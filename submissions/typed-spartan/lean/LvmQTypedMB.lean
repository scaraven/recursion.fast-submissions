-- New for lvm2 (roll 8 = B1, B1-Q; B-DES §1.5): the mini-bus `mbT`. `capTpl`'s `readd`s (the only reads left on a
-- bus) against seeds of the cap regions only, `2^13` leaves. Reuses `InArr.tab` (the seed side, `LvmM3LoopTab`),
-- the `Tab`/`Key` data of `LvmM3Tab`, `openLoops`' cap parameters (`LvmQLink`, untouched).
import LvmQTyped
import LvmQAsmProg

/-!
# The mini-bus's tables

Memory checking as WP-9's (`LvmM3Inst`): a read with count column `c` pulls `⟨k, c⟩` and pushes `⟨k, g·c⟩`; a seed
with finalize column `f` pushes `⟨k, 1⟩` and pulls `⟨k, f⟩`. Only `capTpl`'s reads are on this bus.

* **Seeds** (`mbArrs`): per lane class `l < 17` and aligned block of `2^4` rows meeting some cap region
  (`capRegions`: `capTpl`'s `[capL, capL + 4·2^c)`, `c = height − path`), once (`eraseDups`), an `InArr` over the
  stream cells `sb + 17 q + l` whose value column is `C_rec`'s lane `l` there (`S_flat`'s words, as today's lane
  arrays). Every cap cell is seeded (**`mbSeed_cover`**) and no cell twice (blocks are distinct and aligned).
* **Reads** (`capReads`): per loop block of the program with four `readd` rows (`capTpl`'s; QLT's loop has nine)
  and each of them, a table of `2^ℓ` rows: the address column (the words of the `readd`'s address cells), the value
  column (the words of its result cells), the read count; one read `⟨g^3, addr, [val]⟩`. Every iteration is a real
  read (the padded positions read cap cell `0`), so no padding row. The placements are the layout's (`wordK`, the
  word of a `K` cell; `MbFit`: the address and result cells of a block's row are consecutive words).
* **Targets**: a cap read's address is `g^{lo + 4·idx + r}` with `idx < 2^c`, `r < 4` (`capTpl`), inside the region
  (**`capTarget_mem`**), hence seeded (**`capRead_seeded`**). With honest counts (`g^0, g^1, …` per cell in read
  order, finalize `g^{reads}`) the bus balances.
-/

set_option autoImplicit false

namespace Lvm.QTyped

open Lvm Lvm.Loop Lvm.Loop.Build Lvm.QAsm Lvm.Har Lvm.M3 Lvm.QLink

/-! ## The seed side -/

/-- The cap regions `(first stream lane, cap bits)` of the openings (`openLoops`' `capL`, `height − path`). -/
def capRegions (p : Params) : List (Nat × Nat) :=
  ((opens p).map fun o => (eLane p o.ce + 1 + o.co / 8, o.L.height - o.L.path)).eraseDups

/-- The rows `[q0, q1)` of lane class `l < 17` whose lanes `17 q + l` lie in `[a, a + n)`. -/
def laneRows (a n l : Nat) : Nat × Nat := ((a + 16 - l) / 17, (a + n + 16 - l) / 17)

/-- The aligned blocks of `2^t` rows covering `[q0, q1)` (their first rows): from `q0`'s block, as many as cover
`⌈n/17⌉` rows at the worst alignment (B1-IX: a fixed count, so that the mini-bus's record does not depend on where
the caps fall in the stream, and the refreeze reaches a fixpoint). -/
def laneBlocks (a n l t : Nat) : List Nat :=
  let b0 := (laneRows a n l).1 / 2 ^ t
  (List.range (((n + 16) / 17 + 2 ^ t - 2) / 2 ^ t + 1)).map fun i => (b0 + i) * 2 ^ t

/-- The mini-bus's seed block: `2^4` rows. -/
abbrev mbBlk : Nat := 4

/-- The seeded `(lane class, first row)` blocks, each once. -/
def mbBlocks (p : Params) : List (Nat × Nat) :=
  ((capRegions p).flatMap fun c => (List.range 17).flatMap fun l =>
    (laneBlocks c.1 (4 * 2 ^ c.2) l mbBlk).map fun q => (l, q)).eraseDups

/-- **The mini-bus's seed arrays** (finalize count of array `k` at `fin k`). -/
def mbArrs (C : QCfg) (fin : Nat → Bool × Nat) : List InArr :=
  (mbBlocks C.p).zipIdx.map fun x =>
    ⟨.K, mbBlk, (lay C).sb + 17 * x.1.2 + x.1.1, 17, [(true, x.1.1 * 2 ^ C.rl + x.1.2)], fin x.2, none⟩

/-- The seed arrays' fixed address columns, for the circuit's check (`TData.mbFix`): table `k`, column `2`. -/
def mbFixOf (C : QCfg) : List (Nat × Nat × Nat × Nat) :=
  (mbArrs C fun _ => (false, 0)).zipIdx.map fun a => (a.2, a.1.val.length + 1, a.1.base, a.1.stride)

/-! ## The read side -/

/-- Q_link alone (its cells are the B program's first cells: Q_link runs first). -/
def qlinkProg (C : QCfg) : Program := toProgram (nK C) 0 (qlink C.p (lay C))

/-- The `readd` rows of a block's template. -/
def readdRows (B : Block) : List Nat :=
  (List.range B.tpl.length).filter fun t => match (B.tpl.getD t default).op with
    | .readd _ _ => true
    | _ => false

/-- **`capTpl`'s reads**: `(block, template row)` of every `readd` row of a block with four (`capTpl`'s; QLT's
loop has nine). -/
def capReadRows (Q : Program) : List (Nat × Nat) :=
  (List.range Q.blocks.length).flatMap fun b =>
    if (readdRows (Q.blk b)).length = 4 then (readdRows (Q.blk b)).map (b, ·) else []

/-- Row `t`'s result cell at iteration `jf` (`K`). -/
def resCell (Q : Program) (b t jf : Nat) : Nat :=
  Q.start .K b + (Q.blk b).tw .K * jf + (Q.blk b).rank .K t

/-- The address cell of `readd` row `t` at iteration `jf`. -/
def adrCell (Q : Program) (b t jf : Nat) : Nat :=
  (((Q.blk b).tpl.getD t default).args.getD 0 default).at (unflat (Q.blk b).dims jf)

/-- The read key: `⟨g^3, column 0, [column 1]⟩`. -/
def readKey : Key := ⟨sep .K, CPoly.var 0, [CPoly.var 1]⟩

/-- **A read table**: `2^ℓ` reads of block `b`'s row `t`, address column at word `wa`, value column at `wv`, count
column at `wc` (all `C_main`). -/
def readTab (τ wa wv wc : Nat) : Tab where
  τ := τ
  cols := [.com false wa, .com false wv, .com false wc]
  cons := []
  reads := [(readKey, 2)]
  seeds := []
  deg := by
    refine ⟨fun C hC ↦ by simp at hC, fun r hr ↦ ?_, fun s hs ↦ by simp at hs⟩
    simp only [List.mem_singleton] at hr; subst hr
    have hv : ∀ i, CPoly.Deg2 (CPoly.var i) := fun i m hm ↦ by
      simp [CPoly.var] at hm; subst hm; simp
    exact ⟨hv _, fun P hP ↦ by simp [readKey] at hP; subst hP; exact hv _⟩

/-- **The read tables** of `capTpl`'s reads; `wordK` the layout's word of a `K` cell, `cnt k` table `k`'s count
column. -/
def capReads (C : QCfg) (wordK : Nat → Nat) (cnt : Nat → Nat) : List Tab :=
  let Q := qlinkProg C
  (capReadRows Q).zipIdx.map fun x =>
    readTab (Q.blk x.1.1).lsize (wordK (adrCell Q x.1.1 x.1.2 0)) (wordK (resCell Q x.1.1 x.1.2 0)) (cnt x.2)

/-- **The layout fits the read tables**: a read table's address and result cells are consecutive words. -/
def MbFit (C : QCfg) (wordK : Nat → Nat) : Prop :=
  ∀ x ∈ capReadRows (qlinkProg C), ∀ jf < 2 ^ ((qlinkProg C).blk x.1).lsize,
    wordK (adrCell (qlinkProg C) x.1 x.2 jf) = wordK (adrCell (qlinkProg C) x.1 x.2 0) + jf ∧
    wordK (resCell (qlinkProg C) x.1 x.2 jf) = wordK (resCell (qlinkProg C) x.1 x.2 0) + jf

/-- **The mini-bus's tables**: the seed arrays, then the read tables. -/
def mbT (C : QCfg) (wordK : Nat → Nat) (fin : Nat → Bool × Nat) (cnt : Nat → Nat) : List Tab :=
  (mbArrs C fin).map InArr.tab ++ capReads C wordK cnt

/-- **Each read block is a cap region's** (a native check, `true` at `P20` and `P8` [B1-Q]): a block with four
`readd` rows has `capTpl`'s length `2c + 16` and its address row's constant `g^{sb + a}` for a region `(a, c)` of
`capRegions`, and its reads search the stream. Then its targets are that region's (`capTpl`: `g^{lo + 4 idx + r}`,
`idx < 2^c`), so seeded (`capRead_seeded`), each once (`mbBlocks_disjoint`): with honest counts (`g^0 … g^{m−1}` on
a cell's `m` reads in order, finalize `g^m`) every cell's pushes `1, g, …, g^m` are its pulls, and the bus
balances. -/
def capBlocksOk (C : QCfg) : Bool :=
  let Q := qlinkProg C
  (capReadRows Q).all fun x =>
    let B := Q.blk x.1
    (capRegions C.p).any fun r =>
      B.tpl.length == 2 * r.2 + 16 &&
      (match (B.tpl.getD 2 default).op with
        | .lin _ k' => k' == Lvm.Loop.Build.gpow ((lay C).sb + r.1)
        | _ => false) &&
      (match (B.tpl.getD x.2 default).op with
        | .readd lo m => lo == (lay C).sb && m == (lay C).m
        | _ => false)

/-! ## Value lemmas -/

/-- **A cap read's target lies in its region**: `lo + 4·idx + r < lo + 4·2^c` for `idx < 2^c`, `r < 4`. -/
theorem capTarget_mem {lo c idx r : Nat} (hi : idx < 2 ^ c) (hr : r < 4) :
    lo ≤ lo + 4 * idx + r ∧ lo + 4 * idx + r < lo + 4 * 2 ^ c := by
  constructor <;> omega

/-- `K` aligned blocks of `m` rows from `x0`'s block reach every `x < x0 + c` (`K = ⌊(c + m − 2)/m⌋ + 1`). -/
theorem blocks_span {q0 x c m : Nat} (hm : 0 < m) (hx : x < q0 + c) :
    x / m - q0 / m < (c + m - 2) / m + 1 := by
  have e1 := Nat.div_add_mod q0 m
  have e2 := Nat.mod_lt q0 hm
  have e3 := Nat.div_mul_le_self x m
  have e5 := Nat.div_add_mod (c + m - 2) m
  have e6 := Nat.mod_lt (c + m - 2) hm
  have key : (x / m - q0 / m) * m < ((c + m - 2) / m + 1) * m := by
    rw [Nat.sub_mul, Nat.add_mul, Nat.one_mul]
    rw [Nat.mul_comm] at e1 e5
    omega
  exact Nat.lt_of_mul_lt_mul_right key

/-- **The blocks cover the lane class's rows**: a lane `p ∈ [a, a + n)` of class `p % 17` lies in a block. -/
theorem laneBlocks_cover {a n t p : Nat} (hp : a ≤ p) (hpn : p < a + n) :
    ∃ q ∈ laneBlocks a n (p % 17) t, q ≤ p / 17 ∧ p / 17 < q + 2 ^ t := by
  have h17 := Nat.div_add_mod p 17
  have hl : p % 17 < 17 := Nat.mod_lt _ (by decide)
  have ht : 0 < 2 ^ t := Nat.two_pow_pos t
  have hq0 : (a + 16 - p % 17) / 17 ≤ p / 17 := by
    have : (a + 16 - p % 17) / 17 < p / 17 + 1 := (Nat.div_lt_iff_lt_mul (by decide)).mpr (by omega)
    omega
  have hq1 : p / 17 < (a + 16 - p % 17) / 17 + (n + 16) / 17 := by
    have h1 := Nat.div_add_mod (a + 16 - p % 17) 17
    have h2 := Nat.mod_lt (a + 16 - p % 17) (show 17 > 0 by decide)
    have h3 := Nat.div_add_mod (n + 16) 17
    have h4 := Nat.mod_lt (n + 16) (show 17 > 0 by decide)
    omega
  have hb : (a + 16 - p % 17) / 17 / 2 ^ t ≤ p / 17 / 2 ^ t := Nat.div_le_div_right hq0
  refine ⟨p / 17 / 2 ^ t * 2 ^ t, ?_, Nat.div_mul_le_self _ _, ?_⟩
  · simp only [laneBlocks, laneRows, List.mem_map, List.mem_range]
    exact ⟨p / 17 / 2 ^ t - (a + 16 - p % 17) / 17 / 2 ^ t, blocks_span ht hq1,
      by rw [Nat.add_sub_cancel' hb]⟩
  · have h5 := Nat.div_add_mod (p / 17) (2 ^ t)
    have h6 := Nat.mod_lt (p / 17) ht
    rw [Nat.mul_comm] at h5
    omega

/-- **Every cap cell is seeded**: a lane `p` of a cap region `(a, c)` of `capRegions` lies in a seeded block
`(p % 17, q)` of `mbBlocks`. -/
theorem mbSeed_cover {p : Params} {a c x : Nat} (hc : (a, c) ∈ capRegions p) (h1 : a ≤ x)
    (h2 : x < a + 4 * 2 ^ c) :
    ∃ q, (x % 17, q) ∈ mbBlocks p ∧ q ≤ x / 17 ∧ x / 17 < q + 2 ^ mbBlk := by
  obtain ⟨q, hq, hq1, hq2⟩ := laneBlocks_cover (t := mbBlk) h1 h2
  refine ⟨q, ?_, hq1, hq2⟩
  simp only [mbBlocks, List.mem_eraseDups, List.mem_flatMap, List.mem_map, List.mem_range]
  exact ⟨(a, c), hc, x % 17, Nat.mod_lt _ (by decide), q, hq, rfl⟩

/-- **A cap read is seeded**: the target `lo + 4·idx + r` of a read of region `(lo, c)` lies in a seeded block. -/
theorem capRead_seeded {p : Params} {lo c idx r : Nat} (hc : (lo, c) ∈ capRegions p) (hi : idx < 2 ^ c)
    (hr : r < 4) :
    ∃ q, ((lo + 4 * idx + r) % 17, q) ∈ mbBlocks p ∧ q ≤ (lo + 4 * idx + r) / 17 ∧
      (lo + 4 * idx + r) / 17 < q + 2 ^ mbBlk :=
  mbSeed_cover hc (capTarget_mem hi hr).1 (capTarget_mem hi hr).2

/-- **Seeded blocks are disjoint**: two blocks of `mbBlocks` sharing a cell are equal (aligned blocks of one
size). -/
theorem mbBlocks_disjoint {p : Params} {l l' q q' x : Nat} (hb : (l, q) ∈ mbBlocks p) (hb' : (l', q') ∈ mbBlocks p)
    (hx : q ≤ x ∧ x < q + 2 ^ mbBlk) (hx' : q' ≤ x ∧ x < q' + 2 ^ mbBlk) : q = q' := by
  have al : ∀ {l q}, (l, q) ∈ mbBlocks p → q % 2 ^ mbBlk = 0 := by
    intro l q h
    simp only [mbBlocks, List.mem_eraseDups, List.mem_flatMap, List.mem_map, List.mem_range, laneBlocks] at h
    obtain ⟨_, _, _, _, _, ⟨i, _, rfl⟩, he⟩ := h
    cases he
    exact Nat.mul_mod_left _ _
  have h1 := al hb
  have h2 := al hb'
  simp only [show (2 : Nat) ^ mbBlk = 16 from rfl] at h1 h2 hx hx'
  omega

end Lvm.QTyped
