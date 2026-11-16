-- new for lvm (WP-12b): WP-12's `BITS` row (`LvmBits`) as an auxiliary table of WP-9's lvm M3
-- instance (`LvmM3Tab.Tab`), read through the bus (WP-9b `LvmM3Aux`: `aux_read_at`, `aux_cons`).
-- Searched for reuse: WP-9's `InArr.tab` (the fixed address-column pattern, followed here),
-- `LvmM3Loop.evalB_ofPoly2` (the `evalB` transport pattern); FR has no bus-read bit table.
import LvmBits
import LvmM3FidFixC
import LvmM3Loop

-- ===== merged from `LvmM3Aux` (GOLF module merge: `LvmM3Aux.lean` is now a stub importing `LvmBitsTab`) =====
section
-- new for lvm (WP-9b): the auxiliary tables' reads through the bus (the `BITS` bridge for WP-12),
-- from WP-9's `seed_key`/`mem_lookup` and WP-10's `seed_cases`/`holds_seedMem`/`interp_unique`
-- (the first lines of `loopir_sound`'s proof, `LvmLoopSound.lean:348`).

/-!
# Auxiliary tables read the interpreter's cells

**The `BITS` bridge (option "reads through the bus").** An auxiliary table (`aux`, WP-12's `BITS`)
seeds nothing; it *reads* cells of the LoopIR memories through the bus, like a LoopIR piece: the
word it decomposes and each of its outputs (`shl k`, `shr k`, `bit z`, a linear form of its bit
columns). The outputs are LoopIR *input* cells (seeded by an input array, any value the prover
chose); the table's reads pin them to the word's functions. `aux_read`: on the lvm instance with
`M3Holds`, each read of an auxiliary table at each row is, coordinate by coordinate, the key of a
cell of the interpreter's run on the inputs read off the stack (`interpMem (inKOf q) (inEOf q)`):
separator `sep τ`, address `g^e`, value limbs the cell's. `aux_read_at`: with the address known
(`g^a`, `a` below the cell count, a fixed column of the table), the value limbs are cell `a`'s.

WP-12 combines this with its row lemma (`LvmBits.row_sound`: the row's constraints make every
output the word function of the word) to get `SigBits` for `M = interpMem`.
-/

namespace Lvm.M3

open LeanVM.Parameters LeanVM.Protocol CompPoly
open Lvm.Loop

/-! ## The seed memory is the interpreter's -/

/-- **Under `loopir_sound`'s hypotheses the seed memory is the interpreter's memory** on every
cell (the agreement `loopir_sound` proves on the way, `LvmLoopSound.lean:356`). -/
theorem seedMem_eq_interp (Q : Program) (hwf : Q.wf = true) (inK : Array FK) (inE : Array FE)
    (hsz : inK.size = Q.nInK ∧ inE.size = Q.nInE) (W : Witness) (hcons : Q.ConstraintsHold W)
    (hbus : ∀ m ∈ Q.readMsgs W, m.key ∈ (Q.seedMsgs W inK inE).map Msg.key)
    (hinj : GInj (max (Q.cells .K) (Q.cells .E))) (hinb : (Q.interp inK inE).inb = true)
    {τ : Ty} {e : ℕ} (he : e < Q.cells τ) :
    (Q.seedMem W inK inE).rd τ e = (Q.interpMem inK inE).rd τ e := by
  obtain ⟨hH, -⟩ := Q.holds_seedMem hwf hcons hbus hinj
  have hin : Q.Inputs (Q.seedMem W inK inE) inK inE :=
    ⟨fun n hn => by simp [Program.seedMem, hn], fun n hn => by simp [Program.seedMem, hn]⟩
  obtain ⟨hag, -⟩ := Q.interp_unique hwf inK inE hsz _ hin hH hinj hinb
  exact Program.Mem.rd_agree' hag _ _ (by rw [Q.cells_pick]; exact he)

section Aux

variable (Q : Program) (pl : ℕ → Var → Bool × ℕ) (groups : List Grp) (arrs : List InArr)
  (aux : List Tab) (L : Lay) (hτ : ∀ t ∈ lvmTabs Q pl groups arrs aux, t.τ ≤ L.μ)

/-- The hypotheses `aux_read` shares with `loop_bus` and `loopir_sound`. -/
structure AuxHyps (q : Column L.μ) : Prop where
  wf : Q.wf = true
  grp : GrpOk Q groups
  inOk : InOk Q arrs
  auxSeeds : ∀ t ∈ aux, t.seeds = []
  cnt : ∀ t ∈ lvmTabs Q pl groups arrs aux, ∀ r ∈ t.reads, r.2 < t.w
  len : nReads (lvmTabs Q pl groups arrs aux) < 2 ^ 64 - 1
  inj : GInj (max (Q.cells .K) (Q.cells .E))
  holds : M3Holds (lvmInst Q pl groups arrs aux L hτ) () q
  inb : (Q.interp (inKOf Q pl groups arrs aux L hτ q) (inEOf Q pl groups arrs aux L hτ q)).inb = true

/-- **An auxiliary table's read is a cell of the interpreter's run** (the `BITS` bridge). At row `x`
of auxiliary table `k` (instance table `groups.length + arrs.length + k`), the read `r`'s
separator, address and value limbs, evaluated on the row, are those of cell `e` of memory `τ` of
`interpMem (inKOf q) (inEOf q)`, for some `e` below the cell count. -/
theorem aux_read (q : Column L.μ) (H : AuxHyps Q pl groups arrs aux L hτ q) {k : ℕ}
    (hk : k < aux.length)
    (hj : groups.length + arrs.length + k < (lvmTabs Q pl groups arrs aux).length)
    (x : Fin (2 ^ ((lvmTabs Q pl groups arrs aux).get ⟨_, hj⟩).τ)) {r : Key × ℕ}
    (hr : r ∈ aux[k].reads) :
    ∃ τ e, e < Q.cells τ ∧ r.1.sep = sep τ ∧
      CPoly.evalB (CPoly.ext ((lvmInst Q pl groups arrs aux L hτ).row q ⟨_, hj⟩ x)) r.1.addr =
        FK.toBF64 (FK.x ^ e) ∧
      ∀ l < 13, CPoly.evalB (CPoly.ext ((lvmInst Q pl groups arrs aux L hτ).row q ⟨_, hj⟩ x))
          (r.1.val.getD l []) =
        FK.toBF64 ((limbsOf τ ((Q.interpMem (inKOf Q pl groups arrs aux L hτ q)
          (inEOf Q pl groups arrs aux L hτ q)).rd τ e)).getD l 0) := by
  set W := witOf Q pl groups arrs aux L hτ q
  set inK := inKOf Q pl groups arrs aux L hτ q
  set inE := inEOf Q pl groups arrs aux L hτ q
  have hget := get_aux Q pl groups arrs aux hk hj
  set row := (lvmInst Q pl groups arrs aux L hτ).row q ⟨_, hj⟩ x
  have hrd : r ∈ ((lvmTabs Q pl groups arrs aux).get ⟨_, hj⟩).reads := by rw [hget]; exact hr
  have hu : evalV row (((lvmTabs Q pl groups arrs aux).get ⟨_, hj⟩).readVec r) ∈
      readTuples L (lvmTabs Q pl groups arrs aux) hτ q := by
    simp only [readTuples, partT, List.mem_flatMap, List.mem_map]
    refine ⟨⟨_, hj⟩, List.mem_finRange _, _, ⟨_, hrd, rfl⟩, x, ?_, rfl⟩
    simp [M3Instance.executed, inst]
  obtain ⟨s, hs, hks⟩ := List.mem_map.mp (mem_lookup L (lvmTabs Q pl groups arrs aux) hτ q
    H.holds.2.1 H.holds.2.2.1 H.cnt H.len _ hu)
  obtain ⟨m', -, hm', he⟩ := seed_key Q pl groups arrs aux L hτ H.grp H.inOk H.auxSeeds q hs
  obtain ⟨τ, e, hec, h1, h2, h3⟩ := Q.seed_cases W inK inE hm'
  have hkey : keyT (evalV row (((lvmTabs Q pl groups arrs aux).get ⟨_, hj⟩).readVec r)) =
      keyT (encT m') := hks.symm.trans he
  have hagree := seedMem_eq_interp Q H.wf inK inE
    ⟨inKOf_size Q pl groups arrs aux L hτ q, inEOf_size Q pl groups arrs aux L hτ q⟩ W
    (loop_cons Q pl groups arrs aux L hτ H.grp q H.holds) (loop_bus Q pl groups arrs aux L hτ H.grp
      H.inOk H.auxSeeds H.cnt H.len q H.holds) H.inj H.inb hec
  have hcoord : ∀ i (hi : i < 16), i ≠ 2 →
      (evalV row (((lvmTabs Q pl groups arrs aux).get ⟨_, hj⟩).readVec r))[i] = (encT m')[i] :=
    fun i hi hi2 ↦ keyT_coord hkey i hi hi2
  refine ⟨τ, e, hec, ?_, ?_, fun l hl ↦ ?_⟩
  · have := hcoord 0 (by norm_num) (by norm_num)
    simp only [evalV, Tab.readVec, Key.vec, Vector.getElem_map, Vector.getElem_ofFn, encT,
      if_true, MvPolynomial.eval_C] at this
    exact (FK.toBF64_injective this).trans h1
  · have := hcoord 1 (by norm_num) (by norm_num)
    simp only [evalV, Tab.readVec, Key.vec, Vector.getElem_map, Vector.getElem_ofFn, encT,
      show (1 : ℕ) ≠ 0 from by decide, if_true, if_false, CPoly.eval_toMv] at this
    rw [this, h2]
  · have := hcoord (l + 3) (by omega) (by omega)
    simp only [evalV, Tab.readVec, Key.vec, Vector.getElem_map, Vector.getElem_ofFn, encT,
      show l + 3 ≠ 0 from by omega, show l + 3 ≠ 1 from by omega, show l + 3 ≠ 2 from by omega,
      if_false, Nat.add_sub_cancel, CPoly.eval_toMv] at this
    rw [this, h3, hagree]

/-- **An auxiliary table's read at a known address is that cell of the interpreter's run**: if the
read names memory `τ` and evaluates its address to `g^a` with `a` below the cell count, its value
limbs are cell `a`'s. -/
theorem aux_read_at (q : Column L.μ) (H : AuxHyps Q pl groups arrs aux L hτ q) {k : ℕ}
    (hk : k < aux.length)
    (hj : groups.length + arrs.length + k < (lvmTabs Q pl groups arrs aux).length)
    (x : Fin (2 ^ ((lvmTabs Q pl groups arrs aux).get ⟨_, hj⟩).τ)) {r : Key × ℕ}
    (hr : r ∈ aux[k].reads) {τ : Ty} {a : ℕ} (hsep : r.1.sep = sep τ) (ha : a < Q.cells τ)
    (haddr : CPoly.evalB (CPoly.ext ((lvmInst Q pl groups arrs aux L hτ).row q ⟨_, hj⟩ x))
      r.1.addr = FK.toBF64 (FK.x ^ a)) :
    ∀ l < 13, CPoly.evalB (CPoly.ext ((lvmInst Q pl groups arrs aux L hτ).row q ⟨_, hj⟩ x))
        (r.1.val.getD l []) =
      FK.toBF64 ((limbsOf τ ((Q.interpMem (inKOf Q pl groups arrs aux L hτ q)
        (inEOf Q pl groups arrs aux L hτ q)).rd τ a)).getD l 0) := by
  obtain ⟨τ', e, he, h1, h2, h3⟩ := aux_read Q pl groups arrs aux L hτ q H hk hj x hr
  obtain rfl : τ' = τ := sep_inj' (h1.symm.trans hsep)
  have hN : ∀ σ, Q.cells σ ≤ max (Q.cells .K) (Q.cells .E) := fun σ ↦ by cases σ <;> simp
  obtain rfl : e = a := H.inj _ _ (lt_of_lt_of_le he (hN _)) (lt_of_lt_of_le ha (hN _))
    (FK.toBF64_injective (h2.symm.trans haddr))
  exact h3

/-- **An auxiliary table's constraints vanish on every row** (`ConstraintsVanish`, on the row as
`CPoly.evalB` reads it): WP-12's row lemma starts here. -/
theorem aux_cons (q : Column L.μ) (hM : M3Holds (lvmInst Q pl groups arrs aux L hτ) () q) {k : ℕ}
    (hk : k < aux.length)
    (hj : groups.length + arrs.length + k < (lvmTabs Q pl groups arrs aux).length)
    (x : Fin (2 ^ ((lvmTabs Q pl groups arrs aux).get ⟨_, hj⟩).τ)) {C : CPoly} (hC : C ∈ aux[k].cons) :
    CPoly.evalB (CPoly.ext ((lvmInst Q pl groups arrs aux L hτ).row q ⟨_, hj⟩ x)) C = 0 := by
  have hcm : C ∈ ((lvmTabs Q pl groups arrs aux).get ⟨_, hj⟩).cons := by
    rw [get_aux Q pl groups arrs aux hk hj]; exact hC
  have hz := hM.1 ⟨_, hj⟩ _ (List.mem_map_of_mem hcm) x
  rwa [CPoly.eval_toMv] at hz

end Aux

end Lvm.M3
end
-- ===== end of `LvmM3Aux` =====

/-!
# The `BITS` table and its soundness through the bus

**The table** (`BSpec.tab`). A `BITS` class `S` (one output list for all rows) is a table of
height `2^τ`. Columns:
* `0`: the word `w`; `1 + z` (`z < 64`): the bit column `β_z` (committed);
* `65`: the count column of the word's read; `66`: its address `g^{wc x}` (fixed);
* `67 + j`: output `j`'s read count (committed);
* then the output addresses (fixed): with `sh > 0` (lvm2 EVD2), one **shared** column `g^{oc 0 x}`
  at `67 + |outs|` whose `g^j` multiple is output `j`'s address for `j < sh` (the class's cells
  satisfy `oc j x = oc 0 x + j` there, `hsh`); then one column `g^{oc j x}` per output `j ≥ sh`.

Constraints (degree 2, `CPoly`): `w + Σ_z x^z·β_z` and `β_z·β_z + β_z`. Reads of the `K` memory:
the word (value polynomial `w`; only when `rd`) and every output `j`, whose value polynomial is
the linear form `Σ_z coef_z·β_z` of `LvmBits` (`outPoly`). Rows `x < n` are the real ones; rows
`n ≤ x < 2^τ` repeat row `0`'s addresses (`BSpec.row`): `CountsNonzero` forbids count-`0` padding
(`rows = 2^τ`), so the honest prover fills them with further reads of row `0`'s cells, their counts
continuing those cells' `g`-power read sequences (finalize counts include them). With `rd = false`
columns `65`, `66` are don't-care (committed / fixed, never read).
A fixed column's closed form is its multilinear extension (`Loop.mle`, `O(2^τ)` for the native
verifier), so `FixOk` holds by definition (`fixOk_tab`).

**Soundness** (`out_sound`): under WP-9b's `AuxHyps` (the hypotheses of `loopir_sound`), at a real
row `x` of a `BITS` table in `aux`, with the cells it names below `Q.cells .K`, there is a word
`w` (the row's) such that the read word cell holds `w` (when `rd`) and output cell `oc j x` holds
`⟨outs[j].word w.val⟩`, in the interpreter's memory: WP-12's `row_sound` transported through
`FK.toBF64` (WP-1's ring isomorphism `ringEquivBF64`).

**Completeness** (`honest_cons`, `honest_out`): the honest row of any word (its bits) makes every
constraint vanish and every output polynomial its word function.
-/

set_option autoImplicit false

namespace Lvm.BitsTab

open LeanVM.Parameters LeanVM.Protocol Lvm Lvm.Bits Lvm.M3 Lvm.Loop

/-! ## `CPoly`s over `FK` -/

/-- A `CPoly`'s value at an `FK` row. -/
def evalK (v : Nat → FK) (P : CPoly) : FK := (P.map fun m => m.1 * (m.2.map v).prod).sum

/-- **`evalB` is `evalK` through `FK.toBF64`.** -/
theorem evalB_eq (u : Nat → K) (P : CPoly) :
    CPoly.evalB u P = FK.toBF64 (evalK (fun i => FK.ofBF64 (u i)) P) := by
  unfold CPoly.evalB evalK
  rw [← FK.ringEquivBF64_apply, map_list_sum, List.map_map]
  congr 1
  refine List.map_congr_left fun m _ => ?_
  simp only [Function.comp, map_mul, map_list_prod, List.map_map, FK.ringEquivBF64_apply,
    FK.toBF64_ofBF64]
  rfl

theorem sum_range (g : Nat → FK) : ∀ n, ((List.range n).map g).sum = lsum g n
  | 0 => rfl
  | n + 1 => by rw [List.range_succ, List.map_append, List.sum_append, sum_range g n]; simp [lsum]

theorem evalB_var (u : Nat → K) (i : Nat) : CPoly.evalB u (CPoly.var i) = u i := by
  simp [CPoly.evalB, CPoly.var]

/-! ## The table -/

/-- The word constraint `w + Σ_z x^z·β_z`. -/
def wcons : CPoly := (1, [0]) :: (List.range 64).map fun z => (wt z, [1 + z])

/-- The bit constraint `β_z·β_z + β_z`. -/
def bcons (z : Nat) : CPoly := [(1, [1 + z, 1 + z]), (1, [1 + z])]

/-- The constraints. -/
def cons : List CPoly := wcons :: (List.range 64).map bcons

/-- An output's value polynomial: `Σ_z coef_z·β_z`. -/
def outPoly (o : BOut) : CPoly := (List.range 64).map fun z => (o.coef z, [1 + z])

/-- **A `BITS` class**: `n` real rows of `2^τ`; row `x` reads the word of `K` cell `wc x` (when
`rd`) and writes output `outs[j]` to `K` cell `oc j x`; `pl c` places committed column `c`. -/
structure BSpec where
  /-- Log-height. -/
  τ : Nat
  /-- The real rows. -/
  n : Nat
  /-- The outputs of every row. -/
  outs : List BOut
  /-- Whether the word is read from a cell (else it is a free committed word). -/
  rd : Bool
  /-- The word's cell. -/
  wc : Nat → Nat
  /-- Output `j`'s cell at row `x`. -/
  oc : Nat → Nat → Nat
  /-- The committed columns' placements. -/
  pl : Nat → Bool × Nat
  /-- The first `sh` outputs share one address column (lvm2 EVD2; `0`: one column per output). -/
  sh : Nat
  /-- Their cells are consecutive at every real row. -/
  hsh : ∀ j < sh, ∀ x < n, oc j x = oc 0 x + j

namespace BSpec

variable (S : BSpec)

/-- Output `j`. -/
def out (j : Nat) : BOut := S.outs.getD j (.bit 0)

/-- The real row whose addresses row `x` uses (padding rows repeat row `0`). -/
def row (x : Nat) : Nat := if x < S.n then x else 0

/-- The number of shared address columns (`0` or `1`). -/
def nA : Nat := if S.sh = 0 then 0 else 1

/-- The first output-address column. -/
def ab : Nat := 67 + S.outs.length

/-- The width: `67`, the output counts, the shared address column, the other outputs' addresses. -/
def width : Nat := S.ab + S.nA + (S.outs.length - S.sh)

/-- The fixed address column `x ↦ g^{a (row x)}`, its closed form the extension. -/
def adrCol (a : Nat → Nat) : ColSrc :=
  .fix (fun x => FK.x ^ a (S.row x)) fun r => Loop.mle r fun x => FE.ofK (FK.x ^ a (S.row x))

/-- Column `c`. -/
def col (c : Nat) : ColSrc :=
  if c = 66 then S.adrCol S.wc
  else if c < S.ab then .com (S.pl c).1 (S.pl c).2
  else if S.sh ≠ 0 ∧ c = S.ab then S.adrCol (S.oc 0)
  else S.adrCol (S.oc (c - S.ab - S.nA + S.sh))

/-- Output `j`'s address: `g^j` times the shared column (`j < sh`), else its own column. -/
def oaddr (j : Nat) : CPoly :=
  if j < S.sh then [(FK.x ^ j, [S.ab])] else CPoly.var (S.ab + S.nA + (j - S.sh))

/-- The word's read. -/
def wread : Key × Nat := (⟨sep .K, CPoly.var 66, [CPoly.var 0]⟩, 65)

/-- Output `j`'s read. -/
def oread (j : Nat) : Key × Nat := (⟨sep .K, S.oaddr j, [outPoly (S.out j)]⟩, 67 + j)

/-- The reads. -/
def reads : List (Key × Nat) :=
  (if S.rd then [wread] else []) ++ (List.range S.outs.length).map S.oread

theorem deg_var (i : Nat) : CPoly.Deg2 (CPoly.var i) := fun m hm => by
  simp [CPoly.var] at hm; subst hm; simp

/-- **The `BITS` table.** -/
def tab : Tab where
  τ := S.τ
  cols := (List.range S.width).map S.col
  cons := cons
  reads := S.reads
  seeds := []
  deg := by
    refine ⟨fun C hC m hm => ?_, fun r hr => ?_, fun s hs => by simp at hs⟩
    · simp only [cons, List.mem_cons, List.mem_map, List.mem_range] at hC
      rcases hC with rfl | ⟨z, -, rfl⟩
      · simp only [wcons, List.mem_cons, List.mem_map, List.mem_range] at hm
        rcases hm with rfl | ⟨z, -, rfl⟩ <;> simp
      · simp only [bcons, List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at hm
        rcases hm with rfl | rfl <;> simp
    · simp only [reads, List.mem_append, List.mem_map, List.mem_range] at hr
      rcases hr with h | ⟨j, -, rfl⟩
      · split at h
        · simp only [List.mem_singleton] at h; subst h
          exact ⟨deg_var 66, fun P hP => by simp [wread] at hP; subst hP; exact deg_var 0⟩
        · simp at h
      · refine ⟨?_, fun P hP => ?_⟩
        · unfold oread oaddr; split
          · intro m hm; simp only [List.mem_singleton] at hm; subst hm; simp
          · exact deg_var _
        simp only [oread, List.mem_singleton] at hP; subst hP
        intro m hm
        simp only [outPoly, List.mem_map, List.mem_range] at hm
        obtain ⟨z, -, rfl⟩ := hm; simp

theorem tab_w : S.tab.w = S.width := by simp [Tab.w, tab]

theorem tab_seeds : S.tab.seeds = [] := rfl

/-- The read-count columns lie inside the width (`AuxHyps.cnt`). -/
theorem tab_cnt : ∀ r ∈ S.tab.reads, r.2 < S.tab.w := by
  intro r hr
  rw [tab_w]
  simp only [tab, reads, List.mem_append, List.mem_map, List.mem_range] at hr
  rcases hr with h | ⟨j, hj, rfl⟩
  · split at h
    · simp only [List.mem_singleton] at h; subst h; simp only [wread, width, ab]; omega
    · simp at h
  · simp only [oread, width, ab]; omega

theorem tab_cols (c : Nat) (hc : c < S.width) : S.tab.cols[c]? = some (S.col c) := by
  simp [tab, hc]

/-- **An output's address on a row whose address columns hold their powers** is `g^{oc j x}`. -/
theorem oaddr_eval (u : Nat → K) {x : Nat} (hx : x < S.n)
    (hfix : ∀ (c : Nat) (a : Nat → Nat), c < S.width → S.col c = S.adrCol a → u c = FK.toBF64 (FK.x ^ a x))
    {j : Nat} (hj : j < S.outs.length) : CPoly.evalB u (S.oaddr j) = FK.toBF64 (FK.x ^ S.oc j x) := by
  unfold oaddr
  split
  · rename_i hjs
    have hs : S.sh ≠ 0 := by omega
    have hw : S.ab < S.width := by unfold width nA; rw [if_neg hs]; omega
    have hc := hfix S.ab (S.oc 0) hw (by unfold col ab; rw [if_neg (by omega), if_neg (by omega), if_pos ⟨hs, rfl⟩])
    rw [evalB_eq, S.hsh j hjs x hx, pow_add]
    congr 1
    simp [evalK, hc, FK.ofBF64_toBF64, mul_comm]
  · rename_i hjs
    have hw : S.ab + S.nA + (j - S.sh) < S.width := by unfold width; omega
    have hc := hfix _ (S.oc j) hw (by
      unfold col
      rw [if_neg (by unfold ab; omega), if_neg (by omega), if_neg (by unfold nA; split <;> omega)]
      congr 2; omega)
    rw [evalB_var, hc]

/-- **The closed forms are the extensions** (`FixOk`). -/
theorem fixOk_tab : FixOk [S.tab] := by
  intro t ht f ev hf r _
  simp only [List.mem_singleton] at ht; subst ht
  simp only [tab, List.mem_map, List.mem_range] at hf
  obtain ⟨c, -, hc⟩ := hf
  unfold col adrCol at hc
  split at hc
  · cases hc; rfl
  · split at hc
    · cases hc
    · split at hc <;> (cases hc; rfl)

theorem fixOk_append {a b : List Tab} (ha : FixOk a) (hb : FixOk b) : FixOk (a ++ b) := by
  intro t ht
  rcases List.mem_append.mp ht with h | h
  · exact ha t h
  · exact hb t h

theorem fixOk_tabs (Ss : List BSpec) : FixOk (Ss.map tab) := by
  intro t ht
  obtain ⟨S, -, rfl⟩ := List.mem_map.mp ht
  exact S.fixOk_tab _ (List.mem_singleton_self _)

end BSpec

/-! ## The row lemma on `FK` rows -/

theorem evalK_wcons (v : Nat → FK) : evalK v wcons = v 0 + lsum (fun z => wt z * v (1 + z)) 64 := by
  simp only [evalK, wcons, List.map_cons, List.sum_cons, List.map_map, Function.comp_def,
    List.map_nil, List.prod_cons, List.prod_nil, mul_one, one_mul, sum_range]

theorem evalK_bcons (v : Nat → FK) (z : Nat) :
    evalK v (bcons z) = v (1 + z) * v (1 + z) + v (1 + z) := by
  simp [evalK, bcons]

theorem evalK_outPoly (v : Nat → FK) (o : BOut) :
    evalK v (outPoly o) = lsum (fun z => o.coef z * v (1 + z)) 64 := by
  simp only [evalK, outPoly, List.map_map, Function.comp_def, List.map_cons, List.map_nil,
    List.prod_cons, List.prod_nil, mul_one, sum_range]

/-- The `LvmBits` row of an `FK` row of the table. -/
def rowOf (v : Nat → FK) : Bits.Row := ⟨v 0, fun z => v (1 + z)⟩

theorem rowOf_cons {v : Nat → FK} (h : ∀ C ∈ cons, evalK v C = 0) : (rowOf v).Constraints := by
  refine ⟨fun z hz => ?_, ?_⟩
  · have := h (bcons z) (List.mem_cons_of_mem _ (List.mem_map.mpr ⟨z, List.mem_range.mpr hz, rfl⟩))
    rwa [evalK_bcons] at this
  · have := h wcons (List.mem_cons_self ..)
    rwa [evalK_wcons] at this

theorem rowOf_out (v : Nat → FK) (o : BOut) : evalK v (outPoly o) = (rowOf v).out o := by
  rw [evalK_outPoly]; rfl

/-! ## Soundness through the bus -/

section Sound

variable (Q : Program) (pl : ℕ → Var → Bool × ℕ) (groups : List Grp) (arrs : List InArr)
  (aux : List Tab) (L : Lay) (hτ : ∀ t ∈ lvmTabs Q pl groups arrs aux, t.τ ≤ L.μ)

/-- The interpreter's `K` cells on the inputs read off the stack `q`. -/
noncomputable def memK (q : Column L.μ) : Nat → FK :=
  (Q.interpMem (inKOf Q pl groups arrs aux L hτ q) (inEOf Q pl groups arrs aux L hτ q)).k

/-- **`BITS` soundness through the bus.** At a real row `x` of a `BITS` table of `aux`, whose
cells lie below `Q.cells .K`, the row's word `w` is the word cell's value (when `rd`) and output
cell `oc j x` holds output `j`'s word function of `w`. -/
theorem out_sound (q : Column L.μ) (H : M3.AuxHyps Q pl groups arrs aux L hτ q) (S : BSpec)
    (hS : S.tab ∈ aux) {x : Nat} (hx : x < S.n) (hn : S.n ≤ 2 ^ S.τ)
    (hw : S.rd = true → S.wc x < Q.cells .K) (ho : ∀ j < S.outs.length, S.oc j x < Q.cells .K) :
    ∃ w : FK, (S.rd = true → memK Q pl groups arrs aux L hτ q (S.wc x) = w) ∧
      ∀ j < S.outs.length, (S.out j).Valid →
        memK Q pl groups arrs aux L hτ q (S.oc j x) = ⟨(S.out j).word w.val⟩ := by
  obtain ⟨k, hk, hak⟩ := List.mem_iff_getElem.mp hS
  have hj : groups.length + arrs.length + k < (lvmTabs Q pl groups arrs aux).length := by
    rw [lvmTabs_length]; omega
  have hT : (lvmTabs Q pl groups arrs aux).get ⟨_, hj⟩ = S.tab :=
    (get_aux Q pl groups arrs aux hk hj).trans hak
  have hxT : x < 2 ^ ((lvmTabs Q pl groups arrs aux).get ⟨_, hj⟩).τ := by
    rw [hT]; show x < 2 ^ S.τ; omega
  set xF : Fin (2 ^ ((lvmTabs Q pl groups arrs aux).get ⟨_, hj⟩).τ) := ⟨x, hxT⟩
  set u := CPoly.ext ((lvmInst Q pl groups arrs aux L hτ).row q ⟨_, hj⟩ xF) with hu
  set M := Q.interpMem (inKOf Q pl groups arrs aux L hτ q) (inEOf Q pl groups arrs aux L hτ q)
  have hrow : S.row x = x := if_pos hx
  -- the fixed address columns
  have hfix : ∀ (c : Nat) (a : Nat → Nat), c < S.width → S.col c = S.adrCol a →
      u c = FK.toBF64 (FK.x ^ a x) := by
    intro c a hc hcol
    have hcw : c < ((lvmTabs Q pl groups arrs aux).get ⟨_, hj⟩).w := by
      rw [hT, BSpec.tab_w]; exact hc
    have hf : ((lvmTabs Q pl groups arrs aux).get ⟨_, hj⟩).fixedOf c =
        some fun x => FK.x ^ a (S.row x) := by
      rw [hT, Tab.fixedOf, BSpec.tab_cols S c hc, hcol]; rfl
    have := row_fixed Q pl groups arrs aux L hτ q ⟨_, hj⟩ xF ⟨c, hcw⟩ hf
    rw [hu, CPoly.ext, dif_pos hcw, this, hrow]
  -- a read at a fixed address column is the cell's value
  have hread : ∀ (r : Key × Nat) (c : Nat) (a : Nat → Nat) (P : CPoly), r ∈ S.reads → r.1.sep = sep .K →
      r.1.addr = CPoly.var c → r.1.val = [P] → c < S.width → S.col c = S.adrCol a →
      a x < Q.cells .K → CPoly.evalB u P = FK.toBF64 (M.k (a x)) := by
    intro r c a P hr hsep haddr hval hc hcol hlt
    have hr' : r ∈ aux[k].reads := by rw [hak]; exact hr
    have := aux_read_at Q pl groups arrs aux L hτ q H hk hj xF hr' hsep hlt
      (by rw [haddr, evalB_var]; exact hfix c a hc hcol) 0 (by norm_num)
    rw [hval] at this
    simpa [limbsOf, Mem.rd, FE.ofK] using this
  -- a read whose address evaluates to `g^e`
  have hreadA : ∀ (r : Key × Nat) (e : Nat) (P : CPoly), r ∈ S.reads → r.1.sep = sep .K →
      CPoly.evalB u r.1.addr = FK.toBF64 (FK.x ^ e) → r.1.val = [P] →
      e < Q.cells .K → CPoly.evalB u P = FK.toBF64 (M.k e) := by
    intro r e P hr hsep haddr hval hlt
    have hr' : r ∈ aux[k].reads := by rw [hak]; exact hr
    have := aux_read_at Q pl groups arrs aux L hτ q H hk hj xF hr' hsep hlt haddr 0 (by norm_num)
    rw [hval] at this
    simpa [limbsOf, Mem.rd, FE.ofK] using this
  -- the constraints on the `FK` row
  set v : Nat → FK := fun i => FK.ofBF64 (u i)
  have hcons : ∀ C ∈ cons, evalK v C = 0 := by
    intro C hC
    have hC' : C ∈ aux[k].cons := by rw [hak]; exact hC
    have := aux_cons Q pl groups arrs aux L hτ q H.holds hk hj xF hC'
    rw [evalB_eq] at this
    exact FK.toBF64_injective (this.trans FK.toBF64_zero.symm)
  obtain ⟨-, hout⟩ := row_sound (rowOf_cons hcons)
  have hwid : 66 < S.width := by unfold BSpec.width BSpec.ab; omega
  refine ⟨(rowOf v).w, fun hrd => ?_, fun j hj' hv => ?_⟩
  · have h := hread BSpec.wread 66 S.wc (CPoly.var 0)
      (by simp [BSpec.reads, hrd]) rfl rfl rfl hwid (by simp [BSpec.col]) (hw hrd)
    rw [evalB_var] at h
    show M.k (S.wc x) = FK.ofBF64 (u 0)
    rw [h]; rfl
  · have h := hreadA (S.oread j) (S.oc j x) (outPoly (S.out j))
      (by simp only [BSpec.reads, List.mem_append, List.mem_map, List.mem_range]
          exact Or.inr ⟨j, hj', rfl⟩)
      rfl (S.oaddr_eval u hx (fun c a hc hcol => hfix c a hc hcol) hj') rfl (ho j hj')
    rw [evalB_eq, rowOf_out, hout _ hv] at h
    exact (FK.toBF64_injective h).symm

end Sound

/-! ## Completeness: the honest row -/

/-- The honest `FK` row of a word: `w`, then its bits. -/
def honest (w : FK) (i : Nat) : FK :=
  if i = 0 then w else if ubit w.val (i - 1) then 1 else 0

theorem lsum_honest (w : FK) : lsum (fun z => wt z * honest w (1 + z)) 64 = w := by
  have hb : ∀ z, honest w (1 + z) = if ubit w.val z then 1 else 0 := fun z => by
    simp [honest, show 1 + z ≠ 0 by omega, show 1 + z - 1 = z by omega]
  have key : (lsum (fun z => wt z * honest w (1 + z)) 64).val = w.val := by
    apply u64_ext
    intro i hi
    apply Bool.eq_iff_iff.mpr
    rw [ubit_lsum _ (fun z => ubit w.val z) id i 64 (fun z hz => by
        rw [hb, wt, ubit_mul_bit _ (by split <;> simp), ubit_one_shl hz]
        have h01 : ((0 : FK) = 1) ↔ False := by decide
        by_cases hz' : ubit w.val z = true <;> simp [hz', h01, @eq_comm _ i z])
      (fun z _ z' _ _ _ h => h)]
    exact ⟨fun ⟨z, _, h1, h2⟩ => h2 ▸ h1, fun h1 => ⟨i, hi, h1, rfl⟩⟩
  exact congrArg FK.mk key

/-- **Completeness of the row**: the honest row of any word satisfies the constraints. -/
theorem honest_cons (w : FK) : ∀ C ∈ cons, evalK (honest w) C = 0 := by
  intro C hC
  simp only [cons, List.mem_cons, List.mem_map, List.mem_range] at hC
  rcases hC with rfl | ⟨z, -, rfl⟩
  · rw [evalK_wcons, lsum_honest]
    show w + w = 0
    exact CharTwo.add_self_eq_zero w
  · rw [evalK_bcons]
    have : honest w (1 + z) = 0 ∨ honest w (1 + z) = 1 := by
      simp only [honest, show 1 + z ≠ 0 by omega, if_false]; split <;> simp
    rcases this with h | h <;> rw [h] <;> decide

/-- **Completeness of the outputs**: on the honest row every output polynomial is the output's
word function. -/
theorem honest_out (w : FK) {o : BOut} (ho : o.Valid) : evalK (honest w) (outPoly o) = ⟨o.word w.val⟩ := by
  rw [rowOf_out, (row_sound (rowOf_cons (honest_cons w))).2 o ho]
  rfl

/-- **The honest table row satisfies the table** (as `aux_cons` reads it): on the honest row of any
word, every constraint of every `BITS` table vanishes and every output read's value polynomial is
the output's word function. -/
theorem honest_tab (S : BSpec) (w : FK) :
    (∀ C ∈ S.tab.cons, CPoly.evalB (fun i => FK.toBF64 (honest w i)) C = 0) ∧
      ∀ j < S.outs.length, (S.out j).Valid →
        CPoly.evalB (fun i => FK.toBF64 (honest w i)) (outPoly (S.out j)) =
          FK.toBF64 ⟨(S.out j).word w.val⟩ := by
  refine ⟨fun C hC => ?_, fun j _ hv => ?_⟩
  · rw [evalB_eq]
    simp only [FK.ofBF64_toBF64]
    rw [honest_cons w C hC]; rfl
  · rw [evalB_eq]
    simp only [FK.ofBF64_toBF64]
    rw [honest_out w hv]

end Lvm.BitsTab
