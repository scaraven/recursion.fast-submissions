-- New for lvm6 (WP MBT). The deployed mini-bus tables of the node circuit: season 1's seed arrays (`mbArrs`,
-- `InArr.tab`) over the cap regions of `opensP18` at stride 1, and its read tables (`readTab`) of `Q_link`'s cap
-- `readd` rows, with their static facts (`AllSc`, `KeysOk`, `FixOk`, `mbLinB6`, `τ ≤ μ`, `LayOk`, `μBus`).
-- Phase 2: parametric over `MbPar` (the stream base, `C_main`'s size, the count words, the region targets); it no
-- longer imports `Lvm6NodeDeploy`, which instantiates it (`mbPar6`) and builds the circuit's tables from it.
import Lvm6QLinkP18
import Lvm6NodeStmt
import Lvm6QDStmt
import LvmTypedLayQ
import LvmM3FidFix
import LvmM3Fid
import Lvm6MbProg
import Lvm6P18Memo
import Lvm6QFast

/-!
# The node's mini-bus tables (`mbTL`, WP MBT)

Only `Q_link`'s cap `readd`s are on the mini-bus: QLT's `readd`s are static (`mkLayI` aliases them), `BITS` rows are
auxiliary rows (`BSpec.tab` has constraints, which `mbLinB6` excludes).

* **`MbPar`**: the stream cell base `sb`, `C_main`'s log-size `nu`, the first count word `cnt0`, the region targets
  `tgt`; **`MbPar.Ok`** its static conditions (alignment and room for the count words).
* **Seeds** (`seedTabs6 P`): per aligned block `q` of `2^4` stream lanes meeting a cap region `[capL, capL + 4·2^c)`
  of an opening (`capRegs6`), once, an `InArr` over the stream cells `sb + 16q + x`; its value column is the
  stream's stack words `streamIdx (16q) + x` (slot 33, stride 1), its finalize column `fin6 P i`.
* **Reads** (`readTabs6 P wa wv`): per opening, per chunk `c` of `pchunks t` and each of `capTpl`'s four `readd`
  rows, a table of `2^c.2` rows (`capTaus6`); read `k`'s address and value columns are the stack words `wa k`, `wv k`
  of the `readd`'s address and result cells (`mbTL P Q lay`: `capReadRows Q`, `lay.wordK`, the `com` target),
  clamped to an aligned block (`alignW`: the layout's words are aligned, a misaligned word reads `0`), its count
  column `cnt6 P k`.
* **Facts** (every `P` with `P.Ok`, every `wa wv`): `mbTOf6_sc`, `_keys`, `_fix`, `_lin`, `_τ`, **`mbTOf6_layOk`**
  by structure; `mbStatic6` (one `decide +kernel` on `opensP18`: 76 seeds, 40 reads, `Σ 2^τ = 1000`, `τ ≤ 6`, blocks
  below `2^14`); `pushLeaves_mbTOf6`: `2216`, so **`mbTOf6_μBus`**: `μBus = clog₂ 2216 = 12 = miniDepth`.
-/

set_option autoImplicit false

namespace Lvm6.Node.Mb

open Lvm Lvm.M3 Lvm.Loop Lvm.QLink Lvm6.Q

/-! ## Parameters -/

/-- **The mini-bus's placement parameters.** -/
structure MbPar where
  /-- Stream word `j` is the `K` cell `sb + j`. -/
  sb : ℕ
  /-- `C_main` has `2^nu` words. -/
  nu : ℕ
  /-- The first count word. -/
  cnt0 : ℕ
  /-- A word region's stack target. -/
  tgt : Typed.YReg → ℕ

/-! ## Placements -/

/-- The cap regions `(first stream lane, cap bits)` of the openings (`openLoops6`' `capL`, `h − path`). -/
def capRegs6 : List (ℕ × ℕ) := opensP18.map fun o => (eLane6 Lvm6.Node.P6 o.ce + 1 + o.co / 8, o.h - o.path)

/-- The seed blocks' log-height. -/
abbrev mbBlk6 : ℕ := 4

/-- The seeded blocks `q` (lanes `[16q, 16q + 16)`), each once. -/
def seedBlocks6 : List ℕ :=
  (capRegs6.flatMap fun c => (List.range ((c.1 + 4 * 2 ^ c.2 - 1) / 2 ^ mbBlk6 + 1 - c.1 / 2 ^ mbBlk6)).map
    fun i => c.1 / 2 ^ mbBlk6 + i).eraseDups

/-- The read tables' log-heights: per opening, per chunk, four (`capTpl`'s `readd` rows). -/
def capTaus6 : List ℕ := opensP18.flatMap fun o => (pchunks o.t).flatMap fun c => List.replicate 4 c.2

/-- The read tables' largest log-height (`mbStatic6`). -/
abbrev mbτMax : ℕ := 6

/-- Seed `i`'s finalize column. -/
def fin6 (P : MbPar) (i : ℕ) : ℕ := P.cnt0 + 2 ^ mbBlk6 * i

/-- Read `k`'s count column. -/
def cnt6 (P : MbPar) (k : ℕ) : ℕ := P.cnt0 + 2 ^ 12 + 2 ^ mbτMax * k

/-- A read column's word, clamped to an aligned block of `C_main` (`0` otherwise). -/
def alignW (P : MbPar) (τ y : ℕ) : ℕ := if 2 ^ τ ∣ y ∧ y + 2 ^ τ ≤ 2 ^ P.nu then y else 0

/-- **Seed array `i`** over block `q`. -/
def seedArr6 (P : MbPar) (i q : ℕ) : InArr :=
  ⟨.K, mbBlk6, P.sb + 2 ^ mbBlk6 * q, 1, [(false, QD.streamIdx (2 ^ mbBlk6 * q))], (false, fin6 P i), none⟩

/-- The seed tables. -/
def seedTabs6 (P : MbPar) : List Tab := seedBlocks6.zipIdx.map fun x => (seedArr6 P x.2 x.1).tab

/-- The read tables, read `k`'s address and value columns at `wa k`, `wv k` (clamped). -/
def readTabs6 (P : MbPar) (wa wv : ℕ → ℕ) : List Tab :=
  capTaus6.zipIdx.map fun x => QTyped.readTab x.1 (alignW P x.1 (wa x.2)) (alignW P x.1 (wv x.2)) (cnt6 P x.2)

/-- **The mini-bus's tables**: the seeds, then the reads. -/
def mbTOf6 (P : MbPar) (wa wv : ℕ → ℕ) : List Tab := seedTabs6 P ++ readTabs6 P wa wv

/-! ## The deployed words of the reads -/

/-- The stack word of word `y` of source `s` (its region's target plus its offset; `0` outside). -/
def regW6 (P : MbPar) (lay : Typed.Lay) (s : Typed.YSrc) (y : ℕ) : ℕ :=
  match lay.yregs.find? (fun r => r.src == s && decide (r.base ≤ y ∧ y < r.base + 2 ^ r.log)) with
  | some r => P.tgt r + (y - r.base)
  | none => 0

/-- The stack words `(address, value)` of each cap `readd` (`capReadRows`' order, iteration `0`). -/
def capWords6 (P : MbPar) (Q : Program) (lay : Typed.Lay) : Array (ℕ × ℕ) :=
  ((QTyped.capReadRows Q).map fun x =>
    (regW6 P lay .com (lay.wordK (QTyped.adrCell Q x.1 x.2 0)),
      regW6 P lay .com (lay.wordK (QTyped.resCell Q x.1 x.2 0)))).toArray

/-- **The deployed mini-bus tables of a program and its layout** (the exporter prints them as `MINIBUS`). -/
def mbTL (P : MbPar) (Q : Program) (lay : Typed.Lay) : List Tab :=
  let cw := capWords6 P Q lay
  mbTOf6 P (fun k => (cw.getD k (0, 0)).1) (fun k => (cw.getD k (0, 0)).2)

/-- **R7's `MINIBUS` lines** (`prover-src/crates/r3typed/EXPORT.md`, without the header `MINIBUS 76 40`): per seed
`limbs base stride tau v_0 fin`, then per read `limbs tau addr v_0 cnt`, in `mbTL P Q lay`'s table order, with the
same placements (`seedArr6`, `capWords6` clamped by `alignW`, `fin6`, `cnt6`). -/
def minibusLines (P : MbPar) (Q : Program) (lay : Typed.Lay) : List String :=
  let cw := capWords6 P Q lay
  (seedBlocks6.zipIdx.map fun x =>
    let a := seedArr6 P x.2 x.1
    s!"1 {a.base} {a.stride} {a.τ} {QD.streamIdx (2 ^ mbBlk6 * x.1)} {fin6 P x.2}") ++
  (capTaus6.zipIdx.map fun x =>
    s!"1 {x.1} {alignW P x.1 (cw.getD x.2 (0, 0)).1} {alignW P x.1 (cw.getD x.2 (0, 0)).2} {cnt6 P x.2}")

/-! ## The plan's static facts (one kernel evaluation) -/

/-- **The tables' static shape** at `P18`. -/
structure MbStatic : Prop where
  nSeeds : seedBlocks6.length = 76
  nReads : capTaus6.length = 40
  readLeaves : (capTaus6.map (2 ^ ·)).sum = 1000
  τle : ∀ τ ∈ capTaus6, τ ≤ mbτMax
  seedLt : ∀ q ∈ seedBlocks6, q < 2 ^ 14

/-- `MbStatic` as one Boolean. -/
def mbStaticB : Bool :=
  decide (seedBlocks6.length = 76) && decide (capTaus6.length = 40) && decide ((capTaus6.map (2 ^ ·)).sum = 1000) &&
    capTaus6.all (fun τ => decide (τ ≤ mbτMax)) && seedBlocks6.all (fun q => decide (q < 2 ^ 14))

/-- **The node's static Booleans over `opensP18` and the plan, as one** (KDN): `mbStaticB`, every opening's
`0 < per` (`Asm.opens_per`) and every plan grind `≤ 64` (`Dep.powG64B_P18`). One `decide +kernel` evaluates
`opensP18` and `P6` once for the three (the kernel's caches are per declaration). -/
def nodeStaticB : Bool :=
  mbStaticB && opensP18.all (fun o ↦ decide (0 < o.per)) &&
    Lvm6.Node.P6.all fun e ↦ match e.k with
      | .fs _ g => decide (g ≤ 64)
      | _ => true

/-- `nodeStaticB` with the plan `P` and the openings `O` as parameters (KDN): at `planOf P18` and `opensP18` it is
`nodeStaticB` by unfolding, at KDQ's literals `planP18`, `opensTabP18` the kernel evaluates it without rebuilding
the plan. -/
def nodeStaticG (P : List PE6) (O : List Open6Q) : Bool :=
  let regs := O.map fun o => (eLane6 P o.ce + 1 + o.co / 8, o.h - o.path)
  let seeds := (regs.flatMap fun c => (List.range ((c.1 + 4 * 2 ^ c.2 - 1) / 2 ^ mbBlk6 + 1 - c.1 / 2 ^ mbBlk6)).map
    fun i => c.1 / 2 ^ mbBlk6 + i).eraseDups
  let taus := O.flatMap fun o => (pchunks o.t).flatMap fun c => List.replicate 4 c.2
  (decide (seeds.length = 76) && decide (taus.length = 40) && decide ((taus.map (2 ^ ·)).sum = 1000) &&
    taus.all (fun τ => decide (τ ≤ mbτMax)) && seeds.all (fun q => decide (q < 2 ^ 14))) &&
    O.all (fun o ↦ decide (0 < o.per)) &&
    P.all fun e ↦ match e.k with
      | .fs _ g => decide (g ≤ 64)
      | _ => true

theorem nodeStaticG_lit : nodeStaticG planP18 opensTabP18 = true := by decide +kernel

theorem nodeStaticB_true : nodeStaticB = true := by
  have h := nodeStaticG_lit
  rw [← planOf_P18_eq, ← opens6_P18] at h
  exact h

theorem mbStaticB_true : mbStaticB = true :=
  (Bool.and_eq_true _ _).mp ((Bool.and_eq_true _ _).mp nodeStaticB_true).1 |>.1

/-- **The static shape** (from `mbStaticB_true`, i.e. `nodeStaticB_true`: one kernel evaluation of the tables). -/
theorem mbStatic6 : MbStatic := by
  have h := mbStaticB_true
  simp only [mbStaticB, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true] at h
  exact ⟨h.1.1.1.1, h.1.1.1.2, h.1.1.2, h.1.2, h.2⟩

/-- **The parameters' static conditions.** -/
structure MbPar.Ok (P : MbPar) : Prop where
  /-- The read columns' clamp target `0` holds a block of `2^6`. -/
  nuGe : mbτMax ≤ P.nu
  /-- The seeds' stream words fit (`seedLt`: blocks below `2^14`). -/
  seedFit : QD.streamIdx (2 ^ mbBlk6 * 2 ^ 14) ≤ 2 ^ P.nu
  /-- The finalize columns: aligned, inside. -/
  finAl : 2 ^ mbBlk6 ∣ P.cnt0
  finFit : P.cnt0 + 2 ^ mbBlk6 * 76 ≤ 2 ^ P.nu
  /-- The count columns: aligned, inside. -/
  cntAl : 2 ^ mbτMax ∣ P.cnt0 + 2 ^ 12
  cntFit : P.cnt0 + 2 ^ 12 + 2 ^ mbτMax * 40 ≤ 2 ^ P.nu

/-! ## Static facts (every `P`, every `wa wv`) -/

section Facts

variable (P : MbPar) (wa wv : ℕ → ℕ)

theorem mem_mbTOf6 {t : Tab} (ht : t ∈ mbTOf6 P wa wv) :
    (∃ i q, t = (seedArr6 P i q).tab ∧ i < seedBlocks6.length ∧ q ∈ seedBlocks6) ∨
      ∃ τ k, t = QTyped.readTab τ (alignW P τ (wa k)) (alignW P τ (wv k)) (cnt6 P k) ∧ τ ∈ capTaus6 ∧
        k < capTaus6.length := by
  rcases List.mem_append.mp ht with h | h
  · obtain ⟨x, hx, rfl⟩ := List.mem_map.mp h
    -- `Nat.add_zero` by rewriting, not by unfolding: a closed `l.length + 0` against `l.length` would make the
    -- kernel evaluate `seedBlocks6` (KDN).
    have hi := List.snd_lt_of_mem_zipIdx hx
    rw [Nat.add_zero] at hi
    exact Or.inl ⟨_, _, rfl, hi, List.fst_mem_of_mem_zipIdx hx⟩
  · obtain ⟨x, hx, rfl⟩ := List.mem_map.mp h
    have hk := List.snd_lt_of_mem_zipIdx hx
    rw [Nat.add_zero] at hk
    exact Or.inr ⟨_, _, rfl, List.fst_mem_of_mem_zipIdx hx, hk⟩

/-- Every table reads or seeds. -/
theorem mbTOf6_sc : AllSc (mbTOf6 P wa wv) := by
  intro t ht
  rcases mem_mbTOf6 P wa wv ht with ⟨i, q, rfl, -, -⟩ | ⟨τ, k, rfl, -, -⟩
  · exact Or.inr (by simp [InArr.tab])
  · exact Or.inl (by simp [QTyped.readTab])

/-- Every key has one value limb. -/
theorem mbTOf6_keys : KeysOk (mbTOf6 P wa wv) := by
  intro t ht
  rcases mem_mbTOf6 P wa wv ht with ⟨i, q, rfl, -, -⟩ | ⟨τ, k, rfl, -, -⟩
  · refine ⟨fun r hr => by simp [InArr.tab] at hr, fun s hs => ?_⟩
    simp only [InArr.tab, List.mem_singleton] at hs
    subst hs; simp [seedArr6]
  · refine ⟨fun r hr => ?_, fun s hs => by simp [QTyped.readTab] at hs⟩
    simp only [QTyped.readTab, List.mem_singleton] at hr
    subst hr; simp [QTyped.readKey]

/-- **`FixOk`**: a seed's address column is its closed form (`inArr_eval_eq`); reads have no fixed column. -/
theorem mbTOf6_fix : FixOk (mbTOf6 P wa wv) := by
  intro t ht f ev hfe r hr
  rcases mem_mbTOf6 P wa wv ht with ⟨i, q, rfl, -, -⟩ | ⟨τ, k, rfl, -, -⟩
  · simp only [InArr.tab, seedArr6, InArr.vcols, List.map_cons, List.map_nil, List.cons_append,
      List.nil_append, List.mem_cons, List.not_mem_nil, or_false, reduceCtorEq, false_or,
      ColSrc.fix.injEq] at hfe
    obtain ⟨rfl, rfl⟩ := hfe
    exact inArr_eval_eq (seedArr6 P i q) r
  · simp [QTyped.readTab] at hfe

/-- **Tableless** (`mbLinB6`): no constraint, keys of single columns, every committed column on `C_main`. -/
theorem mbTOf6_lin : Lvm6.Mb.mbLinB6 (mbTOf6 P wa wv) = true := by
  simp only [Lvm6.Mb.mbLinB6, List.all_eq_true]
  intro t ht
  rcases mem_mbTOf6 P wa wv ht with ⟨i, q, rfl, -, -⟩ | ⟨τ, k, rfl, -, -⟩
  · simp [InArr.tab, seedArr6, InArr.vcols, Lvm6.Mb.cpolyLinB, CPoly.var]
  · simp [QTyped.readTab, QTyped.readKey, Lvm6.Mb.cpolyLinB, CPoly.var]

/-- Every table is at most `2^6` high. -/
theorem mbTOf6_τ : ∀ t ∈ mbTOf6 P wa wv, t.τ ≤ mbτMax := by
  intro t ht
  rcases mem_mbTOf6 P wa wv ht with ⟨i, q, rfl, -, -⟩ | ⟨τ, k, rfl, hτ, -⟩
  · simp [InArr.tab, seedArr6, mbBlk6, mbτMax]
  · exact mbStatic6.τle τ hτ

theorem alignW_ok (P : MbPar) {τ : ℕ} (hτ : τ ≤ P.nu) (y : ℕ) :
    2 ^ τ ∣ alignW P τ y ∧ alignW P τ y + 2 ^ τ ≤ 2 ^ P.nu := by
  unfold alignW
  split
  · rename_i h; exact h
  · exact ⟨dvd_zero _, by simpa using Nat.pow_le_pow_right (by norm_num : 0 < 2) hτ⟩

/-- **`LayOk`** on a stack with `C_main` of `2^nu` words: every committed column is an aligned block, by
construction (the seeds' and counts' placements by `P.Ok`, the read columns by `alignW`). -/
theorem mbTOf6_layOk {P : MbPar} (hP : P.Ok) (L : Lay) (hL : L.nuMain = P.nu) (hr : L.nuRec ≤ L.nuMain) :
    LayOk L (mbTOf6 P wa wv) := by
  intro t ht c hc
  unfold Aligned
  rw [hL] at hr
  rcases mem_mbTOf6 P wa wv ht with ⟨i, q, rfl, hi, hq⟩ | ⟨τ, k, rfl, hτ, hk⟩
  · have hq' := mbStatic6.seedLt q hq
    have hi' : i < 76 := mbStatic6.nSeeds ▸ hi
    have hs := hP.seedFit
    have hfa := hP.finAl
    have hff := hP.finFit
    simp only [InArr.tab, seedArr6, InArr.vcols, List.map_cons, List.map_nil, List.cons_append,
      List.nil_append, Tab.w, List.length_cons, List.length_nil] at hc ⊢
    simp only [QD.streamIdx, QD.recSlot, fin6, mbBlk6] at hs hfa hff ⊢
    rcases c with _ | _ | _ | c
    · simp only [List.getElem?_cons_zero, Bool.false_eq_true, ↓reduceIte]
      rw [hL]
      generalize 2 ^ P.nu = N at hs ⊢
      simp only [show (2 : ℕ) ^ 4 = 16 from rfl, show (2 : ℕ) ^ 14 = 16384 from rfl,
        show (2 : ℕ) ^ 19 = 524288 from rfl] at hs hq' ⊢
      exact ⟨by omega, by omega, hr⟩
    · simp only [List.getElem?_cons_succ, List.getElem?_cons_zero, Bool.false_eq_true, ↓reduceIte]
      rw [hL]
      generalize 2 ^ P.nu = N at hff ⊢
      simp only [show (2 : ℕ) ^ 4 = 16 from rfl] at hfa hff ⊢
      exact ⟨by omega, by omega, hr⟩
    · simp
    · omega
  · have hτ' := mbStatic6.τle τ hτ
    have hk' : k < 40 := mbStatic6.nReads ▸ hk
    have hng := hP.nuGe
    have hca := hP.cntAl
    have hcf := hP.cntFit
    have hdv : 2 ^ τ ∣ 2 ^ mbτMax := Nat.pow_dvd_pow 2 hτ'
    have h2 : 2 ^ τ ≤ 2 ^ mbτMax := Nat.pow_le_pow_right (by norm_num) hτ'
    have hal := alignW_ok P (hτ'.trans hng)
    simp only [QTyped.readTab, Tab.w, List.length_cons, List.length_nil] at hc ⊢
    rw [hL]
    rcases c with _ | _ | _ | c
    · simp only [List.getElem?_cons_zero, Bool.false_eq_true, ↓reduceIte]
      exact ⟨(hal _).1, (hal _).2, hr⟩
    · simp only [List.getElem?_cons_succ, List.getElem?_cons_zero, Bool.false_eq_true, ↓reduceIte]
      exact ⟨(hal _).1, (hal _).2, hr⟩
    · simp only [List.getElem?_cons_succ, List.getElem?_cons_zero, Bool.false_eq_true, ↓reduceIte, cnt6]
      refine ⟨Nat.dvd_add (hdv.trans hca) (Dvd.dvd.mul_right hdv k), ?_, hr⟩
      have : 2 ^ mbτMax * (k + 1) ≤ 2 ^ mbτMax * 40 := Nat.mul_le_mul_left _ (by omega)
      rw [Nat.mul_add, mul_one] at this
      omega
    · omega

/-! ## The depth -/

/-- **The push leaves**: `76·2^4 + 1000 = 2216`, whatever the read columns' words. -/
theorem pushLeaves_mbTOf6 :
    ((mbTOf6 P wa wv).map fun t ↦ (t.reads.length + t.seeds.length) * 2 ^ t.τ).sum = 2216 := by
  have hs : ((seedTabs6 P).map fun t ↦ (t.reads.length + t.seeds.length) * 2 ^ t.τ) =
      List.replicate seedBlocks6.length 16 := by
    simp only [seedTabs6, List.map_map]
    rw [List.eq_replicate_iff]
    refine ⟨by simp, fun n hn => ?_⟩
    obtain ⟨x, -, rfl⟩ := List.mem_map.mp hn
    simp [InArr.tab, seedArr6, mbBlk6]
  have hr : ((readTabs6 P wa wv).map fun t ↦ (t.reads.length + t.seeds.length) * 2 ^ t.τ) =
      capTaus6.map (2 ^ ·) := by
    simp only [readTabs6, List.map_map]
    conv_rhs => rw [← List.zipIdx_map_fst 0 capTaus6]
    rw [List.map_map]
    exact List.map_congr_left fun x _ => by simp [QTyped.readTab]
  rw [mbTOf6, List.map_append, List.sum_append, hs, hr, mbStatic6.readLeaves, mbStatic6.nSeeds,
    List.sum_replicate, smul_eq_mul]

/-- The push leaves of the lvm instance, table by table (season 1's `LvmVEqFit.pushLeaves_inst`). -/
theorem pushLeaves_inst (L : Lay) (T : List Tab) (hτ : ∀ t ∈ T, t.τ ≤ L.μ) :
    (inst L T hτ).pushLeaves = (T.map fun t ↦ (t.reads.length + t.seeds.length) * 2 ^ t.τ).sum := by
  have e : ∀ j : Fin T.length, (((inst L T hτ).flushes j).filter fun f ↦ decide (f.1 = LeanVM.Protocol.Side.push)).length *
      2 ^ (inst L T hτ).τ j = (fun t : Tab ↦ (t.reads.length + t.seeds.length) * 2 ^ t.τ) (T.get j) :=
    fun j ↦ congrArg (· * 2 ^ (T.get j).τ) (flushes_push_length (T.get j))
  simp only [LeanVM.Protocol.M3Instance.pushLeaves, List.filter_nil, List.map_nil, List.sum_nil, zero_add]
  rw [List.map_congr_left fun j _ ↦ e j]
  exact congrArg List.sum ((List.map_map (g := fun t : Tab ↦ (t.reads.length + t.seeds.length) * 2 ^ t.τ)
    (f := T.get) (l := List.finRange T.length)).symm.trans (by rw [List.map_get_finRange]))

/-- **The mini-bus's depth is `miniDepth`** (`clog₂ 2216 = 12`), on every stack and every read placement. -/
theorem mbTOf6_μBus (L : Lay) (hτ : ∀ t ∈ mbTOf6 P wa wv, t.τ ≤ L.μ) :
    (inst L (mbTOf6 P wa wv) hτ).μBus = Lvm6.Mb.miniDepth := by
  rw [LeanVM.Protocol.M3Instance.μBus, pushLeaves_inst, pushLeaves_mbTOf6]
  decide

end Facts

end Lvm6.Node.Mb
