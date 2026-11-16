-- New for lvm (WP-8): ring switching on a block column with a carried predicate, and a zero test over
-- challenges. Adapted from leanVM `EndToEnd/Front/RingSwitch.lean` as ported by WP-2 (`LvmRingSwitch`:
-- `RingAlive`, `ring_escape`, `ring_start`, `ring_end`, `ringSpecOf`), with the leanISA stack and
-- `ColumnClaimsHold` replaced by a column accessor and an arbitrary carried predicate `R`.
import LvmRingFidelity
import LvmKeccakRounds
import LvmKeccakGkr
import LvmClaims
import LvmEqLemmas
import LvmLayoutArith
import LvmSpineKeccakZero
import LvmSpecRulesBasic

-- ===== merged from `LvmKeccakBridge` (GOLF module merge: `LvmKeccakBridge.lean` is now a stub importing `LvmKeccakCallerRing`) =====
section
-- Ported from leanVM (formal rev 40f877dc) for lvm (WP-2) as `LvmKeccakBridge`: the generic parts of
-- `EndToEnd/Sound/Returns.lean` (the return invariant `RetOK`, lines 46-107), of
-- `EndToEnd/Front/LayoutBridgeB.lean` (`castColumn`, `holds_castColumn`, `sum_eqEval_mul`, lines
-- 37-56) and of `EndToEnd/Front/KeccakBridge.lean` (the returns of the Keccak reduction and the
-- equality weights, lines 57-234). Cut (leanISA): `retOK_verifyBusBalance` ... `retOK_publicInputPhase`
-- of Returns, the candidate reading of LayoutBridgeB (`toI`, `WireHolds`, ...), and from KeccakBridge
-- line 235 on (`q_keccak` on a leanISA candidate, `tablePost_pubPre`, `keccakPhaseSpec`): the Keccak
-- phase spec over the leanISA layout. lvm's Keccak phase (caller claims, WP-8) uses `gkrSpec`
-- (`LvmKeccakGkr`) directly.

namespace LeanVM.Protocol.EndToEnd.Sound

open LeanVM.Parameters LeanVM.Protocol.Compile LeanVM.Protocol.Verifier

section

variable {α β : Type}

variable {α β : Type}

/-! ## The return invariant -/

/-- Every return of `p` satisfies `Q`. -/
def RetOK (Q : α → Prop) (p : VerifierProgram α) : Prop :=
  ∀ (l : List Ev) (a : α), p.after l = some (.ret a) → Q a

/-- A weaker predicate holds of every return. -/
theorem RetOK.mono {Q Q' : α → Prop} {p : VerifierProgram α} (h : RetOK Q p) (hQ : ∀ a, Q a →
    Q' a) :
    RetOK Q' p :=
  fun l a hl ↦ hQ a (h l a hl)

/-- A program that returns at once returns its value. -/
theorem RetOK.ret {Q : α → Prop} {a : α} (h : Q a) : RetOK Q (VerifierProgram.ret a) := by
  intro l b hl
  cases l with
  | nil =>
    simp only [VerifierProgram.after, Option.some.injEq, VerifierProgram.ret.injEq] at hl
    exact hl ▸ h
  | cons e l => cases e <;> simp [VerifierProgram.after] at hl

/-- A rejecting program returns nothing. -/
theorem RetOK.fail {Q : α → Prop} : RetOK Q (VerifierProgram.fail : VerifierProgram α) := by
  intro l b hl
  cases l with
  | nil => simp [VerifierProgram.after] at hl
  | cons e l => cases e <;> simp [VerifierProgram.after] at hl

/-- The trivial predicate holds of every return. -/
theorem RetOK.true (p : VerifierProgram α) : RetOK (fun _ ↦ True) p :=
  fun _ _ _ ↦ trivial

/-- A sequence that returns at once: both parts return. -/
private theorem bind_eq_ret' {p : VerifierProgram α} {f : α → VerifierProgram β} {b : β} (h : p.bind
    f = .ret b) :
    ∃ a, p = .ret a ∧ f a = .ret b := by
  cases p <;> simp_all [VerifierProgram.bind]

/-- A sequence returns what its continuation returns on a return of its first part. -/
theorem RetOK.bind {Q' : α → Prop} {Q : β → Prop} {p : VerifierProgram α} {f : α →
    VerifierProgram β}
    (hp : RetOK Q' p) (hf : ∀ a, Q' a → RetOK Q (f a)) : RetOK Q (p.bind f) := by
  intro l b hl
  rcases VerifierProgram.after_bind_cases f hl with ⟨q, hq, hr⟩ | ⟨a, l₁, l₂, -, h1, -, h2⟩
  · obtain ⟨a, rfl, hfa⟩ := bind_eq_ret' hr.symm
    exact hf a (hp l a hq) [] b (by simp [VerifierProgram.after, hfa])
  · exact hf a (hp l₁ a h1) l₂ b h2

/-- A sequence whose continuation's returns satisfy `Q` whatever the first part returns. -/
theorem RetOK.bind_true {Q : β → Prop} {p : VerifierProgram α} {f : α → VerifierProgram β}
    (hf : ∀ a, RetOK Q (f a)) : RetOK Q (p.bind f) :=
  (RetOK.true p).bind fun a _ ↦ hf a

/-- `readN n` returns `n` scalars. -/
theorem RetOK.readN : ∀ n : ℕ, RetOK (fun xs : List E ↦ xs.length = n)
    (VerifierProgram.readScalars n)
  | 0 => RetOK.ret rfl
  | n + 1 => RetOK.bind_true fun _ ↦ (RetOK.readN n).bind fun xs hxs ↦
      RetOK.ret (by simp [hxs])


end

end LeanVM.Protocol.EndToEnd.Sound

namespace LeanVM.Protocol.EndToEnd.Front

open LeanVM.Parameters LeanVM.Semantics LeanVM.Protocol LeanVM.Protocol.Compile
open LeanVM.Protocol.Verifier CompPoly CMlPolynomialEval
open LeanVM.Protocol.EndToEnd.Sound (RetOK RetOK.ret RetOK.bind RetOK.bind_true)
open Finset
open scoped NNReal ENNReal

section

/-! ## Stacks on equal numbers of variables -/

/-- A stack on `a` variables read on `b = a`. -/
def castColumn {a b : ℕ} (h : a = b) (q : Column a) : Column b :=
  ⟨Vector.cast (congrArg (2 ^ ·) h) q.values⟩

/-- A stack claim holds of a stack exactly when it holds of the stack read on equal variables. -/
theorem holds_castColumn {a b : ℕ} (h : a = b) (c : StackClaim) (q : Column a) :
    StackClaim.Holds a c q ↔ StackClaim.Holds b c (castColumn h q) := by
  subst h
  simp [castColumn]

/-- Pairing the equality weight of `z` with a stack is the stack's extension at `z`. -/
theorem sum_eqEval_mul {μ : ℕ} (z : Vector E μ) (q : Column μ) :
    ∑ x : Fin (2 ^ μ), eqEval z.toList (boolPoint μ x) * ofK (q.values.getD x 0) =
      eval₂Mle q.values (algebraMap K E) z := by
  rw [eval₂Mle, evalMle_eq_sum]
  refine Finset.sum_congr rfl fun x _ ↦ ?_
  rw [eqEval_boolPoint, mul_comm]
  simp [CMlPolynomialEval.map, Vector.getD, x.isLt]


/-- A sumcheck returns one challenge per round. -/
theorem retOK_sumcheck (count : ℕ) : ∀ (eqs : List (Option E)) (claim : E),
    RetOK (fun r : List E × E ↦ r.1.length = eqs.length) (Verifier.sumcheck claim count eqs)
  | [], _ => RetOK.ret rfl
  | _ :: eqs, _ => RetOK.bind_true fun _ ↦ RetOK.bind_true fun _ ↦
      (retOK_sumcheck count eqs _).bind fun r hr ↦ RetOK.ret (by simp [hr])

/-- `keccak_open` returns a slot of six challenges. -/
theorem retOK_keccakOpen (logSteps : ℕ) (claim : KeccakClaim) (first count : ℕ) (value : E) :
    RetOK (fun r : List E × List E × E ↦ r.1.length = qkeccakSlotBits)
      (keccakOpen logSteps claim first count value) :=
  (retOK_sumcheck 3 _ value).bind fun r hr ↦ RetOK.ret (by simpa using hr)

/-- **The Keccak reduction's column claims are on `QKECCAK`**, at `|inst| + 6` coordinates when
`inst` has at least four. -/
theorem retOK_verifyKeccak (logSteps : ℕ) (inst output : List E) (hi : 4 ≤ inst.length) :
    RetOK (fun r : List Verifier.ColumnClaim × List E × List E ↦
      ∀ c ∈ r.1, c.column = qkeccak ∧ c.point.length = inst.length + 6)
      (verifyKeccak logSteps inst output) := by
  unfold verifyKeccak
  refine RetOK.bind_true fun _ ↦ RetOK.bind_true fun _ ↦ RetOK.bind_true fun _ ↦
    RetOK.bind_true fun _ ↦ ?_
  simp only [show 1 < keccakSegments from by decide, ↓reduceIte]
  refine (retOK_keccakOpen _ _ _ _ _).bind fun r hr ↦ ?_
  obtain ⟨slot, weights, value⟩ := r
  refine RetOK.bind_true fun _ ↦ RetOK.bind_true fun _ ↦
    (RetOK.ret (Q := fun cs : List Verifier.ColumnClaim ↦
      ∀ c ∈ cs, c.column = qkeccak ∧ c.point.length = inst.length + 6) ?_).bind fun cs hcs ↦ ?_
  · intro c hc
    simp only [List.mem_singleton] at hc
    subst hc
    refine ⟨rfl, ?_⟩
    simp only [List.length_append, List.length_take, List.length_drop]
    rw [show (slot, weights, value).1 = slot from rfl] at hr
    rw [hr, show qkeccakSlotBits = 6 by decide]
    (clear * - hi; omega)
  · refine RetOK.bind_true fun r ↦ ?_
    obtain ⟨low, v⟩ := r
    refine RetOK.bind_true fun r ↦ ?_
    obtain ⟨slot', weights', value'⟩ := r
    exact RetOK.bind_true fun _ ↦ RetOK.bind_true fun _ ↦ RetOK.ret hcs

/-- The Keccak reduction returns one column claim. -/
theorem retOK_verifyKeccak_count (logSteps : ℕ) (inst output : List E) :
    RetOK (fun r : List Verifier.ColumnClaim × List E × List E ↦ r.1.length ≤ 1)
      (verifyKeccak logSteps inst output) := by
  unfold verifyKeccak
  refine RetOK.bind_true fun _ ↦ RetOK.bind_true fun _ ↦ RetOK.bind_true fun _ ↦
    RetOK.bind_true fun _ ↦ ?_
  simp only [show 1 < keccakSegments from by decide, ↓reduceIte]
  refine RetOK.bind_true fun r ↦ ?_
  obtain ⟨slot, weights, value⟩ := r
  refine RetOK.bind_true fun _ ↦ RetOK.bind_true fun _ ↦
    (RetOK.ret (Q := fun cs : List Verifier.ColumnClaim ↦ cs.length ≤ 1) (by simp)).bind
      fun cs hcs ↦ ?_
  refine RetOK.bind_true fun r ↦ ?_
  obtain ⟨low, v⟩ := r
  refine RetOK.bind_true fun r ↦ ?_
  obtain ⟨slot', weights', value'⟩ := r
  exact RetOK.bind_true fun _ ↦ RetOK.bind_true fun _ ↦ RetOK.ret hcs

-- lvm (WP-2): `retOK_keccakPhase` (leanISA's `keccakPhaseClaims`) is not ported.

/-- `sampleN n` returns `n` challenges. -/
theorem retOK_sampleN : ∀ n : ℕ, RetOK (fun xs : List E ↦ xs.length = n)
    (VerifierProgram.sampleChallenges n)
  | 0 => RetOK.ret rfl
  | n + 1 => RetOK.bind_true fun _ ↦ (retOK_sampleN n).bind fun xs hxs ↦
      RetOK.ret (by simp [hxs])

/-- The pack rounds return one challenge per coordinate of the point. -/
theorem retOK_keccakPackRounds : ∀ (rs : List E) (value scale : E),
    RetOK (fun r : E × E × List E ↦ r.2.2.length = rs.length) (keccakPackRounds rs value scale)
  | [], _, _ => RetOK.ret rfl
  | _ :: rs, _, _ => RetOK.bind_true fun _ ↦ RetOK.bind_true fun _ ↦
      (retOK_keccakPackRounds rs _ _).bind fun r hr ↦ RetOK.ret (by simp [hr])

/-- A layer keeps the length of the claim's point. -/
theorem retOK_verifyKeccakLayer (logSteps step : ℕ) (claim : KeccakClaim) :
    RetOK (fun c : KeccakClaim ↦ c.point.length = claim.point.length)
      (verifyKeccakLayer logSteps step claim) := by
  unfold verifyKeccakLayer
  refine RetOK.bind_true fun _ ↦ RetOK.bind_true fun _ ↦ RetOK.bind_true fun _ ↦ ?_
  refine (retOK_keccakPackRounds _ _ _).bind fun r hr ↦ ?_
  obtain ⟨value, scale, point⟩ := r
  refine RetOK.bind_true fun r ↦ ?_
  obtain ⟨localPoint, value'⟩ := r
  exact RetOK.bind_true fun _ ↦ RetOK.bind_true fun _ ↦ RetOK.bind_true fun _ ↦ RetOK.ret hr

/-- The layers keep the length of the claim's point. -/
theorem retOK_keccakLayers (logSteps : ℕ) : ∀ (steps : List ℕ) (claim : KeccakClaim),
    RetOK (fun c : KeccakClaim ↦ c.point.length = claim.point.length)
      (keccakLayers logSteps steps claim)
  | [], _ => RetOK.ret rfl
  | _ :: steps, _ => (retOK_verifyKeccakLayer _ _ _).bind fun c hc ↦
      (retOK_keccakLayers logSteps steps c).mono fun _ h ↦ h.trans hc

/-- **The Keccak reduction's point and slices**: the point it leaves for ring switching has
`|inst| + 6` coordinates, and it leaves 64 slices, when `inst` has at least four. -/
theorem retOK_verifyKeccak_point (logSteps : ℕ) (inst output : List E)
    (hi : 4 ≤ inst.length) (hl : inst.length = logSteps) :
    RetOK (fun r : List Verifier.ColumnClaim × List E × List E ↦
      r.2.1.length = inst.length + 6 ∧ r.2.2.length = 64)
      (verifyKeccak logSteps inst output) := by
  unfold verifyKeccak
  refine (retOK_sampleN _).bind fun segment hseg ↦ RetOK.bind_true fun _ ↦
    RetOK.bind_true fun _ ↦ ?_
  refine (retOK_keccakLayers _ _ _).bind fun claim hclaim ↦ ?_
  simp only [show 1 < keccakSegments from by decide, ↓reduceIte]
  refine RetOK.bind_true fun r ↦ ?_
  obtain ⟨slot, weights, value⟩ := r
  refine RetOK.bind_true fun _ ↦ RetOK.bind_true fun _ ↦ RetOK.bind_true fun _ ↦ ?_
  refine (retOK_sumcheck 3 _ _).bind fun r hr ↦ ?_
  obtain ⟨low, v⟩ := r
  refine (retOK_keccakOpen _ _ _ _ _).bind fun r hr' ↦ ?_
  obtain ⟨slot', weights', value'⟩ := r
  refine (RetOK.readN _).bind fun slices hs ↦ RetOK.bind_true fun _ ↦ RetOK.ret ⟨?_, ?_⟩
  · simp only [List.length_append, List.length_take] at hr hr' ⊢
    rw [hclaim]
    simp only [keccakFirstClaim, List.length_append, List.length_drop, List.length_replicate]
      at hr ⊢
    rw [hseg, hr, hr', show qkeccakSlotBits = 6 by decide,
      show keccakSegmentBits = 1 by decide]
    (clear * - hi hl; omega)
  · exact hs

/-! ## Equality weights -/

/-- The cube point of `x` on `n + 1` coordinates: bit `0`, then the cube point of `x / 2`. -/
theorem boolPoint_succ (n x : ℕ) :
    boolPoint (n + 1) x = (if x.testBit 0 then 1 else 0) :: boolPoint n (x / 2) := by
  simp only [boolPoint, List.range_succ_eq_map, List.map_cons, List.map_map]
  congr 1
  refine List.map_congr_left fun i _ ↦ ?_
  simp [Nat.testBit_succ]

/-- `eq_eval` at the cube point of `x` is the Keccak reduction's equality weight of `x`. -/
theorem eqAt_eq_eqEval : ∀ (pt : List E) (x : ℕ),
    KeccakGkr.eqAt pt x = eqEval pt (boolPoint pt.length x)
  | [], x => by simp [eqEval]
  | r :: rs, x => by
    rw [KeccakGkr.eqAt_cons, eqAt_eq_eqEval rs (x / 2), List.length_cons, boolPoint_succ,
      eqEval_eq_list_prod, eqEval_eq_list_prod, List.zipWith_cons_cons, List.prod_cons,
      Nat.testBit_zero]
    congr 1
    by_cases h : x % 2 = 1
    · simp only [h, ↓reduceIte, decide_true]
      rw [add_comm 1 r, add_assoc, CharTwo.add_self_eq_zero, add_zero]
    · simp [h]

/-- The table sumcheck's zero test weighs as the Keccak reduction (characteristic two). -/
theorem keccakZero_eqAt : ∀ (pt : List E) (x : ℕ), KeccakZero.eqAt pt x = KeccakGkr.eqAt pt x
  | [], _ => rfl
  | r :: rs, x => by
    rw [KeccakZero.eqAt, KeccakGkr.eqAt_cons, keccakZero_eqAt rs, CharTwo.sub_eq_add]

/-- **A column's extension** is the sum of its cells weighted by the equality weights of the
point. -/
theorem eval₂Mle_eq_sum_eqAt {n : ℕ} (v : Vector K (2 ^ n)) (z : Vector E n) :
    eval₂Mle v (algebraMap K E) z =
      ∑ x ∈ range (2 ^ n), KeccakGkr.eqAt z.toList x * ofK (v.getD x 0) := by
  rw [← sum_eqEval_mul z ⟨v⟩, Finset.sum_range]
  refine Finset.sum_congr rfl fun x _ ↦ ?_
  rw [eqAt_eq_eqEval, Vector.length_toList]

end

end LeanVM.Protocol.EndToEnd.Front
end
-- ===== end of `LvmKeccakBridge` =====

/-!
# Generic tools for the `CH`/`KS` phases

* `specWithRet`: a specification's postcondition strengthened by a fact every return satisfies
  (`RetOK`), e.g. the lengths `verifyKeccak` returns.
* `RingColTrue h col (target, W)`: the ring-switched claim on a `2^(h+6)`-word block column,
  `target = Σ_n W(n)·col(n)` (the claim V_S places as `⟨blk, ring.2, ring.1⟩`); **`ringCol_iff`**: it
  holds iff `Σ_i x^i Φ(s_i − ẑ_i(pt)) = 0` (leanVM's `ringClaim_holds_iff` on a block).
* **`ringColSpec`**: `ringSwitch pt sv` from doom of `slicesTrue ∧ R` to doom of `RingColTrue ∧ R`,
  six challenges at `L₀/|E|` each (leanVM's `ringSpecOf` with `R` for the column claims).
* `ZeroAlive`, **`zero_escape`**: a multilinear zero test with a carried predicate, `1/|E|` per
  coordinate (leanVM's `zt_escape`, any number of coordinates).
-/

set_option autoImplicit false

namespace Lvm.KG

open LeanVM.Parameters LeanVM.Protocol.Compile LeanVM.Protocol.Verifier LeanVM.Protocol.KeccakGkr
open LeanVM.Protocol.EndToEnd LeanVM.Protocol.EndToEnd.Front LeanVM.Protocol.EndToEnd.Sound
open LeanVM.Protocol.Ring Finset
open scoped ENNReal

/-! ## Returns -/

/-- A specification whose postcondition also states a fact of every return. -/
def specWithRet {α : Type} {p : VerifierProgram α} {Pre : List Ev → Prop}
    {Post : α → List Ev → Prop} {εmax L T : ℝ≥0∞} (S : Spec p Pre Post εmax L T) {Q : α → Prop}
    (hQ : RetOK Q p) : Spec p Pre (fun a h ↦ Q a ∧ Post a h) εmax L T :=
  { S with post := fun hl ha hD ↦ ⟨hQ _ _ ha, S.post hl ha hD⟩ }

/-! ## The ring claim on a block column -/

/-- **The ring-switched claim on a block column** of `2^(h+6)` words. -/
def RingColTrue (h : ℕ) (col : ℕ → K) (ring : E × (List E → E)) : Prop :=
  ring.1 = ∑ n ∈ range (2 ^ (h + 6)), ring.2 (boolPoint (h + 6) n) * ofK (col n)

/-- The program's ring weight paired with a block column packs the slices' staged maps. -/
theorem pair_ringCol (h : ℕ) (col : ℕ → K) {pt ch : List E} (hpt : pt.length = h + 6)
    (hch : ch.length = 6) :
    ∑ n ∈ range (2 ^ (h + 6)), ringWeight pt (boolPoint (h + 6) n) (ringCoefficients ch) * ofK (col n) =
      ∑ i : Fin 64, ringW i * phiMap (sliceExt h col pt i) ch := by
  simp only [ringWeight_eq_sum, length_ringCoefficients, Finset.sum_mul]
  rw [Finset.sum_comm]
  have e : ∀ k ∈ range 64, ∑ n ∈ range (2 ^ (h + 6)),
      (ringCoefficients ch).getD k 0 * eqEval (pt.map (· ^ 2 ^ k)) (boolPoint (h + 6) n) *
        ofK (col n) =
      (ringCoefficients ch).getD k 0 * ∑ i : Fin 64, ringW i * sliceExt h col pt i ^ 2 ^ k := by
    intro k _
    rw [← colExt_frob, colExt, Finset.mul_sum]
    refine Finset.sum_congr rfl fun n _ ↦ ?_
    have hl : (pt.map (· ^ 2 ^ k)).length = h + 6 := by rw [List.length_map, hpt]
    rw [← hl, eqEval_boolPoint_eqAt]
    ring
  rw [Finset.sum_congr rfl e]
  simp only [phiMap_eq_sum hch, Finset.mul_sum]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun i _ ↦ Finset.sum_congr rfl fun k _ ↦ by ring

/-- **The ring claim on a block holds iff the errors' twisted sum vanishes.** -/
theorem ringCol_iff (h : ℕ) (col : ℕ → K) {pt sv ch : List E} (hpt : pt.length = h + 6)
    (hsv : sv.length = 64) (hch : ch.length = 6) :
    RingColTrue h col (polyEval (sv.map (phiMap · ch)) gen,
        fun rPrime ↦ ringWeight pt rPrime (ringCoefficients ch)) ↔
      ∑ i : Fin 64, ringW i * phiMap (ringErr h col pt sv i) ch = 0 := by
  unfold RingColTrue
  simp only
  rw [pair_ringCol h col hpt hch, ringTarget_eq_sum sv ch hsv]
  simp only [ringErr, phiMap_sub, mul_sub, Finset.sum_sub_distrib]
  rw [sub_eq_zero]

/-! ## Ring switching with a carried predicate -/

variable {β : Type} {C : List Ev → Set β}

/-- Alive after the coefficients `acc`: `R`, and every `π_k`, `k < 2^(6 - |acc|)`, of the
slices' errors under the stages of `acc` vanishes. -/
def RingAliveC (h : ℕ) (col : β → ℕ → K) (R : β → Prop) (pt sv acc : List E) (q : β) : Prop :=
  R q ∧ ∀ k < 2 ^ (6 - acc.length),
    frobPair Finset.univ ringW (fun i ↦ frobMap (stagesOf acc) (ringErr h (col q) pt sv i)) k = 0

/-- A coefficient's escape (leanVM's `ring_escape`). -/
theorem ringC_escape (h : ℕ) (col : β → ℕ → K) (R : β → Prop) (pt sv acc : List E) (q : β)
    (hq : ¬ RingAliveC h col R pt sv acc q) :
    avgE (fun c ↦ indE (RingAliveC h col R pt sv (acc ++ [c]) q)) ≤ errE 1 := by
  classical
  have hzero : avgE (fun _ : E ↦ indE False) ≤ errE 1 :=
    (avgE_le_of_le fun c ↦ (indE_of_not not_false).le).trans zero_le
  by_cases hG : R q
  swap
  · exact (avgE_mono fun c ↦ indE_mono (q := False) fun hc ↦ hG hc.1).trans hzero
  let b : Fin 64 → E := fun i ↦ frobMap (stagesOf acc) (ringErr h (col q) pt sv i)
  rcases Nat.lt_or_ge acc.length 6 with hlen | hlen
  · let M := 2 ^ (5 - acc.length)
    have h2M : 2 * M = 2 ^ (6 - acc.length) := by
      simp only [M, ← pow_succ']
      congr 1
      (clear * - hlen; omega)
    have hex : ∃ k < 2 * M, frobPair Finset.univ ringW b k ≠ 0 := by
      by_contra hall
      simp only [not_exists, not_and, not_not] at hall
      exact hq ⟨hG, fun k hk ↦ hall k (by rw [h2M]; exact hk)⟩
    have hcard := card_stage_zero_le_one Finset.univ ringW b M hex
    calc avgE (fun c ↦ indE (RingAliveC h col R pt sv (acc ++ [c]) q))
        ≤ avgE (fun c ↦ indE (∀ k < M,
            frobPair Finset.univ ringW (fun i ↦ b i + c * b i ^ 2 ^ M) k = 0)) :=
          avgE_mono fun c ↦ indE_mono fun hc k hk ↦ by
            have h' := hc.2 k (by
              rw [List.length_append, List.length_singleton]
              simp only [M] at hk
              rwa [show 6 - (acc.length + 1) = 5 - acc.length by (clear * - hlen hex; omega)])
            rw [stagesOf_snoc acc c hlen] at h'
            simp only [frobMap_append] at h'
            exact h'
      _ = (Fintype.card E : ℝ≥0∞)⁻¹ * ((Finset.univ.filter fun c : E ↦ ∀ k < M,
            frobPair Finset.univ ringW (fun i ↦ b i + c * b i ^ 2 ^ M) k = 0).card : ℝ≥0∞) :=
          (card_filter_eq_avgE _).symm
      _ ≤ (Fintype.card E : ℝ≥0∞)⁻¹ * 1 := by
          gcongr
          exact_mod_cast hcard
      _ = errE 1 := by rw [mul_one, errE, Nat.cast_one, one_mul]
  · refine (avgE_mono fun c ↦ indE_mono (q := False) fun hc ↦ hq ⟨hG, fun k hk ↦ ?_⟩).trans hzero
    have h' := hc.2 k (by
      rw [List.length_append, List.length_singleton]
      rwa [show 6 - (acc.length + 1) = 6 - acc.length by (clear * - hlen; omega)])
    rwa [stagesOf_snoc_of_le acc c hlen] at h'

variable [Finite β] {L₀ : ℕ}

/-- Ring switching draws the six coefficients and returns the target and the weight. -/
theorem ringSwitch_eq' (point sv : List E) :
    ringSwitch point sv = VerifierProgram.sampleChallenges 6 >>= fun ch ↦
      VerifierProgram.ret (polyEval (sv.map (phiMap · ch)) gen,
        fun rPrime ↦ ringWeight point rPrime (ringCoefficients ch)) := rfl

/-- **Ring switching on a block column**, carrying `R`: from doom of `slicesTrue ∧ R` to doom of
`RingColTrue ∧ R`; lead `6·L₀/|E|` plus the follower's. -/
noncomputable def ringColSpec (hst : Stable C) (hcard : ∀ h, (C h).ncard ≤ L₀) (h : ℕ)
    (col : β → ℕ → K) (R : β → Prop) {εmax T : ℝ≥0∞} (pt sv : List E)
    (hl : pt.length = h + 6 ∧ sv.length = 64) :
    Spec (ringSwitch pt sv) (Doomed C (fun q ↦ slicesTrue h (col q) pt sv ∧ R q))
      (fun r hist ↦ Doomed C (fun q ↦ RingColTrue h (col q) r ∧ R q) hist) εmax
      ((∑ _i ∈ range 6, (L₀ : ℝ≥0∞) * errE 1) + T) T :=
  Spec.congr (ringSwitch_eq' pt sv).symm <|
    ((doomSampleN hst hcard (fun acc q ↦ RingAliveC h col R pt sv acc q) (fun _ ↦ errE 1)
        (fun acc q hq ↦ ringC_escape h col R pt sv acc q hq) 6 []).mono
        (fun _ hd q hq ⟨hR, hπ⟩ ↦ hd q hq ⟨by
          refine ⟨hl.1, hl.2, fun i hi ↦ ?_⟩
          have hδ := ringSwitch_injective (fun i ↦ ringErr h (col q) pt sv i)
            (fun k hk ↦ hπ k (by simpa using hk)) ⟨i, hi⟩
          exact sub_eq_zero.mp hδ, hR⟩)
        (fun _ _ h ↦ h) le_rfl (by simp) le_rfl).bind' fun ch ↦
      (Spec.ret _).mono (fun _ hd ↦ by
          intro q hq ⟨hclaim, hR⟩
          refine hd.2 q hq ?_
          have h6 : ch.length = 6 := by simpa using hd.1
          refine ⟨hR, fun k hk ↦ ?_⟩
          rw [List.nil_append, h6, Nat.sub_self, pow_zero, Nat.lt_one_iff] at hk
          subst hk
          have := (ringCol_iff h (col q) hl.1 hl.2 h6).mp hclaim
          simpa only [List.nil_append, frobPair, pow_zero, pow_one, phiMap_eq_frobMap] using this)
        (fun _ _ h ↦ h) le_rfl le_rfl le_rfl

/-! ## A zero test with a carried predicate -/

/-- The escape bound of the `i`-th of `n` zero-test coordinates (`1` past them). -/
noncomputable def zE (n i : ℕ) : ℝ≥0∞ := if i < n then errE 1 else 1

omit [Finite β] in
/-- **A zero-test coordinate's escape**, carrying `R` (leanVM's `zt_escape`, `n` coordinates). -/
theorem zero_escape (δ : β → ℕ → E) (R : β → Prop) (n : ℕ) (acc : List E) (q : β)
    (hq : ¬ (ZeroOn (δ q) acc n ∧ R q)) :
    avgE (fun c ↦ indE (ZeroOn (δ q) (acc ++ [c]) n ∧ R q)) ≤ zE n acc.length := by
  unfold zE
  split_ifs with hn
  · by_cases hR : R q
    · exact (avgE_mono fun c ↦ indE_mono fun hc ↦ hc.1).trans
        (zeroOn_escape (δ q) hn fun h ↦ hq ⟨h, hR⟩)
    · exact (avgE_mono fun c ↦ indE_mono (q := False) fun h ↦ hR h.2).trans
        ((avgE_le_of_le fun c ↦ (indE_of_not not_false).le).trans zero_le)
  · exact avgE_indE_le_one _

theorem sum_zE {n m : ℕ} (hm : m ≤ n) (L₀ : ℕ) :
    ∑ i ∈ range m, (L₀ : ℝ≥0∞) * zE n (0 + i) = m * (L₀ * errE 1) := by
  rw [Finset.sum_congr rfl fun i hi ↦ by
    rw [zE, if_pos (by have := Finset.mem_range.1 hi; (clear * - hm this; omega))]]
  simp

/-- **`m ≤ n` zero-test coordinates**, carrying `R`: from doom of `ZeroOn δ [] n ∧ R` to doom of
`ZeroOn δ pt n ∧ R` at the `m` challenges `pt`; lead `m·L₀/|E|` plus the follower's. -/
noncomputable def zeroSpec (hst : Stable C) (hcard : ∀ h, (C h).ncard ≤ L₀) (δ : β → ℕ → E)
    (R : β → Prop) {n m : ℕ} (hm : m ≤ n) {εmax T : ℝ≥0∞} :
    Spec (VerifierProgram.sampleChallenges m) (Doomed C (fun q ↦ ZeroOn (δ q) [] n ∧ R q))
      (fun pt hist ↦ pt.length = m ∧ Doomed C (fun q ↦ ZeroOn (δ q) pt n ∧ R q) hist) εmax
      (m * (L₀ * errE 1) + T) T :=
  (doomSampleN hst hcard (fun acc q ↦ ZeroOn (δ q) acc n ∧ R q) (zE n)
      (fun acc q hq ↦ zero_escape δ R n acc q hq) m []).mono (fun _ h ↦ h)
    (fun _ _ h ↦ by simpa using h) le_rfl (by rw [List.length_nil, sum_zE hm]) le_rfl

end Lvm.KG
