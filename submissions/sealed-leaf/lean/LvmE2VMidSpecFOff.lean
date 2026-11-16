/- `LvmE2VMidSpecFOff` (GOLF2 off-path move, group 3 of 48): declarations that the certificate `certified`
   does not use, moved here verbatim (same names, same namespaces and context) from LvmSpecRulesLeaves, LvmKeccakGkr, LvmVEqRel, LvmVEqClaims, LvmE2FCert, LvmE2VMidSpecF,
   so that `Solution`'s import closure need not elaborate them. Import this module where they are needed;
   the name -> module map is GOLF2's moved.tsv. -/
import LvmSpecRulesLeaves
import LvmKeccakGkr
import LvmVEqRel
import LvmVEqClaims
import LvmE2FCert
import LvmE2VMidSpecF
import LvmMPCertOff
import LvmChainTablePad
import LvmJBMutual
import LvmMlListLemmas
import LvmQAsmHar47
import LvmSpecRulesCert
import LvmTensorSwitch
import LvmVerifierST

-- ===== from `LvmSpecRulesLeaves` =====

section
namespace LeanVM.Protocol.Compile
open LeanVM.Parameters VerifierProgram
section
variable {α : Type}
namespace Spec
variable {Pre : List Ev → Prop} {Post : α → List Ev → Prop} {εmax T : ENNReal}

private theorem reach_queryP {i : ℕ} {ps : List ℕ} {h₀ l : List Ev}
    (hl : (queryOpenings i ps).Reach h₀ l) :
    l = [] ∨ ∃ rows, answer h₀ i ps = some rows ∧ l = [Ev.query rows] := by
  induction hl with
  | nil => exact .inl rfl
  | @query l i' ps' k rows _ ha hans ih =>
    rcases ih with rfl | ⟨y, -, rfl⟩
    · simp only [queryOpenings, after, Option.some.injEq, VerifierProgram.query.injEq] at ha
      obtain ⟨rfl, rfl, -⟩ := ha
      exact .inr ⟨rows, by simpa using hans, rfl⟩
    · simp [queryOpenings, after] at ha
  | read _ _ ha ih | sample _ _ ha ih | grind _ ha ih | commit _ _ ha _ ih =>
    rcases ih with rfl | ⟨y, -, rfl⟩ <;> simp [queryOpenings, after] at ha

/-- The doom of `Spec.queryP`. -/
def queryD (Pre : List Ev → Prop) (Post : List (List K) → List Ev → Prop) (h₀ l : List Ev) :
    Prop :=
  match l with
  | [] => Pre h₀
  | [Ev.query rows] => Post rows (h₀ ++ [Ev.query rows])
  | _ => True

open Classical in
/-- **Open** rows of the `i`-th commitment: `Post` of the rows the words give; the lead is the
follower's. -/
noncomputable def queryP {Post : List (List K) → List Ev → Prop} (i : ℕ) (ps : List ℕ)
    (h : ∀ h₀ rows, Pre h₀ → answer h₀ i ps = some rows → Post rows (h₀ ++ [Ev.query rows])) :
    Spec (VerifierProgram.queryOpenings i ps) Pre Post εmax T T where
  D := queryD Pre Post
  V h₀ l := if queryD Pre Post h₀ l then min 1 T else 1
  le_one _ _ := by split_ifs <;> simp
  start_D _ h := h
  start_V _ h := by simp [queryD, h]
  read := by
    intro _ _ _ _ hl ha
    rcases reach_queryP hl with
        rfl | ⟨y, -, rfl⟩ <;> simp [VerifierProgram.queryOpenings, after] at ha
  grind := by
    intro _ _ _ _ hl ha
    rcases reach_queryP hl with
        rfl | ⟨y, -, rfl⟩ <;> simp [VerifierProgram.queryOpenings, after] at ha
  commit := by
    intro _ _ _ _ _ _ hl ha
    rcases reach_queryP hl with
        rfl | ⟨y, -, rfl⟩ <;> simp [VerifierProgram.queryOpenings, after] at ha
  sample := by
    intro _ _ _ hl ha
    rcases reach_queryP hl with
        rfl | ⟨y, -, rfl⟩ <;> simp [VerifierProgram.queryOpenings, after] at ha
  query := by
    intro h₀ l i' ps' k rows hl ha hans
    rcases reach_queryP hl with rfl | ⟨y, -, rfl⟩
    · simp only [VerifierProgram.queryOpenings, after, Option.some.injEq,
        VerifierProgram.query.injEq] at ha
      obtain ⟨rfl, rfl, -⟩ := ha
      by_cases hP : Pre h₀
      · have := h h₀ rows hP (by simpa using hans)
        simp [queryD, hP, this]
      · simp only [queryD, hP, ite_false]
        split_ifs <;> simp
    · simp [VerifierProgram.queryOpenings, after] at ha
  moveEnd := by
    intro h₀ l q hl ha hm
    rcases reach_queryP hl with rfl | ⟨y, -, rfl⟩
    · simp only [VerifierProgram.queryOpenings, after, Option.some.injEq] at ha; subst ha; simp
        [IsMove] at hm
    · simp only [VerifierProgram.queryOpenings, after, Option.some.injEq] at ha; subst ha; simp
        [IsMove] at hm
  retEnd := by intro _ _ _ _ _ hD; simp [hD]
  retDoom := by intro _ _ _ _ _ hD; simp [hD]
  post := by
    intro h₀ l a hl ha hD
    rcases reach_queryP hl with rfl | ⟨y, -, rfl⟩
    · simp [VerifierProgram.queryOpenings, after] at ha
    · simp only [VerifierProgram.queryOpenings, after, Option.some.injEq, VerifierProgram.ret.injEq] at ha; subst ha; exact hD
  bound := by
    intro h₀ l hl hne hm
    rcases reach_queryP hl with rfl | ⟨y, -, rfl⟩
    · exact absurd rfl hne
    · simp [EndsMove] at hm

end Spec
end
end LeanVM.Protocol.Compile
end

-- ===== from `LvmKeccakGkr` =====

section
section
namespace LeanVM.Protocol.KeccakGkr
open LeanVM.Parameters LeanVM.Semantics LeanVM.Protocol.Compile LeanVM.Protocol.Verifier
open LeanVM.Protocol.EndToEnd.Front Finset
open scoped ENNReal
section
variable (h : ℕ)

/-- **The first claim on a candidate**: the lanes of the two segments' outputs, combined. -/
theorem firstClaim_sum (P : ℕ) (hP : h = P + 4) (col : ℕ → K) {inst segment lanesPt : List E}
    (hi : inst.length = h) (hl : lanesPt.length = 5) (output : List E) (committed : E) :
    claimSum (statesAt h col 0) P (firstClaim inst segment lanesPt output committed).point
        (firstClaim inst segment lanesPt output committed).mu
        (firstClaim inst segment lanesPt output committed).weights =
      ∑ m ∈ range 2, eqAt segment m * ∑ l ∈ range 25, eqAt lanesPt l *
        stepMle h inst (fun x ↦ laneWord (segState h col m 12 x) l) := by
  subst hP
  have ha : (inst.take 4).length = 4 := by simp [hi]
  have hb : (inst.drop 4).length = P := by simp [hi]
  simp only [firstClaim, claimSum, stAt]
  have hmu : ∀ i ∈ range 16, (eqKernel (inst.take 4)).getD i 0 = eqAt (inst.take 4) i :=
    fun i hi' ↦ by
      rw [eqKernel_getD, ha, ite_eq_left (show i < 2 ^ 4 by
        have := Finset.mem_range.1 hi'; simpa using this)]
  have e : ∀ z, ∑ i ∈ range 16, (eqKernel (inst.take 4)).getD i 0 * ∑ j ∈ range 1600,
      (firstWeights lanesPt).getD j 0 * bitE (statesAt (P + 4) col 0 (z / 2 ^ P) (i + 16 * (z % 2 ^ P)) j) =
      ∑ i ∈ range 16, eqAt (inst.take 4) i * (fun m x ↦ ∑ l ∈ range 25, eqAt lanesPt l *
        ofK (laneWord (segState (P + 4) col m 12 x) l)) (z / 2 ^ P) (i + 16 * (z % 2 ^ P)) := by
    intro z
    refine Finset.sum_congr rfl fun i hi' ↦ ?_
    rw [hmu i hi']
    exact congrArg _ (sum_firstWeights hl _)
  simp only [e]
  rw [sum_split ha hb (fun m x ↦ ∑ l ∈ range 25, eqAt lanesPt l *
    ofK (laneWord (segState (P + 4) col m 12 x) l)), List.take_append_drop]
  refine Finset.sum_congr rfl fun m _ ↦ congrArg _ ?_
  simp only [stepMle, Finset.mul_sum]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun l _ ↦ Finset.sum_congr rfl fun x _ ↦ by ring

end
end LeanVM.Protocol.KeccakGkr
end
end

section
section
namespace LeanVM.Protocol.KeccakGkr
open LeanVM.Parameters LeanVM.Semantics LeanVM.Protocol.Compile LeanVM.Protocol.Verifier
open LeanVM.Protocol.EndToEnd.Front Finset
open scoped ENNReal
section
variable (h : ℕ)

/-- The fifty mismatches, index `m + 2ℓ`: segment `0`'s output against the committed middle
state, segment `1`'s output against the claimed `output`. -/
def startDelta (col : ℕ → K) (inst output : List E) (u : ℕ) : E :=
  if u / 2 < 25 then
    (if u % 2 = 0 then stepMle h inst (fun x ↦ laneWord (segState h col 0 12 x) (u / 2)) +
        midMle h col inst (u / 2)
      else stepMle h inst (fun x ↦ laneWord (segState h col 1 12 x) (u / 2)) +
        output.getD (u / 2) 0)
  else 0

end
end LeanVM.Protocol.KeccakGkr
end
end

section
section
namespace LeanVM.Protocol.KeccakGkr
open LeanVM.Parameters LeanVM.Semantics LeanVM.Protocol.Compile LeanVM.Protocol.Verifier
open LeanVM.Protocol.EndToEnd.Front Finset
open scoped ENNReal
section
variable (h : ℕ)

/-- A zero mismatch table: the middle-state and output claims hold. -/
theorem claims_of_zeroOn (col : ℕ → K) (inst output : List E)
    (hz : ZeroOn (startDelta h col inst output) [] 6) :
    outClaimsTrueMid h col inst output ∧ midAgree h col inst := by
  rw [zeroOn_nil] at hz
  refine ⟨fun l hl ↦ ?_, fun l hl ↦ ?_⟩
  · have := hz (1 + 2 * l) (by (clear * - hl; omega))
    have e1 : (1 + 2 * l) / 2 = l := by (clear * -; omega)
    have e2 : (1 + 2 * l) % 2 = 1 := by (clear * - e1; omega)
    rw [startDelta, e1, e2, ite_eq_left hl, ite_eq_right (by norm_num)] at this
    exact add_eq_zero_iff_E.1 this
  · have := hz (2 * l) (by (clear * - hl; omega))
    have e1 : 2 * l / 2 = l := by (clear * -; omega)
    have e2 : 2 * l % 2 = 0 := by (clear * - e1; omega)
    rw [startDelta, e1, e2, ite_eq_left hl, ite_eq_left rfl] at this
    exact add_eq_zero_iff_E.1 this

end
end LeanVM.Protocol.KeccakGkr
end
end

section
section
namespace LeanVM.Protocol.KeccakGkr
open LeanVM.Parameters LeanVM.Semantics LeanVM.Protocol.Compile LeanVM.Protocol.Verifier
open LeanVM.Protocol.EndToEnd.Front Finset
open scoped ENNReal
section
variable (h : ℕ)

/-- **After `committed`**: an open value and a true first claim leave the mismatch table's
extension zero at the challenges. -/
theorem zeroOn_of_first (P : ℕ) (hP : h = P + 4) (col : ℕ → K) {inst segment lanesPt output : List E}
    (hi : inst.length = h) (hs : segment.length = 1) (hl : lanesPt.length = 5)
    (ho : output.length = 25) (committed : E)
    (hopen : OpenTrue h col inst segment lanesPt committed)
    (htrue : ClaimTrue (statesAt h col 0) P (firstClaim inst segment lanesPt output committed)) :
    ZeroOn (startDelta h col inst output) (segment ++ lanesPt) 6 := by
  rw [zeroOn_full _ (by simp [hs, hl])]
  rw [ClaimTrue, firstClaim_sum h P hP col hi hl] at htrue
  have hdot : dot ((eqKernel lanesPt).take 25) output =
      ∑ l ∈ range 25, eqAt lanesPt l * output.getD l 0 := by
    rw [dot_eq _ _ (by simp [eqKernel_length, hl, ho])]
    simp only [List.length_take, eqKernel_length, hl]
    refine Finset.sum_congr rfl fun l hl' ↦ ?_
    have hl'' := Finset.mem_range.1 hl'
    rw [List.getD_eq_getElem?_getD, List.getElem?_take, ite_eq_left (by omega),
      ← List.getD_eq_getElem?_getD, eqKernel_getD, hl, ite_eq_left (by (clear * - hl''; omega))]
  have hseg : (eqKernel segment).getD (keccakSegments - 1) 0 = eqAt segment 1 := by
    rw [eqKernel_getD, hs]; rfl
  change committed + (eqKernel segment).getD (keccakSegments - 1) 0 *
    dot ((eqKernel lanesPt).take 25) output = _ at htrue
  rw [hseg, hdot] at htrue
  -- the sum over the 64 indices, split into segment and lane
  have hsplit : ∑ w ∈ range (2 ^ 6), eqAt (segment ++ lanesPt) w * startDelta h col inst output w =
      ∑ m ∈ range 2, eqAt segment m * ∑ l ∈ range 32, eqAt lanesPt l *
        startDelta h col inst output (2 * l + m) := by
    rw [show 2 ^ 6 = 32 * 2 from rfl, sum_range_mul 32 2, Finset.sum_comm]
    refine Finset.sum_congr rfl fun m hm ↦ ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun l _ ↦ ?_
    have hm' := Finset.mem_range.1 hm
    have e1 : (2 * l + m) / 2 = l := by (clear * - hm'; omega)
    rw [eqAt_append, hs, eqAt_mod segment, hs, pow_one, e1,
      show (2 * l + m) % 2 = m by (clear * - e1; omega)]
    ring
  have hzero : ∀ m < 2, ∑ x ∈ range 7, eqAt lanesPt (25 + x) *
      startDelta h col inst output (2 * (25 + x) + m) = 0 := fun m hm ↦
    Finset.sum_eq_zero fun x _ ↦ by
      rw [startDelta, ite_eq_right (by (clear * - hm; omega)), mul_zero]
  have hm0 : ∑ l ∈ range 32, eqAt lanesPt l * startDelta h col inst output (2 * l + 0) =
      ∑ l ∈ range 25, eqAt lanesPt l *
        stepMle h inst (fun x ↦ laneWord (segState h col 0 12 x) l) +
      ∑ l ∈ range 25, eqAt lanesPt l * midMle h col inst l := by
    rw [show 32 = 25 + 7 from rfl, Finset.sum_range_add, hzero 0 (by norm_num), add_zero,
      ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun l hl' ↦ ?_
    have hl'' := Finset.mem_range.1 hl'
    rw [startDelta, ite_eq_left (by (clear * - hl''; omega)), ite_eq_left (by (clear * -; omega)),
      show (2 * l + 0) / 2 = l by (clear * -; omega), mul_add]
  have hm1 : ∑ l ∈ range 32, eqAt lanesPt l * startDelta h col inst output (2 * l + 1) =
      ∑ l ∈ range 25, eqAt lanesPt l *
        stepMle h inst (fun x ↦ laneWord (segState h col 1 12 x) l) +
      ∑ l ∈ range 25, eqAt lanesPt l * output.getD l 0 := by
    rw [show 32 = 25 + 7 from rfl, Finset.sum_range_add, hzero 1 (by norm_num), add_zero,
      ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun l hl' ↦ ?_
    have hl'' := Finset.mem_range.1 hl'
    rw [startDelta, ite_eq_left (by (clear * - hl''; omega)), ite_eq_right (by (clear * -; omega)),
      show (2 * l + 1) / 2 = l by (clear * -; omega), mul_add]
  rw [hsplit, Finset.sum_range_succ (n := 1), Finset.sum_range_succ (n := 0),
    Finset.sum_range_zero, zero_add, hm0, hm1]
  rw [Finset.sum_range_succ (n := 1), Finset.sum_range_succ (n := 0), Finset.sum_range_zero,
    zero_add] at htrue
  rw [OpenTrue] at hopen
  linear_combination (-1 : E) * htrue + (-1 : E) * hopen +
    (CharTwo.two_eq_zero (R := E)) * (eqAt segment 1 *
      ∑ l ∈ range 25, eqAt lanesPt l * output.getD l 0 + committed)

end
end LeanVM.Protocol.KeccakGkr
end
end

section
section
namespace LeanVM.Protocol.KeccakGkr
open LeanVM.Parameters LeanVM.Semantics LeanVM.Protocol.Compile LeanVM.Protocol.Verifier
open LeanVM.Protocol.EndToEnd.Front Finset
open scoped ENNReal
section

theorem firstClaim_v1 (inst segment lanesPt output : List E) (committed : E) :
    firstClaim inst segment lanesPt output committed =
      firstClaimS Shape.v1 inst segment lanesPt output committed := rfl

end
end LeanVM.Protocol.KeccakGkr
end
end

section
section
namespace LeanVM.Protocol.KeccakGkr
open LeanVM.Parameters LeanVM.Semantics LeanVM.Protocol.Compile LeanVM.Protocol.Verifier
open LeanVM.Protocol.EndToEnd.Front Finset
open scoped ENNReal
section

theorem outClaimsTrueMid_v1 (h : ℕ) (col : ℕ → K) (inst output : List E) :
    outClaimsTrueMid h col inst output ↔ outClaimsTrueMidS Shape.v1 h (inState h col) inst output :=
  Iff.rfl

end
end LeanVM.Protocol.KeccakGkr
end
end

section
namespace LeanVM.Protocol.KeccakGkr
open LeanVM.Parameters LeanVM.Semantics LeanVM.Protocol.Compile LeanVM.Protocol.Verifier
open LeanVM.Protocol.EndToEnd.Front LeanVM.Protocol.EndToEnd.Complete Finset
open scoped ENNReal
section
variable {β : Type} [Finite β] {C : List Ev → Set β} {L₀ : ℕ} {εmax T : ℝ≥0∞}

omit [Finite β] in
theorem zt_escape (δ : β → ℕ → E) (R : β → Prop) (pre : List E) {n : ℕ}
    (hpre : pre.length + n = 6) (acc : List E) (q : β)
    (hq : ¬ (ZeroOn (δ q) (pre ++ acc) 6 ∧ R q)) :
    avgE (fun c ↦ indE (ZeroOn (δ q) (pre ++ (acc ++ [c])) 6 ∧ R q)) ≤ ztE n acc.length := by
  unfold ztE
  split_ifs with hn
  · by_cases hR : R q
    · refine (avgE_mono fun c ↦ indE_mono fun hc ↦ ?_).trans
        (zeroOn_escape (δ q) (acc := pre ++ acc) (by simp; (clear * - hpre hn; omega)) fun h ↦ hq ⟨h, hR⟩)
      rw [List.append_assoc]; exact hc.1
    · exact (avgE_mono fun c ↦ indE_mono (q := False) fun h ↦ hR h.2).trans
        ((avgE_le_of_le fun c ↦ (indE_of_not not_false).le).trans zero_le)
  · exact avgE_indE_le_one _

end
end LeanVM.Protocol.KeccakGkr
end

section
namespace LeanVM.Protocol.KeccakGkr
open LeanVM.Parameters LeanVM.Semantics LeanVM.Protocol.Compile LeanVM.Protocol.Verifier
open LeanVM.Protocol.EndToEnd.Front LeanVM.Protocol.EndToEnd.Complete Finset
open scoped ENNReal
section
variable {β : Type} [Finite β] {C : List Ev → Set β} {L₀ : ℕ} {εmax T : ℝ≥0∞}

theorem lead_eq (L₀ : ℕ) :
    (∑ i ∈ range 1, (L₀ : ℝ≥0∞) * ztE 6 (0 + i)) +
        ((∑ i ∈ range 5, (L₀ : ℝ≥0∞) * ztE 5 (0 + i)) + 0) = (L₀ : ℝ≥0∞) * errE 6 := by
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, ztE, errE]
  norm_num
  ring

end
end LeanVM.Protocol.KeccakGkr
end

section
namespace LeanVM.Protocol.KeccakGkr
open LeanVM.Parameters LeanVM.Semantics LeanVM.Protocol.Compile LeanVM.Protocol.Verifier
open LeanVM.Protocol.EndToEnd.Front LeanVM.Protocol.EndToEnd.Complete Finset
open scoped ENNReal
section
variable {β : Type} [Finite β] {C : List Ev → Set β} {L₀ : ℕ} {εmax T : ℝ≥0∞}

theorem keccakF_roundsFrom (a : KeccakState) : keccakF1600 a = roundsFrom 0 24 a := rfl

end
end LeanVM.Protocol.KeccakGkr
end

section
namespace LeanVM.Protocol.KeccakGkr
open LeanVM.Parameters LeanVM.Semantics LeanVM.Protocol.Compile LeanVM.Protocol.Verifier
open LeanVM.Protocol.EndToEnd.Front LeanVM.Protocol.EndToEnd.Complete Finset
open scoped ENNReal
section
variable {β : Type} [Finite β] {C : List Ev → Set β} {L₀ : ℕ} {εmax T : ℝ≥0∞}

theorem outClaims_iff_of_regionValid (h : ℕ) (col : ℕ → K) (inst output : List E)
    (hv : RegionValid h col) :
    outClaimsTrue h col inst output ↔ outClaimsTrueMid h col inst output := by
  have hx : ∀ x ∈ range (2 ^ h), keccakF1600 (inState h col 0 x) = roundsFrom 12 12 (inState h col 1 x) :=
    fun x hx ↦ by rw [keccakF_eq, hv x (Finset.mem_range.1 hx)]
  have e : ∀ l, stepMle h inst (fun x ↦ laneWord (keccakF1600 (inState h col 0 x)) l) =
      stepMle h inst (fun x ↦ laneWord (roundsFrom 12 12 (inState h col 1 x)) l) := fun l ↦
    Finset.sum_congr rfl fun x hxr ↦ by simp only; rw [hx x hxr]
  unfold outClaimsTrue outClaimsTrueMid
  simp only [e]

/-- **The Keccak reduction against `keccakF`**: from doom of "the output-lane claims against
`keccakF` of the inputs hold at `inst`, the region is valid, and `R`", to doom of the reduction's
claims with `RegionValid` and `R` carried. -/
noncomputable def gkrSpec_regionValid (hst : Stable C) (hcard : ∀ h, (C h).ncard ≤ L₀)
    (R : β → Prop) (qk : β → ℕ → K) (P : ℕ) {inst output : List E} (hi : inst.length = P + 4)
    (ho : output.length = 25) (hT : T ≤ εmax) (h46 : (L₀ : ℝ≥0∞) * errE 46 ≤ εmax) :
    Spec (verifyKeccak (P + 4) inst output)
      (Doomed C (fun q ↦ outClaimsTrue (P + 4) (qk q) inst output ∧
        RegionValid (P + 4) (qk q) ∧ R q))
      (KeccakPost qk (fun q ↦ RegionValid (P + 4) (qk q) ∧ R q) P C) εmax
      ((L₀ : ℝ≥0∞) * errE 6) T :=
  (gkrSpec hst hcard (fun q ↦ RegionValid (P + 4) (qk q) ∧ R q) qk P hi ho hT h46).mono
    (fun _ hd ↦ Doomed.mono hd fun _ ⟨hmid, _, hv, hR⟩ ↦
      ⟨(outClaims_iff_of_regionValid _ _ _ _ hv).2 hmid, hv, hR⟩)
    (fun _ _ h' ↦ h') le_rfl le_rfl le_rfl

/-- A column given on `Fin (2^(h + 6))`, read as words of `ℕ` (`0` past the end). -/
def colOfFin {h : ℕ} (c : Fin (2 ^ (h + 6)) → K) : ℕ → K :=
  fun n ↦ if hn : n < 2 ^ (h + 6) then c ⟨n, hn⟩ else 0

end
end LeanVM.Protocol.KeccakGkr
end

-- ===== from `LvmVEqRel` =====

section
section
set_option autoImplicit false
namespace Lvm.VEq
open Lvm DM

/-- The two caps (phase 1). -/
def dCommit (p : Params) : DM Unit := do
  skip (nodeBytes * 2 ^ (p.level ⟨.main, 0⟩).cap)
  skip (nodeBytes * 2 ^ (p.level ⟨.crec, 0⟩).cap)

end Lvm.VEq
end
end

section
section
set_option autoImplicit false
namespace Lvm.VEq
open Lvm DM

/-- The claims of phases 2–7 (`decideProg`'s list; lvm2 S2: the tape's claims in place of `CH`'s
and the `CH` link's). -/
def dClaims (m : M3) (p : Params) (pub : Pub) (bus : BusOut) (evals : List (List FE × List FE))
    (tp : TapeRes) (wo : WireOut)
    (ks : List FE × List FE × KeccakOut × (FE × (List FE → FE)))
    (kLinkClaims : List (Com × BlockClaim)) : List (Com × BlockClaim) :=
  bus.claims ++ m.tableClaims pub evals ++
    (tapeClaims p tp wo pub ++ keccakClaims m.ksBlock ks.2.2.1 ks.2.2.2).map (.main, ·) ++
    m.ksOutputClaims ks.1 ks.2.1 ++ kLinkClaims

/-- The claims of phases 2–7 with their tail values (roll 7, SH2-Z; `dClaimsZ`; `dClaimsT_fst`: without
the tails they are `dClaims`). -/
def dClaimsT (m : M3) (p : Params) (pub : Pub) (bus : BusOut) (evals : List (List FE × List FE))
    (tp : TapeRes) (wo : WireOut × List FE)
    (ks : List FE × List FE × KeccakOut × (FE × (List FE → FE)))
    (kLinkClaims : List (Com × BlockClaim)) : List (Com × BlockClaim × FE) :=
  Shape.dClaimsZ m p pub bus.claims evals tp wo.1 wo.2 ks.1 ks.2.1 (keccakClaims m.ksBlock ks.2.2.1 ks.2.2.2)
    kLinkClaims

/-- **`decideProg` by phases** (its value: phase 3b's folded accumulator). -/
def decidePhases (p : Params) (m : M3) (vk c : Vector UInt8 32) : DM Acc := do
  let sig ← read
  let pub := pubOf vk c sig
  dCommit p
  let pb ← dBus p m pub
  let evals ← dTab p m pub pb.1 pb.2
  let accOut ← accFold p m pub evals
  let tp ← dTape p.logN
  dRange p pub
  let wo ← Shape.dWireC p pub tp.claim
  let ks ← dKec p.ksLog
  let kLinkClaims ← dKsLink p m ks.1 pub
  Shape.dOpenZ p (Shape.smallP p pub) (dClaimsT m p pub pb.2 evals tp wo ks kLinkClaims)
  pure accOut

/-- `decideProg` is its phases. -/
theorem decideProg_eq (p : Params) (m : M3) (vk c : Vector UInt8 32) :
    decideProg p m vk c = decidePhases p m vk c := by
  simp only [decideProg, decidePhases, dCommit, dBus, dTab, dKec, dKsLink, dClaimsT,
    bind_assoc, pure_bind]

end Lvm.VEq
end
end

-- ===== from `LvmVEqClaims` =====

section
set_option autoImplicit false
namespace Lvm.VEq
open Lvm LeanVM.Parameters LeanVM.Protocol
open Lvm.M3 (tE_mul tE_ofK)
namespace Lk

/-- **A sum claim.** -/
theorem sumClaim_rel (nu : ℕ) (parts : List (FE × Lvm.Placement × List FE)) (v : FE)
    {parts' : List (E × VPlacement × List E)} {v' : E} (hp : parts' = parts.map partE)
    (hv : v' = FE.toExt3 v) : BCRel (sumClaim nu parts v) (sumClaimE nu parts' v') := by
  subst hp hv
  refine ⟨rfl, rfl, fun xs ↦ ?_⟩
  simp only [sumClaim, sumClaimE, toExt3_sumE, List.map_map]
  congr 1
  refine List.map_congr_left fun q _ ↦ ?_
  obtain ⟨c, b, z⟩ := q
  simp only [Function.comp, partE, tE_mul, toExt3_eqAbove, toExt3_eqEval, ← List.map_take]
  rfl

/-- `D`'s block at `P20` (lvm2 S2). -/
theorem dBlk_eq : plE (dBlock P20) = dBlkE := by
  rw [dBlock, layout0_P20]; rfl

/-- `KS`'s `Y` lane `l` of `P20`. -/
theorem ksYPart_rel (l : ℕ) (pt : List FE) :
    plE (ksYPart P20 (layout0 P20) l pt).1 = (ksYPartE l (pt.map FE.toExt3)).1 ∧
      (ksYPart P20 (layout0 P20) l pt).2.map FE.toExt3 = (ksYPartE l (pt.map FE.toExt3)).2 := by
  by_cases hl : l < 14 <;> refine ⟨?_, ?_⟩ <;>
    simp only [ksYPart, ksYPartE, hl, ↓reduceIte, List.map_append, map_selectorPoint] <;> rfl

end Lk
end Lvm.VEq
end

section
set_option autoImplicit false
namespace Lvm.VEq
open Lvm LeanVM.Parameters LeanVM.Protocol
open Lvm.M3 (tE_mul tE_ofK)
open Lk

/-- **Per commitment.** -/
theorem on_rel {l : List (Com × BlockClaim)} {l' : List (Com × BClaim)} (h : List.Forall₂ CRel l l')
    (com : Com) :
    List.Forall₂ SCRel ((l.filter (·.1 == com)).map (·.2.onStack))
      ((l'.filter (·.1 == com)).map (·.2.onStack)) := by
  induction h with
  | nil => exact .nil
  | @cons a b _ _ hab _ ih =>
    obtain ⟨h1, h2⟩ := hab
    by_cases hc : (b.1 == com) = true
    · simp only [List.filter_cons, h1, hc, ↓reduceIte, List.map_cons]
      exact .cons (onStack_rel h2) ih
    · simp only [List.filter_cons, h1, hc, Bool.false_eq_true, ↓reduceIte]
      exact ih

/-- **The tape's claims** (lvm2 S2, T1, T4, T5) against `tapeClaimsE`, given related `r`, lanes
and ring. -/
theorem tapeClaims_rel (tp : TapeRes) (wo : WireOut) (tpE : Lvm.KG.TapeOutE) (pub : Pub)
    (hr : tpE.1 = tp.r.map FE.toExt3) (hv : tpE.2.1 = tp.v.map FE.toExt3)
    (hring1 : tpE.2.2.2.d.ring.1 = FE.toExt3 wo.ring.1)
    (hring2 : ∀ xs, tpE.2.2.2.d.ring.2 (xs.map FE.toExt3) = FE.toExt3 (wo.ring.2 xs)) :
    List.Forall₂ BCRel (tapeClaims P20 tp wo pub) (tapeClaimsE tpE pub) := by
  have hb := dBlk_eq.symm
  simp only [tapeClaims, tapeClaimsE]
  refine forall₂_append (forall₂_append ?_ ?_) ?_
  · exact forall₂_map_map _ fun l _ ↦ point_rel _ _ _ hb
      (by simp only [hr, List.map_append, map_selectorPoint])
      (by rw [hv]; exact getD_map_toExt3 tp.v l)
  · exact List.Forall₂.cons ⟨rfl, hring1, hring2⟩ List.Forall₂.nil
  · exact forall₂_map_map _ fun ⟨w, l⟩ _ ↦ point_rel _ _ _ hb
      (by simp only [List.map_append, map_selectorPoint]; rfl) (tE_ofK w).symm

/-- **`KS`'s 25 output lanes.** -/
theorem ksOutputClaims_rel (rk v : List FE) :
    List.Forall₂ CRel (ksOutputClaims0 P20 rk v)
      (ksOutputClaimsE (rk.map FE.toExt3) (v.map FE.toExt3)) := by
  simp only [ksOutputClaims0, ksOutputClaimsE]
  refine forall₂_map_map _ fun l _ ↦ ⟨rfl, ?_⟩
  obtain ⟨h1, h2⟩ := ksYPart_rel l rk
  exact point_rel _ _ _ h1.symm h2.symm (getD_map_toExt3 v l)

end Lvm.VEq
end

-- ===== from `LvmE2FCert` =====

section
set_option autoImplicit false
namespace Lvm.E2F
open RecursionFast Lvm.FS Lvm.T Lvm.ASM
open LeanVM.Parameters
open LeanVM.Protocol LeanVM.Protocol.Verifier LeanVM.Protocol.EndToEnd
open LeanVM.Protocol.Compile hiding Proof Bytes
open scoped NNReal ENNReal
variable {mid : List UInt8 → VerifierProgram (List LeanVM.Protocol.Verifier.StackClaim)} {Good : GoodRelM}
  {Lm : ℝ≥0∞}

/-- **The knowledge certificate of S1's `S` branch**: M′'s `kcertSM` at the pinned middle phases. -/
noncomputable def kcertSF (hm : MidSpecPin mid Good εS Lm) (hsh : MidShapeM mid) (hL : leadP Lm ≤ εS)
    {VS : SProg} {vk : RecursionFast.Digest} (X : ExtJM (midP mid) Good VS vk) :
    KCert (schemeS vk (PSWithM (midP mid))) (Rel (accV VS vk)) :=
  kcertSM (midSpecP_of hm hsh hL) hL (midShapeP_of hsh) X

/-- **Its error**: `εFS ≤ 2^-128` (`εS = 7·2^-131`, luck `2^-132`, hash `2^-139`, as M′). -/
theorem εFS_kcertSF (hm : MidSpecPin mid Good εS Lm) (hsh : MidShapeM mid) (hL : leadP Lm ≤ εS)
    {VS : SProg} {vk : RecursionFast.Digest} (X : ExtJM (midP mid) Good VS vk) :
    Scheme.εFS (kcertSF hm hsh hL X) ≤ (2 : ℝ≥0)⁻¹ ^ 128 :=
  εFS_kcertSM _ _ _ X

/-- **S1's open obligations** (the frame of statement 18): the middle phases at `candZ`, the node's soundness, the
refinement of `V_S` to the pinned `P_S`, the executable extractor on good logs. -/
structure OpenSF (VS : SProg) (E : RecursionFast.Digest → RecursionFast.Proof → Log → Option Wit) : Type where
  mid : List UInt8 → VerifierProgram (List LeanVM.Protocol.Verifier.StackClaim)
  Good : GoodRelM
  Lm : ℝ≥0∞
  hmid : MidSpecPin mid Good εS Lm
  hsh : MidShapeM mid
  hL : leadP Lm ≤ εS
  child : List UInt8 → List BF64 → Signed
  hnode : ∀ vk, NodeSoundM VS vk Good child
  refines : ∀ vk L c π, isS π = true → (VS vk c π).runLog L = some true →
    ((schemeS vk (PSWithM (midP mid))).V c π).runLog L = some true
  ext_eq : ∀ vk L c π, isS π = true → L.length ≤ logCap →
    Lvm.FS.Scheme.μ (kcertSF hmid hsh hL (extJM (midShapeP_of hsh) (hnode vk))) L < 1 →
    ((schemeS vk (PSWithM (midP mid))).V c π).runLog L = some true →
    (∃ w, E c π L = some w ∧ Rel (accV VS vk) c w) ∨
      E c π L = (schemeS vk (PSWithM (midP mid))).Ex
        (kcertSF hmid hsh hL (extJM (midShapeP_of hsh) (hnode vk))).ext c π L

/-- **`OpenSF` is M′'s `OpenSM` at the pinned middle phases.** -/
noncomputable def openSF {VS : SProg} {E : RecursionFast.Digest → RecursionFast.Proof → Log → Option Wit} (o : OpenSF VS E) :
    OpenSM VS E where
  mid := midP o.mid
  Good := o.Good
  Lm := leadP o.Lm
  hmid := midSpecP_of o.hmid o.hsh o.hL
  hLm := o.hL
  hsh := midShapeP_of o.hsh
  child := o.child
  hnode := o.hnode
  refines := o.refines
  ext_eq := o.ext_eq

/-- **`SSound` from S1's open obligations.** -/
theorem sSound_of_openSF {VS : SProg} {E : RecursionFast.Digest → RecursionFast.Proof → Log → Option Wit} (o : OpenSF VS E)
    (vk : RecursionFast.Digest) : SSound VS E vk :=
  sSound_of_openSM (openSF o) vk

end Lvm.E2F
end

section
set_option autoImplicit false
namespace Lvm.E2F
open RecursionFast Lvm.FS Lvm.T Lvm.ASM
open LeanVM.Parameters
open LeanVM.Protocol LeanVM.Protocol.Verifier LeanVM.Protocol.EndToEnd
open LeanVM.Protocol.Compile hiding Proof Bytes
open scoped NNReal ENNReal
variable {mid : List UInt8 → VerifierProgram (List LeanVM.Protocol.Verifier.StackClaim)} {Good : GoodRelM}
  {Lm : ℝ≥0∞}
section PinBridge
variable {recOf : List UInt8 → LeanVM.Protocol.Column CMain.nu20 → LeanVM.Protocol.Column 19}
  {reloc : List UInt8 → LeanVM.Protocol.Verifier.StackClaim → LeanVM.Protocol.Verifier.StackClaim}

end PinBridge
end Lvm.E2F
end

section
set_option autoImplicit false
namespace Lvm.E2F
open RecursionFast Lvm.FS Lvm.T Lvm.ASM
open LeanVM.Parameters
open LeanVM.Protocol LeanVM.Protocol.Verifier LeanVM.Protocol.EndToEnd
open LeanVM.Protocol.Compile hiding Proof Bytes
open scoped NNReal ENNReal
variable {mid : List UInt8 → VerifierProgram (List LeanVM.Protocol.Verifier.StackClaim)} {Good : GoodRelM}
  {Lm : ℝ≥0∞}
section W
variable (f : SFmt)

end W
end Lvm.E2F
end

section
set_option autoImplicit false
namespace Lvm.E2F
open RecursionFast Lvm.FS Lvm.T Lvm.ASM
open LeanVM.Parameters
open LeanVM.Protocol LeanVM.Protocol.Verifier LeanVM.Protocol.EndToEnd
open LeanVM.Protocol.Compile hiding Proof Bytes
open scoped NNReal ENNReal
variable {mid : List UInt8 → VerifierProgram (List LeanVM.Protocol.Verifier.StackClaim)} {Good : GoodRelM}
  {Lm : ℝ≥0∞}
section W
variable (f : SFmt)

/-- **`SSound` from S1's open obligations at a format `f`.** -/
theorem sSound_of_openSFW {VS : SProg} {E : RecursionFast.Digest → RecursionFast.Proof → Log → Option Wit}
    (o : OpenSFW f VS E) (vk : RecursionFast.Digest) : SSound VS E vk :=
  sSound_of_openSMW f (openSFW f o) vk

end W
end Lvm.E2F
end

-- ===== from `LvmE2VMidSpecF` =====

section
set_option autoImplicit false
namespace Lvm.E2V
open LeanVM.Parameters LeanVM.Protocol LeanVM.Protocol.Compile LeanVM.Protocol.Verifier
open Lvm.M3 (NoCG cg_ret cg_sample cg_readScalar cg_require cg_sampleChallenges)

theorem cg_pure {α : Type} (a : α) : NoCG (pure a : VerifierProgram α) := cg_ret a

end Lvm.E2V
end
