-- New for lvm2 σ_LEAF (SLF-L, 2026-11-16): S2GU's merged-tape front (`LvmS2GUFront`'s `b`-generic section, RF-2)
-- generalised from the two `cont` intervals `contIvB b` to any list `iv` of disjoint intervals in `[1, 2^13)` (S2GS: the
-- trace's, Q_sig's key leaf, the node's own key leaf). The proofs are `LvmS2GUFront`'s with `contB b`, `kksTB b` →
-- `contL iv`, `kksTL iv`; the two-interval facts (`contB_ivl`, `kksTB_split`, `kksF_eqB`) become `contL_zero`,
-- `kksTL_eq_sum`, `kksF_eqL` under `IvOk iv`. `contIvB b` is an instance (`ivOk_contIvB`); the definitions agree with
-- the `b` ones by `rfl` (`contL_contIvB`, `wireProgL_contIvB`, `tapeProgL_contIvB`).
import LvmS2GUFront

/-!
# The merged tape over a list of `cont` intervals

* Programs: `contL`, `wireProgL`, `tapeProgL`; the virtual inputs and relation `tapeInL`, `TapeRelL`.
* `IvOk iv`: every interval inside `[1, 2^13)`, pairwise disjoint. `kksTL iv` (`K_ks`), `kksTL_eq_sum`, `kksF_eqL`.
* The wire and the tape as specifications: `wire_identityL`, `wireUFL` (`_plain`, `_nil`, `_end`),
  `inClaim_of_wireTargetL`, `wireSpecLW`, `t1_spongeL`, the T1 tables and `tapeSpecLW`.
-/

set_option autoImplicit false

namespace Lvm.E2U

open LeanVM.Parameters LeanVM.Semantics LeanVM.Protocol.Compile LeanVM.Protocol.Verifier
open LeanVM.Protocol.KeccakGkr (laneWord errE tapeStates)
open LeanVM.Protocol.EndToEnd.Front (Doomed Stable)
open Lvm.E2V
open Lvm.KG (TapeOut dOf chainIn tapeIn)
open Lvm.ASM (εS)
open Finset
open scoped ENNReal

/-- **`cont` over a list of intervals** (`contB b = contL (contIvB b)`). -/
def contL (iv : List (ℕ × ℕ)) (j : ℕ) : Bool := iv.any fun ab ↦ decide (ab.1 ≤ j ∧ j ≤ ab.2)

theorem contL_contIvB (b : ℕ) : contL (contIvB b) = contB b := rfl

/-- **The merged tape's wire over the intervals `iv`** (`wireProgB` with `contIvB b` replaced by `iv`). -/
def wireProgL (iv : List (ℕ × ℕ)) (s : RecursionFast.Digest) (n : ℕ) (claim : KClaim E2) :
    VerifierProgram WireOutU :=
  sumcheckE2 gC2 (E2V.wireTargetF s n claim) 3 (List.replicate 20 none) >>= fun sc ↦
  e2Reads 3 >>= fun g ↦
  VerifierProgram.require (sc.2 = E2V.msEvalF claim.point claim.mu sc.1 0 (n - 1) * g.getD 0 0 +
    eTailF 13 20 sc.1 * (kksF iv claim.point claim.mu (sc.1.take 13) (2 ^ 20) * g.getD 1 0 +
      ikEvalF claim.point claim.mu (sc.1.take 13) (2 ^ 20) * g.getD 2 0)) >>= fun _ ↦
  slotProgE2 2 1 0 (E2V.dWF claim.weights) sc.1 (g.getD 0 0) >>= fun d ↦
  slotProgE2 5 5 22 (yWF claim.weights) (sc.1.take 13) (g.getD 1 0) >>= fun y ↦
  slotProgE2 5 4 10 (mWF claim.weights) (sc.1.take 13 ++ [0]) (g.getD 2 0) >>= fun m ↦
  pure ⟨sc, g, d, y, m⟩

theorem wireProgL_contIvB (b : ℕ) : wireProgL (contIvB b) = wireProgB b := rfl

/-- **The merged tape over the intervals `iv`** (`tapeProgB`'s twin). -/
def tapeProgL (iv : List (ℕ × ℕ)) (s : RecursionFast.Digest) (n : ℕ) : VerifierProgram TapeOutU :=
  e2Sep >>= fun _ ↦
  e2Samples gC1 20 >>= fun r ↦
  e2Reads 50 >>= fun ab ↦
  e2Samples gC1 1 >>= fun r20 ↦
  tapeGkrE2 21 (r ++ r20) (t1ValsF 20 13 (r ++ r20) ab) >>= fun claim ↦
  VerifierProgram.require (1 ≤ n ∧ n ≤ 2 ^ 20) >>= fun _ ↦
  wireProgL iv s n claim >>= fun wo ↦
  pure (r ++ r20, ab, claim, wo)

theorem tapeProgL_contIvB (b : ℕ) : tapeProgL (contIvB b) = tapeProgB b := rfl

/-- **The merged tape's virtual inputs over `iv`.** -/
def tapeInL (iv : List (ℕ × ℕ)) (s : RecursionFast.Digest) (n : ℕ) (col : ℕ → K) : ℕ → KeccakState :=
  tapeIn 20 13 s n (dU col) (yU col) (msgU col) (contL iv)

/-- **What the merged tape over `iv` proves** (`TapeRelB`'s twin). -/
def TapeRelL (iv : List (ℕ × ℕ)) (s : RecursionFast.Digest) (n : ℕ) (col : ℕ → K) : Prop :=
  TapeOut 20 s n (dU col) ∧
    ∀ j < 2 ^ 13, ∀ l < 25, yU col j l = laneWord (keccakF1600 (tapeInL iv s n col (2 ^ 20 + j))) l

variable {iv : List (ℕ × ℕ)}

/-- **`cont`'s intervals are well placed**: each inside `[1, 2^13)`, pairwise disjoint. -/
def IvOk (iv : List (ℕ × ℕ)) : Prop :=
  (∀ ab ∈ iv, 1 ≤ ab.1 ∧ ab.1 ≤ ab.2 ∧ ab.2 < 2 ^ 13) ∧ iv.Pairwise fun a c ↦ a.2 < c.1 ∨ c.2 < a.1

/-- S2GU's two intervals are well placed. -/
theorem ivOk_contIvB {b : ℕ} (hcb : 1 ≤ b ∧ b < 8080) : IvOk (contIvB b) := by
  refine ⟨fun ab hab ↦ ?_, ?_⟩
  · simp only [contIvB, List.mem_cons, List.mem_nil_iff, or_false] at hab
    rcases hab with rfl | rfl <;> (simp only; omega)
  · simp only [contIvB, List.pairwise_cons, List.mem_cons, List.mem_nil_iff, or_false, forall_eq,
      List.not_mem_nil, false_imp_iff, implies_true, List.Pairwise.nil, and_true]
    omega

/-- Row `0` starts a sponge. -/
theorem contL_zero (hiv : IvOk iv) : contL iv 0 = false := by
  rw [contL, List.any_eq_false]
  intro ab hab h
  have := (hiv.1 ab hab).1
  simp only [decide_eq_true_eq] at h
  omega

/-- `K_ks(x) = [x + 1 < 2^13]·cont_{x+1}·ι(2^20 + x + 1)` over the intervals `iv`. -/
def kksTL (iv : List (ℕ × ℕ)) (ρ μ : List E2) (x : ℕ) : E2 :=
  if x + 1 < 2 ^ 13 ∧ contL iv (x + 1) then E2V.iotaF ρ μ (2 ^ 20 + x + 1) else 0

/-- The intervals' kernels summed (`msIntKF` per interval). -/
theorem sum_msIntKF_list (hiv : IvOk iv) (ρ μ : List E2) (x : ℕ) :
    (iv.map fun ab ↦ msIntKF ρ μ (2 ^ 20) ab.1 ab.2 x).sum =
      if contL iv (x + 1) then E2V.iotaF ρ μ (2 ^ 20 + x + 1) else 0 := by
  obtain ⟨hin, hpw⟩ := hiv
  induction iv with
  | nil => simp [contL]
  | cons ab rest ih =>
    rw [List.pairwise_cons] at hpw
    have ih' := ih (fun c hc ↦ hin c (List.mem_cons_of_mem _ hc)) hpw.2
    rw [List.map_cons, List.sum_cons, ih']
    have hcons : contL (ab :: rest) (x + 1) = (decide (ab.1 ≤ x + 1 ∧ x + 1 ≤ ab.2) || contL rest (x + 1)) := rfl
    rw [hcons]
    unfold msIntKF
    by_cases h1 : ab.1 ≤ x + 1 ∧ x + 1 ≤ ab.2
    · have hr : contL rest (x + 1) = false := by
        rw [contL, List.any_eq_false]
        intro c hc hcd
        have := hpw.1 c hc
        simp only [decide_eq_true_eq] at hcd
        omega
      simp [h1, hr]
    · rw [if_neg h1, zero_add]
      cases hc : contL rest (x + 1)
      · rw [if_neg (by simp), if_neg (by simpa using h1)]
      · rw [if_pos rfl, if_pos (by simp)]

/-- **`K_ks` as the intervals' kernels.** -/
theorem kksTL_eq_sum (hiv : IvOk iv) (ρ μ : List E2) (x : ℕ) :
    kksTL iv ρ μ x = (iv.map fun ab ↦ msIntKF ρ μ (2 ^ 20) ab.1 ab.2 x).sum := by
  rw [sum_msIntKF_list hiv, kksTL]
  by_cases hc : contL iv (x + 1) = true
  · have hlt : x + 1 < 2 ^ 13 := by
      obtain ⟨ab, hab, h⟩ := List.any_eq_true.mp hc
      have := (hiv.1 ab hab).2.2
      simp only [decide_eq_true_eq] at h
      omega
    rw [if_pos ⟨hlt, hc⟩, if_pos hc]
  · rw [if_neg (fun h ↦ hc h.2), if_neg hc]

theorem foldl_add_eq_sum (l : List E2) (a : E2) : l.foldl (· + ·) a = a + l.sum := by
  induction l generalizing a with
  | nil => simp
  | cons y l ih => rw [List.foldl_cons, ih, List.sum_cons, add_assoc]

/-- **`K̃_ks` is `K_ks`'s extension** over well-placed intervals. -/
theorem kksF_eqL (hiv : IvOk iv) (ρ μ σ' : List E2) (hσ : σ'.length = 13) (hρ : 8 ≤ ρ.length) :
    kksF iv ρ μ σ' (2 ^ 20) = E2V.extF 13 σ' (kksTL iv ρ μ) := by
  have h4 : 5 ≤ σ'.length := by rw [hσ]; norm_num
  have hρ' : σ'.length - 5 ≤ ρ.length := by rw [hσ]; exact hρ
  have hb : 2 ^ σ'.length ∣ 2 ^ 20 := Nat.pow_dvd_pow 2 (by rw [hσ]; norm_num)
  rw [E2V.extF, Finset.sum_congr rfl fun x _ ↦ by rw [kksTL_eq_sum hiv], kksF, E2V.sumF, foldl_add_eq_sum, zero_add]
  obtain ⟨hin, -⟩ := hiv
  clear hb
  induction iv with
  | nil => simp
  | cons ab rest ih =>
    have hab := hin ab (List.mem_cons_self ..)
    simp only [List.map_cons, List.sum_cons, mul_add, Finset.sum_add_distrib]
    rw [ih fun c hc ↦ hin c (List.mem_cons_of_mem _ hc)]
    have i1 := sum_msIntKF ρ μ σ' (2 ^ 20) ab.1 ab.2 h4 hρ' (Nat.pow_dvd_pow 2 (by rw [hσ]; norm_num)) hab.1 hab.2.1
      (by rw [hσ]; exact hab.2.2)
    rw [hσ] at i1
    rw [i1]

/-- **The wiring identity at S2GU**: the input claim's sum over the 21-variable tape is the chain's constant plus
the kernel-weighted chain and sponge parts. -/
theorem wire_identityL (hiv0 : contL iv 0 = false) (ρ μ ω : List E2) (s : RecursionFast.Digest) {n : ℕ} (hn : 1 ≤ n)
    (hN : n ≤ 2 ^ 20) (col : ℕ → K) :
    ∑ i ∈ range (2 ^ 21), E2V.iotaF ρ μ i * E2V.omegaDotF ω (tapeInL iv s n col i) =
      E2V.iotaF ρ μ 0 * E2V.padDotF ω (Lvm.KG.digestBits s) +
        E2V.padDotF ω (fun _ ↦ false) * ∑ i ∈ range (n - 1), E2V.iotaF ρ μ (i + 1) +
        ∑ x ∈ range (2 ^ 20), (E2V.msKF ρ μ 0 (n - 1) x * E2V.gDTF ω (dU col) x +
          kksTL iv ρ μ x * gYTF ω (yU col) x + ikTF ρ μ x * gMTF ω (msgU col) x) := by
  rw [show (2 : ℕ) ^ 21 = 2 ^ 20 + 2 ^ 20 by norm_num, Finset.sum_range_add]
  have hch : ∑ i ∈ range (2 ^ 20), E2V.iotaF ρ μ i * E2V.omegaDotF ω (tapeInL iv s n col i) =
      ∑ i ∈ range (2 ^ 20), E2V.iotaF ρ μ i * E2V.omegaDotF ω (chainIn s n (dU col) i) :=
    Finset.sum_congr rfl fun i hi ↦ by rw [tapeInL, tapeIn, if_pos (Finset.mem_range.1 hi)]
  let Yp : ℕ → E2 := fun j ↦
    if j < 2 ^ 13 ∧ contL iv j then E2V.iotaF ρ μ (2 ^ 20 + j) * gYTF ω (yU col) (j - 1) else 0
  let Mp : ℕ → E2 := fun j ↦ if j < 2 ^ 13 then E2V.iotaF ρ μ (2 ^ 20 + j) * gMTF ω (msgU col) j else 0
  have hrow : ∀ j, E2V.iotaF ρ μ (2 ^ 20 + j) * E2V.omegaDotF ω (tapeInL iv s n col (2 ^ 20 + j)) = Yp j + Mp j := by
    intro j
    rw [tapeInL, tapeIn, if_neg (by (clear * - ; omega)), Nat.add_sub_cancel_left]
    by_cases hj : j < 2 ^ 13
    · rw [if_pos hj, omegaDotF_ks _ _ _ _ hj]
      simp only [Yp, Mp, hj, true_and, if_true]
      split_ifs <;> ring
    · rw [if_neg hj, E2V.omegaDotF_zero, mul_zero]
      simp only [Yp, Mp]
      rw [if_neg (fun h ↦ hj h.1), if_neg hj, add_zero]
  have hY : ∑ j ∈ range (2 ^ 20), Yp j = ∑ x ∈ range (2 ^ 20), kksTL iv ρ μ x * gYTF ω (yU col) x := by
    have key : ∀ M : ℕ, 2 ^ 13 ≤ M →
        ∑ j ∈ range (M + 1), Yp j = ∑ x ∈ range (M + 1), kksTL iv ρ μ x * gYTF ω (yU col) x := by
      intro M hM
      rw [Finset.sum_range_succ', Finset.sum_range_succ]
      have h0 : Yp 0 = 0 := by
        simp only [Yp]
        rw [if_neg (fun h ↦ by rw [hiv0] at h; simp at h)]
      have hN0 : kksTL iv ρ μ M * gYTF ω (yU col) M = 0 := by
        rw [kksTL, if_neg (fun h ↦ by (clear * - h hM; omega)), zero_mul]
      rw [h0, hN0]
      refine congrArg (· + 0) (Finset.sum_congr rfl fun x _ ↦ ?_)
      simp only [Yp, kksTL, Nat.add_sub_cancel, ← Nat.add_assoc]
      split_ifs <;> simp
    have e : (2 : ℕ) ^ 20 = (2 ^ 20 - 1) + 1 := by norm_num
    rw [show range (2 ^ 20) = range ((2 ^ 20 - 1) + 1) from congrArg range e]
    exact key _ (by norm_num)
  have hM : ∑ j ∈ range (2 ^ 20), Mp j = ∑ x ∈ range (2 ^ 20), ikTF ρ μ x * gMTF ω (msgU col) x :=
    Finset.sum_congr rfl fun x _ ↦ by
      simp only [Mp, ikTF]
      split_ifs <;> simp
  rw [hch, E2V.wire_identity_chF ρ μ ω s (dU col) hn hN, Finset.sum_congr rfl fun j _ ↦ hrow j,
    Finset.sum_add_distrib, hY, hM]
  simp only [Finset.sum_add_distrib]
  ring


/-- The S2GU wire sumcheck's family; the sponge data are read periodically. -/
noncomputable def wireUFL (iv : List (ℕ × ℕ)) (ρ μ ω : List E2) (m : ℕ) (col : ℕ → K) (acc : List E2) : E2 :=
  cubeSumF (fun pt ↦ E2V.extF 20 pt (E2V.msKF ρ μ 0 m) * E2V.extF 20 pt (E2V.gDTF ω (dU col)) +
    E2V.extF 20 pt (kksTL iv ρ μ) * E2V.extF 20 pt (fun x ↦ gYTF ω (yU col) (x % 2 ^ 13)) +
    E2V.extF 20 pt (ikTF ρ μ) * E2V.extF 20 pt (fun x ↦ gMTF ω (msgU col) (x % 2 ^ 13))) 20 acc

theorem wireUFL_plain {β : Type} (ρ μ ω : List E2) (m : ℕ) (col : β → ℕ → K) :
    PlainFamilyF (fun q acc ↦ wireUFL iv ρ μ ω m (col q) acc) 2 20 :=
  cube_plainFamilyF _ 20 fun _ pre post ↦
    PolyLEF.add (PolyLEF.add (polyLEF_mle_mul _ _ _ _ pre post) (polyLEF_mle_mul _ _ _ _ pre post))
      (polyLEF_mle_mul _ _ _ _ pre post)

theorem wireUFL_nil (ρ μ ω : List E2) (m : ℕ) (col : ℕ → K) :
    wireUFL iv ρ μ ω m col [] = ∑ x ∈ range (2 ^ 20), (E2V.msKF ρ μ 0 m x * E2V.gDTF ω (dU col) x +
      kksTL iv ρ μ x * gYTF ω (yU col) x + ikTF ρ μ x * gMTF ω (msgU col) x) := by
  rw [wireUFL, cubeSumF_nil]
  refine Finset.sum_congr rfl fun u hu ↦ ?_
  have hu' := Finset.mem_range.1 hu
  simp only [E2V.extF, sum_eqAtF_bitsF hu']
  have hY : kksTL iv ρ μ u * gYTF ω (yU col) (u % 2 ^ 13) = kksTL iv ρ μ u * gYTF ω (yU col) u := by
    unfold kksTL
    split_ifs with h
    · rw [Nat.mod_eq_of_lt (by (clear * - h; omega))]
    · simp
  have hM : ikTF ρ μ u * gMTF ω (msgU col) (u % 2 ^ 13) = ikTF ρ μ u * gMTF ω (msgU col) u := by
    unfold ikTF
    split_ifs with h
    · rw [Nat.mod_eq_of_lt h]
    · simp
  rw [hY, hM]

/-- **The family's end**, in the verifier's closed forms. -/
theorem wireUFL_end (hiv : IvOk iv) (ρ μ ω : List E2) {m : ℕ} (col : ℕ → K) {σ : List E2} (hσ : σ.length = 20)
    (hρ : 15 ≤ ρ.length) (hm : m < 2 ^ 20) :
    wireUFL iv ρ μ ω m col σ = E2V.msEvalF ρ μ σ 0 m * E2V.extF 20 σ (E2V.gDTF ω (dU col)) +
      eTailF 13 20 σ * (kksF iv ρ μ (σ.take 13) (2 ^ 20) * E2V.extF 13 (σ.take 13) (gYTF ω (yU col)) +
        ikEvalF ρ μ (σ.take 13) (2 ^ 20) * E2V.extF 13 (σ.take 13) (gMTF ω (msgU col))) := by
  have hσ' : (σ.take 13).length = 13 := by simp [hσ]
  rw [wireUFL, cubeSumF_full _ hσ,
    show E2V.extF 20 σ (E2V.msKF ρ μ 0 m) = E2V.msEvalF ρ μ σ 0 m by
      rw [E2V.extF, ← hσ]
      exact E2V.sum_msKF_zero ρ μ σ m (by rw [hσ]; norm_num) (by rw [hσ]; (clear * - hρ; omega))
        (by rw [hσ]; exact hm),
    extF_low (k := 13) hσ (by norm_num) (kksTL iv ρ μ) (fun x hx ↦ by rw [kksTL, if_neg (by (clear * - hx; omega))]),
    extF_low (k := 13) hσ (by norm_num) (ikTF ρ μ) (fun x hx ↦ by rw [ikTF, if_neg (by (clear * - hx; omega))]),
    extF_mod (k := 13) hσ (by norm_num), extF_mod (k := 13) hσ (by norm_num),
    ← kksF_eqL hiv ρ μ _ hσ' (by (clear * - hρ; omega)), ← ikEvalF_eq ρ μ _ hσ' (by (clear * - hρ; omega)), eTailF_eq,
    List.take_of_length_le (l := σ) (i := 20) (by rw [hσ])]
  ring

/-- **The wire sumcheck's claim is the input claim** (S2GU). -/
theorem inClaim_of_wireTargetL (hiv0 : contL iv 0 = false) (s : RecursionFast.Digest) {n : ℕ} (hn : 1 ≤ n)
    (hN : n ≤ 2 ^ 20)
    (claim : KClaim E2) (hρ : claim.point.length + 5 = 21) (col : ℕ → K)
    (hv : E2V.wireTargetF s n claim = wireUFL iv claim.point claim.mu claim.weights (n - 1) col []) :
    E2V.InClaimTrueF 21 (tapeInL iv s n col) claim := by
  rw [wireUFL_nil] at hv
  have hS := E2V.sum_range_iotaF_succ claim.point claim.mu (n - 1) (by rw [hρ]; (clear * - hN hn; omega))
  rw [CharTwo.sub_eq_add] at hS
  rw [E2V.InClaimTrueF, wire_identityL hiv0 _ _ _ s hn hN, hS]
  rw [E2V.wireTargetF] at hv
  linear_combination hv - (E2V.iotaF claim.point claim.mu 0 * E2V.padDotF claim.weights
    (Lvm.KG.digestBits s) + E2V.padDotF claim.weights (fun _ ↦ false) *
      (E2V.thrEvalF claim.point claim.mu (n - 1) + E2V.iotaF claim.point claim.mu 0)) *
      CharTwo.two_eq_zero (R := E2)


variable {β : Type} {C : List Ev → Set β} [Finite β] {T : ℝ≥0∞}

section WireSpecL


open Classical in
/-- The witness of `wireSpecL` (`wireSpecE2W` with the sponge terms and three slot reductions). -/
noncomputable def wireSpecLW (hiv : IvOk iv) (hst : Stable C) (hcard : ∀ h, (C h).ncard ≤ 1) (s : RecursionFast.Digest) {n : ℕ}
    (hn : 1 ≤ n) (hN : n ≤ 2 ^ 20) (claim : KClaim E2) (hρ : claim.point.length + 5 = 21)
    (colM : β → ℕ → K) (R : β → Prop) (hrT : (∑ _i ∈ range 7, errE 1) + T ≤ εS) :
    Spec (wireProgL iv s n claim)
      (Doomed C (fun q ↦ E2V.InClaimTrueF 21 (tapeInL iv s n (colM q)) claim ∧ R q))
      (fun out hist ↦ out.sc.1.length = 20 ∧ out.d.sl.1.length = 2 ∧ out.y.sl.1.length = 5 ∧
        out.m.sl.1.length = 5 ∧
        Doomed C (fun q ↦ RowColTrue 23 (colM q) out.d.row ∧ RowColTrue 23 (colM q) out.y.row ∧
          RowColTrue 23 (colM q) out.m.row ∧ R q) hist) εS 0 T :=
  have hρ' : 15 ≤ claim.point.length := by (clear * - hρ; omega)
  have hr0 : (∑ _i ∈ range 7, errE 1) + (0 : ℝ≥0∞) ≤ εS := le_trans (by rw [add_zero]; exact le_self_add) hrT
  ((sumcheckGSpec (T := 0) (L₀ := 1) hst hcard R
      (wireUFL_plain claim.point claim.mu claim.weights (n - 1) colM) (count := 3)
      (by norm_num) (by norm_num) (g := gC2) (by norm_num) errG_c2 20 [] (E2V.wireTargetF s n claim) (by simp)).mono
    (fun _ hd ↦ Doomed.mono hd fun q ⟨hv, hR⟩ ↦ ⟨inClaim_of_wireTargetL (contL_zero hiv) s hn hN claim hρ (colM q) hv, hR⟩)
    (fun _ _ h ↦ h) le_rfl le_rfl le_rfl).bind' fun sc ↦
  if hs : sc.1.length = 20 then
    have hs13 : (sc.1.take 13).length = 13 := by simp [hs]
    have hs14 : (sc.1.take 13 ++ [(0 : E2)]).length = 14 := by simp [hs]
    ((e2ReadsSpec (T := 0) hst (fun q ↦ sc.2 = wireUFL iv claim.point claim.mu claim.weights (n - 1) (colM q)
        ([] ++ sc.1) ∧ R q) zero_le 2).mono
      (fun _ hd ↦ hd.2) (fun _ _ h ↦ h) le_rfl le_rfl le_rfl).bind' fun g ↦
    (Spec.require (Pre := fun hist ↦ g.length = 2 + 1 ∧ Doomed C (fun q ↦ sc.2 =
        wireUFL iv claim.point claim.mu claim.weights (n - 1) (colM q) ([] ++ sc.1) ∧ R q) hist)
      (Post := fun _ hist ↦ Doomed C (fun q ↦
        g.getD 0 0 = slotSumF 20 2 0 (E2V.dWF claim.weights) (colM q) sc.1 ∧
          ((g.getD 1 0 = slotSumF 13 5 22 (yWF claim.weights) (colM q) (sc.1.take 13) ∧
            g.getD 2 0 = slotSumF 14 5 10 (mWF claim.weights) (colM q) (sc.1.take 13 ++ [0])) ∧ R q)) hist)
      (fun _ hd hcond ↦ Doomed.mono hd.2 fun q hq ↦ ⟨by
        rw [List.nil_append, wireUFL_end hiv claim.point claim.mu claim.weights (colM q) hs hρ'
            (by (clear * - hN hn; omega)),
          show E2V.extF 20 sc.1 (E2V.gDTF claim.weights (dU (colM q))) =
            slotSumF 20 2 0 (E2V.dWF claim.weights) (colM q) sc.1 from E2V.gD_slotF 20 0 _ _ _,
          gY_slotF, gM_slotF _ _ _ hs13, hcond, hq.1, hq.2.1.1, hq.2.1.2], hq.2.2⟩)).bind' fun _ ↦
    (slotSpecE2W (T := 0) hst hcard (k := 20) (b := 2) (sb := 1) (blk := 0) (m := 23) rfl (by norm_num)
        (E2V.dWF claim.weights) colM
        (fun q ↦ (g.getD 1 0 = slotSumF 13 5 22 (yWF claim.weights) (colM q) (sc.1.take 13) ∧
          g.getD 2 0 = slotSumF 14 5 10 (mWF claim.weights) (colM q) (sc.1.take 13 ++ [0])) ∧ R q)
        hs (g.getD 0 0) hr0).bind' fun d ↦
    if hd2 : d.sl.1.length = 2 then
    ((slotSpecE2W (T := 0) hst hcard (k := 13) (b := 5) (sb := 5) (blk := 22) (m := 23) rfl (by norm_num)
        (yWF claim.weights) colM
        (fun q ↦ RowColTrue 23 (colM q) d.row ∧
          g.getD 2 0 = slotSumF 14 5 10 (mWF claim.weights) (colM q) (sc.1.take 13 ++ [0]) ∧ R q)
        hs13 (g.getD 1 0) hr0).mono
      (fun _ hd ↦ Doomed.mono hd.2.2 fun q ⟨hy, hr, hm, hR⟩ ↦ ⟨hr, ⟨hy, hm⟩, hR⟩)
      (fun _ _ h ↦ h) le_rfl le_rfl le_rfl).bind' fun y ↦
    if hy5 : y.sl.1.length = 5 then
    ((slotSpecE2W (T := T) hst hcard (k := 14) (b := 5) (sb := 4) (blk := 10) (m := 23) rfl (by norm_num)
        (mWF claim.weights) colM
        (fun q ↦ RowColTrue 23 (colM q) d.row ∧ RowColTrue 23 (colM q) y.row ∧ R q)
        hs14 (g.getD 2 0) hrT).mono
      (fun _ hd ↦ Doomed.mono hd.2.2 fun q ⟨hm, hd', hy, hR⟩ ↦ ⟨hy, hd', hm, hR⟩)
      (fun _ _ h ↦ h) le_rfl le_rfl le_rfl).bind' fun m ↦
    (Spec.ret (⟨sc, g, d, y, m⟩ : WireOutU)).mono
      (fun _ hd ↦ ⟨hs, hd2, hy5, hd.1, Doomed.mono hd.2.2 fun q ⟨hd', hy, hm, hR⟩ ↦ ⟨hm, hd', hy, hR⟩⟩)
      (fun _ _ h ↦ h) le_rfl le_rfl le_rfl
    else Spec.dead.mono (fun _ hd ↦ hy5 hd.1) (fun _ _ h ↦ h) le_rfl le_rfl le_rfl
    else Spec.dead.mono (fun _ hd ↦ hd2 hd.1) (fun _ _ h ↦ h) le_rfl le_rfl le_rfl
  else Spec.dead.mono (fun _ hd ↦ hs hd.1) (fun _ _ h ↦ h) le_rfl le_rfl le_rfl

end WireSpecL

/-- **UTAPE-STMT 8** (owner V): **T1's region formula, the sponge half**: on the tape's relation and the `Y` word
claims `Ỹ_l(r_{<13}) = b_l`, the sponge half's output lane `l` at `r_{<20}` is `e·b_l + (1 − e)·z*_l` (rows
`j < 2^13` are `Y`, the void rows `Keccak-f(0)`). With the chain half (`TapeOut`, `D̃_l(r_{<20}) = a_l` for `l < 4`,
`a_l` free for `l ≥ 4`) and `r_20` drawn after `a ‖ b`, the GKR's output claim `t1ValsF` is the tape's. -/
theorem t1_spongeL (s : RecursionFast.Digest) (n : ℕ) (col : ℕ → K) (r ab : List E2) (hr : r.length = 21)
    (hout : TapeRelL iv s n col) (hY : TiedYF (yU col) r ab) :
    ∀ l < 25, E2V.stepMleF 20 (r.take 20) (fun j ↦ laneWord (keccakF1600 (tapeInL iv s n col (2 ^ 20 + j))) l) =
      eTailF 13 20 r * ab.getD (25 + l) 0 + (1 - eTailF 13 20 r) * kF (zStarK l) := by
  intro l hl
  set pt := r.take 20 with hpt
  have hptl : pt.length = 20 := by rw [hpt, List.length_take, hr]; rfl
  have ha : (pt.take 13).length = 13 := by rw [List.length_take, hptl]; rfl
  have hs : (pt.drop 13).length = 7 := by rw [List.length_drop, hptl]
  have hat : pt.take 13 = r.take 13 := by rw [hpt, List.take_take]; rfl
  -- the sponge half's rows: `Y` below `2^13`, `Keccak-f(0)` above
  have hf : ∀ j, laneWord (keccakF1600 (tapeInL iv s n col (2 ^ 20 + j))) l =
      if j < 2 ^ 13 then yU col j l else zStarK l := fun j ↦ by
    split
    · rename_i hj; exact (hout.2 j hj l hl).symm
    · rename_i hj
      have e : tapeInL iv s n col (2 ^ 20 + j) = Lvm.KSponge.zeroSt := by
        unfold tapeInL tapeIn
        rw [if_neg (by (clear * - ; omega)), if_neg (by (clear * - hj; omega))]
      rw [e]; rfl
  have he : eTailF 13 20 r = E2V.eqAtF (pt.drop 13) 0 := by
    have g : ∀ (c : List E2) (acc : E2), (c.map fun x ↦ 1 - x).foldl (· * ·) acc = acc * E2V.eqAtF c 0 := by
      intro c
      induction c with
      | nil => intro acc; simp [E2V.eqAtF]
      | cons x c ih =>
        intro acc
        rw [List.map_cons, List.foldl_cons, ih, E2V.eqAtF, if_neg (by (clear * - ; omega)), CharTwo.sub_eq_add,
          Nat.zero_div]
        ring
    rw [eTailF, E2V.prodF, g, one_mul]
  have hinner : ∀ o ∈ range (2 ^ 7), ∑ x ∈ range (2 ^ 13), E2V.eqAtF (pt.take 13) x *
      kF (laneWord (keccakF1600 (tapeInL iv s n col (2 ^ 20 + (x + 2 ^ 13 * o)))) l) =
      kF (zStarK l) + if o = 0 then ab.getD (25 + l) 0 - kF (zStarK l) else 0 := by
    intro o _
    by_cases ho : o = 0
    · subst ho
      rw [if_pos rfl, add_sub_cancel, ← hY l hl, E2V.stepMleF, ← hat]
      refine Finset.sum_congr rfl fun x hx ↦ ?_
      rw [Nat.mul_zero, Nat.add_zero, hf, if_pos (Finset.mem_range.1 hx)]
    · rw [if_neg ho, add_zero]
      have e : ∀ x ∈ range (2 ^ 13), E2V.eqAtF (pt.take 13) x *
          kF (laneWord (keccakF1600 (tapeInL iv s n col (2 ^ 20 + (x + 2 ^ 13 * o)))) l) =
          E2V.eqAtF (pt.take 13) x * kF (zStarK l) := fun x _ ↦ by
        rw [hf, if_neg (by have : 1 ≤ o := Nat.pos_of_ne_zero ho; nlinarith)]
      rw [Finset.sum_congr rfl e, ← Finset.sum_mul]
      have h1 := E2V.sum_eqAtF (pt.take 13)
      rw [ha] at h1
      rw [h1, one_mul]
  have hsum := E2V.sum_eqAtF (pt.drop 13)
  rw [hs] at hsum
  rw [E2V.stepMleF]
  conv_lhs => rw [← List.take_append_drop 13 pt, show 20 = 13 + (pt.drop 13).length by rw [hs]]
  rw [E2V.col_splitF ha, hs, Finset.sum_congr rfl fun o ho ↦ by rw [hinner o ho], he]
  simp only [mul_add, Finset.sum_add_distrib, ← Finset.sum_mul, hsum, mul_ite, mul_zero,
    Finset.sum_ite_eq', Finset.mem_range, Nat.two_pow_pos, if_true]
  ring


section TapeSpecL

/-- The chain half's output lane `l` at row `x`. -/
abbrev zChL (iv : List (ℕ × ℕ)) (s : RecursionFast.Digest) (n : ℕ) (col : ℕ → K) (x l : ℕ) : K :=
  laneWord (keccakF1600 (tapeInL iv s n col x)) l

/-- The sponge half's output lane `l` at sponge row `x` (tape row `2^20 + x`). -/
abbrev zSpL (iv : List (ℕ × ℕ)) (s : RecursionFast.Digest) (n : ℕ) (col : ℕ → K) (x l : ℕ) : K :=
  laneWord (keccakF1600 (tapeInL iv s n col (2 ^ 20 + x))) l

/-- **T1's zero-test table** on 26 bits (`x < 2^20`, the half `h`, the lane `l < 32`; `i = x + 2^20·(h + 2l)`):
`D − Z` on the chain half's four digest lanes, `Y − Z` on the sponge half's 25 lanes below `2^13`. -/
def t1DeltaL (iv : List (ℕ × ℕ)) (s : RecursionFast.Digest) (n : ℕ) (col : ℕ → K) (i : ℕ) : E2 :=
  if (i / 2 ^ 20) % 2 = 0 then
    (if i / 2 ^ 20 / 2 < 4 then
      kF (dU col (i % 2 ^ 20) (i / 2 ^ 20 / 2)) + kF (zChL iv s n col (i % 2 ^ 20) (i / 2 ^ 20 / 2)) else 0)
  else (if i / 2 ^ 20 / 2 < 25 ∧ i % 2 ^ 20 < 2 ^ 13 then
      kF (yU col (i % 2 ^ 20) (i / 2 ^ 20 / 2)) + kF (zSpL iv s n col (i % 2 ^ 20) (i / 2 ^ 20 / 2)) else 0)

theorem t1DeltaL_at (s : RecursionFast.Digest) (n : ℕ) (col : ℕ → K) {x : ℕ} (hx : x < 2 ^ 20) (h l : ℕ)
    (hh : h < 2) :
    t1DeltaL iv s n col (x + 2 ^ 20 * (h + 2 * l)) =
      if h = 0 then (if l < 4 then kF (dU col x l) + kF (zChL iv s n col x l) else 0)
      else (if l < 25 ∧ x < 2 ^ 13 then kF (yU col x l) + kF (zSpL iv s n col x l) else 0) := by
  have e1 : (x + 2 ^ 20 * (h + 2 * l)) / 2 ^ 20 = h + 2 * l := by
    rw [Nat.add_mul_div_left _ _ (Nat.two_pow_pos 20), Nat.div_eq_of_lt hx, zero_add]
  have e2 : (x + 2 ^ 20 * (h + 2 * l)) % 2 ^ 20 = x := by rw [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hx]
  rw [t1DeltaL, e1, e2, show (h + 2 * l) / 2 = l by (clear * - hh; omega),
    show (h + 2 * l) % 2 = h by (clear * - hh; omega)]


/-- **The table vanishing is the tape relation.** -/
theorem tapeRelL_of_zero (s : RecursionFast.Digest) (n : ℕ) (col : ℕ → K)
    (hz : ZeroOnF (t1DeltaL iv s n col) [] 26) : TapeRelL iv s n col := by
  rw [zeroOnF_nil] at hz
  refine ⟨fun x hx l hl ↦ ?_, fun j hj l hl ↦ ?_⟩
  · have := hz (x + 2 ^ 20 * (0 + 2 * l)) (by
      have : 2 * l < 2 ^ 6 := by (clear * - hl; omega)
      calc x + 2 ^ 20 * (0 + 2 * l) < 2 ^ 20 + 2 ^ 20 * (2 * l) := by (clear * - hx; omega)
        _ = 2 ^ 20 * (2 * l + 1) := by ring
        _ ≤ 2 ^ 20 * 2 ^ 6 := Nat.mul_le_mul_left _ this
        _ = 2 ^ 26 := by norm_num)
    rw [t1DeltaL_at s n col hx 0 l (by norm_num), if_pos rfl, if_pos hl] at this
    have e : tapeInL iv s n col x = chainIn s n (dU col) x := by rw [tapeInL, tapeIn, if_pos hx]
    exact (kF_eq_of_add _ _ this).trans (by rw [zChL, e])
  · have hj20 : j < 2 ^ 20 := lt_of_lt_of_le hj (Nat.pow_le_pow_right (by norm_num) (by norm_num))
    have := hz (j + 2 ^ 20 * (1 + 2 * l)) (by
      have : 2 * l + 1 < 2 ^ 6 := by (clear * - hl; omega)
      calc j + 2 ^ 20 * (1 + 2 * l) < 2 ^ 20 + 2 ^ 20 * (1 + 2 * l) := by (clear * - hj20; omega)
        _ = 2 ^ 20 * (2 * l + 1 + 1) := by ring
        _ ≤ 2 ^ 20 * 2 ^ 6 := Nat.mul_le_mul_left _ this
        _ = 2 ^ 26 := by norm_num)
    rw [t1DeltaL_at s n col hj20 1 l (by norm_num), if_neg one_ne_zero, if_pos ⟨hl, hj⟩] at this
    exact kF_eq_of_add _ _ this

/-- The sponge half at a 20-coordinate point: `e·Z̃_sp(r_{<13}) + (1 − e)·z*` (the void rows are `Keccak-f(0)`). -/
theorem stepMle_spL (s : RecursionFast.Digest) (n : ℕ) (col : ℕ → K) {r : List E2} (hr : r.length = 20) (l : ℕ) :
    E2V.stepMleF 20 r (fun x ↦ zSpL iv s n col x l) =
      eTailF 13 20 r * E2V.stepMleF 13 (r.take 13) (fun x ↦ zSpL iv s n col x l) +
        (1 - eTailF 13 20 r) * kF (zStarK l) := by
  have hz : ∀ x, 2 ^ 13 ≤ x → zSpL iv s n col x l = zStarK l := fun x hx ↦ by
    have e : tapeInL iv s n col (2 ^ 20 + x) = Lvm.KSponge.zeroSt := by
      unfold tapeInL tapeIn
      rw [if_neg (by (clear * - ; omega)), if_neg (by (clear * - hx; omega))]
    rw [zSpL, e]; rfl
  have hsplit : ∀ x, (kF (zSpL iv s n col x l) : E2) =
      (if x < 2 ^ 13 then kF (zSpL iv s n col x l) - kF (zStarK l) else 0) + kF (zStarK l) := fun x ↦ by
    split_ifs with h
    · ring
    · rw [hz x (by (clear * - h; omega)), zero_add]
  have hlow := extF_low (k := 13) hr (by norm_num)
    (fun x ↦ if x < 2 ^ 13 then (kF (zSpL iv s n col x l) : E2) - kF (zStarK l) else 0)
    (fun x hx ↦ by rw [if_neg (by (clear * - hx; omega))])
  have h1 := E2V.sum_eqAtF r
  have h13 := E2V.sum_eqAtF (r.take 13)
  rw [hr] at h1
  rw [show (r.take 13).length = 13 by simp [hr]] at h13
  rw [E2V.stepMleF, Finset.sum_congr rfl fun x _ ↦ by rw [hsplit x, mul_add], Finset.sum_add_distrib,
    ← Finset.sum_mul, h1, one_mul]
  rw [E2V.extF] at hlow
  rw [hlow, eTailF_eq, List.take_of_length_le (l := r) (i := 20) (by rw [hr]), E2V.extF, E2V.stepMleF]
  have e : ∑ x ∈ range (2 ^ 13), E2V.eqAtF (r.take 13) x *
      (if x < 2 ^ 13 then (kF (zSpL iv s n col x l) : E2) - kF (zStarK l) else 0) =
      ∑ x ∈ range (2 ^ 13), E2V.eqAtF (r.take 13) x * kF (zSpL iv s n col x l) - kF (zStarK l) := by
    rw [Finset.sum_congr rfl fun x hx ↦ by rw [if_pos (Finset.mem_range.1 hx), mul_sub], Finset.sum_sub_distrib,
      ← Finset.sum_mul, h13, one_mul]
  rw [e]
  ring

/-- **T1's gap table** on 6 bits (`h`, the lane `l`; `v = h + 2l`): the chain half's lane `l` at `r` minus `a_l`, the
sponge half's minus `e·b_l + (1 − e)·z*_l`. -/
def t1GapL (iv : List (ℕ × ℕ)) (s : RecursionFast.Digest) (n : ℕ) (col : ℕ → K) (r ab : List E2) (v : ℕ) : E2 :=
  if v / 2 < 25 then
    (if v % 2 = 0 then E2V.stepMleF 20 r (fun x ↦ zChL iv s n col x (v / 2)) - ab.getD (v / 2) 0
     else E2V.stepMleF 20 r (fun x ↦ zSpL iv s n col x (v / 2)) -
       (eTailF 13 20 r * ab.getD (25 + v / 2) 0 + (1 - eTailF 13 20 r) * kF (zStarK (v / 2))))
  else 0

theorem t1GapL_at (s : RecursionFast.Digest) (n : ℕ) (col : ℕ → K) (r ab : List E2) (h l : ℕ) (hh : h < 2) :
    t1GapL iv s n col r ab (h + 2 * l) =
      if l < 25 then
        (if h = 0 then E2V.stepMleF 20 r (fun x ↦ zChL iv s n col x l) - ab.getD l 0
         else E2V.stepMleF 20 r (fun x ↦ zSpL iv s n col x l) -
           (eTailF 13 20 r * ab.getD (25 + l) 0 + (1 - eTailF 13 20 r) * kF (zStarK l)))
      else 0 := by
  rw [t1GapL, show (h + 2 * l) / 2 = l by (clear * - hh; omega), show (h + 2 * l) % 2 = h by (clear * - hh; omega)]

/-- **The gap vanishing and the tied claims give T1's zero test at `r`.** -/
theorem t1DeltaL_zero_of_gap (s : RecursionFast.Digest) (n : ℕ) (col : ℕ → K) {r ab : List E2} (hr : r.length = 20)
    (hg : ZeroOnF (t1GapL iv s n col r ab) [] 6) (hD : E2V.TiedDF 20 (dU col) r ab) (hY : TiedYF (yU col) r ab) :
    ZeroOnF (t1DeltaL iv s n col) r 26 := by
  rw [zeroOnF_nil] at hg
  intro v hv
  rw [hr, show 26 - 20 = 6 by norm_num] at hv
  obtain ⟨h, l, hh, rfl⟩ : ∃ h l, h < 2 ∧ v = h + 2 * l := ⟨v % 2, v / 2, Nat.mod_lt _ (by norm_num), by omega⟩
  have hl32 : l < 32 := by (clear * - hv; omega)
  have hgap := hg (h + 2 * l) (by (clear * - hv; omega))
  rw [t1GapL_at s n col r ab h l hh] at hgap
  unfold foldTF
  rw [hr, Finset.sum_congr rfl fun x hx ↦ by rw [t1DeltaL_at s n col (Finset.mem_range.1 hx) h l hh]]
  by_cases h0 : h = 0
  · subst h0
    simp only [if_true]
    by_cases hl : l < 4
    · simp only [hl, if_true, mul_add, Finset.sum_add_distrib]
      have e1 := hD l hl
      rw [if_pos (by (clear * - hl; omega)), if_pos rfl, sub_eq_zero] at hgap
      simp only [E2V.stepMleF] at e1 hgap
      rw [show ∑ x ∈ range (2 ^ 20), E2V.eqAtF r x * kF (dU col x l) = _ from e1,
        show ∑ x ∈ range (2 ^ 20), E2V.eqAtF r x * kF (zChL iv s n col x l) = _ from hgap]
      exact CharTwo.add_self_eq_zero _
    · simp only [hl, if_false, mul_zero, Finset.sum_const_zero]
  · have h1 : h = 1 := by (clear * - hh h0; omega)
    subst h1
    simp only [one_ne_zero, if_false]
    by_cases hl : l < 25
    · rw [if_pos hl, if_neg one_ne_zero, sub_eq_zero, stepMle_spL s n col hr] at hgap
      have hlow := extF_low (k := 13) hr (by norm_num)
        (fun x ↦ if l < 25 ∧ x < 2 ^ 13 then (kF (yU col x l) : E2) + kF (zSpL iv s n col x l) else 0)
        (fun x hx ↦ by rw [if_neg (fun h ↦ by (clear * - h hx; omega))])
      have hE : E2V.eqAtF (r.drop 13) 0 = eTailF 13 20 r := by
        rw [eTailF_eq, List.take_of_length_le (l := r) (i := 20) (by rw [hr])]
      rw [E2V.extF] at hlow
      rw [hlow, hE, E2V.extF, Finset.sum_congr rfl fun x hx ↦ by
        rw [if_pos ⟨hl, Finset.mem_range.1 hx⟩, mul_add], Finset.sum_add_distrib]
      have hY' := hY l hl
      rw [E2V.stepMleF] at hY' hgap
      rw [hY']
      linear_combination hgap + (eTailF 13 20 r * ab.getD (25 + l) 0) * CharTwo.two_eq_zero (R := E2)
    · simp only [hl, false_and, if_false, mul_zero, Finset.sum_const_zero]

/-- **The GKR's output claim is T1's**: `r_20` drawn after `a ‖ b`, the 21-coordinate lane claims are `t1ValsF`'s
exactly when the gap's extension vanishes at `r_20`. -/
theorem gap_zero_of_t1L (s : RecursionFast.Digest) (n : ℕ) (col : ℕ → K) {r ab : List E2} (hr : r.length = 20)
    (c : E2) (hall : ∀ l < 25, E2V.stepMleF 21 (r ++ [c]) (fun x ↦ laneWord (keccakF1600 (tapeInL iv s n col x)) l) =
      (t1ValsF 20 13 (r ++ [c]) ab).getD l 0) :
    ZeroOnF (t1GapL iv s n col r ab) [c] 6 := by
  intro v hv
  rw [show 6 - [c].length = 5 from rfl] at hv
  unfold foldTF
  rw [show (2 : ℕ) ^ [c].length = 2 from rfl, Finset.sum_range_succ, Finset.sum_range_one,
    t1GapL_at s n col r ab 0 v (by norm_num), t1GapL_at s n col r ab 1 v (by norm_num)]
  simp only [E2V.eqAtF, Nat.zero_mod, show (1 : ℕ) % 2 = 1 from rfl, if_true,
    show ¬ ((0 : ℕ) = 1) from by norm_num, if_false, one_ne_zero, mul_one]
  by_cases hl : v < 25
  · rw [if_pos hl, if_pos hl]
    have h := hall v hl
    have e : E2V.stepMleF 21 (r ++ [c]) (fun x ↦ laneWord (keccakF1600 (tapeInL iv s n col x)) v) =
        (1 + c) * E2V.stepMleF 20 r (fun x ↦ zChL iv s n col x v) + c * E2V.stepMleF 20 r (fun x ↦ zSpL iv s n col x v) := by
      unfold E2V.stepMleF
      rw [show 21 = 20 + [c].length from rfl, E2V.col_splitF (s := [c]) hr, show (2 : ℕ) ^ [c].length = 2 from rfl,
        Finset.sum_range_succ, Finset.sum_range_one]
      have s0 : ∑ x ∈ range (2 ^ 20), E2V.eqAtF r x *
          (kF (laneWord (keccakF1600 (tapeInL iv s n col (x + 2 ^ 20 * 0))) v) : E2) =
          ∑ x ∈ range (2 ^ 20), E2V.eqAtF r x * kF (zChL iv s n col x v) :=
        Finset.sum_congr rfl fun x _ ↦ by rw [zChL, Nat.mul_zero, Nat.add_zero]
      have s1 : ∑ x ∈ range (2 ^ 20), E2V.eqAtF r x *
          (kF (laneWord (keccakF1600 (tapeInL iv s n col (x + 2 ^ 20 * 1))) v) : E2) =
          ∑ x ∈ range (2 ^ 20), E2V.eqAtF r x * kF (zSpL iv s n col x v) :=
        Finset.sum_congr rfl fun x _ ↦ by rw [zSpL, show x + 2 ^ 20 * 1 = 2 ^ 20 + x by ring]
      rw [s0, s1]
      simp only [E2V.eqAtF, Nat.zero_mod, show (1 : ℕ) % 2 = 1 from rfl, if_true,
        show ¬ ((0 : ℕ) = 1) from by norm_num, if_false, mul_one]
    have hv' : (t1ValsF 20 13 (r ++ [c]) ab).getD v 0 = (1 - c) * ab.getD v 0 +
        c * (eTailF 13 20 r * ab.getD (25 + v) 0 + (1 - eTailF 13 20 r) * kF (zStarK v)) := by
      have et : eTailF 13 20 (r ++ [c]) = eTailF 13 20 r := by
        rw [eTailF, eTailF, List.take_append_of_le_length (by rw [hr])]
      have gc : (r ++ [c]).getD 20 0 = c := by
        rw [List.getD_append_right _ _ _ _ (by rw [hr])]; simp [hr]
      rw [t1ValsF, List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range hl]
      simp only [Option.map_some, Option.getD_some, gc, et]
    rw [e, hv'] at h
    rw [CharTwo.sub_eq_add] at h
    linear_combination h
  · rw [if_neg hl, if_neg hl]
    simp


open Classical in
/-- The witness of `tapeSpecL`. -/
noncomputable def tapeSpecLW (hiv : IvOk iv) (hst : Stable C) (hcard : ∀ h, (C h).ncard ≤ 1) (s : RecursionFast.Digest) {n : ℕ}
    (colM : β → ℕ → K) (R : β → Prop) (hrT : (∑ _i ∈ range 7, errE 1) + T ≤ εS) :
    Spec (tapeProgL iv s n) (Doomed C (fun q ↦ TapeRelL iv s n (colM q) ∧ R q)) (TapePostU (C := C) colM R) εS 0 T :=
  (sepSpec (T' := 0) hst hcard _).bind' fun _ ↦
  ((zeroSpecE2 (T := 0) (L₀ := 1) hst hcard (g := gC1) (by norm_num)
      (fun q ↦ t1DeltaL iv s n (colM q)) R (n := 26) (m := 19) (by norm_num) errG_c1).mono
    (fun _ hd ↦ Doomed.mono hd fun q ⟨hz, hR⟩ ↦ ⟨tapeRelL_of_zero s n _ hz, hR⟩)
    (fun _ _ h ↦ h) le_rfl le_rfl le_rfl).bind' fun r ↦
  if hr : r.length = 20 then
    ((e2ReadsSpec (T := 0) hst (fun q ↦ ZeroOnF (t1DeltaL iv s n (colM q)) r 26 ∧ R q) zero_le 49).mono
      (fun _ hd ↦ by simpa using hd.2) (fun _ _ h ↦ h) le_rfl le_rfl le_rfl).bind' fun ab ↦
    if hab : ab.length = 50 then
      ((zeroSpecE2 (T := 0) (L₀ := 1) hst hcard (g := gC1) (by norm_num)
          (fun q ↦ t1GapL iv s n (colM q) r ab)
          (fun q ↦ E2V.TiedDF 20 (dU (colM q)) r ab ∧ TiedYF (yU (colM q)) r ab ∧ R q)
          (n := 6) (m := 0) (by norm_num) errG_c1).mono
        (fun _ hd ↦ Doomed.mono hd.2 fun q ⟨hg, hD, hY, hR⟩ ↦ ⟨t1DeltaL_zero_of_gap s n _ hr hg hD hY, hR⟩)
        (fun _ _ h ↦ h) le_rfl le_rfl le_rfl).bind' fun r20 ↦
      if h20 : r20.length = 1 then
        have hc1 : ∃ c, r20 = [c] := List.length_eq_one_iff.1 h20
        ((tapeGkrSpecE2W (T := 0) hst hcard
            (fun q ↦ E2V.TiedDF 20 (dU (colM q)) r ab ∧ TiedYF (yU (colM q)) r ab ∧ R q)
            (fun q ↦ tapeInL iv s n (colM q)) 15 (inst := r ++ r20) (output := t1ValsF 20 13 (r ++ r20) ab)
            (by simp [hr, h20]) (by simp [t1ValsF]) (by simpa using errG_c2)).mono
          (fun _ hd ↦ Doomed.mono hd.2 fun q ⟨hall, hD, hY, hR⟩ ↦ ⟨by
            obtain ⟨c, rfl⟩ := hc1
            exact gap_zero_of_t1L s n (colM q) hr c hall, hD, hY, hR⟩)
          (fun _ _ h ↦ h) le_rfl le_rfl le_rfl).bind' fun claim ↦
        if hc : claim.point.length + 5 = 21 then
          (Spec.require (T := 0) (c := 1 ≤ n ∧ n ≤ 2 ^ 20)
            (Post := fun _ hist ↦ (1 ≤ n ∧ n ≤ 2 ^ 20) ∧ (ClaimShapeF 15 claim ∧
              Doomed C (fun q ↦ ClaimTrueF (tapeStates 15 (tapeInL iv s n (colM q)) 24) 15 claim ∧
                (E2V.TiedDF 20 (dU (colM q)) r ab ∧ TiedYF (yU (colM q)) r ab ∧ R q)) hist))
            (fun _ hp hcond ↦ ⟨hcond, hp⟩)).bind' fun _ ↦
          if hb : 1 ≤ n ∧ n ≤ 2 ^ 20 then
            ((wireSpecLW hiv (T := T) hst hcard s hb.1 hb.2 claim hc colM
                (fun q ↦ E2V.TiedDF 20 (dU (colM q)) r ab ∧ TiedYF (yU (colM q)) r ab ∧ R q) hrT).mono
              (fun _ hd ↦ Doomed.mono hd.2.2 fun q ⟨hin, hR⟩ ↦ ⟨claimTrue_of_inClaimF _ claim hin, hR⟩)
              (fun _ _ h ↦ h) le_rfl le_rfl le_rfl).bind' fun wo ↦
            have e20 : (r ++ r20).take 20 = r := List.take_left' hr
            have e13 : (r ++ r20).take 13 = r.take 13 := List.take_append_of_le_length (by rw [hr]; norm_num)
            (Spec.ret ((r ++ r20, ab, claim, wo) : TapeOutU)).mono
              (fun _ hd ↦ ⟨by simp [hr, h20], hab, hd.1, Doomed.mono hd.2.2.2.2 fun q ⟨h1, h2, h3, hD, hY, hR⟩ ↦
                ⟨h1, h2, h3, by rwa [e20] at hD, fun l hl ↦ by have := hY l hl; rwa [e13] at this, hR⟩⟩)
              (fun _ _ h ↦ h) le_rfl le_rfl le_rfl
          else Spec.dead.mono (fun _ hd ↦ hb hd.1) (fun _ _ h ↦ h) le_rfl le_rfl le_rfl
        else Spec.dead.mono (fun _ (hd : ClaimShapeF 15 claim ∧ _) ↦ hc (by
            obtain ⟨-, h1, -⟩ := hd.1; (clear * - h1; omega))) (fun _ _ h ↦ h) le_rfl le_rfl le_rfl
      else Spec.dead.mono (fun _ hd ↦ h20 hd.1) (fun _ _ h ↦ h) le_rfl le_rfl le_rfl
    else Spec.dead.mono (fun _ hd ↦ hab hd.1) (fun _ _ h ↦ h) le_rfl le_rfl le_rfl
  else Spec.dead.mono (fun _ hd ↦ hr (by simpa using hd.1)) (fun _ _ h ↦ h) le_rfl le_rfl le_rfl

end TapeSpecL

end Lvm.E2U
