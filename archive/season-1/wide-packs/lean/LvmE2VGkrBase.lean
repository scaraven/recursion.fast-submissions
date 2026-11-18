-- New for lvm2 S1 (E2-F, E2F-V): the Keccak GKR's list algebra, linear transpose and RMFE embedding over a
-- field `F` of characteristic two (`LvmKeccakMultilinear`'s `eqKernel`/`dot`, `LvmKeccakLinear`'s transpose,
-- `LvmKeccakRmfe`'s `embP`/`projE`), generic in `F`, for `LvmE2VProg`'s `E2` layer.
import LvmE2VProg
import LvmE2VWireKer
import LvmKeccakCallerTape
import LvmQKeccakConst

/-!
# The GKR's base algebra over `F`

* bits: `bitF_xor`, `bitF_and`, `bitF_not`; lists: `sumF_filterMap_range`, `sumF_zip_filterMap`,
  `powersF_getD`, `eqKernelF_getD`, `dot_eqKernelF`, `sum_eqAtF`;
* the transpose: `linearTransposeF_getD`, `linearTransposeF_length`, **`transpose_bitsF`**;
* the RMFE: `embPF`, `projF`, **`projF_bilin`**, `instWeightsF_getD`, **`projected_eqF`**.

The RMFE identity is the `Bool`-level kernel check `rmfeOk_at` (`LvmKeccakRmfeLit`, field
independent); over `F` (characteristic two) a coefficient of a product of `0/1` polynomials is the
parity of the carry-less product's.
-/

set_option autoImplicit false

namespace Lvm.E2V

open LeanVM.Parameters LeanVM.Protocol.Verifier Finset Polynomial
open LeanVM.Protocol.KeccakGkr (Lb chiB colB thetaB iotaB rhoPiSrc rhoPiDst rhoPiSrc_lt rhoPiDst_lt
  rhoPiSrc_dst rhoPiDst_src parityL mulGF2 xorL bitsFrom bitsFrom_getD rmfeOk_at)

/-- `LvmE2VProg`'s tables (`Lvm.*`, `LvmDecideKeccak`) are the verifier language's. -/
theorem rmfeEmbed_eqV : Lvm.rmfeEmbed = LeanVM.Protocol.Verifier.rmfeEmbed := congrArg Prod.fst Lvm.Q1.rmfe_eq_V

theorem rmfeProject_eqV : Lvm.rmfeProject = LeanVM.Protocol.Verifier.rmfeProject :=
  congrArg Prod.snd Lvm.Q1.rmfe_eq_V

theorem keccakPi_eqV : Lvm.keccakPi = LeanVM.Parameters.keccakPi := rfl
theorem keccakRho_eqV : Lvm.keccakRho = LeanVM.Parameters.keccakRho := rfl
theorem keccakAlong_eqV : Lvm.keccakAlong = LeanVM.Protocol.Verifier.keccakAlong := rfl
theorem keccakRC_eqV : Lvm.keccakRC = LeanVM.Parameters.keccakRC := rfl

section

variable {F : Type} [Field F]

/-! ## Bits -/

@[simp] theorem bitF_true : (bitF true : F) = 1 := rfl
@[simp] theorem bitF_false : (bitF false : F) = 0 := rfl

theorem bitF_and (a b : Bool) : (bitF (a && b) : F) = bitF a * bitF b := by
  cases a <;> cases b <;> simp [bitF]

/-! ## Lists -/

theorem sumF_filterMap_range (n : ℕ) (p : ℕ → Prop) [DecidablePred p] (f : ℕ → F) :
    sumF ((List.range n).filterMap fun b ↦ if p b then some (f b) else none) =
      ∑ b ∈ range n, if p b then f b else 0 := by
  rw [sumF_eq_sum]
  induction n with
  | zero => simp
  | succ n ih =>
    rw [List.range_succ, List.filterMap_append, List.sum_append, ih, Finset.sum_range_succ]
    by_cases h : p n <;> simp [h]

theorem list_sum_getDF (l : List F) : l.sum = ∑ i ∈ range l.length, l.getD i 0 := by
  induction l with
  | nil => simp
  | cons x l ih => rw [List.sum_cons, ih, List.length_cons, Finset.sum_range_succ']; simp [add_comm]

theorem sumF_zip_filterMap (p : ℕ → Prop) [DecidablePred p] :
    ∀ (l₁ : List F) (l₂ : List ℕ), l₁.length = l₂.length →
      sumF ((List.zip l₁ l₂).filterMap fun x ↦ if p x.2 then some x.1 else none) =
        ∑ i ∈ range l₁.length, if p (l₂.getD i 0) then l₁.getD i 0 else 0
  | [], [], _ => by simp [sumF]
  | x :: l₁, y :: l₂, h => by
    rw [List.zip_cons_cons, List.length_cons, Finset.sum_range_succ']
    have ih := sumF_zip_filterMap p l₁ l₂ (by simpa using h)
    rw [sumF_eq_sum] at ih ⊢
    by_cases hp : p y
    · simp only [List.filterMap_cons, hp, ite_true, List.sum_cons, ih, List.getD_cons_succ,
        List.getD_cons_zero]
      ring
    · simp only [List.filterMap_cons, hp, ite_false, ih, List.getD_cons_succ, List.getD_cons_zero,
        add_zero]
  | [], _ :: _, h => by simp at h
  | _ :: _, [], h => by simp at h

theorem powersFromF_getD (acc base : F) : ∀ (n b : ℕ), b < n →
    (powersFromF acc base n).getD b 0 = acc * base ^ b
  | n + 1, 0, _ => by simp [powersFromF]
  | n + 1, b + 1, h => by
    rw [powersFromF, List.getD_cons_succ, powersFromF_getD _ base n b (by omega), pow_succ]
    ring

theorem powersF_getD (base : F) {n b : ℕ} (h : b < n) : (powersF base n).getD b 0 = base ^ b := by
  rw [powersF, powersFromF_getD 1 base n b h, one_mul]

/-! ## `eq_kernel` and `dot` -/

theorem eqKernelF_append (pt : List F) (r : F) :
    eqKernelF (pt ++ [r]) = (eqKernelF pt).map (· * (1 + r)) ++ (eqKernelF pt).map (· * r) := by
  unfold eqKernelF
  rw [List.foldl_concat]

theorem eqKernelF_length : ∀ pt : List F, (eqKernelF pt).length = 2 ^ pt.length := by
  intro pt
  induction pt using List.reverseRecOn with
  | nil => rfl
  | append_singleton pt r ih =>
    rw [eqKernelF_append, List.length_append, List.length_map, List.length_map, ih,
      List.length_append, List.length_singleton, pow_succ]
    ring

theorem getD_map_mulF (l : List F) (c : F) (w : ℕ) :
    (l.map (· * c)).getD w 0 = l.getD w 0 * c := by
  simp only [List.getD_eq_getElem?_getD, List.getElem?_map]
  cases l[w]? <;> simp

/-- **`eq_kernel` lists the equality weights.** -/
theorem eqKernelF_getD : ∀ (pt : List F) (w : ℕ),
    (eqKernelF pt).getD w 0 = if w < 2 ^ pt.length then eqAtF pt w else 0 := by
  intro pt
  induction pt using List.reverseRecOn with
  | nil =>
    intro w
    rcases w with _ | w
    · rfl
    · simp [eqKernelF, List.getD_eq_getElem?_getD]
  | append_singleton pt r ih =>
    intro w
    have hlen := eqKernelF_length pt
    rw [eqKernelF_append, List.length_append, List.length_singleton, eqAtF_append]
    by_cases hw : w < 2 ^ pt.length
    · rw [List.getD_append _ _ _ _ (by simpa [hlen] using hw), getD_map_mulF, ih,
        ite_eq_left hw, ite_eq_left (by rw [pow_succ]; omega), Nat.div_eq_of_lt hw]
      simp [eqAtF]
    · rw [List.getD_append_right _ _ _ _ (by simp [hlen]; omega), List.length_map, hlen,
        getD_map_mulF, ih]
      by_cases hw2 : w < 2 ^ (pt.length + 1)
      · have hq : w / 2 ^ pt.length = 1 :=
          Nat.div_eq_of_lt_le (by rw [pow_succ] at hw2; omega) (by omega)
        rw [ite_eq_left hw2, hq, ite_eq_left (by rw [pow_succ] at hw2; omega), eqAtF_mod pt w,
          eqAtF_mod pt (w - 2 ^ pt.length), ← Nat.mod_eq_sub_mod (by omega)]
        simp [eqAtF]
      · rw [ite_eq_right hw2, ite_eq_right (by rw [pow_succ] at hw2; omega), zero_mul]

theorem dotF_eq : ∀ (a b : List F), a.length = b.length →
    dotF a b = ∑ j ∈ range a.length, a.getD j 0 * b.getD j 0 := by
  intro a b h
  unfold dotF
  rw [← sumF, sumF_eq_sum]
  induction a generalizing b with
  | nil => simp
  | cons x a ih =>
    rcases b with _ | ⟨y, b⟩
    · simp at h
    · simp only [List.zipWith_cons_cons, List.sum_cons, List.length_cons, Finset.sum_range_succ']
      rw [ih b (by simpa using h)]
      simp [add_comm]

/-- **The verifier's `dot(eq[:n], w)`**: the equality-weighted sum of `w`. -/
theorem dot_eqKernelF (pt w : List F) (hn : w.length ≤ 2 ^ pt.length) :
    dotF ((eqKernelF pt).take w.length) w = ∑ j ∈ range w.length, eqAtF pt j * w.getD j 0 := by
  rw [dotF_eq _ _ (by simp [eqKernelF_length, hn]), List.length_take, eqKernelF_length,
    min_eq_left hn]
  refine Finset.sum_congr rfl fun j hj ↦ ?_
  have hj' := Finset.mem_range.1 hj
  rw [List.getD_eq_getElem?_getD, List.getElem?_take, ite_eq_left hj', ← List.getD_eq_getElem?_getD,
    eqKernelF_getD, ite_eq_left (by omega)]

/-! ## The linear map's transpose -/

/-- A θ column sum. -/
def colLF (v : ℕ → F) (x z : ℕ) : F := ∑ y ∈ range 5, v (64 * (x + 5 * y) + z)

/-- θ on vectors. -/
def thetaLF (v : ℕ → F) (p : ℕ) : F :=
  v p + colLF v ((p / 64 % 5 + 4) % 5) (p % 64) + colLF v ((p / 64 % 5 + 1) % 5) ((p % 64 + 63) % 64)

/-- `L = π ∘ ρ ∘ θ` on vectors. -/
def LlinF (v : ℕ → F) (j : ℕ) : F := thetaLF v (rhoPiSrc j)

/-- The transpose of θ. -/
def thetaTF (g : ℕ → F) (p : ℕ) : F :=
  g p + colLF g ((p / 64 % 5 + 1) % 5) (p % 64) + colLF g ((p / 64 % 5 + 4) % 5) ((p % 64 + 1) % 64)

theorem sum_regroupF (G : ℕ → F) :
    ∑ p ∈ range 1600, G p = ∑ x ∈ range 5, ∑ z ∈ range 64, ∑ y ∈ range 5, G (64 * (x + 5 * y) + z) := by
  rw [show 1600 = 25 * 64 from rfl, sum_range_mulB]
  rw [show 25 = 5 * 5 from rfl, sum_range_mulB, Finset.sum_comm]
  refine Finset.sum_congr rfl fun x _ ↦ ?_
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun z _ ↦ Finset.sum_congr rfl fun y _ ↦ ?_
  congr 1; ring

theorem sum_colF (g : ℕ → F) (H : ℕ → ℕ → F) :
    ∑ p ∈ range 1600, g p * H (p / 64 % 5) (p % 64) =
      ∑ x ∈ range 5, ∑ z ∈ range 64, H x z * colLF g x z := by
  rw [sum_regroupF]
  refine Finset.sum_congr rfl fun x hx ↦ Finset.sum_congr rfl fun z hz ↦ ?_
  rw [colLF, Finset.mul_sum]
  refine Finset.sum_congr rfl fun y hy ↦ ?_
  simp only [Finset.mem_range] at hx hz hy
  have h1 : (64 * (x + 5 * y) + z) / 64 % 5 = x := by omega
  have h2 : (64 * (x + 5 * y) + z) % 64 = z := by omega
  rw [h1, h2, mul_comm]

theorem sum_permF (n : ℕ) (σ τ : ℕ → ℕ) (hσ : ∀ x < n, σ x < n) (hτ : ∀ x < n, τ x < n)
    (hστ : ∀ x < n, σ (τ x) = x) (hτσ : ∀ x < n, τ (σ x) = x) (G : ℕ → F) :
    ∑ x ∈ range n, G (σ x) = ∑ x ∈ range n, G x :=
  Finset.sum_nbij' σ τ (fun x hx ↦ by simpa using hσ x (by simpa using hx))
    (fun x hx ↦ by simpa using hτ x (by simpa using hx))
    (fun x hx ↦ hτσ x (by simpa using hx)) (fun x hx ↦ hστ x (by simpa using hx))
    fun _ _ ↦ rfl

theorem theta_transposeF (g v : ℕ → F) :
    ∑ p ∈ range 1600, g p * thetaLF v p = ∑ p ∈ range 1600, thetaTF g p * v p := by
  simp only [thetaLF, thetaTF, mul_add, add_mul, Finset.sum_add_distrib]
  have t2 : ∑ p ∈ range 1600, g p * colLF v ((p / 64 % 5 + 4) % 5) (p % 64) =
      ∑ p ∈ range 1600, colLF g ((p / 64 % 5 + 1) % 5) (p % 64) * v p := by
    rw [sum_colF g (fun x z ↦ colLF v ((x + 4) % 5) z)]
    rw [show (∑ p ∈ range 1600, colLF g ((p / 64 % 5 + 1) % 5) (p % 64) * v p) =
      ∑ p ∈ range 1600, v p * colLF g ((p / 64 % 5 + 1) % 5) (p % 64) from
        Finset.sum_congr rfl fun _ _ ↦ mul_comm _ _]
    rw [sum_colF v (fun x z ↦ colLF g ((x + 1) % 5) z)]
    rw [← sum_permF 5 (fun x ↦ (x + 1) % 5) (fun x ↦ (x + 4) % 5) (by omega) (by omega)
      (by omega) (by omega)]
    refine Finset.sum_congr rfl fun x hx ↦ Finset.sum_congr rfl fun z _ ↦ ?_
    simp only [Finset.mem_range] at hx
    have : ((x + 1) % 5 + 4) % 5 = x := by omega
    rw [this, mul_comm]
  have t3 : ∑ p ∈ range 1600, g p * colLF v ((p / 64 % 5 + 1) % 5) ((p % 64 + 63) % 64) =
      ∑ p ∈ range 1600, colLF g ((p / 64 % 5 + 4) % 5) ((p % 64 + 1) % 64) * v p := by
    rw [sum_colF g (fun x z ↦ colLF v ((x + 1) % 5) ((z + 63) % 64))]
    rw [show (∑ p ∈ range 1600, colLF g ((p / 64 % 5 + 4) % 5) ((p % 64 + 1) % 64) * v p) =
      ∑ p ∈ range 1600, v p * colLF g ((p / 64 % 5 + 4) % 5) ((p % 64 + 1) % 64) from
        Finset.sum_congr rfl fun _ _ ↦ mul_comm _ _]
    rw [sum_colF v (fun x z ↦ colLF g ((x + 4) % 5) ((z + 1) % 64))]
    rw [← sum_permF 5 (fun x ↦ (x + 4) % 5) (fun x ↦ (x + 1) % 5) (by omega) (by omega)
      (by omega) (by omega)]
    refine Finset.sum_congr rfl fun x hx ↦ ?_
    rw [← sum_permF 64 (fun z ↦ (z + 1) % 64) (fun z ↦ (z + 63) % 64) (by omega) (by omega)
      (by omega) (by omega)]
    refine Finset.sum_congr rfl fun z hz ↦ ?_
    simp only [Finset.mem_range] at hx hz
    have e1 : ((x + 4) % 5 + 1) % 5 = x := by omega
    have e2 : ((z + 1) % 64 + 63) % 64 = z := by omega
    rw [e1, e2, mul_comm]
  rw [t2, t3]

theorem array_getD_toArrayF (l : List F) (i : ℕ) : l.toArray.getD i 0 = l.getD i 0 := by
  simp [Array.getD_eq_getD_getElem?, List.getD_eq_getElem?_getD]

theorem setIfInBounds_getDF (a : Array F) (i p : ℕ) (x : F) :
    (a.setIfInBounds i x).getD p 0 = if i = p ∧ i < a.size then x else a.getD p 0 := by
  simp only [Array.getD_eq_getD_getElem?, Array.getElem?_setIfInBounds]
  split_ifs <;> simp_all
  omega

theorem flatMap_getDF (G : ℕ → ℕ → F) (m : ℕ) :
    ∀ (n x z : ℕ), x < n → z < m →
      ((List.range n).flatMap fun x ↦ (List.range m).map (G x)).getD (m * x + z) 0 = G x z
  | 0, _, _, hx, _ => absurd hx (Nat.not_lt_zero _)
  | n + 1, x, z, hx, hz => by
    have hlen : ((List.range n).flatMap fun x ↦ (List.range m).map (G x)).length = n * m := by
      simp [List.length_flatMap, List.sum_replicate]
    rw [List.range_succ, List.flatMap_append]
    by_cases hxn : x < n
    · rw [List.getD_append _ _ _ _ (by rw [hlen]; nlinarith)]
      exact flatMap_getDF G m n x z hxn hz
    · have : x = n := by omega
      subst this
      rw [List.getD_append_right _ _ _ _ (by rw [hlen]; nlinarith), hlen]
      simp [Nat.mul_comm, hz, List.getD_eq_getElem?_getD]

theorem flatMap_lengthF (G : ℕ → ℕ → F) (m n : ℕ) :
    ((List.range n).flatMap fun x ↦ (List.range m).map (G x)).length = n * m := by
  simp [List.length_flatMap, List.sum_replicate]

/-- θ's input weights after ρπ. -/
def gOfF (w : List F) (p : ℕ) : F := w.getD (rhoPiDst p) 0

theorem inner_loopF (W : ℕ → F) (lane : ℕ) (g : Array F) :
    ∀ Z, ((List.range Z).foldl (fun g z ↦ g.setIfInBounds (64 * lane + z) (W z)) g).size =
        g.size ∧
      ∀ p, ((List.range Z).foldl (fun g z ↦ g.setIfInBounds (64 * lane + z) (W z)) g).getD p 0 =
        if 64 * lane ≤ p ∧ p < 64 * lane + Z ∧ p < g.size then W (p - 64 * lane)
        else g.getD p 0
  | 0 => ⟨rfl, fun p ↦ by simp; omega⟩
  | Z + 1 => by
    obtain ⟨hs, hg⟩ := inner_loopF W lane g Z
    rw [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil]
    refine ⟨by simp [hs], fun p ↦ ?_⟩
    rw [setIfInBounds_getDF, hg p, hs]
    split_ifs <;> first | rfl | (exfalso; omega) | (congr 1; omega)

theorem outer_loopF (w : List F) :
    ∀ L, L ≤ 25 →
      ((List.range L).foldl (fun g lane ↦ (List.range 64).foldl (fun g z ↦
        g.setIfInBounds (64 * lane + z)
          (w.toArray.getD (64 * keccakPi lane + (z + keccakRho.getD lane 0) % 64) 0)) g)
        (Array.replicate keccakBits 0)).size = 1600 ∧
      ∀ p, ((List.range L).foldl (fun g lane ↦ (List.range 64).foldl (fun g z ↦
        g.setIfInBounds (64 * lane + z)
          (w.toArray.getD (64 * keccakPi lane + (z + keccakRho.getD lane 0) % 64) 0)) g)
        (Array.replicate keccakBits 0)).getD p 0 = if p < 64 * L then gOfF w p else 0
  | 0, _ => ⟨by simp [keccakBits], fun p ↦ by
      simp [Array.getD_eq_getD_getElem?, keccakBits, Array.getElem?_replicate]
      split_ifs <;> rfl⟩
  | L + 1, hL => by
    obtain ⟨hs, hg⟩ := outer_loopF w L (by omega)
    rw [List.range_succ (n := L), List.foldl_append, List.foldl_cons, List.foldl_nil]
    obtain ⟨hs', hg'⟩ := inner_loopF
      (fun z ↦ w.toArray.getD (64 * keccakPi L + (z + keccakRho.getD L 0) % 64) 0) L
      ((List.range L).foldl (fun g lane ↦ (List.range 64).foldl (fun g z ↦
        g.setIfInBounds (64 * lane + z)
          (w.toArray.getD (64 * keccakPi lane + (z + keccakRho.getD lane 0) % 64) 0)) g)
        (Array.replicate keccakBits 0)) 64
    refine ⟨hs'.trans hs, fun p ↦ ?_⟩
    rw [hg' p, hg p, hs]
    by_cases h1 : 64 * L ≤ p ∧ p < 64 * L + 64 ∧ p < 1600
    · rw [ite_eq_left h1, ite_eq_left (by omega), array_getD_toArrayF, gOfF, rhoPiDst]
      have e1 : p / 64 = L := by omega
      have e2 : p % 64 = p - 64 * L := by omega
      rw [e1, e2, keccakPi_eqV, keccakRho_eqV]
    · rw [ite_eq_right h1]
      by_cases h2 : p < 64 * L
      · rw [ite_eq_left h2, ite_eq_left (by omega)]
      · rw [ite_eq_right h2, ite_eq_right (by omega)]

theorem columns_getDF (A : Array F) {x z : ℕ} (hx : x < 5) (hz : z < 64) :
    ((List.range 5).flatMap fun x ↦ (List.range 64).map fun z ↦
        sumF ((List.range 5).map fun y ↦ A.getD (64 * (x + 5 * y) + z) 0)).toArray.getD
      (64 * x + z) 0 = colLF (fun p ↦ A.getD p 0) x z := by
  rw [array_getD_toArrayF, flatMap_getDF (fun x z ↦
    sumF ((List.range 5).map fun y ↦ A.getD (64 * (x + 5 * y) + z) 0)) 64 5 x z hx hz]
  rw [sumF_map_range]
  rfl

theorem transposeList_getDF (A : Array F) (g : ℕ → F) (hA : ∀ p < 1600, A.getD p 0 = g p)
    {p : ℕ} (hp : p < 1600) :
    ((List.range 25).flatMap fun lane ↦ (List.range 64).map fun z ↦
      A.getD (64 * lane + z) 0 +
        ((List.range 5).flatMap fun x ↦ (List.range 64).map fun z ↦
          sumF ((List.range 5).map fun y ↦ A.getD (64 * (x + 5 * y) + z) 0)).toArray.getD
          (64 * ((lane % 5 + 1) % 5) + z) 0 +
        ((List.range 5).flatMap fun x ↦ (List.range 64).map fun z ↦
          sumF ((List.range 5).map fun y ↦ A.getD (64 * (x + 5 * y) + z) 0)).toArray.getD
          (64 * ((lane % 5 + 4) % 5) + (z + 1) % 64) 0).getD p 0 = thetaTF g p := by
  have hp' : p = 64 * (p / 64) + p % 64 := by omega
  conv_lhs => rw [hp']
  rw [flatMap_getDF _ 64 25 (p / 64) (p % 64) (by omega) (Nat.mod_lt _ (by omega))]
  rw [columns_getDF _ (by omega) (Nat.mod_lt _ (by omega)),
    columns_getDF _ (by omega) (Nat.mod_lt _ (by omega)), ← hp', hA p hp]
  have hcol : ∀ x z, x < 5 → z < 64 → colLF (fun p ↦ A.getD p 0) x z = colLF g x z := by
    intro x z hx hz
    refine Finset.sum_congr rfl fun y hy ↦ ?_
    simp only [Finset.mem_range] at hy
    exact hA _ (by omega)
  rw [hcol _ _ (by omega) (Nat.mod_lt _ (by omega)), hcol _ _ (by omega) (Nat.mod_lt _ (by omega))]
  rfl

/-- **`linear_transpose` in closed form.** -/
theorem linearTransposeF_getD (w : List F) {p : ℕ} (hp : p < 1600) :
    (linearTransposeF w).getD p 0 = thetaTF (gOfF w) p := by
  obtain ⟨-, hg⟩ := outer_loopF w 25 le_rfl
  exact transposeList_getDF _ (gOfF w) (fun q hq ↦ by rw [hg, ite_eq_left (by omega)]) hp

theorem linearTransposeF_length (w : List F) : (linearTransposeF w).length = 1600 := by
  unfold linearTransposeF
  simp only []
  rw [flatMap_lengthF]

/-- **The transpose.** -/
theorem transposeF (w : List F) (v : ℕ → F) :
    ∑ j ∈ range 1600, w.getD j 0 * LlinF v j =
      ∑ j ∈ range 1600, (linearTransposeF w).getD j 0 * v j := by
  have h1 : ∑ j ∈ range 1600, w.getD j 0 * LlinF v j =
      ∑ p ∈ range 1600, gOfF w p * thetaLF v p :=
    Finset.sum_nbij' rhoPiSrc rhoPiDst (fun _ _ ↦ Finset.mem_range.2 rhoPiSrc_lt)
      (fun p hp ↦ Finset.mem_range.2 (rhoPiDst_lt (Finset.mem_range.1 hp)))
      (fun j hj ↦ rhoPiDst_src (Finset.mem_range.1 hj))
      (fun p hp ↦ rhoPiSrc_dst (Finset.mem_range.1 hp))
      fun j hj ↦ by rw [LlinF, gOfF, rhoPiDst_src (Finset.mem_range.1 hj)]
  rw [h1, theta_transposeF]
  refine Finset.sum_congr rfl fun p hp ↦ ?_
  rw [linearTransposeF_getD w (Finset.mem_range.1 hp)]

/-! ## Characteristic two -/

variable [CharP F 2]

theorem bitF_xor (a b : Bool) : (bitF (a ^^ b) : F) = bitF a + bitF b := by
  cases a <;> cases b <;> simp [bitF, CharTwo.add_self_eq_zero]

theorem bitF_not (a : Bool) : (bitF (!a) : F) = 1 + bitF a := by
  cases a <;> simp [bitF, CharTwo.add_self_eq_zero]

theorem bitF_colB (f : ℕ → Bool) (x z : ℕ) :
    (bitF (colB f x z) : F) = colLF (fun p ↦ bitF (f p)) x z := by
  simp only [colB, bitF_xor, colLF, Finset.sum_range_succ, Finset.sum_range_zero]
  ring_nf

theorem bitF_Lb (f : ℕ → Bool) (j : ℕ) : (bitF (Lb f j) : F) = LlinF (fun p ↦ bitF (f p)) j := by
  simp only [Lb, thetaB, bitF_xor, bitF_colB, LlinF, thetaLF]

/-- The transpose on bits. -/
theorem transpose_bitsF (w : List F) (f : ℕ → Bool) :
    ∑ j ∈ range 1600, w.getD j 0 * bitF (Lb f j) =
      ∑ j ∈ range 1600, (linearTransposeF w).getD j 0 * bitF (f j) := by
  simp only [bitF_Lb]
  exact transposeF w _

/-- The equality weights sum to one. -/
theorem sum_eqAtF : ∀ pt : List F, ∑ w ∈ range (2 ^ pt.length), eqAtF pt w = 1
  | [] => by simp
  | r :: rs => by
    rw [List.length_cons, sum_cube_succW, ← sum_eqAtF rs, Finset.sum_congr rfl fun w _ ↦ ?_]
    rw [eqAtF_succ, eqAtF_succ]
    have h1 : 2 * w % 2 = 0 := by omega
    have h2 : (2 * w + 1) % 2 = 1 := by omega
    have h3 : 2 * w / 2 = w := by omega
    have h4 : (2 * w + 1) / 2 = w := by omega
    simp only [h1, h2, h3, h4, ite_true, zero_ne_one, ite_false]
    rw [← add_mul, add_assoc, CharTwo.add_self_eq_zero, add_zero, one_mul]

/-! ## The RMFE over `F` -/

/-- A binary polynomial, coefficient list lowest first, over `F`. -/
noncomputable def polyOfBitsF : List Bool → F[X]
  | [] => 0
  | b :: l => C (bitF b) + X * polyOfBitsF l

theorem coeff_polyOfBitsF : ∀ (l : List Bool) (c : ℕ),
    (polyOfBitsF l : F[X]).coeff c = bitF (l.getD c false)
  | [], c => by simp [polyOfBitsF]
  | b :: l, 0 => by simp [polyOfBitsF]
  | b :: l, c + 1 => by simp [polyOfBitsF, coeff_polyOfBitsF l c]

theorem polyOfBitsF_xorL : ∀ A B : List Bool,
    (polyOfBitsF (xorL A B) : F[X]) = polyOfBitsF A + polyOfBitsF B
  | [], l => by simp [xorL, polyOfBitsF]
  | x :: xs, [] => by simp [xorL, polyOfBitsF]
  | x :: xs, y :: ys => by
    simp only [xorL, polyOfBitsF, polyOfBitsF_xorL xs ys, bitF_xor, C_add]
    ring

theorem polyOfBitsF_mulGF2 : ∀ A B : List Bool,
    (polyOfBitsF (mulGF2 A B) : F[X]) = polyOfBitsF A * polyOfBitsF B
  | [], B => by simp [mulGF2, polyOfBitsF]
  | a :: A, B => by
    rw [mulGF2, polyOfBitsF_xorL]
    cases a <;> simp [polyOfBitsF, polyOfBitsF_mulGF2 A B] <;> ring

/-- `emb_a` over `F`. -/
noncomputable def embPF (a : ℕ) : F[X] := polyOfBitsF (bitsFrom (rmfeEmbed.getD a 0) 53)

theorem embPF_coeff (a c : ℕ) :
    (embPF a : F[X]).coeff c = if c < 53 then bitF ((rmfeEmbed.getD a 0).testBit c) else 0 := by
  rw [embPF, coeff_polyOfBitsF, bitsFrom_getD]
  by_cases h : c < 53 <;> simp [h]

theorem embPF_natDegree (a : ℕ) : (embPF a : F[X]).natDegree ≤ 52 := by
  rw [natDegree_le_iff_coeff_eq_zero]
  intro c hc
  rw [embPF_coeff, ite_eq_right (by exact_mod_cast (show ¬ c < 53 by omega))]

/-- The projection to bit `mask`. -/
noncomputable def projF (mask : ℕ) (P : F[X]) : F :=
  ∑ c ∈ range 105, if mask.testBit c then P.coeff c else 0

theorem projF_add (mask : ℕ) (P Q : F[X]) : projF mask (P + Q) = projF mask P + projF mask Q := by
  simp only [projF, coeff_add, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun c _ ↦ ?_
  split_ifs <;> simp

theorem projF_C_mul (mask : ℕ) (a : F) (P : F[X]) : projF mask (C a * P) = a * projF mask P := by
  simp only [projF, coeff_C_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl fun c _ ↦ ?_
  split_ifs <;> simp

theorem projF_sum {ι : Type} (mask : ℕ) (s : Finset ι) (P : ι → F[X]) :
    projF mask (∑ i ∈ s, P i) = ∑ i ∈ s, projF mask (P i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [projF]
  | insert a s ha ih => rw [Finset.sum_insert ha, projF_add, ih, Finset.sum_insert ha]

theorem sum_bitF_xor (f : ℕ → Bool) (n : ℕ) :
    ∑ c ∈ range n, (bitF (f c) : F) = bitF ((List.range n).foldl (fun acc c ↦ acc ^^ f c) false) := by
  induction n with
  | zero => simp
  | succ n ih => rw [Finset.sum_range_succ, ih, List.range_succ, List.foldl_concat, bitF_xor]

/-- **The embedding lemma over `F`**. -/
theorem projF_embP_mul {i a b : ℕ} (hi : i < 32) (ha : a < 32) (hb : b < 32) :
    projF (rmfeProject.getD i 0) (embPF a * embPF b : F[X]) = if i = a ∧ a = b then 1 else 0 := by
  rw [embPF, embPF, ← polyOfBitsF_mulGF2]
  unfold projF
  simp_rw [coeff_polyOfBitsF]
  have h : ∀ c, (if (rmfeProject.getD i 0).testBit c then
      (bitF ((mulGF2 (bitsFrom (rmfeEmbed.getD a 0) 53) (bitsFrom (rmfeEmbed.getD b 0) 53)).getD
        c false) : F) else 0) =
      bitF ((rmfeProject.getD i 0).testBit c &&
        (mulGF2 (bitsFrom (rmfeEmbed.getD a 0) 53) (bitsFrom (rmfeEmbed.getD b 0) 53)).getD
          c false) := by
    intro c
    cases (rmfeProject.getD i 0).testBit c <;> simp
  simp_rw [h]
  rw [sum_bitF_xor]
  have := rmfeOk_at ha hb hi
  rw [← rmfeEmbed_eqV, ← rmfeProject_eqV] at this
  unfold parityL at this
  rw [this]
  by_cases h2 : a = b
  · subst h2
    by_cases h1 : i = a
    · subst h1; simp
    · have h3 : (i == a) = false := by simpa using h1
      simp [h3, h1]
  · have : (a == b) = false := by simpa using h2
    simp [this, h2]

/-- **Bilinearity** over `F`. -/
theorem projF_bilin {i : ℕ} (hi : i < 32) (u v : ℕ → F) :
    projF (rmfeProject.getD i 0)
      ((∑ a ∈ range 32, C (u a) * embPF a) * (∑ b ∈ range 32, C (v b) * embPF b)) = u i * v i := by
  rw [Finset.sum_mul_sum, projF_sum]
  have h : ∀ a ∈ range 32, projF (rmfeProject.getD i 0)
      (∑ b ∈ range 32, C (u a) * embPF a * (C (v b) * embPF b)) =
        if a = i then u i * v i else 0 := by
    intro a ha
    rw [projF_sum]
    have h2 : ∀ b ∈ range 32, projF (rmfeProject.getD i 0) (C (u a) * embPF a * (C (v b) * embPF b)) =
        u a * v b * (if i = a ∧ a = b then 1 else 0) := by
      intro b hb
      rw [show C (u a) * embPF a * (C (v b) * embPF b) = C (u a * v b) * (embPF a * embPF b) by
        rw [C_mul]; ring, projF_C_mul, projF_embP_mul hi (Finset.mem_range.1 ha)
          (Finset.mem_range.1 hb)]
    rw [Finset.sum_congr rfl h2]
    by_cases hai : a = i
    · subst hai
      rw [Finset.sum_eq_single a (fun b _ hb ↦ by simp [Ne.symm hb]) (fun h ↦ absurd ha h)]
      simp
    · rw [ite_eq_right hai]
      exact Finset.sum_eq_zero fun b _ ↦ by simp [Ne.symm hai]
  rw [Finset.sum_congr rfl h, Finset.sum_ite_eq' (range 32) i, ite_eq_left (Finset.mem_range.2 hi)]

theorem embPF_eval (a : ℕ) (s : F) :
    (embPF a).eval s = ∑ b ∈ range 53, if (rmfeEmbed.getD a 0).testBit b then s ^ b else 0 := by
  rw [eval_eq_sum_range' (n := 53) (by have := embPF_natDegree (F := F) a; omega)]
  refine Finset.sum_congr rfl fun b hb ↦ ?_
  rw [embPF_coeff, ite_eq_left (Finset.mem_range.1 hb)]
  cases (rmfeEmbed.getD a 0).testBit b <;> simp

theorem instWeightsF_length (s : F) : (instWeightsF s).length = 32 := by
  simp [instWeightsF, rmfeEmbed_eqV, LeanVM.Protocol.KeccakGkr.rmfeEmbed_length]

/-- **The instance weights at `s`** are `emb_a(s)`. -/
theorem instWeightsF_getD (s : F) {a : ℕ} (ha : a < 32) :
    (instWeightsF s).getD a 0 = (embPF a).eval s := by
  have hl : a < rmfeEmbed.length := by rw [rmfeEmbed_eqV, LeanVM.Protocol.KeccakGkr.rmfeEmbed_length]; exact ha
  rw [embPF_eval, instWeightsF, List.getD_eq_getElem?_getD, List.getElem?_map,
    List.getElem?_eq_getElem hl, List.getD_eq_getElem _ 0 hl]
  simp only [Option.map_some, Option.getD_some]
  rw [sumF_filterMap_range, show embedBits = 53 from rfl]
  refine Finset.sum_congr rfl fun b hb ↦ ?_
  rw [powersF_getD s (Finset.mem_range.1 hb)]

/-- **The verifier's projected value** over `F`. -/
theorem projected_eqF (mu product : List F) (hmu : mu.length = 32) (G : F[X])
    (hG : ∀ c < 105, product.getD c 0 = G.coeff c) :
    sumF ((List.range productBits).map fun c ↦
      sumF ((List.zip mu rmfeProject).filterMap fun (m, mask) ↦
        if mask.testBit c then some m else none) * product.getD c 0) =
      ∑ i ∈ range 32, mu.getD i 0 * projF (rmfeProject.getD i 0) G := by
  rw [sumF_map_range]
  have h : ∀ c ∈ range productBits, sumF ((List.zip mu rmfeProject).filterMap fun (m, mask) ↦
      if mask.testBit c then some m else none) * product.getD c 0 =
        ∑ i ∈ range 32, mu.getD i 0 * (if (rmfeProject.getD i 0).testBit c then G.coeff c else 0) := by
    intro c hc
    have e : (fun (x : F × ℕ) ↦ match x with | (m, mask) => if mask.testBit c then some m else none) =
        fun x ↦ if x.2.testBit c then some x.1 else none := by
      funext x; rfl
    rw [e, sumF_zip_filterMap (fun mask ↦ mask.testBit c) mu rmfeProject
      (by rw [hmu, rmfeProject_eqV, LeanVM.Protocol.KeccakGkr.rmfeProject_length]), hmu, Finset.sum_mul,
      hG c (Finset.mem_range.1 hc)]
    refine Finset.sum_congr rfl fun i _ ↦ ?_
    split_ifs <;> simp
  rw [Finset.sum_congr rfl h, Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  rw [projF, Finset.mul_sum]
  rfl

end

end Lvm.E2V
