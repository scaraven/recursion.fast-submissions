-- Ported from leanVM `formal/lean_vm/LeanVM/Protocol/Keccak/LayerSum.lean` (formal rev 40f877dc) as `LvmKeccakLayerSum` for lvm (WP-2).
/-
  LeanVM.Protocol.Keccak.LayerSum

  The algebra of a layer's sumchecks: the pack and segment rounds and the position rounds as
  sumcheck families, the final check's terms, and the batched claim on the states before the
  round, through the transpose of the linear map.
-/
import LvmKeccakRounds
import LvmKeccakMultilinear
import LvmKeccakRmfeLit

-- ===== merged from `LvmKeccakRmfe` (GOLF module merge: `LvmKeccakRmfe.lean` is now a stub importing `LvmKeccakLayerSum`) =====
section
-- Ported from leanVM `formal/lean_vm/LeanVM/Protocol/Keccak/Rmfe.lean` (formal rev 40f877dc) as `LvmKeccakRmfe` for lvm (WP-2).
/-
  LeanVM.Protocol.Keccak.Rmfe

  The reverse multiplication-friendly embedding of `verifyKeccak`: the verifier's `RMFE_EMBED`
  and `RMFE_PROJECT` as literals, the product property checked by the kernel, and its reading
  over `E`: the projection of a product of two embeddings is the AND of what they embed.
-/

/-!
# The embedding

`RMFE_EMBED` and `RMFE_PROJECT` (`crates/verifier/src/keccak.rs:22-46`, `rmfe`) are sixteen binary
polynomials `emb_a` of degree at most `23` (`rmfeEmbed`) and sixteen masks over the `47`
coefficients of a product (`rmfeProject`); the lemma of `doc/leanvm` §`keccak:rmfe-proof` is that
the parity of `mask_i ∧ (emb(u)·emb(v))` is `u_i ∧ v_i`. By bilinearity it is enough on unit
vectors:

* `rmfeOk_lit` (kernel, in `LvmKeccakRmfeLit` with the literals): for all `a, b, i < 16`, the
  parity of the masked coefficients of the carry-less product `emb_a · emb_b` is `[i = a = b]`; `rmfe_carryless` states it with the
  verifier's own `carryless` and `bitParity`;
* `embP a`, the embedding as a polynomial over `E` with `0/1` coefficients, and `projE`, the
  projection of a polynomial with `E` coefficients (the masked sum of its coefficients);
* `projE_embP_mul`: `projE_i (embP a · embP b) = [i = a = b]` in `E` (characteristic two:
  a coefficient of the product over `E` is the parity of the carry-less one);
* `projE_bilin`: for `E`-combinations, `projE_i ((Σ_a u_a emb_a)(Σ_b v_b emb_b)) = u_i v_i`;
* `keccakInstanceWeights_getD`: the verifier's instance weights at `s` are `emb_a(s)`;
* `projected_eq`: the verifier's projected value `Σ_c (Σ_{i : mask_i ∋ c} μ_i) · G_c` is
  `Σ_i μ_i · projE_i(G)`.
-/

namespace LeanVM.Protocol.KeccakGkr

open LeanVM.Parameters LeanVM.Protocol.Verifier LeanVM.Protocol.EndToEnd.Complete Finset Polynomial

section

/-! ## The kernel check (`LvmKeccakRmfeLit`), at the verifier's tables -/

theorem rmfeOk_at {a b i : ℕ} (ha : a < 16) (hb : b < 16) (hi : i < 16) :
    parityL (rmfeProject.getD i 0)
      (mulGF2 (bitsFrom (rmfeEmbed.getD a 0) 24) (bitsFrom (rmfeEmbed.getD b 0) 24)) =
        (i == a && a == b) := by
  rw [rmfeEmbed_eq, rmfeProject_eq]
  exact rmfeOk_lit_at ha hb hi

/-! ## Binary polynomials over `E` -/

/-- A binary polynomial, coefficient list lowest first, over `E`. -/
noncomputable def polyOfBits : List Bool → E[X]
  | [] => 0
  | b :: l => C (bitE b) + X * polyOfBits l

theorem coeff_polyOfBits : ∀ (l : List Bool) (c : ℕ),
    (polyOfBits l).coeff c = bitE (l.getD c false)
  | [], c => by simp [polyOfBits]
  | b :: l, 0 => by simp [polyOfBits]
  | b :: l, c + 1 => by simp [polyOfBits, coeff_polyOfBits l c]

theorem polyOfBits_xorL : ∀ A B : List Bool, polyOfBits (xorL A B) = polyOfBits A + polyOfBits B
  | [], l => by simp [xorL, polyOfBits]
  | x :: xs, [] => by simp [xorL, polyOfBits]
  | x :: xs, y :: ys => by
    simp only [xorL, polyOfBits, polyOfBits_xorL xs ys, bitE_xor, C_add]
    ring

theorem polyOfBits_mulGF2 : ∀ A B : List Bool,
    polyOfBits (mulGF2 A B) = polyOfBits A * polyOfBits B
  | [], B => by simp [mulGF2, polyOfBits]
  | a :: A, B => by
    rw [mulGF2, polyOfBits_xorL]
    cases a <;> simp [polyOfBits, polyOfBits_mulGF2 A B] <;> ring

/-! ## The embedding and the projection over `E` -/

/-- `emb_a`, the embedding of the unit vector `a`, a polynomial of degree at most `23`. -/
noncomputable def embP (a : ℕ) : E[X] := polyOfBits (bitsFrom (rmfeEmbed.getD a 0) 24)

theorem embP_coeff (a c : ℕ) :
    (embP a).coeff c = if c < 24 then bitE ((rmfeEmbed.getD a 0).testBit c) else 0 := by
  rw [embP, coeff_polyOfBits, bitsFrom_getD]
  by_cases h : c < 24 <;> simp [h]

theorem embP_natDegree (a : ℕ) : (embP a).natDegree ≤ 23 := by
  rw [natDegree_le_iff_coeff_eq_zero]
  intro c hc
  rw [embP_coeff, ite_eq_right (by exact_mod_cast (show ¬ c < 24 by omega))]

/-- The projection to bit `mask`: the sum of the masked coefficients among the first `47`. -/
noncomputable def projE (mask : ℕ) (P : E[X]) : E :=
  ∑ c ∈ range 47, if mask.testBit c then P.coeff c else 0

theorem projE_add (mask : ℕ) (P Q : E[X]) : projE mask (P + Q) = projE mask P + projE mask Q := by
  simp only [projE, coeff_add, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun c _ ↦ ?_
  split_ifs <;> simp

theorem projE_C_mul (mask : ℕ) (a : E) (P : E[X]) : projE mask (C a * P) = a * projE mask P := by
  simp only [projE, coeff_C_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl fun c _ ↦ ?_
  split_ifs <;> simp

theorem projE_sum {ι : Type} (mask : ℕ) (s : Finset ι) (P : ι → E[X]) :
    projE mask (∑ i ∈ s, P i) = ∑ i ∈ s, projE mask (P i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [projE]
  | insert a s ha ih => rw [Finset.sum_insert ha, projE_add, ih, Finset.sum_insert ha]

theorem sum_bitE_xor (f : ℕ → Bool) (n : ℕ) :
    ∑ c ∈ range n, bitE (f c) = bitE ((List.range n).foldl (fun acc c ↦ acc ^^ f c) false) := by
  induction n with
  | zero => simp
  | succ n ih => rw [Finset.sum_range_succ, ih, List.range_succ, List.foldl_concat, bitE_xor]

/-- **The embedding lemma over `E`**: the projection to bit `i` of `emb_a · emb_b` is
`[i = a = b]`. -/
theorem projE_embP_mul {i a b : ℕ} (hi : i < 16) (ha : a < 16) (hb : b < 16) :
    projE (rmfeProject.getD i 0) (embP a * embP b) = if i = a ∧ a = b then 1 else 0 := by
  rw [embP, embP, ← polyOfBits_mulGF2]
  unfold projE
  simp_rw [coeff_polyOfBits]
  have h : ∀ c, (if (rmfeProject.getD i 0).testBit c then
      bitE ((mulGF2 (bitsFrom (rmfeEmbed.getD a 0) 24) (bitsFrom (rmfeEmbed.getD b 0) 24)).getD
        c false) else 0) =
      bitE ((rmfeProject.getD i 0).testBit c &&
        (mulGF2 (bitsFrom (rmfeEmbed.getD a 0) 24) (bitsFrom (rmfeEmbed.getD b 0) 24)).getD
          c false) := by
    intro c
    cases (rmfeProject.getD i 0).testBit c <;> simp
  simp_rw [h]
  rw [sum_bitE_xor]
  have := rmfeOk_at ha hb hi
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

/-- **Bilinearity**: the projection to bit `i` of a product of two combinations of the
embeddings is the product of their `i`-th weights. -/
theorem projE_bilin {i : ℕ} (hi : i < 16) (u v : ℕ → E) :
    projE (rmfeProject.getD i 0)
      ((∑ a ∈ range 16, C (u a) * embP a) * (∑ b ∈ range 16, C (v b) * embP b)) = u i * v i := by
  rw [Finset.sum_mul_sum, projE_sum]
  have h : ∀ a ∈ range 16, projE (rmfeProject.getD i 0)
      (∑ b ∈ range 16, C (u a) * embP a * (C (v b) * embP b)) =
        if a = i then u i * v i else 0 := by
    intro a ha
    rw [projE_sum]
    have h2 : ∀ b ∈ range 16, projE (rmfeProject.getD i 0) (C (u a) * embP a * (C (v b) * embP b)) =
        u a * v b * (if i = a ∧ a = b then 1 else 0) := by
      intro b hb
      rw [show C (u a) * embP a * (C (v b) * embP b) = C (u a * v b) * (embP a * embP b) by
        rw [C_mul]; ring, projE_C_mul, projE_embP_mul hi (Finset.mem_range.1 ha)
          (Finset.mem_range.1 hb)]
    rw [Finset.sum_congr rfl h2]
    by_cases hai : a = i
    · subst hai
      rw [Finset.sum_eq_single a (fun b _ hb ↦ by simp [Ne.symm hb]) (fun h ↦ absurd ha h)]
      simp
    · rw [ite_eq_right hai]
      exact Finset.sum_eq_zero fun b _ ↦ by simp [Ne.symm hai]
  rw [Finset.sum_congr rfl h, Finset.sum_ite_eq' (range 16) i, ite_eq_left (Finset.mem_range.2 hi)]

/-! ## The verifier's sums -/

theorem sumE_filterMap_range (n : ℕ) (p : ℕ → Prop) [DecidablePred p] (f : ℕ → E) :
    sumE ((List.range n).filterMap fun b ↦ if p b then some (f b) else none) =
      ∑ b ∈ range n, if p b then f b else 0 := by
  rw [sumE_eq_sum]
  induction n with
  | zero => simp
  | succ n ih =>
    rw [List.range_succ, List.filterMap_append, List.sum_append, ih, Finset.sum_range_succ]
    by_cases h : p n <;> simp [h]

theorem powersFrom_getD (acc base : E) : ∀ (n b : ℕ), b < n →
    (powersFrom acc base n).getD b 0 = acc * base ^ b
  | n + 1, 0, _ => by simp [powersFrom]
  | n + 1, b + 1, h => by
    rw [powersFrom, List.getD_cons_succ, powersFrom_getD _ base n b (by omega), pow_succ]
    ring

theorem powers_getD (base : E) {n b : ℕ} (h : b < n) : (powers base n).getD b 0 = base ^ b := by
  rw [powers, powersFrom_getD 1 base n b h, one_mul]

theorem embP_eval (a : ℕ) (s : E) :
    (embP a).eval s = ∑ b ∈ range 24, if (rmfeEmbed.getD a 0).testBit b then s ^ b else 0 := by
  rw [eval_eq_sum_range' (n := 24) (by have := embP_natDegree a; omega)]
  refine Finset.sum_congr rfl fun b hb ↦ ?_
  rw [embP_coeff, ite_eq_left (Finset.mem_range.1 hb)]
  cases (rmfeEmbed.getD a 0).testBit b <;> simp

theorem keccakInstanceWeights_length (s : E) : (keccakInstanceWeights s).length = 16 := by
  simp [keccakInstanceWeights, rmfeEmbed_length]

/-- **The instance weights at `s`** are the embeddings' values there, `emb_a(s)`. -/
theorem keccakInstanceWeights_getD (s : E) {a : ℕ} (ha : a < 16) :
    (keccakInstanceWeights s).getD a 0 = (embP a).eval s := by
  have hl : a < rmfeEmbed.length := by rw [rmfeEmbed_length]; exact ha
  rw [embP_eval, keccakInstanceWeights, List.getD_eq_getElem?_getD, List.getElem?_map,
    List.getElem?_eq_getElem hl, List.getD_eq_getElem _ 0 hl]
  simp only [Option.map_some, Option.getD_some]
  rw [sumE_filterMap_range, show embedBits = 24 from rfl]
  refine Finset.sum_congr rfl fun b hb ↦ ?_
  rw [powers_getD s (Finset.mem_range.1 hb)]

theorem sumE_zip_filterMap (p : ℕ → Prop) [DecidablePred p] :
    ∀ (l₁ : List E) (l₂ : List ℕ), l₁.length = l₂.length →
      sumE ((List.zip l₁ l₂).filterMap fun x ↦ if p x.2 then some x.1 else none) =
        ∑ i ∈ range l₁.length, if p (l₂.getD i 0) then l₁.getD i 0 else 0
  | [], [], _ => by simp [sumE]
  | x :: l₁, y :: l₂, h => by
    rw [List.zip_cons_cons, List.length_cons, Finset.sum_range_succ']
    have ih := sumE_zip_filterMap p l₁ l₂ (by simpa using h)
    rw [sumE_eq_sum] at ih ⊢
    by_cases hp : p y
    · simp only [List.filterMap_cons, hp, ite_true, List.sum_cons, ih, List.getD_cons_succ,
        List.getD_cons_zero]
      ring
    · simp only [List.filterMap_cons, hp, ite_false, ih, List.getD_cons_succ, List.getD_cons_zero,
        add_zero]
  | [], _ :: _, h => by simp at h
  | _ :: _, [], h => by simp at h

/-- **The verifier's projected value** (`keccak.rs:125-132`): `Σ_c (Σ_{i ∋ c} μ_i) · G_c` is
`Σ_i μ_i · projE_i(G)`, for coefficients `G_c = product[c]`. -/
theorem projected_eq (mu product : List E) (hmu : mu.length = 16) (G : E[X])
    (hG : ∀ c < 47, product.getD c 0 = G.coeff c) :
    sumE ((List.range productBits).map fun c ↦
      sumE ((List.zip mu rmfeProject).filterMap fun (m, mask) ↦
        if mask.testBit c then some m else none) * product.getD c 0) =
      ∑ i ∈ range 16, mu.getD i 0 * projE (rmfeProject.getD i 0) G := by
  rw [sumE_eq_sum, list_sum_range]
  have h : ∀ c ∈ range productBits, sumE ((List.zip mu rmfeProject).filterMap fun (m, mask) ↦
      if mask.testBit c then some m else none) * product.getD c 0 =
        ∑ i ∈ range 16, mu.getD i 0 * (if (rmfeProject.getD i 0).testBit c then G.coeff c else 0) := by
    intro c hc
    have e : (fun (x : E × ℕ) ↦ match x with | (m, mask) => if mask.testBit c then some m else none) =
        fun x ↦ if x.2.testBit c then some x.1 else none := by
      funext x; rfl
    rw [e, sumE_zip_filterMap (fun mask ↦ mask.testBit c) mu rmfeProject
      (by rw [hmu, rmfeProject_length]), hmu, Finset.sum_mul, hG c (Finset.mem_range.1 hc)]
    refine Finset.sum_congr rfl fun i _ ↦ ?_
    split_ifs <;> simp
  rw [Finset.sum_congr rfl h, Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  rw [projE, Finset.mul_sum]
  rfl

end
end LeanVM.Protocol.KeccakGkr
end
-- ===== end of `LvmKeccakRmfe` =====

-- ===== merged from `LvmKeccakLayerAlg` (GOLF module merge: `LvmKeccakLayerAlg.lean` is now a stub importing `LvmKeccakLayerSum`) =====
section
-- Ported from leanVM `formal/lean_vm/LeanVM/Protocol/Keccak/LayerAlg.lean` (formal rev 40f877dc) as `LvmKeccakLayerAlg` for lvm (WP-2).
/-
  LeanVM.Protocol.Keccak.LayerAlg

  The algebra of a layer's first two steps: a claim on the states after a round, the honest
  product polynomial `G`, its projection (the round's χ and ι on the claim), and its value at
  the evaluation point.
-/

/-!
# A layer: the product polynomial

States are given by segment `m`, step `x` and position `j` (`States`). A claim
`(value, μ, point, w)` on states `st` (`ClaimTrue`, `doc/leanvm` eq. `keccak:eq:claim` with the
segment coordinate of §`keccak:segments`) is

  `value = Σ_{z < 2^(P+1)} eq(point, z) Σ_{i < 16} μ_i Σ_{j < 1600} w_j · st(m, x, j)`,

`z = y + 2^P·m` (pack `y`, segment `m`), step `x = i + 16y`. For a layer at `step`, the states
after the round are `roundB (layerRC step m)` of the states `T` before it (`afterRound`); with
`b = L(T)` the bits entering χ and `S_{z,j} = Σ_i b(z, i, j)·emb_i` the honest product polynomial
is (`Gpoly`, eq. `keccak:eq:product`)

  `G = Σ_z eq(point, z) Σ_j w_j (κ·S_{z,j} + (κ + S_{z,j+1})·S_{z,j+2})`,  `κ = Σ_i emb_i`.

* `claimSum_round`: the claim's sum on the states after the round is
  `Σ_i μ_i · projE_i(G) + (Σ_m eq(point_P, m)·ι_m(w)) · Σ_i μ_i` (eq. `keccak:eq:projection`);
* `iota_eq`: the verifier's `iota` is `Σ_m eq(point_P, m)·ι_m(w)`;
* `eval_Gpoly`: `G(s)` is the χ of the packs' states at `s` (eq. `keccak:eq:at-s`);
* `natDegree_Gpoly`: `G` has degree at most `46`.
-/

namespace LeanVM.Protocol.KeccakGkr

open LeanVM.Parameters LeanVM.Protocol.Verifier LeanVM.Protocol.EndToEnd.Complete Finset Polynomial

section

/-! ## Claims -/

/-- States by segment, step and position. -/
abbrev States : Type := ℕ → ℕ → ℕ → Bool

/-- The state of the index `z` (pack `z mod 2^P`, segment `z / 2^P`) and instance `i`. -/
def stAt (st : States) (P z i : ℕ) : ℕ → Bool := st (z / 2 ^ P) (i + 16 * (z % 2 ^ P))

/-- A claim's sum on the states `st`. -/
def claimSum (st : States) (P : ℕ) (point mu w : List E) : E :=
  ∑ z ∈ range (2 ^ (P + 1)), eqAt point z * ∑ i ∈ range 16, mu.getD i 0 *
    ∑ j ∈ range 1600, w.getD j 0 * bitE (stAt st P z i j)

/-- **A true claim** on the states `st`. -/
def ClaimTrue (st : States) (P : ℕ) (c : KeccakClaim) : Prop :=
  c.value = claimSum st P c.point c.mu c.weights

/-- A claim's sum reads the states at segments `0, 1` and positions below `1600` only. -/
theorem claimSum_congr {st st' : States} (P : ℕ)
    (h : ∀ m x j, m < 2 → j < 1600 → st m x j = st' m x j) (point mu w : List E) :
    claimSum st P point mu w = claimSum st' P point mu w := by
  unfold claimSum
  refine Finset.sum_congr rfl fun z hz ↦ ?_
  have hm : z / 2 ^ P < 2 := by
    rw [Nat.div_lt_iff_lt_mul (by positivity)]
    have := Finset.mem_range.1 hz
    rw [pow_succ] at this
    linarith
  refine congrArg (HMul.hMul _) (Finset.sum_congr rfl fun i _ ↦ congrArg (HMul.hMul _)
    (Finset.sum_congr rfl fun j hj ↦ ?_))
  rw [stAt, stAt, h _ _ _ hm (Finset.mem_range.1 hj)]

/-- The round constant of segment `m` at layer `step` (`crates/verifier/src/keccak.rs:137`): round
`12(m + 1) - step - 1`. -/
def layerRC (step m : ℕ) : UInt64 := keccakRC.getD (keccakDepth * (m + 1) - step - 1) 0

/-- The states after the layer's round. -/
def afterRound (T : States) (step : ℕ) : States := fun m x j ↦ roundB (layerRC step m) (T m x) j

/-! ## The product polynomial -/

/-- A pack's bits entering χ at position `j`, embedded: `Σ_i b(z, i, j)·emb_i`. -/
noncomputable def SP (T : States) (P z j : ℕ) : E[X] :=
  ∑ i ∈ range 16, C (bitE (Lb (stAt T P z i) j)) * embP i

/-- `κ = emb(1, …, 1)`. -/
noncomputable def kP : E[X] := ∑ i ∈ range 16, C 1 * embP i

/-- χ on the packs' embeddings at position `j`. -/
noncomputable def Gterm (T : States) (P z j : ℕ) : E[X] :=
  kP * SP T P z j + (kP + SP T P z (keccakAlong j 1)) * SP T P z (keccakAlong j 2)

/-- **The honest product polynomial**. -/
noncomputable def Gpoly (T : States) (P : ℕ) (point w : List E) : E[X] :=
  ∑ z ∈ range (2 ^ (P + 1)), C (eqAt point z) *
    ∑ j ∈ range 1600, C (w.getD j 0) * Gterm T P z j

theorem kP_add_SP (T : States) (P z j : ℕ) :
    kP + SP T P z j = ∑ i ∈ range 16, C (1 + bitE (Lb (stAt T P z i) j)) * embP i := by
  rw [kP, SP, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  rw [C_add]; ring

/-- The projection of χ on the embeddings is χ on bits. -/
theorem projE_Gterm (T : States) (P z j : ℕ) {i : ℕ} (hi : i < 16) :
    projE (rmfeProject.getD i 0) (Gterm T P z j) = bitE (chiB (Lb (stAt T P z i)) j) := by
  rw [Gterm, projE_add, kP_add_SP, kP, SP, SP, projE_bilin hi, projE_bilin hi, chiB, bitE_xor,
    bitE_and, bitE_not, one_mul]

theorem projE_Gpoly (T : States) (P : ℕ) (point w : List E) {i : ℕ} (hi : i < 16) :
    projE (rmfeProject.getD i 0) (Gpoly T P point w) =
      ∑ z ∈ range (2 ^ (P + 1)), eqAt point z *
        ∑ j ∈ range 1600, w.getD j 0 * bitE (chiB (Lb (stAt T P z i)) j) := by
  rw [Gpoly, projE_sum]
  refine Finset.sum_congr rfl fun z _ ↦ ?_
  rw [projE_C_mul, projE_sum]
  refine congrArg (HMul.hMul _) (Finset.sum_congr rfl fun j _ ↦ ?_)
  rw [projE_C_mul, projE_Gterm T P z j hi]

theorem natDegree_SP (T : States) (P z j : ℕ) : (SP T P z j).natDegree ≤ 23 :=
  natDegree_sum_le_of_forall_le _ _ fun i _ ↦
    (natDegree_C_mul_le _ _).trans (embP_natDegree i)

theorem natDegree_kP : kP.natDegree ≤ 23 :=
  natDegree_sum_le_of_forall_le _ _ fun i _ ↦
    (natDegree_C_mul_le _ _).trans (embP_natDegree i)

theorem natDegree_Gterm (T : States) (P z j : ℕ) : (Gterm T P z j).natDegree ≤ 46 := by
  unfold Gterm
  refine natDegree_add_le_of_degree_le ?_ ?_
  · exact natDegree_mul_le_of_le natDegree_kP (natDegree_SP T P z j)
  · exact natDegree_mul_le_of_le (natDegree_add_le_of_degree_le natDegree_kP (natDegree_SP _ _ _ _))
      (natDegree_SP T P z _)

theorem natDegree_Gpoly (T : States) (P : ℕ) (point w : List E) :
    (Gpoly T P point w).natDegree ≤ 46 :=
  natDegree_sum_le_of_forall_le _ _ fun z _ ↦ (natDegree_C_mul_le _ _).trans
    (natDegree_sum_le_of_forall_le _ _ fun j _ ↦ (natDegree_C_mul_le _ _).trans
      (natDegree_Gterm T P z j))

/-! ## The projection check -/

/-- ι's weight: `Σ_{z < 64, RC bit z} w_z`. -/
def iotaW (rc : UInt64) (w : List E) : E :=
  ∑ z ∈ range 64, if rc.toNat.testBit z then w.getD z 0 else 0

theorem sum_iotaB (rc : UInt64) (w : List E) :
    ∑ j ∈ range 1600, w.getD j 0 * bitE (iotaB rc j) = iotaW rc w := by
  rw [show 1600 = 64 + 1536 from rfl, Finset.sum_range_add]
  have h2 : ∑ x ∈ range 1536, w.getD (64 + x) 0 * bitE (iotaB rc (64 + x)) = 0 :=
    Finset.sum_eq_zero fun x _ ↦ by simp [iotaB]
  rw [h2, add_zero, iotaW]
  refine Finset.sum_congr rfl fun z hz ↦ ?_
  have hz' := Finset.mem_range.1 hz
  have e : rc.toNat.testBit z = rc.toBitVec.getLsbD z := rfl
  rw [iotaB, e]
  cases rc.toBitVec.getLsbD z <;> simp [hz']

/-- A sum over the (pack, segment) indices of a function of the segment. -/
theorem sum_segment {P : ℕ} {point : List E} (hpt : point.length = P + 1) (f : ℕ → E) :
    ∑ z ∈ range (2 ^ (P + 1)), eqAt point z * f (z / 2 ^ P) =
      ∑ m ∈ range 2, eqAt (point.drop P) m * f m := by
  have hsplit : point = point.take P ++ point.drop P := (List.take_append_drop P point).symm
  have htl : (point.take P).length = P := by simp [hpt]
  rw [pow_succ, mul_comm, sum_range_mul]
  refine Finset.sum_congr rfl fun m hm ↦ ?_
  have hm' := Finset.mem_range.1 hm
  have h1 : ∀ y ∈ range (2 ^ P), eqAt point (2 ^ P * m + y) * f ((2 ^ P * m + y) / 2 ^ P) =
      eqAt (point.take P) y * (eqAt (point.drop P) m * f m) := by
    intro y hy
    have hy' := Finset.mem_range.1 hy
    have hd : (2 ^ P * m + y) / 2 ^ P = m := by
      rw [Nat.add_comm, Nat.add_mul_div_left _ _ (by positivity), Nat.div_eq_of_lt hy', zero_add]
    conv_lhs => rw [hsplit]
    rw [eqAt_append, htl, hd, eqAt_mod (point.take P), htl,
      Nat.add_comm, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hy']
    ring
  have hs : ∑ y ∈ range (2 ^ P), eqAt (point.take P) y = 1 := by
    have := sum_eqAt (point.take P); rwa [htl] at this
  rw [Finset.sum_congr rfl h1, ← Finset.sum_mul, hs, one_mul]

/-- The claim's sum after the round: the projection of `G` and ι's known bits
(eq. `keccak:eq:projection`). -/
theorem claimSum_round (T : States) (step P : ℕ) (point mu w : List E)
    (hpt : point.length = P + 1) :
    claimSum (afterRound T step) P point mu w =
      ∑ i ∈ range 16, mu.getD i 0 * projE (rmfeProject.getD i 0) (Gpoly T P point w) +
        (∑ m ∈ range 2, eqAt (point.drop P) m * iotaW (layerRC step m) w) *
          ∑ i ∈ range 16, mu.getD i 0 := by
  have hb : ∀ z i j, bitE (stAt (afterRound T step) P z i j) =
      bitE (chiB (Lb (stAt T P z i)) j) + bitE (iotaB (layerRC step (z / 2 ^ P)) j) := by
    intro z i j
    rw [stAt, afterRound, roundB, bitE_xor]
    rfl
  have e1 : claimSum (afterRound T step) P point mu w =
      ∑ z ∈ range (2 ^ (P + 1)), eqAt point z * ∑ i ∈ range 16, mu.getD i 0 *
        ∑ j ∈ range 1600, w.getD j 0 * bitE (chiB (Lb (stAt T P z i)) j) +
      ∑ z ∈ range (2 ^ (P + 1)), eqAt point z * (∑ i ∈ range 16, mu.getD i 0) *
        iotaW (layerRC step (z / 2 ^ P)) w := by
    rw [claimSum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun z _ ↦ ?_
    have : ∑ i ∈ range 16, mu.getD i 0 * ∑ j ∈ range 1600, w.getD j 0 *
          bitE (stAt (afterRound T step) P z i j) =
        ∑ i ∈ range 16, mu.getD i 0 * ∑ j ∈ range 1600, w.getD j 0 *
          bitE (chiB (Lb (stAt T P z i)) j) +
        (∑ i ∈ range 16, mu.getD i 0) * iotaW (layerRC step (z / 2 ^ P)) w := by
      rw [Finset.sum_mul, ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun i _ ↦ ?_
      simp only [hb, mul_add, Finset.sum_add_distrib, sum_iotaB]
    rw [this]
    ring
  have p1 : ∑ i ∈ range 16, mu.getD i 0 * projE (rmfeProject.getD i 0) (Gpoly T P point w) =
      ∑ z ∈ range (2 ^ (P + 1)), eqAt point z * ∑ i ∈ range 16, mu.getD i 0 *
        ∑ j ∈ range 1600, w.getD j 0 * bitE (chiB (Lb (stAt T P z i)) j) := by
    have h : ∀ i ∈ range 16, mu.getD i 0 * projE (rmfeProject.getD i 0) (Gpoly T P point w) =
        mu.getD i 0 * ∑ z ∈ range (2 ^ (P + 1)), eqAt point z *
          ∑ j ∈ range 1600, w.getD j 0 * bitE (chiB (Lb (stAt T P z i)) j) :=
      fun i hi ↦ by rw [projE_Gpoly T P point w (Finset.mem_range.1 hi)]
    rw [Finset.sum_congr rfl h]
    simp_rw [Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun z _ ↦ Finset.sum_congr rfl fun i _ ↦
      Finset.sum_congr rfl fun j _ ↦ by ring
  have p2 : ∑ z ∈ range (2 ^ (P + 1)), eqAt point z * (∑ i ∈ range 16, mu.getD i 0) *
        iotaW (layerRC step (z / 2 ^ P)) w =
      (∑ m ∈ range 2, eqAt (point.drop P) m * iotaW (layerRC step m) w) *
        ∑ i ∈ range 16, mu.getD i 0 := by
    rw [← sum_segment hpt (fun m ↦ iotaW (layerRC step m) w), Finset.sum_mul]
    exact Finset.sum_congr rfl fun z _ ↦ by ring
  rw [e1, p1, p2]

/-- **The verifier's `iota`** (`keccak.rs:133-139`). -/
theorem iota_eq (step P : ℕ) (point w : List E) (hpt : point.length = P + 1) :
    sumE ((List.range keccakSegments).map fun segment ↦
      (eqKernel (point.drop P)).getD segment 0 *
        sumE ((List.range 64).filterMap fun z ↦
          if (keccakRC.getD (keccakDepth * (segment + 1) - step - 1) 0).toNat.testBit z then
            some (w.getD z 0) else none)) =
      ∑ m ∈ range 2, eqAt (point.drop P) m * iotaW (layerRC step m) w := by
  have hl : (point.drop P).length = 1 := by simp [hpt]
  rw [sumE_eq_sum, list_sum_range, show keccakSegments = 2 from rfl]
  refine Finset.sum_congr rfl fun m hm ↦ ?_
  rw [eqKernel_getD, hl, ite_eq_left (by simpa using hm), sumE_filterMap_range]
  rfl

/-! ## The value at the evaluation point -/

/-- A pack's state entering χ at `s`: `Σ_i emb_i(s)·b(z, i, j)`. -/
noncomputable def Shat0 (T : States) (P : ℕ) (s : E) (z j : ℕ) : E :=
  ∑ i ∈ range 16, (embP i).eval s * bitE (Lb (stAt T P z i) j)

/-- `κ(s) = Σ_i emb_i(s)`. -/
noncomputable def kappaAt (s : E) : E := ∑ i ∈ range 16, (embP i).eval s

/-- `eval_Gpoly` for any number `n` of bit positions (proved over a variable `n`: with the
literal `1600` the kernel took 25 s to check the same proof). -/
theorem eval_Gpoly_aux (T : States) (P : ℕ) (point w : List E) (s : E) (n : ℕ) :
    (∑ z ∈ range (2 ^ (P + 1)), C (eqAt point z) *
      ∑ j ∈ range n, C (w.getD j 0) * Gterm T P z j).eval s =
      ∑ z ∈ range (2 ^ (P + 1)), eqAt point z * ∑ j ∈ range n, w.getD j 0 *
        (kappaAt s * Shat0 T P s z j + (kappaAt s + Shat0 T P s z (keccakAlong j 1)) *
          Shat0 T P s z (keccakAlong j 2)) := by
  have hS : ∀ z j, (SP T P z j).eval s = Shat0 T P s z j := fun z j ↦ by
    simp only [SP, Shat0, eval_finsetSum, eval_mul, eval_C]
    exact Finset.sum_congr rfl fun i _ ↦ mul_comm _ _
  have hk : kP.eval s = kappaAt s := by
    simp only [kP, kappaAt, eval_finsetSum, eval_mul, eval_C, one_mul]
  simp only [Gterm, eval_finsetSum, eval_mul, eval_C, eval_add, hS, hk]

/-- **`G(s)`** is χ of the packs' states at `s` (eq. `keccak:eq:at-s`). -/
theorem eval_Gpoly (T : States) (P : ℕ) (point w : List E) (s : E) :
    (Gpoly T P point w).eval s =
      ∑ z ∈ range (2 ^ (P + 1)), eqAt point z * ∑ j ∈ range 1600, w.getD j 0 *
        (kappaAt s * Shat0 T P s z j + (kappaAt s + Shat0 T P s z (keccakAlong j 1)) *
          Shat0 T P s z (keccakAlong j 2)) :=
  eval_Gpoly_aux T P point w s 1600

/-- The coefficients of `G`, as the honest prover sends them. -/
@[irreducible] noncomputable def gList (G : E[X]) : List E := (List.range 47).map G.coeff

theorem gList_length (G : E[X]) : (gList G).length = 47 := by simp [gList]

theorem gList_getD (G : E[X]) {c : ℕ} (hc : c < 47) : (gList G).getD c 0 = G.coeff c := by
  simp [gList, List.getD_eq_getElem?_getD, hc]

theorem polyEval_gList {G : E[X]} (hG : G.natDegree ≤ 46) (s : E) :
    polyEval (gList G) s = G.eval s := by
  rw [polyEval_eq_sum, gList_length, eval_eq_sum_range' (n := 47) (by omega)]
  exact Finset.sum_congr rfl fun c hc ↦ by rw [gList_getD G (Finset.mem_range.1 hc)]

end
end LeanVM.Protocol.KeccakGkr
end
-- ===== end of `LvmKeccakLayerAlg` =====

/-!
# A layer: the sumchecks and the next claim

After the evaluation point `s`, the packs' states at `s`, `Ŝ_j(z) = Σ_i emb_i(s)·b(z, i, j)`
(`Shat0`), are extended multilinearly in the (pack, segment) point (`Shat`), and

  `g(c) = Σ_j w_j (κ·Ŝ_j(c) + (κ + Ŝ_{j+1}(c))·Ŝ_{j+2}(c))`   (`gt`)

is the summand of the pack rounds (eq. `keccak:eq:after-packs`):

* `FP r acc = Σ_{z} eq(r_{≥|acc|}, z) · g(acc ++ z)` is an equality-mode family of degree two
  at `r` (`FP_eqFamily`), equal to `G(s)` before any challenge (`FP_nil`) and to `g(c)` after all
  (`FP_full`);
* with `c` bound, `FX acc = scale · Σ_u φ(acc ++ u)`,
  `φ(p) = W(p)·(κ·T_0(p) + (κ + T_1(p))·T_2(p))`, `W` and `T_k(p) = Σ_j eq(p, j)·Ŝ_{j+k}(c)` the
  multilinear extensions over the `11` position bits, is a plain family of degree three
  (`FX_plainFamily`), equal to `scale · g(c)` before any challenge (`FX_nil`); `dot_weights`: the
  verifier's `dot(eq[:1600], w)` is `W` (eq. `keccak:eq:terminal`);
* `batch_eq`: `T_0 + β(T_1 + βT_2)` at the position point is the claim's sum on the states before
  the round, with weights `keccakLinearTranspose` of the verifier's batched weights and instance
  weights `emb_i(s)` (eq. `keccak:eq:flat` and step 6).
-/

namespace LeanVM.Protocol.KeccakGkr

open LeanVM.Parameters LeanVM.Protocol.Verifier LeanVM.Protocol.EndToEnd.Complete Finset Polynomial

section

variable (T : States) (P : ℕ) (s : E) (w : List E)

/-! ## The pack and segment rounds -/

/-- The packs' states at `s`, extended multilinearly in the (pack, segment) point. -/
noncomputable def Shat (j : ℕ) (c : List E) : E :=
  ∑ z ∈ range (2 ^ (P + 1)), eqAt c z * Shat0 T P s z j

/-- χ of the packs' states at the point `c`. -/
noncomputable def gt (c : List E) : E :=
  ∑ j ∈ range 1600, w.getD j 0 * (kappaAt s * Shat T P s j c +
    (kappaAt s + Shat T P s (keccakAlong j 1) c) * Shat T P s (keccakAlong j 2) c)

/-- The pack and segment rounds' family at the claim's point `r`. -/
noncomputable def FP (r acc : List E) : E :=
  ∑ z ∈ range (2 ^ (P + 1 - acc.length)), eqAt (r.drop acc.length) z *
    gt T P s w (acc ++ bitsE z (P + 1 - acc.length))

theorem Shat_bitsE (j : ℕ) {z : ℕ} (hz : z < 2 ^ (P + 1)) :
    Shat T P s j (bitsE z (P + 1)) = Shat0 T P s z j :=
  sum_eqAt_bitsE hz _

/-- Before any challenge, the family is `G(s)`. -/
theorem FP_nil (r : List E) : FP T P s w r [] = (Gpoly T P r w).eval s := by
  rw [eval_Gpoly, FP]
  refine Finset.sum_congr rfl fun z hz ↦ ?_
  simp only [List.length_nil, Nat.sub_zero, List.drop_zero, List.nil_append, gt]
  have hz' := Finset.mem_range.1 hz
  simp only [Shat_bitsE T P s _ hz']

/-- After all the challenges, the family is `g(c)`. -/
theorem FP_full (r acc : List E) (hr : r.length = P + 1) (h : acc.length = P + 1) :
    FP T P s w r acc = gt T P s w acc := by
  rw [FP, h, Nat.sub_self, List.drop_eq_nil_of_le (by (clear * - hr; omega))]
  simp [bitsE]

theorem polyLE_Shat (pre post : List E) (j : ℕ) :
    PolyLE 1 fun x ↦ Shat T P s j (pre ++ x :: post) :=
  polyLE_mle pre post _ _

theorem polyLE_gt (pre post : List E) : PolyLE 2 fun x ↦ gt T P s w (pre ++ x :: post) := by
  refine PolyLE.sum _ fun j _ ↦ PolyLE.const_mul ?_ _
  refine PolyLE.add ((PolyLE.const_mul (polyLE_Shat T P s pre post j) _).mono (by norm_num)) ?_
  exact (PolyLE.mul ((PolyLE.add (PolyLE.const 1 _) (polyLE_Shat T P s pre post _)))
    (polyLE_Shat T P s pre post _))

/-- **The pack and segment rounds' family**: degree two, split by the equality weights. -/
theorem FP_eqFamily {β : Type} (Tq : β → States) (r : List E) (hr : r.length = P + 1) :
    EqFamily (fun q acc ↦ FP (Tq q) P s w r acc) r 2 := by
  intro q acc hacc
  have hm : P + 1 - acc.length = (P + 1 - (acc.length + 1)) + 1 := by omega
  have hdrop : r.drop acc.length = r[acc.length] :: r.drop (acc.length + 1) :=
    List.drop_eq_getElem_cons hacc
  refine ⟨?_, ?_⟩
  · have e : ∀ x, FP (Tq q) P s w r (acc ++ [x]) =
        ∑ z ∈ range (2 ^ (P + 1 - (acc.length + 1))), eqAt (r.drop (acc.length + 1)) z *
          gt (Tq q) P s w (acc ++ x :: bitsE z (P + 1 - (acc.length + 1))) := by
      intro x
      simp only [FP, List.length_append, List.length_singleton, List.append_assoc,
        List.singleton_append]
    refine PolyLE.congr (f := fun x ↦ ∑ z ∈ range (2 ^ (P + 1 - (acc.length + 1))),
      eqAt (r.drop (acc.length + 1)) z *
        gt (Tq q) P s w (acc ++ x :: bitsE z (P + 1 - (acc.length + 1)))) ?_ fun x ↦ (e x).symm
    exact PolyLE.sum _ fun z _ ↦ PolyLE.const_mul (polyLE_gt (Tq q) P s w acc _) _
  · simp only [FP, List.length_append, List.length_singleton]
    rw [hm, sum_cube_succ, hdrop, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun z _ ↦ ?_
    rw [eqAt_cons, eqAt_cons, bitsE_two_mul, bitsE_two_mul_add_one]
    have h1 : 2 * z % 2 = 0 := by (clear * -; omega)
    have h2 : (2 * z + 1) % 2 = 1 := by (clear * - h1; omega)
    have h3 : 2 * z / 2 = z := by (clear * - h1; omega)
    have h4 : (2 * z + 1) / 2 = z := by (clear * - h1 h2; omega)
    simp only [h1, h2, h3, h4, ite_true, zero_ne_one, ite_false, List.append_assoc,
      List.singleton_append]
    ring

/-! ## The position rounds -/

/-- The packs' state at `c`, `k` columns along, extended over the position bits. -/
noncomputable def Tk (c : List E) (k : ℕ) (p : List E) : E :=
  ∑ j ∈ range 1600, eqAt p j * Shat T P s (keccakAlong j k) c

/-- The position weights, extended over the position bits. -/
noncomputable def Wt (p : List E) : E := ∑ j ∈ range 1600, eqAt p j * w.getD j 0

/-- The position rounds' summand. -/
noncomputable def phi (c p : List E) : E :=
  Wt w p * (kappaAt s * Tk T P s c 0 p + (kappaAt s + Tk T P s c 1 p) * Tk T P s c 2 p)

/-- The position rounds' family. -/
noncomputable def FX (c : List E) (scale : E) (acc : List E) : E :=
  scale * ∑ u ∈ range (2 ^ (11 - acc.length)), phi T P s w c (acc ++ bitsE u (11 - acc.length))

theorem sum1600_bitsE {u : ℕ} (hu : u < 2 ^ 11) (f : ℕ → E) :
    ∑ j ∈ range 1600, eqAt (bitsE u 11) j * f j = if u < 1600 then f u else 0 := by
  have h : ∀ j ∈ range 1600, eqAt (bitsE u 11) j * f j = if u = j then f j else 0 := by
    intro j hj
    rw [eqAt_bitsE_lt hu (by have := Finset.mem_range.1 hj; (clear * - this; omega))]
    by_cases h : j = u
    · subst h; simp
    · simp [h, Ne.symm h]
  rw [Finset.sum_congr rfl h, Finset.sum_ite_eq]
  simp

/-- Before any position challenge, the family is `scale · g(c)`. -/
theorem FX_nil (c : List E) (scale : E) : FX T P s w c scale [] = scale * gt T P s w c := by
  unfold FX
  refine congrArg (HMul.hMul _) ?_
  simp only [List.length_nil, Nat.sub_zero, List.nil_append]
  rw [show 2 ^ 11 = 1600 + 448 from rfl, Finset.sum_range_add]
  have hrest : ∑ x ∈ range 448, phi T P s w c (bitsE (1600 + x) 11) = 0 := by
    refine Finset.sum_eq_zero fun x hx ↦ ?_
    have hx' := Finset.mem_range.1 hx
    rw [phi, Wt, sum1600_bitsE (by (clear * - hx'; omega)), ite_eq_right (by (clear * - hx'; omega)), zero_mul]
  rw [hrest, add_zero, gt]
  refine Finset.sum_congr rfl fun u hu ↦ ?_
  have hu' := Finset.mem_range.1 hu
  rw [phi, Wt, Tk, Tk, Tk, sum1600_bitsE (by (clear * - hu'; omega)), sum1600_bitsE (by (clear * - hu'; omega)),
    sum1600_bitsE (by (clear * - hu'; omega)), sum1600_bitsE (by (clear * - hu'; omega)), ite_eq_left hu', ite_eq_left hu',
    ite_eq_left hu', ite_eq_left hu', keccakAlong_zero hu']

theorem FX_full (c : List E) (scale : E) (acc : List E) (h : acc.length = 11) :
    FX T P s w c scale acc = scale * phi T P s w c acc := by
  rw [FX, h, Nat.sub_self]
  simp [bitsE]

theorem polyLE_phi (c pre post : List E) : PolyLE 3 fun x ↦ phi T P s w c (pre ++ x :: post) := by
  unfold phi Wt Tk
  refine PolyLE.mul (d := 1) (d' := 2) (polyLE_mle pre post _ _) ?_
  refine PolyLE.add ((PolyLE.const_mul (polyLE_mle pre post _ _) _).mono (by norm_num)) ?_
  exact PolyLE.mul (PolyLE.add (PolyLE.const 1 _) (polyLE_mle pre post _ _))
    (polyLE_mle pre post _ _)

/-- **The position rounds' family**: degree three, plain. -/
theorem FX_plainFamily {β : Type} (Tq : β → States) (c : List E) (scale : E) :
    PlainFamily (fun q acc ↦ FX (Tq q) P s w c scale acc) 3 11 := by
  intro q acc hacc
  have hm : 11 - acc.length = (11 - (acc.length + 1)) + 1 := by omega
  refine ⟨?_, ?_⟩
  · have e : ∀ x, FX (Tq q) P s w c scale (acc ++ [x]) =
        scale * ∑ u ∈ range (2 ^ (11 - (acc.length + 1))),
          phi (Tq q) P s w c (acc ++ x :: bitsE u (11 - (acc.length + 1))) := by
      intro x
      simp only [FX, List.length_append, List.length_singleton, List.append_assoc,
        List.singleton_append]
    refine PolyLE.congr (f := fun x ↦ scale * ∑ u ∈ range (2 ^ (11 - (acc.length + 1))),
      phi (Tq q) P s w c (acc ++ x :: bitsE u (11 - (acc.length + 1)))) ?_ fun x ↦ (e x).symm
    exact PolyLE.const_mul (PolyLE.sum _ fun u _ ↦ polyLE_phi (Tq q) P s w c acc _) scale
  · simp only [FX, List.length_append, List.length_singleton]
    rw [hm, sum_cube_succ, ← mul_add, ← Finset.sum_add_distrib]
    refine congrArg (HMul.hMul _) (Finset.sum_congr rfl fun u _ ↦ ?_)
    rw [bitsE_two_mul, bitsE_two_mul_add_one]
    simp only [List.append_assoc, List.singleton_append]

/-- **The final check's weight**: the verifier's `dot(eq[:1600], w)` is `W`. -/
theorem dot_weights (p : List E) (hp : p.length = 11) (hw : w.length = 1600) :
    dot ((eqKernel p).take keccakBits) w = Wt w p := by
  rw [show keccakBits = w.length from hw.symm, dot_eqKernel p w (by rw [hp, hw]; norm_num), hw]
  rfl

/-! ## The batched claim -/

theorem list_sum_getD (l : List E) : l.sum = ∑ i ∈ range l.length, l.getD i 0 := by
  induction l with
  | nil => simp
  | cons x l ih => rw [List.sum_cons, ih, List.length_cons, Finset.sum_range_succ']; simp [add_comm]

theorem kappa_eq (s : E) : sumE (keccakInstanceWeights s) = kappaAt s := by
  rw [sumE_eq_sum, list_sum_getD, keccakInstanceWeights_length, kappaAt]
  exact Finset.sum_congr rfl fun i hi ↦ keccakInstanceWeights_getD s (Finset.mem_range.1 hi)

/-- `T_k` with the shift moved onto the weights. -/
theorem Tk_shift (c p : List E) {k k' : ℕ} (hk : k + k' = 5) :
    Tk T P s c k p = ∑ j ∈ range 1600, eqAt p (keccakAlong j k') * Shat T P s j c := by
  unfold Tk
  calc ∑ j ∈ range 1600, eqAt p j * Shat T P s (keccakAlong j k) c
      = ∑ j ∈ range 1600, eqAt p (keccakAlong (keccakAlong j k) k') *
          Shat T P s (keccakAlong j k) c :=
        Finset.sum_congr rfl fun j _ ↦ by rw [keccakAlong_along hk]
    _ = _ := sum_perm 1600 (fun j ↦ keccakAlong j k) (fun j ↦ keccakAlong j k')
        (fun j hj ↦ keccakAlong_lt k hj) (fun j hj ↦ keccakAlong_lt k' hj)
        (fun j _ ↦ keccakAlong_along (by omega)) (fun j _ ↦ keccakAlong_along hk)
        (fun j ↦ eqAt p (keccakAlong j k') * Shat T P s j c)

/-- The verifier's batched weights (`crates/verifier/src/keccak.rs:184-189`). -/
def batchW (p : List E) (beta : E) : List E :=
  (List.range keccakBits).map fun j ↦ (eqKernel p).getD j 0 +
    beta * ((eqKernel p).getD (keccakAlong j 4) 0 + beta * (eqKernel p).getD (keccakAlong j 3) 0)

theorem batchW_getD (p : List E) (hp : p.length = 11) (beta : E) {j : ℕ} (hj : j < 1600) :
    (batchW p beta).getD j 0 =
      eqAt p j + beta * (eqAt p (keccakAlong j 4) + beta * eqAt p (keccakAlong j 3)) := by
  have hA : ∀ k, (eqKernel p).getD (keccakAlong j k) 0 = eqAt p (keccakAlong j k) :=
    fun k ↦ by rw [eqKernel_getD, hp, ite_eq_left (by have := keccakAlong_lt k hj; (clear * - this; omega))]
  rw [batchW, List.getD_eq_getElem?_getD, List.getElem?_map,
    List.getElem?_range (by simpa [keccakBits] using hj)]
  simp only [Option.map_some, Option.getD_some]
  rw [hA 4, hA 3, eqKernel_getD, hp, ite_eq_left (by (clear * - hj; omega))]

/-- **The batched claim** (eqs. `keccak:eq:flat` and step 6): `T_0 + β(T_1 + βT_2)` at the
position point is the claim's sum on the states before the round, at the pack point `c`, with
instance weights `emb_i(s)` and position weights `Lᵀ` of the batched weights. -/
theorem batch_eq (c p : List E) (hp : p.length = 11) (beta : E) :
    Tk T P s c 0 p + beta * (Tk T P s c 1 p + beta * Tk T P s c 2 p) =
      claimSum T P c (keccakInstanceWeights s) (keccakLinearTranspose (batchW p beta)) := by
  have h0 : Tk T P s c 0 p = ∑ j ∈ range 1600, eqAt p j * Shat T P s j c :=
    Finset.sum_congr rfl fun j hj ↦ by rw [keccakAlong_zero (Finset.mem_range.1 hj)]
  have hcomb : Tk T P s c 0 p + beta * (Tk T P s c 1 p + beta * Tk T P s c 2 p) =
      ∑ j ∈ range 1600, (batchW p beta).getD j 0 * Shat T P s j c := by
    rw [h0, Tk_shift T P s c p (show 1 + 4 = 5 from rfl),
      Tk_shift T P s c p (show 2 + 3 = 5 from rfl)]
    simp only [Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun j hj ↦ ?_
    rw [batchW_getD p hp beta (Finset.mem_range.1 hj)]
    ring
  have step1 : ∑ j ∈ range 1600, (batchW p beta).getD j 0 * Shat T P s j c =
      ∑ z ∈ range (2 ^ (P + 1)), eqAt c z * ∑ i ∈ range 16, (embP i).eval s *
        ∑ j ∈ range 1600, (batchW p beta).getD j 0 * bitE (Lb (stAt T P z i) j) := by
    simp only [Shat, Shat0, Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun z _ ↦ ?_
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun i _ ↦ Finset.sum_congr rfl fun j _ ↦ by ring
  rw [hcomb, step1, claimSum]
  refine Finset.sum_congr rfl fun z _ ↦ congrArg (HMul.hMul _)
    (Finset.sum_congr rfl fun i hi ↦ ?_)
  rw [transpose_bits, keccakInstanceWeights_getD s (Finset.mem_range.1 hi)]

end
end LeanVM.Protocol.KeccakGkr
