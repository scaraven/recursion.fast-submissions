-- Ported from v3 `spartan-chain` (submissions repo, local `main` at `1f59b38`) to the v4 contract.
/-
# The submission and its certificate (BLUEPRINT §3–§5; v3 BLUEPRINT-R1 §1.4, §10)

The assembly of the entry, parametrised by the parts other modules supply, so that the final
instantiation is one line once they exist (v3's structure, v4's contract):

* `LV : LeafVerifier`, the leaf size, the SNARK verifier and its query bound (`Verifier.lean`);
* `proveLeaf s n h : OProg ByteArray`, the SNARK prover for `n ≥ 1` (`Prover.lean`);
* `Facts LV proveLeaf`, the facts proved elsewhere:
  * `size_zero`: `leafSize 0 = 80`;
  * `leaf_complete`: for every oracle, the honest SNARK has the right size and is accepted;
  * `ks`: for every public key, a knowledge state with error `2^-129` for the relation of
    `accV LV vk` (`SoundnessKState`);
  * `atMost`, `qb_le`: the SNARK verifier asks at most `qb n ≤ 2^16` queries along every path of
    answers on every chain of at most `chainCap` steps (v3's L-Q1, along paths:
    `SpartanSromSnarkQueries`).

What this module proves, for every such instantiation:
* `acc_eq`: the submission's `acc` is `accV LV` (`SpartanSromNode`);
* `complete`: perfect completeness for every public key (leaves as v3; nodes by `N`, with no
  query), so completeness with error `δ = 0` (`complete_withError_zero`);
* `V_queries`: at most `2^16` queries on every input and oracle;
* `certificateOf`: the contract's `Certificate` (`KS` and completeness for every key; `E`, `ext`,
  `fuel` and `computes` the library's witness-sending copy extractor);
* `certificateR_of`: `CertificateR` against any rendered claim within the declared numbers.

The honest prover (§3): a leaf is its 80-byte header (`enc64 0 ‖ s ‖ enc64 n ‖ h`,
`h = chainEnd s n` recomputed) followed by the SNARK, which is absent when `n = 0` (v3's); a node
is its plain encoding `N` (`encode w`), no query (D-5: only the native prover emits bundles).

**Changed from v3.** `P` takes the public key; the node proof is the library's `encode` of a
node with signed children (v3: `encodeNodeB` of two plain proofs); `qV = 2^16` (v3: `2^14`; the
bundle branch's static bound); `δ = 0` and completeness for every key; v3's `img`/`imageCap`
(the RISC-V extractor image) is the v4 machine program `ext` of the library.
-/
import SpartanSromNode
import RecursionFast.Library.Completeness

open scoped NNReal

namespace SpartanSrom
open RecursionFast
open RecursionFast.WitnessSending (encode decode decode_encode size_encode size_eq_length encodeF
  encodeF_eq)

/-! ## The honest prover (§3) -/

/-- The bytes of a leaf proof: the header `encode (.leaf s n) ‖ h` (80 bytes), then the SNARK. -/
def leafBytes (s : Digest) (n : ℕ) (h : Digest) (πS : ByteArray) : Proof :=
  encodeF (.leaf s n) ++ ⟨h.toArray⟩ ++ πS

/-- **The honest prover** (any key, any statement). A leaf: the header with `h = chainEnd s n`,
and `proveLeaf`'s SNARK when `n ≥ 1`. A node: its plain encoding `N`. -/
def P (proveLeaf : Digest → ℕ → Digest → OProg ByteArray) (_ _ : Digest) : Wit → OProg Proof
  | .leaf s n =>
    if n = 0 then .ret (leafBytes s 0 s ByteArray.empty)
    else proveLeaf s n (chainEnd s n) >>= fun πS => .ret (leafBytes s n (chainEnd s n) πS)
  | w@(.node ..) => .ret (encodeF w)


/-! ## Parsing the honest leaf proof -/

private theorem toList_append (a b : ByteArray) :
    (a ++ b).data.toList = a.data.toList ++ b.data.toList := by
  simp [ByteArray.data_append]

theorem leafBytes_toList (s : Digest) (n : ℕ) (h : Digest) (πS : ByteArray) :
    (leafBytes s n h πS).data.toList =
      (encode (.leaf s n)).data.toList ++ h.toList ++ πS.data.toList := by
  rw [leafBytes, toList_append, toList_append, encodeF_eq]; rfl

theorem leafBytes_size (s : Digest) (n : ℕ) (h : Digest) (πS : ByteArray) :
    (leafBytes s n h πS).size = 80 + πS.size := by
  rw [size_eq_length, leafBytes_toList, List.length_append, List.length_append,
    ← size_eq_length, ← size_eq_length, WitnessSending.size_encode_leaf]
  simp

/-- The honest leaf proof parses back to its parts. -/
theorem leafBytes_parse (s : Digest) {n : ℕ} (hn : n < 2 ^ 64) (h : Digest) (πS : ByteArray) :
    tagWord (leafBytes s n h πS) = 0 ∧ leafN (leafBytes s n h πS) = n ∧
      leafS (leafBytes s n h πS) = s ∧ leafH (leafBytes s n h πS) = h ∧
      leafSnark (leafBytes s n h πS) = πS := by
  set π := leafBytes s n h πS
  set e := encode (.leaf s n)
  have he : e.data.toList.length = 48 := by
    rw [← size_eq_length]; exact WitnessSending.size_encode_leaf s n
  have h48 : π.data.toList.take 48 = e.data.toList.take 48 := by
    rw [leafBytes_toList, List.append_assoc, List.take_append_of_le_length (le_of_eq he.symm)]
  have hte : tagWord e = 0 := by
    rw [tagWord_eq, take8_encode, ofLE_wordBytes]; rfl
  have hde := decode_leaf (show 48 ≤ e.size by rw [WitnessSending.size_encode_leaf]) hte
  rw [decode_encode _ (show (Wit.leaf s n).Fits from hn)] at hde
  obtain ⟨hsE, hnE⟩ : s = leafS e ∧ n = leafN e := by
    injection hde with hw; injection hw with h1 h2; exact ⟨h1, h2⟩
  obtain ⟨ht, hN, hS⟩ := parse48_congr h48
  refine ⟨ht.trans hte, hN.trans hnE.symm, hS.trans hsE.symm, ?_, ?_⟩
  · ext i hi
    have he' : (encode (Wit.leaf s n)).data.toList.length = 48 := he
    simp only [leafH, digestFrom, Vector.getElem_ofFn, byteAt_eq, proof_getD_eq, π,
      leafBytes_toList]
    rw [List.append_assoc, List.getD_append_right _ _ _ _ (by omega), he',
      List.getD_append _ _ _ _ (by simp; omega)]
    simp [List.getD_eq_getElem?_getD, hi]
  · have h80 : (encodeF (.leaf s n) ++ (⟨h.toArray⟩ : ByteArray)).size = 80 := by
      have := leafBytes_size s n h ByteArray.empty
      rwa [leafBytes, ByteArray.append_empty, ByteArray.size_empty] at this
    rw [leafSnark, show π.size = 80 + πS.size from leafBytes_size s n h πS]
    exact ByteArray.extract_append_eq_right h80.symm (by rw [h80])

/-! ## The submission -/

/-- The proved knowledge error, `2^-129` (v3 §5.5, §9.4), as the cast of a non-negative rational
so that the submission is computable (the harness's badge compiles `S.accF` of the whole
structure; `(2 : ℝ≥0)⁻¹ ^ 129`, v3's form, has no compiled code). -/
def εR1 : ℝ≥0 := ((1 / 2 ^ 129 : ℚ≥0) : ℝ≥0)

theorem εR1_eq : εR1 = (2 : ℝ≥0)⁻¹ ^ 129 := by
  unfold εR1; push_cast; rw [one_div, inv_pow]

/-- The verifier query bound, `2^16` (the bundle branch's static bound; v3: `2^14`). -/
def qVR1 : ℕ := 2 ^ 16

variable (LV : LeafVerifier) (proveLeaf : Digest → ℕ → Digest → OProg ByteArray)

/-- **The submission** for a leaf verifier and a SNARK prover: `V` (`SpartanSromNode`), the honest
prover `P`, and the library's copy extractor, its program and fuel. -/
def submissionOf : Submission where
  V := V LV
  P := P proveLeaf
  E := WitnessSending.E
  ext := WitnessSending.ext
  ε := εR1
  δ := 0
  qV := qVR1
  fuel := WitnessSending.fuel

/-- **The facts the other modules prove**, as hypotheses of the certificate. -/
structure Facts : Prop where
  /-- `leafSize 0 = 80`: the zero-step leaf is its header (§7). -/
  size_zero : LV.size 0 = 80
  /-- Leaf completeness, for every oracle: the honest SNARK of a chain of `1 ≤ n ≤ chainCap` steps
  has `leafSize n − 80` bytes and is accepted. -/
  leaf_complete : ∀ (H : ByteArray → Digest) (s : Digest) (n : ℕ), 1 ≤ n → n ≤ chainCap →
    80 + ((proveLeaf s n (chainEnd s n)).run H).size = LV.size n ∧
      (LV.prog s n (chainEnd s n) ((proveLeaf s n (chainEnd s n)).run H)).run H = true
  /-- A knowledge state with error `2^-129` for every public key (`SoundnessKState`). -/
  ks : ∀ vk, Nonempty (KState (Rel (accV LV vk)) (V LV vk) WitnessSending.E εR1)
  /-- The SNARK verifier asks at most `qb n` queries along every path of answers, on a chain of
  at most `chainCap` steps. -/
  atMost : ∀ s n h π, n ≤ chainCap → OProg.AtMost (LV.qb n) (LV.prog s n h π)
  /-- `qb n ≤ 2^16` on every chain of at most `chainCap` steps. -/
  qb_le : ∀ n ≤ chainCap, LV.qb n ≤ 2 ^ 16

/-- The submission's `acc` is `accV LV`. -/
theorem acc_eq : (submissionOf LV proveLeaf).acc = accV LV := accV_eq_acc LV _ rfl rfl

variable {LV proveLeaf}

/-- **The query bound**: at most `2^16` queries along every path, on every input. -/
theorem V_atMost (F : Facts LV proveLeaf) (vk c : Digest) (π : Proof) :
    OProg.AtMost (2 ^ 16) (V LV vk c π) :=
  atMost_V F.atMost F.qb_le vk c π

/-- **Perfect completeness**, for every public key and oracle function. -/
theorem complete (F : Facts LV proveLeaf) (vk : Digest) :
    Complete (Rel ((submissionOf LV proveLeaf).acc vk)) ((submissionOf LV proveLeaf).P vk)
      ((submissionOf LV proveLeaf).V vk) := by
  intro H c w hR
  rw [acc_eq] at hR
  show (V LV vk c ((P proveLeaf vk c w).run H)).run H = true
  cases w with
  | node c₁ c₂ p₁ p₂ =>
    have hπ : (P proveLeaf vk c (.node c₁ c₂ p₁ p₂)).run H = encode (.node c₁ c₂ p₁ p₂) := by
      simp [P, OProg.run, encodeF_eq]
    rw [hπ, V_encode_node (V_atMost F vk) hR]; rfl
  | leaf s n =>
    obtain ⟨hn, hc⟩ := hR
    have hn64 : n < 2 ^ 64 := hn.trans_lt (by decide)
    by_cases h0 : n = 0
    · subst h0
      have hπ : (P proveLeaf vk c (.leaf s 0)).run H = leafBytes s 0 s ByteArray.empty := by
        simp [P, OProg.run]
      obtain ⟨ht, hN, hS, hH, -⟩ := leafBytes_parse s (show 0 < 2 ^ 64 by decide) s .empty
      have hsz := leafBytes_size s 0 s .empty
      rw [hπ, V_leaf LV (by rw [hsz]; simp) (by rw [hsz]; simp) ht, leafProg]
      have hh : leafHeaderOK LV c (leafBytes s 0 s .empty) = true :=
        (leafHeaderOK_iff LV).mpr ⟨by rw [hN]; exact Nat.zero_le _,
          by rw [hsz, hN, F.size_zero]; rfl, by rw [hH, hN, hc]; rfl⟩
      rw [ite_eq_left hh, ite_eq_left hN]
      simp [OProg.run, hS, hH]
    · set πS := (proveLeaf s n (chainEnd s n)).run H
      have hπ : (P proveLeaf vk c (.leaf s n)).run H = leafBytes s n (chainEnd s n) πS := by
        simp [P, h0, OProg.run_bind, πS]; rfl
      obtain ⟨ht, hN, hS, hH, hSn⟩ := leafBytes_parse s hn64 (chainEnd s n) πS
      obtain ⟨hsize, hacc⟩ := F.leaf_complete H s n (Nat.one_le_iff_ne_zero.mpr h0) hn
      have hsz := leafBytes_size s n (chainEnd s n) πS
      have h80 := LV.size_ge n
      rw [hπ, V_leaf LV (by omega) (by omega) ht, leafProg]
      have hh : leafHeaderOK LV c (leafBytes s n (chainEnd s n) πS) = true :=
        (leafHeaderOK_iff LV).mpr ⟨by rw [hN]; exact hn, by rw [hsz, hN, hsize], by rw [hH, hN, hc]⟩
      rw [ite_eq_left hh, ite_eq_right (by rw [hN]; exact h0), hS, hN, hH, hSn]
      exact hacc

/-- **The query bound** of `KS`: at most `2^16` queries on every input and oracle. -/
theorem V_queries (F : Facts LV proveLeaf) (vk : Digest) (H : ByteArray → Digest) (c : Digest)
    (π : Proof) : ((V LV vk c π).queries H).length ≤ qVR1 :=
  (V_atMost F vk c π).queries_length H

theorem εR1_le_errorCap : εR1 ≤ errorCap := by
  rw [εR1_eq]; unfold errorCap
  exact pow_le_pow_of_le_one (by positivity) (inv_le_one_of_one_le₀ (by norm_num)) (by norm_num)

/-- **The certificate**: knowledge soundness and completeness (`δ = 0`) for every public key, the
library's extractor program computing `E`, and the caps. -/
theorem certificateOf (F : Facts LV proveLeaf) : Certificate (submissionOf LV proveLeaf) where
  secure vk := by
    show KS (Rel ((submissionOf LV proveLeaf).acc vk)) (V LV vk) WitnessSending.E εR1 qVR1
    rw [acc_eq]
    exact ⟨F.ks vk, V_queries F vk⟩
  complete vk := complete_withError_zero (complete F vk)
  computes := WitnessSending.computes
  cap := ⟨εR1_le_errorCap, show (0 : ℝ≥0) ≤ _ from zero_le, show qVR1 ≤ 2 ^ 16 from le_rfl,
    fun t => by simp only [submissionOf, WitnessSending.fuel, extractorBudget]; omega,
    show WitnessSending.ext.body.size ≤ progCap by decide⟩

/-- **The certificate against a rendered claim** whose numbers are at least the submission's and
whose fuel is within the budget. -/
theorem certificateR_of (F : Facts LV proveLeaf) (D : Declared) (hε : εR1 ≤ D.ε)
    (hq : qVR1 ≤ D.qV) (hf : ∀ t, 8 * t ≤ D.fuel t ∧ D.fuel t ≤ extractorBudget t) :
    CertificateR D (submissionOf LV proveLeaf) :=
  ⟨certificateOf F, hε, show (0 : ℝ≥0) ≤ _ from zero_le, hq, hf⟩

/-- The declared error of the claim, `1 / 2^129` as rendered, bounds the proved `2^-129`. -/
theorem εR1_le_declared : εR1 ≤ (1 : ℝ≥0) / 680564733841876926926749214863536422912 := by
  rw [εR1_eq, one_div, inv_pow]
  exact inv_anti₀ (by positivity) (by norm_num)

end SpartanSrom
