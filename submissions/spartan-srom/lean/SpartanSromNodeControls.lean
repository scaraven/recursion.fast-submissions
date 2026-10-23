/-
# Controls of the v4 verifier's branches and of the claim (BLUEPRINT §6; new in v4)

Positive and negative controls, kernel-checked, that evaluate no hash: every statement about a
signature goes through the library's symbolic `Signer.sigOk_sign`, every chain through the
definitions. They hold for every leaf verifier `LV` unless the entry's is named.

* **Formats** (§1): a clear leaf `C` and a plain node `N` decode to their witnesses
  (`format_C`, `format_N`); a bundle `encode W ‖ T` decodes to `W` (`format_B`: `decode` stops
  at `W`).
* **Positive** (§6): under the reference signer's key `Signer.pk sk`, with `σ0` its signature of
  the empty trace: a clear slot is accepted (`clearSlot_acc`); the clear tree of two clear leaves
  is a node witness of the relation and its plain encoding, signed `σ0`, is accepted by the
  submission's `acc` (`clearTree_rel`, `clearTree_acc`); the bundle of that tree with any `T` of
  the right size passes the whole static phase and reduces to its SNARK runs (`bundle_static`),
  so the bundle branch's conclusion is reachable. The zero-step `L` leaf and a clear `C` leaf of
  `n = 0` are accepted with no query (`zeroLeaf_accepted`, `zeroClear_accepted`); the `L` leaf
  is rejected under another statement and with a byte appended or removed
  (`zeroLeaf_other_stmt`, `zeroLeaf_canaries`).
* **Bundle negatives** (§6): a slot with a non-empty trace (`clearLeaves_trace`), two slots
  with different signatures (`clearLeaves_sig`), `|T|` off by one byte (`bundleOK_size`, used by
  `canary_B_push`/`canary_B_pop`), the static query bound exceeded (`bundleOK_qbound`; reachable
  with fourteen `n = 2^12` leaves, `qbound_fourteen`, though not within `proofCap`), a bundled
  leaf with `n = 0` (`bundleOK_zero`), a clear or bundled leaf with `n > clearCap = 2^12` (D-6:
  `clearLeafOK_cap`, `clear_overCap` and `bundle_overCap` at `n = 4097`, `bundleOK_cap`): each
  rejected with no query (`V_bundle_reject`, `bundleProg_none₁`, `bundleProg_none₂`).
* **Statement binding** (review F1-m3): `clearLeafOK_stmt` (`C`), `V_node_stmt` (`N`),
  `bundleOK_stmt` (`B`'s node statement), `runBundle_stmt` (a bundled leaf's slot statement),
  with `zeroLeaf_other_stmt` (`L`).
* **Canaries** (§6, DESIGN-v3 §6.3 step 7): one byte appended to or removed from an `L`, `C`,
  `N` or accepted `B` proof is rejected with no query (`canary_*`).
* **The claim**: the claim of `claim.json` is certified (`certificateR_claim`); one declaring
  `ε = 2^-130`, `qV = 2^16 − 1` or fuel `7 t` is not (`claim_negatives`).
-/
import SpartanSromFinal
import RecursionFast.Library.Signer

open scoped NNReal

namespace SpartanSrom.NodeControls
open RecursionFast OProg
open RecursionFast.WitnessSending (encode decode decode_encode encodeF decodeF encodeF_eq
  decodeF_eq size_encode size_encode_leaf size_eq_length)

variable (LV : LeafVerifier)

/-! ## Helpers -/

/-- A program that returns `false` is accepted on no trace. -/
theorem ret_false_rejects (tr : Trace) : (OProg.ret false : OProg Bool).runSeq tr ≠ some true := by
  cases tr <;> simp [RecursionFast.OProg.runSeq]

/-- The header of a clear leaf names its start and length. -/
theorem leaf_parts (s : Digest) {n : ℕ} (hn : n < 2 ^ 64) :
    leafS (encode (.leaf s n)) = s ∧ leafN (encode (.leaf s n)) = n := by
  have h := decode_leaf (show 48 ≤ (encode (.leaf s n)).size by rw [size_encode_leaf])
    (tagWord_encode_leaf s n)
  rw [decode_encode _ (show (Wit.leaf s n).Fits from hn)] at h
  injection h with h; injection h with h1 h2; exact ⟨h1.symm, h2.symm⟩

theorem bundleBytes_cons (x : BLeaf) (ls : List BLeaf) :
    bundleBytes LV (x :: ls) = 32 + (LV.size x.2.2 - 80) + bundleBytes LV ls := by
  simp [bundleBytes]

/-- A non-empty bundle takes at least 32 bytes of `T`; so never exactly one. -/
theorem bundleBytes_ne_one (ls : List BLeaf) : bundleBytes LV ls ≠ 1 := by
  cases ls with
  | nil => simp [bundleBytes]
  | cons x ls => rw [bundleBytes_cons]; omega

/-- A slot that `clearLeaves` accepts has an empty trace, the shared signature and a proof
within `proofCap`. -/
theorem clearLeaves_slot {σ0 : Sig} {c : Digest} {p : Signed} {l : List BLeaf}
    (h : clearLeaves σ0 c p = some l) : p.tr = [] ∧ p.σ = σ0 ∧ p.π.size ≤ proofCap := by
  by_contra hn
  rw [clearLeaves_eq, ite_eq_right fun hs => hn ⟨List.isEmpty_iff.mp hs.1, hs.2.1, hs.2.2⟩] at h
  cases h

/-- A node passing the bundle's static phase fits the output format. -/
theorem fits_of_bundleOK {vk c c₁ c₂ : Digest} {p₁ p₂ : Signed} {l₁ l₂ : List BLeaf}
    {T : ByteArray} (h₁ : clearLeaves p₁.σ c₁ p₁ = some l₁) (h₂ : clearLeaves p₁.σ c₂ p₂ = some l₂)
    (hok : bundleOK LV vk c c₁ c₂ p₁.σ (l₁ ++ l₂) T = true) : (Wit.node c₁ c₂ p₁ p₂).Fits := by
  have hσ := ((bundleOK_iff LV).mp hok).2.2.2.2
  simp only [SigOkF_eq, SigOk, Bool.and_eq_true, decide_eq_true_eq] at hσ
  obtain ⟨⟨⟨hi, ho⟩, hp⟩, -⟩ := hσ
  obtain ⟨t₁, -, c₁'⟩ := clearLeaves_slot h₁
  obtain ⟨t₂, σ₂, c₂'⟩ := clearLeaves_slot h₂
  have hcap : proofCap < 2 ^ 64 := by unfold proofCap; norm_num
  have hidx : 2 ^ sigHeight < 2 ^ 64 := by unfold sigHeight; norm_num
  exact ⟨⟨c₁'.trans_lt hcap, by simp [t₁], by simp [t₁], hi.trans hidx, ho, hp⟩,
    ⟨c₂'.trans_lt hcap, by simp [t₂], by simp [t₂], by rw [σ₂]; exact hi.trans hidx,
      by rw [σ₂]; exact ho, by rw [σ₂]; exact hp⟩⟩

/-- On a proof that starts with a node's canonical encoding and is longer, `V` is the bundle
branch. -/
theorem V_bundle {vk c c₁ c₂ : Digest} {p₁ p₂ : Signed} {π : Proof}
    (hf : (Wit.node c₁ c₂ p₁ p₂).Fits) (hpre : π.extract 0 (encode (.node c₁ c₂ p₁ p₂)).size =
      encode (.node c₁ c₂ p₁ p₂)) (hlt : (encode (.node c₁ c₂ p₁ p₂)).size < π.size) :
    V LV vk c π = bundleProg LV vk c π c₁ c₂ p₁ p₂ := by
  have he8 := size_encode_node c₁ c₂ p₁ p₂
  have hd : decode π = some (.node c₁ c₂ p₁ p₂) := decode_of_extract hf hpre
  have ht : tagWord π = tagWord (encode (.node c₁ c₂ p₁ p₂)) := by
    rw [tagWord_eq, tagWord_eq]
    congr 1
    rw [← hpre, extract_zero_toList, List.take_take, Nat.min_eq_left he8]
  rw [V_tag LV (by omega) (by rw [ht, tagWord_encode_node]; decide), decodeF_eq, hd]
  simp only [encodeF_eq, show encode (.node c₁ c₂ p₁ p₂) ≠ π from fun h => by
    rw [h] at hlt; omega, ↓reduceIte]

/-- **The bundle branch's static phase**: with both slots clear trees, `bundleProg` runs the
SNARKs iff `bundleOK` holds, and rejects with no query otherwise. -/
theorem bundleProg_static {vk c c₁ c₂ : Digest} {p₁ p₂ : Signed} {π : Proof} {l₁ l₂ : List BLeaf}
    (hpre : IsStrictPrefix (encode (.node c₁ c₂ p₁ p₂)) π)
    (h₁ : clearLeaves p₁.σ c₁ p₁ = some l₁) (h₂ : clearLeaves p₁.σ c₂ p₂ = some l₂) :
    bundleProg LV vk c π c₁ c₂ p₁ p₂ =
      let T := π.extract (encode (.node c₁ c₂ p₁ p₂)).size π.size
      if bundleOK LV vk c c₁ c₂ p₁.σ (l₁ ++ l₂) T then runBundle LV T (l₁ ++ l₂) 0
      else .ret false := by
  rw [bundleProg]
  simp only [encodeF_eq, hpre, ↓reduceIte, h₁, h₂]

/-- A bundle whose first slot is not a clear tree is rejected with no query. -/
theorem bundleProg_none₁ {vk c c₁ c₂ : Digest} {p₁ p₂ : Signed} {π : Proof}
    (h : clearLeaves p₁.σ c₁ p₁ = none) : bundleProg LV vk c π c₁ c₂ p₁ p₂ = .ret false := by
  rw [bundleProg]; split_ifs <;> simp [h]

/-- A bundle whose second slot is not a clear tree is rejected with no query. -/
theorem bundleProg_none₂ {vk c c₁ c₂ : Digest} {p₁ p₂ : Signed} {π : Proof}
    (h : clearLeaves p₁.σ c₂ p₂ = none) : bundleProg LV vk c π c₁ c₂ p₁ p₂ = .ret false := by
  rw [bundleProg]; split_ifs
  · split
    · rename_i h₂; rw [h] at h₂; cases h₂
    · rfl
  · rfl

/-! ## Bytes: pushing and dropping a byte keeps the front -/

theorem extract_push {π : Proof} {k : ℕ} (hk : k ≤ π.size) (b : UInt8) :
    (π.push b).extract 0 k = π.extract 0 k :=
  ByteArray.ext_toList (by rw [extract_zero_toList, extract_zero_toList, take_push hk])

theorem extract_dropLast {π : Proof} {k : ℕ} (hk : k + 1 ≤ π.size) :
    (dropLast π).extract 0 k = π.extract 0 k :=
  ByteArray.ext_toList (by rw [extract_zero_toList, extract_zero_toList, take_dropLast hk])

theorem tagWord_push {π : Proof} (h : 8 ≤ π.size) (b : UInt8) :
    tagWord (π.push b) = tagWord π := by
  rw [tagWord_eq, tagWord_eq, take_push h]

theorem tagWord_dropLast {π : Proof} (h : 9 ≤ π.size) : tagWord (dropLast π) = tagWord π := by
  rw [tagWord_eq, tagWord_eq, take_dropLast h]

/-! ## Formats (§1) -/

/-- `C`: the clear leaf decodes to its leaf witness. -/
theorem format_C (s : Digest) {n : ℕ} (hn : n < 2 ^ 64) :
    decode (encode (.leaf s n)) = some (.leaf s n) := decode_encode _ hn

/-- `N`: the plain node decodes to its node witness. -/
theorem format_N {c₁ c₂ : Digest} {p₁ p₂ : Signed} (h : (Wit.node c₁ c₂ p₁ p₂).Fits) :
    decode (encode (.node c₁ c₂ p₁ p₂)) = some (.node c₁ c₂ p₁ p₂) := decode_encode _ h

/-- `B`: the bundle decodes to its clear tree; `decode` stops before `T`. -/
theorem format_B {W : Wit} (h : W.Fits) (T : ByteArray) : decode (encode W ++ T) = some W :=
  decode_append W h T

/-! ## Positive controls: the reference signer (symbolic, no hash evaluated) -/

section Signer

variable (sk : ℕ → ℕ → Digest)

/-- The reference signer's signature of the empty trace with one-time key `0`. -/
def σ0 : Sig := Signer.sign sk 0 (traceDigest [])

theorem sigOk_σ0 : SigOk (Signer.pk sk) (traceDigest []) (σ0 sk) = true :=
  Signer.sigOk_sign sk 0 (by unfold sigHeight; norm_num) _

/-- A clear slot: the clear leaf of `(s, n)`, the empty trace, `σ0`. -/
def clearSlot (s : Digest) (n : ℕ) : Signed := ⟨encode (.leaf s n), [], σ0 sk⟩

/-- **Positive**: a clear slot of a chain within `clearCap`, signed `σ0`, is accepted under the
reference key, with no query. -/
theorem clearSlot_acc (s : Digest) {n : ℕ} (hn : n ≤ clearCap) :
    accV LV (Signer.pk sk) (leafStmt (chainEnd s n) n) (clearSlot sk s n) = true := by
  have hn64 : n < 2 ^ 64 := hn.trans_lt (by unfold clearCap; norm_num)
  obtain ⟨hS, hN⟩ := leaf_parts s hn64
  rw [accV, accWith, clearSlot, V_clear LV (size_encode_leaf s n) (tagWord_encode_leaf s n)]
  simp only [size_encode_leaf, List.not_mem_nil, IsEmpty.forall_iff, implies_true,
    decide_true, SigOkF_eq, traceDigestF_eq, sigOk_σ0, clearLeafOK, hS, hN, hn,
    leafStmtF_eq, chainEndF_eq, RecursionFast.OProg.runSeq, Bool.and_true, List.length_nil]
  simp [proofCap]

/-- The statement of the clear leaf of `(s, n)`. -/
abbrev cl (s : Digest) (n : ℕ) : Digest := leafStmt (chainEnd s n) n

/-- The clear tree of two clear leaves, every slot signed `σ0`. -/
def clearTree (s₁ : Digest) (n₁ : ℕ) (s₂ : Digest) (n₂ : ℕ) : Wit :=
  .node (cl s₁ n₁) (cl s₂ n₂) (clearSlot sk s₁ n₁) (clearSlot sk s₂ n₂)

/-- **Positive**: the clear tree is a node witness of the relation under the reference key. -/
theorem clearTree_rel (s₁ : Digest) {n₁ : ℕ} (s₂ : Digest) {n₂ : ℕ} (h₁ : n₁ ≤ clearCap)
    (h₂ : n₂ ≤ clearCap) :
    Rel (accV LV (Signer.pk sk)) (nodeStmt (cl s₁ n₁) (cl s₂ n₂)) (clearTree sk s₁ n₁ s₂ n₂) :=
  ⟨rfl, clearSlot_acc LV sk s₁ h₁, clearSlot_acc LV sk s₂ h₂⟩

theorem σ0_counts : (σ0 sk).ots.length = wotsLen ∧ (σ0 sk).path.length = sigHeight ∧
    (σ0 sk).idx = 0 := by
  refine ⟨by simp [σ0, Signer.sign, Signer.wotsDigits_length], Signer.sibs_length _ _ _ _, rfl⟩

theorem clearSlot_fits (s : Digest) (n : ℕ) : (clearSlot sk s n).Fits := by
  obtain ⟨ho, hp, hi⟩ := σ0_counts sk
  refine ⟨by simp [clearSlot, size_encode_leaf], by simp [clearSlot], by simp [clearSlot],
    by simp [clearSlot, hi], ho, hp⟩

/-- A clear slot is a clear-tree slot of one clear leaf (whatever its length). -/
theorem clearLeaves_clearSlot (s : Digest) {n : ℕ} (hn : n < 2 ^ 64) :
    clearLeaves (σ0 sk) (cl s n) (clearSlot sk s n) = some [(cl s n, s, n)] := by
  obtain ⟨hS, hN⟩ := leaf_parts s hn
  rw [clearLeaves_eq]
  simp [clearSlot, size_encode_leaf, tagWord_encode_leaf, hS, hN, proofCap]

theorem clearTree_size (s₁ : Digest) (n₁ : ℕ) (s₂ : Digest) (n₂ : ℕ) :
    (encode (clearTree sk s₁ n₁ s₂ n₂)).size = 9752 := by
  -- stated for every signature with the right counts: the kernel then never evaluates `σ0 sk`
  have h : ∀ σ : Sig, σ.ots.length = wotsLen → σ.path.length = sigHeight →
      (encode (.node (cl s₁ n₁) (cl s₂ n₂) ⟨encode (.leaf s₁ n₁), [], σ⟩
        ⟨encode (.leaf s₂ n₂), [], σ⟩)).size = 9752 := fun σ ho hp => by
    rw [size_encode]
    simp only [witWords, signedWords, sigWords, bytesWords, logWords, List.length_cons,
      List.length_append, List.length_flatMap, packBytes_length, Vector.length_toList,
      List.flatMap_nil, List.length_nil, ← size_eq_length, size_encode_leaf, List.map_const',
      List.sum_replicate, smul_eq_mul, ho, hp]
    rfl
  exact h _ (σ0_counts sk).1 (σ0_counts sk).2.1

/-- **Positive** (§6): the plain encoding of the clear tree, with the empty trace and the
signature `σ0`, is accepted by the entry's `acc` under the reference key. -/
theorem clearTree_acc (s₁ : Digest) {n₁ : ℕ} (s₂ : Digest) {n₂ : ℕ} (h₁ : n₁ ≤ clearCap)
    (h₂ : n₂ ≤ clearCap) :
    submission.acc (Signer.pk sk) (nodeStmt (cl s₁ n₁) (cl s₂ n₂))
      ⟨encode (clearTree sk s₁ n₁ s₂ n₂), [], σ0 sk⟩ = true := by
  rw [show submission = submissionOf leafVerifier proveLeafR1 from rfl, acc_eq, accV, accWith]
  rw [clearTree, V_encode_node (atMost_V KS.atMost_leaf KS.qb_le _)
    (clearTree_rel leafVerifier sk s₁ s₂ h₁ h₂), ← clearTree, clearTree_size]
  simp only [List.not_mem_nil, IsEmpty.forall_iff, implies_true, decide_true,
    SigOkF_eq, traceDigestF_eq, sigOk_σ0, RecursionFast.OProg.runSeq, Bool.and_true,
    List.length_nil]
  simp [proofCap]

/-- **Positive** (§6): the bundle of the clear tree with bytes `T` of the right size passes the
whole static phase (clear tree, `σ0` checked once, sizes, the query bound) and reduces to the two
leaves' SNARK runs over `T`: it is accepted exactly when they accept. -/
theorem bundle_static (s₁ : Digest) {n₁ : ℕ} (s₂ : Digest) {n₂ : ℕ} (h₁ : 1 ≤ n₁ ∧ n₁ ≤ clearCap)
    (h₂ : 1 ≤ n₂ ∧ n₂ ≤ clearCap) (T : ByteArray)
    (hT : T.size = bundleBytes LV [(cl s₁ n₁, s₁, n₁), (cl s₂ n₂, s₂, n₂)])
    (hq : LV.qb n₁ + LV.qb n₂ ≤ 2 ^ 16) :
    V LV (Signer.pk sk) (nodeStmt (cl s₁ n₁) (cl s₂ n₂)) (encode (clearTree sk s₁ n₁ s₂ n₂) ++ T) =
      runBundle LV T [(cl s₁ n₁, s₁, n₁), (cl s₂ n₂, s₂, n₂)] 0 := by
  have hT0 : 0 < T.size := by rw [hT, bundleBytes_cons]; omega
  have hfit : (clearTree sk s₁ n₁ s₂ n₂).Fits :=
    ⟨clearSlot_fits sk s₁ n₁, clearSlot_fits sk s₂ n₂⟩
  have hpre : IsStrictPrefix (encode (clearTree sk s₁ n₁ s₂ n₂))
      (encode (clearTree sk s₁ n₁ s₂ n₂) ++ T) := isStrictPrefix_append hT0
  have hcl := fun s n (hn : n < 2 ^ 64) => clearLeaves_clearSlot sk s hn
  have hTx : (encode (clearTree sk s₁ n₁ s₂ n₂) ++ T).extract
      (encode (clearTree sk s₁ n₁ s₂ n₂)).size (encode (clearTree sk s₁ n₁ s₂ n₂) ++ T).size = T :=
    ByteArray.extract_append_eq_right rfl (by rw [ByteArray.size_append])
  have hok : bundleOK LV (Signer.pk sk) (nodeStmt (cl s₁ n₁) (cl s₂ n₂)) (cl s₁ n₁) (cl s₂ n₂)
      (σ0 sk) ([(cl s₁ n₁, s₁, n₁)] ++ [(cl s₂ n₂, s₂, n₂)]) T = true :=
    (bundleOK_iff LV).mpr ⟨fun x hx => by
      rcases List.mem_pair.mp hx with rfl | rfl
      exacts [h₁, h₂], hT, by simpa [bundleQ] using hq, by rw [nodeStmtF_eq],
      by rw [SigOkF_eq, traceDigestF_eq]; exact sigOk_σ0 sk⟩
  unfold clearTree at hfit hpre hTx ⊢
  rw [V_bundle LV hfit hpre.2 hpre.1, bundleProg_static LV hpre
    (hcl s₁ n₁ (h₁.2.trans_lt (by unfold clearCap; norm_num)))
    (hcl s₂ n₂ (h₂.2.trans_lt (by unfold clearCap; norm_num)))]
  dsimp only
  rw [hTx]
  exact ite_eq_left hok

end Signer

/-! ## Negative controls of the bundle (§6): rejected with no query -/

/-- A slot with a non-empty trace is not a clear-tree slot. -/
theorem clearLeaves_trace {σ0 : Sig} {c : Digest} {p : Signed} (h : p.tr ≠ []) :
    clearLeaves σ0 c p = none := by
  rw [clearLeaves_eq, ite_eq_right]; rintro ⟨he, -⟩; exact h (List.isEmpty_iff.mp he)

/-- A slot whose signature is not the shared one is not a clear-tree slot. -/
theorem clearLeaves_sig {σ0 : Sig} {c : Digest} {p : Signed} (h : p.σ ≠ σ0) :
    clearLeaves σ0 c p = none := by
  rw [clearLeaves_eq, ite_eq_right]; rintro ⟨-, hs, -⟩; exact h hs

/-- `|T|` other than the leaves' bytes: rejected. -/
theorem bundleOK_size {vk c c₁ c₂ : Digest} {σ : Sig} {ls : List BLeaf} {T : ByteArray}
    (h : T.size ≠ bundleBytes LV ls) : bundleOK LV vk c c₁ c₂ σ ls T = false :=
  Bool.eq_false_iff.mpr fun hok => h ((bundleOK_iff LV).mp hok).2.1

/-- The static query bound exceeded: rejected. -/
theorem bundleOK_qbound {vk c c₁ c₂ : Digest} {σ : Sig} {ls : List BLeaf} {T : ByteArray}
    (h : 2 ^ 16 < bundleQ LV ls) : bundleOK LV vk c c₁ c₂ σ ls T = false :=
  Bool.eq_false_iff.mpr fun hok => absurd ((bundleOK_iff LV).mp hok).2.2.1 (by omega)

/-- A bundled leaf with `n = 0`: rejected. -/
theorem bundleOK_zero {vk c c₁ c₂ : Digest} {σ : Sig} {ls : List BLeaf} {T : ByteArray}
    {x : BLeaf} (hx : x ∈ ls) (h : x.2.2 = 0) : bundleOK LV vk c c₁ c₂ σ ls T = false :=
  Bool.eq_false_iff.mpr fun hok => absurd (((bundleOK_iff LV).mp hok).1 x hx).1 (by omega)

/-- A bundled leaf with `n > clearCap` (D-6): rejected. -/
theorem bundleOK_cap {vk c c₁ c₂ : Digest} {σ : Sig} {ls : List BLeaf} {T : ByteArray}
    {x : BLeaf} (hx : x ∈ ls) (h : clearCap < x.2.2) : bundleOK LV vk c c₁ c₂ σ ls T = false :=
  Bool.eq_false_iff.mpr fun hok => absurd (((bundleOK_iff LV).mp hok).1 x hx).2 (by omega)

/-- A clear leaf with `n > clearCap` (D-6): rejected by `C` before any hash. -/
theorem clearLeafOK_cap {c : Digest} {π : Proof} (h : clearCap < leafN π) :
    clearLeafOK c π = false := by
  simp [clearLeafOK, show ¬ leafN π ≤ clearCap by omega]

/-! ### Statement binding (review F1-m3): each branch rejects a proof under another statement -/

/-- `C` binds the statement: under any digest other than the leaf statement of the recomputed
chain, the clear leaf is rejected. -/
theorem clearLeafOK_stmt {c : Digest} {π : Proof}
    (h : c ≠ leafStmt (chainEnd (leafS π) (leafN π)) (leafN π)) : clearLeafOK c π = false := by
  simp [clearLeafOK, leafStmtF_eq, chainEndF_eq, h]

/-- `N` binds the statement: a plain node is rejected under any digest other than `nodeStmt` of
its children, with no query. -/
theorem V_node_stmt {vk c c₁ c₂ : Digest} {p₁ p₂ : Signed} (hf : (Wit.node c₁ c₂ p₁ p₂).Fits)
    (h : c ≠ nodeStmt c₁ c₂) : V LV vk c (encode (.node c₁ c₂ p₁ p₂)) = .ret false := by
  rw [V_tag LV (size_encode_node _ _ _ _) (by rw [tagWord_encode_node]; decide), decodeF_eq,
    decode_encode _ hf]
  simp [encodeF_eq, nodeStmtF_eq, h]

/-- `B` binds the node statement: the static checks fail under any other digest. -/
theorem bundleOK_stmt {vk c c₁ c₂ : Digest} {σ : Sig} {ls : List BLeaf} {T : ByteArray}
    (h : c ≠ nodeStmt c₁ c₂) : bundleOK LV vk c c₁ c₂ σ ls T = false :=
  Bool.eq_false_iff.mpr fun hok => h (by rw [((bundleOK_iff LV).mp hok).2.2.2.1, nodeStmtF_eq])

/-- `B` binds each bundled leaf's slot statement: a leaf whose slot statement is not
`leafStmt h n` for the `h` read from `T` stops the runs, before its SNARK. -/
theorem runBundle_stmt {T : ByteArray} {c s : Digest} {n o : ℕ} {ls : List BLeaf}
    (h : c ≠ leafStmt (digestFrom T o) n) : runBundle LV T ((c, s, n) :: ls) o = .ret false := by
  rw [runBundle, ite_eq_right (by rwa [leafStmtF_eq])]

/-- **The static query bound is reachable within `clearCap`** (not within `proofCap`, review
F1-m5: fourteen `2^12`-step leaves need `14 · 796,031` bytes of `T`): fourteen bundled leaves of
`2^12` steps ask more than `2^16` queries (`qBound 12 = 4 753`), so `bundleOK_qbound` rejects
them. -/
theorem qbound_fourteen (c s : Digest) :
    2 ^ 16 < bundleQ leafVerifier (List.replicate 14 (c, s, 2 ^ 12)) := by
  have hk : Leaf.kap (2 ^ 12) = 12 := Nat.clog_pow 2 12 (by norm_num)
  simp only [bundleQ, List.map_replicate, List.sum_replicate, smul_eq_mul, leafVerifier,
    Leaf.leafVerifier, hk]
  decide

/-- On a bundle whose static phase fails, `V` rejects with no query. -/
theorem V_bundle_reject {vk c c₁ c₂ : Digest} {p₁ p₂ : Signed} {π : Proof}
    (hf : (Wit.node c₁ c₂ p₁ p₂).Fits) (hpre : IsStrictPrefix (encode (.node c₁ c₂ p₁ p₂)) π)
    (hbad : ∀ l₁ l₂, clearLeaves p₁.σ c₁ p₁ = some l₁ → clearLeaves p₁.σ c₂ p₂ = some l₂ →
      bundleOK LV vk c c₁ c₂ p₁.σ (l₁ ++ l₂)
        (π.extract (encode (.node c₁ c₂ p₁ p₂)).size π.size) = false) :
    V LV vk c π = .ret false := by
  rw [V_bundle LV hf hpre.2 hpre.1]
  cases h₁ : clearLeaves p₁.σ c₁ p₁ with
  | none => exact bundleProg_none₁ LV h₁
  | some l₁ =>
    cases h₂ : clearLeaves p₁.σ c₂ p₂ with
    | none => exact bundleProg_none₂ LV h₂
    | some l₂ =>
      rw [bundleProg_static LV hpre h₁ h₂]
      simp only [hbad l₁ l₂ h₁ h₂]; rfl

/-! ## Canaries (§6): one byte appended or removed, rejected with no query -/

theorem leafProg_header_seq {c : Digest} {π : Proof} {tr : Trace}
    (h : (leafProg LV c π).runSeq tr = some true) : leafHeaderOK LV c π = true := by
  by_contra hn
  rw [leafProg, ite_eq_right hn] at h
  exact ret_false_rejects tr h

/-- A proof `V` accepts on some trace has at least 8 bytes. -/
theorem size_of_accept {vk c : Digest} {π : Proof} {tr : Trace}
    (h : (V LV vk c π).runSeq tr = some true) : 8 ≤ π.size := by
  by_contra h8; rw [V_short LV (by omega)] at h; exact ret_false_rejects tr h

/-- The leaf branch rejects a proof whose size is not the leaf size of its header. -/
theorem leafProg_size {c : Digest} {π : Proof} (h : π.size ≠ LV.size (leafN π)) :
    leafProg LV c π = .ret false := by
  rw [leafProg, ite_eq_right]; intro hh; exact h ((leafHeaderOK_iff LV).mp hh).2.1

/-- **`L`**: one byte appended to an accepted SNARK leaf proof is rejected. -/
theorem canary_L_push {vk c : Digest} {π : Proof} {tr : Trace}
    (h : (V LV vk c π).runSeq tr = some true) (ht : tagWord π = 0) (hs : π.size ≠ 48)
    (b : UInt8) (c' : Digest) : V LV vk c' (π.push b) = .ret false := by
  have h8 := size_of_accept LV h
  rw [V_leaf LV h8 hs ht] at h
  obtain ⟨-, hsz, -⟩ := (leafHeaderOK_iff LV).mp (leafProg_header_seq LV h)
  have h80 := LV.size_ge (leafN π)
  obtain ⟨ht', hn', -⟩ := parse48_congr (take_push (π := π) (by omega) b)
  rw [V_leaf LV (by rw [ByteArray.size_push]; omega) (by rw [ByteArray.size_push]; omega)
    (by rw [ht', ht]), leafProg_size LV (by rw [ByteArray.size_push, hn']; omega)]

/-- **`L`**: the last byte removed from an accepted SNARK leaf proof is rejected. -/
theorem canary_L_pop {vk c : Digest} {π : Proof} {tr : Trace}
    (h : (V LV vk c π).runSeq tr = some true) (ht : tagWord π = 0) (hs : π.size ≠ 48)
    (c' : Digest) : V LV vk c' (dropLast π) = .ret false := by
  have h8 := size_of_accept LV h
  rw [V_leaf LV h8 hs ht] at h
  obtain ⟨-, hsz, -⟩ := (leafHeaderOK_iff LV).mp (leafProg_header_seq LV h)
  have h80 := LV.size_ge (leafN π)
  obtain ⟨ht', hn', -⟩ := parse48_congr (take_dropLast (π := π) (by omega))
  rw [V_leaf LV (by rw [size_dropLast]; omega) (by rw [size_dropLast]; omega)
    (by rw [ht', ht]), leafProg_size LV (by rw [size_dropLast, hn']; omega)]

/-- **`C`**: one byte appended to a clear leaf (48 bytes, tag `0`) is rejected. -/
theorem canary_C_push {π : Proof} (hs : π.size = 48) (ht : tagWord π = 0) (b : UInt8)
    (vk c' : Digest) : V LV vk c' (π.push b) = .ret false := by
  have h80 := LV.size_ge (leafN (π.push b))
  rw [V_leaf LV (by rw [ByteArray.size_push]; omega) (by rw [ByteArray.size_push]; omega)
    (by rw [tagWord_push (by omega), ht]), leafProg_size LV (by rw [ByteArray.size_push]; omega)]

/-- **`C`**: the last byte removed from a clear leaf is rejected. -/
theorem canary_C_pop {π : Proof} (hs : π.size = 48) (ht : tagWord π = 0) (vk c' : Digest) :
    V LV vk c' (dropLast π) = .ret false := by
  have h80 := LV.size_ge (leafN (dropLast π))
  rw [V_leaf LV (by rw [size_dropLast]; omega) (by rw [size_dropLast]; omega)
    (by rw [tagWord_dropLast (by omega), ht]), leafProg_size LV (by rw [size_dropLast]; omega)]

theorem push_eq_append (π : Proof) (b : UInt8) : π.push b = π ++ ⟨#[b]⟩ :=
  ByteArray.ext_toList (by simp [ByteArray.push, ByteArray.data_append])

/-- **`N`**: one byte appended to a plain node is rejected (it reads as a bundle with one byte
of `T`, which no bundle has). -/
theorem canary_N_push {c₁ c₂ : Digest} {p₁ p₂ : Signed} (hf : (Wit.node c₁ c₂ p₁ p₂).Fits)
    (b : UInt8) (vk c' : Digest) :
    V LV vk c' ((encode (.node c₁ c₂ p₁ p₂)).push b) = .ret false := by
  rw [push_eq_append]
  refine V_bundle_reject LV hf (isStrictPrefix_append (by simp [ByteArray.size])) fun l₁ l₂ _ _ =>
    bundleOK_size LV ?_
  rw [ByteArray.size_extract, ByteArray.size_append]
  have := bundleBytes_ne_one LV (l₁ ++ l₂)
  simp only [show ByteArray.size ⟨#[b]⟩ = 1 from rfl]
  omega

/-- **`N`**: the last byte removed from a plain node is rejected. -/
theorem canary_N_pop {c₁ c₂ : Digest} {p₁ p₂ : Signed} (hf : (Wit.node c₁ c₂ p₁ p₂).Fits)
    (vk c' : Digest) : V LV vk c' (dropLast (encode (.node c₁ c₂ p₁ p₂))) = .ret false := by
  set π := encode (.node c₁ c₂ p₁ p₂) with hπ
  have he8 := size_encode_node c₁ c₂ p₁ p₂
  have hsz := size_dropLast π
  by_cases hsmall : (dropLast π).size < 8
  · exact V_short LV hsmall
  have ht : tagWord (dropLast π) ≠ 0 := by
    rw [tagWord_dropLast (by omega), hπ, tagWord_encode_node]; decide
  rw [V_tag LV (by omega) ht]
  split
  · rename_i d₁ d₂ q₁ q₂ hd
    have hne : encodeF (.node d₁ d₂ q₁ q₂) ≠ dropLast π := by
      intro h
      have h1 : (encode (.node d₁ d₂ q₁ q₂)).size = π.size - 1 := by rw [← encodeF_eq, h, hsz]
      have h2 := size_encode (.node d₁ d₂ q₁ q₂)
      have h3 := size_encode (.node c₁ c₂ p₁ p₂)
      rw [← hπ] at h3
      omega
    rw [ite_eq_right hne, bundleProg]
    by_cases hpre : IsStrictPrefix (encodeF (.node d₁ d₂ q₁ q₂)) (dropLast π)
    · rw [ite_eq_left hpre]
      split
      · rename_i l₁ l₂ h₁ h₂
        dsimp only
        rw [ite_eq_right]
        intro hok
        have hf' := fits_of_bundleOK LV h₁ h₂ hok
        rw [encodeF_eq] at hpre
        have hdec : decode π = some (.node d₁ d₂ q₁ q₂) := by
          refine decode_of_extract hf' ?_
          rw [← extract_dropLast (by have := hpre.1; omega), hpre.2]
        have hsame : Wit.node d₁ d₂ q₁ q₂ = Wit.node c₁ c₂ p₁ p₂ := by
          rw [hπ, decode_encode _ hf] at hdec; exact (Option.some.inj hdec).symm
        have hlt := hpre.1
        rw [hsame, ← hπ, hsz] at hlt
        omega
      · rfl
    · rw [ite_eq_right hpre]
  · rfl

/-- What an accepted bundle passed: the strict prefix, the clear tree, the static checks. -/
theorem bundle_accepted {vk c c₁ c₂ : Digest} {p₁ p₂ : Signed} {π : Proof} {tr : Trace}
    (h : (bundleProg LV vk c π c₁ c₂ p₁ p₂).runSeq tr = some true) :
    IsStrictPrefix (encode (.node c₁ c₂ p₁ p₂)) π ∧ ∃ l₁ l₂,
      clearLeaves p₁.σ c₁ p₁ = some l₁ ∧ clearLeaves p₁.σ c₂ p₂ = some l₂ ∧
        bundleOK LV vk c c₁ c₂ p₁.σ (l₁ ++ l₂)
          (π.extract (encode (.node c₁ c₂ p₁ p₂)).size π.size) = true := by
  rw [bundleProg] at h
  split_ifs at h with hpre
  · split at h
    · rename_i l₁ l₂ h₁ h₂
      dsimp only at h
      split_ifs at h with hok
      · rw [encodeF_eq] at hpre hok
        exact ⟨hpre, l₁, l₂, h₁, h₂, hok⟩
      · exact absurd h (ret_false_rejects tr)
    · exact absurd h (ret_false_rejects tr)
  · exact absurd h (ret_false_rejects tr)

/-- **`B`**: one byte appended to an accepted bundle is rejected (`|T|` is one too many). -/
theorem canary_B_push {vk c c₁ c₂ : Digest} {p₁ p₂ : Signed} {π : Proof} {tr : Trace}
    (h : (bundleProg LV vk c π c₁ c₂ p₁ p₂).runSeq tr = some true) (b : UInt8) (c' : Digest) :
    V LV vk c' (π.push b) = .ret false := by
  obtain ⟨hpre, l₁, l₂, h₁, h₂, hok⟩ := bundle_accepted LV h
  have hlt := hpre.1
  have hf := fits_of_bundleOK LV h₁ h₂ hok
  have hT := ((bundleOK_iff LV).mp hok).2.1
  rw [ByteArray.size_extract] at hT
  refine V_bundle_reject LV hf ⟨by rw [ByteArray.size_push]; omega,
    by rw [extract_push (by omega), hpre.2]⟩ fun l₁' l₂' h₁' h₂' => bundleOK_size LV ?_
  rw [h₁] at h₁'; rw [h₂] at h₂'; cases h₁'; cases h₂'
  rw [ByteArray.size_extract, ByteArray.size_push]
  omega

/-- **`B`**: the last byte removed from an accepted bundle is rejected (`|T|` is one too few). -/
theorem canary_B_pop {vk c c₁ c₂ : Digest} {p₁ p₂ : Signed} {π : Proof} {tr : Trace}
    (h : (bundleProg LV vk c π c₁ c₂ p₁ p₂).runSeq tr = some true) (c' : Digest) :
    V LV vk c' (dropLast π) = .ret false := by
  obtain ⟨hpre, l₁, l₂, h₁, h₂, hok⟩ := bundle_accepted LV h
  have hlt := hpre.1
  have hf := fits_of_bundleOK LV h₁ h₂ hok
  have hT := ((bundleOK_iff LV).mp hok).2.1
  rw [ByteArray.size_extract] at hT
  have h32 : 32 ≤ bundleBytes LV (l₁ ++ l₂) := by
    cases hl : l₁ ++ l₂ with
    | nil => rw [hl, show bundleBytes LV [] = 0 from rfl] at hT; omega
    | cons x ls => rw [bundleBytes_cons]; omega
  refine V_bundle_reject LV hf ⟨by rw [size_dropLast]; omega,
    by rw [extract_dropLast (by omega), hpre.2]⟩ fun l₁' l₂' h₁' h₂' => bundleOK_size LV ?_
  rw [h₁] at h₁'; rw [h₂] at h₂'; cases h₁'; cases h₂'
  rw [ByteArray.size_extract, size_dropLast]
  omega

/-! ## The claim (`claim.json`) -/

/-- The claim of `claim.json` as a `Declared` literal (the rendered challenge's `declared`). -/
noncomputable def claimR1 : Declared where
  ε := ((1 : ℝ≥0) / 680564733841876926926749214863536422912)
  δ := ((0 : ℝ≥0) / 1)
  qV := 65536
  fuel t := 0 + 8 * t

/-- **Positive**: the claim of `claim.json` is certified. -/
theorem certificateR_claim : CertificateR claimR1 submission :=
  certificateR_of facts claimR1 εR1_le_declared (show qVR1 ≤ 65536 by decide)
    fun t => ⟨show 8 * t ≤ 0 + 8 * t by omega, show 0 + 8 * t ≤ 2 ^ 48 + 2 ^ 16 * t by omega⟩

/-- **Negative**: a claim declaring `ε = 2^-130` (below the proved `2^-129`), the query bound
`2^16 − 1`, or the fuel `7 t` is not certified. -/
theorem claim_negatives :
    ¬ CertificateR { claimR1 with ε := (2 : ℝ≥0)⁻¹ ^ 130 } submission ∧
    ¬ CertificateR { claimR1 with qV := 65535 } submission ∧
    ¬ CertificateR { claimR1 with fuel := fun t => 7 * t } submission := by
  refine ⟨fun h => ?_, fun h => ?_, fun h => ?_⟩
  · have h1 : εR1 ≤ (2 : ℝ≥0)⁻¹ ^ 130 := h.bounds.1
    rw [εR1_eq] at h1
    have : ((2 : ℝ≥0)⁻¹ ^ 130 : ℝ≥0) < (2 : ℝ≥0)⁻¹ ^ 129 :=
      pow_lt_pow_right_of_lt_one₀ (by norm_num) (by norm_num) (by norm_num)
    exact absurd h1 (not_le.mpr this)
  · exact absurd (h.bounds.2.2.1 : qVR1 ≤ 65535) (by decide)
  · exact absurd ((h.bounds.2.2.2 1).1 : 8 * 1 ≤ 7 * 1) (by decide)

/-! ## The zero-step leaf, as `L` and as `C` (no query) -/

/-- **Positive (`L`)**: the 80-byte zero-step leaf proof is accepted under its statement with no
query, for every leaf verifier whose `leafSize 0` is 80. -/
theorem zeroLeaf_accepted (h0 : LV.size 0 = 80) (vk : Digest) :
    V LV vk ctlStmt zeroLeaf = .ret true := by
  obtain ⟨hs, ht, hn, hS, hH⟩ := zeroLeaf_parse
  have hh : leafHeaderOK LV ctlStmt zeroLeaf = true :=
    (leafHeaderOK_iff LV).mpr ⟨by rw [hn]; exact Nat.zero_le _, by rw [hs, hn, h0], by rw [hH, hn]⟩
  rw [V_leaf LV (by omega) (by omega) ht, leafProg, ite_eq_left hh, ite_eq_left hn]
  simp [hS, hH]

/-- **Negative (`L`)**: under any other statement, the zero-step leaf proof is rejected. -/
theorem zeroLeaf_other_stmt {c' : Digest} (hc : c' ≠ ctlStmt) (vk : Digest) :
    V LV vk c' zeroLeaf = .ret false := by
  obtain ⟨hs, ht, hn, hS, hH⟩ := zeroLeaf_parse
  rw [V_leaf LV (by omega) (by omega) ht, leafProg, ite_eq_right]
  intro hh
  exact hc (by rw [((leafHeaderOK_iff LV).mp hh).2.2, hH, hn])

/-- **Negative (`L`)**: the zero-step leaf proof with a byte appended or removed is rejected. -/
theorem zeroLeaf_canaries (h0 : LV.size 0 = 80) (vk : Digest) (b : UInt8) (c' : Digest) :
    V LV vk c' (zeroLeaf.push b) = .ret false ∧ V LV vk c' (dropLast zeroLeaf) = .ret false := by
  have hacc : (V LV vk ctlStmt zeroLeaf).runSeq [] = some true := by
    rw [zeroLeaf_accepted LV h0]; rfl
  obtain ⟨hs, ht, -⟩ := zeroLeaf_parse
  exact ⟨canary_L_push LV hacc ht (by omega) b c', canary_L_pop LV hacc ht (by omega) c'⟩

/-- **Positive (`C`)**: the clear leaf of the zero-step chain is accepted with no query. -/
theorem zeroClear_accepted (vk : Digest) :
    V LV vk ctlStmt (encode (.leaf ctlStart 0)) = .ret true := by
  obtain ⟨hS, hN⟩ := leaf_parts ctlStart (show 0 < 2 ^ 64 by norm_num)
  rw [V_clear LV (size_encode_leaf _ _) (tagWord_encode_leaf _ _)]
  simp [clearLeafOK, hS, hN, leafStmtF_eq, chainEndF_eq, ctlStmt, chainEnd]

/-- **Negative (`C`, D-6)**: the clear leaf of a chain of `2^12 + 1 = 4097` steps is rejected
before any hash, under every key and statement. -/
theorem clear_overCap (s : Digest) (vk c : Digest) :
    V LV vk c (encode (.leaf s 4097)) = .ret false := by
  obtain ⟨-, hN⟩ := leaf_parts s (show 4097 < 2 ^ 64 by norm_num)
  rw [V_clear LV (size_encode_leaf _ _) (tagWord_encode_leaf _ _),
    clearLeafOK_cap (by rw [hN]; unfold clearCap; norm_num)]

/-- **Negative (`B`, D-6)**: a bundle whose clear tree holds a leaf of `4097` steps is rejected
with no query, under the reference key, whatever its `T` (the clear tree is otherwise
well-formed: `σ0`-signed, empty traces). -/
theorem bundle_overCap (sk : ℕ → ℕ → Digest) (s₁ s₂ : Digest) {n₂ : ℕ} (h₂ : n₂ < 2 ^ 64)
    (T : ByteArray) (hT : 0 < T.size) (c : Digest) :
    V LV (Signer.pk sk) c (encode (clearTree sk s₁ 4097 s₂ n₂) ++ T) = .ret false := by
  have hfit : (clearTree sk s₁ 4097 s₂ n₂).Fits :=
    ⟨clearSlot_fits sk s₁ 4097, clearSlot_fits sk s₂ n₂⟩
  unfold clearTree at hfit ⊢
  refine V_bundle_reject LV hfit (isStrictPrefix_append hT) fun l₁ l₂ h₁ _ => ?_
  rw [show (clearSlot sk s₁ 4097).σ = σ0 sk from rfl,
    clearLeaves_clearSlot sk s₁ (by norm_num)] at h₁
  cases h₁
  exact bundleOK_cap LV (List.mem_append_left _ (List.mem_singleton_self _))
    (by unfold clearCap; norm_num)

end SpartanSrom.NodeControls
