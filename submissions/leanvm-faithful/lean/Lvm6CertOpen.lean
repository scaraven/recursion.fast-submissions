-- lvm6 C4 (CERT-plan §1 link 9, §2 C4): `Open6D`, the obligations of `Open6` with `sound` in season 1's
-- disjunctive form (`LvmCertSGen.SSound`: on an available log the extractor gives a witness, or it is the ideal
-- extractor), and `certified_ofD`, the certificate against `declared6` from them. `Lvm6Stmt` is untouched.
import Lvm6Stmt

/-!
# `Open6D` and `certified_ofD`

`ExtEq6 EX K` asks `EX = Eideal K` on **every** available log. The contract's `Computes` only covers logs whose
entries are below `2^64` bytes and whose tape is at most `2^64` words, while `Avail` bounds a log only by
`logCap` entries; so an extractor whose `S` branch is the program's denotation can meet `ExtEq6` only on the
domain. Season 1 (`SSound`) and A0 (`Lvm6WOnly.EW`) split the extractor at the domain; this module states the
matching obligation.

* **`ExtEqD EX K`**: on every available log, `EX` returns a witness of the relation, or agrees with `Eideal K`.
  `ExtEq6.toD`: `ExtEq6` is the special case.
* **`XOpen6D`**: the extractor's four obligations (`sound` with `ExtEqD`, `wBranch`, `computes`, `size`).
* **`Open6D`**: `XOpen6D` at `VS P18` plus `queries` and `refines`, as in `Open6`. `Open6.toD`: `Open6` gives it.
* **`certified_ofD`**: `Open6D` gives `CertificateR declared6 (submissionOf (VS P18) EX extX)`; the proof is
  `certified_of`'s, with the witness case of `KState.congr` taken from `ExtEqD`'s left disjunct.
-/

set_option autoImplicit false

namespace Lvm6

open RecursionFast Lvm.T LeanVM.Parameters
open RecursionFast.WitnessSending (decode)
open LeanVM.Protocol.Compile hiding Proof Bytes Word
open scoped NNReal

section Ext

variable {S : Lvm.FS.Scheme} {R : Digest → Wit → Prop}

/-- **`ext_eq6`, disjunctive form** (season 1's `SSound`): on every available log the extractor returns a
witness of the relation, or it is the ideal extractor. -/
def ExtEqD (EX : Digest → Proof → Log → Option Wit) (K : Lvm.FS.KCert S R) : Prop :=
  ∀ c π L, Avail K c π L → (∃ w, EX c π L = some w ∧ R c w) ∨ EX c π L = Eideal K c π L

/-- `ExtEq6` is the case of `ExtEqD` without witnesses. -/
theorem ExtEq6.toD {EX : Digest → Proof → Log → Option Wit} {K : Lvm.FS.KCert S R} (h : ExtEq6 EX K) :
    ExtEqD EX K :=
  fun c π L hA => .inr (h c π L hA)

end Ext

/-- **The extractor's obligations** under the `S` branch `VS` (`Open6`'s `sound`, `wBranch`, `computes`, `size`,
with `sound` in the form `ExtEqD`). -/
structure XOpen6D (VS : SProg) (prog : Shape → Digest → List UInt8 → VerifierProgram Bool)
    (EX : Digest → Proof → Log → Option Wit) (extX : XProg) : Prop where
  /-- `kcert6`, `εFS_kcert6` and `ext_eq6` in the disjunctive form. -/
  sound : ∀ vk, ∃ K : Lvm.FS.KCert (schemeOf prog P18 vk) (Rel (accV VS vk)),
    Lvm.FS.Scheme.εFS K ≤ (2 : ℝ≥0)⁻¹ ^ 128 ∧ ExtEqD EX K
  /-- The extractor decodes `W` proofs. -/
  wBranch : ∀ c π L, isS π = false → EX c π L = decode π
  /-- `computes6`. -/
  computes : Computes extX EX fuel6
  /-- The program within `progCap` statements. -/
  size : extX.body.size ≤ progCap

/-- **The six obligations of the certificate** at `P18`, `sound` in the form `ExtEqD`. -/
structure Open6D (VS : Shape → SProg) (prog : Shape → Digest → List UInt8 → VerifierProgram Bool)
    (EX : Digest → Proof → Log → Option Wit) (extX : XProg) : Prop
    extends XOpen6D (VS P18) prog EX extX where
  /-- `VS_queries` at `P18`. -/
  queries : ∀ vk c π (H : ByteArray → Digest), ((VS P18 vk c π).queries H).length ≤ P18.qS
  /-- `refines6` at `P18`. -/
  refines : Refines (VS P18) (schemeV (schemeOf prog P18))

/-- `Open6` gives `Open6D`. -/
theorem Open6.toD {VS : Shape → SProg} {prog : Shape → Digest → List UInt8 → VerifierProgram Bool}
    {EX : Digest → Proof → Log → Option Wit} {extX : XProg} (h : Open6 VS prog EX extX) :
    Open6D VS prog EX extX where
  sound vk := (h.sound vk).imp fun _ hK => ⟨hK.1, hK.2.toD⟩
  wBranch := h.wBranch
  computes := h.computes
  size := h.size
  queries := h.queries
  refines := h.refines

/-- **T9 assembly, disjunctive form**: the six obligations of `Open6D` give the certificate against
`declared6`. -/
theorem certified_ofD {VS : Shape → SProg}
    {prog : Shape → Digest → List UInt8 → VerifierProgram Bool}
    {EX : Digest → Proof → Log → Option Wit} {extX : XProg} (h : Open6D VS prog EX extX) :
    CertificateR declared6 (submissionOf (VS P18) EX extX) := by
  have hq : ∀ H vk c π, isS π = true → ((VS P18 vk c π).queries H).length ≤ qVlvm :=
    fun H vk c π _ => (h.queries vk c π H).trans (by decide)
  refine ⟨⟨fun vk => ?_, fun vk => ?_, h.computes, ?_⟩, ?_⟩
  · obtain ⟨K, hε, hE⟩ := h.sound vk
    rw [submissionOf_acc, submissionOf_ε]
    have k := (Lvm.FS.KState.congr (Lvm.FS.Scheme.kstate_of_kcert K)
      (V' := Vwith (VS P18) vk) (E' := EX) (by
        intro L c π hl hμ hacc
        cases hs : isS π
        · left
          obtain ⟨w, hw, hR⟩ := V_W_runLog (VS P18) vk c π hs hacc
          exact ⟨w, by rw [h.wBranch c π L hs, hw], hR⟩
        · rw [V_S (VS P18) vk c π hs] at hacc
          have hv := h.refines vk L c π hs hacc
          rcases hE c π L ⟨hs, hl, hμ, hv⟩ with hw | he
          · exact .inl hw
          · exact .inr ⟨hv, he⟩)).mono hε
    exact k.ks fun H c π => V_queries_le (VS P18) H (hq H) vk c π
  · rw [submissionOf_δ]; exact complete (VS P18) _ rfl rfl rfl vk
  · refine ⟨by rw [submissionOf_ε]; rfl, by rw [submissionOf_δ]; exact zero_le,
      show qVlvm ≤ 2 ^ 16 by decide, fun t => ?_, h.size⟩
    simp only [submissionOf, fuel6, extractorBudget]; omega
  · refine ⟨?_, by simp [submissionOf, declared6], le_rfl, fun t => ⟨le_of_eq ?_, ?_⟩⟩
    · simp only [submissionOf, declared6]; push_cast; norm_num
    · simp [submissionOf, declared6, fuel6]
    · simp only [declared6, extractorBudget]; omega

end Lvm6
