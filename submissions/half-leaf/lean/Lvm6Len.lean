-- New for lvm6 (WP LEN, F-X8b-1): `Len6` proved. An accepted `S` proof of the composed scheme
-- `schemeOf (prog6 Φ) P17` has `pz6` bytes, for phases that follow the schedule and whose opening's
-- queries open `t_i` positions (the deployed opening does: `qlen_whirP`).
import Lvm6LenP18
import Lvm6XCorrect

/-!
# `Len6` (LEN)

* **`qlen_prog6`**: the composed program's queries open `tPD i` positions, given the phases'
  `Follows` facts (§6.1–§6.5 have no opening: `noOpn_parts`) and the opening's `QLen`.
* **`len6`**: `Len6 Φ` from `PhasesFollow Φ P17` and the opening's `QLen` (`trun_len` on the replay
  of the accepting run, `opB_P`, `piLen_P17`); **`len6_whirAt`** for the deployed opening.
* **`open6XL`**: X8b's `open6X` with `Len6` discharged (phases with the deployed opening).
-/

set_option autoImplicit false

namespace Lvm6

open RecursionFast LeanVM.Protocol.Compile Lvm.FS

section Prog

variable {Φ : Phases}

/-- **The composed program's queries open `tPD i` positions.** -/
theorem qlen_prog6 (hF : PhasesFollow Φ P17) (hW : ∀ cl, QLen tPD (Φ.whir P17 cl)) (vk : Digest)
    (x : List UInt8) : QLen tPD (prog6 Φ P17 vk x) := by
  obtain ⟨n1, n2, n3, n4, n5⟩ := noOpn_parts
  unfold prog6 rest6 batchJ
  exact QLen.bind' (qlen_of_follows hF.commit (noOpn_of _ n1)) fun _ ↦
    QLen.bind' (qlen_of_follows (hF.tree _) (noOpn_of _ n2)) fun _ ↦
    QLen.bind' (qlen_of_follows (hF.sponge _) (noOpn_of _ n3)) fun _ ↦
    QLen.bind' (qlen_of_follows (hF.typed _) (noOpn_of _ n4)) fun _ ↦
    QLen.bind' (QLen.bind' (qlen_of_follows (follows_require _) (noOpn_of [] rfl)) fun _ ↦
      qlen_of_follows (hF.ring _ _) (noOpn_of _ n5)) fun _ ↦ hW _

/-- **`Len6`**: an accepted `S` proof of `schemeOf (prog6 Φ) P17` has `pz6` bytes, when the phases
follow the schedule and the opening's queries open `tPD i` positions. -/
theorem len6 (hF : PhasesFollow Φ P17) (hW : ∀ cl, QLen tPD (Φ.whir P17 cl)) : X.Len6 Φ := by
  intro vk c π L _ hacc
  set S := schemeOf (prog6 Φ) P17 vk with hS
  rw [Scheme.runLog_V] at hacc
  rcases hx : S.hdr π with _ | ⟨x, body⟩
  · rw [hx] at hacc; simp at hacc
  · rw [hx] at hacc
    simp only at hacc
    split at hacc
    · simp only [Option.bind_eq_some_iff, Option.map_eq_some_iff] at hacc
      obtain ⟨e₀, -, e₁, -, ⟨b, h'⟩, hr, hb⟩ := hacc
      simp only at hb
      subst hb
      have hlen := Len.trun_len S L tPD (prog6 Φ P17 vk x) (opsOf P17.levs (sched6 P17))
        (V.widths (sched6 P17)) e₁.2 [] [] body [] h' (prog6_sched Φ hF vk x)
        (qlen_prog6 hF hW vk x) (fun k ↦ by rw [nReads_nil, Nat.zero_add]; rfl) hr
      have hB : body.length = bodyLen P17 := by rw [hlen]; exact opB_P
      have hx' : V.hdr6 (toV P17) π = some (x, body) := hx
      unfold V.hdr6 at hx'
      split at hx'
      · rename_i hle
        try simp only [Option.some.injEq, Prod.mk.injEq] at hx'
        obtain ⟨-, rfl⟩ := hx'
        rw [List.length_drop, Array.length_toList] at hB
        have hp : piLenOf P17 = 230424 := piLen_P17
        have hsz : π.size = π.data.size := rfl
        show π.size = 230424
        unfold piLenOf at hp
        have h1 : V.hdrLen (toV P17) = hdrLen P17 := rfl
        rw [h1] at hle hB
        omega
      · simp at hx'
    · simp at hacc

/-- **`Len6` for the deployed opening.** -/
theorem len6_whirAt (hF : PhasesFollow Φ P17) (hw : Φ.whir = whirAt Whir.whirP) : X.Len6 Φ :=
  len6 hF fun cl ↦ by
    rw [hw]
    show QLen tPD (if openKey P17 = true then Whir.whirP cl else .fail)
    rw [openKey_P17]
    exact Whir.qlen_whirP cl

end Prog

namespace X

open Lvm Lvm.X Lvm.T
open LeanVM.Parameters (E2)
open scoped NNReal ENNReal

section Assembly

variable {Φ : Phases} {SGood TGood : Hdr → Stack → Prop} (H : PhaseSpecs Φ Whir.I6 SGood TGood)
  (HG : Stmt.openGoodC Whir.GWDc Φ.whir) (hF : PhasesFollow Φ P17) {VS : Shape → SProg}
  (Xe : ∀ vk, Ext6 (schemeOf (prog6 Φ) P17 vk) (Rel (accV (VS P17) vk)) (G6 SGood TGood))

include H HG hF in
/-- **X8b's `open6X` with `Len6` discharged** (`len6_whirAt`), for phases with the deployed opening. -/
theorem open6XL (hw : Φ.whir = whirAt Whir.whirP) {Lv : ℕ → LevelX} {fin : XIR}
    (hX : ∀ vk, (Xe vk).ext = ExtSpec6 (Whir.I6 P17)) (hD : DescProg6 Φ (descX6 Lv fin))
    (hL : ∀ i < 5, LevelOk i (Lv i)) (hf : PartOk fin finCap) (hS : ∀ i < 5, LevelSz i (Lv i))
    (hfs : sizeIR fin ≤ finSz) :
    (∀ vk, ∃ K : KCert (schemeOf (prog6 Φ) P17 vk) (Rel (accV (VS P17) vk)),
      Scheme.εFS K ≤ (2 : ℝ≥0)⁻¹ ^ 128 ∧ ExtEq6 (EX6 (descX6 Lv fin)) K) ∧
    (∀ c π L, isS π = false → EX6 (descX6 Lv fin) c π L = RecursionFast.WitnessSending.decode π) ∧
    Computes (extX6 (descX6 Lv fin)) (EX6 (descX6 Lv fin)) fuel6 ∧
    (extX6 (descX6 Lv fin)).body.size ≤ progCap :=
  open6X H HG hF Xe hX (len6_whirAt hF hw) hD hL hf hS hfs

end Assembly

end X

end Lvm6
