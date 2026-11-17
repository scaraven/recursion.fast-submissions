-- New for lvm2 MP-B cap pruning (CAP-X, 2026-11-17): S2GB's extractor and its statements (lead D-V1, D-X1, D-X2).
-- DAY-0 STATEMENTS: every `sorry` is tagged `-- CAP-FRZ X`. A proof never changes its statement; a needed change goes
-- to the lead old → new.
import LvmS2GBExtProg
import LvmS2GBExtOK
import LvmS2GBExtNode
import LvmS2GBExtGen

/-!
# S2GB's extractor

E reads the real proof π (its size in `SzB`: the static part and the tail), the specification scheme reads the expanded
proof `fillB P20B π w` (V's `LvmS2GBFill`); E never computes `w`.

* **The program** `extXB20`: the parse checks `SzB` (`extIRWithB`); the node branch `nodeB20` indexes the log, scans
  the chain, reads `C_main`'s three words by walking from the **sent caps** (`2^c` nodes, `h − c` levels: 18 / 16 / 13),
  copies the fold challenges and the residual, decodes, and outputs the node witness whose left child is
  `childB20` (static part `‖` tail); every log access computes the log position from `|π|` (`LvmS2GBExtDyn`).
* **`EXB20 A`**: the program's denotation on `InDomE`, `EoutXB20 A` outside.
* **`kcertSMWBτ`**, **`kcertSFWBτ`**: `kcertSMWSτ`/`kcertSFWSτ` over `schemeSWB` (`kcertOfInv` reads only `S.P`,
  `S.ok`).
* Statements: **`computesXB20`**, **`extXB20_size`**, **`EXB20_Wn`** (bundled as `extB20 VS : ExtF20`), and
  **`ext_eqB_gen`**: on proofs in `SzB` whose expansion by any `w` the scheme accepts, E decodes or is the scheme's
  extractor on the expansion.
-/

set_option autoImplicit false

namespace Lvm.XB

open RecursionFast Lvm Lvm.X Lvm.XS Lvm.Replay

/-! ## The executable side -/

/-- **CAP-FRZ X**: S2GB's extractor computes its specification within the declared fuel. -/
theorem computesXB20 (A : Digest → Digest → Signed → Bool) : Computes extXB20 (EXB20 A) fuel :=
  fun c π L h1 h2 h3 => by
    obtain ⟨o, ho', hl, hd⟩ := computesWithB decOk_decXB20 c π L h1 h2 h3
    exact ⟨o, ho', hl, hd.trans (if_pos ⟨h1, h2, h3⟩).symm⟩

/-- **CAP-FRZ X**: the program within `progCap`. -/
theorem extXB20_size : extXB20.body.size ≤ progCap :=
  size_extWithB decOk_decXB20.size

/-- **CAP-FRZ X**: witness-sending proofs decode. -/
theorem EXB20_Wn (A : Digest → Digest → Signed → Bool) (c : Digest) (π : Proof) (L : Log)
    (h : Lvm.T.isS π = false) : EXB20 A c π L = WitnessSending.decode π := by
  have hW : π.data[0]? ≠ some 0x53 := fun h0 ↦ by
    have : π.data.getD 0 0 = 0x53 := by rw [Array.getD_eq_getD_getElem?, h0]; rfl
    simp [Lvm.T.isS, this, Lvm.T.sByte] at h
  by_cases hD : InDomE c π L
  · rw [EXB20, if_pos hD, EdXB20]
    have hπ : π.size < 2 ^ 64 := by have := hD.1; rw [outCap] at this; (clear * - π this; omega)
    have hrun := run_W_tapeB decOk_decXB20 (by show 0 < piStatic P20B; rw [sizes_P20B.1.1]; norm_num) (extractorInput c π L) π.size hπ
      (by rw [getD_toArray, tape_getD4]) (tape_length c π L) (fun hne he => by
        obtain ⟨b, hb⟩ : ∃ b, π.data[0]? = some b := by
          rcases h : π.data[0]? with _ | b
          · rw [Array.getElem?_eq_none_iff] at h; exact (hne (Nat.le_zero.mp h)).elim
          · exact ⟨b, rfl⟩
        have h1 := tape_byte0 c π L hb
        have h2 := congrArg BitVec.toNat he
        rw [lowByte, getD_toArray, h1] at h2
        exact hW (by rw [hb]; congr 1; exact UInt8.toNat_inj.mp h2))
    rw [Eden, ← den_of_run (by simp only [regs, memM]; norm_num) (wf_extIRWithB decOk_decXB20.wf) hrun,
      WitnessSending.decode]
    congr 1
    refine List.ext_getElem (by
      simp only [List.length_map, List.length_range, packBytes_length]
      rw [WitnessSending.size_eq_length]) fun j _ h2 => ?_
    simp only [List.getElem_map, List.getElem_range, getD_toArray]
    exact tape_getD_proof c π L (by rwa [packBytes_length, ← WitnessSending.size_eq_length] at h2)
  · rw [EXB20, if_neg hD, EoutXB20, if_neg hW]

end Lvm.XB

namespace Lvm.CT

open RecursionFast Lvm Lvm.T Lvm.XB

/-- **S2GB's executable extractor** for a verifier `VS`. -/
def extB20 (VS : SProg) : ExtF20 :=
  ⟨EXB20 (accV VS), extXB20, computesXB20 _, extXB20_size, EXB20_Wn _⟩

end Lvm.CT

namespace Lvm.XB

open RecursionFast Lvm Lvm.X Lvm.XS Lvm.FS Lvm.T Lvm.ASM Lvm.CT Lvm.E2F
open LeanVM.Protocol LeanVM.Protocol.Verifier
open LeanVM.Protocol.Compile hiding Proof Bytes
open scoped NNReal ENNReal

/-- **CAP-FRZ X**: **O5c at S2GB**, generic in the middle phases: on proofs in `SzB` whose expansion
`fillB P20B π w` (any `w`) `schemeSWB fmtB20` accepts over a log of `μ < 1`, `EXB20` decodes a witness of the relation,
or is the scheme's extractor on the expansion; the left child is `childB20` (static part `‖` tail), the right leaf
signs with `sigLeafS20` of the window. -/
theorem ext_eqB_gen {mid : List UInt8 → VerifierProgram (List LeanVM.Protocol.Verifier.StackClaim)} {Good : GoodRelM}
    {Lm τ : ℝ≥0∞} (hmid : MidSpecMτ mid Good εS Lm τ) (hτ : leadOpenM ≤ τ) (hLm : Lm ≤ εS) (hsh : MidShapeM mid)
    {VS : SProg} (hnode : ∀ vk, NodeSoundMLS loU VS vk Good childB20 sigLeafS20)
    (hfol : MidFollowsS (midItemsS stB20) mid)
    (hA : ∀ vk c p, accV VS vk c p = true → Lvm.X.SFits p) (vk : RecursionFast.Digest) (L : Log)
    (c : RecursionFast.Digest) (π : RecursionFast.Proof) (w : List UInt8) (hsz : SzB π)
    (hμ : Scheme.μ (kcertSMWBτ fmtB20 hmid hτ hLm hsh (extJMLS loU loU_le hsh (hnode vk))) L < 1)
    (hacc : ((schemeSWB fmtB20 vk (PSWithM mid)).V c (fillB P20B π w)).runLog L = some true) :
    (∃ wt, EXB20 (accV VS) c π L = some wt ∧ Rel (accV VS vk) c wt) ∨
      EXB20 (accV VS) c π L =
        (schemeSWB fmtB20 vk (PSWithM mid)).Ex (kcertSMWBτ fmtB20 hmid hτ hLm hsh (extJMLS loU loU_le hsh (hnode vk))).ext
          c (fillB P20B π w) L :=
  ext_eqB_genG stB20 fmtB20 fmtOKB_stB20 replayOKB_stB20 hmid hτ hLm hsh loU loU_le
    (fun π x hn => loU_eqB π x hn) hnode (fun π x out hn _ => childWB_streamB20 π x out hn)
    (fun π x out hn _ => sigLeaf_streamB20 π x out hn) hfol hA vk L c π w (EXB20 (accV VS) c π L)
    (by have h := hsz.1; rw [show piStatic P20B = 269336 from sizes_P20B.1.1] at h; exact h)
    (fun hb h0 => EXB_leaf _ c π L hsz h0 hb)
    (fun hD h0 hb => EXB_node_out _ c π L hD hsz h0 hb)
    (fun hD h0 hb hS αk hα wd₀ wd₁ wd₂ hw₀ hw₁ hw₂ α₀ α₁ α₂ ha₀ ha₁ ha₂ f₂ hf₂ m₂ hd₂ m₁ hd₁ out hd₀ =>
      EXB_node _ c π L hD hsz h0 hb hS αk hα wd₀ wd₁ wd₂ hw₀ hw₁ hw₂ α₀ α₁ α₂ ha₀ ha₁ ha₂ f₂ hf₂ m₂ hd₂ m₁ hd₁ out hd₀)
    hμ hacc rfl

end Lvm.XB
