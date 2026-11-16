-- New for lvm2 E2-FT (E2F-C), E2AC-DES §6 statement 16 (`nodeF20`): the node soundness of the S2GF circuit
-- (`NodeSound` at stage S2GF), statement shape of roll 11's `nodeT20`.
import LvmE2QHarF

/-!
# `nodeF20`: `NodeSound` at S2GF

* **`staticOkBF20`**: the S2GF guard: QH3's `staticOkTF20` (it decides `QF20.twinsOk` and `cacheF20.okB`, review
  condition 1), QH6's `nodeChkBG` at S2GF's sponge blocks and `PUB` length, and `σ′`'s regions in the stream block
  `S` (`sigInSB`), the HAR's static checks `harChkBF20` (roll 11's `harChkB`), and the word `1`'s region
  (`oneOkB`, `THypX.ok`'s; roll 11's guard had it).
* **`SFF20`**: the guard's facts, `NodeGF frzF20 QF20 layF20 NTF20 ∧ harChkBF20 = true ∧ oneOkB layF20 = true`;
  every field comes from `staticOkBF20 = true` (`sfF20`), so no fact of the circuit reaches the certificate as a hypothesis.
* **`nodeF20`** (statement 16): on stream-block pairs (`SBlk`) of the S2GF good relation `GoodTF TiF20 H`
  (`GbTX ∧ GkF`, E2F-V), a statement the header check accepts gives the relation for the witness whose left child is
  `childSP P20F qr` (the child read with S2GF's schedule), for S2GF's verifier `VSFX NTF20`. Proof: QH6's
  `nodeSoundFG` (roll 11's `nodeSoundTG` at S2GF, every hypothesis but Q_arith's discharged from `S` and `H`) with
  `harithF20` (`LvmE2QHarF`).
-/

set_option autoImplicit false

namespace Lvm.E2Q

open RecursionFast Lvm Lvm.ASM Lvm.Typed

/-- **The S2GF guard.** -/
def staticOkBF20 : Bool :=
  staticOkTF20 && Lvm.QTyped.nodeChkBG (spongeBlocks P20F) (pubLanesX accVF) cfgF20 frzF20 QF20 layF20 NTF20 &&
    Lvm.TypedV.sigInSB NTF20 && harChkBF20 && Lvm.T.oneOkB layF20

/-- **The S2GF guard's facts.** -/
abbrev SFF20 : Prop := NodeGF frzF20 QF20 layF20 NTF20 ∧ harChkBF20 = true ∧ Lvm.T.oneOkB layF20 = true

/-- **The guard's facts** from `staticOkBF20 = true`. -/
theorem sfF20 (h : staticOkBF20 = true) : SFF20 := by
  simp only [staticOkBF20, Bool.and_eq_true] at h
  exact ⟨nodeGF_of QF20_eq rfl rfl rfl h.1.1.1.1 h.1.1.1.2 h.1.1.2, h.1.2, h.2⟩

/-- **Statement 16 (`nodeF20`)**: `NodeSound` of the S2GF circuit for `VSFX NTF20`, on stream-block pairs of the
S2GF good relation, with the left child read at `P20F` (roll 11's `nodeT20` shape). -/
theorem nodeF20 (S : SFF20) (H : THypX TiF20) (vk : RecursionFast.Digest) :
    NodeSound (Lvm.E2V.VSFX NTF20) vk (fun x qm qr ↦ Lvm.E2V.GoodTF TiF20 H x qm qr ∧ Lvm.NS.SBlk qm qr)
      (Lvm.NS.childSP P20F) :=
  nodeSoundFG (F := frzF20) (Q := QF20) (tl := layF20) (N := NTF20) S.1 H vk NTF20 qaF20 QF20_qa
    (harithF20 S.1 S.2.1 H vk)

end Lvm.E2Q
