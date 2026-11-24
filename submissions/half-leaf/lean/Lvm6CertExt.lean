-- New for lvm6 (WP C5, CERT-plan link 10): the extractor's obligations `Ext6` for `kcertAsmG`, with no luck
-- (`BL := False`) and the extraction map `ExtSpec6 (I6 P17)`, from the node theorem (link 11) and the reader
-- equalities (link 12).
import Lvm6CertRead
import Lvm6NodeAsm
import Lvm6XCorrect
import Lvm6VHdr
import Lvm6CertPhasesX

/-!
# `Xe`: the extractor's obligations (WP C5)

`open6XD` takes `Xe : ∀ vk, Ext6 (schemeOf (prog6 Φ) P17 vk) (Rel (accV (VS P17) vk)) (G6 SGood TGood)` and
`hX : ∀ vk, (Xe vk).ext = ExtSpec6 (I6 P17)`. This module builds `Xe`, so that `hX` is `rfl`.

* **No luck**: `BL := False`. Every rule about luck holds, and `esc` of the invariant `¬ False` is `0`
  (`esc_of_forall`). `extract` then has to hold on **every** accepting history whose `G6` holds.
* **`extract6`**: `G6` gives a pinned history with a candidate `q` good for the header's view (`GoodAll`); the
  extraction map's stack `pick6 (I6 P17) h` is `q` (`pick6_eq`); the scheme's header check gives the view's
  well-formedness, statement and key (`hdrView_ok`); `extSpec6_eq` puts `ExtSpec6` in the node theorem's readers;
  the node theorem `node6V` gives the relation.
* **`hdrView_ok`**: `Stmt.hdrView_okV` without its length premise. The scheme's `ok c x` is the header check on
  the bytes `x` alone (`scheme6V`), and the length of `x` is not in it; `hdrView_okV`'s proof does not use it.
* **`XeOf`**: `Xe` for any phases `Φ`, branch `VS` and relations `SGood`, `TGood` under `node6V` for their
  conjunction. **`XeB`**: at the guard's instance, `SGood := fun _ q ↦ SGood6 q`,
  `TGood := fun x q ↦ TGood6 (inst6 B h x) q`, from `node6V` for `Node.Asm.rest6 B h`.
* **`Xe6`**: `XeB` at C3's phases `Φ6 B h` and `V_S` `VSasm (Φ6 B h)`, given `node6V` there; **`Xe6T`**: at the
  deployed base `tiOf6 P`, with C3's `node6V_Φ6`. `Xe6_ext`, `Xe6T_ext`: `hX` by `rfl`.
-/

set_option autoImplicit false

namespace Lvm6.Cert

open RecursionFast Lvm.T LeanVM.Parameters
open LeanVM.Protocol.Compile hiding Proof Bytes Word
open Lvm6.X (G6 ExtSpec6 pick6 pick6_mem)

/-! ## No luck -/

/-- **An invariant that always holds is never escaped.** -/
theorem esc_of_forall {D : List Ev → Prop} (hD : ∀ h, D h) :
    ∀ (p : VerifierProgram Bool) (h : List Ev), esc D h p = 0
  | .ret true, h => by simp [esc, hD h]
  | .ret false, h => by simp [esc]
  | .fail, h => by simp [esc]
  | .read k, h => by simp [esc, hD h]
  | .grind b k, h => by simp [esc, hD h]
  | .commit ht w k, h => by simp [esc, hD h]
  | .sample k, h => by simp [esc, esc_of_forall hD (k _)]
  | .query i ps k, h => by
    simp only [esc]
    split
    · exact esc_of_forall hD _ _
    · rfl

/-! ## The header -/

/-- **`Stmt.hdrView_okV` without the length premise**: a header the scheme's check accepts has a well-formed
view whose statement is `c` and whose key is `vk`. (The proof is `hdrView_okV`'s, which does not read the
length.) -/
theorem hdrView_ok (vk c : Digest) (x : List UInt8)
    (h : V.hdrOkWith leafStmt nodeStmt (2 ^ P17.logN) vk c ⟨x.toArray⟩ = true) :
    HdrWF P17 (hdrView P17 x) ∧ stmtOk c (hdrView P17 x) = true ∧ (hdrView P17 x).vk = vk := by
  simp only [V.hdrOkWith, Bool.and_eq_true, Bool.or_eq_true, beq_iff_eq, decide_eq_true_eq, bne_iff_ne,
    ne_eq] at h
  obtain ⟨⟨⟨⟨⟨_, hvk⟩, hb⟩, hn⟩, hc'⟩, hc⟩ := h
  have hst : stmtOf (hdrView P17 x) = V.stmtWith leafStmt nodeStmt ⟨x.toArray⟩ := by
    simp only [stmtOf, hdrView, V.stmtWith, rdU64_eq_zero, rdD_eq, toNat_rdU64, leafStmtF_eq, nodeStmtF_eq]
  refine ⟨⟨?_, ?_, ?_, ?_⟩, ?_, ?_⟩
  · simp only [hdrView, rdU64_eq_zero, rdU64_eq_one]; exact hb
  · simp only [hdrView, toNat_rdU64]; exact hn
  · intro h0
    simp only [hdrView, rdU64_eq_zero] at h0
    simp only [hdrView, rdD_eq]
    rcases hc' with h1 | h1
    · exact absurd h0 h1
    · exact h1
  · simp [hdrView]
  · simp only [stmtOk, decide_eq_true_eq, hst]; exact hc
  · simp only [hdrView, rdD_eq]; exact hvk

/-- **The scheme's check gives the header's view**: `hdrView_ok` at `schemeOf prog P17 vk`'s `ok`. -/
theorem hdrView_ok_of {prog : Shape → Digest → List UInt8 → VerifierProgram Bool} {vk c : Digest}
    {x : List UInt8} (hok : (schemeOf prog P17 vk).ok c x = true) :
    HdrWF P17 (hdrView P17 x) ∧ stmtOk c (hdrView P17 x) = true ∧ (hdrView P17 x).vk = vk :=
  hdrView_ok vk c x hok

/-! ## The extraction -/

/-- **The pinned pick is the candidate**: on a pinned history, `pick6` is any candidate. -/
theorem pick6_eq {I : OpeningIface} {h : List Ev} {q : Stack} (hp : I.pinned h) (hq : q ∈ I.cands h) :
    pick6 I h = q :=
  I.pinned_sub h hp (pick6_mem ⟨q, hq⟩) hq

section Ext

variable {Φ : Phases} {VS : Shape → SProg} {SGood TGood : Hdr → Stack → Prop}

/-- **The extraction is sound** (`Ext6.extract` without luck): if the scheme's header check accepts `x` and the
history's `G6` holds, `ExtSpec6 (I6 P17)` gives a witness of the relation, under `node6V` for the conjunction of
the relations `SGood` and `TGood`, with the node theorem's readers. -/
theorem extract6
    (hN : Stmt.node6V VS (fun x q ↦ SGood x q ∧ TGood x q) (Node.childOf6 Node.Asm.trOfS Node.Asm.σOfS)
      Node.Asm.σlOfS)
    {vk c : Digest} {x : List UInt8} {h : List Ev} (hok : (schemeOf (prog6 Φ) P17 vk).ok c x = true)
    (hG : G6 SGood TGood x h) : Rel (accV (VS P17) vk) c (ExtSpec6 (Whir.I6 P17) c x h) := by
  obtain ⟨⟨hp, q, hq, hT, hS, hTg⟩, -⟩ := hG
  obtain ⟨hwf, hst, hvk⟩ := hdrView_ok_of hok
  rw [extSpec6_eq, pick6_eq hp hq]
  exact hN vk c (hdrView P17 x) q hwf hst hvk ⟨hT, hS, hTg⟩

/-- **`Xe`** for `kcertAsmG` at the phases `Φ`: no luck (`BL := False`), the extraction map `ExtSpec6 (I6 P17)`,
the extraction by `extract6`. -/
noncomputable def XeOf
    (hN : Stmt.node6V VS (fun x q ↦ SGood x q ∧ TGood x q) (Node.childOf6 Node.Asm.trOfS Node.Asm.σOfS)
      Node.Asm.σlOfS)
    (vk : Digest) : Ext6 (schemeOf (prog6 Φ) P17 vk) (Rel (accV (VS P17) vk)) (G6 SGood TGood) where
  BL _ _ := False
  BL_nil _ := not_false
  BL_read _ _ _ _ := not_false
  BL_commit _ _ _ _ _ := not_false
  BL_group _ _ _ _ _ := by
    rw [esc_of_forall (fun _ => not_false)]
    exact zero_le
  ext := ExtSpec6 (Whir.I6 P17)
  extract hok _ _ hG _ _ := extract6 hN hok hG

end Ext

/-! ## At the guard's instance -/

section Inst

variable {Φ : Phases} {VS : Shape → SProg} (B : V.TyBase6) (hB : V.staticOk6 B = true)

/-- **`Xe` at the guard's instance**: the sponge relation `SGood6` and the typed relation of `inst6 B hB` at the
header, from `node6V` for `Node.Asm.rest6 B hB`. -/
noncomputable def XeB
    (hN : Stmt.node6V VS (Node.Asm.rest6 B hB) (Node.childOf6 Node.Asm.trOfS Node.Asm.σOfS) Node.Asm.σlOfS)
    (vk : Digest) :
    Ext6 (schemeOf (prog6 Φ) P17 vk) (Rel (accV (VS P17) vk))
      (G6 (fun _ q ↦ SP.SGood6 q) (fun x q ↦ Ty.TGood6 (V.inst6 B hB x) q)) :=
  XeOf hN vk

/-- **`hX`**: the extraction map is `ExtSpec6 (I6 P17)`. -/
theorem XeB_ext
    (hN : Stmt.node6V VS (Node.Asm.rest6 B hB) (Node.childOf6 Node.Asm.trOfS Node.Asm.σOfS) Node.Asm.σlOfS)
    (vk : Digest) : (XeB (Φ := Φ) B hB hN vk).ext = ExtSpec6 (Whir.I6 P17) :=
  rfl

end Inst

/-! ## At the certificate's phases -/

/-- **`Xe6`**: `Xe` at the certificate's phases `Φ6 B hB` and `V_S` `VSasm (Φ6 B hB)`, from the node theorem
transported to `Φ6` (link 11; C3's `V.node6V_Φ6 P h` gives it at `B = tiOf6 P`: `Xe6T`). -/
noncomputable def Xe6 (B : V.TyBase6) (hB : V.staticOk6 B = true)
    (hN : Stmt.node6V (VSasm (V.Φ6 B hB)) (Node.Asm.rest6 B hB) (Node.childOf6 Node.Asm.trOfS Node.Asm.σOfS)
      Node.Asm.σlOfS) (vk : Digest) :
    Ext6 (schemeOf (prog6 (V.Φ6 B hB)) P17 vk) (Rel (accV (VSasm (V.Φ6 B hB) P17) vk))
      (G6 (fun _ q ↦ SP.SGood6 q) (fun x q ↦ Ty.TGood6 (V.inst6 B hB x) q)) :=
  XeB B hB hN vk

/-- **`hX` for `Xe6`**, by `rfl`. -/
theorem Xe6_ext (B : V.TyBase6) (hB : V.staticOk6 B = true)
    (hN : Stmt.node6V (VSasm (V.Φ6 B hB)) (Node.Asm.rest6 B hB) (Node.childOf6 Node.Asm.trOfS Node.Asm.σOfS)
      Node.Asm.σlOfS) (vk : Digest) : (Xe6 B hB hN vk).ext = ExtSpec6 (Whir.I6 P17) :=
  rfl

/-- **`Xe6` at the deployed base `tiOf6 P`**, with C3's `node6V_Φ6` (NODE6's `node6V_tiOf6` along `VSasm_Φ6`). -/
noncomputable def Xe6T (P : V.PT) (hB : V.staticOk6 (Node.Ti.tiOf6 P) = true) (vk : Digest) :
    Ext6 (schemeOf (prog6 (V.Φ6 (Node.Ti.tiOf6 P) hB)) P17 vk)
      (Rel (accV (VSasm (V.Φ6 (Node.Ti.tiOf6 P) hB) P17) vk))
      (G6 (fun _ q ↦ SP.SGood6 q) (fun x q ↦ Ty.TGood6 (V.inst6 (Node.Ti.tiOf6 P) hB x) q)) :=
  Xe6 (Node.Ti.tiOf6 P) hB (V.node6V_Φ6 P hB) vk

/-- **`hX` for `Xe6T`**, by `rfl`. -/
theorem Xe6T_ext (P : V.PT) (hB : V.staticOk6 (Node.Ti.tiOf6 P) = true) (vk : Digest) :
    (Xe6T P hB vk).ext = ExtSpec6 (Whir.I6 P17) :=
  rfl

end Lvm6.Cert
