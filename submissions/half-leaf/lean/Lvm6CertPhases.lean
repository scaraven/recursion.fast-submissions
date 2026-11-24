-- New for lvm6 (WP C3 of CERT, links 5, 7, 8 and the node transport of link 11): the deployed phases with the opening
-- keyed on the shape (`whirAt`), the form `open6XD`'s `hw` asks, and their certificate inputs.
import Lvm6VGuard
import Lvm6SpPhase
import Lvm6TyFollows
import Lvm6WhirFollow
import Lvm6WhirCommit
import Lvm6WhirBack
import Lvm6VQueries
import Lvm6XCorrect
import Lvm6P17MemoS

/-!
# The certificate's phases `Φ6`

* **`phasesW inst`** = `phases6 (typedPhase6 · (inst ·)) ringPhase6 (whirAt whirP)`: `phasesV inst` with W1's opening
  keyed on the shape (`whirP` on shapes with `P17`'s opening constants, rejection elsewhere).
* **`Φ6 B h`** = `phasesW (inst6 B h)`: the phases at the guard's instance; `(Φ6 B h).whir = whirAt whirP` by `rfl`.
* **`prog6_whir`**, **`VSasm_whir`**: `prog6` and `VSasm` at a shape read the opening only at that shape.
  **`VSasm_whirAt`**: `VSasm (phasesV inst) sh = VSasm (phasesW inst) sh` where `openKey sh`; `VSasm_whirAtD` at `P17`.
* **`queries_VSasm`**, **`queries_VSF6`**: `V_S` at `P17` asks at most `P17.qS` queries (`VS6_queries`, `queriesD`).
* **`phasesFollowW`** (`PhasesFollow` at `P17`), **`openGoodW`** (`openGoodC GWDc`), **`phaseSpecsW`** (`PhaseSpecs`
  with `SGood6` and `TGood6 (inst x)`), at every instance map; the `Φ6` forms are corollaries.
* **`listL_I6`**: `PhaseSpecs`'s field `listL` for W1's seam `I6` (`listL_I6_of`: `openKey` fixes `L₀ = P17.L₀`).
-/

set_option autoImplicit false

namespace Lvm6.V

open RecursionFast LeanVM.Parameters
open LeanVM.Protocol.Compile hiding Proof Bytes Word

/-! ## The phases -/

/-- **The deployed phases with the shape-keyed opening** at a typed instance map: `phasesV inst` with
`whirAt whirP` in place of `fun _ cl ↦ whirP cl`. -/
noncomputable def phasesW (inst : Hdr → Ty.TyInst6) : Phases :=
  phases6 (fun sh x => Ty.typedPhase6 sh (inst x)) ringPhase6 (whirAt Whir.whirP)

/-- **The certificate's phases** at the guard's instance `inst6 B h`. -/
noncomputable def Φ6 (B : TyBase6) (h : staticOk6 B = true) : Phases := phasesW (inst6 B h)

theorem Φ6_whir (B : TyBase6) (h : staticOk6 B = true) : (Φ6 B h).whir = whirAt Whir.whirP := rfl

/-! ## Link 7: `VSasm` reads the opening only at its shape -/

/-- **`prog6` at a shape reads the opening only at that shape.** -/
theorem prog6_whir (Φ : Phases) (w : Shape → StackClaim6 → VerifierProgram Bool) {sh : Shape}
    (hw : w sh = Φ.whir sh) : prog6 { Φ with whir := w } sh = prog6 Φ sh := by
  funext vk x
  simp only [prog6, rest6, batchJ, hw]

/-- **`VSasm` at a shape reads the opening only at that shape.** -/
theorem VSasm_whir (Φ : Phases) (w : Shape → StackClaim6 → VerifierProgram Bool) {sh : Shape}
    (hw : w sh = Φ.whir sh) : VSasm { Φ with whir := w } sh = VSasm Φ sh := by
  unfold VSasm F6
  rw [prog6_whir Φ w hw]

/-- `whirAt whirP` is `whirP` on a shape with `P17`'s opening constants. -/
theorem whirAt_key {sh : Shape} (hk : openKey sh = true) : whirAt Whir.whirP sh = fun cl => Whir.whirP cl :=
  funext fun _ => ite_eq_left hk

/-- **`VSasm_whirAt`**: on a shape with `P17`'s opening constants, `phasesV` and `phasesW` give the same `V_S`. -/
theorem VSasm_whirAt (inst : Hdr → Ty.TyInst6) {sh : Shape} (hk : openKey sh = true) :
    VSasm (phasesV inst) sh = VSasm (phasesW inst) sh :=
  (VSasm_whir (phasesV inst) (whirAt Whir.whirP) (whirAt_key hk)).symm

/-- `VSasm_whirAt` at `P17`. -/
theorem VSasm_whirAtD (inst : Hdr → Ty.TyInst6) : VSasm (phasesV inst) P17 = VSasm (phasesW inst) P17 :=
  VSasm_whirAt inst openKey_P17

/-- `VSasm_whirAtD` at the guard's instance: `VSasm (phasesV (inst6 B h))` (`VSspec6`'s branch with the guard on)
is `VSasm (Φ6 B h)` at `P17`. -/
theorem VSasm_Φ6 (B : TyBase6) (h : staticOk6 B = true) :
    VSasm (phasesV (inst6 B h)) P17 = VSasm (Φ6 B h) P17 :=
  VSasm_whirAtD (inst6 B h)

/-! ## Link 5: the query bound -/

/-- **`P17`'s walk count is within `qS`** (`qOf`, V1's driver walk, against FORMAT6's `qS`). -/
theorem queriesD : 2 + qOf (toV P17).levs (sched6 P17) ≤ P17.qS := by
  rw [sched6_P17_eq]
  decide +kernel

theorem toV_sched (sh : Shape) : (toV sh).sched = sched6 sh := rfl

/-- `VS6_queries` at `P17` with `queriesD`. -/
theorem VS6_queriesD (F : ByteArray → List NV → Bool) (vk c : Digest) (π : Proof) (H : ByteArray → Digest) :
    ((VS6 (toV P17) F vk c π).queries H).length ≤ P17.qS := by
  have h := VS6_queries (toV P17) F vk c π H
  rw [toV_sched] at h
  exact Nat.le_trans h queriesD

/-- **`V_S` for any phases asks at most `qS` queries at `P17`.** -/
theorem queries_VSasm (Φ : Phases) (vk c : Digest) (π : Proof) (H : ByteArray → Digest) :
    ((VSasm Φ P17 vk c π).queries H).length ≤ P17.qS :=
  VS6_queriesD (F6 Φ P17 vk) vk c π H

/-- **The guarded fast `V_S` asks at most `qS` queries at `P17`**, for either value of the guard. -/
theorem queries_VSF6 (B : TyBase6) (vk c : Digest) (π : Proof) (H : ByteArray → Digest) :
    ((VSF6 B P17 vk c π).queries H).length ≤ P17.qS := by
  unfold VSF6
  split
  · exact VS6_queriesD _ vk c π H
  · simp [OProg.queries]

/-! ## Link 8: the certificate's phase inputs -/

/-- `whirAt whirP` follows §6.6 of `P17`'s schedule. -/
theorem whirAt_follows (cl : StackClaim6) :
    Follows (whirAt Whir.whirP P17 cl) (opsOf P17.levs P17.openPart) := by
  rw [whirAt_key openKey_P17]
  exact Whir.whirP_follows cl

/-- **`PhasesFollow` at `P17`** for the shape-keyed phases at every instance map. -/
theorem phasesFollowW (inst : Hdr → Ty.TyInst6) : PhasesFollow (phasesW inst) P17 :=
  SP.phases6_follows (fun x => Ty.typedPhase6_follows P17 rfl (inst x)) (ringPhase6_follows P17)
    whirAt_follows

/-- **The opening's good-history facts** (`HG`) for the shape-keyed phases. -/
theorem openGoodW (inst : Hdr → Ty.TyInst6) : Stmt.openGoodC Whir.GWDc (phasesW inst).whir :=
  X.openGoodC_W1

/-- **`listL` from a key that fixes `L₀`**: if every shape with `P17`'s opening constants has `L₀ ≥ P17.L₀`, the list
bound holds for `I6` (`ID`'s `L₀` is `111`, which is `P17.L₀` by definition; `Itriv`'s is `0`). `openKey` reads `L₀` (its last conjunct), so the hypothesis holds: `listL_I6`. -/
theorem listL_I6_of (hk : ∀ sh, openKey sh = true → P17.L₀ ≤ sh.L₀) : ∀ sh, (Whir.I6 sh).L₀ ≤ sh.L₀ := fun sh => by
  by_cases k : openKey sh = true
  · rw [show Whir.I6 sh = Whir.ID from ite_eq_left k]
    exact hk sh k
  · rw [show Whir.I6 sh = Whir.Itriv from ite_eq_right k]
    exact Nat.zero_le _

/-- **The list bound of W1's seam** (`PhaseSpecs.listL` for `I6`): `openKey` fixes `L₀ = P17.L₀`. -/
theorem listL_I6 : ∀ sh, (Whir.I6 sh).L₀ ≤ sh.L₀ :=
  listL_I6_of fun sh hk => by
    simp only [openKey, Bool.and_eq_true, decide_eq_true_eq] at hk
    exact hk.2.ge

/-- **`PhaseSpecs`** for the shape-keyed phases at every instance map (sponge relation `SGood6`, typed relation
`TGood6 (inst x)`), from W1's, RS's, Y1's and MA's phase statements and the list bound `listL_I6`. -/
theorem phaseSpecsW (inst : Hdr → Ty.TyInst6) :
    PhaseSpecs (phasesW inst) Whir.I6 (fun _ q => SP.SGood6 q) (fun x q => Ty.TGood6 (inst x) q) :=
  SP.phases6_specs Whir.commitSpec6_W1 (fun sh x => Ty.typedSpec6 sh (inst x)) ringSpec6_asm Whir.openSpec6_W1 listL_I6
    (fun sh x => Ty.typedPhase6_noCommit sh (inst x)) ringPhase6_noCommit (typedPhase6_ma_at inst)

/-! ## The `Φ6` forms -/

section Φ6

variable (B : TyBase6) (h : staticOk6 B = true)

theorem phasesFollow6 : PhasesFollow (Φ6 B h) P17 := phasesFollowW (inst6 B h)

theorem openGood6 : Stmt.openGoodC Whir.GWDc (Φ6 B h).whir := openGoodW (inst6 B h)

theorem phaseSpecs6 :
    PhaseSpecs (Φ6 B h) Whir.I6 (fun _ q => SP.SGood6 q) (fun x q => Ty.TGood6 (inst6 B h x) q) :=
  phaseSpecsW (inst6 B h)

end Φ6

end Lvm6.V
