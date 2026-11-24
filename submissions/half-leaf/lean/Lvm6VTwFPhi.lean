-- New for lvm6 (ST-4; additive; moved into `lean/` at V1c4, used by `Lvm6VGuard.VSF6_eq` with `phiChk_ok`):
-- `F_VS` with `hpt` weakened to `PhiOk P.eval …`. `Lvm6VTwF`'s statements are unchanged; `F_VS` is `F_VS_phi` at
-- `fun x => phiOk_pt (hpt x)`. C1: `MAOK` restated (see `Lvm6VTwF`); every theorem takes `hM : sh.M = P17.M`
-- (PORT17 L1; was `P18.M`).
import Lvm6VTwF

/-!
# The fast decision under `PhiOk`

* `tw_rest6_phi`, `tw_prog6_phi`, `F_eq_phi`, **`F_VS_phi`**: `Lvm6VTwF`'s `tw_rest6`, `tw_prog6`, `F_eq`, `F_VS`
  with `hpt : ∀ x, PhiOk P.eval (inst x).Ti.Q (inst x).Ti.lay` (argument order unchanged).
* `F_VS_of_phi`: `F_VS` again, from `F_VS_phi` (the reference route through `ptCheck`).
-/

set_option autoImplicit false

namespace Lvm6.V

open RecursionFast LeanVM.Parameters Lvm.FS Lvm.Replay Lvm Lvm.E2V
open LeanVM.Protocol.Compile hiding Proof Bytes Word

theorem tw_rest6_phi (inst : Hdr → Ty.TyInst6) (P : PT) (hlay : ∀ x, QD.TyLayOk (inst x).Ti)
    (hpt : ∀ x, PhiOk P.eval (inst x).Ti.Q (inst x).Ti.lay)
    (hreg : ∀ x, regsOkB (inst x).Ti = true) (hMA : MAOK inst)
    (sh : Lvm6.Shape) (hM : sh.M = P17.M) (x : Hdr) (c0 : FClaim) (h0 : c0.dec.Multiaffine sh.M) :
    TwinF id (rest6 (phasesV inst) sh x c0.dec) (fRest6 inst P sh x c0) := by
  unfold rest6 fRest6
  refine tw_bindRA (tw_treePh sh x) (hMA.tree sh x) fun t ht => ?_
  refine tw_bindRA (tw_spongePhase6 sh x) (hMA.sponge sh x) fun s hs => ?_
  refine tw_bindRA (tw_typedPhase6X sh (inst x) (hlay x) (hreg x) (hpt x)) (hMA.typed sh x) fun ty hty => ?_
  show TwinF id ((batchJ (phasesV inst) sh [t.dec.slices, s.dec.slices]
    (stackedOf c0.dec t.dec s.dec (ty.map FClaim.dec))) >>= fun cl => Whir.whirP cl) _
  rw [stacked_dec]
  unfold batchJ
  refine (congrArg (fun p => TwinF id p _) (VerifierProgram.bind_assoc _ _ _)).mpr ?_
  refine tw_guard _ _ ?_ ?_
  · rw [decide_eq_true_iff, List.length_map]; exact Iff.rfl
  have hst : ∀ c ∈ (c0 :: (t.2 ++ (s.2 ++ ty))).map FClaim.dec, c.Multiaffine sh.M := by
    intro c hc
    simp only [List.map_cons, List.map_append, List.mem_cons, List.mem_append] at hc
    rcases hc with rfl | hc | hc | hc
    · exact h0
    · exact ht c hc
    · exact hs c hc
    · exact hty c hc
  have hring := tw_ringPhase6 sh [t.1, s.1] (c0 :: (t.2 ++ (s.2 ++ ty)))
  refine tw_bindRA hring (hMA.ring sh _ _ hst) fun cl hcl => ?_
  rw [hM] at hcl
  exact tw_whirPw cl.f cl.v (Whir.MA_w₀ cl.dec hcl)

theorem tw_prog6_phi (inst : Hdr → Ty.TyInst6) (P : PT) (hlay : ∀ x, QD.TyLayOk (inst x).Ti)
    (hpt : ∀ x, PhiOk P.eval (inst x).Ti.Q (inst x).Ti.lay)
    (hreg : ∀ x, regsOkB (inst x).Ti = true) (hMA : MAOK inst)
    (sh : Lvm6.Shape) (hM : sh.M = P17.M) (vk : Digest) (x : List UInt8) :
    TwinF id (prog6 (phasesV inst) sh vk x) (fProg6 inst P sh (hdrView sh x)) := by
  unfold prog6 fProg6
  exact tw_bindRA (tw_commit6 sh) (hMA.commit sh) fun c0 h0 => tw_rest6_phi inst P hlay hpt hreg hMA sh hM _ c0 h0

/-- **`F` is the decision of `prog6`**, the evaluator by `PhiOk` (`F_eq` with `hpt` weakened). -/
theorem F_eq_phi (inst : Hdr → Ty.TyInst6) (P : PT) (hlay : ∀ x, QD.TyLayOk (inst x).Ti)
    (hpt : ∀ x, PhiOk P.eval (inst x).Ti.Q (inst x).Ti.lay)
    (hreg : ∀ x, regsOkB (inst x).Ti = true) (hMA : MAOK inst)
    (sh : Lvm6.Shape) (hM : sh.M = P17.M) (vk : Digest) (π : ByteArray) (acc : List NV) :
    F inst P sh π acc = F6 (phasesV inst) sh vk π acc := by
  unfold F F6
  rw [replay_eq, ← List.map_reverse, ← hdrBytes_eq]
  have h := tw_prog6_phi inst P hlay hpt hreg hMA sh hM vk (hdrBytes sh π) π acc.reverse
  revert h
  generalize fProg6 inst P sh (hdrView sh (hdrBytes sh π)) π acc.reverse = u
  generalize replayP (prog6 (phasesV inst) sh vk (hdrBytes sh π)) (acc.reverse.map (NV.val π)) = w
  intro h
  cases h with
  | none => rfl
  | some h =>
    obtain ⟨hb, hrest⟩ := h
    rename_i b a
    obtain ⟨b1, b2⟩ := b
    obtain ⟨a1, a2⟩ := a
    simp only [id] at hb hrest
    subst hb hrest
    cases b2 <;> rfl

/-- **`V_S` with `F` is ASM's `VSasm`**, the evaluator by `PhiOk` (`F_VS` with `hpt` weakened; same argument order). -/
theorem F_VS_phi (inst : Hdr → Ty.TyInst6) (P : PT) (hlay : ∀ x, QD.TyLayOk (inst x).Ti)
    (hpt : ∀ x, PhiOk P.eval (inst x).Ti.Q (inst x).Ti.lay)
    (hreg : ∀ x, regsOkB (inst x).Ti = true) (hMA : MAOK inst)
    (sh : Lvm6.Shape) (hM : sh.M = P17.M) (vk : Digest) (c : Digest) (π : Proof) :
    VS6 (toV sh) (F inst P sh) vk c π = VSasm (phasesV inst) sh vk c π := by
  unfold VSasm
  rw [show F inst P sh = F6 (phasesV inst) sh vk from funext fun π' => funext fun acc =>
    F_eq_phi inst P hlay hpt hreg hMA sh hM vk π' acc]

/-- `F_VS` through `F_VS_phi` (`phiOk_pt` gives `PhiOk` from `ptCheck`). -/
theorem F_VS_of_phi (inst : Hdr → Ty.TyInst6) (P : PT) (hlay : ∀ x, QD.TyLayOk (inst x).Ti)
    (hpt : ∀ x, ptCheck P (Ty.entsE (inst x).Ti.Q (inst x).Ti.lay) = true)
    (hreg : ∀ x, regsOkB (inst x).Ti = true) (hMA : MAOK inst)
    (sh : Lvm6.Shape) (hM : sh.M = P17.M) (vk : Digest) (c : Digest) (π : Proof) :
    VS6 (toV sh) (F inst P sh) vk c π = VSasm (phasesV inst) sh vk c π :=
  F_VS_phi inst P hlay (fun x => phiOk_pt (hpt x)) hreg hMA sh hM vk c π

end Lvm6.V
