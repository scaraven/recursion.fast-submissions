-- New for lvm6 (WP V1c): the fast decision `F` of `prog6` assembled from the phase twins, and `F = F6`.
-- The deployed phases: `commit6`, K2's `treeProgS6`, SPH's `spongePhase6`, Y1's `typedPhase6` at an instance map (fast: PHIV's factored region claims, `fTypedPhase6X`),
-- ASM's `batchJ` and `ringPhase6`, W1's `whirP`. The fast typed phase evaluates `Φ_Q` with PHIV's `PT.eval`, which
-- `ptCheck` licenses (`phiOk_pt`); the fast opening needs the batched claim multiaffine (`tw_whirP`'s `hma`), here
-- a hypothesis on the phases (`MAOK`: the same facts W1's `openSpecD` asks).
-- C1 (2026-11-23): `MAOK` restated over S's `Multiaffine sh.M` (MA's theorems; `MAW` was unprovable: no `padD`, tails
-- of every length); the twins take `sh.M = P17.M` (PORT17 L1; was `P18.M`) and read the opening's hypothesis by
-- `Whir.MA_w₀` (`tw_whirPw`).
import Lvm6VTwC
import Lvm6VPhiPT
import Lvm6VPhiReg
import Lvm6VTwO2
import Lvm6AsmSpec
import Lvm6MultiaffBase
import Lvm6WhirIface

/-!
# The fast decision `F`

* `retAll_replayP`, **`tw_bindRA`** (a bind whose first value carries a `RetAll` property of the program).
* `MAW c` (W1's `MA 24` of the rotated weight; no longer used); **`MAOK inst`**: every phase's claims are
  multiaffine on `sh.M` variables (S's `Multiaffine`), and the ring phase keeps it.
* `phasesV inst` = `phases6 (typedPhase6 · (inst ·)) ringPhase6 whirP`.
* `fRest6`, `fProg6`; **`tw_prog6`**: `TwinF id (prog6 (phasesV inst) sh vk x) (fProg6 …)`.
* **`F`**, **`F_eq`**: `F … π acc = F6 (phasesV inst) sh vk π acc`, so `VS6` with `F` is `VSasm` (`F_VS`).
-/

set_option autoImplicit false

namespace Lvm6.V

open RecursionFast LeanVM.Parameters Lvm.FS Lvm.Replay Lvm Lvm.E2V
open LeanVM.Protocol.Compile hiding Proof Bytes Word

/-! ## Binds with a property of the specification's value -/

theorem retAll_replayP {α : Type} {Q : α → Prop} :
    ∀ (p : VerifierProgram α) (tr : List Val) (r : α × List Val), RetAll Q p → replayP p tr = some r → Q r.1 := by
  intro p
  induction p with
  | ret a =>
    intro tr r hQ h
    have e : replayP (VerifierProgram.ret a) tr = some (a, tr) := rfl
    rw [e] at h
    cases h
    exact hQ
  | fail => intro tr r _ h; rw [replayP_fail] at h; cases h
  | grind g k _ =>
    intro tr r _ h
    have e : ∀ tr', replayP (VerifierProgram.grind g k : VerifierProgram α) tr' = none := fun tr' => by
      cases tr' <;> rfl
    rw [e] at h; cases h
  | read k ih =>
    intro tr r hQ h
    rcases tr with _ | ⟨v, tr⟩
    · cases h
    · cases v with
      | e x => exact ih x tr r (hQ x) h
      | _ => cases h
  | sample k ih =>
    intro tr r hQ h
    rcases tr with _ | ⟨v, tr⟩
    · cases h
    · cases v with
      | c x => exact ih x tr r (hQ x) h
      | _ => cases h
  | commit ht w k ih =>
    intro tr r hQ h
    rcases tr with _ | ⟨v, tr⟩
    · cases h
    · cases v with
      | cap ht' w' =>
        have e : replayP (VerifierProgram.commit ht w k) (Val.cap ht' w' :: tr) =
            if ht = ht' ∧ w = w' then replayP k tr else none := rfl
        rw [e] at h
        split at h
        · exact ih tr r hQ h
        · cases h
      | _ => cases h
  | query i ps k ih =>
    intro tr r hQ h
    rcases tr with _ | ⟨v, tr⟩
    · cases h
    · cases v with
      | rows i' ps' rr =>
        have e : replayP (VerifierProgram.query i ps k) (Val.rows i' ps' rr :: tr) =
            if i = i' ∧ ps = ps' then replayP (k rr) tr else none := rfl
        rw [e] at h
        split at h
        · exact ih rr tr r (hQ rr) h
        · cases h
      | _ => cases h

theorem tw_bindRA {α β α' β' : Type} {d : β → α} {R' : ByteArray → β' → α' → Prop} {Q : α → Prop}
    {p : VerifierProgram α} {fp : VF β} {f : α → VerifierProgram α'} {fg : β → VF β'} (hp : TwinF d p fp)
    (hR : RetAll Q p) (hf : ∀ b, Q (d b) → Twin R' (f (d b)) (fg b)) : Twin R' (p >>= f) (VF.bind fp fg) := by
  intro π tr
  show Option.Rel _ ((fp π tr).bind fun r => fg r.1 π r.2) (replayP (p.bind f) (tr.map (NV.val π)))
  rw [replayP_bind]
  have h := hp π tr
  rcases hf1 : fp π tr with _ | b <;> rcases hr1 : replayP p (tr.map (NV.val π)) with _ | a <;> rw [hf1, hr1] at h
  · exact Option.Rel.none
  · cases h
  · cases h
  · cases h with
    | some h =>
      obtain ⟨hd, hrest⟩ := h
      have hQ : Q a.1 := retAll_replayP p _ a hR hr1
      simp only [Option.bind_some]
      rw [hrest, ← hd]
      rw [← hd] at hQ
      exact hf b.1 hQ π b.2

/-! ## The deployed phases and the multiaffinity they owe -/

/-- W1's multiaffinity of a claim's weight in the opening's rotated order (C1: no longer in `MAOK`). -/
def MAW (c : StackClaim6) : Prop := Whir.MA 24 fun y => c.1 (y.drop 6 ++ y.take 6)

/-- The phases of `prog6` at a typed instance map. -/
noncomputable def phasesV (inst : Hdr → Ty.TyInst6) : Phases :=
  phases6 (fun sh x => Ty.typedPhase6 sh (inst x)) ringPhase6 (fun _ cl => Whir.whirP cl)

/-- **The multiaffinity the fast opening needs** (W1's `openSpecD` asks the same, through `MA_w₀`): every phase's
claims are multiaffine on `sh.M` variables (S's `Multiaffine`), and the ring phase keeps it. -/
structure MAOK (inst : Hdr → Ty.TyInst6) : Prop where
  commit : ∀ sh, RetAll (fun c : StackClaim6 => c.Multiaffine sh.M) (commit6 sh)
  tree : ∀ sh x, RetAll (fun t : TreeOut => ∀ c ∈ t.claims, c.Multiaffine sh.M) (K.treeProgS6 sh x)
  sponge : ∀ sh x, RetAll (fun t : TreeOut => ∀ c ∈ t.claims, c.Multiaffine sh.M) (SP.spongePhase6 sh x)
  typed : ∀ sh x, RetAll (fun ty : List StackClaim6 => ∀ c ∈ ty, c.Multiaffine sh.M) (Ty.typedPhase6 sh (inst x))
  ring : ∀ sh sl st, (∀ c ∈ st, c.Multiaffine sh.M) →
    RetAll (fun c : StackClaim6 => c.Multiaffine sh.M) (ringPhase6 sh sl st)

/-! ## The fast program -/

/-- The fast tree phase as a `PhF`. -/
def fTreePh (sh : Lvm6.Shape) (x : Hdr) : VF PhF := VF.bind (fTreeProgS6 sh x) fun t => VF.pure (treePhF t)

theorem tw_treePh (sh : Lvm6.Shape) (x : Hdr) : TwinF PhF.dec (K.treeProgS6 sh x) (fTreePh sh x) := by
  have h := tw_bind (f := pure) (fg := fun t => VF.pure (treePhF t)) (tw_treeProgS6 sh x)
    (fun t => tw_pure (treePhF_dec t))
  intro π tr
  have h2 := h π tr
  rwa [show (K.treeProgS6 sh x >>= pure) = K.treeProgS6 sh x from VerifierProgram.bind_ret _] at h2

/-- **The fast program after the commitment** (`rest6`). -/
def fRest6 (inst : Hdr → Ty.TyInst6) (P : PT) (sh : Lvm6.Shape) (x : Hdr) (c0 : FClaim) : VF Bool :=
  VF.bind (fTreePh sh x) fun t =>
  VF.bind (fSpongePhase6 sh) fun s =>
  VF.bind (fTypedPhase6X sh (inst x) P.eval) fun ty =>
  VF.guard (decide ([t.1, s.1].length + (c0 :: (t.2 ++ (s.2 ++ ty))).length ≤ sh.J₀))
    (VF.bind (fRingPhase6 sh [t.1, s.1] (c0 :: (t.2 ++ (s.2 ++ ty)))) fun cl => fWhir cl.f cl.v)

/-- **The fast program** on the header view `x`. -/
def fProg6 (inst : Hdr → Ty.TyInst6) (P : PT) (sh : Lvm6.Shape) (x : Hdr) : VF Bool :=
  VF.bind (fCommit6 sh) fun c0 => fRest6 inst P sh x c0

theorem stacked_dec (c0 : FClaim) (t s : PhF) (ty : List FClaim) :
    stackedOf c0.dec t.dec s.dec (ty.map FClaim.dec) = (c0 :: (t.2 ++ (s.2 ++ ty))).map FClaim.dec := by
  simp [stackedOf, PhF.dec, List.map_append]

theorem tw_rest6 (inst : Hdr → Ty.TyInst6) (P : PT) (hlay : ∀ x, QD.TyLayOk (inst x).Ti)
    (hpt : ∀ x, ptCheck P (Ty.entsE (inst x).Ti.Q (inst x).Ti.lay) = true)
    (hreg : ∀ x, regsOkB (inst x).Ti = true) (hMA : MAOK inst)
    (sh : Lvm6.Shape) (hM : sh.M = P17.M) (x : Hdr) (c0 : FClaim) (h0 : c0.dec.Multiaffine sh.M) :
    TwinF id (rest6 (phasesV inst) sh x c0.dec) (fRest6 inst P sh x c0) := by
  unfold rest6 fRest6
  refine tw_bindRA (tw_treePh sh x) (hMA.tree sh x) fun t ht => ?_
  refine tw_bindRA (tw_spongePhase6 sh x) (hMA.sponge sh x) fun s hs => ?_
  refine tw_bindRA (tw_typedPhase6X sh (inst x) (hlay x) (hreg x) (phiOk_pt (hpt x))) (hMA.typed sh x) fun ty hty => ?_
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

theorem tw_prog6 (inst : Hdr → Ty.TyInst6) (P : PT) (hlay : ∀ x, QD.TyLayOk (inst x).Ti)
    (hpt : ∀ x, ptCheck P (Ty.entsE (inst x).Ti.Q (inst x).Ti.lay) = true)
    (hreg : ∀ x, regsOkB (inst x).Ti = true) (hMA : MAOK inst)
    (sh : Lvm6.Shape) (hM : sh.M = P17.M) (vk : Digest) (x : List UInt8) :
    TwinF id (prog6 (phasesV inst) sh vk x) (fProg6 inst P sh (hdrView sh x)) := by
  unfold prog6 fProg6
  exact tw_bindRA (tw_commit6 sh) (hMA.commit sh) fun c0 h0 => tw_rest6 inst P hlay hpt hreg hMA sh hM _ c0 h0

/-! ## The decision -/

/-- The header bytes of `π`. -/
def hdrBytes (sh : Lvm6.Shape) (π : ByteArray) : List UInt8 := bl (π.extract 0 (hdrLen (toV sh)))

theorem hdrBytes_eq (sh : Lvm6.Shape) (π : ByteArray) : hdrBytes sh π = (bl π).take (hdrLen (toV sh)) := by
  rw [hdrBytes, bl_extract, List.drop_zero, Nat.sub_zero]

/-- **The fast decision**: the fast program on the driver's transcript (oldest first), accepting when it returns
`true` with the transcript used up. -/
def F (inst : Hdr → Ty.TyInst6) (P : PT) (sh : Lvm6.Shape) (π : ByteArray) (acc : List NV) : Bool :=
  match fProg6 inst P sh (hdrView sh (hdrBytes sh π)) π acc.reverse with
  | some (b, []) => b
  | _ => false

/-- **`F` is the decision of `prog6`** (`F6`, ASM). -/
theorem F_eq (inst : Hdr → Ty.TyInst6) (P : PT) (hlay : ∀ x, QD.TyLayOk (inst x).Ti)
    (hpt : ∀ x, ptCheck P (Ty.entsE (inst x).Ti.Q (inst x).Ti.lay) = true)
    (hreg : ∀ x, regsOkB (inst x).Ti = true) (hMA : MAOK inst)
    (sh : Lvm6.Shape) (hM : sh.M = P17.M) (vk : Digest) (π : ByteArray) (acc : List NV) :
    F inst P sh π acc = F6 (phasesV inst) sh vk π acc := by
  unfold F F6
  rw [replay_eq, ← List.map_reverse, ← hdrBytes_eq]
  have h := tw_prog6 inst P hlay hpt hreg hMA sh hM vk (hdrBytes sh π) π acc.reverse
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

/-- **`V_S` with `F` is ASM's `VSasm`** on the deployed phases. -/
theorem F_VS (inst : Hdr → Ty.TyInst6) (P : PT) (hlay : ∀ x, QD.TyLayOk (inst x).Ti)
    (hpt : ∀ x, ptCheck P (Ty.entsE (inst x).Ti.Q (inst x).Ti.lay) = true)
    (hreg : ∀ x, regsOkB (inst x).Ti = true) (hMA : MAOK inst)
    (sh : Lvm6.Shape) (hM : sh.M = P17.M) (vk : Digest) (c : Digest) (π : Proof) :
    VS6 (toV sh) (F inst P sh) vk c π = VSasm (phasesV inst) sh vk c π := by
  unfold VSasm
  rw [show F inst P sh = F6 (phasesV inst) sh vk from funext fun π' => funext fun acc =>
    F_eq inst P hlay hpt hreg hMA sh hM vk π' acc]

end Lvm6.V
