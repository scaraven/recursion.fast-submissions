-- New for lvm6 (WP NODE2). `ChildOk` from the node circuit's composed HARs: the link, header and signature
-- fields from `Q_link`/`Q_sig` (CA's `childLink6`) and CB's trace digest, the grinds from the PoW lanes, and
-- V1's decision `F6` from the phase runs (CB, CD) with the commitment, ring and opening phases (CC) named.
import Lvm6NodeChild
import Lvm6NodeQ
import Lvm6SpProg
import Lvm6KProgS6
import Lvm6QKWire
import Lvm6TyStmt

/-!
# `ChildOk` from the node circuit (WP NODE2)

The proofs use the HAR interfaces only (`Runs`, `Har`/`HarIn` conclusions, `childLink6`'s and
`traceDigest6`'s statements), never a gadget's rows.

* **Transcript values as events.** V1's decision `F6` replays `prog6` on the values `NV.val` read off the
  proof (`V.replay`, values `V.Val`). `afterV` is `VerifierProgram.after` on values, with `replay`'s
  extra checks (a cap's shape, an opening's commitment index and positions). `replay_of_afterV`,
  `afterV_bind_append`, and **`afterV_of_runs`**: a phase that `Runs` on its slots, on values without
  openings whose events (`toEv`) match the slots, returns on those values.
* **`replay_prog6`**: `prog6` replays to `true` on `vc ++ vt ++ vs ++ vy ++ vr ++ vo` when each phase
  returns on its segment, the `J₀` bound holds and the opening returns `true`.
* **`dec_of_runs`**: the `dec` field for `phases6 (typedPhase6 · ∘ tyOf) ring whir` from the runs of
  `node6E_har` (tree, sponge caller and link, typed), with named hypotheses for the parts without a
  placed gadget: the value split (`EvMatch` bridge, NODE §7 (i)), the commitment phase (lanes only),
  and `htail`: ring switching (CC-5′) and the opening (CC-2/CC-3 per level, CC-8; CCV/CC8).
* **`powOK6_of_lanes`**: the PoW rows' conclusion on the stream lanes gives `PowOK6`.
* **`linkHdrSig6`**: `childLink6`'s conclusion at `planOf P18`, CB-4's trace digest and the digest cells
  give `link`, `hdr`, `sig`. **`childOk_of_node`** assembles the five fields.
-/

set_option autoImplicit false

namespace Lvm6.Node

open RecursionFast Lvm6.Q Lvm.Replay
open LeanVM.Protocol.Compile hiding Proof Bytes Word
open Lvm Lvm.Loop Lvm.Loop.Build Lvm.Q2 Lvm.Har Lvm.E2V
open Lvm6.QK Lvm6.QK.W Lvm.QSig Lvm.QLink
open LeanVM.Parameters

/-! ## Transcript values as events -/

/-- The event a transcript value stands for (a cap's matrix words are not observed). -/
def toEv : V.Val → Ev
  | .e x => .read x
  | .c x => .sample x
  | .cap ht w => .commit ht w fun _ ↦ []
  | .rows _ _ r => .query r

/-- No value is an opening. -/
def NoRows (vs : List V.Val) : Prop := ∀ v ∈ vs, ∀ i ps r, v ≠ .rows i ps r

/-- **`after` on transcript values**, with `replay`'s checks. -/
def afterV {α : Type} : VerifierProgram α → List V.Val → Option (VerifierProgram α)
  | p, [] => some p
  | .read k, .e x :: tr => afterV (k x) tr
  | .sample k, .c x :: tr => afterV (k x) tr
  | .commit ht w k, .cap ht' w' :: tr => if ht = ht' ∧ w = w' then afterV k tr else none
  | .query i ps k, .rows i' ps' r :: tr => if i = i' ∧ ps = ps' then afterV (k r) tr else none
  | _, _ :: _ => none

theorem replay_of_afterV : ∀ (p : VerifierProgram Bool) (vs : List V.Val),
    afterV p vs = some (.ret true) → V.replay p vs = true
  | p, [], h => by
    simp only [afterV, Option.some.injEq] at h
    subst h
    rfl
  | p, v :: vs, h => by
    cases p <;> cases v <;> simp only [afterV, reduceCtorEq] at h
    all_goals first
      | exact replay_of_afterV _ vs h
      | (split at h
         · rename_i hc
           obtain ⟨rfl, rfl⟩ := hc
           simp only [V.replay, beq_self_eq_true, Bool.and_self, Bool.true_and]
           exact replay_of_afterV _ vs h
         · simp at h)

theorem afterV_append {α : Type} : ∀ (p : VerifierProgram α) (l₁ l₂ : List V.Val),
    afterV p (l₁ ++ l₂) = (afterV p l₁).bind fun q ↦ afterV q l₂
  | p, [], l₂ => by simp [afterV]
  | p, v :: l₁, l₂ => by
    cases p <;> cases v <;> simp only [List.cons_append, afterV, Option.bind_none]
    all_goals first
      | exact afterV_append _ l₁ l₂
      | (split
         · exact afterV_append _ l₁ l₂
         · rfl)

theorem afterV_bind_of {α β : Type} (f : α → VerifierProgram β) : ∀ (p : VerifierProgram α)
    (l : List V.Val) {q : VerifierProgram α}, afterV p l = some q → afterV (p.bind f) l = some (q.bind f)
  | p, [], _, h => by simp only [afterV, Option.some.injEq] at h; simp [afterV, h]
  | p, v :: vs, _, h => by
    cases p <;> cases v <;> simp only [afterV, reduceCtorEq] at h
    all_goals first
      | exact afterV_bind_of f _ vs h
      | (split at h
         · rename_i hc
           simp only [VerifierProgram.bind, afterV, hc, and_self, ↓reduceIte]
           exact afterV_bind_of f _ vs h
         · simp at h)

/-- After a return of `p` on `l₁`, `p >>= f` runs `f` on `l₂`. -/
theorem afterV_bind_append {α β : Type} (f : α → VerifierProgram β) {p : VerifierProgram α}
    {l₁ : List V.Val} {a : α} (h : afterV p l₁ = some (.ret a)) (l₂ : List V.Val) :
    afterV (p >>= f) (l₁ ++ l₂) = afterV (f a) l₂ := by
  rw [afterV_append, show p >>= f = p.bind f from rfl, afterV_bind_of f p l₁ h]
  rfl

/-- Without openings, `afterV` is `after` on the events. -/
theorem afterV_of_after {α : Type} : ∀ (p : VerifierProgram α) (vs : List V.Val) {q : VerifierProgram α},
    NoRows vs → p.after (vs.map toEv) = some q → afterV p vs = some q
  | p, [], _, _, h => by simpa [afterV, VerifierProgram.after] using h
  | p, v :: vs, _, hn, h => by
    have hn' : NoRows vs := fun w hw ↦ hn w (List.mem_cons_of_mem _ hw)
    cases v with
    | rows i ps r => exact absurd rfl (hn _ (by simp) i ps r)
    | _ =>
      cases p <;> simp only [List.map_cons, toEv, VerifierProgram.after, reduceCtorEq] at h
      all_goals first
        | exact afterV_of_after _ vs hn' h
        | (split at h
           · rename_i hc
             simp only [afterV, hc, and_self, ↓reduceIte]
             exact afterV_of_after _ vs hn' h
           · simp at h)

/-- **A phase that runs on its slots returns on matching values.** -/
theorem afterV_of_runs {β : Type} {M : Mem} {lay : List LEv} {p : VerifierProgram β} {P : β → Prop}
    (h : Runs M lay p P) (hp : PowLay M lay) {vs : List V.Val} (hn : NoRows vs)
    (he : EvMatch M lay (vs.map toEv)) : ∃ out, afterV p vs = some (.ret out) ∧ P out := by
  obtain ⟨out, h1, h2⟩ := h hp _ he
  exact ⟨out, afterV_of_after p vs hn h1, h2⟩

theorem afterV_require {c : Prop} [Decidable c] (hc : c) :
    afterV (VerifierProgram.require c) [] = some (.ret ()) := by
  simp [afterV, VerifierProgram.require, hc]

/-! ## `prog6` from its phases -/

/-- **`prog6` replays to `true`** on the concatenated phase segments. -/
theorem replay_prog6 (Φ : Phases) (sh : Shape) (vk : Digest) (x : List UInt8)
    {vc vt vs vy vr vo : List V.Val} {c0 : StackClaim6} {t s : TreeOut} {ty : List StackClaim6}
    {cl : StackClaim6}
    (hc : afterV (Φ.commit sh) vc = some (.ret c0))
    (ht : afterV (Φ.tree sh (hdrView sh x)) vt = some (.ret t))
    (hs : afterV (Φ.sponge sh (hdrView sh x)) vs = some (.ret s))
    (hy : afterV (Φ.typed sh (hdrView sh x)) vy = some (.ret ty))
    (hJ : [t.slices, s.slices].length + (stackedOf c0 t s ty).length ≤ sh.J₀)
    (hr : afterV (Φ.ring sh [t.slices, s.slices] (stackedOf c0 t s ty)) vr = some (.ret cl))
    (hw : afterV (Φ.whir sh cl) vo = some (.ret true)) :
    V.replay (prog6 Φ sh vk x) (vc ++ (vt ++ (vs ++ (vy ++ (vr ++ vo))))) = true := by
  apply replay_of_afterV
  have hb : afterV (batchJ Φ sh [t.slices, s.slices] (stackedOf c0 t s ty)) vr = some (.ret cl) := by
    rw [batchJ, ← List.nil_append vr, afterV_bind_append _ (afterV_require hJ)]
    exact hr
  rw [prog6, afterV_bind_append _ hc, rest6, afterV_bind_append _ ht, afterV_bind_append _ hs,
    afterV_bind_append _ hy, afterV_bind_append _ hb]
  exact hw

/-! ## The node's phases from the runs -/

theorem treeShape_P18 : K.TreeShapeOK P18 := by unfold K.TreeShapeOK; decide

/-- At `P18` the tree phase is `treeProg 19`, its output mapped by `toS`. -/
theorem treeProgS6_P18 (x : Hdr) :
    K.treeProgS6 P18 x = K.treeProg 19 >>= fun out ↦ pure (K.toS 19 x.h out) := by
  rw [K.treeProgS6, if_pos treeShape_P18, if_pos (by decide)]
  rfl

theorem contRows6_eq : SP.contRows6 = rowsBK2 4002 7567 8032 := rfl

/-- At `P18` the sponge phase is the caller, then the link, mapped by `spS`. -/
theorem spongePhase6_P18 (x : Hdr) : SP.spongePhase6 P18 x = SP.spongeBody := by
  rw [SP.spongePhase6, if_pos ⟨by decide, rfl⟩]

variable {M : Mem}

theorem tree_afterV {x : Hdr} {P : K.TreeOut → Prop}
    (h : Runs M (layItems (treeItems 19) aTree) (K.treeProg 19) P)
    (hp : PowLay M (layItems (treeItems 19) aTree)) {vt : List V.Val} (hn : NoRows vt)
    (he : EvMatch M (layItems (treeItems 19) aTree) (vt.map toEv)) :
    ∃ t, afterV (K.treeProgS6 P18 x) vt = some (.ret t) ∧ ∃ o, P o ∧ t = K.toS 19 x.h o := by
  have hR : Runs M (layItems (treeItems 19) aTree ++ []) (K.treeProgS6 P18 x)
      fun t ↦ ∃ o, P o ∧ t = K.toS 19 x.h o := by
    rw [treeProgS6_P18]
    exact runs_bind h fun o ho ↦ runs_pure ⟨o, ho, rfl⟩
  rw [List.append_nil] at hR
  exact afterV_of_runs hR hp hn he

theorem sponge_afterV {x : Hdr} {P : K.SpOut → Prop} {Q : SP.LinkOut → Prop}
    (hs : Runs M (layItems (spItems 13) aSp) (K.spCaller6 13) P)
    (hl : Runs M (layItems (linkItems 13) aLink) (ksLinkProgE2 13 10 (rowsBK2 4002 7567 8032)) Q)
    (hp : PowLay M (layItems (spItems 13 ++ linkItems 13) aSp)) {vs : List V.Val} (hn : NoRows vs)
    (he : EvMatch M (layItems (spItems 13 ++ linkItems 13) aSp) (vs.map toEv)) :
    ∃ s, afterV (SP.spongePhase6 P18 x) vs = some (.ret s) ∧ ∃ o lk, P o ∧ Q lk ∧ s = SP.spS o lk := by
  have hlay : layItems (spItems 13 ++ linkItems 13) aSp =
      layItems (spItems 13) aSp ++ (layItems (linkItems 13) aLink ++ []) := by
    rw [layItems_append, List.append_nil]
    rfl
  have hR : Runs M (layItems (spItems 13 ++ linkItems 13) aSp) (SP.spongePhase6 P18 x)
      fun s ↦ ∃ o lk, P o ∧ Q lk ∧ s = SP.spS o lk := by
    rw [spongePhase6_P18, SP.spongeBody, hlay, contRows6_eq]
    exact runs_bind hs fun o ho ↦ runs_bind hl fun lk hlk ↦ runs_pure ⟨o, lk, ho, hlk, rfl⟩
  exact afterV_of_runs hR hp hn he

theorem typed_afterV {i : Lvm6.Ty.TyInst6} {L : Lvm.M3.Lay} {P : Lvm6.Ty.OpenClaimsE → Prop} {lay : List LEv}
    (hL : L = Lvm6.Ty.L6) (h : Runs M lay (Lvm6.Ty.typedProgE i.Ti L i.pw i.acc) P) (hp : PowLay M lay)
    {vy : List V.Val} (hn : NoRows vy) (he : EvMatch M lay (vy.map toEv)) :
    ∃ ty, afterV (Lvm6.Ty.typedPhase6 P18 i) vy = some (.ret ty) ∧ ∃ o, P o ∧ ty = Lvm6.Ty.claimsOnStack o := by
  subst hL
  have hR : Runs M (lay ++ []) (Lvm6.Ty.typedPhase6 P18 i) fun ty ↦ ∃ o, P o ∧ ty = Lvm6.Ty.claimsOnStack o := by
    rw [Lvm6.Ty.typedPhase6, if_pos (by decide)]
    exact runs_bind h fun o ho ↦ runs_pure ⟨o, ho, rfl⟩
  rw [List.append_nil] at hR
  exact afterV_of_runs hR hp hn he

/-! ## The decision -/

theorem phases6_sponge {ty : Shape → Hdr → VerifierProgram (List StackClaim6)}
    {r : Shape → List SliceClaim → List StackClaim6 → VerifierProgram StackClaim6}
    {w : Shape → StackClaim6 → VerifierProgram Bool} : (phases6 ty r w).sponge = SP.spongePhase6 := rfl

theorem phases6_typed {ty : Shape → Hdr → VerifierProgram (List StackClaim6)}
    {r : Shape → List SliceClaim → List StackClaim6 → VerifierProgram StackClaim6}
    {w : Shape → StackClaim6 → VerifierProgram Bool} : (phases6 ty r w).typed = ty := rfl

/-- The header view `F6` replays `prog6` at: `hdrView` of the proof's first `hdrLen` bytes. -/
def hdrOf6 (π : ByteArray) : Hdr := hdrView P18 ((Lvm.Replay.bl π).take (V.hdrLen (toV P18)))

/-- **The `dec` field from the phase runs** (`node6E_har`'s conclusions at the node's lanes). The value
split `hsplit` with its `EvMatch`/`NoRows`/`PowLay` facts is the stream-lane bridge (NODE §7 (i)); the
commitment phase `hc` (lanes only) and `htail` (CC's ring and opening) are named. The typed run `hY` and
`htail` are taken at the header `F6` replays, `hdrOf6 π` (N4-tail: the typed instance's `pw`, `acc` and the
tree's root claims depend on the header, so a `∀ x` form could not be met). -/
theorem dec_of_runs {tyOf : Hdr → Lvm6.Ty.TyInst6}
    {ring : Shape → List SliceClaim → List StackClaim6 → VerifierProgram StackClaim6}
    {whir : Shape → StackClaim6 → VerifierProgram Bool} {vk : Digest} {π : ByteArray} {acc : List V.NV}
    {L : Lvm.M3.Lay} (hL : L = Lvm6.Ty.L6)
    {Pt : K.TreeOut → Prop} {Ps : K.SpOut → Prop} {Pl : SP.LinkOut → Prop} {Py : Lvm6.Ty.OpenClaimsE → Prop}
    {layY : List LEv}
    (hT : Runs M (layItems (treeItems 19) aTree) (K.treeProg 19) Pt)
    (hS : Runs M (layItems (spItems 13) aSp) (K.spCaller6 13) Ps)
    (hK : Runs M (layItems (linkItems 13) aLink) (ksLinkProgE2 13 10 (rowsBK2 4002 7567 8032)) Pl)
    (hY : Runs M layY (Lvm6.Ty.typedProgE (tyOf (hdrOf6 π)).Ti L (tyOf (hdrOf6 π)).pw (tyOf (hdrOf6 π)).acc) Py)
    {vc vt vs vy vr vo : List V.Val}
    (hsplit : (acc.map (V.NV.val π)).reverse = vc ++ (vt ++ (vs ++ (vy ++ (vr ++ vo)))))
    (hpT : PowLay M (layItems (treeItems 19) aTree)) (hnT : NoRows vt)
    (heT : EvMatch M (layItems (treeItems 19) aTree) (vt.map toEv))
    (hpS : PowLay M (layItems (spItems 13 ++ linkItems 13) aSp)) (hnS : NoRows vs)
    (heS : EvMatch M (layItems (spItems 13 ++ linkItems 13) aSp) (vs.map toEv))
    (hpY : PowLay M layY) (hnY : NoRows vy) (heY : EvMatch M layY (vy.map toEv))
    {c0 : StackClaim6} (hc : afterV (commit6 P18) vc = some (.ret c0))
    (htail : ∀ ot os lk oy, Pt ot → Ps os → Pl lk → Py oy →
      let t := K.toS 19 (hdrOf6 π).h ot; let s := SP.spS os lk; let ty := Lvm6.Ty.claimsOnStack oy
      [t.slices, s.slices].length + (stackedOf c0 t s ty).length ≤ P18.J₀ ∧
      ∃ cl, afterV (ring P18 [t.slices, s.slices] (stackedOf c0 t s ty)) vr = some (.ret cl) ∧
        afterV (whir P18 cl) vo = some (.ret true)) :
    F6 (phases6 (fun sh x ↦ Lvm6.Ty.typedPhase6 sh (tyOf x)) ring whir) P18 vk π acc = true := by
  unfold F6
  rw [hsplit]
  have ex : hdrOf6 π = hdrView P18 ((Lvm.Replay.bl π).take (V.hdrLen (toV P18))) := rfl
  rw [ex] at hY htail
  generalize (Lvm.Replay.bl π).take (V.hdrLen (toV P18)) = xb at hY htail ⊢
  obtain ⟨t, ht, ot, hot, rfl⟩ := tree_afterV (x := hdrView P18 xb) hT hpT hnT heT
  obtain ⟨s, hs, os, lk, hos, hlk, rfl⟩ := sponge_afterV (x := hdrView P18 xb) hS hK hpS hnS heS
  obtain ⟨ty, hy, oy, hoy, rfl⟩ := typed_afterV (i := tyOf (hdrView P18 xb)) hL hY hpY hnY heY
  obtain ⟨hJ, cl, hr, hw⟩ := htail ot os lk oy hot hos hlk hoy
  refine replay_prog6 (phases6 (fun sh x ↦ Lvm6.Ty.typedPhase6 sh (tyOf x)) ring whir) P18 vk xb
    (vc := vc) (vt := vt) (vs := vs) (vy := vy) ?_ ?_ ?_ ?_ hJ hr hw
  · exact hc
  · exact ht
  · rw [phases6_sponge]
    exact hs
  · rw [phases6_typed]
    exact hy

/-! ## The grinds -/

/-- **The PoW rows' conclusion** (SLOT): every ground draw's PoW lane (answer word 2) passes its grind. -/
def PowLanes6 (P : List PE6) (ws : List Word) : Prop :=
  ∀ i < P.length, ∀ st g, (P.getD i default).k = .fs st g → lw ws (ansLane6 P i + 2) < 2 ^ (64 - g)

/-- **`pow` from the PoW lanes.** -/
theorem powOK6_of_lanes {P : List PE6} {ws : List Word} (hS : streamOkL6 P = true)
    (hw : hashedLen6 P ≤ 8 * ws.length) (h : PowLanes6 P ws) : PowOK6 P (decode6 P ws) := by
  intro i hi st g hk
  have ha := aOf_lanes6 hS hw hi
  have hb := ansLane6_bound hS hw (e := i) hi
  have hl : ((ws.drop (ansLane6 P i)).take 4).length = 4 := by
    rw [List.length_take, List.length_drop]; omega
  have e := Lvm.QLink.u64At_digest hl ha (k := 2) (by norm_num)
  rw [Lvm.QLink.lw_of_slice (ws := ws) (a := ansLane6 P i) (n := 4) (l := 2) (by norm_num) (by omega)] at e
  have e2 : Lvm6.Q.powLane (aOf (decode6 P ws) i) = lw ws (ansLane6 P i + 2) := e
  rw [Lvm6.Q.powOK, e2]
  exact decide_eq_true (h i hi st g hk)

/-! ## Link, header, signature -/

/-- **`link`, `hdr`, `sig`** from `childLink6`'s conclusion at `planOf P18` (the `Q_link`/`Q_sig` SLOT),
CB-4's trace digest (the node's sponge rows `hout`, `hlink`) and the digest cells `I.md` = row `B − 1`'s
output lanes. -/
theorem linkHdrSig6 {I : Lvm.QSig.SigIn} {ws : List Word} {B : ℕ} {ks : ℕ → K} {Yl Mx X : ℕ → ℕ → K}
    (hQ : QLinkConcl P6 (digAt M.k I.cL) ws ∧ LaneLink6 P6 (digAt M.k I.cL) ws ∧
      ChildHdr6 (digAt M.k I.vk) (digAt M.k I.cL) (decode6 P6 ws) ∧
      SigOk (digAt M.k I.vk) (digAt M.k I.md) (sigAt' M.k I.sg) = true)
    (hB : B ≤ 7168) (hout : Lvm.KG.OutRel 13 25 ks Yl)
    (hlink : Lvm.KG.SpongeLink 13 (rowsBK2 B 7567 8032) ks (fun i l ↦ Yl l i) (Lvm.KG.ksMsg 7168 Mx X))
    (hBL : B = Lvm.KSponge.nBlk (hashedLen6 P6))
    (hM : ∀ i < 7168, ∀ l < 17, (Mx i l).toBitVec.toNat = lw ws (17 * i + l))
    (hmd : ∀ l < 4, M.k (I.md + l) = FK.ofBF64 (Yl l (B - 1))) :
    LinkOk6 P6 (digAt M.k I.cL) (decode6 P6 ws) ∧ ChildHdr6 (digAt M.k I.vk) (digAt M.k I.cL) (decode6 P6 ws) ∧
      SigOk (digAt M.k I.vk) (traceDigest (decode6 P6 ws)) (sigAt' M.k I.sg) = true := by
  obtain ⟨⟨hlk, hpad⟩, hLL, hH, hsig⟩ := hQ
  have hd := traceDigest6 hB hout hlink streamOkP18 (Nat.lt_of_lt_of_le (by norm_num) P6_two) hLL hpad hBL hM
  have hc : digAt M.k I.md = traceDigest (decode6 P6 ws) := by
    rw [← hd]
    exact digAt_of_cells6 hmd
  exact ⟨hlk, hH, hc ▸ hsig⟩

/-! ## The five fields -/

/-- **`ChildOk` from the node circuit's conclusions**: the `Q_link`/`Q_sig` conclusion and CB-4's trace
digest (`link`, `hdr`, `sig`), the PoW lanes (`pow`), and V1's decision (`dec`, from `dec_of_runs`). -/
theorem childOk_of_node {Φ : Phases} {I : Lvm.QSig.SigIn} {ws : List Word} {B : ℕ} {ks : ℕ → K}
    {Yl Mx X : ℕ → ℕ → K}
    (hQ : QLinkConcl P6 (digAt M.k I.cL) ws ∧ LaneLink6 P6 (digAt M.k I.cL) ws ∧
      ChildHdr6 (digAt M.k I.vk) (digAt M.k I.cL) (decode6 P6 ws) ∧
      SigOk (digAt M.k I.vk) (digAt M.k I.md) (sigAt' M.k I.sg) = true)
    (hB : B ≤ 7168) (hout : Lvm.KG.OutRel 13 25 ks Yl)
    (hlink : Lvm.KG.SpongeLink 13 (rowsBK2 B 7567 8032) ks (fun i l ↦ Yl l i) (Lvm.KG.ksMsg 7168 Mx X))
    (hBL : B = Lvm.KSponge.nBlk (hashedLen6 P6))
    (hM : ∀ i < 7168, ∀ l < 17, (Mx i l).toBitVec.toNat = lw ws (17 * i + l))
    (hmd : ∀ l < 4, M.k (I.md + l) = FK.ofBF64 (Yl l (B - 1)))
    (hpow : PowLanes6 P6 ws)
    (hdec : F6 Φ P18 (digAt M.k I.vk) (reassemble6 P6 (decode6 P6 ws))
      (accOf P18 (reassemble6 P6 (decode6 P6 ws)) (decode6 P6 ws)) = true) :
    ChildOk Φ (digAt M.k I.vk) (digAt M.k I.cL) (decode6 P6 ws) (sigAt' M.k I.sg) := by
  obtain ⟨hlk, hH, hsig⟩ := linkHdrSig6 hQ hB hout hlink hBL hM hmd
  exact ⟨hlk, hH, powOK6_of_lanes streamOkP18 hQ.2.1.size hpow, hdec, hsig⟩

end Lvm6.Node
