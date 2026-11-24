-- New for lvm6 (WP NODE5a). CC's 53 claim gadgets at the deployed inputs `inpReal` compute the placed claims
-- (`ClaimsAt`), and the input cells hold the slice and stacked values (`hval`), from the families' representations.
import Lvm6NodeFin
import Lvm6MultiaffPhases
import Lvm6MultiaffSponge
import Lvm6NodeMbS
import Lvm6NodeTail

/-!
# CC's claims at the deployed inputs (WP NODE5a)

At `I = inpReal o lay z one tv mo` (the cells of `node6E`'s output `o`, CC's `0`/`1` cells, `ccPre`'s tree values
`tv`, `mbPre`'s mini-bus parts and values `mo`):
* **`claimsAt_real`**: `ClaimsAt I M rp sl st` for the placed claims of the represented outputs (`TreeRep`, `SpRep`,
  `LinkRep`, the typed claims of `node6E_har`): claim by claim, CLG's gadget lemmas (`eqClaim_ok`, `ringClaim_ok`,
  `eqBitsClaim_ok`, `cOut_ok`, `cTied_ok`, `cY/cIn/cM/cX_ok`, `relayClaim_ok`, `sigClaim_ok`, `regClaim_ok` with
  the guard's `RegAff`) and MBS's `mbClaimF_ok` with `mbPartsG_pt`; the batch's `MA 24` from `MA_rot`. Inputs
  beyond the representations: claim 0's weight (`Claim0At.w`), the tables (`Ti.mbT = mbTD Ti.lay`), `L.nuMain = 24`.
* **`vals_real`**: `hval`'s two equations (slice values, stacked values), from the cells' lengths (`OutShape`),
  `ccPre`'s values, `mbPre`'s values, claim 0's value (`Claim0At.v`) and the root lanes (`RootLanes`).
* **`hs_ccPre`**: `ccPre`'s HAR (`0`, `1`, `D⁰_m + eq(ρ, 0)·δ_m`). `hsh_real`, `hty_real`: `hsh`, `hty`.
-/

set_option autoImplicit false

namespace Lvm6.Node.Fin

open RecursionFast Lvm Lvm.Replay Lvm6.Q Lvm6.QK Lvm6.Node Lvm6.Node.Split
open LeanVM.Protocol.Compile hiding Proof Bytes Word
open Lvm.Loop Lvm.Loop.Build Lvm.Q2 Lvm.Har Lvm.E2V LeanVM.Parameters

variable {c : Ctx} {M : Mem}

/-! ## Residual facts, by name -/

/-- **The lengths of `node6E`'s output cells** (the tree's and the sponge core's slice points and slices, the
caller's scalars, the link's values, the wiring's point). -/
structure OutShape (o : NodeOutE) : Prop where
  treePt : o.tree.pt.length = 18 + 6
  treeS : o.tree.s.length = 64
  spPt : o.sp.pt.length = 13 + 6
  spS : o.sp.s.length = 64
  spV : o.sp.v.length = 25
  vals : o.link.vals.length = 4
  ry : o.ty.wire.ry.length = Lvm.Typed.yVars

/-- **Claim 0 at the cells** (`commit6`'s output): its point is `z₀`'s cells, its value `y₀`'s. -/
structure Claim0At (M : Mem) (c0 : StackClaim6) : Prop where
  w : ∀ X, eqPt (Dep.inpD.z0.map (ev2 M)) X = c0.1 X
  v : [c0.2] = Dep.inpD.y0.map (ev2 M)

/-- **The root claims' values** (tree claims 11–14): the child header's root lanes are the cells `hdrLaneC (3 + m)`. -/
def RootLanes (M : Mem) (h : Digest) : Prop :=
  ∀ m < 4, K.ofLane (dLane h m) = kv M (Dep.hdrLaneC (3 + m))

/-! ## Helpers -/

theorem forall₂_app {α β : Type} {R : α → β → Prop} {l₁ l₂ : List α} {m₁ m₂ : List β}
    (h₁ : List.Forall₂ R l₁ m₁) (h₂ : List.Forall₂ R l₂ m₂) : List.Forall₂ R (l₁ ++ l₂) (m₁ ++ m₂) := by
  induction h₁ with
  | nil => exact h₂
  | cons h _ ih => exact .cons h ih

theorem forall₂_map_map {α β γ : Type} {R : β → γ → Prop} (l : List α) (f : α → β) (g : α → γ)
    (h : ∀ a ∈ l, R (f a) (g a)) : List.Forall₂ R (l.map f) (l.map g) := by
  induction l with
  | nil => exact .nil
  | cons a l ih => exact .cons (h a List.mem_cons_self) (ih fun b hb ↦ h b (List.mem_cons_of_mem _ hb))

theorem bitsF_hi (a k n : ℕ) : (E2V.bitsF (a * 2 ^ k) (k + n) : List E2) = E2V.bitsF 0 k ++ E2V.bitsF a n := by
  rw [← List.take_append_drop k (E2V.bitsF (a * 2 ^ k) (k + n) : List E2), Mb.bitsF_take _ _ _ (by omega),
    Mb.bitsF_drop _ _ _ (by omega), Nat.add_sub_cancel_left, Nat.mul_div_cancel _ (by positivity),
    show a * 2 ^ k = 0 + 2 ^ k * a by ring, Ty.bitsF_add_mul]

theorem ofFn_getD {α : Type} {n : ℕ} (l : List α) (d : α) (hl : l.length = n) :
    List.ofFn (fun i : Fin n ↦ l.getD i d) = l := by
  subst hl
  apply List.ext_getElem (by simp)
  intro i h1 h2
  simp [List.getD_eq_getElem _ _ h2]

theorem four_getD {α : Type} (l : List α) (d : α) (hl : l.length = 4) :
    [l.getD 0 d, l.getD 1 d, l.getD 2 d, l.getD 3 d] = l := by
  rcases l with _ | ⟨a, _ | ⟨b, _ | ⟨c, _ | ⟨e, _ | ⟨f, l⟩⟩⟩⟩⟩ <;> simp_all

/-- `placeRing` on the stacked claims: claim 0, the tree's ring claim, the 13 tree claims, the sponge's ring claim,
the rest. -/
theorem csOf_eq (M : Mem) (rp : QC.RingPhC) (sa sb : SliceClaim) (c0 : StackClaim6) (t s : TreeOut)
    (ty : List StackClaim6) (ht : t.claims.length = 13) :
    csOf M rp [sa, sb] (stackedOf c0 t s ty) = c0 :: ringOf sa (rp.ft.map (ev2 M)) (rp.gt.map (ev2 M)) ::
      (t.claims ++ ringOf sb (rp.fs.map (ev2 M)) (rp.gs.map (ev2 M)) :: (s.claims ++ ty)) := by
  have e1 : (stackedOf c0 t s ty).take 1 = [c0] := rfl
  have e2 : ((stackedOf c0 t s ty).drop 1).take 13 = t.claims := by
    show (t.claims ++ (s.claims ++ ty)).take 13 = _
    exact List.take_left' ht
  have e3 : (stackedOf c0 t s ty).drop 14 = s.claims ++ ty := by
    show (t.claims ++ (s.claims ++ ty)).drop 13 = _
    exact List.drop_left' ht
  simp only [csOf, placeRing, e1, e2, e3, List.getD_cons_zero, List.getD_cons_succ, List.singleton_append,
    List.cons_append, List.nil_append, List.append_assoc]

theorem toS_claims_len (h : Digest) (ot : K.TreeOut) : (K.toS 18 h ot).claims.length = 13 := by
  simp [K.toS, K.treeColsS]

/-! ## `ccPre` -/

/-- **`ccPre`'s cells**: a zero, a one, and tree claims 3–6's values `D⁰_m + eq(ρ, 0)·δ_m`. -/
theorem hs_ccPre (o : NodeOutE) : Hs c M (Dep.ccPre o) fun pr ↦ ev2 M pr.1 = 0 ∧ ev2 M pr.2.1 = 1 ∧
    pr.2.2.map (ev2 M) = (List.range 4).map fun m ↦
      E2V.eqAtF (o.tree.ρ.map (ev2 M)) 0 * ev2 M ⟨o.tree.δ.getD m pr.1.re, pr.1.re⟩ +
        ev2 M (o.tree.dd.getD m pr.1) := by
  unfold Dep.ccPre
  refine hs_bind (hs_g2Zero _) fun z hz ↦ hs_bind (hs_g2Const 1 z) fun one hone ↦
    hs_bind (QC.hs_eqAtG hz (ev2_one' hone) o.tree.ρ 0) fun e he ↦
      hs_bind (QC.hs_mapB_eq (g := fun m ↦ E2V.eqAtF (o.tree.ρ.map (ev2 M)) 0 *
          ev2 M ⟨o.tree.δ.getD m z.re, z.re⟩ + ev2 M (o.tree.dd.getD m z)) (List.range 4)
        fun m _ ↦ hs_mono (hs_g2Mul _ _ _) fun r hr ↦ ?_) fun tv htv ↦
        hs_pure ⟨QC.ev2_of_zero hz, ev2_one' hone, htv⟩
  rw [ev2_mul hr, he]

/-! ## The claims -/

/-- **Tree claims 2–14** (`treeClaimGs`): the point `(u, ρ, ϱm)`, `ρ ‖ 0 ‖ bits(m, 6)` as `ρ ‖ bits(2m, 7)`, and
the root claims' `bits(0, 18) ‖ bits(4 + m, 6)` as `bits((4 + m)·2^18, 24)`. -/
theorem tree_ok {I : Dep.Inp} {ot : K.TreeOut} (h : Digest)
    (eP2 : I.tPt2.map (ev2 M) = (ot.u :: ot.ρ) ++ ot.hd.ϱm) (eR : I.tRho.map (ev2 M) = ot.ρ) :
    List.Forall₂ (fun G cl ↦ QC.ClaimAt (· = M) cl G) (Dep.treeClaimGs I) (K.toS 18 h ot).claims := by
  have e8 : List.range 8 = List.range 4 ++ (List.range 4).map (4 + ·) := List.range_add (n := 4) (m := 4)
  simp only [Dep.treeClaimGs, K.toS, K.treeColsS, e8, List.map_cons, List.map_append, List.map_map,
    List.cons_append, List.append_assoc]
  refine .cons ?_ (forall₂_app (forall₂_map_map _ _ _ fun m _ ↦ ?_)
    (forall₂_app (forall₂_map_map _ _ _ fun m _ ↦ ?_) (forall₂_map_map _ _ _ fun m _ ↦ ?_)))
  · exact QC.eqClaim_ok (· = M) I.tPt2 _ _ (fun _ hM ↦ by rw [hM]; exact eP2)
  · refine (QC.eqBitsClaim_ok (· = M) I.tRho ot.ρ (2 * m) 7 0 (fun _ hM ↦ by rw [hM]; exact eR)).congr
      fun X ↦ ?_
    show eqPt (ot.ρ ++ E2V.bitsF (2 * m) 7) X = eqPt (ot.ρ ++ 0 :: ([] ++ E2V.bitsF m 6)) X
    rw [show (7 : ℕ) = 6 + 1 from rfl, E2V.bitsF_two_mul, List.nil_append]
  · refine (QC.eqBitsClaim_ok (· = M) I.tRho ot.ρ (2 * (4 + m)) 7 0
      (fun _ hM ↦ by rw [hM]; exact eR)).congr fun X ↦ ?_
    show eqPt (ot.ρ ++ E2V.bitsF (2 * (4 + m)) 7) X = eqPt (ot.ρ ++ 0 :: ([] ++ E2V.bitsF (4 + m) 6)) X
    rw [show (7 : ℕ) = 6 + 1 from rfl, E2V.bitsF_two_mul, List.nil_append]
  · refine (QC.eqBitsClaim_ok (· = M) [] [] ((4 + m) * 2 ^ 18) 24 0 (fun _ _ ↦ rfl)).congr fun X ↦ ?_
    show eqPt ([] ++ E2V.bitsF ((4 + m) * 2 ^ 18) 24) X = eqPt (E2V.bitsF 0 18 ++ E2V.bitsF (4 + m) 6) X
    rw [List.nil_append, show (24 : ℕ) = 18 + 6 from rfl, bitsF_hi]

/-- The typed claims of `node6E_har` at the cells `o`. -/
noncomputable abbrev tyClaims (Ti : Ty.TInst6) (L : Lvm.M3.Lay) (M : Mem) (o : NodeOutE) : Ty.OpenClaimsE :=
  Ty.typedClaimsE Ti (o.ty.wire.ry.map (ev2 M)) (o.ty.wire.rv.map (ev2 M)) (o.ty.relay.rr.map (ev2 M))
    (ev2 M o.ty.relay.vR) ((Mb.mbClaimsG L.nuMain Ti.mbT (QD.busOf M o.ty.mb)).map (·.onStack))

/-- **CC's 53 claim gadgets at the deployed inputs compute the placed claims**, and the batch is affine in its 24
variables. -/
theorem claimsAt_real {o : NodeOutE} {Ti : Ty.TInst6} {L : Lvm.M3.Lay} {z one : C2} {tv : List C2}
    {mo : List (List (C2 × LeanVM.Protocol.Verifier.Placement × List C2)) × List C2} {h : Digest}
    {c0 : StackClaim6} {ot : K.TreeOut} {os : K.SpOut} {lk : SP.LinkOut}
    (hok : Ti.Ok) (hlay : QD.TyLayOk Ti)
    (hcom : QC.RegAff Ti .com Ti.comW (Dep.regsOf Ti.lay .com))
    (hks : QC.RegAff Ti .ks Ti.ksW (Dep.regsOf Ti.lay .ks))
    (hmbT : Ti.mbT = Dep.mbTD Ti.lay) (hnu : L.nuMain = 24)
    (hz : ev2 M z = 0) (hone : ev2 M one = 1)
    (hmo : mo.1.map (QC.partsV M) = (List.range 3).map (Mb.mbPartsG (Dep.mbTD Ti.lay)
      (Mb.busResG (Dep.mbTD Ti.lay) (QD.busOf M o.ty.mb))))
    (hry : o.ty.wire.ry.length = Lvm.Typed.yVars) (h0 : ∀ X, eqPt (Dep.inpD.z0.map (ev2 M)) X = c0.1 X)
    (hT : TreeRep M o.tree ot) (hS : SpRep M o.sp os) (hK : LinkRep M o.link lk)
    (hpt : ot.en.pt.length = 18 + 6) (hps : os.2.2.2.pt.length = 13 + 6) (rp : QC.RingPhC) :
    ClaimsAt (Dep.inpReal o Ti.lay z one tv mo) M rp [(K.toS 18 h ot).slices, (SP.spS os lk).slices]
      (stackedOf c0 (K.toS 18 h ot) (SP.spS os lk) (Ty.claimsOnStack (tyClaims Ti L M o))) := by
  -- the record's fields
  have eZ0 : (Dep.inpReal o Ti.lay z one tv mo).z0 = Dep.inpD.z0 := by simp only [Dep.inpReal]
  have eTX : (Dep.inpReal o Ti.lay z one tv mo).treeX = o.tree.pt := by simp only [Dep.inpReal]
  have eP2 : (Dep.inpReal o Ti.lay z one tv mo).tPt2 = (o.tree.u :: o.tree.ρ) ++ o.tree.ϱm := by
    simp only [Dep.inpReal]
  have eTR : (Dep.inpReal o Ti.lay z one tv mo).tRho = o.tree.ρ := by simp only [Dep.inpReal]
  have eSX : (Dep.inpReal o Ti.lay z one tv mo).spX = o.sp.pt ++ QC.bitC z one 17 5 := by simp only [Dep.inpReal]
  have eRS : (Dep.inpReal o Ti.lay z one tv mo).rS = o.sp.r := by simp only [Dep.inpReal]
  have eRM : (Dep.inpReal o Ti.lay z one tv mo).rhoM = o.sp.ϱm := by simp only [Dep.inpReal]
  have eRP : (Dep.inpReal o Ti.lay z one tv mo).rhoP = o.link.shift := by simp only [Dep.inpReal]
  have eLL : (Dep.inpReal o Ti.lay z one tv mo).lamL = o.link.kchal.drop 13 := by simp only [Dep.inpReal]
  have eRY : (Dep.inpReal o Ti.lay z one tv mo).rY = o.ty.wire.ry := by simp only [Dep.inpReal]
  have eRR : (Dep.inpReal o Ti.lay z one tv mo).rrc = o.ty.relay.rr := by simp only [Dep.inpReal]
  have eSB : (Dep.inpReal o Ti.lay z one tv mo).sigB = Dep.sigBgOf Ti.lay := by simp only [Dep.inpReal]
  have eCQ : (Dep.inpReal o Ti.lay z one tv mo).comQs = QC.regQs (Dep.regsOf Ti.lay .com) := by
    simp only [Dep.inpReal]
  have eKQ : (Dep.inpReal o Ti.lay z one tv mo).ksQs = QC.regQs (Dep.regsOf Ti.lay .ks) := by
    simp only [Dep.inpReal]
  have eMB : (Dep.inpReal o Ti.lay z one tv mo).mbP = mo.1 := by simp only [Dep.inpReal]
  -- the representations
  obtain ⟨-, hρ, -, hu, hϱ, -, hpT, -⟩ := hT
  obtain ⟨hr, -, hϱs, -, hpS, -⟩ := hS
  obtain ⟨hkc, hsft, -, -⟩ := hK
  obtain ⟨⟨bs, bg, -, hfσ, -, hwσ⟩, -, -⟩ := hlay
  have hσb : Dep.sigBgOf Ti.lay = bg := by simp [Dep.sigBgOf, hfσ]
  have hpt' : ot.en.pt.length = 24 := hpt
  have hps' : (SP.spS os lk).slices.pt.length = 24 := by
    show (os.2.2.2.pt ++ E2V.bitsF 17 5).length = 24
    rw [List.length_append, hps, E2V.bitsF_length]
  have hlog : ∀ s, ∀ p ∈ Dep.regsOf Ti.lay s, p.1.log ≤ (o.ty.wire.ry.map (ev2 M)).length := by
    intro s p hp
    obtain ⟨r, hr', rfl⟩ := List.mem_map.mp hp
    rw [List.length_map, hry]
    exact QD.ok_log hok r (List.mem_filter.mp hr').1
  have hTX : (Dep.inpReal o Ti.lay z one tv mo).treeX.map (ev2 M) = ot.en.pt := by rw [eTX, hpT]
  have hc0w : QC.ClaimAt (· = M) c0 (QC.eqClaimG Dep.inpD.z0) := by
    intro c' M' hP x gate _
    rw [hP]
    refine hsA_of_hs (hs_mono (QC.hs_eqClaimG Dep.inpD.z0 x gate) fun r hr ↦ ?_)
    rw [hr, h0]
  have hcs := csOf_eq M rp (K.toS 18 h ot).slices (SP.spS os lk).slices c0 _ (SP.spS os lk)
    (Ty.claimsOnStack (tyClaims Ti L M o)) (toS_claims_len h ot)
  refine ⟨?_, ?_⟩
  · rw [hcs]
    simp only [Dep.claimGs, SP.spS, tyClaims, Ty.claimsOnStack, Ty.typedClaimsE, Mb.mbClaimsG, List.map_cons,
      List.map_nil, List.map_map, List.cons_append, List.nil_append, List.append_assoc]
    refine .cons ?_ (.cons ?_ (forall₂_app (tree_ok h (by rw [eP2, List.map_append, List.map_cons, hu, hρ, hϱ])
      (by rw [eTR, hρ])) (.cons ?_ (.cons ?_ (forall₂_app (forall₂_map_map _ _ _ fun l _ ↦ ?_)
        (.cons ?_ (.cons ?_ (.cons ?_ (.cons ?_ (.cons ?_ (.cons ?_ (.cons ?_ (.cons ?_
          (forall₂_map_map _ _ _ fun s hs ↦ ?_))))))))))))))
    -- claim 0
    · rw [eZ0]
      exact hc0w
    -- the tree's ring claim
    · have hR := QC.ringClaim_ok (· = M) 24 (Dep.inpReal o Ti.lay z one tv mo).treeX rp.ft rp.gt ot.en.pt
        (List.ofFn (K.toS 18 h ot).slices.s) (rp.ft.map (ev2 M)) (rp.gt.map (ev2 M))
        (fun _ hM ↦ by rw [hM]; exact ⟨hTX, rfl, rfl⟩)
      refine hR.congr fun X ↦ ?_
      show _ = (Ring.ringClaim ot.en.pt.length ot.en.pt _ [] _ _).1 X
      rw [hpt'] <;> rfl
    -- the sponge's ring claim
    · have hSX : (Dep.inpReal o Ti.lay z one tv mo).spX.map (ev2 M) = (SP.spS os lk).slices.pt := by
        rw [eSX, List.map_append, hpS, QC.bitC_map hz hone] <;> rfl
      have hR := QC.ringClaim_ok (· = M) 24 (Dep.inpReal o Ti.lay z one tv mo).spX rp.fs rp.gs
        (SP.spS os lk).slices.pt (List.ofFn (SP.spS os lk).slices.s) (rp.fs.map (ev2 M)) (rp.gs.map (ev2 M))
        (fun _ hM ↦ by rw [hM]; exact ⟨hSX, rfl, rfl⟩)
      refine hR.congr fun X ↦ ?_
      show _ = (Ring.ringClaim (SP.spS os lk).slices.pt.length (SP.spS os lk).slices.pt _ [] _ _).1 X
      rw [hps'] <;> rfl
    -- claim 16
    · exact QC.cOut_ok (· = M) os _ (fun _ hM ↦ by rw [hM]; rw [eRS, eRM, List.map_append, hr, hϱs])
    -- claims 17–41
    · exact QC.cTied_ok (· = M) os l _ (fun _ hM ↦ by rw [hM]; rw [eRS, hr])
    -- claims 42–45
    · exact QC.cY_ok (· = M) lk _ _ (fun _ hM ↦ by rw [hM]; exact ⟨by rw [eLL, List.map_drop, hkc], by rw [eRP, hsft]⟩)
    · exact QC.cIn_ok (· = M) lk _ _ (fun _ hM ↦ by rw [hM]; exact ⟨by rw [eLL, List.map_drop, hkc], by rw [eRP, hsft]⟩)
    · exact QC.cM_ok (· = M) lk _ _ (fun _ hM ↦ by rw [hM]; exact ⟨by rw [eLL, List.map_drop, hkc], by rw [eRP, hsft]⟩)
    · exact QC.cX_ok (· = M) lk _ _ (fun _ hM ↦ by
        rw [hM]; exact ⟨by rw [eLL, List.map_drop, hkc], by rw [eRP, List.map_take, hsft]⟩)
    -- claim 46
    · exact QC.relayClaim_ok (· = M) _ _ _ (fun _ hM ↦ by rw [hM]; rw [eRR])
    -- claim 47
    · have hg := QC.sigClaim_ok (· = M) Ti hok bg hfσ hwσ (Dep.inpReal o Ti.lay z one tv mo).rY
        (o.ty.wire.ry.map (ev2 M)) ((o.ty.wire.rv.map (ev2 M)).getD 2 0)
        (by rw [List.length_map, hry]; decide) (fun _ hM ↦ by rw [hM]; rw [eRY])
      rw [← hσb, ← eSB] at hg
      exact hg
    -- claims 48, 49
    · have hg := QC.regClaim_ok (· = M) Ti .com Ti.comW _ hcom (Dep.inpReal o Ti.lay z one tv mo).rY
        (o.ty.wire.ry.map (ev2 M)) ((o.ty.wire.rv.map (ev2 M)).getD 0 0) (hlog .com) (fun _ hM ↦ by rw [hM]; rw [eRY])
      rw [← eCQ] at hg
      exact hg
    · have hg := QC.regClaim_ok (· = M) Ti .ks Ti.ksW _ hks (Dep.inpReal o Ti.lay z one tv mo).rY
        (o.ty.wire.ry.map (ev2 M)) ((o.ty.wire.rv.map (ev2 M)).getD 3 0) (hlog .ks) (fun _ hM ↦ by rw [hM]; rw [eRY])
      rw [← eKQ] at hg
      exact hg
    -- claims 50–52
    · have hp : QC.partsV M (Dep.mbQs (Dep.inpReal o Ti.lay z one tv mo) s) =
          Mb.mbPartsG Ti.mbT (Mb.busResG Ti.mbT (QD.busOf M o.ty.mb)) s := by
        have gd : ∀ (l : List (List (C2 × LeanVM.Protocol.Verifier.Placement × List C2))) (i : ℕ),
            QC.partsV M (l.getD i []) = (l.map (QC.partsV M)).getD i [] := by
          intro l i
          rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, List.getElem?_map]
          cases l[i]? <;> rfl
        rw [Dep.mbQs, eMB, gd, hmo, hmbT]
        exact QC.getD_range_map _ _ (List.mem_range.mp hs)
      have hg := MbS.mbClaimF_ok (· = M) 24 (Dep.mbQs (Dep.inpReal o Ti.lay z one tv mo) s) _
        (Mb.mbValueG Ti.mbT (Mb.busResG Ti.mbT (QD.busOf M o.ty.mb)) s) (Mb.busResG Ti.mbT (QD.busOf M o.ty.mb)).point
        (fun _ hM ↦ by rw [hM]; exact hp) (MbS.mbPartsG_pt _ _ s)
      show QC.ClaimAt (· = M) (Mb.sumClaimG L.nuMain _ _).onStack _
      rw [hnu]
      exact hg
  · rw [hcs]
    refine MA_rot (isMA_batch _ _ fun cl hcl ↦ ?_) 24 6
    simp only [List.mem_cons, List.mem_append] at hcl
    rcases hcl with rfl | rfl | hcl | rfl | hcl | hcl
    · exact (fun ν ↦ (isMA_eqPt _ ν).congr (fun p _ ↦ h0 p))
    · exact isMA_ringOf _ _ _
    · simp only [K.toS, List.mem_map] at hcl
      obtain ⟨c', -, rfl⟩ := hcl
      exact (fun ν ↦ isMA_eqPt _ ν)
    · exact isMA_ringOf _ _ _
    · simp only [SP.spS, List.mem_cons, List.mem_append, List.mem_map, List.mem_range, List.not_mem_nil,
        or_false] at hcl
      rcases hcl with rfl | ⟨l, -, rfl⟩ | rfl | rfl | rfl | rfl
      · exact (fun ν ↦ isMA_eqPt _ ν)
      · exact (fun ν ↦ isMA_eqPt _ ν)
      all_goals
        intro ν
        dsimp only [SP.cY, SP.cIn, SP.cM, SP.cX]
        exact isMA_finsetSum _ _ fun _ _ ↦ (isMA_eqPt _ _).smul _
    · simp only [tyClaims, Ty.claimsOnStack, Ty.typedClaimsE, List.map_cons, List.map_nil, List.mem_append,
        List.mem_cons, List.not_mem_nil, or_false] at hcl
      rcases hcl with (rfl | rfl) | ((rfl | rfl) | hcl)
      · exact isMA_above _ (isMA_above _ (isMA_eqEvalF _))
      · exact isMA_above _ (isMA_regClaimE _ _ _ _ _)
      · exact isMA_regClaimE _ _ _ _ _
      · exact isMA_regClaimE _ _ _ _ _
      · obtain ⟨c', hc', rfl⟩ := List.mem_map.mp hcl
        unfold Mb.mbClaimsG at hc'
        obtain ⟨s, -, rfl⟩ := List.mem_map.mp hc'
        exact isMA_above _ (isMA_sumClaimG _ _ _)

/-! ## The values, the shapes, the typed count -/

/-- **`hval` at the deployed inputs**: the slice values are the cells `o.tree.s`, `o.sp.s`; the stacked claims'
values are `inpReal`'s `vs` (claim 0's `y₀`, the tree's, the sponge's, the typed values, the mini-bus values). -/
theorem vals_real {o : NodeOutE} {Ti : Ty.TInst6} {L : Lvm.M3.Lay} {z one : C2} {tv : List C2}
    {mo : List (List (C2 × LeanVM.Protocol.Verifier.Placement × List C2)) × List C2} {h : Digest}
    {c0 : StackClaim6} {ot : K.TreeOut} {os : K.SpOut} {lk : SP.LinkOut}
    (hsh : OutShape o) (hmbT : Ti.mbT = Dep.mbTD Ti.lay) (hz : ev2 M z = 0)
    (htv : tv.map (ev2 M) = (List.range 4).map fun m ↦
      E2V.eqAtF (o.tree.ρ.map (ev2 M)) 0 * ev2 M ⟨o.tree.δ.getD m z.re, z.re⟩ + ev2 M (o.tree.dd.getD m z))
    (hmv : mo.2.map (ev2 M) = (List.range 3).map (Mb.mbValueG (Dep.mbTD Ti.lay)
      (Mb.busResG (Dep.mbTD Ti.lay) (QD.busOf M o.ty.mb))))
    (h0 : [c0.2] = Dep.inpD.y0.map (ev2 M)) (hroot : RootLanes M h)
    (hT : TreeRep M o.tree ot) (hS : SpRep M o.sp os) (hK : LinkRep M o.link lk) :
    [List.ofFn (K.toS 18 h ot).slices.s, List.ofFn (SP.spS os lk).slices.s] =
        [(Dep.inpReal o Ti.lay z one tv mo).svT.map (ev2 M), (Dep.inpReal o Ti.lay z one tv mo).svS.map (ev2 M)] ∧
      (stackedOf c0 (K.toS 18 h ot) (SP.spS os lk) (Ty.claimsOnStack (tyClaims Ti L M o))).map (·.2) =
        (Dep.inpReal o Ti.lay z one tv mo).vs.map (ev2 M) := by
  obtain ⟨hδ, hρ, hdd, -, -, hco, -, hsT⟩ := hT
  obtain ⟨-, hv, -, hcs, -, hsS⟩ := hS
  obtain ⟨-, -, -, hvals⟩ := hK
  have hzk : kv M z.re = 0 := QC.kv_re_zero hz
  have eK : ∀ x : Cell, ev2 M ⟨x, z.re⟩ = kF (kv M x) := fun x ↦ by rw [QC.ev2_mk, hzk]; rfl
  have eSV : (Dep.inpReal o Ti.lay z one tv mo).svT = o.tree.s := by simp only [Dep.inpReal]
  have eSS : (Dep.inpReal o Ti.lay z one tv mo).svS = o.sp.s := by simp only [Dep.inpReal]
  have eVS : (Dep.inpReal o Ti.lay z one tv mo).vs = Dep.inpD.y0 ++ [o.tree.cout] ++ tv ++
      ((List.range 4).map fun m ↦ o.tree.dd.getD (4 + m) z) ++
      ((List.range 4).map fun m ↦ (⟨Dep.hdrLaneC (3 + m), z.re⟩ : C2)) ++ [o.sp.cout] ++ o.sp.v ++
      o.link.vals ++ [o.ty.relay.vR, o.ty.wire.rv.getD 2 z, o.ty.wire.rv.getD 0 z, o.ty.wire.rv.getD 3 z] ++
      mo.2 := by simp only [Dep.inpReal]
  have gE : ∀ (l : List C2) (k : ℕ), (l.map (ev2 M)).getD k 0 = ev2 M (l.getD k z) := fun l k ↦ by
    rw [← hz, List.getD_map]
  refine ⟨?_, ?_⟩
  · rw [eSV, eSS]
    show [List.ofFn fun i : Fin 64 ↦ ot.en.s.getD i 0, List.ofFn fun i : Fin 64 ↦ os.2.2.2.s.getD i 0] = _
    rw [ofFn_getD _ _ (by rw [← hsT, List.length_map, hsh.treeS]), ofFn_getD _ _ (by rw [← hsS, List.length_map,
      hsh.spS]), hsT, hsS]
  -- the tree's values
  have eT : (K.toS 18 h ot).claims.map (·.2) = ([o.tree.cout] ++ tv ++
      ((List.range 4).map fun m ↦ o.tree.dd.getD (4 + m) z) ++
      ((List.range 4).map fun m ↦ (⟨Dep.hdrLaneC (3 + m), z.re⟩ : C2))).map (ev2 M) := by
    simp only [K.toS, K.treeColsS, List.map_map, List.map_cons, List.map_append, List.map_nil, htv,
      List.cons_append, List.nil_append, List.append_assoc]
    refine congrArg₂ List.cons hco.symm (congrArg₂ (· ++ ·) ?_ (congrArg₂ (· ++ ·) ?_ ?_))
    · refine List.map_congr_left fun m _ ↦ ?_
      simp only [Function.comp_apply]
      rw [eK, ← hdd, ← hρ, ← hδ, ← hzk, List.getD_map, gE]
      ring
    · refine List.map_congr_left fun m _ ↦ ?_
      simp only [Function.comp_apply]
      rw [← hdd, gE]
    · refine List.map_congr_left fun m hm ↦ ?_
      simp only [Function.comp_apply]
      rw [eK, hroot m (List.mem_range.mp hm)]
  -- the sponge's values
  have eS : (SP.spS os lk).claims.map (·.2) = ([o.sp.cout] ++ o.sp.v ++ o.link.vals).map (ev2 M) := by
    have hv25 : (List.range 25).map (fun l ↦ os.2.1.getD l 0) = os.2.1 := by
      have hl : os.2.1.length = 25 := by rw [← hv, List.length_map, hsh.spV]
      have := QC.map_range_getD id os.2.1 0
      rw [hl] at this
      simpa using this
    have hv4 : [lk.2.2.getD 0 0, lk.2.2.getD 1 0, lk.2.2.getD 2 0, lk.2.2.getD 3 0] = lk.2.2 :=
      four_getD _ _ (by rw [← hvals, List.length_map, hsh.vals])
    simp only [SP.spS, SP.cOut, SP.cTied, SP.cY, SP.cIn, SP.cM, SP.cX, Function.comp_def, List.map_cons,
      List.map_append, List.map_map, List.map_nil, List.cons_append, List.nil_append, List.append_assoc]
    rw [hv25, hv4, ← hcs, ← hv, ← hvals]
  -- the typed values
  have eY : (Ty.claimsOnStack (tyClaims Ti L M o)).map (·.2) = ([o.ty.relay.vR, o.ty.wire.rv.getD 2 z,
      o.ty.wire.rv.getD 0 z, o.ty.wire.rv.getD 3 z] ++ mo.2).map (ev2 M) := by
    simp only [tyClaims, Ty.claimsOnStack, Ty.typedClaimsE, Mb.mbClaimsG, List.map_cons, List.map_nil,
      List.map_append, List.map_map, List.cons_append, List.nil_append, hmv, hmbT, gE]
    rfl
  rw [eVS]
  simp only [stackedOf, List.map_cons, List.map_append, eT, eS, eY, List.append_assoc, List.singleton_append,
    List.cons_append, List.map_nil, List.nil_append, ← h0]

/-- **`hsh` from the cells' lengths.** -/
theorem hsh_real {o : NodeOutE} (hsh : OutShape o) {ot : K.TreeOut} {os : K.SpOut} (hT : TreeRep M o.tree ot)
    (hS : SpRep M o.sp os) : ot.en.pt.length = 18 + 6 ∧ os.2.2.2.pt.length = 13 + 6 := by
  obtain ⟨-, -, -, -, -, -, hpT, -⟩ := hT
  obtain ⟨-, -, -, -, hpS, -⟩ := hS
  rw [← hpT, ← hpS, List.length_map, List.length_map]
  exact ⟨hsh.treePt, hsh.spPt⟩

/-- **`hty`**: at most 7 typed claims (four, and the mini-bus's three). -/
theorem hty_real (Ti : Ty.TInst6) (L : Lvm.M3.Lay) (o : NodeOutE) :
    (Ty.claimsOnStack (tyClaims Ti L M o)).length ≤ 7 := by
  rw [tyClaims, typed_len, mbClaims_len] <;> omega

end Lvm6.Node.Fin
