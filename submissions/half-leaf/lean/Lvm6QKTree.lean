-- New for lvm6 (WP CB). The two Keccak batches of the node circuit assembled from their parts:
-- CB-1 (the tree batch, FORMAT6 §6.2 rows 1–10) and CB-2 (the sponge caller and its core, §6.3),
-- each the head, the 12 layers, the middle-state opening and the input end, in stream order.
import Lvm6QKLay
import Lvm6QKEnd
import Lvm6QKSpHead

/-!
# CB-1 and CB-2 (assembly)

* **`treeG6 κ a gate`**: `treeHeadG`, then `layers6G` on the first claim (`claim0`: value and `μ`
  from the head, point `(u :: ρ).drop 4 ++ [r_seg]`, weights `first r_lane`), then `treeMidG`
  (slots `8 + ℓ`), then the input end `treeEndG`; lanes from `a`, each part at the `layEnd` of the
  items before it (`treeItems_split`). **`treeHar : TreeHarStmt treeG6`**.
* **`spG6 h a gate`**: the same on the sponge head (`spHeadG`; slots `25 + ℓ`, end `spEndG`).
  **`spHar : SpHarStmt spG6`**.

The programs are regrouped (`treeRest_eq`, `spRest_eq`) so that the middle-state opening is
`midProg` and the layers run at `κ` (not `κ − 4 + 4`).
-/

set_option autoImplicit false

namespace Lvm6.QK

open LeanVM.Parameters LeanVM.Protocol.Compile LeanVM.Protocol.Verifier
open LeanVM.Protocol.KeccakGkr (Shape)
open Lvm Lvm.Loop Lvm.Loop.Build Lvm.Q2 Lvm.Har Lvm.E2V Lvm6.K Lvm6.KPack
open Lvm6 (Item rep rnd)

variable {c : Ctx} {M : Mem}

/-! ## Combinators -/

/-- Two postconditions of one run (the program is deterministic). -/
theorem runs_and {β : Type} {lay : List LEv} {p : VerifierProgram β} {P Q : β → Prop}
    (hP : Runs M lay p P) (hQ : Runs M lay p Q) : Runs M lay p fun b ↦ P b ∧ Q b := fun hp evs he ↦ by
  obtain ⟨o1, h1, hP1⟩ := hP hp evs he
  obtain ⟨o2, h2, hQ2⟩ := hQ hp evs he
  rw [h1] at h2
  cases h2
  exact ⟨o1, h1, hP1, hQ2⟩

/-- A family of gadget facts, one for each hypothesis-satisfying index. -/
theorem hsA_forall {α ι : Type} {g : BM α} {R : ι → Prop} {Q : ι → α → Prop}
    (h : ∀ i, R i → HsA c M g (Q i)) : HsA c M g fun o ↦ ∀ i, R i → Q i o :=
  fun p hh ha i hi ↦ h i hi p hh ha

theorem ev2_headD_of {l : List C2} {L : List E2} (h : l.map (ev2 M) = L) (hl : 0 < L.length) :
    ev2 M (l.headD default) = L.headD 0 := by
  cases l with
  | nil => subst h; simp at hl
  | cons x xs => subst h; rfl

/-! ## CB-1: the tree batch -/

/-- The items of the tree batch, part by part. -/
theorem treeItems_split (κ : ℕ) :
    treeItems κ = headItems κ ++ (rep 12 (P18.layer κ) ++ (midItems ++ treeEndItems)) := by
  simp only [treeItems, Shape.treePart, Shape.keccakCore, headItems, midItems, treeEndItems,
    List.cons_append, List.nil_append, List.append_assoc, show κ - 1 - 1 = κ - 2 by omega]
  rfl

/-- `treeRest` with the middle-state opening as `midProg` and the layers at `κ`. -/
theorem treeRest_eq (κ : ℕ) (hκ : 5 ≤ κ) (v : HeadV) : treeRest κ v =
    layers6 κ (List.range 12)
      (firstClaimSF Shape.v1 (v.2.2.2.1 :: v.2.1) (v.2.2.2.2.2.1.take 1) (v.2.2.2.2.2.1.drop 1)
        (oLow v.2.2.2.1 v.2.2.1 ++ v.2.2.2.2.1) v.2.2.2.2.2.2) >>= fun claim ↦
    midProg 8 (v.2.2.2.2.2.1.headD 0) (v.2.2.2.2.2.1.drop 1) v.2.2.2.2.2.2 >>= fun r ↦
    treeEnd6 (κ - 4) claim >>= fun en ↦
    pure ⟨v.1, v.2.1, v.2.2.1, v.2.2.2.1, oLow v.2.2.2.1 v.2.2.1 ++ v.2.2.2.2.1,
      ⟨v.2.2.2.2.2.1, v.2.2.2.2.2.2, claim, r.1, r.2⟩, en⟩ := by
  simp only [treeRest, midProg, bind_assoc, pure_bind, Nat.sub_add_cancel (by omega : 4 ≤ κ)]

/-- The first claim's cells (value and `μ` from the head; the point and the lane cells). -/
def claim0 (value : C2) (mu inst sl : List C2) : ClaimC := ⟨value, mu, inst.drop 4 ++ sl.take 1, .first (sl.drop 1)⟩

theorem claim0_rep (value : C2) (mu inst sl : List C2) (cst : E2) (out : List E2)
    (hmu : mu.map (ev2 M) = (firstClaimSF Shape.v1 (inst.map (ev2 M)) ((sl.map (ev2 M)).take 1)
      ((sl.map (ev2 M)).drop 1) out cst).mu)
    (hv : ev2 M value = (firstClaimSF Shape.v1 (inst.map (ev2 M)) ((sl.map (ev2 M)).take 1)
      ((sl.map (ev2 M)).drop 1) out cst).value) :
    ClaimRep M (claim0 value mu inst sl)
      (firstClaimSF Shape.v1 (inst.map (ev2 M)) ((sl.map (ev2 M)).take 1) ((sl.map (ev2 M)).drop 1) out cst) :=
  ⟨hv, hmu, by simp [claim0, firstClaimSF, List.map_drop, List.map_take], by
    simp [claim0, wOf, firstClaimSF]⟩

/-- **The tree batch gadget** for `2^κ` rows, lanes from `a`. -/
def treeG6 (κ a : ℕ) (gate : Cell) : BM TreeOutC :=
  let q1 := layEnd (headItems κ) a
  let q2 := layEnd (rep 12 (P18.layer κ)) q1
  treeHeadG κ a >>= fun hd ↦
  layers6G κ q1 (claim0 hd.value hd.mu (hd.u :: hd.ρ) hd.sl) gate >>= fun cl ↦
  treeMidG 8 q2 hd.cst (hd.sl.headD default) hd.lanes gate >>= fun om ↦
  En.treeEndG κ (layEnd midItems q2) cl gate >>= fun en ↦
  pure ⟨hd.δ, hd.ρ, hd.dd, hd.u, om.1, om.2, en.2.1, en.2.2⟩

/-- **CB-1: the tree batch gadget re-executes `treeProg κ`.** -/
theorem treeHar : TreeHarStmt treeG6 := by
  refine fun κ hκ a gate ↦ (har_iff _ _ _ _ _).2 fun c M hg ↦ ?_
  rw [treeItems_split κ, layItems_append, layItems_append, layItems_append, treeProg_head]
  unfold treeG6
  refine hsA_bind (hsA_of_hs (treeHead_runs (c := c) (M := M) κ a)) fun hd hhd ↦ ?_
  refine hsA_mono (hsA_forall (R := fun v ↦ HeadRep M hd v ∧ v = headVals M κ a) fun v hv ↦ ?_)
    fun o h ↦ runs_bind (runs_and hhd (runs_treeHead M κ a)) h
  obtain ⟨⟨hδ, hρ, hdd, hu, ho, hsl, hcst, hlan, hmu, hval⟩, hvv⟩ := hv
  have hsl6 : v.2.2.2.2.2.1.length = 6 := by rw [hvv]; simp [headVals, draws]
  have hρl : v.2.1.length = κ - 1 := by rw [hvv]; simp [headVals, draws]; omega
  have hrep0 := claim0_rep (M := M) hd.value hd.mu (hd.u :: hd.ρ) hd.sl v.2.2.2.2.2.2
    (oLow v.2.2.2.1 v.2.2.1 ++ v.2.2.2.2.1)
    (by rw [hmu, List.map_cons, hu, hρ, hsl]) (by rw [hval, List.map_cons, hu, hρ, hsl])
  rw [List.map_cons, hu, hρ, hsl] at hrep0
  have hpt0 : (claim0 hd.value hd.mu (hd.u :: hd.ρ) hd.sl).point.length = κ - 3 := by
    have h1 := congrArg List.length hρ
    have h2 := congrArg List.length hsl
    simp only [List.length_map] at h1 h2
    simp only [claim0, List.length_append, List.length_drop, List.length_take, List.length_cons]
    omega
  rw [treeRest_eq κ hκ]
  refine hsA_bind (layers6G_runs κ hκ _ _ gate hg hpt0 _ hrep0) fun cl hcl ↦ ?_
  have hmid := treeMid_har (c := c) (M := M) 8 (layEnd (rep 12 (P18.layer κ)) (layEnd (headItems κ) a))
    (by norm_num) hd.cst (hd.sl.headD default) hd.lanes (v.2.2.2.2.2.1.drop 1) (by simp [hsl6]) hlan gate hg
  rw [hcst, ev2_headD_of hsl (by omega)] at hmid
  refine hsA_bind hmid fun om hom ↦ ?_
  refine hsA_bind (hsA_forall (R := fun cl' ↦ ClaimRep M cl cl' ∧ cl.point.length = κ - 3 ∧ LtS cl.w)
    fun cl' h ↦ En.treeEnd_har κ hκ _ cl gate c M hg h.2.1 h.2.2 cl' h.1) fun en hen ↦ hsA_pure ?_
  refine runs_bind hcl fun cl' hcl' ↦ runs_bind hom fun r hr ↦
    runs_bind' (List.append_nil _).symm (hen cl' hcl') fun e he ↦ runs_pure ?_
  exact ⟨hδ, hρ, hdd, hu, hr.1.symm, hr.2.symm, he.2.1, he.2.2⟩

/-! ## CB-2: the sponge caller and its core -/

/-- The items of the sponge caller and its core, part by part. -/
theorem spItems_split (h : ℕ) :
    spItems h = spHeadItems h ++ (rep 12 (P18.layer h) ++ (midItems ++ spEndItems)) := by
  simp only [spItems, spCallerItems, coreItems, Shape.keccakCore, spHeadItems, midItems, spEndItems,
    List.cons_append, List.nil_append, List.append_assoc]
  rfl

/-- `spRest` with the middle-state opening as `midProg` and the layers at `h`. -/
theorem spRest_eq (h : ℕ) (hh : 5 ≤ h) (x : SpHeadV) : spRest h x =
    layers6 h (List.range 12)
      (firstClaimSF Shape.v1 x.1 (x.2.2.1.take 1) (x.2.2.1.drop 1) x.2.1 x.2.2.2) >>= fun claim ↦
    midProg 25 (x.2.2.1.headD 0) (x.2.2.1.drop 1) x.2.2.2 >>= fun r ↦
    spongeEnd6 (h - 4) claim >>= fun en ↦
    pure (x.1, x.2.1, (⟨x.2.2.1, x.2.2.2, claim, r.1, r.2⟩, en)) := by
  simp only [spRest, midProg, bind_assoc, pure_bind, Nat.sub_add_cancel (by omega : 4 ≤ h)]

/-- **The sponge caller gadget** for `2^h` rows, lanes from `a`. -/
def spG6 (h a : ℕ) (gate : Cell) : BM SpOutC :=
  let q1 := layEnd (spHeadItems h) a
  let q2 := layEnd (rep 12 (P18.layer h)) q1
  spHeadG h a >>= fun hd ↦
  layers6G h q1 (claim0 hd.value hd.mu hd.r hd.sl) gate >>= fun cl ↦
  treeMidG 25 q2 hd.cst (hd.sl.headD default) hd.lanes gate >>= fun om ↦
  En.spEndG h (layEnd midItems q2) cl gate >>= fun en ↦
  pure ⟨hd.r, hd.v, om.1, om.2, en.2.1, en.2.2⟩

/-- **CB-2: the sponge caller gadget re-executes `spCaller6 h`.** -/
theorem spHar : SpHarStmt spG6 := by
  refine fun h hh a gate ↦ (har_iff _ _ _ _ _).2 fun c M hg ↦ ?_
  rw [spItems_split h, layItems_append, layItems_append, layItems_append, spCaller6_head]
  unfold spG6
  refine hsA_bind (hsA_of_hs (spHead_runs (c := c) (M := M) h a)) fun hd hhd ↦ ?_
  refine hsA_mono (hsA_forall (R := fun x ↦ SpHeadRep M hd x ∧ x = spHeadVals M h a) fun x hx ↦ ?_)
    fun o hp ↦ runs_bind (runs_and hhd (runs_spHead M h a)) hp
  obtain ⟨⟨hr, hv, hsl, hcst, hlan, hmu, hval⟩, hxx⟩ := hx
  have hsl6 : x.2.2.1.length = 6 := by rw [hxx]; simp [spHeadVals, draws]
  have hrl : x.1.length = h := by rw [hxx]; simp [spHeadVals, gdraws]
  have hrep0 := claim0_rep (M := M) hd.value hd.mu hd.r hd.sl x.2.2.2 x.2.1
    (by rw [hmu, hr, hsl]) (by rw [hval, hr, hsl])
  rw [hr, hsl] at hrep0
  have hpt0 : (claim0 hd.value hd.mu hd.r hd.sl).point.length = h - 3 := by
    have h1 := congrArg List.length hr
    have h2 := congrArg List.length hsl
    simp only [List.length_map] at h1 h2
    simp only [claim0, List.length_append, List.length_drop, List.length_take]
    omega
  rw [spRest_eq h hh]
  refine hsA_bind (layers6G_runs h hh _ _ gate hg hpt0 _ hrep0) fun cl hcl ↦ ?_
  have hmid := treeMid_har (c := c) (M := M) 25 (layEnd (rep 12 (P18.layer h)) (layEnd (spHeadItems h) a))
    (by norm_num) hd.cst (hd.sl.headD default) hd.lanes (x.2.2.1.drop 1) (by simp [hsl6]) hlan gate hg
  rw [hcst, ev2_headD_of hsl (by omega)] at hmid
  refine hsA_bind hmid fun om hom ↦ ?_
  refine hsA_bind (hsA_forall (R := fun cl' ↦ ClaimRep M cl cl' ∧ cl.point.length = h - 3 ∧ LtS cl.w)
    fun cl' hc ↦ En.spEnd_har h hh _ cl gate c M hg hc.2.1 hc.2.2 cl' hc.1) fun en hen ↦ hsA_pure ?_
  refine runs_bind hcl fun cl' hcl' ↦ runs_bind hom fun r hr' ↦
    runs_bind' (List.append_nil _).symm (hen cl' hcl') fun e he ↦ runs_pure ?_
  exact ⟨hr, hv, hr'.1.symm, hr'.2.symm, he.2.1, he.2.2⟩

end Lvm6.QK
