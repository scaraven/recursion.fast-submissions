-- New for lvm6 (WP CB). CB-2's front: the sponge caller's reads before the layers (§T caller,
-- §6.3 rows 6–7) and leanVM's first claim at the sponge's instance point, with the HAR.
import Lvm6QKLink

/-!
# The sponge caller's head (generator and HAR)

* **`spHeadProg h`**: `spCaller6 h`'s reads up to the layers: `r` (`h` ground draws `G(1)`), the
  25 output scalars `v`, `r_seg :: r_lane` (`G(3) D(5)`), `c_st`; `spCaller6_head`: `spCaller6 h`
  is `spHeadProg h` followed by `spRest h`.
* **`spHeadG h a`**: the gadget (lanes from `a`): the `eq` table of `r_lane` (62 products), the first
  claim's value `c_st + r_seg·Σ_{ℓ<25} eq(r_lane, ℓ)·v_ℓ` (26) and `μ = eq(r₀ … r₃, ·)` (30).
* **`spHead_runs`**: the cells represent the reads and `firstClaimSF Shape.v1 r [r_seg] r_lane v c_st`.
-/

set_option autoImplicit false

namespace Lvm6.QK

open LeanVM.Parameters LeanVM.Protocol.Compile LeanVM.Protocol.Verifier
open LeanVM.Protocol.KeccakGkr (Shape)
open Lvm Lvm.Loop Lvm.Loop.Build Lvm.Q2 Lvm.Har Lvm.E2V Lvm6.K Lvm6.KPack
open Lvm6 (Item rep rnd)

variable {c : Ctx} {M : Mem}

/-- The sponge head's raw values: `r`, `v`, `r_seg :: r_lane`, `c_st`. -/
abbrev SpHeadV : Type := List E2 × List E2 × List E2 × E2

/-- **`spCaller6`'s reads up to the layers.** -/
def spHeadProg (h : ℕ) : VerifierProgram SpHeadV :=
  e2Samples gC1 h >>= fun r ↦ e2Reads 25 >>= fun v ↦ gPoint gSeg 5 >>= fun sl ↦ e2Read >>= fun cst ↦
  pure (r, v, sl, cst)

/-- The rest of `spCaller6` after its head. -/
def spRest (h : ℕ) (x : SpHeadV) : VerifierProgram SpOut :=
  layers6 (h - 4 + 4) (List.range 12)
    (firstClaimSF Shape.v1 x.1 (x.2.2.1.take 1) (x.2.2.1.drop 1) x.2.1 x.2.2.2) >>= fun claim ↦
  sumcheckE2 gC2 x.2.2.2 3 (List.replicate 6 none) >>= fun om ↦
  e2Read >>= fun cout ↦
  VerifierProgram.require (midWt 25 (x.2.2.1.headD 0) (x.2.2.1.drop 1) om.1 * cout = om.2) >>= fun _ ↦
  spongeEnd6 (h - 4) claim >>= fun en ↦
  pure (x.1, x.2.1, (⟨x.2.2.1, x.2.2.2, claim, om.1, cout⟩, en))

/-- **`spCaller6 h` is its head followed by the rest.** -/
theorem spCaller6_head (h : ℕ) : spCaller6 h = spHeadProg h >>= spRest h := by
  simp only [spCaller6, spongeCore6, spHeadProg, spRest, kHead6, bind_assoc, pure_bind]

/-- The items of the sponge head. -/
def spHeadItems (h : ℕ) : List Item := rep h [.G 1] ++ ([.E 25] ++ ([.G 3, .D 5] ++ [.E 1]))

/-- The lane after `r`. -/
def sA1 (h a : ℕ) : ℕ := a + 10 * h
/-- The lane after `v`. -/
def sA2 (h a : ℕ) : ℕ := sA1 h a + 50
/-- The lane of `c_st`. -/
def sA3 (h a : ℕ) : ℕ := sA2 h a + 55

/-- The values the sponge head reads, from the stream. -/
def spHeadVals (M : Mem) (h a : ℕ) : SpHeadV :=
  (gdraws M a h, scal M (sA1 h a) 25, ev2 M (ld2 (sA2 h a + 1)) :: draws M (sA2 h a + 10) 5,
    ev2 M (ld2 (sA3 h a)))

theorem runs_spHead (M : Mem) (h a : ℕ) :
    Runs M (layItems (spHeadItems h) a) (spHeadProg h) (· = spHeadVals M h a) := by
  unfold spHeadItems spHeadProg
  simp only [layItems_append, layEnd_repG]
  refine runs_bind (runs_e2Samples M (by norm_num) h a) fun r hr ↦ runs_bind (runs_e2Reads' M 25 _)
    fun v hv ↦ runs_bind (runs_gPoint M (by norm_num) _ _) fun sl hsl ↦ ?_
  rw [show ∀ x, layItems [V.Item.E 1] x = layItems [V.Item.E 1] x ++ [] from fun _ ↦ (List.append_nil _).symm]
  refine runs_bind (runs_e2Read' M _) fun cst hcst ↦ runs_pure ?_
  rw [hr, hv, hsl, hcst]
  rfl

/-- **What the sponge head gadget hands on.** -/
structure SpHeadC where
  r : List C2
  v : List C2
  sl : List C2
  cst : C2
  lanes : List C2
  mu : List C2
  value : C2

/-- **The sponge head gadget** for `2^h` rows, lanes from `a`. -/
def spHeadG (h a : ℕ) : BM SpHeadC :=
  let r := (List.range h).map fun i ↦ ld2 (a + 1 + 10 * i)
  let v := (List.range 25).map fun i ↦ ld2 (sA1 h a + 2 * i)
  let sl := ld2 (sA2 h a + 1) :: (List.range 5).map fun i ↦ ld2 (sA2 h a + 10 + 9 * i)
  let cst := ld2 (sA3 h a)
  g2Zero cst >>= fun z ↦ g2One z >>= fun one ↦
  g2EqTab z [one] (sl.drop 1) >>= fun lanes ↦
  g2Dot z ((lanes.take 25).zip v) >>= fun dot ↦
  g2Mul (sl.headD default) dot cst >>= fun value ↦
  g2EqTab z [one] (r.take 4) >>= fun mu ↦
  pure ⟨r, v, sl, cst, lanes, mu, value⟩

/-- **The sponge head gadget's cells represent the head's values and the first claim.** -/
def SpHeadRep (M : Mem) (o : SpHeadC) (x : SpHeadV) : Prop :=
  o.r.map (ev2 M) = x.1 ∧ o.v.map (ev2 M) = x.2.1 ∧ o.sl.map (ev2 M) = x.2.2.1 ∧ ev2 M o.cst = x.2.2.2 ∧
    o.lanes.map (ev2 M) = eqKernelF (x.2.2.1.drop 1) ∧
    o.mu.map (ev2 M) = (firstClaimSF Shape.v1 x.1 (x.2.2.1.take 1) (x.2.2.1.drop 1) x.2.1 x.2.2.2).mu ∧
    ev2 M o.value = (firstClaimSF Shape.v1 x.1 (x.2.2.1.take 1) (x.2.2.1.drop 1) x.2.1 x.2.2.2).value

/-- **The sponge head gadget re-executes the head of `spCaller6`.** -/
theorem spHead_runs (h a : ℕ) :
    Hs c M (spHeadG h a) fun o ↦ Runs M (layItems (spHeadItems h) a) (spHeadProg h) (SpHeadRep M o) := by
  unfold spHeadG
  refine hs_bind (hs_g2Zero _) fun z hz ↦ hs_bind (hs_g2One z) fun one hone ↦ ?_
  rw [hz, add_zero] at hone
  refine hs_bind (hs_g2EqTab hz [one] _) fun lanes hlanes ↦ hs_bind (hs_g2Dot _ _) fun dot hdot ↦
    hs_bind (hs_g2Mul _ _ _) fun value hvalue ↦ hs_bind (hs_g2EqTab hz [one] _) fun mu hmu ↦
      hs_pure (runs_mono (runs_spHead M h a) fun x hx ↦ ?_)
  subst hx
  have hlan := eqTab_ev2 hone _ hlanes
  have hd : (List.drop 1 (ld2 (sA2 h a + 1) :: List.map (fun i ↦ ld2 (sA2 h a + 10 + 9 * i))
      (List.range 5))).map (ev2 M) = draws M (sA2 h a + 10) 5 := by
    simp [draws, List.map_map]
  have hv : (List.map (fun i ↦ ld2 (sA1 h a + 2 * i)) (List.range 25)).map (ev2 M) =
      scal M (sA1 h a) 25 := by simp [scal, List.map_map]
  have hr : (List.map (fun i ↦ ld2 (a + 1 + 10 * i)) (List.range h)).map (ev2 M) = gdraws M a h := by
    simp [gdraws, List.map_map]
  refine ⟨hr, hv, ?_, rfl, ?_, ?_, ?_⟩
  · simp [spHeadVals, draws, List.map_map]
  · rw [hlan, hd]
    simp [spHeadVals]
  · rw [eqTab_ev2 hone _ hmu, List.map_take, hr]
    simp [firstClaimSF, spHeadVals]
  · rw [ev2, hvalue, FE2.toE2_add, FE2.fe2_mul_eq, hdot, hz, zero_add, ev2_sum, List.map_map]
    simp only [firstClaimSF, dotF]
    rw [foldl_add_eq_sum, zero_add]
    have hseg : Shape.v1.segments - 1 = 1 := by decide
    have hm : (FE2.toE2 ∘ fun e : C2 × C2 ↦ C2.val M e.1 * C2.val M e.2) =
        fun e ↦ ev2 M e.1 * ev2 M e.2 := by
      funext e; simp [ev2, FE2.fe2_mul_eq]
    rw [hm, zip_map_mul, List.map_take, hlan, hd, hv, hseg]
    simp only [spHeadVals, List.take_succ_cons, List.take_zero, List.drop_succ_cons, List.drop_zero,
      eqKernelF, List.foldl_cons, List.foldl_nil, List.map_cons, List.map_nil, List.cons_append,
      List.nil_append, List.getD_cons_succ, List.getD_cons_zero, one_mul, List.headD_cons]
    rw [add_comm]
    rfl

end Lvm6.QK
