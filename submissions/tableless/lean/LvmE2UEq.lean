-- New for lvm2 U-TAPE (UT-V, UTAPE-STMT 22's front): V_S's S2GU front on the reader `DM` refines the statement's
-- programs (`tapeProgU`, `wireProgU`) on the width-aware stream, values through `FE2.toE2`; the closure-level twins
-- `wireUD`, `tapeUD` (the statement's programs read for read at `FE2`) and the transport of the S2GU algebra.
import LvmE2VEqTape
import LvmS2GUFront
import LvmE2UDec
import LvmS2GUSched
import LvmS2GUMid
import LvmE2VDecClaims

/-!
# The S2GU front at `E2`, refined

* transport along a ring homomorphism: `map_eTailF`, `map_kksF`, `map_ikEvalP`, `map_t1ValsF`; `ikEvalP_eq`
  (`eqEvalF` as the sum `ikEvalF` states);
* **`wireUD`**, **`tapeUD`**: `wireProgU`, `tapeProgU` on `DM` at `FE2` (the slot reductions `slotD`, the GKR
  `tapeGkrD`, `ikEvalP` for `Ĩ_ks`);
* widths `wWireU`, `wTapeU`; **`refW_wireUD`**, **`refW_tapeUD`**.
-/

set_option autoImplicit false

namespace Lvm.E2U

open LeanVM.Parameters Finset

section Map

variable {F G : Type} [Field F] [Field G] (f : F →+* G)

theorem map_eTailF (hs w : ℕ) (r : List F) : f (eTailF hs w r) = eTailF hs w (r.map f) := by
  unfold eTailF
  rw [E2V.map_prodF]
  congr 1
  simp only [List.map_map, ← List.map_drop, ← List.map_take]
  exact List.map_congr_left fun c _ ↦ by simp

theorem map_kksF (iv : List (ℕ × ℕ)) (ρ μ σ' : List F) (base : ℕ) :
    f (kksF iv ρ μ σ' base) = kksF iv (ρ.map f) (μ.map f) (σ'.map f) base := by
  simp only [kksF, E2V.map_sumF, List.map_map]
  congr 1
  exact List.map_congr_left fun ab _ ↦ by simp [map_sub, E2V.map_msEvalF]

theorem map_ikEvalP (ρ μ σ : List F) (base : ℕ) :
    f (E2V.ikEvalP ρ μ σ base) = E2V.ikEvalP (ρ.map f) (μ.map f) (σ.map f) base := by
  simp only [E2V.ikEvalP, map_mul, E2V.map_sumF, List.map_map, E2V.map_eqEvalF, E2V.map_eqAtF, List.map_take,
    List.map_drop, List.length_map]
  congr 3
  exact List.map_congr_left fun d _ ↦ by
    simp only [Function.comp_apply, map_mul, E2V.map_eqAtF, E2V.map_getD, List.map_take]

theorem map_t1ValsF [Algebra K F] [Algebra K G] (hf : ∀ a : K, f (algebraMap K F a) = algebraMap K G a)
    (w hs : ℕ) (r ab : List F) : (t1ValsF w hs r ab).map f = t1ValsF w hs (r.map f) (ab.map f) := by
  simp only [t1ValsF, List.map_map]
  exact List.map_congr_left fun l _ ↦ by
    simp only [Function.comp_apply, map_add, map_mul, map_sub, map_one, E2V.map_getD, map_eTailF, E2V.kF, hf]

theorem map_yWG (ω : List F) (o z : ℕ) : f (E2V.yWG ω o z) = E2V.yWG (ω.map f) o z := by
  unfold E2V.yWG; split_ifs
  · exact E2V.map_getD f _ _
  · exact map_zero f

theorem map_mWG (ω : List F) (o z : ℕ) : f (E2V.mWG ω o z) = E2V.mWG (ω.map f) o z := by
  unfold E2V.mWG; split_ifs
  · exact E2V.map_getD f _ _
  · exact map_zero f

end Map

/-- **`ikEvalP` is the statement's `ikEvalF`** (`eqEvalF` of the pack bits as the sum over the cube). -/
theorem ikEvalP_eq {F : Type} [Field F] [CharP F 2] (ρ μ σ : List F) (base : ℕ) (hσ : 4 ≤ σ.length)
    (hρ : σ.length - 4 ≤ ρ.length) : E2V.ikEvalP ρ μ σ base = ikEvalF ρ μ σ base := by
  have hl : (ρ.take (σ.length - 4)).length = (σ.drop 4).length := by simp; omega
  rw [E2V.ikEvalP, ikEvalF, ← E2V.sum_eqAtF_mul_eqAtF _ _ hl,
    show (ρ.take (σ.length - 4)).length = σ.length - 4 by simp; omega]

end Lvm.E2U

/-! ## The closure-level twins of the statement's programs -/

namespace Lvm

open DM Lvm.E2V Lvm.E2U

/-- **`wireProgU` on `DM` at `FE2`** (the statement's wire, read for read; `Ĩ_ks` by `ikEvalP`). -/
def wireUD (s : List FK) (n : Nat) (claim : E2V.KClaim FE2) :
    DM ((List FE2 × FE2) × List FE2 × SlotU ((FE × (List FE → FE)) × List FE) ×
      SlotU ((FE × (List FE → FE)) × List FE) × SlotU ((FE × (List FE → FE)) × List FE)) := do
  let sc ← sumcheckD gC2 (wireTargetD (sBitsD s) n claim) 3 (List.replicate 20 none)
  let g ← readE2s 3
  require (sc.2 == E2V.msEvalF claim.point claim.mu sc.1 0 (n - 1) * g.getD 0 0 +
    eTailF 13 20 sc.1 * (kksF contIvU claim.point claim.mu (sc.1.take 13) (2 ^ 20) * g.getD 1 0 +
      E2V.ikEvalP claim.point claim.mu (sc.1.take 13) (2 ^ 20) * g.getD 2 0))
  let d ← slotD 2 1 0 (E2V.dWF claim.weights) sc.1 (g.getD 0 0)
  let y ← slotD 5 5 22 (E2V.yWG claim.weights) (sc.1.take 13) (g.getD 1 0)
  let m ← slotD 5 4 10 (E2V.mWG claim.weights) (sc.1.take 13 ++ [0]) (g.getD 2 0)
  pure (sc, g, d, y, m)

/-- **`tapeProgU` on `DM` at `FE2`** (`r_{<20}` and `r_20` returned apart). -/
def tapeUD (s : List FK) (n : Nat) :
    DM (List FE2 × List FE2 × List FE2 × E2V.KClaim FE2 × ((List FE2 × FE2) × List FE2 ×
      SlotU ((FE × (List FE → FE)) × List FE) × SlotU ((FE × (List FE → FE)) × List FE) ×
      SlotU ((FE × (List FE → FE)) × List FE))) := do
  sepE2
  let r ← samplesG gC1 20
  let ab ← readE2s 50
  let r20 ← samplesG gC1 1
  let claim ← tapeGkrD 21 (r ++ r20) (t1ValsF 20 13 (r ++ r20) ab)
  require (decide (1 ≤ n ∧ n ≤ 2 ^ 20))
  let wo ← wireUD s n claim
  pure (r, r20, ab, claim, wo)

end Lvm

namespace Lvm.VEq

open Lvm DM LeanVM.Parameters LeanVM.Protocol.Compile Finset
open Lvm.FE2 (toE2)
open Lvm.E2U

theorem toE2_eTailF (hs w : ℕ) (r : List FE2) : toE2 (eTailF hs w r) = eTailF hs w (r.map toE2) :=
  map_eTailF E2V.toE2Hom hs w r

theorem toE2_kksF (iv : List (ℕ × ℕ)) (ρ μ σ' : List FE2) (base : ℕ) :
    toE2 (kksF iv ρ μ σ' base) = kksF iv (ρ.map toE2) (μ.map toE2) (σ'.map toE2) base :=
  map_kksF E2V.toE2Hom iv ρ μ σ' base

theorem toE2_ikEvalP (ρ μ σ : List FE2) (base : ℕ) :
    toE2 (E2V.ikEvalP ρ μ σ base) = E2V.ikEvalP (ρ.map toE2) (μ.map toE2) (σ.map toE2) base :=
  map_ikEvalP E2V.toE2Hom ρ μ σ base

theorem map_toE2_t1ValsF (w hs : ℕ) (r ab : List FE2) :
    (t1ValsF w hs r ab).map toE2 = t1ValsF w hs (r.map toE2) (ab.map toE2) :=
  map_t1ValsF E2V.toE2Hom E2V.toE2_algebraMap w hs r ab

theorem monoD_wireUD (s : List FK) (n : ℕ) (claim : E2V.KClaim FE2) : MonoD (wireUD s n claim) :=
  (monoD_sumcheckD _ _ _ _).bind fun _ ↦ (monoD_readE2s _).bind fun _ ↦ (MonoD.require _).bind fun _ ↦
    (monoD_slotD _ _ _ _ _ _).bind fun _ ↦ (monoD_slotD _ _ _ _ _ _).bind fun _ ↦
      (monoD_slotD _ _ _ _ _ _).bind fun _ ↦ MonoD.pure _

/-- The widths of the S2GU wire. -/
def wWireU : List ℕ := wSc 3 20 ++ wReads 3 ++ wSlot 2 ++ wSlot 5 ++ wSlot 5

/-- What the S2GU wire's two sides relate. -/
def WireURelW (x : (List FE2 × FE2) × List FE2 × SlotU ((FE × (List FE → FE)) × List FE) ×
      SlotU ((FE × (List FE → FE)) × List FE) × SlotU ((FE × (List FE → FE)) × List FE))
    (o : WireOutU) : Prop :=
  o.sc.1 = x.1.1.map toE2 ∧ o.sc.2 = toE2 x.1.2 ∧ o.g = x.2.1.map toE2 ∧ SlotRelW x.2.2.1 o.d ∧
    SlotRelW x.2.2.2.1 o.y ∧ SlotRelW x.2.2.2.2 o.m

section Ref

variable {cap : ℕ → ℕ → ℕ} {occ : ℕ → ℕ → ℕ} {shp : ℕ → ℕ × ℕ} {rw : ℕ → ℕ} {sig : ByteArray}

/-- **The S2GU wire** (V_S's statement words `s` with the digest's bits; the claim's point long enough for
`Ĩ_ks`). -/
theorem refW_wireUD (s : List FK) (d : RecursionFast.Digest) (hs : sBitsD s = Lvm.KG.digestBits d) (n : ℕ)
    (claim : E2V.KClaim FE2) (hρ : 9 ≤ claim.point.length) {i : ℕ} (hw : WAt rw i wWireU) :
    RefAtW cap occ shp rw sig i (wireUD s n claim) (wireProgU d n (cE2 claim)) WireURelW
      (i + wWireU.length) := by
  rw [wWireU, WAt.append, WAt.append, WAt.append, WAt.append] at hw
  obtain ⟨⟨⟨⟨hw1, hw2⟩, hw3⟩, hw4⟩, hw5⟩ := hw
  unfold wireUD wireProgU wireProgB
  rw [hs]
  refine RefAtW.bind (fun _ ↦ (monoD_readE2s _).bind fun _ ↦ (MonoD.require _).bind fun _ ↦
    (monoD_slotD _ _ _ _ _ _).bind fun _ ↦ (monoD_slotD _ _ _ _ _ _).bind fun _ ↦
      (monoD_slotD _ _ _ _ _ _).bind fun _ ↦ MonoD.pure _)
    ((refW_sumcheckD E2V.gC2 3 (by norm_num) (List.replicate 20 none)
      (wireTargetD (Lvm.KG.digestBits d) n claim) ?_).congr_prog ?_) ?_
  · simpa using hw1
  · rw [map_replicate_noneE2, E2V.toE2_wireTargetD]
  rintro sc sc' ⟨h1, h2, hl⟩
  have hl' : sc.1.length = 20 := by simpa using hl
  refine RefAtW.bind (fun _ ↦ (MonoD.require _).bind fun _ ↦ (monoD_slotD _ _ _ _ _ _).bind fun _ ↦
    (monoD_slotD _ _ _ _ _ _).bind fun _ ↦ (monoD_slotD _ _ _ _ _ _).bind fun _ ↦ MonoD.pure _)
    (refW_readE2s 3 (WAt.idx_eq hw2 (by simp))) ?_
  intro g g' hg
  subst hg
  refine RefAtW.bind (fun _ ↦ (monoD_slotD _ _ _ _ _ _).bind fun _ ↦ (monoD_slotD _ _ _ _ _ _).bind fun _ ↦
    (monoD_slotD _ _ _ _ _ _).bind fun _ ↦ MonoD.pure _) (RefAtW.require fun h ↦ ?_) fun _ _ _ ↦ ?_
  · have h' := congrArg toE2 (beq_iff_eq.1 h)
    have h13 : 4 ≤ (sc.1.take 13).length := by simp [hl']
    rw [h2, h', Lvm.FE2.toE2_add, Lvm.FE2.fe2_mul_eq, Lvm.FE2.fe2_mul_eq, Lvm.FE2.toE2_add, Lvm.FE2.fe2_mul_eq,
      Lvm.FE2.fe2_mul_eq, E2V.toE2_msEvalF, toE2_getD, toE2_getD, toE2_getD, toE2_eTailF, toE2_kksF, toE2_ikEvalP,
      ikEvalP_eq _ _ _ _ (by simpa using h13) (by simp [hl']; omega), List.map_take, ← h1]
    rfl
  · have hD : (fun o z ↦ toE2 (E2V.dWF claim.weights o z)) = E2V.dWF (claim.weights.map toE2) :=
      funext fun o ↦ funext fun z ↦ E2V.toE2_dWF _ _ _
    have hY : (fun o z ↦ toE2 (E2V.yWG claim.weights o z)) = yWF (claim.weights.map toE2) :=
      funext fun o ↦ funext fun z ↦ (map_yWG E2V.toE2Hom _ _ _).trans rfl
    have hM : (fun o z ↦ toE2 (E2V.mWG claim.weights o z)) = mWF (claim.weights.map toE2) :=
      funext fun o ↦ funext fun z ↦ (map_mWG E2V.toE2Hom _ _ _).trans rfl
    refine RefAtW.bind (fun _ ↦ (monoD_slotD _ _ _ _ _ _).bind fun _ ↦ (monoD_slotD _ _ _ _ _ _).bind fun _ ↦
      MonoD.pure _)
      ((refW_slotD 2 1 0 (E2V.dWF claim.weights) sc.1 (g.getD 0 0)
        (WAt.idx_eq hw3 (by simp [length_wReads]; omega))).congr_prog ?_) fun dd dd' hd ↦ ?_
    · rw [hD, toE2_getD, ← h1]
      rfl
    refine RefAtW.bind (fun _ ↦ (monoD_slotD _ _ _ _ _ _).bind fun _ ↦ MonoD.pure _)
      ((refW_slotD 5 5 22 (E2V.yWG claim.weights) (sc.1.take 13) (g.getD 1 0)
        (WAt.idx_eq hw4 (by simp [wSlot, length_wReads]; omega))).congr_prog ?_) fun yy yy' hy ↦ ?_
    · rw [hY, toE2_getD, List.map_take, ← h1]
      rfl
    refine RefAtW.bind (fun _ ↦ MonoD.pure _)
      ((refW_slotD 5 4 10 (E2V.mWG claim.weights) (sc.1.take 13 ++ [0]) (g.getD 2 0)
        (WAt.idx_eq hw5 (by simp [wSlot, length_wReads]; omega))).congr_prog ?_) fun mm mm' hm ↦ ?_
    · rw [hM, toE2_getD, List.map_append, List.map_take, ← h1, List.map_singleton, Lvm.FE2.toE2_zero]
      rfl
    exact (RefAtW.pure ⟨h1, h2, rfl, hd, hy, hm⟩).idx (by simp [wSlot, wWireU, length_wReads]; omega)

/-- The widths of the S2GU tape. -/
def wTapeU : List ℕ := List.replicate 20 8 ++ wReads 50 ++ List.replicate 1 8 ++ wTapeGkr 21 ++ wWireU

/-- What the S2GU tape's two sides relate. -/
def TapeURelW (x : List FE2 × List FE2 × List FE2 × E2V.KClaim FE2 × ((List FE2 × FE2) × List FE2 ×
      SlotU ((FE × (List FE → FE)) × List FE) × SlotU ((FE × (List FE → FE)) × List FE) ×
      SlotU ((FE × (List FE → FE)) × List FE)))
    (o : TapeOutU) : Prop :=
  o.1 = (x.1 ++ x.2.1).map toE2 ∧ x.1.length = 20 ∧ x.2.1.length = 1 ∧ o.2.1 = x.2.2.1.map toE2 ∧
    o.2.2.1 = cE2 x.2.2.2.1 ∧ WireURelW x.2.2.2.2 o.2.2.2

/-- **The S2GU tape** (V_S's statement words `s` with the digest's bits). -/
theorem refW_tapeUD (s : List FK) (d : RecursionFast.Digest) (hs : sBitsD s = Lvm.KG.digestBits d) (n : ℕ)
    {i : ℕ} (hw : WAt rw i wTapeU) :
    RefAtW cap occ shp rw sig i (tapeUD s n) (tapeProgU d n) TapeURelW (i + wTapeU.length) := by
  rw [wTapeU, WAt.append, WAt.append, WAt.append, WAt.append] at hw
  obtain ⟨⟨⟨⟨hw1, hw2⟩, hw3⟩, hw4⟩, hw5⟩ := hw
  unfold tapeUD tapeProgU tapeProgB
  refine RefAtW.bind (fun _ ↦ (monoD_samplesG _ _).bind fun _ ↦ (monoD_readE2s _).bind fun _ ↦
    (monoD_samplesG _ _).bind fun _ ↦ (monoD_tapeGkrD _ _ _).bind fun _ ↦ (MonoD.require _).bind fun _ ↦
      (monoD_wireUD _ _ _).bind fun _ ↦ MonoD.pure _) refW_sepE2 fun _ _ _ ↦ ?_
  refine RefAtW.bind (fun _ ↦ (monoD_readE2s _).bind fun _ ↦ (monoD_samplesG _ _).bind fun _ ↦
    (monoD_tapeGkrD _ _ _).bind fun _ ↦ (MonoD.require _).bind fun _ ↦ (monoD_wireUD _ _ _).bind
      fun _ ↦ MonoD.pure _) (refW_samplesGL E2V.gC1 20 hw1) ?_
  rintro r r' ⟨hr, hrl⟩
  subst hr
  refine RefAtW.bind (fun _ ↦ (monoD_samplesG _ _).bind fun _ ↦ (monoD_tapeGkrD _ _ _).bind fun _ ↦
    (MonoD.require _).bind fun _ ↦ (monoD_wireUD _ _ _).bind fun _ ↦ MonoD.pure _)
    (refW_readE2s 50 (WAt.idx_eq hw2 (by simp only [List.length_replicate]))) ?_
  intro ab ab' hab
  subst hab
  refine RefAtW.bind (fun _ ↦ (monoD_tapeGkrD _ _ _).bind fun _ ↦ (MonoD.require _).bind fun _ ↦
    (monoD_wireUD _ _ _).bind fun _ ↦ MonoD.pure _)
    (refW_samplesGL E2V.gC1 1
      (WAt.idx_eq hw3 (by simp only [List.length_append, List.length_replicate, length_wReads]))) ?_
  rintro r20 r20' ⟨h20, h20l⟩
  subst h20
  refine RefAtW.bind (fun _ ↦ (MonoD.require _).bind fun _ ↦ (monoD_wireUD _ _ _).bind fun _ ↦ MonoD.pure _)
    ((refW_tapeGkrD 21 (r ++ r20) (t1ValsF 20 13 (r ++ r20) ab) (by simp [hrl, h20l])
      (WAt.idx_eq hw4 (by simp only [List.length_append, List.length_replicate, length_wReads]))).congr_prog ?_) ?_
  · rw [List.map_append, map_toE2_t1ValsF, List.map_append]
  rintro c c' ⟨hc, hcl⟩
  subst hc
  refine RefAtW.bind (fun _ ↦ (monoD_wireUD _ _ _).bind fun _ ↦ MonoD.pure _)
    (RefAtW.require fun h ↦ of_decide_eq_true h) fun _ _ _ ↦ ?_
  refine RefAtW.bind (fun _ ↦ MonoD.pure _)
    (refW_wireUD s d hs n c (by omega)
      (WAt.idx_eq hw5 (by simp only [List.length_append, List.length_replicate, length_wReads]; omega))) ?_
  intro wo wo' hwo
  exact (RefAtW.pure ⟨by rw [List.map_append], hrl, h20l, rfl, rfl, hwo⟩).idx
    (by simp only [wTapeU, List.length_append, List.length_replicate, length_wReads]; omega)

end Ref

end Lvm.VEq

/-! ## V_S's front is the closure twin (`tapeUDG` at `P20U` → `tapeUD`; items → claims) -/

namespace Lvm.E2U

open Lvm DM E2V

/-- A slot reduction's output in the closures' form. -/
abbrev SlotC : Type := SlotU ((FE × (List FE → FE)) × List FE)

/-- `tapeUD`'s output type. -/
abbrev TapeVU : Type := List FE2 × List FE2 × List FE2 × E2V.KClaim FE2 × ((List FE2 × FE2) × List FE2 × SlotC × SlotC ×
  SlotC)

/-- A slot's row-switch data in the closures' form. -/
def mapSl (t : SlotU RowZ) : SlotC := (t.1, t.2.1, t.2.2.1.out)

/-- V_S's tape output in the closures' form. -/
def mapTU (t : TapeU RowZ) : TapeVU :=
  (t.r, [t.rw], t.ab, t.claim, (t.wo.sc, t.wo.g, mapSl t.wo.d, mapSl t.wo.y, mapSl t.wo.m))

theorem slotDFG_R (b sb blk : ℕ) (W : ℕ → ℕ → FE2) (pt : List FE2) (v : FE2) :
    mapSl <$> slotDFG rowSwitchDR b sb blk W pt v = slotD b sb blk W pt v := by
  rw [← slotDF_eq, slotDF, rowSwitchDF_R, slotDFG_map]
  rfl

theorem samplesG_one (g : ℕ) : samplesG g 1 = (fun x ↦ [x]) <$> sampleG g := by
  simp only [samplesG, map_bind, bind_pure_comp]
  rfl

theorem dSelBits_P20U : dSelBits P20U = 1 := rfl
theorem dSel_P20U : dSel P20U = 0 := by unfold dSel; rw [layout0_P20U]; rfl

/-- **V_S's merged tape at `P20U` is `tapeUD`** (the row switches' data mapped to their closures). -/
theorem tapeUDG_R (s : List FK) (n : ℕ) : mapTU <$> tapeUDG rowSwitchDR P20U s n = tapeUD s n := by
  have hy : (layout0 P20U).ks / 2 ^ (13 + 5) = 22 := by rw [layout0_P20U]; rfl
  have hm : (layout0 P20U).s / 2 ^ 19 = 10 := by rw [layout0_P20U]; rfl
  unfold tapeUDG wireUDG tapeUD wireUD
  simp only [slotDFW_yWG, slotDFW_mWG, dSelBits_P20U, dSel_P20U, ← slotDFG_R, ← tapeGkrDF_eq,
    ← wireTargetDF_eq, ← dWA_eq, samplesG_one, map_bind, bind_map_left, map_pure, bind_assoc, pure_bind,
    show P20U.logN = 20 from rfl, show P20U.ksLog = 13 from rfl, show P20U.nuMain = 23 from rfl,
    show P20U.nuRec = 19 from rfl, show (2 : ℕ) * 25 = 50 from rfl, slotBitsU, hy, hm,
    show (23 : ℕ) - (13 + 5) = 5 from rfl, show (23 : ℕ) - 19 = 4 from rfl, show (20 : ℕ) + 1 = 21 from rfl]
  rfl

/-- **The front's claims at `P20U` as V_S forms them** (`frontItemsU`'s flattening, closures). -/
def frontClaimsUD (p : Params) (pub : Pub) (tp : TapeVU) : List (Com × BlockClaim × FE) :=
  let L := layout0 p
  let blkD := dBlock p
  let r := tp.1
  let ab := tp.2.2.1
  let wo := tp.2.2.2.2
  let rowPt := wo.1.1 ++ wo.2.2.1.1.1 ++ selPtF (dSel p) (dSelBits p)
  ((List.range dLanes).flatMap fun l =>
    ((splitD p.nuMain [(1, blkD, r ++ selPtF l 2)] (ab.getD l 0)).zip (tailDE2 r l)).map fun e =>
      (Com.main, e.1, e.2)) ++
  ((List.range 25).flatMap fun l =>
    splitZ p.nuMain [(1, ⟨p.ksLog, L.ks + l * 2 ^ p.ksLog⟩, r.take p.ksLog)] (ab.getD (25 + l) 0)) ++
  [(Com.main, ⟨⟨p.nuMain, 0⟩, wo.2.2.1.2.2.1.2, wo.2.2.1.2.2.1.1⟩, rowTailE2 wo.2.2.1.2.2.2 rowPt),
   (Com.main, ⟨⟨p.nuMain, 0⟩, wo.2.2.2.1.2.2.1.2, wo.2.2.2.1.2.2.1.1⟩, (0 : FE)),
   (Com.main, ⟨⟨p.nuMain, 0⟩, wo.2.2.2.2.2.2.1.2, wo.2.2.2.2.2.2.1.1⟩, (0 : FE))] ++
  (pub.h.zipIdx.map fun (w, l) =>
    (Com.main, BlockClaim.point blkD (selectorPoint (pub.n - 1) p.logN ++ selectorPoint l 2) (FE.ofK w), (0 : FE)))

end Lvm.E2U

/-! ## The front's claims against the statement's (`front_rel` at S2GU) -/

namespace Lvm.VEq

open Lvm DM LeanVM.Parameters LeanVM.Protocol.Compile Finset
open Lvm.FE2 (toE2)
open Lvm.E2U

/-- **The shape of `tapeUD`'s value**: the lengths of `r`, the wire point and the slot points, and the three row
switches' weights. -/
def TapeShapeU (tp : TapeVU) : Prop :=
  tp.1.length = 20 ∧ tp.2.2.2.2.1.1.length = 20 ∧
    tp.2.2.2.2.2.2.1.1.1.length = 2 ∧
    tp.2.2.2.2.2.2.1.2.2.1.2 = rowWD (tp.2.2.2.2.1.1 ++ tp.2.2.2.2.2.2.1.1.1 ++ E2V.selPtF 0 1)
      tp.2.2.2.2.2.2.1.2.2.2 ∧
    tp.2.2.2.2.2.2.2.1.1.1.length = 5 ∧
    tp.2.2.2.2.2.2.2.1.2.2.1.2 = rowWD (tp.2.2.2.2.1.1.take 13 ++ tp.2.2.2.2.2.2.2.1.1.1 ++ E2V.selPtF 22 5)
      tp.2.2.2.2.2.2.2.1.2.2.2 ∧
    tp.2.2.2.2.2.2.2.2.1.1.length = 5 ∧
    tp.2.2.2.2.2.2.2.2.2.2.1.2 = rowWD (tp.2.2.2.2.1.1.take 13 ++ [0] ++ tp.2.2.2.2.2.2.2.2.1.1 ++ E2V.selPtF 10 4)
      tp.2.2.2.2.2.2.2.2.2.2.2

theorem retD_wireUD (s : List FK) (n : ℕ) (claim : E2V.KClaim FE2) :
    RetD (fun wo : (List FE2 × FE2) × List FE2 × SlotC × SlotC × SlotC ↦
      wo.1.1.length = 20 ∧ wo.2.2.1.1.1.length = 2 ∧
        wo.2.2.1.2.2.1.2 = rowWD (wo.1.1 ++ wo.2.2.1.1.1 ++ E2V.selPtF 0 1) wo.2.2.1.2.2.2 ∧
        wo.2.2.2.1.1.1.length = 5 ∧
        wo.2.2.2.1.2.2.1.2 = rowWD (wo.1.1.take 13 ++ wo.2.2.2.1.1.1 ++ E2V.selPtF 22 5) wo.2.2.2.1.2.2.2 ∧
        wo.2.2.2.2.1.1.length = 5 ∧
        wo.2.2.2.2.2.2.1.2 = rowWD (wo.1.1.take 13 ++ [0] ++ wo.2.2.2.2.1.1 ++ E2V.selPtF 10 4) wo.2.2.2.2.2.2.2)
      (wireUD s n claim) :=
  (retD_sumcheckD _ _ _ _).bind fun _ hsc ↦ RetD.bind_true fun _ ↦ RetD.bind_true fun _ ↦
    (retD_slotD _ _ _ _ _ _).bind fun _ hd ↦ (retD_slotD _ _ _ _ _ _).bind fun _ hy ↦
      (retD_slotD _ _ _ _ _ _).bind fun _ hm ↦
        RetD.pure ⟨by simpa using hsc, hd.1, hd.2, hy.1, hy.2, hm.1, hm.2⟩

theorem retD_tapeUD (s : List FK) (n : ℕ) : RetD TapeShapeU (tapeUD s n) :=
  RetD.bind_true fun _ ↦ (retD_samplesG _ _).bind fun _ hr ↦ RetD.bind_true fun _ ↦ RetD.bind_true fun _ ↦
    RetD.bind_true fun _ ↦ RetD.bind_true fun _ ↦ (retD_wireUD _ _ _).bind fun _ hwo ↦
      RetD.pure ⟨hr, hwo⟩

/-- **A row claim whose point selects a block above `D`** has the tail `0` (`D`'s tail slices vanish: the block
bit is `1`). -/
theorem rowTailE2_zero (z : List FE2) (hz : z.length = 23) (h22 : z.getD 22 0 = 1) (eqR : List FE) :
    rowTailE2 eqR z = 0 := by
  have h22' : 22 < z.length := by omega
  have hd : z.drop 22 = [1] := by
    rw [List.drop_eq_getElem_cons h22', List.drop_eq_nil_of_le (by omega), ← h22,
      List.getD_eq_getElem _ _ h22']
  have hblk : E2V.eqEvalF (z.drop 22) (E2V.selPtF 0 (CMain.nu20 - 22)) = 0 := by rw [hd]; rfl
  have hs : ∀ i, (tailSlicesE2 z).getD i 0 = 0 := by
    intro i
    unfold tailSlicesE2
    simp only [hblk, mul_zero, zero_mul, List.getD_eq_getElem?_getD, List.getElem?_map]
    cases (List.range 64)[i]? <;> rfl
  have hw : ∀ j, rowWordD (tailSlicesE2 z) j = 0 := by
    intro j
    have hb0 : bitFE2 0 j = false := by
      unfold bitFE2
      split
      · exact Nat.zero_testBit j
      · exact Nat.zero_testBit _
    unfold rowWordD
    have hf : ∀ (l : List ℕ) (acc : ℕ), l.foldl (fun acc i ↦
        if bitFE2 ((tailSlicesE2 z).getD i 0) j then acc + 2 ^ i else acc) acc = acc := by
      intro l
      induction l with
      | nil => intro acc; rfl
      | cons a l ih =>
        intro acc
        rw [List.foldl_cons, hs a, hb0]
        simp only [Bool.false_eq_true, if_false]
        exact ih acc
    rw [hf]
    rfl
  unfold rowTailE2
  simp only [hw]
  rw [show FE.ofK (0 : FK) = 0 from rfl]
  simp only [mul_zero]
  unfold sumE
  generalize (List.range 128) = l
  induction l with
  | nil => rfl
  | cons a l ih => simpa using ih

theorem offOK_yU (l : ℕ) (hl : l < 25) : Shape.OffOK ⟨13, CMain.yOffU20 + l * 2 ^ 13⟩ := by
  have : ∀ l < 25, Shape.OffOK ⟨13, CMain.yOffU20 + l * 2 ^ 13⟩ := by decide +kernel
  exact this l hl

theorem dBlock_P20U : dBlock P20U = ⟨22, 0⟩ := by unfold dBlock; rw [layout0_P20U]; rfl

theorem ks_P20U : (layout0 P20U).ks = CMain.yOffU20 := by rw [layout0_P20U]

/-- **The front's claims at S2GU** (`frontClaimsUD`, with their tails) against the statement's (`tapeClaimsU`). -/
theorem front_relU {s : Bool} (x : List UInt8) (tp : TapeVU) (k : TapeOutU) (hk : TapeURelW tp k)
    (hsh : TapeShapeU tp) (hn : s = true → (pubX x).n ≤ 2 ^ 18) (hh : (pubX x).h.length ≤ 4) :
    List.Forall₂ (VRel s) (frontClaimsUD P20U (pubXT x) tp) ((tapeClaimsU k (pubX x)).map BClaim.onStack) := by
  obtain ⟨hk1, hrl, -, hk2, -, hsc1, -, -, hD, hY, hM⟩ := hk
  obtain ⟨-, hlsc, hτD, hwD, hτY, hwY, hτM, hwM⟩ := hsh
  have ht20 : k.1.take 20 = tp.1.map toE2 := by
    rw [hk1, List.map_append, List.take_append_of_le_length (by simp [hrl]),
      List.take_of_length_le (by simp [hrl])]
  have ht13 : k.1.take 13 = (tp.1.take 13).map toE2 := by
    rw [List.map_take, ← ht20, List.take_take]
    rfl
  unfold frontClaimsUD tapeClaimsU
  dsimp only
  simp only [List.map_append]
  refine Lk.forall₂_append (Lk.forall₂_append (Lk.forall₂_append ?_ ?_) ?_) ?_
  · -- `D`'s split word claims
    rw [List.map_flatMap, show dLanes = 4 from rfl]
    refine forall₂_flatMap_same _ fun l hl ↦ ?_
    rw [show P20U.nuMain = 23 from rfl, dBlock_P20U, nuMainE_eq]
    refine vrel_splitD _ _ _ rfl (fun _ ↦ tails_D tp.1 hrl l (mem_range.1 hl) _) _ ?_
    rw [ht20, hk2, dBlkE_eq, toE2_getD]
    simp only [E2V.pointE2, List.map_cons, List.map_nil, E2V.partE, Lvm.FE2.toE2_one, List.map_append,
      E2V.map_toE2_selPtF]
    rfl
  · -- the `Y` block's split word claims
    rw [List.map_flatMap]
    refine forall₂_flatMap_same _ fun l hl ↦ ?_
    rw [show P20U.nuMain = 23 from rfl, nuMainE_eq, show P20U.ksLog = 13 from rfl, ks_P20U]
    refine vrel_splitZ _ (by simpa using offOK_yU l (mem_range.1 hl)) _ _ ?_
    rw [ht13, hk2, toE2_getD]
    simp only [E2V.pointE2, List.map_cons, List.map_nil, E2V.partE, Lvm.FE2.toE2_one]
    rfl
  · -- the three row claims
    have hzD : (tp.2.2.2.2.1.1 ++ tp.2.2.2.2.2.2.1.1.1 ++ E2V.selPtF 0 1 : List FE2).length = 23 := by
      simp [hlsc, hτD, E2V.selPtF]
    have hzY : (tp.2.2.2.2.1.1.take 13 ++ tp.2.2.2.2.2.2.2.1.1.1 ++ E2V.selPtF 22 5 : List FE2).length = 23 := by
      simp [hlsc, hτY, E2V.selPtF]
    have hzM : (tp.2.2.2.2.1.1.take 13 ++ [0] ++ tp.2.2.2.2.2.2.2.2.1.1 ++ E2V.selPtF 10 4 : List FE2).length =
        23 := by simp [hlsc, hτM, E2V.selPtF]
    have h22Y : (tp.2.2.2.2.1.1.take 13 ++ tp.2.2.2.2.2.2.2.1.1.1 ++ E2V.selPtF 22 5 : List FE2).getD 22 0 = 1 := by
      rw [List.getD_append_right _ _ _ _ (by simp [hlsc, hτY]), List.length_append, List.length_take, hlsc, hτY]
      rfl
    have h22M : (tp.2.2.2.2.1.1.take 13 ++ [0] ++ tp.2.2.2.2.2.2.2.2.1.1 ++ E2V.selPtF 10 4 : List FE2).getD 22 0 =
        1 := by
      rw [List.getD_append_right _ _ _ _ (by simp [hlsc, hτM]), List.length_append, List.length_append,
        List.length_take, hlsc, hτM]
      rfl
    refine .cons (vrel_of (onStack_rel ⟨rfl, hD.2.2.2.1, hD.2.2.2.2⟩) fun _ ↦ ⟨inStack_full, ?_⟩)
      (.cons (vrel_of (onStack_rel ⟨rfl, hY.2.2.2.1, hY.2.2.2.2⟩) fun _ ↦ ⟨inStack_full, ?_⟩)
        (.cons (vrel_of (onStack_rel ⟨rfl, hM.2.2.2.1, hM.2.2.2.2⟩) fun _ ↦ ⟨inStack_full, ?_⟩) .nil))
    · rw [hwD, dSel_P20U, dSelBits_P20U, show P20U.nuMain = 23 from rfl]
      dsimp only
      exact tail_row _ hzD _ _
    · rw [hwY, show P20U.nuMain = 23 from rfl, ← tail_row _ hzY, rowTailE2_zero _ hzY h22Y]
    · rw [hwM, show P20U.nuMain = 23 from rfl, ← tail_row _ hzM, rowTailE2_zero _ hzM h22M]
  · -- the boundary claims
    rw [List.map_map]
    refine Lk.forall₂_map_map _ fun wl hwl ↦ ?_
    obtain ⟨w, l⟩ := wl
    have hh' : (pubXT x).h.length ≤ 4 := hh
    have hl : l < 4 := lt_of_lt_of_le (List.mem_zipIdx hwl).2.1 (by simpa using hh')
    refine vrel_of (onStack_rel (Lk.point_rel _ _ _ ?_ ?_ ?_)) fun hs ↦ ⟨?_, ?_⟩
    · rw [dBlock_P20U]; rfl
    · rw [List.map_append, map_selectorPoint, map_selectorPoint]; rfl
    · exact (M3.tE_ofK w).symm
    · rw [dBlock_P20U]; exact (by decide : Shape.InStack ⟨22, 0⟩)
    · exact (Shape.tailValueF_bnd ((pubX x).n - 1) (by have := hn hs; omega) l hl (FE.ofK w)).symm

end Lvm.VEq
