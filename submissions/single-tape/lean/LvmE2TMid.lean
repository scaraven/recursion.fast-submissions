-- New for lvm2 E2-FT (stage S2GT, E2F-T; helper T-H2): S2GT's middle phases in the pinned pair form, the port of
-- E2F-V's `midSpecP_F₂_core` (`LvmE2VMidSpecF`) to the typed phases at `E2` (`typedProgT`, E2F-T's `typedSpecGT`)
-- and any continuation rows (`kgProgFR`). Lemmas only: `LvmE2TSpec` closes `midSpecP_GT` with `midSpecP_GT_of`.
import LvmE2TSpecP
import LvmE2TRet
import LvmE2VMidSpecF
import LvmE2FCert

/-!
# S2GT's middle phases: the pinned pair form

* `rowsOfB_struct`: S2GT's continuation rows (`contRowsT`'s form, any block count `B ≤ ksSplit P20 + 400`) are distinct and
  inside `[1, 2^13)`;
* **`specBusGT`** (`specBusTF`'s twin): the typed phases at `E2` on the viewed pinned pairs, from `typedSpecGT` at
  `L₀ = 1`, follower `0`; lead `0 ≤ leadF₂`;
* **`kgSpecFRT`** (`kgSpecF` on any continuation rows): the `E2` front;
* **`midSpecP_GT_of`**: `midSpecOfRelG` with V's `linkF`, `sideF`, `retOK_kgProgFR`, `noCG_kgFrontT` and the typed
  return facts `retOK_typedProgT_of`; the statement of `midSpecP_GT` with `THypT`'s fields spelled out.
-/

set_option autoImplicit false

namespace Lvm.E2T

open Lvm.Loop Lvm.Typed Lvm.E2V LeanVM.Parameters LeanVM.Protocol LeanVM.Protocol.Compile
open LeanVM.Protocol.Verifier LeanVM.Protocol.EndToEnd LeanVM.Protocol.EndToEnd.Front
open Lvm.M3 (NoCG AllSc LayOk KeysOk FixOk inst lay26)
open Lvm.ASM (Pair LkSJ εS MidSpecP midSpecOfRelG BndS OpenClaims)
open Lvm.VEq (hdX pubX pubXT)
open Lvm.E2F (candRelZ)
open Lvm.NS (colM ksCol ksY2 msgM msgX)
open Lvm.Shape (vp)
open LeanVM.Protocol.EndToEnd.Sound (RetOK)
open scoped ENNReal

/-! ## The continuation rows -/

/-- `contRowsT`'s form with `B` sponge blocks: rows `1 … B − 1` and rows 1–31 of the WOTS leaf. -/
def rowsOfB (B : ℕ) : List ℕ :=
  (List.range (B - 1)).map (· + 1) ++ (List.range 31).map (ksSplit P20 + 399 + 1 + ·)

/-- **The rows' structure** (`contRowsF_struct`'s): distinct, inside `[1, 2^13)`. -/
theorem rowsOfB_struct (B : ℕ) (hB : B ≤ ksSplit P20 + 400) :
    (rowsOfB B).Nodup ∧ ∀ i ∈ rowsOfB B, 1 ≤ i ∧ i < 2 ^ (9 + 4) := by
  have hs : B - 1 < ksSplit P20 + 400 ∧ ksSplit P20 + 400 + 31 ≤ 2 ^ (9 + 4) := by
    rw [Lvm.ksSplit_P20] at hB ⊢
    omega
  refine ⟨?_, ?_⟩
  · unfold rowsOfB
    rw [List.nodup_append]
    refine ⟨(List.nodup_range).map fun a b h ↦ by omega, (List.nodup_range).map fun a b h ↦ by omega,
      fun a ha b hb hab ↦ ?_⟩
    simp only [List.mem_map, List.mem_range] at ha hb
    obtain ⟨a', ha', rfl⟩ := ha
    obtain ⟨b', hb', rfl⟩ := hb
    omega
  · intro i hi
    unfold rowsOfB at hi
    simp only [List.mem_append, List.mem_map, List.mem_range] at hi
    rcases hi with ⟨a, ha, rfl⟩ | ⟨b, hb, rfl⟩ <;> omega

/-! ## The typed phases on the viewed pinned pairs -/

section Typed

variable {Ti : TInst}

theorem imgCZ_ncard_le_one (recOf : List UInt8 → Column CMain.nu20 → Column 19) (za : List E × E)
    (x : List UInt8) (h : List Ev) : (imgCZ recOf za x h).ncard ≤ 1 :=
  (Set.ncard_image_le (Set.toFinite _)).trans (candRelZ_ncard_le recOf za x h)

/-- The typed half of S2GT's good pair (`GbTT`'s body). -/
def GbTB (Ti : TInst) (hτ : ∀ t ∈ Ti.mbT, t.τ ≤ lay26.μ) (x : List UInt8) (p : Pair) : Prop :=
  (TGoodT Ti lay26 hτ (pubXT x) p ∧ BndS x p.1) ∧ AccOkTT Ti (pubXT x)

/-- **The typed phases at `E2` on the viewed pinned pairs** (`specBusTF`'s twin), the `KS` half `Gk` a parameter;
`typedSpecGT` at `L₀ = 1` (`candRelZ` has at most one pair), follower `0`; lead `leadF₂`. -/
noncomputable def specBusGT (hτ : ∀ t ∈ Ti.mbT, t.τ ≤ lay26.μ) (hok : Ti.Ok) (hmaps : Ti.MapsFit lay26)
    (hacc : ∀ x, (pubXT x).accIn.pt.length = phiVarsT) (hsc : AllSc Ti.mbT) (hlay : LayOk lay26 Ti.mbT)
    (hkey : KeysOk Ti.mbT) (hw : ∀ t ∈ Ti.mbT, 0 < t.w) (hfix : FixOk Ti.mbT)
    (hμ : (inst lay26 Ti.mbT hτ).μBus = miniDepth) (herr : TErrsT 1 (inst lay26 Ti.mbT hτ) εS 0)
    (recOf : List UInt8 → Column CMain.nu20 → Column 19) (za : List E × E) (x : List UInt8)
    (Gk N : Pair → Prop) :
    Spec (typedProgT Ti (pubXT x))
      (fun h ↦ Lvm.E2F.PinPost za h ∧
        Doomed (candRelZ recOf za x) (fun p ↦ GbTB Ti hτ x (vp x p) ∧ (Gk (vp x p) ∧ N (vp x p))) h)
      (fun a h ↦ Doomed (candRelZ recOf za x)
        (fun p ↦ (BT x a (vp x p) ∧ N (vp x p)) ∧ (Gk (vp x p) ∧ N (vp x p))) h ∧ Lvm.E2F.PinPost za h)
      εS leadF₂ 0 :=
  have S0 := typedSpecGT Ti lay26 (pubXT x) hτ hok hmaps rfl (hacc x) hsc hlay hkey hw hfix hμ
    (imgCZ recOf za x) (fun p ↦ BndS x p.1 ∧ Gk p ∧ N p) (L₀ := 1) (εmax := εS) (T := 0)
    (fun h ↦ 1 ≤ (commits h).length) (imgCZ_append recOf za x) (fun _ ↦ Set.toFinite _)
    (imgCZ_ncard_le_one recOf za x) herr
  (S0.frame (Lvm.E2F.PinPost za) (fun _ _ hl hr ↦ pinPost_append za
      ((noCG_typedProgT Ti (pubXT x)).1.reach_commits hl) hr)).mono
    (fun _ ⟨hr, hDm⟩ ↦ ⟨⟨Lvm.Typed.rootShapeM_one hr.1, Lvm.Typed.rootShapeM_firstWord hr.1,
      doomed_imgCZ.mpr (Doomed.mono hDm fun _ hq ↦ ⟨⟨⟨hq.1, hq.2.1.1⟩, hq.2.2⟩, hq.2.1.2⟩)⟩, hr⟩)
    (fun _ _ hp ↦ ⟨Doomed.mono (doomed_imgCZ.mp hp.1) fun _ hq ↦ ⟨hq.1.1.1, hq.1.1.2, hq.2.1, hq.1.2⟩,
      hp.2⟩)
    le_rfl zero_le le_rfl

end Typed

/-! ## The `E2` front on any continuation rows -/

section Front

open LeanVM.Protocol.KeccakGkr (errE RegionValid)
open Lvm.KG (TapeOut dOf KSRel SpongeLink ksMsg ksSplitN ksY ksYRow)

variable {β : Type} {C : List Ev → Set β} [Finite β]

open Classical in
/-- **The `E2` front on the continuation rows `rows`** (`kgSpecF` with `rows` a parameter, distinct and inside
`[1, 2^13)`). Lead `0`; every group `≤ εS`. -/
noncomputable def kgSpecFRT (rows : List ℕ) (hrows : rows.Nodup ∧ ∀ i ∈ rows, 1 ≤ i ∧ i < 2 ^ (9 + 4))
    (hst : Stable C) (hcard : ∀ h, (C h).ncard ≤ 1) (s : RecursionFast.Digest)
    (n y2 : ℕ) (col main ks : β → ℕ → K) (M X : β → ℕ → ℕ → K) (R : β → Prop) {T : ℝ≥0∞}
    (hT : T ≤ εS) :
    Spec (kgProgFR rows s n)
      (Doomed C (fun q ↦ TapeOut 20 s n (dOf 20 0 (col q)) ∧
        KSRel 13 9 y2 rows (main q) (ks q) (M q) (X q) ∧ R q))
      (fun out hist ↦ (out.1.1.length = 20 ∧ out.1.2.1.length = 25 ∧
          out.1.2.2.2.sc.1.length = 20 ∧ out.1.2.2.2.d.sl.1.length = 2) ∧
        (out.2.1.1.length = 13 ∧ out.2.1.2.1.length = 25 ∧ out.2.2.2.1.1.length = 13) ∧
        Doomed C (fun q ↦ KcFr y2 (col q) (main q) (ks q) (M q) (X q) out ∧ R q) hist)
      εS 0 T :=
  ((tapeSpecE2 (P := 15) (sb := 1) (dsel := 0) (h := 17) (T := 0) hst hcard (by norm_num)
      (by norm_num) s col (fun q ↦ KSRel 13 9 y2 rows (main q) (ks q) (M q) (X q) ∧ R q)
      sum7_le_εS).some).bind' fun tp ↦
  if htp : tp.1.length = 20 ∧ tp.2.1.length = 25 ∧ tp.2.2.2.sc.1.length = 20 ∧
      tp.2.2.2.d.sl.1.length = 2 then
    (((ksSpecE2 (T := 0) hst hcard 9 25 le_rfl ks (fun q ↦ ksY 13 y2 (main q) (ks q))
        (fun q ↦ (RowColTrue (17 + 6) (col q) tp.2.2.2.d.row ∧ TiedDF 20 (dOf 20 0 (col q)) tp.1 tp.2.1) ∧
          SpongeLink 13 rows (ks q) (ksYRow 13 y2 (main q) (ks q))
            (ksMsg (ksSplitN 13 9) (M q) (X q)) ∧ R q) sum7_le_εS).some).mono
      (fun _ hd ↦ Doomed.mono hd.2.2.2.2 fun _ ⟨hv, ho, ⟨hrow, htied⟩, hl, hR⟩ ↦
        ⟨hrow, htied, ⟨hv, ho, hl⟩, hR⟩)
      (fun _ _ h ↦ h) le_rfl le_rfl le_rfl).bind' fun co ↦
    if hco : co.1.length = 13 ∧ co.2.1.length = 25 then
      (((ksLinkSpecE2 (T := T) hst hcard (9 + 4) 9 (by norm_num) rows hrows.1
          hrows.2 ks (fun q ↦ ksYRow 13 y2 (main q) (ks q)) M X
          (fun q ↦ (RowColTrue (17 + 6) (col q) tp.2.2.2.d.row ∧ TiedDF 20 (dOf 20 0 (col q)) tp.1 tp.2.1) ∧
            CallerClaimsE2 13 25 (ks q) (ksY 13 y2 (main q) (ks q)) co ∧ R q) hT).some).mono
        (fun _ hd ↦ Doomed.mono hd.2.2 fun _ ⟨hl, ⟨hrow, htied⟩, hcc, hR⟩ ↦ ⟨hcc, ⟨hrow, htied⟩, hl, hR⟩)
        (fun _ _ h ↦ h) le_rfl le_rfl le_rfl).bind' fun lo ↦
      (Spec.ret (tp, (co, lo))).mono
        (fun _ hd ↦ ⟨htp, ⟨hco.1, hco.2, hd.1⟩, Doomed.mono hd.2 fun _ ⟨⟨⟨hrow, htied⟩, hcc, hk⟩, hR⟩ ↦
          ⟨hk, ⟨hrow, htied⟩, hcc, hR⟩⟩)
        (fun _ _ h ↦ h) le_rfl le_rfl le_rfl
    else Spec.dead.mono (fun _ hd ↦ hco ⟨hd.1, hd.2.1⟩) (fun _ _ h ↦ h) le_rfl le_rfl le_rfl
  else Spec.dead.mono (fun _ hd ↦ htp ⟨hd.1, hd.2.1, hd.2.2.1, hd.2.2.2.1⟩) (fun _ _ h ↦ h) le_rfl le_rfl
    le_rfl

end Front

/-! ## The pinned pair form -/

/-- `TRetT`'s body gives roll 11's `TRet` (the counts split). -/
theorem tRet_of {a : OpenClaims}
    (ha : (∀ c ∈ a.1, LeanVM.Protocol.Whir.Sound.IsMultiaffine 19 c.1) ∧
      (∀ c ∈ a.2, LeanVM.Protocol.Whir.Sound.IsMultiaffine CMain.nu20 c.1) ∧ a.1.length + a.2.length ≤ 2 ^ 39) :
    TRet a :=
  ⟨ha.1, ha.2.1, by have := ha.2.2; omega, by have := ha.2.2; omega⟩

/-- **The pinned pair form of S2GT's middle phases** (`midSpecP_F₂_core`'s twin), `THypT`'s fields spelled out and
the continuation rows `rows` a parameter (distinct, inside `[1, 2^13)`). -/
theorem midSpecP_GT_of (Ti : TInst) (hτ : ∀ t ∈ Ti.mbT, t.τ ≤ lay26.μ) (hok : Ti.Ok) (hmaps : Ti.MapsFit lay26)
    (hacc : ∀ x, (pubXT x).accIn.pt.length = phiVarsT) (hsc : AllSc Ti.mbT) (hlay : LayOk lay26 Ti.mbT)
    (hkey : KeysOk Ti.mbT) (hw : ∀ t ∈ Ti.mbT, 0 < t.w) (hfix : FixOk Ti.mbT)
    (hwid : (Ti.mbT.map (·.w)).sum ≤ 2 ^ 38) (hμ : (inst lay26 Ti.mbT hτ).μBus = miniDepth)
    (herr : TErrsT 1 (inst lay26 Ti.mbT hτ) εS 0) (rows : List ℕ)
    (hrows : rows.Nodup ∧ ∀ i ∈ rows, 1 ≤ i ∧ i < 2 ^ (9 + 4))
    (recOf : List UInt8 → Column CMain.nu20 → Column 19) (za : List E × E) :
    MidSpecP (midFWithR (fun x ↦ typedProgT Ti (pubXT x)) rows) (Lvm.E2F.candRelZ recOf za) (Lvm.E2F.PinPost za)
      (Lvm.Shape.Good₂ fun x qm qr ↦ GbTB Ti hτ x (qm, qr) ∧ GkFR rows x (qm, qr)) εS leadF₂ :=
  have hS : SplitSound := fun nu c hc q h ↦ splitE2_sound nu c hc q h
  have hA : SplitAffine := fun nu c hc ↦ isMultiaffine_splitE2 nu c hc
  midSpecOfRelG (busP := fun x ↦ typedProgT Ti (pubXT x)) (kgP := fun x ↦ kgProgFR rows (hdX x).s (pubX x).n)
    (asm := fun x a k ↦ assembleF₂ x a k) (Lb := leadF₂) (Lk := 0)
    (Gb := fun x p ↦ GbTB Ti hτ x (vp x p)) (Gk := fun x p ↦ GkFR rows x (vp x p))
    (B := fun x a p ↦ BT x a (vp x p))
    (Kc := fun x k p ↦ KcFr ksY2 (colM (vp x p).1) (colM (vp x p).1) (ksCol (vp x p).1) (msgM (vp x p).2)
      (msgX (vp x p).1) k)
    (Qa := fun _ a ↦ (∀ c ∈ a.1, LeanVM.Protocol.Whir.Sound.IsMultiaffine 19 c.1) ∧
      (∀ c ∈ a.2, LeanVM.Protocol.Whir.Sound.IsMultiaffine CMain.nu20 c.1) ∧ a.1.length + a.2.length ≤ 2 ^ 39)
    (Qk := fun _ ↦ KgRetF) (C := candRelZ recOf za) (Sh := Lvm.E2F.PinPost za)
    (fun _ _ hl hr ↦ pinPost_append za hl hr)
    (fun x ↦ specBusGT hτ hok hmaps hacc hsc hlay hkey hw hfix hμ herr recOf za x (GkFR rows x)
      fun p ↦ ¬ (GbTB Ti hτ x p ∧ GkFR rows x p))
    (fun x ↦ retOK_typedProgT_of Ti hlay hwid (pubXT x))
    (fun x a T hT ↦ (kgSpecFRT rows hrows (candRelZ_stable recOf za x) (candRelZ_ncard_le recOf za x)
        (hdX x).s (pubX x).n ksY2 (fun p ↦ colM (vp x p).1) (fun p ↦ colM (vp x p).1) (fun p ↦ ksCol (vp x p).1)
        (fun p ↦ msgM (vp x p).2) (fun p ↦ msgX (vp x p).1)
        (fun p ↦ BT x a (vp x p) ∧ ¬ (GbTB Ti hτ x (vp x p) ∧ GkFR rows x (vp x p))) hT).mono
      (fun _ hd ↦ Doomed.mono hd fun p ⟨ht, hks, hb, hn⟩ ↦
        ⟨⟨⟨by rw [Lvm.ASM.pubX_n x] at ht; exact ht, hks⟩, hn⟩, hb, hn⟩)
      (fun _ _ hp ↦ hp.2.2) le_rfl le_rfl le_rfl)
    (fun _ ↦ retOK_kgProgFR _ _ _) (fun _ ↦ noCG_kgFrontT _ _ _)
    (fun x a k p _ hk h1 h2 ↦ linkF hS x a k p hk h1 h2)
    (fun x a k ha hk ↦ sideF hA x a k (tRet_of ha) hk)

end Lvm.E2T
