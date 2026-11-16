-- New for lvm2 S1 (E2-F, E2F-V): the helpers of `midSpecP_F₂` (`LvmE2VMidSpec`): the `E2` front commits and
-- grinds nothing (`cg_kgProgF`), its returns' facts (`retOK_kgProgF`), its specification (`kgSpecF`, the tape
-- caller, `KS`, the `KS` link), the facts of `contRowsF`.
import LvmE2VKS
import LvmE2VMid
import LvmMPMidT
import LvmE2FCert
import LvmCertTInst
import LvmE2QTypedSpec
import LvmTypedSpecX

-- (GOLF2: 1 declarations that `certified` does not use moved verbatim to `LvmE2VMidSpecFOff`, outside its import closure.)

/-!
# The `E2` front in the middle phases

* `cg_kgProgF`: `kgProgF` commits nothing and asks no proof of work of the language (its grinding is the
  ground challenges' `require (powOK …)`);
* `contRowsF_struct`: the continuation rows are distinct and inside `[1, 2^13)`.
-/

set_option autoImplicit false

namespace Lvm.E2V

open LeanVM.Parameters LeanVM.Protocol LeanVM.Protocol.Compile LeanVM.Protocol.Verifier
open Lvm.M3 (NoCG cg_ret cg_sample cg_readScalar cg_require cg_sampleChallenges)

/-! ## No commitment, no grinding -/

theorem cg_iteE2 {α : Type} {c : Prop} [Decidable c] {a b : VerifierProgram α} (ha : NoCG a)
    (hb : NoCG b) : NoCG (if c then a else b) := by
  split
  · exact ha
  · exact hb

theorem cg_e2Read : NoCG e2Read := NoCG.bind cg_readScalar fun _ ↦ cg_ret _

theorem cg_e2Reads : ∀ n, NoCG (e2Reads n)
  | 0 => cg_ret _
  | n + 1 => NoCG.bind cg_e2Read fun _ ↦ NoCG.bind (cg_e2Reads n) fun _ ↦ cg_ret _

theorem cg_e2Sample (g : ℕ) : NoCG (e2Sample g) :=
  NoCG.bind cg_readScalar fun _ ↦ NoCG.bind cg_sample fun _ ↦ NoCG.bind (cg_require _) fun _ ↦
    cg_ret _

theorem cg_e2Samples (g : ℕ) : ∀ n, NoCG (e2Samples g n)
  | 0 => cg_ret _
  | n + 1 => NoCG.bind (cg_e2Sample g) fun _ ↦ NoCG.bind (cg_e2Samples g n) fun _ ↦ cg_ret _

theorem cg_e2Sep : NoCG e2Sep := NoCG.bind cg_sample fun _ ↦ cg_ret _

theorem cg_roundPolyE2 (count : ℕ) (claim : E2) : ∀ mode, NoCG (roundPolyE2 count claim mode)
  | none => NoCG.bind cg_e2Read fun _ ↦ NoCG.bind (cg_e2Reads _) fun _ ↦ cg_ret _
  | some _ => NoCG.bind (cg_e2Reads _) fun _ ↦ cg_ret _

theorem cg_sumcheckE2 (g count : ℕ) : ∀ (modes : List (Option E2)) (claim : E2),
    NoCG (sumcheckE2 g claim count modes)
  | [], _ => cg_ret _
  | mode :: modes, claim =>
    NoCG.bind (cg_roundPolyE2 count claim mode) fun _ ↦ NoCG.bind (cg_e2Sample g) fun _ ↦
      NoCG.bind (cg_sumcheckE2 g count modes _) fun _ ↦ cg_ret _

theorem cg_packRoundsE2 (g : ℕ) : ∀ (rs : List E2) (value scale : E2),
    NoCG (packRoundsE2 g rs value scale)
  | [], _, _ => cg_ret _
  | _ :: rs, _, _ =>
    NoCG.bind (cg_roundPolyE2 _ _ _) fun _ ↦ NoCG.bind (cg_e2Sample g) fun _ ↦
      NoCG.bind (cg_packRoundsE2 g rs _ _) fun _ ↦ cg_ret _

theorem cg_verifyKeccakLayerE2 (sh : LeanVM.Protocol.KeccakGkr.Shape) (logSteps step : ℕ)
    (claim : KClaim E2) : NoCG (verifyKeccakLayerE2 sh logSteps step claim) :=
  NoCG.bind (cg_e2Reads _) fun _ ↦ NoCG.bind (cg_require _) fun _ ↦ NoCG.bind cg_e2Sep fun _ ↦
    NoCG.bind (cg_e2Sample _) fun _ ↦ NoCG.bind (cg_packRoundsE2 _ _ _ _) fun _ ↦
      NoCG.bind (cg_sumcheckE2 _ _ _ _) fun _ ↦ NoCG.bind (cg_e2Reads _) fun _ ↦
        NoCG.bind (cg_require _) fun _ ↦ NoCG.bind (cg_e2Sample _) fun _ ↦ cg_ret _

theorem cg_keccakLayersE2 (sh : LeanVM.Protocol.KeccakGkr.Shape) (logSteps : ℕ) :
    ∀ (steps : List ℕ) (claim : KClaim E2), NoCG (keccakLayersE2 sh logSteps steps claim)
  | [], _ => cg_ret _
  | _ :: steps, _ =>
    NoCG.bind (cg_verifyKeccakLayerE2 _ _ _ _) fun _ ↦ cg_keccakLayersE2 sh logSteps steps _

theorem cg_keccakOpenE2 (logSteps : ℕ) (claim : KClaim E2) (first count : ℕ) (value : E2) :
    NoCG (keccakOpenE2 logSteps claim first count value) :=
  NoCG.bind (cg_sumcheckE2 _ _ _ _) fun _ ↦ cg_ret _

theorem cg_verifyKeccakE2 (logSteps : ℕ) (inst output : List E2) :
    NoCG (verifyKeccakE2 logSteps inst output) :=
  NoCG.bind (cg_e2Samples _ _) fun _ ↦ NoCG.bind (cg_e2Samples _ _) fun _ ↦
    NoCG.bind (cg_iteE2 cg_e2Read (cg_ret _)) fun _ ↦ NoCG.bind (cg_keccakLayersE2 _ _ _ _) fun _ ↦
      NoCG.bind (cg_iteE2 (NoCG.bind (cg_keccakOpenE2 _ _ _ _ _) fun _ ↦ NoCG.bind cg_e2Read fun _ ↦
          NoCG.bind (cg_require _) fun _ ↦ cg_ret _) (cg_ret _)) fun _ ↦
        NoCG.bind (cg_sumcheckE2 _ _ _ _) fun _ ↦ NoCG.bind (cg_keccakOpenE2 _ _ _ _ _) fun _ ↦
          NoCG.bind (cg_e2Reads _) fun _ ↦ NoCG.bind (cg_require _) fun _ ↦ cg_ret _

theorem cg_rowSwitch (z sv : List E2) : NoCG (rowSwitch z sv) :=
  NoCG.bind (cg_sampleChallenges _) fun _ ↦ cg_ret _

theorem cg_callerProgE2 (h : ℕ) : NoCG (callerProgE2 h) :=
  NoCG.bind (cg_e2Samples _ _) fun _ ↦ NoCG.bind (cg_e2Reads _) fun _ ↦
    NoCG.bind (cg_verifyKeccakE2 _ _ _) fun _ ↦ NoCG.bind (cg_rowSwitch _ _) fun _ ↦ cg_ret _

theorem cg_ksLinkProgE2 (hk xl : ℕ) (rows : List ℕ) : NoCG (ksLinkProgE2 hk xl rows) :=
  NoCG.bind (cg_e2Samples _ _) fun _ ↦ NoCG.bind (cg_sumcheckE2 _ _ _ _) fun _ ↦
    NoCG.bind (cg_e2Reads _) fun _ ↦ NoCG.bind (cg_require _) fun _ ↦ cg_ret _

theorem cg_tapeGkrE2 (h : ℕ) (inst output : List E2) : NoCG (tapeGkrE2 h inst output) :=
  NoCG.bind (cg_e2Samples _ _) fun _ ↦ cg_keccakLayersE2 _ _ _ _

theorem cg_slotProgE2 (b sb blk : ℕ) (W : ℕ → ℕ → E2) (pt : List E2) (v : E2) :
    NoCG (slotProgE2 b sb blk W pt v) :=
  NoCG.bind (cg_sumcheckE2 _ _ _ _) fun _ ↦ NoCG.bind (cg_e2Reads _) fun _ ↦
    NoCG.bind (cg_require _) fun _ ↦ NoCG.bind (cg_rowSwitch _ _) fun _ ↦ cg_ret _

theorem cg_wireChProgE2 (w sb dsel : ℕ) (s : RecursionFast.Digest) (n : ℕ) (claim : KClaim E2) :
    NoCG (wireChProgE2 w sb dsel s n claim) :=
  NoCG.bind (cg_sumcheckE2 _ _ _ _) fun _ ↦ NoCG.bind (cg_e2Reads _) fun _ ↦
    NoCG.bind (cg_require _) fun _ ↦ NoCG.bind (cg_slotProgE2 _ _ _ _ _ _) fun _ ↦ cg_ret _

theorem cg_tapeProgE2 (w sb dsel : ℕ) (s : RecursionFast.Digest) (n : ℕ) :
    NoCG (tapeProgE2 w sb dsel s n) :=
  NoCG.bind cg_e2Sep fun _ ↦ NoCG.bind (cg_e2Samples _ _) fun _ ↦ NoCG.bind (cg_e2Reads _) fun _ ↦
    NoCG.bind (cg_tapeGkrE2 _ _ _) fun _ ↦ NoCG.bind (cg_require _) fun _ ↦
      NoCG.bind (cg_wireChProgE2 _ _ _ _ _ _) fun _ ↦ cg_ret _

/-- **The `E2` front commits nothing and asks no proof of work** (`cg_kgProgS`'s twin). -/
theorem cg_kgProgF (s : RecursionFast.Digest) (n : ℕ) : NoCG (kgProgF s n) :=
  NoCG.bind (cg_tapeProgE2 _ _ _ _ _) fun _ ↦ NoCG.bind (cg_callerProgE2 _) fun _ ↦
    NoCG.bind (cg_ksLinkProgE2 _ _ _) fun _ ↦ cg_ret _

/-! ## The continuation rows -/

theorem spongeBlocksF_eq : spongeBlocksF P20F accVF = 4295 := checks_P20F.1.2.2.2.2.1

/-- **`contRowsF`'s structure** (`kg_struct`'s at S2GF): distinct, inside `[1, 2^13)`. -/
theorem contRowsF_struct : contRowsF.Nodup ∧ ∀ i ∈ contRowsF, 1 ≤ i ∧ i < 2 ^ (9 + 4) := by
  have hs : spongeBlocksF P20F accVF - 1 < ksSplit P20 + 400 ∧ ksSplit P20 + 400 + 31 ≤ 2 ^ (9 + 4) := by
    rw [spongeBlocksF_eq, Lvm.ksSplit_P20]
    decide
  refine ⟨?_, ?_⟩
  · unfold contRowsF
    rw [List.nodup_append]
    refine ⟨(List.nodup_range).map fun a b h ↦ by omega, (List.nodup_range).map fun a b h ↦ by omega,
      fun a ha b hb hab ↦ ?_⟩
    simp only [List.mem_map, List.mem_range] at ha hb
    obtain ⟨a', ha', rfl⟩ := ha
    obtain ⟨b', hb', rfl⟩ := hb
    omega
  · intro i hi
    unfold contRowsF at hi
    simp only [List.mem_append, List.mem_map, List.mem_range] at hi
    rcases hi with ⟨a, ha, rfl⟩ | ⟨b, hb, rfl⟩ <;> omega

/-! ## The typed phases at the pinned pairs -/

section Typed

open LeanVM.Protocol.EndToEnd LeanVM.Protocol.EndToEnd.Front
open Lvm.ASM (Pair RootShapeM LkSJ BndS εS)
open Lvm.Typed (TInst THypX GbTX BT TRet typedProgX)
open Lvm.Shape (vp)
open LeanVM.Protocol.EndToEnd.Sound (RetOK)
open LeanVM.Protocol.Whir.Sound (IsMultiaffine)
open Lvm.ASM (OpenClaims)
open Lvm.E2F (candRelZ)
open scoped ENNReal

theorem candZ_append (za : List E × E) (h₀ l : List Ev) (h1 : 1 ≤ (commits h₀).length) :
    Lvm.E2F.candZ za (h₀ ++ l) = Lvm.E2F.candZ za h₀ := by
  unfold Lvm.E2F.candZ Lvm.E2F.PinOK Lvm.E2F.pinCons
  rw [Lvm.Typed.candM_append h₀ l h1]

theorem candRelZ_stable (recOf : List UInt8 → Column CMain.nu20 → Column 19) (za : List E × E)
    (x : List UInt8) : Stable (candRelZ recOf za x) := fun h₀ l hl ↦ by
  rw [Lvm.E2F.candRelZ, Lvm.E2F.candRelZ, Lvm.E2F.candZ_stable za h₀ l hl]

theorem candRelZ_ncard_le (recOf : List UInt8 → Column CMain.nu20 → Column 19) (za : List E × E)
    (x : List UInt8) (h : List Ev) : (candRelZ recOf za x h).ncard ≤ 1 :=
  (Set.ncard_image_le (Set.toFinite _)).trans (Lvm.E2F.candZ_ncard_le za h)

theorem pinPost_append (za : List E × E) {h₀ l : List Ev} (hl : commits l = [])
    (hr : Lvm.E2F.PinPost za h₀) : Lvm.E2F.PinPost za (h₀ ++ l) :=
  ⟨Lvm.Typed.rootShapeM_append hl hr.1, by
    unfold Lvm.E2F.PinOK; rw [Lvm.E2F.pinCons_stable za h₀ l hl]; exact hr.2⟩

/-- The viewed pinned pairs. -/
def imgCZ (recOf : List UInt8 → Column CMain.nu20 → Column 19) (za : List E × E) (x : List UInt8)
    (h : List Ev) : Set Pair :=
  vp x '' candRelZ recOf za x h

theorem imgCZ_append (recOf : List UInt8 → Column CMain.nu20 → Column 19) (za : List E × E)
    (x : List UInt8) (h₀ l : List Ev) (h1 : 1 ≤ (commits h₀).length) :
    imgCZ recOf za x (h₀ ++ l) = imgCZ recOf za x h₀ := by
  rw [imgCZ, imgCZ, Lvm.E2F.candRelZ, Lvm.E2F.candRelZ, candZ_append za h₀ l h1]

theorem imgCZ_ncard_le (recOf : List UInt8 → Column CMain.nu20 → Column 19) (za : List E × E)
    (x : List UInt8) (h : List Ev) : (imgCZ recOf za x h).ncard ≤ 37696 :=
  (Set.ncard_image_le (Set.toFinite _)).trans
    ((candRelZ_ncard_le recOf za x h).trans (by norm_num))

theorem doomed_imgCZ {recOf : List UInt8 → Column CMain.nu20 → Column 19} {za : List E × E}
    {x : List UInt8} {A : Pair → Prop} {h : List Ev} :
    Doomed (imgCZ recOf za x) A h ↔ Doomed (candRelZ recOf za x) (fun p ↦ A (vp x p)) h :=
  ⟨fun hd p hp ↦ hd _ ⟨p, hp, rfl⟩, fun hd _ ⟨p, hp, e⟩ ↦ e ▸ hd p hp⟩

/-- `errE (6·2^61) = 6·2^-131`. -/
theorem errE_six_eq : LeanVM.Protocol.KeccakGkr.errE (6 * 2 ^ 61) = 6 * (2 : ℝ≥0∞)⁻¹ ^ 131 := by
  unfold LeanVM.Protocol.KeccakGkr.errE
  rw [BF64.card_ext3, Nat.cast_pow, Nat.cast_ofNat, Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat,
    Nat.cast_ofNat, show (192 : ℕ) = 61 + 131 from rfl, pow_add,
    ENNReal.mul_inv (Or.inl (pow_ne_zero _ two_ne_zero)) (Or.inl (ENNReal.pow_ne_top ENNReal.ofNat_ne_top)),
    mul_assoc, ← mul_assoc ((2 : ℝ≥0∞) ^ 61),
    ENNReal.mul_inv_cancel (pow_ne_zero _ two_ne_zero) (ENNReal.pow_ne_top ENNReal.ofNat_ne_top), one_mul,
    ENNReal.inv_pow]

/-- The coordinate-split typed phases' lead at `37,696` candidates (`τ` and `ω`, 21 samples) is far below
`6·2^-131`. -/
theorem leadTX_le_six : Lvm.Typed.leadTX 37696 ≤ 6 * (2 : ℝ≥0∞)⁻¹ ^ 131 := by
  rw [Lvm.Typed.leadTX, add_zero, Lvm.ASM.errE_smul, Lvm.ASM.errE_smul, ← errE_six_eq]
  exact LeanVM.Protocol.KeccakGkr.errE_mono (by norm_num)

/-- **The coordinate-split typed phases commit nothing and ask no proof of work.** -/
theorem cg_typedProgX (Ti : TInst) (pub : Lvm.Pub) : NoCG (typedProgX Ti pub) := by
  unfold typedProgX Lvm.Typed.zeroProgX Lvm.Typed.wireProgX Lvm.Typed.relayProg Lvm.Typed.miniBusProg
    Lvm.Typed.accProgQX Lvm.M3.lbusTableCheckProg
  refine NoCG.bind (NoCG.bind (cg_sampleChallenges _) fun _ ↦ NoCG.bind cg_sample fun _ ↦
    NoCG.bind (Lvm.M3.cg_sumcheck _ _ _) fun _ ↦ NoCG.bind (Lvm.M3.cg_readScalars _) fun _ ↦
      NoCG.bind (cg_require _) fun _ ↦ cg_ret _) fun _ ↦ ?_
  refine NoCG.bind (NoCG.bind cg_sample fun _ ↦ NoCG.bind (Lvm.M3.cg_sumcheck _ _ _) fun _ ↦
    NoCG.bind (Lvm.M3.cg_readScalars _) fun _ ↦ NoCG.bind (Lvm.M3.cg_readScalars _) fun _ ↦
      NoCG.bind (cg_require _) fun _ ↦ cg_ret _) fun _ ↦ ?_
  refine NoCG.bind (NoCG.bind (Lvm.M3.cg_sumcheck _ _ _) fun _ ↦ NoCG.bind cg_readScalar fun _ ↦
    NoCG.bind (cg_require _) fun _ ↦ cg_ret _) fun _ ↦ ?_
  exact NoCG.bind (Lvm.Acc.cg_accProg _ _ _ _ _ _ _ _) fun _ ↦
    NoCG.bind (NoCG.bind (NoCG.bind (Lvm.M3.cg_lvmBusProg _) fun _ ↦ Lvm.M3.cg_tablePhaseClaims _ _ _)
      fun _ ↦ NoCG.bind (cg_require _) fun _ ↦ cg_ret _) fun _ ↦ cg_ret _

/-- **Every return of the coordinate-split typed phases meets `TRet`** (the claims are `typedClaims`, as
`retOK_typedProg`'s). -/
theorem retOK_typedProgX {Ti : TInst} (H : THypX Ti) (pub : Lvm.Pub) : RetOK TRet (typedProgX Ti pub) := by
  unfold typedProgX
  refine RetOK.bind_true fun z ↦ RetOK.bind_true fun w ↦ RetOK.bind_true fun r ↦ RetOK.bind_true fun _ ↦ ?_
  refine (Lvm.ASM.retOK_lbusTableCheckProg Ti.mbT Lvm.Typed.miniDepth).bind fun cl hcl ↦ RetOK.ret ?_
  have hm1 := Lvm.Typed.isMultiaffine_miniClaims Ti H.layOk .crec cl
  have hm2 := Lvm.Typed.isMultiaffine_miniClaims Ti H.layOk .main cl
  have hl1 := Lvm.Typed.length_miniClaims Ti .crec cl
  have hl2 := Lvm.Typed.length_miniClaims Ti .main cl
  have hcl' : cl.length ≤ 2 ^ 38 := hcl.2.trans H.widths
  refine ⟨fun c hc ↦ ?_, fun c hc ↦ ?_, ?_, ?_⟩
  · rcases List.mem_cons.mp hc with rfl | hc
    · exact Lvm.ASM.isMultiaffine_onStack _ le_rfl (Lvm.ASM.isMultiaffine_eqEvalN _ _)
    rcases List.mem_cons.mp hc with rfl | hc
    · exact Lvm.Typed.isMultiaffine_regClaim Ti 19 _ _ _ _
    · exact hm1 c hc
  · rcases List.mem_cons.mp hc with rfl | hc
    · exact Lvm.Typed.isMultiaffine_regClaim Ti _ _ _ _ _
    rcases List.mem_cons.mp hc with rfl | hc
    · exact Lvm.Typed.isMultiaffine_regClaim Ti _ _ _ _ _
    · exact hm2 c hc
  · simp only [Lvm.Typed.typedClaims, List.length_cons]; omega
  · simp only [Lvm.Typed.typedClaims, List.length_cons]; omega

/-- The coordinate-split typed phases return at most `2^39 + 4` claims. -/
theorem retOK_typedProgX_len {Ti : TInst} (H : THypX Ti) (pub : Lvm.Pub) :
    RetOK (fun a : OpenClaims ↦ a.1.length + a.2.length ≤ 2 ^ 39 + 4) (typedProgX Ti pub) := by
  unfold typedProgX
  refine RetOK.bind_true fun z ↦ RetOK.bind_true fun w ↦ RetOK.bind_true fun r ↦ RetOK.bind_true fun _ ↦ ?_
  refine (Lvm.ASM.retOK_lbusTableCheckProg Ti.mbT Lvm.Typed.miniDepth).bind fun cl hcl ↦ RetOK.ret ?_
  have hl1 := Lvm.Typed.length_miniClaims Ti .crec cl
  have hl2 := Lvm.Typed.length_miniClaims Ti .main cl
  have hcl' : cl.length ≤ 2 ^ 38 := hcl.2.trans H.widths
  simp only [Lvm.Typed.typedClaims, List.length_cons]
  norm_num at hcl' ⊢
  omega

variable {Ti : TInst}

/-- **The coordinate-split typed phases on the viewed pinned pairs** (`specBusTM` with `candRelZ`, `PinPost`, on
`typedSpecX`), the `KS` half of the good pair a parameter `Gk`; lead `6·2^-131`. -/
noncomputable def specBusTF (H : THypX Ti) (recOf : List UInt8 → Column CMain.nu20 → Column 19)
    (za : List E × E) (x : List UInt8) (Gk N : Pair → Prop) :
    Spec (typedProgX Ti (Lvm.VEq.pubXF x))
      (fun h ↦ Lvm.E2F.PinPost za h ∧
        Doomed (candRelZ recOf za x) (fun p ↦ GbTX Ti H x (vp x p) ∧ (Gk (vp x p) ∧ N (vp x p))) h)
      (fun a h ↦ Doomed (candRelZ recOf za x)
        (fun p ↦ (BT x a (vp x p) ∧ N (vp x p)) ∧ (Gk (vp x p) ∧ N (vp x p))) h ∧ Lvm.E2F.PinPost za h)
      εS (6 * (2 : ℝ≥0∞)⁻¹ ^ 131) LkSJ :=
  have S0 := Lvm.Typed.typedSpecX Ti Lvm.M3.lay26 (Lvm.VEq.pubXF x) H.hτ H.ok H.maps rfl (H.acc x) H.sc
    H.layOk H.keys H.width H.fix (H.μBus H.hτ) (imgCZ recOf za x)
    (fun p ↦ BndS x p.1 ∧ Gk p ∧ N p) (L₀ := 37696) (εmax := εS) (T := LkSJ)
    (fun h ↦ 1 ≤ (commits h).length) (imgCZ_append recOf za x) (fun _ ↦ Set.toFinite _)
    (imgCZ_ncard_le recOf za x) (H.errs H.hτ)
  (S0.frame (Lvm.E2F.PinPost za) (fun _ _ hl hr ↦ pinPost_append za
      ((cg_typedProgX Ti (Lvm.VEq.pubXF x)).1.reach_commits hl) hr)).mono
    (fun _ ⟨hr, hDm⟩ ↦ ⟨⟨Lvm.Typed.rootShapeM_one hr.1, Lvm.Typed.rootShapeM_firstWord hr.1,
      doomed_imgCZ.mpr (Doomed.mono hDm fun _ hq ↦ ⟨⟨⟨hq.1, hq.2.1.1⟩, hq.2.2⟩, hq.2.1.2⟩)⟩, hr⟩)
    (fun _ _ hp ↦ ⟨Doomed.mono (doomed_imgCZ.mp hp.1) fun _ hq ↦ ⟨hq.1.1.1, hq.1.1.2, hq.2.1, hq.1.2⟩,
      hp.2⟩)
    le_rfl leadTX_le_six le_rfl

end Typed

/-! ## The `E2` front's specification -/

section Front

open LeanVM.Protocol.EndToEnd.Front
open LeanVM.Protocol.KeccakGkr (errE RegionValid)
open Lvm.KG (TapeOut dOf KSRel SpongeLink ksMsg ksSplitN ksY ksYRow)
open Lvm.ASM (εS)
open scoped ENNReal

theorem sum7_le_εS : (∑ _i ∈ Finset.range 7, errE 1) + 0 ≤ εS := by
  rw [add_zero, Finset.sum_const, Finset.card_range, nsmul_eq_mul, Lvm.ASM.errE_smul]
  exact Lvm.ASM.errE_le_εS7 (by norm_num)

variable {β : Type} {C : List Ev → Set β} [Finite β]

/-- The claims the `E2` front leaves on a candidate (`KcS`'s twin): the tape's row claim and tied lanes, `KS`'s
caller claims, the `KS` link's four combined claims. -/
def KcFr (y2 : ℕ) (col main ks : ℕ → K) (M X : ℕ → ℕ → K) (out : KgOutF) : Prop :=
  (RowColTrue (17 + 6) col out.1.2.2.2.d.row ∧ TiedDF 20 (dOf 20 0 col) out.1.1 out.1.2.1) ∧
  (CallerClaimsE2 13 25 ks (ksY 13 y2 main ks) out.2.1 ∧
    KsClaimsE2 13 9 ks (ksYRow 13 y2 main ks) M X (out.2.2.1.drop 13) out.2.2.2.1.1 out.2.2.2.2)

open Classical in
/-- **The `E2` front** (`kgSpecS`'s twin at S2GF): the tape caller (`tapeSpecE2`), `KS` (`ksSpecE2`), the `KS`
link (`ksLinkSpecE2` on `contRowsF`), from doom of the tape's chain part, `KS`'s relation and `R` to doom of
every claim they leave and `R`. Lead `0`; every group `≤ εS`. -/
noncomputable def kgSpecF (hst : Stable C) (hcard : ∀ h, (C h).ncard ≤ 1) (s : RecursionFast.Digest)
    (n y2 : ℕ) (col main ks : β → ℕ → K) (M X : β → ℕ → ℕ → K) (R : β → Prop) {T : ℝ≥0∞}
    (hT : T ≤ εS) :
    Spec (kgProgF s n)
      (Doomed C (fun q ↦ TapeOut 20 s n (dOf 20 0 (col q)) ∧
        KSRel 13 9 y2 contRowsF (main q) (ks q) (M q) (X q) ∧ R q))
      (fun out hist ↦ (out.1.1.length = 20 ∧ out.1.2.1.length = 25 ∧
          out.1.2.2.2.sc.1.length = 20 ∧ out.1.2.2.2.d.sl.1.length = 2) ∧
        (out.2.1.1.length = 13 ∧ out.2.1.2.1.length = 25 ∧ out.2.2.2.1.1.length = 13) ∧
        Doomed C (fun q ↦ KcFr y2 (col q) (main q) (ks q) (M q) (X q) out ∧ R q) hist)
      εS 0 T :=
  ((tapeSpecE2 (P := 15) (sb := 1) (dsel := 0) (h := 17) (T := 0) hst hcard (by norm_num)
      (by norm_num) s col (fun q ↦ KSRel 13 9 y2 contRowsF (main q) (ks q) (M q) (X q) ∧ R q)
      sum7_le_εS).some).bind' fun tp ↦
  if htp : tp.1.length = 20 ∧ tp.2.1.length = 25 ∧ tp.2.2.2.sc.1.length = 20 ∧
      tp.2.2.2.d.sl.1.length = 2 then
    (((ksSpecE2 (T := 0) hst hcard 9 25 le_rfl ks (fun q ↦ ksY 13 y2 (main q) (ks q))
        (fun q ↦ (RowColTrue (17 + 6) (col q) tp.2.2.2.d.row ∧ TiedDF 20 (dOf 20 0 (col q)) tp.1 tp.2.1) ∧
          SpongeLink 13 contRowsF (ks q) (ksYRow 13 y2 (main q) (ks q))
            (ksMsg (ksSplitN 13 9) (M q) (X q)) ∧ R q) sum7_le_εS).some).mono
      (fun _ hd ↦ Doomed.mono hd.2.2.2.2 fun _ ⟨hv, ho, ⟨hrow, htied⟩, hl, hR⟩ ↦
        ⟨hrow, htied, ⟨hv, ho, hl⟩, hR⟩)
      (fun _ _ h ↦ h) le_rfl le_rfl le_rfl).bind' fun co ↦
    if hco : co.1.length = 13 ∧ co.2.1.length = 25 then
      (((ksLinkSpecE2 (T := T) hst hcard (9 + 4) 9 (by norm_num) contRowsF contRowsF_struct.1
          contRowsF_struct.2 ks (fun q ↦ ksYRow 13 y2 (main q) (ks q)) M X
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

/-! ## The returns' facts -/

section Ret

open LeanVM.Protocol.EndToEnd.Sound (RetOK)
open LeanVM.Protocol.Whir.Sound (IsMultiaffine)

theorem retOK_e2Reads : ∀ n, RetOK (fun l : List E2 ↦ l.length = n) (e2Reads n)
  | 0 => RetOK.ret rfl
  | n + 1 => RetOK.bind_true fun _ ↦ (retOK_e2Reads n).bind fun xs hxs ↦ RetOK.ret (by simp [hxs])

theorem retOK_e2Samples (g : ℕ) : ∀ n, RetOK (fun l : List E2 ↦ l.length = n) (e2Samples g n)
  | 0 => RetOK.ret rfl
  | n + 1 => RetOK.bind_true fun _ ↦ (retOK_e2Samples g n).bind fun xs hxs ↦
      RetOK.ret (by simp [hxs])

theorem retOK_sumcheckE2 (g count : ℕ) : ∀ (modes : List (Option E2)) (claim : E2),
    RetOK (fun r : List E2 × E2 ↦ r.1.length = modes.length) (sumcheckE2 g claim count modes)
  | [], _ => RetOK.ret rfl
  | _ :: modes, _ => RetOK.bind_true fun _ ↦ RetOK.bind_true fun _ ↦
      (retOK_sumcheckE2 g count modes _).bind fun r hr ↦ RetOK.ret (by simp [hr])

theorem retOK_packRoundsE2 (g : ℕ) : ∀ (rs : List E2) (value scale : E2),
    RetOK (fun r : E2 × E2 × List E2 ↦ r.2.2.length = rs.length) (packRoundsE2 g rs value scale)
  | [], _, _ => RetOK.ret rfl
  | _ :: rs, _, _ => RetOK.bind_true fun _ ↦ RetOK.bind_true fun _ ↦
      (retOK_packRoundsE2 g rs _ _).bind fun r hr ↦ RetOK.ret (by simp [hr])

theorem retOK_verifyKeccakLayerE2 (sh : LeanVM.Protocol.KeccakGkr.Shape) (logSteps step : ℕ)
    (claim : KClaim E2) :
    RetOK (fun c : KClaim E2 ↦ c.point.length = claim.point.length)
      (verifyKeccakLayerE2 sh logSteps step claim) :=
  RetOK.bind_true fun _ ↦ RetOK.bind_true fun _ ↦ RetOK.bind_true fun _ ↦ RetOK.bind_true fun _ ↦
    (retOK_packRoundsE2 _ _ _ _).bind fun _ hr ↦ RetOK.bind_true fun _ ↦ RetOK.bind_true fun _ ↦
      RetOK.bind_true fun _ ↦ RetOK.bind_true fun _ ↦ RetOK.ret hr

theorem retOK_keccakLayersE2 (sh : LeanVM.Protocol.KeccakGkr.Shape) (logSteps : ℕ) :
    ∀ (steps : List ℕ) (claim : KClaim E2),
      RetOK (fun c : KClaim E2 ↦ c.point.length = claim.point.length)
        (keccakLayersE2 sh logSteps steps claim)
  | [], _ => RetOK.ret rfl
  | _ :: steps, _ => (retOK_verifyKeccakLayerE2 _ _ _ _).bind fun c hc ↦
      (retOK_keccakLayersE2 sh logSteps steps c).mono fun _ h ↦ h.trans hc

theorem retOK_rowSwitch (z sv : List E2) :
    RetOK (fun r : E × (List E → E) ↦ IsMultiaffine z.length r.2) (rowSwitch z sv) :=
  RetOK.bind_true fun rr ↦ RetOK.ret (isMultiaffine_rowWeight z rr)

/-- The v1 reduction's word claims, point and slices (`retOK_verifyKeccak_point`'s twin). -/
theorem retOK_vkFlat (P : ℕ) (inst output : List E2) (hi : inst.length = P + 4) :
    RetOK (fun res : List ColClaimE2 × List E2 × List E2 ↦
      ((∀ c ∈ res.1, c.column = qkeccak ∧ c.point.length = P + 4 + 6) ∧ res.1.length ≤ 1) ∧
        res.2.1.length = P + 4 + 6 ∧ res.2.2.length = 64) (vkFlat P inst output) := by
  unfold vkFlat
  refine (retOK_e2Samples _ _).bind fun seg hseg ↦ RetOK.bind_true fun _ ↦ RetOK.bind_true fun _ ↦ ?_
  refine (retOK_keccakLayersE2 _ _ _ _).bind fun claim hclaim ↦ ?_
  refine RetOK.bind (Q' := fun outs : List ColClaimE2 ↦
      (∀ c ∈ outs, c.column = qkeccak ∧ c.point.length = P + 4 + 6) ∧ outs.length ≤ 1) ?_ ?_
  · refine ((retOK_sumcheckE2 _ _ _ _).bind fun sv hsv ↦
      RetOK.ret (Q := fun o : List E2 × List E2 × E2 ↦ o.1.length = 6) (by simpa using hsv)).bind
        fun o ho ↦ RetOK.bind_true fun word ↦ RetOK.bind_true fun _ ↦ RetOK.ret ⟨fun c hc ↦ ?_, by simp⟩
    simp only [List.mem_singleton] at hc
    subst hc
    refine ⟨rfl, ?_⟩
    simp only [List.length_append, List.length_take, List.length_drop, ho, hi]
    omega
  · intro outs hout
    refine (retOK_sumcheckE2 _ _ _ _).bind fun lv hlv ↦ ?_
    refine ((retOK_sumcheckE2 _ _ _ _).bind fun sv hsv ↦
      RetOK.ret (Q := fun o : List E2 × List E2 × E2 ↦ o.1.length = 6) (by simpa using hsv)).bind
        fun o ho ↦ (retOK_e2Reads _).bind fun slices hs ↦ RetOK.bind_true fun _ ↦ RetOK.ret ⟨hout, ?_, hs⟩
    have hcp : claim.point.length = P + 1 := by
      rw [hclaim]
      simp only [firstClaimSF, List.length_append, List.length_drop, hi, hseg]
      omega
    simp only [List.length_append, List.length_take, hlv, ho, hcp, List.length_replicate]
    omega

/-- **Facts of every return of the `E2` front** (`KgRet`'s twin): lengths, the word claims on `q_keccak`, the
row weights' multiaffinity. -/
def KgRetF (k : KgOutF) : Prop :=
  (k.1.1.length = 20 ∧ k.1.2.1.length = 25 ∧ IsMultiaffine 23 k.1.2.2.2.d.row.2) ∧
  (k.2.1.1.length = 13 ∧ k.2.1.2.1.length = 25 ∧
    (∀ c ∈ k.2.1.2.2.1.1, c.column = qkeccak ∧ c.point.length = 19) ∧ k.2.1.2.2.1.1.length ≤ 1 ∧
    IsMultiaffine 19 k.2.1.2.2.2.2) ∧
  (k.2.2.1.length = 18 ∧ k.2.2.2.1.1.length = 13)

theorem retOK_tapeProgE2 (s : RecursionFast.Digest) (n : ℕ) :
    RetOK (fun tp : TapeOutE2 ↦ tp.1.length = 20 ∧ tp.2.1.length = 25 ∧
      IsMultiaffine 23 tp.2.2.2.d.row.2) (tapeProgE2 20 1 0 s n) :=
  RetOK.bind_true fun _ ↦ (retOK_e2Samples _ _).bind fun r hr ↦ (retOK_e2Reads _).bind fun v hv ↦
    RetOK.bind_true fun _ ↦ RetOK.bind_true fun _ ↦
      ((retOK_sumcheckE2 _ _ _ _).bind fun sc hsc ↦ RetOK.bind_true fun _ ↦ RetOK.bind_true fun _ ↦
        ((retOK_sumcheckE2 _ _ _ _).bind fun sl hsl ↦ RetOK.bind_true fun _ ↦ RetOK.bind_true fun _ ↦
          (retOK_rowSwitch _ _).bind fun row hrow ↦
            RetOK.ret (Q := fun d : SlotOutE2 ↦ IsMultiaffine 23 d.row.2) (by
              show IsMultiaffine 23 row.2
              have e : (sc.1 ++ sl.1 ++ selPtF 0 1 : List E2).length = 23 := by
                simp only [List.length_append, hsc, hsl, List.length_replicate, selPtF,
                  List.length_map, List.length_range]
              rw [← e]; exact hrow)).bind fun d hd ↦
          RetOK.ret (Q := fun wo : WireChOutE2 ↦ IsMultiaffine 23 wo.d.row.2) hd).bind fun wo hwo ↦
        RetOK.ret ⟨hr, hv, hwo⟩

theorem retOK_callerProgE2 :
    RetOK (fun co : CallerOutE2 ↦ co.1.length = 13 ∧ co.2.1.length = 25 ∧
      (∀ c ∈ co.2.2.1.1, c.column = qkeccak ∧ c.point.length = 19) ∧ co.2.2.1.1.length ≤ 1 ∧
      IsMultiaffine 19 co.2.2.2.2) (callerProgE2 (9 + 4)) :=
  (retOK_e2Samples _ _).bind fun r hr ↦ (retOK_e2Reads _).bind fun v hv ↦
    ((verifyKeccakE2_flat 9 r v) ▸ retOK_vkFlat 9 r v hr).bind fun res hres ↦
      (retOK_rowSwitch _ _).bind fun row hrow ↦
        RetOK.ret ⟨hr, hv, hres.1.1, hres.1.2, by rw [hres.2.1] at hrow; exact hrow⟩

theorem retOK_ksLinkProgE2 (hk xl : ℕ) (rows : List ℕ) :
    RetOK (fun lo : List E2 × (List E2 × E2) × List E2 ↦ lo.1.length = hk + 5 ∧ lo.2.1.1.length = hk)
      (ksLinkProgE2 hk xl rows) :=
  (retOK_e2Samples _ _).bind fun kc hkc ↦ (retOK_sumcheckE2 _ _ _ _).bind fun ks hks ↦
    RetOK.bind_true fun _ ↦ RetOK.bind_true fun _ ↦ RetOK.ret ⟨hkc, by simpa using hks⟩

/-- **Every return of the `E2` front meets `KgRetF`.** -/
theorem retOK_kgProgF (s : RecursionFast.Digest) (n : ℕ) : RetOK KgRetF (kgProgF s n) :=
  (retOK_tapeProgE2 s n).bind fun _tp htp ↦ retOK_callerProgE2.bind fun _co hco ↦
    (retOK_ksLinkProgE2 _ _ _).bind fun _lo hlo ↦ RetOK.ret ⟨htp, hco, hlo⟩

end Ret

/-! ## The split claims' meaning (`LvmE2VMidSpec`'s `SumE2.Holds`, `SumE2.Fits`, restated) -/

section Split

open LeanVM.Protocol.Whir.Sound (IsMultiaffine)
open Lvm.VEq (BClaim VPlacement)
open Finset

/-- `SumE2.Holds`, restated (the same body). -/
def holdsE2 (c : SumE2) (col : ℕ → K) : Prop :=
  (c.parts.map fun p ↦ p.1 *
    ∑ n ∈ range (2 ^ p.2.1.variableCount), eqAtF p.2.2 n * Lvm.Quad.C (col (p.2.1.index + n))).sum = c.value

/-- `SumE2.Fits`, restated (the same body). -/
def fitsE2 (nu : ℕ) (c : SumE2) : Prop :=
  ∀ p ∈ c.parts, p.2.2.length = p.2.1.variableCount ∧ p.2.1.variableCount ≤ nu ∧
    2 ^ p.2.1.variableCount ∣ p.2.1.index ∧ p.2.1.index + 2 ^ p.2.1.variableCount ≤ 2 ^ nu

/-- `splitE2_sound`'s statement. -/
def SplitSound : Prop :=
  ∀ (nu : ℕ) (c : SumE2), fitsE2 nu c → ∀ q : Column nu, ¬ holdsE2 c (fun i ↦ q.values.getD i 0) →
    ∃ b ∈ splitE2 nu c, ¬ LeanVM.Protocol.EndToEnd.StackClaim.Holds nu b.onStack q

/-- `isMultiaffine_splitE2`'s statement. -/
def SplitAffine : Prop :=
  ∀ (nu : ℕ) (c : SumE2), fitsE2 nu c → ∀ b ∈ splitE2 nu c, IsMultiaffine nu b.onStack.1

theorem holdsE2_of (hS : SplitSound) {nu : ℕ} {c : SumE2} (hc : fitsE2 nu c) (q : Column nu)
    (H : ∀ b ∈ splitE2 nu c, LeanVM.Protocol.EndToEnd.StackClaim.Holds nu b.onStack q) :
    holdsE2 c (fun i ↦ q.values.getD i 0) := by
  by_contra hn
  obtain ⟨b, hb, hnb⟩ := hS nu c hc q hn
  exact hnb (H b hb)

theorem holdsE2_point (blk : VPlacement) (z : List E2) (v : E2) (col : ℕ → K) :
    holdsE2 (pointE2 blk z v) col ↔
      ∑ n ∈ range (2 ^ blk.variableCount), eqAtF z n * Lvm.Quad.C (col (blk.index + n)) = v := by
  simp [holdsE2, pointE2]

theorem fitsE2_point {nu : ℕ} {blk : VPlacement} {z : List E2} (v : E2) (hz : z.length = blk.variableCount)
    (hv : blk.variableCount ≤ nu) (hal : 2 ^ blk.variableCount ∣ blk.index)
    (hfit : blk.index + 2 ^ blk.variableCount ≤ 2 ^ nu) : fitsE2 nu (pointE2 blk z v) := by
  intro p hp
  simp only [pointE2, List.mem_singleton] at hp
  subst hp
  exact ⟨hz, hv, hal, hfit⟩

/-- A list sum over `range k` is the `Finset` sum. -/
theorem sum_map_rangeE2 (g : ℕ → E2) : ∀ k, ((List.range k).map g).sum = ∑ l ∈ range k, g l
  | 0 => by simp
  | k + 1 => by
    rw [List.range_succ, List.map_append, List.sum_append, sum_map_rangeE2 g k, Finset.sum_range_succ]
    simp

/-- A sum weighted by `eq(a ‖ sel(b), ·)` is slot `b`'s. -/
theorem sum_selF {h k b : ℕ} {a : List E2} (ha : a.length = h) (hb : b < 2 ^ k) (G : ℕ → E2) :
    ∑ n ∈ range (2 ^ (h + k)), eqAtF (a ++ selPtF b k) n * G n =
      ∑ x ∈ range (2 ^ h), eqAtF a x * G (x + 2 ^ h * b) := by
  have hs : (selPtF b k : List E2).length = k := by simp [selPtF]
  have e := col_splitF (s := (selPtF b k : List E2)) ha G
  rw [hs] at e
  rw [e, selPtF_eq_bitsF, sum_eqAtF_bitsF hb]

end Split

/-! ## The front's claims holding on the commitments -/

section Link

open LeanVM.Protocol.Whir.Sound (IsMultiaffine)
open Lvm.VEq (BClaim VPlacement selE dBlkE ksBlk ksY2Off xOff nuMainE)
open Lvm.NS (colM ksCol ksY2 msgM msgX)
open Finset

local notation "Holds" => LeanVM.Protocol.EndToEnd.StackClaim.Holds

/-- A point claim at `E2` whose two split claims hold. -/
theorem point_of_split (hS : SplitSound) {nu : ℕ} {blk : VPlacement} {z : List E2} {v : E2}
    (hz : z.length = blk.variableCount) (hv : blk.variableCount ≤ nu)
    (hal : 2 ^ blk.variableCount ∣ blk.index) (hfit : blk.index + 2 ^ blk.variableCount ≤ 2 ^ nu)
    (q : Column nu) (H : ∀ b ∈ splitE2 nu (pointE2 blk z v), Holds nu b.onStack q) :
    ∑ n ∈ range (2 ^ blk.variableCount), eqAtF z n * Lvm.Quad.C (q.values.getD (blk.index + n) 0) = v := by
  have h := (holdsE2_point blk z v (fun i ↦ q.values.getD i 0)).1
    (holdsE2_of hS (fitsE2_point v hz hv hal hfit) q H)
  exact h

/-- **The tape's tied lanes** (`tapeClaims_of`'s second half at `E2`). -/
theorem tiedDF_of (hS : SplitSound) (tp : TapeOutE2) (hr : tp.1.length = 20) {qm : Column CMain.nu20}
    (H : ∀ l < 4, ∀ b ∈ splitE2 nuMainE (pointE2 dBlkE (tp.1 ++ selPtF l 2) (tp.2.1.getD l 0)),
      Holds CMain.nu20 b.onStack qm) :
    TiedDF 20 (Lvm.KG.dOf 20 0 (colM qm)) tp.1 tp.2.1 := by
  intro l hl
  have e := point_of_split hS (blk := dBlkE) (z := tp.1 ++ selPtF l 2)
    (by simp [hr, dBlkE, selPtF]) (by decide) (by simp [dBlkE]) (by decide) qm (H l hl)
  simp only [dBlkE, CMain.dOff20, zero_add] at e
  rw [sum_selF (h := 20) (k := 2) hr (by omega)] at e
  rw [← e]
  refine Finset.sum_congr rfl fun x _ ↦ ?_
  simp only [Lvm.KG.dOf, colM, Lvm.NS.wd, Nat.mul_zero, Nat.add_zero]
  rfl

/-- **A row claim on a block** (`ringCol_of_holds` at `E2`'s row switch). -/
theorem rowCol_of_holds {μ h off : ℕ} (hal : 2 ^ (h + 6) ∣ off) (hfit : off + 2 ^ (h + 6) ≤ 2 ^ μ)
    {q : Column μ} {row : E × (List E → E)}
    (H : Holds μ (⟨⟨h + 6, off⟩, row.2, row.1⟩ : BClaim).onStack q) :
    RowColTrue (h + 6) (fun n ↦ q.values.getD (off + n) 0) row :=
  Lvm.ASM.Kec.ringCol_of_holds hal hfit H

/-- The tape's row claim on the whole `C_main`. -/
theorem rowTape_of (tp : TapeOutE2) {qm : Column CMain.nu20}
    (H : Holds CMain.nu20 (⟨⟨nuMainE, 0⟩, tp.2.2.2.d.row.2, tp.2.2.2.d.row.1⟩ : BClaim).onStack qm) :
    RowColTrue (17 + 6) (colM qm) tp.2.2.2.d.row := by
  have := rowCol_of_holds (μ := CMain.nu20) (h := 17) (off := 0) (dvd_zero _) (by norm_num) H
  have e : (fun n ↦ qm.values.getD (0 + n) 0) = colM qm := funext fun n ↦ by
    simp [colM, Lvm.NS.wd]
  rw [e] at this
  exact this

/-- **`KS`'s caller claims at `E2`** (`callerClaims_ks`'s twin). -/
theorem callerClaimsE2_of (hS : SplitSound) (co : CallerOutE2) (hr : co.1.length = 13)
    (hcol : ∀ c ∈ co.2.2.1.1, c.column = qkeccak ∧ c.point.length = 19) {qm : Column CMain.nu20}
    (hrow : Holds CMain.nu20 (⟨ksBlk, co.2.2.2.2, co.2.2.2.1⟩ : BClaim).onStack qm)
    (hw : ∀ c ∈ co.2.2.1.1, ∀ b ∈ splitE2 nuMainE (pointE2 ksBlk c.point c.value),
      Holds CMain.nu20 b.onStack qm)
    (ho : ∀ l < 25, ∀ b ∈ splitE2 nuMainE (pointE2 (ksYPartF l co.1).1 (ksYPartF l co.1).2 (co.2.1.getD l 0)),
      Holds CMain.nu20 b.onStack qm) :
    CallerClaimsE2 13 25 (ksCol qm) (Lvm.KG.ksY 13 ksY2 (colM qm) (ksCol qm)) co := by
  have hal : 2 ^ (13 + 6) ∣ CMain.ksOff20 := ⟨10, by norm_num⟩
  have hfit : CMain.ksOff20 + 2 ^ (13 + 6) ≤ 2 ^ CMain.nu20 := by norm_num
  refine ⟨rowCol_of_holds (μ := CMain.nu20) hal hfit hrow, fun c hc ↦ ⟨(hcol c hc).1, (hcol c hc).2, ?_⟩,
    fun l hl ↦ ?_⟩
  · have e := point_of_split hS (blk := ksBlk) (z := c.point) (by simp [ksBlk, slotLog, (hcol c hc).2])
      (by decide) (by show 2 ^ (13 + 6) ∣ CMain.ksOff20; exact ⟨10, by norm_num⟩) (by decide) qm (hw c hc)
    rw [← e]
    rfl
  · have H := ho l hl
    unfold stepMleF Lvm.KG.ksY
    by_cases h14 : l < 14
    · simp only [ite_eq_left h14]
      have eP : ksYPartF l co.1 = (ksBlk, co.1 ++ selPtF (50 + l) slotLog) := if_pos h14
      rw [eP] at H
      have e := point_of_split hS (blk := ksBlk) (z := co.1 ++ selPtF (50 + l) slotLog)
        (by simp [ksBlk, slotLog, hr, selPtF]) (by decide)
        (by show 2 ^ (13 + 6) ∣ CMain.ksOff20; exact ⟨10, by norm_num⟩) (by decide) qm H
      simp only [ksBlk, slotLog] at e
      rw [sum_selF (h := 13) (k := 6) hr (by omega)] at e
      rw [← e]
      refine Finset.sum_congr rfl fun x _ ↦ ?_
      simp only [ksCol, Lvm.NS.wd]
      rfl
    · simp only [ite_eq_right h14]
      have eP : ksYPartF l co.1 = (⟨13, ksY2Off + (l - 14) * 2 ^ 13⟩, co.1) := if_neg h14
      rw [eP] at H
      have hal' : 2 ^ 13 ∣ ksY2Off + (l - 14) * 2 ^ 13 :=
        Nat.dvd_add ⟨739, by norm_num [ksY2Off]⟩ (Nat.dvd_mul_left _ _)
      have hfit' : ksY2Off + (l - 14) * 2 ^ 13 + 2 ^ 13 ≤ 2 ^ CMain.nu20 := by
        simp only [ksY2Off]; norm_num; omega
      have e := point_of_split hS (blk := ⟨13, ksY2Off + (l - 14) * 2 ^ 13⟩) (z := co.1) hr
        (by show 13 ≤ CMain.nu20; norm_num) hal' hfit' qm H
      rw [← e]
      refine Finset.sum_congr rfl fun x _ ↦ ?_
      simp only [colM, Lvm.NS.wd, ksY2, ksY2Off]
      rfl

end Link

/-! ## The `KS` link's claims -/

section LinkKS

open LeanVM.Protocol.Whir.Sound (IsMultiaffine)
open Lvm.VEq (BClaim VPlacement selE dBlkE ksBlk ksY2Off xOff nuMainE)
open Lvm.NS (colM ksCol ksY2 msgM msgX)
open Finset

local notation "Holds" => LeanVM.Protocol.EndToEnd.StackClaim.Holds

/-- **The cut at the split** at `F` (`cut_split`). -/
theorem cut_splitF {F : Type} [Field F] [CharP F 2] {hk xl : ℕ} (hxl : xl ≤ hk) {pt : List F}
    (hpt : pt.length = hk) (G : ℕ → F) :
    ∑ n ∈ range (2 ^ hk), eqAtF pt n * G n +
        selXF xl pt * ∑ n ∈ range (2 ^ xl), eqAtF (pt.take xl) n * G (Lvm.KG.ksSplitN hk xl + n) =
      ∑ n ∈ range (Lvm.KG.ksSplitN hk xl), eqAtF pt n * G n := by
  have hz : ∑ j ∈ range (2 ^ xl), (eqAtF pt (Lvm.KG.ksSplitN hk xl + j) * G (Lvm.KG.ksSplitN hk xl + j) +
      selXF xl pt * (eqAtF (pt.take xl) j * G (Lvm.KG.ksSplitN hk xl + j))) = 0 :=
    Finset.sum_eq_zero fun j hj ↦ by
      rw [eqAtF_split hxl hpt (Finset.mem_range.1 hj),
        show selXF xl pt * (eqAtF (pt.take xl) j * G (Lvm.KG.ksSplitN hk xl + j)) =
          eqAtF (pt.take xl) j * selXF xl pt * G (Lvm.KG.ksSplitN hk xl + j) by ring]
      exact CharTwo.add_self_eq_zero _
  rw [show range (2 ^ hk) = range (Lvm.KG.ksSplitN hk xl + 2 ^ xl) by rw [Lvm.KG.ksSplitN_add hxl],
    Finset.sum_range_add, Finset.mul_sum, add_assoc, ← Finset.sum_add_distrib, hz, add_zero]

/-- The link's `Y` claim (`ksLinkClaimsF`'s `yC`). -/
def ksYCF (kchal : List E2) (kshift : List E2 × E2) (vals : List E2) : SumE2 :=
  ⟨(List.range 25).map fun l ↦
    let bz := ksYPartF l kshift.1
    ((eqKernelF (kchal.drop 13)).getD l 0, bz.1, bz.2), vals.getD 0 0⟩

/-- The link's `in` claim. -/
def ksInCF (kchal : List E2) (kshift : List E2 × E2) (vals : List E2) : SumE2 :=
  ⟨(List.range 25).map fun l ↦ ((eqKernelF (kchal.drop 13)).getD l 0, ksBlk, kshift.1 ++ selPtF l slotLog),
    vals.getD 1 0⟩

/-- The link's `M` claim (on `C_rec`). -/
def ksMCF (kchal : List E2) (kshift : List E2 × E2) (vals : List E2) : SumE2 :=
  ⟨(List.range 17).map (fun l ↦ ((eqKernelF (kchal.drop 13)).getD l 0, (⟨13, l * 2 ^ 14⟩ : VPlacement),
      kshift.1)) ++
    (List.range 17).map (fun l ↦ ((eqKernelF (kchal.drop 13)).getD l 0 * selXF 9 kshift.1,
      (⟨9, l * 2 ^ 14 + ksSplit P20⟩ : VPlacement), kshift.1.take 9)),
    vals.getD 2 0⟩

/-- The link's `X` claim. -/
def ksXCF (kchal : List E2) (kshift : List E2 × E2) (vals : List E2) : SumE2 :=
  ⟨(List.range 17).map fun l ↦ ((eqKernelF (kchal.drop 13)).getD l 0,
    (⟨9, xOff + l * 2 ^ 14⟩ : VPlacement), kshift.1.take 9), vals.getD 3 0⟩

theorem ksLinkClaimsF_eq (kchal : List E2) (kshift : List E2 × E2) (vals : List E2) :
    ksLinkClaimsF kchal kshift vals =
      (splitE2 nuMainE (ksYCF kchal kshift vals)).map (.main, ·) ++
        (splitE2 nuMainE (ksInCF kchal kshift vals)).map (.main, ·) ++
        (splitE2 19 (ksMCF kchal kshift vals)).map (.crec, ·) ++
        (splitE2 nuMainE (ksXCF kchal kshift vals)).map (.main, ·) := rfl

theorem fits_ksYCF {kchal : List E2} {kshift : List E2 × E2} (vals : List E2)
    (h2 : kshift.1.length = 13) : fitsE2 nuMainE (ksYCF kchal kshift vals) := by
  intro p hp
  simp only [ksYCF, List.mem_map, List.mem_range] at hp
  obtain ⟨l, hl, rfl⟩ := hp
  by_cases h14 : l < 14
  · simp only [ksYPartF, h14, ↓reduceIte, ksBlk, slotLog]
    refine ⟨by simp [h2, selPtF], by decide, ⟨10, by norm_num⟩, by norm_num [nuMainE]⟩
  · simp only [ksYPartF, h14, ↓reduceIte]
    exact ⟨h2, by show 13 ≤ CMain.nu20; norm_num, ⟨739 + (l - 14), by rw [ksY2Off]; ring⟩,
      by show ksY2Off + (l - 14) * 2 ^ 13 + 2 ^ 13 ≤ 2 ^ CMain.nu20; rw [ksY2Off]; norm_num; omega⟩

theorem fits_ksInCF {kchal : List E2} {kshift : List E2 × E2} (vals : List E2)
    (h2 : kshift.1.length = 13) : fitsE2 nuMainE (ksInCF kchal kshift vals) := by
  intro p hp
  simp only [ksInCF, List.mem_map, List.mem_range] at hp
  obtain ⟨l, hl, rfl⟩ := hp
  simp only [ksBlk, slotLog]
  exact ⟨by simp [h2, selPtF], by decide, ⟨10, by norm_num⟩, by norm_num [nuMainE]⟩

theorem fits_ksMCF {kchal : List E2} {kshift : List E2 × E2} (vals : List E2)
    (h2 : kshift.1.length = 13) : fitsE2 19 (ksMCF kchal kshift vals) := by
  have hsp : ksSplit P20 = 7680 := Lvm.ksSplit_P20
  intro p hp
  simp only [ksMCF, List.mem_append, List.mem_map, List.mem_range] at hp
  rcases hp with ⟨l, hl, rfl⟩ | ⟨l, hl, rfl⟩
  · exact ⟨h2, by norm_num, ⟨2 * l, by ring⟩, by dsimp only; omega⟩
  · exact ⟨by simp [h2], by norm_num, ⟨l * 32 + 15, by rw [hsp]; ring⟩, by dsimp only; rw [hsp]; omega⟩

theorem fits_ksXCF {kchal : List E2} {kshift : List E2 × E2} (vals : List E2)
    (h2 : kshift.1.length = 13) : fitsE2 nuMainE (ksXCF kchal kshift vals) := by
  intro p hp
  simp only [ksXCF, List.mem_map, List.mem_range] at hp
  obtain ⟨l, hl, rfl⟩ := hp
  exact ⟨by simp [h2], by show 9 ≤ CMain.nu20; norm_num, ⟨11279 + 32 * l, by rw [xOff]; ring⟩,
    by show xOff + l * 2 ^ 14 + 2 ^ 9 ≤ 2 ^ CMain.nu20; simp only [xOff, CMain.xOff20]; norm_num; omega⟩

theorem holdsE2_map_sum (parts : List (ℕ)) (G : ℕ → E2 × VPlacement × List E2) (val : E2) (col : ℕ → K) :
    holdsE2 ⟨parts.map G, val⟩ col ↔
      (parts.map fun l ↦ (G l).1 * ∑ n ∈ range (2 ^ (G l).2.1.variableCount),
        eqAtF (G l).2.2 n * Lvm.Quad.C (col ((G l).2.1.index + n))).sum = val := by
  simp only [holdsE2, List.map_map]
  rfl

/-- **The `KS` link's claims at `E2`** (`ksLinkClaims_of`'s twin). -/
theorem ksClaimsE2_of (hS : SplitSound) (kchal : List E2) (kshift : List E2 × E2) (vals : List E2)
    (h1 : kchal.length = 18) (h2 : kshift.1.length = 13) {qm : Column CMain.nu20} {qr : Column 19}
    (hy : ∀ b ∈ splitE2 nuMainE (ksYCF kchal kshift vals), Holds CMain.nu20 b.onStack qm)
    (hi : ∀ b ∈ splitE2 nuMainE (ksInCF kchal kshift vals), Holds CMain.nu20 b.onStack qm)
    (hm : ∀ b ∈ splitE2 19 (ksMCF kchal kshift vals), Holds 19 b.onStack qr)
    (hx : ∀ b ∈ splitE2 nuMainE (ksXCF kchal kshift vals), Holds CMain.nu20 b.onStack qm) :
    KsClaimsE2 13 9 (ksCol qm) (Lvm.KG.ksYRow 13 ksY2 (colM qm) (ksCol qm)) (msgM qr) (msgX qm)
      (kchal.drop 13) kshift.1 vals := by
  have hlam : (kchal.drop 13).length = 5 := by simp [h1]
  have hom : ∀ l < 25, (eqKernelF (kchal.drop 13)).getD l 0 = eqAtF (kchal.drop 13) l := fun l hl ↦ by
    rw [eqKernelF_getD, hlam, if_pos (by omega)]
  have hlo9 : (kshift.1.take 9).length = 9 := by simp [h2]
  refine ⟨?_, ?_, ?_, ?_⟩
  · have e := holdsE2_of hS (fits_ksYCF vals h2) qm hy
    simp only [ksYCF, holdsE2_map_sum, sum_map_rangeE2] at e
    rw [← e]
    refine Finset.sum_congr rfl fun l hl ↦ ?_
    have hl' := Finset.mem_range.1 hl
    rw [hom l hl']
    refine congrArg (eqAtF (kchal.drop 13) l * ·) ?_
    unfold stepMleF
    by_cases hl14 : l < 14
    · simp only [ksYPartF, hl14, ↓reduceIte, ksBlk, slotLog]
      rw [sum_selF (h := 13) (k := 6) h2 (by omega)]
      refine Finset.sum_congr rfl fun x _ ↦ ?_
      simp only [Lvm.KG.ksYRow, Lvm.KG.ksY, hl14, ↓reduceIte, ksCol, Lvm.NS.wd]
      rfl
    · simp only [ksYPartF, hl14, ↓reduceIte]
      refine Finset.sum_congr rfl fun x _ ↦ ?_
      simp only [Lvm.KG.ksYRow, Lvm.KG.ksY, hl14, ↓reduceIte, colM, Lvm.NS.wd, ksY2Off, ksY2]
      rfl
  · have e := holdsE2_of hS (fits_ksInCF vals h2) qm hi
    simp only [ksInCF, holdsE2_map_sum, sum_map_rangeE2] at e
    rw [← e]
    refine Finset.sum_congr rfl fun l hl ↦ ?_
    have hl' := Finset.mem_range.1 hl
    rw [hom l hl']
    refine congrArg (eqAtF (kchal.drop 13) l * ·) ?_
    unfold stepMleF
    simp only [ksBlk, slotLog]
    rw [sum_selF (h := 13) (k := 6) h2 (by omega)]
    refine Finset.sum_congr rfl fun x _ ↦ ?_
    simp only [ksCol, Lvm.NS.wd]
    rfl
  · have e := holdsE2_of hS (fits_ksMCF vals h2) qr hm
    have hsp : ksSplit P20 = 7680 := Lvm.ksSplit_P20
    have hsN : Lvm.KG.ksSplitN 13 9 = 7680 := by decide
    simp only [ksMCF, holdsE2, List.map_append, List.sum_append, List.map_map] at e
    rw [sum_map_rangeE2, sum_map_rangeE2, ← Finset.sum_add_distrib] at e
    rw [← e]
    refine Finset.sum_congr rfl fun l hl ↦ ?_
    have hl' := Finset.mem_range.1 hl
    simp only [Function.comp_apply]
    rw [hom l (by omega), mul_assoc, ← mul_add]
    refine congrArg (eqAtF (kchal.drop 13) l * ·) ?_
    rw [← cut_splitF (hk := 13) (xl := 9) (by norm_num) h2 (fun n ↦ kF (msgM qr n l))]
    simp only [msgM, Lvm.NS.wd, hsp, hsN, Nat.add_assoc, Lvm.Quad.C_eq_algebraMap]
  · have e := holdsE2_of hS (fits_ksXCF vals h2) qm hx
    simp only [ksXCF, holdsE2_map_sum, sum_map_rangeE2] at e
    rw [← e]
    refine Finset.sum_congr rfl fun l hl ↦ ?_
    have hl' := Finset.mem_range.1 hl
    rw [hom l (by omega)]
    unfold stepMleF
    refine congrArg (eqAtF (kchal.drop 13) l * ·) (Finset.sum_congr rfl fun x _ ↦ ?_)
    simp only [msgX, Lvm.NS.wd, CMain.ksXW20_eq, xOff, CMain.xOff20]
    rfl

end LinkKS

/-! ## The assembled claims -/

section Assembled

open LeanVM.Protocol.Whir.Sound (IsMultiaffine)
open LeanVM.Protocol.KeccakGkr (bitsE sum_eqAt_bitsE)
open Lvm.VEq (BClaim VPlacement selE dBlkE ksBlk ksY2Off xOff nuMainE hdX pubX)
open Lvm.NS (colM ksCol ksY2 msgM msgX)
open Lvm.ASM (BndS OpenClaims Pair)
open Lvm.Typed (TRet BT)
open Lvm.Shape (vp view)
open Finset

local notation "Holds" => LeanVM.Protocol.EndToEnd.StackClaim.Holds

/-- The front's claims with their commitment (`assembleSF`'s list). -/
def claimsF (pub : Lvm.Pub) (kg : KgOutF) : List (Lvm.Com × BClaim) :=
  (tapeClaimsF kg.1 pub ++ keccakClaimsF ksBlk kg.2.1 ++ ksOutputClaimsF kg.2.1.1 kg.2.1.2.1).map (.main, ·) ++
    ksLinkClaimsF kg.2.2.1 kg.2.2.2.1 kg.2.2.2.2

theorem assembleSF_eq (pub : Lvm.Pub) (kg : KgOutF) :
    assembleSF pub kg = (((claimsF pub kg).filter (·.1 == .crec)).map (·.2.onStack),
      ((claimsF pub kg).filter (·.1 == .main)).map (·.2.onStack)) := rfl

theorem mem_assembleSF_main {pub : Lvm.Pub} {kg : KgOutF} {b : BClaim} (hb : (.main, b) ∈ claimsF pub kg) :
    b.onStack ∈ (assembleSF pub kg).2 := by
  rw [assembleSF_eq]
  exact List.mem_map.2 ⟨(.main, b), List.mem_filter.2 ⟨hb, rfl⟩, rfl⟩

theorem mem_assembleSF_crec {pub : Lvm.Pub} {kg : KgOutF} {b : BClaim} (hb : (.crec, b) ∈ claimsF pub kg) :
    b.onStack ∈ (assembleSF pub kg).1 := by
  rw [assembleSF_eq]
  exact List.mem_map.2 ⟨(.crec, b), List.mem_filter.2 ⟨hb, rfl⟩, rfl⟩

theorem mem_claimsF_front {pub : Lvm.Pub} {kg : KgOutF} {b : BClaim}
    (hb : b ∈ tapeClaimsF kg.1 pub ++ keccakClaimsF ksBlk kg.2.1 ++ ksOutputClaimsF kg.2.1.1 kg.2.1.2.1) :
    (.main, b) ∈ claimsF pub kg :=
  List.mem_append_left _ (List.mem_map.2 ⟨b, hb, rfl⟩)

theorem mem_claimsF_link {pub : Lvm.Pub} {kg : KgOutF} {e : Lvm.Com × BClaim}
    (he : e ∈ ksLinkClaimsF kg.2.2.1 kg.2.2.2.1 kg.2.2.2.2) : e ∈ claimsF pub kg :=
  List.mem_append_right _ he

/-- **T5's boundary claims** give `BndS` (`bndS_of_tape` at `E2`'s tape claims). -/
theorem bndS_of_tapeF (x : List UInt8) (tp : TapeOutE2) {qm : Column CMain.nu20}
    (h : ∀ b ∈ tapeClaimsF tp (pubX x), Holds CMain.nu20 b.onStack qm) : BndS x qm := by
  intro hn m hm
  have hal2 : 2 ^ (20 + 2) ∣ 0 := dvd_zero _
  have hfit2 : 0 + 2 ^ (20 + 2) ≤ 2 ^ 23 := by norm_num
  have hN : (pubX x).n = (Lvm.ASM.hdrOf x).n := Lvm.ASM.pubX_n x
  have hH : ∀ m < 4, ((pubX x).h.getD m 0).val =
      RecursionFast.Keccak.blockLane (Lvm.ASM.hdrOf x).h.toArray m := by
    intro m hm
    show (((List.range 4).map fun i ↦ kAt (Lvm.VEq.sigOfX x) (headerAt 120 + 8 * i)).getD m 0).val = _
    rw [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range hm]
    exact Lvm.ASM.Kec.lane_hdr x (by norm_num) hm
  have hlenH : (pubX x).h.length = 4 := Lvm.ASM.length_pubX_h x
  have hmem : BClaim.point dBlkE (selE ((pubX x).n - 1) 20 ++ selE m 2)
      (Lvm.M3.kE ((pubX x).h.getD m 0)) ∈ tapeClaimsF tp (pubX x) :=
    List.mem_append_right _ (List.mem_map.2 ⟨_, Lvm.ASM.Kec.getD_mem_zipIdx _ (by omega), rfl⟩)
  have hlt : (pubX x).n - 1 < 2 ^ 20 := by rw [hN]; omega
  have H := Lvm.ASM.Kec.holds_split (h := 20) (k := 2) hal2 hfit2 (by simp [Lvm.ASM.Kec.selE_eq_bitsE])
    (b := m) (by omega) (h _ hmem)
  rw [Lvm.ASM.Kec.selE_eq_bitsE, sum_eqAt_bitsE hlt, zero_add] at H
  have H' := Lvm.KG.ofK_injective H
  rw [hN] at H'
  simp only [Lvm.NS.dD, Lvm.KG.dOf, colM, Lvm.NS.wd, Nat.mul_zero, Nat.add_zero]
  rw [H', ← hH m hm]
  rfl

/-- **The semantic link at `E2`** (`linkT₂`'s twin): the assembled claims holding on a pair give the front's
claims (`KcFr`) and the typed claims with the boundary claims on the view. -/
theorem linkF (hS : SplitSound) (x : List UInt8) (a : OpenClaims) (k : KgOutF) (p : Pair) (hk : KgRetF k)
    (h1 : ∀ c ∈ (assembleF₂ x a k).1, Holds 19 c p.2)
    (h2 : ∀ c ∈ (assembleF₂ x a k).2, Holds CMain.nu20 c p.1) :
    KcFr ksY2 (colM (vp x p).1) (colM (vp x p).1) (ksCol (vp x p).1) (msgM (vp x p).2) (msgX (vp x p).1) k ∧
      BT x a (vp x p) := by
  have h2' : ∀ c ∈ a.2 ++ (assembleSF (pubX x) k).2, Holds CMain.nu20 c (vp x p).1 := by
    intro c hc
    unfold assembleF₂ Lvm.Shape.onStackZs at h2
    unfold vp view
    by_cases hs : Lvm.Shape.small x = true
    · simp only [hs, ite_true, List.mem_map] at h2 ⊢
      exact (Lvm.Shape.holds_onStackZ c p.1).mp (h2 _ ⟨c, hc, rfl⟩)
    · simp only [hs, ite_false, Bool.false_eq_true] at h2 ⊢
      exact h2 c hc
  have h1' : ∀ c ∈ a.1 ++ (assembleSF (pubX x) k).1, Holds 19 c p.2 := h1
  have hm : ∀ b, (Lvm.Com.main, b) ∈ claimsF (pubX x) k → Holds CMain.nu20 b.onStack (vp x p).1 :=
    fun b hb ↦ h2' _ (List.mem_append_right _ (mem_assembleSF_main hb))
  have hc : ∀ b, (Lvm.Com.crec, b) ∈ claimsF (pubX x) k → Holds 19 b.onStack (vp x p).2 :=
    fun b hb ↦ h1' _ (List.mem_append_right _ (mem_assembleSF_crec hb))
  have htape : ∀ b ∈ tapeClaimsF k.1 (pubX x), Holds CMain.nu20 b.onStack (vp x p).1 := fun b hb ↦
    hm b (mem_claimsF_front (List.mem_append_left _ (List.mem_append_left _ hb)))
  have hkec : ∀ b ∈ keccakClaimsF ksBlk k.2.1, Holds CMain.nu20 b.onStack (vp x p).1 := fun b hb ↦
    hm b (mem_claimsF_front (List.mem_append_left _ (List.mem_append_right _ hb)))
  have hout : ∀ b ∈ ksOutputClaimsF k.2.1.1 k.2.1.2.1, Holds CMain.nu20 b.onStack (vp x p).1 :=
    fun b hb ↦ hm b (mem_claimsF_front (List.mem_append_right _ hb))
  have hlink : ∀ e ∈ ksLinkClaimsF k.2.2.1 k.2.2.2.1 k.2.2.2.2, e ∈ claimsF (pubX x) k :=
    fun e he ↦ mem_claimsF_link he
  rw [ksLinkClaimsF_eq] at hlink
  obtain ⟨⟨hr, -, -⟩, ⟨hrk, -, hck, -, -⟩, hkc, hks⟩ := hk
  refine ⟨⟨⟨rowTape_of k.1 (htape _ (List.mem_append_left _ (List.mem_append_right _
      (List.mem_singleton_self _)))),
    tiedDF_of hS k.1 hr fun l hl b hb ↦ htape b (List.mem_append_left _ (List.mem_append_left _
      (List.mem_flatMap.2 ⟨l, List.mem_range.2 hl, hb⟩)))⟩,
    callerClaimsE2_of hS k.2.1 hrk hck (hkec _ (List.mem_append_right _ (List.mem_singleton_self _)))
      (fun c hc' b hb ↦ hkec b (List.mem_append_left _ (List.mem_flatMap.2 ⟨c, hc', hb⟩)))
      (fun l hl b hb ↦ hout b (List.mem_flatMap.2 ⟨l, List.mem_range.2 hl, hb⟩)),
    ksClaimsE2_of hS _ _ _ hkc hks
      (fun b hb ↦ hm b (hlink _ (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _
        (List.mem_map.2 ⟨b, hb, rfl⟩))))))
      (fun b hb ↦ hm b (hlink _ (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_right _
        (List.mem_map.2 ⟨b, hb, rfl⟩))))))
      (fun b hb ↦ hc b (hlink _ (List.mem_append_left _ (List.mem_append_right _
        (List.mem_map.2 ⟨b, hb, rfl⟩)))))
      (fun b hb ↦ hm b (hlink _ (List.mem_append_right _ (List.mem_map.2 ⟨b, hb, rfl⟩))))⟩,
    ⟨fun c hc' ↦ h1' c (List.mem_append_left _ hc'), fun c hc' ↦ h2' c (List.mem_append_left _ hc')⟩,
    bndS_of_tapeF x k.1 htape⟩

/-- A claim's multiaffinity on its commitment. -/
def OkE (e : Lvm.Com × BClaim) : Prop :=
  (e.1 = .main → IsMultiaffine CMain.nu20 e.2.onStack.1) ∧ (e.1 = .crec → IsMultiaffine 19 e.2.onStack.1)

theorem okE_main {b : BClaim} (h : IsMultiaffine CMain.nu20 b.onStack.1) : OkE (.main, b) :=
  ⟨fun _ ↦ h, fun h' ↦ by cases h'⟩

theorem okE_crec {b : BClaim} (h : IsMultiaffine 19 b.onStack.1) : OkE (.crec, b) :=
  ⟨fun h' ↦ (by cases h'), fun _ ↦ h⟩

/-- **Every front claim is multiaffine on its commitment.** -/
theorem okE_claimsF (hA : SplitAffine) (pub : Lvm.Pub) (k : KgOutF) (hk : KgRetF k) :
    ∀ e ∈ claimsF pub k, OkE e := by
  obtain ⟨⟨hr, -, haff⟩, ⟨hrk, -, hck, -, haffk⟩, hkc, hks⟩ := hk
  intro e he
  rcases List.mem_append.1 he with h | h
  · obtain ⟨b, hb, rfl⟩ := List.mem_map.1 h
    refine okE_main ?_
    rcases List.mem_append.1 hb with hb | hb
    · rcases List.mem_append.1 hb with hb | hb
      · -- the tape's claims
        rcases List.mem_append.1 hb with hb | hb
        · rcases List.mem_append.1 hb with hb | hb
          · obtain ⟨l, hl, hb⟩ := List.mem_flatMap.1 hb
            have hl' := List.mem_range.1 hl
            exact hA _ _ (fitsE2_point _ (by simp [hr, dBlkE, selPtF]) (by decide) (by simp [dBlkE])
              (by decide)) b hb
          · rw [List.mem_singleton] at hb
            subst hb
            exact Lvm.ASM.isMultiaffine_onStack _ le_rfl haff
        · obtain ⟨⟨w, l⟩, -, rfl⟩ := List.mem_map.1 hb
          exact Lvm.ASM.isMultiaffine_onStack _ (by show 20 + 2 ≤ CMain.nu20; norm_num)
            (Lvm.ASM.isMultiaffine_eqEvalN _ _)
      · -- `KS`'s claims
        rcases List.mem_append.1 hb with hb | hb
        · obtain ⟨c, hc, hb⟩ := List.mem_flatMap.1 hb
          exact hA _ _ (fitsE2_point _ (by simp [ksBlk, slotLog, (hck c hc).2]) (by decide)
            (by show 2 ^ (13 + 6) ∣ CMain.ksOff20; exact ⟨10, by norm_num⟩) (by decide)) b hb
        · rw [List.mem_singleton] at hb
          subst hb
          exact Lvm.ASM.isMultiaffine_onStack _ (by show 13 + slotLog ≤ CMain.nu20; norm_num [slotLog])
            haffk
    · -- the output lanes
      obtain ⟨l, hl, hb⟩ := List.mem_flatMap.1 hb
      have hl' := List.mem_range.1 hl
      by_cases h14 : l < 14
      · have eP : ksYPartF l k.2.1.1 = (ksBlk, k.2.1.1 ++ selPtF (50 + l) slotLog) := if_pos h14
        simp only [eP] at hb
        exact hA _ _ (fitsE2_point _ (by simp [ksBlk, slotLog, hrk, selPtF]) (by decide)
          (by show 2 ^ (13 + 6) ∣ CMain.ksOff20; exact ⟨10, by norm_num⟩) (by decide)) b hb
      · have eP : ksYPartF l k.2.1.1 = (⟨13, ksY2Off + (l - 14) * 2 ^ 13⟩, k.2.1.1) := if_neg h14
        simp only [eP] at hb
        exact hA _ _ (fitsE2_point _ hrk (by show 13 ≤ CMain.nu20; norm_num)
          (Nat.dvd_add ⟨739, by norm_num [ksY2Off]⟩ (Nat.dvd_mul_left _ _))
          (by show ksY2Off + (l - 14) * 2 ^ 13 + 2 ^ 13 ≤ 2 ^ CMain.nu20
              simp only [ksY2Off]; norm_num; omega)) b hb
  · rw [ksLinkClaimsF_eq] at h
    rcases List.mem_append.1 h with h | h
    · rcases List.mem_append.1 h with h | h
      · rcases List.mem_append.1 h with h | h
        · obtain ⟨b, hb, rfl⟩ := List.mem_map.1 h
          exact okE_main (hA _ _ (fits_ksYCF _ hks) b hb)
        · obtain ⟨b, hb, rfl⟩ := List.mem_map.1 h
          exact okE_main (hA _ _ (fits_ksInCF _ hks) b hb)
      · obtain ⟨b, hb, rfl⟩ := List.mem_map.1 h
        exact okE_crec (hA _ _ (fits_ksMCF _ hks) b hb)
    · obtain ⟨b, hb, rfl⟩ := List.mem_map.1 h
      exact okE_main (hA _ _ (fits_ksXCF _ hks) b hb)

theorem length_flatMap_split {α : Type} (nu : ℕ) (f : α → SumE2) :
    ∀ l : List α, (l.flatMap fun a ↦ splitE2 nu (f a)).length = 2 * l.length
  | [] => rfl
  | a :: l => by
    rw [List.flatMap_cons, List.length_append, length_flatMap_split nu f l]
    simp [splitE2]
    ring

/-- The front leaves at most `100` claims. -/
theorem length_claimsF (x : List UInt8) (k : KgOutF) (hk : KgRetF k) : (claimsF (pubX x) k).length ≤ 100 := by
  have h1 : (k.2.1.2.2.1.1).length ≤ 1 := hk.2.1.2.2.2.1
  have hh : (pubX x).h.length = 4 := Lvm.ASM.length_pubX_h x
  have e1 : (tapeClaimsF k.1 (pubX x)).length = 2 * 4 + 1 + 4 := by
    simp only [tapeClaimsF, List.length_append, List.length_singleton, List.length_map,
      List.length_zipIdx, hh]
    rw [length_flatMap_split nuMainE (fun l ↦ pointE2 dBlkE (k.1.1 ++ selPtF l 2) (k.1.2.1.getD l 0)),
      List.length_range]
  have e2 : (keccakClaimsF ksBlk k.2.1).length = 2 * (k.2.1.2.2.1.1).length + 1 := by
    simp only [keccakClaimsF, List.length_append, List.length_singleton]
    rw [length_flatMap_split nuMainE (fun c : ColClaimE2 ↦ pointE2 ksBlk c.point c.value)]
  have e3 : (ksOutputClaimsF k.2.1.1 k.2.1.2.1).length = 2 * 25 := by
    unfold ksOutputClaimsF
    rw [length_flatMap_split nuMainE (fun l ↦ pointE2 (ksYPartF l k.2.1.1).1 (ksYPartF l k.2.1.1).2
      (k.2.1.2.1.getD l 0)), List.length_range]
  have e4 : (ksLinkClaimsF k.2.2.1 k.2.2.2.1 k.2.2.2.2).length = 8 := by
    rw [ksLinkClaimsF_eq]; simp [splitE2]
  simp only [claimsF, List.length_append, List.length_map, e1, e2, e3, e4]
  omega

/-- **The side conditions at `E2`** (`sideT₂`'s twin). -/
theorem sideF (hA : SplitAffine) (x : List UInt8) (a : OpenClaims) (k : KgOutF) (ha : TRet a)
    (hk : KgRetF k) :
    (∀ c ∈ (assembleF₂ x a k).1, IsMultiaffine 19 c.1) ∧
    (∀ c ∈ (assembleF₂ x a k).2, IsMultiaffine CMain.nu20 c.1) ∧
    (assembleF₂ x a k).1.length ≤ 2 ^ 55 ∧ (assembleF₂ x a k).2.length ≤ 2 ^ 40 := by
  have hok := okE_claimsF hA (pubX x) k hk
  have hlen := length_claimsF x k hk
  obtain ⟨a1, a2, a3, a4⟩ := ha
  have s1 : ∀ c ∈ (assembleSF (pubX x) k).1, IsMultiaffine 19 c.1 := by
    rw [assembleSF_eq]
    intro c hc
    obtain ⟨e, he, rfl⟩ := List.mem_map.1 hc
    obtain ⟨he, hcom⟩ := List.mem_filter.1 he
    exact (hok e he).2 (by simpa using hcom)
  have s2 : ∀ c ∈ (assembleSF (pubX x) k).2, IsMultiaffine CMain.nu20 c.1 := by
    rw [assembleSF_eq]
    intro c hc
    obtain ⟨e, he, rfl⟩ := List.mem_map.1 hc
    obtain ⟨he, hcom⟩ := List.mem_filter.1 he
    exact (hok e he).1 (by simpa using hcom)
  have l1 : (assembleSF (pubX x) k).1.length ≤ 100 := by
    rw [assembleSF_eq, List.length_map]; exact (List.length_filter_le _ _).trans hlen
  have l2 : (assembleSF (pubX x) k).2.length ≤ 100 := by
    rw [assembleSF_eq, List.length_map]; exact (List.length_filter_le _ _).trans hlen
  have hm : ∀ c ∈ a.2 ++ (assembleSF (pubX x) k).2, IsMultiaffine CMain.nu20 c.1 := fun c hc ↦ by
    rcases List.mem_append.mp hc with hc | hc
    · exact a2 c hc
    · exact s2 c hc
  refine ⟨fun c hc ↦ ?_, fun c hc ↦ ?_, ?_, ?_⟩
  · rcases List.mem_append.mp hc with hc | hc
    · exact a1 c hc
    · exact s1 c hc
  · unfold assembleF₂ Lvm.Shape.onStackZs at hc
    split_ifs at hc
    · obtain ⟨c', hc', rfl⟩ := List.mem_map.mp hc
      exact Lvm.Shape.isMultiaffine_onStackZ (hm c' hc')
    · exact hm c hc
  · simp only [assembleF₂, List.length_append]
    omega
  · simp only [assembleF₂, Lvm.Shape.onStackZs]
    split_ifs <;> simp only [List.length_map, List.length_append] <;> omega

end Assembled

/-! ## The pinned pair form -/

section Core

open LeanVM.Protocol.EndToEnd.Front
open Lvm.ASM (Pair LkSJ εS MidSpecP midSpecOfRelG)
open Lvm.Typed (TInst THypX GbTX BT TRet typedProgX)
open Lvm.VEq (hdX pubX)
open Lvm.E2F (candRelZ)
open Lvm.NS (colM ksCol ksY2 msgM msgX)
open Lvm.Shape (vp)
open scoped ENNReal

/-- **The pinned pair form of S2GF's middle phases** (`midSpecP_T₂`'s twin through `midSpecOfRelG`), given the
split's soundness and multiaffinity (`splitE2_sound`, `isMultiaffine_splitE2`) and a `KS` half `Gk` of the good pair
implied by the tape's and `KS`'s relations on `contRowsF`. -/
theorem midSpecP_F₂_core (hS : SplitSound) (hA : SplitAffine) {Ti : TInst} (H : THypX Ti)
    (recOf : List UInt8 → Column CMain.nu20 → Column 19) (za : List E × E)
    (Gk : List UInt8 → Pair → Prop)
    (hGk : ∀ x p, Lvm.NS.TapeG x p.1 →
      Lvm.KG.KSRel 13 9 ksY2 contRowsF (colM p.1) (ksCol p.1) (msgM p.2) (msgX p.1) → Gk x p) :
    MidSpecP (midF₂ Ti) (candRelZ recOf za) (Lvm.E2F.PinPost za)
      (fun x qm qr ↦ GbTX Ti H x (vp x (qm, qr)) ∧ Gk x (vp x (qm, qr))) εS (6 * (2 : ℝ≥0∞)⁻¹ ^ 131) :=
  midSpecOfRelG (busP := fun x ↦ typedProgX Ti (Lvm.VEq.pubXF x)) (kgP := fun x ↦ kgProgF (hdX x).s (pubX x).n)
    (asm := fun x a k ↦ assembleF₂ x a k) (Lb := 6 * (2 : ℝ≥0∞)⁻¹ ^ 131) (Lk := LkSJ)
    (Gb := fun x p ↦ GbTX Ti H x (vp x p)) (Gk := fun x p ↦ Gk x (vp x p))
    (B := fun x a p ↦ BT x a (vp x p))
    (Kc := fun x k p ↦ KcFr ksY2 (colM (vp x p).1) (colM (vp x p).1) (ksCol (vp x p).1) (msgM (vp x p).2)
      (msgX (vp x p).1) k)
    (Qa := fun _ ↦ TRet) (Qk := fun _ ↦ KgRetF) (C := candRelZ recOf za) (Sh := Lvm.E2F.PinPost za)
    (fun _ _ hl hr ↦ pinPost_append za hl hr)
    (fun x ↦ specBusTF H recOf za x (Gk x) fun p ↦ ¬ (GbTX Ti H x p ∧ Gk x p))
    (fun _ ↦ retOK_typedProgX H _)
    (fun x a T hT ↦ (kgSpecF (candRelZ_stable recOf za x) (candRelZ_ncard_le recOf za x) (hdX x).s (pubX x).n
        ksY2 (fun p ↦ colM (vp x p).1) (fun p ↦ colM (vp x p).1) (fun p ↦ ksCol (vp x p).1)
        (fun p ↦ msgM (vp x p).2) (fun p ↦ msgX (vp x p).1)
        (fun p ↦ BT x a (vp x p) ∧ ¬ (GbTX Ti H x (vp x p) ∧ Gk x (vp x p))) hT).mono
      (fun _ hd ↦ Doomed.mono hd fun p ⟨ht, hks, hb, hn⟩ ↦
        ⟨⟨hGk x (vp x p) (by rw [Lvm.ASM.pubX_n x] at ht; exact ht) hks, hn⟩, hb, hn⟩)
      (fun _ _ hp ↦ hp.2.2) le_rfl zero_le le_rfl)
    (fun _ ↦ retOK_kgProgF _ _) (fun _ ↦ cg_kgProgF _ _)
    (fun x a k p _ hk h1 h2 ↦ linkF hS x a k p hk h1 h2)
    (fun x a k ha hk ↦ sideF hA x a k ha hk)

end Core

end Lvm.E2V
