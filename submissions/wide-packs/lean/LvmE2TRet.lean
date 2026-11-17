-- New for lvm2 E2-FT (stage S2GT, E2F-T; helper T-H2): the shape facts of S2GT's typed phases and middle phases
-- (no commitment, no `grind` node; the returned claims multiaffine and few), the twins of roll 11's `cg_typedProg`,
-- `retOK_typedProg`, `retOK_midT₂_len` (`LvmTypedSpec`, `LvmMPMidT`). Lemmas only: `LvmE2TSpec` states the four
-- facts on its own objects (`TRetT`, `THypT`, `midGT`) and closes them with these.
import LvmE2TProg
import LvmE2VMidSpec
import LvmTypedSpec
import LvmCertSMid3
import LvmM3MidCert

/-!
# S2GT's typed phases: no commitment, no proof-of-work node, the return facts

* **`NoCG`** of the typed phases at `E2` (on E2F-V's `cg_e2Read`, `cg_sumcheckE2`, … in `LvmE2VMidSpecF`): every
  `E2` proof of work is a `require` on a sampled answer, not a `grind` node; **`noCG_typedProgT`**,
  **`noCG_kgFrontT`** (`kgProgFR` on any continuation rows).
* **`retOK_typedProgT_of`**: the typed claims are multiaffine on their commitments (the relayout's split point
  claim, the split region claims, the mini-bus's) and at most `8 + 2^38` in all.
* **`retOK_kgProgFR`** (`retOK_kgProgF` on any rows), **`retOK_kgFrontT`**: the `KS` caller's committed outputs
  are at most one claim; **`retOK_midT_len_of`**: the
  middle phases (typed phases, the front, `assembleF₂`) return fewer than `2^40` claims.
-/

set_option autoImplicit false

namespace Lvm.E2T

open Lvm.Loop Lvm.Typed Lvm.E2V LeanVM.Parameters LeanVM.Protocol LeanVM.Protocol.Compile
open LeanVM.Protocol.Compile.VerifierProgram LeanVM.Protocol.EndToEnd LeanVM.Protocol.EndToEnd.Front
open LeanVM.Protocol.Whir.Sound (IsMultiaffine)
open LeanVM.Protocol.EndToEnd.Sound (RetOK)
open Lvm.M3 (NoCG cg_ret cg_sample cg_readScalar cg_require cg_sampleChallenges)
open Lvm.ASM (OpenClaims)
open Lvm.VEq (ksBlk BClaim pubX pubXT)

/-! ## No commitment, no `grind` node -/

/-- **The `E2` front with any continuation rows** (`kgProgF`'s body) commits nothing and asks no proof of work. -/
theorem noCG_kgFrontT (rows : List ℕ) (s : RecursionFast.Digest) (n : ℕ) : NoCG (kgProgFR rows s n) :=
  NoCG.bind (cg_tapeProgE2 _ _ _ _ _) fun _ ↦ NoCG.bind (cg_callerProgE2 _) fun _ ↦
    NoCG.bind (cg_ksLinkProgE2 _ _ _) fun _ ↦ cg_ret _

theorem cg_zeroProgT : NoCG zeroProgT :=
  NoCG.bind cg_e2Sep fun _ ↦ NoCG.bind (cg_e2Samples _ _) fun _ ↦ NoCG.bind (cg_e2Sample _) fun _ ↦
    NoCG.bind (cg_sumcheckE2 _ _ _ _) fun _ ↦ NoCG.bind (cg_e2Reads _) fun _ ↦
      NoCG.bind (cg_require _) fun _ ↦ cg_ret _

theorem cg_wireProgT (Ti : TInst) (pub : Lvm.Pub) (v : List E2) : NoCG (wireProgT Ti pub v) :=
  NoCG.bind (cg_e2Sample _) fun _ ↦ NoCG.bind (cg_sumcheckE2 _ _ _ _) fun _ ↦
    NoCG.bind (cg_e2Reads _) fun _ ↦ NoCG.bind (cg_e2Reads _) fun _ ↦ NoCG.bind (cg_require _) fun _ ↦ cg_ret _

theorem cg_relayProgT (Ti : TInst) (ry : List E2) (vS : E2) : NoCG (relayProgT Ti ry vS) :=
  NoCG.bind (cg_sumcheckE2 _ _ _ _) fun _ ↦ NoCG.bind cg_e2Read fun _ ↦ NoCG.bind (cg_require _) fun _ ↦
    cg_ret _

theorem cg_accProgT (Q : Program) (lay : Lay) (ok : Bool) (yIn : E2) (a rxy vs : List E2) :
    NoCG (accProgT Q lay ok yIn a rxy vs) :=
  NoCG.bind (cg_e2Samples _ _) fun _ ↦ NoCG.bind (cg_e2Reads _) fun _ ↦ NoCG.bind (cg_e2Sample _) fun _ ↦
    NoCG.bind cg_e2Read fun _ ↦ cg_require _

theorem cg_miniBusProg (Ti : TInst) : NoCG (miniBusProg Ti) := by
  unfold miniBusProg Lvm.M3.lbusTableCheckProg
  exact NoCG.bind (NoCG.bind (Lvm.M3.cg_lvmBusProg _) fun _ ↦ Lvm.M3.cg_tablePhaseClaims _ _ _)
    fun _ ↦ NoCG.bind (cg_require _) fun _ ↦ cg_ret _

/-- **The typed phases at `E2` commit nothing and ask no proof of work.** -/
theorem noCG_typedProgT (Ti : TInst) (pub : Lvm.Pub) : NoCG (typedProgT Ti pub) := by
  unfold typedProgT
  exact NoCG.bind cg_zeroProgT fun _ ↦ NoCG.bind (cg_wireProgT _ _ _) fun _ ↦
    NoCG.bind (cg_relayProgT _ _ _) fun _ ↦ NoCG.bind (cg_accProgT _ _ _ _ _ _ _) fun _ ↦
      NoCG.bind (cg_miniBusProg _) fun _ ↦ cg_ret _

/-! ## The return facts -/

theorem retOK_sumcheckE2_len (g count : ℕ) : ∀ (modes : List (Option E2)) (claim : E2),
    RetOK (fun r : List E2 × E2 ↦ r.1.length = modes.length) (sumcheckE2 g claim count modes)
  | [], _ => RetOK.ret rfl
  | _ :: ms, _ => RetOK.bind_true fun _ ↦ RetOK.bind_true fun _ ↦
      (retOK_sumcheckE2_len g count ms _).bind fun _ h ↦ RetOK.ret (by simp [h])

theorem retOK_relayProgT_len (Ti : TInst) (ry : List E2) (vS : E2) :
    RetOK (fun r : List E2 × E2 ↦ r.1.length = relayRounds) (relayProgT Ti ry vS) :=
  (retOK_sumcheckE2_len _ _ _ _).bind fun _ h ↦ RetOK.bind_true fun _ ↦ RetOK.bind_true fun _ ↦
    RetOK.ret (by simpa using h)

/-- A split region claim's weight is multiaffine. -/
theorem isMultiaffine_regClaimT (Ti : TInst) (n : ℕ) (s : YSrc) (w : ℕ → ℕ) (r : List E2) (v : E2) :
    ∀ c ∈ regClaimT Ti s w r v, IsMultiaffine n c.1 := by
  intro c hc
  simp only [regClaimT, List.mem_map, List.mem_cons, List.not_mem_nil, or_false] at hc
  obtain ⟨h, -, rfl⟩ := hc
  refine Lvm.Shape.isMultiaffine_list_sum _ _ fun reg _ ↦ ?_
  by_cases hS : (reg.src == s) = true
  · simp only [hS, ite_true]
    exact Lvm.Shape.isMultiaffine_list_sum _ _ fun i _ ↦ (isMultiaffine_eqAt n _).const_mul _
  · simp only [hS, Bool.false_eq_true, ite_false]
    exact IsMultiaffine.zero

theorem length_regClaimT (Ti : TInst) (s : YSrc) (w : ℕ → ℕ) (r : List E2) (v : E2) :
    (regClaimT Ti s w r v).length = 2 := rfl

/-- The two commitments' filters split a list. -/
theorem length_filter_com {β : Type} : ∀ l : List (Lvm.Com × β),
    (l.filter (·.1 == .crec)).length + (l.filter (·.1 == .main)).length = l.length
  | [] => rfl
  | e :: l => by
    have ih := length_filter_com l
    obtain ⟨c, b⟩ := e
    cases c <;> simp <;> omega

/-- The mini-bus's claims on the two commitments are at most its column claims. -/
theorem length_miniClaims_two (Ti : TInst) (cl : List LeanVM.Protocol.Verifier.ColumnClaim) :
    (miniClaims Ti .crec cl).length + (miniClaims Ti .main cl).length ≤ cl.length := by
  unfold miniClaims
  rw [List.length_map, List.length_map, length_filter_com]
  exact List.length_filterMap_le _ _

/-- **Every return of the typed phases at `E2` meets `TRetT`'s body** (from `THypT`'s `layOk`, `widths`). -/
theorem retOK_typedProgT_of (Ti : TInst) (hlay : Lvm.M3.LayOk Lvm.M3.lay26 Ti.mbT)
    (hwid : (Ti.mbT.map (·.w)).sum ≤ 2 ^ 38) (pub : Lvm.Pub) :
    RetOK (fun a : OpenClaims ↦ (∀ c ∈ a.1, IsMultiaffine 19 c.1) ∧ (∀ c ∈ a.2, IsMultiaffine CMain.nu20 c.1) ∧
      a.1.length + a.2.length ≤ 2 ^ 39) (typedProgT Ti pub) := by
  unfold typedProgT
  refine RetOK.bind_true fun z ↦ RetOK.bind_true fun w ↦ (retOK_relayProgT_len _ _ _).bind fun r hr ↦
    RetOK.bind_true fun _ ↦ ?_
  refine (Lvm.ASM.retOK_lbusTableCheckProg Ti.mbT miniDepth).bind fun cl hcl ↦ RetOK.ret ?_
  have hm1 := isMultiaffine_miniClaims Ti hlay .crec cl
  have hm2 := isMultiaffine_miniClaims Ti hlay .main cl
  have hl := length_miniClaims_two Ti cl
  have hcl' : cl.length ≤ 2 ^ 38 := hcl.2.trans hwid
  have hfit : (pointE2 ⟨relayRounds, 0⟩ r.1 r.2).Fits 19 := by
    intro p hp
    simp only [pointE2, List.mem_cons, List.not_mem_nil, or_false] at hp
    subst hp
    exact ⟨hr, le_rfl, dvd_zero _, by norm_num⟩
  refine ⟨fun c hc ↦ ?_, fun c hc ↦ ?_, ?_⟩
  · simp only [typedClaimsT, List.mem_append] at hc
    rcases hc with (hc | hc) | hc
    · obtain ⟨b, hb, rfl⟩ := List.mem_map.mp hc
      exact isMultiaffine_splitE2 _ _ hfit b hb
    · exact isMultiaffine_regClaimT Ti 19 _ _ _ _ c hc
    · exact hm1 c hc
  · simp only [typedClaimsT, List.mem_append] at hc
    rcases hc with (hc | hc) | hc
    · exact isMultiaffine_regClaimT Ti _ _ _ _ _ c hc
    · exact isMultiaffine_regClaimT Ti _ _ _ _ _ c hc
    · exact hm2 c hc
  · simp only [typedClaimsT, List.length_append, List.length_map, length_regClaimT]
    have h2 : (splitE2 relayRounds (pointE2 ⟨relayRounds, 0⟩ r.1 r.2)).length = 2 := rfl
    rw [h2]
    omega

/-! ## The middle phases' claim count -/

/-- **The front's returns on any continuation rows** (`retOK_kgProgF`'s twin). -/
theorem retOK_kgProgFR (rows : List ℕ) (s : RecursionFast.Digest) (n : ℕ) : RetOK KgRetF (kgProgFR rows s n) :=
  (retOK_tapeProgE2 s n).bind fun _tp htp ↦ retOK_callerProgE2.bind fun _co hco ↦
    (retOK_ksLinkProgE2 _ _ _).bind fun _lo hlo ↦ RetOK.ret ⟨htp, hco, hlo⟩

/-- **The front's returns**: the `KS` caller's committed outputs are at most one claim. -/
theorem retOK_kgFrontT (rows : List ℕ) (s : RecursionFast.Digest) (n : ℕ) :
    RetOK (fun k : KgOutF ↦ k.2.1.2.2.1.1.length ≤ 1) (kgProgFR rows s n) :=
  (retOK_kgProgFR rows s n).mono fun _ h ↦ h.2.1.2.2.2.1

theorem length_splitE2 (nu : ℕ) (c : SumE2) : (splitE2 nu c).length = 2 := rfl

theorem length_flatMap_two {α β : Type} (l : List α) (f : α → List β) (hf : ∀ a, (f a).length = 2) :
    (l.flatMap f).length = 2 * l.length := by
  induction l with
  | nil => rfl
  | cons a l ih => rw [List.flatMap_cons, List.length_append, ih, hf, List.length_cons]; ring

/-- The front's claims on both commitments: at most `2·100`. -/
theorem length_assembleSF (pub : Lvm.Pub) (kg : KgOutF) (hk : kg.2.1.2.2.1.1.length ≤ 1)
    (hh : pub.h.length = 4) :
    (assembleSF pub kg).1.length + (assembleSF pub kg).2.length ≤ 2 * 100 := by
  have hc : (tapeClaimsF kg.1 pub ++ keccakClaimsF ksBlk kg.2.1 ++ ksOutputClaimsF kg.2.1.1 kg.2.1.2.1).length +
      (ksLinkClaimsF kg.2.2.1 kg.2.2.2.1 kg.2.2.2.2).length ≤ 100 := by
    simp only [tapeClaimsF, keccakClaimsF, ksOutputClaimsF, ksLinkClaimsF, List.length_append, List.length_map,
      List.length_zipIdx, List.length_cons, List.length_nil, hh]
    rw [length_flatMap_two _ _ fun _ ↦ length_splitE2 _ _, length_flatMap_two _ _ fun _ ↦ length_splitE2 _ _,
      length_flatMap_two _ _ fun _ ↦ length_splitE2 _ _]
    simp only [List.length_range, length_splitE2]
    omega
  unfold assembleSF
  simp only [List.length_map]
  have h1 := List.length_filter_le (fun e : Lvm.Com × BClaim ↦ e.1 == Lvm.Com.crec)
    ((tapeClaimsF kg.1 pub ++ keccakClaimsF ksBlk kg.2.1 ++ ksOutputClaimsF kg.2.1.1 kg.2.1.2.1).map (.main, ·) ++
      ksLinkClaimsF kg.2.2.1 kg.2.2.2.1 kg.2.2.2.2)
  have h2 := List.length_filter_le (fun e : Lvm.Com × BClaim ↦ e.1 == Lvm.Com.main)
    ((tapeClaimsF kg.1 pub ++ keccakClaimsF ksBlk kg.2.1 ++ ksOutputClaimsF kg.2.1.1 kg.2.1.2.1).map (.main, ·) ++
      ksLinkClaimsF kg.2.2.1 kg.2.2.2.1 kg.2.2.2.2)
  rw [List.length_append, List.length_map] at h1 h2
  omega

/-- **The middle phases return fewer than `2^40` claims** (any front `kg` whose `KS` outputs are at most one
claim). -/
theorem retOK_midT_len_of (Ti : TInst) (hlay : Lvm.M3.LayOk Lvm.M3.lay26 Ti.mbT)
    (hwid : (Ti.mbT.map (·.w)).sum ≤ 2 ^ 38) (x : List UInt8) (kg : VerifierProgram KgOutF)
    (hkg : RetOK (fun k : KgOutF ↦ k.2.1.2.2.1.1.length ≤ 1) kg) :
    RetOK (fun cl : OpenClaims ↦ cl.2.length + cl.1.length < 2 ^ 40)
      (typedProgT Ti (pubXT x) >>= fun a ↦ kg >>= fun k ↦ pure (assembleF₂ x a k)) :=
  (retOK_typedProgT_of Ti hlay hwid (pubXT x)).bind fun a ha ↦ hkg.bind fun k hk ↦ RetOK.ret (by
    have hs := length_assembleSF (pubX x) k hk (Lvm.ASM.length_pubX_h x)
    have hz : (Lvm.Shape.onStackZs x (a.2 ++ (assembleSF (pubX x) k).2)).length =
        a.2.length + (assembleSF (pubX x) k).2.length := by
      unfold Lvm.Shape.onStackZs
      split_ifs <;> simp only [List.length_map, List.length_append]
    simp only [assembleF₂, List.length_append]
    rw [hz]
    have := ha.2.2
    omega)

end Lvm.E2T
