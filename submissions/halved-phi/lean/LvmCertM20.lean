-- New for lvm2 roll 11 (M′, R11-LEAD, INT): the certificate of the M′ submission at `P20`. The open obligations
-- `OpenSM` on the typed instance: `midM reloc20 (midT₂ Ti20)` (R11-I's bridge), `NodeSoundM` by transfer from B1's
-- pair-form `nodeT20` (parametric: B1's L-D stub), the relocation `relocB20` onto `C_main`'s stream block `S`, the
-- window fact, the refinement (`LvmMPVEq.refinesM20L`, R11-IR) and the executable extractor's agreement
-- (`LvmMPXExtEq.ext_eqM_gen`, R11-X).
import LvmMPMidT
import LvmMPVEq
import LvmMPXExtEq
import LvmFinGuard
import LvmCertSExq2
import LvmVerifierST
import LvmCertTInst
import LvmNodeSoundTRd
import LvmSchedLit
import LvmNodeSoundTBV
import LvmTypedVEqTop
import LvmMPSig
import LvmMPCert
import LvmMPMid

-- ===== merged from `LvmCertT` (GOLF module merge: `LvmCertT.lean` is now a stub importing `LvmCertM20`) =====
section
-- New for lvm2 (roll 8 = B1, wave L, L-W): the typed certificate's generic glue. `LvmFinGuard`'s and
-- `LvmSubmissionS`'s certificate of a guarded submission, for any `V_S` with a query bound (roll 7's were at
-- `VSt tabs`, the bus path's `V_S`), and O1 for the typed `V_S` (`VST`, the same driver as `VS`).

/-!
# The certificate of a guarded submission, for any `V_S`

* **`queries_VST_le`**, **`hq_VST20`**: O1 for `VST p N` (the driver over the schedule, as `queries_VS_le`): at
  most `2 + qcItems p (schedule p) 0` queries on every oracle path, `≤ qVlvm` at `P20`.
* **`EX_Wv`**: O4 for `EX (accV VS)`, any `VS`.
* **`certificateR_openV`**: the certificate of `subWith VS (EX (accV VS)) extX` from O1 and `OpenS`.
* **`certificateR_guardV`**: the certificate of `subG b VS` from O1 and `OpenS` under `b = true`.
-/

set_option autoImplicit false

namespace Lvm.CT

open RecursionFast Lvm Lvm.T Lvm.ASM Lvm.FS
open RecursionFast.WitnessSending (encode decode encodeF)
open LeanVM.Protocol.Compile hiding Proof Bytes
open scoped NNReal ENNReal

/-! ## O1 for the typed `V_S` -/

/-- **The query bound of the typed `V_S`** on every oracle path (`queries_VS_le`'s proof: the decision is a
`.ret`). -/
theorem queries_VST_le (p : Params) (N : TypedV.TNat) (vk c : Digest) (π : RecursionFast.Proof)
    (H : ByteArray → Digest) :
    ((VST p N vk c π).queries H).length ≤ 2 + qcItems p (schedule p) 0 := by
  unfold VST
  split
  · simp only [drive, OProg.queries, List.length_cons]
    refine (Nat.add_le_add_right (Nat.add_le_add_right (q_driveItems H π p _ 0 (fun s ↦ by
      simp [OProg.queries]) (schedule p) 0 _ (by simp)) 1) 1).trans ?_
    omega
  · simp [OProg.queries]

/-- **O1** for the typed `V_S` at `P20`, any instance. -/
theorem hq_VST20 (N : TypedV.TNat) (H : ByteArray → Digest) (vk c : Digest) (π : RecursionFast.Proof) :
    ((VST P20 N vk c π).queries H).length ≤ qVlvm :=
  (queries_VST_le P20 N vk c π H).trans qcItems_P20

/-! ## The certificate for any `V_S` -/

/-- O4 for `EX (accV VS)`: on witness-sending proofs it decodes. -/
theorem EX_Wv (VS : SProg) (c : Digest) (π : RecursionFast.Proof) (L : Log) (h : isS π = false) :
    Lvm.X.EX (accV VS) c π L = decode π := by
  refine Lvm.X.EX_W _ c π L fun h0 ↦ ?_
  have : π.data.getD 0 0 = 0x53 := by
    rw [Array.getD_eq_getD_getElem?, h0]; rfl
  simp [isS, this, sByte] at h

/-- **The certificate of `subWith VS (EX (accV VS)) extX`** from O1 and the open obligations. -/
theorem certificateR_openV (VS : SProg)
    (hq : ∀ H vk c π, ((VS vk c π).queries H).length ≤ qVlvm) (o : OpenS VS (Lvm.X.EX (accV VS))) :
    CertificateR ⟨(1 : ℝ≥0) / 340282366920938463463374607431768211456, (0 : ℝ≥0) / 1, 16384,
      fun t => 70368744177664 + 8192 * t⟩ (subWith VS (Lvm.X.EX (accV VS)) Lvm.X.extX) :=
  certificateR_claim VS _ Lvm.X.extX
    ⟨fun H vk c π _ ↦ hq H vk c π, Lvm.X.computesX _, Lvm.X.extX_caps.2, EX_Wv VS, sSound_of_openS o⟩

/-- The guarded submission with the guard on is the plain one. -/
theorem subG_true (VS : SProg) : Lvm.Fin.subG true VS = subWith VS (Lvm.X.EX (accV VS)) Lvm.X.extX := rfl

/-- **The certificate of the guarded submission `subG b VS`** from O1 and the open obligations under
`b = true` (`certificateR_guardT`'s, any `V_S`). -/
theorem certificateR_guardV (VS : SProg) (hq : ∀ H vk c π, ((VS vk c π).queries H).length ≤ qVlvm) {b : Bool}
    (h : b = true → OpenS VS (Lvm.X.EX (accV VS))) :
    CertificateR ⟨(1 : ℝ≥0) / 340282366920938463463374607431768211456, (0 : ℝ≥0) / 1, 16384,
      fun t => 70368744177664 + 8192 * t⟩ (Lvm.Fin.subG b VS) := by
  cases b with
  | false => exact Lvm.Fin.certificateR_reject _
  | true => rw [subG_true]; exact certificateR_openV VS hq (h rfl)

-- (R11-IS, M′: `ext_eqV`, O5c through B1's `ext_eq_gen`, is removed; M′'s O5c is `LvmCertM20.ext_eqM20`.)

end Lvm.CT
end
-- ===== end of `LvmCertT` =====

-- ===== merged from `LvmCertTHyp` (GOLF module merge: `LvmCertTHyp.lean` is now a stub importing `LvmCertM20`) =====
section
-- New for lvm2 (roll 8 = B1, wave L, L-W): `THyp` of the typed instance at `P20` (`LvmCertT20.thyp20`): the
-- region maps' fit (`NT20.okB`), `acc_in`'s 43 coordinates, the word `1`'s region (the guard's `oneOkB`), the
-- mini-bus's table facts (by the shape of `mbT`, and `fitsMiniB` from the guard) and the error terms at the mini-bus
-- instance (B-DES §1.7; M′ `S2GM`: `μBus = 12`, no constraints, `L₀ = 37,696`). No kernel decision on `QB20`/`layT20`/`mbT20`.

/-!
# `THyp` at `P20`, glue

* **`mapsFit_inst`**: `(N.inst Q lay).MapsFit ⟨23, 19⟩` from `N.layOk lay` and `N.okB 23 19` (any instance; M′:
  `σ′`'s word is `off` modulo `2^19`, `TNat.inst`).
* **`src_one_of`**: `(N.inst Q lay).src? lay.one = some .one` from the guard's `oneOkB lay`.
* **`accLen`**: every statement's `acc_in` has `phiVars = 43` coordinates (`accVars = 43`).
* **The mini-bus's tables** `mbT C wk fin cnt` (any placement): `tabsOkB` (`AllSc`, widths, `KeysOk`), `FixOk`, a
  `C_main` column per table, no constraints; with `fitsMiniB`: heights `≤ 22`, `LayOk`, `μBus = busDepth`, the widths'
  sum `= tableEvals`.
* **`errs_at`**: `TErrs 37696 I εS LkSJ` for any instance with `μBus = 12` and `B = 0` (M′ `S2GM`; B1: 13).
-/

set_option autoImplicit false

namespace Lvm.CT

open Lvm Lvm.Typed Lvm.QTyped Lvm.TypedV Lvm.M3 Lvm.QAsm
open Lvm.VEq (pubX)
open scoped ENNReal NNReal

/-- `P20`'s record: `ν = (23, 19)`, the mini-bus's depth and evaluations. -/
theorem p20_facts : P20.nuMain = 23 ∧ P20.nuRec = 19 ∧ P20.busDepth = 12 ∧ P20.tableEvals = 633 := by
  decide +kernel

/-! ## The word space -/

/-- The region maps of `N.inst Q lay` land in a `ν = (23, 19)` commitment pair when `N` passes its shape check. -/
theorem mapsFit_inst (N : TNat) (Q : Lvm.Loop.Program) (lay : Typed.Lay) (hl : N.layOk lay = true)
    (hok : N.okB 23 19 = true) : (N.inst Q lay).MapsFit lay26 := by
  intro y
  rw [src?_inst N Q lay hl y]
  cases hr : N.regAt y with
  | none => trivial
  | some r =>
    have hmem : r ∈ N.regs := List.mem_of_find?_eq_some hr
    have hp := List.find?_some hr
    simp only [decide_eq_true_eq] at hp
    have hoff : N.off y = r.dst + (y - r.base) := by simp [TNat.off, hr]
    unfold TNat.okB at hok
    simp only [Bool.and_eq_true, List.all_eq_true] at hok
    have hr' := hok.1.1.1.1.1 r hmem
    simp only [beq_iff_eq, decide_eq_true_eq] at hr'
    obtain ⟨-, hsrc⟩ := hr'
    simp only [Option.map_some]
    cases hs : r.src <;> simp only [hs] at hsrc <;>
      simp only [TNat.inst, hoff, beq_iff_eq, decide_eq_true_eq, Bool.and_eq_true, posBits] at hsrc ⊢
    all_goals first
      | trivial
      | exact Nat.mod_lt _ (Nat.two_pow_pos 19)
      | (simp only [lay26]; omega)
      | omega
      | (have h1 : r.dst + (y - r.base) < 2 ^ 19 := by (clear * - hp hsrc; omega)
         unfold sflatWord
         split <;> simp only [sPos, sLanes, recRowBits, recStreamCols] at * <;> omega)

/-- `acc_in` has `phiVars = 43` coordinates on every statement (`pubOf` reads `accVars = 43`). -/
theorem accLen : ∀ x, (pubX x).accIn.pt.length = phiVars := by
  intro x
  simp only [pubX, pubOf, List.length_map, List.length_range]
  rfl

/-- **The word `1` lies in a `1` region** when the guard's `oneOkB` holds. -/
theorem src_one_of (N : TNat) (Q : Lvm.Loop.Program) (lay : Typed.Lay) (h : Lvm.T.oneOkB lay = true) :
    (N.inst Q lay).src? lay.one = some .one := by
  simpa [Lvm.T.oneOkB, TInst.src?, TNat.inst] using h

/-! ## The mini-bus's tables -/

/-- The mini-bus's tables pass `tabsOkB` (every table reads or seeds, widths, key sizes), by their shape. -/
theorem tabsOkB_mbT (C : QCfg) (wk : ℕ → ℕ) (fin : ℕ → Bool × ℕ) (cnt : ℕ → ℕ) :
    tabsOkB (mbT C wk fin cnt) = true := by
  simp [tabsOkB, mbT, mbArrs, capReads, readTab, InArr.tab, InArr.vcols, readKey, List.all_append,
    List.all_map, Tab.w]

/-- A seed array's fixed column is its address column's closed form (`inArr_eval_eq`). -/
theorem fixOk_arrT {C : QCfg} {fin : ℕ → Bool × ℕ} (a : InArr) (ha : a ∈ mbArrs C fin) {f : ℕ → FK}
    {ev : List FE → FE} (hfe : ColSrc.fix f ev ∈ a.tab.cols) (r : List FE) (hr : r.length = a.tab.τ) :
    ev r = Loop.mle r fun x ↦ FE.ofK (f x) := by
  have hpub : a.pub = none := by
    unfold mbArrs at ha
    obtain ⟨_, -, rfl⟩ := List.mem_map.mp ha; rfl
  simp only [InArr.tab, List.mem_append, List.mem_cons, List.mem_nil_iff, or_false] at hfe
  rcases hfe with hv | hv | hv
  · unfold InArr.vcols at hv
    rw [hpub] at hv
    obtain ⟨_, -, hv⟩ := List.mem_map.mp hv
    cases hv
  · cases hv
  · simp only [ColSrc.fix.injEq] at hv
    obtain ⟨rfl, rfl⟩ := hv
    exact inArr_eval_eq a r

/-- **`FixOk`** of the mini-bus's tables: the seed arrays' address columns; the read tables have none. -/
theorem fixOk_mbT (C : QCfg) (wk : ℕ → ℕ) (fin : ℕ → Bool × ℕ) (cnt : ℕ → ℕ) :
    FixOk (mbT C wk fin cnt) := by
  intro t ht f ev hfe r hr
  unfold mbT at ht
  rcases List.mem_append.mp ht with ht | ht
  · obtain ⟨a, ha, rfl⟩ := List.mem_map.mp ht
    exact fixOk_arrT a ha hfe r hr
  · unfold capReads at ht
    obtain ⟨x, -, rfl⟩ := List.mem_map.mp ht
    simp [readTab] at hfe

/-- Every table of `mbT` has a `C_main` column (the read tables' columns, the seed arrays' finalize column). -/
theorem com_mbT (C : QCfg) (wk : ℕ → ℕ) (fin : ℕ → Bool × ℕ) (cnt : ℕ → ℕ) (hfin : ∀ k, (fin k).1 = false) :
    ∀ t ∈ mbT C wk fin cnt, ∃ off, ColSrc.com false off ∈ t.cols := by
  intro t ht
  unfold mbT at ht
  rcases List.mem_append.mp ht with ht | ht
  · obtain ⟨a, ha, rfl⟩ := List.mem_map.mp ht
    unfold mbArrs at ha
    obtain ⟨y, -, rfl⟩ := List.mem_map.mp ha
    exact ⟨(fin y.2).2, by simp [InArr.tab, ← hfin y.2]⟩
  · unfold capReads at ht
    obtain ⟨x, -, rfl⟩ := List.mem_map.mp ht
    exact ⟨wk (adrCell (qlinkProg C) x.1.1 x.1.2 0), by simp [readTab]⟩

/-- A table with a `C_main` column off `D` (`colsHiB`) is at most `2^22` high. -/
theorem hτ_of_hi {tabs : List Tab} (hc : ∀ t ∈ tabs, ∃ off, ColSrc.com false off ∈ t.cols)
    (h : colsHiB tabs = true) : ∀ t ∈ tabs, t.τ ≤ (⟨23, 19⟩ : M3.Lay).μ := by
  intro t ht
  obtain ⟨off, hoff⟩ := hc t ht
  simp only [colsHiB, List.all_eq_true] at h
  have := h t ht _ hoff
  simp only [Bool.false_or, Bool.and_eq_true, decide_eq_true_eq] at this
  simp only [Lay.μ]; (clear * - this; omega)

/-- **`LayOk`** from `colsFitB` at `ν = (23, 19)` (`Fit.layOk`'s proof). -/
theorem layOk_of_fit {p : Params} {tabs : List Tab} (hp : p.nuMain = 23 ∧ p.nuRec = 19)
    (h : colsFitB p tabs = true) : LayOk ⟨23, 19⟩ tabs := by
  apply layOk_of_B
  simp only [colsFitB, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true] at h
  simp only [layOkB, List.all_eq_true]
  intro t ht c hc
  have := h.2 t ht c hc
  cases c with
  | com rec off =>
    simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at this
    simp only [colOkB, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq, ← hp.1, ← hp.2]
    exact ⟨⟨this.1, this.2⟩, h.1⟩
  | fix f ev => rfl

/-- Tables that all read or seed are all sumcheck tables. -/
theorem sc_all (tabs : List Tab) (h : AllSc tabs) : sumcheckTabs tabs = tabs := by
  unfold sumcheckTabs
  rw [List.filter_eq_self]
  intro t ht
  rcases h t ht with h1 | h1 <;> simp [h1]

/-- The mini-bus's tables have no constraints (so the batching count `B` is `0`). -/
theorem cons_mbT (C : QCfg) (wk : ℕ → ℕ) (fin : ℕ → Bool × ℕ) (cnt : ℕ → ℕ) :
    ((mbT C wk fin cnt).map fun t ↦ t.cons.length).sum = 0 := by
  refine List.sum_eq_zero fun n hn ↦ ?_
  obtain ⟨t, ht, rfl⟩ := List.mem_map.mp hn
  unfold mbT at ht
  rcases List.mem_append.mp ht with ht | ht
  · obtain ⟨a, -, rfl⟩ := List.mem_map.mp ht; rfl
  · unfold capReads at ht
    obtain ⟨x, -, rfl⟩ := List.mem_map.mp ht; rfl

open LeanVM.Protocol.KeccakGkr (errE errE_mono) in
open LeanVM.Protocol.EndToEnd.Front in
open Lvm.ASM in
/-- **The typed phases' error terms** (`TErrs`) at `L₀ = 37,696` against `εS` with follower `LkSJ`, for an instance
of depth `12` (M′ `S2GM`; B1: 13) without constraints: every term is `errE d` with `d ≤ 2^63` (`errE_le_εS`). -/
theorem errs_at (I : LeanVM.Protocol.M3Instance) (hμ : I.μBus = 12) (hB : I.B = 0) :
    TErrs 37696 I εS LkSJ := by
  have hab : abError I 37696 = errE (37696 * (4 * 2 ^ 12)) := by
    rw [abError, coe_overE, errE_smul, hμ]
  have hr : ∀ d, roundError 37696 d = errE (37696 * d) := fun d ↦ by
    rw [roundError, coe_div_card, errE_smul]
  have hl : lambdaError 37696 = errE (37696 * 2) := by
    rw [lambdaError, coe_div_card, errE_smul]
  have hu : unitError 37696 = errE (37696 * 1) := by
    rw [← errE_smul]; simp [unitError, errE]
  have hx : xiError I 37696 = errE (37696 * (I.B + 3 - 1)) := by
    rw [xiError, coe_div_card, errE_smul]
  have hlead : leadT 37696 = errE (20 * (37696 * 1)) := by
    simp only [leadT, add_zero, errE_smul, Lvm.Typed.xVars]
  have h2 : (2 : ℝ≥0∞) * errE 1 = errE (2 * 1) := by rw [← errE_smul]; norm_num
  have hM : leadMaxT 37696 I LkSJ ≤ errE (37696 * (4 * 2 ^ 12)) := by
    unfold leadMaxT
    rw [hlead, hab, add_zero, h2, LkSJ_eq]
    exact max_le (errE_mono (by norm_num)) (max_le le_rfl (max_le (errE_mono (by norm_num))
      (errE_mono (by norm_num))))
  have fin : ∀ a : ℕ, a ≤ 2 ^ 62 → errE a + leadMaxT 37696 I LkSJ ≤ εS := by
    intro a ha
    calc errE a + leadMaxT 37696 I LkSJ ≤ errE a + errE (37696 * (4 * 2 ^ 12)) := by gcongr
      _ = errE (a + 37696 * (4 * 2 ^ 12)) := errE_add _ _
      _ ≤ εS := errE_le_εS (Nat.le_trans (Nat.add_le_add_right ha _) (by norm_num))
  refine ⟨?_, fun d hd ↦ ?_, ?_, ⟨?_, ?_⟩, ⟨?_, ?_⟩, ?_, ?_⟩
  · rw [hlead]; exact errE_le_εS (by norm_num)
  · rw [hr]; exact fin _ (by (clear * - hd; omega))
  · exact fin _ (by norm_num [Lvm.Typed.phiVars, Lvm.Typed.xVars, Lvm.Typed.yVars])
  · rw [hab]; exact lt_of_le_of_lt (errE_le_εS (by norm_num)) εS_lt_one
  · rw [hab]; exact fin _ (by norm_num)
  · rw [interpLead_eq, hu, hl, errE_smul, errE_add]; exact fin _ (by norm_num)
  · rw [hl]; exact fin _ (by norm_num)
  · rw [hx, hB]; exact fin _ (by norm_num)
  · exact hM.trans (errE_le_εS (by norm_num))

end Lvm.CT
end
-- ===== end of `LvmCertTHyp` =====

-- ===== merged from `LvmNodeSoundT20` (GOLF module merge: `LvmNodeSoundT20.lean` is now a stub importing `LvmCertM20`) =====
section
-- New for lvm2 (roll 8 = B1, L-D): the guard-side pieces of `nodeT20` (L-W's stub `LvmCertT20.nodeT20`): of
-- `nodeSoundT`'s (`LvmNodeSoundT`) hypotheses, `ReaddOk` (`LvmNodeSoundTRd`, from the guard's `rdChkB`, the
-- mini-bus's `M3Holds` and L-B's `rowDef_of_wiring`), the input map and QLT (`LvmNodeSoundTIn`), Q_arith through the
-- typed HAR (`LvmQTypedHarS.harithT20`, L-H) and `Φ_Q` (`PhiQC_eq`, `AccOkT`). The `BITS` rows' facts (`hpos`,
-- `hbits`, `BVT`) and the assembly: `LvmNodeSoundT20B.nodeT20B`.

/-!
# `nodeT20`'s guard-side pieces

* **`hlinT`**: the non-`readd` rows hold on a good pair's memory (`rowDef_of_wiring`, L-B).
* **`readdT`**: `ReaddOk` on it (`readdOk_of_chk` with `mbRead_seeded` on `GoodT`'s mini-bus `M3Holds` and the
  stream's cells from `inMapB`).
* **`decideFT_of`**: `decideFT = decideCoreT && Φ_Q(acc_out) == y`: the HAR gives the first and `acc_out = acc_in`,
  `AccOkT` (in `GoodT`) and `PhiQC_eq` (the guard's `cache`, rewritten by `cacheT20_eq`) the second.
-/

set_option autoImplicit false

namespace Lvm.NS

open RecursionFast Lvm Lvm.T Lvm.ASM Lvm.Replay Lvm.Loop Lvm.Loop.Build Lvm.QLink Lvm.QSig Lvm.M3
open Lvm.QAsm Lvm.QTyped Lvm.Typed Lvm.TypedV LeanVM.Protocol
open Lvm.VEq (pubX)

theorem mbT_TiB : TiB.mbT = mbTOf cfg20 frz20 := rfl

theorem m3Holds_eq {L : Lvm.M3.Lay} {t t' : List Tab} (h : t = t') {hτ : ∀ u ∈ t, u.τ ≤ L.μ}
    {hτ' : ∀ u ∈ t', u.τ ≤ L.μ} {q : Column L.μ} (hm : M3Holds (inst L t hτ) () q) :
    M3Holds (inst L t' hτ') () q := by
  subst h; exact hm

/-- **The non-`readd` rows hold** on a good pair's memory (L-B's `rowDef_of_wiring`). -/
theorem hlinT (S : Lvm.CT.SF20) {H : THyp TiB} {x : List UInt8} {qm : Column CMain.nu20} {qr : Column 19}
    (hG : GoodT TiB H x qm qr) : NonReaddHolds QB20 (memT x qm qr) :=
  fun _ hi hop ↦ rowDef_of_wiring QB20 layT20 (zT x qm qr) S.wf S.hlay (zT_one H x qm qr) (goodT_wiring hG) hi hop
    (S.noE2 _ hi)

/-- `V_S`'s regions fit `ν = 23`, `ν_rec = 19` (the guard's `regs`). -/
theorem okB20 (S : Lvm.CT.SF20) : NT20.okB 23 19 = true := by
  have h := S.regs
  rwa [show Lvm.QAsm.cfg20.p = P20 from rfl, show P20.nuMain = 23 by decide +kernel,
    show P20.nuRec = 19 by decide +kernel] at h

/-- **`ReaddOk` on a pair's memory** from the node checks at any stage (lvm2 E2-FT: any configuration `C` whose
stream is `C_main`'s stream block (`hrl`, `hs0`, `hrr`), any public values `pub`; on a stream-block pair, `SBlk`; the
seeds are `C_main`'s stream-block words): the mini-bus's `M3Holds` on the pair's stack and the non-`readd` rows. -/
theorem readdTGL (C : QCfg) (F : TFrz) (Q : Program) (tl : Typed.Lay) (N : TNat) (pl : Lvm.Pub → List FK)
    (pub : Lvm.Pub) (B nPub : ℕ)
    (hlay : tl.Ok Q) (hreg : N.okB 23 19 = true) (hl : N.layOk tl = true) (hσ : SigInS N)
    (hchk : nodeChkBG B nPub C F Q tl N = true) (hrl : C.rl = 14) (hs0 : (layout0 C.p).s = CMain.sOff20)
    (hrr : C.p.recRowsLog = 14) (hnK : 17 * 2 ^ 14 ≤ nK C) (hc : nK C ≤ Q.cells .K)
    {qm : Column CMain.nu20} {qr : Column 19} (hτ : ∀ t ∈ mbTOf C F, t.τ ≤ lay26.μ)
    (hLay : LayOk lay26 (mbTOf C F)) (hM : M3Holds (inst lay26 (mbTOf C F) hτ) () (stackOf lay26 qm qr))
    (hSB : SBlk qm qr) (hlin : NonReaddHolds Q (memOf tl ((N.instL pl Q tl).zOf lay26 pub qm qr))) :
    ReaddOk Q (memOf tl ((N.instL pl Q tl).zOf lay26 pub qm qr)) := by
  simp only [nodeChkBG, Bool.and_eq_true] at hchk
  obtain ⟨⟨hin, hrd⟩, hsd⟩ := hchk
  simp only [mbSeedsOkB, Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq] at hsd
  obtain ⟨hblk, hlen⟩ := hsd
  have hS := (inMap_of_okGL B nPub C N pl Q tl hlay pub qm qr hSB hreg hl hσ hin).1
  refine readdOk_of_chkL C F Q tl N pl hlay pub qm qr hSB hreg hl hσ hrd ?_ ?_ hlin
  · intro τ wa wv hp y hy
    obtain ⟨k, hk⟩ := List.mem_iff_getElem?.mp hp
    exact mbRead_seeded C F lay26 hτ qm qr hLay hM hlen hk hy
  · intro lq hlq x' hx'
    obtain ⟨hl17, hq⟩ := hblk lq hlq
    rw [hrl] at hq
    have hx'16 : x' < 16 := hx'
    have hj : 17 * (lq.2 + x') + lq.1 < 17 * 2 ^ 14 := by omega
    have e : (Lvm.QAsm.lay C).sb + 17 * lq.2 + lq.1 + 17 * x' =
        (Lvm.QAsm.lay C).sb + (17 * (lq.2 + x') + lq.1) := by ring
    have h16 : (2 : ℕ) ^ 14 = 16384 := by norm_num
    refine ⟨?_, ?_⟩
    · have hsb : (Lvm.QAsm.lay C).sb = 0 := rfl
      rw [e, hsb]
      (clear * - hj hnK hc; omega)
    · have h1 := hS (17 * (lq.2 + x') + lq.1) hj
      beta_reduce at h1
      have e2 : (17 * (lq.2 + x') + lq.1) % 17 * 2 ^ 14 + (17 * (lq.2 + x') + lq.1) / 17 =
          lq.1 * 2 ^ C.rl + lq.2 + x' := by
        rw [hrl, h16]; omega
      have hs : Lvm.sCol C.p lq.1 + lq.2 + x' = CMain.sOff20 + (lq.1 * 2 ^ C.rl + lq.2 + x') := by
        simp only [Lvm.sCol, hs0, hrr, hrl]
        omega
      rw [e, h1, e2, hs, comCell_S hSB (by rw [hrl, h16]; omega)]

/-- `readdTGL` at `PUB`'s 3-lane layout (`TNat.inst`). -/
theorem readdTG (C : QCfg) (F : TFrz) (Q : Program) (tl : Typed.Lay) (N : TNat) (pub : Lvm.Pub) (B nPub : ℕ)
    (hlay : tl.Ok Q) (hreg : N.okB 23 19 = true) (hl : N.layOk tl = true) (hσ : SigInS N)
    (hchk : nodeChkBG B nPub C F Q tl N = true) (hrl : C.rl = 14) (hs0 : (layout0 C.p).s = CMain.sOff20)
    (hrr : C.p.recRowsLog = 14) (hnK : 17 * 2 ^ 14 ≤ nK C) (hc : nK C ≤ Q.cells .K)
    {qm : Column CMain.nu20} {qr : Column 19} (hτ : ∀ t ∈ mbTOf C F, t.τ ≤ lay26.μ)
    (hLay : LayOk lay26 (mbTOf C F)) (hM : M3Holds (inst lay26 (mbTOf C F) hτ) () (stackOf lay26 qm qr))
    (hSB : SBlk qm qr) (hlin : NonReaddHolds Q (memOf tl ((N.inst Q tl).zOf lay26 pub qm qr))) :
    ReaddOk Q (memOf tl ((N.inst Q tl).zOf lay26 pub qm qr)) :=
  readdTGL C F Q tl N Pub.hdrLanes pub B nPub hlay hreg hl hσ hchk hrl hs0 hrr hnK hc hτ hLay hM hSB hlin

/-- **`ReaddOk` on a good pair's memory** from the guard's checks (M′ `S2GM`: on a stream-block pair, `SBlk`; the
seeds are `S`'s `C_main` words). -/
theorem readdT (S : Lvm.CT.SF20) (H : THyp TiB) (hchk : nodeChkB cfg20 frz20 QB20 layT20 NT20 = true)
    {x : List UInt8} {qm : Column CMain.nu20} {qr : Column 19} (hG : GoodT TiB H x qm qr) (hSB : SBlk qm qr) :
    ReaddOk QB20 (memT x qm qr) := by
  have hτ : ∀ t ∈ mbTOf cfg20 frz20, t.τ ≤ lay26.μ := fun t ht ↦ H.hτ t (by rw [mbT_TiB]; exact ht)
  have hlay : LayOk lay26 (mbTOf cfg20 frz20) := by have := H.layOk; rwa [mbT_TiB] at this
  rw [nodeChkB_eq] at hchk
  exact readdTG cfg20 frz20 QB20 layT20 NT20 (pubX x) _ _ S.hlay (okB20 S) S.hlayOk S.sig hchk rfl
    (by show (layout0 P20).s = _; rw [Lvm.layout0_P20]) (by decide) (by decide)
    (by rw [QB20_qn]; exact nK_le_cells _ _ _) hτ hlay (m3Holds_eq mbT_TiB hG.1.1.1.2) hSB (hlinT S hG)

/-- `Φ_Q` at the incoming accumulator is its claim (`AccOkT`), through the cache (`PhiQC_eq`, `cacheT20_eq`). -/
theorem phi_accIn (S : Lvm.CT.SF20) (H : THyp TiB) (x : List UInt8) (hacc : AccOkT TiB (pubX x)) :
    PhiQC cacheT20 (pubX x).accIn.pt = (pubX x).accIn.y := by
  have hc := S.cache
  rw [cacheT20_eq] at hc ⊢
  rw [PhiQC_eq QB20 layT20 S.hlay hc _ (H.acc x)]
  have h := hacc
  unfold AccOkT PhiQ at h
  rw [Q_TiB, lay_TiB, List.map_map] at h
  simp only [Function.comp_def, FE.ofExt3_toExt3, List.map_id'] at h
  exact FE.toExt3_injective h

theorem NT20_phi : NT20.phi = PhiQC cacheT20 := rfl

/-- **`decideFT` from the HAR and the incoming accumulator.** -/
theorem decideFT_of (S : Lvm.CT.SF20) (H : THyp TiB) {vk cL : RecursionFast.Digest} {sig : ByteArray}
    {x : List UInt8} (hacc : AccOkT TiB (pubX x)) (hc : decideCoreT P20 NT20 vk cL sig = true)
    (ha : accOutOfT P20 NT20 vk cL sig = (pubX x).accIn) : decideFT P20 NT20 vk cL sig = true := by
  rw [decideFT_eq, hc, ha, NT20_phi, phi_accIn S H x hacc]
  simp

end Lvm.NS
end
-- ===== end of `LvmNodeSoundT20` =====

-- (lvm2 E2F-G: `LvmMPNodePos`'s `posLanesKS20`/`posLanesS20` moved to `LvmCertM20R`.)

-- ===== merged from `LvmNodeSoundT20B` (GOLF module merge: `LvmNodeSoundT20B.lean` is now a stub importing `LvmCertM20`) =====
section
-- New for lvm2 (roll 8 = B1, L-D): `nodeT20` with the typed `BITS` rows' facts discharged (`LvmNodeSoundTBits`,
-- `LvmNodeSoundTBV`): Q_link's position bits, Q_sig's `SigBits`, and `BVT` for the typed HAR, with the openings'
-- position cells (`posCellsT`; roll 7's `posCells20`) and `PosOk` (`posOk_of`). lvm2 roll 11 (M′ `S2GM`, R11-N): on
-- stream-block pairs (`SBlk`), one opening (`posOkMT` from `LvmMPNodePos.posLanesS20`; B1's `posOkRT` is gone).

/-!
# `nodeT20` with the `BITS` facts

* **`childOkT`**: Q_sig's `ChildOk` on a good node pair's memory (the holds chain, `qsig_sound_in`).
* **`posCellsT`**: Q_link's position cells hold `kOf (posL …)` of the child's stream (`qlink_pos`, `posVal_on`).
* **`posOkMT`**: `BVT`'s `posm` (M′: the child's one opening, `C_main`'s, from `openU P20 + 15`).
* **`nodeT20B S H vk hchk`**: `NodeSound VSB20 vk (fun x qm qr ↦ GoodT Ti20 H x qm qr ∧ SBlk qm qr) childS`
  (`nodeT20 S H vk` is `nodeT20B S H vk S.chk`; B1: on every `GoodT` pair).
-/

set_option autoImplicit false

namespace Lvm.NS

open RecursionFast Lvm Lvm.T Lvm.ASM Lvm.Replay Lvm.Loop Lvm.Loop.Build Lvm.QLink Lvm.QSig Lvm.M3
open Lvm.QAsm Lvm.QTyped Lvm.Typed Lvm.TypedV Lvm.BitsTab Lvm.Bits Lvm.SigBits Lvm.Har LeanVM.Protocol
open Lvm.VEq (pubX)

/-- **Q_sig's `ChildOk` on a good node pair's memory.** -/
theorem childOkT (S : Lvm.CT.SF20) (H : THyp TiB) (hchk : nodeChkB cfg20 frz20 QB20 layT20 NT20 = true)
    {vk c : RecursionFast.Digest} {x : List UInt8} {qm : Column CMain.nu20} {qr : Column 19}
    (hok : okS vk c x = true) (hb : (hdrOf x).b = 1) (hG : GoodT TiB H x qm qr) (hSB : SBlk qm qr) :
    ChildOk (sigIn cfg20) (memT x qm qr).k := by
  have hin : inMapB cfg20 QB20 layT20 NT20 = true := by
    simp only [nodeChkB, Bool.and_eq_true] at hchk; exact hchk.1.1
  obtain ⟨hH, hA⟩ := holds_memT S.toStaticFactsT hG (readdT S H hchk hG hSB)
  have hinj := S.inj
  rw [QB20_qn] at hH hA hinj
  have P := parts_of_holds hH hA
  have mp := inMapT S.toStaticFactsT hin S.sig qm qr hSB hok hb
  have hks := sigKSin_of_goodK (goodK_of hok hG) mp.xs mp.ys mp.yc mp.yls mp.yns
  exact (qsig_sound_in (by rw [hln20]; omega) P.2.1 mp.flag hks (sigBitsT S H hG)
    fun a b ha hb h => FK.FKx_pow_inj (by omega) (by omega) h).2

theorem cfg20_pT : cfg20.p = P20 := rfl

/-- **Q_link's position cells hold `kOf (posL …)` of the child's stream** on a good pair's memory
(`posCells20`: Q_link's `qlink_pos` and `posVal_on`). -/
theorem posCellsT (S : Lvm.CT.SF20) (H : THyp TiB) (hchk : nodeChkB cfg20 frz20 QB20 layT20 NT20 = true)
    {vk c : RecursionFast.Digest} {x : List UInt8} {qm : Column CMain.nu20} {qr : Column 19}
    (hok : okS vk c x = true) (hb : (hdrOf x).b = 1) (hG : GoodT TiB H x qm qr) (hSB : SBlk qm qr) :
    ∀ k < (opens P20).length, ((opens P20).getD k default).L.height ≤ 64 →
      ∀ j < ((opens P20).getD k default).L.t,
      (memT x qm qr).k (nK cfg20 + posIdx P20 k j) =
        kOf (posL P20 (wsC qr) (((opens P20).getD k default).pe + j / 8)
          (j % 8 * ((opens P20).getD k default).L.height) ((opens P20).getD k default).L.height) := by
  intro k hk hH j hj
  have hin : inMapB cfg20 QB20 layT20 NT20 = true := by
    simp only [nodeChkB, Bool.and_eq_true] at hchk; exact hchk.1.1
  obtain ⟨hH', hA⟩ := holds_memT S.toStaticFactsT hG (readdT S H hchk hG hSB)
  rw [QB20_qn] at hH' hA
  have P := parts_of_holds hH' hA
  have mp := inMapT S.toStaticFactsT hin S.sig qm qr hSB hok hb
  have hk' : k < (opens cfg20.p).length := by rw [cfg20_pT]; exact hk
  have hH'' : ((opens cfg20.p).getD k default).L.height ≤ 64 := by rw [cfg20_pT]; exact hH
  have hj' : j < ((opens cfg20.p).getD k default).L.t := by rw [cfg20_pT]; exact hj
  have hv := posVal_onT (outsOn_memT S H hG) (by rw [cfg20_pT]; exact hS20) (by rw [cfg20_pT]; exact hQ20)
    mp.stream hk' hH'' hj'
  rw [cfg20_pT] at hv
  have hq := qlink_pos (pt := p0 (nK cfg20) 0) hQ20 P.1.1 hk hj
  exact hq.trans hv

end Lvm.NS
end
-- ===== end of `LvmNodeSoundT20B` =====

-- ===== merged from `LvmCertT20` (GOLF module merge: `LvmCertT20.lean` is now a stub importing `LvmCertM20`) =====
section
-- New for lvm2 (roll 8 = B1, wave L, L-W): the typed certificate's pieces at `P20`: the guard's facts (`sf20`),
-- `THyp` of the typed instance `Ti20 = NT20.inst QB20 layT20`, `NodeSound` on `GoodT` (L-D). lvm2 roll 11 (M′): the
-- certificate is `LvmCertM20.certificateM20`; B1's `openT20`/`certificateT20` and `ext_eq_gen` are gone.

/-!
# The typed certificate at `P20`

* **`Ti20`**, **`SF20`** (`LvmCertTInst`): the typed instance and the guard's facts at `P20`.
* **`thyp20 S`**: `THyp Ti20` from the guard's facts `S` (the layout's word `1`, the region maps' fit, `acc_in`'s
  43 coordinates, the mini-bus's table facts, the error terms).
* (lvm2 roll 11, M′ `S2GM`: B1's `refinesT20`, `openT20`, `certificateT20` targeted the two-root `PSWith` and are
  gone; the M′ certificate is `LvmCertM20.certificateM20`. `nodeT20` is on stream-block pairs, `SBlk`: B1's
  `NodeSound` on every `GoodT` pair does not hold at M′, R11-IS.)

`nodeT20` (L-D) is restated at M′ to stream-block pairs (R11-IS) and proved there (R11-N). `THyp`'s glue is proved
(`LvmCertTHyp`); `midFollowsT20` is L-C's `LvmTypedVEqTop.midFollowsT20L`.
-/

set_option autoImplicit false

namespace Lvm.CT

open RecursionFast Lvm Lvm.T Lvm.ASM Lvm.FS Lvm.Typed Lvm.QTyped
open Lvm.M3 (Tab inst AllSc LayOk KeysOk FixOk lay26)
open Lvm.VEq (pubX)
open scoped NNReal ENNReal

/-! ## `THyp` at `P20` -/

/-- The layout's word `1` lies in the `1` region (`TInst.Ok`'s second half), from the guard's `oneOkB`. -/
theorem one20 (h : Lvm.T.oneOkB layT20 = true) : Ti20.src? layT20.one = some .one :=
  src_one_of NT20 QB20 layT20 h

/-- **The region maps land in the commitments** at `lay26` (`NT20.okB`, `NT20`'s regions are the layout's). -/
theorem maps20 (S : SF20) : Ti20.MapsFit lay26 :=
  mapsFit_inst NT20 QB20 layT20 S.hlayOk (by
    have h := S.regs
    rwa [show Lvm.QAsm.cfg20.p = P20 from rfl, p20_facts.1, p20_facts.2.1] at h)

/-- `acc_in` has `phiVars = 43` coordinates on every statement (`accVars = 43`). -/
theorem acc20 : ∀ x, (pubX x).accIn.pt.length = phiVars := accLen

/-- **The mini-bus's table facts at `P20`** (`THyp`'s `hτ` … `μBus`, as roll 7's `MidHyp` on the bus tables). -/
structure MbHyp20 : Prop where
  hτ : ∀ t ∈ mbT20, t.τ ≤ lay26.μ
  sc : AllSc mbT20
  layOk : LayOk lay26 mbT20
  keys : KeysOk mbT20
  width : ∀ t ∈ mbT20, 0 < t.w
  fix : FixOk mbT20
  widths : (mbT20.map (·.w)).sum ≤ 2 ^ 38
  μBus : ∀ (h : ∀ t ∈ mbT20, t.τ ≤ lay26.μ), (inst lay26 mbT20 h).μBus = miniDepth

/-- **The mini-bus's table facts hold at `P20`**: the shape of `mbT` (`tabsOkB`, `FixOk`, a `C_main` column per
table) and the guard's `fitsMiniB` (heights, `LayOk`, depth `12`, `633` evaluations; M′ `S2GM`). -/
theorem mbHyp20 (S : SF20) : MbHyp20 := by
  have hm : TypedV.fitsMiniB P20 mbT20 = true := S.mini
  unfold TypedV.fitsMiniB at hm
  simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at hm
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨-, hb⟩, -⟩, -⟩, -⟩, hf⟩, hg⟩, hh⟩, -⟩ := hm
  have ht : Lvm.M3.tabsOkB mbT20 = true := tabsOkB_mbT _ _ _ _
  have hsc : AllSc mbT20 := Lvm.M3.allSc_of_B ht
  have hsum : Lvm.M3.sumcheckTabs mbT20 = mbT20 := sc_all _ hsc
  refine ⟨hτ_of_hi (com_mbT _ _ _ _ fun _ ↦ rfl) hh, hsc, layOk_of_fit ⟨p20_facts.1, p20_facts.2.1⟩ hg,
    Lvm.M3.keys_of_B ht, Lvm.M3.width_pos_of_B ht, fixOk_mbT _ _ _ _, ?_, fun h ↦ ?_⟩
  · rw [hsum] at hf
    rw [← hf, p20_facts.2.2.2]
    norm_num
  · have e : (inst lay26 mbT20 h).μBus = P20.busDepth := by
      rw [LeanVM.Protocol.M3Instance.μBus, Lvm.VEq.pushLeaves_inst, hb, Lvm.VEq.log2Ceil_eq_clog,
        Lvm.M3.pushLeavesR, hsum]
    rw [e, p20_facts.2.2.1]

/-- **The typed phases' error terms at `P20`** (`L₀ = 37,696`, against `εS`, follower `LkSJ`): the mini-bus has
depth `12` (M′ `S2GM`; B1: 13) and no constraints (`B = 0`). -/
theorem errs20 (S : SF20) (h : ∀ t ∈ mbT20, t.τ ≤ lay26.μ) : TErrs 37696 (inst lay26 mbT20 h) εS LkSJ :=
  errs_at _ ((mbHyp20 S).μBus h)
    (Nat.le_zero.mp ((B_inst_le lay26 mbT20 h).trans (cons_mbT _ _ _ _).le))

/-- **`THyp` of the typed instance at `P20`** from the guard's facts. -/
theorem thyp20 (S : SF20) : THyp Ti20 where
  ok := ⟨S.hlay, one20 S.one⟩
  maps := maps20 S
  acc := acc20
  hτ := (mbHyp20 S).hτ
  sc := (mbHyp20 S).sc
  layOk := (mbHyp20 S).layOk
  keys := (mbHyp20 S).keys
  width := (mbHyp20 S).width
  fix := (mbHyp20 S).fix
  widths := (mbHyp20 S).widths
  μBus := (mbHyp20 S).μBus
  errs := errs20 S

/-! ## The other WPs' obligations (`nodeT20`: L-D's; the refinement: L-C's) -/

/-- **The typed middle phases follow the schedule** (`midFollows_midS₂`'s, against the typed `phases P20`).
Owner **L-C**. -/
theorem midFollowsT20 (S : SF20) (H : THyp Ti20) : MidFollows (midT₂ Ti20) :=
  Lvm.VEq.midFollowsT20L S H

end Lvm.CT
end
-- ===== end of `LvmCertT20` =====

-- ===== merged from `LvmMPNode` (GOLF module merge: `LvmMPNode.lean` is now a stub importing `LvmCertM20`) =====
section
-- New for lvm2 roll 11 (M′, R11-LEAD): `NodeSoundM` from a pair-form `NodeSound`, given that M′'s child reads
-- from the stream window what the pair form's child reads from the relocated `C_rec` column.

/-!
# `NodeSoundM` by transfer

`nodeSoundM_of`: if `childM x (winOf q) = childS (recOf x q)` for every statement and `C_main` column (the layout's
window fact), `NodeSound VS vk G childS` gives `NodeSoundM VS vk (GoodOfM recOf G) childM`. The node program's own
soundness (`NodeSound` for M′'s `V_S`) is the instance's obligation.
-/

set_option autoImplicit false

namespace Lvm.ASM

open RecursionFast LeanVM.Protocol

theorem nodeSoundM_of {VS : Lvm.T.SProg} {vk : RecursionFast.Digest} {G : GoodRel}
    {recOf : List UInt8 → Column CMain.nu20 → Column 19} {childS : Column 19 → RecursionFast.Signed}
    {childM : List UInt8 → List BF64 → RecursionFast.Signed}
    (hch : ∀ x q, childM x (Lvm.X.winOf q) = childS (recOf x q)) (h : NodeSound VS vk G childS) :
    NodeSoundM VS vk (GoodOfM recOf G) childM := fun c x q hok hG ↦ by
  rw [hch]
  exact h c x q (recOf x q) hok hG

end Lvm.ASM
end
-- ===== end of `LvmMPNode` =====

/-!
# M′'s certificate at `P20`

* `recB20`: the `C_rec`-shaped column of a big-layout `C_main` column, its stream block `S` (`2^19` words at
  `CMain.sOff20`); `relocB20`: a `C_rec` claim as the block claim `⟨19, sOff20⟩` on `C_main` (the V side's
  `typedClaimsN`/KS-link claims at M′). `recOf20 := recOfV recB20`, `reloc20 := relocV relocB20`.
* **`relocLaw20`**: `RelocLaw recOf20 reloc20` (R11-I's `relocLaw_view` on the big laws).
* `sIdx`, **`childM20`**: the child read from the stream window (`winOf`, lanes 40–47) at the statement's shape;
  **`win20`**: `childM20 x (winOf q) = childS (recOf20 x q)` (the window fact).
* `refinesM20` (V_S refines `PSWithM`: `LvmMPVEq.refinesM20L`); **`ext_eqM20`** (the executable extractor on good logs: `LvmMPXExtEq.ext_eqM_gen`, R11-X; `childW_stream20`).
* **`openM20`**, **`certificateM20`**.
-/

set_option autoImplicit false

namespace Lvm.CT

open RecursionFast Lvm Lvm.T Lvm.ASM Lvm.FS Lvm.Typed Lvm.QTyped
open LeanVM.Protocol LeanVM.Protocol.Verifier
open scoped NNReal ENNReal

/-! ## The relocation onto `S` -/

/-- **The stream block of a big-layout `C_main` column**, as a `C_rec` column. -/
def recB20 (q : Column CMain.nu20) : Column 19 :=
  ⟨CompPoly.CMlPolynomialEval.mk 19 (Vector.ofFn fun i ↦ q.values.getD (CMain.sOff20 + i) 0)⟩

/-- **A `C_rec` claim as a block claim on `S`.** -/
def relocB20 (c : Lvm.VEq.VStackClaim) : Lvm.VEq.VStackClaim :=
  (⟨⟨19, CMain.sOff20⟩, c.1, c.2⟩ : Lvm.VEq.BClaim).onStack

abbrev recOf20 : List UInt8 → Column CMain.nu20 → Column 19 := recOfV recB20
abbrev reloc20 : List UInt8 → Lvm.VEq.VStackClaim → Lvm.VEq.VStackClaim := relocV relocB20

/-- `S`'s words in `recB20`. -/
theorem getD_recB20 (q : Column CMain.nu20) {i : ℕ} (hi : i < 2 ^ 19) :
    (recB20 q).values.getD i 0 = q.values.getD (CMain.sOff20 + i) 0 := by
  unfold recB20 CompPoly.CMlPolynomialEval.mk
  exact Lvm.Shape.vector_getD_ofFn _ 0 hi

/-- **`recB20 q` is `q`'s stream block** (`SBlk`, `nodeT20`'s pairs). -/
theorem sBlk_recB20 (q : Column CMain.nu20) : Lvm.NS.SBlk q (recB20 q) := fun _ hw ↦ getD_recB20 q hw

theorem vgetD_ofFn_ge {α : Type} {m : ℕ} (f : Fin m → α) (d : α) {n : ℕ} (h : m ≤ n) :
    (Vector.ofFn f).getD n d = d := by
  unfold Vector.getD
  rw [Array.getD_eq_getD_getElem?, Vector.getElem?_toArray, Vector.getElem?_ofFn]
  simp [show ¬ n < m by omega]

theorem getD_recB20_ge (q : Column CMain.nu20) {i : ℕ} (hi : 2 ^ 19 ≤ i) :
    (recB20 q).values.getD i 0 = 0 := by
  unfold recB20 CompPoly.CMlPolynomialEval.mk
  exact vgetD_ofFn_ge _ 0 hi

/-- **The relocation's laws** (big layout, then `relocLaw_view`). -/
theorem relocLaw20 : RelocLaw recOf20 reloc20 := by
  refine relocLaw_view (fun c q _ h ↦ ?_) (fun c hc ↦ ?_)
  · have hal : 2 ^ 19 ∣ CMain.sOff20 := ⟨11, by norm_num [CMain.sOff20]⟩
    have hfit : CMain.sOff20 + 2 ^ 19 ≤ 2 ^ CMain.nu20 := by norm_num [CMain.sOff20, CMain.nu20]
    have h' := (holds_onStack (μ := CMain.nu20) ⟨⟨19, CMain.sOff20⟩, c.1, c.2⟩ hal hfit q).mp h
    dsimp only at h'
    unfold LeanVM.Protocol.EndToEnd.StackClaim.Holds
    rw [← h', Fin.sum_univ_eq_sum_range
      (fun n ↦ c.1 (LeanVM.Protocol.EndToEnd.boolPoint 19 n) * LeanVM.Parameters.ofK ((recB20 q).values.getD n 0))]
    exact Finset.sum_congr rfl fun n hn ↦ by rw [getD_recB20 q (Finset.mem_range.mp hn)]
  · exact isMultiaffine_onStack (n := CMain.nu20) ⟨⟨19, CMain.sOff20⟩, c.1, c.2⟩ (by norm_num [CMain.nu20]) hc

/-! ## The child from the window -/

/-- Stream word `i` (`i < 2^19`) of the statement's shape, as an index into the window (`winLo · 2^17` on). -/
def sIdx (x : List UInt8) (i : ℕ) : ℕ :=
  (if Lvm.Shape.small x then 2 * (CMain.sOff20s + i) else CMain.sOff20 + i) - Lvm.X.winLo * 2 ^ 17

/-- **The left child read from the stream window.** -/
def childM20 (x : List UInt8) (w : List BF64) : Signed :=
  Lvm.NS.childW fun i ↦ if i < 2 ^ 19 then BF64.toBitVec (w.getD (sIdx x i) 0) else BF64.toBitVec 0

theorem getD_winOf (q : Column CMain.nu20) {j : ℕ} (hj : j < 2 ^ 20) :
    (Lvm.X.winOf q).getD j 0 = q.values.getD (Lvm.X.winLo * 2 ^ 17 + j) 0 := by
  unfold Lvm.X.winOf
  rw [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range (by simp only [Lvm.X.winC]; omega)]
  rfl

/-- The big shape: `S` (`sOff20 ≥ winLo · 2^17`, `sOff20 + 2^19 ≤ (winLo + winC) · 2^17`) is read in place. -/
theorem win_big (q : Column CMain.nu20) {i : ℕ} (hi : i < 2 ^ 19) :
    (Lvm.X.winOf q).getD (CMain.sOff20 + i - Lvm.X.winLo * 2 ^ 17) 0 = q.values.getD (CMain.sOff20 + i) 0 := by
  rw [getD_winOf q (by simp only [CMain.sOff20, Lvm.X.winLo]; omega)]
  refine congrArg (fun k ↦ q.values.getD k 0) ?_
  simp only [CMain.sOff20, Lvm.X.winLo]; omega

/-- The small shape: `S` lies in `Shape.regions`' block `(20, 5·2^20, 2·2^20)` (big `sOff20 = 5·2^20 + 2^19`,
small logical `sOff20s = 2·2^20 + 2^19`), so `bigOf`'s word `sOff20 + i` is physical word `2·(sOff20s + i)`. -/
theorem win_small (q : Column CMain.nu20) {i : ℕ} (hi : i < 2 ^ 19) :
    (Lvm.X.winOf q).getD (2 * (CMain.sOff20s + i) - Lvm.X.winLo * 2 ^ 17) 0 =
      (Lvm.Shape.bigOf q).values.getD (CMain.sOff20 + i) 0 := by
  rw [getD_winOf q (by simp only [CMain.sOff20s, Lvm.X.winLo]; omega),
    Lvm.Shape.getD_bigOf q (by simp only [CMain.sOff20, CMain.nu20]; omega),
    show CMain.sOff20 + i = 4 * 2 ^ 20 + (1 * 2 ^ 20 + (2 ^ 19 + i)) by
      simp only [CMain.sOff20]; (clear * -; omega),
    Lvm.Shape.bigWord_hi q (by norm_num) (by omega), Lvm.NS.wd]
  refine congrArg (fun k ↦ q.values.getD k 0) ?_
  simp only [CMain.sOff20s, Lvm.X.winLo]; omega

theorem recOf20_eq (x : List UInt8) (q : Column CMain.nu20) :
    recOf20 x q = recB20 (Lvm.Shape.view x q) := rfl

theorem wOfCol_eq (r : Column 19) (i : ℕ) : Lvm.NS.wOfCol r i = BF64.toBitVec (r.values.getD i 0) := rfl

/-- **The window's words are the stream block's** (both shapes; `LvmMPWin`, `bigOf`). -/
theorem winW20 (x : List UInt8) (q : Column CMain.nu20) :
    (fun i ↦ if i < 2 ^ 19 then BF64.toBitVec ((Lvm.X.winOf q).getD (sIdx x i) 0) else BF64.toBitVec 0) =
      Lvm.NS.wOfCol (recOf20 x q) := funext fun i ↦ by
  -- (rewrite `wOfCol`/`recOf20` first: the kernel must not unfold `recB20`'s `2^19`-entry vector)
  rw [wOfCol_eq, recOf20_eq]
  by_cases hi : i < 2 ^ 19
  · rw [ite_eq_left hi, getD_recB20 _ hi]
    refine congrArg BF64.toBitVec ?_
    unfold sIdx Lvm.Shape.view
    cases hs : Lvm.Shape.small x
    · exact win_big q hi
    · exact win_small q hi
  · rw [ite_eq_right hi, getD_recB20_ge _ (by omega)]

/-- **The window fact**: the window's child is the stream block's (both shapes; `LvmMPWin`, `bigOf`). -/
theorem win20 (x : List UInt8) (q : Column CMain.nu20) :
    childM20 x (Lvm.X.winOf q) = Lvm.NS.childS (recOf20 x q) := by
  unfold childM20 Lvm.NS.childS
  rw [winW20]

/-! ## The other obligations -/

/-- **O5b at M′**: `VST P20 NT20` refines the compiled verifier of `PSWithM (midM reloc20 (midT₂ Ti20))`. -/
theorem refinesM20 (S : SF20) (H : THyp Ti20) :
    ∀ (vk : RecursionFast.Digest) (L : Log) (c : RecursionFast.Digest) (π : RecursionFast.Proof), isS π = true →
      (VSB20 vk c π).runLog L = some true →
      ((schemeS vk (PSWithM (midM reloc20 (midT₂ Ti20)))).V c π).runLog L = some true :=
  Lvm.VEq.refinesM20L S H

/-- **The stream block `EXM` reads is `childM20`'s** (both shapes): window word `2i` (small, `n ≤ 2^18`) or
`2^19 + i` (big) of a `2^20`-word window. -/
theorem childW_stream20 (π : RecursionFast.Proof) (x : List UInt8) (out : List BF64)
    (hn : (Lvm.VEq.pubX x).n = (Lvm.X.pw π 14).toNat) (hl : out.length = 2 ^ 20) :
    Lvm.NS.childW (Lvm.X.wStreamM π out) = childM20 x out := by
  unfold childM20
  congr 1
  funext i
  have hc : (Lvm.X.pw π 14 < RecursionFast.toWord (2 ^ 18 + 1)) ↔ Lvm.Shape.small x = true := by
    rw [BitVec.lt_def, RecursionFast.toNat_toWord (by norm_num), Lvm.Shape.small, hn, decide_eq_true_iff]
    (clear * - hn; omega)
  unfold Lvm.X.wStreamM sIdx
  by_cases hi : i < 2 ^ 19
  · rw [ite_eq_left hi]
    by_cases hs : Lvm.Shape.small x = true
    · rw [if_pos (hc.2 hs), if_pos hs,
        show 2 * (CMain.sOff20s + i) - Lvm.X.winLo * 2 ^ 17 = 2 * i by simp only [CMain.sOff20s, Lvm.X.winLo]; (clear * - hi; omega)]
    · rw [if_neg (fun h => hs (hc.1 h)), if_neg hs,
        show CMain.sOff20 + i - Lvm.X.winLo * 2 ^ 17 = 2 ^ 19 + i by simp only [CMain.sOff20, Lvm.X.winLo]; (clear * - hi; omega)]
  · rw [ite_eq_right hi]
    rw [List.getD_eq_default _ _ (by split_ifs <;> (clear * - hl hi; omega))]

/-! ## The certificate -/

/-- O4 for `EXM (accV VS)`: on witness-sending proofs it decodes. -/
theorem EXM_Wv (VS : SProg) (c : RecursionFast.Digest) (π : RecursionFast.Proof) (L : Log) (h : isS π = false) :
    Lvm.X.EXM (accV VS) c π L = RecursionFast.WitnessSending.decode π := by
  refine Lvm.X.EXM_W _ c π L fun h0 ↦ ?_
  have : π.data.getD 0 0 = 0x53 := by
    rw [Array.getD_eq_getD_getElem?, h0]; rfl
  simp [isS, this, sByte] at h

/-- The certificate of `subWith VS (EXM (accV VS)) extXM` from O1 and M′'s open obligations. -/
theorem certificateR_openVM (VS : SProg)
    (hq : ∀ H vk c π, ((VS vk c π).queries H).length ≤ qVlvm) (o : OpenSM VS (Lvm.X.EXM (accV VS))) :
    CertificateR ⟨(1 : ℝ≥0) / 340282366920938463463374607431768211456, (0 : ℝ≥0) / 1, 16384,
      fun t => 70368744177664 + 8192 * t⟩ (subWith VS (Lvm.X.EXM (accV VS)) Lvm.X.extXM) :=
  certificateR_claim VS _ Lvm.X.extXM
    ⟨fun H vk c π _ ↦ hq H vk c π, Lvm.X.computesXM _, Lvm.X.extXM_caps.2, EXM_Wv VS, sSound_of_openSM o⟩

/-- **`certificateR_openVM` at a format `f`** (the stage's `schemeSW f`). -/
theorem certificateR_openVMW (f : SFmt) (VS : SProg)
    (hq : ∀ H vk c π, ((VS vk c π).queries H).length ≤ qVlvm) (o : OpenSMW f VS (Lvm.X.EXM (accV VS))) :
    CertificateR ⟨(1 : ℝ≥0) / 340282366920938463463374607431768211456, (0 : ℝ≥0) / 1, 16384,
      fun t => 70368744177664 + 8192 * t⟩ (subWith VS (Lvm.X.EXM (accV VS)) Lvm.X.extXM) :=
  certificateR_claim VS _ Lvm.X.extXM
    ⟨fun H vk c π _ ↦ hq H vk c π, Lvm.X.computesXM _, Lvm.X.extXM_caps.2, EXM_Wv VS, sSound_of_openSMW f o⟩

end Lvm.CT
