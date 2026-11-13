-- New for lvm2 roll 11 (M′, R11-LEAD, INT): the certificate of the M′ submission at `P20`. The open obligations
-- `OpenSM` on the typed instance: `midM reloc20 (midT₂ Ti20)` (R11-I's bridge), `NodeSoundM` by transfer from B1's
-- pair-form `nodeT20` (parametric: B1's L-D stub), the relocation `relocB20` onto `C_main`'s stream block `S`, the
-- window fact, the refinement (`LvmMPVEq.refinesM20L`, R11-IR) and the executable extractor's agreement
-- (`LvmMPXExtEq.ext_eqM_gen`, R11-X).
import LvmCertT20
import LvmMPMidT
import LvmMPNode
import LvmMPVEq
import LvmMPXExtEq

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
      simp only [CMain.sOff20]; omega,
    Lvm.Shape.bigWord_hi q (by norm_num) (by omega), Lvm.NS.wd]
  refine congrArg (fun k ↦ q.values.getD k 0) ?_
  simp only [CMain.sOff20s, Lvm.X.winLo]; omega

theorem recOf20_eq (x : List UInt8) (q : Column CMain.nu20) :
    recOf20 x q = recB20 (Lvm.Shape.view x q) := rfl

theorem wOfCol_eq (r : Column 19) (i : ℕ) : Lvm.NS.wOfCol r i = BF64.toBitVec (r.values.getD i 0) := rfl

/-- **The window fact**: the window's child is the stream block's (both shapes; `LvmMPWin`, `bigOf`). -/
theorem win20 (x : List UInt8) (q : Column CMain.nu20) :
    childM20 x (Lvm.X.winOf q) = Lvm.NS.childS (recOf20 x q) := by
  unfold childM20 Lvm.NS.childS
  refine congrArg Lvm.NS.childW (funext fun i ↦ ?_)
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

/-! ## The other obligations -/

/-- **O5b at M′**: `VST P20 NT20` refines the compiled verifier of `PSWithM (midM reloc20 (midT₂ Ti20))`. -/
theorem refinesM20 (S : SF20) (H : THyp Ti20) :
    ∀ (vk : RecursionFast.Digest) (L : Log) (c : RecursionFast.Digest) (π : RecursionFast.Proof), isS π = true →
      (VSB20 vk c π).runLog L = some true →
      ((schemeS vk (PSWithM (midM reloc20 (midT₂ Ti20)))).V c π).runLog L = some true :=
  Lvm.VEq.refinesM20L S H

/-- `NodeSoundM` at `P20` from the pair form on stream-block pairs (`nodeT20`, L-D), `sBlk_recB20` and the window
fact. -/
theorem nodeM20 (S : SF20) (H : THyp Ti20) (vk : RecursionFast.Digest) :
    NodeSoundM VSB20 vk (GoodTM recOf20 Ti20 H) childM20 := fun c x q hok hG ↦ by
  rw [win20]
  exact nodeT20 S H vk c x (Lvm.Shape.view x q) (recB20 (Lvm.Shape.view x q)) hok
    ⟨hG, sBlk_recB20 _⟩

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
    omega
  unfold Lvm.X.wStreamM sIdx
  by_cases hi : i < 2 ^ 19
  · rw [ite_eq_left hi]
    by_cases hs : Lvm.Shape.small x = true
    · rw [if_pos (hc.2 hs), if_pos hs,
        show 2 * (CMain.sOff20s + i) - Lvm.X.winLo * 2 ^ 17 = 2 * i by simp only [CMain.sOff20s, Lvm.X.winLo]; omega]
    · rw [if_neg (fun h => hs (hc.1 h)), if_neg hs,
        show CMain.sOff20 + i - Lvm.X.winLo * 2 ^ 17 = 2 ^ 19 + i by simp only [CMain.sOff20, Lvm.X.winLo]; omega]
  · rw [ite_eq_right hi]
    rw [List.getD_eq_default _ _ (by split_ifs <;> omega)]

/-- **O5c at M′**: the executable extractor on good logs. -/
theorem ext_eqM20 (S : SF20) (H : THyp Ti20) :
    ∀ vk L c π, isS π = true → L.length ≤ logCap →
      Lvm.FS.Scheme.μ (kcertSM (midSpecM_T₂ H relocLaw20) le_rfl (midShapeM_T₂ Ti20 reloc20)
        (extJM (midShapeM_T₂ Ti20 reloc20) (nodeM20 S H vk))) L < 1 →
      ((schemeS vk (PSWithM (midM reloc20 (midT₂ Ti20)))).V c π).runLog L = some true →
      (∃ w, Lvm.X.EXM (accV VSB20) c π L = some w ∧ Rel (accV VSB20 vk) c w) ∨
        Lvm.X.EXM (accV VSB20) c π L = (schemeS vk (PSWithM (midM reloc20 (midT₂ Ti20)))).Ex
          (kcertSM (midSpecM_T₂ H relocLaw20) le_rfl (midShapeM_T₂ Ti20 reloc20)
            (extJM (midShapeM_T₂ Ti20 reloc20) (nodeM20 S H vk))).ext c π L := by
  exact fun vk L c π _ _ hμ hacc =>
    Lvm.ASM.ext_eqM_gen (midSpecM_T₂ H relocLaw20) le_rfl (midShapeM_T₂ Ti20 reloc20) (nodeM20 S H)
      (fun π x out hn hl => childW_stream20 π x out hn hl) (Lvm.VEq.midFollowsM20 S H reloc20)
      (fun _ _ _ hp => Lvm.X.sFits_of_acc (S := subWith VSB20 (Lvm.X.EXM (accV VSB20)) Lvm.X.extXM)
        (by show qVlvm ≤ Lvm.X.qMax; decide)
        (by rw [subWith_acc]; exact hp))
      vk L c π hμ hacc

/-! ## The certificate -/

/-- **M′'s open obligations** from the guard's facts. -/
noncomputable def openM20 (S : SF20) : OpenSM VSB20 (Lvm.X.EXM (accV VSB20)) :=
  have H := thyp20 S
  { mid := midM reloc20 (midT₂ Ti20)
    Good := GoodTM recOf20 Ti20 H
    Lm := εS
    hmid := midSpecM_T₂ H relocLaw20
    hLm := le_rfl
    hsh := midShapeM_T₂ Ti20 reloc20
    child := childM20
    hnode := nodeM20 S H
    refines := refinesM20 S H
    ext_eq := ext_eqM20 S H }

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

/-- **The certificate of the M′ submission** against the declared claim. -/
theorem certificateM20 :
    CertificateR ⟨(1 : ℝ≥0) / 340282366920938463463374607431768211456, (0 : ℝ≥0) / 1, 16384,
      fun t => 70368744177664 + 8192 * t⟩ submissionB20 := by
  unfold submissionB20
  cases h : staticOkB20 with
  | false => exact Lvm.Fin.certificateR_rejectM _
  | true => rw [Lvm.Fin.subGM_true]; exact certificateR_openVM VSB20 (hq_VST20 NT20) (openM20 (sf20 h))

end Lvm.CT
