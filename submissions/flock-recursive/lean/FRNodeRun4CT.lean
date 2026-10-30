-- New for `flock-recursive` (track SIB): the node's template with the siblings and the closure folded
-- (`askTG`'s fold, `askFold_close`), and `Gap4.imp` / `Gaps4` from the closed residual `SlotRunC`.
import FRNodeRun4CD

/-!
# `Gaps4` from the closed residual

`FRNodeRows4.askTG` folds, after IMPC2's bits and statement reads, the siblings (`sibTG`, beside by `addE`)
and closes the whole (`TG.close`). As ask templates: **`withSib`**, **`withClose`**; **`askFold_close`** is the
fold (by `rfl`).

* **`gap4Imp_of_close`**: `Gap4.imp` from the replay, the fold, `StmtN4R` and, per active slot and
  selectable index, **`SlotRunC`** — the `felems` auxiliary cells and the imports of the replay ops neither
  `rt` nor the template covers (`impQP`). The siblings' `ATImp` is `atImp_sib` with `sibOk_of`; the closure's is `atImp_close`;
  `SlotRunB` comes from `SlotRunC` by `slotRunB_of_close`, then `SlotRunA` by `slotRunA_of_bits`.
* **`gap4Imp_rtC1dC`**, **`gaps4_of_runC`**: at the certificate's replay templates `rtC1d` (SEG-R2), over
  `withRep` (the template failing at the replay ops `rtC1d` does not cover, `TG.repF`);
* **`gaps4_of_runF`** (SEG-R2): `Gaps4` from `SlotRunF`, the `felems` cells alone (`impQP_repF`).
-/

namespace FR
namespace N4s
open RecursionFast Rev4 Circ TEval W4 Tpl

/-- **The node's template with the siblings** (beside, `addE`). -/
def withSib (Aq : ℕ → AT) (π : ℕ) : AT := (withBitsS Aq π).addE (sibTG (XofA π) π (bitTabP π)).toAT

/-- **The node's template failing at the replay ops `rtC1d π` does not cover** (SEG-R2, `TG.repF`). -/
def withRep (Aq : ℕ → AT) (π : ℕ) : AT := (withSib Aq π).repF (rtC1d π).cov

/-- **The node's template closed** (`askTG`'s, SIB; SEG-R2: over `withRep`). -/
def withClose (Aq : ℕ → AT) (π : ℕ) : AT := closeP (withRep Aq π) π

/-- **The fold** (`askTG` folds the siblings and the closure after IMPC2's classes). -/
theorem askFold_close {κ : NodeKind} {w : Asg} (hone : w κ.oneCell = 1) (hE : Snd.P4b.truthEI (nodeIRows4 κ) w) :
    ∀ v < κ.vslots, ∀ p ∈ askIRows4 (withClose askAq) κ v arR2, p ∈ nodeIRows4 κ :=
  askFold (fun π _ => ⟨rfl, rfl⟩) hone hE

theorem sibCov_bitRowsB {T : BTab} {X : Ext} {π : ℕ} {P : Params} {c : CS} {pre : Option Op} {op : Op} {k : ℕ}
    {r : Row} (hr : r ∈ bitRowsB T X π P c pre op k) : sibCov op = false := by
  cases op <;> simp_all [bitRowsB, sibCov]

theorem addE_rows_left {A B : AT} {P : Params} {c : CS} {pre : Option Op} {op : Op} {k : ℕ} {r : Row}
    (hB : B.cov op = false) (hr : r ∈ A.rows P c pre op k) : r ∈ (A.addE B).rows P c pre op k := by
  simp only [AT.addE, hB, Bool.false_eq_true, ite_false]
  exact List.mem_append_left _ hr

/-- **`bitTGB`'s rows are the closed template's.** -/
theorem close_rowsB (π : ℕ) : ∀ c pre op k, ∀ r ∈ bitRowsB (bitTabP π) (XofA π) π (protoP π) c pre op k,
    r ∈ (withClose askAq π).rows (protoP π) c pre op k := by
  intro c pre op k r hr
  have hS := bitsS_rowsB π c pre op k r hr
  have hs := sibCov_bitRowsB hr
  have hs' : (sibTG (XofA π) π (bitTabP π)).cov op = false := hs
  have hE0 : r ∈ (withSib askAq π).rows (protoP π) c pre op k := addE_rows_left hs' hS
  have hnr : isRep op = false := by cases op <;> first | rfl | simp [bitRowsB] at hr
  have hE : r ∈ (withRep askAq π).rows (protoP π) c pre op k := by
    rw [withRep, repF_rows (by simp [hnr])]; exact hE0
  have hcov : closeCov op = false ∨ (withRep askAq π).cov op = true := by
    cases op with
    | tensorW j r' =>
      right
      simp only [withRep, AT.repF, withSib, AT.addE, withBitsS, withBitsB, AT.addD, TG.toAT, bitTGB, bitCovB,
        Bool.or_true, Bool.true_or]
    | askSeed _ => left; rfl
    | selectHalf _ _ _ => left; rfl
    | _ => simp [bitRowsB] at hr
  simp only [withClose, closeP, AT.close]
  split
  · rename_i hcc
    rcases hcov with h | h
    · rw [h] at hcc; cases hcc
    · split
      · first | exact hE | (rw [if_pos h]; exact hE)
      · first | exact List.mem_append_left _ hE | (rw [if_pos h]; exact List.mem_append_left _ hE)
  · exact List.mem_append_left _ hE

/-- **`Gap4.imp` from the closed residual**: from the replay (`RepOk`, its fold), the fold of `withClose`,
`StmtN4R` and, at every active slot and selectable index, `SlotRunC`. -/
theorem gap4Imp_of_close {rt : ℕ → RT} {impl₀ : OpImpl} {base : NodeKind → OpImpl}
    (hT₀ : ImplT impl₀) (hT : ∀ ν, ImplT (base ν)) (hok : RepOk rt impl₀ base) {κ : NodeKind}
    {vk c₁ c₂ : Digest} {w : Asg} {ch : List F}
    (hfoldR : ∀ v < κ.vslots, ∀ p ∈ repIRows4 rt κ v, p ∈ nodeIRows4 κ)
    (hfoldA : ∀ v < κ.vslots, ∀ p ∈ askIRows4 (withClose askAq) κ v arR2, p ∈ nodeIRows4 κ)
    (hS : N4c.StmtN4R κ (lRows4 κ) (nodeIRows4 κ) vk c₁ c₂ w ch)
    (h : ∀ v, N4c.Active4 (rd4 X.pf4) κ w v → ∀ ι, SelOk (slotAsg κ v w) (protoP (protoOf κ v)) ι →
      SlotRunC (rt (protoOf κ v)) (withRep askAq (protoOf κ v)) (implP impl₀ base (protoOf κ v) ι)
        (protoOf κ v) ι (N4c.slotIn (rd4 X.pf4) κ vk c₁ w v) ((rd4 X.pf4).slotTr κ v w) (slotAsg κ v w)) :
    ∀ v, N4c.Active4 (rd4 X.pf4) κ w v →
      SlotImp impl₀ base κ v w (N4c.slotIn (rd4 X.pf4) κ vk c₁ w v) ((rd4 X.pf4).slotTr κ v w) := by
  have hone := one_of_pubCells hS.1.2.2.2.2
  have hE := hS.1.2.2.2.1
  refine gap4Imp_of_runS hT₀ hT hok (fun e tr => X.pfHdr_reassemble4 e tr)
    (fun e₀ e₁ tr => X.pfView_reassemble4 e₀ e₁ tr) hfoldR hfoldA hS.1 fun v hv ι hι => ?_
  have hvs := active_lt X.pf4 hv
  have hask := askHolds_of (hfoldA v hvs) hE
  have hpc := pfCells_of_rows hS.1 hv
  have hX := tplExt4_okK (implTF_implP hT₀ hT (protoOf κ v) ι) (routeOk_implP impl₀ base (protoOf_le' κ v) ι)
    (protoLay (protoOf κ v))
  have hrB := close_rowsB (protoOf κ v)
  have hg := seed_rows hrB hask
  have hB : ∀ c < arNb, slotAsg κ v w (bitC (protoOf κ v) c) = 0 ∨ slotAsg κ v w (bitC (protoOf κ v) c) = 1 :=
    fun c hc => bit_slot hone hE hvs hc
  have hpad := (wots_aggPad_of_rows X.pf4 hS.1).2
  have hSt := stmtBits_of_glob hι.1 hpc hB hg
  have hPB : PosBits (bitTabP (protoOf κ v)) (slotAsg κ v w) (protoOf κ v) ι ((rd4 X.pf4).slotTr κ v w) :=
    posBits_of_glob hι (fun k v h => mkTab_ans h) hB hg fun k it e hit he => by
      rw [itemsT_get] at hit
      obtain ⟨hkn, rfl⟩ := itAt_of hit
      have ha0 : aElT k (itAt k) = ansE k := by rw [aElT, offT_get hkn.le]; rfl
      have hs := itOff_slen hkn
      have hal := ans_al hkn
      obtain ⟨h1, h2⟩ := slot_ans' hv hpad hkn he
      rw [ha0, arC, a1_slot hone hE hvs (elem_arN (by unfold ansE; omega)), arC,
        a1_slot hone hE hvs (elem_arN (by unfold ansE; omega)), h1, h2]
      exact ⟨rfl, rfl⟩
  have hSib : SibOk (bitTabP (protoOf κ v)) (slotAsg κ v w) (protoOf κ v) ι (N4c.slotIn (rd4 X.pf4) κ vk c₁ w v).π :=
    sibOk_of hS.1 hv hvs hι hPB fun x => by
      have : (N4c.slotIn (rd4 X.pf4) κ vk c₁ w v).π = (rd4 X.pf4).slotπ κ v w := by
        unfold N4c.slotIn; split <;> rfl
      rw [this, X.slotπ_byte]; rfl
  refine ⟨atOk_close (F := protoF (protoOf κ v)) (R := protoR (protoOf κ v)) (tc := (protoLay (protoOf κ v)).ctx)
      rfl (fun P cs op => xofA_isNone _ P cs op)
      (atOk_repF (atOk_addE (atOk_addD (atOk_addD (atOk_add (atOk_add (atOk_add (atOk_askT _ hS.1 hv hι)
        (atImp_inp (inpCells_of_rows (fun e₀ e₁ tr => X.pfView_reassemble4 e₀ e₁ tr)
          (fun e tr => X.pfHdr_reassemble4 e tr) hS.1 v hv ι hι)))
        (atImp_rsv_slot hS.2.1 hS.2.2 v ι _)) (atImp_impc (pfCells_of_rows hS.1 hv)))
        (atImp_bitB (xofA_imp _))) (atImp_bitS (fun P cs op hop => xofA_read _ P cs op hop) hSt))
        (atImp_sib (fun P cs op hop => xofA_sib _ P cs op hop) hSib))), ?_⟩
  refine slotRunA_of_bits (Xa := XofA (protoOf κ v)) (stepOut_len hX _)
    (fun c j r => xofA_aux _ _ c j r)
    (fun op hc => by
      simp [withClose, closeP, AT.close, withRep, AT.repF, withSib, withBitsS, withBitsB, withImpc, AT.addE,
        AT.addD, AT.add, TG.toAT, impcTG, hc])
    (fun P c pre a act k r hr => by
      have hcc : closeCov (.assertZero a act) = true := rfl
      simp only [withClose, closeP, AT.close, hcc, if_true, opImp, Bool.false_eq_true, if_false]
      refine List.mem_append_left _ ?_
      rw [if_pos (by simp [withRep, AT.repF, withSib, withBitsS, withBitsB, withImpc, AT.addE, AT.addD, AT.add,
        TG.toAT, impcTG, impcCov])]
      rw [withRep, repF_rows (by simp [isRep])]
      simp only [withSib, AT.addE, TG.toAT, sibTG, sibCov, Bool.false_eq_true, if_false]
      refine List.mem_append_left _ ?_
      simp only [withBitsS, withBitsB, AT.addD, TG.toAT, bitTGS, bitTGB, bitCovS, bitCovB, withImpc, AT.add,
        impcTG, pvP] at hr ⊢
      simp [hr])
    (fun op hc => by
      simp [withClose, closeP, AT.close, withRep, AT.repF, withSib, withBitsS, withBitsB, AT.addE, AT.addD,
        TG.toAT, bitTGB, hc])
    hrB hι hask hpc hSt hPB ?_
  exact slotRunB_of_close (stepOut_len hX _) hι.1 hask (h v hv ι hι)

/-- **`Gap4.imp` at the certificate's replay templates** (`rtC1d`, `implB`; SEG-R2: was `rtC1c`). -/
theorem gap4Imp_rtC1dC {κ : NodeKind} {vk c₁ c₂ : Digest} {w : Asg} {ch : List F}
    (hS : N4c.StmtN4R κ (lRows4 κ) (nodeIRows4 κ) vk c₁ c₂ w ch)
    (h : ∀ v, N4c.Active4 (rd4 X.pf4) κ w v → ∀ ι, SelOk (slotAsg κ v w) (protoP (protoOf κ v)) ι →
      SlotRunC (rtC1d (protoOf κ v)) (withRep askAq (protoOf κ v)) (implP Sub4.implB (fun _ => Sub4.implB) (protoOf κ v) ι)
        (protoOf κ v) ι (N4c.slotIn (rd4 X.pf4) κ vk c₁ w v) ((rd4 X.pf4).slotTr κ v w) (slotAsg κ v w)) :
    ∀ v, N4c.Active4 (rd4 X.pf4) κ w v →
      SlotImp Sub4.implB (fun _ => Sub4.implB) κ v w (N4c.slotIn (rd4 X.pf4) κ vk c₁ w v) ((rd4 X.pf4).slotTr κ v w) :=
  gap4Imp_of_close implT_implB (fun _ => implT_implB) repOk_rtC1dB
    (repFold (one_of_pubCells hS.1.2.2.2.2) hS.1.2.2.2.1)
    (askFold_close (one_of_pubCells hS.1.2.2.2.2) hS.1.2.2.2.1) hS h

/-- **`Gaps4` from the closed residual `SlotRunC` at `rtC1d`**: what is left per active slot is the `felems`
auxiliary cells and the imports of the replay ops neither `rtC1d` nor the template covers (none:
`impQP_repF`; see `gaps4_of_runF`). -/
theorem gaps4_of_runC
    (h : ∀ vk κ w c₁ c₂ ch, N4c.StmtN4R κ (lRows4 κ) (nodeIRows4 κ) vk c₁ c₂ w ch →
      ∀ v, N4c.Active4 (rd4 X.pf4) κ w v → ∀ ι, SelOk (slotAsg κ v w) (protoP (protoOf κ v)) ι →
        SlotRunC (rtC1d (protoOf κ v)) (withRep askAq (protoOf κ v)) (implP Sub4.implB (fun _ => Sub4.implB) (protoOf κ v) ι)
          (protoOf κ v) ι (N4c.slotIn (rd4 X.pf4) κ vk c₁ w v) ((rd4 X.pf4).slotTr κ v w) (slotAsg κ v w)) :
    Sub4.Gaps4 :=
  fun vk κ w c₁ c₂ ch hS => gap4Imp_rtC1dC hS (h vk κ w c₁ c₂ ch hS)

/-- **`Gaps4` from the `felems` run facts alone** (SEG-R2): the replay ops' imports are gone (`rtC1d` replays
the five segment ops; any other replay op fails in the circuit, `TG.repF`), so per active slot and
selectable index what is left is `SlotRunF`: the `felems` auxiliary cells. -/
theorem gaps4_of_runF
    (h : ∀ vk κ w c₁ c₂ ch, N4c.StmtN4R κ (lRows4 κ) (nodeIRows4 κ) vk c₁ c₂ w ch →
      ∀ v, N4c.Active4 (rd4 X.pf4) κ w v → ∀ ι, SelOk (slotAsg κ v w) (protoP (protoOf κ v)) ι →
        SlotRunF (implP Sub4.implB (fun _ => Sub4.implB) (protoOf κ v) ι)
          (protoOf κ v) ι (N4c.slotIn (rd4 X.pf4) κ vk c₁ w v) ((rd4 X.pf4).slotTr κ v w) (slotAsg κ v w)) :
    Sub4.Gaps4 :=
  gaps4_of_runC fun vk κ w c₁ c₂ ch hS v hv ι hι => slotRunC_of_F (h vk κ w c₁ c₂ ch hS v hv ι hι)

/-! ## Controls -/

namespace SibCtl

/-- (+) **`bitNxAll`**: a `bitOf` followed by a `selectHalf` on its result; (−) followed by another op, by a
`selectHalf` on another register, or last. -/
theorem bitNxAll_ctl : bitNxAll 5 [.bitOf 3 0, .selectHalf 5 1 2] = true ∧ bitNxAll 5 [.bitOf 3 0, .addF 1 2] = false ∧
    bitNxAll 5 [.bitOf 3 0, .selectHalf 4 1 2] = false ∧ bitNxAll 5 [.bitOf 3 0] = false := by
  refine ⟨rfl, rfl, rfl, rfl⟩

/-- (+) **`closeCov`**: a proof read, an `input`, an assertion are the closure's; (−) an ask, a `bitOf`, a
replay op and an arithmetic op are not. -/
theorem closeCov_ctl : closeCov (.piDigest 17 0) = true ∧ closeCov (.input 0) = true ∧
    closeCov (.assertEq 0 1 fun _ => true) = true ∧ closeCov (.askSeed 0) = false ∧ closeCov (.bitOf 0 0) = false ∧
    closeCov (.shiftTarget 0 0 0 0) = false ∧ closeCov (.addF 0 1) = false := by
  refine ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- No template. -/
def X0 : Ext := fun _ _ _ => none
/-- A template taking every op. -/
def X1 : Ext := fun _ _ _ => some { slots := [] }
/-- Toy selector forms. -/
def P0 : Params := ⟨Lin.cell 0, fun _ => []⟩
/-- A table without a statement. -/
def T0 : BTab := ⟨#[], #[], #[], #[], 0, none⟩

/-- (+) **`impRows`**: an import no template takes fails (an `input`; a `piDigest`); (−) one a template may
take (`eqPt`) and takes does not. -/
theorem impRows_ctl : impRows X0 P0 (CS.init 0) (.input 0) = [failRT P0] ∧
    impRows X1 P0 (CS.init 0) (.piDigest 17 0) = [failRT P0] ∧ impRows X1 P0 (CS.init 0) (.eqPt 0 1) = [] := by
  refine ⟨rfl, rfl, rfl⟩

/-- (+) **`forRows`**: a foreign `assertBit` neither the zero pins nor the statement discharge fails; (−) an
`assertEq` off at every kind is not foreign. -/
theorem forRows_ctl : forRows X0 [] T0 P0 (CS.init 0) (.assertBit 0 fun _ => true) = [failRT P0] ∧
    forRows X0 [] T0 P0 (CS.init 0) (.assertEq 0 1 fun _ => false) = [] := by
  refine ⟨rfl, rfl⟩

/-- (+) **`TG.close`**: at an import its part does not cover, the failing row; (−) at one its part covers, the
part's rows; at the first ask with a `bitOf` not followed by its `selectHalf`, the failing row. -/
theorem close_ctl :
    (TG.none.close X0 [] T0 (bitNxAll 0 [])).rows P0 (CS.init 0) none (.input 0) 0 = [failRT P0] ∧
    ((inpTG X0 0).close X0 [] T0 (bitNxAll 0 [])).rows P0 (CS.init 0) none (.input 0) 0 = (inpTG X0 0).rows P0 (CS.init 0) none (.input 0) 0 ∧
    (TG.none.close X0 [] T0 (bitNxAll 0 [.bitOf 3 0])).rows P0 (CS.init 0) none (.askSeed 0) 0 = [failRT P0] ∧
    (TG.none.close X0 [] T0 (bitNxAll 0 [.bitOf 3 0, .selectHalf 0 1 2])).rows P0 (CS.init 0) none (.askSeed 0) 0 = [] := by
  refine ⟨rfl, rfl, rfl, rfl⟩

end SibCtl

end N4s
end FR
