-- New for lvm2 MP-B cap pruning (CAP-X2, 2026-11-17): S2GB's extractor program meets `DecOkB` (well-formed, safe on
-- the size range, within the fuel budget, the outputs and the size). Proof-help statements of `computesXB20`.
import LvmS2GBExtProg
import LvmS2GBExtComp
import LvmS2GBExtRep
import LvmS2GBExtTailSem
import LvmS2GBExtPlanW

/-!
# S2GB's extractor program is well-formed, safe and within budget

* **`wf_decXB20`**: the node branch's program is well-formed (the dynamic copies by `Sim.wf`);
* **`decOk_decXB20`**: `DecOkB loB hiB decXB20` (safe on every tape of a proof in the size range, the cost within
  `decBudgetM`, the outputs within `outCap`, the size within `2^19`).
-/

set_option autoImplicit false

namespace Lvm.XB

open RecursionFast Lvm Lvm.X Lvm.XS

/-! ## The dynamic reads: the syntactic facts by `Sim` -/

/-- A tape and a log position at which `pLW` is the log position (the syntactic facts do not depend on them). -/
theorem pLW_nil : pLW #[] = BitVec.ofNat 64 (pLW #[]).toNat := by simp

theorem wf_idxIR4D (bX : ℕ) : WF (idxIR4D bX) := (idxIR4D_sim pLW_nil bX).wf (wf_idxIR4 bX _)

theorem wf_chainIRD (N : ℕ) (tab : List Word) {sd : XIR} (hsd : WF sd) (hc : ¬ Writes sd rCC) :
    WF (chainIRD N tab sd) :=
  (chainIRD_sim pLW_nil N tab sd).wf (wf_chainIR _ N tab hsd hc)

theorem wf_readGIRD (bX capW wB nPos D z occ : ℕ) : WF (readGIRD bX capW wB nPos D z occ) :=
  (readGIRD_sim pLW_nil bX capW wB nPos D z occ).wf (wf_readGIR ..)

theorem noLoopT_readGIRD (bX capW wB nPos D z occ : ℕ) : NoLoopT (readGIRD bX capW wB nPos D z occ) :=
  (readGIRD_sim pLW_nil bX capW wB nPos D z occ).noLoopT (noLoopT_readGIR ..)

/-! ## The π tail's programs: well formed, no tape loop -/

theorem wf_clrIR : ∀ (b n : ℕ), WF (clrIR b n)
  | _, 0 => by simp [clrIR, WF]
  | b, n + 1 => ⟨⟨by simp +decide [WF, Prim.dst, tA, tC], show tA ≠ cTmp by decide⟩, wf_clrIR (b + 1) n⟩

theorem wf_markIR (bm m : ℕ) : ∀ ps : List (ℕ × ℕ), WF (markIR bm m ps)
  | [] => by simp [markIR, WF]
  | (a, off) :: ps => ⟨wf_mark1IR bm m a off, wf_markIR bm m ps⟩

theorem wf_cntIR' : ∀ (b n : ℕ), WF (cntIR' b n)
  | _, 0 => by simp [cntIR', WF]
  | b, n + 1 => ⟨by simp +decide [WF, Prim.dst, tA, tB, tK, tN], wf_cntIR' (b + 1) n⟩

theorem wf_nodesIR (bm : ℕ) (heap : List ℕ) : ∀ xs : List ℕ, WF (nodesIR bm heap xs)
  | [] => by simp [nodesIR, WF]
  | x :: xs => ⟨wf_node1IR _ _ _, wf_nodesIR bm heap xs⟩

theorem wf_bmIR : ∀ ls : List TLv, WF (bmIR ls)
  | [] => by simp [bmIR, WF]
  | l :: ls => ⟨⟨wf_clrIR _ _, wf_markIR _ _ _⟩, wf_bmIR ls⟩

theorem wf_cntAllIR : ∀ ls : List TLv, WF (cntAllIR ls)
  | [] => by simp [cntAllIR, WF]
  | l :: ls => ⟨wf_cntIR' _ _, wf_cntAllIR ls⟩

theorem wf_sizeWIR (pz0 : ℕ) (ls : List TLv) : WF (sizeWIR pz0 ls) :=
  ⟨by simp +decide [WF, Prim.dst, tN], wf_cntAllIR ls, by simp +decide [WF, Prim.dst, tN, tK], trivial⟩

theorem wf_tailIR : ∀ ls : List TLv, WF (tailIR ls)
  | [] => by simp [tailIR, WF]
  | l :: ls => ⟨wf_nodesIR _ _ _, wf_tailIR ls⟩

theorem noLoopT_clrIR : ∀ (b n : ℕ), NoLoopT (clrIR b n)
  | _, 0 => trivial
  | b, n + 1 => ⟨⟨trivial, trivial⟩, noLoopT_clrIR (b + 1) n⟩

theorem noLoopT_mark1IR (bm m a off : ℕ) : NoLoopT (mark1IR bm m a off) := by
  unfold mark1IR
  split <;> simp [NoLoopT]

theorem noLoopT_markIR (bm m : ℕ) : ∀ ps : List (ℕ × ℕ), NoLoopT (markIR bm m ps)
  | [] => trivial
  | (a, off) :: ps => ⟨noLoopT_mark1IR bm m a off, noLoopT_markIR bm m ps⟩

theorem noLoopT_cntIR' : ∀ (b n : ℕ), NoLoopT (cntIR' b n)
  | _, 0 => trivial
  | b, n + 1 => ⟨⟨trivial, trivial, trivial⟩, noLoopT_cntIR' (b + 1) n⟩

theorem noLoopT_cpWIR : ∀ (a n : ℕ), NoLoopT (cpWIR a n)
  | _, 0 => trivial
  | a, n + 1 => ⟨⟨trivial, trivial, trivial⟩, noLoopT_cpWIR (a + 1) n⟩

theorem noLoopT_nodesIR (bm : ℕ) (heap : List ℕ) : ∀ xs : List ℕ, NoLoopT (nodesIR bm heap xs)
  | [] => trivial
  | _ :: xs => ⟨⟨⟨trivial, trivial⟩, trivial, noLoopT_cpWIR _ _⟩, noLoopT_nodesIR bm heap xs⟩

theorem noLoopT_bmIR : ∀ ls : List TLv, NoLoopT (bmIR ls)
  | [] => trivial
  | _ :: ls => ⟨⟨noLoopT_clrIR _ _, noLoopT_markIR _ _ _⟩, noLoopT_bmIR ls⟩

theorem noLoopT_cntAllIR : ∀ ls : List TLv, NoLoopT (cntAllIR ls)
  | [] => trivial
  | _ :: ls => ⟨noLoopT_cntIR' _ _, noLoopT_cntAllIR ls⟩

theorem noLoopT_sizeWIR (pz0 : ℕ) (ls : List TLv) : NoLoopT (sizeWIR pz0 ls) :=
  ⟨trivial, noLoopT_cntAllIR ls, trivial, trivial⟩

theorem noLoopT_tailIR : ∀ ls : List TLv, NoLoopT (tailIR ls)
  | [] => trivial
  | _ :: ls => ⟨noLoopT_nodesIR _ _ _, noLoopT_tailIR ls⟩

/-! ## The node output -/

/-- `outIRB` with its static data as parameters. -/
def outIRBG (ls : List TLv) (st : XStage) (pz0 mB : ℕ) : XIR :=
  .seq (emitIR (toWord 1)) (.seq (tcpIR 11 4) (.seq (leafStmtIR 20 19)
  (.seq (copyIR mB) (.seq (bmIR ls) (.seq (sizeWIR pz0 ls)
  (.seq (setR sgB) (.seq (segIR apC 0 (pSegS st)) (.seq (tailIR ls) (.seq (segIR apC 0 (trSegS st))
  (.seq (setR (sigB mB)) (.seq (segIR apC 0 (.cp 0 597))
  (.seq (emitIR (toWord 48)) (.seq (emitIR (toWord 0)) (.seq (tcpIR 15 5)
  (.seq (emitIR (toWord 0)) (rsigIR st mB))))))))))))))))

theorem outIRB_eq (m : ℕ) : outIRB m = outIRBG tlvB20 stB20 (piStatic P20B) m := rfl

theorem depth_pSegS (st : XStage) : depthSeg (pSegS st) ≤ 2 := by
  rw [pSegS, depthSeg]
  exact max_le (Nat.zero_le _) (depthSeg_blkPSegsS 6 _)

theorem depth_trSegS (st : XStage) : depthSeg (trSegS st) ≤ 2 := by
  rw [trSegS]
  simp only [depthSeg]
  have := depthSeg_blkTSegsS 6 (blocksS st)
  omega

theorem wf_outIRBG (ls : List TLv) (st : XStage) (pz0 m : ℕ) : WF (outIRBG ls st pz0 m) := by
  have h1 := depth_pSegS st
  have h2 := depth_trSegS st
  refine ⟨wf_emitIR _, wf_tcpIR _ _, wf_leafStmtIR _ _, wf_copyIR _, wf_bmIR _, wf_sizeWIR _ _, ?_,
    wf_segIR _ _ _ (by omega), wf_tailIR _, wf_segIR _ _ _ (by omega), ?_,
    wf_segIR _ _ _ (by decide), wf_emitIR _, wf_emitIR _, wf_tcpIR _ _, wf_emitIR _, wf_rsigIR st m⟩ <;>
  simp +decide [setR, WF, Prim.dst, oR, oKF, oBd]

theorem noLoopT_outIRBG (ls : List TLv) (st : XStage) (pz0 m : ℕ) : NoLoopT (outIRBG ls st pz0 m) :=
  ⟨noLoopT_emitIR _, noLoopT_tcpIR _ _, noLoopT_leafStmtIR _ _, noLoopT_copyIR _, noLoopT_bmIR _,
    noLoopT_sizeWIR _ _, noLoopT_setR _, noLoopT_segIR _ _ _, noLoopT_tailIR _, noLoopT_segIR _ _ _, noLoopT_setR _,
    noLoopT_segIR _ _ _, noLoopT_emitIR _, noLoopT_emitIR _, noLoopT_tcpIR _ _, noLoopT_emitIR _,
    noLoopT_rsigIR st m⟩

theorem wf_outIRB (m : ℕ) : WF (outIRB m) := by
  rw [outIRB_eq]; exact wf_outIRBG _ _ _ _

theorem noLoopT_outIRB (m : ℕ) : NoLoopT (outIRB m) := by
  rw [outIRB_eq]; exact noLoopT_outIRBG _ _ _ _

/-! ## Well formed -/

theorem wf_okL0B : WF okL0B :=
  ⟨by simp +decide [WF], show 4 ≤ eW by decide, ⟨wf_streamS stB20, wf_outIRB _⟩, by simp [WF]⟩

theorem wf_okL1B : WF okL1B :=
  ⟨by simp +decide [WF], show 4 ≤ eW by decide, ⟨wf_dec0S stB20, wf_okL0B⟩, by simp [WF]⟩

theorem wf_okL2B : WF okL2B :=
  ⟨by simp +decide [WF], show 4 ≤ eW by decide, ⟨wf_dec1MPIR .., wf_okL1B⟩, by simp [WF]⟩

theorem wf_nodeB20 : WF nodeB20 :=
  ⟨wf_idxIR4D _, wf_chainIRD _ _ wf_sdL (nw_sdL _ (by decide) (by decide) (by decide)),
    wf_readGIRD .., wf_readGIRD .., wf_readGIRD .., wf_acpS stB20, wf_thcpIR _ _ _, wf_dec1MPIR .., wf_okL2B⟩

/-- S2GB's SNARK branch is well-formed. -/
theorem wf_decXB20 : WF decXB20 := by
  refine ⟨?_, wf_nodeB20, wf_leafIR⟩
  simp +decide [readAt, WF, rA, rBb]

/-! ## The dynamic reads: cost, outputs, size -/

theorem cost_idxIR4D (bX t : ℕ) : cost (idxIR4D bX) t = 3516 + t / 5 * 11871 := by
  simp only [idxIR4D, walkIR4D, walkPre4D, pLIR, walkBody, sortIR4D, sortPre4D, passIR4D, passPre4D, swapPs,
    stepIR, blockIR, cmpIR, cmpWord, aposIR, ceil8Ps, minPs, readAt, cost, blkSteps,
    List.length_cons, List.length_nil, List.length_append, Aff.eval, Nat.one_mul]
  norm_num
  (clear * - t; omega)

theorem outs_idxIR4D (bX t : ℕ) : outs (idxIR4D bX) t = 0 := by
  simp [idxIR4D, walkIR4D, walkPre4D, pLIR, walkBody, sortIR4D, sortPre4D, passIR4D, passPre4D, swapPs, stepIR,
    blockIR, cmpIR, cmpWord, aposIR, readAt, outs]

theorem sizeIR_idxIR4D (bX : ℕ) : sizeIR (idxIR4D bX) = 336 := by
  simp only [idxIR4D, walkIR4D, walkPre4D, pLIR, walkBody, sortIR4D, sortPre4D, passIR4D, passPre4D, swapPs,
    stepIR, blockIR, cmpIR, cmpWord, aposIR, ceil8Ps, minPs, readAt, sizeIR, blkSteps,
    List.length_cons, List.length_nil, List.length_append]
  norm_num

theorem cost_chainIRD (N t : ℕ) (tab : List Word) (sd : XIR) :
    cost (chainIRD N tab sd) t = 80 + 9 * tab.length + cost sd t + t / 5 * 24 + t * 168 := by
  simp only [chainIRD, cntIRD, cntPreD, cntPostD, startD, pLIR, cntBody, readAt, ceil8Ps, cost, cost_storesIR,
    cost_wordIR, blkSteps, List.length_cons, List.length_nil, List.length_append, Aff.eval, Nat.one_mul,
    Nat.div_one]
  norm_num
  (clear * - t tab sd; omega)

theorem outs_chainIRD (N t : ℕ) (tab : List Word) {sd : XIR} (hsd : outs sd t = 0) :
    outs (chainIRD N tab sd) t = 0 := by
  simp [chainIRD, cntIRD, cntPreD, cntPostD, startD, pLIR, cntBody, readAt, wordIR, lenIR, qryIR, ansIR, lastIR,
    recIR, recPre, recPs, st4IR, nextIR, nextPre, nextPs, stNext, outs, outs_storesIR, hsd]

theorem sizeIR_chainIRD (N : ℕ) (tab : List Word) (sd : XIR) :
    sizeIR (chainIRD N tab sd) = 318 + 10 * tab.length + sizeIR sd := by
  simp only [chainIRD, cntIRD, cntPreD, cntPostD, startD, pLIR, cntBody, readAt, wordIR, lenIR, qryIR, ansIR,
    ansPs, setSPs, lastIR, recIR, recPre, recPs, st4IR, nextIR, nextPre, nextPs, stNext, ceil8Ps, sizeIR,
    size_storesIR, blkSteps, List.length_cons, List.length_nil, List.length_append]
  norm_num
  (clear * - tab sd; omega)

theorem cost_lookIR4D (bX t : ℕ) : cost (lookIR4D bX) t = 6500 := by
  simp only [lookIR4D, lookPre4D, pLIR, bsBody4, foundIR4, ansLtIR, cmpTWord, eqTWord, aposIR, ceil8Ps, readAt,
    cost, blkSteps, List.length_append, List.length_cons, List.length_nil]
  norm_num

theorem cost_crPosGD (bX capW D z occ t : ℕ) (hD : D < 2 ^ 64) (hz : z < 2 ^ 64) (ho : occ < 2 ^ 64) :
    cost (crPosGD bX capW D z occ) t = 6583 + 6546 * D + 9 * z + 25 * occ := by
  simp only [crPosGD, crCapGPs, crLd4, crNodeD, crGet, crChkPs, crChildPs, crLeafD, crCopyG, crZeroG,
    crZeroBody, crCopyBody, cost, cost_lookIR4D, blkSteps, List.length_cons, List.length_nil,
    toNat_toWord hD, toNat_toWord hz, toNat_toWord ho]
  norm_num; ring

/-- **The dynamic read's cost** on every tape. -/
theorem cost_readGIRD (bX capW wB nPos D z occ t : ℕ) (hn : nPos < 2 ^ 64) (hD : D < 2 ^ 64)
    (hz : z < 2 ^ 64) (ho : occ < 2 ^ 64) :
    cost (readGIRD bX capW wB nPos D z occ) t = 14 + nPos * (6586 + 6546 * D + 9 * z + 25 * occ) := by
  simp only [readGIRD, cost, cost_crPosGD bX capW D z occ t hD hz ho, blkSteps, List.length_cons,
    List.length_nil, toNat_toWord hn]
  norm_num; ring

theorem outs_readGIRD (bX capW wB nPos D z occ t : ℕ) : outs (readGIRD bX capW wB nPos D z occ) t = 0 := by
  simp [readGIRD, crPosGD, crLd4, crGet, crNodeD, crLeafD, crCopyBody, crCopyG, crZeroG, crZeroBody,
    lookIR4D, lookPre4D, pLIR, bsBody4, ansLtIR, cmpTWord, eqTWord, foundIR4, aposIR, readAt, outs]

theorem sizeIR_readGIRD (bX capW wB nPos D z occ : ℕ) : sizeIR (readGIRD bX capW wB nPos D z occ) = 591 := by
  simp only [readGIRD, crPosGD, crLd4, crCapGPs, crGet, crChkPs, crChildPs, crNodeD, crLeafD, crCopyBody,
    crCopyG, crZeroG, crZeroBody, lookIR4D, lookPre4D, pLIR, bsBody4, ansLtIR, cmpTWord, eqTWord, foundIR4,
    aposIR, ceil8Ps, readAt, sizeIR, blkSteps, List.length_cons, List.length_nil, List.length_append]
  norm_num

/-! ## The π tail's programs: cost, outputs, size -/

theorem cost_clrIR (t : ℕ) : ∀ (b n : ℕ), cost (clrIR b n) t = 9 * n + 1
  | _, 0 => rfl
  | b, n + 1 => by
    rw [clrIR, cost, cost_clrIR t (b + 1) n]
    norm_num [cost, blkSteps]; omega

theorem sizeIR_clrIR : ∀ (b n : ℕ), sizeIR (clrIR b n) = 10 * n + 1
  | _, 0 => rfl
  | b, n + 1 => by
    rw [clrIR, sizeIR, sizeIR_clrIR (b + 1) n]
    norm_num [sizeIR, blkSteps]; omega

theorem outs_clrIR (t : ℕ) : ∀ (b n : ℕ), outs (clrIR b n) t = 0
  | _, 0 => rfl
  | b, n + 1 => by rw [clrIR, outs, outs_clrIR t (b + 1) n]; rfl

theorem cost_mark1IR (bm m a off t : ℕ) : cost (mark1IR bm m a off) t ≤ 32 := by
  unfold mark1IR
  split <;> simp [cost, blkSteps]

theorem sizeIR_mark1IR (bm m a off : ℕ) : sizeIR (mark1IR bm m a off) ≤ 33 := by
  unfold mark1IR
  split <;> simp [sizeIR, blkSteps]

theorem outs_mark1IR (bm m a off t : ℕ) : outs (mark1IR bm m a off) t = 0 := by
  unfold mark1IR
  split <;> simp [outs]

theorem cost_markIR (bm m t : ℕ) : ∀ ps : List (ℕ × ℕ), cost (markIR bm m ps) t ≤ 33 * ps.length + 1
  | [] => le_refl _
  | (a, off) :: ps => by
    have h1 := cost_mark1IR bm m a off t
    have h2 := cost_markIR bm m t ps
    rw [markIR, cost, List.length_cons]
    omega

theorem sizeIR_markIR (bm m : ℕ) : ∀ ps : List (ℕ × ℕ), sizeIR (markIR bm m ps) ≤ 34 * ps.length + 1
  | [] => le_refl _
  | (a, off) :: ps => by
    have h1 := sizeIR_mark1IR bm m a off
    have h2 := sizeIR_markIR bm m ps
    rw [markIR, sizeIR, List.length_cons]
    omega

theorem outs_markIR (bm m t : ℕ) : ∀ ps : List (ℕ × ℕ), outs (markIR bm m ps) t = 0
  | [] => rfl
  | (a, off) :: ps => by rw [markIR, outs, outs_mark1IR, outs_markIR bm m t ps]

theorem cost_cntIR' (t : ℕ) : ∀ (b n : ℕ), cost (cntIR' b n) t = 10 * n + 1
  | _, 0 => rfl
  | b, n + 1 => by
    rw [cntIR', cost, cost_cntIR' t (b + 1) n]
    norm_num [cost, blkSteps]; omega

theorem sizeIR_cntIR' : ∀ (b n : ℕ), sizeIR (cntIR' b n) = 10 * n + 1
  | _, 0 => rfl
  | b, n + 1 => by
    rw [cntIR', sizeIR, sizeIR_cntIR' (b + 1) n]
    norm_num [sizeIR, blkSteps]; omega

theorem outs_cntIR' (t : ℕ) : ∀ (b n : ℕ), outs (cntIR' b n) t = 0
  | _, 0 => rfl
  | b, n + 1 => by rw [cntIR', outs, outs_cntIR' t (b + 1) n]; rfl

theorem cost_cpWIR (t : ℕ) : ∀ (a n : ℕ), cost (cpWIR a n) t = 6 * n + 1
  | _, 0 => rfl
  | a, n + 1 => by
    rw [cpWIR, cost, cost_cpWIR t (a + 1) n]
    norm_num [cost, blkSteps]; omega

theorem sizeIR_cpWIR : ∀ (a n : ℕ), sizeIR (cpWIR a n) = 6 * n + 1
  | _, 0 => rfl
  | a, n + 1 => by
    rw [cpWIR, sizeIR, sizeIR_cpWIR (a + 1) n]
    norm_num [sizeIR, blkSteps]; omega

theorem outs_cpWIR (t : ℕ) : ∀ (a n : ℕ), outs (cpWIR a n) t = n
  | _, 0 => rfl
  | a, n + 1 => by
    rw [cpWIR, outs, outs_cpWIR t (a + 1) n]
    simp only [outs]
    omega

theorem cost_nodesIR (bm : ℕ) (heap : List ℕ) (t : ℕ) : ∀ xs : List ℕ, cost (nodesIR bm heap xs) t = 31 * xs.length + 1
  | [] => rfl
  | x :: xs => by
    rw [nodesIR, cost, cost_nodesIR bm heap t xs, node1IR]
    norm_num [cost, cost_cpWIR, blkSteps]; omega

theorem sizeIR_nodesIR (bm : ℕ) (heap : List ℕ) : ∀ xs : List ℕ, sizeIR (nodesIR bm heap xs) = 32 * xs.length + 1
  | [] => rfl
  | x :: xs => by
    rw [nodesIR, sizeIR, sizeIR_nodesIR bm heap xs, node1IR]
    norm_num [sizeIR, sizeIR_cpWIR, blkSteps]; omega

theorem outs_nodesIR (bm : ℕ) (heap : List ℕ) (t : ℕ) : ∀ xs : List ℕ, outs (nodesIR bm heap xs) t = 4 * xs.length
  | [] => rfl
  | x :: xs => by
    rw [nodesIR, outs, outs_nodesIR bm heap t xs, node1IR]
    simp only [outs, outs_cpWIR, List.length_cons]
    omega

/-- The levels' node count. -/
def tN1 (ls : List TLv) : ℕ := (ls.map fun l => 2 ^ l.m).sum
/-- The levels' path count. -/
def tN2 (ls : List TLv) : ℕ := (ls.map fun l => l.pos.length).sum

theorem cost_bmIR (t : ℕ) : ∀ ls : List TLv, cost (bmIR ls) t ≤ 9 * tN1 ls + 33 * tN2 ls + 4 * ls.length + 1
  | [] => le_refl _
  | l :: ls => by
    have h1 := cost_markIR l.bm l.m t l.pos
    have h2 := cost_bmIR t ls
    rw [bmIR, cost, cost, cost_clrIR]
    simp only [tN1, tN2, List.map_cons, List.sum_cons, List.length_cons] at h2 ⊢
    omega

theorem sizeIR_bmIR : ∀ ls : List TLv, sizeIR (bmIR ls) ≤ 10 * tN1 ls + 34 * tN2 ls + 4 * ls.length + 1
  | [] => le_refl _
  | l :: ls => by
    have h1 := sizeIR_markIR l.bm l.m l.pos
    have h2 := sizeIR_bmIR ls
    rw [bmIR, sizeIR, sizeIR, sizeIR_clrIR]
    simp only [tN1, tN2, List.map_cons, List.sum_cons, List.length_cons] at h2 ⊢
    omega

theorem outs_bmIR (t : ℕ) : ∀ ls : List TLv, outs (bmIR ls) t = 0
  | [] => rfl
  | l :: ls => by rw [bmIR, outs, outs, outs_clrIR, outs_markIR, outs_bmIR t ls]

theorem cost_cntAllIR (t : ℕ) : ∀ ls : List TLv, cost (cntAllIR ls) t = 10 * tN1 ls + 2 * ls.length + 1
  | [] => rfl
  | l :: ls => by
    have h2 := cost_cntAllIR t ls
    rw [cntAllIR, cost, cost_cntIR', h2]
    simp only [tN1, List.map_cons, List.sum_cons, List.length_cons]
    omega

theorem sizeIR_cntAllIR : ∀ ls : List TLv, sizeIR (cntAllIR ls) = 10 * tN1 ls + 2 * ls.length + 1
  | [] => rfl
  | l :: ls => by
    have h2 := sizeIR_cntAllIR ls
    rw [cntAllIR, sizeIR, sizeIR_cntIR', h2]
    simp only [tN1, List.map_cons, List.sum_cons, List.length_cons]
    omega

theorem outs_cntAllIR (t : ℕ) : ∀ ls : List TLv, outs (cntAllIR ls) t = 0
  | [] => rfl
  | l :: ls => by rw [cntAllIR, outs, outs_cntIR', outs_cntAllIR t ls]

theorem cost_sizeWIR (pz0 t : ℕ) (ls : List TLv) : cost (sizeWIR pz0 ls) t = 10 * tN1 ls + 2 * ls.length + 13 := by
  norm_num [sizeWIR, cost, cost_cntAllIR, blkSteps]; omega

theorem sizeIR_sizeWIR (pz0 : ℕ) (ls : List TLv) : sizeIR (sizeWIR pz0 ls) = 10 * tN1 ls + 2 * ls.length + 13 := by
  norm_num [sizeWIR, sizeIR, sizeIR_cntAllIR, blkSteps]; omega

theorem outs_sizeWIR (pz0 t : ℕ) (ls : List TLv) : outs (sizeWIR pz0 ls) t = 1 := by
  simp only [sizeWIR, outs, outs_cntAllIR]

theorem cost_tailIR (t : ℕ) : ∀ ls : List TLv, cost (tailIR ls) t = 31 * tN1 ls + 2 * ls.length + 1
  | [] => rfl
  | l :: ls => by
    have h2 := cost_tailIR t ls
    rw [tailIR, cost, cost_nodesIR, h2, List.length_range]
    simp only [tN1, List.map_cons, List.sum_cons, List.length_cons]
    omega

theorem sizeIR_tailIR : ∀ ls : List TLv, sizeIR (tailIR ls) = 32 * tN1 ls + 2 * ls.length + 1
  | [] => rfl
  | l :: ls => by
    have h2 := sizeIR_tailIR ls
    rw [tailIR, sizeIR, sizeIR_nodesIR, h2, List.length_range]
    simp only [tN1, List.map_cons, List.sum_cons, List.length_cons]
    omega

theorem outs_tailIR (t : ℕ) : ∀ ls : List TLv, outs (tailIR ls) t = 4 * tN1 ls
  | [] => rfl
  | l :: ls => by
    have h2 := outs_tailIR t ls
    rw [tailIR, outs, outs_nodesIR, h2, List.length_range]
    simp only [tN1, List.map_cons, List.sum_cons]
    omega

/-! ## S2GB's static facts (one kernel evaluation each) -/

/-- A plan entry's layer nodes in `tlvsFrom` (`2^m` at a level's first heap entry). -/
def tlvM (e : Replay.PE) : ℕ :=
  match e.k with
  | .heap _ _ _ _ _ m k _ => if k + 1 = 2 ^ m then 2 ^ m else 0
  | _ => 0

/-- A plan entry's paths in `tlvsFrom`. -/
def tlvT (e : Replay.PE) : ℕ :=
  match e.k with
  | .heap _ _ t _ _ m k _ => if k + 1 = 2 ^ m then t else 0
  | _ => 0

/-- A plan entry's levels in `tlvsFrom`. -/
def tlvC (e : Replay.PE) : ℕ :=
  match e.k with
  | .heap _ _ _ _ _ m k _ => if k + 1 = 2 ^ m then 1 else 0
  | _ => 0

/-- `tlvsFrom`'s shape from the plan entries alone. -/
theorem tlvsFrom_shape (st : XStage) : ∀ (bm : ℕ) (l : List (ℕ × Replay.PE)),
    tN1 (tlvsFrom st bm l) = (l.map fun x => tlvM x.2).sum ∧ tN2 (tlvsFrom st bm l) = (l.map fun x => tlvT x.2).sum ∧
      (tlvsFrom st bm l).length = (l.map fun x => tlvC x.2).sum
  | _, [] => ⟨rfl, rfl, rfl⟩
  | bm, (i, e) :: r => by
    rcases e with ⟨k, len⟩
    cases k with
    | heap pe h t path i0 m k cap =>
      by_cases hk : k + 1 = 2 ^ m
      · obtain ⟨h1, h2, h3⟩ := tlvsFrom_shape st (bm + 2 ^ m) r
        simp only [tlvsFrom, tlvAt, hk, ite_true, tN1, tN2, tlvM, tlvT, tlvC, List.map_cons, List.sum_cons,
          List.length_cons, List.length_map, List.length_range] at h1 h2 h3 ⊢
        omega
      · obtain ⟨h1, h2, h3⟩ := tlvsFrom_shape st bm r
        simp only [tlvsFrom, tlvAt, hk, ite_false, tN1, tN2, tlvM, tlvT, tlvC, List.map_cons, List.sum_cons] at h1 h2 h3 ⊢
        omega
    | _ =>
      obtain ⟨h1, h2, h3⟩ := tlvsFrom_shape st bm r
      simp only [tlvsFrom, tlvAt, tN1, tN2, tlvM, tlvT, tlvC, List.map_cons, List.sum_cons] at h1 h2 h3 ⊢
      omega

theorem map_snd_range_getD {β : Type} (f : Replay.PE → β) (L : List Replay.PE) :
    ((List.range L.length).map fun i => (i, L.getD i default)).map (fun x => f x.2) = L.map f := by
  apply List.ext_getElem (by simp)
  intro j h1 h2
  simp only [List.length_map, List.length_range] at h1
  simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h1]

/-- **The plan's heap levels at `P20B`** (one kernel evaluation of the plan): 512 layer nodes, 250 paths, 3
levels. -/
theorem planShapeB20 : ((Replay.plan P20B).map tlvM).sum = 512 ∧ ((Replay.plan P20B).map tlvT).sum = 250 ∧
    ((Replay.plan P20B).map tlvC).sum = 3 := by
  rw [show tlvM = bmOf from rfl, show tlvT = tlvTW from rfl, show tlvC = tlvCW from rfl]
  exact planW_B20.2.2

/-- **S2GB's tail shape**: 512 layer nodes (`2^8 + 2^7 + 2^7`), 250 paths, 3 levels. -/
theorem tlvB20_shape : tN1 tlvB20 = 512 ∧ tN2 tlvB20 = 250 ∧ tlvB20.length = 3 := by
  obtain ⟨h1, h2, h3⟩ := tlvsFrom_shape stB20 wB2M
    ((List.range (Replay.plan P20B).length).map fun i => (i, (Replay.plan P20B).getD i default))
  rw [map_snd_range_getD] at h1 h2 h3
  rw [tlvB20, h1, h2, h3]
  exact planShapeB20

/-- S2GB's chain length (the scan's table has `4 · 1051` words). -/
theorem nChainS_stB20 : nChainS stB20 = 1050 := by
  rw [Lvm.ASM.replayOKB_stB20.nc, Lvm.ASM.replayOKB_stB20.nm]

/-! ## The node output: cost, outputs, size -/

theorem cost_outIRBG (ls : List TLv) (st : XStage) (hst : OutOK st) (pz0 m t : ℕ) :
    cost (outIRBG ls st pz0 m) t ≤ 15800000 + 50 * tN1 ls + 33 * tN2 ls + 8 * ls.length + 20 := by
  have h1 := cost_segIR apC (pSegS st) 0 t
  have h2 := cost_segIR apC (trSegS st) 0 t
  have h3 := cost_segIR apC (.cp 0 597) 0 t
  have h4 := hst.cost
  have h5 := cost_rsigIR st m t
  have h6 := cost_bmIR t ls
  rw [segCost_pSegS] at h1; rw [segCost_trSegS] at h2; rw [show segCost (.cp 0 597) = 21506 from rfl] at h3
  simp only [outIRBG, cost, emitIR, setR, blkSteps, List.length_cons, List.length_nil, cost_sizeWIR, cost_tailIR,
    cost_tcpIR _ _ t (show 4 < 2 ^ 64 by norm_num), cost_tcpIR _ _ t (show 5 < 2 ^ 64 by norm_num),
    cost_tcpIR _ _ t (show 11 < 2 ^ 64 by norm_num), cost_leafStmtIR, cost_copyIR, nCp]
  norm_num
  (clear * - t h1 h2 h3 h4 h5 h6; omega)

theorem outs_outIRBG (ls : List TLv) (st : XStage) (hst : OutOK st) (pz0 m t : ℕ) :
    outs (outIRBG ls st pz0 m) t ≤ 164753 + 4 * tN1 ls := by
  have h1 := outs_segIR apC (pSegS st) 0 t
  have h2 := outs_segIR apC (trSegS st) 0 t
  have h3 := outs_segIR apC (.cp 0 597) 0 t
  have h4 := hst.outs
  have h5 := outs_rsigIR st m t
  rw [segOuts_pSegS] at h1; rw [segOuts_trSegS] at h2; rw [show segOuts (.cp 0 597) = 597 from rfl] at h3
  simp only [outIRBG, outs, emitIR, setR, outs_tcpIR _ _ t (show 4 < 2 ^ 64 by norm_num),
    outs_tcpIR _ _ t (show 5 < 2 ^ 64 by norm_num), outs_tcpIR _ _ t (show 11 < 2 ^ 64 by norm_num),
    outs_leafStmtIR, outs_bmIR, outs_sizeWIR, outs_tailIR, copyIR, copyBody, Nat.zero_add, Nat.add_zero]
  simp at h1 h2 h3 ⊢
  (clear * - t h1 h2 h3 h4 h5; omega)

theorem sizeIR_outIRBG (ls : List TLv) (st : XStage) (hst : OutOK st) (pz0 m : ℕ) :
    sizeIR (outIRBG ls st pz0 m) ≤ 2 ^ 18 - 2 ^ 10 + 52 * tN1 ls + 34 * tN2 ls + 8 * ls.length + 20 := by
  have h4 := hst.size
  have h5 := sizeIR_rsigIR st m
  have h6 := sizeIR_bmIR ls
  simp only [outIRBG, sizeIR, sizeIR_segIR, pSegS, trSegS, segSize, segPSsS, segTSsS, sizeIR_leafStmtIR,
    sizeIR_sizeWIR, sizeIR_tailIR]
  simp [emitIR, setR, tcpIR, tcpBody, copyIR, copyBody, cpAddrPs, sizeIR, blkSteps]
  (clear * - h4 h5 h6; omega)

theorem cost_outIRB (m t : ℕ) : cost (outIRB m) t ≤ 15800000 + 50 * 512 + 33 * 250 + 8 * 3 + 20 := by
  obtain ⟨n1, n2, n3⟩ := tlvB20_shape
  have h := cost_outIRBG tlvB20 stB20 outOK_stB20 (piStatic P20B) m t
  rw [n1, n2, n3] at h
  rw [outIRB_eq]; exact h

theorem outs_outIRB (m t : ℕ) : outs (outIRB m) t ≤ 164753 + 4 * 512 := by
  obtain ⟨n1, -, -⟩ := tlvB20_shape
  have h := outs_outIRBG tlvB20 stB20 outOK_stB20 (piStatic P20B) m t
  rw [n1] at h
  rw [outIRB_eq]; exact h

theorem sizeIR_outIRB (m : ℕ) : sizeIR (outIRB m) ≤ 2 ^ 18 - 2 ^ 10 + 52 * 512 + 34 * 250 + 8 * 3 + 20 := by
  obtain ⟨n1, n2, n3⟩ := tlvB20_shape
  have h := sizeIR_outIRBG tlvB20 stB20 outOK_stB20 (piStatic P20B) m
  rw [n1, n2, n3] at h
  rw [outIRB_eq]; exact h

/-! ## The SNARK branch: no tape loop after the chain, outputs, cost, size -/

theorem noLoopT_okL0B : NoLoopT okL0B :=
  ⟨trivial, trivial, ⟨noLoopT_streamS stB20, noLoopT_outIRB _⟩, trivial⟩
theorem noLoopT_okL1B : NoLoopT okL1B :=
  ⟨trivial, trivial, ⟨noLoopT_dec0S stB20, noLoopT_okL0B⟩, trivial⟩
theorem noLoopT_okL2B : NoLoopT okL2B :=
  ⟨trivial, trivial, ⟨noLoopT_dec1MPIR .., noLoopT_okL1B⟩, trivial⟩

theorem outs_decXB20 (t : ℕ) : outs decXB20 t ≤ outCap := by
  have h := outs_outIRB mBM t
  have h0 : outs (dec0S stB20) t = 0 := outs_dec0S stB20 t
  have hs : outs (streamS stB20) t = 0 := outs_streamS stB20 t
  have h1 : outs (decMP1IR dB1M wB1M aB1M fB1M fB0M) t = 0 := outs_dec1MPIR ..
  have h2 : outs (decMP2IR dB2M wB2M aB2M fB2M fB1M) t = 0 := outs_dec1MPIR ..
  simp only [decXB20, nodeB20, okL2B, okL1B, okL0B, hs, leafIR, readAt, outs, outs_idxIR4D, outs_readGIRD,
    read0B, read1B, read2B, outs_acpS, h0, h1, h2, emitIR, outs_thcpIRM,
    outs_tcpIR _ _ t (show 5 < 2 ^ 64 by norm_num),
    outs_chainIRD (nChainS stB20) t (chTabS stB20) (show outs sdL t = 0 by simp [sdL, outs])]
  generalize outs (outIRB mBM) t = o at h ⊢
  simp at *
  rw [outCap]; (clear * - t h; omega)

theorem cost_okL0B (t : ℕ) : cost okL0B t ≤ 22800000 := by
  have hO := cost_outIRB mBM t
  have hS := cost_streamS stB20 t
  simp only [okL0B, cost, blkSteps, List.length_cons, List.length_nil, Nat.max_def]
  split_ifs <;> omega

/-- The level reads' costs from the sent caps (18, 16, 13 levels). -/
theorem cost_read0B (t : ℕ) : cost read0B t ≤ 65916633102 := by
  have h : stB20.occ0 = 46 := rfl
  rw [read0B, cost_readGIRD _ _ _ _ _ _ _ t (by norm_num) (by norm_num) (by omega) (by omega), h]
  norm_num

theorem cost_read1B (t : ℕ) : cost read1B t = 7374241806 := by
  rw [read1B, cost_readGIRD _ _ _ _ _ _ _ t (by norm_num) (by norm_num) (by norm_num) (by norm_num)]
  norm_num

theorem cost_read2B (t : ℕ) : cost read2B t = 760905742 := by
  rw [read2B, cost_readGIRD _ _ _ _ _ _ _ t (by norm_num) (by norm_num) (by norm_num) (by norm_num)]
  norm_num

/-- **S2GB's SNARK branch's cost** (S2GS's bound `2^45 + t/5 · 11,895 + t · 168`). -/
theorem cost_decXB20 (t : ℕ) : cost decXB20 t ≤ 2 ^ 45 + t / 5 * 11895 + t * 168 := by
  have hC := cost_chainIRD (nChainS stB20) t (chTabS stB20) sdL
  rw [chTabS_length, cost_sdL] at hC
  have hN := nChainS_stB20
  have hD2 := cost_decMP2IR dB2M wB2M aB2M fB2M fB1M t
  have hD1 := cost_decMP1IR dB1M wB1M aB1M fB1M fB0M t
  have hD0 := cost_dec0S stB20 t
  have h0 := cost_okL0B t
  have hR0 := cost_read0B t
  have hR1 := cost_read1B t
  have hR2 := cost_read2B t
  simp only [decXB20, nodeB20, okL2B, okL1B, leafIR, readAt, cost, blkSteps, List.length_cons,
    List.length_nil, cost_idxIR4D, hC, hR1, hR2, cost_acpS, cost_tcpIR _ _ t (show 5 < 2 ^ 64 by norm_num),
    emitIR, cost_thcpIR _ _ _ t (show 3 * 2 ^ 9 < 2 ^ 64 by norm_num), Nat.max_def]
  split_ifs <;> omega

private theorem szBlkB (ps : List Prim) : sizeIR (.blk ps) = blkSteps ps.length := by rw [sizeIR]
private theorem szLoadB (d a : ℕ) : sizeIR (.load d a) = 1 := by rw [sizeIR]
private theorem szInputB (d a : ℕ) : sizeIR (.input d a) = 1 := by rw [sizeIR]
private theorem szSeqB (p q : XIR) : sizeIR (.seq p q) = sizeIR p + sizeIR q + 1 := by rw [sizeIR]
private theorem szIteB (c : ℕ) (p q : XIR) : sizeIR (.ite c p q) = sizeIR p + sizeIR q + 1 := by
  rw [sizeIR]

theorem sizeIR_decXB20 : sizeIR decXB20 ≤ 2 ^ 19 := by
  have h2 := sizeIR_dec2M
  have h1 := sizeIR_dec1M
  have h0 := sizeIR_dec0S stB20
  have hO := sizeIR_outIRB mBM
  have hS := sizeIR_streamS stB20
  have hN := nChainS_stB20
  have hA := sizeIR_acp3IR (ansB + 4 * foldPosS stB20 0 0) aB0M 6
  have hB := sizeIR_acp3IR (ansB + 4 * foldPosS stB20 1 0) aB1M 4
  have hC := sizeIR_acp3IR (ansB + 4 * foldPosS stB20 2 0) aB2M 4
  simp only [decXB20, nodeB20, okL2B, okL1B, okL0B, leafIR, readAt, emitIR, acpS, szBlkB, szLoadB, szInputB,
    szSeqB, szIteB, blkSteps, List.length_cons, List.length_nil, sizeIR_idxIR4D, sizeIR_chainIRD,
    chTabS_length, read0B, read1B, read2B, sizeIR_readGIRD, hA, hB, hC]
  simp only [tcpIR, tcpBody, thcpIR, thcpBody, sdL, sizeIR, blkSteps, List.length_cons, List.length_nil,
    Nat.zero_add, Nat.add_eq_zero_iff, one_ne_zero, and_false, ↓reduceIte]
  (clear * - h2 h1 h0 hO hS hN; omega)

/-! ## Safety -/

/-- **The SNARK branch's loop bounds** on every domain tape of an `S` proof in the size range: the dynamic walk and
chain simulate the static ones at the proof's log position (`Sim.safe`). -/
theorem safe_decXB20 (c : Digest) (π : Proof) (L : Log) (hhi : π.size ≤ hiB)
    (hq : ∀ e ∈ L, e.1.size < 2 ^ 64) (ht : (extractorInput c π L).length ≤ 2 ^ 64) :
    Safe (extractorInput c π L).toArray (extractorInput c π L).length decXB20 := by
  have hhi' : hiB = 285624 := hiB_val
  have hv : pLW (extractorInput c π L).toArray = BitVec.ofNat 64 (posL π.size) :=
    pLW_eq (by rw [getD_toArray, tape_getD4]) (by omega)
  have hs := hs_posL (pz := π.size) (π := π) rfl
  refine .seq (safe_of_noLoopT (by simp [readAt, NoLoopT])) (.ite ?_ (safe_of_noLoopT
    ⟨noLoopT_emitIR _, noLoopT_tcpIR _ _⟩))
  refine .seq ((idxIR4D_sim hv memM).safe (safe_idxIR4 _ _ (by rw [← hs]; have := tape_length c π L; omega)
    (tape_count_le4 c π L hs ht)) (wf_idxIR4 _ _))
    (.seq ?_ (.seq (safe_of_noLoopT (noLoopT_readGIRD ..)) (.seq (safe_of_noLoopT (noLoopT_readGIRD ..))
      (.seq (safe_of_noLoopT (noLoopT_readGIRD ..)) (.seq (safe_of_noLoopT (noLoopT_acpS stB20))
        (.seq (safe_of_noLoopT (noLoopT_thcpIR ..)) (.seq (safe_of_noLoopT (noLoopT_dec1MPIR ..))
          (safe_of_noLoopT noLoopT_okL2B))))))))
  exact (chainIRD_sim hv _ _ _).safe (safe_chainIR c π L hs hq ht _ _ noLoopT_sdL wf_sdL
    (nw_sdL _ (by decide) (by decide) (by decide))) (wf_chainIR _ _ _ wf_sdL (nw_sdL _ (by decide) (by decide) (by decide)))

/-! ## `DecOkB` -/

/-- **S2GB's SNARK branch meets `DecOkB`** on the size range `[loB, hiB]`. -/
theorem decOk_decXB20 : DecOkB loB hiB decXB20 where
  lo_lt := by simp only [loB, sizes_P20B.1.1]; norm_num
  hi_lt := by rw [hiB_val]; norm_num
  wf := wf_decXB20
  safe := fun c π L _ hh hq ht => safe_decXB20 c π L hh hq ht
  cost := fun t => by
    have := cost_decXB20 t
    simp only [decBudgetM, fuelBase, fuelPerWord]
    omega
  outs := outs_decXB20
  size := sizeIR_decXB20

end Lvm.XB
