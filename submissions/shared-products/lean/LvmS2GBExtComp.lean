-- New for lvm2 MP-B cap pruning (CAP-X, 2026-11-17): `Computes` for an extractor whose parse checks a size range
-- (`extIRWithB lo hi`; the ports of `DecOkM`, `halts_of_tapeM`, `computesWithM`, `run_W_tapeS`).
import LvmS2GBExtProg

/-!
# `Computes` with a size range

* `DecOkB lo hi dec`: `DecOkM` with the domain tapes of proofs of `lo ≤ |π| ≤ hi` bytes;
* **`computesWithB`**, `size_extWithB`, **`run_W_tapeB`** (a witness-sending tape copies π).
-/

set_option autoImplicit false

namespace Lvm.XB

open RecursionFast Lvm.X

/-! ## The parse -/

theorem wf_extIRWithB {lo hi : ℕ} {dec : XIR} (h : WF dec) : WF (extIRWithB lo hi dec) := by
  simp only [extIRWithB, parseIRB, readAt, kindPsB, wIR, wPre, wCntPs, wBody, WF, Writes, Prim.dst,
    List.mem_cons, List.mem_nil_iff, rA, rLen, rK, rCnt, rT, rW, rPos, rC, rB0, rIsK, rIsSz, regs,
    cTmp, cOne]
  refine ⟨?_, ?_⟩ <;> simp_all

theorem cost_extIRWithB (lo hi : ℕ) (dec : XIR) (t : ℕ) :
    cost (extIRWithB lo hi dec) t = 31 + max (max (cost dec t) 1 + 1) (23 + 8 * t) := by
  simp only [extIRWithB, parseIRB, readAt, kindPsB, wIR, wPre, wCntPs, wBody, cost, blkSteps,
    List.length_cons, List.length_nil, Aff.eval, Nat.div_one]
  norm_num; (clear * - dec t; omega)

theorem sizeIR_extIRWithB (lo hi : ℕ) (dec : XIR) : sizeIR (extIRWithB lo hi dec) = 63 + sizeIR dec := by
  simp only [extIRWithB, parseIRB, readAt, kindPsB, wIR, wPre, wCntPs, wBody, sizeIR, blkSteps,
    List.length_cons, List.length_nil]
  norm_num; (clear * - dec; omega)

theorem parseB_o (lo hi : ℕ) (I : Array Word) (s : St) : (semXIR I (parseIRB lo hi) s).o = s.o := by
  simp [parseIRB, readAt, semXIR]

theorem safe_parseIRB (lo hi : ℕ) (I : Array Word) (t : ℕ) : Safe I t (parseIRB lo hi) :=
  .seq (.seq (.blk _) (.input _ _)) (.seq (.seq (.blk _) (.input _ _)) (.blk _))

theorem parseB_isK (lo hi : ℕ) (I : Array Word) (s : St) (hM : Lvm.X.Inv s.M) :
    Lvm.X.rd (semXIR I (parseIRB lo hi) s).M rIsK = (if I.getD 5 0 &&& 0xFF = kindS then 1 else 0) := by
  have hs := hM.1
  simp only [regs] at hs
  simp only [parseIRB, readAt, kindPsB, semXIR, runPrims, List.foldl, Prim.run, rA, rLen, rK, rB0,
    rIsK, rT, rIsSz]
  simp (disch := first | decide | (clear * - s hs; omega) | (simp only [size_set]; (clear * - s hs; omega)))
    [rd_set_self, rd_set_ne, XOp.eval]

/-- **The size flag**: on a tape whose word 4 is `a < 2^64`, `rIsSz ≠ 0` iff `lo ≤ a ≤ hi` (`lo, hi < 2^64`). -/
theorem parseB_sz (lo hi : ℕ) (hlo : lo < 2 ^ 64) (hhi : hi < 2 ^ 64) (I : Array Word) (s : St) (hM : Lvm.X.Inv s.M)
    {a : ℕ} (ha : a < 2 ^ 64) (h4 : I.getD 4 0 = toWord a) :
    Lvm.X.rd (semXIR I (parseIRB lo hi) s).M rIsSz ≠ 0 ↔ lo ≤ a ∧ a ≤ hi := by
  have hs := hM.1
  simp only [regs] at hs
  simp only [parseIRB, readAt, kindPsB, semXIR, runPrims, List.foldl, Prim.run, rA, rLen, rK, rB0,
    rIsK, rT, rIsSz]
  simp (disch := first | decide | (clear * - s hs; omega) | (simp only [size_set]; (clear * - s hs; omega)))
    [rd_set_self, rd_set_ne, XOp.eval]
  have h4' : I[4]?.getD 0#64 = toWord a := by rw [← h4, Array.getD_eq_getD_getElem?]; rfl
  rw [h4', BitVec.le_def, BitVec.le_def, toNat_toWord ha, BitVec.toNat_ofNat, BitVec.toNat_ofNat,
    Nat.mod_eq_of_lt hlo, Nat.mod_eq_of_lt hhi]

/-! ## The obligations and `Computes` -/

/-- **The obligations on a SNARK branch** whose parse checks `lo ≤ |π| ≤ hi` (`DecOkM`'s, budget `decBudgetM`). -/
structure DecOkB (lo hi : ℕ) (dec : XIR) : Prop where
  lo_lt : lo < 2 ^ 64
  hi_lt : hi < 2 ^ 64
  wf : WF dec
  safe : ∀ c (π : Proof) (L : Log), lo ≤ π.size → π.size ≤ hi → (∀ e ∈ L, e.1.size < 2 ^ 64) →
    (extractorInput c π L).length ≤ 2 ^ 64 →
    Safe (extractorInput c π L).toArray (extractorInput c π L).length dec
  cost : ∀ t, cost dec t ≤ decBudgetM t
  outs : ∀ t, outs dec t ≤ outCap
  size : sizeIR dec ≤ 2 ^ 19

theorem fuel_coversB {lo hi : ℕ} {dec : XIR} (h : ∀ t, cost dec t ≤ decBudgetM t) (t : ℕ) :
    memM + mpwX * t + cost (extIRWithB lo hi dec) t + 8 ≤ fuel t := by
  have := h t
  rw [cost_extIRWithB]
  simp only [memM, mpwX, fuel, fuelBase, fuelPerWord, decBudgetM] at *
  (clear * - this; omega)

theorem size_extWithB {lo hi : ℕ} {dec : XIR} (h : sizeIR dec ≤ 2 ^ 19) :
    (toProg memM mpwX (extIRWithB lo hi dec)).body.size ≤ progCap := by
  simp only [toProg, size_compile, sizeIR, sizeIR_extIRWithB, initPs, blkSteps,
    List.length_cons, List.length_nil, progCap]
  norm_num; (clear * - dec h; omega)

theorem halts_of_tapeB {lo hi : ℕ} {dec : XIR} (hd : DecOkB lo hi dec) (inp : List Word) (a : ℕ)
    (ha : a ≤ 8 * outCap)
    (h4 : inp.toArray.getD 4 0 = toWord a) (hlen : (a + 7) / 8 + 6 ≤ inp.length)
    (hsafe : lo ≤ a → a ≤ hi → Safe inp.toArray inp.length dec) :
    ∃ o, (toProg memM mpwX (extIRWithB lo hi dec)).run inp (fuel inp.length) = some o ∧ o.length ≤ outCap := by
  rw [outCap] at ha
  have hwf := wf_extIRWithB (lo := lo) (hi := hi) hd.wf
  have hreg : regs ≤ memM := by simp only [regs, memM]; norm_num
  have h0 : Lvm.X.Inv (initSt (memM + mpwX * inp.length)).M := inv_initSt (Nat.le_add_right_of_le hreg)
  generalize hs0 : initSt (memM + mpwX * inp.length) = s0 at h0
  generalize hI : inp.toArray = I at h4 hsafe
  have h1 : Lvm.X.Inv (semXIR I (parseIRB lo hi) s0).M := inv_sem I hwf.1 h0
  have hpi : Lvm.X.rd (semXIR I (parseIRB lo hi) s0).M rIsSz ≠ 0 → lo ≤ a ∧ a ≤ hi :=
    (parseB_sz lo hi hd.lo_lt hd.hi_lt I s0 h0 (by (clear * - ha; omega)) h4).1
  have hpo : (semXIR I (parseIRB lo hi) s0).o = #[] := by rw [parseB_o, ← hs0, initSt_o]
  generalize hs1 : semXIR I (parseIRB lo hi) s0 = s1 at h1 hpi hpo
  have hB : BoundsOk I inp.length (extIRWithB lo hi dec) s0 := by
    rw [extIRWithB, boundsOk_seq]
    refine ⟨boundsOk_of_safe (safe_parseIRB lo hi _ _) hwf.1 _ h0, ?_⟩
    rw [hs1, boundsOk_ite]
    by_cases hk : Lvm.X.rd s1.M rIsK = 0
    · rw [if_pos hk]
      exact boundsOk_of_safe (safe_wIR (by (clear * - ha; omega)) h4 (by (clear * - hlen; omega))) hwf.2.2 _ h1
    · rw [if_neg hk, boundsOk_ite]
      by_cases hz : Lvm.X.rd s1.M rIsSz = 0
      · rw [if_pos hz]; trivial
      · rw [if_neg hz]
        exact boundsOk_of_safe (hsafe (hpi hz).1 (hpi hz).2) hd.wf _ h1
  have hrun := run_toProg (P := extIRWithB lo hi dec) (input := inp) (f := fuel inp.length) hreg hwf
    (by rw [hs0, hI]; exact hB) (fuel_coversB hd.cost _)
  rw [hs0, hI] at hrun
  refine ⟨_, hrun, ?_⟩
  by_cases hk : Lvm.X.rd s1.M rIsK = 0
  · have e : semXIR I (extIRWithB lo hi dec) s0 = semXIR I wIR s1 := by
      rw [extIRWithB, semXIR_seq, hs1, semXIR_ite, if_pos hk]
    have hw : (ceil8 (I.getD 4 0)).toNat = (a + 7) / 8 := by rw [h4, toNat_ceil8 (by (clear * - ha; omega))]
    have := congrArg List.length ((congrArg (fun s' : St => s'.o.toList) e).trans
      (wIR_sem I _ h1 (by (clear * - ha hw; omega))))
    simp only [hpo, hw, Array.toList_empty, List.nil_append, List.length_map,
      List.length_range] at this
    rw [this, outCap]
    (clear * - ha hw this; omega)
  · by_cases hz : Lvm.X.rd s1.M rIsSz = 0
    · have e : semXIR I (extIRWithB lo hi dec) s0 = semXIR I (.blk []) s1 := by
        rw [extIRWithB, semXIR_seq, hs1, semXIR_ite, if_neg hk, semXIR_ite, if_pos hz]
      have hl : (semXIR I (extIRWithB lo hi dec) s0).o.toList.length = 0 := by
        rw [e]; simp [semXIR, hpo]
      rw [hl]; exact Nat.zero_le _
    · have e : semXIR I (extIRWithB lo hi dec) s0 = semXIR I dec s1 := by
        rw [extIRWithB, semXIR_seq, hs1, semXIR_ite, if_neg hk, semXIR_ite, if_neg hz]
      have := outs_le (I := I) inp.length dec _ hd.wf h1
        (boundsOk_of_safe (hsafe (hpi hz).1 (hpi hz).2) hd.wf _ h1)
      rw [hpo, ← e] at this
      have h2 := hd.outs inp.length
      simp only [Array.size_empty, Nat.zero_add] at this
      rw [Array.length_toList]; exact this.trans h2

/-- **`Computes` with a size range.** -/
theorem computesWithB {lo hi : ℕ} {dec : XIR} (hd : DecOkB lo hi dec) :
    Computes (toProg memM mpwX (extIRWithB lo hi dec)) (Eden memM mpwX (extIRWithB lo hi dec)) fuel :=
  computes_Eof fuel (by simp only [regs, memM]; norm_num) (wf_extIRWithB (lo := lo) (hi := hi) hd.wf)
    fun c π L h1 h2 h3 => halts_of_tapeB hd _ π.size h1 (by rw [getD_toArray, tape_getD4])
      (tape_length c π L) fun hl hh => hd.safe c π L hl hh h2 h3

/-- **A witness-sending tape copies π** (`run_W_tapeS` with the size range, `0 < lo`). -/
theorem run_W_tapeB {lo hi : ℕ} {dec : XIR} (hd : DecOkB lo hi dec) (hlo : 0 < lo) (inp : List Word) (a : ℕ)
    (ha : a < 2 ^ 64) (h4 : inp.toArray.getD 4 0 = toWord a) (hlen : (a + 7) / 8 + 6 ≤ inp.length)
    (hk : a ≠ 0 → ¬ (inp.toArray.getD 5 0 &&& 0xFF = kindS)) :
    (toProg memM mpwX (extIRWithB lo hi dec)).run inp (fuel inp.length) =
      some ((List.range ((a + 7) / 8)).map fun j => inp.toArray.getD (5 + j) 0) := by
  have hwf := wf_extIRWithB (lo := lo) (hi := hi) hd.wf
  have hreg : regs ≤ memM := by simp only [regs, memM]; norm_num
  have h0 : Lvm.X.Inv (initSt (memM + mpwX * inp.length)).M := inv_initSt (Nat.le_add_right_of_le hreg)
  generalize hs0 : initSt (memM + mpwX * inp.length) = s0 at h0
  generalize hI : inp.toArray = I at h4 hk ⊢
  have h1 : Lvm.X.Inv (semXIR I (parseIRB lo hi) s0).M := inv_sem I hwf.1 h0
  have hz0 : a = 0 → Lvm.X.rd (semXIR I (parseIRB lo hi) s0).M rIsSz = 0 := by
    intro h
    by_contra hne
    have := ((parseB_sz lo hi hd.lo_lt hd.hi_lt I s0 h0 ha h4).1 hne).1
    omega
  have hk' : a ≠ 0 → Lvm.X.rd (semXIR I (parseIRB lo hi) s0).M rIsK = 0 := fun h => by
    rw [parseB_isK _ _ I s0 h0, if_neg (hk h)]
  have hpo : (semXIR I (parseIRB lo hi) s0).o = #[] := by rw [parseB_o, ← hs0, initSt_o]
  have hw : (ceil8 (I.getD 4 0)).toNat = (a + 7) / 8 := by rw [h4, toNat_ceil8 ha]
  generalize hs1 : semXIR I (parseIRB lo hi) s0 = s1 at h1 hz0 hk' hpo
  have hB : BoundsOk I inp.length (extIRWithB lo hi dec) s0 := by
    rw [extIRWithB, boundsOk_seq]
    refine ⟨boundsOk_of_safe (safe_parseIRB _ _ _ _) hwf.1 _ h0, ?_⟩
    rw [hs1, boundsOk_ite]
    by_cases hk1 : Lvm.X.rd s1.M rIsK = 0
    · rw [if_pos hk1]
      exact boundsOk_of_safe (safe_wIR ha h4 (by (clear * - a inp hlen I hw; omega))) hwf.2.2 _ h1
    · have ha0 : a = 0 := by by_contra h; exact hk1 (hk' h)
      rw [if_neg hk1, boundsOk_ite, if_pos (hz0 ha0)]; trivial
  have hrun := run_toProg (P := extIRWithB lo hi dec) (input := inp) (f := fuel inp.length) hreg hwf
    (by rw [hs0, hI]; exact hB) (fuel_coversB hd.cost _)
  rw [hs0, hI] at hrun
  refine hrun.trans (congrArg some ?_)
  by_cases hk1 : Lvm.X.rd s1.M rIsK = 0
  · have e : semXIR I (extIRWithB lo hi dec) s0 = semXIR I wIR s1 := by
      rw [extIRWithB, semXIR_seq, hs1, semXIR_ite, if_pos hk1]
    rw [congrArg (fun s' : St => s'.o.toList) e, wIR_sem I _ h1 (by (clear * - I inp a ha hw; omega)), hpo, hw]
    rfl
  · have ha0 : a = 0 := by by_contra h; exact hk1 (hk' h)
    have e : semXIR I (extIRWithB lo hi dec) s0 = semXIR I (.blk []) s1 := by
      rw [extIRWithB, semXIR_seq, hs1, semXIR_ite, if_neg hk1, semXIR_ite, if_pos (hz0 ha0)]
    rw [congrArg (fun s' : St => s'.o.toList) e, ha0]
    simp [semXIR, hpo]

end Lvm.XB
