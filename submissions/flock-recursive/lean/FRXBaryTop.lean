-- New for `flock-recursive` (BLUEPRINT §6.2 step 4; stage S-H2, track L-ext).
import FRXBary

/-!
# The barycentric interpolation on the machine: one target, the target loop, `baryIR_sem`

On top of `FRXBary`'s loops (`eLoop_sem`, `cLoop_sem`) and tables (`djIR_sem`, `wtIR_sem`):

* `sBody_sem`: one target `s₀`: `out[c][s₀] = (ℓ = 0 ? y_c(s₀) : ℓ Σ_t y_c(J_t) E[t])`;
* `sLoop_sem`: every target `s < k`;
* **`baryIR_sem`**: the whole program, `out[c][s] = baryVal Jl k s y_c`, hence (`baryVal_eq`)
  `interpF D Jl.toFinset y_c s` (`baryIR_interp`).
-/

namespace FR.X

open RecursionFast FR Finset

/-! ## The flag `[ℓ = 0]` -/

theorem or_eq_zero_w (a b : Word) : XOp.or.eval a b = 0 ↔ a = 0 ∧ b = 0 := by
  constructor
  · intro h
    refine ⟨BitVec.eq_of_getLsbD_eq fun i hi => ?_, BitVec.eq_of_getLsbD_eq fun i hi => ?_⟩ <;>
    · have := congrArg (fun x : Word => x.getLsbD i) h
      rw [show (0 : Word) = 0#64 from rfl] at this
      simp only [XOp.eval, BitVec.getLsbD_or, BitVec.getLsbD_zero, Bool.or_eq_false_iff] at this
      simp [this]
  · rintro ⟨rfl, rfl⟩; rfl

/-- **The zero test of an `F` pair**: `[(a ||| b) = 0] = [⟨a, b⟩ = 0]`. -/
theorem eqz_or (a b : Word) :
    XOp.eq.eval (XOp.or.eval a b) 0 = bW (decide ((⟨wB a, wB b⟩ : F) = 0)) := by
  rw [eq_bW]
  congr 1
  apply decide_eq_decide.mpr
  rw [or_eq_zero_w]
  constructor
  · rintro ⟨rfl, rfl⟩; rfl
  · intro h
    have h' : (⟨wB a, wB b⟩ : F) = ⟨⟨0⟩, ⟨0⟩⟩ := h
    simp only [F.mk.injEq, wB, B64.mk.injEq] at h'
    exact ⟨congrArg UInt64.toBitVec h'.1, congrArg UInt64.toBitVec h'.2⟩

/-! ## One target -/

theorem wf_sBody (k C jb djb wb eb cb cs ob tb : ℕ) : WF (sBody k C jb djb wb eb cb cs ob tb) := by
  simp [sBody, eBody, cBody, aBody, yIR, addrPs, alphaIR, alphaBody, ldF, stF, WF, Writes,
    Prim.dst, bnw_mulF, bnw_addF, bnw_invF, wfF_mul, wfF_add, wfF_inv, fDs, fLp, fDd, fIv, fEt,
    fPr, fY, fAc, fX, bT, bS, bCi, bA, bA1, bJ, bK, bZ, bC2, bN2, bC3, bN3, bCo, rBs, rTr, rTa,
    rTa1, rBit, uI, uT1, fG, fAl, rC2, rN2, cTmp, regs]

theorem nw_eBody_bS (djb wb eb : ℕ) : ¬ Writes (eBody djb wb eb) bS := by
  simp [eBody, addrPs, ldF, stF, Writes, Prim.dst, bnw_mulF, bnw_addF, bnw_invF, bA, bK, bA1, fX,
    fDd, fLp, fIv, fEt, bT, bS, cTmp]

theorem nw_cBody_bS (k jb eb cb cs ob : ℕ) : ¬ Writes (cBody k jb eb cb cs ob) bS := by
  simp [cBody, aBody, yIR, addrPs, ldF, stF, Writes, Prim.dst, bnw_mulF, bnw_addF, bA, bK, bA1,
    bJ, fY, fX, fPr, fAc, bT, bN3, bC3, bCi, bCo, cTmp, bS]

theorem nw_alphaIR_bS : ¬ Writes alphaIR bS := by
  simp [alphaIR, alphaBody, ldF, Writes, Prim.dst, rBit, uT1, rTa, rTa1, fG, fAl, uI, rN2, rC2,
    cTmp, bS]

/-- **One target `s₀`**: the `C` output cells of `s₀`, `bS := s₀ + 1`; the heap outside the `E`
row and those cells is kept. -/
theorem sBody_sem (I : Array Word) (s : St) (hM : Inv s.M)
    {k C jb djb wb eb cb cs ob tb s0 : ℕ} {x : ℕ → ℕ}
    (hk : k < 2 ^ 64) (hC : C < 2 ^ 62) (hs0 : s0 < k) (hs0n : s0 < nMax)
    (hjb : regs ≤ jb) (hdjb : regs ≤ djb) (hwb : regs ≤ wb) (heb : regs ≤ eb) (hcb : regs ≤ cb)
    (hob : regs ≤ ob) (htb : regs ≤ tb)
    (hjb2 : jb + k < 2 ^ 64) (hdj2 : djb + 2 * k < 2 ^ 64) (hwb2 : wb + 2 * k < 2 ^ 64)
    (heb2 : eb + 2 * k < 2 ^ 64) (htb2 : tb + 40 < 2 ^ 64)
    (hcb2 : ∀ t < k, ∀ c < C, cb + cs * x t + 2 * c + 1 < 2 ^ 64)
    (hcs2 : ∀ c < C, cb + cs * s0 + 2 * c + 1 < 2 ^ 64)
    (hob2 : ob + 2 * k * C < 2 ^ 64) (hsz : ob + 2 * k * C ≤ s.M.size)
    (hszE : eb + 2 * k ≤ s.M.size)
    (hdE : djb + 2 * k ≤ eb ∨ eb + 2 * k ≤ djb) (hwE : wb + 2 * k ≤ eb ∨ eb + 2 * k ≤ wb)
    (hJE : jb + k ≤ eb ∨ eb + 2 * k ≤ jb)
    (hOJ : ob + 2 * k * C ≤ jb ∨ jb + k ≤ ob) (hOE : ob + 2 * k * C ≤ eb ∨ eb + 2 * k ≤ ob)
    (hOY : ∀ c < C, ∀ j, j ∈ (List.range k).map x ∨ j = s0 →
      (ob + 2 * k * C ≤ cb + cs * j + 2 * c ∨ cb + cs * j + 2 * c + 2 ≤ ob) ∧
      (eb + 2 * k ≤ cb + cs * j + 2 * c ∨ cb + cs * j + 2 * c + 2 ≤ eb))
    (hS : rd s.M bS = toWord s0)
    (hT : ∀ i < 20, rdF s.M (tb + 2 * i) = (wRow D logNMax 0).getD i 0)
    (hJ : ∀ t < k, rd s.M (jb + t) = toWord (x t)) :
    (∀ c < C, rdF (semXIR I (sBody k C jb djb wb eb cb cs ob tb) s).M (ob + 2 * k * c + 2 * s0) =
      (if ∏ t ∈ range k, (D s0 + rdF s.M (djb + 2 * t)) = 0 then rdF s.M (cb + cs * s0 + 2 * c)
       else (∏ t ∈ range k, (D s0 + rdF s.M (djb + 2 * t))) *
        ∑ t ∈ range k, rdF s.M (cb + cs * x t + 2 * c) *
          (rdF s.M (wb + 2 * t) * (D s0 + rdF s.M (djb + 2 * t))⁻¹))) ∧
    rd (semXIR I (sBody k C jb djb wb eb cb cs ob tb) s).M bS = toWord (s0 + 1) ∧
    (∀ y, regs ≤ y → (y < eb ∨ eb + 2 * k ≤ y) →
      (∀ c < C, y ≠ ob + 2 * k * c + 2 * s0 ∧ y ≠ ob + 2 * k * c + 2 * s0 + 1) →
      rd (semXIR I (sBody k C jb djb wb eb cb cs ob tb) s).M y = rd s.M y) ∧
    Inv (semXIR I (sBody k C jb djb wb eb cb cs ob tb) s).M := by
  have hs := hM.1
  rw [sBody]
  simp only [semXIR_seq]
  -- `rBs := s₀`, `rTr := tb`
  have hM0 := inv_sem I (P := .blk [.op .or rBs bS bS, .const rTr (toWord tb)]) (s := s)
    (by simp [WF, Prim.dst, rBs, rTr]) hM
  have H0 := hframe I (.blk [.op .or rBs bS bS, .const rTr (toWord tb)]) s
    (by simp [Lo, Prim.dst, regs, rBs, rTr])
  have r0 : rd (semXIR I (.blk [.op .or rBs bS bS, .const rTr (toWord tb)]) s).M rBs = toWord s0 ∧
      rd (semXIR I (.blk [.op .or rBs bS bS, .const rTr (toWord tb)]) s).M rTr = toWord tb ∧
      rd (semXIR I (.blk [.op .or rBs bS bS, .const rTr (toWord tb)]) s).M bS = toWord s0 := by
    simp only [semXIR, runPrims, List.foldl, Prim.run]
    refine ⟨?_, ?_, ?_⟩ <;>
    simp (disch := first | decide | ((try simp only [size_set]); exact lt_of_lt_of_le (by decide) hs))
      only [rd_set_self, rd_set_ne]
    · rw [hS, or_self_eval]
    · exact hS
  have z0 := size_sem I (.blk [.op .or rBs bS bS, .const rTr (toWord tb)]) s
  generalize semXIR I (.blk [.op .or rBs bS bS, .const rTr (toWord tb)]) s = q0 at hM0 H0 r0 z0 ⊢
  -- `fAl := D(s₀)`
  have a1 := alphaD_sem I q0 hM0 hs0n htb htb2 r0.1 r0.2.1 fun i hi => by
    rw [rdF_eq (H0 _ (by simp only [regs] at htb ⊢; omega)) (H0 _ (by simp only [regs] at htb ⊢; omega))]
    exact hT i hi
  have hM1 := inv_sem I wf_alphaIR hM0
  have H1 := hframeK I alphaIR q0 loK_alphaIR
  have r1 : rd (semXIR I alphaIR q0).M bS = toWord s0 :=
    (frame I alphaIR q0 wf_alphaIR hM0 bS (by decide) nw_alphaIR_bS).trans r0.2.2
  have z1 := size_sem I alphaIR q0
  generalize semXIR I alphaIR q0 = q1 at a1 hM1 H1 r1 z1 ⊢
  -- `fDs := D(s₀)`, `ℓ := 1`, `t := 0`, `bN2 := k`
  have hM2 := inv_sem I (P := .blk [.op .or fDs fAl fAl, .op .or (fDs + 1) (fAl + 1) (fAl + 1),
    .const fLp 1, .const (fLp + 1) 0, .const bT 0, .const bN2 (toWord k)]) (s := q1)
    (by simp [WF, Prim.dst, fDs, fLp, bT, bN2]) hM1
  have H2 := hframe I (.blk [.op .or fDs fAl fAl, .op .or (fDs + 1) (fAl + 1) (fAl + 1),
    .const fLp 1, .const (fLp + 1) 0, .const bT 0, .const bN2 (toWord k)]) q1
    (by simp [Lo, Prim.dst, regs, fDs, fLp, bT, bN2])
  have hs1 : regs ≤ q1.M.size := hM1.1
  have r2 : rdF (semXIR I (.blk [.op .or fDs fAl fAl, .op .or (fDs + 1) (fAl + 1) (fAl + 1),
        .const fLp 1, .const (fLp + 1) 0, .const bT 0, .const bN2 (toWord k)]) q1).M fDs = D s0 ∧
      rdF (semXIR I (.blk [.op .or fDs fAl fAl, .op .or (fDs + 1) (fAl + 1) (fAl + 1),
        .const fLp 1, .const (fLp + 1) 0, .const bT 0, .const bN2 (toWord k)]) q1).M fLp = 1 ∧
      rd (semXIR I (.blk [.op .or fDs fAl fAl, .op .or (fDs + 1) (fAl + 1) (fAl + 1),
        .const fLp 1, .const (fLp + 1) 0, .const bT 0, .const bN2 (toWord k)]) q1).M bT =
        toWord 0 ∧
      rd (semXIR I (.blk [.op .or fDs fAl fAl, .op .or (fDs + 1) (fAl + 1) (fAl + 1),
        .const fLp 1, .const (fLp + 1) 0, .const bT 0, .const bN2 (toWord k)]) q1).M bN2 =
        toWord k ∧
      rd (semXIR I (.blk [.op .or fDs fAl fAl, .op .or (fDs + 1) (fAl + 1) (fAl + 1),
        .const fLp 1, .const (fLp + 1) 0, .const bT 0, .const bN2 (toWord k)]) q1).M bS =
        toWord s0 := by
    simp only [semXIR, runPrims, List.foldl, Prim.run, rdF, rdB]
    refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;>
    simp (disch := first | decide | ((try simp only [size_set]); exact lt_of_lt_of_le (by decide) hs1))
      only [rd_set_self, rd_set_ne]
    · rw [or_self_eval, or_self_eval, ← a1]; rfl
    · exact F_one_w
    · rfl
    · exact r1
  have z2 := size_sem I (.blk [.op .or fDs fAl fAl, .op .or (fDs + 1) (fAl + 1) (fAl + 1),
    .const fLp 1, .const (fLp + 1) 0, .const bT 0, .const bN2 (toWord k)]) q1
  generalize semXIR I (.blk [.op .or fDs fAl fAl, .op .or (fDs + 1) (fAl + 1) (fAl + 1),
    .const fLp 1, .const (fLp + 1) 0, .const bT 0, .const bN2 (toWord k)]) q1 = q2
    at hM2 H2 r2 z2 ⊢
  -- the heap of `q2` is `s`'s
  have Hq2 : ∀ y, regs ≤ y → rd q2.M y = rd s.M y := fun y hy =>
    (H2 y hy).trans ((H1 y hy).trans (H0 y hy))
  have Fq2 : ∀ y, regs ≤ y → rdF q2.M y = rdF s.M y := fun y hy =>
    rdF_eq (Hq2 y hy) (Hq2 (y + 1) (by omega))
  -- the `E` row and `ℓ`
  obtain ⟨e1, e2, e3, e4, hM3⟩ := eLoop_sem I q2 hM2 (k := k) (djb := djb) (wb := wb) (eb := eb)
    hk hdjb hwb heb hdj2 hwb2 heb2 (by rw [z2, z1, z0]; exact hszE) hdE hwE r2.2.2.2.1 r2.2.2.1
    r2.1 r2.2.1
  have z3 := size_sem I (.loopK bC2 bN2 (toWord k) (eBody djb wb eb)) q2
  have r3 : rd (semXIR I (.loopK bC2 bN2 (toWord k) (eBody djb wb eb)) q2).M bS = toWord s0 :=
    (e4 bS (by decide) (by decide) (by decide) (nw_eBody_bS djb wb eb)).trans r2.2.2.2.2
  generalize semXIR I (.loopK bC2 bN2 (toWord k) (eBody djb wb eb)) q2 = q3
    at e1 e2 e3 e4 hM3 z3 r3 ⊢
  -- the flag, `c := 0`, `2c := 0`, `bN2 := C`
  have hM4 := inv_sem I (P := .blk [.op .or bZ fLp (fLp + 1), .const bK 0, .op .eq bZ bZ bK,
    .const bCi 0, .const bCo 0, .const bN2 (toWord C)]) (s := q3)
    (by simp [WF, Prim.dst, bZ, bK, bCi, bCo, bN2]) hM3
  have H4 := hframe I (.blk [.op .or bZ fLp (fLp + 1), .const bK 0, .op .eq bZ bZ bK,
    .const bCi 0, .const bCo 0, .const bN2 (toWord C)]) q3
    (by simp [Lo, Prim.dst, regs, bZ, bK, bCi, bCo, bN2])
  have hs3 : regs ≤ q3.M.size := hM3.1
  have r4 : rd (semXIR I (.blk [.op .or bZ fLp (fLp + 1), .const bK 0, .op .eq bZ bZ bK,
        .const bCi 0, .const bCo 0, .const bN2 (toWord C)]) q3).M bN2 = toWord C ∧
      rd (semXIR I (.blk [.op .or bZ fLp (fLp + 1), .const bK 0, .op .eq bZ bZ bK,
        .const bCi 0, .const bCo 0, .const bN2 (toWord C)]) q3).M bCi = toWord 0 ∧
      rd (semXIR I (.blk [.op .or bZ fLp (fLp + 1), .const bK 0, .op .eq bZ bZ bK,
        .const bCi 0, .const bCo 0, .const bN2 (toWord C)]) q3).M bCo = toWord 0 ∧
      rd (semXIR I (.blk [.op .or bZ fLp (fLp + 1), .const bK 0, .op .eq bZ bZ bK,
        .const bCi 0, .const bCo 0, .const bN2 (toWord C)]) q3).M bS = toWord s0 ∧
      rdF (semXIR I (.blk [.op .or bZ fLp (fLp + 1), .const bK 0, .op .eq bZ bZ bK,
        .const bCi 0, .const bCo 0, .const bN2 (toWord C)]) q3).M fLp = rdF q3.M fLp ∧
      rd (semXIR I (.blk [.op .or bZ fLp (fLp + 1), .const bK 0, .op .eq bZ bZ bK,
        .const bCi 0, .const bCo 0, .const bN2 (toWord C)]) q3).M bZ =
        bW (decide (rdF q3.M fLp = 0)) := by
    simp only [semXIR, runPrims, List.foldl, Prim.run, rdF, rdB]
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    simp (disch := first | decide | ((try simp only [size_set]); exact lt_of_lt_of_le (by decide) hs3))
      only [rd_set_self, rd_set_ne]
    · rfl
    · rfl
    · exact r3
    · exact eqz_or _ _
  have z4 := size_sem I (.blk [.op .or bZ fLp (fLp + 1), .const bK 0, .op .eq bZ bZ bK,
    .const bCi 0, .const bCo 0, .const bN2 (toWord C)]) q3
  generalize semXIR I (.blk [.op .or bZ fLp (fLp + 1), .const bK 0, .op .eq bZ bZ bK,
    .const bCi 0, .const bCo 0, .const bN2 (toWord C)]) q3 = q4 at hM4 H4 r4 z4 ⊢
  -- the heap of `q4` is `s`'s off the `E` row
  have Hq4 : ∀ y, regs ≤ y → (y < eb ∨ eb + 2 * k ≤ y) → rd q4.M y = rd s.M y := fun y hy hy2 =>
    (H4 y hy).trans ((e3 y hy hy2).trans (Hq2 y hy))
  have Fq4 : ∀ y, regs ≤ y → (y + 1 < eb ∨ eb + 2 * k ≤ y) → rdF q4.M y = rdF s.M y :=
    fun y hy hy2 => rdF_eq (Hq4 y hy (by omega)) (Hq4 (y + 1) (by omega) (by omega))
  have hE4 : ∀ t < k, rdF q4.M (eb + 2 * t) =
      rdF s.M (wb + 2 * t) * (D s0 + rdF s.M (djb + 2 * t))⁻¹ := fun t ht => by
    rw [rdF_eq (H4 _ (by omega)) (H4 _ (by omega)), e1 t ht,
      Fq2 _ (by omega), Fq2 _ (by omega)]
  have hL4 : rdF q4.M fLp = ∏ t ∈ range k, (D s0 + rdF s.M (djb + 2 * t)) := by
    rw [r4.2.2.2.2.1, e2]
    exact Finset.prod_congr rfl fun t ht => by
      rw [Fq2 _ (by have := Finset.mem_range.1 ht; omega)]
  -- the coordinates
  obtain ⟨c1, c2, c3, hM5⟩ := cLoop_sem I q4 hM4 (k := k) (C := C) (jb := jb) (eb := eb) (cb := cb)
    (cs := cs) (ob := ob) (s0 := s0) (x := x) (lp := rdF q4.M fLp) hk hC hjb heb hcb hob hjb2
    heb2 hcb2 hcs2 hs0 hob2 (by rw [z4, z3, z2, z1, z0]; exact hsz) hOJ hOE
    (fun c hc j hj => (hOY c hc j hj).1) r4.1 r4.2.1 r4.2.2.1 r4.2.2.2.1 rfl
    (r4.2.2.2.2.2.trans (by rw [r4.2.2.2.2.1]))
    (fun t ht => by
      rw [Hq4 _ (by omega) (by rcases hJE with h | h <;> omega), hJ t ht])
  have r5 : rd (semXIR I (.loopK bC2 bN2 (toWord C) (cBody k jb eb cb cs ob)) q4).M bS =
      toWord s0 :=
    (c3 bS (by decide) (by decide) (by decide) (nw_cBody_bS k jb eb cb cs ob)).trans r4.2.2.2.1
  have z5 := size_sem I (.loopK bC2 bN2 (toWord C) (cBody k jb eb cb cs ob)) q4
  generalize semXIR I (.loopK bC2 bN2 (toWord C) (cBody k jb eb cb cs ob)) q4 = q5
    at c1 c2 c3 hM5 r5 z5 ⊢
  -- `s₀ += 1`
  obtain ⟨i1, i2⟩ := incr_sem q5.M hM5 (r := bS) (by decide) (by decide) r5
  have e6 : semXIR I (.blk [.op .add bS bS cOne]) q5 = ⟨runPrims [.op .add bS bS cOne] q5.M, q5.o⟩ :=
    rfl
  rw [e6]
  refine ⟨fun c hc => ?_, i1, fun y hy hy2 hy3 => ?_, inv_runPrims (by simp [Prim.dst, bS]) hM5⟩
  · rw [rdF_eq (i2 _ (by simp only [regs] at hob ⊢; simp only [bS]; omega))
      (i2 _ (by simp only [regs] at hob ⊢; simp only [bS]; omega)), c1 c hc, hL4]
    have hy' : ∀ j, j ∈ (List.range k).map x ∨ j = s0 →
        rdF q4.M (cb + cs * j + 2 * c) = rdF s.M (cb + cs * j + 2 * c) := fun j hj =>
      Fq4 _ (by omega) (by rcases (hOY c hc j hj).2 with h | h <;> omega)
    split_ifs
    · exact hy' s0 (.inr rfl)
    · refine congrArg (_ * ·) (Finset.sum_congr rfl fun t ht => ?_)
      have ht' := Finset.mem_range.1 ht
      rw [hy' (x t) (.inl (List.mem_map.2 ⟨t, List.mem_range.2 ht', rfl⟩)), hE4 t ht']
  · rw [i2 y (by simp only [regs] at hy; simp only [bS]; omega), c2 y hy hy3, Hq4 y hy hy2]

/-! ## The layout and the target loop -/

/-- **The interpolation's layout**, in increasing order: the basis table's row 0 (40 cells), the
list `J` (`k` words), `DJ`, `W`, `E` (`2k` each), the output rows (`2kC`), then the column store
from `cb` (`y_c(j)` at `cb + cs·j + 2c`). -/
structure BaryLay (k C jb djb wb eb cb ob tb : ℕ) : Prop where
  rt : regs ≤ tb
  tj : tb + 40 ≤ jb
  jd : jb + k ≤ djb
  dw : djb + 2 * k ≤ wb
  we : wb + 2 * k ≤ eb
  eo : eb + 2 * k ≤ ob
  oc : ob + 2 * k * C ≤ cb

/-- Distinct targets have disjoint output cells. -/
theorem cell_ne {k c c' s s' a b : ℕ} (hs : s < k) (hs' : s' < k) (hne : s ≠ s') (ha : a < 2)
    (hb : b < 2) : 2 * k * c + 2 * s + a ≠ 2 * k * c' + 2 * s' + b := by
  intro h
  have e1 : 2 * k * c = 2 * (k * c) := by ring
  have e2 : 2 * k * c' = 2 * (k * c') := by ring
  rw [e1, e2] at h
  have h2 : k * c + s = k * c' + s' := by omega
  have h3 : c = c' := by
    have := congrArg (· / k) h2
    rwa [Nat.mul_add_div (by omega), Nat.mul_add_div (by omega), Nat.div_eq_of_lt hs,
      Nat.div_eq_of_lt hs', add_zero, add_zero] at this
  subst h3; omega

theorem out_lt {k c C s : ℕ} (hc : c < C) (hs : s < k) : 2 * k * c + 2 * s + 1 < 2 * k * C := by
  have := Nat.mul_le_mul_left (2 * k) (show c + 1 ≤ C by omega); nlinarith

/-- The value of target `s₀`, coordinate `c`, on the heap `M` (the `DJ` and `W` tables and the
column store). -/
def sValM (M : Mem) (k djb wb cb cs : ℕ) (x : ℕ → ℕ) (s0 c : ℕ) : F :=
  if ∏ t ∈ range k, (D s0 + rdF M (djb + 2 * t)) = 0 then rdF M (cb + cs * s0 + 2 * c)
  else (∏ t ∈ range k, (D s0 + rdF M (djb + 2 * t))) *
    ∑ t ∈ range k, rdF M (cb + cs * x t + 2 * c) *
      (rdF M (wb + 2 * t) * (D s0 + rdF M (djb + 2 * t))⁻¹)

/-- **The target loop**: `out[c][s] = sValM s c` for every `s < k`, `c < C`; the heap outside
the `E` row and the output rows is kept. -/
theorem sLoop_sem (I : Array Word) (s : St) (hM : Inv s.M)
    {k C jb djb wb eb cb cs ob tb : ℕ} {x : ℕ → ℕ} (hL : BaryLay k C jb djb wb eb cb ob tb)
    (hk : k ≤ nMax) (hC : C < 2 ^ 62) (hc64 : cb < 2 ^ 64)
    (hcb2 : ∀ j < nMax, ∀ c < C, cb + cs * j + 2 * c + 1 < 2 ^ 64)
    (hsz : ob + 2 * k * C ≤ s.M.size) (hJn : ∀ t < k, x t < nMax)
    (hN : rd s.M bN1 = toWord k) (hS : rd s.M bS = toWord 0)
    (hT : ∀ i < 20, rdF s.M (tb + 2 * i) = (wRow D logNMax 0).getD i 0)
    (hJ : ∀ t < k, rd s.M (jb + t) = toWord (x t)) :
    (∀ s0 < k, ∀ c < C, rdF (semXIR I (.loopK bC1 bN1 (toWord k)
        (sBody k C jb djb wb eb cb cs ob tb)) s).M (ob + 2 * k * c + 2 * s0) =
      sValM s.M k djb wb cb cs x s0 c) ∧
    (∀ y, regs ≤ y → (y < eb ∨ eb + 2 * k ≤ y) → (y < ob ∨ ob + 2 * k * C ≤ y) →
      rd (semXIR I (.loopK bC1 bN1 (toWord k) (sBody k C jb djb wb eb cb cs ob tb)) s).M y =
        rd s.M y) ∧
    Inv (semXIR I (.loopK bC1 bN1 (toWord k) (sBody k C jb djb wb eb cb cs ob tb)) s).M := by
  obtain ⟨htb, htj, hjd, hdw, hwe, heo, hoc⟩ := hL
  have hnM : nMax = 2 ^ 20 := rfl
  have hk64 : k < 2 ^ 64 := by omega
  have hob2 : ob + 2 * k * C < 2 ^ 64 := by omega
  let Q : ℕ → St → Prop := fun j st => Inv st.M ∧ st.M.size = s.M.size ∧ rd st.M bS = toWord j ∧
    (∀ s0 < j, ∀ c < C, rdF st.M (ob + 2 * k * c + 2 * s0) = sValM s.M k djb wb cb cs x s0 c) ∧
    (∀ y, regs ≤ y → (y < eb ∨ eb + 2 * k ≤ y) → (y < ob ∨ ob + 2 * k * C ≤ y) →
      rd st.M y = rd s.M y)
  have ef : ∀ i, i ≠ bC1 → i ≠ cTmp → rd (entryK bC1 bN1 (toWord k) s.M) i = rd s.M i :=
    fun i a b => entryK_frame _ (Ne.symm a) (Ne.symm b)
  have h := loopK_run I (c := bC1) (n := bN1) (K := k) (sBody k C jb djb wb eb cb cs ob tb) Q s hM
    (by decide) (by decide) (by decide) hN hk64 ⟨inv_of_frame hM (size_entryK ..) fun i hi => ef i
      (by simp only [bC1]; omega) (by simp only [cTmp]; omega), size_entryK .., by
        rw [ef _ (by decide) (by decide), hS],
      fun s0 hs0 => absurd hs0 (Nat.not_lt_zero _),
      fun y hy _ _ => ef y (by simp only [regs, bC1] at hy ⊢; omega)
        (by simp only [regs, cTmp] at hy ⊢; omega)⟩ ?_
  · exact ⟨h.2.2.2.1, h.2.2.2.2, h.1⟩
  · rintro j st hj ⟨hM', hz, hS', hV, hH⟩
    simp only [regs] at htb
    have hF : ∀ y, 256 ≤ y → (y + 1 < eb ∨ ob + 2 * k * C ≤ y) → rdF st.M y = rdF s.M y :=
      fun y hy hy2 => rdF_eq (hH y (by simp only [regs]; omega) (by omega) (by omega))
        (hH (y + 1) (by simp only [regs]; omega) (by omega) (by omega))
    have hcol : ∀ j' < nMax, ∀ c < C, ob + 2 * k * C ≤ cb + cs * j' + 2 * c := fun _ _ _ _ => by
      omega
    obtain ⟨b1, b2, b3, hM2⟩ := sBody_sem I st hM' (k := k) (C := C) (jb := jb) (djb := djb)
      (wb := wb) (eb := eb) (cb := cb) (cs := cs) (ob := ob) (tb := tb) (s0 := j) (x := x) hk64 hC
      hj (by omega) (by simp only [regs]; omega) (by simp only [regs]; omega)
      (by simp only [regs]; omega) (by simp only [regs]; omega) (by simp only [regs]; omega)
      (by simp only [regs]; omega) (by simp only [regs]; omega) (by omega) (by omega) (by omega)
      (by omega) (by omega) (fun t ht c hc => hcb2 _ (hJn t ht) c hc)
      (fun c hc => hcb2 _ (by omega) c hc) hob2 (by rw [hz]; exact hsz) (by rw [hz]; omega)
      (.inl (by omega)) (.inl (by omega)) (.inl (by omega)) (.inr (by omega)) (.inr (by omega))
      (fun c hc j' hj' => by
        have h' : j' < nMax := by
          rcases hj' with h' | rfl
          · obtain ⟨t, ht, rfl⟩ := List.mem_map.1 h'; exact hJn t (List.mem_range.1 ht)
          · omega
        have := hcol j' h' c hc
        exact ⟨.inl this, .inl (by omega)⟩) hS'
      (fun i hi => by rw [hF _ (by omega) (by omega), hT i hi])
      (fun t ht => by rw [hH _ (by simp only [regs]; omega) (by omega) (by omega), hJ t ht])
    refine ⟨inv_decS hM2 (by decide), by rw [size_decS, size_sem, hz],
      by rw [rd_decS (by decide), b2], fun s0 hs0 c hc => ?_, fun y hy hy2 hy3 => ?_⟩
    · have hlt := out_lt (k := k) hc (show s0 < k by omega)
      rw [rdF_decS _ (by simp only [bC1]; omega) (by simp only [bC1]; omega)]
      rcases Nat.lt_succ_iff_lt_or_eq.1 hs0 with hs0 | rfl
      · have hne : ∀ y', y' = ob + 2 * k * c + 2 * s0 ∨ y' = ob + 2 * k * c + 2 * s0 + 1 →
            ∀ c' < C, y' ≠ ob + 2 * k * c' + 2 * j ∧ y' ≠ ob + 2 * k * c' + 2 * j + 1 := by
          rintro y' hy' c' hc'
          have n1 := cell_ne (k := k) (c := c) (c' := c') (a := 0) (b := 0) (show s0 < k by omega)
            hj (by omega) (by omega) (by omega)
          have n2 := cell_ne (k := k) (c := c) (c' := c') (a := 0) (b := 1) (show s0 < k by omega)
            hj (by omega) (by omega) (by omega)
          have n3 := cell_ne (k := k) (c := c) (c' := c') (a := 1) (b := 0) (show s0 < k by omega)
            hj (by omega) (by omega) (by omega)
          have n4 := cell_ne (k := k) (c := c) (c' := c') (a := 1) (b := 1) (show s0 < k by omega)
            hj (by omega) (by omega) (by omega)
          rcases hy' with rfl | rfl <;> constructor <;> omega
        rw [rdF_eq (b3 _ (by simp only [regs]; omega) (.inr (by omega)) (hne _ (.inl rfl)))
          (b3 _ (by simp only [regs]; omega) (.inr (by omega)) (hne _ (.inr rfl))), hV s0 hs0 c hc]
      · rw [b1 c hc, sValM]
        have hcl : ∀ j' < nMax, rdF st.M (cb + cs * j' + 2 * c) = rdF s.M (cb + cs * j' + 2 * c) :=
          fun j' hj' => hF _ (by omega) (.inr (hcol j' hj' c hc))
        have hdj : ∀ t < k, rdF st.M (djb + 2 * t) = rdF s.M (djb + 2 * t) := fun t ht =>
          hF _ (by omega) (.inl (by omega))
        have hwt : ∀ t < k, rdF st.M (wb + 2 * t) = rdF s.M (wb + 2 * t) := fun t ht =>
          hF _ (by omega) (.inl (by omega))
        have hP : ∏ t ∈ range k, (D s0 + rdF st.M (djb + 2 * t)) =
            ∏ t ∈ range k, (D s0 + rdF s.M (djb + 2 * t)) :=
          Finset.prod_congr rfl fun t ht => by rw [hdj t (Finset.mem_range.1 ht)]
        rw [hP, hcl s0 (by omega)]
        split_ifs
        · rfl
        · refine congrArg (_ * ·) (Finset.sum_congr rfl fun t ht => ?_)
          have ht' := Finset.mem_range.1 ht
          rw [hcl _ (hJn t ht'), hwt t ht', hdj t ht']
    · rw [rd_decS (by simp only [bC1, regs] at hy ⊢; omega)]
      rw [b3 y hy hy2 (fun c' hc' => by
        have := out_lt (k := k) hc' hj
        constructor <;> omega), hH y hy hy2 hy3]

/-! ## The whole program -/

theorem pre_bS (M : Mem) (hM : Inv M) (k : ℕ) :
    rd (runPrims [.const bS 0, .const bN1 (toWord k)] M) bS = toWord 0 ∧
    rd (runPrims [.const bS 0, .const bN1 (toWord k)] M) bN1 = toWord k ∧
    (∀ i, i ≠ bS → i ≠ bN1 → rd (runPrims [.const bS 0, .const bN1 (toWord k)] M) i = rd M i) ∧
    Inv (runPrims [.const bS 0, .const bN1 (toWord k)] M) := by
  obtain ⟨p1, p2, p3, p4⟩ := pre2_sem M hM (r := bS) (n := bN1) 0 (toWord k) (by decide)
    (by decide) (by decide) (by decide) (by decide)
  exact ⟨p1.trans toWord_zero'.symm, p2, p3, p4⟩

/-- **The interpolation on the machine**: for the list `Jl` at `jb` (`k = |Jl|` entries below
`2^20`) and the column store at `cb`, `out[c][s] = baryVal Jl k s y_c` for every target `s < k`
and coordinate `c < C`, with `y_c(j)` the store's element `cb + cs·j + 2c`; the heap outside
`DJ`, `W`, `E` and the output rows is kept. -/
theorem baryIR_sem (I : Array Word) (s : St) (hM : Inv s.M)
    {k C jb djb wb eb cb cs ob tb : ℕ} {Jl : List ℕ} (hL : BaryLay k C jb djb wb eb cb ob tb)
    (hk : k ≤ nMax) (hC : C < 2 ^ 62) (hc64 : cb < 2 ^ 64)
    (hcb2 : ∀ j < nMax, ∀ c < C, cb + cs * j + 2 * c + 1 < 2 ^ 64)
    (hsz : ob + 2 * k * C ≤ s.M.size) (hJn : ∀ t < k, Jl.getD t 0 < nMax)
    (hT : ∀ i < 20, rdF s.M (tb + 2 * i) = (wRow D logNMax 0).getD i 0)
    (hJ : ∀ t < k, rd s.M (jb + t) = toWord (Jl.getD t 0)) :
    (∀ s0 < k, ∀ c < C, rdF (semXIR I (baryIR k C jb djb wb eb cb cs ob tb) s).M
        (ob + 2 * k * c + 2 * s0) = baryVal Jl k s0 (fun j => rdF s.M (cb + cs * j + 2 * c))) ∧
    (∀ y, regs ≤ y → (y < djb ∨ eb + 2 * k ≤ y) → (y < ob ∨ ob + 2 * k * C ≤ y) →
      rd (semXIR I (baryIR k C jb djb wb eb cb cs ob tb) s).M y = rd s.M y) ∧
    Inv (semXIR I (baryIR k C jb djb wb eb cb cs ob tb) s).M := by
  have hL' := hL
  obtain ⟨htb, htj, hjd, hdw, hwe, heo, hoc⟩ := hL'
  have hnM : nMax = 2 ^ 20 := rfl
  have hk64 : k < 2 ^ 64 := by omega
  simp only [regs] at htb
  rw [baryIR]
  simp only [semXIR_seq]
  -- `DJ`
  obtain ⟨d1, d2, hM1⟩ := djIR_sem I s hM (k := k) (jb := jb) (djb := djb) (tb := tb)
    (J := fun t => Jl.getD t 0) hk64 (by simp only [regs]; omega) (by simp only [regs]; omega)
    (by simp only [regs]; omega) (by omega) (by omega) (by omega) (by omega) (.inl hjd)
    (.inl (by omega)) hJ hJn hT
  have z1 := size_sem I (djIR k jb djb tb) s
  generalize semXIR I (djIR k jb djb tb) s = q1 at d1 d2 hM1 z1 ⊢
  -- `W`
  obtain ⟨w1, w2, hM2⟩ := wtIR_sem I q1 hM1 (k := k) (djb := djb) (wb := wb)
    (G := fun t => D (Jl.getD t 0)) hk64 (by simp only [regs]; omega)
    (by simp only [regs]; omega) (by omega) (by omega) (by rw [z1]; omega) (.inl hdw) d1
  have z2 := size_sem I (wtIR k djb wb) q1
  generalize semXIR I (wtIR k djb wb) q1 = q2 at w1 w2 hM2 z2 ⊢
  have H2 : ∀ y, regs ≤ y → (y < djb ∨ eb ≤ y) → rd q2.M y = rd s.M y := fun y hy hy2 =>
    (w2 y hy (by omega)).trans (d2 y hy (by omega))
  have hdj2 : ∀ t < k, rdF q2.M (djb + 2 * t) = D (Jl.getD t 0) := fun t ht => by
    rw [rdF_eq (w2 _ (by simp only [regs]; omega) (.inl (by omega)))
      (w2 _ (by simp only [regs]; omega) (.inl (by omega))), d1 t ht]
  -- `s := 0`, `bN1 := k`
  obtain ⟨p1, p2, p3, hM3⟩ := pre_bS q2.M hM2 k
  have e3 : semXIR I (.blk [.const bS 0, .const bN1 (toWord k)]) q2 =
      ⟨runPrims [.const bS 0, .const bN1 (toWord k)] q2.M, q2.o⟩ := rfl
  rw [e3]
  have z3 := size_runPrims [.const bS 0, .const bN1 (toWord k)] q2.M
  generalize runPrims [.const bS 0, .const bN1 (toWord k)] q2.M = M3 at p1 p2 p3 hM3 z3 ⊢
  have H3 : ∀ y, regs ≤ y → rd M3 y = rd q2.M y := fun y hy =>
    p3 y (by simp only [regs, bS] at hy ⊢; omega) (by simp only [regs, bN1] at hy ⊢; omega)
  have F3 : ∀ y, regs ≤ y → rdF M3 y = rdF q2.M y := fun y hy =>
    rdF_eq (H3 y hy) (H3 (y + 1) (by simp only [regs] at hy ⊢; omega))
  obtain ⟨l1, l2, hM4⟩ := sLoop_sem I ⟨M3, q2.o⟩ hM3 (k := k) (C := C) (jb := jb) (djb := djb)
    (wb := wb) (eb := eb) (cb := cb) (cs := cs) (ob := ob) (tb := tb) (x := fun t => Jl.getD t 0)
    hL hk hC hc64 hcb2 (by rw [z3, z2, z1]; exact hsz) hJn p2 p1
    (fun i hi => by
      rw [F3 _ (by simp only [regs]; omega), rdF_eq (H2 _ (by simp only [regs]; omega)
        (.inl (by omega))) (H2 _ (by simp only [regs]; omega) (.inl (by omega))), hT i hi])
    (fun t ht => by
      rw [H3 _ (by simp only [regs]; omega), H2 _ (by simp only [regs]; omega) (.inl (by omega)),
        hJ t ht])
  refine ⟨fun s0 hs0 c hc => ?_, fun y hy hy2 hy3 => ?_, hM4⟩
  · rw [l1 s0 hs0 c hc, sValM, baryVal]
    have hcl : ∀ j < nMax, rdF M3 (cb + cs * j + 2 * c) = rdF s.M (cb + cs * j + 2 * c) :=
      fun j _ => by
        rw [F3 _ (by simp only [regs]; omega)]
        exact rdF_eq (H2 _ (by simp only [regs]; omega) (.inr (by omega)))
          (H2 _ (by simp only [regs]; omega) (.inr (by omega)))
    have hd : ∀ t < k, rdF M3 (djb + 2 * t) = dj Jl t := fun t ht => by
      rw [F3 _ (by simp only [regs]; omega), hdj2 t ht]; rfl
    have hw : ∀ t < k, rdF M3 (wb + 2 * t) = wgt Jl k t :=
      fun t ht => by rw [F3 _ (by simp only [regs]; omega), w1 t ht]; rfl
    have hP : ∏ t ∈ range k, (D s0 + rdF M3 (djb + 2 * t)) = ellS Jl k s0 :=
      Finset.prod_congr rfl fun t ht => by rw [hd t (Finset.mem_range.1 ht)]
    rw [hP, hcl s0 (by omega)]
    by_cases h0 : ellS Jl k s0 = 0
    · rw [if_pos h0, if_pos h0]
    · rw [if_neg h0, if_neg h0]
      refine congrArg (_ * ·) (Finset.sum_congr rfl fun t ht => ?_)
      have ht' := Finset.mem_range.1 ht
      rw [hcl _ (hJn t ht'), hw t ht', hd t ht', eAt]
  · rw [l2 y hy (by omega) hy3, H3 y hy, H2 y hy (by omega)]

/-- **The interpolation computed**: with `k = |Jl|`, `Jl` without repeats, every `out[c][s]` is
`interpF D J y_c s` (`J = Jl.toFinset`). -/
theorem baryIR_interp (I : Array Word) (s : St) (hM : Inv s.M)
    {C jb djb wb eb cb cs ob tb : ℕ} {Jl : List ℕ}
    (hL : BaryLay Jl.length C jb djb wb eb cb ob tb) (hnd : Jl.Nodup) (hJn : ∀ j ∈ Jl, j < nMax)
    (hk : Jl.length ≤ nMax) (hC : C < 2 ^ 62) (hc64 : cb < 2 ^ 64)
    (hcb2 : ∀ j < nMax, ∀ c < C, cb + cs * j + 2 * c + 1 < 2 ^ 64)
    (hsz : ob + 2 * Jl.length * C ≤ s.M.size)
    (hT : ∀ i < 20, rdF s.M (tb + 2 * i) = (wRow D logNMax 0).getD i 0)
    (hJ : ∀ t < Jl.length, rd s.M (jb + t) = toWord (Jl.getD t 0)) :
    ∀ s0 < Jl.length, ∀ c < C,
      rdF (semXIR I (baryIR Jl.length C jb djb wb eb cb cs ob tb) s).M
        (ob + 2 * Jl.length * c + 2 * s0) =
      interpF D Jl.toFinset (fun j => rdF s.M (cb + cs * j + 2 * c)) s0 := by
  have hget : ∀ t < Jl.length, Jl.getD t 0 < nMax := fun t ht => by
    rw [List.getD_eq_getElem _ _ ht]; exact hJn _ (List.getElem_mem ht)
  intro s0 hs0 c hc
  rw [(baryIR_sem I s hM hL hk hC hc64 hcb2 hsz hget hT hJ).1 s0 hs0 c hc]
  exact baryVal_eq hnd hJn (by omega) _

/-! ## Level 0's layout -/

/-- The basis table (`2^20`; 800 cells). -/ def tb0 : ℕ := 1048576
/-- The list `J` (`2^21`). -/ def jb0 : ℕ := 2097152
/-- `DJ` (`2^22`). -/ def djb0 : ℕ := 4194304
/-- `W` (`2^22 + 2^19`). -/ def wb0 : ℕ := 4718592
/-- `E` (`2^22 + 2^20`). -/ def eb0 : ℕ := 5242880
/-- The output rows (`2^24`): row `c` at `ob0 + 2^18 c`. -/ def ob0 : ℕ := 16777216

/-- Level 0's interpolation: `k₀ = 2^17` targets, `C = 64` coordinates, the column store of the
read (`colBase`, 128 words a column). -/
def bary0 : XIR := baryIR (2 ^ 17) 64 jb0 djb0 wb0 eb0 colBase 128 ob0 tb0

theorem lay0 : BaryLay (2 ^ 17) 64 jb0 djb0 wb0 eb0 colBase ob0 tb0 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    simp only [regs, tb0, jb0, djb0, wb0, eb0, ob0, colBase] <;> norm_num

/-- **Level 0's interpolation computed**: on a list `Jl` of `2^17` distinct positions below
`2^18` at `jb0`, output row `c` holds `interpF D J y_c` on `D[0, 2^17)`, `y_c(j)` the column
store's coordinate `c` of position `j`. The heap below `2^22` and from `2^25` on, and the cells
in `[2^22 + 5·2^18, 2^24)` (the chain's answers among them) are kept. -/
theorem bary0_interp (I : Array Word) (s : St) (hM : Inv s.M) {Jl : List ℕ}
    (hlen : Jl.length = 2 ^ 17) (hnd : Jl.Nodup) (hJn : ∀ j ∈ Jl, j < 2 ^ 18)
    (hsz : memX ≤ s.M.size)
    (hT : ∀ i < 20, rdF s.M (tb0 + 2 * i) = (wRow D logNMax 0).getD i 0)
    (hJ : ∀ t < 2 ^ 17, rd s.M (jb0 + t) = toWord (Jl.getD t 0)) :
    (∀ s0 < 2 ^ 17, ∀ c < 64, rdF (semXIR I bary0 s).M (ob0 + 2 ^ 18 * c + 2 * s0) =
      interpF D Jl.toFinset (fun j => rdF s.M (colBase + 128 * j + 2 * c)) s0) ∧
    (∀ y, regs ≤ y → (y < djb0 ∨ eb0 + 2 ^ 18 ≤ y) → (y < ob0 ∨ colBase ≤ y) →
      rd (semXIR I bary0 s).M y = rd s.M y) ∧
    Inv (semXIR I bary0 s).M := by
  have hnM : nMax = 2 ^ 20 := rfl
  have hL := lay0
  rw [← hlen] at hL
  have hmx : memX = 2 ^ 26 := rfl
  have hsz' : ob0 + 2 * Jl.length * 64 ≤ s.M.size := by
    rw [hlen]; simp only [ob0]; omega
  have hcb2 : ∀ j < nMax, ∀ c < 64, colBase + 128 * j + 2 * c + 1 < 2 ^ 64 := fun j hj c hc => by
    simp only [colBase]; omega
  have hJ' : ∀ t < Jl.length, rd s.M (jb0 + t) = toWord (Jl.getD t 0) := fun t ht =>
    hJ t (by omega)
  have hJn' : ∀ j ∈ Jl, j < nMax := fun j hj => by have := hJn j hj; omega
  have hb := baryIR_sem I s hM hL (by omega) (by norm_num) (by simp only [colBase]; norm_num) hcb2
    hsz' (fun t ht => by
      rw [List.getD_eq_getElem _ _ ht]; exact hJn' _ (List.getElem_mem ht)) hT hJ'
  rw [hlen] at hb
  refine ⟨fun s0 hs0 c hc => ?_, fun y hy hy2 hy3 => hb.2.1 y hy hy2 (by
    simp only [ob0, colBase] at hy3 ⊢; omega), hb.2.2⟩
  have := baryIR_interp I s hM (C := 64) (cs := 128) hL hnd hJn' (by omega) (by norm_num)
    (by simp only [colBase]; norm_num) hcb2 hsz' hT hJ' s0 (by omega) c hc
  rw [hlen] at this
  rw [show 2 ^ 18 * c = 2 * 2 ^ 17 * c by ring]
  exact this

end FR.X
