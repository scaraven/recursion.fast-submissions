-- G6: this module also holds the former modules `FRXBaryTop` (one section each, in import order).
import FRXBary

section G6_FRXBaryTop

-- New for `flock-recursive` (BLUEPRINT §6.2 step 4; stage S-H2, track L-ext).

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

attribute [local irreducible] entryK storeM runPrims

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
  simp +decide only [sBody, eBody, cBody, aBody, yIR, addrPs, alphaIR, alphaBody, ldF, stF, WF,
    Writes, Prim.dst, bnw_mulF, bnw_addF, bnw_invF, wfF_mul, wfF_add, wfF_inv, fDs, fLp, fDd, fIv,
    fEt, fPr, fY, fAc, fX, bT, bS, bCi, bA, bA1, bJ, bK, bZ, bC2, bN2, bC3, bN3, bCo, rBs, rTr, rTa,
    rTa1, rBit, uI, uT1, fG, fAl, rC2, rN2, cTmp, regs, List.mem_cons, List.mem_nil_iff,
    forall_eq_or_imp, exists_eq_or_imp, forall_eq, exists_eq_left, or_false, and_true,
    List.cons_append, List.nil_append]

theorem nw_eBody_bS (djb wb eb : ℕ) : ¬ Writes (eBody djb wb eb) bS := by
  simp +decide only [eBody, addrPs, ldF, stF, Writes, Prim.dst, bnw_mulF, bnw_addF, bnw_invF, bA,
    bK, bA1, fX, fDd, fLp, fIv, fEt, bT, bS, cTmp, List.mem_cons, List.mem_nil_iff,
    exists_eq_or_imp, exists_eq_left, or_false]

theorem nw_cBody_bS (k jb eb cb cs ob : ℕ) : ¬ Writes (cBody k jb eb cb cs ob) bS := by
  simp +decide only [cBody, aBody, yIR, addrPs, ldF, stF, Writes, Prim.dst, bnw_mulF, bnw_addF, bA,
    bK, bA1, bJ, fY, fX, fPr, fAc, bT, bN3, bC3, bCi, bCo, cTmp, bS, List.mem_cons,
    List.mem_nil_iff, exists_eq_or_imp, exists_eq_left, or_false, List.cons_append, List.nil_append]

theorem nw_alphaIR_bS : ¬ Writes alphaIR bS := by
  simp +decide only [alphaIR, alphaBody, ldF, Writes, Prim.dst, rBit, uT1, rTa, rTa1, fG, fAl, uI,
    rN2, rC2, cTmp, bS, or_false]

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
    (by simp +decide only [WF, Prim.dst, rBs, rTr, List.mem_cons, List.mem_nil_iff,
      forall_eq_or_imp, forall_eq, or_false, and_true]) hM
  have H0 := hframe I (.blk [.op .or rBs bS bS, .const rTr (toWord tb)]) s
    (by simp +decide only [Lo, Prim.dst, regs, rBs, rTr, List.mem_cons, List.mem_nil_iff,
      forall_eq_or_imp, forall_eq, or_false, and_true])
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
    (by simp +decide only [WF, Prim.dst, fDs, fLp, bT, bN2, List.mem_cons, List.mem_nil_iff,
      forall_eq_or_imp, forall_eq, or_false, and_true]) hM1
  have H2 := hframe I (.blk [.op .or fDs fAl fAl, .op .or (fDs + 1) (fAl + 1) (fAl + 1),
    .const fLp 1, .const (fLp + 1) 0, .const bT 0, .const bN2 (toWord k)]) q1
    (by simp +decide only [Lo, Prim.dst, regs, fDs, fLp, bT, bN2, List.mem_cons, List.mem_nil_iff,
      forall_eq_or_imp, forall_eq, or_false, and_true])
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
    (by simp +decide only [WF, Prim.dst, bZ, bK, bCi, bCo, bN2, List.mem_cons, List.mem_nil_iff,
      forall_eq_or_imp, forall_eq, or_false, and_true]) hM3
  have H4 := hframe I (.blk [.op .or bZ fLp (fLp + 1), .const bK 0, .op .eq bZ bZ bK,
    .const bCi 0, .const bCo 0, .const bN2 (toWord C)]) q3
    (by simp +decide only [Lo, Prim.dst, regs, bZ, bK, bCi, bCo, bN2, List.mem_cons,
      List.mem_nil_iff, forall_eq_or_imp, forall_eq, or_false, and_true])
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
  have := Nat.mul_le_mul_left (2 * k) (show c + 1 ≤ C by omega)
  rw [Nat.mul_add, Nat.mul_one] at this; omega

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

end G6_FRXBaryTop

section G6_FRXLag

-- New for `flock-recursive` (BLUEPRINT revision 4.2, §10 changes 27 (A)(ii); stage S-H4).

/-!
# The interpolation by prefix and suffix products, on a window of rows

Revision 4.2's node decoder interpolates only the rows the output reads (level 0's rows 4–7).
3.x's `baryIR` pays one `F` inversion (1,107 steps) per pair (target, agreement point): `k²·1,363`
steps plus `106` per row and pair. This module's **`lagIR`** pays none:

* the evaluation domain is `D x = ofB64 x` (`FRRS.D`), so every difference `D s − D J_u` is the
  `B64` element `s ⊕ J_u`, one word, and its products are `B64` products (`mulB`, 13 steps);
* for a target `s`, the Lagrange numerator `Π_{u ≠ t} (s ⊕ J_u)` is `P_t · Q_t`, the prefix product
  `P_t = Π_{u < t}` (stored by a forward pass) times the suffix product `Q_t = Π_{u > t}` (kept in a
  register by a backward pass). This is Montgomery's batched-inversion pass without its one
  inversion: the barycentric form needs `ℓ(s)⁻¹ · ℓ(s) / (s − J_t)`, the Lagrange form only the
  product, so no case `ℓ(s) = 0` arises;
* the weights `W_t = (Π_{m ≠ t} (J_t ⊕ J_m))⁻¹` are `k` `B64` inversions, folded into the values:
  `Y_c[t] = W_t · y_c(J_t)` (two `B64` products per row).

Cost (`cost_lagIR`): `27 + k (1,122 + 72 C) + k² (101 + 40 C)` for `C` rows; at `C = 4` that is
`261` steps per pair against 3.x's `1,363 + 106 · 64`.

**Layout** (`LagLay`): the list `J` (`k` words at `jb`), the prefix table (`k` words at `pb`), the
values `Y` (`2Ck` words at `yb`, row `c` of position `t` at `yb + 2(Ct + c)`), the output (row `c`
of `2k` words at `ob + 2kc`, as `bfRowsIR` reads it), then the column store from `cb`: `y_c(j)` is
the `F` element at `cb + cs·j + 2(c₀ + c)`, rows `c₀ … c₀ + C − 1`.

**Main statements.**
* `lagVal_eq`: the machine's value `lagVal` is `interpF D J y s` (`J` without repeats, below
  `2^20`);
* `lagIR_sem`: on `LagLay`, output row `c` holds `lagVal` of row `c₀ + c` at every target `s < k`;
  the heap outside the prefix table, `Y` and the output is kept;
* `lagIR_interp`: the same with `interpF`;
* `cost_lagIR`, `wf_lagIR`, `noLoopT_lagIR`, `outs_lagIR`.
-/

namespace FR.X

open RecursionFast FR Finset

-- G2: `entryK`/`storeM`/`runPrims` are never unfolded while unifying states (elaboration time).
attribute [local irreducible] entryK storeM runPrims

/-! ## Registers (`160 …`) -/

/-- A loaded `J` word. -/ def lgJ : ℕ := 160
/-- `J_t` in the weight loop. -/ def lgT : ℕ := 161
/-- A difference `a ⊕ b`. -/ def lgD : ℕ := 162
/-- The flag `[a = b]`. -/ def lgZ : ℕ := 163
/-- A product (`P`, the weight's product). -/ def lgP : ℕ := 164
/-- The suffix product `Q`, or the weight `W_t`. -/ def lgQ : ℕ := 165
/-- The coefficient `P_t · Q`. -/ def lgE : ℕ := 166
/-- The pointer into `J`. -/ def lgA : ℕ := 167
/-- The outer pointer (`J_t`, or the prefix table). -/ def lgB : ℕ := 168
/-- The pointer into `Y`. -/ def lgY : ℕ := 169
/-- A walking pointer (the column, or `Y`'s row). -/ def lgX : ℕ := 170
/-- A loaded word. -/ def lgV : ℕ := 171
/-- A loaded word. -/ def lgV1 : ℕ := 172
/-- Constant scratch. -/ def lgK : ℕ := 173
/-- The target `s`. -/ def lgS : ℕ := 174
/-- The outer loop's counter. -/ def lgC1 : ℕ := 175
/-- Its count. -/ def lgN1 : ℕ := 176
/-- The inner loop's counter. -/ def lgC2 : ℕ := 177
/-- Its count. -/ def lgN2 : ℕ := 178
/-- The output pointer. -/ def lgO : ℕ := 181
/-- The accumulators: row `c` in `lgAc + 2c`, `lgAc + 2c + 1` (`C ≤ 16`). -/ def lgAc : ℕ := 184

/-! ## The program -/

/-- The weight's factor `(a ⊕ b) ||| [a = b]`: `a ⊕ b`, and `1` when `a = b`. -/
def fct (a b : Word) : Word := (a ^^^ b) ||| bW (decide (a = b))

/-- **One factor of `W_t`'s product**: `P *= (J_t ⊕ J_m) ||| [J_t = J_m]`, `m` at `lgA`. -/
def wInL : XIR :=
  .seq (.load lgJ lgA) (.blk ([.op .xor lgD lgT lgJ, .op .eq lgZ lgT lgJ, .op .or lgD lgD lgZ,
    .op .add lgA lgA cOne] ++ mulBC lgP lgP lgD))

/-- The loads of one value: `lgV, lgV1 := M[x], M[x + 1]`, both times `W_t` (`lgQ`). -/
def yLd : XIR :=
  .seq (.load lgV lgX) (.seq (.blk [.op .add lgX lgX cOne]) (.seq (.load lgV1 lgX)
    (.blk ([.op .add lgX lgX cOne] ++ mulBC lgV lgV lgQ ++ mulBC lgV1 lgV1 lgQ))))

/-- The stores of one value at `lgY`, `lgY + 1`. -/
def ySt : XIR :=
  .seq (.store lgY lgV) (.seq (.blk [.op .add lgY lgY cOne])
    (.seq (.store lgY lgV1) (.blk [.op .add lgY lgY cOne])))

/-- **One value** `Y_c[t] := W_t · y_c(J_t)` (the column pointer `lgX`, `Y`'s pointer `lgY`). -/
def yRowL : XIR := .seq yLd ySt

/-- The column pointer `cb + 2c₀ + cs · J_t`, then `C` as the count. -/
def wyMid (C cb cs c0 : ℕ) : List Prim :=
  [.const lgK (toWord cs), .op .mul lgX lgT lgK, .const lgK (toWord (cb + 2 * c0)),
    .op .add lgX lgX lgK, .const lgN2 (toWord C)]

/-- **One position `t`**: `W_t` (`k` factors, one `B64` inversion), then its `C` values. -/
def wyBody (k C jb cb cs c0 : ℕ) : XIR :=
  .seq (.load lgT lgB) (.seq (.blk [.const lgP 1, .const lgA (toWord jb), .const lgN2 (toWord k)])
    (.seq (.loopK lgC2 lgN2 (toWord k) wInL) (.seq (.seq (invB lgQ lgP) (.blk (wyMid C cb cs c0)))
      (.seq (.loopK lgC2 lgN2 (toWord C) yRowL) (.blk [.op .add lgB lgB cOne])))))

/-- **The values** `Y_c[t] = W_t · y_{c₀+c}(J_t)` for `t < k`, `c < C`. -/
def yTabIR (k C jb yb cb cs c0 : ℕ) : XIR :=
  .seq (.blk [.const lgB (toWord jb), .const lgY (toWord yb), .const lgN1 (toWord k)])
    (.loopK lgC1 lgN1 (toWord k) (wyBody k C jb cb cs c0))

/-- **The forward pass's step**: `P_t := P` at `pb + t`, `P *= s ⊕ J_t`. -/
def fwdL : XIR :=
  .seq (.load lgJ lgA) (.seq (.store lgB lgP)
    (.blk ([.op .xor lgD lgS lgJ, .op .add lgA lgA cOne, .op .add lgB lgB cOne] ++
      mulBC lgP lgP lgD)))

/-- **Row `c`'s accumulation**: `acc_c += e · Y_c[t]` (two words, `lgX` walking `Y`'s row). -/
def accRow (c : ℕ) : XIR :=
  .seq (.load lgV lgX) (.seq (.blk [.op .add lgX lgX cOne]) (.seq (.load lgV1 lgX)
    (.blk ([.op .add lgX lgX cOne] ++ mulBC lgV lgV lgE ++ mulBC lgV1 lgV1 lgE ++
      [.op .xor (lgAc + 2 * c) (lgAc + 2 * c) lgV, .op .xor (lgAc + 2 * c + 1) (lgAc + 2 * c + 1) lgV1]))))

/-- The rows `0 … C − 1`, unrolled. -/
def accIR : ℕ → XIR
  | 0 => .blk []
  | C + 1 => .seq (accIR C) (accRow C)

/-- **The backward pass's step** (`t` from `k − 1` down): `e := P_t · Q`, `Q *= s ⊕ J_t`, then
the rows. -/
def bwdL (C : ℕ) : XIR :=
  .seq (.blk [.op .sub lgA lgA cOne, .op .sub lgB lgB cOne, .op .sub lgY lgY lgK, .op .or lgX lgY lgY])
    (.seq (.load lgJ lgA) (.seq (.load lgE lgB)
      (.seq (.blk ([.op .xor lgD lgS lgJ] ++ mulBC lgE lgE lgQ ++ mulBC lgQ lgQ lgD)) (accIR C))))

/-- The output of row `c`: `acc_c` at `lgO`, `lgO += 2k` (`2k` in `lgK`). -/
def stRow (c : ℕ) : XIR :=
  .seq (.store lgO (lgAc + 2 * c)) (.seq (.blk [.op .add lgO lgO cOne])
    (.seq (.store lgO (lgAc + 2 * c + 1)) (.blk [.op .sub lgO lgO cOne, .op .add lgO lgO lgK])))

/-- The outputs of rows `0 … C − 1`, unrolled. -/
def stAcc : ℕ → XIR
  | 0 => .blk []
  | C + 1 => .seq (stAcc C) (stRow C)

/-- The accumulators' zeros. -/
def zeroPs (C : ℕ) : List Prim := (List.range (2 * C)).map fun i => .const (lgAc + i) 0

/-- **One target `s`** (in `lgS`): the forward pass, the backward pass, the `C` outputs at
`ob + 2s + 2kc`. -/
def tgBody (k C jb pb yb ob : ℕ) : XIR :=
  .seq (.blk [.const lgP 1, .const lgA (toWord jb), .const lgB (toWord pb), .const lgN2 (toWord k)])
    (.seq (.loopK lgC2 lgN2 (toWord k) fwdL)
      (.seq (.blk ([.const lgQ 1, .const lgY (toWord (yb + 2 * C * k)), .const lgK (toWord (2 * C)),
          .const lgN2 (toWord k)] ++ zeroPs C))
        (.seq (.loopK lgC2 lgN2 (toWord k) (bwdL C))
          (.seq (.blk [.const lgK (toWord (2 * k)), .const lgO (toWord ob), .op .add lgO lgO lgS,
              .op .add lgO lgO lgS])
            (.seq (stAcc C) (.blk [.op .add lgS lgS cOne]))))))

/-- **The targets** `s < k`. -/
def tgIR (k C jb pb yb ob : ℕ) : XIR :=
  .seq (.blk [.const lgS 0, .const lgN1 (toWord k)]) (.loopK lgC1 lgN1 (toWord k) (tgBody k C jb pb yb ob))

/-- **The interpolation of rows `c₀ … c₀ + C − 1`** at the targets `0 … k − 1` from the `k`
positions listed at `jb`. -/
def lagIR (k C c0 jb pb yb ob cb cs : ℕ) : XIR :=
  .seq (yTabIR k C jb yb cb cs c0) (tgIR k C jb pb yb ob)

/-! ## Well formed, loop-free in `t`, no output, cost -/

theorem len_zeroPs (C : ℕ) : (zeroPs C).length = 2 * C := by simp [zeroPs]

theorem nw_accIR (i : ℕ) (h1 : 9 ≤ i) (h2 : i < lgAc) (h3 : i ≠ lgV) (h4 : i ≠ lgV1)
    (h5 : i ≠ lgX) : ∀ C, Writes (accIR C) i ↔ False
  | 0 => by simp [accIR, Writes]
  | C + 1 => by
    simp only [accIR, Writes, nw_accIR i h1 h2 h3 h4 h5 C, false_or, iff_false]
    simp only [lgAc, lgV, lgV1, lgX] at *
    simp [accRow, mulBC, redC, Writes, Prim.dst, lgAc, lgV, lgV1, lgX]
    omega

theorem wf_accIR : ∀ C, WF (accIR C) ↔ True
  | 0 => by simp [accIR, WF]
  | C + 1 => by
    simp only [accIR, WF, wf_accIR C, true_and, iff_true]
    simp [accRow, mulBC, redC, WF, Prim.dst, lgV, lgV1, lgX, lgE, lgAc]
    omega

theorem nw_stAcc (i : ℕ) (h1 : i ≠ cTmp) (h2 : i ≠ lgO) : ∀ C, Writes (stAcc C) i ↔ False
  | 0 => by simp [stAcc, Writes]
  | C + 1 => by
    simp only [stAcc, Writes, nw_stAcc i h1 h2 C, false_or, iff_false]
    simp only [stRow, Writes, Prim.dst, List.mem_cons, List.not_mem_nil, or_false,
      exists_eq_or_imp, exists_eq_left, not_or]
    exact ⟨h1, fun h => h2 h.symm, h1, fun h => h2 h.symm, fun h => h2 h.symm⟩

theorem wf_stAcc : ∀ C, WF (stAcc C) ↔ True
  | 0 => by simp [stAcc, WF]
  | C + 1 => by
    simp only [stAcc, WF, wf_stAcc C, true_and, iff_true]
    simp [stRow, WF, Prim.dst, lgO, lgAc, cTmp]

theorem nw_invB {i : ℕ} (h1 : 12 ≤ i) (h2 : i ≠ 165) : Writes (invB 165 164) i ↔ False :=
  ⟨fun ⟨p, hp, he⟩ => by have := invBC_dst 165 164 p hp; omega, False.elim⟩

theorem wfB_inv : WF (invB 165 164) ↔ True := iff_true_intro (wf_invB _ _ (by decide))

theorem wf_lagIR (k C c0 jb pb yb ob cb cs : ℕ) : WF (lagIR k C c0 jb pb yb ob cb cs) := by
  simp [lagIR, yTabIR, wyBody, wyMid, wInL, yRowL, yLd, ySt, tgIR, tgBody, fwdL, bwdL, zeroPs, WF, Writes,
    Prim.dst, mulBC, redC, wf_accIR, wf_stAcc, wfB_inv,
    nw_invB (i := 175) (by omega) (by decide),
    nw_accIR 175 (by decide) (by decide) (by decide) (by decide) (by decide),
    nw_accIR 177 (by decide) (by decide) (by decide) (by decide) (by decide),
    nw_stAcc 175 (by decide) (by decide), lgJ, lgT, lgD, lgZ, lgP, lgQ, lgE, lgA, lgB, lgY, lgX,
    lgV, lgV1, lgK, lgS, lgC1, lgN1, lgC2, lgN2, lgO, lgAc, cTmp, regs, cOne, cRed]
  exact ⟨fun x _ => by omega, fun a _ => by omega⟩

theorem noLoopT_accIR : ∀ C, NoLoopT (accIR C)
  | 0 => by simp [accIR, NoLoopT]
  | C + 1 => ⟨noLoopT_accIR C, by simp [accRow, NoLoopT]⟩

theorem noLoopT_stAcc : ∀ C, NoLoopT (stAcc C)
  | 0 => by simp [stAcc, NoLoopT]
  | C + 1 => ⟨noLoopT_stAcc C, by simp [stRow, NoLoopT]⟩

theorem noLoopT_lagIR (k C c0 jb pb yb ob cb cs : ℕ) : NoLoopT (lagIR k C c0 jb pb yb ob cb cs) := by
  simp [lagIR, yTabIR, wyBody, wInL, yRowL, yLd, ySt, tgIR, tgBody, fwdL, bwdL, invB, NoLoopT, noLoopT_accIR,
    noLoopT_stAcc]

theorem outs_accIR (t : ℕ) : ∀ C, outs (accIR C) t = 0
  | 0 => by simp [accIR, outs]
  | C + 1 => by simp [accIR, accRow, outs, outs_accIR t C]

theorem outs_stAcc (t : ℕ) : ∀ C, outs (stAcc C) t = 0
  | 0 => by simp [stAcc, outs]
  | C + 1 => by simp [stAcc, stRow, outs, outs_stAcc t C]

theorem outs_lagIR (k C c0 jb pb yb ob cb cs t : ℕ) : outs (lagIR k C c0 jb pb yb ob cb cs) t = 0 := by
  simp [lagIR, yTabIR, wyBody, wInL, yRowL, yLd, ySt, tgIR, tgBody, fwdL, bwdL, invB, outs, outs_accIR,
    outs_stAcc]

theorem cost_accIR (t : ℕ) : ∀ C, cost (accIR C) t = 1 + 40 * C
  | 0 => by simp [accIR, cost, blkSteps]
  | C + 1 => by
    simp only [accIR, accRow, cost, cost_accIR t C, blkSteps, mulBC, redC, List.length_append,
      List.length_cons, List.length_nil]
    norm_num; ring

theorem cost_stAcc (t : ℕ) : ∀ C, cost (stAcc C) t = 1 + 16 * C
  | 0 => by simp [stAcc, cost, blkSteps]
  | C + 1 => by
    simp only [stAcc, stRow, cost, cost_stAcc t C, blkSteps, List.length_cons, List.length_nil]
    norm_num; ring

theorem cost_wyBody (k C jb cb cs c0 t : ℕ) (hk : k < 2 ^ 64) (hC : C < 2 ^ 64) :
    cost (wyBody k C jb cb cs c0) t = 1071 + 26 * k + 52 * C := by
  simp only [wyBody, wInL, yRowL, yLd, ySt, wyMid, cost, cost_invB, blkSteps, mulBC, redC,
    List.length_append, List.length_cons, List.length_nil, toNat_toWord hk, toNat_toWord hC]
  norm_num; ring

theorem cost_tgBody (k C jb pb yb ob t : ℕ) (hk : k < 2 ^ 64) :
    cost (tgBody k C jb pb yb ob) t = 45 + 20 * C + k * (75 + 40 * C) := by
  simp only [tgBody, cost, fwdL, bwdL, cost_accIR, cost_stAcc, blkSteps, mulBC, redC,
    List.length_append, List.length_cons, List.length_nil, toNat_toWord hk, len_zeroPs]
  norm_num; ring_nf; omega

/-- **The cost**: `27 + k (1,122 + 72 C) + k² (101 + 40 C)` (`k, C < 2^64`). -/
theorem cost_lagIR (k C c0 jb pb yb ob cb cs t : ℕ) (hk : k < 2 ^ 64) (hC : C < 2 ^ 64) :
    cost (lagIR k C c0 jb pb yb ob cb cs) t = 27 + k * (1122 + 72 * C) + k ^ 2 * (101 + 40 * C) := by
  simp only [lagIR, yTabIR, tgIR, cost, cost_wyBody k C jb cb cs c0 t hk hC,
    cost_tgBody k C jb pb yb ob t hk, blkSteps, List.length_cons, List.length_nil,
    toNat_toWord hk]
  norm_num; ring

theorem sizeIR_accIR : ∀ C, sizeIR (accIR C) = 1 + 40 * C
  | 0 => by simp [accIR, sizeIR, blkSteps]
  | C + 1 => by
    simp only [accIR, accRow, sizeIR, sizeIR_accIR C, blkSteps, mulBC, redC, List.length_append,
      List.length_cons, List.length_nil]
    norm_num; ring

theorem sizeIR_stAcc : ∀ C, sizeIR (stAcc C) = 1 + 18 * C
  | 0 => by simp [stAcc, sizeIR, blkSteps]
  | C + 1 => by
    simp only [stAcc, stRow, sizeIR, sizeIR_stAcc C, blkSteps, List.length_cons, List.length_nil]
    norm_num; ring

/-! ## The machine's value, against `interpF` -/

/-- `J_t` as a word. -/
def jw (Jl : List ℕ) (t : ℕ) : Word := toWord (Jl.getD t 0)

/-- The difference `s ⊕ J_u`, a `B64`. -/
def dif (Jl : List ℕ) (s u : ℕ) : B64 := wB (toWord s ^^^ jw Jl u)

/-- The prefix product `P_t = Π_{u < t} (s ⊕ J_u)`. -/
def preP (Jl : List ℕ) (s t : ℕ) : B64 := ∏ u ∈ range t, dif Jl s u

/-- The suffix product `Π_{t ≤ u < k} (s ⊕ J_u)`. -/
def sufP (Jl : List ℕ) (k s t : ℕ) : B64 := ∏ u ∈ Ico t k, dif Jl s u

/-- **The weight** `W_t = (Π_{m < k} ((J_t ⊕ J_m) ||| [J_t = J_m]))⁻¹`. -/
def wgtB (Jl : List ℕ) (k t : ℕ) : B64 := (∏ m ∈ range k, wB (fct (jw Jl t) (jw Jl m)))⁻¹

/-- **The value** `Y[t] = W_t · y(J_t)`. -/
def yv (Jl : List ℕ) (k : ℕ) (y : ℕ → F) (t : ℕ) : F := F.smulBase (wgtB Jl k t) (y (Jl.getD t 0))

/-- One term of the sum: `P_t · Q_t · Y[t]`. -/
def lagTerm (Jl : List ℕ) (k s : ℕ) (y : ℕ → F) (t : ℕ) : F :=
  F.smulBase (preP Jl s t * sufP Jl k s (t + 1)) (yv Jl k y t)

/-- **The machine's value** at target `s`: `Σ_{t < k} P_t Q_t W_t y(J_t)`. -/
def lagVal (Jl : List ℕ) (k s : ℕ) (y : ℕ → F) : F := ∑ t ∈ range k, lagTerm Jl k s y t

theorem wB_one : wB 1 = 1 := rfl

theorem D_eq_wB (x : ℕ) : D x = F.ofB64 (wB (toWord x)) := rfl

theorem D_sub_D (a b : ℕ) : D a - D b = F.ofB64 (wB (toWord a ^^^ toWord b)) := by
  rw [D_eq_wB, D_eq_wB, wB_xor]
  show F.add _ _ = _
  simp only [F.add, F.ofB64, add_zero]

/-- The prefix and suffix products make the product with `t` left out. -/
theorem pre_suf {k t : ℕ} (ht : t < k) (f : ℕ → B64) :
    (∏ u ∈ range t, f u) * ∏ u ∈ Ico (t + 1) k, f u = ∏ u ∈ range k, if u = t then 1 else f u := by
  rw [← Finset.prod_range_mul_prod_Ico _ (show t + 1 ≤ k by omega), Finset.prod_range_succ,
    if_pos rfl, mul_one]
  congr 1
  · exact Finset.prod_congr rfl fun u hu => by rw [if_neg (by have := Finset.mem_range.1 hu; omega)]
  · exact Finset.prod_congr rfl fun u hu => by rw [if_neg (by have := (Finset.mem_Ico.1 hu).1; omega)]

theorem ofB64_prod (s : Finset ℕ) (f : ℕ → B64) : F.ofB64 (∏ u ∈ s, f u) = ∏ u ∈ s, F.ofB64 (f u) :=
  map_prod F.ofB64RingHom f s

theorem ofB64_inv (a : B64) : F.ofB64 a⁻¹ = (F.ofB64 a)⁻¹ := map_inv₀ F.ofB64RingHom a

theorem jw_inj {Jl : List ℕ} (hnd : Jl.Nodup) (hJ : ∀ j ∈ Jl, j < nMax) {t u : ℕ}
    (ht : t < Jl.length) (hu : u < Jl.length) : jw Jl t = jw Jl u ↔ u = t := by
  have hn : nMax < 2 ^ 64 := by decide
  have h1 := hJ _ (List.getElem_mem ht)
  have h2 := hJ _ (List.getElem_mem hu)
  constructor
  · intro h
    have h' := congrArg BitVec.toNat h
    simp only [jw, List.getD_eq_getElem _ _ ht, List.getD_eq_getElem _ _ hu] at h'
    rw [toNat_toWord (by omega), toNat_toWord (by omega)] at h'
    exact ((hnd.getElem_inj_iff).1 h'.symm)
  · rintro rfl; rfl

theorem fct_eq {Jl : List ℕ} (hnd : Jl.Nodup) (hJ : ∀ j ∈ Jl, j < nMax) {t u : ℕ}
    (ht : t < Jl.length) (hu : u < Jl.length) :
    wB (fct (jw Jl t) (jw Jl u)) = if u = t then 1 else wB (jw Jl t ^^^ jw Jl u) := by
  by_cases h : u = t
  · subst h
    rw [if_pos rfl, fct, BitVec.xor_self, decide_eq_true rfl]
    rfl
  · rw [if_neg h, fct, decide_eq_false (fun e => h ((jw_inj hnd hJ ht hu).1 e))]
    simp [bW]

/-- **The machine's value is the interpolation** (`J` without repeats, below `2^20`; `s < 2^20`). -/
theorem lagVal_eq {Jl : List ℕ} (hnd : Jl.Nodup) (hJ : ∀ j ∈ Jl, j < nMax) {s : ℕ}
    (y : ℕ → F) : lagVal Jl Jl.length s y = interpF D Jl.toFinset y s := by
  have hget : ∀ t < Jl.length, Jl.getD t 0 ∈ Jl := fun t ht => by
    rw [List.getD_eq_getElem _ _ ht]; exact List.getElem_mem ht
  unfold interpF
  simp only [Algebra.algebraMap_self, RingHom.id_apply]
  rw [sum_toFinset hnd]
  refine Finset.sum_congr rfl fun t ht => ?_
  have ht' := Finset.mem_range.1 ht
  rw [prod_erase_ite (List.mem_toFinset.2 (hget t ht')), prod_toFinset hnd]
  have e1 : ∀ u ∈ range Jl.length, (if Jl.getD u 0 = Jl.getD t 0 then (1 : F) else
      (D s - D (Jl.getD u 0)) / (D (Jl.getD t 0) - D (Jl.getD u 0))) =
      F.ofB64 (if u = t then 1 else dif Jl s u) *
        (F.ofB64 (if u = t then 1 else wB (jw Jl t ^^^ jw Jl u)))⁻¹ := fun u hu => by
    have hu' := Finset.mem_range.1 hu
    have hJu : Jl.getD u 0 = Jl.getD t 0 ↔ u = t := by
      rw [List.getD_eq_getElem _ _ hu', List.getD_eq_getElem _ _ ht']
      exact hnd.getElem_inj_iff
    by_cases h : u = t
    · rw [if_pos (hJu.2 h), if_pos h, if_pos h]
      show (1 : F) = F.ofB64 1 * (F.ofB64 1)⁻¹
      rw [show F.ofB64 1 = 1 from rfl, inv_one, mul_one]
    · rw [if_neg (fun e => h (hJu.1 e)), if_neg h, if_neg h, D_sub_D, D_sub_D, div_eq_mul_inv]
      rfl
  rw [Finset.prod_congr rfl e1, Finset.prod_mul_distrib, ← ofB64_prod, Finset.prod_inv_distrib,
    ← ofB64_prod]
  rw [lagTerm, yv, wgtB, F.smulBase_eq_mul, F.smulBase_eq_mul, preP, sufP, pre_suf ht',
    ofB64_inv]
  have e2 : ∏ m ∈ range Jl.length, wB (fct (jw Jl t) (jw Jl m)) =
      ∏ u ∈ range Jl.length, if u = t then 1 else wB (jw Jl t ^^^ jw Jl u) :=
    Finset.prod_congr rfl fun u hu => fct_eq hnd hJ ht' (Finset.mem_range.1 hu)
  rw [e2]
  ring

/-! ## The machine: helpers -/

theorem ld_M (I : Array Word) (s : St) {d a x : ℕ} (ha : rd s.M a = toWord x) (hx : x < 2 ^ 64) :
    semXIR I (.load d a) s = ⟨s.M.setIfInBounds d (rd s.M x), s.o⟩ := by
  simp only [semXIR, ha, toNat_toWord hx]

theorem inv_set {M : Mem} (hM : Inv M) {d : ℕ} (hd : 4 ≤ d) (v : Word) : Inv (M.setIfInBounds d v) :=
  inv_of_frame hM (size_set ..) fun i hi => rd_set_ne (by omega)

/-- A store to the heap cell `x` (`M[a] = x`), under `Inv`: `x` gets `M[v]`. -/
theorem st_rd (I : Array Word) (s : St) (hM : Inv s.M) {a v x : ℕ} (ha : rd s.M a = toWord x)
    (hx : regs ≤ x) (hx2 : x < 2 ^ 64) (hxs : x < s.M.size) (haT : a ≠ cTmp) (hvT : v ≠ cTmp) {i : ℕ}
    (hi : i ≠ cTmp) : rd (semXIR I (.store a v) s).M i = if i = x then rd s.M v else rd s.M i :=
  rd_storeM hM ha hx hx2 hxs haT hvT hi

theorem lo_wInL : Lo wInL := by
  simp [wInL, Lo, mulBC, redC, Prim.dst, lgJ, lgD, lgZ, lgA, lgP, regs]

theorem wf_wInL : WF wInL := by
  simp [wInL, WF, mulBC, redC, Prim.dst, lgJ, lgD, lgZ, lgA, lgP]

/-! ## The weights and the values -/

/-- **One factor of the weight.** -/
theorem wInL_sem (I : Array Word) (s : St) (hM : Inv s.M) {x : ℕ} (hA : rd s.M lgA = toWord x)
    (hx : x + 1 < 2 ^ 64) :
    rd (semXIR I wInL s).M lgA = toWord (x + 1) ∧
    rdB (semXIR I wInL s).M lgP = rdB s.M lgP * wB (fct (rd s.M lgT) (rd s.M x)) := by
  have hs : 256 ≤ s.M.size := hM.1
  have h1 : rd s.M cOne = 1 := hM.2 0 (by decide)
  have e : (semXIR I wInL s).M = runPrims (mulBC lgP lgP lgD) (runPrims [.op .xor lgD lgT lgJ,
      .op .eq lgZ lgT lgJ, .op .or lgD lgD lgZ, .op .add lgA lgA cOne]
      (s.M.setIfInBounds lgJ (rd s.M x))) := by
    rw [wInL, semXIR_seq, ld_M I s hA (by omega), sem_blk, runPrims_append]
  have hI : Inv (runPrims [.op .xor lgD lgT lgJ, .op .eq lgZ lgT lgJ, .op .or lgD lgD lgZ,
      .op .add lgA lgA cOne] (s.M.setIfInBounds lgJ (rd s.M x))) :=
    inv_runPrims (by simp [Prim.dst, lgD, lgZ, lgA]) (inv_set hM (by decide) _)
  rw [e]
  constructor
  · rw [mulBC_frame _ _ _ (by simp only [lgA]; omega) (by decide)]
    simp only [runPrims_cons, runPrims_nil, Prim.run]
    simp (disch := first | decide | (simp only [size_set, lgA, lgZ, lgD, lgJ]; omega)) only
      [rd_set_self, rd_set_ne]
    rw [hA, h1, add_one_toWord]
  · rw [rdB, mulBC_run hI (by decide) (by decide) (by decide) (by decide), mulBW_spec]
    simp only [rdB, runPrims_cons, runPrims_nil, Prim.run]
    simp (disch := first | decide | (simp only [size_set, lgA, lgZ, lgD, lgJ]; omega)) only
      [rd_set_self, rd_set_ne, eval_xor, eval_or, eq_bW]
    rfl

/-- **The weight's product**: from `P = 1`, `lgA = jb`, `k` factors over `J` at `jb`. -/
theorem wLoop_sem (I : Array Word) (s : St) (hM : Inv s.M) {k jb : ℕ} {J : ℕ → ℕ}
    (hk : k < 2 ^ 64) (hjb : regs ≤ jb) (hjb2 : jb + k < 2 ^ 64)
    (hA : rd s.M lgA = toWord jb) (hN : rd s.M lgN2 = toWord k) (hP : rdB s.M lgP = 1)
    (hJ : ∀ m < k, rd s.M (jb + m) = toWord (J m)) :
    rdB (semXIR I (.loopK lgC2 lgN2 (toWord k) wInL) s).M lgP =
      ∏ m ∈ range k, wB (fct (rd s.M lgT) (toWord (J m))) := by
  let P : ℕ → St → Prop := fun j st => Inv st.M ∧ rd st.M lgA = toWord (jb + j) ∧
    rdB st.M lgP = ∏ m ∈ range j, wB (fct (rd s.M lgT) (toWord (J m))) ∧
    rd st.M lgT = rd s.M lgT ∧ ∀ x, regs ≤ x → rd st.M x = rd s.M x
  have ef : ∀ i, i ≠ lgC2 → i ≠ cTmp → rd (entryK lgC2 lgN2 (toWord k) s.M) i = rd s.M i :=
    fun i a b => entryK_frame _ (Ne.symm a) (Ne.symm b)
  refine (loopK_run I wInL P s hM (by decide) (by decide) (by decide) hN hk ⟨inv_entryK hM (by decide),
    by rw [ef _ (by decide) (by decide), hA, Nat.add_zero], by
      rw [rdB, ef _ (by decide) (by decide), ← rdB, hP, Finset.prod_range_zero],
    ef _ (by decide) (by decide), fun x hx => ef x (by simp only [regs, lgC2] at hx ⊢; omega)
      (by simp only [regs, cTmp] at hx ⊢; omega)⟩ ?_).2.2.1
  rintro j st hj ⟨hI, hA', hP', hT', hH⟩
  obtain ⟨b1, b2⟩ := wInL_sem I st hI hA' (by omega)
  have hI2 := inv_sem I wf_wInL hI
  refine ⟨inv_decS hI2 (by decide), by rw [rd_decS (by decide), b1, Nat.add_assoc], ?_, ?_,
    fun x hx => ?_⟩
  · rw [rdB, rd_decS (by decide), ← rdB, b2, hP', hT', hH _ (by omega), hJ j hj,
      Finset.prod_range_succ]
  · rw [rd_decS (by decide), frame I wInL st wf_wInL hI lgT (by decide) (by
      simp [wInL, Writes, mulBC, redC, Prim.dst, lgJ, lgD, lgZ, lgA, lgP, lgT]), hT']
  · rw [rd_decS (by simp only [regs, lgC2] at hx ⊢; omega), hframe I wInL st lo_wInL x hx, hH x hx]

theorem wf_yRowL : WF yRowL := by
  simp [yRowL, yLd, ySt, WF, mulBC, redC, Prim.dst, lgV, lgV1, lgX, lgY, cTmp]

theorem semB (I : Array Word) (ps : List Prim) (s : St) :
    semXIR I (.blk ps) s = ⟨runPrims ps s.M, s.o⟩ := rfl

/-- `r += 1`, then `a *= q`, `b *= q` (`B64`). -/
theorem amm_run {M : Mem} (hM : Inv M) {r a b q x : ℕ} (hr : 9 ≤ r) (hrr : r < regs)
    (ha : 9 ≤ a) (har : a < regs) (hb : 9 ≤ b) (hbr : b < regs) (hq : 9 ≤ q) (hra : r ≠ a)
    (hrb : r ≠ b) (hab : a ≠ b) (hbq : b ≠ q) (haq : a ≠ q) (hrq : r ≠ q) (hR : rd M r = toWord x) :
    rd (runPrims ([.op .add r r cOne] ++ mulBC a a q ++ mulBC b b q) M) r = toWord (x + 1) ∧
    rd (runPrims ([.op .add r r cOne] ++ mulBC a a q ++ mulBC b b q) M) a = mulBW (rd M a) (rd M q) ∧
    rd (runPrims ([.op .add r r cOne] ++ mulBC a a q ++ mulBC b b q) M) b = mulBW (rd M b) (rd M q) ∧
    ∀ i, i ≠ r → i ≠ a → i ≠ b → (i < 5 ∨ 9 ≤ i) →
      rd (runPrims ([.op .add r r cOne] ++ mulBC a a q ++ mulBC b b q) M) i = rd M i := by
  obtain ⟨i1, i1f⟩ := incr_sem M hM (r := r) (x := x) hrr (by omega) hR
  have hM1 : Inv (runPrims [.op .add r r cOne] M) := inv_runPrims (by simp [Prim.dst]; omega) hM
  have hM2 := mulBC_inv a a q (by omega) hM1
  simp only [runPrims_append]
  refine ⟨?_, ?_, ?_, fun i h1 h2 h3 h4 => ?_⟩
  · rw [mulBC_frame _ _ _ (by omega) hrb, mulBC_frame _ _ _ (by omega) hra, i1]
  · rw [mulBC_frame _ _ _ (by omega) hab, mulBC_run hM1 ha har ha hq, i1f _ (Ne.symm hra),
      i1f _ (Ne.symm hrq)]
  · rw [mulBC_run hM2 hb hbr hb hq, mulBC_frame _ _ _ (by omega) (Ne.symm hab),
      mulBC_frame _ _ _ (by omega) (Ne.symm haq), i1f _ (Ne.symm hrb), i1f _ (Ne.symm hrq)]
  · rw [mulBC_frame _ _ _ h4 h3, mulBC_frame _ _ _ h4 h2, i1f _ h1]

/-- The loads of one value. -/
theorem yLd_sem (I : Array Word) (s : St) (hM : Inv s.M) {x : ℕ} (hX : rd s.M lgX = toWord x)
    (hx : regs ≤ x) (hx2 : x + 2 < 2 ^ 64) :
    rd (semXIR I yLd s).M lgX = toWord (x + 2) ∧
    rd (semXIR I yLd s).M lgV = mulBW (rd s.M x) (rd s.M lgQ) ∧
    rd (semXIR I yLd s).M lgV1 = mulBW (rd s.M (x + 1)) (rd s.M lgQ) ∧
    (∀ i, i ≠ lgX → i ≠ lgV → i ≠ lgV1 → (i < 5 ∨ 9 ≤ i) → rd (semXIR I yLd s).M i = rd s.M i) ∧
    (semXIR I yLd s).o = s.o := by
  simp only [regs] at hx
  rw [yLd, semXIR_seq]
  obtain ⟨l1, l1f⟩ := bload_sem I s hM (d := lgV) (a := lgX) (x := x) (by decide) hX (by omega)
  have hM1 := inv_sem I (P := .load lgV lgX) (by simp [WF, lgV]) hM
  have o1 : (semXIR I (.load lgV lgX) s).o = s.o := rfl
  generalize semXIR I (.load lgV lgX) s = s1 at l1 l1f hM1 o1
  rw [semXIR_seq, semB]
  obtain ⟨i2, i2f⟩ := incr_sem s1.M hM1 (r := lgX) (x := x) (by decide) (by decide)
    ((l1f _ (by decide)).trans hX)
  have hM2 : Inv (runPrims [.op .add lgX lgX cOne] s1.M) := inv_runPrims (by simp [Prim.dst, lgX]) hM1
  generalize runPrims [.op .add lgX lgX cOne] s1.M = M2 at i2 i2f hM2
  rw [semXIR_seq]
  obtain ⟨l3, l3f⟩ := bload_sem I ⟨M2, s1.o⟩ hM2 (d := lgV1) (a := lgX) (x := x + 1) (by decide) i2
    (by omega)
  have hM3 := inv_sem I (P := .load lgV1 lgX) (s := ⟨M2, s1.o⟩) (by simp [WF, lgV1]) hM2
  have o3 : (semXIR I (.load lgV1 lgX) ⟨M2, s1.o⟩).o = s1.o := rfl
  generalize semXIR I (.load lgV1 lgX) ⟨M2, s1.o⟩ = s3 at l3 l3f hM3 o3
  rw [semB]
  have hX3 : rd s3.M lgX = toWord (x + 1) := (l3f _ (by decide)).trans i2
  obtain ⟨a1, a2, a3, a4⟩ := amm_run hM3 (r := lgX) (a := lgV) (b := lgV1) (q := lgQ) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) hX3
  have hb : ∀ i, i ≠ lgX → i ≠ lgV → i ≠ lgV1 → rd s3.M i = rd s.M i := fun i h1 h2 h3 =>
    (l3f _ h3).trans ((i2f _ h1).trans (l1f _ h2))
  dsimp only
  generalize runPrims ([.op .add lgX lgX cOne] ++ mulBC lgV lgV lgQ ++ mulBC lgV1 lgV1 lgQ) s3.M = M4
    at a1 a2 a3 a4 ⊢
  refine ⟨a1.trans (congrArg toWord (by omega)), ?_, ?_,
    fun i h1 h2 h3 h4 => (a4 i h1 h2 h3 h4).trans (hb i h1 h2 h3), o3.trans o1⟩
  · rw [a2, hb lgQ (by decide) (by decide) (by decide), l3f lgV (by decide),
      i2f lgV (by decide), l1]
  · rw [a3, hb lgQ (by decide) (by decide) (by decide), l3,
      i2f _ (by simp only [lgX]; omega), l1f _ (by simp only [lgV]; omega)]

/-- The stores of one value. -/
theorem ySt_sem (I : Array Word) (s : St) (hM : Inv s.M) {y : ℕ} (hY : rd s.M lgY = toWord y)
    (hy : regs ≤ y) (hy2 : y + 2 < 2 ^ 64) (hys : y + 1 < s.M.size) :
    rd (semXIR I ySt s).M lgY = toWord (y + 2) ∧ rd (semXIR I ySt s).M y = rd s.M lgV ∧
    rd (semXIR I ySt s).M (y + 1) = rd s.M lgV1 ∧
    (∀ i, i ≠ lgY → i ≠ y → i ≠ y + 1 → i ≠ cTmp → rd (semXIR I ySt s).M i = rd s.M i) ∧
    Inv (semXIR I ySt s).M := by
  simp only [regs] at hy
  rw [ySt, semXIR_seq]
  have a1 := fun i (hi : i ≠ cTmp) => st_rd I s hM hY (by simp only [regs]; omega) (by omega)
    (by omega) (by decide) (by decide) (v := lgV) hi
  have hM1 := inv_sem I (P := .store lgY lgV) (by simp [WF, lgY, cTmp]) hM
  have z1 := size_sem I (.store lgY lgV) s
  generalize semXIR I (.store lgY lgV) s = s1 at a1 hM1 z1
  rw [semXIR_seq]
  obtain ⟨i2, i2f⟩ := incr_sem s1.M hM1 (r := lgY) (x := y) (by decide) (by decide)
    ((a1 _ (by decide)).trans (by rw [if_neg (by simp only [lgY]; omega), hY]))
  have hM2 : Inv (runPrims [.op .add lgY lgY cOne] s1.M) := inv_runPrims (by simp [Prim.dst, lgY]) hM1
  rw [semB]
  have z2 := size_runPrims [.op .add lgY lgY cOne] s1.M
  generalize runPrims [.op .add lgY lgY cOne] s1.M = M2 at i2 i2f hM2 z2
  rw [semXIR_seq]
  have a3 := fun i (hi : i ≠ cTmp) => st_rd I ⟨M2, s1.o⟩ hM2 i2 (by simp only [regs]; omega)
    (by omega) (by show y + 1 < M2.size; omega) (by decide) (by decide) (v := lgV1) hi
  have hM3 := inv_sem I (P := .store lgY lgV1) (s := ⟨M2, s1.o⟩) (by simp [WF, lgY, cTmp]) hM2
  generalize semXIR I (.store lgY lgV1) ⟨M2, s1.o⟩ = s3 at a3 hM3
  rw [semB]
  obtain ⟨i4, i4f⟩ := incr_sem s3.M hM3 (r := lgY) (x := y + 1) (by decide) (by decide)
    ((a3 _ (by decide)).trans (by rw [if_neg (by simp only [lgY]; omega)]; exact i2))
  have hM4 : Inv (runPrims [.op .add lgY lgY cOne] s3.M) := inv_runPrims (by simp [Prim.dst, lgY]) hM3
  have hf : ∀ i, i ≠ lgY → i ≠ y → i ≠ y + 1 → i ≠ cTmp →
      rd (runPrims [.op .add lgY lgY cOne] s3.M) i = rd s.M i := fun i h1 h2 h3 h4 => by
    rw [i4f _ h1, a3 _ h4, if_neg h3, i2f _ h1, a1 _ h4, if_neg h2]
  refine ⟨i4.trans (congrArg toWord (by omega)), ?_, ?_, hf, hM4⟩
  · rw [i4f _ (by simp only [lgY]; omega), a3 _ (by simp only [cTmp]; omega), if_neg (by omega),
      i2f _ (by simp only [lgY]; omega), a1 _ (by simp only [cTmp]; omega), if_pos rfl]
  · rw [i4f _ (by simp only [lgY]; omega), a3 _ (by simp only [cTmp]; omega), if_pos rfl,
      i2f _ (by decide), a1 _ (by decide), if_neg (by simp only [lgV1]; omega)]

theorem wf_yLd : WF yLd := by simp [yLd, WF, mulBC, redC, Prim.dst, lgV, lgV1, lgX]

/-- **One value**, both halves. -/
theorem yRowL_sem (I : Array Word) (s : St) (hM : Inv s.M) {x y : ℕ} (hX : rd s.M lgX = toWord x)
    (hY : rd s.M lgY = toWord y) (hx : regs ≤ x) (hx2 : x + 2 < 2 ^ 64) (hy : regs ≤ y)
    (hy2 : y + 2 < 2 ^ 64) (hys : y + 1 < s.M.size) :
    rd (semXIR I yRowL s).M lgX = toWord (x + 2) ∧ rd (semXIR I yRowL s).M lgY = toWord (y + 2) ∧
    rd (semXIR I yRowL s).M y = mulBW (rd s.M x) (rd s.M lgQ) ∧
    rd (semXIR I yRowL s).M (y + 1) = mulBW (rd s.M (x + 1)) (rd s.M lgQ) ∧
    (∀ i, i ≠ lgX → i ≠ lgY → i ≠ lgV → i ≠ lgV1 → i ≠ y → i ≠ y + 1 → i ≠ cTmp → (i < 5 ∨ 9 ≤ i) →
      rd (semXIR I yRowL s).M i = rd s.M i) ∧
    Inv (semXIR I yRowL s).M := by
  rw [yRowL, semXIR_seq]
  obtain ⟨a1, a2, a3, a4, -⟩ := yLd_sem I s hM hX hx hx2
  have hM1 := inv_sem I wf_yLd hM
  have z1 := size_sem I yLd s
  generalize semXIR I yLd s = s1 at a1 a2 a3 a4 hM1 z1
  obtain ⟨b1, b2, b3, b4, hM2⟩ := ySt_sem I s1 hM1 (y := y)
    ((a4 _ (by decide) (by decide) (by decide) (by decide)).trans hY) hy hy2 (by omega)
  refine ⟨?_, b1, by rw [b2, a2], by rw [b3, a3], fun i h1 h2 h3 h4 h5 h6 h7 h8 => ?_, hM2⟩
  · rw [b4 _ (by decide) (by simp only [regs] at hy; simp only [lgX]; omega)
      (by simp only [regs] at hy; simp only [lgX]; omega) (by decide), a1]
  · rw [b4 _ h2 h5 h6 h7, a4 _ h1 h3 h4 h8]

/-- **The `C` values of one position**: `Y[y₀ + 2c] = M[x₀ + 2c] · W`, `Y[y₀ + 2c + 1] =
M[x₀ + 2c + 1] · W`. -/
theorem yLoop_sem (I : Array Word) (s : St) (hM : Inv s.M) {C x0 y0 : ℕ} (hC : C < 2 ^ 64)
    (hX : rd s.M lgX = toWord x0) (hY : rd s.M lgY = toWord y0) (hN : rd s.M lgN2 = toWord C)
    (hx : regs ≤ x0) (hx2 : x0 + 2 * C + 2 < 2 ^ 64) (hy : regs ≤ y0) (hy2 : y0 + 2 * C + 2 < 2 ^ 64)
    (hys : y0 + 2 * C ≤ s.M.size) (hxy : y0 + 2 * C ≤ x0) :
    rd (semXIR I (.loopK lgC2 lgN2 (toWord C) yRowL) s).M lgY = toWord (y0 + 2 * C) ∧
    (∀ c < C, rd (semXIR I (.loopK lgC2 lgN2 (toWord C) yRowL) s).M (y0 + 2 * c) =
        mulBW (rd s.M (x0 + 2 * c)) (rd s.M lgQ) ∧
      rd (semXIR I (.loopK lgC2 lgN2 (toWord C) yRowL) s).M (y0 + 2 * c + 1) =
        mulBW (rd s.M (x0 + 2 * c + 1)) (rd s.M lgQ)) ∧
    (∀ i, regs ≤ i → (i < y0 ∨ y0 + 2 * C ≤ i) →
      rd (semXIR I (.loopK lgC2 lgN2 (toWord C) yRowL) s).M i = rd s.M i) ∧
    Inv (semXIR I (.loopK lgC2 lgN2 (toWord C) yRowL) s).M := by
  simp only [regs] at hx hy
  let P : ℕ → St → Prop := fun j st => Inv st.M ∧ st.M.size = s.M.size ∧
    rd st.M lgX = toWord (x0 + 2 * j) ∧ rd st.M lgY = toWord (y0 + 2 * j) ∧
    rd st.M lgQ = rd s.M lgQ ∧
    (∀ c < j, rd st.M (y0 + 2 * c) = mulBW (rd s.M (x0 + 2 * c)) (rd s.M lgQ) ∧
      rd st.M (y0 + 2 * c + 1) = mulBW (rd s.M (x0 + 2 * c + 1)) (rd s.M lgQ)) ∧
    (∀ i, regs ≤ i → (i < y0 ∨ y0 + 2 * j ≤ i) → rd st.M i = rd s.M i)
  have ef : ∀ i, i ≠ lgC2 → i ≠ cTmp → rd (entryK lgC2 lgN2 (toWord C) s.M) i = rd s.M i :=
    fun i a b => entryK_frame _ (Ne.symm a) (Ne.symm b)
  have h := loopK_run I yRowL P s hM (by decide) (by decide) (by decide) hN hC
    ⟨inv_entryK hM (by decide), size_entryK .., by rw [ef _ (by decide) (by decide), hX]; rfl,
      by rw [ef _ (by decide) (by decide), hY]; rfl, ef _ (by decide) (by decide),
      fun c hc => absurd hc (Nat.not_lt_zero _),
      fun i hi _ => ef i (by simp only [regs, lgC2] at hi ⊢; omega)
        (by simp only [regs, cTmp] at hi ⊢; omega)⟩ ?_
  · exact ⟨h.2.2.2.1, h.2.2.2.2.2.1, fun i hi hi2 => h.2.2.2.2.2.2 i hi hi2, h.1⟩
  rintro j st hj ⟨hI, hz, hX', hY', hQ, hV, hH⟩
  have hxr : rd st.M (x0 + 2 * j) = rd s.M (x0 + 2 * j) := hH _ (by simp only [regs]; omega)
    (.inr (by omega))
  have hxr1 : rd st.M (x0 + 2 * j + 1) = rd s.M (x0 + 2 * j + 1) := hH _ (by simp only [regs]; omega)
    (.inr (by omega))
  obtain ⟨b1, b2, b3, b4, b5, hI2⟩ := yRowL_sem I st hI hX' hY' (by simp only [regs]; omega)
    (by omega) (by simp only [regs]; omega) (by omega) (by omega)
  refine ⟨inv_decS hI2 (by decide), by rw [size_decS, size_sem, hz], ?_, ?_, ?_, fun c hc => ?_,
    fun i hi hi2 => ?_⟩
  · rw [rd_decS (by decide), b1]; exact congrArg toWord (by omega)
  · rw [rd_decS (by decide), b2]; exact congrArg toWord (by omega)
  · rw [rd_decS (by decide), b5 _ (by decide) (by decide) (by decide) (by decide)
      (by simp only [lgQ]; omega) (by simp only [lgQ]; omega) (by decide)
      (by decide), hQ]
  · rw [rd_decS (by simp only [lgC2]; omega), rd_decS (by simp only [lgC2]; omega)]
    rcases Nat.lt_succ_iff_lt_or_eq.1 hc with hc | rfl
    · rw [b5 (y0 + 2 * c) (by simp only [lgX]; omega) (by simp only [lgY]; omega)
          (by simp only [lgV]; omega) (by simp only [lgV1]; omega) (by omega) (by omega)
          (by simp only [cTmp]; omega) (.inr (by omega)),
        b5 (y0 + 2 * c + 1) (by simp only [lgX]; omega) (by simp only [lgY]; omega)
          (by simp only [lgV]; omega) (by simp only [lgV1]; omega) (by omega) (by omega)
          (by simp only [cTmp]; omega) (.inr (by omega))]
      exact hV c hc
    · rw [b3, b4, hxr, hxr1, hQ]; exact ⟨rfl, rfl⟩
  · simp only [regs] at hi
    rw [rd_decS (by simp only [lgC2]; omega), b5 _ (by simp only [lgX]; omega)
      (by simp only [lgY]; omega) (by simp only [lgV]; omega) (by simp only [lgV1]; omega)
      (by omega) (by omega) (by simp only [cTmp]; omega) (.inr (by omega)),
      hH i (by simp only [regs]; omega) (by omega)]

theorem loK_wInL : LoK wInL := by
  simp [wInL, LoK, mulBC, redC, Prim.dst, lgJ, lgD, lgZ, lgA, lgP, regs]

theorem wf_wLoop (k : ℕ) : WF (.loopK lgC2 lgN2 (toWord k) wInL) :=
  ⟨⟨by decide, by decide, by decide⟩, by decide, by
    simp [wInL, Writes, mulBC, redC, Prim.dst, lgJ, lgD, lgZ, lgA, lgP, lgC2], wf_wInL⟩

theorem nw_wLoop (k : ℕ) {i : ℕ} (h1 : i ≠ lgC2) (h2 : i ≠ cTmp) (h3 : i ≠ lgJ) (h4 : i ≠ lgD)
    (h5 : i ≠ lgZ) (h6 : i ≠ lgA) (h7 : i ≠ lgP) (h8 : i < 5 ∨ 9 ≤ i) :
    ¬ Writes (.loopK lgC2 lgN2 (toWord k) wInL) i := by
  simp only [Writes, wInL, mulBC, redC, Prim.dst, List.mem_append, List.mem_cons,
    List.not_mem_nil, or_false]
  rintro (h | h | h | ⟨p, hp, he⟩)
  · exact h1 h
  · exact h2 h
  · exact h3 h
  · rcases hp with (hp | hp | hp | hp) | (hp | hp) | hp | hp | hp | hp | hp <;> subst hp <;>
      simp only at he <;> subst he <;> simp_all

theorem wf_yLoop {C : ℕ} : WF (.loopK lgC2 lgN2 (toWord C) yRowL) :=
  ⟨⟨by decide, by decide, by decide⟩, by decide, by
    simp [yRowL, yLd, ySt, Writes, mulBC, redC, Prim.dst, lgV, lgV1, lgX, lgY, lgC2, cTmp], wf_yRowL⟩

theorem nwB_yLoop {C : ℕ} : ¬ Writes (.loopK lgC2 lgN2 (toWord C) yRowL) lgB := by
  simp [Writes, yRowL, yLd, ySt, mulBC, redC, Prim.dst, lgB, lgC2, lgV, lgV1, lgX, lgY, cTmp]

/-- **One position `t`** of the values: `Y[y₀ + 2c] = M[x₀ + 2c] · W_t` (`x₀ = cb + cs J_t + 2c₀`),
`lgB += 1`, `lgY += 2C`. -/
theorem wyBody_sem (I : Array Word) (s : St) (hM : Inv s.M) {k C jb cb cs c0 t y0 : ℕ}
    {J : ℕ → ℕ} (hk : k < 2 ^ 64) (hC : C < 2 ^ 64) (hjb : regs ≤ jb) (hjb2 : jb + k < 2 ^ 64)
    (ht : t < k) (hB : rd s.M lgB = toWord (jb + t)) (hY : rd s.M lgY = toWord y0)
    (hJ : ∀ m < k, rd s.M (jb + m) = toWord (J m))
    (hx : regs ≤ cb + cs * J t + 2 * c0) (hx2 : cb + cs * J t + 2 * c0 + 2 * C + 2 < 2 ^ 64)
    (hy : regs ≤ y0) (hy2 : y0 + 2 * C + 2 < 2 ^ 64) (hys : y0 + 2 * C ≤ s.M.size)
    (hxy : y0 + 2 * C ≤ cb + cs * J t + 2 * c0) (hjy : jb + k ≤ y0) :
    rd (semXIR I (wyBody k C jb cb cs c0) s).M lgB = toWord (jb + t + 1) ∧
    rd (semXIR I (wyBody k C jb cb cs c0) s).M lgY = toWord (y0 + 2 * C) ∧
    (∀ c < C, rdB (semXIR I (wyBody k C jb cb cs c0) s).M (y0 + 2 * c) =
        rdB s.M (cb + cs * J t + 2 * c0 + 2 * c) *
          (∏ m ∈ range k, wB (fct (toWord (J t)) (toWord (J m))))⁻¹ ∧
      rdB (semXIR I (wyBody k C jb cb cs c0) s).M (y0 + 2 * c + 1) =
        rdB s.M (cb + cs * J t + 2 * c0 + 2 * c + 1) *
          (∏ m ∈ range k, wB (fct (toWord (J t)) (toWord (J m))))⁻¹) ∧
    (∀ i, regs ≤ i → (i < y0 ∨ y0 + 2 * C ≤ i) →
      rd (semXIR I (wyBody k C jb cb cs c0) s).M i = rd s.M i) ∧
    Inv (semXIR I (wyBody k C jb cb cs c0) s).M := by
  have hs : 256 ≤ s.M.size := hM.1
  simp only [regs] at hjb hy hx
  simp only [wyBody, semXIR_seq, semB]
  -- `lgT := J_t`
  obtain ⟨l1, l1f⟩ := bload_sem I s hM (d := lgT) (a := lgB) (x := jb + t) (by decide) hB (by omega)
  rw [hJ t ht] at l1
  have hM1 := inv_sem I (P := .load lgT lgB) (by simp [WF, lgT]) hM
  have z1 := size_sem I (.load lgT lgB) s
  generalize semXIR I (.load lgT lgB) s = s1 at l1 l1f hM1 z1 ⊢
  -- the constants
  have hs1 : 256 ≤ s1.M.size := hM1.1
  have c1 : rd (runPrims [.const lgP 1, .const lgA (toWord jb), .const lgN2 (toWord k)] s1.M) lgP = 1 ∧
      rd (runPrims [.const lgP 1, .const lgA (toWord jb), .const lgN2 (toWord k)] s1.M) lgA =
        toWord jb ∧
      rd (runPrims [.const lgP 1, .const lgA (toWord jb), .const lgN2 (toWord k)] s1.M) lgN2 =
        toWord k := by
    simp only [runPrims_cons, runPrims_nil, Prim.run]
    refine ⟨?_, ?_, ?_⟩ <;>
    simp (disch := first | decide | (simp only [size_set, lgP, lgA, lgN2]; omega)) only
      [rd_set_self, rd_set_ne]
  have c1f : ∀ i, i ≠ lgP → i ≠ lgA → i ≠ lgN2 →
      rd (runPrims [.const lgP 1, .const lgA (toWord jb), .const lgN2 (toWord k)] s1.M) i =
        rd s1.M i := fun i a b c =>
    rd_runPrims_of_not_writes (by simp [Prim.dst]; exact ⟨Ne.symm a, Ne.symm b, Ne.symm c⟩) _
  have hM2 : Inv (runPrims [.const lgP 1, .const lgA (toWord jb), .const lgN2 (toWord k)] s1.M) :=
    inv_runPrims (by simp [Prim.dst, lgP, lgA, lgN2]) hM1
  have z2 := size_runPrims [.const lgP 1, .const lgA (toWord jb), .const lgN2 (toWord k)] s1.M
  generalize runPrims [.const lgP 1, .const lgA (toWord jb), .const lgN2 (toWord k)] s1.M = M2
    at c1 c1f hM2 z2 ⊢
  have hH2 : ∀ i, regs ≤ i → rd M2 i = rd s.M i := fun i hi => by
    simp only [regs] at hi
    rw [c1f _ (by simp only [lgP]; omega) (by simp only [lgA]; omega) (by simp only [lgN2]; omega),
      l1f _ (by simp only [lgT]; omega)]
  -- the weight's product
  have w3 := wLoop_sem I ⟨M2, s1.o⟩ hM2 (J := J) hk (by simp only [regs]; omega) hjb2 c1.2.1
    c1.2.2 (by show wB _ = 1; rw [c1.1]; rfl) (fun m hm => by
      show rd M2 _ = _; rw [hH2 _ (by simp only [regs]; omega), hJ m hm])
  have hT2 : rd M2 lgT = toWord (J t) := (c1f _ (by decide) (by decide) (by decide)).trans l1
  have hM3 := inv_sem I (wf_wLoop k) (s := ⟨M2, s1.o⟩) hM2
  have f3 : ∀ i, i < regs → i ≠ lgC2 → i ≠ cTmp → i ≠ lgJ → i ≠ lgD → i ≠ lgZ → i ≠ lgA →
      i ≠ lgP → (i < 5 ∨ 9 ≤ i) →
      rd (semXIR I (.loopK lgC2 lgN2 (toWord k) wInL) ⟨M2, s1.o⟩).M i = rd M2 i :=
    fun i hi h1 h2 h3 h4 h5 h6 h7 h8 => frame I _ _ (wf_wLoop k) hM2 i hi
      (nw_wLoop k h1 h2 h3 h4 h5 h6 h7 h8)
  have H3 : ∀ i, regs ≤ i →
      rd (semXIR I (.loopK lgC2 lgN2 (toWord k) wInL) ⟨M2, s1.o⟩).M i = rd M2 i :=
    hframeK I _ _ ⟨by decide, loK_wInL⟩
  have z3 := size_sem I (.loopK lgC2 lgN2 (toWord k) wInL) ⟨M2, s1.o⟩
  dsimp only at w3 z3
  rw [hT2] at w3
  generalize semXIR I (.loopK lgC2 lgN2 (toWord k) wInL) ⟨M2, s1.o⟩ = s3 at w3 hM3 f3 H3 z3 ⊢
  -- `W_t` and the column pointer
  have v4 := invB_sem (I := I) (s := s3) hM3 (d := lgQ) (a := lgP) (by decide) (by decide)
  rw [w3] at v4
  have f4 : ∀ i, i ≠ lgQ → (i < 5 ∨ 12 ≤ i) → rd (semXIR I (invB lgQ lgP) s3).M i = rd s3.M i :=
    fun i h1 h2 => by rw [invB, sem_blk]; exact invBC_frame lgQ lgP h2 h1 s3.M
  have hM4 := inv_sem I (wf_invB lgQ lgP (by decide)) hM3
  have z4 := size_sem I (invB lgQ lgP) s3
  generalize semXIR I (invB lgQ lgP) s3 = s4 at v4 f4 hM4 z4 ⊢
  have hs4 : 256 ≤ s4.M.size := hM4.1
  have hT4 : rd s4.M lgT = toWord (J t) := by
    rw [f4 _ (by decide) (by decide), f3 _ (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide) (by decide), hT2]
  have m5 : rd (runPrims (wyMid C cb cs c0) s4.M) lgX = toWord (cb + cs * J t + 2 * c0) ∧
      rd (runPrims (wyMid C cb cs c0) s4.M) lgN2 = toWord C := by
    simp only [wyMid, runPrims_cons, runPrims_nil, Prim.run]
    refine ⟨?_, ?_⟩ <;>
    simp (disch := first | decide | (simp only [size_set, lgX, lgK, lgN2]; omega)) only
      [rd_set_self, rd_set_ne]
    rw [hT4, mul_toWord, add_toWord]
    exact congrArg toWord (by ring)
  have m5f : ∀ i, i ≠ lgK → i ≠ lgX → i ≠ lgN2 → rd (runPrims (wyMid C cb cs c0) s4.M) i = rd s4.M i :=
    fun i a b c => rd_runPrims_of_not_writes (by
      simp [wyMid, Prim.dst]; exact ⟨Ne.symm a, Ne.symm b, Ne.symm a, Ne.symm b, Ne.symm c⟩) _
  have hM5 : Inv (runPrims (wyMid C cb cs c0) s4.M) :=
    inv_runPrims (by simp [wyMid, Prim.dst, lgK, lgX, lgN2]) hM4
  have z5 := size_runPrims (wyMid C cb cs c0) s4.M
  generalize runPrims (wyMid C cb cs c0) s4.M = M5 at m5 m5f hM5 z5 ⊢
  -- the values
  have H5 : ∀ i, regs ≤ i → rd M5 i = rd s.M i := fun i hi => by
    simp only [regs] at hi
    rw [m5f _ (by simp only [lgK]; omega) (by simp only [lgX]; omega) (by simp only [lgN2]; omega),
      f4 _ (by simp only [lgQ]; omega) (by omega), H3 i (by simp only [regs]; omega),
      hH2 i (by simp only [regs]; omega)]
  have hY5 : rd M5 lgY = toWord y0 := by
    rw [m5f _ (by decide) (by decide) (by decide), f4 _ (by decide) (by decide),
      f3 _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
        (by decide) (by decide), c1f _ (by decide) (by decide) (by decide),
      l1f _ (by decide), hY]
  have hQ5 : rd M5 lgQ = rd s4.M lgQ := m5f _ (by decide) (by decide) (by decide)
  obtain ⟨y1, y2, y3, hM6⟩ := yLoop_sem I ⟨M5, s4.o⟩ hM5 hC m5.1 hY5 m5.2
    (by simp only [regs]; omega) hx2 (by simp only [regs]; omega) hy2
    (by show _ ≤ M5.size; rw [z5, z4, z3, z2, z1]; omega) hxy
  dsimp only at y1 y2 y3
  have fB : rd (semXIR I (.loopK lgC2 lgN2 (toWord C) yRowL) ⟨M5, s4.o⟩).M lgB = rd M5 lgB :=
    frame I _ _ wf_yLoop hM5 lgB (by decide) nwB_yLoop
  generalize semXIR I (.loopK lgC2 lgN2 (toWord C) yRowL) ⟨M5, s4.o⟩ = s6 at y1 y2 y3 hM6 fB ⊢
  -- `lgB += 1`
  have hB6 : rd s6.M lgB = toWord (jb + t) := by
    rw [fB, m5f _ (by decide) (by decide) (by decide), f4 _ (by decide) (by decide),
      f3 _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
        (by decide) (by decide), c1f _ (by decide) (by decide) (by decide), l1f _ (by decide), hB]
  obtain ⟨i7, i7f⟩ := incr_sem s6.M hM6 (r := lgB) (x := jb + t) (by decide) (by decide) hB6
  have hM7 : Inv (runPrims [.op .add lgB lgB cOne] s6.M) := inv_runPrims (by simp [Prim.dst, lgB]) hM6
  generalize runPrims [.op .add lgB lgB cOne] s6.M = M7 at i7 i7f hM7 ⊢
  refine ⟨i7, ?_, fun c hc => ?_, fun i hi hi2 => ?_, hM7⟩
  · rw [i7f _ (by decide)]; exact y1
  · have hx5 := H5 (cb + cs * J t + 2 * c0 + 2 * c) (by simp only [regs]; omega)
    have hx6 := H5 (cb + cs * J t + 2 * c0 + 2 * c + 1) (by simp only [regs]; omega)
    have hW : wB (rd s4.M lgQ) = (∏ m ∈ range k, wB (fct (toWord (J t)) (toWord (J m))))⁻¹ := v4
    show wB (rd M7 (y0 + 2 * c)) = _ ∧ wB (rd M7 (y0 + 2 * c + 1)) = _
    rw [i7f (y0 + 2 * c) (by simp only [lgB]; omega), i7f (y0 + 2 * c + 1) (by simp only [lgB]; omega),
      (y2 c hc).1, (y2 c hc).2, mulBW_spec, mulBW_spec, hx5, hx6, hQ5, hW]
    exact ⟨rfl, rfl⟩
  · simp only [regs] at hi
    rw [i7f _ (by simp only [lgB]; omega), y3 i (by simp only [regs]; omega) hi2,
      H5 i (by simp only [regs]; omega)]

/-- The weight `W_t` over a position function `J`. -/
def wgtJ (J : ℕ → ℕ) (k t : ℕ) : B64 := (∏ m ∈ range k, wB (fct (toWord (J t)) (toWord (J m))))⁻¹

/-- **The values** `Y[yb + 2(Ct + c)] = y_{c₀+c}(J_t) · W_t` (two words each) for `t < k`, `c < C`;
the heap outside `[yb, yb + 2Ck)` is kept. -/
theorem yTab_sem (I : Array Word) (s : St) (hM : Inv s.M) {k C jb yb cb cs c0 : ℕ} {J : ℕ → ℕ}
    (hk : k < 2 ^ 64) (hC : C < 2 ^ 64) (hjb : regs ≤ jb) (hjy : jb + k ≤ yb)
    (hy2 : yb + 2 * C * k + 2 < 2 ^ 64) (hys : yb + 2 * C * k ≤ s.M.size)
    (hcb : yb + 2 * C * k ≤ cb) (hcb2 : ∀ t < k, cb + cs * J t + 2 * c0 + 2 * C + 2 < 2 ^ 64)
    (hJ : ∀ t < k, rd s.M (jb + t) = toWord (J t)) :
    (∀ t < k, ∀ c < C,
      rdB (semXIR I (yTabIR k C jb yb cb cs c0) s).M (yb + 2 * (C * t + c)) =
        rdB s.M (cb + cs * J t + 2 * c0 + 2 * c) * wgtJ J k t ∧
      rdB (semXIR I (yTabIR k C jb yb cb cs c0) s).M (yb + 2 * (C * t + c) + 1) =
        rdB s.M (cb + cs * J t + 2 * c0 + 2 * c + 1) * wgtJ J k t) ∧
    (∀ i, regs ≤ i → (i < yb ∨ yb + 2 * C * k ≤ i) →
      rd (semXIR I (yTabIR k C jb yb cb cs c0) s).M i = rd s.M i) ∧
    Inv (semXIR I (yTabIR k C jb yb cb cs c0) s).M := by
  have hs : 256 ≤ s.M.size := hM.1
  simp only [regs] at hjb
  rw [yTabIR, semXIR_seq, semB]
  have c1 : rd (runPrims [.const lgB (toWord jb), .const lgY (toWord yb), .const lgN1 (toWord k)] s.M)
      lgB = toWord jb ∧
      rd (runPrims [.const lgB (toWord jb), .const lgY (toWord yb), .const lgN1 (toWord k)] s.M)
        lgY = toWord yb ∧
      rd (runPrims [.const lgB (toWord jb), .const lgY (toWord yb), .const lgN1 (toWord k)] s.M)
        lgN1 = toWord k := by
    simp only [runPrims_cons, runPrims_nil, Prim.run]
    refine ⟨?_, ?_, ?_⟩ <;>
    simp (disch := first | decide | (simp only [size_set, lgB, lgY, lgN1]; omega)) only
      [rd_set_self, rd_set_ne]
  have c1f : ∀ i, regs ≤ i →
      rd (runPrims [.const lgB (toWord jb), .const lgY (toWord yb), .const lgN1 (toWord k)] s.M) i =
        rd s.M i := fun i hi =>
    rd_runPrims_of_not_writes (by simp only [regs] at hi; simp [Prim.dst, lgB, lgY, lgN1]; omega) _
  have hM1 : Inv (runPrims [.const lgB (toWord jb), .const lgY (toWord yb), .const lgN1 (toWord k)]
      s.M) := inv_runPrims (by simp [Prim.dst, lgB, lgY, lgN1]) hM
  have z1 := size_runPrims [.const lgB (toWord jb), .const lgY (toWord yb), .const lgN1 (toWord k)] s.M
  generalize runPrims [.const lgB (toWord jb), .const lgY (toWord yb), .const lgN1 (toWord k)] s.M
    = M1 at c1 c1f hM1 z1 ⊢
  let P : ℕ → St → Prop := fun j st => Inv st.M ∧ st.M.size = s.M.size ∧
    rd st.M lgB = toWord (jb + j) ∧ rd st.M lgY = toWord (yb + 2 * C * j) ∧
    (∀ t < j, ∀ c < C,
      rdB st.M (yb + 2 * (C * t + c)) = rdB s.M (cb + cs * J t + 2 * c0 + 2 * c) * wgtJ J k t ∧
      rdB st.M (yb + 2 * (C * t + c) + 1) =
        rdB s.M (cb + cs * J t + 2 * c0 + 2 * c + 1) * wgtJ J k t) ∧
    (∀ i, regs ≤ i → (i < yb ∨ yb + 2 * C * j ≤ i) → rd st.M i = rd s.M i)
  have ef : ∀ i, i ≠ lgC1 → i ≠ cTmp → rd (entryK lgC1 lgN1 (toWord k) M1) i = rd M1 i :=
    fun i a b => entryK_frame _ (Ne.symm a) (Ne.symm b)
  have h := loopK_run I (wyBody k C jb cb cs c0) P ⟨M1, s.o⟩ hM1 (by decide) (by decide) (by decide)
    c1.2.2 hk ⟨inv_entryK hM1 (by decide), by rw [size_entryK, z1],
      by rw [ef _ (by decide) (by decide), c1.1, Nat.add_zero],
      by rw [ef _ (by decide) (by decide), c1.2.1, Nat.mul_zero, Nat.add_zero],
      fun t ht => absurd ht (Nat.not_lt_zero _),
      fun i hi _ => (ef i (by simp only [regs, lgC1] at hi ⊢; omega)
        (by simp only [regs, cTmp] at hi ⊢; omega)).trans (c1f i hi)⟩ ?_
  · exact ⟨h.2.2.2.2.1, fun i hi hi2 => h.2.2.2.2.2 i hi hi2, h.1⟩
  rintro j st hj ⟨hI, hz, hB', hY', hV, hH⟩
  have hcj := hcb2 j hj
  have hCj : 2 * C * (j + 1) ≤ 2 * C * k := Nat.mul_le_mul_left _ hj
  obtain ⟨b1, b2, b3, b4, hI2⟩ := wyBody_sem I st hI (J := J) (y0 := yb + 2 * C * j) (cb := cb)
    (cs := cs) (c0 := c0) hk hC
    (by simp only [regs]; omega) (by omega) hj hB' hY'
    (fun m hm => by rw [hH _ (by simp only [regs]; omega) (.inl (by omega)), hJ m hm])
    (by simp only [regs]; omega) (by omega) (by simp only [regs]; omega)
    (by rw [Nat.mul_succ] at hCj; omega) (by rw [hz]; rw [Nat.mul_succ] at hCj; omega)
    (by rw [Nat.mul_succ] at hCj; omega) (by omega)
  have hx : ∀ c < C, ∀ e < 2, rd st.M (cb + cs * J j + 2 * c0 + 2 * c + e) =
      rd s.M (cb + cs * J j + 2 * c0 + 2 * c + e) := fun c hc e he =>
    hH _ (by simp only [regs]; omega) (.inr (by nlinarith))
  refine ⟨inv_decS hI2 (by decide), by rw [size_decS, size_sem, hz], ?_, ?_, fun t ht c hc => ?_,
    fun i hi hi2 => ?_⟩
  · rw [rd_decS (by decide), b1]; exact congrArg toWord (by omega)
  · rw [rd_decS (by decide), b2]; exact congrArg toWord (by ring)
  · have hr : ∀ a, regs ≤ a → rdB (decS lgC1 (semXIR I (wyBody k C jb cb cs c0) st)).M a =
        rdB (semXIR I (wyBody k C jb cb cs c0) st).M a := fun a ha => by
      simp only [regs] at ha; rw [rdB, rd_decS (by simp only [lgC1]; omega), ← rdB]
    have hCt : C * t + c < C * k :=
      lt_of_lt_of_le (Nat.add_lt_add_left hc _) (by rw [← Nat.mul_succ]; exact Nat.mul_le_mul_left _ (by omega))
    rw [hr _ (by simp only [regs]; omega), hr _ (by simp only [regs]; omega)]
    rcases Nat.lt_succ_iff_lt_or_eq.1 ht with ht | rfl
    · have hCt' : C * t + c < C * j :=
        lt_of_lt_of_le (Nat.add_lt_add_left hc _) (by rw [← Nat.mul_succ]; exact Nat.mul_le_mul_left _ ht)
      have e2 : 2 * C * j = 2 * (C * j) := by ring
      unfold rdB
      rw [b4 (yb + 2 * (C * t + c)) (by simp only [regs]; omega) (.inl (by omega)),
        b4 (yb + 2 * (C * t + c) + 1) (by simp only [regs]; omega) (.inl (by omega))]
      exact hV t ht c hc
    · have e1 : yb + 2 * (C * t + c) = yb + 2 * C * t + 2 * c := by ring
      rw [e1, (b3 c hc).1, (b3 c hc).2]
      unfold rdB
      rw [show cb + cs * J t + 2 * c0 + 2 * c = cb + cs * J t + 2 * c0 + 2 * c + 0 from rfl,
        hx c hc 0 (by omega), hx c hc 1 (by omega)]
      exact ⟨rfl, rfl⟩
  · have e3 : 2 * C * (j + 1) = 2 * C * j + 2 * C := by ring
    rw [rd_decS (by simp only [regs, lgC1] at hi ⊢; omega)]
    rw [b4 i hi (by omega), hH i hi (by omega)]

end FR.X

end G6_FRXLag
