-- lvm6 X1 (BLUEPRINT §3 `FD1`): proof helpers for the semantics of the decoder programs. New.
import Lvm6FDIR

/-!
# Semantics of `FD1`'s programs: helpers

* `fwdNIR_nw_hi`, `wtabNIR_nw_hi`: season 1's forward NTT and basis table write no register
  `≥ 187` (`bflyNIR_nw_hi` is season 1's);
* `wf_*`: the programs are well formed;
* **`loopK_gen`**: a counted loop by invariant, where the invariant ignores the loop's counter and
  the compiler's scratch (the entry and the decrement are dealt with once here);
* `store_hp`, `load_hp`, `blk_hp`: one heap store, one load, one register block, in the form the
  loop bodies use (heap frame plus the cells written).
-/

namespace Lvm6.FD

open RecursionFast Lvm.X Lvm.Nb

attribute [local irreducible] entryK storeM

/-! ## Registers not written by season 1's programs -/

theorem fwdNIR_nw_hi (N ℓ tb : ℕ) {r : ℕ} (hr : 187 ≤ r) : ¬ Writes (fwdNIR N ℓ tb) r := by
  intro hw
  simp only [fwdNIR, fStepN, fPreN, flevelNIR, fpairNBody, pairPs, alphaNIR, alphaBody, farithIR,
    addK, mulK, mulKC, redC, Writes, Prim.dst, List.mem_cons, List.mem_nil_iff, List.cons_append,
    List.nil_append, exists_eq_or_imp, exists_eq_left, or_false, false_or] at hw
  simp only [rLv, rTr, rN3, rC3, rQ, rP2, rN1, rC1, uT1, uX, uT2, rBs, rAL, rAH, rA0, rBit, uI,
    rTa, rN2, rC2, fAl, fG, fU, fW, fH, fT, fN, cTmp, rKf, rTbf] at hw
  omega

theorem bflyNIR_nw_hi (N ℓ tb : ℕ) {r : ℕ} (hr : 187 ≤ r) : ¬ Writes (bflyNIR N ℓ tb) r := by
  intro hw
  simp only [bflyNIR, lvlNStep, levelNIR, pairNBody, pairPs, alphaNIR, alphaBody, arithIR, addK, mulK,
    mulKC, redC, Writes, Prim.dst, List.mem_cons, List.mem_nil_iff, List.cons_append,
    List.nil_append, exists_eq_or_imp, exists_eq_left, or_false, false_or] at hw
  simp only [rLv, rTr, rN3, rC3, rQ, rP2, rN1, rC1, uT1, uX, uT2, rBs, rAL, rAH, rA0, rBit, uI,
    rTa, rN2, rC2, fAl, fG, fU, fW, fH, fT, fN, cTmp] at hw
  omega

theorem nw_seq {p q : XIR} {r : ℕ} (hp : ¬ Writes p r) (hq : ¬ Writes q r) : ¬ Writes (.seq p q) r :=
  fun h => h.elim hp hq

theorem nw_loopK {c n : ℕ} {K : Word} {b : XIR} {r : ℕ} (hc : r ≠ c) (hT : r ≠ cTmp)
    (hb : ¬ Writes b r) : ¬ Writes (.loopK c n K b) r := fun h => by
  rcases h with h | h | h
  · exact hc h
  · exact hT h
  · exact hb h

theorem nw_blk {ps : List Prim} {r : ℕ} (h : ∀ p ∈ ps, p.dst ≠ r) : ¬ Writes (.blk ps) r :=
  fun ⟨p, hp, he⟩ => h p hp he

theorem nw_mulK {d a b r : ℕ} (hr : 9 ≤ r) (hd : r ≠ d) : ¬ Writes (mulK d a b) r :=
  fun ⟨p, hp, he⟩ => by rcases mulKC_dst d a b p hp with h | h <;> omega

theorem nw_invK {d a r : ℕ} (hr : 12 ≤ r) (hd : r ≠ d) : ¬ Writes (invK d a) r :=
  fun ⟨p, hp, he⟩ => by rcases invKC_dst d a p hp with h | h <;> omega

/-! ## Well formed -/

theorem wf_leavesIR (ℓ B : ℕ) : WF (leavesIR ℓ B) := by
  simp +decide [leavesIR, leafBody, WF, Writes, Prim.dst, zI, zA, zB, zT, zC1, zN1, cTmp, regs]

theorem wf_dummiesIR (ℓ m B : ℕ) : WF (dummiesIR ℓ m B) := by
  simp +decide [dummiesIR, dummyBody, WF, Writes, Prim.dst, zI, zA, zB, zC, zD, zC1, zN1, cTmp,
    regs]

theorem wf_copyBody (c : ℕ) : WF (copyBody c) := by
  simp +decide [copyBody, WF, Prim.dst, zU, zV, zD, zT, zA, zB, zC, zE, cTmp]

theorem wf_prodBody : WF prodBody := by
  simp +decide [prodBody, WF, Prim.dst, zU, zV, zA, zC, zE, cTmp, mulK_wf_iff]

theorem nw_copyBody (c : ℕ) {r : ℕ} (hr : 198 ≤ r) (hr' : r ≤ 205) : ¬ Writes (copyBody c) r := by
  simp only [copyBody]
  refine nw_seq (fun h => ?_) (nw_seq (fun h => ?_) (nw_seq (fun h => ?_) (nw_seq (fun h => ?_)
    (nw_seq (nw_blk ?_) (nw_seq (fun h => ?_) (nw_seq (nw_blk ?_) (nw_seq (fun h => ?_) (nw_blk ?_))))))))
  all_goals first
    | (simp only [Writes, zU, zV, zD, zT, zA, zB, zC, zE, cTmp] at h; omega)
    | (simp only [List.mem_cons, List.mem_nil_iff, or_false]
       rintro p (rfl | rfl | rfl | rfl) <;> simp only [Prim.dst, zU, zV, zD, zT, zA, zB, zC, zE] <;> omega)

theorem nw_prodBody {r : ℕ} (hr : 198 ≤ r) (hr' : r ≤ 205) : ¬ Writes prodBody r := by
  simp only [prodBody]
  refine nw_seq (fun h => ?_) (nw_seq (fun h => ?_) (nw_seq (nw_mulK (by omega) (by simp [zW]; omega))
    (nw_seq (fun h => ?_) (nw_blk ?_))))
  all_goals first
    | (simp only [Writes, zU, zV, zA, zC, zE, cTmp] at h; omega)
    | (simp only [List.mem_cons, List.mem_nil_iff, or_false]
       rintro p (rfl | rfl | rfl) <;> simp only [Prim.dst, zA, zC, zE] <;> omega)

theorem wf_parentBody (N ℓ B h : ℕ) : WF (parentBody N ℓ B h) := by
  refine ⟨?_, ⟨?_, ?_, nw_copyBody _ (by decide) (by decide), wf_copyBody _⟩, ?_, wf_bflyNIR N _ _, wf_fwdNIR N _ _, ?_,
    wf_bflyNIR N _ _, wf_fwdNIR N _ _, ?_, ⟨?_, ?_, nw_prodBody (by decide) (by decide), wf_prodBody⟩, ?_⟩ <;>
    simp +decide [WF, Prim.dst, zA, zD, zB, zC, zE, zN2, zC2, zP, rA0, cTmp, regs]

theorem nw_parentBody (N ℓ B h : ℕ) {r : ℕ} (hr : 201 ≤ r) (hr' : r ≤ 205) (h3 : r ≠ zC2) (h4 : r ≠ zN2)
    (h5 : r ≠ zP) : ¬ Writes (parentBody N ℓ B h) r := by
  have hT : r ≠ cTmp := by simp [cTmp]; omega
  simp only [parentBody]
  refine nw_seq (nw_blk ?_) (nw_seq (nw_loopK h3 hT (nw_copyBody _ (by omega) hr')) (nw_seq (nw_blk ?_)
    (nw_seq (bflyNIR_nw_hi N _ _ (by omega)) (nw_seq (fwdNIR_nw_hi N _ _ (by omega)) (nw_seq (nw_blk ?_)
    (nw_seq (bflyNIR_nw_hi N _ _ (by omega)) (nw_seq (fwdNIR_nw_hi N _ _ (by omega)) (nw_seq (nw_blk ?_)
    (nw_seq (nw_loopK h3 hT (nw_prodBody (by omega) hr')) (nw_blk ?_))))))))))
  all_goals simp only [List.mem_cons, List.mem_nil_iff, or_false]
  all_goals rintro p (rfl | rfl | rfl | rfl | rfl | rfl) <;>
    simp_all [Prim.dst, zA, zD, zB, zC, zE, zN2, zP, rA0, zC2, cTmp] <;> omega

theorem wf_tLevelIR (N ℓ B h : ℕ) : WF (tLevelIR N ℓ B h) :=
  ⟨by simp +decide [WF, Prim.dst, zP, zN1], ⟨by decide, by decide,
    nw_parentBody N ℓ B h (by decide) (by decide) (by decide) (by decide) (by decide),
    wf_parentBody N ℓ B h⟩⟩

theorem wf_treeIR (N ℓ B : ℕ) : ∀ h, WF (treeIR N ℓ B h)
  | 0 => by simp [treeIR, WF]
  | h + 1 => ⟨wf_treeIR N ℓ B h, wf_tLevelIR N ℓ B h⟩

theorem wf_invsIR (ℓ B : ℕ) : WF (invsIR ℓ B) := by
  refine ⟨by simp +decide [WF, Prim.dst, zA, zB, zN1], ⟨⟨by decide, by decide, by decide⟩, by decide, ?_, ?_⟩⟩
  · simp only [invBody]
    refine nw_seq (fun h => ?_) (nw_seq (nw_invK (by decide) (by decide)) (nw_seq (fun h => ?_) (nw_blk ?_)))
    · simp only [Writes, zU, zC1] at h; omega
    · simp only [Writes, cTmp, zC1] at h; omega
    · simp +decide [Prim.dst, zA, zB, zC1]
  · exact ⟨by simp [WF, zU], wf_invK _ _ (by decide), by simp [WF, zB, cTmp],
      by simp +decide [WF, Prim.dst, zA, zB]⟩

theorem wf_lamIR (N ℓ m B : ℕ) : WF (lamIR N ℓ m B) :=
  ⟨wf_wtabNIR N _, wf_leavesIR ℓ B, wf_dummiesIR ℓ m B, wf_treeIR N ℓ B ℓ, wf_invsIR ℓ B⟩

/-! ## A counted loop by invariant -/

/-- **`loopK_gen`**: an invariant `R` that ignores the counter `c` and the scratch `cTmp`, holds on
entry and is preserved by the body for `j < K`, holds after the loop; `Inv` and the memory size
are kept. -/
theorem loopK_gen (I : Array Word) (b : XIR) {c n K : ℕ} (s : St) (hM : Inv s.M) (hc : 4 < c)
    (hcr : c < regs) (hn : n ≠ c) (hN : rd s.M n = toWord K) (hK : K < 2 ^ 64)
    (R : ℕ → Mem → Prop)
    (hR : ∀ j (M M' : Mem), (∀ i, i ≠ c → i ≠ cTmp → rd M' i = rd M i) → R j M → R j M')
    (h0 : R 0 s.M)
    (hb : ∀ j (s' : St), j < K → Inv s'.M → s'.M.size = s.M.size → R j s'.M →
      Inv (semXIR I b s').M ∧ R (j + 1) (semXIR I b s').M) :
    R K (semXIR I (.loopK c n (toWord K) b) s).M ∧ Inv (semXIR I (.loopK c n (toWord K) b) s).M ∧
      (semXIR I (.loopK c n (toWord K) b) s).M.size = s.M.size := by
  let P : ℕ → St → Prop := fun j s' => Inv s'.M ∧ s'.M.size = s.M.size ∧ R j s'.M
  have h := loopK_run I b P s hM hc hcr hn hN hK ⟨inv_entryK hM hc, size_entryK .., hR 0 _ _
    (fun i h1 h2 => entryK_frame _ (Ne.symm h1) (Ne.symm h2)) h0⟩ (by
      rintro j s' hj ⟨i1, i2, i3⟩
      obtain ⟨b1, b2⟩ := hb j s' hj i1 i2 i3
      exact ⟨inv_decS b1 (by omega), by rw [size_decS, size_sem, i2],
        hR _ _ _ (fun i h1 _ => rd_decS (Ne.symm h1) _) b2⟩)
  exact ⟨h.2.2, h.1, h.2.1⟩

/-! ## One instruction -/

theorem semBlk (I : Array Word) (ps : List Prim) (s : St) :
    semXIR I (.blk ps) s = ⟨runPrims ps s.M, s.o⟩ := rfl

/-- A block keeps every cell it does not name as a destination. -/
theorem rdBlk_nw (I : Array Word) (ps : List Prim) (s : St) {r : ℕ}
    (h : ∀ p ∈ ps, p.dst ≠ r) : rd (semXIR I (.blk ps) s).M r = rd s.M r :=
  rd_runPrims_of_not_writes h s.M

/-- A heap store `M[M[p]] := M[v]` at `x ≥ regs`, in frame form. -/
theorem store_hp (I : Array Word) (s : St) (hM : Inv s.M) {p v x : ℕ} (hpT : p ≠ cTmp)
    (hvT : v ≠ cTmp) (hP : rd s.M p = toWord x) (hx : regs ≤ x) (hx2 : x < 2 ^ 64)
    (hxs : x < s.M.size) :
    (∀ i, i ≠ cTmp → rd (semXIR I (.store p v) s).M i = if i = x then rd s.M v else rd s.M i) ∧
    Inv (semXIR I (.store p v) s).M := by
  obtain ⟨a1, a2, a3⟩ := store_sem I s hM hpT hvT hP hx hx2 hxs
  refine ⟨fun i hi => ?_, a3⟩
  split_ifs with h
  · subst h; exact a1
  · exact a2 i h hi

/-- A heap load `M[d] := M[M[p]]`, in frame form. -/
theorem load_hp (I : Array Word) (s : St) (hM : Inv s.M) {d p x : ℕ} (hd : 4 ≤ d)
    (hdr : d < regs) (hP : rd s.M p = toWord x) (hx2 : x < 2 ^ 64) :
    (∀ i, rd (semXIR I (.load d p) s).M i = if i = d then rd s.M x else rd s.M i) ∧
    Inv (semXIR I (.load d p) s).M := by
  obtain ⟨a1, a2, a3⟩ := load_sem I s hM hd hdr hP hx2
  refine ⟨fun i => ?_, a3⟩
  split_ifs with h
  · subst h; exact a1
  · exact a2 i h

end Lvm6.FD
