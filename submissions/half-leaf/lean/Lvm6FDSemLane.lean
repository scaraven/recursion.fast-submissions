-- lvm6 X1 (BLUEPRINT §3 `FD1`): `laneIR` decodes one lane. New; on season 1's `bflyNIR_sem`,
-- `fwdNIR_sem` (`LvmMPXNtt4`).
import Lvm6FDSemBase

/-!
# `laneIR` computes `fd1`

* `zeroGIR_sem`: the lane workspace `[gA, gA + 2n)` is zeroed;
* `synIR_sem`: `G[j] = y_j Λ_j` on `S`, and the syndromes `s₀`, `s₁` (list order) in `zS0`, `zS1`;
* `corrIR_sem`: the correction `G[s₁/s₀] += s₀` when `s₀ ≠ 0` and `s₁/s₀ < n`: `G = gIn` on `V`;
* `cosIR_sem`: `G = 0` on `V` and `G · Λ⁻¹` on the coset;
* **`laneIR_sem`** (frozen statement): with season 1's NTTs in between, `fd1` at `outA`.
-/

namespace Lvm6.FD

open RecursionFast Lvm.X Lvm.Nb

attribute [local irreducible] entryK storeM

/-! ## Proof helpers -/

/-- Does the program contain an output statement? -/
def hasOutL : XIR → Bool
  | .out _ => true
  | .seq p q => hasOutL p || hasOutL q
  | .ite _ p q => hasOutL p || hasOutL q
  | .loopK _ _ _ b => hasOutL b
  | .loopT _ _ _ b => hasOutL b
  | _ => false

theorem iterL_oL {f : St → St} {c : ℕ} (hf : ∀ s, (f s).o = s.o) :
    ∀ k s, (iterL f c k s).o = s.o
  | 0, _ => rfl
  | k + 1, s => (iterL_oL hf k _).trans (hf s)

/-- A program without output statements leaves the output unchanged. -/
theorem sem_oL (I : Array Word) : ∀ (P : XIR) (s : St), hasOutL P = false → (semXIR I P s).o = s.o
  | .blk _, _, _ => rfl
  | .load .., _, _ => rfl
  | .store .., _, _ => rfl
  | .input .., _, _ => rfl
  | .out _, _, h => by simp [hasOutL] at h
  | .seq p q, s, h => by
    simp only [hasOutL, Bool.or_eq_false_iff] at h
    rw [semXIR_seq, sem_oL I q _ h.2, sem_oL I p s h.1]
  | .ite c p q, s, h => by
    simp only [hasOutL, Bool.or_eq_false_iff] at h
    rw [semXIR_ite]; split
    · exact sem_oL I q s h.2
    · exact sem_oL I p s h.1
  | .loopK c n K b, s, h => by
    simp only [semXIR]; exact iterL_oL (fun s' => sem_oL I b s' h) _ _
  | .loopT c n cap b, s, h => by
    simp only [semXIR]; exact iterL_oL (fun s' => sem_oL I b s' h) _ _

theorem wK_zeroL : wK 0 = 0 := rfl

theorem semXIR_nilL (I : Array Word) (s : St) : semXIR I (.blk []) s = s := by
  rw [semBlk]; rfl

theorem wK_eq_zeroL {w : Word} : wK w = 0 ↔ w = 0 :=
  ⟨fun h => by simpa [wK] using congrArg BF64.toBitVec h, fun h => h ▸ rfl⟩

theorem toWord_toNatL (u : Word) : toWord u.toNat = u :=
  BitVec.eq_of_toNat_eq (by rw [toNat_toWord u.isLt])

theorem bflyNIR_nwAL (N ℓ tb : ℕ) : ¬ Writes (bflyNIR N ℓ tb) rA0 := by
  simp only [bflyNIR, lvlNStep]
  exact nw_seq (nw_blk (by simp +decide [Prim.dst, rLv, rTr, rN3, rA0]))
    (nw_loopK (by decide) (by decide) (nw_seq (levelNIR_nw (Or.inl rfl) ℓ)
      (nw_blk (by simp +decide [Prim.dst, rLv, uT1, rTr, rA0]))))

theorem fwdNIR_nwAL (N ℓ tb : ℕ) : ¬ Writes (fwdNIR N ℓ tb) rA0 := by
  simp only [fwdNIR, fStepN]
  exact nw_seq (nw_blk (by simp +decide [Prim.dst, rKf, rTbf, rN3, rA0]))
    (nw_loopK (by decide) (by decide) (nw_seq (nw_blk (by simp +decide [fPreN, Prim.dst, rLv, uT1, rTr, rA0]))
      (nw_seq (flevelNIR_nw (Or.inl rfl) ℓ) (nw_blk (by simp +decide [Prim.dst, rKf, rA0])))))

/-! ## Zeroing the lane workspace -/

theorem zeroGIR_sem (I : Array Word) (s : St) (hM : Inv s.M) {ℓ B : ℕ} (hB : regs ≤ B)
    (hsz : fdEnd B ℓ ≤ s.M.size) (h64 : fdEnd B ℓ < 2 ^ 64) :
    (∀ i < 2 ^ (ℓ + 1), rd (semXIR I (zeroGIR ℓ B) s).M (gA B ℓ + i) = 0) ∧
    (∀ x, regs ≤ x → (x < gA B ℓ ∨ gA B ℓ + 2 ^ (ℓ + 1) ≤ x) →
      rd (semXIR I (zeroGIR ℓ B) s).M x = rd s.M x) ∧
    Inv (semXIR I (zeroGIR ℓ B) s).M := by
  have hs := hM.1
  simp only [regs] at hs hB
  have hp : 2 ^ (ℓ + 1) = 2 * 2 ^ ℓ := by rw [pow_succ]; ring
  rw [zeroGIR, semXIR_seq]
  simp only [fdEnd, gA, hp] at hsz h64 ⊢
  set b0 : List Prim := [.const zA (toWord (B + 4096 + 2 * 2 ^ ℓ)), .const zV 0,
    .const zN1 (toWord (2 * 2 ^ ℓ))]
  have w0 : WF (.blk b0) := by simp +decide [b0, WF, Prim.dst, zA, zV, zN1]
  have hM0 := inv_sem I w0 hM
  have r0 : rd (semXIR I (.blk b0) s).M zA = toWord (B + 4096 + 2 * 2 ^ ℓ + 0) ∧
      rd (semXIR I (.blk b0) s).M zV = 0 ∧
      rd (semXIR I (.blk b0) s).M zN1 = toWord (2 * 2 ^ ℓ) := by
    rw [semBlk]; simp only [b0, runPrims, List.foldl, Prim.run]
    refine ⟨?_, ?_, ?_⟩ <;>
    simp (disch := first | decide | ((try simp only [size_set]); refine Nat.lt_of_lt_of_le (m := 256) (by decide) ?_; first | assumption | omega)) only
      [rd_set_self, rd_set_ne] <;> rfl
  have k0 : ∀ r, regs ≤ r → rd (semXIR I (.blk b0) s).M r = rd s.M r := fun r hr => by
    simp only [regs] at hr
    refine rdBlk_nw I _ s ?_
    simp only [b0, List.mem_cons, List.mem_nil_iff, or_false]
    rintro p (rfl | rfl | rfl) <;> simp only [Prim.dst, zA, zV, zN1] <;> first | decide | exact Nat.ne_of_lt (Nat.lt_of_lt_of_le (by decide) hr)
  have z0 := size_sem I (.blk b0) s
  generalize semXIR I (.blk b0) s = s0 at hM0 r0 k0 z0 ⊢
  obtain ⟨a0, v0, n0⟩ := r0
  set G := B + 4096 + 2 * 2 ^ ℓ with hG
  let R : ℕ → Mem → Prop := fun j M => rd M zA = toWord (G + j) ∧ rd M zV = 0 ∧
    (∀ i < j, rd M (G + i) = 0) ∧
    (∀ x, regs ≤ x → (x < G ∨ G + j ≤ x) → rd M x = rd s.M x)
  have hR : ∀ j (M M' : Mem), (∀ i, i ≠ zC1 → i ≠ cTmp → rd M' i = rd M i) → R j M → R j M' := by
    rintro j M M' hMM ⟨r1, r2, r3, r4⟩
    have hx : ∀ x, regs ≤ x → x ≠ zC1 ∧ x ≠ cTmp := fun x hx => by
      simp only [regs, zC1, cTmp] at *; omega
    refine ⟨by rw [hMM _ (by decide) (by decide), r1], by rw [hMM _ (by decide) (by decide), r2],
      fun i hi => ?_, fun x hx' hx2 => ?_⟩
    · rw [hMM _ (hx _ (by simp only [regs]; omega)).1 (hx _ (by simp only [regs]; omega)).2, r3 i hi]
    · rw [hMM _ (hx x hx').1 (hx x hx').2, r4 x hx' hx2]
  have h0 : R 0 s0.M := ⟨a0, v0, fun i hi => absurd hi (by omega), fun x hx _ => k0 x hx⟩
  have hb : ∀ j (s' : St), j < 2 * 2 ^ ℓ → Inv s'.M → s'.M.size = s0.M.size → R j s'.M →
      Inv (semXIR I zeroBodyG s').M ∧ R (j + 1) (semXIR I zeroBodyG s').M := by
    rintro j s' hj i1 i2 ⟨r1, r2, r3, r4⟩
    rw [zeroBodyG, semXIR_seq]
    obtain ⟨c1, hM1⟩ := store_hp I s' i1 (p := zA) (v := zV) (by decide) (by decide) r1
      (by simp only [regs]; omega) (by omega) (by omega)
    have z1 := size_sem I (.store zA zV) s'
    generalize semXIR I (.store zA zV) s' = s1 at c1 hM1 z1 ⊢
    have hM2 := inv_sem I (P := .blk [.op .add zA zA cOne]) (by simp +decide [WF, Prim.dst, zA]) hM1
    have e2 : ∀ i, i ≠ zA → rd (semXIR I (.blk [.op .add zA zA cOne]) s1).M i = rd s1.M i :=
      fun i h1 => rdBlk_nw I _ _ (by simp [Prim.dst]; exact Ne.symm h1)
    have hone : rd s1.M cOne = 1 := hM1.2 0 (by decide)
    have hz1 := hM1.1; simp only [regs] at hz1
    refine ⟨hM2, ?_, ?_, fun i hi => ?_, fun x hx hx2 => ?_⟩
    · rw [semBlk]; simp only [runPrims, List.foldl, Prim.run]
      simp (disch := first | decide | ((try simp only [size_set]); refine Nat.lt_of_lt_of_le (m := 256) (by decide) ?_; first | assumption | omega)) only [rd_set_self]
      rw [c1 _ (by decide), if_neg (by simp only [zA]; omega), r1, hone, add_one_toWord]
      exact congrArg toWord (by ring)
    · rw [e2 _ (by decide), c1 _ (by decide), if_neg (by simp only [zV]; omega), r2]
    · have hxr : regs ≤ G + i := by simp only [regs]; omega
      rw [e2 _ (by simp only [regs, zA] at *; omega), c1 _ (by simp only [cTmp]; omega)]
      by_cases h1 : G + i = G + j
      · rw [if_pos h1, r2]
      · rw [if_neg h1, r3 i (by omega)]
    · rw [e2 _ (by simp only [regs, zA] at *; omega), c1 _ (by simp only [regs, cTmp] at *; omega),
        if_neg (by omega), r4 x hx (by omega)]
  have hfin := loopK_gen I zeroBodyG s0 hM0 (by decide) (by decide) (by decide) n0 (by omega) R hR h0
    (fun j s' hj i1 i2 i3 => hb j s' hj i1 i2 i3)
  obtain ⟨⟨_, _, f3, f4⟩, f5, _⟩ := hfin
  exact ⟨fun i hi => f3 i hi, fun x hx hx2 => f4 x hx hx2, f5⟩

/-! ## The syndromes -/

theorem regs_neL {x : ℕ} (hx : regs ≤ x) : x ≠ zI ∧ x ≠ zA ∧ x ≠ zB ∧ x ≠ zC ∧ x ≠ zT ∧ x ≠ zU ∧
    x ≠ zV ∧ x ≠ zW ∧ x ≠ zS0 ∧ x ≠ zS1 ∧ x ≠ zK ∧ x ≠ zD ∧ x ≠ zE ∧ x ≠ zC1 ∧ x ≠ cTmp ∧
    (x < 5 ∨ 9 ≤ x) ∧ (x < 5 ∨ 12 ≤ x) := by
  simp only [regs, zI, zA, zB, zC, zT, zU, zV, zW, zS0, zS1, zK, zD, zE, zC1, cTmp] at *
  omega

theorem take_succL {S : List ℕ} {i : ℕ} (hi : i < S.length) :
    S.take (i + 1) = S.take i ++ [S.getD i 0] := by
  rw [List.take_succ, List.getElem?_eq_getElem hi, List.getD_eq_getElem _ _ hi]; rfl

theorem getD_memL {S : List ℕ} {i : ℕ} (hi : i < S.length) : S.getD i 0 ∈ S := by
  rw [List.getD_eq_getElem _ _ hi]; exact List.getElem_mem hi

theorem synBody_semL (I : Array Word) (s' : St) (i1 : Inv s'.M) {ℓ B i j : ℕ} {a b : BF64}
    (hB : 256 ≤ B) (hsz : B + 4096 + 11 * 2 ^ ℓ ≤ s'.M.size) (h64 : B + 4096 + 11 * 2 ^ ℓ < 2 ^ 64)
    (hi : i < 2 ^ ℓ) (hj : j < 2 ^ ℓ) (r1 : rd s'.M zC = toWord (B + 4096 + i))
    (v1 : rd s'.M (B + 4096 + i) = toWord j)
    (hyj : rdK s'.M (B + 4096 + 2 ^ ℓ + j) = a) (hTj : rdK s'.M (B + 4096 + 4 * 2 ^ ℓ + j) = b) :
    Inv (semXIR I (synBody ℓ B) s').M ∧
    rd (semXIR I (synBody ℓ B) s').M zC = toWord (B + 4096 + (i + 1)) ∧
    rdK (semXIR I (synBody ℓ B) s').M zS0 = rdK s'.M zS0 + a * b ∧
    rdK (semXIR I (synBody ℓ B) s').M zS1 = rdK s'.M zS1 + a * b * ptK j ∧
    rdK (semXIR I (synBody ℓ B) s').M (B + 4096 + 2 * 2 ^ ℓ + j) = a * b ∧
    (∀ x, regs ≤ x → x ≠ B + 4096 + 2 * 2 ^ ℓ + j → rd (semXIR I (synBody ℓ B) s').M x = rd s'.M x) := by
  have hs' := i1.1
  simp only [regs] at hs'
  have hR4 : ∀ {k1 k2 k3 : ℕ}, regs ≤ B + k1 + k2 + k3 :=
    Nat.le_add_right_of_le (Nat.le_add_right_of_le (Nat.le_add_right_of_le hB))
  have rE : 256 ≤ B + 4096 + 2 * 2 ^ ℓ + j := hR4
  have hEn : ∀ {u : ℕ}, u < 256 → u ≠ B + 4096 + 2 * 2 ^ ℓ + j := fun hu => Nat.ne_of_lt (Nat.lt_of_lt_of_le hu rE)
  rw [synBody, semXIR_seq]
  simp only [yA, tA, gA]
  -- s1: zI := S[i]
  obtain ⟨c1, hM1⟩ := load_hp I s' i1 (d := zI) (p := zC) (by decide) (by decide) r1 (by omega)
  have z1 := size_sem I (.load zI zC) s'
  generalize semXIR I (.load zI zC) s' = s1 at c1 hM1 z1 ⊢
  have hI1 : rd s1.M zI = toWord j := by rw [c1, if_pos rfl, v1]
  rw [semXIR_seq]
  -- s2: the addresses
  set b2 : List Prim := [.const zD (toWord (B + 4096 + 2 ^ ℓ)), .op .add zA zD zI,
    .const zD (toWord (B + 4096 + 4 * 2 ^ ℓ)), .op .add zB zD zI,
    .const zD (toWord (B + 4096 + 2 * 2 ^ ℓ)), .op .add zE zD zI]
  have hM2 := inv_sem I (P := .blk b2) (by simp +decide [b2, WF, Prim.dst, zD, zA, zB, zE]) hM1
  have e2 : ∀ r, r ≠ zD → r ≠ zA → r ≠ zB → r ≠ zE → rd (semXIR I (.blk b2) s1).M r = rd s1.M r :=
    fun r h1 h2 h3 h4 => rdBlk_nw I _ _ (by
      simp [b2, Prim.dst, Ne.symm h1, Ne.symm h2, Ne.symm h3, Ne.symm h4])
  have hz1 := hM1.1; simp only [regs] at hz1
  have t2 : rd (semXIR I (.blk b2) s1).M zA = toWord (B + 4096 + 2 ^ ℓ + j) ∧
      rd (semXIR I (.blk b2) s1).M zB = toWord (B + 4096 + 4 * 2 ^ ℓ + j) ∧
      rd (semXIR I (.blk b2) s1).M zE = toWord (B + 4096 + 2 * 2 ^ ℓ + j) := by
    rw [semBlk]; simp only [b2, runPrims, List.foldl, Prim.run]
    refine ⟨?_, ?_, ?_⟩ <;>
    simp (disch := first | decide | ((try simp only [size_set]); refine Nat.lt_of_lt_of_le (m := 256) (by decide) ?_; first | assumption | omega)) only
      [rd_set_self, rd_set_ne] <;> rw [hI1, add_toWord]
  have z2 := size_sem I (.blk b2) s1
  generalize semXIR I (.blk b2) s1 = s2 at hM2 e2 t2 z2 ⊢
  rw [semXIR_seq]
  -- s3: zU := y_j
  obtain ⟨c3, hM3⟩ := load_hp I s2 hM2 (d := zU) (p := zA) (by decide) (by decide) t2.1 (by omega)
  have z3 := size_sem I (.load zU zA) s2
  generalize semXIR I (.load zU zA) s2 = s3 at c3 hM3 z3 ⊢
  rw [semXIR_seq]
  -- s4: zV := Λ_j
  obtain ⟨c4, hM4⟩ := load_hp I s3 hM3 (d := zV) (p := zB) (by decide) (by decide)
    (by rw [c3, if_neg (by decide)]; exact t2.2.1) (by omega)
  have z4 := size_sem I (.load zV zB) s3
  generalize semXIR I (.load zV zB) s3 = s4 at c4 hM4 z4 ⊢
  -- heap through s1 … s4
  have hh2 : ∀ x, regs ≤ x → rd s2.M x = rd s'.M x := fun x hx => by
    have h := regs_neL hx
    rw [e2 _ h.2.2.2.2.2.2.2.2.2.2.2.1 h.2.1 h.2.2.1 h.2.2.2.2.2.2.2.2.2.2.2.2.1, c1, if_neg h.1]
  have hh3 : ∀ x, regs ≤ x → rd s3.M x = rd s'.M x := fun x hx => by
    rw [c3, if_neg (regs_neL hx).2.2.2.2.2.1, hh2 x hx]
  have hh4 : ∀ x, regs ≤ x → rd s4.M x = rd s'.M x := fun x hx => by
    rw [c4, if_neg (regs_neL hx).2.2.2.2.2.2.1, hh3 x hx]
  have u4 : rdK s4.M zU = a := by
    rw [rdK, c4, if_neg (by decide), c3, if_pos rfl, ← rdK,
      rdK_eq (hh2 _ hR4),
      hyj]
  have v4 : rdK s4.M zV = b := by
    rw [rdK, c4, if_pos rfl, ← rdK, rdK_eq (hh3 _ hR4),
      hTj]
  rw [semXIR_seq]
  -- s5: zW := y_j Λ_j
  have w5 := mulK_sem (I := I) (s := s4) hM4 (d := zW) (a := zU) (b := zV) (by decide) (by decide)
    (by decide) (by decide)
  have e5 : ∀ r, (r < 5 ∨ 9 ≤ r) → r ≠ zW → rd (semXIR I (mulK zW zU zV) s4).M r = rd s4.M r :=
    fun r h1 h2 => by rw [mulK, sem_blk]; exact mulKC_frame zW zU zV h1 h2 s4.M
  have hM5 := inv_sem I (wf_mulK zW zU zV (by decide)) hM4
  have z5 := size_sem I (mulK zW zU zV) s4
  rw [u4, v4] at w5
  generalize semXIR I (mulK zW zU zV) s4 = s5 at w5 e5 hM5 z5 ⊢
  rw [semXIR_seq]
  -- s6: G[j] := zW
  have zE5 : rd s5.M zE = toWord (B + 4096 + 2 * 2 ^ ℓ + j) := by
    rw [e5 _ (by decide) (by decide), c4, if_neg (by decide), c3, if_neg (by decide), t2.2.2]
  have hsz5 : s5.M.size = s'.M.size := by
    rw [z5, z4, z3, z2, z1]
  obtain ⟨c6, hM6⟩ := store_hp I s5 hM5 (p := zE) (v := zW) (by decide) (by decide) zE5
    rE (by omega) (by omega)
  generalize semXIR I (.store zE zW) s5 = s6 at c6 hM6 ⊢
  rw [semXIR_seq]
  -- s7: s₀ += zW
  set b7 : List Prim := [.op .xor zS0 zS0 zW]
  have hM7 := inv_sem I (P := .blk b7) (by simp +decide [b7, WF, Prim.dst, zS0]) hM6
  have e7 : ∀ r, r ≠ zS0 → rd (semXIR I (.blk b7) s6).M r = rd s6.M r :=
    fun r h1 => rdBlk_nw I _ _ (by simp [b7, Prim.dst]; exact Ne.symm h1)
  have hz6 := hM6.1; simp only [regs] at hz6
  have t7 : rd (semXIR I (.blk b7) s6).M zS0 = rd s6.M zS0 ^^^ rd s6.M zW := by
    rw [semBlk]; simp only [b7, runPrims, List.foldl, Prim.run]
    simp (disch := first | decide | ((try simp only [size_set]); refine Nat.lt_of_lt_of_le (m := 256) (by decide) ?_; first | assumption | omega)) only [rd_set_self]
    rfl
  generalize semXIR I (.blk b7) s6 = s7 at hM7 e7 t7 ⊢
  rw [semXIR_seq]
  -- s8: zU := zW · ptK j
  have u8 := mulK_sem (I := I) (s := s7) hM7 (d := zU) (a := zW) (b := zI) (by decide) (by decide)
    (by decide) (by decide)
  have e8 : ∀ r, (r < 5 ∨ 9 ≤ r) → r ≠ zU → rd (semXIR I (mulK zU zW zI) s7).M r = rd s7.M r :=
    fun r h1 h2 => by rw [mulK, sem_blk]; exact mulKC_frame zU zW zI h1 h2 s7.M
  have hM8 := inv_sem I (wf_mulK zU zW zI (by decide)) hM7
  have zW7 : rdK s7.M zW = a * b := by
    rw [rdK, e7 _ (by decide), c6 _ (by decide), if_neg (hEn (by decide)), ← rdK, w5]
  have zI7 : rdK s7.M zI = ptK j := by
    rw [rdK, e7 _ (by decide), c6 _ (by decide), if_neg (hEn (by decide)),
      e5 _ (by decide) (by decide), c4, if_neg (by decide), c3, if_neg (by decide),
      e2 _ (by decide) (by decide) (by decide) (by decide), hI1]
    rfl
  rw [zW7, zI7] at u8
  generalize semXIR I (mulK zU zW zI) s7 = s8 at u8 e8 hM8 ⊢
  -- s9: s₁ += zU, zC += 1
  set b9 : List Prim := [.op .xor zS1 zS1 zU, .op .add zC zC cOne]
  have hM9 := inv_sem I (P := .blk b9) (by simp +decide [b9, WF, Prim.dst, zS1, zC]) hM8
  have e9 : ∀ r, r ≠ zS1 → r ≠ zC → rd (semXIR I (.blk b9) s8).M r = rd s8.M r :=
    fun r h1 h2 => rdBlk_nw I _ _ (by simp [b9, Prim.dst]; exact ⟨Ne.symm h1, Ne.symm h2⟩)
  have hz8 := hM8.1; simp only [regs] at hz8
  have hone : rd s8.M cOne = 1 := hM8.2 0 (by decide)
  -- the registers' path back to `s'`
  have back : ∀ r, r ≠ zI → r ≠ zA → r ≠ zB → r ≠ zE → r ≠ zD → r ≠ zU → r ≠ zV → r ≠ zW →
      r ≠ zS0 → r ≠ cTmp → (r < 5 ∨ 9 ≤ r) → r ≠ B + 4096 + 2 * 2 ^ ℓ + j → rd s8.M r = rd s'.M r := by
    intro r h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12
    rw [e8 _ h11 h6, e7 _ h9, c6 _ h10, if_neg h12, e5 _ h11 h8, c4, if_neg h7, c3, if_neg h6,
      e2 _ h5 h2 h3 h4, c1, if_neg h1]
  have q1 : rd s6.M zS0 = rd s'.M zS0 := by
    rw [c6 _ (by decide), if_neg (hEn (by decide)), e5 _ (by decide) (by decide), c4,
      if_neg (by decide), c3, if_neg (by decide), e2 _ (by decide) (by decide) (by decide) (by decide),
      c1, if_neg (by decide)]
  have q2 : rdK s6.M zW = a * b := by
    rw [rdK, c6 _ (by decide), if_neg (hEn (by decide)), ← rdK, w5]
  refine ⟨hM9, ?_, ?_, ?_, ?_, fun x hx hxj => ?_⟩
  · rw [semBlk]; simp only [b9, runPrims, List.foldl, Prim.run]
    simp (disch := first | decide | ((try simp only [size_set]); refine Nat.lt_of_lt_of_le (m := 256) (by decide) ?_; first | assumption | omega)) only
      [rd_set_self, rd_set_ne]
    rw [hone, back _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide) (by decide) (hEn (by decide)),
      r1, add_one_toWord]
    rfl
  · rw [rdK, e9 _ (by decide) (by decide), e8 _ (by decide) (by decide), t7, wK_xor, ← rdK, ← rdK,
      rdK_eq q1, q2]
  · rw [rdK, semBlk]; simp only [b9, runPrims, List.foldl, Prim.run]
    simp (disch := first | decide | ((try simp only [size_set]); refine Nat.lt_of_lt_of_le (m := 256) (by decide) ?_; first | assumption | omega)) only
      [rd_set_self, rd_set_ne]
    rw [eval_xor, wK_xor, ← rdK, ← rdK, u8, rdK_eq (back _ (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (hEn (by decide)))]
  · obtain ⟨n1, n2, n3, n4, n5, n6, n7, n8, n9, n10, n11, n12, n13, n14, n15, n16, n17⟩ :=
      regs_neL (show regs ≤ B + 4096 + 2 * 2 ^ ℓ + j from rE)
    rw [rdK_eq (e9 _ n10 n4), rdK_eq (e8 _ n16 n6), rdK_eq (e7 _ n9), rdK, c6 _ n15, if_pos rfl,
      ← rdK, w5]
  · obtain ⟨n1, n2, n3, n4, n5, n6, n7, n8, n9, n10, n11, n12, n13, n14, n15, n16, n17⟩ :=
      regs_neL hx
    rw [e9 _ n10 n4]
    exact back _ n1 n2 n3 n13 n12 n6 n7 n8 n9 n15 n16 hxj

theorem synIR_sem (I : Array Word) (s : St) (hM : Inv s.M) {ℓ B : ℕ} {S : List ℕ}
    {y L : ℕ → BF64} (hB : regs ≤ B) (hsz : fdEnd B ℓ ≤ s.M.size) (h64 : fdEnd B ℓ < 2 ^ 64)
    (hm : S.length ≤ 2 ^ ℓ) (hSn : ∀ j ∈ S, j < 2 ^ ℓ)
    (hS : ∀ i < S.length, rd s.M (sA B + i) = toWord (S.getD i 0))
    (hy : ∀ j < 2 ^ ℓ, rdK s.M (yA B ℓ + j) = y j)
    (hT : ∀ j < 2 ^ ℓ, rdK s.M (tA B ℓ + j) = L j)
    (hG : ∀ i < 2 ^ (ℓ + 1), rd s.M (gA B ℓ + i) = 0) :
    (∀ i < 2 ^ (ℓ + 1), rdK (semXIR I (synIR ℓ S.length B) s).M (gA B ℓ + i) =
      if i ∈ S then y i * L i else 0) ∧
    rdK (semXIR I (synIR ℓ S.length B) s).M zS0 = (S.map fun j => y j * L j).sum ∧
    rdK (semXIR I (synIR ℓ S.length B) s).M zS1 = (S.map fun j => y j * L j * ptK j).sum ∧
    (∀ x, regs ≤ x → (x < gA B ℓ ∨ gA B ℓ + 2 ^ (ℓ + 1) ≤ x) →
      rd (semXIR I (synIR ℓ S.length B) s).M x = rd s.M x) ∧
    Inv (semXIR I (synIR ℓ S.length B) s).M := by
  have hs := hM.1
  simp only [regs] at hs hB
  have hp : 2 ^ (ℓ + 1) = 2 * 2 ^ ℓ := by rw [pow_succ]; ring
  rw [synIR, semXIR_seq]
  simp only [fdEnd, gA, sA, yA, tA, hp] at hsz h64 hS hy hT hG ⊢
  set b0 : List Prim := [.const zC (toWord (B + 4096)), .const zS0 0, .const zS1 0,
    .const zN1 (toWord S.length)]
  have w0 : WF (.blk b0) := by simp +decide [b0, WF, Prim.dst, zC, zS0, zS1, zN1]
  have hM0 := inv_sem I w0 hM
  have r0 : rd (semXIR I (.blk b0) s).M zC = toWord (B + 4096 + 0) ∧
      rd (semXIR I (.blk b0) s).M zS0 = 0 ∧ rd (semXIR I (.blk b0) s).M zS1 = 0 ∧
      rd (semXIR I (.blk b0) s).M zN1 = toWord S.length := by
    rw [semBlk]; simp only [b0, runPrims, List.foldl, Prim.run]
    refine ⟨?_, ?_, ?_, ?_⟩ <;>
    simp (disch := first | decide | ((try simp only [size_set]); refine Nat.lt_of_lt_of_le (m := 256) (by decide) ?_; first | assumption | omega)) only
      [rd_set_self, rd_set_ne] <;> rfl
  have k0 : ∀ r, regs ≤ r → rd (semXIR I (.blk b0) s).M r = rd s.M r := fun r hr => by
    simp only [regs] at hr
    refine rdBlk_nw I _ s ?_
    simp only [b0, List.mem_cons, List.mem_nil_iff, or_false]
    rintro p (rfl | rfl | rfl | rfl) <;> simp only [Prim.dst, zC, zS0, zS1, zN1] <;> first | decide | exact Nat.ne_of_lt (Nat.lt_of_lt_of_le (by decide) hr)
  have z0 := size_sem I (.blk b0) s
  generalize semXIR I (.blk b0) s = s0 at hM0 r0 k0 z0 ⊢
  obtain ⟨c0, a0, b0', n0⟩ := r0
  set G := B + 4096 + 2 * 2 ^ ℓ with hG'
  let f0 : ℕ → BF64 := fun j => y j * L j
  let f1 : ℕ → BF64 := fun j => y j * L j * ptK j
  let R : ℕ → Mem → Prop := fun i M => rd M zC = toWord (B + 4096 + i) ∧
    rdK M zS0 = ((S.take i).map f0).sum ∧ rdK M zS1 = ((S.take i).map f1).sum ∧
    (∀ k < 2 * 2 ^ ℓ, rdK M (G + k) = if k ∈ S.take i then y k * L k else 0) ∧
    (∀ x, regs ≤ x → (x < G ∨ G + 2 * 2 ^ ℓ ≤ x) → rd M x = rd s.M x)
  have hR : ∀ j (M M' : Mem), (∀ i, i ≠ zC1 → i ≠ cTmp → rd M' i = rd M i) → R j M → R j M' := by
    rintro j M M' hMM ⟨r1, r2, r3, r4, r5⟩
    refine ⟨by rw [hMM _ (by decide) (by decide), r1],
      by rw [← r2]; exact rdK_eq (hMM _ (by decide) (by decide)),
      by rw [← r3]; exact rdK_eq (hMM _ (by decide) (by decide)), fun k hk => ?_, fun x hx hx2 => ?_⟩
    · have h := regs_neL (show regs ≤ G + k by simp only [regs]; omega)
      rw [← r4 k hk]; exact rdK_eq (hMM _ h.2.2.2.2.2.2.2.2.2.2.2.2.2.1 h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1)
    · have h := regs_neL hx
      rw [hMM _ h.2.2.2.2.2.2.2.2.2.2.2.2.2.1 h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1, r5 x hx hx2]
  have h0 : R 0 s0.M := by
    refine ⟨c0, by rw [rdK, a0]; rfl, by rw [rdK, b0']; rfl, fun k hk => ?_, fun x hx _ => k0 x hx⟩
    rw [rdK, k0 _ (by simp only [regs]; omega), hG k hk]
    simp only [List.take_zero, List.not_mem_nil, if_false]; rfl
  have hb : ∀ i (s' : St), i < S.length → Inv s'.M → s'.M.size = s0.M.size → R i s'.M →
      Inv (semXIR I (synBody ℓ B) s').M ∧ R (i + 1) (semXIR I (synBody ℓ B) s').M := by
    rintro i s' hi i1 i2 ⟨r1, r2, r3, r4, r5⟩
    set j := S.getD i 0 with hjdef
    have hjS : j ∈ S := getD_memL hi
    have hj : j < 2 ^ ℓ := hSn j hjS
    obtain ⟨d1, d2, d3, d4, d5, d6⟩ := synBody_semL I s' i1 (i := i) (j := j) (a := y j) (b := L j)
      hB (by omega) h64 (by omega) hj r1
      (by rw [r5 _ (by simp only [regs]; omega) (by omega), hS i hi])
      (by rw [rdK_eq (r5 _ (by simp only [regs]; omega) (by omega)), hy j hj])
      (by rw [rdK_eq (r5 _ (by simp only [regs]; omega) (by omega)), hT j hj])
    have hjm : S.take (i + 1) = S.take i ++ [j] := take_succL hi
    refine ⟨d1, d2, ?_, ?_, fun k hk => ?_, fun x hx hx2 => ?_⟩
    · rw [d3, r2, hjm, List.map_append, List.sum_append]; simp [f0]
    · rw [d4, r3, hjm, List.map_append, List.sum_append]; simp [f1]
    · simp only [hjm, List.mem_append, List.mem_singleton]
      by_cases hkj : k = j
      · subst hkj; rw [d5, if_pos (Or.inr rfl)]
      · rw [rdK_eq (d6 _ (by simp only [regs]; omega) (by omega)), r4 k hk]
        simp only [hkj, or_false]
    · rw [d6 x hx (by omega), r5 x hx hx2]
  have hfin := loopK_gen I (synBody ℓ B) s0 hM0 (by decide) (by decide) (by decide) n0 (by omega)
    R hR h0 (fun j s' hj i1 i2 i3 => hb j s' hj i1 i2 i3)
  obtain ⟨⟨_, f2, f3, f4, f5⟩, f6, _⟩ := hfin
  refine ⟨fun k hk => ?_, by rw [f2, List.take_length], by rw [f3, List.take_length],
    fun x hx hx2 => f5 x hx hx2, f6⟩
  rw [f4 k hk, List.take_length]

/-! ## The correction -/

/-- The correcting store: `G[k] += s₀` at `k = zU < n`. -/
theorem corrFixL (I : Array Word) (t : St) (ht : Inv t.M) {ℓ B k : ℕ} (hB : regs ≤ B)
    (hsz : fdEnd B ℓ ≤ t.M.size) (h64 : fdEnd B ℓ < 2 ^ 64) (hk : k < 2 ^ ℓ)
    (hU : rd t.M zU = toWord k) :
    rd (semXIR I (.seq (.blk [.const zD (toWord (gA B ℓ)), .op .add zA zD zU])
      (.seq (.load zV zA) (.seq (.blk [.op .xor zV zV zS0]) (.store zA zV)))) t).M (gA B ℓ + k) =
      rd t.M (gA B ℓ + k) ^^^ rd t.M zS0 ∧
    (∀ x, regs ≤ x → x ≠ gA B ℓ + k → rd (semXIR I (.seq (.blk [.const zD (toWord (gA B ℓ)),
      .op .add zA zD zU]) (.seq (.load zV zA) (.seq (.blk [.op .xor zV zV zS0]) (.store zA zV)))) t).M x =
      rd t.M x) ∧
    Inv (semXIR I (.seq (.blk [.const zD (toWord (gA B ℓ)), .op .add zA zD zU])
      (.seq (.load zV zA) (.seq (.blk [.op .xor zV zV zS0]) (.store zA zV)))) t).M := by
  have hs := ht.1
  simp only [regs] at hs hB
  simp only [fdEnd, gA] at hsz h64 ⊢
  set G := B + 4096 + 2 * 2 ^ ℓ with hG'
  rw [semXIR_seq]
  set b4 : List Prim := [.const zD (toWord G), .op .add zA zD zU]
  have hM4 := inv_sem I (P := .blk b4) (by simp +decide [b4, WF, Prim.dst, zD, zA]) ht
  have e4 : ∀ r, r ≠ zD → r ≠ zA → rd (semXIR I (.blk b4) t).M r = rd t.M r := fun r h1 h2 =>
    rdBlk_nw I _ _ (by simp [b4, Prim.dst, Ne.symm h1, Ne.symm h2])
  have t4 : rd (semXIR I (.blk b4) t).M zA = toWord (G + k) := by
    rw [semBlk]; simp only [b4, runPrims, List.foldl, Prim.run]
    simp (disch := first | decide | ((try simp only [size_set]); refine Nat.lt_of_lt_of_le (m := 256) (by decide) ?_; first | assumption | omega)) only
      [rd_set_self, rd_set_ne]
    rw [hU, add_toWord]
  have z4 := size_sem I (.blk b4) t
  generalize semXIR I (.blk b4) t = s4 at hM4 e4 t4 z4 ⊢
  rw [semXIR_seq]
  obtain ⟨c5, hM5⟩ := load_hp I s4 hM4 (d := zV) (p := zA) (by decide) (by decide) t4 (by omega)
  have z5 := size_sem I (.load zV zA) s4
  generalize semXIR I (.load zV zA) s4 = s5 at c5 hM5 z5 ⊢
  rw [semXIR_seq]
  set b6 : List Prim := [.op .xor zV zV zS0]
  have hM6 := inv_sem I (P := .blk b6) (by simp +decide [b6, WF, Prim.dst, zV]) hM5
  have e6 : ∀ r, r ≠ zV → rd (semXIR I (.blk b6) s5).M r = rd s5.M r := fun r h1 =>
    rdBlk_nw I _ _ (by simp [b6, Prim.dst, Ne.symm h1])
  have hz5 := hM5.1; simp only [regs] at hz5
  have t6 : rd (semXIR I (.blk b6) s5).M zV = rd s5.M zV ^^^ rd s5.M zS0 := by
    rw [semBlk]; simp only [b6, runPrims, List.foldl, Prim.run]
    simp (disch := first | decide | ((try simp only [size_set]); refine Nat.lt_of_lt_of_le (m := 256) (by decide) ?_; first | assumption | omega)) only [rd_set_self]
    rfl
  have z6 := size_sem I (.blk b6) s5
  generalize semXIR I (.blk b6) s5 = s6 at hM6 e6 t6 z6 ⊢
  have zA6 : rd s6.M zA = toWord (G + k) := by
    rw [e6 _ (by decide), c5, if_neg (by decide), t4]
  obtain ⟨c7, hM7⟩ := store_hp I s6 hM6 (p := zA) (v := zV) (by decide) (by decide) zA6
    (by simp only [regs]; omega) (by omega) (by omega)
  have hh6 : ∀ x, regs ≤ x → rd s6.M x = rd t.M x := fun x hx => by
    have h := regs_neL hx
    rw [e6 _ h.2.2.2.2.2.2.1, c5, if_neg h.2.2.2.2.2.2.1, e4 _ h.2.2.2.2.2.2.2.2.2.2.2.1 h.2.1]
  refine ⟨?_, fun x hx hx2 => ?_, hM7⟩
  · rw [c7 _ (by simp only [cTmp]; omega), if_pos rfl, t6, c5, if_pos rfl, c5, if_neg (by decide),
      e4 zS0 (by decide) (by decide), e4 (G + k) (by simp only [zD]; omega) (by simp only [zA]; omega)]
  · rw [c7 _ (by simp only [regs, cTmp] at *; omega), if_neg hx2, hh6 x hx]

theorem corrIR_sem (I : Array Word) (s : St) (hM : Inv s.M) {ℓ B : ℕ} {base : ℕ → BF64}
    {s0v s1v : BF64} (hB : regs ≤ B) (hsz : fdEnd B ℓ ≤ s.M.size) (h64 : fdEnd B ℓ < 2 ^ 64)
    (h0 : rdK s.M zS0 = s0v) (h1 : rdK s.M zS1 = s1v)
    (hG : ∀ j < 2 ^ ℓ, rdK s.M (gA B ℓ + j) = base j) :
    (∀ j < 2 ^ ℓ, rdK (semXIR I (corrIR ℓ B) s).M (gA B ℓ + j) = base j +
      if s0v ≠ 0 ∧ (s1v * s0v⁻¹).toBitVec.toNat < 2 ^ ℓ ∧ (s1v * s0v⁻¹).toBitVec.toNat = j
      then s0v else 0) ∧
    (∀ x, regs ≤ x → (x < gA B ℓ ∨ gA B ℓ + 2 ^ ℓ ≤ x) →
      rd (semXIR I (corrIR ℓ B) s).M x = rd s.M x) ∧
    Inv (semXIR I (corrIR ℓ B) s).M := by
  have hs := hM.1
  have hsz' := hsz; have h64' := h64
  simp only [regs] at hs hB
  simp only [fdEnd] at hsz' h64'
  rw [corrIR, semXIR_ite]
  by_cases hz : rd s.M zS0 = 0
  · rw [if_pos hz, semXIR_nilL]
    have hs0 : s0v = 0 := by rw [← h0, rdK, hz]; exact wK_zeroL
    refine ⟨fun j hj => ?_, fun x _ _ => rfl, hM⟩
    rw [hG j hj, if_neg (by simp [hs0]), add_zero]
  rw [if_neg hz]
  have hs0 : s0v ≠ 0 := by rw [← h0, rdK]; exact fun h => hz (wK_eq_zeroL.1 h)
  rw [semXIR_seq]
  have w1 := invK_sem (I := I) (s := s) hM (d := zW) (a := zS0) (by decide) (by decide)
  have f1 : ∀ r, (r < 5 ∨ 12 ≤ r) → r ≠ zW → rd (semXIR I (invK zW zS0) s).M r = rd s.M r :=
    fun r h1 h2 => by rw [invK, sem_blk]; exact invKC_frame zW zS0 h1 h2 s.M
  have hM1 := inv_sem I (wf_invK zW zS0 (by decide)) hM
  have z1 := size_sem I (invK zW zS0) s
  rw [h0] at w1
  generalize semXIR I (invK zW zS0) s = s1 at w1 f1 hM1 z1 ⊢
  rw [semXIR_seq]
  have u2 := mulK_sem (I := I) (s := s1) hM1 (d := zU) (a := zS1) (b := zW) (by decide) (by decide)
    (by decide) (by decide)
  have f2 : ∀ r, (r < 5 ∨ 9 ≤ r) → r ≠ zU → rd (semXIR I (mulK zU zS1 zW) s1).M r = rd s1.M r :=
    fun r h1 h2 => by rw [mulK, sem_blk]; exact mulKC_frame zU zS1 zW h1 h2 s1.M
  have hM2 := inv_sem I (wf_mulK zU zS1 zW (by decide)) hM1
  have z2 := size_sem I (mulK zU zS1 zW) s1
  rw [w1, rdK_eq (f1 _ (by decide) (by decide)), h1] at u2
  generalize semXIR I (mulK zU zS1 zW) s1 = s2 at u2 f2 hM2 z2 ⊢
  have hidx : (s1v * s0v⁻¹).toBitVec.toNat = (rd s2.M zU).toNat := by
    rw [← u2]; rfl
  rw [hidx]
  rw [semXIR_seq]
  set b3 : List Prim := [.const zK (toWord (2 ^ ℓ)), .op .ltu zT zU zK]
  have hM3 := inv_sem I (P := .blk b3) (by simp +decide [b3, WF, Prim.dst, zK, zT]) hM2
  have e3 : ∀ r, r ≠ zK → r ≠ zT → rd (semXIR I (.blk b3) s2).M r = rd s2.M r := fun r h1 h2 =>
    rdBlk_nw I _ _ (by simp [b3, Prim.dst, Ne.symm h1, Ne.symm h2])
  have hz2 := hM2.1; simp only [regs] at hz2
  have t3 : rd (semXIR I (.blk b3) s2).M zT =
      XOp.ltu.eval (rd s2.M zU) (toWord (2 ^ ℓ)) := by
    rw [semBlk]; simp only [b3, runPrims, List.foldl, Prim.run]
    simp (disch := first | decide | ((try simp only [size_set]); refine Nat.lt_of_lt_of_le (m := 256) (by decide) ?_; first | assumption | omega)) only
      [rd_set_self, rd_set_ne]
  have z3 := size_sem I (.blk b3) s2
  have hU3 : rd (semXIR I (.blk b3) s2).M zU = rd s2.M zU := e3 _ (by decide) (by decide)
  generalize semXIR I (.blk b3) s2 = s3 at hM3 e3 t3 z3 hU3 ⊢
  generalize hu : rd s2.M zU = u at t3 hU3 ⊢
  have hlt : u < toWord (2 ^ ℓ) ↔ u.toNat < 2 ^ ℓ := by
    rw [BitVec.lt_def, toNat_toWord (by omega)]
  have hgr : ∀ k, regs ≤ gA B ℓ + k := fun k => by simp only [regs, gA]; omega
  have hh3 : ∀ x, regs ≤ x → rd s3.M x = rd s.M x := fun x hx => by
    have h := regs_neL hx
    rw [e3 _ h.2.2.2.2.2.2.2.2.2.2.1 h.2.2.2.2.1, f2 _ h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 h.2.2.2.2.2.1,
      f1 _ h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2 h.2.2.2.2.2.2.2.1]
  have hS03 : rd s3.M zS0 = rd s.M zS0 := by
    rw [e3 _ (by decide) (by decide), f2 _ (by decide) (by decide), f1 _ (by decide) (by decide)]
  rw [semXIR_ite]
  by_cases hn : u.toNat < 2 ^ ℓ
  · have hz3 : ¬ rd s3.M zT = 0 := by
      rw [t3]; simp only [XOp.eval]; rw [if_pos (hlt.2 hn)]; decide
    rw [if_neg hz3]
    obtain ⟨g1, g2, g3⟩ := corrFixL I s3 hM3 (k := u.toNat) hB (by rw [z3, z2, z1]; exact hsz) h64 hn
      (by rw [hU3, toWord_toNatL])
    refine ⟨fun j hj => ?_, fun x hx hx2 => ?_, g3⟩
    · by_cases hju : u.toNat = j
      · subst hju
        rw [rdK, g1, wK_xor, ← rdK, ← rdK, rdK_eq hS03, rdK_eq (hh3 _ (hgr _)), hG _ hj,
          h0, if_pos ⟨hs0, hn, rfl⟩]
      · rw [rdK_eq (g2 _ (hgr _) (by omega)),
          rdK_eq (hh3 _ (hgr _)), hG j hj, if_neg (fun h => hju h.2.2), add_zero]
    · rw [g2 x hx (by simp only [gA] at hx2 ⊢; omega), hh3 x hx]
  · have hz3 : rd s3.M zT = 0 := by
      rw [t3]; simp only [XOp.eval]; rw [if_neg (fun h => hn (hlt.1 h))]
    rw [if_pos hz3, semXIR_nilL]
    refine ⟨fun j hj => ?_, fun x hx _ => hh3 x hx, hM3⟩
    rw [rdK_eq (hh3 _ (hgr _)), hG j hj, if_neg (fun h => hn h.2.1), add_zero]

/-! ## `f` on the coset -/

theorem cosBody_semL (I : Array Word) (s' : St) (i1 : Inv s'.M) {a1 a2 a3 : ℕ} {e l : BF64}
    (r1 : regs ≤ a1) (r2 : regs ≤ a2) (r3 : regs ≤ a3) (b1 : a1 + 1 < 2 ^ 64) (b2 : a2 + 1 < 2 ^ 64)
    (b3 : a3 + 1 < 2 ^ 64) (z1 : a1 < s'.M.size) (z2 : a2 < s'.M.size) (h12 : a1 ≠ a2)
    (h13 : a1 ≠ a3) (hA : rd s'.M zA = toWord a1) (hB : rd s'.M zB = toWord a2)
    (hC : rd s'.M zC = toWord a3) (hV : rd s'.M zV = 0) (he : rdK s'.M a2 = e)
    (hl : rdK s'.M a3 = l) :
    Inv (semXIR I cosBody s').M ∧ rd (semXIR I cosBody s').M zA = toWord (a1 + 1) ∧
    rd (semXIR I cosBody s').M zB = toWord (a2 + 1) ∧ rd (semXIR I cosBody s').M zC = toWord (a3 + 1) ∧
    rd (semXIR I cosBody s').M zV = 0 ∧ rd (semXIR I cosBody s').M a1 = 0 ∧
    rdK (semXIR I cosBody s').M a2 = e * l ∧
    (∀ x, regs ≤ x → x ≠ a1 → x ≠ a2 → rd (semXIR I cosBody s').M x = rd s'.M x) := by
  have hs := i1.1
  simp only [regs] at hs
  have h1 := regs_neL r1
  have h2 := regs_neL r2
  have h3 := regs_neL r3
  have t1 : a1 ≠ cTmp := h1.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have t2 : a2 ≠ cTmp := h2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have t3 : a3 ≠ cTmp := h3.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  simp only [regs] at r1 r2 r3
  rw [cosBody, semXIR_seq]
  obtain ⟨c1, hM1⟩ := store_hp I s' i1 (p := zA) (v := zV) (by decide) (by decide) hA r1
    (by omega) z1
  have q1 := size_sem I (.store zA zV) s'
  generalize semXIR I (.store zA zV) s' = s1 at c1 hM1 q1 ⊢
  rw [semXIR_seq]
  obtain ⟨c2, hM2⟩ := load_hp I s1 hM1 (d := zU) (p := zB) (by decide) (by decide)
    (by rw [c1 _ (by decide), if_neg (by simp only [zB]; omega), hB]) (by omega)
  have q2 := size_sem I (.load zU zB) s1
  generalize semXIR I (.load zU zB) s1 = s2 at c2 hM2 q2 ⊢
  rw [semXIR_seq]
  obtain ⟨c3, hM3⟩ := load_hp I s2 hM2 (d := zW) (p := zC) (by decide) (by decide)
    (by rw [c2, if_neg (by decide), c1 _ (by decide), if_neg (by simp only [zC]; omega), hC]) (by omega)
  have q3 := size_sem I (.load zW zC) s2
  generalize semXIR I (.load zW zC) s2 = s3 at c3 hM3 q3 ⊢
  rw [semXIR_seq]
  have m4 := mulK_sem (I := I) (s := s3) hM3 (d := zE) (a := zU) (b := zW) (by decide) (by decide)
    (by decide) (by decide)
  have f4 : ∀ r, (r < 5 ∨ 9 ≤ r) → r ≠ zE → rd (semXIR I (mulK zE zU zW) s3).M r = rd s3.M r :=
    fun r h1 h2 => by rw [mulK, sem_blk]; exact mulKC_frame zE zU zW h1 h2 s3.M
  have hM4 := inv_sem I (wf_mulK zE zU zW (by decide)) hM3
  have q4 := size_sem I (mulK zE zU zW) s3
  have u3 : rdK s3.M zU = e := by
    rw [rdK, c3, if_neg (by decide), c2, if_pos rfl, c1 _ t2,
      if_neg (Ne.symm h12), ← rdK, he]
  have w3 : rdK s3.M zW = l := by
    rw [rdK, c3, if_pos rfl, c2, if_neg h3.2.2.2.2.2.1, c1 _ t3,
      if_neg (Ne.symm h13), ← rdK, hl]
  rw [u3, w3] at m4
  generalize semXIR I (mulK zE zU zW) s3 = s4 at m4 f4 hM4 q4 ⊢
  rw [semXIR_seq]
  have zB4 : rd s4.M zB = toWord a2 := by
    rw [f4 _ (by decide) (by decide), c3, if_neg (by decide), c2, if_neg (by decide), c1 _ (by decide),
      if_neg (by simp only [zB]; omega), hB]
  obtain ⟨c5, hM5⟩ := store_hp I s4 hM4 (p := zB) (v := zE) (by decide) (by decide) zB4 r2
    (by omega) (by omega)
  have q5 := size_sem I (.store zB zE) s4
  generalize semXIR I (.store zB zE) s4 = s5 at c5 hM5 q5 ⊢
  set b6 : List Prim := [.op .add zA zA cOne, .op .add zB zB cOne, .op .add zC zC cOne]
  have hM6 := inv_sem I (P := .blk b6) (by simp +decide [b6, WF, Prim.dst, zA, zB, zC]) hM5
  have e6 : ∀ r, r ≠ zA → r ≠ zB → r ≠ zC → rd (semXIR I (.blk b6) s5).M r = rd s5.M r :=
    fun r h1 h2 h3 => rdBlk_nw I _ _ (by simp [b6, Prim.dst, Ne.symm h1, Ne.symm h2, Ne.symm h3])
  have hz5 := hM5.1; simp only [regs] at hz5
  have hone : rd s5.M cOne = 1 := hM5.2 0 (by decide)
  -- registers from `s5` back to `s'`
  have back : ∀ r, r ≠ zU → r ≠ zW → r ≠ zE → r ≠ cTmp → (r < 5 ∨ 9 ≤ r) → r ≠ a1 → r ≠ a2 →
      rd s5.M r = rd s'.M r := fun r g1 g2 g3 g4 g5 g6 g7 => by
    rw [c5 _ g4, if_neg g7, f4 _ g5 g3, c3, if_neg g2, c2, if_neg g1, c1 _ g4, if_neg g6]
  refine ⟨hM6, ?_, ?_, ?_, ?_, ?_, ?_, fun x hx g1 g2 => ?_⟩
  · rw [semBlk]; simp only [b6, runPrims, List.foldl, Prim.run]
    simp (disch := first | decide | ((try simp only [size_set]); refine Nat.lt_of_lt_of_le (m := 256) (by decide) ?_; first | assumption | omega)) only
      [rd_set_self, rd_set_ne]
    rw [hone, back _ (by decide) (by decide) (by decide) (by decide) (by decide)
      (by simp only [zA]; omega) (by simp only [zA]; omega), hA, add_one_toWord]
  · rw [semBlk]; simp only [b6, runPrims, List.foldl, Prim.run]
    simp (disch := first | decide | ((try simp only [size_set]); refine Nat.lt_of_lt_of_le (m := 256) (by decide) ?_; first | assumption | omega)) only
      [rd_set_self, rd_set_ne]
    rw [hone, back _ (by decide) (by decide) (by decide) (by decide) (by decide)
      (by simp only [zB]; omega) (by simp only [zB]; omega), hB, add_one_toWord]
  · rw [semBlk]; simp only [b6, runPrims, List.foldl, Prim.run]
    simp (disch := first | decide | ((try simp only [size_set]); refine Nat.lt_of_lt_of_le (m := 256) (by decide) ?_; first | assumption | omega)) only
      [rd_set_self, rd_set_ne]
    rw [hone, back _ (by decide) (by decide) (by decide) (by decide) (by decide)
      (by simp only [zC]; omega) (by simp only [zC]; omega), hC, add_one_toWord]
  · rw [e6 _ (by decide) (by decide) (by decide), back _ (by decide) (by decide) (by decide) (by decide)
      (by decide) (by simp only [zV]; omega) (by simp only [zV]; omega), hV]
  · rw [e6 _ h1.2.1 h1.2.2.1 h1.2.2.2.1, c5 _ t1, if_neg h12,
      f4 _ h1.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 h1.2.2.2.2.2.2.2.2.2.2.2.2.1, c3, if_neg h1.2.2.2.2.2.2.2.1,
      c2, if_neg h1.2.2.2.2.2.1, c1 _ t1, if_pos rfl, hV]
  · rw [rdK_eq (e6 _ h2.2.1 h2.2.2.1 h2.2.2.2.1), rdK, c5 _ t2, if_pos rfl,
      ← rdK, m4]
  · have h := regs_neL hx
    rw [e6 _ h.2.1 h.2.2.1 h.2.2.2.1, back _ h.2.2.2.2.2.1 h.2.2.2.2.2.2.2.1 h.2.2.2.2.2.2.2.2.2.2.2.2.1
      h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 g1 g2]

theorem cosIR_sem (I : Array Word) (s : St) (hM : Inv s.M) {ℓ B : ℕ} {E Li : ℕ → BF64}
    (hB : regs ≤ B) (hsz : fdEnd B ℓ ≤ s.M.size) (h64 : fdEnd B ℓ < 2 ^ 64)
    (hE : ∀ i < 2 ^ (ℓ + 1), rdK s.M (gA B ℓ + i) = E i)
    (hL : ∀ j < 2 ^ ℓ, rdK s.M (iA B ℓ + j) = Li j) :
    (∀ i < 2 ^ (ℓ + 1), rdK (semXIR I (cosIR ℓ B) s).M (gA B ℓ + i) =
      if i < 2 ^ ℓ then 0 else E i * Li (i - 2 ^ ℓ)) ∧
    (∀ x, regs ≤ x → (x < gA B ℓ ∨ gA B ℓ + 2 ^ (ℓ + 1) ≤ x) →
      rd (semXIR I (cosIR ℓ B) s).M x = rd s.M x) ∧
    Inv (semXIR I (cosIR ℓ B) s).M := by
  have hs := hM.1
  simp only [regs] at hs hB
  have hp : 2 ^ (ℓ + 1) = 2 * 2 ^ ℓ := by rw [pow_succ]; ring
  rw [cosIR, semXIR_seq]
  simp only [fdEnd, gA, outA, iA, hp] at hsz h64 hE hL ⊢
  set b0 : List Prim := [.const zA (toWord (B + 4096 + 2 * 2 ^ ℓ)),
    .const zB (toWord (B + 4096 + 3 * 2 ^ ℓ)), .const zC (toWord (B + 4096 + 6 * 2 ^ ℓ)), .const zV 0,
    .const zN1 (toWord (2 ^ ℓ))]
  have w0 : WF (.blk b0) := by simp +decide [b0, WF, Prim.dst, zA, zB, zC, zV, zN1]
  have hM0 := inv_sem I w0 hM
  have r0 : rd (semXIR I (.blk b0) s).M zA = toWord (B + 4096 + 2 * 2 ^ ℓ + 0) ∧
      rd (semXIR I (.blk b0) s).M zB = toWord (B + 4096 + 3 * 2 ^ ℓ + 0) ∧
      rd (semXIR I (.blk b0) s).M zC = toWord (B + 4096 + 6 * 2 ^ ℓ + 0) ∧
      rd (semXIR I (.blk b0) s).M zV = 0 ∧
      rd (semXIR I (.blk b0) s).M zN1 = toWord (2 ^ ℓ) := by
    rw [semBlk]; simp only [b0, runPrims, List.foldl, Prim.run]
    refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;>
    simp (disch := first | decide | ((try simp only [size_set]); refine Nat.lt_of_lt_of_le (m := 256) (by decide) ?_; first | assumption | omega)) only
      [rd_set_self, rd_set_ne] <;> rfl
  have k0 : ∀ r, regs ≤ r → rd (semXIR I (.blk b0) s).M r = rd s.M r := fun r hr => by
    simp only [regs] at hr
    refine rdBlk_nw I _ s ?_
    simp only [b0, List.mem_cons, List.mem_nil_iff, or_false]
    rintro p (rfl | rfl | rfl | rfl | rfl) <;> simp only [Prim.dst, zA, zB, zC, zV, zN1] <;> first | decide | exact Nat.ne_of_lt (Nat.lt_of_lt_of_le (by decide) hr)
  have z0 := size_sem I (.blk b0) s
  generalize semXIR I (.blk b0) s = s0 at hM0 r0 k0 z0 ⊢
  obtain ⟨a0, b0', c0, v0, n0⟩ := r0
  set G := B + 4096 + 2 * 2 ^ ℓ with hG'
  have hR4 : ∀ {k1 k2 k3 : ℕ}, regs ≤ B + k1 + k2 + k3 :=
    Nat.le_add_right_of_le (Nat.le_add_right_of_le (Nat.le_add_right_of_le hB))
  have hGr : ∀ {k : ℕ}, regs ≤ G + k := Nat.le_add_right_of_le (Nat.le_add_right_of_le (Nat.le_add_right_of_le hB))
  let R : ℕ → Mem → Prop := fun j M => rd M zA = toWord (G + j) ∧
    rd M zB = toWord (B + 4096 + 3 * 2 ^ ℓ + j) ∧ rd M zC = toWord (B + 4096 + 6 * 2 ^ ℓ + j) ∧
    rd M zV = 0 ∧
    (∀ i < 2 ^ ℓ, rdK M (G + i) = if i < j then 0 else E i) ∧
    (∀ i < 2 ^ ℓ, rdK M (G + 2 ^ ℓ + i) = if i < j then E (2 ^ ℓ + i) * Li i else E (2 ^ ℓ + i)) ∧
    (∀ x, regs ≤ x → (x < G ∨ G + 2 * 2 ^ ℓ ≤ x) → rd M x = rd s.M x)
  have hR : ∀ j (M M' : Mem), (∀ i, i ≠ zC1 → i ≠ cTmp → rd M' i = rd M i) → R j M → R j M' := by
    rintro j M M' hMM ⟨r1, r2, r3, r4, r5, r6, r7⟩
    refine ⟨by rw [hMM _ (by decide) (by decide), r1], by rw [hMM _ (by decide) (by decide), r2],
      by rw [hMM _ (by decide) (by decide), r3], by rw [hMM _ (by decide) (by decide), r4],
      fun i hi => ?_, fun i hi => ?_, fun x hx hx2 => ?_⟩
    · have h := regs_neL (show regs ≤ G + i from hGr)
      rw [← r5 i hi]; exact rdK_eq (hMM _ h.2.2.2.2.2.2.2.2.2.2.2.2.2.1 h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1)
    · have h := regs_neL (show regs ≤ G + 2 ^ ℓ + i from Nat.le_add_right_of_le hGr)
      rw [← r6 i hi]; exact rdK_eq (hMM _ h.2.2.2.2.2.2.2.2.2.2.2.2.2.1 h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1)
    · have h := regs_neL hx
      rw [hMM _ h.2.2.2.2.2.2.2.2.2.2.2.2.2.1 h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1, r7 x hx hx2]
  have h0 : R 0 s0.M := by
    refine ⟨a0, b0', c0, v0, fun i hi => ?_, fun i hi => ?_, fun x hx _ => k0 x hx⟩
    · rw [if_neg (by omega), rdK_eq (k0 _ hGr), hE i (by omega)]
    · rw [if_neg (by omega), rdK_eq (k0 _ (Nat.le_add_right_of_le hGr)), ← hE (2 ^ ℓ + i) (by omega)]
      exact congrArg (rdK _) (by ring)
  have hb : ∀ j (s' : St), j < 2 ^ ℓ → Inv s'.M → s'.M.size = s0.M.size → R j s'.M →
      Inv (semXIR I cosBody s').M ∧ R (j + 1) (semXIR I cosBody s').M := by
    rintro j s' hj i1 i2 ⟨r1, r2, r3, r4, r5, r6, r7⟩
    have hGn : B + 4096 + 3 * 2 ^ ℓ + j = G + 2 ^ ℓ + j := by omega
    obtain ⟨d1, d2, d3, d4, d5, d6, d7, d8⟩ := cosBody_semL I s' i1 (a1 := G + j)
      (a2 := B + 4096 + 3 * 2 ^ ℓ + j) (a3 := B + 4096 + 6 * 2 ^ ℓ + j)
      (e := E (2 ^ ℓ + j)) (l := Li j)
      hGr hR4 hR4
      (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) r1 r2 r3 r4
      (by rw [hGn, r6 j hj, if_neg (by omega)])
      (by rw [rdK_eq (r7 _ hR4 (by omega)), hL j hj])
    refine ⟨d1, by rw [d2]; rfl, by rw [d3]; rfl, by rw [d4]; rfl, d5, fun i hi => ?_, fun i hi => ?_,
      fun x hx hx2 => ?_⟩
    · by_cases hij : i = j
      · subst hij; rw [rdK, d6, if_pos (by omega)]; rfl
      · rw [rdK_eq (d8 _ hGr (by omega) (by omega)), r5 i hi]
        by_cases h' : i < j
        · rw [if_pos h', if_pos (by omega)]
        · rw [if_neg h', if_neg (by omega)]
    · by_cases hij : i = j
      · subst hij; rw [← hGn, d7, if_pos (by omega)]
      · rw [rdK_eq (d8 _ (Nat.le_add_right_of_le hGr) (by omega) (by omega)), r6 i hi]
        by_cases h' : i < j
        · rw [if_pos h', if_pos (by omega)]
        · rw [if_neg h', if_neg (by omega)]
    · rw [d8 x hx (by omega) (by omega), r7 x hx hx2]
  have hfin := loopK_gen I cosBody s0 hM0 (by decide) (by decide) (by decide) n0 (by omega) R hR h0
    (fun j s' hj i1 i2 i3 => hb j s' hj i1 i2 i3)
  obtain ⟨⟨_, _, _, _, f5, f6, f7⟩, f8, _⟩ := hfin
  refine ⟨fun i hi => ?_, fun x hx hx2 => f7 x hx hx2, f8⟩
  by_cases h : i < 2 ^ ℓ
  · rw [f5 i h, if_pos h, if_pos h]
  · obtain ⟨i', rfl⟩ := Nat.exists_eq_add_of_le (not_lt.1 h)
    rw [← Nat.add_assoc, f6 i' (by omega), if_pos (by omega), if_neg h, Nat.add_sub_cancel_left]

/-! ## One lane -/

theorem wf_laneIR (N ℓ m B : ℕ) : WF (laneIR N ℓ m B) := by
  refine ⟨?_, ?_, ?_, ?_, wf_bflyNIR N _ _, wf_fwdNIR N _ _, ?_, ?_, wf_bflyNIR N _ _⟩
  · refine ⟨by simp +decide [WF, Prim.dst, zA, zV, zN1], ⟨by decide, by decide, by decide⟩, by decide,
      ?_, ?_⟩
    · exact nw_seq (fun h => by simp only [Writes, cTmp, zC1] at h; omega)
        (nw_blk (by simp +decide [Prim.dst, zA, zC1]))
    · exact ⟨by simp [WF, zA, cTmp], by simp +decide [WF, Prim.dst, zA]⟩
  · refine ⟨by simp +decide [WF, Prim.dst, zC, zS0, zS1, zN1], ⟨by decide, by decide, by decide⟩,
      by decide, ?_, ?_⟩
    · simp only [synBody]
      refine nw_seq (fun h => ?_) (nw_seq (nw_blk ?_) (nw_seq (fun h => ?_) (nw_seq (fun h => ?_)
        (nw_seq (nw_mulK (by decide) (by decide)) (nw_seq (fun h => ?_) (nw_seq (nw_blk ?_)
          (nw_seq (nw_mulK (by decide) (by decide)) (nw_blk ?_))))))))
      all_goals first
        | (simp only [Writes, zI, zU, zV, cTmp, zC1] at h; omega)
        | simp +decide [Prim.dst, zD, zA, zB, zE, zS0, zS1, zC, zC1]
    · refine ⟨by simp [WF, zI], by simp +decide [WF, Prim.dst, zD, zA, zB, zE], by simp [WF, zU],
        by simp [WF, zV], wf_mulK _ _ _ (by decide), by simp [WF, zE, cTmp],
        by simp +decide [WF, Prim.dst, zS0], wf_mulK _ _ _ (by decide),
        by simp +decide [WF, Prim.dst, zS1, zC]⟩
  · refine ⟨⟨wf_invK _ _ (by decide), wf_mulK _ _ _ (by decide),
      by simp +decide [WF, Prim.dst, zK, zT], ⟨by simp +decide [WF, Prim.dst, zD, zA], by simp [WF, zV],
      by simp +decide [WF, Prim.dst, zV], by simp [WF, zA, cTmp]⟩, by simp [WF]⟩, by simp [WF]⟩
  · simp +decide [WF, Prim.dst, rA0]
  · refine ⟨by simp +decide [WF, Prim.dst, zA, zB, zC, zV, zN1], ⟨by decide, by decide, by decide⟩,
      by decide, ?_, ?_⟩
    · simp only [cosBody]
      refine nw_seq (fun h => ?_) (nw_seq (fun h => ?_) (nw_seq (fun h => ?_)
        (nw_seq (nw_mulK (by decide) (by decide)) (nw_seq (fun h => ?_) (nw_blk ?_)))))
      all_goals first
        | (simp only [Writes, zU, zW, cTmp, zC1] at h; omega)
        | simp +decide [Prim.dst, zA, zB, zC, zC1]
    · exact ⟨by simp [WF, zA, cTmp], by simp [WF, zU], by simp [WF, zW], wf_mulK _ _ _ (by decide),
        by simp [WF, zB, cTmp], by simp +decide [WF, Prim.dst, zA, zB, zC]⟩
  · simp +decide [WF, Prim.dst, rA0]

theorem hasOut_laneIRL (N ℓ m B : ℕ) : hasOutL (laneIR N ℓ m B) = false := by
  simp [hasOutL, laneIR, zeroGIR, zeroBodyG, synIR, synBody, corrIR, cosIR, cosBody, mulK, invK,
    bflyNIR, lvlNStep, levelNIR, pairNBody, alphaNIR, alphaBody, arithIR, addK, fwdNIR, fStepN,
    flevelNIR, fpairNBody, farithIR]

/-- The lane's front: zero, syndromes, correction leave `gIn` on `V` and `0` on the coset. -/
theorem laneFrontL (I : Array Word) (s : St) (hM : Inv s.M) {N ℓ B : ℕ} {S : List ℕ} {y : ℕ → BF64}
    (hN : ℓ + 1 ≤ N) (hB : regs ≤ B) (hsz : fdEnd B ℓ ≤ s.M.size)
    (h64 : fdEnd B ℓ < 2 ^ 64) (hm : S.length ≤ 2 ^ ℓ) (hSn : ∀ j ∈ S, j < 2 ^ ℓ)
    (hL : LamOk N ℓ B S s.M) (hy : ∀ j < 2 ^ ℓ, rdK s.M (yA B ℓ + j) = y j) :
    (∀ j < 2 ^ ℓ, rdK (semXIR I (corrIR ℓ B) (semXIR I (synIR ℓ S.length B)
      (semXIR I (zeroGIR ℓ B) s))).M (gA B ℓ + j) = gIn N ℓ S y j) ∧
    (∀ j < 2 ^ ℓ, rd (semXIR I (corrIR ℓ B) (semXIR I (synIR ℓ S.length B)
      (semXIR I (zeroGIR ℓ B) s))).M (gA B ℓ + 2 ^ ℓ + j) = 0) ∧
    (∀ x, regs ≤ x → (x < gA B ℓ ∨ gA B ℓ + 2 ^ (ℓ + 1) ≤ x) → rd (semXIR I (corrIR ℓ B)
      (semXIR I (synIR ℓ S.length B) (semXIR I (zeroGIR ℓ B) s))).M x = rd s.M x) ∧
    Inv (semXIR I (corrIR ℓ B) (semXIR I (synIR ℓ S.length B) (semXIR I (zeroGIR ℓ B) s))).M ∧
    (semXIR I (corrIR ℓ B) (semXIR I (synIR ℓ S.length B)
      (semXIR I (zeroGIR ℓ B) s))).M.size = s.M.size := by
  obtain ⟨L1, L2, L3, L4⟩ := hL
  have hp : 2 ^ (ℓ + 1) = 2 * 2 ^ ℓ := by rw [pow_succ]; ring
  have hsz' : B + 4096 + 11 * 2 ^ ℓ ≤ s.M.size := hsz
  have h64' : B + 4096 + 11 * 2 ^ ℓ < 2 ^ 64 := h64
  have hB' : 256 ≤ B := hB
  have hG : gA B ℓ = B + 4096 + 2 * 2 ^ ℓ := rfl
  have hT : tA B ℓ = B + 4096 + 4 * 2 ^ ℓ := rfl
  have hY : yA B ℓ = B + 4096 + 2 ^ ℓ := rfl
  have hS : sA B = B + 4096 := rfl
  have outG : ∀ x, x < B + 4096 + 2 * 2 ^ ℓ → x < gA B ℓ ∨ gA B ℓ + 2 ^ (ℓ + 1) ≤ x :=
    fun x hx => Or.inl (by rw [hG]; exact hx)
  have outG' : ∀ x, B + 4096 + 4 * 2 ^ ℓ ≤ x → x < gA B ℓ ∨ gA B ℓ + 2 ^ (ℓ + 1) ≤ x :=
    fun x hx => Or.inr (by rw [hG, hp]; omega)
  obtain ⟨z1, zf1, zi1⟩ := zeroGIR_sem I s hM hB hsz h64
  have q1 := size_sem I (zeroGIR ℓ B) s
  generalize semXIR I (zeroGIR ℓ B) s = s1 at z1 zf1 zi1 q1 ⊢
  obtain ⟨y2, a2, b2, zf2, zi2⟩ := synIR_sem I s1 zi1 (y := y) (L := lam N S ℓ) hB
    (by rw [q1]; exact hsz) h64 hm hSn
    (fun i hi => by rw [zf1 _ (by rw [hS]; simp only [regs]; omega) (outG _ (by rw [hS]; omega)), L2 i hi])
    (fun j hj => by
      rw [rdK_eq (zf1 _ (by rw [hY]; simp only [regs]; omega) (outG _ (by rw [hY]; omega))), hy j hj])
    (fun j hj => by
      rw [rdK_eq (zf1 _ (by rw [hT]; simp only [regs]; omega) (outG' _ (by rw [hT]; omega))),
        L3 j (by omega)])
    z1
  have q2 := size_sem I (synIR ℓ S.length B) s1
  generalize semXIR I (synIR ℓ S.length B) s1 = s2 at y2 a2 b2 zf2 zi2 q2 ⊢
  obtain ⟨y3, zf3, zi3⟩ := corrIR_sem I s2 zi2 (base := fun j => if j ∈ S then y j * lam N S ℓ j else 0)
    (s0v := syn0 N ℓ S y) (s1v := syn1 N ℓ S y) hB (by rw [q2, q1]; exact hsz) h64 a2 b2
    (fun j hj => y2 j (by omega))
  have q3 := size_sem I (corrIR ℓ B) s2
  generalize semXIR I (corrIR ℓ B) s2 = s3 at y3 zf3 zi3 q3 ⊢
  refine ⟨fun j hj => ?_, fun j hj => ?_, fun x hx hx2 => ?_, zi3, by rw [q3, q2, q1]⟩
  · rw [y3 j hj, gIn]; rfl
  · have e := y2 (2 ^ ℓ + j) (by omega)
    rw [if_neg (fun h => absurd (hSn _ h) (by omega))] at e
    rw [zf3 _ (by rw [hG]; simp only [regs]; omega) (Or.inr (by omega))]
    rw [← Nat.add_assoc] at e
    exact wK_eq_zeroL.1 e
  · rw [zf3 x hx (by rcases hx2 with h | h <;> [left; right] <;> omega), zf2 x hx hx2, zf1 x hx hx2]

/-- The lane's tail: season 1's NTTs and the coset step, from `gIn` on `V` and `0` on the coset. -/
theorem laneTailL (I : Array Word) (t : St) (ht : Inv t.M) {N ℓ B : ℕ} {S : List ℕ} {y : ℕ → BF64}
    (hN : ℓ + 1 ≤ N) (hN64 : N ≤ 64) (hB : regs ≤ B) (hsz : fdEnd B ℓ ≤ t.M.size)
    (h64 : fdEnd B ℓ < 2 ^ 64)
    (L1 : ∀ v < N, ∀ i < N, rdK t.M (tbA B + N * v + i) = (wRow ptK N v).getD i 0)
    (L4 : ∀ j < 2 ^ ℓ, rdK t.M (iA B ℓ + j) = (lam N S ℓ (2 ^ ℓ + j))⁻¹)
    (g3 : ∀ j < 2 ^ ℓ, rdK t.M (gA B ℓ + j) = gIn N ℓ S y j)
    (hi3 : ∀ j < 2 ^ ℓ, rd t.M (gA B ℓ + 2 ^ ℓ + j) = 0) :
    (∀ x < 2 ^ ℓ, rdK (semXIR I (.seq (.blk [.const rA0 (toWord (gA B ℓ))]) (.seq (bflyNIR N ℓ (tbA B))
      (.seq (fwdNIR N (ℓ + 1) (tbA B)) (.seq (cosIR ℓ B) (.seq (.blk [.const rA0 (toWord (gA B ℓ))])
      (bflyNIR N (ℓ + 1) (tbA B))))))) t).M (outA B ℓ + x) = fd1 N ℓ S y x) ∧
    Inv (semXIR I (.seq (.blk [.const rA0 (toWord (gA B ℓ))]) (.seq (bflyNIR N ℓ (tbA B))
      (.seq (fwdNIR N (ℓ + 1) (tbA B)) (.seq (cosIR ℓ B) (.seq (.blk [.const rA0 (toWord (gA B ℓ))])
      (bflyNIR N (ℓ + 1) (tbA B))))))) t).M ∧
    (∀ x, regs ≤ x → (x < gA B ℓ ∨ gA B ℓ + 2 ^ (ℓ + 1) ≤ x) →
      rd (semXIR I (.seq (.blk [.const rA0 (toWord (gA B ℓ))]) (.seq (bflyNIR N ℓ (tbA B))
      (.seq (fwdNIR N (ℓ + 1) (tbA B)) (.seq (cosIR ℓ B) (.seq (.blk [.const rA0 (toWord (gA B ℓ))])
      (bflyNIR N (ℓ + 1) (tbA B))))))) t).M x = rd t.M x) := by
  have hB' : 256 ≤ B := hB
  have hp : 2 ^ (ℓ + 1) = 2 * 2 ^ ℓ := by rw [pow_succ]; ring
  have hsz' : B + 4096 + 11 * 2 ^ ℓ ≤ t.M.size := hsz
  have h64' : B + 4096 + 11 * 2 ^ ℓ < 2 ^ 64 := h64
  have hNN : N * N ≤ 4096 := Nat.mul_le_mul hN64 hN64
  have htab : ∀ v < N, ∀ i < N, N * v + i < 4096 := fun v hv i hi => by
    have : N * v + N ≤ N * N := by rw [← Nat.mul_succ]; exact Nat.mul_le_mul_left N hv
    omega
  have hG : gA B ℓ = B + 4096 + 2 * 2 ^ ℓ := rfl
  have hI : iA B ℓ = B + 4096 + 6 * 2 ^ ℓ := rfl
  have hO : outA B ℓ = B + 4096 + 3 * 2 ^ ℓ := rfl
  have hTb : tbA B = B := rfl
  have outG : ∀ x, x < B + 4096 + 2 * 2 ^ ℓ → x < gA B ℓ ∨ gA B ℓ + 2 ^ (ℓ + 1) ≤ x :=
    fun x hx => Or.inl (by rw [hG]; exact hx)
  have outG' : ∀ x, B + 4096 + 4 * 2 ^ ℓ ≤ x → x < gA B ℓ ∨ gA B ℓ + 2 ^ (ℓ + 1) ≤ x :=
    fun x hx => Or.inr (by rw [hG, hp]; omega)
  have hrA : ∀ x, regs ≤ x → x ≠ rA0 := fun x hx => Nat.ne_of_gt (Nat.lt_of_lt_of_le (by decide) hx)
  have hTr : ∀ {k1 k2 : ℕ}, regs ≤ tbA B + k1 + k2 := Nat.le_add_right_of_le (Nat.le_add_right_of_le hB)
  have hGr : regs ≤ gA B ℓ := by rw [hG]; exact Nat.le_add_right_of_le (Nat.le_add_right_of_le hB)
  have hGr' : ∀ {k : ℕ}, regs ≤ gA B ℓ + k := Nat.le_add_right_of_le hGr
  rw [semXIR_seq]
  have hM4 := inv_sem I (P := .blk [.const rA0 (toWord (gA B ℓ))]) (by simp +decide [WF, Prim.dst, rA0]) ht
  have e4 : ∀ x, x ≠ rA0 → rd (semXIR I (.blk [.const rA0 (toWord (gA B ℓ))]) t).M x = rd t.M x :=
    fun x hx => rdBlk_nw I _ _ (by simp [Prim.dst, Ne.symm hx])
  have hz3 := ht.1; simp only [regs] at hz3
  have a4 : rd (semXIR I (.blk [.const rA0 (toWord (gA B ℓ))]) t).M rA0 = toWord (gA B ℓ) := by
    rw [semBlk]; simp only [runPrims, List.foldl, Prim.run]
    exact rd_set_self (Nat.lt_of_lt_of_le (m := 256) (by decide) (by assumption))
  have q4 := size_sem I (.blk [.const rA0 (toWord (gA B ℓ))]) t
  generalize semXIR I (.blk [.const rA0 (toWord (gA B ℓ))]) t = s4 at hM4 e4 a4 q4 ⊢
  have hW4 : ∀ v < N, ∀ i < N, rdK s4.M (tbA B + N * v + i) = (wRow ptK N v).getD i 0 :=
    fun v hv i hi => by
      have := htab v hv i hi
      rw [rdK_eq (e4 _ (hrA _ hTr)), L1 v hv i hi]
  rw [semXIR_seq]
  obtain ⟨n5, nf5, ni5⟩ := bflyNIR_sem (N := N) I s4 hM4 hN64 (A := gA B ℓ) (tb := tbA B) (ℓ := ℓ)
    (Y := gIn N ℓ S y) (by omega) hGr (by rw [hG]; omega)
    (by rw [hG, q4]; omega) (by rw [hTb]; exact hB) (by rw [hTb]; omega)
    (Or.inl (by rw [hTb, hG]; omega)) a4 hW4
    (fun i hi => by rw [rdK_eq (e4 _ (hrA _ hGr')), g3 i hi])
  have a5 : rd (semXIR I (bflyNIR N ℓ (tbA B)) s4).M rA0 = toWord (gA B ℓ) := by
    rw [frame I _ s4 (wf_bflyNIR N ℓ _) hM4 rA0 (by decide) (bflyNIR_nwAL N ℓ _), a4]
  have q5 := size_sem I (bflyNIR N ℓ (tbA B)) s4
  generalize semXIR I (bflyNIR N ℓ (tbA B)) s4 = s5 at n5 nf5 ni5 a5 q5 ⊢
  have F5 : ∀ x, regs ≤ x → (x < gA B ℓ ∨ gA B ℓ + 2 ^ (ℓ + 1) ≤ x) → rd s5.M x = rd t.M x :=
    fun x hx hx2 => by
      rw [nf5 x hx (by rcases hx2 with h | h <;> [left; right] <;> omega), e4 _ (hrA x hx)]
  have hW5 : ∀ v < N, ∀ i < N, rdK s5.M (tbA B + N * v + i) = (wRow ptK N v).getD i 0 :=
    fun v hv i hi => by
      have := htab v hv i hi
      rw [rdK_eq (F5 _ hTr (outG _ (by rw [hTb]; omega))), L1 v hv i hi]
  rw [semXIR_seq]
  obtain ⟨n6, nf6, ni6⟩ := fwdNIR_sem (N := N) I s5 ni5 hN64 (A := gA B ℓ) (tb := tbA B) (ℓ := ℓ + 1)
    (Y := fun i => if i < 2 ^ ℓ then bflyRun ptK N 0 ℓ (gIn N ℓ S y) i else 0) hN
    hGr (by rw [hG, hp]; omega)
    (by rw [hG, hp, q5, q4]; omega) (by rw [hTb]; exact hB) (by rw [hTb]; omega)
    (Or.inl (by rw [hTb, hG]; omega)) a5 hW5
    (fun i hi => by
      by_cases h : i < 2 ^ ℓ
      · rw [if_pos h, n5 i h]
      · obtain ⟨i', rfl⟩ := Nat.exists_eq_add_of_le (not_lt.1 h)
        rw [if_neg h, rdK_eq (nf5 _ hGr' (Or.inr (by omega))),
          rdK_eq (e4 _ (hrA _ hGr')), rdK, ← Nat.add_assoc,
          hi3 i' (by omega)]
        rfl)
  have q6 := size_sem I (fwdNIR N (ℓ + 1) (tbA B)) s5
  generalize semXIR I (fwdNIR N (ℓ + 1) (tbA B)) s5 = s6 at n6 nf6 ni6 q6 ⊢
  have F6 : ∀ x, regs ≤ x → (x < gA B ℓ ∨ gA B ℓ + 2 ^ (ℓ + 1) ≤ x) → rd s6.M x = rd t.M x :=
    fun x hx hx2 => by rw [nf6 x hx hx2, F5 x hx hx2]
  rw [semXIR_seq]
  obtain ⟨c7, cf7, ci7⟩ := cosIR_sem I s6 ni6 (E := gEval N ℓ S y)
    (Li := fun j => (lam N S ℓ (2 ^ ℓ + j))⁻¹) hB (by rw [q6, q5, q4]; exact hsz) h64
    (fun i hi => n6 i hi)
    (fun j hj => by rw [rdK_eq (F6 _ (by rw [hI]; simp only [regs]; omega) (outG' _ (by rw [hI]; omega))),
      L4 j hj])
  have q7 := size_sem I (cosIR ℓ B) s6
  generalize semXIR I (cosIR ℓ B) s6 = s7 at c7 cf7 ci7 q7 ⊢
  have F7 : ∀ x, regs ≤ x → (x < gA B ℓ ∨ gA B ℓ + 2 ^ (ℓ + 1) ≤ x) → rd s7.M x = rd t.M x :=
    fun x hx hx2 => by rw [cf7 x hx hx2, F6 x hx hx2]
  rw [semXIR_seq]
  have hM8 := inv_sem I (P := .blk [.const rA0 (toWord (gA B ℓ))]) (by simp +decide [WF, Prim.dst, rA0]) ci7
  have e8 : ∀ x, x ≠ rA0 → rd (semXIR I (.blk [.const rA0 (toWord (gA B ℓ))]) s7).M x = rd s7.M x :=
    fun x hx => rdBlk_nw I _ _ (by simp [Prim.dst, Ne.symm hx])
  have hz7 := ci7.1; simp only [regs] at hz7
  have a8 : rd (semXIR I (.blk [.const rA0 (toWord (gA B ℓ))]) s7).M rA0 = toWord (gA B ℓ) := by
    rw [semBlk]; simp only [runPrims, List.foldl, Prim.run]
    exact rd_set_self (Nat.lt_of_lt_of_le (m := 256) (by decide) (by assumption))
  have q8 := size_sem I (.blk [.const rA0 (toWord (gA B ℓ))]) s7
  generalize semXIR I (.blk [.const rA0 (toWord (gA B ℓ))]) s7 = s8 at hM8 e8 a8 q8 ⊢
  have hW8 : ∀ v < N, ∀ i < N, rdK s8.M (tbA B + N * v + i) = (wRow ptK N v).getD i 0 :=
    fun v hv i hi => by
      have := htab v hv i hi
      rw [rdK_eq (e8 _ (hrA _ hTr)),
        rdK_eq (F7 _ hTr (outG _ (by rw [hTb]; omega))), L1 v hv i hi]
  obtain ⟨n9, nf9, ni9⟩ := bflyNIR_sem (N := N) I s8 hM8 hN64 (A := gA B ℓ) (tb := tbA B) (ℓ := ℓ + 1)
    (Y := fCos N ℓ S y) hN hGr (by rw [hG, hp]; omega)
    (by rw [hG, hp, q8, q7, q6, q5, q4]; omega) (by rw [hTb]; exact hB) (by rw [hTb]; omega)
    (Or.inl (by rw [hTb, hG]; omega)) a8 hW8
    (fun i hi => by
      rw [rdK_eq (e8 _ (hrA _ hGr')), c7 i hi, fCos]
      by_cases h : i < 2 ^ ℓ
      · rw [if_pos h, if_pos h]
      · rw [if_neg h, if_neg h, Nat.add_sub_cancel' (not_lt.1 h)])
  refine ⟨fun x hx => ?_, ni9, fun x hx hx2 => ?_⟩
  · rw [hO, show B + 4096 + 3 * 2 ^ ℓ + x = gA B ℓ + (2 ^ ℓ + x) by rw [hG]; omega, n9 _ (by omega)]
    rfl
  · rw [nf9 x hx (by rw [hp] at hx2; rcases hx2 with h | h <;> [left; right] <;> omega), e8 x (hrA x hx),
      F7 x hx hx2]

theorem laneIR_sem (I : Array Word) (s : St) (hM : Inv s.M) {N ℓ B : ℕ} {S : List ℕ} {y : ℕ → BF64}
    (hN : ℓ + 1 ≤ N) (hN64 : N ≤ 64) (hB : regs ≤ B) (hsz : fdEnd B ℓ ≤ s.M.size)
    (h64 : fdEnd B ℓ < 2 ^ 64) (hm : S.length ≤ 2 ^ ℓ) (hSn : ∀ j ∈ S, j < 2 ^ ℓ)
    (hL : LamOk N ℓ B S s.M) (hy : ∀ j < 2 ^ ℓ, rdK s.M (yA B ℓ + j) = y j) :
    (∀ x < 2 ^ ℓ, rdK (semXIR I (laneIR N ℓ S.length B) s).M (outA B ℓ + x) = fd1 N ℓ S y x) ∧
    Inv (semXIR I (laneIR N ℓ S.length B) s).M ∧ (semXIR I (laneIR N ℓ S.length B) s).o = s.o ∧
    ∀ x, regs ≤ x → (x < gA B ℓ ∨ tA B ℓ ≤ x) →
      rd (semXIR I (laneIR N ℓ S.length B) s).M x = rd s.M x := by
  have ho := sem_oL I _ s (hasOut_laneIRL N ℓ S.length B)
  have hB' : 256 ≤ B := hB
  have hp : 2 ^ (ℓ + 1) = 2 * 2 ^ ℓ := by rw [pow_succ]; ring
  have hNN : N * N ≤ 4096 := Nat.mul_le_mul hN64 hN64
  obtain ⟨g3, hi3, F3, zi3, q3⟩ := laneFrontL I s hM hN hB hsz h64 hm hSn hL hy
  have outG : ∀ x, x < B + 4096 + 2 * 2 ^ ℓ → x < gA B ℓ ∨ gA B ℓ + 2 ^ (ℓ + 1) ≤ x :=
    fun x hx => Or.inl (by show x < B + 4096 + 2 * 2 ^ ℓ; exact hx)
  obtain ⟨L1, L2, L3, L4⟩ := hL
  rw [laneIR, semXIR_seq, semXIR_seq, semXIR_seq]
  rw [laneIR, semXIR_seq, semXIR_seq, semXIR_seq] at ho
  generalize semXIR I (corrIR ℓ B) (semXIR I (synIR ℓ S.length B) (semXIR I (zeroGIR ℓ B) s)) = t
    at g3 hi3 F3 zi3 q3 ho ⊢
  have htab : ∀ v < N, ∀ i < N, N * v + i < 4096 := fun v hv i hi => by
    have : N * v + N ≤ N * N := by rw [← Nat.mul_succ]; exact Nat.mul_le_mul_left N hv
    omega
  obtain ⟨o1, o2, o3⟩ := laneTailL I t zi3 (S := S) (y := y) hN hN64 hB (by rw [q3]; exact hsz) h64
    (fun v hv i hi => by
      have := htab v hv i hi
      rw [rdK_eq (F3 _ (by show 256 ≤ B + N * v + i; omega) (outG _ (by show B + N * v + i < _; omega))),
        L1 v hv i hi])
    (fun j hj => by
      rw [rdK_eq (F3 _ (by show 256 ≤ B + 4096 + 6 * 2 ^ ℓ + j; omega)
        (Or.inr (by show B + 4096 + 2 * 2 ^ ℓ + 2 ^ (ℓ + 1) ≤ B + 4096 + 6 * 2 ^ ℓ + j; omega))), L4 j hj])
    g3 hi3
  refine ⟨o1, o2, ho, fun x hx hx2 => ?_⟩
  rw [o3 x hx (by
    rcases hx2 with h | h
    · exact Or.inl h
    · exact Or.inr (by show B + 4096 + 2 * 2 ^ ℓ + 2 ^ (ℓ + 1) ≤ x; have : B + 4096 + 4 * 2 ^ ℓ ≤ x := h; omega)),
    F3 x hx (by
    rcases hx2 with h | h
    · exact Or.inl h
    · exact Or.inr (by show B + 4096 + 2 * 2 ^ ℓ + 2 ^ (ℓ + 1) ≤ x; have : B + 4096 + 4 * 2 ^ ℓ ≤ x := h; omega))]

end Lvm6.FD
