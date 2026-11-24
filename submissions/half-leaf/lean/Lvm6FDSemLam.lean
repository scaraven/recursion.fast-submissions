-- lvm6 X1 (BLUEPRINT §3 `FD1`): `lamIR` computes the product tree. New; on season 1's `wtabNIR_sem`,
-- `bflyNIR_sem`, `fwdNIR_sem` (`LvmMPXNtt4`).
import Lvm6FDSemBase
import Lvm6FDTree

/-!
# `lamIR` computes `Λ`

* `leavesIR_sem`: cell `tA + i` holds `ptK (i/2) + ptK (i%2)` (leaf `X − ptK j` at `0`, `1`);
* `dummiesIR_sem`: the leaves of `S` become `1`, so the tree holds `leafRow S`;
* `copyBody`/`prodBody` loops, `parentBody_sem`, `tLevelIR_sem`, `treeIR_sem`: level `h` of the
  tree holds `lam N S h`;
* `invsIR_sem`: `Λ⁻¹` on the coset;
* **`lamIR_sem`** (frozen statement): `LamOk` after `lamIR`.
-/

namespace Lvm6.FD

open RecursionFast Lvm.X Lvm.Nb

attribute [local irreducible] entryK storeM

/-! ## Proof helpers -/

theorem wK_toWord (j : ℕ) : wK (toWord j) = ptK j := rfl

theorem wK_one : wK 1 = 1 := rfl

/-- The registers' bound. -/
theorem regs_le_size {M : Mem} (hM : Inv M) : 256 ≤ M.size := hM.1

/-! ## The leaves -/

theorem leavesIR_sem (I : Array Word) (s : St) (hM : Inv s.M) {ℓ B : ℕ} (hB : regs ≤ B)
    (hsz : fdEnd B ℓ ≤ s.M.size) (h64 : fdEnd B ℓ < 2 ^ 64) :
    (∀ i < 2 ^ (ℓ + 1), rdK (semXIR I (leavesIR ℓ B) s).M (tA B ℓ + i) = ptK (i / 2) + ptK (i % 2)) ∧
    (∀ x, regs ≤ x → (x < tA B ℓ ∨ tA B ℓ + 2 ^ (ℓ + 1) ≤ x) →
      rd (semXIR I (leavesIR ℓ B) s).M x = rd s.M x) ∧
    Inv (semXIR I (leavesIR ℓ B) s).M := by
  have hs := hM.1
  simp only [regs] at hs hB
  have hp : 2 ^ (ℓ + 1) = 2 * 2 ^ ℓ := by rw [pow_succ]; ring
  simp only [fdEnd, tA] at hsz h64 ⊢
  rw [leavesIR, semXIR_seq]
  set b0 : List Prim := [.const zI 0, .const zA (toWord (tA B ℓ)), .const zN1 (toWord (2 ^ ℓ))]
  have w0 : WF (.blk b0) := by simp +decide [b0, WF, Prim.dst, zI, zA, zN1]
  have hM0 := inv_sem I w0 hM
  have z0 := size_sem I (.blk b0) s
  have r0 : rd (semXIR I (.blk b0) s).M zI = toWord 0 ∧
      rd (semXIR I (.blk b0) s).M zA = toWord (B + 4096 + 4 * 2 ^ ℓ + 2 * 0) ∧
      rd (semXIR I (.blk b0) s).M zN1 = toWord (2 ^ ℓ) := by
    rw [semBlk]; simp only [b0, runPrims, List.foldl, Prim.run]
    refine ⟨?_, ?_, ?_⟩ <;>
    simp (disch := first | decide | ((try simp only [size_set]); refine Nat.lt_of_lt_of_le (m := 256) (by decide) ?_; first | assumption | omega)) only
      [rd_set_self, rd_set_ne] <;> rfl
  have k0 : ∀ r, regs ≤ r → rd (semXIR I (.blk b0) s).M r = rd s.M r := fun r hr => by
    simp only [regs] at hr
    refine rdBlk_nw I _ s ?_
    simp only [b0, List.mem_cons, List.mem_nil_iff, or_false]
    rintro p (rfl | rfl | rfl) <;> simp only [Prim.dst, zI, zA, zN1] <;> first | decide | exact Nat.ne_of_lt (Nat.lt_of_lt_of_le (by decide) hr)
  generalize semXIR I (.blk b0) s = s0 at hM0 z0 r0 k0
  obtain ⟨i0, a0, n0⟩ := r0
  let R : ℕ → Mem → Prop := fun j M => rd M zI = toWord j ∧
    rd M zA = toWord (B + 4096 + 4 * 2 ^ ℓ + 2 * j) ∧
    (∀ i < 2 * j, rdK M (B + 4096 + 4 * 2 ^ ℓ + i) = ptK (i / 2) + ptK (i % 2)) ∧
    (∀ x, regs ≤ x → (x < B + 4096 + 4 * 2 ^ ℓ ∨ B + 4096 + 4 * 2 ^ ℓ + 2 * j ≤ x) → rd M x = rd s.M x)
  have hR : ∀ j (M M' : Mem), (∀ i, i ≠ zC1 → i ≠ cTmp → rd M' i = rd M i) → R j M → R j M' := by
    rintro j M M' hMM ⟨r1, r2, r3, r4⟩
    have hx : ∀ x, regs ≤ x → x ≠ zC1 ∧ x ≠ cTmp := fun x hx => by
      simp only [regs, zC1, cTmp] at hx ⊢; (clear h64; omega)
    refine ⟨by rw [hMM _ (by decide) (by decide), r1], by rw [hMM _ (by decide) (by decide), r2],
      fun i hi => ?_, fun x hx' hx2 => ?_⟩
    · rw [← r3 i hi]; exact rdK_eq (hMM _ (hx _ (by simp only [regs]; (clear h64; omega))).1
        (hx _ (by simp only [regs]; (clear h64; omega))).2)
    · rw [hMM _ (hx x hx').1 (hx x hx').2, r4 x hx' hx2]
  have h0 : R 0 s0.M := ⟨i0, a0, fun i hi => absurd hi (by (clear h64; omega)), fun x hx _ => k0 x hx⟩
  have hb : ∀ j (s' : St), j < 2 ^ ℓ → Inv s'.M → s'.M.size = s0.M.size → R j s'.M →
      Inv (semXIR I leafBody s').M ∧
        R (j + 1) (semXIR I leafBody s').M := by
    rintro j s' hj i1 i2 ⟨r1, r2, r3, r4⟩
    have hs' := i1.1
    simp only [regs] at hs'
    have hX : B + 4096 + 4 * 2 ^ ℓ + 2 * j + 1 < s'.M.size := by (clear h64; omega)
    have rA : 256 ≤ B + 4096 + 4 * 2 ^ ℓ + 2 * j :=
      Nat.le_add_right_of_le (Nat.le_add_right_of_le (Nat.le_add_right_of_le hB))
    have rA1 : 256 ≤ B + 4096 + 4 * 2 ^ ℓ + 2 * j + 1 := Nat.le_add_right_of_le rA
    have hg : ∀ {u v : ℕ}, u < 256 → 256 ≤ v → v ≠ u := fun hu hv => Nat.ne_of_gt (Nat.lt_of_lt_of_le hu hv)
    have hl : ∀ {u v : ℕ}, u < 256 → 256 ≤ v → u ≠ v := fun hu hv => Nat.ne_of_lt (Nat.lt_of_lt_of_le hu hv)
    rw [leafBody, semXIR_seq]
    obtain ⟨c1, hM1⟩ := store_hp I s' i1 (p := zA) (v := zI) (by decide) (by decide) r2
      rA (by omega) (by (clear h64; omega))
    have z1 := size_sem I (.store zA zI) s'
    generalize semXIR I (.store zA zI) s' = s1 at c1 hM1 z1
    rw [semXIR_seq]
    set b1 : List Prim := [.op .xor zT zI cOne, .op .add zB zA cOne]
    have hM2 := inv_sem I (P := .blk b1) (by simp +decide [b1, WF, Prim.dst, zT, zB]) hM1
    have z2 := size_sem I (.blk b1) s1
    have e2 : ∀ i, i ≠ zT → i ≠ zB → rd (semXIR I (.blk b1) s1).M i = rd s1.M i := fun i h1 h2 =>
      rdBlk_nw I _ _ (by simp [b1, Prim.dst]; exact ⟨Ne.symm h1, Ne.symm h2⟩)
    have hone : rd s1.M cOne = 1 := hM1.2 0 (by decide)
    have t2 : rd (semXIR I (.blk b1) s1).M zT = toWord j ^^^ 1 ∧
        rd (semXIR I (.blk b1) s1).M zB = toWord (B + 4096 + 4 * 2 ^ ℓ + 2 * j + 1) := by
      rw [semBlk]; simp only [b1, runPrims, List.foldl, Prim.run]
      have hz1 := hM1.1; simp only [regs] at hz1
      refine ⟨?_, ?_⟩ <;>
      simp (disch := first | decide | ((try simp only [size_set]); refine Nat.lt_of_lt_of_le (m := 256) (by decide) ?_; first | assumption | omega)) only
        [rd_set_self, rd_set_ne]
      · rw [c1 _ (by decide), if_neg (hl (by decide) rA), r1, hone]; rfl
      · rw [c1 _ (by decide), if_neg (hl (by decide) rA), r2, hone, add_one_toWord]
    generalize semXIR I (.blk b1) s1 = s2 at hM2 z2 e2 t2
    rw [semXIR_seq]
    obtain ⟨c3, hM3⟩ := store_hp I s2 hM2 (p := zB) (v := zT) (by decide) (by decide) t2.2
      rA1 (by omega) (by (clear h64; omega))
    have z3 := size_sem I (.store zB zT) s2
    generalize semXIR I (.store zB zT) s2 = s3 at c3 hM3 z3
    set b3 : List Prim := [.op .add zI zI cOne, .op .add zA zA cOne, .op .add zA zA cOne]
    have hM4 := inv_sem I (P := .blk b3) (by simp +decide [b3, WF, Prim.dst, zI, zA]) hM3
    have e4 : ∀ i, i ≠ zI → i ≠ zA → rd (semXIR I (.blk b3) s3).M i = rd s3.M i := fun i h1 h2 =>
      rdBlk_nw I _ _ (by simp [b3, Prim.dst]; exact ⟨Ne.symm h1, Ne.symm h2⟩)
    have hone3 : rd s3.M cOne = 1 := hM3.2 0 (by decide)
    have hz3 := hM3.1; simp only [regs] at hz3
    -- the old value of a heap cell, through the two stores
    have old : ∀ x, regs ≤ x → x ≠ B + 4096 + 4 * 2 ^ ℓ + 2 * j →
        x ≠ B + 4096 + 4 * 2 ^ ℓ + 2 * j + 1 → rd s3.M x = rd s'.M x := fun x hx h1 h2 => by
      have hx' : x ≠ cTmp := hg (by decide) hx
      rw [c3 x hx', if_neg h2, e2 x (hg (by decide) hx)
        (hg (by decide) hx), c1 x hx', if_neg h1]
    refine ⟨hM4, ?_, ?_, fun i hi => ?_, fun x hx hx2 => ?_⟩
    · rw [semBlk]; simp only [b3, runPrims, List.foldl, Prim.run]
      simp (disch := first | decide | ((try simp only [size_set]); refine Nat.lt_of_lt_of_le (m := 256) (by decide) ?_; first | assumption | omega)) only
        [rd_set_self, rd_set_ne]
      rw [c3 _ (by decide), if_neg (hl (by decide) rA1), e2 _ (by decide) (by decide),
        c1 _ (by decide), if_neg (hl (by decide) rA), r1, hone3, add_one_toWord]
    · rw [semBlk]; simp only [b3, runPrims, List.foldl, Prim.run]
      simp (disch := first | decide | ((try simp only [size_set]); refine Nat.lt_of_lt_of_le (m := 256) (by decide) ?_; first | assumption | omega)) only
        [rd_set_self, rd_set_ne]
      rw [c3 _ (by decide), if_neg (hl (by decide) rA1), e2 _ (by decide) (by decide),
        c1 _ (by decide), if_neg (hl (by decide) rA), r2, hone3, add_one_toWord,
        add_one_toWord]
      exact congrArg toWord (by ring)
    · have hxr : regs ≤ B + 4096 + 4 * 2 ^ ℓ + i := Nat.le_add_right_of_le (Nat.le_add_right_of_le (Nat.le_add_right_of_le hB))
      have hxT : B + 4096 + 4 * 2 ^ ℓ + i ≠ cTmp := hg (by decide) hxr
      rw [rdK_eq (e4 _ (hg (by decide) hxr) (hg (by decide) hxr))]
      by_cases h1 : i = 2 * j + 1
      · subst h1
        rw [rdK, c3 _ hxT, if_pos (by ring), t2.1, wK_xor, wK_toWord, wK_one]
        rw [show (2 * j + 1) / 2 = j by (clear h64; omega), show (2 * j + 1) % 2 = 1 by (clear h64; omega)]; rfl
      by_cases h2 : i = 2 * j
      · subst h2
        rw [rdK, c3 _ hxT, if_neg (by (clear h64; omega)), e2 _ (hg (by decide) hxr) (hg (by decide) hxr),
          c1 _ hxT, if_pos rfl, r1, wK_toWord]
        rw [show 2 * j / 2 = j by (clear h64; omega), show 2 * j % 2 = 0 by (clear h64; omega), ptK_zero, add_zero]
      · rw [rdK_eq (old _ hxr (by omega) (by (clear h64; omega)))]
        exact r3 i (by (clear h64; omega))
    · rw [e4 x (hg (by decide) hx) (hg (by decide) hx),
        old x hx (by omega) (by (clear h64; omega)), r4 x hx (by (clear h64; omega))]
  have hfin := loopK_gen I leafBody s0 hM0 (by decide) (by decide) (by decide) n0
    (by omega) R hR h0
    (fun j s' hj i1 i2 i3 => hb j s' hj i1 i2 i3)
  obtain ⟨⟨_, _, f3, f4⟩, f5, _⟩ := hfin
  refine ⟨fun i hi => f3 i (by (clear h64; omega)), fun x hx hx2 => f4 x hx (by (clear h64; omega)), f5⟩

/-! ## The dummy leaves -/

theorem mem_take_succ_iff {S : List ℕ} {j q : ℕ} (hj : j < S.length) :
    q ∈ S.take (j + 1) ↔ q ∈ S.take j ∨ q = S.getD j 0 := by
  rw [List.take_succ, List.mem_append, List.getElem?_eq_getElem hj, Option.toList_some,
    List.mem_singleton, List.getD_eq_getElem _ _ hj]

theorem dummiesIR_sem (I : Array Word) (s : St) (hM : Inv s.M) {ℓ B : ℕ} {S : List ℕ}
    {Y : ℕ → BF64} (hB : regs ≤ B) (hsz : fdEnd B ℓ ≤ s.M.size) (h64 : fdEnd B ℓ < 2 ^ 64)
    (hm : S.length ≤ 2 ^ ℓ) (hSn : ∀ j ∈ S, j < 2 ^ ℓ)
    (hS : ∀ i < S.length, rd s.M (sA B + i) = toWord (S.getD i 0))
    (hY : ∀ i < 2 ^ (ℓ + 1), rdK s.M (tA B ℓ + i) = Y i) :
    (∀ i < 2 ^ (ℓ + 1), rdK (semXIR I (dummiesIR ℓ S.length B) s).M (tA B ℓ + i) =
      if i / 2 ∈ S then 1 else Y i) ∧
    (∀ x, regs ≤ x → (x < tA B ℓ ∨ tA B ℓ + 2 ^ (ℓ + 1) ≤ x) →
      rd (semXIR I (dummiesIR ℓ S.length B) s).M x = rd s.M x) ∧
    Inv (semXIR I (dummiesIR ℓ S.length B) s).M := by
  have hs := hM.1
  simp only [regs] at hs hB
  have hp : 2 ^ (ℓ + 1) = 2 * 2 ^ ℓ := by rw [pow_succ]; ring
  simp only [fdEnd, tA, sA] at hsz h64 hS hY ⊢
  rw [dummiesIR, semXIR_seq]
  set b0 : List Prim := [.const zC (toWord (sA B)), .const zN1 (toWord S.length)]
  have w0 : WF (.blk b0) := by simp +decide [b0, WF, Prim.dst, zC, zN1]
  have hM0 := inv_sem I w0 hM
  have z0 := size_sem I (.blk b0) s
  have r0 : rd (semXIR I (.blk b0) s).M zC = toWord (B + 4096 + 0) ∧
      rd (semXIR I (.blk b0) s).M zN1 = toWord S.length := by
    rw [semBlk]; simp only [b0, runPrims, List.foldl, Prim.run]
    refine ⟨?_, ?_⟩ <;>
    simp (disch := first | decide | ((try simp only [size_set]); refine Nat.lt_of_lt_of_le (m := 256) (by decide) ?_; first | assumption | omega)) only
      [rd_set_self, rd_set_ne] <;> rfl
  have k0 : ∀ r, regs ≤ r → rd (semXIR I (.blk b0) s).M r = rd s.M r := fun r hr => by
    simp only [regs] at hr
    refine rdBlk_nw I _ s ?_
    simp only [b0, List.mem_cons, List.mem_nil_iff, or_false]
    rintro p (rfl | rfl) <;> simp only [Prim.dst, zC, zN1] <;> first | decide | exact Nat.ne_of_lt (Nat.lt_of_lt_of_le (by decide) hr)
  generalize semXIR I (.blk b0) s = s0 at hM0 z0 r0 k0
  obtain ⟨c0, n0⟩ := r0
  have hT0 : ∀ x, x < 2 ^ (ℓ + 1) → regs ≤ B + 4096 + 4 * 2 ^ ℓ + x := fun x _ => by
    simp only [regs]; (clear h64; omega)
  let R : ℕ → Mem → Prop := fun j M => rd M zC = toWord (B + 4096 + j) ∧
    (∀ i < 2 ^ (ℓ + 1), rdK M (B + 4096 + 4 * 2 ^ ℓ + i) = if i / 2 ∈ S.take j then 1 else Y i) ∧
    (∀ x, regs ≤ x → (x < B + 4096 + 4 * 2 ^ ℓ ∨ B + 4096 + 4 * 2 ^ ℓ + 2 ^ (ℓ + 1) ≤ x) →
      rd M x = rd s.M x)
  have hR : ∀ j (M M' : Mem), (∀ i, i ≠ zC1 → i ≠ cTmp → rd M' i = rd M i) → R j M → R j M' := by
    rintro j M M' hMM ⟨r1, r3, r4⟩
    have hx : ∀ x, regs ≤ x → x ≠ zC1 ∧ x ≠ cTmp := fun x hx => by
      simp only [regs, zC1, cTmp] at hx ⊢; (clear h64; omega)
    refine ⟨by rw [hMM _ (by decide) (by decide), r1], fun i hi => ?_, fun x hx' hx2 => ?_⟩
    · rw [← r3 i hi]; exact rdK_eq (hMM _ (hx _ (hT0 i hi)).1 (hx _ (hT0 i hi)).2)
    · rw [hMM _ (hx x hx').1 (hx x hx').2, r4 x hx' hx2]
  have h0 : R 0 s0.M := ⟨c0, fun i hi => by
      rw [List.take_zero, if_neg List.not_mem_nil, ← hY i hi]; exact rdK_eq (k0 _ (hT0 i hi)),
    fun x hx _ => k0 x hx⟩
  have hb : ∀ j (s' : St), j < S.length → Inv s'.M → s'.M.size = s0.M.size → R j s'.M →
      Inv (semXIR I (dummyBody ℓ B) s').M ∧ R (j + 1) (semXIR I (dummyBody ℓ B) s').M := by
    rintro j s' hj i1 i2 ⟨r1, r3, r4⟩
    have hs' := i1.1
    simp only [regs] at hs'
    set q := S.getD j 0 with hq
    have hqS : q ∈ S := by rw [hq, List.getD_eq_getElem _ _ hj]; exact List.getElem_mem hj
    have hqn : q < 2 ^ ℓ := hSn q hqS
    have hg : ∀ {u v : ℕ}, u < 256 → 256 ≤ v → v ≠ u := fun hu hv => Nat.ne_of_gt (Nat.lt_of_lt_of_le hu hv)
    have hl : ∀ {u v : ℕ}, u < 256 → 256 ≤ v → u ≠ v := fun hu hv => Nat.ne_of_lt (Nat.lt_of_lt_of_le hu hv)
    have rQ : 256 ≤ B + 4096 + 4 * 2 ^ ℓ + 2 * q :=
      Nat.le_add_right_of_le (Nat.le_add_right_of_le (Nat.le_add_right_of_le hB))
    have rQ1 : 256 ≤ B + 4096 + 4 * 2 ^ ℓ + 2 * q + 1 := Nat.le_add_right_of_le rQ
    rw [dummyBody, semXIR_seq]
    have hSj : rd s'.M (B + 4096 + j) = toWord q := by
      rw [r4 _ (Nat.le_add_right_of_le (Nat.le_add_right_of_le hB)) (by (clear h64; omega)), hS j hj]
    obtain ⟨l1, hM1⟩ := load_hp I s' i1 (d := zI) (p := zC) (by decide) (by decide) r1 (by omega)
    have z1 := size_sem I (.load zI zC) s'
    generalize semXIR I (.load zI zC) s' = s1 at l1 hM1 z1
    rw [semXIR_seq]
    set b1 : List Prim := [.op .add zA zI zI, .const zD (toWord (tA B ℓ)), .op .add zA zA zD,
      .op .add zB zA cOne]
    have hM2 := inv_sem I (P := .blk b1) (by simp +decide [b1, WF, Prim.dst, zA, zD, zB]) hM1
    have z2 := size_sem I (.blk b1) s1
    have e2 : ∀ i, i ≠ zA → i ≠ zD → i ≠ zB → rd (semXIR I (.blk b1) s1).M i = rd s1.M i :=
      fun i h1 h2 h3 => rdBlk_nw I _ _ (by
        intro p hp; simp only [b1, List.mem_cons, List.mem_nil_iff, or_false] at hp
        rcases hp with rfl | rfl | rfl | rfl <;> simp only [Prim.dst] <;>
          first | exact Ne.symm h1 | exact Ne.symm h2 | exact Ne.symm h3)
    have hone : rd s1.M cOne = 1 := hM1.2 0 (by decide)
    have t2 : rd (semXIR I (.blk b1) s1).M zA = toWord (B + 4096 + 4 * 2 ^ ℓ + 2 * q) ∧
        rd (semXIR I (.blk b1) s1).M zB = toWord (B + 4096 + 4 * 2 ^ ℓ + 2 * q + 1) := by
      rw [semBlk]; simp only [b1, runPrims, List.foldl, Prim.run]
      have hz1 := hM1.1; simp only [regs] at hz1
      refine ⟨?_, ?_⟩ <;>
      simp (disch := first | decide | ((try simp only [size_set]); refine Nat.lt_of_lt_of_le (m := 256) (by decide) ?_; first | assumption | omega)) only
        [rd_set_self, rd_set_ne]
      · rw [l1, if_pos rfl, hSj, add_toWord, add_toWord, tA]; exact congrArg toWord (by ring)
      · rw [l1, if_pos rfl, hSj, add_toWord, add_toWord, tA, hone, add_one_toWord]; exact congrArg toWord (by ring)
    generalize semXIR I (.blk b1) s1 = s2 at hM2 z2 e2 t2
    have hone2 : rd s2.M cOne = 1 := hM2.2 0 (by decide)
    rw [semXIR_seq]
    obtain ⟨c3, hM3⟩ := store_hp I s2 hM2 (p := zA) (v := cOne) (by decide) (by decide) t2.1
      rQ (by omega) (by (clear h64; omega))
    have z3 := size_sem I (.store zA cOne) s2
    generalize semXIR I (.store zA cOne) s2 = s3 at c3 hM3 z3
    rw [semXIR_seq]
    have t3 : rd s3.M zB = toWord (B + 4096 + 4 * 2 ^ ℓ + 2 * q + 1) := by
      rw [c3 _ (by decide), if_neg (hl (by decide) rQ), t2.2]
    obtain ⟨c4, hM4⟩ := store_hp I s3 hM3 (p := zB) (v := cOne) (by decide) (by decide) t3
      rQ1 (by omega) (by (clear h64; omega))
    have z4 := size_sem I (.store zB cOne) s3
    generalize semXIR I (.store zB cOne) s3 = s4 at c4 hM4 z4
    have hM5 := inv_sem I (P := .blk [.op .add zC zC cOne]) (by simp +decide [WF, Prim.dst, zC]) hM4
    have e5 : ∀ i, i ≠ zC → rd (semXIR I (.blk [.op .add zC zC cOne]) s4).M i = rd s4.M i :=
      fun i h1 => rdBlk_nw I _ _ (by simp [Prim.dst]; exact Ne.symm h1)
    have hone4 : rd s4.M cOne = 1 := hM4.2 0 (by decide)
    have hz4 := hM4.1; simp only [regs] at hz4
    have old : ∀ x, regs ≤ x → x ≠ B + 4096 + 4 * 2 ^ ℓ + 2 * q →
        x ≠ B + 4096 + 4 * 2 ^ ℓ + 2 * q + 1 → rd s4.M x = rd s'.M x := fun x hx h1 h2 => by
      have hx' : x ≠ cTmp := hg (by decide) hx
      rw [c4 x hx', if_neg h2, c3 x hx', if_neg h1, e2 x (hg (by decide) hx)
        (hg (by decide) hx) (hg (by decide) hx), l1,
        if_neg (hg (by decide) hx)]
    refine ⟨hM5, ?_, fun i hi => ?_, fun x hx hx2 => ?_⟩
    · rw [semBlk]; simp only [runPrims, List.foldl, Prim.run]
      simp (disch := first | decide | ((try simp only [size_set]); refine Nat.lt_of_lt_of_le (m := 256) (by decide) ?_; first | assumption | omega)) only
        [rd_set_self, rd_set_ne]
      rw [c4 _ (by decide), if_neg (hl (by decide) rQ1), c3 _ (by decide),
        if_neg (hl (by decide) rQ), e2 _ (by decide) (by decide) (by decide), l1,
        if_neg (by decide), r1, hone4, add_one_toWord]
      exact congrArg toWord (by ring)
    · have hxT : B + 4096 + 4 * 2 ^ ℓ + i ≠ cTmp := hg (by decide) (hT0 i hi)
      rw [rdK_eq (e5 _ (hg (by decide) (hT0 i hi)))]
      simp only [mem_take_succ_iff hj]
      by_cases hiq : i / 2 = q
      · rw [if_pos (Or.inr hiq)]
        by_cases h1 : i = 2 * q + 1
        · rw [rdK, c4 _ hxT, if_pos (by (clear h64; omega)), c3 _ (by decide), if_neg (by simp only [cOne]; (clear h64; omega)), hone2]; rfl
        · rw [rdK, c4 _ hxT, if_neg (by (clear h64; omega)), c3 _ hxT, if_pos (by (clear h64; omega)), hone2]; rfl
      · rw [rdK_eq (old _ (hT0 i hi) (by omega) (by (clear h64; omega))), r3 i hi]
        simp only [← hq, hiq, or_false]
    · rw [e5 x (hg (by decide) hx), old x hx (by omega) (by (clear h64; omega)), r4 x hx hx2]
  have hfin := loopK_gen I (dummyBody ℓ B) s0 hM0 (by decide) (by decide) (by decide) n0
    (by omega) R hR h0 (fun j s' hj i1 i2 i3 => hb j s' hj i1 i2 i3)
  obtain ⟨⟨_, f3, f4⟩, f5, _⟩ := hfin
  refine ⟨fun i hi => ?_, fun x hx hx2 => f4 x hx hx2, f5⟩
  rw [f3 i hi, List.take_length]

/-! ## Copying and padding two children -/

-- The arithmetic of `copyLoop_sem` (proof helper; a small context keeps `omega` cheap).
private theorem copyLoop_arith {a b x w c S : ℕ} (hx64 : x + 2 * c < 2 ^ 64) (hw64 : w + 2 * c < 2 ^ 64)
    (ha64 : a + c < 2 ^ 64) (hb64 : b + c < 2 ^ 64) (hsz : x + 2 * c ≤ S ∧ w + 2 * c ≤ S)
    (hxw : x + 2 * c ≤ w) (hab : a + c ≤ x ∨ w + 2 * c ≤ a) (hbb : b + c ≤ x ∨ w + 2 * c ≤ b) :
    (∀ j < c, a + j < 2 ^ 64) ∧
    (∀ j < c, b + j < 2 ^ 64) ∧
    (∀ j < c, x + j < 2 ^ 64) ∧
    (∀ j < c, w + j < 2 ^ 64) ∧
    (∀ j < c, x + c + j < 2 ^ 64) ∧
    (∀ j < c, w + c + j < 2 ^ 64) ∧
    (∀ j < c, x + j < S) ∧
    (∀ j < c, w + j < S) ∧
    (∀ j < c, x + c + j < S) ∧
    (∀ j < c, w + c + j < S) ∧
    (∀ j < c, b + j ≠ x + j) ∧
    (∀ j < c, a + j < x ∨ w + 2 * c ≤ a + j) ∧
    (∀ j < c, b + j < x ∨ w + 2 * c ≤ b + j) ∧
    (∀ j < c, ∀ i < j + 1, x + i ≠ w + c + j) ∧
    (∀ j < c, ∀ i < j + 1, x + i ≠ x + c + j) ∧
    (∀ j < c, ∀ i < j + 1, x + i ≠ w + j) ∧
    (∀ j < c, ∀ i < j + 1, x + c + i ≠ w + c + j) ∧
    (∀ j < c, ∀ i < j + 1, x + c + i ≠ w + j) ∧
    (∀ j < c, ∀ i < j + 1, x + c + i ≠ x + j) ∧
    (∀ j < c, ∀ i < j + 1, w + i ≠ w + c + j) ∧
    (∀ j < c, ∀ i < j + 1, w + i ≠ x + c + j) ∧
    (∀ j < c, ∀ i < j + 1, w + i ≠ x + j) ∧
    (∀ j < c, ∀ i < j + 1, w + c + i ≠ x + c + j) ∧
    (∀ j < c, ∀ i < j + 1, w + c + i ≠ w + j) ∧
    (∀ j < c, ∀ i < j + 1, w + c + i ≠ x + j) ∧
    (∀ j < c, ∀ y, (y < x ∨ w + 2 * c ≤ y) → y ≠ w + c + j) ∧
    (∀ j < c, ∀ y, (y < x ∨ w + 2 * c ≤ y) → y ≠ x + c + j) ∧
    (∀ j < c, ∀ y, (y < x ∨ w + 2 * c ≤ y) → y ≠ w + j) ∧
    (∀ j < c, ∀ y, (y < x ∨ w + 2 * c ≤ y) → y ≠ x + j) :=
  ⟨fun j hj => Nat.lt_of_le_of_lt (by clear hx64 hw64 ha64 hb64; omega : a + j ≤ a + c) ha64,
   fun j hj => Nat.lt_of_le_of_lt (by clear hx64 hw64 ha64 hb64; omega : b + j ≤ b + c) hb64,
   fun j hj => Nat.lt_of_le_of_lt (by clear hx64 hw64 ha64 hb64; omega : x + j ≤ x + 2 * c) hx64,
   fun j hj => Nat.lt_of_le_of_lt (by clear hx64 hw64 ha64 hb64; omega : w + j ≤ w + 2 * c) hw64,
   fun j hj => Nat.lt_of_le_of_lt (by clear hx64 hw64 ha64 hb64; omega : x + c + j ≤ x + 2 * c) hx64,
   fun j hj => Nat.lt_of_le_of_lt (by clear hx64 hw64 ha64 hb64; omega : w + c + j ≤ w + 2 * c) hw64,
   fun j hj => by clear hx64 hw64 ha64 hb64; omega,
   fun j hj => by clear hx64 hw64 ha64 hb64; omega,
   fun j hj => by clear hx64 hw64 ha64 hb64; omega,
   fun j hj => by clear hx64 hw64 ha64 hb64; omega,
   fun j hj => by clear hx64 hw64 ha64 hb64; omega,
   fun j hj => by clear hx64 hw64 ha64 hb64; omega,
   fun j hj => by clear hx64 hw64 ha64 hb64; omega,
   fun j hj i hi => by clear hx64 hw64 ha64 hb64; omega,
   fun j hj i hi => by clear hx64 hw64 ha64 hb64; omega,
   fun j hj i hi => by clear hx64 hw64 ha64 hb64; omega,
   fun j hj i hi => by clear hx64 hw64 ha64 hb64; omega,
   fun j hj i hi => by clear hx64 hw64 ha64 hb64; omega,
   fun j hj i hi => by clear hx64 hw64 ha64 hb64; omega,
   fun j hj i hi => by clear hx64 hw64 ha64 hb64; omega,
   fun j hj i hi => by clear hx64 hw64 ha64 hb64; omega,
   fun j hj i hi => by clear hx64 hw64 ha64 hb64; omega,
   fun j hj i hi => by clear hx64 hw64 ha64 hb64; omega,
   fun j hj i hi => by clear hx64 hw64 ha64 hb64; omega,
   fun j hj i hi => by clear hx64 hw64 ha64 hb64; omega,
   fun j hj y hy => by clear hx64 hw64 ha64 hb64; omega,
   fun j hj y hy => by clear hx64 hw64 ha64 hb64; omega,
   fun j hj y hy => by clear hx64 hw64 ha64 hb64; omega,
   fun j hj y hy => by clear hx64 hw64 ha64 hb64; omega⟩

theorem copyLoop_sem (I : Array Word) (s : St) (hM : Inv s.M) {a b x w c : ℕ}
    (hc : c < 2 ^ 64) (ha : regs ≤ a) (hb : regs ≤ b) (hx : regs ≤ x) (hw : regs ≤ w)
    (h64 : x + 2 * c < 2 ^ 64 ∧ w + 2 * c < 2 ^ 64 ∧ a + c < 2 ^ 64 ∧ b + c < 2 ^ 64)
    (hsz : x + 2 * c ≤ s.M.size ∧ w + 2 * c ≤ s.M.size)
    (hxw : x + 2 * c ≤ w) (hab : a + c ≤ x ∨ w + 2 * c ≤ a) (hbb : b + c ≤ x ∨ w + 2 * c ≤ b)
    (hA : rd s.M zA = toWord a) (hB : rd s.M zB = toWord b) (hC : rd s.M zC = toWord x)
    (hE : rd s.M zE = toWord w) (hN : rd s.M zN2 = toWord c) :
    (∀ i < c, rd (semXIR I (.loopK zC2 zN2 (toWord c) (copyBody c)) s).M (x + i) = rd s.M (a + i)) ∧
    (∀ i < c, rd (semXIR I (.loopK zC2 zN2 (toWord c) (copyBody c)) s).M (x + c + i) = 0) ∧
    (∀ i < c, rd (semXIR I (.loopK zC2 zN2 (toWord c) (copyBody c)) s).M (w + i) = rd s.M (b + i)) ∧
    (∀ i < c, rd (semXIR I (.loopK zC2 zN2 (toWord c) (copyBody c)) s).M (w + c + i) = 0) ∧
    (∀ y, regs ≤ y → (y < x ∨ w + 2 * c ≤ y) →
      rd (semXIR I (.loopK zC2 zN2 (toWord c) (copyBody c)) s).M y = rd s.M y) ∧
    rd (semXIR I (.loopK zC2 zN2 (toWord c) (copyBody c)) s).M zP = rd s.M zP ∧
    Inv (semXIR I (.loopK zC2 zN2 (toWord c) (copyBody c)) s).M := by
  have hs := hM.1
  simp only [regs] at hs ha hb hx hw
  obtain ⟨hx64, hw64, ha64, hb64⟩ := h64
  have hne : ∀ {u v : ℕ}, u < 256 → 256 ≤ v → v ≠ u := fun h1 h2 => by omega
  obtain ⟨pa, pb, px, pw, pxc, pwc, sx, sw, sxc, swc, fbx, fra, frb, hX1, hX2, hX3, hXC1, hXC3, hXC4, hW1, hW2, hW4, hWC2, hWC3, hWC4, hY1, hY2, hY3, hY4⟩ :=
    copyLoop_arith hx64 hw64 ha64 hb64 hsz hxw hab hbb
  let R : ℕ → Mem → Prop := fun j M => rd M zA = toWord (a + j) ∧ rd M zB = toWord (b + j) ∧
    rd M zC = toWord (x + j) ∧ rd M zE = toWord (w + j) ∧
    (∀ i < j, rd M (x + i) = rd s.M (a + i)) ∧ (∀ i < j, rd M (x + c + i) = 0) ∧
    (∀ i < j, rd M (w + i) = rd s.M (b + i)) ∧ (∀ i < j, rd M (w + c + i) = 0) ∧
    (∀ y, regs ≤ y → (y < x ∨ w + 2 * c ≤ y) → rd M y = rd s.M y) ∧ rd M zP = rd s.M zP
  have hR : ∀ j (M M' : Mem), (∀ i, i ≠ zC2 → i ≠ cTmp → rd M' i = rd M i) → R j M → R j M' := by
    rintro j M M' hMM ⟨r1, r2, r3, r4, r5, r6, r7, r8, r9, r10⟩
    have hy : ∀ y, 256 ≤ y → y ≠ zC2 ∧ y ≠ cTmp := fun y hy => by simp only [zC2, cTmp]; omega
    refine ⟨by rw [hMM _ (by decide) (by decide), r1], by rw [hMM _ (by decide) (by decide), r2],
      by rw [hMM _ (by decide) (by decide), r3], by rw [hMM _ (by decide) (by decide), r4],
      fun i hi => ?_, fun i hi => ?_, fun i hi => ?_, fun i hi => ?_, fun y hy' hy2 => ?_,
      by rw [hMM _ (by decide) (by decide), r10]⟩
    · have hv : 256 ≤ x + i := Nat.le_add_right_of_le hx
      rw [hMM _ (hy _ hv).1 (hy _ hv).2, r5 i hi]
    · have hv : 256 ≤ x + c + i := Nat.le_add_right_of_le (Nat.le_add_right_of_le hx)
      rw [hMM _ (hy _ hv).1 (hy _ hv).2, r6 i hi]
    · have hv : 256 ≤ w + i := Nat.le_add_right_of_le hw
      rw [hMM _ (hy _ hv).1 (hy _ hv).2, r7 i hi]
    · have hv : 256 ≤ w + c + i := Nat.le_add_right_of_le (Nat.le_add_right_of_le hw)
      rw [hMM _ (hy _ hv).1 (hy _ hv).2, r8 i hi]
    · simp only [regs] at hy'
      rw [hMM _ (hy _ hy').1 (hy _ hy').2, r9 y hy' hy2]
  have h0 : R 0 s.M := ⟨by rw [hA, Nat.add_zero], by rw [hB, Nat.add_zero], by rw [hC, Nat.add_zero],
    by rw [hE, Nat.add_zero], fun i hi => absurd hi (Nat.not_lt_zero i), fun i hi => absurd hi (Nat.not_lt_zero i),
    fun i hi => absurd hi (Nat.not_lt_zero i), fun i hi => absurd hi (Nat.not_lt_zero i), fun _ _ _ => rfl, rfl⟩
  have hb' : ∀ j (s' : St), j < c → Inv s'.M → s'.M.size = s.M.size → R j s'.M →
      Inv (semXIR I (copyBody c) s').M ∧ R (j + 1) (semXIR I (copyBody c) s').M := by
    rintro j s' hj i1 i2 ⟨r1, r2, r3, r4, r5, r6, r7, r8, r9, r10⟩
    have hs' := i1.1
    simp only [regs] at hs'
    have rxj : 256 ≤ x + j := Nat.le_add_right_of_le hx
    have rwj : 256 ≤ w + j := Nat.le_add_right_of_le hw
    have rxcj : 256 ≤ x + c + j := Nat.le_add_right_of_le (Nat.le_add_right_of_le hx)
    have rwcj : 256 ≤ w + c + j := Nat.le_add_right_of_le (Nat.le_add_right_of_le hw)
    have hxj : ∀ {u : ℕ}, u < 256 → u ≠ x + j := fun hu => Ne.symm (hne hu rxj)
    have hwj : ∀ {u : ℕ}, u < 256 → u ≠ w + j := fun hu => Ne.symm (hne hu rwj)
    have hxcj : ∀ {u : ℕ}, u < 256 → u ≠ x + c + j := fun hu => Ne.symm (hne hu rxcj)
    have hwcj : ∀ {u : ℕ}, u < 256 → u ≠ w + c + j := fun hu => Ne.symm (hne hu rwcj)
    rw [copyBody, semXIR_seq]
    obtain ⟨l1, hM1⟩ := load_hp I s' i1 (d := zU) (p := zA) (by decide) (by decide) r1 (pa j hj)
    have z1 := size_sem I (.load zU zA) s'
    generalize semXIR I (.load zU zA) s' = s1 at l1 hM1 z1
    have T1 := z1.trans i2
    rw [semXIR_seq]
    have q1 : ∀ i, i ≠ zU → rd s1.M i = rd s'.M i := fun i h => by rw [l1, if_neg h]
    obtain ⟨c2, hM2⟩ := store_hp I s1 hM1 (p := zC) (v := zU) (by decide) (by decide)
      (by rw [q1 _ (by decide), r3]) rxj (px j hj) ((sx j hj).trans_eq T1.symm)
    have z2 := size_sem I (.store zC zU) s1
    generalize semXIR I (.store zC zU) s1 = s2 at c2 hM2 z2
    have T2 := z2.trans T1
    rw [semXIR_seq]
    have q2 : ∀ i, i ≠ cTmp → i ≠ x + j → rd s2.M i = rd s1.M i := fun i h1 h2 => by
      rw [c2 i h1, if_neg h2]
    obtain ⟨l3, hM3⟩ := load_hp I s2 hM2 (d := zU) (p := zB) (by decide) (by decide)
      (by rw [q2 _ (by decide) (hxj (by decide)), q1 _ (by decide), r2]) (pb j hj)
    have z3 := size_sem I (.load zU zB) s2
    generalize semXIR I (.load zU zB) s2 = s3 at l3 hM3 z3
    have T3 := z3.trans T2
    rw [semXIR_seq]
    have q3 : ∀ i, i ≠ zU → rd s3.M i = rd s2.M i := fun i h => by rw [l3, if_neg h]
    obtain ⟨c4, hM4⟩ := store_hp I s3 hM3 (p := zE) (v := zU) (by decide) (by decide)
      (by rw [q3 _ (by decide), q2 _ (by decide) (hxj (by decide)), q1 _ (by decide), r4])
      rwj (pw j hj) ((sw j hj).trans_eq T3.symm)
    have z4 := size_sem I (.store zE zU) s3
    generalize semXIR I (.store zE zU) s3 = s4 at c4 hM4 z4
    have T4 := z4.trans T3
    rw [semXIR_seq]
    have q4 : ∀ i, i ≠ cTmp → i ≠ w + j → rd s4.M i = rd s3.M i := fun i h1 h2 => by
      rw [c4 i h1, if_neg h2]
    set b5 : List Prim := [.const zV 0, .const zD (toWord c), .op .add zT zC zD]
    have hM5 := inv_sem I (P := .blk b5) (by simp +decide [b5, WF, Prim.dst, zV, zD, zT]) hM4
    have e5 : ∀ i, i ≠ zV → i ≠ zD → i ≠ zT → rd (semXIR I (.blk b5) s4).M i = rd s4.M i :=
      fun i h1 h2 h3 => rdBlk_nw I _ _ (by
        intro p hp; simp only [b5, List.mem_cons, List.mem_nil_iff, or_false] at hp
        rcases hp with rfl | rfl | rfl <;> simp only [Prim.dst] <;>
          first | exact Ne.symm h1 | exact Ne.symm h2 | exact Ne.symm h3)
    have hz4 := hM4.1; simp only [regs] at hz4
    have t5 : rd (semXIR I (.blk b5) s4).M zV = 0 ∧ rd (semXIR I (.blk b5) s4).M zD = toWord c ∧
        rd (semXIR I (.blk b5) s4).M zT = toWord (x + c + j) := by
      rw [semBlk]; simp only [b5, runPrims, List.foldl, Prim.run]
      refine ⟨?_, ?_, ?_⟩ <;>
      simp (disch := first | decide | ((try simp only [size_set]); refine Nat.lt_of_lt_of_le (m := 256) (by decide) ?_; first | assumption | omega)) only
        [rd_set_self, rd_set_ne]
      rw [q4 _ (by decide) (hwj (by decide)), q3 _ (by decide),
        q2 _ (by decide) (hxj (by decide)), q1 _ (by decide), r3, add_toWord]
      exact congrArg toWord (by ring)
    have z5 := size_sem I (.blk b5) s4
    generalize semXIR I (.blk b5) s4 = s5 at hM5 e5 t5 z5
    have T5 := z5.trans T4
    rw [semXIR_seq]
    obtain ⟨c6, hM6⟩ := store_hp I s5 hM5 (p := zT) (v := zV) (by decide) (by decide) t5.2.2
      rxcj (pxc j hj) ((sxc j hj).trans_eq T5.symm)
    have z6 := size_sem I (.store zT zV) s5
    generalize semXIR I (.store zT zV) s5 = s6 at c6 hM6 z6
    have T6 := z6.trans T5
    rw [semXIR_seq]
    have q6 : ∀ i, i ≠ cTmp → i ≠ x + c + j → rd s6.M i = rd s5.M i := fun i h1 h2 => by
      rw [c6 i h1, if_neg h2]
    set b7 : List Prim := [.op .add zT zE zD]
    have hM7 := inv_sem I (P := .blk b7) (by simp +decide [b7, WF, Prim.dst, zT]) hM6
    have e7 : ∀ i, i ≠ zT → rd (semXIR I (.blk b7) s6).M i = rd s6.M i :=
      fun i h1 => rdBlk_nw I _ _ (by simp [b7, Prim.dst]; exact Ne.symm h1)
    have hz6 := hM6.1; simp only [regs] at hz6
    have t7 : rd (semXIR I (.blk b7) s6).M zT = toWord (w + c + j) := by
      rw [semBlk]; simp only [b7, runPrims, List.foldl, Prim.run]
      simp (disch := first | decide | ((try simp only [size_set]); refine Nat.lt_of_lt_of_le (m := 256) (by decide) ?_; first | assumption | omega)) only [rd_set_self]
      rw [q6 _ (by decide) (hxcj (by decide)), q6 _ (by decide) (hxcj (by decide)),
        t5.2.1, e5 _ (by decide) (by decide) (by decide), q4 _ (by decide) (hwj (by decide)),
        q3 _ (by decide), q2 _ (by decide) (hxj (by decide)), q1 _ (by decide), r4,
        add_toWord]
      exact congrArg toWord (by ring)
    have z7 := size_sem I (.blk b7) s6
    generalize semXIR I (.blk b7) s6 = s7 at hM7 e7 t7 z7
    have T7 := z7.trans T6
    rw [semXIR_seq]
    have v7 : rd s7.M zV = 0 := by
      rw [e7 _ (by decide), q6 _ (by decide) (hxcj (by decide)), t5.1]
    obtain ⟨c8, hM8⟩ := store_hp I s7 hM7 (p := zT) (v := zV) (by decide) (by decide) t7
      rwcj (pwc j hj) ((swc j hj).trans_eq T7.symm)
    have z8 := size_sem I (.store zT zV) s7
    generalize semXIR I (.store zT zV) s7 = s8 at c8 hM8 z8
    set b9 : List Prim := [.op .add zA zA cOne, .op .add zB zB cOne, .op .add zC zC cOne,
      .op .add zE zE cOne]
    have hM9 := inv_sem I (P := .blk b9) (by simp +decide [b9, WF, Prim.dst, zA, zB, zC, zE]) hM8
    have e9 : ∀ i, i ≠ zA → i ≠ zB → i ≠ zC → i ≠ zE → rd (semXIR I (.blk b9) s8).M i = rd s8.M i :=
      fun i h1 h2 h3 h4 => rdBlk_nw I _ _ (by
        intro p hp; simp only [b9, List.mem_cons, List.mem_nil_iff, or_false] at hp
        rcases hp with rfl | rfl | rfl | rfl <;> simp only [Prim.dst] <;>
          first | exact Ne.symm h1 | exact Ne.symm h2 | exact Ne.symm h3 | exact Ne.symm h4)
    have hz8 := hM8.1; simp only [regs] at hz8
    have hone : rd s8.M cOne = 1 := hM8.2 0 (by decide)
    -- registers through the body: the eight registers below `regs` other than the written ones
    have reg8 : ∀ r, r < 256 → r ≠ cTmp → r ≠ zU → r ≠ zV → r ≠ zD → r ≠ zT →
        rd s8.M r = rd s'.M r := fun r hr h0 h1 h2 h3 h4 => by
      rw [c8 r h0, if_neg (hwcj hr), e7 r h4, q6 r h0 (hxcj hr), e5 r h2 h3 h4, q4 r h0 (hwj hr),
        q3 r h1, q2 r h0 (hxj hr), q1 r h1]
    -- heap cells through the body
    have heap8 : ∀ y, 256 ≤ y → rd s8.M y =
        if y = w + c + j then 0 else if y = x + c + j then 0 else if y = w + j then rd s'.M (b + j)
        else if y = x + j then rd s'.M (a + j) else rd s'.M y := fun y hy => by
      have hyT : y ≠ cTmp := hne (by decide) hy
      rw [c8 y hyT]
      have hbj : ∀ {u : ℕ}, u < 256 → b + j ≠ u := fun hu => hne hu (Nat.le_trans hb (Nat.le_add_right b j))
      by_cases g1 : y = w + c + j
      · rw [if_pos g1, if_pos g1]; exact v7
      rw [if_neg g1, if_neg g1]
      by_cases g2 : y = x + c + j
      · rw [if_pos g2, e7 _ (hne (by decide) hy), c6 y hyT, if_pos g2, t5.1]
      rw [if_neg g2]
      by_cases g3 : y = w + j
      · rw [if_pos g3, e7 _ (hne (by decide) hy), q6 y hyT g2, e5 _ (hne (by decide) hy)
          (hne (by decide) hy) (hne (by decide) hy), c4 y hyT, if_pos g3, l3, if_pos rfl,
          q2 _ (hbj (by decide)) (fbx j hj), q1 _ (hbj (by decide))]
      rw [if_neg g3]
      by_cases g4 : y = x + j
      · rw [if_pos g4, e7 _ (hne (by decide) hy), q6 y hyT g2, e5 _ (hne (by decide) hy)
          (hne (by decide) hy) (hne (by decide) hy), q4 y hyT g3, q3 _ (hne (by decide) hy),
          c2 y hyT, if_pos g4, l1, if_pos rfl]
      rw [if_neg g4, e7 _ (hne (by decide) hy), q6 y hyT g2, e5 _ (hne (by decide) hy)
          (hne (by decide) hy) (hne (by decide) hy), q4 y hyT g3, q3 _ (hne (by decide) hy),
          q2 y hyT g4, q1 _ (hne (by decide) hy)]
    have ra : rd s'.M (a + j) = rd s.M (a + j) := r9 _ (Nat.le_add_right_of_le ha) (fra j hj)
    have rb : rd s'.M (b + j) = rd s.M (b + j) := r9 _ (Nat.le_add_right_of_le hb) (frb j hj)
    refine ⟨hM9, ?_, ?_, ?_, ?_, fun i hi => ?_, fun i hi => ?_, fun i hi => ?_, fun i hi => ?_,
      fun y hy hy2 => ?_, ?_⟩
    · rw [semBlk]; simp only [b9, runPrims, List.foldl, Prim.run]
      simp (disch := first | decide | ((try simp only [size_set]); refine Nat.lt_of_lt_of_le (m := 256) (by decide) ?_; first | assumption | omega)) only
        [rd_set_self, rd_set_ne]
      rw [reg8 _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), r1, hone,
        add_one_toWord, Nat.add_assoc]
    · rw [semBlk]; simp only [b9, runPrims, List.foldl, Prim.run]
      simp (disch := first | decide | ((try simp only [size_set]); refine Nat.lt_of_lt_of_le (m := 256) (by decide) ?_; first | assumption | omega)) only
        [rd_set_self, rd_set_ne]
      rw [reg8 _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), r2, hone,
        add_one_toWord, Nat.add_assoc]
    · rw [semBlk]; simp only [b9, runPrims, List.foldl, Prim.run]
      simp (disch := first | decide | ((try simp only [size_set]); refine Nat.lt_of_lt_of_le (m := 256) (by decide) ?_; first | assumption | omega)) only
        [rd_set_self, rd_set_ne]
      rw [reg8 _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), r3, hone,
        add_one_toWord, Nat.add_assoc]
    · rw [semBlk]; simp only [b9, runPrims, List.foldl, Prim.run]
      simp (disch := first | decide | ((try simp only [size_set]); refine Nat.lt_of_lt_of_le (m := 256) (by decide) ?_; first | assumption | omega)) only
        [rd_set_self, rd_set_ne]
      rw [reg8 _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), r4, hone,
        add_one_toWord, Nat.add_assoc]
    · have hv : 256 ≤ x + i := Nat.le_add_right_of_le hx
      rw [e9 _ (hne (by decide) hv) (hne (by decide) hv) (hne (by decide) hv)
        (hne (by decide) hv), heap8 _ hv]
      by_cases g : i = j
      · rw [g, if_neg (hX1 j hj j (Nat.lt_succ_self j)), if_neg (hX2 j hj j (Nat.lt_succ_self j)),
          if_neg (hX3 j hj j (Nat.lt_succ_self j)), if_pos rfl, ra]
      · rw [if_neg (hX1 j hj i hi), if_neg (hX2 j hj i hi), if_neg (hX3 j hj i hi),
          if_neg (fun e => g (Nat.add_left_cancel e)), r5 i (Nat.lt_of_le_of_ne (Nat.le_of_lt_succ hi) g)]
    · have hv : 256 ≤ x + c + i := Nat.le_add_right_of_le (Nat.le_add_right_of_le hx)
      rw [e9 _ (hne (by decide) hv) (hne (by decide) hv) (hne (by decide) hv)
        (hne (by decide) hv), heap8 _ hv]
      by_cases g : i = j
      · rw [g, if_neg (hXC1 j hj j (Nat.lt_succ_self j)), if_pos rfl]
      · rw [if_neg (hXC1 j hj i hi), if_neg (fun e => g (Nat.add_left_cancel e)), if_neg (hXC3 j hj i hi),
          if_neg (hXC4 j hj i hi), r6 i (Nat.lt_of_le_of_ne (Nat.le_of_lt_succ hi) g)]
    · have hv : 256 ≤ w + i := Nat.le_add_right_of_le hw
      rw [e9 _ (hne (by decide) hv) (hne (by decide) hv) (hne (by decide) hv)
        (hne (by decide) hv), heap8 _ hv]
      by_cases g : i = j
      · rw [g, if_neg (hW1 j hj j (Nat.lt_succ_self j)), if_neg (hW2 j hj j (Nat.lt_succ_self j)), if_pos rfl, rb]
      · rw [if_neg (hW1 j hj i hi), if_neg (hW2 j hj i hi), if_neg (fun e => g (Nat.add_left_cancel e)),
          if_neg (hW4 j hj i hi), r7 i (Nat.lt_of_le_of_ne (Nat.le_of_lt_succ hi) g)]
    · have hv : 256 ≤ w + c + i := Nat.le_add_right_of_le (Nat.le_add_right_of_le hw)
      rw [e9 _ (hne (by decide) hv) (hne (by decide) hv) (hne (by decide) hv)
        (hne (by decide) hv), heap8 _ hv]
      by_cases g : i = j
      · rw [g, if_pos rfl]
      · rw [if_neg (fun e => g (Nat.add_left_cancel e)), if_neg (hWC2 j hj i hi), if_neg (hWC3 j hj i hi),
          if_neg (hWC4 j hj i hi), r8 i (Nat.lt_of_le_of_ne (Nat.le_of_lt_succ hi) g)]
    · simp only [regs] at hy
      rw [e9 _ (hne (by decide) hy) (hne (by decide) hy) (hne (by decide) hy)
        (hne (by decide) hy), heap8 _ hy, if_neg (hY1 j hj y hy2), if_neg (hY2 j hj y hy2),
        if_neg (hY3 j hj y hy2), if_neg (hY4 j hj y hy2), r9 y hy hy2]
    · rw [e9 _ (by decide) (by decide) (by decide) (by decide),
        reg8 _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), r10]
  have hfin := loopK_gen I (copyBody c) s hM (by decide) (by decide) (by decide) hN hc R hR h0
    (fun j s' hj i1 i2 i3 => hb' j s' hj i1 i2 i3)
  obtain ⟨⟨_, _, _, _, f5, f6, f7, f8, f9, f10⟩, f11, _⟩ := hfin
  exact ⟨f5, f6, f7, f8, f9, f10, f11⟩

/-! ## The parent: pointwise product -/

theorem mulK_frame' (I : Array Word) (s : St) {d a b i : ℕ} (hi : i < 5 ∨ 9 ≤ i) (hd : i ≠ d) :
    rd (semXIR I (mulK d a b) s).M i = rd s.M i := by
  rw [mulK, sem_blk]; exact mulKC_frame _ _ _ hi hd _

theorem prodLoop_sem (I : Array Word) (s : St) (hM : Inv s.M) {p0 x w c : ℕ}
    (hc : c < 2 ^ 64) (hp : regs ≤ p0) (hx : regs ≤ x) (hw : regs ≤ w)
    (h64 : p0 + c < 2 ^ 64 ∧ x + c < 2 ^ 64 ∧ w + c < 2 ^ 64) (hsz : p0 + c ≤ s.M.size)
    (hpx : p0 + c ≤ x ∨ x + c ≤ p0) (hpw : p0 + c ≤ w ∨ w + c ≤ p0)
    (hA : rd s.M zA = toWord p0) (hC : rd s.M zC = toWord x) (hE : rd s.M zE = toWord w)
    (hN : rd s.M zN2 = toWord c) :
    (∀ i < c, rdK (semXIR I (.loopK zC2 zN2 (toWord c) prodBody) s).M (p0 + i) =
      rdK s.M (x + i) * rdK s.M (w + i)) ∧
    (∀ y, regs ≤ y → (y < p0 ∨ p0 + c ≤ y) →
      rd (semXIR I (.loopK zC2 zN2 (toWord c) prodBody) s).M y = rd s.M y) ∧
    rd (semXIR I (.loopK zC2 zN2 (toWord c) prodBody) s).M zP = rd s.M zP ∧
    Inv (semXIR I (.loopK zC2 zN2 (toWord c) prodBody) s).M := by
  have hs := hM.1
  simp only [regs] at hs hp hx hw
  obtain ⟨hp64, hx64, hw64⟩ := h64
  have hg : ∀ {u v : ℕ}, u < 256 → 256 ≤ v → v ≠ u := fun hu hv => Nat.ne_of_gt (Nat.lt_of_lt_of_le hu hv)
  let R : ℕ → Mem → Prop := fun j M => rd M zA = toWord (p0 + j) ∧ rd M zC = toWord (x + j) ∧
    rd M zE = toWord (w + j) ∧ (∀ i < j, rdK M (p0 + i) = rdK s.M (x + i) * rdK s.M (w + i)) ∧
    (∀ y, regs ≤ y → (y < p0 ∨ p0 + j ≤ y) → rd M y = rd s.M y) ∧ rd M zP = rd s.M zP
  have hR : ∀ j (M M' : Mem), (∀ i, i ≠ zC2 → i ≠ cTmp → rd M' i = rd M i) → R j M → R j M' := by
    rintro j M M' hMM ⟨r1, r2, r3, r4, r5, r6⟩
    have hy : ∀ y, 256 ≤ y → y ≠ zC2 ∧ y ≠ cTmp := fun y hy => by simp only [zC2, cTmp]; (clear hc hp64 hx64 hw64; omega)
    refine ⟨by rw [hMM _ (by decide) (by decide), r1], by rw [hMM _ (by decide) (by decide), r2],
      by rw [hMM _ (by decide) (by decide), r3], fun i hi => ?_, fun y hy' hy2 => ?_,
      by rw [hMM _ (by decide) (by decide), r6]⟩
    · have hv : 256 ≤ p0 + i := Nat.le_add_right_of_le hp
      rw [← r4 i hi]; exact rdK_eq (hMM _ (hy _ hv).1 (hy _ hv).2)
    · simp only [regs] at hy'
      rw [hMM _ (hy _ hy').1 (hy _ hy').2, r5 y hy' hy2]
  have h0 : R 0 s.M := ⟨by rw [hA, Nat.add_zero], by rw [hC, Nat.add_zero], by rw [hE, Nat.add_zero],
    fun i hi => absurd hi (Nat.not_lt_zero i), fun _ _ _ => rfl, rfl⟩
  have hb' : ∀ j (s' : St), j < c → Inv s'.M → s'.M.size = s.M.size → R j s'.M →
      Inv (semXIR I prodBody s').M ∧ R (j + 1) (semXIR I prodBody s').M := by
    rintro j s' hj i1 i2 ⟨r1, r2, r3, r4, r5, r6⟩
    have hs' := i1.1
    simp only [regs] at hs'
    rw [prodBody, semXIR_seq]
    obtain ⟨l1, hM1⟩ := load_hp I s' i1 (d := zU) (p := zC) (by decide) (by decide) r2 (by omega)
    have z1 := size_sem I (.load zU zC) s'
    generalize semXIR I (.load zU zC) s' = s1 at l1 hM1 z1
    rw [semXIR_seq]
    obtain ⟨l2, hM2⟩ := load_hp I s1 hM1 (d := zV) (p := zE) (by decide) (by decide)
      (by rw [l1, if_neg (by decide), r3]) (by omega)
    have z2 := size_sem I (.load zV zE) s1
    generalize semXIR I (.load zV zE) s1 = s2 at l2 hM2 z2
    rw [semXIR_seq]
    have m3 := mulK_sem (I := I) (s := s2) hM2 (d := zW) (a := zU) (b := zV) (by decide) (by decide)
      (by decide) (by decide)
    have f3 : ∀ i, (i < 5 ∨ 9 ≤ i) → i ≠ zW → rd (semXIR I (mulK zW zU zV) s2).M i = rd s2.M i :=
      fun i h1 h2 => mulK_frame' I s2 h1 h2
    have hM3 := inv_sem I (wf_mulK zW zU zV (by decide)) hM2
    have z3 := size_sem I (mulK zW zU zV) s2
    generalize semXIR I (mulK zW zU zV) s2 = s3 at m3 f3 hM3 z3
    rw [semXIR_seq]
    obtain ⟨c4, hM4⟩ := store_hp I s3 hM3 (p := zA) (v := zW) (by decide) (by decide)
      (by rw [f3 _ (by decide) (by decide), l2, if_neg (by decide), l1, if_neg (by decide), r1])
      (Nat.le_add_right_of_le hp) (by omega) (by (clear hc hp64 hx64 hw64; omega))
    have z4 := size_sem I (.store zA zW) s3
    generalize semXIR I (.store zA zW) s3 = s4 at c4 hM4 z4
    set b5 : List Prim := [.op .add zA zA cOne, .op .add zC zC cOne, .op .add zE zE cOne]
    have hM5 := inv_sem I (P := .blk b5) (by simp +decide [b5, WF, Prim.dst, zA, zC, zE]) hM4
    have e5 : ∀ i, i ≠ zA → i ≠ zC → i ≠ zE → rd (semXIR I (.blk b5) s4).M i = rd s4.M i :=
      fun i h1 h2 h3 => rdBlk_nw I _ _ (by
        intro p hp; simp only [b5, List.mem_cons, List.mem_nil_iff, or_false] at hp
        rcases hp with rfl | rfl | rfl <;> simp only [Prim.dst] <;>
          first | exact Ne.symm h1 | exact Ne.symm h2 | exact Ne.symm h3)
    have hz4 := hM4.1; simp only [regs] at hz4
    have hone : rd s4.M cOne = 1 := hM4.2 0 (by decide)
    have reg4 : ∀ r, r < 256 → 9 ≤ r → r ≠ zU → r ≠ zV → r ≠ zW → rd s4.M r = rd s'.M r :=
      fun r hr h0 h1 h2 h3 => by
        rw [c4 r (by simp only [cTmp]; (clear hc hp64 hx64 hw64; omega)), if_neg (Nat.ne_of_lt (Nat.lt_of_lt_of_le hr (Nat.le_add_right_of_le hp))), f3 r (Or.inr h0) h3, l2, if_neg h2,
          l1, if_neg h1]
    have heap4 : ∀ y, 256 ≤ y → rd s4.M y = if y = p0 + j then rd s3.M zW else rd s'.M y :=
      fun y hy => by
        rw [c4 y (hg (by decide) hy)]
        split_ifs
        · rfl
        · rw [f3 y (Or.inr (Nat.le_trans (by decide) hy)) (hg (by decide) hy), l2, if_neg (hg (by decide) hy),
            l1, if_neg (hg (by decide) hy)]
    have val : rdK s3.M zW = rdK s.M (x + j) * rdK s.M (w + j) := by
      rw [m3]
      have u1 : rdK s2.M zU = rdK s.M (x + j) := by
        rw [rdK, l2, if_neg (by decide), l1, if_pos rfl, r5 _ (Nat.le_add_right_of_le hx) (by (clear hc hp64 hx64 hw64; omega))]; rfl
      have u2 : rdK s2.M zV = rdK s.M (w + j) := by
        rw [rdK, l2, if_pos rfl, l1, if_neg (hg (by decide) (Nat.le_add_right_of_le hw)),
          r5 _ (Nat.le_add_right_of_le hw) (by (clear hc hp64 hx64 hw64; omega))]; rfl
      rw [u1, u2]
    refine ⟨hM5, ?_, ?_, ?_, fun i hi => ?_, fun y hy hy2 => ?_, ?_⟩
    · rw [semBlk]; simp only [b5, runPrims, List.foldl, Prim.run]
      simp (disch := first | decide | ((try simp only [size_set]); refine Nat.lt_of_lt_of_le (m := 256) (by decide) ?_; first | assumption | omega)) only
        [rd_set_self, rd_set_ne]
      rw [reg4 _ (by decide) (by decide) (by decide) (by decide) (by decide), r1, hone,
        add_one_toWord, Nat.add_assoc]
    · rw [semBlk]; simp only [b5, runPrims, List.foldl, Prim.run]
      simp (disch := first | decide | ((try simp only [size_set]); refine Nat.lt_of_lt_of_le (m := 256) (by decide) ?_; first | assumption | omega)) only
        [rd_set_self, rd_set_ne]
      rw [reg4 _ (by decide) (by decide) (by decide) (by decide) (by decide), r2, hone,
        add_one_toWord, Nat.add_assoc]
    · rw [semBlk]; simp only [b5, runPrims, List.foldl, Prim.run]
      simp (disch := first | decide | ((try simp only [size_set]); refine Nat.lt_of_lt_of_le (m := 256) (by decide) ?_; first | assumption | omega)) only
        [rd_set_self, rd_set_ne]
      rw [reg4 _ (by decide) (by decide) (by decide) (by decide) (by decide), r3, hone,
        add_one_toWord, Nat.add_assoc]
    · have hv : 256 ≤ p0 + i := Nat.le_add_right_of_le hp
      rw [rdK_eq (e5 _ (hg (by decide) hv) (hg (by decide) hv) (hg (by decide) hv)),
        rdK, heap4 _ hv]
      by_cases g : i = j
      · subst g; rw [if_pos rfl, ← val]; rfl
      · rw [if_neg (by (clear hc hp64 hx64 hw64; omega))]; exact r4 i (by (clear hc hp64 hx64 hw64; omega))
    · simp only [regs] at hy
      rw [e5 _ (hg (by decide) hy) (hg (by decide) hy) (hg (by decide) hy),
        heap4 _ hy, if_neg (by (clear hc hp64 hx64 hw64; omega)), r5 y hy (by (clear hc hp64 hx64 hw64; omega))]
    · rw [e5 _ (by decide) (by decide) (by decide),
        reg4 _ (by decide) (by decide) (by decide) (by decide) (by decide), r6]
  have hfin := loopK_gen I prodBody s hM (by decide) (by decide) (by decide) hN hc R hR h0
    (fun j s' hj i1 i2 i3 => hb' j s' hj i1 i2 i3)
  obtain ⟨⟨_, _, _, f4, f5, f6⟩, f7, _⟩ := hfin
  exact ⟨f4, f5, f6, f7⟩

/-! ## One parent -/

theorem bflyNIR_nw_rA0 (N ℓ tb : ℕ) : ¬ Writes (bflyNIR N ℓ tb) rA0 := by
  intro hw
  simp only [bflyNIR, lvlNStep, levelNIR, pairNBody, pairPs, alphaNIR, alphaBody, arithIR, addK, mulK,
    mulKC, redC, Writes, Prim.dst, List.mem_cons, List.mem_nil_iff, List.cons_append,
    List.nil_append, exists_eq_or_imp, exists_eq_left, or_false] at hw
  simp only [rLv, rTr, rN3, rC3, rQ, rP2, rN1, rC1, uT1, uX, uT2, rBs, rAL, rAH, rA0, rBit, uI,
    rTa, rN2, rC2, fAl, fG, fU, fW, fH, fT, fN, cTmp] at hw
  omega

theorem fwdNIR_nw_rA0 (N ℓ tb : ℕ) : ¬ Writes (fwdNIR N ℓ tb) rA0 := by
  intro hw
  simp only [fwdNIR, fStepN, fPreN, flevelNIR, fpairNBody, pairPs, alphaNIR, alphaBody, farithIR,
    addK, mulK, mulKC, redC, Writes, Prim.dst, List.mem_cons, List.mem_nil_iff, List.cons_append,
    List.nil_append, exists_eq_or_imp, exists_eq_left, or_false] at hw
  simp only [rLv, rTr, rN3, rC3, rQ, rP2, rN1, rC1, uT1, uX, uT2, rBs, rAL, rAH, rA0, rBit, uI,
    rTa, rN2, rC2, fAl, fG, fU, fW, fH, fT, fN, cTmp, rKf, rTbf] at hw
  omega

theorem NN_le {N : ℕ} (hN64 : N ≤ 64) : N * N ≤ 4096 := by
  have := Nat.mul_le_mul hN64 hN64; simpa using this

-- The arithmetic of `parentBody_sem` (proof helper; a small context keeps `omega` cheap).
private theorem parentBody_arith {B n c q N h : ℕ} (hcn : c ≤ n) (hpq : q + 2 * c ≤ 2 * n)
    (h64 : B + 4096 + 11 * n < 2 ^ 64) (hB : 256 ≤ B) (hN : h + 2 ≤ N) (hNN : N * N ≤ 4096) :
    (2 * c < 2 ^ 64) ∧
    (c ≤ 2 * c) ∧
    (c < 2 ^ 64) ∧
    (B + 4096 + 7 * n + 2 * c < 2 ^ 64) ∧
    (B + 4096 + 9 * n + 2 * c < 2 ^ 64) ∧
    (B + 4096 + 4 * n + q + c < 2 ^ 64) ∧
    (B + 4096 + 4 * n + q + c + c < 2 ^ 64) ∧
    (B + 4096 + 4 * n + q + 2 * c < 2 ^ 64) ∧
    (B + 4096 + 7 * n + c < 2 ^ 64) ∧
    (B + 4096 + 9 * n + c < 2 ^ 64) ∧
    (B + 4096 + 7 * n + 2 * c ≤ B + 4096 + 11 * n) ∧
    (B + 4096 + 9 * n + 2 * c ≤ B + 4096 + 11 * n) ∧
    (B + 4096 + 7 * n + c ≤ B + 4096 + 11 * n) ∧
    (B + 4096 + 9 * n + c ≤ B + 4096 + 11 * n) ∧
    (B + 4096 + 4 * n + q + 2 * c ≤ B + 4096 + 11 * n) ∧
    (B + 4096 + 7 * n + 2 * c ≤ B + 4096 + 9 * n) ∧
    (B + 4096 + 4 * n + q + c ≤ B + 4096 + 7 * n) ∧
    (B + 4096 + 4 * n + q + c + c ≤ B + 4096 + 7 * n) ∧
    (B + 4096 + 4 * n + q + 2 * c ≤ B + 4096 + 7 * n) ∧
    (B + 4096 + 4 * n + q + 2 * c ≤ B + 4096 + 9 * n) ∧
    (B + N * N < 2 ^ 64) ∧
    (B + N * N ≤ B + 4096 + 7 * n) ∧
    (B + N * N ≤ B + 4096 + 9 * n) ∧
    (h + 1 ≤ N) ∧
    (∀ i < c, q + i < 2 * n) ∧
    (∀ i < c, q + c + i < 2 * n) ∧
    (∀ y, (y < B + 4096 + 4 * n + q ∨ (B + 4096 + 4 * n + (q + 2 * c) ≤ y ∧ y < B + 4096 + 7 * n) ∨ B + 4096 + 11 * n ≤ y) → y < B + 4096 + 7 * n ∨ B + 4096 + 7 * n + 2 * c ≤ y) ∧
    (∀ y, (y < B + 4096 + 4 * n + q ∨ (B + 4096 + 4 * n + (q + 2 * c) ≤ y ∧ y < B + 4096 + 7 * n) ∨ B + 4096 + 11 * n ≤ y) → y < B + 4096 + 9 * n ∨ B + 4096 + 9 * n + 2 * c ≤ y) ∧
    (∀ y, (y < B + 4096 + 4 * n + q ∨ (B + 4096 + 4 * n + (q + 2 * c) ≤ y ∧ y < B + 4096 + 7 * n) ∨ B + 4096 + 11 * n ≤ y) → y < B + 4096 + 4 * n + q ∨ B + 4096 + 4 * n + q + 2 * c ≤ y) ∧
    (∀ y, (y < B + 4096 + 4 * n + q ∨ (B + 4096 + 4 * n + (q + 2 * c) ≤ y ∧ y < B + 4096 + 7 * n) ∨ B + 4096 + 11 * n ≤ y) → y < B + 4096 + 7 * n ∨ B + 4096 + 9 * n + 2 * c ≤ y) ∧
    (∀ v < N, ∀ i < N, B + N * v + i < B + 4096 + 7 * n) :=
  ⟨Nat.lt_of_le_of_lt (by clear h64; omega : 2 * c ≤ B + 4096 + 11 * n) h64,
   by clear h64; omega,
   Nat.lt_of_le_of_lt (by clear h64; omega : c ≤ B + 4096 + 11 * n) h64,
   Nat.lt_of_le_of_lt (by clear h64; omega : B + 4096 + 7 * n + 2 * c ≤ B + 4096 + 11 * n) h64,
   Nat.lt_of_le_of_lt (by clear h64; omega : B + 4096 + 9 * n + 2 * c ≤ B + 4096 + 11 * n) h64,
   Nat.lt_of_le_of_lt (by clear h64; omega : B + 4096 + 4 * n + q + c ≤ B + 4096 + 11 * n) h64,
   Nat.lt_of_le_of_lt (by clear h64; omega : B + 4096 + 4 * n + q + c + c ≤ B + 4096 + 11 * n) h64,
   Nat.lt_of_le_of_lt (by clear h64; omega : B + 4096 + 4 * n + q + 2 * c ≤ B + 4096 + 11 * n) h64,
   Nat.lt_of_le_of_lt (by clear h64; omega : B + 4096 + 7 * n + c ≤ B + 4096 + 11 * n) h64,
   Nat.lt_of_le_of_lt (by clear h64; omega : B + 4096 + 9 * n + c ≤ B + 4096 + 11 * n) h64,
   by clear h64; omega,
   by clear h64; omega,
   by clear h64; omega,
   by clear h64; omega,
   by clear h64; omega,
   by clear h64; omega,
   by clear h64; omega,
   by clear h64; omega,
   by clear h64; omega,
   by clear h64; omega,
   Nat.lt_of_le_of_lt (by clear h64; omega : B + N * N ≤ B + 4096 + 11 * n) h64,
   by clear h64; omega,
   by clear h64; omega,
   by clear h64; omega,
   fun i hi => by clear h64; omega,
   fun i hi => by clear h64; omega,
   fun y hy => by clear h64; omega,
   fun y hy => by clear h64; omega,
   fun y hy => by clear h64; omega,
   fun y hy => by clear h64; omega,
   fun v hv i hi => by
    clear h64
    have := Nat.mul_le_mul_left N (show v + 1 ≤ N by omega); rw [Nat.mul_succ] at this; omega⟩

theorem parentBody_sem (I : Array Word) (s : St) (hM : Inv s.M) {N ℓ B h p : ℕ}
    {Tf : ℕ → BF64} (hN : h + 2 ≤ N) (hN64 : N ≤ 64) (hh : h < ℓ) (hB : regs ≤ B)
    (hsz : fdEnd B ℓ ≤ s.M.size) (h64 : fdEnd B ℓ < 2 ^ 64)
    (hp : (p + 1) * 2 ^ (h + 2) ≤ 2 ^ (ℓ + 1))
    (hP : rd s.M zP = toWord (tA B ℓ + p * 2 ^ (h + 2)))
    (hW : ∀ v < N, ∀ i < N, rdK s.M (tbA B + N * v + i) = (wRow ptK N v).getD i 0)
    (hT : ∀ i < 2 ^ (ℓ + 1), rdK s.M (tA B ℓ + i) = Tf i) :
    (∀ i < 2 ^ (h + 2), rdK (semXIR I (parentBody N ℓ B h) s).M (tA B ℓ + p * 2 ^ (h + 2) + i) =
      treeLevel N h Tf (p * 2 ^ (h + 2) + i)) ∧
    (∀ y, regs ≤ y → (y < tA B ℓ + p * 2 ^ (h + 2) ∨
        (tA B ℓ + (p + 1) * 2 ^ (h + 2) ≤ y ∧ y < xA B ℓ) ∨ fdEnd B ℓ ≤ y) →
      rd (semXIR I (parentBody N ℓ B h) s).M y = rd s.M y) ∧
    rd (semXIR I (parentBody N ℓ B h) s).M zP = toWord (tA B ℓ + (p + 1) * 2 ^ (h + 2)) ∧
    Inv (semXIR I (parentBody N ℓ B h) s).M := by
  have hs := hM.1
  simp only [regs] at hs hB
  have hNN := NN_le hN64
  have hc2 : 2 ^ (h + 2) = 2 * 2 ^ (h + 1) := by rw [pow_succ]; ring
  have hn2 : 2 ^ (ℓ + 1) = 2 * 2 ^ ℓ := by rw [pow_succ]; ring
  have hcn : 2 ^ (h + 1) ≤ 2 ^ ℓ := Nat.pow_le_pow_right (by norm_num) hh
  have hpq : p * 2 ^ (h + 2) + 2 ^ (h + 2) ≤ 2 ^ (ℓ + 1) := by
    have := hp; rw [Nat.add_mul, one_mul] at this; exact this
  set c := 2 ^ (h + 1) with hcdef
  set q := p * 2 ^ (h + 2) with hqdef
  have hq1 : (p + 1) * 2 ^ (h + 2) = q + 2 * c := by rw [Nat.succ_mul, ← hqdef, hc2]
  simp only [fdEnd, tA, xA, wA, tbA] at hsz h64 hP hW hT ⊢
  rw [hq1]
  rw [hc2] at hpq ⊢
  rw [hn2] at hpq hT
  obtain ⟨hc64, hcc, pc64, pX64, pW64, pA64, pB64, pA264, pXc64, pWc64, pXE, pWE, pXcE, pWcE, pAE, pXW, pAX, pBX, pA2X, pA2W, pBNN, pBNNX, pBNNW, hN1, hqi, hqci, hyX, hyW, hyA, hyXW, htX⟩ :=
    parentBody_arith hcn hpq h64 hB hN hNN
  have hR3 : ∀ {k1 k2 : ℕ}, regs ≤ B + k1 + k2 := Nat.le_add_right_of_le (Nat.le_add_right_of_le hB)
  have hR4 : ∀ {k1 k2 k3 : ℕ}, regs ≤ B + k1 + k2 + k3 := Nat.le_add_right_of_le hR3
  have hR5 : ∀ {k1 k2 k3 k4 : ℕ}, regs ≤ B + k1 + k2 + k3 + k4 := Nat.le_add_right_of_le hR4
  have hR6 : ∀ {k1 k2 k3 k4 k5 : ℕ}, regs ≤ B + k1 + k2 + k3 + k4 + k5 := Nat.le_add_right_of_le hR5
  have htW : ∀ v < N, ∀ i < N, B + N * v + i < B + 4096 + 9 * 2 ^ ℓ := fun v hv i hi =>
    Nat.lt_of_lt_of_le (htX v hv i hi) (Nat.le_trans (Nat.le_add_right _ _) pXW)
  have hz : ∀ (M : Mem) (y : ℕ), rd M y = 0 → rdK M y = 0 := fun M y h => by rw [rdK, h]; rfl
  -- 1. the registers
  rw [parentBody, semXIR_seq, show tbA B = B from rfl]
  set b0 : List Prim := [.op .or zA zP zP, .const zD (toWord c), .op .add zB zP zD,
    .const zC (toWord (xA B ℓ)), .const zE (toWord (wA B ℓ)), .const zN2 (toWord c)]
  have hM0 := inv_sem I (P := .blk b0) (by simp +decide [b0, WF, Prim.dst, zA, zD, zB, zC, zE, zN2]) hM
  have z0 := size_sem I (.blk b0) s
  have k0 : ∀ r, (256 ≤ r ∨ r = zP) → rd (semXIR I (.blk b0) s).M r = rd s.M r := fun r hr => by
    refine rdBlk_nw I _ s ?_
    intro p' hp'; simp only [b0, List.mem_cons, List.mem_nil_iff, or_false] at hp'
    rcases hp' with rfl | rfl | rfl | rfl | rfl | rfl <;> simp only [Prim.dst] <;>
      rcases hr with hr | rfl <;> simp only [zA, zD, zB, zC, zE, zN2, zP] <;> first | decide | exact Nat.ne_of_lt (Nat.lt_of_lt_of_le (by decide) hr)
  have r0 : rd (semXIR I (.blk b0) s).M zA = toWord (B + 4096 + 4 * 2 ^ ℓ + q) ∧
      rd (semXIR I (.blk b0) s).M zB = toWord (B + 4096 + 4 * 2 ^ ℓ + q + c) ∧
      rd (semXIR I (.blk b0) s).M zC = toWord (B + 4096 + 7 * 2 ^ ℓ) ∧
      rd (semXIR I (.blk b0) s).M zE = toWord (B + 4096 + 9 * 2 ^ ℓ) ∧
      rd (semXIR I (.blk b0) s).M zN2 = toWord c := by
    rw [semBlk]; simp only [b0, runPrims, List.foldl, Prim.run]
    refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;>
    simp (disch := first | decide | ((try simp only [size_set]); refine Nat.lt_of_lt_of_le (m := 256) (by decide) ?_; first | assumption | omega)) only
      [rd_set_self, rd_set_ne] <;> (try simp only [xA, wA])
    · rw [hP]; exact BitVec.or_self
    · rw [hP, add_toWord]
  generalize semXIR I (.blk b0) s = s0 at hM0 z0 k0 r0
  obtain ⟨a0, b0', c0, e0, n0⟩ := r0
  have hs0 := hM0.1; simp only [regs] at hs0
  have hE0 := hsz.trans_eq z0.symm
  -- 2. copy and pad
  rw [semXIR_seq]
  obtain ⟨y1, y2, y3, y4, y5, y6, hM1⟩ := copyLoop_sem I s0 hM0 (a := B + 4096 + 4 * 2 ^ ℓ + q)
    (b := B + 4096 + 4 * 2 ^ ℓ + q + c) (x := B + 4096 + 7 * 2 ^ ℓ) (w := B + 4096 + 9 * 2 ^ ℓ)
    (c := c) pc64 hR4 hR5 hR3 hR3 ⟨pX64, pW64, pA64, pB64⟩
    ⟨le_trans pXE hE0, le_trans pWE hE0⟩ pXW (Or.inl pAX) (Or.inl pBX) a0 b0' c0 e0 n0
  have z1 := size_sem I (.loopK zC2 zN2 (toWord c) (copyBody c)) s0
  generalize semXIR I (.loopK zC2 zN2 (toWord c) (copyBody c)) s0 = s1 at y1 y2 y3 y4 y5 y6 hM1 z1
  have hs1 := hM1.1; simp only [regs] at hs1
  have hE1 := hE0.trans_eq z1.symm
  -- the children, as `K` values
  have ch0 : ∀ i < c, rdK s1.M (B + 4096 + 7 * 2 ^ ℓ + i) = Tf (q + i) := fun i hi => by
    rw [rdK_eq (y1 i hi), rdK_eq (k0 _ (Or.inl hR5)), show B + 4096 + 4 * 2 ^ ℓ + q + i =
      B + 4096 + 4 * 2 ^ ℓ + (q + i) by ring, hT _ (hqi i hi)]
  have ch1 : ∀ i < c, rdK s1.M (B + 4096 + 9 * 2 ^ ℓ + i) = Tf (q + c + i) := fun i hi => by
    rw [rdK_eq (y3 i hi), rdK_eq (k0 _ (Or.inl hR6)), show B + 4096 + 4 * 2 ^ ℓ + q + c + i =
      B + 4096 + 4 * 2 ^ ℓ + (q + c + i) by ring, hT _ (hqci i hi)]
  -- 3–8. the extensions
  have tb1 : ∀ v < N, ∀ i < N, rdK s1.M (B + N * v + i) = (wRow ptK N v).getD i 0 := fun v hv i hi => by
    rw [rdK_eq (y5 _ hR3 (Or.inl (htX v hv i hi))), rdK_eq (k0 _ (Or.inl hR3)),
      hW v hv i hi]
  rw [semXIR_seq]
  have hA1 : rd (semXIR I (.blk [.const rA0 (toWord (xA B ℓ))]) s1).M rA0 = toWord (B + 4096 + 7 * 2 ^ ℓ) := by
    rw [semBlk]; simp only [runPrims, List.foldl, Prim.run]
    rw [rd_set_self (Nat.lt_of_lt_of_le (m := 256) (by decide) hM1.1)]; rfl
  have hM2 := inv_sem I (P := .blk [.const rA0 (toWord (xA B ℓ))]) (by simp +decide [WF, Prim.dst, rA0]) hM1
  have k2 : ∀ r, r ≠ rA0 → rd (semXIR I (.blk [.const rA0 (toWord (xA B ℓ))]) s1).M r = rd s1.M r :=
    fun r hr => rdBlk_nw I _ _ (by simp [Prim.dst]; exact Ne.symm hr)
  have z2 := size_sem I (.blk [.const rA0 (toWord (xA B ℓ))]) s1
  generalize semXIR I (.blk [.const rA0 (toWord (xA B ℓ))]) s1 = s2 at hA1 hM2 k2 z2
  have hE2 := hE1.trans_eq z2.symm
  have hrA : ∀ y, 256 ≤ y → y ≠ rA0 := fun y hy => Nat.ne_of_gt (Nat.lt_of_lt_of_le (by decide) hy)
  rw [semXIR_seq]
  obtain ⟨x3, f3, hM3⟩ := bflyNIR_sem I s2 hM2 hN64 (A := B + 4096 + 7 * 2 ^ ℓ) (tb := B) (ℓ := h + 1)
    (Y := fun i => Tf (q + i)) hN1 hR3 pXc64 (le_trans pXcE hE2)
    hB pBNN (Or.inl pBNNX) hA1
    (fun v hv i hi => by rw [rdK_eq (k2 _ (hrA _ hR3)), tb1 v hv i hi])
    (fun i hi => by rw [rdK_eq (k2 _ (hrA _ hR4)), ch0 i hi])
  have g3 := frame I (bflyNIR N (h + 1) B) s2 (wf_bflyNIR N _ _) hM2 zP (by decide)
    (bflyNIR_nw_hi N _ _ (by decide))
  have a3 := frame I (bflyNIR N (h + 1) B) s2 (wf_bflyNIR N _ _) hM2 rA0 (by decide)
    (bflyNIR_nw_rA0 N _ _)
  rw [hA1] at a3
  have z3 := size_sem I (bflyNIR N (h + 1) B) s2
  generalize semXIR I (bflyNIR N (h + 1) B) s2 = s3 at x3 f3 hM3 g3 z3 a3
  have hE3 := hE2.trans_eq z3.symm
  rw [semXIR_seq]
  obtain ⟨x4, f4, hM4⟩ := fwdNIR_sem I s3 hM3 hN64 (A := B + 4096 + 7 * 2 ^ ℓ) (tb := B) (ℓ := h + 2)
    (Y := fun i => if i < c then bflyRun ptK N 0 (h + 1) (fun i => Tf (q + i)) i else 0)
    hN hR3 (by rw [hc2]; exact pX64) (by rw [hc2]; exact le_trans pXE hE3)
    hB pBNN (Or.inl pBNNX) a3
    (fun v hv i hi => by
      rw [rdK_eq (f3 _ hR3 (Or.inl (htX v hv i hi))), rdK_eq (k2 _ (hrA _ hR3)),
        tb1 v hv i hi])
    (fun i hi => by
      rw [hc2] at hi
      by_cases hic : i < c
      · rw [if_pos hic, x3 i hic]
      · have hic' := Nat.le_of_not_lt hic
        rw [if_neg hic, rdK_eq (f3 _ hR4 (Or.inr (Nat.add_le_add_left hic' _))),
          rdK_eq (k2 _ (hrA _ hR4)), show B + 4096 + 7 * 2 ^ ℓ + i =
            B + 4096 + 7 * 2 ^ ℓ + c + (i - c) by rw [Nat.add_assoc _ c (i - c), Nat.add_sub_cancel' hic'],
          hz _ _ (y2 _ (Nat.sub_lt_left_of_lt_add hic' (hi.trans_eq (Nat.two_mul c))))])
  have g4 := frame I (fwdNIR N (h + 2) B) s3 (wf_fwdNIR N _ _) hM3 zP (by decide)
    (fwdNIR_nw_hi N _ _ (by decide))
  have z4 := size_sem I (fwdNIR N (h + 2) B) s3
  generalize semXIR I (fwdNIR N (h + 2) B) s3 = s4 at x4 f4 hM4 g4 z4
  have hE4 := hE3.trans_eq z4.symm
  rw [hc2] at x4 f4
  -- the second child
  rw [semXIR_seq]
  have hA5 : rd (semXIR I (.blk [.const rA0 (toWord (wA B ℓ))]) s4).M rA0 = toWord (B + 4096 + 9 * 2 ^ ℓ) := by
    rw [semBlk]; simp only [runPrims, List.foldl, Prim.run]
    rw [rd_set_self (Nat.lt_of_lt_of_le (m := 256) (by decide) hM4.1)]; rfl
  have hM5 := inv_sem I (P := .blk [.const rA0 (toWord (wA B ℓ))]) (by simp +decide [WF, Prim.dst, rA0]) hM4
  have k5 : ∀ r, r ≠ rA0 → rd (semXIR I (.blk [.const rA0 (toWord (wA B ℓ))]) s4).M r = rd s4.M r :=
    fun r hr => rdBlk_nw I _ _ (by simp [Prim.dst]; exact Ne.symm hr)
  have z5 := size_sem I (.blk [.const rA0 (toWord (wA B ℓ))]) s4
  generalize semXIR I (.blk [.const rA0 (toWord (wA B ℓ))]) s4 = s5 at hA5 hM5 k5 z5
  have hE5 := hE4.trans_eq z5.symm
  -- the heap after the first child's extension, outside the `X` row
  have back5 : ∀ y, 256 ≤ y → (y < B + 4096 + 7 * 2 ^ ℓ ∨ B + 4096 + 7 * 2 ^ ℓ + 2 * c ≤ y) →
      rd s5.M y = rd s1.M y := fun y hy hy2 => by
    rw [k5 _ (hrA _ hy), f4 _ hy hy2, f3 _ hy
      (hy2.imp_right (le_trans (Nat.add_le_add_left hcc _))), k2 _ (hrA _ hy)]
  have tb5 : ∀ v < N, ∀ i < N, rdK s5.M (B + N * v + i) = (wRow ptK N v).getD i 0 := fun v hv i hi => by
    rw [rdK_eq (back5 _ hR3 (Or.inl (htX v hv i hi))), tb1 v hv i hi]
  rw [semXIR_seq]
  obtain ⟨x6, f6, hM6⟩ := bflyNIR_sem I s5 hM5 hN64 (A := B + 4096 + 9 * 2 ^ ℓ) (tb := B) (ℓ := h + 1)
    (Y := fun i => Tf (q + c + i)) hN1 hR3 pWc64 (le_trans pWcE hE5)
    hB pBNN (Or.inl pBNNW) hA5 tb5
    (fun i hi => by rw [rdK_eq (back5 _ hR4 (Or.inr (le_trans pXW (Nat.le_add_right _ _)))), ch1 i hi])
  have g6 := frame I (bflyNIR N (h + 1) B) s5 (wf_bflyNIR N _ _) hM5 zP (by decide)
    (bflyNIR_nw_hi N _ _ (by decide))
  have a6 := frame I (bflyNIR N (h + 1) B) s5 (wf_bflyNIR N _ _) hM5 rA0 (by decide)
    (bflyNIR_nw_rA0 N _ _)
  rw [hA5] at a6
  have z6 := size_sem I (bflyNIR N (h + 1) B) s5
  generalize semXIR I (bflyNIR N (h + 1) B) s5 = s6 at x6 f6 hM6 g6 z6 a6
  have hE6 := hE5.trans_eq z6.symm
  rw [semXIR_seq]
  obtain ⟨x7, f7, hM7⟩ := fwdNIR_sem I s6 hM6 hN64 (A := B + 4096 + 9 * 2 ^ ℓ) (tb := B) (ℓ := h + 2)
    (Y := fun i => if i < c then bflyRun ptK N 0 (h + 1) (fun i => Tf (q + c + i)) i else 0)
    hN hR3 (by rw [hc2]; exact pW64) (by rw [hc2]; exact le_trans pWE hE6)
    hB pBNN (Or.inl pBNNW) a6
    (fun v hv i hi => by
      rw [rdK_eq (f6 _ hR3 (Or.inl (htW v hv i hi))), tb5 v hv i hi])
    (fun i hi => by
      rw [hc2] at hi
      by_cases hic : i < c
      · rw [if_pos hic, x6 i hic]
      · have hic' := Nat.le_of_not_lt hic
        rw [if_neg hic, rdK_eq (f6 _ hR4 (Or.inr (Nat.add_le_add_left hic' _))),
          rdK_eq (back5 _ hR4 (Or.inr (le_trans pXW (Nat.le_add_right _ _)))),
          show B + 4096 + 9 * 2 ^ ℓ + i =
            B + 4096 + 9 * 2 ^ ℓ + c + (i - c) by rw [Nat.add_assoc _ c (i - c), Nat.add_sub_cancel' hic'],
          hz _ _ (y4 _ (Nat.sub_lt_left_of_lt_add hic' (hi.trans_eq (Nat.two_mul c))))])
  have g7 := frame I (fwdNIR N (h + 2) B) s6 (wf_fwdNIR N _ _) hM6 zP (by decide)
    (fwdNIR_nw_hi N _ _ (by decide))
  have z7 := size_sem I (fwdNIR N (h + 2) B) s6
  generalize semXIR I (fwdNIR N (h + 2) B) s6 = s7 at x7 f7 hM7 g7 z7
  have hE7 := hE6.trans_eq z7.symm
  rw [hc2] at x7 f7
  -- the `X` row is untouched by the second child's extension
  have xrow : ∀ i < 2 * c, rdK s7.M (B + 4096 + 7 * 2 ^ ℓ + i) = rdK s4.M (B + 4096 + 7 * 2 ^ ℓ + i) :=
    fun i hi => rdK_eq (by
      have hiW := Or.inl (b := B + 4096 + 9 * 2 ^ ℓ + 2 * c ≤ B + 4096 + 7 * 2 ^ ℓ + i)
        (Nat.lt_of_lt_of_le (Nat.add_lt_add_left hi _) pXW)
      rw [f7 _ hR4 hiW, f6 _ hR4 (hiW.imp_right (le_trans (Nat.add_le_add_left hcc _))),
        k5 _ (hrA _ hR4)])
  have zP7 : rd s7.M zP = toWord (B + 4096 + 4 * 2 ^ ℓ + q) := by
    rw [g7, g6, k5 _ (by decide), g4, g3, k2 _ (by decide), y6, k0 _ (Or.inr rfl), hP]
  -- 9–10. the product
  rw [semXIR_seq]
  set b9 : List Prim := [.op .or zA zP zP, .const zC (toWord (xA B ℓ)), .const zE (toWord (wA B ℓ)),
    .const zN2 (toWord (2 ^ (h + 2)))]
  have hM8 := inv_sem I (P := .blk b9) (by simp +decide [b9, WF, Prim.dst, zA, zC, zE, zN2]) hM7
  have z8 := size_sem I (.blk b9) s7
  have hs7 := hM7.1; simp only [regs] at hs7
  have k8 : ∀ r, (256 ≤ r ∨ r = zP) → rd (semXIR I (.blk b9) s7).M r = rd s7.M r := fun r hr => by
    refine rdBlk_nw I _ _ ?_
    intro p' hp'; simp only [b9, List.mem_cons, List.mem_nil_iff, or_false] at hp'
    rcases hp' with rfl | rfl | rfl | rfl <;> simp only [Prim.dst] <;>
      rcases hr with hr | rfl <;> simp only [zA, zC, zE, zN2, zP] <;> first | decide | exact Nat.ne_of_lt (Nat.lt_of_lt_of_le (by decide) hr)
  have r8 : rd (semXIR I (.blk b9) s7).M zA = toWord (B + 4096 + 4 * 2 ^ ℓ + q) ∧
      rd (semXIR I (.blk b9) s7).M zC = toWord (B + 4096 + 7 * 2 ^ ℓ) ∧
      rd (semXIR I (.blk b9) s7).M zE = toWord (B + 4096 + 9 * 2 ^ ℓ) ∧
      rd (semXIR I (.blk b9) s7).M zN2 = toWord (2 * c) := by
    rw [semBlk]; simp only [b9, runPrims, List.foldl, Prim.run]
    refine ⟨?_, ?_, ?_, ?_⟩ <;>
    simp (disch := first | decide | ((try simp only [size_set]); refine Nat.lt_of_lt_of_le (m := 256) (by decide) ?_; first | assumption | omega)) only
      [rd_set_self, rd_set_ne] <;> (try simp only [xA, wA])
    · rw [zP7]; exact BitVec.or_self
    · rw [hc2]
  generalize semXIR I (.blk b9) s7 = s8 at hM8 z8 k8 r8
  have hE8 := hE7.trans_eq z8.symm
  obtain ⟨a8, c8, e8, n8⟩ := r8
  rw [semXIR_seq, show (2 : ℕ) ^ (h + 2) = 2 * c from hc2]
  obtain ⟨p9, f9, g9, hM9⟩ := prodLoop_sem I s8 hM8 (p0 := B + 4096 + 4 * 2 ^ ℓ + q)
    (x := B + 4096 + 7 * 2 ^ ℓ) (w := B + 4096 + 9 * 2 ^ ℓ) (c := 2 * c) hc64
    hR4 hR3 hR3
    ⟨pA264, pX64, pW64⟩ (le_trans pAE hE8) (Or.inl pA2X) (Or.inl pA2W) a8 c8 e8 n8
  have z9 := size_sem I (.loopK zC2 zN2 (toWord (2 * c)) prodBody) s8
  generalize semXIR I (.loopK zC2 zN2 (toWord (2 * c)) prodBody) s8 = s9 at p9 f9 g9 hM9 z9
  -- 11. the next parent
  set b10 : List Prim := [.const zD (toWord (2 * c)), .op .add zP zP zD]
  have hM10 := inv_sem I (P := .blk b10) (by simp +decide [b10, WF, Prim.dst, zD, zP]) hM9
  have k10 : ∀ r, 256 ≤ r → rd (semXIR I (.blk b10) s9).M r = rd s9.M r := fun r hr => by
    refine rdBlk_nw I _ _ ?_
    intro p' hp'; simp only [b10, List.mem_cons, List.mem_nil_iff, or_false] at hp'
    rcases hp' with rfl | rfl <;> simp only [Prim.dst, zD, zP] <;> first | decide | exact Nat.ne_of_lt (Nat.lt_of_lt_of_le (by decide) hr)
  have hs9 := hM9.1; simp only [regs] at hs9
  refine ⟨fun i hi => ?_, fun y hy hy2 => ?_, ?_, hM10⟩
  · rw [rdK_eq (k10 _ hR5), p9 i hi, rdK_eq (k8 _ (Or.inl hR4)),
      rdK_eq (k8 _ (Or.inl hR4)), xrow i hi, x4 i hi, x7 i hi]
    have hdiv : (q + i) / 2 ^ (h + 2) = p := by
      rw [hc2, hqdef, hc2, Nat.add_comm, Nat.add_mul_div_right _ _ (by positivity),
        Nat.div_eq_of_lt hi, Nat.zero_add]
    have hmod : (q + i) % 2 ^ (h + 2) = i := by
      rw [hc2, hqdef, hc2, Nat.add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hi]
    simp only [treeLevel, hdiv, hmod, ext, ← hqdef, ← hcdef]
  · simp only [regs] at hy
    have hy4 := hyW y hy2
    rw [k10 _ hy, f9 _ hy (hyA y hy2), k8 _ (Or.inl hy),
      f7 _ hy hy4, f6 _ hy (hy4.imp_right (le_trans (Nat.add_le_add_left hcc _))),
      back5 _ hy (hyX y hy2), y5 _ hy (hyXW y hy2), k0 _ (Or.inl hy)]
  · rw [semBlk]; simp only [b10, runPrims, List.foldl, Prim.run]
    simp (disch := first | decide | ((try simp only [size_set]); refine Nat.lt_of_lt_of_le (m := 256) (by decide) ?_; first | assumption | omega)) only
      [rd_set_self, rd_set_ne]
    rw [g9, k8 _ (Or.inr rfl), zP7, add_toWord]
    exact congrArg toWord (by ring)

/-! ## One tree level -/

theorem ext_congr (N h : ℕ) {A A' : ℕ → BF64} (hA : ∀ j < 2 ^ (h + 1), A j = A' j) :
    ext N h A = ext N h A' := by
  unfold ext
  congr 1
  funext i
  split_ifs with hi
  · rw [bflyRun_eq ptK N 0 (h + 1) A hi, bflyRun_eq ptK N 0 (h + 1) A' hi]
    exact coeffsAt_congr N (h + 1) 0 A A' hA i hi
  · rfl

theorem treeLevel_congr (N h p : ℕ) {T T' : ℕ → BF64}
    (hT : ∀ j < 2 ^ (h + 2), T (p * 2 ^ (h + 2) + j) = T' (p * 2 ^ (h + 2) + j)) {i : ℕ}
    (hi : i < 2 ^ (h + 2)) : treeLevel N h T (p * 2 ^ (h + 2) + i) = treeLevel N h T' (p * 2 ^ (h + 2) + i) := by
  have hc2 : 2 ^ (h + 2) = 2 * 2 ^ (h + 1) := by rw [pow_succ]; ring
  have hdiv : (p * 2 ^ (h + 2) + i) / 2 ^ (h + 2) = p := by
    rw [Nat.add_comm, Nat.add_mul_div_right _ _ (by positivity), Nat.div_eq_of_lt hi, Nat.zero_add]
  simp only [treeLevel, hdiv]
  rw [ext_congr N h (A := fun j => T (p * 2 ^ (h + 2) + j)) (A' := fun j => T' (p * 2 ^ (h + 2) + j))
      (fun j hj => hT j (by omega)),
    ext_congr N h (A := fun j => T (p * 2 ^ (h + 2) + 2 ^ (h + 1) + j))
      (A' := fun j => T' (p * 2 ^ (h + 2) + 2 ^ (h + 1) + j))
      (fun j hj => by rw [Nat.add_assoc]; exact hT _ (by omega))]

theorem tLevelIR_sem (I : Array Word) (s : St) (hM : Inv s.M) {N ℓ B h : ℕ}
    {Tf : ℕ → BF64} (hN : h + 2 ≤ N) (hN64 : N ≤ 64) (hh : h < ℓ) (hB : regs ≤ B)
    (hsz : fdEnd B ℓ ≤ s.M.size) (h64 : fdEnd B ℓ < 2 ^ 64)
    (hW : ∀ v < N, ∀ i < N, rdK s.M (tbA B + N * v + i) = (wRow ptK N v).getD i 0)
    (hT : ∀ i < 2 ^ (ℓ + 1), rdK s.M (tA B ℓ + i) = Tf i) :
    (∀ i < 2 ^ (ℓ + 1), rdK (semXIR I (tLevelIR N ℓ B h) s).M (tA B ℓ + i) = treeLevel N h Tf i) ∧
    (∀ y, regs ≤ y → (y < tA B ℓ ∨ (tA B ℓ + 2 ^ (ℓ + 1) ≤ y ∧ y < xA B ℓ) ∨ fdEnd B ℓ ≤ y) →
      rd (semXIR I (tLevelIR N ℓ B h) s).M y = rd s.M y) ∧
    Inv (semXIR I (tLevelIR N ℓ B h) s).M := by
  have hs := hM.1
  simp only [regs] at hs hB
  have hNN := NN_le hN64
  have hPP : 2 ^ (ℓ - h - 1) * 2 ^ (h + 2) = 2 ^ (ℓ + 1) := by
    rw [← pow_add]; exact congrArg (2 ^ ·) (by omega)
  have hn2 : 2 ^ (ℓ + 1) = 2 * 2 ^ ℓ := by rw [pow_succ]; ring
  simp only [fdEnd, tA, xA, tbA] at hsz h64 hW hT ⊢
  rw [tLevelIR, semXIR_seq]
  set b0 : List Prim := [.const zP (toWord (tA B ℓ)), .const zN1 (toWord (2 ^ (ℓ - h - 1)))]
  have hM0 := inv_sem I (P := .blk b0) (by simp +decide [b0, WF, Prim.dst, zP, zN1]) hM
  have z0 := size_sem I (.blk b0) s
  have k0 : ∀ r, 256 ≤ r → rd (semXIR I (.blk b0) s).M r = rd s.M r := fun r hr => by
    refine rdBlk_nw I _ s ?_
    intro p' hp'; simp only [b0, List.mem_cons, List.mem_nil_iff, or_false] at hp'
    rcases hp' with rfl | rfl <;> simp only [Prim.dst, zP, zN1] <;> first | decide | exact Nat.ne_of_lt (Nat.lt_of_lt_of_le (by decide) hr)
  have hPlt : 2 ^ (ℓ - h - 1) < 2 ^ 64 := by
    have : 2 ^ (ℓ - h - 1) ≤ 2 ^ (ℓ - h - 1) * 2 ^ (h + 2) := Nat.le_mul_of_pos_right _ (by positivity)
    omega
  have r0 : rd (semXIR I (.blk b0) s).M zP = toWord (B + 4096 + 4 * 2 ^ ℓ + 0 * 2 ^ (h + 2)) ∧
      rd (semXIR I (.blk b0) s).M zN1 = toWord (2 ^ (ℓ - h - 1)) := by
    rw [semBlk]; simp only [b0, runPrims, List.foldl, Prim.run]
    refine ⟨?_, ?_⟩ <;>
    simp (disch := first | decide | ((try simp only [size_set]); refine Nat.lt_of_lt_of_le (m := 256) (by decide) ?_; first | assumption | omega)) only
      [rd_set_self, rd_set_ne]
    simp [tA]
  generalize semXIR I (.blk b0) s = s0 at hM0 z0 k0 r0
  obtain ⟨p0, n0⟩ := r0
  let Tp : ℕ → ℕ → BF64 := fun p i => if i < p * 2 ^ (h + 2) then treeLevel N h Tf i else Tf i
  let R : ℕ → Mem → Prop := fun p M =>
    rd M zP = toWord (B + 4096 + 4 * 2 ^ ℓ + p * 2 ^ (h + 2)) ∧
    (∀ i < 2 ^ (ℓ + 1), rdK M (B + 4096 + 4 * 2 ^ ℓ + i) = Tp p i) ∧
    (∀ y, 256 ≤ y → (y < B + 4096 + 4 * 2 ^ ℓ ∨ (B + 4096 + 4 * 2 ^ ℓ + 2 ^ (ℓ + 1) ≤ y ∧
      y < B + 4096 + 7 * 2 ^ ℓ) ∨ B + 4096 + 11 * 2 ^ ℓ ≤ y) → rd M y = rd s.M y)
  have hR : ∀ j (M M' : Mem), (∀ i, i ≠ zC1 → i ≠ cTmp → rd M' i = rd M i) → R j M → R j M' := by
    rintro j M M' hMM ⟨r1, r2, r3⟩
    have hy : ∀ y, 256 ≤ y → y ≠ zC1 ∧ y ≠ cTmp := fun y hy => by simp only [zC1, cTmp]; (clear h64 hPlt; omega)
    refine ⟨by rw [hMM _ (by decide) (by decide), r1], fun i hi => ?_, fun y hy' hy2 => ?_⟩
    · rw [← r2 i hi]; have hv : 256 ≤ B + 4096 + 4 * 2 ^ ℓ + i :=
        Nat.le_add_right_of_le (Nat.le_add_right_of_le (Nat.le_add_right_of_le hB))
      exact rdK_eq (hMM _ (hy _ hv).1 (hy _ hv).2)
    · rw [hMM _ (hy _ hy').1 (hy _ hy').2, r3 y hy' hy2]
  have h0 : R 0 s0.M := ⟨p0, fun i hi => by
      simp only [Tp, Nat.zero_mul, Nat.not_lt_zero, if_false]
      rw [← hT i hi]; exact rdK_eq (k0 _ (Nat.le_add_right_of_le (Nat.le_add_right_of_le (Nat.le_add_right_of_le hB)))), fun y hy _ => k0 y hy⟩
  have hb : ∀ p (s' : St), p < 2 ^ (ℓ - h - 1) → Inv s'.M → s'.M.size = s0.M.size → R p s'.M →
      Inv (semXIR I (parentBody N ℓ B h) s').M ∧ R (p + 1) (semXIR I (parentBody N ℓ B h) s').M := by
    rintro p s' hp i1 i2 ⟨r1, r2, r3⟩
    have hp' : (p + 1) * 2 ^ (h + 2) ≤ 2 ^ (ℓ + 1) := by
      rw [← hPP]; exact Nat.mul_le_mul_right _ hp
    have hq : p * 2 ^ (h + 2) + 2 ^ (h + 2) ≤ 2 ^ (ℓ + 1) := by
      have := hp'; rw [Nat.add_mul, one_mul] at this; exact this
    obtain ⟨q1, q2, q3, q4⟩ := parentBody_sem I s' i1 (N := N) (ℓ := ℓ) (B := B) (h := h) (p := p)
      (Tf := Tp p) hN hN64 hh (by simp only [regs]; (clear h64 hPlt; omega))
      (by simp only [fdEnd]; (clear h64 hPlt; omega)) (by simp only [fdEnd]; omega) hp' (by simpa [tA] using r1)
      (fun v hv i hi => by
        have : N * v + i < 4096 := by
          have := Nat.mul_le_mul_left N (show v + 1 ≤ N by (clear h64 hPlt; omega)); rw [Nat.mul_succ] at this; (clear h64 hPlt; omega)
        rw [tbA, ← hW v hv i hi]; exact rdK_eq (r3 _ (by omega) (by (clear h64 hPlt; omega))))
      (fun i hi => by simpa [tA] using r2 i hi)
    simp only [tA, xA, fdEnd] at q1 q2 q3
    refine ⟨q4, by simpa using q3, fun i hi => ?_, fun y hy hy2 => ?_⟩
    · simp only [Tp]
      by_cases g1 : i < p * 2 ^ (h + 2)
      · rw [if_pos (Nat.lt_of_lt_of_le g1 (Nat.mul_le_mul_right _ (Nat.le_succ p))),
          rdK_eq (q2 _ (by simp only [regs]; (clear h64 hPlt; omega)) (Or.inl (by (clear h64 hPlt; omega)))), r2 i hi]
        simp only [Tp, if_pos g1]
      by_cases g2 : i < (p + 1) * 2 ^ (h + 2)
      · rw [if_pos g2]
        obtain ⟨j, rfl⟩ := Nat.exists_eq_add_of_le (not_lt.1 g1)
        have hj : j < 2 ^ (h + 2) := by rw [Nat.add_mul, one_mul] at g2; (clear h64 hPlt; omega)
        rw [← Nat.add_assoc, q1 j hj]
        refine treeLevel_congr N h p (fun j' hj' => ?_) hj
        simp only [Tp, if_neg (show ¬ (p * 2 ^ (h + 2) + j' < p * 2 ^ (h + 2)) by (clear h64 hPlt; omega))]
      · rw [if_neg g2, rdK_eq (q2 _ (by simp only [regs]; (clear h64 hPlt; omega)) (Or.inr (Or.inl ⟨by (clear h64 hPlt; omega), by (clear h64 hPlt; omega)⟩))),
          r2 i hi]
        simp only [Tp, if_neg g1]
    · rw [q2 y (by simp only [regs]; (clear h64 hPlt; omega)) (by
        rcases hy2 with h1 | ⟨h1, h2⟩ | h1
        · left; (clear h64 hPlt; omega)
        · right; left; constructor <;> (clear h64 hPlt; omega)
        · right; right; (clear h64 hPlt; omega)), r3 y hy hy2]
  have hfin := loopK_gen I (parentBody N ℓ B h) s0 hM0 (by decide) (by decide) (by decide) n0 hPlt R hR h0
    (fun j s' hj i1 i2 i3 => hb j s' hj i1 i2 i3)
  obtain ⟨⟨_, f2, f3⟩, f4, _⟩ := hfin
  refine ⟨fun i hi => ?_, fun y hy hy2 => ?_, f4⟩
  · rw [f2 i hi]; simp only [Tp, hPP, if_pos hi]
  · simp only [regs] at hy
    exact f3 y hy hy2

/-! ## The tree -/

theorem treeIR_sem (I : Array Word) {N ℓ B : ℕ} {S : List ℕ} (hN : ℓ + 1 ≤ N) (hN64 : N ≤ 64)
    (hB : regs ≤ B) : ∀ h ≤ ℓ, ∀ (s : St), Inv s.M → fdEnd B ℓ ≤ s.M.size → fdEnd B ℓ < 2 ^ 64 →
    (∀ v < N, ∀ i < N, rdK s.M (tbA B + N * v + i) = (wRow ptK N v).getD i 0) →
    (∀ i < 2 ^ (ℓ + 1), rdK s.M (tA B ℓ + i) = lam N S 0 i) →
    (∀ i < 2 ^ (ℓ + 1), rdK (semXIR I (treeIR N ℓ B h) s).M (tA B ℓ + i) = lam N S h i) ∧
    (∀ y, regs ≤ y → (y < tA B ℓ ∨ (tA B ℓ + 2 ^ (ℓ + 1) ≤ y ∧ y < xA B ℓ) ∨ fdEnd B ℓ ≤ y) →
      rd (semXIR I (treeIR N ℓ B h) s).M y = rd s.M y) ∧
    Inv (semXIR I (treeIR N ℓ B h) s).M ∧ (semXIR I (treeIR N ℓ B h) s).M.size = s.M.size
  | 0, _, s, hM, _, _, _, hT => ⟨hT, fun _ _ _ => rfl, hM, rfl⟩
  | h + 1, hh, s, hM, hsz, h64, hW, hT => by
    obtain ⟨t1, t2, t3, t4⟩ := treeIR_sem I hN hN64 hB h (by omega) s hM hsz h64 hW hT
    rw [treeIR, semXIR_seq]
    have hNN := NN_le hN64
    simp only [regs] at hB
    obtain ⟨u1, u2, u3⟩ := tLevelIR_sem I (semXIR I (treeIR N ℓ B h) s) t3 (N := N) (ℓ := ℓ) (B := B)
      (h := h) (Tf := lam N S h) (by omega) hN64 (by omega) (by simp only [regs]; omega)
      (by rw [t4]; exact hsz) h64
      (fun v hv i hi => by
        have : N * v + i < 4096 := by
          have := Nat.mul_le_mul_left N (show v + 1 ≤ N by omega); rw [Nat.mul_succ] at this; omega
        rw [← hW v hv i hi]
        exact rdK_eq (t2 _ (by simp only [regs, tbA]; omega) (Or.inl (by simp only [tbA, tA]; omega))))
      t1
    exact ⟨u1, fun y hy hy2 => (u2 y hy hy2).trans (t2 y hy hy2), u3, by rw [size_sem, t4]⟩

/-! ## `Λ⁻¹` on the coset -/

theorem invK_frame' (I : Array Word) (s : St) {d a i : ℕ} (hi : i < 5 ∨ 12 ≤ i) (hd : i ≠ d) :
    rd (semXIR I (invK d a) s).M i = rd s.M i := by
  rw [invK, sem_blk]; exact invKC_frame _ _ hi hd _

theorem invsIR_sem (I : Array Word) (s : St) (hM : Inv s.M) {ℓ B : ℕ} (hB : regs ≤ B)
    (hsz : fdEnd B ℓ ≤ s.M.size) (h64 : fdEnd B ℓ < 2 ^ 64) :
    (∀ j < 2 ^ ℓ, rdK (semXIR I (invsIR ℓ B) s).M (iA B ℓ + j) = (rdK s.M (tA B ℓ + 2 ^ ℓ + j))⁻¹) ∧
    (∀ y, regs ≤ y → (y < iA B ℓ ∨ iA B ℓ + 2 ^ ℓ ≤ y) → rd (semXIR I (invsIR ℓ B) s).M y = rd s.M y) ∧
    Inv (semXIR I (invsIR ℓ B) s).M := by
  have hs := hM.1
  simp only [regs] at hs hB
  simp only [fdEnd, tA, iA] at hsz h64 ⊢
  have hg : ∀ {u v : ℕ}, u < 256 → 256 ≤ v → v ≠ u := fun hu hv => Nat.ne_of_gt (Nat.lt_of_lt_of_le hu hv)
  have hR4 : ∀ {k1 k2 k3 : ℕ}, 256 ≤ B + k1 + k2 + k3 :=
    Nat.le_add_right_of_le (Nat.le_add_right_of_le (Nat.le_add_right_of_le hB))
  rw [invsIR, semXIR_seq]
  set b0 : List Prim := [.const zA (toWord (tA B ℓ + 2 ^ ℓ)), .const zB (toWord (iA B ℓ)),
    .const zN1 (toWord (2 ^ ℓ))]
  have hM0 := inv_sem I (P := .blk b0) (by simp +decide [b0, WF, Prim.dst, zA, zB, zN1]) hM
  have z0 := size_sem I (.blk b0) s
  have k0 : ∀ r, 256 ≤ r → rd (semXIR I (.blk b0) s).M r = rd s.M r := fun r hr => by
    refine rdBlk_nw I _ s ?_
    intro p' hp'; simp only [b0, List.mem_cons, List.mem_nil_iff, or_false] at hp'
    rcases hp' with rfl | rfl | rfl <;> simp only [Prim.dst, zA, zB, zN1] <;> first | decide | exact Nat.ne_of_lt (Nat.lt_of_lt_of_le (by decide) hr)
  have r0 : rd (semXIR I (.blk b0) s).M zA = toWord (B + 4096 + 4 * 2 ^ ℓ + 2 ^ ℓ + 0) ∧
      rd (semXIR I (.blk b0) s).M zB = toWord (B + 4096 + 6 * 2 ^ ℓ + 0) ∧
      rd (semXIR I (.blk b0) s).M zN1 = toWord (2 ^ ℓ) := by
    rw [semBlk]; simp only [b0, runPrims, List.foldl, Prim.run]
    refine ⟨?_, ?_, ?_⟩ <;>
    simp (disch := first | decide | ((try simp only [size_set]); refine Nat.lt_of_lt_of_le (m := 256) (by decide) ?_; first | assumption | omega)) only
      [rd_set_self, rd_set_ne] <;> simp [tA, iA]
  generalize semXIR I (.blk b0) s = s0 at hM0 z0 k0 r0
  obtain ⟨a0, b0', n0⟩ := r0
  let R : ℕ → Mem → Prop := fun j M => rd M zA = toWord (B + 4096 + 4 * 2 ^ ℓ + 2 ^ ℓ + j) ∧
    rd M zB = toWord (B + 4096 + 6 * 2 ^ ℓ + j) ∧
    (∀ i < j, rdK M (B + 4096 + 6 * 2 ^ ℓ + i) = (rdK s.M (B + 4096 + 4 * 2 ^ ℓ + 2 ^ ℓ + i))⁻¹) ∧
    (∀ y, 256 ≤ y → (y < B + 4096 + 6 * 2 ^ ℓ ∨ B + 4096 + 6 * 2 ^ ℓ + j ≤ y) → rd M y = rd s.M y)
  have hR : ∀ j (M M' : Mem), (∀ i, i ≠ zC1 → i ≠ cTmp → rd M' i = rd M i) → R j M → R j M' := by
    rintro j M M' hMM ⟨r1, r2, r3, r4⟩
    have hy : ∀ y, 256 ≤ y → y ≠ zC1 ∧ y ≠ cTmp := fun y hy => by simp only [zC1, cTmp]; (clear h64; omega)
    refine ⟨by rw [hMM _ (by decide) (by decide), r1], by rw [hMM _ (by decide) (by decide), r2],
      fun i hi => ?_, fun y hy' hy2 => ?_⟩
    · rw [← r3 i hi]; exact rdK_eq (hMM _ (hy _ hR4).1 (hy _ hR4).2)
    · rw [hMM _ (hy _ hy').1 (hy _ hy').2, r4 y hy' hy2]
  have h0 : R 0 s0.M := ⟨a0, b0', fun i hi => absurd hi (Nat.not_lt_zero i), fun y hy _ => k0 y hy⟩
  have hb : ∀ j (s' : St), j < 2 ^ ℓ → Inv s'.M → s'.M.size = s0.M.size → R j s'.M →
      Inv (semXIR I invBody s').M ∧ R (j + 1) (semXIR I invBody s').M := by
    rintro j s' hj i1 i2 ⟨r1, r2, r3, r4⟩
    have hs' := i1.1
    simp only [regs] at hs'
    rw [invBody, semXIR_seq]
    obtain ⟨l1, hM1⟩ := load_hp I s' i1 (d := zU) (p := zA) (by decide) (by decide) r1 (by omega)
    have z1 := size_sem I (.load zU zA) s'
    generalize semXIR I (.load zU zA) s' = s1 at l1 hM1 z1
    rw [semXIR_seq]
    have m2 := invK_sem (I := I) (s := s1) hM1 (d := zW) (a := zU) (by decide) (by decide)
    have f2 : ∀ i, (i < 5 ∨ 12 ≤ i) → i ≠ zW → rd (semXIR I (invK zW zU) s1).M i = rd s1.M i :=
      fun i h1 h2 => invK_frame' I s1 h1 h2
    have hM2 := inv_sem I (wf_invK zW zU (by decide)) hM1
    have z2 := size_sem I (invK zW zU) s1
    generalize semXIR I (invK zW zU) s1 = s2 at m2 f2 hM2 z2
    rw [semXIR_seq]
    obtain ⟨c3, hM3⟩ := store_hp I s2 hM2 (p := zB) (v := zW) (by decide) (by decide)
      (by rw [f2 _ (by decide) (by decide), l1, if_neg (by decide), r2])
      (hR4 : 256 ≤ B + 4096 + 6 * 2 ^ ℓ + j) (by omega) (by (clear h64; omega))
    have z3 := size_sem I (.store zB zW) s2
    generalize semXIR I (.store zB zW) s2 = s3 at c3 hM3 z3
    set b4 : List Prim := [.op .add zA zA cOne, .op .add zB zB cOne]
    have hM4 := inv_sem I (P := .blk b4) (by simp +decide [b4, WF, Prim.dst, zA, zB]) hM3
    have e4 : ∀ i, i ≠ zA → i ≠ zB → rd (semXIR I (.blk b4) s3).M i = rd s3.M i :=
      fun i h1 h2 => rdBlk_nw I _ _ (by
        intro p hp; simp only [b4, List.mem_cons, List.mem_nil_iff, or_false] at hp
        rcases hp with rfl | rfl <;> simp only [Prim.dst] <;>
          first | exact Ne.symm h1 | exact Ne.symm h2)
    have hz3 := hM3.1; simp only [regs] at hz3
    have hone : rd s3.M cOne = 1 := hM3.2 0 (by decide)
    have reg3 : ∀ r, r < 256 → 12 ≤ r → r ≠ zU → r ≠ zW → rd s3.M r = rd s'.M r :=
      fun r hr h0 h1 h2 => by
        rw [c3 r (by simp only [cTmp]; (clear h64; omega)), if_neg (Nat.ne_of_lt (Nat.lt_of_lt_of_le hr hR4)), f2 r (Or.inr h0) h2, l1, if_neg h1]
    have heap3 : ∀ y, 256 ≤ y → rd s3.M y =
        if y = B + 4096 + 6 * 2 ^ ℓ + j then rd s2.M zW else rd s'.M y := fun y hy => by
      rw [c3 y (hg (by decide) hy)]
      split_ifs
      · rfl
      · rw [f2 y (Or.inr (Nat.le_trans (by decide) hy)) (hg (by decide) hy), l1, if_neg (hg (by decide) hy)]
    have val : rdK s2.M zW = (rdK s.M (B + 4096 + 4 * 2 ^ ℓ + 2 ^ ℓ + j))⁻¹ := by
      rw [m2, rdK, l1, if_pos rfl, r4 _ (by omega) (by (clear h64; omega))]; rfl
    refine ⟨hM4, ?_, ?_, fun i hi => ?_, fun y hy hy2 => ?_⟩
    · rw [semBlk]; simp only [b4, runPrims, List.foldl, Prim.run]
      simp (disch := first | decide | ((try simp only [size_set]); refine Nat.lt_of_lt_of_le (m := 256) (by decide) ?_; first | assumption | omega)) only
        [rd_set_self, rd_set_ne]
      rw [reg3 _ (by decide) (by decide) (by decide) (by decide), r1, hone, add_one_toWord, Nat.add_assoc]
    · rw [semBlk]; simp only [b4, runPrims, List.foldl, Prim.run]
      simp (disch := first | decide | ((try simp only [size_set]); refine Nat.lt_of_lt_of_le (m := 256) (by decide) ?_; first | assumption | omega)) only
        [rd_set_self, rd_set_ne]
      rw [reg3 _ (by decide) (by decide) (by decide) (by decide), r2, hone, add_one_toWord, Nat.add_assoc]
    · rw [rdK_eq (e4 _ (hg (by decide) hR4) (hg (by decide) hR4)), rdK, heap3 _ hR4]
      by_cases g : i = j
      · subst g; rw [if_pos rfl, ← val]; rfl
      · rw [if_neg (by (clear h64; omega))]; exact r3 i (by (clear h64; omega))
    · rw [e4 _ (hg (by decide) hy) (hg (by decide) hy), heap3 _ hy, if_neg (by (clear h64; omega)),
        r4 y hy (by (clear h64; omega))]
  have hfin := loopK_gen I invBody s0 hM0 (by decide) (by decide) (by decide) n0 (by omega) R hR h0
    (fun j s' hj i1 i2 i3 => hb j s' hj i1 i2 i3)
  obtain ⟨⟨_, _, f3, f4⟩, f5, _⟩ := hfin
  exact ⟨fun j hj => f3 j hj, fun y hy hy2 => by simp only [regs] at hy; exact f4 y hy hy2, f5⟩

/-! ## The output tape -/

/-- Does the program contain an output statement? -/
def hasOutF : XIR → Bool
  | .out _ => true
  | .seq p q => hasOutF p || hasOutF q
  | .ite _ p q => hasOutF p || hasOutF q
  | .loopK _ _ _ b => hasOutF b
  | .loopT _ _ _ b => hasOutF b
  | _ => false

theorem iterL_oF {f : St → St} {c : ℕ} (hf : ∀ s, (f s).o = s.o) :
    ∀ k s, (iterL f c k s).o = s.o
  | 0, _ => rfl
  | k + 1, s => (iterL_oF hf k _).trans (hf s)

/-- A program without output statements leaves the output unchanged. -/
theorem sem_oF (I : Array Word) : ∀ (P : XIR) (s : St), hasOutF P = false → (semXIR I P s).o = s.o
  | .blk _, _, _ => rfl
  | .load .., _, _ => rfl
  | .store .., _, _ => rfl
  | .input .., _, _ => rfl
  | .out _, _, h => by simp [hasOutF] at h
  | .seq p q, s, h => by
    simp only [hasOutF, Bool.or_eq_false_iff] at h
    rw [semXIR_seq, sem_oF I q _ h.2, sem_oF I p s h.1]
  | .ite c p q, s, h => by
    simp only [hasOutF, Bool.or_eq_false_iff] at h
    rw [semXIR_ite]; split
    · exact sem_oF I q s h.2
    · exact sem_oF I p s h.1
  | .loopK c n K b, s, h => by
    simp only [semXIR]; exact iterL_oF (fun s' => sem_oF I b s' h) _ _
  | .loopT c n cap b, s, h => by
    simp only [semXIR]; exact iterL_oF (fun s' => sem_oF I b s' h) _ _

theorem hasOutF_treeIR (N ℓ B : ℕ) : ∀ h, hasOutF (treeIR N ℓ B h) = false
  | 0 => rfl
  | h + 1 => by
    simp [treeIR, hasOutF, hasOutF_treeIR N ℓ B h, tLevelIR, parentBody, copyBody, prodBody, mulK,
      bflyNIR, lvlNStep, levelNIR, pairNBody, alphaNIR, alphaBody, arithIR, addK, fwdNIR, fStepN,
      flevelNIR, fpairNBody, farithIR]

theorem lamIR_o (I : Array Word) (N ℓ m B : ℕ) (s : St) : (semXIR I (lamIR N ℓ m B) s).o = s.o := by
  refine sem_oF I _ s ?_
  simp [lamIR, hasOutF, hasOutF_treeIR, wtabNIR, row0NIR, row0Body, rowNIR, rowNBody, mulK, invK,
    leavesIR, leafBody, dummiesIR, dummyBody, invsIR, invBody]

/-! ## `lamIR` -/

/-- **`lamIR_sem`**: after `lamIR`, the basis table, `S`, `Λ` on `ptK [0, 2^(ℓ+1))` and `Λ⁻¹` on the
coset are in place (`LamOk`); `S`, `y` and the lane workspace are untouched. -/
theorem lamIR_sem (I : Array Word) (s : St) (hM : Inv s.M) {N ℓ B : ℕ} {S : List ℕ}
    (hN : ℓ + 1 ≤ N) (hN64 : N ≤ 64) (hB : regs ≤ B) (hsz : fdEnd B ℓ ≤ s.M.size)
    (h64 : fdEnd B ℓ < 2 ^ 64) (hm : S.length ≤ 2 ^ ℓ) (hSn : ∀ j ∈ S, j < 2 ^ ℓ)
    (hS : ∀ i < S.length, rd s.M (sA B + i) = toWord (S.getD i 0)) :
    LamOk N ℓ B S (semXIR I (lamIR N ℓ S.length B) s).M ∧ Inv (semXIR I (lamIR N ℓ S.length B) s).M ∧
    (semXIR I (lamIR N ℓ S.length B) s).o = s.o ∧
    ∀ x, regs ≤ x → (x < B ∨ (sA B ≤ x ∧ x < tA B ℓ) ∨ fdEnd B ℓ ≤ x) →
      rd (semXIR I (lamIR N ℓ S.length B) s).M x = rd s.M x := by
  have hs := hM.1
  have hB' := hB
  simp only [regs] at hs hB'
  have hNN := NN_le hN64
  have hN1 : 1 ≤ N := by (clear h64; omega)
  have hn2 : 2 ^ (ℓ + 1) = 2 * 2 ^ ℓ := by rw [pow_succ]; ring
  have hfd : fdEnd B ℓ = B + 4096 + 11 * 2 ^ ℓ := rfl
  have hto := lamIR_o I N ℓ S.length B s
  refine (fun (h : _ ∧ _ ∧ _) => ⟨h.1, h.2.1, hto, h.2.2⟩) ?_
  rw [lamIR, semXIR_seq]; (try rw [semXIR_seq]); (try rw [semXIR_seq]); (try rw [semXIR_seq])
  all_goals
    obtain ⟨w1, w2, w3, w4⟩ := wtabNIR_sem I s hM hN64 hN1 (tb := tbA B) hB (by simp only [tbA]; omega)
      (by simp only [tbA]; omega)
    generalize semXIR I (wtabNIR N (tbA B)) s = s1 at w1 w2 w3 w4
    obtain ⟨l1, l2, l3⟩ := leavesIR_sem I s1 w3 hB (by rw [w4]; exact hsz) h64
    have z2 := size_sem I (leavesIR ℓ B) s1
    generalize semXIR I (leavesIR ℓ B) s1 = s2 at l1 l2 l3 z2
    have hS2 : ∀ i < S.length, rd s2.M (sA B + i) = toWord (S.getD i 0) := fun i hi => by
      rw [l2 _ (by simp only [regs, sA]; (clear h64; omega)) (Or.inl (by simp only [sA, tA]; (clear h64; omega))),
        w2 _ (by simp only [regs, sA]; (clear h64; omega)) (Or.inr (by simp only [sA, tbA]; (clear h64; omega))), hS i hi]
    obtain ⟨d1, d2, d3⟩ := dummiesIR_sem I s2 l3 hB (by rw [z2, w4]; exact hsz) h64 hm hSn hS2 l1
    have z3 := size_sem I (dummiesIR ℓ S.length B) s2
    generalize semXIR I (dummiesIR ℓ S.length B) s2 = s3 at d1 d2 d3 z3
    have tb3 : ∀ v < N, ∀ i < N, rdK s3.M (tbA B + N * v + i) = (wRow ptK N v).getD i 0 :=
      fun v hv i hi => by
        have : N * v + i < 4096 := by
          have := Nat.mul_le_mul_left N (show v + 1 ≤ N by (clear h64; omega)); rw [Nat.mul_succ] at this; (clear h64; omega)
        rw [rdK_eq (d2 _ (by simp only [regs, tbA]; (clear h64; omega)) (Or.inl (by simp only [tbA, tA]; (clear h64; omega)))),
          rdK_eq (l2 _ (by simp only [regs, tbA]; (clear h64; omega)) (Or.inl (by simp only [tbA, tA]; (clear h64; omega)))),
          w1 v hv i hi]
    obtain ⟨t1, t2, t3, t4⟩ := treeIR_sem I (S := S) hN hN64 hB ℓ le_rfl s3 d3
      (by rw [z3, z2, w4]; exact hsz) h64 tb3 (fun i hi => by rw [d1 i hi]; rfl)
    generalize semXIR I (treeIR N ℓ B ℓ) s3 = s4 at t1 t2 t3 t4
    obtain ⟨v1, v2, v3⟩ := invsIR_sem I s4 t3 hB (by rw [t4, z3, z2, w4]; exact hsz) h64
  refine ⟨?_, ?_, ?_⟩
  · -- `LamOk`
    refine ⟨fun v hv i hi => ?_, fun i hi => ?_, fun i hi => ?_, fun j hj => ?_⟩
    · have : N * v + i < 4096 := by
        have := Nat.mul_le_mul_left N (show v + 1 ≤ N by (clear h64; omega)); rw [Nat.mul_succ] at this; (clear h64; omega)
      rw [rdK_eq (v2 _ (by simp only [regs, tbA]; (clear h64; omega)) (Or.inl (by simp only [tbA, iA]; (clear h64; omega)))),
        rdK_eq (t2 _ (by simp only [regs, tbA]; (clear h64; omega)) (Or.inl (by simp only [tbA, tA]; (clear h64; omega)))),
        tb3 v hv i hi]
    · rw [v2 _ (by simp only [regs, sA]; (clear h64; omega)) (Or.inl (by simp only [sA, iA]; (clear h64; omega))),
        t2 _ (by simp only [regs, sA]; (clear h64; omega)) (Or.inl (by simp only [sA, tA]; (clear h64; omega))),
        d2 _ (by simp only [regs, sA]; (clear h64; omega)) (Or.inl (by simp only [sA, tA]; (clear h64; omega))), hS2 i hi]
    · rw [rdK_eq (v2 _ (by simp only [regs, tA]; (clear h64; omega)) (Or.inl (by simp only [tA, iA]; (clear h64; omega)))), t1 i hi]
    · rw [v1 j hj, show tA B ℓ + 2 ^ ℓ + j = tA B ℓ + (2 ^ ℓ + j) by ring, t1 _ (by (clear h64; omega))]
  · exact v3
  · intro x hx hx2
    simp only [regs] at hx
    have hx3 : x < tbA B ∨ tbA B + N * N ≤ x := by
      rcases hx2 with h1 | h1 | h1
      · left; simp only [tbA]; (clear h64; omega)
      · right; simp only [tbA, sA] at *; (clear h64; omega)
      · right; simp only [tbA, fdEnd] at *; (clear h64; omega)
    rw [v2 x (by simp only [regs]; (clear h64; omega)) (by simp only [iA, sA, tA, fdEnd] at *; (clear h64; omega)),
      t2 x (by simp only [regs]; (clear h64; omega)) (by simp only [xA, sA, tA, fdEnd] at *; (clear h64; omega)),
      d2 x (by simp only [regs]; (clear h64; omega)) (by simp only [sA, tA, fdEnd] at *; (clear h64; omega)),
      l2 x (by simp only [regs]; (clear h64; omega)) (by simp only [sA, tA, fdEnd] at *; (clear h64; omega)),
      w2 x (by simp only [regs]; (clear h64; omega)) hx3]

end Lvm6.FD

