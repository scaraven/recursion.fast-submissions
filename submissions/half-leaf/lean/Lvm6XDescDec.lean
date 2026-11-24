-- lvm6 X6b (X4 §4 item 6, X6b §3 item 4): the level-0 map. X's novel basis at `ptK` is W1's (`novelX_ptK`,
-- `novM_eq_novelF`); the low message of a polynomial given by novel-basis coefficients below `2^(κ+1)` is its
-- coefficients below `2^κ` (`lowMsgF_sum_novelF`); hence W1's `decD` of a decoded tuple reads its coefficients
-- (`decD_of_rep`). The program `fin` (`finIR`): the 34 slot copies to the stack at `colB6`, with its semantics
-- (`finIR_sem`, `finIR_heapHolds`) and budget (`finIR_part`). New.
import Lvm6XDescLoad
import Lvm6WhirOpen
import Lvm6XExt

/-!
# The level-0 map `fin`

* **`normW_ptK`**, **`novelX_ptK`**: `Ŵ_v` and `X_x` at `ptK` (X's `bitProd (normW ptK)`) are leanVM's
  `normVanishing v`, `novel x` (W1's basis), for `x < 2^64`; **`novM_eq_novelF`** over any `F`.
* **`novel_two_pow_add`**: `X_{2^κ + y} = X_y · Ŵ_κ` (`y < 2^κ`); **`novelF_two_pow_add`**: `= W_κ · (c · X_y)`.
* **`lowMsgF_sum_novelF`**: for `m ≤ 2^κ`, `lowMsgF κ (Σ_{x < 2^κ + m} c_x X_x) u = c_{⟨u⟩}`.
* **`decD_of_rep`**: if `Tc` holds the coefficients of `U` (`RepT (2^18 − 1 + 6)`, `P17`), `decD U x` is the `K` part
  of `Tc` at lane `x[18..24)` and row `x[0..18)`.
* **`finIR src`**: slot `m < 34` (`2^18` words at `P17`) from `src m` to `colB6 + m·2^18` (`mcpIR`); **`finIR_heapHolds`**:
  when the sources hold the stack `q`'s slots, the heap holds `q` from `colB6` (X5's `HeapHolds`).
-/

set_option autoImplicit false

namespace Lvm6.X

open RecursionFast Polynomial Finset Lvm.Nb Lvm.X LeanVM.Parameters LeanVM.Protocol.Whir

/-! ## The two novel bases -/

theorem subW_ptK (v : ℕ) : subW ptK v = vanishing v := by
  rw [subW, vanishing]
  refine Finset.prod_congr rfl fun a _ ↦ ?_
  rw [sub_eq_add_neg, ← C_neg, CharTwo.neg_eq]
  rfl

theorem normW_ptK (v : ℕ) : Lvm.Nb.normW ptK v = normVanishing v := by
  rw [Lvm.Nb.normW, normVanishing, subW_ptK]
  congr 3
  rw [vanishing, eval_prod, vanishingAt]
  refine Finset.prod_congr rfl fun a _ ↦ ?_
  simp only [eval_add, eval_X, eval_C]
  rfl

/-- **X's novel basis at `ptK` is leanVM's.** -/
theorem novelX_ptK {x : ℕ} (hx : x < 2 ^ 64) : novelX ptK x = novel x := by
  rw [novelX_eq_bitProd ptK hx, bitProd, bitSel, novel]
  refine Finset.prod_congr rfl fun i _ ↦ ?_
  split_ifs
  · exact normW_ptK i
  · rfl

/-- **X4's `novM ptK` is W1's `novelF`.** -/
theorem novM_eq_novelF {F : Type} [Field F] [Algebra K F] {x : ℕ} (hx : x < 2 ^ 64) :
    (novM ptK x : F[X]) = Lvm6.Whir.novelF x := by
  rw [novM, novelX_ptK hx]

theorem novel_two_pow_add {κ y : ℕ} (hκ : κ < 64) (hy : y < 2 ^ κ) :
    novel (2 ^ κ + y) = novel y * normVanishing κ := by
  have hyκ : y.testBit κ = false := Nat.testBit_lt_two_pow hy
  have hb : ∀ i, i ≠ κ → (2 ^ κ + y).testBit i = y.testBit i := by
    intro i hi
    rcases Nat.lt_or_gt_of_ne hi with h | h
    · exact Nat.testBit_two_pow_add_gt h y
    · have h2 : 2 ^ (κ + 1) ≤ 2 ^ i := Nat.pow_le_pow_right (by norm_num) h
      rw [pow_succ] at h2
      have h3 : y < 2 ^ i := by omega
      rw [Nat.testBit_lt_two_pow (show 2 ^ κ + y < 2 ^ i by omega), Nat.testBit_lt_two_pow h3]
  have hk : (2 ^ κ + y).testBit κ = true := by rw [Nat.testBit_two_pow_add_eq, hyκ]; rfl
  rw [novel, novel, ← Finset.mul_prod_erase _ _ (mem_range.2 hκ),
    ← Finset.mul_prod_erase (range 64) _ (mem_range.2 hκ), if_pos hk, hyκ, if_neg Bool.false_ne_true, one_mul,
    mul_comm]
  congr 1
  exact Finset.prod_congr rfl fun i hi ↦ by rw [hb i (Finset.ne_of_mem_erase hi)]

section Msg

variable {F : Type} [Field F] [Algebra K F]

theorem novelF_two_pow_add {κ y : ℕ} (hκ : κ < 64) (hy : y < 2 ^ κ) :
    (Lvm6.Whir.novelF (2 ^ κ + y) : F[X]) =
      Lvm6.Whir.vanF κ * (C (algebraMap K F (vanishingAt κ (basisVec κ))⁻¹) * Lvm6.Whir.novelF y) := by
  simp only [Lvm6.Whir.novelF, Lvm6.Whir.vanF, novel_two_pow_add hκ hy, normVanishing, Polynomial.map_mul,
    Polynomial.map_C]
  ring

/-- **The low message of a polynomial in the novel basis**: its coefficients below `2^κ`. -/
theorem lowMsgF_sum_novelF {κ m : ℕ} (hκ : κ < 64) (hm : m ≤ 2 ^ κ) (c : ℕ → F) (u : Fin κ → Bool) :
    Lvm6.Whir.lowMsgF κ (∑ x ∈ range (2 ^ κ + m), C (c x) * Lvm6.Whir.novelF x) u = c (bitsToNat u) := by
  rw [Finset.sum_range_add]
  have hlow : ∑ x ∈ range (2 ^ κ), C (c x) * (Lvm6.Whir.novelF x : F[X]) =
      Lvm6.Whir.msgPolyF κ (fun v ↦ c (bitsToNat v)) := by
    show _ = ∑ v, c (bitsToNat v) • Lvm6.Whir.novelF (bitsToNat v)
    rw [← Fin.sum_univ_eq_sum_range (fun x ↦ C (c x) * (Lvm6.Whir.novelF x : F[X])),
      ← (bitsEquiv κ).sum_comp]
    exact Finset.sum_congr rfl fun v _ ↦ by rw [bitsEquiv_val, Polynomial.smul_eq_C_mul]
  have hhigh : ∑ x ∈ range m, C (c (2 ^ κ + x)) * (Lvm6.Whir.novelF (2 ^ κ + x) : F[X]) =
      Lvm6.Whir.vanF κ * ∑ x ∈ range m, C (c (2 ^ κ + x)) *
        (C (algebraMap K F (vanishingAt κ (basisVec κ))⁻¹) * Lvm6.Whir.novelF x) := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun x hx ↦ ?_
    rw [novelF_two_pow_add hκ (lt_of_lt_of_le (mem_range.1 hx) hm)]
    ring
  rw [hlow, hhigh, Lvm6.Whir.lowMsgF_msgPolyF_add hκ.le]

end Msg

/-- **W1's `decD` of a decoded level-0 tuple** reads its novel-basis coefficients. -/
theorem decD_of_rep {Tc : CT E2 (0 + 6)} {U : Lvm6.Whir.Tup E2 (0 + 6)} (hR : RepT (2 ^ 18 - 1 + 6) Tc U)
    (x : ℕ) : Lvm6.Whir.decD U x =
      (Tc (fun i ↦ x.testBit (18 + i)) (bitsToNat fun i : Fin 18 ↦ x.testBit i)).re := by
  have hR' : ∀ u, U u = ∑ j : Fin (2 ^ 18 - 1 + 6 + 1), C (Tc u j) * (novM ptK j : E2[X]) := hR
  set u : Fin (0 + 6) → Bool := fun i ↦ x.testBit (18 + i)
  have hs : ∑ j ∈ range (2 ^ 18 + 6), C (Tc u j) * (novM ptK j : E2[X]) =
      ∑ j ∈ range (2 ^ 18 + 6), C (Tc u j) * Lvm6.Whir.novelF j :=
    Finset.sum_congr rfl fun j hj ↦ by
      rw [novM_eq_novelF (F := E2) (lt_of_lt_of_le (mem_range.1 hj) (by norm_num))]
  simp only [Lvm6.Whir.decD]
  rw [hR' u, Fin.sum_univ_eq_sum_range (fun j : ℕ ↦ C (Tc u j) * (novM ptK j : E2[X])) (2 ^ 18 - 1 + 6 + 1),
    show 2 ^ 18 - 1 + 6 + 1 = 2 ^ 18 + 6 by norm_num, hs, lowMsgF_sum_novelF (by norm_num) (by norm_num)]

/-! ## The program -/

/-- **`fin`**: slots `0 … k − 1`, slot `m` (`2^18` words at `P17`) from `src m` to `colB6 + m·2^18`. -/
def finIR (src : ℕ → ℕ) : ℕ → XIR
  | 0 => .blk []
  | k + 1 => .seq (finIR src k) (mcpIR stride6 (src k) 1 (colB6 + k * stride6))

theorem finIR_part (src : ℕ → ℕ) : ∀ k, k ≤ 34 → PartOk (finIR src k) (k * (17 + 13 * stride6) + 1)
  | 0, _ => ⟨by simp [finIR, WF], by simp [finIR, NoLoopT], fun _ ↦ by simp [finIR, outs],
      fun _ ↦ by simp [finIR, cost, blkSteps]⟩
  | k + 1, hk => by
    have ih := finIR_part src k (by omega)
    refine ⟨⟨ih.wf, wf_mcpIR ..⟩, ⟨ih.noLoopT, noLoopT_mcpIR ..⟩, fun t ↦ ?_, fun t ↦ ?_⟩
    · simp only [finIR, outs, ih.outs, outs_mcpIR, Nat.add_zero]
    · have h1 := ih.cost t
      simp only [finIR, cost, cost_mcpIR _ _ _ _ t (show stride6 < 2 ^ 64 by simp only [stride6]; norm_num)]
      nlinarith

/-- **`fin` within `finCap`.** -/
theorem finIR_part34 (src : ℕ → ℕ) : PartOk (finIR src 34) finCap := by
  obtain ⟨a, b, c, d⟩ := finIR_part src 34 le_rfl
  exact ⟨a, b, c, fun t ↦ (d t).trans (by simp only [stride6, finCap]; norm_num)⟩

/-- **The slot copies on the machine**: the sources lie outside the stack and stay below `2^64`. -/
theorem finIR_sem (I : Array Word) (src : ℕ → ℕ)
    (hsrc : ∀ m < 34, regs ≤ src m ∧ src m + stride6 < 2 ^ 64 ∧
      (src m + stride6 ≤ colB6 ∨ colB6 + 34 * stride6 ≤ src m)) :
    ∀ k ≤ 34, ∀ s : St, Inv s.M → colB6 + 34 * stride6 ≤ s.M.size →
      (∀ m < k, ∀ r < stride6, rd (semXIR I (finIR src k) s).M (colB6 + m * stride6 + r) = rd s.M (src m + r)) ∧
      (∀ x, regs ≤ x → (x < colB6 ∨ colB6 + k * stride6 ≤ x) → rd (semXIR I (finIR src k) s).M x = rd s.M x) ∧
      Inv (semXIR I (finIR src k) s).M ∧ (semXIR I (finIR src k) s).o = s.o
  | 0, _, s, hM, _ => by
    have e : semXIR I (finIR src 0) s = s := by simp [finIR, semXIR, runPrims]
    rw [e]
    exact ⟨fun _ h ↦ absurd h (Nat.not_lt_zero _), fun _ _ _ ↦ rfl, hM, rfl⟩
  | k + 1, hk, s, hM, hsz => by
    obtain ⟨a1, a2, a3, a4⟩ := finIR_sem I src hsrc k (by omega) s hM hsz
    obtain ⟨r1, r2, r3⟩ := hsrc k (by omega)
    have z1 := size_sem I (finIR src k) s
    have eS : stride6 = 262144 := rfl
    have eC : colB6 = 67108864 := rfl
    have hk1 : k * stride6 + stride6 ≤ 34 * stride6 := by
      have := Nat.mul_le_mul_right stride6 hk; rwa [Nat.add_mul, Nat.one_mul] at this
    simp only [finIR, semXIR_seq]
    generalize semXIR I (finIR src k) s = s1 at a1 a2 a3 a4 z1
    obtain ⟨c1, c2, c3⟩ := mcpIR_sem I s1 a3 (n := stride6) (src := src k) (str := 1)
      (dst := colB6 + k * stride6) (by rw [eS]; norm_num) (by omega) (by norm_num) (by simp only [regs]; omega)
      (by omega) (by omega) (fun i hi ↦ by omega) (fun i _ ↦ by omega)
    have c4 := sem_o I (mcpIR stride6 (src k) 1 (colB6 + k * stride6)) s1 (hasOut_mcpIR _ _ _ _)
    refine ⟨fun m hm r hr ↦ ?_, fun x hx hx' ↦ ?_, c3, c4.trans a4⟩
    · rcases Nat.lt_succ_iff_lt_or_eq.1 hm with hm | rfl
      · have hmk : (m + 1) * stride6 ≤ k * stride6 := Nat.mul_le_mul_right _ hm
        rw [Nat.add_mul, Nat.one_mul] at hmk
        rw [c2 _ (by simp only [regs]; omega) (Or.inl (by omega)), a1 m hm r hr]
      · rw [c1 r hr, Nat.one_mul, a2 _ (by omega) (by omega)]
    · rw [c2 x hx (by rw [Nat.add_mul, Nat.one_mul] at hx'; omega),
        a2 x hx (by rw [Nat.add_mul, Nat.one_mul] at hx'; omega)]

/-- **`fin` puts the stack `q` at `colB6`** when slot `m`'s source holds `q`'s slot `m`. -/
theorem finIR_heapHolds (I : Array Word) (src : ℕ → ℕ)
    (hsrc : ∀ m < 34, regs ≤ src m ∧ src m + stride6 < 2 ^ 64 ∧
      (src m + stride6 ≤ colB6 ∨ colB6 + 34 * stride6 ≤ src m))
    (s : St) (hM : Inv s.M) (hsz : colB6 + 34 * stride6 ≤ s.M.size) (q : Stack)
    (hq : ∀ m < 34, ∀ r < stride6, rd s.M (src m + r) = stW q (m * stride6 + r)) :
    HeapHolds (semXIR I (finIR src 34) s).M q := by
  obtain ⟨a1, -, -, -⟩ := finIR_sem I src hsrc 34 le_rfl s hM hsz
  intro w hw
  have hs : 0 < stride6 := by simp only [stride6]; norm_num
  have hm : w / stride6 < 34 := (Nat.div_lt_iff_lt_mul hs).2 hw
  have hw' : w = w / stride6 * stride6 + w % stride6 := by
    rw [Nat.mul_comm]; exact (Nat.div_add_mod w stride6).symm
  rw [hw', ← Nat.add_assoc, a1 _ hm _ (Nat.mod_lt _ hs), hq _ hm _ (Nat.mod_lt _ hs)]

end Lvm6.X
