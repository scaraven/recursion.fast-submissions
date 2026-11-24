-- lvm6 A2: the generic part of `LvmCertSNo` (season 1's `P_S` group error `εS = 7·2^-131` and the commitment
-- count `CommitsN`), cut verbatim out of it so that the Keccak GKR caller specs (`LvmE2VGkrSpec`, `LvmE2VSpecTape`)
-- build without season 1's `P_S` (whose `LvmCertS` half is parked).
import LvmCertSFrame

set_option autoImplicit false

namespace Lvm.ASM

open scoped NNReal ENNReal

/-- The per-group error of `P_S` (lvm2 JB-VQP, J1: the exact budget, JB-L §1): `7·2^-131 = 2^-128 − 2^-131`.
`C_main`'s Johnson query groups reach `2^-128.30`; the luck (`2^-132`) and the hash term (`2^-139`) fit the
margin `2^-131`. Every other group is at most `2^-129` (`pow129_le_εS`). -/
noncomputable abbrev εS : ℝ≥0∞ := 7 * (2 : ℝ≥0∞)⁻¹ ^ 131

theorem inv_pow_131_ne_top : (2 : ℝ≥0∞)⁻¹ ^ 131 ≠ ⊤ :=
  ENNReal.pow_ne_top (ENNReal.inv_ne_top.mpr two_ne_zero)

theorem inv_pow_add2 (k : ℕ) : (2 : ℝ≥0∞)⁻¹ ^ k = (2 : ℝ≥0∞)⁻¹ ^ (k + 2) * 4 := by
  rw [pow_add, mul_assoc, show (4 : ℝ≥0∞) = 2 ^ 2 by norm_num, ← mul_pow,
    ENNReal.inv_mul_cancel two_ne_zero ENNReal.ofNat_ne_top, one_pow, mul_one]

/-- Every group bounded by `2^-129` is within `εS`. -/
theorem pow129_le_εS : (2 : ℝ≥0∞)⁻¹ ^ 129 ≤ εS := by
  rw [inv_pow_add2 129]
  show (2 : ℝ≥0∞)⁻¹ ^ 131 * 4 ≤ 7 * (2 : ℝ≥0∞)⁻¹ ^ 131
  rw [mul_comm]
  exact mul_le_mul' (by norm_num) le_rfl

/-- `2^-128 = 7·2^-131 + 2^-131`. -/
theorem inv_pow_128_eq : (2 : ℝ≥0∞)⁻¹ ^ 128 = 7 * (2 : ℝ≥0∞)⁻¹ ^ 131 + (2 : ℝ≥0∞)⁻¹ ^ 131 := by
  rw [inv_pow_add2 128, inv_pow_add2 130, show 128 + 2 + 2 = 131 + 1 from rfl]
  rw [show (2 : ℝ≥0∞)⁻¹ ^ (131 + 1) * 4 * 4 = (2 : ℝ≥0∞)⁻¹ ^ (131 + 1) * 2 * 8 by ring,
    pow_succ, mul_assoc ((2 : ℝ≥0∞)⁻¹ ^ 131), ENNReal.inv_mul_cancel two_ne_zero ENNReal.ofNat_ne_top]
  ring

/-- `x + 2^-131 ≤ 2^-128` gives `x ≤ εS` (JB-L's margin form of the Johnson groups). -/
theorem le_εS_of_margin {x : ℝ≥0∞} (h : x + (2 : ℝ≥0∞)⁻¹ ^ 131 ≤ (2 : ℝ≥0∞)⁻¹ ^ 128) : x ≤ εS := by
  rw [inv_pow_128_eq] at h
  exact (ENNReal.add_le_add_iff_right inv_pow_131_ne_top).1 h

theorem εS_le_128 : εS ≤ (2 : ℝ≥0∞)⁻¹ ^ 128 := le_self_add.trans_eq inv_pow_128_eq.symm

end Lvm.ASM

namespace LeanVM.Protocol.Compile.VerifierProgram

variable {α β : Type}

/-- **Every completed run of `p` commits exactly `n` words.** -/
def CommitsN : VerifierProgram α → ℕ → Prop
  | .ret _, n => n = 0
  | .fail, _ => True
  | .read k, n => ∀ x, CommitsN (k x) n
  | .sample k, n => ∀ c, CommitsN (k c) n
  | .grind _ k, n => CommitsN k n
  | .commit _ _ _, 0 => False
  | .commit _ _ k, n + 1 => CommitsN k n
  | .query _ _ k, n => ∀ r, CommitsN (k r) n

theorem CommitsN.bind {p : VerifierProgram α} {f : α → VerifierProgram β} {m n : ℕ}
    (hp : p.CommitsN m) (hf : ∀ a, (f a).CommitsN n) : (p.bind f).CommitsN (m + n) := by
  induction p generalizing m with
  | ret a =>
    have hm : m = 0 := hp
    subst hm; rw [Nat.zero_add]; exact hf a
  | fail => trivial
  | read k ih => exact fun x ↦ ih x (hp x)
  | sample k ih => exact fun c ↦ ih c (hp c)
  | grind b k ih => exact ih hp
  | commit ht w k ih =>
    cases m with
    | zero => exact hp.elim
    | succ m =>
      rw [show m + 1 + n = (m + n) + 1 by omega]
      exact ih hp
  | query i ps k ih => exact fun r ↦ ih r (hp r)

theorem CommitsN.bind' {p : VerifierProgram α} {f : α → VerifierProgram β} {m n k : ℕ}
    (hp : p.CommitsN m) (hf : ∀ a, (f a).CommitsN n) (hk : m + n = k) : (p.bind f).CommitsN k :=
  hk ▸ CommitsN.bind hp hf

theorem CommitsN.of_noCommit {p : VerifierProgram α} (hp : p.NoCommit) : p.CommitsN 0 := by
  induction p with
  | ret a => rfl
  | fail => trivial
  | read k ih => exact fun x ↦ ih x (hp x)
  | sample k ih => exact fun c ↦ ih c (hp c)
  | grind b k ih => exact ih hp
  | commit ht w k ih => exact (hp : False).elim
  | query i ps k ih => exact fun r ↦ ih r (hp r)

/-- **A completed run of `p` commits `n` words.** -/
theorem CommitsN.after_ret {p : VerifierProgram α} {n : ℕ} {l : List Ev} {a : α}
    (hp : p.CommitsN n) (h : p.after l = some (.ret a)) : (commits l).length = n := by
  induction l generalizing p n with
  | nil =>
    simp only [VerifierProgram.after, Option.some.injEq] at h
    subst h
    exact (hp : n = 0).symm
  | cons e es ih =>
    cases p <;> cases e <;> simp only [VerifierProgram.after, reduceCtorEq] at h
    · exact ih (hp _) h
    · exact ih (hp _) h
    · split_ifs at h
      refine ih ?_ h; exact hp
    · split_ifs at h
      cases n with
      | zero => exact (hp : False).elim
      | succ n =>
        simp only [commits, List.length_cons, Nat.add_right_cancel_iff]
        refine ih ?_ h; exact hp
    · exact ih (hp _) h

end LeanVM.Protocol.Compile.VerifierProgram
