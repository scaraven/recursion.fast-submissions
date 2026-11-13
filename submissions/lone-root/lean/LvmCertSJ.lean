-- New for lvm2 (R5-CERT, roll 5): design-independent numerics for the J2′ certificate (`C_rec` at the Johnson
-- radius, `cfgRec20Jp`); J2C-A moved the front end's bounds to `LvmCertSMid2`/`LvmCertSMid3`.
import LvmCertSMid3
import LvmWhirDoomJ2

/-!
# J2′ numerics: the front end at `L₀ = 124·304` and the fold luck over lists

* `l0J2_eq`: `L₀ = 37,696 = 124·304`. J2C-A moved `kg_errsJ2` (`LvmCertSMid2`), `LkSJ` and `bus_errsJ2`
  (`LvmCertSMid3`) to the front end's modules, where they replaced the `L₀ = 98` bounds: at J2′ `candPairs` is at
  the Johnson `thrRec` (`candPairs_ncard_le`: `≤ 37,696`). `bus_errsJ2` needs `I.B ≤ 2^48` (`MidHyp.cons`).
* **`card_luckL_snoc_le`**, **`ten_δLJ_le`**: the extractor's fold luck over Johnson lists (`card_luck_snoc_le`
  with the list bound `L`): at most `L·n` challenges per round; with `L ≤ 311`, `n ≤ 2^15` and ten rounds the
  total is `10·311·2^15/|E| ≤ 2^-132` (in fact `2^-165.4`; JB-L's `luckL_rec20Jp` has the exact sum).
-/

set_option autoImplicit false

namespace Lvm.ASM

open LeanVM.Parameters LeanVM.Protocol LeanVM.Protocol.Compile LeanVM.Protocol.Verifier
open LeanVM.Protocol.Compile.VerifierProgram LeanVM.Protocol.Whir.Sound LeanVM.Protocol.EndToEnd
open LeanVM.Protocol.EndToEnd.Front LeanVM.Protocol.KeccakGkr
open Lvm.VEq Lvm.KG Lvm.M3
open scoped ENNReal NNReal

/-! ## The front end at `L₀ = 124·304` -/

/-- `124·304`: J2′'s candidate pairs (`candPairsJ_ncard_le`; the front end's `kg_errsJ2`, `LkSJ`, `bus_errsJ2`
are in `LvmCertSMid2`/`LvmCertSMid3`, where `specKgS` and `specBusA` use them). -/
theorem l0J2_eq : (37696 : ℕ) = 124 * 304 := rfl

/-! ## The fold luck over lists -/

open Classical in
/-- **A round's luck over a list of at most `L` members** on at most `2^15` columns: at most `L·2^15` challenges
(`card_luck_snoc_le`, generic in the list bound). -/
theorem card_luckL_snoc_le {ι : Type} [Fintype ι] {k L : ℕ} (hι : Fintype.card ι ≤ 2 ^ 15)
    (Λ : Finset ((Fin k → Bool) → ι → E)) (hΛ : Λ.card ≤ L) (O : (Fin k → Bool) → ι → E) (α : List E)
    (hα : α.length < k) (hn : ¬ ∃ V ∈ Λ, RoundsLuck k α O V) :
    (Finset.univ.filter fun c : E ↦ ∃ V ∈ Λ, RoundsLuck k (α ++ [c]) O V).card ≤ L * 2 ^ 15 :=
  (card_luck_snoc_le Λ hΛ O α hα hn).trans (Nat.mul_le_mul_left L hι)

/-- The per-round fold luck of J2′'s extractor over the lists (`L ≤ 311` at both `C_rec` levels, `n ≤ 2^15`). -/
noncomputable def δLJ : ℝ≥0∞ := ((311 * 2 ^ 15 : ℕ) : ℝ≥0∞) / Fintype.card E

/-- **Ten rounds of list luck fit the luck budget**: `10·311·2^15/|E| ≤ 2^-132`. -/
theorem ten_δLJ_le : (10 : ℝ≥0∞) * δLJ ≤ (2 : ℝ≥0∞)⁻¹ ^ 132 := by
  rw [δLJ, card_E_ennreal, ← mul_div_assoc, ← two_pow_cast 192,
    show (10 : ℝ≥0∞) * ((311 * 2 ^ 15 : ℕ) : ℝ≥0∞) = ((10 * (311 * 2 ^ 15) : ℕ) : ℝ≥0∞) by push_cast; ring]
  exact natCast_div_le_inv_pow (by positivity) (by norm_num)

end Lvm.ASM
