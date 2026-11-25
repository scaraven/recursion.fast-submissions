-- New for lvm6 K0: the Keccak layer's pack and segment rounds in leanVM's normalized form (leanVM #767,
-- `41e89f2e5`), ported from leanVM formal `Protocol/Verifier/KeccakPack.lean` (`keccakPackRounds`,
-- `sumcheck_eq_keccakPackRounds`) at `fdb317982` onto season 1's `E2` DSL (`LvmE2VSample`, `LvmE2TSum`).
import LvmE2TSum

/-!
# Normalized pack rounds at `E2`

A pack round (`crates/verifier/src/keccak.rs:162-163`, `transcript.rs:216-266`) reads the round polynomial
`q` in equality mode (`roundPolyE2 3 value (some r)`: `[c1, c2]` read, `c0 = value + r·(c1 + c2)`), draws a
ground challenge `c`, and keeps `q(c)` as the next value. Season 1's `packRoundsE2` multiplied that value by
`1 + r + c` and carried the product of those factors (`scale`); since leanVM #767 there is no factor.

* **`packRoundsN`**: the rounds, the value first (`keccakPackRounds`);
* **`sumcheckE2_eq_packRoundsN`**: they are the plain `sumcheckE2` in equality mode, count 3
  (`sumcheck_eq_keccakPackRounds`);
* **`packRoundGN`**: their doom rule, from doom of `value = Fm q acc` to doom of `value' = Fm q (acc ++ point)`,
  each challenge escaping at `L₀ · errG g d`;
* `EqFamilyF.mono`: a larger degree bound (the layer keeps season 1's group `errG gC3 3`).
-/

set_option autoImplicit false

namespace Lvm6.KPack

open LeanVM.Parameters LeanVM.Protocol.Compile LeanVM.Protocol.Verifier LeanVM.Protocol.EndToEnd.Front
open Lvm.E2V Lvm.E2T
open scoped ENNReal

/-! ## The program -/

/-- **The pack and segment rounds, normalized** (`keccakPackRounds`): an equality-mode round per
coordinate of the claim's point, each keeping the round polynomial's value at the challenge. The final
value and the challenges. -/
def packRoundsN (g : ℕ) : List E2 → E2 → VerifierProgram (E2 × List E2)
  | [], value => pure (value, [])
  | r :: rs, value =>
    roundPolyE2 3 value (some r) >>= fun msg ↦ e2Sample g >>= fun c ↦
      packRoundsN g rs (polyEvalF msg c) >>= fun res ↦ pure (res.1, c :: res.2)

/-- **The rounds are the equality-mode sumcheck** of count 3 (`sumcheck_eq_keccakPackRounds`). -/
theorem sumcheckE2_eq_packRoundsN (g : ℕ) :
    ∀ (rs : List E2) (value : E2),
      sumcheckE2 g value 3 (rs.map some) = packRoundsN g rs value >>= fun res ↦ pure (res.2, res.1)
  | [], _ => rfl
  | r :: rs, value => by
    show (roundPolyE2 3 value (some r) >>= fun msg ↦ e2Sample g >>= fun c ↦
        sumcheckE2 g (polyEvalF msg c) 3 (rs.map some) >>= fun res ↦ pure (c :: res.1, res.2)) = _
    simp only [sumcheckE2_eq_packRoundsN g rs, packRoundsN, bind, VerifierProgram.bind_assoc]
    rfl

/-! ## The doom rule -/

/-- A larger degree bound keeps an equality family. -/
theorem EqFamilyF.mono {F : Type} [Field F] {β : Type} {Fm : β → List F → F} {r : List F} {d d' : ℕ}
    (hF : EqFamilyF Fm r d) (hd : d ≤ d') : EqFamilyF Fm r d' :=
  fun q acc h ↦ ⟨(hF q acc h).1.mono hd, (hF q acc h).2⟩

section Doom

variable {β : Type} {C : List Ev → Set β} [Finite β] {L₀ : ℕ} {εmax T : ℝ≥0∞}

/-- The witness of `packRoundGN` (`eqSumcheckGSpec` at count 3, on `packRoundsN`'s result order). -/
noncomputable def packGNSpec (hst : Stable C) (hcard : ∀ h, (C h).ncard ≤ L₀) (R : β → Prop)
    {Fm : β → List E2 → E2} {r : List E2} {d : ℕ} (hF : EqFamilyF Fm r d) (hd : 2 ≤ d) {g : ℕ}
    (hg : g ≤ 64) (he : (L₀ : ℝ≥0∞) * errG g d + T ≤ εmax) :
    (rs acc : List E2) → (value : E2) → rs = r.drop acc.length →
      Spec (packRoundsN g rs value)
        (Doomed C (fun q ↦ value = Fm q acc ∧ R q))
        (fun res h ↦ res.2.length = rs.length ∧
          Doomed C (fun q ↦ res.1 = Fm q (acc ++ res.2) ∧ R q) h) εmax T T
  | [], acc, value, _ =>
    (Spec.ret (Post := fun (res : E2 × List E2) h ↦ res.2.length = 0 ∧
        Doomed C (fun q ↦ res.1 = Fm q (acc ++ res.2) ∧ R q) h) (value, [])).mono
      (fun _ h ↦ ⟨rfl, by simpa using h⟩) (fun _ _ h ↦ h) le_rfl le_rfl le_rfl
  | rk :: rs, acc, value, hrs => by
    have hlt : acc.length < r.length := by
      by_contra h
      rw [List.drop_eq_nil_of_le (by omega)] at hrs
      exact List.cons_ne_nil _ _ hrs
    have hrk : r[acc.length] = rk := by
      have := congrArg List.head? hrs
      rw [List.head?_drop, List.getElem?_eq_getElem hlt] at this
      simpa using this.symm
    refine ((roundSpecE2 (T := 0) hst _ zero_le 3 (by norm_num) value (some rk)).mono
      (fun _ h ↦ h) (fun msg h (hm : msg.length = 3 ∧ _ ∧ _) ↦ hm) le_rfl zero_le
      le_rfl).bind' fun msg ↦ ?_
    by_cases hm : msg.length = 3
    · refine ((doomE2SampleSpec (εmax := εmax) (T := T) hst hcard
        (fun q ↦ (∀ x, polyEvalF msg x = Fm q (acc ++ [x])) ∧ R q)
        (fun y q ↦ polyEvalF msg y = Fm q (acc ++ [y]) ∧ R q) (errG g d)
        (fun q hq ↦ eqfG_escape hg hF R hlt (by omega) q hq) he).mono
          (fun h (hh : msg.length = 3 ∧
              RoundSplitF (some rk) value (polyEvalF msg 0) (polyEvalF msg 1) ∧
              Doomed C (fun q ↦ value = Fm q acc ∧ R q) h) ↦
            Doomed.mono hh.2.2 fun q ⟨hall, hR⟩ ↦ ⟨by
              have hs := hh.2.1
              rw [RoundSplitF, hall, hall, ← hrk] at hs
              rw [← hs, (hF q acc hlt).2], hR⟩)
          (fun _ _ h ↦ h) le_rfl le_rfl le_rfl).bind' fun c ↦ ?_
      refine (packGNSpec hst hcard R hF hd hg he rs (acc ++ [c]) (polyEvalF msg c) ?_).bind'
        fun res ↦ ?_
      · rw [List.length_append, List.length_singleton, ← List.drop_drop, ← hrs]
        rfl
      · exact (Spec.ret (res.1, c :: res.2)).mono
          (fun _ h ↦ ⟨by simp [h.1], by simpa using h.2⟩) (fun _ _ h ↦ h) le_rfl le_rfl le_rfl
    · exact Spec.dead.mono (fun _ h ↦ hm h.1) (fun _ _ h ↦ h) le_rfl le_rfl le_rfl

/-- **The normalized pack rounds' doom rule** (the twin of season 1's `packRoundG` without `scale`), at the
point `r` with `rs = r.drop acc.length` left: from doom of `value = Fm q acc` to doom of
`value' = Fm q (acc ++ point)`; each ground challenge escapes at `L₀ · 2^-g · d / 2^128`. Lead `T`. -/
theorem packRoundGN (hst : Stable C) (hcard : ∀ h, (C h).ncard ≤ L₀) (R : β → Prop)
    {Fm : β → List E2 → E2} {r : List E2} {d : ℕ} (hF : EqFamilyF Fm r d) (hd : 2 ≤ d) {g : ℕ}
    (hg : g ≤ 64) (he : (L₀ : ℝ≥0∞) * errG g d + T ≤ εmax)
    (rs acc : List E2) (value : E2) (hrs : rs = r.drop acc.length) :
    Nonempty (Spec (packRoundsN g rs value)
      (Doomed C (fun q ↦ value = Fm q acc ∧ R q))
      (fun res h ↦ res.2.length = rs.length ∧
        Doomed C (fun q ↦ res.1 = Fm q (acc ++ res.2) ∧ R q) h) εmax T T) :=
  ⟨packGNSpec hst hcard R hF hd hg he rs acc value hrs⟩

end Doom

end Lvm6.KPack
