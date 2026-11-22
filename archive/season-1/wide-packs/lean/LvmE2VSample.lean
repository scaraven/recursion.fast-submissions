-- New for lvm2 S1 (E2-F, E2F-V), E2AC-DES §6 statements 4 and 5: the `E2` front's reads and ground challenges
-- (`e2Read`, `e2Sample`), their doom rules (`doomE2Sample`, `coordG`) and the grinding twins of the
-- sumcheck-round rules (`sumcheckRoundG`, `packRoundG`).
import LvmE2VBaseLemmas
import LvmKeccakRounds

/-!
# Reads and ground challenges at `E2`

The verifier language reads and samples `E` (24 B) values. The `E2` front (frozen transcript S2GF):
* **`e2Read`**: a 16-B scalar; in the language a read whose lanes 0–1 are the value (`e2OfE`);
* **`e2Sample g`** (statement 4): the challenge's own 8-B nonce (a read, so every ground challenge
  is its own group), the answer `c`, the proof of work `powOK g c` (lane 2 `< 2^(64−g)`), the value
  `e2OfE c`;
* `e2Sep`: the separator (one sample, value discarded), before the first `E2` nonce and after `U`.

**Escapes.** `errG g d = 2^-g · d / 2^128` (`grpEpsE L₀ d g = L₀ · errG g d`):
* **`sampleG_escape`**: two distinct `E2` polynomials of degree `≤ d` agree at an accepted
  challenge with probability `≤ errG g d` (from `sz_escape_grind`);
* **`doomE2Sample`**: the doom rule of one ground challenge, lead `0` (the nonce is a move), the
  group's escape `L₀ · e + T ≤ εmax`;
* **`coordG`** (statement 5): `n + 1` ground coordinates in a row (`r`, lanes, instance, `ρ`, `λ`);
* **`sumcheckRoundG`**, **`packRoundG`** (statement 5): plain and equality-mode rounds at `E2`, each
  challenge at `L₀ · errG g d` (`L₀ · errG g (d + 1)`), the twins of `sumcheckSpec`/`packSpec`.
-/

set_option autoImplicit false

namespace Lvm.E2V

open LeanVM.Parameters LeanVM.Protocol.Compile LeanVM.Protocol.Verifier LeanVM.Protocol.EndToEnd.Front
open Polynomial
open scoped ENNReal

/-! ## The programs -/

/-- **An `E2` scalar** (16 B): lanes 0–1 of a read. -/
def e2Read : VerifierProgram E2 := VerifierProgram.readScalar >>= fun x ↦ pure (e2OfE x)

/-- `n` `E2` scalars. -/
def e2Reads : ℕ → VerifierProgram (List E2)
  | 0 => pure []
  | n + 1 => e2Read >>= fun x ↦ e2Reads n >>= fun xs ↦ pure (x :: xs)

/-- **Statement 4: a ground `E2` challenge** with `g` bits of proof of work: its nonce (one read),
the answer `c`, `powOK g c`, the value `e2OfE c`. -/
def e2Sample (g : ℕ) : VerifierProgram E2 :=
  VerifierProgram.readScalar >>= fun _ ↦ VerifierProgram.sampleChallenge >>= fun c ↦
    VerifierProgram.require (powOK g c) >>= fun _ ↦ pure (e2OfE c)

/-- `n` ground challenges in a row, each with its own nonce (S2GF: consecutive challenges such as the
coordinates of `r` each take a nonce, E2-G0 §1.2). -/
def e2Samples (g : ℕ) : ℕ → VerifierProgram (List E2)
  | 0 => pure []
  | n + 1 => e2Sample g >>= fun x ↦ e2Samples g n >>= fun xs ↦ pure (x :: xs)

/-- **The separator**: one sample, its value discarded (S2GF: before the first `E2` nonce, after `U`). -/
def e2Sep : VerifierProgram Unit := VerifierProgram.sampleChallenge >>= fun _ ↦ pure ()

/-- A round's message at `E2` (`sumcheckRoundPoly`): plain mode reads `c₀` and `count − 2` more, the
linear coefficient derived; equality mode reads `count − 1`, the constant derived. -/
def roundPolyE2 (count : ℕ) (claim : E2) : Option E2 → VerifierProgram (List E2)
  | none => e2Read >>= fun c0 ↦ e2Reads (count - 2) >>= fun tail ↦
      pure (c0 :: (claim + sumF tail) :: tail)
  | some r => e2Reads (count - 1) >>= fun tail ↦ pure ((claim + r * sumF tail) :: tail)

/-- **The sumcheck at `E2`** (`sumcheck`): per round the message, then a ground challenge (`g` bits). -/
def sumcheckE2 (g : ℕ) (claim : E2) (count : ℕ) : List (Option E2) → VerifierProgram (List E2 × E2)
  | [] => pure ([], claim)
  | mode :: modes =>
    roundPolyE2 count claim mode >>= fun msg ↦ e2Sample g >>= fun c ↦
      sumcheckE2 g (polyEvalF msg c) count modes >>= fun res ↦ pure (c :: res.1, res.2)

/-- **The equality-mode rounds at `E2`** (`keccakPackRounds`): the value scaled by `1 + r + c`. -/
def packRoundsE2 (g : ℕ) : List E2 → E2 → E2 → VerifierProgram (E2 × E2 × List E2)
  | [], value, scale => pure (value, scale, [])
  | r :: rs, value, scale =>
    roundPolyE2 3 value (some r) >>= fun msg ↦ e2Sample g >>= fun c ↦
      packRoundsE2 g rs ((1 + r + c) * polyEvalF msg c) (scale * (1 + r + c)) >>= fun res ↦
        pure (res.1, res.2.1, c :: res.2.2)

/-! ## Escapes -/

/-- **A ground group's per-candidate unit**: `2^-g · d / 2^128`. -/
noncomputable def errG (g d : ℕ) : ℝ≥0∞ := (2 : ℝ≥0∞)⁻¹ ^ g * (d * ((2 : ℝ≥0∞) ^ 128)⁻¹)

/-- `L₀ · errG g c` is E2-S's table entry `grpEpsE L₀ c g`. -/
theorem errG_grpEpsE (L₀ g c : ℕ) : (L₀ : ℝ≥0∞) * errG g c = grpEpsE L₀ c g := rfl

/-- **Statement 4 (`sampleG_escape`)**: two distinct `E2` polynomials of degree `≤ d` agree at an
accepted challenge with probability `≤ 2^-g · d / 2^128` (the joint probability over `E`). -/
theorem sampleG_escape {g : ℕ} (hg : g ≤ 64) {p q : E2[X]} (hne : p ≠ q) {d : ℕ}
    (hp : p.natDegree ≤ d) (hq : q.natDegree ≤ d) :
    avgE (fun c ↦ indE (powOK g c ∧ p.eval (e2OfE c) = q.eval (e2OfE c))) ≤ errG g d := by
  have hsub : p - q ≠ 0 := sub_ne_zero.2 hne
  have hdeg : (p - q).natDegree ≤ d := (natDegree_sub_le p q).trans (max_le hp hq)
  refine (avgE_mono fun c ↦ indE_mono fun hc ↦ ⟨hc.1, ?_⟩).trans (sz_escape_grind hg hsub hdeg)
  rw [eval_sub, sub_eq_zero]
  exact hc.2

/-- A message that agrees with a polynomial function of degree `≤ d` everywhere, and the escape of
its ground challenge when it does not (the twin of `msg_escape`): `w · msg` against `w · f`. -/
theorem msgG_escape {g : ℕ} (hg : g ≤ 64) {msg : List E2} {d : ℕ} (hd : msg.length - 1 ≤ d)
    {f : E2 → E2} (hf : PolyLEF d f) (hne : ¬ ∀ x, polyEvalF msg x = f x) (w : E2 → E2) {k : ℕ}
    (hw : PolyLEF k w) (hw0 : ∃ x, w x ≠ 0) :
    avgE (fun c ↦ indE (powOK g c ∧
      w (e2OfE c) * polyEvalF msg (e2OfE c) = w (e2OfE c) * f (e2OfE c))) ≤ errG g (d + k) := by
  obtain ⟨P, hP, hfP⟩ := hf
  obtain ⟨Q, hQ, hwQ⟩ := hw
  have hQ0 : Q ≠ 0 := by
    rintro rfl
    obtain ⟨x, hx⟩ := hw0
    exact hx (by simp [hwQ])
  have hne' : listPolyF msg ≠ P := by
    rintro h
    exact hne fun x ↦ by rw [← eval_listPolyF, h, hfP]
  have hne'' : Q * listPolyF msg ≠ Q * P := fun h ↦ hne' (mul_left_cancel₀ hQ0 h)
  have h1 : (Q * listPolyF msg).natDegree ≤ d + k :=
    natDegree_mul_le.trans (by have := natDegree_listPolyF msg; (clear * - Q msg d k g hd P hQ this; omega))
  have h2 : (Q * P).natDegree ≤ d + k := natDegree_mul_le.trans (by (clear * - Q P d k g msg hP hQ; omega))
  refine (avgE_mono fun c ↦ indE_mono fun hc ↦ ⟨hc.1, ?_⟩).trans (sampleG_escape hg hne'' h1 h2)
  rw [eval_mul, eval_mul, eval_listPolyF, ← hwQ, ← hfP]; exact hc.2

/-- The escape of a plain round's ground challenge (the twin of `plain_escape`). -/
theorem plainG_escape {g : ℕ} (hg : g ≤ 64) {β : Type} {Fm : β → List E2 → E2} {d N : ℕ}
    (hF : PlainFamilyF Fm d N) (R : β → Prop) {acc msg : List E2} (hacc : acc.length < N)
    (hd : msg.length - 1 ≤ d) (q : β) (hq : ¬ ((∀ x, polyEvalF msg x = Fm q (acc ++ [x])) ∧ R q)) :
    avgE (fun c ↦ indE (powOK g c ∧
      (polyEvalF msg (e2OfE c) = Fm q (acc ++ [e2OfE c]) ∧ R q))) ≤ errG g d := by
  by_cases hR : R q
  · have hne : ¬ ∀ x, polyEvalF msg x = Fm q (acc ++ [x]) := fun h ↦ hq ⟨h, hR⟩
    refine (avgE_mono fun c ↦ indE_mono fun hc ↦ ⟨hc.1, ?_⟩).trans
      (msgG_escape hg hd (hF q acc hacc).1 hne (fun _ ↦ 1) (PolyLEF.const 0 1) ⟨0, one_ne_zero⟩)
    simp only [one_mul]
    exact hc.2.1
  · refine (avgE_mono fun c ↦ indE_mono (q := False) fun h ↦ hR h.2.2).trans ?_
    exact (avgE_le_of_le fun c ↦ (indE_of_not not_false).le).trans zero_le

/-- The escape of an equality-mode round's ground challenge (the twin of `eq_escape`): the value
`(1 + r + c)·msg(c)` against `(1 + r + c)·scale·Fm(acc ++ [c])`, degree `d + 1`. -/
theorem eqG_escape {g : ℕ} (hg : g ≤ 64) {β : Type} {Fm : β → List E2 → E2} {r : List E2} {d : ℕ}
    (hF : EqFamilyF Fm r d) (R : β → Prop) {acc msg : List E2} (hacc : acc.length < r.length)
    (hd : msg.length - 1 ≤ d) (scale : E2) (q : β)
    (hq : ¬ ((∀ x, polyEvalF msg x = scale * Fm q (acc ++ [x])) ∧ R q)) :
    avgE (fun c ↦ indE (powOK g c ∧ ((1 + r[acc.length] + e2OfE c) * polyEvalF msg (e2OfE c) =
      (scale * (1 + r[acc.length] + e2OfE c)) * Fm q (acc ++ [e2OfE c]) ∧ R q))) ≤
      errG g (d + 1) := by
  by_cases hR : R q
  · have hne : ¬ ∀ x, polyEvalF msg x = scale * Fm q (acc ++ [x]) := fun h ↦ hq ⟨h, hR⟩
    refine (avgE_mono fun c ↦ indE_mono fun hc ↦ ⟨hc.1, ?_⟩).trans
      (msgG_escape hg hd (PolyLEF.const_mul (hF q acc hacc).1 scale) hne
        (fun c ↦ 1 + r[acc.length] + c) ((PolyLEF.affine (1 + r[acc.length]) 1).congr
          fun x ↦ by ring) ⟨r[acc.length], by
            rw [add_assoc, CharTwo.add_self_eq_zero, add_zero]; exact one_ne_zero⟩)
    rw [hc.2.1]; ring
  · refine (avgE_mono fun c ↦ indE_mono (q := False) fun h ↦ hR h.2.2).trans ?_
    exact (avgE_le_of_le fun c ↦ (indE_of_not not_false).le).trans zero_le

section Reads

variable {β : Type} {C : List Ev → Set β} {εmax T : ℝ≥0∞}

/-- An `E2` scalar keeps doom. -/
noncomputable def e2ReadSpec (hst : Stable C) (A : β → Prop) (hT : T ≤ εmax) :
    Spec e2Read (Doomed C A) (fun _ h ↦ Doomed C A h) εmax 0 T :=
  (doomRead hst A hT).bind' fun x ↦ Spec.ret (Post := fun _ h ↦ Doomed C A h) (e2OfE x)

/-- `n + 1` `E2` scalars keep doom; lead `0`. -/
noncomputable def e2ReadsSpec (hst : Stable C) (A : β → Prop) (hT : T ≤ εmax) :
    (n : ℕ) → Spec (e2Reads (n + 1)) (Doomed C A)
      (fun xs h ↦ xs.length = n + 1 ∧ Doomed C A h) εmax 0 T
  | 0 => (e2ReadSpec hst A hT).bind' fun x ↦
      (Spec.ret (Post := fun xs h ↦ xs = [] ∧ Doomed C A h) []).mono
        (fun _ hd ↦ ⟨rfl, hd⟩) (fun _ _ h ↦ h) le_rfl le_rfl le_rfl |>.bind' fun xs ↦
          (Spec.ret (x :: xs)).mono (fun _ h ↦ ⟨by simp [h.1], h.2⟩) (fun _ _ h ↦ h) le_rfl
            le_rfl le_rfl
  | n + 1 => (e2ReadSpec (T := 0) hst A zero_le).bind' fun x ↦
        (e2ReadsSpec hst A hT n).bind' fun xs ↦
          (Spec.ret (x :: xs)).mono (fun _ h ↦ ⟨by simp [h.1], h.2⟩) (fun _ _ h ↦ h) le_rfl
            le_rfl le_rfl

/-- `n` `E2` scalars keep doom; lead `T`. -/
noncomputable def e2ReadsSpecT (hst : Stable C) (A : β → Prop) (hT : T ≤ εmax) :
    (n : ℕ) → Spec (e2Reads n) (Doomed C A) (fun xs h ↦ xs.length = n ∧ Doomed C A h) εmax T T
  | 0 => (Spec.ret (Post := fun xs h ↦ xs.length = 0 ∧ Doomed C A h) []).mono
      (fun _ h ↦ ⟨rfl, h⟩) (fun _ _ h ↦ h) le_rfl le_rfl le_rfl
  | n + 1 => (e2ReadsSpec hst A hT n).mono (fun _ h ↦ h) (fun _ _ h ↦ h) le_rfl zero_le le_rfl

/-- **A round's message at `E2`** (the twin of `roundSpec`): the reads keep doom and the message
passes the round's check. Lead `0`. -/
noncomputable def roundSpecE2 (hst : Stable C) (A : β → Prop) (hT : T ≤ εmax) (count : ℕ)
    (hc : 2 ≤ count) (claim : E2) (mode : Option E2) :
    Spec (roundPolyE2 count claim mode) (Doomed C A)
      (fun msg h ↦ msg.length = count ∧
        RoundSplitF mode claim (polyEvalF msg 0) (polyEvalF msg 1) ∧ Doomed C A h) εmax 0 T :=
  match mode with
  | none =>
    (e2ReadSpec hst A hT).bind' fun c0 ↦ (e2ReadsSpecT hst A hT (count - 2)).bind' fun tail ↦
      (Spec.ret (c0 :: (claim + sumF tail) :: tail)).mono
        (fun _ h ↦ ⟨by simp [h.1]; omega, split_noneF c0 claim tail, h.2⟩) (fun _ _ h ↦ h)
        le_rfl le_rfl le_rfl
  | some r =>
    Spec.congr (p := e2Reads (count - 2 + 1) >>= fun tail ↦
        pure ((claim + r * sumF tail) :: tail)) (by
          rw [show count - 2 + 1 = count - 1 by omega]; rfl) <|
      (e2ReadsSpec hst A hT (count - 2)).bind' fun tail ↦
        (Spec.ret ((claim + r * sumF tail) :: tail)).mono
          (fun _ h ↦ ⟨by simp [h.1]; omega, split_someF r claim tail, h.2⟩) (fun _ _ h ↦ h)
          le_rfl le_rfl le_rfl

end Reads

section Doom

variable {β : Type} {C : List Ev → Set β} [Finite β] {L₀ : ℕ} {εmax T : ℝ≥0∞}

/-- The witness of `doomE2Sample`: the nonce (`doomRead`, follower `L₀ · e + T`), the answer
(`doomSample` on "accepted and alive"), the proof of work (`Spec.require`), the value. -/
noncomputable def doomE2SampleSpec (hst : Stable C) (hcard : ∀ h, (C h).ncard ≤ L₀) {g : ℕ}
    (A : β → Prop) (A' : E2 → β → Prop) (e : ℝ≥0∞)
    (hesc : ∀ q, ¬ A q → avgE (fun c ↦ indE (powOK g c ∧ A' (e2OfE c) q)) ≤ e)
    (he : (L₀ : ℝ≥0∞) * e + T ≤ εmax) :
    Spec (e2Sample g) (Doomed C A) (fun y h ↦ Doomed C (A' y) h) εmax 0 T :=
  (doomRead hst A he).bind' fun _ ↦
    (doomSample (εmax := εmax) (T := T) hst hcard A (fun c q ↦ powOK g c ∧ A' (e2OfE c) q) e
      hesc).bind' fun c ↦
      (Spec.require (Post := fun _ h ↦ Doomed C (A' (e2OfE c)) h)
        (fun _ hd hp q hq ha ↦ hd q hq ⟨hp, ha⟩)).bind' fun _ ↦
        Spec.ret (Post := fun y h ↦ Doomed C (A' y) h) (e2OfE c)

/-- **Statement 4, the doom rule of a ground challenge**: from doom of `A`, to doom of `A' y` at the
challenge `y`, when each candidate not alive becomes alive at an accepted answer with probability
`≤ e`. Lead `0` (the nonce is a move); the group (answer and follower) is `L₀ · e + T ≤ εmax`. -/
theorem doomE2Sample (hst : Stable C) (hcard : ∀ h, (C h).ncard ≤ L₀) {g : ℕ} (A : β → Prop)
    (A' : E2 → β → Prop) (e : ℝ≥0∞)
    (hesc : ∀ q, ¬ A q → avgE (fun c ↦ indE (powOK g c ∧ A' (e2OfE c) q)) ≤ e)
    (he : (L₀ : ℝ≥0∞) * e + T ≤ εmax) :
    Nonempty (Spec (e2Sample g) (Doomed C A) (fun y h ↦ Doomed C (A' y) h) εmax 0 T) :=
  ⟨doomE2SampleSpec hst hcard A A' e hesc he⟩

/-- The witness of `coordG`, by recursion on `n` (the twin of `doomSampleN`). -/
noncomputable def coordGSpec (hst : Stable C) (hcard : ∀ h, (C h).ncard ≤ L₀) {g : ℕ}
    (A : List E2 → β → Prop) (e : ℝ≥0∞)
    (hesc : ∀ acc q, ¬ A acc q → avgE (fun c ↦ indE (powOK g c ∧ A (acc ++ [e2OfE c]) q)) ≤ e)
    (he : (L₀ : ℝ≥0∞) * e + T ≤ εmax) :
    (n : ℕ) → (acc : List E2) →
      Spec (e2Samples g (n + 1)) (Doomed C (A acc))
        (fun l h ↦ l.length = n + 1 ∧ Doomed C (A (acc ++ l)) h) εmax 0 T
  | 0, acc => (doomE2SampleSpec hst hcard (A acc) (fun y ↦ A (acc ++ [y])) e (hesc acc) he).bind'
      fun x ↦ (Spec.ret (Post := fun xs h ↦ xs = [] ∧ Doomed C (A (acc ++ [x])) h) []).mono
        (fun _ hd ↦ ⟨rfl, hd⟩) (fun _ _ h ↦ h) le_rfl le_rfl le_rfl |>.bind' fun xs ↦
          (Spec.ret (x :: xs)).mono (fun _ h ↦ ⟨by simp [h.1], by simpa [h.1] using h.2⟩)
            (fun _ _ h ↦ h) le_rfl le_rfl le_rfl
  | n + 1, acc => (doomE2SampleSpec hst hcard (A acc) (fun y ↦ A (acc ++ [y])) e (hesc acc)
      he).bind' fun x ↦
        ((coordGSpec hst hcard A e hesc he n (acc ++ [x])).mono (fun _ h ↦ h) (fun _ _ h ↦ h)
          le_rfl zero_le le_rfl).bind' fun xs ↦
          (Spec.ret (x :: xs)).mono (fun _ h ↦ ⟨by simp [h.1], by simpa using h.2⟩)
            (fun _ _ h ↦ h) le_rfl le_rfl le_rfl

/-- **Statement 5 (`coordG`)**: `n + 1` ground coordinates, the alive predicate on the coordinates
drawn after `acc`, each escaping at `e` per candidate. Lead `0`; each group `L₀ · e + T ≤ εmax`. -/
theorem coordG (hst : Stable C) (hcard : ∀ h, (C h).ncard ≤ L₀) {g : ℕ} (A : List E2 → β → Prop)
    (e : ℝ≥0∞)
    (hesc : ∀ acc q, ¬ A acc q → avgE (fun c ↦ indE (powOK g c ∧ A (acc ++ [e2OfE c]) q)) ≤ e)
    (he : (L₀ : ℝ≥0∞) * e + T ≤ εmax) (n : ℕ) (acc : List E2) :
    Nonempty (Spec (e2Samples g (n + 1)) (Doomed C (A acc))
      (fun l h ↦ l.length = n + 1 ∧ Doomed C (A (acc ++ l)) h) εmax 0 T) :=
  ⟨coordGSpec hst hcard A e hesc he n acc⟩

/-- The witness of `sumcheckRoundG` (the twin of `sumcheckSpec`). -/
noncomputable def sumcheckGSpec (hst : Stable C) (hcard : ∀ h, (C h).ncard ≤ L₀) (R : β → Prop)
    {Fm : β → List E2 → E2} {d N : ℕ} (hF : PlainFamilyF Fm d N) {count : ℕ} (hc : 2 ≤ count)
    (hcd : count - 1 ≤ d) {g : ℕ} (hg : g ≤ 64) (he : (L₀ : ℝ≥0∞) * errG g d + T ≤ εmax) :
    (n : ℕ) → (acc : List E2) → (claim : E2) → acc.length + n ≤ N →
      Spec (sumcheckE2 g claim count (List.replicate n none))
        (Doomed C (fun q ↦ claim = Fm q acc ∧ R q))
        (fun res h ↦ res.1.length = n ∧ Doomed C (fun q ↦ res.2 = Fm q (acc ++ res.1) ∧ R q) h)
        εmax T T
  | 0, acc, claim, _ =>
    (Spec.ret (Post := fun (res : List E2 × E2) h ↦ res.1.length = 0 ∧
        Doomed C (fun q ↦ res.2 = Fm q (acc ++ res.1) ∧ R q) h) ([], claim)).mono
      (fun _ h ↦ ⟨rfl, by simpa using h⟩) (fun _ _ h ↦ h) le_rfl le_rfl le_rfl
  | n + 1, acc, claim, hN => by
    refine ((roundSpecE2 (T := 0) hst _ zero_le count hc claim none).mono
      (fun _ h ↦ h) (fun msg h (hm : msg.length = count ∧ _ ∧ _) ↦ hm) le_rfl zero_le
      le_rfl).bind' fun msg ↦ ?_
    by_cases hm : msg.length = count
    · refine ((doomE2SampleSpec (εmax := εmax) (T := T) hst hcard
        (fun q ↦ (∀ x, polyEvalF msg x = Fm q (acc ++ [x])) ∧ R q)
        (fun y q ↦ polyEvalF msg y = Fm q (acc ++ [y]) ∧ R q) (errG g d)
        (fun q hq ↦ plainG_escape hg hF R (by omega) (by omega) q hq) he).mono
          (fun h (hh : msg.length = count ∧
              RoundSplitF none claim (polyEvalF msg 0) (polyEvalF msg 1) ∧
              Doomed C (fun q ↦ claim = Fm q acc ∧ R q) h) ↦
            Doomed.mono hh.2.2 fun q ⟨hall, hR⟩ ↦ ⟨by
              have hs := hh.2.1
              rw [RoundSplitF, hall, hall] at hs
              rw [← hs]
              exact (hF q acc (by omega)).2.symm, hR⟩)
          (fun _ _ h ↦ h) le_rfl le_rfl le_rfl).bind' fun c ↦ ?_
      refine (sumcheckGSpec hst hcard R hF hc hcd hg he n (acc ++ [c]) (polyEvalF msg c)
        (by simp; omega)).bind' fun res ↦ ?_
      exact (Spec.ret (c :: res.1, res.2)).mono
        (fun _ h ↦ ⟨by simp [h.1], by simpa using h.2⟩) (fun _ _ h ↦ h) le_rfl le_rfl le_rfl
    · exact Spec.dead.mono (fun _ h ↦ hm h.1) (fun _ _ h ↦ h) le_rfl le_rfl le_rfl

/-- **Statement 5 (`sumcheckRoundG`)**: plain rounds at `E2` (the twin of `sumcheckSpec`): from doom
of `claim = Fm q acc` to doom of `final = Fm q (acc ++ point)`; each challenge escapes at
`L₀ · 2^-g · d / 2^128`. Lead `T` (`0` when a round is left). -/
theorem sumcheckRoundG (hst : Stable C) (hcard : ∀ h, (C h).ncard ≤ L₀) (R : β → Prop)
    {Fm : β → List E2 → E2} {d N : ℕ} (hF : PlainFamilyF Fm d N) {count : ℕ} (hc : 2 ≤ count)
    (hcd : count - 1 ≤ d) {g : ℕ} (hg : g ≤ 64) (hT : T ≤ εmax)
    (he : (L₀ : ℝ≥0∞) * errG g d + T ≤ εmax) (n : ℕ) (acc : List E2) (claim : E2)
    (hN : acc.length + n ≤ N) :
    Nonempty (Spec (sumcheckE2 g claim count (List.replicate n none))
      (Doomed C (fun q ↦ claim = Fm q acc ∧ R q))
      (fun res h ↦ res.1.length = n ∧ Doomed C (fun q ↦ res.2 = Fm q (acc ++ res.1) ∧ R q) h)
      εmax T T) :=
  ⟨sumcheckGSpec hst hcard R hF hc hcd hg he n acc claim hN⟩

/-- The witness of `packRoundG` (the twin of `packSpec`). -/
noncomputable def packGSpec (hst : Stable C) (hcard : ∀ h, (C h).ncard ≤ L₀) (R : β → Prop)
    {Fm : β → List E2 → E2} {r : List E2} {d : ℕ} (hF : EqFamilyF Fm r d) (hd : 2 ≤ d) {g : ℕ}
    (hg : g ≤ 64) (he : (L₀ : ℝ≥0∞) * errG g (d + 1) + T ≤ εmax) :
    (rs acc : List E2) → (value scale : E2) → rs = r.drop acc.length →
      Spec (packRoundsE2 g rs value scale)
        (Doomed C (fun q ↦ value = scale * Fm q acc ∧ R q))
        (fun res h ↦ res.2.2.length = rs.length ∧
          Doomed C (fun q ↦ res.1 = res.2.1 * Fm q (acc ++ res.2.2) ∧ R q) h) εmax T T
  | [], acc, value, scale, _ =>
    (Spec.ret (Post := fun (res : E2 × E2 × List E2) h ↦ res.2.2.length = 0 ∧
        Doomed C (fun q ↦ res.1 = res.2.1 * Fm q (acc ++ res.2.2) ∧ R q) h)
      (value, scale, [])).mono
      (fun _ h ↦ ⟨rfl, by simpa using h⟩) (fun _ _ h ↦ h) le_rfl le_rfl le_rfl
  | rk :: rs, acc, value, scale, hrs => by
    have hlt : acc.length < r.length := by
      by_contra h
      rw [List.drop_eq_nil_of_le (by omega)] at hrs
      exact List.cons_ne_nil _ _ hrs
    have hrk : r[acc.length] = rk := by
      have := congrArg List.head? hrs
      rw [List.head?_drop, List.getElem?_eq_getElem hlt] at this
      simpa using this.symm
    refine ((roundSpecE2 (T := 0) hst _ zero_le 3 (by norm_num) value
      (some rk)).mono (fun _ h ↦ h) (fun msg h (hm : msg.length = 3 ∧ _ ∧ _) ↦ hm) le_rfl
      zero_le le_rfl).bind' fun msg ↦ ?_
    by_cases hm : msg.length = 3
    · refine ((doomE2SampleSpec (εmax := εmax) (T := T) hst hcard
        (fun q ↦ (∀ x, polyEvalF msg x = scale * Fm q (acc ++ [x])) ∧ R q)
        (fun y q ↦ (1 + r[acc.length] + y) * polyEvalF msg y =
          (scale * (1 + r[acc.length] + y)) * Fm q (acc ++ [y]) ∧ R q) (errG g (d + 1))
        (fun q hq ↦ eqG_escape hg hF R hlt (by omega) scale q hq) he).mono
          (fun h (hh : msg.length = 3 ∧
              RoundSplitF (some rk) value (polyEvalF msg 0) (polyEvalF msg 1) ∧
              Doomed C (fun q ↦ value = scale * Fm q acc ∧ R q) h) ↦
            Doomed.mono hh.2.2 fun q ⟨hall, hR⟩ ↦ ⟨by
              have hs := hh.2.1
              rw [RoundSplitF, hall, hall, ← hrk] at hs
              rw [← hs, (hF q acc hlt).2]
              ring, hR⟩)
          (fun _ _ h ↦ h) le_rfl le_rfl le_rfl).bind' fun c ↦ ?_
      refine (packGSpec hst hcard R hF hd hg he rs (acc ++ [c])
        ((1 + rk + c) * polyEvalF msg c) (scale * (1 + rk + c)) ?_).mono
        (fun _ h ↦ by rw [hrk] at h; exact h) (fun _ _ h ↦ h) le_rfl le_rfl le_rfl
        |>.bind' fun res ↦ ?_
      · rw [List.length_append, List.length_singleton, ← List.drop_drop, ← hrs]
        rfl
      · exact (Spec.ret (res.1, res.2.1, c :: res.2.2)).mono
          (fun _ h ↦ ⟨by simp [h.1], by simpa using h.2⟩) (fun _ _ h ↦ h) le_rfl le_rfl le_rfl
    · exact Spec.dead.mono (fun _ h ↦ hm h.1) (fun _ _ h ↦ h) le_rfl le_rfl le_rfl

/-- **Statement 5 (`packRoundG`)**: the equality-mode rounds at `E2` (the twin of `packSpec`), at the
point `r`, `rs = r.drop acc.length` left: from doom of `value = scale · Fm q acc` to doom of
`value' = scale' · Fm q (acc ++ point)`; each challenge escapes at `L₀ · 2^-g · (d + 1) / 2^128`. -/
theorem packRoundG (hst : Stable C) (hcard : ∀ h, (C h).ncard ≤ L₀) (R : β → Prop)
    {Fm : β → List E2 → E2} {r : List E2} {d : ℕ} (hF : EqFamilyF Fm r d) (hd : 2 ≤ d) {g : ℕ}
    (hg : g ≤ 64) (hT : T ≤ εmax) (he : (L₀ : ℝ≥0∞) * errG g (d + 1) + T ≤ εmax)
    (rs acc : List E2) (value scale : E2) (hrs : rs = r.drop acc.length) :
    Nonempty (Spec (packRoundsE2 g rs value scale)
      (Doomed C (fun q ↦ value = scale * Fm q acc ∧ R q))
      (fun res h ↦ res.2.2.length = rs.length ∧
        Doomed C (fun q ↦ res.1 = res.2.1 * Fm q (acc ++ res.2.2) ∧ R q) h) εmax T T) :=
  ⟨packGSpec hst hcard R hF hd hg he rs acc value scale hrs⟩

end Doom

end Lvm.E2V
