-- New for lvm6 (WP-V1b): functional twins. A fast phase `fp : VF β` is a twin of the phase program `p` when
-- its value decodes (`d : β → α`) to the program's replayed value on every proof and transcript (`TwinF`).
-- The season-1 DSL steps at `E2` (reads, ground draws, sumcheck rounds) get their word-field twins here, and
-- the field-generic list functions commute with ring maps (`map_sumF`, `map_polyEvalF`, …).
import Lvm6VFastW
import LvmE2VSample

/-!
# Functional twins and the `E2` DSL steps

* `VF β`: a fast phase (proof and driver transcript to a value and the rest); `VF.bind`, `VF.pure`,
  `VF.guard` (a check: fail unless the flag holds).
* **`TwinF d p fp`**: `Twin` with the value relation `d b = a`. Rules: `tw_bind`, `tw_bindR` (a first
  step with any relation), `tw_pure`, `tw_guard` (a `require` against a Boolean flag), `tw_sample`.
* `tE : FE2 →+* E2` (`toE2`); generic map lemmas over any ring map `φ`: `map_sumF`, `map_polyEvalF`,
  `map_foldPairsF`, `map_multilinearEvalF`, `map_eqAtF`.
* Twins of the `E2` DSL (`LvmE2VSample`): `tw_e2Read`, `tw_e2Reads`, `tw_e2Sample`, `tw_roundPoly`,
  `tw_sumcheck` (value `(cs, v) ↦ (cs.map toE2, toE2 v)`).
-/

set_option autoImplicit false

namespace Lvm6.V

open RecursionFast LeanVM.Parameters Lvm.FS Lvm.Replay Lvm Lvm.E2V
open LeanVM.Protocol.Compile hiding Proof Bytes Word

/-! ## Fast phases -/

/-- A fast phase: the proof and the driver's transcript (oldest first) to a value and the rest. -/
abbrev VF (β : Type) : Type := ByteArray → List NV → Option (β × List NV)

/-- Sequencing of fast phases. -/
@[inline] def VF.bind {β γ : Type} (fp : VF β) (fg : β → VF γ) : VF γ :=
  fun π tr => (fp π tr).bind fun r => fg r.1 π r.2

/-- A value, nothing read. -/
@[inline] def VF.pure {β : Type} (b : β) : VF β := fun _ tr => some (b, tr)

/-- A check: fail unless `c`. -/
@[inline] def VF.guard {β : Type} (c : Bool) (fk : VF β) : VF β := fun π tr => if c then fk π tr else none

/-- **`fp` is a fast twin of `p` with the decoding `d`.** -/
abbrev TwinF {α β : Type} (d : β → α) (p : VerifierProgram α) (fp : VF β) : Prop :=
  Twin (fun _ b a => d b = a) p fp

theorem tw_bind {α β α' β' : Type} {d : β → α} {d' : β' → α'} {p : VerifierProgram α} {fp : VF β}
    {f : α → VerifierProgram α'} {fg : β → VF β'} (hp : TwinF d p fp)
    (hf : ∀ b, TwinF d' (f (d b)) (fg b)) : TwinF d' (p >>= f) (VF.bind fp fg) :=
  twin_bind hp fun π b a h tr => by subst h; exact hf b π tr

theorem tw_bindR {α β α' β' : Type} {R : ByteArray → β → α → Prop} {d' : β' → α'} {p : VerifierProgram α}
    {fp : VF β} {f : α → VerifierProgram α'} {fg : β → VF β'} (hp : Twin R p fp)
    (hf : ∀ π b a, R π b a → ∀ tr, Option.Rel (fun (b : β' × List NV) (a : α' × List Val) =>
      d' b.1 = a.1 ∧ a.2 = b.2.map (NV.val π)) (fg b π tr) (replayP (f a) (tr.map (NV.val π)))) :
    TwinF d' (p >>= f) (VF.bind fp fg) :=
  twin_bind hp hf

theorem tw_pure {α β : Type} {d : β → α} {a : α} {b : β} (h : d b = a) :
    TwinF d (pure a) (VF.pure b) :=
  twin_ret _ (b := fun _ => b) fun _ => h

/-- A failing program replays to `none`. -/
theorem replayP_fail {α : Type} (tr : List Val) : replayP (VerifierProgram.fail : VerifierProgram α) tr = none := by
  cases tr <;> rfl

theorem tw_guard {α β : Type} {d : β → α} (c : Prop) [Decidable c] (fc : Bool) (hc : c ↔ fc = true)
    {k : VerifierProgram α} {fk : VF β} (hk : TwinF d k fk) :
    TwinF d (VerifierProgram.require c >>= fun _ => k) (VF.guard fc fk) := by
  intro π tr
  by_cases h : fc = true
  · have e : (VerifierProgram.require c >>= fun _ => k) = k := by
      show (VerifierProgram.require c).bind _ = _
      rw [VerifierProgram.require, if_pos (hc.mpr h)]
      rfl
    rw [e]
    show Option.Rel _ (if fc then fk π tr else none) _
    rw [if_pos h]
    exact hk π tr
  · have e : (VerifierProgram.require c >>= fun _ => k) = VerifierProgram.fail := by
      show (VerifierProgram.require c).bind _ = _
      rw [VerifierProgram.require, if_neg (fun h' => h (hc.mp h'))]
      rfl
    rw [e, replayP_fail]
    show Option.Rel _ (if fc then fk π tr else none) none
    rw [if_neg h]
    exact Option.Rel.none

/-- A draw, its value used through its answer. -/
theorem tw_sample {α' β' : Type} {d' : β' → α'} {f : E → VerifierProgram α'} {fg : Digest → VF β'}
    (hf : ∀ a, TwinF d' (f (chalOf a)) (fg a)) :
    TwinF d' (VerifierProgram.sampleChallenge >>= f) (VF.bind fSample fg) :=
  tw_bindR twin_sample fun π a c h tr => by
    simp only [chalR] at h
    subst h
    exact hf a π tr

/-- A read whose value is not used. -/
theorem tw_skipRead {α' β' : Type} {d' : β' → α'} {k : VerifierProgram α'} {fk : VF β'} (hk : TwinF d' k fk) :
    TwinF d' (VerifierProgram.readScalar >>= fun _ => k) (VF.bind fRead fun _ => fk) :=
  tw_bindR twin_read fun π _ _ _ tr => hk π tr

/-! ## `toE2` as a ring map, and the generic list functions under ring maps -/

/-- `toE2` as a ring map. -/
def tE : FE2 →+* E2 := FE2.ringEquivE2.toRingHom

theorem coe_tE : (⇑tE : FE2 → E2) = FE2.toE2 := rfl

section MapLemmas

variable {F F' : Type} [Field F] [Field F'] (φ : F →+* F')

theorem map_foldl_add (l : List F) (acc : F) :
    φ (l.foldl (· + ·) acc) = (l.map φ).foldl (· + ·) (φ acc) := by
  induction l generalizing acc with
  | nil => rfl
  | cons a l ih => simp only [List.foldl_cons, List.map_cons]; rw [ih, map_add]

theorem map_sumF (l : List F) : φ (sumF l) = sumF (l.map φ) := by
  unfold sumF; rw [map_foldl_add, map_zero]

theorem map_polyEvalF (l : List F) (x : F) : φ (polyEvalF l x) = polyEvalF (l.map φ) (φ x) := by
  unfold polyEvalF
  induction l with
  | nil => simp
  | cons c l ih => simp only [List.foldr_cons, List.map_cons, map_add, map_mul, ih]

theorem map_foldPairsF (r : F) : ∀ l : List F, (foldPairsF r l).map φ = foldPairsF (φ r) (l.map φ)
  | a :: b :: rest => by
    simp only [foldPairsF, List.map_cons, map_add, map_mul, map_one, map_foldPairsF r rest]
  | [_] => rfl
  | [] => rfl

theorem map_foldl_foldPairs (pt : List F) : ∀ mle : List F,
    (pt.foldl (fun cur r => foldPairsF r cur) mle).map φ =
      (pt.map φ).foldl (fun cur r => foldPairsF r cur) (mle.map φ) := by
  induction pt with
  | nil => intro mle; rfl
  | cons r pt ih => intro mle; simp only [List.foldl_cons, List.map_cons]; rw [ih, map_foldPairsF]

theorem map_headD (l : List F) : φ (l.headD 0) = (l.map φ).headD 0 := by
  cases l <;> simp

theorem map_multilinearEvalF (mle pt : List F) :
    φ (multilinearEvalF mle pt) = multilinearEvalF (mle.map φ) (pt.map φ) := by
  unfold multilinearEvalF; rw [map_headD, map_foldl_foldPairs]

theorem map_eqAtF : ∀ (pt : List F) (w : ℕ), φ (eqAtF pt w) = eqAtF (pt.map φ) w
  | [], _ => map_one φ
  | r :: rs, w => by
    simp only [eqAtF, List.map_cons, map_mul, apply_ite (⇑φ), map_add, map_one, map_eqAtF rs]

theorem map_getD (l : List F) (i : ℕ) : φ (l.getD i 0) = (l.map φ).getD i 0 := by
  rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, List.getElem?_map]
  cases l[i]? <;> simp

end MapLemmas

theorem toE2_sumF (l : List FE2) : FE2.toE2 (sumF l) = sumF (l.map FE2.toE2) := map_sumF tE l

theorem toE2_polyEvalF (l : List FE2) (x : FE2) :
    FE2.toE2 (polyEvalF l x) = polyEvalF (l.map FE2.toE2) (FE2.toE2 x) := map_polyEvalF tE l x

theorem toE2_multilinearEvalF (mle pt : List FE2) :
    FE2.toE2 (multilinearEvalF mle pt) = multilinearEvalF (mle.map FE2.toE2) (pt.map FE2.toE2) :=
  map_multilinearEvalF tE mle pt

theorem toE2_eqAtF (pt : List FE2) (w : ℕ) : FE2.toE2 (eqAtF pt w) = eqAtF (pt.map FE2.toE2) w :=
  map_eqAtF tE pt w

theorem toE2_getD (l : List FE2) (i : ℕ) : FE2.toE2 (l.getD i 0) = (l.map FE2.toE2).getD i 0 :=
  map_getD tE l i

theorem toE2_add' (a b : FE2) : FE2.toE2 (a + b) = FE2.toE2 a + FE2.toE2 b := map_add tE a b
theorem toE2_mul' (a b : FE2) : FE2.toE2 (a * b) = FE2.toE2 a * FE2.toE2 b := map_mul tE a b
theorem toE2_one' : FE2.toE2 1 = 1 := map_one tE
theorem toE2_zero' : FE2.toE2 0 = 0 := map_zero tE

/-- Equality in `E2` is equality of the words. -/
theorem toE2_eq_iff (a b : FE2) : FE2.toE2 a = FE2.toE2 b ↔ decide (a = b) = true := by
  rw [decide_eq_true_iff]
  exact ⟨fun h => FE2.toE2_injective h, fun h => h ▸ rfl⟩

/-! ## The `E2` DSL steps -/

theorem tw_e2Read : TwinF FE2.toE2 e2Read fReadF :=
  twin_map' (R := readR) (fun x => e2OfE x) (fun π ow => decRd π ow.1 ow.2) twin_read fun π ow x hR => by
    simp only [readR] at hR
    rw [toE2_decRd, hR]

/-- Fast `e2Reads n`. -/
def fE2Reads : ℕ → VF (List FE2)
  | 0 => VF.pure []
  | n + 1 => VF.bind fReadF fun x => VF.bind (fE2Reads n) fun xs => VF.pure (x :: xs)

theorem tw_e2Reads : ∀ n, TwinF (List.map FE2.toE2) (e2Reads n) (fE2Reads n)
  | 0 => tw_pure rfl
  | n + 1 => tw_bind (f := fun x => e2Reads n >>= fun xs => pure (x :: xs)) tw_e2Read fun x =>
      tw_bind (tw_e2Reads n) fun xs => tw_pure rfl

/-- The proof of work of a draw on its answer's bits. -/
theorem powOK_iff (g : ℕ) (a : Digest) :
    LeanVM.Protocol.Verifier.powOK g (chalOf a) ↔ pw g (answerBits a) = true := by
  rw [LeanVM.Protocol.Verifier.powOK, pw, decide_eq_true_iff, Lvm.VEq.answerBits_eq]

/-- Fast `e2Sample g`: the nonce, the draw, its proof of work, lanes 0–1. -/
def fE2Sample (g : ℕ) : VF FE2 :=
  VF.bind fRead fun _ => VF.bind fSample fun a => VF.guard (pw g (answerBits a)) (VF.pure (fe2OfAns a))

theorem tw_e2Sample (g : ℕ) : TwinF FE2.toE2 (e2Sample g) (fE2Sample g) :=
  tw_skipRead (tw_sample fun a =>
    tw_guard _ _ (powOK_iff g a) (tw_pure (e2OfE_chal a).symm))

/-- Fast `roundPolyE2 count claim mode`. -/
def fRoundPoly (count : ℕ) (claim : FE2) : Option FE2 → VF (List FE2)
  | none => VF.bind fReadF fun c0 => VF.bind (fE2Reads (count - 2)) fun tail =>
      VF.pure (c0 :: (claim + sumF tail) :: tail)
  | some r => VF.bind (fE2Reads (count - 1)) fun tail => VF.pure ((claim + r * sumF tail) :: tail)

theorem tw_roundPoly (count : ℕ) (claim : FE2) : ∀ mode : Option FE2,
    TwinF (List.map FE2.toE2) (roundPolyE2 count (FE2.toE2 claim) (mode.map FE2.toE2))
      (fRoundPoly count claim mode)
  | none => by
    show TwinF (List.map FE2.toE2) (e2Read >>= fun c0 => e2Reads (count - 2) >>= fun tail =>
      pure (c0 :: (FE2.toE2 claim + sumF tail) :: tail)) (VF.bind fReadF fun c0 =>
        VF.bind (fE2Reads (count - 2)) fun tail => VF.pure (c0 :: (claim + sumF tail) :: tail))
    refine tw_bind tw_e2Read fun c0 => tw_bind (tw_e2Reads _) fun tail => tw_pure ?_
    simp only [List.map_cons, toE2_add', toE2_sumF]
  | some r => by
    show TwinF (List.map FE2.toE2) (e2Reads (count - 1) >>= fun tail =>
      pure ((FE2.toE2 claim + FE2.toE2 r * sumF tail) :: tail))
        (VF.bind (fE2Reads (count - 1)) fun tail => VF.pure ((claim + r * sumF tail) :: tail))
    refine tw_bind (tw_e2Reads _) fun tail => tw_pure ?_
    simp only [List.map_cons, toE2_add', toE2_mul', toE2_sumF]

/-- Fast `sumcheckE2 g claim count modes`. -/
def fSumcheck (g : ℕ) (claim : FE2) (count : ℕ) : List (Option FE2) → VF (List FE2 × FE2)
  | [] => VF.pure ([], claim)
  | mode :: modes => VF.bind (fRoundPoly count claim mode) fun msg => VF.bind (fE2Sample g) fun c =>
      VF.bind (fSumcheck g (polyEvalF msg c) count modes) fun res => VF.pure (c :: res.1, res.2)

/-- The decoding of a sumcheck's value. -/
def scD (r : List FE2 × FE2) : List E2 × E2 := (r.1.map FE2.toE2, FE2.toE2 r.2)

theorem tw_sumcheck (g count : ℕ) : ∀ (modes : List (Option FE2)) (claim : FE2),
    TwinF scD (sumcheckE2 g (FE2.toE2 claim) count (modes.map (Option.map FE2.toE2)))
      (fSumcheck g claim count modes)
  | [], _ => tw_pure rfl
  | mode :: modes, claim =>
    tw_bind (f := fun msg => e2Sample g >>= fun c => sumcheckE2 g (polyEvalF msg c) count
        (modes.map (Option.map FE2.toE2)) >>= fun res => pure (c :: res.1, res.2))
      (tw_roundPoly count claim mode) fun msg =>
      tw_bind (f := fun c => sumcheckE2 g (polyEvalF (msg.map FE2.toE2) c) count
          (modes.map (Option.map FE2.toE2)) >>= fun res => pure (c :: res.1, res.2))
        (tw_e2Sample g) fun c => by
        try dsimp only
        rw [← toE2_polyEvalF]
        exact tw_bind (tw_sumcheck g count modes _) fun res => tw_pure rfl

/-- The plain sumcheck of `n` rounds. -/
theorem tw_sumcheckPlain (g count n : ℕ) (claim : FE2) :
    TwinF scD (sumcheckE2 g (FE2.toE2 claim) count (List.replicate n none))
      (fSumcheck g claim count (List.replicate n none)) := by
  have h := tw_sumcheck g count (List.replicate n none) claim
  rwa [List.map_replicate] at h

end Lvm6.V
