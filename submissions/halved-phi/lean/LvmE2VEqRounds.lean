-- New for lvm2 S1 (E2-F, E2F-V): V_S's `E2` rounds (`roundPolyD`, `sumcheckD`, `packRoundsD`) refine the spec's
-- (`roundPolyE2`, `sumcheckE2`, `packRoundsE2`) on the width-aware stream, values through `FE2.toE2`.
import LvmE2VEqCore

/-!
# The rounds at `E2`

* `wRound count = wReads (count − 1)` (a round's message), `wSc count n` (`n` rounds, each the message then
  the challenge's nonce), `wPack n` (`n` equality-mode rounds of 3 coefficients);
* **`refW_roundPolyD`**, **`refW_sumcheckD`**, **`refW_packRoundsD`**, and `MonoD` of each.
-/

set_option autoImplicit false

namespace Lvm.VEq

open Lvm DM LeanVM.Parameters LeanVM.Protocol.Compile
open Lvm.FE2 (toE2)

/-! ## Widths -/

/-- A round of `count` coefficients and its challenge's nonce. -/
def wRoundG (count : ℕ) : List ℕ := wReads (count - 1) ++ wSampleG

/-- `n` plain rounds. -/
def wSc (count n : ℕ) : List ℕ := (List.replicate n (wRoundG count)).flatten

/-- `n` equality-mode rounds (3 coefficients: 2 reads). -/
def wPack (n : ℕ) : List ℕ := wSc 3 n

theorem length_wReads (n : ℕ) : (wReads n).length = n := by simp [wReads]

theorem length_wRoundG (count : ℕ) : (wRoundG count).length = count - 1 + 1 := by
  simp [wRoundG, length_wReads, wSampleG]

theorem length_wSc (count n : ℕ) : (wSc count n).length = n * (count - 1 + 1) := by
  induction n with
  | zero => simp [wSc]
  | succ n ih =>
    rw [wSc, List.replicate_succ, List.flatten_cons, List.length_append, ← wSc, ih, length_wRoundG]
    ring

theorem wSc_succ (count n : ℕ) : wSc count (n + 1) = wRoundG count ++ wSc count n := by
  rw [wSc, List.replicate_succ, List.flatten_cons, ← wSc]

/-! ## `MonoD` -/

theorem monoD_roundPolyD (count : ℕ) (claim : FE2) : ∀ mode, MonoD (roundPolyD count claim mode)
  | none => monoD_readE2.bind fun _ ↦ (monoD_readE2s _).bind fun _ ↦ MonoD.pure _
  | some _ => (monoD_readE2s _).bind fun _ ↦ MonoD.pure _

theorem monoD_sumcheckD (g count : ℕ) : ∀ (modes : List (Option FE2)) (claim : FE2),
    MonoD (sumcheckD g claim count modes)
  | [], _ => MonoD.pure _
  | m :: ms, _ => (monoD_roundPolyD _ _ m).bind fun _ ↦ (monoD_sampleG g).bind fun _ ↦
      (monoD_sumcheckD g count ms _).bind fun _ ↦ MonoD.pure _

theorem monoD_packRoundsD (g : ℕ) : ∀ (rs : List FE2) (value scale : FE2),
    MonoD (packRoundsD g rs value scale)
  | [], _, _ => MonoD.pure _
  | _ :: rs, _, _ => (monoD_roundPolyD _ _ _).bind fun _ ↦ (monoD_sampleG g).bind fun _ ↦
      (monoD_packRoundsD g rs _ _).bind fun _ ↦ MonoD.pure _

section Ref

variable {cap : ℕ → ℕ → ℕ} {occ : ℕ → ℕ → ℕ} {shp : ℕ → ℕ × ℕ} {rw : ℕ → ℕ} {sig : ByteArray}

/-- **A round's message.** -/
theorem refW_roundPolyD (count : ℕ) (hc : 2 ≤ count) (claim : FE2) (mode : Option FE2) {i : ℕ}
    (hw : WAt rw i (wReads (count - 1))) :
    RefAtW cap occ shp rw sig i (roundPolyD count claim mode)
      (E2V.roundPolyE2 count (toE2 claim) (mode.map toE2)) (fun xs ys ↦ ys = xs.map toE2)
      (i + (count - 1)) := by
  cases mode with
  | none =>
    rw [show count - 1 = (count - 2) + 1 by omega, wReads, List.replicate_succ, WAt.cons] at hw
    refine RefAtW.bind (fun _ ↦ (monoD_readE2s _).bind fun _ ↦ MonoD.pure _) (refW_readE2 hw.1) ?_
    intro c0 y0 hy0
    refine RefAtW.bind (fun _ ↦ MonoD.pure _) (refW_readE2s _ hw.2) ?_
    intro tail ys hys
    refine (RefAtW.pure ?_).idx (by omega)
    subst hy0 hys
    simp [E2V.toE2_sumF]
  | some r =>
    show RefAtW cap occ shp rw sig i (readE2s (count - 1) >>= fun tail ↦
        Pure.pure ((claim + r * E2V.sumF tail) :: tail))
      (E2V.e2Reads (count - 1) >>= fun tail ↦ Pure.pure ((toE2 claim + toE2 r * E2V.sumF tail) :: tail)) _ _
    refine RefAtW.bind (fun _ ↦ MonoD.pure _) (refW_readE2s _ hw) ?_
    intro tail ys hys
    refine RefAtW.pure ?_
    subst hys
    simp [E2V.toE2_sumF]

/-- **The plain sumcheck at `E2`.** -/
theorem refW_sumcheckD (g count : ℕ) (hc : 2 ≤ count) : ∀ (modes : List (Option FE2)) (claim : FE2)
    {i : ℕ}, WAt rw i (wSc count modes.length) →
    RefAtW cap occ shp rw sig i (sumcheckD g claim count modes)
      (E2V.sumcheckE2 g (toE2 claim) count (modes.map (Option.map toE2)))
      (fun xs ys ↦ ys.1 = xs.1.map toE2 ∧ ys.2 = toE2 xs.2 ∧ xs.1.length = modes.length)
      (i + (wSc count modes.length).length)
  | [], claim, i, _ => RefAtW.pure ⟨rfl, rfl, rfl⟩
  | m :: ms, claim, i, hw => by
    rw [List.length_cons, wSc_succ, WAt.append, wRoundG, WAt.append] at hw
    obtain ⟨⟨hr, hs⟩, hrest⟩ := hw
    rw [wSampleG, WAt.cons] at hs
    refine RefAtW.bind (fun _ ↦ (monoD_sampleG g).bind fun _ ↦ (monoD_sumcheckD g count ms _).bind
      fun _ ↦ MonoD.pure _) (refW_roundPolyD count hc claim m hr) ?_
    intro msg msg' hmsg
    refine RefAtW.bind (fun _ ↦ (monoD_sumcheckD g count ms _).bind fun _ ↦ MonoD.pure _)
      (refW_sampleG g (by rw [length_wReads] at hs; exact hs.1)) ?_
    intro c c' hc'
    have hrest' : WAt rw (i + (count - 1) + 1) (wSc count ms.length) := by
      simpa [length_wReads, wSampleG, Nat.add_assoc] using hrest
    subst hmsg hc'
    have hrec := refW_sumcheckD g count hc ms (E2V.polyEvalF msg c) hrest'
    rw [E2V.toE2_polyEvalF] at hrec
    refine RefAtW.bind (fun _ ↦ MonoD.pure _) hrec ?_
    intro res res' hres
    refine (RefAtW.pure ⟨by simp [hres.1], hres.2.1, by simp [hres.2.2]⟩).idx ?_
    rw [List.length_cons, wSc_succ, List.length_append, length_wRoundG]
    omega

/-- **The equality-mode rounds at `E2`.** -/
theorem refW_packRoundsD (g : ℕ) : ∀ (rs : List FE2) (value scale : FE2) {i : ℕ},
    WAt rw i (wPack rs.length) →
    RefAtW cap occ shp rw sig i (packRoundsD g rs value scale)
      (E2V.packRoundsE2 g (rs.map toE2) (toE2 value) (toE2 scale))
      (fun xs ys ↦ ys.1 = toE2 xs.1 ∧ ys.2.1 = toE2 xs.2.1 ∧ ys.2.2 = xs.2.2.map toE2 ∧
        xs.2.2.length = rs.length)
      (i + (wPack rs.length).length)
  | [], value, scale, i, _ => RefAtW.pure ⟨rfl, rfl, rfl, rfl⟩
  | r :: rs, value, scale, i, hw => by
    rw [List.length_cons, wPack, wSc_succ, WAt.append, wRoundG, WAt.append] at hw
    obtain ⟨⟨hr, hs⟩, hrest⟩ := hw
    rw [wSampleG, WAt.cons] at hs
    refine RefAtW.bind (fun _ ↦ (monoD_sampleG g).bind fun _ ↦ (monoD_packRoundsD g rs _ _).bind
      fun _ ↦ MonoD.pure _) (refW_roundPolyD 3 (by norm_num) value (some r) hr) ?_
    intro msg msg' hmsg
    refine RefAtW.bind (fun _ ↦ (monoD_packRoundsD g rs _ _).bind fun _ ↦ MonoD.pure _)
      (refW_sampleG g (by rw [length_wReads] at hs; exact hs.1)) ?_
    intro c c' hc'
    have hrest' : WAt rw (i + (3 - 1) + 1) (wPack rs.length) := by
      simpa [length_wReads, wSampleG, Nat.add_assoc, wPack] using hrest
    subst hmsg hc'
    have hrec := refW_packRoundsD g rs ((1 + r + c) * E2V.polyEvalF msg c) (scale * (1 + r + c))
      hrest'
    have e1 : toE2 ((1 + r + c) * E2V.polyEvalF msg c) =
        (1 + toE2 r + toE2 c) * E2V.polyEvalF (msg.map toE2) (toE2 c) := by
      rw [Lvm.FE2.fe2_mul_eq, Lvm.FE2.toE2_add, Lvm.FE2.toE2_add, Lvm.FE2.toE2_one, E2V.toE2_polyEvalF]
    have e2 : toE2 (scale * (1 + r + c)) = toE2 scale * (1 + toE2 r + toE2 c) := by
      rw [Lvm.FE2.fe2_mul_eq, Lvm.FE2.toE2_add, Lvm.FE2.toE2_add, Lvm.FE2.toE2_one]
    rw [e1, e2] at hrec
    refine RefAtW.bind (fun _ ↦ MonoD.pure _) hrec ?_
    intro res res' hres
    refine (RefAtW.pure ⟨hres.1, hres.2.1, by simp [hres.2.2.1], by simp [hres.2.2.2]⟩).idx ?_
    simp only [wPack, length_wSc, List.length_cons]
    ring

end Ref

end Lvm.VEq
