-- New for `flock-recursive` (revision 4.4.2, the reserve in RSV2's stacked form; RSV2 §5 item 8; track
-- RSV-S2b): the controls of the child claim (`truthChild4`, `ChildBad4`) and of the kind change.
import FRSoundness4P4bB

/-!
# Controls of the reserve's child claim

* **`truthChild_pos`** (+): an honest child claim (`X = Σ_i s_i·M̃_i(p)`) on honest M rows is not
  doomed: `ChildBad4` fails, E1's table `zcE4` is zero, so `ZCwE4` fails at every `(τ, η)`.
* **`childBad_neg`** (−): the claim `X + 1` is in `ChildBad4` (`D = −1`); E1's table is nonzero
  (`zcT_ne`), and at the concrete point `τ = 0`, `η = 1` its extension is `−1`; on the log, `ZCwE4`
  holds at every `η ≠ 0`.
* **`kindChange_pos`** (+): the parent's sum over its own row coordinates with the claim's higher
  coordinates fixed is the stacked extension at the claim's point, for an `N2` parent (22
  coordinates; `N4`'s and `N8`'s matrices read 23: the fixed evaluation) and an `N4` parent (23;
  `N2`'s read 22: the constant extension), at any coefficients `s` (full support included); per
  matrix: `N2 ← N4` and `N4 ← N2` (`matMLE_hiRow` both ways).
* **`n8_zero`** (+): the zero claim (`N8`'s `fLrEnd[48, 1008) = 0`) is a true child claim.
-/

namespace FR.Snd.P4b
open RecursionFast FR.Merkle FR.Rev4 Finset

set_option linter.constructorNameAsVariable false

section
variable (R : FSrc) (srcE : NodeKind → ESrc)

/-- The reserve's readers are the claim's values: `p_x` at `0 … 22`, `p_y` at `23 … 47`, `s` at
`48 … 56`, `X` at `57`. -/
theorem child_rsvV (es : Log) :
    (∀ j, pxL es j = rsvV es j) ∧ (∀ j, pyL es j = rsvV es (23 + j)) ∧
      (∀ i, sL es i = rsvV es (48 + i)) ∧ xL es = rsvV es 57 := by
  refine ⟨fun j => rfl, fun j => ?_, fun i => ?_, rfl⟩
  · simp only [pyL, rsvV]; congr 1; ring
  · simp only [sL, rsvV]; congr 1; ring

/-- (+) **An honest child claim on honest M rows is never doomed by E1**: `ChildBad4` fails, E1's
table is `0`, and `ZCwE4` fails whatever `(τ, η)` was drawn. -/
theorem truthChild_pos {κ : NodeKind} {L es : Log} (hk : kindOfC es = .node κ)
    (htc : truthChild4 srcE es)
    (hrows : residual (entMat (srcE κ).ea (e2R κ) (ncR κ)) (entMat (srcE κ).eb (e2R κ) (ncR κ))
      (entMat (srcE κ).ec (e2R κ) (ncR κ)) (zCG R (ncR κ) L es) = 0) :
    ¬ ChildBad4 srcE L es ∧ zcE4 R srcE κ L es = 0 ∧ ¬ ZCwE4 R srcE L es := by
  have hD : dChild srcE es = 0 := (truthChild_iff srcE es).1 htc
  refine ⟨fun ⟨_, _, _, h⟩ => h htc, ?_, fun ⟨κ', hk', h⟩ => ?_⟩
  · funext u
    simp only [zcE4, Rsv.zcT, hrows, hD, zero_mul, add_zero, Pi.zero_apply]
    simp [mle]
  · rw [hk] at hk'
    cases hk'
    apply h
    show _ = _
    rw [hrows, hD, mul_zero, add_zero]
    simp [mle]

/-- (−) **The claim `X + 1` is caught** (RSV2 §5 item 8): it is in `ChildBad4` with defect `−1`; E1's
table is nonzero (`zcT_ne`), and its extension at the concrete point `τ = 0`, `η = 1` (coordinate 23)
is `−1` on honest M rows; on the log, `ZCwE4` holds at every `η ≠ 0`. -/
theorem childBad_neg {κ : NodeKind} {L es : Log} (hk : kindOfC es = .node κ) (hl : 214 ≤ es.length)
    (hX : xL es = mStack srcE (sL es) (pxL es) (pyL es) + 1)
    (hrows : residual (entMat (srcE κ).ea (e2R κ) (ncR κ)) (entMat (srcE κ).eb (e2R κ) (ncR κ))
      (entMat (srcE κ).ec (e2R κ) (ncR κ)) (zCG R (ncR κ) L es) = 0) :
    ChildBad4 srcE L es ∧ dChild srcE es = -1 ∧ zcE4 R srcE κ L es ≠ 0 ∧
      mle (zcE4 R srcE κ L es) (fun j => if j.val = 23 then 1 else 0) = -1 ∧
      (etaL es ≠ 0 → ZCwE4 R srcE L es) := by
  have hD : dChild srcE es = -1 := by rw [dChild, hX]; ring
  have hD0 : dChild srcE es ≠ 0 := by rw [hD]; exact neg_ne_zero.mpr one_ne_zero
  refine ⟨⟨κ, hk, hl, fun h => hD0 ((truthChild_iff srcE es).1 h)⟩, hD,
    Rsv.zcT_ne _ (dims_le' κ).2.1 (.inr hD0), ?_, fun he => ⟨κ, hk, ?_⟩⟩
  · rw [zcE4, Rsv.mle_zcT, hrows, hD]
    simp [mle]
  · show _ ≠ _
    rw [hrows, hD]
    simpa [mle] using he

end

/-! ## The kind change -/

/-- (+) **The kind change goes through** (RSV2 §2.5, the E2 sum at the mixed point): for an `N2` parent
(22 row coordinates) and an `N4` parent (23), at any coefficients `s` (full support included), the
sum over the parent's coordinates with the claim's higher ones fixed is the stacked extension at the
claim's point `p`. -/
theorem kindChange_pos (srcE : NodeKind → ESrc) (s p q : ℕ → F) :
    mle (fun x : Fin (2 ^ 22) => mStack srcE s (Rsv.hiPt (cube x) p) q) (Rsv.lowA 22 p) =
        mStack srcE s p q ∧
      mle (fun x : Fin (2 ^ 23) => mStack srcE s (Rsv.hiPt (cube x) p) q) (Rsv.lowA 23 p) =
        mStack srcE s p q := by
  refine ⟨?_, ?_⟩ <;> rw [mle_mStack_row, Rsv.hiPt_self]

/-- (+) **Per matrix, both directions**: `N2 ← N4` (a 22-coordinate parent, `N4`'s 23-coordinate
matrix: coordinate 22 is the claim's, fixed) and `N4 ← N2` (a 23-coordinate parent, `N2`'s
22-coordinate matrix: constant in coordinate 22). -/
theorem kindChange_mat (E : Eval.Entries) {b : ℕ} (p : ℕ → F) (σ : Fin b → F) :
    mle (fun x : Fin (2 ^ e2R .N2) => Eval.matMLE E (Rsv.lowA (e2R .N4) (Rsv.hiPt (cube x) p)) σ)
        (Rsv.lowA (e2R .N2) p) = Eval.matMLE E (Rsv.lowA (e2R .N4) p) σ ∧
      mle (fun x : Fin (2 ^ e2R .N4) => Eval.matMLE E (Rsv.lowA (e2R .N2) (Rsv.hiPt (cube x) p)) σ)
        (Rsv.lowA (e2R .N4) p) = Eval.matMLE E (Rsv.lowA (e2R .N2) p) σ := by
  refine ⟨?_, ?_⟩ <;> rw [Rsv.matMLE_hiRow, Rsv.hiPt_self]

/-- The two parents' row counts: `N2` sums over 22 coordinates, `N4` over 23 (so `kindChange_mat` is
the fixed evaluation one way and the constant extension the other). -/
theorem e2R_N2_N4 : e2R .N2 = 22 ∧ e2R .N4 = 23 := ⟨rfl, rfl⟩

/-! ## `N8`'s zero claim -/

/-- (+) **The zero claim is true** (`N8` writes `fLrEnd[48, 1008) = 0`): with every claim value `0`,
`X = 0 = Σ_i 0·M̃_i(p)`, so `truthChild4` holds and `ChildBad4` fails. -/
theorem n8_zero (srcE : NodeKind → ESrc) {L es : Log} (h0 : ∀ i < 60, rsvV es i = 0) :
    truthChild4 srcE es ∧ ¬ ChildBad4 srcE L es := by
  obtain ⟨-, -, hs, hx⟩ := child_rsvV es
  have hs0 : ∀ i < 9, sL es i = 0 := fun i hi => by rw [hs]; exact h0 _ (by omega)
  have ht : truthChild4 srcE es := by
    rw [truthChild4, hx, h0 57 (by norm_num)]
    simp only [mStack, NodeKind.all, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil]
    simp [hs0, NodeKind.ix]
  exact ⟨ht, fun ⟨_, _, _, h⟩ => h ht⟩

/-- (−) … and a nonzero `X` on zero coefficients is a false claim. -/
theorem n8_neg (srcE : NodeKind → ESrc) {es : Log} (hs : ∀ i < 9, sL es i = 0) (hx : xL es ≠ 0) :
    ¬ truthChild4 srcE es := by
  rw [truthChild4]
  simp only [mStack, NodeKind.all, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil]
  simpa [hs, NodeKind.ix] using hx

end FR.Snd.P4b
