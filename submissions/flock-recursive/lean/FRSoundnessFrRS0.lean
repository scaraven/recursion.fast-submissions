-- New for `flock-recursive` (BLUEPRINT A.10 RS0, §5.2 row RS0; stage S-G6).
-- RET-2: the declarations revision 4.1 reads moved to `FRSoundnessCoreRows`.
import FRSoundnessFrRS
import FRSoundnessCoreFront

/-!
# RS0: the column checks (`habs` at RS0's absorb, position 312) and `RejF`'s slice part

The RS claim values have no message of their own: `finRS` *computes* `α_j = Σ_i c_{j,i} s_{j,i}`
from RS0's slices (`rsAlpha`), and the other finals bind each `α_j` where it is used (`finLc`:
`v_β = α_Lc`; `finSh`: `c_Sh = (w_out + w_in)·α_Sh`; `finE` (iv)–(v): E4 end's value is `α_E`;
`finZ`: `α_Z = P^z*(λ)`, asserted since INT-4, `relZ`). So:

* **`cwL`**: the inner weights `c_{j,i}` on the log (`rsW`'s mirror: `eqZS λ ρ₁`, `eq` at the low
  7 coordinates of Lc's and Sh's points, the packing basis `bb`).
* **`alphaL`** (`α_j` from the slices) and **`trueL`** (the same weights on the true slices
  `Σ_u g_j(u) Q_i(u)`).
* A claim's **binding** is a predicate `ok κ es j v` ("the final that uses claim `j` accepts the
  value `v`"), reading the log before RS0 (`OkReads`). **`PendBad ok`**: some claim's binding fails
  at its true value (the pending claims' doom, E4 end's `DF 22` with `far₀`, `¬ PubOK`:
  **`DPend`**). **`RejRS ok`** (from position 313): some binding fails at the slices' value.
* **`habs_RS0`**: `DPend` before RS0's absorb gives `RejRS` or RS0's doom `DRS0` after it
  (`rs_column`). **`rejRS_ok`**: `RejRS` is a `RejOK` (`rejOK_at`).
-/

namespace FR.Snd
open RecursionFast Finset

set_option linter.constructorNameAsVariable false

/-! ## The inner weights and the two values of a claim -/

/-- **Claim `j`'s value from RS0's slices**, `α_j = Σ_i c_{j,i} s_{j,i}` (`rsAlpha`). -/
def alphaL (κ : Kind) (es : Log) (j : Fin 4) : F := ∑ i : Fin 128, cwL κ es j i * sL κ es j i

/-- **Claim `j`'s true value**: the same weights on the true slices `Σ_u g_j(u) Q_i(u)`. -/
noncomputable def trueL (κ : Kind) (L es : Log) (j : Fin 4) : F :=
  ∑ i : Fin 128, cwL κ es j i *
    ∑ u, gL κ es j u * algebraMap F F (rsQ κ L es (nrP 0 κ) i u)

section Bind

variable (ok : Kind → Log → ℕ → F → Prop)

/-- The bindings read the log before RS0's absorb. -/
def OkReads : Prop := ∀ κ es es', Agree es es' 312 → ok κ es = ok κ es'

/-- **A pending claim is false**: some claim's binding fails at its true value. -/
def PendBad (L es : Log) : Prop :=
  ∃ j : Fin 4, j.val < (rsPtsL (kindOf es) es).length ∧
    ¬ ok (kindOf es) es j (trueL (kindOf es) L es j)

/-- **The doom before RS0** (E4 end's): far, a public cell false, or a pending claim false. -/
def DPend (L es : Log) : Prop :=
  farL (kindOf es) L es 0 ∨ ¬ PubOK (kindOf es) L es ∨ PendBad ok L es

/-- **`RejF`'s slice part** (from position 313): some claim's binding fails at the slices' value
`α_j` (the finals' `assertEq`s on `rsAlpha`). -/
def RejRS (L es : Log) : Prop :=
  313 ≤ es.length ∧ ∃ j : Fin 4, j.val < (rsPtsL (kindOf es) es).length ∧
    ¬ ok (kindOf es) es j (alphaL (kindOf es) es j)

end Bind

/-! ## Reads -/

section Reads
variable {L es L' es' : Log} {p : ℕ}

theorem cwL_congr (h : Agree es es' 312) (κ : Kind) : cwL κ es = cwL κ es' := by
  have hm := Kind.m_le κ
  have h1 : xLL es = xLL es' :=
    List.map_congr_left fun l hl => rch_congr h (by simp at hl; omega)
  have h2 : xSL κ es = xSL κ es' :=
    List.map_congr_left fun l hl => rch_congr h (by simp at hl; omega)
  have h0 : fAt es 14 0 = fAt es' 14 0 := fAt_congr h (by norm_num) 0
  unfold cwL; rw [h0, h1, h2]

theorem alphaL_congr (h : Agree es es' 313) (κ : Kind) : alphaL κ es = alphaL κ es' := by
  funext j; simp only [alphaL, cwL_congr (h.mono (by norm_num)) κ, sL_congr h κ]

theorem trueL_same (h : Same L es L' es' p) (hp : 312 ≤ p) (κ : Kind) :
    trueL κ L es = trueL κ L' es' := by
  have hq : rsQ κ L es (nrP 0 κ) = rsQ κ L' es' (nrP 0 κ) := by
    funext i u; simp only [rsQ, fF_same h (by omega) κ]
  funext j
  simp only [trueL, cwL_congr (h.1.mono hp) κ, gL_congr (h.1.mono (by omega)) κ, hq]

theorem pubOK_same (h : Same L es L' es' p) (hp : 3 ≤ p) (κ : Kind) :
    PubOK κ L es ↔ PubOK κ L' es' := by
  simp only [PubOK, fF_same h hp κ, vkL, stL, h.1 0 (by omega),
    msgAt_congr h.1 (show 1 < p by omega)]

theorem farL0_same (h : Same L es L' es' p) (hp : 3 ≤ p) (κ : Kind) :
    farL κ L es 0 ↔ farL κ L' es' 0 :=
  farL_same h (i := 0) (by norm_num) κ (by rw [capPos_zero]; omega)

variable {ok : Kind → Log → ℕ → F → Prop}

theorem pendBad_reads (hok : OkReads ok) : Reads 312 (PendBad ok) := fun L es L' es' h1 h2 h => by
  have hk := h.kind (by omega)
  simp only [PendBad, hk, rsPtsL_congr (h.1.mono (by norm_num)), hok _ es es' h.1,
    trueL_same h le_rfl]

theorem dPend_reads (hok : OkReads ok) : Reads 312 (DPend ok) := fun L es L' es' h1 h2 h => by
  have hk := h.kind (by omega)
  unfold DPend
  rw [hk, farL0_same h (by omega), pubOK_same h (by omega), pendBad_reads hok L es L' es' h1 h2 h]

theorem rejRS_reads (hok : OkReads ok) : Reads 313 (RejRS ok) := fun L es L' es' h1 h2 h => by
  have hk := h.kind (by omega)
  simp only [RejRS, hk, rsPtsL_congr (h.1.mono (by norm_num)), hok _ es es' (h.1.mono (by omega)),
    alphaL_congr h.1]
  exact and_congr_left fun _ => ⟨fun _ => h2, fun _ => h1⟩

end Reads

/-! ## `RejOK` for a check from a position on -/

/-- A check that holds from position `p + 1` on and reads the entries before it is a `RejOK`,
when `p` is not a squeeze. -/
theorem rejOK_at {p : ℕ} {P : Log → Log → Prop} (hP : Reads (p + 1) P)
    (hp : fsItems[p]? ≠ some .squeeze) : RejOK fun L es => p + 1 ≤ es.length ∧ P L es where
  mono L es x h := ⟨by simp; omega, (hP.append L es [x] h.1).mpr h.2⟩
  sq L es x hit := by
    by_cases hle : p + 1 ≤ es.length
    · exact and_congr (by simp; omega) (hP.append L es [x] hle)
    · have hne : es.length ≠ p := fun he => hp (he ▸ hit)
      exact ⟨fun h => absurd h.1 (by simp; omega), fun h => absurd h.1 hle⟩
  stab L i hb hci X hX := by
    by_cases hle : p + 1 ≤ X.length
    · exact and_congr Iff.rfl (hP.stab hb hci hX hle)
    · exact ⟨fun h => absurd h.1 hle, fun h => absurd h.1 hle⟩

theorem rejRS_ok {ok : Kind → Log → ℕ → F → Prop} (hok : OkReads ok)
    (hp : fsItems[312]? ≠ some .squeeze) : RejOK (RejRS ok) := by
  have h := rejOK_at (p := 312) (P := fun L es => ∃ j : Fin 4,
    j.val < (rsPtsL (kindOf es) es).length ∧ ¬ ok (kindOf es) es j (alphaL (kindOf es) es j))
    (fun L es L' es' h1 h2 hS => by
      have hk := hS.kind (by omega)
      simp only [hk, rsPtsL_congr (hS.1.mono (by norm_num)), hok _ es es' (hS.1.mono (by omega)),
        alphaL_congr hS.1]) hp
  exact h

/-! ## `habs` at RS0 -/

/-- **`habs` at RS0's absorb** (A.10 RS0, `rs_column`): if a pending claim is false before the
absorb, then after it either a binding fails at the slices' value (`RejRS`), or the slices are
false (`DRS0`). Far words and false public cells carry over. -/
theorem habs_RS0 {ok : Kind → Log → ℕ → F → Prop} (hok : OkReads ok) {L es : Log}
    (x : ByteArray × Digest) (hl : es.length = 312) (hd : DPend ok L es) :
    RejRS ok L (es ++ [x]) ∨ DRS0 L (es ++ [x]) := by
  have hS : Same L (es ++ [x]) L es 312 := hl ▸ same_append L es [x]
  have hk : kindOf (es ++ [x]) = kindOf es := hS.kind (by norm_num)
  have hfar := farL0_same hS (by norm_num) (kindOf es)
  have hpub := pubOK_same hS (by norm_num) (kindOf es)
  rcases hd with h | h | ⟨j, hj, hn⟩
  · exact .inr (.inl (by rw [hk, hfar]; exact h))
  · exact .inr (.inr (.inl (by rw [hk, hpub]; exact h)))
  by_cases hr : RejRS ok L (es ++ [x])
  · exact .inl hr
  refine .inr (.inr (.inr ?_))
  have hag : Agree (es ++ [x]) es 312 := hS.1
  have hok' : ok (kindOf es) (es ++ [x]) = ok (kindOf es) es := hok _ _ _ hag
  have hpts := rsPtsL_congr (hag.mono (by norm_num)) (kindOf es)
  have hα : ok (kindOf es) es j (alphaL (kindOf es) (es ++ [x]) j) := by
    by_contra hc
    exact hr ⟨by simp; omega, j, by rw [hk, hpts]; exact hj, by rw [hk, hok']; exact hc⟩
  have hne : alphaL (kindOf es) (es ++ [x]) j ≠ trueL (kindOf es) L (es ++ [x]) j := by
    rw [trueL_same hS le_rfl]; intro he; exact hn (he ▸ hα)
  have hcol := rs_column (c := fun i => cwL (kindOf es) (es ++ [x]) j i)
    (s := fun i => sL (kindOf es) (es ++ [x]) j i)
    (t := fun i => ∑ u, gL (kindOf es) (es ++ [x]) j u *
      algebraMap F F (rsQ (kindOf es) L (es ++ [x]) (nrP 0 (kindOf es)) i u)) rfl
    (fun he => hne (by unfold alphaL trueL; exact he.symm))
  rw [hk]
  intro ht
  exact hcol (funext fun i => sub_eq_zero.mpr (ht j i))

/-! ## Controls -/

/-- Control (positive): with the bindings at the true values, no pending claim is false. -/
theorem not_pendBad_true (L es : Log) :
    ¬ PendBad (fun κ _ j v => ∀ hj : j < 4, v = trueL κ L es ⟨j, hj⟩) L es := by
  rintro ⟨j, -, hn⟩; exact hn fun _ => rfl

/-- Control (negative, non-vacuous): a binding that refuses every value makes a node's first
claim pending-false and, after RS0, rejected. -/
theorem pendBad_false (L es : Log) : PendBad (fun _ _ _ _ => False) L es :=
  ⟨0, by rw [rsPtsL_length]; split_ifs <;> norm_num, not_false⟩

theorem rejRS_false (L es : Log) (hl : 313 ≤ es.length) : RejRS (fun _ _ _ _ => False) L es :=
  ⟨hl, 0, by rw [rsPtsL_length]; split_ifs <;> norm_num, not_false⟩

/-- Control: the E claim's inner weight is the packing basis. -/
theorem cwL_three (κ : Kind) (es : Log) (i : ℕ) : cwL κ es 3 i = bb i := rfl

/-- Control (positive): with RS0's truth, a claim's slice value is its true value. -/
theorem alphaL_true {κ : Kind} {L es : Log} (h : truthRS0 κ L es (gL κ es) (sL κ es)) (j : Fin 4) :
    alphaL κ es j = trueL κ L es j := by
  unfold alphaL trueL; exact sum_congr rfl fun i _ => by rw [h j i]

/-- Control (negative): zero slices give every claim the value `0`. -/
theorem alphaL_zero {κ : Kind} {es : Log} (h : ∀ j i, sliceL es j i = 0) (j : Fin 4) :
    alphaL κ es j = 0 := by
  unfold alphaL sL; exact sum_eq_zero fun i _ => by split_ifs <;> simp [h]

end FR.Snd
