-- New for `flock-recursive` (BLUEPRINT §5.4, A.10 "What `final` then gets"; stage S-G1h).
-- RET-1: position-free declarations moved to `FRSoundnessCoreHide`.
import FRSoundnessHide
import FRSoundness4TailStep

/-!
# The chain walk: no escape on any prefix carries the doom along a chain (§5.4)

`final` (S-G2) reads an accepted chain backwards: below `1` the potential has no escape, so a doom
that holds on a prefix of the chain holds at its end (and, contrapositively, a doom refuted at the
end is refuted on every prefix). The prefixes are charged on different logs (`L.take j` for the
prefix ending at entry `j`), so the walk transports the doom between them by a stability property
of the doom on chains (`ChainStab`).

* **Part A: logs and their prefixes.** `predIdx_take`, **`pathOf_take`** (a path ending before `t`
  is the same in `L.take t`), `entriesOf_take`, `isChain_take`, **`not_bad_take`** (a prefix of a
  non-bad log is non-bad), **`pathOf_prefix`** (the path to an entry of a path is the path's
  prefix), `pathOf_lt` (paths increase strictly).
* **Part B: the walk.** **`ChainStab D`**: on a non-bad log, `D` reads the same off the log before
  a chain's last entry and off the log, on the chain itself. **`walk_step`**, **`walk_fwd`**:
  with no escape, `D` on the chain's first `m` entries (charged at their last entry) gives `D` on
  the whole chain; **`walk_back`**: `¬ D` at the end gives `¬ D` on every prefix.
* **Part C: the Hide potential's walk.** **`DH_chainStab`** (`noHide_zero`, `capOK_of_matches`,
  `wordK_stab`); **`DH_of_noEsc`**: on a non-bad log with no Hide escape every chain satisfies
  `DH`; **`consSet_eq_of_noEsc`**: so on such a chain past P1.i a close level whose next message
  is the fold has `A_c = jointAgree` (what `final` hands the extractor, §10 changes 14).
-/

namespace FR.Snd
open RecursionFast FR.Merkle

/-! ## Part A: logs and their prefixes -/

theorem isChain_take {L : Log} {j : ℕ} (h : IsChain L j) {t : ℕ} (ht : j < t) :
    IsChain (L.take t) j :=
  ⟨by simp; exact ⟨ht, h.1⟩, by rw [entriesOf_pathOf_take L ht]; exact h.2⟩

/-! ## Part B: the walk -/

/-- **Stability of a doom on chains**: on a non-bad log, `D` reads the same off the log before a
chain's last entry and off the log, on the chain itself (the reads of A.10's `hstab` column, on
the real chain). -/
def ChainStab (D : Log → Log → Prop) : Prop :=
  ∀ L j, ¬ Bad L → IsChain L j →
    (D (L.take j) (entriesOf L (pathOf L j)) ↔ D L (entriesOf L (pathOf L j)))

/-- A nonempty prefix of a matching chain matches. -/
theorem matches_take {es : Log} (h : Matches es) : ∀ d k, es.length = k + d → 1 ≤ k →
    Matches (es.take k) := by
  intro d
  induction d with
  | zero => intro k hk _; rw [List.take_of_length_le (by omega)]; exact h
  | succ d ih =>
    intro k hk h1
    have h' := ih (k + 1) (by omega) (by omega)
    rw [List.take_add_one, List.getElem?_eq_getElem (by omega), Option.toList_some] at h'
    exact matches_of_append (fun he => by
      have := congrArg List.length he; rw [List.length_take, List.length_nil] at this; omega) h'

theorem isChain_prefix {L : Log} {i : ℕ} (hci : IsChain L i) {m : ℕ}
    (hm : m < (pathOf L i).length) : IsChain L (pathOf L i)[m] := by
  refine ⟨lt_of_le_of_lt (mem_pathOf_le (List.getElem_mem _)) hci.1, ?_⟩
  rw [entriesOf_prefix L i hm]
  exact matches_take hci.2 ((pathOf L i).length - (m + 1)) (m + 1)
    (by rw [length_entriesOf]; omega) (by omega)

/-- **One step of the walk**: with no escape, `D` on the chain's first `m + 1` entries (charged at
the `(m+1)`-th) gives `D` on its first `m + 2` (charged at the `(m+2)`-th). -/
theorem walk_step {D : Log → Log → Prop} (hS : ChainStab D) {L : Log} (hb : ¬ Bad L)
    (hE : ¬ EscG D L) {i : ℕ} (hci : IsChain L i) {m : ℕ} (hm : m + 1 < (pathOf L i).length)
    (hD : D (L.take (pathOf L i)[m]) ((entriesOf L (pathOf L i)).take (m + 1))) :
    D (L.take (pathOf L i)[m + 1]) ((entriesOf L (pathOf L i)).take (m + 2)) := by
  set p := pathOf L i
  set es := entriesOf L p
  have hlt : p[m] < p[m + 1] := pathOf_lt hm
  -- transport `D` on the `(m+1)`-prefix from `L.take p[m]` to `L.take p[m+1]`
  have hb' := not_bad_take hb p[m + 1]
  have hc' : IsChain (L.take p[m + 1]) p[m] := isChain_take (isChain_prefix hci (by omega)) hlt
  have key := hS _ _ hb' hc'
  rw [List.take_take, min_eq_left hlt.le, entriesOf_pathOf_take L hlt,
    entriesOf_prefix L i (by omega)] at key
  have hD' := key.mp hD
  -- no escape at the chain of `p[m+1]`
  by_contra hnd
  refine hE ⟨p[m + 1], mem_chains.mpr (isChain_prefix hci hm), ?_⟩
  rw [entriesOf_prefix L i hm]
  refine ⟨by rw [List.length_take, length_entriesOf]; omega, ?_, hnd⟩
  rw [List.dropLast_eq_take, List.length_take, length_entriesOf, List.take_take,
    show min (m + 2) p.length - 1 = m + 1 by omega, min_eq_left (by omega)]
  exact hD'

/-- **The walk forwards**: with no escape, `D` on a prefix carries to the whole chain (charged at
its last entry). -/
theorem walk_fwd {D : Log → Log → Prop} (hS : ChainStab D) {L : Log} (hb : ¬ Bad L)
    (hE : ¬ EscG D L) {i : ℕ} (hci : IsChain L i) {m : ℕ} (hm : m < (pathOf L i).length)
    (hD : D (L.take (pathOf L i)[m]) ((entriesOf L (pathOf L i)).take (m + 1))) :
    D (L.take i) (entriesOf L (pathOf L i)) := by
  have hn : ∀ d, ∀ m (hm : m < (pathOf L i).length), (pathOf L i).length - (m + 1) = d →
      D (L.take (pathOf L i)[m]) ((entriesOf L (pathOf L i)).take (m + 1)) →
      D (L.take i) (entriesOf L (pathOf L i)) := by
    intro d
    induction d with
    | zero =>
      intro m hm hd hD
      have hlast : (pathOf L i)[m] = i := by
        have := pathOf_getLast? L i
        rw [List.getLast?_eq_getElem?] at this
        have h2 : (pathOf L i)[m]? = some i := by
          rw [show m = (pathOf L i).length - 1 by omega]; exact this
        rw [List.getElem?_eq_getElem hm] at h2
        exact Option.some.inj h2
      rw [hlast, List.take_of_length_le (l := entriesOf L (pathOf L i))
        (by rw [length_entriesOf]; omega)] at hD
      exact hD
    | succ d ih =>
      intro m hm hd hD
      exact ih (m + 1) (by omega) (by omega) (walk_step hS hb hE hci (by omega) hD)
  exact hn _ m hm rfl hD

/-- **The walk backwards** (A.10: "by induction from Pf upwards"): with no escape, `¬ D` at the
chain's end gives `¬ D` on every prefix. -/
theorem walk_back {D : Log → Log → Prop} (hS : ChainStab D) {L : Log} (hb : ¬ Bad L)
    (hE : ¬ EscG D L) {i : ℕ} (hci : IsChain L i) (hend : ¬ D (L.take i) (entriesOf L (pathOf L i)))
    {m : ℕ} (hm : m < (pathOf L i).length) :
    ¬ D (L.take (pathOf L i)[m]) ((entriesOf L (pathOf L i)).take (m + 1)) :=
  fun hD => hend (walk_fwd hS hb hE hci hm hD)

/-! ## Part C: the Hide potential's walk -/

/-- **The Hide doom is stable on chains**: before P1.i a level holds on both logs; after, the
chain's cap is a real entry (`capOK_of_matches`), so the word reads the same (`wordK_stab`). -/
theorem DH_chainStab : ChainStab DH := by
  intro L j hb hci
  refine forall₂_congr fun i hi => ?_
  set es := entriesOf L (pathOf L j)
  by_cases h0 : hRnd es i = 0
  · exact ⟨fun _ => noHide_zero h0, fun _ => noHide_zero h0⟩
  have hl : capPos i < es.length := by
    have := capPos_lt hi; unfold hRnd at h0; omega
  have hc := capOK_of_matches hci.2 hi hl
  have hes : ext (es.take es.length) [] = es := by rw [ext_nil, List.take_length]
  have hw := wordK_stab hb hci es.length [] hi (kindOf es) (by rw [hes]; exact hc)
  rw [hes] at hw
  have hd := decodeL_congr hw
  unfold noHide hDiff farL
  rw [hw, hd]

/-- **No Hide escape keeps `DH` on every chain** (it holds at the seed, `DH_short`). -/
theorem DH_of_noEsc {L : Log} (hb : ¬ Bad L) (hE : ¬ EscG DH L) {i : ℕ} (hci : IsChain L i) :
    DH L (entriesOf L (pathOf L i)) := by
  have hne : 0 < (pathOf L i).length := List.length_pos_iff.mpr (pathOf_ne_nil L i)
  have h0 : DH (L.take (pathOf L i)[0]) ((entriesOf L (pathOf L i)).take (0 + 1)) :=
    DH_short (by
      have := (p1_phase (i := 0) (by norm_num)).hb1
      simp only [List.length_take]; omega)
  exact (DH_chainStab L i hb hci).mp (walk_fwd DH_chainStab hb hE hci hne h0)

/-- **What `final` gets from `μ_Hide`** (§10 changes 14–15): on a non-bad log with no Hide escape,
a chain past P1.i whose level `i` is close and whose next message is the fold has
`A_c = jointAgree`. -/
theorem consSet_eq_of_noEsc {L : Log} (hb : ¬ Bad L) (hE : ¬ EscG DH L) {j : ℕ}
    (hci : IsChain L j) {i : ℕ} (hi : i < 5)
    (hlen : p1Start i + 2 * hEll i ≤ (entriesOf L (pathOf L j)).length)
    (hfar : ¬ farL (kindOf (entriesOf L (pathOf L j))) L (entriesOf L (pathOf L j)) i)
    (hC : truthC (kindOf (entriesOf L (pathOf L j))) L (entriesOf L (pathOf L j)) i) :
    consSet (kindOf (entriesOf L (pathOf L j))) L (entriesOf L (pathOf L j)) i =
      jointAgree (wordK (kindOf (entriesOf L (pathOf L j))) L (entriesOf L (pathOf L j)) i)
        (decodeL (kindOf (entriesOf L (pathOf L j))) L (entriesOf L (pathOf L j)) i) :=
  consSet_eq_of_DH hi hlen (DH_of_noEsc hb hE hci) hfar hC

/-- Control (positive): a doom that reads only the chain is stable. -/
theorem chainStab_const (P : Log → Prop) : ChainStab fun _ es => P es :=
  fun _ _ _ _ => Iff.rfl

end FR.Snd
