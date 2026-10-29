-- New for `flock-recursive` (BLUEPRINT §5.1–§5.2, A.10; stage S-G1e).
-- RET-1: position-free declarations moved to `FRSoundnessCoreSteps`.
-- RET-2: the declarations revision 4.1 reads moved to `FRSoundnessCoreRows`.
import FRSoundnessStepD
import FRSoundnessCoreSteps
import FRSoundnessCoreRows

/-!
# The per-phase dooms, the multi-squeeze bad sets, and `KState.step` for the whole transcript

* **Part A: the multi-squeeze bad sets** (A.10's `hround` rows). `flat_round_le`: escapes that put
  a phase's `2r` coordinates (`coordAt`) in `W` are charged `|W| / 2^(256 r)` (`pairsEquiv`,
  `coords_round_le`). **`seq_round_le`**: a doom on the coordinate list losing `b i` values at
  coordinate `i` (`seq_bad_le`) is charged `Σ b / 2^128`. **`ml_round_le`**: the multilinear zero
  test (`mlDoom`: the table with its first coordinates bound is nonzero; `zerocheck_bad_le`) is
  charged `n / 2^128` (Z1, Lr1, E1, P3). **`rs1_round_le`**: RS1's `(r″, κ)` in a set of
  `c·|F|^7` (`rs1_joint`) is charged `c / 2^128`. `coord_rows_le`: A.10's counts fit `deltaR`.
* **Part B: the phase map.** **`phOf p`** is the phase of position `p` (`fsStarts`); `Dp Dk p` is
  phase `phOf p`'s doom. Checked: `phOf_start`; `phOf_succ` (the phase changes only at a phase
  start), `ms_phOf` (a multi-squeeze phase is one phase).
* **Part C: the multi-squeeze dooms.** **`msD prev fin s0 r`**: inside the phase, the entry's doom;
  at its last answer, `fin`. With every multi-squeeze phase in this form (`MsForm`), `hmid` holds
  at every multi-squeeze position (**`hmid_of_msForm`**), and an escape is "the entry doomed and
  `fin` false" (**`esc_msD`**).
* **Part D: the whole transcript.** **`PhaseObl Rej Dk N`**: the per-phase obligations that are
  left (absorbs and handoffs, single squeezes, each multi-squeeze phase's charge, stability).
  **`kstate_step`**: the library's `KState.step` law at `εD = εR − ε_H` for the potential of
  `DC Rej (Dp Dk)` (`stepObl_compose`, `step_epsD`). `hfin_ml`, `hfin_seq`, `hfin_rs1`, `hfin_p2`
  discharge `PhaseObl.hfin` per phase shape from Part A and `p2_hround`.
* **Part E: the asserted rounds** (degree 2 over F: L2, S2, E4; over K: P1.i, Pf): **`D2`**
  (`Rej ∨ Wrong2` with the check in `Rej`), `D2_append_iff` (absorbs inside the phase), and
  **`D2_single`** (`2·M` escaping answers, `M = 2^128` for F, `1` for K).
-/

namespace FR.Snd
open RecursionFast FR.Merkle Finset
open scoped NNReal

set_option linter.constructorNameAsVariable false

/-! ## Part A: the multi-squeeze bad sets -/

/-! ## Part B: the phase map and the position doom -/

/-- **The phase of Fiat–Shamir position `p`**: the last phase starting at or before `p`
(`fsStarts` is sorted; a phase without Fiat–Shamir items, `Q`, shares its start with the next
phase and is never returned). -/
def phOf (p : ℕ) : ℕ := (fsStarts.filter (· ≤ p)).length - 1

/-- **The position doom** (A.10): position `p`'s doom is the doom of its phase. -/
def Dp (Dk : ℕ → Log → Log → Prop) (p : ℕ) : Log → Log → Prop := Dk (phOf p)

/-- Checked: every phase with Fiat–Shamir items is the phase of its first position. -/
theorem phOf_start : (List.range 52).all (fun k => isQ k || phOf (phStart k) == k) = true := by
  unfold phOf phStart; rw [fsStarts_eq]; decide +kernel

/-- The phase changes only at a phase start. -/
theorem phOf_succ {p : ℕ} (hs : p + 1 ∉ fsStarts) : phOf (p + 1) = phOf p := by
  unfold phOf
  congr 2
  refine List.filter_congr fun x hx => ?_
  have : x ≠ p + 1 := fun h => hs (h ▸ hx)
  simp only [decide_eq_decide]
  omega

/-- Checked: a multi-squeeze phase `(s0, r)` is one phase starting at `s0 + 1`, holding its `r`
positions, with `r ≥ 2`. -/
theorem ms_check : fsRanges.all (fun x => 2 ≤ x.2 && fsStarts.contains (x.1 + 1) &&
    (List.range x.2).all fun j => phOf (x.1 + 1 + j) == phOf (x.1 + 1)) = true := by
  unfold phOf; rw [fsRanges_eq, fsStarts_eq]; decide +kernel

theorem ms_phOf {s0 r : ℕ} (h : (s0, r) ∈ fsRanges) :
    2 ≤ r ∧ ∀ p, s0 < p → p ≤ s0 + r → phOf p = phOf (s0 + 1) := by
  have := ms_check
  simp only [List.all_eq_true, Bool.and_eq_true, decide_eq_true_eq, List.mem_range,
    beq_iff_eq] at this
  obtain ⟨⟨h2, -⟩, h3⟩ := this _ h
  refine ⟨h2, fun p h1 hp => ?_⟩
  have := h3 (p - (s0 + 1)) (by simp; omega)
  rwa [show s0 + 1 + (p - (s0 + 1)) = p by omega] at this

/-! ## Part C: the multi-squeeze phases' doom -/

/-- Every multi-squeeze phase's doom has the `msD` form over the doom of its entry. -/
def MsForm (Dk : ℕ → Log → Log → Prop) : Prop :=
  ∀ s0 r, (s0, r) ∈ fsRanges →
    ∃ fin, Dk (phOf (s0 + 1)) = msD (Dk (phOf s0)) fin s0 r

/-- **`hmid` for every multi-squeeze position** (A.10): with every multi-squeeze phase in `msD`
form, a middle answer neither dooms nor undooms. -/
theorem hmid_of_msForm {Dk : ℕ → Log → Log → Prop} (hD : MsForm Dk) (L es : Log)
    (x : ByteArray × Digest) {s0 r : ℕ} (hrnd : fsRnd es.length = some (s0, r))
    (hlt : es.length < s0 + r) : DPos (Dp Dk) L (es ++ [x]) ↔ DPos (Dp Dk) L es := by
  obtain ⟨hmem, h1, -⟩ := fsRnd_mem hrnd
  obtain ⟨hr2, hph⟩ := ms_phOf hmem
  obtain ⟨fin, hfin⟩ := hD s0 r hmem
  have hA : DPos (Dp Dk) L (es ++ [x]) ↔ Dk (phOf s0) L (es.take (s0 + 1)) := by
    have hl' : (es ++ [x]).length - 1 = es.length := by simp
    unfold DPos Dp
    rw [hl', hph _ h1 hlt.le, hfin]
    unfold msD
    rw [ite_pos' (by simp; omega), List.take_append_of_le_length (by omega)]
  have hB : DPos (Dp Dk) L es ↔ Dk (phOf s0) L (es.take (s0 + 1)) := by
    unfold DPos Dp
    rcases Nat.lt_or_ge (s0 + 1) es.length with h | h
    · rw [hph _ (by omega) (by omega), hfin]
      unfold msD
      rw [ite_pos' (by omega)]
    · rw [show es.length - 1 = s0 by omega, List.take_of_length_le (by omega)]
  rw [hA, hB]

/-- **The escape of a multi-squeeze phase in `msD` form**: the entry is doomed and the phase's
final doom fails. Every `hround` row (`ml_round_le`, `seq_round_le`, `rs1_round_le`,
`p2_hround`) is fed from this. -/
theorem esc_msD {Dk : ℕ → Log → Log → Prop} {s0 r : ℕ} (hmem : (s0, r) ∈ fsRanges)
    {fin : Log → Log → Prop} (hfin : Dk (phOf (s0 + 1)) = msD (Dk (phOf s0)) fin s0 r)
    {L es₀ : Log} (hl : es₀.length = s0 + 1) (as : List Digest) (has : as.length = r)
    (he : EscAtG (DPos (Dp Dk)) L (ext es₀ as)) : Dk (phOf s0) L es₀ ∧ ¬ fin L (ext es₀ as) := by
  obtain ⟨hr2, hph⟩ := ms_phOf hmem
  obtain ⟨-, hd, hnd⟩ := he
  have hlen := length_ext as es₀
  have hne : as ≠ [] := by rintro rfl; simp at has; omega
  have hdl : (ext es₀ as).dropLast.length = s0 + r := by rw [List.length_dropLast]; omega
  have htk : (ext es₀ as).dropLast.take (s0 + 1) = es₀ := by
    rw [ext_dropLast _ hne, ← hl, take_ext]
  unfold DPos Dp at hd hnd
  rw [hdl, hph _ (by omega) (by omega), hfin] at hd
  unfold msD at hd
  rw [ite_pos' (by omega), htk] at hd
  rw [hlen, show es₀.length + as.length - 1 = s0 + r by omega, hph _ (by omega) le_rfl, hfin] at hnd
  unfold msD at hnd
  rw [ite_neg' (by omega)] at hnd
  exact ⟨hd, hnd⟩

/-! ## Part D: the whole transcript: the per-phase obligations and `KState.step` at `εR` -/

open Classical in
/-- **The per-phase obligations of the entry's doom** `DC Rej (Dp Dk)` (A.10). `Rej` is the
failed asserted checks; `Dk k` is phase `k`'s doom; every multi-squeeze phase is in `msD` form
(its `hmid` is then automatic, `hmid_of_msForm`). What is left per phase:
* `habs`: an absorb never undooms, inside a phase or at a phase's first absorb (the handoff of
  A.10: the previous phase's doom gives a false initial claim);
* `hsingle`: at a single squeeze (a round's challenge, or a single-squeeze phase's handoff), at
  most `N` answers escape;
* `hfin`: a multi-squeeze phase's charge is at most `deltaR` (`ml_round_le`, `seq_round_le`,
  `rs1_round_le`, `p2_hround`, through `esc_msD`);
* `hstab`: the position's phase doom reads the same off the charging log on `hloc_of`'s
  extensions (`StabExt`: inside a multi-squeeze phase; §10 changes 10, the S-G1g ruling). -/
structure PhaseObl (Rej : Log → Log → Prop) (Dk : ℕ → Log → Log → Prop) (N : ℕ) : Prop where
  rej : RejOK Rej
  ms : MsForm Dk
  habs : ∀ L es x len, Matches (es ++ [x]) → fsItems[es.length]? = some (.absorb len) →
    ¬ Rej L es → Dk (phOf (es.length - 1)) L es →
      Rej L (es ++ [x]) ∨ Dk (phOf es.length) L (es ++ [x])
  hsingle : ∀ L es, Matches es → fsItems[es.length]? = some .squeeze → fsRnd es.length = none →
    ¬ Rej L es →
      (univ.filter fun a => Dk (phOf (es.length - 1)) L es ∧
        ¬ Dk (phOf es.length) L (ext1 es a)).card ≤ N
  hfin : ∀ s0 r, (s0, r) ∈ fsRanges → ∀ L es₀, Matches es₀ → es₀.length = s0 + 1 →
    ¬ Rej L es₀ → condCount (DPos (Dp Dk)) L es₀ r [] ≤ deltaR
  hstab : ∀ k L i, ¬ Bad L → IsChain L i → ∀ X, StabExt fsRnd (entriesOf L (pathOf L i)) X →
    phOf (X.length - 1) = k → (Dk k (L.take i) X ↔ Dk k L X)

open Classical in
/-- **`KState.step` at `εD` for the whole transcript** (BLUEPRINT §5.1, A.10): the potential
`muG` of the entry's doom `DC Rej (Dp Dk)`, charged by `pRoundG … fsRnd`, satisfies the contract's
step law with error `εD = εR − ε_H` (the doom potential's share, §10 changes 15), given the
per-phase obligations and `N ≤ 2^256·deltaR`. -/
theorem kstate_step {Rej : Log → Log → Prop} {Dk : ℕ → Log → Log → Prop} {N : ℕ}
    (hN : (N : ℝ≥0) ≤ 2 ^ 256 * deltaR) (ob : PhaseObl Rej Dk N) (L : Log) (q : ByteArray)
    (hl : L.length < logCap)
    (hμ : muG (DC Rej (Dp Dk)) (pRoundG (DC Rej (Dp Dk)) fsRnd) L < 1)
    (hq : q ∉ L.map Prod.fst) :
    ∑ a : Digest, muG (DC Rej (Dp Dk)) (pRoundG (DC Rej (Dp Dk)) fsRnd) (L ++ [(q, a)]) ≤
      (muG (DC Rej (Dp Dk)) (pRoundG (DC Rej (Dp Dk)) fsRnd) L + epsD) * 2 ^ 256 := by
  refine step_epsD hN (stepObl_compose ob.rej ?_ ?_ ?_ ?_ ?_) L q hl hμ hq
  · intro L es x len hm hit hr hd
    have := ob.habs L es x len hm hit hr hd
    simpa [DPos, Dp] using this
  · intro L es x s0 r _ hrnd hlt _
    exact hmid_of_msForm ob.ms L es x hrnd hlt
  · intro L es hm hit hrnd hr
    have := ob.hsingle L es hm hit hrnd hr
    simpa [DPos, Dp, length_ext1] using this
  · intro L es₀ s0 r hm hl hrnd hr
    exact ob.hfin s0 r (fsRnd_mem hrnd).1 L es₀ hm hl hr
  · intro L i hb hci X hX
    exact ob.hstab _ L i hb hci X hX rfl

/-! ### The multi-squeeze rows in the composition (`hfin` from `esc_msD`) -/

open Classical in
/-- **`hfin` for a multilinear zero-test phase** (Z1, Lr1, E1, P3): the phase's final doom fails
only where the entry's table `t` (nonzero when the entry is doomed) has a vanishing MLE at the
phase's first `n ≤ 239` coordinates. -/
theorem hfin_ml {Dk : ℕ → Log → Log → Prop} {s0 r n : ℕ} (hmem : (s0, r) ∈ fsRanges)
    {fin : Log → Log → Prop} (hfin : Dk (phOf (s0 + 1)) = msD (Dk (phOf s0)) fin s0 r)
    (hn : n ≤ r * 2) (hn' : n ≤ 239) (t : Log → Log → Array F)
    (ht : ∀ L es₀, (t L es₀).size = 2 ^ n)
    (h0 : ∀ L es₀, Dk (phOf s0) L es₀ → tbl n (t L es₀) ≠ 0)
    (hesc : ∀ L es₀ as, es₀.length = s0 + 1 → as.length = r → Dk (phOf s0) L es₀ →
      ¬ fin L (ext es₀ as) →
        ¬ mlDoom n (t L es₀) (List.ofFn fun j : Fin (r * 2) => coordAt (ext es₀ as) s0 j))
    (L es₀ : Log) (hl : es₀.length = s0 + 1) : condCount (DPos (Dp Dk)) L es₀ r [] ≤ deltaR := by
  by_cases hd : Dk (phOf s0) L es₀
  · refine (ml_round_le hl hn (ht L es₀) (h0 L es₀ hd) fun as has he => ?_).trans
      (coord_le_deltaR hn')
    obtain ⟨hd', hnf⟩ := esc_msD hmem hfin hl as has he
    exact hesc L es₀ as hl has hd' hnf
  · rw [condCount_eq_zero fun as has he => hd (esc_msD hmem hfin hl as has he).1]
    exact zero_le

open Classical in
/-- **`hfin` for RS1** (`rs1_round_le`): the escape puts `(r″, κ)` in a set of at most
`c·|F|^7`, `c ≤ 239`. -/
theorem hfin_rs1 {Dk : ℕ → Log → Log → Prop} {s0 : ℕ} (hmem : (s0, 4) ∈ fsRanges)
    {fin : Log → Log → Prop} (hfin : Dk (phOf (s0 + 1)) = msD (Dk (phOf s0)) fin s0 4)
    {c : ℕ} (hc : c ≤ 239) (P : Log → Log → Finset ((Fin 7 → F) × F))
    (hP : ∀ L es₀, Dk (phOf s0) L es₀ → (P L es₀).card ≤ c * Fintype.card F ^ 7)
    (hesc : ∀ L es₀ as, es₀.length = s0 + 1 → as.length = 4 → Dk (phOf s0) L es₀ →
      ¬ fin L (ext es₀ as) →
        ((fun i : Fin 7 => coordAt (ext es₀ as) s0 i), coordAt (ext es₀ as) s0 7) ∈ P L es₀)
    (L es₀ : Log) (hl : es₀.length = s0 + 1) : condCount (DPos (Dp Dk)) L es₀ 4 [] ≤ deltaR := by
  by_cases hd : Dk (phOf s0) L es₀
  · refine (rs1_round_le hl (P L es₀) (hP L es₀ hd) fun as has he => ?_).trans
      (coord_le_deltaR hc)
    obtain ⟨hd', hnf⟩ := esc_msD hmem hfin hl as has he
    exact hesc L es₀ as hl has hd' hnf
  · rw [condCount_eq_zero fun as has he => hd (esc_msD hmem hfin hl as has he).1]
    exact zero_le

open Classical in
/-- **`hfin` for a Schwartz–Zippel phase with per-coordinate losses** (S1: 26 multilinear
coordinates and the power batch `κ_s`), `Σ b ≤ 239`. -/
theorem hfin_seq {Dk : ℕ → Log → Log → Prop} {s0 r : ℕ} (hmem : (s0, r) ∈ fsRanges)
    {fin : Log → Log → Prop} (hfin : Dk (phOf (s0 + 1)) = msD (Dk (phOf s0)) fin s0 r)
    (b : ℕ → ℕ) (hb : ∑ i ∈ range (r * 2), b i ≤ 239) (Doom : Log → Log → List F → Prop)
    (hstep : ∀ L es₀ l, Doom L es₀ l →
      (univ.filter fun c => ¬ Doom L es₀ (l ++ [c])).card ≤ b l.length)
    (h0 : ∀ L es₀, Dk (phOf s0) L es₀ → Doom L es₀ [])
    (hesc : ∀ L es₀ as, es₀.length = s0 + 1 → as.length = r → Dk (phOf s0) L es₀ →
      ¬ fin L (ext es₀ as) →
        ¬ Doom L es₀ (List.ofFn fun j : Fin (r * 2) => coordAt (ext es₀ as) s0 j))
    (L es₀ : Log) (hl : es₀.length = s0 + 1) : condCount (DPos (Dp Dk)) L es₀ r [] ≤ deltaR := by
  by_cases hd : Dk (phOf s0) L es₀
  · refine (seq_round_le hl (Doom L es₀) b (hstep L es₀) (h0 L es₀ hd) fun as has he => ?_).trans
      (coord_le_deltaR hb)
    obtain ⟨hd', hnf⟩ := esc_msD hmem hfin hl as has he
    exact hesc L es₀ as hl has hd' hnf
  · rw [condCount_eq_zero fun as has he => hd (esc_msD hmem hfin hl as has he).1]
    exact zero_le

open Classical in
/-- **`hfin` for P2.i** (`p2_hround`): the escape puts every queried position in a set `S` with
`|S| + eᵢ < nᵢ` (the consistency set of a doomed level, `consSet_card_of_not`). -/
theorem hfin_p2 (κ : Kind) (i : ℕ) (hi : i < 5) {Dk : ℕ → Log → Log → Prop} {s0 : ℕ}
    (hmem : (s0, (lvlStar i).sq) ∈ fsRanges) {fin : Log → Log → Prop}
    (hfin : Dk (phOf (s0 + 1)) = msD (Dk (phOf s0)) fin s0 (lvlStar i).sq)
    (S : Log → Log → Finset (Fin (2 ^ (lvl κ i).logN)))
    (hS : ∀ L es₀, Dk (phOf s0) L es₀ → (S L es₀).card + lvE κ i < lvN κ i)
    (hesc : ∀ L es₀ as, es₀.length = s0 + 1 → as.length = (lvlStar i).sq → Dk (phOf s0) L es₀ →
      ¬ fin L (ext es₀ as) → ∀ k < (lvl κ i).t,
        posAt (ext es₀ as) s0 (lvl κ i).logN (lvl κ i).per k ∈ (S L es₀).map Fin.valEmbedding)
    (L es₀ : Log) (hl : es₀.length = s0 + 1) :
    condCount (DPos (Dp Dk)) L es₀ (lvlStar i).sq [] ≤ deltaR := by
  by_cases hd : Dk (phOf s0) L es₀
  · refine p2_hround κ i hi hl (S L es₀) (hS L es₀ hd) fun as has he => ?_
    obtain ⟨hd', hnf⟩ := esc_msD hmem hfin hl as has he
    exact hesc L es₀ as hl has hd' hnf
  · rw [condCount_eq_zero fun as has he => hd (esc_msD hmem hfin hl as has he).1]
    exact zero_le

/-! ## Part E: the asserted rounds (degree 2 over F: L2, S2, E4; over K: P1.i, Pf)

Round `l`'s message is `c₀ ‖ c₁ ‖ c₂` (coefficients of width `wd` read by `rd`); the verifier
asserts `g(0) + g(1) = claim` (`c₁ + c₂ = claim` in characteristic two), so under `¬ Rej` the
check of every answered round holds (`Rej` contains these asserts); the next claim is `g(r)` with
`r = ch` of the squeeze answer. Unlike `D3`, the round message does not complete itself from the
claim, which is why the doom is `Rej ∨ Wrong2` (A.10). -/

section Rounds2

variable {R : Type*} [Field R]
variable (b wd : ℕ) (rd : ByteArray → ℕ → R) (ch : Digest → R)

variable (c0 : Log → Log → R)

variable (nr : Kind → ℕ) (e : Expr) (T : Log → Log → Array (Array R))

variable {b wd rd ch c0 nr e T}

end Rounds2

/-! ## Controls -/

/-- Control: the phase map at a few positions (Z1's last squeeze, Z2's absorb, P3.0's first
squeeze after the column queries, Pf's last round). -/
theorem phOf_examples : phOf 12 = 3 ∧ phOf 13 = 4 ∧ phOf 356 = 30 ∧ phOf 467 = 51 := by
  unfold phOf; rw [fsStarts_eq]; decide

/-- Control (positive, satisfiability): the empty doom meets every per-phase obligation with
`N = 0` (the structure is not contradictory). -/
theorem phaseObl_false : PhaseObl (fun _ _ => False) (fun _ _ _ => False) 0 where
  rej := rejOK_false
  ms s0 r _ := ⟨fun _ _ => False, by
    funext L es; simp only [msD, eq_iff_iff]; split_ifs <;> exact Iff.rfl⟩
  habs _ _ _ _ _ _ _ h := h.elim
  hsingle _ _ _ _ _ _ := by simp
  hfin _ _ _ L es₀ _ _ _ := by
    rw [condCount_eq_zero fun _ _ h => h.2.1]; exact zero_le
  hstab _ _ _ _ _ _ _ _ := Iff.rfl

/-- Control (positive): a false initial claim dooms the asserted rounds at their first absorb. -/
theorem D2_first_absorb (nr : Kind → ℕ) (L : Log) :
    D2 15 16 readF (fun a => chF a 0) (fun _ _ => (1 : F)) nr (.var 0) (fun _ _ => #[]) L
      (List.replicate 16 default) := by
  refine ⟨by simp, ?_⟩
  simp [Wrong2, ans3, clR2, trueSum, tbl, rchs2, bindAll, Expr.eval]

/-- Control (negative): before the phase's first absorb nothing is doomed. -/
theorem not_D2_before (nr : Kind → ℕ) (L : Log) (c0 : Log → Log → F)
    (T : Log → Log → Array (Array F)) (e : Expr) :
    ¬ D2 15 16 readF (fun a => chF a 0) c0 nr e T L (List.replicate 15 default) :=
  not_D2_short (by simp)

end FR.Snd
