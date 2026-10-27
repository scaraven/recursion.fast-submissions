-- New for `flock-recursive` (BLUEPRINT §5.1–§5.2, A.10; stage S-G1e).
import FRSoundnessStepD

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
  **`kstate_step`**: the contract's `KState.step` law at `εD = εR − ε_H` for the potential of
  `DC Rej (Dp Dk)` (`stepObl_compose`, `step_epsD`). `hfin_ml`, `hfin_seq`, `hfin_rs1`, `hfin_p2`
  discharge `PhaseObl.hfin` per phase shape from Part A and `p2_hround`.
* **Part E: the asserted rounds** (degree 2 over F: L2, S2, Lr4; over K: P1.i, Pf): **`D2`**
  (`Rej ∨ Wrong2` with the check in `Rej`), `D2_append_iff` (absorbs inside the phase), and
  **`D2_single`** (`2·M` escaping answers, `M = 2^128` for F, `1` for K).
-/

namespace FR.Snd
open RecursionFast FR.Merkle Finset
open scoped NNReal

set_option linter.constructorNameAsVariable false

/-! ## Part A: the multi-squeeze bad sets -/

/-- `r` coordinate pairs as `2r` coordinates, pair `s`'s coordinate `c` at `2s + c`. -/
def pairsEquiv (r : ℕ) : (Fin r → F × F) ≃ (Fin (r * 2) → F) :=
  (Equiv.arrowCongr (Equiv.refl _) (finTwoArrowEquiv F).symm).trans
    ((Equiv.curry _ _ _).symm.trans (Equiv.arrowCongr finProdFinEquiv (Equiv.refl F)))

theorem pairsEquiv_apply {r : ℕ} (u : Fin r → F × F) (j : Fin (r * 2)) :
    pairsEquiv r u j =
      if j.val % 2 = 0 then (u ⟨j / 2, by omega⟩).1 else (u ⟨j / 2, by omega⟩).2 := by
  simp only [pairsEquiv, Equiv.trans_apply, Equiv.arrowCongr_apply, Equiv.refl_symm,
    Equiv.coe_refl, Function.comp_apply, Equiv.curry_symm_apply, Function.uncurry_apply_pair,
    finTwoArrowEquiv_symm_apply, finProdFinEquiv_symm_apply, id]
  rcases Nat.mod_two_eq_zero_or_one j.val with h | h
  · have : Fin.modNat j = 0 := Fin.ext (by simp [Fin.modNat, h])
    simp [this, h, Fin.divNat]
  · have : Fin.modNat j = 1 := Fin.ext (by simp [Fin.modNat, h])
    simp [this, h, Fin.divNat]

open Classical in
/-- **The flattened coordinate row**: if a multi-squeeze phase's escape puts its `2r` coordinates
(`coordAt`) in a set `W`, its conditional count from the entry is at most `|W| / 2^(256 r)`. -/
theorem flat_round_le {D : Log → Log → Prop} {L es₀ : Log} {s0 r : ℕ}
    (hl : es₀.length = s0 + 1) (W : Finset (Fin (r * 2) → F))
    (hesc : ∀ as : List Digest, as.length = r → EscAtG D L (ext es₀ as) →
      (fun j : Fin (r * 2) => coordAt (ext es₀ as) s0 j) ∈ W) :
    condCount D L es₀ r [] ≤ (W.card : ℝ≥0) / 2 ^ (256 * r) := by
  have hB := coords_round_le (D := D) (L := L) hl (W.map (pairsEquiv r).symm.toEmbedding)
    fun as has hE => by
      rw [Finset.mem_map_equiv, Equiv.symm_symm]
      convert hesc as has hE using 1
      funext j
      rw [pairsEquiv_apply, coordAt]
      rcases Nat.mod_two_eq_zero_or_one j.val with h | h <;> simp [h]
  rwa [Finset.card_map] at hB

open Classical in
/-- **The Schwartz–Zippel row** (`seq_bad_le`): if a doom on the coordinate list holds at the
entry, loses at most `b i` values at coordinate `i`, and fails at every escape, the phase's charge
is at most `Σ_{i < 2r} b i / 2^128`. -/
theorem seq_round_le {D : Log → Log → Prop} {L es₀ : Log} {s0 r : ℕ}
    (hl : es₀.length = s0 + 1) (Doom : List F → Prop) (b : ℕ → ℕ)
    (hb : ∀ l, Doom l → (univ.filter fun c => ¬ Doom (l ++ [c])).card ≤ b l.length)
    (h0 : Doom [])
    (hesc : ∀ as : List Digest, as.length = r → EscAtG D L (ext es₀ as) →
      ¬ Doom (List.ofFn fun j : Fin (r * 2) => coordAt (ext es₀ as) s0 j)) :
    condCount D L es₀ r [] ≤ ((∑ i ∈ range (r * 2), b i : ℕ) : ℝ≥0) / 2 ^ 128 := by
  set W := univ.filter fun w : Fin (r * 2) → F => ¬ Doom (List.ofFn w)
  have h1 := flat_round_le (D := D) (L := L) hl W fun as has hE => by
    simp only [W, mem_filter, mem_univ, true_and]; exact hesc as has hE
  have h2 := seq_bad_le Doom b hb (r * 2) [] h0
  simp only [List.nil_append, List.length_nil, zero_add, F.card_F] at h2
  refine h1.trans ?_
  rw [div_le_div_iff₀ (by positivity) (by positivity)]
  have h3 : (W.card : ℝ≥0) * 2 ^ 128 ≤ (∑ i ∈ range (r * 2), b i : ℕ) * (2 ^ 128) ^ (r * 2) := by
    exact_mod_cast h2
  calc (W.card : ℝ≥0) * 2 ^ 128 ≤ _ := h3
    _ = _ := by rw [← pow_mul]; ring_nf


/-- A table with its first variables bound to `cs`, in order (`bind0` each). -/
def bindL {R : Type*} [CommRing R] (t : Array R) : List R → Array R
  | [] => t
  | c :: cs => bindL (bind0 t c) cs

theorem bindL_append {R : Type*} [CommRing R] (t : Array R) (cs : List R) (c : R) :
    bindL t (cs ++ [c]) = bind0 (bindL t cs) c := by
  induction cs generalizing t with
  | nil => rfl
  | cons c' cs ih => exact ih _

theorem bindL_size {R : Type*} [CommRing R] {n : ℕ} :
    ∀ (cs : List R) (t : Array R), t.size = 2 ^ (cs.length + n) → (bindL t cs).size = 2 ^ n
  | [], t, h => by rw [bindL]; simpa using h
  | c :: cs, t, h => bindL_size cs _ (by
      rw [bind0_size, h, List.length_cons, show cs.length + 1 + n = (cs.length + n) + 1 by omega,
        pow_succ, Nat.mul_div_cancel _ two_pos])

/-- **The multilinear zero test's doom** over a table of `n` variables: with the first coordinates
bound (at most `n`), the table is not zero. At `n` coordinates this is "the MLE of `t` at the
point is nonzero". -/
def mlDoom {R : Type*} [CommRing R] (n : ℕ) (t : Array R) (l : List R) : Prop :=
  tbl (n - (l.take n).length) (bindL t (l.take n)) ≠ 0

open Classical in
/-- Each coordinate loses at most one value (`zerocheck_bad_le`, `tbl_bind0`); past `n`, none. -/
theorem mlDoom_step {R : Type*} [Field R] [Fintype R] [DecidableEq R] {n : ℕ} {t : Array R}
    (ht : t.size = 2 ^ n) (l : List R) (hd : mlDoom n t l) :
    (univ.filter fun c => ¬ mlDoom n t (l ++ [c])).card ≤ if l.length < n then 1 else 0 := by
  by_cases hl : l.length < n
  · simp only [hl, ↓reduceIte]
    have hlk : l.take n = l := List.take_of_length_le (by omega)
    obtain ⟨m, hm⟩ : ∃ m, n - l.length = m + 1 := ⟨n - l.length - 1, by omega⟩
    have hsz : (bindL t l).size = 2 ^ (m + 1) := bindL_size l t (by rw [ht]; congr 1; omega)
    have hd' : tbl (m + 1) (bindL t l) ≠ 0 := by
      rw [mlDoom, hlk, hm] at hd; exact hd
    refine le_trans (card_le_card fun c hc => ?_) (zerocheck_bad_le _ hd')
    simp only [mem_filter, mem_univ, true_and, mlDoom, not_not] at hc ⊢
    rw [List.take_of_length_le (by simp; omega), bindL_append, List.length_append,
      List.length_singleton, show n - (l.length + 1) = m by omega, tbl_bind0 _ _ hsz] at hc
    exact hc
  · simp only [hl, ↓reduceIte, Nat.le_zero, Finset.card_eq_zero, filter_eq_empty_iff, mem_univ,
      true_implies, not_not]
    intro c
    rw [mlDoom, List.take_append_of_le_length (by omega)]
    exact hd

open Classical in
/-- **The multilinear row** (Z1, Lr1, E1, P3; A.10): if at the entry the table `t` of `n ≤ 2r`
variables is nonzero and every escape makes its MLE vanish at the phase's first `n`
coordinates, the phase's charge is at most `n / 2^128`. -/
theorem ml_round_le {D : Log → Log → Prop} {L es₀ : Log} {s0 r n : ℕ}
    (hl : es₀.length = s0 + 1) (hn : n ≤ r * 2) {t : Array F} (ht : t.size = 2 ^ n)
    (h0 : tbl n t ≠ 0)
    (hesc : ∀ as : List Digest, as.length = r → EscAtG D L (ext es₀ as) →
      ¬ mlDoom n t (List.ofFn fun j : Fin (r * 2) => coordAt (ext es₀ as) s0 j)) :
    condCount D L es₀ r [] ≤ (n : ℝ≥0) / 2 ^ 128 := by
  have h := seq_round_le hl (mlDoom n t) (fun i => if i < n then 1 else 0)
    (fun l hd => mlDoom_step ht l hd) (by cases n <;> exact h0) hesc
  refine h.trans (le_of_eq ?_)
  have : (∑ i ∈ range (r * 2), if i < n then 1 else 0) = n := by
    rw [Finset.sum_boole, show (range (r * 2)).filter (· < n) = range n by
      ext i; simp only [mem_filter, mem_range]; omega, card_range, Nat.cast_id]
  rw [this]


open Classical in
/-- **The ring-switching row** (RS1, 4 squeezes: `r″` = coordinates `0 … 6`, `κ` = coordinate
`7`): if the escape puts `(r″, κ)` in a set of at most `c·|F|^7` pairs (`rs1_joint`), the
phase's charge is at most `c / 2^128`. -/
theorem rs1_round_le {D : Log → Log → Prop} {L es₀ : Log} {s0 : ℕ} (hl : es₀.length = s0 + 1)
    (P : Finset ((Fin 7 → F) × F)) {c : ℕ} (hP : P.card ≤ c * Fintype.card F ^ 7)
    (hesc : ∀ as : List Digest, as.length = 4 → EscAtG D L (ext es₀ as) →
      ((fun i : Fin 7 => coordAt (ext es₀ as) s0 i), coordAt (ext es₀ as) s0 7) ∈ P) :
    condCount D L es₀ 4 [] ≤ (c : ℝ≥0) / 2 ^ 128 := by
  let pr : (Fin (4 * 2) → F) → (Fin 7 → F) × F := fun w => (Fin.init (n := 7) w, w (Fin.last 7))
  set W := univ.filter fun w : Fin (4 * 2) → F => pr w ∈ P
  have h1 := flat_round_le (D := D) (L := L) hl W fun as has hE => by
    simp only [W, mem_filter, mem_univ, true_and]; exact hesc as has hE
  have hinj : Set.InjOn pr W := fun w _ w' _ he => by
    have e1 := congrArg Prod.fst he; have e2 := congrArg Prod.snd he
    rw [← Fin.snoc_init_self (n := 7) w, ← Fin.snoc_init_self (n := 7) w']
    exact congrArg₂ (fun a b => Fin.snoc (α := fun _ => F) a b) e1 e2
  have h2 : W.card ≤ P.card := card_le_card_of_injOn pr (fun w hw => by
    simp only [W, coe_filter, mem_univ, true_and] at hw; exact hw) hinj
  rw [F.card_F] at hP
  refine h1.trans ?_
  rw [div_le_div_iff₀ (by positivity) (by positivity)]
  have h3 : (W.card : ℝ≥0) ≤ c * (2 ^ 128) ^ 7 := by exact_mod_cast h2.trans hP
  calc (W.card : ℝ≥0) * 2 ^ 128 ≤ c * (2 ^ 128) ^ 7 * 2 ^ 128 :=
        mul_le_mul_of_nonneg_right h3 (by positivity)
    _ = c * 2 ^ (256 * 4) := by
      rw [mul_assoc, ← pow_succ, ← pow_mul, show 128 * (7 + 1) = 256 * 4 by norm_num]

/-- A coordinate row of at most `239` bad values per `2^128` fits the rows' budget `deltaR`
(`εR − 2·2^-142 − 2^-238 ≈ 239.9998 / 2^128`). -/
theorem coord_le_deltaR {c : ℕ} (hc : c ≤ 239) : (c : ℝ≥0) / 2 ^ 128 ≤ deltaR := by
  rw [← NNReal.coe_le_coe, NNReal.coe_div, deltaR_coe]
  push_cast
  have : (c : ℝ) ≤ 239 := by exact_mod_cast hc
  rw [div_le_iff₀ (by positivity)]
  norm_num
  linarith

/-- **The Ligerito and PIOP coordinate rows fit `deltaR`** (A.10's counts: Z1 `≤ 20`, S1 `33`,
Lr1 `15`, RS1 `10`, E1 `21`, P3 `9`). -/
theorem coord_rows_le : ∀ c ∈ [20, 33, 15, 10, 21, 9], (c : ℝ≥0) / 2 ^ 128 ≤ deltaR :=
  fun c hc => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl | rfl | rfl | rfl | rfl <;> exact coord_le_deltaR (by norm_num)


/-! ## Part B: the phase map and the position doom -/

/-- **The phase of Fiat–Shamir position `p`**: the last phase starting at or before `p`
(`fsStarts` is sorted; a phase without Fiat–Shamir items, `Q`, shares its start with the next
phase and is never returned). -/
def phOf (p : ℕ) : ℕ := (fsStarts.filter (· ≤ p)).length - 1

/-- **The position doom** (A.10): position `p`'s doom is the doom of its phase. -/
def Dp (Dk : ℕ → Log → Log → Prop) (p : ℕ) : Log → Log → Prop := Dk (phOf p)

/-- The phases with no Fiat–Shamir item (each level's `Q`). -/
def isQ (k : ℕ) : Bool := 28 ≤ k && k ≤ 48 && (k - 28) % 5 == 0

/-- Checked: every phase with Fiat–Shamir items is the phase of its first position. -/
theorem phOf_start : (List.range 51).all (fun k => isQ k || phOf (phStart k) == k) = true := by
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

/-- **A multi-squeeze phase's doom** (A.10's `hround` rows): on a chain ending inside the phase
(before its last answer), the doom of the phase's entry `prev` there; at its last answer, `fin`. -/
def msD (prev fin : Log → Log → Prop) (s0 r : ℕ) (L es : Log) : Prop :=
  if es.length ≤ s0 + r then prev L (es.take (s0 + 1)) else fin L es

/-- Every multi-squeeze phase's doom has the `msD` form over the doom of its entry. -/
def MsForm (Dk : ℕ → Log → Log → Prop) : Prop :=
  ∀ s0 r, (s0, r) ∈ fsRanges →
    ∃ fin, Dk (phOf (s0 + 1)) = msD (Dk (phOf s0)) fin s0 r

theorem ite_pos' {α : Sort*} {p : Prop} [Decidable p] (h : p) (a b : α) :
    (if p then a else b) = a := by simp [h]

theorem ite_neg' {α : Sort*} {p : Prop} [Decidable p] (h : ¬ p) (a b : α) :
    (if p then a else b) = b := by simp [h]

/-- A formal extension keeps its chain as a prefix. -/
theorem take_ext (es₀ : Log) : ∀ as : List Digest, (ext es₀ as).take es₀.length = es₀ := by
  intro as
  induction as using List.reverseRecOn with
  | nil => simp [ext_nil]
  | append_singleton as a ih =>
    rw [ext_append, ext1, List.take_append_of_le_length (by rw [length_ext]; omega), ih]

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
* `hstab`: every phase's doom reads the same off the charging log (§10 changes 10). -/
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
  hstab : ∀ k L i, ¬ Bad L → IsChain L i → ∀ k' as,
    (Dk k (L.take i) (ext ((entriesOf L (pathOf L i)).take k') as) ↔
      Dk k L (ext ((entriesOf L (pathOf L i)).take k') as))

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
  · intro L i hb hci k as
    exact ob.hstab _ L i hb hci k as

/-- **Two step laws add** (§10 changes 15: `μ = μ_doom + μ_Hide`): if `μ₁` and `μ₂` each satisfy
the contract's step law (with errors `ε₁`, `ε₂`) wherever they are below `1`, their sum satisfies
it with error `ε₁ + ε₂` wherever the sum is below `1`. -/
theorem step_add {μ₁ μ₂ : Log → ℝ≥0} {ε₁ ε₂ : ℝ≥0}
    (h₁ : ∀ L q, L.length < logCap → μ₁ L < 1 → q ∉ L.map Prod.fst →
      ∑ a : Digest, μ₁ (L ++ [(q, a)]) ≤ (μ₁ L + ε₁) * 2 ^ 256)
    (h₂ : ∀ L q, L.length < logCap → μ₂ L < 1 → q ∉ L.map Prod.fst →
      ∑ a : Digest, μ₂ (L ++ [(q, a)]) ≤ (μ₂ L + ε₂) * 2 ^ 256)
    (L : Log) (q : ByteArray) (hl : L.length < logCap) (hμ : μ₁ L + μ₂ L < 1)
    (hq : q ∉ L.map Prod.fst) :
    ∑ a : Digest, (μ₁ (L ++ [(q, a)]) + μ₂ (L ++ [(q, a)])) ≤
      (μ₁ L + μ₂ L + (ε₁ + ε₂)) * 2 ^ 256 := by
  rw [Finset.sum_add_distrib]
  have a₁ := h₁ L q hl (lt_of_le_of_lt le_self_add hμ) hq
  have a₂ := h₂ L q hl (lt_of_le_of_lt le_add_self hμ) hq
  calc _ ≤ (μ₁ L + ε₁) * 2 ^ 256 + (μ₂ L + ε₂) * 2 ^ 256 := add_le_add a₁ a₂
    _ = _ := by ring

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

/-! ## Part E: the asserted rounds (degree 2 over F: L2, S2, Lr4; over K: P1.i, Pf)

Round `l`'s message is `c₀ ‖ c₁ ‖ c₂` (coefficients of width `wd` read by `rd`); the verifier
asserts `g(0) + g(1) = claim` (`c₁ + c₂ = claim` in characteristic two), so under `¬ Rej` the
check of every answered round holds (`Rej` contains these asserts); the next claim is `g(r)` with
`r = ch` of the squeeze answer. Unlike `D3`, the round message does not complete itself from the
claim, which is why the doom is `Rej ∨ Wrong2` (A.10). -/

section Rounds2

variable {R : Type*} [Field R]
variable (b wd : ℕ) (rd : ByteArray → ℕ → R) (ch : Digest → R)

/-- Round `l`'s coefficients `c₀, c₁, c₂`. -/
def g2At (es : Log) (l : ℕ) : Array R :=
  #[rd (msgAt es (b + 2 * l)) 0, rd (msgAt es (b + 2 * l)) wd, rd (msgAt es (b + 2 * l)) (2 * wd)]

/-- Round `l`'s challenge. -/
def rch2 (es : Log) (l : ℕ) : R := ch (ansAt es (b + 2 * l + 1))

/-- The first `l` challenges. -/
def rchs2 (es : Log) (l : ℕ) : List R := (List.range l).map (rch2 b ch es)

variable (c0 : Log → Log → R)

/-- The running claims: `c0`, then `g_l(r_l)`. -/
def clR2 (L es : Log) : ℕ → R
  | 0 => c0 L es
  | l + 1 => peval (g2At b wd rd es l) (rch2 b ch es l)

variable (nr : Kind → ℕ) (e : Expr) (T : Log → Log → Array (Array R))

/-- The claim after `l` rounds is not the true sum of the bound tables. -/
def Wrong2 (L es : Log) (l : ℕ) : Prop :=
  clR2 b wd rd ch c0 L es l ≠ trueSum e (bindAll (T L es) (rchs2 b ch es l)) (nr (kindOf es) - l)

/-- **The asserted rounds' doom** (A.10's `Wrong2`): past the phase's first absorb, the running
claim after the answered rounds (`ans3`) is false. -/
def D2 (L es : Log) : Prop := b < es.length ∧ Wrong2 b wd rd ch c0 nr e T L es (ans3 b nr es)

/-- Round `l`'s asserted check, as `Rej` must guarantee it. -/
def Chk2 (L es : Log) (l : ℕ) : Prop :=
  peval (g2At b wd rd es l) 0 + peval (g2At b wd rd es l) 1 = clR2 b wd rd ch c0 L es l

variable {b wd rd ch c0 nr e T}

omit [Field R] in
theorem rchs2_congr {es es' : Log} {l : ℕ} (h : Agree es es' (b + 2 * l)) :
    rchs2 b ch es l = rchs2 b ch es' l := by
  unfold rchs2 rch2 ansAt
  refine List.map_congr_left fun j hj => ?_
  rw [h _ (by simp at hj; omega)]

theorem clR2_congr {L es es' : Log} (hc : c0 L es = c0 L es') :
    ∀ {l : ℕ}, Agree es es' (b + 2 * l) → clR2 b wd rd ch c0 L es l = clR2 b wd rd ch c0 L es' l
  | 0, _ => hc
  | l + 1, h => by
    simp only [clR2]
    simp only [g2At, rch2, ansAt, msgAt, h (b + 2 * l) (by omega), h (b + 2 * l + 1) (by omega)]

/-- The truth reads the entries before `b` only. -/
def TruthLocal2 (b : ℕ) (c0 : Log → Log → R) (T : Log → Log → Array (Array R)) : Prop :=
  ∀ L es es', Agree es es' b → T L es = T L es' ∧ c0 L es = c0 L es'

theorem wrong2_congr (hb1 : 1 ≤ b) (hTc : TruthLocal2 b c0 T) {L es es' : Log} {l : ℕ}
    (h : Agree es es' (b + 2 * l)) :
    Wrong2 b wd rd ch c0 nr e T L es l ↔ Wrong2 b wd rd ch c0 nr e T L es' l := by
  have hb := h.mono (show b ≤ b + 2 * l by omega)
  obtain ⟨hT, hc⟩ := hTc L es es' hb
  simp only [Wrong2, clR2_congr hc h, rchs2_congr h, hT, kindOf_congr (hb.mono hb1)]

/-- **`habs` inside the phase**: appending where no real round is answered keeps the doom. -/
theorem D2_append_iff (hb1 : 1 ≤ b) (hTc : TruthLocal2 b c0 T) {L es : Log}
    (x : ByteArray × Digest) (hlen : b < es.length)
    (hc : (es.length - b) % 2 = 0 ∨ nr (kindOf es) ≤ (es.length - b) / 2) :
    D2 b wd rd ch c0 nr e T L (es ++ [x]) ↔ D2 b wd rd ch c0 nr e T L es := by
  have hk := kindOf_append x (show 0 < es.length by omega)
  have ha : ans3 b nr (es ++ [x]) = ans3 b nr es := by
    simp only [ans3, hk, List.length_append, List.length_singleton]
    rcases hc with hc | hc
    · rw [show (es.length + 1 - b) / 2 = (es.length - b) / 2 by omega]
    · rw [min_eq_left hc, min_eq_left (le_trans hc (Nat.div_le_div_right (by omega)))]
  have hle : b + 2 * ans3 b nr es ≤ es.length := by
    have : ans3 b nr es ≤ (es.length - b) / 2 := min_le_right _ _
    omega
  simp only [D2, ha, List.length_append, List.length_singleton]
  rw [wrong2_congr hb1 hTc (agree_append es [x] hle)]
  exact ⟨fun h => ⟨hlen, h.2⟩, fun h => ⟨by omega, h.2⟩⟩

theorem not_D2_short {L es : Log} (h : es.length ≤ b) : ¬ D2 b wd rd ch c0 nr e T L es :=
  fun hd => by have := hd.1; omega

theorem wrong2_ext1 (hb1 : 1 ≤ b) (hTc : TruthLocal2 b c0 T) (L es : Log) (a : Digest) {j : ℕ}
    (hj : es.length = b + 2 * j + 1) :
    Wrong2 b wd rd ch c0 nr e T L (ext1 es a) (j + 1) ↔
      peval (g2At b wd rd es j) (ch a) ≠
        trueSum e ((bindAll (T L es) (rchs2 b ch es j)).map (bind0 · (ch a)))
          (nr (kindOf es) - (j + 1)) := by
  have hA : Agree (ext1 es a) es (b + 2 * j + 1) := agree_append es _ (by omega)
  have hk : kindOf (ext1 es a) = kindOf es := kindOf_append _ (by omega)
  have hr : rch2 b ch (ext1 es a) j = ch a := by
    simp only [rch2, ansAt]
    rw [← hj, entAt_ext1]
  obtain ⟨hT, -⟩ := hTc L (ext1 es a) es (hA.mono (by omega))
  have hg : g2At b wd rd (ext1 es a) j = g2At b wd rd es j := by
    simp only [g2At, msgAt, hA (b + 2 * j) (by omega)]
  have hrs : rchs2 b ch (ext1 es a) j = rchs2 b ch es j := rchs2_congr (l := j) (hA.mono (by omega))
  have hrs' : rchs2 b ch (ext1 es a) (j + 1) = rchs2 b ch es j ++ [ch a] := by
    simp only [rchs2, List.range_succ, List.map_append, List.map_singleton]
    rw [show (List.range j).map (rch2 b ch (ext1 es a)) = rchs2 b ch (ext1 es a) j from rfl,
      hrs, hr]
    rfl
  simp only [Wrong2, clR2, hg, hr, hrs', hT, hk, bindAll_append]

open Classical in
/-- **The asserted round row** (A.10: L2, S2, Lr4 over F with `M = 2^128`; P1.i, Pf over K with
`M = 1`): from a doomed claim whose round check holds (`Chk2`, from `¬ Rej`), at most `2·M`
answers make the next claim true. `hfib` is the challenge map's fiber count
(`card_chF_fiber`, `card_chK_fiber`). -/
theorem D2_single [Fintype R] [DecidableEq R] (hb1 : 1 ≤ b) (hTc : TruthLocal2 b c0 T)
    (he : e.deg = 2) {M : ℕ}
    (hfib : ∀ S : Finset R, (univ.filter fun a : Digest => ch a ∈ S).card = S.card * M)
    (hsz : ∀ L es, ∀ t ∈ T L es, t.size = 2 ^ nr (kindOf es)) (L es : Log)
    (hchk : ∀ j, es.length = b + 2 * j + 1 → j < nr (kindOf es) → Chk2 b wd rd ch c0 L es j) :
    (univ.filter fun a => D2 b wd rd ch c0 nr e T L es ∧
      ¬ D2 b wd rd ch c0 nr e T L (ext1 es a)).card ≤ 2 * M := by
  by_cases hlen : b < es.length
  swap
  · rw [Finset.filter_false_of_mem fun a _ h => not_D2_short (by omega) h.1]; simp
  by_cases hc : (es.length - b) % 2 = 0 ∨ nr (kindOf es) ≤ (es.length - b) / 2
  · rw [Finset.filter_false_of_mem fun a _ h =>
      h.2 ((D2_append_iff hb1 hTc _ hlen hc).mpr h.1)]
    simp
  simp only [not_or, not_le] at hc
  obtain ⟨j, hjdef⟩ : ∃ j, j = (es.length - b) / 2 := ⟨_, rfl⟩
  have hj : j < nr (kindOf es) := hjdef ▸ hc.2
  have hlj : es.length = b + 2 * j + 1 := by omega
  have hans : ans3 b nr es = j := by rw [ans3, hjdef]; exact min_eq_right hc.2.le
  by_cases hw : Wrong2 b wd rd ch c0 nr e T L es j
  swap
  · rw [Finset.filter_false_of_mem fun a _ h => hw (hans ▸ h.1.2)]; simp
  have hts : ∀ t ∈ bindAll (T L es) (rchs2 b ch es j),
      t.size = 2 ^ (nr (kindOf es) - j - 1 + 1) := by
    refine bindAll_size (rchs2 b ch es j) _ fun t ht => ?_
    rw [hsz L es t ht]; congr 1; simp only [rchs2, List.length_map, List.length_range]; omega
  have hesc := round_escape_le e (bindAll (T L es) (rchs2 b ch es j)) hts
    (claim := clR2 b wd rd ch c0 L es j) (by
      rw [show nr (kindOf es) - j - 1 + 1 = nr (kindOf es) - j by omega]; exact hw)
    (g2At b wd rd es j)
  refine le_trans (Finset.card_le_card (t := univ.filter fun a : Digest => ch a ∈ _)
    fun a ha => ?_) (by rw [hfib]; exact Nat.mul_le_mul_right _ (hesc.trans he.le))
  have hnd : ¬ D2 b wd rd ch c0 nr e T L (ext1 es a) := by
    rw [Finset.mem_filter] at ha; exact ha.2.2
  have hans' : ans3 b nr (ext1 es a) = j + 1 := by
    have hk : kindOf (ext1 es a) = kindOf es := kindOf_append _ (by omega)
    rw [ans3, hk, show (ext1 es a).length = es.length + 1 by simp [ext1],
      min_eq_right (by omega)]
    omega
  have hnw : ¬ Wrong2 b wd rd ch c0 nr e T L (ext1 es a) (j + 1) := fun h =>
    hnd ⟨by simp [ext1]; omega, by rw [hans']; exact h⟩
  rw [wrong2_ext1 hb1 hTc L es a hlj, not_not] at hnw
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  refine ⟨⟨by rw [he]; rfl, hchk j hlj hj⟩, ?_⟩
  rw [hnw, show nr (kindOf es) - (j + 1) = nr (kindOf es) - j - 1 by omega]

end Rounds2

/-! ## Controls -/

/-- Control: the phase map at a few positions (Z1's last squeeze, Z2's absorb, P3.0's first
squeeze after the column queries, Pf's last round). -/
theorem phOf_examples : phOf 12 = 3 ∧ phOf 13 = 4 ∧ phOf 339 = 29 ∧ phOf 450 = 50 := by
  unfold phOf; rw [fsStarts_eq]; decide

/-- Control: inside the phase `msD` is the entry's doom, at the last answer `fin`. -/
theorem msD_inside_last (prev fin : Log → Log → Prop) (s0 r : ℕ) (L es : Log) :
    (es.length ≤ s0 + r → (msD prev fin s0 r L es ↔ prev L (es.take (s0 + 1)))) ∧
      (s0 + r < es.length → (msD prev fin s0 r L es ↔ fin L es)) :=
  ⟨fun h => by rw [msD, ite_pos' h], fun h => by rw [msD, ite_neg' (by omega)]⟩

/-- Control (positive): a nonzero table is doomed before any coordinate. -/
theorem mlDoom_nil {n : ℕ} {t : Array F} (h : tbl n t ≠ 0) : mlDoom n t [] := by
  cases n <;> exact h

/-- Control (negative): the zero table is never doomed. -/
theorem not_mlDoom_zero (n : ℕ) (l : List F) :
    ¬ mlDoom n (Array.replicate (2 ^ n) 0) l := by
  unfold mlDoom
  rw [not_not]
  funext u
  have hz : ∀ (cs : List F) (m : ℕ), cs.length ≤ m →
      bindL (Array.replicate (2 ^ m) (0 : F)) cs = Array.replicate (2 ^ (m - cs.length)) 0 := by
    intro cs
    induction cs with
    | nil => intro m _; simp [bindL]
    | cons c cs ih =>
      intro m hm
      obtain ⟨m', rfl⟩ : ∃ m', m = m' + 1 := ⟨m - 1, by simp at hm; omega⟩
      have : bind0 (Array.replicate (2 ^ (m' + 1)) (0 : F)) c = Array.replicate (2 ^ m') 0 := by
        apply Array.ext
        · simp [bind0_size, pow_succ]
        · intro j h1 h2; simp [bind0]
      rw [bindL, this, ih m' (by simp at hm; omega), List.length_cons,
        show m' + 1 - (cs.length + 1) = m' - cs.length by omega]
  rw [hz _ n (by simp)]
  simp only [tbl, Array.getD_eq_getD_getElem?, Array.getElem?_replicate, Pi.zero_apply]
  split <;> rfl

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
  hstab _ _ _ _ _ _ _ := Iff.rfl

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
