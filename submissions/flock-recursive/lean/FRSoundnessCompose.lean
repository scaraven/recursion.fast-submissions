-- New for `flock-recursive` (BLUEPRINT A.10, §5.1–§5.2; stage S-G1i).
-- RET-1: position-free declarations moved to `FRSoundnessCoreTail`.
import FRSoundnessTailM
import FRKState
import FRSoundnessPhases
import FRSoundnessCoreTail

/-!
# `PhaseObl` from the PIOP front's obligations and the Ligerito tail

The whole transcript's doom is the front's for phases `0 … 25` and the tail's (`DT`) for phases
`26 … 51` (**`DkC`**); `Rej` is the front's or the tail's asserted checks (**`RejC`**).

* **`FrontObl RejF DF W₀ c₀`**: what the PIOP front (Z1 … B′) still owes, for positions before
  P1.0 only: its `RejOK`, its `msD` forms, absorbs, single squeezes and multi-squeeze charges,
  its stability, the handoff into P1.0 (B′'s doom gives P1.0's doom at its first absorb: a far
  level-0 word or a false initial claim `c₀ ≠ ⟨W₀, f⁽⁰⁾⟩`), and the locality of `W₀`, `c₀`.
* **`phaseObl_of`**: `FrontObl` gives `PhaseObl (RejC …) (DkC …) (239·2^128)`; the tail's part is
  discharged here (`tail_cls`: every tail position is a P1.i round, C.i, inside P2.i/P3.i, or a Pf
  round).
* **`kstate_of_front`**: the knowledge state at `εR` from `FrontObl` and `FinalLaw`.
-/

namespace FR.Snd
open RecursionFast FR.Merkle Finset
open scoped NNReal

set_option linter.constructorNameAsVariable false

/-! ## The combined doom -/

/-- The asserted checks: the front's or the tail's. -/
def RejC (RejF : Log → Log → Prop) (c₀ : Log → Log → K) (L es : Log) : Prop :=
  RejF L es ∨ RejT c₀ L es

/-- The phase dooms: the front's before P1.0, the tail's from P1.0 on. -/
def DkC (DF : ℕ → Log → Log → Prop) (W₀ : Log → Log → ℕ → K) (c₀ : Log → Log → K) (k : ℕ) :
    Log → Log → Prop :=
  if k < 26 then DF k else DT W₀ c₀ k

theorem rejOK_or {R₁ R₂ : Log → Log → Prop} (h₁ : RejOK R₁) (h₂ : RejOK R₂) :
    RejOK fun L es => R₁ L es ∨ R₂ L es where
  mono L es x h := h.imp (h₁.mono L es x) (h₂.mono L es x)
  sq L es x hs := or_congr (h₁.sq L es x hs) (h₂.sq L es x hs)
  stab L i hb hci X hX := or_congr (h₁.stab L i hb hci X hX) (h₂.stab L i hb hci X hX)

open Classical in
/-- **What the PIOP front still owes** (phases `0 … 25`, positions before P1.0). -/
structure FrontObl (RejF : Log → Log → Prop) (DF : ℕ → Log → Log → Prop)
    (W₀ : Log → Log → ℕ → K) (c₀ : Log → Log → K) : Prop where
  loc : FrontLocal W₀ c₀
  rej : RejOK RejF
  ms : ∀ s0 r, (s0, r) ∈ fsRanges → s0 + 1 < p1Start 0 →
    ∃ fin, DF (phOf (s0 + 1)) = msD (DF (phOf s0)) fin s0 r
  habs : ∀ L es x len, Matches (es ++ [x]) → fsItems[es.length]? = some (.absorb len) →
    es.length < p1Start 0 → ¬ RejC RejF c₀ L es → DF (phOf (es.length - 1)) L es →
      RejC RejF c₀ L (es ++ [x]) ∨ DF (phOf es.length) L (es ++ [x])
  handoff : ∀ L es x len, Matches (es ++ [x]) → fsItems[es.length]? = some (.absorb len) →
    es.length = p1Start 0 → ¬ RejC RejF c₀ L es → DF 25 L es →
      RejC RejF c₀ L (es ++ [x]) ∨ D1 W₀ c₀ 0 L (es ++ [x])
  hsingle : ∀ L es, Matches es → fsItems[es.length]? = some .squeeze → fsRnd es.length = none →
    es.length < p1Start 0 → ¬ RejC RejF c₀ L es →
      (univ.filter fun a => DF (phOf (es.length - 1)) L es ∧
        ¬ DF (phOf es.length) L (ext1 es a)).card ≤ 239 * 2 ^ 128
  hfin : ∀ s0 r, (s0, r) ∈ fsRanges → s0 + 1 < p1Start 0 → ∀ L es₀, Matches es₀ →
    es₀.length = s0 + 1 → ¬ RejC RejF c₀ L es₀ → condCount (DPos (Dp DF)) L es₀ r [] ≤ deltaR
  hstab : ∀ k < 26, ∀ L i, ¬ Bad L → IsChain L i → ∀ X,
    StabExt fsRnd (entriesOf L (pathOf L i)) X → phOf (X.length - 1) = k →
      (DF k (L.take i) X ↔ DF k L X)

/-! ## Position facts -/

theorem front_check : ((List.range 26).all fun j => decide (p1Start 0 ≤ phStart (26 + j))) &&
    ((List.range 26).all fun k => decide (phStart (k + 1) ≤ p1Start 0)) &&
    phOf (p1Start 0 - 1) == 25 &&
    (List.range 5).all (fun i => fsItems[cStart i]? != some .squeeze) &&
    fsRanges.all (fun x => decide (x.1 + x.2 < p1Start 0) ||
      (List.range 5).any fun i => x == (cStart i, (lvlStar i).sq) || x == (p3S0 i, 5)) = true := by
  unfold p1Start cStart p3S0 phOf phStart
  rw [fsStarts_eq, fsRanges_eq]; decide +kernel

theorem front_facts : (∀ j ≤ 25, p1Start 0 ≤ phStart (26 + j)) ∧
    (∀ k < 26, phStart (k + 1) ≤ p1Start 0) ∧ phOf (p1Start 0 - 1) = 25 ∧
    (∀ i < 5, fsItems[cStart i]? ≠ some .squeeze) ∧
    ∀ x ∈ fsRanges, x.1 + x.2 < p1Start 0 ∨
      ∃ i < 5, x = (cStart i, (lvlStar i).sq) ∨ x = (p3S0 i, 5) := by
  have h := front_check
  simp only [Bool.and_eq_true, List.all_eq_true, List.mem_range, decide_eq_true_eq, beq_iff_eq,
    bne_iff_ne, ne_eq, Bool.or_eq_true, List.any_eq_true] at h
  obtain ⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩ := h
  refine ⟨fun j hj => h1 j (by omega), h2, h3, h4, fun x hx => ?_⟩
  rcases h5 x hx with h | ⟨i, hi, h⟩
  · exact Or.inl h
  · exact Or.inr ⟨i, hi, h⟩

theorem phOf_lt_26 {p : ℕ} (hp : p < p1Start 0) : phOf p < 26 := by
  by_contra h
  obtain ⟨h1, h2, -⟩ := phOf_bounds p
  have := front_facts.1 (phOf p - 26) (by omega)
  rw [show 26 + (phOf p - 26) = phOf p by omega] at this
  omega

theorem phOf_ge_26 {p : ℕ} (hp : p1Start 0 ≤ p) : 26 ≤ phOf p := by
  by_contra h
  obtain ⟨-, -, h3⟩ := phOf_bounds p
  have := front_facts.2.1 (phOf p) (by omega)
  have := h3 (by omega)
  omega

theorem DkC_lt {DF : ℕ → Log → Log → Prop} {W₀ : Log → Log → ℕ → K} {c₀ : Log → Log → K}
    {k : ℕ} (h : k < 26) : DkC DF W₀ c₀ k = DF k := by rw [DkC, ite_pos' h]

theorem DkC_ge {DF : ℕ → Log → Log → Prop} {W₀ : Log → Log → ℕ → K} {c₀ : Log → Log → K}
    {k : ℕ} (h : 26 ≤ k) : DkC DF W₀ c₀ k = DT W₀ c₀ k := by rw [DkC, ite_neg' (by omega)]

/-- Checked: the class of every tail position (P1.i's absorb or squeeze, C.i, inside P2.i or
P3.i, Pf's absorb or squeeze), with the phases of it and of its predecessor. -/
def tailCls (p : ℕ) : Bool :=
  (List.range 5).any (fun i => (List.range (hEll i)).any fun l =>
      (p == p1Start i + 2 * l && phOf p == 26 + 5 * i &&
        ((l == 0 && phOf (p - 1) == 25 + 5 * i) || (l != 0 && phOf (p - 1) == 26 + 5 * i))) ||
      (p == p1Start i + 2 * l + 1 && phOf p == 26 + 5 * i && phOf (p - 1) == 26 + 5 * i)) ||
  (List.range 5).any (fun i => (p == cStart i && phOf p == 27 + 5 * i &&
      phOf (p - 1) == 26 + 5 * i) || (decide (cStart i < p) && decide (p ≤ p3S0 i + 5))) ||
  (List.range 7).any (fun l =>
      (p == pfStart + 2 * l && phOf p == 51 &&
        ((l == 0 && phOf (p - 1) == 50) || (l != 0 && phOf (p - 1) == 51))) ||
      (p == pfStart + 2 * l + 1 && phOf p == 51 && phOf (p - 1) == 51))

theorem tailCls_check : (List.range (fsItems.length - p1Start 0)).all
    (fun j => tailCls (p1Start 0 + j)) = true := by
  rw [fsItems_length]
  unfold tailCls p1Start cStart p3S0 pfStart hEll phOf phStart
  rw [fsStarts_eq]; decide +kernel

theorem tail_cls {p : ℕ} (h1 : p1Start 0 ≤ p) (h2 : p < fsItems.length) :
    (∃ i < 5, ∃ l < hEll i, p = p1Start i + 2 * l ∧ phOf p = 26 + 5 * i ∧
      ((l = 0 ∧ phOf (p - 1) = 25 + 5 * i) ∨ (l ≠ 0 ∧ phOf (p - 1) = 26 + 5 * i))) ∨
    (∃ i < 5, ∃ l < hEll i, p = p1Start i + 2 * l + 1 ∧ phOf p = 26 + 5 * i ∧
      phOf (p - 1) = 26 + 5 * i) ∨
    (∃ i < 5, p = cStart i ∧ phOf p = 27 + 5 * i ∧ phOf (p - 1) = 26 + 5 * i) ∨
    (∃ i < 5, cStart i < p ∧ p ≤ p3S0 i + 5) ∨
    (∃ l < 7, p = pfStart + 2 * l ∧ phOf p = 51 ∧
      ((l = 0 ∧ phOf (p - 1) = 50) ∨ (l ≠ 0 ∧ phOf (p - 1) = 51))) ∨
    (∃ l < 7, p = pfStart + 2 * l + 1 ∧ phOf p = 51 ∧ phOf (p - 1) = 51) := by
  have h := tailCls_check
  simp only [List.all_eq_true, List.mem_range] at h
  have hc := h (p - p1Start 0) (by omega)
  rw [show p1Start 0 + (p - p1Start 0) = p by omega] at hc
  simp only [tailCls, Bool.or_eq_true, List.any_eq_true, List.mem_range, Bool.and_eq_true,
    beq_iff_eq, bne_iff_ne, ne_eq, decide_eq_true_eq] at hc
  rcases hc with (⟨i, hi, l, hl, h⟩ | ⟨i, hi, h⟩) | ⟨l, hl, h⟩
  · rcases h with ⟨⟨h1, h2⟩, h3⟩ | ⟨⟨h1, h2⟩, h3⟩
    · exact Or.inl ⟨i, hi, l, hl, h1, h2, h3⟩
    · exact Or.inr (Or.inl ⟨i, hi, l, hl, h1, h2, h3⟩)
  · rcases h with ⟨⟨h1, h2⟩, h3⟩ | ⟨h1, h2⟩
    · exact Or.inr (Or.inr (Or.inl ⟨i, hi, h1, h2, h3⟩))
    · exact Or.inr (Or.inr (Or.inr (Or.inl ⟨i, hi, h1, h2⟩)))
  · rcases h with ⟨⟨h1, h2⟩, h3⟩ | ⟨⟨h1, h2⟩, h3⟩
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨l, hl, h1, h2, h3⟩))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨l, hl, h1, h2, h3⟩))))

/-- A position inside a multi-squeeze phase is a squeeze of that phase. -/
theorem sq_of_mem {s0 r p : ℕ} (hx : (s0, r) ∈ fsRanges) (h1 : s0 < p) (h2 : p ≤ s0 + r) :
    fsItems[p]? = some .squeeze ∧ fsRnd p = some (s0, r) := by
  have h := rangesOK_eq
  simp only [rangesOK, List.all_eq_true, List.mem_range, Bool.and_eq_true, beq_iff_eq] at h
  have := h _ hx (p - (s0 + 1)) (by simp; omega)
  rwa [show s0 + 1 + (p - (s0 + 1)) = p by omega] at this

theorem sq_tail {i p : ℕ} (hi : i < 5) (h1 : cStart i < p) (h2 : p ≤ p3S0 i + 5) :
    fsItems[p]? = some .squeeze ∧ fsRnd p ≠ none := by
  obtain ⟨-, -, -, -, -, -, -, -, -, hm2, hm3⟩ := tail_ph hi
  have hsq := (tail_pos hi).2.2.2.1
  by_cases h : p ≤ p3S0 i
  · obtain ⟨a, b⟩ := sq_of_mem hm2 h1 (by omega); exact ⟨a, by rw [b]; simp⟩
  · obtain ⟨a, b⟩ := sq_of_mem hm3 (by omega) h2; exact ⟨a, by rw [b]; simp⟩

theorem lt_length_of_get {p : ℕ} {it : Item} (h : fsItems[p]? = some it) : p < fsItems.length := by
  by_contra hc; rw [List.getElem?_eq_none (by omega)] at h; simp at h

/-! ## `PhaseObl` -/

variable {RejF : Log → Log → Prop} {DF : ℕ → Log → Log → Prop} {W₀ : Log → Log → ℕ → K}
  {c₀ : Log → Log → K}

/-- **The per-phase obligations of the whole transcript**, from the front's and the tail's. -/
theorem phaseObl_of (hFr : FrontObl RejF DF W₀ c₀) :
    PhaseObl (RejC RejF c₀) (DkC DF W₀ c₀) (239 * 2 ^ 128) where
  rej := rejOK_or hFr.rej (rejT_ok hFr.loc)
  ms s0 r hmem := by
    by_cases h : s0 + 1 < p1Start 0
    · obtain ⟨fin, hf⟩ := hFr.ms s0 r hmem h
      exact ⟨fin, by rw [DkC_lt (phOf_lt_26 h), DkC_lt (phOf_lt_26 (by omega)), hf]⟩
    rcases front_facts.2.2.2.2 _ hmem with hx | ⟨i, hi, hx | hx⟩
    · have := (ms_phOf hmem).1; simp at hx; omega
    · simp only [Prod.mk.injEq] at hx; obtain ⟨rfl, rfl⟩ := hx
      exact ⟨_, ms_P2 hi (by rw [DkC_ge (by omega), DT_C W₀ c₀ hi])
        (by rw [DkC_ge (by omega), DT_P2 W₀ c₀ hi])⟩
    · simp only [Prod.mk.injEq] at hx; obtain ⟨rfl, rfl⟩ := hx
      exact ⟨_, ms_P3 hi (by rw [DkC_ge (by omega), DT_P2 W₀ c₀ hi])
        (by rw [DkC_ge (by omega), DT_P3 W₀ c₀ hi])⟩
  habs L es x len hm hit hr hd := by
    have hlt := lt_length_of_get hit
    by_cases hp : es.length < p1Start 0
    · rw [DkC_lt (phOf_lt_26 (by omega))] at hd
      rw [DkC_lt (phOf_lt_26 hp)]
      exact hFr.habs L es x len hm hit hp hr hd
    by_cases hp' : es.length = p1Start 0
    · rw [hp', front_facts.2.2.1, DkC_lt (by norm_num)] at hd
      have := hFr.handoff L es x len hm hit hp' hr hd
      have hD : DT W₀ c₀ 26 = D1 W₀ c₀ 0 := DT_P1 W₀ c₀ (i := 0) (by norm_num)
      rwa [hp', (tail_ph (show 0 < 5 by norm_num)).1, DkC_ge le_rfl, hD]
    rcases tail_cls (by omega) hlt with ⟨i, hi, l, hl, he, h1, h2⟩ | ⟨i, hi, l, hl, he, -, -⟩ |
      ⟨i, hi, he, h1, h2⟩ | ⟨i, hi, h1, h2⟩ | ⟨l, hl, he, h1, h2⟩ | ⟨l, hl, he, -, -⟩
    · right
      rw [h1, DkC_ge (by omega), DT_P1 W₀ c₀ hi]
      rcases h2 with ⟨rfl, h2⟩ | ⟨hl0, h2⟩
      · obtain ⟨j, rfl⟩ : ∃ j, i = j + 1 := ⟨i - 1, by
          rcases Nat.eq_zero_or_pos i with rfl | h
          · simp at he; omega
          · omega⟩
        rw [h2, show 25 + 5 * (j + 1) = 30 + 5 * j by ring, DkC_ge (by omega),
          DT_P3 W₀ c₀ (by omega), DP3, msD, ite_neg' (by
            have := (tail_pos (show j < 5 by omega)).2.2.2.2
            rw [nxStart_le hi] at this; omega)] at hd
        exact habs_P1_next hFr.loc x hi (by omega) hd
      · rw [h2, DkC_ge (by omega), DT_P1 W₀ c₀ hi] at hd
        exact habs_P1 hFr.loc x hi (by omega) he hd
    · have := (rounds_P1 hi hl).2; rw [← he, hit] at this; simp at this
    · right
      rw [h2, DkC_ge (by omega), DT_P1 W₀ c₀ hi] at hd
      rw [h1, DkC_ge (by omega), DT_C W₀ c₀ hi]
      exact habs_C hFr.loc x hi he hd
    · have := (sq_tail hi h1 h2).1; rw [hit] at this; simp at this
    · right
      rw [h1, DkC_ge (by omega), DT_Pf]
      rcases h2 with ⟨rfl, h2⟩ | ⟨hl0, h2⟩
      · rw [h2, show (50 : ℕ) = 30 + 5 * 4 by norm_num, DkC_ge (by omega),
          DT_P3 W₀ c₀ (by norm_num), DP3, msD, ite_neg' (by
            have := (tail_pos (show 4 < 5 by norm_num)).2.2.2.2
            have hnx : nxStart 4 = pfStart := rfl
            omega)] at hd
        exact habs_Pf_first hFr.loc x (by omega) hd
      · rw [h2, DkC_ge (by omega), DT_Pf] at hd
        exact habs_Pf hFr.loc x (by omega) he hd
    · have := (rounds_Pf hl).2; rw [← he, hit] at this; simp at this
  hsingle L es hm hit hrnd hr := by
    have hlt := lt_length_of_get hit
    by_cases hp : es.length < p1Start 0
    · rw [DkC_lt (phOf_lt_26 (by omega)), DkC_lt (phOf_lt_26 hp)]
      exact hFr.hsingle L es hm hit hrnd hp hr
    have hrT : ¬ RejT c₀ L es := fun h => hr (Or.inr h)
    rcases tail_cls (by omega) hlt with ⟨i, hi, l, hl, he, -, -⟩ | ⟨i, hi, l, hl, he, h1, h2⟩ |
      ⟨i, hi, he, -, -⟩ | ⟨i, hi, h1, h2⟩ | ⟨l, hl, he, -, -⟩ | ⟨l, hl, he, h1, h2⟩
    · have := (rounds_P1 hi hl).1; rw [← he, hit] at this; simp at this
    · rw [h1, h2, DkC_ge (by omega), DT_P1 W₀ c₀ hi]
      exact (single_P1 hFr.loc hi hl he hrT).trans (p1_N_le _ hi)
    · exact absurd (he ▸ hit) (front_facts.2.2.2.1 i hi)
    · exact absurd hrnd (sq_tail hi h1 h2).2
    · have := (rounds_Pf hl).1; rw [← he, hit] at this; simp at this
    · rw [h1, h2, DkC_ge (by omega), DT_Pf]
      exact (single_Pf hFr.loc he hrT).trans (by norm_num)
  hfin s0 r hmem L es₀ hm hl hr := by
    by_cases h : s0 + 1 < p1Start 0
    · have hb : s0 + r < p1Start 0 := by
        rcases front_facts.2.2.2.2 _ hmem with hx | ⟨i, hi, hx | hx⟩
        · exact hx
        all_goals
          simp only [Prod.mk.injEq] at hx; obtain ⟨rfl, rfl⟩ := hx
          have h0 : p1Start 0 ≤ p1Start i := front_facts.1 (5 * i) (by omega)
          obtain ⟨-, -, h3, h4, -⟩ := tail_pos hi
          omega
      refine le_trans (le_of_eq (condCount_congr fun as has => ?_))
        (hFr.hfin s0 r hmem h L es₀ hm hl hr)
      have hlx := length_ext as es₀
      have hd : (ext es₀ as).dropLast.length = s0 + r := by
        rw [List.length_dropLast]; omega
      simp only [EscAtG, DPos, Dp, hd, hlx, hl, has]
      rw [DkC_lt (phOf_lt_26 (by omega)), DkC_lt (phOf_lt_26 (by omega))]
    rcases front_facts.2.2.2.2 _ hmem with hx | ⟨i, hi, hx | hx⟩
    · have := (ms_phOf hmem).1; simp at hx; omega
    · simp only [Prod.mk.injEq] at hx; obtain ⟨rfl, rfl⟩ := hx
      exact hfin_P2 hFr.loc hi (by rw [DkC_ge (by omega), DT_C W₀ c₀ hi])
        (by rw [DkC_ge (by omega), DT_P2 W₀ c₀ hi]) L es₀ hl
    · simp only [Prod.mk.injEq] at hx; obtain ⟨rfl, rfl⟩ := hx
      exact hfin_P3 hFr.loc hi (by rw [DkC_ge (by omega), DT_P2 W₀ c₀ hi])
        (by rw [DkC_ge (by omega), DT_P3 W₀ c₀ hi]) L es₀ hl
  hstab k L i hb hci X hX hk := by
    by_cases h : k < 26
    · rw [DkC_lt h]; exact hFr.hstab k h L i hb hci X hX hk
    rw [DkC_ge (by omega)]
    have hX1 : 1 ≤ X.length := by
      obtain ⟨s0, r, as, -, hs, -, rfl⟩ := hX
      rw [length_ext, List.length_take]; omega
    obtain ⟨h1, h2, -⟩ := phOf_bounds (X.length - 1)
    rw [hk] at h1 h2
    exact DT_stab hFr.loc (by omega) h2 (same_stabX hb hci hX) le_rfl (by omega)

/-- **The knowledge state at `εR`** from the front's obligations and the `final` law: with the
tail discharged, `kstate_of`'s remaining hypotheses are `FrontObl` and `FinalLaw`. -/
noncomputable def kstate_of_front (S : Submission) (vk : Digest) (hFr : FrontObl RejF DF W₀ c₀)
    (hfin : FinalLaw S vk (RejC RejF c₀) (DkC DF W₀ c₀)) :
    KState (Rel (S.acc vk)) (S.V vk) S.E epsR :=
  kstate_of S vk N_le (phaseObl_of hFr) hfin

/-- **Knowledge soundness at `εR` from the front** (BLUEPRINT B-14, core PR #19's textbook `KS`):
`kstate_of_front` through the library bridge `KState.ks`, at the same `ε`, given the verifier's
query bound. -/
theorem ks_of_front (S : Submission) (vk : Digest) (hFr : FrontObl RejF DF W₀ c₀)
    (hfin : FinalLaw S vk (RejC RejF c₀) (DkC DF W₀ c₀))
    (hq : ∀ H c π, ((S.V vk c π).queries H).length ≤ S.qV) :
    KS (Rel (S.acc vk)) (S.V vk) S.E epsR S.qV :=
  (kstate_of_front S vk hFr hfin).ks hq

/-! ## Stability on the chain itself (`ChainStab`, S-G1h deviation 1) -/

/-- On a non-bad log, a chain reads the same off the log before its last entry and off the log
(its caps are real entries, `capOK_of_matches`, `wordK_stab`). -/
theorem same_chain {L : Log} (hb : ¬ Bad L) {j : ℕ} (hci : IsChain L j) :
    Same (L.take j) (entriesOf L (pathOf L j)) L (entriesOf L (pathOf L j))
      (entriesOf L (pathOf L j)).length := by
  set es := entriesOf L (pathOf L j)
  have hes : ext (es.take es.length) [] = es := by rw [ext_nil, List.take_length]
  refine ⟨fun _ _ => rfl, fun κ i hi hc => ?_⟩
  have hw := wordK_stab hb hci es.length [] hi κ (by rw [hes]; exact capOK_of_matches hci.2 hi hc)
  rwa [hes] at hw

/-- The tail's asserted checks read the same off two logs whose words agree. -/
theorem rejT_same (hF : FrontLocal W₀ c₀) {L L' Y : Log} {p : ℕ} (hS : Same L Y L' Y p)
    (hY : Y.length ≤ p) : RejT c₀ L Y ↔ RejT c₀ L' Y := by
  refine or_congr ⟨fun ⟨i, hi, j, hj, hlt, hc⟩ => ⟨i, hi, j, hj, hlt, fun h' => hc ?_⟩,
    fun ⟨i, hi, j, hj, hlt, hc⟩ => ⟨i, hi, j, hj, hlt, fun h' => hc ?_⟩⟩
    ⟨fun ⟨j, hj, hlt, hc⟩ => ⟨j, hj, hlt, fun h' => hc ?_⟩,
    fun ⟨j, hj, hlt, hc⟩ => ⟨j, hj, hlt, fun h' => hc ?_⟩⟩
  · exact (chk2_same hS (by omega) (lvC_same hF hS hi (by omega))).mpr h'
  · exact (chk2_same hS (by omega) (lvC_same hF hS hi (by omega))).mp h'
  · exact (chk2_same hS (by omega) (lvC5_same hF hS (by omega))).mpr h'
  · exact (chk2_same hS (by omega) (lvC5_same hF hS (by omega))).mp h'

/-- What the front owes for `ChainStab`: its checks and dooms read the same on the chain itself. -/
def FrontChainStab (RejF : Log → Log → Prop) (DF : ℕ → Log → Log → Prop) : Prop :=
  ∀ L j, ¬ Bad L → IsChain L j →
    (RejF (L.take j) (entriesOf L (pathOf L j)) ↔ RejF L (entriesOf L (pathOf L j))) ∧
    ∀ k < 26, phOf ((entriesOf L (pathOf L j)).length - 1) = k →
      (DF k (L.take j) (entriesOf L (pathOf L j)) ↔ DF k L (entriesOf L (pathOf L j)))

/-- **`ChainStab` for the whole transcript's doom** (what `final`'s walk needs, S-G1h deviation 1):
the tail's part is proved (`same_chain`, `DT_stab`, `rejT_same`); the front's is `FrontChainStab`. -/
theorem chainStab_of (hF : FrontLocal W₀ c₀) (hFS : FrontChainStab RejF DF) :
    ChainStab (DC (RejC RejF c₀) (Dp (DkC DF W₀ c₀))) := by
  intro L j hb hci
  set es := entriesOf L (pathOf L j)
  have hS := same_chain hb hci
  obtain ⟨hR, hD⟩ := hFS L j hb hci
  have h1 : 1 ≤ es.length := List.length_pos_iff.mpr (matches_ne_nil hci.2)
  unfold DC RejC DPos Dp
  refine or_congr (or_congr hR (rejT_same hF hS le_rfl)) ?_
  by_cases hk : phOf (es.length - 1) < 26
  · rw [DkC_lt hk]; exact hD _ hk rfl
  rw [DkC_ge (by omega)]
  obtain ⟨b1, b2, -⟩ := phOf_bounds (es.length - 1)
  have hl : (entriesOf L (pathOf L j)).length = es.length := rfl
  exact DT_stab hF (by omega) b2 hS le_rfl (by rw [hl]; omega)

/-! ## Controls -/

/-- Control (positive): on the empty log every intermediate fold is close (the word is `0`). -/
theorem closeP_nil (κ : Kind) (es : Log) {i l : ℕ} (hl : l ≤ (lvl κ i).ell) :
    closeP κ [] es i l := closeP_of_not_far (not_farL_nil κ es i) l hl

/-- Control (positive): a far word before P1.i's first answer dooms P1.i (the far part is live). -/
theorem D1_of_far {i : ℕ} {L es : Log} (h0 : hRnd es i = 0) (hf : farL (kindOf es) L es i) :
    D1 W₀ c₀ i L es := Or.inl (by rw [h0, closeP_zero, not_not]; exact hf)

/-- Control (negative): on the empty log, before P1.i's first absorb, P1.i is not doomed. -/
theorem not_D1_nil {i : ℕ} {es : Log} (hl : es.length ≤ p1Start i) : ¬ D1 W₀ c₀ i [] es := by
  rintro (h | ⟨-, hd⟩)
  · have h0 : hRnd es i = 0 := by unfold hRnd; omega
    rw [h0] at h; exact h (closeP_nil _ _ (Nat.zero_le _))
  · exact not_D2_short hl hd

/-- Control (negative): with every query consistent and no offset, P3.i's table is zero. -/
theorem p3T_zero {κ : Kind} {L es : Log} {i : ℕ} (h : truthP3 κ L es i) :
    tbl 9 (p3T κ L es i 0) = 0 := by
  funext q
  rw [tbl_p3T, add_zero]
  split_ifs with hq
  · exact h q hq
  · rfl

/-- Control (negative): no tail check fails before P1.0's first absorb. -/
theorem not_rejT_short {L es : Log} (hl : es.length ≤ p1Start 0) : ¬ RejT c₀ L es := by
  rintro (⟨i, hi, j, -, hlt, -⟩ | ⟨j, -, hlt, -⟩)
  · have : p1Start 0 ≤ p1Start i := front_facts.1 (5 * i) (by omega)
    omega
  · have : p1Start 0 ≤ pfStart := front_facts.1 25 le_rfl
    omega

open Classical in
/-- Control (positive, satisfiability): the empty front with constant `W₀`, `c₀` meets
`FrontObl` (the interface is not contradictory). -/
theorem frontObl_false :
    FrontObl (fun _ _ => False) (fun _ _ _ => False) (fun _ _ _ => 0) (fun _ _ => 0) where
  loc _ _ _ _ _ _ _ := ⟨rfl, rfl⟩
  rej := rejOK_false
  ms _ _ _ _ := ⟨fun _ _ => False, by funext L es; simp only [msD, eq_iff_iff]; split_ifs <;> rfl⟩
  habs _ _ _ _ _ _ _ _ h := h.elim
  handoff _ _ _ _ _ _ _ _ h := h.elim
  hsingle _ _ _ _ _ _ _ := by simp
  hfin _ _ _ _ L es₀ _ _ _ := by
    rw [condCount_eq_zero fun _ _ h => h.2.1]; exact zero_le
  hstab _ _ _ _ _ _ _ _ _ := Iff.rfl

end FR.Snd
