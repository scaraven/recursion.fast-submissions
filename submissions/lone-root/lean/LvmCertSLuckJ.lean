-- New for lvm2 (J2C-C, J2′): the extractor's luck at J2′ (`C_rec` at the Johnson radius, `cfgRec20Jp`). Adapted
-- from this entry's `LvmCertSLuck.lean` (WP-14 / X-REC2: `LuckB0`, `LuckB1`, `foldChal1`, `card_bad0_le`,
-- `card_bad1_le`, `esc_luck_le`), with the lists of J2′ in place of the unique candidates (`LvmCertSJ`'s
-- `card_luckL_snoc_le`, `ten_δLJ_le`).
import LvmCertSLuck
import LvmCertSJ

/-!
# The luck of `P_S` at J2′ (J2C-DES §3, `LuckBJ`)

The extractor's two decoders need, off luck, that the six level-0 fold challenges are not lucky for the
good root candidate `q`, and the four level-1 challenges not lucky for the level-1 list member `V` on `q`'s
path. At J2′ neither is unique, so the luck quantifies over the lists:

* **J2′'s readers.** `foldChalJ` and `rec1OfJ` are `LvmCertSLuck`'s `foldChal` and `rec1Of` (the program
  up to level 1's cap is the UD one: `ρ`, the first round polynomial, six fold rounds, then the cap).
  `foldChal1J` differs: after the cap, J2′ draws the **13 OOD coordinates**, reads the OOD answer and its
  intro polynomial (3 scalars), then the level-0 query group's `18` challenges (separating, proof of work,
  `15` position challenges for `115` positions, `λ`); so the level-1 fold challenges are the samples after
  the cap without the first `31`, at most four.
* `LuckB0J`: some candidate of `C_rec`'s root word **at `(codesRec20Jp 0).thr`** (at most `304`,
  `candidates_rec20Jp_ncard_le`) is lucky in the level-0 rounds drawn; `LuckB1J`: some member of
  **`iList (codesRec20Jp 1)`** (`codeJ9R3`, at most `311`) of the level-1 rows is lucky in the level-1
  rounds drawn. **`LuckBJ = LuckB0J ∨ LuckB1J`**.
* **`esc_luckJ_le`**: from a history that is not lucky, a group becomes lucky with probability at most
  `((6 − |foldChalJ|) + (4 − |foldChal1J|)) · 311·2^15/|E|`; **`esc_luckJ_le_132`**: `≤ 2^-132`
  (`ten_δLJ_le`).
-/

set_option autoImplicit false

namespace Lvm.ASM

open LeanVM.Parameters LeanVM.Protocol LeanVM.Protocol.Compile LeanVM.Protocol.Verifier
open LeanVM.Protocol.Compile.VerifierProgram LeanVM.Protocol.Whir.Sound LeanVM.Protocol.EndToEnd
open LeanVM.Protocol.Whir LeanVM.Protocol.Whir.Ud
open scoped ENNReal

/-! ## J2′'s readers -/

/-- **The level-0 fold challenges at J2′** (the UD reader: samples after the middle phases, without `ρ`, at
most six). -/
abbrev foldChalJ (mid : List UInt8 → VerifierProgram OpenClaims) (x : List UInt8) (h : List Ev) :
    List E :=
  foldChal mid x h

/-- **`C_rec`'s level-1 cap at J2′** (the UD reader: the first commitment after the middle phases, and the
events after it). -/
abbrev rec1OfJ (mid : List UInt8 → VerifierProgram OpenClaims) (x : List UInt8) (h : List Ev) :
    Option (Word × List Ev) :=
  rec1Of mid x h

/-- **The level-1 fold challenges at J2′**: the samples after `C_rec`'s level-1 cap, without the `13` OOD
coordinates and the level-0 query group's `18` challenges, at most four. -/
def foldChal1J (mid : List UInt8 → VerifierProgram OpenClaims) (x : List UInt8) (h : List Ev) :
    List E :=
  match rec1Of mid x h with
  | none => []
  | some (_, b) => ((b.filterMap sampleOf).drop 31).take 4

/-- The level-1 fold challenges at J2′ grow at the next challenge. -/
def Grows1J (mid : List UInt8 → VerifierProgram OpenClaims) (x : List UInt8) (h : List Ev) : Prop :=
  ∃ W b, rec1Of mid x h = some (W, b) ∧ 31 ≤ (b.filterMap sampleOf).length ∧
    (b.filterMap sampleOf).length < 35

section Readers

variable {mid : List UInt8 → VerifierProgram OpenClaims} {x : List UInt8}

theorem foldChal1J_snoc_of_ne (h : List Ev) (e : Ev) (he : sampleOf e = none) :
    foldChal1J mid x (h ++ [e]) = foldChal1J mid x h := by
  unfold foldChal1J
  rcases hr : rec1Of mid x h with _ | ⟨W, b⟩
  · rcases hr' : rec1Of mid x (h ++ [e]) with _ | ⟨W', b'⟩
    · rfl
    · rw [(rec1Of_snoc h e).2 hr W' b' hr']; rfl
  · rw [(rec1Of_snoc h e).1 W b hr]
    simp [List.filterMap_append, he]

open Classical in
theorem foldChal1J_snoc_sample (h : List Ev) (c : E) :
    foldChal1J mid x (h ++ [Ev.sample c]) =
      if Grows1J mid x h then foldChal1J mid x h ++ [c] else foldChal1J mid x h := by
  unfold foldChal1J
  rcases hr : rec1Of mid x h with _ | ⟨W, b⟩
  · have hg : ¬ Grows1J mid x h := by rintro ⟨_, _, h', -⟩; rw [hr] at h'; cases h'
    rw [if_neg hg]
    rcases hr' : rec1Of mid x (h ++ [Ev.sample c]) with _ | ⟨W', b'⟩
    · rfl
    · rw [(rec1Of_snoc h _).2 hr W' b' hr']; rfl
  · rw [(rec1Of_snoc h _).1 W b hr]
    dsimp only
    rw [List.filterMap_append, show [Ev.sample c].filterMap sampleOf = [c] from rfl]
    set S := b.filterMap sampleOf
    by_cases h1 : 31 ≤ S.length
    · by_cases h2 : S.length < 35
      · have hg : Grows1J mid x h := ⟨W, b, hr, h1, h2⟩
        rw [if_pos hg, List.drop_append_of_le_length h1,
          List.take_of_length_le (by simp; omega), List.take_of_length_le (by simp; omega)]
      · have hg : ¬ Grows1J mid x h := by
          rintro ⟨_, _, h', -, h3⟩; rw [hr] at h'; cases h'; exact h2 h3
        rw [if_neg hg, List.drop_append_of_le_length h1,
          List.take_append_of_le_length (by simp; omega)]
    · have hg : ¬ Grows1J mid x h := by
        rintro ⟨_, _, h', h3, -⟩; rw [hr] at h'; cases h'; exact h1 h3
      rw [if_neg hg, List.drop_eq_nil_of_le (by simp; omega),
        List.drop_eq_nil_of_le (by omega)]

theorem length_foldChal1J_le (h : List Ev) : (foldChal1J mid x h).length ≤ 4 := by
  unfold foldChal1J
  split
  · simp
  · simp

theorem length_foldChal1J_of_grows {h : List Ev} (hg : Grows1J mid x h) :
    (foldChal1J mid x h).length < 4 := by
  obtain ⟨W, b, hr, -, hl⟩ := hg
  unfold foldChal1J
  rw [hr]
  simp only [List.length_take, List.length_drop]
  omega

theorem rec1Of_of_foldChal1J_ne {h : List Ev} (hne : foldChal1J mid x h ≠ []) :
    ∃ W b, rec1Of mid x h = some (W, b) := by
  unfold foldChal1J at hne
  rcases hr : rec1Of mid x h with _ | ⟨W, b⟩
  · rw [hr] at hne; exact absurd rfl hne
  · exact ⟨W, b, rfl⟩

theorem foldChal1J_nil : foldChal1J mid x [] = [] := by
  unfold foldChal1J rec1Of afterMid
  have : rootsProg.retSplit [] = none := by
    simp [rootsProg, commitRootUd, cfgMain24G, VerifierProgram.readCommitment, VerifierProgram.bind,
      retSplit]
  rw [this]

end Readers

/-! ## The luck predicate -/

/-- **The level-0 luck at J2′**: some candidate of `C_rec`'s root word at the Johnson threshold is lucky in
the level-0 fold rounds drawn. -/
def LuckB0J (mid : List UInt8 → VerifierProgram OpenClaims) (x : List UInt8) (h : List Ev) : Prop :=
  ∃ q ∈ Candidates 19 2 (codesRec20Jp 0).thr (WrOf h),
    RoundsLuck LeanVM.Protocol.EndToEnd.laneBits (foldChalJ mid x h) (laneRows 19 2 (WrOf h))
      (encRows 19 2 q)

/-- **The level-1 luck at J2′**: some member of the Johnson list (`codesRec20Jp 1 = codeJ9R3`) of
`C_rec`'s level-1 rows is lucky in the level-1 fold rounds drawn. -/
def LuckB1J (mid : List UInt8 → VerifierProgram OpenClaims) (x : List UInt8) (h : List Ev) : Prop :=
  ∃ V ∈ iList (codesRec20Jp 1).code (codesRec20Jp 1).thr
      (rows1 4 (codesRec20Jp 1).n (W1L mid x h)),
    RoundsLuck 4 (foldChal1J mid x h) (rows1 4 (codesRec20Jp 1).n (W1L mid x h)) V

/-- **The extractor's luck at J2′** (J2C-DES §3): level-0 or level-1 luck over the lists. -/
def LuckBJ (mid : List UInt8 → VerifierProgram OpenClaims) (x : List UInt8) (h : List Ev) : Prop :=
  LuckB0J mid x h ∨ LuckB1J mid x h

section Luck

variable {mid : List UInt8 → VerifierProgram OpenClaims} {x : List UInt8}

/-- `LuckB1J` from a member's two parts (`IsInterleavedCodeword`, `IsClose`; the membership at another
instance of the rows' `Fintype` does not unify cheaply). -/
theorem luckB1J_of_parts {h : List Ev} {V : (Fin 4 → Bool) → Fin (codesRec20Jp 1).n → E}
    (hcw : IsInterleavedCodeword (codesRec20Jp 1).code V)
    (hcl : IsClose (codesRec20Jp 1).thr (rows1 4 (codesRec20Jp 1).n (W1L mid x h)) V)
    (hl : RoundsLuck 4 (foldChal1J mid x h) (rows1 4 (codesRec20Jp 1).n (W1L mid x h)) V) :
    LuckB1J mid x h := by
  unfold LuckB1J
  simp only [mem_iList]
  exact ⟨V, ⟨hcw, hcl⟩, hl⟩

theorem not_luckB0J_of_nil {h : List Ev} (hn : foldChal mid x h = []) : ¬ LuckB0J mid x h := by
  rintro ⟨q, -, hq⟩
  rw [foldChalJ, hn] at hq
  exact roundsLuck_nil _ _ _ hq

theorem luckB0J_snoc_iff {h : List Ev} {e : Ev}
    (hf : foldChal mid x (h ++ [e]) = foldChal mid x h) :
    LuckB0J mid x (h ++ [e]) ↔ LuckB0J mid x h := by
  by_cases hn : foldChal mid x h = []
  · exact ⟨fun h' ↦ absurd h' (not_luckB0J_of_nil (hf.trans hn)),
      fun h' ↦ absurd h' (not_luckB0J_of_nil hn)⟩
  · obtain ⟨l₁, l₃, hm⟩ := afterMid_of_foldChal_ne hn
    unfold LuckB0J WrOf foldChalJ
    rw [rootsOf_snoc hm e, hf]

theorem not_luckB1J_of_nil {h : List Ev} (hn : foldChal1J mid x h = []) : ¬ LuckB1J mid x h := by
  rintro ⟨V, -, hV⟩
  rw [hn] at hV
  exact roundsLuck_nil _ _ _ hV

theorem luckB1J_snoc_iff {h : List Ev} {e : Ev}
    (hf : foldChal1J mid x (h ++ [e]) = foldChal1J mid x h) :
    LuckB1J mid x (h ++ [e]) ↔ LuckB1J mid x h := by
  by_cases hn : foldChal1J mid x h = []
  · exact ⟨fun h' ↦ absurd h' (not_luckB1J_of_nil (hf.trans hn)),
      fun h' ↦ absurd h' (not_luckB1J_of_nil hn)⟩
  · obtain ⟨W, b, hr⟩ := rec1Of_of_foldChal1J_ne hn
    unfold LuckB1J
    rw [W1L_of_rec1Of ((rec1Of_snoc h e).1 W b hr), W1L_of_rec1Of hr, hf]

/-- **A prover move or an opening keeps the luck out.** -/
theorem not_luckBJ_snoc {h : List Ev} {e : Ev} (he : sampleOf e = none) (hB : ¬ LuckBJ mid x h) :
    ¬ LuckBJ mid x (h ++ [e]) := by
  rintro (h' | h')
  · exact hB (.inl ((luckB0J_snoc_iff (foldChal_snoc_of_ne h e he)).1 h'))
  · exact hB (.inr ((luckB1J_snoc_iff (foldChal1J_snoc_of_ne h e he)).1 h'))

theorem LuckBJ_nil : ¬ LuckBJ mid x [] := by
  rintro (h' | h')
  · refine not_luckB0J_of_nil ?_ h'
    unfold foldChal afterMid
    have : rootsProg.retSplit [] = none := by
      simp [rootsProg, commitRootUd, cfgMain24G, VerifierProgram.readCommitment, VerifierProgram.bind,
        retSplit]
    rw [this]
  · exact not_luckB1J_of_nil foldChal1J_nil h'

/-! ## The group bound -/

open Classical in
theorem length_foldChal1J_snoc (h : List Ev) (c : E) :
    (foldChal1J mid x (h ++ [Ev.sample c])).length =
      (foldChal1J mid x h).length + if Grows1J mid x h then 1 else 0 := by
  rw [foldChal1J_snoc_sample]; split_ifs <;> simp

open Classical in
theorem length_foldChal1J_add_le (h : List Ev) :
    (foldChal1J mid x h).length + (if Grows1J mid x h then 1 else 0) ≤ 4 := by
  split_ifs with hg
  · exact length_foldChal1J_of_grows hg
  · simpa using length_foldChal1J_le h

theorem card_lanes_le : Fintype.card (Fin (2 ^ (19 - LeanVM.Protocol.EndToEnd.laneBits + 2))) ≤ 2 ^ 15 :=
  (Fintype.card_fin _).le

theorem card_rows1J_le : Fintype.card (Fin (codesRec20Jp 1).n) ≤ 2 ^ 15 := by
  rw [Fintype.card_fin]
  exact Nat.pow_le_pow_right (by norm_num) (by decide)

open Classical in
/-- The challenges at which the level-0 luck starts: at most `311·2^15` (`304` candidates, `2^15`
columns), and none unless the level-0 challenges grow. -/
theorem card_bad0J_le {h : List Ev} (hB : ¬ LuckB0J mid x h) :
    (Finset.univ.filter fun c : E ↦ LuckB0J mid x (h ++ [Ev.sample c])).card ≤
      (if Grows mid x h then 1 else 0) * (311 * 2 ^ 15) := by
  by_cases hg : Grows mid x h
  · rw [if_pos hg, one_mul]
    have hlt := length_foldChal_of_grows hg
    obtain ⟨l₁, l₃, hm⟩ := afterMid_of_grows hg
    have hfin : (Candidates 19 2 (codesRec20Jp 0).thr (WrOf h)).Finite := Set.toFinite _
    have hΛ : (hfin.toFinset.image (encRows 19 2)).card ≤ 311 :=
      Finset.card_image_le.trans (by
        rw [← Set.ncard_eq_toFinset_card _ hfin]
        exact (candidates_rec20Jp_ncard_le _).trans (by norm_num))
    have hn : ¬ ∃ V ∈ hfin.toFinset.image (encRows 19 2),
        RoundsLuck LeanVM.Protocol.EndToEnd.laneBits (foldChal mid x h) (laneRows 19 2 (WrOf h)) V := by
      rintro ⟨V, hV, hl⟩
      obtain ⟨q, hq, rfl⟩ := Finset.mem_image.1 hV
      exact hB ⟨q, hfin.mem_toFinset.1 hq, hl⟩
    refine le_trans (Finset.card_le_card fun c hc ↦ ?_)
      (card_luckL_snoc_le card_lanes_le _ hΛ _ _ hlt hn)
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hc ⊢
    obtain ⟨q', hq', hl⟩ := hc
    unfold WrOf at hq' hl
    unfold foldChalJ at hl
    rw [rootsOf_snoc hm, foldChal_snoc_sample, if_pos hg] at hl
    rw [rootsOf_snoc hm] at hq'
    exact ⟨encRows 19 2 q', Finset.mem_image_of_mem _ (hfin.mem_toFinset.2 hq'), hl⟩
  · rw [if_neg hg, zero_mul]
    refine le_trans (Finset.card_le_card (t := ∅) fun c hc' ↦ ?_) (by simp)
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hc'
    exact absurd ((luckB0J_snoc_iff (by rw [foldChal_snoc_sample, if_neg hg])).1 hc') hB

open Classical in
/-- The challenges at which the level-1 luck starts: at most `311·2^12 ≤ 311·2^15`, and none unless the
level-1 challenges grow. -/
theorem card_bad1J_le {h : List Ev} (hB : ¬ LuckB1J mid x h) :
    (Finset.univ.filter fun c : E ↦ LuckB1J mid x (h ++ [Ev.sample c])).card ≤
      (if Grows1J mid x h then 1 else 0) * (311 * 2 ^ 15) := by
  by_cases hg : Grows1J mid x h
  · rw [if_pos hg, one_mul]
    have hlt := length_foldChal1J_of_grows hg
    obtain ⟨W, b, hr, -⟩ := id hg
    have hW1 : ∀ c, W1L mid x (h ++ [Ev.sample c]) = W1L mid x h := fun c ↦ by
      rw [W1L_of_rec1Of ((rec1Of_snoc h _).1 W b hr), W1L_of_rec1Of hr]
    have key : ∀ c, LuckB1J mid x (h ++ [Ev.sample c]) ↔
        ∃ V ∈ iList (codesRec20Jp 1).code (codesRec20Jp 1).thr
            (rows1 4 (codesRec20Jp 1).n (W1L mid x h)),
          RoundsLuck 4 (foldChal1J mid x h ++ [c]) (rows1 4 (codesRec20Jp 1).n (W1L mid x h)) V := by
      intro c; unfold LuckB1J; rw [hW1 c, foldChal1J_snoc_sample, if_pos hg]
    simp only [key]
    exact card_luckL_snoc_le card_rows1J_le _ ((codesRec20Jp 1).card_iList_le _) _ _ hlt hB
  · rw [if_neg hg, zero_mul]
    refine le_trans (Finset.card_le_card (t := ∅) fun c hc' ↦ ?_) (by simp)
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hc'
    exact absurd ((luckB1J_snoc_iff (by rw [foldChal1J_snoc_sample, if_neg hg])).1 hc') hB

open Classical in
/-- **The luck's group bound at J2′**: from a history that is not lucky, the next group becomes lucky
with probability at most `((6 − |foldChalJ|) + (4 − |foldChal1J|)) · 311·2^15/|E|`. -/
theorem esc_luckJ_le : ∀ (p : VerifierProgram Bool) (h : List Ev), ¬ LuckBJ mid x h →
    esc (fun h' ↦ ¬ LuckBJ mid x h') h p ≤
      (((6 - (foldChalJ mid x h).length) + (4 - (foldChal1J mid x h).length) : ℕ) : ℝ≥0∞) * δLJ
  | .ret true, h, hB => by simp [esc, hB]
  | .ret false, _, _ => by simp [esc]
  | .fail, _, _ => by simp [esc]
  | .read k, h, hB => by simp [esc, hB]
  | .grind b k, h, hB => by simp [esc, hB]
  | .commit ht w k, h, hB => by simp [esc, hB]
  | .query i ps k, h, hB => by
    simp only [esc]
    split
    · rename_i rows _
      have hf := foldChal_snoc_of_ne (mid := mid) (x := x) h (Ev.query rows) rfl
      have hf1 := foldChal1J_snoc_of_ne (mid := mid) (x := x) h (Ev.query rows) rfl
      rw [foldChalJ, ← hf, ← hf1]
      exact esc_luckJ_le _ _ (not_luckBJ_snoc rfl hB)
    · exact zero_le
  | .sample k, h, hB => by
    simp only [esc]
    have hB0 : ¬ LuckB0J mid x h := fun h' ↦ hB (.inl h')
    have hB1 : ¬ LuckB1J mid x h := fun h' ↦ hB (.inr h')
    set n0 := (foldChal mid x h).length
    set n1 := (foldChal1J mid x h).length
    set k0 : ℕ := if Grows mid x h then 1 else 0
    set k1 : ℕ := if Grows1J mid x h then 1 else 0
    have hle0 : n0 + k0 ≤ 6 := length_foldChal_add_le h
    have hle1 : n1 + k1 ≤ 4 := length_foldChal1J_add_le h
    set N' : ℕ := (6 - (n0 + k0)) + (4 - (n1 + k1))
    set bad := Finset.univ.filter fun c : E ↦ LuckBJ mid x (h ++ [Ev.sample c])
    have hbad : bad.card ≤ (k0 + k1) * (311 * 2 ^ 15) := by
      refine (Finset.card_le_card (t := (Finset.univ.filter fun c : E ↦
          LuckB0J mid x (h ++ [Ev.sample c])) ∪ (Finset.univ.filter fun c : E ↦
          LuckB1J mid x (h ++ [Ev.sample c]))) fun c hc ↦ ?_).trans
        ((Finset.card_union_le _ _).trans ?_)
      · simp only [bad, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_union] at hc ⊢
        exact hc
      · rw [add_mul]
        exact add_le_add (card_bad0J_le hB0) (card_bad1J_le hB1)
    have hstep : ∀ c, esc (fun h' ↦ ¬ LuckBJ mid x h') (h ++ [Ev.sample c]) (k c) ≤
        (if c ∈ bad then 1 else 0) + (N' : ℝ≥0∞) * δLJ := by
      intro c
      by_cases hc : c ∈ bad
      · rw [if_pos hc]; exact (esc_le_one _ _ _).trans le_self_add
      · rw [if_neg hc, zero_add]
        have hB' : ¬ LuckBJ mid x (h ++ [Ev.sample c]) := by simpa [bad] using hc
        have := esc_luckJ_le (k c) _ hB'
        rwa [foldChalJ, length_foldChal_snoc, length_foldChal1J_snoc] at this
    have hK : (Fintype.card E : ℝ≥0∞)⁻¹ * bad.card ≤ ((k0 + k1 : ℕ) : ℝ≥0∞) * δLJ := by
      calc (Fintype.card E : ℝ≥0∞)⁻¹ * bad.card
          ≤ (Fintype.card E : ℝ≥0∞)⁻¹ * (((k0 + k1) * (311 * 2 ^ 15) : ℕ) : ℝ≥0∞) := by
            gcongr
        _ = ((k0 + k1 : ℕ) : ℝ≥0∞) * δLJ := by
            rw [δLJ, ENNReal.div_eq_inv_mul]; push_cast; ring
    calc (Fintype.card E : ℝ≥0∞)⁻¹ * ∑ c, esc (fun h' ↦ ¬ LuckBJ mid x h') (h ++ [Ev.sample c]) (k c)
        ≤ (Fintype.card E : ℝ≥0∞)⁻¹ * ∑ c : E, ((if c ∈ bad then 1 else 0) + (N' : ℝ≥0∞) * δLJ) := by
          gcongr with c; exact hstep c
      _ = (Fintype.card E : ℝ≥0∞)⁻¹ * bad.card + (N' : ℝ≥0∞) * δLJ := by
          rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_add,
            ← mul_assoc, ENNReal.inv_mul_cancel (by simp) (by simp), one_mul, Finset.sum_ite_mem,
            Finset.univ_inter, Finset.sum_const, nsmul_eq_mul, mul_one]
      _ ≤ ((k0 + k1 : ℕ) : ℝ≥0∞) * δLJ + (N' : ℝ≥0∞) * δLJ := by gcongr
      _ = (((6 - n0) + (4 - n1) : ℕ) : ℝ≥0∞) * δLJ := by
          rw [← add_mul, ← Nat.cast_add, show k0 + k1 + N' = (6 - n0) + (4 - n1) by omega]

/-- **`LuckBJ`'s group bound** (J2C-DES §3): `≤ 10 · 311·2^15/|E| ≤ 2^-132`. -/
theorem esc_luckJ_le_132 (p : VerifierProgram Bool) (h : List Ev) (hB : ¬ LuckBJ mid x h) :
    esc (fun h' ↦ ¬ LuckBJ mid x h') h p ≤ (2 : ℝ≥0∞)⁻¹ ^ 132 := by
  refine (esc_luckJ_le p h hB).trans (le_trans ?_ ten_δLJ_le)
  gcongr
  exact_mod_cast (show (6 - (foldChalJ mid x h).length) + (4 - (foldChal1J mid x h).length) ≤ 10
    by omega)

end Luck

end Lvm.ASM
