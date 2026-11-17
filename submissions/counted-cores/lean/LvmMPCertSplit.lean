-- New for lvm2 roll 11 (M′, R11-C): the history parser of M′'s run up to `C_main`'s residual, and the luck's
-- readers on it. Adapted from `LvmCertSExtJSplit` (`recPrefix_split`, `folds_splitJ`, `foldChal_of_splitJ`,
-- `rec1Of_of_splitJ`, `foldChal1J_of_splitJ`), with a level-generic step (`midTailPJ_split`).
import LvmMPCertOpen
import LvmCertSExtJSplit
import LvmCertSLuck
import LvmCertSJ
import LvmWhirParamsJ23

-- ===== merged from `LvmMPCertLuck` (GOLF module merge: `LvmMPCertLuck.lean` is now a stub importing `LvmMPCertSplit`) =====
section
-- New for lvm2 roll 11 (M′, R11-C): the extractor's luck at M′ (one commitment, `C_main` at `cfgMain23Jq 1`),
-- over the lists of its three levels (14 fold rounds). Adapted from `LvmCertSLuck`/`LvmCertSLuckJ` (`afterMid`,
-- `foldChal`, `rec1Of`, `foldChal1J`, `LuckB0J`, `LuckB1J`, `esc_luckJ_le`), generic in the reader.

/-!
# The luck of `P_S` at M′

The three decoders (`LvmMPDec`) need, off luck, that the fold challenges of each level are not lucky for the
list member they decode (a root candidate at level 0, a member of level 1's and level 2's lists). The luck
reads them off the history:

* **readers** `rd : List Ev → Option (Word × List Ev)` (a word and the events after it), kept by appends
  (`SnocRd`): `rd0M` (the root's word and the events after the middle phases), `rd1M`, `rd2M` (the next
  commitments after those: `C_main`'s level-1 and level-2 oracles, `nextRd`);
* `chalR rd d k h`: the samples after the reader's events, without the first `d`, at most `k`: level 0 drops
  `ρ` (`d = 1`, `k = 6`), level 1 the `17` OOD coordinates and level 0's query group (`1 + 15 + 2`; `d = 35`),
  level 2 the `13` OOD coordinates and level 1's query group (`1 + 10 + 2`; `d = 26`), `k = 4`;
* `LuckR rd d k Λ O`: some member of the list `Λ W` of the reader's word `W` is lucky (`RoundsLuck`) in the
  rounds drawn, on the rows `O W`; **`LuckBM`** is the disjunction at the three levels;
* a potential argument (`LuckPot`, `LuckPot.or`, `esc_le_pot`): a group from a history that is not lucky becomes
  lucky with probability at most `(rounds left) · M/|E|`, `M = 615·2^19 ≥ L·n` at every level
  (`124·2^19`, `231·2^16`, `615·2^13`); **`esc_luckBM_le_132`**: `14·615·2^19/|E| ≤ 2^-132` (it is
  `2^-159.93`).
-/

set_option autoImplicit false

namespace Lvm.ASM

open LeanVM.Parameters LeanVM.Protocol LeanVM.Protocol.Compile LeanVM.Protocol.Verifier
open LeanVM.Protocol.Compile.VerifierProgram LeanVM.Protocol.Whir.Sound LeanVM.Protocol.EndToEnd
open LeanVM.Protocol.Whir LeanVM.Protocol.Whir.Ud
open scoped ENNReal

/-! ## Readers -/

section Readers

variable {α β : Type}

/-- The events of a run of `p` and the events after `m` returned behind it. -/
def afterMidG (p : VerifierProgram α) (m : VerifierProgram β) (h : List Ev) : Option (List Ev × List Ev) :=
  match p.retSplit h with
  | none => none
  | some (_, l₁, l₂) => match m.retSplit l₂ with
    | none => none
    | some (_, _, l₃) => some (l₁, l₃)

theorem afterMidG_snoc (p : VerifierProgram α) (m : VerifierProgram β) (h : List Ev) (e : Ev) :
    (∀ l₁ l₃, afterMidG p m h = some (l₁, l₃) → afterMidG p m (h ++ [e]) = some (l₁, l₃ ++ [e])) ∧
      (afterMidG p m h = none → ∀ l₁ l₃, afterMidG p m (h ++ [e]) = some (l₁, l₃) → l₃ = []) := by
  constructor
  · intro l₁ l₃ hm
    unfold afterMidG at hm ⊢
    rcases hr : p.retSplit h with _ | ⟨a, m₁, m₂⟩ <;> rw [hr] at hm
    · cases hm
    · rw [(retSplit_snoc_cases _ h e).1 a m₁ m₂ hr]
      simp only at hm ⊢
      rcases hmid : m.retSplit m₂ with _ | ⟨b, n₁, n₂⟩ <;> rw [hmid] at hm
      · cases hm
      · simp only [Option.some.injEq, Prod.mk.injEq] at hm
        obtain ⟨rfl, rfl⟩ := hm
        rw [(retSplit_snoc_cases _ m₂ e).1 b n₁ n₂ hmid]
  · intro hm l₁ l₃ hm'
    unfold afterMidG at hm hm'
    rcases hr : p.retSplit h with _ | ⟨a, m₁, m₂⟩ <;> rw [hr] at hm
    · rcases hr' : p.retSplit (h ++ [e]) with _ | ⟨a', m₁', m₂'⟩ <;> rw [hr'] at hm'
      · cases hm'
      · have := (retSplit_snoc_cases _ h e).2 hr a' m₁' m₂' hr'
        subst this
        simp only at hm'
        rcases hmid : m.retSplit [] with _ | ⟨b, n₁, n₂⟩ <;> rw [hmid] at hm'
        · cases hm'
        · simp only [Option.some.injEq, Prod.mk.injEq] at hm'
          obtain ⟨rfl, rfl⟩ := hm'
          have h0 := (retSplit_eq_some_iff.1 hmid).1
          rw [eq_comm, List.append_eq_nil_iff] at h0
          exact h0.2
    · rw [(retSplit_snoc_cases _ h e).1 a m₁ m₂ hr] at hm'
      simp only at hm hm'
      rcases hmid : m.retSplit m₂ with _ | ⟨b, n₁, n₂⟩ <;> rw [hmid] at hm
      · rcases hmid' : m.retSplit (m₂ ++ [e]) with _ | ⟨b', n₁', n₂'⟩ <;> rw [hmid'] at hm'
        · cases hm'
        · simp only [Option.some.injEq, Prod.mk.injEq] at hm'
          obtain ⟨rfl, rfl⟩ := hm'
          exact (retSplit_snoc_cases _ m₂ e).2 hmid b' n₁' n₂' hmid'
      · cases hm

/-- **A reader kept by appends**: once it reads `(W, b)`, an appended event extends `b`; before, a reader
that starts at the appended event reads nothing after it. -/
def SnocRd (rd : List Ev → Option (Word × List Ev)) : Prop :=
  ∀ h e, (∀ W b, rd h = some (W, b) → rd (h ++ [e]) = some (W, b ++ [e])) ∧
    (rd h = none → ∀ W b, rd (h ++ [e]) = some (W, b) → b = [])

/-- The root reader: the first word of `p`'s run and the events after `m`. -/
def rootRd (p : VerifierProgram α) (m : VerifierProgram β) (h : List Ev) : Option (Word × List Ev) :=
  (afterMidG p m h).map fun l ↦ (wordOf (commits l.1) 0, l.2)

theorem snocRd_rootRd (p : VerifierProgram α) (m : VerifierProgram β) : SnocRd (rootRd p m) := by
  intro h e
  constructor
  · intro W b hr
    unfold rootRd at hr ⊢
    rcases ha : afterMidG p m h with _ | ⟨l₁, l₃⟩ <;> rw [ha] at hr
    · cases hr
    · rw [(afterMidG_snoc p m h e).1 l₁ l₃ ha]
      simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq] at hr ⊢
      exact ⟨hr.1, by rw [hr.2]⟩
  · intro hr W b hr'
    unfold rootRd at hr hr'
    rcases ha : afterMidG p m h with _ | ⟨l₁, l₃⟩ <;> rw [ha] at hr
    · rcases ha' : afterMidG p m (h ++ [e]) with _ | ⟨l₁', l₃'⟩ <;> rw [ha'] at hr'
      · cases hr'
      · simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq] at hr'
        rw [← hr'.2]
        exact (afterMidG_snoc p m h e).2 ha l₁' l₃' ha'
    · cases hr

/-- The reader of the next commitment after a reader's events. -/
def nextRd (rd : List Ev → Option (Word × List Ev)) (h : List Ev) : Option (Word × List Ev) :=
  (rd h).bind fun wb ↦ splitCommit wb.2

theorem snocRd_nextRd {rd : List Ev → Option (Word × List Ev)} (hrd : SnocRd rd) : SnocRd (nextRd rd) := by
  intro h e
  constructor
  · intro W b hr
    unfold nextRd at hr ⊢
    rcases ha : rd h with _ | ⟨W₀, b₀⟩ <;> rw [ha] at hr
    · cases hr
    · rw [(hrd h e).1 W₀ b₀ ha]
      exact (splitCommit_snoc b₀ e).1 W b hr
  · intro hr W b hr'
    unfold nextRd at hr hr'
    rcases ha : rd h with _ | ⟨W₀, b₀⟩ <;> rw [ha] at hr
    · rcases ha' : rd (h ++ [e]) with _ | ⟨W₀', b₀'⟩ <;> rw [ha'] at hr'
      · cases hr'
      · obtain rfl := (hrd h e).2 ha W₀' b₀' ha'
        simp [splitCommit] at hr'
    · rw [(hrd h e).1 W₀ b₀ ha] at hr'
      exact (splitCommit_snoc b₀ e).2 hr W b hr'

/-- **The challenges a reader reads**: the samples after its events, without the first `d`, at most `k`. -/
def chalR (rd : List Ev → Option (Word × List Ev)) (d k : ℕ) (h : List Ev) : List E :=
  match rd h with
  | none => []
  | some (_, b) => ((b.filterMap sampleOf).drop d).take k

/-- The word a reader reads (the empty word before it reads one). -/
def wdR (rd : List Ev → Option (Word × List Ev)) (h : List Ev) : Word :=
  match rd h with
  | none => fun _ ↦ []
  | some (W, _) => W

/-- A reader's challenges grow at the next challenge. -/
def GrowsR (rd : List Ev → Option (Word × List Ev)) (d k : ℕ) (h : List Ev) : Prop :=
  ∃ W b, rd h = some (W, b) ∧ d ≤ (b.filterMap sampleOf).length ∧ (b.filterMap sampleOf).length < d + k

variable {rd : List Ev → Option (Word × List Ev)} {d k : ℕ}

theorem wdR_of_rd {h : List Ev} {W : Word} {b : List Ev} (hr : rd h = some (W, b)) : wdR rd h = W := by
  unfold wdR; rw [hr]

theorem chalR_snoc_of_ne (hrd : SnocRd rd) (h : List Ev) (e : Ev) (he : sampleOf e = none) :
    chalR rd d k (h ++ [e]) = chalR rd d k h := by
  unfold chalR
  rcases hr : rd h with _ | ⟨W, b⟩
  · rcases hr' : rd (h ++ [e]) with _ | ⟨W', b'⟩
    · rfl
    · rw [(hrd h e).2 hr W' b' hr']; simp
  · rw [(hrd h e).1 W b hr]
    simp [List.filterMap_append, he]

open Classical in
theorem chalR_snoc_sample (hrd : SnocRd rd) (h : List Ev) (c : E) :
    chalR rd d k (h ++ [Ev.sample c]) = if GrowsR rd d k h then chalR rd d k h ++ [c] else chalR rd d k h := by
  unfold chalR
  rcases hr : rd h with _ | ⟨W, b⟩
  · have hg : ¬ GrowsR rd d k h := by rintro ⟨_, _, h', -⟩; rw [hr] at h'; cases h'
    rw [if_neg hg]
    rcases hr' : rd (h ++ [Ev.sample c]) with _ | ⟨W', b'⟩
    · rfl
    · rw [(hrd h _).2 hr W' b' hr']; simp
  · rw [(hrd h _).1 W b hr]
    dsimp only
    rw [List.filterMap_append, show [Ev.sample c].filterMap sampleOf = [c] from rfl]
    set S := b.filterMap sampleOf
    by_cases h1 : d ≤ S.length
    · by_cases h2 : S.length < d + k
      · have hg : GrowsR rd d k h := ⟨W, b, hr, h1, h2⟩
        rw [if_pos hg, List.drop_append_of_le_length h1,
          List.take_of_length_le (by simp; (clear * - h1 h2; omega)), List.take_of_length_le (by simp; (clear * - h2; omega))]
      · have hg : ¬ GrowsR rd d k h := by
          rintro ⟨_, _, h', -, h3⟩; rw [hr] at h'; cases h'; exact h2 h3
        rw [if_neg hg, List.drop_append_of_le_length h1,
          List.take_append_of_le_length (by simp; (clear * - h1 h2; omega))]
    · have hg : ¬ GrowsR rd d k h := by
        rintro ⟨_, _, h', h3, -⟩; rw [hr] at h'; cases h'; exact h1 h3
      rw [if_neg hg, List.drop_eq_nil_of_le (by simp; (clear * - h1; omega)),
        List.drop_eq_nil_of_le (by (clear * - h1; omega))]

theorem length_chalR_le (h : List Ev) : (chalR rd d k h).length ≤ k := by
  unfold chalR
  split
  · simp
  · simp

theorem length_chalR_of_grows {h : List Ev} (hg : GrowsR rd d k h) : (chalR rd d k h).length < k := by
  obtain ⟨W, b, hr, hd, hl⟩ := hg
  unfold chalR
  rw [hr]
  simp only [List.length_take, List.length_drop]
  (clear * - hd hl; omega)

theorem rd_of_chalR_ne {h : List Ev} (hne : chalR rd d k h ≠ []) : ∃ W b, rd h = some (W, b) := by
  unfold chalR at hne
  rcases hr : rd h with _ | ⟨W, b⟩
  · rw [hr] at hne; exact absurd rfl hne
  · exact ⟨W, b, rfl⟩

open Classical in
theorem length_chalR_snoc (hrd : SnocRd rd) (h : List Ev) (c : E) :
    (chalR rd d k (h ++ [Ev.sample c])).length = (chalR rd d k h).length + if GrowsR rd d k h then 1 else 0 := by
  rw [chalR_snoc_sample hrd]; split_ifs <;> simp

open Classical in
theorem length_chalR_add_le (h : List Ev) :
    (chalR rd d k h).length + (if GrowsR rd d k h then 1 else 0) ≤ k := by
  split_ifs with hg
  · exact length_chalR_of_grows hg
  · simpa using length_chalR_le h

end Readers

/-! ## Luck at a reader -/

section LuckR

variable {rd : List Ev → Option (Word × List Ev)} {d k : ℕ} {ι : Type} [Fintype ι]
  {Λ : Word → Set ((Fin k → Bool) → ι → E)} {O : Word → (Fin k → Bool) → ι → E}

/-- **Luck at a reader**: some member of the list `Λ W` of the reader's word `W` is lucky in the rounds drawn,
on the rows `O W`. -/
def LuckR (rd : List Ev → Option (Word × List Ev)) (d k : ℕ) {ι : Type} [Fintype ι]
    (Λ : Word → Set ((Fin k → Bool) → ι → E)) (O : Word → (Fin k → Bool) → ι → E) (h : List Ev) : Prop :=
  ∃ V ∈ Λ (wdR rd h), RoundsLuck k (chalR rd d k h) (O (wdR rd h)) V

theorem not_luckR_of_nil {h : List Ev} (hn : chalR rd d k h = []) : ¬ LuckR rd d k Λ O h := by
  rintro ⟨V, -, hV⟩
  rw [hn] at hV
  exact roundsLuck_nil _ _ _ hV

theorem luckR_snoc_iff (hrd : SnocRd rd) {h : List Ev} {e : Ev}
    (hf : chalR rd d k (h ++ [e]) = chalR rd d k h) :
    LuckR rd d k Λ O (h ++ [e]) ↔ LuckR rd d k Λ O h := by
  by_cases hn : chalR rd d k h = []
  · exact ⟨fun h' ↦ absurd h' (not_luckR_of_nil (hf.trans hn)), fun h' ↦ absurd h' (not_luckR_of_nil hn)⟩
  · obtain ⟨W, b, hr⟩ := rd_of_chalR_ne hn
    unfold LuckR
    rw [wdR_of_rd ((hrd h e).1 W b hr), wdR_of_rd hr, hf]

theorem not_luckR_nil (h0 : rd [] = none) : ¬ LuckR rd d k Λ O [] :=
  not_luckR_of_nil (by unfold chalR; rw [h0])

open Classical in
/-- The challenges at which the luck at a reader starts: at most `L·|ι|` for lists of at most `L` members, and
none unless the reader's challenges grow. -/
theorem card_badR_le (hrd : SnocRd rd) {L : ℕ} (hfin : ∀ W, (Λ W).Finite) (hL : ∀ W, (Λ W).ncard ≤ L)
    {h : List Ev} (hB : ¬ LuckR rd d k Λ O h) :
    (Finset.univ.filter fun c : E ↦ LuckR rd d k Λ O (h ++ [Ev.sample c])).card ≤
      (if GrowsR rd d k h then 1 else 0) * (L * Fintype.card ι) := by
  by_cases hg : GrowsR rd d k h
  · rw [if_pos hg, one_mul]
    have hlt := length_chalR_of_grows hg
    obtain ⟨W, b, hr, -⟩ := id hg
    have hW : ∀ c, wdR rd (h ++ [Ev.sample c]) = wdR rd h := fun c ↦ by
      rw [wdR_of_rd ((hrd h _).1 W b hr), wdR_of_rd hr]
    set F := (hfin (wdR rd h)).toFinset
    have key : ∀ c, LuckR rd d k Λ O (h ++ [Ev.sample c]) ↔
        ∃ V ∈ F, RoundsLuck k (chalR rd d k h ++ [c]) (O (wdR rd h)) V := by
      intro c
      unfold LuckR
      rw [hW c, chalR_snoc_sample hrd, if_pos hg]
      simp only [F, Set.Finite.mem_toFinset]
    simp only [key]
    have hF : F.card ≤ L := by
      rw [← Set.ncard_eq_toFinset_card _ (hfin _)]; exact hL _
    refine card_luck_snoc_le F hF _ _ hlt fun ⟨V, hV, hl⟩ ↦ hB ⟨V, ?_, hl⟩
    simpa [F] using hV
  · rw [if_neg hg, zero_mul]
    refine le_trans (Finset.card_le_card (t := ∅) fun c hc' ↦ ?_) (by simp)
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hc'
    exact absurd ((luckR_snoc_iff hrd (by rw [chalR_snoc_sample hrd, if_neg hg])).1 hc') hB

end LuckR

/-! ## The potential argument -/

/-- **A potential for a luck predicate**: events that are no challenge keep it out and the potential; at a
challenge from outside it, the potential drops by some `k`, and at most `k·M` challenges make it hold. -/
structure LuckPot (B : List Ev → Prop) (φ : List Ev → ℕ) (M : ℕ) : Prop where
  ne : ∀ h e, sampleOf e = none → ¬ B h → ¬ B (h ++ [e]) ∧ φ (h ++ [e]) = φ h
  smp : ∀ h, ¬ B h → ∃ k, (∀ c, φ (h ++ [Ev.sample c]) + k ≤ φ h) ∧
    ∀ [DecidablePred fun c : E ↦ B (h ++ [Ev.sample c])],
      (Finset.univ.filter fun c : E ↦ B (h ++ [Ev.sample c])).card ≤ k * M

namespace LuckPot

variable {B B' : List Ev → Prop} {φ φ' : List Ev → ℕ} {M M' : ℕ}

theorem mono_M (P : LuckPot B φ M) (hM : M ≤ M') : LuckPot B φ M' where
  ne := P.ne
  smp h hB := by
    obtain ⟨k, h1, h2⟩ := P.smp h hB
    exact ⟨k, h1, fun {_} ↦ h2.trans (Nat.mul_le_mul_left k hM)⟩

theorem or (P : LuckPot B φ M) (P' : LuckPot B' φ' M) : LuckPot (fun h ↦ B h ∨ B' h) (fun h ↦ φ h + φ' h) M where
  ne h e he hB := by
    have hB1 : ¬ B h := fun h' ↦ hB (.inl h')
    have hB2 : ¬ B' h := fun h' ↦ hB (.inr h')
    obtain ⟨n1, e1⟩ := P.ne h e he hB1
    obtain ⟨n2, e2⟩ := P'.ne h e he hB2
    exact ⟨fun h' ↦ h'.elim n1 n2, by rw [e1, e2]⟩
  smp h hB := by
    classical
    have hB1 : ¬ B h := fun h' ↦ hB (.inl h')
    have hB2 : ¬ B' h := fun h' ↦ hB (.inr h')
    obtain ⟨k1, f1, c1⟩ := P.smp h hB1
    obtain ⟨k2, f2, c2⟩ := P'.smp h hB2
    refine ⟨k1 + k2, fun c ↦ by have := f1 c; have := f2 c; (clear P P' c1 c2 f1 f2 hB hB1 hB2; omega), fun {_} ↦ ?_⟩
    refine (Finset.card_le_card (t := (Finset.univ.filter fun c : E ↦ B (h ++ [Ev.sample c])) ∪
        (Finset.univ.filter fun c : E ↦ B' (h ++ [Ev.sample c]))) fun c hc ↦ ?_).trans
      ((Finset.card_union_le _ _).trans ?_)
    · simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_union] at hc ⊢
      exact hc
    · rw [add_mul]
      exact add_le_add (by convert c1) (by convert c2)

end LuckPot

open Classical in
/-- **The group bound from a potential**: from a history outside `B`, a group ends inside `B` with probability
at most `φ h · M/|E|`. -/
theorem esc_le_pot {B : List Ev → Prop} {φ : List Ev → ℕ} {M : ℕ} (P : LuckPot B φ M) :
    ∀ (p : VerifierProgram Bool) (h : List Ev), ¬ B h →
      esc (fun h' ↦ ¬ B h') h p ≤ (φ h : ℝ≥0∞) * ((M : ℝ≥0∞) / Fintype.card E)
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
      obtain ⟨hB', hφ⟩ := P.ne h (Ev.query rows) rfl hB
      rw [← hφ]
      exact esc_le_pot P _ _ hB'
    · exact zero_le
  | .sample k, h, hB => by
    simp only [esc]
    obtain ⟨k0, hf, hc⟩ := P.smp h hB
    set δ : ℝ≥0∞ := (M : ℝ≥0∞) / Fintype.card E
    set bad := Finset.univ.filter fun c : E ↦ B (h ++ [Ev.sample c])
    have hbad : bad.card ≤ k0 * M := hc
    have hstep : ∀ c, esc (fun h' ↦ ¬ B h') (h ++ [Ev.sample c]) (k c) ≤
        (if c ∈ bad then 1 else 0) + ((φ h - k0 : ℕ) : ℝ≥0∞) * δ := by
      intro c
      by_cases hcb : c ∈ bad
      · rw [if_pos hcb]; exact (esc_le_one _ _ _).trans le_self_add
      · rw [if_neg hcb, zero_add]
        have hB' : ¬ B (h ++ [Ev.sample c]) := by simpa [bad] using hcb
        refine (esc_le_pot P (k c) _ hB').trans ?_
        gcongr
        have := hf c
        (clear * - this; omega)
    have hK : (Fintype.card E : ℝ≥0∞)⁻¹ * bad.card ≤ (k0 : ℝ≥0∞) * δ := by
      calc (Fintype.card E : ℝ≥0∞)⁻¹ * bad.card
          ≤ (Fintype.card E : ℝ≥0∞)⁻¹ * ((k0 * M : ℕ) : ℝ≥0∞) := by gcongr
        _ = (k0 : ℝ≥0∞) * δ := by simp only [δ, ENNReal.div_eq_inv_mul]; push_cast; ring
    have hk0 : k0 ≤ φ h := by have := hf (0 : E); (clear * - this; omega)
    calc (Fintype.card E : ℝ≥0∞)⁻¹ * ∑ c, esc (fun h' ↦ ¬ B h') (h ++ [Ev.sample c]) (k c)
        ≤ (Fintype.card E : ℝ≥0∞)⁻¹ * ∑ c : E, ((if c ∈ bad then 1 else 0) + ((φ h - k0 : ℕ) : ℝ≥0∞) * δ) := by
          gcongr with c; exact hstep c
      _ = (Fintype.card E : ℝ≥0∞)⁻¹ * bad.card + ((φ h - k0 : ℕ) : ℝ≥0∞) * δ := by
          rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_add,
            ← mul_assoc, ENNReal.inv_mul_cancel (by simp) (by simp), one_mul, Finset.sum_ite_mem,
            Finset.univ_inter, Finset.sum_const, nsmul_eq_mul, mul_one]
      _ ≤ (k0 : ℝ≥0∞) * δ + ((φ h - k0 : ℕ) : ℝ≥0∞) * δ := by gcongr
      _ = (φ h : ℝ≥0∞) * δ := by rw [← add_mul, ← Nat.cast_add, Nat.add_sub_cancel' hk0]

/-- **The potential of the luck at a reader**: the rounds left, `M = L·|ι|`. -/
theorem pot_luckR {rd : List Ev → Option (Word × List Ev)} (hrd : SnocRd rd) (d k : ℕ) {ι : Type}
    [Fintype ι] {Λ : Word → Set ((Fin k → Bool) → ι → E)} (O : Word → (Fin k → Bool) → ι → E) {L : ℕ}
    (hfin : ∀ W, (Λ W).Finite) (hL : ∀ W, (Λ W).ncard ≤ L) :
    LuckPot (LuckR rd d k Λ O) (fun h ↦ k - (chalR rd d k h).length) (L * Fintype.card ι) where
  ne h e he hB := by
    have hf := chalR_snoc_of_ne (d := d) (k := k) hrd h e he
    exact ⟨fun h' ↦ hB ((luckR_snoc_iff hrd hf).1 h'), by rw [hf]⟩
  smp h hB := by
    classical
    refine ⟨if GrowsR rd d k h then 1 else 0, fun c ↦ ?_, fun {_} ↦ ?_⟩
    · have := length_chalR_add_le (rd := rd) (d := d) (k := k) h
      rw [length_chalR_snoc hrd]
      (clear * - this; omega)
    · convert card_badR_le hrd hfin hL hB

/-! ## M′'s luck -/

section M

variable (mid : List UInt8 → VerifierProgram (List LeanVM.Protocol.Verifier.StackClaim)) (x : List UInt8)

/-- **M′'s level-0 reader**: the root word, the events after the middle phases. -/
def rd0M : List Ev → Option (Word × List Ev) := rootRd (commitRootUd cfgMain24G) (mid x)

/-- **M′'s level-1 reader**: `C_main`'s level-1 oracle (the first commitment after the middle phases). -/
def rd1M : List Ev → Option (Word × List Ev) := nextRd (rd0M mid x)

/-- **M′'s level-2 reader**: `C_main`'s level-2 oracle (the second commitment after the middle phases). -/
def rd2M : List Ev → Option (Word × List Ev) := nextRd (rd1M mid x)

/-- Level 0's list: the encodings of the root's candidates at `(codesMain23Jq 0).thr` (at most `124`). -/
def Λ0M (W : Word) : Set ((Fin LeanVM.Protocol.EndToEnd.laneBits → Bool) →
    Fin (2 ^ (CMain.nu20 - LeanVM.Protocol.EndToEnd.laneBits + 2)) → E) :=
  encRows CMain.nu20 2 '' Candidates CMain.nu20 2 (codesMain23Jq 0).thr W

/-- Level `j ≥ 1`'s list (`codesMain23Jq j`) of the level's rows. -/
def ΛjM (j : ℕ) (W : Word) : Set ((Fin 4 → Bool) → Fin (codesMain23Jq j).n → E) :=
  ↑(iList (codesMain23Jq j).code (codesMain23Jq j).thr (rows1 4 (codesMain23Jq j).n W))

/-- **The luck of `P_S` at M′**: a root candidate lucky in level 0's six rounds, or a member of level 1's or
level 2's list lucky in its four. -/
def LuckBM (h : List Ev) : Prop :=
  LuckR (rd0M mid x) 1 LeanVM.Protocol.EndToEnd.laneBits (Λ0M) (laneRows CMain.nu20 2) h ∨
    LuckR (rd1M mid x) 35 4 (ΛjM 1) (rows1 4 (codesMain23Jq 1).n) h ∨
    LuckR (rd2M mid x) 26 4 (ΛjM 2) (rows1 4 (codesMain23Jq 2).n) h

/-- The potential of `LuckBM`: the fold rounds left at the three levels (at most `14`). -/
def φM (h : List Ev) : ℕ :=
  (LeanVM.Protocol.EndToEnd.laneBits - (chalR (rd0M mid x) 1 LeanVM.Protocol.EndToEnd.laneBits h).length) +
    ((4 - (chalR (rd1M mid x) 35 4 h).length) + (4 - (chalR (rd2M mid x) 26 4 h).length))

end M

section MLemmas

variable {mid : List UInt8 → VerifierProgram (List LeanVM.Protocol.Verifier.StackClaim)} {x : List UInt8}

theorem snocRd_rd0M : SnocRd (rd0M mid x) := snocRd_rootRd _ _
theorem snocRd_rd1M : SnocRd (rd1M mid x) := snocRd_nextRd snocRd_rd0M
theorem snocRd_rd2M : SnocRd (rd2M mid x) := snocRd_nextRd snocRd_rd1M

theorem rd0M_nil : rd0M mid x [] = none := by
  unfold rd0M rootRd afterMidG
  have : (commitRootUd cfgMain24G).retSplit [] = none := by
    simp [commitRootUd, cfgMain24G, VerifierProgram.readCommitment, retSplit]
  rw [this]; rfl

theorem rd1M_nil : rd1M mid x [] = none := by unfold rd1M nextRd; rw [rd0M_nil]; rfl
theorem rd2M_nil : rd2M mid x [] = none := by unfold rd2M nextRd; rw [rd1M_nil]; rfl

theorem finite_Λ0M (W : Word) : (Λ0M W).Finite := (Set.toFinite _).image _

theorem ncard_Λ0M_le (W : Word) : (Λ0M W).ncard ≤ 124 :=
  (Set.ncard_image_le (Set.toFinite _)).trans (candidates_main23Jq_ncard_le W)

theorem finite_ΛjM (j : ℕ) (W : Word) : (ΛjM j W).Finite := Finset.finite_toSet _

theorem ncard_ΛjM_le (j : ℕ) (W : Word) : (ΛjM j W).ncard ≤ (codesMain23Jq j).listMax := by
  unfold ΛjM
  rw [Set.ncard_coe_finset]
  exact (codesMain23Jq j).card_iList_le _

/-- **The potential of M′'s luck**, at `M = 615·2^19`. -/
theorem pot_luckBM : LuckPot (LuckBM mid x) (φM mid x) (615 * 2 ^ 19) := by
  have P0 := (pot_luckR (snocRd_rd0M (mid := mid) (x := x)) 1 LeanVM.Protocol.EndToEnd.laneBits (laneRows CMain.nu20 2)
    finite_Λ0M ncard_Λ0M_le).mono_M (M' := 615 * 2 ^ 19) (by
      rw [Fintype.card_fin]; norm_num)
  have P1 := (pot_luckR (snocRd_rd1M (mid := mid) (x := x)) 35 4 (rows1 4 (codesMain23Jq 1).n) (finite_ΛjM 1) (ncard_ΛjM_le 1)).mono_M (M' := 615 * 2 ^ 19) (by
      rw [Fintype.card_fin]; norm_num [codesMain23Jq, codeJ13R3, LevelCode.n])
  have P2 := (pot_luckR (snocRd_rd2M (mid := mid) (x := x)) 26 4 (rows1 4 (codesMain23Jq 2).n) (finite_ΛjM 2) (ncard_ΛjM_le 2)).mono_M (M' := 615 * 2 ^ 19) (by
      rw [Fintype.card_fin]; norm_num [codesMain23Jq, codeJ9R4, LevelCode.n])
  exact P0.or (P1.or P2)

/-- A prover move or an opening keeps M′'s luck out. -/
theorem not_luckBM_snoc {h : List Ev} {e : Ev} (he : sampleOf e = none) (hB : ¬ LuckBM mid x h) :
    ¬ LuckBM mid x (h ++ [e]) :=
  (pot_luckBM.ne h e he hB).1

theorem not_luckBM_nil : ¬ LuckBM mid x [] := by
  rintro (h' | h' | h')
  · exact not_luckR_nil rd0M_nil h'
  · exact not_luckR_nil rd1M_nil h'
  · exact not_luckR_nil rd2M_nil h'

/-- Fourteen rounds at `615·2^19` fit the luck budget: `14·615·2^19/|E| ≤ 2^-132`. -/
theorem fourteen_δM_le :
    (14 : ℝ≥0∞) * (((615 * 2 ^ 19 : ℕ) : ℝ≥0∞) / Fintype.card E) ≤ (2 : ℝ≥0∞)⁻¹ ^ 132 := by
  rw [card_E_ennreal, ← mul_div_assoc, ← two_pow_cast 192,
    show (14 : ℝ≥0∞) * ((615 * 2 ^ 19 : ℕ) : ℝ≥0∞) = ((14 * (615 * 2 ^ 19) : ℕ) : ℝ≥0∞) by push_cast; ring]
  exact natCast_div_le_inv_pow (by positivity) (by norm_num)

/-- **M′'s luck group bound**: `≤ 14·615·2^19/|E| ≤ 2^-132`. -/
theorem esc_luckBM_le_132 (p : VerifierProgram Bool) (h : List Ev) (hB : ¬ LuckBM mid x h) :
    esc (fun h' ↦ ¬ LuckBM mid x h') h p ≤ (2 : ℝ≥0∞)⁻¹ ^ 132 := by
  refine (esc_le_pot pot_luckBM p h hB).trans (le_trans ?_ fourteen_δM_le)
  gcongr
  have h0 := length_chalR_le (rd := rd0M mid x) (d := 1) (k := LeanVM.Protocol.EndToEnd.laneBits) h
  exact_mod_cast (show φM mid x h ≤ 14 by unfold φM; simp only [LeanVM.Protocol.EndToEnd.laneBits] at *; (clear * - h0; omega))

end MLemmas

end Lvm.ASM
end
-- ===== end of `LvmMPCertLuck` =====

/-!
# M′'s history parser

`C_main`'s opening at M′ (`stackPrefixJ (cfgMain23Jq 1)`, levels `(6,2,115) (4,3,77) (4,4,58)`, `g = 14`, OOD)
up to the residual: `ρ`, the first round polynomial, level 0's six fold rounds, then twice a level step
(`midTailPJ_split`: the next level's cap, the OOD point, answer and intro, the query group, the query intro;
`17 + 18 = 35` and `13 + 13 = 26` challenges, no commitment) and the next level's four fold rounds, then the
residual.

* **`mainPrefix_split`**: a completed run of the program up to the residual (`LvmMPCert`'s `mainPrefixProg`) is
  the root `W₀`, the middle phases, and the opening as above, with the level-1 and level-2 caps `W₁`, `W₂` and
  the fold states `r0`, `r1`, `r2` (`r2.1.folds = r0.2 ++ r1.2 ++ r2.2`);
* **`readersM_of_split`**: on such a history (and any events after it) the luck's readers read `W₀, W₁, W₂`
  and the fold challenges `r0.2, r1.2, r2.2`.
-/

set_option autoImplicit false

namespace Lvm.ASM

open RecursionFast Lvm.FS Lvm.T
open LeanVM.Parameters LeanVM.Protocol LeanVM.Protocol.Compile LeanVM.Protocol.Verifier
open LeanVM.Protocol.Compile.VerifierProgram LeanVM.Protocol.Whir.Sound LeanVM.Protocol.EndToEnd
open LeanVM.Protocol.Whir

/-! ## A level step -/

theorem take_drop_appendM {S A B : List E} {d k : ℕ} (hS : S.length = d) (hA : A.length = k) :
    ((S ++ (A ++ B)).drop d).take k = A := by
  rw [List.drop_left' hS, List.take_left' hA]

/-- **A level with a next level, after its fold rounds** (`midTailPJ`, `g ≠ 0`): the next level's cap, then
`μ − |folds|` OOD coordinates, the query group's `1 + (posCount + 2)` challenges and reads, no commitment; then
the next levels from a state with the same fold challenges. -/
theorem midTailPJ_split {μ per c₀ n₀ g i : ℕ} {level next : Whir.Level} {rest : List Whir.Level}
    {r : WhirStateT × List E} {l : List Ev} {b : (WhirStateT × List E) × List E} (hg : g ≠ 0)
    (h : (midTailPJ μ per c₀ n₀ g i level next rest r).after l = some (.ret b)) :
    ∃ (W : Compile.Word) (lm l' : List Ev) (s' : WhirStateT),
      l = Ev.commit (μ - r.1.folds.length - next.fold + next.logInvRate) (3 * 2 ^ next.fold) W :: (lm ++ l') ∧
      commits lm = [] ∧
      (lm.filterMap sampleOf).length = (μ - r.1.folds.length) + (1 + (posCount per level.queries level.queries + 2)) ∧
      s'.folds = r.1.folds ∧ (whirPrefixJ μ per c₀ n₀ g (i + 1) (next :: rest) s').after l' = some (.ret b) := by
  unfold midTailPJ at h
  obtain ⟨_, lc, l₁, rfl, hc, h1⟩ := after_bind_ret h
  obtain ⟨W, rfl⟩ := readCommitment_after hc
  obtain ⟨z, lz, l₂, rfl, hz, h2⟩ := after_bind_ret h1
  obtain ⟨y, ly, l₃, rfl, hy, h3⟩ := after_bind_ret h2
  obtain ⟨hy', lhy, l₄, rfl, hhy, h4⟩ := after_bind_ret h3
  obtain ⟨_, lgp, l₅, rfl, hgp, h5⟩ := after_bind_ret h4
  rw [query_bindG'] at h5
  obtain ⟨gg, lgq, l₆, rfl, hgq, h6⟩ := after_bind_ret h5
  unfold midFinishPJ at h6
  obtain ⟨hq, lhq, l₇, rfl, hhq, h7⟩ := after_bind_ret h6
  obtain ⟨rfl, hzl⟩ := sampleChallenges_after _ hz
  refine ⟨W, z.map Ev.sample ++ (ly ++ (lhy ++ (lgp ++ (lgq ++ lhq)))), l₇, _, by simp, ?_, ?_,
    glueMid_folds _ _ _ _ _ _ _ _, h7⟩
  · simp only [LeanVM.Protocol.Whir.Sound.commits_append,
      NoCommit.after_commits (nc_sampleChallenges _) hz,
      NoCommit.after_commits (p := readScalar) nc_readScalar hy,
      NoCommit.after_commits (nc_roundPoly _ _ _) hhy, NoCommit.after_commits (nc_grindPre _) hgp,
      NoCommit.after_commits (NoCommit.bind (nc_powCheck _) fun _ ↦ nc_queryFrag _ _ _ _) hgq,
      NoCommit.after_commits (nc_roundPoly _ _ _) hhq, List.nil_append]
  · simp only [List.filterMap_append, filterMap_sample_map,
      MovesOnly.after_samples (p := readScalar) (fun _ ↦ trivial) hy,
      MovesOnly.after_samples (movesOnly_roundPoly _) hhy,
      MovesOnly.after_samples (movesOnly_roundPoly _) hhq, List.nil_append, List.append_nil,
      List.length_append, hzl, grindPre_after_samples hg hgp, queryFragG_after_samples hg hgq]

/-- The fold rounds' run: their challenges are the run's samples, no commitment. -/
theorem foldRoundsT_run {n : ℕ} {s : WhirStateT} {l : List Ev} {r : WhirStateT × List E}
    (h : (foldRoundsT n s []).after l = some (.ret r)) :
    commits l = [] ∧ l.filterMap sampleOf = r.2 ∧ r.2.length = n ∧ r.1.folds = s.folds ++ r.2 := by
  obtain ⟨e1, e2, e3, -, -⟩ := foldRoundsT_after n s [] h
  rw [List.nil_append] at e1
  exact ⟨NoCommit.after_commits (nc_foldRoundsT _ _ _) h, e1.symm, by rw [e1]; exact e2, by rw [e3, e1]⟩

/-! ## The run up to the residual -/

section Split

variable {mid : List UInt8 → VerifierProgram (List LeanVM.Protocol.Verifier.StackClaim)} {x : List UInt8}

/-- **A completed run of M′'s program up to the residual** (`LvmMPCert`'s `mainPrefixProg`): the root `W₀`, the
middle phases, `ρ`, the first round polynomial, level 0's fold rounds (`r0`), level 1's cap `W₁`, `35` challenges,
level 1's fold rounds (`r1`), level 2's cap `W₂`, `26` challenges, level 2's fold rounds (`r2`), the residual. -/
theorem mainPrefix_split {h₁ : List Ev} {cl : List LeanVM.Protocol.Verifier.StackClaim}
    {a : E × ((WhirStateT × List E) × List E)}
    (hpre : (commitRootUd cfgMain24G >>= fun _ ↦ mid x >>= fun cl ↦
      stackPrefixJ (cfgMain23Jq 1) cl >>= fun a ↦ VerifierProgram.ret (cl, a)).after h₁ = some (.ret (cl, a))) :
    ∃ (W₀ : Compile.Word) (lm : List Ev) (ρ : E) (lq lf0 : List Ev) (r0 : WhirStateT × List E) (ht1 : ℕ) (W₁ : Compile.Word)
      (lm0 lf1 : List Ev) (r1 : WhirStateT × List E) (ht2 : ℕ) (W₂ : Compile.Word) (lm1 lf2 : List Ev)
      (r2 : WhirStateT × List E) (lres : List Ev) (res : List E),
      h₁ = Ev.commit 19 64 W₀ :: (lm ++ (Ev.sample ρ :: (lq ++ (lf0 ++ (Ev.commit ht1 (3 * 2 ^ 4) W₁ ::
        (lm0 ++ (lf1 ++ (Ev.commit ht2 (3 * 2 ^ 4) W₂ :: (lm1 ++ (lf2 ++ lres)))))))))) ∧
      a = (ρ, (r2, res)) ∧ (mid x).after lm = some (.ret cl) ∧
      commits lq = [] ∧ lq.filterMap sampleOf = [] ∧
      commits lf0 = [] ∧ lf0.filterMap sampleOf = r0.2 ∧ r0.2.length = 6 ∧ r0.1.folds = r0.2 ∧
      commits lm0 = [] ∧ (lm0.filterMap sampleOf).length = 35 ∧
      commits lf1 = [] ∧ lf1.filterMap sampleOf = r1.2 ∧ r1.2.length = 4 ∧ r1.1.folds = r0.1.folds ++ r1.2 ∧
      commits lm1 = [] ∧ (lm1.filterMap sampleOf).length = 26 ∧
      commits lf2 = [] ∧ lf2.filterMap sampleOf = r2.2 ∧ r2.2.length = 4 ∧ r2.1.folds = r1.1.folds ++ r2.2 ∧
      commits lres = [] ∧ lres.filterMap sampleOf = [] := by
  obtain ⟨_, hr, l₂, rfl, h1, h2⟩ := after_bind_ret (p := commitRootUd cfgMain24G) hpre
  obtain ⟨W₀, rfl⟩ := readCommitment_after (ht := 19) (w := 64) h1
  obtain ⟨cl', lm, l₃, rfl, h3, h4⟩ := after_bind_ret (p := mid x) h2
  obtain ⟨a', lp, l₄, rfl, h5, h6⟩ := after_bind_ret (p := stackPrefixJ (cfgMain23Jq 1) cl') h4
  obtain ⟨rfl, rfl, rfl⟩ : l₄ = [] ∧ cl' = cl ∧ a' = a := by
    cases l₄ with
    | nil => simp [VerifierProgram.after] at h6; exact ⟨rfl, h6⟩
    | cons e es => cases e <;> simp [VerifierProgram.after] at h6
  unfold stackPrefixJ at h5
  obtain ⟨ρ, l₆, l₇, rfl, h6, h7⟩ := after_bind_ret (p := sampleChallenge) h5
  obtain rfl := sample_after h6
  obtain ⟨quad, lq, l₈, rfl, h8, h9⟩ := after_bind_ret h7
  obtain ⟨b, lw, l₉, rfl, h10, h11⟩ := after_bind_ret h9
  obtain ⟨rfl, rfl⟩ : l₉ = [] ∧ (ρ, b) = a' := by
    cases l₉ with
    | nil => simp [VerifierProgram.after] at h11; exact ⟨rfl, h11⟩
    | cons e es => cases e <;> simp [VerifierProgram.after] at h11
  change (whirPrefixJ 23 8 0 1 14 0 [⟨6, 2, 115⟩, ⟨4, 3, 77⟩, ⟨4, 4, 58⟩] _).after lw = _ at h10
  rw [whirPrefixJ_mid] at h10
  obtain ⟨r0, lf0, l₁₀, rfl, hf0, h12⟩ := after_bind_ret h10
  obtain ⟨W₁, lm0, l₁₁, s1, rfl, hc0, hs0, hfs1, h13⟩ := midTailPJ_split (by decide) h12
  rw [whirPrefixJ_mid] at h13
  obtain ⟨r1, lf1, l₁₂, rfl, hf1, h14⟩ := after_bind_ret h13
  obtain ⟨W₂, lm1, l₁₃, s2, rfl, hc1, hs1, hfs2, h15⟩ := midTailPJ_split (by decide) h14
  rw [whirPrefixJ_one] at h15
  obtain ⟨r2, lf2, l₁₄, rfl, hf2, h16⟩ := after_bind_ret h15
  obtain ⟨res, lres, l₁₅, rfl, hres, h17⟩ := after_bind_ret h16
  obtain ⟨rfl, rfl⟩ : l₁₅ = [] ∧ (r2, res) = b := by
    cases l₁₅ with
    | nil => simp [VerifierProgram.after] at h17; exact ⟨rfl, h17⟩
    | cons e es => cases e <;> simp [VerifierProgram.after] at h17
  obtain ⟨cf0, sf0, lf0l, ff0⟩ := foldRoundsT_run hf0
  obtain ⟨cf1, sf1, lf1l, ff1⟩ := foldRoundsT_run hf1
  obtain ⟨cf2, sf2, lf2l, ff2⟩ := foldRoundsT_run hf2
  have hr0 : r0.1.folds = r0.2 := by rw [ff0]; rfl
  have hl0 : r0.1.folds.length = 6 := by rw [hr0, lf0l]
  have hr1 : r1.1.folds = r0.1.folds ++ r1.2 := by rw [ff1, hfs1]
  have hl1 : r1.1.folds.length = 10 := by rw [hr1, List.length_append, hl0, lf1l]; rfl
  refine ⟨W₀, lm, ρ, lq, lf0, r0, 23 - r0.1.folds.length - 4 + 3, W₁, lm0, lf1, r1,
    23 - r1.1.folds.length - 4 + 4, W₂, lm1, lf2, r2, lres, res, by simp, rfl, h3,
    NoCommit.after_commits (nc_roundPoly _ _ _) h8, MovesOnly.after_samples (movesOnly_roundPoly _) h8,
    cf0, sf0, lf0l, hr0, hc0, ?_, cf1, sf1, lf1l, hr1, hc1, ?_, cf2, sf2, lf2l, by rw [ff2, hfs2],
    NoCommit.after_commits (nc_readScalars _) hres,
    MovesOnly.after_samples (movesOnly_readScalars _) hres⟩
  · rw [hs0, hl0]; rfl
  · rw [hs1, hl1]; rfl

/-- **The luck's readers on a split run** (and any events `T` after it): the words `W₀, W₁, W₂` and the fold
challenges `r0.2, r1.2, r2.2`. -/
theorem readersM_of_split {W₀ W₁ W₂ : Compile.Word} {lm lq lf0 lm0 lf1 lm1 lf2 T : List Ev} {ρ : E}
    {cl : List LeanVM.Protocol.Verifier.StackClaim} {r0 r1 r2 : WhirStateT × List E} {ht1 ht2 w1 w2 : ℕ}
    (hmid : (mid x).after lm = some (.ret cl))
    (hlq : commits lq = []) (hlqs : lq.filterMap sampleOf = [])
    (hf0 : commits lf0 = []) (hf0s : lf0.filterMap sampleOf = r0.2) (hl0 : r0.2.length = 6)
    (hm0 : commits lm0 = []) (hm0s : (lm0.filterMap sampleOf).length = 35)
    (hf1 : commits lf1 = []) (hf1s : lf1.filterMap sampleOf = r1.2) (hl1 : r1.2.length = 4)
    (hm1s : (lm1.filterMap sampleOf).length = 26)
    (hf2s : lf2.filterMap sampleOf = r2.2) (hl2 : r2.2.length = 4) {h : List Ev}
    (hh : h = Ev.commit 19 64 W₀ :: (lm ++ (Ev.sample ρ :: (lq ++ (lf0 ++ (Ev.commit ht1 w1 W₁ ::
        (lm0 ++ (lf1 ++ (Ev.commit ht2 w2 W₂ :: (lm1 ++ (lf2 ++ T))))))))))) :
    wdR (rd0M mid x) h = W₀ ∧ chalR (rd0M mid x) 1 LeanVM.Protocol.EndToEnd.laneBits h = r0.2 ∧
      wdR (rd1M mid x) h = W₁ ∧ chalR (rd1M mid x) 35 4 h = r1.2 ∧
      wdR (rd2M mid x) h = W₂ ∧ chalR (rd2M mid x) 26 4 h = r2.2 := by
  have hroot : (commitRootUd cfgMain24G).after [Ev.commit 19 64 W₀] = some (.ret ()) := by
    simp [commitRootUd, cfgMain24G, VerifierProgram.readCommitment, VerifierProgram.after]
  have h0 : rd0M mid x h = some (W₀, Ev.sample ρ :: (lq ++ (lf0 ++ (Ev.commit ht1 w1 W₁ ::
      (lm0 ++ (lf1 ++ (Ev.commit ht2 w2 W₂ :: (lm1 ++ (lf2 ++ T))))))))) := by
    unfold rd0M rootRd afterMidG
    rw [hh, show Ev.commit 19 64 W₀ :: (lm ++ (Ev.sample ρ :: (lq ++ (lf0 ++ (Ev.commit ht1 w1 W₁ ::
      (lm0 ++ (lf1 ++ (Ev.commit ht2 w2 W₂ :: (lm1 ++ (lf2 ++ T))))))))))
        = [Ev.commit 19 64 W₀] ++ (lm ++ (Ev.sample ρ :: (lq ++ (lf0 ++ (Ev.commit ht1 w1 W₁ ::
      (lm0 ++ (lf1 ++ (Ev.commit ht2 w2 W₂ :: (lm1 ++ (lf2 ++ T)))))))))) from rfl,
      retSplit_of_after _ _ _ hroot]
    dsimp only
    rw [retSplit_of_after _ _ _ hmid]
    rfl
  have h1 : rd1M mid x h = some (W₁, lm0 ++ (lf1 ++ (Ev.commit ht2 w2 W₂ :: (lm1 ++ (lf2 ++ T))))) := by
    unfold rd1M nextRd
    rw [h0, Option.bind_some]
    have := splitCommit_of_noCommit (Ev.sample ρ :: (lq ++ lf0)) (by
      simp only [commits, LeanVM.Protocol.Whir.Sound.commits_append, hlq, hf0]; rfl) ht1 w1 W₁
      (lm0 ++ (lf1 ++ (Ev.commit ht2 w2 W₂ :: (lm1 ++ (lf2 ++ T)))))
    simpa only [List.cons_append, List.append_assoc] using this
  have h2 : rd2M mid x h = some (W₂, lm1 ++ (lf2 ++ T)) := by
    unfold rd2M nextRd
    rw [h1, Option.bind_some]
    have := splitCommit_of_noCommit (lm0 ++ lf1) (by
      simp only [LeanVM.Protocol.Whir.Sound.commits_append, hm0, hf1]; rfl) ht2 w2 W₂ (lm1 ++ (lf2 ++ T))
    simpa only [List.cons_append, List.append_assoc] using this
  refine ⟨wdR_of_rd h0, ?_, wdR_of_rd h1, ?_, wdR_of_rd h2, ?_⟩
  · unfold chalR
    rw [h0]
    dsimp only
    simp only [List.filterMap_cons, sampleOf, List.filterMap_append, hlqs, hf0s, List.nil_append]
    rw [List.drop_one, List.tail_cons]
    exact List.take_left' hl0
  · unfold chalR
    rw [h1]
    dsimp only
    simp only [List.filterMap_append, hf1s]
    exact take_drop_appendM hm0s hl1
  · unfold chalR
    rw [h2]
    dsimp only
    simp only [List.filterMap_append, hf2s]
    exact take_drop_appendM hm1s hl2

end Split

end Lvm.ASM
