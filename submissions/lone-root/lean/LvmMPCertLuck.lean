-- New for lvm2 roll 11 (M′, R11-C): the extractor's luck at M′ (one commitment, `C_main` at `cfgMain23Jq 1`),
-- over the lists of its three levels (14 fold rounds). Adapted from `LvmCertSLuck`/`LvmCertSLuckJ` (`afterMid`,
-- `foldChal`, `rec1Of`, `foldChal1J`, `LuckB0J`, `LuckB1J`, `esc_luckJ_le`), generic in the reader.
import LvmCertSLuck
import LvmCertSJ
import LvmWhirParamsJ23

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
          List.take_of_length_le (by simp; omega), List.take_of_length_le (by simp; omega)]
      · have hg : ¬ GrowsR rd d k h := by
          rintro ⟨_, _, h', -, h3⟩; rw [hr] at h'; cases h'; exact h2 h3
        rw [if_neg hg, List.drop_append_of_le_length h1,
          List.take_append_of_le_length (by simp; omega)]
    · have hg : ¬ GrowsR rd d k h := by
        rintro ⟨_, _, h', h3, -⟩; rw [hr] at h'; cases h'; exact h1 h3
      rw [if_neg hg, List.drop_eq_nil_of_le (by simp; omega),
        List.drop_eq_nil_of_le (by omega)]

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
  omega

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
    refine ⟨k1 + k2, fun c ↦ by have := f1 c; have := f2 c; omega, fun {_} ↦ ?_⟩
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
        omega
    have hK : (Fintype.card E : ℝ≥0∞)⁻¹ * bad.card ≤ (k0 : ℝ≥0∞) * δ := by
      calc (Fintype.card E : ℝ≥0∞)⁻¹ * bad.card
          ≤ (Fintype.card E : ℝ≥0∞)⁻¹ * ((k0 * M : ℕ) : ℝ≥0∞) := by gcongr
        _ = (k0 : ℝ≥0∞) * δ := by simp only [δ, ENNReal.div_eq_inv_mul]; push_cast; ring
    have hk0 : k0 ≤ φ h := by have := hf (0 : E); omega
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
      omega
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
  exact_mod_cast (show φM mid x h ≤ 14 by unfold φM; simp only [LeanVM.Protocol.EndToEnd.laneBits] at *; omega)

end MLemmas

end Lvm.ASM
