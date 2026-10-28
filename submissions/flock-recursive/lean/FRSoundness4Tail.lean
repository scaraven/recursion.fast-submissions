-- New for `flock-recursive` (BLUEPRINT §5.1, §5.4, A.10; stage T4, S-G13 route C): a copy-port of
-- `FRSoundnessTail` to revision 4.1's item sequence `seq4` (namespace `FR.Snd.T4`, see `FRSoundness4TailStep`):
-- the declarations that read positions, chains or the kind are copied, the rest is imported.
import FRSoundness4TailFold

/-!
# The tail positions and `Same` at `seq4` (T4)

The 3.x declarations of `FRSoundnessTail` that read the positions, the chains or the kind, restated in
`FR.Snd.T4` over `fsItems4`/`phStart4`/`fsRnd4`, `G.Matches`/`G.IsChain` and `CKind`
(`kindOfC`, `CKind.lv`). Positions from P1.0 on are 3.x's plus 14 (`phStart4_shift`); the kind
enters through the ladder `lvOf κ.m` only. Changes beyond the renaming are marked `T4:`.
-/

/-! # Port of `FRSoundnessTail` (its module doc describes the 3.x original) -/

namespace FR.Snd.T4
open RecursionFast FR.Merkle Finset

set_option linter.constructorNameAsVariable false

/-! ## Part A: positions -/

/-- C.i's absorb (the next cap or the final message), P2.i's entry. -/
def cStart (i : ℕ) : ℕ := phStart4 (27 + 5 * i)

/-- P3.i's entry (P2.i's last answer). -/
def p3S0 (i : ℕ) : ℕ := phStart4 (30 + 5 * i) - 1

/-- Pf's first absorb. -/
def pfStart : ℕ := phStart4 51

/-- The first position after P3.i (P1.(i+1)'s first absorb, or Pf's). -/
def nxStart (i : ℕ) : ℕ := if i < 4 then p1Start (i + 1) else pfStart

theorem capPos_succ (i : ℕ) : capPos (i + 1) = cStart i := by
  simp only [capPos, cStart, Nat.add_one_ne_zero, ite_false]; congr 1; ring

theorem tail_pos_check : (List.range 5).all (fun i => decide (capPos i < p1Start i) &&
    decide (1 ≤ p1Start i) && decide (p1Start i + 2 * hEll i = cStart i) &&
    decide (cStart i + (lvlStar i).sq = p3S0 i) && decide (p3S0 i + 6 = nxStart i)) = true := by
  unfold nxStart p1Start pfStart cStart p3S0 capPos hEll phStart4; rw [fsStarts4_eq]; decide

theorem tail_pos {i : ℕ} (hi : i < 5) : capPos i < p1Start i ∧ 1 ≤ p1Start i ∧
    p1Start i + 2 * hEll i = cStart i ∧ cStart i + (lvlStar i).sq = p3S0 i ∧
      p3S0 i + 6 = nxStart i := by
  have h := tail_pos_check
  simp only [List.all_eq_true, List.mem_range, Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩ := h i hi
  exact ⟨h1, h2, h3, h4, h5⟩

theorem pfStart_eq : pfStart = 468 := by unfold pfStart phStart4; rw [fsStarts4_eq]; rfl

theorem p1Start_lt_nx {i : ℕ} (hi : i < 5) : p1Start i < nxStart i := by
  obtain ⟨-, -, h3, h4, h5⟩ := tail_pos hi; omega

theorem nxStart_le {i : ℕ} (hi : i + 1 < 5) : nxStart i = p1Start (i + 1) := by
  simp [nxStart, show i < 4 by omega]

/-! ## Part B: reads -/

/-- **The pairs `(L, es)` and `(L', es')` read the same before position `p`**: the chain entries,
and the level words whose caps lie before `p`. -/
def Same (L es L' es' : Log) (p : ℕ) : Prop :=
  Agree es es' p ∧ ∀ κ, ∀ i < 5, capPos i < p → wordK κ L es i = wordK κ L' es' i

variable {L es L' es' : Log} {p : ℕ}

theorem Same.mono (h : Same L es L' es' p) {q : ℕ} (hq : q ≤ p) : Same L es L' es' q :=
  ⟨h.1.mono hq, fun κ i hi hc => h.2 κ i hi (by omega)⟩

theorem same_of_agree (L : Log) (h : Agree es es' p) : Same L es L es' p :=
  ⟨h, fun κ i _ hc => by
    funext r j; simp only [wordK, wordOf, colOf_congr κ L i j (h.mono (by omega))]⟩

theorem same_append (L es : Log) (xs : Log) : Same L (es ++ xs) L es es.length :=
  same_of_agree L (agree_append es xs le_rfl)

theorem Same.kind (h : Same L es L' es' p) (hp : 1 ≤ p) : kindOfC es = kindOfC es' :=
  kindOfC_congr (h.1.mono hp)

/-- On a `StabExt` extension, the charging log and the whole log read the same. -/
theorem same_stabX (hb : ¬ Bad L) {n : ℕ} (hci : G.IsChain L n) {X : Log}
    (hX : StabExt fsRnd4 (entriesOf L (pathOf L n)) X) : Same (L.take n) X L X X.length :=
  ⟨fun _ _ => rfl, fun κ _ hi hc => wordK_stabX hb hci hX hi κ hc⟩

section Reads

variable (h : Same L es L' es' p) {i : ℕ} (hi : i < 5) (κ : CKind)
include h

theorem sAt_same {l : ℕ} (hp : p1Start i + 2 * l + 2 ≤ p) : sAt es i l = sAt es' i l :=
  sAt_congr (h.1.mono hp)

theorem sAt_same_lt (hp : cStart i ≤ p) (hi : i < 5) :
    ∀ v < hEll i, sAt es i v = sAt es' i v := fun v hv =>
  sAt_same h (by have := (tail_pos hi).2.2.1; omega)

include hi

theorem wordK_same (hp : capPos i < p) : wordK κ L es i = wordK κ L' es' i := h.2 κ i hi hp

theorem farL_same (hp : capPos i < p) : farL κ L es i ↔ farL κ L' es' i := by
  simp only [farL, wordK_same h hi κ hp]

theorem decodeL_same (hp : capPos i < p) : decodeL κ L es i = decodeL κ L' es' i :=
  decodeL_congr (wordK_same h hi κ hp)

theorem msgOf_same (hp : capPos i < p) : msgOf κ L es i = msgOf κ L' es' i := by
  funext r x; simp only [msgOf, decodeL_same h hi κ hp]

theorem fTab_same (hp : capPos i < p) : fTab κ L es i = fTab κ L' es' i := by
  funext y; simp only [fTab, msgOf_same h hi κ hp]

theorem foldAt_same (hp : cStart i ≤ p) : foldAt κ L es i = foldAt κ L' es' i := by
  have hc := (tail_pos hi).1
  have h3 := (tail_pos hi).2.2.1
  funext j
  simp only [foldAt, wordK_same h hi κ (by omega), lvl_ell κ hi,
    eqBits_congr (sAt_same_lt h hp hi)]

theorem foldMsg_same (hp : cStart i ≤ p) : foldMsg κ L es i = foldMsg κ L' es' i := by
  have hc := (tail_pos hi).1
  have h3 := (tail_pos hi).2.2.1
  funext x
  simp only [foldMsg, msgOf_same h hi κ (by omega), lvl_ell κ hi,
    eqBits_congr (sAt_same_lt h hp hi)]

theorem nextMsg_same (hp : cStart i + 1 ≤ p) : nextMsg κ L es i = nextMsg κ L' es' i := by
  funext x
  unfold nextMsg
  by_cases hn : i + 1 < nLevels
  · have := msgOf_same h hn κ (by rw [capPos_succ]; omega)
    simp only [hn, ite_true, this]
  · simp only [hn, ite_false, finalAt, msgAt, entAt]
    have h4 : i = 4 := by unfold nLevels at hn; omega
    subst h4
    have h46 : cStart 4 = phStart4 47 := rfl
    have := h.1 (phStart4 47) (by omega)
    simp only [entAt] at this
    rw [this]

theorem consSet_same (hp : cStart i + 1 ≤ p) : consSet κ L es i = consSet κ L' es' i := by
  simp only [consSet, foldAt_same h hi κ (by omega), nextMsg_same h hi κ hp]

theorem truthP2_same (hp : cStart i + 1 ≤ p) : truthP2 κ L es i ↔ truthP2 κ L' es' i := by
  simp only [truthP2, consSet_same h hi κ hp]

theorem truthC_same (hp : cStart i + 1 ≤ p) : truthC κ L es i ↔ truthC κ L' es' i := by
  simp only [truthC, foldMsg_same h hi κ (by omega), nextMsg_same h hi κ hp]

theorem qPos_same (hp : p3S0 i + 1 ≤ p) {q : ℕ} (hq : q < (CKind.lv κ i).t) :
    qPos κ es i q = qPos κ es' i q := by
  obtain ⟨hper, -, ht⟩ := p2_params κ i hi
  have h4 := (tail_pos hi).2.2.2.1
  have : q / (CKind.lv κ i).per < (lvlStar i).sq := (Nat.div_lt_iff_lt_mul hper).mpr (by omega)
  simp only [qPos, posAt, ansAt]
  rw [h.1 _ (by unfold cStart at h4; omega)]

theorem consErr_same (hp : p3S0 i + 1 ≤ p) {q : ℕ} (hq : q < (CKind.lv κ i).t) :
    consErr κ L es i q = consErr κ L' es' i q := by
  have h4 := (tail_pos hi).2.2.2.1
  simp only [consErr, foldAtN, qPos_same h hi κ hp hq, foldAt_same h hi κ (by omega),
    nextMsg_same h hi κ (by omega)]

theorem truthP3_same (hp : p3S0 i + 1 ≤ p) : truthP3 κ L es i ↔ truthP3 κ L' es' i :=
  forall₂_congr fun q hq => by rw [consErr_same h hi κ hp hq]

theorem kcAt_same (hp : nxStart i ≤ p) : ∀ v < 9, kcAt es i v = kcAt es' i v := by
  intro v hv
  have h5 := (tail_pos hi).2.2.2.2
  simp only [kcAt, coordAt, fAt, ansAt]
  rw [h.1 _ (by unfold p3S0 at h5; omega)]

theorem p3Batch_same (hp : nxStart i ≤ p) : p3Batch κ L es i = p3Batch κ L' es' i := by
  have h5 := (tail_pos hi).2.2.2.2
  refine sum_congr rfl fun q hq => ?_
  rw [eqBits_congr (kcAt_same h hi hp), consErr_same h hi κ (by omega) (mem_range.1 hq)]

theorem vNext_same (hp : nxStart i ≤ p) (c : K) : vNext κ L es i c = vNext κ L' es' i c := by
  have h5 := (tail_pos hi).2.2.2.2
  have h4 := (tail_pos hi).2.2.2.1
  unfold vNext
  exact congrArg (c + ·) (sum_congr rfl fun q hq => by
    rw [eqBits_congr (kcAt_same h hi hp), qPos_same h hi κ (by omega) (mem_range.1 hq),
      foldAtN, foldAtN, foldAt_same h hi κ (by omega)])

theorem wNext_same (hp : nxStart i ≤ p) (Wf : ℕ → K) : wNext κ es i Wf = wNext κ es' i Wf := by
  have h5 := (tail_pos hi).2.2.2.2
  funext x
  unfold wNext
  exact congrArg (Wf x + ·) (sum_congr rfl fun q hq => by
    rw [eqBits_congr (kcAt_same h hi hp), qPos_same h hi κ (by omega) (mem_range.1 hq)])

theorem foldW_same (hp : cStart i ≤ p) (W : ℕ → K) :
    foldW (CKind.lv κ i).ell (sAt es i) W = foldW (CKind.lv κ i).ell (sAt es' i) W := by
  funext x; simp only [foldW, lvl_ell κ hi, eqBits_congr (sAt_same_lt h hp hi)]

theorem nextW_same (hp : nxStart i ≤ p) (W : ℕ → K) : nextW κ es i W = nextW κ es' i W := by
  obtain ⟨-, -, -, h4, h5⟩ := tail_pos hi
  rw [nextW, nextW, foldW_same h hi κ (by omega), wNext_same h hi κ hp]

end Reads

/-! ## Part C: the level chain -/

/-- P1.i's variables: the `ℓᵢ` row bits (the rounds), then level `i`'s message bits. -/
def nrP (i : ℕ) (κ : CKind) : ℕ := (CKind.lv κ i).ell + mLog κ i

end FR.Snd.T4

