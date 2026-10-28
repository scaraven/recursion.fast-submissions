-- New for `flock-recursive` (BLUEPRINT §5.1, §5.4, A.10; stage T4, S-G13 route C): a copy-port of
-- `FRSoundnessTailD` to revision 4.1's item sequence `seq4` (namespace `FR.Snd.T4`, see `FRSoundness4TailStep`):
-- the declarations that read positions, chains or the kind are copied, the rest is imported.
import FRSoundness4Tail

/-!
# The tail dooms at `seq4` (T4)

The 3.x declarations of `FRSoundnessTailD` that read the positions, the chains or the kind, restated in
`FR.Snd.T4` over `fsItems4`/`phStart4`/`fsRnd4`, `G.Matches`/`G.IsChain` and `CKind`
(`kindOfC`, `CKind.lv`). Positions from P1.0 on are 3.x's plus 14 (`phStart4_shift`); the kind
enters through the ladder `lvOf κ.m` only. Changes beyond the renaming are marked `T4:`.
-/

/-! # Port of `FRSoundnessTailD` (its module doc describes the 3.x original) -/

namespace FR.Snd.T4
open RecursionFast FR.Merkle Finset

set_option linter.constructorNameAsVariable false

/-- **What the front hands the tail** reads only what lies before P1.0. -/
def FrontLocal (W₀ : Log → Log → ℕ → K) (c₀ : Log → Log → K) : Prop :=
  ∀ L es L' es' p, Same L es L' es' p → p1Start 0 ≤ p → W₀ L es = W₀ L' es' ∧ c₀ L es = c₀ L' es'

/-! ## Part A: the level chain -/

section Chain

variable (W₀ : Log → Log → ℕ → K) (c₀ : Log → Log → K)

/-- Level `i`'s weight table. -/
noncomputable def lvW : ℕ → Log → Log → ℕ → K
  | 0 => W₀
  | i + 1 => fun L es => nextW (kindOfC es) es i (lvW i L es)

/-- Level `i`'s initial claim (P1.i's; `lvC 5` is Pf's: P1.4's final claim, as `finP 4` asserts). -/
noncomputable def lvC : ℕ → Log → Log → K
  | 0 => c₀
  | i + 1 => fun L es =>
    if i < 4 then vNext (kindOfC es) L es i (clR2 (p1Start i) 32 readK chK (lvC i) L es (hEll i))
    else clR2 (p1Start i) 32 readK chK (lvC i) L es (hEll i)

/-- P1.i's final claim (after its `ℓᵢ` rounds). -/
noncomputable def c1 (i : ℕ) (L es : Log) : K :=
  clR2 (p1Start i) 32 readK chK (lvC c₀ i) L es (hEll i)

/-- P1.i's tables `[Wᵢ, f⁽ⁱ⁾]` over `ℓᵢ + mLog` variables. -/
noncomputable def lvT (i : ℕ) (L es : Log) : Array (Array K) :=
  tabs (lvW W₀ i L es) (fTab (kindOfC es) L es i) (nrP i (kindOfC es))

/-- Level `i`'s table bound at P1.i's challenges. -/
noncomputable def wFold (i : ℕ) (L es : Log) : ℕ → K :=
  foldW (CKind.lv (kindOfC es) i).ell (sAt es i) (lvW W₀ i L es)

/-- The folded claim's truth `⟨foldW Wᵢ, fold_z(f⁽ⁱ⁾)⟩`. -/
noncomputable def foldSum (i : ℕ) (L es : Log) : K :=
  ∑ x ∈ range (2 ^ mLog (kindOfC es) i), wFold W₀ i L es x * foldMsg (kindOfC es) L es i x

/-- Pf's weight: level 4's folded table, zero past its `2^mLog` message (`P30`/`N30`: `2^5`). -/
noncomputable def wPf (L es : Log) (x : ℕ) : K :=
  if x < 2 ^ mLog (kindOfC es) 4 then wFold W₀ 4 L es x else 0

/-- Pf's tables `[W_f, final]` over 7 variables. -/
noncomputable def tPf (L es : Log) : Array (Array K) := tabs (wPf W₀ L es) (finalAt es) 7

/-- Level `i`'s start (`pfStart` for `i = 5`). -/
def lvB (i : ℕ) : ℕ := if i < 5 then p1Start i else pfStart

theorem lvB_succ {i : ℕ} (hi : i < 5) : lvB (i + 1) = nxStart i := by
  unfold lvB nxStart; split_ifs <;> omega

theorem lvB_lt {i : ℕ} (hi : i < 5) : lvB i < lvB (i + 1) := by
  rw [lvB_succ hi]; simp only [lvB, hi, ite_true]; exact p1Start_lt_nx hi

variable {W₀ c₀}

/-- **The level chain reads only what lies before the level's start.** -/
theorem chain_same (hF : FrontLocal W₀ c₀) : ∀ i ≤ 5, ∀ {L es L' es' : Log} {p : ℕ},
    Same L es L' es' p → lvB i ≤ p →
      lvW W₀ i L es = lvW W₀ i L' es' ∧ lvC c₀ i L es = lvC c₀ i L' es'
  | 0, _, _, _, _, _, _, h, hp => hF _ _ _ _ _ h hp
  | i + 1, hi, L, es, L', es', p, h, hp => by
    have hi' : i < 5 := by omega
    have hlt := lvB_lt hi'
    obtain ⟨hW, hC⟩ := chain_same hF i (by omega) h (by omega)
    have hb : lvB i = p1Start i := by simp [lvB, hi']
    have h1 : 1 ≤ p := by have := (tail_pos hi').2.1; omega
    have hk := h.kind h1
    have hnx : nxStart i ≤ p := lvB_succ hi' ▸ hp
    obtain ⟨-, -, h3, h4, h5⟩ := tail_pos hi'
    refine ⟨?_, ?_⟩
    · show nextW (kindOfC es) es i (lvW W₀ i L es) = nextW (kindOfC es') es' i (lvW W₀ i L' es')
      rw [hW, hk, nextW_same h hi' _ hnx]
    · show (if i < 4 then vNext (kindOfC es) L es i
            (clR2 (p1Start i) 32 readK chK (lvC c₀ i) L es (hEll i))
          else clR2 (p1Start i) 32 readK chK (lvC c₀ i) L es (hEll i)) =
        (if i < 4 then vNext (kindOfC es') L' es' i
            (clR2 (p1Start i) 32 readK chK (lvC c₀ i) L' es' (hEll i))
          else clR2 (p1Start i) 32 readK chK (lvC c₀ i) L' es' (hEll i))
      rw [clR2_same hC (h.1.mono (by omega)), hk, vNext_same h hi' _ hnx]

variable (hF : FrontLocal W₀ c₀) {L es L' es' : Log} {p : ℕ} (h : Same L es L' es' p) {i : ℕ}
  (hi : i < 5)
include hF h hi

theorem lvW_same (hp : p1Start i ≤ p) : lvW W₀ i L es = lvW W₀ i L' es' :=
  (chain_same hF i (by omega) h (by simp [lvB, hi]; exact hp)).1

theorem lvC_same (hp : p1Start i ≤ p) : lvC c₀ i L es = lvC c₀ i L' es' :=
  (chain_same hF i (by omega) h (by simp [lvB, hi]; exact hp)).2

theorem c1_same (hp : cStart i ≤ p) : c1 c₀ i L es = c1 c₀ i L' es' := by
  obtain ⟨-, -, h3, -, -⟩ := tail_pos hi
  exact clR2_same (lvC_same hF h hi (by omega)) (h.1.mono (by omega))

theorem lvT_same (hp : p1Start i ≤ p) : lvT W₀ i L es = lvT W₀ i L' es' := by
  obtain ⟨hc, h1, -, -, -⟩ := tail_pos hi
  rw [lvT, lvT, lvW_same hF h hi hp, h.kind (by omega), fTab_same h hi _ (by omega)]

theorem wFold_same (hp : cStart i ≤ p) : wFold W₀ i L es = wFold W₀ i L' es' := by
  obtain ⟨-, h1, h3, -, -⟩ := tail_pos hi
  rw [wFold, wFold, lvW_same hF h hi (by omega), h.kind (by omega), foldW_same h hi _ hp]

theorem foldSum_same (hp : cStart i ≤ p) : foldSum W₀ i L es = foldSum W₀ i L' es' := by
  obtain ⟨-, h1, h3, -, -⟩ := tail_pos hi
  rw [foldSum, foldSum, wFold_same hF h hi hp, h.kind (by omega),
    foldMsg_same h hi _ hp]

end Chain

section ChainPf

variable {W₀ : Log → Log → ℕ → K} {c₀ : Log → Log → K} (hF : FrontLocal W₀ c₀)
  {L es L' es' : Log} {p : ℕ} (h : Same L es L' es' p)
include hF h

theorem tPf_same (hp : pfStart ≤ p) : tPf W₀ L es = tPf W₀ L' es' := by
  have h5 := (tail_pos (show 4 < 5 by norm_num)).2.2.2.2
  have h4 := (tail_pos (show 4 < 5 by norm_num)).2.2.2.1
  have hnx : nxStart 4 = pfStart := rfl
  have h1 : 1 ≤ p := by have := (tail_pos (show 4 < 5 by norm_num)).2.1; omega
  have hk := h.kind h1
  have hw : wPf W₀ L es = wPf W₀ L' es' := by
    funext x
    simp only [wPf, hk, wFold_same hF h (show 4 < 5 by norm_num) (by omega)]
  have hf : finalAt es = finalAt es' := by
    funext x
    have h46 : cStart 4 = phStart4 47 := rfl
    simp only [finalAt, msgAt, entAt]
    have := h.1 (phStart4 47) (by omega)
    simp only [entAt] at this
    rw [this]
  rw [tPf, tPf, hw, hf]

theorem lvC5_same (hp : pfStart ≤ p) : lvC c₀ 5 L es = lvC c₀ 5 L' es' :=
  (chain_same hF 5 le_rfl h (by simpa [lvB] using hp)).2

end ChainPf

/-- Below level 4, level `i + 1`'s initial claim is P3.i's batched claim. -/
theorem lvC_succ (c₀ : Log → Log → K) {i : ℕ} (hi : i < 4) (L es : Log) :
    lvC c₀ (i + 1) L es = vNext (kindOfC es) L es i (c1 c₀ i L es) := by
  show (if i < 4 then vNext (kindOfC es) L es i (c1 c₀ i L es) else c1 c₀ i L es) = _
  exact ite_pos' hi _ _

/-- **Pf's initial claim is P1.4's final claim** (`finP 4`: `claim0 Pf = claimN P1.4`). -/
theorem lvC_five (c₀ : Log → Log → K) (L es : Log) : lvC c₀ 5 L es = c1 c₀ 4 L es := by
  show (if 4 < 4 then vNext (kindOfC es) L es 4 (c1 c₀ 4 L es) else c1 c₀ 4 L es) = _
  exact ite_neg' (by norm_num) _ _

theorem mLog4_le (κ : CKind) : mLog κ 4 ≤ 7 := by rcases κ with (_|_|_) | (_|_|_) <;> decide

/-! ## Part B: the dooms -/

section Dooms

variable (W₀ : Log → Log → ℕ → K) (c₀ : Log → Log → K)

/-- **P1.i's doom** (A.10): the fold so far is far, or the word is close and the asserted rounds'
running claim is false (`D2` over K, the check in `RejT`). -/
def D1 (i : ℕ) (L es : Log) : Prop :=
  ¬ closeP (kindOfC es) L es i (hRnd es i) ∨
    (¬ farL (kindOfC es) L es i ∧
      D2 (p1Start i) 32 readK chK (lvC c₀ i) (nrP i) e2 (lvT W₀ i) L es)

/-- **C.i's doom**: the next codeword is not close to the fold (`¬ truthP2`), or the word is close
and the folded claim is false. -/
def DCi (i : ℕ) (L es : Log) : Prop :=
  ¬ truthP2 (kindOfC es) L es i ∨
    (¬ farL (kindOfC es) L es i ∧ c1 c₀ i L es ≠ foldSum W₀ i L es)

/-- P2.i's final doom: a queried fold is inconsistent, or the word is close, the next message is
the fold and the folded claim is false. -/
def finP2 (i : ℕ) (L es : Log) : Prop :=
  ¬ truthP3 (kindOfC es) L es i ∨
    (¬ farL (kindOfC es) L es i ∧ truthC (kindOfC es) L es i ∧ c1 c₀ i L es ≠ foldSum W₀ i L es)

/-- **P2.i's doom** (`msD` over C.i's). -/
def DP2 (i : ℕ) : Log → Log → Prop :=
  msD (DCi W₀ c₀ i) (finP2 W₀ c₀ i) (cStart i) (lvlStar i).sq

/-- The next level's true claim (`⟨W_{i+1}, f⁽ⁱ⁺¹⁾⟩`; Pf's `⟨W_f, final⟩` for `i = 4`). -/
noncomputable def nxSum (i : ℕ) (L es : Log) : K :=
  if i < 4 then
    ∑ y ∈ range (2 ^ nrP (i + 1) (kindOfC es)), lvW W₀ (i + 1) L es y * fTab (kindOfC es) L es (i + 1) y
  else ∑ x ∈ range (2 ^ 7), wPf W₀ L es x * finalAt es x

/-- P3.i's final doom: the next level is far, or its initial claim is false (`i < 4`); P2.4's
final doom (`i = 4`: `finP 4` does not batch, so `κ_c⁽⁴⁾` changes nothing). -/
def finP3 (i : ℕ) (L es : Log) : Prop :=
  if i < 4 then farL (kindOfC es) L es (i + 1) ∨ lvC c₀ (i + 1) L es ≠ nxSum W₀ i L es
  else finP2 W₀ c₀ i L es

/-- **P3.i's doom** (`msD` over P2.i's). -/
def DP3 (i : ℕ) : Log → Log → Prop := msD (DP2 W₀ c₀ i) (finP3 W₀ c₀ i) (p3S0 i) 5

/-- **Pf's doom**: a queried level-4 fold is not the final codeword's symbol (`finP 4`'s direct
check fails), or `D2` over K, 7 rounds, from P1.4's final claim. -/
def DPf (L es : Log) : Prop :=
  ¬ truthP3 (kindOfC es) L es 4 ∨
    D2 pfStart 32 readK chK (lvC c₀ 5) (fun _ => 7) e2 (tPf W₀) L es

/-- **The tail's phase dooms** (`k = 26 + 5i + t`: P1.i, C.i, P2.i, Q, P3.i; `k = 51`: Pf). -/
def DT (k : ℕ) : Log → Log → Prop :=
  if k = 51 then DPf W₀ c₀
  else if (k - 26) % 5 = 0 then D1 W₀ c₀ ((k - 26) / 5)
  else if (k - 26) % 5 = 1 then DCi W₀ c₀ ((k - 26) / 5)
  else if (k - 26) % 5 = 2 then DP2 W₀ c₀ ((k - 26) / 5)
  else if (k - 26) % 5 = 3 then fun _ _ => False
  else DP3 W₀ c₀ ((k - 26) / 5)

variable {i : ℕ} (hi : i < 5)
include hi

theorem DT_P1 : DT W₀ c₀ (26 + 5 * i) = D1 W₀ c₀ i := by
  unfold DT
  rw [ite_neg' (by omega), ite_pos' (by omega), show (26 + 5 * i - 26) / 5 = i by omega]

theorem DT_C : DT W₀ c₀ (27 + 5 * i) = DCi W₀ c₀ i := by
  unfold DT
  rw [ite_neg' (by omega), ite_neg' (by omega), ite_pos' (by omega),
    show (27 + 5 * i - 26) / 5 = i by omega]

theorem DT_P2 : DT W₀ c₀ (28 + 5 * i) = DP2 W₀ c₀ i := by
  unfold DT
  rw [ite_neg' (by omega), ite_neg' (by omega), ite_neg' (by omega), ite_pos' (by omega),
    show (28 + 5 * i - 26) / 5 = i by omega]

theorem DT_P3 : DT W₀ c₀ (30 + 5 * i) = DP3 W₀ c₀ i := by
  unfold DT
  rw [ite_neg' (by omega), ite_neg' (by omega), ite_neg' (by omega), ite_neg' (by omega),
    ite_neg' (by omega), show (30 + 5 * i - 26) / 5 = i by omega]

omit hi in
theorem DT_Pf : DT W₀ c₀ 51 = DPf W₀ c₀ := by unfold DT; rw [ite_pos' rfl]

end Dooms

/-! ## Part C: the asserted checks -/

/-- **The tail's asserted round checks**: some answered round of P1.i or Pf fails
`g(0) + g(1) = claim`. -/
def RejT (c₀ : Log → Log → K) (L es : Log) : Prop :=
  (∃ i < 5, ∃ j < hEll i, p1Start i + 2 * j < es.length ∧
    ¬ Chk2 (p1Start i) 32 readK chK (lvC c₀ i) L es j) ∨
  (∃ j < 7, pfStart + 2 * j < es.length ∧ ¬ Chk2 pfStart 32 readK chK (lvC c₀ 5) L es j)

theorem chk2_same {b : ℕ} {c0 : Log → Log → K} {L L' es es' : Log} {p : ℕ}
    (h : Same L es L' es' p) {j : ℕ} (hj : b + 2 * j < p) (hc : c0 L es = c0 L' es') :
    Chk2 b 32 readK chK c0 L es j ↔ Chk2 b 32 readK chK c0 L' es' j := by
  have hg : g2At b 32 readK es j = g2At b 32 readK es' j := by
    simp only [g2At, msgAt, h.1 (b + 2 * j) hj]
  simp only [Chk2, hg, clR2_same hc (h.1.mono (by omega) : Agree es es' (b + 2 * j))]

/-! ## Part D: the position facts -/

/-- Checked: phase `phOf4 p`'s first position is at most `p`, and `p` lies before the next phase's
(`p < 482`). -/
theorem phOf_check : (List.range 482).all (fun p => decide (phStart4 (phOf4 p) ≤ p) &&
    decide (phOf4 p ≤ 51) && (decide (phOf4 p = 51) || decide (p < phStart4 (phOf4 p + 1)))) = true := by
  unfold phOf4 phStart4; rw [fsStarts4_eq]; decide +kernel

theorem phOf_ge {p : ℕ} (hp : 468 ≤ p) : phOf4 p = 51 := by
  unfold phOf4
  rw [List.filter_eq_self.mpr fun x hx => by
    rw [fsStarts4_eq] at hx; simp only [decide_eq_true_eq]; fin_cases hx <;> omega, fsStarts4_eq]
  rfl

/-- **The phase bounds**: `phStart4 (phOf4 p) ≤ p`, and before the last phase `p` lies before the
next phase's start. -/
theorem phOf_bounds (p : ℕ) : phStart4 (phOf4 p) ≤ p ∧ phOf4 p ≤ 51 ∧
    (phOf4 p < 51 → p < phStart4 (phOf4 p + 1)) := by
  by_cases hp : p < 482
  · have h := phOf_check
    simp only [List.all_eq_true, List.mem_range, Bool.and_eq_true, Bool.or_eq_true,
      decide_eq_true_eq] at h
    obtain ⟨⟨h1, h2⟩, h3⟩ := h p hp
    exact ⟨h1, h2, fun hl => h3.resolve_left (by omega)⟩
  · rw [phOf_ge (by omega)]
    refine ⟨?_, le_rfl, fun h => absurd h (lt_irrefl _)⟩
    unfold phStart4; rw [fsStarts4_eq]; simp; omega

/-- Checked: the rounds of P1.0 … P1.4 and Pf alternate a 96-byte absorb and a squeeze; there
are 482 Fiat–Shamir items. -/
theorem rounds_check : ((List.range 5).all (fun i => (List.range (hEll i)).all fun l =>
      fsItems4[p1Start i + 2 * l]? == some (.absorb 96) &&
        fsItems4[p1Start i + 2 * l + 1]? == some .squeeze) &&
    (List.range 7).all (fun l => fsItems4[pfStart + 2 * l]? == some (.absorb 96) &&
        fsItems4[pfStart + 2 * l + 1]? == some .squeeze) && fsItems4.length == 482) = true := by
  unfold p1Start pfStart hEll phStart4; rw [fsStarts4_eq]; decide +kernel

end FR.Snd.T4

