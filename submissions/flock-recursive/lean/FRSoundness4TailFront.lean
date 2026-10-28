-- New for `flock-recursive` (BLUEPRINT A.10; stage T4, S-G13 route C): a copy-port of
-- `FRSoundnessFront` Part A (reads and the frame) to revision 4.1's `seq4` (namespace `FR.Snd.T4`,
-- see `FRSoundness4TailStep`). Parts B–D (3.x's node layout, B′ cells) are not copied.
import FRSoundness4TailLig

/-!
# Reads and the frame at `seq4` (T4)

`FRSoundnessFront` Part A over T4's `Same`, `G.IsChain`, `fsRnd4`, `fsRanges4`, `phOf4` and
`p1Start` (`= 332`): **`Reads p P`**, its locality and stability (`Reads.append/ext1/ext`,
`Reads.stab`, `Reads.chain`), the single-squeeze and multi-squeeze frames **`card_frame`**,
**`esc_msD_frame`**, and **`frontLocal_of`**. They are the front's tools for its `FrontObl`
(P4a, P4b); this module exports them at revision 4.1.
-/

/-! # Port of `FRSoundnessFront` (its module doc describes the 3.x original) -/

namespace FR.Snd.T4
open RecursionFast FR.Merkle Finset
open scoped NNReal

set_option linter.constructorNameAsVariable false

/-! ## Part A: reads and the frame -/

/-- **`P` reads only what lies before position `p`** (entries and the words of earlier caps), on
chains of at least `p` entries. -/
def Reads (p : ℕ) (P : Log → Log → Prop) : Prop :=
  ∀ L es L' es', p ≤ es.length → p ≤ es'.length → Same L es L' es' p → (P L es ↔ P L' es')

variable {p : ℕ} {P Q : Log → Log → Prop}

theorem Reads.mono (h : Reads p P) {q : ℕ} (hq : p ≤ q) : Reads q P :=
  fun L es L' es' h1 h2 hS => h L es L' es' (by omega) (by omega) (hS.mono hq)

theorem Reads.or (hP : Reads p P) (hQ : Reads p Q) : Reads p fun L es => P L es ∨ Q L es :=
  fun L es L' es' h1 h2 hS => or_congr (hP L es L' es' h1 h2 hS) (hQ L es L' es' h1 h2 hS)

theorem Reads.and (hP : Reads p P) (hQ : Reads p Q) : Reads p fun L es => P L es ∧ Q L es :=
  fun L es L' es' h1 h2 hS => and_congr (hP L es L' es' h1 h2 hS) (hQ L es L' es' h1 h2 hS)

theorem Reads.not (hP : Reads p P) : Reads p fun L es => ¬ P L es :=
  fun L es L' es' h1 h2 hS => not_congr (hP L es L' es' h1 h2 hS)

theorem reads_false (p : ℕ) : Reads p fun _ _ => False := fun _ _ _ _ _ _ _ => Iff.rfl

/-- Locality: appending to a chain of at least `p` entries does not change `P`. -/
theorem Reads.append (h : Reads p P) (L es xs : Log) (hp : p ≤ es.length) :
    P L (es ++ xs) ↔ P L es :=
  h L _ L es (by simp; omega) hp ((same_append L es xs).mono hp)

theorem Reads.ext1 (h : Reads p P) (L es : Log) (a : Digest) (hp : p ≤ es.length) :
    P L (ext1 es a) ↔ P L es := h.append L es _ hp

theorem ext_eq_append (es : Log) : ∀ as : List Digest, ∃ ys, ext es as = es ++ ys := by
  intro as
  induction as using List.reverseRecOn with
  | nil => exact ⟨[], by simp [ext_nil]⟩
  | append_singleton as a ih =>
    obtain ⟨ys, hy⟩ := ih
    exact ⟨ys ++ [(squeezeQ (lastAns (ext es as)), a)], by rw [ext_append, ext1, hy]; simp⟩

theorem Reads.ext (h : Reads p P) (L es : Log) (as : List Digest) (hp : p ≤ es.length) :
    P L (ext es as) ↔ P L es := by
  obtain ⟨ys, hy⟩ := ext_eq_append es as
  rw [hy]; exact h.append L es ys hp

/-- Stability (`hstab`) on `hloc_of`'s extensions. -/
theorem Reads.stab (h : Reads p P) {L : Log} (hb : ¬ Bad L) {i : ℕ} (hci : G.IsChain L i) {X : Log}
    (hX : StabExt fsRnd4 (entriesOf L (pathOf L i)) X) (hp : p ≤ X.length) :
    P (L.take i) X ↔ P L X :=
  h _ X L X hp hp ((same_stabX hb hci hX).mono hp)

/-- Stability on the chain itself (`FrontChainStab`). -/
theorem Reads.chain (h : Reads p P) {L : Log} (hb : ¬ Bad L) {j : ℕ} (hci : G.IsChain L j)
    (hp : p ≤ (entriesOf L (pathOf L j)).length) :
    P (L.take j) (entriesOf L (pathOf L j)) ↔ P L (entriesOf L (pathOf L j)) :=
  h _ _ L _ hp hp ((same_chain hb hci).mono hp)

/-- A predicate of the level-0 word and the entries before `p` reads before `p` (`p > capPos 0`). -/
theorem reads_of_same {f : Log → Log → Prop}
    (h : ∀ L es L' es', Same L es L' es' p → (f L es ↔ f L' es')) : Reads p f :=
  fun L es L' es' _ _ hS => h L es L' es' hS

open Classical in
/-- **The frame at a single squeeze**: a background that reads before the squeeze never
escapes, so only the phase's own part counts. -/
theorem card_frame {Bg U U' : Log → Log → Prop} (hBg : Reads p Bg) (L es : Log)
    (hp : p ≤ es.length) :
    (univ.filter fun a => (Bg L es ∨ U L es) ∧ ¬ (Bg L (ext1 es a) ∨ U' L (ext1 es a))).card ≤
      (univ.filter fun a => U L es ∧ ¬ U' L (ext1 es a)).card := by
  refine card_le_card fun a ha => ?_
  simp only [mem_filter, mem_univ, true_and, not_or] at ha ⊢
  refine ⟨ha.1.resolve_left fun hb => ha.2.1 ((hBg.ext1 L es a hp).mpr hb), ha.2.2⟩

/-- **The frame in a multi-squeeze phase**: an escape of `msD (Bg ∨ U) (Bg ∨ U')` is an escape of
the phase's own part with the background false. -/
theorem esc_msD_frame {Dk : ℕ → Log → Log → Prop} {s0 r : ℕ} (hmem : (s0, r) ∈ fsRanges4)
    {Bg U U' : Log → Log → Prop} (hBg : Reads (s0 + 1) Bg)
    (hprev : Dk (phOf4 s0) = fun L es => Bg L es ∨ U L es)
    (hfin : Dk (phOf4 (s0 + 1)) = msD (Dk (phOf4 s0)) (fun L es => Bg L es ∨ U' L es) s0 r)
    {L es₀ : Log} (hl : es₀.length = s0 + 1) (as : List Digest) (has : as.length = r)
    (he : EscAtG (DPos (Dp Dk)) L (ext es₀ as)) :
    ¬ Bg L es₀ ∧ U L es₀ ∧ ¬ U' L (ext es₀ as) := by
  obtain ⟨hd, hnf⟩ := esc_msD hmem hfin hl as has he
  rw [hprev] at hd
  simp only [not_or] at hnf
  have hb : ¬ Bg L es₀ := fun hb => hnf.1 ((hBg.ext L es₀ as (by omega)).mpr hb)
  exact ⟨hb, hd.resolve_left hb, hnf.2⟩

/-- **`FrontLocal`** from congruence under `Same` up to P1.0's first absorb. -/
theorem frontLocal_of {W₀ : Log → Log → ℕ → K} {c₀ : Log → Log → K}
    (hW : ∀ L es L' es', Same L es L' es' (p1Start 0) → W₀ L es = W₀ L' es')
    (hc : ∀ L es L' es', Same L es L' es' (p1Start 0) → c₀ L es = c₀ L' es') :
    FrontLocal W₀ c₀ := fun L es L' es' _ hS hp =>
  ⟨hW L es L' es' (hS.mono hp), hc L es L' es' (hS.mono hp)⟩

/-! ## Controls (T4) -/

/-- **Control (negative)**: a predicate of the entry count does not read before position `0`
(`Same … 0` relates any two chains), so `Reads` is not vacuous. -/
theorem not_reads_length : ¬ Reads 0 fun _ es => es.length = 1 := fun h => by
  have := (h [] [(ByteArray.empty, 0)] [] [] (Nat.zero_le _) (Nat.zero_le _)
    ⟨fun _ h => absurd h (Nat.not_lt_zero _), fun _ _ _ h => absurd h (Nat.not_lt_zero _)⟩).mp rfl
  simp at this

end FR.Snd.T4

