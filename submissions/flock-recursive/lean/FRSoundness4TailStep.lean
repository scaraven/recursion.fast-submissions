-- New for `flock-recursive` (BLUEPRINT §5.1, A.10; stage T4, S-G13 route C): the Ligerito tail's
-- step infrastructure at revision 4.1's item sequence `seq4`. A copy-port of `FRSoundnessStepA`
-- (the committed words), `FRSoundnessStepB`, `FRSoundnessStepC` and `FRSoundnessStepE` into
-- `FR.Snd.T4`: only the declarations that read the positions, the chains or the kind are copied;
-- the position-free algebra is imported. Proof text unchanged except where noted (`T4:`).
import FRSoundnessCoreTail
import FRSoundnessCoreSG
import FRSoundness4Pos

/-!
# The tail's step infrastructure at `seq4` (T4)

The 3.x declarations of `FRSoundnessStepA/B/C/E` that read `fsItems`, `phStart`, `fsRanges`,
`fsRnd`, the chains (`Matches`, `IsChain`, `muG`) or the kind (`Kind`, `kindOf`, `lvl`), restated in
namespace `FR.Snd.T4` with the same names over S-G13's revision 4.1 data: `fsItems4`, `phStart4`,
`fsRanges4`, `fsRnd4`, `phOf4`, the generic chains `G.Matches`/`G.IsChain`/`G.muG` at `fsSeq4`, and
the six-kind `CKind` (`kindOfC`, ladder `CKind.lv κ i = lvOf κ.m i`). Inside `FR.Snd.T4` a copied
name shadows its 3.x original; every other name is 3.x's position-free declaration.
The front's rounds phases (`z3_*`, `lr2_phase`, `e2_phase`) are P4's and are not copied.
-/

/-! # Port of `FRSoundnessStepA` (its module doc describes the 3.x original) -/

namespace FR.Snd.T4
open RecursionFast FR.Merkle

/-! ## (1) Readers -/

/-! ## Phase starts (A.4) -/

/-! ## (2) The committed words -/

/-- The position of level `i`'s cap absorb: `cap₀` (phase 2), else `C.(i − 1)` (phase `22 + 5i`). -/
def capPos (i : ℕ) : ℕ := if i = 0 then phStart4 2 else phStart4 (22 + 5 * i)

theorem capPos_eq : (List.range 5).map capPos = [2, 344, 383, 410, 434] := by
  unfold capPos phStart4; rw [fsStarts4_eq]; rfl

/-- Cap entry `c` of level `i`: the 32 bytes at offset `32c` of the cap's message (A.2). -/
def capDig (es : Log) (i c : ℕ) : Digest := bytesAt (msgAt es (capPos i)) (32 * c) 32

/-- **The column of level `i` at position `p`** for kind `k`, read off `L` top-down from its cap
entry (`p / 2^sib`) along the bits of `p` (`colL (frEnc i)`, height `sib = log₂ n − cap`). -/
def colOf (k : CKind) (L es : Log) (i p : ℕ) : Option ByteArray :=
  colL (frEnc i) L (capDig es i (p / 2 ^ (CKind.lv k i).sib)) (CKind.lv k i).sib p

/-- **The committed word of level `i`**: row `r` at position `p` is the column's F element `r`
(16 bytes each, row 0 first, A.2); `0` where `L` reads no column. -/
def wordOf (k : CKind) (L es : Log) (i : ℕ) : Fin (CKind.lv k i).rows → Fin (2 ^ (CKind.lv k i).logN) → F :=
  fun r p => ((colOf k L es i p).map fun col => readF col (16 * r)).getD 0

/-- **Far**: the word (in K) is not jointly `e`-close to `C`: no agreement set makes it
`JointClose` (BLUEPRINT §5.4). The decoded rows of a close word are `JointClose`'s witness. -/
def FarAt (k : CKind) (C : Submodule K (Fin (2 ^ (CKind.lv k 0).logN) → K)) (e : ℕ) (L es : Log) :
    Prop :=
  ∀ A, ¬ JointClose C e (fun r p => algebraMap F K (wordOf k L es 0 r p)) A

/-- The column depends on the entries up to the cap's absorb only. -/
theorem colOf_congr (k : CKind) (L : Log) {es es' : Log} (i p : ℕ)
    (h : Agree es es' (capPos i + 1)) : colOf k L es i p = colOf k L es' i p := by
  simp only [colOf, capDig, msgAt, h (capPos i) (by omega)]

/-! ## Controls -/

/-- Control: on the empty log no column is read, so the word is `0`. -/
theorem wordOf_nil (k : CKind) (es : Log) (i : ℕ) : wordOf k [] es i = 0 := by
  funext r p
  have : colOf k [] es i p = none := by
    unfold colOf
    cases h : (CKind.lv k i).sib <;> simp [colL, pre]
  simp [wordOf, this]

end FR.Snd.T4

/-! # Port of `FRSoundnessStepB` (its module doc describes the 3.x original) -/

namespace FR.Snd.T4
open RecursionFast FR.Merkle Finset
open scoped NNReal

/-! ## Part A: the error `εR` and the obligations -/

open Classical in
/-- **The five per-position obligations of `hloc_of`** for a doom predicate `D`, the phase map
`rnd`, the multi-squeeze budget `δ` and the single-squeeze count `N`. -/
structure StepObl (D : Log → Log → Prop) (rnd : ℕ → Option (ℕ × ℕ)) (δ : ℝ≥0) (N : ℕ) :
    Prop where
  habs : ∀ L es x len, G.Matches (es ++ [x]) → fsItems4[es.length]? = some (.absorb len) →
    D L es → D L (es ++ [x])
  hmid : ∀ L es x s0 r, G.Matches (es ++ [x]) → rnd es.length = some (s0, r) →
    es.length < s0 + r → (D L (es ++ [x]) ↔ D L es)
  hsingle : ∀ L es, G.Matches es → fsItems4[es.length]? = some .squeeze → rnd es.length = none →
    (Finset.univ.filter fun a => D L es ∧ ¬ D L (ext1 es a)).card ≤ N
  hround : ∀ L es₀ s0 r, G.Matches es₀ → es₀.length = s0 + 1 →
    rnd (s0 + 1) = some (s0, r) → condCount D L es₀ r [] ≤ δ
  hstab : ∀ L i, ¬ Bad L → G.IsChain L i → ∀ X, StabExt rnd (entriesOf L (pathOf L i)) X →
    (D (L.take i) X ↔ D L X)

open Classical in
/-- **`step_epsD`**: the library's `KState.step` law with error `εD = εR − ε_H` for the potential
`muG D (pRoundG D fsRnd4)`, from the obligations at `δ = deltaR` and `N ≤ 2^256·deltaR`. -/
theorem step_epsD {D : Log → Log → Prop} {N : ℕ} (hN : (N : ℝ≥0) ≤ 2 ^ 256 * deltaR)
    (ob : StepObl D fsRnd4 deltaR N) (L : Log) (q : ByteArray) (hl : L.length < logCap)
    (hμ : G.muG D (pRoundG D fsRnd4) L < 1) (hq : q ∉ L.map Prod.fst) :
    ∑ a : Digest, G.muG D (pRoundG D fsRnd4) (L ++ [(q, a)]) ≤
      (G.muG D (pRoundG D fsRnd4) L + epsD) * 2 ^ 256 :=
  (G.muG_step_of fsRnd4_ok fsRnd4_zero deltaR N hN ob.habs ob.hmid ob.hsingle ob.hround ob.hstab hl
    hμ hq).trans (by gcongr; exact err_le_epsD)

/-! ## Part B: the degree-3 F rounds -/

section Rounds3

variable (b : ℕ)

variable (c0 : Log → Log → F)

variable (nr : CKind → ℕ)

/-- The rounds answered by the entries `es`: `min (nr (kindOfC es)) ⌊(|es| − b)/2⌋`. -/
def ans3 (es : Log) : ℕ := min (nr (kindOfC es)) ((es.length - b) / 2)

variable (e : Expr) (T : Log → Log → Array (Array F))

/-- The claim after `l` rounds is not the true sum of the tables bound at the first `l`
challenges. -/
def Wrong3 (L es : Log) (l : ℕ) : Prop :=
  clR b c0 L es l ≠ trueSum e (bindAll (T L es) (rchs b es l)) (nr (kindOfC es) - l)

/-- **The round doom** (§5.2 row Z3): past the phase's first absorb, the running claim after the
answered rounds is false. -/
def D3 (L es : Log) : Prop := b < es.length ∧ Wrong3 b c0 nr e T L es (ans3 b nr es)

variable {b c0 nr e T}

theorem wrong3_congr (hb1 : 1 ≤ b) (hTc : TruthLocal b c0 T) {L es es' : Log} {l : ℕ}
    (h : Agree es es' (b + 2 * l)) : Wrong3 b c0 nr e T L es l ↔ Wrong3 b c0 nr e T L es' l := by
  have hb := h.mono (show b ≤ b + 2 * l by omega)
  obtain ⟨hT, hc⟩ := hTc L es es' hb
  simp only [Wrong3, clR_congr hc h, rchs_congr h, hT, kindOfC_congr (hb.mono hb1)]

theorem kindOf_append {es : Log} (x : ByteArray × Digest) (h : 0 < es.length) :
    kindOfC (es ++ [x]) = kindOfC es :=
  kindOfC_congr (agree_append es [x] h)

/-- When the next position is not a real round's squeeze, appending keeps the answered rounds and
the doom. -/
theorem D3_append_iff (hb1 : 1 ≤ b) (hTc : TruthLocal b c0 T) {L es : Log}
    (x : ByteArray × Digest) (hlen : b < es.length)
    (hc : (es.length - b) % 2 = 0 ∨ nr (kindOfC es) ≤ (es.length - b) / 2) :
    D3 b c0 nr e T L (es ++ [x]) ↔ D3 b c0 nr e T L es := by
  have hk := kindOf_append x (show 0 < es.length by omega)
  have ha : ans3 b nr (es ++ [x]) = ans3 b nr es := by
    simp only [ans3, hk, List.length_append, List.length_singleton]
    rcases hc with hc | hc
    · rw [show (es.length + 1 - b) / 2 = (es.length - b) / 2 by omega]
    · rw [min_eq_left hc, min_eq_left (le_trans hc (Nat.div_le_div_right (by omega)))]
  have hle : b + 2 * ans3 b nr es ≤ es.length := by
    have : ans3 b nr es ≤ (es.length - b) / 2 := min_le_right _ _
    omega
  simp only [D3, ha, List.length_append, List.length_singleton]
  rw [wrong3_congr hb1 hTc (agree_append es [x] hle)]
  exact ⟨fun h => ⟨hlen, h.2⟩, fun h => ⟨by omega, h.2⟩⟩

theorem not_D3_short {L es : Log} (h : es.length ≤ b) : ¬ D3 b c0 nr e T L es :=
  fun hd => by have := hd.1; omega

/-- At a real round's squeeze, the extension answers one more round, and its claim and truth
are the round polynomial and the bound tables at the answer's first F coordinate. -/
theorem wrong3_ext1 (hb1 : 1 ≤ b) (hTc : TruthLocal b c0 T) (L es : Log) (a : Digest) {j : ℕ}
    (hj : es.length = b + 2 * j + 1) :
    Wrong3 b c0 nr e T L (ext1 es a) (j + 1) ↔
      peval (g3At b es j (clR b c0 L es j)) (chF a 0) ≠
        trueSum e ((bindAll (T L es) (rchs b es j)).map (bind0 · (chF a 0)))
          (nr (kindOfC es) - (j + 1)) := by
  have hA : Agree (ext1 es a) es (b + 2 * j + 1) := agree_append es _ (by omega)
  have hk : kindOfC (ext1 es a) = kindOfC es := kindOf_append _ (by omega)
  have hr : rch b (ext1 es a) j = chF a 0 := by
    simp only [rch, fAt, ansAt]
    rw [← hj, entAt_ext1]
  obtain ⟨hT, hc0⟩ := hTc L (ext1 es a) es (hA.mono (by omega))
  have hcl : clR b c0 L (ext1 es a) j = clR b c0 L es j :=
    clR_congr (l := j) hc0 (hA.mono (by omega))
  have hg : g3At b (ext1 es a) j (clR b c0 L es j) = g3At b es j (clR b c0 L es j) := by
    simp only [g3At, msgAt, hA (b + 2 * j) (by omega)]
  have hrs : rchs b (ext1 es a) j = rchs b es j := rchs_congr (l := j) (hA.mono (by omega))
  simp only [Wrong3, clR, hcl, hg, hr, rchs_succ, hrs, hT, hk, bindAll_append]

set_option linter.constructorNameAsVariable false in
open Classical in
/-- **The round row** (§5.2 Z3): from a doomed claim, at most `3·2^128` answers make the next
claim true. -/
theorem D3_single (hb1 : 1 ≤ b) (hTc : TruthLocal b c0 T) (he : e.deg = 3)
    (hsz : ∀ L es, ∀ t ∈ T L es, t.size = 2 ^ nr (kindOfC es)) (L es : Log) :
    (Finset.univ.filter fun a => D3 b c0 nr e T L es ∧ ¬ D3 b c0 nr e T L (ext1 es a)).card ≤
      3 * 2 ^ 128 := by
  by_cases hlen : b < es.length
  swap
  · rw [Finset.filter_false_of_mem fun a _ h => not_D3_short (by omega) h.1]; simp
  by_cases hc : (es.length - b) % 2 = 0 ∨ nr (kindOfC es) ≤ (es.length - b) / 2
  · rw [Finset.filter_false_of_mem fun a _ h =>
      h.2 ((D3_append_iff hb1 hTc _ hlen hc).mpr h.1)]
    simp
  simp only [not_or, not_le] at hc
  obtain ⟨j, hjdef⟩ : ∃ j, j = (es.length - b) / 2 := ⟨_, rfl⟩
  have hj : j < nr (kindOfC es) := hjdef ▸ hc.2
  have hlj : es.length = b + 2 * j + 1 := by omega
  have hans : ans3 b nr es = j := by rw [ans3, hjdef]; exact min_eq_right hc.2.le
  by_cases hw : Wrong3 b c0 nr e T L es j
  swap
  · rw [Finset.filter_false_of_mem fun a _ h => hw (hans ▸ h.1.2)]; simp
  have hts : ∀ t ∈ bindAll (T L es) (rchs b es j), t.size = 2 ^ (nr (kindOfC es) - j - 1 + 1) := by
    refine bindAll_size (rchs b es j) _ fun t ht => ?_
    rw [hsz L es t ht]; congr 1; simp only [rchs, List.length_map, List.length_range]; omega
  have hesc := round_escape_le e (bindAll (T L es) (rchs b es j)) hts
    (claim := clR b c0 L es j) (by
      rw [show nr (kindOfC es) - j - 1 + 1 = nr (kindOfC es) - j by omega]; exact hw)
    (g3At b es j (clR b c0 L es j))
  refine le_trans (Finset.card_le_card (t := Finset.univ.filter fun a : Digest => chF a 0 ∈ _)
    fun a ha => ?_) (by rw [card_chF_fiber]; exact Nat.mul_le_mul_right _ (hesc.trans he.le))
  have hnd : ¬ D3 b c0 nr e T L (ext1 es a) := by
    rw [Finset.mem_filter] at ha; exact ha.2.2
  have hans' : ans3 b nr (ext1 es a) = j + 1 := by
    have hk : kindOfC (ext1 es a) = kindOfC es := kindOf_append _ (by omega)
    rw [ans3, hk, show (ext1 es a).length = es.length + 1 by simp [ext1],
      min_eq_right (by omega)]
    omega
  have hnw : ¬ Wrong3 b c0 nr e T L (ext1 es a) (j + 1) := fun h =>
    hnd ⟨by simp [ext1]; omega, by rw [hans']; exact h⟩
  rw [wrong3_ext1 hb1 hTc L es a hlj, not_not] at hnw
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  refine ⟨⟨by rw [he]; rfl, g3_check es j _⟩, ?_⟩
  rw [hnw, show nr (kindOfC es) - (j + 1) = nr (kindOfC es) - j - 1 by omega]

theorem D3_log_congr {L L' X : Log} (hT : T L' X = T L X) (hc : c0 L' X = c0 L X) :
    D3 b c0 nr e T L' X ↔ D3 b c0 nr e T L X := by
  simp only [D3, Wrong3, clR_log_congr hc, hT]

/-- **The position facts of a rounds phase**: it starts at `b ≥ 1`, has `nMax ≥ 1` items
`(absorb, squeeze)` of which at most `nMax` are real, and no multi-squeeze phase meets it. -/
structure RoundsPhase (b nMax : ℕ) (nr : CKind → ℕ) : Prop where
  hb1 : 1 ≤ b
  hn0 : 0 < nMax
  hnr : ∀ κ, nr κ ≤ nMax
  hsq : ∀ j < nMax, fsItems4[b + 2 * j + 1]? = some .squeeze
  hph : ∀ p s0 r, fsRnd4 p = some (s0, r) → p < b ∨ b + 2 * nMax ≤ p

/-- What the truth must read the same off the charging log and the whole log, on `hloc_of`'s
extensions (`StabExt`; §10 changes 10). -/
def TruthStable (c0 : Log → Log → F) (T : Log → Log → Array (Array F)) : Prop :=
  ∀ L i, ¬ Bad L → G.IsChain L i → ∀ X, StabExt fsRnd4 (entriesOf L (pathOf L i)) X →
    T (L.take i) X = T L X ∧ c0 (L.take i) X = c0 L X

/-- **The five obligations for the round doom** at `δ = deltaR`, `N = 3·2^128`. -/
theorem rounds3_obl {nMax : ℕ} (P : RoundsPhase b nMax nr) (hTc : TruthLocal b c0 T)
    (he : e.deg = 3) (hsz : ∀ L es, ∀ t ∈ T L es, t.size = 2 ^ nr (kindOfC es))
    (hst : TruthStable c0 T) : StepObl (D3 b c0 nr e T) fsRnd4 deltaR (3 * 2 ^ 128) where
  habs L es x len _ hit hd := by
    refine (D3_append_iff P.hb1 hTc x hd.1 ?_).mpr hd
    by_contra hc
    simp only [not_or, not_le] at hc
    have h := P.hsq ((es.length - b) / 2) (lt_of_lt_of_le hc.2 (P.hnr _))
    rw [show b + 2 * ((es.length - b) / 2) + 1 = es.length by have := hd.1; omega, hit] at h
    cases h
  hmid L es x s0 r _ hr _ := by
    rcases P.hph _ _ _ hr with h | h
    · exact ⟨fun hd => absurd hd (not_D3_short (by simp; omega)),
        fun hd => absurd hd (not_D3_short (by omega))⟩
    · exact D3_append_iff P.hb1 hTc x (by have := P.hn0; omega)
        (Or.inr (le_trans (P.hnr _) (by omega)))
  hsingle L es _ _ _ := D3_single P.hb1 hTc he hsz L es
  hround L es₀ s0 r _ hl hr := by
    rw [condCount_eq_zero]
    · exact zero_le
    intro as has ⟨_, hd, hnd⟩
    obtain ⟨-, hpr, hspec⟩ := fsRnd4_ok _ _ _ hr
    have hlen := length_ext as es₀
    have hne : ext es₀ as ≠ [] := by
      intro h; rw [h] at hlen; simp at hlen; omega
    have hdl : (ext es₀ as).dropLast.length = s0 + r := by
      rw [List.length_dropLast, hlen]; omega
    by_cases hfar : b + 2 * nMax ≤ s0 + 1
    · have := (D3_append_iff P.hb1 hTc ((ext es₀ as).getLast hne)
        (by have := P.hn0; omega) (Or.inr (le_trans (P.hnr _) (by omega)))).mpr hd
      rw [List.dropLast_append_getLast hne] at this
      exact hnd this
    · have h1 : s0 + 1 < b := (P.hph _ _ _ (hspec (s0 + 1) (by omega) hpr).2).resolve_right
        (by omega)
      have h2 : s0 + r < b := by
        rcases P.hph _ _ _ (hspec (s0 + r) (by omega) le_rfl).2 with h | h
        · exact h
        · have := P.hph _ _ _ (hspec b (by omega) (by omega)).2
          have := P.hn0
          omega
      exact not_D3_short (by omega) hd
  hstab L i hb hci X hX := by
    obtain ⟨hT, hc⟩ := hst L i hb hci X hX
    exact D3_log_congr hT hc

open Classical in
/-- **The contract's step law for the round doom**, with error `εD = εR − ε_H`. -/
theorem rounds3_step {nMax : ℕ} (P : RoundsPhase b nMax nr) (hTc : TruthLocal b c0 T)
    (he : e.deg = 3) (hsz : ∀ L es, ∀ t ∈ T L es, t.size = 2 ^ nr (kindOfC es))
    (hst : TruthStable c0 T) (L : Log) (q : ByteArray) (hl : L.length < logCap)
    (hμ : G.muG (D3 b c0 nr e T) (pRoundG (D3 b c0 nr e T) fsRnd4) L < 1)
    (hq : q ∉ L.map Prod.fst) :
    ∑ a : Digest, G.muG (D3 b c0 nr e T) (pRoundG (D3 b c0 nr e T) fsRnd4) (L ++ [(q, a)]) ≤
      (G.muG (D3 b c0 nr e T) (pRoundG (D3 b c0 nr e T) fsRnd4) L + epsD) * 2 ^ 256 :=
  step_epsD three_le_deltaR (rounds3_obl P hTc he hsz hst) L q hl hμ hq

end Rounds3

/-! ## Part C: Z3 (`b = 15`, 26 items, `m − 6` real rounds) -/

/-! ## Part D: multi-squeeze membership and `roundsPhase_of` (T4: the front's round phases Z3, Lr2, E2 are P4's, not copied) -/

theorem fsRnd_mem {p s0 r : ℕ} (h : fsRnd4 p = some (s0, r)) :
    (s0, r) ∈ fsRanges4 ∧ s0 < p ∧ p ≤ s0 + r := by
  have hp := List.find?_some h
  simp only [decide_eq_true_eq] at hp
  exact ⟨List.mem_of_find?_eq_some h, hp⟩

/-- A rounds phase from a checked item range and a checked gap between the multi-squeeze
phases. -/
theorem roundsPhase_of {b nMax : ℕ} {nr : CKind → ℕ} (hb1 : 1 ≤ b) (hn0 : 0 < nMax)
    (hnr : ∀ κ, nr κ ≤ nMax)
    (hsq : (List.range nMax).all (fun j => fsItems4[b + 2 * j + 1]? == some .squeeze) = true)
    (hgap : fsRanges4.all (fun x => decide (x.1 + x.2 < b ∨ b + 2 * nMax ≤ x.1 + 1)) = true) :
    RoundsPhase b nMax nr where
  hb1 := hb1
  hn0 := hn0
  hnr := hnr
  hsq j hj := by
    simp only [List.all_eq_true, List.mem_range, beq_iff_eq] at hsq
    exact hsq j hj
  hph p s0 r h := by
    obtain ⟨hmem, h1, h2⟩ := fsRnd_mem h
    simp only [List.all_eq_true, decide_eq_true_eq] at hgap
    have := hgap _ hmem
    omega

/-! ## Controls -/

/-- Control (positive): a false initial claim dooms the chain at the phase's first absorb. -/
theorem D3_first_absorb (nr : CKind → ℕ) (L : Log) :
    D3 15 (fun _ _ => 1) nr (.var 0) (fun _ _ => #[]) L (List.replicate 16 default) := by
  refine ⟨by simp, ?_⟩
  simp [Wrong3, ans3, clR, trueSum, tbl, rchs, bindAll, Expr.eval]

/-- Control (negative): before the phase's first absorb nothing is doomed. -/
theorem not_D3_before (nr : CKind → ℕ) (L : Log) (c0 : Log → Log → F)
    (T : Log → Log → Array (Array F)) (e : Expr) :
    ¬ D3 15 c0 nr e T L (List.replicate 15 default) :=
  not_D3_short (by simp)

end FR.Snd.T4

/-! # Port of `FRSoundnessStepC` (its module doc describes the 3.x original) -/

namespace FR.Snd.T4
open RecursionFast FR.Merkle Finset
open scoped NNReal

set_option linter.constructorNameAsVariable false

/-! ## Part A: the composed doom -/

/-- What `Rej` must satisfy: monotone; unchanged by an entry at a squeeze position; stable under
the charging log. -/
structure RejOK (Rej : Log → Log → Prop) : Prop where
  mono : ∀ L es x, Rej L es → Rej L (es ++ [x])
  sq : ∀ L es x, fsItems4[es.length]? = some .squeeze → (Rej L (es ++ [x]) ↔ Rej L es)
  stab : ∀ L i, ¬ Bad L → G.IsChain L i → ∀ X, StabExt fsRnd4 (entriesOf L (pathOf L i)) X →
    (Rej (L.take i) X ↔ Rej L X)

/-- Inside a multi-squeeze phase, `Rej` does not change along a formal extension. -/
theorem rej_ext {Rej : Log → Log → Prop} (hR : RejOK Rej) {L es₀ : Log} {s0 r : ℕ}
    (hl : es₀.length = s0 + 1) (hr : fsRnd4 (s0 + 1) = some (s0, r)) :
    ∀ as : List Digest, as.length ≤ r → (Rej L (ext es₀ as) ↔ Rej L es₀) := by
  obtain ⟨-, hpr, hspec⟩ := fsRnd4_ok _ _ _ hr
  intro as
  induction as using List.reverseRecOn with
  | nil => intro _; rfl
  | append_singleton as a ih =>
    intro hlen
    simp only [List.length_append, List.length_singleton] at hlen
    rw [ext_append, ext1, hR.sq _ _ _ ?_, ih (by omega)]
    rw [length_ext as es₀, hl]
    exact (hspec _ (by omega) (by omega)).1

/-- A position of a multi-squeeze phase is a squeeze. -/
theorem sq_of_fsRnd {p s0 r : ℕ} (h : fsRnd4 p = some (s0, r)) :
    fsItems4[p]? = some .squeeze := by
  obtain ⟨h1, h2, hs⟩ := fsRnd4_ok _ _ _ h
  exact (hs p h1 h2).1

open Classical in
/-- **`stepObl_compose`**: the obligations of the composed doom from those of the phases' doom
under `¬ Rej`. -/
theorem stepObl_compose {Rej : Log → Log → Prop} {Dp : ℕ → Log → Log → Prop} {δ : ℝ≥0} {N : ℕ}
    (hR : RejOK Rej)
    (habs : ∀ L es x len, G.Matches (es ++ [x]) → fsItems4[es.length]? = some (.absorb len) →
      ¬ Rej L es → DPos Dp L es → Rej L (es ++ [x]) ∨ DPos Dp L (es ++ [x]))
    (hmid : ∀ L es x s0 r, G.Matches (es ++ [x]) → fsRnd4 es.length = some (s0, r) →
      es.length < s0 + r → ¬ Rej L es → (DPos Dp L (es ++ [x]) ↔ DPos Dp L es))
    (hsingle : ∀ L es, G.Matches es → fsItems4[es.length]? = some .squeeze →
      fsRnd4 es.length = none → ¬ Rej L es →
      (Finset.univ.filter fun a => DPos Dp L es ∧ ¬ DPos Dp L (ext1 es a)).card ≤ N)
    (hround : ∀ L es₀ s0 r, G.Matches es₀ → es₀.length = s0 + 1 →
      fsRnd4 (s0 + 1) = some (s0, r) → ¬ Rej L es₀ → condCount (DPos Dp) L es₀ r [] ≤ δ)
    (hstab : ∀ L i, ¬ Bad L → G.IsChain L i → ∀ X, StabExt fsRnd4 (entriesOf L (pathOf L i)) X →
      (DPos Dp (L.take i) X ↔ DPos Dp L X)) :
    StepObl (DC Rej Dp) fsRnd4 δ N where
  habs L es x len hm hit hd := by
    by_cases hr : Rej L es
    · exact Or.inl (hR.mono _ _ _ hr)
    · exact habs L es x len hm hit hr (hd.resolve_left hr)
  hmid L es x s0 r hm hrnd hlt := by
    have hrej := hR.sq L es x (sq_of_fsRnd hrnd)
    by_cases hr : Rej L es
    · exact ⟨fun _ => Or.inl hr, fun _ => Or.inl (hrej.mpr hr)⟩
    · have := hmid L es x s0 r hm hrnd hlt hr
      simp only [DC, hrej, hr, false_or, this]
  hsingle L es hm hit hrnd := by
    by_cases hr : Rej L es
    · rw [Finset.filter_false_of_mem fun a _ h =>
        h.2 (Or.inl ((hR.sq L es _ hit).mpr hr))]
      simp
    · refine le_trans (Finset.card_le_card fun a ha => ?_) (hsingle L es hm hit hrnd hr)
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, DC, not_or] at ha ⊢
      exact ⟨ha.1.resolve_left hr, ha.2.2⟩
  hround L es₀ s0 r hm hl hrnd := by
    have hext := rej_ext hR (L := L) hl hrnd
    have hr1 : 1 ≤ r := by have := (fsRnd4_ok _ _ _ hrnd).2.1; omega
    by_cases hr : Rej L es₀
    · rw [condCount_eq_zero]
      · exact zero_le
      intro as has ⟨_, _, hnd⟩
      exact hnd (Or.inl ((hext as has.le).mpr hr))
    · refine le_trans (le_of_eq (condCount_congr fun as has => ?_))
        (hround L es₀ s0 r hm hl hrnd hr)
      have hne : as ≠ [] := by rintro rfl; simp at has; omega
      have h1 : ¬ Rej L (ext es₀ as) := fun h => hr ((hext as has.le).mp h)
      have h2 : ¬ Rej L (ext es₀ as).dropLast := by
        rw [ext_dropLast _ hne]
        exact fun h => hr ((hext _ (by simp; omega)).mp h)
      simp only [EscAtG, DC, h1, h2, false_or]
  hstab L i hb hci X hX := by
    simp only [DC, hR.stab L i hb hci X hX, hstab L i hb hci X hX]

/-! ## Part B: the single-squeeze rows -/

/-! ## Part C: the P2 row -/

/-- The proximity parameters of level `i` of kind `κ`: `n = 2^log₂n`, `k = n/2^(i+1)`,
`e = ⌊(n − k)/2⌋` (§2.2). -/
def lvN (κ : CKind) (i : ℕ) : ℕ := 2 ^ (CKind.lv κ i).logN
def lvK (κ : CKind) (i : ℕ) : ℕ := lvN κ i / 2 ^ (i + 1)
def lvE (κ : CKind) (i : ℕ) : ℕ := (lvN κ i - lvK κ i) / 2

/-- Control: the parameters are `pcsLevels`'s (the levels `mca_ud_line` is checked at). -/
theorem lv_eq_pcsLevels :
    ((List.range 5).map fun i => (lvN (.seg .L30) i, lvK (.seg .L30) i, lvE (.seg .L30) i)) ++
      ((List.range 5).map fun i => (lvN (.seg .L32) i, lvK (.seg .L32) i, lvE (.seg .L32) i)) =
      pcsLevels := by
  decide

/-- T4: control: the `m = 31` ladder (`L31`, `N2`; not in 3.x's `pcsLevels`) meets the same
hypotheses of `mca_ud_line` (`2e + k ≤ n ≤ nMax`, `C_mca ≤ 2^60`, the P1 row). -/
theorem lv31_ok : ∀ i < 5, 2 * lvE (.seg .L31) i + lvK (.seg .L31) i ≤ lvN (.seg .L31) i ∧
    lvN (.seg .L31) i ≤ nMax ∧ cMca (lvN (.seg .L31) i) (lvK (.seg .L31) i) (lvE (.seg .L31) i) ≤ 2 ^ 60 ∧
    2 ^ 6 * cMca (lvN (.seg .L31) i) (lvK (.seg .L31) i) (lvE (.seg .L31) i) + 2 ≤ 2 ^ 66 := by
  intro i hi; interval_cases i <;> decide

/-- **The P2 row** (§5.2), in ℚ as `positions_bad_le` states it: at every level of every kind,
`(1 − eᵢ/nᵢ)^{tᵢ} ≤ 15/2^124 − 2·2^-142 − 2^-238` (kernel arithmetic: the exponents exceed
`norm_num`'s). -/
theorem p2_row_le_q (κ : CKind) (i : ℕ) (hi : i < 5) :
    (1 - (lvE κ i : ℚ) / lvN κ i) ^ (CKind.lv κ i).t ≤ 15 / 2 ^ 124 - 2 / 2 ^ 142 - 1 / 2 ^ 238 := by
  interval_cases i <;> rcases κ with (_|_|_) | (_|_|_) <;> decide +kernel

/-- **The P2 row against `deltaR`.** -/
theorem p2_row_le (κ : CKind) (i : ℕ) (hi : i < 5) :
    ((1 - (lvE κ i : ℚ) / lvN κ i) ^ (CKind.lv κ i).t : ℝ) ≤ deltaR := by
  rw [deltaR_coe]
  have := p2_row_le_q κ i hi
  have h : ((15 / 2 ^ 124 - 2 / 2 ^ 142 - 1 / 2 ^ 238 : ℚ) : ℝ) =
      15 / 2 ^ 124 - 2 / 2 ^ 142 - 1 / 2 ^ 238 := by push_cast; ring
  rw [← h]
  exact_mod_cast this

/-- The P2 phase parameters (checked): `per ≥ 1` indices of `log₂ n` bits fit an answer, and the
phase's `sq` answers (sized for `m* = 32`) carry the `t` indices of every kind. -/
theorem p2_params (κ : CKind) (i : ℕ) (hi : i < 5) :
    0 < (CKind.lv κ i).per ∧ (CKind.lv κ i).per * (CKind.lv κ i).logN ≤ 256 ∧
      (CKind.lv κ i).t ≤ (lvlStar i).sq * (CKind.lv κ i).per := by
  interval_cases i <;> rcases κ with (_|_|_) | (_|_|_) <;> decide

/-- **The P2 row** (`hround`, §5.2): if level `i`'s escape puts all its `tᵢ` positions in a set
`S` with `|S| + eᵢ < nᵢ` (the consistency set of a far or wrong fold, A.10), the phase is charged
at most `deltaR` (`p2_round_le`, `p2_row_le`). -/
theorem p2_hround (κ : CKind) (i : ℕ) (hi : i < 5) {D : Log → Log → Prop} {L es₀ : Log} {s0 : ℕ}
    (hl : es₀.length = s0 + 1) (S : Finset (Fin (2 ^ (CKind.lv κ i).logN)))
    (hS : S.card + lvE κ i < lvN κ i)
    (hesc : ∀ as : List Digest, as.length = (lvlStar i).sq → EscAtG D L (ext es₀ as) →
      ∀ k < (CKind.lv κ i).t, posAt (ext es₀ as) s0 (CKind.lv κ i).logN (CKind.lv κ i).per k ∈
        S.map Fin.valEmbedding) :
    condCount D L es₀ (lvlStar i).sq [] ≤ deltaR := by
  obtain ⟨hper, hpb, ht⟩ := p2_params κ i hi
  have h1 := p2_round_le hl hper hpb ht S hesc
  have h2 := p2_row_le κ i hi
  rw [← NNReal.coe_le_coe] at h1 ⊢
  refine h1.trans (le_trans ?_ h2)
  push_cast
  have hn : (lvN κ i : ℝ) = 2 ^ (CKind.lv κ i).logN := by simp [lvN]
  have hpos : (0 : ℝ) < 2 ^ (CKind.lv κ i).logN := by positivity
  refine pow_le_pow_left₀ (by positivity) ?_ _
  rw [hn, div_le_iff₀ hpos, sub_mul, one_mul, div_mul_cancel₀ _ hpos.ne']
  have : (S.card : ℝ) + lvE κ i ≤ 2 ^ (CKind.lv κ i).logN := by
    rw [← hn]; exact_mod_cast hS.le
  linarith

/-! ## Controls -/

/-- Control (positive): the empty `Rej` satisfies `RejOK`. -/
theorem rejOK_false : RejOK fun _ _ => False :=
  ⟨fun _ _ _ h => h, fun _ _ _ _ => Iff.rfl, fun _ _ _ _ _ _ => Iff.rfl⟩

/-- Control (negative): a `Rej` that changes at a squeeze position (here Z1's first, position 3)
is not `RejOK`. -/
theorem not_rejOK_len : ¬ RejOK fun _ es => 4 ≤ es.length := by
  intro h
  have h3 : fsItems4[(List.replicate 3 (default : ByteArray × Digest)).length]? = some .squeeze := by
    simp only [List.length_replicate]; decide +kernel
  have := (h.sq [] _ default h3).mp (by simp)
  simp at this

end FR.Snd.T4

/-! # Port of `FRSoundnessStepE` (its module doc describes the 3.x original) -/

namespace FR.Snd.T4
open RecursionFast FR.Merkle Finset
open scoped NNReal

set_option linter.constructorNameAsVariable false

/-! ## Part A: the multi-squeeze bad sets -/

/-! ## Part B: the phase map and the position doom -/

/-- **The position doom** (A.10): position `p`'s doom is the doom of its phase. -/
def Dp (Dk : ℕ → Log → Log → Prop) (p : ℕ) : Log → Log → Prop := Dk (phOf4 p)

/-- Checked: every phase with Fiat–Shamir items is the phase of its first position. -/
theorem phOf_start : (List.range 52).all (fun k => isQ k || phOf4 (phStart4 k) == k) = true := by
  unfold phOf4 phStart4; rw [fsStarts4_eq]; decide +kernel

/-- The phase changes only at a phase start. -/
theorem phOf_succ {p : ℕ} (hs : p + 1 ∉ fsStarts4) : phOf4 (p + 1) = phOf4 p := by
  unfold phOf4
  congr 2
  refine List.filter_congr fun x hx => ?_
  have : x ≠ p + 1 := fun h => hs (h ▸ hx)
  simp only [decide_eq_decide]
  omega

/-- Checked: a multi-squeeze phase `(s0, r)` is one phase starting at `s0 + 1`, holding its `r`
positions, with `r ≥ 2`. -/
theorem ms_check : fsRanges4.all (fun x => 2 ≤ x.2 && fsStarts4.contains (x.1 + 1) &&
    (List.range x.2).all fun j => phOf4 (x.1 + 1 + j) == phOf4 (x.1 + 1)) = true := by
  unfold phOf4; rw [fsRanges4_eq, fsStarts4_eq]; decide +kernel

theorem ms_phOf {s0 r : ℕ} (h : (s0, r) ∈ fsRanges4) :
    2 ≤ r ∧ ∀ p, s0 < p → p ≤ s0 + r → phOf4 p = phOf4 (s0 + 1) := by
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
  ∀ s0 r, (s0, r) ∈ fsRanges4 →
    ∃ fin, Dk (phOf4 (s0 + 1)) = msD (Dk (phOf4 s0)) fin s0 r

/-- **`hmid` for every multi-squeeze position** (A.10): with every multi-squeeze phase in `msD`
form, a middle answer neither dooms nor undooms. -/
theorem hmid_of_msForm {Dk : ℕ → Log → Log → Prop} (hD : MsForm Dk) (L es : Log)
    (x : ByteArray × Digest) {s0 r : ℕ} (hrnd : fsRnd4 es.length = some (s0, r))
    (hlt : es.length < s0 + r) : DPos (Dp Dk) L (es ++ [x]) ↔ DPos (Dp Dk) L es := by
  obtain ⟨hmem, h1, -⟩ := fsRnd_mem hrnd
  obtain ⟨hr2, hph⟩ := ms_phOf hmem
  obtain ⟨fin, hfin⟩ := hD s0 r hmem
  have hA : DPos (Dp Dk) L (es ++ [x]) ↔ Dk (phOf4 s0) L (es.take (s0 + 1)) := by
    have hl' : (es ++ [x]).length - 1 = es.length := by simp
    unfold DPos Dp
    rw [hl', hph _ h1 hlt.le, hfin]
    unfold msD
    rw [ite_pos' (by simp; omega), List.take_append_of_le_length (by omega)]
  have hB : DPos (Dp Dk) L es ↔ Dk (phOf4 s0) L (es.take (s0 + 1)) := by
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
theorem esc_msD {Dk : ℕ → Log → Log → Prop} {s0 r : ℕ} (hmem : (s0, r) ∈ fsRanges4)
    {fin : Log → Log → Prop} (hfin : Dk (phOf4 (s0 + 1)) = msD (Dk (phOf4 s0)) fin s0 r)
    {L es₀ : Log} (hl : es₀.length = s0 + 1) (as : List Digest) (has : as.length = r)
    (he : EscAtG (DPos (Dp Dk)) L (ext es₀ as)) : Dk (phOf4 s0) L es₀ ∧ ¬ fin L (ext es₀ as) := by
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
  habs : ∀ L es x len, G.Matches (es ++ [x]) → fsItems4[es.length]? = some (.absorb len) →
    ¬ Rej L es → Dk (phOf4 (es.length - 1)) L es →
      Rej L (es ++ [x]) ∨ Dk (phOf4 es.length) L (es ++ [x])
  hsingle : ∀ L es, G.Matches es → fsItems4[es.length]? = some .squeeze → fsRnd4 es.length = none →
    ¬ Rej L es →
      (univ.filter fun a => Dk (phOf4 (es.length - 1)) L es ∧
        ¬ Dk (phOf4 es.length) L (ext1 es a)).card ≤ N
  hfin : ∀ s0 r, (s0, r) ∈ fsRanges4 → ∀ L es₀, G.Matches es₀ → es₀.length = s0 + 1 →
    ¬ Rej L es₀ → condCount (DPos (Dp Dk)) L es₀ r [] ≤ deltaR
  hstab : ∀ k L i, ¬ Bad L → G.IsChain L i → ∀ X, StabExt fsRnd4 (entriesOf L (pathOf L i)) X →
    phOf4 (X.length - 1) = k → (Dk k (L.take i) X ↔ Dk k L X)

open Classical in
/-- **`KState.step` at `εD` for the whole transcript** (BLUEPRINT §5.1, A.10): the potential
`muG` of the entry's doom `DC Rej (Dp Dk)`, charged by `pRoundG … fsRnd4`, satisfies the contract's
step law with error `εD = εR − ε_H` (the doom potential's share, §10 changes 15), given the
per-phase obligations and `N ≤ 2^256·deltaR`. -/
theorem kstate_step {Rej : Log → Log → Prop} {Dk : ℕ → Log → Log → Prop} {N : ℕ}
    (hN : (N : ℝ≥0) ≤ 2 ^ 256 * deltaR) (ob : PhaseObl Rej Dk N) (L : Log) (q : ByteArray)
    (hl : L.length < logCap)
    (hμ : G.muG (DC Rej (Dp Dk)) (pRoundG (DC Rej (Dp Dk)) fsRnd4) L < 1)
    (hq : q ∉ L.map Prod.fst) :
    ∑ a : Digest, G.muG (DC Rej (Dp Dk)) (pRoundG (DC Rej (Dp Dk)) fsRnd4) (L ++ [(q, a)]) ≤
      (G.muG (DC Rej (Dp Dk)) (pRoundG (DC Rej (Dp Dk)) fsRnd4) L + epsD) * 2 ^ 256 := by
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
theorem hfin_ml {Dk : ℕ → Log → Log → Prop} {s0 r n : ℕ} (hmem : (s0, r) ∈ fsRanges4)
    {fin : Log → Log → Prop} (hfin : Dk (phOf4 (s0 + 1)) = msD (Dk (phOf4 s0)) fin s0 r)
    (hn : n ≤ r * 2) (hn' : n ≤ 239) (t : Log → Log → Array F)
    (ht : ∀ L es₀, (t L es₀).size = 2 ^ n)
    (h0 : ∀ L es₀, Dk (phOf4 s0) L es₀ → tbl n (t L es₀) ≠ 0)
    (hesc : ∀ L es₀ as, es₀.length = s0 + 1 → as.length = r → Dk (phOf4 s0) L es₀ →
      ¬ fin L (ext es₀ as) →
        ¬ mlDoom n (t L es₀) (List.ofFn fun j : Fin (r * 2) => coordAt (ext es₀ as) s0 j))
    (L es₀ : Log) (hl : es₀.length = s0 + 1) : condCount (DPos (Dp Dk)) L es₀ r [] ≤ deltaR := by
  by_cases hd : Dk (phOf4 s0) L es₀
  · refine (ml_round_le hl hn (ht L es₀) (h0 L es₀ hd) fun as has he => ?_).trans
      (coord_le_deltaR hn')
    obtain ⟨hd', hnf⟩ := esc_msD hmem hfin hl as has he
    exact hesc L es₀ as hl has hd' hnf
  · rw [condCount_eq_zero fun as has he => hd (esc_msD hmem hfin hl as has he).1]
    exact zero_le

open Classical in
/-- **`hfin` for RS1** (`rs1_round_le`): the escape puts `(r″, κ)` in a set of at most
`c·|F|^7`, `c ≤ 239`. -/
theorem hfin_rs1 {Dk : ℕ → Log → Log → Prop} {s0 : ℕ} (hmem : (s0, 4) ∈ fsRanges4)
    {fin : Log → Log → Prop} (hfin : Dk (phOf4 (s0 + 1)) = msD (Dk (phOf4 s0)) fin s0 4)
    {c : ℕ} (hc : c ≤ 239) (P : Log → Log → Finset ((Fin 7 → F) × F))
    (hP : ∀ L es₀, Dk (phOf4 s0) L es₀ → (P L es₀).card ≤ c * Fintype.card F ^ 7)
    (hesc : ∀ L es₀ as, es₀.length = s0 + 1 → as.length = 4 → Dk (phOf4 s0) L es₀ →
      ¬ fin L (ext es₀ as) →
        ((fun i : Fin 7 => coordAt (ext es₀ as) s0 i), coordAt (ext es₀ as) s0 7) ∈ P L es₀)
    (L es₀ : Log) (hl : es₀.length = s0 + 1) : condCount (DPos (Dp Dk)) L es₀ 4 [] ≤ deltaR := by
  by_cases hd : Dk (phOf4 s0) L es₀
  · refine (rs1_round_le hl (P L es₀) (hP L es₀ hd) fun as has he => ?_).trans
      (coord_le_deltaR hc)
    obtain ⟨hd', hnf⟩ := esc_msD hmem hfin hl as has he
    exact hesc L es₀ as hl has hd' hnf
  · rw [condCount_eq_zero fun as has he => hd (esc_msD hmem hfin hl as has he).1]
    exact zero_le

open Classical in
/-- **`hfin` for a Schwartz–Zippel phase with per-coordinate losses** (S1: 26 multilinear
coordinates and the power batch `κ_s`), `Σ b ≤ 239`. -/
theorem hfin_seq {Dk : ℕ → Log → Log → Prop} {s0 r : ℕ} (hmem : (s0, r) ∈ fsRanges4)
    {fin : Log → Log → Prop} (hfin : Dk (phOf4 (s0 + 1)) = msD (Dk (phOf4 s0)) fin s0 r)
    (b : ℕ → ℕ) (hb : ∑ i ∈ range (r * 2), b i ≤ 239) (Doom : Log → Log → List F → Prop)
    (hstep : ∀ L es₀ l, Doom L es₀ l →
      (univ.filter fun c => ¬ Doom L es₀ (l ++ [c])).card ≤ b l.length)
    (h0 : ∀ L es₀, Dk (phOf4 s0) L es₀ → Doom L es₀ [])
    (hesc : ∀ L es₀ as, es₀.length = s0 + 1 → as.length = r → Dk (phOf4 s0) L es₀ →
      ¬ fin L (ext es₀ as) →
        ¬ Doom L es₀ (List.ofFn fun j : Fin (r * 2) => coordAt (ext es₀ as) s0 j))
    (L es₀ : Log) (hl : es₀.length = s0 + 1) : condCount (DPos (Dp Dk)) L es₀ r [] ≤ deltaR := by
  by_cases hd : Dk (phOf4 s0) L es₀
  · refine (seq_round_le hl (Doom L es₀) b (hstep L es₀) (h0 L es₀ hd) fun as has he => ?_).trans
      (coord_le_deltaR hb)
    obtain ⟨hd', hnf⟩ := esc_msD hmem hfin hl as has he
    exact hesc L es₀ as hl has hd' hnf
  · rw [condCount_eq_zero fun as has he => hd (esc_msD hmem hfin hl as has he).1]
    exact zero_le

open Classical in
/-- **`hfin` for P2.i** (`p2_hround`): the escape puts every queried position in a set `S` with
`|S| + eᵢ < nᵢ` (the consistency set of a doomed level, `consSet_card_of_not`). -/
theorem hfin_p2 (κ : CKind) (i : ℕ) (hi : i < 5) {Dk : ℕ → Log → Log → Prop} {s0 : ℕ}
    (hmem : (s0, (lvlStar i).sq) ∈ fsRanges4) {fin : Log → Log → Prop}
    (hfin : Dk (phOf4 (s0 + 1)) = msD (Dk (phOf4 s0)) fin s0 (lvlStar i).sq)
    (S : Log → Log → Finset (Fin (2 ^ (CKind.lv κ i).logN)))
    (hS : ∀ L es₀, Dk (phOf4 s0) L es₀ → (S L es₀).card + lvE κ i < lvN κ i)
    (hesc : ∀ L es₀ as, es₀.length = s0 + 1 → as.length = (lvlStar i).sq → Dk (phOf4 s0) L es₀ →
      ¬ fin L (ext es₀ as) → ∀ k < (CKind.lv κ i).t,
        posAt (ext es₀ as) s0 (CKind.lv κ i).logN (CKind.lv κ i).per k ∈ (S L es₀).map Fin.valEmbedding)
    (L es₀ : Log) (hl : es₀.length = s0 + 1) :
    condCount (DPos (Dp Dk)) L es₀ (lvlStar i).sq [] ≤ deltaR := by
  by_cases hd : Dk (phOf4 s0) L es₀
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

variable (nr : CKind → ℕ) (e : Expr) (T : Log → Log → Array (Array R))

/-- The claim after `l` rounds is not the true sum of the bound tables. -/
def Wrong2 (L es : Log) (l : ℕ) : Prop :=
  clR2 b wd rd ch c0 L es l ≠ trueSum e (bindAll (T L es) (rchs2 b ch es l)) (nr (kindOfC es) - l)

/-- **The asserted rounds' doom** (A.10's `Wrong2`): past the phase's first absorb, the running
claim after the answered rounds (`ans3`) is false. -/
def D2 (L es : Log) : Prop := b < es.length ∧ Wrong2 b wd rd ch c0 nr e T L es (ans3 b nr es)

variable {b wd rd ch c0 nr e T}

theorem wrong2_congr (hb1 : 1 ≤ b) (hTc : TruthLocal2 b c0 T) {L es es' : Log} {l : ℕ}
    (h : Agree es es' (b + 2 * l)) :
    Wrong2 b wd rd ch c0 nr e T L es l ↔ Wrong2 b wd rd ch c0 nr e T L es' l := by
  have hb := h.mono (show b ≤ b + 2 * l by omega)
  obtain ⟨hT, hc⟩ := hTc L es es' hb
  simp only [Wrong2, clR2_congr hc h, rchs2_congr h, hT, kindOfC_congr (hb.mono hb1)]

/-- **`habs` inside the phase**: appending where no real round is answered keeps the doom. -/
theorem D2_append_iff (hb1 : 1 ≤ b) (hTc : TruthLocal2 b c0 T) {L es : Log}
    (x : ByteArray × Digest) (hlen : b < es.length)
    (hc : (es.length - b) % 2 = 0 ∨ nr (kindOfC es) ≤ (es.length - b) / 2) :
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
          (nr (kindOfC es) - (j + 1)) := by
  have hA : Agree (ext1 es a) es (b + 2 * j + 1) := agree_append es _ (by omega)
  have hk : kindOfC (ext1 es a) = kindOfC es := kindOf_append _ (by omega)
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
/-- **The asserted round row** (A.10: L2, S2, E4 over F with `M = 2^128`; P1.i, Pf over K with
`M = 1`): from a doomed claim whose round check holds (`Chk2`, from `¬ Rej`), at most `2·M`
answers make the next claim true. `hfib` is the challenge map's fiber count
(`card_chF_fiber`, `card_chK_fiber`). -/
theorem D2_single [Fintype R] [DecidableEq R] (hb1 : 1 ≤ b) (hTc : TruthLocal2 b c0 T)
    (he : e.deg = 2) {M : ℕ}
    (hfib : ∀ S : Finset R, (univ.filter fun a : Digest => ch a ∈ S).card = S.card * M)
    (hsz : ∀ L es, ∀ t ∈ T L es, t.size = 2 ^ nr (kindOfC es)) (L es : Log)
    (hchk : ∀ j, es.length = b + 2 * j + 1 → j < nr (kindOfC es) → Chk2 b wd rd ch c0 L es j) :
    (univ.filter fun a => D2 b wd rd ch c0 nr e T L es ∧
      ¬ D2 b wd rd ch c0 nr e T L (ext1 es a)).card ≤ 2 * M := by
  by_cases hlen : b < es.length
  swap
  · rw [Finset.filter_false_of_mem fun a _ h => not_D2_short (by omega) h.1]; simp
  by_cases hc : (es.length - b) % 2 = 0 ∨ nr (kindOfC es) ≤ (es.length - b) / 2
  · rw [Finset.filter_false_of_mem fun a _ h =>
      h.2 ((D2_append_iff hb1 hTc _ hlen hc).mpr h.1)]
    simp
  simp only [not_or, not_le] at hc
  obtain ⟨j, hjdef⟩ : ∃ j, j = (es.length - b) / 2 := ⟨_, rfl⟩
  have hj : j < nr (kindOfC es) := hjdef ▸ hc.2
  have hlj : es.length = b + 2 * j + 1 := by omega
  have hans : ans3 b nr es = j := by rw [ans3, hjdef]; exact min_eq_right hc.2.le
  by_cases hw : Wrong2 b wd rd ch c0 nr e T L es j
  swap
  · rw [Finset.filter_false_of_mem fun a _ h => hw (hans ▸ h.1.2)]; simp
  have hts : ∀ t ∈ bindAll (T L es) (rchs2 b ch es j),
      t.size = 2 ^ (nr (kindOfC es) - j - 1 + 1) := by
    refine bindAll_size (rchs2 b ch es j) _ fun t ht => ?_
    rw [hsz L es t ht]; congr 1; simp only [rchs2, List.length_map, List.length_range]; omega
  have hesc := round_escape_le e (bindAll (T L es) (rchs2 b ch es j)) hts
    (claim := clR2 b wd rd ch c0 L es j) (by
      rw [show nr (kindOfC es) - j - 1 + 1 = nr (kindOfC es) - j by omega]; exact hw)
    (g2At b wd rd es j)
  refine le_trans (Finset.card_le_card (t := univ.filter fun a : Digest => ch a ∈ _)
    fun a ha => ?_) (by rw [hfib]; exact Nat.mul_le_mul_right _ (hesc.trans he.le))
  have hnd : ¬ D2 b wd rd ch c0 nr e T L (ext1 es a) := by
    rw [Finset.mem_filter] at ha; exact ha.2.2
  have hans' : ans3 b nr (ext1 es a) = j + 1 := by
    have hk : kindOfC (ext1 es a) = kindOfC es := kindOf_append _ (by omega)
    rw [ans3, hk, show (ext1 es a).length = es.length + 1 by simp [ext1],
      min_eq_right (by omega)]
    omega
  have hnw : ¬ Wrong2 b wd rd ch c0 nr e T L (ext1 es a) (j + 1) := fun h =>
    hnd ⟨by simp [ext1]; omega, by rw [hans']; exact h⟩
  rw [wrong2_ext1 hb1 hTc L es a hlj, not_not] at hnw
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  refine ⟨⟨by rw [he]; rfl, hchk j hlj hj⟩, ?_⟩
  rw [hnw, show nr (kindOfC es) - (j + 1) = nr (kindOfC es) - j - 1 by omega]

end Rounds2

/-! ## Controls -/

/-- Control: the phase map at a few positions (Z1's last squeeze, Z2's absorb, P3.0's first
squeeze after the column queries, Pf's last round; T4: `+14` past `E4`). -/
theorem phOf_examples : phOf4 12 = 3 ∧ phOf4 13 = 4 ∧ phOf4 370 = 30 ∧ phOf4 481 = 51 := by
  unfold phOf4; rw [fsStarts4_eq]; decide

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
theorem D2_first_absorb (nr : CKind → ℕ) (L : Log) :
    D2 15 16 readF (fun a => chF a 0) (fun _ _ => (1 : F)) nr (.var 0) (fun _ _ => #[]) L
      (List.replicate 16 default) := by
  refine ⟨by simp, ?_⟩
  simp [Wrong2, ans3, clR2, trueSum, tbl, rchs2, bindAll, Expr.eval]

/-- Control (negative): before the phase's first absorb nothing is doomed. -/
theorem not_D2_before (nr : CKind → ℕ) (L : Log) (c0 : Log → Log → F)
    (T : Log → Log → Array (Array F)) (e : Expr) :
    ¬ D2 15 16 readF (fun a => chF a 0) c0 nr e T L (List.replicate 15 default) :=
  not_D2_short (by simp)

end FR.Snd.T4

