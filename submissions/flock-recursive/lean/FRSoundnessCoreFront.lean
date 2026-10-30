-- G6: this module also holds the former modules `FRSoundnessCoreRows` (one section each, in import order).
import FRVIRFinalsCoreSG
import FRVIRTplFast
import FRSoundness4TailStep
import FRSoundnessCoreTruths
import RecursionFast.Contract.Certificate
import RecursionFast.Library.PaperTheorem

section G6_FRSoundnessCoreRows

-- New for `flock-recursive` (BLUEPRINT §10 changes 27 (B) step 3; stage RET-2): the declarations of
-- the 3.x soundness modules that the revision 4.1 certificate reads, moved here verbatim (same
-- names, statements and proofs) from `FRSoundnessStepE` (7), `FRSoundnessHide` (1), `FRKState` (1),
-- `FRSoundnessPIOP` (7), `FRSoundnessTail` (8), `FRSoundnessTailM` (1), `FRSoundnessFront` (3),
-- `FRSoundnessRows` (22), `FRSoundnessFrW0` (12), `FRSoundnessFrRS` (1), `FRSoundnessFrPend` (2),
-- `FRSoundnessFrZ` (18), `FRSoundnessFrB` (5), `FRSoundnessFrE` (6), `FRSoundnessFrL` (17),
-- `FRSoundnessFrW0V` (10), `FRSoundnessFrRS0` (5). Content: the rows and front readers revision 4.1
-- reuses (`fF`, `rowMat`, `Reads`, the `Rows` matrices, `stL`/`vkL`, `PubOK`, the Z/L/E/RS0 pieces,
-- `D2`/`D3`). The 3.x modules import this one.

/-! ## From `FRSoundnessStepE` (7 declarations) -/

section

namespace FR.Snd

open RecursionFast FR.Merkle Finset

open scoped NNReal

set_option linter.constructorNameAsVariable false

section Rounds2

variable {R : Type*} [Field R]

variable (b wd : ℕ) (rd : ByteArray → ℕ → R) (ch : Digest → R)

variable (c0 : Log → Log → R)

variable (nr : Kind → ℕ) (e : Expr) (T : Log → Log → Array (Array R))

/-- The claim after `l` rounds is not the true sum of the bound tables. -/
def Wrong2 (L es : Log) (l : ℕ) : Prop :=
  clR2 b wd rd ch c0 L es l ≠ trueSum e (bindAll (T L es) (rchs2 b ch es l)) (nr (kindOf es) - l)

/-- **The asserted rounds' doom** (A.10's `Wrong2`): past the phase's first absorb, the running
claim after the answered rounds (`ans3`) is false. -/
def D2 (L es : Log) : Prop := b < es.length ∧ Wrong2 b wd rd ch c0 nr e T L es (ans3 b nr es)

variable {b wd rd ch c0 nr e T}

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
/-- **The asserted round row** (A.10: L2, S2, E4 over F with `M = 2^128`; P1.i, Pf over K with
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

end FR.Snd

end

/-! ## From `FRSoundnessHide` (1 declaration) -/

section

namespace FR.Snd

open RecursionFast FR.Merkle Finset

open scoped NNReal

set_option linter.constructorNameAsVariable false

/-- `decodeL` reads the word only. -/
theorem decodeL_congr {κ : Kind} {L L' es es' : Log} {i : ℕ}
    (h : wordK κ L es i = wordK κ L' es' i) : decodeL κ L es i = decodeL κ L' es' i := by
  have key : ∀ (U U' : Fin (lvl κ i).rows → Fin (2 ^ (lvl κ i).logN) → K) (hU : U = U')
      (p : ∃ V : Fin (lvl κ i).rows → Fin (2 ^ (lvl κ i).logN) → K, (∀ r, V r ∈ codeK κ i) ∧
        2 ^ (lvl κ i).logN - lvE κ i ≤ (jointAgree U V).card)
      (p' : ∃ V : Fin (lvl κ i).rows → Fin (2 ^ (lvl κ i).logN) → K, (∀ r, V r ∈ codeK κ i) ∧
        2 ^ (lvl κ i).logN - lvE κ i ≤ (jointAgree U' V).card),
      Classical.choose p = Classical.choose p' := by
    intro U U' hU p p'; subst hU; rfl
  have hf : farL κ L es i ↔ farL κ L' es' i := by simp only [farL, h]
  unfold decodeL
  by_cases hn : farL κ L es i
  · simp only [hn, hf.mp hn, not_true_eq_false, dite_false]
  · simp only [hn, (not_congr hf).mp hn, not_false_eq_true, dite_true]
    exact key _ _ h _ _

end FR.Snd

end

/-! ## From `FRKState` (1 declaration) -/

section

namespace FR.Snd

open RecursionFast

open scoped NNReal

/-- The claimed error is within the contract's cap: `εR = 15/2^124 ≤ 2^-120`. -/
theorem epsR_le_errorCap : epsR ≤ errorCap := by
  rw [← NNReal.coe_le_coe, epsR, errorCap]
  push_cast
  norm_num

end FR.Snd

end

/-! ## From `FRSoundnessPIOP` (7 declarations) -/

section

namespace FR.Snd

open RecursionFast FR.Merkle Finset

/-- **A.10's `f⁽⁰⁾` in F**: element `e` is the constant coefficient of the decoded level-0
message's element `e` (`fTab`, row bits first). -/
noncomputable def fF (κ : Kind) (L es : Log) (e : ℕ) : F := (fTab κ L es 0 e).f₀

section Rows

open Circ Eval

/-- A row list's `A` (`sel = Row.a`), `B` or `C` matrix over `2^a` rows and `2^b` cells, as
`evalM`/`evalL` read it (`entriesOf`). -/
def rowMat (sel : Row → Lin) (rows : List Row) (a b : ℕ) : Fin (2 ^ a) → Fin (2 ^ b) → F :=
  fun x y => entry (Eval.entriesOf sel rows) x y

/-- The rows fit `2^a` rows and their cells `2^b` cells. -/
def RowsFit (rows : List Row) (a b : ℕ) : Prop :=
  rows.length ≤ 2 ^ a ∧ ∀ r ∈ rows, ∀ t ∈ r.a ++ r.b ++ r.c, t.1 < 2 ^ b

theorem sum_entry_mul (E : Entries) (x : ℕ) {b : ℕ} (w : Asg) (hE : ∀ e ∈ E, e.2.1 < 2 ^ b) :
    ∑ y : Fin (2 ^ b), entry E x y * w y =
      (E.map fun e => if e.1 = x then e.2.2 * w e.2.1 else 0).sum := by
  induction E with
  | nil => simp [entry]
  | cons e E ih =>
    have he : ∀ y : ℕ, entry (e :: E) x y =
        (if e.1 = x ∧ e.2.1 = y then e.2.2 else 0) + entry E x y := fun y => by
      simp only [entry, List.filter_cons]
      by_cases h : e.1 = x ∧ e.2.1 = y <;> simp [h]
    simp only [he, add_mul, Finset.sum_add_distrib, List.map_cons, List.sum_cons]
    rw [ih fun e' h' => hE e' (List.mem_cons_of_mem _ h')]
    congr 1
    have hb := hE e List.mem_cons_self
    rw [Finset.sum_eq_single ⟨e.2.1, hb⟩]
    · by_cases h : e.1 = x <;> simp [h]
    · intro y _ hy
      have : e.2.1 ≠ y.val := fun h => hy (Fin.ext h.symm)
      simp [this]
    · simp

theorem sum_entriesOf (sel : Row → Lin) (w : Asg) (x : ℕ) :
    ∀ (rows : List Row) (k : ℕ),
      List.sum (List.map (fun e : ℕ × ℕ × F => if e.1 = x then e.2.2 * w e.2.1 else 0)
          ((rows.zipIdx k).flatMap (fun p => (sel p.1).map fun t => (p.2, t.1, t.2)))) =
        if h : k ≤ x ∧ x - k < rows.length then (sel rows[x - k]).ev w else 0
  | [], k => by simp
  | r :: rows, k => by
    rw [List.zipIdx_cons, List.flatMap_cons, List.map_append, List.sum_append,
      sum_entriesOf sel w x rows (k + 1)]
    have h1 : List.sum (List.map (fun e : ℕ × ℕ × F => if e.1 = x then e.2.2 * w e.2.1 else 0)
        ((sel r).map fun t => (k, t.1, t.2))) = if k = x then (sel r).ev w else 0 := by
      by_cases hk : k = x
      · simp [hk, Lin.ev, Function.comp_def]
      · simp [hk, Function.comp_def]
    rw [h1]
    by_cases hk : k = x
    · subst hk; simp
    · by_cases h2 : k + 1 ≤ x ∧ x - (k + 1) < rows.length
      · have h3 : k ≤ x ∧ x - k < (r :: rows).length := ⟨by omega, by simp; omega⟩
        rw [dite_eq_left h2, dite_eq_left h3, ite_neg' hk, zero_add]
        congr 2
        rw [List.getElem_cons]
        simp only [show x - k ≠ 0 by omega, dite_false, Nat.sub_sub]
      · have h3 : ¬ (k ≤ x ∧ x - k < (r :: rows).length) := by
          intro h; apply h2; simp at h; omega
        simp only [h2, h3, hk, dite_false, ite_false, add_zero]

/-- **The matrix product is the rows' linear forms**: on rows whose cells fit, `(M w)(x)` is row
`x`'s form at `w` (`0` past the rows). -/
theorem matVec_rowMat (sel : Row → Lin) (rows : List Row) {a b : ℕ}
    (hc : ∀ r ∈ rows, ∀ t ∈ sel r, t.1 < 2 ^ b) (w : Asg) (x : Fin (2 ^ a)) :
    matVec (rowMat sel rows a b) (fun y => w y) x =
      if h : x.val < rows.length then (sel rows[x.val]).ev w else 0 := by
  have hE : ∀ e ∈ Eval.entriesOf sel rows, e.2.1 < 2 ^ b := by
    intro e he
    simp only [Eval.entriesOf, List.mem_flatMap, List.mem_map] at he
    obtain ⟨p, hp, t, ht, rfl⟩ := he
    exact hc p.1 (List.fst_mem_of_mem_zipIdx hp) t ht
  rw [matVec]
  simp only [rowMat]
  rw [sum_entry_mul _ _ w hE, Eval.entriesOf, sum_entriesOf sel w x rows 0]
  simp

/-- **The zerocheck tables' R1CS is "every row holds"** (A.10 E1/Lr1): on rows that fit, the
matrices `rowMat` satisfy `(Az)(x)·(Bz)(x) = (Cz)(x)` on the cube iff every row holds at `w`
(past the rows the three forms are `0`). -/
theorem sat_rowMat_iff (rows : List Row) {a b : ℕ} (hf : RowsFit rows a b) (w : Asg) :
    Sat (rowMat Row.a rows a b) (rowMat Row.b rows a b) (rowMat Row.c rows a b) (fun y => w y) ↔
      ∀ r ∈ rows, r.Holds w := by
  have hc : ∀ sel : Row → Lin, (∀ r, ∀ t ∈ sel r, t ∈ r.a ++ r.b ++ r.c) →
      ∀ r ∈ rows, ∀ t ∈ sel r, t.1 < 2 ^ b := fun sel hs r hr t ht => hf.2 r hr t (hs r t ht)
  have ha := hc Row.a fun r t h => by simp [h]
  have hb := hc Row.b fun r t h => by simp [h]
  have hcc := hc Row.c fun r t h => by simp [h]
  unfold Sat
  simp only [matVec_rowMat _ _ ha, matVec_rowMat _ _ hb, matVec_rowMat _ _ hcc]
  constructor
  · intro h r hr
    obtain ⟨x, hx, rfl⟩ := List.getElem_of_mem hr
    have := h ⟨x, lt_of_lt_of_le hx hf.1⟩
    simp only [hx, dite_true] at this
    exact this
  · intro h x
    by_cases hx : x.val < rows.length
    · simp only [hx, dite_true]; exact h _ (List.getElem_mem _)
    · simp [hx]

end Rows

end FR.Snd

end

/-! ## From `FRSoundnessTail` (8 declarations) -/

section

namespace FR.Snd

open RecursionFast FR.Merkle Finset

set_option linter.constructorNameAsVariable false

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

theorem Same.kind (h : Same L es L' es' p) (hp : 1 ≤ p) : kindOf es = kindOf es' :=
  kindOf_congr (h.1.mono hp)

section Reads

variable (h : Same L es L' es' p) {i : ℕ} (hi : i < 5) (κ : Kind)

include h

include hi

theorem wordK_same (hp : capPos i < p) : wordK κ L es i = wordK κ L' es' i := h.2 κ i hi hp

theorem decodeL_same (hp : capPos i < p) : decodeL κ L es i = decodeL κ L' es' i :=
  decodeL_congr (wordK_same h hi κ hp)

theorem msgOf_same (hp : capPos i < p) : msgOf κ L es i = msgOf κ L' es' i := by
  funext r x; simp only [msgOf, decodeL_same h hi κ hp]

theorem fTab_same (hp : capPos i < p) : fTab κ L es i = fTab κ L' es' i := by
  funext y; simp only [fTab, msgOf_same h hi κ hp]

end Reads

end FR.Snd

end

/-! ## From `FRSoundnessTailM` (1 declaration) -/

section

namespace FR.Snd

open RecursionFast FR.Merkle Finset

open scoped NNReal

set_option linter.constructorNameAsVariable false

variable {W₀ : Log → Log → ℕ → K} {c₀ : Log → Log → K}

theorem D2_congrL {R : Type*} [Field R] {b wd : ℕ} {rd : ByteArray → ℕ → R} {ch : Digest → R}
    {c0 : Log → Log → R} {nr : Kind → ℕ} {e : Expr} {T : Log → Log → Array (Array R)}
    {L L' Y : Log} (hT : T L Y = T L' Y) (hc : c0 L Y = c0 L' Y) :
    D2 b wd rd ch c0 nr e T L Y ↔ D2 b wd rd ch c0 nr e T L' Y := by
  unfold D2 Wrong2
  rw [hT, clR2_same (L' := L') (es' := Y) hc (fun _ _ => rfl)]

end FR.Snd

end

/-! ## From `FRSoundnessFront` (3 declarations) -/

section

namespace FR.Snd

open RecursionFast FR.Merkle Finset

open scoped NNReal

set_option linter.constructorNameAsVariable false

/-- **`P` reads only what lies before position `p`** (entries and the words of earlier caps), on
chains of at least `p` entries. -/
def Reads (p : ℕ) (P : Log → Log → Prop) : Prop :=
  ∀ L es L' es', p ≤ es.length → p ≤ es'.length → Same L es L' es' p → (P L es ↔ P L' es')

variable {p : ℕ} {P Q : Log → Log → Prop}

theorem ext_eq_append (es : Log) : ∀ as : List Digest, ∃ ys, ext es as = es ++ ys := by
  intro as
  induction as using List.reverseRecOn with
  | nil => exact ⟨[], by simp [ext_nil]⟩
  | append_singleton as a ih =>
    obtain ⟨ys, hy⟩ := ih
    exact ⟨ys ++ [(squeezeQ (lastAns (ext es as)), a)], by rw [ext_append, ext1, hy]; simp⟩

/-- **The block class of `nodeKind`** (A.6 per region; the WOTS class is S-E3's
`Layout.wotsKindAt`). -/
def nodeBK (blk : ℕ) : BlockKind :=
  if blk < 2 * Layout.chainN then
    (if blk % Layout.chainN = 0 then .streamStart else .stream)
  else if blk < Layout.wotsBase then
    (if (blk - Layout.stmtBase) % 3 = 0 then .hashA
      else if (blk - Layout.stmtBase) % 3 = 1 then .hashB1 else .hashB2)
  else if blk < Layout.wmBase then Layout.wotsKindAt ((blk - Layout.wotsBase) % Layout.wotsSlot)
  else .free

end FR.Snd

end

/-! ## From `FRSoundnessRows` (22 declarations) -/

section

namespace FR.Snd

open RecursionFast FR.Merkle Finset

open scoped NNReal

set_option linter.constructorNameAsVariable false

theorem capPos_zero : capPos 0 = 2 := by
  simp only [capPos]; rw [phStart, fsStarts_eq]; rfl

section RowSpartan

variable (rows : List Circ.Row) (a nc : ℕ) (on : Kind → Bool)

/-- The rows' `A`, `B`, `C` (`rowMat`). -/
abbrev mA : Fin (2 ^ a) → Fin (2 ^ nc) → F := rowMat Circ.Row.a rows a nc

abbrev mB : Fin (2 ^ a) → Fin (2 ^ nc) → F := rowMat Circ.Row.b rows a nc

abbrev mC : Fin (2 ^ a) → Fin (2 ^ nc) → F := rowMat Circ.Row.c rows a nc

/-- `f⁽⁰⁾` on the cells. -/
noncomputable def zC (L es : Log) : Fin (2 ^ nc) → F := fun y => fF (kindOf es) L es y

/-- **The unit's statement fails**: for a kind it runs on, `f⁽⁰⁾` violates the rows' R1CS. -/
def RowsBad (L es : Log) : Prop :=
  on (kindOf es) = true ∧ ¬ Sat (mA rows a nc) (mB rows a nc) (mC rows a nc) (zC nc L es)

variable (s0 b2 : ℕ)

/-- The zerocheck point: the phase's first `a` F coordinates. -/
def tauS (es : Log) : List F := (List.range a).map (coordAt es s0)

/-- The outer rounds' challenges. -/
def rxs (es : Log) : List F := rchs b2 es a

/-- The end absorb's three values `â, b̂, ĉ`. -/
def vEnd (es : Log) (j : ℕ) : F := readF (msgAt es (b2 + 2 * a)) (16 * j)

/-- The true triple at the outer rounds' point. -/
noncomputable def triT (L es : Log) : F × F × F :=
  (mle (matVec (mA rows a nc) (zC nc L es)) (ptOf a (rxs a b2 es)),
   mle (matVec (mB rows a nc) (zC nc L es)) (ptOf a (rxs a b2 es)),
   mle (matVec (mC rows a nc) (zC nc L es)) (ptOf a (rxs a b2 es)))

/-- **A wrong triple** after the end absorb. -/
noncomputable def EndBad (L es : Log) : Prop :=
  on (kindOf es) = true ∧ b2 + 2 * a < es.length ∧
    (vEnd a b2 es 0, vEnd a b2 es 1, vEnd a b2 es 2) ≠ triT rows a nc b2 L es

/-- **The end check** (`finLr` (ii), `finE` (ii)) fails: the outer claim is not
`eq(τ, r)·(â b̂ + ĉ)`. -/
def RejEnd (L es : Log) : Prop :=
  on (kindOf es) = true ∧ b2 + 2 * a < es.length ∧
    clR b2 (fun _ _ => 0) L es a ≠ eq (ptOf a (tauS a s0 es)) (ptOf a (rxs a b2 es)) *
      (vEnd a b2 es 0 * vEnd a b2 es 1 + vEnd a b2 es 2)

/-- The batching challenge `κ` (at `pk = b2 + 2a + 1`). -/
def kapB (es : Log) : F := fAt es (b2 + 2 * a + 1) 0

/-- The batched claim `â + κ b̂ + κ² ĉ` (`finLr` (iii), `finE` (iii)): the inner rounds' start. -/
def c4 (_L es : Log) : F :=
  vEnd a b2 es 0 + kapB a b2 es * vEnd a b2 es 1 + kapB a b2 es ^ 2 * vEnd a b2 es 2

variable {rows a nc on s0 b2}

theorem tauS_agree {es es' : Log} {p : ℕ} (h : Agree es es' p) (hp : s0 + 1 + (a + 1) / 2 ≤ p) :
    tauS a s0 es = tauS a s0 es' := by
  refine List.map_congr_left fun j hj => ?_
  have hj := List.mem_range.1 hj
  simp only [coordAt, fAt, ansAt]
  rw [h (s0 + 1 + j / 2) (by omega)]

theorem rxs_agree {es es' : Log} {p : ℕ} (h : Agree es es' p) (hp : b2 + 2 * a ≤ p) :
    rxs a b2 es = rxs a b2 es' := by
  unfold rxs; exact rchs_congr (h.mono hp)

theorem vEnd_agree {es es' : Log} {p : ℕ} (h : Agree es es' p) (hp : b2 + 2 * a + 1 ≤ p)
    (j : ℕ) : vEnd a b2 es j = vEnd a b2 es' j := by
  simp only [vEnd, msgAt, h (b2 + 2 * a) (by omega)]

theorem kapB_agree {es es' : Log} {p : ℕ} (h : Agree es es' p) (hp : b2 + 2 * a + 2 ≤ p) :
    kapB a b2 es = kapB a b2 es' := by
  simp only [kapB, fAt, ansAt, h (b2 + 2 * a + 1) (by omega)]

theorem c4_agree {L L' es es' : Log} {p : ℕ} (h : Agree es es' p) (hp : b2 + 2 * a + 2 ≤ p) :
    c4 a b2 L es = c4 a b2 L' es' := by
  simp only [c4, vEnd_agree h (by omega : b2 + 2 * a + 1 ≤ p), kapB_agree h hp]

theorem tbl0_ne_zero (X : Array F) : tbl 0 X ≠ 0 ↔ tbl 0 X 0 ≠ 0 := by
  constructor
  · intro h h0; apply h; funext u
    rw [show u = 0 from Fin.ext (by have := u.isLt; simp at this; omega), h0]; rfl
  · intro h h0; exact h (by rw [h0]; rfl)

theorem mlDoom_full {n : ℕ} (t : Array F) (ht : t.size = 2 ^ n) (l : List F) (hl : n ≤ l.length) :
    mlDoom n t l ↔ mle (tbl n t) (ptOf n (l.take n)) ≠ 0 := by
  have hlen : (l.take n).length = n := by simp; omega
  have hb := bindL_mle (l.take n) t (by rw [hlen, ht])
  rw [pt_eq_ptOf, hlen] at hb
  unfold mlDoom
  rw [hlen, Nat.sub_self, tbl0_ne_zero, hb]

theorem take_ofFn_coord (es : Log) {r : ℕ} (ha : a ≤ r * 2) :
    (List.ofFn fun j : Fin (r * 2) => coordAt es s0 j).take a = tauS a s0 es := by
  apply List.ext_getElem (by simp [tauS]; omega)
  intro j h1 h2
  simp [tauS]

end RowSpartan

end FR.Snd

end

/-! ## From `FRSoundnessFrW0` (12 declarations) -/

section

namespace FR.Snd

open RecursionFast Finset

/-- The Z claim's point (`zSrc`): `ρ₂ … ρ₇`, then Z1's first `m − 13` coordinates. -/
def zPtL (m : ℕ) (es : Log) : List F :=
  (List.ofFn pinnedRho).drop 1 ++ (List.range (m - 13)).map (coordAt es 2)

/-- The Lc claim's point (`lcSrc`): L2's challenges `7 … 13`, then Z3's from `8` to `m − 7`. -/
def lcPtL (m : ℕ) (es : Log) : List F :=
  (List.range 7).map (fun l => rch 69 es (7 + l)) ++
    (List.range (m - 14)).map (fun l => rch 15 es (8 + l))

/-- The Sh claim's point (`shSrc`): S2's position challenges `m − 7 … m − 5`, four zeros, S2's
`m − 14` block challenges. -/
def shPtL (m : ℕ) (es : Log) : List F :=
  (List.range 3).map (fun l => rch 114 es (m - 7 + l)) ++ List.replicate 4 0 ++
    (List.range (m - 14)).map (rch 114 es)

/-- Bit `l` of `y`, `n` coordinates, as F (the cube point). -/
def bitsL (n y : ℕ) : List F := (List.range n).map fun l => if y.testBit l then 1 else 0

/-- The verification key, read off the seed's query (`"FRSEED0" ‖ vk ‖ c ‖ hdr`). -/
def vkL (es : Log) : Digest := bytesAt (entAt es 0).1 7 32

/-- Statement digest `c_σ` (`σ = 0, 1`), read off the statement's absorbed message (bytes
`1 + 32σ …`, `pubH`'s `absOff fStmt (1 + 32σ)`). -/
def stL (es : Log) (σ : ℕ) : Digest := bytesAt (msgAt es 1) (1 + 32 * σ) 32

/-- **The public cells' Horner sum** (`pubH`) on the log's `vk`, `c₁`, `c₂`. -/
def pubHL (es : Log) (kp : F) : F :=
  let vl := dLo (vkL es); let vh := dHi (vkL es)
  1 + kp * (vl + kp * (vh + kp * (dLo (stL es 0) + kp * (dHi (stL es 0) + kp * (vl + kp * (vh +
    kp * (dLo (stL es 1) + kp * dHi (stL es 1))))))))

variable {es es' : Log} {n : ℕ}

theorem fAt_congr (h : Agree es es' n) {p : ℕ} (hp : p < n) (c : ℕ) : fAt es p c = fAt es' p c := by
  simp only [fAt, ansAt, h p hp]

theorem msgAt_congr (h : Agree es es' n) {p : ℕ} (hp : p < n) : msgAt es p = msgAt es' p := by
  simp only [msgAt, h p hp]

theorem Kind.m_le (κ : Kind) : κ.m ≤ 32 := by cases κ <;> decide

theorem rch_congr (h : Agree es es' n) {b l : ℕ} (hl : b + 2 * l + 1 < n) :
    rch b es l = rch b es' l := fAt_congr h hl 0

theorem pubHL_congr (h : Agree es es' 2) : pubHL es = pubHL es' := by
  funext kp
  simp only [pubHL, vkL, stL, h 0 (by norm_num), msgAt_congr h (show 1 < 2 by norm_num)]

end FR.Snd

end

/-! ## From `FRSoundnessFrRS` (1 declaration) -/

section

namespace FR.Snd

open RecursionFast Finset

set_option linter.constructorNameAsVariable false

theorem Phi_zero' (fs : List F) : Phi fs 0 = 0 := frobMap_zero _

end FR.Snd

end

/-! ## From `FRSoundnessFrPend` (2 declarations) -/

section

namespace FR.Snd

open RecursionFast FR.Merkle Finset

set_option linter.constructorNameAsVariable false

/-- `v_β` on the log: L3's eight values (position 97) batched by L3β's `β` (position 98). -/
def vBetaL (es : Log) : F := ∑ i ∈ range 8, fAt es 98 0 ^ i * readF (msgAt es 97) (16 * i)

theorem ptOf_bitsL (u : ℕ) (n : ℕ) (hu : u < 2 ^ n) :
    ptOf n (bitsL n u) = cube (ℓ := n) ⟨u, hu⟩ := by
  funext l
  simp [ptOf, bitsL, cube, List.getD_eq_getElem?_getD, l.isLt]

variable {rows : List Circ.Row}

end FR.Snd

end

/-! ## From `FRSoundnessFrZ` (18 declarations) -/

section

namespace FR.Snd

open RecursionFast FR.Merkle Finset

set_option linter.constructorNameAsVariable false

noncomputable section

/-- **The kinds' block matrices**: `Ak j`, `Bk j` over the `2^14` positions of a block of kind
`j` (A.6's nine kinds in `blockKinds` order, `free` included), the indicators `Ind κ j t` (block
`t` of a `κ` proof is of kind `j`) and the public target bits `Et κ t p`. -/
structure ZLM where
  Ak : Fin 9 → Fin (2 ^ 14) → Fin (2 ^ 14) → F
  Bk : Fin 9 → Fin (2 ^ 14) → Fin (2 ^ 14) → F
  Ind : Kind → Fin 9 → ℕ → F
  Et : Kind → ℕ → Fin (2 ^ 14) → F

/-- A bit of F. -/
abbrev IsBitF (x : F) : Prop := x = 0 ∨ x = 1

/-- Position `σ + 64·(u mod 256)` of a block (6 skip bits low, 8 high bits). -/
def pAt (σ : Fin 64) (u : ℕ) : Fin (2 ^ 14) :=
  ⟨σ.val + 64 * (u % 256), by
    have h1 := σ.isLt; have h2 := Nat.mod_lt u (show 256 > 0 by norm_num); show _ < 16384; omega⟩

variable (M : ZLM)

/-- **Z1's point** `r = (ρ₁ … ρ₇, Z1's first m − 13 coordinates)` (`relZ`'s `rr`). -/
def zrL (es : Log) : List F :=
  List.ofFn pinnedRho ++ (List.range ((kindOf es).m - 13)).map (coordAt es 2)

/-- `λ` (position 14). -/
def lamL (es : Log) : F := fAt es 14 0

/-- Z2's message: `P^z` on `Λ` (64 values), `P^{ab}` on `Λ₀ … Λ₆₂` (63). -/
def pzL (es : Log) : Fin 64 → F := fun k => readF (msgAt es 13) (16 * k.val)

def pabL (es : Log) : Fin 63 → F := fun k => readF (msgAt es 13) (16 * (64 + k.val))

/-- **The c-claim** `P^z*(λ)` (`lagrangeS`'s second value; `finZ` binds it to RS claim 1). -/
def pzStar (es : Log) : F := interpolateAt lNode (pzL es) (lamL es)

/-- Zend's message: `â` (offset 0), `b̂` (16). -/
def vZ (es : Log) (j : ℕ) : F := readF (msgAt es 67) (16 * j)

/-- Z3's challenges `r′`. -/
def rZ (es : Log) : List F := rchs 15 es (mm 6 (kindOf es))

end

theorem m13_le (κ : Kind) : κ.m - 13 ≤ 19 := by cases κ <;> decide

section Reads

variable {M} {L es L' es' : Log} {p : ℕ}

theorem zrL_agree (h : Agree es es' 13) : zrL es = zrL es' := by
  have hk : kindOf es = kindOf es' := kindOf_congr (h.mono (by norm_num))
  have hm := m13_le (kindOf es)
  unfold zrL
  rw [← hk]
  refine congrArg _ (List.map_congr_left fun j hj => ?_)
  simp only [List.mem_range] at hj
  unfold coordAt
  exact fAt_congr h (by omega) _

end Reads

theorem sum_bitF {ι : Type*} (s : Finset ι) (f : ι → F) (h : ∀ i ∈ s, IsBitF (f i)) :
    IsBitF (∑ i ∈ s, f i) :=
  Finset.sum_induction f IsBitF (fun _ _ ha hb => isBit_add ha hb) (Or.inl rfl) h

variable {M}

/-- **The pinned coordinates lose nothing** (`pinned_sound`): a nonzero bit table on `7 + k`
variables has, after fixing the low 7 at `ρ`, a nonzero table `t` on `k` variables whose extension
is the table's at `(ρ, ·)`. -/
theorem pinned_table {ℓ k : ℕ} (hℓ : ℓ = 7 + k) (f : Fin (2 ^ ℓ) → F) (hbit : ∀ u, IsBitF (f u))
    (hf : f ≠ 0) :
    ∃ t : Array F, t.size = 2 ^ k ∧ tbl k t ≠ 0 ∧ ∀ cs : List F, cs.length = k →
      mle (tbl k t) (ptOf k cs) = mle f (ptOf ℓ (List.ofFn pinnedRho ++ cs)) := by
  subst hℓ
  refine ⟨Array.ofFn (fixLow f pinnedRho), by simp, ?_, fun cs hc => ?_⟩
  · rw [tbl_ofFn]; exact pinned_sound pinned_rank f hbit hf
  rw [tbl_ofFn, ← mle_fixLow]
  congr 1
  funext l
  refine Fin.addCases (fun i => ?_) (fun i => ?_) l
  · simp only [Fin.append_left, ptOf, Fin.val_castAdd]
    rw [List.getD_append _ _ _ _ (by simp), List.getD_eq_getElem _ _ (by simp), List.getElem_ofFn]
  · simp only [Fin.append_right, ptOf, Fin.val_natAdd]
    rw [List.getD_append_right _ _ _ _ (by simp)]
    simp

section Reads2

variable {L es L' es' X : Log} {p : ℕ}

theorem z2_agree14 (h : Agree es es' 14) :
    kindOf es = kindOf es' ∧ zrL es = zrL es' ∧ pzL es = pzL es' ∧ pabL es = pabL es' := by
  refine ⟨kindOf_congr (h.mono (by norm_num)), zrL_agree (h.mono (by norm_num)), ?_, ?_⟩ <;>
  · funext k; simp only [pzL, pabL, msgAt_congr h (show 13 < 14 by norm_num)]

theorem z2_agree (h : Agree es es' 15) :
    kindOf es = kindOf es' ∧ zrL es = zrL es' ∧ lamL es = lamL es' ∧ pzL es = pzL es' ∧
      pabL es = pabL es' := by
  obtain ⟨h1, h2, h3, h4⟩ := z2_agree14 (h.mono (by norm_num))
  exact ⟨h1, h2, fAt_congr h (by norm_num) 0, h3, h4⟩

theorem pzStar_agree (h : Agree es es' 15) : pzStar es = pzStar es' := by
  obtain ⟨-, -, hl, hp, -⟩ := z2_agree h
  unfold pzStar; rw [hl, hp]

end Reads2

/-- `single_F_le` for any decidability instance of the escape predicate. -/
theorem single_F_le' (P : Digest → Prop) [DecidablePred P] (S : Finset F) {s : ℕ}
    (hS : S.card ≤ s) (h : ∀ a, P a → chF a 0 ∈ S) : (univ.filter P).card ≤ s * 2 ^ 128 := by
  refine le_trans (card_le_card (t := univ.filter fun a : Digest => chF a 0 ∈ S) fun a ha => ?_) ?_
  · simp only [mem_filter, mem_univ, true_and] at ha ⊢; exact h a ha
  · rw [card_chF_fiber]; exact Nat.mul_le_mul_right _ hS

end FR.Snd

end

/-! ## From `FRSoundnessFrB` (5 declarations) -/

section

namespace FR.Snd

open RecursionFast Finset

set_option linter.constructorNameAsVariable false

/-- The public values on the log (`Node.pubVals` of the seed's `vk` and the statement's digests). -/
def pubL (es : Log) : List F := Node.pubVals (vkL es) (stL es 0) (stL es 1)

/-- **The public cells hold** on `f⁽⁰⁾` (a node; `Node.PubCells`). -/
def PubOK (κ : Kind) (L es : Log) : Prop :=
  κ.isNode = true → Node.PubCells (fF κ L es) (vkL es) (stL es 0) (stL es 1)

/-- The public cells' Horner sum is the batch of `pubL`. -/
theorem pubHL_eq (es : Log) (kp : F) :
    pubHL es kp = ∑ k ∈ range 9, kp ^ k * (pubL es).getD k 0 := by
  simp only [pubHL, pubL, Node.pubVals, Node.halves, Finset.sum_range_succ, Finset.sum_range_zero]
  simp only [List.cons_append, List.nil_append, List.getD_cons_zero, List.getD_cons_succ]
  change _ = _ + kp ^ 1 * dLo _ + kp ^ 2 * dHi _ + kp ^ 3 * dLo _ + kp ^ 4 * dHi _ +
    kp ^ 5 * dLo _ + kp ^ 6 * dHi _ + kp ^ 7 * dLo _ + kp ^ 8 * dHi _
  ring

theorem listGetD_map_lt {l : List ℕ} {f : ℕ → F} {k : ℕ} (hk : k < l.length) :
    (l.map f).getD k 0 = f (l.getD k 0) := by
  rw [List.getD_eq_getElem _ _ (by simpa using hk), List.getElem_map, List.getD_eq_getElem _ _ hk]

open Classical in
/-- A batch of `k + 1` terms by the answer's first F coordinate: if some term is false, at most
`k·2^128` answers make the batch true (`batch_pow_bad_le`, `card_chF_fiber`). -/
theorem batch_count {k : ℕ} (P : Digest → Prop) [DecidablePred P] (v t : Fin (k + 1) → F)
    (hvt : v ≠ t) (h : ∀ a, P a → ∑ i, chF a 0 ^ i.val * v i = ∑ i, chF a 0 ^ i.val * t i) :
    (univ.filter P).card ≤ k * 2 ^ 128 := by
  refine le_trans (card_le_card (t := univ.filter fun a : Digest => chF a 0 ∈
    univ.filter fun c : F => ∑ i, c ^ i.val * v i = ∑ i, c ^ i.val * t i) fun a ha => ?_) ?_
  · simp only [mem_filter, mem_univ, true_and] at ha ⊢; exact h a ha
  · rw [card_chF_fiber]; exact Nat.mul_le_mul_right _ (batch_pow_bad_le hvt)

end FR.Snd

end

/-! ## From `FRSoundnessFrE` (6 declarations) -/

section

namespace FR.Snd

open RecursionFast FR.Merkle Finset

set_option linter.constructorNameAsVariable false

/-- Counting under an implication, the decidability instances taken from the context (so that
two classical `filter`s with different instance terms compare without unfolding them). -/
theorem card_filter_imp {P Q : Digest → Prop} {iP : DecidablePred P} {iQ : DecidablePred Q}
    (h : ∀ d, P d → Q d) : (@filter _ P iP univ).card ≤ (@filter _ Q iQ univ).card := by
  refine card_le_card fun a ha => ?_
  simp only [mem_filter, mem_univ, true_and] at ha ⊢; exact h a ha

/-- A row Spartan's inner weight at `(r_x, ρ)` (`innerTables`' first table). -/
noncomputable def wInn {a nc : ℕ} (A B C : Fin (2 ^ a) → Fin (2 ^ nc) → F) (rx : Fin a → F) (ρ : F)
    (y : Fin (2 ^ nc)) : F :=
  matMle A rx (cube y) + ρ * matMle B rx (cube y) + ρ ^ 2 * matMle C rx (cube y)

section Inner

variable (rows : List Circ.Row)

variable {rows}

/-- **Four claims batched by one challenge** (`batch_count` at degree 3, over abstract values so
that no concrete claim is ever unfolded by the kernel). -/
theorem batch_count4 (P : Digest → Prop) [DecidablePred P] {v0 v1 v2 v3 t0 t1 t2 t3 : F}
    (hvt : v0 ≠ t0 ∨ v1 ≠ t1 ∨ v2 ≠ t2 ∨ v3 ≠ t3)
    (h : ∀ a, P a → v0 + chF a 0 * v1 + chF a 0 ^ 2 * v2 + chF a 0 ^ 3 * v3 =
      t0 + chF a 0 * t1 + chF a 0 ^ 2 * t2 + chF a 0 ^ 3 * t3) :
    (univ.filter P).card ≤ 3 * 2 ^ 128 := by
  refine batch_count (k := 3) P ![v0, v1, v2, v3] ![t0, t1, t2, t3] ?_ fun a ha => ?_
  · intro he
    rcases hvt with h0 | h0 | h0 | h0
    · exact h0 (by simpa using congrFun he 0)
    · exact h0 (by simpa using congrFun he 1)
    · exact h0 (by simpa using congrFun he 2)
    · exact h0 (by simpa using congrFun he 3)
  · have := h a ha
    simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.val_zero, Fin.val_succ,
      Matrix.cons_val_zero, Matrix.cons_val_succ, pow_zero, one_mul, add_zero]
    linear_combination this

theorem innerExpr_eval2 {R : Type*} [CommRing R] (v : ℕ → R) : innerExpr.eval v = v 0 * v 1 := rfl

theorem arrGetD_pair0 {α : Type*} (a b d : α) : (#[a, b] : Array α).getD 0 d = a := rfl

theorem arrGetD_pair1 {α : Type*} (a b d : α) : (#[a, b] : Array α).getD 1 d = b := rfl

end Inner

end FR.Snd

end

/-! ## From `FRSoundnessFrL` (17 declarations) -/

section

namespace FR.Snd

open RecursionFast FR.Merkle Finset

set_option linter.constructorNameAsVariable false

noncomputable section

theorem ptOf_split {a b : ℕ} (rs : List F) :
    ptOf (a + b) rs = Fin.append (ptOf a rs) (ptOf b (rs.drop a)) := by
  funext l
  refine Fin.addCases (fun i => ?_) (fun i => ?_) l
  · simp only [Fin.append_left, ptOf, Fin.val_castAdd]
  · simp only [Fin.append_right, ptOf, Fin.val_natAdd, List.getD_eq_getElem?_getD,
      List.getElem?_drop]

theorem pAt_join {q : ℕ} (σ : Fin 64) (h : Fin (2 ^ 8)) (t : Fin (2 ^ q)) :
    pAt σ (join h t).val = join (a := 6) (b := 8) σ h := by
  apply Fin.ext
  simp only [pAt, join]
  have := h.isLt
  omega

theorem div_join {q : ℕ} (h : Fin (2 ^ 8)) (t : Fin (2 ^ q)) : (join h t).val / 256 = t.val := by
  simp only [join]; have := h.isLt; omega

theorem aStar_bridge {ℓ q : ℕ} (hℓ : ℓ = 8 + q) (A : Fin 9 → Fin (2 ^ 14) → Fin (2 ^ 14) → F) (Ind : Fin 9 → ℕ → F)
    (z : ℕ → F) (l : F) (rs : List F) :
    mle (fun u : Fin (2 ^ ℓ) => (skipExt fun σ => ∑ j : Fin 9, Ind j (u.val / 256) *
        ∑ k, A j (pAt σ u.val) k * z (2 ^ 14 * (u.val / 256) + k.val)).eval l) (ptOf ℓ rs) =
      linAK A (fun j t => Ind j t.val) (rowW (p := 8) l (ptOf 8 rs)) (ptOf q (rs.drop 8))
        (fun y : Fin (2 ^ (14 + q)) => z y.val) := by
  subst hℓ
  have ev_sum : ∀ (c : Fin 9 → F) (g : Fin 9 → Fin 64 → F),
      (skipExt fun σ => ∑ j, c j * g j σ).eval l = ∑ j, c j * (skipExt (g j)).eval l := by
    intro c g
    simp only [skipExt_eval, Finset.mul_sum]
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring
  have hR : ∀ T : Fin (2 ^ 14) → F, ∑ k, rowW (p := 8) l (ptOf 8 rs) k * T k =
      ∑ h : Fin (2 ^ 8), eq (ptOf 8 rs) (cube h) *
        (skipExt fun i => T (join (a := 6) (b := 8) i h)).eval l := fun T => rowW_eq (p := 8) l _ T
  rw [ptOf_split, mle_split]
  unfold linAK
  simp only [div_join, pAt_join, mle, ev_sum]
  simp only [hR]
  simp only [join, Fin.val_mk, Finset.mul_sum]
  rw [Finset.sum_comm (s := (univ : Finset (Fin (2 ^ 8)))) (t := (univ : Finset (Fin (2 ^ q))))]
  refine Finset.sum_congr rfl fun t _ => ?_
  rw [Finset.sum_comm (s := (univ : Finset (Fin (2 ^ 8)))) (t := (univ : Finset (Fin 9)))]
  refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun h _ => ?_
  ring

variable (M : ZLM)

/-- `α` (position 68), the row point's 8 high bits and the block point (Z3's `r′`). -/
def alL (es : Log) : F := fAt es 68 0

/-- L2's initial claim `â + α b̂` (`finLc` (i)). -/
def c0L (es : Log) : F := vZ es 0 + alL es * vZ es 1

/-- **L2's round checks fail** (round 0's is `finLc` (i), the others the rounds' `assertEq`). -/
def RejL2 (L es : Log) : Prop :=
  ∃ l < 14, 69 + 2 * l < es.length ∧ ¬ Chk2 69 16 readF (fun d => chF d 0) (fun _ es => c0L es) L es l

/-- L3's eight values. -/
def vL (es : Log) (i : ℕ) : F := readF (msgAt es 97) (16 * i)

/-- L2's challenges `r_k`. -/
def rkL (es : Log) : List F := rchs 69 es 14

section Reads

variable {M} {L es L' es' X : Log} {p : ℕ}

theorem rZ_agree (h : Agree es es' 67) : rZ es = rZ es' := by
  have hk : kindOf es = kindOf es' := kindOf_congr (h.mono (by norm_num))
  unfold rZ rchs; rw [hk]
  refine List.map_congr_left fun j hj => ?_
  have := Kind.m_le (kindOf es'); simp only [List.mem_range, mm] at hj
  exact rch_congr h (by omega)

theorem lin_agree (h : Agree es es' 69) :
    kindOf es = kindOf es' ∧ lamL es = lamL es' ∧ rZ es = rZ es' ∧ alL es = alL es' ∧
      vZ es 0 = vZ es' 0 ∧ vZ es 1 = vZ es' 1 := by
  refine ⟨kindOf_congr (h.mono (by norm_num)), fAt_congr h (by norm_num) 0,
    rZ_agree (h.mono (by norm_num)), fAt_congr h (by norm_num) 0, ?_, ?_⟩ <;>
  simp only [vZ, msgAt_congr h (show 67 < 69 by norm_num)]

theorem c0L_agree (h : Agree es es' 69) : c0L es = c0L es' := by
  obtain ⟨-, -, -, ha, h0, h1⟩ := lin_agree h
  unfold c0L; rw [ha, h0, h1]

end Reads

variable {M}

theorem chk_of_not_rejL2 {L es : Log} (hr : ¬ RejL2 L es) (j : ℕ)
    (hj : es.length = 69 + 2 * j + 1) (hjn : j < 14) :
    Chk2 69 16 readF (fun d => chF d 0) (fun _ es => c0L es) L es j := by
  by_contra hc; exact hr ⟨j, hjn, by omega, hc⟩

theorem clR2L_log (L L' X : Log) (l : ℕ) :
    clR2 69 16 readF (fun d => chF d 0) (fun _ es => c0L es) L X l =
      clR2 69 16 readF (fun d => chF d 0) (fun _ es => c0L es) L' X l := by
  cases l <;> rfl

theorem chkL_agree {L es es' : Log} {l : ℕ} (h : Agree es es' (69 + 2 * l + 1)) :
    Chk2 69 16 readF (fun d => chF d 0) (fun _ es => c0L es) L es l ↔
      Chk2 69 16 readF (fun d => chF d 0) (fun _ es => c0L es) L es' l := by
  have hg : g2At 69 16 readF es l = g2At 69 16 readF es' l := by
    simp only [g2At, msgAt, h (69 + 2 * l) (by omega)]
  have hc := clR2_congr (b := 69) (wd := 16) (rd := readF) (ch := fun d => chF d 0)
    (c0 := fun _ es => c0L es) (L := L) (c0L_agree (h.mono (by omega))) (l := l) (h.mono (by omega))
  simp only [Chk2, hg, hc]

theorem rejL2_mono {L es : Log} (x : ByteArray × Digest) (h : RejL2 L es) : RejL2 L (es ++ [x]) := by
  obtain ⟨j, hj, hlt, hc⟩ := h
  exact ⟨j, hj, by simp; omega,
    fun h' => hc ((chkL_agree (agree_append es [x] (by omega))).mp h')⟩

theorem mle_zfoldK_zero {q : ℕ} {Ind : Fin 9 → Fin (2 ^ q) → F} {j : Fin 9} (hI : ∀ t, Ind j t = 0)
    (rb : Fin q → F) (z : Fin (2 ^ (14 + q)) → F) (r : Fin 14 → F) :
    mle (zfoldK Ind rb z j) r = 0 := by
  simp [mle, zfoldK, hI]

end

end FR.Snd

end

/-! ## From `FRSoundnessFrW0V` (10 declarations) -/

section

namespace FR.Snd

open RecursionFast Finset FR.Impl

theorem iota_Phi (fs : List F) (a : F) : algebraMap F K (Phi fs a) =
    ∑ k ∈ range (2 ^ fs.length), algebraMap F K ((phiTable fs).getD k 0) *
      algebraMap F K a ^ 2 ^ k := by
  rw [Phi_eq_table]; simp only [map_sum, map_mul, map_pow]

theorem iota_eqPts_bits {n : ℕ} {p : List F} (hp : p.length = n) (y : Fin (2 ^ n)) :
    algebraMap F K (eqPts p (bitsL n y)) = eq (ptOf n (p.map (algebraMap F K))) (cube y) := by
  rw [eqPts_eq _ _ hp (by simp [bitsL]), ptOf_bitsL y.val n y.isLt]
  simp only [eq, map_prod, map_add, map_mul, map_sub, map_one, cube, apply_ite (algebraMap F K),
    map_zero, ptOf, List.getD_eq_getElem?_getD, List.getElem?_map]
  refine prod_congr rfl fun l _ => ?_
  cases h : p[l.val]? <;> simp

/-- `mle(eq(q, ·)^(2^k))(ρ) = eq(q^(2^k), ρ)`. -/
theorem mle_eq_pow {n : ℕ} (q ρ : Fin n → K) (k : ℕ) :
    mle (fun y : Fin (2 ^ n) => eq q (cube y) ^ 2 ^ k) ρ = eq (fun l => q l ^ 2 ^ k) ρ := by
  simp only [mle, eq_frob]
  rw [eq_swap _ ρ, ← eq_mle ρ]
  exact sum_congr rfl fun u _ => by rw [eq_swap (cube u)]

/-- **A plain claim's weight**: the extension of `y ↦ ι Φ(eq(p, y))` is `Σ_k c_k eq(p^(2^k), ρ)`. -/
theorem mle_plain (fs : List F) {n : ℕ} {p : List F} (hp : p.length = n) (ρ : Fin n → K) :
    mle (fun y : Fin (2 ^ n) => algebraMap F K (Phi fs (eqPts p (bitsL n y)))) ρ =
      ∑ k ∈ range (2 ^ fs.length), algebraMap F K ((phiTable fs).getD k 0) *
        eq (fun l => ptOf n (p.map (algebraMap F K)) l ^ 2 ^ k) ρ := by
  simp only [iota_Phi, iota_eqPts_bits hp]
  rw [mle_sum]
  exact sum_congr rfl fun k _ => by rw [mle_eq_pow]

theorem ptOfK_split {a b : ℕ} (rs : List K) :
    ptOf (a + b) rs = Fin.append (ptOf a rs) (ptOf b (rs.drop a)) := by
  funext l
  refine Fin.addCases (fun i => ?_) (fun i => ?_) l
  · simp only [Fin.append_left, ptOf, Fin.val_castAdd]
  · simp only [Fin.append_right, ptOf, Fin.val_natAdd, List.getD_eq_getElem?_getD,
      List.getElem?_drop]

theorem ptOf_sq (n k : ℕ) (q : List K) :
    (fun l => ptOf n q l ^ 2 ^ k) = ptOf n (q.map (sqIter k)) := by
  funext l
  simp only [ptOf, List.getD_eq_getElem?_getD, List.getElem?_map]
  cases q[l.val]? <;> simp [sqIter_eq]

/-- **A plain claim's weight**, in `rsWeightS`'s form. -/
theorem termP (fs : List F) {n : ℕ} {p : List F} (hp : p.length = n) (ρ : List K)
    (hρ : ρ.length = n) :
    mle (fun y : Fin (2 ^ n) => algebraMap F K (Phi fs (eqPts p (bitsL n y)))) (ptOf n ρ) =
      ∑ k ∈ range (2 ^ fs.length), K.ofF ((phiTable fs).getD k 0) *
        eqPts ((p.map (algebraMap F K)).map (sqIter k)) ρ := by
  rw [mle_plain fs hp]
  refine sum_congr rfl fun k _ => ?_
  rw [ptOf_sq, eqPts_eq (ℓ := n) _ _ (by simp [hp]) hρ]
  rfl

theorem eqPts_append (a b c d : List K) (h : a.length = c.length) :
    eqPts (a ++ b) (c ++ d) = eqPts a c * eqPts b d := by
  simp only [eqPts, List.zipWith_append h, List.prod_append]

/-- At `β = 1` claim 2's weight is the plain one (`kwS_one`; `|ρ| ≥ 23`). -/
theorem kwSL_one (q ρ : List K) (hq : q.length = ρ.length) (h : 23 ≤ ρ.length) :
    kwSL 1 q ρ = eqPts q ρ := by
  unfold kwSL
  rw [KW.kwS_one (by omega), ← eqPts_eq _ _ (by simp [hq]) (by simp), ← eqPts_append _ _ _ _
    (by simp [hq]), List.take_append_drop, List.take_append_drop]

theorem mle_add' {n : ℕ} (f g : Fin (2 ^ n) → K) (r : Fin n → K) :
    mle (fun u => f u + g u) r = mle f r + mle g r := mle_add f g r

end FR.Snd

end

/-! ## From `FRSoundnessFrRS0` (5 declarations) -/

section

namespace FR.Snd

open RecursionFast Finset

set_option linter.constructorNameAsVariable false

/-- **The inner weights** `c_{j,i}` (`rsW`'s values): Z's `eqZ(λ, ρ₁)` (λ is Z2's challenge,
position 14), `eq` at L2's challenges 0–6 (Lc), at S2's challenges `m − 14 … m − 8` (Sh), and
the packing basis for E4's `f̂(r′)`. -/
def cwF (lam : F) (xL xS : List F) (j i : ℕ) : F :=
  match j with
  | 0 => (Impl.eqZS lam (pinnedRho 0)).getD i 0
  | 1 => (eqTab xL.toArray).getD i 0
  | 2 => (eqTab xS.toArray).getD i 0
  | _ => bb i

/-- Lc's low point (L2's challenges 0–6) and Sh's (S2's challenges `m − 14 … m − 8`). -/
def xLL (es : Log) : List F := (List.range 7).map (rch 69 es)

def xSL (κ : Kind) (es : Log) : List F := (List.range 7).map fun l => rch 114 es (κ.m - 14 + l)

/-- `cwF` at the log's values. -/
def cwL (κ : Kind) (es : Log) (j i : ℕ) : F := cwF (fAt es 14 0) (xLL es) (xSL κ es) j i

section Reads

variable {L es L' es' : Log} {p : ℕ}

theorem fF_same (h : Same L es L' es' p) (hp : 3 ≤ p) (κ : Kind) : fF κ L es = fF κ L' es' := by
  funext y
  simp only [fF, fTab_same h (i := 0) (by norm_num) κ (by rw [capPos_zero]; omega)]

variable {ok : Kind → Log → ℕ → F → Prop}

end Reads

end FR.Snd

end

end G6_FRSoundnessCoreRows

section G6_FRSoundnessCoreFront

-- New for `flock-recursive` (BLUEPRINT §10 changes 27 (B) step 3; stage RET-2): the declarations of
-- the 3.x soundness modules that the revision 4.1 certificate reads, moved here verbatim (same
-- names, statements and proofs) from `FRSoundnessFrSh` (36), `FRSoundnessFrS` (11),
-- `FRSoundnessFrZM` (23), `FRSoundnessFrBind` (1). Content: the front's Sh/S/ZM/Bind pieces
-- (`slotT`, `coS`, `ksL`, `thL`, `kMat`, `targetS_range`, …). The 3.x modules import this one.

/-! ## From `FRSoundnessFrSh` (36 declarations) -/

section

namespace FR.Snd

open RecursionFast Finset FR.Impl FR.NodeT FR.NodeI

set_option linter.constructorNameAsVariable false

theorem sum_range_mul_split (n : ℕ) (g : ℕ → F) : ∀ m : ℕ,
    ∑ i ∈ range (n * m), g i = ∑ q ∈ range m, ∑ y ∈ range n, g (y + n * q)
  | 0 => by simp
  | m + 1 => by
    rw [Nat.mul_succ, sum_range_add, sum_range_mul_split n g m, sum_range_succ]
    exact congrArg _ (sum_congr rfl fun y _ => by rw [add_comm])

theorem sum_range_pow_add (a b : ℕ) (g : ℕ → F) :
    ∑ i ∈ range (2 ^ (a + b)), g i = ∑ q ∈ range (2 ^ b), ∑ y ∈ range (2 ^ a), g (y + 2 ^ a * q) :=
  by rw [pow_add, sum_range_mul_split]

theorem eq_cube_eqAtR {n : ℕ} (r : Fin n → F) (u : Fin (2 ^ n)) : eq r (cube u) = eqAtR r u.val :=
  eq_cube r u

theorem sum_eqAtR_one {n : ℕ} (r : Fin n → F) : ∑ u ∈ range (2 ^ n), eqAtR r u = 1 := by
  rw [← eq_sum_one r, ← Fin.sum_univ_eq_sum_range (fun u => eqAtR r u)]
  exact sum_congr rfl fun u _ => (eq_cube_eqAtR r u).symm

theorem sum_eqAtR_mul {n : ℕ} (a b : Fin n → F) :
    ∑ u ∈ range (2 ^ n), eqAtR a u * eqAtR b u = eq a b := by
  rw [← eq_mle a b, ← Fin.sum_univ_eq_sum_range (fun u => eqAtR a u * eqAtR b u)]
  refine sum_congr rfl fun u _ => ?_
  rw [eq_cube_eqAtR, eq_swap, eq_cube_eqAtR]

theorem ptOf_drop {a : ℕ} (rs : List F) (l : ℕ) : (rs.drop a).getD l 0 = rs.getD (a + l) 0 := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_drop]

/-- **A table's extension at a split point**: the low `a` coordinates (`rs`'s first `a`) weigh
the index's low part `y`, the next `b` its high part `q`. -/
theorem mle_ofFn_split (a b : ℕ) (g : ℕ → F) (rs : List F) :
    mle (tbl (a + b) (Array.ofFn (n := 2 ^ (a + b)) fun i => g i.val)) (ptOf (a + b) rs) =
      ∑ q ∈ range (2 ^ b), ∑ y ∈ range (2 ^ a),
        eqAtR (ptOf a rs) y * eqAtR (ptOf b (rs.drop a)) q * g (y + 2 ^ a * q) := by
  rw [tbl_ofFn, mle]
  rw [show (∑ u : Fin (2 ^ (a + b)), eq (ptOf (a + b) rs) (cube u) * g u.val) =
      ∑ u : Fin (2 ^ (a + b)), (fun i => eqAtR (ptOf (a + b) rs) i * g i) u.val from
    sum_congr rfl fun u _ => by rw [eq_cube_eqAtR]]
  refine (Fin.sum_univ_eq_sum_range (fun i => eqAtR (ptOf (a + b) rs) i * g i) _).trans ?_
  rw [sum_range_pow_add]
  refine sum_congr rfl fun q hq => sum_congr rfl fun y hy => ?_
  have hy' := mem_range.1 hy
  have hq' := mem_range.1 hq
  have h1 : (y + 2 ^ a * q) % 2 ^ a = y := by
    rw [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hy']
  have h2 : (y + 2 ^ a * q) / 2 ^ a % 2 ^ b = q := by
    rw [Nat.add_mul_div_left _ _ (Nat.two_pow_pos a), Nat.div_eq_of_lt hy', zero_add,
      Nat.mod_eq_of_lt hq']
  have hl : loP (ptOf (a + b) rs) = ptOf a rs := rfl
  have hh : hiP (ptOf (a + b) rs) = ptOf b (rs.drop a) := by
    funext l; simp only [hiP, ptOf, ptOf_drop]; rfl
  rw [eqAtR_split, h1, h2, hl, hh]

theorem sum_range_ite_lt {n L : ℕ} (h : L ≤ n) (g : ℕ → F) :
    ∑ x ∈ range n, (if x < L then g x else 0) = ∑ x ∈ range L, g x := by
  rw [← sum_range_add_sum_Ico _ h, sum_eq_zero (s := Ico L n) fun x hx => by
    simp [(mem_Ico.1 hx).1], add_zero]
  exact sum_congr rfl fun x hx => by simp [mem_range.1 hx]

/-- **A slot's weight** at position `q`: `Σ_{σ<256} eq(θ, σ) [q = b + σ]` (A.8 `slotW`'s table). -/
def slotT (θ : Fin 10 → F) (b q : ℕ) : F := ∑ σ ∈ range 256, eqAtR θ σ * if q = b + σ then 1 else 0

theorem sum_slotT (θ : Fin 10 → F) {b : ℕ} (hb : b + 256 ≤ 2 ^ 10) (g : ℕ → F) :
    ∑ q ∈ range (2 ^ 10), slotT θ b q * g q = ∑ σ ∈ range 256, eqAtR θ σ * g (b + σ) := by
  simp only [slotT, sum_mul, mul_assoc, ite_mul, one_mul, zero_mul]
  rw [sum_comm]
  refine sum_congr rfl fun σ hσ => ?_
  rw [← mul_sum, sum_ite_eq', if_pos (mem_range.2 (by have := mem_range.1 hσ; omega))]

/-- The digest bits read through `eq(θ, ·)`: `Σ_{σ<256} eq(θ, σ) d(σ)`. -/
def thS (θ : Fin 10 → F) (d : ℕ → F) : F := ∑ σ ∈ range 256, eqAtR θ σ * d σ

/-- **A leaf's In-block weight** `shift(τ, y) + κ_s eq(0, y)`: block `y`'s input is block
`y − 1`'s output, block `0`'s is the start. -/
def shL {nb : ℕ} (τ : Fin nb → F) (κ : F) (y : ℕ) : F :=
  (if 1 ≤ y then eqAtR τ (y - 1) else 0) + κ * if y = 0 then 1 else 0

/-- **A leaf's S2 weight** (A.9 `finSh`, a leaf): `h_out` (slot `256 + σ`) out at `eq(τ, y)`,
`d` (slot `520 + σ`) in at `shL`. -/
def wLeaf {nb : ℕ} (τ : Fin nb → F) (θ : Fin 10 → F) (κ : F) (y q : ℕ) : F :=
  eqAtR τ y * slotT θ 256 q + shL τ κ y * slotT θ 520 q

/-- **The residual tables** `R_j(u, q)` (`j < J`) batched by `κ_s^j` at `(τ, θ)`. -/
def resSum (nb J : ℕ) (R : ℕ → ℕ → ℕ → F) {nb' : ℕ} (τ : Fin nb' → F) (θ : Fin 10 → F) (κ : F) :
    F :=
  ∑ j ∈ range J, κ ^ j * ∑ q ∈ range (2 ^ 10), ∑ u ∈ range (2 ^ nb),
    eqAtR τ u * eqAtR θ q * R j u q

/-- **A leaf's S truth** (A.10 S1, `FRShift.ChainLinks` slot by slot): block `y + 1`'s `d` is block
`y`'s `h_out`, block `0`'s `d` is the start `s`, the last block's `h_out` is `h`. -/
def ShHoldsL (nb : ℕ) (z : ℕ → ℕ → F) (sb hb : ℕ → F) : Prop :=
  (∀ y, y + 1 < 2 ^ nb → ∀ σ < 256, z (y + 1) (520 + σ) = z y (256 + σ)) ∧
    (∀ σ < 256, z 0 (520 + σ) = sb σ) ∧ ∀ σ < 256, z (2 ^ nb - 1) (256 + σ) = hb σ

theorem fam_src_lt {f t : ℕ} (ht : t < (fam f).n) : (fam f).src t < Layout.wotsSlot := by
  have hw : Layout.wotsSlot = 498 := rfl
  rcases f with _ | _ | _ | _ | _ | _ | _ | _ | f <;> simp only [fam, id] at ht ⊢ <;> omega

theorem fam_src_inj {f t t' : ℕ} (h : (fam f).src t = (fam f).src t') : t = t' := by
  rcases f with _ | _ | _ | _ | _ | _ | _ | _ | f <;> simp only [fam, id] at h <;> omega

theorem sum_slot_eqAtR (θ rp : Fin 10 → F) {b : ℕ} (hb : b + 256 ≤ 2 ^ 10) :
    ∑ q ∈ range (2 ^ 10), eqAtR rp q * slotT θ b q = ∑ σ ∈ range 256, eqAtR θ σ * eqAtR rp (b + σ) := by
  rw [← sum_slotT θ hb]; exact sum_congr rfl fun q _ => mul_comm _ _

theorem slotWS_eq (s : ℕ) (θ rp : Array F) :
    slotWS s θ rp = ∑ σ ∈ range 256, eqAtR (ptA 10 θ) σ * eqAtR (ptA 10 rp) (slotBase s + σ) := rfl

/-- A product weight's extension splits: `Σ_q Σ_y a(y) b(q) A(y) B(q) = (Σ_y a A)(Σ_q b B)`. -/
theorem sum_prod_split (a A : ℕ → F) (b B : ℕ → F) (m n : ℕ) :
    ∑ q ∈ range m, ∑ y ∈ range n, a y * b q * (A y * B q) =
      (∑ y ∈ range n, a y * A y) * ∑ q ∈ range m, b q * B q := by
  rw [mul_comm, sum_mul_sum]
  exact sum_congr rfl fun _ _ => sum_congr rfl fun _ _ => by ring

theorem eqAtR_zero {n : ℕ} (r : Fin n → F) : eqAtR r 0 = ∏ l : Fin n, (1 - r l) := by
  simp only [eqAtR, Nat.zero_testBit, Bool.false_eq_true, if_false]

theorem eq_zero_pt {n : ℕ} (rb : List F) (hrb : rb.length = n) :
    eqPoint (List.replicate n (0 : F)).toArray rb.toArray = eqAtR (ptOf n rb) 0 := by
  rw [eqPoint_eq, List.size_toArray, List.length_replicate, ptA_toArray, ptA_toArray, eqAtR_zero,
    eq]
  refine prod_congr rfl fun l _ => ?_
  simp [ptOf, List.getD_eq_getElem?_getD]

/-- `shiftEqS` on lists of `n` coordinates: `Σ_u eq(τ, u) eq(r, u + 1)` over `u + 1 < 2^n`. -/
theorem shiftEqS_eq {n : ℕ} (τs rb : List F) (hτ : τs.length = n) (hrb : rb.length = n) :
    shiftEqS τs.toArray rb.toArray = ∑ u ∈ range (2 ^ n),
      eqAtR (ptOf n τs) u * if u + 1 < 2 ^ n then eqAtR (ptOf n rb) (u + 1) else 0 := by
  subst hτ
  show ∑ u : Fin (2 ^ τs.length), ∑ v : Fin (2 ^ τs.length), eq (ptOf τs.length τs) (cube u) *
    succT u v * eq (cube v) (ptOf τs.length rb) = _
  simp only [mul_assoc, ← mul_sum]
  have e : ∀ u : Fin (2 ^ τs.length), ∑ v : Fin (2 ^ τs.length),
      succT u v * eq (cube v) (ptOf τs.length rb) =
        if u.val + 1 < 2 ^ τs.length then eqAtR (ptOf τs.length rb) (u.val + 1) else 0 := by
    intro u
    rw [sum_succT]
    split_ifs with h
    · rw [eq_swap, eq_cube_eqAtR]
    · rfl
  simp only [e, eq_cube_eqAtR]
  exact Fin.sum_univ_eq_sum_range (fun u => eqAtR (ptOf τs.length τs) u *
    if u + 1 < 2 ^ τs.length then eqAtR (ptOf τs.length rb) (u + 1) else 0) _

/-- **The leaf's final value** (A.9 `finSh` (ii), a leaf; revision 3.15's padded points): the
weight's extension at `(r_blk, r_pos)` is `w_out + w_in` on the specifications. -/
theorem final_leaf {nb : ℕ} (hnb : nb ≤ 18) (τs rb : List F) (hτ : τs.length = nb)
    (hrb : rb.length = nb) (θ rp : Array F) (κ : F) :
    ∑ q ∈ range (2 ^ 10), ∑ y ∈ range (2 ^ nb),
        eqAtR (ptOf nb rb) y * eqAtR (ptA 10 rp) q * wLeaf (ptOf nb τs) (ptA 10 θ) κ y q =
      eqPoint (τs ++ List.replicate (18 - nb) 0).toArray (rb ++ List.replicate (18 - nb) 0).toArray *
          slotWS 0 θ rp +
        (shiftEqS (τs ++ List.replicate (18 - nb) 0).toArray
            (rb ++ List.replicate (18 - nb) 0).toArray +
          κ * eqPoint (Array.replicate 18 0) (rb ++ List.replicate (18 - nb) 0).toArray) *
          slotWS 1 θ rp := by
  have h18 : Array.replicate 18 (0 : F) =
      (List.replicate nb (0 : F) ++ List.replicate (18 - nb) (0 : F)).toArray := by
    rw [← List.replicate_add, Nat.add_sub_cancel' hnb]; rfl
  rw [eqPoint_pad _ _ _ (by rw [hτ, hrb]), shiftEqS_pad _ _ _ (by rw [hτ, hrb]), h18,
    eqPoint_pad _ _ _ (by rw [List.length_replicate, hrb]), eq_zero_pt rb hrb, shiftEqS_eq τs rb hτ hrb,
    eqPoint_eq, List.size_toArray, hτ, ptA_toArray nb τs, ptA_toArray nb rb, slotWS_eq, slotWS_eq]
  have hN : 2 ^ nb = (2 ^ nb - 1) + 1 := (Nat.sub_add_cancel Nat.one_le_two_pow).symm
  have hsh : ∑ y ∈ range (2 ^ nb), eqAtR (ptOf nb rb) y * shL (ptOf nb τs) κ y =
      ∑ u ∈ range (2 ^ nb), eqAtR (ptOf nb τs) u *
        (if u + 1 < 2 ^ nb then eqAtR (ptOf nb rb) (u + 1) else 0) + κ * eqAtR (ptOf nb rb) 0 := by
    simp only [shL, mul_add, sum_add_distrib, mul_ite, mul_zero, mul_one, sum_ite_eq', mem_range,
      Nat.two_pow_pos, if_true]
    rw [hN, sum_range_succ', sum_range_succ, if_neg (by omega), add_zero, if_neg (by omega),
      add_zero]
    have e : ∀ u ∈ range (2 ^ nb - 1), (if 1 ≤ u + 1 then eqAtR (ptOf nb rb) (u + 1) *
        eqAtR (ptOf nb τs) (u + 1 - 1) else 0) = (if u + 1 < 2 ^ nb - 1 + 1 then
          eqAtR (ptOf nb τs) u * eqAtR (ptOf nb rb) (u + 1) else 0) := fun u hu => by
      have := mem_range.1 hu
      rw [if_pos (by omega), if_pos (by omega), Nat.add_sub_cancel, mul_comm]
    rw [sum_congr rfl e, mul_comm κ]
  simp only [wLeaf, mul_add, sum_add_distrib]
  rw [sum_prod_split, sum_prod_split, sum_slot_eqAtR _ _ (by norm_num),
    sum_slot_eqAtR _ _ (by norm_num), sum_eqAtR_mul, eq_swap, hsh]
  rfl

/-- S1's coordinates that the residual reads: `τ`'s first `nb` (of 18 drawn), then `θ`'s 10
(coordinates 18 … 27). -/
def selC (nb : ℕ) (l : List F) : List F := l.take nb ++ (l.drop 18).take 10

/-- **S1's doom on a coordinate prefix**: up to `κ_s` (coordinate 28), some residual table with the
read coordinates bound is nonzero; from `κ_s` on, the batched residual `Σ_j κ_s^j R̃_j(τ, θ)` is
nonzero. -/
def DoomS (nb J : ℕ) (T : ℕ → Array F) (l : List F) : Prop :=
  if l.length ≤ 28 then ∃ j < J, mlDoom (nb + 10) (T j) (selC nb l)
  else ∑ j ∈ range J, l.getD 28 0 ^ j * mle (tbl (nb + 10) (T j)) (ptOf (nb + 10) (selC nb l)) ≠ 0

/-- The per-coordinate losses: one per read multilinear coordinate, `J − 1` at `κ_s`. -/
def bS (nb J i : ℕ) : ℕ :=
  if i < nb then 1 else if i < 18 then 0 else if i < 28 then 1 else if i = 28 then J - 1 else 0

theorem sum_bS {nb J : ℕ} (hnb : nb ≤ 18) : ∑ i ∈ range 30, bS nb J i = nb + 10 + (J - 1) := by
  have h : ∀ i, bS nb J i = (if i < nb then 1 else 0) + (if 18 ≤ i ∧ i < 28 then 1 else 0) +
      (if i = 28 then J - 1 else 0) := fun i => by
    unfold bS; split_ifs <;> omega
  simp only [h, sum_add_distrib, sum_ite_eq', mem_range, show 28 < 30 by norm_num, if_true]
  rw [sum_boole, sum_boole]
  have e1 : (range 30).filter (· < nb) = range nb := by
    ext x; simp only [mem_filter, mem_range]; omega
  have e2 : ((range 30).filter fun x => 18 ≤ x ∧ x < 28).card = 10 := by decide
  rw [e1, e2, card_range]; simp

theorem selC_lt {nb : ℕ} {l : List F} (hl : l.length < nb) (hnb : nb ≤ 18) (c : F) :
    selC nb (l ++ [c]) = selC nb l ++ [c] := by
  have h1 : (l ++ [c]).drop 18 = [] := List.drop_eq_nil_of_le (by simp; omega)
  have h2 : l.drop 18 = [] := List.drop_eq_nil_of_le (by omega)
  simp [selC, h1, h2, List.take_of_length_le (show l.length ≤ nb by omega),
    List.take_of_length_le (show (l ++ [c]).length ≤ nb by simp; omega)]

theorem selC_mid {nb : ℕ} {l : List F} (h1 : nb ≤ l.length) (h2 : l.length < 18) (c : F) :
    selC nb (l ++ [c]) = selC nb l := by
  have e1 : (l ++ [c]).drop 18 = [] := List.drop_eq_nil_of_le (by simp; omega)
  have e2 : l.drop 18 = [] := List.drop_eq_nil_of_le (by omega)
  simp [selC, e1, e2, List.take_append_of_le_length h1]

theorem selC_th {nb : ℕ} {l : List F} (hnb : nb ≤ 18) (h1 : 18 ≤ l.length) (h2 : l.length < 28)
    (c : F) : selC nb (l ++ [c]) = selC nb l ++ [c] := by
  simp only [selC, List.take_append_of_le_length (show nb ≤ l.length by omega),
    List.drop_append_of_le_length h1, List.append_assoc]
  rw [List.take_of_length_le (l := l.drop 18 ++ [c]) (i := 10) (by simp; omega),
    List.take_of_length_le (l := l.drop 18) (i := 10) (by simp; omega)]

theorem selC_end {nb : ℕ} {l : List F} (hnb : nb ≤ 18) (h1 : 28 ≤ l.length) (c : F) :
    selC nb (l ++ [c]) = selC nb l := by
  simp only [selC, List.take_append_of_le_length (show nb ≤ l.length by omega),
    List.drop_append_of_le_length (show 18 ≤ l.length by omega),
    List.take_append_of_le_length (show 10 ≤ (l.drop 18).length by simp; omega)]

theorem selC_length {nb : ℕ} {l : List F} (hnb : nb ≤ 18) (h : 28 ≤ l.length) :
    (selC nb l).length = nb + 10 := by
  rw [selC, List.length_append, List.length_take, List.length_take, List.length_drop]; omega

theorem getD_snoc_28 {l : List F} (h : l.length = 28) (c : F) : (l ++ [c]).getD 28 0 = c := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_append_right (show l.length ≤ 28 by omega), h]

theorem getD_snoc_lt {l : List F} (h : 28 < l.length) (c : F) :
    (l ++ [c]).getD 28 0 = l.getD 28 0 := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_append_left h]

open Classical in
/-- **S1's per-coordinate loss**: a read multilinear coordinate loses at most one value (some
residual table stays nonzero), an unread one none, `κ_s` at most `J − 1` (a nonzero polynomial of
degree `< J`). -/
theorem doomS_step {nb J : ℕ} (hnb : nb ≤ 18) (hJ : 1 ≤ J) {T : ℕ → Array F}
    (hT : ∀ j, (T j).size = 2 ^ (nb + 10)) (l : List F) (hd : DoomS nb J T l) :
    (univ.filter fun c => ¬ DoomS nb J T (l ++ [c])).card ≤ bS nb J l.length := by
  have hlen : ∀ c, (l ++ [c]).length = l.length + 1 := fun c => by simp
  by_cases hA : l.length ≤ 27
  · have hl : l.length ≤ 28 := by omega
    rw [DoomS, if_pos hl] at hd
    obtain ⟨j₀, hj₀, hm⟩ := hd
    have hsub : ∀ S : List F → List F, (∀ c, selC nb (l ++ [c]) = S [c]) →
        (univ.filter fun c => ¬ DoomS nb J T (l ++ [c])).card ≤
          (univ.filter fun c => ¬ mlDoom (nb + 10) (T j₀) (S [c])).card := fun S hS =>
      card_le_card fun c hc => by
        have hc' := (mem_filter.1 hc).2
        rw [DoomS, if_pos (show (l ++ [c]).length ≤ 28 by rw [hlen]; omega)] at hc'
        refine mem_filter.2 ⟨mem_univ _, fun h => hc' ⟨j₀, hj₀, ?_⟩⟩
        rw [hS c]; exact h
    by_cases h1 : l.length < nb
    · refine (hsub (fun x => selC nb l ++ x) fun c => selC_lt h1 hnb c).trans ?_
      refine (mlDoom_step (hT j₀) _ hm).trans ?_
      simp only [bS, if_pos h1]; split_ifs <;> omega
    by_cases h2 : l.length < 18
    · rw [filter_false_of_mem fun c _ hc => hc (by
        rw [DoomS, if_pos (by rw [hlen]; omega), selC_mid (by omega) h2]; exact ⟨j₀, hj₀, hm⟩)]
      simp
    · refine (hsub (fun x => selC nb l ++ x) fun c => selC_th hnb (by omega) (by omega) c).trans ?_
      refine (mlDoom_step (hT j₀) _ hm).trans ?_
      simp only [bS, if_neg h1, if_neg h2, if_pos (show l.length < 28 by omega)]
      split_ifs <;> omega
  by_cases hB : l.length = 28
  · rw [DoomS, if_pos (by omega)] at hd
    obtain ⟨j₀, hj₀, hm⟩ := hd
    have hsl := selC_length (l := l) hnb (by omega)
    set a : ℕ → F := fun j => mle (tbl (nb + 10) (T j)) (ptOf (nb + 10) (selC nb l))
    have ha : a j₀ ≠ 0 := by
      have := (mlDoom_full (T j₀) (hT j₀) (selC nb l) hsl.ge).1 hm
      rwa [List.take_of_length_le (l := selC nb l) hsl.le] at this
    obtain ⟨k, rfl⟩ : ∃ k, J = k + 1 := ⟨J - 1, by omega⟩
    have hv : (fun i : Fin (k + 1) => a i) ≠ fun _ => 0 := fun he =>
      ha (by simpa using congrFun he ⟨j₀, hj₀⟩)
    refine le_trans (card_le_card fun c hc => ?_) ((batch_pow_bad_le hv).trans ?_)
    · have hc' := (mem_filter.1 hc).2
      rw [DoomS, if_neg (show ¬ (l ++ [c]).length ≤ 28 by rw [hlen]; omega), not_not,
        selC_end (l := l) hnb (by omega), getD_snoc_28 hB] at hc'
      refine mem_filter.2 ⟨mem_univ _, ?_⟩
      rw [Fin.sum_univ_eq_sum_range (fun i => c ^ i * a i)]
      simp only [mul_zero, sum_const_zero]
      exact hc'
    · simp [bS, hB, show ¬ 28 < nb by omega]
  · rw [DoomS, if_neg (by omega)] at hd
    rw [filter_false_of_mem fun c _ hc => hc (by
      rw [DoomS, if_neg (by rw [hlen]; omega), selC_end hnb (by omega), getD_snoc_lt (by omega)]
      exact hd)]
    simp

end FR.Snd

end

/-! ## From `FRSoundnessFrS` (11 declarations) -/

section

namespace FR.Snd

open RecursionFast Finset FR.Impl FR.NodeT FR.NodeI

set_option linter.constructorNameAsVariable false

/-- S1's coordinate `j`. -/
def coS (es : Log) (j : ℕ) : F := coordAt es 98 j

def thL (es : Log) : List F := (List.range 10).map fun l => coS es (18 + l)

def ksL (es : Log) : F := coS es 28

theorem mle_digTbl (θ : Fin 10 → F) (e₀ e₁ : F) :
    mle (digTbl e₀ e₁) θ = thS θ fun σ => if digBit e₀ e₁ σ then 1 else 0 := by
  rw [mle]
  rw [show (∑ u : Fin (2 ^ 10), eq θ (cube u) * digTbl e₀ e₁ u) = ∑ u : Fin (2 ^ 10),
      (fun q => eqAtR θ q * if q < 256 then (if digBit e₀ e₁ q then 1 else 0) else 0) u.val from
    sum_congr rfl fun u _ => by
      rw [eq_cube_eqAtR, digTbl]; simp only [ite_and]]
  rw [Fin.sum_univ_eq_sum_range (fun q => eqAtR θ q * if q < 256 then
    (if digBit e₀ e₁ q then 1 else 0) else 0)]
  simp only [mul_ite, mul_zero]
  rw [sum_range_ite_lt (by norm_num), thS]
  exact sum_congr rfl fun q _ => by split_ifs <;> simp

theorem digBit_zero (σ : ℕ) : digBit 0 0 σ = false := by
  have h0 : (F.c₀ 0).val = 0 := rfl
  have h1 : (F.c₁ 0).val = 0 := rfl
  unfold digBit bitF; split_ifs <;> simp [h0, h1]

theorem idx_split {a y q : ℕ} (hy : y < 2 ^ a) :
    (y + 2 ^ a * q) % 2 ^ a = y ∧ (y + 2 ^ a * q) / 2 ^ a = q := by
  refine ⟨by rw [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hy], ?_⟩
  rw [Nat.add_mul_div_left _ _ (Nat.two_pow_pos a), Nat.div_eq_of_lt hy, zero_add]

section Reads

variable {L es L' es' : Log} {p : ℕ}

theorem coS_congr (h : Agree es es' p) {j : ℕ} (hj : 99 + j / 2 < p) : coS es j = coS es' j := by
  simp only [coS, coordAt]; exact fAt_congr h (by omega) _

end Reads

theorem coordS_getD (X : Log) {j : ℕ} (hj : j < 30) :
    (List.ofFn fun i : Fin (15 * 2) => coordAt X 98 i).getD j 0 = coS X j := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_ofFn, dif_pos (by omega)]; rfl

theorem sum_eqAtR_split (a b : ℕ) (g : ℕ → F) (P : List F) :
    ∑ i ∈ range (2 ^ (a + b)), eqAtR (ptOf (a + b) P) i * g i =
      ∑ q ∈ range (2 ^ b), ∑ y ∈ range (2 ^ a),
        eqAtR (ptOf a P) y * eqAtR (ptOf b (P.drop a)) q * g (y + 2 ^ a * q) := by
  rw [← mle_ofFn_split, tbl_ofFn, mle]
  exact ((Fin.sum_univ_eq_sum_range (fun i => eqAtR (ptOf (a + b) P) i * g i) _).symm.trans
    (sum_congr rfl fun u _ => by rw [eq_cube_eqAtR]))

theorem eqAtR_zeros4 {h : ℕ} (hh : h < 16) :
    eqAtR (ptOf 4 [(0 : F), 0, 0, 0]) h = if h = 0 then 1 else 0 := by
  interval_cases h <;> simp [eqAtR, Fin.prod_univ_four, ptOf] <;> decide

theorem mle_tab (a : ℕ) (f : ℕ → ℕ → F) (rs : List F) :
    mle (tbl (a + 10) (Array.ofFn (n := 2 ^ (a + 10)) fun i => f (i.val % 2 ^ a) (i.val / 2 ^ a)))
        (ptOf (a + 10) rs) =
      ∑ q ∈ range (2 ^ 10), ∑ y ∈ range (2 ^ a),
        eqAtR (ptOf a rs) y * eqAtR (ptOf 10 (rs.drop a)) q * f y q := by
  refine (mle_ofFn_split a 10 (fun i => f (i % 2 ^ a) (i / 2 ^ a)) rs).trans ?_
  exact sum_congr rfl fun q _ => sum_congr rfl fun u hu => by
    obtain ⟨h1, h2⟩ := idx_split (q := q) (mem_range.1 hu); rw [h1, h2]

end FR.Snd

end

/-! ## From `FRSoundnessFrZM` (23 declarations) -/

section

namespace FR.Snd

open RecursionFast FR.Merkle Finset FR.Impl ProductCircuit

set_option linter.constructorNameAsVariable false

section Pins

theorem blockTarget_isNone (t : ℕ) (fin : Bool) (k : Block.Pos) :
    (Stream.blockTarget t fin k).isNone = !(1024 ≤ k.val && k.val ≤ 1152) := by
  unfold Stream.blockTarget
  split_ifs <;> simp <;> omega

theorem kindTarget_isNone (κ : Kinds.Kind) (k : Block.Pos) :
    (κ.target k).isNone = !((k.val < 256 && κ.h0Pin) ||
      (512 ≤ k.val && k.val < 1024 && (κ.msgPin ((k.val - 512) / 8)).isSome) ||
      (1024 ≤ k.val && k.val ≤ 1152)) := by
  unfold Kinds.Kind.target
  split_ifs <;> (try rw [blockTarget_isNone]) <;> simp_all <;>
    first
    | omega
    | exact ⟨Or.inl (Or.inl (by omega)), Or.inl (by omega)⟩
    | simp [show ¬ (k.val < 256) by omega, show ¬ (1024 ≤ k.val) by omega]

open Kinds in
theorem pins_streamStart (k : Block.Pos) :
    (streamStart.target k).isNone = !isZeroRow .streamStart k.val := by
  rw [kindTarget_isNone]; simp [streamStart, isZeroRow, zeroRows] <;> (try rw [Bool.eq_iff_iff]) <;> (try simp) <;> omega

theorem pins_stream (L i : ℕ) (k : Block.Pos) :
    (Stream.streamTarget L i k).isNone = !isZeroRow .stream k.val := by
  rw [Stream.streamTarget, blockTarget_isNone]; simp [isZeroRow, zeroRows]

open Kinds in
theorem pins_hashA (k : Block.Pos) : (hashA.target k).isNone = !isZeroRow .hashA k.val := by
  rw [kindTarget_isNone]; simp only [hashA, isZeroRow, zeroRows]
  by_cases h0 : (k.val - 512) / 8 = 0 <;> by_cases h1 : 41 ≤ (k.val - 512) / 8 <;> simp [h0, h1] <;> (try rw [Bool.eq_iff_iff]) <;> (try simp) <;> omega

open Kinds in
theorem pins_hashB1 (tag : UInt8) (k : Block.Pos) :
    ((hashB1 tag).target k).isNone = !isZeroRow .hashB1 k.val := by
  rw [kindTarget_isNone]; simp only [hashB1, isZeroRow, zeroRows]
  by_cases h0 : (k.val - 512) / 8 = 0 <;> simp [h0] <;> (try rw [Bool.eq_iff_iff]) <;> (try simp) <;> omega

open Kinds in
theorem pins_hashB2 (k : Block.Pos) : (hashB2.target k).isNone = !isZeroRow .hashB2 k.val := by
  rw [kindTarget_isNone]; simp only [hashB2, isZeroRow, zeroRows]
  by_cases h1 : 1 ≤ (k.val - 512) / 8 <;> simp [h1] <;> (try rw [Bool.eq_iff_iff]) <;> (try simp) <;> omega

open Kinds in
theorem pins_streamEnd41 (k : Block.Pos) :
    (streamEnd41.target k).isNone = !isZeroRow .streamEnd41 k.val := by
  rw [kindTarget_isNone]; simp only [streamEnd41, isZeroRow, zeroRows]
  by_cases h1 : 41 ≤ (k.val - 512) / 8 <;> simp [h1] <;> (try rw [Bool.eq_iff_iff]) <;> (try simp) <;> omega

open Kinds in
theorem pins_w43 (i s : UInt8) (k : Block.Pos) :
    ((w43 i s).target k).isNone = !isZeroRow .w43 k.val := by
  rw [kindTarget_isNone]; simp only [w43, isZeroRow, zeroRows]
  by_cases h0 : (k.val - 512) / 8 = 0 <;> by_cases h9 : (k.val - 512) / 8 = 9 <;>
    by_cases h10 : (k.val - 512) / 8 = 10 <;> by_cases h1 : 43 ≤ (k.val - 512) / 8 <;>
    simp [h0, h9, h10, h1] <;> (try rw [Bool.eq_iff_iff]) <;> (try simp) <;> omega

theorem pins_chain (k : Block.Pos) : (Chain.chainTarget k).isNone = !isZeroRow .chain k.val := by
  unfold Chain.chainTarget; simp only [isZeroRow, zeroRows]
  split_ifs <;> simp <;> (try rw [Bool.eq_iff_iff]) <;> (try simp) <;> omega

end Pins

/-- Kind `j` of A.6 (`blockKinds` order). -/
def bkOf (j : Fin 9) : BlockKind := blockKinds.getD j.val .free

/-- The index of a kind in `blockKinds`. -/
def bkIdx : BlockKind → Fin 9
  | .chain => 0 | .stream => 1 | .streamStart => 2 | .streamEnd41 => 3 | .hashA => 4
  | .hashB1 => 5 | .hashB2 => 6 | .w43 => 7 | .free => 8

theorem bkOf_idx (b : BlockKind) : bkOf (bkIdx b) = b := by cases b <;> rfl

theorem bkOf_eq_iff (j : Fin 9) (b : BlockKind) : bkOf j = b ↔ j = bkIdx b := by
  refine ⟨fun h => ?_, fun h => h ▸ bkOf_idx b⟩
  subst h; fin_cases j <;> rfl

/-- **Kind `j`'s matrix**: the circuit's row `p` where kind `j` pins nothing (`maskRows`), the
identity for `free` (rows `(var k, var k)`), `0` on a pinned row. -/
def kMat (C : Block.Pos → Block.Pos → Bool) (j : Fin 9) (p k : Fin (2 ^ 14)) : F :=
  if isZeroRow (bkOf j) p.val then 0
  else if bkOf j = .free then (if p = k then 1 else 0) else ProductCircuit.ofBool F (C p k)

/-- **The kinds' matrices of the entry** (A.6, A.8). -/
noncomputable def zlmFR : ZLM where
  Ak := kMat Block.circuitR1CS.A
  Bk := kMat Block.circuitR1CS.B
  Ind κ j t := if κ.isNode then (if bkOf j = nodeBK t then 1 else 0) else (if j.val = 0 then 1 else 0)
  Et κ t p := if κ.isNode then NodeT.nodeE t p.val else chainE p.val

theorem kMat_bit (C : Block.Pos → Block.Pos → Bool) (j : Fin 9) (p k : Fin (2 ^ 14)) :
    IsBitF (kMat C j p k) := by
  unfold kMat ProductCircuit.ofBool; split_ifs <;> first | exact Or.inl rfl | exact Or.inr rfl

/-- A non-`free` kind's masked rows against a target that pins exactly the kind's rows are the
block R1CS's rows. -/
theorem kMat_mulVec (C : Block.Pos → Block.Pos → Bool) {b : BlockKind} (hb : b ≠ .free)
    {tgt : Block.Target} (hp : ∀ p : Block.Pos, (tgt p).isNone = !isZeroRow b p.val)
    (z : Fin (2 ^ 14) → F) (p : Fin (2 ^ 14)) :
    ∑ k, kMat C (bkIdx b) p k * z k = BlockR1CS.mulVec (fun k j => (tgt k).isNone && C k j) z p := by
  unfold kMat BlockR1CS.mulVec
  refine sum_congr rfl fun k _ => ?_
  show _ = if ((tgt p).isNone && C p k) = true then z k else 0
  rw [bkOf_idx, if_neg hb, hp p]
  cases isZeroRow b p.val <;> cases C p k <;> simp [ProductCircuit.ofBool]

theorem kMat_free (C : Block.Pos → Block.Pos → Bool) (z : Fin (2 ^ 14) → F) (p : Fin (2 ^ 14)) :
    ∑ k, kMat C (bkIdx .free) p k * z k = z p := by
  unfold kMat
  have h0 : isZeroRow .free p.val = false := rfl
  simp only [bkOf_idx, h0, Bool.false_eq_true, if_false, if_true, ite_mul, one_mul, zero_mul]
  rw [sum_ite_eq]; simp

theorem tgtE_eq (tgt : Block.Target) (k : Block.Pos) : NodeT.tgtE tgt k.val = Block.targetVal F tgt k := by
  unfold NodeT.tgtE NodeT.bF Block.targetVal ProductCircuit.ofBool
  rw [show ProductCircuit.pos k.val = k from Fin.ext (ProductCircuit.pos_val k.isLt)]
  rcases tgt k with _ | _ | _ <;> rfl

theorem chainE_eq (k : Block.Pos) : chainE k.val = Block.targetVal F Chain.chainTarget k := by
  unfold chainE Block.targetVal ProductCircuit.ofBool
  rw [show ProductCircuit.pos k.val = k from Fin.ext (ProductCircuit.pos_val k.isLt)]
  rcases Chain.chainTarget k with _ | _ | _ <;> rfl

theorem bit_sq {x : F} (h : IsBitF x) : x * x = x + 0 := by
  rcases h with rfl | rfl <;> simp

theorem targetS_range {n : ℕ} (P : Fin n → F) (E : Fin 64 → Fin (2 ^ n) → F) (σ : Fin 64)
    (E' : ℕ → F) (hE : ∀ u : Fin (2 ^ n), E σ u = E' u.val) :
    FR.targetS P E σ = ∑ u ∈ range (2 ^ n), eqAtR P u * E' u := by
  unfold FR.targetS
  rw [← Fin.sum_univ_eq_sum_range (fun u => eqAtR P u * E' u)]
  exact sum_congr rfl fun u _ => by rw [eq_cube_eqAtR, hE]

end FR.Snd

end

/-! ## From `FRSoundnessFrBind` (1 declaration) -/

section

namespace FR.Snd

open RecursionFast FR.Merkle Finset FR.Impl

set_option linter.constructorNameAsVariable false

/-- RS claim 1's inner weight: the Lagrange weight of the low 6 bits times `eq(ρ₁, ·)` at bit 6. -/
theorem cwL_zero (κ : Kind) (es : Log) {σ y : ℕ} (hσ : σ < 64) (hy : y < 2) :
    cwL κ es 0 (σ + 64 * y) = lagrangeWeight sNodeF (lamL es) ⟨σ, hσ⟩ *
      eqAtR (ptOf 1 [pinnedRho 0]) y := by
  have hi : σ + 64 * y < 128 := by omega
  have hb : (σ + 64 * y).testBit 6 = y.testBit 0 := by
    have h6 : (σ + 64 * y) / 2 ^ 6 = y := by norm_num; omega
    rw [show (6 : ℕ) = 0 + 6 from rfl, ← Nat.testBit_div_two_pow, h6]
  have hm : (σ + 64 * y) % 64 = σ := by omega
  show (eqZS (fAt es 14 0) (pinnedRho 0)).getD (σ + 64 * y) 0 = _
  simp only [eqZS, Array.getD_eq_getD_getElem?, Array.getElem?_ofFn, hi, dite_true,
    Option.getD_some, hb, hm, eqAtR, Fin.prod_univ_one, Fin.val_zero, ptOf, List.getD_cons_zero]
  rfl

end FR.Snd

end

end G6_FRSoundnessCoreFront
