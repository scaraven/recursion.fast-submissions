-- New for `flock-recursive` (BLUEPRINT §10 changes 27 (B) step 3; stage RET-2): the declarations of
-- the 3.x soundness modules that the revision 4.1 certificate reads, moved here verbatim (same
-- names, statements and proofs) from `FRSoundnessStepE` (7), `FRSoundnessHide` (1), `FRKState` (1),
-- `FRSoundnessPIOP` (7), `FRSoundnessTail` (8), `FRSoundnessTailM` (1), `FRSoundnessFront` (3),
-- `FRSoundnessRows` (22), `FRSoundnessFrW0` (12), `FRSoundnessFrRS` (1), `FRSoundnessFrPend` (2),
-- `FRSoundnessFrZ` (18), `FRSoundnessFrB` (5), `FRSoundnessFrE` (6), `FRSoundnessFrL` (17),
-- `FRSoundnessFrW0V` (10), `FRSoundnessFrRS0` (5). Content: the rows and front readers revision 4.1
-- reuses (`fF`, `rowMat`, `Reads`, the `Rows` matrices, `stL`/`vkL`, `PubOK`, the Z/L/E/RS0 pieces,
-- `D2`/`D3`). The 3.x modules import this one.
import FRVIRFinalsCoreSG
import FRVIRTplFast
import FRSoundnessCoreTail
import FRSoundnessCoreTruths
import RecursionFast.Contract.Certificate
import RecursionFast.Library.PaperTheorem

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
