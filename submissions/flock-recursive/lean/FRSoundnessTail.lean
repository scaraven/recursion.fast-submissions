-- New for `flock-recursive` (BLUEPRINT A.10 P1.i, C.i, P2.i, P3.i, Pf; stage S-G1i).
import FRSoundnessFold

/-!
# The Ligerito tail P1.0 → Pf: the concrete dooms and their per-phase obligations

The tail is parametric in level 0's weight table `W₀` and P1.0's initial claim `c₀` (the front's
outputs: `w0F` of RS's and the cells' weights, and `v*` as `finB′` computes it), which read
only entries before P1.0 (`LocalW`, `LocalC`).

* **Part A: positions** (checked once): `cStart i` (C.i's absorb, P2.i's entry), `p3S0 i` (P3.i's
  entry), `pfStart`.
* **Part B: reads.** **`Same L es L' es' p`**: the entries before `p` agree and so do the words
  whose caps lie before `p`. It holds for a chain and its extension on one log (`same_of_agree`)
  and for a `StabExt` extension on the charging log and the whole log (`same_stabX`). Every tail
  ingredient is congruent under `Same` with its read bound (`*_same`).
* **Part C: the level chain.** `lvW i` (`W₀`, then `nextW`), `lvC i` (`c₀`, then `vNext` of
  P1.(i−1)'s final claim `c1`), P1.i's tables `lvT i` (`[Wᵢ, f⁽ⁱ⁾]` over `ℓᵢ + mLog` variables),
  Pf's (`[W_f, final]`, `W_f` the padded `wNext`). **`trueSum_lvT_fold`**: after the `ℓᵢ` rounds the
  true sum is `⟨foldW Wᵢ, fold_z(f⁽ⁱ⁾)⟩`.
-/

namespace FR.Snd
open RecursionFast FR.Merkle Finset

set_option linter.constructorNameAsVariable false

/-! ## Part A: positions -/

/-- C.i's absorb (the next cap or the final message), P2.i's entry. -/
def cStart (i : ℕ) : ℕ := phStart (27 + 5 * i)

/-- P3.i's entry (P2.i's last answer). -/
def p3S0 (i : ℕ) : ℕ := phStart (30 + 5 * i) - 1

/-- Pf's first absorb. -/
def pfStart : ℕ := phStart 51

/-- The first position after P3.i (P1.(i+1)'s first absorb, or Pf's). -/
def nxStart (i : ℕ) : ℕ := if i < 4 then p1Start (i + 1) else pfStart

theorem capPos_succ (i : ℕ) : capPos (i + 1) = cStart i := by
  simp only [capPos, cStart, Nat.add_one_ne_zero, ite_false]; congr 1; ring

theorem tail_pos_check : (List.range 5).all (fun i => decide (capPos i < p1Start i) &&
    decide (1 ≤ p1Start i) && decide (p1Start i + 2 * hEll i = cStart i) &&
    decide (cStart i + (lvlStar i).sq = p3S0 i) && decide (p3S0 i + 6 = nxStart i)) = true := by
  unfold nxStart p1Start pfStart cStart p3S0 capPos hEll phStart; rw [fsStarts_eq]; decide

theorem tail_pos {i : ℕ} (hi : i < 5) : capPos i < p1Start i ∧ 1 ≤ p1Start i ∧
    p1Start i + 2 * hEll i = cStart i ∧ cStart i + (lvlStar i).sq = p3S0 i ∧
      p3S0 i + 6 = nxStart i := by
  have h := tail_pos_check
  simp only [List.all_eq_true, List.mem_range, Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩ := h i hi
  exact ⟨h1, h2, h3, h4, h5⟩

theorem pfStart_eq : pfStart = 483 := by unfold pfStart phStart; rw [fsStarts_eq]; rfl

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

theorem Same.kind (h : Same L es L' es' p) (hp : 1 ≤ p) : kindOf es = kindOf es' :=
  kindOf_congr (h.1.mono hp)

/-- On a `StabExt` extension, the charging log and the whole log read the same. -/
theorem same_stabX (hb : ¬ Bad L) {n : ℕ} (hci : IsChain L n) {X : Log}
    (hX : StabExt fsRnd (entriesOf L (pathOf L n)) X) : Same (L.take n) X L X X.length :=
  ⟨fun _ _ => rfl, fun κ _ hi hc => wordK_stabX hb hci hX hi κ hc⟩

theorem eqBits_congr {R : Type*} [CommRing R] {r r' : ℕ → R} {ℓ : ℕ}
    (h : ∀ v < ℓ, r v = r' v) (x : ℕ) : eqBits r ℓ x = eqBits r' ℓ x := by
  unfold eqBits bitSel; exact prod_congr rfl fun v hv => by simp only [h v (mem_range.1 hv)]

section Reads

variable (h : Same L es L' es' p) {i : ℕ} (hi : i < 5) (κ : Kind)
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
    have h46 : cStart 4 = phStart 47 := rfl
    have := h.1 (phStart 47) (by omega)
    simp only [entAt] at this
    rw [this]

theorem consSet_same (hp : cStart i + 1 ≤ p) : consSet κ L es i = consSet κ L' es' i := by
  simp only [consSet, foldAt_same h hi κ (by omega), nextMsg_same h hi κ hp]

theorem truthP2_same (hp : cStart i + 1 ≤ p) : truthP2 κ L es i ↔ truthP2 κ L' es' i := by
  simp only [truthP2, consSet_same h hi κ hp]

theorem truthC_same (hp : cStart i + 1 ≤ p) : truthC κ L es i ↔ truthC κ L' es' i := by
  simp only [truthC, foldMsg_same h hi κ (by omega), nextMsg_same h hi κ hp]

theorem qPos_same (hp : p3S0 i + 1 ≤ p) {q : ℕ} (hq : q < (lvl κ i).t) :
    qPos κ es i q = qPos κ es' i q := by
  obtain ⟨hper, -, ht⟩ := p2_params κ i hi
  have h4 := (tail_pos hi).2.2.2.1
  have : q / (lvl κ i).per < (lvlStar i).sq := (Nat.div_lt_iff_lt_mul hper).mpr (by omega)
  simp only [qPos, posAt, ansAt]
  rw [h.1 _ (by unfold cStart at h4; omega)]

theorem consErr_same (hp : p3S0 i + 1 ≤ p) {q : ℕ} (hq : q < (lvl κ i).t) :
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
    foldW (lvl κ i).ell (sAt es i) W = foldW (lvl κ i).ell (sAt es' i) W := by
  funext x; simp only [foldW, lvl_ell κ hi, eqBits_congr (sAt_same_lt h hp hi)]

theorem nextW_same (hp : nxStart i ≤ p) (W : ℕ → K) : nextW κ es i W = nextW κ es' i W := by
  obtain ⟨-, -, -, h4, h5⟩ := tail_pos hi
  rw [nextW, nextW, foldW_same h hi κ (by omega), wNext_same h hi κ hp]

end Reads

/-! ## Part C: the level chain -/

/-- The product summand of the K sumchecks (P1.i, Pf). -/
def e2 : Expr := .mul (.var 0) (.var 1)

theorem e2_deg : e2.deg = 2 := rfl

/-- P1.i's variables: the `ℓᵢ` row bits (the rounds), then level `i`'s message bits. -/
def nrP (i : ℕ) (κ : Kind) : ℕ := (lvl κ i).ell + mLog κ i

/-- Two tables of size `2^m`. -/
noncomputable def tabs (W f : ℕ → K) (m : ℕ) : Array (Array K) :=
  #[Array.ofFn (n := 2 ^ m) fun y => W y, Array.ofFn (n := 2 ^ m) fun y => f y]

theorem tabs_size (W f : ℕ → K) (m : ℕ) : ∀ t ∈ tabs W f m, t.size = 2 ^ m := by
  intro t ht
  simp only [tabs, List.mem_toArray, List.mem_cons, List.not_mem_nil, or_false] at ht
  rcases ht with rfl | rfl <;> exact Array.size_ofFn

theorem getD_bindAll {R : Type*} [CommRing R] :
    ∀ (rs : List R) (ts : Array (Array R)) (k : ℕ),
      (bindAll ts rs).getD k #[] = bindL (ts.getD k #[]) rs
  | [], _, _ => rfl
  | r :: rs, ts, k => by
    rw [bindAll, getD_bindAll rs, getD_map_bind0]; rfl

/-- The top-bit split of an `eq`-weighted sum (as in `pf_succ`). -/
theorem sum_eqBits_succ {R : Type*} [CommRing R] (s : ℕ → R) (ℓ x : ℕ) (G : ℕ → R) :
    ∑ u ∈ range (2 ^ (ℓ + 1)), eqBits s (ℓ + 1) u * G (u + 2 ^ (ℓ + 1) * x) =
      ∑ u ∈ range (2 ^ ℓ), eqBits s ℓ u * G (u + 2 ^ ℓ * (2 * x)) +
        s ℓ * (∑ u ∈ range (2 ^ ℓ), eqBits s ℓ u * G (u + 2 ^ ℓ * (2 * x + 1)) -
          ∑ u ∈ range (2 ^ ℓ), eqBits s ℓ u * G (u + 2 ^ ℓ * (2 * x))) := by
  have hr : range (2 ^ (ℓ + 1)) = range (2 ^ ℓ + 2 ^ ℓ) := by congr 1; ring
  have s1 : ∑ u ∈ range (2 ^ ℓ), eqBits s (ℓ + 1) u * G (u + 2 ^ (ℓ + 1) * x) =
      ∑ u ∈ range (2 ^ ℓ), eqBits s ℓ u * (1 - s ℓ) * G (u + 2 ^ ℓ * (2 * x)) :=
    sum_congr rfl fun u hu => by
      rw [show eqBits s (ℓ + 1) u = _ from bitSel_succ_lo _ _ (mem_range.1 hu),
        show u + 2 ^ (ℓ + 1) * x = u + 2 ^ ℓ * (2 * x) by ring]; rfl
  have s2 : ∑ u ∈ range (2 ^ ℓ), eqBits s (ℓ + 1) (2 ^ ℓ + u) *
      G (2 ^ ℓ + u + 2 ^ (ℓ + 1) * x) =
      ∑ u ∈ range (2 ^ ℓ), eqBits s ℓ u * s ℓ * G (u + 2 ^ ℓ * (2 * x + 1)) :=
    sum_congr rfl fun u hu => by
      rw [show eqBits s (ℓ + 1) (2 ^ ℓ + u) = _ from bitSel_succ_hi _ _ (mem_range.1 hu),
        show 2 ^ ℓ + u + 2 ^ (ℓ + 1) * x = u + 2 ^ ℓ * (2 * x + 1) by ring]; rfl
  rw [hr, sum_range_add, s1, s2, mul_sub, mul_sum, mul_sum, ← sum_sub_distrib,
    ← sum_add_distrib, ← sum_add_distrib]
  exact sum_congr rfl fun u _ => by ring

/-- **Binding the first `ℓ` variables** at `s 0, …, s (ℓ−1)`: entry `x` of the bound table is
`Σ_{u<2^ℓ} eq(s, u)·t[u + 2^ℓ x]`. -/
theorem bindL_range_getD {R : Type*} [CommRing R] (s : ℕ → R) :
    ∀ (ℓ m : ℕ) (t : Array R), t.size = 2 ^ (ℓ + m) → ∀ x < 2 ^ m,
      (bindL t ((List.range ℓ).map s)).getD x 0 =
        ∑ u ∈ range (2 ^ ℓ), eqBits s ℓ u * t.getD (u + 2 ^ ℓ * x) 0
  | 0, m, t, _, x, _ => by simp [bindL, eqBits, bitSel]
  | ℓ + 1, m, t, ht, x, hx => by
    rw [List.range_succ, List.map_append, List.map_singleton, bindL_append,
      sum_eqBits_succ s ℓ x (fun y => t.getD y 0)]
    have hs : (bindL t ((List.range ℓ).map s)).size = 2 ^ (m + 1) :=
      bindL_size _ t (by rw [ht, List.length_map, List.length_range]; congr 1; ring)
    have ih := bindL_range_getD s ℓ (m + 1) t (by rw [ht]; congr 1; ring)
    rw [← ih (2 * x) (by rw [pow_succ]; omega), ← ih (2 * x + 1) (by rw [pow_succ]; omega)]
    have h2 : 2 * x + 1 < (bindL t ((List.range ℓ).map s)).size := by rw [hs, pow_succ]; omega
    simp only [bind0, Array.getD_eq_getD_getElem?, Array.getElem?_ofFn, hs,
      show x < 2 ^ (m + 1) / 2 by rw [pow_succ, Nat.mul_div_cancel _ two_pos]; exact hx,
      dite_true, Option.getD_some, Array.getElem?_eq_getElem h2,
      Array.getElem?_eq_getElem (show 2 * x < (bindL t ((List.range ℓ).map s)).size by omega)]

/-- The two-table summand's true sum. -/
theorem trueSum_e2 (ts : Array (Array K)) (m : ℕ) :
    trueSum e2 ts m = ∑ u ∈ range (2 ^ m), (ts.getD 0 #[]).getD u 0 * (ts.getD 1 #[]).getD u 0 := by
  rw [trueSum, ← Fin.sum_univ_eq_sum_range (fun u => (ts.getD 0 #[]).getD u 0 *
    (ts.getD 1 #[]).getD u 0)]
  exact sum_congr rfl fun u _ => by simp only [e2, Expr.eval, tbl]

theorem tabs_getD0 (W f : ℕ → K) (m : ℕ) :
    (tabs W f m).getD 0 #[] = Array.ofFn (n := 2 ^ m) fun y => W y := rfl

theorem tabs_getD1 (W f : ℕ → K) (m : ℕ) :
    (tabs W f m).getD 1 #[] = Array.ofFn (n := 2 ^ m) fun y => f y := rfl

theorem ofFn_getD {n y : ℕ} (g : ℕ → K) (h : y < n) :
    (Array.ofFn (n := n) fun x => g x).getD y 0 = g y := by
  simp [Array.getD_eq_getD_getElem?, h]

theorem trueSum_tabs (W f : ℕ → K) (m : ℕ) :
    trueSum e2 (tabs W f m) m = ∑ y ∈ range (2 ^ m), W y * f y := by
  rw [trueSum_e2]
  refine sum_congr rfl fun y hy => ?_
  rw [tabs_getD0, tabs_getD1, ofFn_getD _ (mem_range.1 hy), ofFn_getD _ (mem_range.1 hy)]

/-- **After `ℓ` rounds the true sum is the folded inner product** `⟨foldW W, fold(f)⟩`. -/
theorem trueSum_tabs_fold (s : ℕ → K) (ℓ m : ℕ) (W f : ℕ → K) :
    trueSum e2 (bindAll (tabs W f (ℓ + m)) ((List.range ℓ).map s)) m =
      ∑ x ∈ range (2 ^ m), foldW ℓ s W x *
        ∑ u ∈ range (2 ^ ℓ), eqBits s ℓ u * f (u + 2 ^ ℓ * x) := by
  rw [trueSum_e2, getD_bindAll, getD_bindAll]
  refine sum_congr rfl fun x hx => ?_
  have hx' := mem_range.1 hx
  have hsz := tabs_size W f (ℓ + m)
  rw [tabs_getD0, tabs_getD1, bindL_range_getD s ℓ m _ Array.size_ofFn x hx',
    bindL_range_getD s ℓ m _ Array.size_ofFn x hx', foldW,
    Fin.sum_univ_eq_sum_range (fun u => eqBits s ℓ u * W (u + 2 ^ ℓ * x)) (2 ^ ℓ)]
  refine congrArg₂ (· * ·) (sum_congr rfl fun u hu => ?_) (sum_congr rfl fun u hu => ?_)
  · have : u + 2 ^ ℓ * x < 2 ^ (ℓ + m) := by
      have := mem_range.1 hu; rw [pow_add]; nlinarith
    rw [ofFn_getD _ this]
  · have : u + 2 ^ ℓ * x < 2 ^ (ℓ + m) := by
      have := mem_range.1 hu; rw [pow_add]; nlinarith
    rw [ofFn_getD _ this]

end FR.Snd
