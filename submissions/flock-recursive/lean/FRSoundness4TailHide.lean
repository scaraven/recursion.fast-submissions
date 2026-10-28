-- New for `flock-recursive` (BLUEPRINT §5.1, §5.4, A.10; stage T4, S-G13 route C): a copy-port of
-- `FRSoundnessHide` to revision 4.1's item sequence `seq4` (namespace `FR.Snd.T4`, see `FRSoundness4TailStep`):
-- the declarations that read positions, chains or the kind are copied, the rest is imported.
import FRSoundness4TailTruths

/-!
# The Hide doom and the potential `muT` at `seq4` (T4)

The 3.x declarations of `FRSoundnessHide` that read the positions, the chains or the kind, restated in
`FR.Snd.T4` over `fsItems4`/`phStart4`/`fsRnd4`, `G.Matches`/`G.IsChain` and `CKind`
(`kindOfC`, `CKind.lv`). Positions from P1.0 on are 3.x's plus 14 (`phStart4_shift`); the kind
enters through the ladder `lvOf κ.m` only. Changes beyond the renaming are marked `T4:`.
-/

/-! # Port of `FRSoundnessHide` (its module doc describes the 3.x original) -/

namespace FR.Snd.T4
open RecursionFast FR.Merkle Finset
open scoped NNReal

set_option linter.constructorNameAsVariable false

/-! ## Part A: the positions -/

/-- P1.i's first Fiat–Shamir position (phase `26 + 5i`). -/
def p1Start (i : ℕ) : ℕ := phStart4 (26 + 5 * i)

theorem lvl_ell (κ : CKind) {i : ℕ} (hi : i < 5) : (CKind.lv κ i).ell = hEll i := by
  rcases κ with (_|_|_) | (_|_|_) <;> interval_cases i <;> rfl

/-- Checked: P1's starts and rounds (`[332, 375, 402, 426, 448]`, `[6, 4, 4, 4, 4]`), each level's
cap absorbed before its P1, and the P1 phases disjoint. -/
theorem p1_check : (List.range 5).all (fun i => decide (capPos i < p1Start i) &&
    (List.range 5).all fun i' => i == i' || decide (p1Start i + 2 * hEll i ≤ p1Start i') ||
      decide (p1Start i' + 2 * hEll i' ≤ p1Start i)) = true := by
  unfold capPos p1Start phStart4 hEll; rw [fsStarts4_eq]; decide

theorem capPos_lt {i : ℕ} (hi : i < 5) : capPos i < p1Start i := by
  have := p1_check
  simp only [List.all_eq_true, List.mem_range, Bool.and_eq_true, decide_eq_true_eq] at this
  exact (this i hi).1

theorem p1_disj {i i' : ℕ} (hi : i < 5) (hi' : i' < 5) (h : i ≠ i') :
    p1Start i + 2 * hEll i ≤ p1Start i' ∨ p1Start i' + 2 * hEll i' ≤ p1Start i := by
  have := p1_check
  simp only [List.all_eq_true, List.mem_range, Bool.and_eq_true, Bool.or_eq_true, beq_iff_eq,
    decide_eq_true_eq] at this
  have := (this i hi).2 i' hi'
  omega

/-- Checked: every level's cap absorb (`len` bytes, `len ≥ 32·2^cap` for every kind, inside
`queryCap`), with `cap ≤ log₂ n`. -/
theorem cap_check : (List.range 5).all (fun i => match fsItems4[capPos i]? with
    | some (.absorb len) => [CKind.seg .L30, .seg .L31, .seg .L32, .node .N2, .node .N4, .node .N8].all (fun κ =>
        decide (32 * 2 ^ (CKind.lv κ i).cap ≤ len) && decide ((CKind.lv κ i).cap ≤ (CKind.lv κ i).logN)) &&
        decide (40 + len ≤ queryCap)
    | _ => false) = true := by
  unfold capPos phStart4; rw [fsStarts4_eq]; decide +kernel

/-- Checked once for all five levels: P1.i's odd offsets are squeezes, and no multi-squeeze
phase meets P1.i. -/
theorem p1_sq_check : (List.range 5).all (fun i => decide (1 ≤ p1Start i) && decide (0 < hEll i) &&
    (List.range (hEll i)).all (fun j => fsItems4[p1Start i + 2 * j + 1]? == some .squeeze) &&
    fsRanges4.all fun x => decide (x.1 + x.2 < p1Start i ∨ p1Start i + 2 * hEll i ≤ x.1 + 1)) =
      true := by
  rw [fsRanges4_eq]; decide +kernel

/-- **P1.i is a rounds phase** of `ℓᵢ` real rounds (checked squeezes, no multi-squeeze phase). -/
theorem p1_phase {i : ℕ} (hi : i < 5) : RoundsPhase (p1Start i) (hEll i) fun _ => hEll i := by
  have h := p1_sq_check
  rw [List.all_eq_true] at h
  have h' := h i (List.mem_range.mpr hi)
  simp only [Bool.and_eq_true, decide_eq_true_eq] at h'
  exact roundsPhase_of h'.1.1.1 h'.1.1.2 (fun _ => le_rfl) h'.1.2 h'.2

/-! ## Part B: the Hide doom -/

/-- The P1.i rounds answered by `es`: `min ℓᵢ ⌊(|es| − p1Start i)/2⌋`. -/
def hRnd (es : Log) (i : ℕ) : ℕ := min (hEll i) ((es.length - p1Start i) / 2)

/-- P1.i's first `l` fold challenges `sᵢ` (`sAt`). -/
def sList (es : Log) (i l : ℕ) : List K := (List.range l).map (sAt es i)

/-- Column `j`'s difference table between level `i`'s word and its decoded rows (over the
`2^ℓᵢ` rows). -/
noncomputable def hDiff (κ : CKind) (L es : Log) (i : ℕ) (j : Fin (2 ^ (CKind.lv κ i).logN)) :
    Array K :=
  Array.ofFn (n := (CKind.lv κ i).rows) fun r => wordK κ L es i r j - decodeL κ L es i r j

/-- Level `i`'s cap entry passes its absorb item's check (on a chain this is `Matches`; on a formal
extension past the chain it fails, `fsCheck_ext_ge`). -/
def capOK (es : Log) (i : ℕ) : Prop :=
  ∃ len, fsItems4[capPos i]? = some (.absorb len) ∧
    fsCheck (.absorb len) (entAt es (capPos i)).1 = true

/-- **No hidden disagreement so far at level `i`** (§10 changes 14–15): on a close word, every
column outside the joint agreement set keeps a nonzero difference table after binding the P1.i
challenges answered so far (`mlDoom` over K). With all `ℓᵢ` bound this is `¬ Hide_i`
(`noHide_full`); before P1.i it holds for every word (`noHide_zero`). -/
def noHide (κ : CKind) (L es : Log) (i : ℕ) : Prop :=
  ¬ farL κ L es i → ∀ j ∉ jointAgree (wordK κ L es i) (decodeL κ L es i),
    mlDoom (CKind.lv κ i).ell (hDiff κ L es i j) (sList es i (hRnd es i))

/-- **The Hide doom** (§10 changes 15): no level has hidden a disagreement so far. Its potential
`μ_Hide` escapes exactly when some P1.i challenge hides one. -/
def DH (L es : Log) : Prop := ∀ i < 5, noHide (kindOfC es) L es i

theorem hDiff_size (κ : CKind) (L es : Log) (i : ℕ) (j : Fin (2 ^ (CKind.lv κ i).logN)) :
    (hDiff κ L es i j).size = 2 ^ (CKind.lv κ i).ell := Array.size_ofFn

theorem tbl_hDiff (κ : CKind) (L es : Log) (i : ℕ) (j : Fin (2 ^ (CKind.lv κ i).logN)) :
    tbl (CKind.lv κ i).ell (hDiff κ L es i j) = fun r => wordK κ L es i r j - decodeL κ L es i r j := by
  funext r
  simp [tbl, hDiff, Array.getD_eq_getD_getElem?, Level.rows]

/-- Before P1.i (no round answered), nothing is hidden: a column outside the joint agreement set
has a nonzero difference table. -/
theorem noHide_zero {κ : CKind} {L es : Log} {i : ℕ} (h : hRnd es i = 0) : noHide κ L es i := by
  intro _ j hj
  have hnil : ∀ n (t : Array K), tbl n t ≠ 0 → mlDoom n t [] := fun n t h => by cases n <;> exact h
  rw [h, sList, List.range_zero, List.map_nil]
  refine hnil _ _ ?_
  rw [tbl_hDiff]
  intro hz
  refine hj (mem_jointAgree.mpr fun r => ?_)
  have := congrFun hz r
  exact sub_eq_zero.mp this

/-- Every chain short of P1.0's first answer satisfies the Hide doom. -/
theorem DH_short {L es : Log} (h : es.length ≤ p1Start 0 + 1) : DH L es := by
  intro i hi
  refine noHide_zero ?_
  have := p1_phase hi
  have hv : ∀ j, j < 5 → p1Start j = [332, 375, 402, 426, 448].getD j 0 := by
    intro j hj; unfold p1Start phStart4; rw [fsStarts4_eq]; interval_cases j <;> rfl
  have h0 := hv 0 (by norm_num)
  have hi' : p1Start 0 ≤ p1Start i := by
    rw [hv i hi, h0]; interval_cases i <;> decide
  simp only [hRnd]
  omega

/-- The rounds answered change only at a P1.i round's squeeze `p1Start i + 2l + 1`, `l < ℓᵢ`. -/
theorem hRnd_append (es : Log) (x : ByteArray × Digest) {i : ℕ}
    (h : ∀ l < hEll i, es.length ≠ p1Start i + 2 * l + 1) : hRnd (es ++ [x]) i = hRnd es i := by
  by_contra hne
  refine h ((es.length - p1Start i) / 2) ?_ ?_ <;>
    simp only [hRnd, List.length_append, List.length_singleton] at hne <;> omega

theorem hRnd_ext1 (es : Log) (a : Digest) {i l : ℕ} (hl : l < hEll i)
    (h : es.length = p1Start i + 2 * l + 1) : hRnd es i = l ∧ hRnd (ext1 es a) i = l + 1 := by
  simp only [hRnd, ext1, List.length_append, List.length_singleton]
  omega

theorem sAt_congr {es es' : Log} {i l : ℕ} (h : Agree es es' (p1Start i + 2 * l + 2)) :
    sAt es i l = sAt es' i l := by
  simp only [sAt, kAt, ansAt]
  rw [h _ (by unfold p1Start; omega)]

theorem sList_congr {es es' : Log} {i l : ℕ} (h : Agree es es' (p1Start i + 2 * l)) :
    sList es i l = sList es' i l := by
  refine List.map_congr_left fun l' hl' => sAt_congr (h.mono ?_)
  simp only [List.mem_range] at hl'
  omega

theorem sList_ext1 (es : Log) (a : Digest) {i l : ℕ} (h : es.length = p1Start i + 2 * l + 1) :
    sList (ext1 es a) i (l + 1) = sList es i l ++ [chK a] := by
  rw [sList, List.range_succ, List.map_append, List.map_singleton, ← sList,
    sList_congr (l := l) (show Agree (ext1 es a) es _ from agree_append es _ (by omega))]
  have : sAt (ext1 es a) i l = chK a := by
    simp only [sAt, kAt, ansAt]
    rw [show phStart4 (26 + 5 * i) + 2 * l + 1 = es.length by unfold p1Start at h; omega,
      entAt_ext1]
  rw [this]

/-- `decodeL` reads the word only. -/
theorem decodeL_congr {κ : CKind} {L L' es es' : Log} {i : ℕ}
    (h : wordK κ L es i = wordK κ L' es' i) : decodeL κ L es i = decodeL κ L' es' i := by
  have key : ∀ (U U' : Fin (CKind.lv κ i).rows → Fin (2 ^ (CKind.lv κ i).logN) → K) (hU : U = U')
      (p : ∃ V : Fin (CKind.lv κ i).rows → Fin (2 ^ (CKind.lv κ i).logN) → K, (∀ r, V r ∈ codeK κ i) ∧
        2 ^ (CKind.lv κ i).logN - lvE κ i ≤ (jointAgree U V).card)
      (p' : ∃ V : Fin (CKind.lv κ i).rows → Fin (2 ^ (CKind.lv κ i).logN) → K, (∀ r, V r ∈ codeK κ i) ∧
        2 ^ (CKind.lv κ i).logN - lvE κ i ≤ (jointAgree U' V).card),
      Classical.choose p = Classical.choose p' := by
    intro U U' hU p p'; subst hU; rfl
  have hf : farL κ L es i ↔ farL κ L' es' i := by simp only [farL, h]
  unfold decodeL
  by_cases hn : farL κ L es i
  · simp only [hn, hf.mp hn, not_true_eq_false, dite_false]
  · simp only [hn, (not_congr hf).mp hn, not_false_eq_true, dite_true]
    exact key _ _ h _ _

/-- Appending where the rounds answered do not change keeps level `i`'s Hide state. -/
theorem noHide_append {κ : CKind} {L es : Log} {i : ℕ} (hi : i < 5) (x : ByteArray × Digest)
    (hr : hRnd (es ++ [x]) i = hRnd es i) : noHide κ L (es ++ [x]) i ↔ noHide κ L es i := by
  by_cases h0 : hRnd es i = 0
  · exact ⟨fun _ => noHide_zero h0, fun _ => noHide_zero (hr.trans h0)⟩
  have hlen : p1Start i + 2 * hRnd es i ≤ es.length := by unfold hRnd at h0 ⊢; omega
  have hcap := capPos_lt hi
  have hA : Agree (es ++ [x]) es es.length := agree_append es _ le_rfl
  have hw : wordK κ L (es ++ [x]) i = wordK κ L es i := by
    funext r p; simp only [wordK, wordOf, colOf_congr κ L i p (hA.mono (by omega))]
  have hd := decodeL_congr hw
  have hs : sList (es ++ [x]) i (hRnd es i) = sList es i (hRnd es i) := sList_congr (hA.mono hlen)
  unfold noHide hDiff farL
  rw [hr, hs, hw, hd]

theorem kindOf_ext1 (es : Log) (a : Digest) (h : 0 < es.length) : kindOfC (ext1 es a) = kindOfC es :=
  kindOf_append _ h

/-- **Off P1's round squeezes, appending keeps the Hide doom.** -/
theorem DH_append_iff {L es : Log} (x : ByteArray × Digest)
    (h : ∀ i < 5, ∀ l < hEll i, es.length ≠ p1Start i + 2 * l + 1) :
    DH L (es ++ [x]) ↔ DH L es := by
  rcases Nat.eq_zero_or_pos es.length with h0 | h0
  · exact ⟨fun _ => DH_short (by omega),
      fun _ => DH_short (by rw [List.length_append, List.length_singleton]; omega)⟩
  rw [DH, DH, kindOf_append x h0]
  exact forall₂_congr fun i hi => noHide_append hi x (hRnd_append es x (h i hi))

/-! ## Part C: the word read off the charging log (`hstab`) -/

/-- **The level words of a chain's formal extensions read the same off the charging log**
(§10 changes 10; A.10's `hstab` reads): on a non-bad log, when the cap entry of an extension of a
prefix of chain `n` passes its absorb check, it is a real chain entry (`fsCheck_ext_ge`), an
entry of `L.take n` or the chain's last entry `L[n]`; its cap digests are carried within the
windows (`cap_carried`), so every column under them reads the same (`colL_take`,
`colL_take_own`). -/
theorem colOf_stab {L : Log} (hb : ¬ Bad L) {n : ℕ} (hci : G.IsChain L n) (k : ℕ)
    (as : List Digest) {i : ℕ} (hi : i < 5) (κ : CKind)
    (hc : capOK (ext ((entriesOf L (pathOf L n)).take k) as) i) (p : Fin (2 ^ (CKind.lv κ i).logN)) :
    colOf κ (L.take n) (ext ((entriesOf L (pathOf L n)).take k) as) i p =
      colOf κ L (ext ((entriesOf L (pathOf L n)).take k) as) i p := by
  obtain ⟨len, hit, hchk⟩ := hc
  set es₀ := (entriesOf L (pathOf L n)).take k with hes₀
  have hlt : capPos i < es₀.length := by
    by_contra h
    rw [fsCheck_ext_ge _ _ (not_lt.mp h)] at hchk
    cases hchk
  have hlk : capPos i < k := by rw [hes₀, List.length_take] at hlt; omega
  have hlc : capPos i < (entriesOf L (pathOf L n)).length := by
    rw [hes₀, List.length_take] at hlt; omega
  have hpl : capPos i < (pathOf L n).length := by rwa [length_entriesOf] at hlc
  set idx := (pathOf L n)[capPos i] with hidx
  have hidxn : idx ≤ n := mem_pathOf_le (List.getElem_mem hpl)
  have hidxL : idx < L.length := lt_of_le_of_lt hidxn hci.1
  have hent : entAt (ext es₀ as) (capPos i) = L[idx] := by
    rw [entAt_ext_lt _ _ hlt, hes₀, entAt_take hlk, entAt, List.getD_eq_getElem _ _ hlc,
      entriesOf_getElem, getElem!_pos L _ hidxL]
  -- the cap's sizes (checked)
  have hcc := cap_check
  simp only [List.all_eq_true, List.mem_range] at hcc
  have hci' := hcc i hi
  rw [hit] at hci'
  simp only [Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq] at hci'
  have hk32 := hci'.1 κ (by rcases κ with (_|_|_) | (_|_|_) <;> simp)
  have hq := hci'.2
  rw [hent] at hchk
  have hsz : (L[idx]).1.size = 40 + len := by
    simp only [fsCheck, Bool.and_eq_true, beq_iff_eq] at hchk; exact hchk.2
  have hcp : p.val / 2 ^ (CKind.lv κ i).sib < 2 ^ (CKind.lv κ i).cap := by
    rw [Nat.div_lt_iff_lt_mul (by positivity), ← pow_add, Level.sib,
      Nat.add_sub_cancel' hk32.2]
    exact p.isLt
  have hd : capDig (ext es₀ as) i (p.val / 2 ^ (CKind.lv κ i).sib) ∈ (frEncW i).carried (L[idx]).1 := by
    rw [capDig, msgAt, hent]
    refine cap_carried hchk (by omega) ?_ i
    calc 32 * (p.val / 2 ^ (CKind.lv κ i).sib + 1) ≤ 32 * 2 ^ (CKind.lv κ i).cap := by omega
      _ ≤ len := hk32.1
  unfold colOf
  rcases Nat.lt_or_eq_of_le hidxn with h | h
  · refine colL_take hb i n ⟨L[idx], ?_, hd⟩ _ _
    rw [List.mem_iff_getElem]
    exact ⟨idx, by simp; omega, by simp⟩
  · have hd' : capDig (ext es₀ as) i (p.val / 2 ^ (CKind.lv κ i).sib) ∈
        (frEncW i).carried (L[n]'hci.1).1 := by simpa [h] using hd
    exact colL_take_own hb hci.1 hd' _ _

theorem wordK_stab {L : Log} (hb : ¬ Bad L) {n : ℕ} (hci : G.IsChain L n) (k : ℕ)
    (as : List Digest) {i : ℕ} (hi : i < 5) (κ : CKind)
    (hc : capOK (ext ((entriesOf L (pathOf L n)).take k) as) i) :
    wordK κ (L.take n) (ext ((entriesOf L (pathOf L n)).take k) as) i =
      wordK κ L (ext ((entriesOf L (pathOf L n)).take k) as) i := by
  funext r p
  simp only [wordK, wordOf, colOf_stab hb hci k as hi κ hc p]

/-- On a chain past level `i`'s cap absorb, the cap entry is real. -/
theorem capOK_of_matches {es : Log} (hm : G.Matches es) {i : ℕ} (hi : i < 5)
    (hl : capPos i < es.length) : capOK es i := by
  have hcc := cap_check
  simp only [List.all_eq_true, List.mem_range] at hcc
  have h := hcc i hi
  have h1 : 1 ≤ capPos i := by
    unfold capPos phStart4; rw [fsStarts4_eq]; interval_cases i <;> decide
  obtain ⟨_, hl', H⟩ := hm
  dsimp only [fs_eq4] at hl' H  -- T4: `G.Matches` reads `FsSeq.fs`, which is `fsItems4`
  obtain ⟨-, hf⟩ := H (capPos i - 1) (by omega)
  cases hh : fsItems4[capPos i]? with
  | none => rw [hh] at h; simp at h
  | some it =>
    cases it with
    | absorb len =>
      refine ⟨len, hh, ?_⟩
      have hlt : capPos i < fsItems4.length := by omega
      have he : fsItems4[capPos i] = .absorb len :=
        Option.some.inj ((List.getElem?_eq_getElem hlt).symm.trans hh)
      have hidx : capPos i - 1 + 1 = capPos i := by omega
      simp only [hidx, he] at hf
      rw [entAt, List.getD_eq_getElem _ _ hl]
      exact hf
    | _ => rw [hh] at h; simp at h

/-- **On `hloc_of`'s extensions a cap entry inside the extension is real** (the ruling on S-G1g
§8 Q1: `hstab`'s scope is `StabExt`): the formal entries sit on squeeze positions
(`fsRnd4_ok`), and the cap position is an absorb (`cap_check`), so it lies in the chain's prefix,
where `Matches` gives the check (`capOK_of_matches`). -/
theorem capOK_of_stabExt {es X : Log} (hm : G.Matches es) (hX : StabExt fsRnd4 es X) {i : ℕ}
    (hi : i < 5) (hl : capPos i < X.length) : capOK X i := by
  obtain ⟨s0, r, as, hr, hs, has, rfl⟩ := hX
  have htk : (es.take (s0 + 1)).length = s0 + 1 := by simp; omega
  have hlt : capPos i < s0 + 1 := by
    by_contra hge
    obtain ⟨-, hpr, hspec⟩ := fsRnd4_ok _ _ _ hr
    rw [length_ext, htk] at hl
    have hsq := (hspec (capPos i) (by omega) (by omega)).1
    dsimp only [fs_eq4] at hsq  -- T4
    have hcc := cap_check
    simp only [List.all_eq_true, List.mem_range] at hcc
    have h := hcc i hi
    rw [hsq] at h
    simp at h
  obtain ⟨len, hit, hchk⟩ := capOK_of_matches hm hi (by omega)
  refine ⟨len, hit, ?_⟩
  rw [entAt_ext_lt _ _ (by rw [htk]; exact hlt), entAt_take hlt]
  exact hchk

/-- **The level words read the same off the charging log on `hloc_of`'s extensions**, once the
extension reaches the cap (the reusable form for every word-reading doom). -/
theorem wordK_stabX {L : Log} (hb : ¬ Bad L) {n : ℕ} (hci : G.IsChain L n) {X : Log}
    (hX : StabExt fsRnd4 (entriesOf L (pathOf L n)) X) {i : ℕ} (hi : i < 5) (κ : CKind)
    (hl : capPos i < X.length) : wordK κ (L.take n) X i = wordK κ L X i := by
  have hc := capOK_of_stabExt hci.2 hX hi hl
  obtain ⟨s0, r, as, -, -, -, rfl⟩ := hX
  exact wordK_stab hb hci (s0 + 1) as hi κ hc

/-- **Level `i`'s Hide state reads the same off the charging log** on `hloc_of`'s extensions:
before P1.i it holds on both sides (`noHide_zero`); after, the cap is real (`wordK_stabX`). -/
theorem noHide_stab {L : Log} (hb : ¬ Bad L) {n : ℕ} (hci : G.IsChain L n) {X : Log}
    (hX : StabExt fsRnd4 (entriesOf L (pathOf L n)) X) {i : ℕ} (hi : i < 5) (κ : CKind) :
    noHide κ (L.take n) X i ↔ noHide κ L X i := by
  by_cases h0 : hRnd X i = 0
  · exact ⟨fun _ => noHide_zero h0, fun _ => noHide_zero h0⟩
  have hl : capPos i < X.length := by
    have := capPos_lt hi; unfold hRnd at h0; omega
  have hw := wordK_stabX hb hci hX hi κ hl
  have hd := decodeL_congr hw
  unfold noHide hDiff farL
  rw [hw, hd]

/-! ## Part D: the Hide potential's step law at `ε_H` -/

/-- Every level's decoding radius fits `2^18` (level 0 of `L32`: `e₀ = 2^18`). -/
theorem lvE_le (κ : CKind) {i : ℕ} (hi : i < 5) : lvE κ i ≤ 2 ^ 18 := by
  rcases κ with (_|_|_) | (_|_|_) <;> interval_cases i <;> decide

theorem not_p1Sq_of_absorb {es : Log} {len : ℕ} (hit : fsItems4[es.length]? = some (.absorb len)) :
    ∀ i < 5, ∀ l < hEll i, es.length ≠ p1Start i + 2 * l + 1 := by
  intro i hi l hl he
  have := (p1_phase hi).hsq l hl
  rw [← he, hit] at this
  cases this

theorem not_p1Sq_of_rnd {p s0 r : ℕ} (h : fsRnd4 p = some (s0, r)) :
    ∀ i < 5, ∀ l < hEll i, p ≠ p1Start i + 2 * l + 1 := by
  intro i hi l hl he
  rcases (p1_phase hi).hph p s0 r h with h' | h' <;> omega

open Classical in
/-- **The Hide row** (A.10 P1.i, §10 changes 14): at P1.i's round-`l` squeeze, the other levels
keep their state (`p1_disj`), and an answer hides a disagreement only if its challenge `chK a`
makes one of the `≤ eᵢ` nonzero bound difference tables vanish (`mlDoom_step` over K,
`card_not_jointAgree`): at most `eᵢ ≤ 2^18` answers (`card_chK_fiber`). -/
theorem hide_single (L es : Log) {i₀ l : ℕ} (hi₀ : i₀ < 5) (hl : l < hEll i₀)
    (hp : es.length = p1Start i₀ + 2 * l + 1) :
    (univ.filter fun a => DH L es ∧ ¬ DH L (ext1 es a)).card ≤ 2 ^ 18 := by
  have h0 : 0 < es.length := by omega
  set κ := kindOfC es with hκ
  have hsub : (univ.filter fun a => DH L es ∧ ¬ DH L (ext1 es a)) ⊆
      univ.filter fun a => noHide κ L es i₀ ∧ ¬ noHide κ L (ext1 es a) i₀ := by
    intro a ha
    simp only [mem_filter, mem_univ, true_and] at ha ⊢
    obtain ⟨hd, hnd⟩ := ha
    refine ⟨hd i₀ hi₀, fun hn => hnd fun i hi => ?_⟩
    rw [kindOf_ext1 es a h0]
    by_cases hii : i = i₀
    · subst hii; exact hn
    · have hr : hRnd (ext1 es a) i = hRnd es i := hRnd_append es _ fun l' hl' he => by
        rcases p1_disj hi hi₀ hii with h | h <;> omega
      exact (noHide_append hi _ hr).mpr (hd i hi)
  refine (card_le_card hsub).trans ?_
  have hcap := capPos_lt hi₀
  have hA : ∀ a, Agree (ext1 es a) es es.length := fun a => agree_append es _ le_rfl
  have hw : ∀ a, wordK κ L (ext1 es a) i₀ = wordK κ L es i₀ := fun a => by
    funext r p; simp only [wordK, wordOf, colOf_congr κ L i₀ p ((hA a).mono (by omega))]
  have hkey : ∀ a, noHide κ L (ext1 es a) i₀ ↔ (¬ farL κ L es i₀ →
      ∀ j ∉ jointAgree (wordK κ L es i₀) (decodeL κ L es i₀),
        mlDoom (CKind.lv κ i₀).ell (hDiff κ L es i₀ j) (sList es i₀ l ++ [chK a])) := fun a => by
    unfold noHide hDiff farL
    rw [(hRnd_ext1 es a hl hp).2, sList_ext1 es a hp, hw a, decodeL_congr (hw a)]
  have hR : hRnd es i₀ = l := (hRnd_ext1 es default hl hp).1
  by_cases hf1 : farL κ L es i₀
  · rw [Finset.filter_false_of_mem fun a _ ha => ha.2 ((hkey a).mpr fun h2 => absurd hf1 h2)]
    simp
  by_cases hn : noHide κ L es i₀
  swap
  · rw [Finset.filter_false_of_mem fun a _ ha => hn ha.1]; simp
  set P := univ.filter fun j => j ∉ jointAgree (wordK κ L es i₀) (decodeL κ L es i₀)
  set S := univ.filter fun c : K => ∃ j ∈ P,
    ¬ mlDoom (CKind.lv κ i₀).ell (hDiff κ L es i₀ j) (sList es i₀ l ++ [c])
  have h1 : (univ.filter fun a => noHide κ L es i₀ ∧ ¬ noHide κ L (ext1 es a) i₀) ⊆
      univ.filter fun a : Digest => chK a ∈ S := by
    intro a ha
    simp only [mem_filter, mem_univ, true_and] at ha ⊢
    rw [hkey a] at ha
    by_contra hS
    refine ha.2 fun _ j hj => ?_
    by_contra hd
    exact hS (by simp only [S, P, mem_filter, mem_univ, true_and]; exact ⟨j, hj, hd⟩)
  have h2 : S.card ≤ P.card := by
    calc S.card ≤ (P.biUnion fun j => univ.filter fun c : K =>
          ¬ mlDoom (CKind.lv κ i₀).ell (hDiff κ L es i₀ j) (sList es i₀ l ++ [c])).card :=
          card_le_card fun c hc => by
            simp only [S, mem_filter, mem_univ, true_and] at hc
            obtain ⟨j, hj, h⟩ := hc
            exact mem_biUnion.mpr ⟨j, hj, by simp [h]⟩
      _ ≤ ∑ j ∈ P, (univ.filter fun c : K =>
          ¬ mlDoom (CKind.lv κ i₀).ell (hDiff κ L es i₀ j) (sList es i₀ l ++ [c])).card :=
          card_biUnion_le
      _ ≤ ∑ _j ∈ P, 1 := sum_le_sum fun j hj => by
          have hd := hn hf1 j (by simpa [P] using hj)
          rw [hR] at hd
          exact (mlDoom_step (hDiff_size κ L es i₀ j) _ hd).trans (by split <;> omega)
      _ = P.card := by simp
  calc _ ≤ (univ.filter fun a : Digest => chK a ∈ S).card := card_le_card h1
    _ = S.card := card_chK_fiber S
    _ ≤ P.card := h2
    _ ≤ lvE κ i₀ := card_not_jointAgree hf1
    _ ≤ 2 ^ 18 := lvE_le κ hi₀

open Classical in
/-- **The Hide doom's five obligations** at `δ = 2^-238`, `N = 2^18`: off P1's round squeezes the
doom does not move (`DH_append_iff`), so absorbs, middle squeezes and the multi-squeeze phases
cost nothing; P1's squeezes are `hide_single`; the reads are stable (`noHide_stab`). -/
theorem hide_obl : StepObl DH fsRnd4 ((2 : ℝ≥0)⁻¹ ^ 238) (2 ^ 18) where
  habs L es x len _ hit hd := (DH_append_iff x (not_p1Sq_of_absorb hit)).mpr hd
  hmid L es x s0 r _ hr _ := DH_append_iff x (not_p1Sq_of_rnd hr)
  hsingle L es _ _ _ := by
    by_cases h : ∃ i < 5, ∃ l < hEll i, es.length = p1Start i + 2 * l + 1
    · obtain ⟨i, hi, l, hl, hp⟩ := h
      exact hide_single L es hi hl hp
    · push Not at h
      rw [Finset.filter_false_of_mem fun a _ ha => ha.2 ((DH_append_iff _ h).mpr ha.1)]
      simp
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
    have hq := not_p1Sq_of_rnd (hspec (s0 + r) (by omega) le_rfl).2
    rw [← hdl] at hq
    have := (DH_append_iff ((ext es₀ as).getLast hne) hq).mpr hd
    rw [List.dropLast_append_getLast hne] at this
    exact hnd this
  hstab L n hb hci X hX := forall₂_congr fun i hi => noHide_stab hb hci hX hi _

open Classical in
/-- **`μ_Hide`'s step law** (§10 changes 15): the library's `KState.step` law with error
`ε_H = 2^-142 + 2^-238` for `muG DH (pRoundG DH fsRnd4)`. -/
theorem hide_step (L : Log) (q : ByteArray) (hl : L.length < logCap)
    (hμ : G.muG DH (pRoundG DH fsRnd4) L < 1) (hq : q ∉ L.map Prod.fst) :
    ∑ a : Digest, G.muG DH (pRoundG DH fsRnd4) (L ++ [(q, a)]) ≤
      (G.muG DH (pRoundG DH fsRnd4) L + epsH) * 2 ^ 256 :=
  (G.muG_step_of fsRnd4_ok fsRnd4_zero _ _ hide_N_le hide_obl.habs hide_obl.hmid hide_obl.hsingle
    hide_obl.hround hide_obl.hstab hl hμ hq).trans (by gcongr; exact err_le_epsH)

/-! ## Part E: at P1.i's end, `noHide` is `¬ Hide_i` -/

theorem sList_length (es : Log) (i l : ℕ) : (sList es i l).length = l := by simp [sList]

/-- With all `ℓ` challenges bound, the table's value is the `eq(sᵢ, ·)`-weighted row sum. -/
theorem bindL_sList {ℓ : ℕ} {t : Array K} (ht : t.size = 2 ^ ℓ) (es : Log) (i : ℕ) :
    tbl 0 (bindL t (sList es i ℓ)) 0 = ∑ u : Fin (2 ^ ℓ), eqBits (sAt es i) ℓ u * tbl ℓ t u := by
  rw [bindL_mle _ _ (by rw [ht, sList_length]), ← mleEval_eq,
    mleEval_eq' t _ (sList_length es i ℓ), mle]
  refine sum_congr rfl fun u _ => ?_
  have : (fun v : Fin ℓ => sAt es i (v : ℕ)) = ptOf ℓ (sList es i ℓ) := by
    funext v
    simp only [ptOf, sList, List.getD_eq_getElem?_getD, List.getElem?_map,
      List.getElem?_range v.isLt, Option.map_some, Option.getD_some]
  rw [eqBits_eq_eq, this]

/-- **`noHide` at P1.i's end is `¬ Hide_i`** (A.10 P1.i): with every round answered and a close
word, no disagreeing column's fold vanishes. -/
theorem noHide_full {κ : CKind} {L es : Log} {i : ℕ} (hi : i < 5) (hR : hRnd es i = hEll i)
    (hfar : ¬ farL κ L es i) (hn : noHide κ L es i) : ¬ hideL κ L es i := by
  rintro ⟨j, hj, hz⟩
  have hd := hn hfar j hj
  rw [hR, ← lvl_ell κ hi, mlDoom, List.take_of_length_le (by rw [sList_length]),
    sList_length, Nat.sub_self] at hd
  refine hd (funext fun u => ?_)
  obtain ⟨u, hu⟩ := u
  obtain rfl : u = 0 := by simp at hu; omega
  rw [Pi.zero_apply, show (⟨0, hu⟩ : Fin (2 ^ 0)) = 0 from rfl,
    bindL_sList (hDiff_size κ L es i j), tbl_hDiff]
  exact hz

/-- **What `final` gets from `μ_Hide`** (§10 changes 14–15, S-H2 Part 11 Q2): on a chain past
P1.i whose Hide doom holds (no escape of `μ_Hide`), a close level whose next message is the fold
has `A_c = jointAgree` (`consSet_eq_jointAgree`). -/
theorem consSet_eq_of_DH {L es : Log} {i : ℕ} (hi : i < 5)
    (hlen : p1Start i + 2 * hEll i ≤ es.length) (hD : DH L es)
    (hfar : ¬ farL (kindOfC es) L es i) (hC : truthC (kindOfC es) L es i) :
    consSet (kindOfC es) L es i =
      jointAgree (wordK (kindOfC es) L es i) (decodeL (kindOfC es) L es i) :=
  consSet_eq_jointAgree hi hfar hC (noHide_full hi (by unfold hRnd; omega) hfar (hD i hi))

/-! ## Part F: the entry's potential `μ = μ_doom + μ_Hide` and its step law at `εR` -/

/-- **The entry's potential** (§10 changes 15): the doom potential of `DC Rej (Dp Dk)` plus the
Hide potential. -/
noncomputable def muT (Rej : Log → Log → Prop) (Dk : ℕ → Log → Log → Prop) (L : Log) : ℝ≥0 :=
  G.muG (DC Rej (Dp Dk)) (pRoundG (DC Rej (Dp Dk)) fsRnd4) L + G.muG DH (pRoundG DH fsRnd4) L

theorem muT_empty (Rej : Log → Log → Prop) (Dk : ℕ → Log → Log → Prop) : muT Rej Dk [] = 0 := by
  simp only [muT, G.muG_empty, add_zero]

open Classical in
/-- **`KState.step` at `εR` for the entry's potential** (BLUEPRINT §5.1, §10 changes 15):
`kstate_step` (`εD`) and `hide_step` (`ε_H`) through `step_add`, with `εD + ε_H = εR`. -/
theorem muT_step {Rej : Log → Log → Prop} {Dk : ℕ → Log → Log → Prop} {N : ℕ}
    (hN : (N : ℝ≥0) ≤ 2 ^ 256 * deltaR) (ob : PhaseObl Rej Dk N) (L : Log) (q : ByteArray)
    (hl : L.length < logCap) (hμ : muT Rej Dk L < 1) (hq : q ∉ L.map Prod.fst) :
    ∑ a : Digest, muT Rej Dk (L ++ [(q, a)]) ≤ (muT Rej Dk L + epsR) * 2 ^ 256 := by
  have h := step_add (fun L q hl hμ hq => kstate_step hN ob L q hl hμ hq)
    (fun L q hl hμ hq => hide_step L q hl hμ hq) L q hl hμ hq
  rwa [epsD_add_epsH] at h

/-- Below `1`, neither potential has escaped and the log is not bad. -/
theorem muT_lt_one {Rej : Log → Log → Prop} {Dk : ℕ → Log → Log → Prop} {L : Log}
    (h : muT Rej Dk L < 1) :
    ¬ Bad L ∧ ¬ G.EscG (DC Rej (Dp Dk)) L ∧ ¬ G.EscG DH L := by
  have h1 := G.muG_lt_one _ _ (lt_of_le_of_lt le_self_add h)
  have h2 := G.muG_lt_one _ _ (lt_of_le_of_lt le_add_self h)
  exact ⟨h1.1, h1.2, h2.2⟩

/-! ## Controls -/

/-- Control (positive): before P1.0's first answer every chain satisfies the Hide doom. -/
theorem DH_seed (L : Log) (e : ByteArray × Digest) : DH L [e] :=
  DH_short (by
    have := (p1_phase (i := 0) (by norm_num)).hb1; simp only [List.length_singleton]; omega)

/-- Control (negative): a hidden disagreement at P1.i's end refutes `noHide`, so the Hide doom is
not vacuous. -/
theorem not_noHide_of_hideL {κ : CKind} {L es : Log} {i : ℕ} (hi : i < 5)
    (hR : hRnd es i = hEll i) (hfar : ¬ farL κ L es i)
    (hH : hideL κ L es i) : ¬ noHide κ L es i :=
  fun hn => noHide_full hi hR hfar hn hH

/-- Control (negative): a formal extension past the chain has no real cap entry. -/
theorem not_capOK_ext (es₀ : Log) (as : List Digest) {i : ℕ} (h : es₀.length ≤ capPos i) :
    ¬ capOK (ext es₀ as) i := by
  rintro ⟨len, -, hc⟩
  rw [fsCheck_ext_ge es₀ as h] at hc
  cases hc

end FR.Snd.T4

