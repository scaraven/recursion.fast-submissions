-- New for `flock-recursive` (BLUEPRINT A.9 `finSh`, A.10 S1/S2, §5.2 row S; stage S-G7).
import FRSoundnessFrSh

/-!
# S on the log: S1's charge, S2's rounds, and S's pending RS claim (positions 98 … 169)

S1 is the multi-squeeze phase `(98, 15)` (positions 99 … 113): `τ` is coordinates `0 …` (the
kind's `nb = m − 14` are read, 18 drawn), `θ` coordinates `18 … 27`, `κ_s` coordinate 28. S2 is
`nb + 10` product rounds of degree 2 from 114 (`D2`, F, `wd = 16`); for P30/N30 the last two of
the 28 slots are dummies. Then Lr1 (169, 8) starts.

* Readers: `coS` (S1's coordinates), **`tauL`**, **`thL`**, **`ksL`**; S2's challenges **`rbL`**,
  **`rpL`**; the leaf's boundary **`bndL`** (`hdr` bytes 16–47 in the seed query, `stmt` bytes 1–32),
  its bits `sbL`, `hbL`.
* **`c0S`**: S2's initial claim, A.9 `finSh` (i) on the specifications (`shiftTargetS`).
* **`TS`** `= [W, z]` (the S2 weight of `FRSoundnessFrSh` at S1's challenges, and `z` at the block
  positions `< 2^10`); **`trueSum_TS`**: its true sum is `c0S` plus the residual.
* **`truthS`** (the S truth by kind: `truthS1N` or `ShHoldsL`), **`S2Bad`** (S1's final doom),
  **`s1_hfin`** (S1's charge `≤ (nb + 10 + J − 1)/2^128`, §5.2's `26 + 9` on a node).
-/

namespace FR.Snd
open RecursionFast Finset FR.Impl FR.NodeT FR.NodeI

set_option linter.constructorNameAsVariable false

/-! ## Positions -/

/-- **S's positions** (A.4): S1 is the range `(98, 15)` (phase 11), S2's rounds from 114 (phase
12), Lr1's range `(169, 8)` (phase 13). -/
theorem s_unit_pos :
    (98, 15) ∈ fsRanges ∧ phOf 98 = 10 ∧ phOf 99 = 11 ∧ phOf 113 = 11 ∧ phOf 114 = 12 ∧
    phOf 169 = 12 ∧ phOf 170 = 13 := by
  refine ⟨by rw [fsRanges_eq]; simp, ?_⟩
  have hph : ∀ q, phOf q = (fsStarts.filter (· ≤ q)).length - 1 := fun _ => rfl
  simp only [hph, fsStarts_eq]
  exact ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩

/-! ## Readers -/

/-- The kind's block coordinates `nb = m − 14`. -/
def nbS (κ : Kind) : ℕ := κ.m - 14

theorem nbS_le (κ : Kind) : nbS κ ≤ 18 := by cases κ <;> decide

theorem nbS_node {κ : Kind} (h : κ.isNode = true) : nbS κ = 16 := by
  cases κ <;> simp_all [Kind.isNode] <;> rfl

/-- S1's coordinate `j`. -/
def coS (es : Log) (j : ℕ) : F := coordAt es 98 j

/-- S1's `τ` (the kind's `nb` read coordinates), `θ` (coordinates 18 … 27), `κ_s` (28). -/
def tauL (κ : Kind) (es : Log) : List F := (List.range (nbS κ)).map (coS es)
def thL (es : Log) : List F := (List.range 10).map fun l => coS es (18 + l)
def ksL (es : Log) : F := coS es 28

/-- S2's challenges: the block part `r_blk` (`nb`), the position part `r_pos` (10). -/
def rbL (κ : Kind) (es : Log) : List F := (List.range (nbS κ)).map (rch 114 es)
def rpL (κ : Kind) (es : Log) : List F := (List.range 10).map fun l => rch 114 es (nbS κ + l)

/-- **The shift's boundary values** (A.9 `bndOps`): a leaf's `s` (`hdr` bytes 16–47, at 87 in the
seed query) and `h` (`stmt` bytes 1–32); a node's are `0`. -/
def bndL (κ : Kind) (es : Log) : List F :=
  if κ.isNode then [0, 0, 0, 0] else
    [readF (entAt es 0).1 87, readF (entAt es 0).1 103, readF (msgAt es 1) 1, readF (msgAt es 1) 17]

/-- The start digest's bit `σ` and the end digest's (`digBit`). -/
def sbL (κ : Kind) (es : Log) (σ : ℕ) : F :=
  if digBit ((bndL κ es).getD 0 0) ((bndL κ es).getD 1 0) σ then 1 else 0
def hbL (κ : Kind) (es : Log) (σ : ℕ) : F :=
  if digBit ((bndL κ es).getD 2 0) ((bndL κ es).getD 3 0) σ then 1 else 0

/-- A list padded to 18 coordinates (`padB`). -/
def pad18 (κ : Kind) (xs : List F) : Array F := (xs ++ List.replicate (18 - nbS κ) 0).toArray

/-- **S2's initial claim** (A.9 `finSh` (i), on `shiftTarget`'s specification). -/
def c0S (es : Log) : F :=
  shiftTargetS (ksL es) (pad18 (kindOf es) (tauL (kindOf es) es)) (thL es).toArray
    (bndL (kindOf es) es ++ lastPad (nbS (kindOf es)) (18 - nbS (kindOf es))).toArray

/-! ## The target and the tables -/

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

theorem tauL_length (κ : Kind) (es : Log) : (tauL κ es).length = nbS κ := by simp [tauL]
theorem thL_length (es : Log) : (thL es).length = 10 := by simp [thL]
theorem rbL_length (κ : Kind) (es : Log) : (rbL κ es).length = nbS κ := by simp [rbL]
theorem rpL_length (κ : Kind) (es : Log) : (rpL κ es).length = 10 := by simp [rpL]

/-- **S2's initial claim in the residual's terms**: a leaf's `eq(τ, last) h̃(θ) + κ_s s̃(θ)`, a
node's `0`. -/
theorem c0S_eq (es : Log) : c0S es = if (kindOf es).isNode then 0 else
    eqAtR (ptOf (nbS (kindOf es)) (tauL (kindOf es) es)) (2 ^ nbS (kindOf es) - 1) *
        thS (ptOf 10 (thL es)) (hbL (kindOf es) es) +
      ksL es * thS (ptOf 10 (thL es)) (sbL (kindOf es) es) := by
  rw [c0S, pad18]
  generalize kindOf es = κ
  have hb : (bndL κ es).length = 4 := by unfold bndL; split_ifs <;> rfl
  rw [shiftTargetS_pad (ksL es) _ (show nbS κ + (18 - nbS κ) = 18 by
    have := nbS_le κ; omega) _ _ (tauL_length κ es) hb, shiftTarget, mle_digTbl, mle_digTbl,
    ptA_toArray, eq_cube_eqAtR]
  have hl : (lastBlk (nbS κ)).val = 2 ^ nbS κ - 1 := rfl
  rw [hl]
  split_ifs with hn
  · simp only [bndL, hn, if_true, List.getD_cons_zero, List.getD_cons_succ, digBit_zero,
      Bool.false_eq_true, if_false, thS, mul_zero, sum_const_zero, add_zero]
  · rfl

/-- **S2's weight** at S1's challenges, cell `(y, q)` (a node's or a leaf's). -/
def wS (κ : Kind) (es : Log) (y q : ℕ) : F :=
  if κ.isNode then wNode (ptOf 16 (tauL κ es)) (ptOf 10 (thL es)) (ksL es) y q
  else wLeaf (ptOf (nbS κ) (tauL κ es)) (ptOf 10 (thL es)) (ksL es) y q

/-- **S2's tables** `[W, z]` over `2^(nb + 10)` cells, index `y + 2^nb q` (block bits first). -/
noncomputable def TS (L es : Log) : Array (Array F) :=
  #[Array.ofFn (n := 2 ^ (nbS (kindOf es) + 10)) fun i =>
      wS (kindOf es) es (i.val % 2 ^ nbS (kindOf es)) (i.val / 2 ^ nbS (kindOf es)),
    Array.ofFn (n := 2 ^ (nbS (kindOf es) + 10)) fun i =>
      zNode (kindOf es) L es (i.val % 2 ^ nbS (kindOf es)) (i.val / 2 ^ nbS (kindOf es))]

/-- S2's round count `nb + 10` (`mm 4`). -/
def nrS (κ : Kind) : ℕ := nbS κ + 10

theorem nrS_eq (κ : Kind) : nrS κ = mm 4 κ := by cases κ <;> rfl

theorem idx_split {a y q : ℕ} (hy : y < 2 ^ a) :
    (y + 2 ^ a * q) % 2 ^ a = y ∧ (y + 2 ^ a * q) / 2 ^ a = q := by
  refine ⟨by rw [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hy], ?_⟩
  rw [Nat.add_mul_div_left _ _ (Nat.two_pow_pos a), Nat.div_eq_of_lt hy, zero_add]

/-- The S residual by kind: a node's `J = 10` tables, a leaf's `2`. -/
noncomputable def resS (κ : Kind) (L es : Log) (j u q : ℕ) : F :=
  if κ.isNode then resNode (zNode κ L es) j u q
  else resLeaf (nbS κ) (zNode κ L es) (sbL κ es) (hbL κ es) j u q

def nJ (κ : Kind) : ℕ := if κ.isNode then nLinkFam + 2 else 2

/-- **S2's true sum** is its initial claim plus the residual `Σ_j κ_s^j R̃_j(τ, θ)`. -/
theorem trueSum_TS (L es : Log) :
    trueSum innerExpr (TS L es) (nrS (kindOf es)) = c0S es +
      resSum (nbS (kindOf es)) (nJ (kindOf es)) (resS (kindOf es) L es)
        (ptOf (nbS (kindOf es)) (tauL (kindOf es) es)) (ptOf 10 (thL es)) (ksL es) := by
  rw [nrS, TS, prod_trueSum]
  rw [Fin.sum_univ_eq_sum_range (fun i => wS (kindOf es) es (i % 2 ^ nbS (kindOf es))
      (i / 2 ^ nbS (kindOf es)) * zNode (kindOf es) L es (i % 2 ^ nbS (kindOf es))
        (i / 2 ^ nbS (kindOf es))), sum_range_pow_add]
  have e : ∀ q ∈ range (2 ^ 10), ∑ y ∈ range (2 ^ nbS (kindOf es)),
      wS (kindOf es) es ((y + 2 ^ nbS (kindOf es) * q) % 2 ^ nbS (kindOf es))
          ((y + 2 ^ nbS (kindOf es) * q) / 2 ^ nbS (kindOf es)) *
        zNode (kindOf es) L es ((y + 2 ^ nbS (kindOf es) * q) % 2 ^ nbS (kindOf es))
          ((y + 2 ^ nbS (kindOf es) * q) / 2 ^ nbS (kindOf es)) =
      ∑ y ∈ range (2 ^ nbS (kindOf es)), wS (kindOf es) es y q * zNode (kindOf es) L es y q :=
    fun q _ => sum_congr rfl fun y hy => by
      obtain ⟨h1, h2⟩ := idx_split (q := q) (mem_range.1 hy); rw [h1, h2]
  rw [sum_congr rfl e, c0S_eq]
  generalize kindOf es = κ
  unfold wS resS nJ
  split_ifs with hn
  · rw [nbS_node hn, zero_add]
    exact sh_sum_node (ptOf 16 (tauL κ es)) (ptOf 10 (thL es)) (ksL es) (zNode κ L es)
  · exact sh_sum_leaf _ _ _ _ _ _

/-! ## S1: the truth, its final doom and its charge -/

/-- **The S truth** by kind (A.10 S1): a node's `truthS1N` (chain-masked links and families), a
leaf's `ShHoldsL` with the statement's boundary digests. -/
def truthSK (κ : Kind) (L es : Log) : Prop :=
  if κ.isNode then truthS1N κ L es else ShHoldsL (nbS κ) (zNode κ L es) (sbL κ es) (hbL κ es)

def truthS (L es : Log) : Prop := truthSK (kindOf es) L es

/-- **S1's final doom**: S2's initial claim is not the true sum at S1's challenges. -/
noncomputable def S2Bad (L es : Log) : Prop := c0S es ≠ trueSum innerExpr (TS L es) (nrS (kindOf es))

/-- The residual tables `R_j` as arrays (index `u + 2^nb q`). -/
noncomputable def TR (κ : Kind) (L es : Log) (j : ℕ) : Array F :=
  Array.ofFn (n := 2 ^ (nbS κ + 10)) fun i => resS κ L es j (i.val % 2 ^ nbS κ) (i.val / 2 ^ nbS κ)

theorem TR_size (κ : Kind) (L es : Log) (j : ℕ) : (TR κ L es j).size = 2 ^ (nbS κ + 10) := by
  simp [TR]

theorem TR_mle (κ : Kind) (L es : Log) (j : ℕ) (l : List F) :
    mle (tbl (nbS κ + 10) (TR κ L es j)) (ptOf (nbS κ + 10) l) =
      ∑ q ∈ range (2 ^ 10), ∑ u ∈ range (2 ^ nbS κ),
        eqAtR (ptOf (nbS κ) l) u * eqAtR (ptOf 10 (l.drop (nbS κ))) q * resS κ L es j u q := by
  rw [TR]
  refine (mle_ofFn_split _ 10 (fun i => resS κ L es j (i % 2 ^ nbS κ) (i / 2 ^ nbS κ)) l).trans ?_
  exact sum_congr rfl fun q _ => sum_congr rfl fun u hu => by
    obtain ⟨h1, h2⟩ := idx_split (q := q) (mem_range.1 hu); rw [h1, h2]

/-- **A failed S truth leaves a nonzero residual table.** -/
theorem tr_ne {κ : Kind} {L es : Log} (h : ¬ truthSK κ L es) :
    ∃ j < nJ κ, tbl (nbS κ + 10) (TR κ L es j) ≠ 0 := by
  have key : ∀ j u q, u < 2 ^ nbS κ → q < 2 ^ 10 → resS κ L es j u q ≠ 0 →
      tbl (nbS κ + 10) (TR κ L es j) ≠ 0 := fun j u q hu hq hne he => by
    have hi : u + 2 ^ nbS κ * q < 2 ^ (nbS κ + 10) := by
      rw [pow_add]; nlinarith
    have := congrFun he ⟨u + 2 ^ nbS κ * q, hi⟩
    obtain ⟨h1, h2⟩ := idx_split (q := q) hu
    simp only [TR, tbl_ofFn, Pi.zero_apply, h1, h2] at this
    exact hne this
  unfold truthSK at h
  unfold nJ
  split_ifs at h ⊢ with hn
  · obtain ⟨j, hj, u, hu, q, hq, hne⟩ := res_ne_node h
    have hne' : resS κ L es j u q ≠ 0 := by simp only [resS, hn, if_true]; exact hne
    exact ⟨j, hj, key j u q (by rw [nbS_node hn]; exact hu) hq hne'⟩
  · obtain ⟨j, hj, u, hu, q, hq, hne⟩ := res_ne_leaf h
    have hne' : resS κ L es j u q ≠ 0 := by simp only [resS, hn, if_false]; exact hne
    exact ⟨j, hj, key j u q hu hq hne'⟩

/-! ### Reads -/

section Reads
variable {L es L' es' : Log} {p : ℕ}

theorem bndL_congr (h : Agree es es' p) (hp : 2 ≤ p) (κ : Kind) : bndL κ es = bndL κ es' := by
  simp only [bndL, h 0 (by omega), msgAt_congr h (show 1 < p by omega)]

theorem coS_congr (h : Agree es es' p) {j : ℕ} (hj : 99 + j / 2 < p) : coS es j = coS es' j := by
  simp only [coS, coordAt]; exact fAt_congr h (by omega) _

theorem s1_congr (h : Agree es es' p) (hp : 114 ≤ p) (κ : Kind) :
    tauL κ es = tauL κ es' ∧ thL es = thL es' ∧ ksL es = ksL es' := by
  have hn := nbS_le κ
  refine ⟨List.map_congr_left fun l hl => coS_congr h (by simp at hl; omega),
    List.map_congr_left fun l hl => coS_congr h (by simp at hl; omega), coS_congr h (by omega)⟩

theorem c0S_agree (h : Agree es es' p) (hp : 114 ≤ p) : c0S es = c0S es' := by
  have hk : kindOf es = kindOf es' := kindOf_congr (h.mono (by omega))
  obtain ⟨h1, h2, h3⟩ := s1_congr h hp (kindOf es)
  simp only [c0S, hk, ← h1, h2, h3, bndL_congr h (by omega)]
  rw [← hk, h1]

theorem zNode_same (h : Same L es L' es' p) (hp : 3 ≤ p) (κ : Kind) :
    zNode κ L es = zNode κ L' es' := by
  funext b q; simp only [zNode, zW_same h hp κ]

theorem resS_same (h : Same L es L' es' p) (hp : 3 ≤ p) (κ : Kind) :
    resS κ L es = resS κ L' es' := by
  have hb := bndL_congr h.1 (by omega : 2 ≤ p) κ
  have hs : sbL κ es = sbL κ es' := by funext σ; unfold sbL; rw [hb]
  have hh : hbL κ es = hbL κ es' := by funext σ; unfold hbL; rw [hb]
  funext j u q
  simp only [resS, zNode_same h hp κ, hs, hh]

theorem TS_same (h : Same L es L' es' p) (hp : 114 ≤ p) : TS L es = TS L' es' := by
  have hk := h.kind (by omega)
  obtain ⟨h1, h2, h3⟩ := s1_congr h.1 hp (kindOf es)
  simp only [TS, wS, hk, zNode_same h (by omega), ← h1, h2, h3]
  rw [← hk, h1]

end Reads

/-! ### The charge -/

theorem coordS_getD (X : Log) {j : ℕ} (hj : j < 30) :
    (List.ofFn fun i : Fin (15 * 2) => coordAt X 98 i).getD j 0 = coS X j := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_ofFn, dif_pos (by omega)]; rfl

theorem selC_coords (κ : Kind) (X : Log) :
    ptOf (nbS κ) (selC (nbS κ) (List.ofFn fun i : Fin (15 * 2) => coordAt X 98 i)) =
        ptOf (nbS κ) (tauL κ X) ∧
      ptOf 10 ((selC (nbS κ) (List.ofFn fun i : Fin (15 * 2) => coordAt X 98 i)).drop (nbS κ)) =
        ptOf 10 (thL X) := by
  have hn := nbS_le κ
  set cl := List.ofFn fun i : Fin (15 * 2) => coordAt X 98 i
  have hcl : cl.length = 30 := by simp [cl]
  have hd : (selC (nbS κ) cl).drop (nbS κ) = (cl.drop 18).take 10 := by
    rw [selC, List.drop_left' (by simp; omega)]
  refine ⟨funext fun l => ?_, funext fun l => ?_⟩
  · have hl := l.isLt
    simp only [ptOf, selC, List.getD_eq_getElem?_getD]
    rw [List.getElem?_append_left (by simp; omega), List.getElem?_take, if_pos hl,
      ← List.getD_eq_getElem?_getD, coordS_getD X (by omega)]
    simp [tauL, List.getD_eq_getElem?_getD, hl]
  · have hl := l.isLt
    simp only [ptOf, hd, List.getD_eq_getElem?_getD]
    rw [List.getElem?_take, if_pos hl, List.getElem?_drop, ← List.getD_eq_getElem?_getD,
      coordS_getD X (by omega)]
    simp [thL, List.getD_eq_getElem?_getD, hl]

open Classical in
/-- **S1's charge** (A.10 S1, §5.2: `(nb + 10 + J − 1)/2^128`, a node's `16 + 10 + 9 = 35`): with
the doom of S1's entry `Bg ∨ ¬ truthS` and its final doom `Bg ∨ S2Bad`. -/
theorem s1_hfin {Dk : ℕ → Log → Log → Prop} {Bg : Log → Log → Prop} (hBg : Reads 99 Bg)
    (hprev : Dk (phOf 98) = fun L es => Bg L es ∨ ¬ truthS L es)
    (hfin : Dk (phOf 99) = msD (Dk (phOf 98)) (fun L es => Bg L es ∨ S2Bad L es) 98 15)
    (L es₀ : Log) (hl : es₀.length = 99) : condCount (DPos (Dp Dk)) L es₀ 15 [] ≤ deltaR := by
  set κ := kindOf es₀
  have hn := nbS_le κ
  have hJ : 1 ≤ nJ κ := by unfold nJ; split_ifs <;> decide
  by_cases hd : ¬ truthS L es₀
  · have h0 : DoomS (nbS κ) (nJ κ) (TR κ L es₀) [] := by
      obtain ⟨j, hj, hne⟩ := tr_ne hd
      unfold DoomS
      rw [if_pos (by simp)]
      refine ⟨j, hj, ?_⟩
      have hs : selC (nbS κ) ([] : List F) = [] := by simp [selC]
      unfold mlDoom
      rw [hs]
      exact hne
    refine (seq_round_le hl (DoomS (nbS κ) (nJ κ) (TR κ L es₀)) (bS (nbS κ) (nJ κ))
      (fun l hdl => doomS_step hn hJ (TR_size κ L es₀) l hdl) h0 fun as has he => ?_).trans
      (coord_le_deltaR ?_)
    · obtain ⟨-, -, hnf⟩ := esc_msD_frame s_unit_pos.1 hBg hprev hfin hl as has he
      set X := ext es₀ as
      obtain ⟨ys, hy⟩ := ext_eq_append es₀ as
      have hS : Same L X L es₀ 99 := by rw [show X = es₀ ++ ys from hy, ← hl]; exact same_append L es₀ ys
      have hk : kindOf X = κ := hS.kind (by norm_num)
      have hX : X.length = 114 := by simp [X, length_ext, hl, has]
      have hres := trueSum_TS L X
      rw [not_not.mp hnf |>.symm] at hres
      have hr0 := add_eq_left.mp hres.symm
      rw [hk, resS_same hS (by norm_num)] at hr0
      unfold resSum at hr0
      unfold DoomS
      rw [if_neg (by simp), not_not]
      simp only [TR_mle]
      rw [(selC_coords κ X).1, (selC_coords κ X).2, coordS_getD X (by norm_num : 28 < 30)]
      exact hr0
    · rw [sum_bS hn]; unfold nJ nLinkFam; split_ifs <;> omega
  · rw [condCount_eq_zero fun as has he =>
      hd (esc_msD_frame s_unit_pos.1 hBg hprev hfin hl as has he).2.1]
    exact zero_le

/-! ## S2: the rounds (positions 114 … 169) -/

/-- S2's initial claim as a `D2` claim (it reads no log word). -/
def c0SL (_L es : Log) : F := c0S es

/-- **S2's rounds' doom** (`D2`, F, degree 2, from 114, `nb + 10` real rounds). -/
abbrev D2S : Log → Log → Prop :=
  D2 114 16 readF (fun d => chF d 0) c0SL nrS innerExpr TS

/-- **S2's round checks fail** (the verifier's `c₁ + c₂ = claim` asserts). -/
def RejS2 (L es : Log) : Prop :=
  ∃ l < nrS (kindOf es), 114 + 2 * l < es.length ∧
    ¬ Chk2 114 16 readF (fun d => chF d 0) c0SL L es l

theorem nrS_le (κ : Kind) : nrS κ ≤ 28 := by have := nbS_le κ; unfold nrS; omega

theorem TS_local : TruthLocal2 114 c0SL TS := fun L es es' h =>
  ⟨TS_same (same_of_agree L h) le_rfl, c0S_agree h le_rfl⟩

theorem TS_size (L es : Log) : ∀ t ∈ TS L es, t.size = 2 ^ nrS (kindOf es) := by
  simp [TS, nrS]

/-- **Into S2** (`habs` at 114): S1's final doom is S2's doom at its first absorb. -/
theorem habs_S2 {L es : Log} (x : ByteArray × Digest) (hl : es.length = 114)
    (hb : S2Bad L es) : D2S L (es ++ [x]) := by
  have hS := same_append L es [x]
  have hk : kindOf (es ++ [x]) = kindOf es := hS.kind (by omega)
  refine ⟨by simp; omega, ?_⟩
  have ha0 : ans3 114 nrS (es ++ [x]) = 0 := by
    simp only [ans3, List.length_append, List.length_singleton, hl]; simp
  rw [ha0]
  simp only [Wrong2, clR2, rchs2, List.range_zero, List.map_nil, bindAll, Nat.sub_zero]
  rw [TS_same (hl ▸ hS) le_rfl, hk, c0SL, c0S_agree (hl ▸ hS).1 le_rfl]
  exact hb

open Classical in
/-- **S2's squeezes** (A.10 S2, §5.2: `2·2^128`). -/
theorem single_S2 (L es : Log)
    (hchk : ∀ j, es.length = 114 + 2 * j + 1 → j < nrS (kindOf es) →
      Chk2 114 16 readF (fun d => chF d 0) c0SL L es j) :
    (univ.filter fun d => D2S L es ∧ ¬ D2S L (ext1 es d)).card ≤ 2 * 2 ^ 128 :=
  D2_single (by omega) TS_local innerExpr_deg card_chF_fiber TS_size L es hchk

theorem chk_of_not_rejS2 {L es : Log} (hr : ¬ RejS2 L es) (j : ℕ)
    (hj : es.length = 114 + 2 * j + 1) (hjn : j < nrS (kindOf es)) :
    Chk2 114 16 readF (fun d => chF d 0) c0SL L es j := by
  by_contra hc; exact hr ⟨j, hjn, by omega, hc⟩

/-- An S2 round's absorb keeps the doom. -/
theorem append_S2 {L es : Log} (x : ByteArray × Digest) (hlen : 114 < es.length)
    (hc : (es.length - 114) % 2 = 0 ∨ nrS (kindOf es) ≤ (es.length - 114) / 2) :
    D2S L (es ++ [x]) ↔ D2S L es :=
  D2_append_iff (by omega) TS_local x hlen hc

theorem chkS_same {L L' es es' : Log} {p : ℕ} (h : Same L es L' es' p) {j : ℕ}
    (hj : 114 + 2 * j < p) :
    Chk2 114 16 readF (fun d => chF d 0) c0SL L es j ↔
      Chk2 114 16 readF (fun d => chF d 0) c0SL L' es' j := by
  have hg : g2At 114 16 readF es j = g2At 114 16 readF es' j := by
    simp only [g2At, msgAt, h.1 (114 + 2 * j) hj]
  have hc0 : c0SL L es = c0SL L' es' := c0S_agree (h.1.mono (by omega)) (le_refl 114)
  have hc := clR2_same (b := 114) (wd := 16) (rd := readF) (ch := fun d => chF d 0)
    (c0 := c0SL) hc0 (l := j) (h.1.mono (by omega))
  simp only [Chk2, hg, hc]

theorem rejS2_mono {L es : Log} (x : ByteArray × Digest) (h : RejS2 L es) :
    RejS2 L (es ++ [x]) := by
  obtain ⟨j, hj, hlt, hc⟩ := h
  have hS := same_append L es [x]
  refine ⟨j, by rw [hS.kind (by omega)]; exact hj, by simp; omega, fun h' => hc ?_⟩
  exact (chkS_same hS (by omega)).mp h'

/-- **`RejOK` for S2's round checks**, given that their messages are absorbs. -/
theorem rejS2_ok (habs2 : ∀ j < 28, fsItems[114 + 2 * j]? ≠ some .squeeze) : RejOK RejS2 where
  mono L es x := rejS2_mono x
  sq L es x hit := by
    refine ⟨fun ⟨j, hj, hlt, hc⟩ => ?_, rejS2_mono x⟩
    simp only [List.length_append, List.length_singleton] at hlt
    have hS := same_append L es [x]
    rw [hS.kind (by omega)] at hj
    by_cases he : 114 + 2 * j = es.length
    · exact absurd (he ▸ hit) (habs2 j (lt_of_lt_of_le hj (nrS_le _)))
    exact ⟨j, hj, by omega, fun h' => hc ((chkS_same hS (by omega)).mpr h')⟩
  stab L i hb hci X hX := by
    have hS := same_stabX hb hci hX
    by_cases h0 : X.length = 0
    · constructor <;> rintro ⟨j, -, hlt, -⟩ <;> omega
    unfold RejS2
    rw [hS.kind (by omega)]
    exact exists_congr fun j => and_congr_right fun _ => and_congr_right fun _ =>
      not_congr (chkS_same hS (by omega))

/-- **Once every S2 round is answered, S2's doom reads before 170.** -/
theorem D2S_reads : Reads 170 D2S := fun L es L' es' h1 h2 h => by
  have hk := h.kind (by omega)
  have hn := nrS_le (kindOf es)
  have hans : ∀ Y : Log, 170 ≤ Y.length → ans3 114 nrS Y = nrS (kindOf Y) :=
    fun Y hY => by have := nrS_le (kindOf Y); unfold ans3; simp; omega
  unfold D2S D2 Wrong2
  rw [hans es (by omega), hans es' (by omega), hk, TS_same h (by omega),
    clR2_same (c0 := c0SL) (L' := L') (es' := es') (c0S_agree h.1 (by omega))
      (h.1.mono (by rw [← hk]; omega)),
    rchs2_congr (h.1.mono (by rw [← hk]; omega))]
  exact and_congr_left fun _ => ⟨fun _ => by omega, fun _ => by omega⟩

/-! ## S2's end: the Sh claim is RS claim 3 -/

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

theorem kind_m (κ : Kind) : κ.m = nbS κ + 14 := by cases κ <;> rfl

/-- **RS claim 3's true value is `ẑ` at S2's point** `(r_blk, r_pos)` over the block positions
`< 2^10` (the Sh point's four zero coordinates; `ml_claim_split`'s low 7 are `r_pos`'s first 7). -/
theorem trueL_two (L es : Log) :
    trueL (kindOf es) L es 2 = ∑ q ∈ range (2 ^ 10), ∑ y ∈ range (2 ^ nbS (kindOf es)),
      eqAtR (ptOf (nbS (kindOf es)) (rbL (kindOf es) es)) y *
        eqAtR (ptOf 10 (rpL (kindOf es) es)) q * zNode (kindOf es) L es y q := by
  generalize kindOf es = κ
  have hm := kind_m κ
  have hP0 : nrP 0 κ = nbS κ + 7 := by rw [nrP_zero, hm]; omega
  set xS := xSL κ es
  set sP := shPtL κ.m es
  have hxS : xS.length = 7 := by simp [xS, xSL]
  have hsP : sP.length = nbS κ + 7 := by simp [sP, shPtL, nbS]; omega
  -- the weights
  have hcw : ∀ i : Fin 128, cwL κ es (2 : Fin 4) i = eqAtR (ptOf 7 xS) i := by
    intro i
    show (eqTab xS.toArray).getD i 0 = _
    rw [eqTab_getD _ (by simp [hxS]), List.size_toArray, hxS, eqBits, bitSel,
      eqAtR, ← Fin.prod_univ_eq_prod_range]
    refine prod_congr rfl fun l _ => ?_
    simp [ptOf, Array.getD_eq_getD_getElem?, List.getD_eq_getElem?_getD]
  have hg : ∀ u : Fin (2 ^ nrP 0 κ), gL κ es 2 u = eqAtR (ptOf (nrP 0 κ) sP) u := by
    intro u
    have hl : (rsPtsL κ es).getD 2 [] = sP := by cases κ <;> rfl
    have h2 : (2 : ℕ) < (rsPtsL κ es).length := by rw [rsPtsL_length]; split_ifs <;> norm_num
    have h2' : ((2 : Fin 4) : ℕ) = 2 := rfl
    rw [gL, h2', if_pos h2, if_neg (show (2 : ℕ) ≠ 1 by norm_num), mul_one, hl, eqPts_eq _ _ (hsP.trans hP0.symm) (by simp [bitsL, hsP, hP0]),
      hsP, ← hP0, ptOf_bitsL u.val _ u.isLt, eq_cube_eqAtR]
  have hq : ∀ (i : Fin 128) (u : Fin (2 ^ nrP 0 κ)), algebraMap F F (rsQ κ L es (nrP 0 κ) i u) =
      zW κ L es (i.val + 2 ^ 7 * u.val) := by
    intro i u
    have h1 : (i.val + 2 ^ 7 * u.val) / 128 = u.val := by have := i.isLt; omega
    have h2 : (i.val + 2 ^ 7 * u.val) % 128 = i.val := by have := i.isLt; omega
    simp only [rsQ, zW, Algebra.algebraMap_self, RingHom.id_apply, h1]
    congr 2; exact Fin.ext h2.symm
  have step1 : trueL κ L es 2 = ∑ u ∈ range (2 ^ (nbS κ + 7)), ∑ i ∈ range (2 ^ 7),
      eqAtR (ptOf 7 xS) i * eqAtR (ptOf (nbS κ + 7) sP) u * zW κ L es (i + 2 ^ 7 * u) := by
    unfold trueL
    simp only [hcw, hg, hq, mul_sum]
    rw [sum_comm, hP0]
    rw [Fin.sum_univ_eq_sum_range (fun y => ∑ x : Fin 128, eqAtR (ptOf 7 xS) x *
      (eqAtR (ptOf (nbS κ + 7) sP) y * zW κ L es (x + 2 ^ 7 * y)))]
    refine sum_congr rfl fun y _ => ?_
    rw [Fin.sum_univ_eq_sum_range (fun x => eqAtR (ptOf 7 xS) x *
      (eqAtR (ptOf (nbS κ + 7) sP) y * zW κ L es (x + 2 ^ 7 * y)))]
    exact sum_congr rfl fun x _ => by ring
  -- the whole point `xS ++ sP` over the `m` bit coordinates
  have hP7 : ptOf 7 (xS ++ sP) = ptOf 7 xS := by
    funext l; simp only [ptOf, List.getD_eq_getElem?_getD,
      List.getElem?_append_left (show l.val < xS.length by rw [hxS]; exact l.isLt)]
  have hPd : (xS ++ sP).drop 7 = sP := by rw [List.drop_left' hxS]
  have step2 : trueL κ L es 2 = ∑ b ∈ range (2 ^ (14 + nbS κ)),
      eqAtR (ptOf (14 + nbS κ) (xS ++ sP)) b * zW κ L es b := by
    rw [step1, show 14 + nbS κ = 7 + (nbS κ + 7) by omega, sum_eqAtR_split, hP7, hPd]
  rw [step2, sum_eqAtR_split]
  have hD : (xS ++ sP).drop 14 = rbL κ es := by
    rw [show (14 : ℕ) = 7 + 7 from rfl, ← List.drop_drop, hPd]
    simp only [sP, shPtL]
    rw [List.drop_left' (by simp)]; rfl
  obtain ⟨n, hn⟩ : ∃ n, κ.m = n + 14 := ⟨nbS κ, hm⟩
  have hnb : nbS κ = n := by unfold nbS; omega
  have h14 : ptOf 14 (xS ++ sP) = ptOf 14 (rpL κ es ++ [0, 0, 0, 0]) := by
    funext l
    fin_cases l <;> simp [ptOf, xS, sP, xSL, shPtL, rpL, hnb, hn, List.getD_eq_getElem?_getD,
      List.getElem?_append_left, List.getElem?_append_right]
  have hQ10 : ptOf 10 (rpL κ es ++ [0, 0, 0, 0]) = ptOf 10 (rpL κ es) := by
    funext l; simp only [ptOf, List.getD_eq_getElem?_getD,
      List.getElem?_append_left (show l.val < (rpL κ es).length by rw [rpL_length]; exact l.isLt)]
  have hQd : (rpL κ es ++ [0, 0, 0, 0]).drop 10 = [0, 0, 0, 0] := List.drop_left' (rpL_length κ es)
  rw [hD, h14]
  have inner : ∀ y ∈ range (2 ^ nbS κ), ∑ x ∈ range (2 ^ 14),
      eqAtR (ptOf 14 (rpL κ es ++ [0, 0, 0, 0])) x * eqAtR (ptOf (nbS κ) (rbL κ es)) y *
        zW κ L es (x + 2 ^ 14 * y) = ∑ q ∈ range (2 ^ 10),
      eqAtR (ptOf (nbS κ) (rbL κ es)) y * eqAtR (ptOf 10 (rpL κ es)) q * zNode κ L es y q := by
    intro y _
    simp only [mul_assoc]
    rw [show (14 : ℕ) = 10 + 4 from rfl, sum_eqAtR_split, hQ10, hQd]
    rw [sum_eq_single 0]
    · simp only [eqAtR_zeros4 (show 0 < 16 by norm_num), if_true, mul_one, mul_zero, add_zero]
      refine sum_congr rfl fun q _ => ?_
      simp only [zNode, show y * 2 ^ 14 + q = q + 2 ^ (10 + 4) * y by ring]
      ring
    · intro h hh h0
      rw [eqAtR_zeros4 (mem_range.1 hh), if_neg h0]
      simp
    · intro h; exact absurd (mem_range.2 (by norm_num)) h
  rw [sum_congr rfl inner, sum_comm]

/-- **`w_out + w_in` on the log** (A.9 `finSh` (ii) on the operations' specifications, as `relSh`
reads them: `shiftMaskS` for a node, `eqPoint`/`shiftEqS` for a leaf, `slotWS`, `linkWAllS` at the
packed points or a leaf's `0^8`, `linkSum`). -/
def wSumL (κ : Kind) (es : Log) : F :=
  let ks := ksL es
  let τ := pad18 κ (tauL κ es); let rb := pad18 κ (rbL κ es)
  let θ := (thL es).toArray; let rp := (rpL κ es).toArray
  let sm := shiftMaskS τ rb
  let e := if κ.isNode then sm.1 else eqPoint τ rb
  let sh := if κ.isNode then sm.2.1 else shiftEqS τ rb
  let e0 := if κ.isNode then sm.2.2 else eqPoint (Array.replicate 18 0) rb
  let sIn := if κ.isNode then slotWS 2 θ rp else slotWS 1 θ rp
  e * slotWS 0 θ rp +
    linkSum (if κ.isNode then linkWAllS (tauL κ es ++ thL es).toArray (rbL κ es ++ rpL κ es).toArray
      else Array.replicate nLinkFam 0) ks nLinkFam ((sh + ks * e0) * sIn) (ks * ks)

/-- S2's last claim (after the kind's `nb + 10` rounds). -/
def claimSL (κ : Kind) (es : Log) : F :=
  clR2 114 16 readF (fun d => chF d 0) c0SL [] es (nrS κ)

/-- **The Sh claim's binding** (A.9 `finSh` (ii)): `c_Sh = (w_out + w_in)·v`. -/
def oSh (κ : Kind) (es : Log) (v : F) : Prop := claimSL κ es = wSumL κ es * v

/-- **The weight's extension at S2's point is `w_out + w_in`** (`final_leaf`, `final_node`). -/
theorem wSumL_eq (κ : Kind) (es : Log) :
    wSumL κ es = ∑ q ∈ range (2 ^ 10), ∑ y ∈ range (2 ^ nbS κ),
      eqAtR (ptOf (nbS κ) (rbL κ es)) y * eqAtR (ptOf 10 (rpL κ es)) q * wS κ es y q := by
  have hθ : ptA 10 (thL es).toArray = ptOf 10 (thL es) := ptA_toArray _ _
  have hr : ptA 10 (rpL κ es).toArray = ptOf 10 (rpL κ es) := ptA_toArray _ _
  unfold wSumL wS
  dsimp only
  split_ifs with hn
  · cases κ <;> simp only [Kind.isNode, Bool.false_eq_true] at hn
    have e := final_node (tauL .N30 es) (rbL .N30 es) (tauL_length _ es) (rbL_length _ es)
      (thL es).toArray (rpL .N30 es).toArray (ksL es)
    rw [hθ, hr] at e
    exact e.symm
  · have e := final_leaf (nbS_le κ) (tauL κ es) (rbL κ es) (tauL_length κ es) (rbL_length κ es)
      (thL es).toArray (rpL κ es).toArray (ksL es)
    rw [hθ, hr] at e
    rw [e, linkSum_eq _ _ _ le_rfl]
    simp only [pad18]
    rw [sum_eq_zero fun x hx => by simp [Array.getElem?_replicate, mem_range.1 hx], add_zero]

theorem rchsS_pts (κ : Kind) (es : Log) :
    ptOf (nbS κ) (rchs2 114 (fun d => chF d 0) es (nbS κ + 10)) = ptOf (nbS κ) (rbL κ es) ∧
      ptOf 10 ((rchs2 114 (fun d => chF d 0) es (nbS κ + 10)).drop (nbS κ)) =
        ptOf 10 (rpL κ es) := by
  refine ⟨funext fun l => ?_, funext fun l => ?_⟩
  · have := l.isLt
    simp [ptOf, rchs2, rbL, List.getD_eq_getElem?_getD, this, show l.val < nbS κ + 10 by omega]
    rfl
  · have := l.isLt
    simp [ptOf, rchs2, rpL, List.getD_eq_getElem?_getD, this]
    rfl

theorem mle_tab (a : ℕ) (f : ℕ → ℕ → F) (rs : List F) :
    mle (tbl (a + 10) (Array.ofFn (n := 2 ^ (a + 10)) fun i => f (i.val % 2 ^ a) (i.val / 2 ^ a)))
        (ptOf (a + 10) rs) =
      ∑ q ∈ range (2 ^ 10), ∑ y ∈ range (2 ^ a),
        eqAtR (ptOf a rs) y * eqAtR (ptOf 10 (rs.drop a)) q * f y q := by
  refine (mle_ofFn_split a 10 (fun i => f (i % 2 ^ a) (i / 2 ^ a)) rs).trans ?_
  exact sum_congr rfl fun q _ => sum_congr rfl fun u hu => by
    obtain ⟨h1, h2⟩ := idx_split (q := q) (mem_range.1 hu); rw [h1, h2]

/-- **At S2's end its doom is the Sh claim's binding failing at the true value** (RS claim 3). -/
theorem endS {L es : Log} (h : D2S L es) (hl : 170 ≤ es.length) :
    ¬ oSh (kindOf es) es (trueL (kindOf es) L es 2) := by
  obtain ⟨-, hw⟩ := h
  have ha : ans3 114 nrS es = nrS (kindOf es) := by
    have := nrS_le (kindOf es); unfold ans3; simp; omega
  rw [ha] at hw
  unfold Wrong2 at hw
  rw [Nat.sub_self, trueSum_bindAll' _ _ _ (by simp [rchs2]) (TS_size L es), innerExpr_eval2,
    TS, arrGetD_pair0, arrGetD_pair1, nrS, mle_tab, mle_tab,
    (rchsS_pts _ es).1, (rchsS_pts _ es).2] at hw
  intro hok
  apply hw
  rw [oSh, claimSL, wSumL_eq, trueL_two] at hok
  rw [show clR2 114 16 readF (fun d => chF d 0) c0SL L es (nbS (kindOf es) + 10) =
    claimSL (kindOf es) es from clR2_same rfl (fun _ _ => rfl), claimSL]
  exact hok

/-- **S's pending claim is RS0's `PendBad` at claim 3** (any Z binding). -/
theorem pendS_pendBad {oZ : Kind → Log → F → Prop} {L es : Log} (h : D2S L es)
    (hl : 170 ≤ es.length) : PendBad (okRS oZ oSh) L es :=
  ⟨2, by rw [rsPtsL_length]; split_ifs <;> decide, endS h hl⟩

theorem wSumL_congr {es es' : Log} (h : Agree es es' 170) (κ : Kind) : wSumL κ es = wSumL κ es' := by
  obtain ⟨h1, h2, h3⟩ := s1_congr h (by norm_num) κ
  have hn := nbS_le κ
  have h4 : rbL κ es = rbL κ es' :=
    List.map_congr_left fun l hl => rch_congr h (by simp at hl; omega)
  have h5 : rpL κ es = rpL κ es' :=
    List.map_congr_left fun l hl => rch_congr h (by simp at hl; omega)
  simp only [wSumL, h1, h2, h3, h4, h5]

/-- **The Sh binding reads the log before RS0** (`okRS_reads`' form). -/
theorem oSh_reads : ∀ κ es es', Agree es es' 312 → oSh κ es = oSh κ es' := fun κ es es' h => by
  have hc : claimSL κ es = claimSL κ es' := by
    have := nrS_le κ
    exact clR2_same (c0S_agree h (by norm_num)) (h.mono (by omega))
  funext v; simp only [oSh, hc, wSumL_congr (h.mono (by norm_num)) κ]

/-! ## Controls -/

/-- Control (positive): the zero table with zero boundary digests satisfies a leaf's S truth. -/
theorem shHoldsL_zero (nb : ℕ) : ShHoldsL nb (fun _ _ => 0) (fun _ => 0) (fun _ => 0) :=
  ⟨fun _ _ _ _ => rfl, fun _ _ => rfl, fun _ _ => rfl⟩

/-- Control (negative): a start digest with bit 0 set breaks the zero table's leaf S truth. -/
theorem not_shHoldsL_start (nb : ℕ) :
    ¬ ShHoldsL nb (fun _ _ => 0) (fun σ => if σ = 0 then 1 else 0) (fun _ => 0) := fun h => by
  have := h.2.1 0 (by norm_num); simp at this

/-- Control (positive): at a cube point `θ = σ₀` the slot weight picks the slot's position. -/
theorem slotT_cube {b σ₀ : ℕ} (hσ : σ₀ < 256) : slotT (cubeN 10 σ₀) b (b + σ₀) = 1 := by
  unfold slotT
  rw [sum_eq_single σ₀]
  · rw [eqAtR_cubeN (by omega) (by omega)]; simp
  · intro σ hσ' hne
    rw [eqAtR_cubeN (by omega) (by have := mem_range.1 hσ'; omega)]; simp [hne]
  · intro h; exact absurd (mem_range.2 hσ) h

/-- Control (negative): off the slot (below its base) the weight is `0`. -/
theorem slotT_off (θ : Fin 10 → F) {b q : ℕ} (hq : q < b) : slotT θ b q = 0 :=
  sum_eq_zero fun σ _ => by rw [if_neg (by omega), mul_zero]

/-- Control: a node's S2 initial claim is `0` (no boundary). -/
theorem c0S_node {es : Log} (h : (kindOf es).isNode = true) : c0S es = 0 := by
  rw [c0S_eq, if_pos h]

/-- Control (negative): with a nonzero weight the Sh binding accepts one value only. -/
theorem oSh_unique {κ : Kind} {es : Log} {v v' : F} (hw : wSumL κ es ≠ 0) (h : oSh κ es v)
    (h' : oSh κ es v') : v = v' :=
  mul_left_cancel₀ hw (h.symm.trans h')

/-- Control (negative): before its first absorb S2 is not doomed. -/
theorem not_D2S_short {L es : Log} (h : es.length ≤ 114) : ¬ D2S L es := not_D2_short h

end FR.Snd
