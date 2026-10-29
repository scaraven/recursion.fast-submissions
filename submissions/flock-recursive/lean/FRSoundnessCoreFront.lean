-- New for `flock-recursive` (BLUEPRINT §10 changes 27 (B) step 3; stage RET-2): the declarations of
-- the 3.x soundness modules that the revision 4.1 certificate reads, moved here verbatim (same
-- names, statements and proofs) from `FRSoundnessFrSh` (36), `FRSoundnessFrS` (11),
-- `FRSoundnessFrZM` (23), `FRSoundnessFrBind` (1). Content: the front's Sh/S/ZM/Bind pieces
-- (`slotT`, `coS`, `ksL`, `thL`, `kMat`, `targetS_range`, …). The 3.x modules import this one.
import FRSoundnessCoreRows

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
