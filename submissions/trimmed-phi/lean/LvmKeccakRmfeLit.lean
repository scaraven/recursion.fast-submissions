-- Split out of `LvmKeccakRmfe` (BS-1): the literals of the embedding and the kernel check of the
-- embedding lemma, which need only `LvmVCore`, so they build beside the Keccak bit/linear chain.
-- The check `rmfeOk_lit` (statement unchanged) is now proved by two small kernel checks on
-- natural numbers (`rowsOk_lit`, `colsOk_lit`) and a bridge, instead of one `decide +kernel` on
-- bit lists (61 s, 8.5 GB → about 5 s).
import LvmVCore

/-!
# The RMFE literals and the kernel check of the embedding lemma

See `LvmKeccakRmfe` for the lemma over `E`. Here: `RMFE_EMBED`, `RMFE_PROJECT` as literals
(`rmfeEmbed_eq`, `rmfeProject_eq`), and `rmfeOk_lit`, the embedding lemma on unit vectors as a
boolean: for `a, b, i < 16`, the parity of the coefficients of `emb_a · emb_b` selected by
`mask_i` is `[i = a = b]`.

The kernel does not check `rmfeOk` directly. Per pair `(a, b)` it computes the carry-less product
`P = emb_a · emb_b` as a number (`clmulN`) and the 16 parities at once, as the XOR of the columns
`col_c` (bit `i` of `col_c` is bit `c` of `mask_i`) over the set bits `c` of `P` (`rowOf`);
`rowsOk_lit` checks that this is `2^a` if `a = b` and `0` otherwise (the kernel runs `rowsOkH`,
one pass over the columns), `colsOk_lit` checks the columns against `RMFE_PROJECT`.
-/

namespace LeanVM.Protocol.KeccakGkr

open LeanVM.Parameters LeanVM.Protocol.Verifier

section

/-! ## The literals -/

/-- `RMFE_EMBED` (`keccak.rs:25-28`), in decimal. -/
def embedLit : List ℕ := [4244747, 8354290, 4935178, 7500812, 5461978, 1907870, 310894, 7885382,
  621788, 1089150, 2036820, 2178300, 5045448, 7821168, 1602438, 8489494]

/-- `RMFE_PROJECT` (`keccak.rs:29-46`), in decimal. -/
def projectLit : List ℕ := [1, 140737488355327, 43218598786281, 32136906789799, 111925089164473,
  101951566367639, 112771593653537, 102871349771039, 126754541004432, 60819261648545,
  20682647020959, 30409630824272, 11891857888673, 6939470531743, 76314673122000, 70368744177664]

set_option maxRecDepth 100000 in
theorem rmfeEmbed_eq : rmfeEmbed = embedLit := by decide +kernel

/-! ## `RMFE_PROJECT` with the powers of `x` carried along (GOLF3)

`rmfeFactor`'s masks reduce `x^c` modulo the factor by a long division per `c < 47`; the kernel check runs them
by a fold that carries `x^c mod f` instead (`masksS`, one shift and at most one `xor` per step): `carrylessDivmod`
of `x^(c+1)` is one `stepR` of that of `x^c` (`cdm_pow_succ`). -/

private theorem bl_le_iff (n k : ℕ) : bitLength n ≤ k ↔ n < 2 ^ k := by
  unfold bitLength
  split_ifs with h
  · subst h; simp
  · rw [Nat.add_one_le_iff]; exact Nat.log2_lt h

private theorem lt_bl_iff (n k : ℕ) : k < bitLength n ↔ 2 ^ k ≤ n := by
  rw [← Nat.not_le, bl_le_iff, Nat.not_lt]

private theorem bl_pos {n : ℕ} (h : n ≠ 0) : 0 < bitLength n := by
  rw [lt_bl_iff, pow_zero]; exact Nat.one_le_iff_ne_zero.2 h

private theorem bl_shl1 {a : ℕ} (h : a ≠ 0) : bitLength (a <<< 1) = bitLength a + 1 := by
  have hp := bl_pos h
  apply Nat.le_antisymm
  · rw [bl_le_iff, Nat.shiftLeft_eq, pow_one, pow_succ]
    exact Nat.mul_lt_mul_of_pos_right ((bl_le_iff a _).1 le_rfl) (by norm_num)
  · rw [Nat.add_one_le_iff, lt_bl_iff, Nat.shiftLeft_eq, pow_one]
    have h1 := (lt_bl_iff a (bitLength a - 1)).1 (by omega)
    calc 2 ^ bitLength a = 2 ^ (bitLength a - 1) * 2 := by rw [← pow_succ]; congr 1; omega
      _ ≤ a * 2 := Nat.mul_le_mul_right 2 h1

private theorem bl_shl {a : ℕ} (h : a ≠ 0) : ∀ s, bitLength (a <<< s) = bitLength a + s
  | 0 => by simp
  | s + 1 => by
    have h' : a <<< s ≠ 0 := by
      rw [Nat.shiftLeft_eq]; exact Nat.mul_ne_zero h (Nat.pos_iff_ne_zero.1 (Nat.two_pow_pos s))
    rw [Nat.shiftLeft_add, bl_shl1 h', bl_shl h s]; omega

/-- Two numbers of the same bit length `m + 1` differ below bit `m`. -/
private theorem xor_lt_of_top {a b m : ℕ} (ha1 : 2 ^ m ≤ a) (ha2 : a < 2 ^ (m + 1)) (hb1 : 2 ^ m ≤ b)
    (hb2 : b < 2 ^ (m + 1)) : a ^^^ b < 2 ^ m := by
  apply Nat.lt_pow_two_of_testBit
  intro i hi
  rw [Nat.testBit_xor]
  rcases Nat.eq_or_lt_of_le hi with rfl | hi
  · have t : ∀ x, 2 ^ m ≤ x → x < 2 ^ (m + 1) → x.testBit m = true := fun x h1 h2 => by
      rw [Nat.testBit_eq_decide_div_mod_eq, decide_eq_true_eq,
        Nat.div_eq_of_lt_le (k := 1) (by rw [one_mul]; exact h1) (by rw [pow_succ] at h2; omega)]
    rw [t a ha1 ha2, t b hb1 hb2]; rfl
  · have hp : 2 ^ (m + 1) ≤ 2 ^ i := Nat.pow_le_pow_right (by norm_num) hi
    rw [Nat.testBit_lt_two_pow (by omega), Nat.testBit_lt_two_pow (by omega)]; rfl

private theorem bl_xor_lt {f a : ℕ} (hf : f ≠ 0) (ha : a ≠ 0) (h : bitLength f ≤ bitLength a) :
    bitLength (a ^^^ (f <<< (bitLength a - bitLength f))) < bitLength a := by
  have hb := bl_shl hf (bitLength a - bitLength f)
  rw [show bitLength f + (bitLength a - bitLength f) = bitLength a by omega] at hb
  have hpa := bl_pos ha
  obtain ⟨m, hm⟩ : ∃ m, bitLength a = m + 1 := ⟨bitLength a - 1, by omega⟩
  rw [hm] at hb ⊢
  rw [Nat.lt_add_one_iff, bl_le_iff]
  refine xor_lt_of_top ((lt_bl_iff _ _).1 (by omega)) ((bl_le_iff _ _).1 hm.le) ((lt_bl_iff _ _).1 (by omega))
    ((bl_le_iff _ _).1 hb.le)

private theorem shl_xor_shl (a f s : ℕ) : (a <<< 1) ^^^ (f <<< (s + 1)) = (a ^^^ (f <<< s)) <<< 1 := by
  apply Nat.eq_of_testBit_eq
  intro i
  simp only [Nat.testBit_xor, Nat.testBit_shiftLeft]
  rcases i with _ | i
  · simp
  · simp only [ge_iff_le, Nat.le_add_left, decide_true, Bool.true_and, Nat.add_sub_cancel,
      Nat.add_le_add_iff_right, Nat.add_sub_add_right]

/-- One step of `x^c mod f` to `x^(c+1) mod f`. -/
private def stepR (f r : ℕ) : ℕ := bif Nat.ble (bitLength f) (bitLength (r <<< 1)) then (r <<< 1) ^^^ f else r <<< 1

private theorem cdm_red {f a : ℕ} (h : bitLength a < bitLength f) :
    ∀ (n q : ℕ), (carrylessDivmodAux n f q a).2 = a
  | 0, _ => rfl
  | n + 1, q => by
    rw [carrylessDivmodAux, if_neg (fun h' => absurd h'.2 (by omega))]

private theorem cdm_shl_red {f a : ℕ} (hf : f ≠ 0) (hr : bitLength a < bitLength f) (fuel q q' : ℕ) :
    (carrylessDivmodAux (fuel + 1) f q' (a <<< 1)).2 = stepR f (carrylessDivmodAux fuel f q a).2 := by
  rw [cdm_red hr fuel q, stepR]
  by_cases hc : bitLength f ≤ bitLength (a <<< 1)
  · have hfp := bl_pos hf
    have ha1 : a <<< 1 ≠ 0 := fun h0 => by rw [h0] at hc; simp [bitLength] at hc; omega
    have ha : a ≠ 0 := fun h0 => by rw [h0] at ha1; exact ha1 rfl
    have hl1 := bl_shl1 ha
    have hsh : bitLength (a <<< 1) - bitLength f = 0 := by omega
    have hx := bl_xor_lt hf ha1 hc
    rw [hsh, Nat.shiftLeft_zero] at hx
    rw [carrylessDivmodAux, if_pos ⟨ha1, hc⟩]
    simp only [hsh, Nat.shiftLeft_zero]
    rw [cdm_red (by omega), Nat.ble_eq_true_of_le hc]
    rfl
  · rw [carrylessDivmodAux, if_neg (fun h => hc h.2)]
    rw [show Nat.ble (bitLength f) (bitLength (a <<< 1)) = false from
      Bool.eq_false_iff.2 fun h => hc (Nat.le_of_ble_eq_true h)]
    rfl

private theorem cdm_shl {f : ℕ} (hf : f ≠ 0) : ∀ (fuel a q q' : ℕ), bitLength a < fuel + bitLength f →
    (carrylessDivmodAux (fuel + 1) f q' (a <<< 1)).2 = stepR f (carrylessDivmodAux fuel f q a).2 := by
  intro fuel
  induction fuel with
  | zero => intro a q q' h; exact cdm_shl_red hf (by omega) 0 q q'
  | succ k ih =>
    intro a q q' h
    by_cases hr : bitLength a < bitLength f
    · exact cdm_shl_red hf hr _ q q'
    · have hle : bitLength f ≤ bitLength a := by omega
      have hfp := bl_pos hf
      have ha : a ≠ 0 := fun h0 => by rw [h0] at hle; simp [bitLength] at hle; omega
      have hl1 := bl_shl1 ha
      have ha1 : a <<< 1 ≠ 0 := fun h0 => by rw [h0] at hl1; simp [bitLength] at hl1
      have e1 : carrylessDivmodAux (k + 1) f q a = carrylessDivmodAux k f (q ||| (1 <<< (bitLength a - bitLength f)))
          (a ^^^ (f <<< (bitLength a - bitLength f))) := by
        rw [carrylessDivmodAux, if_pos ⟨ha, hle⟩]
      have e2 : carrylessDivmodAux (k + 1 + 1) f q' (a <<< 1) = carrylessDivmodAux (k + 1) f
          (q' ||| (1 <<< (bitLength (a <<< 1) - bitLength f)))
          ((a <<< 1) ^^^ (f <<< (bitLength (a <<< 1) - bitLength f))) := by
        rw [carrylessDivmodAux, if_pos ⟨ha1, by omega⟩]
      rw [e1, e2, hl1, show bitLength a + 1 - bitLength f = bitLength a - bitLength f + 1 by omega,
        shl_xor_shl]
      exact ih _ _ _ (by have := bl_xor_lt hf ha hle; omega)

private theorem bl_one_shl (c : ℕ) : bitLength (1 <<< c) = c + 1 := by
  rw [bl_shl one_ne_zero, show bitLength 1 = 1 from rfl, Nat.add_comm]

/-- `x^(c+1) mod f` is one `stepR` of `x^c mod f`. -/
private theorem cdm_pow_succ {f : ℕ} (hf : f ≠ 0) (c : ℕ) :
    (carrylessDivmod (1 <<< (c + 1)) f).2 = stepR f (carrylessDivmod (1 <<< c) f).2 := by
  rw [carrylessDivmod, carrylessDivmod, bl_one_shl, bl_one_shl, Nat.shiftLeft_add]
  exact cdm_shl hf _ _ _ _ (by rw [bl_one_shl]; omega)

private theorem cdm_pow_zero {f : ℕ} (hf : 2 ≤ bitLength f) : (carrylessDivmod (1 <<< 0) f).2 = 1 :=
  cdm_red (by rw [bl_one_shl]; omega) _ _

/-- One step of `rmfeFactor`'s masks, at the residue `g = x^c mod f`. -/
private def mstep (f bits : ℕ) (masks : List ℕ) (c g : ℕ) : List ℕ :=
  let atZero := g % 2
  let atOne := bitParity g
  let values : List ℕ := if bits = 1 then [if f = 0b10 then atZero else atOne]
    else if bits = 2 then [atZero, atOne] else [atZero, atOne, g >>> 4]
  List.zipWith (fun mask value ↦ mask ||| (value <<< c)) masks values

/-- `rmfeFactor`'s masks with `x^c mod f` carried along (`rmfeFactor_snd`). -/
private def masksS (f bits : ℕ) : List ℕ :=
  ((List.range productBits).foldl (fun (st : List ℕ × ℕ) c ↦ (mstep f bits st.1 c st.2, stepR f st.2))
    (List.replicate bits 0, 1)).1

private theorem foldl_carry {β : Type} (F : β → ℕ → ℕ → β) (G : ℕ → ℕ) (step : ℕ → ℕ)
    (hG : ∀ c, G (c + 1) = step (G c)) : ∀ (n k : ℕ) (m : β),
    ((List.range' k n).foldl (fun (st : β × ℕ) c ↦ (F st.1 c st.2, step st.2)) (m, G k)).1 =
      (List.range' k n).foldl (fun m c ↦ F m c (G c)) m
  | 0, _, _ => rfl
  | n + 1, k, m => by
    rw [List.range'_succ, List.foldl_cons, List.foldl_cons, ← hG]
    exact foldl_carry F G step hG n (k + 1) _

private theorem foldl_carry' {β : Type} (F : β → ℕ → ℕ → β) (G : ℕ → ℕ) (step : ℕ → ℕ)
    (hG : ∀ c, G (c + 1) = step (G c)) (n k : ℕ) (m : β) (g0 : ℕ) (h0 : g0 = G k) :
    ((List.range' k n).foldl (fun (st : β × ℕ) c ↦ (F st.1 c st.2, step st.2)) (m, g0)).1 =
      (List.range' k n).foldl (fun m c ↦ F m c (G c)) m := by
  subst h0; exact foldl_carry F G step hG n k m

private theorem rmfeFactor_snd (modulus : ℕ) {f : ℕ} (hf : 2 ≤ bitLength f) (bits : ℕ) :
    (rmfeFactor modulus f bits).2 = masksS f bits := by
  have hf0 : f ≠ 0 := fun h => by rw [h] at hf; simp [bitLength] at hf
  have h := foldl_carry' (mstep f bits) (fun c ↦ (carrylessDivmod (1 <<< c) f).2) (stepR f)
    (cdm_pow_succ hf0) productBits 0 (List.replicate bits 0) 1 (cdm_pow_zero hf).symm
  rw [← List.range_eq_range'] at h
  rw [masksS, h]
  dsimp only [rmfeFactor, mstep]

/-- `rmfeFactor`'s embedding half. -/
private def rmfeEmbOf (modulus f bits : ℕ) : List ℕ := (rmfeFactor modulus f bits).1

/-- `rmfeFactor`'s masks, by `masksS` when `f` has degree at least `1`. -/
private def masksS' (modulus f bits : ℕ) : List ℕ :=
  if 2 ≤ bitLength f then masksS f bits else (rmfeFactor modulus f bits).2

private theorem rmfeFactor_eq (modulus f bits : ℕ) :
    rmfeFactor modulus f bits = (rmfeEmbOf modulus f bits, masksS' modulus f bits) := by
  unfold rmfeEmbOf masksS'
  split_ifs with h
  · exact Prod.mk.eta.symm.trans (congrArg (Prod.mk _) (rmfeFactor_snd modulus h bits))
  · exact Prod.mk.eta.symm

set_option maxRecDepth 100000 in
theorem rmfeProject_eq : rmfeProject = projectLit := by
  unfold rmfeProject rmfe
  simp only [rmfeFactor_eq]
  decide +kernel

theorem rmfeEmbed_length : rmfeEmbed.length = 16 := by rw [rmfeEmbed_eq]; rfl

theorem rmfeProject_length : rmfeProject.length = 16 := by rw [rmfeProject_eq]; rfl

/-! ## The kernel check -/

/-- The low `k` bits of `n`, as a list. -/
def bitsFrom : ℕ → ℕ → List Bool
  | _, 0 => []
  | n, k + 1 => decide (n % 2 = 1) :: bitsFrom (n / 2) k

/-- The sum of two binary polynomials. -/
def xorL : List Bool → List Bool → List Bool
  | [], l => l
  | x :: xs, [] => x :: xs
  | x :: xs, y :: ys => (x ^^ y) :: xorL xs ys

/-- The product of two binary polynomials. -/
def mulGF2 : List Bool → List Bool → List Bool
  | [], _ => []
  | a :: A, B => xorL (if a then B else []) (false :: mulGF2 A B)

/-- The parity of the coefficients of `M` that `mask` selects, among the first `47`. -/
def parityL (mask : ℕ) (M : List Bool) : Bool :=
  (List.range 47).foldl (fun acc c ↦ acc ^^ (mask.testBit c && M.getD c false)) false

/-- The embedding lemma on unit vectors, as a boolean. -/
def rmfeOk (emb proj : List ℕ) : Bool :=
  (List.range 16).all fun a ↦ (List.range 16).all fun b ↦ (List.range 16).all fun i ↦
    parityL (proj.getD i 0) (mulGF2 (bitsFrom (emb.getD a 0) 24) (bitsFrom (emb.getD b 0) 24)) ==
      (i == a && a == b)

theorem bitsFrom_getD : ∀ (n k c : ℕ), (bitsFrom n k).getD c false = (decide (c < k) && n.testBit c)
  | n, 0, c => by simp [bitsFrom]
  | n, k + 1, 0 => by simp [bitsFrom, Nat.testBit_zero]
  | n, k + 1, c + 1 => by
    rw [bitsFrom, List.getD_cons_succ, bitsFrom_getD (n / 2) k c, Nat.testBit_div_two]
    simp

/-! ## The check on numbers -/

/-- The carry-less product of the binary polynomial `A` (a bit list, lowest first) and `y`. -/
def clmulN : List Bool → ℕ → ℕ
  | [], _ => 0
  | a :: A, y => cond a y 0 ^^^ (clmulN A y <<< 1)

/-- The columns of `RMFE_PROJECT`: bit `i` of `colLit[c]` is bit `c` of `RMFE_PROJECT[i]`. -/
def colLit : List ℕ := [14079, 9386, 9386, 9366, 28082, 4702, 18438, 30526, 7402, 19370, 16214,
  25330, 6302, 3974, 894, 16874, 29034, 22998, 15986, 27166, 24070, 31550, 22506, 29802, 7446,
  3058, 18270, 15558, 9150, 24682, 22826, 14038, 9394, 9374, 9350, 28094, 4714, 18474, 30486,
  7410, 19358, 16198, 25342, 6314, 4010, 854, 49650]

/-- The sixteen parities of `P` at once: the XOR of the columns `cols[c]` over the set bits `c`
of `P`, `c < 47`. -/
def rowOf (P : ℕ) (cols : List ℕ) : ℕ :=
  (List.range 47).foldl (fun acc c ↦ bif P.testBit c then acc ^^^ cols.getD c 0 else acc) 0

/-- Per pair `(a, b)`, the parities of `emb_a · emb_b` are `2^a` if `a = b`, `0` otherwise. -/
def rowsOk (emb cols : List ℕ) : Bool :=
  (List.range 16).all fun a ↦ (List.range 16).all fun b ↦
    rowOf (clmulN (bitsFrom (emb.getD a 0) 24) (emb.getD b 0 % 2 ^ 24)) cols ==
      bif a == b then 1 <<< a else 0

/-- `cols` are the columns of `proj`. -/
def colsOk (proj cols : List ℕ) : Bool :=
  (List.range 16).all fun i ↦ (List.range 47).all fun c ↦
    (cols.getD c 0).testBit i == (proj.getD i 0).testBit c

/-- `rowOf` in one pass over the columns, halving `P` (`rowOf_eq_H`): no `getD`, no `testBit`. -/
def rowOfH : ℕ → List ℕ → ℕ → ℕ
  | _, [], acc => acc
  | P, col :: cs, acc => rowOfH (P / 2) cs (cond (Nat.beq (P % 2) 1) (acc ^^^ col) acc)

/-- `rowsOk` through `rowOfH` (`rowsOk_eq_H`), the form the kernel decides. -/
def rowsOkH (emb cols : List ℕ) : Bool :=
  (List.range 16).all fun a ↦ (List.range 16).all fun b ↦
    rowOfH (clmulN (bitsFrom (emb.getD a 0) 24) (emb.getD b 0 % 2 ^ 24)) cols 0 ==
      bif a == b then 1 <<< a else 0

private theorem foldl_rowOf (P : ℕ) (cols : List ℕ) : ∀ (n k acc : ℕ), k + n ≤ cols.length →
    (List.range' k n).foldl (fun acc c ↦ bif P.testBit c then acc ^^^ cols.getD c 0 else acc) acc =
      rowOfH (P / 2 ^ k) ((cols.drop k).take n) acc
  | 0, k, acc, _ => by simp [rowOfH]
  | n + 1, k, acc, h => by
    have hk : k < cols.length := by omega
    rw [List.range'_succ, List.foldl_cons, foldl_rowOf P cols n (k + 1) _ (by omega),
      List.drop_eq_getElem_cons hk, List.take_succ_cons, rowOfH, Nat.div_div_eq_div_mul, ← Nat.pow_succ,
      List.getD_eq_getElem _ _ hk, Nat.testBit_eq_decide_div_mod_eq]
    congr 1
    cases h2 : Nat.beq (P / 2 ^ k % 2) 1
    · have := Nat.ne_of_beq_eq_false h2; simp [this]
    · have := Nat.eq_of_beq_eq_true h2; simp [this]

theorem rowOf_eq_H (P : ℕ) {cols : List ℕ} (h : cols.length = 47) : rowOf P cols = rowOfH P cols 0 := by
  rw [rowOf, List.range_eq_range', foldl_rowOf P cols 47 0 0 (by omega)]
  simp [← h]

theorem rowsOk_eq_H {emb cols : List ℕ} (h : cols.length = 47) : rowsOk emb cols = rowsOkH emb cols := by
  simp only [rowsOk, rowsOkH, rowOf_eq_H _ h]

section SymPn
open Polynomial

/-! ## `clmulN` is symmetric (GOLF3: `rowsOk_lit` checks the pairs `a ≤ b` only) -/

/-- A natural number's bits as a polynomial over `ZMod 2` (proof help). -/
private noncomputable def pn (n : ℕ) : (ZMod 2)[X] :=
  ∑ i ∈ Finset.range n, if n.testBit i then X ^ i else 0

private theorem coeff_pn (n i : ℕ) : (pn n).coeff i = if n.testBit i then 1 else 0 := by
  unfold pn
  rw [finsetSum_coeff]
  simp only [apply_ite (fun p : (ZMod 2)[X] => p.coeff i), coeff_X_pow, coeff_zero]
  rw [Finset.sum_eq_single i]
  · simp
  · intro j _ hj; simp [hj.symm]
  · intro hi
    rw [Finset.mem_range, Nat.not_lt] at hi
    rw [Nat.testBit_lt_two_pow (lt_of_lt_of_le Nat.lt_two_pow_self (Nat.pow_le_pow_right (by norm_num) hi))]
    simp

private theorem pn_inj {a b : ℕ} (h : pn a = pn b) : a = b := by
  apply Nat.eq_of_testBit_eq
  intro i
  have := congrArg (fun p => p.coeff i) h
  simp only [coeff_pn] at this
  cases ha : a.testBit i <;> cases hb : b.testBit i <;> simp_all

private theorem pn_xor (a b : ℕ) : pn (a ^^^ b) = pn a + pn b := by
  ext i
  rw [coeff_add, coeff_pn, coeff_pn, coeff_pn, Nat.testBit_xor]
  cases a.testBit i <;> cases b.testBit i <;> decide

private theorem pn_shl1 (a : ℕ) : pn (a <<< 1) = X * pn a := by
  ext i
  rcases i with _ | i
  · rw [coeff_X_mul_zero, coeff_pn, Nat.testBit_shiftLeft]; simp
  · rw [coeff_X_mul, coeff_pn, coeff_pn, Nat.testBit_shiftLeft]; simp

private theorem pn_zero : pn 0 = 0 := by simp [pn]

private theorem pn_mod_succ (x k : ℕ) :
    pn (x % 2 ^ (k + 1)) = (if x % 2 = 1 then 1 else 0) + X * pn (x / 2 % 2 ^ k) := by
  ext i
  rcases i with _ | i
  · rw [coeff_add, coeff_X_mul_zero, add_zero, coeff_pn]
    by_cases h : x % 2 = 1 <;> simp [h, Nat.testBit_zero]
  · rw [coeff_add, coeff_X_mul, coeff_pn, coeff_pn]
    by_cases h : x % 2 = 1 <;> simp [h, Nat.testBit_mod_two_pow, Nat.testBit_div_two, coeff_one]

private theorem pn_clmulN (y : ℕ) : ∀ (k x : ℕ), pn (clmulN (bitsFrom x k) y) = pn (x % 2 ^ k) * pn y
  | 0, x => by simp [bitsFrom, clmulN, pn_zero, Nat.mod_one]
  | k + 1, x => by
    rw [bitsFrom, clmulN, pn_xor, pn_shl1, pn_clmulN y k (x / 2), pn_mod_succ]
    by_cases h : x % 2 = 1 <;> simp [h, pn_zero] <;> ring

private theorem clmulN_comm (x y : ℕ) :
    clmulN (bitsFrom x 24) (y % 2 ^ 24) = clmulN (bitsFrom y 24) (x % 2 ^ 24) := by
  apply pn_inj
  rw [pn_clmulN, pn_clmulN, mul_comm]

/-- `rowOfH` by `List.rec` (the kernel runs it a quarter faster than the structural recursion). -/
private noncomputable def rowOfR (P : ℕ) (cols : List ℕ) (acc : ℕ) : ℕ :=
  (List.rec (motive := fun _ => ℕ → ℕ → ℕ) (fun _ acc => acc)
    (fun col _ ih P acc => ih (P / 2) (cond (Nat.beq (P % 2) 1) (acc ^^^ col) acc)) cols) P acc

private theorem rowOfR_eq : ∀ (cols : List ℕ) (P acc : ℕ), rowOfR P cols acc = rowOfH P cols acc
  | [], _, _ => rfl
  | col :: cs, P, acc => by rw [rowOfH, ← rowOfR_eq cs]; rfl

/-- `clmulN` by `List.rec`. -/
private noncomputable def clmulR (A : List Bool) (y : ℕ) : ℕ :=
  List.rec (motive := fun _ => ℕ) 0 (fun a _ ih => cond a y 0 ^^^ (ih <<< 1)) A

private theorem clmulR_eq (y : ℕ) : ∀ A, clmulR A y = clmulN A y
  | [] => rfl
  | a :: A => by rw [clmulN, ← clmulR_eq y A]; rfl

/-- `rowsOkH` on the pairs `a ≤ b` (the others by `clmulN_comm`). -/
private noncomputable def rowsOkHalf (emb cols : List ℕ) : Bool :=
  (List.range 16).all fun a ↦ (List.range 16).all fun b ↦ Nat.blt b a ||
    rowOfR (clmulR (bitsFrom (emb.getD a 0) 24) (emb.getD b 0 % 2 ^ 24)) cols 0 ==
      bif a == b then 1 <<< a else 0

private theorem rowsOkH_of_half {emb cols : List ℕ} (h : rowsOkHalf emb cols = true) :
    rowsOkH emb cols = true := by
  simp only [rowsOkHalf, rowsOkH, List.all_eq_true, List.mem_range, Bool.or_eq_true, rowOfR_eq,
    clmulR_eq] at h ⊢
  intro a ha b hb
  rcases Nat.lt_or_ge b a with hab | hab
  · have h' := (h b hb a ha).resolve_left (by simp only [Nat.blt_eq]; omega)
    rw [clmulN_comm, show (a == b) = (b == a) from by
      rw [beq_false_of_ne (by omega : a ≠ b), beq_false_of_ne (by omega : b ≠ a)]]
    simpa only [show (b == a) = false from beq_false_of_ne (by omega), Bool.cond_false] using h'
  · exact (h a ha b hb).resolve_left (by simp only [Nat.blt_eq]; omega)

end SymPn

set_option maxRecDepth 100000 in
theorem rowsOk_lit : rowsOk embedLit colLit = true := by
  rw [rowsOk_eq_H rfl]; exact rowsOkH_of_half (by decide +kernel)

/-- `List.all` by `List.rec` (the kernel runs it faster than the structural recursion; proof help). -/
private noncomputable def allR {α : Type} (l : List α) (f : α → Bool) : Bool :=
  List.rec (motive := fun _ => Bool) true (fun a _ ih => f a && ih) l

private theorem allR_eq {α : Type} (f : α → Bool) : ∀ l : List α, allR l f = l.all f
  | [] => rfl
  | a :: l => by rw [List.all_cons, ← allR_eq f l]; rfl

set_option maxRecDepth 100000 in
theorem colsOk_lit : colsOk projectLit colLit = true := by
  simp only [colsOk, ← allR_eq]
  decide +kernel

/-! ## The bridge to `rmfeOk` -/

private theorem getD_xorL : ∀ (A B : List Bool) (c : ℕ),
    (xorL A B).getD c false = (A.getD c false ^^ B.getD c false)
  | [], l, c => by simp [xorL]
  | x :: xs, [], c => by simp [xorL]
  | x :: xs, y :: ys, 0 => by simp [xorL]
  | x :: xs, y :: ys, c + 1 => by
    rw [xorL, List.getD_cons_succ, List.getD_cons_succ, List.getD_cons_succ, getD_xorL xs ys c]

private theorem getD_mulGF2 {B : List Bool} {y : ℕ} (hB : ∀ c, B.getD c false = y.testBit c) :
    ∀ (A : List Bool) (c : ℕ), (mulGF2 A B).getD c false = (clmulN A y).testBit c
  | [], c => by simp [mulGF2, clmulN]
  | a :: A, c => by
    rw [mulGF2, clmulN, getD_xorL, Nat.testBit_xor, Nat.testBit_shiftLeft]
    have h1 : (if a then B else []).getD c false = (cond a y 0).testBit c := by
      cases a
      · simp
      · exact hB c
    have h2 : (false :: mulGF2 A B).getD c false =
        (decide (c ≥ 1) && (clmulN A y).testBit (c - 1)) := by
      rcases c with _ | c
      · simp
      · rw [List.getD_cons_succ, getD_mulGF2 hB A c]; simp
    rw [h1, h2]

private theorem getD_bitsFrom_mod (y k c : ℕ) :
    (bitsFrom y k).getD c false = (y % 2 ^ k).testBit c := by
  rw [bitsFrom_getD, Nat.testBit_mod_two_pow]

private theorem testBit_foldl_row (P : ℕ) (cols : List ℕ) (mask i : ℕ) : ∀ (l : List ℕ),
    (∀ c ∈ l, (cols.getD c 0).testBit i = mask.testBit c) → ∀ (acc : ℕ) (b : Bool),
    acc.testBit i = b →
    (l.foldl (fun acc c ↦ bif P.testBit c then acc ^^^ cols.getD c 0 else acc) acc).testBit i =
      l.foldl (fun b c ↦ b ^^ (mask.testBit c && P.testBit c)) b
  | [], _, acc, b, h => h
  | c :: l, hl, acc, b, h => by
    rw [List.foldl_cons, List.foldl_cons]
    apply testBit_foldl_row P cols mask i l (fun c' hc' ↦ hl c' (List.mem_cons_of_mem _ hc'))
    rw [← hl c (by simp), ← h]
    cases P.testBit c <;> simp [Nat.testBit_xor]

theorem rmfeOk_lit_at {a b i : ℕ} (ha : a < 16) (hb : b < 16) (hi : i < 16) :
    parityL (projectLit.getD i 0)
      (mulGF2 (bitsFrom (embedLit.getD a 0) 24) (bitsFrom (embedLit.getD b 0) 24)) =
        (i == a && a == b) := by
  have hr : rowOf (clmulN (bitsFrom (embedLit.getD a 0) 24) (embedLit.getD b 0 % 2 ^ 24)) colLit =
      bif a == b then 1 <<< a else 0 := by
    have h := rowsOk_lit
    simp only [rowsOk, List.all_eq_true, List.mem_range] at h
    exact eq_of_beq (h a ha b hb)
  have hc : ∀ c ∈ List.range 47, (colLit.getD c 0).testBit i = (projectLit.getD i 0).testBit c := by
    have h := colsOk_lit
    simp only [colsOk, List.all_eq_true, List.mem_range] at h
    exact fun c hc ↦ eq_of_beq (h i hi c (List.mem_range.1 hc))
  unfold parityL
  simp_rw [getD_mulGF2 (getD_bitsFrom_mod _ 24)]
  rw [← testBit_foldl_row _ colLit _ i _ hc 0 false (Nat.zero_testBit i)]
  change (rowOf _ colLit).testBit i = _
  rw [hr]
  by_cases hab : a = b
  · subst hab
    by_cases hia : i = a
    · subst hia; simp [Nat.one_shiftLeft]
    · simp [Nat.one_shiftLeft, hia, Ne.symm hia]
  · simp [hab]

/-- **The embedding lemma**, checked by the kernel on the literals (by `rowsOk_lit`,
`colsOk_lit`). -/
theorem rmfeOk_lit : rmfeOk embedLit projectLit = true := by
  simp only [rmfeOk, List.all_eq_true, List.mem_range]
  intro a ha b hb i hi
  rw [rmfeOk_lit_at ha hb hi, beq_self_eq_true]

end
end LeanVM.Protocol.KeccakGkr
