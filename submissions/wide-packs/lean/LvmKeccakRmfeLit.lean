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
boolean: for `a, b, i < 32`, the parity of the coefficients of `emb_a · emb_b` selected by
`mask_i` is `[i = a = b]`.

The kernel does not check `rmfeOk` directly. Per pair `(a, b)` it computes the carry-less product
`P = emb_a · emb_b` as a number (`clmulN`) and the 32 parities at once, as the XOR of the columns
`col_c` (bit `i` of `col_c` is bit `c` of `mask_i`) over the set bits `c` of `P` (`rowOf`);
`rowsOk_lit` checks that this is `2^a` if `a = b` and `0` otherwise (the kernel runs `rowsOkH`,
one pass over the columns), `colsOk_lit` checks the columns against `RMFE_PROJECT`.
-/

namespace LeanVM.Protocol.KeccakGkr

open LeanVM.Parameters LeanVM.Protocol.Verifier

section

/-! ## The literals -/

/-- `RMFE_EMBED` (`keccak.rs:25-28`), in decimal. -/
def embedLit : List ℕ := [3025763659251669, 3612226408043878, 3659286368092212, 2814663869071320,
  4081511718256698, 3096319234539564, 1793164860460636, 2460870985228558, 3586329720921272,
  1237730379074000, 3215427450348550, 2475460758148000, 4437649146411624, 1779783547094742,
  3087275813374842, 4456244284825732, 1774580916524446, 3050085846400674, 1767573208069130,
  2444913787669866, 3535146416138260, 3777969407764812, 1515947212891374, 4406581032758578,
  1990420989879438, 2825448531956598, 3393994828029348, 1474917539936988, 1734702931923816,
  1756895027952582, 1171263351968388, 6051527318503338]

/-- `RMFE_PROJECT` (`keccak.rs:29-46`), in decimal. -/
def projectLit : List ℕ := [1, 40564819207303340847894502572031, 33537842651707486527786793465065,
  12456912984919923567463666144167, 18206257439498349829369973595321,
  7346384580850211334658059520919, 33289351240152929457451498458401,
  28197354155518225006425784105759, 16644675620076464728725749229200,
  37090423351852788361044451684001, 14252235676019302946323930817951,
  18545211675926394180522225842000, 14276695551018034920159182263713,
  32002659226530106001963424222367, 27420757379160687884026842417872,
  32658447951229967940689020579041, 11086025858629895847842844943455,
  16329223975614983970344510289520, 13645114942514852974415350211937,
  32634756084137435654544426409183, 6822557471257426487207675105968,
  6035353598643117225810916668001, 4745259705541245943204901769695,
  23300086402973229036852709620016, 17384922517415717506240501102299,
  37259418429584907055851339576721, 14121612985555870511549198609551,
  8538333020196268862817114299121, 3068947014218725606919476054447,
  22245223436263122400458275604017, 19628138326114519765110243180015,
  20282409603651670423947251286016]

set_option maxRecDepth 100000 in
theorem rmfeEmbed_eq : rmfeEmbed = embedLit := by decide +kernel

/-! ## `RMFE_PROJECT` with the powers of `x` carried along (GOLF3)

`rmfeFactor`'s masks reduce `x^c` modulo the factor by a long division per `c < 105`; the kernel check runs them
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

theorem rmfeEmbed_length : rmfeEmbed.length = 32 := by rw [rmfeEmbed_eq]; rfl

theorem rmfeProject_length : rmfeProject.length = 32 := by rw [rmfeProject_eq]; rfl

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

/-- The parity of the coefficients of `M` that `mask` selects, among the first `105`. -/
def parityL (mask : ℕ) (M : List Bool) : Bool :=
  (List.range 105).foldl (fun acc c ↦ acc ^^ (mask.testBit c && M.getD c false)) false

/-- The embedding lemma on unit vectors, as a boolean. -/
def rmfeOk (emb proj : List ℕ) : Bool :=
  (List.range 32).all fun a ↦ (List.range 32).all fun b ↦ (List.range 32).all fun i ↦
    parityL (proj.getD i 0) (mulGF2 (bitsFrom (emb.getD a 0) 53) (bitsFrom (emb.getD b 0) 53)) ==
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
def colLit : List ℕ := [2137896703, 1430856874, 1414079658, 1430856854, 735800754, 2025230942,
  1232062470, 1599665982, 1388584170, 691162026, 1729085270, 1552474866, 1274681502, 1202163590,
  585270142, 2141438442, 1433596266, 1422776790, 1438334578, 737471006, 2017222150, 1226079038,
  1595824106, 1384510570, 695278870, 1742670834, 1545914206, 1266826438, 1207018430, 574578794,
  2140592426, 1433253590, 1414079666, 1430856862, 726213766, 2027646398, 1236701802, 1601161258,
  1381562134, 700718322, 1731349406, 1544535878, 1267262206, 1207572650, 581406634, 2145551190,
  1436795378, 1416819038, 1439553990, 733691518, 2029316650, 1228693034, 1595177750, 1377720306,
  696644702, 1735466246, 1558121470, 1260701546, 1199717610, 586261398, 2134859890, 1435949342,
  1416476358, 1430856894, 726213802, 2018059434, 1239117206, 1605800562, 1383057438, 693696262,
  1740905726, 1546800042, 1259323242, 1200153302, 586815666, 2141687710, 1440908102, 1420018174,
  1433596266, 734910954, 2025537110, 1240787506, 1597791774, 1377073926, 689854462, 1736832106,
  1550916906, 1272908758, 1193592690, 578960606, 2146542470, 1430216830, 1419172138, 1433253610,
  726213782, 2018059442, 1229530270, 1608215942, 1387696766, 695191594, 1733883690, 1556356310,
  1261587378, 1192214366, 2726879942]

/-- The sixteen parities of `P` at once: the XOR of the columns `cols[c]` over the set bits `c`
of `P`, `c < 105`. -/
def rowOf (P : ℕ) (cols : List ℕ) : ℕ :=
  (List.range 105).foldl (fun acc c ↦ bif P.testBit c then acc ^^^ cols.getD c 0 else acc) 0

/-- Per pair `(a, b)`, the parities of `emb_a · emb_b` are `2^a` if `a = b`, `0` otherwise. -/
def rowsOk (emb cols : List ℕ) : Bool :=
  (List.range 32).all fun a ↦ (List.range 32).all fun b ↦
    rowOf (clmulN (bitsFrom (emb.getD a 0) 53) (emb.getD b 0 % 2 ^ 53)) cols ==
      bif a == b then 1 <<< a else 0

/-- `cols` are the columns of `proj`. -/
def colsOk (proj cols : List ℕ) : Bool :=
  (List.range 32).all fun i ↦ (List.range 105).all fun c ↦
    (cols.getD c 0).testBit i == (proj.getD i 0).testBit c

/-- `rowOf` in one pass over the columns, halving `P` (`rowOf_eq_H`): no `getD`, no `testBit`. -/
def rowOfH : ℕ → List ℕ → ℕ → ℕ
  | _, [], acc => acc
  | P, col :: cs, acc => rowOfH (P / 2) cs (cond (Nat.beq (P % 2) 1) (acc ^^^ col) acc)

/-- `rowsOk` through `rowOfH` (`rowsOk_eq_H`), the form the kernel decides. -/
def rowsOkH (emb cols : List ℕ) : Bool :=
  (List.range 32).all fun a ↦ (List.range 32).all fun b ↦
    rowOfH (clmulN (bitsFrom (emb.getD a 0) 53) (emb.getD b 0 % 2 ^ 53)) cols 0 ==
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

theorem rowOf_eq_H (P : ℕ) {cols : List ℕ} (h : cols.length = 105) : rowOf P cols = rowOfH P cols 0 := by
  rw [rowOf, List.range_eq_range', foldl_rowOf P cols 105 0 0 (by omega)]
  simp [← h]

theorem rowsOk_eq_H {emb cols : List ℕ} (h : cols.length = 105) : rowsOk emb cols = rowsOkH emb cols := by
  simp only [rowsOk, rowsOkH, rowOf_eq_H _ h]

/-! ## `rowsOk_lit` on packed lanes (W32-L kernel golf)

The 32 products `emb_a · emb_b` of a row `a` at once: the embeddings packed in lanes of 128 bits (`packL`), one
carry-less product `clmulN` of the packed number (`clmulN_packL`: no lane overflows, the products have < 106
bits) and one pass of `rowOfH` over all lanes (`rowP`, `rowP_packL`). The kernel decides `checkA_all` (32 rows of
158 steps on 4-kbit numbers) instead of 528 pairs of `rowOfH ∘ clmulN`. -/

section Lanes
/-- `zs` packed in lanes of 128 bits, lane `0` lowest. -/
private def packL : List ℕ → ℕ
  | [] => 0
  | z :: zs => 2 ^ 128 * packL zs + z

private theorem two_pow_mul_add_xor {x y X Y : ℕ} (hx : x < 2 ^ 128) (hy : y < 2 ^ 128) :
    (2 ^ 128 * X + x) ^^^ (2 ^ 128 * Y + y) = 2 ^ 128 * (X ^^^ Y) + (x ^^^ y) := by
  apply Nat.eq_of_testBit_eq
  intro j
  rw [Nat.testBit_xor, Nat.testBit_two_pow_mul_add _ hx, Nat.testBit_two_pow_mul_add _ hy,
    Nat.testBit_two_pow_mul_add _ (Nat.xor_lt_two_pow hx hy), Nat.testBit_xor, Nat.testBit_xor]
  split_ifs <;> rfl

private theorem packL_xor : ∀ (xs ys : List ℕ), xs.length = ys.length → (∀ x ∈ xs, x < 2 ^ 128) →
    (∀ y ∈ ys, y < 2 ^ 128) → packL xs ^^^ packL ys = packL (List.zipWith (· ^^^ ·) xs ys)
  | [], [], _, _, _ => rfl
  | x :: xs, y :: ys, h, hx, hy => by
    simp only [packL, List.zipWith_cons_cons]
    rw [two_pow_mul_add_xor (hx x (by simp)) (hy y (by simp)),
      packL_xor xs ys (by simpa using h) (fun a ha ↦ hx a (by simp [ha])) (fun a ha ↦ hy a (by simp [ha]))]
  | [], _ :: _, h, _, _ => by simp at h
  | _ :: _, [], h, _, _ => by simp at h

private theorem packL_shl1 : ∀ (zs : List ℕ), packL zs <<< 1 = packL (zs.map (· <<< 1))
  | [] => rfl
  | z :: zs => by
    simp only [packL, List.map_cons]
    rw [← packL_shl1 zs]
    simp only [Nat.shiftLeft_eq]; ring

private theorem packL_mul (col : ℕ) : ∀ (zs : List ℕ), packL zs * col = packL (zs.map (· * col))
  | [] => by simp [packL]
  | z :: zs => by
    simp only [packL, List.map_cons]
    rw [← packL_mul col zs]; ring

private theorem packL_zero : ∀ (zs : List ℕ), (∀ z ∈ zs, z = 0) → packL zs = 0
  | [] , _ => rfl
  | z :: zs, h => by
    simp only [packL]
    rw [packL_zero zs (fun a ha ↦ h a (by simp [ha])), h z (by simp)]; norm_num

private theorem testBit_packL : ∀ (zs : List ℕ), (∀ z ∈ zs, z < 2 ^ 128) → ∀ n,
    (packL zs).testBit n = (zs.getD (n / 128) 0).testBit (n % 128)
  | [], _, n => by simp [packL]
  | z :: zs, h, n => by
    simp only [packL]
    rw [Nat.testBit_two_pow_mul_add _ (h z (by simp))]
    split_ifs with hn
    · rw [Nat.div_eq_of_lt hn, Nat.mod_eq_of_lt hn]; rfl
    · rw [testBit_packL zs (fun a ha ↦ h a (by simp [ha]))]
      have e1 : n / 128 = (n - 128) / 128 + 1 := by omega
      have e2 : n % 128 = (n - 128) % 128 := by omega
      rw [e1, e2]; rfl

private theorem getD_map_zero (f : ℕ → ℕ) (hf : f 0 = 0) : ∀ (l : List ℕ) (i : ℕ), (l.map f).getD i 0 = f (l.getD i 0)
  | [], i => by simp [hf]
  | x :: l, 0 => rfl
  | x :: l, i + 1 => by simp only [List.map_cons, List.getD_cons_succ]; exact getD_map_zero f hf l i

private theorem getD_replicate_one (n i : ℕ) : (List.replicate n 1).getD i 0 = if i < n then 1 else 0 := by
  rw [List.getD_eq_getElem?_getD]
  split_ifs with h
  · simp [h]
  · simp [show n ≤ i by omega]

private theorem packL_land (c : ℕ) (hc : c < 128) (ps : List ℕ) (hp : ∀ p ∈ ps, p < 2 ^ 128) :
    (packL ps >>> c) &&& packL (List.replicate ps.length 1) = packL (ps.map (fun p ↦ (p >>> c) % 2)) := by
  have h1 : ∀ z ∈ List.replicate ps.length 1, z < 2 ^ 128 := by
    intro z hz; rw [List.eq_of_mem_replicate hz]; norm_num
  have h2 : ∀ z ∈ ps.map (fun p ↦ (p >>> c) % 2), z < 2 ^ 128 := by
    intro z hz; obtain ⟨p, -, rfl⟩ := List.mem_map.1 hz; omega
  apply Nat.eq_of_testBit_eq
  intro k
  rw [Nat.testBit_land, Nat.testBit_shiftRight, testBit_packL _ hp, testBit_packL _ h1, testBit_packL _ h2,
    getD_replicate_one, getD_map_zero _ (by simp)]
  by_cases hk : k % 128 = 0
  · have e1 : (c + k) / 128 = k / 128 := by omega
    have e2 : (c + k) % 128 = c := by omega
    rw [e1, e2, hk]
    split_ifs with hl
    · have hm : ∀ x : ℕ, (x % 2).testBit 0 = x.testBit 0 := fun x ↦ by
        simpa using Nat.testBit_mod_two_pow x 1 0
      rw [hm, Nat.testBit_shiftRight]; simp
    · rw [List.getD_eq_default _ _ (by omega)]; simp
  · have hb : ∀ x < 2, x.testBit (k % 128) = false := by
      intro x hx
      have h2 : (2 : ℕ) ≤ 2 ^ (k % 128) := by
        calc (2 : ℕ) = 2 ^ 1 := rfl
          _ ≤ 2 ^ (k % 128) := Nat.pow_le_pow_right (by norm_num) (by omega)
      exact Nat.testBit_lt_two_pow (lt_of_lt_of_le hx h2)
    rw [hb _ (by split_ifs <;> norm_num), hb _ (Nat.mod_lt _ (by norm_num)), Bool.and_false]


private theorem packL_inj : ∀ (xs ys : List ℕ), xs.length = ys.length → (∀ x ∈ xs, x < 2 ^ 128) →
    (∀ y ∈ ys, y < 2 ^ 128) → packL xs = packL ys → xs = ys
  | [], [], _, _, _, _ => rfl
  | x :: xs, y :: ys, h, hx, hy, he => by
    simp only [packL] at he
    have hx' := hx x (by simp)
    have hy' := hy y (by simp)
    have h1 : x = y := by
      have := congrArg (· % 2 ^ 128) he
      rwa [Nat.mul_add_mod, Nat.mul_add_mod, Nat.mod_eq_of_lt hx', Nat.mod_eq_of_lt hy'] at this
    subst h1
    have h2 : packL xs = packL ys := by
      have := congrArg (· / 2 ^ 128) he
      rwa [Nat.mul_add_div (by positivity), Nat.mul_add_div (by positivity), Nat.div_eq_of_lt hx', add_zero,
        add_zero] at this
    rw [packL_inj xs ys (by simpa using h) (fun a ha ↦ hx a (by simp [ha])) (fun a ha ↦ hy a (by simp [ha])) h2]
  | [], _ :: _, h, _, _, _ => by simp at h
  | _ :: _, [], h, _, _, _ => by simp at h

private theorem clmulN_lt : ∀ (A : List Bool) (y m : ℕ), y < 2 ^ m → clmulN A y < 2 ^ (A.length + m)
  | [], y, m, _ => by simp [clmulN]
  | a :: A, y, m, hy => by
    rw [clmulN, List.length_cons]
    apply Nat.xor_lt_two_pow
    · cases a
      · simp
      · exact lt_of_lt_of_le hy (Nat.pow_le_pow_right (by norm_num) (by omega))
    · rw [Nat.shiftLeft_eq, show A.length + 1 + m = (A.length + m) + 1 by omega, pow_succ]
      exact Nat.mul_lt_mul_of_pos_right (clmulN_lt A y m hy) (by norm_num)

private theorem clmulN_packL : ∀ (A : List Bool) (ys : List ℕ), A.length + 53 ≤ 127 → (∀ y ∈ ys, y < 2 ^ 53) →
    clmulN A (packL ys) = packL (ys.map (clmulN A))
  | [], ys, _, _ => by
    rw [clmulN, packL_zero]; intro z hz; obtain ⟨y, -, rfl⟩ := List.mem_map.1 hz; rfl
  | a :: A, ys, hA, hy => by
    rw [List.length_cons] at hA
    have hc : cond a (packL ys) 0 = packL (ys.map fun y ↦ cond a y 0) := by
      cases a
      · rw [packL_zero (ys.map _) (by intro z hz; obtain ⟨y, -, rfl⟩ := List.mem_map.1 hz; rfl)]; rfl
      · show packL ys = packL (ys.map fun y ↦ y); simp
    rw [clmulN, hc, clmulN_packL A ys (by omega) hy, packL_shl1, List.map_map,
      packL_xor _ _ (by simp)]
    · rw [List.zipWith_map, List.zipWith_self]
      rfl
    · intro z hz; obtain ⟨y, hy', rfl⟩ := List.mem_map.1 hz
      cases a
      · simp
      · exact lt_of_lt_of_le (hy y hy') (Nat.pow_le_pow_right (by norm_num) (by omega))
    · intro z hz; obtain ⟨y, hy', rfl⟩ := List.mem_map.1 hz
      simp only [Function.comp, Nat.shiftLeft_eq]
      calc clmulN A y * 2 ^ 1 < 2 ^ (A.length + 53) * 2 ^ 1 :=
            Nat.mul_lt_mul_of_pos_right (clmulN_lt A y 53 (hy y hy')) (by norm_num)
        _ ≤ 2 ^ 128 := by rw [← pow_add]; exact Nat.pow_le_pow_right (by norm_num) (by omega)

/-- `rowOfH` on all lanes at once (the kernel's form). -/
private def rowP (L : ℕ) : List ℕ → ℕ → ℕ → ℕ
  | [], _, acc => acc
  | col :: cs, Q, acc => rowP L cs (Q >>> 1) (acc ^^^ ((Q &&& L) * col))

private theorem rowOfH_lt : ∀ (cs : List ℕ) (P acc : ℕ), acc < 2 ^ 32 → (∀ c ∈ cs, c < 2 ^ 32) → rowOfH P cs acc < 2 ^ 32
  | [], _, acc, h, _ => h
  | c :: cs, P, acc, h, hc => by
    rw [rowOfH]
    apply rowOfH_lt cs _ _ _ (fun x hx ↦ hc x (by simp [hx]))
    cases Nat.beq (P % 2) 1
    · exact h
    · exact Nat.xor_lt_two_pow h (hc c (by simp))

private theorem zipWith_zipWith_map {F : ℕ → ℕ → ℕ} {G : ℕ → ℕ → ℕ} {H : ℕ → ℕ} :
    ∀ (ps accs : List ℕ), List.zipWith F ps (List.zipWith G accs (ps.map H)) =
      List.zipWith (fun p a ↦ F p (G a (H p))) ps accs
  | [], _ => by simp
  | _ :: _, [] => by simp
  | p :: ps, a :: accs => by simp only [List.map_cons, List.zipWith_cons_cons, zipWith_zipWith_map ps accs]

private theorem zipWith_snd : ∀ (ps accs : List ℕ), accs.length = ps.length → List.zipWith (fun _ a ↦ a) ps accs = accs
  | [], [], _ => rfl
  | p :: ps, a :: accs, h => by simp only [List.zipWith_cons_cons, zipWith_snd ps accs (by simpa using h)]
  | [], _ :: _, h => by simp at h
  | _ :: _, [], h => by simp at h

private theorem mem_zipWith_xor_lt {n : ℕ} : ∀ (l1 l2 : List ℕ), (∀ x ∈ l1, x < 2 ^ n) → (∀ y ∈ l2, y < 2 ^ n) →
    ∀ z ∈ List.zipWith (· ^^^ ·) l1 l2, z < 2 ^ n
  | [], _, _, _, z, hz => by simp at hz
  | _ :: _, [], _, _, z, hz => by simp at hz
  | x :: l1, y :: l2, h1, h2, z, hz => by
    rw [List.zipWith_cons_cons, List.mem_cons] at hz
    rcases hz with rfl | hz
    · exact Nat.xor_lt_two_pow (h1 x (by simp)) (h2 y (by simp))
    · exact mem_zipWith_xor_lt l1 l2 (fun a ha ↦ h1 a (by simp [ha])) (fun a ha ↦ h2 a (by simp [ha])) z hz

private theorem rowP_packL : ∀ (cs : List ℕ) (c : ℕ) (ps accs : List ℕ), accs.length = ps.length →
    (∀ p ∈ ps, p < 2 ^ 128) → (∀ x ∈ accs, x < 2 ^ 32) → (∀ col ∈ cs, col < 2 ^ 32) → c + cs.length ≤ 127 →
    rowP (packL (List.replicate ps.length 1)) cs (packL ps >>> c) (packL accs) =
      packL (List.zipWith (fun p acc ↦ rowOfH (p >>> c) cs acc) ps accs)
  | [], c, ps, accs, hl, _, _, _, _ => by
    simp only [rowP]
    rw [show (fun p acc ↦ rowOfH (p >>> c) [] acc) = (fun _ a ↦ a) from rfl, zipWith_snd ps accs hl]
  | col :: cs, c, ps, accs, hl, hp, ha, hc, hlen => by
    rw [List.length_cons] at hlen
    have hcol : col < 2 ^ 32 := hc col (by simp)
    simp only [rowP]
    rw [packL_land c (by omega) ps hp, packL_mul, List.map_map, ← Nat.shiftRight_add,
      packL_xor accs _ (by simp [hl]) (fun x hx ↦ lt_trans (ha x hx) (by norm_num))]
    · simp only [Function.comp_def]
      have hb : ∀ z ∈ ps.map (fun p ↦ (p >>> c) % 2 * col), z < 2 ^ 32 := by
        intro z hz; obtain ⟨p, -, rfl⟩ := List.mem_map.1 hz
        calc (p >>> c) % 2 * col ≤ 1 * col := Nat.mul_le_mul_right _ (by omega)
          _ < 2 ^ 32 := by omega
      rw [rowP_packL cs (c + 1) ps _ (by simp [hl]) hp (mem_zipWith_xor_lt _ _ ha hb)
          (fun x hx ↦ hc x (by simp [hx])) (by omega),
        zipWith_zipWith_map]
      congr 1
      congr 1
      funext p acc
      simp only [rowOfH]
      rw [show (p >>> c) / 2 = p >>> (c + 1) by rw [Nat.shiftRight_add, Nat.shiftRight_eq_div_pow (p >>> c) 1]]
      rcases Nat.mod_two_eq_zero_or_one (p >>> c) with h | h <;> simp [h]
    · intro z hz; obtain ⟨p, -, rfl⟩ := List.mem_map.1 hz
      simp only [Function.comp]
      calc (p >>> c) % 2 * col ≤ 1 * col := Nat.mul_le_mul_right _ (by omega)
        _ < 2 ^ 128 := by omega

private theorem bitsFrom_length : ∀ (n k : ℕ), (bitsFrom n k).length = k
  | _, 0 => rfl
  | n, k + 1 => by rw [bitsFrom, List.length_cons, bitsFrom_length]

/-- The lanes check for row `a`: all 32 products `emb_a · emb_b` at once. -/
private def checkA (a : ℕ) : Bool :=
  Nat.beq (rowP (packL (List.replicate 32 1)) colLit (clmulN (bitsFrom (embedLit.getD a 0) 53) (packL embedLit)) 0)
    (packL ((List.range 32).map fun b ↦ bif a == b then 1 <<< a else 0))

private theorem checkA_all : (List.range 32).all checkA = true := by decide +kernel

private theorem embedLit_lt : (embedLit.length = 32 ∧ ∀ e ∈ embedLit, e < 2 ^ 53) ∧
    (colLit.length = 105 ∧ ∀ c ∈ colLit, c < 2 ^ 32) := by decide +kernel

private theorem rowsOkH_of_checkA : rowsOkH embedLit colLit = true := by
  obtain ⟨⟨hEl, hE⟩, hCl, hC⟩ := embedLit_lt
  simp only [rowsOkH, List.all_eq_true, List.mem_range, beq_iff_eq]
  intro a ha b hb
  have h := List.all_eq_true.1 checkA_all a (List.mem_range.2 ha)
  simp only [checkA, Nat.beq_eq] at h
  set A := bitsFrom (embedLit.getD a 0) 53 with hA
  have hAl : A.length + 53 ≤ 127 := by rw [hA, bitsFrom_length]; norm_num
  have hlt : ∀ e ∈ embedLit, clmulN A e < 2 ^ 128 := fun e he ↦
    lt_of_lt_of_le (clmulN_lt A e 53 (hE e he)) (Nat.pow_le_pow_right (by norm_num) (by omega))
  rw [clmulN_packL A embedLit hAl hE] at h
  have h2 : rowP (packL (List.replicate (embedLit.map (clmulN A)).length 1)) colLit
      (packL (embedLit.map (clmulN A)) >>> 0) (packL (List.replicate 32 0)) =
        packL ((List.range 32).map fun b ↦ bif a == b then 1 <<< a else 0) := by
    rw [Nat.shiftRight_zero, packL_zero (List.replicate 32 0) (fun z hz ↦ List.eq_of_mem_replicate hz),
      List.length_map, hEl]
    exact h
  rw [rowP_packL colLit 0 _ _ (by simp [hEl]) (by intro p hp; obtain ⟨e, he, rfl⟩ := List.mem_map.1 hp; exact hlt e he)
      (fun x hx ↦ by rw [List.eq_of_mem_replicate hx]; norm_num) hC (by omega)] at h2
  have hl := packL_inj _ _ (by simp [hEl]) (by
      intro x hx
      obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hx
      rw [List.getElem_zipWith]
      exact lt_of_lt_of_le (rowOfH_lt _ _ _ (by rw [List.getElem_replicate]; norm_num) hC) (by norm_num))
    (by
      intro x hx
      obtain ⟨i, -, rfl⟩ := List.mem_map.1 hx
      cases hai : (a == i)
      · simp
      · simp only [Bool.cond_true, Nat.one_shiftLeft]
        exact Nat.pow_lt_pow_right (by norm_num) (by omega)) h2
  have hb' := congrArg (fun l ↦ l.getD b 0) hl
  simp only [List.getD_eq_getElem?_getD, List.getElem?_zipWith, List.getElem?_map, List.getElem?_range hb,
    List.getElem?_replicate] at hb'
  have hb53 : embedLit.getD b 0 % 2 ^ 53 = embedLit.getD b 0 := Nat.mod_eq_of_lt (by
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by omega)]
    exact hE _ (List.getElem_mem _))
  rw [hb53]
  rw [List.getElem?_eq_getElem (by omega)] at hb'
  simpa [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (show b < embedLit.length by omega),
    show b < 32 from hb] using hb'

end Lanes

set_option maxRecDepth 100000 in
theorem rowsOk_lit : rowsOk embedLit colLit = true := by
  rw [rowsOk_eq_H rfl]; exact rowsOkH_of_checkA

/-- Column `c` of the masks `projs` (bit `i` is bit `c` of `projs[i]`), built bit by bit (proof help). -/
private def colOf : List ℕ → ℕ → ℕ
  | [], _ => 0
  | p :: ps, c => 2 ^ 1 * colOf ps c + (p >>> c) % 2

private theorem testBit_colOf : ∀ (ps : List ℕ) (c i : ℕ), (colOf ps c).testBit i = (ps.getD i 0).testBit c
  | [], c, i => by simp [colOf]
  | p :: ps, c, i => by
    rw [colOf, Nat.testBit_two_pow_mul_add _ (Nat.mod_lt _ (by norm_num))]
    split_ifs with hi
    · obtain rfl : i = 0 := by omega
      simpa [Nat.testBit_shiftRight] using Nat.testBit_mod_two_pow (p >>> c) 1 0
    · obtain ⟨j, rfl⟩ : ∃ j, i = j + 1 := ⟨i - 1, by omega⟩
      rw [testBit_colOf ps c, Nat.add_sub_cancel]; rfl

/-- The columns against `colOf`, in one pass (the form the kernel decides for `colsOk_lit`). -/
private def colsOkR (projs : List ℕ) : List ℕ → ℕ → Bool
  | [], _ => true
  | col :: cs, c => Nat.beq col (colOf projs c) && colsOkR projs cs (c + 1)

private theorem colsOkR_getD (projs : List ℕ) : ∀ (cs : List ℕ) (k : ℕ), colsOkR projs cs k = true →
    ∀ c < cs.length, cs.getD c 0 = colOf projs (k + c)
  | [], _, _, c, hc => by simp at hc
  | col :: cs, k, h, c, hc => by
    simp only [colsOkR, Bool.and_eq_true, Nat.beq_eq] at h
    rcases c with _ | c
    · simpa using h.1
    · rw [List.getD_cons_succ, colsOkR_getD projs cs (k + 1) h.2 c (by simpa using hc)]
      congr 1; omega

theorem colsOk_lit : colsOk projectLit colLit = true := by
  have h := colsOkR_getD projectLit colLit 0 (by decide +kernel)
  simp only [colsOk, List.all_eq_true, List.mem_range, beq_iff_eq]
  intro i _ c hc
  rw [h c (by rw [show colLit.length = 105 from rfl]; exact hc), Nat.zero_add, testBit_colOf]

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

theorem rmfeOk_lit_at {a b i : ℕ} (ha : a < 32) (hb : b < 32) (hi : i < 32) :
    parityL (projectLit.getD i 0)
      (mulGF2 (bitsFrom (embedLit.getD a 0) 53) (bitsFrom (embedLit.getD b 0) 53)) =
        (i == a && a == b) := by
  have hr : rowOf (clmulN (bitsFrom (embedLit.getD a 0) 53) (embedLit.getD b 0 % 2 ^ 53)) colLit =
      bif a == b then 1 <<< a else 0 := by
    have h := rowsOk_lit
    simp only [rowsOk, List.all_eq_true, List.mem_range] at h
    exact eq_of_beq (h a ha b hb)
  have hc : ∀ c ∈ List.range 105, (colLit.getD c 0).testBit i = (projectLit.getD i 0).testBit c := by
    have h := colsOk_lit
    simp only [colsOk, List.all_eq_true, List.mem_range] at h
    exact fun c hc ↦ eq_of_beq (h i hi c (List.mem_range.1 hc))
  unfold parityL
  simp_rw [getD_mulGF2 (getD_bitsFrom_mod _ 53)]
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
