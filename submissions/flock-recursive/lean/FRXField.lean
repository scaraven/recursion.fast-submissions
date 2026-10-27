-- New for `flock-recursive` (BLUEPRINT §6.3–6.4, revision 3; stage S-H1, track L-ext).
import FRXDsl
import FRField256
import CompPoly.Fields.Binary.BF64.Reduce

/-!
# Field arithmetic as `XIR` blocks

`BF64` (`B64`), `F` and `K` multiplication, squaring and inversion as straight-line `XIR` blocks
on the machine's words, with `*_sem` theorems tying each to `FRField128`/`FRField256`'s
operations, and exact step counts on the compiled code (`seq` nodes included).

An element sits in consecutive registers: a `B64` in one word, an `F` element `c₀ + c₁ y` in two
(`c₀` first), a `K` element `f₀ + f₁ u` in four (`f₀` first): `rdB`, `rdF`, `rdK`.

## The `GF(2^64)` product on the machine

The machine has the carry-less product (`clmul`, `clmulh`: the low and high words of the
128-bit product). A product is `clmul`, `clmulh` and a reduction by `x^64 = x^4 + x^3 + x + 1`
that uses the machine's carry-less product again (`redW`, five operations):
`lo + x^64 hi ≡ lo + hi·r = lo + (hi·r)_lo + x^64 (hi·r)_hi ≡ lo + (hi·r)_lo + ((hi·r)_hi · r)_lo`,
`r = 0x1B`, where `(hi·r)_hi` has at most 5 bits, so the last product has no high word
(`Qw_red`). The `F` product is `F.mul`'s Karatsuba with lazy reduction (three `clmul` pairs,
three reductions, `β = x^63` as a shift pair): 29 operations, **57 steps** (BLUEPRINT §6.3 budgets
86). The `K` product is three `F` products, `α ·` (three `β ·`) and the additions.

## Scratch cells and costs

`B64` blocks use cells `5 … 8` (`invB` also `9 … 11`); `F` blocks `5 … 14` (`invF` also
`15 … 18`); `K` blocks `5 … 30` (`invK` also `31 … 38`). A routine's operands and result are
registers above its scratch (hypotheses such as `15 ≤ a`); a result may overwrite an operand.
Exact step counts on the compiled code (`steps_*`, equal to `cost_*`; measured by the contract's
interpreter in `logs/S-H1/stepcount.log`):

`mulB`, `sqB` 13; `invB` 1,033; `mulF` **57**; `sqF` 45; `addF` 3; `invF` 1,107; `mulK` 233;
`sqK` 143; `addK` 7; `invK` 1,379.
-/

namespace FR.X

open RecursionFast Polynomial BinaryField B64

/-! ## Words as field elements -/

/-- The word as a `B64`. -/
def wB (w : Word) : B64 := ⟨⟨w⟩⟩

/-- The `B64` in register `a`. -/
def rdB (M : Mem) (a : ℕ) : B64 := wB (rd M a)

/-- The `F` element in registers `a, a + 1`. -/
def rdF (M : Mem) (a : ℕ) : F := ⟨rdB M a, rdB M (a + 1)⟩

/-- The `K` element in registers `a … a + 3`. -/
def rdK (M : Mem) (a : ℕ) : K := ⟨rdF M a, rdF M (a + 2)⟩

/-! ## Word-level operations -/

/-- The low word of the carry-less product. -/
def clo (a b : Word) : Word := XOp.clmul.eval a b
/-- The high word of the carry-less product. -/
def chi (a b : Word) : Word := XOp.clmulh.eval a b

/-- The reduction of `lo + x^64 hi` by two carry-less products with `0x1B`. -/
def redW (lo hi : Word) : Word := lo ^^^ clo hi 0x1B ^^^ clo (chi hi 0x1B) 0x1B

/-- The `GF(2^64)` product of words. -/
def mulBW (a b : Word) : Word := redW (clo a b) (chi a b)

/-- `β r = x^63 r`: the shift pair, reduced. -/
def betaW (r : Word) : Word := redW (r <<< 63) (r >>> 1)

/-- The `F` product of `a₀ + a₁ y` and `b₀ + b₁ y`, as `F.mul` computes it. -/
def mulFW (a₀ a₁ b₀ b₁ : Word) : Word × Word :=
  let r₁ := mulBW a₁ b₁
  (redW (clo a₀ b₀ ^^^ (r₁ <<< 63)) (chi a₀ b₀ ^^^ (r₁ >>> 1)),
    redW (clo (a₀ ^^^ a₁) (b₀ ^^^ b₁) ^^^ clo a₀ b₀) (chi (a₀ ^^^ a₁) (b₀ ^^^ b₁) ^^^ chi a₀ b₀))

/-! ## Polynomials (proof helpers) -/

/-- The class of a word modulo the `GF(2^64)` modulus. -/
noncomputable abbrev Qw (w : Word) : BF64.BF64Quot := AdjoinRoot.mk BF64.basePoly (toPoly w)

theorem Q_wB (w : Word) : Q (wB w).val = Qw w := rfl

theorem Q_add (a b : B64) : Q (a + b).val = Q a.val + Q b.val := by
  rw [show (a + b).val = a.val ^^^ b.val from rfl, Q, P_xor, map_add]

theorem wB_eq_of_Qw {v : Word} {x : B64} (h : Qw v = Q x.val) : wB v = x := by
  apply toBF64_injective; apply BF64.toQuot_injective
  rw [toQuot_toBF64, toQuot_toBF64, Q_wB, h]

theorem clmul_poly (a b : Word) : toPoly (clo a b) + X ^ 64 * toPoly (chi a b) =
    toPoly a * toPoly b := by
  have h := BF64.toPoly_halves (RecursionFast.clmul a b)
  have hc : toPoly (RecursionFast.clmul a b) = toPoly a * toPoly b :=
    toPoly_carryLessMul a b (by norm_num)
  rw [hc] at h
  rw [h]
  simp only [clo, chi, XOp.eval, BF64.highHalf, BF64.lowHalf]
  ring

theorem chi_red_lt (hi : Word) : (chi hi 0x1B).toNat < 2 ^ 5 :=
  BF64.highHalf_lt _ (BF64.carryLessMul_lt hi BF64.reductionConstant hi.isLt
    BF64.reductionConstant_lt (by norm_num))

theorem chi_chi_red (hi : Word) : chi (chi hi 0x1B) 0x1B = 0 := by
  have h : (chi (chi hi 0x1B) 0x1B).toNat < 2 ^ 0 := BF64.highHalf_lt (d := 0) _
    (lt_of_lt_of_le (BF64.carryLessMul_lt (w := 128) (chi hi 0x1B) BF64.reductionConstant
      (chi_red_lt hi) BF64.reductionConstant_lt (by norm_num)) (by norm_num))
  exact BitVec.eq_of_toNat_eq (by simpa using h)

theorem toPoly_red : toPoly (0x1B : Word) = BF64.baseTail := BF64.toPoly_reductionConstant

/-- **The reduction is the class** of `lo + x^64 hi`. -/
theorem Qw_red (lo hi : Word) :
    Qw (redW lo hi) = AdjoinRoot.mk BF64.basePoly (toPoly lo + X ^ 64 * toPoly hi) := by
  have h1 := clmul_poly hi 0x1B
  have h3 := clmul_poly (chi hi 0x1B) 0x1B
  rw [chi_chi_red, show (0 : Word) = BitVec.ofNat 64 0 from rfl, toPoly_zero_eq_zero] at h3
  rw [toPoly_red] at h1 h3
  rw [Qw, AdjoinRoot.mk_eq_mk, BF64.basePoly_eq_add_tail]
  refine ⟨toPoly hi + toPoly (chi hi 0x1B), ?_⟩
  simp only [redW, toPoly_xor]
  linear_combination h1 + h3 - X ^ 64 * (toPoly hi + toPoly (chi hi 0x1B)) * ZMod2Poly.two_eq_zero

theorem shift_poly (r : Word) : toPoly (r <<< 63) + X ^ 64 * toPoly (r >>> 1) =
    toPoly r * X ^ 63 := by
  have h := P_shiftLeft (⟨r⟩ : UInt64) 63 (by norm_num) (s := 63) (r := 1) (by simp) (by simp)
  have e1 : ((⟨r⟩ : UInt64) <<< (63 : UInt64)).toBitVec = r <<< 63 := by simp
  have e2 : ((⟨r⟩ : UInt64) >>> (1 : UInt64)).toBitVec = r >>> 1 := by simp
  simp only [P, e1, e2] at h
  linear_combination h

/-! ## Word-level correctness -/

/-- **The machine's `GF(2^64)` product is `B64`'s.** -/
theorem mulBW_spec (a b : Word) : wB (mulBW a b) = wB a * wB b := by
  apply wB_eq_of_Qw
  rw [Q_mul, Q_wB, Q_wB, mulBW, Qw_red, clmul_poly, map_mul]

theorem Qw_mulBW (a b : Word) : Qw (mulBW a b) = Qw a * Qw b := by
  rw [← Q_wB, mulBW_spec, Q_mul]; rfl

/-- `betaW` is `β ·`. -/
theorem betaW_spec (r : Word) : wB (betaW r) = beta * wB r := by
  apply wB_eq_of_Qw
  rw [Q_mul, Q_beta, Q_wB, betaW, Qw_red, shift_poly, map_mul, mul_comm]

theorem mulFW_c₀ (a₀ a₁ b₀ b₁ : Word) :
    wB (mulFW a₀ a₁ b₀ b₁).1 = wB a₀ * wB b₀ + beta * (wB a₁ * wB b₁) := by
  apply wB_eq_of_Qw
  rw [Q_add, Q_mul, Q_mul, Q_mul, Q_beta, Q_wB, Q_wB, Q_wB, Q_wB, ← Qw_mulBW a₁ b₁]
  have hs := shift_poly (mulBW a₁ b₁)
  have h0 := clmul_poly a₀ b₀
  simp only [mulFW]
  rw [Qw_red, ← map_mul, ← map_mul, ← map_add]
  refine congrArg (AdjoinRoot.mk BF64.basePoly) ?_
  simp only [toPoly_xor]
  linear_combination h0 + hs

theorem mulFW_c₁ (a₀ a₁ b₀ b₁ : Word) :
    wB (mulFW a₀ a₁ b₀ b₁).2 = (wB a₀ + wB a₁) * (wB b₀ + wB b₁) + wB a₀ * wB b₀ := by
  apply wB_eq_of_Qw
  rw [Q_add, Q_mul, Q_mul, Q_add, Q_add, Q_wB, Q_wB, Q_wB, Q_wB]
  have hm := clmul_poly (a₀ ^^^ a₁) (b₀ ^^^ b₁)
  have h0 := clmul_poly a₀ b₀
  rw [toPoly_xor, toPoly_xor] at hm
  simp only [mulFW]
  rw [Qw_red, ← map_add, ← map_add, ← map_mul, ← map_mul, ← map_add]
  refine congrArg (AdjoinRoot.mk BF64.basePoly) ?_
  simp only [toPoly_xor]
  linear_combination hm + h0

/-- **The machine's `F` product is `F`'s.** -/
theorem mulFW_spec (a₀ a₁ b₀ b₁ : Word) :
    (⟨wB (mulFW a₀ a₁ b₀ b₁).1, wB (mulFW a₀ a₁ b₀ b₁).2⟩ : F) =
      (⟨wB a₀, wB a₁⟩ : F) * ⟨wB b₀, wB b₁⟩ := by
  have e : ∀ x : F, x = ⟨x.c₀, x.c₁⟩ := fun _ => rfl
  rw [e ((⟨wB a₀, wB a₁⟩ : F) * ⟨wB b₀, wB b₁⟩), F.mul_c₀, F.mul_c₁, mulFW_c₀, mulFW_c₁]

/-! ## Running blocks (proof helpers) -/

@[simp] theorem eval_clmul (a b : Word) : XOp.clmul.eval a b = clo a b := rfl
@[simp] theorem eval_clmulh (a b : Word) : XOp.clmulh.eval a b = chi a b := rfl
/-- The constant cells of a state satisfying `Inv`. -/
theorem inv_consts {M : Mem} (h : Inv M) : 256 ≤ M.size ∧ rd M 0 = 1 ∧ rd M 2 = 0x1B ∧
    rd M 3 = 63 := ⟨h.1, h.2 0 (by decide), h.2 2 (by decide), h.2 3 (by decide)⟩

theorem rdF_eq {M M' : Mem} {x : ℕ} (h0 : rd M' x = rd M x) (h1 : rd M' (x + 1) = rd M (x + 1)) :
    rdF M' x = rdF M x := by simp only [rdF, rdB, h0, h1]

theorem rdK_eq {M M' : Mem} {x : ℕ} (h : ∀ j < 4, rd M' (x + j) = rd M (x + j)) :
    rdK M' x = rdK M x := by
  have e0 : rd M' x = rd M x := by simpa using h 0 (by decide)
  simp only [rdK, rdF, rdB, e0, h 1 (by decide), h 2 (by decide), h 3 (by decide),
    show x + 2 + 1 = x + 3 by omega]

/-! ## `B64` multiplication and `β ·` -/

/-- `M[d] := reduce(M[lo] + x^64 M[hi])`, with scratch `u`, `v`. -/
def redC (d lo hi u v : ℕ) : List Prim :=
  [.op .clmul u hi cRed, .op .clmulh v hi cRed, .op .clmul v v cRed, .op .xor u lo u,
    .op .xor d u v]

/-- **The `B64` product** `M[d] := M[a] · M[b]` (7 statements, scratch `5 … 8`). -/
def mulBC (d a b : ℕ) : List Prim := [.op .clmul 5 a b, .op .clmulh 6 a b] ++ redC d 5 6 7 8

/-- `M[d] := β · M[r]` (7 statements, scratch `5, 6, 13, 14`). -/
def betaC (d r : ℕ) : List Prim := [.op .shl 13 r c63, .op .shr 14 r cOne] ++ redC d 13 14 5 6

theorem mulBC_dst (d a b : ℕ) : ∀ p ∈ mulBC d a b, p.dst = d ∨ (5 ≤ p.dst ∧ p.dst < 9) := by
  simp [mulBC, redC, Prim.dst]

theorem betaC_dst (d r : ℕ) :
    ∀ p ∈ betaC d r, p.dst = d ∨ p.dst = 5 ∨ p.dst = 6 ∨ p.dst = 13 ∨ p.dst = 14 := by
  simp [betaC, redC, Prim.dst]

theorem mulBC_run {M : Mem} (hM : Inv M) {d a b : ℕ} (hd : 9 ≤ d) (hd' : d < regs)
    (ha : 9 ≤ a) (hb : 9 ≤ b) :
    rd (runPrims (mulBC d a b) M) d = mulBW (rd M a) (rd M b) := by
  obtain ⟨hs, h0, h2, h3⟩ := inv_consts hM
  simp only [regs] at hd'
  simp only [mulBC, redC, List.cons_append, List.nil_append, runPrims_cons, runPrims_nil,
    Prim.run, cRed, mulBW, redW]
  simp (disch := ((try simp only [size_set]); omega)) only [rd_set_self, rd_set_ne, h2,
    eval_clmul, eval_clmulh, eval_xor]

theorem betaC_run {M : Mem} (hM : Inv M) {d r : ℕ} (hd : 7 ≤ d) (hd' : d < regs)
    (hr : r ≠ 13) :
    rd (runPrims (betaC d r) M) d = betaW (rd M r) := by
  obtain ⟨hs, h0, h2, h3⟩ := inv_consts hM
  simp only [regs] at hd'
  simp only [betaC, redC, List.cons_append, List.nil_append, runPrims_cons, runPrims_nil,
    Prim.run, cRed, c63, cOne, betaW, redW]
  simp (disch := ((try simp only [size_set]); omega)) only [rd_set_self, rd_set_ne, h0, h2, h3,
    eval_clmul, eval_clmulh, eval_xor, eval_shl63, eval_shr1]

theorem mulBC_frame (d a b : ℕ) {i : ℕ} (hi : i < 5 ∨ 9 ≤ i) (hd : i ≠ d) (M : Mem) :
    rd (runPrims (mulBC d a b) M) i = rd M i :=
  rd_runPrims_of_not_writes (fun p hp => by have := mulBC_dst d a b p hp; omega) M

theorem mulBC_inv (d a b : ℕ) (hd : 4 ≤ d) {M : Mem} (hM : Inv M) : Inv (runPrims (mulBC d a b) M)
    :=
  inv_runPrims (fun p hp => by have := mulBC_dst d a b p hp; omega) hM

/-! ## `B64` inversion (Itoh–Tsujii, as `B64.inv`) -/

/-- `M[r] := M[r]^(2^k)`: `k` squarings in place. -/
def sqnC (r k : ℕ) : List Prim := (List.replicate k (mulBC r r r)).flatten

/-- `M[r] := M[r]^(2^k) · M[y]`. -/
def stepC (r k y : ℕ) : List Prim := sqnC r k ++ mulBC r r y

/-- **The `B64` inverse** `M[d] := M[a]⁻¹` (`0⁻¹ = 0`): `B64.inv`'s chain, 63 squarings and 10
products in cells `9` (`x`), `10` (the accumulator) and `11` (a copy); 517 statements. -/
def invBC (d a : ℕ) : List Prim :=
  [.op .or 9 a a, .op .or 10 9 9] ++ stepC 10 1 9 ++ stepC 10 1 9 ++ [.op .or 11 10 10] ++
  stepC 10 3 11 ++ stepC 10 1 9 ++ [.op .or 11 10 10] ++ stepC 10 7 11 ++ stepC 10 1 9 ++
  [.op .or 11 10 10] ++ stepC 10 15 11 ++ stepC 10 1 9 ++ [.op .or 11 10 10] ++
  stepC 10 31 11 ++ stepC 10 1 9 ++ mulBC d 10 10

/-- `B64.inv`'s chain on every element. -/
def chainB (u1 : B64) : B64 :=
  let u2 := frob 1 u1 * u1
  let u3 := frob 1 u2 * u1
  let u6 := frob 3 u3 * u3
  let u7 := frob 1 u6 * u1
  let u14 := frob 7 u7 * u7
  let u15 := frob 1 u14 * u1
  let u30 := frob 15 u15 * u15
  let u31 := frob 1 u30 * u1
  let u62 := frob 31 u31 * u31
  let u63 := frob 1 u62 * u1
  u63 * u63

theorem inv_eq_chainB (x : B64) : x⁻¹ = chainB x := by
  show B64.inv x = _
  unfold B64.inv
  split
  · next h =>
    have hx : x = 0 := by cases x; simp only at h; subst h; rfl
    subst hx
    simp [chainB, B64.frob_eq_pow]
  · simp only [chainB, B64.sq_eq_mul]

/-- The chain's registers: `x` in `9`, the accumulator in `10`, the copy in `11`. -/
def ChainSt (M : Mem) (x acc t : B64) : Prop :=
  Inv M ∧ rdB M 9 = x ∧ rdB M 10 = acc ∧ rdB M 11 = t

theorem sqnC_dst (r k : ℕ) : ∀ p ∈ sqnC r k, p.dst = r ∨ (5 ≤ p.dst ∧ p.dst < 9) := by
  intro p hp
  simp only [sqnC, List.mem_flatten, List.mem_replicate] at hp
  obtain ⟨l, ⟨_, rfl⟩, hp⟩ := hp
  exact mulBC_dst r r r p hp

theorem sqnC_run {r : ℕ} (hr : 9 ≤ r) (hr' : r < regs) :
    ∀ (k : ℕ) {M : Mem}, Inv M → rdB (runPrims (sqnC r k) M) r = frob k (rdB M r)
  | 0, _, _ => rfl
  | k + 1, M, hM => by
    rw [show sqnC r (k + 1) = mulBC r r r ++ sqnC r k by simp [sqnC, List.replicate_succ],
      runPrims_append, sqnC_run hr hr' k (mulBC_inv r r r (by omega) hM)]
    simp only [rdB, mulBC_run hM hr hr' hr hr, mulBW_spec, frob, B64.sq_eq_mul]

theorem stepC_dst (r k y : ℕ) : ∀ p ∈ stepC r k y, p.dst = r ∨ (5 ≤ p.dst ∧ p.dst < 9) := by
  intro p hp
  rcases List.mem_append.mp hp with hp | hp
  · exact sqnC_dst r k p hp
  · exact mulBC_dst r r y p hp

theorem stepC_chain {M : Mem} {x acc t : B64} (h : ChainSt M x acc t) (k : ℕ) :
    ChainSt (runPrims (stepC 10 k 9) M) x (frob k acc * x) t ∧
      ChainSt (runPrims (stepC 10 k 11) M) x (frob k acc * t) t := by
  obtain ⟨hM, h9, h10, h11⟩ := h
  have hi := inv_runPrims (fun p hp => by have := sqnC_dst 10 k p hp; omega) hM
  have f9 := rd_runPrims_of_not_writes (i := 9) (fun p hp => by have := sqnC_dst 10 k p hp; omega) M
  have f11 := rd_runPrims_of_not_writes (i := 11)
    (fun p hp => by have := sqnC_dst 10 k p hp; omega) M
  have s10 := sqnC_run (r := 10) (by omega) (by simp [regs]) k hM
  refine ⟨⟨inv_runPrims (fun p hp => by have := stepC_dst 10 k 9 p hp; omega) hM, ?_, ?_, ?_⟩,
    ⟨inv_runPrims (fun p hp => by have := stepC_dst 10 k 11 p hp; omega) hM, ?_, ?_, ?_⟩⟩ <;>
    simp only [stepC, runPrims_append, rdB] at f9 f11 s10 h9 h10 h11 ⊢
  · rw [mulBC_frame _ _ _ (by omega) (by omega), f9, h9]
  · rw [mulBC_run hi (by omega) (by simp [regs]) (by omega) (by omega), mulBW_spec, s10, f9, h9,
      h10]
  · rw [mulBC_frame _ _ _ (by omega) (by omega), f11, h11]
  · rw [mulBC_frame _ _ _ (by omega) (by omega), f9, h9]
  · rw [mulBC_run hi (by omega) (by simp [regs]) (by omega) (by omega), mulBW_spec, s10, f11, h11,
      h10]
  · rw [mulBC_frame _ _ _ (by omega) (by omega), f11, h11]

theorem copy_chain {M : Mem} {x acc t : B64} (h : ChainSt M x acc t) :
    ChainSt (runPrims [.op .or 11 10 10] M) x acc acc := by
  obtain ⟨hM, h9, h10, h11⟩ := h
  have hs : 11 < M.size := by have := hM.1; simp only [regs] at this; omega
  refine ⟨inv_runPrims (by simp [Prim.dst]) hM, ?_, ?_, ?_⟩ <;>
    simp only [runPrims_cons, runPrims_nil, Prim.run, rdB] at h9 h10 ⊢
  · rw [rd_set_ne (by decide), h9]
  · rw [rd_set_ne (by decide), h10]
  · rw [rd_set_self hs, eval_or, BitVec.or_self, h10]

theorem invBC_dst (d a : ℕ) : ∀ p ∈ invBC d a, p.dst = d ∨ (5 ≤ p.dst ∧ p.dst < 12) := by
  intro p hp
  simp only [invBC, List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with ((((((((((((((((hp | hp) | hp) | hp) | hp) | hp) | hp) | hp) | hp) | hp) | hp) |
      hp) |
    hp) | hp) | hp) | hp) | hp) <;>
    first
    | (subst hp; simp [Prim.dst])
    | (have := stepC_dst _ _ _ p hp; omega)
    | (have := mulBC_dst _ _ _ p hp; omega)

/-- **`invBC` computes `B64`'s inverse.** -/
theorem invBC_run {M : Mem} (hM : Inv M) {d a : ℕ} (hd : 12 ≤ d) (hd' : d < regs) :
    rdB (runPrims (invBC d a) M) d = (rdB M a)⁻¹ := by
  have hs : 11 < M.size := by have := hM.1; simp only [regs] at this; omega
  set x := rdB M a
  have h0 : ChainSt (runPrims [.op .or 9 a a, .op .or 10 9 9] M) x x (rdB M 11) := by
    refine ⟨inv_runPrims (by simp [Prim.dst]) hM, ?_, ?_, ?_⟩ <;>
      simp (disch := ((try simp only [size_set]); omega)) only [runPrims_cons, runPrims_nil,
        Prim.run, rdB, x, rd_set_self, rd_set_ne, eval_or, BitVec.or_self]
  have h1 := (stepC_chain h0 1).1
  have h2 := (stepC_chain h1 1).1
  have h3 := (stepC_chain (copy_chain h2) 3).2
  have h4 := (stepC_chain h3 1).1
  have h5 := (stepC_chain (copy_chain h4) 7).2
  have h6 := (stepC_chain h5 1).1
  have h7 := (stepC_chain (copy_chain h6) 15).2
  have h8 := (stepC_chain h7 1).1
  have h9 := (stepC_chain (copy_chain h8) 31).2
  have h10 := (stepC_chain h9 1).1
  simp only [invBC, runPrims_append]
  rw [rdB, mulBC_run h10.1 (by omega) hd' (by omega) (by omega), mulBW_spec, inv_eq_chainB]
  rw [show wB (rd _ 10) = _ from h10.2.2.1]
  rfl

/-! ## `F` multiplication -/

/-- **The `F` product** `M[d, d+1] := M[a, a+1] · M[b, b+1]` (29 statements, scratch `5 … 14`). -/
def mulFC (d a b : ℕ) : List Prim :=
  [.op .clmul 5 a b, .op .clmulh 6 a b, .op .clmul 7 (a + 1) (b + 1),
    .op .clmulh 8 (a + 1) (b + 1), .op .xor 9 a (a + 1), .op .xor 10 b (b + 1),
    .op .clmul 11 9 10, .op .clmulh 12 9 10, .op .xor 11 11 5, .op .xor 12 12 6] ++
  redC 7 7 8 13 14 ++
  [.op .shl 13 7 c63, .op .shr 14 7 cOne, .op .xor 5 5 13, .op .xor 6 6 14] ++
  redC d 5 6 13 14 ++ redC (d + 1) 11 12 13 14

theorem mulFC_run {M : Mem} (hM : Inv M) {d a b : ℕ} (hd : 15 ≤ d) (hd' : d + 2 ≤ regs)
    (ha : 15 ≤ a) (hb : 15 ≤ b) :
    rd (runPrims (mulFC d a b) M) d = (mulFW (rd M a) (rd M (a + 1)) (rd M b) (rd M (b + 1))).1 ∧
    rd (runPrims (mulFC d a b) M) (d + 1) =
      (mulFW (rd M a) (rd M (a + 1)) (rd M b) (rd M (b + 1))).2 := by
  obtain ⟨hs, h0, h2, h3⟩ := inv_consts hM
  simp only [regs] at hd'
  simp only [mulFC, redC, List.cons_append, List.nil_append, runPrims_cons, runPrims_nil,
    Prim.run, cRed, c63, cOne, mulFW, mulBW, redW]
  simp (disch := ((try simp only [size_set]); omega)) only [rd_set_self, rd_set_ne, h0, h2, h3,
    eval_clmul, eval_clmulh, eval_xor, eval_shl63, eval_shr1, and_self]

theorem mulFC_dst (d a b : ℕ) :
    ∀ p ∈ mulFC d a b, p.dst = d ∨ p.dst = d + 1 ∨ (5 ≤ p.dst ∧ p.dst < 15) := by
  simp [mulFC, redC, Prim.dst]

/-- **`mulFC` computes `F`'s product.** -/
theorem mulFC_spec {M : Mem} (hM : Inv M) {d a b : ℕ} (hd : 15 ≤ d) (hd' : d + 2 ≤ regs)
    (ha : 15 ≤ a) (hb : 15 ≤ b) : rdF (runPrims (mulFC d a b) M) d = rdF M a * rdF M b := by
  obtain ⟨h0, h1⟩ := mulFC_run hM hd hd' ha hb
  simp only [rdF, rdB, h0, h1]
  exact mulFW_spec ..

/-! ## Facts about words as field elements -/

theorem wB_xor (x y : Word) : wB (x ^^^ y) = wB x + wB y := rfl

theorem mulBeta_eq (r : B64) : mulBeta r = beta * r :=
  toBF64_injective (by rw [toBF64_mulBeta, toBF64_mul])

theorem betaC_frame (d r : ℕ) {i : ℕ} (hi : i ≠ 5 ∧ i ≠ 6 ∧ i ≠ 13 ∧ i ≠ 14) (hd : i ≠ d)
    (M : Mem) : rd (runPrims (betaC d r) M) i = rd M i :=
  rd_runPrims_of_not_writes (fun p hp => by have := betaC_dst d r p hp; omega) M

theorem betaC_inv (d r : ℕ) (hd : 4 ≤ d) {M : Mem} (hM : Inv M) : Inv (runPrims (betaC d r) M) :=
  inv_runPrims (fun p hp => by have := betaC_dst d r p hp; omega) hM

theorem mulFC_frame (d a b : ℕ) {i : ℕ} (hi : i < 5 ∨ 15 ≤ i) (hd : i ≠ d) (hd1 : i ≠ d + 1)
    (M : Mem) : rd (runPrims (mulFC d a b) M) i = rd M i :=
  rd_runPrims_of_not_writes (fun p hp => by have := mulFC_dst d a b p hp; omega) M

theorem mulFC_inv (d a b : ℕ) (hd : 4 ≤ d) {M : Mem} (hM : Inv M) : Inv (runPrims (mulFC d a b) M)
    :=
  inv_runPrims (fun p hp => by have := mulFC_dst d a b p hp; omega) hM

/-! ## `F` addition and copy -/

/-- `M[d, d+1] := M[a, a+1] + M[b, b+1]` (2 statements). -/
def addFC (d a b : ℕ) : List Prim := [.op .xor d a b, .op .xor (d + 1) (a + 1) (b + 1)]

theorem addFC_dst (d a b : ℕ) : ∀ p ∈ addFC d a b, p.dst = d ∨ p.dst = d + 1 := by
  simp [addFC, Prim.dst]

/-- **`addFC` computes `F`'s sum** (the result may be an operand, not overlap one). -/
theorem addFC_spec {M : Mem} {d a b : ℕ} (hd : d + 1 < M.size) (ha : d ≠ a + 1)
    (hb : d ≠ b + 1) : rdF (runPrims (addFC d a b) M) d = rdF M a + rdF M b := by
  simp (disch := ((try simp only [size_set]); omega)) only [addFC, runPrims_cons, runPrims_nil,
    Prim.run, rdF, rdB, rd_set_self, rd_set_ne, eval_xor, wB_xor]
  rfl

theorem addFC_frame (d a b : ℕ) {i : ℕ} (hd : i ≠ d) (hd1 : i ≠ d + 1) (M : Mem) :
    rd (runPrims (addFC d a b) M) i = rd M i :=
  rd_runPrims_of_not_writes (fun p hp => by have := addFC_dst d a b p hp; omega) M

theorem addFC_inv (d a b : ℕ) (hd : 4 ≤ d) {M : Mem} (hM : Inv M) : Inv (runPrims (addFC d a b) M)
    :=
  inv_runPrims (fun p hp => by have := addFC_dst d a b p hp; omega) hM

/-! ## `F` squaring -/

/-- **The `F` square** `M[d, d+1] := M[a, a+1]^2` (23 statements, scratch `5 … 14`):
`(c₀^2 + β c₁^2) + c₁^2 y`. -/
def sqFC (d a : ℕ) : List Prim :=
  mulBC 9 (a + 1) (a + 1) ++ mulBC 10 a a ++ betaC 11 9 ++ [.op .xor d 10 11, .op .or (d + 1) 9 9]

theorem sqFC_dst (d a : ℕ) :
    ∀ p ∈ sqFC d a, p.dst = d ∨ p.dst = d + 1 ∨ (5 ≤ p.dst ∧ p.dst < 15) := by
  intro p hp
  simp only [sqFC, List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with ((hp | hp) | hp) | hp | hp
  · have := mulBC_dst _ _ _ p hp; omega
  · have := mulBC_dst _ _ _ p hp; omega
  · have := betaC_dst _ _ p hp; omega
  · subst hp; simp [Prim.dst]
  · subst hp; simp [Prim.dst]

/-- **`sqFC` computes `F`'s square.** -/
theorem sqFC_spec {M : Mem} (hM : Inv M) {d a : ℕ} (hd : 15 ≤ d) (hd' : d + 2 ≤ regs)
    (ha : 15 ≤ a) : rdF (runPrims (sqFC d a) M) d = F.sq (rdF M a) := by
  have hr : regs = 256 := rfl
  have i1 := mulBC_inv 9 (a + 1) (a + 1) (by omega) hM
  have i2 := mulBC_inv 10 a a (by omega) i1
  have i3 := betaC_inv 11 9 (by omega) i2
  have v1 := mulBC_run hM (d := 9) (by omega) (by omega) (a := a + 1) (b := a + 1) (by omega)
    (by omega)
  have fa := mulBC_frame 9 (a + 1) (a + 1) (i := a) (by omega) (by omega) M
  have v2 := mulBC_run i1 (d := 10) (by omega) (by omega) (a := a) (b := a) (by omega) (by omega)
  have f29 := mulBC_frame 10 a a (i := 9) (by omega) (by omega) (runPrims (mulBC 9 (a + 1) (a +
      1)) M)
  have v3 := betaC_run i2 (d := 11) (r := 9) (by omega) (by omega) (by omega)
  have f39 := betaC_frame 11 9 (i := 9) (by omega) (by omega)
    (runPrims (mulBC 10 a a) (runPrims (mulBC 9 (a + 1) (a + 1)) M))
  have f310 := betaC_frame 11 9 (i := 10) (by omega) (by omega)
    (runPrims (mulBC 10 a a) (runPrims (mulBC 9 (a + 1) (a + 1)) M))
  have hs := i3.1
  simp only [size_runPrims] at hs
  simp only [sqFC, runPrims_append]
  simp (disch := ((try simp only [size_runPrims, size_set]); omega)) only [runPrims_cons,
    runPrims_nil, Prim.run, rdF, rdB, rd_set_self, rd_set_ne, eval_xor, eval_or, BitVec.or_self,
    wB_xor, v3, f39, f310, v2, f29, v1, fa, mulBW_spec, betaW_spec]
  simp only [F.sq, B64.sq_eq_mul, mulBeta_eq]

theorem sqFC_frame (d a : ℕ) {i : ℕ} (hi : i < 5 ∨ 15 ≤ i) (hd : i ≠ d) (hd1 : i ≠ d + 1)
    (M : Mem) : rd (runPrims (sqFC d a) M) i = rd M i :=
  rd_runPrims_of_not_writes (fun p hp => by have := sqFC_dst d a p hp; omega) M

theorem sqFC_inv (d a : ℕ) (hd : 4 ≤ d) {M : Mem} (hM : Inv M) : Inv (runPrims (sqFC d a) M) :=
  inv_runPrims (fun p hp => by have := sqFC_dst d a p hp; omega) hM

theorem invBC_frame (d a : ℕ) {i : ℕ} (hi : i < 5 ∨ 12 ≤ i) (hd : i ≠ d) (M : Mem) :
    rd (runPrims (invBC d a) M) i = rd M i :=
  rd_runPrims_of_not_writes (fun p hp => by have := invBC_dst d a p hp; omega) M

theorem invBC_inv (d a : ℕ) (hd : 4 ≤ d) {M : Mem} (hM : Inv M) : Inv (runPrims (invBC d a) M) :=
  inv_runPrims (fun p hp => by have := invBC_dst d a p hp; omega) hM

/-! ## `F` inversion -/

/-- **The `F` inverse** `M[d, d+1] := M[a, a+1]⁻¹` (`0⁻¹ = 0`; 554 statements, scratch `5 … 18`):
the norm `n = c₀(c₀ + c₁) + β c₁^2` to `B64`, one `B64` inverse, `n⁻¹ ((c₀ + c₁) + c₁ y)`. -/
def invFC (d a : ℕ) : List Prim :=
  [.op .xor 15 a (a + 1)] ++ mulBC 16 a 15 ++ mulBC 17 (a + 1) (a + 1) ++ betaC 17 17 ++
  [.op .xor 16 16 17] ++ invBC 16 16 ++ mulBC (d + 1) 16 (a + 1) ++ mulBC d 16 15

theorem invFC_dst (d a : ℕ) :
    ∀ p ∈ invFC d a, p.dst = d ∨ p.dst = d + 1 ∨ (5 ≤ p.dst ∧ p.dst < 19) := by
  intro p hp
  simp only [invFC, List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with ((((((hp | hp) | hp) | hp) | hp) | hp) | hp) | hp
  · subst hp; simp [Prim.dst]
  · have := mulBC_dst _ _ _ p hp; omega
  · have := mulBC_dst _ _ _ p hp; omega
  · have := betaC_dst _ _ p hp; omega
  · subst hp; simp [Prim.dst]
  · have := invBC_dst _ _ p hp; omega
  · have := mulBC_dst _ _ _ p hp; omega
  · have := mulBC_dst _ _ _ p hp; omega

/-- **`invFC` computes `F`'s inverse.** -/
theorem invFC_spec {M : Mem} (hM : Inv M) {d a : ℕ} (hd : 19 ≤ d) (hd' : d + 2 ≤ regs)
    (ha : 19 ≤ a) : rdF (runPrims (invFC d a) M) d = (rdF M a)⁻¹ := by
  have hr : regs = 256 := rfl
  have hs : 256 ≤ M.size := hM.1
  simp only [invFC, runPrims_append]
  set M1 := runPrims [.op .xor 15 a (a + 1)] M with hM1
  have i1 : Inv M1 := xorC_inv 15 a (a + 1) (by omega) hM
  have v1 : rd M1 15 = rd M a ^^^ rd M (a + 1) := rd_xor_run (by omega)
  have f1a : rd M1 a = rd M a := xorC_frame _ _ _ (by omega) M
  have f1b : rd M1 (a + 1) = rd M (a + 1) := xorC_frame _ _ _ (by omega) M
  set M2 := runPrims (mulBC 16 a 15) M1 with hM2
  have i2 : Inv M2 := mulBC_inv 16 a 15 (by omega) i1
  have v2 : rd M2 16 = mulBW (rd M1 a) (rd M1 15) := mulBC_run i1 (by omega) (by omega) (by omega)
    (by omega)
  have f2a : rd M2 15 = rd M1 15 := mulBC_frame 16 a 15
    (i := 15) (by omega) (by omega) M1
  have f2b : rd M2 (a + 1) = rd M1 (a + 1) := mulBC_frame 16 a 15
    (i := a + 1) (by omega) (by omega) M1
  set M3 := runPrims (mulBC 17 (a + 1) (a + 1)) M2 with hM3
  have i3 : Inv M3 := mulBC_inv 17 (a + 1) (a + 1) (by omega) i2
  have v3 : rd M3 17 = mulBW (rd M2 (a + 1)) (rd M2 (a + 1)) :=
    mulBC_run i2 (by omega) (by omega) (by omega) (by omega)
  have f3a : rd M3 15 = rd M2 15 := mulBC_frame 17 (a + 1) (a + 1) (i := 15) (by omega) (by omega)
      M2
  have f3b : rd M3 16 = rd M2 16 := mulBC_frame 17 (a + 1) (a + 1) (i := 16) (by omega) (by omega)
      M2
  have f3c : rd M3 (a + 1) = rd M2 (a + 1) :=
    mulBC_frame 17 (a + 1) (a + 1) (i := a + 1) (by omega) (by omega) M2
  set M4 := runPrims (betaC 17 17) M3 with hM4
  have i4 : Inv M4 := betaC_inv 17 17 (by omega) i3
  have v4 : rd M4 17 = betaW (rd M3 17) := betaC_run i3 (by omega) (by omega) (by omega)
  have f4a : rd M4 15 = rd M3 15 := betaC_frame 17 17
    (i := 15) (by omega) (by omega) M3
  have f4b : rd M4 16 = rd M3 16 := betaC_frame 17 17
    (i := 16) (by omega) (by omega) M3
  have f4c : rd M4 (a + 1) = rd M3 (a + 1) := betaC_frame 17 17
    (i := a + 1) (by omega) (by omega) M3
  set M5 := runPrims [.op .xor 16 16 17] M4 with hM5
  have i5 : Inv M5 := xorC_inv 16 16 17 (by omega) i4
  have v5 : rd M5 16 = rd M4 16 ^^^ rd M4 17 := rd_xor_run (by have := i4.1; omega)
  have f5a : rd M5 15 = rd M4 15 := xorC_frame 16 16 17
    (i := 15) (by omega) M4
  have f5b : rd M5 (a + 1) = rd M4 (a + 1) := xorC_frame 16 16 17
    (i := a + 1) (by omega) M4
  set M6 := runPrims (invBC 16 16) M5 with hM6
  have i6 : Inv M6 := invBC_inv 16 16 (by omega) i5
  have v6 : rdB M6 16 = (rdB M5 16)⁻¹ := invBC_run i5 (by omega) (by omega)
  have f6a : rd M6 15 = rd M5 15 := invBC_frame 16 16
    (i := 15) (by omega) (by omega) M5
  have f6b : rd M6 (a + 1) = rd M5 (a + 1) := invBC_frame 16 16
    (i := a + 1) (by omega) (by omega) M5
  set M7 := runPrims (mulBC (d + 1) 16 (a + 1)) M6 with hM7
  have i7 : Inv M7 := mulBC_inv (d + 1) 16 (a + 1) (by omega) i6
  have v7 : rd M7 (d + 1) = mulBW (rd M6 16) (rd M6 (a + 1)) :=
    mulBC_run i6 (by omega) (by omega) (by omega) (by omega)
  have f7a : rd M7 15 = rd M6 15 := mulBC_frame (d + 1) 16 (a + 1) (i := 15) (by omega) (by omega)
      M6
  have f7b : rd M7 16 = rd M6 16 := mulBC_frame (d + 1) 16 (a + 1) (i := 16) (by omega) (by omega)
      M6
  have v8 : rd (runPrims (mulBC d 16 15) M7) d = mulBW (rd M7 16) (rd M7 15) :=
    mulBC_run i7 (by omega) (by omega) (by omega) (by omega)
  have f8 : rd (runPrims (mulBC d 16 15) M7) (d + 1) = rd M7 (d + 1) := mulBC_frame d 16 15
    (i := d + 1) (by omega) (by omega) M7
  simp only [rdB] at v6
  simp only [rdF, rdB, v8, f8, v7, mulBW_spec, f7a, f7b, v6, f6a, f6b, v5, f5a, f5b, f4a, f4b, f4c,
    v4, betaW_spec, f3a, f3b, f3c, v3, v2, f2a, f2b, v1, f1a, f1b, wB_xor]
  show _ = F.inv _
  simp only [F.inv, F.smulBase, F.norm, B64.sq_eq_mul, mulBeta_eq]

theorem invFC_frame (d a : ℕ) {i : ℕ} (hi : i < 5 ∨ 19 ≤ i) (hd : i ≠ d) (hd1 : i ≠ d + 1)
    (M : Mem) : rd (runPrims (invFC d a) M) i = rd M i :=
  rd_runPrims_of_not_writes (fun p hp => by have := invFC_dst d a p hp; omega) M

theorem invFC_inv (d a : ℕ) (hd : 4 ≤ d) {M : Mem} (hM : Inv M) : Inv (runPrims (invFC d a) M) :=
  inv_runPrims (fun p hp => by have := invFC_dst d a p hp; omega) hM

/-! ## `K` arithmetic -/

/-- The frame of an `F`-valued block at an `F` register: blocks that write their result
`d, d + 1` and scratch below `lo` leave registers `x, x + 1` above `lo`, away from `d`. -/
theorem rdF_frame {ps : List Prim} {d lo : ℕ}
    (hdst : ∀ p ∈ ps, p.dst = d ∨ p.dst = d + 1 ∨ p.dst < lo) {x : ℕ} (hx : lo ≤ x)
    (hxd : x + 2 ≤ d ∨ d + 2 ≤ x) (M : Mem) : rdF (runPrims ps M) x = rdF M x :=
  rdF_eq (rd_runPrims_of_not_writes (fun p hp => by have := hdst p hp; omega) M)
    (rd_runPrims_of_not_writes (fun p hp => by have := hdst p hp; omega) M)

theorem mulFC_dst' (d a b : ℕ) : ∀ p ∈ mulFC d a b, p.dst = d ∨ p.dst = d + 1 ∨ p.dst < 15 :=
  fun p hp => by have := mulFC_dst d a b p hp; omega
theorem sqFC_dst' (d a : ℕ) : ∀ p ∈ sqFC d a, p.dst = d ∨ p.dst = d + 1 ∨ p.dst < 15 :=
  fun p hp => by have := sqFC_dst d a p hp; omega
theorem addFC_dst' (d a b : ℕ) : ∀ p ∈ addFC d a b, p.dst = d ∨ p.dst = d + 1 ∨ p.dst < 0 :=
  fun p hp => by have := addFC_dst d a b p hp; omega
theorem invFC_dst' (d a : ℕ) : ∀ p ∈ invFC d a, p.dst = d ∨ p.dst = d + 1 ∨ p.dst < 19 :=
  fun p hp => by have := invFC_dst d a p hp; omega

/-- `M[d, d+1] := α · M[z, z+1]`, `α = β y` (22 statements, scratch `5, 6, 9, 10, 13, 14`):
`β(β z₁) + β(z₀ + z₁) y`. -/
def alphaC (d z : ℕ) : List Prim :=
  [.op .xor 9 z (z + 1)] ++ betaC 10 (z + 1) ++ betaC d 10 ++ betaC (d + 1) 9

theorem alphaC_dst (d z : ℕ) : ∀ p ∈ alphaC d z, p.dst = d ∨ p.dst = d + 1 ∨ p.dst < 15 := by
  intro p hp
  simp only [alphaC, List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with ((hp | hp) | hp) | hp
  · subst hp; simp [Prim.dst]
  · have := betaC_dst _ _ p hp; omega
  · have := betaC_dst _ _ p hp; omega
  · have := betaC_dst _ _ p hp; omega

theorem alphaC_inv (d z : ℕ) (hd : 15 ≤ d) {M : Mem} (hM : Inv M) : Inv (runPrims (alphaC d z) M) :=
  inv_runPrims (fun p hp => by
    simp only [alphaC, List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with ((hp | hp) | hp) | hp
    · subst hp; simp [Prim.dst]
    · have := betaC_dst _ _ p hp; omega
    · have := betaC_dst _ _ p hp; omega
    · have := betaC_dst _ _ p hp; omega) hM

/-- **`alphaC` computes `α ·`** (`F.mulAlpha`). -/
theorem alphaC_spec {M : Mem} (hM : Inv M) {d z : ℕ} (hd : 15 ≤ d) (hd' : d + 2 ≤ regs)
    (hz : 15 ≤ z) : rdF (runPrims (alphaC d z) M) d = F.mulAlpha (rdF M z) := by
  have hr : regs = 256 := rfl
  have hs : 256 ≤ M.size := hM.1
  simp only [alphaC, runPrims_append]
  set M1 := runPrims [.op .xor 9 z (z + 1)] M with hM1
  have i1 : Inv M1 := xorC_inv 9 z (z + 1) (by omega) hM
  have v1 : rd M1 9 = rd M z ^^^ rd M (z + 1) := rd_xor_run (by omega)
  have f1 : rd M1 (z + 1) = rd M (z + 1) := xorC_frame _ _ _ (by omega) M
  set M2 := runPrims (betaC 10 (z + 1)) M1 with hM2
  have i2 : Inv M2 := betaC_inv 10 (z + 1) (by omega) i1
  have v2 : rd M2 10 = betaW (rd M1 (z + 1)) := betaC_run i1 (by omega) (by omega) (by omega)
  have f2 : rd M2 9 = rd M1 9 := betaC_frame 10 (z + 1) (i := 9) (by omega) (by omega) M1
  set M3 := runPrims (betaC d 10) M2 with hM3
  have i3 : Inv M3 := betaC_inv d 10 (by omega) i2
  have v3 : rd M3 d = betaW (rd M2 10) := betaC_run i2 (by omega) (by omega) (by omega)
  have f3 : rd M3 9 = rd M2 9 := betaC_frame d 10 (i := 9) (by omega) (by omega) M2
  have v4 : rd (runPrims (betaC (d + 1) 9) M3) (d + 1) = betaW (rd M3 9) :=
    betaC_run i3 (by omega) (by omega) (by omega)
  have f4 : rd (runPrims (betaC (d + 1) 9) M3) d = rd M3 d :=
    betaC_frame (d + 1) 9 (i := d) (by omega) (by omega) M3
  simp only [rdF, rdB, v4, f4, v3, f3, v2, f2, v1, f1, betaW_spec, wB_xor]
  simp only [F.mulAlpha, mulBeta_eq]

/-- `M[d … d+3] := M[a … a+3] + M[b … b+3]` (4 statements). -/
def addKC (d a b : ℕ) : List Prim := addFC d a b ++ addFC (d + 2) (a + 2) (b + 2)

/-- **`addKC` computes `K`'s sum** (the result may be an operand, not overlap one). -/
theorem addKC_spec {M : Mem} {d a b : ℕ} (hd : d + 3 < M.size) (ha : d = a ∨ d + 4 ≤ a ∨ a + 4 ≤ d)
    (hb : d = b ∨ d + 4 ≤ b ∨ b + 4 ≤ d) :
    rdK (runPrims (addKC d a b) M) d = rdK M a + rdK M b := by
  simp only [addKC, runPrims_append, rdK]
  rw [addFC_spec (by simpa using hd) (by omega) (by omega),
    rdF_frame (addFC_dst' (d + 2) (a + 2) (b + 2)) (Nat.zero_le _) (by omega),
    addFC_spec (by omega) (by omega) (by omega),
    rdF_frame (addFC_dst' d a b) (Nat.zero_le _) (by omega),
    rdF_frame (addFC_dst' d a b) (Nat.zero_le _) (by omega)]
  rfl

/-- **The `K` product** `M[d … d+3] := M[a … a+3] · M[b … b+3]` (117 statements, scratch
`5 … 30`): three `F` products (Karatsuba), `α ·`, four `F` sums. -/
def mulKC (d a b : ℕ) : List Prim :=
  addFC 19 a (a + 2) ++ addFC 21 b (b + 2) ++ mulFC 23 a b ++ mulFC 25 (a + 2) (b + 2) ++
  mulFC 27 19 21 ++ alphaC 29 25 ++ addFC d 23 29 ++ addFC (d + 2) 27 23

/-- **`mulKC` computes `K`'s product.** -/
theorem mulKC_spec {M : Mem} (hM : Inv M) {d a b : ℕ} (hd : 31 ≤ d) (hd' : d + 4 ≤ regs)
    (ha : 31 ≤ a) (hb : 31 ≤ b) : rdK (runPrims (mulKC d a b) M) d = rdK M a * rdK M b := by
  have hr : regs = 256 := rfl
  have hs : 256 ≤ M.size := hM.1
  simp only [mulKC, runPrims_append]
  set M1 := runPrims (addFC 19 a (a + 2)) M
  have i1 : Inv M1 := addFC_inv 19 a (a + 2) (by omega) hM
  have v1 : rdF M1 19 = rdF M a + rdF M (a + 2) := addFC_spec (by omega) (by omega) (by omega)
  have g1 : ∀ x, 31 ≤ x → rdF M1 x = rdF M x := fun x hx =>
    rdF_frame (addFC_dst' 19 a (a + 2)) (Nat.zero_le _) (by omega) M
  set M2 := runPrims (addFC 21 b (b + 2)) M1
  have i2 : Inv M2 := addFC_inv 21 b (b + 2) (by omega) i1
  have v2 : rdF M2 21 = rdF M1 b + rdF M1 (b + 2) :=
    addFC_spec (by simp only [M1, size_runPrims]; omega) (by omega) (by omega)
  have g2 : ∀ x, (x = 19 ∨ 31 ≤ x) → rdF M2 x = rdF M1 x := fun x hx =>
    rdF_frame (addFC_dst' 21 b (b + 2)) (Nat.zero_le _) (by omega) M1
  set M3 := runPrims (mulFC 23 a b) M2
  have i3 : Inv M3 := mulFC_inv 23 a b (by omega) i2
  have v3 : rdF M3 23 = rdF M2 a * rdF M2 b := mulFC_spec i2 (by omega) (by omega) (by omega) (by
      omega)
  have g3 : ∀ x, (x = 19 ∨ x = 21 ∨ 31 ≤ x) → rdF M3 x = rdF M2 x := fun x hx =>
    rdF_frame (mulFC_dst' 23 a b) (by omega) (by omega) M2
  set M4 := runPrims (mulFC 25 (a + 2) (b + 2)) M3
  have i4 : Inv M4 := mulFC_inv 25 (a + 2) (b + 2) (by omega) i3
  have v4 : rdF M4 25 = rdF M3 (a + 2) * rdF M3 (b + 2) :=
    mulFC_spec i3 (by omega) (by omega) (by omega) (by omega)
  have g4 : ∀ x, (x = 19 ∨ x = 21 ∨ x = 23 ∨ 31 ≤ x) → rdF M4 x = rdF M3 x := fun x hx =>
    rdF_frame (mulFC_dst' 25 (a + 2) (b + 2)) (by omega) (by omega) M3
  set M5 := runPrims (mulFC 27 19 21) M4
  have i5 : Inv M5 := mulFC_inv 27 19 21 (by omega) i4
  have v5 : rdF M5 27 = rdF M4 19 * rdF M4 21 :=
    mulFC_spec i4 (by omega) (by omega) (by omega) (by omega)
  have g5 : ∀ x, (x = 23 ∨ x = 25) → rdF M5 x = rdF M4 x := fun x hx =>
    rdF_frame (mulFC_dst' 27 19 21) (by omega) (by omega) M4
  set M6 := runPrims (alphaC 29 25) M5
  have i6 : Inv M6 := alphaC_inv 29 25 (by omega) i5
  have v6 : rdF M6 29 = F.mulAlpha (rdF M5 25) := alphaC_spec i5 (by omega) (by omega) (by omega)
  have g6 : ∀ x, (x = 23 ∨ x = 27) → rdF M6 x = rdF M5 x := fun x hx =>
    rdF_frame (alphaC_dst 29 25) (by omega) (by omega) M5
  set M7 := runPrims (addFC d 23 29) M6
  have v7 : rdF M7 d = rdF M6 23 + rdF M6 29 :=
    addFC_spec (by simp only [M6, M5, M4, M3, M2, M1, size_runPrims]; omega) (by omega) (by omega)
  have g7 : ∀ x, (x = 23 ∨ x = 27) → rdF M7 x = rdF M6 x := fun x hx =>
    rdF_frame (addFC_dst' d 23 29) (Nat.zero_le _) (by omega) M6
  have v8 : rdF (runPrims (addFC (d + 2) 27 23) M7) (d + 2) = rdF M7 27 + rdF M7 23 :=
    addFC_spec (by simp only [M7, M6, M5, M4, M3, M2, M1, size_runPrims]; omega) (by omega)
      (by omega)
  have g8 : rdF (runPrims (addFC (d + 2) 27 23) M7) d = rdF M7 d :=
    rdF_frame (addFC_dst' (d + 2) 27 23) (Nat.zero_le _) (by omega) M7
  simp only [rdK]
  rw [v8, g8, v7, g7 23 (by omega), g7 27 (by omega), v6, g6 23 (by omega), g6 27 (by omega), v5,
    g5 23 (by omega), g5 25 (by omega), v4, g4 19 (by omega), g4 21 (by omega), g4 23 (by omega),
    v3, g3 19 (by omega), g3 21 (by omega), g3 (a + 2) (by omega), g3 (b + 2) (by omega), v2,
    g2 19 (by omega), g2 a (by omega), g2 b (by omega), g2 (a + 2) (by omega), g2 (b + 2) (by
        omega),
    v1, g1 a (by omega), g1 b (by omega), g1 (a + 2) (by omega), g1 (b + 2) (by omega)]
  rfl

/-- `M[d, d+1] := M[a, a+1]` (2 statements). -/
def copyFC (d a : ℕ) : List Prim := [.op .or d a a, .op .or (d + 1) (a + 1) (a + 1)]

theorem copyFC_dst' (d a : ℕ) : ∀ p ∈ copyFC d a, p.dst = d ∨ p.dst = d + 1 ∨ p.dst < 0 := by
  simp [copyFC, Prim.dst]

theorem copyFC_spec {M : Mem} {d a : ℕ} (hd : d + 1 < M.size) (ha : d ≠ a + 1) :
    rdF (runPrims (copyFC d a) M) d = rdF M a := by
  simp (disch := ((try simp only [size_set]); omega)) only [copyFC, runPrims_cons, runPrims_nil,
    Prim.run, rdF, rdB, rd_set_self, rd_set_ne, eval_or, BitVec.or_self]

/-- **The `K` square** `M[d … d+3] := M[a … a+3]^2` (72 statements, scratch `5 … 24`):
`(f₀^2 + α f₁^2) + f₁^2 u`. -/
def sqKC (d a : ℕ) : List Prim :=
  sqFC 19 (a + 2) ++ sqFC 21 a ++ alphaC 23 19 ++ addFC d 21 23 ++ copyFC (d + 2) 19

/-- **`sqKC` computes `K`'s square.** -/
theorem sqKC_spec {M : Mem} (hM : Inv M) {d a : ℕ} (hd : 31 ≤ d) (hd' : d + 4 ≤ regs)
    (ha : 31 ≤ a) : rdK (runPrims (sqKC d a) M) d = K.sq (rdK M a) := by
  have hr : regs = 256 := rfl
  have hs : 256 ≤ M.size := hM.1
  simp only [sqKC, runPrims_append]
  set M1 := runPrims (sqFC 19 (a + 2)) M
  have i1 : Inv M1 := sqFC_inv 19 (a + 2) (by omega) hM
  have v1 : rdF M1 19 = F.sq (rdF M (a + 2)) := sqFC_spec hM (by omega) (by omega) (by omega)
  have g1 : rdF M1 a = rdF M a := rdF_frame (sqFC_dst' 19 (a + 2)) (by omega) (by omega) M
  set M2 := runPrims (sqFC 21 a) M1
  have i2 : Inv M2 := sqFC_inv 21 a (by omega) i1
  have v2 : rdF M2 21 = F.sq (rdF M1 a) := sqFC_spec i1 (by omega) (by omega) (by omega)
  have g2 : rdF M2 19 = rdF M1 19 := rdF_frame (sqFC_dst' 21 a) (by omega) (by omega) M1
  set M3 := runPrims (alphaC 23 19) M2
  have v3 : rdF M3 23 = F.mulAlpha (rdF M2 19) := alphaC_spec i2 (by omega) (by omega) (by omega)
  have g3 : ∀ x, (x = 19 ∨ x = 21) → rdF M3 x = rdF M2 x := fun x hx =>
    rdF_frame (alphaC_dst 23 19) (by omega) (by omega) M2
  set M4 := runPrims (addFC d 21 23) M3
  have v4 : rdF M4 d = rdF M3 21 + rdF M3 23 :=
    addFC_spec (by simp only [M3, M2, M1, size_runPrims]; omega) (by omega) (by omega)
  have g4 : rdF M4 19 = rdF M3 19 := rdF_frame (addFC_dst' d 21 23) (Nat.zero_le _) (by omega) M3
  have v5 : rdF (runPrims (copyFC (d + 2) 19) M4) (d + 2) = rdF M4 19 :=
    copyFC_spec (by simp only [M4, M3, M2, M1, size_runPrims]; omega) (by omega)
  have g5 : rdF (runPrims (copyFC (d + 2) 19) M4) d = rdF M4 d :=
    rdF_frame (copyFC_dst' (d + 2) 19) (Nat.zero_le _) (by omega) M4
  simp only [rdK]
  rw [v5, g5, v4, g4, v3, g3 19 (by omega), g3 21 (by omega), v2, g2, v1, g1]
  rfl

theorem alphaC_dst5 (d z : ℕ) (hd : 15 ≤ d) : ∀ p ∈ alphaC d z, 5 ≤ p.dst := by
  intro p hp
  simp only [alphaC, List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with ((hp | hp) | hp) | hp
  · subst hp; simp [Prim.dst]
  · have := betaC_dst _ _ p hp; omega
  · have := betaC_dst _ _ p hp; omega
  · have := betaC_dst _ _ p hp; omega

/-- **The `K` inverse** `M[d … d+3] := M[a … a+3]⁻¹` (`0⁻¹ = 0`; 690 statements, scratch
`5 … 38`): the norm `f₀(f₀ + f₁) + α f₁^2` to `F`, one `F` inverse, `n⁻¹ ((f₀ + f₁) + f₁ u)`. -/
def invKC (d a : ℕ) : List Prim :=
  addFC 31 a (a + 2) ++ mulFC 33 a 31 ++ sqFC 35 (a + 2) ++ alphaC 37 35 ++ addFC 33 33 37 ++
  invFC 33 33 ++ mulFC (d + 2) 33 (a + 2) ++ mulFC d 33 31

/-- **`invKC` computes `K`'s inverse.** -/
theorem invKC_spec {M : Mem} (hM : Inv M) {d a : ℕ} (hd : 39 ≤ d) (hd' : d + 4 ≤ regs)
    (ha : 39 ≤ a) : rdK (runPrims (invKC d a) M) d = (rdK M a)⁻¹ := by
  have hr : regs = 256 := rfl
  have hs : 256 ≤ M.size := hM.1
  simp only [invKC, runPrims_append]
  set M1 := runPrims (addFC 31 a (a + 2)) M
  have i1 : Inv M1 := addFC_inv 31 a (a + 2) (by omega) hM
  have v1 : rdF M1 31 = rdF M a + rdF M (a + 2) := addFC_spec (by omega) (by omega) (by omega)
  have g1 : ∀ x, 39 ≤ x → rdF M1 x = rdF M x := fun x hx =>
    rdF_frame (addFC_dst' 31 a (a + 2)) (Nat.zero_le _) (by omega) M
  set M2 := runPrims (mulFC 33 a 31) M1
  have i2 : Inv M2 := mulFC_inv 33 a 31 (by omega) i1
  have v2 : rdF M2 33 = rdF M1 a * rdF M1 31 := mulFC_spec i1 (by omega) (by omega) (by omega)
    (by omega)
  have g2 : ∀ x, (x = 31 ∨ 39 ≤ x) → rdF M2 x = rdF M1 x := fun x hx =>
    rdF_frame (mulFC_dst' 33 a 31) (by omega) (by omega) M1
  set M3 := runPrims (sqFC 35 (a + 2)) M2
  have i3 : Inv M3 := sqFC_inv 35 (a + 2) (by omega) i2
  have v3 : rdF M3 35 = F.sq (rdF M2 (a + 2)) := sqFC_spec i2 (by omega) (by omega) (by omega)
  have g3 : ∀ x, (x = 31 ∨ x = 33 ∨ 39 ≤ x) → rdF M3 x = rdF M2 x := fun x hx =>
    rdF_frame (sqFC_dst' 35 (a + 2)) (by omega) (by omega) M2
  set M4 := runPrims (alphaC 37 35) M3
  have i4 : Inv M4 :=
    inv_runPrims (fun p hp => by have := alphaC_dst5 37 35 (by omega) p hp; omega) i3
  have v4 : rdF M4 37 = F.mulAlpha (rdF M3 35) := alphaC_spec i3 (by omega) (by omega) (by omega)
  have g4 : ∀ x, (x = 31 ∨ x = 33 ∨ 39 ≤ x) → rdF M4 x = rdF M3 x := fun x hx =>
    rdF_frame (alphaC_dst 37 35) (by omega) (by omega) M3
  set M5 := runPrims (addFC 33 33 37) M4
  have i5 : Inv M5 := addFC_inv 33 33 37 (by omega) i4
  have v5 : rdF M5 33 = rdF M4 33 + rdF M4 37 :=
    addFC_spec (by simp only [M4, M3, M2, M1, size_runPrims]; omega) (by omega) (by omega)
  have g5 : ∀ x, (x = 31 ∨ 39 ≤ x) → rdF M5 x = rdF M4 x := fun x hx =>
    rdF_frame (addFC_dst' 33 33 37) (Nat.zero_le _) (by omega) M4
  set M6 := runPrims (invFC 33 33) M5
  have i6 : Inv M6 := invFC_inv 33 33 (by omega) i5
  have v6 : rdF M6 33 = (rdF M5 33)⁻¹ := invFC_spec i5 (by omega) (by omega) (by omega)
  have g6 : ∀ x, (x = 31 ∨ 39 ≤ x) → rdF M6 x = rdF M5 x := fun x hx =>
    rdF_frame (invFC_dst' 33 33) (by omega) (by omega) M5
  set M7 := runPrims (mulFC (d + 2) 33 (a + 2)) M6
  have i7 : Inv M7 := mulFC_inv (d + 2) 33 (a + 2) (by omega) i6
  have v7 : rdF M7 (d + 2) = rdF M6 33 * rdF M6 (a + 2) :=
    mulFC_spec i6 (by omega) (by omega) (by omega) (by omega)
  have g7 : ∀ x, (x = 31 ∨ x = 33) → rdF M7 x = rdF M6 x := fun x hx =>
    rdF_frame (mulFC_dst' (d + 2) 33 (a + 2)) (by omega) (by omega) M6
  have v8 : rdF (runPrims (mulFC d 33 31) M7) d = rdF M7 33 * rdF M7 31 :=
    mulFC_spec i7 (by omega) (by omega) (by omega) (by omega)
  have g8 : rdF (runPrims (mulFC d 33 31) M7) (d + 2) = rdF M7 (d + 2) :=
    rdF_frame (mulFC_dst' d 33 31) (by omega) (by omega) M7
  simp only [rdK]
  rw [v8, g8, v7, g7 31 (by omega), g7 33 (by omega), v6, g6 31 (by omega), g6 (a + 2) (by omega),
    v5, g5 31 (by omega), g5 (a + 2) (by omega), v4, g4 31 (by omega), g4 33 (by omega),
    g4 (a + 2) (by omega), v3, g3 31 (by omega), g3 33 (by omega), g3 (a + 2) (by omega), v2,
    g2 31 (by omega),
    g2 (a + 2) (by omega), v1, g1 a (by omega), g1 (a + 2) (by omega)]
  show _ = K.inv _
  simp only [K.inv, K.smulF, K.norm]

/-! ## The routines as `XIR` -/

/-- `M[d] := M[a] · M[b]` in `B64`. -/
def mulB (d a b : ℕ) : XIR := .blk (mulBC d a b)
/-- `M[d] := M[a]^2` in `B64`. -/
def sqB (d a : ℕ) : XIR := .blk (mulBC d a a)
/-- `M[d] := M[a]⁻¹` in `B64`. -/
def invB (d a : ℕ) : XIR := .blk (invBC d a)
/-- `M[d, d+1] := M[a, a+1] · M[b, b+1]` in `F`. -/
def mulF (d a b : ℕ) : XIR := .blk (mulFC d a b)
/-- `M[d, d+1] := M[a, a+1]^2` in `F`. -/
def sqF (d a : ℕ) : XIR := .blk (sqFC d a)
/-- `M[d, d+1] := M[a, a+1] + M[b, b+1]` in `F`. -/
def addF (d a b : ℕ) : XIR := .blk (addFC d a b)
/-- `M[d, d+1] := M[a, a+1]⁻¹` in `F`. -/
def invF (d a : ℕ) : XIR := .blk (invFC d a)
/-- `M[d … d+3] := M[a … a+3] · M[b … b+3]` in `K`. -/
def mulK (d a b : ℕ) : XIR := .blk (mulKC d a b)
/-- `M[d … d+3] := M[a … a+3]^2` in `K`. -/
def sqK (d a : ℕ) : XIR := .blk (sqKC d a)
/-- `M[d … d+3] := M[a … a+3] + M[b … b+3]` in `K`. -/
def addK (d a b : ℕ) : XIR := .blk (addKC d a b)
/-- `M[d … d+3] := M[a … a+3]⁻¹` in `K`. -/
def invK (d a : ℕ) : XIR := .blk (invKC d a)

variable {I : Array Word} {s : St}

theorem sem_blk (ps : List Prim) : (semXIR I (.blk ps) s).M = runPrims ps s.M := rfl
theorem steps_blk (ps : List Prim) : steps I (.blk ps) s = blkSteps ps.length := rfl
theorem cost_blk (ps : List Prim) (t : ℕ) : cost (.blk ps) t = blkSteps ps.length := rfl

/-- **`B64` product.** -/
theorem mulB_sem (hM : Inv s.M) {d a b : ℕ} (hd : 9 ≤ d) (hd' : d < regs) (ha : 9 ≤ a)
    (hb : 9 ≤ b) : rdB (semXIR I (mulB d a b) s).M d = rdB s.M a * rdB s.M b := by
  rw [mulB, sem_blk, rdB, mulBC_run hM hd hd' ha hb, mulBW_spec]; rfl

/-- **`B64` square.** -/
theorem sqB_sem (hM : Inv s.M) {d a : ℕ} (hd : 9 ≤ d) (hd' : d < regs) (ha : 9 ≤ a) :
    rdB (semXIR I (sqB d a) s).M d = B64.sq (rdB s.M a) := by
  rw [sqB, sem_blk, rdB, mulBC_run hM hd hd' ha ha, mulBW_spec, B64.sq_eq_mul]; rfl

/-- **`B64` inverse.** -/
theorem invB_sem (hM : Inv s.M) {d a : ℕ} (hd : 12 ≤ d) (hd' : d < regs) :
    rdB (semXIR I (invB d a) s).M d = (rdB s.M a)⁻¹ := by
  rw [invB, sem_blk]; exact invBC_run hM hd hd'

/-- **`F` product.** -/
theorem mulF_sem (hM : Inv s.M) {d a b : ℕ} (hd : 15 ≤ d) (hd' : d + 2 ≤ regs) (ha : 15 ≤ a)
    (hb : 15 ≤ b) : rdF (semXIR I (mulF d a b) s).M d = rdF s.M a * rdF s.M b := by
  rw [mulF, sem_blk]; exact mulFC_spec hM hd hd' ha hb

/-- **`F` square.** -/
theorem sqF_sem (hM : Inv s.M) {d a : ℕ} (hd : 15 ≤ d) (hd' : d + 2 ≤ regs) (ha : 15 ≤ a) :
    rdF (semXIR I (sqF d a) s).M d = F.sq (rdF s.M a) := by
  rw [sqF, sem_blk]; exact sqFC_spec hM hd hd' ha

/-- **`F` sum.** -/
theorem addF_sem (hM : Inv s.M) {d a b : ℕ} (hd' : d + 2 ≤ regs) (ha : d ≠ a + 1)
    (hb : d ≠ b + 1) : rdF (semXIR I (addF d a b) s).M d = rdF s.M a + rdF s.M b := by
  rw [addF, sem_blk]; exact addFC_spec (by have := hM.1; omega) ha hb

/-- **`F` inverse.** -/
theorem invF_sem (hM : Inv s.M) {d a : ℕ} (hd : 19 ≤ d) (hd' : d + 2 ≤ regs) (ha : 19 ≤ a) :
    rdF (semXIR I (invF d a) s).M d = (rdF s.M a)⁻¹ := by
  rw [invF, sem_blk]; exact invFC_spec hM hd hd' ha

/-- **`K` product.** -/
theorem mulK_sem (hM : Inv s.M) {d a b : ℕ} (hd : 31 ≤ d) (hd' : d + 4 ≤ regs) (ha : 31 ≤ a)
    (hb : 31 ≤ b) : rdK (semXIR I (mulK d a b) s).M d = rdK s.M a * rdK s.M b := by
  rw [mulK, sem_blk]; exact mulKC_spec hM hd hd' ha hb

/-- **`K` square.** -/
theorem sqK_sem (hM : Inv s.M) {d a : ℕ} (hd : 31 ≤ d) (hd' : d + 4 ≤ regs) (ha : 31 ≤ a) :
    rdK (semXIR I (sqK d a) s).M d = K.sq (rdK s.M a) := by
  rw [sqK, sem_blk]; exact sqKC_spec hM hd hd' ha

/-- **`K` sum.** -/
theorem addK_sem (hM : Inv s.M) {d a b : ℕ} (hd' : d + 4 ≤ regs)
    (ha : d = a ∨ d + 4 ≤ a ∨ a + 4 ≤ d) (hb : d = b ∨ d + 4 ≤ b ∨ b + 4 ≤ d) :
    rdK (semXIR I (addK d a b) s).M d = rdK s.M a + rdK s.M b := by
  rw [addK, sem_blk]; exact addKC_spec (by have := hM.1; omega) ha hb

/-- **`K` inverse.** -/
theorem invK_sem (hM : Inv s.M) {d a : ℕ} (hd : 39 ≤ d) (hd' : d + 4 ≤ regs) (ha : 39 ≤ a) :
    rdK (semXIR I (invK d a) s).M d = (rdK s.M a)⁻¹ := by
  rw [invK, sem_blk]; exact invKC_spec hM hd hd' ha

/-! ## Step counts (exact, on the compiled code) and statement counts -/

theorem len_mulBC (d a b : ℕ) : (mulBC d a b).length = 7 := rfl
theorem len_betaC (d r : ℕ) : (betaC d r).length = 7 := rfl
theorem len_sqnC (r k : ℕ) : (sqnC r k).length = 7 * k := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [show sqnC r (k + 1) = mulBC r r r ++ sqnC r k by simp [sqnC, List.replicate_succ],
      List.length_append, ih, len_mulBC]; ring
theorem len_stepC (r k y : ℕ) : (stepC r k y).length = 7 * k + 7 := by
  rw [stepC, List.length_append, len_sqnC, len_mulBC]
theorem len_invBC (d a : ℕ) : (invBC d a).length = 517 := by
  simp only [invBC, List.length_append, len_stepC, len_mulBC, List.length_cons, List.length_nil]
theorem len_mulFC (d a b : ℕ) : (mulFC d a b).length = 29 := rfl
theorem len_sqFC (d a : ℕ) : (sqFC d a).length = 23 := rfl
theorem len_addFC (d a b : ℕ) : (addFC d a b).length = 2 := rfl
theorem len_invFC (d a : ℕ) : (invFC d a).length = 554 := by
  simp only [invFC, List.length_append, len_invBC, len_mulBC, len_betaC, List.length_cons,
    List.length_nil]
theorem len_mulKC (d a b : ℕ) : (mulKC d a b).length = 117 := rfl
theorem len_sqKC (d a : ℕ) : (sqKC d a).length = 72 := rfl
theorem len_addKC (d a b : ℕ) : (addKC d a b).length = 4 := rfl
theorem len_invKC (d a : ℕ) : (invKC d a).length = 690 := by
  simp only [invKC, List.length_append, len_invFC, len_mulFC, len_sqFC, len_addFC,
    show (alphaC 37 35).length = 22 from rfl]

@[simp] theorem steps_mulB (d a b : ℕ) : steps I (mulB d a b) s = 13 := by
  rw [mulB, steps_blk, len_mulBC]; rfl
@[simp] theorem steps_sqB (d a : ℕ) : steps I (sqB d a) s = 13 := by
  rw [sqB, steps_blk, len_mulBC]; rfl
@[simp] theorem steps_invB (d a : ℕ) : steps I (invB d a) s = 1033 := by
  rw [invB, steps_blk, len_invBC]; rfl
/-- **One `F` product is 57 machine steps** (29 statements and 28 `seq` nodes). -/
@[simp] theorem steps_mulF (d a b : ℕ) : steps I (mulF d a b) s = 57 := by
  rw [mulF, steps_blk, len_mulFC]; rfl
@[simp] theorem steps_sqF (d a : ℕ) : steps I (sqF d a) s = 45 := by
  rw [sqF, steps_blk, len_sqFC]; rfl
@[simp] theorem steps_addF (d a b : ℕ) : steps I (addF d a b) s = 3 := by
  rw [addF, steps_blk, len_addFC]; rfl
@[simp] theorem steps_invF (d a : ℕ) : steps I (invF d a) s = 1107 := by
  rw [invF, steps_blk, len_invFC]; rfl
@[simp] theorem steps_mulK (d a b : ℕ) : steps I (mulK d a b) s = 233 := by
  rw [mulK, steps_blk, len_mulKC]; rfl
@[simp] theorem steps_sqK (d a : ℕ) : steps I (sqK d a) s = 143 := by
  rw [sqK, steps_blk, len_sqKC]; rfl
@[simp] theorem steps_addK (d a b : ℕ) : steps I (addK d a b) s = 7 := by
  rw [addK, steps_blk, len_addKC]; rfl
@[simp] theorem steps_invK (d a : ℕ) : steps I (invK d a) s = 1379 := by
  rw [invK, steps_blk, len_invKC]; rfl

@[simp] theorem cost_mulB (d a b t : ℕ) : cost (mulB d a b) t = 13 := by
  rw [mulB, cost_blk, len_mulBC]; rfl
@[simp] theorem cost_sqB (d a t : ℕ) : cost (sqB d a) t = 13 := by
  rw [sqB, cost_blk, len_mulBC]; rfl
@[simp] theorem cost_invB (d a t : ℕ) : cost (invB d a) t = 1033 := by
  rw [invB, cost_blk, len_invBC]; rfl
@[simp] theorem cost_mulF (d a b t : ℕ) : cost (mulF d a b) t = 57 := by
  rw [mulF, cost_blk, len_mulFC]; rfl
@[simp] theorem cost_sqF (d a t : ℕ) : cost (sqF d a) t = 45 := by
  rw [sqF, cost_blk, len_sqFC]; rfl
@[simp] theorem cost_addF (d a b t : ℕ) : cost (addF d a b) t = 3 := by
  rw [addF, cost_blk, len_addFC]; rfl
@[simp] theorem cost_invF (d a t : ℕ) : cost (invF d a) t = 1107 := by
  rw [invF, cost_blk, len_invFC]; rfl
@[simp] theorem cost_mulK (d a b t : ℕ) : cost (mulK d a b) t = 233 := by
  rw [mulK, cost_blk, len_mulKC]; rfl
@[simp] theorem cost_sqK (d a t : ℕ) : cost (sqK d a) t = 143 := by
  rw [sqK, cost_blk, len_sqKC]; rfl
@[simp] theorem cost_addK (d a b t : ℕ) : cost (addK d a b) t = 7 := by
  rw [addK, cost_blk, len_addKC]; rfl
@[simp] theorem cost_invK (d a t : ℕ) : cost (invK d a) t = 1379 := by
  rw [invK, cost_blk, len_invKC]; rfl

/-- The statement count of a block routine is its step count. -/
theorem sizeIR_blk (ps : List Prim) : sizeIR (.blk ps) = cost (.blk ps) 0 := rfl

/-! ## Well-formedness and what the routines write -/

theorem writes_blk {ps : List Prim} {i : ℕ} : Writes (.blk ps) i ↔ ∃ p ∈ ps, p.dst = i := Iff.rfl

theorem wf_blk {ps : List Prim} (h : ∀ p ∈ ps, 4 ≤ p.dst) : WF (.blk ps) := h

theorem wf_mulB (d a b : ℕ) (hd : 4 ≤ d) : WF (mulB d a b) :=
  fun p hp => by have := mulBC_dst d a b p hp; omega
theorem wf_sqB (d a : ℕ) (hd : 4 ≤ d) : WF (sqB d a) :=
  fun p hp => by have := mulBC_dst d a a p hp; omega
theorem wf_invB (d a : ℕ) (hd : 4 ≤ d) : WF (invB d a) :=
  fun p hp => by have := invBC_dst d a p hp; omega
theorem wf_mulF (d a b : ℕ) (hd : 4 ≤ d) : WF (mulF d a b) :=
  fun p hp => by have := mulFC_dst d a b p hp; omega
theorem wf_sqF (d a : ℕ) (hd : 4 ≤ d) : WF (sqF d a) :=
  fun p hp => by have := sqFC_dst d a p hp; omega
theorem wf_addF (d a b : ℕ) (hd : 4 ≤ d) : WF (addF d a b) :=
  fun p hp => by have := addFC_dst d a b p hp; omega
theorem wf_invF (d a : ℕ) (hd : 4 ≤ d) : WF (invF d a) :=
  fun p hp => by have := invFC_dst d a p hp; omega

/-- The destinations of the `K` routines: the result and scratch below `39`. -/
theorem mulKC_dst (d a b : ℕ) : ∀ p ∈ mulKC d a b, p.dst = d ∨ p.dst = d + 1 ∨ p.dst = d + 2 ∨
    p.dst = d + 3 ∨ (5 ≤ p.dst ∧ p.dst < 31) := by
  intro p hp
  simp only [mulKC, List.mem_append] at hp
  rcases hp with ((((((hp | hp) | hp) | hp) | hp) | hp) | hp) | hp
  · have := addFC_dst _ _ _ p hp; omega
  · have := addFC_dst _ _ _ p hp; omega
  · have := mulFC_dst _ _ _ p hp; omega
  · have := mulFC_dst _ _ _ p hp; omega
  · have := mulFC_dst _ _ _ p hp; omega
  · have := alphaC_dst _ _ p hp; have := alphaC_dst5 29 25 (by omega) p
      hp; omega
  · have := addFC_dst _ _ _ p hp; omega
  · have := addFC_dst _ _ _ p hp; omega

theorem sqKC_dst (d a : ℕ) : ∀ p ∈ sqKC d a, p.dst = d ∨ p.dst = d + 1 ∨ p.dst = d + 2 ∨
    p.dst = d + 3 ∨ (5 ≤ p.dst ∧ p.dst < 31) := by
  intro p hp
  simp only [sqKC, List.mem_append] at hp
  rcases hp with (((hp | hp) | hp) | hp) | hp
  · have := sqFC_dst _ _ p hp; omega
  · have := sqFC_dst _ _ p hp; omega
  · have := alphaC_dst _ _ p hp; have := alphaC_dst5 23 19 (by omega) p hp; omega
  · have := addFC_dst _ _ _ p hp; omega
  · have := copyFC_dst' _ _ p hp; omega

theorem invKC_dst (d a : ℕ) : ∀ p ∈ invKC d a, p.dst = d ∨ p.dst = d + 1 ∨ p.dst = d + 2 ∨
    p.dst = d + 3 ∨ (5 ≤ p.dst ∧ p.dst < 39) := by
  intro p hp
  simp only [invKC, List.mem_append] at hp
  rcases hp with ((((((hp | hp) | hp) | hp) | hp) | hp) | hp) | hp
  · have := addFC_dst _ _ _ p hp; omega
  · have := mulFC_dst _ _ _ p hp; omega
  · have := sqFC_dst _ _ p hp; omega
  · have := alphaC_dst _ _ p hp; have := alphaC_dst5 37 35 (by omega) p hp; omega
  · have := addFC_dst _ _ _ p hp; omega
  · have := invFC_dst _ _ p hp; omega
  · have := mulFC_dst _ _ _ p hp; omega
  · have := mulFC_dst _ _ _ p hp; omega

theorem wf_mulK (d a b : ℕ) (hd : 4 ≤ d) : WF (mulK d a b) :=
  fun p hp => by have := mulKC_dst d a b p hp; omega
theorem wf_sqK (d a : ℕ) (hd : 4 ≤ d) : WF (sqK d a) :=
  fun p hp => by have := sqKC_dst d a p hp; omega
theorem wf_addK (d a b : ℕ) (hd : 4 ≤ d) : WF (addK d a b) := fun p hp => by
  simp only [addKC, List.mem_append] at hp
  rcases hp with hp | hp <;> (have := addFC_dst _ _ _ p hp; omega)
theorem wf_invK (d a : ℕ) (hd : 4 ≤ d) : WF (invK d a) :=
  fun p hp => by have := invKC_dst d a p hp; omega

/-! ## Controls (kernel-checked)

Programs that read their operands from the tape into registers `64 …`, run one routine and
output the result, run by the contract's interpreter (`XProg.run`) with `260` memory words. The
`F` and `K` operands and products are `FRFieldControls`' first KAT (S-A's independent
schoolbook reference, `probe/fr-field/kat.py`).

* Positive: `mulF`, `mulK` give the KAT products (`mulF_kat`, `mulK_kat`); `sqF`, `sqK` give
  `F.sq`, `K.sq` of the operand (`sqF_kat`, `sqK_kat`); `invF` gives an inverse, checked by `F`'s
  own product (`invF_kat`; it runs `invB`); `invK_guard` instantiates `invK_sem`.
* **The measured step count of one `F` product**: the program that is only `mulF` halts with
  `260 + 65` fuel and not with `260 + 64` (`mulF_alone`): `8` for the prologue and `57`, the
  `steps_mulF` count.
* Negative: with the reduction constant cell overwritten (a program that is not `WF`), `mulF`
  does not give the product (`mulF_bad_const`): the invariant is needed.
-/

namespace Controls

/-- Read `n` tape words into registers `base …`. -/
def readN (base : ℕ) : ℕ → XIR
  | 0 => .blk []
  | k + 1 => .seq (readN base k) (.seq (.blk [.const 120 (BitVec.ofNat 64 k)]) (.input (base + k)
      120))

/-- Output registers `base … base + n − 1`. -/
def outN (base : ℕ) : ℕ → XIR
  | 0 => .blk []
  | k + 1 => .seq (outN base k) (.out (base + k))

/-- Read two `n`-word operands into `64 …`, run `op`, output `n` words from `64 + 2n`. -/
def binProg (n : ℕ) (op : XIR) : XIR := .seq (readN 64 (2 * n)) (.seq op (outN (64 + 2 * n) n))

/-- Read one `n`-word operand into `64 …`, run `op`, output `n` words from `64 + n`. -/
def unProg (n : ℕ) (op : XIR) : XIR := .seq (readN 64 n) (.seq op (outN (64 + n) n))

/-- `FRFieldControls`' first `F` KAT operands. -/
def tF : List Word := [0x0CC65817272B53A4, 0x2120FC8CCEE55FE9, 0x99363C9930CF43AC,
    0x6889C91E3005A706]

/-- `FRFieldControls`' first `K` KAT operands. -/
def tK : List Word := [0x2641940B4DF62868, 0xC0450C5C86166DEC, 0x5298E4BB63FE5590,
  0x5DB1608995CCB6A0, 0x95E30255B5D45D27, 0x18B2BF46EE11E992, 0x91782A4F625E5555,
  0xB49F8D70989DA94A]

theorem mulF_kat : (toProg 260 0 (binProg 2 (mulF 68 64 66))).run tF 400 =
    some [0x6BDB7CDE7A2DD504, 0x24D581B7235CF4BE] := by decide +kernel

theorem mulF_alone : (toProg 260 0 (mulF 68 64 66)).run [] (260 + 65) = some [] ∧
    (toProg 260 0 (mulF 68 64 66)).run [] (260 + 64) = none := by decide +kernel

theorem mulF_bad_const : (toProg 260 0 (.seq (.blk [.const cRed 0x1D])
    (binProg 2 (mulF 68 64 66)))).run tF 400 ≠ some [0x6BDB7CDE7A2DD504, 0x24D581B7235CF4BE] := by
  decide +kernel

theorem mulK_kat : (toProg 260 0 (binProg 4 (mulK 72 64 68))).run tK 800 =
    some [0xA7076D7E76A71A45, 0xB6C9CAE676ACD4CA, 0x423E1CBA3D46D2A5, 0xFBB4F8964518C30E] := by
  decide +kernel

theorem sqF_kat : (toProg 260 0 (unProg 2 (sqF 66 64))).run (tF.take 2) 400 =
      some [0xB24FF16D68E5D124, 0x3C4F381611239331] ∧
    F.sq ⟨wB 0x0CC65817272B53A4, wB 0x2120FC8CCEE55FE9⟩ =
      ⟨wB 0xB24FF16D68E5D124, wB 0x3C4F381611239331⟩ := by decide +kernel

theorem sqK_kat : (toProg 260 0 (unProg 4 (sqK 68 64))).run (tK.take 4) 800 =
      some [0xCBBCB27A7B1A08EB, 0xCD0DD1B75DEFD511, 0xFAB9BB0275E22E60, 0xED7CE74A991282C0] ∧
    K.sq ⟨⟨wB 0x2641940B4DF62868, wB 0xC0450C5C86166DEC⟩,
      ⟨wB 0x5298E4BB63FE5590, wB 0x5DB1608995CCB6A0⟩⟩ =
      ⟨⟨wB 0xCBBCB27A7B1A08EB, wB 0xCD0DD1B75DEFD511⟩,
        ⟨wB 0xFAB9BB0275E22E60, wB 0xED7CE74A991282C0⟩⟩ := by decide +kernel

theorem invF_kat : (toProg 260 0 (unProg 2 (invF 66 64))).run (tF.take 2) 2000 =
      some [0x08997E30FD2DF9B0, 0x269AB2B00B5F9067] ∧
    (⟨wB 0x0CC65817272B53A4, wB 0x2120FC8CCEE55FE9⟩ : F) *
      ⟨wB 0x08997E30FD2DF9B0, wB 0x269AB2B00B5F9067⟩ = 1 := by decide +kernel

/-- The routines' hypotheses are met: the prologue's state satisfies `Inv` and the `K` inverse's
register bounds hold at `d = 68`, `a = 64` (a guard; the `K` inverse's run, 1,379 steps, is
not evaluated by the kernel, see `S-H1-RESULT.md`). -/
theorem invK_guard (I : Array Word) : rdK (semXIR I (invK 68 64) (initSt 260)).M 68 =
    (rdK (initSt 260).M 64)⁻¹ :=
  invK_sem (inv_initSt (by decide)) (by decide) (by decide) (by decide)

end Controls

end FR.X
