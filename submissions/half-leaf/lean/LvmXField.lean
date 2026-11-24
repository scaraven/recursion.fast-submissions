-- New for lvm (WP-3). The `K` blocks follow `flock-recursive` `FRXField.lean`'s `B64` blocks (rf-k
-- kk/base 8bff272b: `redC`, `mulBC`, `invBC`), re-targeted from FR's `B64` to CompPoly's `BF64`; the
-- `E = Ext3` blocks are new.
import LvmXDsl
import CompPoly.Fields.Binary.BF64.Ext3

-- (GOLF2: 36 declarations that `certified` does not use moved verbatim to `LvmXSComputesOff`, outside its import closure.)

/-!
# Field arithmetic of `K = GF(2^64)` and `E = GF(2^192)` as `XIR` blocks

`K` is CompPoly's `BF64` (`GF(2)[x] / (x^64 + x^4 + x^3 + x + 1)`, polynomial basis, bit `i` the
coefficient of `x^i`), `E` is CompPoly's `BF64.Ext3 = K[y] / (y^3 + y + 1)` (coefficients
`c₀ + c₁ y + c₂ y²`). A `K` element sits in one machine word (`rdK`), an `E` element in three
consecutive registers, `c₀` first (`rdE`).

## The `K` product on the machine

`clmul`, `clmulh` give the low and high words of the 128-bit carry-less product; the reduction of
`lo + x^64 hi` by `x^64 = x^4 + x^3 + x + 1` uses the carry-less product again (`redW`, five
operations, `Qw_red`): `mulK` is **7 statements, 13 steps**.

## The `E` product (lazy reduction)

`(a₀ + a₁y + a₂y²)(b₀ + b₁y + b₂y²)` with `y³ = y + 1`, `y⁴ = y² + y`:
`r₀ = a₀b₀ + p₃`, `r₁ = a₀b₁ + a₁b₀ + p₃ + a₂b₂`, `r₂ = a₀b₂ + a₁b₁ + a₂b₀ + a₂b₂`,
`p₃ = a₁b₂ + a₂b₁` (`Ext3_mul`). The nine 128-bit carry-less products are summed unreduced and
each coefficient is reduced once: 18 products, 16 `xor`s, 3 reductions: **49 statements, 97 steps**
(`mulE`). On this machine a carry-less product is one statement, so the schoolbook form beats
Karatsuba (fewer `xor`s).

## Exact step counts (on the compiled code, `seq` nodes included; `steps_*` = `cost_*`)

`addK` 1; `mulK`, `sqK` 13; `invK` 1,033; `addE` 5; `mulEK` (`E × K`) 41; `sqE` 45; `mulE` 97;
`invE` 1,217 (cofactors and norm, one `K` inverse: `mkE_inv`).

## Scratch cells

`mulK` uses cells `5 … 8`, `invK` `5 … 11`, `sqE` `5 … 9`, `invE` `5 … 19`, `mulE` `5 … 24`. Operands and results
are registers above a routine's scratch; a result may be an operand (`d = a`), never an
overlapping range.
-/

namespace Lvm.X

open RecursionFast Polynomial BinaryField CompPoly.Extension BF64

/-! ## Words as field elements -/

/-- The word as a `K = BF64` element (polynomial basis). -/
def wK (w : Word) : BF64 := BF64.ofBitVec w

/-- The `K` element in register `a`. -/
def rdK (M : Mem) (a : ℕ) : BF64 := wK (rd M a)

/-- The `E` element `c₀ + c₁ y + c₂ y²`. -/
def mkE (c₀ c₁ c₂ : BF64) : Ext3 := Ext.ofVector #v[c₀, c₁, c₂]

/-- The `E` element in registers `a, a + 1, a + 2`. -/
def rdE (M : Mem) (a : ℕ) : Ext3 := mkE (rdK M a) (rdK M (a + 1)) (rdK M (a + 2))

theorem wK_xor (x y : Word) : wK (x ^^^ y) = wK x + wK y := rfl

/-! ## Word-level operations -/

/-- The low word of the carry-less product. -/
def clo (a b : Word) : Word := XOp.clmul.eval a b
/-- The high word of the carry-less product. -/
def chi (a b : Word) : Word := XOp.clmulh.eval a b

/-- The reduction of `lo + x^64 hi` by two carry-less products with `0x1B`. -/
def redW (lo hi : Word) : Word := lo ^^^ clo hi 0x1B ^^^ clo (chi hi 0x1B) 0x1B

/-- The `K` product of words. -/
def mulKW (a b : Word) : Word := redW (clo a b) (chi a b)

/-! ## Polynomials (proof helpers) -/

/-- The class of a word modulo the `K` modulus. -/
noncomputable abbrev Qw (w : Word) : BF64Quot := AdjoinRoot.mk BF64.basePoly (toPoly w)

theorem toQuot_wK (w : Word) : BF64.toQuot (wK w) = Qw w := rfl

theorem wK_eq_of_Qw {v : Word} {x : BF64} (h : Qw v = BF64.toQuot x) : wK v = x :=
  BF64.toQuot_injective (by rw [toQuot_wK, h])

theorem xf_add_mul_swap {R : Type*} [CommSemiring R] (x a b : R) : a + x * b = b * x + a := by ring

/-- `xf_add_mul_swap` stated at `(ZMod 2)[X]` (GOLF3: its instance at the words' polynomials made the kernel
unfold them, 0.5 M heartbeats). -/
private theorem xf_poly : ∀ x a b : (ZMod 2)[X], a + x * b = b * x + a := fun _ _ _ => by
  rw [add_comm, mul_comm]

theorem clmul_poly (a b : Word) : toPoly (clo a b) + X ^ 64 * toPoly (chi a b) =
    toPoly a * toPoly b := by
  have h := BF64.toPoly_halves (RecursionFast.clmul a b)
  have hc : toPoly (RecursionFast.clmul a b) = toPoly a * toPoly b :=
    toPoly_carryLessMul a b (by norm_num)
  rw [hc] at h
  -- unfolded by `rw` (left to the kernel's defeq, `clo`/`highHalf` against `setWidth` cost 0.5 s)
  rw [h, BF64.highHalf, BF64.lowHalf, clo, chi, XOp.eval, XOp.eval]
  exact xf_poly _ _ _

theorem chi_red_lt (hi : Word) : (chi hi 0x1B).toNat < 2 ^ 5 :=
  BF64.highHalf_lt _ (BF64.carryLessMul_lt hi BF64.reductionConstant hi.isLt
    BF64.reductionConstant_lt (by norm_num))

theorem chi_chi_red (hi : Word) : chi (chi hi 0x1B) 0x1B = 0 := by
  have h : (chi (chi hi 0x1B) 0x1B).toNat < 2 ^ 0 := BF64.highHalf_lt (d := 0) _
    (lt_of_lt_of_le (BF64.carryLessMul_lt (w := 128) (chi hi 0x1B) BF64.reductionConstant
      (chi_red_lt hi) BF64.reductionConstant_lt (by norm_num)) (by norm_num))
  exact BitVec.eq_of_toNat_eq (by simpa using h)

theorem toPoly_red : toPoly (0x1B : Word) = BF64.baseTail := BF64.toPoly_reductionConstant

/-- `Qw_red`'s closing identity over any ring of characteristic two (GOLF3: `linear_combination` in
`(ZMod 2)[X]` cost the kernel 1.3 M heartbeats). -/
private theorem qw_red_ring {R : Type*} [CommRing R] (h2 : (2 : R) = 0) (x t lo hi c1 c2 c3 : R)
    (e1 : c1 + x * c2 = hi * t) (e3 : c3 + x * 0 = c2 * t) :
    lo + c1 + c3 - (lo + x * hi) = (x + t) * (hi + c2) := by
  linear_combination e1 + e3 - x * (hi + c2) * h2

/-- `mulEW_spec`'s three closing identities over any commutative ring (GOLF3: `linear_combination` in
`(ZMod 2)[X]` cost the kernel 5.5 M heartbeats). -/
private theorem mulEW_ring0 {R : Type*} [CommRing R] (x l1 l2 l3 h1 h2 h3 q1 q2 q3 : R)
    (e1 : l1 + x * h1 = q1) (e2 : l2 + x * h2 = q2) (e3 : l3 + x * h3 = q3) :
    l1 + (l2 + l3) + x * (h1 + (h2 + h3)) = q1 + (q2 + q3) := by
  linear_combination e1 + e2 + e3

private theorem mulEW_ring1 {R : Type*} [CommRing R] (x l1 l2 l3 l4 l5 h1 h2 h3 h4 h5 q1 q2 q3 q4 q5 : R)
    (e1 : l1 + x * h1 = q1) (e2 : l2 + x * h2 = q2) (e3 : l3 + x * h3 = q3) (e4 : l4 + x * h4 = q4)
    (e5 : l5 + x * h5 = q5) :
    l1 + l2 + (l3 + l4) + l5 + x * (h1 + h2 + (h3 + h4) + h5) = q1 + q2 + (q3 + q4) + q5 := by
  linear_combination e1 + e2 + e3 + e4 + e5

private theorem mulEW_ring2 {R : Type*} [CommRing R] (x l1 l2 l3 l4 h1 h2 h3 h4 q1 q2 q3 q4 : R)
    (e1 : l1 + x * h1 = q1) (e2 : l2 + x * h2 = q2) (e3 : l3 + x * h3 = q3) (e4 : l4 + x * h4 = q4) :
    l1 + l2 + l3 + l4 + x * (h1 + h2 + h3 + h4) = q1 + q2 + q3 + q4 := by
  linear_combination e1 + e2 + e3 + e4

/-- GOLF3: the four identities at `(ZMod 2)[X]` in one declaration, so that the kernel unfolds
`Polynomial.commRing`'s operations against `(ZMod 2)[X]`'s once, not at every use. -/
private theorem poly_ids :
    (∀ x t lo hi c1 c2 c3 : (ZMod 2)[X], c1 + x * c2 = hi * t → c3 + x * 0 = c2 * t →
      lo + c1 + c3 - (lo + x * hi) = (x + t) * (hi + c2)) ∧
    (∀ x l1 l2 l3 h1 h2 h3 q1 q2 q3 : (ZMod 2)[X], l1 + x * h1 = q1 → l2 + x * h2 = q2 →
      l3 + x * h3 = q3 → l1 + (l2 + l3) + x * (h1 + (h2 + h3)) = q1 + (q2 + q3)) ∧
    (∀ x l1 l2 l3 l4 l5 h1 h2 h3 h4 h5 q1 q2 q3 q4 q5 : (ZMod 2)[X], l1 + x * h1 = q1 → l2 + x * h2 = q2 →
      l3 + x * h3 = q3 → l4 + x * h4 = q4 → l5 + x * h5 = q5 →
      l1 + l2 + (l3 + l4) + l5 + x * (h1 + h2 + (h3 + h4) + h5) = q1 + q2 + (q3 + q4) + q5) ∧
    (∀ x l1 l2 l3 l4 h1 h2 h3 h4 q1 q2 q3 q4 : (ZMod 2)[X], l1 + x * h1 = q1 → l2 + x * h2 = q2 →
      l3 + x * h3 = q3 → l4 + x * h4 = q4 →
      l1 + l2 + l3 + l4 + x * (h1 + h2 + h3 + h4) = q1 + q2 + q3 + q4) :=
  ⟨qw_red_ring ZMod2Poly.two_eq_zero, mulEW_ring0, mulEW_ring1, mulEW_ring2⟩

/-- `Qw_red`'s class step on variables (GOLF3: on the words' polynomials the kernel unfolded them, 1.1 M
heartbeats). -/
private theorem qw_mk : ∀ x t l h c1 c2 c3 : (ZMod 2)[X], BF64.basePoly = x + t → c1 + x * c2 = h * t →
    c3 + x * 0 = c2 * t →
      AdjoinRoot.mk BF64.basePoly (l + c1 + c3) = AdjoinRoot.mk BF64.basePoly (l + x * h) := by
  intro x t l h c1 c2 c3 hb e1 e3
  rw [AdjoinRoot.mk_eq_mk, hb]
  exact ⟨h + c2, poly_ids.1 x t l h c1 c2 c3 e1 e3⟩

/-- **The reduction is the class** of `lo + x^64 hi`. -/
theorem Qw_red (lo hi : Word) :
    Qw (redW lo hi) = AdjoinRoot.mk BF64.basePoly (toPoly lo + X ^ 64 * toPoly hi) := by
  have h1 := clmul_poly hi 0x1B
  have h3 := clmul_poly (chi hi 0x1B) 0x1B
  rw [chi_chi_red, show (0 : Word) = BitVec.ofNat 64 0 from rfl, toPoly_zero_eq_zero] at h3
  rw [toPoly_red] at h1 h3
  have hr : toPoly (redW lo hi) = toPoly lo + toPoly (clo hi 0x1B) + toPoly (clo (chi hi 0x1B) 0x1B) := by
    simp only [redW, toPoly_xor]
  have hb := BF64.basePoly_eq_add_tail
  rw [Qw, hr]
  generalize toPoly (clo (chi hi 0x1B) 0x1B) = c3 at h3 ⊢
  generalize toPoly (clo hi 0x1B) = c1 at h1 ⊢
  generalize toPoly (chi hi 0x1B) = c2 at h1 h3
  generalize toPoly lo = l
  generalize toPoly hi = h at h1 ⊢
  generalize BF64.baseTail = t at h1 h3 hb
  generalize (X ^ 64 : (ZMod 2)[X]) = x at h1 h3 hb ⊢
  exact qw_mk x t l h c1 c2 c3 hb h1 h3

/-- A reduction of a sum of carry-less products is the sum of the field products. -/
theorem wK_red_of_poly {lo hi : Word} {x : BF64} {p : Polynomial (ZMod 2)}
    (hp : toPoly lo + X ^ 64 * toPoly hi = p) (hx : AdjoinRoot.mk BF64.basePoly p = BF64.toQuot x) :
    wK (redW lo hi) = x :=
  wK_eq_of_Qw (by rw [Qw_red, hp, hx])

/-! ## Word-level correctness -/

/-- **The machine's `K` product is `BF64`'s.** -/
theorem mulKW_spec (a b : Word) : wK (mulKW a b) = wK a * wK b :=
  wK_red_of_poly (clmul_poly a b) (by rw [BF64.toQuot_mul, toQuot_wK, toQuot_wK, map_mul])

/-! ## Running blocks (proof helpers) -/

@[simp] theorem eval_clmul (a b : Word) : XOp.clmul.eval a b = clo a b := rfl
@[simp] theorem eval_clmulh (a b : Word) : XOp.clmulh.eval a b = chi a b := rfl

/-- The constant cells of a state satisfying `Inv`. -/
theorem inv_consts {M : Mem} (h : Inv M) : 256 ≤ M.size ∧ rd M 0 = 1 ∧ rd M 2 = 0x1B ∧
    rd M 3 = 63 := ⟨h.1, h.2 0 (by decide), h.2 2 (by decide), h.2 3 (by decide)⟩

/-! ## `K`: product, square, sum -/

/-- `M[d] := reduce(M[lo] + x^64 M[hi])`, with scratch `u`, `v` (5 statements). -/
def redC (d lo hi u v : ℕ) : List Prim :=
  [.op .clmul u hi cRed, .op .clmulh v hi cRed, .op .clmul v v cRed, .op .xor u lo u,
    .op .xor d u v]

/-- **The `K` product** `M[d] := M[a] · M[b]` (7 statements, scratch `5 … 8`). -/
def mulKC (d a b : ℕ) : List Prim :=
  ([.op .clmul 5 a b, .op .clmulh 6 a b] : List Prim) ++ redC d 5 6 7 8

theorem mulKC_dst (d a b : ℕ) : ∀ p ∈ mulKC d a b, p.dst = d ∨ (5 ≤ p.dst ∧ p.dst < 9) := by
  simp [mulKC, redC, Prim.dst]

theorem mulKC_run {M : Mem} (hM : Inv M) {d a b : ℕ} (hd : 9 ≤ d) (hd' : d < regs)
    (ha : 9 ≤ a) (hb : 9 ≤ b) :
    rd (runPrims (mulKC d a b) M) d = mulKW (rd M a) (rd M b) := by
  obtain ⟨hs, h0, h2, h3⟩ := inv_consts hM
  simp only [regs] at hd'
  simp only [mulKC, redC, List.cons_append, List.nil_append, runPrims_cons, runPrims_nil,
    Prim.run, cRed, mulKW, redW]
  simp (disch := first | decide | ((try simp only [size_set]); omega)) only [rd_set_self, rd_set_ne, h2,
    eval_clmul, eval_clmulh, eval_xor]

theorem mulKC_frame (d a b : ℕ) {i : ℕ} (hi : i < 5 ∨ 9 ≤ i) (hd : i ≠ d) (M : Mem) :
    rd (runPrims (mulKC d a b) M) i = rd M i :=
  rd_runPrims_of_not_writes (fun p hp => by have := mulKC_dst d a b p hp; omega) M

theorem mulKC_inv (d a b : ℕ) (hd : 4 ≤ d) {M : Mem} (hM : Inv M) :
    Inv (runPrims (mulKC d a b) M) :=
  inv_runPrims (fun p hp => by have := mulKC_dst d a b p hp; omega) hM

/-- **`mulKC` computes `K`'s product.** -/
theorem mulKC_spec {M : Mem} (hM : Inv M) {d a b : ℕ} (hd : 9 ≤ d) (hd' : d < regs)
    (ha : 9 ≤ a) (hb : 9 ≤ b) : rdK (runPrims (mulKC d a b) M) d = rdK M a * rdK M b := by
  rw [rdK, mulKC_run hM hd hd' ha hb, mulKW_spec]; rfl

/-! ## `K` inversion (Itoh–Tsujii, CompPoly's `BF64.invItohTsujii`) -/

/-- `M[r] := M[r]^(2^k)`: `k` squarings in place. -/
def sqnC (r k : ℕ) : List Prim := (List.replicate k (mulKC r r r)).flatten

/-- `M[r] := M[r]^(2^k) · M[y]`. -/
def stepC (r k y : ℕ) : List Prim := sqnC r k ++ mulKC r r y

/-- **The `K` inverse** `M[d] := M[a]⁻¹` (`0⁻¹ = 0`): `invItohTsujii`'s chain, 63 squarings and
10 products in cells `9` (`x`), `10` (the accumulator) and `11` (a copy); 517 statements. -/
def invKC (d a : ℕ) : List Prim :=
  ([.op .or 9 a a, .op .or 10 9 9] : List Prim) ++ stepC 10 1 9 ++ stepC 10 1 9 ++
  ([.op .or 11 10 10] : List Prim) ++ stepC 10 3 11 ++ stepC 10 1 9 ++
  ([.op .or 11 10 10] : List Prim) ++ stepC 10 7 11 ++ stepC 10 1 9 ++
  ([.op .or 11 10 10] : List Prim) ++ stepC 10 15 11 ++ stepC 10 1 9 ++
  ([.op .or 11 10 10] : List Prim) ++ stepC 10 31 11 ++ stepC 10 1 9 ++ mulKC d 10 10

/-- `invItohTsujii`'s chain on every element. -/
def chainK (u1 : BF64) : BF64 :=
  let u2 := powTwoPow u1 1 * u1
  let u3 := powTwoPow u2 1 * u1
  let u6 := powTwoPow u3 3 * u3
  let u7 := powTwoPow u6 1 * u1
  let u14 := powTwoPow u7 7 * u7
  let u15 := powTwoPow u14 1 * u1
  let u30 := powTwoPow u15 15 * u15
  let u31 := powTwoPow u30 1 * u1
  let u62 := powTwoPow u31 31 * u31
  let u63 := powTwoPow u62 1 * u1
  u63 * u63

theorem inv_eq_chainK (x : BF64) : x⁻¹ = chainK x := by
  rw [BF64.inv_def, invItohTsujii]
  split
  · next h => subst h; simp [chainK]
  · rfl

/-- The chain's registers: `x` in `9`, the accumulator in `10`, the copy in `11`. -/
def ChainSt (M : Mem) (x acc t : BF64) : Prop :=
  Inv M ∧ rdK M 9 = x ∧ rdK M 10 = acc ∧ rdK M 11 = t

theorem sqnC_dst (r k : ℕ) : ∀ p ∈ sqnC r k, p.dst = r ∨ (5 ≤ p.dst ∧ p.dst < 9) := by
  intro p hp
  simp only [sqnC, List.mem_flatten, List.mem_replicate] at hp
  obtain ⟨l, ⟨_, rfl⟩, hp⟩ := hp
  exact mulKC_dst r r r p hp

theorem sqnC_run {r : ℕ} (hr : 9 ≤ r) (hr' : r < regs) :
    ∀ (k : ℕ) {M : Mem}, Inv M → rdK (runPrims (sqnC r k) M) r = powTwoPow (rdK M r) k
  | 0, _, _ => rfl
  | k + 1, M, hM => by
    rw [show sqnC r (k + 1) = mulKC r r r ++ sqnC r k by simp [sqnC, List.replicate_succ],
      runPrims_append, sqnC_run hr hr' k (mulKC_inv r r r (by omega) hM),
      mulKC_spec hM hr hr' hr hr]
    rfl

theorem stepC_dst (r k y : ℕ) : ∀ p ∈ stepC r k y, p.dst = r ∨ (5 ≤ p.dst ∧ p.dst < 9) := by
  intro p hp
  rcases List.mem_append.mp hp with hp | hp
  · exact sqnC_dst r k p hp
  · exact mulKC_dst r r y p hp

theorem stepC_chain {M : Mem} {x acc t : BF64} (h : ChainSt M x acc t) (k : ℕ) :
    ChainSt (runPrims (stepC 10 k 9) M) x (powTwoPow acc k * x) t ∧
      ChainSt (runPrims (stepC 10 k 11) M) x (powTwoPow acc k * t) t := by
  obtain ⟨hM, h9, h10, h11⟩ := h
  have hi := inv_runPrims (fun p hp => by have := sqnC_dst 10 k p hp; omega) hM
  have f9 := rd_runPrims_of_not_writes (i := 9) (fun p hp => by have := sqnC_dst 10 k p hp; omega) M
  have f11 := rd_runPrims_of_not_writes (i := 11)
    (fun p hp => by have := sqnC_dst 10 k p hp; omega) M
  have s10 := sqnC_run (r := 10) (by omega) (by simp [regs]) k hM
  refine ⟨⟨inv_runPrims (fun p hp => by have := stepC_dst 10 k 9 p hp; omega) hM, ?_, ?_, ?_⟩,
    ⟨inv_runPrims (fun p hp => by have := stepC_dst 10 k 11 p hp; omega) hM, ?_, ?_, ?_⟩⟩ <;>
    simp only [stepC, runPrims_append, rdK] at f9 f11 s10 h9 h10 h11 ⊢
  · rw [mulKC_frame _ _ _ (by omega) (by omega), f9, h9]
  · rw [mulKC_run hi (by omega) (by simp [regs]) (by omega) (by omega), mulKW_spec, s10, f9, h9,
      h10]
  · rw [mulKC_frame _ _ _ (by omega) (by omega), f11, h11]
  · rw [mulKC_frame _ _ _ (by omega) (by omega), f9, h9]
  · rw [mulKC_run hi (by omega) (by simp [regs]) (by omega) (by omega), mulKW_spec, s10, f11, h11,
      h10]
  · rw [mulKC_frame _ _ _ (by omega) (by omega), f11, h11]

theorem copy_chain {M : Mem} {x acc t : BF64} (h : ChainSt M x acc t) :
    ChainSt (runPrims [.op .or 11 10 10] M) x acc acc := by
  obtain ⟨hM, h9, h10, h11⟩ := h
  have hs : 11 < M.size := by have := hM.1; simp only [regs] at this; omega
  refine ⟨inv_runPrims (by simp [Prim.dst]) hM, ?_, ?_, ?_⟩ <;>
    simp only [runPrims_cons, runPrims_nil, Prim.run, rdK] at h9 h10 ⊢
  · rw [rd_set_ne (by decide), h9]
  · rw [rd_set_ne (by decide), h10]
  · rw [rd_set_self hs, eval_or, BitVec.or_self, h10]

theorem invKC_dst (d a : ℕ) : ∀ p ∈ invKC d a, p.dst = d ∨ (5 ≤ p.dst ∧ p.dst < 12) := by
  intro p hp
  delta invKC at hp
  simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with ((((((((((((((((hp | hp) | hp) | hp) | hp) | hp) | hp) | hp) | hp) | hp) | hp) |
      hp) |
    hp) | hp) | hp) | hp) | hp) <;>
    first
    | (subst hp; simp [Prim.dst])
    | (have := stepC_dst _ _ _ p hp; omega)
    | (have := mulKC_dst _ _ _ p hp; omega)

/-- **`invKC` computes `K`'s inverse.** -/
theorem invKC_spec {M : Mem} (hM : Inv M) {d a : ℕ} (hd : 12 ≤ d) (hd' : d < regs) :
    rdK (runPrims (invKC d a) M) d = (rdK M a)⁻¹ := by
  have hs : 11 < M.size := by have := hM.1; simp only [regs] at this; omega
  set x := rdK M a
  have h0 : ChainSt (runPrims [.op .or 9 a a, .op .or 10 9 9] M) x x (rdK M 11) := by
    refine ⟨inv_runPrims (by simp [Prim.dst]) hM, ?_, ?_, ?_⟩ <;>
      simp (disch := first | decide | ((try simp only [size_set]); omega)) only [runPrims_cons, runPrims_nil,
        Prim.run, rdK, x, rd_set_self, rd_set_ne, eval_or, BitVec.or_self]
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
  delta invKC
  simp only [runPrims_append]
  rw [mulKC_spec h10.1 (by omega) hd' (by omega) (by omega), inv_eq_chainK, h10.2.2.1]
  rfl

theorem invKC_frame (d a : ℕ) {i : ℕ} (hi : i < 5 ∨ 12 ≤ i) (hd : i ≠ d) (M : Mem) :
    rd (runPrims (invKC d a) M) i = rd M i :=
  rd_runPrims_of_not_writes (fun p hp => by have := invKC_dst d a p hp; omega) M

/-! ## `E = Ext3`: the field side -/

open scoped CompPoly.Extension.Ext

/-- `E`'s embedding of `K` into the specification quotient. -/
noncomputable abbrev ι (c : BF64) : Quot[ext3Params] := algebraMap BF64 Quot[ext3Params] c

/-- The adjoined root `y`. -/
noncomputable abbrev ry : Quot[ext3Params] := Ext.rt ext3Params

theorem toQuot_mkE (c₀ c₁ c₂ : BF64) :
    Ext.toQuot (mkE c₀ c₁ c₂) = ι c₀ + ι c₁ * ry + ι c₂ * ry ^ 2 := by
  rw [Ext.toQuot_rangeForm, ext3Params_d]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero]
  rw [show Ext.coeffNat (mkE c₀ c₁ c₂) 0 = c₀ from rfl, show Ext.coeffNat (mkE c₀ c₁ c₂) 1 = c₁ from rfl,
    show Ext.coeffNat (mkE c₀ c₁ c₂) 2 = c₂ from rfl]
  ring

/-- `y³ = y + 1` in the quotient. -/
theorem ry_cube : ry ^ 3 = ry + 1 := by
  have h := congrArg Ext.toQuot ext3Gen_pow_three
  rwa [Ext.toQuot_pow, toQuot_ext3Gen, Ext.toQuot_add, toQuot_ext3Gen, Ext.toQuot_one] at h

/-- **`E`'s product in coordinates** (`y³ = y + 1`). -/
theorem mkE_mul (a₀ a₁ a₂ b₀ b₁ b₂ : BF64) :
    mkE a₀ a₁ a₂ * mkE b₀ b₁ b₂ =
      mkE (a₀ * b₀ + (a₁ * b₂ + a₂ * b₁)) (a₀ * b₁ + a₁ * b₀ + (a₁ * b₂ + a₂ * b₁) + a₂ * b₂)
        (a₀ * b₂ + a₁ * b₁ + a₂ * b₀ + a₂ * b₂) := by
  apply Ext.toQuot_injective
  rw [Ext.toQuot_mul, toQuot_mkE, toQuot_mkE, toQuot_mkE]
  simp only [ι, map_add, map_mul]
  linear_combination (algebraMap BF64 Quot[ext3Params] a₁ * algebraMap BF64 Quot[ext3Params] b₂ +
    algebraMap BF64 Quot[ext3Params] a₂ * algebraMap BF64 Quot[ext3Params] b₁ +
    algebraMap BF64 Quot[ext3Params] a₂ * algebraMap BF64 Quot[ext3Params] b₂ * ry) * ry_cube

/-- `E`'s sum in coordinates. -/
theorem mkE_add (a₀ a₁ a₂ b₀ b₁ b₂ : BF64) :
    mkE a₀ a₁ a₂ + mkE b₀ b₁ b₂ = mkE (a₀ + b₀) (a₁ + b₁) (a₂ + b₂) := by
  apply Ext.toQuot_injective
  rw [Ext.toQuot_add, toQuot_mkE, toQuot_mkE, toQuot_mkE]
  simp only [ι, map_add]
  ring

/-- `E × K` in coordinates. -/
theorem mkE_smul (a₀ a₁ a₂ k : BF64) :
    mkE a₀ a₁ a₂ * mkE k 0 0 = mkE (a₀ * k) (a₁ * k) (a₂ * k) := by
  rw [mkE_mul]; congr 1 <;> ring

/-- `K ⊂ E`: `mkE k 0 0` is the embedding of `k`. -/
theorem mkE_base (k : BF64) : mkE k 0 0 = algebraMap BF64 Ext3 k := by
  apply Ext.toQuot_injective
  rw [toQuot_mkE, Ext.algebraMap_eq_ofBase, Ext.toQuot_ofBase]
  simp [ι, AdjoinRoot.algebraMap_eq]

/-! ## `E` on the machine -/

/-- The `E` product of words, as `mulEC` computes it: nine carry-less products summed unreduced,
three reductions. -/
def mulEW (a₀ a₁ a₂ b₀ b₁ b₂ : Word) : Word × Word × Word :=
  let l3 := clo a₁ b₂ ^^^ clo a₂ b₁
  let h3 := chi a₁ b₂ ^^^ chi a₂ b₁
  (redW (clo a₀ b₀ ^^^ l3) (chi a₀ b₀ ^^^ h3),
   redW (clo a₀ b₁ ^^^ clo a₁ b₀ ^^^ l3 ^^^ clo a₂ b₂) (chi a₀ b₁ ^^^ chi a₁ b₀ ^^^ h3 ^^^ chi a₂ b₂),
   redW (clo a₀ b₂ ^^^ clo a₁ b₁ ^^^ clo a₂ b₀ ^^^ clo a₂ b₂)
     (chi a₀ b₂ ^^^ chi a₁ b₁ ^^^ chi a₂ b₀ ^^^ chi a₂ b₂))

theorem toQuot_mulW (a b : Word) :
    BF64.toQuot (wK a * wK b) = AdjoinRoot.mk BF64.basePoly (toPoly a * toPoly b) := by
  rw [BF64.toQuot_mul, toQuot_wK, toQuot_wK, map_mul]

/-- **The machine's `E` product is `Ext3`'s.** -/
theorem mulEW_spec (a₀ a₁ a₂ b₀ b₁ b₂ : Word) :
    mkE (wK (mulEW a₀ a₁ a₂ b₀ b₁ b₂).1) (wK (mulEW a₀ a₁ a₂ b₀ b₁ b₂).2.1)
        (wK (mulEW a₀ a₁ a₂ b₀ b₁ b₂).2.2) =
      mkE (wK a₀) (wK a₁) (wK a₂) * mkE (wK b₀) (wK b₁) (wK b₂) := by
  rw [mkE_mul]
  have p := clmul_poly
  congr 1
  · refine wK_red_of_poly (p := toPoly a₀ * toPoly b₀ + (toPoly a₁ * toPoly b₂ +
      toPoly a₂ * toPoly b₁)) ?_ ?_
    · simp only [toPoly_xor]
      exact poly_ids.2.1 _ _ _ _ _ _ _ _ _ _ (p a₀ b₀) (p a₁ b₂) (p a₂ b₁)
    · rw [BF64.toQuot_add, BF64.toQuot_add, toQuot_mulW, toQuot_mulW, toQuot_mulW, map_add,
        map_add]
  · refine wK_red_of_poly (p := toPoly a₀ * toPoly b₁ + toPoly a₁ * toPoly b₀ +
      (toPoly a₁ * toPoly b₂ + toPoly a₂ * toPoly b₁) + toPoly a₂ * toPoly b₂) ?_ ?_
    · simp only [toPoly_xor]
      exact poly_ids.2.2.1 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ (p a₀ b₁) (p a₁ b₀) (p a₁ b₂) (p a₂ b₁)
        (p a₂ b₂)
    · rw [BF64.toQuot_add, BF64.toQuot_add, BF64.toQuot_add, BF64.toQuot_add, toQuot_mulW,
        toQuot_mulW, toQuot_mulW, toQuot_mulW, toQuot_mulW, map_add, map_add, map_add, map_add]
  · refine wK_red_of_poly (p := toPoly a₀ * toPoly b₂ + toPoly a₁ * toPoly b₁ +
      toPoly a₂ * toPoly b₀ + toPoly a₂ * toPoly b₂) ?_ ?_
    · simp only [toPoly_xor]
      exact poly_ids.2.2.2 _ _ _ _ _ _ _ _ _ _ _ _ _ (p a₀ b₂) (p a₁ b₁) (p a₂ b₀) (p a₂ b₂)
    · rw [BF64.toQuot_add, BF64.toQuot_add, BF64.toQuot_add, toQuot_mulW, toQuot_mulW,
        toQuot_mulW, toQuot_mulW, map_add, map_add, map_add]

/-- **The `E` product** `M[d … d+2] := M[a … a+2] · M[b … b+2]` (49 statements, scratch
`5 … 24`): the nine carry-less products into `5 … 22` (`P_ij` at `5 + 2(3i + j)`), `p₃` into
`P₁₂`, the three unreduced coefficients into `P₀₀`, `P₀₁`, `P₀₂`, three reductions. -/
def mulEC (d a b : ℕ) : List Prim :=
  ([.op .clmul 5 a b, .op .clmulh 6 a b, .op .clmul 7 a (b + 1), .op .clmulh 8 a (b + 1),
   .op .clmul 9 a (b + 2), .op .clmulh 10 a (b + 2),
   .op .clmul 11 (a + 1) b, .op .clmulh 12 (a + 1) b, .op .clmul 13 (a + 1) (b + 1),
   .op .clmulh 14 (a + 1) (b + 1), .op .clmul 15 (a + 1) (b + 2), .op .clmulh 16 (a + 1) (b + 2),
   .op .clmul 17 (a + 2) b, .op .clmulh 18 (a + 2) b, .op .clmul 19 (a + 2) (b + 1),
   .op .clmulh 20 (a + 2) (b + 1), .op .clmul 21 (a + 2) (b + 2), .op .clmulh 22 (a + 2) (b + 2),
   .op .xor 15 15 19, .op .xor 16 16 20,
   .op .xor 5 5 15, .op .xor 6 6 16,
   .op .xor 7 7 11, .op .xor 8 8 12, .op .xor 7 7 15, .op .xor 8 8 16, .op .xor 7 7 21,
   .op .xor 8 8 22,
   .op .xor 9 9 13, .op .xor 10 10 14, .op .xor 9 9 17, .op .xor 10 10 18, .op .xor 9 9 21,
   .op .xor 10 10 22] : List Prim) ++
  redC d 5 6 23 24 ++ redC (d + 1) 7 8 23 24 ++ redC (d + 2) 9 10 23 24

theorem mulEC_dst (d a b : ℕ) :
    ∀ p ∈ mulEC d a b, p.dst = d ∨ p.dst = d + 1 ∨ p.dst = d + 2 ∨ (5 ≤ p.dst ∧ p.dst < 25) := by
  simp only [mulEC, redC, List.forall_mem_append, List.forall_mem_cons, Prim.dst, List.mem_nil_iff,
    false_implies, implies_true, true_or, or_true, and_true]
  and_intros <;> omega

theorem mulEC_run {M : Mem} (hM : Inv M) {d a b : ℕ} (hd : 25 ≤ d) (hd' : d + 3 ≤ regs)
    (ha : 25 ≤ a) (hb : 25 ≤ b) :
    rd (runPrims (mulEC d a b) M) d =
      (mulEW (rd M a) (rd M (a + 1)) (rd M (a + 2)) (rd M b) (rd M (b + 1)) (rd M (b + 2))).1 ∧
    rd (runPrims (mulEC d a b) M) (d + 1) =
      (mulEW (rd M a) (rd M (a + 1)) (rd M (a + 2)) (rd M b) (rd M (b + 1)) (rd M (b + 2))).2.1 ∧
    rd (runPrims (mulEC d a b) M) (d + 2) =
      (mulEW (rd M a) (rd M (a + 1)) (rd M (a + 2)) (rd M b) (rd M (b + 1)) (rd M (b + 2))).2.2 := by
  obtain ⟨hs, h0, h2, h3⟩ := inv_consts hM
  simp only [regs] at hd'
  simp only [mulEC, redC, List.cons_append, List.nil_append, runPrims_cons, runPrims_nil,
    Prim.run, cRed, mulEW, redW]
  simp (disch := first | decide | (clear * - hd hd' ha hb hs; (try simp only [size_set]); omega)) only
    [rd_set_self, rd_set_ne, h2, eval_clmul, eval_clmulh, eval_xor, and_self]

/-- **`mulEC` computes `E`'s product.** -/
theorem mulEC_spec {M : Mem} (hM : Inv M) {d a b : ℕ} (hd : 25 ≤ d) (hd' : d + 3 ≤ regs)
    (ha : 25 ≤ a) (hb : 25 ≤ b) : rdE (runPrims (mulEC d a b) M) d = rdE M a * rdE M b := by
  obtain ⟨h0, h1, h2⟩ := mulEC_run hM hd hd' ha hb
  simp only [rdE, rdK, h0, h1, h2]
  exact mulEW_spec ..

/-- `M[d … d+2] := M[a … a+2] + M[b … b+2]` (3 statements). -/
def addEC (d a b : ℕ) : List Prim :=
  [.op .xor d a b, .op .xor (d + 1) (a + 1) (b + 1), .op .xor (d + 2) (a + 2) (b + 2)]

/-- `M[d … d+2] := M[a … a+2] · M[k]`, `E × K` (21 statements, scratch `5 … 8`). -/
def mulEKC (d a k : ℕ) : List Prim := mulKC d a k ++ mulKC (d + 1) (a + 1) k ++ mulKC (d + 2) (a + 2) k

/-- `M[d … d+2] := M[a … a+2]²` (23 statements, scratch `5 … 9`): `a₀² + a₂² y + (a₁² + a₂²) y²`. -/
def sqEC (d a : ℕ) : List Prim :=
  mulKC 9 (a + 2) (a + 2) ++ mulKC d a a ++ mulKC (d + 2) (a + 1) (a + 1) ++
    [.op .xor (d + 2) (d + 2) 9, .op .or (d + 1) 9 9]

/-! ## `E` inversion: the cofactors and the norm -/

theorem mkE_inj {a₀ a₁ a₂ b₀ b₁ b₂ : BF64} (h : mkE a₀ a₁ a₂ = mkE b₀ b₁ b₂) :
    a₀ = b₀ ∧ a₁ = b₁ ∧ a₂ = b₂ := by
  have h' := congrArg Ext.coeffs h
  simp only [mkE, Ext.coeffs_ofVector] at h'
  exact ⟨congrArg (·[0]) h', congrArg (·[1]) h', congrArg (·[2]) h'⟩

theorem mkE_zero : mkE 0 0 0 = 0 := by
  rw [mkE_base, map_zero]

theorem mkE_one : mkE 1 0 0 = 1 := by
  rw [mkE_base, map_one]

/-- The cofactors and the norm on words (`invPre`'s registers `13, 14, 15, 17`). -/
def cof0W (a₀ a₁ a₂ : Word) : Word := mulKW (a₀ ^^^ a₂) (a₀ ^^^ a₂) ^^^ mulKW a₁ a₁ ^^^ mulKW a₁ a₂
/-- See `cof0W`. -/
def cof1W (a₀ a₁ a₂ : Word) : Word := mulKW a₀ a₁ ^^^ mulKW a₂ a₂
/-- See `cof0W`. -/
def cof2W (a₀ a₁ a₂ : Word) : Word := mulKW a₁ a₁ ^^^ mulKW a₂ a₂ ^^^ mulKW a₀ a₂
/-- See `cof0W`. -/
def normW (a₀ a₁ a₂ : Word) : Word :=
  mulKW a₀ (cof0W a₀ a₁ a₂) ^^^ mulKW a₂ (cof1W a₀ a₁ a₂) ^^^ mulKW a₁ (cof2W a₀ a₁ a₂)

/-- The cofactors and the norm of `M[a … a+2]` into `13, 14, 15` and `17` (71 statements, scratch
`5 … 8`, `12`, `16`, `19`). -/
def invPre (a : ℕ) : List Prim :=
  [Prim.op .xor 12 a (a + 2)] ++ mulKC 13 12 12 ++ mulKC 16 (a + 1) (a + 1) ++
  [Prim.op .xor 13 13 16] ++ mulKC 19 (a + 1) (a + 2) ++ [Prim.op .xor 13 13 19] ++
  mulKC 14 a (a + 1) ++ mulKC 19 (a + 2) (a + 2) ++
  [Prim.op .xor 14 14 19, Prim.op .xor 15 16 19] ++ mulKC 16 a (a + 2) ++
  [Prim.op .xor 15 15 16] ++ mulKC 17 a 13 ++ mulKC 16 (a + 2) 14 ++ [Prim.op .xor 17 17 16] ++
  mulKC 16 (a + 1) 15 ++ [Prim.op .xor 17 17 16]

/-- **The `E` inverse** `M[d … d+2] := M[a … a+2]⁻¹` (`0⁻¹ = 0`; 609 statements, scratch
`5 … 19`): the cofactors and the norm, one `K` inverse, three `K` products. -/
def invEC (d a : ℕ) : List Prim :=
  invPre a ++ invKC 18 17 ++ mulKC d 18 13 ++ mulKC (d + 1) 18 14 ++ mulKC (d + 2) 18 15

/-! ## The routines as `XIR` -/

/-- `M[d] := M[a] + M[b]` in `K`. -/
def addK (d a b : ℕ) : XIR := .blk [.op .xor d a b]
/-- `M[d] := M[a] · M[b]` in `K`. -/
def mulK (d a b : ℕ) : XIR := .blk (mulKC d a b)
/-- `M[d] := M[a]²` in `K`. -/
def sqK (d a : ℕ) : XIR := .blk (mulKC d a a)
/-- `M[d] := M[a]⁻¹` in `K`. -/
def invK (d a : ℕ) : XIR := .blk (invKC d a)
/-- `M[d … d+2] := M[a … a+2] + M[b … b+2]` in `E`. -/
def addE (d a b : ℕ) : XIR := .blk (addEC d a b)
/-- `M[d … d+2] := M[a … a+2] · M[b … b+2]` in `E`. -/
def mulE (d a b : ℕ) : XIR := .blk (mulEC d a b)
/-- `M[d … d+2] := M[a … a+2] · M[k]`, `E × K`. -/
def mulEK (d a k : ℕ) : XIR := .blk (mulEKC d a k)
/-- `M[d … d+2] := M[a … a+2]²` in `E`. -/
def sqE (d a : ℕ) : XIR := .blk (sqEC d a)
/-- `M[d … d+2] := M[a … a+2]⁻¹` in `E`. -/
def invE (d a : ℕ) : XIR := .blk (invEC d a)

variable {I : Array Word} {s : St}

theorem sem_blk (ps : List Prim) : (semXIR I (.blk ps) s).M = runPrims ps s.M := rfl
theorem steps_blk (ps : List Prim) : steps I (.blk ps) s = blkSteps ps.length := rfl
theorem cost_blk (ps : List Prim) (t : ℕ) : cost (.blk ps) t = blkSteps ps.length := rfl

/-- **`K` sum.** -/
theorem addK_sem (hM : Inv s.M) {d a b : ℕ} (hd : d < regs) :
    rdK (semXIR I (addK d a b) s).M d = rdK s.M a + rdK s.M b := by
  have := hM.1
  simp only [regs] at hd this
  rw [addK, sem_blk, rdK, runPrims_cons, runPrims_nil, Prim.run, rd_set_self (by omega), eval_xor,
    wK_xor]; rfl

/-- **`K` product.** -/
theorem mulK_sem (hM : Inv s.M) {d a b : ℕ} (hd : 9 ≤ d) (hd' : d < regs) (ha : 9 ≤ a)
    (hb : 9 ≤ b) : rdK (semXIR I (mulK d a b) s).M d = rdK s.M a * rdK s.M b := by
  rw [mulK, sem_blk]; exact mulKC_spec hM hd hd' ha hb

/-- **`K` inverse.** -/
theorem invK_sem (hM : Inv s.M) {d a : ℕ} (hd : 12 ≤ d) (hd' : d < regs) :
    rdK (semXIR I (invK d a) s).M d = (rdK s.M a)⁻¹ := by
  rw [invK, sem_blk]; exact invKC_spec hM hd hd'

/-- **`E` product.** -/
theorem mulE_sem (hM : Inv s.M) {d a b : ℕ} (hd : 25 ≤ d) (hd' : d + 3 ≤ regs) (ha : 25 ≤ a)
    (hb : 25 ≤ b) : rdE (semXIR I (mulE d a b) s).M d = rdE s.M a * rdE s.M b := by
  rw [mulE, sem_blk]; exact mulEC_spec hM hd hd' ha hb

/-! ## Step counts (exact, on the compiled code: `n` statements and `n − 1` `seq` nodes) -/

theorem len_mulKC (d a b : ℕ) : (mulKC d a b).length = 7 := rfl
theorem len_sqnC (r k : ℕ) : (sqnC r k).length = 7 * k := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [show sqnC r (k + 1) = mulKC r r r ++ sqnC r k by simp [sqnC, List.replicate_succ],
      List.length_append, ih, len_mulKC]; ring
theorem len_stepC (r k y : ℕ) : (stepC r k y).length = 7 * k + 7 := by
  rw [stepC, List.length_append, len_sqnC, len_mulKC]
theorem len_invKC (d a : ℕ) : (invKC d a).length = 517 := by
  delta invKC
  simp only [List.length_append, len_stepC, len_mulKC, List.length_cons, List.length_nil]
theorem len_addEC (d a b : ℕ) : (addEC d a b).length = 3 := rfl
theorem len_mulEC (d a b : ℕ) : (mulEC d a b).length = 49 := rfl
theorem len_mulEKC (d a k : ℕ) : (mulEKC d a k).length = 21 := rfl
theorem len_sqEC (d a : ℕ) : (sqEC d a).length = 23 := rfl
theorem len_invEC (d a : ℕ) : (invEC d a).length = 609 := by
  delta invEC invPre
  simp only [List.length_append, len_invKC, len_mulKC, List.length_cons, List.length_nil]

@[simp] theorem steps_addK (d a b : ℕ) : steps I (addK d a b) s = 1 := rfl
/-- **One `K` product is 13 machine steps** (7 statements, 6 `seq` nodes). -/
@[simp] theorem steps_mulK (d a b : ℕ) : steps I (mulK d a b) s = 13 := by
  rw [mulK, steps_blk, len_mulKC]; rfl
@[simp] theorem steps_sqK (d a : ℕ) : steps I (sqK d a) s = 13 := by
  rw [sqK, steps_blk, len_mulKC]; rfl
@[simp] theorem steps_invK (d a : ℕ) : steps I (invK d a) s = 1033 := by
  rw [invK, steps_blk, len_invKC]; rfl
@[simp] theorem steps_addE (d a b : ℕ) : steps I (addE d a b) s = 5 := by
  rw [addE, steps_blk, len_addEC]; rfl
/-- **One `E` product is 97 machine steps** (49 statements, 48 `seq` nodes). -/
@[simp] theorem steps_mulE (d a b : ℕ) : steps I (mulE d a b) s = 97 := by
  rw [mulE, steps_blk, len_mulEC]; rfl
/-- **One `E × K` product is 41 machine steps.** -/
@[simp] theorem steps_mulEK (d a k : ℕ) : steps I (mulEK d a k) s = 41 := by
  rw [mulEK, steps_blk, len_mulEKC]; rfl
@[simp] theorem steps_sqE (d a : ℕ) : steps I (sqE d a) s = 45 := by
  rw [sqE, steps_blk, len_sqEC]; rfl
@[simp] theorem steps_invE (d a : ℕ) : steps I (invE d a) s = 1217 := by
  rw [invE, steps_blk, len_invEC]; rfl

@[simp] theorem cost_addK (d a b t : ℕ) : cost (addK d a b) t = 1 := rfl
@[simp] theorem cost_mulK (d a b t : ℕ) : cost (mulK d a b) t = 13 := by
  rw [mulK, cost_blk, len_mulKC]; rfl
@[simp] theorem cost_sqK (d a t : ℕ) : cost (sqK d a) t = 13 := by
  rw [sqK, cost_blk, len_mulKC]; rfl
@[simp] theorem cost_invK (d a t : ℕ) : cost (invK d a) t = 1033 := by
  rw [invK, cost_blk, len_invKC]; rfl
@[simp] theorem cost_addE (d a b t : ℕ) : cost (addE d a b) t = 5 := by
  rw [addE, cost_blk, len_addEC]; rfl
@[simp] theorem cost_mulE (d a b t : ℕ) : cost (mulE d a b) t = 97 := by
  rw [mulE, cost_blk, len_mulEC]; rfl
@[simp] theorem cost_mulEK (d a k t : ℕ) : cost (mulEK d a k) t = 41 := by
  rw [mulEK, cost_blk, len_mulEKC]; rfl
@[simp] theorem cost_sqE (d a t : ℕ) : cost (sqE d a) t = 45 := by
  rw [sqE, cost_blk, len_sqEC]; rfl
@[simp] theorem cost_invE (d a t : ℕ) : cost (invE d a) t = 1217 := by
  rw [invE, cost_blk, len_invEC]; rfl

/-! ## Well formed -/

theorem wf_addK (d a b : ℕ) (hd : 4 ≤ d) : WF (addK d a b) := by
  intro p hp; simp only [List.mem_singleton] at hp; subst hp; exact hd
theorem wf_mulK (d a b : ℕ) (hd : 4 ≤ d) : WF (mulK d a b) :=
  fun p hp => by have := mulKC_dst d a b p hp; omega
theorem wf_invK (d a : ℕ) (hd : 4 ≤ d) : WF (invK d a) :=
  fun p hp => by have := invKC_dst d a p hp; omega
theorem wf_mulE (d a b : ℕ) (hd : 4 ≤ d) : WF (mulE d a b) :=
  fun p hp => by have := mulEC_dst d a b p hp; omega
end Lvm.X
