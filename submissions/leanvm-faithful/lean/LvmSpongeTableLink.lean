-- New for lvm (WP-8): the KS sponge link as a doom specification (BLUEPRINT §4.2): V_S's `M3.v0` KS link
-- (`ksLink0`, `contShift`) on leanVM's DSL.
import LvmSpongeTable
import LvmChainTable
import LvmShift
import LvmKeccakCaller

-- ===== merged from `LvmChainTableLinkMath` (GOLF module merge: `LvmChainTableLinkMath.lean` is now a stub importing `LvmSpongeTableLink`) =====
section
-- New for lvm (WP-8): the algebra of the CH link (BLUEPRINT §4.1): V_S's `M3.v0` link formulas over `E`,
-- the zero-test tables and the identities the link's specification (`LvmChainTableLink`) needs.

/-!
# The `CH` link: formulas and identities

The link `in_{x+1} = Pad43(Y_x)` (`x + 1 < 2^h`) is checked bitwise on lanes `0 … 7` by a zero test
at `(ρ, λ, ζ) ∈ E^h × E^3 × E^6` and a shift sumcheck, and on lanes `8 … 24` (constants) by a zero
test riding on the shift sumcheck's challenges. With `ω(l, p) = eq(λ, l)·eq(ζ, p)`:

* `padWeightE`, `padConstE`, `chShiftTargetE`, `chSc2TargetE`, `wtE`: V_S's `padWeight`,
  `padConst`, `chShiftTarget0`, `chSc2Target0`, `wt` (`LvmDecideV0`) over `E`, with `eqAt` for the
  verifier's `eq` tables;
* **`padSum_eq`**: `Σ_{l<8, p<64} ω(l,p)·Pad43(y)[64l + p] = padConst + Σ_{m<4, q<64} W(m,q)·y[64m + q]`;
* `linkDelta`, `constDelta`: the zero-test tables; **`linkBits_of_zero`**, **`const_of_zero`**: they
  vanish exactly on the relation; **`linkZero_iff`**: at full length the link table's extension is
  `target + F(0)`, the shift sumcheck's claim (`shiftSum`);
* the sumcheck families `Fsh` (shift, `h` rounds) and `G2` (the `Y` lane, 2 rounds) and their ends
  (`Fsh_end`, `G2_nil`, `G2_end`) in the slices at `(ρ', λ, 0, 0, 0)` and `(ρ', μ, sel(ys/4))`.
-/

set_option autoImplicit false

namespace Lvm.KG

open LeanVM.Parameters LeanVM.Protocol.Verifier LeanVM.Protocol.KeccakGkr
open LeanVM.Protocol.EndToEnd LeanVM.Protocol.EndToEnd.Front LeanVM.Protocol.EndToEnd.Complete
open LeanVM.Protocol.Ring Finset

/-! ## V_S's link formulas over `E` -/

/-- `ρ`, `λ`, `ζ` from the link's `h + 9` challenges. -/
def chRho (h : ℕ) (chal : List E) : List E := chal.take h
/-- The lane challenges `λ` (3). -/
def chLam (h : ℕ) (chal : List E) : List E := (chal.drop h).take 3
/-- The bit challenges `ζ` (6). -/
def chZeta (h : ℕ) (chal : List E) : List E := chal.drop (h + 3)

/-- `ω(l, p) = eq(λ, l)·eq(ζ, p)`. -/
def omegaE (lam zeta : List E) (l p : ℕ) : E := eqAt lam l * eqAt zeta p

/-- The weight of bit `q` of `Y` lane `m` through `Pad43` (V_S's `padWeight`). -/
def padWeightE (lam zeta : List E) (m q : ℕ) : E :=
  if q ≤ 55 then omegaE lam zeta m (q + 8) else omegaE lam zeta (m + 1) (q - 56)

/-- The constant bits of `Pad43`'s lanes `0 … 7` (V_S's `padConst`): `0x43`, and `0x01` at bit 8
of lane 4. -/
def padConstE (lam zeta : List E) : E :=
  (∑ p ∈ range 8, if (0x43 : ℕ).testBit p then omegaE lam zeta 0 p else 0) + omegaE lam zeta 4 8

/-- The shift sumcheck's claim `C·(1 + eq(ρ, 1^h))` (V_S's `chShiftTarget0`). -/
def chShiftTargetE (h : ℕ) (chal : List E) : E :=
  padConstE (chLam h chal) (chZeta h chal) * (1 + prodE (chRho h chal))

/-- The two-round sumcheck's claim `f₁ + S(ρ, ρ')·Σ_p eq(ζ, p) inS_p` (V_S's `chSc2Target0`). -/
def chSc2TargetE (h : ℕ) (chal : List E) (shift : List E × E) (inS : List E) : E :=
  shift.2 + shiftEvalE (chRho h chal) shift.1 *
    ∑ p ∈ range 64, eqAt (chZeta h chal) p * inS.getD p 0

/-- `W̃(μ, q) = Σ_m eq(μ, m)·W(m, q)` (V_S's `wt`). -/
def wtE (lam zeta mu : List E) (q : ℕ) : E := ∑ m ∈ range 4, eqAt mu m * padWeightE lam zeta m q

/-- The point of the `in` slices: `(ρ', λ, 0, 0, 0)` (slots `0 … 7`). -/
def chInPt (h : ℕ) (chal : List E) (shift : List E × E) : List E :=
  shift.1 ++ chLam h chal ++ [0, 0, 0]

/-- The point of the `Y` slices: `(ρ', μ, sel(ys / 4))` (slots `ys … ys + 3`). -/
def chYPt (ys : ℕ) (shift sc2 : List E × E) : List E := shift.1 ++ sc2.1 ++ selectorPoint (ys / 4) 4

/-! ## The `Pad43` weights -/

theorem bitE_add_eq_zero {a b : Bool} (h : bitE a + bitE b = 0) : a = b := by
  cases a <;> cases b <;> simp_all [bitE]

theorem bitE_add_self (a : Bool) : bitE a + bitE a = 0 := CharTwo.add_self_eq_zero _

/-- **The `Pad43` weights**: the link's lanes `0 … 7` weighted by `ω` are the constant bits plus
the `Y` bits through `padWeightE`. -/
theorem padSum_eq (lam zeta : List E) (y : ℕ → Bool) :
    ∑ l ∈ range 8, ∑ p ∈ range 64, omegaE lam zeta l p * bitE (pad43Bit y (64 * l + p)) =
      padConstE lam zeta +
        ∑ m ∈ range 4, ∑ q ∈ range 64, padWeightE lam zeta m q * bitE (y (64 * m + q)) := by
  let F : ℕ → E := fun j ↦ omegaE lam zeta (j / 64) (j % 64) * bitE (pad43Bit y j)
  have hL : ∑ l ∈ range 8, ∑ p ∈ range 64, omegaE lam zeta l p * bitE (pad43Bit y (64 * l + p)) =
      ∑ j ∈ range (8 * 64), F j := by
    rw [sum_range_mul]
    refine Finset.sum_congr rfl fun l _ ↦ Finset.sum_congr rfl fun p hp ↦ ?_
    have hp' := Finset.mem_range.1 hp
    simp only [F, Nat.mul_add_div (by decide : 0 < 64), Nat.div_eq_of_lt hp', Nat.add_zero,
      Nat.mul_add_mod, Nat.mod_eq_of_lt hp']
  rw [hL, show 8 * 64 = 8 + (4 * 64 + 248) from rfl, Finset.sum_range_add, Finset.sum_range_add]
  have h1 : ∑ j ∈ range 8, F j =
      ∑ p ∈ range 8, if (0x43 : ℕ).testBit p then omegaE lam zeta 0 p else 0 := by
    refine Finset.sum_congr rfl fun p hp ↦ ?_
    have hp' := Finset.mem_range.1 hp
    have hp64 : p < 64 := Nat.lt_of_lt_of_le hp' (by decide)
    simp only [F, pad43Bit, if_pos hp', Nat.div_eq_of_lt hp64, Nat.mod_eq_of_lt hp64]
    cases (0x43 : ℕ).testBit p <;> simp [bitE]
  have h2 : ∑ j ∈ range (4 * 64), F (8 + j) =
      ∑ m ∈ range 4, ∑ q ∈ range 64, padWeightE lam zeta m q * bitE (y (64 * m + q)) := by
    rw [sum_range_mul]
    refine Finset.sum_congr rfl fun m hm ↦ Finset.sum_congr rfl fun q hq ↦ ?_
    have hm' := Finset.mem_range.1 hm
    have hq' := Finset.mem_range.1 hq
    simp only [F, pad43Bit, if_neg (Nat.not_lt.2 (Nat.le_add_right 8 _)),
      if_pos (show 8 + (64 * m + q) < 264 by omega), Nat.add_sub_cancel_left, padWeightE]
    split_ifs with h55
    · have hq8 : q + 8 < 64 := Nat.lt_of_le_of_lt (Nat.add_le_add_right h55 8) (by decide)
      rw [show 8 + (64 * m + q) = 64 * m + (q + 8) by ring, Nat.mul_add_div (by decide : 0 < 64),
        Nat.div_eq_of_lt hq8, Nat.add_zero, Nat.mul_add_mod, Nat.mod_eq_of_lt hq8]
    · obtain ⟨t, rfl⟩ : ∃ t, q = 56 + t := ⟨q - 56, (Nat.add_sub_cancel' (Nat.lt_of_not_le h55)).symm⟩
      have ht : t < 64 := Nat.lt_of_le_of_lt (Nat.le_add_left t 56) hq'
      rw [show 8 + (64 * m + (56 + t)) = 64 * (m + 1) + t by ring, Nat.mul_add_div (by decide : 0 < 64),
        Nat.div_eq_of_lt ht, Nat.add_zero, Nat.mul_add_mod, Nat.mod_eq_of_lt ht, Nat.add_sub_cancel_left]
  have h3 : ∑ j ∈ range 248, F (8 + (4 * 64 + j)) = omegaE lam zeta 4 8 := by
    rw [Finset.sum_range_succ']
    have hz : ∑ j ∈ range 247, F (8 + (4 * 64 + (j + 1))) = 0 :=
      Finset.sum_eq_zero fun j hj ↦ by
        have hj' := Finset.mem_range.1 hj
        simp only [F, pad43Bit, if_neg (show ¬ 8 + (4 * 64 + (j + 1)) < 8 by omega),
          if_neg (show ¬ 8 + (4 * 64 + (j + 1)) < 264 by omega)]
        have : ¬ (8 + (4 * 64 + (j + 1)) = 264 ∨ 8 + (4 * 64 + (j + 1)) = 1087) := by omega
        rw [decide_eq_false this, bitE_false, mul_zero]
    rw [hz, zero_add]
    simp [F, pad43Bit, bitE]
  rw [h1, h2, h3, padConstE]
  ring

/-! ## The zero-test tables -/

variable (h ys : ℕ) (col : ℕ → K)

/-- The link's mismatch at row `x`, lane `l < 8`, bit `p` (rows `x + 1 < 2^h`). -/
def linkD (x l p : ℕ) : E :=
  if x + 1 < 2 ^ h then
    bitE ((col (x + 1 + 2 ^ h * l)).toBitVec.getLsbD p) + bitE (pad43Bit (yBits h ys col x) (64 * l + p))
  else 0

/-- The link's zero-test table on `h + 9` bits: row low, then lane (3 bits), then bit (6). -/
def linkDelta (w : ℕ) : E := linkD h ys col (w % 2 ^ h) (w / 2 ^ h % 8) (w / 2 ^ h / 8)

/-- The constant lanes' zero-test table on `h + 5` bits: row low, then lane. -/
def constDelta (w : ℕ) : E :=
  if 8 ≤ w / 2 ^ h ∧ w / 2 ^ h < 25 then
    ofK (col (w % 2 ^ h + 2 ^ h * (w / 2 ^ h))) + ofK (K.ofLane (padConstLane (w / 2 ^ h)))
  else 0

theorem idx_div {x t : ℕ} (hx : x < 2 ^ h) : (x + 2 ^ h * t) / 2 ^ h = t := by
  rw [Nat.add_mul_div_left _ _ (Nat.two_pow_pos h), Nat.div_eq_of_lt hx, zero_add]

theorem idx_mod {x t : ℕ} (hx : x < 2 ^ h) : (x + 2 ^ h * t) % 2 ^ h = x := by
  rw [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hx]

/-- **A vanishing link table is the link** on lanes `0 … 7`. -/
theorem linkBits_of_zero (hz : ZeroOn (linkDelta h ys col) [] (h + 9)) : LinkBits h ys col := by
  rw [zeroOn_nil] at hz
  intro x hx l hl p hp
  have hx' : x < 2 ^ h := Nat.lt_of_succ_lt hx
  have := hz (x + 2 ^ h * (l + 8 * p)) (by
    rw [show 2 ^ (h + 9) = 2 ^ h * 512 by rw [pow_add]; rfl]
    calc x + 2 ^ h * (l + 8 * p) < 2 ^ h * (l + 8 * p) + 2 ^ h := by
          rw [Nat.add_comm]; exact Nat.add_lt_add_left hx' _
      _ = 2 ^ h * (l + 8 * p + 1) := (Nat.mul_succ _ _).symm
      _ ≤ 2 ^ h * 512 := Nat.mul_le_mul_left _ (by omega))
  have e1 : (l + 8 * p) % 8 = l := by rw [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hl]
  have e2 : (l + 8 * p) / 8 = p := by
    rw [Nat.add_mul_div_left _ _ (by decide), Nat.div_eq_of_lt hl, Nat.zero_add]
  simp only [linkDelta, idx_div h hx', idx_mod h hx', e1, e2, linkD, if_pos hx] at this
  exact bitE_add_eq_zero this

theorem ofK_injective' : Function.Injective (ofK : K → E) := (algebraMap K E).injective

/-- **A vanishing constant table is the constant lanes.** -/
theorem const_of_zero (hz : ZeroOn (constDelta h col) [] (h + 5)) : ConstLanes h col := by
  rw [zeroOn_nil] at hz
  intro x hx t h8 h25
  have := hz (x + 2 ^ h * t) (by
    rw [show 2 ^ (h + 5) = 2 ^ h * 32 by rw [pow_add]; rfl]
    calc x + 2 ^ h * t < 2 ^ h * t + 2 ^ h := by
          rw [Nat.add_comm]; exact Nat.add_lt_add_left hx _
      _ = 2 ^ h * (t + 1) := (Nat.mul_succ _ _).symm
      _ ≤ 2 ^ h * 32 := Nat.mul_le_mul_left _ (Nat.le_trans h25 (by decide)))
  simp only [constDelta, idx_div h hx, idx_mod h hx, h8, h25, and_self, if_true] at this
  exact ofK_injective' (add_eq_zero_iff_E.1 this)

/-- The constant lanes' claims at `ρ'`: `in_t(ρ') = c_t` for `t = 8 … 24` (V_S's 17 word claims). -/
def ConstClaims (pt : List E) : Prop :=
  ∀ t, 8 ≤ t → t < 25 → stepMle h pt (fun x ↦ col (x + 2 ^ h * t)) = ofK (K.ofLane (padConstLane t))

/-- The constant claims make the constant table's extension vanish at `ρ'`. -/
theorem constZero_of_claims {pt : List E} (hpt : pt.length = h) (hc : ConstClaims h col pt) :
    ZeroOn (constDelta h col) pt (h + 5) := by
  intro t ht
  unfold foldT
  rw [hpt]
  have e : ∀ x ∈ range (2 ^ h), constDelta h col (x + 2 ^ h * t) =
      if 8 ≤ t ∧ t < 25 then ofK (col (x + 2 ^ h * t)) + ofK (K.ofLane (padConstLane t)) else 0 :=
    fun x hx ↦ by simp only [constDelta, idx_div h (Finset.mem_range.1 hx),
      idx_mod h (Finset.mem_range.1 hx)]
  rw [Finset.sum_congr rfl fun x hx ↦ by rw [e x hx]]
  split_ifs with ht'
  · have h1 : ∑ x ∈ range (2 ^ h), eqAt pt x * ofK (col (x + 2 ^ h * t)) =
        ofK (K.ofLane (padConstLane t)) := hc t ht'.1 ht'.2
    have h2 : ∑ x ∈ range (2 ^ h), eqAt pt x * ofK (K.ofLane (padConstLane t)) =
        ofK (K.ofLane (padConstLane t)) := by
      rw [← Finset.sum_mul, ← hpt, sum_eqAt, one_mul]
    rw [Finset.sum_congr rfl fun x _ ↦ mul_add _ _ _, Finset.sum_add_distrib, h1, h2]
    exact CharTwo.add_self_eq_zero _
  · simp

/-! ## The shift sumcheck -/

variable (lam zeta : List E)

/-- `A(k) = Σ_{l<8, p<64} ω(l,p)·bit_p(in_k[l])`. -/
def linkA (k : ℕ) : E :=
  ∑ l ∈ range 8, ∑ p ∈ range 64, omegaE lam zeta l p * bitE ((col (k + 2 ^ h * l)).toBitVec.getLsbD p)

/-- `B(k) = Σ_{m<4, q<64} W(m,q)·bit_q(Y_k[m])`. -/
def linkB (k : ℕ) : E :=
  ∑ m ∈ range 4, ∑ q ∈ range 64, padWeightE lam zeta m q * bitE (yBits h ys col k (64 * m + q))

/-- The shift sumcheck's family: `Σ_k S(ρ, k)·A(k) + Eq'(ρ, k)·B(k)` over the rows not bound. -/
noncomputable def Fsh (rho : List E) (acc : List E) : E :=
  cubeSum (fun pt ↦ (∑ k ∈ range (2 ^ h), eqAt pt k * shiftK rho k) *
      (∑ k ∈ range (2 ^ h), eqAt pt k * linkA h col lam zeta k) +
    (∑ k ∈ range (2 ^ h), eqAt pt k * maskK rho k) *
      (∑ k ∈ range (2 ^ h), eqAt pt k * linkB h ys col lam zeta k)) h acc

theorem Fsh_plain {β : Type} (cq : β → ℕ → K) (rho : List E) :
    PlainFamily (fun q acc ↦ Fsh h ys (cq q) lam zeta rho acc) 2 h :=
  cube_plainFamily _ h fun _ pre post ↦ PolyLE.add (polyLE_mle_mul _ _ _ _ pre post)
    (polyLE_mle_mul _ _ _ _ pre post)

/-- The family before the rounds: the sum over the rows. -/
theorem Fsh_nil (rho : List E) :
    Fsh h ys col lam zeta rho [] = ∑ k ∈ range (2 ^ h),
      (shiftK rho k * linkA h col lam zeta k + maskK rho k * linkB h ys col lam zeta k) := by
  rw [Fsh, cubeSum_nil]
  refine Finset.sum_congr rfl fun u hu ↦ ?_
  have hu' := Finset.mem_range.1 hu
  rw [sum_eqAt_bitsE hu', sum_eqAt_bitsE hu', sum_eqAt_bitsE hu', sum_eqAt_bitsE hu']

/-- Three nested sums in the other order. -/
theorem sum_comm3 {a b c : ℕ} (g : ℕ → ℕ → ℕ → E) :
    ∑ x ∈ range a, ∑ l ∈ range b, ∑ p ∈ range c, g x l p =
      ∑ p ∈ range c, ∑ l ∈ range b, ∑ x ∈ range a, g x l p := by
  rw [Finset.sum_congr rfl fun x _ ↦ Finset.sum_comm, Finset.sum_comm,
    Finset.sum_congr rfl fun p _ ↦ Finset.sum_comm]

/-- The link table's extension at `(ρ, λ, ζ)`, regrouped: row, then lane, then bit. -/
theorem linkDelta_sum {rho : List E} (hr : rho.length = h) (hl : lam.length = 3)
    (hz : zeta.length = 6) :
    ∑ w ∈ range (2 ^ (h + 9)), eqAt (rho ++ lam ++ zeta) w * linkDelta h ys col w =
      ∑ x ∈ range (2 ^ h), eqAt rho x *
        ∑ l ∈ range 8, ∑ p ∈ range 64, omegaE lam zeta l p * linkD h ys col x l p := by
  have e1 : ∑ w ∈ range (2 ^ (h + 9)), eqAt (rho ++ lam ++ zeta) w * linkDelta h ys col w =
      ∑ o ∈ range (2 ^ (3 + zeta.length)), eqAt (lam ++ zeta) o *
        ∑ x ∈ range (2 ^ h), eqAt rho x * linkD h ys col x (o % 8) (o / 8) := by
    have := col_split (s := lam ++ zeta) hr (linkDelta h ys col)
    rw [show (lam ++ zeta).length = 9 by simp [hl, hz], ← List.append_assoc] at this
    rw [this, hz]
    refine Finset.sum_congr rfl fun o _ ↦ congrArg _ (Finset.sum_congr rfl fun x hx ↦ ?_)
    rw [linkDelta, idx_div h (Finset.mem_range.1 hx), idx_mod h (Finset.mem_range.1 hx)]
  have e2 := col_split (h := 3) (a := lam) (s := zeta) hl
    (fun o ↦ ∑ x ∈ range (2 ^ h), eqAt rho x * linkD h ys col x (o % 8) (o / 8))
  rw [e1, e2, hz]
  simp only [Finset.mul_sum]
  rw [sum_comm3]
  refine Finset.sum_congr rfl fun x _ ↦ Finset.sum_congr rfl fun l hl' ↦
    Finset.sum_congr rfl fun p _ ↦ ?_
  have hl'' := Finset.mem_range.1 hl'
  rw [show (l + 2 ^ 3 * p) % 8 = l from
      (Nat.add_mul_mod_self_left l 8 p).trans (Nat.mod_eq_of_lt hl''),
    show (l + 2 ^ 3 * p) / 8 = p from (Nat.add_mul_div_left l p (by decide : 0 < 8)).trans
      (by rw [Nat.div_eq_of_lt hl'', Nat.zero_add]), omegaE]
  ring

/-- **The link table's extension is the shift sumcheck's claim plus its target.** -/
theorem linkDelta_eq {rho : List E} (hr : rho.length = h) (hl : lam.length = 3)
    (hz : zeta.length = 6) :
    ∑ w ∈ range (2 ^ (h + 9)), eqAt (rho ++ lam ++ zeta) w * linkDelta h ys col w =
      Fsh h ys col lam zeta rho [] + padConstE lam zeta * (1 + prodE rho) := by
  rw [linkDelta_sum h ys col lam zeta hr hl hz, Fsh_nil, ← sum_maskK_one, hr]
  have hrow : ∀ x ∈ range (2 ^ h), eqAt rho x *
      ∑ l ∈ range 8, ∑ p ∈ range 64, omegaE lam zeta l p * linkD h ys col x l p =
      maskK rho x * (linkA h col lam zeta (x + 1) + linkB h ys col lam zeta x +
        padConstE lam zeta) := by
    intro x _
    unfold maskK
    rw [hr]
    split_ifs with hx
    · simp only [linkD, if_pos hx, mul_add, Finset.sum_add_distrib]
      rw [padSum_eq, linkA, linkB]
      simp only [yBits]
      ring
    · simp [linkD, hx]
  rw [Finset.sum_congr rfl hrow, Finset.mul_sum, ← Finset.sum_add_distrib]
  -- the shifted `A` terms: row `x + 1` under `maskK` is row `k` under `shiftK`
  have hp := Nat.two_pow_pos h
  obtain ⟨M, hM⟩ : ∃ M, 2 ^ h = M + 1 := ⟨2 ^ h - 1, by omega⟩
  have hA : ∑ x ∈ range (2 ^ h), maskK rho x * linkA h col lam zeta (x + 1) =
      ∑ k ∈ range (2 ^ h), shiftK rho k * linkA h col lam zeta k := by
    rw [hM, Finset.sum_range_succ, Finset.sum_range_succ']
    simp only [maskK, hr, hM, show ¬ (M + 1 < M + 1) by omega, ite_false, zero_mul, add_zero,
      shiftK, show ¬ (1 ≤ 0) by omega, Nat.le_add_left, ite_true, Nat.add_sub_cancel]
    refine Finset.sum_congr rfl fun x hx ↦ ?_
    rw [if_pos (by have := Finset.mem_range.1 hx; omega)]
  have : ∀ x ∈ range (2 ^ h), maskK rho x * (linkA h col lam zeta (x + 1) +
      linkB h ys col lam zeta x + padConstE lam zeta) =
      maskK rho x * linkA h col lam zeta (x + 1) + (maskK rho x * linkB h ys col lam zeta x +
        padConstE lam zeta * maskK rho x) := fun x _ ↦ by ring
  rw [Finset.sum_congr rfl this, Finset.sum_add_distrib, hA, Finset.sum_add_distrib,
    Finset.sum_add_distrib, Finset.sum_add_distrib]
  ring

/-- **The shift sumcheck's claim at `(ρ, λ, ζ)` is the zero test**: if the claim holds, the link
table's extension vanishes there. -/
theorem zero_of_shiftClaim {chal : List E} (hc : chal.length = h + 9)
    (H : chShiftTargetE h chal = Fsh h ys col (chLam h chal) (chZeta h chal) (chRho h chal) []) :
    ZeroOn (linkDelta h ys col) chal (h + 9) := by
  have hsplit : chal = chRho h chal ++ chLam h chal ++ chZeta h chal := by
    simp only [chRho, chLam, chZeta, List.append_assoc, List.take_append_drop,
      ← List.drop_drop]
  have hr : (chRho h chal).length = h := by simp [chRho, hc]
  have hl : (chLam h chal).length = 3 := by simp [chLam, hc]
  have hz : (chZeta h chal).length = 6 := by simp [chZeta, hc]
  rw [zeroOn_full _ hc]
  conv_lhs => rw [hsplit]
  rw [linkDelta_eq h ys col _ _ hr hl hz, ← H, chShiftTargetE]
  exact CharTwo.add_self_eq_zero _

/-! ## The ends of the two sumchecks -/

/-- Slice `q` of `Y` lane `m` at the rows' point `pt`. -/
def ysl (pt : List E) (m q : ℕ) : E :=
  ∑ x ∈ range (2 ^ h), eqAt pt x * bitE ((col (x + 2 ^ h * (ys + m))).toBitVec.getLsbD q)

theorem eqAt_000 (t : ℕ) (ht : t < 8) : eqAt [0, 0, 0] t = if t = 0 then 1 else 0 := by
  have := eqAt_bitsE_lt (m := 3) (z := 0) (w := t) (by norm_num) (by simpa using ht)
  simpa [bitsE] using this

/-- **The `in` slices at `(ρ', λ, 0, 0, 0)`**: the lanes `0 … 7` weighted by `eq(λ, ·)`. -/
theorem sliceExt_in {pt : List E} (hpt : pt.length = h) (hl : lam.length = 3) (p : ℕ) :
    sliceExt h col (pt ++ lam ++ [0, 0, 0]) p = ∑ l ∈ range 8, eqAt lam l *
      ∑ x ∈ range (2 ^ h), eqAt pt x * bitE ((col (x + 2 ^ h * l)).toBitVec.getLsbD p) := by
  unfold sliceExt
  have := col_split (s := lam ++ ([0, 0, 0] : List E)) hpt
    (fun n ↦ bitE ((col n).toBitVec.getLsbD p))
  rw [show (lam ++ ([0, 0, 0] : List E)).length = 6 by simp [hl], ← List.append_assoc] at this
  rw [this]
  have e2 := col_split (h := 3) (a := lam) (s := ([0, 0, 0] : List E)) hl
    (fun o ↦ ∑ x ∈ range (2 ^ h), eqAt pt x * bitE ((col (x + 2 ^ h * o)).toBitVec.getLsbD p))
  rw [show ([0, 0, 0] : List E).length = 3 from rfl] at e2
  rw [show (6 : ℕ) = 3 + 3 from rfl, e2, Finset.sum_eq_single 0]
  · simp [eqAt_000]
  · intro t ht h0
    rw [eqAt_000 t (by simpa using ht), if_neg h0, zero_mul]
  · simp

/-- **The `Y` slices at `(ρ', μ, sel(ys / 4))`**: the lanes `ys … ys + 3` weighted by `eq(μ, ·)`. -/
theorem sliceExt_y {pt mu : List E} (hpt : pt.length = h) (hmu : mu.length = 2)
    (hys : ys % 4 = 0) (hys' : ys / 4 < 16) (q : ℕ) :
    sliceExt h col (pt ++ mu ++ selectorPoint (ys / 4) 4) q =
      ∑ m ∈ range 4, eqAt mu m * ysl h ys col pt m q := by
  unfold sliceExt
  have hsel : (selectorPoint (ys / 4) 4) = bitsE (ys / 4) 4 := by
    rw [selectorPoint_eq_boolPoint]
    clear hys hys'
    generalize ys / 4 = z
    induction (4 : ℕ) generalizing z with
    | zero => rfl
    | succ n ih =>
      rw [boolPoint_succ, bitsE, ih, Nat.testBit_zero]
      congr 1
      rcases Nat.mod_two_eq_zero_or_one z with h0 | h1 <;> simp [*]
  have := col_split (s := mu ++ selectorPoint (ys / 4) 4) hpt
    (fun n ↦ bitE ((col n).toBitVec.getLsbD q))
  rw [show (mu ++ selectorPoint (ys / 4) 4).length = 6 by simp [hmu, selectorPoint],
    ← List.append_assoc] at this
  rw [this]
  have e2 := col_split (h := 2) (a := mu) (s := selectorPoint (ys / 4) 4) hmu
    (fun o ↦ ∑ x ∈ range (2 ^ h), eqAt pt x * bitE ((col (x + 2 ^ h * o)).toBitVec.getLsbD q))
  rw [show (selectorPoint (ys / 4) 4).length = 4 by simp [selectorPoint]] at e2
  rw [show (6 : ℕ) = 2 + 4 from rfl, e2, hsel, sum_eqAt_bitsE hys']
  refine Finset.sum_congr rfl fun m hm ↦ ?_
  have hm' := Finset.mem_range.1 hm
  rw [ysl, show m + 2 ^ 2 * (ys / 4) = ys + m by omega]

/-- `B` at the rows' point: the `Y` slices weighted by `W`. -/
theorem linkB_mle (pt : List E) :
    ∑ k ∈ range (2 ^ h), eqAt pt k * linkB h ys col lam zeta k =
      ∑ m ∈ range 4, ∑ q ∈ range 64, padWeightE lam zeta m q * ysl h ys col pt m q := by
  simp only [linkB, ysl, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun m hm ↦ ?_
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun q hq ↦ Finset.sum_congr rfl fun x _ ↦ ?_
  · have := Finset.mem_range.1 hq
    simp only [yBits, show (64 * m + q) / 64 = m by omega, show (64 * m + q) % 64 = q by omega]
    ring

/-- `A` at the rows' point: the `in` slices weighted by `eq(ζ, ·)`. -/
theorem linkA_mle {pt : List E} (hpt : pt.length = h) (hl : lam.length = 3) :
    ∑ k ∈ range (2 ^ h), eqAt pt k * linkA h col lam zeta k =
      ∑ p ∈ range 64, eqAt zeta p * sliceExt h col (pt ++ lam ++ [0, 0, 0]) p := by
  simp only [sliceExt_in h col lam hpt hl, linkA, omegaE, Finset.mul_sum]
  rw [sum_comm3]
  refine Finset.sum_congr rfl fun p _ ↦ Finset.sum_congr rfl fun l _ ↦
    Finset.sum_congr rfl fun x _ ↦ by ring

/-- **The shift sumcheck's end** at `ρ'`. -/
theorem Fsh_end {rho pt : List E} (hr : rho.length = h) (hpt : pt.length = h)
    (hl : lam.length = 3) :
    Fsh h ys col lam zeta rho pt =
      shiftEvalE rho pt * ∑ p ∈ range 64, eqAt zeta p * sliceExt h col (pt ++ lam ++ [0, 0, 0]) p +
        eqMaskedE rho pt *
          ∑ m ∈ range 4, ∑ q ∈ range 64, padWeightE lam zeta m q * ysl h ys col pt m q := by
  rw [Fsh, cubeSum_full _ hpt, ← hr, sum_shiftK rho pt (by rw [hr, hpt]),
    sum_maskK rho pt (by rw [hr, hpt]), hr, linkA_mle h col lam zeta hpt hl, linkB_mle]

/-- The `Y` lane sumcheck's family (2 rounds over the lane `m` of `Y`). -/
noncomputable def G2 (rho pt : List E) (acc : List E) : E :=
  cubeSum (fun mpt ↦ eqMaskedE rho pt * ∑ q ∈ range 64,
    (∑ m ∈ range 4, eqAt mpt m * padWeightE lam zeta m q) *
      (∑ m ∈ range 4, eqAt mpt m * ysl h ys col pt m q)) 2 acc

theorem G2_plain {β : Type} (cq : β → ℕ → K) (rho pt : List E) :
    PlainFamily (fun q acc ↦ G2 h ys (cq q) lam zeta rho pt acc) 2 2 :=
  cube_plainFamily _ 2 fun _ pre post ↦ PolyLE.const_mul (PolyLE.sum _ fun _ _ ↦
    polyLE_mle_mul _ _ _ _ pre post) _

theorem G2_nil (rho pt : List E) :
    G2 h ys col lam zeta rho pt [] = eqMaskedE rho pt *
      ∑ m ∈ range 4, ∑ q ∈ range 64, padWeightE lam zeta m q * ysl h ys col pt m q := by
  rw [G2, cubeSum_nil, ← Finset.mul_sum]
  refine congrArg _ ?_
  rw [show (2 : ℕ) ^ 2 = 4 from rfl]
  refine Finset.sum_congr rfl fun m hm ↦ Finset.sum_congr rfl fun q _ ↦ ?_
  have hm' : m < 2 ^ 2 := Finset.mem_range.1 hm
  have e1 := sum_eqAt_bitsE hm' (fun m' ↦ padWeightE lam zeta m' q)
  have e2 := sum_eqAt_bitsE hm' (fun m' ↦ ysl h ys col pt m' q)
  rw [show (2 : ℕ) ^ 2 = 4 from rfl] at e1 e2
  rw [e1, e2]

theorem G2_end (rho pt : List E) {mu : List E} (hmu : mu.length = 2) :
    G2 h ys col lam zeta rho pt mu = eqMaskedE rho pt * ∑ q ∈ range 64,
      wtE lam zeta mu q * ∑ m ∈ range 4, eqAt mu m * ysl h ys col pt m q := by
  rw [G2, cubeSum_full _ hmu]
  rfl

end Lvm.KG
end
-- ===== end of `LvmChainTableLinkMath` =====

-- ===== merged from `LvmChainTableLink` (GOLF module merge: `LvmChainTableLink.lean` is now a stub importing `LvmSpongeTableLink`) =====
section
-- New for lvm (WP-8): the CH link as a doom specification (BLUEPRINT §4.1, §7.2 `linkSpec`). The
-- sumcheck with a riding zero test (`sumcheckZSpec`) is leanVM's `sumcheckSpec` (`LvmKeccakRounds`)
-- with the zero test of `zeroOn_escape` carried along the rounds.

/-!
# The `CH` link

`chLinkProg` is V_S's phase 5 (`LvmDecide`, with `M3.v0`'s `chShiftTarget0`, `chSc2Target0`,
`chLink0`) on leanVM's DSL, read for read and sample for sample:

```
chal ← h + 9 challenges (ρ, λ, ζ);  shift ← h plain rounds of degree 2 on chShiftTarget;
inS ← 64 scalars;  ringIn ← ringSwitch (ρ', λ, 0, 0, 0) inS;
sc2 ← 2 plain rounds on chSc2Target;  yS ← 64 scalars;  ringY ← ringSwitch (ρ', μ, sel(ys/4)) yS;
5 challenges (unused);  require sc2.2 = Eq'(ρ, ρ')·Σ_q W̃(μ, q)·yS_q
```

**`chLinkSpec`**: from doom of `LinkBits ∧ ConstLanes ∧ R` (the link `in_{x+1} = Pad43(Y_x)` on every
row but the last, A9) to doom of the two ring claims (`RingColTrue`), the 17 constant-lane claims
at `ρ'` (`ConstClaims`) and `R`. Groups: `ρλζ`, `(h + 9)·L₀/|E|` (lead); each shift round
`L₀·2/|E|`, the constant lanes' zero test riding on the same challenges; each ring switch
`6·L₀/|E|`; each `Y`-lane round `L₀·2/|E|`.
-/

set_option autoImplicit false

namespace Lvm.KG

open LeanVM.Parameters LeanVM.Protocol.Compile LeanVM.Protocol.Verifier LeanVM.Protocol.KeccakGkr
open LeanVM.Protocol.EndToEnd LeanVM.Protocol.EndToEnd.Front LeanVM.Protocol.EndToEnd.Complete Finset
open scoped ENNReal

/-! ## The program -/

/-- What the `CH` link returns. -/
structure ChLinkOut where
  /-- `ρ ‖ λ ‖ ζ`. -/
  chal : List E
  /-- The shift sumcheck's point `ρ'` and final claim. -/
  shift : List E × E
  /-- The 64 `in` slices at `(ρ', λ, 0, 0, 0)`. -/
  inS : List E
  /-- Their ring switch. -/
  ringIn : E × (List E → E)
  /-- The `Y`-lane sumcheck's point `μ` and final claim. -/
  sc2 : List E × E
  /-- The 64 `Y` slices at `(ρ', μ, sel(ys / 4))`. -/
  yS : List E
  /-- Their ring switch. -/
  ringY : E × (List E → E)

/-- **The `CH` link** (V_S phase 5, `M3.v0`). -/
def chLinkProg (h ys : ℕ) : VerifierProgram ChLinkOut :=
  VerifierProgram.sampleChallenges (h + 9) >>= fun chal ↦
  sumcheck (chShiftTargetE h chal) 3 (List.replicate h none) >>= fun shift ↦
  VerifierProgram.readScalars 64 >>= fun inS ↦
  ringSwitch (chInPt h chal shift) inS >>= fun ringIn ↦
  sumcheck (chSc2TargetE h chal shift inS) 3 (List.replicate 2 none) >>= fun sc2 ↦
  VerifierProgram.readScalars 64 >>= fun yS ↦
  ringSwitch (chYPt ys shift sc2) yS >>= fun ringY ↦
  VerifierProgram.sampleChallenges 5 >>= fun _ ↦
  VerifierProgram.require (sc2.2 = eqMaskedE (chRho h chal) shift.1 *
    ∑ q ∈ range 64, wtE (chLam h chal) (chZeta h chal) sc2.1 q * yS.getD q 0) >>= fun _ ↦
  VerifierProgram.ret ⟨chal, shift, inS, ringIn, sc2, yS, ringY⟩

/-- Characteristic two moves a summand across. -/
theorem char2_move {a b c : E} (h : a + b = c) : a = b + c := by
  linear_combination h - b * CharTwo.two_eq_zero (R := E)

/-! ## A sumcheck with a riding zero test -/

variable {β : Type} {C : List Ev → Set β}

/-- The escape of a round's challenge when a zero test rides on it. -/
theorem zplain_escape {F : β → List E → E} {d N : ℕ} (hF : PlainFamily F d N) (hd : 1 ≤ d)
    (κ : β → ℕ → E) (nZ : ℕ) (R : β → Prop) {acc msg : List E} (hacc : acc.length < N)
    (haccZ : acc.length < nZ) (hdm : msg.length - 1 ≤ d) (q : β)
    (hq : ¬ ((∀ x, polyEval msg x = F q (acc ++ [x])) ∧ ZeroOn (κ q) acc nZ ∧ R q)) :
    avgE (fun c ↦ indE (polyEval msg c = F q (acc ++ [c]) ∧ ZeroOn (κ q) (acc ++ [c]) nZ ∧ R q)) ≤
      errE d := by
  by_cases hR : R q
  swap
  · exact (avgE_mono fun c ↦ indE_mono (q := False) fun h ↦ hR h.2.2).trans
      ((avgE_le_of_le fun c ↦ (indE_of_not not_false).le).trans zero_le)
  by_cases hZ : ZeroOn (κ q) acc nZ
  · have hm : ¬ ((∀ x, polyEval msg x = F q (acc ++ [x])) ∧ True) := fun h ↦ hq ⟨h.1, hZ, hR⟩
    exact (avgE_mono fun c ↦ indE_mono fun hc ↦ ⟨hc.1, trivial⟩).trans
      (plain_escape hF (fun _ ↦ True) hacc hdm q hm)
  · exact (avgE_mono fun c ↦ indE_mono fun hc ↦ hc.2.1).trans
      ((zeroOn_escape (κ q) haccZ hZ).trans (errE_mono hd))

variable [Finite β] {L₀ : ℕ} {εmax T : ℝ≥0∞}

/-- **Plain sumcheck rounds with a riding zero test** (leanVM's `sumcheckSpec` with
`ZeroOn (κ q) acc nZ` carried): from doom of `claim = F q acc ∧ ZeroOn κ acc ∧ R` to doom of
`final = F q (acc ++ point) ∧ ZeroOn κ (acc ++ point) ∧ R`; each challenge at `L₀·d/|E|`. -/
noncomputable def sumcheckZSpec (hst : Stable C) (hcard : ∀ h, (C h).ncard ≤ L₀)
    (R : β → Prop) (κ : β → ℕ → E) (nZ : ℕ) {F : β → List E → E} {d N : ℕ}
    (hF : PlainFamily F d N) (hd1 : 1 ≤ d) {count : ℕ} (hc : 2 ≤ count) (hcd : count - 1 ≤ d)
    (hT : T ≤ εmax) (he : (L₀ : ℝ≥0∞) * errE d + T ≤ εmax) :
    (n : ℕ) → (acc : List E) → (claim : E) → acc.length + n ≤ N → acc.length + n ≤ nZ →
      Spec (sumcheck claim count (List.replicate n none))
        (Doomed C (fun q ↦ claim = F q acc ∧ ZeroOn (κ q) acc nZ ∧ R q))
        (fun res h ↦ res.1.length = n ∧
          Doomed C (fun q ↦ res.2 = F q (acc ++ res.1) ∧ ZeroOn (κ q) (acc ++ res.1) nZ ∧ R q) h)
        εmax T T
  | 0, acc, claim, _, _ =>
    (Spec.ret (Post := fun (res : List E × E) h ↦ res.1.length = 0 ∧
        Doomed C (fun q ↦ res.2 = F q (acc ++ res.1) ∧ ZeroOn (κ q) (acc ++ res.1) nZ ∧ R q) h)
        ([], claim)).mono
      (fun _ h ↦ ⟨rfl, by simpa using h⟩) (fun _ _ h ↦ h) le_rfl le_rfl le_rfl
  | n + 1, acc, claim, hN, hZ => by
    refine ((roundSpec (T := (L₀ : ℝ≥0∞) * errE d + T) hst _ he count hc claim none).mono
      (fun _ h ↦ h) (fun msg h (hm : msg.length = count ∧ _ ∧ _) ↦ hm) le_rfl zero_le
      le_rfl).bind' fun msg ↦ ?_
    by_cases hm : msg.length = count
    · refine ((doomSample (εmax := εmax) (T := T) hst hcard
        (fun q ↦ (∀ x, polyEval msg x = F q (acc ++ [x])) ∧ ZeroOn (κ q) acc nZ ∧ R q)
        (fun c q ↦ polyEval msg c = F q (acc ++ [c]) ∧ ZeroOn (κ q) (acc ++ [c]) nZ ∧ R q) (errE d)
        (fun q hq ↦ zplain_escape hF hd1 κ nZ R (by omega) (by omega) (by omega) q hq)).mono
          (fun h (hh : msg.length = count ∧
              RoundSplit none claim (polyEval msg 0) (polyEval msg 1) ∧
              Doomed C (fun q ↦ claim = F q acc ∧ ZeroOn (κ q) acc nZ ∧ R q) h) ↦
            Doomed.mono hh.2.2 fun q ⟨hall, hZq, hR⟩ ↦ ⟨by
              have hs := hh.2.1
              rw [RoundSplit, hall, hall] at hs
              rw [← hs]
              exact (hF q acc (by omega)).2.symm, hZq, hR⟩)
          (fun _ _ h ↦ h) le_rfl le_rfl le_rfl).bind' fun c ↦ ?_
      · refine (sumcheckZSpec hst hcard R κ nZ hF hd1 hc hcd hT he n (acc ++ [c]) (polyEval msg c)
          (by simp; omega) (by simp; omega)).bind' fun res ↦ ?_
        exact (Spec.ret (c :: res.1, res.2)).mono
          (fun _ h ↦ ⟨by simp [h.1], by simpa using h.2⟩) (fun _ _ h ↦ h) le_rfl le_rfl le_rfl
    · exact Spec.dead.mono (fun _ h ↦ hm h.1) (fun _ _ h ↦ h) le_rfl le_rfl le_rfl

/-- Challenges nobody uses keep doom; the lead is the follower's. -/
noncomputable def samplesKeep (hst : Stable C) (hcard : ∀ h, (C h).ncard ≤ L₀) (A : β → Prop)
    (n : ℕ) : Spec (VerifierProgram.sampleChallenges n) (Doomed C A) (fun _ h ↦ Doomed C A h)
      εmax T T :=
  (doomSampleN hst hcard (fun _ q ↦ A q) (fun _ ↦ 0)
      (fun _ q hq ↦ avgE_le_of_le fun _ ↦ (indE_of_not hq).le) n []).mono (fun _ h ↦ h)
    (fun _ _ h ↦ h.2) le_rfl (by simp) le_rfl

/-! ## The specification -/

/-- The postcondition of the `CH` link. -/
def ChLinkPost (h : ℕ) (col : β → ℕ → K) (R : β → Prop) (out : ChLinkOut) (hist : List Ev) :
    Prop :=
  out.shift.1.length = h ∧ Doomed C (fun q ↦ RingColTrue h (col q) out.ringIn ∧
    RingColTrue h (col q) out.ringY ∧ ConstClaims h (col q) out.shift.1 ∧ R q) hist

/-- **The `CH` link**, round by round: from doom of the link (`LinkBits`, `ConstLanes`) and `R` to
doom of the two ring-switched slice claims, the 17 constant-lane claims at `ρ'`, and `R`. -/
noncomputable def chLinkSpec (hst : Stable C) (hcard : ∀ h, (C h).ncard ≤ L₀) (h ys : ℕ)
    (hys : ys % 4 = 0) (hys' : ys / 4 < 16) (col : β → ℕ → K) (R : β → Prop)
    (h2 : (L₀ : ℝ≥0∞) * errE 2 + 0 ≤ εmax)
    (hr0 : (∑ _i ∈ range 6, (L₀ : ℝ≥0∞) * errE 1) + 0 ≤ εmax)
    (hrT : (∑ _i ∈ range 6, (L₀ : ℝ≥0∞) * errE 1) + T ≤ εmax) :
    Spec (chLinkProg h ys)
      (Doomed C (fun q ↦ LinkBits h ys (col q) ∧ ConstLanes h (col q) ∧ R q))
      (ChLinkPost (C := C) h col R) εmax (((h + 9 : ℕ) : ℝ≥0∞) * (L₀ * errE 1) + 0) T :=
  ((zeroSpec (T := 0) hst hcard (fun q ↦ linkDelta h ys (col q))
      (fun q ↦ ZeroOn (constDelta h (col q)) [] (h + 5) ∧ R q) (n := h + 9) (m := h + 9)
      le_rfl).mono
    (fun hist (hd : Doomed C (fun q ↦ LinkBits h ys (col q) ∧ ConstLanes h (col q) ∧ R q) hist) ↦
      Doomed.mono hd fun q ⟨hz, hk, hR⟩ ↦
        ⟨linkBits_of_zero h ys (col q) hz, const_of_zero h (col q) hk, hR⟩)
    (fun _ _ h ↦ h) le_rfl le_rfl le_rfl).bind' fun chal ↦
  if hc : chal.length = h + 9 then
    ((sumcheckZSpec (T := 0) hst hcard R (fun q ↦ constDelta h (col q)) (h + 5)
        (Fsh_plain h ys (chLam h chal) (chZeta h chal) col (chRho h chal)) (by norm_num)
        (count := 3) (by norm_num) (by norm_num) zero_le h2 h [] (chShiftTargetE h chal)
        (by simp) (by simp)).mono
      (fun _ (hd : chal.length = h + 9 ∧ Doomed C (fun q ↦ ZeroOn (linkDelta h ys (col q)) chal
          (h + 9) ∧ (ZeroOn (constDelta h (col q)) [] (h + 5) ∧ R q)) _) ↦
        Doomed.mono hd.2 fun q ⟨hcl, hk, hR⟩ ↦ ⟨zero_of_shiftClaim h ys (col q) hc hcl, hk, hR⟩)
      (fun _ _ h ↦ h) le_rfl le_rfl le_rfl).bind' fun shift ↦
    if hs : shift.1.length = h then
      ((doomReadN (T := (∑ _i ∈ range 6, (L₀ : ℝ≥0∞) * errE 1) + 0) hst
          (fun q ↦ shift.2 = Fsh h ys (col q) (chLam h chal) (chZeta h chal) (chRho h chal)
            ([] ++ shift.1) ∧ ZeroOn (constDelta h (col q)) ([] ++ shift.1) (h + 5) ∧ R q)
          hr0 63).mono (fun _ hd ↦ hd.2) (fun _ _ h ↦ h) le_rfl le_rfl le_rfl).bind' fun inS ↦
      if hi : inS.length = 64 then
        ((ringColSpec (T := 0) hst hcard h col
            (fun q ↦ chSc2TargetE h chal shift inS =
                G2 h ys (col q) (chLam h chal) (chZeta h chal) (chRho h chal) shift.1 [] ∧
              ZeroOn (constDelta h (col q)) shift.1 (h + 5) ∧ R q)
            (chInPt h chal shift) inS ⟨by simp [chInPt, chLam, hs, hc], hi⟩).mono
          (fun _ hd ↦ Doomed.mono hd.2 fun q ⟨hsl, h2c, hk, hR⟩ ↦ ⟨by
              have hr : (chRho h chal).length = h := by simp [chRho, hc]
              have hl : (chLam h chal).length = 3 := by simp [chLam, hc]
              rw [List.nil_append, Fsh_end h ys (col q) _ _ hr hs hl]
              rw [chSc2TargetE, G2_nil] at h2c
              have hin : ∑ p ∈ range 64, eqAt (chZeta h chal) p * inS.getD p 0 =
                  ∑ p ∈ range 64, eqAt (chZeta h chal) p *
                    sliceExt h (col q) (shift.1 ++ chLam h chal ++ [0, 0, 0]) p :=
                Finset.sum_congr rfl fun p hp ↦ by rw [hsl.2.2 p (Finset.mem_range.1 hp)]; rfl
              rw [hin] at h2c
              exact char2_move h2c, by simpa using hk, hR⟩)
          (fun _ _ h ↦ h) le_rfl le_rfl le_rfl).bind' fun ringIn ↦
        ((sumcheckSpec (T := 0) hst hcard
            (fun q ↦ RingColTrue h (col q) ringIn ∧ ZeroOn (constDelta h (col q)) shift.1 (h + 5) ∧
              R q)
            (G2_plain h ys (chLam h chal) (chZeta h chal) col (chRho h chal) shift.1)
            (count := 3) (by norm_num) (by norm_num) zero_le h2 2 [] (chSc2TargetE h chal shift inS)
            (by simp)).mono
          (fun _ hd ↦ Doomed.mono hd fun q ⟨hc2, hRc, hk, hR⟩ ↦ ⟨hRc, hc2, hk, hR⟩)
          (fun _ _ h ↦ h) le_rfl le_rfl le_rfl).bind' fun sc2 ↦
        if hm : sc2.1.length = 2 then
          ((doomReadN (T := (∑ _i ∈ range 6, (L₀ : ℝ≥0∞) * errE 1) + T) hst
              (fun q ↦ sc2.2 = G2 h ys (col q) (chLam h chal) (chZeta h chal) (chRho h chal)
                shift.1 ([] ++ sc2.1) ∧ (RingColTrue h (col q) ringIn ∧
                  ZeroOn (constDelta h (col q)) shift.1 (h + 5) ∧ R q)) hrT 63).mono
            (fun _ hd ↦ hd.2) (fun _ _ h ↦ h) le_rfl le_rfl le_rfl).bind' fun yS ↦
          if hy : yS.length = 64 then
            ((ringColSpec (T := T) hst hcard h col
                (fun q ↦ (sc2.2 = eqMaskedE (chRho h chal) shift.1 *
                    ∑ q ∈ range 64, wtE (chLam h chal) (chZeta h chal) sc2.1 q * yS.getD q 0) ∧
                  (RingColTrue h (col q) ringIn ∧
                    ZeroOn (constDelta h (col q)) shift.1 (h + 5) ∧ R q))
                (chYPt ys shift sc2) yS
                ⟨by simp [chYPt, hs, hm, selectorPoint], hy⟩).mono
              (fun _ hd ↦ Doomed.mono hd.2 fun q ⟨hsl, hcheck, hrest⟩ ↦ ⟨by
                  rw [List.nil_append, G2_end h ys (col q) _ _ _ _ hm, hcheck]
                  refine congrArg _ (Finset.sum_congr rfl fun qq hqq ↦ ?_)
                  rw [hsl.2.2 qq (Finset.mem_range.1 hqq)]
                  exact congrArg _ (sliceExt_y h ys (col q) hs hm hys hys' qq), hrest⟩)
              (fun _ _ h ↦ h) le_rfl le_rfl le_rfl).bind' fun ringY ↦
            (samplesKeep (T := T) hst hcard
              (fun q ↦ RingColTrue h (col q) ringY ∧
                ((sc2.2 = eqMaskedE (chRho h chal) shift.1 *
                    ∑ q ∈ range 64, wtE (chLam h chal) (chZeta h chal) sc2.1 q * yS.getD q 0) ∧
                  (RingColTrue h (col q) ringIn ∧
                    ZeroOn (constDelta h (col q)) shift.1 (h + 5) ∧ R q))) 5).bind' fun _ ↦
            (Spec.require (Post := fun _ hist ↦ Doomed C (fun q ↦ RingColTrue h (col q) ringY ∧
                RingColTrue h (col q) ringIn ∧ ZeroOn (constDelta h (col q)) shift.1 (h + 5) ∧
                  R q) hist)
              (fun _ hd hcond ↦ Doomed.mono hd fun q ⟨hy', hin, hk, hR⟩ ↦
                ⟨hy', hcond, hin, hk, hR⟩)).bind' fun _ ↦
            (Spec.ret (⟨chal, shift, inS, ringIn, sc2, yS, ringY⟩ : ChLinkOut)).mono
              (fun _ hd ↦ ⟨hs, Doomed.mono hd fun q ⟨hin, hy', hcc, hR⟩ ↦
                ⟨hy', hin, constZero_of_claims h (col q) hs hcc, hR⟩⟩)
              (fun _ _ h ↦ h) le_rfl le_rfl le_rfl
          else Spec.dead.mono (fun _ hd ↦ hy hd.1) (fun _ _ h ↦ h) le_rfl le_rfl le_rfl
        else Spec.dead.mono (fun _ hd ↦ hm hd.1) (fun _ _ h ↦ h) le_rfl le_rfl le_rfl
      else Spec.dead.mono (fun _ hd ↦ hi hd.1) (fun _ _ h ↦ h) le_rfl le_rfl le_rfl
    else Spec.dead.mono (fun _ hd ↦ hs hd.1) (fun _ _ h ↦ h) le_rfl le_rfl le_rfl
  else Spec.dead.mono (fun _ hd ↦ hc hd.1) (fun _ _ h ↦ h) le_rfl le_rfl le_rfl

end Lvm.KG
end
-- ===== end of `LvmChainTableLink` =====

/-!
# The `KS` sponge link

For every row `i < 2^hk` and lane `l < 25`: `in_i[l] = cont_i·Y_{i−1}[l] + [l < 17]·Msg_l[i]`, where
`Msg_l[i]` is `C_rec`'s stream column `M_l` below the split `s = 2^hk − 2^xl` and `C_main`'s `X_l` (17 columns
of `2^xl` rows) from it, and `cont_i = [i ∈ rows]` (V_S's `contRows`, `0 ∉ rows`). This is
`SpongeRel.link` (`LvmSpongeTable`) with `msg = ksMsg s`. (lvm2 CR-K, KS14: at `P20` `hk = 14`, `xl = 10`, the
split 15,360 and the selector `x₁₃x₁₂x₁₁x₁₀`; v1's layout is `xl = hk − 1`, split `2^(hk−1)`, selector `x_{hk−1}`.)
The rows from the split are the subcube whose coordinates `xl … hk − 1` are all one, so their weight at `ρ'`
is `sel(ρ') · eq(ρ'_{<xl}, ·)` with `sel(ρ') = Π_{j ≥ xl} ρ'_j` (`selX`, `eqAt_split`).

`ksLinkProg` is V_S's phase 7, read for read:

```
kchal ← hk + 5 challenges (ρ, λ);  kshift ← hk plain rounds of degree 2 on the claim 0;
vals ← 4 scalars (Y_ω(ρ'), in_ω(ρ'), M_ω(ρ') on the rows below the split, X_ω(ρ'_{<xl}));
require f = Sc(ρ, ρ')·Y_ω + eq(ρ, ρ')·(in_ω + M_ω + sel(ρ')·X_ω)
```

**`ksLinkSpec`**: from doom of `SpongeLink ∧ R` to doom of the four combined claims (`KsClaims`)
and `R`. `contShiftE_eq` proves V_S's `contShift` (a sum over the rows of `cont`) is the shifted
kernel's extension. Groups: `ρλ`, `(hk + 5)·L₀/|E|`; each round `L₀·2/|E|`.
-/

set_option autoImplicit false

namespace Lvm.KG

open LeanVM.Parameters LeanVM.Protocol.Compile LeanVM.Protocol.Verifier LeanVM.Protocol.KeccakGkr
open LeanVM.Protocol.EndToEnd LeanVM.Protocol.EndToEnd.Front LeanVM.Protocol.EndToEnd.Complete
open Finset
open scoped ENNReal

/-! ## V_S's formulas over `E` -/

/-- V_S's `contShift`: `Sc(ρ, ρ') = Σ_{i ∈ rows} eq(ρ, i)·eq(ρ', i − 1)`. -/
def contShiftE (rows : List ℕ) (rho rho' : List E) : E :=
  (rows.map fun i ↦ eqAt rho i * eqAt rho' (i - 1)).sum

/-- The message lane `l` of row `i`: `M` below the split `s`, `X` (indexed from the split) from it. -/
def ksMsg (s : ℕ) (M X : ℕ → ℕ → K) (i l : ℕ) : K := if i < s then M i l else X (i - s) l

/-- The split of `2^hk` rows when `X` has `2^xl`: `2^hk − 2^xl`. -/
def ksSplitN (hk xl : ℕ) : ℕ := 2 ^ hk - 2 ^ xl

theorem ksSplitN_add {hk xl : ℕ} (hxl : xl ≤ hk) : ksSplitN hk xl + 2 ^ xl = 2 ^ hk := by
  have := Nat.pow_le_pow_right two_pos hxl
  unfold ksSplitN; (clear * - this; omega)

/-- **V_S's selector** of the rows from the split: `Π_{j ≥ xl} ρ'_j`. -/
def selX (xl : ℕ) (pt : List E) : E := (pt.drop xl).prod

/-- **The sponge link** on every row (`SpongeRel.link`, `cont i = [i ∈ rows]`). -/
def SpongeLink (hk : ℕ) (rows : List ℕ) (ks : ℕ → K) (Y msg : ℕ → ℕ → K) : Prop :=
  ∀ i < 2 ^ hk, ∀ l < 25,
    ks (i + 2 ^ hk * l) = (if i ∈ rows then Y (i - 1) l else 0) + (if l < 17 then msg i l else 0)

/-- **The `KS` link** (V_S phase 7, `M3.v0`; `X` on `2^xl` rows). -/
def ksLinkProg (hk xl : ℕ) (rows : List ℕ) :
    VerifierProgram (List E × (List E × E) × List E) :=
  VerifierProgram.sampleChallenges (hk + 5) >>= fun kchal ↦
  sumcheck 0 3 (List.replicate hk none) >>= fun kshift ↦
  VerifierProgram.readScalars 4 >>= fun vals ↦
  VerifierProgram.require (kshift.2 =
    contShiftE rows (kchal.take hk) kshift.1 * vals.getD 0 0 +
      eqEval (kchal.take hk) kshift.1 * (vals.getD 1 0 + vals.getD 2 0 +
        selX xl kshift.1 * vals.getD 3 0)) >>= fun _ ↦
  VerifierProgram.ret (kchal, kshift, vals)

/-- **The four combined claims** at `ρ'` (V_S's `yC`, `inC`, `mC`, `xC`): `M`'s on the rows below the split
(`eq(ρ', ·)` cut at `2^hk − 2^xl`), `X`'s at `ρ'_{<xl}`. -/
def KsClaims (hk xl : ℕ) (ks : ℕ → K) (Y M X : ℕ → ℕ → K) (lam rho' vals : List E) : Prop :=
  vals.getD 0 0 = ∑ l ∈ range 25, eqAt lam l * stepMle hk rho' (fun x ↦ Y x l) ∧
  vals.getD 1 0 = ∑ l ∈ range 25, eqAt lam l * stepMle hk rho' (fun x ↦ ks (x + 2 ^ hk * l)) ∧
  vals.getD 2 0 = ∑ l ∈ range 17, eqAt lam l * ∑ x ∈ range (ksSplitN hk xl), eqAt rho' x * ofK (M x l) ∧
  vals.getD 3 0 = ∑ l ∈ range 17, eqAt lam l * stepMle xl (rho'.take xl) (fun x ↦ X x l)

/-! ## `contShift` is the shifted kernel's extension -/

/-- The shifted continuation kernel on the cube: `Sc(ρ, k) = [k + 1 ∈ rows]·eq(ρ, k + 1)`. -/
def scK (rows : List ℕ) (rho : List E) (k : ℕ) : E := if k + 1 ∈ rows then eqAt rho (k + 1) else 0

theorem contShiftE_eq (n : ℕ) {rows : List ℕ} (hnd : rows.Nodup)
    (hrows : ∀ i ∈ rows, 1 ≤ i ∧ i < 2 ^ n) (rho rho' : List E) :
    contShiftE rows rho rho' = ∑ k ∈ range (2 ^ n), eqAt rho' k * scK rows rho k := by
  classical
  rw [contShiftE, ← List.sum_toFinset _ hnd]
  simp only [scK, mul_ite, mul_zero]
  rw [← Finset.sum_filter]
  refine Finset.sum_nbij' (fun i ↦ i - 1) (fun k ↦ k + 1) ?_ ?_ ?_ ?_ ?_
  · intro i hi
    have := hrows i (List.mem_toFinset.1 hi)
    simp only [Finset.mem_filter, Finset.mem_range]
    exact ⟨by (clear * - this; omega), by rw [show i - 1 + 1 = i by (clear * - this; omega)]; exact List.mem_toFinset.1 hi⟩
  · intro k hk
    simp only [Finset.mem_filter] at hk
    exact List.mem_toFinset.2 hk.2
  · intro i hi
    have := hrows i (List.mem_toFinset.1 hi)
    (clear * - this; omega)
  · intro k _
    simp
  · intro i hi
    have := hrows i (List.mem_toFinset.1 hi)
    simp only [show i - 1 + 1 = i by (clear * - this; omega)]
    ring

/-! ## The zero test and the sumcheck family -/

variable (hk xl : ℕ) (rows : List ℕ) (ks : ℕ → K) (Y M X : ℕ → ℕ → K) (lam : List E)

/-- The sponge link's zero-test table on `hk + 5` bits: row low, lane high. -/
def ksDelta (w : ℕ) : E :=
  if w / 2 ^ hk < 25 then
    ofK (ks (w % 2 ^ hk + 2 ^ hk * (w / 2 ^ hk))) +
      (if w % 2 ^ hk ∈ rows then ofK (Y (w % 2 ^ hk - 1) (w / 2 ^ hk)) else 0) +
      (if w / 2 ^ hk < 17 then ofK (ksMsg (ksSplitN hk xl) M X (w % 2 ^ hk) (w / 2 ^ hk)) else 0)
  else 0

theorem ofK_add' (a b : K) : ofK (a + b) = ofK a + ofK b := map_add (algebraMap K E) a b

theorem ofK_zero' : ofK (0 : K) = 0 := map_zero (algebraMap K E)

theorem char2_sum3 {a b c : E} (h : a + b + c = 0) : a = b + c := by
  linear_combination h - (b + c) * CharTwo.two_eq_zero (R := E)

/-- A vanishing table is the sponge link. -/
theorem spongeLink_of_zero (hz : ZeroOn (ksDelta hk xl rows ks Y M X) [] (hk + 5)) :
    SpongeLink hk rows ks Y (ksMsg (ksSplitN hk xl) M X) := by
  rw [zeroOn_nil] at hz
  intro i hi l hl
  have := hz (i + 2 ^ hk * l) (by
    rw [show 2 ^ (hk + 5) = 2 ^ hk * 32 by rw [pow_add]; rfl]
    calc i + 2 ^ hk * l < 2 ^ hk * l + 2 ^ hk := by
          rw [Nat.add_comm]; exact Nat.add_lt_add_left hi _
      _ = 2 ^ hk * (l + 1) := (Nat.mul_succ _ _).symm
      _ ≤ 2 ^ hk * 32 := Nat.mul_le_mul_left _ (Nat.le_trans hl (by decide)))
  simp only [ksDelta, idx_div hk hi, idx_mod hk hi, if_pos hl] at this
  apply ofK_injective'
  rw [ofK_add', apply_ite ofK, apply_ite ofK, ofK_zero']
  exact char2_sum3 this

/-- `Y_ω(k)`, `in_ω(k)`, `Msg_ω(k)`: the lanes combined by `eq(λ, ·)`. -/
def yOm (k : ℕ) : E := ∑ l ∈ range 25, eqAt lam l * ofK (Y k l)
/-- `in_ω(k)`. -/
def inOm (k : ℕ) : E := ∑ l ∈ range 25, eqAt lam l * ofK (ks (k + 2 ^ hk * l))
/-- `Msg_ω(k)`. -/
def msgOm (k : ℕ) : E := ∑ l ∈ range 17, eqAt lam l * ofK (ksMsg (ksSplitN hk xl) M X k l)

/-- The `KS` link sumcheck's family. -/
noncomputable def Fks (rho acc : List E) : E :=
  cubeSum (fun pt ↦ (∑ k ∈ range (2 ^ hk), eqAt pt k * scK rows rho k) *
      (∑ k ∈ range (2 ^ hk), eqAt pt k * yOm Y lam k) +
    (∑ k ∈ range (2 ^ hk), eqAt pt k * eqAt rho k) *
      (∑ k ∈ range (2 ^ hk), eqAt pt k * (inOm hk ks lam k + msgOm hk xl M X lam k))) hk acc

theorem Fks_plain {β : Type} (kq : β → ℕ → K) (Yq Mq Xq : β → ℕ → ℕ → K) (rho : List E) :
    PlainFamily (fun q acc ↦ Fks hk xl rows (kq q) (Yq q) (Mq q) (Xq q) lam rho acc) 2 hk :=
  cube_plainFamily _ hk fun _ pre post ↦ PolyLE.add (polyLE_mle_mul _ _ _ _ pre post)
    (polyLE_mle_mul _ _ _ _ pre post)

/-- One row of the table, its lanes combined by `eq(λ, ·)`. -/
theorem ksDelta_row (hl : lam.length = 5) {x : ℕ} (hx : x < 2 ^ hk) :
    ∑ o ∈ range (2 ^ lam.length), eqAt lam o * ksDelta hk xl rows ks Y M X (x + 2 ^ hk * o) =
      inOm hk ks lam x + (if x ∈ rows then yOm Y lam (x - 1) else 0) + msgOm hk xl M X lam x := by
  rw [hl, show (2 : ℕ) ^ 5 = 25 + 7 from rfl, Finset.sum_range_add]
  have h7 : ∑ o ∈ range 7, eqAt lam (25 + o) * ksDelta hk xl rows ks Y M X (x + 2 ^ hk * (25 + o)) =
      0 := by
    refine Finset.sum_eq_zero fun o _ ↦ ?_
    rw [ksDelta, idx_div hk hx, if_neg (by (clear * -; omega)), mul_zero]
  rw [h7, add_zero]
  have e : ∀ o ∈ range 25, eqAt lam o * ksDelta hk xl rows ks Y M X (x + 2 ^ hk * o) =
      eqAt lam o * ofK (ks (x + 2 ^ hk * o)) +
        ((if x ∈ rows then eqAt lam o * ofK (Y (x - 1) o) else 0) +
          (if o < 17 then eqAt lam o * ofK (ksMsg (ksSplitN hk xl) M X x o) else 0)) := by
    intro o ho
    rw [ksDelta, idx_div hk hx, idx_mod hk hx, if_pos (Finset.mem_range.1 ho), mul_add, mul_add,
      mul_ite, mul_ite, mul_zero, add_assoc]
  rw [Finset.sum_congr rfl e, Finset.sum_add_distrib, Finset.sum_add_distrib]
  have hY : ∑ o ∈ range 25, (if x ∈ rows then eqAt lam o * ofK (Y (x - 1) o) else 0) =
      if x ∈ rows then yOm Y lam (x - 1) else 0 := by
    split_ifs <;> simp [yOm]
  have hM : ∑ o ∈ range 25, (if o < 17 then eqAt lam o * ofK (ksMsg (ksSplitN hk xl) M X x o) else 0) =
      msgOm hk xl M X lam x := by
    rw [show 25 = 17 + 8 from rfl, Finset.sum_range_add, msgOm,
      Finset.sum_eq_zero (s := range 8) fun o _ ↦ if_neg (by (clear * -; omega)), add_zero]
    exact Finset.sum_congr rfl fun o ho ↦ if_pos (Finset.mem_range.1 ho)
  rw [hY, hM, inOm, add_assoc]

/-- **The zero test at `(ρ, λ)` is the claim `0`.** -/
theorem ks_zero_of_claim (h0 : 0 ∉ rows) (hrows : ∀ i ∈ rows, i < 2 ^ hk) {kchal : List E}
    (hc : kchal.length = hk + 5)
    (H : (0 : E) = Fks hk xl rows ks Y M X (kchal.drop hk) (kchal.take hk) []) :
    ZeroOn (ksDelta hk xl rows ks Y M X) kchal (hk + 5) := by
  have hr : (kchal.take hk).length = hk := by simp [hc]
  have hl : (kchal.drop hk).length = 5 := by simp [hc]
  set ρ := kchal.take hk with hρ
  set lm := kchal.drop hk with hlm
  rw [zeroOn_full _ hc]
  have hsplit : kchal = ρ ++ lm := (List.take_append_drop hk kchal).symm
  have e1 : ∑ w ∈ range (2 ^ (hk + 5)), eqAt kchal w * ksDelta hk xl rows ks Y M X w =
      ∑ x ∈ range (2 ^ hk), eqAt ρ x *
        (inOm hk ks lm x + (if x ∈ rows then yOm Y lm (x - 1) else 0) + msgOm hk xl M X lm x) := by
    conv_lhs => rw [hsplit]
    rw [show hk + 5 = hk + lm.length by rw [hl], col_split hr]
    simp only [Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun x hx ↦ ?_
    rw [← ksDelta_row hk xl rows ks Y M X lm hl (Finset.mem_range.1 hx), Finset.mul_sum]
    exact Finset.sum_congr rfl fun o _ ↦ by ring
  rw [e1]
  refine Eq.trans ?_ H.symm
  rw [Fks, cubeSum_nil]
  have hcube : ∀ u ∈ range (2 ^ hk),
      (∑ k ∈ range (2 ^ hk), eqAt (bitsE u hk) k * scK rows ρ k) *
        (∑ k ∈ range (2 ^ hk), eqAt (bitsE u hk) k * yOm Y lm k) +
      (∑ k ∈ range (2 ^ hk), eqAt (bitsE u hk) k * eqAt ρ k) *
        (∑ k ∈ range (2 ^ hk), eqAt (bitsE u hk) k * (inOm hk ks lm k + msgOm hk xl M X lm k)) =
      scK rows ρ u * yOm Y lm u + eqAt ρ u * (inOm hk ks lm u + msgOm hk xl M X lm u) := by
    intro u hu
    have hu' := Finset.mem_range.1 hu
    rw [sum_eqAt_bitsE hu', sum_eqAt_bitsE hu', sum_eqAt_bitsE hu', sum_eqAt_bitsE hu']
  rw [Finset.sum_congr rfl hcube, Finset.sum_add_distrib]
  have hp := Nat.two_pow_pos hk
  obtain ⟨Mk, hMk⟩ : ∃ Mk, 2 ^ hk = Mk + 1 := ⟨2 ^ hk - 1, by (clear * - hp; omega)⟩
  have hshift : ∑ u ∈ range (2 ^ hk), scK rows ρ u * yOm Y lm u =
      ∑ x ∈ range (2 ^ hk), eqAt ρ x * (if x ∈ rows then yOm Y lm (x - 1) else 0) := by
    rw [hMk, Finset.sum_range_succ, Finset.sum_range_succ']
    have hlast : Mk + 1 ∉ rows := fun hm ↦ by have := hrows _ hm; (clear * - hMk this; omega)
    simp only [scK, hlast, ite_false, zero_mul, add_zero, h0, mul_zero, Nat.add_sub_cancel]
    refine Finset.sum_congr rfl fun x _ ↦ ?_
    split_ifs <;> simp
  rw [hshift, ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun x _ ↦ by ring

/-! ## The end of the sumcheck -/

/-- `eq` at the all-ones index of a point is the product of its coordinates. -/
theorem eqAt_ones : ∀ pt : List E, eqAt pt (2 ^ pt.length - 1) = pt.prod
  | [] => by simp
  | r :: rs => by
    have h1 : 1 ≤ 2 ^ rs.length := Nat.one_le_two_pow
    obtain ⟨M, hM⟩ : ∃ M, 2 ^ rs.length = M + 1 := ⟨_, (Nat.succ_pred_eq_of_pos h1).symm⟩
    have e : 2 ^ rs.length * 2 - 1 = 1 + 2 * M := by
      rw [hM, show (M + 1) * 2 = 1 + 2 * M + 1 by ring, Nat.add_sub_cancel]
    have hm : (2 ^ rs.length * 2 - 1) % 2 = 1 := by rw [e, Nat.add_mul_mod_self_left]
    have hd : (2 ^ rs.length * 2 - 1) / 2 = 2 ^ rs.length - 1 := by
      rw [e, Nat.add_mul_div_left _ _ (by decide), hM, Nat.add_sub_cancel, show 1 / 2 = 0 from rfl,
        Nat.zero_add]
    rw [eqAt_cons, List.length_cons, List.prod_cons, pow_succ, hm, hd, eqAt_ones rs, if_pos rfl]

/-- **A row from the split**: `eq(pt, 2^hk − 2^xl + j) = eq(pt_{<xl}, j)·sel(pt)`. -/
theorem eqAt_split {hk xl : ℕ} (hxl : xl ≤ hk) {pt : List E} (hpt : pt.length = hk) {j : ℕ}
    (hj : j < 2 ^ xl) : eqAt pt (ksSplitN hk xl + j) = eqAt (pt.take xl) j * selX xl pt := by
  have hd : (pt.drop xl).length = hk - xl := by simp [hpt]
  have ht : (pt.take xl).length = xl := by simp [hpt]; omega
  have hp : 2 ^ hk = 2 ^ xl * 2 ^ (hk - xl) := by rw [← pow_add]; congr 1; (clear * - hxl hpt ht; omega)
  have h1 : 1 ≤ 2 ^ (hk - xl) := Nat.one_le_two_pow
  have hw : ksSplitN hk xl + j = j + 2 ^ xl * (2 ^ (hk - xl) - 1) := by
    have e := ksSplitN_add hxl
    rw [hp] at e
    rw [Nat.mul_sub_one]
    have : 2 ^ xl ≤ 2 ^ xl * 2 ^ (hk - xl) := Nat.le_mul_of_pos_right _ (by positivity)
    (clear * - e; omega)
  conv_lhs => rw [← List.take_append_drop xl pt]
  rw [eqAt_append, ht, hw, eqAt_mod (pt.take xl), ht, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hj,
    Nat.add_mul_div_left _ _ (by positivity), Nat.div_eq_of_lt hj, zero_add, ← hd, eqAt_ones, selX]

/-- **The messages split at `2^hk − 2^xl`**: `M` on the rows below, `X` (its `xl` low coordinates) times the
selector on the rows from it. -/
theorem msgOm_mle (hxl : xl ≤ hk) {pt : List E} (hpt : pt.length = hk) :
    ∑ k ∈ range (2 ^ hk), eqAt pt k * msgOm hk xl M X lam k =
      ∑ x ∈ range (ksSplitN hk xl), eqAt pt x * ∑ l ∈ range 17, eqAt lam l * ofK (M x l) +
        selX xl pt * ∑ x ∈ range (2 ^ xl), eqAt (pt.take xl) x *
          ∑ l ∈ range 17, eqAt lam l * ofK (X x l) := by
  rw [show range (2 ^ hk) = range (ksSplitN hk xl + 2 ^ xl) by rw [ksSplitN_add hxl],
    Finset.sum_range_add, Finset.mul_sum]
  refine congrArg₂ (· + ·) ?_ ?_
  · refine Finset.sum_congr rfl fun x hx ↦ ?_
    simp only [msgOm, ksMsg, if_pos (Finset.mem_range.1 hx)]
  · refine Finset.sum_congr rfl fun j hj ↦ ?_
    have hj' := Finset.mem_range.1 hj
    simp only [msgOm, ksMsg, if_neg (show ¬ ksSplitN hk xl + j < ksSplitN hk xl by (clear * -; omega)),
      Nat.add_sub_cancel_left, eqAt_split hxl hpt hj']
    ring

/-- **The cut at the split** (char 2): the extension over all `2^hk` rows plus `sel(pt)` times the rows from the
split at `pt_{<xl}` is the extension over the rows below the split (V_S's `M` claim, KS14). -/
theorem cut_split {hk xl : ℕ} (hxl : xl ≤ hk) {pt : List E} (hpt : pt.length = hk) (F : ℕ → E) :
    ∑ n ∈ range (2 ^ hk), eqAt pt n * F n +
        selX xl pt * ∑ n ∈ range (2 ^ xl), eqAt (pt.take xl) n * F (ksSplitN hk xl + n) =
      ∑ n ∈ range (ksSplitN hk xl), eqAt pt n * F n := by
  have hz : ∑ j ∈ range (2 ^ xl), (eqAt pt (ksSplitN hk xl + j) * F (ksSplitN hk xl + j) +
      selX xl pt * (eqAt (pt.take xl) j * F (ksSplitN hk xl + j))) = 0 :=
    Finset.sum_eq_zero fun j hj ↦ by
      rw [eqAt_split hxl hpt (Finset.mem_range.1 hj),
        show selX xl pt * (eqAt (pt.take xl) j * F (ksSplitN hk xl + j)) =
          eqAt (pt.take xl) j * selX xl pt * F (ksSplitN hk xl + j) by ring]
      exact CharTwo.add_self_eq_zero _
  rw [show range (2 ^ hk) = range (ksSplitN hk xl + 2 ^ xl) by rw [ksSplitN_add hxl],
    Finset.sum_range_add, Finset.mul_sum, add_assoc, ← Finset.sum_add_distrib, hz, add_zero]

/-- **The `KS` link sumcheck's end** at `ρ'`, in V_S's closed forms. -/
theorem Fks_end (hxl : xl ≤ hk) (hnd : rows.Nodup) (hrows : ∀ i ∈ rows, 1 ≤ i ∧ i < 2 ^ hk)
    {rho pt : List E} (hr : rho.length = hk) (hpt : pt.length = hk) :
    Fks hk xl rows ks Y M X lam rho pt =
      contShiftE rows rho pt * ∑ l ∈ range 25, eqAt lam l * stepMle hk pt (fun x ↦ Y x l) +
        eqEval rho pt * (∑ l ∈ range 25, eqAt lam l * stepMle hk pt (fun x ↦ ks (x + 2 ^ hk * l)) +
          ∑ l ∈ range 17, eqAt lam l * ∑ x ∈ range (ksSplitN hk xl), eqAt pt x * ofK (M x l) +
          selX xl pt * ∑ l ∈ range 17, eqAt lam l * stepMle xl (pt.take xl) (fun x ↦ X x l)) := by
  rw [Fks, cubeSum_full _ hpt, ← contShiftE_eq hk hnd hrows]
  have hee : ∑ k ∈ range (2 ^ hk), eqAt pt k * eqAt rho k = eqEval rho pt := by
    rw [← sum_eqAt_mul_eqAt rho pt (by rw [hr, hpt]), hr]
    exact Finset.sum_congr rfl fun k _ ↦ mul_comm _ _
  have hy : ∑ k ∈ range (2 ^ hk), eqAt pt k * yOm Y lam k =
      ∑ l ∈ range 25, eqAt lam l * stepMle hk pt (fun x ↦ Y x l) := by
    simp only [yOm, stepMle, Finset.mul_sum]
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun l _ ↦ Finset.sum_congr rfl fun k _ ↦ by ring
  have hin : ∑ k ∈ range (2 ^ hk), eqAt pt k * inOm hk ks lam k =
      ∑ l ∈ range 25, eqAt lam l * stepMle hk pt (fun x ↦ ks (x + 2 ^ hk * l)) := by
    simp only [inOm, stepMle, Finset.mul_sum]
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun l _ ↦ Finset.sum_congr rfl fun k _ ↦ by ring
  have hm : ∀ (n : ℕ) (a : List E) (Z : ℕ → ℕ → K), ∑ x ∈ range n, eqAt a x *
      ∑ l ∈ range 17, eqAt lam l * ofK (Z x l) =
      ∑ l ∈ range 17, eqAt lam l * ∑ x ∈ range n, eqAt a x * ofK (Z x l) := fun n a Z ↦ by
    simp only [Finset.mul_sum]
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun l _ ↦ Finset.sum_congr rfl fun k _ ↦ by ring
  rw [hee, hy, Finset.sum_congr rfl fun k _ ↦ mul_add _ _ _, Finset.sum_add_distrib, hin,
    msgOm_mle hk xl M X lam hxl hpt, hm, hm]
  simp only [stepMle]
  ring

/-! ## The specification -/

variable {β : Type} {C : List Ev → Set β} [Finite β] {L₀ : ℕ} {εmax T : ℝ≥0∞}

/-- **The `KS` sponge link**, round by round: from doom of the sponge link and `R` to doom of the
four combined claims at `ρ'` and `R`. Lead `(hk + 5)·L₀/|E|`. -/
noncomputable def ksLinkSpec (hst : Stable C) (hcard : ∀ h, (C h).ncard ≤ L₀) (hk xl : ℕ)
    (hxl : xl ≤ hk) (rows : List ℕ) (hnd : rows.Nodup)
    (hrows : ∀ i ∈ rows, 1 ≤ i ∧ i < 2 ^ hk) (ks : β → ℕ → K) (Y M X : β → ℕ → ℕ → K)
    (R : β → Prop) (h2 : (L₀ : ℝ≥0∞) * errE 2 + 0 ≤ εmax) (hT : T ≤ εmax) :
    Spec (ksLinkProg hk xl rows)
      (Doomed C (fun q ↦ SpongeLink hk rows (ks q) (Y q) (ksMsg (ksSplitN hk xl) (M q) (X q)) ∧ R q))
      (fun out hist ↦ out.2.1.1.length = hk ∧ Doomed C (fun q ↦
        KsClaims hk xl (ks q) (Y q) (M q) (X q) (out.1.drop hk) out.2.1.1 out.2.2 ∧ R q) hist)
      εmax (((hk + 5 : ℕ) : ℝ≥0∞) * (L₀ * errE 1) + 0) T :=
  have h0 : 0 ∉ rows := fun h ↦ by have := hrows 0 h; omega
  ((zeroSpec (T := 0) hst hcard (fun q ↦ ksDelta hk xl rows (ks q) (Y q) (M q) (X q)) R
      (n := hk + 5) (m := hk + 5) le_rfl).mono
    (fun hist (hd : Doomed C (fun q ↦ SpongeLink hk rows (ks q) (Y q) (ksMsg (ksSplitN hk xl) (M q) (X q)) ∧
        R q) hist) ↦ Doomed.mono hd fun q ⟨hz, hR⟩ ↦
      ⟨spongeLink_of_zero hk xl rows (ks q) (Y q) (M q) (X q) hz, hR⟩)
    (fun _ _ h ↦ h) le_rfl le_rfl le_rfl).bind' fun kchal ↦
  if hc : kchal.length = hk + 5 then
    ((sumcheckSpec (T := 0) hst hcard R
        (Fks_plain hk xl rows (kchal.drop hk) ks Y M X (kchal.take hk)) (count := 3)
        (by norm_num) (by norm_num) zero_le h2 hk [] 0 (by simp)).mono
      (fun _ (hd : kchal.length = hk + 5 ∧ Doomed C (fun q ↦
          ZeroOn (ksDelta hk xl rows (ks q) (Y q) (M q) (X q)) kchal (hk + 5) ∧ R q) _) ↦
        Doomed.mono hd.2 fun q ⟨hcl, hR⟩ ↦
          ⟨ks_zero_of_claim hk xl rows (ks q) (Y q) (M q) (X q) h0
            (fun i hi ↦ (hrows i hi).2) hc hcl, hR⟩)
      (fun _ _ h ↦ h) le_rfl le_rfl le_rfl).bind' fun kshift ↦
    if hs : kshift.1.length = hk then
      ((doomReadN (T := T) hst
          (fun q ↦ kshift.2 = Fks hk xl rows (ks q) (Y q) (M q) (X q) (kchal.drop hk)
            (kchal.take hk) ([] ++ kshift.1) ∧ R q) hT 3).mono
        (fun _ hd ↦ hd.2) (fun _ _ h ↦ h) le_rfl le_rfl le_rfl).bind' fun vals ↦
      (Spec.require (Post := fun _ hist ↦ Doomed C (fun q ↦
          KsClaims hk xl (ks q) (Y q) (M q) (X q) (kchal.drop hk) kshift.1 vals ∧ R q) hist)
        (fun _ hd hcond ↦ Doomed.mono hd.2 fun q ⟨⟨h1, h2', h3, h4⟩, hR⟩ ↦ ⟨by
          rw [List.nil_append, Fks_end hk xl rows (ks q) (Y q) (M q) (X q) _ hxl hnd hrows
            (by simp [hc]) hs, hcond, h1, h2', h3, h4], hR⟩)).bind' fun _ ↦
      (Spec.ret (kchal, kshift, vals)).mono (fun _ hd ↦ ⟨hs, hd⟩) (fun _ _ h ↦ h) le_rfl
        le_rfl le_rfl
    else Spec.dead.mono (fun _ hd ↦ hs hd.1) (fun _ _ h ↦ h) le_rfl le_rfl le_rfl
  else Spec.dead.mono (fun _ hd ↦ hc hd.1) (fun _ _ h ↦ h) le_rfl le_rfl le_rfl

end Lvm.KG
