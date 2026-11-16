-- New for lvm2 U-TAPE (UT-L, 2026-11-16): DAY-0 STATEMENTS of S2GU's front at `E2` (the merged tape: chain and
-- sponge halves, T1's region formula, the wire with the sponge terms, three slot reductions). The programs are the
-- statement layer (UT-L drafted them from `ref/utape.py` and COMMON's draft transcript; the V side may replace them
-- by definitions of the same name and type). Every `sorry` is a day-0 statement tagged `-- UTAPE-STMT <n>`.
import LvmE2VSpecTape

-- (SLF-K: 6 declarations that `certified` does not use moved verbatim to `LvmS2GUOff`, outside its import closure.)

/-!
# The S2GU front at `E2` (day-0 statements)

The tape has `2^21` rows: the chain half `i < 2^20` (`chainIn`, S2GF's), the sponge half `2^20 + j` (`KS13`'s row `j`
for `j < 2^13`, input `cont_j·Y[j−1] + [l < 17]·Msg_l[j]`, `LvmWireSpec.tapeIn` at `w = 20`, `hs = 13`), void above.

* **T1** (`t1U`): the separator, `r_0 … r_19`, the 50 scalars `a_0 … a_24`, `b_0 … b_24`, `r_20` (R-BP2's B1 order);
  `v_l = (1 − r_20)·a_l + r_20·(e·b_l + (1 − e)·z*_l)`, `e = Π_{k=13}^{19}(1 − r_k)` (`t1ValsF`).
* **T2**: `tapeGkrE2 21` (S2GF's GKR at `P = 16`: `tapeGkrSpecE2` reused).
* **T3** (`wireProgU`): 20 rounds of degree 2 on `E2V.wireTargetF` (S2GF's chain constant), `g_D, g_Y, g_M`, the final check
  `K̃_ch(σ)·g_D + e'·(K̃_ks(σ')·g_Y + Ĩ_ks(σ')·g_M)` (`kksF`: two `cont` intervals by `MS` differences, `ikEvalF`).
* **T4**: three `slotProgE2`: `D` (`k = 20, b = 2, sb = 1, blk = 0`), `Y` (`k = 13, b = 5, sb = 5, blk = 22`: the `Y`
  block at `22·2^18`), `M` (`k = 14` at `σ'‖0`, `b = 5, sb = 4, blk = 10`: the stream block at `10·2^19`).

Statements (owner UT-V): `sum_msIntKF`, `sum_ikKF` (T-K's kernels at `F`), `wireSpecU`, `t1_zeroU`, `tapeSpecU`.
-/

set_option autoImplicit false

namespace Lvm.E2U

open LeanVM.Parameters LeanVM.Semantics LeanVM.Protocol.Compile LeanVM.Protocol.Verifier
open LeanVM.Protocol.KeccakGkr (laneWord errE tapeStates)
open LeanVM.Protocol.EndToEnd.Front (Doomed Stable)
open Lvm.E2V
open Lvm.KG (TapeOut dOf chainIn tapeIn)
open Lvm.ASM (εS)
open Finset
open scoped ENNReal

/-! ## Kernels and T1's values, field-generic -/

section Kernels

variable {F : Type} [Field F] [Algebra K F]

/-- `I_ks`'s kernel `ι(base + x)` (T-K's `ikK` at `F`). -/
def ikKF (ρ μ : List F) (base x : ℕ) : F := E2V.iotaF ρ μ (base + x)

/-- `Ĩ(σ) = (Σ_{d<16} eq(σ_{<4}, d)·μ_d)·eq(ρ_{<w−4}, σ_{≥4})·eq(ρ_{≥w−4}, base/2^w)` (T-K's `ikEval` at `F`). -/
def ikEvalF (ρ μ σ : List F) (base : ℕ) : F :=
  E2V.sumF ((List.range 16).map fun d ↦ E2V.eqAtF (σ.take 4) d * μ.getD d 0) *
    (∑ y ∈ range (2 ^ (σ.length - 4)), E2V.eqAtF (ρ.take (σ.length - 4)) y * E2V.eqAtF (σ.drop 4) y) *
    E2V.eqAtF (ρ.drop (σ.length - 4)) (base / 2 ^ σ.length)

/-- `MS`'s interval kernel `[a ≤ x + 1 ≤ b]·ι(base + x + 1)` (T-K's `msIntK` at `F`). -/
def msIntKF (ρ μ : List F) (base a b x : ℕ) : F :=
  if a ≤ x + 1 ∧ x + 1 ≤ b then E2V.iotaF ρ μ (base + x + 1) else 0

/-- **`K̃_ks(σ')`**: `cont`'s intervals `[a, b]` as differences of `MS` at `base` (T-W's `kksE` at `F`). -/
def kksF (iv : List (ℕ × ℕ)) (ρ μ σ' : List F) (base : ℕ) : F :=
  E2V.sumF (iv.map fun ab ↦ E2V.msEvalF ρ μ σ' base ab.2 - E2V.msEvalF ρ μ σ' base (ab.1 - 1))

/-- `Π_{k = hs}^{w−1} (1 − r_k)`: the tape point's mass on the rows below `2^hs` of a `2^w` half. -/
def eTailF (hs w : ℕ) (r : List F) : F := E2V.prodF (((r.take w).drop hs).map fun c ↦ 1 - c)

/-- `z*_l`: lane `l` of `Keccak-f(0)` (the output of every zero-input row). -/
def zStarK (l : ℕ) : K := laneWord (keccakF1600 Lvm.KSponge.zeroSt) l

/-- **T1's output values** at the tape point `r` (`w + 1` coordinates) from the 50 scalars `ab = a ‖ b`:
`v_l = (1 − r_w)·a_l + r_w·(e·b_l + (1 − e)·z*_l)`, `e = Π_{k=hs}^{w−1}(1 − r_k)`. -/
def t1ValsF (w hs : ℕ) (r ab : List F) : List F :=
  (List.range 25).map fun l ↦
    (1 - r.getD w 0) * ab.getD l 0 +
      r.getD w 0 * (eTailF hs w r * ab.getD (25 + l) 0 + (1 - eTailF hs w r) * kF (zStarK l))

/-- **UTAPE-STMT 6a** (owner V): T-K's interval kernel at `F` (`sum_msIntK`'s port: `K̃_ks` is two of them). -/
theorem sum_msIntKF (ρ μ σ : List F) (base a b : ℕ) (h4 : 4 ≤ σ.length) (hρ : σ.length - 4 ≤ ρ.length)
    (hb : 2 ^ σ.length ∣ base) (ha : 1 ≤ a) (hab : a ≤ b) (hbw : b < 2 ^ σ.length) :
    ∑ x ∈ range (2 ^ σ.length), E2V.eqAtF σ x * msIntKF ρ μ base a b x =
      E2V.msEvalF ρ μ σ base b - E2V.msEvalF ρ μ σ base (a - 1) := by
  have hk : ∀ x, msIntKF ρ μ base a b x = E2V.msKF ρ μ base b x - E2V.msKF ρ μ base (a - 1) x := fun x ↦ by
    unfold msIntKF E2V.msKF
    by_cases h1 : x + 1 ≤ b
    · by_cases h2 : x + 1 ≤ a - 1
      · rw [if_neg (by (clear * - h2 ha; omega)), if_pos h1, if_pos h2, sub_self]
      · rw [if_pos (by (clear * - h1 h2 ha; omega)), if_pos h1, if_neg h2, sub_zero]
    · rw [if_neg (by (clear * - h1; omega)), if_neg h1, if_neg (by (clear * - h1 hab; omega)), sub_zero]
  simp only [hk, mul_sub, Finset.sum_sub_distrib]
  rw [E2V.sum_msKF ρ μ σ base b h4 hρ hb hbw,
    E2V.sum_msKF ρ μ σ base (a - 1) h4 hρ hb (by (clear * - hab hbw; omega))]

/-- **UTAPE-STMT 6b** (owner V): T-K's `I_ks` kernel at `F` (`sum_ikK`'s port). -/
theorem sum_ikKF (ρ μ σ : List F) (base : ℕ) (h4 : 4 ≤ σ.length) (hρ : σ.length - 4 ≤ ρ.length)
    (hb : 2 ^ σ.length ∣ base) :
    ∑ x ∈ range (2 ^ σ.length), E2V.eqAtF σ x * ikKF ρ μ base x = ikEvalF ρ μ σ base := by
  obtain ⟨v, hv⟩ : ∃ v, σ.length = v + 4 := ⟨σ.length - 4, by (clear * - h4; omega)⟩
  have hσ4 : (σ.take 4).length = 4 := by simp; omega
  have hpow : 2 ^ σ.length = 2 ^ v * 16 := by rw [hv, pow_add]; norm_num
  have key : ∀ d ∈ range 16, ∀ x' ∈ range (2 ^ v),
      E2V.eqAtF σ (16 * x' + d) * ikKF ρ μ base (16 * x' + d) =
        E2V.eqAtF (σ.take 4) d * μ.getD d 0 *
          (E2V.eqAtF (ρ.take (σ.length - 4)) x' * E2V.eqAtF (σ.drop 4) x') *
          E2V.eqAtF (ρ.drop (σ.length - 4)) (base / 2 ^ σ.length) := by
    intro d hd x' hx'
    have hd' := Finset.mem_range.1 hd
    have hx'' := Finset.mem_range.1 hx'
    have hes : E2V.eqAtF σ (16 * x' + d) = E2V.eqAtF (σ.take 4) d * E2V.eqAtF (σ.drop 4) x' := by
      conv_lhs => rw [← List.take_append_drop 4 σ]
      rw [E2V.eqAtF_append, hσ4, E2V.eqAtF_mod (σ.take 4), hσ4,
        show (16 * x' + d) % 2 ^ 4 = d by norm_num; (clear * - hd'; omega),
        show (16 * x' + d) / 2 ^ 4 = x' by norm_num; (clear * - hd'; omega)]
    rw [ikKF, E2V.iotaF_block ρ μ σ.length base _ h4 hρ hb (by (clear * - hpow hd' hx''; omega)), hes,
      show (16 * x' + d) / 16 = x' by (clear * - hd'; omega),
      show (16 * x' + d) % 16 = d by (clear * - hd'; omega)]
    ring
  rw [ikEvalF, E2V.sumF_map_range, show σ.length - 4 = v by (clear * - hv; omega), Finset.sum_mul_sum,
    Finset.sum_mul]
  rw [show σ.length - 4 = v by (clear * - hv; omega)] at key
  conv_lhs => rw [hpow, E2V.sum_range_mulB, Finset.sum_comm]
  refine Finset.sum_congr rfl fun d hd ↦ ?_
  rw [Finset.sum_mul]
  exact Finset.sum_congr rfl fun x' hx' ↦ key d hd x' hx'

end Kernels

/-! ## The S2GU front's programs -/

variable {b : ℕ}

/-- `cont`'s intervals for a child trace of `b + 1` sponge blocks (lvm2 ACW RE-FREEZE RF-2: `b = B − 1` is a parameter,
S2GU's `B = spongeBlocks P20U = 3,961`, S2GA's `3,898`): the trace rows `1 … b` and the key leaf's rows
`8,080 … 8,110` (`ks_split + 399 + 1 …`, 31 rows). -/
def contIvB (b : ℕ) : List (ℕ × ℕ) := [(1, b), (8080, 8110)]

/-- `cont` at S2GU as a row predicate. -/
def contB (b : ℕ) (j : ℕ) : Bool := (contIvB b).any fun ab ↦ decide (ab.1 ≤ j ∧ j ≤ ab.2)

/-- `Y`'s slot weights: `ω(64l + z)` on slot `l < 25`. -/
def yWF (ω : List E2) (o z : ℕ) : E2 := if o < 25 then ω.getD (64 * o + z) 0 else 0

/-- `M`'s slot weights: `ω(64l + z)` on column `l < 17`. -/
def mWF (ω : List E2) (o z : ℕ) : E2 := if o < 17 then ω.getD (64 * o + z) 0 else 0

/-- What the S2GU wire returns: `σ` and the final claim, `[g_D, g_Y, g_M]`, the three slot reductions. -/
structure WireOutU where
  sc : List E2 × E2
  g : List E2
  d : SlotOutE2
  y : SlotOutE2
  m : SlotOutE2

/-- **The S2GU wire** (`ref/utape.py`'s `CHwire`, COMMON's T3–T4) on the GKR's input claim. -/
def wireProgB (b : ℕ) (s : RecursionFast.Digest) (n : ℕ) (claim : KClaim E2) : VerifierProgram WireOutU :=
  sumcheckE2 gC2 (E2V.wireTargetF s n claim) 3 (List.replicate 20 none) >>= fun sc ↦
  e2Reads 3 >>= fun g ↦
  VerifierProgram.require (sc.2 = E2V.msEvalF claim.point claim.mu sc.1 0 (n - 1) * g.getD 0 0 +
    eTailF 13 20 sc.1 * (kksF (contIvB b) claim.point claim.mu (sc.1.take 13) (2 ^ 20) * g.getD 1 0 +
      ikEvalF claim.point claim.mu (sc.1.take 13) (2 ^ 20) * g.getD 2 0)) >>= fun _ ↦
  slotProgE2 2 1 0 (E2V.dWF claim.weights) sc.1 (g.getD 0 0) >>= fun d ↦
  slotProgE2 5 5 22 (yWF claim.weights) (sc.1.take 13) (g.getD 1 0) >>= fun y ↦
  slotProgE2 5 4 10 (mWF claim.weights) (sc.1.take 13 ++ [0]) (g.getD 2 0) >>= fun m ↦
  pure ⟨sc, g, d, y, m⟩

/-- What the S2GU tape returns: `r` (21), the 50 scalars, the input claim, the wire. -/
abbrev TapeOutU : Type := List E2 × List E2 × KClaim E2 × WireOutU

/-- **The S2GU tape** (`ref/utape.py`'s `CHtape` and `CHwire`): the separator, `r_0 … r_19`, `a ‖ b`, `r_20`, the GKR
of `Shape {21, 24}` on `t1ValsF`, `n`'s range, the wire. -/
def tapeProgB (b : ℕ) (s : RecursionFast.Digest) (n : ℕ) : VerifierProgram TapeOutU :=
  e2Sep >>= fun _ ↦
  e2Samples gC1 20 >>= fun r ↦
  e2Reads 50 >>= fun ab ↦
  e2Samples gC1 1 >>= fun r20 ↦
  tapeGkrE2 21 (r ++ r20) (t1ValsF 20 13 (r ++ r20) ab) >>= fun claim ↦
  VerifierProgram.require (1 ≤ n ∧ n ≤ 2 ^ 20) >>= fun _ ↦
  wireProgB b s n claim >>= fun wo ↦
  pure (r ++ r20, ab, claim, wo)

/-! ## The columns of a `C_main` candidate at S2GU -/

/-- `D` (lane `l` of row `x` at `x + 2^20·l`). -/
def dU (col : ℕ → K) : ℕ → ℕ → K := dOf 20 0 col

/-- `Y` (`KS13`'s output lane `l` of row `j` at `Y + l·2^13 + j`, `Y = 22·2^18`). -/
def yU (col : ℕ → K) (j l : ℕ) : K := col (22 * 2 ^ 18 + l * 2 ^ 13 + j)

/-- `Msg` (message lane `l` of row `j`, the stream block's column `l` at `S + l·2^14 + j`, `S = 10·2^19`). -/
def msgU (col : ℕ → K) (j l : ℕ) : K := col (10 * 2 ^ 19 + l * 2 ^ 14 + j)

/-- **The S2GU tape's virtual inputs** on a `C_main` column. -/
def tapeInB (b : ℕ) (s : RecursionFast.Digest) (n : ℕ) (col : ℕ → K) : ℕ → KeccakState :=
  tapeIn 20 13 s n (dU col) (yU col) (msgU col) (contB b)

/-- **What the S2GU tape proves**: the chain half's digest lanes and every sponge row's 25 lanes are the
permutation's outputs on the virtual inputs (`TapeOut` and `TapeRel.sponge` at `w = 20`, `hs = 13`). -/
def TapeRelB (b : ℕ) (s : RecursionFast.Digest) (n : ℕ) (col : ℕ → K) : Prop :=
  TapeOut 20 s n (dU col) ∧
    ∀ j < 2 ^ 13, ∀ l < 25, yU col j l = laneWord (keccakF1600 (tapeInB b s n col (2 ^ 20 + j))) l

/-- T1's tied claims on the `Y` block: `Ỹ_l(r_{<13}) = b_l` (`l < 25`). -/
def TiedYF (Y : ℕ → ℕ → K) (r ab : List E2) : Prop :=
  ∀ l < 25, E2V.stepMleF 13 (r.take 13) (fun j ↦ Y j l) = ab.getD (25 + l) 0

/-! ## The S2GU wire's algebra (UT-V; proof help for STMT 7–9) -/

section WireAlgU

/-- `e`, the mass of a tape point's sponge rows, is `eq(r_{13..19}, 0)`. -/
theorem eTailF_eq (r : List E2) : eTailF 13 20 r = E2V.eqAtF ((r.take 20).drop 13) 0 := by
  have g : ∀ (c : List E2) (acc : E2), (c.map fun x ↦ 1 - x).foldl (· * ·) acc = acc * E2V.eqAtF c 0 := by
    intro c
    induction c with
    | nil => intro acc; simp [E2V.eqAtF]
    | cons x c ih =>
      intro acc
      rw [List.map_cons, List.foldl_cons, ih, E2V.eqAtF, if_neg (by (clear * - ; omega)), CharTwo.sub_eq_add,
        Nat.zero_div]
      ring
  rw [eTailF, E2V.prodF, g, one_mul]

/-- `G_Y(x) = Σ_{q<1600} ω_q·bit_q(Y[x])`. -/
def gYTF (ω : List E2) (Y : ℕ → ℕ → K) (x : ℕ) : E2 :=
  ∑ q ∈ range 1600, ω.getD q 0 * bitF (Lvm.KG.rowBits Y x q)

/-- `G_M(x) = Σ_{q<1088} ω_q·bit_q(Msg[x])` (the rate). -/
def gMTF (ω : List E2) (M : ℕ → ℕ → K) (x : ℕ) : E2 :=
  ∑ q ∈ range 1088, ω.getD q 0 * bitF (Lvm.KG.rowBits M x q)

/-- `K_ks(x) = [x + 1 < 2^13]·cont_{x+1}·ι(2^20 + x + 1)`. -/
def kksTB (b : ℕ) (ρ μ : List E2) (x : ℕ) : E2 :=
  if x + 1 < 2 ^ 13 ∧ contB b (x + 1) then E2V.iotaF ρ μ (2 ^ 20 + x + 1) else 0

/-- `I_ks(x) = [x < 2^13]·ι(2^20 + x)`. -/
def ikTF (ρ μ : List E2) (x : ℕ) : E2 := if x < 2 ^ 13 then E2V.iotaF ρ μ (2 ^ 20 + x) else 0

/-- A sponge row's pairing: the predecessor's 1600 bits if it continues, and its 1088 message bits
(`omegaDot_ks` at `E2`). -/
theorem omegaDotF_ks (ω : List E2) (Y Msg : ℕ → ℕ → K) (cont : ℕ → Bool) {j : ℕ} (hj : j < 2 ^ 13) :
    E2V.omegaDotF ω (LeanVM.Protocol.KeccakGkr.inState 13 (Lvm.KG.ksVirt 13 Y Msg cont) 0 j) =
      (if cont j then gYTF ω Y (j - 1) else 0) + gMTF ω Msg j := by
  have hq : ∀ q < 1600, (bitF (LeanVM.Protocol.KeccakGkr.sbit
      (LeanVM.Protocol.KeccakGkr.inState 13 (Lvm.KG.ksVirt 13 Y Msg cont) 0 j) q) : E2) =
      (if cont j then bitF (Lvm.KG.rowBits Y (j - 1) q) else 0) +
        (if q < 1088 then bitF (Lvm.KG.rowBits Msg j q) else 0) := by
    intro q hq
    rw [← Lvm.KG.stBit_eq_sbit _ hq, Lvm.KG.stBit_inState 13 _ j hq, Lvm.KG.ksVirt, Nat.add_mul_mod_self_left,
      Nat.mod_eq_of_lt hj, Nat.add_mul_div_left _ _ (Nat.two_pow_pos 13), Nat.div_eq_of_lt hj, zero_add,
      show ∀ a b : K, (a + b).toBitVec = a.toBitVec ^^^ b.toBitVec from fun _ _ ↦ rfl, BitVec.getLsbD_xor,
      E2V.bitF_xor]
    congr 1
    · split_ifs
      · rfl
      · simp [BF64.toBitVec_zero, bitF]
    · by_cases h17 : q / 64 < 17
      · rw [if_pos h17, if_pos (by (clear * - h17 hq; omega))]
        rfl
      · rw [if_neg h17, if_neg (by (clear * - h17; omega)), BF64.toBitVec_zero, BitVec.getLsbD_zero]
        simp [bitF]
  rw [E2V.omegaDotF, Finset.sum_congr rfl fun q hq' ↦ by rw [hq q (Finset.mem_range.1 hq'), mul_add],
    Finset.sum_add_distrib]
  refine congr (congrArg HAdd.hAdd ?_) ?_
  · split_ifs
    · rfl
    · simp
  · rw [gMTF, show 1600 = 1088 + 512 from rfl, Finset.sum_range_add,
      Finset.sum_eq_zero (s := range 512) fun q _ ↦ by rw [if_neg (by (clear * - ; omega)), mul_zero], add_zero]
    exact Finset.sum_congr rfl fun q hq' ↦ by rw [if_pos (Finset.mem_range.1 hq')]

/-- **The wiring identity at S2GU**: the input claim's sum over the 21-variable tape is the chain's constant plus
the kernel-weighted chain and sponge parts. -/
theorem wire_identityB (ρ μ ω : List E2) (s : RecursionFast.Digest) {n : ℕ} (hn : 1 ≤ n) (hN : n ≤ 2 ^ 20)
    (col : ℕ → K) :
    ∑ i ∈ range (2 ^ 21), E2V.iotaF ρ μ i * E2V.omegaDotF ω (tapeInB b s n col i) =
      E2V.iotaF ρ μ 0 * E2V.padDotF ω (Lvm.KG.digestBits s) +
        E2V.padDotF ω (fun _ ↦ false) * ∑ i ∈ range (n - 1), E2V.iotaF ρ μ (i + 1) +
        ∑ x ∈ range (2 ^ 20), (E2V.msKF ρ μ 0 (n - 1) x * E2V.gDTF ω (dU col) x +
          kksTB b ρ μ x * gYTF ω (yU col) x + ikTF ρ μ x * gMTF ω (msgU col) x) := by
  rw [show (2 : ℕ) ^ 21 = 2 ^ 20 + 2 ^ 20 by norm_num, Finset.sum_range_add]
  have hch : ∑ i ∈ range (2 ^ 20), E2V.iotaF ρ μ i * E2V.omegaDotF ω (tapeInB b s n col i) =
      ∑ i ∈ range (2 ^ 20), E2V.iotaF ρ μ i * E2V.omegaDotF ω (chainIn s n (dU col) i) :=
    Finset.sum_congr rfl fun i hi ↦ by rw [tapeInB, tapeIn, if_pos (Finset.mem_range.1 hi)]
  let Yp : ℕ → E2 := fun j ↦
    if j < 2 ^ 13 ∧ contB b j then E2V.iotaF ρ μ (2 ^ 20 + j) * gYTF ω (yU col) (j - 1) else 0
  let Mp : ℕ → E2 := fun j ↦ if j < 2 ^ 13 then E2V.iotaF ρ μ (2 ^ 20 + j) * gMTF ω (msgU col) j else 0
  have hrow : ∀ j, E2V.iotaF ρ μ (2 ^ 20 + j) * E2V.omegaDotF ω (tapeInB b s n col (2 ^ 20 + j)) = Yp j + Mp j := by
    intro j
    rw [tapeInB, tapeIn, if_neg (by (clear * - ; omega)), Nat.add_sub_cancel_left]
    by_cases hj : j < 2 ^ 13
    · rw [if_pos hj, omegaDotF_ks _ _ _ _ hj]
      simp only [Yp, Mp, hj, true_and, if_true]
      split_ifs <;> ring
    · rw [if_neg hj, E2V.omegaDotF_zero, mul_zero]
      simp only [Yp, Mp]
      rw [if_neg (fun h ↦ hj h.1), if_neg hj, add_zero]
  have hY : ∑ j ∈ range (2 ^ 20), Yp j = ∑ x ∈ range (2 ^ 20), kksTB b ρ μ x * gYTF ω (yU col) x := by
    have key : ∀ M : ℕ, 2 ^ 13 ≤ M →
        ∑ j ∈ range (M + 1), Yp j = ∑ x ∈ range (M + 1), kksTB b ρ μ x * gYTF ω (yU col) x := by
      intro M hM
      rw [Finset.sum_range_succ', Finset.sum_range_succ]
      have h0 : Yp 0 = 0 := by
        simp only [Yp]
        rw [if_neg (fun h ↦ by simp [contB, contIvB] at h)]
      have hN0 : kksTB b ρ μ M * gYTF ω (yU col) M = 0 := by
        rw [kksTB, if_neg (fun h ↦ by (clear * - h hM; omega)), zero_mul]
      rw [h0, hN0]
      refine congrArg (· + 0) (Finset.sum_congr rfl fun x _ ↦ ?_)
      simp only [Yp, kksTB, Nat.add_sub_cancel, ← Nat.add_assoc]
      split_ifs <;> simp
    have e : (2 : ℕ) ^ 20 = (2 ^ 20 - 1) + 1 := by norm_num
    rw [show range (2 ^ 20) = range ((2 ^ 20 - 1) + 1) from congrArg range e]
    exact key _ (by norm_num)
  have hM : ∑ j ∈ range (2 ^ 20), Mp j = ∑ x ∈ range (2 ^ 20), ikTF ρ μ x * gMTF ω (msgU col) x :=
    Finset.sum_congr rfl fun x _ ↦ by
      simp only [Mp, ikTF]
      split_ifs <;> simp
  rw [hch, E2V.wire_identity_chF ρ μ ω s (dU col) hn hN, Finset.sum_congr rfl fun j _ ↦ hrow j,
    Finset.sum_add_distrib, hY, hM]
  simp only [Finset.sum_add_distrib]
  ring

/-- A table supported below `2^k` (`extE_low` at `E2`). -/
theorem extF_low {w k : ℕ} {σ : List E2} (hσ : σ.length = w) (hk : k ≤ w) (f : ℕ → E2)
    (hf : ∀ x, 2 ^ k ≤ x → f x = 0) :
    E2V.extF w σ f = E2V.eqAtF (σ.drop k) 0 * E2V.extF k (σ.take k) f := by
  have hl : (σ.take k).length = k := by simp [hσ]; (clear * - hσ hk; omega)
  have e := E2V.col_splitF (s := σ.drop k) hl f
  rw [List.take_append_drop, show k + (σ.drop k).length = w by simp [hσ]; (clear * - hk; omega)] at e
  rw [E2V.extF, e, Finset.sum_eq_single 0]
  · simp [E2V.extF]
  · intro o _ ho
    rw [Finset.sum_eq_zero fun x _ ↦ by
      rw [hf _ (by have : 1 ≤ o := Nat.pos_of_ne_zero ho; nlinarith [Nat.two_pow_pos k]), mul_zero],
      mul_zero]
  · intro h; exact absurd (Finset.mem_range.2 (Nat.two_pow_pos _)) h

/-- A periodic table (`extE_mod` at `E2`). -/
theorem extF_mod {w k : ℕ} {σ : List E2} (hσ : σ.length = w) (hk : k ≤ w) (f : ℕ → E2) :
    E2V.extF w σ (fun x ↦ f (x % 2 ^ k)) = E2V.extF k (σ.take k) f := by
  have hl : (σ.take k).length = k := by simp [hσ]; (clear * - hσ hk; omega)
  have e := E2V.col_splitF (s := σ.drop k) hl (fun x ↦ f (x % 2 ^ k))
  rw [List.take_append_drop, show k + (σ.drop k).length = w by simp [hσ]; (clear * - hk; omega)] at e
  rw [E2V.extF, e]
  have e' : ∀ o, ∑ x ∈ range (2 ^ k), E2V.eqAtF (σ.take k) x * f ((x + 2 ^ k * o) % 2 ^ k) =
      E2V.extF k (σ.take k) f := fun o ↦ Finset.sum_congr rfl fun x hx ↦ by
    rw [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt (Finset.mem_range.1 hx)]
  simp only [e', ← Finset.sum_mul, E2V.sum_eqAtF, one_mul]

/-- `cont` at S2GU as two comparisons. -/
theorem contB_ivl (j : ℕ) : contB b j = true ↔ (1 ≤ j ∧ j ≤ b) ∨ (8080 ≤ j ∧ j ≤ 8110) := by
  simp only [contB, contIvB, List.any_cons, List.any_nil, Bool.or_false, Bool.or_eq_true, decide_eq_true_eq]

/-- `K_ks` as the two intervals' kernels. -/
theorem kksTB_split (hcb : 1 ≤ b ∧ b < 8080) (ρ μ : List E2) (x : ℕ) :
    kksTB b ρ μ x = msIntKF ρ μ (2 ^ 20) 1 b x + msIntKF ρ μ (2 ^ 20) 8080 8110 x := by
  have h13 : (2 : ℕ) ^ 13 = 8192 := by norm_num
  unfold kksTB msIntKF
  by_cases h1 : 1 ≤ x + 1 ∧ x + 1 ≤ b
  · rw [if_pos ⟨by rw [h13]; (clear * - h1 hcb; omega), (contB_ivl _).2 (Or.inl h1)⟩, if_pos h1,
      if_neg (by (clear * - h1 hcb; omega)), add_zero]
  · by_cases h2 : 8080 ≤ x + 1 ∧ x + 1 ≤ 8110
    · rw [if_pos ⟨by rw [h13]; (clear * - h2 hcb; omega), (contB_ivl _).2 (Or.inr h2)⟩, if_neg h1, if_pos h2,
        zero_add]
    · rw [if_neg (fun h ↦ (((contB_ivl _).1 h.2).elim h1 h2)), if_neg h1, if_neg h2, add_zero]

/-- `K̃_ks` is `K_ks`'s extension. -/
theorem kksF_eqB (hcb : 1 ≤ b ∧ b < 8080) (ρ μ σ' : List E2) (hσ : σ'.length = 13) (hρ : 9 ≤ ρ.length) :
    kksF (contIvB b) ρ μ σ' (2 ^ 20) = E2V.extF 13 σ' (kksTB b ρ μ) := by
  have h4 : 4 ≤ σ'.length := by rw [hσ]; norm_num
  have hρ' : σ'.length - 4 ≤ ρ.length := by rw [hσ]; exact hρ
  have hb : 2 ^ σ'.length ∣ 2 ^ 20 := Nat.pow_dvd_pow 2 (by rw [hσ]; norm_num)
  have hb1 : b < 2 ^ σ'.length := by rw [hσ]; have := hcb.2; norm_num; omega
  have hb2 : (8110 : ℕ) < 2 ^ σ'.length := by rw [hσ]; norm_num
  have i1 := sum_msIntKF ρ μ σ' (2 ^ 20) 1 b h4 hρ' hb le_rfl hcb.1 hb1
  have i2 := sum_msIntKF ρ μ σ' (2 ^ 20) 8080 8110 h4 hρ' hb (by norm_num) (by norm_num) hb2
  rw [hσ] at i1 i2
  have hk : E2V.extF 13 σ' (kksTB b ρ μ) =
      (∑ x ∈ range (2 ^ 13), E2V.eqAtF σ' x * msIntKF ρ μ (2 ^ 20) 1 b x) +
        ∑ x ∈ range (2 ^ 13), E2V.eqAtF σ' x * msIntKF ρ μ (2 ^ 20) 8080 8110 x := by
    rw [E2V.extF, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun x _ ↦ by rw [kksTB_split hcb, mul_add]
  rw [hk, i1, i2, kksF, contIvB, List.map_cons, List.map_cons, List.map_nil, E2V.sumF, List.foldl_cons,
    List.foldl_cons, List.foldl_nil, zero_add]

/-- `Ĩ_ks` is `I_ks`'s extension. -/
theorem ikEvalF_eq (ρ μ σ' : List E2) (hσ : σ'.length = 13) (hρ : 9 ≤ ρ.length) :
    ikEvalF ρ μ σ' (2 ^ 20) = E2V.extF 13 σ' (ikTF ρ μ) := by
  rw [← sum_ikKF ρ μ σ' (2 ^ 20) (by rw [hσ]; norm_num) (by rw [hσ]; exact hρ)
    (Nat.pow_dvd_pow 2 (by rw [hσ]; norm_num)), E2V.extF, hσ]
  exact Finset.sum_congr rfl fun x hx ↦ by rw [ikTF, if_pos (Finset.mem_range.1 hx), ikKF]

/-- Rows' pairing over `c` lanes, lane by lane and bit by bit (`extE_rows` at `E2`). -/
theorem extF_rows (k c : ℕ) (ω pt : List E2) (G : ℕ → ℕ → K) :
    E2V.extF k pt (fun x ↦ ∑ q ∈ range (c * 64), ω.getD q 0 * bitF (Lvm.KG.rowBits G x q)) =
      ∑ l ∈ range c, ∑ z ∈ range 64, ω.getD (64 * l + z) 0 *
        ∑ x ∈ range (2 ^ k), E2V.eqAtF pt x * bitF ((G x l).toBitVec.getLsbD z) := by
  simp only [E2V.extF, Finset.mul_sum]
  rw [Finset.sum_comm]
  simp only [E2V.sum_range_mulB]
  refine Finset.sum_congr rfl fun l _ ↦ Finset.sum_congr rfl fun z hz ↦ Finset.sum_congr rfl fun x _ ↦ ?_
  have hz' := Finset.mem_range.1 hz
  simp only [Lvm.KG.rowBits, show (64 * l + z) / 64 = l by (clear * - hz'; omega),
    show (64 * l + z) % 64 = z by (clear * - hz'; omega)]
  ring

/-- **`G̃_Y` is the `Y` block's slot sum** (the `Y` block at `22·2^18`, lane `l` in slot `l`). -/
theorem gY_slotF (ω : List E2) (col : ℕ → K) (pt : List E2) :
    E2V.extF 13 pt (gYTF ω (yU col)) = slotSumF 13 5 22 (yWF ω) col pt := by
  have e1 : gYTF ω (yU col) = fun x ↦ ∑ q ∈ range (25 * 64), ω.getD q 0 * bitF (Lvm.KG.rowBits (yU col) x q) := by
    funext x
    rw [gYTF, show (1600 : ℕ) = 25 * 64 by norm_num]
  rw [e1, extF_rows, slotSumF, show (2 : ℕ) ^ 5 = 25 + 7 by norm_num, Finset.sum_range_add,
    Finset.sum_eq_zero (s := range 7) fun o _ ↦ Finset.sum_eq_zero fun z _ ↦ by
      rw [yWF, if_neg (by (clear * - ; omega)), zero_mul], add_zero]
  refine Finset.sum_congr rfl fun o ho ↦ Finset.sum_congr rfl fun z _ ↦ ?_
  rw [yWF, if_pos (Finset.mem_range.1 ho), slotSliceF]
  refine congrArg (ω.getD (64 * o + z) 0 * ·) ?_
  refine Finset.sum_congr rfl fun x _ ↦ ?_
  rw [yU, show 22 * 2 ^ 18 + o * 2 ^ 13 + x = x + 2 ^ 13 * (o + 2 ^ 5 * 22) by ring]

/-- **`G̃_M` is the stream block's slot sum at `(pt, 0)`** (the stream block at `10·2^19`, message lane `l` in
column `l`, rows below `2^13`). -/
theorem gM_slotF (ω : List E2) (col : ℕ → K) (pt : List E2) (hpt : pt.length = 13) :
    E2V.extF 13 pt (gMTF ω (msgU col)) = slotSumF 14 5 10 (mWF ω) col (pt ++ [0]) := by
  have hsl : ∀ o z, slotSliceF 14 5 10 col (pt ++ [0]) o z =
      ∑ x ∈ range (2 ^ 13), E2V.eqAtF pt x * bitF ((col (x + 2 ^ 14 * (o + 2 ^ 5 * 10))).toBitVec.getLsbD z) := by
    intro o z
    rw [slotSliceF]
    generalize 2 ^ 14 * (o + 2 ^ 5 * 10) = c
    have e := E2V.col_splitF (s := [(0 : E2)]) hpt (fun n ↦ bitF ((col (n + c)).toBitVec.getLsbD z))
    rw [show (2 : ℕ) ^ 14 = 2 ^ (13 + [(0 : E2)].length) from rfl, e,
      show (2 : ℕ) ^ [(0 : E2)].length = 2 from rfl, Finset.sum_range_succ, Finset.sum_range_one]
    simp [E2V.eqAtF]
  have e1 : gMTF ω (msgU col) =
      fun x ↦ ∑ q ∈ range (17 * 64), ω.getD q 0 * bitF (Lvm.KG.rowBits (msgU col) x q) := by
    funext x
    rw [gMTF, show (1088 : ℕ) = 17 * 64 by norm_num]
  rw [e1, extF_rows, slotSumF, show (2 : ℕ) ^ 5 = 17 + 15 by norm_num, Finset.sum_range_add,
    Finset.sum_eq_zero (s := range 15) fun o _ ↦ Finset.sum_eq_zero fun z _ ↦ by
      rw [mWF, if_neg (by (clear * - ; omega)), zero_mul], add_zero]
  refine Finset.sum_congr rfl fun o ho ↦ Finset.sum_congr rfl fun z _ ↦ ?_
  rw [mWF, if_pos (Finset.mem_range.1 ho), hsl]
  refine congrArg (ω.getD (64 * o + z) 0 * ·) ?_
  refine Finset.sum_congr rfl fun x _ ↦ ?_
  rw [msgU, show 10 * 2 ^ 19 + o * 2 ^ 14 + x = x + 2 ^ 14 * (o + 2 ^ 5 * 10) by ring]

/-- The S2GU wire sumcheck's family; the sponge data are read periodically. -/
noncomputable def wireUFB (b : ℕ) (ρ μ ω : List E2) (m : ℕ) (col : ℕ → K) (acc : List E2) : E2 :=
  cubeSumF (fun pt ↦ E2V.extF 20 pt (E2V.msKF ρ μ 0 m) * E2V.extF 20 pt (E2V.gDTF ω (dU col)) +
    E2V.extF 20 pt (kksTB b ρ μ) * E2V.extF 20 pt (fun x ↦ gYTF ω (yU col) (x % 2 ^ 13)) +
    E2V.extF 20 pt (ikTF ρ μ) * E2V.extF 20 pt (fun x ↦ gMTF ω (msgU col) (x % 2 ^ 13))) 20 acc

theorem wireUFB_plain {β : Type} (ρ μ ω : List E2) (m : ℕ) (col : β → ℕ → K) :
    PlainFamilyF (fun q acc ↦ wireUFB b ρ μ ω m (col q) acc) 2 20 :=
  cube_plainFamilyF _ 20 fun _ pre post ↦
    PolyLEF.add (PolyLEF.add (polyLEF_mle_mul _ _ _ _ pre post) (polyLEF_mle_mul _ _ _ _ pre post))
      (polyLEF_mle_mul _ _ _ _ pre post)

theorem wireUFB_nil (ρ μ ω : List E2) (m : ℕ) (col : ℕ → K) :
    wireUFB b ρ μ ω m col [] = ∑ x ∈ range (2 ^ 20), (E2V.msKF ρ μ 0 m x * E2V.gDTF ω (dU col) x +
      kksTB b ρ μ x * gYTF ω (yU col) x + ikTF ρ μ x * gMTF ω (msgU col) x) := by
  rw [wireUFB, cubeSumF_nil]
  refine Finset.sum_congr rfl fun u hu ↦ ?_
  have hu' := Finset.mem_range.1 hu
  simp only [E2V.extF, sum_eqAtF_bitsF hu']
  have hY : kksTB b ρ μ u * gYTF ω (yU col) (u % 2 ^ 13) = kksTB b ρ μ u * gYTF ω (yU col) u := by
    unfold kksTB
    split_ifs with h
    · rw [Nat.mod_eq_of_lt (by (clear * - h; omega))]
    · simp
  have hM : ikTF ρ μ u * gMTF ω (msgU col) (u % 2 ^ 13) = ikTF ρ μ u * gMTF ω (msgU col) u := by
    unfold ikTF
    split_ifs with h
    · rw [Nat.mod_eq_of_lt h]
    · simp
  rw [hY, hM]

/-- **The family's end**, in the verifier's closed forms. -/
theorem wireUFB_end (hcb : 1 ≤ b ∧ b < 8080) (ρ μ ω : List E2) {m : ℕ} (col : ℕ → K) {σ : List E2} (hσ : σ.length = 20)
    (hρ : 16 ≤ ρ.length) (hm : m < 2 ^ 20) :
    wireUFB b ρ μ ω m col σ = E2V.msEvalF ρ μ σ 0 m * E2V.extF 20 σ (E2V.gDTF ω (dU col)) +
      eTailF 13 20 σ * (kksF (contIvB b) ρ μ (σ.take 13) (2 ^ 20) * E2V.extF 13 (σ.take 13) (gYTF ω (yU col)) +
        ikEvalF ρ μ (σ.take 13) (2 ^ 20) * E2V.extF 13 (σ.take 13) (gMTF ω (msgU col))) := by
  have hσ' : (σ.take 13).length = 13 := by simp [hσ]
  rw [wireUFB, cubeSumF_full _ hσ,
    show E2V.extF 20 σ (E2V.msKF ρ μ 0 m) = E2V.msEvalF ρ μ σ 0 m by
      rw [E2V.extF, ← hσ]
      exact E2V.sum_msKF_zero ρ μ σ m (by rw [hσ]; norm_num) (by rw [hσ]; (clear * - hρ; omega))
        (by rw [hσ]; exact hm),
    extF_low (k := 13) hσ (by norm_num) (kksTB b ρ μ) (fun x hx ↦ by rw [kksTB, if_neg (by (clear * - hx; omega))]),
    extF_low (k := 13) hσ (by norm_num) (ikTF ρ μ) (fun x hx ↦ by rw [ikTF, if_neg (by (clear * - hx; omega))]),
    extF_mod (k := 13) hσ (by norm_num), extF_mod (k := 13) hσ (by norm_num),
    ← kksF_eqB hcb ρ μ _ hσ' (by (clear * - hρ; omega)), ← ikEvalF_eq ρ μ _ hσ' (by (clear * - hρ; omega)), eTailF_eq,
    List.take_of_length_le (l := σ) (i := 20) (by rw [hσ])]
  ring

/-- **The wire sumcheck's claim is the input claim** (S2GU). -/
theorem inClaim_of_wireTargetB (s : RecursionFast.Digest) {n : ℕ} (hn : 1 ≤ n) (hN : n ≤ 2 ^ 20)
    (claim : KClaim E2) (hρ : claim.point.length + 4 = 21) (col : ℕ → K)
    (hv : E2V.wireTargetF s n claim = wireUFB b claim.point claim.mu claim.weights (n - 1) col []) :
    E2V.InClaimTrueF 21 (tapeInB b s n col) claim := by
  rw [wireUFB_nil] at hv
  have hS := E2V.sum_range_iotaF_succ claim.point claim.mu (n - 1) (by rw [hρ]; (clear * - hN hn; omega))
  rw [CharTwo.sub_eq_add] at hS
  rw [E2V.InClaimTrueF, wire_identityB _ _ _ s hn hN, hS]
  rw [E2V.wireTargetF] at hv
  linear_combination hv - (E2V.iotaF claim.point claim.mu 0 * E2V.padDotF claim.weights
    (Lvm.KG.digestBits s) + E2V.padDotF claim.weights (fun _ ↦ false) *
      (E2V.thrEvalF claim.point claim.mu (n - 1) + E2V.iotaF claim.point claim.mu 0)) *
      CharTwo.two_eq_zero (R := E2)

end WireAlgU


variable {β : Type} {C : List Ev → Set β} [Finite β] {T : ℝ≥0∞}

/-! ## STMT 7: the S2GU wire as a specification -/

section WireSpecU


open Classical in
/-- The witness of `wireSpecB` (`wireSpecE2W` with the sponge terms and three slot reductions). -/
noncomputable def wireSpecBW (hcb : 1 ≤ b ∧ b < 8080) (hst : Stable C) (hcard : ∀ h, (C h).ncard ≤ 1) (s : RecursionFast.Digest) {n : ℕ}
    (hn : 1 ≤ n) (hN : n ≤ 2 ^ 20) (claim : KClaim E2) (hρ : claim.point.length + 4 = 21)
    (colM : β → ℕ → K) (R : β → Prop) (hrT : (∑ _i ∈ range 7, errE 1) + T ≤ εS) :
    Spec (wireProgB b s n claim)
      (Doomed C (fun q ↦ E2V.InClaimTrueF 21 (tapeInB b s n (colM q)) claim ∧ R q))
      (fun out hist ↦ out.sc.1.length = 20 ∧ out.d.sl.1.length = 2 ∧ out.y.sl.1.length = 5 ∧
        out.m.sl.1.length = 5 ∧
        Doomed C (fun q ↦ RowColTrue 23 (colM q) out.d.row ∧ RowColTrue 23 (colM q) out.y.row ∧
          RowColTrue 23 (colM q) out.m.row ∧ R q) hist) εS 0 T :=
  have hρ' : 16 ≤ claim.point.length := by (clear * - hρ; omega)
  have hr0 : (∑ _i ∈ range 7, errE 1) + (0 : ℝ≥0∞) ≤ εS := le_trans (by rw [add_zero]; exact le_self_add) hrT
  ((sumcheckGSpec (T := 0) (L₀ := 1) hst hcard R
      (wireUFB_plain claim.point claim.mu claim.weights (n - 1) colM) (count := 3)
      (by norm_num) (by norm_num) (g := gC2) (by norm_num) errG_c2 20 [] (E2V.wireTargetF s n claim) (by simp)).mono
    (fun _ hd ↦ Doomed.mono hd fun q ⟨hv, hR⟩ ↦ ⟨inClaim_of_wireTargetB s hn hN claim hρ (colM q) hv, hR⟩)
    (fun _ _ h ↦ h) le_rfl le_rfl le_rfl).bind' fun sc ↦
  if hs : sc.1.length = 20 then
    have hs13 : (sc.1.take 13).length = 13 := by simp [hs]
    have hs14 : (sc.1.take 13 ++ [(0 : E2)]).length = 14 := by simp [hs]
    ((e2ReadsSpec (T := 0) hst (fun q ↦ sc.2 = wireUFB b claim.point claim.mu claim.weights (n - 1) (colM q)
        ([] ++ sc.1) ∧ R q) zero_le 2).mono
      (fun _ hd ↦ hd.2) (fun _ _ h ↦ h) le_rfl le_rfl le_rfl).bind' fun g ↦
    (Spec.require (Pre := fun hist ↦ g.length = 2 + 1 ∧ Doomed C (fun q ↦ sc.2 =
        wireUFB b claim.point claim.mu claim.weights (n - 1) (colM q) ([] ++ sc.1) ∧ R q) hist)
      (Post := fun _ hist ↦ Doomed C (fun q ↦
        g.getD 0 0 = slotSumF 20 2 0 (E2V.dWF claim.weights) (colM q) sc.1 ∧
          ((g.getD 1 0 = slotSumF 13 5 22 (yWF claim.weights) (colM q) (sc.1.take 13) ∧
            g.getD 2 0 = slotSumF 14 5 10 (mWF claim.weights) (colM q) (sc.1.take 13 ++ [0])) ∧ R q)) hist)
      (fun _ hd hcond ↦ Doomed.mono hd.2 fun q hq ↦ ⟨by
        rw [List.nil_append, wireUFB_end hcb claim.point claim.mu claim.weights (colM q) hs hρ'
            (by (clear * - hN hn; omega)),
          show E2V.extF 20 sc.1 (E2V.gDTF claim.weights (dU (colM q))) =
            slotSumF 20 2 0 (E2V.dWF claim.weights) (colM q) sc.1 from E2V.gD_slotF 20 0 _ _ _,
          gY_slotF, gM_slotF _ _ _ hs13, hcond, hq.1, hq.2.1.1, hq.2.1.2], hq.2.2⟩)).bind' fun _ ↦
    (slotSpecE2W (T := 0) hst hcard (k := 20) (b := 2) (sb := 1) (blk := 0) (m := 23) rfl (by norm_num)
        (E2V.dWF claim.weights) colM
        (fun q ↦ (g.getD 1 0 = slotSumF 13 5 22 (yWF claim.weights) (colM q) (sc.1.take 13) ∧
          g.getD 2 0 = slotSumF 14 5 10 (mWF claim.weights) (colM q) (sc.1.take 13 ++ [0])) ∧ R q)
        hs (g.getD 0 0) hr0).bind' fun d ↦
    if hd2 : d.sl.1.length = 2 then
    ((slotSpecE2W (T := 0) hst hcard (k := 13) (b := 5) (sb := 5) (blk := 22) (m := 23) rfl (by norm_num)
        (yWF claim.weights) colM
        (fun q ↦ RowColTrue 23 (colM q) d.row ∧
          g.getD 2 0 = slotSumF 14 5 10 (mWF claim.weights) (colM q) (sc.1.take 13 ++ [0]) ∧ R q)
        hs13 (g.getD 1 0) hr0).mono
      (fun _ hd ↦ Doomed.mono hd.2.2 fun q ⟨hy, hr, hm, hR⟩ ↦ ⟨hr, ⟨hy, hm⟩, hR⟩)
      (fun _ _ h ↦ h) le_rfl le_rfl le_rfl).bind' fun y ↦
    if hy5 : y.sl.1.length = 5 then
    ((slotSpecE2W (T := T) hst hcard (k := 14) (b := 5) (sb := 4) (blk := 10) (m := 23) rfl (by norm_num)
        (mWF claim.weights) colM
        (fun q ↦ RowColTrue 23 (colM q) d.row ∧ RowColTrue 23 (colM q) y.row ∧ R q)
        hs14 (g.getD 2 0) hrT).mono
      (fun _ hd ↦ Doomed.mono hd.2.2 fun q ⟨hm, hd', hy, hR⟩ ↦ ⟨hy, hd', hm, hR⟩)
      (fun _ _ h ↦ h) le_rfl le_rfl le_rfl).bind' fun m ↦
    (Spec.ret (⟨sc, g, d, y, m⟩ : WireOutU)).mono
      (fun _ hd ↦ ⟨hs, hd2, hy5, hd.1, Doomed.mono hd.2.2 fun q ⟨hd', hy, hm, hR⟩ ↦ ⟨hm, hd', hy, hR⟩⟩)
      (fun _ _ h ↦ h) le_rfl le_rfl le_rfl
    else Spec.dead.mono (fun _ hd ↦ hy5 hd.1) (fun _ _ h ↦ h) le_rfl le_rfl le_rfl
    else Spec.dead.mono (fun _ hd ↦ hd2 hd.1) (fun _ _ h ↦ h) le_rfl le_rfl le_rfl
  else Spec.dead.mono (fun _ hd ↦ hs hd.1) (fun _ _ h ↦ h) le_rfl le_rfl le_rfl

end WireSpecU



/-- The postcondition of the S2GU tape. -/
def TapePostU (colM : β → ℕ → K) (R : β → Prop) (out : TapeOutU) (hist : List Ev) : Prop :=
  out.1.length = 21 ∧ out.2.1.length = 50 ∧ out.2.2.2.sc.1.length = 20 ∧
    Doomed C (fun q ↦ RowColTrue 23 (colM q) out.2.2.2.d.row ∧ RowColTrue 23 (colM q) out.2.2.2.y.row ∧
      RowColTrue 23 (colM q) out.2.2.2.m.row ∧ E2V.TiedDF 20 (dU (colM q)) (out.1.take 20) out.2.1 ∧
      TiedYF (yU (colM q)) out.1 out.2.1 ∧ R q) hist

/-! ## STMT 9: T1 in R-BP2's B1 order and the S2GU tape caller -/

section TapeSpecU

/-- The chain half's output lane `l` at row `x`. -/
abbrev zChB (b : ℕ) (s : RecursionFast.Digest) (n : ℕ) (col : ℕ → K) (x l : ℕ) : K :=
  laneWord (keccakF1600 (tapeInB b s n col x)) l

/-- The sponge half's output lane `l` at sponge row `x` (tape row `2^20 + x`). -/
abbrev zSpB (b : ℕ) (s : RecursionFast.Digest) (n : ℕ) (col : ℕ → K) (x l : ℕ) : K :=
  laneWord (keccakF1600 (tapeInB b s n col (2 ^ 20 + x))) l

/-- **T1's zero-test table** on 26 bits (`x < 2^20`, the half `h`, the lane `l < 32`; `i = x + 2^20·(h + 2l)`):
`D − Z` on the chain half's four digest lanes, `Y − Z` on the sponge half's 25 lanes below `2^13`. -/
def t1DeltaB (b : ℕ) (s : RecursionFast.Digest) (n : ℕ) (col : ℕ → K) (i : ℕ) : E2 :=
  if (i / 2 ^ 20) % 2 = 0 then
    (if i / 2 ^ 20 / 2 < 4 then
      kF (dU col (i % 2 ^ 20) (i / 2 ^ 20 / 2)) + kF (zChB b s n col (i % 2 ^ 20) (i / 2 ^ 20 / 2)) else 0)
  else (if i / 2 ^ 20 / 2 < 25 ∧ i % 2 ^ 20 < 2 ^ 13 then
      kF (yU col (i % 2 ^ 20) (i / 2 ^ 20 / 2)) + kF (zSpB b s n col (i % 2 ^ 20) (i / 2 ^ 20 / 2)) else 0)

theorem t1DeltaB_at (s : RecursionFast.Digest) (n : ℕ) (col : ℕ → K) {x : ℕ} (hx : x < 2 ^ 20) (h l : ℕ)
    (hh : h < 2) :
    t1DeltaB b s n col (x + 2 ^ 20 * (h + 2 * l)) =
      if h = 0 then (if l < 4 then kF (dU col x l) + kF (zChB b s n col x l) else 0)
      else (if l < 25 ∧ x < 2 ^ 13 then kF (yU col x l) + kF (zSpB b s n col x l) else 0) := by
  have e1 : (x + 2 ^ 20 * (h + 2 * l)) / 2 ^ 20 = h + 2 * l := by
    rw [Nat.add_mul_div_left _ _ (Nat.two_pow_pos 20), Nat.div_eq_of_lt hx, zero_add]
  have e2 : (x + 2 ^ 20 * (h + 2 * l)) % 2 ^ 20 = x := by rw [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hx]
  rw [t1DeltaB, e1, e2, show (h + 2 * l) / 2 = l by (clear * - hh; omega),
    show (h + 2 * l) % 2 = h by (clear * - hh; omega)]

theorem kF_eq_of_add (a b : K) (h : (kF a : E2) + kF b = 0) : a = b :=
  (algebraMap K E2).injective ((add_eq_zero_iff_eq_neg.1 h).trans (CharTwo.neg_eq _))

/-- **The table vanishing is the tape relation.** -/
theorem tapeRelB_of_zero (s : RecursionFast.Digest) (n : ℕ) (col : ℕ → K)
    (hz : ZeroOnF (t1DeltaB b s n col) [] 26) : TapeRelB b s n col := by
  rw [zeroOnF_nil] at hz
  refine ⟨fun x hx l hl ↦ ?_, fun j hj l hl ↦ ?_⟩
  · have := hz (x + 2 ^ 20 * (0 + 2 * l)) (by
      have : 2 * l < 2 ^ 6 := by (clear * - hl; omega)
      calc x + 2 ^ 20 * (0 + 2 * l) < 2 ^ 20 + 2 ^ 20 * (2 * l) := by (clear * - hx; omega)
        _ = 2 ^ 20 * (2 * l + 1) := by ring
        _ ≤ 2 ^ 20 * 2 ^ 6 := Nat.mul_le_mul_left _ this
        _ = 2 ^ 26 := by norm_num)
    rw [t1DeltaB_at s n col hx 0 l (by norm_num), if_pos rfl, if_pos hl] at this
    have e : tapeInB b s n col x = chainIn s n (dU col) x := by rw [tapeInB, tapeIn, if_pos hx]
    exact (kF_eq_of_add _ _ this).trans (by rw [zChB, e])
  · have hj20 : j < 2 ^ 20 := lt_of_lt_of_le hj (Nat.pow_le_pow_right (by norm_num) (by norm_num))
    have := hz (j + 2 ^ 20 * (1 + 2 * l)) (by
      have : 2 * l + 1 < 2 ^ 6 := by (clear * - hl; omega)
      calc j + 2 ^ 20 * (1 + 2 * l) < 2 ^ 20 + 2 ^ 20 * (1 + 2 * l) := by (clear * - hj20; omega)
        _ = 2 ^ 20 * (2 * l + 1 + 1) := by ring
        _ ≤ 2 ^ 20 * 2 ^ 6 := Nat.mul_le_mul_left _ this
        _ = 2 ^ 26 := by norm_num)
    rw [t1DeltaB_at s n col hj20 1 l (by norm_num), if_neg one_ne_zero, if_pos ⟨hl, hj⟩] at this
    exact kF_eq_of_add _ _ this

/-- The sponge half at a 20-coordinate point: `e·Z̃_sp(r_{<13}) + (1 − e)·z*` (the void rows are `Keccak-f(0)`). -/
theorem stepMle_sp (s : RecursionFast.Digest) (n : ℕ) (col : ℕ → K) {r : List E2} (hr : r.length = 20) (l : ℕ) :
    E2V.stepMleF 20 r (fun x ↦ zSpB b s n col x l) =
      eTailF 13 20 r * E2V.stepMleF 13 (r.take 13) (fun x ↦ zSpB b s n col x l) +
        (1 - eTailF 13 20 r) * kF (zStarK l) := by
  have hz : ∀ x, 2 ^ 13 ≤ x → zSpB b s n col x l = zStarK l := fun x hx ↦ by
    have e : tapeInB b s n col (2 ^ 20 + x) = Lvm.KSponge.zeroSt := by
      unfold tapeInB tapeIn
      rw [if_neg (by (clear * - ; omega)), if_neg (by (clear * - hx; omega))]
    rw [zSpB, e]; rfl
  have hsplit : ∀ x, (kF (zSpB b s n col x l) : E2) =
      (if x < 2 ^ 13 then kF (zSpB b s n col x l) - kF (zStarK l) else 0) + kF (zStarK l) := fun x ↦ by
    split_ifs with h
    · ring
    · rw [hz x (by (clear * - h; omega)), zero_add]
  have hlow := extF_low (k := 13) hr (by norm_num)
    (fun x ↦ if x < 2 ^ 13 then (kF (zSpB b s n col x l) : E2) - kF (zStarK l) else 0)
    (fun x hx ↦ by rw [if_neg (by (clear * - hx; omega))])
  have h1 := E2V.sum_eqAtF r
  have h13 := E2V.sum_eqAtF (r.take 13)
  rw [hr] at h1
  rw [show (r.take 13).length = 13 by simp [hr]] at h13
  rw [E2V.stepMleF, Finset.sum_congr rfl fun x _ ↦ by rw [hsplit x, mul_add], Finset.sum_add_distrib,
    ← Finset.sum_mul, h1, one_mul]
  rw [E2V.extF] at hlow
  rw [hlow, eTailF_eq, List.take_of_length_le (l := r) (i := 20) (by rw [hr]), E2V.extF, E2V.stepMleF]
  have e : ∑ x ∈ range (2 ^ 13), E2V.eqAtF (r.take 13) x *
      (if x < 2 ^ 13 then (kF (zSpB b s n col x l) : E2) - kF (zStarK l) else 0) =
      ∑ x ∈ range (2 ^ 13), E2V.eqAtF (r.take 13) x * kF (zSpB b s n col x l) - kF (zStarK l) := by
    rw [Finset.sum_congr rfl fun x hx ↦ by rw [if_pos (Finset.mem_range.1 hx), mul_sub], Finset.sum_sub_distrib,
      ← Finset.sum_mul, h13, one_mul]
  rw [e]
  ring

/-- **T1's gap table** on 6 bits (`h`, the lane `l`; `v = h + 2l`): the chain half's lane `l` at `r` minus `a_l`, the
sponge half's minus `e·b_l + (1 − e)·z*_l`. -/
def t1GapB (b : ℕ) (s : RecursionFast.Digest) (n : ℕ) (col : ℕ → K) (r ab : List E2) (v : ℕ) : E2 :=
  if v / 2 < 25 then
    (if v % 2 = 0 then E2V.stepMleF 20 r (fun x ↦ zChB b s n col x (v / 2)) - ab.getD (v / 2) 0
     else E2V.stepMleF 20 r (fun x ↦ zSpB b s n col x (v / 2)) -
       (eTailF 13 20 r * ab.getD (25 + v / 2) 0 + (1 - eTailF 13 20 r) * kF (zStarK (v / 2))))
  else 0

theorem t1GapB_at (s : RecursionFast.Digest) (n : ℕ) (col : ℕ → K) (r ab : List E2) (h l : ℕ) (hh : h < 2) :
    t1GapB b s n col r ab (h + 2 * l) =
      if l < 25 then
        (if h = 0 then E2V.stepMleF 20 r (fun x ↦ zChB b s n col x l) - ab.getD l 0
         else E2V.stepMleF 20 r (fun x ↦ zSpB b s n col x l) -
           (eTailF 13 20 r * ab.getD (25 + l) 0 + (1 - eTailF 13 20 r) * kF (zStarK l)))
      else 0 := by
  rw [t1GapB, show (h + 2 * l) / 2 = l by (clear * - hh; omega), show (h + 2 * l) % 2 = h by (clear * - hh; omega)]

/-- **The gap vanishing and the tied claims give T1's zero test at `r`.** -/
theorem t1DeltaB_zero_of_gap (s : RecursionFast.Digest) (n : ℕ) (col : ℕ → K) {r ab : List E2} (hr : r.length = 20)
    (hg : ZeroOnF (t1GapB b s n col r ab) [] 6) (hD : E2V.TiedDF 20 (dU col) r ab) (hY : TiedYF (yU col) r ab) :
    ZeroOnF (t1DeltaB b s n col) r 26 := by
  rw [zeroOnF_nil] at hg
  intro v hv
  rw [hr, show 26 - 20 = 6 by norm_num] at hv
  obtain ⟨h, l, hh, rfl⟩ : ∃ h l, h < 2 ∧ v = h + 2 * l := ⟨v % 2, v / 2, Nat.mod_lt _ (by norm_num), by omega⟩
  have hl32 : l < 32 := by (clear * - hv; omega)
  have hgap := hg (h + 2 * l) (by (clear * - hv; omega))
  rw [t1GapB_at s n col r ab h l hh] at hgap
  unfold foldTF
  rw [hr, Finset.sum_congr rfl fun x hx ↦ by rw [t1DeltaB_at s n col (Finset.mem_range.1 hx) h l hh]]
  by_cases h0 : h = 0
  · subst h0
    simp only [if_true]
    by_cases hl : l < 4
    · simp only [hl, if_true, mul_add, Finset.sum_add_distrib]
      have e1 := hD l hl
      rw [if_pos (by (clear * - hl; omega)), if_pos rfl, sub_eq_zero] at hgap
      simp only [E2V.stepMleF] at e1 hgap
      rw [show ∑ x ∈ range (2 ^ 20), E2V.eqAtF r x * kF (dU col x l) = _ from e1,
        show ∑ x ∈ range (2 ^ 20), E2V.eqAtF r x * kF (zChB b s n col x l) = _ from hgap]
      exact CharTwo.add_self_eq_zero _
    · simp only [hl, if_false, mul_zero, Finset.sum_const_zero]
  · have h1 : h = 1 := by (clear * - hh h0; omega)
    subst h1
    simp only [one_ne_zero, if_false]
    by_cases hl : l < 25
    · rw [if_pos hl, if_neg one_ne_zero, sub_eq_zero, stepMle_sp s n col hr] at hgap
      have hlow := extF_low (k := 13) hr (by norm_num)
        (fun x ↦ if l < 25 ∧ x < 2 ^ 13 then (kF (yU col x l) : E2) + kF (zSpB b s n col x l) else 0)
        (fun x hx ↦ by rw [if_neg (fun h ↦ by (clear * - h hx; omega))])
      have hE : E2V.eqAtF (r.drop 13) 0 = eTailF 13 20 r := by
        rw [eTailF_eq, List.take_of_length_le (l := r) (i := 20) (by rw [hr])]
      rw [E2V.extF] at hlow
      rw [hlow, hE, E2V.extF, Finset.sum_congr rfl fun x hx ↦ by
        rw [if_pos ⟨hl, Finset.mem_range.1 hx⟩, mul_add], Finset.sum_add_distrib]
      have hY' := hY l hl
      rw [E2V.stepMleF] at hY' hgap
      rw [hY']
      linear_combination hgap + (eTailF 13 20 r * ab.getD (25 + l) 0) * CharTwo.two_eq_zero (R := E2)
    · simp only [hl, false_and, if_false, mul_zero, Finset.sum_const_zero]

/-- **The GKR's output claim is T1's**: `r_20` drawn after `a ‖ b`, the 21-coordinate lane claims are `t1ValsF`'s
exactly when the gap's extension vanishes at `r_20`. -/
theorem gap_zero_of_t1 (s : RecursionFast.Digest) (n : ℕ) (col : ℕ → K) {r ab : List E2} (hr : r.length = 20)
    (c : E2) (hall : ∀ l < 25, E2V.stepMleF 21 (r ++ [c]) (fun x ↦ laneWord (keccakF1600 (tapeInB b s n col x)) l) =
      (t1ValsF 20 13 (r ++ [c]) ab).getD l 0) :
    ZeroOnF (t1GapB b s n col r ab) [c] 6 := by
  intro v hv
  rw [show 6 - [c].length = 5 from rfl] at hv
  unfold foldTF
  rw [show (2 : ℕ) ^ [c].length = 2 from rfl, Finset.sum_range_succ, Finset.sum_range_one,
    t1GapB_at s n col r ab 0 v (by norm_num), t1GapB_at s n col r ab 1 v (by norm_num)]
  simp only [E2V.eqAtF, Nat.zero_mod, show (1 : ℕ) % 2 = 1 from rfl, if_true,
    show ¬ ((0 : ℕ) = 1) from by norm_num, if_false, one_ne_zero, mul_one]
  by_cases hl : v < 25
  · rw [if_pos hl, if_pos hl]
    have h := hall v hl
    have e : E2V.stepMleF 21 (r ++ [c]) (fun x ↦ laneWord (keccakF1600 (tapeInB b s n col x)) v) =
        (1 + c) * E2V.stepMleF 20 r (fun x ↦ zChB b s n col x v) + c * E2V.stepMleF 20 r (fun x ↦ zSpB b s n col x v) := by
      unfold E2V.stepMleF
      rw [show 21 = 20 + [c].length from rfl, E2V.col_splitF (s := [c]) hr, show (2 : ℕ) ^ [c].length = 2 from rfl,
        Finset.sum_range_succ, Finset.sum_range_one]
      have s0 : ∑ x ∈ range (2 ^ 20), E2V.eqAtF r x *
          (kF (laneWord (keccakF1600 (tapeInB b s n col (x + 2 ^ 20 * 0))) v) : E2) =
          ∑ x ∈ range (2 ^ 20), E2V.eqAtF r x * kF (zChB b s n col x v) :=
        Finset.sum_congr rfl fun x _ ↦ by rw [zChB, Nat.mul_zero, Nat.add_zero]
      have s1 : ∑ x ∈ range (2 ^ 20), E2V.eqAtF r x *
          (kF (laneWord (keccakF1600 (tapeInB b s n col (x + 2 ^ 20 * 1))) v) : E2) =
          ∑ x ∈ range (2 ^ 20), E2V.eqAtF r x * kF (zSpB b s n col x v) :=
        Finset.sum_congr rfl fun x _ ↦ by rw [zSpB, show x + 2 ^ 20 * 1 = 2 ^ 20 + x by ring]
      rw [s0, s1]
      simp only [E2V.eqAtF, Nat.zero_mod, show (1 : ℕ) % 2 = 1 from rfl, if_true,
        show ¬ ((0 : ℕ) = 1) from by norm_num, if_false, mul_one]
    have hv' : (t1ValsF 20 13 (r ++ [c]) ab).getD v 0 = (1 - c) * ab.getD v 0 +
        c * (eTailF 13 20 r * ab.getD (25 + v) 0 + (1 - eTailF 13 20 r) * kF (zStarK v)) := by
      have et : eTailF 13 20 (r ++ [c]) = eTailF 13 20 r := by
        rw [eTailF, eTailF, List.take_append_of_le_length (by rw [hr])]
      have gc : (r ++ [c]).getD 20 0 = c := by
        rw [List.getD_append_right _ _ _ _ (by rw [hr])]; simp [hr]
      rw [t1ValsF, List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range hl]
      simp only [Option.map_some, Option.getD_some, gc, et]
    rw [e, hv'] at h
    rw [CharTwo.sub_eq_add] at h
    linear_combination h
  · rw [if_neg hl, if_neg hl]
    simp


open Classical in
/-- The witness of `tapeSpecB`. -/
noncomputable def tapeSpecBW (hcb : 1 ≤ b ∧ b < 8080) (hst : Stable C) (hcard : ∀ h, (C h).ncard ≤ 1) (s : RecursionFast.Digest) {n : ℕ}
    (colM : β → ℕ → K) (R : β → Prop) (hrT : (∑ _i ∈ range 7, errE 1) + T ≤ εS) :
    Spec (tapeProgB b s n) (Doomed C (fun q ↦ TapeRelB b s n (colM q) ∧ R q)) (TapePostU (C := C) colM R) εS 0 T :=
  (sepSpec (T' := 0) hst hcard _).bind' fun _ ↦
  ((zeroSpecE2 (T := 0) (L₀ := 1) hst hcard (g := gC1) (by norm_num)
      (fun q ↦ t1DeltaB b s n (colM q)) R (n := 26) (m := 19) (by norm_num) errG_c1).mono
    (fun _ hd ↦ Doomed.mono hd fun q ⟨hz, hR⟩ ↦ ⟨tapeRelB_of_zero s n _ hz, hR⟩)
    (fun _ _ h ↦ h) le_rfl le_rfl le_rfl).bind' fun r ↦
  if hr : r.length = 20 then
    ((e2ReadsSpec (T := 0) hst (fun q ↦ ZeroOnF (t1DeltaB b s n (colM q)) r 26 ∧ R q) zero_le 49).mono
      (fun _ hd ↦ by simpa using hd.2) (fun _ _ h ↦ h) le_rfl le_rfl le_rfl).bind' fun ab ↦
    if hab : ab.length = 50 then
      ((zeroSpecE2 (T := 0) (L₀ := 1) hst hcard (g := gC1) (by norm_num)
          (fun q ↦ t1GapB b s n (colM q) r ab)
          (fun q ↦ E2V.TiedDF 20 (dU (colM q)) r ab ∧ TiedYF (yU (colM q)) r ab ∧ R q)
          (n := 6) (m := 0) (by norm_num) errG_c1).mono
        (fun _ hd ↦ Doomed.mono hd.2 fun q ⟨hg, hD, hY, hR⟩ ↦ ⟨t1DeltaB_zero_of_gap s n _ hr hg hD hY, hR⟩)
        (fun _ _ h ↦ h) le_rfl le_rfl le_rfl).bind' fun r20 ↦
      if h20 : r20.length = 1 then
        have hc1 : ∃ c, r20 = [c] := List.length_eq_one_iff.1 h20
        ((tapeGkrSpecE2W (T := 0) hst hcard
            (fun q ↦ E2V.TiedDF 20 (dU (colM q)) r ab ∧ TiedYF (yU (colM q)) r ab ∧ R q)
            (fun q ↦ tapeInB b s n (colM q)) 16 (inst := r ++ r20) (output := t1ValsF 20 13 (r ++ r20) ab)
            (by simp [hr, h20]) (by simp [t1ValsF]) (by simpa using errG_c2)).mono
          (fun _ hd ↦ Doomed.mono hd.2 fun q ⟨hall, hD, hY, hR⟩ ↦ ⟨by
            obtain ⟨c, rfl⟩ := hc1
            exact gap_zero_of_t1 s n (colM q) hr c hall, hD, hY, hR⟩)
          (fun _ _ h ↦ h) le_rfl le_rfl le_rfl).bind' fun claim ↦
        if hc : claim.point.length + 4 = 21 then
          (Spec.require (T := 0) (c := 1 ≤ n ∧ n ≤ 2 ^ 20)
            (Post := fun _ hist ↦ (1 ≤ n ∧ n ≤ 2 ^ 20) ∧ (ClaimShapeF 16 claim ∧
              Doomed C (fun q ↦ ClaimTrueF (tapeStates 16 (tapeInB b s n (colM q)) 24) 16 claim ∧
                (E2V.TiedDF 20 (dU (colM q)) r ab ∧ TiedYF (yU (colM q)) r ab ∧ R q)) hist))
            (fun _ hp hcond ↦ ⟨hcond, hp⟩)).bind' fun _ ↦
          if hb : 1 ≤ n ∧ n ≤ 2 ^ 20 then
            ((wireSpecBW hcb (T := T) hst hcard s hb.1 hb.2 claim hc colM
                (fun q ↦ E2V.TiedDF 20 (dU (colM q)) r ab ∧ TiedYF (yU (colM q)) r ab ∧ R q) hrT).mono
              (fun _ hd ↦ Doomed.mono hd.2.2 fun q ⟨hin, hR⟩ ↦ ⟨claimTrue_of_inClaimF _ claim hin, hR⟩)
              (fun _ _ h ↦ h) le_rfl le_rfl le_rfl).bind' fun wo ↦
            have e20 : (r ++ r20).take 20 = r := List.take_left' hr
            have e13 : (r ++ r20).take 13 = r.take 13 := List.take_append_of_le_length (by rw [hr]; norm_num)
            (Spec.ret ((r ++ r20, ab, claim, wo) : TapeOutU)).mono
              (fun _ hd ↦ ⟨by simp [hr, h20], hab, hd.1, Doomed.mono hd.2.2.2.2 fun q ⟨h1, h2, h3, hD, hY, hR⟩ ↦
                ⟨h1, h2, h3, by rwa [e20] at hD, fun l hl ↦ by have := hY l hl; rwa [e13] at this, hR⟩⟩)
              (fun _ _ h ↦ h) le_rfl le_rfl le_rfl
          else Spec.dead.mono (fun _ hd ↦ hb hd.1) (fun _ _ h ↦ h) le_rfl le_rfl le_rfl
        else Spec.dead.mono (fun _ (hd : ClaimShapeF 16 claim ∧ _) ↦ hc (by
            obtain ⟨-, h1, -⟩ := hd.1; (clear * - h1; omega))) (fun _ _ h ↦ h) le_rfl le_rfl le_rfl
      else Spec.dead.mono (fun _ hd ↦ h20 hd.1) (fun _ _ h ↦ h) le_rfl le_rfl le_rfl
    else Spec.dead.mono (fun _ hd ↦ hab hd.1) (fun _ _ h ↦ h) le_rfl le_rfl le_rfl
  else Spec.dead.mono (fun _ hd ↦ hr (by simpa using hd.1)) (fun _ _ h ↦ h) le_rfl le_rfl le_rfl

end TapeSpecU

/-! ## S2GU's instances (RE-FREEZE RF-2: the old names at `b = 3,960`, `B = spongeBlocks P20U = 3,961`) -/

/-- `cont`'s intervals at S2GU. -/
def contIvU : List (ℕ × ℕ) := contIvB 3960

/-- **The S2GU wire.** -/
def wireProgU (s : RecursionFast.Digest) (n : ℕ) (claim : KClaim E2) : VerifierProgram WireOutU :=
  wireProgB 3960 s n claim

/-- **The S2GU tape.** -/
def tapeProgU (s : RecursionFast.Digest) (n : ℕ) : VerifierProgram TapeOutU := tapeProgB 3960 s n

end Lvm.E2U
