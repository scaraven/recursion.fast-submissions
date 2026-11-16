-- Ported from leanVM `formal/lean_vm/LeanVM/Protocol/Keccak/Linear.lean` (formal rev 40f877dc) as `LvmKeccakLinear` for lvm (WP-2).
/-
  LeanVM.Protocol.Keccak.Linear

  The round's linear map over `E` and its transpose: bits as `0/1` field elements, `L` on
  vectors, and `⟨w, L v⟩ = ⟨keccakLinearTranspose w, v⟩`.
-/
import Mathlib.Algebra.CharP.Two
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Tactic.Ring
import LvmVCore

-- ===== merged from `LvmKeccakBits` (GOLF module merge: `LvmKeccakBits.lean` is now a stub importing `LvmKeccakLinear`) =====
section
-- Ported from leanVM `formal/lean_vm/LeanVM/Protocol/Keccak/Bits.lean` (formal rev 40f877dc) as `LvmKeccakBits` for lvm (WP-2).
/-
  LeanVM.Protocol.Keccak.Bits

  The bit-level semantics of a Keccak-f round: the state's 1600 bits, the linear map
  `L = π ∘ ρ ∘ θ`, χ along the rows, ι, and the theorem that `Keccak.round` on 64-bit lanes is
  `ι ∘ χ ∘ L` on bits.
-/

/-!
# Keccak-f on bits

The GKR reduction of `verifyKeccak` (`crates/verifier/src/keccak.rs` at leanVM `40f877dc`,
`doc/leanvm/body/c-keccak-gkr.tex`,
§`keccak:perm`) speaks of a state as `1600` bits, position `j = z + 64ℓ` being bit `z` (the
*slice*) of lane `ℓ`. A round maps a state `a` to

  `b = L(a)`,  `a'[j] = b[j] + (1 + b[along j 1]) · b[along j 2] + [j < 64] · RC[j]`,

`L = π ∘ ρ ∘ θ`, `along j k` the position `k` columns along in the same row and slice
(`keccakAlong`). This module proves it of the specification's `Keccak.round`, which computes on
`UInt64` lanes (`sbit_round`):

* `sbit a j`, bit `j` of a state;
* `thetaB`, `rhoPiSrc`, `Lb = thetaB ∘ rhoPiSrc` (position `j` of `L(a)` is position
  `rhoPiSrc j` of `θ(a)`), `chiB`, `roundB`;
* the stages of `Keccak.round` as functions (`Stage.theta`, `Stage.rhoPi`, `Stage.chi`,
  `Stage.iota`; `Keccak.round` is their composition by `rfl`) and the bits of each;
* the rounds of a segment (`roundsFrom`) and `keccakF` as two segments of twelve.
-/

namespace LeanVM.Protocol.KeccakGkr

open LeanVM.Parameters LeanVM.Semantics LeanVM.Protocol.Verifier

section

/-! ## Lanes and bits -/

/-- A lane of a state is its entry. -/
theorem lane_eq (v : KeccakState) {i : ℕ} (hi : i < 25) : Keccak.lane v i = v[i] := by
  simp [Keccak.lane, Array.getD, hi]

/-- Bit `j = z + 64ℓ` of a state: bit `z` of lane `ℓ`. -/
def sbit (a : KeccakState) (j : ℕ) : Bool := (Keccak.lane a (j / 64)).toBitVec.getLsbD (j % 64)

theorem sbit_eq (a : KeccakState) (j : ℕ) :
    sbit a j = (Keccak.lane a (j / 64)).toBitVec.getLsbD (j % 64) := rfl

theorem sbit_lane (a : KeccakState) (l : ℕ) {z : ℕ} (hz : z < 64) :
    sbit a (64 * l + z) = (Keccak.lane a l).toBitVec.getLsbD z := by
  unfold sbit
  have h1 : (64 * l + z) / 64 = l := by omega
  have h2 : (64 * l + z) % 64 = z := by (clear * - h1; omega)
  rw [h1, h2]

/-- `rot x n` holds at `z` the bit `z - n` of `x`, cyclically. -/
theorem rot_bit (x : UInt64) (n z : ℕ) (hn : n < 64) (hz : z < 64) :
    (Keccak.rot x n).toBitVec.getLsbD z = x.toBitVec.getLsbD ((z + 64 - n) % 64) := by
  unfold Keccak.rot
  split_ifs with h0
  · subst h0; congr 1; (clear * - hz; omega)
  · simp only [UInt64.toBitVec_or, UInt64.toBitVec_shiftLeft, UInt64.toBitVec_shiftRight,
      BitVec.getLsbD_or]
    rw [BitVec.shiftLeft_eq', BitVec.ushiftRight_eq']
    have h1 : (n.toUInt64.toBitVec % 64).toNat = n := by
      simp [Nat.toUInt64]; omega
    have h2 : ((64 - n).toUInt64.toBitVec % 64).toNat = 64 - n := by
      simp [Nat.toUInt64]; (clear * - hn h0 h1; omega)
    rw [h1, h2, BitVec.getLsbD_shiftLeft, BitVec.getLsbD_ushiftRight]
    by_cases hzn : z < n
    · have : (z + 64 - n) % 64 = 64 - n + z := by (clear * - hn hz h1 hzn; omega)
      simp [hzn, hz, this]
    · have : (z + 64 - n) % 64 = z - n := by (clear * - hn hz h1 hzn; omega)
      have h3 : x.toBitVec.getLsbD (64 - n + z) = false := BitVec.getLsbD_of_ge _ _ (by (clear * - hn h1 hzn this; omega))
      simp [hzn, hz, this, h3]

/-! ## `keccakAlong` -/

theorem keccakAlong_def (j k : ℕ) :
    keccakAlong j k = 64 * ((j / 64 % 5 + k) % 5 + 5 * (j / 64 / 5)) + j % 64 := rfl

theorem keccakAlong_lt {j : ℕ} (k : ℕ) (hj : j < 1600) : keccakAlong j k < 1600 := by
  rw [keccakAlong_def]; omega

theorem keccakAlong_zero {j : ℕ} (hj : j < 1600) : keccakAlong j 0 = j := by
  rw [keccakAlong_def]; omega

/-- Going `k` columns along, then `5 - k`, comes back. -/
theorem keccakAlong_along {j k k' : ℕ} (hk : k + k' = 5) :
    keccakAlong (keccakAlong j k) k' = j := by
  rw [keccakAlong_def, keccakAlong_def]; omega

/-! ## The linear map, χ and ι on bits -/

/-- The θ column sum on bits: the parity of column `x` at slice `z`. -/
def colB (f : ℕ → Bool) (x z : ℕ) : Bool :=
  f (64 * x + z) ^^ f (64 * (x + 5) + z) ^^ f (64 * (x + 10) + z) ^^ f (64 * (x + 15) + z) ^^
    f (64 * (x + 20) + z)

/-- θ on bits: position `p` (lane `ℓ`, slice `z`, column `x = ℓ mod 5`) gains the columns
`x - 1` at `z` and `x + 1` at `z - 1`. -/
def thetaB (f : ℕ → Bool) (p : ℕ) : Bool :=
  f p ^^ colB f ((p / 64 % 5 + 4) % 5) (p % 64) ^^
    colB f ((p / 64 % 5 + 1) % 5) ((p % 64 + 63) % 64)

/-- The inverse of `KECCAK_PI` on lanes: lane `k` of `π(a)` is lane `piInv k` of `a`. -/
def piInv (k : ℕ) : ℕ := (3 * (k / 5) + k % 5) % 5 + 5 * (k % 5)

theorem piInv_lt {k : ℕ} : piInv k < 25 := by unfold piInv; omega

theorem keccakPi_piInv : ∀ k < 25, keccakPi (piInv k) = k := by decide

theorem piInv_keccakPi : ∀ i < 25, piInv (keccakPi i) = i := by decide

theorem keccakPi_lt : ∀ i < 25, keccakPi i < 25 := by decide

theorem keccakRho_lt (i : ℕ) : keccakRho.getD i 0 < 64 := by
  by_cases hi : i < 25
  · revert i; decide
  · have h : keccakRho.length ≤ i := by
      have : keccakRho.length = 25 := rfl
      omega
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none h]
    decide

/-- ρ and π on positions: position `j` of `ρπ(a)` is position `rhoPiSrc j` of `a`. -/
def rhoPiSrc (j : ℕ) : ℕ :=
  64 * piInv (j / 64) + (j % 64 + 64 - keccakRho.getD (piInv (j / 64)) 0) % 64

/-- Where ρ and π send position `p`: the inverse of `rhoPiSrc`. -/
def rhoPiDst (p : ℕ) : ℕ := 64 * keccakPi (p / 64) + (p % 64 + keccakRho.getD (p / 64) 0) % 64

theorem rhoPiSrc_lt {j : ℕ} : rhoPiSrc j < 1600 := by
  have := @piInv_lt (j / 64)
  unfold rhoPiSrc; omega

theorem rhoPiDst_lt {p : ℕ} (hp : p < 1600) : rhoPiDst p < 1600 := by
  have := keccakPi_lt (p / 64) (by omega)
  unfold rhoPiDst; (clear * - this; omega)

theorem rhoPiSrc_dst {p : ℕ} (hp : p < 1600) : rhoPiSrc (rhoPiDst p) = p := by
  have hl : p / 64 < 25 := by omega
  have hr := keccakRho_lt (p / 64)
  have hpi := keccakPi_lt _ hl
  have h1 : rhoPiDst p / 64 = keccakPi (p / 64) := by unfold rhoPiDst; (clear * -; omega)
  have h2 : rhoPiDst p % 64 = (p % 64 + keccakRho.getD (p / 64) 0) % 64 := by
    unfold rhoPiDst; (clear * - h1; omega)
  unfold rhoPiSrc
  rw [h1, h2, piInv_keccakPi _ hl]
  (clear * - hr h2; omega)

theorem rhoPiDst_src {j : ℕ} (hj : j < 1600) : rhoPiDst (rhoPiSrc j) = j := by
  have hl : j / 64 < 25 := by omega
  have hr := keccakRho_lt (piInv (j / 64))
  have h1 : rhoPiSrc j / 64 = piInv (j / 64) := by unfold rhoPiSrc; (clear * -; omega)
  have h2 : rhoPiSrc j % 64 = (j % 64 + 64 - keccakRho.getD (piInv (j / 64)) 0) % 64 := by
    unfold rhoPiSrc; (clear * -; omega)
  unfold rhoPiDst
  rw [h1, h2, keccakPi_piInv _ hl]
  (clear * - hr; omega)

/-- `L = π ∘ ρ ∘ θ` on bits. -/
def Lb (f : ℕ → Bool) (j : ℕ) : Bool := thetaB f (rhoPiSrc j)

/-- χ on bits: `b[j] + (1 + b[along j 1]) · b[along j 2]`. -/
def chiB (b : ℕ → Bool) (j : ℕ) : Bool := b j ^^ (!b (keccakAlong j 1) && b (keccakAlong j 2))

/-- ι on bits: the round constant on lane `0`. -/
def iotaB (rc : UInt64) (j : ℕ) : Bool := decide (j < 64) && rc.toBitVec.getLsbD j

/-- A round on bits: `ι ∘ χ ∘ L`. -/
def roundB (rc : UInt64) (f : ℕ → Bool) (j : ℕ) : Bool := chiB (Lb f) j ^^ iotaB rc j

/-! ## The stages of `Keccak.round` -/

namespace Stage

/-- θ's column parities. -/
def colV (a : KeccakState) : Vector UInt64 5 := Vector.ofFn fun x ↦
  Keccak.lane a x ^^^ Keccak.lane a (x + 5) ^^^ Keccak.lane a (x + 10) ^^^
    Keccak.lane a (x + 15) ^^^ Keccak.lane a (x + 20)

/-- θ. -/
def theta (a : KeccakState) : KeccakState :=
  Vector.ofFn fun i ↦ Keccak.lane a i ^^^ (colV a).toArray.getD ((i.val + 4) % 5) 0 ^^^
    Keccak.rot ((colV a).toArray.getD ((i.val + 1) % 5) 0) 1

/-- ρ and π. -/
def rhoPi (a : KeccakState) : KeccakState :=
  (List.range 25).foldl
    (fun b i ↦ b.setIfInBounds (keccakPi i) (Keccak.rot (Keccak.lane a i) (keccakRho.getD i 0)))
    (Vector.replicate 25 0)

/-- χ. -/
def chi (b : KeccakState) : KeccakState :=
  Vector.ofFn fun i ↦ Keccak.lane b i ^^^ (~~~ Keccak.lane b (i.val - i.val % 5 + (i.val + 1) % 5) &&&
    Keccak.lane b (i.val - i.val % 5 + (i.val + 2) % 5))

/-- ι. -/
def iota (a : KeccakState) (rc : UInt64) : KeccakState := a.setIfInBounds 0 (Keccak.lane a 0 ^^^ rc)

/-- `Keccak.round` is the composition of its stages. -/
theorem round_eq (a : KeccakState) (rc : UInt64) :
    Keccak.round a rc = iota (chi (rhoPi (theta a))) rc := rfl

theorem colV_bit (a : KeccakState) {x z : ℕ} (hx : x < 5) (hz : z < 64) :
    ((colV a).toArray.getD x 0).toBitVec.getLsbD z = colB (sbit a) x z := by
  have h : (colV a).toArray.getD x 0 = (colV a)[x] := by simp [Array.getD, hx]
  rw [h]
  simp only [colV, Vector.getElem_ofFn, UInt64.toBitVec_xor, BitVec.getLsbD_xor, colB,
    sbit_lane a _ hz]

theorem sbit_theta (a : KeccakState) {p : ℕ} (hp : p < 1600) : sbit (theta a) p = thetaB (sbit a) p := by
  have hl : p / 64 < 25 := by omega
  have hz : p % 64 < 64 := Nat.mod_lt _ (by (clear * -; omega))
  rw [sbit_eq (theta a) p, lane_eq _ hl]
  simp only [theta, Vector.getElem_ofFn, UInt64.toBitVec_xor, BitVec.getLsbD_xor]
  rw [rot_bit _ 1 _ (by (clear * -; omega)) hz, colV_bit a (by (clear * -; omega)) hz, colV_bit a (by (clear * -; omega)) (by (clear * -; omega))]
  have e1 : (p / 64 + 4) % 5 = (p / 64 % 5 + 4) % 5 := by (clear * -; omega)
  have e2 : (p / 64 + 1) % 5 = (p / 64 % 5 + 1) % 5 := by (clear * -; omega)
  have e3 : (p % 64 + 64 - 1) % 64 = (p % 64 + 63) % 64 := by (clear * -; omega)
  rw [e1, e2, e3]
  rfl

/-- A fold of writes whose targets miss `k` leaves entry `k`. -/
theorem foldl_set_miss (σ : ℕ → ℕ) (f : ℕ → UInt64) {k : ℕ} (hk : k < 25) :
    ∀ (l : List ℕ) (b : KeccakState), (∀ i ∈ l, σ i ≠ k) →
      (l.foldl (fun b i ↦ b.setIfInBounds (σ i) (f i)) b)[k] = b[k]
  | [], _, _ => rfl
  | i :: l, b, h => by
    rw [List.foldl_cons, foldl_set_miss σ f hk l _ (fun i' hi' ↦ h i' (by simp [hi'])),
      Vector.getElem_setIfInBounds hk, ite_eq_right (h i (by simp))]

/-- A fold of writes hitting `k` once, at `i₀`, leaves `f i₀` there. -/
theorem foldl_set_hit (σ : ℕ → ℕ) (f : ℕ → UInt64) {k i₀ : ℕ} (hk : k < 25) (hσ : σ i₀ = k) :
    ∀ (l : List ℕ) (b : KeccakState), i₀ ∈ l → (∀ i ∈ l, σ i = k → i = i₀) →
      (l.foldl (fun b i ↦ b.setIfInBounds (σ i) (f i)) b)[k] = f i₀
  | [], _, h, _ => by simp at h
  | i :: l, b, hmem, huniq => by
    rw [List.foldl_cons]
    by_cases hl : i₀ ∈ l
    · exact foldl_set_hit σ f hk hσ l _ hl fun i' hi' ↦ huniq i' (by simp [hi'])
    · have hi : i = i₀ := by
        rcases List.mem_cons.1 hmem with h | h
        · exact h.symm
        · exact absurd h hl
      subst hi
      rw [foldl_set_miss σ f hk l _ (fun i' hi' he ↦ hl (huniq i' (by simp [hi']) he ▸ hi')),
        Vector.getElem_setIfInBounds hk, ite_eq_left hσ]

theorem lane_rhoPi (a : KeccakState) {k : ℕ} (hk : k < 25) :
    Keccak.lane (rhoPi a) k =
      Keccak.rot (Keccak.lane a (piInv k)) (keccakRho.getD (piInv k) 0) := by
  rw [lane_eq _ hk, rhoPi]
  exact foldl_set_hit keccakPi (fun i ↦ Keccak.rot (Keccak.lane a i) (keccakRho.getD i 0)) hk
    (keccakPi_piInv k hk) _ _ (List.mem_range.2 piInv_lt) fun i hi he ↦ by
      rw [← he, piInv_keccakPi i (List.mem_range.1 hi)]

theorem sbit_rhoPi (a : KeccakState) {j : ℕ} (hj : j < 1600) : sbit (rhoPi a) j = sbit a (rhoPiSrc j) := by
  have hl : j / 64 < 25 := by omega
  have hz : j % 64 < 64 := Nat.mod_lt _ (by (clear * -; omega))
  have hr := keccakRho_lt (piInv (j / 64))
  unfold sbit
  rw [lane_rhoPi a hl, rot_bit _ _ _ hr hz]
  have h1 : rhoPiSrc j / 64 = piInv (j / 64) := by unfold rhoPiSrc; (clear * -; omega)
  have h2 : rhoPiSrc j % 64 = (j % 64 + 64 - keccakRho.getD (piInv (j / 64)) 0) % 64 := by
    unfold rhoPiSrc; (clear * -; omega)
  rw [h1, h2]

theorem sbit_chi (b : KeccakState) {j : ℕ} (hj : j < 1600) : sbit (chi b) j = chiB (sbit b) j := by
  have hl : j / 64 < 25 := by omega
  have hz : j % 64 < 64 := Nat.mod_lt _ (by (clear * -; omega))
  rw [sbit_eq (chi b) j, lane_eq _ hl]
  simp only [chi, Vector.getElem_ofFn, UInt64.toBitVec_xor, UInt64.toBitVec_and,
    UInt64.toBitVec_not, BitVec.getLsbD_xor, BitVec.getLsbD_and, BitVec.getLsbD_not, hz,
    decide_true, Bool.true_and]
  unfold chiB
  have e : ∀ k, keccakAlong j k = 64 * ((j / 64 % 5 + k) % 5 + 5 * (j / 64 / 5)) + j % 64 :=
    fun k ↦ keccakAlong_def j k
  rw [e 1, e 2, sbit_lane b _ hz, sbit_lane b _ hz]
  have e1 : j / 64 - j / 64 % 5 + (j / 64 + 1) % 5 = (j / 64 % 5 + 1) % 5 + 5 * (j / 64 / 5) := by
    (clear * -; omega)
  have e2 : j / 64 - j / 64 % 5 + (j / 64 + 2) % 5 = (j / 64 % 5 + 2) % 5 + 5 * (j / 64 / 5) := by
    (clear * - e1; omega)
  rw [e1, e2]
  rfl

theorem sbit_iota (a : KeccakState) (rc : UInt64) {j : ℕ} (hj : j < 1600) :
    sbit (iota a rc) j = (sbit a j ^^ iotaB rc j) := by
  have hl : j / 64 < 25 := by omega
  unfold sbit iota iotaB
  rw [lane_eq _ hl, Vector.getElem_setIfInBounds hl, ← lane_eq _ hl]
  by_cases h0 : j < 64
  · have hj0 : j / 64 = 0 := by omega
    have hjz : j % 64 = j := by (clear * - hj0; omega)
    simp only [hj0, ite_true, UInt64.toBitVec_xor, BitVec.getLsbD_xor, hjz, h0, decide_true,
      Bool.true_and]
  · have hj0 : ¬ 0 = j / 64 := by (clear * - hj h0; omega)
    simp [hj0, h0]

end Stage

/-- **A round on bits.** Bit `j` of `Keccak.round a rc` is `ι ∘ χ ∘ L` of the bits of `a`
(`doc/leanvm`, eq. `keccak:eq:round`). -/
theorem sbit_round (a : KeccakState) (rc : UInt64) {j : ℕ} (hj : j < 1600) :
    sbit (Keccak.round a rc) j = roundB rc (sbit a) j := by
  rw [Stage.round_eq, Stage.sbit_iota _ _ hj, Stage.sbit_chi _ hj]
  unfold roundB chiB Lb
  rw [Stage.sbit_rhoPi _ hj, Stage.sbit_rhoPi _ (keccakAlong_lt 1 hj),
    Stage.sbit_rhoPi _ (keccakAlong_lt 2 hj), Stage.sbit_theta _ rhoPiSrc_lt,
    Stage.sbit_theta _ rhoPiSrc_lt, Stage.sbit_theta _ rhoPiSrc_lt]

/-! ## Segments of rounds -/

/-- `e` rounds from round `start`: rounds `start, …, start + e - 1` of `keccakF`. -/
def roundsFrom (start e : ℕ) (a : KeccakState) : KeccakState :=
  ((keccakRC.drop start).take e).foldl Keccak.round a

theorem roundsFrom_zero (start : ℕ) (a : KeccakState) : roundsFrom start 0 a = a := rfl

/-- One more round. -/
theorem roundsFrom_succ {start e : ℕ} (h : start + e < 24) (a : KeccakState) :
    roundsFrom start (e + 1) a =
      Keccak.round (roundsFrom start e a) (keccakRC.getD (start + e) 0) := by
  have hlen : keccakRC.length = 24 := rfl
  unfold roundsFrom
  rw [List.take_add_one, List.foldl_append, List.getElem?_drop,
    List.getElem?_eq_getElem (by omega)]
  simp only [Option.toList_some, List.foldl_cons, List.foldl_nil]
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by omega), Option.getD_some]

/-- `keccakF` is twelve rounds, then the twelve others. -/
theorem keccakF_eq (a : KeccakState) : keccakF1600 a = roundsFrom 12 12 (roundsFrom 0 12 a) := by
  unfold keccakF1600 roundsFrom
  rw [← List.foldl_append]
  rfl

end
end LeanVM.Protocol.KeccakGkr
end
-- ===== end of `LvmKeccakBits` =====

/-!
# The linear map over `E` and its transpose

A layer of the reduction (`verify_layer`, `crates/verifier/src/keccak.rs:115-196`) moves a claim's
position weights across the round's linear map with `linear_transpose`
(`keccak.rs:83-101`, `keccakLinearTranspose`), whose defining property is
`⟨w, L(a)⟩ = ⟨Lᵀ(w), a⟩` (`doc/leanvm`, §`keccak:layer`, step 6). This module proves it:

* `bitE`: a bit as `0` or `1` of `E`; in characteristic two XOR is `+`, AND is `·` and NOT is
  `1 + ·` (`bitE_xor`, `bitE_and`, `bitE_not`);
* `Llin`: `L` on vectors `ℕ → E` (θ is the identity plus two column sums, ρπ a permutation of
  the positions), and `bitE (Lb f j) = Llin (bitE ∘ f) j` (`bitE_Lb`);
* `keccakLinearTranspose_getD`: the verifier's array program in closed form;
* `transpose`: `Σ_j w_j (L v)_j = Σ_j (Lᵀ w)_j v_j` over the `1600` positions, for every `v`.
-/

namespace LeanVM.Protocol.KeccakGkr

open LeanVM.Parameters LeanVM.Semantics LeanVM.Protocol.Verifier Finset

section

/-! ## Bits in `E` -/

/-- A bit as a field element. -/
def bitE (b : Bool) : E := if b then 1 else 0

@[simp] theorem bitE_true : bitE true = 1 := rfl
@[simp] theorem bitE_false : bitE false = 0 := rfl

theorem bitE_xor (a b : Bool) : bitE (a ^^ b) = bitE a + bitE b := by
  cases a <;> cases b <;> simp [bitE, CharTwo.add_self_eq_zero]

theorem bitE_and (a b : Bool) : bitE (a && b) = bitE a * bitE b := by
  cases a <;> cases b <;> simp [bitE]

theorem bitE_not (a : Bool) : bitE (!a) = 1 + bitE a := by
  cases a <;> simp [bitE, CharTwo.add_self_eq_zero]

/-! ## The linear map on vectors -/

/-- A θ column sum: `Σ_y v(x + 5y, z)`. -/
def colL (v : ℕ → E) (x z : ℕ) : E := ∑ y ∈ range 5, v (64 * (x + 5 * y) + z)

/-- θ on vectors. -/
def thetaL (v : ℕ → E) (p : ℕ) : E :=
  v p + colL v ((p / 64 % 5 + 4) % 5) (p % 64) + colL v ((p / 64 % 5 + 1) % 5) ((p % 64 + 63) % 64)

/-- `L = π ∘ ρ ∘ θ` on vectors. -/
def Llin (v : ℕ → E) (j : ℕ) : E := thetaL v (rhoPiSrc j)

/-- The transpose of θ: `g` plus the columns `x + 1` at `z` and `x - 1` at `z + 1`. -/
def thetaT (g : ℕ → E) (p : ℕ) : E :=
  g p + colL g ((p / 64 % 5 + 1) % 5) (p % 64) + colL g ((p / 64 % 5 + 4) % 5) ((p % 64 + 1) % 64)

theorem bitE_colB (f : ℕ → Bool) (x z : ℕ) : bitE (colB f x z) = colL (fun p ↦ bitE (f p)) x z := by
  simp only [colB, bitE_xor, colL, Finset.sum_range_succ, Finset.sum_range_zero]
  ring_nf

/-- On bits, `L` is `Llin`. -/
theorem bitE_Lb (f : ℕ → Bool) (j : ℕ) : bitE (Lb f j) = Llin (fun p ↦ bitE (f p)) j := by
  simp only [Lb, thetaB, bitE_xor, bitE_colB, Llin, thetaL]

/-! ## Reindexing sums -/

theorem sum_range_mul (a b : ℕ) (F : ℕ → E) :
    ∑ p ∈ range (a * b), F p = ∑ i ∈ range a, ∑ k ∈ range b, F (b * i + k) := by
  induction a with
  | zero => simp
  | succ a ih =>
    rw [Nat.succ_mul, Finset.sum_range_add, ih, Finset.sum_range_succ]
    congr 1
    refine Finset.sum_congr rfl fun k _ ↦ ?_
    rw [Nat.mul_comm a b]

/-- The positions by column, slice and row. -/
theorem sum_regroup (F : ℕ → E) :
    ∑ p ∈ range 1600, F p = ∑ x ∈ range 5, ∑ z ∈ range 64, ∑ y ∈ range 5, F (64 * (x + 5 * y) + z) := by
  rw [show 1600 = 25 * 64 from rfl, sum_range_mul, show 25 = 5 * 5 from rfl, sum_range_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun x _ ↦ ?_
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun z _ ↦ ?_
  refine Finset.sum_congr rfl fun y _ ↦ ?_
  congr 1
  ring

/-- A sum weighted by a function of the column and the slice collects the columns. -/
theorem sum_col (g : ℕ → E) (H : ℕ → ℕ → E) :
    ∑ p ∈ range 1600, g p * H (p / 64 % 5) (p % 64) =
      ∑ x ∈ range 5, ∑ z ∈ range 64, H x z * colL g x z := by
  rw [sum_regroup]
  refine Finset.sum_congr rfl fun x hx ↦ Finset.sum_congr rfl fun z hz ↦ ?_
  rw [colL, Finset.mul_sum]
  refine Finset.sum_congr rfl fun y hy ↦ ?_
  simp only [Finset.mem_range] at hx hz hy
  have h1 : (64 * (x + 5 * y) + z) / 64 % 5 = x := by (clear * - hx hz; omega)
  have h2 : (64 * (x + 5 * y) + z) % 64 = z := by (clear * - hz h1; omega)
  rw [h1, h2, mul_comm]

/-- A permutation of `range n` does not change a sum over it. -/
theorem sum_perm (n : ℕ) (σ τ : ℕ → ℕ) (hσ : ∀ x < n, σ x < n) (hτ : ∀ x < n, τ x < n)
    (hστ : ∀ x < n, σ (τ x) = x) (hτσ : ∀ x < n, τ (σ x) = x) (F : ℕ → E) :
    ∑ x ∈ range n, F (σ x) = ∑ x ∈ range n, F x :=
  Finset.sum_nbij' σ τ (fun x hx ↦ by simpa using hσ x (by simpa using hx))
    (fun x hx ↦ by simpa using hτ x (by simpa using hx))
    (fun x hx ↦ hτσ x (by simpa using hx)) (fun x hx ↦ hστ x (by simpa using hx))
    fun _ _ ↦ rfl

/-! ## The transpose of θ -/

theorem theta_transpose (g v : ℕ → E) :
    ∑ p ∈ range 1600, g p * thetaL v p = ∑ p ∈ range 1600, thetaT g p * v p := by
  simp only [thetaL, thetaT, mul_add, add_mul, Finset.sum_add_distrib]
  have t1 : ∑ p ∈ range 1600, g p * v p = ∑ p ∈ range 1600, v p * g p :=
    Finset.sum_congr rfl fun _ _ ↦ mul_comm _ _
  have t2 : ∑ p ∈ range 1600, g p * colL v ((p / 64 % 5 + 4) % 5) (p % 64) =
      ∑ p ∈ range 1600, colL g ((p / 64 % 5 + 1) % 5) (p % 64) * v p := by
    rw [sum_col g (fun x z ↦ colL v ((x + 4) % 5) z)]
    rw [show (∑ p ∈ range 1600, colL g ((p / 64 % 5 + 1) % 5) (p % 64) * v p) =
      ∑ p ∈ range 1600, v p * colL g ((p / 64 % 5 + 1) % 5) (p % 64) from
        Finset.sum_congr rfl fun _ _ ↦ mul_comm _ _]
    rw [sum_col v (fun x z ↦ colL g ((x + 1) % 5) z)]
    rw [← sum_perm 5 (fun x ↦ (x + 1) % 5) (fun x ↦ (x + 4) % 5) (by (clear * -; omega)) (by (clear * -; omega))
      (by (clear * -; omega)) (by (clear * -; omega))]
    refine Finset.sum_congr rfl fun x hx ↦ Finset.sum_congr rfl fun z _ ↦ ?_
    simp only [Finset.mem_range] at hx
    have : ((x + 1) % 5 + 4) % 5 = x := by (clear * - hx; omega)
    rw [this, mul_comm]
  have t3 : ∑ p ∈ range 1600, g p * colL v ((p / 64 % 5 + 1) % 5) ((p % 64 + 63) % 64) =
      ∑ p ∈ range 1600, colL g ((p / 64 % 5 + 4) % 5) ((p % 64 + 1) % 64) * v p := by
    rw [sum_col g (fun x z ↦ colL v ((x + 1) % 5) ((z + 63) % 64))]
    rw [show (∑ p ∈ range 1600, colL g ((p / 64 % 5 + 4) % 5) ((p % 64 + 1) % 64) * v p) =
      ∑ p ∈ range 1600, v p * colL g ((p / 64 % 5 + 4) % 5) ((p % 64 + 1) % 64) from
        Finset.sum_congr rfl fun _ _ ↦ mul_comm _ _]
    rw [sum_col v (fun x z ↦ colL g ((x + 4) % 5) ((z + 1) % 64))]
    rw [← sum_perm 5 (fun x ↦ (x + 4) % 5) (fun x ↦ (x + 1) % 5) (by (clear * -; omega)) (by (clear * -; omega))
      (by (clear * -; omega)) (by (clear * -; omega))]
    refine Finset.sum_congr rfl fun x hx ↦ ?_
    rw [← sum_perm 64 (fun z ↦ (z + 1) % 64) (fun z ↦ (z + 63) % 64) (by (clear * -; omega)) (by (clear * -; omega))
      (by (clear * -; omega)) (by (clear * -; omega))]
    refine Finset.sum_congr rfl fun z hz ↦ ?_
    simp only [Finset.mem_range] at hx hz
    have e1 : ((x + 4) % 5 + 1) % 5 = x := by (clear * - hx; omega)
    have e2 : ((z + 1) % 64 + 63) % 64 = z := by (clear * - hz; omega)
    rw [e1, e2, mul_comm]
  rw [t2, t3]

/-! ## The verifier's transpose in closed form -/

theorem sumE_eq_sum (l : List E) : sumE l = l.sum := by
  unfold sumE
  suffices h : ∀ a : E, l.foldl (· + ·) a = a + l.sum by simpa using h 0
  induction l with
  | nil => simp
  | cons x l ih => intro a; rw [List.foldl_cons, ih, List.sum_cons, add_assoc]

theorem list_sum_range (f : ℕ → E) (n : ℕ) :
    ((List.range n).map f).sum = ∑ y ∈ range n, f y := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [List.range_succ, List.map_append, List.sum_append, ih, Finset.sum_range_succ]
    simp

theorem array_getD_toArray (l : List E) (i : ℕ) : l.toArray.getD i 0 = l.getD i 0 := by
  simp [Array.getD_eq_getD_getElem?, List.getD_eq_getElem?_getD]

theorem setIfInBounds_getD (a : Array E) (i p : ℕ) (x : E) :
    (a.setIfInBounds i x).getD p 0 = if i = p ∧ i < a.size then x else a.getD p 0 := by
  simp only [Array.getD_eq_getD_getElem?, Array.getElem?_setIfInBounds]
  split_ifs <;> simp_all
  omega

/-- A row of a grid flattened by rows. -/
theorem flatMap_getD (F : ℕ → ℕ → E) (m : ℕ) :
    ∀ (n x z : ℕ), x < n → z < m →
      ((List.range n).flatMap fun x ↦ (List.range m).map (F x)).getD (m * x + z) 0 = F x z
  | 0, _, _, hx, _ => absurd hx (Nat.not_lt_zero _)
  | n + 1, x, z, hx, hz => by
    have hlen : ((List.range n).flatMap fun x ↦ (List.range m).map (F x)).length = n * m := by
      simp [List.length_flatMap, List.sum_replicate]
    rw [List.range_succ, List.flatMap_append]
    by_cases hxn : x < n
    · rw [List.getD_append _ _ _ _ (by rw [hlen]; nlinarith)]
      exact flatMap_getD F m n x z hxn hz
    · have : x = n := by (clear * - hx hxn; omega)
      subst this
      rw [List.getD_append_right _ _ _ _ (by rw [hlen]; nlinarith), hlen]
      simp [Nat.mul_comm, hz, List.getD_eq_getElem?_getD]

theorem flatMap_length (F : ℕ → ℕ → E) (m n : ℕ) :
    ((List.range n).flatMap fun x ↦ (List.range m).map (F x)).length = n * m := by
  simp [List.length_flatMap, List.sum_replicate]

/-- θ's input weights after ρπ: position `p` of θ's output carries `w` at `rhoPiDst p`. -/
def gOf (w : List E) (p : ℕ) : E := w.getD (rhoPiDst p) 0

/-- The inner loop of `keccak_linear_transpose`'s first array, writing one lane. -/
theorem inner_loop (W : ℕ → E) (lane : ℕ) (g : Array E) :
    ∀ Z, ((List.range Z).foldl (fun g z ↦ g.setIfInBounds (64 * lane + z) (W z)) g).size =
        g.size ∧
      ∀ p, ((List.range Z).foldl (fun g z ↦ g.setIfInBounds (64 * lane + z) (W z)) g).getD p 0 =
        if 64 * lane ≤ p ∧ p < 64 * lane + Z ∧ p < g.size then W (p - 64 * lane)
        else g.getD p 0
  | 0 => ⟨rfl, fun p ↦ by simp; omega⟩
  | Z + 1 => by
    obtain ⟨hs, hg⟩ := inner_loop W lane g Z
    rw [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil]
    refine ⟨by simp [hs], fun p ↦ ?_⟩
    rw [setIfInBounds_getD, hg p, hs]
    split_ifs <;> first | rfl | (exfalso; omega) | (congr 1; (clear hg hs; omega))

/-- `keccak_linear_transpose`'s first array, lane by lane. -/
theorem outer_loop (w : List E) :
    ∀ L, L ≤ 25 →
      ((List.range L).foldl (fun g lane ↦ (List.range 64).foldl (fun g z ↦
        g.setIfInBounds (64 * lane + z)
          (w.toArray.getD (64 * keccakPi lane + (z + keccakRho.getD lane 0) % 64) 0)) g)
        (Array.replicate keccakBits 0)).size = 1600 ∧
      ∀ p, ((List.range L).foldl (fun g lane ↦ (List.range 64).foldl (fun g z ↦
        g.setIfInBounds (64 * lane + z)
          (w.toArray.getD (64 * keccakPi lane + (z + keccakRho.getD lane 0) % 64) 0)) g)
        (Array.replicate keccakBits 0)).getD p 0 = if p < 64 * L then gOf w p else 0
  | 0, _ => ⟨by simp [keccakBits], fun p ↦ by
      simp [Array.getD_eq_getD_getElem?, keccakBits, Array.getElem?_replicate]
      split_ifs <;> rfl⟩
  | L + 1, hL => by
    obtain ⟨hs, hg⟩ := outer_loop w L (by omega)
    rw [List.range_succ (n := L), List.foldl_append, List.foldl_cons, List.foldl_nil]
    obtain ⟨hs', hg'⟩ := inner_loop
      (fun z ↦ w.toArray.getD (64 * keccakPi L + (z + keccakRho.getD L 0) % 64) 0) L
      ((List.range L).foldl (fun g lane ↦ (List.range 64).foldl (fun g z ↦
        g.setIfInBounds (64 * lane + z)
          (w.toArray.getD (64 * keccakPi lane + (z + keccakRho.getD lane 0) % 64) 0)) g)
        (Array.replicate keccakBits 0)) 64
    refine ⟨hs'.trans hs, fun p ↦ ?_⟩
    rw [hg' p, hg p, hs]
    by_cases h1 : 64 * L ≤ p ∧ p < 64 * L + 64 ∧ p < 1600
    · rw [ite_eq_left h1, ite_eq_left (by (clear * - h1; omega)), array_getD_toArray, gOf, rhoPiDst]
      have e1 : p / 64 = L := by (clear * - h1; omega)
      have e2 : p % 64 = p - 64 * L := by (clear * - h1 e1; omega)
      rw [e1, e2]
    · rw [ite_eq_right h1]
      by_cases h2 : p < 64 * L
      · rw [ite_eq_left h2, ite_eq_left (by (clear * - h2; omega))]
      · rw [ite_eq_right h2, ite_eq_right (by (clear * - hL h1 h2; omega))]

/-- `keccak_linear_transpose`'s column sums. -/
theorem columns_getD (A : Array E) {x z : ℕ} (hx : x < 5) (hz : z < 64) :
    ((List.range 5).flatMap fun x ↦ (List.range 64).map fun z ↦
        sumE ((List.range 5).map fun y ↦ A.getD (64 * (x + 5 * y) + z) 0)).toArray.getD
      (64 * x + z) 0 = colL (fun p ↦ A.getD p 0) x z := by
  rw [array_getD_toArray, flatMap_getD (fun x z ↦
    sumE ((List.range 5).map fun y ↦ A.getD (64 * (x + 5 * y) + z) 0)) 64 5 x z hx hz]
  rw [sumE_eq_sum, list_sum_range]
  rfl

/-- The list `keccak_linear_transpose` returns, from its first array `A`, in closed form. -/
theorem transposeList_getD (A : Array E) (g : ℕ → E) (hA : ∀ p < 1600, A.getD p 0 = g p)
    {p : ℕ} (hp : p < 1600) :
    ((List.range 25).flatMap fun lane ↦ (List.range 64).map fun z ↦
      A.getD (64 * lane + z) 0 +
        ((List.range 5).flatMap fun x ↦ (List.range 64).map fun z ↦
          sumE ((List.range 5).map fun y ↦ A.getD (64 * (x + 5 * y) + z) 0)).toArray.getD
          (64 * ((lane % 5 + 1) % 5) + z) 0 +
        ((List.range 5).flatMap fun x ↦ (List.range 64).map fun z ↦
          sumE ((List.range 5).map fun y ↦ A.getD (64 * (x + 5 * y) + z) 0)).toArray.getD
          (64 * ((lane % 5 + 4) % 5) + (z + 1) % 64) 0).getD p 0 = thetaT g p := by
  have hp' : p = 64 * (p / 64) + p % 64 := by (clear * -; omega)
  conv_lhs => rw [hp']
  rw [flatMap_getD _ 64 25 (p / 64) (p % 64) (by (clear * - hp; omega)) (Nat.mod_lt _ (by (clear * -; omega)))]
  rw [columns_getD _ (by (clear * -; omega)) (Nat.mod_lt _ (by (clear * -; omega))),
    columns_getD _ (by (clear * -; omega)) (Nat.mod_lt _ (by (clear * -; omega))), ← hp', hA p hp]
  have hcol : ∀ x z, x < 5 → z < 64 → colL (fun p ↦ A.getD p 0) x z = colL g x z := by
    intro x z hx hz
    refine Finset.sum_congr rfl fun y hy ↦ ?_
    simp only [Finset.mem_range] at hy
    exact hA _ (by (clear * - hx hz hy; omega))
  rw [hcol _ _ (by (clear * -; omega)) (Nat.mod_lt _ (by (clear * -; omega))), hcol _ _ (by (clear * -; omega)) (Nat.mod_lt _ (by (clear * -; omega)))]
  rfl

/-- **`keccak_linear_transpose` in closed form**: θ's transpose of the weights moved back
through ρπ. -/
theorem keccakLinearTranspose_getD (w : List E) {p : ℕ} (hp : p < 1600) :
    (keccakLinearTranspose w).getD p 0 = thetaT (gOf w) p := by
  obtain ⟨-, hg⟩ := outer_loop w 25 le_rfl
  exact transposeList_getD _ (gOf w) (fun q hq ↦ by rw [hg, ite_eq_left (by omega)]) hp

theorem keccakLinearTranspose_length (w : List E) : (keccakLinearTranspose w).length = 1600 := by
  unfold keccakLinearTranspose
  simp only []
  rw [flatMap_length]

/-- **The transpose.** For every vector `v` on the positions,
`Σ_j w_j (L v)_j = Σ_j (keccakLinearTranspose w)_j v_j` (`keccak.rs:83-101`). -/
theorem transpose (w : List E) (v : ℕ → E) :
    ∑ j ∈ range 1600, w.getD j 0 * Llin v j =
      ∑ j ∈ range 1600, (keccakLinearTranspose w).getD j 0 * v j := by
  have h1 : ∑ j ∈ range 1600, w.getD j 0 * Llin v j =
      ∑ p ∈ range 1600, gOf w p * thetaL v p :=
    Finset.sum_nbij' rhoPiSrc rhoPiDst (fun _ _ ↦ Finset.mem_range.2 rhoPiSrc_lt)
      (fun p hp ↦ Finset.mem_range.2 (rhoPiDst_lt (Finset.mem_range.1 hp)))
      (fun j hj ↦ rhoPiDst_src (Finset.mem_range.1 hj))
      (fun p hp ↦ rhoPiSrc_dst (Finset.mem_range.1 hp))
      fun j hj ↦ by rw [Llin, gOf, rhoPiDst_src (Finset.mem_range.1 hj)]
  rw [h1, theta_transpose]
  refine Finset.sum_congr rfl fun p hp ↦ ?_
  rw [keccakLinearTranspose_getD w (Finset.mem_range.1 hp)]

/-- The transpose on bits: `Σ_j w_j (L a)_j = Σ_j (Lᵀ w)_j a_j`, bits as `0/1` of `E`. -/
theorem transpose_bits (w : List E) (f : ℕ → Bool) :
    ∑ j ∈ range 1600, w.getD j 0 * bitE (Lb f j) =
      ∑ j ∈ range 1600, (keccakLinearTranspose w).getD j 0 * bitE (f j) := by
  simp only [bitE_Lb]
  exact transpose w _

end
end LeanVM.Protocol.KeccakGkr
