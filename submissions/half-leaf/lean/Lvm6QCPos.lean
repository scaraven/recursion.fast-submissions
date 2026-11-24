-- New for lvm6 (WP CC). The deployed position gadget (CC-3a): the draw lanes decomposed into
-- asserted bits, the positions `K(p)` as sums of powers of `x` over those bits (W1's `posE2`).
import Lvm6QCStmt
import LvmE2QWKitSem
import Lvm6RingMap
import Lvm6FSGroup

/-!
# Positions from the draws' bits (generator and proof of `PosE2Stmt`)

`posGen B h c kq t ds gate`: `128·(kq + 1)` bit cells at `B, B + 1, …` (draw `j`'s lane 0 at
`B + 128j`, lane 1 at `B + 128j + 64`), each asserted `b·b + b = 0` (so `b ∈ {0, 1}`); each lane
asserted equal to `Σ_{z<64} x^z·b_z` (`laneG`); position `k` is the cell `Σ_{z<h} x^z·b_{off+z}`,
`off = 128·(k / c) + h·(k mod c)` (`posCell`). Rows: `2` per bit, `64 + 1` per lane, `h + 1` per
position. The bits of a word are unique (`rep_injective`: `x^0 … x^63` is a basis, from
`K.eq_sum_bits` and `|K| = 2^64`), so the cells are the digits of `e2Nat` and hold `K(p)`.
**`posE2Har B : PosE2Stmt (posGen B)`** for every base `B` (NODE places the bit cells).
-/

set_option autoImplicit false

namespace Lvm6.QC

open LeanVM.Parameters LeanVM.Protocol.Compile LeanVM.Protocol.Verifier
open Lvm Lvm.Loop Lvm.Loop.Build Lvm.Q2 Lvm.Har Lvm.E2V Lvm6.QK
open Finset

/-! ## Words and their bits -/

/-- The word with bits `b`: `Σ_{i<64} b_i·x^i`. -/
def rep (b : Fin 64 → Bool) : K := ∑ i : Fin 64, if b i then g ^ (i : ℕ) else 0

/-- The bits of a word. -/
def bitsK (a : K) : Fin 64 → Bool := fun i ↦ a.toBitVec.getLsbD i

theorem rep_bitsK (a : K) : rep (bitsK a) = a := (Ring.K.eq_sum_bits a).symm

theorem bitsK_injective : Function.Injective bitsK := fun a b h ↦
  BF64.toBitVec_injective (BitVec.eq_of_getLsbD_eq fun i hi ↦ congrFun h ⟨i, hi⟩)

theorem bitsK_bijective : Function.Bijective bitsK := by
  rw [Fintype.bijective_iff_injective_and_card]
  refine ⟨bitsK_injective, ?_⟩
  rw [card_K6]
  simp

theorem bitsK_rep (b : Fin 64 → Bool) : bitsK (rep b) = b := by
  obtain ⟨a, rfl⟩ := bitsK_bijective.2 b
  rw [rep_bitsK]

theorem bitsK_ofBits (d z : ℕ) (hz : z < 64) : bitsK (K.ofBits d) ⟨z, hz⟩ = d.testBit z := by
  show (BF64.ofBitVec (BitVec.ofNat 64 d)).toBitVec.getLsbD z = _
  rw [BF64.toBitVec_ofBitVec, BitVec.getLsbD_ofNat]
  simp [hz]

theorem kToNat_ofBits {d : ℕ} (hd : d < 2 ^ 64) : kToNat (K.ofBits d) = d := by
  show (BF64.ofBitVec (BitVec.ofNat 64 d)).toBitVec.toNat = d
  rw [BF64.toBitVec_ofBitVec, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hd]

/-- **A sum of powers of `x` over `0/1` values** is the word with those bits. -/
theorem sum_bits_eq_rep {m : ℕ} (hm : m ≤ 64) (T : ℕ → K) (hT : ∀ z < m, T z = 0 ∨ T z = 1) :
    ∑ z ∈ range m, g ^ z * T z = rep fun i ↦ decide ((i : ℕ) < m) && decide (T i = 1) := by
  unfold rep
  rw [← Finset.sum_range (fun i ↦ if (decide (i < m) && decide (T i = 1)) = true then g ^ i else 0),
    ← Finset.sum_range_add_sum_Ico _ hm,
    Finset.sum_eq_zero (s := Ico m 64) fun i hi ↦ by
      simp only [Finset.mem_Ico] at hi
      simp [show ¬ i < m by omega], add_zero]
  refine Finset.sum_congr rfl fun z hz ↦ ?_
  have hz' : z < m := Finset.mem_range.mp hz
  rcases hT z hz' with h | h <;> simp [h, hz']

/-! ## Facts on `FK` -/

theorem fk_eq_of_add {a b : FK} (h : a + b = 0) : a = b :=
  calc a = a + (b + b) := by rw [fk_add_self, add_zero]
    _ = (a + b) + b := by ring
    _ = b := by rw [h, zero_add]

theorem k_one_add_one : (1 : K) + 1 = 0 := by
  rw [← FK.toBF64_one, ← FK.toBF64_add, fk_add_self, FK.toBF64_zero]

theorem fk_bool {b : FK} (h : b * b + b = 0) : FK.toBF64 b = 0 ∨ FK.toBF64 b = 1 := by
  have h' : FK.toBF64 b * (FK.toBF64 b + 1) = 0 := by
    rw [mul_add, mul_one, ← FK.toBF64_mul, ← FK.toBF64_add, h, FK.toBF64_zero]
  rcases mul_eq_zero.mp h' with h0 | h1
  · exact Or.inl h0
  · right
    calc FK.toBF64 b = FK.toBF64 b + (1 + 1) := by rw [k_one_add_one, add_zero]
      _ = (FK.toBF64 b + 1) + 1 := by ring
      _ = 1 := by rw [h1, zero_add]

theorem toBF64_sum (s : Finset ℕ) (f : ℕ → FK) :
    FK.toBF64 (∑ i ∈ s, f i) = ∑ i ∈ s, FK.toBF64 (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, FK.toBF64_add, ih]

theorem toBF64_gpow : ∀ z : ℕ, FK.toBF64 (Build.gpow z) = g ^ z
  | 0 => by rw [Build.gpow, pow_zero, FK.toBF64_one, pow_zero]
  | z + 1 => by
    rw [Build.gpow, pow_succ, FK.toBF64_mul, ← Build.gpow, toBF64_gpow z, pow_succ]
    rfl

theorem ofK_zero : FE.ofK 0 = 0 := rfl

/-! ## Gadgets -/

variable {c : Ctx} {M : Mem}

theorem hsA_assert0 {a gate : Cell} (hg : gate.val M = 1) :
    HsA c M (assert0 a gate) fun _ ↦ a.val M = 0 := by
  intro p _ ha
  have := assert0_spec ha
  rwa [hg, one_mul] at this

/-- `b·b + b`, asserted `0`. -/
def boolG (x gate : Cell) : BM Unit := mulAdd .K x x x >>= fun m ↦ assert0 m gate

theorem hsA_boolG {n : ℕ} {gate : Cell} (hg : gate.val M = 1) :
    HsA c M (boolG (kc n) gate) fun _ ↦ M.k n * M.k n + M.k n = 0 :=
  hsA_bind (hsA_of_hs (hs_mulAdd .K (kc n) (kc n) (kc n))) fun m hm ↦
    hsA_mono (hsA_assert0 hg) fun _ h ↦ by
      rw [hm] at h
      simp only [Cell.val_K, ← Build.ofK_mul, ← Build.ofK_add] at h
      exact Build.ofK_inj (h.trans ofK_zero.symm)

/-- The bit cells `B … B + n − 1`, each asserted `0/1`. -/
def boolsG (B : ℕ) (gate : Cell) : ℕ → BM Unit
  | 0 => pure ()
  | n + 1 => boolsG B gate n >>= fun _ ↦ boolG (kc (B + n)) gate

theorem hsA_boolsG {B : ℕ} {gate : Cell} (hg : gate.val M = 1) : ∀ n,
    HsA c M (boolsG B gate n) fun _ ↦ ∀ i < n, M.k (B + i) * M.k (B + i) + M.k (B + i) = 0
  | 0 => hsA_pure fun i hi ↦ absurd hi (Nat.not_lt_zero i)
  | n + 1 => hsA_bind (hsA_boolsG hg n) fun _ h₁ ↦ hsA_mono (hsA_boolG hg) fun _ h₂ i hi ↦ by
      rcases Nat.lt_succ_iff_lt_or_eq.mp hi with h | rfl
      · exact h₁ i h
      · exact h₂

/-- `acc + Σ_{z<m} x^z·b_{base+z}`. -/
def sumG (B base : ℕ) (acc : Cell) : ℕ → BM Cell
  | 0 => pure acc
  | m + 1 => sumG B base acc m >>= fun a ↦ lin .K (Build.gpow m) 0 a (kc (B + base + m))

theorem hs_sumG (B base : ℕ) (acc : Cell) : ∀ m,
    Hs c M (sumG B base acc m) fun r ↦
      r.val M = acc.val M + FE.ofK (∑ z ∈ range m, Build.gpow z * M.k (B + base + z))
  | 0 => hs_pure (by rw [Finset.sum_range_zero, ofK_zero, add_zero])
  | m + 1 => hs_bind (hs_sumG B base acc m) fun a ha ↦
      hs_mono (hs_lin .K (Build.gpow m) 0 a (kc (B + base + m))) fun r hr ↦ by
        rw [hr, ha, Cell.val_K, ← Build.ofK_mul, ofK_zero, add_zero, Finset.sum_range_succ, Build.ofK_add,
          add_assoc]

/-- A lane asserted equal to its bits' word. -/
def laneG (B base : ℕ) (lane gate : Cell) : BM Unit :=
  sumG B base lane 64 >>= fun a ↦ assert0 a gate

theorem hsA_laneG {B base : ℕ} {lane gate : Cell} (hg : gate.val M = 1) :
    HsA c M (laneG B base lane gate) fun _ ↦
      kv M lane = ∑ z ∈ range 64, g ^ z * FK.toBF64 (M.k (B + base + z)) :=
  hsA_bind (hsA_of_hs (hs_sumG B base lane 64)) fun a ha ↦ hsA_mono (hsA_assert0 hg) fun _ h ↦ by
    rw [ha] at h
    have h0 : (lane.val M).c₀ + ∑ z ∈ range 64, Build.gpow z * M.k (B + base + z) = 0 := congrArg FE.c₀ h
    rw [kv, fk_eq_of_add h0, toBF64_sum]
    exact Finset.sum_congr rfl fun z _ ↦ by rw [FK.toBF64_mul, toBF64_gpow]

/-- A position cell: `Σ_{z<h} x^z·b_{base+z}` (from a zero `b_B + b_B`). -/
def posCell (B base h : ℕ) : BM Cell := lin .K 1 0 (kc B) (kc B) >>= fun z ↦ sumG B base z h

theorem hs_posCell (B base h : ℕ) :
    Hs c M (posCell B base h) fun r ↦
      kv M r = ∑ z ∈ range h, g ^ z * FK.toBF64 (M.k (B + base + z)) :=
  hs_bind (hs_lin .K 1 0 (kc B) (kc B)) fun z hz ↦ hs_mono (hs_sumG B base z h) fun r hr ↦ by
    have hz0 : (z.val M).c₀ = 0 := by
      rw [hz]
      simp only [Cell.val_K, ← Build.ofK_mul, ← Build.ofK_add]
      show M.k B + 1 * M.k B + 0 = 0
      rw [one_mul, add_zero, fk_add_self]
    have : (r.val M).c₀ = (z.val M).c₀ + ∑ z ∈ range h, Build.gpow z * M.k (B + base + z) :=
      congrArg FE.c₀ hr
    rw [kv, this, hz0, zero_add, toBF64_sum]
    exact Finset.sum_congr rfl fun z _ ↦ by rw [FK.toBF64_mul, toBF64_gpow]

/-- The draw cells as a function of `ℕ`. -/
def dsAt {kq : ℕ} (ds : Fin (kq + 1) → C2) (j : ℕ) : C2 :=
  if hj : j < kq + 1 then ds ⟨j, hj⟩ else default

/-- Draws `0 … n − 1`: lane 0 on bits `128j …`, lane 1 on bits `128j + 64 …`. -/
def lanesG (B : ℕ) (gate : Cell) (dd : ℕ → C2) : ℕ → BM Unit
  | 0 => pure ()
  | n + 1 => lanesG B gate dd n >>= fun _ ↦ laneG B (128 * n) (dd n).re gate >>= fun _ ↦
      laneG B (128 * n + 64) (dd n).im gate

theorem hsA_lanesG {B : ℕ} {gate : Cell} (hg : gate.val M = 1) (dd : ℕ → C2) : ∀ n,
    HsA c M (lanesG B gate dd n) fun _ ↦ ∀ j < n,
      kv M (dd j).re = ∑ z ∈ range 64, g ^ z * FK.toBF64 (M.k (B + 128 * j + z)) ∧
      kv M (dd j).im = ∑ z ∈ range 64, g ^ z * FK.toBF64 (M.k (B + (128 * j + 64) + z))
  | 0 => hsA_pure fun j hj ↦ absurd hj (Nat.not_lt_zero j)
  | n + 1 => hsA_bind (hsA_lanesG hg dd n) fun _ h₁ ↦ hsA_bind (hsA_laneG hg) fun _ h₂ ↦
      hsA_mono (hsA_laneG hg) fun _ h₃ j hj ↦ by
        rcases Nat.lt_succ_iff_lt_or_eq.mp hj with h | rfl
        · exact h₁ j h
        · exact ⟨h₂, h₃⟩

/-- Positions `0 … t − 1`. -/
def posCells (B h c : ℕ) : ℕ → BM (List Cell)
  | 0 => pure []
  | t + 1 => posCells B h c t >>= fun ps ↦ posCell B (128 * (t / c) + h * (t % c)) h >>= fun p ↦
      pure (ps ++ [p])

theorem hs_posCells (B h cc : ℕ) : ∀ t,
    Hs c M (posCells B h cc t) fun ps ↦ ps.map (kv M) = (List.range t).map fun k ↦
      ∑ z ∈ range h, g ^ z * FK.toBF64 (M.k (B + (128 * (k / cc) + h * (k % cc)) + z))
  | 0 => hs_pure rfl
  | t + 1 => hs_bind (hs_posCells B h cc t) fun ps hps ↦ hs_bind (hs_posCell B _ h) fun p hp ↦
      hs_pure (by rw [List.map_append, hps, List.range_succ, List.map_append]; simp [hp])

/-- **The deployed position gadget** with its bit cells from `B`. -/
def posGen (B h c kq t : ℕ) (ds : Fin (kq + 1) → C2) (gate : Cell) : BM (List Cell) :=
  boolsG B gate (128 * (kq + 1)) >>= fun _ ↦ lanesG B gate (dsAt ds) (kq + 1) >>= fun _ ↦
    posCells B h c t

/-! ## The digits -/

/-- A lane's bits are the asserted bits. -/
theorem lane_bits {T : ℕ → K} {w : K} (hT : ∀ z < 64, T z = 0 ∨ T z = 1)
    (hw : w = ∑ z ∈ range 64, g ^ z * T z) (z : ℕ) (hz : z < 64) :
    (kToNat w).testBit z = decide (T z = 1) := by
  have hrep := congrArg bitsK (hw.trans (sum_bits_eq_rep le_rfl T hT))
  rw [bitsK_rep] at hrep
  have := congrFun hrep ⟨z, hz⟩
  simp only [bitsK] at this
  show w.toBitVec.toNat.testBit z = _
  rw [BitVec.testBit_toNat, this]
  simp [hz]

/-- **A position's digit**: the asserted bits of its draw. -/
theorem digit_eq {h off : ℕ} {T : ℕ → K} (hT : ∀ z < 128, T z = 0 ∨ T z = 1) {re im : K}
    (hre : re = ∑ z ∈ range 64, g ^ z * T z) (him : im = ∑ z ∈ range 64, g ^ z * T (64 + z))
    (hh : h ≤ 64) (hoff : off + h ≤ 128) :
    kToNat (∑ z ∈ range h, g ^ z * T (off + z)) =
      (kToNat re + 2 ^ 64 * kToNat im) / 2 ^ off % 2 ^ h := by
  set N := kToNat re + 2 ^ 64 * kToNat im
  set d := N / 2 ^ off % 2 ^ h
  have hd : d < 2 ^ 64 :=
    lt_of_lt_of_le (Nat.mod_lt _ (by positivity)) (Nat.pow_le_pow_right (by norm_num) hh)
  have hNbit : ∀ n < 128, N.testBit n = decide (T n = 1) := by
    intro n hn
    have hre' := lane_bits (fun z hz ↦ hT z (by omega)) hre
    have him' := lane_bits (T := fun z ↦ T (64 + z)) (fun z hz ↦ hT (64 + z) (by omega)) him
    have hN : N = 2 ^ 64 * kToNat im + kToNat re := by simp only [N]; ring
    rw [hN, Nat.testBit_two_pow_mul_add _ (show LeanVM.Protocol.Verifier.kToNat re < 2 ^ 64 from
      re.toBitVec.isLt)]
    split_ifs with h64
    · exact hre' n h64
    · rw [him' (n - 64) (by omega), show 64 + (n - 64) = n by omega]
  rw [← kToNat_ofBits hd]
  congr 1
  rw [sum_bits_eq_rep hh (fun z ↦ T (off + z)) (fun z hz ↦ hT _ (by omega)), ← rep_bitsK (K.ofBits d)]
  congr 1
  funext i
  rw [bitsK_ofBits d i i.isLt]
  simp only [d, Nat.testBit_mod_two_pow, Nat.testBit_div_two_pow]
  by_cases hi : (i : ℕ) < h
  · rw [show (i : ℕ) + off = off + i by omega, hNbit (off + i) (by omega)]
    try simp [hi]
  · simp [hi]

/-- **CC-3a proved**: the gadget computes W1's deployed positions, for every bit base `B`. -/
theorem posE2Har (B : ℕ) : PosE2Stmt (posGen B) := by
  intro h c kq t hc ht hch hh cc M ds gate hg
  refine hsA_bind (hsA_boolsG hg _) fun _ hb ↦ hsA_bind (hsA_lanesG hg (dsAt ds) _) fun _ hl ↦
    hsA_of_hs (hs_mono (hs_posCells B h c t) fun ps hps ↦ ?_)
  set T : ℕ → K := fun i ↦ FK.toBF64 (M.k (B + i)) with hTdef
  have hT : ∀ i < 128 * (kq + 1), T i = 0 ∨ T i = 1 := fun i hi ↦ fk_bool (hb i hi)
  have hlen : ps.length = t := by simpa using congrArg List.length hps
  unfold posOf
  apply List.ext_getElem
  · simp [hlen]
  intro k h1 _
  have hk : k < t := by simpa [hlen] using h1
  have hj : k / c < kq + 1 := (Nat.div_lt_iff_lt_mul hc).mpr (by omega)
  have hpk : kv M ps[k] = ∑ z ∈ range h, g ^ z * T (128 * (k / c) + (h * (k % c) + z)) := by
    have e := congrArg (fun l ↦ l[k]?) hps
    simp only [List.getElem?_map, List.getElem?_eq_getElem (by omega : k < ps.length),
      List.getElem?_range hk, Option.map_some, Option.some.injEq] at e
    rw [e]
    exact Finset.sum_congr rfl fun z _ ↦ by simp only [hTdef]; congr 3; omega
  have hkc : h * (k % c) + h ≤ 128 := by
    have := Nat.mod_lt k hc
    calc h * (k % c) + h = h * (k % c + 1) := by ring
      _ ≤ h * c := Nat.mul_le_mul_left _ this
      _ ≤ 128 := by rw [Nat.mul_comm]; exact hch
  obtain ⟨hre, him⟩ := hl (k / c) hj
  have hT' : ∀ z < 128, T (128 * (k / c) + z) = 0 ∨ T (128 * (k / c) + z) = 1 :=
    fun z hz ↦ hT _ (by nlinarith)
  have hd := digit_eq (T := fun z ↦ T (128 * (k / c) + z)) hT'
    (re := kv M (dsAt ds (k / c)).re) (im := kv M (dsAt ds (k / c)).im)
    (hre.trans (Finset.sum_congr rfl fun z _ ↦ by simp only [hTdef]; congr 3; omega))
    (him.trans (Finset.sum_congr rfl fun z _ ↦ by simp only [hTdef]; congr 3; omega)) hh hkc
  simp only [List.getElem_map, List.getElem_ofFn]
  rw [hpk, hd]
  simp only [Whir.posE2, Whir.e2Nat, dsAt, dif_pos hj, ← pow_mul]
  rfl

end Lvm6.QC
