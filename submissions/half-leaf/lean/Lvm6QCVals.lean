-- New for lvm6 (WP CCV). The deployed value gadget of a mid level (CC-3b): each opened row's lanes
-- folded at the domain point `K(p)` by the level's rounds, minus the high part `Ŵ_κ·Σ hi_s X_s`
-- at `K(p)` (W1's `valsE`), with the subspace polynomials by their recurrence (LvmNovelBasis's
-- `vanishingAt_succ`), never by their product.
import Lvm6QCPos
import Lvm6QKLayKit
import LvmE2VBaseLemmas

/-!
# The opened values at a mid level (generator and proof of `ValsEStmt`)

Exported for CC-8 (the final level's `fvE` check uses the same fold and the same tables):

* `cW i = W_i(e_i)` (a `K` constant, from the table `wRow` of `W_i(e_j)` by the recurrence
  `W_{i+1}(y) = W_i(y)·(W_i(y) + W_i(e_i))`; `cW_eq`); generation computes `≈ i²` products of `K`
  and one inversion per constant, the circuit none.
* `wConsts z n`: the class constants `W_i(e_i)`, `W_i(e_i)⁻¹` (`i < n`) as cells (`ConstsOK`).
* `vChain z cs (n − 1) 0 x`: the cells `W_0(a) … W_{n−1}(a)` from the point cell `x = a`
  (`w ↦ w·(w + W_i(e_i))`, 2 twin pairs a step; `hs_vChain`); `nStep`: `Ŵ_i(a) = W_i(a)·W_i(e_i)⁻¹`
  (1 twin pair, the inverse a constant cell: no free cell, no assertion); `novG`: `X_s(a)` as the
  product of `Ŵ_i(a)` over the bits of `s` (`hs_novG`).
* `foldG z x j rc ls`: the lanes `ls` (`2^j` cells) folded by the rounds `rc` at `x`
  (`L'(u) = L(2u+1) + (α + β·x)·L(2u)`, a zero round past the end of `rc`; `hs_foldG`), against
  `foldN` and W1's `foldRowE` (`foldRowE_nat`).
* `laneC`, `lanesC`: lane `s` of an opened row as a cell pair (level 0: `⟨word 63 − s, 0⟩`; else
  `⟨word 2s, word 2s + 1⟩`; a zero word or a short row reads the zero cell).
* **Instance class** (PHI-decision §3.2 item 4): `valsPre` (once per level: zero, one, constants),
  then `valAt` (**one call per opened row**, all constants entering as the prelude's cells, the
  row's words and the position as external cells; `hs_valAt`); **`valsGen`** = prelude + one
  instance per position; **`valsEHar : ValsEStmt valsGen`**.

Rows per position: `2n + n` twin pairs for the tables (`n = max (κ + 1) ℓ`), `≤ ℓ·(bits + 1)` for the
novel values, `ℓ + 1` for the high part, `2^ℓ − 1 + ℓ` for the fold, `1` for the difference.
-/

set_option autoImplicit false

namespace Lvm6.QC

open LeanVM.Parameters LeanVM.Protocol.Compile LeanVM.Protocol.Verifier LeanVM.Protocol.Whir
open Lvm Lvm.Loop Lvm.Loop.Build Lvm.Q2 Lvm.Har Lvm.E2V Lvm6.QK

/-! ## The subspace polynomials' constants -/

/-- One step of the recurrence: `y ↦ y·(y + c)`. -/
def wMul (c y : K) : K := y * (y + c)

/-- The next table row from row `i` (`c = W_i(e_i)` computed once, not per entry). -/
def wStep (i : ℕ) (r : List K) : List K := r.map (wMul (r.getD i 0))

/-- The table row `W_i(e_j)`, `j < n`, by the recurrence (level `0`: `e_j`). LAY4: one recursive call per level
(`wStep`); the earlier text re-evaluated `wRow n i` inside the map's function, `n^i` calls. -/
def wRow (n : ℕ) : ℕ → List K
  | 0 => (List.range n).map basisVec
  | i + 1 => wStep i (wRow n i)

theorem length_wRow (n : ℕ) : ∀ i, (wRow n i).length = n
  | 0 => by simp [wRow]
  | i + 1 => by simp [wRow, wStep, length_wRow n i]

theorem getD_map_lt {α β : Type} (f : α → β) (l : List α) (d : α) (e : β) {j : ℕ}
    (hj : j < l.length) : (l.map f).getD j e = f (l.getD j d) := by
  simp [List.getD_eq_getElem?_getD, hj]

theorem vanishingAt_zero_idx (a : K) : vanishingAt 0 a = a := by
  simp [vanishingAt]

theorem wRow_getD (n : ℕ) : ∀ i, i ≤ n → ∀ j < n, (wRow n i).getD j 0 = vanishingAt i (basisVec j)
  | 0, _, j, hj => by
    rw [wRow, getD_map_lt _ _ 0 _ (by simpa using hj), vanishingAt_zero_idx]
    simp [List.getD_eq_getElem?_getD, hj]
  | i + 1, hi, j, hj => by
    rw [wRow, wStep, getD_map_lt _ _ 0 _ (by rw [length_wRow]; exact hj), wMul, wRow_getD n i (by omega) j hj,
      wRow_getD n i (by omega) i (by omega), vanishingAt_succ]
    ring

/-- **`W_i(e_i)`**, from the table (no product over the subspace). -/
def cW (i : ℕ) : K := (wRow (i + 1) i).getD i 0

theorem cW_eq (i : ℕ) : cW i = vanishingAt i (basisVec i) := wRow_getD (i + 1) i (by omega) i (by omega)

/-! ## Values in `E2` -/

variable {c : Ctx} {M : Mem}

theorem hs2_prod {z : C2} (hz : ev2 M z = 0) : ∀ (acc : C2) (xs : List C2),
    Hs c M (g2Prod z acc xs) (fun r ↦ ev2 M r = ev2 M acc * (xs.map (ev2 M)).prod)
  | acc, [] => hs_pure (by simp)
  | acc, x :: xs => hs_bind (hs2_mul acc x z) fun s hs ↦ hs_mono (hs2_prod hz s xs) fun r hr ↦ by
    rw [hr, hs, hz, add_zero, List.map_cons, List.prod_cons, mul_assoc]

/-- A cell pair's value is its two words. -/
theorem ev2_mk (a b : Cell) : ev2 M ⟨a, b⟩ = (⟨kv M a, kv M b⟩ : E2) := rfl

theorem algebraMap_E2 (w : K) : algebraMap K E2 w = (⟨w, 0⟩ : E2) := rfl

theorem kv_re_zero {z : C2} (hz : ev2 M z = 0) : kv M z.re = 0 := congrArg QuadraticAlgebra.re hz

theorem getD_range_map {α : Type} (f : ℕ → α) (d : α) {N k : ℕ} (hk : k < N) :
    ((List.range N).map f).getD k d = f k := by
  simp [List.getD_eq_getElem?_getD, hk]

/-! ## The tables `W_i(a)`, `Ŵ_i(a)`, `X_s(a)` -/

/-- A `K` constant as a cell pair (from a zero `z`). -/
def kConst (w : K) (z : C2) : BM C2 := g2Const (FE2.ofK (FK.ofBF64 w)) z

theorem hs_kConst (w : K) (z : C2) : Hs c M (kConst w z) fun r ↦ ev2 M r = algebraMap K E2 w :=
  hs_mono (hs_g2Const _ z) fun _ hr ↦ by
    rw [ev2, hr, FE2.toE2_ofK, FK.toBF64_ofBF64]
    rfl

/-- **The class constants** `W_i(e_i)` and `W_i(e_i)⁻¹`, `i < n`, as cells (from a zero `z`). -/
def wConsts (z : C2) (n : ℕ) : BM (List C2 × List C2) :=
  mapB (fun i ↦ kConst (cW i) z) (List.range n) >>= fun cs ↦
    mapB (fun i ↦ kConst (cW i)⁻¹ z) (List.range n) >>= fun ci ↦ pure (cs, ci)

/-- The constants' cells hold `W_i(e_i)` and its inverse. -/
def ConstsOK (M : Mem) (z : C2) (n : ℕ) (k : List C2 × List C2) : Prop :=
  ∀ i < n, ev2 M (k.1.getD i z) = algebraMap K E2 (vanishingAt i (basisVec i)) ∧
    ev2 M (k.2.getD i z) = algebraMap K E2 (vanishingAt i (basisVec i))⁻¹

theorem hs_wConsts {z : C2} (hz : ev2 M z = 0) (n : ℕ) : Hs c M (wConsts z n) (ConstsOK M z n) :=
  hs_bind (hs2_mapB _ (fun i ↦ algebraMap K E2 (cW i)) _ fun i _ ↦ hs_kConst _ z) fun cs hcs ↦
    hs_bind (hs2_mapB _ (fun i ↦ algebraMap K E2 (cW i)⁻¹) _ fun i _ ↦ hs_kConst _ z) fun ci hci ↦
      hs_pure fun i hi ↦ ⟨by rw [ev2_getDz hcs hz, getD_range_map _ _ hi, cW_eq],
        by rw [ev2_getDz hci hz, getD_range_map _ _ hi, cW_eq]⟩

/-- One step `w ↦ w·(w + W_i(e_i))` (`W_{i+1}(a)` from `W_i(a)`; `cc` the constant's cell). -/
def vStep (z cc w : C2) : BM C2 := g2Add w cc >>= fun s ↦ g2Mul w s z

/-- `W_i(a), …, W_{i+m}(a)` from the cell `w` of `W_i(a)` (`cs` the constants' cells). -/
def vChain (z : C2) (cs : List C2) : ℕ → ℕ → C2 → BM (List C2)
  | 0, _, w => pure [w]
  | m + 1, i, w => vStep z (cs.getD i z) w >>= fun w' ↦ vChain z cs m (i + 1) w' >>= fun ws ↦
      pure (w :: ws)

theorem hs_vStep {z : C2} (hz : ev2 M z = 0) (i : ℕ) (a : K) (cc w : C2)
    (hc : ev2 M cc = algebraMap K E2 (vanishingAt i (basisVec i)))
    (hw : ev2 M w = algebraMap K E2 (vanishingAt i a)) :
    Hs c M (vStep z cc w) fun r ↦ ev2 M r = algebraMap K E2 (vanishingAt (i + 1) a) :=
  hs_bind (hs2_add w cc) fun s hs ↦ hs_mono (hs2_mul w s z) fun r hr ↦ by
    rw [hr, hs, hz, hw, hc, vanishingAt_succ]
    simp only [map_add, map_mul, map_pow]
    ring

theorem hs_vChain {z : C2} (hz : ev2 M z = 0) (cs : List C2) (N : ℕ)
    (hcs : ∀ i < N, ev2 M (cs.getD i z) = algebraMap K E2 (vanishingAt i (basisVec i))) (a : K) :
    ∀ (m i : ℕ) (w : C2), i + m ≤ N → ev2 M w = algebraMap K E2 (vanishingAt i a) →
    Hs c M (vChain z cs m i w) fun ws ↦
      ∀ j ≤ m, ev2 M (ws.getD j z) = algebraMap K E2 (vanishingAt (i + j) a)
  | 0, _, _, _, hw => hs_pure fun j hj ↦ by
      obtain rfl : j = 0 := by omega
      simpa using hw
  | m + 1, i, w, hm, hw => hs_bind (hs_vStep hz i a _ w (hcs i (by omega)) hw) fun w' hw' ↦
    hs_bind (hs_vChain hz cs N hcs a m (i + 1) w' (by omega) hw') fun ws hws ↦ hs_pure fun j hj ↦ by
      rcases j with _ | j
      · simpa using hw
      · rw [List.getD_cons_succ, hws j (by omega), show i + 1 + j = i + (j + 1) by omega]

/-- `Ŵ_i(a) = W_i(a)·W_i(e_i)⁻¹` (`ci` the inverse's cell). -/
def nStep (z ci w : C2) : BM C2 := g2Mul w ci z

theorem hs_nStep {z : C2} (hz : ev2 M z = 0) (i : ℕ) (a : K) (ci w : C2)
    (hc : ev2 M ci = algebraMap K E2 (vanishingAt i (basisVec i))⁻¹)
    (hw : ev2 M w = algebraMap K E2 (vanishingAt i a)) :
    Hs c M (nStep z ci w) fun r ↦ ev2 M r = algebraMap K E2 (normVanishingAt i a) :=
  hs_mono (hs2_mul w ci z) fun r hr ↦ by
    rw [hr, hz, hw, hc, normVanishingAt, map_mul, add_zero]

/-- `X_s(a)`: the product of `Ŵ_i(a)` over the bits `i < 64` of `s` (`one` a one). -/
def novG (z one : C2) (nws : List C2) (s : ℕ) : BM C2 :=
  g2Prod z one (((List.range 64).filter fun i ↦ s.testBit i).map fun i ↦ nws.getD i z)

theorem prod_range_list {R : Type} [CommMonoid R] (f : ℕ → R) : ∀ n,
    ∏ i ∈ Finset.range n, f i = ((List.range n).map f).prod
  | 0 => by simp
  | n + 1 => by
    rw [Finset.prod_range_succ, List.range_succ, List.map_append, List.prod_append, prod_range_list f n]
    simp

theorem sum_range_list {R : Type} [AddCommMonoid R] (f : ℕ → R) : ∀ n,
    ∑ i ∈ Finset.range n, f i = ((List.range n).map f).sum
  | 0 => by simp
  | n + 1 => by
    rw [Finset.sum_range_succ, List.range_succ, List.map_append, List.sum_append, sum_range_list f n]
    simp

theorem prod_map_ite_filter {R : Type} [CommMonoid R] (b : ℕ → Bool) (g : ℕ → R) : ∀ l : List ℕ,
    (l.map fun i ↦ if b i then g i else 1).prod = ((l.filter b).map g).prod
  | [] => rfl
  | x :: l => by
    by_cases h : b x <;> simp [h, prod_map_ite_filter b g l]

theorem hs_novG {z one : C2} (hz : ev2 M z = 0) (hone : ev2 M one = 1) (a : K) {n : ℕ}
    (nws : List C2) (hn : ∀ i < n, ev2 M (nws.getD i z) = algebraMap K E2 (normVanishingAt i a))
    (s : ℕ) (hs : s < n) :
    Hs c M (novG z one nws s) fun r ↦ ev2 M r = algebraMap K E2 (novelAt s a) :=
  hs_mono (hs2_prod hz one _) fun r hr ↦ by
    have e : ∀ i ∈ (List.range 64).filter (fun i ↦ s.testBit i),
        (ev2 M ∘ fun i ↦ nws.getD i z) i = algebraMap K E2 (normVanishingAt i a) := fun i hi ↦ by
      have hb : s.testBit i = true := (List.mem_filter.mp hi).2
      exact hn i (lt_of_lt_of_le Nat.lt_two_pow_self (le_trans (Nat.ge_two_pow_of_testBit hb) hs.le))
    rw [hr, hone, one_mul, List.map_map, List.map_congr_left e, ← prod_map_ite_filter,
      ← prod_range_list, novelAt, map_prod]
    exact Finset.prod_congr rfl fun i _ ↦ by by_cases hb : s.testBit i <;> simp [hb]

/-! ## The fold -/

/-- **The fold on `ℕ`-indexed lanes**: `j` rounds, the low bit first. -/
def foldN (x : E2) : ℕ → List (Whir.Rnd E2) → (ℕ → E2) → ℕ → E2
  | 0, _, F => F
  | j + 1, rs, F => foldN x j rs.tail fun u ↦
      F (2 * u + 1) + ((rs.headD default).α + (rs.headD default).β * x) * F (2 * u)

theorem bitsToNat_cons {n : ℕ} (b : Bool) (u : Fin n → Bool) :
    bitsToNat (Fin.cons b u : Fin (n + 1) → Bool) = 2 * bitsToNat u + b.toNat := by
  unfold bitsToNat
  rw [Fin.sum_univ_succ]
  simp only [Fin.cons_zero, Fin.cons_succ, Fin.val_zero, Fin.val_succ, pow_zero, mul_one, pow_succ,
    Finset.mul_sum]
  rw [add_comm]
  congr 1
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  ring

/-- **W1's `foldRowE` on lanes read by index** is `foldN`. -/
theorem foldRowE_nat (x : E2) {m : ℕ} : ∀ (j : ℕ) (rs : List (Whir.Rnd E2)) (F : ℕ → E2)
    (u : Fin m → Bool),
    Whir.foldRowE x j rs (fun v : Fin (m + j) → Bool ↦ F (bitsToNat v)) u = foldN x j rs F (bitsToNat u)
  | 0, _, _, _ => rfl
  | j + 1, rs, F, u => by
    refine Eq.trans ?_ (foldRowE_nat x j rs.tail (fun n ↦
      F (2 * n + 1) + ((rs.headD default).α + (rs.headD default).β * x) * F (2 * n)) u)
    show Whir.foldRowE x j rs.tail _ u = _
    congr 1
    funext v
    simp only [bitsToNat_cons, Bool.toNat_true, Bool.toNat_false, add_zero]

/-- A zero round. -/
def zR (z : C2) : RndC := ⟨z, z, z, z, z, z⟩

/-- **The lanes `ls` (`2^j` cells) folded by `j` rounds** of `rc` at `x` (a zero round past its end). -/
def foldG (z x : C2) : ℕ → List RndC → List C2 → BM C2
  | 0, _, ls => pure (ls.getD 0 z)
  | j + 1, rc, ls => g2Mul (rc.headD (zR z)).β x (rc.headD (zR z)).α >>= fun cc ↦
      mapB (fun u ↦ g2Mul cc (ls.getD (2 * u) z) (ls.getD (2 * u + 1) z)) (List.range (2 ^ j)) >>=
        fun ls' ↦ foldG z x j rc.tail ls'

theorem rnds_head {z : C2} (hz : ev2 M z = 0) {rc : List RndC} {rs : List (Whir.Rnd E2)}
    (h : RndsRep M rc rs) :
    ev2 M (rc.headD (zR z)).α = (rs.headD default).α ∧ ev2 M (rc.headD (zR z)).β = (rs.headD default).β ∧
      RndsRep M rc.tail rs.tail := by
  unfold RndsRep at h
  cases h with
  | nil => exact ⟨hz, hz, List.Forall₂.nil⟩
  | cons h₁ h₂ =>
    obtain ⟨-, -, -, -, h5, h6⟩ := h₁
    exact ⟨h5, h6, h₂⟩

theorem hs_foldG {z : C2} (hz : ev2 M z = 0) (x : C2) : ∀ (j : ℕ) (rc : List RndC)
    (rs : List (Whir.Rnd E2)), RndsRep M rc rs → ∀ (ls : List C2) (F : ℕ → E2),
    (∀ n < 2 ^ j, ev2 M (ls.getD n z) = F n) →
    Hs c M (foldG z x j rc ls) fun r ↦ ev2 M r = foldN (ev2 M x) j rs F 0
  | 0, _, _, _, ls, F, hF => hs_pure (hF 0 (by norm_num))
  | j + 1, rc, rs, hrep, ls, F, hF => by
    obtain ⟨ha, hb, ht⟩ := rnds_head hz hrep
    refine hs_bind (hs2_mul _ x _) fun cc hcc ↦ hs_bind (hs2_mapB _
      (fun u ↦ ev2 M cc * F (2 * u) + F (2 * u + 1)) _ fun u hu ↦ hs_mono (hs2_mul _ _ _) fun r hr ↦ ?_)
      fun ls' hls' ↦ hs_mono (hs_foldG hz x j rc.tail rs.tail ht ls'
        (fun u ↦ ev2 M cc * F (2 * u) + F (2 * u + 1)) fun n hn ↦ ?_) fun r hr ↦ ?_
    · have hu' := List.mem_range.mp hu
      rw [hr, hF (2 * u) (by rw [pow_succ]; omega), hF (2 * u + 1) (by rw [pow_succ]; omega)]
    · rw [ev2_getDz hls' hz, getD_range_map _ _ hn]
    · rw [hr]
      exact congrArg (fun G ↦ foldN (ev2 M x) j rs.tail G 0) (funext fun u ↦ by rw [hcc, ha, hb]; ring)

/-! ## Lanes of an opened row -/

/-- A row entry's cell: the lane's word, or the zero cell. -/
def entC (zk : Cell) : Option ℕ → Cell
  | none => zk
  | some a => kc a

/-- **Lane `s` of an opened row** (level 0: `⟨word 63 − s, 0⟩`; else `⟨word 2s, word 2s + 1⟩`). -/
def laneC (zz : Bool) (zk : Cell) (r : List (Option ℕ)) (s : ℕ) : C2 :=
  if zz then ⟨entC zk (r.getD (63 - s) none), zk⟩
  else ⟨entC zk (r.getD (2 * s) none), entC zk (r.getD (2 * s + 1) none)⟩

/-- The `2^ℓ` lanes of an opened row. -/
def lanesC (zz : Bool) (zk : Cell) (ℓ : ℕ) (r : List (Option ℕ)) : List C2 :=
  (List.range (2 ^ ℓ)).map (laneC zz zk r)

theorem kv_entC {zk : Cell} (hzk : kv M zk = 0) : ∀ o, kv M (entC zk o) = lw M o
  | none => hzk
  | some _ => rfl

theorem getD_rowsOf (r : List (Option ℕ)) (j : ℕ) : (r.map (lw M)).getD j 0 = lw M (r.getD j none) := by
  rw [show (0 : K) = lw M none from rfl, List.getD_map]

theorem ev2_laneC {zk : Cell} (hzk : kv M zk = 0) (zz : Bool) (r : List (Option ℕ)) (s : ℕ) :
    ev2 M (laneC zz zk r s) = Whir.laneVal zz (r.map (lw M)) s := by
  cases zz
  · simp only [laneC, Whir.laneVal, Bool.false_eq_true, ite_false, ev2_mk, kv_entC hzk, getD_rowsOf]
  · simp only [laneC, Whir.laneVal, ite_true, ev2_mk, kv_entC hzk, getD_rowsOf, hzk, algebraMap_E2]

/-! ## One position (the instance), every position (the class) -/

/-- **The value at one position**, one instance of the class: `pc` a `K` cell holding `a = K(p)`, `r`
its opened row; `z`, `one`, the constants' cells `cs`, `ci` and the cells `rc`, `hi` are the class's
inputs (no constant inside). The row's lanes folded at `a` by `rc`, plus (characteristic 2) the high
part `Ŵ_κ(a)·Σ_{s<ℓ} hi_s X_s(a)`. -/
def valAt (z one : C2) (k : List C2 × List C2) (zz : Bool) (ℓ κ : ℕ) (rc : List RndC) (hi : List C2)
    (pc : Cell) (r : List (Option ℕ)) : BM C2 :=
  vChain z k.1 (max (κ + 1) ℓ - 1) 0 ⟨pc, z.re⟩ >>= fun ws ↦
  mapB (fun i ↦ nStep z (k.2.getD i z) (ws.getD i z)) (List.range (max (κ + 1) ℓ)) >>= fun nws ↦
  mapB (novG z one nws) (List.range ℓ) >>= fun novs ↦
  g2Dot z ((List.range ℓ).map fun s ↦ (hi.getD s z, novs.getD s z)) >>= fun d ↦
  g2Mul (nws.getD κ z) d z >>= fun hv ↦
  foldG z ⟨pc, z.re⟩ ℓ rc (lanesC zz z.re ℓ r) >>= fun fv ↦
  g2Add fv hv

/-- **The class prelude**: a zero and a one (from the gate's cell), the constants `W_i(e_i)^{±1}`,
`i < max (κ + 1) ℓ`. -/
def valsPre (κ ℓ : ℕ) (gate : Cell) : BM (C2 × C2 × (List C2 × List C2)) :=
  g2Zero ⟨gate, gate⟩ >>= fun z ↦ g2Const 1 z >>= fun one ↦ wConsts z (max (κ + 1) ℓ) >>= fun k ↦
    pure (z, one, k)

/-- **The deployed value gadget**: the prelude, then one `valAt` instance per position cell `ps[k]`
with the row `rows[k]` (`[]` past the end). No assertions, no free cells. -/
def valsGen (zz : Bool) (_h ℓ κ : ℕ) (rc : List RndC) (hi : List C2) (ps : List Cell)
    (rows : List (List (Option ℕ))) (gate : Cell) : BM (List C2) :=
  valsPre κ ℓ gate >>= fun e ↦
    mapB (fun k ↦ valAt e.1 e.2.1 e.2.2 zz ℓ κ rc hi (ps.getD k gate) (rows.getD k []))
      (List.range ps.length)

/-- The value `valAt` computes. -/
noncomputable def valOf (rs : List (Whir.Rnd E2)) (zz : Bool) (ℓ κ : ℕ) (hi : List E2) (a : K)
    (row : List K) : E2 :=
  foldN (algebraMap K E2 a) ℓ rs (Whir.laneVal zz row) 0 +
    algebraMap K E2 (normVanishingAt κ a) *
      ((List.range ℓ).map fun s ↦ hi.getD s 0 * algebraMap K E2 (novelAt s a)).sum

theorem hs_valsPre (κ ℓ : ℕ) (gate : Cell) :
    Hs c M (valsPre κ ℓ gate) fun e ↦ ev2 M e.1 = 0 ∧ ev2 M e.2.1 = 1 ∧
      ConstsOK M e.1 (max (κ + 1) ℓ) e.2.2 :=
  hs_bind (hs_g2Zero _) fun z hz0 ↦ hs_bind (hs_g2Const 1 z) fun _ hone ↦
    hs_bind (hs_wConsts (ev2_zero hz0) _) fun _ hk ↦ hs_pure ⟨ev2_zero hz0, ev2_one' hone, hk⟩

/-- **One instance computes `valOf`.** -/
theorem hs_valAt {z one : C2} (hz : ev2 M z = 0) (hone : ev2 M one = 1) (k : List C2 × List C2)
    (zz : Bool) (ℓ κ : ℕ) (hk : ConstsOK M z (max (κ + 1) ℓ) k)
    {rc : List RndC} {rs : List (Whir.Rnd E2)} (hrep : RndsRep M rc rs) (hi : List C2) (pc : Cell)
    (r : List (Option ℕ)) :
    Hs c M (valAt z one k zz ℓ κ rc hi pc r) fun o ↦
      ev2 M o = valOf rs zz ℓ κ (hi.map (ev2 M)) (kv M pc) (r.map (lw M)) := by
  have hzk := kv_re_zero hz
  have hx : ev2 M ⟨pc, z.re⟩ = algebraMap K E2 (kv M pc) := by rw [ev2_mk, hzk]; rfl
  have hx0 : ev2 M ⟨pc, z.re⟩ = algebraMap K E2 (vanishingAt 0 (kv M pc)) := by
    rw [hx, vanishingAt_zero_idx]
  have hn1 : 0 + (max (κ + 1) ℓ - 1) ≤ max (κ + 1) ℓ := by omega
  refine hs_bind (hs_vChain hz k.1 _ (fun i hi ↦ (hk i hi).1) (kv M pc) _ 0 _ hn1 hx0) fun ws hws ↦
    hs_bind (hs2_mapB _ (fun i ↦ algebraMap K E2 (normVanishingAt i (kv M pc))) _ fun i hi ↦
      hs_nStep hz i _ _ _ (hk i (List.mem_range.mp hi)).2 (by
        have := List.mem_range.mp hi
        rw [hws i (by omega), zero_add])) fun nws hnws ↦ ?_
  have hn : ∀ i < max (κ + 1) ℓ, ev2 M (nws.getD i z) =
      algebraMap K E2 (normVanishingAt i (kv M pc)) := fun i hi ↦ by
    rw [ev2_getDz hnws hz, getD_range_map _ _ hi]
  refine hs_bind (hs2_mapB _ (fun s ↦ algebraMap K E2 (novelAt s (kv M pc))) _ fun s hs ↦
    hs_novG hz hone _ nws hn s (lt_of_lt_of_le (List.mem_range.mp hs) (le_max_right _ _)))
    fun novs hnovs ↦ hs_bind (hs2_dot z _) fun d hd ↦ hs_bind (hs2_mul _ d z) fun hv hhv ↦
    hs_bind (hs_foldG hz _ ℓ rc rs hrep _ (Whir.laneVal zz (r.map (lw M))) fun s hs ↦ ?_)
    fun fv hfv ↦ hs_mono (hs2_add fv hv) fun o ho ↦ ?_
  · rw [lanesC, getD_range_map _ _ hs, ev2_laneC hzk]
  · have hL : ((List.range ℓ).map fun s ↦ (hi.getD s z, novs.getD s z)).map
        (fun e ↦ ev2 M e.1 * ev2 M e.2) = (List.range ℓ).map fun s ↦
          (hi.map (ev2 M)).getD s 0 * algebraMap K E2 (novelAt s (kv M pc)) := by
      rw [List.map_map]
      refine List.map_congr_left fun s hs ↦ ?_
      simp only [Function.comp_apply]
      rw [ev2_getDz (l := hi) rfl hz, ev2_getDz hnovs hz, getD_range_map _ _ (List.mem_range.mp hs)]
    rw [ho, hfv, hhv, hz, add_zero, hd, hz, zero_add, hn κ (by omega), hx, hL]
    rfl

/-! ## The verifier's values -/

theorem ofBits_kToNat (a : K) : K.ofBits (kToNat a) = a := by
  apply BF64.toBitVec_injective
  apply BitVec.eq_of_toNat_eq
  exact kToNat_ofBits a.toBitVec.isLt

theorem domE_apply (h : ℕ) (hh : h ≤ 64) (p : Fin (2 ^ h)) :
    Whir.domE h hh p = algebraMap K E2 (K.ofBits p) := rfl

theorem bitsToNat_lane0 : bitsToNat Whir.lane0 = 0 := by simp [bitsToNat]

theorem eval_highF (κ ℓ : ℕ) (hi : List E2) (a : K) :
    (Whir.highF κ ℓ hi).eval (algebraMap K E2 a) = algebraMap K E2 (normVanishingAt κ a) *
      ((List.range ℓ).map fun s ↦ hi.getD s 0 * algebraMap K E2 (novelAt s a)).sum := by
  rw [Whir.highF, Whir.vanNF, Polynomial.eval_mul, Polynomial.eval_map, Polynomial.eval₂_at_apply,
    eval_normVanishing, Polynomial.eval_finsetSum, sum_range_list]
  congr 1
  congr 1
  refine List.map_congr_left fun s _ ↦ ?_
  rw [Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_map, Polynomial.eval₂_at_apply,
    eval_novel]

/-- **W1's `valsE` at one position** is `valOf` at its point. -/
theorem valsE_eq (zz : Bool) (h ℓ κ : ℕ) (hh : h ≤ 64) {t : ℕ} (rs : List (Whir.Rnd E2))
    (hi : List E2) (ps : Fin t → Fin (2 ^ h)) (rows : List (List K)) (k : Fin t) :
    Whir.valsE zz h ℓ κ hh rs hi ps rows k =
      valOf rs zz ℓ κ hi (K.ofBits (ps k)) (Whir.rowAt rows k) := by
  rw [Whir.valsE, valOf, CharTwo.sub_eq_add, domE_apply,
    foldRowE_nat _ ℓ rs (Whir.laneVal zz (Whir.rowAt rows k)), bitsToNat_lane0, eval_highF]

/-- **CC-3b proved**: the gadget computes W1's deployed mid-level values. -/
theorem valsEHar : ValsEStmt valsGen := by
  intro zz h ℓ κ hh t c M rc rs hrep hi ps rows gate _
  refine hsA_of_hs (hs_bind (hs_valsPre κ ℓ gate) fun e he ↦ ?_)
  obtain ⟨hz, hone, hk⟩ := he
  refine hs_mono (hs2_mapB _ (fun k ↦ valOf rs zz ℓ κ (hi.map (ev2 M)) (kv M (ps.getD k gate))
    ((rows.getD k []).map (lw M))) _ fun k _ ↦ hs_valAt hz hone e.2.2 zz ℓ κ hk hrep hi _ _)
    fun cs hcs p hp ↦ ?_
  have hlen : ps.length = t := by simpa [posOf] using congrArg List.length hp
  rw [hcs]
  apply List.ext_getElem
  · simp [hlen]
  intro k h1 _
  have hk : k < t := by simpa [hlen] using h1
  have hpk : kToNat (kv M ps[k]) = (p ⟨k, hk⟩ : ℕ) := by
    have e := congrArg (fun l ↦ l[k]?) hp
    simp only [posOf, List.getElem?_map, List.getElem?_eq_getElem (by omega : k < ps.length),
      List.getElem?_ofFn, Option.map_some] at e
    simp only [hk, ↓reduceDIte] at e
    exact Option.some.inj e
  simp only [List.getElem_map, List.getElem_range, List.getElem_ofFn]
  rw [valsE_eq, ← hpk, ofBits_kToNat, List.getD_eq_getElem?_getD,
    List.getElem?_eq_getElem (by omega : k < ps.length), Option.getD_some]
  congr 1
  show _ = (rows.map (·.map (lw M))).getD k []
  rw [show ([] : List K) = (([] : List (Option ℕ)).map (lw M)) from rfl, List.getD_map]

end Lvm6.QC
