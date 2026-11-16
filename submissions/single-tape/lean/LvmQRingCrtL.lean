-- New for lvm2 S2GT (GT-L, 2026-11-15): the semantics of blob v4's looped `ν` gadget (`rowNuGL`, lever L1): the
-- squaring loop gives the Frobenius powers, the `ν` loop the components' sums; `rowNuGL`'s cells meet `rowNuG`'s
-- specification (`hs_rowNuGL`), so `RowNuOk` follows as for `rowNuG` (`rowNuGL_ok`).
import LvmQRingCrtSem

/-!
# The looped row-switch `ν` (blob v4)

* `hs_frobLoop`: row `t` of `frobLoop zk as` at iteration `j < 64` is `as[t]^(2^(j+1))`.
* `Opd.val_abs_addr`: a later loop over the same dimensions reads `D.addr i` at its iteration `j` as `D`'s cell.
* `hs_nuLoop`: rows 64, 65 of the `ν` loop at iteration `j` are `(Σ_i D(i, j)·e_i)·r₆'` and `·r₆`.
* **`hs_rowNuGL`** (`hs_rowNuG`'s statement), **`rowNuGL_ok`**: iteration `(c + 63) mod 64` is component `c`
  (`a^(2^64) = a` in `K`).
-/

set_option autoImplicit false

noncomputable section

namespace Lvm.Q2

open Finset Lvm.Loop Lvm.Loop.Build Lvm.Har

variable {c : Ctx} {M : Mem}

theorem hs_const (τ : Ty) (k' : FK) (x : Cell) : Hs c M (const τ k' x) (fun r => r.val M = FE.ofK k') :=
  hs_mono (hs_lin τ 1 k' x x) fun r hr => by
    rw [hr, show FE.ofK 1 = 1 from rfl, one_mul]
    linear_combination x.val M * CharTwo.two_eq_zero (R := FE)

/-- `a^(2^64) = a` in `K`. -/
theorem fk_pow_two_pow_64 (a : FK) : a ^ 2 ^ 64 = a := by
  rw [← FK.card_FK]; exact FiniteField.pow_card a

/-- **The squaring loop**: row `t` at iteration `j < 64` is `as[t]^(2^(j+1))`. -/
theorem hs_frobLoop {zk : Cell} (hzk : zk.val M = 0) (as : List Cell) :
    Hs c M (frobLoop zk as) (fun D => D.dims = [6] ∧ ∀ t < as.length, ∀ j < 64,
      (D.cell t j).val M = (as.getD t default).val M ^ 2 ^ (j + 1)) := by
  intro p h
  refine ⟨rfl, fun t ht j hj => ?_⟩
  unfold frobLoop at h ⊢
  have htl : t < (frobTpl zk as.length).length := by simp [frobTpl, ht]
  have hrow : (frobTpl zk as.length).getD t default = ⟨.muladd, .K, [.prev t, .prev t, zk.opd]⟩ := by
    simp [frobTpl, List.getD_eq_getElem?_getD, ht]
  induction j with
  | zero =>
    have hr := lrel_muladd hrow (loopP_rel h (show 0 < 2 ^ [6].sum by decide) htl)
    simp only [List.getD_cons_zero, List.getD_cons_succ] at hr
    rw [hr, loopP_prev_zero h htl (fun e => by rw [hrow] at e; cases e), Cell.val_opd, hzk, add_zero]
    ring
  | succ j ih =>
    have hr := lrel_muladd hrow (loopP_rel h (show j + 1 < 2 ^ [6].sum by simp; omega) htl)
    simp only [List.getD_cons_zero, List.getD_cons_succ] at hr
    rw [hr, loopP_prev_succ M [6] _ _ p (show j + 1 < 2 ^ [6].sum by simp; omega), ih (by omega), Cell.val_opd,
      hzk, add_zero, ← pow_two, ← pow_mul, ← pow_succ]

/-- A loop over `D`'s dimensions reads `D.addr i` at its iteration `j` as `D`'s cell `(i, j)`. -/
theorem Opd.val_abs_addr (N D : LoopOut) (hd : N.dims = D.dims) {j : ℕ} (hj : j < 2 ^ D.dims.sum) (i : ℕ) :
    (Opd.abs (D.addr i)).val M N j = (D.cell i j).val M := by
  rw [← Opd.val_cur M D hj i]
  simp only [Opd.val, Opd.resolve, LoopOut.addr, hd]

theorem nuTpl_getD_lt (D : LoopOut) (e : List Cell) (r6' r6 : Cell) (z : ℕ) {i : ℕ} (hi : i < 64) :
    (nuTpl D e r6' r6 z).getD i default =
      ⟨.muladd, .E, [.abs (D.addr i), (e.getD i default).opd, if i = 0 then (ec z).opd else .cur (i - 1)]⟩ := by
  simp [nuTpl, List.getD_eq_getElem?_getD, List.getElem?_append_left (show i < ((List.range 64).map _).length by
    simpa using hi), hi]

theorem nuTpl_getD_64 (D : LoopOut) (e : List Cell) (r6' r6 : Cell) (z : ℕ) :
    (nuTpl D e r6' r6 z).getD 64 default = ⟨.muladd, .E, [.cur 63, r6'.opd, (ec z).opd]⟩ := by
  simp [nuTpl, List.getD_eq_getElem?_getD]

theorem nuTpl_getD_65 (D : LoopOut) (e : List Cell) (r6' r6 : Cell) (z : ℕ) :
    (nuTpl D e r6' r6 z).getD 65 default = ⟨.muladd, .E, [.cur 63, r6.opd, (ec z).opd]⟩ := by
  simp [nuTpl, List.getD_eq_getElem?_getD]

theorem nuTpl_length (D : LoopOut) (e : List Cell) (r6' r6 : Cell) (z : ℕ) : (nuTpl D e r6' r6 z).length = 66 := by
  simp [nuTpl]

/-- **The `ν` loop**: rows 64, 65 at iteration `j < 64` are `(Σ_i D(i, j)·e_i)·r₆'` and `·r₆`. -/
theorem hs_nuLoop (D : LoopOut) (hD : D.dims = [6]) (e : List Cell) (r6' r6 : Cell) {z : ℕ} (hz : M.e z = 0) :
    Hs c M (loop [6] (nuTpl D e r6' r6 z)) (fun N => ∀ j < 64,
      (N.cell 64 j).val M = (∑ i ∈ range 64, (D.cell i j).val M * (e.getD i default).val M) * r6'.val M ∧
      (N.cell 65 j).val M = (∑ i ∈ range 64, (D.cell i j).val M * (e.getD i default).val M) * r6.val M) := by
  intro p h j hj
  have hj' : j < 2 ^ [6].sum := by simpa using hj
  have hjD : j < 2 ^ D.dims.sum := by rw [hD]; exact hj'
  have hN : (loop [6] (nuTpl D e r6' r6 z) p).1.dims = D.dims := by rw [hD]; rfl
  have hacc : ∀ i < 64, ((loop [6] (nuTpl D e r6' r6 z) p).1.cell i j).val M =
      ∑ i' ∈ range (i + 1), (D.cell i' j).val M * (e.getD i' default).val M := by
    intro i hi
    induction i with
    | zero =>
      have hr := lrel_muladd (nuTpl_getD_lt D e r6' r6 z hi) (loop_rel h hj' (by rw [nuTpl_length]; omega))
      simp only [List.getD_cons_zero, List.getD_cons_succ, ↓reduceIte] at hr
      rw [hr, Opd.val_abs_addr _ D hN hjD, Cell.val_opd, Cell.val_opd, Cell.val_E, hz, add_zero,
        Finset.sum_range_one]
    | succ i ih =>
      have hr := lrel_muladd (nuTpl_getD_lt D e r6' r6 z hi) (loop_rel h hj' (by rw [nuTpl_length]; omega))
      simp only [List.getD_cons_zero, List.getD_cons_succ, Nat.add_one_ne_zero, ↓reduceIte, Nat.add_sub_cancel] at hr
      rw [hr, Opd.val_abs_addr _ D hN hjD, Cell.val_opd, Opd.val_cur M _ hj', ih (by omega),
        Finset.sum_range_succ _ (i + 1)]
      ring
  have h63 := hacc 63 (by norm_num)
  have h64 := lrel_muladd (nuTpl_getD_64 D e r6' r6 z) (loop_rel h hj' (by rw [nuTpl_length]; omega))
  have h65 := lrel_muladd (nuTpl_getD_65 D e r6' r6 z) (loop_rel h hj' (by rw [nuTpl_length]; omega))
  simp only [List.getD_cons_zero, List.getD_cons_succ] at h64 h65
  rw [Opd.val_cur M _ hj', h63, Cell.val_opd, Cell.val_opd, Cell.val_E, hz, add_zero] at h64 h65
  exact ⟨h64, h65⟩

/-- Iteration `(c + 63) mod 64` of the squaring loop is the `2^c`-th power (`c < 64`). -/
theorem pow_iter (a : FK) {k : ℕ} (hk : k < 64) : a ^ 2 ^ ((k + 63) % 64 + 1) = a ^ 2 ^ k := by
  rcases Nat.eq_zero_or_pos k with rfl | hk0
  · rw [show (0 + 63) % 64 + 1 = 64 from rfl, fk_pow_two_pow_64, pow_zero, pow_one]
  · rw [show (k + 63) % 64 + 1 = k by omega]

/-- **`rowNuGL`'s specification is `rowNuG`'s** (`hs_rowNuG`'s statement). -/
theorem hs_rowNuGL (rw : RowOut) {z o : ℕ} (hz : M.e z = 0) (ho : M.e o = 1)
    (hρ : ∀ i < 64, (rw.eqR.getD i default).val M =
        ((rw.eqR.getD i default).val M + (rw.eqR.getD (i + 64) default).val M) * (1 + (rw.rr.getD 6 default).val M) ∧
      (rw.eqR.getD (i + 64) default).val M =
        ((rw.eqR.getD i default).val M + (rw.eqR.getD (i + 64) default).val M) * (rw.rr.getD 6 default).val M) :
    Hs c M (rowNuGL rw z o) (fun nu => ∀ k < 64,
      (nu.nu0.getD k default).val M = nuH (fun j => (rw.eqR.getD j default).val M) false k ∧
      (nu.nu1.getD k default).val M = nuH (fun j => (rw.eqR.getD j default).val M) true k) := by
  unfold rowNuGL
  have hlin : ∀ a b : Cell, Hs c M (add a b) (fun r => r.val M = a.val M + b.val M) := fun a b =>
    hs_mono (hs_lin _ _ _ _ _) fun r hr => by rw [hr, show FE.ofK 1 = 1 from rfl, show FE.ofK 0 = 0 from rfl]; ring
  refine hs_bind (hs_mapB_getD _ (fun i (r : Cell) => r.val M = (rw.eqR.getD i default).val M +
    (rw.eqR.getD (i + 64) default).val M) 0 default (List.range 64) fun i _ => hlin _ _) fun e ⟨_, he⟩ => ?_
  have he' : ∀ i < 64, (e.getD i default).val M = (rw.eqR.getD i default).val M +
      (rw.eqR.getD (i + 64) default).val M := fun i hi => by
    have := he i (by simpa using hi)
    rwa [show (List.range 64).getD i 0 = i by simp [List.getD_eq_getElem?_getD, hi]] at this
  refine hs_bind (hs_const _ _ _) fun zk hzk => ?_
  refine hs_bind (hs_mapB_getD _ (fun i (r : Cell) => r.val M = FE.ofK (dualK i)) 0 default (List.range 64)
    fun i _ => hs_const _ _ _) fun ds ⟨hdl, hds⟩ => ?_
  have hds' : ∀ i < 64, (ds.getD i default).val M = FE.ofK (dualK i) := fun i hi => by
    have := hds i (by simpa using hi)
    rwa [show (List.range 64).getD i 0 = i by simp [List.getD_eq_getElem?_getD, hi]] at this
  rw [show FE.ofK 0 = 0 from rfl] at hzk
  refine hs_bind (hs_frobLoop hzk ds) fun D ⟨hD, hDv⟩ => ?_
  refine hs_bind (hlin _ _) fun r6' hr6' => ?_
  refine hs_bind (hs_nuLoop D hD e r6' (rw.rr.getD 6 default) hz) fun N hNv => hs_pure fun k hk => ?_
  have hj : (k + 63) % 64 < 64 := Nat.mod_lt _ (by norm_num)
  have hsum : ∑ i ∈ range 64, (D.cell i ((k + 63) % 64)).val M * (e.getD i default).val M =
      ∑ i ∈ range 64, dK k i * ((rw.eqR.getD i default).val M + (rw.eqR.getD (i + 64) default).val M) := by
    refine Finset.sum_congr rfl fun i hi => ?_
    have hi' := Finset.mem_range.mp hi
    rw [hDv i (by simpa using hdl ▸ hi') _ hj, hds' i hi', he' i hi', dK,
      show FE.ofK (dualK i) ^ 2 ^ ((k + 63) % 64 + 1) = FE.ofK (dualK i ^ 2 ^ ((k + 63) % 64 + 1)) from
        (map_pow FE.ofKRingHom _ _).symm, pow_iter _ hk]
  obtain ⟨h0, h1⟩ := hNv _ hj
  have g0 : ((List.range 64).map fun c => N.cell 64 ((c + 63) % 64)).getD k default = N.cell 64 ((k + 63) % 64) := by
    simp [List.getD_eq_getElem?_getD, hk]
  have g1 : ((List.range 64).map fun c => N.cell 65 ((c + 63) % 64)).getD k default = N.cell 65 ((k + 63) % 64) := by
    simp [List.getD_eq_getElem?_getD, hk]
  refine ⟨?_, ?_⟩
  · show (((List.range 64).map fun c => N.cell 64 ((c + 63) % 64)).getD k default).val M = _
    rw [g0, h0, hsum, hr6', Cell.val_E, ho, nuH, Finset.sum_mul]
    refine Finset.sum_congr rfl fun i hi => ?_
    rw [if_neg Bool.false_ne_true, Nat.add_zero]
    linear_combination (-(dK k i)) * (hρ i (Finset.mem_range.mp hi)).1
  · show (((List.range 64).map fun c => N.cell 65 ((c + 63) % 64)).getD k default).val M = _
    rw [g1, h1, hsum, nuH, Finset.sum_mul]
    refine Finset.sum_congr rfl fun i hi => ?_
    rw [if_pos rfl]
    linear_combination (-(dK k i)) * (hρ i (Finset.mem_range.mp hi)).2

/-- A loop row's cells at iterations `(c + 63) mod 64` (`rowNuGL`'s lists) are read back by `nuAt` (an `E` row). -/
theorem nuAt_loop (N : LoopOut) {t : ℕ} (hτ : (N.tpl.getD t default).ty = .E) {k : ℕ} (hk : k < 64) :
    nuAt ((List.range 64).map fun c => N.cell t ((c + 63) % 64)) ((k + 63) % 64) =
      ((List.range 64).map fun c => N.cell t ((c + 63) % 64)).getD k default := by
  have g : ∀ i < 64, ((List.range 64).map fun c => N.cell t ((c + 63) % 64)).getD i default =
      N.cell t ((i + 63) % 64) := fun i hi => by simp [List.getD_eq_getElem?_getD, hi]
  rw [g k hk]
  unfold nuAt
  rw [g 1 (by norm_num), g 2 (by norm_num)]
  simp only [LoopOut.cell, hτ, show (1 + 63) % 64 = 0 from rfl, show (2 + 63) % 64 = 1 from rfl, Nat.mul_zero,
    Nat.add_zero, Nat.mul_one, Nat.add_sub_cancel_left]

theorem hs_any {α : Type} (m : BM α) : Hs c M m (fun _ => True) := fun _ _ => trivial

theorem hs_loop_tpl (dims : List ℕ) (tpl : List LRow) : Hs c M (loop dims tpl) (fun N => N.tpl = tpl ∧ N.dims = dims) :=
  fun _ _ => ⟨rfl, rfl⟩

/-- **`rowNuGL`'s lists are its loop's rows 64, 65 as the looped leaves read them** (`nuAt`). -/
theorem hs_rowNuGL_at (rw : RowOut) (z o : ℕ) :
    Hs c M (rowNuGL rw z o) (fun nu => ∀ k < 64, nuAt nu.nu0 ((k + 63) % 64) = nu.nu0.getD k default ∧
      nuAt nu.nu1 ((k + 63) % 64) = nu.nu1.getD k default) := by
  unfold rowNuGL
  refine hs_bind (hs_any _) fun _ _ => hs_bind (hs_any _) fun _ _ => hs_bind (hs_any _) fun _ _ => ?_
  refine hs_bind (hs_any _) fun D _ => hs_bind (hs_any _) fun r6' _ => ?_
  refine hs_bind (hs_loop_tpl _ _) fun N hN => hs_pure fun k hk => ⟨?_, ?_⟩
  · exact nuAt_loop N (by rw [hN.1, nuTpl_getD_64]) hk
  · exact nuAt_loop N (by rw [hN.1, nuTpl_getD_65]) hk

/-- **`rowNuGL`'s cells stand for the switch's `eq` table** (`rowNuG_ok` for blob v4's looped gadget, as its leaves
read them). -/
theorem rowNuGL_ok (rw : RowOut) {z o : ℕ} (hz : M.e z = 0) (ho : M.e o = 1) (rv : List FE) (hrl : rv.length = 7)
    (hE : rw.eqR.map (Cell.val M) = eqKernel rv) (hr6 : (rw.rr.getD 6 default).val M = rv.getD 6 0) {p : Ptr}
    (h : SegsHold c M p (rowNuGL rw z o p).2) : RowNuOk M (rowNuGL rw z o p).1 (eqKernel rv) :=
  rowNuOk_of_v (rowNuOk_of_hs rw (hs_rowNuGL rw hz ho) rv hrl hE hr6 h) (hs_rowNuGL_at rw z o p h)

end Lvm.Q2
