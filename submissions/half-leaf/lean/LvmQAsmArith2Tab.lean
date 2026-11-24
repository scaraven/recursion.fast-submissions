-- New for lvm (HAR-BT): phase 3 of Q_arith (`tabPh`: ξ, the table sumcheck, the evaluations, the
-- constraints and bus forms over them, the final check) as one gadget `tabG` from the tables' static
-- shapes and phase 2's output cells, its replay theorem, and the committed columns' claims as cells.
-- Reuses QA2's `scRunP4_eq`, `tableW_eq`, `tableFinal_check`, `eqTab_eq`; the rest is this family's.
import LvmQBusGkr
import LvmQAsmArith2Bus
import LvmM3FidNative
import LvmQWhirBatch
import LvmBits

-- ===== merged from `LvmQTable` (GOLF module merge: `LvmQTable.lean` is now a stub importing `LvmQAsmArith2Tab`) =====
section
-- New for lvm (WP-11b-QA2, H2): the table sumcheck's weights and final check as straight-line
-- gadgets. Searched leanerVM `Protocol/TableSumcheck.lean` (`tableWeights` over `Fin τmax`, a
-- per-coordinate pair, no product closed form we could reuse) and `ClaimWeights.lean`; the closed
-- form `tableWeights_eq` below is new.

/-!
# The table sumcheck: weights and the final check (`F`'s `tableSumcheck`)

`F` (`LvmDecideSumcheck.tableSumcheck`): the rounds (plain, count 4: `LvmQBusRound.scRunP4`), the
point = the challenges reversed, the weights `tableWeights heights equalityPoint point` (per table
`Π_{c<R} (c < h ? 1 + e_c + r_c : r_c)`), the per-table terms (`tableTerms`, from the M3 tables'
constraints and bus forms: WP-9/WP-10, **inputs here**), and `require (final == claim)`.

* `tableWeights_eq`: the closed form `Π_{c < min h R} (1 + e_c + r_c) · Π_{j < R − min h R} ch_j`
  with `r_c = ch_{R−1−c}` (`ch` the challenges in round order: the suffix products of the point are
  prefix products of the challenges).
* `prefG`: a running product (one `E·E+E` row per factor, after the factor's own rows);
  `tableW`: the prefix products `A_m` (a `lin` and a product row per coordinate), the challenges'
  prefix products `B_m` (one row per round) and one row per table, `A_{min h R} · B_{R − min h R}`.
  Rows: `3R + T` (`R` `lin` 12 words, `2R + T` `E·E+E` 16 words).
* `tableFinal`: `Σ_t w_t · τ_t` (one row per table) and `assertEq` with the claim.

Theorems: **`tableW_spec`** (= `F`'s `tableWeights`), `tableTerms_final` (`F`'s final is
`finalOf weights terms`), **`tableFinal_check`** (gate on: assertion ↔ `F`'s `final == claim`).
-/

set_option autoImplicit false

namespace Lvm.QB

open Lvm DM

/-! ## `F`'s weights in closed form -/

/-- Table weight of height `h` from coordinate `k` on. -/
def wF (e pt : List FE) (k h : Nat) : FE :=
  ∏ j ∈ Finset.range pt.length, if k + j < h then 1 + e.getD (k + j) 0 + pt.getD j 0 else pt.getD j 0

theorem zipWith_zipWith_same {α β γ δ : Type} (f₁ : α → β → γ) (f₂ : γ → β → δ) :
    ∀ (ws : List α) (hs : List β),
      List.zipWith f₂ (List.zipWith f₁ ws hs) hs = List.zipWith (fun w h => f₂ (f₁ w h) h) ws hs
  | [], _ => rfl
  | _ :: _, [] => rfl
  | w :: ws, h :: hs => by simp [zipWith_zipWith_same f₁ f₂ ws hs]

theorem zipWith_mul_one (hs : List Nat) : ∀ ws : List FE, ws.length ≤ hs.length →
    List.zipWith (fun w (_ : Nat) => w * 1) ws hs = ws
  | [], _ => by simp
  | w :: ws, h => by
    cases hs with
    | nil => simp at h
    | cons x hs =>
      simp only [List.zipWith_cons_cons, mul_one, List.cons.injEq, true_and]
      have := zipWith_mul_one hs ws (by simpa using h)
      simpa using this

/-- The fold of `tableWeights` from coordinate `k` on. -/
theorem weights_fold (e : List FE) (hs : List Nat) (pt : List FE) : ∀ (k : Nat) (ws : List FE),
    ws.length ≤ hs.length →
    (pt.zipIdx k).foldl (fun weights (x : FE × Nat) =>
      List.zipWith (fun weight height => weight * if x.2 < height then 1 + e.getD x.2 0 + x.1 else x.1)
        weights hs) ws =
      List.zipWith (fun w h => w * wF e pt k h) ws hs := by
  induction pt with
  | nil =>
    intro k ws hl
    simp only [List.zipIdx_nil, List.foldl_nil, wF, List.length_nil, Finset.range_zero,
      Finset.prod_empty]
    exact (zipWith_mul_one hs ws hl).symm
  | cons r pt ih =>
    intro k ws hl
    rw [List.zipIdx_cons, List.foldl_cons]
    have hl' : (List.zipWith (fun weight height => weight *
        if k < height then 1 + e.getD k 0 + r else r) ws hs).length ≤ hs.length := by
      rw [List.length_zipWith]; exact Nat.min_le_right _ _
    have := ih (k + 1) _ hl'
    refine this.trans ?_
    rw [zipWith_zipWith_same]
    refine congrArg (List.zipWith · ws hs) (funext fun w => funext fun h => ?_)
    simp only [wF, List.length_cons, Finset.prod_range_succ', List.getD_cons_succ,
      List.getD_cons_zero, Nat.add_zero]
    rw [mul_assoc, mul_comm (if k < h then _ else _)]
    congr 2
    refine Finset.prod_congr rfl fun j _ => ?_
    rw [show k + (j + 1) = k + 1 + j by (clear * - k j e hs r ws; omega)]

/-- **`F`'s table weights**: one product per table. -/
theorem tableWeights_eq (hs : List Nat) (e pt : List FE) :
    tableWeights hs e pt = hs.map (wF e pt 0) := by
  unfold tableWeights
  dsimp only
  rw [weights_fold e hs pt 0 _ (by simp)]
  induction hs with
  | nil => rfl
  | cons h hs ih => simp only [List.map_cons, List.zipWith_cons_cons, one_mul, ih]

/-- **`F`'s weights at the reversed challenges** in closed form: with `m = min h R`,
`Π_{c<m} (1 + e_c + ch_{R−1−c}) · Π_{j < R − m} ch_j`. -/
theorem wF_rev (e chs : List FE) (h : Nat) :
    wF e chs.reverse 0 h =
      (∏ c ∈ Finset.range (min h chs.length),
        (1 + e.getD c 0 + chs.getD (chs.length - 1 - c) 0)) *
      ∏ j ∈ Finset.range (chs.length - min h chs.length), chs.getD j 0 := by
  set R := chs.length with hR
  set m := min h R with hm
  have hrev : ∀ c < R, chs.reverse.getD c 0 = chs.getD (R - 1 - c) 0 := by
    intro c hc
    rw [List.getD_eq_getElem _ _ (by simp; (clear * - hc; omega)), List.getElem_reverse,
      List.getD_eq_getElem _ _ (by (clear * - R c chs h hc; omega))]
  unfold wF
  rw [List.length_reverse, ← hR, show R = m + (R - m) by (clear * - R m chs h; omega), Finset.prod_range_add]
  rw [show m + (R - m) - m = R - m by (clear * - m R chs h; omega)]
  congr 1
  · refine Finset.prod_congr rfl fun c hc => ?_
    have hc' := Finset.mem_range.mp hc
    rw [if_pos (by (clear * - c h chs hc'; omega)), Nat.zero_add, hrev c (by (clear * - c R chs h hc'; omega))]
    congr 3; (clear * - R m chs h c hc'; omega)
  · rw [← Finset.prod_range_reflect (fun j => chs.getD j 0)]
    refine Finset.prod_congr rfl fun x hx => ?_
    have hx' := Finset.mem_range.mp hx
    rw [if_neg (by (clear * - m x h chs hx'; omega)), hrev _ (by (clear * - m x R chs h hx'; omega))]
    congr 1; (clear * - R m x chs h; omega)

/-! ## `F`'s final: the weighted sum of the terms -/

/-- `Σ_t w_t · τ_t`, accumulated as `F` does. -/
def finalOf (ws ts : List FE) (f₀ : FE) : FE := (ws.zip ts).foldl (fun f wt => f + wt.1 * wt.2) f₀

/-- The per-table terms `tableTerms` adds (`summand + dot formPowers forms`), in order. -/
def tableTermT (constraintPowers formPowers point : List FE) :
    List (TableSpec × List Form × FE) → Nat → DM (List FE)
  | [], _ => pure []
  | (table, forms, _) :: rest, cursor => do
    let evaluations ← readEs table.width
    let tpoint := point.take table.logHeight
    let summand := dot ((constraintPowers.drop cursor).take table.nConstraints)
      (table.constraints tpoint evaluations)
    let term := summand + dot formPowers (forms.map (·.value (evaluations.getD · 0)))
    let terms ← tableTermT constraintPowers formPowers point rest (cursor + table.nConstraints)
    pure (term :: terms)

/-- **`F`'s table final** is `finalOf` of the weights and the terms (same reads). -/
theorem tableTerms_final (cp fp point : List FE) (sig : ByteArray) :
    ∀ (rows : List (TableSpec × List Form × FE)) (cursor : Nat) (final : FE) (s : RS),
      (tableTerms cp fp point rows cursor final sig s).1.1 =
          finalOf (rows.map (·.2.2)) (tableTermT cp fp point rows cursor sig s).1 final ∧
        (tableTerms cp fp point rows cursor final sig s).2 = (tableTermT cp fp point rows cursor sig s).2
  | [], _, _, _ => ⟨rfl, rfl⟩
  | (table, forms, weight) :: rest, cursor, final, s => by
    have ih := fun f s' => tableTerms_final cp fp point sig rest (cursor + table.nConstraints) f s'
    show (tableTerms cp fp point rest (cursor + table.nConstraints) (final + weight * _) sig
        (readEs table.width sig s).2).1.1 = _ ∧ (tableTerms cp fp point rest _ _ sig _).2 = _
    rw [(ih _ _).1, (ih _ _).2]
    exact ⟨rfl, rfl⟩

end Lvm.QB

namespace Lvm.Loop.Build.QB

open Lvm.Loop Lvm.QB

/-! ## The weights gadget -/

/-- **A running product** `o · x₀ ⋯ x_{n−1}` (the factor `x_c` from the gadget `step c`), all
its running values `[A₀, …, A_n]`. -/
def prefG (z o : Cell) (step : Nat → BM Cell) : Nat → BM (List Cell)
  | 0 => pure [o]
  | n + 1 => do
    let as ← prefG z o step n
    let x ← step n
    let a ← mulAdd .E x (as.getD n o) z
    pure (as ++ [a])

/-- One weight per table: `A_{min h R} · B_{R − min h R}`. -/
def weightsG (z o : Cell) (A B : List Cell) (R : Nat) : List Nat → BM (List Cell)
  | [] => pure []
  | h :: hs => do
    let w ← mulAdd .E (A.getD (min h R) o) (B.getD (R - min h R) o) z
    let ws ← weightsG z o A B R hs
    pure (w :: ws)

/-- **The table weights**: `e c` the equality point's cells, `ch j` the table sumcheck's challenge
cells (round order), `R` the rounds, `hs` the tables' heights. -/
def tableW (z o : Cell) (e ch : Nat → Cell) (R : Nat) (hs : List Nat) : BM (List Cell) := do
  let A ← prefG z o (fun c => lin .E 1 1 (e c) (ch (R - 1 - c))) R
  let B ← prefG z o (fun j => pure (ch j)) R
  weightsG z o A B R hs

section
variable {c : Ctx} {M : Mem}

theorem prefG_spec {z o : Cell} (hz : z.val M = 0) (ho : o.val M = 1) (step : Nat → BM Cell)
    (fv : Nat → FE) (hstep : ∀ k, ASpec c M (step k) (fun x => x.val M = fv k) True) :
    ∀ n, ASpec c M (prefG z o step n)
      (fun as => as.length = n + 1 ∧ ∀ m ≤ n, (as.getD m o).val M = ∏ k ∈ Finset.range m, fv k) True
  | 0 => aspec_pure ⟨rfl, fun m hm => by
      obtain rfl : m = 0 := by (clear * - hm; omega)
      simp [ho]⟩
  | n + 1 => by
    show ASpec c M (prefG z o step n >>= fun as => step n >>= fun x =>
      mulAdd .E x (as.getD n o) z >>= fun a => pure (as ++ [a])) _ _
    refine aspec_congr (aspec_bind (prefG_spec hz ho step fv hstep n) fun as has =>
      aspec_bind (hstep n) fun x hx =>
        aspec_bind (aspec_mulAdd (c := c) (M := M) .E x (as.getD n o) z) fun a ha =>
          aspec_pure (x := as ++ [a]) ?_) (fun _ h => h) (by simp)
    refine ⟨by simp [has.1], fun m hm => ?_⟩
    rcases Nat.lt_or_ge m (n + 1) with hlt | hge
    · rw [List.getD_append _ _ _ _ (by (clear * - has hlt; omega))]; exact has.2 m (by (clear * - hlt; omega))
    · obtain rfl : m = n + 1 := by (clear * - hm hge; omega)
      rw [List.getD_append_right _ _ _ _ (by (clear * - has; omega)), has.1, Nat.sub_self]
      simp only [List.getD_cons_zero]
      rw [ha, hx, has.2 n le_rfl, hz, add_zero, Finset.prod_range_succ, mul_comm]

theorem weightsG_spec {z o : Cell} (hz : z.val M = 0) (A B : List Cell) (R : Nat) (fA fB : Nat → FE)
    (hA : ∀ m ≤ R, (A.getD m o).val M = fA m) (hB : ∀ m ≤ R, (B.getD m o).val M = fB m) :
    ∀ hs : List Nat, ASpec c M (weightsG z o A B R hs)
      (fun ws => vals M ws = hs.map fun h => fA (min h R) * fB (R - min h R)) True
  | [] => aspec_pure rfl
  | h :: hs => by
    show ASpec c M (mulAdd .E (A.getD (min h R) o) (B.getD (R - min h R) o) z >>= fun w =>
      weightsG z o A B R hs >>= fun ws => pure (w :: ws)) _ _
    refine aspec_congr (aspec_bind (aspec_mulAdd (c := c) (M := M) .E _ _ z) fun w hw =>
      aspec_bind (weightsG_spec hz A B R fA fB hA hB hs) fun ws hws =>
        aspec_pure (x := w :: ws) ?_) (fun _ h => h) (by simp)
    simp only [vals, List.map_cons] at hws ⊢
    rw [hws, hw, hA _ (Nat.min_le_right _ _), hB _ (Nat.sub_le _ _), hz, add_zero]

/-- **The weights gadget's values**, in closed form. -/
theorem tableW_spec {z o : Cell} (hz : z.val M = 0) (ho : o.val M = 1) (e ch : Nat → Cell) (R : Nat)
    (hs : List Nat) :
    ASpec c M (tableW z o e ch R hs)
      (fun ws => vals M ws = hs.map fun h =>
        (∏ k ∈ Finset.range (min h R), (1 + (e k).val M + (ch (R - 1 - k)).val M)) *
          ∏ j ∈ Finset.range (R - min h R), (ch j).val M) True := by
  have hA := prefG_spec (c := c) hz ho (fun k => lin .E 1 1 (e k) (ch (R - 1 - k)))
    (fun k => 1 + (e k).val M + (ch (R - 1 - k)).val M)
    (fun k => aspec_congr (aspec_lin .E 1 1 _ _) (fun x hx => by
      rw [hx, ofK_one, one_mul]; ring) Iff.rfl) R
  have hB := prefG_spec (c := c) hz ho (fun j => pure (ch j)) (fun j => (ch j).val M)
    (fun j => aspec_pure rfl) R
  have := aspec_bind hA fun A hA' => aspec_bind hB fun B hB' =>
    weightsG_spec (c := c) hz A B R _ _ hA'.2 hB'.2 hs
  exact aspec_congr this (fun _ h => h) (by simp)

/-- **Q_arith_eq, the table weights**: with the cells holding `F`'s equality point and the
table sumcheck's challenges (`R` of them), the outputs are `F`'s `tableWeights heights
equalityPoint (challenges.reverse)`. -/
theorem tableW_eq {z o : Cell} (hz : z.val M = 0) (ho : o.val M = 1) (e ch : Nat → Cell)
    (hs : List Nat) (eqPt chs : List FE) (he : ∀ k < chs.length, (e k).val M = eqPt.getD k 0)
    (hch : ∀ j < chs.length, (ch j).val M = chs.getD j 0) (p : Ptr)
    (h : SegsHold c M p (tableW z o e ch chs.length hs p).2) :
    vals M (tableW z o e ch chs.length hs p).1 = tableWeights hs eqPt chs.reverse := by
  rw [(tableW_spec (c := c) hz ho e ch chs.length hs p h).1, tableWeights_eq]
  refine List.map_congr_left fun hh _ => ?_
  rw [wF_rev]
  congr 1
  · refine Finset.prod_congr rfl fun k hk => ?_
    have hk' := Finset.mem_range.mp hk
    rw [he k (by (clear * - k chs hh hk'; omega)), hch _ (by (clear * - chs k hh hk'; omega))]
  · refine Finset.prod_congr rfl fun j hj => ?_
    have hj' := Finset.mem_range.mp hj
    rw [hch j (by (clear * - j chs hh hj'; omega))]

/-! ## The final check -/

/-- `acc + Σ_t w_t · τ_t` (one `E·E+E` row per table). -/
def dotFrom : Cell → List Cell → List Cell → BM Cell
  | acc, w :: ws, t :: ts => do
    let a ← mulAdd .E w t acc
    dotFrom a ws ts
  | acc, _, _ => pure acc

/-- **The table sumcheck's final check**: `Σ_t w_t · τ_t` (the terms `τ_t` are inputs) against the
sumcheck's final claim, gated. -/
def tableFinal (z gate claim : Cell) (ws ts : List Cell) : BM Unit := do
  let f ← dotFrom z ws ts
  assertEq f claim gate

theorem dotFrom_spec : ∀ (ws ts : List Cell) (acc : Cell),
    ASpec c M (dotFrom acc ws ts) (fun r => r.val M = finalOf (vals M ws) (vals M ts) (acc.val M)) True
  | w :: ws, t :: ts, acc => by
    show ASpec c M (mulAdd .E w t acc >>= fun a => dotFrom a ws ts) _ _
    refine aspec_congr (aspec_bind (aspec_mulAdd (c := c) (M := M) .E w t acc) fun a ha =>
      aspec_congr (dotFrom_spec ws ts a) (Q := fun r => r.val M =
        finalOf (vals M (w :: ws)) (vals M (t :: ts)) (acc.val M)) (fun r hr => by
          rw [hr, ha]; simp only [finalOf, vals, List.map_cons, List.zip_cons_cons, List.foldl_cons]
          rw [add_comm (w.val M * t.val M)]) Iff.rfl) (fun _ h => h) (by simp)
  | [], ts, acc => aspec_pure (by simp [finalOf, vals])
  | _ :: _, [], acc => aspec_pure (by simp [finalOf, vals])

/-- **Q_arith_eq, the table final check**: with `z = 0` and the gate on, the assertion holds iff
`F`'s `require (final == claim)` passes, `final = finalOf weights terms 0` (`tableTerms_final`). -/
theorem tableFinal_check {z gate claim : Cell} (hz : z.val M = 0) (hg : gate.val M = 1)
    (ws ts : List Cell) (p : Ptr) (h : SegsHold c M p (tableFinal z gate claim ws ts p).2) :
    SegsAssert M p (tableFinal z gate claim ws ts p).2 ↔
      (finalOf (vals M ws) (vals M ts) 0 == claim.val M) = true := by
  have := aspec_bind (dotFrom_spec (c := c) (M := M) ws ts z) fun f hf =>
    aspec_congr (aspec_assertEq (c := c) (M := M) f claim gate) (fun _ _ => trivial)
      (B := finalOf (vals M ws) (vals M ts) 0 = claim.val M)
      (by rw [hf, hz, gate_eq_iff hg])
  exact ((this p h).2.trans (by rw [true_and])).trans (FE.beq_iff _ _).symm

end

/-- Non-vacuity: the weights and the final check pass the program check. -/
theorem table_segsOk :
    segsOk ⟨1, 20⟩ (tableW (ec 0) (ec 1) (fun c => ec (2 + c)) (fun j => ec (6 + j)) 3 [1, 3, 2]
      ⟨1, 20⟩).2 = true ∧
      segsOk ⟨1, 20⟩ (tableFinal (ec 0) (kc 0) (ec 1) [ec 2, ec 3] [ec 4, ec 5] ⟨1, 20⟩).2 = true := by
  decide

end Lvm.Loop.Build.QB
end
-- ===== end of `LvmQTable` =====

-- ===== merged from `LvmQAsmArith2TabF` (GOLF module merge: `LvmQAsmArith2TabF.lean` is now a stub importing `LvmQAsmArith2Tab`) =====
section
-- New for lvm (HAR-BT): `F`'s table phase (`tabPh`) in the form the phase-3 gadget computes: the bus
-- forms' values as sums over a static stacking (`stackBlocks` of the shapes' blocks), the push and
-- pull sides merged (same stacking), block weights as `eqW` (split into a low table and a high
-- part), `BITS` output polynomials through suffix sums. Reuses WP-9b's `LvmM3FidNative`
-- (`bucketR_getD`, `sidesR`, `busFinalR_*_def`), QA2's `eqW_append`, core's `List.map_mergeSort`;
-- the rest is new (searched leanerVM `Protocol/{Bus,TableSumcheck}`, WP-9b's `LvmM3FidBus`: those
-- state the same objects over `E`, not as gadget-shaped sums).

/-!
# Phase 3, `F` side

* **Forms** (`value_leafForm`, `value_bucketN`): a leaf form's value is
  `β + α₀·sep + α₁·addr + α₂·cnt + Σ_l α_{3+l}·val_l` at the evaluations; a side's form of table `j`
  is `Σ_b w_b · value_b` over the side's stacked blocks of table `j`.
* **Static stacking** (`stackG`, `stackBlocks_map`): `stackBlocks` of blocks that are a map of static
  blocks (`SBlk`: table, height, key, read or seed) is `stackG` of the static ones; the push and pull
  sides are maps of the same static list (`sideBlocks_eq`), so they have the same weights.
* **Weights** (`blockWeight_eqW`): `blockWeight ζ κ off = eqW (ζ.drop κ) (off >>> κ)`.
* **Geometric forms** (`geoPoly`, `evalE_geo`): `Σ_{a≤z<e} x^{z−a+d} β_z = x^d (S a + x^{e−a} S e)`
  with the suffix sums `S k = β_k + x · S (k+1)`.
-/

set_option autoImplicit false

namespace Lvm.Har

open Lvm Lvm.M3 DM

/-! ## Sums -/

theorem foldl_add_from (l : List FE) (a : FE) : l.foldl (· + ·) a = a + l.foldl (· + ·) 0 := by
  induction l generalizing a with
  | nil => simp
  | cons x l ih => rw [List.foldl_cons, List.foldl_cons, ih, ih (0 + x)]; ring

theorem sumE_cons (x : FE) (l : List FE) : sumE (x :: l) = x + sumE l := by
  rw [sumE, List.foldl_cons, foldl_add_from, zero_add]; rfl

theorem sumE_nil : sumE [] = 0 := rfl

theorem sumE_append (a b : List FE) : sumE (a ++ b) = sumE a + sumE b := by
  rw [sumE, List.foldl_append, foldl_add_from]; rfl

theorem sumE_reverse (l : List FE) : sumE l.reverse = sumE l := by
  induction l with
  | nil => rfl
  | cons x l ih => rw [List.reverse_cons, sumE_append, ih, sumE_cons, sumE_cons, sumE_nil]; ring

theorem sumE_flatMap {α : Type} (f : α → List FE) (l : List α) :
    sumE (l.flatMap f) = sumE (l.map fun a => sumE (f a)) := by
  induction l with
  | nil => rfl
  | cons a l ih => rw [List.flatMap_cons, sumE_append, ih, List.map_cons, sumE_cons]

theorem sumE_map_mul {α : Type} (w : FE) (f : α → FE) (l : List α) :
    sumE (l.map fun a => w * f a) = w * sumE (l.map f) := by
  induction l with
  | nil => simp [sumE]
  | cons a l ih => rw [List.map_cons, List.map_cons, sumE_cons, sumE_cons, ih]; ring

theorem sumE_map_add {α : Type} (f g : α → FE) (l : List α) :
    sumE (l.map fun a => f a + g a) = sumE (l.map f) + sumE (l.map g) := by
  induction l with
  | nil => simp [sumE]
  | cons a l ih => rw [List.map_cons, List.map_cons, List.map_cons, sumE_cons, sumE_cons, sumE_cons, ih]; ring

theorem foldl_mul_one (m : List FE) (a : FE) : m.foldl (· * ·) a = a * m.foldl (· * ·) 1 := by
  induction m generalizing a with
  | nil => simp
  | cons x m ihm => rw [List.foldl_cons, List.foldl_cons, ihm, ihm (1 * x)]; ring

theorem foldl_mul_from (col : Nat → FE) (c : FE) (l : List Nat) :
    l.foldl (fun acc i => acc * col i) c = c * (l.map col).foldl (· * ·) 1 := by
  induction l generalizing c with
  | nil => simp
  | cons i l ih =>
    rw [List.foldl_cons, ih, List.map_cons, List.foldl_cons, foldl_mul_one _ (1 * col i)]; ring

/-! ## Values of forms -/

/-- A monomial's value at a row of `FE` values (`CPoly.evalE`'s summand). -/
def monV (v : Nat → FE) (m : FK × List Nat) : FE := FE.ofK m.1 * (m.2.map v).foldl (· * ·) 1

theorem evalE_eq (v : Nat → FE) (P : CPoly) : CPoly.evalE v P = sumE (P.map (monV v)) := rfl

theorem evalE_append (v : Nat → FE) (P Q : CPoly) :
    CPoly.evalE v (P ++ Q) = CPoly.evalE v P + CPoly.evalE v Q := by
  rw [evalE_eq, evalE_eq, evalE_eq, List.map_append, sumE_append]

theorem value_eq (f : Form) (col : Nat → FE) :
    f.value col = sumE (f.terms.map fun t => t.2 * (t.1.map col).foldl (· * ·) 1) := by
  rw [Form.value]
  exact congrArg sumE (List.map_congr_left fun t _ => foldl_mul_from col t.2 t.1)

theorem value_cpolyForm (w : FE) (P : CPoly) (col : Nat → FE) :
    (cpolyForm w P).value col = w * CPoly.evalE col P := by
  rw [value_eq, evalE_eq, ← sumE_map_mul]
  simp only [cpolyForm, List.map_map]
  exact congrArg sumE (List.map_congr_left fun m _ => by simp [monV]; ring)

theorem value_formSum (fs : List Form) (col : Nat → FE) :
    (formSum fs).value col = sumE (fs.map (·.value col)) := by
  rw [value_eq, formSum, List.map_flatMap, sumE_flatMap]
  exact congrArg sumE (List.map_congr_left fun f _ => (value_eq f col).symm)

theorem value_const (x : FE) (col : Nat → FE) : (Form.const x).value col = x := by
  simp [value_eq, Form.const, sumE]

theorem value_col (c : Nat) (col : Nat → FE) : (Form.col c).value col = col c := by
  simp [value_eq, Form.col, sumE, gpow]

/-- The value limbs' part of a leaf form. -/
def limbsV (eqα : List FE) (col : Nat → FE) (val : List CPoly) : FE :=
  sumE (val.zipIdx.map fun (P, l) => eqα.getD (3 + l) 0 * CPoly.evalE col P)

/-- **A leaf form's value.** -/
theorem value_leafForm (eqα : List FE) (β : FE) (k : Key) (cnt : CPoly) (col : Nat → FE) :
    (leafForm eqα β k cnt).value col =
      β + eqα.getD 0 0 * FE.ofK k.sep + eqα.getD 1 0 * CPoly.evalE col k.addr +
        eqα.getD 2 0 * CPoly.evalE col cnt + limbsV eqα col k.val := by
  rw [leafForm, value_formSum, List.map_append, sumE_append]
  simp only [List.map_cons, List.map_nil, sumE_cons, sumE_nil, value_const, value_cpolyForm,
    List.map_map, limbsV]
  rw [show ((fun f : Form => f.value col) ∘ fun x : CPoly × Nat => cpolyForm (eqα.getD (3 + x.2) 0) x.1) =
    fun x => eqα.getD (3 + x.2) 0 * CPoly.evalE col x.1 from funext fun x => value_cpolyForm _ _ _]
  ring

theorem value_bucketN (s : List (NBlock × FE)) (j : Nat) (col : Nat → FE) :
    (⟨bucketN s j⟩ : Form).value col =
      sumE ((s.filter fun bw => bw.1.tab == j).map fun bw => bw.2 * bw.1.form.value col) := by
  rw [value_eq, bucketN, List.map_flatMap, sumE_flatMap]
  rw [show ∀ (l : List (NBlock × FE)) (F : NBlock × FE → FE), sumE (l.reverse.map F) = sumE (l.map F) from
    fun l F => by rw [List.map_reverse, sumE_reverse]]
  refine congrArg sumE (List.map_congr_left fun bw _ => ?_)
  rw [List.map_map, value_eq, ← sumE_map_mul]
  exact congrArg sumE (List.map_congr_left fun t _ => by simp; ring)

/-! ## Static stacking -/

/-- `stackBlocks` on any type of blocks with heights `κ`. -/
def stackG {α : Type} (κ : α → Nat) (bs : List α) : List (α × Nat) :=
  ((bs.mergeSort fun a b => decide (κ b ≤ κ a)).foldl
    (fun (acc : List (α × Nat) × Nat) b => (acc.1 ++ [(b, acc.2)], acc.2 + 2 ^ κ b)) ([], 0)).1

theorem stackBlocks_map {α : Type} (κ : α → Nat) (f : α → NBlock) (hf : ∀ a, (f a).κ = κ a)
    (bs : List α) : stackBlocks (bs.map f) = (stackG κ bs).map fun bo => (f bo.1, bo.2) := by
  unfold stackBlocks stackG
  have hs : (bs.mergeSort fun a b => decide (κ b ≤ κ a)).map f =
      (bs.map f).mergeSort fun a b => decide (b.κ ≤ a.κ) :=
    List.map_mergeSort fun a _ b _ => by simp [hf]
  simp only
  rw [← hs]
  generalize bs.mergeSort (fun a b => decide (κ b ≤ κ a)) = l
  suffices h : ∀ (acc : List (α × Nat)) (c : Nat),
      ((l.map f).foldl (fun (acc : List (NBlock × Nat) × Nat) b => (acc.1 ++ [(b, acc.2)], acc.2 + 2 ^ b.κ))
        (acc.map (fun bo => (f bo.1, bo.2)), c)).1 =
      (l.foldl (fun (acc : List (α × Nat) × Nat) b => (acc.1 ++ [(b, acc.2)], acc.2 + 2 ^ κ b))
        (acc, c)).1.map (fun bo => (f bo.1, bo.2)) from h [] 0
  induction l with
  | nil => intro acc c; rfl
  | cons b l ih =>
    intro acc c
    simp only [List.foldl_cons, List.map_cons]
    rw [← ih]
    simp [hf]

/-- A static block of the push and pull sides: table, height, key, read (count column) or seed
(finalize column). -/
structure SBlk where
  /-- The table. -/
  tab : Nat
  /-- The height. -/
  κ : Nat
  /-- The key. -/
  key : Key
  /-- A read (else a seed). -/
  rd : Bool
  /-- The count (read) or finalize (seed) column. -/
  col : Nat

/-- A table's push/pull blocks: its reads, then its seeds. -/
def ppOfShape (t : TShape) (j : Nat) : List SBlk :=
  t.reads.map (fun r => ⟨j, t.τ, r.1, true, r.2⟩) ++ t.seeds.map (fun s => ⟨j, t.τ, s.1, false, s.2⟩)

/-- The push (and pull) side's static blocks. -/
def ppBlocks (S : List TShape) : List SBlk := S.zipIdx.flatMap fun (t, j) => ppOfShape t j

/-- A shape's read-count columns inside its width. -/
def countsS (t : TShape) : List Nat :=
  t.reads.filterMap fun r => if r.2 < t.cols.length then some r.2 else none

/-- The count side's static blocks: table, height, column. -/
def cBlocks (S : List TShape) : List (Nat × Nat × Nat) :=
  S.zipIdx.flatMap fun (t, j) => (countsS t).map fun c => (j, t.τ, c)

/-- The push side's count polynomial. -/
def cntPush (b : SBlk) : CPoly := if b.rd then [(FK.x, [b.col])] else CPoly.const 1

/-- The executable blocks of a static block. -/
def fPush (eqα : List FE) (β : FE) (b : SBlk) : NBlock := ⟨b.tab, b.κ, leafForm eqα β b.key (cntPush b)⟩
def fPull (eqα : List FE) (β : FE) (b : SBlk) : NBlock := ⟨b.tab, b.κ, leafForm eqα β b.key (CPoly.var b.col)⟩
def fCnt (c : Nat × Nat × Nat) : NBlock := ⟨c.1, c.2.1, Form.col c.2.2⟩

theorem counts_val (t : Tab) : t.counts.map (·.val) = countsS t.shape := by
  unfold Tab.counts countsS
  rw [List.map_filterMap]
  refine List.filterMap_congr fun r _ => ?_
  simp only [Tab.shape, List.length_map, Tab.w]
  split <;> simp_all

/-- **The three sides are maps of the static blocks.** -/
theorem sideBlocks_eq (st : List Tab) (eqα : List FE) (β : FE) :
    sideBlocks st eqα β = [(ppBlocks (st.map Tab.shape)).map (fPush eqα β),
      (ppBlocks (st.map Tab.shape)).map (fPull eqα β), (cBlocks (st.map Tab.shape)).map fCnt] := by
  simp only [sideBlocks, ppBlocks, cBlocks, List.zipIdx_map, List.flatMap_map, List.map_flatMap,
    List.cons.injEq, and_true]
  refine ⟨?_, ?_, ?_⟩ <;> refine List.flatMap_congr fun tj _ => ?_
  · simp [ppOfShape, Tab.shape, fPush, cntPush, Prod.map, Function.comp_def]
  · simp [ppOfShape, Tab.shape, fPull, Prod.map, Function.comp_def]
  · simp only [Prod.map, id_eq]
    rw [← counts_val, List.map_map, List.map_map]
    rfl

/-! ## Block weights -/

theorem eOfNat_mod2 (q : Nat) : eOfNat (q % 2) = if q % 2 = 1 then 1 else 0 := by
  rcases Nat.mod_two_eq_zero_or_one q with h | h <;> rw [h] <;> rfl

theorem eqEval_selector : ∀ (r : List FE) (q : Nat),
    eqEval (selectorPoint q r.length) r = Loop.eqW r q
  | [], q => rfl
  | a :: r, q => by
    have hs : selectorPoint q (r.length + 1) = eOfNat (q % 2) :: selectorPoint (q / 2) r.length := by
      simp only [selectorPoint, List.range_succ_eq_map, List.map_cons, List.map_map]
      refine congrArg₂ _ (by simp) (List.map_congr_left fun i _ => ?_)
      simp only [Function.comp_apply, Nat.shiftRight_eq_div_pow, pow_succ, Nat.div_div_eq_div_mul]
      simp only [Nat.mul_comm]
    rw [List.length_cons, hs, eqEval, List.zipWith_cons_cons, List.foldl_cons, foldl_mul_one,
      ← eqEval, eqEval_selector r (q / 2), Loop.eqW, eOfNat_mod2]
    split
    · simp only [one_mul]; rw [show (1 : FE) + 1 = 0 from CharTwo.add_self_eq_zero 1, zero_add]
    · simp only [one_mul, add_zero, sub_eq_add_neg, CharTwo.neg_eq]

/-- **A block weight is `eqW` of the point above the block at the block's index.** -/
theorem blockWeight_eqW (ζ : List FE) (κ off : Nat) :
    blockWeight ζ κ off = Loop.eqW (ζ.drop κ) (off >>> κ) := by
  rw [blockWeight, ← List.length_drop, eqEval_selector]

/-! ## The bus forms and totals of a table -/

/-- The push/pull side's stacked static blocks. -/
def ppS (S : List TShape) : List (SBlk × Nat) := stackG SBlk.κ (ppBlocks S)

/-- The count side's stacked static blocks. -/
def cS (S : List TShape) : List ((Nat × Nat × Nat) × Nat) := stackG (fun c => c.2.1) (cBlocks S)

theorem sidesR_eq (st : List Tab) (i : BusIn) :
    sidesR st i = [(ppS (st.map Tab.shape)).map (fun bo => (fPush (eqKernel i.alphas) i.beta bo.1,
        blockWeight i.point bo.1.κ bo.2)),
      (ppS (st.map Tab.shape)).map (fun bo => (fPull (eqKernel i.alphas) i.beta bo.1,
        blockWeight i.point bo.1.κ bo.2)),
      (cS (st.map Tab.shape)).map (fun bo => (fCnt bo.1, blockWeight i.point bo.1.2.1 bo.2))] := by
  rw [sidesR, sideBlocks_eq]
  simp only [List.map_cons, List.map_nil, ppS, cS]
  rw [stackBlocks_map SBlk.κ _ (fun _ => rfl), stackBlocks_map SBlk.κ _ (fun _ => rfl),
    stackBlocks_map (fun c : Nat × Nat × Nat => c.2.1) _ (fun _ => rfl)]
  simp [List.map_map, Function.comp_def, fPush, fPull, fCnt]

theorem filter_map_tab {α : Type} (l : List α) (g : α → NBlock × FE) (t : α → Nat)
    (hg : ∀ a, (g a).1.tab = t a) (j : Nat) (h : NBlock × FE → FE) :
    ((l.map g).filter fun bw => bw.1.tab == j).map h = (l.filter fun a => t a == j).map (h ∘ g) := by
  induction l with
  | nil => rfl
  | cons a l ih =>
    simp only [List.map_cons, List.filter_cons, hg]
    split <;> simp [ih]

/-- **Table `j`'s bus forms at its evaluations**: sums over the stacked static blocks of table `j`. -/
theorem forms_value (st : List Tab) (i : BusIn) {j : Nat} (hj : j < st.length) (col : Nat → FE) :
    ((busFinalR st i).forms.getD j []).map (·.value col) =
      [sumE (((ppS (st.map Tab.shape)).filter (·.1.tab == j)).map fun bo =>
          blockWeight i.point bo.1.κ bo.2 * (fPush (eqKernel i.alphas) i.beta bo.1).form.value col),
        sumE (((ppS (st.map Tab.shape)).filter (·.1.tab == j)).map fun bo =>
          blockWeight i.point bo.1.κ bo.2 * (fPull (eqKernel i.alphas) i.beta bo.1).form.value col),
        sumE (((cS (st.map Tab.shape)).filter (·.1.1 == j)).map fun bo =>
          blockWeight i.point bo.1.2.1 bo.2 * col bo.1.2.2)] := by
  have hl : j < ((List.range st.length).map fun j => ((sidesR st i).map (bucketR st.length)).map
      fun a => (⟨a.getD j []⟩ : Form)).length := by rw [List.length_map, List.length_range]; exact hj
  rw [busFinalR_forms_def, List.getD_eq_getElem _ _ hl, List.getElem_map, List.getElem_range,
    sidesR_eq]
  simp only [List.map_cons, List.map_nil]
  rw [bucketR_getD _ _ hj, bucketR_getD _ _ hj, bucketR_getD _ _ hj, value_bucketN, value_bucketN,
    value_bucketN, filter_map_tab _ _ (fun bo : SBlk × Nat => bo.1.tab) (fun _ => rfl),
    filter_map_tab _ _ (fun bo : SBlk × Nat => bo.1.tab) (fun _ => rfl),
    filter_map_tab _ _ (fun bo : (Nat × Nat × Nat) × Nat => bo.1.1) (fun _ => rfl)]
  simp only [Function.comp_def, fCnt, value_col]

/-- **The totals**: `v_k + 1 + Σ_b w_b`, the push and pull sides with the same weights. -/
theorem totals_eq (st : List Tab) (i : BusIn) :
    (busFinalR st i).totals =
      [i.values.getD 0 0 + 1 + sumE ((ppS (st.map Tab.shape)).map fun bo => blockWeight i.point bo.1.κ bo.2),
       i.values.getD 1 0 + 1 + sumE ((ppS (st.map Tab.shape)).map fun bo => blockWeight i.point bo.1.κ bo.2),
       i.values.getD 2 0 + 1 + sumE ((cS (st.map Tab.shape)).map fun bo => blockWeight i.point bo.1.2.1 bo.2)] := by
  rw [busFinalR_totals_def, sidesR_eq]
  simp [List.range_succ, Function.comp_def]

/-! ## `F`'s table terms -/

/-- Rows of the table sumcheck. -/
abbrev TRow := TableSpec × List Form × FE

/-- `F`'s term of a table from its evaluations (`tableTerms`' summand plus forms). -/
def termF (cp fp pt : List FE) (t : TableSpec) (forms : List Form) (cur : Nat) (ev : List FE) : FE :=
  dot ((cp.drop cur).take t.nConstraints) (t.constraints (pt.take t.logHeight) ev) +
    dot fp (forms.map (·.value (ev.getD · 0)))

/-- The evaluations `F` reads from byte `o` on, table by table. -/
def evsAt (v : Nat → FE) (pt : List FE) : List TRow → Nat → List (List FE × List FE)
  | [], _ => []
  | (t, _, _) :: rest, o => (pt.take t.logHeight, Q1.scalarsAt v o t.width) :: evsAt v pt rest (o + 24 * t.width)

/-- The terms. -/
def termsAt (v : Nat → FE) (cp fp pt : List FE) : List TRow → Nat → Nat → List FE
  | [], _, _ => []
  | (t, forms, _) :: rest, cur, o => termF cp fp pt t forms cur (Q1.scalarsAt v o t.width) ::
      termsAt v cp fp pt rest (cur + t.nConstraints) (o + 24 * t.width)

theorem tableTerms_run (cp fp pt : List FE) (sig : ByteArray) : ∀ (rows : List TRow) (cur : Nat) (f0 : FE)
    (s : RS), tableTerms cp fp pt rows cur f0 sig s =
      ((QB.finalOf (rows.map (·.2.2)) (termsAt (feAt sig) cp fp pt rows cur (s.ent + s.msg + 40)) f0,
        evsAt (feAt sig) pt rows (s.ent + s.msg + 40)),
       { s with msg := s.msg + 24 * (rows.map (·.1.width)).sum })
  | [], _, _, s => by simp [tableTerms, QB.finalOf, evsAt, termsAt]; rfl
  | (t, forms, w) :: rest, cur, f0, s => by
    unfold tableTerms
    simp only [Q1.bind_run, Q1.readEs_run, Q1.pure_run]
    rw [tableTerms_run cp fp pt sig rest]
    have e1 : s.ent + (s.msg + 24 * t.width) + 40 = s.ent + s.msg + 40 + 24 * t.width := by (clear * - s t; omega)
    simp only [e1, QB.finalOf, termsAt, evsAt, List.map_cons, List.zip_cons_cons, List.foldl_cons,
      List.sum_cons, termF]
    refine Prod.ext (Prod.ext rfl rfl) ?_
    simp only [RS.mk.injEq, true_and, and_true]; ring

/-! ## `tabPh` from a position -/

/-- **`F`'s table phase from position `pos s`** (the tables `m.tables pub` being executable tables). -/
theorem tabPh_run (p : Params) (m : M3) (pub : Pub) (bus : BusOut) (point : List FE) (st : List Tab)
    (hm : m.tables pub = st.map nativeTable) (sig : ByteArray) (s : RS) :
    tabPh p m pub bus point sig s =
      let ξ := feAt sig (pos s + 40)
      let nC := (st.map (·.cons.length)).sum
      let xp := powers ξ (nC + 3)
      let sc := sumcheck (dot (xp.drop nC) bus.totals) 4 (List.replicate p.tableRounds none) sig
        ⟨pos s + 72, 0, s.ok⟩
      let pt := sc.1.1.reverse
      let rows := List.zip (st.map nativeTable) (List.zip bus.forms (tableWeights (st.map (·.τ)) point pt))
      let B := pos s + 72 + 144 * p.tableRounds
      (evsAt (feAt sig) pt rows (B + 40),
        ⟨B, 24 * (rows.map (·.1.width)).sum,
          (QB.finalOf (rows.map (·.2.2)) (termsAt (feAt sig) (xp.take nC) (xp.drop nC) pt rows 0 (B + 40)) 0
            == sc.1.2) && s.ok⟩) := by
  have hR := QB.sumcheck_run 4 (by decide) sig (List.replicate p.tableRounds none)
  unfold tabPh tableSumcheck
  simp only [Q1.bind_run, Q1.sampleE_run, hm]
  rw [show s.ent + 40 + s.msg = pos s + 40 by simp [pos]; (clear * -; first | decide | (simp only [Nat.add_comm, Nat.add_left_comm, Nat.add_assoc]; done) | ring1 | omega),
    show ({ s with ent := s.ent + 72 + s.msg, msg := 0 } : RS) = ⟨pos s + 72, 0, s.ok⟩ by
      simp [pos]; (clear * -; first | decide | (simp only [Nat.add_comm, Nat.add_left_comm, Nat.add_assoc]; done) | ring1 | omega)]
  have e1 : (st.map nativeTable).map (·.nConstraints) = st.map (·.cons.length) := by
    simp [nativeTable, Function.comp_def]
  have e2 : (st.map nativeTable).map (·.logHeight) = st.map (·.τ) := by
    simp [nativeTable, Function.comp_def]
  simp only [e1, e2]
  rw [hR _ ⟨pos s + 72, 0, s.ok⟩ rfl]
  simp only [tableTerms_run, require_run, Q1.pure_run, List.length_replicate, QB.entB,
    Nat.add_zero, Nat.zero_add, show 72 + 24 * (4 - 1) = 144 from rfl]

/-! ## Powers of `ξ` -/

theorem powers_length (b : FE) (n : Nat) : (powers b n).length = n := by
  have key : ∀ (acc : FE) (n : Nat), (powersFrom acc b n).length = n := by
    intro acc n
    induction n generalizing acc with
    | zero => rfl
    | succ n ih => simp [powersFrom, ih]
  exact key 1 n

theorem take_drop_powers (ξ : FE) (N cur n : Nat) (h : cur + n ≤ N) :
    ((powers ξ N).drop cur).take n = (List.range n).map fun i => ξ ^ (cur + i) := by
  apply List.ext_getElem
  · simp [powers_length]; (clear * - n N cur h; omega)
  · intro i h1 h2
    simp only [List.getElem_take, List.getElem_drop, List.getElem_map, List.getElem_range]
    have := Loop.Build.powers_getD ξ N (cur + i) (by simp at h2; (clear * - h h2; omega))
    rw [List.getD_eq_getElem _ _ (by rw [powers_length]; simp at h2; (clear * - h h2; omega))] at this
    exact this

theorem dot_cons (a b : FE) (l r : List FE) : dot (a :: l) (b :: r) = a * b + dot l r := by
  rw [dot, List.zipWith_cons_cons, List.foldl_cons, foldl_add_from, zero_add]; rfl

theorem dot_pows (ξ : FE) : ∀ (vs : List FE) (cur : Nat),
    dot ((List.range vs.length).map fun i => ξ ^ (cur + i)) vs = ξ ^ cur * polyEval vs ξ
  | [], _ => by simp [dot, polyEval]
  | v :: vs, cur => by
    rw [List.length_cons, List.range_succ_eq_map, List.map_cons, List.map_map, dot_cons]
    have := dot_pows ξ vs (cur + 1)
    rw [show ((fun i => ξ ^ (cur + i)) ∘ Nat.succ) = fun i => ξ ^ (cur + 1 + i) from
      funext fun i => by simp only [Function.comp_apply]; rw [show cur + i.succ = cur + 1 + i by (clear * -; first | decide | (simp only [Nat.add_comm, Nat.add_left_comm, Nat.add_assoc]; done) | ring1 | omega)],
      this]
    simp only [polyEval, List.foldr_cons, Nat.add_zero]
    rw [show List.foldr (fun c acc => acc * ξ + c) 0 vs = polyEval vs ξ from rfl]
    ring

theorem drop_powers3 (ξ : FE) (nC : Nat) :
    (powers ξ (nC + 3)).drop nC = [ξ ^ nC, ξ ^ (nC + 1), ξ ^ (nC + 2)] := by
  have := take_drop_powers ξ (nC + 3) nC 3 le_rfl
  rw [List.take_of_length_le (by simp [powers_length])] at this
  rw [this]; rfl

theorem dot3 (a b c x y z : FE) : dot [a, b, c] [x, y, z] = a * x + b * y + c * z := by
  rw [dot_cons, dot_cons, dot_cons, show dot [] [] = 0 from rfl, add_zero, add_assoc]

/-! ## The merged push/pull value of a static block -/

theorem evalE_cons (v : Nat → FE) (m : FK × List Nat) (P : CPoly) :
    CPoly.evalE v (m :: P) = monV v m + CPoly.evalE v P := by
  rw [evalE_eq, evalE_eq, List.map_cons, sumE_cons]

theorem evalE_nil (v : Nat → FE) : CPoly.evalE v [] = 0 := rfl

theorem dval_eq (eqα : List FE) (β fp0 fp1 : FE) (b : SBlk) (col : Nat → FE) :
    fp0 * (fPush eqα β b).form.value col + fp1 * (fPull eqα β b).form.value col =
      (fp0 + fp1) * (β + eqα.getD 0 0 * FE.ofK b.key.sep) +
        (fp0 + fp1) * eqα.getD 1 0 * CPoly.evalE col b.key.addr +
        (fp0 + fp1) * limbsV eqα col b.key.val +
        (if b.rd then eqα.getD 2 0 * (fp0 * FE.ofK FK.x + fp1) * col b.col
         else eqα.getD 2 0 * fp0 + eqα.getD 2 0 * fp1 * col b.col) := by
  simp only [fPush, fPull, value_leafForm, cntPush]
  have hv : CPoly.evalE col (CPoly.var b.col) = col b.col := by
    simp [CPoly.var, evalE_cons, evalE_nil, monV, Loop.Build.ofK_one]
  rw [hv]
  split
  · have : CPoly.evalE col [(FK.x, [b.col])] = FE.ofK FK.x * col b.col := by
      simp [evalE_cons, evalE_nil, monV]
    rw [this]; ring
  · have : CPoly.evalE col (CPoly.const 1) = 1 := by simp [CPoly.const, evalE_cons, evalE_nil, monV]; rfl
    rw [this]; ring

/-! ## Geometric polynomials over the bit columns -/

/-- Bits `z ∈ [a, e)` of the columns `1 + z` with coefficients `x^{z−a+d}` (a `BITS` output). -/
def geoPoly (a e d : Nat) : CPoly :=
  (List.range 64).map fun z => (if a ≤ z ∧ z < e then Bits.wt (z - a + d) else 0, [1 + z])

/-- The suffix sums `S k = Σ_{k ≤ z < 64} x^{z−k} · col (1 + z)`. -/
def Sv (col : Nat → FE) (k : Nat) : FE := ∑ z ∈ Finset.Ico k 64, gen ^ (z - k) * col (1 + z)

theorem Sv_succ (col : Nat → FE) {k : Nat} (hk : k < 64) : Sv col k = col (1 + k) + gen * Sv col (k + 1) := by
  rw [Sv, Finset.sum_eq_sum_Ico_succ_bot hk, Nat.sub_self, pow_zero, one_mul, Sv, Finset.mul_sum]
  refine congrArg (col (1 + k) + ·) (Finset.sum_congr rfl fun z hz => ?_)
  have := (Finset.mem_Ico.mp hz).1
  rw [← mul_assoc, ← pow_succ', show z - k = z - (k + 1) + 1 by (clear * - this; omega)]

theorem Sv_64 (col : Nat → FE) : Sv col 64 = 0 := by simp [Sv]

theorem sumE_eq_sum (l : List FE) : sumE l = l.sum := by
  induction l with
  | nil => rfl
  | cons x l ih => rw [sumE_cons, ih, List.sum_cons]

theorem sum_map_range (f : Nat → FE) : ∀ n, ((List.range n).map f).sum = ∑ i ∈ Finset.range n, f i
  | 0 => rfl
  | n + 1 => by rw [List.range_succ, List.map_append, List.sum_append, sum_map_range f n,
      Finset.sum_range_succ]; simp

theorem ofK_wt {k : Nat} (hk : k < 64) : FE.ofK (Bits.wt k) = gen ^ k := by
  rw [Bits.wt_eq_pow hk, gen]; exact map_pow FE.ofKRingHom FK.x k

/-- **A geometric polynomial by suffix sums.** -/
theorem evalE_geo (col : Nat → FE) {a e d : Nat} (hae : a ≤ e) (he : e ≤ 64) (hd : e - a + d ≤ 64) :
    CPoly.evalE col (geoPoly a e d) = gen ^ d * (Sv col a + gen ^ (e - a) * Sv col e) := by
  rw [evalE_eq, sumE_eq_sum, geoPoly, List.map_map, sum_map_range]
  have h1 : ∑ z ∈ Finset.range 64, (monV col ∘ fun z =>
      ((if a ≤ z ∧ z < e then Bits.wt (z - a + d) else 0 : FK), [1 + z])) z =
      ∑ z ∈ Finset.Ico a e, gen ^ d * (gen ^ (z - a) * col (1 + z)) := by
    rw [← Finset.sum_filter_add_sum_filter_not (Finset.range 64) (fun z => a ≤ z ∧ z < e)]
    have hf : (Finset.range 64).filter (fun z => a ≤ z ∧ z < e) = Finset.Ico a e := by
      ext z; simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_Ico]; (clear * - he; omega)
    rw [hf, Finset.sum_eq_zero (s := Finset.filter _ _) (fun z hz => by
      rw [Finset.mem_filter] at hz
      simp [monV, hz.2, Loop.Build.ofK_zero]), add_zero]
    refine Finset.sum_congr rfl fun z hz => ?_
    have hz' := Finset.mem_Ico.mp hz
    simp only [Function.comp_apply, monV, if_pos hz', List.map_cons, List.map_nil, List.foldl_cons,
      List.foldl_nil, one_mul]
    rw [ofK_wt (by (clear * - hae hd hz'; omega)), ← mul_assoc, ← pow_add, show z - a + d = d + (z - a) by (clear * -; first | decide | (simp only [Nat.add_comm, Nat.add_left_comm, Nat.add_assoc]; done) | ring1 | omega)]
  rw [h1, ← Finset.mul_sum]
  congr 1
  have hsplit := Finset.sum_Ico_consecutive (fun z => gen ^ (z - a) * col (1 + z)) hae he
  have h2 : ∑ z ∈ Finset.Ico e 64, gen ^ (z - a) * col (1 + z) = gen ^ (e - a) * Sv col e := by
    rw [Sv, Finset.mul_sum]
    refine Finset.sum_congr rfl fun z hz => ?_
    have := (Finset.mem_Ico.mp hz).1
    rw [← mul_assoc, ← pow_add, show z - a = e - a + (z - e) by (clear * - hae this; omega)]
  rw [Sv, ← hsplit, h2, add_assoc, CharTwo.add_self_eq_zero, add_zero]

end Lvm.Har
end
-- ===== end of `LvmQAsmArith2TabF` =====

-- ===== merged from `LvmQAsmArith2TabG` (GOLF module merge: `LvmQAsmArith2TabG.lean` is now a stub importing `LvmQAsmArith2Tab`) =====
section
-- New for lvm (HAR-BT): `CPoly` evaluation gadgets over a table's evaluation cells (QL's builder):
-- monomials scaled or not, geometric (`BITS` output) suffixes by suffix sums, a fresh evaluation
-- with a one-row `a·b + c` start (the `BITS` bit constraints), Horner over a table's constraints.
-- Searched QA2's `LvmQBusGkr` (`hornerG`, `prodG`: lists of cells, reused in spirit), QA1's `LvmQKeccakTB`
-- (template builder): no `CPoly` evaluator to adapt.

/-!
# Evaluating `CPoly`s on cells

`ev i` is the cell of column `i` (value `col i`), `sc k` the suffix-sum cell `S k` (`Sv col k`, `k ≤ 64`).

* `prodAccG t vs acc`: `acc + t·Π_{v∈vs} col v`; `monAccS A acc m`: `acc + A·m(col)`;
  `monAccU acc m`: `acc + m(col)` (one row for `c·x_i`, `x_i x_j`, a constant).
* `geoMatch P`: `P = pre ++ geoPoly a e d` (checked); `geoAccU`/`geoAccS`: the suffix by `S`
  (`x^d (S a + x^{e−a} S e)`: two rows, three when scaled).
* `polyAccU`, `polyAccS`: `acc + P(col)`, `acc + A·P(col)`; `polyFresh`: `P(col)` (a first
  `x_i x_j` and `x_k` in one row: `β_z² + β_z`); `hornerC`: `Σ_c ξ^c C_c(col)`.
-/

set_option autoImplicit false

namespace Lvm.Har

open Lvm Lvm.M3 Lvm.Loop Lvm.Loop.Build

/-! ## Monomials -/

/-- `acc + t·Π_{v∈vs} ev v`. -/
def prodAccG (z : Cell) (ev : Nat → Cell) : Cell → List Nat → Cell → BM Cell
  | t, [], acc => lin .E 1 0 acc t
  | t, [v], acc => mulAdd .E t (ev v) acc
  | t, v :: w :: vs, acc => do
    let t' ← mulAdd .E t (ev v) z
    prodAccG z ev t' (w :: vs) acc

/-- `k·A` (no row for `k = 1`). -/
def scaleC (z : Cell) (k : FK) (A : Cell) : BM Cell := if k = 1 then pure A else lin .E k 0 z A

/-- `acc + A·m(ev)`. -/
def monAccS (z : Cell) (ev : Nat → Cell) (A acc : Cell) (m : FK × List Nat) : BM Cell :=
  scaleC z m.1 A >>= fun t => prodAccG z ev t m.2 acc

/-- `acc + m(ev)`. -/
def monAccU (z : Cell) (ev : Nat → Cell) (acc : Cell) : FK × List Nat → BM Cell
  | (c, []) => lin .E 0 c acc acc
  | (c, [i]) => lin .E c 0 acc (ev i)
  | (c, [i, j]) => if c = 1 then mulAdd .E (ev i) (ev j) acc else do
      let t ← lin .E c 0 z (ev i)
      mulAdd .E t (ev j) acc
  | (c, i :: vs) => do
      let t ← lin .E c 0 z (ev i)
      prodAccG z ev t vs acc

/-- The monomials one by one, unscaled. -/
def monsAccU (z : Cell) (ev : Nat → Cell) : Cell → CPoly → BM Cell
  | acc, [] => pure acc
  | acc, m :: ms => do
    let acc' ← monAccU z ev acc m
    monsAccU z ev acc' ms

/-- The monomials one by one, scaled by `A`. -/
def monsAccS (z : Cell) (ev : Nat → Cell) (A : Cell) : Cell → CPoly → BM Cell
  | acc, [] => pure acc
  | acc, m :: ms => do
    let acc' ← monAccS z ev A acc m
    monsAccS z ev A acc' ms

section
variable {c : Ctx} {M : Mem} {z : Cell} {ev : Nat → Cell} {col : Nat → FE}

theorem prodAccG_sound (hz : z.val M = 0) (hev : ∀ i, (ev i).val M = col i) :
    ∀ (vs : List Nat) (t acc : Cell),
      SoundG c M (prodAccG z ev t vs acc) fun r =>
        r.val M = acc.val M + t.val M * (vs.map col).foldl (· * ·) 1
  | [], t, acc => fun p hH _ => by
    simp only [prodAccG] at hH ⊢
    rw [lin_spec hH, ofK_one, ofK_zero]; simp
  | [v], t, acc => fun p hH _ => by
    simp only [prodAccG] at hH ⊢
    rw [mulAdd_spec hH, hev]; simp; ring
  | v :: w :: vs, t, acc => by
    show SoundG c M (mulAdd .E t (ev v) z >>= fun t' => prodAccG z ev t' (w :: vs) acc) _
    refine soundG_bind (soundG_mono (soundG_aspec (QB.aspec_mulAdd .E t (ev v) z)) fun _ h => h.1)
      fun t' ht' => soundG_mono (prodAccG_sound hz hev (w :: vs) t' acc) fun r hr => ?_
    rw [hr, ht', hev, hz, add_zero]
    simp only [List.map_cons, List.foldl_cons]
    rw [foldl_mul_one _ (1 * col w), foldl_mul_one _ (1 * col v * col w)]
    ring

theorem monAccS_sound (hz : z.val M = 0) (hev : ∀ i, (ev i).val M = col i) (A acc : Cell)
    (m : FK × List Nat) :
    SoundG c M (monAccS z ev A acc m) fun r => r.val M = acc.val M + A.val M * monV col m := by
  unfold monAccS
  have h1 : SoundG c M (scaleC z m.1 A) (fun t => t.val M = FE.ofK m.1 * A.val M) := by
    unfold scaleC
    split
    · rename_i h
      exact soundG_pure (by rw [h, ofK_one, one_mul])
    · exact soundG_mono (soundG_aspec (QB.aspec_lin .E m.1 0 z A)) fun x h => by
        rw [h.1, hz, ofK_zero]; ring
  refine soundG_bind h1 fun t ht => soundG_mono (prodAccG_sound hz hev m.2 t acc) fun r hr => ?_
  rw [hr, ht, monV]; ring

theorem monAccU_sound (hz : z.val M = 0) (hev : ∀ i, (ev i).val M = col i) (acc : Cell) :
    ∀ m : FK × List Nat, SoundG c M (monAccU z ev acc m) fun r => r.val M = acc.val M + monV col m
  | (k, []) => fun p hH _ => by
    simp only [monAccU] at hH ⊢; rw [lin_spec hH, monV]; simp [ofK_zero]
  | (k, [i]) => fun p hH _ => by
    simp only [monAccU] at hH ⊢; rw [lin_spec hH, monV, hev]; simp [ofK_zero]
  | (k, [i, j]) => by
    rw [show monAccU z ev acc (k, [i, j]) = (if k = 1 then mulAdd .E (ev i) (ev j) acc else
      (lin .E k 0 z (ev i) >>= fun t => mulAdd .E t (ev j) acc)) from rfl]
    split
    · rename_i h; subst h
      exact fun p hH _ => by
        simp only at hH ⊢; rw [mulAdd_spec hH, hev, hev, monV]; simp [ofK_one]; ring
    · refine soundG_bind (soundG_mono (soundG_aspec (QB.aspec_lin .E k 0 z (ev i))) fun _ h => h.1)
        fun t ht => soundG_mono (soundG_aspec (QB.aspec_mulAdd .E t (ev j) acc)) fun r hr => ?_
      rw [hr.1, ht, hz, hev, hev, monV, ofK_zero]; simp; ring
  | (k, i :: w :: x :: vs) => by
    show SoundG c M (lin .E k 0 z (ev i) >>= fun t => prodAccG z ev t (w :: x :: vs) acc) _
    refine soundG_bind (soundG_mono (soundG_aspec (QB.aspec_lin .E k 0 z (ev i))) fun _ h => h.1)
      fun t ht => soundG_mono (prodAccG_sound hz hev _ t acc) fun r hr => ?_
    rw [hr, ht, hz, hev, monV, ofK_zero]
    simp only [List.map_cons, List.foldl_cons]
    rw [foldl_mul_one _ (1 * col w * col x), foldl_mul_one _ (1 * col i * col w * col x)]
    ring

theorem monsAccU_sound (hz : z.val M = 0) (hev : ∀ i, (ev i).val M = col i) :
    ∀ (P : CPoly) (acc : Cell),
      SoundG c M (monsAccU z ev acc P) fun r => r.val M = acc.val M + CPoly.evalE col P
  | [], acc => soundG_pure (by rw [evalE_nil, add_zero])
  | m :: ms, acc => soundG_bind (monAccU_sound hz hev acc m) fun a ha =>
      soundG_mono (monsAccU_sound hz hev ms a) fun r hr => by rw [hr, ha, evalE_cons]; ring

theorem monsAccS_sound (hz : z.val M = 0) (hev : ∀ i, (ev i).val M = col i) (A : Cell) :
    ∀ (P : CPoly) (acc : Cell),
      SoundG c M (monsAccS z ev A acc P) fun r => r.val M = acc.val M + A.val M * CPoly.evalE col P
  | [], acc => soundG_pure (by rw [evalE_nil, mul_zero, add_zero])
  | m :: ms, acc => soundG_bind (monAccS_sound hz hev A acc m) fun a ha =>
      soundG_mono (monsAccS_sound hz hev A ms a) fun r hr => by rw [hr, ha, evalE_cons]; ring

end

/-! ## Geometric suffixes -/

/-- **Recognise a geometric suffix** (checked: the result is `P = pre ++ geoPoly a e d`). -/
def geoMatch (P : CPoly) : Option (CPoly × Nat × Nat × Nat) :=
  let g := P.drop (P.length - 64)
  let a := g.findIdx (·.1 != 0)
  let e := 64 - g.reverse.findIdx (·.1 != 0)
  let d := (g.getD a (0, [])).1.val.toNat.log2
  if 64 ≤ P.length ∧ a ≤ e ∧ e ≤ 64 ∧ e - a + d ≤ 64 ∧ g = geoPoly a e d then
    some (P.take (P.length - 64), a, e, d) else none

theorem geoMatch_spec {P pre : CPoly} {a e d : Nat} (h : geoMatch P = some (pre, a, e, d)) :
    P = pre ++ geoPoly a e d ∧ a ≤ e ∧ e ≤ 64 ∧ e - a + d ≤ 64 := by
  unfold geoMatch at h
  dsimp only at h
  split at h
  · rename_i hc
    simp only [Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl, rfl, rfl⟩ := h
    exact ⟨(List.take_append_drop _ P).symm.trans (congrArg _ hc.2.2.2.2), hc.2.1, hc.2.2.1,
      hc.2.2.2.1⟩
  · simp at h

/-- `S a + x^{e−a} S e`. -/
def geoT (sc : Nat → Cell) (a e : Nat) : BM Cell :=
  if e < 64 then lin .E (Bits.wt (e - a)) 0 (sc a) (sc e) else pure (sc a)

/-- `acc + x^d (S a + x^{e−a} S e)`. -/
def geoAccU (sc : Nat → Cell) (acc : Cell) (a e d : Nat) : BM Cell :=
  geoT sc a e >>= fun t => lin .E (Bits.wt d) 0 acc t

/-- `acc + A · x^d (S a + x^{e−a} S e)`. -/
def geoAccS (z : Cell) (sc : Nat → Cell) (A acc : Cell) (a e d : Nat) : BM Cell := do
  let t ← geoT sc a e
  let u ← scaleC z (Bits.wt d) A
  mulAdd .E u t acc

section
variable {c : Ctx} {M : Mem} {z : Cell} {sc : Nat → Cell} {col : Nat → FE}

theorem geoT_sound (hsc : ∀ k ≤ 64, (sc k).val M = Sv col k) {a e : Nat} (hae : a ≤ e) (he : e ≤ 64) :
    SoundG c M (geoT sc a e) fun t => t.val M = Sv col a + gen ^ (e - a) * Sv col e := by
  unfold geoT
  split
  · rename_i h
    exact soundG_mono (soundG_aspec (QB.aspec_lin .E _ 0 _ _)) fun t ht => by
      rw [ht.1, hsc a (by (clear * - hae he h; omega)), hsc e (by omega), ofK_wt (by (clear * - hae he h; omega)), ofK_zero, add_zero]
  · rename_i h
    exact soundG_pure (by rw [show e = 64 by (clear * - he h; omega), Sv_64, mul_zero, add_zero, hsc a (by (clear * - hae he h; omega))])

theorem geo_zero {a : Nat} (k : FE) : k * (Sv col a + gen ^ (a - a) * Sv col a) = 0 := by
  rw [Nat.sub_self, pow_zero, one_mul, CharTwo.add_self_eq_zero, mul_zero]

theorem geoAccU_sound (hsc : ∀ k ≤ 64, (sc k).val M = Sv col k) (acc : Cell) {a e d : Nat}
    (hae : a ≤ e) (he : e ≤ 64) (hd : e - a + d ≤ 64) :
    SoundG c M (geoAccU sc acc a e d) fun r =>
      r.val M = acc.val M + gen ^ d * (Sv col a + gen ^ (e - a) * Sv col e) :=
  soundG_bind (geoT_sound hsc hae he) fun t ht =>
    soundG_mono (soundG_aspec (QB.aspec_lin .E _ 0 acc t)) fun r hr => by
      rw [hr.1, ht, ofK_zero, add_zero]
      rcases Nat.lt_or_ge a e with h | h
      · rw [ofK_wt (by (clear * - he hd h; omega))]
      · obtain rfl : a = e := by (clear * - hae h; omega)
        rw [geo_zero, geo_zero]

theorem scaleC_sound (hz : z.val M = 0) (k : FK) (A : Cell) :
    SoundG c M (scaleC z k A) fun t => t.val M = FE.ofK k * A.val M := by
  unfold scaleC
  split
  · rename_i h
    exact soundG_pure (by rw [h, ofK_one, one_mul])
  · exact soundG_mono (soundG_aspec (QB.aspec_lin .E k 0 z A)) fun x h => by
      rw [h.1, hz, ofK_zero]; ring

theorem geoAccS_sound (hz : z.val M = 0) (hsc : ∀ k ≤ 64, (sc k).val M = Sv col k) (A acc : Cell)
    {a e d : Nat} (hae : a ≤ e) (he : e ≤ 64) (hd : e - a + d ≤ 64) :
    SoundG c M (geoAccS z sc A acc a e d) fun r =>
      r.val M = acc.val M + A.val M * (gen ^ d * (Sv col a + gen ^ (e - a) * Sv col e)) :=
  soundG_bind (geoT_sound hsc hae he) fun t ht =>
    soundG_bind (scaleC_sound hz _ A) fun u hu =>
      soundG_mono (soundG_aspec (QB.aspec_mulAdd .E u t acc)) fun r hr => by
        rw [hr.1, hu, ht]
        rcases Nat.lt_or_ge a e with h | h
        · rw [ofK_wt (by (clear * - he hd h; omega))]; ring
        · obtain rfl : a = e := by (clear * - hae h; omega)
          rw [Nat.sub_self, pow_zero, one_mul, CharTwo.add_self_eq_zero]; ring

end

/-! ## Polynomials -/

/-- `acc + P(ev)`. -/
def polyAccU (z : Cell) (ev sc : Nat → Cell) (acc : Cell) (P : CPoly) : BM Cell :=
  match geoMatch P with
  | some (pre, a, e, d) => monsAccU z ev acc pre >>= fun r => geoAccU sc r a e d
  | none => monsAccU z ev acc P

/-- `acc + A·P(ev)`. -/
def polyAccS (z : Cell) (ev sc : Nat → Cell) (A acc : Cell) (P : CPoly) : BM Cell :=
  match geoMatch P with
  | some (pre, a, e, d) => monsAccS z ev A acc pre >>= fun r => geoAccS z sc A r a e d
  | none => monsAccS z ev A acc P

/-- `P(ev)`, a first `c x_i` or `x_i x_j + x_k` at no or one row. -/
def monsFresh (z : Cell) (ev : Nat → Cell) : CPoly → BM Cell
  | [] => pure z
  | (k, [i]) :: ms => if k = 1 then monsAccU z ev (ev i) ms else monsAccU z ev z ((k, [i]) :: ms)
  | (k, [i, j]) :: (k', [l]) :: ms =>
    if k = 1 ∧ k' = 1 then mulAdd .E (ev i) (ev j) (ev l) >>= fun r => monsAccU z ev r ms
    else monsAccU z ev z ((k, [i, j]) :: (k', [l]) :: ms)
  | ms => monsAccU z ev z ms

/-- `P(ev)`. -/
def polyFresh (z : Cell) (ev sc : Nat → Cell) (P : CPoly) : BM Cell :=
  match geoMatch P with
  | some (pre, a, e, d) => monsFresh z ev pre >>= fun r => geoAccU sc r a e d
  | none => monsFresh z ev P

/-- **Horner over constraints**: `Σ_c ξ^c C_c(ev)`. -/
def hornerC (z : Cell) (ev sc : Nat → Cell) (xi : Cell) : List CPoly → BM Cell
  | [] => pure z
  | [C] => polyFresh z ev sc C
  | C :: D :: Cs => do
    let h ← hornerC z ev sc xi (D :: Cs)
    let c ← polyFresh z ev sc C
    mulAdd .E xi h c

/-- The suffix sums `S (64 − n) … S 63` (`S 64` is the zero cell). -/
def sufG (z : Cell) (ev : Nat → Cell) : Nat → BM (List Cell)
  | 0 => pure []
  | n + 1 => do
    let l ← sufG z ev n
    let s ← lin .E FK.x 0 (ev (1 + (63 - n))) (l.headD z)
    pure (s :: l)

section
variable {c : Ctx} {M : Mem} {z : Cell} {ev sc : Nat → Cell} {col : Nat → FE}

theorem polyAccU_sound (hz : z.val M = 0) (hev : ∀ i, (ev i).val M = col i) (acc : Cell) (P : CPoly)
    (hsc : (geoMatch P).isSome = true → ∀ k ≤ 64, (sc k).val M = Sv col k) :
    SoundG c M (polyAccU z ev sc acc P) fun r => r.val M = acc.val M + CPoly.evalE col P := by
  unfold polyAccU
  split
  · rename_i pre a e d hm
    obtain ⟨hP, hae, he, hd⟩ := geoMatch_spec hm
    exact soundG_bind (monsAccU_sound hz hev pre acc) fun r hr =>
      soundG_mono (geoAccU_sound (hsc (by rw [hm]; rfl)) r hae he hd) fun x hx => by
        rw [hx, hr, hP, evalE_append, evalE_geo col hae he hd]; ring
  · exact monsAccU_sound hz hev P acc

theorem polyAccS_sound (hz : z.val M = 0) (hev : ∀ i, (ev i).val M = col i) (A acc : Cell) (P : CPoly)
    (hsc : (geoMatch P).isSome = true → ∀ k ≤ 64, (sc k).val M = Sv col k) :
    SoundG c M (polyAccS z ev sc A acc P) fun r =>
      r.val M = acc.val M + A.val M * CPoly.evalE col P := by
  unfold polyAccS
  split
  · rename_i pre a e d hm
    obtain ⟨hP, hae, he, hd⟩ := geoMatch_spec hm
    exact soundG_bind (monsAccS_sound hz hev A pre acc) fun r hr =>
      soundG_mono (geoAccS_sound hz (hsc (by rw [hm]; rfl)) A r hae he hd) fun x hx => by
        rw [hx, hr, hP, evalE_append, evalE_geo col hae he hd]; ring
  · exact monsAccS_sound hz hev A P acc

theorem monsFresh_sound (hz : z.val M = 0) (hev : ∀ i, (ev i).val M = col i) (P : CPoly) :
    SoundG c M (monsFresh z ev P) fun r => r.val M = CPoly.evalE col P := by
  have hz0 : ∀ Q : CPoly, SoundG c M (monsAccU z ev z Q) fun r => r.val M = CPoly.evalE col Q :=
    fun Q => soundG_mono (monsAccU_sound hz hev Q z) fun r hr => by rw [hr, hz, zero_add]
  unfold monsFresh
  split
  · exact soundG_pure (by rw [hz, evalE_nil])
  · rename_i k i ms
    split
    · rename_i hk
      exact soundG_mono (monsAccU_sound hz hev ms (ev i)) fun r hr => by
        rw [hr, hev, evalE_cons, monV, hk]; simp [ofK_one]
    · exact hz0 _
  · rename_i k i j k' l ms
    split
    · rename_i hk
      exact soundG_bind (soundG_aspec (QB.aspec_mulAdd .E (ev i) (ev j) (ev l))) fun r hr =>
        soundG_mono (monsAccU_sound hz hev ms r) fun x hx => by
          rw [hx, hr.1, hev, hev, hev, evalE_cons, evalE_cons, monV, monV, hk.1, hk.2]
          simp [ofK_one]; ring
    · exact hz0 _
  · exact hz0 _

theorem polyFresh_sound (hz : z.val M = 0) (hev : ∀ i, (ev i).val M = col i) (P : CPoly)
    (hsc : (geoMatch P).isSome = true → ∀ k ≤ 64, (sc k).val M = Sv col k) :
    SoundG c M (polyFresh z ev sc P) fun r => r.val M = CPoly.evalE col P := by
  unfold polyFresh
  split
  · rename_i pre a e d hm
    obtain ⟨hP, hae, he, hd⟩ := geoMatch_spec hm
    exact soundG_bind (monsFresh_sound hz hev pre) fun r hr =>
      soundG_mono (geoAccU_sound (hsc (by rw [hm]; rfl)) r hae he hd) fun x hx => by
        rw [hx, hr, hP, evalE_append, evalE_geo col hae he hd]
  · exact monsFresh_sound hz hev P

theorem hornerC_sound (hz : z.val M = 0) (hev : ∀ i, (ev i).val M = col i) (xi : Cell) :
    ∀ Cs : List CPoly, (∀ C ∈ Cs, (geoMatch C).isSome = true → ∀ k ≤ 64, (sc k).val M = Sv col k) →
      SoundG c M (hornerC z ev sc xi Cs) fun r =>
        r.val M = polyEval (Cs.map (CPoly.evalE col)) (xi.val M)
  | [], _ => soundG_pure (by rw [hz]; rfl)
  | [C], hsc => soundG_mono (polyFresh_sound hz hev C (hsc C List.mem_cons_self)) fun r hr => by
      rw [hr]; simp [polyEval]
  | C :: D :: Cs, hsc => soundG_bind (hornerC_sound hz hev xi (D :: Cs)
      fun C' h => hsc C' (List.mem_cons_of_mem _ h)) fun h hh =>
      soundG_bind (polyFresh_sound hz hev C (hsc C List.mem_cons_self)) fun c' hc =>
        soundG_mono (soundG_aspec (QB.aspec_mulAdd .E xi h c')) fun r hr => by
          rw [hr.1, hh, hc]
          simp only [List.map_cons, polyEval, List.foldr_cons]
          ring

theorem sufG_sound (hev : ∀ i, (ev i).val M = col i) (hz : z.val M = 0) :
    ∀ n ≤ 64, SoundG c M (sufG z ev n) fun l =>
      l.length = n ∧ ∀ i < n, (l.getD i z).val M = Sv col (64 - n + i)
  | 0, _ => soundG_pure ⟨rfl, fun i hi => absurd hi (by (clear * - hi; omega))⟩
  | n + 1, hn => soundG_bind (sufG_sound hev hz n (by (clear * - hn; omega))) fun l hl =>
      soundG_bind (soundG_aspec (QB.aspec_lin .E FK.x 0 (ev (1 + (63 - n))) (l.headD z)))
        fun s hs => soundG_pure ⟨by simp [hl.1], fun i hi => by
          rcases i with _ | i
          · simp only [List.getD_cons_zero]
            have hh : (l.headD z).val M = Sv col (64 - n) := by
              rcases l with _ | ⟨x, l'⟩
              · have : n = 0 := by simpa using hl.1.symm
                subst this; simp [hz, Sv_64]
              · have := hl.2 0 (by simp at hl; (clear * - hn hl; omega))
                simpa using this
            rw [show 64 - (n + 1) + 0 = 63 - n by (clear * - hn hl; omega), Sv_succ col (by (clear * - hn hl; omega) : 63 - n < 64),
              show 63 - n + 1 = 64 - n by (clear * - hn hl; omega), hs.1, hev, ofK_zero, add_zero, hh]
            rfl
          · simp only [List.getD_cons_succ]
            rw [hl.2 i (by (clear * - hl hi; omega)), show 64 - (n + 1) + (i + 1) = 64 - n + i by (clear * - hn hl; omega)]⟩

end

end Lvm.Har
end
-- ===== end of `LvmQAsmArith2TabG` =====

-- ===== merged from `LvmQAsmArith2TabW` (GOLF module merge: `LvmQAsmArith2TabW.lean` is now a stub importing `LvmQAsmArith2Tab`) =====
section
-- New for lvm (HAR-BT): phase 3's block weights (`eqW` of the GKR point above each stacked block:
-- per level a low `eq` table, QA2's `eqTab`, times a high part computed once per prefix), the
-- leaf-form constants, one static block's merged push/pull value (`dG`), the per-table folds and term.
-- Searched QA2 (`LvmQWhirBatch.eqTab`, reused), WP-9b (`LvmM3FidBus`: the same weights over `E`).

/-!
# Weights, constants, blocks

* `eqWG fs x`: `eqW` of the factor cells (`(1 + ζ_i, ζ_i)`) at `x`, one row per coordinate.
* `bwG … κ q`: `eqW (ζ.drop κ) q` = (table entry of the low `s` bits) · (high part, from the list
  `hi` or computed); correct for any static choice of tables and high parts (`bwG_sound`).
* `tkG`: `F = fp₀ + fp₁`, `F·β`, `F·eqα_i`, `γ_r = eqα₂(fp₀ x + fp₁)`, `eqα₂ fp₀`, `eqα₂ fp₁`, and per
  separator `F(β + eqα₀ sep)` (read) / `+ eqα₂ fp₀` (seed).
* `dG b`: `fp₀ · push_b + fp₁ · pull_b` at the evaluations (`dG_sound`, = `dval_eq`'s right side).
* `ppFoldG`, `cFoldG`, `termG`: a table's term `ξ^{cur}·H + Σ_pp w·D + fp₂ Σ_c w·x_c`.
-/

set_option autoImplicit false

namespace Lvm.Har

open Lvm Lvm.M3 Lvm.Loop Lvm.Loop.Build

/-! ## `eqW` from factor cells -/

/-- `eqW` of the factor cells `(1 + ζ_i, ζ_i)` at `x`. -/
def eqWG (z o : Cell) : List (Cell × Cell) → Nat → BM Cell
  | [], _ => pure o
  | f :: fs, x => do
    let r ← eqWG z o fs (x / 2)
    mulAdd .E (if x % 2 = 1 then f.2 else f.1) r z

/-- The factor cells of a point: `(1 + ζ_i, ζ_i)`. -/
def facG : List Cell → BM (List (Cell × Cell))
  | [] => pure []
  | c :: cs => do
    let f0 ← lin .E 0 1 c c
    let fs ← facG cs
    pure ((f0, c) :: fs)

/-- Factor cells are `(1 + ζ_i, ζ_i)`. -/
def FacOk (M : Mem) (fs : List (Cell × Cell)) : Prop := ∀ f ∈ fs, f.1.val M = 1 + f.2.val M

section
variable {c : Ctx} {M : Mem} {z o : Cell}

theorem one_add_eq_sub (a : FE) : 1 + a = 1 - a := by rw [sub_eq_add_neg, CharTwo.neg_eq]

theorem eqWG_sound (hz : z.val M = 0) (ho : o.val M = 1) :
    ∀ (fs : List (Cell × Cell)) (x : Nat), FacOk M fs →
      SoundG c M (eqWG z o fs x) fun r => r.val M = Loop.eqW (fs.map (·.2.val M)) x
  | [], _, _ => soundG_pure (by rw [ho]; rfl)
  | f :: fs, x, hf => soundG_bind (eqWG_sound hz ho fs (x / 2) fun g hg => hf g (List.mem_cons_of_mem _ hg))
      fun r hr => soundG_mono (soundG_aspec (QB.aspec_mulAdd .E _ r z)) fun y hy => by
        rw [hy.1, hr, hz, add_zero, List.map_cons, Loop.eqW]
        split
        · rfl
        · rw [hf f List.mem_cons_self, one_add_eq_sub]

theorem facG_sound : ∀ cs : List Cell, SoundG c M (facG cs) fun fs => fs.map (·.2) = cs ∧ FacOk M fs
  | [] => soundG_pure ⟨rfl, fun _ h => absurd h List.not_mem_nil⟩
  | x :: cs => soundG_bind (soundG_aspec (QB.aspec_lin .E 0 1 x x)) fun f0 hf0 =>
      soundG_bind (facG_sound cs) fun fs hfs => soundG_pure ⟨by simp [hfs.1], fun f hf => by
        rcases List.mem_cons.mp hf with rfl | hf
        · rw [hf0.1, ofK_zero, ofK_one, zero_mul, add_zero, add_comm]
        · exact hfs.2 f hf⟩

end

/-! ## Block weights -/

/-- The low `eq` table of level `κ` with `s` coordinates (QA2's `eqTab`). -/
def lvlG (z o : Cell) (zeta : List Cell) (κ s : Nat) : BM Nat :=
  eqTab (fun i => zeta.getD (κ + i) z) z o false s

/-- The tables of a static list of levels: `(κ, s, base)`. -/
def lvlsG (z o : Cell) (zeta : List Cell) : List (Nat × Nat) → BM (List (Nat × Nat × Nat))
  | [] => pure []
  | (κ, s) :: ls => do
    let b ← lvlG z o zeta κ s
    let r ← lvlsG z o zeta ls
    pure ((κ, s, b) :: r)

/-- High parts `eqW (ζ.drop l) h` of a static list of prefixes. -/
def hisG (z o : Cell) (facs : List (Cell × Cell)) : List (Nat × Nat) → BM (List ((Nat × Nat) × Cell))
  | [] => pure []
  | (l, h) :: ks => do
    let x ← eqWG z o (facs.drop l) h
    let r ← hisG z o facs ks
    pure (((l, h), x) :: r)

/-- A high part: from the list, else computed. -/
def hiG (z o : Cell) (facs : List (Cell × Cell)) (hi : List ((Nat × Nat) × Cell)) (l h : Nat) : BM Cell :=
  match hi.find? (fun e => decide (e.1 = (l, h))) with
  | some e => pure e.2
  | none => eqWG z o (facs.drop l) h

/-- **The weight `eqW (ζ.drop κ) q`** of a block at level `κ`, prefix `q` (`D` coordinates). -/
def bwG (z o : Cell) (facs : List (Cell × Cell)) (lt : List (Nat × Nat × Nat))
    (hi : List ((Nat × Nat) × Cell)) (D κ q : Nat) : BM Cell :=
  match lt.find? (fun e => decide (e.1 = κ ∧ e.2.1 ≠ 0 ∧ κ + e.2.1 ≤ D)) with
  | some e => do
    let h ← hiG z o facs hi (κ + e.2.1) (q / 2 ^ e.2.1)
    mulAdd .E h (ec (e.2.2 + q % 2 ^ e.2.1)) z
  | none => hiG z o facs hi κ q

/-- The low point of level `κ` with `s` coordinates. -/
def lowPt (ζ : List FE) (κ s : Nat) : List FE := (List.range s).map fun i => ζ.getD (κ + i) 0

/-- What the level tables hold. -/
def LvlOk (M : Mem) (ζ : List FE) (lt : List (Nat × Nat × Nat)) : Prop :=
  ∀ e ∈ lt, ∀ x < 2 ^ e.2.1, M.e (e.2.2 + x) = Loop.eqW (lowPt ζ e.1 e.2.1) x

/-- What the high parts hold. -/
def HiOk (M : Mem) (ζ : List FE) (hi : List ((Nat × Nat) × Cell)) : Prop :=
  ∀ e ∈ hi, e.2.val M = Loop.eqW (ζ.drop e.1.1) e.1.2

theorem lowPt_eq {ζ : List FE} {κ s : Nat} (h : κ + s ≤ ζ.length) : lowPt ζ κ s = (ζ.drop κ).take s := by
  apply List.ext_getElem
  · simp [lowPt]; (clear * - s ζ κ h; omega)
  · intro i h1 h2
    simp only [lowPt, List.getElem_map, List.getElem_range, List.getElem_take, List.getElem_drop]
    rw [List.getD_eq_getElem _ _ (by simp [lowPt] at h1; (clear * - h h1; omega))]

theorem eqW_split {ζ : List FE} {κ s : Nat} (h : κ + s ≤ ζ.length) (q : Nat) :
    Loop.eqW (ζ.drop κ) q = Loop.eqW (lowPt ζ κ s) (q % 2 ^ s) * Loop.eqW (ζ.drop (κ + s)) (q / 2 ^ s) := by
  have hl : (lowPt ζ κ s).length = s := by simp [lowPt]
  rw [show ζ.drop κ = lowPt ζ κ s ++ ζ.drop (κ + s) by
    rw [lowPt_eq h, ← List.drop_drop, List.take_append_drop], Build.eqW_append, hl]

section
variable {c : Ctx} {M : Mem} {z o : Cell}

theorem facs_drop {facs : List (Cell × Cell)} {ζ : List FE} (hf : (facs.map (·.2)).map (·.val M) = ζ)
    (l : Nat) : (facs.drop l).map (·.2.val M) = ζ.drop l := by
  rw [← hf, List.map_map, List.map_drop]; rfl

theorem facOk_drop {facs : List (Cell × Cell)} (hf : FacOk M facs) (l : Nat) : FacOk M (facs.drop l) :=
  fun f h => hf f (List.mem_of_mem_drop h)

theorem hisG_sound (hz : z.val M = 0) (ho : o.val M = 1) {facs : List (Cell × Cell)} {ζ : List FE}
    (hf1 : (facs.map (·.2)).map (·.val M) = ζ) (hf2 : FacOk M facs) :
    ∀ ks : List (Nat × Nat), SoundG c M (hisG z o facs ks) fun hi => HiOk M ζ hi
  | [] => soundG_pure fun _ h => absurd h List.not_mem_nil
  | (l, h) :: ks => soundG_bind (eqWG_sound hz ho _ h (facOk_drop hf2 l)) fun x hx =>
      soundG_bind (hisG_sound hz ho hf1 hf2 ks) fun r hr => soundG_pure fun e he => by
        rcases List.mem_cons.mp he with rfl | he
        · rw [hx, facs_drop hf1]
        · exact hr e he

theorem hiG_sound (hz : z.val M = 0) (ho : o.val M = 1) {facs : List (Cell × Cell)} {ζ : List FE}
    (hf1 : (facs.map (·.2)).map (·.val M) = ζ) (hf2 : FacOk M facs) {hi : List ((Nat × Nat) × Cell)}
    (hhi : HiOk M ζ hi) (l h : Nat) :
    SoundG c M (hiG z o facs hi l h) fun r => r.val M = Loop.eqW (ζ.drop l) h := by
  unfold hiG
  split
  · rename_i e he
    have h1 := List.find?_some he
    have h2 := List.mem_of_find?_eq_some he
    simp only [decide_eq_true_eq] at h1
    refine soundG_pure ?_
    rw [hhi e h2, h1]
  · exact soundG_mono (eqWG_sound hz ho _ h (facOk_drop hf2 l)) fun r hr => by rw [hr, facs_drop hf1]

/-- **A block weight.** -/
theorem bwG_sound (hz : z.val M = 0) (ho : o.val M = 1) {facs : List (Cell × Cell)} {ζ : List FE}
    (hf1 : (facs.map (·.2)).map (·.val M) = ζ) (hf2 : FacOk M facs) {hi : List ((Nat × Nat) × Cell)}
    (hhi : HiOk M ζ hi) {lt : List (Nat × Nat × Nat)} (hlt : LvlOk M ζ lt) {D : Nat} (hD : D = ζ.length)
    (κ q : Nat) :
    SoundG c M (bwG z o facs lt hi D κ q) fun r => r.val M = Loop.eqW (ζ.drop κ) q := by
  unfold bwG
  split
  · rename_i e he
    have h1 := List.find?_some he
    have h2 := List.mem_of_find?_eq_some he
    simp only [decide_eq_true_eq] at h1
    refine soundG_bind (hiG_sound hz ho hf1 hf2 hhi _ _) fun h hh =>
      soundG_mono (soundG_aspec (QB.aspec_mulAdd .E h _ z)) fun r hr => ?_
    rw [hr.1, hh, hz, add_zero, Cell.val_E, hlt e h2 _ (Nat.mod_lt _ (by positivity)), h1.1,
      eqW_split (s := e.2.1) (by rw [← hD]; exact h1.2.2) q, mul_comm]
  · exact hiG_sound hz ho hf1 hf2 hhi κ q

end

section
variable {c : Ctx} {M : Mem} {z o : Cell}

theorem lvlsG_sound (hz : z.val M = 0) (hzE : z.ty = .E) (hoE : o.ty = .E) (ho : o.val M = 1)
    {zeta : List Cell} (hzeE : ∀ x ∈ zeta, x.ty = .E) {ζ : List FE} (hζ : vs M zeta = ζ) :
    ∀ ls : List (Nat × Nat), SoundG c M (lvlsG z o zeta ls) fun lt => LvlOk M ζ lt
  | [] => soundG_pure fun _ h => absurd h List.not_mem_nil
  | (κ, s) :: ls => by
    refine soundG_bind (Φ := fun b => ∀ x < 2 ^ s, M.e (b + x) = Loop.eqW (lowPt ζ κ s) x)
      (fun p hH _ => ?_) fun b hb => soundG_bind (lvlsG_sound hz hzE hoE ho hzeE hζ ls) fun r hr =>
        soundG_pure fun e he => by
          rcases List.mem_cons.mp he with rfl | he
          · exact hb
          · exact hr e he
    have hal : ∀ i, (zeta.getD (κ + i) z).ty = .E := fun i => by
      rw [List.getD_eq_getElem?_getD]
      cases h : zeta[κ + i]? with
      | none => exact hzE
      | some x => exact hzeE x (List.mem_of_getElem? h)
    have hone : M.e o.n = 1 := by rw [← ho]; rcases o with ⟨τ, n⟩; simp at hoE; subst hoE; rfl
    have hlen : (lowPt ζ κ s).length = s := by simp [lowPt]
    have hv : ∀ i < (lowPt ζ κ s).length, (zeta.getD (κ + i) z).val M = (lowPt ζ κ s).getD i 0 := by
      intro i hi
      rw [List.getD_eq_getElem (lowPt ζ κ s) 0 hi]
      rw [hlen] at hi
      simp only [lowPt, List.getElem_map, List.getElem_range, ← hζ, vs]
      rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, List.getElem?_map]
      cases zeta[κ + i]? <;> simp [hz]
    have := eqTab_eq (fun i => zeta.getD (κ + i) z) z o false (lowPt ζ κ s) (p := p)
      (by rw [hlen]; exact hH) hz hal hone hv
    intro x hx
    have h2 := this x (by rw [hlen]; exact hx)
    simp only [Bool.false_eq_true, ite_false] at h2
    rw [show lvlG z o zeta κ s p = eqTab (fun i => zeta.getD (κ + i) z) z o false s p from rfl]
    rw [hlen] at h2
    rw [h2, eqKernelA_getD _ _ (by rw [hlen]; exact hx)]

end

/-! ## Leaf constants -/

/-- The leaf-form constants of the table phase. -/
structure TK where
  /-- `fp₀ + fp₁`. -/
  F : Cell
  /-- `F·β`. -/
  fb : Cell
  /-- `F·eqα_i`. -/
  fa : List Cell
  /-- `eqα₂ (fp₀ x + fp₁)`. -/
  gr : Cell
  /-- `eqα₂ fp₀`. -/
  gs0 : Cell
  /-- `eqα₂ fp₁`. -/
  gs1 : Cell
  /-- Per separator: `F(β + eqα₀ sep)` and that `+ eqα₂ fp₀`. -/
  cs : List (FK × Cell × Cell)

/-- `F·eqα_i`, `i < n` (`eqα_i` at `E` cell `eb + i`). -/
def faG (z F : Cell) (eb : Nat) : Nat → BM (List Cell)
  | 0 => pure []
  | n + 1 => do
    let l ← faG z F eb n
    let x ← mulAdd .E F (ec (eb + n)) z
    pure (l ++ [x])

/-- The per-separator constants. -/
def csG (fb fa0 gs0 : Cell) : List FK → BM (List (FK × Cell × Cell))
  | [] => pure []
  | k :: ks => do
    let cr ← lin .E k 0 fb fa0
    let cs ← lin .E 1 0 cr gs0
    let r ← csG fb fa0 gs0 ks
    pure ((k, cr, cs) :: r)

/-- **The constants** (`eqα_i` at `E` cell `eb + i`, `i < n`). -/
def tkG (z fp0 fp1 be : Cell) (eb n : Nat) (seps : List FK) : BM TK := do
  let F ← lin .E 1 0 fp0 fp1
  let fb ← mulAdd .E F be z
  let fa ← faG z F eb n
  let t ← lin .E FK.x 0 fp1 fp0
  let gr ← mulAdd .E (ec (eb + 2)) t z
  let gs0 ← mulAdd .E (ec (eb + 2)) fp0 z
  let gs1 ← mulAdd .E (ec (eb + 2)) fp1 z
  let cs ← csG fb (fa.getD 0 z) gs0 seps
  pure ⟨F, fb, fa, gr, gs0, gs1, cs⟩

/-- What the constants hold. -/
def TKOk (M : Mem) (z : Cell) (K : TK) (fp0 fp1 β : FE) (eqα : List FE) : Prop :=
  (∀ i, (K.fa.getD i z).val M = (fp0 + fp1) * eqα.getD i 0) ∧ K.fb.val M = (fp0 + fp1) * β ∧
    K.gr.val M = eqα.getD 2 0 * (fp0 * FE.ofK FK.x + fp1) ∧ K.gs0.val M = eqα.getD 2 0 * fp0 ∧
    K.gs1.val M = eqα.getD 2 0 * fp1 ∧
    ∀ e ∈ K.cs, e.2.1.val M = (fp0 + fp1) * (β + eqα.getD 0 0 * FE.ofK e.1) ∧
      e.2.2.val M = e.2.1.val M + eqα.getD 2 0 * fp0

section
variable {c : Ctx} {M : Mem} {z : Cell}

theorem faG_sound (hz : z.val M = 0) (F : Cell) (eb : Nat) : ∀ n,
    SoundG c M (faG z F eb n) fun l => l.length = n ∧ ∀ i < n, (l.getD i z).val M = F.val M * M.e (eb + i)
  | 0 => soundG_pure ⟨rfl, fun i h => absurd h (by (clear * - h; omega))⟩
  | n + 1 => soundG_bind (faG_sound hz F eb n) fun l hl =>
      soundG_bind (soundG_aspec (QB.aspec_mulAdd .E F (ec (eb + n)) z)) fun x hx =>
        soundG_pure ⟨by simp [hl.1], fun i hi => by
          rcases Nat.lt_or_ge i n with h | h
          · rw [List.getD_append _ _ _ _ (by (clear * - hl h; omega))]; exact hl.2 i h
          · obtain rfl : i = n := by (clear * - hi h; omega)
            rw [List.getD_append_right _ _ _ _ (by (clear * - hl; omega)), hl.1, Nat.sub_self, List.getD_cons_zero,
              hx.1, hz, add_zero]; rfl⟩

theorem csG_sound (fb fa0 gs0 : Cell) : ∀ ks : List FK,
    SoundG c M (csG fb fa0 gs0 ks) fun cs => ∀ e ∈ cs,
      e.2.1.val M = fb.val M + FE.ofK e.1 * fa0.val M ∧ e.2.2.val M = e.2.1.val M + gs0.val M
  | [] => soundG_pure fun _ h => absurd h List.not_mem_nil
  | k :: ks => soundG_bind (soundG_aspec (QB.aspec_lin .E k 0 fb fa0)) fun cr hcr =>
      soundG_bind (soundG_aspec (QB.aspec_lin .E 1 0 cr gs0)) fun cs hcs =>
        soundG_bind (csG_sound fb fa0 gs0 ks) fun r hr => soundG_pure fun e he => by
          rcases List.mem_cons.mp he with rfl | he
          · refine ⟨?_, ?_⟩
            · rw [hcr.1, ofK_zero, add_zero]
            · rw [hcs.1, ofK_one, ofK_zero, one_mul, add_zero]
          · exact hr e he

theorem tkG_sound (hz : z.val M = 0) (fp0 fp1 be : Cell) (eb n : Nat) (seps : List FK)
    {eqα : List FE} (hlen : eqα.length = n) (hn : 2 < n) (hα : ∀ i < n, M.e (eb + i) = eqα.getD i 0) :
    SoundG c M (tkG z fp0 fp1 be eb n seps) fun K =>
      TKOk M z K (fp0.val M) (fp1.val M) (be.val M) eqα := by
  unfold tkG
  refine soundG_bind (soundG_aspec (QB.aspec_lin .E 1 0 fp0 fp1)) fun F hF => ?_
  refine soundG_bind (soundG_aspec (QB.aspec_mulAdd .E F be z)) fun fb hfb => ?_
  refine soundG_bind (faG_sound hz F eb n) fun fa hfa => ?_
  refine soundG_bind (soundG_aspec (QB.aspec_lin .E FK.x 0 fp1 fp0)) fun t ht => ?_
  refine soundG_bind (soundG_aspec (QB.aspec_mulAdd .E (ec (eb + 2)) t z)) fun gr hgr => ?_
  refine soundG_bind (soundG_aspec (QB.aspec_mulAdd .E (ec (eb + 2)) fp0 z)) fun gs0 hgs0 => ?_
  refine soundG_bind (soundG_aspec (QB.aspec_mulAdd .E (ec (eb + 2)) fp1 z)) fun gs1 hgs1 => ?_
  refine soundG_bind (csG_sound fb (fa.getD 0 z) gs0 seps) fun cs hcs => soundG_pure ?_
  have hFv : F.val M = fp0.val M + fp1.val M := by rw [hF.1, ofK_one, ofK_zero, one_mul, add_zero]
  have hfa' : ∀ i, (fa.getD i z).val M = (fp0.val M + fp1.val M) * eqα.getD i 0 := by
    intro i
    rcases Nat.lt_or_ge i n with h | h
    · rw [hfa.2 i h, hα i h, hFv]
    · rw [List.getD_eq_default _ _ (by rw [hfa.1]; exact h), hz,
        List.getD_eq_default _ _ (by rw [hlen]; exact h), mul_zero]
  have he2 : M.e (eb + 2) = eqα.getD 2 0 := hα 2 hn
  refine ⟨hfa', by rw [hfb.1, hFv, hz, add_zero], ?_, ?_, ?_, fun e he => ?_⟩
  · rw [hgr.1, Cell.val_E, he2, ht.1, hz, add_zero, ofK_zero, add_zero]; ring
  · rw [hgs0.1, Cell.val_E, he2, hz, add_zero]
  · rw [hgs1.1, Cell.val_E, he2, hz, add_zero]
  · obtain ⟨h1, h2⟩ := hcs e he
    refine ⟨?_, ?_⟩
    · rw [h1, hfb.1, hz, add_zero, hFv, hfa' 0]; ring
    · rw [h2, hgs0.1, Cell.val_E, he2, hz, add_zero]

end

/-! ## A static block's merged push/pull value -/

/-- The separator constant of a block (from the list, else computed). -/
def csepG (z : Cell) (K : TK) (sep : FK) (rd : Bool) : BM Cell :=
  match K.cs.find? (fun e => decide (e.1 = sep)) with
  | some e => pure (if rd then e.2.1 else e.2.2)
  | none => do
    let cr ← lin .E sep 0 K.fb (K.fa.getD 0 z)
    if rd then pure cr else lin .E 1 0 cr K.gs0

/-- `acc + Σ_l F·eqα_{3+l}·P_l`. -/
def limbsG (z : Cell) (ev sc : Nat → Cell) (K : TK) : List (CPoly × Nat) → Cell → BM Cell
  | [], acc => pure acc
  | x :: rest, acc => polyAccS z ev sc (K.fa.getD (3 + x.2) z) acc x.1 >>= limbsG z ev sc K rest

/-- **`fp₀ · push_b + fp₁ · pull_b`** at the evaluations. -/
def dG (z : Cell) (ev sc : Nat → Cell) (K : TK) (b : SBlk) : BM Cell := do
  let c0 ← csepG z K b.key.sep b.rd
  let c1 ← polyAccS z ev sc (K.fa.getD 1 z) c0 b.key.addr
  let c2 ← limbsG z ev sc K b.key.val.zipIdx c1
  mulAdd .E (if b.rd then K.gr else K.gs1) (ev b.col) c2

/-- The polynomials of a block's key. -/
def keyPolys (k : Key) : List CPoly := k.addr :: k.val

/-- Suffix-sum cells are right if a polynomial is geometric. -/
def ScOk (M : Mem) (sc : Nat → Cell) (col : Nat → FE) (P : CPoly) : Prop :=
  (geoMatch P).isSome = true → ∀ k ≤ 64, (sc k).val M = Sv col k

section
variable {c : Ctx} {M : Mem} {z : Cell} {ev sc : Nat → Cell} {col : Nat → FE}
  {K : TK} {fp0 fp1 β : FE} {eqα : List FE}

theorem csepG_sound (hz : z.val M = 0) (hK : TKOk M z K fp0 fp1 β eqα) (sep : FK) (rd : Bool) :
    SoundG c M (csepG z K sep rd) fun r => r.val M =
      (fp0 + fp1) * (β + eqα.getD 0 0 * FE.ofK sep) + (if rd then 0 else eqα.getD 2 0 * fp0) := by
  obtain ⟨hfa, hfb, -, hgs0, -, hcs⟩ := hK
  unfold csepG
  split
  · rename_i e he
    have h1 := List.find?_some he
    have h2 := hcs e (List.mem_of_find?_eq_some he)
    simp only [decide_eq_true_eq] at h1
    refine soundG_pure ?_
    rw [← h1]
    cases rd
    · simp only [Bool.false_eq_true, ite_false]; rw [h2.2, h2.1]
    · simp only [ite_true, add_zero]; exact h2.1
  · refine soundG_bind (soundG_aspec (QB.aspec_lin .E sep 0 K.fb (K.fa.getD 0 z))) fun cr hcr => ?_
    have hcv : cr.val M = (fp0 + fp1) * (β + eqα.getD 0 0 * FE.ofK sep) := by
      rw [hcr.1, hfb, hfa, ofK_zero, add_zero]; ring
    cases rd
    · exact soundG_mono (soundG_aspec (QB.aspec_lin .E 1 0 cr K.gs0)) fun r hr => by
        rw [hr.1, hcv, hgs0, ofK_one, ofK_zero, one_mul, add_zero]; rfl
    · exact soundG_pure (by rw [hcv]; simp)

theorem limbsG_sound (hz : z.val M = 0) (hev : ∀ i, (ev i).val M = col i) (hK : TKOk M z K fp0 fp1 β eqα) :
    ∀ (L : List (CPoly × Nat)) (acc : Cell), (∀ x ∈ L, ScOk M sc col x.1) →
      SoundG c M (limbsG z ev sc K L acc) fun r => r.val M =
        acc.val M + sumE (L.map fun x => (fp0 + fp1) * eqα.getD (3 + x.2) 0 * CPoly.evalE col x.1)
  | [], acc, _ => soundG_pure (by rw [List.map_nil, sumE_nil, add_zero])
  | x :: rest, acc, hsc => soundG_bind (polyAccS_sound hz hev _ acc x.1 (hsc x List.mem_cons_self))
      fun a ha => soundG_mono (limbsG_sound hz hev hK rest a fun y hy => hsc y (List.mem_cons_of_mem _ hy))
        fun r hr => by rw [hr, ha, hK.1, List.map_cons, sumE_cons]; ring

theorem dG_sound (hz : z.val M = 0) (hev : ∀ i, (ev i).val M = col i) (hK : TKOk M z K fp0 fp1 β eqα)
    (b : SBlk) (hsc : ∀ P ∈ keyPolys b.key, ScOk M sc col P) :
    SoundG c M (dG z ev sc K b) fun r => r.val M =
      fp0 * (fPush eqα β b).form.value col + fp1 * (fPull eqα β b).form.value col := by
  rw [dval_eq eqα β fp0 fp1 b col]
  unfold dG
  refine soundG_bind (csepG_sound hz hK b.key.sep b.rd) fun c0 hc0 => ?_
  refine soundG_bind (polyAccS_sound hz hev _ c0 b.key.addr (hsc _ List.mem_cons_self)) fun c1 hc1 => ?_
  refine soundG_bind (limbsG_sound hz hev hK b.key.val.zipIdx c1 fun x hx =>
    hsc _ (List.mem_cons_of_mem _ (by
      obtain ⟨h1, h2⟩ := List.mem_zipIdx' hx
      rw [h2]; exact List.getElem_mem _))) fun c2 hc2 => ?_
  refine soundG_mono (soundG_aspec (QB.aspec_mulAdd .E _ (ev b.col) c2)) fun r hr => ?_
  rw [hr.1, hc2, hc1, hc0, hK.1, hev]
  have hl : sumE (b.key.val.zipIdx.map fun x => (fp0 + fp1) * eqα.getD (3 + x.2) 0 * CPoly.evalE col x.1) =
      (fp0 + fp1) * limbsV eqα col b.key.val := by
    rw [limbsV, ← sumE_map_mul]
    exact congrArg sumE (List.map_congr_left fun x _ => by ring)
  rw [hl]
  cases hb : b.rd
  · simp only [Bool.false_eq_true, ite_false, hK.2.2.2.2.1]; ring
  · simp only [ite_true, hK.2.2.1]; ring

end

/-! ## A table's term -/

/-- `acc + Σ w · D_b` over a table's stacked push/pull blocks with their weight cells. -/
def ppFoldG (z : Cell) (ev sc : Nat → Cell) (K : TK) : List ((SBlk × Nat) × Cell) → Cell → BM Cell
  | [], acc => pure acc
  | x :: rest, acc => do
    let d ← dG z ev sc K x.1.1
    let a ← mulAdd .E x.2 d acc
    ppFoldG z ev sc K rest a

/-- `acc + Σ w · x_c` over a table's stacked count blocks. -/
def cFoldG (ev : Nat → Cell) : List (((Nat × Nat × Nat) × Nat) × Cell) → Cell → BM Cell
  | [], acc => pure acc
  | x :: rest, acc => do
    let a ← mulAdd .E x.2 (ev x.1.1.2.2) acc
    cFoldG ev rest a

/-- The key polynomials of a table's push/pull blocks and its constraints. -/
def tPolys (cons : List CPoly) (Lpp : List ((SBlk × Nat) × Cell)) : List CPoly :=
  cons ++ Lpp.flatMap fun x => keyPolys x.1.1.key

/-- Whether a table needs suffix-sum cells. -/
def needS (cons : List CPoly) (Lpp : List ((SBlk × Nat) × Cell)) : Bool :=
  (tPolys cons Lpp).any fun P => (geoMatch P).isSome

/-- The suffix-sum cells of a table, if it needs them. -/
def scG (z : Cell) (ev : List Cell) (b : Bool) : BM (List Cell) :=
  if b then sufG z (fun i => ev.getD i z) 64 else pure []

/-- **A table's term**: `X · H + Σ_pp w·D + fp₂ · Σ_c w·x_c` (`H` the constraints' Horner sum). -/
def termG (z xi X fp2 : Cell) (K : TK) (cons : List CPoly) (ev : List Cell)
    (Lpp : List ((SBlk × Nat) × Cell)) (Lc : List (((Nat × Nat × Nat) × Nat) × Cell)) : BM Cell := do
  let sc ← scG z ev (needS cons Lpp)
  let H ← hornerC z (fun i => ev.getD i z) (fun k => sc.getD k z) xi cons
  let sm ← mulAdd .E X H z
  let a ← ppFoldG z (fun i => ev.getD i z) (fun k => sc.getD k z) K Lpp sm
  let cc ← cFoldG (fun i => ev.getD i z) Lc z
  mulAdd .E fp2 cc a

section
variable {c : Ctx} {M : Mem} {z : Cell} {ev sc : Nat → Cell} {col : Nat → FE}
  {K : TK} {fp0 fp1 β : FE} {eqα : List FE}

theorem ppFoldG_sound (hz : z.val M = 0) (hev : ∀ i, (ev i).val M = col i) (hK : TKOk M z K fp0 fp1 β eqα) :
    ∀ (L : List ((SBlk × Nat) × Cell)) (acc : Cell), (∀ x ∈ L, ∀ P ∈ keyPolys x.1.1.key, ScOk M sc col P) →
      SoundG c M (ppFoldG z ev sc K L acc) fun r => r.val M = acc.val M + sumE (L.map fun x =>
        x.2.val M * (fp0 * (fPush eqα β x.1.1).form.value col + fp1 * (fPull eqα β x.1.1).form.value col))
  | [], acc, _ => soundG_pure (by rw [List.map_nil, sumE_nil, add_zero])
  | x :: rest, acc, hsc => soundG_bind (dG_sound hz hev hK x.1.1 (hsc x List.mem_cons_self)) fun d hd =>
      soundG_bind (soundG_aspec (QB.aspec_mulAdd .E x.2 d acc)) fun a ha =>
        soundG_mono (ppFoldG_sound hz hev hK rest a fun y hy => hsc y (List.mem_cons_of_mem _ hy))
          fun r hr => by rw [hr, ha.1, hd, List.map_cons, sumE_cons]; ring

theorem cFoldG_sound (hev : ∀ i, (ev i).val M = col i) :
    ∀ (L : List (((Nat × Nat × Nat) × Nat) × Cell)) (acc : Cell),
      SoundG c M (cFoldG ev L acc) fun r => r.val M = acc.val M + sumE (L.map fun x => x.2.val M * col x.1.1.2.2)
  | [], acc => soundG_pure (by rw [List.map_nil, sumE_nil, add_zero])
  | x :: rest, acc => soundG_bind (soundG_aspec (QB.aspec_mulAdd .E x.2 (ev x.1.1.2.2) acc)) fun a ha =>
      soundG_mono (cFoldG_sound hev rest a) fun r hr => by
        rw [hr, ha.1, hev, List.map_cons, sumE_cons]; ring

theorem termG_sound (hz : z.val M = 0) (hzE : z.ty = .E) (hK : TKOk M z K fp0 fp1 β eqα)
    (xi X fp2 : Cell) (cons : List CPoly) (ev : List Cell) (Lpp : List ((SBlk × Nat) × Cell))
    (Lc : List (((Nat × Nat × Nat) × Nat) × Cell)) :
    SoundG c M (termG z xi X fp2 K cons ev Lpp Lc) fun r =>
      r.val M = X.val M * polyEval (cons.map (CPoly.evalE ((vs M ev).getD · 0))) (xi.val M) +
        sumE (Lpp.map fun x => x.2.val M * (fp0 * (fPush eqα β x.1.1).form.value ((vs M ev).getD · 0) +
          fp1 * (fPull eqα β x.1.1).form.value ((vs M ev).getD · 0))) +
        fp2.val M * sumE (Lc.map fun x => x.2.val M * (vs M ev).getD x.1.1.2.2 0) := by
  have hev : ∀ i, (ev.getD i z).val M = (vs M ev).getD i 0 := by
    intro i
    simp only [vs, List.getD_eq_getElem?_getD, List.getElem?_map]
    cases ev[i]? <;> simp [hz]
  unfold termG
  refine soundG_bind (Φ := fun (sc : List Cell) => ∀ P ∈ tPolys cons Lpp, ScOk M (fun k => sc.getD k z)
      ((vs M ev).getD · 0) P) ?_ fun sc hsc => ?_
  · unfold scG
    split
    · exact soundG_mono (sufG_sound hev hz 64 le_rfl) fun l hl P _ _ k hk => by
        rcases Nat.lt_or_ge k 64 with h | h
        · have := hl.2 k h; simpa using this
        · obtain rfl : k = 64 := by (clear * - hk h; omega)
          show (l.getD 64 z).val M = _
          rw [List.getD_eq_default _ _ (by rw [hl.1]), hz, Sv_64]
    · rename_i hn
      refine soundG_pure fun P hP hg => absurd ?_ hn
      unfold needS; rw [List.any_eq_true]; exact ⟨P, hP, hg⟩
  · refine soundG_bind (hornerC_sound hz hev xi cons fun C hC => hsc C (List.mem_append_left _ hC))
      fun H hH => ?_
    refine soundG_bind (soundG_aspec (QB.aspec_mulAdd .E X H z)) fun sm hsm => ?_
    refine soundG_bind (ppFoldG_sound hz hev hK Lpp sm fun x hx P hP => hsc P
      (List.mem_append_right _ (List.mem_flatMap.mpr ⟨x, hx, hP⟩))) fun a ha => ?_
    refine soundG_bind (cFoldG_sound hev Lc z) fun cc hcc => ?_
    refine soundG_mono (soundG_aspec (QB.aspec_mulAdd .E fp2 cc a)) fun r hr => ?_
    rw [hr.1, hcc, ha, hsm.1, hH, hz]; ring

end

end Lvm.Har
end
-- ===== end of `LvmQAsmArith2TabW` =====

/-!
# Phase 3: the table sumcheck (`tabPh`)

`tabG S R P z o g bc` for the shapes `S` of the sumcheck tables, `R` rounds, start position `P`,
phase 2's cells `bc`: ξ (a load), `ξ^k` for the largest constraint count, `ξ^{cur_j}` per table and
`fp = ξ^{nC..nC+2}`, `eqα` (QA2's `eqTab`), the leaf constants, the block weights of both stackings,
the totals and the target, the rounds (`scRunP4`), the table weights (`tableW`), the evaluations
(loads), each table's term (`termG`), the final check (`tableFinal`). Output per table: its point cells
(`point.take τ`) and its evaluation cells.

**`tabG_replays`**: with `m.tables pub` the executable tables of `st` and `bus = busFinalR st ⟨…⟩` on
phase 2's values, wherever `tabG (st.map Tab.shape) …` holds and asserts (gate on), `F`'s table phase
keeps `ok`, ends at `tabEnd`, and its evaluations are the output cells' values. **`tabClaims`**: the
committed columns' claims as `CClaim`s, `= tableClaimsR st evals` (`tabClaims_val`).
-/

set_option autoImplicit false

namespace Lvm.Har

open Lvm Lvm.M3 Lvm.Loop Lvm.Loop.Build

/-! ## Helper gadgets -/

/-- `ξ^0 … ξ^n`. -/
def powsG (z o xi : Cell) : Nat → BM (List Cell)
  | 0 => pure [o]
  | n + 1 => do
    let l ← powsG z o xi n
    let x ← mulAdd .E (l.getD n o) xi z
    pure (l ++ [x])

/-- `X, X·ξ^{n₀}, X·ξ^{n₀+n₁}, …` (`ξ^n` from the powers `pw`). -/
def curG (z o : Cell) (pw : List Cell) : List Nat → Cell → BM (List Cell)
  | [], X => pure [X]
  | n :: ns, X => do
    let X' ← mulAdd .E X (pw.getD n o) z
    let r ← curG z o pw ns X'
    pure (X :: r)

/-- `Σ w`. -/
def sumG (z : Cell) : List Cell → BM Cell
  | [] => pure z
  | w :: ws => do
    let r ← sumG z ws
    lin .E 1 0 r w

/-- The weights of blocks `(κ, off)`. -/
def bwsG (z o : Cell) (facs : List (Cell × Cell)) (lt : List (Nat × Nat × Nat))
    (hi : List ((Nat × Nat) × Cell)) (D : Nat) : List (Nat × Nat) → BM (List Cell)
  | [] => pure []
  | b :: bs => do
    let w ← bwG z o facs lt hi D b.1 (b.2 >>> b.1)
    let r ← bwsG z o facs lt hi D bs
    pure (w :: r)

/-- Each table's evaluations, `3` lanes per scalar from lane `a`. -/
def evLoads (a : Nat) : List Nat → BM (List (List Cell))
  | [] => pure []
  | w :: ws => do
    let e ← ldEs a 3 w
    let r ← evLoads (a + 3 * w) ws
    pure (e :: r)

/-- The prefix sums. -/
def pre (l : List Nat) (j : Nat) : Nat := (l.take j).sum

section
variable {c : Ctx} {M : Mem} {z o : Cell}

theorem powsG_sound (hz : z.val M = 0) (ho : o.val M = 1) (xi : Cell) : ∀ n,
    SoundG c M (powsG z o xi n) fun l => l.length = n + 1 ∧ ∀ i ≤ n, (l.getD i o).val M = xi.val M ^ i
  | 0 => soundG_pure ⟨rfl, fun i hi => by rw [show i = 0 by (clear * - hi; omega)]; simp [ho]⟩
  | n + 1 => soundG_bind (powsG_sound hz ho xi n) fun l hl =>
      soundG_bind (soundG_aspec (QB.aspec_mulAdd .E (l.getD n o) xi z)) fun x hx =>
        soundG_pure ⟨by simp [hl.1], fun i hi => by
          rcases Nat.lt_or_ge i (n + 1) with h | h
          · rw [List.getD_append _ _ _ _ (by (clear * - hl h; omega))]; exact hl.2 i (by (clear * - h; omega))
          · obtain rfl : i = n + 1 := by (clear * - hi h; omega)
            rw [List.getD_append_right _ _ _ _ (by (clear * - hl; omega)), hl.1, Nat.sub_self, List.getD_cons_zero,
              hx.1, hl.2 n le_rfl, hz, add_zero, pow_succ]⟩

theorem curG_sound (hz : z.val M = 0) {pw : List Cell} {ξ : FE} :
    ∀ (ns : List Nat) (X : Cell), (∀ n ∈ ns, (pw.getD n o).val M = ξ ^ n) →
      SoundG c M (curG z o pw ns X) fun l =>
      l.length = ns.length + 1 ∧ ∀ j ≤ ns.length, (l.getD j o).val M = X.val M * ξ ^ pre ns j
  | [], X, _ => soundG_pure ⟨rfl, fun j hj => by
      rw [show j = 0 by simpa using hj]; simp [pre]⟩
  | n :: ns, X, hpw => soundG_bind (soundG_aspec (QB.aspec_mulAdd .E X (pw.getD n o) z)) fun X' hX =>
      soundG_bind (curG_sound hz ns X' fun k hk => hpw k (List.mem_cons_of_mem _ hk)) fun r hr =>
        soundG_pure ⟨by simp [hr.1], fun j hj => by
        rcases j with _ | j
        · simp [pre]
        · simp only [List.getD_cons_succ]
          rw [hr.2 j (by simpa using hj), hX.1, hpw n List.mem_cons_self, hz, add_zero]
          simp only [pre, List.take_succ_cons, List.sum_cons, pow_add]
          ring⟩

theorem sumG_sound (hz : z.val M = 0) : ∀ ws : List Cell,
    SoundG c M (sumG z ws) fun r => r.val M = sumE (vs M ws)
  | [] => soundG_pure (by rw [hz]; rfl)
  | w :: ws => soundG_bind (sumG_sound hz ws) fun r hr =>
      soundG_mono (soundG_aspec (QB.aspec_lin .E 1 0 r w)) fun x hx => by
        rw [hx.1, hr, ofK_one, ofK_zero, one_mul, add_zero]
        simp only [vs, List.map_cons, sumE_cons]; ring

theorem bwsG_sound (hz : z.val M = 0) (ho : o.val M = 1) {facs : List (Cell × Cell)} {ζ : List FE}
    (hf1 : (facs.map (·.2)).map (·.val M) = ζ) (hf2 : FacOk M facs) {hi : List ((Nat × Nat) × Cell)}
    (hhi : HiOk M ζ hi) {lt : List (Nat × Nat × Nat)} (hlt : LvlOk M ζ lt) {D : Nat} (hD : D = ζ.length) :
    ∀ bs : List (Nat × Nat), SoundG c M (bwsG z o facs lt hi D bs) fun ws =>
      vs M ws = bs.map fun b => blockWeight ζ b.1 b.2
  | [] => soundG_pure rfl
  | b :: bs => soundG_bind (bwG_sound hz ho hf1 hf2 hhi hlt hD b.1 (b.2 >>> b.1)) fun w hw =>
      soundG_bind (bwsG_sound hz ho hf1 hf2 hhi hlt hD bs) fun r hr => soundG_pure (by
        rw [vs, List.map_cons, List.map_cons, ← vs, hr, hw, blockWeight_eqW])

theorem evLoads_sound {sig : ByteArray} {T : Nat} (hS : Q1.Streamed M sig T) :
    ∀ (ws : List Nat) (a : Nat), 8 * (a + 3 * ws.sum) ≤ 8 * T →
      SoundG c M (evLoads a ws) fun es => es.length = ws.length ∧
        ∀ j < ws.length, vs M (es.getD j []) =
          Q1.scalarsAt (feAt sig) (8 * a + 24 * pre ws j) (ws.getD j 0)
  | [], _, _ => soundG_pure ⟨rfl, fun j h => absurd h (by simp)⟩
  | w :: ws, a, hT => soundG_bind (ldEs_sound hS a 3 w fun i hi => by simp at hT; (clear * - hi hT; omega)) fun e he =>
      soundG_bind (evLoads_sound hS ws (a + 3 * w) (by simp at hT ⊢; (clear * - hT; omega))) fun r hr =>
        soundG_pure ⟨by simp [hr.1], fun j hj => by
          rcases j with _ | j
          · simp only [List.getD_cons_zero, he, Q1.scalarsAt, pre, List.take_zero, List.sum_nil]
            exact List.map_congr_left fun i _ => congrArg _ (by (clear * -; first | decide | (simp only [Nat.add_comm, Nat.add_left_comm, Nat.add_assoc]; done) | ring1 | omega))
          · simp only [List.getD_cons_succ]
            rw [hr.2 j (by simpa using hj)]
            simp only [pre, List.take_succ_cons, List.sum_cons]
            congr 1; (clear * -; first | decide | (simp only [Nat.add_comm, Nat.add_left_comm, Nat.add_assoc]; done) | ring1 | omega)⟩

end

/-! ## The terms of all tables -/

/-- Each table's term (`termG`), table `j` with its stacked blocks. -/
def termsG (z xi fp2 : Cell) (K : TK) (Xs : List Cell) (evs : List (List Cell))
    (Lpp : List ((SBlk × Nat) × Cell)) (Lc : List (((Nat × Nat × Nat) × Nat) × Cell)) :
    List (TShape × Nat) → BM (List Cell)
  | [] => pure []
  | tj :: rest => do
    let x ← termG z xi (Xs.getD tj.2 z) fp2 K tj.1.cons (evs.getD tj.2 [])
      (Lpp.filter fun y => y.1.1.tab == tj.2) (Lc.filter fun y => y.1.1.1 == tj.2)
    let r ← termsG z xi fp2 K Xs evs Lpp Lc rest
    pure (x :: r)

/-- The value `termG` computes for table `(t, j)`. -/
def termVal (M : Mem) (xi X fp2 : Cell) (fp0 fp1 β : FE) (eqα : List FE) (cons : List CPoly)
    (ev : List Cell) (Lpp : List ((SBlk × Nat) × Cell)) (Lc : List (((Nat × Nat × Nat) × Nat) × Cell)) : FE :=
  X.val M * polyEval (cons.map (CPoly.evalE ((vs M ev).getD · 0))) (xi.val M) +
    sumE (Lpp.map fun x => x.2.val M * (fp0 * (fPush eqα β x.1.1).form.value ((vs M ev).getD · 0) +
      fp1 * (fPull eqα β x.1.1).form.value ((vs M ev).getD · 0))) +
    fp2.val M * sumE (Lc.map fun x => x.2.val M * (vs M ev).getD x.1.1.2.2 0)

section
variable {c : Ctx} {M : Mem} {z : Cell}

theorem termsG_sound (hz : z.val M = 0) (hzE : z.ty = .E) {K : TK} {fp0 fp1 β : FE} {eqα : List FE}
    (hK : TKOk M z K fp0 fp1 β eqα) (xi fp2 : Cell) (Xs : List Cell) (evs : List (List Cell))
    (Lpp : List ((SBlk × Nat) × Cell)) (Lc : List (((Nat × Nat × Nat) × Nat) × Cell)) :
    ∀ l : List (TShape × Nat), SoundG c M (termsG z xi fp2 K Xs evs Lpp Lc l) fun ts =>
      vs M ts = l.map fun tj => termVal M xi (Xs.getD tj.2 z) fp2 fp0 fp1 β eqα tj.1.cons
        (evs.getD tj.2 []) (Lpp.filter fun y => y.1.1.tab == tj.2) (Lc.filter fun y => y.1.1.1 == tj.2)
  | [] => soundG_pure rfl
  | tj :: rest => soundG_bind (termG_sound hz hzE hK xi _ fp2 tj.1.cons _ _ _) fun x hx =>
      soundG_bind (termsG_sound hz hzE hK xi fp2 Xs evs Lpp Lc rest) fun r hr => soundG_pure (by
        rw [vs, List.map_cons, List.map_cons, ← vs, hr, hx]; rfl)

end

/-! ## The static plan of the weights -/

/-- The separators of the shapes' keys. -/
def sepsOf (S : List TShape) : List FK := ((ppBlocks S).map (·.key.sep)).eraseDups

/-- Every stacked block of both sides: (height, offset). -/
def allKO (S : List TShape) : List (Nat × Nat) :=
  (ppS S).map (fun bo => (bo.1.κ, bo.2)) ++ (cS S).map (fun bo => (bo.1.2.1, bo.2))

/-- The rows of a level with `s` table coordinates: table, products, high parts. -/
def costS (D κ s : Nat) (qs : List Nat) : Nat :=
  (if s = 0 then 0 else 2 * 2 ^ s + qs.length) + (qs.map (· / 2 ^ s)).eraseDups.length * (D - κ - s)

/-- The cheapest `s` of a level. -/
def bestS (D κ : Nat) (qs : List Nat) : Nat :=
  (List.range (D - κ + 1)).foldl (fun b s => if costS D κ s qs < costS D κ b qs then s else b) 0

/-- The levels' table sizes. -/
def planLv (D : Nat) (ko : List (Nat × Nat)) : List (Nat × Nat) :=
  (ko.map (·.1)).eraseDups.map fun κ => (κ, bestS D κ ((ko.filter (·.1 == κ)).map fun x => x.2 >>> κ))

/-- The high parts the blocks use. -/
def planHi (D : Nat) (lv : List (Nat × Nat)) (ko : List (Nat × Nat)) : List (Nat × Nat) :=
  (ko.map fun x =>
    let s := ((lv.find? (·.1 == x.1)).map (·.2)).getD 0
    if s ≠ 0 ∧ x.1 + s ≤ D then (x.1 + s, (x.2 >>> x.1) / 2 ^ s) else (x.1, x.2 >>> x.1)).eraseDups

/-! ## The table phase's gadget -/

/-- The rounds, with the pointer of their first cell. -/
def scP (R L₀ : Nat) (tgt : Cell) : BM (Cell × Nat) := do
  let q ← getPtr
  let fin ← QB.scRunP4 (binParts R) L₀ tgt
  pure (fin, q.e)

/-- Round `i`'s challenge cell of a run from `qe`. -/
def chC (qe i : Nat) : Cell := ec (qe + 1 + 8 * i + 3)

/-- **Phase 3's gadget.** -/
def tabG (S : List TShape) (R P : Nat) (z o g : Cell) (bc : BusC) : BM (List (List Cell × List Cell)) := do
  let xi ← ldE ((P + 40) / 8)
  let pw ← powsG z o xi ((S.map (·.cons.length)).foldl max 0)
  let Xs ← curG z o pw (S.map (·.cons.length)) o
  let fp0 := Xs.getD S.length o
  let fp1 ← mulAdd .E fp0 xi z
  let fp2 ← mulAdd .E fp1 xi z
  let eb ← eqTab (fun i => bc.al.getD i z) z o false bc.al.length
  let K ← tkG z fp0 fp1 bc.be eb (2 ^ bc.al.length) (sepsOf S)
  let facs ← facG bc.pt
  let lv := planLv bc.pt.length (allKO S)
  let lt ← lvlsG z o bc.pt lv
  let hi ← hisG z o facs (planHi bc.pt.length lv (allKO S))
  let wpp ← bwsG z o facs lt hi bc.pt.length ((ppS S).map fun bo => (bo.1.κ, bo.2))
  let wc ← bwsG z o facs lt hi bc.pt.length ((cS S).map fun bo => (bo.1.2.1, bo.2))
  let spp ← sumG z wpp
  let scc ← sumG z wc
  let T0 ← lin .E 1 1 (bc.vals.getD 0 z) spp
  let T1 ← lin .E 1 1 (bc.vals.getD 1 z) spp
  let T2 ← lin .E 1 1 (bc.vals.getD 2 z) scc
  let t0 ← mulAdd .E fp0 T0 z
  let t1 ← mulAdd .E fp1 T1 t0
  let tgt ← mulAdd .E fp2 T2 t1
  let r ← scP R ((P + 72) / 8) tgt
  let ws ← QB.tableW z o (fun k => bc.pt.getD k z) (chC r.2) R (S.map (·.τ))
  let evs ← evLoads ((P + 72 + 144 * R + 40) / 8) (S.map (·.cols.length))
  let terms ← termsG z xi fp2 K Xs evs ((ppS S).zip wpp) ((cS S).zip wc) S.zipIdx
  QB.tableFinal z g r.1 ws terms
  pure ((S.zip evs).map fun x => (((List.range R).map (chC r.2)).reverse.take x.1.τ, x.2))

/-- The position after phase 3. -/
def tabEnd (S : List TShape) (R P : Nat) : Nat := P + 72 + 144 * R + 24 * (S.map (·.cols.length)).sum

/-! ## Soundness -/

section
variable {c : Ctx} {M : Mem} {sig : ByteArray} {T : Nat}

theorem eqTab_sound {z o : Cell} (hz : z.val M = 0) (hzE : z.ty = .E) (hoE : o.ty = .E) (ho : o.val M = 1)
    {al : List Cell} (halE : ∀ x ∈ al, x.ty = .E) {alphas : List FE} (hal : vs M al = alphas) :
    SoundG c M (eqTab (fun i => al.getD i z) z o false al.length) fun eb =>
      ∀ x < 2 ^ alphas.length, M.e (eb + x) = (eqKernel alphas).getD x 0 := by
  intro p hH _ x hx
  have hlen : al.length = alphas.length := by rw [← hal, vs, List.length_map]
  have hone : M.e o.n = 1 := by rw [← ho]; rcases o with ⟨τ, n⟩; simp at hoE; subst hoE; rfl
  have hty : ∀ i, (al.getD i z).ty = .E := fun i => by
    rw [List.getD_eq_getElem?_getD]
    cases h : al[i]? with
    | none => exact hzE
    | some y => exact halE y (List.mem_of_getElem? h)
  have hv : ∀ i < alphas.length, (al.getD i z).val M = alphas.getD i 0 := fun i hi => by
    rw [← hal, vs, List.getD_eq_getElem _ _ (by rw [hlen]; exact hi),
      List.getD_eq_getElem _ _ (by simp [hlen]; exact hi), List.getElem_map]
  rw [hlen] at hH
  have := eqTab_eq (fun i => al.getD i z) z o false alphas (p := p) hH hz hty hone hv x hx
  rw [hlen]
  simp only [Bool.false_eq_true, ite_false] at this
  rw [this, eqKernelA_getD _ _ hx, List.getD_eq_getElem?_getD, eqKernel_get? _ _ hx]
  rfl

theorem scP_sound (hS : Q1.Streamed M sig T) (R L₀ : Nat) (tgt : Cell) (hT : L₀ + 18 * R ≤ T) :
    SoundG c M (scP R L₀ tgt) fun r => ∀ s : RS, s.msg = 0 → s.ent = 8 * L₀ →
      r.1.val M = (sumcheck (tgt.val M) 4 (List.replicate R none) sig s).1.2 ∧
      ∀ i < R, (chC r.2 i).val M = (sumcheck (tgt.val M) 4 (List.replicate R none) sig s).1.1.getD i 0 := by
  intro p hH _
  simp only [scP, getPtr, bind_apply, pure_apply, Ptr.adv_nil, List.nil_append,
    List.append_nil] at hH ⊢
  intro s hs hent
  have := QB.scRunP4_eq (binParts R) L₀ tgt p hH sig s hs hent (fun j h1 h2 => by
    rw [nRounds_binParts] at h2; exact hS j (by (clear * - hT h2; omega)))
  rw [nRounds_binParts] at this
  exact ⟨this.1, fun i hi => this.2 i hi⟩

theorem tableW_sound {z o : Cell} (hz : z.val M = 0) (ho : o.val M = 1) (e ch : Nat → Cell) (R : Nat)
    (hs : List Nat) (eqPt : List FE) (he : ∀ k, (e k).val M = eqPt.getD k 0) :
    SoundG c M (QB.tableW z o e ch R hs) fun ws => ∀ chs : List FE, chs.length = R →
      (∀ j < R, (ch j).val M = chs.getD j 0) → vs M ws = tableWeights hs eqPt chs.reverse := by
  intro p hH _ chs hl hch
  subst hl
  exact QB.tableW_eq hz ho e ch hs eqPt chs (fun k _ => he k) hch p hH

theorem tableFinal_sound {z g claim : Cell} (hz : z.val M = 0) (hg : g.val M = 1) (ws ts : List Cell) :
    SoundG c M (QB.tableFinal z g claim ws ts) fun _ =>
      (QB.finalOf (vs M ws) (vs M ts) 0 == claim.val M) = true :=
  fun p hH hA => (QB.tableFinal_check hz hg ws ts p hH).mp hA

end

section
variable {c : Ctx} {M : Mem} {sig : ByteArray} {T : Nat}

theorem termsAt_getD (v : Nat → FE) (cp fp pt : List FE) (d : TRow) : ∀ (rows : List TRow) (cur o j : Nat),
    j < rows.length →
    (termsAt v cp fp pt rows cur o).getD j 0 =
      termF cp fp pt (rows.getD j d).1 (rows.getD j d).2.1 (cur + pre (rows.map (·.1.nConstraints)) j)
        (Q1.scalarsAt v (o + 24 * pre (rows.map (·.1.width)) j) (rows.getD j d).1.width)
  | [], _, _, _, h => absurd h (by simp)
  | r :: rest, cur, o, j, h => by
    rcases j with _ | j
    · simp [termsAt, pre]
    · simp only [termsAt, List.getD_cons_succ]
      rw [termsAt_getD v cp fp pt d rest _ _ j (by simpa using h)]
      simp only [pre, List.map_cons, List.take_succ_cons, List.sum_cons]
      rw [show cur + r.1.nConstraints + (List.take j (List.map (fun x => x.1.nConstraints) rest)).sum =
          cur + (r.1.nConstraints + (List.take j (List.map (fun x => x.1.nConstraints) rest)).sum) by (clear * -; first | decide | (simp only [Nat.add_comm, Nat.add_left_comm, Nat.add_assoc]; done) | ring1 | omega),
        show o + 24 * r.1.width + 24 * (List.take j (List.map (fun x => x.1.width) rest)).sum =
          o + 24 * (r.1.width + (List.take j (List.map (fun x => x.1.width) rest)).sum) by (clear * -; first | decide | (simp only [Nat.add_comm, Nat.add_left_comm, Nat.add_assoc]; done) | ring1 | omega)]

theorem termsAt_length (v : Nat → FE) (cp fp pt : List FE) : ∀ (rows : List TRow) (cur o : Nat),
    (termsAt v cp fp pt rows cur o).length = rows.length
  | [], _, _ => rfl
  | r :: rest, cur, o => by simp [termsAt, termsAt_length v cp fp pt rest]

theorem evsAt_getD (v : Nat → FE) (pt : List FE) (d : TRow) : ∀ (rows : List TRow) (o j : Nat),
    j < rows.length →
    (evsAt v pt rows o).getD j ([], []) =
      (pt.take (rows.getD j d).1.logHeight,
        Q1.scalarsAt v (o + 24 * pre (rows.map (·.1.width)) j) (rows.getD j d).1.width)
  | [], _, _, h => absurd h (by simp)
  | r :: rest, o, j, h => by
    rcases j with _ | j
    · simp [evsAt, pre]
    · simp only [evsAt, List.getD_cons_succ]
      rw [evsAt_getD v pt d rest _ j (by simpa using h)]
      simp only [pre, List.map_cons, List.take_succ_cons, List.sum_cons]
      congr 2; (clear * -; first | decide | (simp only [Nat.add_comm, Nat.add_left_comm, Nat.add_assoc]; done) | ring1 | omega)

theorem evsAt_length (v : Nat → FE) (pt : List FE) : ∀ (rows : List TRow) (o : Nat),
    (evsAt v pt rows o).length = rows.length
  | [], _ => rfl
  | r :: rest, o => by simp [evsAt, evsAt_length v pt rest]

theorem sumE_zip_filter {M : Mem} {α : Type} (W : α → FE) (q : α → Bool) (f : α → FE) :
    ∀ (l : List α) (ws : List Cell), vs M ws = l.map W →
      sumE (((l.zip ws).filter fun y => q y.1).map fun y => y.2.val M * f y.1) =
        sumE ((l.filter q).map fun a => W a * f a)
  | [], _, _ => rfl
  | a :: l, [], h => by simp [vs] at h
  | a :: l, w :: ws, h => by
    simp only [vs, List.map_cons, List.cons.injEq] at h
    have ih := sumE_zip_filter W q f l ws h.2
    simp only [List.zip_cons_cons, List.filter_cons]
    split <;> simp only [List.map_cons, sumE_cons, ih, h.1]

theorem pre_add_le (l : List Nat) {j : Nat} (hj : j < l.length) : pre l j + l.getD j 0 ≤ l.sum := by
  rw [pre, List.getD_eq_getElem _ _ hj, ← List.sum_take_succ, ← List.sum_take_add_sum_drop l (j + 1)]
  (clear * -; first | decide | (simp only [Nat.add_comm, Nat.add_left_comm, Nat.add_assoc]; done) | ring1 | (clear * - j l; omega))

theorem take_drop_take {α : Type} (l : List α) {m c n : Nat} (h : c + n ≤ m) :
    ((l.take m).drop c).take n = (l.drop c).take n := by
  rw [List.drop_take, List.take_take, Nat.min_eq_left (by (clear * - n m c h; omega))]

theorem sumE_W2 {α : Type} (W f g : α → FE) (A B : FE) (l : List α) :
    sumE (l.map fun x => W x * (A * f x + B * g x)) =
      A * sumE (l.map fun x => W x * f x) + B * sumE (l.map fun x => W x * g x) := by
  rw [← sumE_map_mul, ← sumE_map_mul, ← sumE_map_add]
  exact congrArg sumE (List.map_congr_left fun x _ => by ring)

theorem le_foldl_max : ∀ (l : List Nat) (a : Nat), a ≤ l.foldl max a ∧ ∀ n ∈ l, n ≤ l.foldl max a
  | [], a => ⟨le_rfl, fun _ h => absurd h List.not_mem_nil⟩
  | x :: l, a => by
    obtain ⟨h1, h2⟩ := le_foldl_max l (max a x)
    refine ⟨le_trans (le_max_left a x) h1, fun n hn => ?_⟩
    rcases List.mem_cons.mp hn with rfl | hn
    · exact le_trans (le_max_right a n) h1
    · exact h2 n hn

/-- **Phase 3, soundness of the gadget.** -/
theorem tabG_sound (hS : Q1.Streamed M sig T) {z o g : Cell} (hz : z.val M = 0) (ho : o.val M = 1)
    (hg : g.val M = 1) (hzE : z.ty = .E) (hoE : o.ty = .E) (p : Params) (m : M3) (pub : Pub)
    (tabs : List Tab) (hm : m.tables pub = (sumcheckTabs tabs).map nativeTable) (bc : BusC)
    {alphas : List FE} {beta countRoot : FE} {point values leafdec : List FE}
    (hal : vs M bc.al = alphas) (hbe : bc.be.val M = beta) (hpt : vs M bc.pt = point)
    (hvals : vs M bc.vals = values) (hal2 : 2 ≤ alphas.length) (halE : ∀ x ∈ bc.al, x.ty = .E)
    (hptE : ∀ x ∈ bc.pt, x.ty = .E) (bus : BusOut)
    (hbus : bus = busFinalR (sumcheckTabs tabs) ⟨alphas, beta, countRoot, point, values, leafdec, pub⟩)
    {P : Nat} (hP : P % 8 = 0)
    (hT : tabEnd ((sumcheckTabs tabs).map Tab.shape) p.tableRounds P + 40 ≤ 8 * T) :
    SoundG c M (tabG ((sumcheckTabs tabs).map Tab.shape) p.tableRounds P z o g bc) fun out =>
      ∀ s : RS, pos s = P → s.ok = true →
        (tabPh p m pub bus point sig s).2.ok = true ∧
        pos (tabPh p m pub bus point sig s).2 = tabEnd ((sumcheckTabs tabs).map Tab.shape) p.tableRounds P ∧
        (tabPh p m pub bus point sig s).1 = out.map fun x => (vs M x.1, vs M x.2) := by
  set st := sumcheckTabs tabs with hst
  set S := st.map Tab.shape with hS'
  set R := p.tableRounds with hR
  have hTE : tabEnd S R P = P + 72 + 144 * R + 24 * (S.map (·.cols.length)).sum := rfl
  unfold tabG
  refine soundG_bind (ldE_sound hS (a := (P + 40) / 8) (by (clear * - hP hT hTE; omega))) fun xi hxi => ?_
  refine soundG_bind (powsG_sound hz ho xi _) fun pw hpw => ?_
  have hpw' : ∀ n ∈ S.map (·.cons.length), (pw.getD n o).val M = xi.val M ^ n := fun n hn =>
    hpw.2 n ((le_foldl_max _ 0).2 n hn)
  refine soundG_bind (curG_sound hz _ o hpw') fun Xs hXs => ?_
  refine soundG_bind (soundG_aspec (QB.aspec_mulAdd .E (Xs.getD S.length o) xi z)) fun fp1 hfp1 => ?_
  refine soundG_bind (soundG_aspec (QB.aspec_mulAdd .E fp1 xi z)) fun fp2 hfp2 => ?_
  refine soundG_bind (eqTab_sound hz hzE hoE ho halE hal) fun eb heb => ?_
  have hall : bc.al.length = alphas.length := by rw [← hal, vs, List.length_map]
  have hlenα : (eqKernel alphas).length = 2 ^ bc.al.length := by rw [eqKernel_length, hall]
  refine soundG_bind (tkG_sound hz (Xs.getD S.length o) fp1 bc.be eb (2 ^ bc.al.length) (sepsOf S)
    (eqα := eqKernel alphas) hlenα (by
      have : 2 ^ 2 ≤ 2 ^ bc.al.length := Nat.pow_le_pow_right (by (clear * -; first | decide | (simp only [Nat.add_comm, Nat.add_left_comm, Nat.add_assoc]; done) | ring1 | omega)) (by (clear * - hal2 hall; omega))
      (clear * - this; omega)) fun i hi => heb i (by rw [hall] at hi; exact hi)) fun K hK => ?_
  refine soundG_bind (facG_sound bc.pt) fun facs hfacs => ?_
  have hf1 : (facs.map (·.2)).map (·.val M) = point := by rw [hfacs.1, ← hpt]; rfl
  have hD : bc.pt.length = point.length := by rw [← hpt, vs, List.length_map]
  refine soundG_bind (lvlsG_sound hz hzE hoE ho hptE hpt _) fun lt hlt => ?_
  refine soundG_bind (hisG_sound hz ho hf1 hfacs.2 _) fun hi hhi => ?_
  refine soundG_bind (bwsG_sound hz ho hf1 hfacs.2 hhi hlt hD _) fun wpp hwpp => ?_
  refine soundG_bind (bwsG_sound hz ho hf1 hfacs.2 hhi hlt hD _) fun wc hwc => ?_
  refine soundG_bind (sumG_sound hz wpp) fun spp hspp => ?_
  refine soundG_bind (sumG_sound hz wc) fun scc hscc => ?_
  refine soundG_bind (soundG_aspec (QB.aspec_lin .E 1 1 (bc.vals.getD 0 z) spp)) fun T0 hT0 => ?_
  refine soundG_bind (soundG_aspec (QB.aspec_lin .E 1 1 (bc.vals.getD 1 z) spp)) fun T1 hT1 => ?_
  refine soundG_bind (soundG_aspec (QB.aspec_lin .E 1 1 (bc.vals.getD 2 z) scc)) fun T2 hT2 => ?_
  refine soundG_bind (soundG_aspec (QB.aspec_mulAdd .E (Xs.getD S.length o) T0 z)) fun t0 ht0 => ?_
  refine soundG_bind (soundG_aspec (QB.aspec_mulAdd .E fp1 T1 t0)) fun t1 ht1 => ?_
  refine soundG_bind (soundG_aspec (QB.aspec_mulAdd .E fp2 T2 t1)) fun tgt htgt => ?_
  refine soundG_bind (scP_sound hS R ((P + 72) / 8) tgt (by (clear * - hP hT hTE; omega))) fun r hr => ?_
  refine soundG_bind (tableW_sound hz ho (fun k => bc.pt.getD k z) (chC r.2) R (S.map fun x : TShape => x.τ) point
    (fun k => by
      simp only [← hpt, vs, List.getD_eq_getElem?_getD, List.getElem?_map]
      cases bc.pt[k]? <;> simp [hz])) fun ws hws => ?_
  refine soundG_bind (evLoads_sound hS (S.map fun x : TShape => x.cols.length) ((P + 72 + 144 * R + 40) / 8)
    (by rw [Nat.mul_add, show 8 * ((P + 72 + 144 * R + 40) / 8) = P + 72 + 144 * R + 40 by (clear * - hP; omega)]
        (clear * - hP hT hTE; omega))) fun evs hevs => ?_
  refine soundG_bind (termsG_sound hz hzE hK xi fp2 Xs evs _ _ S.zipIdx) fun terms hterms => ?_
  refine soundG_bind (tableFinal_sound hz hg ws terms) fun _ hfin => soundG_pure ?_
  intro s hs hok
  rw [tabPh_run p m pub bus point st hm sig s, hs, hok]
  dsimp only
  have hξ : feAt sig (P + 40) = xi.val M := by rw [hxi]; exact congrArg _ (by (clear * - hP; omega))
  have hnC : S.map (·.cons.length) = st.map (·.cons.length) := by simp [hS', Tab.shape]
  have hfp0 : (Xs.getD S.length o).val M = xi.val M ^ (st.map (·.cons.length)).sum := by
    rw [hXs.2 S.length (by simp), ho, one_mul, hnC, pre, show S.length = (st.map (·.cons.length)).length by
      simp [hS'], List.take_length]
  rw [← hR]
  generalize hnC' : (st.map (·.cons.length)).sum = nC at hfp0
  rw [hξ]
  have hfp1v : fp1.val M = xi.val M ^ (nC + 1) := by rw [hfp1.1, hfp0, hz, add_zero, pow_succ]
  have hfp2v : fp2.val M = xi.val M ^ (nC + 2) := by rw [hfp2.1, hfp1v, hz, add_zero]; ring
  have hvk : ∀ k, (bc.vals.getD k z).val M = values.getD k 0 := fun k => by
    simp only [← hvals, vs, List.getD_eq_getElem?_getD, List.getElem?_map]
    cases bc.vals[k]? <;> simp [hz]
  have hWpp : vs M wpp = (ppS S).map fun bo => blockWeight point bo.1.κ bo.2 := by
    rw [hwpp, List.map_map]; rfl
  have hWc : vs M wc = (cS S).map fun bo => blockWeight point bo.1.2.1 bo.2 := by
    rw [hwc, List.map_map]; rfl
  have htgtv : tgt.val M = dot ((powers (xi.val M) (nC + 3)).drop nC) bus.totals := by
    rw [drop_powers3, hbus, totals_eq, dot3, htgt.1, ht1.1, ht0.1, hT0.1, hT1.1, hT2.1, hspp, hscc,
      hWpp, hWc, hvk, hvk, hvk, hfp0, hfp1v, hfp2v, hz, ofK_one]
    ring
  obtain ⟨hr1, hr2⟩ := hr ⟨P + 72, 0, true⟩ rfl (by show P + 72 = _; (clear * - hP; omega))
  rw [htgtv] at hr1 hr2
  have hscl := sumcheck_len (dot ((powers (xi.val M) (nC + 3)).drop nC) bus.totals) 4 (by decide)
    (List.replicate R none) sig ⟨P + 72, 0, true⟩ rfl
  rw [List.length_replicate] at hscl
  generalize sumcheck (dot ((powers (xi.val M) (nC + 3)).drop nC) bus.totals) 4 (List.replicate R none) sig
    ⟨P + 72, 0, true⟩ = SC at hr1 hr2 hscl ⊢
  have hτ : S.map (·.τ) = st.map (·.τ) := by simp [hS', Tab.shape]
  have hW := hws SC.1.1 hscl (fun j hj => hr2 j hj)
  rw [hτ] at hW
  generalize hWdef : tableWeights (st.map (·.τ)) point SC.1.1.reverse = W at hW ⊢
  have hlS : S.length = st.length := by simp [hS']
  have hlF : bus.forms.length = st.length := by rw [hbus, busFinalR_forms_def]; simp
  have hlW : W.length = st.length := by rw [← hWdef, QB.tableWeights_eq]; simp
  have hrows1 : ((st.map nativeTable).zip (bus.forms.zip W)).map (·.1) = st.map nativeTable :=
    List.map_fst_zip (by simp [hlF, hlW])
  have hrows2 : ((st.map nativeTable).zip (bus.forms.zip W)).map (·.2.2) = W := by
    rw [show (fun x : TRow => x.2.2) = Prod.snd ∘ Prod.snd from rfl, ← List.map_map,
      List.map_snd_zip (by simp [hlF, hlW]),
      List.map_snd_zip (by simp [hlF, hlW])]
  have hwid : ((st.map nativeTable).zip (bus.forms.zip W)).map (·.1.width) = S.map (·.cols.length) := by
    rw [show (fun x : TRow => x.1.width) = TableSpec.width ∘ Prod.fst from rfl, ← List.map_map, hrows1,
      List.map_map, hS', List.map_map]
    exact List.map_congr_left fun t _ => by simp [nativeTable, Tab.shape, Tab.w]
  have hncs : ((st.map nativeTable).zip (bus.forms.zip W)).map (·.1.nConstraints) =
      st.map (·.cons.length) := by
    rw [show (fun x : TRow => x.1.nConstraints) = TableSpec.nConstraints ∘ Prod.fst from rfl,
      ← List.map_map, hrows1, List.map_map]; rfl
  have hB : 8 * ((P + 72 + 144 * R + 40) / 8) = P + 72 + 144 * R + 40 := by (clear * - hP hscl; omega)
  have hlX : Xs.length = S.length + 1 := by rw [hXs.1, List.length_map]
  have hev : ∀ j < st.length, vs M (evs.getD j []) =
      Q1.scalarsAt (feAt sig) (P + 72 + 144 * R + 40 + 24 * pre (S.map (·.cols.length)) j)
        ((S.map (·.cols.length)).getD j 0) := fun j hj => by
    rw [hevs.2 j (by simp [hlS, hj]), hB]
  have hWSj : ∀ j (hj : j < st.length), (S.map (·.cols.length)).getD j 0 = (nativeTable st[j]).width := by
    intro j hj
    rw [List.getD_eq_getElem _ _ (by simp [hlS, hj])]
    simp [hS', Tab.shape, nativeTable, Tab.w]
  have hXj : ∀ j < st.length, (Xs.getD j z).val M = xi.val M ^ pre (st.map (·.cons.length)) j := by
    intro j hj
    rw [List.getD_eq_getElem _ _ (by rw [hlX]; (clear * - hlS hlF hlW hj; omega)), ← List.getD_eq_getElem _ o (by rw [hlX]; (clear * - hlS hlF hlW hj; omega)),
      hXs.2 j (by simp [hlS]; (clear * - hlF hlW hj; omega)), ho, one_mul, hnC]
  let d0 : TRow := (⟨0, 0, 0, fun _ _ => []⟩, [], 0)
  have hrowj : ∀ j (hj : j < st.length), ((st.map nativeTable).zip (bus.forms.zip W)).getD j d0 =
      (nativeTable st[j], bus.forms.getD j [], W.getD j 0) := by
    intro j hj
    rw [List.getD_eq_getElem _ _ (by simp [hlF, hlW, hj]), List.getD_eq_getElem _ _ (by rw [hlF]; exact hj),
      List.getD_eq_getElem _ _ (by rw [hlW]; exact hj)]
    simp
  have key : ∀ j (hj : j < st.length),
      termF (List.take nC (powers (xi.val M) (nC + 3))) (List.drop nC (powers (xi.val M) (nC + 3)))
        SC.1.1.reverse (nativeTable st[j]) (bus.forms.getD j []) (pre (st.map (·.cons.length)) j)
        (vs M (evs.getD j [])) =
      termVal M xi (Xs.getD j z) fp2 ((Xs.getD S.length o).val M) (fp1.val M) (bc.be.val M)
        (eqKernel alphas) st[j].cons (evs.getD j [])
        (((ppS S).zip wpp).filter fun y => y.1.1.tab == j) (((cS S).zip wc).filter fun y => y.1.1.1 == j) := by
    intro j hj
    have hcn : pre (st.map (·.cons.length)) j + st[j].cons.length ≤ nC := by
      rw [← hnC']
      have := pre_add_le (st.map (·.cons.length)) (j := j) (by simp [hj])
      rwa [List.getD_eq_getElem _ _ (by simp [hj]), List.getElem_map] at this
    unfold termF termVal
    rw [show (nativeTable st[j]).nConstraints = st[j].cons.length from rfl,
      show ∀ q, (nativeTable st[j]).constraints q (vs M (evs.getD j [])) =
        st[j].cons.map (CPoly.evalE ((vs M (evs.getD j [])).getD · 0)) from fun _ => rfl,
      take_drop_take _ hcn, take_drop_powers _ _ _ _ (by (clear * - hj hcn; omega))]
    have hdp := dot_pows (xi.val M) (st[j].cons.map (CPoly.evalE ((vs M (evs.getD j [])).getD · 0)))
      (pre (st.map (·.cons.length)) j)
    rw [List.length_map] at hdp
    rw [hdp, hbus, forms_value _ _ hj, drop_powers3, dot3, hXj j hj]
    dsimp only
    rw [sumE_zip_filter (fun bo : SBlk × Nat => blockWeight point bo.1.κ bo.2) (fun bo => bo.1.tab == j)
        (fun bo => (Xs.getD S.length o).val M *
            (fPush (eqKernel alphas) (bc.be.val M) bo.1).form.value (fun x => (vs M (evs.getD j [])).getD x 0) +
          fp1.val M *
            (fPull (eqKernel alphas) (bc.be.val M) bo.1).form.value (fun x => (vs M (evs.getD j [])).getD x 0))
        (ppS S) wpp hWpp,
      sumE_zip_filter (fun bo : (Nat × Nat × Nat) × Nat => blockWeight point bo.1.2.1 bo.2)
        (fun bo => bo.1.1 == j) (fun bo => (vs M (evs.getD j [])).getD bo.1.2.2 0) (cS S) wc hWc,
      sumE_W2, hfp0, hfp1v, hfp2v, hbe]
    ring
  have hlr : ((st.map nativeTable).zip (bus.forms.zip W)).length = st.length := by simp [hlF, hlW]
  have hterms' : termsAt (feAt sig) (List.take nC (powers (xi.val M) (nC + 3)))
      (List.drop nC (powers (xi.val M) (nC + 3))) SC.1.1.reverse ((st.map nativeTable).zip (bus.forms.zip W))
      0 (P + 72 + 144 * R + 40) = vs M terms := by
    apply List.ext_getElem
    · rw [termsAt_length, hterms, List.length_map, List.length_zipIdx, hlr, hlS]
    · intro j h1 h2
      have hj : j < st.length := by rw [termsAt_length, hlr] at h1; exact h1
      rw [← List.getD_eq_getElem _ 0 h1, ← List.getD_eq_getElem _ 0 h2,
        termsAt_getD _ _ _ _ d0 _ 0 _ j (by rw [hlr]; exact hj), hrowj j hj, hncs, hwid]
      dsimp only
      rw [Nat.zero_add, ← hWSj j hj, ← hev j hj, key j hj, hterms,
        List.getD_eq_getElem (List.map _ S.zipIdx) 0 (by rw [List.length_map, List.length_zipIdx, hlS]; exact hj),
        List.getElem_map, List.getElem_zipIdx]
      simp only [Nat.zero_add, hS', List.getElem_map]
      rfl
  have hch : (List.range R).map (fun i => (chC r.2 i).val M) = SC.1.1 := by
    apply List.ext_getElem (by simp [hscl])
    intro i h1 h2
    simp only [List.getElem_map, List.getElem_range]
    rw [hr2 i (by simpa using h1), List.getD_eq_getElem _ _ h2]
  refine ⟨?_, ?_, ?_⟩
  · rw [hrows2, hterms', ← hW, ← hr1, Bool.and_true]; exact hfin
  · simp only [pos, hwid, tabEnd]
  · apply List.ext_getElem
    · rw [evsAt_length, hlr]; simp [hlS, hevs.1]
    · intro j h1 h2
      have hj : j < st.length := by rw [evsAt_length, hlr] at h1; exact h1
      rw [← List.getD_eq_getElem _ ([], []) h1, evsAt_getD _ _ d0 _ _ j (by rw [hlr]; exact hj),
        hrowj j hj, hwid]
      dsimp only
      rw [← hWSj j hj, ← hev j hj]
      have hej : evs.getD j [] = evs[j]'(by rw [hevs.1]; simpa [hlS] using hj) :=
        List.getD_eq_getElem _ _ _
      simp only [List.getElem_map, List.getElem_zip, Function.comp_apply]
      refine Prod.ext ?_ (by simp only [hej])
      simp only [vs, List.map_take, List.map_reverse, List.map_map, Function.comp_def]
      rw [hch]
      simp [hS', Tab.shape, nativeTable]

end

/-! ## The headline -/

/-- What phase 3 hands on: `F`'s evaluations are the output cells' values, per table its point cells
(`point.take τ`) and its evaluation cells. -/
def TabR (M : Mem) (evals : List (List FE × List FE)) (out : List (List Cell × List Cell)) : Prop :=
  evals = out.map fun x => (vs M x.1, vs M x.2)

section
variable {c : Ctx} {M : Mem} {sig : ByteArray} {T : Nat}

/-- **Phase 3 replayed** (soundness direction): with `m.tables pub` the executable tables of the sumcheck
tables `st` of `tabs` and `bus = busFinalR st ⟨…⟩` on the values of phase 2's cells, wherever
`tabG (st.map Tab.shape) …` holds and asserts (gate on), `F`'s table phase from any state at position
`P` with `ok` keeps `ok`, ends at `tabEnd`, and its evaluations are the output cells' values. -/
theorem tabG_replays (hS : Q1.Streamed M sig T) {z o g : Cell} (hz : z.val M = 0) (ho : o.val M = 1)
    (hg : g.val M = 1) (hzE : z.ty = .E) (hoE : o.ty = .E) (p : Params) (m : M3) (pub : Pub)
    (tabs : List Tab) (hm : m.tables pub = (sumcheckTabs tabs).map nativeTable) (bc : BusC)
    {alphas : List FE} {beta countRoot : FE} {point values leafdec : List FE}
    (hal : vs M bc.al = alphas) (hbe : bc.be.val M = beta) (hpt : vs M bc.pt = point)
    (hvals : vs M bc.vals = values) (hal2 : 2 ≤ alphas.length) (halE : ∀ x ∈ bc.al, x.ty = .E)
    (hptE : ∀ x ∈ bc.pt, x.ty = .E) (bus : BusOut)
    (hbus : bus = busFinalR (sumcheckTabs tabs) ⟨alphas, beta, countRoot, point, values, leafdec, pub⟩)
    {P : Nat} (hP : P % 8 = 0)
    (hT : tabEnd ((sumcheckTabs tabs).map Tab.shape) p.tableRounds P + 40 ≤ 8 * T) (ptr : Ptr) :
    Replays c M sig (tabPh p m pub bus point)
      (tabG ((sumcheckTabs tabs).map Tab.shape) p.tableRounds P z o g bc) ptr P
      (tabEnd ((sumcheckTabs tabs).map Tab.shape) p.tableRounds P) (TabR M) :=
  fun hok s hs hsok => soundG_ok (tabG_sound hS hz ho hg hzE hoE p m pub tabs hm bc hal hbe hpt hvals
    hal2 halE hptE bus hbus hP hT) hok s hs hsok

end

/-- Phase 3's start at `P20`/`P8`: right after phase 2. -/
def tabPos (p : Params) : Nat := busEnd p (busPos p)

theorem tabPos_mod_P20 : tabPos P20 % 8 = 0 := by decide
theorem tabPos_mod_P8 : tabPos P8 % 8 = 0 := by decide

section
variable {c : Ctx} {M : Mem} {sig : ByteArray} {T : Nat}

/-- **Phase 3 at `P20`** (from `tabPos P20`, right after phase 2). -/
theorem tabG_replays_P20 (hS : Q1.Streamed M sig T) {z o g : Cell} (hz : z.val M = 0)
    (ho : o.val M = 1) (hg : g.val M = 1) (hzE : z.ty = .E) (hoE : o.ty = .E) (m : M3) (pub : Pub)
    (tabs : List Tab) (hm : m.tables pub = (sumcheckTabs tabs).map nativeTable) (bc : BusC)
    {alphas : List FE} {beta countRoot : FE} {point values leafdec : List FE}
    (hal : vs M bc.al = alphas) (hbe : bc.be.val M = beta) (hpt : vs M bc.pt = point)
    (hvals : vs M bc.vals = values) (hal2 : 2 ≤ alphas.length) (halE : ∀ x ∈ bc.al, x.ty = .E)
    (hptE : ∀ x ∈ bc.pt, x.ty = .E) (bus : BusOut)
    (hbus : bus = busFinalR (sumcheckTabs tabs) ⟨alphas, beta, countRoot, point, values, leafdec, pub⟩)
    (hT : tabEnd ((sumcheckTabs tabs).map Tab.shape) P20.tableRounds (tabPos P20) + 40 ≤ 8 * T)
    (ptr : Ptr) :
    Replays c M sig (tabPh P20 m pub bus point)
      (tabG ((sumcheckTabs tabs).map Tab.shape) P20.tableRounds (tabPos P20) z o g bc) ptr (tabPos P20)
      (tabEnd ((sumcheckTabs tabs).map Tab.shape) P20.tableRounds (tabPos P20)) (TabR M) :=
  tabG_replays hS hz ho hg hzE hoE P20 m pub tabs hm bc hal hbe hpt hvals hal2 halE hptE bus hbus
    tabPos_mod_P20 hT ptr

/-- **Phase 3 at `P8`.** -/
theorem tabG_replays_P8 (hS : Q1.Streamed M sig T) {z o g : Cell} (hz : z.val M = 0)
    (ho : o.val M = 1) (hg : g.val M = 1) (hzE : z.ty = .E) (hoE : o.ty = .E) (m : M3) (pub : Pub)
    (tabs : List Tab) (hm : m.tables pub = (sumcheckTabs tabs).map nativeTable) (bc : BusC)
    {alphas : List FE} {beta countRoot : FE} {point values leafdec : List FE}
    (hal : vs M bc.al = alphas) (hbe : bc.be.val M = beta) (hpt : vs M bc.pt = point)
    (hvals : vs M bc.vals = values) (hal2 : 2 ≤ alphas.length) (halE : ∀ x ∈ bc.al, x.ty = .E)
    (hptE : ∀ x ∈ bc.pt, x.ty = .E) (bus : BusOut)
    (hbus : bus = busFinalR (sumcheckTabs tabs) ⟨alphas, beta, countRoot, point, values, leafdec, pub⟩)
    (hT : tabEnd ((sumcheckTabs tabs).map Tab.shape) P8.tableRounds (tabPos P8) + 40 ≤ 8 * T)
    (ptr : Ptr) :
    Replays c M sig (tabPh P8 m pub bus point)
      (tabG ((sumcheckTabs tabs).map Tab.shape) P8.tableRounds (tabPos P8) z o g bc) ptr (tabPos P8)
      (tabEnd ((sumcheckTabs tabs).map Tab.shape) P8.tableRounds (tabPos P8)) (TabR M) :=
  tabG_replays hS hz ho hg hzE hoE P8 m pub tabs hm bc hal hbe hpt hvals hal2 halE hptE bus hbus
    tabPos_mod_P8 hT ptr

end

/-! ## The committed columns' claims as cells -/

/-- **The tables' committed-column claims** as `CClaim`s: per table, each committed column's
evaluation cell at the table's point cells, on its commitment, block `⟨τ, off⟩`. -/
def tabClaims (S : List TShape) (out : List (List Cell × List Cell)) (z : Cell) : List CClaim :=
  (S.zip out).flatMap fun x => x.1.cols.zipIdx.filterMap fun ci => match ci.1 with
    | some (rec, off) => some ⟨if rec then .crec else .main, .point ⟨x.1.τ, off⟩ x.2.1, x.2.2.getD ci.2 z⟩
    | none => none

/-- **The claims' values are `F`'s** (`tableClaimsR` on the evaluations phase 3 returns). -/
theorem tabClaims_val {M : Mem} {z : Cell} (hz : z.val M = 0) (st : List Tab)
    (out : List (List Cell × List Cell)) :
    (tabClaims (st.map Tab.shape) out z).map (CClaim.val M) =
      tableClaimsR st (out.map fun x => (vs M x.1, vs M x.2)) := by
  unfold tabClaims tableClaimsR
  rw [List.map_flatMap, List.zip_map_left, List.zip_map_right, List.flatMap_map, List.flatMap_map]
  refine List.flatMap_congr fun x _ => ?_
  rw [List.map_filterMap]
  simp only [Prod.map, Tab.shape, id_eq]
  rw [List.zipIdx_map, List.filterMap_map]
  refine List.filterMap_congr fun ci _ => ?_
  rcases ci with ⟨col, i⟩
  cases col with
  | com rec off =>
    show Option.map (CClaim.val M) (some _) = some _
    rw [Option.map_some]
    refine congrArg some (Prod.ext rfl ?_)
    show BlockClaim.point _ _ ((x.2.2.getD i z).val M) = BlockClaim.point _ _ _
    congr 1
    simp only [vs, List.getD_eq_getElem?_getD, List.getElem?_map]
    cases x.2.2[i]? <;> simp [hz]
  | fix f ev => rfl

end Lvm.Har
