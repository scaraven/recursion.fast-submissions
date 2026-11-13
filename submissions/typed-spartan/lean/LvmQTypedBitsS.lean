-- New for lvm2 (roll 8 = B1, L-D; B1-Q's open item "bitsAux ⇒ row_sound"): the soundness of `BITS` as typed rows.
-- The layout's auxiliary blocks are B1-Q's `bitsAux` (the solver's `auxOf`, by `rfl`); a class's chunk rows hold
-- (L-B's `auxRow_of_wiring`) and are WP-12's `Row.Constraints` and `Row.out`, so `LvmBits.row_sound` gives every output
-- of every real row (`outT_sound`, `LvmBitsTab.out_sound`'s form on the memory read off the words).
import LvmQTypedBits
import LvmTyped
import LvmTypedLayQ

/-!
# `BITS` as typed rows: soundness

* **`aux_mkLayD`**, **`specQ_auxOf`**: the layout's auxiliary blocks are `bitsAux C bw` for the solver's bases `bw`.
* **`chunks_cover`**, **`chunks_cell`**: a class's chunks cover its real rows, and on a chunk every cell function is
  the chunk's affine address (`cellAddr`).
* **`chunk_sound`**: where a chunk's rows hold at iteration `j`, the row `x₀ + j` has a word `w` (its cell's value when
  `rd`) whose output cells hold `o.word w` (`row_sound`).
* **`outT_sound`**: on a checked layout whose auxiliary blocks are `bitsAux C bw`, with the wiring relation and the word
  `1`: every class of `bspecs C noData`, every real row, every valid output (`LvmBitsTab.out_sound`'s statement).
-/

set_option autoImplicit false

namespace Lvm.QTyped

open Lvm Lvm.Loop Lvm.Typed Lvm.BitsTab Lvm.Bits Lvm.QAsm

/-! ## The layout's auxiliary blocks -/

/-- The solver's auxiliary blocks are its specification's (`auxOf`) at its bases. -/
theorem aux_mkLayD (Q : Program) (S : LSpec) (d : Array (Ty × ℕ × ℕ)) :
    ∃ f, (mkLayD Q S d).1.aux = S.auxOf f := by
  unfold mkLayD
  simp only [Id.run]
  exact ⟨_, rfl⟩

theorem moveAux_chunk (S : BSpec) (d x₀ l : ℕ) :
    moveAux d ⟨l, S.chunkRows 0 x₀ l⟩ = ⟨l, S.chunkRows d x₀ l⟩ := by
  simp only [moveAux, BSpec.chunkRows, List.map_append, List.map_map, ABlk.mk.injEq, true_and]
  refine congrArg₂ _ (congrArg₂ _ ?_ ?_) ?_
  · refine List.map_congr_left fun z _ ↦ ?_
    simp [bitOp]; omega
  · split
    · simp only [List.map_cons, List.map_nil, List.map_map, List.cons.injEq, and_true, ARow.mk.injEq, true_and]
      refine List.map_congr_left fun z _ ↦ ?_
      simp [bitOp]; omega
    · rfl
  · refine List.map_congr_left fun j _ ↦ ?_
    simp only [Function.comp_apply, List.map_cons, List.map_map, ARow.mk.injEq, List.cons.injEq, true_and]
    refine List.map_congr_left fun z _ ↦ ?_
    simp [bitOp]; omega

/-- **A class's chunk block is a block of the specification's auxiliary blocks** at the bases `f`. -/
theorem mem_specQ_auxOf (C : QCfg) (Q : Program) (f : ℕ → ℕ) {i : ℕ} {S : BSpec}
    (hS : (bspecs C noData)[i]? = some S) {c : ℕ × ℕ} (hc : c ∈ S.chunks) :
    (⟨c.2, S.chunkRows (f i) c.1 c.2⟩ : ABlk) ∈ (specQ C Q).auxOf f := by
  rw [specQ_eq]
  have hi : i < (bspecs C noData).length := (List.getElem?_eq_some_iff.mp hS).1
  simp only [specQRef, List.mem_flatMap, List.mem_range, List.size_toArray, List.length_map, List.mem_map]
  refine ⟨i, hi, ⟨c.2, S.chunkRows 0 c.1 c.2⟩, ?_, moveAux_chunk S (f i) c.1 c.2⟩
  simp only [Array.getD_eq_getD_getElem?, List.getElem?_toArray, List.getElem?_map, hS, Option.map_some,
    Option.getD_some, BSpec.ablks, List.mem_map]
  exact ⟨c, hc, rfl⟩

/-! ## Chunks -/

section Chunks

variable (S : BSpec)

theorem chunkAt_spec (ts : List (Array ℕ)) (x₀ : ℕ) : ∀ L, S.chunkAt ts x₀ L = 0 ∨
    (x₀ + 2 ^ S.chunkAt ts x₀ L ≤ S.n ∧ BSpec.affChunk ts x₀ (S.chunkAt ts x₀ L) = true)
  | 0 => Or.inl rfl
  | L + 1 => by
    unfold BSpec.chunkAt
    split
    · rename_i h; exact Or.inr ⟨h.2.1, h.2.2⟩
    · exact chunkAt_spec ts x₀ L

theorem chunksGo_mem (ts : List (Array ℕ)) : ∀ (fuel x₀ : ℕ) (c : ℕ × ℕ), c ∈ S.chunksGo ts fuel x₀ →
    ∃ L, c.2 = S.chunkAt ts c.1 L
  | 0, _, _, h => by simp [BSpec.chunksGo] at h
  | fuel + 1, x₀, c, h => by
    unfold BSpec.chunksGo at h
    split at h
    · simp at h
    · rcases List.mem_cons.mp h with rfl | h
      · exact ⟨_, rfl⟩
      · exact chunksGo_mem ts fuel _ c h

theorem chunksGo_cover (ts : List (Array ℕ)) : ∀ (fuel x₀ : ℕ), S.n ≤ x₀ + fuel → ∀ x, x₀ ≤ x → x < S.n →
    ∃ c ∈ S.chunksGo ts fuel x₀, c.1 ≤ x ∧ x < c.1 + 2 ^ c.2
  | 0, x₀, h, x, h1, h2 => by omega
  | fuel + 1, x₀, h, x, h1, h2 => by
    unfold BSpec.chunksGo
    rw [if_neg (by omega)]
    have hp := Nat.one_le_two_pow (n := S.chunkAt ts x₀ (Nat.log2 (S.n - x₀)))
    by_cases hx : x < x₀ + 2 ^ S.chunkAt ts x₀ (Nat.log2 (S.n - x₀))
    · exact ⟨_, List.mem_cons_self .., h1, hx⟩
    · obtain ⟨c, hc, hc1, hc2⟩ := chunksGo_cover ts fuel (x₀ + 2 ^ S.chunkAt ts x₀ (Nat.log2 (S.n - x₀)))
        (by omega) x (by omega) h2
      exact ⟨c, List.mem_cons_of_mem _ hc, hc1, hc2⟩

/-- **The chunks cover the real rows.** -/
theorem chunks_cover {x : ℕ} (hx : x < S.n) : ∃ c ∈ S.chunks, c.1 ≤ x ∧ x < c.1 + 2 ^ c.2 :=
  chunksGo_cover S _ S.n 0 (by omega) x (Nat.zero_le _) hx

/-- **On a chunk, a cell function is its affine address.** -/
theorem chunks_cell {f : ℕ → ℕ} (hf : f ∈ S.cellFns) {c : ℕ × ℕ} (hc : c ∈ S.chunks) {j : ℕ}
    (hj : j < 2 ^ c.2) : (cellAddr f c.1 c.2).at [j] = f (c.1 + j) := by
  obtain ⟨L, hL⟩ := chunksGo_mem S _ _ _ c hc
  rcases chunkAt_spec S S.cellTabs c.1 L with h0 | ⟨hn, ha⟩
  · rw [hL, h0] at hj ⊢
    have : j = 0 := by simpa using hj
    subst this
    simp [cellAddr, affOn, Addr.at, Loop.dot]
  · rw [← hL] at hn ha
    have hfa := List.all_eq_true.mp ha _ (List.mem_map_of_mem (f := fun f => (Array.range S.n).map f) hf)
    by_cases hl : c.2 = 0
    · rw [hl] at hj ⊢
      have : j = 0 := by simpa using hj
      subst this
      simp [cellAddr, affOn, Addr.at, Loop.dot]
    · have h2 : 2 ≤ 2 ^ c.2 := by
        calc 2 = 2 ^ 1 := rfl
          _ ≤ 2 ^ c.2 := Nat.pow_le_pow_right (by norm_num) (by omega)
      simp only [affOnA, Bool.or_eq_true, beq_iff_eq, hl, false_or, Bool.and_eq_true, decide_eq_true_eq,
        List.all_eq_true, List.mem_range] at hfa
      obtain ⟨hb, hall⟩ := hfa
      rw [tab_getD f (show c.1 < S.n by omega), tab_getD f (show c.1 + 1 < S.n by omega)] at hb
      have hall' : ∀ i < 2 ^ c.2, f (c.1 + i) = f c.1 + (f (c.1 + 1) - f c.1) * i := by
        intro i hi
        have := hall i hi
        rw [tab_getD f (show c.1 + i < S.n by omega), tab_getD f (show c.1 < S.n by omega),
          tab_getD f (show c.1 + 1 < S.n by omega)] at this
        simpa using this
      have hA : affOn f c.1 c.2 = some (f c.1, f (c.1 + 1) - f c.1) := by
        simp only [affOn, hl, if_false]
        rw [if_pos ⟨hb, List.all_eq_true.mpr fun i hi => by
          simpa using hall' i (List.mem_range.mp hi)⟩]
      simp only [cellAddr, hA, Addr.at, Loop.dot, add_zero]
      rw [hall' j hj]

end Chunks

/-! ## A chunk's rows -/

section Rows

variable (lay : Typed.Lay) (z : ℕ → FK) (j : ℕ)

theorem lsum_succ (g : ℕ → FK) (n : ℕ) : lsum g (n + 1) = lsum g n + g n := rfl

/-- A sum over `range n` of embedded words is the embedded `lsum`. -/
theorem sum_range_ofK (g : ℕ → FK) : ∀ n, ((List.range n).map fun i ↦ FE.ofK (g i)).sum = FE.ofK (lsum g n)
  | 0 => rfl
  | n + 1 => by
    rw [List.range_succ, List.map_append, List.sum_append, sum_range_ofK g n, lsum_succ, Build.ofK_add]
    simp

/-- Terms dropped by a filter that vanish do not change the sum. -/
theorem sum_filter_eq {α β : Type} [AddCommMonoid β] (l : List α) (p : α → Bool) (g : α → β)
    (h : ∀ a ∈ l, p a = false → g a = 0) : ((l.filter p).map g).sum = (l.map g).sum := by
  induction l with
  | nil => rfl
  | cons a l ih =>
    have ih' := ih fun b hb ↦ h b (List.mem_cons_of_mem _ hb)
    by_cases hp : p a = true
    · simp [List.filter_cons, hp, ih']
    · simp only [Bool.not_eq_true] at hp
      simp [List.filter_cons, hp, ih', h a List.mem_cons_self hp]

/-- A booleanity row holds: its word is a bit's square-sum. -/
theorem arow_bool {op : AOp} (h : ARowHolds lay z j ⟨[(0, op, 1), (1, op, 1), (2, op, 1)]⟩) :
    aopVal lay z j op * aopVal lay z j op + aopVal lay z j op = 0 := by
  simpa [ARowHolds, aRowMat] using h

/-- A row of `D` entries only holds: its entries sum to `0`. -/
theorem arow_D {ops : List (ℕ × AOp × FE)} (hD : ∀ e ∈ ops, e.1 = 2) (h : ARowHolds lay z j ⟨ops⟩) :
    (ops.map fun e ↦ e.2.2 * aopVal lay z j e.2.1).sum = 0 := by
  have h0 : ∀ o, o ≠ 2 → ops.filter (fun e ↦ e.1 == o) = [] := by
    intro o ho
    rw [List.filter_eq_nil_iff]
    intro e he; simp [hD e he, Ne.symm ho]
  have h2 : ops.filter (fun e ↦ e.1 == 2) = ops := by
    rw [List.filter_eq_self]; intro e he; simp [hD e he]
  simpa [ARowHolds, aRowMat, h0 0 (by decide), h0 1 (by decide), h0 3 (by decide), h2] using h

end Rows

/-- **A chunk's rows give its real rows' outputs** (`row_sound`): where every row of the chunk at `x₀` holds at
iteration `j` and its cell operands read the cell functions at `x₀ + j`, row `x₀ + j` has a word `w` (its cell's
value when `rd`) whose output cells hold `o.word w`. -/
theorem chunk_sound (lay : Typed.Lay) (z : ℕ → FK) (S : BSpec) (bw x₀ l j : ℕ)
    (hrows : ∀ r ∈ S.chunkRows bw x₀ l, ARowHolds lay z j r)
    (hwc : S.rd = true → (cellAddr S.wc x₀ l).at [j] = S.wc (x₀ + j))
    (hoc : ∀ i < S.outs.length, (cellAddr (S.oc i) x₀ l).at [j] = S.oc i (x₀ + j)) :
    ∃ w : FK, (S.rd = true → (memOf lay z).k (S.wc (x₀ + j)) = w) ∧
      ∀ i < S.outs.length, (S.out i).Valid → (memOf lay z).k (S.oc i (x₀ + j)) = ⟨(S.out i).word w.val⟩ := by
  set β : ℕ → FK := fun y ↦ z (bw + 64 * x₀ + y + 64 * j) with hβ
  have hval : ∀ y, aopVal lay z j (bitOp bw x₀ y) = FE.ofK (β y) := fun y ↦ rfl
  -- booleanity
  have hbool : ∀ y < 64, β y * β y + β y = 0 := by
    intro y hy
    have h := arow_bool lay z j (hrows _ (by
      simp only [BSpec.chunkRows, List.mem_append, List.mem_map, List.mem_range]
      exact Or.inl (Or.inl ⟨y, hy, rfl⟩)))
    rw [hval, ← Build.ofK_mul, ← Build.ofK_add] at h
    exact Build.ofK_inj (h.trans Build.ofK_zero.symm)
  -- the word
  set w : FK := if S.rd then (memOf lay z).k (S.wc (x₀ + j)) else lsum (fun y ↦ wt y * β y) 64 with hw
  have hsum : ∀ (g : ℕ → FK), (((List.range 64).map fun y ↦ (2, bitOp bw x₀ y, FE.ofK (g y))).map
      fun e ↦ e.2.2 * aopVal lay z j e.2.1).sum = FE.ofK (lsum (fun y ↦ g y * β y) 64) := by
    intro g
    rw [List.map_map, ← sum_range_ofK]
    congr 1
    refine List.map_congr_left fun y _ ↦ ?_
    simp only [Function.comp_apply, hval, Build.ofK_mul]
  have hcon : Row.Constraints ⟨w, β⟩ := by
    refine ⟨hbool, ?_⟩
    show w + lsum (fun y ↦ wt y * β y) 64 = 0
    by_cases hrd : S.rd = true
    · have hmem : (⟨(2, .cell (cellAddr S.wc x₀ l), 1) ::
          (List.range 64).map fun y ↦ (2, bitOp bw x₀ y, FE.ofK (wt y))⟩ : ARow) ∈ S.chunkRows bw x₀ l := by
        simp [BSpec.chunkRows, hrd]
      have h := arow_D lay z j (by
        intro e he
        simp only [List.mem_cons, List.mem_map, List.mem_range] at he
        rcases he with rfl | ⟨y, -, rfl⟩ <;> rfl) (hrows _ hmem)
      rw [List.map_cons, List.sum_cons, hsum] at h
      have hty : (cellAddr S.wc x₀ l).ty = .K := by unfold cellAddr; split <;> rfl
      simp only [aopVal, hty, hwc hrd, Mem.rd, one_mul] at h
      rw [← Build.ofK_add] at h
      have h' := Build.ofK_inj (h.trans Build.ofK_zero.symm)
      rw [hw, if_pos hrd]; exact h'
    · simp only [Bool.not_eq_true] at hrd
      rw [hw, hrd]; exact CharTwo.add_self_eq_zero _
  obtain ⟨-, hout⟩ := row_sound hcon
  refine ⟨w, fun hrd ↦ by rw [hw, if_pos hrd], fun i hi hv ↦ ?_⟩
  have hmem : (⟨(2, .cell (cellAddr (S.oc i) x₀ l), 1) ::
      ((List.range 64).filter fun y ↦ (S.out i).coef y != 0).map fun y ↦ (2, bitOp bw x₀ y, FE.ofK ((S.out i).coef y))⟩ :
      ARow) ∈ S.chunkRows bw x₀ l := by
    simp only [BSpec.chunkRows, List.mem_append, List.mem_map, List.mem_range]
    exact Or.inr ⟨i, hi, rfl⟩
  have h := arow_D lay z j (by
    intro e he
    simp only [List.mem_cons, List.mem_map, List.mem_filter, List.mem_range] at he
    rcases he with rfl | ⟨y, -, rfl⟩ <;> rfl) (hrows _ hmem)
  rw [List.map_cons, List.sum_cons, List.map_map] at h
  have hf : (((List.range 64).filter fun y ↦ (S.out i).coef y != 0).map
      ((fun e : ℕ × AOp × FE ↦ e.2.2 * aopVal lay z j e.2.1) ∘ fun y ↦ (2, bitOp bw x₀ y, FE.ofK ((S.out i).coef y)))).sum =
      FE.ofK (lsum (fun y ↦ (S.out i).coef y * β y) 64) := by
    rw [sum_filter_eq _ _ _ (fun y _ hy ↦ by
      simp only [bne_eq_false_iff_eq] at hy
      simp [Function.comp_apply, hy, Build.ofK_zero])]
    rw [← sum_range_ofK]
    congr 1
    refine List.map_congr_left fun y _ ↦ ?_
    simp only [Function.comp_apply, hval, Build.ofK_mul]
  rw [hf] at h
  have hty : (cellAddr (S.oc i) x₀ l).ty = .K := by unfold cellAddr; split <;> rfl
  simp only [aopVal, hty, hoc i hi, Mem.rd, one_mul] at h
  rw [← Build.ofK_add] at h
  have h' := FK.eq_neg_of_add (Build.ofK_inj (h.trans Build.ofK_zero.symm))
  rw [h']
  exact hout _ hv

/-! ## Every class's outputs -/

/-- **`BITS` as typed rows is sound** (`LvmBitsTab.out_sound`'s statement on the memory read off the words): on a
checked layout holding every class's chunk blocks at bases `bw`, with the wiring relation and the word `1`, every
real row of every class of `bspecs C noData` has a word (its cell's value when `rd`) whose valid outputs' cells hold
the output words. -/
theorem outT_sound (C : QCfg) (Q : Program) (lay : Typed.Lay) (z : ℕ → FK) (bw : ℕ → ℕ)
    (haux : ∀ (i : ℕ) (S : BSpec) (c : ℕ × ℕ), (bspecs C noData)[i]? = some S → c ∈ S.chunks →
      (⟨c.2, S.chunkRows (bw i) c.1 c.2⟩ : ABlk) ∈ lay.aux)
    (hlay : lay.Ok Q) (hone : z lay.one = 1) (h : WiringRel Q lay z)
    {i : ℕ} {S : BSpec} (hS : (bspecs C noData)[i]? = some S) {x : ℕ} (hx : x < S.n) :
    ∃ w : FK, (S.rd = true → (memOf lay z).k (S.wc x) = w) ∧
      ∀ j < S.outs.length, (S.out j).Valid → (memOf lay z).k (S.oc j x) = ⟨(S.out j).word w.val⟩ := by
  obtain ⟨c, hc, hc1, hc2⟩ := chunks_cover S hx
  obtain ⟨k, hk, hak⟩ := List.mem_iff_getElem.mp (haux i S c hS hc)
  have hget : lay.aux.getD k default = ⟨c.2, S.chunkRows (bw i) c.1 c.2⟩ := by
    rw [List.getD_eq_getElem _ _ hk, hak]
  have hjj : x - c.1 < 2 ^ (lay.aux.getD k default).l := by rw [hget]; show x - c.1 < 2 ^ c.2; omega
  have hrows : ∀ r ∈ S.chunkRows (bw i) c.1 c.2, ARowHolds lay z (x - c.1) r := by
    intro r hr
    obtain ⟨r', hr', hrr⟩ := List.mem_iff_getElem.mp hr
    have hr'' : r' < (lay.aux.getD k default).rows.length := by rw [hget]; exact hr'
    have := auxRow_of_wiring Q lay z hlay hone h hk hjj hr''
    rw [hget] at this
    rw [List.getD_eq_getElem _ _ hr', hrr] at this
    exact this
  have hcf : ∀ f ∈ S.cellFns, (cellAddr f c.1 c.2).at [x - c.1] = f (c.1 + (x - c.1)) :=
    fun f hf ↦ chunks_cell S hf hc (by omega)
  obtain ⟨w, h1, h2⟩ := chunk_sound lay z S (bw i) c.1 c.2 (x - c.1) hrows
    (fun hrd ↦ hcf _ (by simp [BSpec.cellFns, hrd]))
    (fun j hj ↦ hcf _ (List.mem_append_right _ (List.mem_map.mpr ⟨j, List.mem_range.mpr hj, rfl⟩)))
  have e : c.1 + (x - c.1) = x := by omega
  rw [e] at h1 h2
  exact ⟨w, h1, h2⟩

/-- The solver's layout holds every class's chunk blocks (`mkLayD` on `specQ`). -/
theorem aux_specQ (C : QCfg) (Q : Program) (d : Array (Ty × ℕ × ℕ)) :
    ∃ bw : ℕ → ℕ, ∀ (i : ℕ) (S : BSpec) (c : ℕ × ℕ), (bspecs C noData)[i]? = some S → c ∈ S.chunks →
      (⟨c.2, S.chunkRows (bw i) c.1 c.2⟩ : ABlk) ∈ (mkLayD Q (specQ C Q) d).1.aux := by
  obtain ⟨f, hf⟩ := aux_mkLayD Q (specQ C Q) d
  exact ⟨f, fun i S c hS hc ↦ hf ▸ mem_specQ_auxOf C Q f hS hc⟩

end Lvm.QTyped
