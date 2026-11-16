-- New for lvm2 (roll 8 = B1, L-D): roll 7's FIN-BV memory facts (`LvmFinBV`: `posBits_of`, `hpos20`, `sBits20`,
-- `pw20`, `nBits20`, `n1_20`, `nN_20`) on any memory whose `K` cells carry the `BITS` classes' outputs (`OutsOn`, the
-- typed rows' `outT20`), their proofs copied with the bus's `out1_at` replaced by `out1_of`. Q_link's position bits are
-- nodeT20's `hpos`; the others are `BVT`'s fields (the typed HAR's hypothesis).
import LvmQAsmInb
import LvmQLinkBits
import LvmQAsmHarBase
import LvmQWireSound
import LvmFinPos
import LvmQTypedBits
import LvmTyped
import LvmTypedLayQ
import LvmNodeSoundT

-- ===== merged from `LvmQTypedBitsS` (GOLF module merge: `LvmQTypedBitsS.lean` is now a stub importing `LvmNodeSoundTBV`) =====
section
-- New for lvm2 (roll 8 = B1, L-D; B1-Q's open item "bitsAux ⇒ row_sound"): the soundness of `BITS` as typed rows.
-- The layout's auxiliary blocks are B1-Q's `bitsAux` (the solver's `auxOf`, by `rfl`); a class's chunk rows hold
-- (L-B's `auxRow_of_wiring`) and are WP-12's `Row.Constraints` and `Row.out`, so `LvmBits.row_sound` gives every output
-- of every real row (`outT_sound`, `LvmBitsTab.out_sound`'s form on the memory read off the words).

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
    rw [if_neg (by (clear * - h1 h2; omega))]
    have hp := Nat.one_le_two_pow (n := S.chunkAt ts x₀ (Nat.log2 (S.n - x₀)))
    by_cases hx : x < x₀ + 2 ^ S.chunkAt ts x₀ (Nat.log2 (S.n - x₀))
    · exact ⟨_, List.mem_cons_self .., h1, hx⟩
    · obtain ⟨c, hc, hc1, hc2⟩ := chunksGo_cover ts fuel (x₀ + 2 ^ S.chunkAt ts x₀ (Nat.log2 (S.n - x₀)))
        (by (clear * - h hp; omega)) x (by (clear * - hx; omega)) h2
      exact ⟨c, List.mem_cons_of_mem _ hc, hc1, hc2⟩

/-- **The chunks cover the real rows.** -/
theorem chunks_cover {x : ℕ} (hx : x < S.n) : ∃ c ∈ S.chunks, c.1 ≤ x ∧ x < c.1 + 2 ^ c.2 :=
  chunksGo_cover S _ S.n 0 (by (clear * -; omega)) x (Nat.zero_le _) hx

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
          _ ≤ 2 ^ c.2 := Nat.pow_le_pow_right (by norm_num) (by (clear * - hL hl; omega))
      simp only [affOnA, Bool.or_eq_true, beq_iff_eq, hl, false_or, Bool.and_eq_true, decide_eq_true_eq,
        List.all_eq_true, List.mem_range] at hfa
      obtain ⟨hb, hall⟩ := hfa
      rw [tab_getD f (show c.1 < S.n by (clear * - hj hn; omega)), tab_getD f (show c.1 + 1 < S.n by (clear * - hj hn h2; omega))] at hb
      have hall' : ∀ i < 2 ^ c.2, f (c.1 + i) = f c.1 + (f (c.1 + 1) - f c.1) * i := by
        intro i hi
        have := hall i hi
        rw [tab_getD f (show c.1 + i < S.n by (clear * - hn hi; omega)), tab_getD f (show c.1 < S.n by (clear * - hj hn; omega)),
          tab_getD f (show c.1 + 1 < S.n by (clear * - hn h2; omega))] at this
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

/-- **`BITS` as typed rows is sound, from the auxiliary rows** (lvm2 E2-FT: any relation that makes every auxiliary
row hold, `hrow`; S2GF's coordinate-split one through `auxRow_of_wiringX`): on a layout holding every class's chunk
blocks at bases `bw`, every real row of every class of `bspecs C noData` has a word (its cell's value when `rd`) whose
valid outputs' cells hold the output words. -/
theorem outT_soundA (C : QCfg) (lay : Typed.Lay) (z : ℕ → FK) (bw : ℕ → ℕ)
    (haux : ∀ (i : ℕ) (S : BSpec) (c : ℕ × ℕ), (bspecs C noData)[i]? = some S → c ∈ S.chunks →
      (⟨c.2, S.chunkRows (bw i) c.1 c.2⟩ : ABlk) ∈ lay.aux)
    (hrow : ∀ {k r j : ℕ}, k < lay.aux.length → j < 2 ^ (lay.aux.getD k default).l →
      r < (lay.aux.getD k default).rows.length → ARowHolds lay z j ((lay.aux.getD k default).rows.getD r default))
    {i : ℕ} {S : BSpec} (hS : (bspecs C noData)[i]? = some S) {x : ℕ} (hx : x < S.n) :
    ∃ w : FK, (S.rd = true → (memOf lay z).k (S.wc x) = w) ∧
      ∀ j < S.outs.length, (S.out j).Valid → (memOf lay z).k (S.oc j x) = ⟨(S.out j).word w.val⟩ := by
  obtain ⟨c, hc, hc1, hc2⟩ := chunks_cover S hx
  obtain ⟨k, hk, hak⟩ := List.mem_iff_getElem.mp (haux i S c hS hc)
  have hget : lay.aux.getD k default = ⟨c.2, S.chunkRows (bw i) c.1 c.2⟩ := by
    rw [List.getD_eq_getElem _ _ hk, hak]
  have hjj : x - c.1 < 2 ^ (lay.aux.getD k default).l := by rw [hget]; show x - c.1 < 2 ^ c.2; (clear * - hc1 hc2; omega)
  have hrows : ∀ r ∈ S.chunkRows (bw i) c.1 c.2, ARowHolds lay z (x - c.1) r := by
    intro r hr
    obtain ⟨r', hr', hrr⟩ := List.mem_iff_getElem.mp hr
    have hr'' : r' < (lay.aux.getD k default).rows.length := by rw [hget]; exact hr'
    have := hrow hk hjj hr''
    rw [hget] at this
    rw [List.getD_eq_getElem _ _ hr', hrr] at this
    exact this
  have hcf : ∀ f ∈ S.cellFns, (cellAddr f c.1 c.2).at [x - c.1] = f (c.1 + (x - c.1)) :=
    fun f hf ↦ chunks_cell S hf hc (by (clear * - hc1 hc2; omega))
  obtain ⟨w, h1, h2⟩ := chunk_sound lay z S (bw i) c.1 c.2 (x - c.1) hrows
    (fun hrd ↦ hcf _ (by simp [BSpec.cellFns, hrd]))
    (fun j hj ↦ hcf _ (List.mem_append_right _ (List.mem_map.mpr ⟨j, List.mem_range.mpr hj, rfl⟩)))
  have e : c.1 + (x - c.1) = x := by (clear * - hc1; omega)
  rw [e] at h1 h2
  exact ⟨w, h1, h2⟩

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
      ∀ j < S.outs.length, (S.out j).Valid → (memOf lay z).k (S.oc j x) = ⟨(S.out j).word w.val⟩ :=
  outT_soundA C lay z bw haux (fun hk hj hr ↦ auxRow_of_wiring Q lay z hlay hone h hk hj hr) hS hx

/-- The solver's layout holds every class's chunk blocks (`mkLayD` on `specQ`). -/
theorem aux_specQ (C : QCfg) (Q : Program) (d : Array (Ty × ℕ × ℕ)) :
    ∃ bw : ℕ → ℕ, ∀ (i : ℕ) (S : BSpec) (c : ℕ × ℕ), (bspecs C noData)[i]? = some S → c ∈ S.chunks →
      (⟨c.2, S.chunkRows (bw i) c.1 c.2⟩ : ABlk) ∈ (mkLayD Q (specQ C Q) d).1.aux := by
  obtain ⟨f, hf⟩ := aux_mkLayD Q (specQ C Q) d
  exact ⟨f, fun i S c hS hc ↦ hf ▸ mem_specQ_auxOf C Q f hS hc⟩

end Lvm.QTyped
end
-- ===== end of `LvmQTypedBitsS` =====

-- ===== merged from `LvmNodeSoundTBits` (GOLF module merge: `LvmNodeSoundTBits.lean` is now a stub importing `LvmNodeSoundTBV`) =====
section
-- New for lvm2 (roll 8 = B1, L-D): the typed `BITS` rows' facts that `NodeSound` reads, on the memory read off a good
-- pair's words: `outT_sound` (`LvmQTypedBitsS`) at `P20`, then Q_sig's `SigBits` as roll 7's `sigBitsOk`
-- (`LvmSigBits`, WP-12b) with the bus's `out1_at` replaced by the typed rows' outputs (its case analysis copied).

/-!
# The typed `BITS` rows' facts at `P20`

* **`outT20`**: every class of `bspecs cfg20 noData`, every real row, every valid output, on `memT x qm qr` of a good
  pair (`outT_sound` with the solver's bases, `aux_specQ`).
* **`sigBits_of_outs`**: `SigBits I o v` from the six classes' outputs on `v` (roll 7's `sigBitsOk`, generic in the
  memory); **`sigBitsT`**: Q_sig's `SigBits` on `memT` (nodeT20's `hbits`).
-/

set_option autoImplicit false

namespace Lvm.NS

open RecursionFast Lvm Lvm.T Lvm.ASM Lvm.Replay Lvm.Loop Lvm.Loop.Build Lvm.QLink Lvm.QSig Lvm.M3
open Lvm.QAsm Lvm.QTyped Lvm.Typed Lvm.TypedV Lvm.BitsTab Lvm.Bits Lvm.SigBits LeanVM.Protocol
open Lvm.VEq (pubX)

theorem layT20_mk : layT20 = (mkLayD QB20 (specQ cfg20 QB20) dints20).1 := rfl

/-- **The `BITS` classes' outputs on a good pair's memory** at `P20`. -/
theorem outT20 (S : Lvm.CT.SF20) (H : THyp TiB) {x : List UInt8} {qm : Column CMain.nu20} {qr : Column 19}
    (hG : GoodT TiB H x qm qr) {B : BSpec} (hB : B ∈ bspecs cfg20 noData) {y : ℕ} (hy : y < B.n) :
    ∃ w : FK, (B.rd = true → (memT x qm qr).k (B.wc y) = w) ∧
      ∀ j < B.outs.length, (B.out j).Valid → (memT x qm qr).k (B.oc j y) = ⟨(B.out j).word w.val⟩ := by
  obtain ⟨bw, haux⟩ := aux_specQ cfg20 QB20 dints20
  rw [← layT20_mk] at haux
  obtain ⟨i, hi⟩ := List.getElem?_of_mem hB
  exact outT_sound cfg20 QB20 layT20 (zT x qm qr) bw haux S.hlay (zT_one H x qm qr) (goodT_wiring hG) hi hy

/-- **Q_sig's `BITS` outputs from the classes' outputs** (roll 7's `sigBitsOk`, its case analysis, on any memory). -/
theorem sigBits_of_outs (v : ℕ → FK) (I : SigIn) (o : SigOut) (bpl : Nat → Nat → Bool × Nat) (Ss : List BSpec)
    (hT : ∀ B ∈ sigSpecs I o bpl, B ∈ Ss) (hln : 1 ≤ I.ln ∧ I.ln ≤ 62)
    (hws : ∀ B ∈ Ss, ∀ y < B.n, ∃ w : FK, (B.rd = true → v (B.wc y) = w) ∧
      ∀ j < B.outs.length, (B.out j).Valid → v (B.oc j y) = ⟨(B.out j).word w.val⟩) :
    SigBits I o v := by
  have o1 : ∀ (B : BSpec), B ∈ Ss → B.rd = true → ∀ (y j : ℕ), y < B.n → j < B.outs.length →
      ∀ {A Bc : ℕ} {b : BOut}, B.wc y = A → B.oc j y = Bc → B.out j = b → b.Valid → Out1 v A b Bc := by
    intro B hB hrd y j hy hj A Bc b hA hBc hb hv
    obtain ⟨w, h1, h2⟩ := hws B hB y hy
    have := h2 j hj (hb ▸ hv)
    unfold Out1
    rw [← hA, ← hBc, this, h1 hrd, hb]
  have tI := hT (sIdx I (bpl 0)) (by simp [sigSpecs])
  have tM := hT (sMd I (bpl 1)) (by simp [sigSpecs])
  have tC := hT (sCs I (bpl 2)) (by simp [sigSpecs])
  have t24 := hT (s24 I o (bpl 3)) (by simp [sigSpecs])
  have t8 := hT (s8 I o (bpl 4)) (by simp [sigSpecs])
  have tN := hT (sN I (bpl 5)) (by simp [sigSpecs])
  have x0 : ∀ {S : BSpec}, S.n = 1 → 0 < S.n := fun h => by (clear * - h; omega)
  refine ⟨?_, fun z hz => ?_, ?_, fun r hr => ?_, ?_, fun i hi s hs l hl => ⟨?_, ?_⟩,
    fun i hi l hl => ⟨?_, ?_⟩, fun t ht u hu l hl => ⟨?_, ?_⟩, fun l hl => ⟨?_, ?_⟩, ?_, ?_,
    fun z hz => ?_, ?_, ?_, fun l hl => ⟨?_, ?_⟩, fun l hl => ⟨?_, ?_⟩⟩
  -- idx: `shl 8`, bits, `shr 16`
  · exact o1 _ tI rfl 0 0 (x0 rfl) (by simp [sIdx]) rfl (by simp [sIdx]) rfl
      (by simp [BOut.Valid])
  · exact o1 _ tI rfl 0 (1 + z) (x0 rfl) (by simp [sIdx] <;> (clear * - hz; omega)) rfl
      (by simp [sIdx] <;> (clear * -; omega)) (getD_idx hz) (show z < 64 by (clear * - hz; omega))
  · exact o1 _ tI rfl 0 17 (x0 rfl) (by simp [sIdx]) rfl (by simp [sIdx]) rfl
      (by simp [BOut.Valid])
  -- md: 256 bits
  · exact o1 _ tM rfl (r / 64) (r % 64) (by simp [sMd] <;> (clear * - hr; omega)) (by simp [sMd] <;> (clear * -; omega))
      rfl (by simp only [sMd] <;> (clear * -; omega))
      (getD_bit (Nat.mod_lt _ (by norm_num))) (Nat.mod_lt _ (by norm_num))
  -- cs: ten bits of a free word
  · obtain ⟨w, -, h2⟩ := hws _ tC 0 (by simp [sCs])
    refine ⟨w.val, fun k hk => ?_⟩
    have hb : (sCs I (bpl 2)).out k = .bit k := getD_bit hk
    have := h2 k (by simp [sCs, hk]) (by rw [hb]; show k < 64; (clear * - hk; omega))
    rw [hb] at this
    exact this
  -- step inputs: `shl 24`, `shr 40`
  · exact o1 _ t24 rfl (4 * (3 * i + s) + l) 0 (by simp only [s24] <;> (clear * - hi hs hl; omega)) (by simp [s24])
      (by simp only [s24]; rw [show (4 * (3 * i + s) + l) / 12 = i by (clear * - hs hl; omega),
        show (4 * (3 * i + s) + l) / 4 % 3 = s by (clear * - hs hl; omega), show (4 * (3 * i + s) + l) % 4 = l by (clear * - hl; omega)])
      (by simp only [s24] <;> (clear * -; omega)) rfl (by simp [BOut.Valid])
  · exact o1 _ t24 rfl (4 * (3 * i + s) + l) 1 (by simp only [s24] <;> (clear * - hi hs hl; omega)) (by simp [s24])
      (by simp only [s24]; rw [show (4 * (3 * i + s) + l) / 12 = i by (clear * - hs hl; omega),
        show (4 * (3 * i + s) + l) / 4 % 3 = s by (clear * - hs hl; omega), show (4 * (3 * i + s) + l) % 4 = l by (clear * - hl; omega)])
      (by simp only [s24] <;> omega) rfl (by simp [BOut.Valid])
  -- chain ends
  · exact o1 _ t8 rfl (4 * i + l) 0 (by simp only [s8] <;> (clear * - hi hl; omega)) (by simp [s8])
      (by simp only [s8]; rw [if_pos (by (clear * - hi hl; omega)), show (4 * i + l) / 4 = i by (clear * - hl; omega),
        show (4 * i + l) % 4 = l by (clear * - hl; omega)])
      (by simp only [s8]; rw [if_pos (by (clear * - hi hl; omega))] <;> (clear * -; omega)) rfl (by simp [BOut.Valid])
  · exact o1 _ t8 rfl (4 * i + l) 1 (by simp only [s8] <;> (clear * - hi hl; omega)) (by simp [s8])
      (by simp only [s8]; rw [if_pos (by (clear * - hi hl; omega)), show (4 * i + l) / 4 = i by (clear * - hl; omega),
        show (4 * i + l) % 4 = l by (clear * - hl; omega)])
      (by simp only [s8]; rw [if_pos (by (clear * - hi hl; omega))] <;> omega) rfl (by simp [BOut.Valid])
  -- path node halves
  · exact o1 _ t8 rfl (532 + (8 * t + 4 * u + l)) 0 (by simp only [s8] <;> (clear * - ht hu hl; omega)) (by simp [s8])
      (by simp only [s8]; rw [if_neg (by (clear * - ht hu hl; omega)), if_pos (by (clear * - ht hu hl; omega)), Nat.add_sub_cancel_left,
        show (8 * t + 4 * u + l) / 4 % 2 = u by (clear * - hu hl; omega), show (8 * t + 4 * u + l) % 4 = l by (clear * - hl; omega),
        show (8 * t + 4 * u + l) / 8 = t by (clear * - hu hl; omega)])
      (by simp only [s8]; rw [if_neg (by (clear * - ht hu hl; omega)), if_pos (by (clear * - ht hu hl; omega))] <;> (clear * -; omega)) rfl (by simp [BOut.Valid])
  · exact o1 _ t8 rfl (532 + (8 * t + 4 * u + l)) 1 (by simp only [s8] <;> (clear * - ht hu hl; omega)) (by simp [s8])
      (by simp only [s8]; rw [if_neg (by (clear * - ht hu hl; omega)), if_pos (by (clear * - ht hu hl; omega)), Nat.add_sub_cancel_left,
        show (8 * t + 4 * u + l) / 4 % 2 = u by (clear * - hu hl; omega), show (8 * t + 4 * u + l) % 4 = l by (clear * - hl; omega),
        show (8 * t + 4 * u + l) / 8 = t by (clear * - hu hl; omega)])
      (by simp only [s8]; rw [if_neg (by (clear * - ht hu hl; omega)), if_pos (by (clear * - ht hu hl; omega))] <;> (clear * -; omega)) rfl (by simp [BOut.Valid])
  -- h'
  · exact o1 _ t8 rfl (660 + l) 0 (by simp only [s8] <;> (clear * - hl; omega)) (by simp [s8])
      (by simp only [s8]; rw [if_neg (by (clear * - hl; omega)), if_neg (by (clear * - hl; omega)), if_pos (by (clear * - hl; omega))] <;> (clear * - hl; omega))
      (by simp only [s8]; rw [if_neg (by (clear * - hl; omega)), if_neg (by (clear * - hl; omega)), if_pos (by (clear * - hl; omega))] <;> (clear * - hl; omega))
      rfl (by simp [BOut.Valid])
  · exact o1 _ t8 rfl (660 + l) 1 (by simp only [s8] <;> (clear * - hl; omega)) (by simp [s8])
      (by simp only [s8]; rw [if_neg (by (clear * - hl; omega)), if_neg (by (clear * - hl; omega)), if_pos (by (clear * - hl; omega))] <;> (clear * - hl; omega))
      (by simp only [s8]; rw [if_neg (by (clear * - hl; omega)), if_neg (by (clear * - hl; omega)), if_pos (by (clear * - hl; omega))] <;> (clear * - hl; omega))
      rfl (by simp [BOut.Valid])
  -- n': `shl 8`, `shr 56`, bits, top, low
  · exact o1 _ tN rfl 0 0 (x0 rfl) (by simp [sN]) rfl (by simp [sN]) rfl
      (by simp [BOut.Valid])
  · exact o1 _ tN rfl 0 1 (x0 rfl) (by simp [sN]) rfl (by simp [sN]) rfl
      (by simp [BOut.Valid])
  · exact o1 _ tN rfl 0 (2 + z) (x0 rfl) (by simp [sN] <;> (clear * - hz; omega)) rfl
      (by simp [sN] <;> (clear * -; omega)) (getD_n hz) (show z < 64 by (clear * - hln hz; omega))
  · exact o1 _ tN rfl 0 (I.ln + 3) (x0 rfl) (by simp [sN]) rfl
      (by simp only [sN] <;> (clear * -; omega)) getD_n_top (by simp only [BOut.Valid]; (clear * - hln; omega))
  · exact o1 _ tN rfl 0 (I.ln + 4) (x0 rfl) (by simp [sN]) rfl
      (by simp only [sN] <;> (clear * -; omega)) getD_n_low (by simp only [BOut.Valid]; (clear * - hln; omega))
  -- c_L'
  · exact o1 _ t8 rfl (664 + l) 0 (by simp only [s8] <;> (clear * - hl; omega)) (by simp [s8])
      (by simp only [s8]; rw [if_neg (by (clear * - hl; omega)), if_neg (by (clear * - hl; omega)), if_neg (by (clear * - hl; omega)),
        if_pos (by (clear * - hl; omega))] <;> (clear * - hl; omega))
      (by simp only [s8]; rw [if_neg (by (clear * - hl; omega)), if_neg (by (clear * - hl; omega)), if_neg (by (clear * - hl; omega)),
        if_pos (by (clear * - hl; omega))] <;> (clear * - hl; omega))
      rfl (by simp [BOut.Valid])
  · exact o1 _ t8 rfl (664 + l) 1 (by simp only [s8] <;> (clear * - hl; omega)) (by simp [s8])
      (by simp only [s8]; rw [if_neg (by (clear * - hl; omega)), if_neg (by (clear * - hl; omega)), if_neg (by (clear * - hl; omega)),
        if_pos (by (clear * - hl; omega))] <;> (clear * - hl; omega))
      (by simp only [s8]; rw [if_neg (by (clear * - hl; omega)), if_neg (by (clear * - hl; omega)), if_neg (by (clear * - hl; omega)),
        if_pos (by (clear * - hl; omega))] <;> (clear * - hl; omega))
      rfl (by simp [BOut.Valid])
  -- leafStmt lanes
  · exact o1 _ t8 rfl (668 + l) 0 (by simp only [s8] <;> (clear * - hl; omega)) (by simp [s8])
      (by simp only [s8]; rw [if_neg (by (clear * - hl; omega)), if_neg (by (clear * - hl; omega)), if_neg (by (clear * - hl; omega)),
        if_neg (by (clear * - hl; omega))] <;> (clear * - hl; omega))
      (by simp only [s8]; rw [if_neg (by (clear * - hl; omega)), if_neg (by (clear * - hl; omega)), if_neg (by (clear * - hl; omega)),
        if_neg (by (clear * - hl; omega))] <;> (clear * - hl; omega))
      rfl (by simp [BOut.Valid])
  · exact o1 _ t8 rfl (668 + l) 1 (by simp only [s8] <;> (clear * - hl; omega)) (by simp [s8])
      (by simp only [s8]; rw [if_neg (by (clear * - hl; omega)), if_neg (by (clear * - hl; omega)), if_neg (by (clear * - hl; omega)),
        if_neg (by (clear * - hl; omega))] <;> (clear * - hl; omega))
      (by simp only [s8]; rw [if_neg (by (clear * - hl; omega)), if_neg (by (clear * - hl; omega)), if_neg (by (clear * - hl; omega)),
        if_neg (by (clear * - hl; omega))] <;> (clear * - hl; omega))
      rfl (by simp [BOut.Valid])


/-! ## At any configuration (lvm2 E2-FT) -/

/-- **The `BITS` classes' outputs hold on `v`** (any configuration `C`). -/
def OutsOnC (C : QCfg) (v : ℕ → FK) : Prop :=
  ∀ B ∈ bspecs C noData, ∀ y < B.n, ∃ w : FK, (B.rd = true → v (B.wc y) = w) ∧
    ∀ j < B.outs.length, (B.out j).Valid → v (B.oc j y) = ⟨(B.out j).word w.val⟩

/-- **The `BITS` classes' outputs** on the memory read off words through a layout holding the classes' chunk blocks,
where every auxiliary row holds (`outT_soundA`; S2GF: `auxRow_of_wiringX`). -/
theorem outsOnC_of (C : QCfg) (tl : Typed.Lay) (z : ℕ → FK) (bw : ℕ → ℕ)
    (haux : ∀ (i : ℕ) (S : BSpec) (c : ℕ × ℕ), (bspecs C noData)[i]? = some S → c ∈ S.chunks →
      (⟨c.2, S.chunkRows (bw i) c.1 c.2⟩ : ABlk) ∈ tl.aux)
    (hrow : ∀ {k r j : ℕ}, k < tl.aux.length → j < 2 ^ (tl.aux.getD k default).l →
      r < (tl.aux.getD k default).rows.length → ARowHolds tl z j ((tl.aux.getD k default).rows.getD r default)) :
    OutsOnC C (memOf tl z).k := fun _ hB _ hy ↦ by
  obtain ⟨i, hi⟩ := List.getElem?_of_mem hB
  exact outT_soundA C tl z bw haux hrow hi hy

/-- **Q_sig's `SigBits`** from the classes' outputs (any configuration). -/
theorem sigBits_ofC (C : QCfg) {v : ℕ → FK} (hv : OutsOnC C v) (hln : 1 ≤ C.ln ∧ C.ln ≤ 62) :
    SigBits (sigIn C) (sigOut C) v :=
  sigBits_of_outs v (sigIn C) _ (bplOf noData) (bspecs C noData)
    (fun B hB ↦ List.mem_append_left _ (List.mem_append_left _ hB)) hln hv

/-- **Q_sig's `SigBits` on a good pair's memory** at `P20` (nodeT20's `hbits`). -/
theorem sigBitsT (S : Lvm.CT.SF20) (H : THyp TiB) {x : List UInt8} {qm : Column CMain.nu20} {qr : Column 19}
    (hG : GoodT TiB H x qm qr) :
    SigBits (sigIn cfg20) (qsig (sigIn cfg20) (p1 (lay cfg20) (nK cfg20) 0)).1 (memT x qm qr).k :=
  sigBits_of_outs _ (sigIn cfg20) _ (bplOf noData) (bspecs cfg20 noData)
    (fun B hB ↦ List.mem_append_left _ (List.mem_append_left _ hB)) ⟨by decide, by decide⟩
    (fun B hB y hy ↦ outT20 S H hG hB hy)

end Lvm.NS
end
-- ===== end of `LvmNodeSoundTBits` =====

/-!
# The `BITS` facts that `NodeSound` and the HAR read, on the typed rows

* **`OutsOn v`**: every class of `bspecs cfg20 noData`, every real row, every valid output holds on `v`
  (`outT20` on `memT`); **`out1_of`**: then `Out1` for an output.
* **`posBits_on`** (`posBits_of`): Q_link's `PosBits`; **`hposT`**: nodeT20's `hpos` (`qin_bits`).
* **`sBits_on`** (`sBits20`), **`pw_on`** (`pw20`), **`nBits_on`** (`nBits20`), **`nRange_on`** (`n1_20`,
  `nN_20`, from Q_sig's `ChildOk`).
* **`out1_entryT`** (`out1_entry`), **`posVal_on`** (`posVal_of`): a position's two field cells add up to
  `kOf (posL …)` (Q_link's position cells then hold it on a good pair: `LvmNodeSoundT20B.posCellsT`).
-/

set_option autoImplicit false

namespace Lvm.NS

open RecursionFast Lvm Lvm.T Lvm.ASM Lvm.Replay Lvm.Loop Lvm.Loop.Build Lvm.QLink Lvm.QSig Lvm.M3
open Lvm.QAsm Lvm.QTyped Lvm.Typed Lvm.TypedV Lvm.BitsTab Lvm.Bits Lvm.SigBits Lvm.Har LeanVM.Protocol
open Lvm.VEq (pubX)

/-- **The `BITS` classes' outputs hold on `v`** (`outT20`'s form; `OutsOnC` at `cfg20`). -/
abbrev OutsOn (v : ℕ → FK) : Prop := OutsOnC cfg20 v

theorem outsOn_memT (S : Lvm.CT.SF20) (H : THyp TiB) {x : List UInt8} {qm : Column CMain.nu20} {qr : Column 19}
    (hG : GoodT TiB H x qm qr) : OutsOn (memT x qm qr).k :=
  fun _ hB _ hy ↦ outT20 S H hG hB hy

theorem lt_padT' {t j : ℕ} (hj : j < t) : j < padT t := by
  obtain ⟨c, hc, h1, h2, h3⟩ := pchunks_cover hj
  have := pchunks_end c hc
  (clear * - h1 h3 this; omega)

theorem posSpecs_memC (C : QCfg) {B : BSpec} (hB : B ∈ posSpecs C fun c ↦ bplOf noData (6 + c)) :
    B ∈ bspecs C noData :=
  List.mem_append_left _ (List.mem_append_right _ hB)

theorem posSpecs_mem {B : BSpec} (hB : B ∈ posSpecs cfg20 fun c ↦ bplOf noData (6 + c)) :
    B ∈ bspecs cfg20 noData :=
  posSpecs_memC cfg20 hB

/-- The low `m` bits field of a word is below `2^m` (`LvmFinBV.fld_lt`). -/
theorem fld_lt' (w : UInt64) {m : Nat} (hm : 1 ≤ m) (hm' : m ≤ 64) :
    ((BOut.fld 0 m 0).word w).toNat < 2 ^ m := by
  simp only [BOut.word]
  rw [UInt64.toNat_shiftRight]
  have h1 : ((64 - m - 0 : Nat).toUInt64).toNat % 64 = 64 - m := by
    rw [Nat.toUInt64_eq, UInt64.toNat_ofNat']; omega
  rw [h1, Nat.shiftRight_eq_div_pow]
  have hlt := (((w >>> (0 : Nat).toUInt64) <<< (64 - m : Nat).toUInt64)).toNat_lt
  have e : 2 ^ 64 = 2 ^ (64 - m) * 2 ^ m := by rw [← pow_add]; congr 1; (clear * - hm hm'; omega)
  rw [e] at hlt
  exact Nat.div_lt_of_lt_mul hlt

/-- **A position's two field cells add up to `kOf (posL …)`** (`posVal_of`: the position classes' `fld`
outputs on the answer lanes, the stream cells `hs`). -/
theorem posVal_on {v : ℕ → FK} (C : QCfg)
    (hout : ∀ {k l x : ℕ} {o : OpenInfo}, k < (opens C.p).length → (opens C.p).getD k default = o →
      l < QAsm.nLanes o.L.height → x < nRows o → ∀ {e : BOut × ℕ × ℕ}, e ∈ laneOuts o.L.height l →
      e.1.Valid → Out1 v (ansLane C.p (o.pe + x) + l) e.1 (posCell C k o x e))
    (hS : StreamOk C.p) (hQ : QOk C.p (lay C)) {ws : List Word}
    (hs : ∀ l < 2 ^ (lay C).m, v ((lay C).sb + l) = laneK ws l)
    {k : ℕ} (hk : k < (opens C.p).length) (hH : ((opens C.p).getD k default).L.height ≤ 64)
    {j : ℕ} (hj : j < ((opens C.p).getD k default).L.t) :
    v ((lay C).fl + posIdx C.p k j) + v ((lay C).fl + 2 ^ (lay C).pa + posIdx C.p k j) =
      kOf (posL C.p ws (((opens C.p).getD k default).pe + j / 8)
        (j % 8 * ((opens C.p).getD k default).L.height) ((opens C.p).getD k default).L.height) := by
  generalize hoD : (opens C.p).getD k default = o at hH hj ⊢
  have ho : o ∈ opens C.p := by
    rw [← hoD, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hk]; exact List.getElem_mem hk
  obtain ⟨h192, h1, hlt⟩ := open_pos_facts hS hQ ho hj
  obtain ⟨hp1, hp2, -, -, -⟩ := hQ.opens _ ho
  have hin := lanes_in hS h1 hlt
  have hT := hQ.hT
  have hx : j / 8 < nRows o := by
    have := lt_padT' hj; unfold nRows; (clear * - this; omega)
  have hj8 : j % 8 < 8 := Nat.mod_lt _ (by norm_num)
  have hji : 8 * (j / 8) + j % 8 = j := by (clear * -; omega)
  have hsH : j % 8 * o.L.height ≤ 7 * o.L.height := Nat.mul_le_mul_right _ (by (clear * -; omega))
  -- the two field entries, their lanes and validity
  have hl1 : (fields o.L.height (j % 8)).1.1 < QAsm.nLanes o.L.height := by
    simp only [fields, QAsm.nLanes]; (clear * - h192 hp1 hp2 hsH; omega)
  have hl2 : (fields o.L.height (j % 8)).2.1 < QAsm.nLanes o.L.height := by
    simp only [fields, QAsm.nLanes]; split_ifs <;> omega
  have hv1 : (BOut.fld (fields o.L.height (j % 8)).1.2.1 (fields o.L.height (j % 8)).1.2.2.1
      (fields o.L.height (j % 8)).1.2.2.2).Valid := by
    show _ < 64 ∧ _ ∧ _
    simp only [fields]; split_ifs <;> omega
  have hv2 : (BOut.fld (fields o.L.height (j % 8)).2.2.1 (fields o.L.height (j % 8)).2.2.2.1
      (fields o.L.height (j % 8)).2.2.2.2).Valid := by
    show _ < 64 ∧ _ ∧ _
    simp only [fields]; split_ifs <;> omega
  have o1 := hout hk hoD hl1 hx (Lvm.Fin.lo_mem o.L.height hj8) hv1
  have o2 := hout hk hoD hl2 hx (Lvm.Fin.hi_mem o.L.height hj8) hv2
  have c1 : posCell C k o (j / 8) ((BOut.fld (fields o.L.height (j % 8)).1.2.1
      (fields o.L.height (j % 8)).1.2.2.1 (fields o.L.height (j % 8)).1.2.2.2), 1, j % 8) =
      (lay C).fl + posIdx C.p k j := by
    simp only [posCell, hji, if_pos hj, ↓reduceIte, Nat.add_zero]; rfl
  have c2 : posCell C k o (j / 8) ((BOut.fld (fields o.L.height (j % 8)).2.2.1
      (fields o.L.height (j % 8)).2.2.2.1 (fields o.L.height (j % 8)).2.2.2.2), 2, j % 8) =
      (lay C).fl + 2 ^ (lay C).pa + posIdx C.p k j := by
    simp only [posCell, hji, if_pos hj]; rfl
  have hlane : ∀ l ≤ 2, ansLane C.p (o.pe + j / 8) + l < 2 ^ (lay C).m := by
    intro l hl
    simp only [ansLane, if_neg (show o.pe + j / 8 ≠ 0 by (clear * - h1; omega))]; (clear * - hin hT hl; omega)
  have hl1' : (fields o.L.height (j % 8)).1.1 ≤ 2 := by
    simp only [fields]; (clear * - h192 hsH; omega)
  have hl2' : (fields o.L.height (j % 8)).2.1 ≤ 2 := by
    simp only [fields]; split_ifs <;> omega
  have hs' : ∀ l < 2 ^ (lay C).m, v l = laneK ws l := fun l hl => by
    have := hs l hl; rwa [show (lay C).sb = 0 from rfl, Nat.zero_add] at this
  unfold Out1 at o1 o2
  rw [← c1, ← c2, o1, o2, hs' _ (hlane _ hl1'), hs' _ (hlane _ hl2')]
  exact Lvm.Fin.fields_posL C.p ws (o.pe + j / 8) (by (clear * - hH hp1 hp2; omega)) hH h192

section OnC

variable {C : QCfg} {v : ℕ → FK} (hv : OutsOnC C v)
include hv

/-- One output, as `Out1` (the typed rows' `out1_at`; any configuration). -/
theorem out1_ofC {B : BSpec} (hB : B ∈ bspecs C noData) (hrd : B.rd = true) {y j : ℕ} (hy : y < B.n)
    (hj : j < B.outs.length) {A Bc : ℕ} {b : BOut} (hA : B.wc y = A) (hBc : B.oc j y = Bc) (hb : B.out j = b)
    (hvb : b.Valid) : Out1 v A b Bc := by
  obtain ⟨w, h1, h2⟩ := hv B hB y hy
  have := h2 j hj (hb ▸ hvb)
  unfold Out1
  rw [← hA, ← hBc, this, h1 hrd, hb]

/-- **Q_link's position bits are the position classes' `bit` outputs** (`posBits_of`; any configuration). -/
theorem posBits_onC : PosBits C.p (lay C) v := by
  constructor
  intro k hk j hj z hz
  obtain ⟨S, hS, -, hrd, y, hy, hwc, jo, hjo, hout, hoc⟩ :=
    posSpecs_bit C (fun c ↦ bplOf noData (6 + c)) hk (lt_padT' hj) hz
  have hA : S.wc y = (lay C).sb + ansLane C.p (((opens C.p).getD k default).pe + j / 8) +
      (j % 8 * ((opens C.p).getD k default).L.height + z) / 64 := by
    rw [hwc]; show _ = 0 + _ + _; rw [Nat.zero_add]
  exact out1_ofC hv (posSpecs_memC C hS) hrd hy hjo hA hoc hout (Nat.mod_lt _ (by norm_num))

end OnC

/-- **Q_link's position bit cells are the answers' bits** (any configuration; `qin_bits`). -/
theorem hposTC {C : QCfg} (hS : StreamOk C.p) (hQ : QOk C.p (lay C)) {v : ℕ → FK} (hv : OutsOnC C v)
    {ws : List Word} (hs : ∀ L < 2 ^ (lay C).m, v ((lay C).sb + L) = laneK ws L) :
    ∀ k < (opens C.p).length, ∀ j < ((opens C.p).getD k default).L.t, ∀ z < ((opens C.p).getD k default).L.height,
      v (bitBase C.p (lay C) k + ((opens C.p).getD k default).L.height * j + z) =
        if ansBit C.p ws (((opens C.p).getD k default).pe + j / 8) (j % 8 * ((opens C.p).getD k default).L.height + z)
        then 1 else 0 :=
  qin_bits hS hQ hs (posBits_onC hv)

section On

variable {v : ℕ → FK} (hv : OutsOn v)
include hv

/-- One output, as `Out1` (the typed rows' `out1_at`). -/
theorem out1_of {B : BSpec} (hB : B ∈ bspecs cfg20 noData) (hrd : B.rd = true) {y j : ℕ} (hy : y < B.n)
    (hj : j < B.outs.length) {A Bc : ℕ} {b : BOut} (hA : B.wc y = A) (hBc : B.oc j y = Bc) (hb : B.out j = b)
    (hvb : b.Valid) : Out1 v A b Bc :=
  out1_ofC hv hB hrd hy hj hA hBc hb hvb

/-- **Q_link's position bits are the position classes' `bit` outputs** (`posBits_of`). -/
theorem posBits_on : PosBits cfg20.p (lay cfg20) v :=
  posBits_onC hv

/-- **The bits of `s'`** (`sBits20`): the class `sSpec`. -/
theorem sBits_on : Lvm.Q1.SBitsS v (sigIn cfg20).hd (bsB cfg20) := by
  intro l hl z hz
  have hS : sSpec cfg20 (bplOf noData (6 + nPosCls cfg20)) ∈ bspecs cfg20 noData :=
    List.mem_append_right _ (by simp)
  have hlen : (sSpec cfg20 (bplOf noData (6 + nPosCls cfg20))).outs.length = 64 := by
    show ((List.range 64).map BOut.bit).length = 64; simp
  have hout : (sSpec cfg20 (bplOf noData (6 + nPosCls cfg20))).out z = .bit z := by
    show ((List.range 64).map BOut.bit).getD z (.bit 0) = .bit z
    rw [List.getD_eq_getElem _ _ (by simpa using hz)]
    simp
  exact out1_of hv hS rfl (y := l) (j := z) hl (by rw [hlen]; exact hz) rfl rfl hout (show z < 64 from hz)

/-- **The PoW fields** (`pw20`): the class `powSpec` writes the low `64 − g` bits of each opening's PoW lane. -/
theorem pw_on (hg : 1 ≤ 64 - P20.grind) :
    ∀ k < (opens P20).length, (v (pwB cfg20 + k)).val.toNat < 2 ^ (64 - P20.grind) := by
  intro k hk
  have hS : powSpec cfg20 (bplOf noData (7 + nPosCls cfg20)) ∈ bspecs cfg20 noData :=
    List.mem_append_right _ (by simp)
  have hcp : cfg20.p = P20 := rfl
  have eout : (powSpec cfg20 (bplOf noData (7 + nPosCls cfg20))).out 0 = .fld 0 (64 - cfg20.p.grind) 0 := by
    simp only [powSpec, BitsTab.BSpec.out, List.getD_cons_zero]
  have hx : k < (powSpec cfg20 (bplOf noData (7 + nPosCls cfg20))).n := by
    simp only [powSpec]; rw [hcp]; exact hk
  have h1 := out1_of hv hS rfl hx (j := 0) (Bc := pwB cfg20 + k) (by simp [powSpec]) rfl rfl eout
    (by rw [hcp]; exact ⟨by decide, hg, by (clear * -; omega)⟩)
  unfold Out1 at h1
  rw [h1]
  show ((BOut.fld 0 (64 - cfg20.p.grind) 0).word _).toNat < _
  rw [hcp]
  exact fld_lt' _ hg (by (clear * -; omega))

/-- An output of a position class's row, in `Out1` form (`out1_entry`). -/
theorem out1_entryT {k l x : ℕ} {o : OpenInfo} (hk : k < (opens cfg20.p).length)
    (ho : (opens cfg20.p).getD k default = o) (hl : l < QAsm.nLanes o.L.height) (hx : x < nRows o)
    {e : BOut × ℕ × ℕ} (he : e ∈ laneOuts o.L.height l) (hve : e.1.Valid) :
    Out1 v (ansLane cfg20.p (o.pe + x) + l) e.1 (posCell cfg20 k o x e) := by
  subst ho
  obtain ⟨S, hS, -, hrd, y, hy, hwc, jo, hjo, hout, hoc⟩ :=
    posSpecs_hit cfg20 (fun c ↦ bplOf noData (6 + c)) hk hl hx he
  exact out1_of hv (posSpecs_mem hS) hrd hy hjo hwc hoc hout hve

/-- `posVal_on` on `v` (the position classes' outputs: `out1_entryT`). -/
theorem posVal_onT (hS : StreamOk cfg20.p) (hQ : QOk cfg20.p (lay cfg20)) {ws : List Word}
    (hs : ∀ l < 2 ^ (lay cfg20).m, v ((lay cfg20).sb + l) = laneK ws l)
    {k : ℕ} (hk : k < (opens cfg20.p).length) (hH : ((opens cfg20.p).getD k default).L.height ≤ 64)
    {j : ℕ} (hj : j < ((opens cfg20.p).getD k default).L.t) :
    v ((lay cfg20).fl + posIdx cfg20.p k j) + v ((lay cfg20).fl + 2 ^ (lay cfg20).pa + posIdx cfg20.p k j) =
      kOf (posL cfg20.p ws (((opens cfg20.p).getD k default).pe + j / 8)
        (j % 8 * ((opens cfg20.p).getD k default).L.height) ((opens cfg20.p).getD k default).L.height) :=
  posVal_on cfg20 (out1_entryT hv) hS hQ hs hk hH hj

end On

/-- **Q_link's position bit cells are the answers' bits** (nodeT20's `hpos`; `qin_bits`). -/
theorem hposT {v : ℕ → FK} (hv : OutsOn v) {ws : List Word} (hs : ∀ L < 2 ^ (lay cfg20).m, v ((lay cfg20).sb + L) = laneK ws L) :
    ∀ k < (opens P20).length, ∀ j < ((opens P20).getD k default).L.t, ∀ z < ((opens P20).getD k default).L.height,
      v (bitBase P20 (lay cfg20) k + ((opens P20).getD k default).L.height * j + z) =
        if ansBit P20 ws (((opens P20).getD k default).pe + j / 8) (j % 8 * ((opens P20).getD k default).L.height + z)
        then 1 else 0 :=
  by
  have h := hposTC (C := cfg20) hS20 hQ20 hv hs
  rw [show cfg20.p = P20 from rfl] at h
  exact h

/-- The bits of the child's `n'` (`nBits20`): Q_sig's class `sN` (`SigBits.n_bit`). -/
theorem nBits_on {v : ℕ → FK} {o : SigOut} (hsb : SigBits (sigIn cfg20) o v) :
    NBits v ((sigIn cfg20).bn + 2) P20.logN := by
  intro j hj
  have hlog : P20.logN = 20 := rfl
  rw [hlog] at hj
  exact SigBits.n_bit hsb j (show j ≤ 20 by (clear * - hj; omega))

/-- `Σ` holds the seed query: `hashedLen ≥ 5,040 (the seed holds at least the header's fixed part)` (`LvmFinBV.hashedLen_ge`). -/
theorem hashedLen_ge' {p : Params} (hS : StreamOk p) : 5040 ≤ hashedLen p := by
  have h := entry_end p (i := 1) (by have := plan_length_ge p; omega)
  have h1 : 4952 ≤ ((plan p).getD 1 default).len := by
    rw [plan_one]
    show 4952 ≤ seedLenP p
    have := hdrFix_le_P p
    have : hdrFix = 4928 := by decide
    rw [seedLenP_eq]; omega
  rw [bOff_one, ← hS.2] at h
  omega

/-- **`1 ≤ n' ≤ 2^logN`** (`n1_20`, `nN_20`): Q_sig's `ChildOk` on the child's header lane `n'` (stream lane 24). -/
theorem nRange_on {v : ℕ → FK} (hch : ChildOk (sigIn cfg20) v) {qr : Column 19}
    (hhd : ∀ k < 615, v ((sigIn cfg20).hd + k) = laneK (wsC qr) (11 + k)) (hL : LaneLink P20 (wsC qr))
    (vk cL : RecursionFast.Digest) :
    1 ≤ (pubOf vk cL (traceBytesB (decode P20 (wsC qr)))).n ∧
      (pubOf vk cL (traceBytesB (decode P20 (wsC qr)))).n ≤ 2 ^ P20.logN := by
  have h1 : 1 ≤ (v ((sigIn cfg20).hd + 13)).val.toNat := hch.2.2.1
  have h2 : (v ((sigIn cfg20).hd + 13)).val.toNat ≤ 2 ^ P20.logN := hch.2.2.2.1
  rw [hhd 13 (by norm_num)] at h1 h2
  have hlen := hashedLen_ge' hS20
  have hws : (wsC qr).length = 17 * 2 ^ 14 := by simp [wsC, wsOf]
  have hk := kAt_sigma P20 (wsC qr) 24 (by (clear * - hlen; omega)) (by (clear * - hws; omega))
  rw [traceBytesB_decode hS20 hL]
  have e : (pubOf vk cL (sigma P20 (wsC qr))).n = (laneAt (sigma P20 (wsC qr)) (headerAt 112)).toNat := rfl
  rw [e, show headerAt 112 = 8 * 24 from rfl,
    show laneAt (sigma P20 (wsC qr)) (8 * 24) = (kAt (sigma P20 (wsC qr)) (8 * 24)).val from rfl, hk]
  exact ⟨h1, h2⟩

end Lvm.NS
