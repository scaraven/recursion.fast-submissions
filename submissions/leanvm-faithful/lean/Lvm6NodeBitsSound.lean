-- New for lvm6 (WP NODE3 phase 3, RV4 m5). The deployed `BITS` rows' outputs from the guard (`bitsAuxInB`) and the
-- auxiliary rows: season 1's typed-`BITS` soundness (`chunk_sound`, `sigBits_of_outs`, copied from the parked
-- `LvmNodeSoundTBV`, unchanged) at one row (`rowBlk6`), then `SigBits`, `SigBitsC` and `Q_link`'s position bits.
import Lvm6NodeBits

/-!
# The `BITS` outputs of the deployed circuit (WP NODE3, RV4 m5)

The aux rows are not gated: the prover fills them at `b = 0` too. Copied from season 1 (`lean-s1-parked/
LvmNodeSoundTBV`): `lsum_succ`, `sum_range_ofK`, `sum_filter_eq`, `arow_bool`, `arow_D`, `chunk_sound`, and
`sigBits_of_outs`. New:
* **`rowBlk6_sound`**: a row's two blocks (`boolBlk6`, `outBlk6`) whose rows hold give the class row's word and outputs.
* **`bitsOuts6`**: with `bitsAuxInB lay` and every aux row holding (N4-cells' `blkRows_of_tgoodE`), every row of every
  class of `bitsSpecs6 lay`.
* **`sigBits6`**, **`sigBitsC6`**: `Q_sig`'s `SigBits sigI o` and `SigBitsC sigIl pa` on `memOf lay z`.
* **`posOut6`**: `Q_link`'s position-bit cells hold bit `n mod 64` of answer lane `n / 64` (the `QIn6.bits` form
  modulo the stream lanes).
-/

set_option autoImplicit false

namespace Lvm6.Node.BitsS

open Lvm Lvm.Loop Lvm.Typed Lvm.BitsTab Lvm.Bits Lvm.QTyped Lvm.QSig Lvm.SigBits

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



/-! ## The deployed rows -/

open Lvm6.Node.Dep
open Lvm6.Q (qsig6 opensP18 ansLane6)

theorem cellAddr00 (f : ℕ → ℕ) : (cellAddr f 0 0).at [0] = f 0 := by
  simp [cellAddr, affOn, Addr.at, Loop.dot]

/-- **A row's two blocks whose rows hold** give the class row's word and outputs. -/
theorem rowBlk6_sound (lay : Typed.Lay) (z : ℕ → FK) (S : BSpec) (w x : ℕ)
    (hb : ∀ r ∈ (boolBlk6 S w x).rows, ARowHolds lay z 0 r) (ho : ∀ r ∈ (outBlk6 S w x).rows, ARowHolds lay z 0 r) :
    ∃ wv : FK, (S.rd = true → (memOf lay z).k (S.wc x) = wv) ∧
      ∀ i < S.outs.length, (S.out i).Valid → (memOf lay z).k (S.oc i x) = ⟨(S.out i).word wv.val⟩ := by
  have hrows : ∀ r ∈ rowRows6 S w x, ARowHolds lay z 0 r := by
    intro r hr
    rw [← List.take_append_drop 64 (rowRows6 S w x), List.mem_append] at hr
    rcases hr with hr | hr
    · exact hb r hr
    · exact ho r hr
  exact chunk_sound lay z _ w 0 0 0 hrows (fun _ ↦ cellAddr00 _) (fun _ _ ↦ cellAddr00 _)

/-- **Every row of every class** of the deployed `BITS` classes, from the guard and the aux rows. -/
theorem bitsOuts6 {lay : Typed.Lay} {z : ℕ → FK} (h : bitsAuxInB lay = true)
    (hrow : ∀ blk ∈ lay.aux, ∀ r ∈ blk.rows, ARowHolds lay z 0 r) :
    ∀ S ∈ bitsSpecs6 lay, ∀ x < S.n, ∃ wv : FK, (S.rd = true → (memOf lay z).k (S.wc x) = wv) ∧
      ∀ i < S.outs.length, (S.out i).Valid → (memOf lay z).k (S.oc i x) = ⟨(S.out i).word wv.val⟩ := by
  intro S hS x hx
  obtain ⟨w, hb, ho⟩ := bitsAuxInB_sound h S hS x hx
  exact rowBlk6_sound lay z S w x (hrow _ hb) (hrow _ ho)

/-- **`Q_sig`'s `SigBits`** on the deployed layout's memory. -/
theorem sigBits6 {lay : Typed.Lay} {z : ℕ → FK} (h : bitsAuxInB lay = true)
    (hrow : ∀ blk ∈ lay.aux, ∀ r ∈ blk.rows, ARowHolds lay z 0 r) :
    SigBits sigI (qsig6 sigI sigIl sbC (pS lay ⟨nK, 0⟩)).1.1 (memOf lay z).k :=
  sigBits_of_outs _ _ _ (fun _ ↦ noPl) (bitsSpecs6 lay)
    (fun B hB ↦ by
      simp only [bitsSpecs6, sigSpecs6]
      exact List.mem_append_left _ (List.mem_append_left _ hB))
    ⟨by decide, by decide⟩ (bitsOuts6 h hrow)

/-- **The leaf walk's `SigBitsC`** on the deployed layout's memory. -/
theorem sigBitsC6 {lay : Typed.Lay} {z : ℕ → FK} (h : bitsAuxInB lay = true)
    (hrow : ∀ blk ∈ lay.aux, ∀ r ∈ blk.rows, ARowHolds lay z 0 r) :
    SigBitsC sigIl (qsig6 sigI sigIl sbC (pS lay ⟨nK, 0⟩)).1.2.pa (memOf lay z).k :=
  sigBitsC_of_outs _ sigIl _ (fun _ ↦ noPl) (bitsSpecs6 lay)
    (fun B hB ↦ by
      simp only [bitsSpecs6, sigSpecs6]
      exact List.mem_append_left _ (List.mem_append_right _ hB))
    (bitsOuts6 h hrow)

theorem posSpec6_oc (k l zz q : ℕ) : (posSpec6 k l).oc zz q = posOut k q (64 * l + zz) := by
  simp only [posSpec6]

theorem posSpec6_wc (k l q : ℕ) :
    (posSpec6 k l).wc q = sbC + ansLane6 P6 ((opensP18.getD k default).pd0 + q) + l := by
  simp only [posSpec6]

/-- **`Q_link`'s position-bit cells** (and the scratch cells): bit `zz` of answer lane `l` of draw `q` of opening `k`.
With `posOut`'s index arithmetic and the stream lanes this is `QIn6.bits`. -/
theorem posOut6 {lay : Typed.Lay} {z : ℕ → FK} (h : bitsAuxInB lay = true)
    (hrow : ∀ blk ∈ lay.aux, ∀ r ∈ blk.rows, ARowHolds lay z 0 r) {k : ℕ} (hk : k < opensP18.length)
    {l : ℕ} (hl : l < 2) {q : ℕ} (hq : q < nDraws k) {zz : ℕ} (hzz : zz < 64) :
    (memOf lay z).k (posOut k q (64 * l + zz)) =
      ⟨(BOut.bit zz).word ((memOf lay z).k (sbC + ansLane6 P6 ((opensP18.getD k default).pd0 + q) + l)).val⟩ := by
  have hS : posSpec6 k l ∈ bitsSpecs6 lay := by
    simp only [bitsSpecs6]
    refine List.mem_append_right _ (List.mem_flatMap.mpr ⟨k, List.mem_range.mpr hk, ?_⟩)
    rcases (by omega : l = 0 ∨ l = 1) with rfl | rfl <;> simp
  obtain ⟨wv, h1, h2⟩ := bitsOuts6 h hrow _ hS q hq
  have hout : (posSpec6 k l).out zz = .bit zz := getD_bit hzz
  have := h2 zz (by simp [posSpec6, hzz]) (by rw [hout]; exact hzz)
  rw [hout, posSpec6_oc] at this
  have e := h1 (by simp only [posSpec6])
  rw [posSpec6_wc] at e
  rw [e]
  exact this

end Lvm6.Node.BitsS
