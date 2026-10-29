-- New for `flock-recursive` (BLUEPRINT revision 4.1, §6.2 step 5, A.5, A.7; stage S-H4, pass 11, item 3:
-- a segment's words in the buffer, the previous node's child program). 3.x analogue: `FRXOutRun.slot_step`.
import FRXOut4F
import FRXOut4K

/-!
# A segment in the buffer; the previous node's signed child

The heap after the decode holds `f⁽⁰⁾`'s decoded cells (**`HeapW κ M₀ w`**: cell `e` with `Dec0 e`,
`e < 2^(m − 7)`, at `wAddr κ e`), so H's message word `n` of a block below `hEnd κ` is the heap word at
`hAddr κ n` (**`hMW_heapW`**). The chain loader's registers for signed child `σ` with `k` segments
(**`ChR`**) make the loader's word `n` the chain word `chW κ σ k w n`: H word
`ldIx cb jL Δ n = 8·blkOf κ σ k ⌊n/8⌋ + n mod 8` of a block below `hEnd κ`. Then

* **`rl_vS`**: after `realign κ` with `qI = i`, the buffer's words are segment `i`'s virtual words
  `vS κ σ k i w` (`realign_sem`, `vS_get`);
* **`prevIR κ`** emits a previous node's signed child (`κ.hasPrev`, child `0`): `|π|`, the proof at
  the ladder of word 10, the trace, the signature (**`prevIR_sem`**: `signedWords (sgnX sigH κ 0 w)`).
-/

namespace FR.X

open RecursionFast FR.Read FR.Rev4 FR.Snd

attribute [local irreducible] entryK storeM runPrims

/-! ## The heap after the decode -/

/-- **The decoded cells on the heap**: cell `e` of `w` at `wAddr κ e` (`decF04_wF`'s conclusion). -/
def HeapW (κ : NodeKind) (M₀ : Mem) (w : Circ.Asg) : Prop :=
  ∀ e, Dec0 e → e < 2 ^ (κ.m - 7) → rdF M₀ (wAddr κ e) = w e

/-- `hEnd κ` blocks fit `f`'s cells (`128` cells a block). -/
theorem hEnd_fit (κ : NodeKind) : N4c.hEnd κ * 128 + 128 ≤ 2 ^ (κ.m - 7) := by cases κ <;> decide

theorem hMW_heapW {κ : NodeKind} {M₀ : Mem} {w : Circ.Asg} (hH : HeapW κ M₀ w) {n : ℕ}
    (hn : n / 8 < N4c.hEnd κ) : rd M₀ (hAddr κ n) = hMW w n := by
  have hf := hEnd_fit κ
  have h := hH (W4.hc (n / 8) (4 + n % 8 / 2)) (by unfold Dec0 W4.hc; omega) (by unfold W4.hc; omega)
  rw [hMW, ← h]
  unfold hAddr
  rcases Nat.mod_two_eq_zero_or_one n with h2 | h2 <;> rw [h2] <;> rfl

theorem hAddr_lt' {κ : NodeKind} {n : ℕ} (hn : n / 8 < N4c.hEnd κ) : hAddr κ n < bufB :=
  hAddr_lt κ (by have := hEnd_fit κ; omega)

/-! ## The chain loader's registers -/

/-- **The chain loader for signed child `σ` with `k` segments**: the loader's H word for chain word
`n` is block `blkOf κ σ k ⌊n/8⌋`'s word `n mod 8`, a block below `hEnd κ` for `n ≤ nB`. -/
structure ChR (κ : NodeKind) (σ k cb jL Δ nB : ℕ) : Prop where
  ld : ∀ n, ldIx cb jL Δ n = 8 * N4c.blkOf κ σ k (n / 8) + n % 8
  blk : ∀ n ≤ nB, N4c.blkOf κ σ k (n / 8) < N4c.hEnd κ
  big : 2 ^ 23 + nW + 1 + cb + Δ < 2 ^ 64
  jl : jL < 2 ^ 64

/-- **After `realign κ` with `qI = i`, the buffer holds segment `i`'s virtual words.** -/
theorem rl_vS (I : Array Word) (κ : NodeKind) {σ k i cb jL Δ nB : ℕ} {w : Circ.Asg} {M₀ : Mem} {t : St}
    (hO : OF M₀ t) (hsz : bufB + 2 ^ 22 ≤ M₀.size) (hH : HeapW κ M₀ w) (hC : ChR κ σ k cb jL Δ nB) (hi4 : i ≤ 4)
    (hnB : i * (N4c.segB - 1) / 8 + nW ≤ nB) (hD : i * (N4c.segB - 1) + N4c.segB ≤ N4c.streamB κ σ k)
    (hi : rd t.M qI = toWord i) (hcb : rd t.M qCB = toWord cb) (hjr : rd t.M qJ = toWord jL)
    (hd : rd t.M qDl = toWord Δ) :
    OF M₀ (semXIR I (realign κ) t) ∧ (semXIR I (realign κ) t).o = t.o ∧
      ∀ u (hu : u < (vS κ σ k i w).length), (vS κ σ k i w)[u] = src (semXIR I (realign κ) t).M apB bufB u := by
  have hG : ∀ n ≤ nB, rd M₀ (hAddr κ (ldIx cb jL Δ n)) = chW κ σ k w n ∧ hAddr κ (ldIx cb jL Δ n) < bufB :=
    fun n hn => by
      have hb := hC.blk n hn
      have e : ldIx cb jL Δ n / 8 = N4c.blkOf κ σ k (n / 8) := by rw [hC.ld]; omega
      refine ⟨?_, hAddr_lt' (by rw [e]; exact hb)⟩
      rw [hMW_heapW hH (n := ldIx cb jL Δ n) (by rw [e]; exact hb), hC.ld, chW]
  obtain ⟨O1, o1, b1⟩ := realign_sem I κ hO hsz hi4 hi hcb hjr hd hC.big hC.jl
    (fun n hn => (hG n (by omega)).2)
  refine ⟨O1, o1, fun u hu => ?_⟩
  have hl := vS_length κ σ k i w hD
  have huW : u < nW := by rw [hl] at hu; simp only [nW, N4c.segB] at hu ⊢; omega
  rw [vS_get κ σ k i w hD hu, src_bufA _ (by simp only [nW] at huW; omega), b1 u huW]
  simp only [shWd]
  rw [(hG _ (by omega)).1, (hG _ (by omega)).1]

/-! ## The previous node's signed child -/

/-- A previous node's chain registers: base `0`, last block `cLen − 1`, no redirect, segment `0`. -/
def prevRegs (κ : NodeKind) : XIR :=
  .blk [.const qCB (toWord (8 * N4c.chBase κ 0)), .const qJ (toWord (N4c.cLen - 1)), .const qDl 0, .const qI 0]

/-- **A previous node's signed child** (child `0`): `|π|`, the proof, the trace, the signature. -/
def prevIR (κ : NodeKind) : XIR :=
  .seq (.blk [.const oX (toWord (piSizeOf seq4))]) (.seq (.out oX)
  (.seq (prevRegs κ) (.seq (realign κ) (.seq pfIR (.seq (bufSeg (trSeg4 seq4)) (sigIR κ 0))))))

theorem chR_prev (κ : NodeKind) (hκ : κ.hasPrev = true) :
    ChR κ 0 0 (8 * N4c.chBase κ 0) (N4c.cLen - 1) 0 nW := by
  have hl : N4c.streamL κ 0 0 = N4c.cLen := by simp [N4c.streamL, N4c.isAgg, hκ]
  have hf : N4c.finBlk κ 0 0 = N4c.cLen - 1 := by
    simp [N4c.finBlk, N4c.isAgg, hκ, N4c.chBase, N4c.chLen]
  have hb : ∀ i, N4c.blkOf κ 0 0 i = i := fun i => by
    unfold N4c.blkOf; rw [hl, hf]; simp only [N4c.chBase, Nat.zero_mul, Nat.zero_add]; split_ifs <;> omega
  refine ⟨fun n => ?_, fun n hn => ?_, by simp [N4c.chBase, nW], by simp [N4c.cLen]⟩
  · rw [hb]; unfold ldIx; simp only [N4c.chBase, Nat.zero_mul, Nat.mul_zero]; split_ifs <;> omega
  · rw [hb]
    have : 23168 < N4c.hEnd κ := by cases κ <;> decide
    simp only [nW] at hn; omega

/-- The signature's WOTS blocks lie below `hEnd κ`. -/
theorem wb_fit (κ : NodeKind) {σ : ℕ} (hσ : σ < 2) : W4.wb κ σ 0 + 500 < N4c.hEnd κ ∧ W4.wb κ σ 0 < 2 ^ 50 := by
  interval_cases σ <;> cases κ <;> decide

/-- The index word is the shift-1 pair at WOTS block `399` (`sigWords_sigH`'s first word). -/
theorem idx_word (κ : NodeKind) (σ : ℕ) (w : Circ.Asg) :
    toWord (idxH κ σ w) = shWd (hMW w) 1 (8 * W4.wb κ σ 399) := by
  show wOf (fun k => hMB w (W4.wb κ σ 399) (1 + k)) = _
  rw [← wOf_hMBs w (by norm_num) (by norm_num)]
  exact wOf_congr fun k hk => by
    rw [show 8 * (8 * W4.wb κ σ 399) + 1 + k = 64 * W4.wb κ σ 399 + (1 + k) by ring, hMBs_blk _ _ (by omega)]

theorem sigL_eq (κ : NodeKind) {σ : ℕ} (hσ : σ < 2) {M₀ : Mem} {w : Circ.Asg} (hH : HeapW κ M₀ w) :
    sigL (fun m => rd M₀ (hAddr κ m)) (W4.wb κ σ 0) = sigWords (sigH κ σ w) := by
  have hf := wb_fit κ hσ
  have hG : ∀ m ≤ 8 * W4.wb κ σ 0 + 4000, rd M₀ (hAddr κ m) = hMW w m := fun m hm =>
    hMW_heapW hH (by omega)
  have sh : ∀ s n, n + 1 ≤ 8 * W4.wb κ σ 0 + 4000 →
      shWd (fun m => rd M₀ (hAddr κ m)) s n = shWd (hMW w) s n := fun s n hn => by
    simp only [shWd]; rw [hG n (by omega), hG (n + 1) hn]
  have hw : ∀ o, W4.wb κ σ o = W4.wb κ σ 0 + o := fun o => by simp only [W4.wb]; omega
  have h399 : 8 * W4.wb κ σ 0 + 3192 = 8 * W4.wb κ σ 399 := by simp only [W4.wb]; omega
  have hidx : (shWd (hMW w) 1 (8 * W4.wb κ σ 0 + 3192)).toNat = idxH κ σ w := by
    rw [h399, ← idx_word, toNat_toWord (show idxH κ σ w < 2 ^ 64 from ofLE_lt64 (by simp))]
  have hX : shWd (fun m => rd M₀ (hAddr κ m)) 1 (8 * W4.wb κ σ 0 + 3192) = shWd (hMW w) 1 (8 * W4.wb κ σ 0 + 3192) :=
    sh _ _ (by omega)
  simp only [sigL, sigWords_sigH]
  refine congrArg₂ (· ++ ·) (congrArg₂ List.cons (by rw [hX, h399]) ?_) ?_
  · refine List.flatMap_congr fun i hi => List.map_congr_left fun j hj => ?_
    have := List.mem_range.1 hi; have := List.mem_range.1 hj
    rw [sh _ _ (by simp only [wotsLen] at *; omega), show 8 * W4.wb κ σ 0 + 1 + 24 * i + j =
      8 * W4.wb κ σ (3 * i) + 1 + j by simp only [W4.wb]; ring]
  · refine List.flatMap_congr fun t ht => List.map_congr_left fun j hj => ?_
    have := List.mem_range.1 ht; have := List.mem_range.1 hj
    have hof : offB (shWd (fun m => rd M₀ (hAddr κ m)) 1 (8 * W4.wb κ σ 0 + 3192)) t =
        if idxH κ σ w / 2 ^ t % 2 = 1 then 0 else 4 := by
      rw [hX, offB, hidx]
    rw [hof, sh _ _ (by simp only [sigHeight] at *; split_ifs <;> omega),
      show 8 * W4.wb κ σ 0 + 3728 + 16 * t = 8 * W4.wb κ σ (466 + 2 * t) by simp only [W4.wb]; ring]

/-- A heap word above the registers is kept: the buffer's source is too. -/
theorem src_congr {M M' : Mem} (h : ∀ y, regs ≤ y → rd M' y = rd M y) : src M' apB bufB = src M apB bufB :=
  funext fun u => h _ (hA_B _)

/-- **A previous node's signed child is emitted** (`signedWords_prev`). -/
theorem prevIR_sem (I : Array Word) (κ : NodeKind) (hκ : κ.hasPrev = true) {M₀ : Mem} {w : Circ.Asg} {s : St}
    (hO : OF M₀ s) (hsz : bufB + 2 ^ 22 ≤ M₀.size) (hH : HeapW κ M₀ w) :
    (semXIR I (prevIR κ) s).o.toList = s.o.toList ++ signedWords (sgnX sigH κ 0 w) ∧
      OF M₀ (semXIR I (prevIR κ) s) := by
  have hs := hO.inv.1
  simp only [regs] at hs
  rw [prevIR, semXIR_seq, semXIR_blk, semXIR_seq]
  rw [show semXIR I (.out oX) ⟨runPrims [.const oX (toWord (piSizeOf seq4))] s.M, s.o⟩ =
    ⟨runPrims [.const oX (toWord (piSizeOf seq4))] s.M,
      s.o.push (rd (runPrims [.const oX (toWord (piSizeOf seq4))] s.M) oX)⟩ from rfl]
  have x1 : rd (runPrims [.const oX (toWord (piSizeOf seq4))] s.M) oX = toWord (piSizeOf seq4) := by
    simp only [runPrims, List.foldl, Prim.run]; rw [rd_set_self (by simp only [oX]; omega)]
  rw [x1]
  have O1 : OF M₀ ⟨runPrims [.const oX (toWord (piSizeOf seq4))] s.M, s.o.push (toWord (piSizeOf seq4))⟩ :=
    of_mk (of_loK I (P := .blk [.const oX (toWord (piSizeOf seq4))]) (by simp [LoK, Prim.dst, oX, regs])
      (by simp [WF, Prim.dst, oX]) hO) _
  have o1 : (⟨runPrims [.const oX (toWord (piSizeOf seq4))] s.M, s.o.push (toWord (piSizeOf seq4))⟩ : St).o =
    s.o.push (toWord (piSizeOf seq4)) := rfl
  generalize (⟨runPrims [.const oX (toWord (piSizeOf seq4))] s.M, s.o.push (toWord (piSizeOf seq4))⟩ : St) = s1 at O1 o1
  have hs1 := O1.inv.1
  simp only [regs] at hs1
  rw [semXIR_seq, prevRegs, semXIR_blk]
  set ps : List Prim := [.const qCB (toWord (8 * N4c.chBase κ 0)), .const qJ (toWord (N4c.cLen - 1)), .const qDl 0,
    .const qI 0] with hps
  have v : rd (runPrims ps s1.M) qI = toWord 0 ∧ rd (runPrims ps s1.M) qCB = toWord (8 * N4c.chBase κ 0) ∧
      rd (runPrims ps s1.M) qJ = toWord (N4c.cLen - 1) ∧ rd (runPrims ps s1.M) qDl = toWord 0 := by
    simp only [hps, runPrims, List.foldl, Prim.run]
    simp (disch := (simp only [size_set, qCB, qJ, qDl, qI] at *; omega)) only [rd_set_self, rd_set_ne]
    refine ⟨?_, ?_, ?_, ?_⟩ <;> first | exact True.intro | rfl
  have O2 : OF M₀ ⟨runPrims ps s1.M, s1.o⟩ := of_loK I (P := .blk ps)
    (by simp [hps, LoK, Prim.dst, regs, qCB, qJ, qDl, qI]) (by simp [hps, WF, Prim.dst, qCB, qJ, qDl, qI]) O1
  rw [semXIR_seq]
  obtain ⟨O3, o3, hV⟩ := rl_vS I κ (σ := 0) (k := 0) (i := 0) (w := w) O2 hsz hH (chR_prev κ hκ) (by norm_num)
    (by simp) (by simp [N4c.streamB, N4c.isAgg, hκ]) v.1 v.2.1 v.2.2.1 v.2.2.2
  generalize semXIR I (realign κ) ⟨runPrims ps s1.M, s1.o⟩ = s3 at O3 o3 hV
  rw [semXIR_seq]
  obtain ⟨o4, O4, h4⟩ := pfIR_sem I O3
  generalize semXIR I pfIR s3 = s4 at o4 O4 h4
  rw [semXIR_seq]
  obtain ⟨o5, O5, h5⟩ := bufSeg_sem I (trSeg4 seq4) okSeg_tr.1 (le_trans okSeg_tr.2.1 (by norm_num)) O4
  generalize semXIR I (bufSeg (trSeg4 seq4)) s4 = s5 at o5 O5 h5
  have hf := wb_fit κ (σ := 0) (by norm_num)
  obtain ⟨o6, O6⟩ := sigIR_sem I κ 0 O5 hf.2 (fun m hm => hAddr_lt' (by omega))
  refine ⟨?_, O6⟩
  rw [o6, o5, o4, src_congr h4, sigL_eq κ (by norm_num) hH, signedWords_prev κ hκ w (src s3.M apB bufB) hV]
  rw [o3]
  simp only [o1, Array.toList_push, List.append_assoc, List.cons_append, List.singleton_append, List.nil_append]

end FR.X
