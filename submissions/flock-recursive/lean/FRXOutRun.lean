-- New for `flock-recursive` (BLUEPRINT §6.2 step 5, §6.5 `output_spec`; stage S-H2, track L-ext,
-- S-H2l).
import FRXOut

/-!
# The node output program `outIR`

After the decode, `f⁽⁰⁾`'s rows are at `ob0 = 2^24` (row `r`, coefficient `x` at
`ob0 + 2^18 r + 2x`). Element `e` of the committed witness is row `e mod 64`, coefficient
`⌊e/64⌋` (`fF`, A.10), so

* stream word `u` of slot `σ` (`streamWord`) is at `baseS σ + 2^18·((u/2) mod 4) + 4·⌊u/8⌋ +
  u mod 2` (`apS`), from `streamCell σ (u/2) = ((σ−1)·chainLen + ⌊u/8⌋)·128 + 4 + (u/2) mod 4`;
* L word `v` of slot `σ` (`lWord`) is at `baseL σ + 2^18·((v/2) mod 64) + 2·⌊v/128⌋ + v mod 2`
  (`apL`), from `lCell σ k = lBlk·128 + (σ−1)·2^14 + k`.

`outIR` emits the tag `1`, both statements (stream words 6–9), then per slot the kind flag
(`kflag` of stream word 10), `slotSeg` over the stream and `sigSeg` over L.

**`outIR_out`**: from a state whose heap holds `w` at `ob0` (`hF`), `outIR` appends
`witWords (readWit w)` to the output. `cost_outIR`, `outs_outIR`, `sizeIR_outIR` are exact.
-/

namespace FR.X

open RecursionFast FR.Read

attribute [local irreducible] entryK storeM runPrims

/-! ## Specification -/

/-- The stream words' address shape. -/
def apS : AP := ⟨3, 3, 2, 18⟩

/-- The L words' address shape. -/
def apL : AP := ⟨63, 7, 1, 18⟩

/-- Slot `σ`'s stream base: `ob0 + 4·2^18 + 4·(σ − 1)·chainLen`. -/
def baseS (σ : ℕ) : ℕ := 16777216 + 1048576 + 4 * ((σ - 1) * 23146)

/-- Slot `σ`'s L base: `ob0 + 2·(2·lBlk + (σ − 1)·256)`. -/
def baseL (σ : ℕ) : ℕ := 16777216 + 2 * (2 * 47616 + (σ - 1) * 256)

/-- Set the source base. -/
def setR (R : ℕ) : XIR := .blk [.const oR (toWord R)]

/-- **The kind flag** from stream word 10: its low byte is `'N'` or `'P'`. -/
def kflagIR : XIR :=
  .seq (.blk [.const oU (toWord 10)]) (.seq (ldw apS)
    (.blk [.const oK (toWord 255), .op .and oX oX oK, .const oK (toWord 0x4E), .op .eq oT1 oX oK,
      .const oK (toWord 0x50), .op .eq oT2 oX oK, .op .or oKF oT1 oT2]))

/-- **One slot**: the kind flag, `slotSeg` over the stream, `sigSeg` over L. -/
def slotIR (σ : ℕ) : XIR :=
  .seq (setR (baseS σ)) (.seq kflagIR (.seq (segIR apS 0 slotSeg)
    (.seq (setR (baseL σ)) (.seq (.blk [.const oKF 0]) (segIR apL 0 sigSeg)))))

/-- **The node output program**: the tag, the statements, the two slots. -/
def outIR : XIR :=
  .seq (.blk [.const (oBd 0) 0, .const oKF 0, .const oX 1]) (.seq (.out oX)
    (.seq (setR (baseS 1)) (.seq (segIR apS 0 (.cp 6 4)) (.seq (setR (baseS 2))
      (.seq (segIR apS 0 (.cp 6 4)) (.seq (slotIR 1) (slotIR 2)))))))

/-! ## The segments' side conditions, decided -/

theorem okSeg_slot : okSeg slotSeg = true ∧ depthSeg slotSeg ≤ 9 := by decide +kernel

theorem okSeg_sig : okSeg sigSeg = true ∧ depthSeg sigSeg ≤ 9 := by decide +kernel

/-- Without `loopT`, the cost does not depend on the tape length. -/
theorem cost_noLoopT : ∀ (P : XIR), NoLoopT P → ∀ t, cost P t = cost P 0
  | .blk _, _, _ | .load .., _, _ | .store .., _, _ | .input .., _, _ | .out _, _, _ => rfl
  | .seq p q, h, t => by simp only [cost, cost_noLoopT p h.1 t, cost_noLoopT q h.2 t]
  | .ite _ p q, h, t => by simp only [cost, cost_noLoopT p h.1 t, cost_noLoopT q h.2 t]
  | .loopK _ _ _ b, h, t => by simp only [cost, cost_noLoopT b h t]
  | .loopT .., h, _ => h.elim

theorem outs_noLoopT : ∀ (P : XIR), NoLoopT P → ∀ t, outs P t = outs P 0
  | .blk _, _, _ | .load .., _, _ | .store .., _, _ | .input .., _, _ | .out _, _, _ => rfl
  | .seq p q, h, t => by simp only [outs, outs_noLoopT p h.1 t, outs_noLoopT q h.2 t]
  | .ite _ p q, h, t => by simp only [outs, outs_noLoopT p h.1 t, outs_noLoopT q h.2 t]
  | .loopK _ _ _ b, h, t => by simp only [outs, outs_noLoopT b h t]
  | .loopT .., h, _ => h.elim

theorem noLoopT_outIR : NoLoopT outIR := by
  simp [outIR, slotIR, setR, kflagIR, NoLoopT, ldw, noLoopT_segIR]


/-! ## Exact costs -/

theorem cost_outIR (t : ℕ) : cost outIR t = 21609039 := by
  rw [cost_noLoopT _ noLoopT_outIR t]; decide +kernel

theorem outs_outIR (t : ℕ) : outs outIR t = 571019 := by
  rw [outs_noLoopT _ noLoopT_outIR t]; decide +kernel

theorem sizeIR_outIR : sizeIR outIR = 22421 := by decide +kernel

theorem wf_kflagIR : WF kflagIR :=
  ⟨by simp [WF, Prim.dst, oU], wf_ldw apS, by simp [WF, Prim.dst, oK, oX, oT1, oT2, oKF]⟩

theorem wf_outIR : WF outIR := by
  have h1 := wf_segIR apS slotSeg 0 (by have := okSeg_slot.2; omega)
  have h2 := wf_segIR apL sigSeg 0 (by have := okSeg_sig.2; omega)
  have h3 := wf_segIR apS (.cp 6 4) 0 (by simp [depthSeg])
  simp only [outIR, slotIR, setR, WF]
  refine ⟨by simp [Prim.dst, oBd, oKF, oX], trivial, by simp [Prim.dst, oR], h3, by simp [Prim.dst, oR], h3,
    ⟨by simp [Prim.dst, oR], wf_kflagIR, h1, by simp [Prim.dst, oR], by simp [Prim.dst, oKF], h2⟩,
    ⟨by simp [Prim.dst, oR], wf_kflagIR, h1, by simp [Prim.dst, oR], by simp [Prim.dst, oKF], h2⟩⟩

/-! ## Proof helpers: the addresses -/

theorem and_mask_toWord {a k : ℕ} (ha : a < 2 ^ 64) (hk : k ≤ 64) :
    XOp.and.eval (toWord a) (toWord (2 ^ k - 1)) = toWord (a % 2 ^ k) := by
  apply BitVec.eq_of_toNat_eq
  simp only [XOp.eval]
  rw [BitVec.toNat_and, toNat_toWord ha, toNat_toWord (by have := Nat.pow_le_pow_right (by norm_num : 0 < 2) hk; omega),
    Nat.and_two_pow_sub_one_eq_mod, toNat_toWord (lt_of_le_of_lt (Nat.mod_le _ _) ha)]

/-- **A stream word's address** (`apS`). -/
theorem addrS_toNat {R u : ℕ} (hR : R < 2 ^ 62) (hu : u < 2 ^ 64) :
    (addrW apS (toWord R) (toWord u)).toNat = R + u / 2 % 4 * 2 ^ 18 + u / 8 * 4 + u % 2 := by
  simp only [addrW, apS]
  rw [shr_toWord hu (by norm_num), show (3 : ℕ) = 2 ^ 2 - 1 from rfl,
    and_mask_toWord (lt_of_le_of_lt (Nat.div_le_self _ _) hu) (by norm_num),
    shl_toWord (by norm_num) (by omega), shr_toWord hu (by norm_num),
    shl_toWord (by norm_num) (by omega), and_one_toWord hu, add_toWord, add_toWord, add_toWord,
    toNat_toWord (by omega)]
  norm_num

/-- **An L word's address** (`apL`). -/
theorem addrL_toNat {R v : ℕ} (hR : R < 2 ^ 62) (hv : v < 2 ^ 64) :
    (addrW apL (toWord R) (toWord v)).toNat = R + v / 2 % 64 * 2 ^ 18 + v / 128 * 2 + v % 2 := by
  simp only [addrW, apL]
  rw [shr_toWord hv (by norm_num), show (63 : ℕ) = 2 ^ 6 - 1 from rfl,
    and_mask_toWord (lt_of_le_of_lt (Nat.div_le_self _ _) hv) (by norm_num),
    shl_toWord (by norm_num) (by omega), shr_toWord hv (by norm_num),
    shl_toWord (by norm_num) (by omega), and_one_toWord hv, add_toWord, add_toWord, add_toWord,
    toNat_toWord (by omega)]
  norm_num

theorem hA_S {R : ℕ} (h1 : regs ≤ R) (hR : R < 2 ^ 62) (x : Word) : regs ≤ (addrW apS (toWord R) x).toNat := by
  have := addrS_toNat hR x.isLt
  rw [show toWord x.toNat = x by simp [toWord]] at this
  omega

theorem hA_L {R : ℕ} (h1 : regs ≤ R) (hR : R < 2 ^ 62) (x : Word) : regs ≤ (addrW apL (toWord R) x).toNat := by
  have := addrL_toNat hR x.isLt
  rw [show toWord x.toNat = x by simp [toWord]] at this
  omega

theorem elemWords_rdF (M : Mem) (a : ℕ) : elemWords (rdF M a) = [rd M a, rd M (a + 1)] := rfl

/-- **The stream words are the sources** at `baseS σ` (slots 1, 2). -/
theorem src_stream {M : Mem} {w : ℕ → F}
    (hF : ∀ e < 2 ^ 23, rdF M (16777216 + 2 ^ 18 * (e % 64) + 2 * (e / 64)) = w e)
    {σ : ℕ} (hσ : σ = 1 ∨ σ = 2) {u : ℕ} (hu : u < 185168) :
    src M apS (baseS σ) u = streamWord w σ u := by
  have hb : baseS σ < 2 ^ 62 := by rcases hσ with rfl | rfl <;> simp [baseS]
  have he : streamCell σ (u / 2) < 2 ^ 23 := by
    rcases hσ with rfl | rfl <;> simp only [streamCell, chainLen_eq] <;> omega
  rw [src, addrS_toNat hb (by omega), streamWord, ← hF _ he, elemWords_rdF]
  have e1 : streamCell σ (u / 2) % 64 = 4 + u / 2 % 4 := by
    rcases hσ with rfl | rfl <;> simp only [streamCell, chainLen_eq] <;> omega
  have e2 : streamCell σ (u / 2) / 64 = 2 * ((σ - 1) * 23146 + u / 8) := by
    rcases hσ with rfl | rfl <;> simp only [streamCell, chainLen_eq] <;> omega
  rw [e1, e2]
  rcases Nat.mod_two_eq_zero_or_one u with h | h <;> rw [h] <;> simp only [List.getD_cons_zero,
    List.getD_cons_succ] <;> congr 1 <;> simp only [baseS] <;> ring_nf <;> omega

/-- **The L words are the sources** at `baseL σ` (slots 1, 2). -/
theorem src_l {M : Mem} {w : ℕ → F}
    (hF : ∀ e < 2 ^ 23, rdF M (16777216 + 2 ^ 18 * (e % 64) + 2 * (e / 64)) = w e)
    {σ : ℕ} (hσ : σ = 1 ∨ σ = 2) {v : ℕ} (hv : v < 598) :
    src M apL (baseL σ) v = lWord w σ v := by
  have hb : baseL σ < 2 ^ 62 := by rcases hσ with rfl | rfl <;> simp [baseL]
  have he : lCell σ (v / 2) < 2 ^ 23 := by
    rcases hσ with rfl | rfl <;> simp only [lCell, lBlk] <;> omega
  rw [src, addrL_toNat hb (by omega), lWord, ← hF _ he, elemWords_rdF]
  have e1 : lCell σ (v / 2) % 64 = v / 2 % 64 := by
    rcases hσ with rfl | rfl <;> simp only [lCell, lBlk] <;> omega
  have e2 : lCell σ (v / 2) / 64 = 2 * 47616 + (σ - 1) * 256 + v / 128 := by
    rcases hσ with rfl | rfl <;> simp only [lCell, lBlk] <;> omega
  rw [e1, e2]
  rcases Nat.mod_two_eq_zero_or_one v with h | h <;> rw [h] <;> simp only [List.getD_cons_zero,
    List.getD_cons_succ] <;> congr 1 <;> simp only [baseL] <;> ring_nf <;> omega

/-! ## Proof helpers: the steps of `outIR` -/

/-- The part of the context that does not name `R` or the flag. -/
def Base (M₀ : Mem) (s : St) : Prop :=
  Inv s.M ∧ s.M.size = M₀.size ∧ (∀ y, regs ≤ y → rd s.M y = rd M₀ y) ∧ rd s.M (oBd 0) = toWord 0

theorem base_blk {M₀ : Mem} {ps : List Prim} (h : ∀ p ∈ ps, 4 ≤ p.dst ∧ p.dst < regs ∧ p.dst ≠ oBd 0)
    {s : St} (hb : Base M₀ s) : Base M₀ ⟨runPrims ps s.M, s.o⟩ :=
  ⟨inv_runPrims (fun p hp => (h p hp).1) hb.1, (size_runPrims _ _).trans hb.2.1,
    fun y hy => (rd_runPrims_of_not_writes (fun p hp he => by have := (h p hp).2.1; omega) _).trans (hb.2.2.1 y hy),
    (rd_runPrims_of_not_writes (fun p hp => (h p hp).2.2) _).trans hb.2.2.2⟩

theorem ctx_of_base {M₀ : Mem} {R : ℕ} {κ : Bool} {s : St} (hb : Base M₀ s) (hr : rd s.M oR = toWord R)
    (hk : rd s.M oKF = 0 ↔ κ = false) : Ctx M₀ R κ s := ⟨hb.1, hb.2.1, hb.2.2.1, hr, hk⟩

/-- A segment step: its words, and the base kept. -/
theorem seg_step (I : Array Word) (ap : AP) {M₀ : Mem} {R : ℕ} {κ : Bool}
    (hA : ∀ x, regs ≤ (addrW ap (toWord R) x).toNat) (seg : Seg) (hok : okSeg seg = true)
    (hd : depthSeg seg ≤ 9) {s : St} (hc : Ctx M₀ R κ s) (hb : rd s.M (oBd 0) = toWord 0) :
    (semXIR I (segIR ap 0 seg) s).o.toList = s.o.toList ++ segOut (src M₀ ap R) κ 0 seg ∧
      Ctx M₀ R κ (semXIR I (segIR ap 0 seg) s) ∧ Base M₀ (semXIR I (segIR ap 0 seg) s) := by
  have c := ctx_segIR I ap seg 0 (by omega) hc
  refine ⟨segIR_sem I ap hA seg 0 0 s hok (by omega) hc hb, c, c.inv, c.size, c.heap, ?_⟩
  exact (frame I _ s (wf_segIR ap seg 0 (by omega)) hc.inv _ (by simp [oBd, regs])
    (noW_segIR ap seg 0 _ (.inr (.inr (.inr rfl))))).trans hb

theorem kflag_step (I : Array Word) {M₀ : Mem} {R : ℕ} {κ : Bool}
    (hA : ∀ x, regs ≤ (addrW apS (toWord R) x).toNat) {s : St} (hc : Ctx M₀ R κ s) (hb : Base M₀ s) :
    (semXIR I kflagIR s).o = s.o ∧ Ctx M₀ R (kflag (src M₀ apS R 10)) (semXIR I kflagIR s) ∧
      Base M₀ (semXIR I kflagIR s) := by
  have hs := hc.inv.1
  simp only [regs] at hs
  simp only [kflagIR, semXIR_seq, semXIR_blk]
  have c1 := ctx_blk (ps := [.const oU (toWord 10)]) (by simp [Prim.dst, oU, oR, oKF, regs]) hc
  have b1 := base_blk (ps := [.const oU (toWord 10)]) (by simp [Prim.dst, oU, oBd, regs]) hb
  have u1 : rd (runPrims [.const oU (toWord 10)] s.M) oU = toWord 10 := by
    simp only [runPrims, List.foldl, Prim.run]; rw [rd_set_self (by simp only [oU]; omega)]
  obtain ⟨l1, l2⟩ := ldw_src I apS hA _ c1 u1
  have c2 := ctx_ldw I apS c1
  have b2 : Base M₀ (semXIR I (ldw apS) ⟨runPrims [.const oU (toWord 10)] s.M, s.o⟩) :=
    ⟨c2.inv, c2.size, c2.heap, (ldw_keep I apS _ c1.inv (by simp [oBd, regs])
      (by simp [oBd, oK, oT1, oT2, oT3, oAd, oX])).trans b1.2.2.2⟩
  have r2 := c2.r
  generalize semXIR I (ldw apS) ⟨runPrims [.const oU (toWord 10)] s.M, s.o⟩ = s2 at l1 l2 c2 b2 r2
  have hs2 := c2.inv.1
  simp only [regs] at hs2
  refine ⟨l2, ctx_of_base (base_blk (by simp [Prim.dst, oK, oX, oT1, oT2, oKF, oBd, regs]) b2) ?_ ?_,
    base_blk (by simp [Prim.dst, oK, oX, oT1, oT2, oKF, oBd, regs]) b2⟩
  · rw [rd_runPrims_of_not_writes (by simp [Prim.dst, oK, oX, oT1, oT2, oKF, oR])]; exact r2
  · simp only [runPrims, List.foldl, Prim.run]
    simp (disch := (simp only [size_set, oK, oX, oT1, oT2, oKF] at *; omega)) only [rd_set_self, rd_set_ne]
    rw [l1]
    generalize src M₀ apS R 10 = x
    have e1 : (toWord 255 : Word) = 0xFF := rfl
    have e2 : (toWord 0x4E : Word) = 0x4E := rfl
    have e3 : (toWord 0x50 : Word) = 0x50 := rfl
    simp only [XOp.eval, e1, e2, e3, kflag]
    by_cases h1 : x &&& 0xFF = 0x4E <;> by_cases h2 : x &&& 0xFF = 0x50 <;> simp [h1, h2]

theorem setR_step (I : Array Word) {M₀ : Mem} (R : ℕ) {t : St} (hb : Base M₀ t) (hk : rd t.M oKF = 0) :
    Ctx M₀ R false (semXIR I (setR R) t) ∧ Base M₀ (semXIR I (setR R) t) ∧ (semXIR I (setR R) t).o = t.o := by
  rw [setR, semXIR_blk]
  have hb' := base_blk (ps := [.const oR (toWord R)]) (by simp [Prim.dst, oR, oBd, regs]) hb
  refine ⟨ctx_of_base hb' ?_ ?_, hb', rfl⟩
  · simp only [runPrims, List.foldl, Prim.run]; rw [rd_set_self (by have := hb.1.1; simp only [oR, regs] at *; omega)]
  · simp only [runPrims, List.foldl, Prim.run]; rw [rd_set_ne (by simp [oR, oKF]), hk]; simp

theorem sig_step (I : Array Word) {M₀ : Mem} {σ : ℕ} (hσ : σ = 1 ∨ σ = 2) {t : St} (hb : Base M₀ t) :
    (semXIR I (.seq (setR (baseL σ)) (.seq (.blk [.const oKF 0]) (segIR apL 0 sigSeg))) t).o.toList =
      t.o.toList ++ segOut (src M₀ apL (baseL σ)) false 0 sigSeg ∧
    Base M₀ (semXIR I (.seq (setR (baseL σ)) (.seq (.blk [.const oKF 0]) (segIR apL 0 sigSeg))) t) ∧
    rd (semXIR I (.seq (setR (baseL σ)) (.seq (.blk [.const oKF 0]) (segIR apL 0 sigSeg))) t).M oKF = 0 := by
  have aL := hA_L (R := baseL σ) (by rcases hσ with rfl | rfl <;> simp [baseL, regs])
    (by rcases hσ with rfl | rfl <;> simp [baseL])
  have hs := hb.1.1
  simp only [regs] at hs
  have e : semXIR I (.seq (setR (baseL σ)) (.seq (.blk [.const oKF 0]) (segIR apL 0 sigSeg))) t =
      semXIR I (segIR apL 0 sigSeg) ⟨runPrims [.const oR (toWord (baseL σ)), .const oKF 0] t.M, t.o⟩ :=
    by with_unfolding_all rfl
  rw [e]
  have hb5 := base_blk (ps := [.const oR (toWord (baseL σ)), .const oKF 0]) (by simp [Prim.dst, oKF, oR, oBd, regs]) hb
  have c5 : Ctx M₀ (baseL σ) false ⟨runPrims [.const oR (toWord (baseL σ)), .const oKF 0] t.M, t.o⟩ := by
    refine ctx_of_base hb5 ?_ ?_
    · simp only [runPrims, List.foldl, Prim.run]
      rw [rd_set_ne (by simp [oR, oKF]), rd_set_self (by simp only [oR]; omega)]
    · simp only [runPrims, List.foldl, Prim.run]
      rw [rd_set_self (by simp only [oKF, size_set]; omega)]; simp
  obtain ⟨o6, c6, b6⟩ := seg_step I apL aL sigSeg okSeg_sig.1 okSeg_sig.2 c5 hb5.2.2.2
  exact ⟨o6, b6, c6.k.2 rfl⟩

/-- **One slot's words**: `slotSeg` over the stream (kind flag from word 10), `sigSeg` over L. -/
theorem slot_step (I : Array Word) {M₀ : Mem} {σ : ℕ} (hσ : σ = 1 ∨ σ = 2) {t : St} (hb : Base M₀ t)
    (hk : rd t.M oKF = 0) :
    (semXIR I (slotIR σ) t).o.toList = t.o.toList ++
      (segOut (src M₀ apS (baseS σ)) (kflag (src M₀ apS (baseS σ) 10)) 0 slotSeg ++
        segOut (src M₀ apL (baseL σ)) false 0 sigSeg) ∧
      Base M₀ (semXIR I (slotIR σ) t) ∧ rd (semXIR I (slotIR σ) t).M oKF = 0 := by
  have aS := hA_S (R := baseS σ) (by rcases hσ with rfl | rfl <;> simp [baseS, regs])
    (by rcases hσ with rfl | rfl <;> simp [baseS])
  have aL := hA_L (R := baseL σ) (by rcases hσ with rfl | rfl <;> simp [baseL, regs])
    (by rcases hσ with rfl | rfl <;> simp [baseL])
  rw [slotIR, semXIR_seq]
  obtain ⟨c1, b1, o1⟩ := setR_step I (baseS σ) hb hk
  generalize semXIR I (setR (baseS σ)) t = t1 at c1 b1 o1
  rw [semXIR_seq]
  obtain ⟨o2, c2, b2⟩ := kflag_step I aS c1 b1
  generalize semXIR I kflagIR t1 = t2 at o2 c2 b2
  rw [semXIR_seq]
  obtain ⟨o3, c3, b3⟩ := seg_step I apS aS slotSeg okSeg_slot.1 okSeg_slot.2 c2 b2.2.2.2
  generalize semXIR I (segIR apS 0 slotSeg) t2 = t3 at o3 c3 b3
  obtain ⟨o4, b4, k4⟩ := sig_step I hσ b3
  refine ⟨?_, b4, k4⟩
  rw [o4, o3, o2, o1, List.append_assoc]

/-- **The node output**: from a heap holding the committed witness `w` at `ob0` (row
`e mod 64`, coefficient `⌊e/64⌋`), `outIR` appends `witWords (readWit w)`. -/
theorem outIR_out (I : Array Word) (w : ℕ → F) (s : St) (hM : Inv s.M)
    (hF : ∀ e < 2 ^ 23, rdF s.M (16777216 + 2 ^ 18 * (e % 64) + 2 * (e / 64)) = w e) :
    (semXIR I outIR s).o.toList = s.o.toList ++ witWords (readWit w) := by
  have hs := hM.1
  simp only [regs] at hs
  rw [witWords_readWit w _ _ _ _ (fun u hu => src_stream hF (.inl rfl) hu) (fun u hu => src_stream hF (.inr rfl) hu)
    (fun v hv => src_l hF (.inl rfl) hv) (fun v hv => src_l hF (.inr rfl) hv)]
  have aS : ∀ σ, σ = 1 ∨ σ = 2 → ∀ x, regs ≤ (addrW apS (toWord (baseS σ)) x).toNat := fun σ hσ =>
    hA_S (by rcases hσ with rfl | rfl <;> simp [baseS, regs]) (by rcases hσ with rfl | rfl <;> simp [baseS])
  generalize hM₀ : s.M = M₀
  rw [outIR, semXIR_seq, semXIR_blk]
  have b0 : Base M₀ ⟨runPrims [.const (oBd 0) 0, .const oKF 0, .const oX 1] s.M, s.o⟩ := by
    refine ⟨inv_runPrims (by simp [Prim.dst, oBd, oKF, oX]) hM, by simp [hM₀], fun y hy => ?_, ?_⟩
    · rw [rd_runPrims_of_not_writes (by simp only [regs] at hy; simp [Prim.dst, oBd, oKF, oX]; omega), hM₀]
    · simp only [runPrims, List.foldl, Prim.run]
      simp (disch := (simp only [size_set, oBd, oKF, oX] at *; omega)) only [rd_set_self, rd_set_ne]; rfl
  have k0 : rd (runPrims [.const (oBd 0) 0, .const oKF 0, .const oX 1] s.M) oKF = 0 := by
    simp only [runPrims, List.foldl, Prim.run]
    simp (disch := (simp only [size_set, oBd, oKF, oX] at *; omega)) only [rd_set_self, rd_set_ne]
  have x0 : rd (runPrims [.const (oBd 0) 0, .const oKF 0, .const oX 1] s.M) oX = toWord 1 := by
    simp only [runPrims, List.foldl, Prim.run]
    simp (disch := (simp only [size_set, oBd, oKF, oX] at *; omega)) only [rd_set_self, rd_set_ne]; rfl
  generalize runPrims [.const (oBd 0) 0, .const oKF 0, .const oX 1] s.M = M1 at b0 k0 x0
  rw [semXIR_seq, show semXIR I (.out oX) ⟨M1, s.o⟩ = ⟨M1, s.o.push (rd M1 oX)⟩ from rfl, x0]
  have b1 : Base M₀ ⟨M1, s.o.push (toWord 1)⟩ := b0
  have k1 : rd (⟨M1, s.o.push (toWord 1)⟩ : St).M oKF = 0 := k0
  have o1 : (⟨M1, s.o.push (toWord 1)⟩ : St).o.toList = s.o.toList ++ [toWord 1] := by simp
  generalize (⟨M1, s.o.push (toWord 1)⟩ : St) = t1 at b1 k1 o1
  rw [semXIR_seq]
  obtain ⟨c2, b2, o2⟩ := setR_step I (baseS 1) b1 k1
  generalize semXIR I (setR (baseS 1)) t1 = t2 at c2 b2 o2
  rw [semXIR_seq]
  obtain ⟨o3, c3, b3⟩ := seg_step I apS (aS 1 (.inl rfl)) (.cp 6 4) rfl (by decide) c2 b2.2.2.2
  generalize semXIR I (segIR apS 0 (.cp 6 4)) t2 = t3 at o3 c3 b3
  rw [semXIR_seq]
  obtain ⟨c4, b4, o4⟩ := setR_step I (baseS 2) b3 (c3.k.2 rfl)
  generalize semXIR I (setR (baseS 2)) t3 = t4 at c4 b4 o4
  rw [semXIR_seq]
  obtain ⟨o5, c5, b5⟩ := seg_step I apS (aS 2 (.inr rfl)) (.cp 6 4) rfl (by decide) c4 b4.2.2.2
  generalize semXIR I (segIR apS 0 (.cp 6 4)) t4 = t5 at o5 c5 b5
  rw [semXIR_seq]
  obtain ⟨o6, b6, k6⟩ := slot_step I (σ := 1) (.inl rfl) b5 (c5.k.2 rfl)
  generalize semXIR I (slotIR 1) t5 = t6 at o6 b6 k6
  obtain ⟨o7, -, -⟩ := slot_step I (σ := 2) (.inr rfl) b6 k6
  rw [o7, o6, o5, o4, o3, o2, o1]
  simp only [List.append_assoc, List.cons_append, List.singleton_append, List.nil_append]

/-! ## Controls -/

namespace OutControls

/-- **The stream address** (`apS`): word 1 is the next cell, word 2 the next stream element
(the next row, `2^18` on), word 8 the next H block (4 cells on). -/
theorem addrS_ctl : (addrW apS (toWord 0) (toWord 1)).toNat = 1 ∧ (addrW apS (toWord 0) (toWord 2)).toNat = 2 ^ 18 ∧
    (addrW apS (toWord 0) (toWord 8)).toNat = 4 := by
  refine ⟨?_, ?_, ?_⟩ <;> rw [addrS_toNat (by norm_num) (by norm_num)] <;> norm_num

/-- **The L address** (`apL`): word 2 is the next L element (next row), word 128 the next 64
elements (2 cells on). -/
theorem addrL_ctl : (addrW apL (toWord 0) (toWord 2)).toNat = 2 ^ 18 ∧ (addrW apL (toWord 0) (toWord 128)).toNat = 2 := by
  refine ⟨?_, ?_⟩ <;> rw [addrL_toNat (by norm_num) (by norm_num)] <;> norm_num

/-- `okSeg` holds on the program's segments and fails on a count past `2^32` or `per = 0`. -/
theorem okSeg_ctl : okSeg FR.Read.slotSeg = true ∧ okSeg (.cp 0 (2 ^ 32)) = false ∧
    okSeg (.sib 0 0 0 0 0 0 0 0) = false := ⟨okSeg_slot.1, by decide, by decide⟩

/-- **`outIR_out`'s hypothesis is satisfiable on every heap**: the witness it emits is the one
read off the heap at `ob0`. -/
theorem outIR_any (I : Array Word) (s : St) (hM : Inv s.M) :
    (semXIR I outIR s).o.toList = s.o.toList ++
      witWords (FR.readWit fun e => rdF s.M (16777216 + 2 ^ 18 * (e % 64) + 2 * (e / 64))) :=
  outIR_out I _ s hM fun _ _ => rfl

/-- **The first word `outIR` emits is the node tag `1`**, so `decodeWit` reads a node. -/
theorem outIR_tag (I : Array Word) (s : St) (hM : Inv s.M) (hs : s.o = #[]) :
    (semXIR I outIR s).o.toList.head? = some (toWord 1) := by
  rw [outIR_any I s hM, hs, Array.toList_empty, List.nil_append]
  exact FR.Read.ReadControls.witWords_tag _

end OutControls

end FR.X
