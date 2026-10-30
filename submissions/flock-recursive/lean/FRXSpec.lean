-- G6: this module also holds the former modules `FRXOutRun`, `FRXNode`, `FRXExt` (one section each, in import order).
import FRXOut
import FRXDec4Front
import FRXDec
import FRXSearch

section G6_FRXOutRun

-- New for `flock-recursive` (BLUEPRINT §6.2 step 5, §6.5 `output_spec`; stage S-H2, track L-ext,
-- S-H2l).

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

end G6_FRXOutRun

section G6_FRXNode

-- New for `flock-recursive` (BLUEPRINT §6.2 steps 3–4, the five levels chained; stage S-H2,
-- track L-ext, S-H2j).

/-!
# The five levels chained

After the node branch's index, level 0's read and the chain replay, the decode runs

`wtabIR tb0 ; (readLv 4 ; decLvIR msg₄ 4) ; (readLv 3 ; decLvIR msg₃ 3) ; … ; decLvIR msg₀ 0`

(`decLevels`). Level `i + 1`'s decoded rows at `obL` feed level `i`'s message step (`msgHIR`);
level 4's message is π's final field (`msgTIR`).

* `readIR_frame`: the ladder read keeps the heap outside its store (from `posLoop`);
* `lvStep_sem`: one read-and-decode step of levels 1–4 on the memory map of `FRXDecLv`;
* **`decLevels_sem`**: level 0's rows at `ob0` are `msgOf 0` (`F`-valued), given the basis-table
  free heap, level 0's word at `colBase`, the chain's answers at `ansB`, the sorted index, the cap
  link `capDig = capPiL`, the final-message link `finalAt = finPi`, and per level `¬ farL` and
  `A_c = jointAgree`.
-/

namespace FR.X

open RecursionFast FR FR.Snd FR.Merkle

attribute [local irreducible] entryK storeM

/-! ## The read keeps the heap outside its store -/

section Pos

variable {c : Digest} {π : Proof} {L : Log} {i : ℕ}

/-- **The ladder read's frame** (`posLoop`'s): `readIR` keeps every heap cell outside
`[sb, sb + nw·np)`. `readIR_sem` states the store and the index. -/
theorem readIR_frame (hD : Dom c π L) {Xi : ℕ → Word} (hX : Sorted (tp c π L) L Xi) (s : St)
    (hM : Inv s.M) (hXs : ∀ a < L.length, rd s.M (memX + a) = Xi a) {cw nw ncap sb : ℕ}
    {cap : ℕ → Digest} (hcw : cw + 4 * ncap < 2 ^ 62)
    (hcap : ∀ e < ncap, ∀ m < 4,
      (tp c π L).getD (cw + 4 * e + m) 0 = (packBytes (cap e).toList).getD m 0)
    (hnw : nw < 2 ^ 60) {sib np : ℕ}
    (hsib : sib < 64) (hnp : np ≤ 2 ^ 20) (hst : sb + nw * np ≤ memX) (hsb : regs ≤ sb)
    (hcapn : np ≤ ncap * 2 ^ sib) (hsz : memX ≤ s.M.size) :
    ∀ y, regs ≤ y → (y < sb ∨ sb + nw * np ≤ y) →
      rd (semXIR (tp c π L) (readIR i cw sb nw sib np) s).M y = rd s.M y :=
  readIR4_frame (bX := memX) (pL := posL) (by decide) (by decide) (by decide) hD.d4 hX s hM hXs hcw
    hcap hnw hsib hnp hst hsb hcapn hsz

end Pos

variable {c : Digest} {π : Proof} {L : Log}

/-- **The read of level `i ∈ [1, 4]` keeps the heap** outside `[stB, stB + 32·2^logNL i)`. -/
theorem readLv_frame (hD : Dom c π L) {Xi : ℕ → Word} (hX : Sorted (tp c π L) L Xi) (s : St)
    (hM : Inv s.M) (hXs : ∀ a < L.length, rd s.M (memX + a) = Xi a) (hsz : memX ≤ s.M.size)
    {i : ℕ} (hi1 : 1 ≤ i) (hi : i ≤ 4) :
    ∀ y, regs ≤ y → (y < stB ∨ stB + 32 * 2 ^ logNL i ≤ y) →
      rd (semXIR (tp c π L) (readLv i) s).M y = rd s.M y := by
  have hps : π.size = 797904 := hD.hs.trans piSize_eq
  have hfit := capOffL_fit hi
  have hlog := capLogL_le i
  have hoff := capOffL_le i
  have hmod := capOffL_mod i
  have hcl : 2 ^ capLogL i ≤ 2 ^ 9 := Nat.pow_le_pow_right (by norm_num) hlog
  have hnp : 2 ^ logNL i ≤ 2 ^ 16 := Nat.pow_le_pow_right (by norm_num) (by unfold logNL; omega)
  have hcapn : 2 ^ logNL i ≤ 2 ^ capLogL i * 2 ^ sibL i := by
    rw [← Nat.pow_add]; refine Nat.pow_le_pow_right (by norm_num) ?_
    unfold sibL logNL capLogL; split_ifs <;> omega
  have hsib : sibL i < 64 := by unfold sibL logNL; omega
  exact readIR_frame hD hX s hM hXs (i := i) (cw := capWL i) (nw := 32) (ncap := 2 ^ capLogL i)
    (sb := stB) (cap := capPiL i π) (by unfold capWL; omega)
    (fun e he m hm => by
      simp only [tp, getD_toArray]
      exact tape_capL c π L hmod (by
        have : 32 * e + 32 ≤ 32 * 2 ^ capLogL i := by omega
        omega) hm)
    (by norm_num) hsib (by omega) (by simp only [stB, memX]; omega)
    (by simp only [regs, stB]; omega) hcapn hsz

/-! ## The level parameters -/

theorem lvl_logN {i : ℕ} (hi1 : 1 ≤ i) (hi : i ≤ 4) : (lvl .N30 i).logN = logNL i := by
  interval_cases i <;> rfl

theorem lvl_sib {i : ℕ} (hi1 : 1 ≤ i) (hi : i ≤ 4) : (lvl .N30 i).sib = sibL i := by
  interval_cases i <;> rfl

theorem lvl_rows {i : ℕ} (hi1 : 1 ≤ i) (hi : i ≤ 4) : (lvl .N30 i).rows = 16 := by
  interval_cases i <;> rfl

/-- P1.i's answers are chain positions below `nRep`. -/
theorem p1_lt_nRep {i v : ℕ} (hi : i < 5) (hv : v < (lvl .N30 i).ell) :
    phStart (26 + 5 * i) + 2 * v + 1 < nRep := by
  have : phStart (26 + 5 * i) + 2 * (lvl .N30 i).ell ≤ nRep := by
    unfold phStart; rw [fsStarts_eq]; interval_cases i <;> decide
  omega

/-- **The read is the committed word** of level `i ∈ [1, 4]` when the caps π carries are the
log's (`capDig es i = capPiL i π`, the C phases' absorbs). -/
theorem readLv_wordOf (hD : Dom c π L) {Xi : ℕ → Word} (hX : Sorted (tp c π L) L Xi) (s : St)
    (hM : Inv s.M) (hXs : ∀ a < L.length, rd s.M (memX + a) = Xi a) (hsz : memX ≤ s.M.size)
    {es : Log} {i : ℕ} (hi1 : 1 ≤ i) (hi : i ≤ 4)
    (hcap : ∀ e < 2 ^ capLogL i, capDig es i e = capPiL i π e) :
    ∀ j (hj : j < 2 ^ (lvl .N30 i).logN) (r : Fin (lvl .N30 i).rows),
      rdF (semXIR (tp c π L) (readLv i) s).M (stB + 32 * j + 2 * r) =
        wordOf .N30 L es i r ⟨j, hj⟩ := by
  intro j hj r
  have hR := lvl_rows hi1 hi
  have hr : (r : ℕ) < 16 := hR ▸ r.2
  rw [lvl_logN hi1 hi] at hj
  rw [readLv_spec_F hD hX s hM hXs hsz hi1 hi hj hr, wordOf, colOf, lvl_sib hi1 hi]
  have hcl : capLogL i = (lvl .N30 i).cap := by interval_cases i <;> rfl
  have hq : j / 2 ^ sibL i < 2 ^ capLogL i := by
    rw [Nat.div_lt_iff_lt_mul (by positivity), ← Nat.pow_add]
    refine lt_of_lt_of_le hj (Nat.pow_le_pow_right (by norm_num) ?_)
    unfold sibL logNL capLogL; split_ifs <;> omega
  rw [hcap _ hq]
  rfl

/-! ## The message steps, from a heap that agrees below `2^24` -/

/-- The `eq` table of level `i` keeps the heap outside `[eqB, eqB + 256)`. -/
theorem eqt_keep (I : Array Word) (s : St) (hM : Inv s.M) (hsz : memX ≤ s.M.size) {i : ℕ}
    (hi : i < 5) :
    Inv (semXIR I (eqtIR (lvl .N30 i).ell (cbS i) eqB) s).M ∧
    ∀ y, regs ≤ y → (y < eqB ∨ eqB + 256 ≤ y) →
      rd (semXIR I (eqtIR (lvl .N30 i).ell (cbS i) eqB) s).M y = rd s.M y := by
  have hl : (lvl .N30 i).ell ≤ 6 := by interval_cases i <;> decide
  have hp : 2 ^ (lvl .N30 i).ell ≤ 2 ^ 6 := Nat.pow_le_pow_right (by norm_num) hl
  obtain ⟨c1, c2⟩ := cbS_le hi
  have eq : eqB = 8421376 := rfl
  have hm : memX = 67108864 := rfl
  obtain ⟨-, h2, h3⟩ := eqtIR_sem I s hM (ℓ := (lvl .N30 i).ell) (cb := cbS i) (eb := eqB)
    (S := fun v => rdK s.M (cbS i + 8 * v)) (by omega) c1 (by omega) (by simp only [regs]; omega)
    (by omega) (by omega) (.inl c2) (fun _ _ => rfl)
  exact ⟨h3, fun y hy hy2 => h2 y hy (hy2.imp_right fun h => le_trans (by omega) h)⟩

/-- The message step of levels `0 … 3`. -/
def lvMsg (i : ℕ) : XIR := msgHIR (lvl .N30 i).logN (2 ^ mLog .N30 (i + 1)) obL xbM ybM

/-- The message step of level 4: π's final field. -/
def msg4 : XIR := msgTIR 10 32 finW xbM ybM

/-- `MsgOk` for level 4 from every state of the same size (`msgOk_four`). -/
theorem msg4_keep (c : Digest) (π : Proof) (L es : Log) (hs : π.size = piSize)
    (hfin : ∀ x < 32, finalAt es x = finPi π x) (s : St) (hsz : memX ≤ s.M.size) :
    ∀ s' : St, Inv s'.M → s'.M.size = s.M.size →
      MsgOk (tp c π L) msg4 s' (lvl .N30 4).logN (mLog .N30 4) (nextMsg .N30 L es 4) :=
  fun s' _ hz => msgOk_four c π L es hs hfin s' (hz ▸ hsz)

/-- `MsgOk` for level `i < 4` from every state that agrees below `2^24`, outside the `eq` table,
with one holding level `i + 1`'s decoded rows at `obL` (`msgOk_lower`). -/
theorem lvMsg_keep {L es : Log} {i : ℕ} (hi : i < 4) (I : Array Word) (s : St)
    (hsz : memX ≤ s.M.size)
    (hdec : ∀ r < (lvl .N30 (i + 1)).rows, ∀ x < 2 ^ mLog .N30 (i + 1),
      algebraMap F K (rdF s.M (obL + 2 * 2 ^ mLog .N30 (i + 1) * r + 2 * x)) =
        msgOf .N30 L es (i + 1) r x)
    (hF : ∀ r x, msgOf .N30 L es (i + 1) r x = algebraMap F K (msgOf .N30 L es (i + 1) r x).f₀) :
    ∀ s' : St, Inv s'.M → s'.M.size = s.M.size →
      (∀ y, regs ≤ y → y < 2 ^ 24 → (y < eqB ∨ eqB + 256 ≤ y) → rd s'.M y = rd s.M y) →
      MsgOk I (lvMsg i) s' (lvl .N30 i).logN (mLog .N30 i) (nextMsg .N30 L es i) := by
  intro s' _ hz hag
  have hR : (lvl .N30 (i + 1)).rows = 16 := by interval_cases i <;> rfl
  have hm : mLog .N30 (i + 1) ≤ 14 := by interval_cases i <;> decide
  have hk : 2 ^ mLog .N30 (i + 1) ≤ 2 ^ 14 := Nat.pow_le_pow_right (by norm_num) hm
  have eob : obL = 6291456 := rfl
  have eqb : eqB = 8421376 := rfl
  refine msgOk_lower hi I s' (hz ▸ hsz) (fun r hr x hx => ?_) hF
  rw [← hdec r (hR ▸ hr) x hx]
  have : 2 * 2 ^ mLog .N30 (i + 1) * r ≤ 2 * 2 ^ 14 * 16 :=
    Nat.mul_le_mul (Nat.mul_le_mul_left 2 hk) hr.le
  congr 1
  exact rdF_eq (hag _ (by simp only [regs]; omega) (by omega) (.inl (by omega)))
    (hag _ (by simp only [regs]; omega) (by omega) (.inl (by omega)))

/-! ## One step of levels 1–4: the read, then the decode -/

/-- **Read and decode level `i`** (`1 ≤ i ≤ 4`): the word to `stB`, the rows to `obL`. -/
def stepU (msg : XIR) (i : ℕ) : XIR := .seq (readLv i) (decLvIR msg i 32 stB (cbS i) obL)

/-- The heap the chained decode keeps: below `jb0` (the basis table), the chain's region
`[chB, eqB)`, and from `2^25` on (level 0's word, the index). -/
def KeepR (y : ℕ) : Prop := y < jb0 ∨ (chB ≤ y ∧ y < eqB) ∨ 2 ^ 25 ≤ y

/-- **One step of levels 1–4**: from a state `s` that agrees with `s₀` on `KeepR`, where `s₀`
holds the basis table, the chain's answers and the sorted index, `stepU msg i` leaves level `i`'s
decoded rows `msgOf i` at `obL` and keeps `KeepR`. -/
theorem lvStep_sem (hD : Dom c π L) {Xi : ℕ → Word} (hX : Sorted (tp c π L) L Xi) (s₀ s : St)
    (hM : Inv s.M) (hsz : memX ≤ s.M.size)
    (hK : ∀ y, regs ≤ y → KeepR y → rd s.M y = rd s₀.M y)
    (hXs : ∀ a < L.length, rd s₀.M (memX + a) = Xi a)
    (hT : ∀ v < 20, ∀ i < 20, rdF s₀.M (tb0 + 40 * v + 2 * i) = (wRow D logNMax v).getD i 0)
    {es : Log}
    (hans : ∀ p < nRep, ∀ m < 4, rd s₀.M (ansB + 4 * p + m) = (packBytes (ansAt es p).toList).getD m 0)
    {i : ℕ} {msg : XIR} (hi1 : 1 ≤ i) (hi : i ≤ 4) (hfar : ¬ farL .N30 L es i)
    (hA : consSet .N30 L es i = jointAgree (wordK .N30 L es i) (decodeL .N30 L es i))
    (hcap : ∀ e < 2 ^ capLogL i, capDig es i e = capPiL i π e)
    (hmsg : ∀ s' : St, Inv s'.M → s'.M.size = s.M.size →
      (∀ y, regs ≤ y → y < 2 ^ 24 → (y < eqB ∨ eqB + 256 ≤ y) → rd s'.M y = rd s.M y) →
      MsgOk (tp c π L) msg s' (lvl .N30 i).logN (mLog .N30 i) (nextMsg .N30 L es i)) :
    (∀ r < (lvl .N30 i).rows, ∀ x < 2 ^ mLog .N30 i,
      algebraMap F K (rdF (semXIR (tp c π L) (stepU msg i) s).M
        (obL + 2 * 2 ^ mLog .N30 i * r + 2 * x)) = msgOf .N30 L es i r x) ∧
    (∀ y, regs ≤ y → KeepR y → rd (semXIR (tp c π L) (stepU msg i) s).M y = rd s.M y) ∧
    Inv (semXIR (tp c π L) (stepU msg i) s).M := by
  set I := tp c π L
  have hm : memX = 67108864 := rfl
  have ejb : jb0 = 2097152 := rfl
  have ech : chB = 8388608 := rfl
  have eqb : eqB = 8421376 := rfl
  have est : stB = 16777216 := rfl
  have eans : ansB = 8392704 := rfl
  have et : tb0 = 1048576 := rfl
  have hXs' : ∀ a < L.length, rd s.M (memX + a) = Xi a := fun a ha =>
    (hK _ (by simp only [regs]; omega) (.inr (.inr (by omega)))).trans (hXs a ha)
  have hW := readLv_wordOf hD hX s hM hXs' hsz hi1 hi hcap
  have fr := readLv_frame hD hX s hM hXs' hsz hi1 hi
  have hM1 := inv_sem I (wf_readLv i) hM
  have z1 := size_sem I (readLv i) s
  have hnp : 2 ^ logNL i ≤ 2 ^ 16 := Nat.pow_le_pow_right (by norm_num) (by unfold logNL; omega)
  rw [stepU, semXIR_seq]
  generalize semXIR I (readLv i) s = s1 at hW fr hM1 z1
  have hT1 : ∀ v < 20, ∀ i' < 20, rdF s1.M (tb0 + 40 * v + 2 * i') = (wRow D logNMax v).getD i' 0 :=
    fun v hv i' hi' => by
      rw [← hT v hv i' hi']
      exact rdF_eq ((fr _ (by simp only [regs]; omega) (.inl (by omega))).trans
          (hK _ (by simp only [regs]; omega) (.inl (by omega))))
        ((fr _ (by simp only [regs]; omega) (.inl (by omega))).trans
          (hK _ (by simp only [regs]; omega) (.inl (by omega))))
  have hS1 : ∀ v < (lvl .N30 i).ell, rdK s1.M (cbS i + 8 * v) = sAt es i v := by
    refine sAt_words fun v hv m hm4 => ?_
    have hp := p1_lt_nRep (by omega : i < 5) hv
    have hp' : phStart (26 + 5 * i) + 2 * v + 1 < 442 := hp
    rw [(fr _ (by simp only [regs]; omega) (.inl (by omega))).trans
      (hK _ (by simp only [regs]; omega) (.inr (.inl ⟨by omega, by omega⟩))), hans _ hp m hm4]
  obtain ⟨e1, e2⟩ := eqt_keep I s1 hM1 (by rw [z1]; exact hsz) (i := i) (by omega)
  have hmsg1 := hmsg _ e1 (by rw [size_sem, z1]) fun y hy h24 hq =>
    (e2 y hy hq).trans (fr y hy (.inl (by omega)))
  obtain ⟨b1, b2, b3⟩ := decLvU_sem I s1 hM1 hi1 hi hfar hA (by rw [z1]; exact hsz) hT1 hW hS1 hmsg1
  refine ⟨b1, fun y hy hy2 => ?_, b3⟩
  have hy3 : y < stB ∨ stB + 32 * 2 ^ logNL i ≤ y := by
    rcases hy2 with h | h | h
    · exact .inl (by omega)
    · exact .inl (by omega)
    · exact .inr (by omega)
  refine (b2 y hy ?_).trans (fr y hy hy3)
  rcases hy2 with h | h | h
  · exact .inl h
  · exact .inr (.inl h)
  · exact .inr (.inr (by omega))

/-- **Level 0's decode** (`decLv0_sem`) from a state agreeing with `s₀` on `KeepR`. -/
theorem lv0Step_sem (I : Array Word) (s₀ s : St) (hM : Inv s.M) (hsz : memX ≤ s.M.size)
    (hK : ∀ y, regs ≤ y → KeepR y → rd s.M y = rd s₀.M y)
    (hT : ∀ v < 20, ∀ i < 20, rdF s₀.M (tb0 + 40 * v + 2 * i) = (wRow D logNMax v).getD i 0)
    {L es : Log}
    (hans : ∀ p < nRep, ∀ m < 4, rd s₀.M (ansB + 4 * p + m) = (packBytes (ansAt es p).toList).getD m 0)
    (hW : ∀ j (hj : j < 2 ^ (lvl .N30 0).logN) (r : Fin (lvl .N30 0).rows),
      rdF s₀.M (colBase + 128 * j + 2 * r) = wordOf .N30 L es 0 r ⟨j, hj⟩)
    {msg : XIR} (hfar : ¬ farL .N30 L es 0)
    (hA : consSet .N30 L es 0 = jointAgree (wordK .N30 L es 0) (decodeL .N30 L es 0))
    (hmsg : ∀ s' : St, Inv s'.M → s'.M.size = s.M.size →
      (∀ y, regs ≤ y → y < 2 ^ 24 → (y < eqB ∨ eqB + 256 ≤ y) → rd s'.M y = rd s.M y) →
      MsgOk I msg s' (lvl .N30 0).logN (mLog .N30 0) (nextMsg .N30 L es 0)) :
    (∀ r < (lvl .N30 0).rows, ∀ x < 2 ^ mLog .N30 0,
      algebraMap F K (rdF (semXIR I (decLvIR msg 0 128 colBase (cbS 0) ob0) s).M
        (ob0 + 2 * 2 ^ mLog .N30 0 * r + 2 * x)) = msgOf .N30 L es 0 r x) ∧
    Inv (semXIR I (decLvIR msg 0 128 colBase (cbS 0) ob0) s).M := by
  have ejb : jb0 = 2097152 := rfl
  have ech : chB = 8388608 := rfl
  have eqb : eqB = 8421376 := rfl
  have eans : ansB = 8392704 := rfl
  have et : tb0 = 1048576 := rfl
  have ecb : colBase = 33554432 := rfl
  have hT1 : ∀ v < 20, ∀ i' < 20, rdF s.M (tb0 + 40 * v + 2 * i') = (wRow D logNMax v).getD i' 0 :=
    fun v hv i' hi' => by
      rw [← hT v hv i' hi']
      exact rdF_eq (hK _ (by simp only [regs]; omega) (.inl (by omega)))
        (hK _ (by simp only [regs]; omega) (.inl (by omega)))
  have hS1 : ∀ v < (lvl .N30 0).ell, rdK s.M (cbS 0 + 8 * v) = sAt es 0 v := by
    refine sAt_words fun v hv m hm4 => ?_
    have hp := p1_lt_nRep (by norm_num : 0 < 5) hv
    have hp' : phStart (26 + 5 * 0) + 2 * v + 1 < 442 := hp
    rw [hK _ (by simp only [regs]; omega) (.inr (.inl ⟨by omega, by omega⟩)), hans _ hp m hm4]
  have hW1 : ∀ j (hj : j < 2 ^ (lvl .N30 0).logN) (r : Fin (lvl .N30 0).rows),
      rdF s.M (colBase + 128 * j + 2 * r) = wordOf .N30 L es 0 r ⟨j, hj⟩ := fun j hj r => by
    rw [← hW j hj r]
    exact rdF_eq (hK _ (by simp only [regs]; omega) (.inr (.inr (by omega))))
      (hK _ (by simp only [regs]; omega) (.inr (.inr (by omega))))
  obtain ⟨e1, e2⟩ := eqt_keep I s hM hsz (i := 0) (by norm_num)
  have hmsg1 := hmsg _ e1 (by rw [size_sem]) fun y hy _ hq => e2 y hy hq
  obtain ⟨b1, -, b3⟩ := decLv0_sem I s hM hfar hA hsz hT1 hW1 hS1 hmsg1
  exact ⟨b1, b3⟩

/-! ## The five levels -/

theorem le_add3 (a b c : ℕ) : a ≤ a + b + c := by omega
theorem le_add4 (a b c d : ℕ) : a ≤ a + b + c + d := by omega


/-- **The decode of the five levels**: the basis table, then levels 4, 3, 2, 1 (read and decode),
then level 0 (its word read by `read0` at `colBase`), into `ob0`. -/
def decLevels : XIR :=
  .seq (wtabIR tb0) (.seq (stepU msg4 4) (.seq (stepU (lvMsg 3) 3) (.seq (stepU (lvMsg 2) 2)
    (.seq (stepU (lvMsg 1) 1) (decLvIR (lvMsg 0) 0 128 colBase (cbS 0) ob0)))))

/-- **The five levels decode** (BLUEPRINT §6.2 step 4, §6.5 `interp_spec`/`coeffs_spec`): on a
domain tape with the sorted index at `memX`, level 0's word at `colBase` (`read_spec_F`), the
chain's answers at `ansB` (`chain_dec`), and, as the log's transcript `es` provides them, the cap
link `capDig es i = capPiL i π` (levels 1–4), the final-message link `finalAt es = finPi π`, and
at every level a close word with `A_c = jointAgree`: level 0's decoded rows sit at `ob0` as the
`F` values of `msgOf 0` (`f⁽⁰⁾`, row `r` at `ob0 + 2^18 r`). -/
theorem decLevels_sem (hD : Dom c π L) {Xi : ℕ → Word} (hX : Sorted (tp c π L) L Xi) (s : St)
    (hM : Inv s.M) (hsz : memX ≤ s.M.size) (hXs : ∀ a < L.length, rd s.M (memX + a) = Xi a)
    {es : Log}
    (hW : ∀ j (hj : j < 2 ^ (lvl .N30 0).logN) (r : Fin (lvl .N30 0).rows),
      rdF s.M (colBase + 128 * j + 2 * r) = wordOf .N30 L es 0 r ⟨j, hj⟩)
    (hans : ∀ p < nRep, ∀ m < 4, rd s.M (ansB + 4 * p + m) = (packBytes (ansAt es p).toList).getD m 0)
    (hcap : ∀ i, 1 ≤ i → i ≤ 4 → ∀ e < 2 ^ capLogL i, capDig es i e = capPiL i π e)
    (hfin : ∀ x < 32, finalAt es x = finPi π x)
    (hfar : ∀ i < 5, ¬ farL .N30 L es i)
    (hA : ∀ i < 5, consSet .N30 L es i = jointAgree (wordK .N30 L es i) (decodeL .N30 L es i)) :
    (∀ r < (lvl .N30 0).rows, ∀ x < 2 ^ mLog .N30 0,
      algebraMap F K (rdF (semXIR (tp c π L) decLevels s).M (ob0 + 2 * 2 ^ mLog .N30 0 * r + 2 * x)) =
        msgOf .N30 L es 0 r x) ∧
    Inv (semXIR (tp c π L) decLevels s).M := by
  set I := tp c π L
  -- the basis table
  obtain ⟨t1, t2, t3, t4⟩ := wtabIR_sem I s hM (tb := tb0) (by decide) (by decide)
    (le_trans (by decide) hsz)
  rw [decLevels, semXIR_seq]
  generalize semXIR I (wtabIR tb0) s = s₀ at t1 t2 t3 t4
  have hsz0 : memX ≤ s₀.M.size := t4 ▸ hsz
  have hXs0 : ∀ a < L.length, rd s₀.M (memX + a) = Xi a := fun a ha =>
    (t2 _ (le_trans (by decide) (Nat.le_add_right _ _))
      (.inr (le_trans (by decide) (Nat.le_add_right _ _)))).trans (hXs a ha)
  have hans0 : ∀ p < nRep, ∀ m < 4, rd s₀.M (ansB + 4 * p + m) =
      (packBytes (ansAt es p).toList).getD m 0 := fun p hp m hm4 => by
    rw [t2 _ (le_trans (by decide) (le_add3 _ _ _))
      (.inr (le_trans (by decide) (le_add3 _ _ _))), hans p hp m hm4]
  have hW0 : ∀ j (hj : j < 2 ^ (lvl .N30 0).logN) (r : Fin (lvl .N30 0).rows),
      rdF s₀.M (colBase + 128 * j + 2 * r) = wordOf .N30 L es 0 r ⟨j, hj⟩ := fun j hj r => by
    rw [← hW j hj r]
    exact rdF_eq (t2 _ (le_trans (by decide) (le_add3 _ _ _))
        (.inr (le_trans (by decide) (le_add3 _ _ _))))
      (t2 _ (le_trans (by decide) (le_add4 _ _ _ _)) (.inr (le_trans (by decide) (le_add4 _ _ _ _))))
  have hF : ∀ i < 5, ∀ r x, msgOf .N30 L es i r x = algebraMap F K (msgOf .N30 L es i r x).f₀ :=
    fun i hi => msgOf_embed hi (hfar i hi) (hA i hi)
  -- level 4
  obtain ⟨a1, a2, a3⟩ := lvStep_sem hD hX s₀ s₀ t3 hsz0 (fun _ _ _ => rfl) hXs0 t1 hans0
    (i := 4) (msg := msg4) (by norm_num) le_rfl (hfar 4 (by norm_num)) (hA 4 (by norm_num))
    (hcap 4 (by norm_num) le_rfl) fun s' h1 h2 _ => msg4_keep c π L es hD.hs hfin s₀ hsz0 s' h1 h2
  rw [semXIR_seq]
  have z4 := size_sem I (stepU msg4 4) s₀
  generalize semXIR I (stepU msg4 4) s₀ = s4 at a1 a2 a3 z4
  -- level 3
  obtain ⟨b1, b2, b3⟩ := lvStep_sem hD hX s₀ s4 a3 (z4 ▸ hsz0) a2 hXs0 t1 hans0
    (i := 3) (msg := lvMsg 3) (by norm_num) (by norm_num) (hfar 3 (by norm_num))
    (hA 3 (by norm_num)) (hcap 3 (by norm_num) (by norm_num))
    (lvMsg_keep (i := 3) (by norm_num) I s4 (z4 ▸ hsz0) a1 (hF 4 (by norm_num)))
  rw [semXIR_seq]
  have z3 := size_sem I (stepU (lvMsg 3) 3) s4
  generalize semXIR I (stepU (lvMsg 3) 3) s4 = s3 at b1 b2 b3 z3
  have k3 : ∀ y, regs ≤ y → KeepR y → rd s3.M y = rd s₀.M y := fun y hy h =>
    (b2 y hy h).trans (a2 y hy h)
  -- level 2
  obtain ⟨c1, c2, c3⟩ := lvStep_sem hD hX s₀ s3 b3 (z3 ▸ z4 ▸ hsz0) k3 hXs0 t1 hans0
    (i := 2) (msg := lvMsg 2) (by norm_num) (by norm_num) (hfar 2 (by norm_num))
    (hA 2 (by norm_num)) (hcap 2 (by norm_num) (by norm_num))
    (lvMsg_keep (i := 2) (by norm_num) I s3 (z3 ▸ z4 ▸ hsz0) b1 (hF 3 (by norm_num)))
  rw [semXIR_seq]
  have z2 := size_sem I (stepU (lvMsg 2) 2) s3
  generalize semXIR I (stepU (lvMsg 2) 2) s3 = s2 at c1 c2 c3 z2
  have k2 : ∀ y, regs ≤ y → KeepR y → rd s2.M y = rd s₀.M y := fun y hy h =>
    (c2 y hy h).trans (k3 y hy h)
  -- level 1
  obtain ⟨d1, d2, d3⟩ := lvStep_sem hD hX s₀ s2 c3 (z2 ▸ z3 ▸ z4 ▸ hsz0) k2 hXs0 t1 hans0
    (i := 1) (msg := lvMsg 1) le_rfl (by norm_num) (hfar 1 (by norm_num))
    (hA 1 (by norm_num)) (hcap 1 le_rfl (by norm_num))
    (lvMsg_keep (i := 1) (by norm_num) I s2 (z2 ▸ z3 ▸ z4 ▸ hsz0) c1 (hF 2 (by norm_num)))
  rw [semXIR_seq]
  have z1 := size_sem I (stepU (lvMsg 1) 1) s2
  generalize semXIR I (stepU (lvMsg 1) 1) s2 = s1 at d1 d2 d3 z1
  have k1 : ∀ y, regs ≤ y → KeepR y → rd s1.M y = rd s₀.M y := fun y hy h =>
    (d2 y hy h).trans (k2 y hy h)
  -- level 0
  have hsz1 : memX ≤ s1.M.size := z1 ▸ z2 ▸ z3 ▸ z4 ▸ hsz0
  exact lv0Step_sem I s₀ s1 d3 hsz1 k1 t1 hans0 hW0 (hfar 0 (by norm_num)) (hA 0 (by norm_num))
    (lvMsg_keep (i := 0) (by norm_num) I s1 hsz1 d1 (hF 1 (by norm_num)))

/-! ## Well formed, no `loopT`, no output; the exact cost -/

theorem wf_setA (b : ℕ) : WF (setA b) := by simp +decide only [setA, WF, Prim.dst, rA0,
  List.mem_cons, List.mem_nil_iff, forall_eq, or_false]
theorem noLoopT_setA (b : ℕ) : NoLoopT (setA b) := trivial
theorem outs_setA (b t : ℕ) : outs (setA b) t = 0 := rfl

theorem wf_decLvIR {msg : XIR} (h : WF msg) (i cs cb cbS ob : ℕ) :
    WF (decLvIR msg i cs cb cbS ob) :=
  ⟨⟨wf_eqtIR .., h, wf_setA _, wf_fwdIR .., wf_setA _, wf_fwdIR .., wf_flagIR ..⟩,
    wf_scanIR .., wf_baryIR .., wf_bfRowsIR ..⟩

theorem noLoopT_decLvIR {msg : XIR} (h : NoLoopT msg) (i cs cb cbS ob : ℕ) :
    NoLoopT (decLvIR msg i cs cb cbS ob) :=
  ⟨⟨noLoopT_eqtIR .., h, noLoopT_setA _, noLoopT_fwdIR .., noLoopT_setA _, noLoopT_fwdIR ..,
    noLoopT_flagIR ..⟩, noLoopT_scanIR .., noLoopT_baryIR .., noLoopT_bfRowsIR ..⟩

theorem outs_decLvIR {msg : XIR} {t : ℕ} (h : outs msg t = 0) (i cs cb cbS ob : ℕ) :
    outs (decLvIR msg i cs cb cbS ob) t = 0 := by
  simp only [decLvIR, decFrontIR, decBackIR, outs, h, outs_eqtIR, outs_setA, outs_fwdIR,
    outs_flagIR, outs_scanIR, outs_baryIR, outs_bfRowsIR]

/-- **The cost of one level** (exact): the message step's, plus the `eq` table, two forward
transforms, the flags, the scan, the interpolation and the row butterflies, plus 11 for the
sequencing and the two `setA`. -/
theorem cost_decLvIR (msg : XIR) {i : ℕ} (hi : i < 5) (cs cb cbS ob t : ℕ) :
    cost (decLvIR msg i cs cb cbS ob) t = cost msg t +
      (12 + 2 ^ (lvl .N30 i).ell * (63 + (lvl .N30 i).ell * 271)) +
      2 * (14 + (lvl .N30 i).logN * (741 * 2 ^ ((lvl .N30 i).logN - 1) + 27)) +
      (12 + 2 ^ (lvl .N30 i).logN * (92 + 156 * (lvl .N30 i).rows)) +
      (16 + 2 ^ (lvl .N30 i).logN * 32) +
      (38 + 2 ^ mLog .N30 i * 2487 + 2 ^ mLog .N30 i * (lvl .N30 i).rows * 108 +
        (2 ^ mLog .N30 i) ^ 2 * 1363 + (2 ^ mLog .N30 i) ^ 2 * (lvl .N30 i).rows * 106) +
      (1 + (lvl .N30 i).rows * (17 + mLog .N30 i * (741 * 2 ^ (mLog .N30 i - 1) + 23))) + 11 := by
  have hl : (lvl .N30 i).ell ≤ 6 := by interval_cases i <;> decide
  have hn : (lvl .N30 i).logN ≤ 18 := by interval_cases i <;> decide
  have hm : mLog .N30 i ≤ 17 := by interval_cases i <;> decide
  have hR : (lvl .N30 i).rows ≤ 64 := by interval_cases i <;> decide
  have p1 : 2 ^ (lvl .N30 i).ell < 2 ^ 64 := Nat.pow_lt_pow_right (by norm_num) (by omega)
  have p2 : 2 ^ ((lvl .N30 i).logN - 1) < 2 ^ 64 := Nat.pow_lt_pow_right (by norm_num) (by omega)
  have p3 : 2 ^ (lvl .N30 i).logN < 2 ^ 64 := Nat.pow_lt_pow_right (by norm_num) (by omega)
  have p4 : 2 ^ mLog .N30 i < 2 ^ 64 := Nat.pow_lt_pow_right (by norm_num) (by omega)
  have p5 : 2 ^ (mLog .N30 i - 1) < 2 ^ 64 := Nat.pow_lt_pow_right (by norm_num) (by omega)
  rw [decLvIR, decFrontIR, decBackIR, cost, cost, cost, cost, cost, cost, cost, cost, cost,
    cost_eqtIR _ _ _ _ p1 (by omega), cost_fwdIR _ _ _ p2 (by omega),
    cost_flagIR _ _ _ _ _ _ _ _ _ p3 (by omega), cost_scanIR _ _ _ _ _ p3,
    cost_baryIR _ _ _ _ _ _ _ _ _ _ _ p4 (by omega), cost_bfRowsIR _ _ _ _ p5 (by omega)]
  simp only [setA, cost, blkSteps, List.length_cons, List.length_nil, ite_self]
  ring

/-- The message steps' costs. -/
theorem cost_msg4 (t : ℕ) : cost msg4 t = 38446 := by
  rw [msg4, cost_msgTIR _ _ _ _ _ _ (by norm_num) (by norm_num)]; norm_num

theorem cost_lvMsg {i : ℕ} (hi : i < 4) (t : ℕ) :
    cost (lvMsg i) t = 46 + 36 * 2 ^ (lvl .N30 i).logN + 560 * 2 ^ mLog .N30 (i + 1) := by
  have hn : 2 * 2 ^ (lvl .N30 i).logN < 2 ^ 64 := by interval_cases i <;> decide
  have hk : 8 * 2 ^ mLog .N30 (i + 1) < 2 ^ 64 := by interval_cases i <;> decide
  rw [lvMsg, cost_msgHIR _ _ _ _ _ _ hn hk]

/-- **The five levels' exact costs** (`≈ 2^47.0` in all; level 0's interpolation dominates). -/
theorem cost_levels (t : ℕ) :
    cost (decLvIR msg4 4 32 stB (cbS 4) obL) t = 14546064 ∧
    cost (decLvIR (lvMsg 3) 3 32 stB (cbS 3) obL) t = 261035116 ∧
    cost (decLvIR (lvMsg 2) 2 32 stB (cbS 2) obL) t = 13186204712 ∧
    cost (decLvIR (lvMsg 1) 1 32 stB (cbS 1) obL) t = 823525089508 ∧
    cost (decLvIR (lvMsg 0) 0 128 colBase (cbS 0) ob0) t = 140024626811056 := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · rw [cost_decLvIR _ (by norm_num), cost_msg4]; rfl
  · rw [cost_decLvIR _ (by norm_num), cost_lvMsg (by norm_num)]; rfl
  · rw [cost_decLvIR _ (by norm_num), cost_lvMsg (by norm_num)]; rfl
  · rw [cost_decLvIR _ (by norm_num), cost_lvMsg (by norm_num)]; rfl
  · rw [cost_decLvIR _ (by norm_num), cost_lvMsg (by norm_num)]; rfl

theorem wf_lvMsg (i : ℕ) : WF (lvMsg i) := wf_msgHIR ..
theorem noLoopT_lvMsg (i : ℕ) : NoLoopT (lvMsg i) := noLoopT_msgHIR ..
theorem outs_lvMsg (i t : ℕ) : outs (lvMsg i) t = 0 := outs_msgHIR ..

theorem wf_decLevels : WF decLevels :=
  ⟨wf_wtabIR _, ⟨wf_readLv _, wf_decLvIR (wf_msgTIR ..) ..⟩, ⟨wf_readLv _, wf_decLvIR (wf_lvMsg _) ..⟩,
    ⟨wf_readLv _, wf_decLvIR (wf_lvMsg _) ..⟩, ⟨wf_readLv _, wf_decLvIR (wf_lvMsg _) ..⟩,
    wf_decLvIR (wf_lvMsg _) ..⟩

theorem noLoopT_decLevels : NoLoopT decLevels :=
  ⟨noLoopT_wtabIR _, ⟨noLoopT_readLv _, noLoopT_decLvIR (noLoopT_msgTIR ..) ..⟩,
    ⟨noLoopT_readLv _, noLoopT_decLvIR (noLoopT_lvMsg _) ..⟩,
    ⟨noLoopT_readLv _, noLoopT_decLvIR (noLoopT_lvMsg _) ..⟩,
    ⟨noLoopT_readLv _, noLoopT_decLvIR (noLoopT_lvMsg _) ..⟩,
    noLoopT_decLvIR (noLoopT_lvMsg _) ..⟩

theorem outs_decLevels (t : ℕ) : outs decLevels t = 0 := by
  simp only [decLevels, stepU, msg4, outs, outs_wtabIR, outs_readLv,
    outs_decLvIR (outs_msgTIR _ _ _ _ _ t), outs_decLvIR (outs_lvMsg _ t)]

/-- **The decode's exact cost**: the basis table (79,606), the four reads (`cost_readLv`), the
five levels (`cost_levels`) and 9 for the sequencing: `140,866,457,335,279 ≈ 2^47.0`. -/
theorem cost_decLevels (t : ℕ) : cost decLevels t = 140866457335279 := by
  obtain ⟨r1, r2, r3, r4⟩ := cost_readLv t
  obtain ⟨l4, l3, l2, l1, l0⟩ := cost_levels t
  simp only [decLevels, stepU, cost, cost_wtabIR, r1, r2, r3, r4, l4, l3, l2, l1, l0]

theorem sizeIR_decLevels : sizeIR decLevels = 53515 := by decide +kernel

/-! ## The node branch: index, level 0's read, the chain, the five levels -/

/-- **The decode** (BLUEPRINT §6.2 steps 2–4): the log index and level 0's read (`decRead`), the
Fiat–Shamir replay (`chainIR`, answers at `ansB`), then the five levels (`decLevels`). The chain
runs after the read: its frame keeps the index and the column store. -/
def decF0 : XIR := .seq decRead (.seq (chainIR posL nRep chTab seedIR) decLevels)

/-- **The node branch** (BLUEPRINT §6.2 steps 2–5): the decode `decF0` leaves `f⁽⁰⁾` at `ob0`,
then `outIR` emits `witWords (readWit f⁽⁰⁾)` (`FRXOutRun`). -/
def decNode : XIR := .seq decF0 outIR

/-- **The SNARK branch**: a node runs `decNode`, a leaf outputs its witness. -/
def decLN3 : XIR := .seq kindIR (.ite rKN decNode leafIR)

theorem cost_decF0 (t : ℕ) : cost decF0 t = cost decN t + cost decLevels t + 1 := by
  rw [decF0, decN, cost, cost, cost]
  generalize cost decRead t = a
  generalize cost (chainIR posL nRep chTab seedIR) t = b
  generalize cost decLevels t = c
  omega

/-- The node branch's cost: the decode and the output's `21,609,039` steps. -/
theorem cost_decNode (t : ℕ) : cost decNode t = cost decN t + cost decLevels t + 21609041 := by
  have h1 := cost_decF0 t
  have h2 := cost_outIR t
  show cost decF0 t + cost outIR t + 1 = _
  generalize cost decF0 t = a at h1 ⊢
  generalize cost outIR t = b at h2 ⊢
  generalize cost decN t = c at h1 ⊢
  generalize cost decLevels t = d at h1 ⊢
  omega

theorem outs_decF0 (t : ℕ) : outs decF0 t = 0 := by
  have h1 : outs decRead t = 0 := by simp [decRead, outs, outs_logIR, outs_readIR, read0]
  rw [decF0, outs, outs, h1, outs_chainIR posL nRep t chTab (sd := seedIR) (outs_sdList t _),
    outs_decLevels]

theorem outs_decNode (t : ℕ) : outs decNode t = 571019 := by
  rw [decNode, outs, outs_decF0, outs_outIR]

theorem decOk_decLN3 : DecOk decLN3 where
  wf := ⟨by simp +decide only [kindIR, readAt, WF, Prim.dst, rB, rK2, rKN, rKL, rA, and_true],
    ⟨⟨decOk_decRead.wf, wf_chainIR posL nRep chTab (wf_sdList _) (noWrite_seedIR (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide)), wf_decLevels⟩, wf_outIR⟩,
    by simp +decide only [leafIR, outAt, readAt, WF, Prim.dst, rK2, rV2, rA, and_true]⟩
  safe := fun c π L hs hq ht => .seq (safe_of_noLoopT noLoopT_leaf.1)
    (.ite (.seq (.seq (decOk_decRead.safe c π L hs hq ht)
      (.seq (safe_chainIR c π L (hs_posL hs) hq ht nRep chTab (noLoopT_sdList _) (wf_sdList _)
        (noWrite_seedIR (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)))
        (safe_of_noLoopT noLoopT_decLevels))) (safe_of_noLoopT noLoopT_outIR)) (safe_of_noLoopT noLoopT_leaf.2))
  cost := fun t => by
    have h := cost_decN t
    have e : cost leafIR t = 32 := by simp [leafIR, outAt, readAt, cost, blkSteps]
    have e2 : cost kindIR t = 15 := by simp [kindIR, readAt, cost, blkSteps]
    have h2 : decBudget t = 211106098315264 + 8176 * t := by
      simp only [decBudget, fuelBase, fuelPerWord]; norm_num
    rw [h2, decLN3, cost, cost, e, e2, cost_decNode, cost_decLevels]
    omega
  outs := fun t => by
    simp [decLN3, kindIR, leafIR, outAt, readAt, outs, outs_decNode, outCap]
  size := by
    have := sizeIR_decN
    have e : sizeIR leafIR = 35 := by simp [leafIR, outAt, readAt, sizeIR, blkSteps]
    have e2 : sizeIR kindIR = 15 := by simp [kindIR, readAt, sizeIR, blkSteps]
    have e3 : sizeIR decNode = sizeIR decN + 53515 + 1 + 22421 + 1 := by
      rw [decNode, decF0, sizeIR, sizeIR_outIR, decN, sizeIR, sizeIR, sizeIR, sizeIR_decLevels]
      generalize sizeIR decRead = a
      generalize sizeIR (chainIR posL nRep chTab seedIR) = b
      omega
    rw [decLN3, sizeIR, sizeIR, e, e2, e3]
    generalize sizeIR decN = a at this ⊢
    omega

/-- **The SNARK branch's cost within its fuel** (F): `cost decLN3 t ≤ 211,106,098,315,264 +
8,176 t` (`fuel_base − 2^27`, `fuel_per_word − 16`), with the decode at
`140,866,457,335,279 ≈ 2^47.0` and the output (`outIR`) at `21,609,039` steps. -/
theorem cost_le_decLN3 (t : ℕ) : cost decLN3 t ≤ 211106098315264 + 8176 * t := by
  have h := decOk_decLN3.cost t
  simp only [decBudget, fuelBase, fuelPerWord] at h
  omega

/-- **The SNARK branch's cost with the output** (S-H2l): `cost decLN3 t ≤ 140,884,480,944,337 +
2,558 t`, of which the output is `21,609,039` steps; the budget's margin is
`70,221,617,370,927 + 5,618 t`. -/
theorem cost_le_decLN3_node (t : ℕ) : cost decLN3 t ≤ 140884480944337 + 2558 * t := by
  have h := cost_decN t
  have e : cost leafIR t = 32 := by simp [leafIR, outAt, readAt, cost, blkSteps]
  have e2 : cost kindIR t = 15 := by simp [kindIR, readAt, cost, blkSteps]
  rw [decLN3, cost, cost, e, e2, cost_decNode, cost_decLevels]
  omega

/-! ## The node branch decodes `f⁽⁰⁾` -/

/-- **The chain keeps the heap** outside `[chB, chEnd)` (`chainIR_sem` for the seed block). -/
theorem chain_frame (c : Digest) (π : Proof) (L : Log) (hD : Dom c π L) (st₀ : Digest) (s : St)
    (hM : Inv s.M) (hsz : chEnd ≤ s.M.size) :
    ∀ y, regs ≤ y → (y < chB ∨ chEnd ≤ y) →
      rd (semXIR (tp c π L) (chainIR posL nRep chTab seedIR) s).M y = rd s.M y := by
  have h119 : (fsQ (vkOf π) c π 0 st₀).size = 119 := by
    have hp' : π.size = 797904 := hD.hs.trans piSize_eq
    unfold fsQ
    rw [fsMsgs_ctl.1]
    simp only [if_true]
    rw [seedQ, ByteArray.size_append, extract_size π (by omega),
      show (bytesOf (tagSeed ++ (vkOf π).toList ++ c.toList)).size = 71 by
        simp [bytesOf, ByteArray.size, tagSeed]]
  exact (chainIR_sem c π L (hs_posL hD.hs) hD.hq hD.ht (N := nRep) (by decide)
    (tabW_chTab (vkOf π) c π L hD.hs) (seedOK_seedIR c π L hD.hs st₀) h119 s hM hsz).2.2

/-- Level 0's committed word is π's column store when π's cap is the log's (`capDig es 0 =
capPi π`, the absorb of `cap₀`). -/
theorem wordOf0_eq {L es : Log} {π : Proof} (hcap0 : ∀ e < 2 ^ 9, capDig es 0 e = capPi π e)
    (j : ℕ) (hj : j < 2 ^ (lvl .N30 0).logN) (r : Fin (lvl .N30 0).rows) :
    wordOf .N30 L es 0 r ⟨j, hj⟩ = ((colL (frEnc 0) L (capPi π (j / 2 ^ 9)) 9 j).map
      fun col => F.ofBytes (bytesAt col (16 * r) 16)).getD 0 := by
  have hj' : j < 2 ^ 18 := hj
  have hq : j / 2 ^ 9 < 2 ^ 9 := by rw [Nat.div_lt_iff_lt_mul (by positivity)]; omega
  simp only [wordOf, colOf, show (lvl .N30 0).sib = 9 from rfl, hcap0 _ hq]
  rfl

/-- **The node branch decodes `f⁽⁰⁾`** (BLUEPRINT §6.2 steps 2–4, §6.5 up to `output_spec`): on a
domain tape of a node proof whose log has no state hit, if the log's transcript `es` is the
first-match chain the replay reads (`fmAns … = ansAt es`, the chain link of `runLog`) and its
absorbs are π's fields (the caps `capDig es i`, the final message `finalAt es`), and the word of
every level is close with `A_c = jointAgree` (what `final` hands over), then after `decNode` the
heap at `ob0 + 2^18 r + 2x` holds, as an `F` value, coefficient `x` of row `r` of `f⁽⁰⁾`
(`msgOf .N30 L es 0`). -/
theorem decF0_sem (c : Digest) (π : Proof) (L : Log) (hD : Dom c π L) (hS : ¬ StateHit L)
    (st₀ : Digest) {es : Log}
    (hfm : ∀ p < nRep, fmAns (fsQ (vkOf π) c π) st₀ L p = some (ansAt es p))
    (hcap0 : ∀ e < 2 ^ 9, capDig es 0 e = capPi π e)
    (hcap : ∀ i, 1 ≤ i → i ≤ 4 → ∀ e < 2 ^ capLogL i, capDig es i e = capPiL i π e)
    (hfin : ∀ x < 32, finalAt es x = finPi π x)
    (hfar : ∀ i < 5, ¬ farL .N30 L es i)
    (hA : ∀ i < 5, consSet .N30 L es i = jointAgree (wordK .N30 L es i) (decodeL .N30 L es i))
    (s : St) (hM : Inv s.M) (hsz : memX + L.length + L.length ≤ s.M.size) :
    ∀ r < (lvl .N30 0).rows, ∀ x < 2 ^ mLog .N30 0,
      algebraMap F K (rdF (semXIR (tp c π L) decF0 s).M (ob0 + 2 * 2 ^ mLog .N30 0 * r + 2 * x)) =
        msgOf .N30 L es 0 r x := by
  have hm : memX = 67108864 := rfl
  have ech : chEnd = 8394752 := rfl
  have ecb : colBase = 33554432 := rfl
  -- the index and level 0's read
  have hWF : ∀ q < 2 ^ 18, ∀ r < 64,
      rdF (semXIR (tp c π L) read0 (semXIR (tp c π L) idxIR s)).M (colBase + 128 * q + 2 * r) =
        ((colL (frEnc 0) L (capPi π (q / 2 ^ 9)) 9 q).map
          fun col => F.ofBytes (bytesAt col (16 * r) 16)).getD 0 := fun q hq r hr => by
    have := read_spec_F c π L hD s hM hsz hq hr
    rwa [semXIR_seq] at this
  obtain ⟨r1, r2, r3⟩ := idxIR_sorted c π L hD.hs hD.hq hD.ht s hM hsz
  have hM1 : Inv (semXIR (tp c π L) idxIR s).M := inv_sem _ wf_logIR hM
  have z1 := size_sem (tp c π L) idxIR s
  rw [decF0, semXIR_seq, semXIR_seq, show decRead = .seq idxIR read0 from rfl, semXIR_seq]
  generalize semXIR (tp c π L) idxIR s = s1 at r1 r2 r3 hM1 z1 hWF
  have hX : Sorted (tp c π L) L (fun a => rd s1.M (memX + a)) := ⟨r1, r2, r3⟩
  have hsz1 : memX ≤ s1.M.size := by rw [z1]; exact le_trans (by omega) hsz
  have d2 : ∀ a < L.length, rd (semXIR (tp c π L) read0 s1).M (memX + a) = rd s1.M (memX + a) :=
    (readIR_sem hD (Xi := fun a => rd s1.M (memX + a)) hX s1 hM1 (fun _ _ => rfl)
    (i := 0) (cw := capW0) (nw := 128) (ncap := 512) (sb := colBase) (cap := capPi π) (sib := 9)
    (np := 2 ^ 18)
    (by rw [capW0_eq]; norm_num)
    (fun e he m hm => by simp only [tp, getD_toArray]; exact tape_cap c π L hD.hs he hm)
    (by norm_num) (by norm_num) (by norm_num) (by simp only [colBase, memX]; norm_num)
    (by simp only [regs, colBase]; norm_num) (by norm_num) hsz1).2.1
  have hM2 : Inv (semXIR (tp c π L) read0 s1).M := inv_sem _ (wf_readIR ..) hM1
  have z2 := size_sem (tp c π L) read0 s1
  generalize semXIR (tp c π L) read0 s1 = s2 at d2 hM2 z2 hWF
  have hsz2 : memX ≤ s2.M.size := z2 ▸ hsz1
  -- the chain
  have hans : ∀ p < nRep, ∀ m < 4, rd (semXIR (tp c π L) (chainIR posL nRep chTab seedIR) s2).M
      (ansB + 4 * p + m) = (packBytes (ansAt es p).toList).getD m 0 := fun p hp m hm4 =>
    chain_dec c π L hD.hs hD.hq hD.ht hS st₀ s2 hM2 (le_trans (by decide) hsz2) hp (hfm p hp) hm4
  have cf := chain_frame c π L hD st₀ s2 hM2 (le_trans (by decide) hsz2)
  have hM3 : Inv (semXIR (tp c π L) (chainIR posL nRep chTab seedIR) s2).M := inv_sem _
    (wf_chainIR posL nRep chTab (wf_sdList _) (noWrite_seedIR (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide))) hM2
  have z3 := size_sem (tp c π L) (chainIR posL nRep chTab seedIR) s2
  generalize semXIR (tp c π L) (chainIR posL nRep chTab seedIR) s2 = s3 at hans cf hM3 z3
  have hXs3 : ∀ a < L.length, rd s3.M (memX + a) = rd s1.M (memX + a) := fun a ha =>
    (cf _ (le_trans (by decide) (Nat.le_add_right _ _))
      (.inr (le_trans (by decide) (Nat.le_add_right _ _)))).trans (d2 a ha)
  have hW3 : ∀ j (hj : j < 2 ^ (lvl .N30 0).logN) (r : Fin (lvl .N30 0).rows),
      rdF s3.M (colBase + 128 * j + 2 * r) = wordOf .N30 L es 0 r ⟨j, hj⟩ := fun j hj r => by
    have hR : (lvl .N30 0).rows = 64 := rfl
    have hj' : j < 2 ^ 18 := hj
    rw [wordOf0_eq hcap0, ← hWF j hj' r (hR ▸ r.2)]
    exact rdF_eq (cf _ (le_trans (by decide) (le_add3 _ _ _))
        (.inr (le_trans (by decide) (le_add3 _ _ _))))
      (cf _ (le_trans (by decide) (le_add4 _ _ _ _)) (.inr (le_trans (by decide) (le_add4 _ _ _ _))))
  exact (decLevels_sem hD hX s3 hM3 (z3 ▸ hsz2) hXs3 hW3 hans hcap hfin hfar hA).1

theorem loK_outIR : LoK outIR := by
  have h1 := loK_segIR apS FR.Read.slotSeg 0 (by have := okSeg_slot.2; omega)
  have h2 := loK_segIR apL FR.Read.sigSeg 0 (by have := okSeg_sig.2; omega)
  have h3 := loK_segIR apS (.cp 6 4) 0 (by simp [depthSeg])
  have hk : LoK kflagIR := ⟨by simp +decide only [LoK, Prim.dst, oU, regs], loK_ldw apS,
    by simp +decide only [LoK, Prim.dst, oK, oX, oT1, oT2, oKF, regs]⟩
  simp only [outIR, slotIR, setR, LoK]
  refine ⟨by simp [Prim.dst, oBd, oKF, oX, regs], trivial, by simp [Prim.dst, oR, regs], h3,
    by simp [Prim.dst, oR, regs], h3, ⟨by simp [Prim.dst, oR, regs], hk, h1, by simp [Prim.dst, oR, regs],
      by simp [Prim.dst, oKF, regs], h2⟩, ⟨by simp [Prim.dst, oR, regs], hk, h1, by simp [Prim.dst, oR, regs],
      by simp [Prim.dst, oKF, regs], h2⟩⟩

/-- **The node branch decodes `f⁽⁰⁾`** (as `decF0_sem`; the output step keeps the heap). -/
theorem decNode_sem (c : Digest) (π : Proof) (L : Log) (hD : Dom c π L) (hS : ¬ StateHit L)
    (st₀ : Digest) {es : Log}
    (hfm : ∀ p < nRep, fmAns (fsQ (vkOf π) c π) st₀ L p = some (ansAt es p))
    (hcap0 : ∀ e < 2 ^ 9, capDig es 0 e = capPi π e)
    (hcap : ∀ i, 1 ≤ i → i ≤ 4 → ∀ e < 2 ^ capLogL i, capDig es i e = capPiL i π e)
    (hfin : ∀ x < 32, finalAt es x = finPi π x)
    (hfar : ∀ i < 5, ¬ farL .N30 L es i)
    (hA : ∀ i < 5, consSet .N30 L es i = jointAgree (wordK .N30 L es i) (decodeL .N30 L es i))
    (s : St) (hM : Inv s.M) (hsz : memX + L.length + L.length ≤ s.M.size) :
    ∀ r < (lvl .N30 0).rows, ∀ x < 2 ^ mLog .N30 0,
      algebraMap F K (rdF (semXIR (tp c π L) decNode s).M (ob0 + 2 * 2 ^ mLog .N30 0 * r + 2 * x)) =
        msgOf .N30 L es 0 r x := fun r hr x hx => by
  rw [decNode, semXIR_seq, ← decF0_sem c π L hD hS st₀ hfm hcap0 hcap hfin hfar hA s hM hsz r hr x hx]
  exact congrArg _ (rdF_eq (hframeK _ _ _ loK_outIR _ (by simp only [ob0, regs]; omega))
    (hframeK _ _ _ loK_outIR _ (by simp only [ob0, regs]; omega)))

/-- **The node branch outputs the node witness** read off `f⁽⁰⁾` (BLUEPRINT §6.2 step 5): after
the decode, `outIR` appends `witWords (readWit w)` with `w e = (msgOf .N30 L es 0 (e mod 64)
⌊e/64⌋).f₀` (A.10's `fF .N30 L es`). -/
theorem decNode_out (c : Digest) (π : Proof) (L : Log) (hD : Dom c π L) (hS : ¬ StateHit L)
    (st₀ : Digest) {es : Log}
    (hfm : ∀ p < nRep, fmAns (fsQ (vkOf π) c π) st₀ L p = some (ansAt es p))
    (hcap0 : ∀ e < 2 ^ 9, capDig es 0 e = capPi π e)
    (hcap : ∀ i, 1 ≤ i → i ≤ 4 → ∀ e < 2 ^ capLogL i, capDig es i e = capPiL i π e)
    (hfin : ∀ x < 32, finalAt es x = finPi π x)
    (hfar : ∀ i < 5, ¬ farL .N30 L es i)
    (hA : ∀ i < 5, consSet .N30 L es i = jointAgree (wordK .N30 L es i) (decodeL .N30 L es i))
    (s : St) (hM : Inv s.M) (hsz : memX + L.length + L.length ≤ s.M.size) :
    (semXIR (tp c π L) decNode s).o.toList = (semXIR (tp c π L) decF0 s).o.toList ++
      witWords (FR.readWit fun e => (msgOf .N30 L es 0 (e % 64) (e / 64)).f₀) := by
  rw [decNode, semXIR_seq]
  have hM' : Inv (semXIR (tp c π L) decF0 s).M := inv_sem _ (decOk_decLN3.wf.2.1.1) hM
  refine outIR_out _ _ _ hM' fun e he => ?_
  have h := decF0_sem c π L hD hS st₀ hfm hcap0 hcap hfin hfar hA s hM hsz (e % 64)
    (Nat.mod_lt _ (by decide)) (e / 64) (by rw [show mLog .N30 0 = 17 from rfl]; omega)
  rw [show mLog .N30 0 = 17 from rfl, show ob0 = 16777216 from rfl] at h
  rw [show 16777216 + 2 ^ 18 * (e % 64) + 2 * (e / 64) = 16777216 + 2 * 2 ^ 17 * (e % 64) + 2 * (e / 64) by
    norm_num, ← h]
  rfl

end FR.X

end G6_FRXNode

section G6_FRXExt

-- New for `flock-recursive` (BLUEPRINT §6.4; stage S-H2, track L-ext).

/-!
# The extractor `ext`, its specification `E`, and `computes`

`ext := extWith decSnark` with the SNARK branch delivered so far. **`E` (B-15, revision 4.0)** is
`if InDomE then Ed else Eout`:
* `Ed`, the decoded denotation of `ext`'s program (B-8, revision 3.17), on the contract's
  `Computes` domain `InDomE`: proofs of at most `8 · outCap` bytes, queries below `2^64` bytes, a
  tape of at most `2^64` words;
* `Eout` outside it, by the proof's kind: a `W` proof is decoded (`WitnessSending.decode`), a node
  SNARK is searched (`FRXSearch.search` with the acceptance `A` under the key `vkOf π` that the
  proof carries), a leaf SNARK keeps the denotation (domain-free, `FRXLeaf.E_leaf`), a `bad` proof
  has none.

`E` is parametric in `A`, the acceptance the search tests: the verifier is still parametric
(`finPf`, `lRows`), and the certificate instantiates `A := S.acc`. `computes` holds for every `A`,
since `E = Ed` on the domain. Every branch is a compiled `def`: the badge compiles `E`, it does not
run it.

*Why the dispatch (deviation from B-15's text "else `E_search`").* The search's key is `vkOf π`,
which is the verifier's key only on an accepted node run (`vkOf_of_run`). A `W` proof's bytes
`16 … 47` are arbitrary, and for a leaf SNARK the search could return a node witness for the
wrong key; both have a domain-free witness instead.
-/

namespace FR.X

open RecursionFast

/-! ## The program delivered: `ext`, `E`, `computes` -/

/-- **The SNARK branch delivered so far**: a leaf (`'L'`, `'P'`) outputs its witness from the
header (§6.2 step 1, `FRXLeaf.E_leaf`); a node (`'N'`) runs the log index and the ladder read of
level 0 (§6.2 steps 2–3, `read_spec`), replays the Fiat–Shamir chain from the seed it carries
(`FRXDec.chain_dec`), decodes the five levels into `f⁽⁰⁾`'s rows (§6.2 step 4,
`FRXNode.decLevels_sem`), and outputs the node witness read off `f⁽⁰⁾` (§6.2 step 5,
`FRXOutRun.outIR_out`, `FRXNodeRun.E_node`). -/
def decSnark : XIR := decLN3

theorem decOk_decSnark : DecOk decSnark := decOk_decLN3

/-- **The extractor program** `ext := toProg 2^26 3 extIR` (§6.4). -/
def ext : XProg := extWith decSnark

/-- **The in-domain extractor** (B-8, revision 3.17): the decoded denotation of `ext`'s program,
`Ed c π L = decodeWit (semXIR extIR …).o` on the tape `extractorInput c π L`, a total computable
function on every log (no fuel). On the domain it is `ext`'s output (`computesWith`). -/
def Ed : Digest → Proof → Log → Option Wit := Eden memX mpwX (extIRWith decSnark)

/-- **The contract's `Computes` domain**: a proof of at most `8 · outCap` bytes, queries below
`2^64` bytes, a tape of at most `2^64` words. -/
def InDomE (c : Digest) (π : Proof) (L : Log) : Prop :=
  π.size ≤ 8 * outCap ∧ (∀ e ∈ L, e.1.size < 2 ^ 64) ∧ (extractorInput c π L).length ≤ 2 ^ 64

instance (c : Digest) (π : Proof) (L : Log) : Decidable (InDomE c π L) :=
  inferInstanceAs (Decidable (_ ∧ _ ∧ _))

/-- **The extractor outside the domain** (B-15), by the proof's kind: `W` decoded, a node SNARK
searched under the key it carries, a leaf SNARK's denotation, `bad` none. -/
def Eout (A : Digest → Digest → Signed → Bool) (c : Digest) (π : Proof) (L : Log) : Option Wit :=
  match kindOf π with
  | .W => WitnessSending.decode π
  | .snark k => if k.isNode then search A (vkOf π) c else Ed c π L
  | .bad => none

/-- **The extractor specification** (B-15, revision 4.0): `Ed` on the domain, `Eout` outside it;
`A` is the acceptance the search tests (the certificate's `S.acc`). -/
def E (A : Digest → Digest → Signed → Bool) (c : Digest) (π : Proof) (L : Log) : Option Wit :=
  if InDomE c π L then Ed c π L else Eout A c π L

variable {A : Digest → Digest → Signed → Bool} {c : Digest} {π : Proof} {L : Log}

theorem E_of_dom (h : InDomE c π L) : E A c π L = Ed c π L := if_pos h

theorem E_of_not_dom (h : ¬ InDomE c π L) : E A c π L = Eout A c π L := if_neg h

/-- A SNARK proof has `piSize` bytes. -/
theorem size_snarkX {k : Kind} (hk : kindOf π = .snark k) : π.size = piSize := by
  by_contra hne
  simp only [kindOf, byteAt?_eq, hne, if_false] at hk
  split at hk <;> simp at hk

/-- A SNARK proof is within the domain's proof bound. -/
theorem size_snark_le {k : Kind} (hk : kindOf π = .snark k) : π.size ≤ 8 * outCap := by
  rw [size_snarkX hk, piSize_eq, outCap]; norm_num

/-- **A leaf SNARK's extractor is the denotation, on every log.** -/
theorem E_snark_leaf {k : Kind} (hk : kindOf π = .snark k) (hkn : k.isNode = false) :
    E A c π L = Ed c π L := by
  by_cases h : InDomE c π L
  · exact E_of_dom h
  · rw [E_of_not_dom h, Eout]; simp [hk, hkn]

/-- **A node SNARK outside the domain is searched** under the key it carries. -/
theorem E_snark_node {k : Kind} (hk : kindOf π = .snark k) (hkN : k.isNode = true)
    (h : ¬ InDomE c π L) : E A c π L = search A (vkOf π) c := by
  rw [E_of_not_dom h, Eout]; simp [hk, hkN]

/-- **`Computes ext (E A) fuel`**, for every `A`: the certificate's `computes` conjunct (on the
domain `E A = Ed`, `computesWith`). -/
theorem computes (A : Digest → Digest → Signed → Bool) : Computes ext (E A) fuel :=
  fun c π L h1 h2 h3 => by
    obtain ⟨o, ho, hl, hd⟩ := computesWith decOk_decSnark c π L h1 h2 h3
    exact ⟨o, ho, hl, hd.trans (E_of_dom ⟨h1, h2, h3⟩).symm⟩

/-- The certificate's caps on the extractor: the fuel within `B`, the program within `progCap`. -/
theorem ext_caps : (∀ t, fuel t ≤ extractorBudget t) ∧ ext.body.size ≤ progCap :=
  ⟨fuel_le_budget, size_extWith decOk_decSnark.size⟩

end FR.X

end G6_FRXExt

section G6_FRXSpec

-- New for `flock-recursive` (BLUEPRINT §6.5, §5.4; stage S-H2, track L-ext).

/-!
# What `ext` outputs: the `W` and `bad` cases of `ext_good_tape`

BLUEPRINT §6.5, §5.4 ("`W` is `Rel` by definition and `E` copies the proof (§6.2, any size)").

* `parse_isK`: the parse's kind flag is `kindFlag` of tape word 5, which is `0` exactly when the
  word's low byte is not a kind byte (`kindFlag_eq_zero`);
* **`E_W`**: on a proof of the `W` kind (`kindOf π = .W`, `FRFormat`) of fewer than `2^64` bytes,
  `Eden … c π L = WitnessSending.decode π`, for every SNARK branch with `DecOk`, **on every log**
  (no domain hypothesis): the program halts within `fuel` on every such tape, and its output is
  the denotation (`den_of_run`);
* **`ext_W`** (B-15): `E A c π L = WitnessSending.decode π` on **every** `W` proof and log: `E_W`
  on the domain, `Eout`'s `W` branch outside it (proofs above `8 · outCap` bytes included);
* **`E_bad`**: on a kind byte with `|π| ≠ piSize` (`kindOf π = .bad`), `Eden … c π L = none` (no
  output; the negative control: an ill-formed tape halts within the fuel); `ext_bad` for `E`.

The SNARK case (`kindOf π = .snark k`) is the decoder's (§6.2 steps 2–5), not delivered here.
-/

namespace FR.X

open RecursionFast

/-- The parse's kind flag: `1` if the low byte of `w` is `'L'`, `'P'` or `'N'`, else `0`. -/
def kindFlag (w : Word) : Word :=
  ((if w &&& 0xFF = 0x4C then 1 else 0) ||| (if w &&& 0xFF = 0x50 then 1 else 0)) |||
    (if w &&& 0xFF = 0x4E then 1 else 0)

theorem parse_isK (I : Array Word) (s : St) (hM : Inv s.M) :
    rd (semXIR I parseIR s).M rIsK = kindFlag (I.getD 5 0) := by
  have hs := hM.1
  simp only [regs] at hs
  simp only [parseIR, readAt, kindPs, semXIR, runPrims, List.foldl, Prim.run, rA, rLen, rK, rB0,
    rIsK, rT, rIsSz]
  simp (disch := first | decide | omega | (simp only [size_set]; omega))
    [rd_set_self, rd_set_ne, XOp.eval, kindFlag]

theorem kindFlag_eq_zero (w : Word) :
    kindFlag w = 0 ↔ (w &&& 0xFF ≠ 0x4C ∧ w &&& 0xFF ≠ 0x50 ∧ w &&& 0xFF ≠ 0x4E) := by
  unfold kindFlag
  by_cases h1 : w &&& 0xFF = 0x4C <;> by_cases h2 : w &&& 0xFF = 0x50 <;>
    by_cases h3 : w &&& 0xFF = 0x4E <;> simp_all <;> decide

/-- The low byte of a word. -/
theorem lowByte (w : Word) : (w &&& 0xFF).toNat = w.toNat % 256 := by
  rw [BitVec.toNat_and, show (0xFF : Word).toNat = 2 ^ 8 - 1 from rfl,
    Nat.and_two_pow_sub_one_eq_mod]

theorem toNat_toUInt8 (n : ℕ) : n.toUInt8.toNat = n % 256 := by
  rw [Nat.toUInt8_eq, UInt8.toNat_ofNat']

/-- The low byte of tape word 5 is the proof's first byte. -/
theorem tape_byte0 (c : Digest) (π : Proof) (L : Log) {b : UInt8} (h0 : π.data[0]? = some b) :
    ((extractorInput c π L).getD 5 0).toNat.toUInt8 = b := by
  have hpos : 0 < π.size := by
    rcases Nat.eq_zero_or_pos π.size with h | h
    · simp [ByteArray.size, Array.size_eq_zero_iff.mp h] at h0
    · exact h
  have := tape_getD_proof c π L (j := 0) (by omega)
  rw [Nat.add_zero] at this
  rw [this]
  have hw := wordByte_packBytes π.data.toList 0
  simp only [wordByte, Nat.zero_div, Nat.zero_mod, pow_zero, Nat.div_one] at hw
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by
    rw [packBytes_length, ← WitnessSending.size_eq_length]; omega), Option.getD_some] at hw
  rw [hw, List.getD_eq_getElem?_getD, Array.getElem?_toList, h0, Option.getD_some]

/-- A first byte that is a kind byte, as `kindFlag` sees it. -/
theorem kindFlag_byte (w : Word) :
    kindFlag w = 0 ↔ Kind.ofByte? w.toNat.toUInt8 = none := by
  have A : ∀ v : Word, v.toNat < 256 → (w &&& 0xFF = v ↔ w.toNat % 256 = v.toNat) :=
    fun v _ => by rw [← BitVec.toNat_inj, lowByte]
  have B : ∀ u : UInt8, (w.toNat.toUInt8 = u ↔ w.toNat % 256 = u.toNat) := fun u => by
    rw [← UInt8.toNat_inj, toNat_toUInt8]
  rw [kindFlag_eq_zero]
  simp only [ne_eq]
  rw [A _ (by decide), A _ (by decide), A _ (by decide)]
  simp only [Kind.ofByte?, B, UInt8.reduceToNat]
  split_ifs <;> simp_all

/-! ## The run on a tape whose proof is not a SNARK proof -/

/-- **The run when the kind flag is clear or the length is not `piSize`**: on a tape whose word 4
is `a < 2^64` followed by `⌈a/8⌉` words, if `a ≠ 0` forces a clear kind flag, the program halts
within the fuel and outputs the `⌈a/8⌉` words from word 5. -/
theorem run_W_tape {dec : XIR} (hd : DecOk dec) (inp : List Word) (a : ℕ) (ha : a < 2 ^ 64)
    (h4 : inp.toArray.getD 4 0 = toWord a) (hlen : (a + 7) / 8 + 6 ≤ inp.length)
    (hk : a ≠ 0 → kindFlag (inp.toArray.getD 5 0) = 0) :
    (extWith dec).run inp (fuel inp.length) =
      some ((List.range ((a + 7) / 8)).map fun j => inp.toArray.getD (5 + j) 0) := by
  have hwf := wf_extIRWith hd.wf
  have hreg : regs ≤ memX := by simp only [regs, memX]; norm_num
  have h0 : Inv (initSt (memX + mpwX * inp.length)).M := inv_initSt (Nat.le_add_right_of_le hreg)
  generalize hs0 : initSt (memX + mpwX * inp.length) = s0 at h0
  generalize hI : inp.toArray = I at h4 hk ⊢
  have h1 : Inv (semXIR I parseIR s0).M := inv_sem I hwf.1 h0
  have hz0 : a = 0 → rd (semXIR I parseIR s0).M rIsSz = 0 := by
    intro h
    rw [parse_regs I s0 h0, h4, h, if_neg]
    intro he
    have := congrArg BitVec.toNat he
    rw [toNat_toWord (by omega), BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by rw [piSize_eq]; omega),
      piSize_eq] at this
    omega
  have hk' : a ≠ 0 → rd (semXIR I parseIR s0).M rIsK = 0 := fun h => by
    rw [parse_isK I s0 h0]; exact hk h
  have hpo : (semXIR I parseIR s0).o = #[] := by rw [parse_o, ← hs0, initSt_o]
  have hw : (ceil8 (I.getD 4 0)).toNat = (a + 7) / 8 := by rw [h4, toNat_ceil8 ha]
  generalize hs1 : semXIR I parseIR s0 = s1 at h1 hz0 hk' hpo
  have hB : BoundsOk I inp.length (extIRWith dec) s0 := by
    rw [extIRWith, boundsOk_seq]
    refine ⟨boundsOk_of_safe (safe_parseIR _ _) hwf.1 _ h0, ?_⟩
    rw [hs1, boundsOk_ite]
    by_cases hk1 : rd s1.M rIsK = 0
    · rw [if_pos hk1]
      exact boundsOk_of_safe (safe_wIR ha h4 (by omega)) hwf.2.2 _ h1
    · have ha0 : a = 0 := by by_contra h; exact hk1 (hk' h)
      rw [if_neg hk1, boundsOk_ite, if_pos (hz0 ha0)]; trivial
  have hrun := run_toProg (P := extIRWith dec) (input := inp) (f := fuel inp.length) hreg hwf
    (by rw [hs0, hI]; exact hB) (fuel_covers hd.cost _)
  rw [hs0, hI] at hrun
  refine hrun.trans (congrArg some ?_)
  by_cases hk1 : rd s1.M rIsK = 0
  · have e : semXIR I (extIRWith dec) s0 = semXIR I wIR s1 := by
      rw [extIRWith, semXIR_seq, hs1, semXIR_ite, if_pos hk1]
    rw [congrArg (fun s' : St => s'.o.toList) e, wIR_sem I _ h1 (by omega), hpo, hw]
    rfl
  · have ha0 : a = 0 := by by_contra h; exact hk1 (hk' h)
    have e : semXIR I (extIRWith dec) s0 = semXIR I (.blk []) s1 := by
      rw [extIRWith, semXIR_seq, hs1, semXIR_ite, if_neg hk1, semXIR_ite, if_pos (hz0 ha0)]
    rw [congrArg (fun s' : St => s'.o.toList) e, ha0]
    simp [semXIR, hpo]

/-- **The `W` case**: on a `W` proof of fewer than `2^64` bytes, any size above the contract's
domain `8 · outCap` included, the program outputs the proof's packed words within the fuel. -/
theorem run_W {dec : XIR} (hd : DecOk dec) (c : Digest) (π : Proof) (L : Log)
    (hW : kindOf π = .W) (hπ : π.size < 2 ^ 64) :
    (extWith dec).run (extractorInput c π L) (fuel (extractorInput c π L).length) =
      some (packBytes π.data.toList) := by
  rw [run_W_tape hd _ π.size hπ (by rw [getD_toArray, tape_getD4]) (tape_length c π L)]
  · congr 1
    refine List.ext_getElem (by
      simp only [List.length_map, List.length_range, packBytes_length]
      rw [WitnessSending.size_eq_length]) fun j _ h2 => ?_
    simp only [List.getElem_map, List.getElem_range, getD_toArray]
    exact tape_getD_proof c π L (by rwa [packBytes_length, ← WitnessSending.size_eq_length] at h2)
  · intro hne
    obtain ⟨b, hb⟩ : ∃ b, π.data[0]? = some b := by
      rcases h : π.data[0]? with _ | b
      · rw [Array.getElem?_eq_none_iff] at h; exact (hne (Nat.le_zero.mp h)).elim
      · exact ⟨b, rfl⟩
    rw [kindFlag_byte, getD_toArray, tape_byte0 c π L hb]
    simp only [kindOf, byteAt?_eq, hb, Option.bind_some] at hW
    revert hW; cases Kind.ofByte? b
    · intro; rfl
    · intro h; by_cases hs : π.size = piSize <;> simp [hs] at h

/-- **`E` on a `W` proof is `WitnessSending.decode`** (§5.4: "`E` copies the proof"). -/
theorem E_W {dec : XIR} (hd : DecOk dec) (c : Digest) (π : Proof) (L : Log)
    (hW : kindOf π = .W) (hπ : π.size < 2 ^ 64) :
    Eden memX mpwX (extIRWith dec) c π L = WitnessSending.decode π := by
  rw [Eden, ← den_of_run (by simp only [regs, memX]; norm_num) (wf_extIRWith hd.wf)
    (run_W hd c π L hW hπ)]
  rfl

/-- The run on a tape whose kind flag is set and whose word 4 is not `piSize`: no output. -/
theorem run_bad_tape {dec : XIR} (hd : DecOk dec) (inp : List Word) (a : ℕ) (ha : a < 2 ^ 64)
    (h4 : inp.toArray.getD 4 0 = toWord a) (hs : a ≠ piSize)
    (hk : kindFlag (inp.toArray.getD 5 0) ≠ 0) :
    (extWith dec).run inp (fuel inp.length) = some [] := by
  have hwf := wf_extIRWith hd.wf
  have hreg : regs ≤ memX := by simp only [regs, memX]; norm_num
  have h0 : Inv (initSt (memX + mpwX * inp.length)).M := inv_initSt (Nat.le_add_right_of_le hreg)
  generalize hs0 : initSt (memX + mpwX * inp.length) = s0 at h0
  generalize hI : inp.toArray = I at h4 hk ⊢
  have h1 : Inv (semXIR I parseIR s0).M := inv_sem I hwf.1 h0
  have hz : rd (semXIR I parseIR s0).M rIsSz = 0 := by
    rw [parse_regs I s0 h0, h4, if_neg]
    intro he
    have := congrArg BitVec.toNat he
    rw [toNat_toWord ha, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by rw [piSize_eq]; omega)] at this
    exact hs this
  have hk1 : rd (semXIR I parseIR s0).M rIsK ≠ 0 := by rw [parse_isK I s0 h0]; exact hk
  have hpo : (semXIR I parseIR s0).o = #[] := by rw [parse_o, ← hs0, initSt_o]
  generalize hs1 : semXIR I parseIR s0 = s1 at h1 hz hk1 hpo
  have hB : BoundsOk I inp.length (extIRWith dec) s0 := by
    rw [extIRWith, boundsOk_seq]
    refine ⟨boundsOk_of_safe (safe_parseIR _ _) hwf.1 _ h0, ?_⟩
    rw [hs1, boundsOk_ite, if_neg hk1, boundsOk_ite, if_pos hz]; trivial
  have hrun := run_toProg (P := extIRWith dec) (input := inp) (f := fuel inp.length) hreg hwf
    (by rw [hs0, hI]; exact hB) (fuel_covers hd.cost _)
  rw [hs0, hI] at hrun
  refine hrun.trans (congrArg some ?_)
  have e : semXIR I (extIRWith dec) s0 = semXIR I (.blk []) s1 := by
    rw [extIRWith, semXIR_seq, hs1, semXIR_ite, if_neg hk1, semXIR_ite, if_pos hz]
  rw [congrArg (fun s' : St => s'.o.toList) e]
  simp [semXIR, hpo]

/-- **The `bad` case** (the ill-formed control): a kind byte with `|π| ≠ piSize` makes no output
within the fuel, so `E` is `none`. -/
theorem E_bad {dec : XIR} (hd : DecOk dec) (c : Digest) (π : Proof) (L : Log)
    (hb : kindOf π = .bad) (hπ : π.size < 2 ^ 64) :
    (extWith dec).run (extractorInput c π L) (fuel (extractorInput c π L).length) = some [] ∧
      Eden memX mpwX (extIRWith dec) c π L = none := by
  obtain ⟨b, hb0⟩ : ∃ b, π.data[0]? = some b := by
    rcases h : π.data[0]? with _ | b
    · simp [kindOf, byteAt?_eq, h] at hb
    · exact ⟨b, rfl⟩
  have hk : kindFlag ((extractorInput c π L).toArray.getD 5 0) ≠ 0 := by
    rw [Ne, kindFlag_byte, getD_toArray, tape_byte0 c π L hb0]
    simp only [kindOf, byteAt?_eq, hb0, Option.bind_some] at hb
    intro h; rw [h] at hb; cases hb
  have hs : π.size ≠ piSize := by
    intro h
    simp only [kindOf, byteAt?_eq, hb0, Option.bind_some, h, ↓reduceIte] at hb
    revert hb; cases Kind.ofByte? b <;> simp
  have hr := run_bad_tape hd _ π.size hπ (by rw [getD_toArray, tape_getD4]) hs hk
  exact ⟨hr, by
    rw [Eden, ← den_of_run (by simp only [regs, memX]; norm_num) (wf_extIRWith hd.wf) hr]; rfl⟩

/-- **`E` on a `W` proof is `WitnessSending.decode`, on every size and log** (B-15: `E_W` on the
domain, `Eout`'s `W` branch outside it). -/
theorem ext_W (A : Digest → Digest → Signed → Bool) (c : Digest) (π : Proof) (L : Log)
    (hW : kindOf π = .W) : E A c π L = WitnessSending.decode π := by
  by_cases h : InDomE c π L
  · rw [E_of_dom h]
    exact E_W decOk_decSnark c π L hW (by have := h.1; rw [outCap] at this; omega)
  · rw [E_of_not_dom h, Eout]; simp [hW]

/-- **`E` on a `bad` proof is `none`**, on every size and log (`E_bad` on the domain). -/
theorem ext_bad (A : Digest → Digest → Signed → Bool) (c : Digest) (π : Proof) (L : Log)
    (hb : kindOf π = .bad) : E A c π L = none := by
  by_cases h : InDomE c π L
  · rw [E_of_dom h]
    exact (E_bad decOk_decSnark c π L hb (by have := h.1; rw [outCap] at this; omega)).2
  · rw [E_of_not_dom h, Eout]; simp [hb]

/-! ## Controls

* Positive (every witness-sending witness): `ext_encode`: `E A c (encode w) L = some w` for every
  `w` that fits the output format, on every statement and log.
* Negative (ill-formed, `E_bad`/`ext_bad`): a kind byte with another length halts within the
  fuel with no output.
* Kernel runs of the compiled code (the parse and the `W` branch with a 260-word memory, the
  program's statement unchanged): a toy `W` tape outputs its two proof words (`toy_W`); a toy tape
  whose first byte is `'N'` and whose length is not `piSize` outputs nothing (`toy_bad`); with the
  run takes exactly `260 + 80` fuel (`toy_W_exact`).
-/

/-- A witness-sending proof's first byte is its tag word's: `0` or `1`. -/
theorem encode_byte0 (w : Wit) :
    (WitnessSending.encode w).data[0]? = some 0 ∨ (WitnessSending.encode w).data[0]? = some 1 := by
  cases w <;> simp [WitnessSending.encode, witWords, wordsBytes, wordBytes, enc64, toWord]

/-- **Positive control**: `ext` recovers every witness-sending witness. -/
theorem ext_encode (A : Digest → Digest → Signed → Bool) (c : Digest) (L : Log) (w : Wit)
    (hw : w.Fits) : E A c (WitnessSending.encode w) L = some w := by
  have hk : kindOf (WitnessSending.encode w) = .W := by
    rcases encode_byte0 w with h | h
    · exact kindOf_W h (.inl rfl)
    · exact kindOf_W h (.inr rfl)
  rw [ext_W A c _ L hk, WitnessSending.decode_encode w hw]

namespace Controls

/-- The program with a 260-word memory (the toy runs; `ext`'s memory is `2^26`). -/
def toyP : XProg := toProg 260 0 (extIRWith decSnark)

/-- A toy `W` tape: statement, `|π| = 9`, two proof words (first byte `0x00`), `|L| = 0`. -/
def tapeW : List Word := [0, 0, 0, 0, 9, 0x1100, 0x22, 0]

/-- A toy ill-formed tape: first byte `'N'`, `|π| = 9 ≠ piSize`. -/
def tapeBad : List Word := [0, 0, 0, 0, 9, 0x114E, 0x22, 0]

theorem toy_W : toyP.run tapeW 400 = some [0x1100, 0x22] := by
  simp only [toyP, extIRWith, parseIR, kindPs, piSize_eq]; decide +kernel

/-- Exactly `260 + 80` steps: `340` suffices, `339` does not. -/
theorem toy_W_exact : toyP.run tapeW 340 = some [0x1100, 0x22] ∧ toyP.run tapeW 339 = none := by
  simp only [toyP, extIRWith, parseIR, kindPs, piSize_eq]; decide +kernel

theorem toy_bad : toyP.run tapeBad 400 = some [] := by
  simp only [toyP, extIRWith, parseIR, kindPs, piSize_eq]; decide +kernel

end Controls

end FR.X

end G6_FRXSpec
