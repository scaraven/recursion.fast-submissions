-- New for lvm6 (WP CB, CB-4). The node's sponge block as a sponge table: from K1's `OutRel 13 25`
-- and the sponge link over CB-3's rows (`rowsBK2 B 7567 8032`), the trace digest of the child's
-- stream (with CA's `LaneLink6` and padding) and `Q_sig`'s two `KS` hypotheses (`SigKSin` for `σ'`,
-- `SigKSinC` for `σ_leaf`). Season 1's parked `traceDigest_of_goodKP`/`sigKSin_of_goodKP`, re-instantiated.
import Lvm6QKLink
import Lvm6QLinkBridge
import Lvm6QSig
import Lvm6QFormat
import Lvm6P17Memo
import LvmKeccakCaller

/-!
# CB-4: the sponge row map and what it proves

The node's sponge block has `2^13` rows (FORMAT6 v2.5.1 §T): the split is `7,168 = 2^13 − 2^10`
(`xl = 10`); rows `i < 7,168` absorb stream words `17 i … 17 i + 16` (`M`), rows from it absorb
`X` (`σ'`'s walk at `X` rows `0 … 448`, `σ_leaf`'s at `512 … 911`). The continuation rows are
`rowsBK2 B K₁ K₂` with `K₁ = 7,567` (`σ'`'s key leaf, `X` rows `399 … 430`) and `K₂ = 8,032`
(`σ_leaf`'s, `X` rows `864 … 895`, `nStepRowsC = 352`).

* **`spongeRel6`**: `OutRel` and `SpongeLink` give season 1's `SpongeRel` (`cont i = [i ∈ rows]`).
* **`blocks_P18`** (in `Lvm6P18Park` since INT11): at `P18` (FORMAT6 v2.5.2, `qS = 4,349`) the stream hashes `L = 544,152`
  bytes in `B = 4,002` blocks (kernel `decide` over CA's plan of WP-S's `sched6`); **`blocks_P17`**: at the
  node's shape `P17` (FORMAT6 v2.6, `qS = 4,106`), `L = 518,928` bytes in `B = 3,816` blocks.
* **`traceDigest6`**: rows `0 … B − 1`, `B = nBlk (hashedLen6 P) ≤ 7,168`, output the child's
  trace digest `traceDigest (decode6 P ws)` at row `B − 1`.
* **`sigKSin6`**, **`sigKSinC6`**: with `Q_sig`'s input arrays holding `X`'s rows and its digest
  cells holding the output lanes of the matching rows, `SigKSin I v` and `SigKSinC Il v` hold.
-/

set_option autoImplicit false

namespace Lvm6.QK.W

open RecursionFast Lvm Lvm.Replay Lvm.QLink Lvm.QSig Lvm.KG Lvm6.Q
open LeanVM.Parameters LeanVM.Protocol

/-! ## The rows -/

theorem split6 : ksSplitN 13 10 = 7168 := by decide

theorem nStepRowsC_eq : nStepRowsC = 352 := by decide

/-- **The node's continuation rows**: the trace `[1, B)`, `σ'`'s key leaf, `σ_leaf`'s key leaf. -/
theorem mem_rows6 {B i : ℕ} :
    i ∈ rowsBK2 B 7567 8032 ↔ (1 ≤ i ∧ i < B) ∨ (7568 ≤ i ∧ i < 7599) ∨ (8033 ≤ i ∧ i < 8064) := by
  simp only [rowsBK2, Lvm.Q2.rowsBK, List.mem_append, List.mem_map, List.mem_range]
  constructor
  · rintro ((⟨a, ha, rfl⟩ | ⟨a, ha, rfl⟩) | ⟨a, ha, rfl⟩) <;> omega
  · rintro (h | h | h)
    · exact Or.inl (Or.inl ⟨i - 1, by omega, by omega⟩)
    · exact Or.inl (Or.inr ⟨i - 7568, by omega, by omega⟩)
    · exact Or.inr ⟨i - 8033, by omega, by omega⟩

/-- **`B` at `P17`** (FORMAT6 v2.6 §6.3; P17-freeze §1.3). -/
theorem blocks_P17 : hashedLen6 (planOf Lvm6.P17) = 518928 ∧
    Lvm.KSponge.nBlk (hashedLen6 (planOf Lvm6.P17)) = 3816 := by
  rw [Lvm6.planOf_P17_eq]
  decide +kernel

/-- **K1's sponge relations are a sponge table.** -/
theorem spongeRel6 {ks : ℕ → K} {Yl msg : ℕ → ℕ → K} {rows : List ℕ} (hout : OutRel 13 25 ks Yl)
    (hlink : SpongeLink 13 rows ks (fun i l ↦ Yl l i) msg) (h0 : 0 ∉ rows) :
    SpongeRel 13 ks (fun i l ↦ Yl l i) msg (fun i ↦ decide (i ∈ rows)) where
  out i hi l hl := hout l hl i hi
  link i hi l hl := by simpa using hlink i hi l hl
  cont0 := by simpa using h0

/-! ## The trace digest -/

theorem byteW_lane6 (x : K) {k : ℕ} (hk : k < 8) :
    (x.lane >>> (8 * k).toUInt64).toUInt8 = (x.toBitVec.toNat / 256 ^ k).toUInt8 :=
  Lvm.Wots.byteW_toNat _ hk

/-- **Byte `p` of the stream is byte `p mod 136` of row `p / 136`** (below the split). -/
theorem msgBytes_stream6 {M X : ℕ → ℕ → K} {ws : List Word}
    (hM : ∀ i < 7168, ∀ l < 17, (M i l).toBitVec.toNat = lw ws (17 * i + l)) {p : ℕ} (hp : p / 136 < 7168) :
    msgBytes (ksMsg 7168 M X) (p / 136) (p % 136) = (wordsBytes ws).getD p 0 := by
  have hl : p % 136 / 8 < 17 := by omega
  have hb : p % 136 % 8 < 8 := Nat.mod_lt _ (by norm_num)
  have e1 : p = 8 * (17 * (p / 136) + p % 136 / 8) + p % 136 % 8 := by omega
  conv_rhs => rw [e1]
  rw [byte_of_lane _ _ _ hb, toUInt8_mod, ← hM _ hp _ hl]
  simp only [msgBytes, ksMsg, if_pos hp]
  exact byteW_lane6 _ hb

theorem padAt_eq6 (L p : ℕ) : Lvm.QLink.padAt L p = Lvm.KSponge.padAt L p := rfl

theorem nBlk_eq6 (L : ℕ) : Lvm.QLink.nBlk L = Lvm.KSponge.nBlk L := rfl

/-- **CB-4, the trace digest**: row `B − 1` of the node's sponge block outputs the child's trace
digest. -/
theorem traceDigest6 {B : ℕ} (hB : B ≤ 7168) {ks : ℕ → K} {Yl M X : ℕ → ℕ → K}
    (hout : OutRel 13 25 ks Yl)
    (hlink : SpongeLink 13 (rowsBK2 B 7567 8032) ks (fun i l ↦ Yl l i) (ksMsg 7168 M X))
    {P : List PE6} {c : RecursionFast.Digest} {ws : List Word} (hS : streamOkL6 P = true) (hP : 0 < P.length)
    (hL : LaneLink6 P c ws) (hpad : PadOkB (wordsBytes ws) (hashedLen6 P))
    (hBL : B = Lvm.KSponge.nBlk (hashedLen6 P))
    (hM : ∀ i < 7168, ∀ l < 17, (M i l).toBitVec.toNat = lw ws (17 * i + l)) :
    Lvm.KSponge.stDigest (yState (fun i l ↦ Yl l i) (B - 1)) = traceDigest (decode6 P ws) := by
  have hnb : Lvm.KSponge.nBlk (hashedLen6 P) = hashedLen6 P / 136 + 1 := rfl
  have H := spongeRel6 hout hlink (by rw [mem_rows6]; omega)
  have hS' := stream_of_laneLink6 hS hP hL
  have hsz : hashedLen6 P ≤ (wordsBytes ws).length := by rw [wordsBytes_length]; exact hL.size
  have hin : ∀ i, 0 < i → i < Lvm.KSponge.nBlk (hashedLen6 P) →
      decide (i ∈ rowsBK2 B 7567 8032) = true :=
    fun i h1 h2 ↦ by simp only [decide_eq_true_eq, mem_rows6]; omega
  rw [hBL]
  refine traceDigest_of_KS 13 ks _ _ _ H (hashedLen6 P) (by norm_num; omega) hin ?_ _ ?_
  · intro p h1 h2
    have h2' : p < 136 * Lvm.KSponge.nBlk (hashedLen6 P) := h2
    rw [show p / RecursionFast.Keccak.rate = p / 136 from rfl,
      show p % RecursionFast.Keccak.rate = p % 136 from rfl, msgBytes_stream6 hM (by omega), ← padAt_eq6]
    exact hpad p h1 (by rw [nBlk_eq6]; omega)
  · rw [← hS']
    refine List.ext_getElem (by rw [Lvm.KSponge.streamOf_length, List.length_take]; omega) fun p h1 h2 ↦ ?_
    have hp : p < hashedLen6 P := by rw [Lvm.KSponge.streamOf_length] at h1; exact h1
    simp only [Lvm.KSponge.streamOf, List.getElem_ofFn, List.getElem_take]
    rw [show p / RecursionFast.Keccak.rate = p / 136 from rfl,
      show p % RecursionFast.Keccak.rate = p % 136 from rfl, msgBytes_stream6 hM (by omega),
      List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by omega), Option.getD_some]

/-! ## `Q_sig`'s `KS` hypotheses -/

/-- **Four cells holding a row's output lanes 0–3 are its digest.** -/
theorem digAt_of_cells6 {v : ℕ → FK} {a : ℕ} {Yt : ℕ → ℕ → K} {i : ℕ}
    (h : ∀ l < 4, v (a + l) = FK.ofBF64 (Yt i l)) : digAt v a = Lvm.KSponge.stDigest (yState Yt i) := by
  apply Vector.ext
  intro e he
  rw [digAt, Lvm.Wots.digOfW_get _ he, Lvm.KSponge.stDigest_getElem _ he]
  simp only [yState, Vector.getElem_ofFn]
  rw [h _ (by omega)]
  rfl

/-- A row from the split absorbs the `X` cells. -/
theorem xorMsg_cells6 {M X : ℕ → ℕ → K} {v : ℕ → FK} {f : ℕ → ℕ} {i : ℕ} (hi : 7168 ≤ i)
    (h : ∀ l < 17, v (f l) = FK.ofBF64 (X (i - 7168) l)) (a : RecursionFast.Keccak.State) :
    Lvm.KSponge.xorMsg a (Lvm.Wots.laneByte (lanesW v f)) = Lvm.KSponge.xorMsg a (msgBytes (ksMsg 7168 M X) i) := by
  have e : Lvm.KSponge.rateArr (Lvm.Wots.laneByte (lanesW v f)) =
      Lvm.KSponge.rateArr (msgBytes (ksMsg 7168 M X) i) := by
    unfold Lvm.KSponge.rateArr
    congr 1
    funext j
    have hj : j.val < 136 := j.2
    simp only [Lvm.Wots.laneByte, lanesW, msgBytes, ksMsg, if_neg (show ¬ i < 7168 by omega)]
    rw [h _ (by omega)]
    rfl
  simp only [Lvm.KSponge.xorMsg, e]

variable {B : ℕ} {ks : ℕ → K} {Yl M X : ℕ → ℕ → K} {v : ℕ → FK}

/-- **CB-4, `σ'`'s `KS` rows** (`X` rows `0 … 448` at sponge rows `7,168 + r`). -/
theorem sigKSin6 (hB : B ≤ 7168) (hout : OutRel 13 25 ks Yl)
    (hlink : SpongeLink 13 (rowsBK2 B 7567 8032) ks (fun i l ↦ Yl l i) (ksMsg 7168 M X)) {I : SigIn}
    (hx : ∀ r < 449, ∀ l < 17, v (I.xs + 17 * r + l) = FK.ofBF64 (X r l))
    (hys : ∀ r < 399, ∀ l < 4, v (I.ys + 4 * r + l) = FK.ofBF64 (Yl l (7168 + r)))
    (hyc : ∀ t ≤ 16, ∀ l < 4, v (I.yc + 4 * t + l) = FK.ofBF64 (Yl l (7168 + 430 + t)))
    (hyls : ∀ l < 4, v (I.yls + l) = FK.ofBF64 (Yl l (7168 + 447)))
    (hyns : ∀ l < 4, v (I.yns + l) = FK.ofBF64 (Yl l (7168 + 448))) :
    SigKSin I v := by
  have H := spongeRel6 hout hlink (by rw [mem_rows6]; omega)
  have hrow : ∀ r < 449, 7168 + r < 2 ^ 13 := fun r hr ↦ by norm_num; omega
  have hcF : ∀ r, r < 449 → ¬ (400 ≤ r ∧ r ≤ 430) → decide (7168 + r ∈ rowsBK2 B 7567 8032) = false :=
    fun r h1 h2 ↦ by simp only [decide_eq_false_iff_not, mem_rows6]; omega
  have hcT : ∀ r, 400 ≤ r → r ≤ 430 → decide (7168 + r ∈ rowsBK2 B 7567 8032) = true :=
    fun r h1 h2 ↦ by simp only [decide_eq_true_eq, mem_rows6]; omega
  have hxr : ∀ r < 449, ∀ l < 17, v (I.xs + 17 * r + l) = FK.ofBF64 (X (7168 + r - 7168) l) :=
    fun r hr l hl ↦ by rw [Nat.add_sub_cancel_left]; exact hx r hr l hl
  have one : ∀ r < 449, ¬ (400 ≤ r ∧ r ≤ 430) → ∀ y, (∀ l < 4, v (y + l) = FK.ofBF64 (Yl l (7168 + r))) →
      OneHash v (fun l ↦ I.xs + 17 * r + l) y := fun r hr hn y hy ↦
    ⟨yState (fun i l ↦ Yl l i) (7168 + r), by
      rw [xorMsg_cells6 (M := M) (by omega) (hxr r hr)]
      exact oneRow_perm 13 ks _ _ _ H (hrow r hr) (hcF r hr hn), digAt_of_cells6 hy⟩
  refine ⟨fun r hr ↦ one r (by omega) (by omega) _ (hys r hr), ?_, fun t ht ↦ ?_,
    one 447 (by norm_num) (by norm_num) _ hyls, one 448 (by norm_num) (by norm_num) _ hyns⟩
  · refine ⟨fun u ↦ prevState (fun i l ↦ Yl l i) (fun i ↦ decide (i ∈ rowsBK2 B 7567 8032)) (7168 + (399 + u)),
      fun u ↦ yState (fun i l ↦ Yl l i) (7168 + (399 + u)), ?_, fun u hu ↦ ?_, fun u hu ↦ ?_, ?_⟩
    · simp only [prevState, Nat.add_zero, hcF 399 (by norm_num) (by norm_num)]
      rfl
    · rw [xorMsg_cells6 (M := M) (by omega) (hxr (399 + u) (by omega))]
      exact row_perm 13 ks _ _ _ H (hrow _ (by omega))
    · simp only [prevState, hcT (399 + (u + 1)) (by omega) (by omega), if_true]
      congr 1
    · refine digAt_of_cells6 fun l hl ↦ ?_
      have := hyc 0 (by norm_num) l hl
      simpa using this
  · refine one (431 + t) (by omega) (by omega) _ fun l hl ↦ ?_
    have := hyc (t + 1) (by omega) l hl
    rw [show 7168 + 430 + (t + 1) = 7168 + (431 + t) by omega] at this
    exact this

/-- **CB-4, `σ_leaf`'s `KS` rows** (`X` rows `512 … 911` at sponge rows `7,680 + r`). -/
theorem sigKSinC6 (hB : B ≤ 7168) (hout : OutRel 13 25 ks Yl)
    (hlink : SpongeLink 13 (rowsBK2 B 7567 8032) ks (fun i l ↦ Yl l i) (ksMsg 7168 M X)) {Il : SigIn}
    (hx : ∀ r < 400, ∀ l < 17, v (Il.xs + 17 * r + l) = FK.ofBF64 (X (512 + r) l))
    (hys : ∀ r < 352, ∀ l < 4, v (Il.ys + 4 * r + l) = FK.ofBF64 (Yl l (7680 + r)))
    (hyc : ∀ t ≤ 16, ∀ l < 4, v (Il.yc + 4 * t + l) = FK.ofBF64 (Yl l (7680 + 383 + t))) :
    SigKSinC Il v := by
  have H := spongeRel6 hout hlink (by rw [mem_rows6]; omega)
  have hrow : ∀ r < 400, 7680 + r < 2 ^ 13 := fun r hr ↦ by norm_num; omega
  have hcF : ∀ r, r < 400 → ¬ (353 ≤ r ∧ r ≤ 383) → decide (7680 + r ∈ rowsBK2 B 7567 8032) = false :=
    fun r h1 h2 ↦ by simp only [decide_eq_false_iff_not, mem_rows6]; omega
  have hcT : ∀ r, 353 ≤ r → r ≤ 383 → decide (7680 + r ∈ rowsBK2 B 7567 8032) = true :=
    fun r h1 h2 ↦ by simp only [decide_eq_true_eq, mem_rows6]; omega
  have hxr : ∀ r < 400, ∀ l < 17, v (Il.xs + 17 * r + l) = FK.ofBF64 (X (7680 + r - 7168) l) :=
    fun r hr l hl ↦ by rw [show 7680 + r - 7168 = 512 + r by omega]; exact hx r hr l hl
  have one : ∀ r < 400, ¬ (353 ≤ r ∧ r ≤ 383) → ∀ y, (∀ l < 4, v (y + l) = FK.ofBF64 (Yl l (7680 + r))) →
      OneHash v (fun l ↦ Il.xs + 17 * r + l) y := fun r hr hn y hy ↦
    ⟨yState (fun i l ↦ Yl l i) (7680 + r), by
      rw [xorMsg_cells6 (M := M) (by omega) (hxr r hr)]
      exact oneRow_perm 13 ks _ _ _ H (hrow r hr) (hcF r hr hn), digAt_of_cells6 hy⟩
  have e := nStepRowsC_eq
  refine ⟨fun r hr ↦ ?_, ?_, fun t ht ↦ ?_⟩
  · rw [e] at hr
    exact one r (by omega) (by omega) _ (hys r hr)
  · refine ⟨fun u ↦ prevState (fun i l ↦ Yl l i) (fun i ↦ decide (i ∈ rowsBK2 B 7567 8032)) (7680 + (352 + u)),
      fun u ↦ yState (fun i l ↦ Yl l i) (7680 + (352 + u)), ?_, fun u hu ↦ ?_, fun u hu ↦ ?_, ?_⟩
    · simp only [prevState, Nat.add_zero, hcF 352 (by norm_num) (by norm_num)]
      rfl
    · rw [e, xorMsg_cells6 (M := M) (by omega) (hxr (352 + u) (by omega))]
      exact row_perm 13 ks _ _ _ H (hrow _ (by omega))
    · simp only [prevState, hcT (352 + (u + 1)) (by omega) (by omega), if_true]
      congr 1
    · refine digAt_of_cells6 fun l hl ↦ ?_
      have := hyc 0 (by norm_num) l hl
      simpa using this
  · rw [e]
    refine one (352 + 32 + t) (by omega) (by omega) _ fun l hl ↦ ?_
    have := hyc (t + 1) (by omega) l hl
    rw [show 7680 + 383 + (t + 1) = 7680 + (352 + 32 + t) by omega] at this
    exact this

end Lvm6.QK.W
