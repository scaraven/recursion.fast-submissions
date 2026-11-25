-- lvm6 DP6 (X9 §3 item 1): level 0's transition `tr0IR = expIR ; trIR` (the K→E2 expansion of the committed rows,
-- then the fold chain and the round tables) as one part within `trCap`, its semantics from the committed rows, and
-- the transitions' size caps (`LevelSz.tr`). New.
import Lvm6XDescTr
import Lvm6XDescL0

/-!
# Level 0's transition as one part

* **`tr0IR h base bf ch tb tS`** `= expIR h base (bf 0) ; trIR h 0 6 bf ch tb tS`: buffer `0` is the expansion of the
  rows at `base` (46 `K` words a position), then six folds and the tables.
* **`tr0IR_part`** (`h ≤ 21`): `PartOk … trCap` (`37 + 1955·2^21 + 6·(43 + 152·2^27) + 279 ≈ 2^36.85 < 2^38`).
* **`sizeIR_trIR_le`** / **`sizeIR_tr0IR_le`**: `≤ trSz = 2^13` for `j ≤ 6` (`LevelSz.tr` at every level).
* **`tr0IR_sem`**: from the committed rows (W1's `wordE true 0 6 h cs`), the chain's words, the tables, `Inv`, the
  output and the heap outside the buffers and tables (X9's `trIR_sem` with `expIR_holds_wordE` for its `hW`).
-/

set_option autoImplicit false

namespace Lvm6.X

open RecursionFast Lvm.X Lvm.Nb Lvm6.FD Finset Lvm6.Whir LeanVM.Parameters LeanVM.Protocol.Whir

/-- **Level 0's transition**: the expansion into buffer `0`, then `trIR` with `m = 0`, `j = 6`. -/
def tr0IR (h base : ℕ) (bf ch : ℕ → ℕ) (tb tS : ℕ) : XIR :=
  .seq (expIR h base (bf 0)) (trIR h 0 6 bf ch tb tS)

theorem noLoopT_expIR (h base buf : ℕ) : NoLoopT (expIR h base buf) :=
  ⟨noLoopT_zeroIR .., noLoopT_sIR _, by simp [expOut, expIn, NoLoopT, noLoopT_sIR]⟩

theorem outs_expIR (h base buf t : ℕ) : outs (expIR h base buf) t = 0 := by
  simp [expIR, expOut, expIn, outs, outs_sIR, outs_zeroIR]

/-- **Level 0's transition within `trCap`.** -/
theorem tr0IR_part (h base : ℕ) (bf ch : ℕ → ℕ) (tb tS : ℕ) (hh : h ≤ 21) :
    PartOk (tr0IR h base bf ch tb tS) trCap where
  wf := ⟨wf_expIR .., (trIR_part h 0 6 bf ch tb tS (by omega) le_rfl).wf⟩
  noLoopT := ⟨noLoopT_expIR .., (trIR_part h 0 6 bf ch tb tS (by omega) le_rfl).noLoopT⟩
  outs t := by
    simp only [tr0IR, outs, outs_expIR, (trIR_part h 0 6 bf ch tb tS (by omega) le_rfl).outs t, Nat.add_zero]
  cost t := by
    have hp : 2 ^ h ≤ 2 ^ 21 := Nat.pow_le_pow_right (by norm_num) hh
    have hp' : 2 ^ (h + (0 + 6)) ≤ 2 ^ 27 := Nat.pow_le_pow_right (by norm_num) (by omega)
    have e1 := cost_expIR h base (bf 0) t (by
      have : (128 : ℕ) * 2 ^ 21 < 2 ^ 64 := by norm_num
      omega)
    have c1 := cost_foldsIR_le h t 0 6 bf ch (by omega)
    have c2 := (part_tabsIR 6 0 tb tS bf t 6).2.2.2
    simp only [tr0IR, trIR, cost, trCap]
    have e : (2 : ℕ) ^ 38 = 274877906944 := by norm_num
    have e' : (2 : ℕ) ^ 27 = 134217728 := by norm_num
    have e'' : (2 : ℕ) ^ 21 = 2097152 := by norm_num
    rw [e]; rw [e'] at hp'; rw [e''] at hp
    omega

/-! ## Sizes -/

theorem sizeIR_foldsIR (h : ℕ) : ∀ m j (bf ch : ℕ → ℕ), sizeIR (foldsIR h m j bf ch) = 1 + 197 * j
  | _, 0, _, _ => by simp [foldsIR, sizeIR, blkSteps]
  | m, j + 1, bf, ch => by
    simp only [foldsIR, sizeIR, sizeIR_foldIR, sizeIR_foldsIR h m j]
    ring

theorem sizeIR_wrsIR : ∀ l : List (ℕ × ℕ), sizeIR (wrsIR l) = 1 + 12 * l.length
  | [] => by simp [wrsIR, sizeIR, blkSteps]
  | (a, v) :: l => by
    simp only [wrsIR, wrIR, sizeIR, sizeIR_sIR, sSize, sizeIR_wrsIR l, List.length_cons]
    ring

theorem sizeIR_tabsIR (j m tb tS : ℕ) (bf : ℕ → ℕ) : ∀ n, sizeIR (tabsIR j m tb tS bf n) = 1 + 50 * n
  | 0 => by simp [tabsIR, sizeIR, blkSteps]
  | n + 1 => by
    simp only [tabsIR, sizeIR, sizeIR_tabsIR j m tb tS bf n, sizeIR_wrsIR, tabL, List.length_cons,
      List.length_nil]
    ring

/-- **A transition's size** (`LevelSz.tr` for `trIR`, `j ≤ 6`). -/
theorem sizeIR_trIR_le (h m j : ℕ) (bf ch : ℕ → ℕ) (tb tS : ℕ) (hj : j ≤ 6) :
    sizeIR (trIR h m j bf ch tb tS) ≤ trSz := by
  simp only [trIR, sizeIR, sizeIR_foldsIR, sizeIR_tabsIR, trSz]
  have : (2 : ℕ) ^ 13 = 8192 := by norm_num
  omega

theorem sizeIR_expIR (h base buf : ℕ) : sizeIR (expIR h base buf) = 86 := rfl

/-- **Level 0's transition's size** (`LevelSz.tr`). -/
theorem sizeIR_tr0IR_le (h base : ℕ) (bf ch : ℕ → ℕ) (tb tS : ℕ) : sizeIR (tr0IR h base bf ch tb tS) ≤ trSz := by
  simp only [tr0IR, sizeIR, sizeIR_expIR h base (bf 0), trIR, sizeIR_foldsIR, sizeIR_tabsIR, trSz]
  have : (2 : ℕ) ^ 13 = 8192 := by norm_num
  omega

/-! ## Semantics -/

/-- **Level 0's transition on the machine**: from the committed rows (word `t` of row `p` at `base + 46p + t`, W1's
`wordE true 0 6 h cs` when commitment `0` has height `h` and padded rows), the chain's words from buffer `0`, the
tables, `Inv`, no output, the size, and the heap outside buffers `0..6` and the tables. -/
theorem tr0IR_sem (I : Array Word) {h : ℕ} (hh : h ≤ 64) {base : ℕ} {bf ch : ℕ → ℕ} {tb tS : ℕ}
    (l : List (E2 × E2)) (s : St) (hM : Inv s.M)
    (hb : regs ≤ base) (hb2 : base + 46 * 2 ^ h < 2 ^ 64)
    (hdis0 : base + 46 * 2 ^ h ≤ bf 0 ∨ bf 0 + 128 * 2 ^ h ≤ base)
    (row : ℕ → List BF64) (hrow : ∀ p < 2 ^ h, ∀ t < 46, rdK s.M (base + 46 * p + t) = (row p).getD t 0)
    {cs : List (ℕ × ℕ × LeanVM.Protocol.Compile.Word)} {c : ℕ × ℕ × LeanVM.Protocol.Compile.Word}
    (hc : cs[0]? = some c) (hc1 : c.1 = h) (hcr : ∀ p < 2 ^ h, c.2.2 p = List.replicate 18 0 ++ row p)
    (hB : ∀ k ≤ 6, regs ≤ bf k ∧ bf k + bsz h 0 6 k < 2 ^ 64 ∧ bf k + bsz h 0 6 k ≤ s.M.size)
    (hC : ∀ k < 6, regs ≤ ch k ∧ ch k + 4 < 2 ^ 64)
    (hD : ∀ k ≤ 6, ∀ k' ≤ 6, k ≠ k' → bf k + bsz h 0 6 k ≤ bf k' ∨ bf k' + bsz h 0 6 k' ≤ bf k)
    (hDC : ∀ k < 6, ∀ k' ≤ 6, ch k + 4 ≤ bf k' ∨ bf k' + bsz h 0 6 k' ≤ ch k)
    (htb : regs ≤ tb) (htS : regs ≤ tS) (hd : tb + 2 * 6 ≤ tS ∨ tS + 2 * 6 ≤ tb) (h64 : tb + 2 * 6 < 2 ^ 64)
    (h64' : tS + 2 * 6 < 2 ^ 64) (hs1 : tb + 2 * 6 ≤ s.M.size) (hs2 : tS + 2 * 6 ≤ s.M.size)
    (hDT : ∀ k ≤ 6, (tb + 2 * 6 ≤ bf k ∨ bf k + bsz h 0 6 k ≤ tb) ∧ (tS + 2 * 6 ≤ bf k ∨ bf k + bsz h 0 6 k ≤ tS))
    (hch : ∀ k < 6, rdE2 s.M (ch k) = (l.getD k (0, 0)).1 ∧ rdE2 s.M (ch k + 2) = (l.getD k (0, 0)).2) :
    let s' := semXIR I (tr0IR h base bf ch tb tS) s
    ChainW s'.M h hh 0 6 bf l (Lvm6.Whir.wordE true 0 (0 + 6) h cs) ∧ TabW s'.M 6 0 tb tS bf 6 ∧ Inv s'.M ∧
      s'.o = s.o ∧ s'.M.size = s.M.size ∧
      ∀ x, regs ≤ x → (∀ k ≤ 6, x < bf k ∨ bf k + bsz h 0 6 k ≤ x) →
        (x < tb ∨ tb + 2 * 6 ≤ x) → (x < tS ∨ tS + 2 * 6 ≤ x) → rd s'.M x = rd s.M x := by
  intro s'
  have e0 : bsz h 0 6 0 = 128 * 2 ^ h := by
    rw [bsz, show h + (0 + 6 - 0) = h + 6 by omega, pow_add]; ring
  obtain ⟨b0, b0', b0s⟩ := hB 0 (by omega)
  rw [e0] at b0' b0s
  obtain ⟨x1, x2, x3, x4⟩ := expIR_sem I s hM hb hb2 b0 b0' b0s hdis0
  have hW := expIR_holds_wordE I s hM hb hb2 b0 b0' b0s hdis0 row hrow hc hc1 hcr
  have z1 := size_sem I (expIR h base (bf 0)) s
  simp only [s', tr0IR, semXIR_seq]
  generalize semXIR I (expIR h base (bf 0)) s = s1 at x1 x2 x3 x4 hW z1
  have hch1 : ∀ k < 6, rdE2 s1.M (ch k) = (l.getD k (0, 0)).1 ∧
      rdE2 s1.M (ch k + 2) = (l.getD k (0, 0)).2 := by
    intro k hk
    obtain ⟨c0, -⟩ := hC k hk
    have hd0 := hDC k hk 0 (by omega)
    rw [e0] at hd0
    simp only [regs] at c0
    have fr : ∀ i < 4, rd s1.M (ch k + i) = rd s.M (ch k + i) := fun i hi ↦
      x4 _ (by simp only [regs]; omega) (by omega)
    obtain ⟨e1, e2⟩ := hch k hk
    refine ⟨(rdE2_of_frame (by simpa using fr 0 (by omega)) (fr 1 (by omega))).trans e1, ?_⟩
    exact (rdE2_of_frame (fr 2 (by omega)) (by rw [Nat.add_assoc]; exact fr 3 (by omega))).trans e2
  obtain ⟨a1, a2, a3, a4, a5, a6⟩ := trIR_sem I hh (m := 0) (j := 6) (bf := bf) (ch := ch) l
    (Lvm6.Whir.wordE true 0 (0 + 6) h cs) s1 x1 (by omega)
    (fun k hk ↦ by obtain ⟨y1, y2, y3⟩ := hB k hk; exact ⟨y1, y2, by rw [z1]; exact y3⟩) hC hD
    (fun k hk k' _ hk' ↦ hDC k hk k' hk') htb htS hd h64 h64' (by rw [z1]; exact hs1) (by rw [z1]; exact hs2)
    hDT hW hch1
  refine ⟨a1, a2, a3, a4.trans x2, a5.trans z1, fun x hx hk h1 h2 ↦ ?_⟩
  rw [a6 x hx (fun k hk1 hk2 ↦ hk k hk2) h1 h2]
  have := hk 0 (by omega)
  rw [e0] at this
  exact x4 x hx this

end Lvm6.X
