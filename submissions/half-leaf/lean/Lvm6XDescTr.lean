-- lvm6 X9 (X8a §3 item 4, M4): a level's transition `trIR`: the fold chain (`foldIR` per round, buffer `k` to
-- buffer `k + 1`, W1's `foldQ` at `domE`) and the round tables the loaders (`ldF`, table `tb`) and the builder
-- (`sbIR`, table `tS`) read; `levelX_sem_tr` discharges `levelX_sem`'s transition hypothesis. New.
import Lvm6XDescGroups

/-!
# A level's transition: the fold chain and the round tables

* **`foldsIR h m j bf ch`**: `j` folds, fold `k` reads buffer `bf k` (a word on `m + j − k` lane variables,
  position-major, `HoldsW`) and the challenge pair at `ch k`, and writes buffer `bf (k + 1)`.
  **`ChainW`**: buffer `k` holds the word folded by the first `k` challenges (the shape of X4's `foldsQX`).
  **`foldsIR_sem`**: `ChainW` after the chain, `Inv`, no output, the heap outside buffers `1..j` kept.
* **`wrsIR`** (stores of constants), **`tabsIR`**: round `r`'s entries (decode order: round `0` is the most folded
  word): `tb + 2r ↦ (bf (j−1−r), 2·2^(m+1+r))` (the unfolded word, for `ldF`), `tS + 2r ↦ (bf (j−r), 2·2^(m+r))` (the
  folded word, for `sbIR`). **`TabW`**, **`tabsIR_sem`**, **`TabW.entries`** (the entries as `tbBase`/`tbOcc`).
* **`trIR`** `= foldsIR ; tabsIR`; **`trIR_sem`**; **`levelX_sem_tr`**: `levelX_sem` with `L.tr = trIR …` and
  `M₀` = the heap after the transition, from `Q 0` of any state with the chain and the tables.
-/

set_option autoImplicit false

namespace Lvm6.X

open RecursionFast Lvm.X Lvm.Nb Lvm6.FD Finset Lvm6.Whir LeanVM.Parameters LeanVM.Protocol.Whir

attribute [local irreducible] entryK storeM

/-! ## Words under a heap frame -/

theorem rdE2_of_frame {M M' : Mem} {a : ℕ} (h0 : rd M' a = rd M a) (h1 : rd M' (a + 1) = rd M (a + 1)) :
    rdE2 M' a = rdE2 M a := by
  simp only [rdE2, rdK, h0, h1]

theorem HoldsW.of_frame {M M' : Mem} {buf h m : ℕ} {W : Wd E2 (2 ^ h) m} (hW : HoldsW M buf h m W)
    (hf : ∀ x, buf ≤ x → x < buf + 2 * 2 ^ (h + m) → rd M' x = rd M x) : HoldsW M' buf h m W := by
  intro p u
  have hu := bitsToNat_lt u
  have hp := p.isLt
  have hk : (p : ℕ) * 2 ^ m + bitsToNat u < 2 ^ (h + m) := by
    rw [pow_add]
    have : ((p : ℕ) + 1) * 2 ^ m ≤ 2 ^ h * 2 ^ m := Nat.mul_le_mul_right _ hp
    rw [Nat.add_mul, one_mul] at this
    omega
  rw [← hW p u]
  exact rdE2_of_frame (hf _ (by omega) (by omega)) (hf _ (by omega) (by omega))

/-! ## The fold chain -/

/-- **`j` folds**: buffer `bf k` (on `m + j − k` lane variables) to `bf (k + 1)`, challenge pair at `ch k`. -/
def foldsIR (h : ℕ) : (m j : ℕ) → (bf ch : ℕ → ℕ) → XIR
  | _, 0, _, _ => .blk []
  | m, j + 1, bf, ch => .seq (foldIR h (m + j) (bf 0) (bf 1) (ch 0))
      (foldsIR h m j (fun k ↦ bf (k + 1)) (fun k ↦ ch (k + 1)))

/-- **The chain's words**: buffer `k` holds the word folded by the first `k` challenges (X4's `foldsQX`). -/
def ChainW (M : Mem) (h : ℕ) (hh : h ≤ 64) : (m j : ℕ) → (bf : ℕ → ℕ) → List (E2 × E2) →
    Wd E2 (2 ^ h) (m + j) → Prop
  | m, 0, bf, _, W => HoldsW M (bf 0) h m W
  | m, j + 1, bf, ch, W => HoldsW M (bf 0) h (m + j + 1) W ∧
      ChainW M h hh m j (fun k ↦ bf (k + 1)) ch.tail (foldQ (domE h hh) (ch.headD (0, 0)).1 (ch.headD (0, 0)).2 W)

/-- Buffer `k`'s size (words) in a chain of `j` folds down to `m` lane variables. -/
def bsz (h m j k : ℕ) : ℕ := 2 * 2 ^ (h + (m + j - k))

theorem bsz_zero (h m j : ℕ) : bsz h m (j + 1) 0 = 4 * 2 ^ (h + (m + j)) := by
  rw [bsz, show h + (m + (j + 1) - 0) = h + (m + j) + 1 by omega, pow_succ]; ring

theorem bsz_one (h m j : ℕ) : bsz h m (j + 1) 1 = 2 * 2 ^ (h + (m + j)) := by
  rw [bsz, show m + (j + 1) - 1 = m + j by omega]

theorem bsz_succ (h m j k : ℕ) : bsz h m (j + 1) (k + 1) = bsz h m j k := by
  rw [bsz, bsz, show m + (j + 1) - (k + 1) = m + j - k by omega]

theorem getD_tail' {α : Type} (l : List α) (d : α) (k : ℕ) : l.tail.getD k d = l.getD (k + 1) d := by
  cases l <;> simp

theorem headD_eq_getD {α : Type} (l : List α) (d : α) : l.headD d = l.getD 0 d := by
  cases l <;> simp

/-- **The fold chain on the machine.** -/
theorem foldsIR_sem (I : Array Word) {h : ℕ} (hh : h ≤ 64) (m : ℕ) :
    ∀ (j : ℕ) (bf ch : ℕ → ℕ) (l : List (E2 × E2)) (W : Wd E2 (2 ^ h) (m + j)) (s : St), Inv s.M →
      m + j < 64 →
      (∀ k ≤ j, regs ≤ bf k ∧ bf k + bsz h m j k < 2 ^ 64 ∧ bf k + bsz h m j k ≤ s.M.size) →
      (∀ k < j, regs ≤ ch k ∧ ch k + 4 < 2 ^ 64) →
      (∀ k ≤ j, ∀ k' ≤ j, k ≠ k' → bf k + bsz h m j k ≤ bf k' ∨ bf k' + bsz h m j k' ≤ bf k) →
      (∀ k < j, ∀ k', 1 ≤ k' → k' ≤ j → ch k + 4 ≤ bf k' ∨ bf k' + bsz h m j k' ≤ ch k) →
      HoldsW s.M (bf 0) h (m + j) W →
      (∀ k < j, rdE2 s.M (ch k) = (l.getD k (0, 0)).1 ∧ rdE2 s.M (ch k + 2) = (l.getD k (0, 0)).2) →
      ChainW (semXIR I (foldsIR h m j bf ch) s).M h hh m j bf l W ∧ Inv (semXIR I (foldsIR h m j bf ch) s).M ∧
        (semXIR I (foldsIR h m j bf ch) s).o = s.o ∧
        (semXIR I (foldsIR h m j bf ch) s).M.size = s.M.size ∧
        ∀ x, regs ≤ x → (∀ k, 1 ≤ k → k ≤ j → x < bf k ∨ bf k + bsz h m j k ≤ x) →
          rd (semXIR I (foldsIR h m j bf ch) s).M x = rd s.M x
  | 0, bf, ch, l, W, s, hM, _, _, _, _, _, hW, _ => ⟨hW, hM, rfl, rfl, fun _ _ _ ↦ rfl⟩
  | j + 1, bf, ch, l, W, s, hM, hm, hB, hC, hD, hDC, hW, hch => by
    have hs := hM.1
    simp only [regs] at hs
    obtain ⟨b0, b0', b0s⟩ := hB 0 (by omega)
    obtain ⟨b1, b1', b1s⟩ := hB 1 (by omega)
    rw [bsz_zero] at b0' b0s
    rw [bsz_one] at b1' b1s
    obtain ⟨c0, c0'⟩ := hC 0 (by omega)
    have d01 := hD 0 (by omega) 1 (by omega) (by omega)
    rw [bsz_zero, bsz_one] at d01
    have dc := hDC 0 (by omega) 1 le_rfl (by omega)
    rw [bsz_one] at dc
    obtain ⟨hα, hβ⟩ := hch 0 (by omega)
    rw [← headD_eq_getD] at hα hβ
    -- the first fold
    have H1 := foldIR_holds I s hM hh (m := m + j) (by omega) b0 (by omega) c0 c0' b1 b1' b1s (by omega) dc hW hα hβ
    obtain ⟨-, f2, f3, f4⟩ := foldIR_sem I s hM (h := h) (m := m + j) (inB := bf 0) (outB := bf 1) (chA := ch 0)
      (by omega) b0 (by omega) c0 c0' b1 b1' b1s (by omega) dc
    have z1 := size_sem I (foldIR h (m + j) (bf 0) (bf 1) (ch 0)) s
    simp only [foldsIR, semXIR_seq]
    generalize semXIR I (foldIR h (m + j) (bf 0) (bf 1) (ch 0)) s = s1 at H1 f2 f3 f4 z1
    -- the rest
    obtain ⟨g1, g2, g3, g4, g5⟩ := foldsIR_sem I hh m j (fun k ↦ bf (k + 1)) (fun k ↦ ch (k + 1)) l.tail _ s1 f3
      (by omega)
      (fun k hk ↦ by
        obtain ⟨x1, x2, x3⟩ := hB (k + 1) (by omega)
        rw [bsz_succ] at x2 x3
        exact ⟨x1, x2, by rw [z1]; exact x3⟩)
      (fun k hk ↦ hC (k + 1) (by omega))
      (fun k hk k' hk' hne ↦ by
        have := hD (k + 1) (by omega) (k' + 1) (by omega) (by omega)
        rwa [bsz_succ, bsz_succ] at this)
      (fun k hk k' hk1 hk' ↦ by
        have := hDC (k + 1) (by omega) (k' + 1) (by omega) (by omega)
        rwa [bsz_succ] at this)
      H1
      (fun k hk ↦ by
        obtain ⟨e1, e2⟩ := hch (k + 1) (by omega)
        have hd := hDC (k + 1) (by omega) 1 le_rfl (by omega)
        rw [bsz_one] at hd
        obtain ⟨x1, -⟩ := hC (k + 1) (by omega)
        simp only [regs] at x1
        rw [getD_tail']
        refine ⟨(rdE2_of_frame (f2 _ (by simp only [regs]; omega) (by omega))
          (f2 _ (by simp only [regs]; omega) (by omega))).trans e1,
          (rdE2_of_frame (f2 _ (by simp only [regs]; omega) (by omega))
          (f2 _ (by simp only [regs]; omega) (by omega))).trans e2⟩)
    have hfr : ∀ x, regs ≤ x → (∀ k, 1 ≤ k → k ≤ j + 1 → x < bf k ∨ bf k + bsz h m (j + 1) k ≤ x) →
        rd (semXIR I (foldsIR h m j (fun k ↦ bf (k + 1)) (fun k ↦ ch (k + 1))) s1).M x = rd s.M x := by
      intro x hx hk
      rw [g5 x hx (fun k h1 h2 ↦ by have := hk (k + 1) (by omega) (by omega); rwa [bsz_succ] at this)]
      have := hk 1 le_rfl (by omega)
      rw [bsz_one] at this
      exact f2 x hx this
    have e2 : 2 ^ (h + (m + (j + 1))) = 2 * 2 ^ (h + (m + j)) := by
      rw [show h + (m + (j + 1)) = h + (m + j) + 1 by omega, pow_succ]; ring
    have hc : ChainW (semXIR I (foldsIR h m j (fun k ↦ bf (k + 1)) (fun k ↦ ch (k + 1))) s1).M h hh m (j + 1) bf l
        W := by
      rw [ChainW]
      refine ⟨hW.of_frame fun x h1 h2 ↦ hfr x (by simp only [regs] at b0 ⊢; omega) fun k hk1 hk2 ↦ ?_, g1⟩
      have := hD 0 (by omega) k (by omega) (by omega)
      rw [bsz_zero] at this
      rw [e2] at h2
      omega
    exact ⟨hc, g2, g3.trans f4, g4.trans (by rw [z1]), hfr⟩

/-! ## Stores of constants -/

/-- A store register. -/ def tA : ℕ := 236
/-- A store register. -/ def tV : ℕ := 237

/-- `M[a] := v`. -/
def wrIR (a v : ℕ) : XIR := .seq (sIR [.cst tA (toWord a), .cst tV (toWord v)]) (.store tA tV)

theorem wrIR_sem (I : Array Word) (s : St) (hM : Inv s.M) {a v : ℕ} (ha : regs ≤ a) (ha2 : a < 2 ^ 64)
    (hsz : a < s.M.size) :
    rd (semXIR I (wrIR a v) s).M a = toWord v ∧
      (∀ x, regs ≤ x → x ≠ a → rd (semXIR I (wrIR a v) s).M x = rd s.M x) ∧ Inv (semXIR I (wrIR a v) s).M ∧
      (semXIR I (wrIR a v) s).M.size = s.M.size ∧ (semXIR I (wrIR a v) s).o = s.o := by
  obtain ⟨a1, a2, a3, a4⟩ := sIR_sem I (rd s.M) [.cst tA (toWord a), .cst tV (toWord v)] s (rd s.M) hM
    (by simp +decide [SOp.Ok, regs, tA, tV]) (fun _ _ ↦ rfl) (fun _ _ ↦ rfl) (by simp [sLd, SOp.LdOk])
  have r1 : rd (semXIR I (sIR [.cst tA (toWord a), .cst tV (toWord v)]) s).M tA = toWord a := by
    rw [a1 _ ((show Trk tA from ⟨by decide, Or.inr (by decide)⟩))]
    simp [sRun, SOp.step, Function.update_apply, tA, tV]
  have r2 : rd (semXIR I (sIR [.cst tA (toWord a), .cst tV (toWord v)]) s).M tV = toWord v := by
    rw [a1 _ ((show Trk tV from ⟨by decide, Or.inr (by decide)⟩))]
    simp [sRun, SOp.step, Function.update_apply, tA, tV]
  have z1 := size_sIR I [.cst tA (toWord a), .cst tV (toWord v)] s
  rw [wrIR, semXIR_seq]
  generalize semXIR I (sIR [.cst tA (toWord a), .cst tV (toWord v)]) s = s1 at a1 a2 a3 a4 r1 r2 z1
  obtain ⟨w1, w2, w3⟩ := store_sem I s1 a3 (p := tA) (v := tV) (x := a) (by decide) (by decide) r1 ha ha2
    (by rw [z1]; exact hsz)
  refine ⟨w1.trans r2, fun x hx hxa ↦ ?_, w3, by rw [size_sem, z1], a4⟩
  rw [w2 x hxa (by simp only [regs, cTmp] at hx ⊢; omega), a2 x hx]

/-- Stores of constants, in order. -/
def wrsIR : List (ℕ × ℕ) → XIR
  | [] => .blk []
  | (a, v) :: t => .seq (wrIR a v) (wrsIR t)

theorem wrsIR_sem (I : Array Word) : ∀ (l : List (ℕ × ℕ)) (s : St), Inv s.M →
    (∀ p ∈ l, regs ≤ p.1 ∧ p.1 < 2 ^ 64 ∧ p.1 < s.M.size) → (l.map Prod.fst).Nodup →
    (∀ p ∈ l, rd (semXIR I (wrsIR l) s).M p.1 = toWord p.2) ∧
      (∀ x, regs ≤ x → x ∉ l.map Prod.fst → rd (semXIR I (wrsIR l) s).M x = rd s.M x) ∧
      Inv (semXIR I (wrsIR l) s).M ∧ (semXIR I (wrsIR l) s).M.size = s.M.size ∧ (semXIR I (wrsIR l) s).o = s.o
  | [], s, hM, _, _ => ⟨fun _ h ↦ absurd h List.not_mem_nil, fun _ _ _ ↦ rfl, hM, rfl, rfl⟩
  | (a, v) :: t, s, hM, hl, hnd => by
    obtain ⟨ha, ha2, has⟩ := hl (a, v) List.mem_cons_self
    obtain ⟨w1, w2, w3, w4, w5⟩ := wrIR_sem I s hM (v := v) ha ha2 has
    rw [List.map_cons, List.nodup_cons] at hnd
    simp only [wrsIR, semXIR_seq]
    generalize semXIR I (wrIR a v) s = s1 at w1 w2 w3 w4 w5
    obtain ⟨b1, b2, b3, b4, b5⟩ := wrsIR_sem I t s1 w3
      (fun p hp ↦ by obtain ⟨x1, x2, x3⟩ := hl p (List.mem_cons_of_mem _ hp); exact ⟨x1, x2, by rw [w4]; exact x3⟩)
      hnd.2
    refine ⟨fun p hp ↦ ?_, fun x hx hxl ↦ ?_, b3, b4.trans w4, b5.trans w5⟩
    · rcases List.mem_cons.1 hp with e | hp'
      · subst e; rw [b2 a ha hnd.1, w1]
      · exact b1 p hp'
    · rw [List.map_cons, List.mem_cons, not_or] at hxl
      rw [b2 x hx hxl.2, w2 x hx hxl.1]

/-! ## The round tables -/

/-- Round `r`'s entries: `tb + 2r` the unfolded word (buffer `j − 1 − r`), `tS + 2r` the folded one (`j − r`). -/
def tabL (j m tb tS : ℕ) (bf : ℕ → ℕ) (r : ℕ) : List (ℕ × ℕ) :=
  [(tb + 2 * r, bf (j - 1 - r)), (tb + 2 * r + 1, 2 * 2 ^ (m + 1 + r)), (tS + 2 * r, bf (j - r)),
    (tS + 2 * r + 1, 2 * 2 ^ (m + r))]

/-- The tables of rounds `r < n`. -/
def tabsIR (j m tb tS : ℕ) (bf : ℕ → ℕ) : ℕ → XIR
  | 0 => .blk []
  | n + 1 => .seq (tabsIR j m tb tS bf n) (wrsIR (tabL j m tb tS bf n))

/-- **The tables hold rounds `r < n`.** -/
def TabW (M : Mem) (j m tb tS : ℕ) (bf : ℕ → ℕ) (n : ℕ) : Prop :=
  ∀ r < n, rd M (tb + 2 * r) = toWord (bf (j - 1 - r)) ∧ rd M (tb + 2 * r + 1) = toWord (2 * 2 ^ (m + 1 + r)) ∧
    rd M (tS + 2 * r) = toWord (bf (j - r)) ∧ rd M (tS + 2 * r + 1) = toWord (2 * 2 ^ (m + r))

theorem tabsIR_sem (I : Array Word) {j m tb tS : ℕ} {bf : ℕ → ℕ} (htb : regs ≤ tb) (htS : regs ≤ tS)
    (hd : tb + 2 * j ≤ tS ∨ tS + 2 * j ≤ tb) (h64 : tb + 2 * j < 2 ^ 64) (h64' : tS + 2 * j < 2 ^ 64) :
    ∀ n ≤ j, ∀ s : St, Inv s.M → tb + 2 * j ≤ s.M.size → tS + 2 * j ≤ s.M.size →
      TabW (semXIR I (tabsIR j m tb tS bf n) s).M j m tb tS bf n ∧ Inv (semXIR I (tabsIR j m tb tS bf n) s).M ∧
        (semXIR I (tabsIR j m tb tS bf n) s).M.size = s.M.size ∧ (semXIR I (tabsIR j m tb tS bf n) s).o = s.o ∧
        ∀ x, regs ≤ x → (x < tb ∨ tb + 2 * n ≤ x) → (x < tS ∨ tS + 2 * n ≤ x) →
          rd (semXIR I (tabsIR j m tb tS bf n) s).M x = rd s.M x
  | 0, _, s, hM, _, _ => ⟨fun _ h ↦ absurd h (Nat.not_lt_zero _), hM, rfl, rfl, fun _ _ _ _ ↦ rfl⟩
  | n + 1, hn, s, hM, hs1, hs2 => by
    obtain ⟨a1, a2, a3, a4, a5⟩ := tabsIR_sem I htb htS hd h64 h64' n (by omega) s hM hs1 hs2
    simp only [regs] at htb htS
    simp only [tabsIR, semXIR_seq]
    generalize semXIR I (tabsIR j m tb tS bf n) s = s1 at a1 a2 a3 a4 a5
    obtain ⟨b1, b2, b3, b4, b5⟩ := wrsIR_sem I (tabL j m tb tS bf n) s1 a2
      (by simp only [tabL, List.mem_cons, List.mem_nil_iff, or_false]; rintro p (rfl | rfl | rfl | rfl) <;>
        simp only [regs] <;> omega)
      (by simp only [tabL, List.map_cons, List.map_nil, List.nodup_cons, List.mem_cons, List.mem_nil_iff,
        or_false, List.not_mem_nil, not_false_eq_true, List.nodup_nil, and_true]; omega)
    have hnot : ∀ x, x < tb ∨ tb + 2 * (n + 1) ≤ x → x < tS ∨ tS + 2 * (n + 1) ≤ x →
        x ∉ (tabL j m tb tS bf n).map Prod.fst := fun x h1 h2 ↦ by
      simp only [tabL, List.map_cons, List.map_nil, List.mem_cons, List.mem_nil_iff, or_false]; omega
    refine ⟨fun r hr ↦ ?_, b3, b4.trans a3, b5.trans a4, fun x hx h1 h2 ↦ ?_⟩
    · rcases Nat.lt_succ_iff_lt_or_eq.1 hr with hr | hrn
      · obtain ⟨e1, e2, e3, e4⟩ := a1 r hr
        have hn1 : ∀ y, (y = tb + 2 * r ∨ y = tb + 2 * r + 1 ∨ y = tS + 2 * r ∨ y = tS + 2 * r + 1) →
            y ∉ (tabL j m tb tS bf n).map Prod.fst := fun y hy ↦ by
          simp only [tabL, List.map_cons, List.map_nil, List.mem_cons, List.mem_nil_iff, or_false]; omega
        refine ⟨?_, ?_, ?_, ?_⟩
        · rw [b2 _ (by simp only [regs]; omega) (hn1 _ (by omega)), e1]
        · rw [b2 _ (by simp only [regs]; omega) (hn1 _ (by omega)), e2]
        · rw [b2 _ (by simp only [regs]; omega) (hn1 _ (by omega)), e3]
        · rw [b2 _ (by simp only [regs]; omega) (hn1 _ (by omega)), e4]
      · rw [hrn]
        exact ⟨b1 (tb + 2 * n, bf (j - 1 - n)) (by simp [tabL]), b1 (tb + 2 * n + 1, 2 * 2 ^ (m + 1 + n))
          (by simp [tabL]), b1 (tS + 2 * n, bf (j - n)) (by simp [tabL]),
          b1 (tS + 2 * n + 1, 2 * 2 ^ (m + n)) (by simp [tabL])⟩
    · rw [b2 x hx (hnot x h1 h2), a5 x hx (by omega) (by omega)]

/-- **The tables as the loaders and the builder read them** (`tbBase`/`tbOcc`). -/
theorem TabW.entries {M : Mem} {j m tb tS n : ℕ} {bf : ℕ → ℕ} (hT : TabW M j m tb tS bf n)
    (hbf : ∀ k ≤ j, bf k < 2 ^ 64) (hmj : m + j < 63) {r : ℕ} (hr : r < n) (hrj : r < j) :
    Lvm6.X.tbBase M tb r = bf (j - 1 - r) ∧ tbOcc M tb r = 2 * 2 ^ (m + 1 + r) ∧
      Lvm6.X.tbBase M tS r = bf (j - r) ∧ tbOcc M tS r = 2 * 2 ^ (m + r) := by
  obtain ⟨e1, e2, e3, e4⟩ := hT r hr
  have p1 : 2 * 2 ^ (m + 1 + r) < 2 ^ 64 := by
    rw [← pow_succ']; exact Nat.pow_lt_pow_right (by norm_num) (by omega)
  have p2 : 2 * 2 ^ (m + r) < 2 ^ 64 := by
    rw [← pow_succ']; exact Nat.pow_lt_pow_right (by norm_num) (by omega)
  simp only [Lvm6.X.tbBase, tbOcc, e1, e2, e3, e4, toNat_toWord (hbf (j - 1 - r) (by omega)),
    toNat_toWord (hbf (j - r) (by omega)), toNat_toWord p1, toNat_toWord p2, and_self]

/-! ## The transition -/

/-- **A level's transition**: the fold chain, then the round tables. -/
def trIR (h m j : ℕ) (bf ch : ℕ → ℕ) (tb tS : ℕ) : XIR := .seq (foldsIR h m j bf ch) (tabsIR j m tb tS bf j)

/-- **The transition on the machine**: the chain's words and the tables. -/
theorem trIR_sem (I : Array Word) {h : ℕ} (hh : h ≤ 64) {m j : ℕ} {bf ch : ℕ → ℕ} {tb tS : ℕ}
    (l : List (E2 × E2)) (W : Wd E2 (2 ^ h) (m + j)) (s : St) (hM : Inv s.M) (hm : m + j < 64)
    (hB : ∀ k ≤ j, regs ≤ bf k ∧ bf k + bsz h m j k < 2 ^ 64 ∧ bf k + bsz h m j k ≤ s.M.size)
    (hC : ∀ k < j, regs ≤ ch k ∧ ch k + 4 < 2 ^ 64)
    (hD : ∀ k ≤ j, ∀ k' ≤ j, k ≠ k' → bf k + bsz h m j k ≤ bf k' ∨ bf k' + bsz h m j k' ≤ bf k)
    (hDC : ∀ k < j, ∀ k', 1 ≤ k' → k' ≤ j → ch k + 4 ≤ bf k' ∨ bf k' + bsz h m j k' ≤ ch k)
    (htb : regs ≤ tb) (htS : regs ≤ tS) (hd : tb + 2 * j ≤ tS ∨ tS + 2 * j ≤ tb) (h64 : tb + 2 * j < 2 ^ 64)
    (h64' : tS + 2 * j < 2 ^ 64) (hs1 : tb + 2 * j ≤ s.M.size) (hs2 : tS + 2 * j ≤ s.M.size)
    (hDT : ∀ k ≤ j, (tb + 2 * j ≤ bf k ∨ bf k + bsz h m j k ≤ tb) ∧
      (tS + 2 * j ≤ bf k ∨ bf k + bsz h m j k ≤ tS))
    (hW : HoldsW s.M (bf 0) h (m + j) W)
    (hch : ∀ k < j, rdE2 s.M (ch k) = (l.getD k (0, 0)).1 ∧ rdE2 s.M (ch k + 2) = (l.getD k (0, 0)).2) :
    let s' := semXIR I (trIR h m j bf ch tb tS) s
    ChainW s'.M h hh m j bf l W ∧ TabW s'.M j m tb tS bf j ∧ Inv s'.M ∧ s'.o = s.o ∧ s'.M.size = s.M.size ∧
      ∀ x, regs ≤ x → (∀ k, 1 ≤ k → k ≤ j → x < bf k ∨ bf k + bsz h m j k ≤ x) →
        (x < tb ∨ tb + 2 * j ≤ x) → (x < tS ∨ tS + 2 * j ≤ x) → rd s'.M x = rd s.M x := by
  intro s'
  obtain ⟨a1, a2, a3, a4, a5⟩ := foldsIR_sem I hh m j bf ch l W s hM hm hB hC hD hDC hW hch
  simp only [s', trIR, semXIR_seq]
  generalize semXIR I (foldsIR h m j bf ch) s = s1 at a1 a2 a3 a4 a5
  obtain ⟨b1, b2, b3, b4, b5⟩ := tabsIR_sem I (m := m) (bf := bf) htb htS hd h64 h64' j le_rfl s1 a2
    (by rw [a4]; exact hs1) (by rw [a4]; exact hs2)
  refine ⟨?_, b1, b2, b4.trans a3, b3.trans a4, fun x hx hk h1 h2 ↦ by rw [b5 x hx h1 h2, a5 x hx hk]⟩
  -- the chain survives the tables: its buffers lie outside them
  have keep : ∀ (j' : ℕ) (bf' : ℕ → ℕ) (l' : List (E2 × E2)) (W' : Wd E2 (2 ^ h) (m + j')),
      (∀ k ≤ j', ∀ x, bf' k ≤ x → x < bf' k + bsz h m j' k →
        rd (semXIR I (tabsIR j m tb tS bf j) s1).M x = rd s1.M x) →
      ChainW s1.M h hh m j' bf' l' W' → ChainW (semXIR I (tabsIR j m tb tS bf j) s1).M h hh m j' bf' l' W' := by
    intro j'
    induction j' with
    | zero =>
      intro bf' l' W' hk hc
      rw [ChainW] at hc ⊢
      exact HoldsW.of_frame hc fun x h1 h2 ↦ hk 0 le_rfl x h1 (by simpa [bsz] using h2)
    | succ j' ih =>
      intro bf' l' W' hk hc
      rw [ChainW] at hc ⊢
      refine ⟨HoldsW.of_frame hc.1 fun x h1 h2 ↦ hk 0 (by omega) x h1 ?_, ih _ _ _ (fun k hk' x h1 h2 ↦
        hk (k + 1) (by omega) x h1 (by rwa [bsz_succ])) hc.2⟩
      rw [bsz_zero]; rw [show h + (m + j' + 1) = h + (m + j') + 1 by omega, pow_succ] at h2; omega
  refine keep j bf l W (fun k hk x h1 h2 ↦ b5 x ?_ ?_ ?_) a1
  · have := (hB k hk).1; simp only [regs] at this ⊢; omega
  · have := (hDT k hk).1; omega
  · have := (hDT k hk).2; omega

/-- **A level with the transition `trIR`** (`levelX_sem`'s transition hypothesis discharged): `M₀` is the heap after
the transition; `Q 0` follows from the chain's words and the tables. -/
theorem levelX_sem_tr (I : Array Word) (i : ℕ) (L : LevelX) (Ss : ℕ → List ℕ) (ys : ℕ → ℕ → ℕ → BF64)
    (Q : ℕ → St → Prop) (hN64 : ht6 i + 1 ≤ 64) (hBr : regs ≤ L.B) (hcol : fdEnd L.B (ht6 i) ≤ L.colB)
    (hstr : 2 ^ ht6 i ≤ L.str) (hQ : ∀ j, HeapPred (Q j)) (s : St) (hM : Inv s.M)
    {h : ℕ} (hh : h ≤ 64) {m j : ℕ} {bf ch : ℕ → ℕ} {tb tS : ℕ} (htr : L.tr = trIR h m j bf ch tb tS)
    (l : List (E2 × E2)) (W : Wd E2 (2 ^ h) (m + j)) (hm : m + j < 64)
    (hB : ∀ k ≤ j, regs ≤ bf k ∧ bf k + bsz h m j k < 2 ^ 64 ∧ bf k + bsz h m j k ≤ s.M.size)
    (hC : ∀ k < j, regs ≤ ch k ∧ ch k + 4 < 2 ^ 64)
    (hD : ∀ k ≤ j, ∀ k' ≤ j, k ≠ k' → bf k + bsz h m j k ≤ bf k' ∨ bf k' + bsz h m j k' ≤ bf k)
    (hDC : ∀ k < j, ∀ k', 1 ≤ k' → k' ≤ j → ch k + 4 ≤ bf k' ∨ bf k' + bsz h m j k' ≤ ch k)
    (htb : regs ≤ tb) (htS : regs ≤ tS) (hd : tb + 2 * j ≤ tS ∨ tS + 2 * j ≤ tb) (h64 : tb + 2 * j < 2 ^ 64)
    (h64' : tS + 2 * j < 2 ^ 64) (hs1 : tb + 2 * j ≤ s.M.size) (hs2 : tS + 2 * j ≤ s.M.size)
    (hDT : ∀ k ≤ j, (tb + 2 * j ≤ bf k ∨ bf k + bsz h m j k ≤ tb) ∧
      (tS + 2 * j ≤ bf k ∨ bf k + bsz h m j k ≤ tS))
    (hW : HoldsW s.M (bf 0) h (m + j) W)
    (hch : ∀ k < j, rdE2 s.M (ch k) = (l.getD k (0, 0)).1 ∧ rdE2 s.M (ch k + 2) = (l.getD k (0, 0)).2)
    (hQ0 : ∀ t : St, Inv t.M → ChainW t.M h hh m j bf l W → TabW t.M j m tb tS bf j → Q 0 t)
    (hgs : GroupsSem I (ht6 i + 1) (ht6 i) L.B L.colB L.str (semXIR I L.tr s).M Ss ys Q (semXIR I L.tr s).M.size
      L.gs 0) :
    Q (L.gs.map GroupX.nr).sum (semXIR I (levelX i L) s) ∧ Inv (semXIR I (levelX i L) s).M ∧
      (semXIR I (levelX i L) s).o = s.o ∧
      ∀ x, regs ≤ x → x < L.B → rd (semXIR I (levelX i L) s).M x = rd (semXIR I L.tr s).M x := by
  obtain ⟨a1, a2, a3, a4, -, -⟩ := trIR_sem I hh l W s hM hm hB hC hD hDC htb htS hd h64 h64' hs1 hs2 hDT hW hch
  rw [← htr] at a1 a2 a3 a4
  obtain ⟨b1, b2, b3, b4⟩ := levelX_sem I i L (semXIR I L.tr s).M Ss ys Q hN64 hBr hcol hstr hQ s
    ⟨a3, hQ0 _ a3 a1 a2, fun _ _ _ ↦ rfl⟩ hgs
  exact ⟨b1, b2, b3.trans a4, b4⟩

/-! ## The transition as a part (`PartOk … trCap`) -/

theorem wf_foldsIR (h : ℕ) : ∀ m j (bf ch : ℕ → ℕ), WF (foldsIR h m j bf ch)
  | _, 0, _, _ => by simp [foldsIR, WF]
  | m, j + 1, bf, ch => ⟨wf_foldIR .., wf_foldsIR h m j _ _⟩

theorem noLoopT_foldsIR (h : ℕ) : ∀ m j (bf ch : ℕ → ℕ), NoLoopT (foldsIR h m j bf ch)
  | _, 0, _, _ => by simp [foldsIR, NoLoopT]
  | m, j + 1, bf, ch => ⟨noLoopT_foldIR .., noLoopT_foldsIR h m j _ _⟩

theorem outs_foldsIR (h t : ℕ) : ∀ m j (bf ch : ℕ → ℕ), outs (foldsIR h m j bf ch) t = 0
  | _, 0, _, _ => by simp [foldsIR, outs]
  | m, j + 1, bf, ch => by simp only [foldsIR, outs, outs_foldIR, outs_foldsIR h t m j, Nat.add_zero]

theorem cost_foldsIR_le (h t : ℕ) : ∀ m j (bf ch : ℕ → ℕ), h + (m + j) < 64 →
    cost (foldsIR h m j bf ch) t ≤ 1 + j * (43 + 152 * 2 ^ (h + (m + j)))
  | _, 0, _, _, _ => by simp [foldsIR, cost, blkSteps]
  | m, j + 1, bf, ch, hj => by
    have ih := cost_foldsIR_le h t m j (fun k ↦ bf (k + 1)) (fun k ↦ ch (k + 1)) (by omega)
    have hf := cost_foldIR h (m + j) (bf 0) (bf 1) (ch 0) t
      (Nat.pow_lt_pow_right (by norm_num) (by omega))
    have hp : 2 ^ (h + (m + j)) ≤ 2 ^ (h + (m + (j + 1))) := Nat.pow_le_pow_right (by norm_num) (by omega)
    have := Nat.mul_le_mul_left j (show 43 + 152 * 2 ^ (h + (m + j)) ≤ 43 + 152 * 2 ^ (h + (m + (j + 1))) by omega)
    simp only [foldsIR, cost]
    rw [Nat.add_mul, one_mul]
    omega

theorem wf_wrsIR : ∀ l : List (ℕ × ℕ), WF (wrsIR l)
  | [] => by simp [wrsIR, WF]
  | (a, v) :: t => ⟨⟨wf_sIR _ (by simp +decide [SOp.Ok, regs, tA, tV]), by simp only [WF]; decide⟩, wf_wrsIR t⟩

theorem noLoopT_wrsIR : ∀ l : List (ℕ × ℕ), NoLoopT (wrsIR l)
  | [] => by simp [wrsIR, NoLoopT]
  | (a, v) :: t => ⟨⟨noLoopT_sIR _, trivial⟩, noLoopT_wrsIR t⟩

theorem outs_wrsIR (t : ℕ) : ∀ l : List (ℕ × ℕ), outs (wrsIR l) t = 0
  | [] => by simp [wrsIR, outs]
  | (a, v) :: l => by simp only [wrsIR, wrIR, outs, outs_sIR, outs_wrsIR t l, Nat.add_zero]

theorem cost_wrsIR (t : ℕ) : ∀ l : List (ℕ × ℕ), cost (wrsIR l) t = 1 + 11 * l.length
  | [] => by simp [wrsIR, cost, blkSteps]
  | (a, v) :: l => by
    simp only [wrsIR, wrIR, cost, cost_sIR, cost_wrsIR t l, List.length_cons, sCost, SOp.ir, blkSteps,
      List.length_cons, List.length_nil]
    norm_num
    ring

theorem part_tabsIR (j m tb tS : ℕ) (bf : ℕ → ℕ) (t : ℕ) : ∀ n,
    WF (tabsIR j m tb tS bf n) ∧ NoLoopT (tabsIR j m tb tS bf n) ∧ outs (tabsIR j m tb tS bf n) t = 0 ∧
      cost (tabsIR j m tb tS bf n) t = 1 + 46 * n
  | 0 => by simp [tabsIR, WF, NoLoopT, outs, cost, blkSteps]
  | n + 1 => by
    obtain ⟨a1, a2, a3, a4⟩ := part_tabsIR j m tb tS bf t n
    refine ⟨⟨a1, wf_wrsIR _⟩, ⟨a2, noLoopT_wrsIR _⟩, ?_, ?_⟩
    · simp only [tabsIR, outs, a3, outs_wrsIR, Nat.add_zero]
    · simp only [tabsIR, cost, a4, cost_wrsIR, tabL, List.length_cons, List.length_nil]
      ring

/-- **The transition within `trCap`** (`h + (m + j) ≤ 27`, `j ≤ 6`: level 0 has `21 + 6`). -/
theorem trIR_part (h m j : ℕ) (bf ch : ℕ → ℕ) (tb tS : ℕ) (hc : h + (m + j) ≤ 27) (hj : j ≤ 6) :
    PartOk (trIR h m j bf ch tb tS) trCap where
  wf := ⟨wf_foldsIR .., (part_tabsIR j m tb tS bf 0 j).1⟩
  noLoopT := ⟨noLoopT_foldsIR .., (part_tabsIR j m tb tS bf 0 j).2.1⟩
  outs t := by simp only [trIR, outs, outs_foldsIR, (part_tabsIR j m tb tS bf t j).2.2.1, Nat.add_zero]
  cost t := by
    have c1 := cost_foldsIR_le h t m j bf ch (by omega)
    have c2 := (part_tabsIR j m tb tS bf t j).2.2.2
    have hp : 2 ^ (h + (m + j)) ≤ 2 ^ 27 := Nat.pow_le_pow_right (by norm_num) hc
    have := Nat.mul_le_mul hj (show 43 + 152 * 2 ^ (h + (m + j)) ≤ 43 + 152 * 2 ^ 27 by omega)
    simp only [trIR, cost, trCap]
    have e : (2 : ℕ) ^ 38 = 274877906944 := by norm_num
    have e' : (2 : ℕ) ^ 27 = 134217728 := by norm_num
    rw [e]; rw [e'] at this
    omega

end Lvm6.X
