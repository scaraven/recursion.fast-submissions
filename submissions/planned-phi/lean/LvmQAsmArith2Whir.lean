-- New for lvm (HAR-WH): Q_arith phases 8–9: one stacked WHIR opening (`stackGW`, `stack_run`) and
-- `openPh`'s two (`openG`, `openPh_replays`: `C_rec`, then `C_main`). Lvm2 roll 8 (wave L): the gadgets' definitions
-- (`stackGW`, `stackGZ`, `openG`, …) are in `LvmQAsmArith2WhirD`, off the B program's build path; the proofs stay here.
import LvmQAsmArith2WhirD
import LvmQAsmArith2WhirBasis
import LvmQShapeB
import LvmQAsmArith2WhirOk
import LvmQAsmArith2WhirG
import LvmQAsmArith2WhirL

-- ===== merged from `LvmQAsmArith2WhirGS` (GOLF module merge: `LvmQAsmArith2WhirGS.lean` is now a stub importing `LvmQAsmArith2Whir`) =====
section
-- New for lvm (HAR-WH): the circuit specs of the phase 8–9 level gadgets (`LvmQAsmArith2WhirG`):
-- loads, round polynomials, fold and tail rounds, glue, row folds with the enforced sum, column
-- weights, constants, the final weight sum, copies and preloads (QA2's `LvmQWhir*` lemmas wired).

/-!
# Phases 8–9: specs of the level gadgets

The specs relate each gadget's output to `F` under its `SegsHold` constraints and the
hypotheses on its inputs: `ldE_spec` (= `feAt`), `pev_spec` (= `polyEval`), `rdQ_spec`
(= `sumcheckRoundPoly 3`), `roundsG_spec` (= `frQ`), `tailG_spec` (= `tlT`), `glueG_spec`
(= `glue`'s update), `colWG_spec` (= `inducedWeight` by `inducedWeight_pow`), `iwConsts_spec`,
`wsumG_spec`, `copiesG_spec`, `preloadG_spec`; pointer lemmas `*_out`, `*_adv`, `adv_e_le`.

`rowCh_window_spec` gives consecutive row-fold cells, and `foldsG_window_spec` gives their
weighted sum `Σ λ^q fold_q`. At level zero, the reversed weights for the `w ≤ 2^l` occupied
words are followed by zeros; at later levels, each row has `2^l` scalars and natural-order
weights.
-/

set_option autoImplicit false

namespace Lvm.Har

open Lvm Lvm.Loop Lvm.Loop.Build

variable {c : Ctx} {M : Mem}

/-- A quadratic's three cells' values. -/
def qv (M : Mem) (q : Cell × Cell × Cell) : List FE := [q.1.val M, q.2.1.val M, q.2.2.val M]

/-! ## Pointers -/

-- `adv_e_le` is in `LvmQAsmArith2WhirOk` (lvm2 roll 8: off the B program's build path).
theorem adv_k_le (p : Ptr) (δ : List Seg) : p.k ≤ (p.adv δ).k := Nat.le_add_right _ _

theorem ldE_out (v : Nat) (p : Ptr) : (ldEW v p).1 = ec p.e := rfl

theorem ldEW_adv (v : Nat) (p : Ptr) : p.adv (ldEW v p).2 = ⟨p.k, p.e + 1⟩ := by
  simp [ldEW, loadE, rowRes, Ptr.adv, segsW, Seg.w, Row.w, Row.writes]

/-! ## Loads, round polynomials -/

theorem ldE_spec {sig : ByteArray} {T v : Nat} {p : Ptr} (hS : Lvm.Q1.Streamed M sig T) (hv : v + 2 < T)
    (h : SegsHold c M p (ldEW v p).2) : (ldEW v p).1.val M = feAt sig (8 * v) := by
  rw [ldEW, loadE_spec h]
  exact Lvm.Q1.load_feAt hS hv

theorem pev_spec {q : Cell × Cell × Cell} {cc : Cell} {p : Ptr} (h : SegsHold c M p (pev q cc p).2) :
    (pev q cc p).1.val M = polyEval (qv M q) (cc.val M) := by
  simp only [pev, bind_apply] at h ⊢
  rw [segsHold_append] at h
  rw [mulAdd_spec h.2, mulAdd_spec h.1]
  simp only [qv, polyEval, List.foldr_cons, List.foldr_nil]
  ring

theorem rdQ_spec {sig : ByteArray} {T v : Nat} {cl : Cell} {p : Ptr} (hS : Lvm.Q1.Streamed M sig T)
    (hv : v + 10 < T) (h : SegsHold c M p (rdQ v cl p).2) :
    qv M (rdQ v cl p).1 = [feAt sig (8 * v + 40), cl.val M + feAt sig (8 * v + 64), feAt sig (8 * v + 64)] := by
  simp only [rdQ, bind_apply, pure_apply, List.append_nil] at h ⊢
  rw [segsHold_append, segsHold_append] at h
  have h0 := ldE_spec hS (by (clear * - hv; omega)) h.1
  have h2 := ldE_spec hS (by omega) h.2.1
  have h1 := lin_spec h.2.2
  simp only [add] at h1 ⊢
  simp only [qv]
  rw [h1, h0, h2, ofK_one, ofK_zero, one_mul, add_zero,
    show 8 * (v + 5) = 8 * v + 40 by ring, show 8 * (v + 8) = 8 * v + 64 by ring]

theorem roundsG_spec {sig : ByteArray} {T pc : Nat} (hS : Lvm.Q1.Streamed M sig T) :
    ∀ (n f V : Nat) (q : Cell × Cell × Cell) (p : Ptr), V + 15 * n + 4 < T →
      (∀ j < n, M.e (pc + f + j) = feAt sig (8 * V + 120 * j + 40)) →
      SegsHold c M p (roundsG pc f V n q p).2 → qv M (roundsG pc f V n q p).1 = frQ sig (8 * V) n (qv M q)
  | 0, f, V, q, p, _, _, _ => by simp [roundsG, pure_apply, frQ]
  | n + 1, f, V, q, p, hT, hc, h => by
    simp only [roundsG, bind_apply] at h ⊢
    rw [segsHold_append, segsHold_append] at h
    have hcl := pev_spec h.1
    have hq := rdQ_spec hS (by (clear * - hT; omega)) h.2.1
    rw [roundsG_spec hS n (f + 1) (V + 15) _ _ (by (clear * - hT; omega)) (fun j hj => by
      rw [show pc + (f + 1) + j = pc + f + (j + 1) by ring, hc (j + 1) (by (clear * - hj; omega))]
      congr 1; ring) h.2.2, hq, hcl]
    have h0 := hc 0 (by (clear * -; omega))
    simp only [Nat.add_zero, Nat.mul_zero] at h0
    simp only [frQ, Cell.val_E, h0]
    rw [show 8 * (V + 15) = 8 * V + 120 by ring, show 8 * (V + 9) + 40 = 8 * V + 112 by ring,
      show 8 * (V + 9) + 64 = 8 * V + 136 by ring]

theorem tailG_spec {sig : ByteArray} {T pc : Nat} (hS : Lvm.Q1.Streamed M sig T) :
    ∀ (n f V : Nat) (q : Cell × Cell × Cell) (p : Ptr), 1 ≤ n → V + 15 * (n - 1) + 8 < T →
      (∀ j < n, M.e (pc + f + j) = feAt sig (8 * V + 120 * j + 40)) →
      SegsHold c M p (tailG pc f V n q p).2 → (tailG pc f V n q p).1.val M = tlT sig (8 * V) n (qv M q)
  | 0, _, _, _, _, h1, _, _, _ => absurd h1 (by (clear * - h1; omega))
  | 1, f, V, q, p, _, _, hc, h => by
    simp only [tailG] at h ⊢
    rw [pev_spec h]
    have h0 := hc 0 (by (clear * -; omega))
    simp only [Nat.add_zero, Nat.mul_zero] at h0
    simp only [tlT, Cell.val_E, h0]
  | n + 2, f, V, q, p, _, hT, hc, h => by
    simp only [tailG, bind_apply] at h ⊢
    rw [segsHold_append, segsHold_append] at h
    have hcl := pev_spec h.1
    have hq := rdQ_spec hS (by (clear * - hT; omega)) h.2.1
    rw [tailG_spec hS (n + 1) (f + 1) (V + 15) _ _ (by (clear * -; omega)) (by (clear * - hT; omega)) (fun j hj => by
      rw [show pc + (f + 1) + j = pc + f + (j + 1) by ring, hc (j + 1) (by (clear * - hj; omega))]
      congr 1; ring) h.2.2, hq, hcl]
    have h0 := hc 0 (by (clear * -; omega))
    simp only [Nat.add_zero, Nat.mul_zero] at h0
    simp only [tlT, Cell.val_E, h0]
    rw [show 8 * (V + 15) = 8 * V + 120 by ring, show 8 * (V + 9) + 40 = 8 * V + 112 by ring,
      show 8 * (V + 9) + 64 = 8 * V + 136 by ring]

theorem glueG_spec {lam : Cell} {q i : Cell × Cell × Cell} {p : Ptr} (h : SegsHold c M p (glueG lam q i p).2) :
    qv M (glueG lam q i p).1 = List.zipWith (fun a b => a + 1 * lam.val M * b) (qv M q) (qv M i) := by
  simp only [glueG, bind_apply, pure_apply, List.append_nil] at h ⊢
  rw [segsHold_append, segsHold_append] at h
  simp only [qv, List.zipWith_cons_cons, List.zipWith_nil_left]
  rw [mulAdd_spec h.1, mulAdd_spec h.2.1, mulAdd_spec h.2.2]
  simp only [List.cons.injEq, and_true]
  refine ⟨by ring, by ring, by ring⟩

/-! ## Row folds and the enforced sum -/

theorem rowFold0_cell (l a lb S er : Nat) (p : Ptr) (q : Nat) :
    (rowFold0 l a lb S er p).1 q = ec (p.e + 2 ^ (l + a) + q) := by
  simp only [rowFold0, bind_apply, getPtr, pure_apply, Ptr.adv_nil, List.nil_append]
  rw [loop_adv]
  simp [LoopOut.cell, loop_apply, lrank, ltw, LRow.w, Row.w, Row.writes, Ptr.at]

theorem rowFoldE_cell (l a lb S er : Nat) (p : Ptr) (q : Nat) :
    (rowFoldE l a lb S er p).1 q = ec (p.e + 2 * 2 ^ (l + a) + q) := by
  simp only [rowFoldE, bind_apply, getPtr, pure_apply, Ptr.adv_nil, List.nil_append]
  rw [loop_adv]
  simp [LoopOut.cell, loop_apply, lrank, ltw, LRow.w, Row.w, Row.writes, Ptr.at]

/-- A chunk returns consecutive fold cells: at level zero they fold the `w` occupied words
against reversed weights followed by zeros; at later levels they fold all `2^l` scalars. -/
theorem rowCh_window_spec {sig : ByteArray} {T : Nat} (hS : Lvm.Q1.Streamed M sig T)
    {lvl0 : Bool} {l a lb S er w : Nat} (eq : Array FE) (hw : lvl0 = true → w ≤ 2 ^ l)
    (he : ∀ k < 2 ^ l, M.e (er + k) =
      if lvl0 then if k < w then eq.getD (w - 1 - k) 0 else 0 else eq.getD k 0)
    {p : Ptr} (hp : 1 ≤ p.e)
    (h : SegsHold c M p ((if lvl0 then rowFold0 l a lb S er else rowFoldE l a lb S er) p).2) :
    (∀ i, ((if lvl0 then rowFold0 l a lb S er else rowFoldE l a lb S er) p).1 i =
      ec ((((if lvl0 then rowFold0 l a lb S er else rowFoldE l a lb S er) p).1 0).n + i)) ∧
    ∀ i < 2 ^ a, lb + S * i + 3 * 2 ^ l + 2 < T →
      (((if lvl0 then rowFold0 l a lb S er else rowFoldE l a lb S er) p).1 i).val M =
        (if lvl0 then foldRow0 sig eq (8 * (lb + S * i)) w
          else foldRowE sig eq (8 * (lb + S * i)) (2 ^ l)) := by
  cases lvl0
  · simp only [Bool.false_eq_true, ite_false] at h he ⊢
    refine ⟨fun i => by rw [rowFoldE_cell, rowFoldE_cell]; simp, fun i hi hT => ?_⟩
    refine rowFoldE_eq h hp sig eq hi (fun k hk c' hc => ?_) he
    rw [hS _ (by (clear * - hT hk hc; omega))]; rfl
  · simp only [ite_true] at h he ⊢
    have hw' := hw rfl
    refine ⟨fun i => by rw [rowFold0_cell, rowFold0_cell]; simp, fun i hi hT => ?_⟩
    refine rowFold0_window h hp sig eq hi hw' (fun k hk => ?_) (fun k hk => ?_) (fun k hk hkl => ?_)
    · rw [hS _ (by (clear * - hw' hT hk; omega))]; rfl
    · simpa [hk] using he k (by (clear * - hw' hk; omega))
    · simpa [show ¬ k < w by (clear * - hk; omega)] using he k hkl

/-- A chunk of `min A (t − q₀)` terms followed by the rest from `q₀ + A` is the sum over `[q₀, t)`. -/
theorem sum_chunk (G : Nat → FE) (q₀ A t : Nat) (h : q₀ < t) :
    ∑ i ∈ Finset.range (min A (t - q₀)), G (q₀ + i) + ∑ q ∈ Finset.Ico (q₀ + A) t, G q =
      ∑ q ∈ Finset.Ico q₀ t, G q := by
  rcases Nat.le_total A (t - q₀) with hA | hA
  · rw [min_eq_left hA, ← Finset.sum_Ico_consecutive G (Nat.le_add_right q₀ A) (by omega),
      Finset.sum_Ico_eq_sum_range G q₀ (q₀ + A), Nat.add_sub_cancel_left]
  · rw [min_eq_right hA, Finset.Ico_eq_empty (by omega), Finset.sum_empty, add_zero,
      Finset.sum_Ico_eq_sum_range]

theorem chunks_tail {q₀ a t : Nat} {as : List Nat} (ht : t ≤ q₀ + ((a :: as).map (2 ^ ·)).sum)
    (hch : ∀ i < (a :: as).length, q₀ + (((a :: as).take i).map (2 ^ ·)).sum < t) :
    q₀ < t ∧ t ≤ q₀ + 2 ^ a + (as.map (2 ^ ·)).sum ∧
      ∀ i < as.length, q₀ + 2 ^ a + ((as.take i).map (2 ^ ·)).sum < t := by
  refine ⟨by simpa using hch 0 (by simp), by simp at ht; (clear * - ht; omega), fun i hi => ?_⟩
  have := hch (i + 1) (by simp; omega)
  simp only [List.take_succ_cons, List.map_cons, List.sum_cons] at this
  (clear * - this; omega)

theorem foldsG_cons (lvl0 : Bool) (l lb S er lp t : Nat) (z : Cell) (q₀ a : Nat) (as : List Nat) :
    foldsG lvl0 l lb S er lp t z q₀ (a :: as) =
      (if lvl0 then rowFold0 l a (lb + S * q₀) S er else rowFoldE l a (lb + S * q₀) S er) >>= fun fc =>
        dotG a (min (2 ^ a) (t - q₀)) (lp + q₀) 1 (fc 0).n 1 >>= fun d =>
          foldsG lvl0 l lb S er lp t z (q₀ + 2 ^ a) as >>= fun rest => add d rest := by
  cases lvl0 <;> rfl

/-- `foldsG` computes the sum of row folds weighted by powers of `lam` over `[q₀, t)`,
using `w` occupied words per level-zero row and all `2^l` scalars at later levels. -/
theorem foldsG_window_spec {sig : ByteArray} {T : Nat} (hS : Lvm.Q1.Streamed M sig T) {lvl0 : Bool}
    {l lb S er lp t w : Nat} {z : Cell} (hz : z.val M = 0) (eq : Array FE) (lam : FE)
    (hw : lvl0 = true → w ≤ 2 ^ l)
    (he : ∀ k < 2 ^ l, M.e (er + k) = if lvl0 then if k < w then eq.getD (w - 1 - k) 0 else 0 else eq.getD k 0)
    (hlp : ∀ q < t, M.e (lp + q) = lam ^ q) (hT : ∀ q < t, lb + S * q + 3 * 2 ^ l + 2 < T) :
    ∀ (as : List Nat) (q₀ : Nat) (p : Ptr), 1 ≤ p.e → t ≤ q₀ + (as.map (2 ^ ·)).sum →
      (∀ i < as.length, q₀ + ((as.take i).map (2 ^ ·)).sum < t) →
      SegsHold c M p (foldsG lvl0 l lb S er lp t z q₀ as p).2 →
      (foldsG lvl0 l lb S er lp t z q₀ as p).1.val M = ∑ q ∈ Finset.Ico q₀ t, lam ^ q *
        (if lvl0 then foldRow0 sig eq (8 * (lb + S * q)) w else foldRowE sig eq (8 * (lb + S * q)) (2 ^ l))
  | [], q₀, p, _, ht, _, _ => by
    simp only [foldsG, pure_apply, hz]
    rw [Finset.Ico_eq_empty (by simpa using ht), Finset.sum_empty]
  | a :: as, q₀, p, hp, ht, hch, h => by
    obtain ⟨hq₀, ht', hch'⟩ := chunks_tail ht hch
    rw [foldsG_cons] at h ⊢
    simp only [bind_apply] at h ⊢
    rw [segsHold_append, segsHold_append, segsHold_append] at h
    obtain ⟨hc, hd, hr, ha⟩ := h
    have hcs := rowCh_window_spec (lb := lb + S * q₀) hS eq hw he hp hc
    have hd' := dotG_spec hd (le_trans hp (adv_e_le _ _)) (Nat.le_min.mpr ⟨Nat.one_le_two_pow, by (clear * - hq₀; omega)⟩)
      (min_le_left _ _)
    have hr' := foldsG_window_spec hS hz eq lam hw he hlp hT as (q₀ + 2 ^ a) _
      (le_trans hp (le_trans (adv_e_le _ _) (adv_e_le _ _))) ht' hch' hr
    simp only [add] at ha ⊢
    rw [lin_spec ha, hd', hr', ofK_one, ofK_zero, one_mul, add_zero]
    rw [← sum_chunk _ q₀ (2 ^ a) t hq₀]
    congr 1
    refine Finset.sum_congr rfl fun i hi => ?_
    have hi' := Finset.mem_range.mp hi
    have hit : q₀ + i < t := by have := min_le_right (2 ^ a) (t - q₀); (clear * - hq₀ hi' this; omega)
    rw [Nat.one_mul, Nat.add_assoc lp, hlp _ hit]
    congr 1
    rw [← Cell.val_E, ← (hcs.1 i), hcs.2 i (lt_of_lt_of_le hi' (min_le_left _ _))
      (by have := hT _ hit; rw [Nat.mul_add] at this; (clear * - this; omega)),
      show lb + S * q₀ + S * i = lb + S * (q₀ + i) by ring]

/-! ## Column weights -/

theorem colWG_spec {cs : List Nat} {ptb ib rb lp xb t : Nat} {z : Cell} {zk : Nat} (hzE : z.ty = .E)
    (hz : z.val M = 0) (hzk : M.k zk = 0) (m : Nat) (qs : List Nat) (lam : FE) (pt : List FE)
    (hκ : csum cs = pt.length)
    (hpt : ∀ k < pt.length, M.e (ptb + k) = pt.getD k 0)
    (hI : ∀ k < pt.length, FE.ofK (M.k (ib + k)) = (iwInvs m).getD k 0)
    (hR : ∀ k < pt.length, FE.ofK (M.k (rb + k)) = (iwRoots m).getD k 0)
    (hw : ∀ q < t, M.e (lp + q) = lam ^ q) (hx : ∀ q < t, FE.ofK (M.k (xb + q)) = eOfNat (qs.getD q 0)) :
    ∀ (as : List Nat) (q₀ : Nat) (p : Ptr), 1 ≤ p.e → t ≤ q₀ + (as.map (2 ^ ·)).sum →
      (∀ i < as.length, q₀ + ((as.take i).map (2 ^ ·)).sum < t) →
      SegsHold c M p (colWG cs ptb ib rb lp xb t z zk q₀ as p).2 →
      (colWG cs ptb ib rb lp xb t z zk q₀ as p).1.val M = ∑ q ∈ Finset.Ico q₀ t,
        (iwSeq (iwRoots m) (iwInvs m) pt (lam ^ q) (eOfNat (qs.getD q 0)) pt.length).1
  | [], q₀, p, _, ht, _, _ => by
    simp only [colWG, pure_apply, hz]
    rw [Finset.Ico_eq_empty (by simpa using ht), Finset.sum_empty]
  | a :: as, q₀, p, hp, ht, hch, h => by
    obtain ⟨hq₀, ht', hch'⟩ := chunks_tail ht hch
    simp only [colWG, bind_apply] at h ⊢
    rw [segsHold_append, segsHold_append] at h
    obtain ⟨hc, hr, ha⟩ := h
    have hzn : M.e z.n = 0 := by
      obtain ⟨zt, zn⟩ := z
      simp only at hzE
      subst hzE
      exact hz
    have hcw := colWeight_spec hc hzn hzk (Nat.le_min.mpr ⟨Nat.one_le_two_pow, by (clear * - hq₀; omega)⟩) (min_le_left _ _) (iwRoots m) (iwInvs m) pt
      (hκ ▸ hpt) (hκ ▸ hI) (hκ ▸ hR)
    have hr' := colWG_spec hzE hz hzk m qs lam pt hκ hpt hI hR hw hx as (q₀ + 2 ^ a) _
      (le_trans hp (adv_e_le _ _)) ht' hch' hr
    simp only [add] at ha ⊢
    rw [lin_spec ha, hcw, hr', ofK_one, ofK_zero, one_mul, add_zero]
    rw [← sum_chunk _ q₀ (2 ^ a) t hq₀]
    congr 1
    refine Finset.sum_congr rfl fun i hi => ?_
    have hi' := Finset.mem_range.mp hi
    have hit : q₀ + i < t := by have := min_le_right (2 ^ a) (t - q₀); (clear * - hq₀ hi' this; omega)
    rw [Nat.add_assoc lp, hw _ hit, Nat.add_assoc xb, hx _ hit, hκ]

/-! ## `F`'s sums -/

theorem powers_len_wh (b : FE) (n : Nat) : (powers b n).length = n := by
  have key : ∀ (acc : FE) (n : Nat), (powersFrom acc b n).length = n := by
    intro acc n
    induction n generalizing acc with
    | zero => rfl
    | succ n ih => simp [powersFrom, ih]
  exact key 1 n

theorem inducedWeight_pow (m : Nat) (qs : List Nat) (lam : FE) (pt : List FE) :
    inducedWeight m qs (powers lam qs.length) pt = ∑ q ∈ Finset.range qs.length,
      (iwSeq (iwRoots m) (iwInvs m) pt (lam ^ q) (eOfNat (qs.getD q 0)) pt.length).1 := by
  rw [inducedWeight_sum m qs _ pt (powers_len_wh _ _)]
  refine Finset.sum_congr rfl fun q hq => ?_
  rw [powers_getD lam qs.length q (Finset.mem_range.mp hq)]

theorem dot_powers (lam : FE) (l : List FE) :
    Lvm.dot (powers lam l.length) l = ∑ q ∈ Finset.range l.length, lam ^ q * l.getD q 0 := by
  rw [dot_eq_sum _ _ (powers_len_wh _ _), powers_len_wh]
  refine Finset.sum_congr rfl fun q hq => ?_
  rw [powers_getD lam l.length q (Finset.mem_range.mp hq)]

/-! ## Constants -/

theorem constK_adv (v : FK) (g : Cell) (p : Ptr) : p.adv (const .K v g p).2 = ⟨p.k + 1, p.e⟩ := by
  simp [const, lin, rowRes, Ptr.adv, segsW, Seg.w, Row.w, Row.writes]

theorem kconsts_adv (g : Cell) (hg : g.ty = .K) : ∀ (vs : List FK) (p : Ptr),
    p.adv (kconsts g vs p).2 = ⟨p.k + vs.length, p.e⟩
  | [], p => by simp [kconsts, pure_apply]
  | v :: vs, p => by
    simp only [kconsts, bind_apply, Ptr.adv_append, constK_adv, kconsts_adv g hg vs, List.length_cons]
    congr 1; (clear * -; omega)

theorem kconsts_spec {g : Cell} (hg : g.ty = .K) : ∀ (vs : List FK) (p : Ptr), SegsHold c M p (kconsts g vs p).2 →
    ∀ k < vs.length, M.k (p.k + k) = vs.getD k 0
  | [], _, _, k, hk => absurd hk (by simp)
  | v :: vs, p, h, k, hk => by
    simp only [kconsts, bind_apply] at h
    rw [segsHold_append] at h
    rcases k with _ | k
    · have e := lin_spec h.1
      have hv : (const .K v g p).1.val M = FE.ofK (M.k p.k) := rfl
      simp only [const] at e hv
      rw [hv, ofK_one, one_mul, CharTwo.add_self_eq_zero, zero_add] at e
      simpa using ofK_inj e
    · have := kconsts_spec hg vs _ (by rw [constK_adv] at h; exact h.2) k (by simpa using hk)
      simp only [List.getD_cons_succ]
      rw [← this]; congr 1; show p.k + (k + 1) = p.k + 1 + k; (clear * -; omega)

theorem iwConsts_adv (m : Nat) {g : Cell} (hg : g.ty = .K) (p : Ptr) :
    p.adv (iwConsts m g p).2 = ⟨p.k + 2 * m, p.e⟩ := by
  simp only [iwConsts, bind_apply, Ptr.adv_append, kconsts_adv g hg, List.length_map, List.length_range]
  congr 1; (clear * -; omega)

theorem iwConsts_spec (m : Nat) {g : Cell} (hg : g.ty = .K) {p : Ptr} (h : SegsHold c M p (iwConsts m g p).2) :
    ∀ k < m, FE.ofK (M.k (p.k + k)) = (iwRoots m).getD k 0 ∧ FE.ofK (M.k (p.k + m + k)) = (iwInvs m).getD k 0 := by
  simp only [iwConsts, bind_apply] at h
  rw [segsHold_append] at h
  intro k hk
  have h1 := kconsts_spec hg _ p h.1 k (by simpa using hk)
  have h2 := kconsts_spec hg _ _ h.2 k (by simpa using hk)
  rw [kconsts_adv g hg] at h2
  simp only [List.length_map, List.length_range] at h2
  have hr := iwRoots_isK m k
  have hi := iwInvs_isK m k
  refine ⟨?_, ?_⟩
  · rw [h1]; simp only [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range hk,
      Option.map_some, Option.getD_some]
    rw [← List.getD_eq_getElem?_getD]; exact hr
  · rw [h2]; simp only [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range hk,
      Option.map_some, Option.getD_some]
    rw [← List.getD_eq_getElem?_getD]; exact hi

/-! ## The final weight sum -/

theorem wsumG_spec : ∀ (gl : List (Cell × Cell)) (w : Cell) (p : Ptr), SegsHold c M p (wsumG w gl p).2 →
    (wsumG w gl p).1.val M = gl.foldl (fun acc x => acc + x.1.val M * x.2.val M) (w.val M)
  | [], w, p, _ => by simp [wsumG, pure_apply]
  | (lam, W) :: gl, w, p, h => by
    simp only [wsumG, bind_apply] at h ⊢
    rw [segsHold_append] at h
    rw [wsumG_spec gl _ _ h.2, mulAdd_spec h.1, List.foldl_cons]
    congr 1
    ring

/-! ## Copies and preloads -/

theorem seqCopy_adv : ∀ (cells : List Cell), (∀ x ∈ cells, x.ty = .E) → ∀ p : Ptr,
    p.adv (seqAll (cells.map copy) p).2 = ⟨p.k, p.e + cells.length⟩
  | [], _, p => by simp [seqAll, pure_apply]
  | x :: cells, hE, p => by
    obtain ⟨xt, xn⟩ := x
    have hx : xt = .E := hE ⟨xt, xn⟩ (by simp)
    subst hx
    rw [List.map_cons, Lvm.QSig.seqAll_cons_apply, List.append_nil, Ptr.adv_append, QRing.copyE_adv,
      seqCopy_adv cells (fun y hy => hE y (List.mem_cons_of_mem _ hy))]
    simp only [List.length_cons, Ptr.mk.injEq, true_and]; omega

theorem seqCopy_spec : ∀ (cells : List Cell), (∀ x ∈ cells, x.ty = .E) → ∀ p : Ptr,
    SegsHold c M p (seqAll (cells.map copy) p).2 → ∀ i < cells.length, M.e (p.e + i) = (cells.getD i default).val M
  | [], _, _, _, i, hi => absurd hi (by simp)
  | x :: cells, hE, p, h, i, hi => by
    obtain ⟨xt, xn⟩ := x
    have hx : xt = .E := hE ⟨xt, xn⟩ (by simp)
    subst hx
    rw [List.map_cons, Lvm.QSig.seqAll_cons_apply, List.append_nil, segsHold_append] at h
    rcases i with _ | i
    · simpa using (QRing.copyE_spec h.1).2
    · have := seqCopy_spec cells (fun y hy => hE y (List.mem_cons_of_mem _ hy)) _ (by rw [QRing.copyE_adv] at h; exact h.2) i
        (by simpa using hi)
      simp only [List.getD_cons_succ]
      rw [← this]; congr 1; show p.e + (i + 1) = p.e + 1 + i; (clear * -; omega)

theorem copiesG_adv (cells : List Cell) (hE : ∀ x ∈ cells, x.ty = .E) (p : Ptr) :
    p.adv (copiesG cells p).2 = ⟨p.k, p.e + cells.length⟩ := by
  simp only [copiesG, bind_apply, getPtr, pure_apply, Ptr.adv_nil, List.nil_append, List.append_nil]
  exact seqCopy_adv cells hE p

theorem copiesG_spec {cells : List Cell} (hE : ∀ x ∈ cells, x.ty = .E) {p : Ptr} (h : SegsHold c M p (copiesG cells p).2) :
    (copiesG cells p).1 = p.e ∧ ∀ i < cells.length, M.e (p.e + i) = (cells.getD i default).val M := by
  simp only [copiesG, bind_apply, getPtr, pure_apply, Ptr.adv_nil, List.nil_append, List.append_nil] at h ⊢
  exact ⟨by first | rfl | trivial, seqCopy_spec cells hE p h⟩

theorem seqLd_adv : ∀ (ls : List Nat) (p : Ptr), p.adv (seqAll (ls.map ldEW) p).2 = ⟨p.k, p.e + ls.length⟩
  | [], p => by simp [seqAll, pure_apply]
  | v :: ls, p => by
    rw [List.map_cons, Lvm.QSig.seqAll_cons_apply, List.append_nil, Ptr.adv_append, ldEW_adv, seqLd_adv ls]
    simp only [List.length_cons, Ptr.mk.injEq, true_and]; omega

theorem seqLd_spec {sig : ByteArray} {T : Nat} (hS : Lvm.Q1.Streamed M sig T) : ∀ (ls : List Nat) (p : Ptr),
    (∀ v ∈ ls, v + 2 < T) → SegsHold c M p (seqAll (ls.map ldEW) p).2 →
    ∀ i < ls.length, M.e (p.e + i) = feAt sig (8 * ls.getD i 0)
  | [], _, _, _, i, hi => absurd hi (by simp)
  | v :: ls, p, hT, h, i, hi => by
    rw [List.map_cons, Lvm.QSig.seqAll_cons_apply, List.append_nil, segsHold_append] at h
    rcases i with _ | i
    · have := ldE_spec hS (hT v (by simp)) h.1
      rw [ldE_out] at this
      simpa using this
    · have := seqLd_spec hS ls _ (fun w hw => hT w (by simp [hw])) (by rw [ldEW_adv] at h; exact h.2) i
        (by simpa using hi)
      simp only [List.getD_cons_succ]
      rw [← this]; congr 1; show p.e + (i + 1) = p.e + 1 + i; (clear * -; omega)

theorem preloadG_adv (ls : List Nat) (p : Ptr) : p.adv (preloadG ls p).2 = ⟨p.k, p.e + ls.length⟩ := by
  simp only [preloadG, bind_apply, getPtr, pure_apply, Ptr.adv_nil, List.nil_append, List.append_nil]
  exact seqLd_adv ls p

theorem preloadG_spec {sig : ByteArray} {T : Nat} (hS : Lvm.Q1.Streamed M sig T) {ls : List Nat} {p : Ptr}
    (hT : ∀ v ∈ ls, v + 2 < T) (h : SegsHold c M p (preloadG ls p).2) :
    (preloadG ls p).1 = p.e ∧ ∀ i < ls.length, M.e (p.e + i) = feAt sig (8 * ls.getD i 0) := by
  simp only [preloadG, bind_apply, getPtr, pure_apply, Ptr.adv_nil, List.nil_append, List.append_nil] at h ⊢
  exact ⟨by first | rfl | trivial, seqLd_spec hS ls p hT h⟩

/-! ## Pointers of the straight-line gadgets -/

theorem pev_adv (q : Cell × Cell × Cell) (cc : Cell) (p : Ptr) : p.adv (pev q cc p).2 = ⟨p.k, p.e + 2⟩ := by
  simp [pev, bind_apply, mulAdd, rowRes, Ptr.adv, segsW, Seg.w, Row.w, Row.writes]

theorem rdQ_adv (v : Nat) (cl : Cell) (p : Ptr) : p.adv (rdQ v cl p).2 = ⟨p.k, p.e + 3⟩ := by
  simp [rdQ, bind_apply, pure_apply, ldEW, loadE, add, lin, jn, rowRes, Ptr.adv, segsW, Seg.w, Row.w,
    Row.writes]

theorem glueG_adv (lam : Cell) (q i : Cell × Cell × Cell) (p : Ptr) : p.adv (glueG lam q i p).2 = ⟨p.k, p.e + 3⟩ := by
  simp [glueG, bind_apply, pure_apply, mulAdd, rowRes, Ptr.adv, segsW, Seg.w, Row.w, Row.writes]

theorem wsumG_adv : ∀ (gl : List (Cell × Cell)) (w : Cell) (p : Ptr), p.adv (wsumG w gl p).2 = ⟨p.k, p.e + gl.length⟩
  | [], w, p => by simp [wsumG, pure_apply]
  | (lam, W) :: gl, w, p => by
    simp only [wsumG, bind_apply, Ptr.adv_append]
    rw [wsumG_adv gl]
    simp [mulAdd, rowRes, Ptr.adv, segsW, Seg.w, Row.w, Row.writes]; omega

theorem roundsG_adv (pc : Nat) : ∀ (n f V : Nat) (q : Cell × Cell × Cell) (p : Ptr),
    p.adv (roundsG pc f V n q p).2 = ⟨p.k, p.e + 5 * n⟩
  | 0, f, V, q, p => by simp [roundsG, pure_apply]
  | n + 1, f, V, q, p => by
    simp only [roundsG, bind_apply, Ptr.adv_append, pev_adv, rdQ_adv, roundsG_adv pc n]
    simp only [Ptr.mk.injEq, true_and]; omega

theorem tailG_adv (pc : Nat) : ∀ (n f V : Nat) (q : Cell × Cell × Cell) (p : Ptr), 1 ≤ n →
    p.adv (tailG pc f V n q p).2 = ⟨p.k, p.e + 5 * n - 3⟩
  | 0, _, _, _, _, h => absurd h (by omega)
  | 1, f, V, q, p, _ => by simp only [tailG, pev_adv, Ptr.mk.injEq, true_and]; omega
  | n + 2, f, V, q, p, _ => by
    simp only [tailG, bind_apply, Ptr.adv_append, pev_adv, rdQ_adv]
    rw [tailG_adv pc (n + 1) _ _ _ _ (by omega)]
    simp only [Ptr.mk.injEq, true_and]; omega

end Lvm.Har
end
-- ===== end of `LvmQAsmArith2WhirGS` =====

-- ===== merged from `LvmQAsmArith2WhirF` (GOLF module merge: `LvmQAsmArith2WhirF.lean` is now a stub importing `LvmQAsmArith2Whir`) =====
section
-- New for lvm (HAR-WH): `F`'s reads in phases 8–9 (the stacked WHIR openings) as pure functions of
-- the stream and the reader's position (`pos s = s.ent + s.msg`).

/-!
# Phases 8–9: run lemmas of `F`'s reader

Every read of the stacked opening depends only on the position `pos s` (and `openingR` on `ent`
with `msg = 0`): `sampleE_run`, `readE_run`, `readEs_run`, `srp3_run` (`sumcheckRoundPoly 3 _ none`),
`foldRounds_run` (`frQ`, `frC`), `positionsR_run` (`qsAt`, `qsAt_length`), `openingR_run`,
`tailRounds_run` (`frC`, `tlT`); the monad's `bind`, `read`, `require`, `skip`.
-/

set_option autoImplicit false

namespace Lvm.Har

open Lvm DM

theorem dm_bind {α β : Type} (x : DM α) (f : α → DM β) (sig : ByteArray) (s : RS) :
    (x >>= f) sig s = f (x sig s).1 sig (x sig s).2 := rfl

theorem dm_pure {α : Type} (a : α) (sig : ByteArray) (s : RS) : (pure a : DM α) sig s = (a, s) := rfl

theorem read_run (sig : ByteArray) (s : RS) : (read : DM ByteArray) sig s = (sig, s) := rfl

theorem require_runW (b : Bool) (sig : ByteArray) (s : RS) :
    require b sig s = ((), { s with ok := b && s.ok }) := rfl

theorem skip_run (n : Nat) (sig : ByteArray) (s : RS) : skip n sig s = ((), { s with msg := s.msg + n }) :=
  rfl

theorem pos_mk (a b : Nat) (o : Bool) : pos ⟨a, b, o⟩ = a + b := rfl

theorem sampleE_run (sig : ByteArray) (s : RS) :
    sampleE sig s = (feAt sig (pos s + 40), ⟨pos s + 72, 0, s.ok⟩) := by
  have h : sampleE sig s = (feAt sig (s.ent + 40 + s.msg), ⟨s.ent + 72 + s.msg, 0, s.ok⟩) := rfl
  rw [h]
  unfold pos
  rw [Nat.add_right_comm s.ent 40 s.msg, Nat.add_right_comm s.ent 72 s.msg]

theorem readE_run (sig : ByteArray) (s : RS) :
    readE sig s = (feAt sig (pos s + 40), { s with msg := s.msg + 24 }) := by
  have h : readE sig s = (feAt sig (s.ent + 40 + s.msg), { s with msg := s.msg + 24 }) := rfl
  rw [h]
  unfold pos
  rw [Nat.add_right_comm s.ent 40 s.msg]

theorem readEs_run (n : Nat) (sig : ByteArray) (s : RS) :
    readEs n sig s = ((List.range n).map (fun i => feAt sig (pos s + 40 + 24 * i)),
      { s with msg := s.msg + 24 * n }) := by
  induction n generalizing s with
  | zero => rfl
  | succ n ih =>
    have e : readEs (n + 1) sig s =
        (feAt sig (pos s + 40) :: (readEs n sig { s with msg := s.msg + 24 }).1,
          (readEs n sig { s with msg := s.msg + 24 }).2) := by
      rw [readEs, dm_bind, readE_run]; rfl
    rw [e, ih]
    obtain ⟨en, m, o⟩ := s
    refine Prod.ext ?_ ?_
    · show feAt sig (en + m + 40) :: (List.range n).map (fun i => feAt sig (en + (m + 24) + 40 + 24 * i)) =
        (List.range (n + 1)).map (fun i => feAt sig (en + m + 40 + 24 * i))
      rw [List.range_succ_eq_map, List.map_cons, List.map_map]
      refine congrArg (List.cons _) ?_
      refine List.map_congr_left fun i _ => ?_
      show feAt sig _ = feAt sig _
      congr 1
      omega
    · show (⟨en, m + 24 + 24 * n, o⟩ : RS) = ⟨en, m + 24 * (n + 1), o⟩
      congr 1
      omega

theorem srp3_run (claim : FE) (sig : ByteArray) (s : RS) :
    sumcheckRoundPoly 3 claim none sig s =
      ([feAt sig (pos s + 40), claim + feAt sig (pos s + 64), feAt sig (pos s + 64)],
        { s with msg := s.msg + 48 }) := by
  have e : sumcheckRoundPoly 3 claim none sig s =
      (feAt sig (pos s + 40) :: (claim + sumE (readEs 1 sig { s with msg := s.msg + 24 }).1) ::
        (readEs 1 sig { s with msg := s.msg + 24 }).1, (readEs 1 sig { s with msg := s.msg + 24 }).2) := by
    rw [sumcheckRoundPoly, dm_bind, readE_run]; rfl
  rw [e, readEs_run]
  obtain ⟨en, m, o⟩ := s
  simp only [pos_mk, List.range_one, List.map_cons, List.map_nil, sumE, List.foldl_cons,
    List.foldl_nil, zero_add, Nat.mul_zero, Nat.add_zero, Nat.mul_one]
  have e1 : en + (m + 24) + 40 = en + m + 64 := by omega
  have e2 : m + 24 + 24 = m + 48 := by omega
  rw [e1, e2]

/-! ## Fold rounds -/

theorem foldRounds_step (n : Nat) (st : WhirState) (lf : List FE) (sig : ByteArray) (s : RS) :
    foldRounds (n + 1) st lf sig s =
      foldRounds n { st with
          runningQuad := [feAt sig (pos s + 112),
            polyEval st.runningQuad (feAt sig (pos s + 40)) + feAt sig (pos s + 136),
            feAt sig (pos s + 136)],
          folds := st.folds ++ [feAt sig (pos s + 40)] }
        (lf ++ [feAt sig (pos s + 40)]) sig ⟨pos s + 72, 48, s.ok⟩ := by
  rw [foldRounds, dm_bind, sampleE_run]
  dsimp only
  rw [dm_bind, srp3_run]
  simp only [pos_mk, Nat.add_zero, Nat.zero_add]

theorem frC_succ (sig : ByteArray) (P n : Nat) :
    frC sig P (n + 1) = feAt sig (P + 40) :: frC sig (P + 120) n := by
  simp only [frC, List.range_succ_eq_map, List.map_cons, List.map_map, Nat.mul_zero, Nat.add_zero,
    List.cons.injEq, true_and]
  refine List.map_congr_left fun i _ => ?_
  simp only [Function.comp]
  congr 1
  omega

theorem foldRounds_run (n : Nat) (st : WhirState) (lf : List FE) (sig : ByteArray) (s : RS) :
    (foldRounds n st lf sig s).1 =
      ({ st with runningQuad := frQ sig (pos s) n st.runningQuad, folds := st.folds ++ frC sig (pos s) n },
        lf ++ frC sig (pos s) n) ∧
    pos (foldRounds n st lf sig s).2 = pos s + 120 * n ∧ (foldRounds n st lf sig s).2.ok = s.ok := by
  induction n generalizing st lf s with
  | zero =>
    refine ⟨?_, ?_, rfl⟩
    · show (st, lf) = _
      simp [frQ, frC]
    · show pos s = pos s + 120 * 0
      simp
  | succ n ih =>
    rw [foldRounds_step]
    obtain ⟨h1, h2, h3⟩ := ih _ _ _
    have hp : pos (⟨pos s + 72, 48, s.ok⟩ : RS) = pos s + 120 := by
      show pos s + 72 + 48 = pos s + 120; omega
    rw [hp] at h1 h2
    refine ⟨?_, ?_, h3⟩
    · rw [h1, frC_succ]
      simp only [frQ, List.append_assoc, List.singleton_append]
    · rw [h2]; ring

/-! ## Positions -/

/-- The positions of `n` answers from position `P` (`positionsAux`'s values). -/
def paF (sig : ByteArray) (h : Nat) : Nat → Nat → Nat → List Nat
  | _, 0, _ => []
  | P, n + 1, rem =>
    (List.range (min positionsPerAnswer rem)).map
        (fun j => (eToNat (feAt sig (P + 40)) >>> (j * h)) % 2 ^ h) ++
      paF sig h (P + 72) n (rem - min positionsPerAnswer rem)

theorem positionsAux_step (h n rem : Nat) (sig : ByteArray) (s : RS) :
    positionsAux h (n + 1) rem sig s =
      ((List.range (min positionsPerAnswer rem)).map
          (fun j => (eToNat (feAt sig (pos s + 40)) >>> (j * h)) % 2 ^ h) ++
        (positionsAux h n (rem - min positionsPerAnswer rem) sig ⟨pos s + 72, 0, s.ok⟩).1,
        (positionsAux h n (rem - min positionsPerAnswer rem) sig ⟨pos s + 72, 0, s.ok⟩).2) := by
  rw [positionsAux, dm_bind, sampleE_run]; rfl

theorem positionsAux_run (h : Nat) : ∀ (n rem : Nat) (sig : ByteArray) (s : RS),
    (positionsAux h n rem sig s).1 = paF sig h (pos s) n rem ∧
    pos (positionsAux h n rem sig s).2 = pos s + 72 * n ∧ (positionsAux h n rem sig s).2.ok = s.ok
  | 0, _, _, s => ⟨rfl, by show pos s = pos s + 72 * 0; simp, rfl⟩
  | n + 1, rem, sig, s => by
    rw [positionsAux_step]
    obtain ⟨h1, h2, h3⟩ := positionsAux_run h n (rem - min positionsPerAnswer rem) sig
      ⟨pos s + 72, 0, s.ok⟩
    have hp : pos (⟨pos s + 72, 0, s.ok⟩ : RS) = pos s + 72 := rfl
    rw [hp] at h1 h2
    refine ⟨?_, ?_, h3⟩
    · dsimp only
      rw [h1]; rfl
    · show pos (positionsAux h n _ sig _).2 = _
      rw [h2]; ring

theorem paF_length (sig : ByteArray) (h : Nat) : ∀ (n P rem : Nat),
    (paF sig h P n rem).length = min (positionsPerAnswer * n) rem
  | 0, _, _ => by simp [paF]
  | n + 1, P, rem => by
    rw [paF, List.length_append, List.length_map, List.length_range, paF_length sig h n]
    simp only [positionsPerAnswer]
    omega

theorem positionsR_run (L : Level) (sig : ByteArray) (s : RS) :
    (positionsR L sig s).1 = qsAt sig (pos s) L ∧
    pos (positionsR L sig s).2 = pos s + 72 * ((L.t + positionsPerAnswer - 1) / positionsPerAnswer) ∧
    (positionsR L sig s).2.ok = s.ok := by
  obtain ⟨h1, h2, h3⟩ := positionsAux_run L.height ((L.t + positionsPerAnswer - 1) / positionsPerAnswer)
    L.t sig s
  refine ⟨?_, h2, h3⟩
  show (positionsAux _ _ _ sig s).1 = (positionsAux _ _ _ sig ⟨pos s, 0, true⟩).1
  rw [h1, (positionsAux_run _ _ _ sig ⟨pos s, 0, true⟩).1]
  rfl

theorem qsAt_length (sig : ByteArray) (P : Nat) (L : Level) : (qsAt sig P L).length = L.t := by
  show (positionsAux _ _ _ sig ⟨P, 0, true⟩).1.length = L.t
  rw [(positionsAux_run _ _ _ sig ⟨P, 0, true⟩).1, paF_length]
  simp only [positionsPerAnswer]
  omega

/-! ## Openings -/

theorem openingAux_run (L : Level) (sig : ByteArray) : ∀ (n : Nat) (s : RS),
    openingAux L n sig s = ((List.range n).map (fun j => s.ent + 8 + (40 + L.row + 104 * L.path) * j),
      { s with ent := s.ent + (40 + L.row + 104 * L.path) * n })
  | 0, s => by
    show (([] : List Nat), s) = _
    obtain ⟨en, m, o⟩ := s
    simp
  | n + 1, s => by
    have e : openingAux L (n + 1) sig s =
        ((s.ent + 8) :: (openingAux L n sig { s with ent := s.ent + 40 + L.row + 104 * L.path }).1,
          (openingAux L n sig { s with ent := s.ent + 40 + L.row + 104 * L.path }).2) := by
      rw [openingAux]; rfl
    rw [e, openingAux_run L sig n]
    obtain ⟨en, m, o⟩ := s
    refine Prod.ext ?_ ?_
    · show (en + 8) :: (List.range n).map
          (fun j => en + 40 + L.row + 104 * L.path + 8 + (40 + L.row + 104 * L.path) * j) =
        (List.range (n + 1)).map (fun j => en + 8 + (40 + L.row + 104 * L.path) * j)
      rw [List.range_succ_eq_map, List.map_cons, List.map_map]
      congr 1
      refine List.map_congr_left fun i _ => ?_
      show _ = en + 8 + (40 + L.row + 104 * L.path) * (i + 1)
      ring
    · show (⟨en + 40 + L.row + 104 * L.path + (40 + L.row + 104 * L.path) * n, m, o⟩ : RS) =
        ⟨en + (40 + L.row + 104 * L.path) * (n + 1), m, o⟩
      congr 1
      ring

theorem openingR_run (L : Level) (sig : ByteArray) (s : RS) (h : s.msg = 0) :
    openingR L sig s = ((List.range L.t).map (fun j => s.ent + 8 + (40 + L.row + 104 * L.path) * j),
      ⟨s.ent + (40 + L.row + 104 * L.path) * L.t, 0, s.ok⟩) := by
  have e : openingR L sig s = openingAux L L.t sig { s with ok := s.ok && s.msg == 0 } := rfl
  rw [e, openingAux_run]
  obtain ⟨en, m, o⟩ := s
  simp only at h
  subst h
  simp

/-! ## Tail rounds -/

theorem tailRounds_one (q : List FE) (sig : ByteArray) (s : RS) :
    tailRounds 1 q sig s = (([feAt sig (pos s + 40)], polyEval q (feAt sig (pos s + 40))),
      ⟨pos s + 72, 0, s.ok⟩) := by
  rw [tailRounds, dm_bind, sampleE_run]; rfl

theorem tailRounds_step (n : Nat) (q : List FE) (sig : ByteArray) (s : RS) :
    tailRounds (n + 2) q sig s =
      ((feAt sig (pos s + 40) :: (tailRounds (n + 1) [feAt sig (pos s + 112),
          polyEval q (feAt sig (pos s + 40)) + feAt sig (pos s + 136), feAt sig (pos s + 136)] sig
          ⟨pos s + 72, 48, s.ok⟩).1.1,
        (tailRounds (n + 1) [feAt sig (pos s + 112),
          polyEval q (feAt sig (pos s + 40)) + feAt sig (pos s + 136), feAt sig (pos s + 136)] sig
          ⟨pos s + 72, 48, s.ok⟩).1.2),
        (tailRounds (n + 1) [feAt sig (pos s + 112),
          polyEval q (feAt sig (pos s + 40)) + feAt sig (pos s + 136), feAt sig (pos s + 136)] sig
          ⟨pos s + 72, 48, s.ok⟩).2) := by
  rw [tailRounds, dm_bind, sampleE_run]
  dsimp only
  rw [if_neg (show ¬(n + 1 = 0) by omega), dm_bind, srp3_run]
  simp only [pos_mk, Nat.add_zero, Nat.zero_add]
  have e1 : pos s + 72 + 40 = pos s + 112 := by omega
  have e2 : pos s + 72 + 64 = pos s + 136 := by omega
  rw [e1, e2]
  rfl

theorem tailRounds_run' (n : Nat) : ∀ (q : List FE) (sig : ByteArray) (s : RS),
    tailRounds (n + 1) q sig s =
      ((frC sig (pos s) (n + 1), tlT sig (pos s) (n + 1) q), ⟨pos s + 120 * n + 72, 0, s.ok⟩) := by
  induction n with
  | zero =>
    intro q sig s
    rw [tailRounds_one]
    simp [frC, tlT]
  | succ n ih =>
    intro q sig s
    rw [tailRounds_step, ih]
    have hp : pos (⟨pos s + 72, 48, s.ok⟩ : RS) = pos s + 120 := by
      show pos s + 72 + 48 = pos s + 120; omega
    rw [hp, frC_succ sig (pos s) (n + 1)]
    refine Prod.ext (Prod.ext rfl rfl) ?_
    show (⟨pos s + 120 + 120 * n + 72, 0, s.ok⟩ : RS) = ⟨pos s + 120 * (n + 1) + 72, 0, s.ok⟩
    congr 1
    ring

theorem tailRounds_run (n : Nat) (hn : 1 ≤ n) (q : List FE) (sig : ByteArray) (s : RS) :
    tailRounds n q sig s = ((frC sig (pos s) n, tlT sig (pos s) n q), ⟨pos s + 120 * (n - 1) + 72, 0, s.ok⟩) := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  rw [tailRounds_run' m]
  simp

/-! ## Simp forms -/

theorem foldRounds_fst (n : Nat) (st : WhirState) (lf : List FE) (sig : ByteArray) (s : RS) :
    (foldRounds n st lf sig s).1 =
      ({ st with runningQuad := frQ sig (pos s) n st.runningQuad, folds := st.folds ++ frC sig (pos s) n },
        lf ++ frC sig (pos s) n) := (foldRounds_run n st lf sig s).1

theorem foldRounds_pos (n : Nat) (st : WhirState) (lf : List FE) (sig : ByteArray) (s : RS) :
    pos (foldRounds n st lf sig s).2 = pos s + 120 * n := (foldRounds_run n st lf sig s).2.1

theorem foldRounds_ok (n : Nat) (st : WhirState) (lf : List FE) (sig : ByteArray) (s : RS) :
    (foldRounds n st lf sig s).2.ok = s.ok := (foldRounds_run n st lf sig s).2.2

theorem positionsR_fst (L : Level) (sig : ByteArray) (s : RS) :
    (positionsR L sig s).1 = qsAt sig (pos s) L := (positionsR_run L sig s).1

theorem positionsR_pos (L : Level) (sig : ByteArray) (s : RS) :
    pos (positionsR L sig s).2 = pos s + 72 * ((L.t + positionsPerAnswer - 1) / positionsPerAnswer) :=
  (positionsR_run L sig s).2.1

theorem positionsR_ok (L : Level) (sig : ByteArray) (s : RS) : (positionsR L sig s).2.ok = s.ok :=
  (positionsR_run L sig s).2.2

theorem frC_length (sig : ByteArray) (P n : Nat) : (frC sig P n).length = n := by simp [frC]

theorem pos_mk0 (a : Nat) (o : Bool) : pos ⟨a, 0, o⟩ = a := rfl

theorem pos_msg (s : RS) (n : Nat) : pos { s with msg := s.msg + n } = pos s + n := by
  show s.ent + (s.msg + n) = s.ent + s.msg + n; omega

theorem pos_upd (s : RS) (n : Nat) (o : Bool) : pos ⟨s.ent, s.msg + n, o⟩ = pos s + n := by
  show s.ent + (s.msg + n) = s.ent + s.msg + n; omega

theorem pos_mk48 (a : Nat) (o : Bool) : pos ⟨a, 48, o⟩ = a + 48 := rfl

theorem openingR_mk (L : Level) (sig : ByteArray) (a : Nat) (o : Bool) :
    openingR L sig ⟨a, 0, o⟩ = ((List.range L.t).map (fun j => a + 8 + (40 + L.row + 104 * L.path) * j),
      ⟨a + (40 + L.row + 104 * L.path) * L.t, 0, o⟩) := openingR_run L sig _ rfl

/-! ## The OOD items and the grinding (JB-L §3, PI-GRIND) -/

/-- The OOD point `z` of a level: `κ` samples from position `Pc`. -/
def oodZ (sig : ByteArray) (Pc κ : Nat) : List FE := (List.range κ).map fun j => feAt sig (Pc + 72 * j + 40)

/-- `F`'s OOD claims of a level (`oodStep`) from position `Pc` (after the next cap): with `ood`, the
intro polynomial `[c₀, y + c₂, c₂]` and the weight `eq(z, ·)`; none without. -/
def oodF (sig : ByteArray) (ood : Bool) (κ Pc : Nat) : List (List FE × (List FE → FE)) :=
  if ood then [([feAt sig (Pc + 72 * κ + 24 + 40), feAt sig (Pc + 72 * κ + 40) + feAt sig (Pc + 72 * κ + 24 + 64),
    feAt sig (Pc + 72 * κ + 24 + 64)], fun x => eqEval (oodZ sig Pc κ) x)] else []

/-- `F`'s proof-of-work check of a level whose grinding starts at position `Po`: the PoW challenge is the
answer at `Po + 136` (after the separator and the nonce). -/
def powF (sig : ByteArray) (g Po : Nat) : Bool := if g = 0 then true else powOKR g (feAt sig (Po + 136))

theorem samples_succ_run (sig : ByteArray) : ∀ (n : Nat) (s : RS),
    samples (n + 1) sig s = ((List.range (n + 1)).map fun j => feAt sig (pos s + 72 * j + 40),
      ⟨pos s + 72 * (n + 1), 0, s.ok⟩)
  | 0, s => by
    rw [samples, dm_bind, sampleE_run]
    show ([feAt sig (pos s + 40)], (⟨pos s + 72, 0, s.ok⟩ : RS)) = _
    simp
  | n + 1, s => by
    have e : samples (n + 1 + 1) sig s =
        (feAt sig (pos s + 40) :: (samples (n + 1) sig ⟨pos s + 72, 0, s.ok⟩).1,
          (samples (n + 1) sig ⟨pos s + 72, 0, s.ok⟩).2) := by
      show (sampleE >>= fun x => samples (n + 1) >>= fun xs => pure (x :: xs)) sig s = _
      rw [dm_bind, sampleE_run]; rfl
    rw [e, samples_succ_run sig n, pos_mk0]
    refine Prod.ext ?_ ?_
    · show feAt sig (pos s + 40) :: _ = _
      apply List.ext_getElem (by simp)
      intro i h1 h2
      cases i with
      | zero => simp
      | succ i =>
        simp only [List.getElem_cons_succ, List.getElem_map, List.getElem_range]
        congr 1; ring
    · show (⟨_, _, _⟩ : RS) = ⟨_, _, _⟩
      rw [RS.mk.injEq]; exact ⟨by ring, rfl, rfl⟩

theorem oodStep_true (κ : Nat) (hκ : 1 ≤ κ) (sig : ByteArray) (s : RS) :
    oodStep true κ sig s = (oodF sig true κ (pos s), ⟨pos s + 72 * κ, 72, s.ok⟩) := by
  obtain ⟨m, rfl⟩ : ∃ m, κ = m + 1 := ⟨κ - 1, by omega⟩
  show (samples (m + 1) >>= fun z => readE >>= fun y => sumcheckRoundPoly 3 y none >>= fun intro =>
    pure [(intro, fun x => eqEval z x)]) sig s = _
  rw [dm_bind, samples_succ_run, dm_bind, readE_run, dm_bind, srp3_run, dm_pure]
  simp only [oodF, ↓reduceIte, oodZ, pos_mk0, pos_msg]
  rfl

theorem oodStep_false (κ : Nat) (sig : ByteArray) (s : RS) : oodStep false κ sig s = ([], s) := rfl

theorem grindPreR_run (g : Nat) (hg : g ≠ 0) (sig : ByteArray) (s : RS) :
    grindPreR g sig s = ((), ⟨pos s + 72, 24, s.ok⟩) := by
  simp only [grindPreR, hg, ↓reduceIte, dm_bind, sampleE_run, readE_run, dm_pure]

theorem powCheckR_run (g : Nat) (hg : g ≠ 0) (sig : ByteArray) (s : RS) :
    powCheckR g sig s = ((), ⟨pos s + 72, 0, powOKR g (feAt sig (pos s + 40)) && s.ok⟩) := by
  simp only [powCheckR, hg, ↓reduceIte, dm_bind, sampleE_run, require_runW]

theorem pos_mk72 (a : Nat) (o : Bool) : pos ⟨a, 72, o⟩ = a + 72 := rfl
theorem pos_mk24 (a : Nat) (o : Bool) : pos ⟨a, 24, o⟩ = a + 24 := rfl

theorem grindPreR_zero (sig : ByteArray) (s : RS) : grindPreR 0 sig s = ((), s) := rfl
theorem powCheckR_zero (sig : ByteArray) (s : RS) : powCheckR 0 sig s = ((), s) := rfl

/-! ## One level of `whirLevels` -/

theorem whirLevels_step (ν lf : Nat) (B : List FE → FE) (g : Nat) (ood : Bool) (L N : Level) (rest : List Level)
    (st : WhirState) (sig : ByteArray) (s : RS) (V : Nat) (hs : pos s = 8 * V) (hrow : L.row % 8 = 0)
    (hκ : L.kappa = ν - (st.folds.length + L.fold)) (hκ1 : 1 ≤ L.kappa) :
    whirLevels ν lf B false g ood (L :: N :: rest) st sig s =
      whirLevels ν lf B false g ood (N :: rest)
        (glue (feAt sig (8 * (lvLanes g ood L (some N) V).V3 + 40))
          ⟨frQ sig (8 * V) L.fold st.runningQuad, st.folds ++ frC sig (8 * V) L.fold, st.glued⟩
          (oodF sig ood L.kappa (8 * (lvLanes g ood L (some N) V).Vc) ++
          [([feAt sig (8 * (lvLanes g ood L (some N) V).V5 + 40),
              Lvm.dot (powers (feAt sig (8 * (lvLanes g ood L (some N) V).V3 + 40)) L.t)
                ((List.range L.t).map fun j =>
                  if L.level = 0 then foldRow0 sig (eqKernelA (frC sig (8 * V) L.fold))
                    (8 * ((lvLanes g ood L (some N) V).V4 + 1 + oStr L * j)) (L.row / 8)
                  else foldRowE sig (eqKernelA (frC sig (8 * V) L.fold))
                    (8 * ((lvLanes g ood L (some N) V).V4 + 1 + oStr L * j)) (2 ^ L.fold)) +
                feAt sig (8 * (lvLanes g ood L (some N) V).V5 + 64),
              feAt sig (8 * (lvLanes g ood L (some N) V).V5 + 64)],
            fun x => inducedWeight L.kappa
              (qsAt sig (8 * (lvLanes g ood L (some N) V).V2) L)
              (powers (feAt sig (8 * (lvLanes g ood L (some N) V).V3 + 40)) L.t) x)]))
        sig ⟨8 * (lvLanes g ood L (some N) V).V5, 48, powF sig g (8 * (lvLanes g ood L (some N) V).Vo) && s.ok⟩ := by
  have hD : 40 + L.row + 104 * L.path = 8 * oStr L := by unfold oStr; omega
  conv_lhs => rw [whirLevels]
  have hfl : ∀ (x : List FE), (st.folds ++ x).length = st.folds.length + x.length := fun x => List.length_append
  have base := fun (h1 : List (List FE × (List FE → FE)) → Prop) => h1
  cases ood <;> rcases Nat.eq_zero_or_pos g with rfl | hg
  all_goals first
    | (have hg0 : g ≠ 0 := Nat.pos_iff_ne_zero.mp hg
       simp only [oodStep_true _ hκ1, oodStep_false, grindPreR_run _ hg0, powCheckR_run _ hg0,
        dm_bind, dm_pure, skip_run, read_run, sampleE_run, srp3_run, foldRounds_fst, foldRounds_pos,
        foldRounds_ok, positionsR_fst, positionsR_pos, positionsR_ok, pos_upd, pos_mk0, pos_mk72, pos_mk24, pos_mk48,
        openingR_mk, hs, List.nil_append, hfl, frC_length, qsAt_length, List.map_map, Nat.zero_add, Function.comp_def, ← hκ]
       simp only [lvLanes, oodF, powF, nodeBytes, hg0, Bool.and_true, Bool.true_and, Bool.and_false,
        Option.isSome_some, ↓reduceIte, Bool.false_eq_true, List.nil_append, hD]
       ring_nf)
    | (simp only [oodStep_true _ hκ1, oodStep_false, grindPreR_zero, powCheckR_zero,
        dm_bind, dm_pure, skip_run, read_run, sampleE_run, srp3_run, foldRounds_fst, foldRounds_pos,
        foldRounds_ok, positionsR_fst, positionsR_pos, positionsR_ok, pos_upd, pos_mk0, pos_mk72, pos_mk24, pos_mk48,
        openingR_mk, hs, List.nil_append, hfl, frC_length, qsAt_length, List.map_map, Nat.zero_add, Function.comp_def, ← hκ]
       simp only [lvLanes, oodF, powF, nodeBytes, Bool.and_true, Bool.true_and, Bool.and_false,
        Option.isSome_some, ↓reduceIte, Bool.false_eq_true, List.nil_append, hD]
       ring_nf)

/-- The final level of `whirLevels` from position `8V`, explicitly (`m` = the message log). -/
theorem whirLevels_final (ν lf : Nat) (B : List FE → FE) (g : Nat) (ood : Bool) (L : Level) (st : WhirState)
    (sig : ByteArray) (s : RS) (V : Nat) (hs : pos s = 8 * V) (hrow : L.row % 8 = 0)
    (hκ : L.kappa = ν - (st.folds.length + L.fold)) (hm : 1 ≤ L.kappa) :
    let ll := lvLanes g ood L none V
    let lam := feAt sig (8 * ll.V3 + 40)
    let st' := glue lam ⟨frQ sig (8 * V) L.fold st.runningQuad, st.folds ++ frC sig (8 * V) L.fold, st.glued⟩
      [([feAt sig (8 * ll.V5 + 40),
          Lvm.dot (powers lam L.t) ((List.range L.t).map fun j =>
              if L.level = 0 then foldRow0 sig (eqKernelA (frC sig (8 * V) L.fold)) (8 * (ll.V4 + 1 + oStr L * j))
                (L.row / 8)
              else foldRowE sig (eqKernelA (frC sig (8 * V) L.fold)) (8 * (ll.V4 + 1 + oStr L * j)) (2 ^ L.fold)) +
            feAt sig (8 * ll.V5 + 64),
          feAt sig (8 * ll.V5 + 64)],
        fun x => inducedWeight L.kappa (qsAt sig (8 * ll.V2) L) (powers lam L.t) x)]
    let tf := frC sig (8 * ll.V6) L.kappa
    let point := st'.folds ++ tf
    let weight := st'.glued.foldl
      (fun w cl => w + cl.scalar * cl.weightAt (st'.folds.drop cl.foldStart ++ tf))
      (B (point.drop lf ++ point.take lf))
    whirLevels ν lf B false g ood [L] st sig s =
      ((), ⟨8 * ll.V6 + 120 * (L.kappa - 1) + 72, 0,
        (weight * multilinearEval ((List.range (2 ^ L.kappa)).map fun i => feAt sig (8 * ll.V1 + 40 + 24 * i)) tf ==
          tlT sig (8 * ll.V6) L.kappa st'.runningQuad) && (powF sig g (8 * ll.Vo) && s.ok)⟩) := by
  dsimp only
  have hD : 40 + L.row + 104 * L.path = 8 * oStr L := by unfold oStr; omega
  conv_lhs => rw [whirLevels]
  have hfl : ∀ (x : List FE), (st.folds ++ x).length = st.folds.length + x.length := fun x => List.length_append
  rcases Nat.eq_zero_or_pos g with rfl | hg
  all_goals first
    | (have hg0 : g ≠ 0 := Nat.pos_iff_ne_zero.mp hg
       simp only [grindPreR_run _ hg0, powCheckR_run _ hg0, dm_bind, dm_pure, read_run, sampleE_run, srp3_run,
        readEs_run, require_runW, foldRounds_fst, foldRounds_pos, foldRounds_ok, positionsR_fst, positionsR_pos,
        positionsR_ok, pos_upd, pos_mk0, pos_mk24, pos_mk48, openingR_mk, hs, List.nil_append, hfl, frC_length,
        qsAt_length, List.map_map, Nat.zero_add, Function.comp_def, ← hκ, tailRounds_run L.kappa hm,
        Bool.false_eq_true, ↓reduceIte, pos_msg]
       simp only [lvLanes, powF, hg0, Bool.and_false, Option.isSome_none, Bool.false_eq_true, ↓reduceIte, hD]
       ring_nf)
    | (simp only [grindPreR_zero, powCheckR_zero, dm_bind, dm_pure, read_run, sampleE_run, srp3_run,
        readEs_run, require_runW, foldRounds_fst, foldRounds_pos, foldRounds_ok, positionsR_fst, positionsR_pos,
        positionsR_ok, pos_upd, pos_mk0, pos_mk24, pos_mk48, openingR_mk, hs, List.nil_append, hfl, frC_length,
        qsAt_length, List.map_map, Nat.zero_add, Function.comp_def, ← hκ, tailRounds_run L.kappa hm,
        Bool.false_eq_true, ↓reduceIte, pos_msg]
       simp only [lvLanes, powF, Bool.and_false, Option.isSome_none, Bool.false_eq_true, ↓reduceIte, hD, Bool.true_and]
       ring_nf)
end Lvm.Har
end
-- ===== end of `LvmQAsmArith2WhirF` =====

-- ===== merged from `LvmQAsmArith2WhirLS` (GOLF module merge: `LvmQAsmArith2WhirLS.lean` is now a stub importing `LvmQAsmArith2Whir`) =====
section
-- New for lvm (HAR-WH): the soundness of one stacked opening's levels: the circuit's `levelsG`
-- replays `F`'s `whirLevels` (`levels_run`), level by level (`lvPre_spec`, `whirLevels_step`,
-- `whirLevels_final`).

/-!
# The levels of a stacked opening replay `F`'s `whirLevels`

* `lvPre_spec`: one level's prefix gadget (`lvPre`) computes `F`'s running quadratic after the
  glue, `λ`, and the level's column weight `inducedWeight κ qs (powers λ t) (point.drop F_i)`.
* **`levels_run`**: wherever `levelsG` holds and asserts (gate on), `F`'s `whirLevels` from any
  state at position `8V` keeps `ok`, ends at `8 · stackEndL`, `msg = 0`. Invariants: `ChOk` (the
  challenge cells hold `F`'s challenges), `PosOk` (the position cells hold `F`'s positions), `GlOk`
  (the glued claims are the `(λ, W)` cells), the folds so far are a prefix of the point.
-/

set_option autoImplicit false
namespace Lvm.Har
open Lvm Lvm.Loop Lvm.Loop.Build DM
variable {c : Ctx} {M : Mem}

-- `okb` is in `LvmQAsmArith2WhirOk` (lvm2 roll 8: off the B program's build path).

theorem val_E {x : Cell} (hx : x.ty = .E) : x.val M = M.e x.n := by
  obtain ⟨ty, n⟩ := x; cases hx; rfl

theorem ptv_getD (pc ν n k : Nat) (h : n + k < ν) :
    ((ptv M pc ν).drop n).getD k 0 = M.e (pc + n + k) := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_drop, ptv, List.getElem?_map,
    List.getElem?_range h, Option.map_some, Option.getD_some, Nat.add_assoc]

theorem ptv_length (pc ν : Nat) : (ptv M pc ν).length = ν := by simp [ptv]

theorem frC_getD (sig : ByteArray) (P n j : Nat) (h : j < n) :
    (frC sig P n).getD j 0 = feAt sig (P + 120 * j + 40) := by
  rw [frC, List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range h]; rfl

theorem dot_map_range (lam : FE) (t : Nat) (φ : Nat → FE) :
    Lvm.dot (powers lam t) ((List.range t).map φ) = ∑ q ∈ Finset.range t, lam ^ q * φ q := by
  have := dot_powers lam ((List.range t).map φ)
  simp only [List.length_map, List.length_range] at this
  rw [this]
  refine Finset.sum_congr rfl fun q hq => ?_
  rw [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range (Finset.mem_range.mp hq)]
  rfl

theorem lvLanes_facts (g : Nat) (ood : Bool) (L : Level) (nxt : Option Level) (V : Nat) :
    (lvLanes g ood L nxt V).V1 = V + 15 * L.fold ∧ (lvLanes g ood L nxt V).V1 ≤ (lvLanes g ood L nxt V).Vc ∧
    (lvLanes g ood L nxt V).V2 ≤ (lvLanes g ood L nxt V).V3 ∧ (lvLanes g ood L nxt V).V4 = (lvLanes g ood L nxt V).V3 + 9 ∧
    (lvLanes g ood L nxt V).V5 = (lvLanes g ood L nxt V).V4 + oStr L * L.t ∧
    (lvLanes g ood L nxt V).V6 = (lvLanes g ood L nxt V).V5 + 6 ∧
    (lvLanes g ood L nxt V).Vc ≤ (lvLanes g ood L nxt V).Vo ∧
    (lvLanes g ood L nxt V).Vo = (if ood && nxt.isSome then (lvLanes g ood L nxt V).Vc + 9 * L.kappa + 9
      else (lvLanes g ood L nxt V).Vc) ∧
    (lvLanes g ood L nxt V).V2 = (if g = 0 then (lvLanes g ood L nxt V).Vo else (lvLanes g ood L nxt V).Vo + 21) ∧
    (lvLanes g ood L nxt V).Vo ≤ (lvLanes g ood L nxt V).V2 := by
  cases nxt <;> cases ood <;> by_cases hg : g = 0 <;> simp [lvLanes, hg] <;> (clear * -; omega)

/-! ## The OOD weight and the PoW check -/

theorem eqZG_spec {zc : Cell} : ∀ (ab : List (Cell × Cell)) (acc : Cell) (p : Ptr),
    SegsHold c M p (eqZG zc ab acc p).2 → zc.val M = 0 →
    (eqZG zc ab acc p).1.val M = acc.val M * (ab.map fun x => 1 + x.1.val M + x.2.val M).prod
  | [], acc, p, _, _ => by simp [eqZG, pure_apply]
  | (a, b) :: ab, acc, p, h, hz => by
    simp only [eqZG, bind_apply] at h ⊢
    rw [segsHold_append] at h
    obtain ⟨h1, h⟩ := h
    rw [segsHold_append] at h
    obtain ⟨h2, h⟩ := h
    rw [eqZG_spec ab _ _ h hz, mulAdd_spec h2, lin_spec h1, hz, ofK_one, one_mul, add_zero]
    simp only [List.map_cons, List.prod_cons]
    ring

theorem eqEval_range (κ : Nat) (zf xf : Nat → FE) :
    eqEval ((List.range κ).map zf) ((List.range κ).map xf) =
      ((List.range κ).map fun j => 1 + zf j + xf j).prod := by
  rw [eqEval, List.zipWith_map, List.zipWith_self, ← List.prod_eq_foldl]

theorem eqZG_range {zc acc : Cell} {κ : Nat} {cz cx : Nat → Cell} {p : Ptr}
    (h : SegsHold c M p (eqZG zc ((List.range κ).map fun j => (cz j, cx j)) acc p).2) (hz : zc.val M = 0)
    (hacc : acc.val M = 1) :
    (eqZG zc ((List.range κ).map fun j => (cz j, cx j)) acc p).1.val M =
      eqEval ((List.range κ).map fun j => (cz j).val M) ((List.range κ).map fun j => (cx j).val M) := by
  rw [eqZG_spec _ _ _ h hz, hacc, one_mul, eqEval_range, List.map_map]
  rfl

/-- **The PoW check from the lane bound** (PI-GRIND): lane 2 of the answer below `2^(64−g)` makes
`eToNat c < 2^(192−g)`. -/
theorem powOKR_of {g : Nat} (hg : g ≤ 64) (sig : ByteArray) (o : Nat)
    (h : (kAt sig (o + 16)).val.toNat < 2 ^ (64 - g)) : powOKR g (feAt sig o) = true := by
  unfold powOKR eToNat feAt kToNat
  apply decide_eq_true
  dsimp only
  have h0 := (kAt sig o).val.toNat_lt
  have h1 := (kAt sig (o + 8)).val.toNat_lt
  have e : 2 ^ (192 - g) = 2 ^ 128 * 2 ^ (64 - g) := by rw [← pow_add]; congr 1; (clear * - hg; omega)
  rw [e]
  have h2 : (kAt sig (o + 16)).val.toNat + 1 ≤ 2 ^ (64 - g) := h
  have h3 : 2 ^ 128 * ((kAt sig (o + 16)).val.toNat + 1) ≤ 2 ^ 128 * 2 ^ (64 - g) := Nat.mul_le_mul_left _ h2
  have : (kAt sig o).val.toNat + 2 ^ 64 * (kAt sig (o + 8)).val.toNat < 2 ^ 128 := by
    have : 2 ^ 64 * (kAt sig (o + 8)).val.toNat ≤ 2 ^ 64 * (2 ^ 64 - 1) := Nat.mul_le_mul_left _ (by (clear * - h1; omega))
    norm_num at this ⊢; (clear * - h0 h1; omega)
  nlinarith

/-- If `z` holds zero, the sequence of `n` zero rows in `lvPre` forces the `n` consecutive
`E` cells from its incoming pointer to hold zero. -/
theorem seqZeros_hold (z : Cell) (hz : z.val M = 0) : ∀ (n : Nat) (p : Ptr),
    SegsHold c M p (seqAll ((List.range n).map fun _ => lin .E 0 0 z z) p).2 →
      ∀ k < n, M.e (p.e + k) = 0
  | 0, _, _, _, hk => by (clear * - hk; omega)
  | n + 1, p, h, k, hk => by
    simp only [List.range_succ_eq_map, List.map_cons, List.map_map, Function.comp_def,
      seqAll, bind_apply, pure_apply, List.append_nil] at h
    rw [segsHold_append] at h
    have hzero := lin_spec h.1
    have hadv : p.adv (lin .E 0 0 z z p).2 = ⟨p.k, p.e + 1⟩ := by
      simp [lin, rowRes, Ptr.adv, segsW, Seg.w, Row.w, Row.writes]
    rw [hadv] at h
    cases k with
    | zero => simpa [lin, rowRes, Ptr.at, hz, ofK_zero] using hzero
    | succ k =>
      simpa [Nat.add_assoc, Nat.add_comm 1 k] using seqZeros_hold z hz n ⟨p.k, p.e + 1⟩ h.2 k (by (clear * - hk; omega))

/-- Factor a shared builder continuation out of an `if`, whose true branch first runs `m`
and whose branches return `a` and `b`, respectively. -/
theorem ite_bind_eq_bind_ite {α β γ : Type} (P : Prop) [Decidable P] (m : BM α) (a b : β) (f : β → BM γ) :
    (if P then m >>= fun _ => pure a >>= f else pure b >>= f) =
      ((if P then m >>= fun _ => pure a else pure b) >>= f) := by
  funext p
  by_cases h : P <;>
    simp only [h, ite_true, ite_false, bind_apply, pure_apply, List.append_nil,
      List.nil_append, Ptr.adv_nil]

theorem lvPre_spec (C : SCfg) {sig : ByteArray} {T : Nat} (hS : Lvm.Q1.Streamed M sig T) (pc : Nat)
    (zc oc g : Cell) (zk : Nat) (hz : zc.val M = 0) (ho : oc.val M = 1) (hzE : zc.ty = .E)
    (hoE : oc.ty = .E) (hgK : g.ty = .K) (hg : g.val M = 1) (hzk : M.k zk = 0)
    (L : Level) (nxt : Option Level) (i f V : Nat) (q : Cell × Cell × Cell) (p : Ptr) (hp : 1 ≤ p.e)
    (hν : f + L.fold + L.kappa = C.nu) (hw0 : L.level ≠ 0 ∨ (0 < L.fold ∧ L.row / 8 ≤ 2 ^ L.fold))
    (htc : L.t ≤ pw (C.pch i))
    (hch : ∀ k < (C.pch i).length, pw ((C.pch i).take k) < L.t) (hcs : csum (C.cch i) = L.kappa)
    (hT1 : (lvLanes C.g C.ood L nxt V).V4 + 1 + oStr L * (L.t - 1) + 3 * 2 ^ L.fold + 2 < T)
    (hT2 : (lvLanes C.g C.ood L nxt V).V6 + 8 < T) (hg64 : C.g ≤ 64)
    (hfold : ∀ j < L.fold, M.e (pc + f + j) = feAt sig (8 * V + 120 * j + 40))
    (hpos : ∀ j < L.t, FE.ofK (M.k (C.pb i + j)) =
      eOfNat ((qsAt sig (8 * (lvLanes C.g C.ood L nxt V).V2) L).getD j 0))
    (hpw : C.g ≠ 0 → (M.k (C.pw i)).val.toNat < 2 ^ (64 - C.g))
    (h : Lvm.QSig.Ok c M (lvPre C pc zc oc g zk L nxt i f V q) p) :
    qv M (lvPre C pc zc oc g zk L nxt i f V q p).1.1 =
      (if C.ood && nxt.isSome then
        List.zipWith (fun a b => a + 1 * feAt sig (8 * (lvLanes C.g C.ood L nxt V).V3 + 40) *
            feAt sig (8 * (lvLanes C.g C.ood L nxt V).V3 + 40) * b)
          (List.zipWith (fun a b => a + 1 * feAt sig (8 * (lvLanes C.g C.ood L nxt V).V3 + 40) * b)
            (frQ sig (8 * V) L.fold (qv M q))
            ((oodF sig true L.kappa (8 * (lvLanes C.g C.ood L nxt V).Vc)).headD ([], fun _ => 0)).1)
      else
        List.zipWith (fun a b => a + 1 * feAt sig (8 * (lvLanes C.g C.ood L nxt V).V3 + 40) * b)
          (frQ sig (8 * V) L.fold (qv M q)))
        [feAt sig (8 * (lvLanes C.g C.ood L nxt V).V5 + 40),
          Lvm.dot (powers (feAt sig (8 * (lvLanes C.g C.ood L nxt V).V3 + 40)) L.t) ((List.range L.t).map fun j =>
            if L.level = 0 then foldRow0 sig (eqKernelA (frC sig (8 * V) L.fold))
              (8 * ((lvLanes C.g C.ood L nxt V).V4 + 1 + oStr L * j)) (L.row / 8)
            else foldRowE sig (eqKernelA (frC sig (8 * V) L.fold))
              (8 * ((lvLanes C.g C.ood L nxt V).V4 + 1 + oStr L * j)) (2 ^ L.fold)) +
            feAt sig (8 * (lvLanes C.g C.ood L nxt V).V5 + 64),
          feAt sig (8 * (lvLanes C.g C.ood L nxt V).V5 + 64)] ∧
    (lvPre C pc zc oc g zk L nxt i f V q p).1.2.map (fun x => (x.1.val M, x.2.val M)) =
      (if C.ood && nxt.isSome then
        [(1 * feAt sig (8 * (lvLanes C.g C.ood L nxt V).V3 + 40),
            eqEval (oodZ sig (8 * (lvLanes C.g C.ood L nxt V).Vc) L.kappa) ((ptv M pc C.nu).drop (f + L.fold))),
          (1 * feAt sig (8 * (lvLanes C.g C.ood L nxt V).V3 + 40) * feAt sig (8 * (lvLanes C.g C.ood L nxt V).V3 + 40),
            inducedWeight L.kappa (qsAt sig (8 * (lvLanes C.g C.ood L nxt V).V2) L)
              (powers (feAt sig (8 * (lvLanes C.g C.ood L nxt V).V3 + 40)) L.t) ((ptv M pc C.nu).drop (f + L.fold)))]
      else
        [(1 * feAt sig (8 * (lvLanes C.g C.ood L nxt V).V3 + 40),
          inducedWeight L.kappa (qsAt sig (8 * (lvLanes C.g C.ood L nxt V).V2) L)
            (powers (feAt sig (8 * (lvLanes C.g C.ood L nxt V).V3 + 40)) L.t) ((ptv M pc C.nu).drop (f + L.fold)))]) ∧
    powF sig C.g (8 * (lvLanes C.g C.ood L nxt V).Vo) = true := by
  have lf := lvLanes_facts C.g C.ood L nxt V
  obtain ⟨l1, l2, l3, l4, l5, l6, l7, l8, l9, l10⟩ := lf
  simp only [lvPre] at h ⊢
  generalize (lvLanes C.g C.ood L nxt V).V1 = V1 at *
  generalize (lvLanes C.g C.ood L nxt V).V2 = V2 at *
  generalize (lvLanes C.g C.ood L nxt V).V3 = V3 at *
  generalize (lvLanes C.g C.ood L nxt V).V4 = V4 at *
  generalize (lvLanes C.g C.ood L nxt V).V5 = V5 at *
  generalize (lvLanes C.g C.ood L nxt V).V6 = V6 at *
  generalize (lvLanes C.g C.ood L nxt V).Vc = Vc at *
  generalize (lvLanes C.g C.ood L nxt V).Vo = Vo at *
  have hpw2 : L.t ≤ 2 ^ Nat.clog 2 (pw (C.pch i)) := le_trans htc (Nat.le_pow_clog (by norm_num) _)
  -- 1. fold rounds
  obtain ⟨h1, h⟩ := okb h
  rw [bind_apply]; dsimp only
  have e1 := roundsG_spec hS L.fold f V q p (by (clear * - l1 l3 hT1 l4 l5 l6 l2 l9 l10 l7 l8; omega)) hfold h1.1
  have hp1 := le_trans hp (adv_e_le p (roundsG pc f V L.fold q p).2)
  generalize (roundsG pc f V L.fold q p).1 = q1 at h e1 ⊢
  generalize p.adv (roundsG pc f V L.fold q p).2 = p1 at h hp1 ⊢
  -- 2. λ
  obtain ⟨h2, h⟩ := okb h
  rw [bind_apply]; dsimp only
  have e2 := ldE_spec hS (by (clear * - hT1 l4 l5 l6; omega)) h2.1
  rw [ldE_out] at e2 h ⊢
  rw [ldEW_adv] at h ⊢
  have e2' : M.e p1.e = feAt sig (8 * V3 + 40) := by
    rw [show 8 * V3 + 40 = 8 * (V3 + 5) by ring]; exact e2
  -- 3. powers of λ
  obtain ⟨h3, h⟩ := okb h
  rw [bind_apply]; dsimp only
  have e3 := pows_spec h3.1 hz ho hoE
  have hlp : ∀ k < L.t, M.e ((pows (Nat.clog 2 (pw (C.pch i))) (ec p1.e) oc zc ⟨p1.k, p1.e + 1⟩).1 + k) =
      feAt sig (8 * V3 + 40) ^ k := fun k hk => by rw [e3 k (by (clear * - hpw2 hk; omega)), Cell.val_E, e2']
  have hp3 : 1 ≤ ((⟨p1.k, p1.e + 1⟩ : Ptr).adv
      (pows (Nat.clog 2 (pw (C.pch i))) (ec p1.e) oc zc ⟨p1.k, p1.e + 1⟩).2).e :=
    le_trans (by simp) (adv_e_le _ _)
  generalize (pows (Nat.clog 2 (pw (C.pch i))) (ec p1.e) oc zc ⟨p1.k, p1.e + 1⟩).1 = lp at h hlp ⊢
  generalize (⟨p1.k, p1.e + 1⟩ : Ptr).adv
    (pows (Nat.clog 2 (pw (C.pch i))) (ec p1.e) oc zc ⟨p1.k, p1.e + 1⟩).2 = p3 at h hp3 ⊢
  -- 4. the fold `eq` table
  obtain ⟨h4, h⟩ := okb h
  rw [bind_apply]; dsimp only
  have hlen := frC_length sig (8 * V) L.fold
  have h4' := h4.1
  rw [← hlen] at h4'
  have e4 := eqTab_eq (fun j => ec (pc + f + j)) zc oc (decide (L.level = 0)) (frC sig (8 * V) L.fold)
    h4' hz (fun _ => rfl) (by rw [← val_E hoE]; exact ho)
    (fun j hj => by rw [Cell.val_E, frC_getD _ _ _ _ (by (clear * - hlen hj; omega)), hfold j (by (clear * - hlen hj; omega))])
  simp only [hlen] at e4
  have hp4 := le_trans hp3 (adv_e_le p3
    (eqTab (fun j => ec (pc + f + j)) zc oc (decide (L.level = 0)) L.fold p3).2)
  have hend := fun (hn : 0 < L.fold) =>
    eqTab_end (fun j => ec (pc + f + j)) zc oc (decide (L.level = 0)) hn p3
  generalize (eqTab (fun j => ec (pc + f + j)) zc oc (decide (L.level = 0)) L.fold p3).1 = er0
    at h e4 hend ⊢
  generalize p3.adv (eqTab (fun j => ec (pc + f + j)) zc oc (decide (L.level = 0)) L.fold p3).2 = p4
    at h hp4 hend ⊢
  rw [ite_bind_eq_bind_ite] at h ⊢
  let win : BM Nat := if L.level = 0 ∧ L.row / 8 < 2 ^ L.fold then do
      let _ ← seqAll ((List.range (2 ^ L.fold - L.row / 8)).map fun _ => lin .E 0 0 zc zc)
      pure (er0 + (2 ^ L.fold - L.row / 8))
    else pure er0
  obtain ⟨hwin, h⟩ := okb h
  rw [bind_apply]; dsimp only
  change Lvm.QSig.Ok c M win p4 at hwin
  have hww : decide (L.level = 0) = true → L.row / 8 ≤ 2 ^ L.fold := by
    intro hl
    have hl' : L.level = 0 := of_decide_eq_true hl
    exact (hw0.resolve_left (by simp [hl'])).2
  have e4w : ∀ k < 2 ^ L.fold, M.e ((win p4).1 + k) =
      if decide (L.level = 0) then
        if k < L.row / 8 then (eqKernelA (frC sig (8 * V) L.fold)).getD (L.row / 8 - 1 - k) 0 else 0
      else (eqKernelA (frC sig (8 * V) L.fold)).getD k 0 := by
    intro k hk
    by_cases hnwin : L.level = 0 ∧ L.row / 8 < 2 ^ L.fold
    · have hpositive := (hw0.resolve_left (by simp [hnwin.1])).1
      have heEnd := hend hpositive
      have hzwin := hwin
      simp only [win, if_pos hnwin] at hzwin
      have hzeros := seqZeros_hold zc hz (2 ^ L.fold - L.row / 8) p4 (okb hzwin).1.1
      simp only [win, if_pos hnwin, bind_apply, pure_apply, hnwin.1, decide_true, ite_true]
      by_cases hkw : k < L.row / 8
      · rw [if_pos hkw]
        have he := e4 (2 ^ L.fold - L.row / 8 + k) (by (clear * - hnwin heEnd hkw; omega))
        simpa only [hnwin.1, decide_true, ite_true,
          show 2 ^ L.fold - 1 - (2 ^ L.fold - L.row / 8 + k) = L.row / 8 - 1 - k by (clear * - hnwin heEnd hkw; omega),
          Nat.add_assoc] using he
      · rw [if_neg hkw, show er0 + (2 ^ L.fold - L.row / 8) + k = p4.e + (k - L.row / 8) by (clear * - hnwin heEnd hkw; omega)]
        exact hzeros (k - L.row / 8) (by (clear * - hk hnwin heEnd hkw; omega))
    · simp only [win, if_neg hnwin, pure_apply]
      by_cases hl : L.level = 0
      · have hw : L.row / 8 = 2 ^ L.fold := by
          have := (hw0.resolve_left (by simp [hl])).2
          (clear * - hnwin hl this; omega)
        simpa [hl, hw, hk] using e4 k hk
      · simpa [hl] using e4 k hk
  have hp4w := le_trans hp4 (adv_e_le p4 (win p4).2)
  generalize (win p4).1 = er at h e4w ⊢
  generalize p4.adv (win p4).2 = p4w at h hp4w ⊢
  -- 5. row folds and the enforced sum
  obtain ⟨h5, h⟩ := okb h
  rw [bind_apply]; dsimp only
  have e5 := foldsG_window_spec hS hz (eqKernelA (frC sig (8 * V) L.fold)) (feAt sig (8 * V3 + 40)) hww e4w hlp
    (fun k hk => by
      have : oStr L * k ≤ oStr L * (L.t - 1) := Nat.mul_le_mul_left _ (by (clear * - hk; omega))
      (clear * - hT1 l5 l6 this; omega))
    (C.pch i) 0 p4w hp4w (by simpa [pw] using htc) (fun k hk => by simpa [pw] using hch k hk) h5.1
  have hp5 := le_trans hp4w (adv_e_le p4w (foldsG (decide (L.level = 0)) L.fold (V4 + 1) (oStr L) er lp
    L.t zc 0 (C.pch i) p4w).2)
  generalize (foldsG (decide (L.level = 0)) L.fold (V4 + 1) (oStr L) er lp L.t zc 0 (C.pch i) p4w).1 = enf
    at h e5 ⊢
  generalize p4w.adv (foldsG (decide (L.level = 0)) L.fold (V4 + 1) (oStr L) er lp L.t zc 0 (C.pch i)
    p4w).2 = p5 at h hp5 ⊢
  -- 6. the intro polynomial
  obtain ⟨h6, h⟩ := okb h
  rw [bind_apply]; dsimp only
  have e6 := rdQ_spec hS (by (clear * - hT2 l6; omega)) h6.1
  have hp6 := le_trans hp5 (adv_e_le p5 (rdQ V5 enf p5).2)
  generalize (rdQ V5 enf p5).1 = it at h e6 ⊢
  generalize p5.adv (rdQ V5 enf p5).2 = p6 at h hp6 ⊢
  -- 7. pointer, 8. roots and inverses
  obtain ⟨-, h⟩ := okb h
  rw [bind_apply]; dsimp only [getPtr] at h ⊢
  rw [Ptr.adv_nil] at h ⊢
  obtain ⟨h8, h⟩ := okb h
  rw [bind_apply]; dsimp only
  have e8 := iwConsts_spec L.kappa hgK h8.1
  have hp8 := le_trans hp6 (adv_e_le p6 (iwConsts L.kappa g p6).2)
  generalize p6.adv (iwConsts L.kappa g p6).2 = p8 at h hp8 ⊢
  -- 9. the column weight
  obtain ⟨h9, h⟩ := okb h
  rw [bind_apply]; dsimp only
  have hptl : ((ptv M pc C.nu).drop (f + L.fold)).length = L.kappa := by
    rw [List.length_drop, ptv_length]; (clear * - hν hcs; omega)
  have e9 := colWG_spec hzE hz hzk L.kappa (qsAt sig (8 * V2) L) (feAt sig (8 * V3 + 40))
    ((ptv M pc C.nu).drop (f + L.fold)) (by rw [hptl, hcs])
    (fun k hk => by rw [ptv_getD _ _ _ _ (by (clear * - hν hcs hptl hk; omega))])
    (fun k hk => by rw [hptl] at hk; exact (e8 k hk).2)
    (fun k hk => by rw [hptl] at hk; exact (e8 k hk).1) hlp hpos (C.pch i) 0 p8
    hp8 (by simpa [pw] using htc) (fun k hk => by simpa [pw] using hch k hk) h9.1
  have eW : (colWG (C.cch i) (pc + (f + L.fold)) (p6.k + L.kappa) p6.k lp (C.pb i) L.t zc zk 0 (C.pch i)
      p8).1.val M = inducedWeight L.kappa (qsAt sig (8 * V2) L) (powers (feAt sig (8 * V3 + 40)) L.t)
        ((ptv M pc C.nu).drop (f + L.fold)) := by
    rw [e9, ← Finset.range_eq_Ico, ← qsAt_length sig (8 * V2) L, inducedWeight_pow]
  have hp9 := le_trans hp8 (adv_e_le p8 (colWG (C.cch i) (pc + (f + L.fold)) (p6.k + L.kappa) p6.k lp
    (C.pb i) L.t zc zk 0 (C.pch i) p8).2)
  generalize (colWG (C.cch i) (pc + (f + L.fold)) (p6.k + L.kappa) p6.k lp (C.pb i) L.t zc zk 0 (C.pch i)
    p8).1 = W at h eW ⊢
  generalize p8.adv (colWG (C.cch i) (pc + (f + L.fold)) (p6.k + L.kappa) p6.k lp (C.pb i) L.t zc zk 0
    (C.pch i) p8).2 = p9 at h hp9 ⊢
  -- 10. the PoW check
  obtain ⟨h10, h⟩ := okb h
  rw [bind_apply]; dsimp only
  have hpow : powF sig C.g (8 * Vo) = true := by
    unfold powF
    split_ifs with hg0
    · rfl
    · obtain ⟨gt, gn⟩ := g
      cases hgK
      have hV2 : V2 = Vo + 21 := by rw [l9]; simp [hg0]
      simp only [powG, hg0, ↓reduceIte] at h10
      have e := assertEqKK_spec h10.1 h10.2 (ofK_inj (hg.trans ofK_one.symm))
      have hl := hS (V2 - 2) (by (clear * - l3 hT1 l4 l5 l6 l9 l8 hV2; omega))
      rw [hl] at e
      apply powOKR_of hg64
      rw [show 8 * Vo + 136 + 16 = 8 * (V2 - 2) by (clear * - l9 l8 hV2; omega), e]
      exact hpw hg0
  have hp10 := le_trans hp9 (adv_e_le p9 (powG C V2 i g p9).2)
  generalize p9.adv (powG C V2 i g p9).2 = p10 at h hp10 ⊢
  -- 11. the OOD items and the glue
  by_cases hod : (C.ood && nxt.isSome) = true
  · simp only [hod, ↓reduceIte] at h ⊢
    have hVo : Vo = Vc + 9 * L.kappa + 9 := by rw [l8]; simp [hod]
    obtain ⟨g1, h⟩ := okb h
    rw [bind_apply]; dsimp only
    obtain ⟨ezb, ez⟩ := preloadG_spec hS (fun v hv => by
      simp only [List.mem_map, List.mem_range] at hv; obtain ⟨j, hj, rfl⟩ := hv; (clear * - hcs l3 hT1 l4 l5 l6 l9 l10 l8 hptl hVo hj; omega)) g1.1
    rw [ezb] at h ⊢
    rw [preloadG_adv] at h ⊢
    obtain ⟨g2, h⟩ := okb h
    rw [bind_apply]; dsimp only
    have ey := ldE_spec hS (by (clear * - hcs l3 hT1 l4 l5 l6 l9 l10 l8 hptl hVo; omega)) g2.1
    rw [ldE_out] at ey h ⊢
    rw [ldEW_adv] at h ⊢
    obtain ⟨g3, h⟩ := okb h
    rw [bind_apply]; dsimp only
    have eio := rdQ_spec hS (by (clear * - hcs l3 hT1 l4 l5 l6 l9 l10 l8 hptl hVo; omega)) g3.1
    rw [rdQ_adv] at h ⊢
    obtain ⟨g4, h⟩ := okb h
    rw [bind_apply]; dsimp only
    have el2 := mulAdd_spec g4.1
    obtain ⟨g5, h⟩ := okb h
    rw [bind_apply]; dsimp only
    have eg1 := glueG_spec g5.1
    obtain ⟨g6, h⟩ := okb h
    rw [bind_apply]; dsimp only
    have eg2 := glueG_spec g6.1
    obtain ⟨g7, -⟩ := okb h
    rw [bind_apply]; dsimp only
    have eo := eqZG_range g7.1 hz ho
    simp only [pure_apply]
    refine ⟨?_, ?_, hpow⟩
    · rw [eg2, eg1, eio, e1, e6, e5, el2, ey, hz, add_zero, Cell.val_E, e2']
      simp only [oodF, ↓reduceIte, List.headD_cons]
      rw [show 8 * (Vc + 9 * L.kappa + 3) + 40 = 8 * Vc + 72 * L.kappa + 24 + 40 by ring,
        show 8 * (Vc + 9 * L.kappa + 3) + 64 = 8 * Vc + 72 * L.kappa + 24 + 64 by ring,
        show 8 * (Vc + 9 * L.kappa + 5) = 8 * Vc + 72 * L.kappa + 40 by ring, dot_map_range,
        Finset.range_eq_Ico]
      simp only [decide_eq_true_eq, mul_one, one_mul, mul_assoc]
    · simp only [List.map_cons, List.map_nil, el2, Cell.val_E, e2', hz, add_zero, eW, eo, one_mul]
      refine List.cons_eq_cons.mpr ⟨?_, rfl⟩
      congr 1
      congr 1
      · simp only [oodZ]
        refine List.map_congr_left fun j hj => ?_
        rw [ez j (by simpa using hj)]
        simp only [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range (List.mem_range.mp hj),
          Option.map_some, Option.getD_some]
        congr 1; ring
      · apply List.ext_getElem (by simp [ptv_length]; (clear * - hν hcs hptl; omega))
        intro k h1 h2
        simp only [List.length_map, List.length_range] at h1
        rw [List.getElem_map, List.getElem_range, ← List.getD_eq_getElem _ 0,
          ptv_getD _ _ _ _ (by (clear * - hν hcs hptl h2; omega))]
  · simp only [hod, Bool.false_eq_true, ↓reduceIte] at h ⊢
    obtain ⟨g5, -⟩ := okb h
    rw [bind_apply]; dsimp only
    have eg1 := glueG_spec g5.1
    simp only [pure_apply]
    refine ⟨?_, ?_, hpow⟩
    · rw [eg1, e1, e6, e5, Cell.val_E, e2', dot_map_range, Finset.range_eq_Ico]
      simp only [decide_eq_true_eq]
    · simp only [List.map_cons, List.map_nil, Cell.val_E, e2', eW, one_mul]


/-! ## Invariants of the level induction -/

/-- The challenge cells from `pc + f` hold `F`'s challenges of the levels `Ls` from lane `V`. -/
def ChOk (g : Nat) (ood : Bool) (M : Mem) (sig : ByteArray) (pc f : Nat) (Ls : List Level) (V : Nat) : Prop :=
  ∀ j < (chLanes g ood Ls V).length, M.e (pc + f + j) = feAt sig (8 * (chLanes g ood Ls V).getD j 0)

/-- The position cells of the levels `Ls` (level `i` first) hold `F`'s positions. -/
def PosOk (C : SCfg) (M : Mem) (sig : ByteArray) (i : Nat) (Ls : List Level) (V : Nat) : Prop :=
  ∀ i' < Ls.length, ∀ j < (Ls.getD i' default).t, FE.ofK (M.k (C.pb (i + i') + j)) =
    eOfNat ((qsAt sig (8 * (posLanes C.g C.ood Ls V).getD i' 0) (Ls.getD i' default)).getD j 0)

/-- The PoW fields of the levels `Ls` (level `i` first) are below `2^(64−g)` (the `BITS` class
`powSpec`'s `fld 0 (64−g) 0` outputs). -/
def PwOk (C : SCfg) (M : Mem) (i : Nat) (Ls : List Level) : Prop :=
  ∀ i' < Ls.length, C.g ≠ 0 → (M.k (C.pw (i + i'))).val.toNat < 2 ^ (64 - C.g)

theorem pwOk_head {C : SCfg} {M : Mem} {i : Nat} {L : Level} {rest : List Level} (h : PwOk C M i (L :: rest)) :
    C.g ≠ 0 → (M.k (C.pw i)).val.toNat < 2 ^ (64 - C.g) := by
  have := h 0 (by simp); simpa using this

theorem pwOk_next {C : SCfg} {M : Mem} {i : Nat} {L : Level} {rest : List Level} (h : PwOk C M i (L :: rest)) :
    PwOk C M (i + 1) rest := by
  intro i' hi' hg
  have := h (i' + 1) (by simp; omega) hg
  rwa [show i + (i' + 1) = i + 1 + i' by ring] at this

/-- The glued claims are the `(λ, W)` cells (weights at the point's suffix). -/
def GlOk (M : Mem) (pc ν f : Nat) (st : WhirState) (gl : List (Cell × Cell)) : Prop :=
  st.glued.map (fun gc => (gc.scalar, gc.weightAt ((ptv M pc ν).drop gc.foldStart))) =
    gl.map (fun x => (x.1.val M, x.2.val M)) ∧ ∀ gc ∈ st.glued, gc.foldStart ≤ f

theorem getD_app_left (a b : List Nat) (j : Nat) (h : j < a.length) : (a ++ b).getD j 0 = a.getD j 0 := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_append_left h]

theorem getD_app_right (a b : List Nat) (j : Nat) : (a ++ b).getD (a.length + j) 0 = b.getD j 0 := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_append_right]

theorem getD_map_range {α : Type} (n j : Nat) (φ : Nat → α) (d : α) (h : j < n) :
    ((List.range n).map φ).getD j d = φ j := by
  simp [List.getD_eq_getElem?_getD, h]

theorem chOk_fold {g : Nat} {ood : Bool} {M : Mem} {sig : ByteArray} {pc f : Nat} {L : Level} {rest : List Level} {V : Nat}
    (h : ChOk g ood M sig pc f (L :: rest) V) : ∀ j < L.fold, M.e (pc + f + j) = feAt sig (8 * V + 120 * j + 40) := by
  intro j hj
  have hl : j < (chLanes g ood (L :: rest) V).length := by
    cases rest <;> simp [chLanes] <;> (clear * - hj; omega)
  rw [h j hl]
  have : (chLanes g ood (L :: rest) V).getD j 0 = V + 15 * j + 5 := by
    cases rest <;> (simp only [chLanes]; rw [getD_app_left _ _ _ (by simpa using hj), getD_map_range _ _ _ _ hj])
  rw [this]; congr 1; ring

theorem chOk_next {g : Nat} {ood : Bool} {M : Mem} {sig : ByteArray} {pc f : Nat} {L N : Level} {rest : List Level} {V : Nat}
    (h : ChOk g ood M sig pc f (L :: N :: rest) V) :
    ChOk g ood M sig pc (f + L.fold) (N :: rest) (lvLanes g ood L (some N) V).V6 := by
  intro j hj
  have e := h (L.fold + j) (by simp only [chLanes] at hj ⊢; simp; omega)
  simp only [chLanes] at e ⊢
  have hlen : ((List.range L.fold).map (fun j => V + 15 * j + 5)).length = L.fold := by simp
  have ga := getD_app_right ((List.range L.fold).map (fun j => V + 15 * j + 5))
    (chLanes g ood (N :: rest) (lvLanes g ood L (some N) V).V6) j
  rw [hlen] at ga
  rw [ga] at e
  rw [show pc + (f + L.fold) + j = pc + f + (L.fold + j) by ring]; exact e

theorem chOk_tail {g : Nat} {ood : Bool} {M : Mem} {sig : ByteArray} {pc f : Nat} {L : Level} {V : Nat}
    (h : ChOk g ood M sig pc f [L] V) :
    ∀ j < L.kappa, M.e (pc + (f + L.fold) + j) = feAt sig (8 * (lvLanes g ood L none V).V6 + 120 * j + 40) := by
  intro j hj
  have e := h (L.fold + j) (by simp [chLanes]; omega)
  simp only [chLanes] at e
  have hlen : ((List.range L.fold).map (fun j => V + 15 * j + 5)).length = L.fold := by simp
  have ga := getD_app_right ((List.range L.fold).map (fun j => V + 15 * j + 5))
    ((List.range L.kappa).map (fun j => (lvLanes g ood L none V).V6 + 15 * j + 5)) j
  rw [hlen] at ga
  rw [ga, getD_map_range _ _ _ _ hj] at e
  rw [show pc + (f + L.fold) + j = pc + f + (L.fold + j) by ring, e]; congr 1; ring

theorem posOk_head {C : SCfg} {M : Mem} {sig : ByteArray} {i : Nat} {L : Level} {rest : List Level} {V : Nat}
    (h : PosOk C M sig i (L :: rest) V) : ∀ j < L.t, FE.ofK (M.k (C.pb i + j)) =
      eOfNat ((qsAt sig (8 * (lvLanes C.g C.ood L rest.head? V).V2) L).getD j 0) := by
  intro j hj
  have e := h 0 (by simp) j (by simpa using hj)
  cases rest <;> simpa [posLanes] using e

theorem posOk_next {C : SCfg} {M : Mem} {sig : ByteArray} {i : Nat} {L N : Level} {rest : List Level} {V : Nat}
    (h : PosOk C M sig i (L :: N :: rest) V) : PosOk C M sig (i + 1) (N :: rest) (lvLanes C.g C.ood L (some N) V).V6 := by
  intro i' hi' j hj
  have e := h (i' + 1) (by simp at hi' ⊢; omega) j (by simpa using hj)
  simp only [posLanes] at e
  rw [show i + 1 + i' = i + (i' + 1) by ring]
  simpa using e

theorem glue_one (lam : FE) (st : WhirState) (i : List FE) (w : List FE → FE) :
    glue lam st [(i, w)] = ⟨List.zipWith (fun q i => q + 1 * lam * i) st.runningQuad i, st.folds,
      st.glued ++ [⟨1 * lam, st.folds.length, w⟩]⟩ := rfl

theorem glue_two (lam : FE) (st : WhirState) (i₁ i₂ : List FE) (w₁ w₂ : List FE → FE) :
    glue lam st [(i₁, w₁), (i₂, w₂)] = ⟨List.zipWith (fun q i => q + 1 * lam * lam * i)
      (List.zipWith (fun q i => q + 1 * lam * i) st.runningQuad i₁) i₂, st.folds,
      st.glued ++ [⟨1 * lam, st.folds.length, w₁⟩] ++ [⟨1 * lam * lam, st.folds.length, w₂⟩]⟩ := rfl

theorem ptv_take_append {M : Mem} {pc ν f n : Nat} {a : List FE} (ha : a.length = n) (hν : f + n ≤ ν)
    (h : ∀ j < n, M.e (pc + f + j) = a.getD j 0) : (ptv M pc ν).take f ++ a = (ptv M pc ν).take (f + n) := by
  apply List.ext_getElem
  · simp [ptv, ha]; (clear * - ha hν; omega)
  · intro k h1 h2
    simp only [List.length_append, List.length_take, ptv_length] at h1
    by_cases hk : k < f
    · rw [List.getElem_append_left (by simp [ptv]; (clear * - ha hν hk; omega))]
      simp [ptv]
    · rw [List.getElem_append_right (by simp [ptv]; (clear * - hk; omega))]
      have hm : ((ptv M pc ν).take f).length = f := by simp [ptv]; (clear * - ha hν; omega)
      simp only [hm]
      have e := h (k - f) (by (clear * - ha h1 hk hm; omega))
      rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by (clear * - ha h1 hk hm; omega)), Option.getD_some] at e
      rw [← e]
      simp only [List.getElem_take, ptv, List.getElem_map, List.getElem_range]
      congr 1; (clear * - hk hm; omega)

theorem wh_fe_beq (x y : FE) : (x == y) = true ↔ x = y := by
  obtain ⟨a0, a1, a2⟩ := x
  obtain ⟨b0, b1, b2⟩ := y
  show ((a0 == b0 && a1 == b1) && a2 == b2) = true ↔ _
  simp only [Bool.and_eq_true, beq_iff_eq, FE.mk.injEq, and_assoc]

theorem glued_foldl (gs : List GluedClaim) (fl tf pt : List FE) (b : FE) (hpt : fl ++ tf = pt)
    (hfs : ∀ gc ∈ gs, gc.foldStart ≤ fl.length) :
    gs.foldl (fun w cl => w + cl.scalar * cl.weightAt (fl.drop cl.foldStart ++ tf)) b =
      (gs.map fun gc => (gc.scalar, gc.weightAt (pt.drop gc.foldStart))).foldl (fun acc x => acc + x.1 * x.2) b := by
  induction gs generalizing b with
  | nil => rfl
  | cons gc gs ih =>
    simp only [List.foldl_cons, List.map_cons]
    rw [ih _ (fun g hg => hfs g (List.mem_cons_of_mem _ hg)), ← hpt,
      List.drop_append_of_le_length (hfs gc List.mem_cons_self)]

set_option maxHeartbeats 4000000 in
theorem levels_run (C : SCfg) {sig : ByteArray} {T : Nat} (hS : Lvm.Q1.Streamed M sig T) (pc : Nat)
    (zc oc g : Cell) (zk : Nat) (bas : Cell) (hz : zc.val M = 0) (ho : oc.val M = 1) (hzE : zc.ty = .E)
    (hoE : oc.ty = .E) (hg : g.val M = 1) (hgK : g.ty = .K) (hzk : M.k zk = 0) (lf : Nat)
    (B : List FE → FE) (hbas : bas.val M = B ((ptv M pc C.nu).drop lf ++ (ptv M pc C.nu).take lf)) :
    ∀ (Ls : List Level) (i f V : Nat) (q : Cell × Cell × Cell) (gl : List (Cell × Cell)) (st : WhirState)
      (p : Ptr), lvOk C T Ls i f V = true → 1 ≤ p.e → qv M q = st.runningQuad →
      st.folds = (ptv M pc C.nu).take f → ChOk C.g C.ood M sig pc f Ls V → PosOk C M sig i Ls V →
      PwOk C M i Ls → GlOk M pc C.nu f st gl → Lvm.QSig.Ok c M (levelsG C pc zc oc g zk bas Ls i f V q gl) p →
      ∀ s : RS, pos s = 8 * V →
        (whirLevels C.nu lf B false C.g C.ood Ls st sig s).2.ok = s.ok ∧
        pos (whirLevels C.nu lf B false C.g C.ood Ls st sig s).2 = 8 * stackEndL C.g C.ood Ls V ∧
        (whirLevels C.nu lf B false C.g C.ood Ls st sig s).2.msg = 0 := by
  intro Ls
  induction Ls with
  | nil => intro i f V q gl st p hok; simp [lvOk] at hok
  | cons L rest ih =>
    intro i f V q gl st p hok hp hq hfo hch hpo hpw hgl h s hs
    have hA := fun (n : Nat) (hn : f + L.fold + n = C.nu) => ptv_take_append (M := M) (pc := pc) (ν := C.nu) (f := f)
      (frC_length sig (8 * V) L.fold) (by (clear * - hn; omega)) (fun j hj => by rw [frC_getD _ _ _ _ hj, chOk_fold hch j hj])
    cases rest with
    | nil =>
      simp only [lvOk, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true, List.mem_range,
        and_assoc, List.head?_nil, and_true] at hok
      obtain ⟨hν, hrow, hw0, ht1, htc, hchk, hcs, hT1, hT2, hm, hg64⟩ := hok
      replace hT1 := of_decide_eq_true hT1
      replace hT2 := of_decide_eq_true hT2
      have hfl : st.folds.length = f := by rw [hfo, List.length_take, ptv_length]; (clear * - hν hcs hm; omega)
      obtain ⟨l1, l2, l3, l4, l5, l6, l7, l8, l9, l10⟩ := lvLanes_facts C.g C.ood L none V
      simp only [levelsG, List.head?_nil] at h
      obtain ⟨hpre, h⟩ := okb h
      have hpo0 := posOk_head hpo
      have e := lvPre_spec C hS pc zc oc g zk hz ho hzE hoE hgK hg hzk L none i f V q p hp hν hw0 htc
        hchk hcs hT1 (by (clear * - hT2 l6; omega)) hg64 (chOk_fold hch) hpo0 (pwOk_head hpw) hpre
      generalize (lvPre C pc zc oc g zk L none i f V q p).1 = r at h e
      generalize p.adv (lvPre C pc zc oc g zk L none i f V q p).2 = p' at h
      obtain ⟨eq, el, epw⟩ := e
      simp only [Option.isSome_none, Bool.and_false, Bool.false_eq_true, ↓reduceIte] at eq el
      rw [hq] at eq
      obtain ⟨ht, h⟩ := okb h
      have et := tailG_spec hS L.kappa (f + L.fold) (lvLanes C.g C.ood L none V).V6 r.1 p' hm (by omega)
        (fun j hj => chOk_tail hch j hj) ht.1
      generalize (tailG pc (f + L.fold) (lvLanes C.g C.ood L none V).V6 L.kappa r.1 p').1 = tgt at h et
      generalize p'.adv (tailG pc (f + L.fold) (lvLanes C.g C.ood L none V).V6 L.kappa r.1 p').2 = p2 at h
      obtain ⟨hmf, h⟩ := okb h
      have hVc : (lvLanes C.g C.ood L none V).Vc = (lvLanes C.g C.ood L none V).V1 + 3 * 2 ^ L.kappa := by
        simp [lvLanes]
      have hVcV2 : (lvLanes C.g C.ood L none V).Vc ≤ (lvLanes C.g C.ood L none V).V2 := by
        rw [l9]; split_ifs <;> omega
      have em := mleFold_eq hmf.1 sig
        ((List.range (2 ^ L.kappa)).map fun i => feAt sig (8 * (lvLanes C.g C.ood L none V).V1 + 40 + 24 * i))
        (frC sig (8 * (lvLanes C.g C.ood L none V).V6) L.kappa) (by simp) (frC_length _ _ _)
        (fun j hj => by rw [Cell.val_E, frC_getD _ _ _ _ hj, chOk_tail hch j hj])
        (fun v hv k hk => by
          have : 3 * v < 3 * 2 ^ L.kappa := by (clear * - hv; omega)
          rw [hS _ (by (clear * - hT1 l3 l4 l5 l9 hVc hVcV2 hv hk; omega))]; rfl)
        (fun v hv => by rw [getD_map_range _ _ _ _ hv]; congr 1; ring)
      generalize (mleFold L.kappa ((lvLanes C.g C.ood L none V).V1 + 5) (fun j => ec (pc + (f + L.fold) + j)) p2).1
        = mle at h em
      generalize p2.adv (mleFold L.kappa ((lvLanes C.g C.ood L none V).V1 + 5)
        (fun j => ec (pc + (f + L.fold) + j)) p2).2 = p3 at h
      obtain ⟨hw, h⟩ := okb h
      have ew := wsumG_spec (gl ++ r.2) bas p3 hw.1
      generalize (wsumG bas (gl ++ r.2) p3).1 = w at h ew
      generalize p3.adv (wsumG bas (gl ++ r.2) p3).2 = p4 at h
      have hfin := (terminalCheck_iff h.1 hg).mp h.2
      have hF := whirLevels_final C.nu lf B C.g C.ood L st sig s V hs hrow (by (clear * - hν hcs hm hfl; omega)) hm
      dsimp only at hF
      rw [hF]
      refine ⟨?_, ?_, rfl⟩
      · rw [epw, Bool.true_and, Bool.and_eq_right_iff_imp]
        intro _
        rw [wh_fe_beq, glue_one]
        dsimp only
        rw [← eq, ← et, ← em, hfo, hA L.kappa (by omega)]
        have hB := ptv_take_append (M := M) (pc := pc) (ν := C.nu) (f := f + L.fold)
          (frC_length sig (8 * (lvLanes C.g C.ood L none V).V6) L.kappa) (by (clear * - hν; omega))
          (fun j hj => by rw [frC_getD _ _ _ _ hj, chOk_tail hch j hj])
        rw [List.take_of_length_le (l := ptv M pc C.nu) (i := f + L.fold + L.kappa)
          (by rw [ptv_length]; (clear * - hν; omega))] at hB
        rw [glued_foldl _ _ _ _ _ hB (fun gc hgc => ?_), hB, ← hbas]
        · rw [List.map_append, hgl.1]
          have hnew : ([⟨1 * feAt sig (8 * (lvLanes C.g C.ood L none V).V3 + 40),
              ((ptv M pc C.nu).take (f + L.fold)).length, fun x => inducedWeight L.kappa
                (qsAt sig (8 * (lvLanes C.g C.ood L none V).V2) L)
                (powers (feAt sig (8 * (lvLanes C.g C.ood L none V).V3 + 40)) L.t) x⟩] : List GluedClaim).map
              (fun gc => (gc.scalar, gc.weightAt ((ptv M pc C.nu).drop gc.foldStart))) =
              r.2.map (fun x => (x.1.val M, x.2.val M)) := by
            rw [el]
            simp only [List.map_cons, List.map_nil, List.length_take, ptv_length]
            rw [show min (f + L.fold) C.nu = f + L.fold by (clear * - hν hcs hm; omega)]
          rw [hnew, ← List.map_append, List.foldl_map, ← ew]
          exact hfin
        · rw [List.length_take, ptv_length, show min (f + L.fold) C.nu = f + L.fold by (clear * - hν hcs hm; omega)]
          rcases List.mem_append.mp hgc with h1 | h1
          · exact le_trans (hgl.2 gc h1) (by (clear * - hν hcs hfl; omega))
          · simp only [List.mem_singleton] at h1; subst h1; simp [ptv_length]
      · simp only [pos, stackEndL]
        have : 1 ≤ L.kappa := hm
        (clear * -; omega)
    | cons N rest' =>
      simp only [lvOk, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true, List.mem_range,
        and_assoc, List.head?_cons] at hok
      obtain ⟨hν, hrow, hw0, ht1, htc, hchk, hcs, hT1, hT2, hm, hg64, hrest⟩ := hok
      replace hT1 := of_decide_eq_true hT1
      replace hT2 := of_decide_eq_true hT2
      have hfl : st.folds.length = f := by rw [hfo, List.length_take, ptv_length]; (clear * - hν hcs hm; omega)
      obtain ⟨l1, l2, l3, l4, l5, l6, l7, l8, l9, l10⟩ := lvLanes_facts C.g C.ood L (some N) V
      rw [levelsG] at h
      simp only [List.head?_cons] at h
      obtain ⟨hpre, h⟩ := okb h
      have hpo0 := posOk_head hpo
      have e := lvPre_spec C hS pc zc oc g zk hz ho hzE hoE hgK hg hzk L (some N) i f V q p hp hν hw0 htc
        hchk hcs hT1 (by (clear * - hT2 l6; omega)) hg64 (chOk_fold hch) hpo0 (pwOk_head hpw) hpre
      have hpr := le_trans hp (adv_e_le p (lvPre C pc zc oc g zk L (some N) i f V q p).2)
      generalize (lvPre C pc zc oc g zk L (some N) i f V q p).1 = r at h e
      generalize p.adv (lvPre C pc zc oc g zk L (some N) i f V q p).2 = p' at h hpr
      obtain ⟨eq, el, epw⟩ := e
      simp only [Option.isSome_some, Bool.and_true] at eq el
      rw [hq] at eq
      rw [whirLevels_step C.nu lf B C.g C.ood L N rest' st sig s V hs hrow (by (clear * - hν hcs hm hfl; omega)) hm, epw, Bool.true_and]
      simp only [stackEndL]
      have hfo' : st.folds ++ frC sig (8 * V) L.fold = (ptv M pc C.nu).take (f + L.fold) := by
        rw [hfo]; exact hA L.kappa (by omega)
      by_cases hod : C.ood = true
      · rw [if_pos hod] at eq el
        rw [show oodF sig C.ood = oodF sig true by rw [hod]]
        simp only [oodF, ↓reduceIte, List.headD_cons, List.cons_append, List.nil_append, glue_two] at eq ⊢
        exact ih (i + 1) (f + L.fold) (lvLanes C.g C.ood L (some N) V).V6 r.1 (gl ++ r.2) _ p' hrest hpr
          (by exact eq) (by exact hfo') (chOk_next hch) (posOk_next hpo) (pwOk_next hpw)
          (by
            dsimp only [GlOk]
            refine ⟨?_, ?_⟩
            · rw [List.map_append, List.map_append, hgl.1, List.map_append, el]
              simp only [List.map_cons, List.map_nil, List.length_append, frC_length, hfl, List.append_assoc,
                List.singleton_append]
            · intro gc hgc
              simp only [List.mem_append, List.mem_singleton] at hgc
              rcases hgc with (h1 | h1) | h1
              · exact le_trans (hgl.2 gc h1) (by (clear * - hν hcs hfl; omega))
              · subst h1; simp [frC_length, hfl]
              · subst h1; simp [frC_length, hfl])
          h _ (by simp only [pos]; (clear * - l6; omega))
      · rw [if_neg hod] at eq el
        rw [show oodF sig C.ood = oodF sig false by simp only [Bool.not_eq_true] at hod; rw [hod]]
        simp only [oodF, Bool.false_eq_true, ↓reduceIte, List.nil_append, glue_one]
        exact ih (i + 1) (f + L.fold) (lvLanes C.g C.ood L (some N) V).V6 r.1 (gl ++ r.2) _ p' hrest hpr
          (by exact eq) (by exact hfo') (chOk_next hch) (posOk_next hpo) (pwOk_next hpw)
          (by
            dsimp only [GlOk]
            refine ⟨?_, ?_⟩
            · rw [List.map_append, hgl.1, List.map_append, el]
              simp only [List.map_cons, List.map_nil, List.length_append, frC_length, hfl]
            · intro gc hgc
              rcases List.mem_append.mp hgc with h1 | h1
              · exact le_trans (hgl.2 gc h1) (by (clear * - hν hcs hfl; omega))
              · simp only [List.mem_singleton] at h1; subst h1; simp [frC_length, hfl])
          h _ (by simp only [pos]; (clear * - l6; omega))
end Lvm.Har
end
-- ===== end of `LvmQAsmArith2WhirLS` =====

/-!
# Phases 8–9: the stacked WHIR openings

**`stackGW C cl zc oc g`** is `F`'s `verifyStackedOpening C.levels C.nu (cl.map onStack) false` for
the claims `cl` of one commitment (cells `CClaim`): every fold and tail challenge loaded from the
stream (`preloadG`, `chLanes`' order), the batching challenge `s` and its powers, the target
`Σ s^i v_i` (`targetG`), the basis point (the challenges rotated by the first fold, `copiesG`), the
batched weight `Σ s^i onStack_i(x)` (`basisG`), `verifyWhir`'s first polynomial, the levels
(`levelsG`). **`stack_run`**: wherever it holds and asserts (gate on), `F` from any state at
position `8 U` keeps `ok`, ends at `8 · stackEndL`, `msg = 0`.

**`openPh_replays`**: `openG Cr Cm cs` (`stackGW` on `cs`' `C_rec` claims, then on its `C_main`
claims) replays `openPh p (cs.map (CClaim.val M))` (`Replays`, LvmQAsmHarBase), `C_main` starting
where `C_rec` ends. Hypotheses: the stream (`Streamed`), the static checks (`StackOk`, decidable),
the zero/one/gate cells, the positions (`PosOk`: position `j` of level `i` is the `K` cell
`pb i + j` holding `eOfNat` of `F`'s `j`-th position, `qsAt`).
-/

set_option autoImplicit false

namespace Lvm.Har

open Lvm Lvm.Loop Lvm.Loop.Build DM

variable {c : Ctx} {M : Mem}

theorem xs_eq {pc ν lf xb : Nat} (hlf : lf ≤ ν)
    (h : ∀ i < (((List.range ν).map fun k => ec (pc + k)).drop lf ++
      ((List.range ν).map fun k => ec (pc + k)).take lf).length,
      M.e (xb + i) = ((((List.range ν).map fun k => ec (pc + k)).drop lf ++
        ((List.range ν).map fun k => ec (pc + k)).take lf).getD i default).val M) :
    (List.range ν).map (fun i => M.e (xb + i)) = (ptv M pc ν).drop lf ++ (ptv M pc ν).take lf := by
  have hc : ((((List.range ν).map fun k => ec (pc + k)).drop lf ++
      ((List.range ν).map fun k => ec (pc + k)).take lf)).map (Cell.val M) =
      (ptv M pc ν).drop lf ++ (ptv M pc ν).take lf := by
    rw [List.map_append, List.map_drop, List.map_take, List.map_map]; rfl
  rw [← hc]
  apply List.ext_getElem
  · simp; (clear * - hlf; omega)
  · intro i h1 h2
    simp only [List.length_map, List.length_range] at h1
    rw [List.getElem_map, List.getElem_range, List.getElem_map, h i (by simp; (clear * - hlf h1; omega)),
      List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by simp; (clear * - hlf h1; omega)), Option.getD_some]

set_option maxHeartbeats 1000000 in
/-- **One generic stacked opening replays `F`'s `verifyStackedOpening`** on any claim list `scs` whose batched
values the target and the basis gadgets give. -/
theorem stackG_run {β : Type} (C : SCfg) (n : Nat) (pre : BM β) (tg : β → Nat → BM Cell)
    (bg : β → Nat → Nat → BM Cell) (W : β → Prop) (scs : List StackClaim) (hn : scs.length = n)
    (hpre : Hs c M pre W)
    (htg : ∀ w, W w → ∀ (sp : Nat) (s : FE), (∀ i < n, M.e (sp + i) = s ^ i) →
      Hs c M (tg w sp) (fun t => t.val M = Lvm.dot (powers s n) (scs.map (·.2))))
    (hbg : ∀ w, W w → ∀ (sp xb : Nat) (s : FE), (∀ i < n, M.e (sp + i) = s ^ i) →
      Hs c M (bg w sp xb) (fun b => b.val M =
        Lvm.dot (powers s n) (scs.map fun sc => sc.1 ((List.range C.nu).map fun i => M.e (xb + i)))))
    (zc oc g : Cell) {sig : ByteArray} {T : Nat}
    (hS : Lvm.Q1.Streamed M sig T) (hok : LayOk C T = true) (hz : zc.val M = 0)
    (ho : oc.val M = 1) (hzE : zc.ty = .E) (hoE : oc.ty = .E) (hg : g.val M = 1) (hgK : g.ty = .K)
    (hpos : PosOk C M sig 0 C.levels (C.U + 15)) (hpw : PwOk C M 0 C.levels) {p : Ptr} (hp : 1 ≤ p.e)
    (h : Lvm.QSig.Ok c M (stackGWG C n pre tg bg zc oc g) p) (s : RS) (hs : pos s = 8 * C.U) :
    (verifyStackedOpening C.levels C.nu scs false C.g C.ood sig s).2.ok = s.ok ∧
    pos (verifyStackedOpening C.levels C.nu scs false C.g C.ood sig s).2 =
      8 * stackEndL C.g C.ood C.levels (C.U + 15) ∧
    (verifyStackedOpening C.levels C.nu scs false C.g C.ood sig s).2.msg = 0 := by
  simp only [LayOk, Bool.and_eq_true, List.all_eq_true] at hok
  obtain ⟨⟨⟨hlv, hch⟩, hU⟩, hlf⟩ := hok
  replace hU := of_decide_eq_true hU
  replace hlf := of_decide_eq_true hlf
  simp only [stackGWG] at h
  -- the shape and the muxed claims
  obtain ⟨h0, h⟩ := okb h
  have hw := hpre p h0.1
  have hp0 := le_trans hp (adv_e_le p (pre p).2)
  generalize (pre p).1 = w at h hw
  generalize p.adv (pre p).2 = p at h hp0
  clear hp
  -- the challenges
  obtain ⟨h1, h⟩ := okb h
  obtain ⟨epc, ech⟩ := preloadG_spec hS (fun v hv => of_decide_eq_true (hch v hv)) h1.1
  rw [epc] at h
  have hp1 := le_trans hp0 (adv_e_le p (preloadG (chLanes C.g C.ood C.levels (C.U + 15)) p).2)
  generalize p.adv (preloadG (chLanes C.g C.ood C.levels (C.U + 15)) p).2 = p1 at h hp1
  -- the batching challenge and its powers
  obtain ⟨h2, h⟩ := okb h
  have esb := ldE_spec hS (by (clear * - hU; omega)) h2.1
  rw [ldE_out] at esb h
  rw [ldEW_adv] at h
  have esb' : M.e p1.e = feAt sig (8 * C.U + 40) := by
    rw [show 8 * C.U + 40 = 8 * (C.U + 5) by ring]; exact esb
  obtain ⟨h3, h⟩ := okb h
  have e3 := pows_spec h3.1 hz ho hoE
  have hsp : ∀ i < n,
      M.e ((pows (Nat.clog 2 n) (ec p1.e) oc zc ⟨p1.k, p1.e + 1⟩).1 + i) =
        feAt sig (8 * C.U + 40) ^ i := fun i hi => by
    rw [e3 i (le_trans hi.le (Nat.le_pow_clog (by norm_num) _)), Cell.val_E, esb']
  have hp3 : 1 ≤ ((⟨p1.k, p1.e + 1⟩ : Ptr).adv
      (pows (Nat.clog 2 n) (ec p1.e) oc zc ⟨p1.k, p1.e + 1⟩).2).e :=
    le_trans (by show 1 ≤ p1.e + 1; (clear * - hp1; omega)) (adv_e_le _ _)
  generalize (pows (Nat.clog 2 n) (ec p1.e) oc zc ⟨p1.k, p1.e + 1⟩).1 = sp at h hsp
  generalize (⟨p1.k, p1.e + 1⟩ : Ptr).adv
    (pows (Nat.clog 2 n) (ec p1.e) oc zc ⟨p1.k, p1.e + 1⟩).2 = p3 at h hp3
  -- the target
  obtain ⟨h4, h⟩ := okb h
  have et := htg w hw sp _ hsp p3 h4.1
  have hp4 := le_trans hp3 (adv_e_le p3 (tg w sp p3).2)
  generalize (tg w sp p3).1 = tgt at h et
  generalize p3.adv (tg w sp p3).2 = p4 at h hp4
  -- the basis point and the basis
  obtain ⟨h5, h⟩ := okb h
  obtain ⟨exb, ecp⟩ := copiesG_spec (fun x hx => by
    rcases List.mem_append.mp hx with hx | hx
    · obtain ⟨k, -, rfl⟩ := List.mem_map.mp (List.mem_of_mem_drop hx); rfl
    · obtain ⟨k, -, rfl⟩ := List.mem_map.mp (List.mem_of_mem_take hx); rfl) h5.1
  have hxs := xs_eq (M := M) hlf ecp
  rw [exb] at h
  have hp5 : 1 ≤ (p4.adv (copiesG (((List.range C.nu).map fun k => ec (p.e + k)).drop C.lf ++
      ((List.range C.nu).map fun k => ec (p.e + k)).take C.lf) p4).2).e :=
    le_trans hp4 (adv_e_le _ _)
  generalize p4.adv (copiesG (((List.range C.nu).map fun k => ec (p.e + k)).drop C.lf ++
      ((List.range C.nu).map fun k => ec (p.e + k)).take C.lf) p4).2 = p5 at h hp5
  obtain ⟨h6, h⟩ := okb h
  have eb := hbg w hw sp p4.e _ hsp p5 h6.1
  rw [hxs] at eb
  have hp6 := le_trans hp5 (adv_e_le p5 (bg w sp p4.e p5).2)
  generalize (bg w sp p4.e p5).1 = bas at h eb
  generalize p5.adv (bg w sp p4.e p5).2 = p6 at h hp6
  -- the `K` zero cell
  obtain ⟨h7, h⟩ := okb h
  have ez := lin_spec (τ := .K) (k := 1) (k' := 0) (a := g) (b := g) h7.1
  have hzk : M.k p6.k = 0 := by
    rw [show (lin .K 1 0 g g p6).1 = kc p6.k from rfl, Cell.val_K, hg, ofK_one, ofK_zero, one_mul,
      add_zero, CharTwo.add_self_eq_zero] at ez
    exact ofK_inj (ez.trans ofK_zero.symm)
  have hp7 := le_trans hp6 (adv_e_le p6 (const .K 0 g p6).2)
  rw [show (const .K 0 g p6).1 = kc p6.k from rfl] at h
  generalize p6.adv (const .K 0 g p6).2 = p7 at h hp7
  -- `verifyWhir`'s first polynomial
  obtain ⟨h8, h⟩ := okb h
  have eq0 := rdQ_spec hS (by (clear * - hU; omega)) h8.1
  have hp8 := le_trans hp7 (adv_e_le p7 (rdQ (C.U + 9) tgt p7).2)
  generalize (rdQ (C.U + 9) tgt p7).1 = q at h eq0
  generalize p7.adv (rdQ (C.U + 9) tgt p7).2 = p8 at h hp8
  -- `F`
  simp only [verifyStackedOpening, verifyWhir]
  rw [dm_bind, sampleE_run]
  dsimp only
  rw [dm_bind, srp3_run]
  dsimp only
  refine levels_run C hS p.e zc oc g p6.k bas hz ho hzE hoE hg hgK hzk C.lf _ ?_ C.levels 0 0 (C.U + 15)
    q [] _ p8 hlv hp8 ?_ (by simp) (fun j hj => by rw [Nat.add_zero]; exact ech j hj) hpos hpw
    ⟨by simp, by simp⟩ h _ ?_
  · rw [eb, hs, hn]
  · rw [eq0, et, pos_mk0, hs, hn, show 8 * (C.U + 9) = 8 * C.U + 72 by ring]
  · simp only [pos] at hs ⊢; (clear * - hs; omega)

set_option maxHeartbeats 1000000 in
/-- **One stacked opening replays `F`'s `verifyStackedOpening`.** -/
theorem stack_run (C : SCfg) (cl : List CClaim) (zc oc g : Cell) {sig : ByteArray} {T : Nat}
    (hS : Lvm.Q1.Streamed M sig T) (hok : StackOk C cl T = true) (hz : zc.val M = 0)
    (ho : oc.val M = 1) (hzE : zc.ty = .E) (hoE : oc.ty = .E) (hg : g.val M = 1) (hgK : g.ty = .K)
    (hpos : PosOk C M sig 0 C.levels (C.U + 15)) (hpw : PwOk C M 0 C.levels) {p : Ptr} (hp : 1 ≤ p.e)
    (h : Lvm.QSig.Ok c M (stackGW C cl zc oc g) p) (s : RS) (hs : pos s = 8 * C.U) :
    (verifyStackedOpening C.levels C.nu (cl.map fun cc => (cc.val M).2.onStack) false C.g C.ood sig s).2.ok = s.ok ∧
    pos (verifyStackedOpening C.levels C.nu (cl.map fun cc => (cc.val M).2.onStack) false C.g C.ood sig s).2 =
      8 * stackEndL C.g C.ood C.levels (C.U + 15) ∧
    (verifyStackedOpening C.levels C.nu (cl.map fun cc => (cc.val M).2.onStack) false C.g C.ood sig s).2.msg = 0 := by
  simp only [StackOk, Bool.and_eq_true] at hok
  unfold stackGW at h
  have e1 : (cl.map fun cc => (cc.val M).2.onStack).map (·.2) = cl.map fun cc => (cc.val M).2.value := by
    rw [List.map_map]; rfl
  have hn : (cl.map fun cc => (cc.val M).2.onStack).length = cl.length := List.length_map _
  have htg : ∀ (w : Unit), True → ∀ (sp : Nat) (σ : FE), (∀ i < cl.length, M.e (sp + i) = σ ^ i) →
      Hs c M (targetG cl sp zc) (fun t => t.val M =
        Lvm.dot (powers σ cl.length) ((cl.map fun cc => (cc.val M).2.onStack).map (·.2))) :=
    fun _ _ sp σ hsp p' h' => by rw [e1]; exact targetG_spec h' hz σ hsp
  have hbg : ∀ (w : Unit), True → ∀ (sp xb : Nat) (σ : FE), (∀ i < cl.length, M.e (sp + i) = σ ^ i) →
      Hs c M (basisG C.nu cl sp xb zc oc g) (fun b => b.val M = Lvm.dot (powers σ cl.length)
        ((cl.map fun cc => (cc.val M).2.onStack).map fun sc => sc.1 ((List.range C.nu).map fun i => M.e (xb + i)))) :=
    fun _ _ sp xb σ hsp p' h' => by rw [List.map_map]; exact basisG_spec h' hok.2 hz ho hzE hoE hgK σ hsp
  have k1 := stackG_run (β := Unit) (c := c) (M := M) C cl.length (pure ()) (fun _ sp => targetG cl sp zc)
    (fun _ sp xb => basisG C.nu cl sp xb zc oc g) (fun _ => True) (cl.map fun cc => (cc.val M).2.onStack) hn
    (fun _ _ => trivial) htg hbg zc oc g hS
  have k2 := k1 hok.1 hz ho hzE hoE hg hgK hpos hpw hp h s hs
  exact k2

/-! ## `C_main`'s opening in both shapes (roll 7, SH2-Z; CR-Q) -/

section Z

open Lvm.QShape Lvm.Shape

theorem fa2_mem {α β : Type} {R : α → β → Prop} : ∀ {l₁ : List α} {l₂ : List β}, List.Forall₂ R l₁ l₂ →
    ∀ b ∈ l₂, ∃ a ∈ l₁, R a b
  | [], [], _, _, h => absurd h (by simp)
  | a :: l₁, b' :: l₂, .cons hab hr, b, hb => by
    rcases List.mem_cons.mp hb with rfl | hb
    · exact ⟨a, List.mem_cons_self, hab⟩
    · obtain ⟨a', ha', hr'⟩ := fa2_mem hr b hb
      exact ⟨a', List.mem_cons_of_mem _ ha', hr'⟩

theorem rotZ_getD (X : List FE) (hX : X.length = CMain.nu20) {i : Nat} (hi : i < CMain.nu20) :
    (rotZ X).getD i 0 = X.getD ((i + 1) % CMain.nu20) 0 := by
  have hnu : CMain.nu20 = 23 := rfl
  cases X with
  | nil => simp at hX
  | cons x0 xt =>
    have hxt : xt.length = CMain.nu20 - 1 := by simp only [List.length_cons] at hX; (clear * - hnu hX; omega)
    simp only [rotZ, List.tail_cons, List.headD_cons]
    by_cases h : i < CMain.nu20 - 1
    · rw [getD_append_lo (by (clear * - hxt h; omega)), Nat.mod_eq_of_lt (by (clear * - hi hnu h; omega) : i + 1 < CMain.nu20)]; rfl
    · have e : i = xt.length + 0 := by (clear * - hi hnu hxt h; omega)
      rw [e, getD_append_hi, show xt.length + 0 + 1 = CMain.nu20 by omega, Nat.mod_self]; rfl

/-- The muxed values of the claims are the stack claims' values on the shape's stack. -/
theorem tgt_list (b : Bool) {s : Cell} (hsv : s.val M = if b then 1 else 0) :
    ∀ (cl : List CClaim) (zs : List (CClaim × Bool)), List.Forall₂ (ZRel M s) cl zs →
      (zs.map (·.1)).map (fun cc => (cc.val M).2.value) =
        (onStackZsF b (cl.map fun cc => ((cc.val M).2, tailC M cc))).map (·.2)
  | [], [], _ => by cases b <;> simp [onStackZsF]
  | cc :: cl, r :: zs, .cons hr hrs => by
    have ih := tgt_list b hsv cl zs hrs
    cases b
    · simp only [onStackZsF, Bool.false_eq_true, if_false] at ih ⊢
      simp only [List.map_cons, List.map_map] at ih ⊢
      refine congrArg₂ List.cons ?_ ih
      rw [cval_value, hr.value, hsv]
      simp only [Bool.false_eq_true, if_false, zero_mul, add_zero, Function.comp_apply]
      show _ = (cc.val M).2.value
      rw [cval_value]
    · simp only [onStackZsF, if_true] at ih ⊢
      simp only [List.map_cons, List.map_map] at ih ⊢
      refine congrArg₂ List.cons ?_ ih
      rw [cval_value, hr.value, hsv]
      simp only [if_true, one_mul, Function.comp_apply, onStackZB]
      rw [cval_value, CharTwo.sub_eq_add]

theorem bas_list (b : Bool) {s : Cell} (hsv : s.val M = if b then 1 else 0) (X : List FE)
    (hX : X.length = CMain.nu20) :
    ∀ (cl : List CClaim) (zs : List (CClaim × Bool)), List.Forall₂ (ZRel M s) cl zs →
      zs.map (if b then wSml M (rotZ X) else wBig M X) =
        (onStackZsF b (cl.map fun cc => ((cc.val M).2, tailC M cc))).map fun sc => sc.1 X
  | [], [], _ => by cases b <;> simp [onStackZsF]
  | cc :: cl, r :: zs, .cons hr hrs => by
    have ih := bas_list b hsv X hX cl zs hrs
    cases b
    · simp only [onStackZsF, Bool.false_eq_true, if_false] at ih ⊢
      simp only [List.map_cons, List.map_map] at ih ⊢
      refine congrArg₂ List.cons ?_ ih
      simp only [Function.comp_apply, wBig]
      by_cases h2 : r.2 = true
      · rw [hr.reg h2]
      · exact hr.big (by simpa using h2) (by rw [hsv]; rfl) X hX
    · simp only [onStackZsF, if_true] at ih ⊢
      simp only [List.map_cons, List.map_map] at ih ⊢
      refine congrArg₂ List.cons ?_ ih
      simp only [Function.comp_apply, wSml]
      have hsm := hr.small (by rw [hsv]; rfl) X hX
      by_cases h2 : r.2 = true
      · rw [if_pos h2] at hsm ⊢; rw [hr.reg h2]; exact hsm
      · rw [if_neg h2] at hsm ⊢; exact hsm

set_option maxHeartbeats 1000000 in
/-- **`C_main`'s opening in both shapes replays `F`'s** on `V_S`'s stack claims `onStackZsF b` of the claims
with their tails (`b`: the child is small; `σ'` holds `1` iff `b`). -/
theorem stackZ_run (C : SCfg) (cl : List CClaim) (mb : List Cell) (zc oc g : Cell) (b : Bool)
    (hσ : (1 + (mb.getD 18 default).val M) * (1 + (mb.getD 19 default).val M) = if b then 1 else 0)
    (hν : C.nu = CMain.nu20) (hwf : ClaimsWF CMain.nu20 cl = true) (hzw : ∀ cc ∈ cl, ZWF zc cc = true)
    {sig : ByteArray} {T : Nat} (hS : Lvm.Q1.Streamed M sig T) (hok : LayOk C T = true) (hz : zc.val M = 0)
    (ho : oc.val M = 1) (hzE : zc.ty = .E) (hoE : oc.ty = .E) (hg : g.val M = 1) (hgK : g.ty = .K)
    (hpos : PosOk C M sig 0 C.levels (C.U + 15)) (hpw : PwOk C M 0 C.levels) {p : Ptr} (hp : 1 ≤ p.e)
    (h : Lvm.QSig.Ok c M (stackGZ C cl mb zc oc g) p) (s : RS) (hs : pos s = 8 * C.U) :
    let scs := onStackZsF b (cl.map fun cc => ((cc.val M).2, tailC M cc))
    (verifyStackedOpening C.levels C.nu scs false C.g C.ood sig s).2.ok = s.ok ∧
    pos (verifyStackedOpening C.levels C.nu scs false C.g C.ood sig s).2 =
      8 * stackEndL C.g C.ood C.levels (C.U + 15) ∧
    (verifyStackedOpening C.levels C.nu scs false C.g C.ood sig s).2.msg = 0 := by
  intro scs
  have hlen : scs.length = cl.length := by cases b <;> simp [scs, onStackZsF]
  have hwf1 : ∀ cc ∈ cl, WF1 CMain.nu20 cc = true := by simpa [ClaimsWF, List.all_eq_true] using hwf
  refine stackG_run C cl.length _ _ _
    (fun w => (w.1.val M = if b then 1 else 0) ∧ List.Forall₂ (ZRel M w.1) cl w.2) scs hlen ?_ ?_ ?_
    zc oc g hS hok hz ho hzE hoE hg hgK hpos hpw hp h s hs
  · exact hs_bind (sigmaG_spec hz) fun σ hσv =>
      hs_bind (zClaimsG_spec hz ho cl hzw) fun zs hzs => hs_pure ⟨by rw [hσv, hσ], hzs⟩
  · intro w ⟨hsv, hrel⟩ sp σ hsp p' h'
    have hl : (w.2.map (·.1)).length = cl.length := by simp [hrel.length_eq.symm]
    rw [targetG_spec h' hz σ (fun i hi => hsp i (by rw [← hl]; exact hi)), hl, tgt_list b hsv cl w.2 hrel]
  · intro w ⟨hsv, hrel⟩ sp xb σ hsp
    have hl : w.2.length = cl.length := hrel.length_eq.symm
    have hX : ((List.range C.nu).map fun i => M.e (xb + i)).length = CMain.nu20 := by simp [hν]
    refine hs_bind (muxPtG_spec w.1 xb (List.range CMain.nu20)) fun ms ⟨hml, hmE, hmv⟩ => ?_
    have hcp : Hs c M (copiesG ms) (fun xs => ∀ i < CMain.nu20, M.e (xs + i) = (ms.getD i default).val M) :=
      fun p' h' => by
        obtain ⟨e1, e2⟩ := copiesG_spec hmE h'
        rw [e1]; exact fun i hi => e2 i (by rw [hml]; simpa using hi)
    have hw : ∀ e ∈ w.2, WF1 CMain.nu20 e.1 = true ∧ (e.2 = true → RegC e.1) := by
      intro e he
      obtain ⟨cc, hcc, hr⟩ := fa2_mem hrel e he
      refine ⟨hr.wf (hwf1 cc hcc), fun h2 => ?_⟩
      rw [hr.reg h2]; exact hr.regC h2
    refine hs_bind hcp fun xs hxs =>
      hs_mono (basisZ_spec hz ho hzE hw σ (fun j hj => hsp j (by rw [← hl]; exact hj))) fun bv hbv => ?_
    rw [hbv]
    set X := (List.range C.nu).map fun i => M.e (xb + i) with hXd
    have hXl : X.length = CMain.nu20 := hX
    have hXg : ∀ i < CMain.nu20, X.getD i 0 = M.e (xb + i) := fun i hi => by
      simp [hXd, List.getD_eq_getElem?_getD, List.getElem?_map, hν, hi]
    have hxs' : xsOf M CMain.nu20 xs = if b then rotZ X else X := by
      refine list_ext_getD _ _ (by cases b <;> simp [xs_length, hXl, rotZ_length X hXl]) fun i hi => ?_
      rw [xs_length] at hi
      have hm := hmv i (by simpa using hi)
      have hrN : (List.range CMain.nu20).getD i 0 = i := by
        simp [List.getD_eq_getElem?_getD, List.getElem?_range hi]
      rw [hrN] at hm
      rw [xs_getD hi, hxs i hi, hm, hsv]
      cases b
      · simp only [Bool.false_eq_true, if_false, mux_zero]; rw [hXg i hi]
      · simp only [if_true, mux_one]; rw [rotZ_getD X hXl hi, hXg _ (Nat.mod_lt _ (by decide))]
    have hsl : (scs.map fun sc => sc.1 X).length = cl.length := by rw [List.length_map, hlen]
    rw [← hsl, dot_powers_bsum, hsv, hxs']
    cases b
    · simp only [Bool.false_eq_true, if_false, mux_zero]
      rw [← bas_list false (by rw [hsv]) X hXl cl w.2 hrel]
      rfl
    · simp only [if_true, mux_one]
      rw [← bas_list true (by rw [hsv]) X hXl cl w.2 hrel]
      rfl

end Z

/-! ## Phases 8–9 -/

theorem on_eq (cs : List CClaim) (com : Com) :
    ((cs.map (CClaim.val M)).filter (·.1 == com)).map (·.2.onStack) =
      (onCom cs com).map fun cc => (cc.val M).2.onStack := by
  rw [List.filter_map, List.map_map]; rfl

theorem claimsT_rec (cs : List CClaim) :
    ((claimsT M cs).filter (·.1 == .crec)).map (·.2.1.onStack) = (onCom cs .crec).map fun cc => (cc.val M).2.onStack := by
  rw [claimsT, onCom, List.filter_map, List.map_map]; rfl

theorem claimsT_main (cs : List CClaim) :
    ((claimsT M cs).filter (·.1 == .main)).map (·.2) =
      (onCom cs .main).map fun cc => ((cc.val M).2, Lvm.QShape.tailC M cc) := by
  rw [claimsT, onCom, List.filter_map, List.map_map]; rfl

/-- The child's shape cell: `σ' = 1` iff `n' ≤ 2^18` (its bits `m = n' − 1`, `1 ≤ n' ≤ 2^20`). -/
theorem sigma_val (mb : List Cell) (n : Nat) (hmb : vs M mb = selectorPoint (n - 1) 20) (hn1 : 1 ≤ n)
    (hnN : n ≤ 2 ^ 20) :
    (1 + (mb.getD 18 default).val M) * (1 + (mb.getD 19 default).val M) =
      if decide (n ≤ 2 ^ 18) then 1 else 0 := by
  have hl : mb.length = 20 := by simpa [vs, selectorPoint] using congrArg List.length hmb
  have g : ∀ i < 20, (mb.getD i default).val M = eOfNat (((n - 1) >>> i) % 2) := fun i hi => by
    rw [Lvm.QShape.vs_getD' mb i (by (clear * - hl hi; omega)), hmb, Lvm.QShape.selectorPoint_getD' hi]
  rw [g 18 (by norm_num), g 19 (by norm_num), Nat.shiftRight_eq_div_pow, Nat.shiftRight_eq_div_pow]
  have h18 : (n - 1) / 2 ^ 18 % 2 < 2 := Nat.mod_lt _ (by norm_num)
  have h19 : (n - 1) / 2 ^ 19 % 2 < 2 := Nat.mod_lt _ (by norm_num)
  by_cases hs : n ≤ 2 ^ 18
  · rw [show (n - 1) / 2 ^ 18 % 2 = 0 by (clear * - hn1 hnN h18 hs; omega), show (n - 1) / 2 ^ 19 % 2 = 0 by (clear * - hn1 hnN h19 hs; omega)]
    have hs' : n ≤ 262144 := hs
    simp [hs', eOfNat_zero]
  · rw [if_neg (by simpa using hs)]
    rcases Nat.lt_or_ge ((n - 1) / 2 ^ 18 % 2) 1 with h | h
    · rw [show (n - 1) / 2 ^ 18 % 2 = 0 by (clear * - h18 h; omega), show (n - 1) / 2 ^ 19 % 2 = 1 by (clear * - hn1 hnN h18 h19 hs h; omega)]
      simp [eOfNat_zero, eOfNat_one, CharTwo.add_self_eq_zero]
    · rw [show (n - 1) / 2 ^ 18 % 2 = 1 by (clear * - h18 h; omega)]
      simp [eOfNat_one, CharTwo.add_self_eq_zero]

-- (R11-IS, M′: `openPhZ_run` is removed. It related M′'s `openG`, which has no `C_rec` opening, to the dead bus
-- path's `openPhZ`, which still opens `C_rec`; no consumer.)

/-! ## `F`'s positions as bit fields of the answers -/

theorem paF_getD (sig : ByteArray) (h : Nat) : ∀ (n P rem j : Nat), j < min (positionsPerAnswer * n) rem →
    (paF sig h P n rem).getD j 0 = (eToNat (feAt sig (P + 72 * (j / 8) + 40)) >>> ((j % 8) * h)) % 2 ^ h
  | 0, _, _, j, hj => by simp [positionsPerAnswer] at hj
  | n + 1, P, rem, j, hj => by
    rw [paF]
    simp only [positionsPerAnswer] at hj ⊢
    by_cases hj8 : j < min 8 rem
    · rw [List.getD_eq_getElem?_getD, List.getElem?_append_left (by simpa using hj8),
        List.getElem?_map, List.getElem?_range hj8]
      simp only [Option.map_some, Option.getD_some]
      have e1 : j / 8 = 0 := by (clear * - hj8; omega)
      have e2 : j % 8 = j := by (clear * - e1; omega)
      rw [e1, e2, Nat.mul_zero, Nat.add_zero]
    · have h8 : min 8 rem = 8 := by omega
      have e := paF_getD sig h n (P + 72) (rem - 8) (j - 8) (by simp only [positionsPerAnswer]; omega)
      have hl : ((List.range (min 8 rem)).map
          (fun j => (eToNat (feAt sig (P + 40)) >>> (j * h)) % 2 ^ h)).length = 8 := by simp [h8]
      rw [List.getD_eq_getElem?_getD, List.getElem?_append_right (by rw [hl]; (clear * - hj8 h8; omega)), hl,
        ← List.getD_eq_getElem?_getD, h8, e]
      have e1 : (j - 8) / 8 = j / 8 - 1 := by (clear * - hj8 h8; omega)
      have e2 : (j - 8) % 8 = j % 8 := by (clear * - hj8 h8 e1; omega)
      have e3 : P + 72 + 72 * (j / 8 - 1) = P + 72 * (j / 8) := by
        have : 1 ≤ j / 8 := by (clear * - hj8 h8 e1 e2; omega)
        rw [Nat.mul_sub, Nat.mul_one]; (clear * - this; omega)
      rw [e1, e2, e3]

/-- **`F`'s `j`-th position** of level `L` at position `P`: bits `(j mod 8)·height …` of the
`⌊j/8⌋`-th positions answer (lanes `0–2` as one number, `eToNat`). -/
theorem qsAt_getD (sig : ByteArray) (P : Nat) (L : Level) (j : Nat) (hj : j < L.t) :
    (qsAt sig P L).getD j 0 =
      (eToNat (feAt sig (P + 72 * (j / 8) + 40)) >>> ((j % 8) * L.height)) % 2 ^ L.height := by
  have e := (positionsAux_run L.height ((L.t + positionsPerAnswer - 1) / positionsPerAnswer) L.t sig
    ⟨P, 0, true⟩).1
  show (positionsAux L.height ((L.t + positionsPerAnswer - 1) / positionsPerAnswer) L.t sig
    ⟨P, 0, true⟩).1.getD j 0 = _
  rw [e, pos_mk0]
  exact paF_getD sig L.height _ P L.t j (by simp only [positionsPerAnswer]; (clear * - hj; omega))

end Lvm.Har
