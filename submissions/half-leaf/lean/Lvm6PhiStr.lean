-- New for lvm6 (WP STR, PHI-decision v2 A4): the strided-read kind of `Φ_Q`'s class evaluator. A loop reads
-- stream words at a stride that is not a power of two (Q_link's node checks: 13 per path level, `posStride6` per
-- position); entry by entry each read costs about 3 products. A run sums every iteration of such reads with
-- season 1's carry automaton (`LvmWiringK.runAuto_eq`, at `FE2` through `runAuto2`).
import LvmE2VPhiTEq
import LvmE2VWireAlg

/-!
# Strided runs of `Φ_Q`

* **`SRun`**: atoms `(c, o, x₀)` grouped by their initial word `s`; iteration `j < 2^n` of an atom is the entry
  `(c, o, x₀ + 2^p·j, s + R·j)` (`SRun.ents`). The bits `[p, p + n)` of every `x₀` are zero (`SRun.okB`).
* **`SRun.valW`**: the initial states `(s, Σ_atoms c·eq(κ, o)·eq(m_lo, x₀)·eq(m_hi, x₀))`, `n` automaton steps
  (`runAuto2`: step `k` reads slot coordinate `p + k` and word coordinate `k`, stride `R`), then
  `Σ_finals v·eq(b[n…], z)`.
* **`SRun.valW_eq`**: with the weights the `eq` functions, the run's value is the sum of its entries' values
  `c·eq(κ, o)·eq(m, x)·eq(b, y)` (PHIV's `qv`).
-/

set_option autoImplicit false

namespace Lvm6.V

open Lvm Lvm.E2V Lvm.Typed.K Lvm.Typed.KT

/-- **A strided run**: `n` iteration bits at slot bit `p`, word stride `R`; per initial word `s` (strictly
increasing) its atoms `(c, o, x₀)`. -/
structure SRun where
  p : ℕ
  n : ℕ
  R : ℕ
  grp : Array (ℕ × Array (FE2 × ℕ × ℕ))
  deriving Inhabited

/-- **The run's entries** `(c, o, x, y)`. -/
def SRun.ents (r : SRun) : List (FE2 × ℕ × ℕ × ℕ) :=
  r.grp.toList.flatMap fun g => g.2.toList.flatMap fun a =>
    (List.range (2 ^ r.n)).map fun j => (a.1, a.2.1, a.2.2 + 2 ^ r.p * j, g.1 + r.R * j)

/-- **The run's check**: increasing initial words, free iteration bits, the bits inside the point. -/
def SRun.okB (r : SRun) : Bool :=
  decide (r.p + r.n ≤ 20) && decide (r.n ≤ 21) &&
    decide ((r.grp.toList.map (·.1)).Pairwise (· < ·)) &&
    r.grp.toList.all fun g => g.2.toList.all fun a => a.2.2 / 2 ^ r.p % 2 ^ r.n == 0

/-- The automaton's slot coordinates `p, …, p + n − 1`. -/
def SRun.xs (r : SRun) : Array ℕ := (Array.range r.n).map (r.p + ·)

/-- The initial states: per group its word and its atoms' summed weight. -/
def SRun.init (r : SRun) (fa fl fh : ℕ → FE2) : Array (ℕ × FE2) :=
  r.grp.map fun g => (g.1, g.2.foldl (fun s a => s + a.1 * (fa a.2.1 *
    (fl (a.2.2 % 2 ^ r.p) * fh (a.2.2 / 2 ^ (r.p + r.n))))) 0)

/-- **The run's value** with its weights: `fa` the matrix's, `fl`/`fh` the slot bits below `p` and from
`p + n`, `fy` the word bits from `n`; `m`, `b` the slot and word coordinates. -/
def SRun.valW (r : SRun) (fa fl fh fy : ℕ → FE2) (m b : List FE2) : FE2 :=
  (runAuto2 ⟨#[], m.toArray, b.toArray⟩ r.xs r.R (r.init fa fl fh)).foldl (fun s cv => s + cv.2 * fy cv.1) 0

/-- **The run's value** at the point's parts (`eq` evaluated directly). -/
def SRun.val (r : SRun) (fa : ℕ → FE2) (m b : List FE2) : FE2 :=
  r.valW fa (eqAtF (m.take r.p)) (eqAtF (m.drop (r.p + r.n))) (eqAtF (b.drop r.n)) m b

/-! ## Correctness -/

theorem foldl_sumF {α : Type} (f : α → FE2) : ∀ (l : List α) (s : FE2),
    l.foldl (fun s c => s + f c) s = s + (l.map f).sum
  | [], s => by simp
  | c :: l, s => by rw [List.foldl_cons, foldl_sumF f l, List.map_cons, List.sum_cons, add_assoc]

theorem sum_map_flatMapF {α β : Type} (l : List α) (f : α → List β) (g : β → FE2) :
    ((l.flatMap f).map g).sum = (l.map fun a => ((f a).map g).sum).sum := by
  induction l with
  | nil => rfl
  | cons a l ih => rw [List.flatMap_cons, List.map_append, List.sum_append, ih, List.map_cons, List.sum_cons]

theorem eqWG_eqAtF : ∀ (l : List FE2) (x : ℕ), eqWG l x = eqAtF l x
  | [], _ => rfl
  | r :: rs, x => by
    simp only [eqWG, eqAtF_succ, eqWG_eqAtF rs, kt_sub2]

theorem xs_map (r : SRun) (m : List FE2) (h : r.p + r.n ≤ m.length) :
    r.xs.toList.map (fun i => m.toArray.getD i 0) = (m.drop r.p).take r.n := by
  apply List.ext_getElem (by simp [SRun.xs]; omega)
  intro k h1 h2
  simp only [SRun.xs, Array.toList_map, Array.toList_range, List.length_map, List.length_range] at h1
  simp only [SRun.xs, Array.toList_map, Array.toList_range, List.getElem_map, List.getElem_range,
    List.getElem_take, List.getElem_drop, Array.getD_eq_getD_getElem?, List.getElem?_toArray]
  rw [List.getElem?_eq_getElem (by omega)]
  rfl

theorem sub_take (b : List FE2) (n : ℕ) (h : n ≤ b.length) : sub b.toArray 0 n = b.take n := by
  apply List.ext_getElem (by simp [sub]; omega)
  intro k h1 h2
  simp only [sub, List.length_map, List.length_range] at h1
  simp only [sub, List.getElem_map, List.getElem_range, Nat.zero_add, List.getElem_take,
    Array.getD_eq_getD_getElem?, List.getElem?_toArray]
  rw [List.getElem?_eq_getElem (by omega)]
  rfl

/-- The word point split at bit `n`. -/
theorem eq_ysplit (b : List FE2) (n y : ℕ) (h : n ≤ b.length) :
    eqAtF (b.take n) (y % 2 ^ n) * eqAtF (b.drop n) (y / 2 ^ n) = eqAtF b y := by
  have hl : (b.take n).length = n := by simp [h]
  conv_rhs => rw [← List.take_append_drop n b]
  rw [eqAtF_append, hl, eqAtF_mod (b.take n) y, hl]

/-- The slot point split at bits `p` and `p + n`, at an iteration `j` on free bits. -/
theorem eq_xsplit (m : List FE2) (p n x₀ j : ℕ) (h : p + n ≤ m.length) (hx : x₀ / 2 ^ p % 2 ^ n = 0)
    (hj : j < 2 ^ n) :
    eqAtF (m.take p) (x₀ % 2 ^ p) * (eqAtF ((m.drop p).take n) j * eqAtF (m.drop (p + n)) (x₀ / 2 ^ (p + n))) =
      eqAtF m (x₀ + 2 ^ p * j) := by
  have hp : (m.take p).length = p := by simp; omega
  have hn : ((m.drop p).take n).length = n := by simp; omega
  have hd : (m.drop p).drop n = m.drop (p + n) := by rw [List.drop_drop]
  have h2 : (x₀ + 2 ^ p * j) % 2 ^ p = x₀ % 2 ^ p := by rw [Nat.add_mul_mod_self_left]
  have h3 : (x₀ + 2 ^ p * j) / 2 ^ p = x₀ / 2 ^ p + j := by
    rw [Nat.add_mul_div_left _ _ (by positivity)]
  obtain ⟨q, hq⟩ : 2 ^ n ∣ x₀ / 2 ^ p := Nat.dvd_of_mod_eq_zero hx
  have h4 : (x₀ / 2 ^ p + j) % 2 ^ n = j := by
    rw [hq, Nat.mul_comm (2 ^ n) q, Nat.mul_add_mod_of_lt hj]
  have h5 : (x₀ / 2 ^ p + j) / 2 ^ n = x₀ / 2 ^ (p + n) := by
    rw [pow_add, ← Nat.div_div_eq_div_mul, hq, Nat.mul_div_cancel_left q (by positivity),
      Nat.mul_add_div (by positivity), Nat.div_eq_of_lt hj, Nat.add_zero]
  conv_rhs => rw [← List.take_append_drop p m, eqAtF_append, hp, eqAtF_mod (m.take p), hp, h2, h3,
    ← List.take_append_drop n (m.drop p), eqAtF_append, hn, eqAtF_mod ((m.drop p).take n), hn, h4, h5, hd]

section
variable (r : SRun) (fa : ℕ → FE2) (m b : List FE2)

/-- **A run is the sum of its entries.** -/
theorem SRun.valW_eq (hok : r.okB = true) (hm : m.length = 20) (hb : b.length = 21) :
    r.valW fa (eqAtF (m.take r.p)) (eqAtF (m.drop (r.p + r.n))) (eqAtF (b.drop r.n)) m b =
      (r.ents.map fun e => e.1 * (fa e.2.1 * (eqAtF m e.2.2.1 * eqAtF b e.2.2.2))).sum := by
  simp only [SRun.okB, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true, beq_iff_eq] at hok
  obtain ⟨⟨⟨hpn, hn⟩, hsrt⟩, hfree⟩ := hok
  have hs : (r.init fa (eqAtF (m.take r.p)) (eqAtF (m.drop (r.p + r.n)))).toList.Pairwise
      fun a b => a.1 < b.1 := by
    simpa [SRun.init, List.pairwise_map] using hsrt
  have hxs : r.xs.size = r.n := by simp [SRun.xs]
  have hrx : (r.xs.toList.map fun i => (⟨#[], m.toArray, b.toArray⟩ : PtG FE2).rx.getD i 0) =
      (m.drop r.p).take r.n := xs_map r m (by omega)
  have hry : sub (⟨#[], m.toArray, b.toArray⟩ : PtG FE2).ry 0 r.xs.size = b.take r.n := by
    rw [hxs]; exact sub_take b r.n (by omega)
  unfold SRun.valW
  rw [← Array.foldl_toList, foldl_sumF, zero_add, runAuto2_eqG, runAuto_eq _ _ _ _ hs, hrx, hry, hxs]
  unfold SRun.ents SRun.init
  rw [Array.toList_map, List.map_map, sum_map_flatMapF]
  refine congrArg List.sum (List.map_congr_left fun g hg => ?_)
  simp only [Function.comp_apply]
  rw [← Array.foldl_toList, foldl_sumF, zero_add, ← List.sum_map_mul_right, sum_map_flatMapF]
  refine congrArg List.sum (List.map_congr_left fun a ha => ?_)
  rw [← List.sum_map_mul_left, List.map_map]
  refine congrArg List.sum (List.map_congr_left fun j hj => ?_)
  have hj' : j < 2 ^ r.n := List.mem_range.mp hj
  simp only [Function.comp_apply, eqWG_eqAtF]
  rw [← eq_xsplit m r.p r.n a.2.2 j (by omega) (hfree g hg a ha) hj', ← eq_ysplit b r.n (g.1 + r.R * j) (by omega)]
  ring

end

end Lvm6.V
