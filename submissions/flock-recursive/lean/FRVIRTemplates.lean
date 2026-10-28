-- New for `flock-recursive` (BLUEPRINT A.11, stage S-E3; track L-circ).
import FRVIRCompile
import FRVerifierImplOps

/-!
# The replay templates of the structured ops (A.11)

BLUEPRINT A.11: every structured op of the replayed child verifier is constrained by a template of
rows in M. Each template here **mirrors the op's implementation** in `implC`
(`FRVerifierImplOps`' `…I`, or `FRVIR`'s own definition), gate for gate, so that its correctness is
an identity between the gate equations and that implementation; the implementation is the
specification by S-F2's `…_meets`.

Per template `X`: `tplX` (gates and output forms, inputs `inp i` the operands' `F` components in
order) and **`tplX_ok`**: the gate equations (`Eqns`, which the rows give by
`Tpl.eqns_of_rows`), `one = 1` and the inputs' values give the outputs' values, `encV` of the op's
result. With `inst_eqns` this is A.11's `tplX_sound`: an instance's rows hold ⇒ its output cells
hold the op's value on its input cells (`FRVIRTplExt.tplExt_ok`).

The combinators (`mulsG`, `prodG`, `scanG`, `sqG`, `mulKG`, `eqTblG`, `lagG`) carry the proofs.
-/

namespace FR
namespace Tpl
open Circ

variable {e : Env}

/-! ## Combinators -/

theorem ev_cons (t : Wire × F) (l : LinT) : LinT.ev e (t :: l) = t.2 * t.1.ev e + l.ev e := by
  simp [LinT.ev]

/-- `n` products `A v · B v`, locals `k + v`. -/
def mulsG (n : ℕ) (A B : ℕ → LinT) : List Gate := (List.range n).map fun v => .mul (A v) (B v)

theorem mulsG_nlocs (n : ℕ) (A B : ℕ → LinT) : nlocs (mulsG n A B) = n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [mulsG, nlocs, List.range_succ, List.map_append, List.sum_append] at ih ⊢
    rw [ih]; rfl

theorem mulsG_eqns {n : ℕ} {A B : ℕ → LinT} {k : ℕ} (h : Eqns e (mulsG n A B) k) :
    ∀ v < n, e.loc (k + v) = (A v).ev e * (B v).ev e := by
  induction n with
  | zero => intro v hv; omega
  | succ n ih =>
    simp only [mulsG, List.range_succ, List.map_append, List.map_cons, List.map_nil] at h
    rw [Eqns.append] at h
    intro v hv
    rcases Nat.lt_succ_iff_lt_or_eq.1 hv with hv | rfl
    · exact ih h.1 v hv
    · have := (Eqns.cons.1 h.2).1
      have e1 := mulsG_nlocs v A B
      simp only [mulsG] at e1
      rwa [Gate.Eqn, e1] at this

/-- `a · Π fs`, one gate per factor, locals from `k`. -/
def prodG (a : LinT) : List LinT → ℕ → List Gate × LinT
  | [], _ => ([], a)
  | f :: fs, k => let r := prodG (L k) fs (k + 1); (.mul a f :: r.1, r.2)

theorem prodG_nlocs (a : LinT) (fs : List LinT) (k : ℕ) : nlocs (prodG a fs k).1 = fs.length := by
  induction fs generalizing a k with
  | nil => rfl
  | cons f fs ih =>
    have := ih (L k) (k + 1)
    simp only [prodG, nlocs, List.map_cons, List.sum_cons, Gate.nloc, List.length_cons] at this ⊢
    omega

theorem prodG_ev (a : LinT) (fs : List LinT) (k : ℕ) (h : Eqns e (prodG a fs k).1 k) :
    (prodG a fs k).2.ev e = a.ev e * (fs.map (LinT.ev e)).prod := by
  induction fs generalizing a k with
  | nil => simp [prodG]
  | cons f fs ih =>
    simp only [prodG, Eqns.cons, Gate.nloc, Gate.Eqn] at h ⊢
    rw [ih _ _ h.2, ev_L, h.1]; simp [mul_assoc]

/-- The running products `a, a·f₀, a·f₀·f₁, …` (the same gates as `prodG`). -/
def scanG (a : LinT) : List LinT → ℕ → List Gate × List LinT
  | [], _ => ([], [a])
  | f :: fs, k => let r := scanG (L k) fs (k + 1); (.mul a f :: r.1, a :: r.2)

theorem scanG_nlocs (a : LinT) (fs : List LinT) (k : ℕ) : nlocs (scanG a fs k).1 = fs.length := by
  induction fs generalizing a k with
  | nil => rfl
  | cons f fs ih =>
    have := ih (L k) (k + 1)
    simp only [scanG, nlocs, List.map_cons, List.sum_cons, Gate.nloc, List.length_cons] at this ⊢
    omega

theorem scanG_ev (a : LinT) (fs : List LinT) (k : ℕ) (h : Eqns e (scanG a fs k).1 k) :
    (scanG a fs k).2.map (LinT.ev e) = List.scanl (· * ·) (a.ev e) (fs.map (LinT.ev e)) := by
  induction fs generalizing a k with
  | nil => simp [scanG]
  | cons f fs ih =>
    simp only [scanG, Eqns.cons, Gate.nloc, Gate.Eqn] at h ⊢
    rw [List.map_cons, ih _ _ h.2, ev_L, h.1]; simp

theorem scanG_length (a : LinT) (fs : List LinT) (k : ℕ) : (scanG a fs k).2.length = fs.length + 1 := by
  induction fs generalizing a k with
  | nil => rfl
  | cons f fs ih => simp [scanG, ih]

/-- `s` squarings of `x`, locals from `k`. -/
def sqG : ℕ → LinT → ℕ → List Gate × LinT
  | 0, x, _ => ([], x)
  | s + 1, x, k => let r := sqG s (L k) (k + 1); (.mul x x :: r.1, r.2)

theorem sqG_nlocs (s : ℕ) (x : LinT) (k : ℕ) : nlocs (sqG s x k).1 = s := by
  induction s generalizing x k with
  | zero => rfl
  | succ s ih =>
    have := ih (L k) (k + 1)
    simp only [sqG, nlocs, List.map_cons, List.sum_cons, Gate.nloc] at this ⊢; omega

theorem sqG_ev (s : ℕ) (x : LinT) (k : ℕ) (h : Eqns e (sqG s x k).1 k) :
    (sqG s x k).2.ev e = sqIter s (x.ev e) := by
  induction s generalizing x k with
  | zero => rfl
  | succ s ih =>
    simp only [sqG, Eqns.cons, Gate.nloc, Gate.Eqn] at h ⊢
    rw [ih _ _ h.2, ev_L, h.1]; rfl

/-! ## `eqPt` (A.8; `FRVIR.eqPoint`) -/

/-- The `b` coordinate `v` (`0` past `m`). -/
def yIn (n m v : ℕ) : LinT := if v < m then I (n + v) else []

/-- `x·y + (1 − x)(1 − y)` from the product `t = x·y`. -/
def eqFac (x y t : LinT) : LinT := sc 2 t ++ C 1 ++ sc (-1) x ++ sc (-1) y

theorem eqFac_ev (h1 : e.one = 1) (x y t : LinT) (ht : t.ev e = x.ev e * y.ev e) :
    (eqFac x y t).ev e = x.ev e * y.ev e + (1 - x.ev e) * (1 - y.ev e) := by
  simp only [eqFac, ev_append, ev_sc, ev_C, h1, ht]; ring

/-- **`eqPt`** for `a : AF n`, `b : AF m` (inputs `a`, then `b`): the `n` products `a_v b_v`, then
the running product of the factors. -/
def tplEqPt (n m : ℕ) : Tpl :=
  let g := prodG (C 1) ((List.range n).map fun v => eqFac (I v) (yIn n m v) (L v)) n
  ⟨mulsG n I (yIn n m) ++ g.1, [g.2]⟩

/-- The inputs are the concatenated encodings `xs` (`e.inp i = xs[i]`, `0` past the end). -/
def InpIs (e : Env) (xs : List F) : Prop := ∀ i, e.inp i = xs.getD i 0

theorem foldl_mul_range {M : Type*} [CommMonoid M] (n : ℕ) (g : ℕ → M) :
    (List.range n).foldl (fun acc v => acc * g v) 1 = ((List.range n).map g).prod := by
  rw [List.prod_eq_foldl, List.foldl_map]

theorem getD_append_left {xs ys : List F} {i : ℕ} (h : i < xs.length) :
    (xs ++ ys).getD i 0 = xs.getD i 0 := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_append_left h]

theorem getD_append_right (xs ys : List F) (j : ℕ) :
    (xs ++ ys).getD (xs.length + j) 0 = ys.getD j 0 := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_append_right]

theorem arr_getD (a : Array F) (i : ℕ) : a.toList.getD i 0 = a.getD i 0 := by
  simp [List.getD_eq_getElem?_getD, Array.getD_eq_getD_getElem?]

theorem tplEqPt_ok (h1 : e.one = 1) {a b : Array F} (hi : InpIs e (a.toList ++ b.toList))
    (h : Eqns e (tplEqPt a.size b.size).gates 0) :
    (tplEqPt a.size b.size).outs.map (LinT.ev e) = encV (.f (eqPoint a b)) := by
  simp only [tplEqPt, Eqns.append, zero_add, mulsG_nlocs] at h
  have hm := mulsG_eqns h.1
  have hx : ∀ v < a.size, (I v).ev e = a.getD v 0 := fun v hv => by
    rw [ev_I, hi, getD_append_left (by simpa using hv), arr_getD]
  have hy : ∀ v, (yIn a.size b.size v).ev e = b.getD v 0 := fun v => by
    by_cases hv : v < b.size
    · simp only [yIn, hv, if_true]
      rw [ev_I, hi, ← arr_getD, ← getD_append_right a.toList b.toList v, Array.length_toList]
    · simp only [yIn, hv, if_false, ev_nil]
      rw [← arr_getD, List.getD_eq_getElem?_getD, List.getElem?_eq_none (by simp; omega)]; rfl
  have hp : eqPoint a b = ((List.range a.size).map fun v =>
      a.getD v 0 * b.getD v 0 + (1 - a.getD v 0) * (1 - b.getD v 0)).prod := by
    rw [← foldl_mul_range]; rfl
  simp only [tplEqPt, List.map_cons, List.map_nil, encV, List.cons.injEq, and_true]
  rw [prodG_ev _ _ _ h.2, ev_C, h1, one_mul, one_mul, List.map_map, hp]
  refine congrArg List.prod (List.map_congr_left fun v hv => ?_)
  have hv := List.mem_range.1 hv
  have ht := hm v hv
  rw [zero_add] at ht
  simp only [Function.comp_apply]
  rw [eqFac_ev h1 _ _ _ (by rw [ev_L]; exact ht), hx v hv, hy v]

/-! ## `shiftEq` (`FRShift.shiftPair`) -/

/-- `shiftPair` over forms: per coordinate `t = x·y`, `E′ = (x y + (1−x)(1−y))·E`,
`(y − t)·E`, `(x − t)·S` (4 gates); the tail first. -/
def shiftG : List LinT → List LinT → ℕ → List Gate × (LinT × LinT)
  | x :: xs, y :: ys, k =>
    let r := shiftG xs ys k
    let k' := k + nlocs r.1
    (r.1 ++ [.mul x y, .mul (eqFac x y (L k')) r.2.1, .mul (y ++ sc (-1) (L k')) r.2.1,
      .mul (x ++ sc (-1) (L k')) r.2.2], (L (k' + 1), L (k' + 2) ++ L (k' + 3)))
  | _, _, _ => ([], (C 1, []))

theorem shiftG_ev (h1 : e.one = 1) : ∀ (xs ys : List LinT) (k : ℕ), Eqns e (shiftG xs ys k).1 k →
    ((shiftG xs ys k).2.1.ev e, (shiftG xs ys k).2.2.ev e) =
      shiftPair (xs.map (LinT.ev e)) (ys.map (LinT.ev e))
  | x :: xs, y :: ys, k, h => by
    simp only [shiftG, Eqns.append, Eqns.cons, Gate.nloc, Gate.Eqn, Eqns.nil, and_true] at h
    have ih := shiftG_ev h1 xs ys k h.1
    simp only [shiftG, List.map_cons, shiftPair, ← ih]
    obtain ⟨-, h0, h2, h3, h4⟩ := h
    rw [ev_L, ev_append, ev_L, ev_L, h2, h3, h4, eqFac_ev h1 _ _ _ (by rw [ev_L]; exact h0)]
    refine Prod.ext ?_ ?_ <;> simp only [ev_append, ev_sc, ev_L, h0] <;> ring
  | [], _, _, _ => by simp [shiftG, shiftPair, h1]
  | _ :: _, [], _, _ => by simp [shiftG, shiftPair, h1]

/-- **`shiftEq`** for `a : AF n`, `b : AF m`. -/
def tplShiftEq (n m : ℕ) : Tpl :=
  let g := shiftG ((List.range n).map I) ((List.range m).map fun v => I (n + v)) 0
  ⟨g.1, [g.2.2]⟩

theorem map_I_ev {xs ys : List F} (hi : InpIs e (xs ++ ys)) :
    ((List.range xs.length).map I).map (LinT.ev e) = xs ∧
    ((List.range ys.length).map fun v => I (xs.length + v)).map (LinT.ev e) = ys := by
  constructor <;> refine List.ext_getElem (by simp) fun j h₁ h₂ => ?_ <;>
    simp only [List.getElem_map, List.getElem_range, ev_I]
  · rw [hi, getD_append_left h₂, List.getD_eq_getElem _ _ h₂]
  · rw [hi, getD_append_right, List.getD_eq_getElem _ _ h₂]

theorem tplShiftEq_ok (h1 : e.one = 1) {a b : Array F} (hi : InpIs e (a.toList ++ b.toList))
    (h : Eqns e (tplShiftEq a.size b.size).gates 0) :
    (tplShiftEq a.size b.size).outs.map (LinT.ev e) = encV (.f (Impl.shiftEqI a b)) := by
  have hm := map_I_ev hi
  simp only [Array.length_toList] at hm
  have := shiftG_ev h1 _ _ 0 h
  simp only [tplShiftEq, List.map_cons, List.map_nil, encV, Impl.shiftEqI, hm.1, hm.2] at this ⊢
  rw [← this]

/-! ## `phiRS` (`FRRingSwitch.phiApply`) -/

/-- The staged map over forms: per stage `s` squarings and one product. -/
def frobG : List (ℕ × LinT) → LinT → ℕ → List Gate × LinT
  | [], a, _ => ([], a)
  | (s, f) :: st, a, k =>
    let q := sqG s a k
    let r := frobG st (a ++ L (k + s)) (k + s + 1)
    (q.1 ++ [.mul f q.2] ++ r.1, r.2)

theorem frobG_ev : ∀ (st : List (ℕ × LinT)) (a : LinT) (k : ℕ), Eqns e (frobG st a k).1 k →
    (frobG st a k).2.ev e = frobMapC (st.map fun p => (p.1, p.2.ev e)) (a.ev e)
  | [], a, k, _ => rfl
  | (s, f) :: st, a, k, h => by
    simp only [frobG, Eqns.append, Eqns.cons, Gate.nloc, Gate.Eqn, Eqns.nil, sqG_nlocs,
      List.map_cons, frobMapC] at h ⊢
    obtain ⟨⟨hq, hm, -⟩, hr⟩ := h
    have hs : (List.map Gate.nloc (sqG s a k).1).sum = s := sqG_nlocs s a k
    simp only [nlocs, List.map_append, List.map_cons, List.map_nil, List.sum_append, List.sum_cons,
      List.sum_nil, Gate.nloc, hs, add_zero] at hr hm
    rw [frobG_ev st _ _ (by simpa [Nat.add_assoc] using hr), ev_append, ev_L, hm, sqG_ev _ _ _ hq]

/-- **`phiRS`** for `r : AF n`, `a : F` (inputs `r`, then `a`): stage `p` squares `2^(n−1−p)`
times. -/
def tplPhiRS (n : ℕ) : Tpl :=
  let g := frobG ((List.range n).map fun p => (2 ^ (n - 1 - p), I p)) (I n) 0
  ⟨g.1, [g.2]⟩

theorem tplPhiRS_ok {r : Array F} {a : F} (hi : InpIs e (r.toList ++ [a]))
    (h : Eqns e (tplPhiRS r.size).gates 0) :
    (tplPhiRS r.size).outs.map (LinT.ev e) = encV (.f (Impl.phiRSI r a)) := by
  have hm := (map_I_ev hi).1
  simp only [Array.length_toList] at hm
  have ha : (I r.size).ev e = a := by
    rw [ev_I, hi, ← Array.length_toList, ← add_zero r.toList.length, getD_append_right]; rfl
  simp only [tplPhiRS, List.map_cons, List.map_nil, encV, Impl.phiRSI, phiApply, List.cons.injEq,
    and_true]
  rw [frobG_ev _ _ _ h, ha, List.map_map]
  congr 1
  refine List.ext_getElem (by simp [stages]) fun j h₁ h₂ => ?_
  have hj : j < r.size := by simpa using h₁
  have := congrArg (·[j]?) hm
  simp only [List.getElem?_map, List.getElem?_range hj, Option.map_some] at this
  simp only [List.getElem_map, List.getElem_range, Function.comp_apply, stages, List.getElem_mapIdx,
    Array.length_toList, Prod.mk.injEq, true_and]
  exact Option.some.inj (this.trans (List.getElem?_eq_getElem _))

/-! ## `linkW`, `kindFoldWeight` (`implC`: `0`) -/

/-- The constant `0` (no rows). -/
def tplZero : Tpl := ⟨[], [[]]⟩

theorem tplZero_ok : tplZero.outs.map (LinT.ev e) = encV (.f 0) := rfl

end Tpl
end FR
