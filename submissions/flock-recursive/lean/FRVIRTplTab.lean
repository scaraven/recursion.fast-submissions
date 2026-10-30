-- G6: this module also holds the former modules `FRVIRTemplates`, `FRVIRTplDag` (one section each, in import order).
import FRVIRCompile
import FRVerifierImplOps

section G6_FRVIRTemplates

-- New for `flock-recursive` (BLUEPRINT A.11, stage S-E3; track L-circ).

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

/-! ## `kindFoldWeight` (`implC`: `0`) -/

/-- The constant `0` (no rows). -/
def tplZero : Tpl := ⟨[], [[]]⟩

theorem tplZero_ok : tplZero.outs.map (LinT.ev e) = encV (.f 0) := rfl

end Tpl
end FR

end G6_FRVIRTemplates

section G6_FRVIRTplDag

-- New for `flock-recursive` (BLUEPRINT §4.4 "The walk", A.11 `walkAB`, revision 3.15; stage
-- S-E10, track L-circ).

/-!
# The walk as the node's own XOR DAG: the gadget program that emits rows

BLUEPRINT §4.4 (revision 3.15, changes 22 (a)): `walkAB rowW′ colW` is materialised as the BLAKE2s
gadget DAG — **one linear row per XOR** and two product rows per gate. This file is the row-emitting
interpretation of `FRBlake2sGeneric`'s gadget program: the same gadgets, statement for statement,
where a value is a **single-wire form** (`LinT`: an input `rowW′[k]`/`colW[k]`, a local, or `[]`
for zero), `xor` is a **program step** that emits the row `loc = a + b` (`dxor`; free when an
operand is `0`), and the product gate at position `k` emits `p_A = rowW′[k]·a + p_A`,
`p_B = rowW′[k]·b + p_B` (`dmul`: the two walk accumulators as running sums, single cells) and
returns `colW[k]`.

**Layout** (`dgW`): every `G` gadget starts at a fresh block (`Gate.pad`), so the 80 instances
(10 rounds × 8) sit at one stride, and their locals at fixed offsets.

The correctness theorem (`tplWalkAB_ok`, `FRVIRTplWalk`) relates this program to the walk
interpretation (`walkOps`) of the generic program by a relational simulation (`RelT`).
-/

namespace FR
namespace Tpl
open RecursionFast RecursionFast.Blake2s ProductCircuit Blake2sCircuit

/-! ## The builder -/

/-- The DAG builder's state: the next gate position, the gates so far, their locals and rows, the
two accumulators' wires. -/
structure DSt where
  next : ℕ
  gs : Array Gate
  nl : ℕ
  nr : ℕ
  accA : LinT
  accB : LinT

/-- The DAG builder. -/
abbrev DB := StateM DSt

/-- Emit a gate; its first local. -/
def emit (g : Gate) : DB LinT :=
  modifyGet fun s =>
    -- every other field first, the gate array last, so that its push is in place (S-E13)
    let nx := s.next; let nl := s.nl; let nr := s.nr; let a := s.accA; let b := s.accB
    (L nl, ⟨nx, s.gs.push g, nl + g.nloc, nr + (g.rows 0).length, a, b⟩)

/-- Pad the locals and the rows to the next multiples of `2^b` (a fresh block). -/
def padTo (b : ℕ) : DB Unit :=
  modify fun s =>
    let nx := s.next; let nl := s.nl; let nr := s.nr; let a := s.accA; let c := s.accB
    ⟨nx, s.gs.push (.pad (Circ.alignUp nr b - nr) (Circ.alignUp nl b - nl)), Circ.alignUp nl b,
      Circ.alignUp nr b, a, c⟩

/-- **XOR** of two forms: their formal sum (no row; characteristic 2). -/
def dx (a b : LinT) : LinT := a ++ b

/-- **A form as a cell**: a linear row `loc = l` when `l` has two terms or more (an XOR chain's
row); a single wire or `0` is kept as it is. -/
def dcell (l : LinT) : DB LinT := if l.length ≤ 1 then pure l else emit (.mulAdd [] [] l)

/-- A copy row `loc = a`, always (gives every bit of a constant word its own cell). -/
def dcopy (a : LinT) : DB LinT := emit (.mulAdd [] [] a)

variable (ri ci : ℕ → LinT)

/-- **The product gate** at the next position `k`: `p_A ← rowW′[k]·a + p_A`,
`p_B ← rowW′[k]·b + p_B` (two rows, two locals); its value is `colW[k]`. -/
def dmul (a b : LinT) : DB LinT :=
  modifyGet fun s =>
    let k := (pos (m := Blake2sCircuit.m) s.next).val
    let nx := s.next; let nl := s.nl; let nr := s.nr; let pa := s.accA; let pb := s.accB
    (ci k, ⟨nx + 1, (s.gs.push (.mulAdd (ri k) a pa)).push (.mulAdd (ri k) b pb),
      nl + 2, nr + 2, L nl, L (nl + 1)⟩)

/-- `n` values from a program per index, in order. -/
def dvec {β : Type} : (n : ℕ) → (Fin n → DB β) → DB (Vector β n)
  | 0, _ => pure #v[]
  | n + 1, f => do
    let v ← dvec n fun i => f i.castSucc
    let x ← f (Fin.last n)
    pure (v.push x)

/-- A word's bits as cells. -/
def dcellW (x : Vector LinT 32) : DB (Vector LinT 32) := dvec 32 fun i => dcell x[i]

/-- The form of a position: `colW[k]`. -/
def dvar (k : Pos Blake2sCircuit.m) : LinT := ci k.val

/-- `xorW` (forms). -/
def dxorW (x y : Vector LinT 32) : Vector LinT 32 := Vector.ofFn fun i => dx x[i] y[i]

/-- `litW`. -/
def dlitW (c : UInt32) : Vector LinT 32 :=
  Vector.ofFn fun i => if c.toNat.testBit i then dvar ci constPos else []

/-- `inW`. -/
def dinW (b : ℕ) : Vector LinT 32 := Vector.ofFn fun i => dvar ci (pos (b + i))

/-- `addCarries` (each carry a cell). -/
def daddCarries (x y : Vector LinT 32) : (n : ℕ) → LinT → DB (List LinT)
  | 0, c => pure [c]
  | n + 1, c => do
    let i := 30 - n
    let g ← dmul ri ci (dx (x[i]'(by omega)) c) (dx (y[i]'(by omega)) c)
    let c' ← dcell (dx c g)
    let rest ← daddCarries x y n c'
    pure (c :: rest)

/-- `sumW`: each output bit a cell (one row of `p ⊕ q ⊕ c`). -/
def dsumW (p q : Vector LinT 32) (cs : List LinT) : DB (Vector LinT 32) :=
  dvec 32 fun i => dcell (dx (dx p[i] q[i]) (cs.getD i []))

/-- `addW`. -/
def daddW (x y : Vector LinT 32) : DB (Vector LinT 32) :=
  daddCarries ri ci x y 31 [] >>= dsumW x y

/-- `majorities` (the majority bits are forms). -/
def dmajorities (x y z : Vector LinT 32) : (n : ℕ) → DB (List LinT)
  | 0 => pure []
  | n + 1 => do
    let i := 30 - n
    let g ← dmul ri ci (dx (x[i]'(by omega)) (z[i]'(by omega))) (dx (y[i]'(by omega)) (z[i]'(by omega)))
    let rest ← dmajorities x y z n
    pure (dx g (z[i]'(by omega)) :: rest)

/-- `rippleCarries` (each carry a cell). -/
def drippleCarries (p q : Vector LinT 32) : (n : ℕ) → LinT → DB (List LinT)
  | 0, c => pure [c]
  | n + 1, c => do
    let i := 30 - n
    if 1 ≤ i then
      let g ← dmul ri ci (dx (p[i]'(by omega)) c) (dx (q[i]'(by omega)) c)
      let c' ← dcell (dx c g)
      let rest ← drippleCarries p q n c'
      pure (c :: rest)
    else
      let rest ← drippleCarries p q n c
      pure (c :: rest)

/-- `xor3W` (forms). -/
def dxor3W (x y z : Vector LinT 32) : Vector LinT 32 := Vector.ofFn fun i => dx (dx x[i] y[i]) z[i]

/-- `shiftW`. -/
def dshiftW (ms : List LinT) : Vector LinT 32 :=
  Vector.ofFn fun i => if i.val = 0 then [] else ms.getD (i.val - 1) []

/-- `add3W`. -/
def dadd3W (x y z : Vector LinT 32) : DB (Vector LinT 32) := do
  let ms ← dmajorities ri ci x y z 31
  let cs ← drippleCarries ri ci (dxor3W x y z) (dshiftW ms) 31 []
  dsumW (dxor3W x y z) (dshiftW ms) cs

/-- The row bits of a `G` block. -/
def gBits : ℕ := 10

/-- `gW`, in a fresh block of `2^gBits` rows and locals; its four output words are cells. -/
def dgW (v : Vector (Vector LinT 32) 16) (a b c d : Fin 16) (mx my : Vector LinT 32) :
    DB (Vector (Vector LinT 32) 16) := do
  padTo gBits
  let a1 ← dadd3W ri ci v[a] v[b] mx
  let d1 := GOps.rotrW (dxorW v[d] a1) 16
  let c1 ← daddW ri ci v[c] d1
  let b1 := GOps.rotrW (dxorW v[b] c1) 12
  let a2 ← dadd3W ri ci a1 b1 my
  let d2 := GOps.rotrW (← dcellW (dxorW d1 a2)) 8
  let c2 ← daddW ri ci c1 d2
  let b2 := GOps.rotrW (← dcellW (dxorW b1 c2)) 7
  pure ((((v.set a a2).set b b2).set c c2).set d d2)

/-- `roundW`. -/
def droundW (v m' : Vector (Vector LinT 32) 16) (s : Vector (Fin 16) 16) :
    DB (Vector (Vector LinT 32) 16) := do
  let v ← dgW ri ci v 0 4 8 12 m'[s[0]] m'[s[1]]
  let v ← dgW ri ci v 1 5 9 13 m'[s[2]] m'[s[3]]
  let v ← dgW ri ci v 2 6 10 14 m'[s[4]] m'[s[5]]
  let v ← dgW ri ci v 3 7 11 15 m'[s[6]] m'[s[7]]
  let v ← dgW ri ci v 0 5 10 15 m'[s[8]] m'[s[9]]
  let v ← dgW ri ci v 1 6 11 12 m'[s[10]] m'[s[11]]
  let v ← dgW ri ci v 2 7 8 13 m'[s[12]] m'[s[13]]
  dgW ri ci v 3 4 9 14 m'[s[14]] m'[s[15]]

/-- `initW`, word `w` (the compression runs `dvec 16 dinitWord`): the words built from the IV get a cell per bit (`dcopy`), so that every `G` reads
single, distinct cells. -/
def dinitWord (w : Fin 16) : DB (Vector LinT 32) :=
  if w.val < 8 then pure (dinW ci (32 * w))
  else if w.val < 12 then dvec 32 fun i => dcopy (dlitW ci iv[w.val - 8])[i]
  else dvec 32 fun i => dcopy (dxorW (dlitW ci iv[w.val - 8]) (dinW ci (counterLo + 32 * (w.val - 12))))[i]

/-- Output word `w` of the compression: `v[w] ⊕ v[w+8] ⊕ h[w]`, its bits as cells. -/
def dfinWord (v : Vector (Vector LinT 32) 16) (w : Fin 8) : DB (Vector LinT 32) :=
  dcellW (dxorW (dxorW v[w] v[w.val + 8]) (dinW ci (32 * w)))

/-- `compressW`. -/
def dcompressW : DB (Vector (Vector LinT 32) 8) := do
  let msg : Vector (Vector LinT 32) 16 := Vector.ofFn fun w => dinW ci (msgBase + 32 * w)
  let v0 ← dvec 16 (dinitWord ci)
  let v ← sigma.toList.foldlM (fun v s => droundW ri ci v msg s) v0
  padTo gBits
  dvec 8 (dfinWord ci v)

/-- A product row into accumulator `A` (`B` if `b`): `p ← rowW′[k]·a + p`. -/
def dacc (b : Bool) (k : ℕ) (a : LinT) : DB Unit :=
  modifyGet fun s =>
    let nx := s.next; let nl := s.nl; let nr := s.nr; let pa := s.accA; let pb := s.accB
    ((), ⟨nx, s.gs.push (.mulAdd (ri k) a (if b then pb else pa)), nl + 1, nr + 1,
      if b then pa else L nl, if b then L nl else pb⟩)

/-- The accumulations after the compression (`walkABF`'s order): per output row the form into `A`
and the constant into `B`; per input position `colW[k]` into `A` and the constant into `B`; the
constant's row into both. -/
def accOps (r : Vector (Vector LinT 32) 8) : List (Bool × ℕ × LinT) :=
  (outPairs r).flatMap (fun p => [(false, p.1.val, p.2), (true, p.1.val, dvar ci constPos)]) ++
    Eval.inPos.map (fun k => (false, k, dvar ci (pos k))) ++
    Eval.inPos.map (fun k => (true, k, dvar ci constPos)) ++
    [(false, constPos.val, dvar ci constPos), (true, constPos.val, dvar ci constPos)]

/-- Row weight `k` (`0` past `n`): input `k`. -/
def rowI (n k : ℕ) : LinT := if k < n then I k else []

/-- Column weight `j` (`0` past `m`): input `n + j`, after the `n` row weights. -/
def colI (n m j : ℕ) : LinT := if j < m then I (n + j) else []

/-- The builder's start: gate position `gateBase`, nothing emitted. -/
def dst0 : DSt := ⟨gateBase, #[], 0, 0, [], []⟩

/-- **The walk's DAG**, the builder's final state for `rowW′ : AF n`, `colW : AF m`: the compression,
then the accumulations. -/
def dwalkRun (n m : ℕ) : DSt :=
  let p := (dcompressW (rowI n) (colI n m)).run dst0
  (((accOps (colI n m) p.1).forM fun t => dacc (rowI n) t.1 t.2.1 t.2.2).run p.2).2

/-- **The `walkAB` template** for `rowW′ : AF n`, `colW : AF m` (inputs `rowW′`, then `colW`): the
DAG's gates; outputs the two accumulators. Irreducible: no unification evaluates the DAG. -/
@[irreducible] def tplWalkG (n m : ℕ) : Tpl :=
  ⟨(dwalkRun n m).gs.toList, [(dwalkRun n m).accA, (dwalkRun n m).accB]⟩

/-! ## Controls -/

/-- (+) A form of two terms becomes a cell: one gate is emitted. -/
theorem dcell_emits (a b : Wire × F) (s : DSt) : ((dcell [a, b]).run s).2.gs.size = s.gs.size + 1 := by
  show (s.gs.push _).size = _
  exact Array.size_push ..

/-- (−) A single wire stays a wire: no gate. -/
theorem dcell_free (a : Wire × F) (s : DSt) : ((dcell [a]).run s).2 = s := rfl

/-- (+) Padding: `r` empty rows and `l` locals, its equation trivial. -/
theorem pad_rows : (Gate.pad 2 3).rows 0 = [⟨[], [], []⟩, ⟨[], [], []⟩] ∧ (Gate.pad 2 3).nloc = 3 :=
  ⟨rfl, rfl⟩

/-- (−) An XOR row constrains its cell: `loc 2 = loc 0 + loc 1` fails at `(0, 0, 1)`. -/
theorem xor_row_neg :
    ¬ (Gate.mulAdd [] [] [(.loc 0, 1), (.loc 1, 1)]).Eqn ⟨1, fun _ => 0, fun k => if k = 2 then 1 else 0⟩ 2 := by
  simp [Gate.Eqn, LinT.ev, Wire.ev]

end Tpl
end FR

end G6_FRVIRTplDag

section G6_FRVIRTplTab

-- New for `flock-recursive` (BLUEPRINT A.11, stage S-E3; track L-circ).

/-!
# Replay templates over `eq` tables: `targetS`, `slotW`, `maskRows`

BLUEPRINT A.11. `eqTblG` builds `FRMLE.eqTable` over forms, one product per table entry of the
coordinate below (`eqTblG_ev`); the templates mirror `implC`'s `targetSLeafI` (the leaf kinds'
`targetS`), `slotWI` and `FRVIR.maskRows`.
-/

namespace FR
namespace Tpl
open Circ

variable {e : Env}

/-! ## `eq` tables over forms (`FRMLE.eqTable`'s order: the first coordinate is the low bit) -/

theorem getElem_flatMap_pair {α β : Type*} (f g : α → β) :
    ∀ (l : List α) (u : ℕ) (h : u < (l.flatMap fun x => [f x, g x]).length),
    (l.flatMap fun x => [f x, g x])[u] =
      if u % 2 = 0 then f (l[u / 2]'(by simp at h; omega)) else g (l[u / 2]'(by simp at h; omega))
  | [], u, h => by simp at h
  | x :: l, u, h => by
    rcases u with _ | _ | u
    · simp
    · simp
    · have := getElem_flatMap_pair f g l u (by simp at h ⊢; omega)
      simp only [List.flatMap_cons, List.cons_append, List.nil_append, List.getElem_cons_succ] at this ⊢
      rw [this]
      simp only [show (u + 2) % 2 = u % 2 by omega, show (u + 2) / 2 = u / 2 + 1 by omega,
        List.getElem_cons_succ]

theorem length_flatMap_two {α β : Type*} (f g : α → β) (l : List α) :
    (l.flatMap fun x => [f x, g x]).length = 2 * l.length := by
  induction l with
  | nil => rfl
  | cons x l ih => simp [List.flatMap_cons, ih]; ring

theorem eqTable_toList_cons {R : Type*} [CommRing R] (c : R) (r : List R) :
    (eqTable (c :: r)).toList = (eqTable r).toList.flatMap fun x => [x * (1 - c), x * c] := by
  apply List.ext_getElem (by rw [length_flatMap_two]; simp [eqTable])
  intro u h₁ h₂
  rw [getElem_flatMap_pair (fun x => x * (1 - c)) (fun x => x * c)]
  simp only [eqTable, Array.getElem_toList, Array.getElem_ofFn]
  rcases Nat.mod_two_eq_zero_or_one u with h | h <;> simp [h]

theorem flatMap_range_getD {β : Type*} (l : List F) (f : F → List β) :
    l.flatMap f = (List.range l.length).flatMap fun i => f (l.getD i 0) := by
  induction l with
  | nil => rfl
  | cons x l ih =>
    simp only [List.length_cons, List.range_succ_eq_map, List.flatMap_cons, List.flatMap_map, ih,
      Function.comp_def, List.getD_cons_zero, List.getD_cons_succ]

theorem getD_map_ev (l : List LinT) (i : ℕ) :
    (l.getD i []).ev e = (l.map (LinT.ev e)).getD i 0 := by
  rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, List.getElem?_map]
  cases l[i]? <;> rfl

/-- **`eqTable` over forms**: per coordinate (the last first), one product per entry (the previous
table's entries read from an array: `List.getD` per entry was quadratic in the table, INIT). -/
def eqTblG : List LinT → ℕ → List Gate × List LinT
  | [], _ => ([], [C 1])
  | c :: cs, k =>
    let r := eqTblG cs k
    let k' := k + nlocs r.1
    let a := r.2.toArray
    (r.1 ++ mulsG r.2.length (fun i => a.getD i []) (fun _ => c),
     (List.range r.2.length).flatMap fun i => [a.getD i [] ++ sc (-1) (L (k' + i)), L (k' + i)])

theorem toArray_getD {α : Type*} (l : List α) (i : ℕ) (d : α) : l.toArray.getD i d = l.getD i d := by
  simp [Array.getD_eq_getD_getElem?, List.getD_eq_getElem?_getD]

theorem eqTblG_nlocs : ∀ (cs : List LinT) (k : ℕ), nlocs (eqTblG cs k).1 + 1 = 2 ^ cs.length ∧
    (eqTblG cs k).2.length = 2 ^ cs.length
  | [], _ => ⟨rfl, rfl⟩
  | c :: cs, k => by
    obtain ⟨h1, h2⟩ := eqTblG_nlocs cs k
    have hm := mulsG_nlocs (eqTblG cs k).2.length (fun i => (eqTblG cs k).2.getD i []) (fun _ => c)
    refine ⟨?_, ?_⟩
    · simp only [eqTblG, toArray_getD, nlocs, List.map_append, List.sum_append] at h1 hm ⊢
      rw [hm, h2, List.length_cons, pow_succ]; omega
    · simp only [eqTblG, toArray_getD]
      rw [length_flatMap_two, List.length_range, h2, List.length_cons, pow_succ]; ring

theorem eqTblG_ev (h1 : e.one = 1) : ∀ (cs : List LinT) (k : ℕ), Eqns e (eqTblG cs k).1 k →
    (eqTblG cs k).2.map (LinT.ev e) = (eqTable (cs.map (LinT.ev e))).toList
  | [], _, _ => by simp [eqTblG, eqTable, h1]
  | c :: cs, k, h => by
    simp only [eqTblG, toArray_getD, Eqns.append] at h
    have ih := eqTblG_ev h1 cs k h.1
    have hm := mulsG_eqns h.2
    rw [List.map_cons, eqTable_toList_cons, ← ih, flatMap_range_getD, List.length_map]
    simp only [eqTblG, toArray_getD, List.map_flatMap]
    refine List.flatMap_congr fun i hi => ?_
    have hi := List.mem_range.1 hi
    rw [← getD_map_ev]
    simp only [List.map_cons, List.map_nil, ev_append, ev_sc, ev_L, hm i hi]
    simp only [List.cons.injEq, and_true]
    ring

theorem nlocs_append (a b : List Gate) : nlocs (a ++ b) = nlocs a + nlocs b := by
  simp [nlocs]

/-! ## `targetS` of the leaf kinds (`Impl.targetSLeafI`) -/

/-- The 8 coordinates `zLo r` as forms: the pinned `pr₀ … pr₆` (constants), then `r₀`. -/
def zLoT (pr : Fin 7 → F) (n : ℕ) : List LinT :=
  List.ofFn fun l : Fin 8 => if h : l.val < 7 then C (pr ⟨l, h⟩) else if 0 < n then I 0 else []

/-- The template over constant pins `pr` and coefficients `cf` (generic, so that no proof sees the
constants). -/
def tgtT (pr : Fin 7 → F) (cf : ℕ → F) (n : ℕ) : Tpl :=
  let g := eqTblG (zLoT pr n) 0
  ⟨g.1, (List.range 64).map fun σ => (List.range 256).flatMap fun hi => sc (cf (σ + 64 * hi)) (g.2.getD hi [])⟩

/-- **`targetS`** for `r : AF n`: the table over `zLo r` (255 products), each output a constant
combination of its entries. -/
def tplTargetS (n : ℕ) : Tpl := tgtT pinnedRho (fun p => Impl.chainTab.getD p 0) n

theorem ev_flatMap {α : Type*} (l : List α) (f : α → LinT) :
    LinT.ev e (l.flatMap f) = (l.map fun x => (f x).ev e).sum := by
  induction l with
  | nil => rfl
  | cons x l ih => simp [List.flatMap_cons, ih]

theorem sumTo_list {M : Type*} [AddCommMonoid M] (n : ℕ) (g : ℕ → M) :
    sumTo n g = ((List.range n).map g).sum := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [sumTo, Nat.fold_succ, ← sumTo, ih, List.range_succ, List.map_append, List.sum_append]; simp

theorem tgtT_ok (h1 : e.one = 1) (pr : Fin 7 → F) (cf : ℕ → F) {r : Array F} (hi : InpIs e r.toList)
    (h : Eqns e (tgtT pr cf r.size).gates 0) :
    (tgtT pr cf r.size).outs.map (LinT.ev e) = encV (.af (Array.ofFn (n := 64) fun σ =>
      sumTo 256 fun hi => cf (σ + 64 * hi) *
        (eqTable (List.ofFn fun l : Fin 8 => if h : l.val < 7 then pr ⟨l, h⟩ else r.getD 0 0)).getD hi 0)) := by
  have hz : (zLoT pr r.size).map (LinT.ev e) =
      List.ofFn fun l : Fin 8 => if h : l.val < 7 then pr ⟨l, h⟩ else r.getD 0 0 := by
    refine List.ext_getElem (by simp [zLoT]) fun l h₁ h₂ => ?_
    simp only [zLoT, List.getElem_map, List.getElem_ofFn]
    by_cases hl : l < 7
    · simp only [hl, dite_true, ev_C, h1, mul_one]
    · by_cases hn : 0 < r.size
      · simp only [hl, dite_false, hn, if_true, ev_I]; rw [hi, arr_getD]
      · simp only [hl, dite_false, hn, if_false, ev_nil]
        rw [Array.getD_eq_getD_getElem?, Array.getElem?_eq_none (by omega)]; rfl
  have ht := eqTblG_ev h1 _ 0 h
  rw [hz] at ht
  simp only [tgtT, encV, Array.toList_ofFn, List.map_map]
  refine List.ext_getElem (by simp) fun σ h₁ h₂ => ?_
  simp only [List.getElem_map, List.getElem_range, Function.comp_apply, List.getElem_ofFn,
    ev_flatMap, ev_sc, sumTo_list]
  refine congrArg List.sum (List.map_congr_left fun hi _ => ?_)
  rw [getD_map_ev, ht, arr_getD]

theorem tplTargetS_ok (h1 : e.one = 1) {r : Array F} (hi : InpIs e r.toList)
    (h : Eqns e (tplTargetS r.size).gates 0) :
    (tplTargetS r.size).outs.map (LinT.ev e) = encV (.af (Impl.targetSLeafI r)) :=
  tgtT_ok h1 pinnedRho (fun p => Impl.chainTab.getD p 0) hi h

/-! ## `slotW` (`Impl.slotWI`) -/

/-- Ten coordinates of an `AF n` input at offset `o` (missing ones `0`). -/
def ptT (o n : ℕ) : List LinT := List.ofFn fun l : Fin 10 => if l.val < n then I (o + l) else []

/-- **`slotW`** of slot map `s` for `θ : AF n`, `r : AF m`: two tables (1023 products each), then
the 256 products and their sum. -/
def tplSlotW (s n m : ℕ) : Tpl :=
  let g₁ := eqTblG (ptT 0 n) 0
  let g₂ := eqTblG (ptT n m) (nlocs g₁.1)
  let k := nlocs g₁.1 + nlocs g₂.1
  ⟨g₁.1 ++ g₂.1 ++ mulsG 256 (fun σ => g₁.2.getD σ []) (fun σ => g₂.2.getD (Impl.slotBase s + σ) []),
   [(List.range 256).flatMap fun σ => L (k + σ)]⟩

theorem ptT_ev {xs ys : List F} (hi : InpIs e (xs ++ ys)) :
    (ptT 0 xs.length).map (LinT.ev e) = List.ofFn (fun l : Fin 10 => xs.getD l 0) ∧
    (ptT xs.length ys.length).map (LinT.ev e) = List.ofFn (fun l : Fin 10 => ys.getD l 0) := by
  constructor <;> refine List.ext_getElem (by simp [ptT]) fun l h₁ h₂ => ?_ <;>
    simp only [ptT, List.getElem_map, List.getElem_ofFn]
  · by_cases hl : l < xs.length
    · simp only [hl, if_true, ev_I, zero_add]; rw [hi, getD_append_left hl]
    · simp only [hl, if_false, ev_nil]
      rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by omega)]; rfl
  · by_cases hl : l < ys.length
    · simp only [hl, if_true, ev_I]; rw [hi, getD_append_right]
    · simp only [hl, if_false, ev_nil]
      rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by omega)]; rfl

theorem tbl_getD {cs : List LinT} {k : ℕ} {xs : List F}
    (h : (eqTblG cs k).2.map (LinT.ev e) = (eqTable xs).toList) (i : ℕ) :
    ((eqTblG cs k).2.getD i []).ev e = (eqTable xs).getD i 0 := by
  rw [getD_map_ev, h, arr_getD]

theorem ofFn_ptA (a : Array F) : List.ofFn (Impl.ptA 10 a) = List.ofFn fun l : Fin 10 => a.getD l 0 :=
  rfl

theorem tplSlotW_ok (h1 : e.one = 1) (s : ℕ) {θ r : Array F} (hi : InpIs e (θ.toList ++ r.toList))
    (h : Eqns e (tplSlotW s θ.size r.size).gates 0) :
    (tplSlotW s θ.size r.size).outs.map (LinT.ev e) = encV (.f (Impl.slotWI s θ r)) := by
  simp only [tplSlotW, Eqns.append, zero_add, nlocs_append] at h
  obtain ⟨⟨h₁, h₂⟩, h₃⟩ := h
  have hp := ptT_ev hi
  simp only [Array.length_toList] at hp
  have t₁ := eqTblG_ev h1 _ _ h₁; have t₂ := eqTblG_ev h1 _ _ h₂
  rw [hp.1] at t₁; rw [hp.2] at t₂
  have hm := mulsG_eqns h₃
  simp only [tplSlotW, List.map_cons, List.map_nil, encV, Impl.slotWI, List.cons.injEq, and_true,
    ev_flatMap, ev_L, sumTo_list]
  refine congrArg List.sum (List.map_congr_left fun σ hσ => ?_)
  rw [hm σ (List.mem_range.1 hσ), tbl_getD t₁, tbl_getD t₂, ofFn_ptA, ofFn_ptA]
  simp only [arr_getD]

/-! ## `maskRows` (`FRVIR.maskRows`) -/

theorem ev_flatten (l : List LinT) : LinT.ev e l.flatten = (l.map (LinT.ev e)).sum := by
  induction l with
  | nil => rfl
  | cons x l ih => simp [ih]

/-- The mask of row `k` as a form over the `n` kind weights. -/
def maskT (n k : ℕ) : LinT :=
  ((blockKinds.zipIdx.filter fun p => !isZeroRow p.1 k).map fun p => if p.2 < n then I p.2 else []).flatten

/-- **`maskRows`** for `kindW : AF n`, `rowW : AF m` (inputs in that order): one product per row. -/
def tplMaskRows (n m : ℕ) : Tpl :=
  ⟨mulsG m (fun k => I (n + k)) (maskT n), (List.range m).map L⟩

theorem tplMaskRows_ok {kw rw : Array F} (hi : InpIs e (kw.toList ++ rw.toList))
    (h : Eqns e (tplMaskRows kw.size rw.size).gates 0) :
    (tplMaskRows kw.size rw.size).outs.map (LinT.ev e) = encV (.af (maskRows kw rw)) := by
  have hm := mulsG_eqns h
  simp only [tplMaskRows, encV, List.map_map]
  refine List.ext_getElem (by simp [maskRows]) fun k h₁ h₂ => ?_
  have hk : k < rw.size := by simpa using h₁
  simp only [List.getElem_map, List.getElem_range, Function.comp_apply, ev_L, maskRows_eq, maskOf,
    Array.getElem_toList, Array.getElem_mapIdx]
  have hk' := hm k hk
  rw [zero_add] at hk'
  rw [hk']
  congr 1
  · rw [ev_I, hi, ← Array.length_toList, getD_append_right, arr_getD, Array.getD_eq_getD_getElem?,
      Array.getElem?_eq_getElem hk]; rfl
  · rw [maskT, ev_flatten, List.map_map]
    refine congrArg List.sum (List.map_congr_left fun p _ => ?_)
    simp only [Function.comp_apply]
    by_cases hp : p.2 < kw.size
    · simp only [hp, if_true, ev_I]; rw [hi, getD_append_left (by simpa using hp), arr_getD]
    · simp only [hp, if_false, ev_nil]
      rw [Array.getD_eq_getD_getElem?, Array.getElem?_eq_none (by omega)]; rfl

end Tpl
end FR

end G6_FRVIRTplTab
