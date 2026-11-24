-- New for lvm6 (PHF, start-up speed): `rowsK` without intermediate lists. `rowsKF` builds every row's entry list,
-- splits it (`splitEnt`), filters `o < 4` and pushes the keys; the row instances come from a list too. Here the keys
-- are pushed straight from the cells' (word, coefficient) pairs, in loops over the row instances.
import Lvm6VPhiChkF

/-!
# `rowsK`, fused

* `pushEnt a e`: the one key of `e` that survives `splitEnt` and `o < 4` (coordinate 0); **`pushL_split`**:
  `pushL keyE a ((l.flatMap splitEnt).filter (o < 4)) = l.foldl pushEnt a`.
* `pushT`, `rowPushA`, `rowPushXA`, `auxPushA`: `rowEntsA`, `rowEntsXA`, `auxEntsA` folded by `pushEnt`
  (**`rowPushA_eq`**, **`rowPushXA_eq`**, **`auxPushA_eq`**).
* **`rowsKG Q lay`**: `rowsKF`'s fold as loops; **`rowsKG_eq : rowsKG Q lay = rowsK Q lay`** (no hypothesis).
-/

set_option autoImplicit false

namespace Lvm6.V

open LeanVM.Parameters Lvm Lvm.E2V Lvm.Typed Lvm.Loop

/-! ## The layout caches -/

/-- `Row.w` by cases. -/
@[inline] def wF (τ : Ty) (r : Row) : ℕ :=
  match r.op with
  | .assert0 => 0
  | _ => match r.ty, τ with
    | .K, .K => 1
    | .E, .E => 1
    | _, _ => 0

theorem wF_eq (τ : Ty) : wF τ = Row.w τ := by
  funext r
  unfold wF Row.w Row.writes
  cases r.op <;> cases r.ty <;> cases τ <;> rfl

/-- `Block.tw` as a fold. -/
def twF (τ : Ty) (B : Block) : ℕ := B.tpl.foldl (fun s r => s + wF τ r) 0

theorem foldl_add_sum (f : Row → ℕ) : ∀ (l : List Row) (s : ℕ), l.foldl (fun s r => s + f r) s = s + (l.map f).sum
  | [], s => by simp
  | r :: l, s => by rw [List.foldl_cons, foldl_add_sum f l, List.map_cons, List.sum_cons]; omega

theorem twF_eq (τ : Ty) : twF τ = fun B : Block => B.tw τ := by
  funext B
  unfold twF Block.tw
  rw [foldl_add_sum, wF_eq, Nat.zero_add]

/-- **`FL.ofLay` with the writer counts as folds.** -/
def flOfLayG (Q : Program) (lay : Lay) : Lvm.Typed.K.FL :=
  let qb := Q.blocks.toArray
  let tpls := qb.map (·.tpl.toArray)
  let bl := lay.blocks.toArray
  let stK := K.psumA (qb.map fun B ↦ twF .K B * B.size) Q.nInK
  let stE := K.psumA (qb.map fun B ↦ twF .E B * B.size) Q.nInE
  let rk (τ : Ty) : Array (Array ℕ) := tpls.map fun tp ↦ K.psumA (tp.map (wF τ)) 0
  let own (τ : Ty) : Array (ℕ × ℕ × ℕ) := Id.run do
    let mut out : Array (ℕ × ℕ × ℕ) := #[]
    for b in [0:bl.size] do
      let B := bl.getD b default
      if B.tw τ > 0 then out := out.push (B.st τ, B.st τ + B.tw τ * 2 ^ B.l, b)
    return out
  let nB := bl.size
  let nX := nB + lay.aux.length
  let xch : Array (Array XChunk) := Id.run do
    let mut out : Array (Array XChunk) := Array.replicate nX #[]
    for c in lay.xs do
      if c.blk < nX then out := out.modify c.blk (·.push c)
    return out
  ⟨Q, lay, qb, tpls, bl, stK, stE, rk .K, rk .E, own .K, own .E, (lay.dense ++ lay.inp).toArray, xch,
    bl.map (·.srcK.toArray), bl.map (·.srcE.toArray), bl.map (·.cr.toArray),
    (lay.cst.map fun r ↦ (r.1, r.2.toArray)).toArray⟩

theorem flOfLayG_eq (Q : Program) (lay : Lay) : flOfLayG Q lay = Lvm.Typed.K.FL.ofLay Q lay := by
  unfold flOfLayG Lvm.Typed.K.FL.ofLay
  simp only [twF_eq, wF_eq]

/-- **`FLF.ofLay` with the writer counts as folds.** -/
def flfOfLayG (Q : Program) (lay : Lay) : K.FLF :=
  let F := flOfLayG Q lay
  ⟨F, F.qb.map (twF .K), F.qb.map (twF .E)⟩

theorem flfOfLayG_eq (Q : Program) (lay : Lay) : flfOfLayG Q lay = K.FLF.ofLay Q lay := by
  unfold flfOfLayG K.FLF.ofLay
  simp only [flOfLayG_eq, twF_eq]

/-! ## One entry's key -/

/-- **The key of an entry** that survives `splitEnt` and `o < 4`: its coordinate-0 part, if non-zero. -/
@[inline] def pushEnt (a : Array (FE2 × ℕ)) (e : Ent) : Array (FE2 × ℕ) :=
  if e.c.c₀ == 0 then a
  else a.push (if e.o / 4 = 0 then ⟨e.c.c₀, 0⟩ else ⟨0, e.c.c₀⟩, e.o % 4 + 4 * (e.x + 2 ^ 20 * e.y))

/-- `c·X^s` without the product. -/
theorem ofK_mul_xPowT (c : FK) (s : ℕ) : FE2.ofK c * xPowT s = if s = 0 then ⟨c, 0⟩ else ⟨0, c⟩ := by
  unfold xPowT
  split
  · show FE2.mul ⟨c, 0⟩ ⟨1, 0⟩ = ⟨c, 0⟩
    simp only [FE2.mul, FE2.mk.injEq, mul_one, mul_zero, add_zero]
    exact ⟨trivial, CharTwo.add_self_eq_zero c⟩
  · show FE2.mul ⟨c, 0⟩ ⟨0, 1⟩ = ⟨0, c⟩
    simp only [FE2.mul, mul_one, mul_zero, add_zero, zero_add]

theorem splitEnt_filter (e : Ent) : (splitEnt e).filter (fun e => decide (e.o < 4)) =
    if feCoord e.c 0 == 0 then [] else [⟨e.o % 4 + 4 * 0, e.x, e.y, FE2.ofK (feCoord e.c 0) * xPowT (e.o / 4)⟩] := by
  have h1 : ¬ e.o % 4 + 4 * 1 < 4 := by omega
  have h2 : ¬ e.o % 4 + 4 * 2 < 4 := by omega
  have h0 : e.o % 4 + 4 * 0 < 4 := by omega
  have hr : List.range 3 = [0, 1, 2] := rfl
  unfold splitEnt
  rw [hr]
  by_cases c0 : feCoord e.c 0 == 0 <;> by_cases c1 : feCoord e.c 1 == 0 <;> by_cases c2 : feCoord e.c 2 == 0 <;>
    simp only [List.filterMap_cons, List.filterMap_nil, c0, c1, c2, ite_true, ite_false, Bool.false_eq_true,
      List.filter_cons, List.filter_nil, decide_eq_true h0, decide_eq_false h1, decide_eq_false h2]

theorem pushEnt_eq (a : Array (FE2 × ℕ)) (e : Ent) :
    pushL keyE a ((splitEnt e).filter fun e => decide (e.o < 4)) = pushEnt a e := by
  rw [splitEnt_filter]
  unfold pushEnt
  simp only [feCoord, ofK_mul_xPowT]
  by_cases h : (e.c.c₀ == 0) = true <;> simp only [h, ↓reduceIte, Bool.false_eq_true] <;> rfl

/-- **The keys of a list of entries, one by one.** -/
theorem pushL_split (a : Array (FE2 × ℕ)) (l : List Ent) :
    pushL keyE a ((l.flatMap splitEnt).filter fun e => decide (e.o < 4)) = l.foldl pushEnt a := by
  induction l generalizing a with
  | nil => rfl
  | cons e l ih =>
    rw [List.flatMap_cons, List.filter_append, List.foldl_cons, ← pushEnt_eq, ← ih]
    unfold pushL
    rw [List.foldl_append]

/-! ## A row's keys -/

/-- `tagE o x l` folded by `pushEnt`. -/
@[inline] def pushT (o x : ℕ) (a : Array (FE2 × ℕ)) (l : List (ℕ × FE)) : Array (FE2 × ℕ) :=
  l.foldl (fun a p => pushEnt a ⟨o, x, p.1, p.2⟩) a

theorem foldl_tagE (o x : ℕ) (a : Array (FE2 × ℕ)) (l : List (ℕ × FE)) :
    (tagE o x l).foldl pushEnt a = pushT o x a l := by
  unfold tagE pushT
  rw [List.foldl_map]

/-- `rowEntsA` folded by `pushEnt`. -/
def rowPushA (A : K.AC) (C : K.SC) (G : K.FLF) (b t jf : ℕ) (a : Array (FE2 × ℕ)) : Array (FE2 × ℕ) :=
  let F := G.F
  let Bq := F.qb.getD b default
  let row := (F.tpls.getD b #[]).getD t default
  let j := unflat Bq.dims jf
  let x := match (F.crA.getD b #[]).getD t none with
    | some r => K.slotRA C F b r jf
    | none => 0
  let arg (k : ℕ) (w : FE) : List (ℕ × FE) :=
    let a := row.args.getD k default
    K.cellEntsFA A C F a.ty (a.at j) w
  let ck := F.stK.getD b 0 + G.twK.getD b 0 * jf + (F.rkK.getD b #[]).getD t 0
  let ce := F.stE.getD b 0 + G.twE.getD b 0 * jf + (F.rkE.getD b #[]).getD t 0
  let res : List (ℕ × FE) := K.cellEntsFA A C F row.ty (match row.ty with | .K => ck | .E => ce) 1
  match row.op with
  | .muladd => pushT 3 x (pushT 2 x (pushT 1 x (pushT 0 x a (arg 0 1)) (arg 1 1)) (arg 2 1)) res
  | .lin k k' => pushT 3 x (pushT 2 x (pushT 2 x (pushT 2 x a (arg 0 1)) (arg 1 (FE.ofK k)))
      [(F.lay.one, FE.ofK k')]) res
  | .assert0 => pushT 1 x (pushT 0 x a (arg 1 1)) (arg 0 1)
  | .fixmul => pushT 3 x (pushT 2 x (pushT 2 x a (arg 0 (FE.ofK (F.Q.fixMat j)))) (arg 1 1)) res
  | _ => a

theorem rowPushA_eq (A : K.AC) (C : K.SC) (G : K.FLF) (b t jf : ℕ) (a : Array (FE2 × ℕ)) :
    rowPushA A C G b t jf a = (K.rowEntsA A C G b t jf).foldl pushEnt a := by
  unfold rowPushA K.rowEntsA
  dsimp only
  cases ((G.F.tpls.getD b #[]).getD t default).op <;>
    simp only [List.foldl_append, foldl_tagE, List.foldl_nil, List.foldl_cons, pushT] <;> rfl

/-- `rowEntsXA` folded by `pushEnt`. -/
def rowPushXA (A : K.AC) (C : K.SC) (G : K.FLF) (b t jf : ℕ) (a : Array (FE2 × ℕ)) : Array (FE2 × ℕ) :=
  let F := G.F
  let Bq := F.qb.getD b default
  let row := (F.tpls.getD b #[]).getD t default
  let j := unflat Bq.dims jf
  let x := match (F.crA.getD b #[]).getD t none with
    | some r => K.slotRA C F b r jf
    | none => 0
  let arg (k : ℕ) (w : FE) : List (ℕ × FE) :=
    let a := row.args.getD k default
    K.cellEntsFA A C F a.ty (a.at j) w
  let ck := F.stK.getD b 0 + G.twK.getD b 0 * jf + (F.rkK.getD b #[]).getD t 0
  let ce := F.stE.getD b 0 + G.twE.getD b 0 * jf + (F.rkE.getD b #[]).getD t 0
  let res : List (ℕ × FE) := K.cellEntsFA A C F row.ty (match row.ty with | .K => ck | .E => ce) 1
  let res1 : List (ℕ × FE) := K.cellEntsFA A C F .K (ck + 1) 1
  match row.op with
  | .e2 .mul false =>
      pushT 7 x (pushT 3 x (pushT 6 x (pushT 2 x (pushT 5 x (pushT 1 x (pushT 4 x (pushT 0 x a
        (arg 0 1)) (arg 1 1)) (arg 2 1)) (arg 3 1)) (arg 4 1)) (arg 5 1)) res) res1
  | .e2 (.lin k k₀ k₁) false =>
      pushT 7 x (pushT 3 x (pushT 6 x (pushT 6 x (pushT 6 x (pushT 2 x (pushT 2 x (pushT 2 x a
        (arg 0 1)) (arg 2 (FE.ofK k))) [(F.lay.one, FE.ofK k₀)]) (arg 1 1)) (arg 3 (FE.ofK k)))
        [(F.lay.one, FE.ofK k₁)]) res) res1
  | .e2 _ true => a
  | _ => rowPushA A C G b t jf a

theorem rowPushXA_eq (A : K.AC) (C : K.SC) (G : K.FLF) (b t jf : ℕ) (a : Array (FE2 × ℕ)) :
    rowPushXA A C G b t jf a = (K.rowEntsXA A C G b t jf).foldl pushEnt a := by
  unfold rowPushXA K.rowEntsXA
  dsimp only
  cases ((G.F.tpls.getD b #[]).getD t default).op with
  | e2 f h =>
    cases f <;> cases h <;> simp only [List.foldl_append, foldl_tagE, List.foldl_nil, List.foldl_cons, pushT] <;> rfl
  | _ => exact rowPushA_eq A C G b t jf a

/-- `auxEntsA` folded by `pushEnt`. -/
def auxPushA (A : K.AC) (C : K.SC) (G : K.FLF) (k r j : ℕ) (a : Array (FE2 × ℕ)) : Array (FE2 × ℕ) :=
  let F := G.F
  let x := K.slotRA C F (F.bl.size + k) r j
  ((A.aux.getD k #[]).getD r default).ops.foldl (fun a e ↦
    pushT e.1 x a (match e.2.1 with
      | .word base stride => [(base + stride * j, e.2.2)]
      | .cell c => K.cellEntsFA A C F c.ty (c.at [j]) e.2.2
      | .one => [(F.lay.one, e.2.2)])) a

theorem auxPushA_eq (A : K.AC) (C : K.SC) (G : K.FLF) (k r j : ℕ) (a : Array (FE2 × ℕ)) :
    auxPushA A C G k r j a = (K.auxEntsA A C G k r j).foldl pushEnt a := by
  unfold auxPushA K.auxEntsA
  dsimp only
  rw [List.foldl_flatMap]
  simp only [foldl_tagE]
  rfl

/-- `rawXA` folded by `pushEnt`. -/
def rawPushA (A : K.AC) (C : K.SC) (G : K.FLF) (a : Array (FE2 × ℕ)) : TSrc → ℕ → Array (FE2 × ℕ)
  | .row b t, jf => rowPushXA A C G b t jf a
  | .aux k r, j => auxPushA A C G k r j a

theorem rawPushA_eq (A : K.AC) (C : K.SC) (G : K.FLF) (a : Array (FE2 × ℕ)) (s : TSrc) (jf : ℕ) :
    rawPushA A C G a s jf = (rawXA A C G s jf).foldl pushEnt a := by
  cases s with
  | row b t => exact rowPushXA_eq A C G b t jf a
  | aux k r => exact auxPushA_eq A C G k r jf a

/-! ## The `K` words in a table -/

/-- A table of `wordKFA`'s values at `L, L + 1, …`. -/
structure WM where
  L : ℕ
  M : Array ℕ

/-- `wordKFA` read from a table where it has one. -/
@[inline] def wordKM (W : WM) (A : K.AC) (C : K.SC) (F : Lvm.Typed.K.FL) (n : ℕ) : ℕ :=
  if h : W.L ≤ n ∧ n - W.L < W.M.size then W.M[n - W.L] else K.wordKFA A C F n

/-- **The table of `wordKFA`** on `[L, N)`. -/
def memoK (A : K.AC) (C : K.SC) (F : Lvm.Typed.K.FL) (L N : ℕ) : WM :=
  ⟨L, (Array.range (N - L)).map fun i => K.wordKFA A C F (L + i)⟩

theorem wordKM_memoK (A : K.AC) (C : K.SC) (F : Lvm.Typed.K.FL) (L N n : ℕ) :
    wordKM (memoK A C F L N) A C F n = K.wordKFA A C F n := by
  unfold wordKM memoK
  dsimp only
  split
  · rename_i h
    simp only [Array.getElem_map, Array.getElem_range]
    congr 1
    omega
  · rfl

/-- A cell's keys (`cellEntsFA` tagged and folded), the `K` words from `M`. -/
@[inline] def pushC (M : WM) (A : K.AC) (C : K.SC) (F : Lvm.Typed.K.FL) (o x : ℕ) (a : Array (FE2 × ℕ)) (τ : Ty)
    (n : ℕ) (w : FE) : Array (FE2 × ℕ) :=
  match τ with
  | .K => match F.cst n with
    | some v => pushEnt a ⟨o, x, F.lay.one, w * FE.ofK v⟩
    | none => pushEnt a ⟨o, x, wordKM M A C F n, w⟩
  | .E => pushT o x a (K.cellEntsFA A C F .E n w)

theorem pushC_memoK (A : K.AC) (C : K.SC) (F : Lvm.Typed.K.FL) (L N o x : ℕ) (a : Array (FE2 × ℕ)) (τ : Ty) (n : ℕ)
    (w : FE) : pushC (memoK A C F L N) A C F o x a τ n w = pushT o x a (K.cellEntsFA A C F τ n w) := by
  unfold pushC K.cellEntsFA
  cases τ with
  | K =>
    cases F.cst n with
    | some v => rfl
    | none =>
      show pushEnt a ⟨o, x, wordKM (memoK A C F L N) A C F n, w⟩ = _
      rw [wordKM_memoK]
      rfl
  | E => rfl

/-- `unflat` with the dimensions' powers given (no `2 ^ d` per call). -/
def unflatP : List (ℕ × ℕ) → ℕ → List ℕ
  | [], _ => []
  | d :: ds, n => n % d.2 :: unflatP ds (n / d.2)

theorem unflatP_eq : ∀ (ds : List ℕ) (n : ℕ), unflatP (ds.map fun d => (d, 2 ^ d)) n = unflat ds n
  | [], _ => rfl
  | d :: ds, n => by
    rw [List.map_cons, unflatP, unflat, unflatP_eq ds]

/-- A template row's data that does not move with the iteration. -/
structure RowD where
  row : Row
  /-- The loop dimensions with their powers. -/
  dims : List (ℕ × ℕ)
  /-- The slot without the iteration (`slotRA C F b r 0`'s search), if any. -/
  xb : Option ℕ
  sK : ℕ
  tK : ℕ
  rK : ℕ
  sE : ℕ
  tE : ℕ
  rE : ℕ

/-- The slot search of `slotRA`, once per template row. -/
def slotB (C : K.SC) (F : Lvm.Typed.K.FL) (b r : ℕ) : Option ℕ :=
  match K.bsI (C.xt.getD b #[]) r with
  | some i =>
    let c := (F.xch.getD b #[]).getD i default
    some (c.base + (r - c.r0) * 2 ^ c.l)
  | none => none

theorem slotB_eq (C : K.SC) (F : Lvm.Typed.K.FL) (b r jf : ℕ) :
    (match slotB C F b r with | some v => v + jf | none => 0) = K.slotRA C F b r jf := by
  unfold slotB K.slotRA
  cases K.bsI (C.xt.getD b #[]) r <;> rfl

/-- **Row `t` of block `b`'s data.** -/
def RowD.of (C : K.SC) (G : K.FLF) (b t : ℕ) : RowD :=
  let F := G.F
  ⟨(F.tpls.getD b #[]).getD t default, (F.qb.getD b default).dims.map fun d => (d, 2 ^ d),
    match (F.crA.getD b #[]).getD t none with
    | some r => slotB C F b r
    | none => none,
    F.stK.getD b 0, G.twK.getD b 0, (F.rkK.getD b #[]).getD t 0,
    F.stE.getD b 0, G.twE.getD b 0, (F.rkE.getD b #[]).getD t 0⟩

/-- `rowPushA` on `RowD` and `pushC`. -/
def rowPushM (M : WM) (A : K.AC) (C : K.SC) (F : Lvm.Typed.K.FL) (D : RowD) (jf : ℕ) (a : Array (FE2 × ℕ)) :
    Array (FE2 × ℕ) :=
  let row := D.row
  let j := unflatP D.dims jf
  let x := match D.xb with
    | some v => v + jf
    | none => 0
  let ck := D.sK + D.tK * jf + D.rK
  let ce := D.sE + D.tE * jf + D.rE
  let arg (k : ℕ) (o : ℕ) (w : FE) (a : Array (FE2 × ℕ)) : Array (FE2 × ℕ) :=
    let c := row.args.getD k default
    pushC M A C F o x a c.ty (c.at j) w
  let res (o : ℕ) (a : Array (FE2 × ℕ)) : Array (FE2 × ℕ) :=
    pushC M A C F o x a row.ty (match row.ty with | .K => ck | .E => ce) 1
  match row.op with
  | .muladd => res 3 (arg 2 2 1 (arg 1 1 1 (arg 0 0 1 a)))
  | .lin k k' => res 3 (pushEnt (arg 1 2 (FE.ofK k) (arg 0 2 1 a)) ⟨2, x, F.lay.one, FE.ofK k'⟩)
  | .assert0 => arg 0 1 1 (arg 1 0 1 a)
  | .fixmul => res 3 (arg 1 2 1 (arg 0 2 (FE.ofK (F.Q.fixMat j)) a))
  | _ => a

/-- `rowPushXA` on `RowD` and `pushC`. -/
def rowPushXM (M : WM) (A : K.AC) (C : K.SC) (F : Lvm.Typed.K.FL) (D : RowD) (jf : ℕ) (a : Array (FE2 × ℕ)) :
    Array (FE2 × ℕ) :=
  let row := D.row
  let j := unflatP D.dims jf
  let x := match D.xb with
    | some v => v + jf
    | none => 0
  let ck := D.sK + D.tK * jf + D.rK
  let ce := D.sE + D.tE * jf + D.rE
  let arg (k : ℕ) (o : ℕ) (w : FE) (a : Array (FE2 × ℕ)) : Array (FE2 × ℕ) :=
    let c := row.args.getD k default
    pushC M A C F o x a c.ty (c.at j) w
  let res (o : ℕ) (a : Array (FE2 × ℕ)) : Array (FE2 × ℕ) :=
    pushC M A C F o x a row.ty (match row.ty with | .K => ck | .E => ce) 1
  match row.op with
  | .e2 .mul false =>
      pushC M A C F 7 x (res 3 (arg 5 6 1 (arg 4 2 1 (arg 3 5 1 (arg 2 1 1 (arg 1 4 1 (arg 0 0 1 a))))))) .K (ck + 1) 1
  | .e2 (.lin k k₀ k₁) false =>
      pushC M A C F 7 x (res 3 (pushEnt (arg 3 6 (FE.ofK k) (arg 1 6 1
        (pushEnt (arg 2 2 (FE.ofK k) (arg 0 2 1 a)) ⟨2, x, F.lay.one, FE.ofK k₀⟩))) ⟨6, x, F.lay.one, FE.ofK k₁⟩))
        .K (ck + 1) 1
  | .e2 _ true => a
  | _ => rowPushM M A C F D jf a

theorem rowPushM_eq (A : K.AC) (C : K.SC) (G : K.FLF) (L N b t jf : ℕ) (a : Array (FE2 × ℕ)) :
    rowPushM (memoK A C G.F L N) A C G.F (RowD.of C G b t) jf a = rowPushA A C G b t jf a := by
  unfold rowPushM rowPushA RowD.of
  dsimp only
  simp only [pushC_memoK, unflatP_eq]
  have hx : (match (match (G.F.crA.getD b #[]).getD t none with
      | some r => slotB C G.F b r
      | none => none) with
      | some v => v + jf
      | none => 0) = (match (G.F.crA.getD b #[]).getD t none with
      | some r => K.slotRA C G.F b r jf
      | none => 0) := by
    cases (G.F.crA.getD b #[]).getD t none with
    | some r => exact slotB_eq C G.F b r jf
    | none => rfl
  rw [hx]
  cases ((G.F.tpls.getD b #[]).getD t default).op <;> simp only [pushT, List.foldl_cons, List.foldl_nil]

theorem rowPushXM_eq (A : K.AC) (C : K.SC) (G : K.FLF) (L N b t jf : ℕ) (a : Array (FE2 × ℕ)) :
    rowPushXM (memoK A C G.F L N) A C G.F (RowD.of C G b t) jf a = rowPushXA A C G b t jf a := by
  unfold rowPushXM rowPushXA
  rw [← rowPushM_eq A C G L N b t jf a]
  unfold RowD.of
  dsimp only
  simp only [pushC_memoK, unflatP_eq]
  have hx : (match (match (G.F.crA.getD b #[]).getD t none with
      | some r => slotB C G.F b r
      | none => none) with
      | some v => v + jf
      | none => 0) = (match (G.F.crA.getD b #[]).getD t none with
      | some r => K.slotRA C G.F b r jf
      | none => 0) := by
    cases (G.F.crA.getD b #[]).getD t none with
    | some r => exact slotB_eq C G.F b r jf
    | none => rfl
  rw [hx]
  cases ((G.F.tpls.getD b #[]).getD t default).op with
  | e2 f h =>
    cases f <;> cases h <;> simp only [pushT, List.foldl_cons, List.foldl_nil]
  | _ => rfl

/-- `auxPushA` with the `K` words from `M`. -/
def auxPushM (M : WM) (A : K.AC) (C : K.SC) (F : Lvm.Typed.K.FL) (k r j : ℕ) (a : Array (FE2 × ℕ)) :
    Array (FE2 × ℕ) :=
  let x := K.slotRA C F (F.bl.size + k) r j
  ((A.aux.getD k #[]).getD r default).ops.foldl (fun a e ↦
    match e.2.1 with
    | .word base stride => pushEnt a ⟨e.1, x, base + stride * j, e.2.2⟩
    | .cell c => pushC M A C F e.1 x a c.ty (c.at [j]) e.2.2
    | .one => pushEnt a ⟨e.1, x, F.lay.one, e.2.2⟩) a

theorem auxPushM_eq (A : K.AC) (C : K.SC) (G : K.FLF) (L N k r j : ℕ) (a : Array (FE2 × ℕ)) :
    auxPushM (memoK A C G.F L N) A C G.F k r j a = auxPushA A C G k r j a := by
  unfold auxPushM auxPushA
  dsimp only
  congr 1
  funext a e
  cases e.2.1 <;> simp only [pushC_memoK, pushT, List.foldl_cons, List.foldl_nil]

/-- `auxPushM` with the row's entries and slot search given. -/
def auxRowM (M : WM) (A : K.AC) (C : K.SC) (F : K.FL) (ops : List (ℕ × AOp × FE)) (xb : Option ℕ) (j : ℕ)
    (a : Array (FE2 × ℕ)) : Array (FE2 × ℕ) :=
  let x := match xb with
    | some v => v + j
    | none => 0
  ops.foldl (fun a e ↦
    match e.2.1 with
    | .word base stride => pushEnt a ⟨e.1, x, base + stride * j, e.2.2⟩
    | .cell c => pushC M A C F e.1 x a c.ty (c.at [j]) e.2.2
    | .one => pushEnt a ⟨e.1, x, F.lay.one, e.2.2⟩) a

theorem auxRowM_eq (M : WM) (A : K.AC) (C : K.SC) (F : K.FL) (k r j : ℕ) (a : Array (FE2 × ℕ)) :
    auxRowM M A C F ((A.aux.getD k #[]).getD r default).ops (slotB C F (F.bl.size + k) r) j a =
      auxPushM M A C F k r j a := by
  unfold auxRowM auxPushM
  rw [slotB_eq]

/-! ## All rows -/

/-- The keys of the row instances of `Q`'s blocks (`rowIsF`'s first part), as loops. -/
def blkPush (A : K.AC) (C : K.SC) (G : K.FLF) (ab : Array Block) (a : Array (FE2 × ℕ)) : Array (FE2 × ℕ) :=
  foldRange (fun a b =>
    let B := ab.getD b default
    foldRange (fun a t => foldRange (fun a jf => rowPushXA A C G b t jf a) 0 (2 ^ B.lsize) a) 0 B.tpl.length a)
    0 ab.size a

/-- The keys of the auxiliary row instances (`rowIsF`'s second part), as loops. -/
def auxPush (A : K.AC) (C : K.SC) (G : K.FLF) (ax : Array ABlk) (a : Array (FE2 × ℕ)) : Array (FE2 × ℕ) :=
  foldRange (fun a k =>
    let X := ax.getD k default
    foldRange (fun a r => foldRange (fun a j => auxPushA A C G k r j a) 0 (2 ^ X.l) a) 0 X.rows.length a)
    0 ax.size a

/-- `blkPush` on `RowD` and the word table. -/
def blkPushM (M : WM) (A : K.AC) (C : K.SC) (G : K.FLF) (ab : Array Block) (a : Array (FE2 × ℕ)) :
    Array (FE2 × ℕ) :=
  foldRange (fun a b =>
    let B := ab.getD b default
    foldRange (fun a t =>
      let D := RowD.of C G b t
      foldRange (fun a jf => rowPushXM M A C G.F D jf a) 0 (2 ^ B.lsize) a) 0 B.tpl.length a)
    0 ab.size a

/-- `auxPush` on the word table. -/
def auxPushW (M : WM) (A : K.AC) (C : K.SC) (G : K.FLF) (ax : Array ABlk) (a : Array (FE2 × ℕ)) :
    Array (FE2 × ℕ) :=
  foldRange (fun a k =>
    let X := ax.getD k default
    foldRange (fun a r =>
      let ops := ((A.aux.getD k #[]).getD r default).ops
      let xb := slotB C G.F (G.F.bl.size + k) r
      foldRange (fun a j => auxRowM M A C G.F ops xb j a) 0 (2 ^ X.l) a) 0 X.rows.length a)
    0 ax.size a

theorem blkPushM_eq (A : K.AC) (C : K.SC) (G : K.FLF) (L N : ℕ) (ab : Array Block) (a : Array (FE2 × ℕ)) :
    blkPushM (memoK A C G.F L N) A C G ab a = blkPush A C G ab a := by
  unfold blkPushM blkPush
  simp only [rowPushXM_eq]

theorem auxPushW_eq (A : K.AC) (C : K.SC) (G : K.FLF) (L N : ℕ) (ax : Array ABlk) (a : Array (FE2 × ℕ)) :
    auxPushW (memoK A C G.F L N) A C G ax a = auxPush A C G ax a := by
  unfold auxPushW auxPush
  simp only [auxRowM_eq, auxPushM_eq]

/-- **`rowsK`, fused**: on sorted chunk tables, the keys pushed in loops (the `K` words below the last `K` cell
read from a table); else `rowsK`. -/
def rowsKG (Q : Program) (lay : Lay) : Array (FE2 × ℕ) :=
  let G := flfOfLayG Q lay
  let C := K.SC.of G.F
  let A := K.AC.of G.F
  if C.okBL then
    let M := memoK A C G.F Q.nInK (G.F.stK.getD (G.F.stK.size - 1) 0)
    auxPushW M A C G lay.aux.toArray (blkPushM M A C G Q.blocks.toArray (Array.mkEmpty 3000000))
  else rowsK Q lay

theorem foldl_rowIsF (Q : Program) (lay : Lay) (A : K.AC) (C : K.SC) (G : K.FLF) (a : Array (FE2 × ℕ)) :
    (rowIsF Q lay).foldl (fun a r => (rawXA A C G r.1 r.2).foldl pushEnt a) a =
      auxPush A C G lay.aux.toArray (blkPush A C G Q.blocks.toArray a) := by
  unfold rowIsF auxPush blkPush
  simp only [List.foldl_append, List.foldl_flatMap, List.foldl_map, foldRange_eq, ← List.range_eq_range',
    ← rawPushA_eq]
  rfl

/-- **`rowsKG` is `rowsK`.** -/
theorem rowsKG_eq (Q : Program) (lay : Lay) : rowsKG Q lay = rowsK Q lay := by
  rw [← rowsKF_eq]
  unfold rowsKG rowsKF
  rw [flfOfLayG_eq]
  dsimp only
  split
  · simp only [pushL_split, blkPushM_eq, auxPushW_eq]
    rw [foldl_rowIsF]
    simp [Array.mkEmpty]
  · rfl

end Lvm6.V
