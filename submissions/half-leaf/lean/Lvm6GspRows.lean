-- New for lvm6 (GSP, guard speed): the template-row counts without lists, and `Lay.okB`'s run-time twin on them.
-- `Block.tw` maps every row through `Row.w` (an `Option` equality) and sums the list: 215 ms for `tw .K` over the
-- deployed program's 282,742 template rows, where one pass that matches the row costs about 20 ms. `okB` takes
-- `tw .K`, `tw .E` and `nCon` of every block; `auxOk` recomputes `2^l` per operand; `cstOk` the constant regions'
-- lengths per alias target. The twins here count by matching, in one accumulated pass. No statement changes.
import Lvm6LayOkF

/-!
# Row counts in one pass, and `okBH` (`Lay.okB`)

* `wF τ r` (`Row.w` by matching; **`wF_eq`**), `twF τ B` (**`twF_eq : twF τ B = B.tw τ`**), `nConF B`
  (**`nConF_eq`**), `cntF B` (the three in one pass; **`cntF_eq`**), `cellsF Q τ` (**`cellsF_eq : cellsF Q τ = Q.cells τ`**).
* `tplOkH` (**`tplOkH_eq`**: `tplOk` with the constraint-rank test and `srcOk`'s `slot` case by matching).
* `blocksOkH`, `auxOkH`, `cstOkH`: `blocksOkF`, `auxOkF`, `cstOk` with those counts and `tplOkH`, `2^l - 1` once per auxiliary
  block, the constant regions as `(start, length)`; each equal to its original.
* **`okBH_eq : okBH lay Q = lay.okB Q`**.
-/

set_option autoImplicit false

namespace Lvm6.Gsp

open Lvm.Loop Lvm.Typed

/-! ## Counts -/

/-- `Row.w τ r` by matching on the row. -/
def wF (τ : Ty) (r : Row) : ℕ :=
  match r.op, r.ty, τ with
  | .assert0, _, _ => 0
  | _, .K, .K => 1
  | _, .E, .E => 1
  | _, _, _ => 0

theorem wF_eq (τ : Ty) (r : Row) : wF τ r = r.w τ := by
  obtain ⟨op, ty, args⟩ := r
  cases op <;> cases ty <;> cases τ <;> simp [wF, Row.w, Row.writes]

/-- `Σ wF τ` over the rows, accumulated. -/
def twGo (τ : Ty) : List Row → ℕ → ℕ
  | [], a => a
  | r :: rs, a => twGo τ rs (a + wF τ r)

theorem twGo_eq (τ : Ty) : ∀ (rs : List Row) (a : ℕ), twGo τ rs a = a + (rs.map (Row.w τ)).sum
  | [], a => by simp [twGo]
  | r :: rs, a => by
    rw [twGo, twGo_eq τ rs, wF_eq, List.map_cons, List.sum_cons, Nat.add_assoc]

/-- **`Block.tw` in one pass.** -/
def twF (τ : Ty) (B : Block) : ℕ := twGo τ B.tpl 0

theorem twF_eq (τ : Ty) (B : Block) : twF τ B = B.tw τ := by
  rw [twF, twGo_eq, Nat.zero_add, Block.tw]

theorem twF_fun (τ : Ty) : twF τ = fun B ↦ B.tw τ := funext (twF_eq τ)

/-- The constraint rows, counted. -/
def conGo : List Row → ℕ → ℕ
  | [], a => a
  | r :: rs, a => conGo rs (if Row.isCon r then a + 1 else a)

theorem conGo_eq : ∀ (rs : List Row) (a : ℕ), conGo rs a = a + (rs.filter Row.isCon).length
  | [], a => by simp [conGo]
  | r :: rs, a => by
    rw [conGo, conGo_eq rs, List.filter_cons]
    split <;> simp [Nat.add_assoc, Nat.add_comm 1]

/-- **`nCon` in one pass.** -/
def nConF (B : Block) : ℕ := conGo B.tpl 0

theorem nConF_eq (B : Block) : nConF B = nCon B := by
  rw [nConF, conGo_eq, Nat.zero_add, nCon]

/-- `(tw .K, tw .E, nCon)` of a template in one pass. -/
def cntGo : List Row → ℕ → ℕ → ℕ → ℕ × ℕ × ℕ
  | [], a, b, c => (a, b, c)
  | r :: rs, a, b, c => cntGo rs (a + wF .K r) (b + wF .E r) (if Row.isCon r then c + 1 else c)

theorem cntGo_eq : ∀ (rs : List Row) (a b c : ℕ), cntGo rs a b c = (twGo .K rs a, twGo .E rs b, conGo rs c)
  | [], _, _, _ => rfl
  | r :: rs, a, b, c => by
    rw [cntGo, twGo, twGo, conGo]
    exact cntGo_eq rs _ _ _

/-- **A block's counts in one pass**: `(tw .K, tw .E, nCon)`. -/
def cntF (B : Block) : ℕ × ℕ × ℕ := cntGo B.tpl 0 0 0

theorem cntF_eq (B : Block) : cntF B = (B.tw .K, B.tw .E, nCon B) := by
  rw [cntF, cntGo_eq, ← twF, ← twF, ← nConF, twF_eq, twF_eq, nConF_eq]

/-- The cells the blocks write, accumulated. -/
def startGo (τ : Ty) : List Block → ℕ → ℕ
  | [], a => a
  | B :: Bs, a => startGo τ Bs (a + twF τ B * B.size)

theorem startGo_eq (τ : Ty) :
    ∀ (Bs : List Block) (a : ℕ), startGo τ Bs a = a + (Bs.map fun B ↦ B.tw τ * B.size).sum
  | [], a => by simp [startGo]
  | B :: Bs, a => by
    rw [startGo, startGo_eq τ Bs, twF_eq, List.map_cons, List.sum_cons, Nat.add_assoc]

/-- **`Program.cells` in one pass.** -/
def cellsF (Q : Program) (τ : Ty) : ℕ := startGo τ Q.blocks (Q.nIn τ)

theorem cellsF_eq (Q : Program) (τ : Ty) : cellsF Q τ = Q.cells τ := by
  rw [cellsF, startGo_eq, Program.cells, Program.start, List.take_length]

/-! ## `okB` -/

/-- `c == (if isC then some rC else none)` by matching. -/
def conOk (c : Option ℕ) (isC : Bool) (rC : ℕ) : Bool :=
  match c, isC with
  | some x, true => x == rC
  | none, false => true
  | _, _ => false

theorem conOk_eq (c : Option ℕ) (isC : Bool) (rC : ℕ) : conOk c isC rC = (c == if isC then some rC else none) := by
  cases c <;> cases isC <;> simp [conOk]

/-- A `loadE` operation. -/
def isLoadE : Op → Bool
  | .loadE => true
  | _ => false

theorem isLoadE_eq (o : Op) : (o.kind != .loadE) = !isLoadE o := by
  rcases o with _ | _ | _ | _ | _ | _ | ⟨f, h⟩
  all_goals try rfl
  cases f <;> rfl

/-- `srcOk`, the `slot` case by `isLoadE`. -/
def srcOkH (r : Row) (size nInK : ℕ) : CSrc → Bool
  | .slot _ => !isLoadE r.op
  | s => srcOk r size nInK s

theorem srcOkH_eq (r : Row) (size nInK : ℕ) (s : CSrc) : srcOkH r size nInK s = srcOk r size nInK s := by
  cases s <;> simp only [srcOkH, srcOk, isLoadE_eq]

/-- `tplOk` with `conOk`, `srcOkH`. -/
def tplOkH (size nInK : ℕ) : List Row → List (Option ℕ) → List CSrc → List CSrc → ℕ → Bool
  | [], cr, sK, sE, _ => cr.isEmpty && sK.isEmpty && sE.isEmpty
  | _ :: _, [], _, _, _ => false
  | r :: rs, c :: cr, sK, sE, rC =>
    let isC := Row.isCon r
    let okC := conOk c isC rC
    let rC' := if isC then rC + 1 else rC
    match r.writes, sK, sE with
    | some .K, s :: sK', _ => okC && srcOkH r size nInK s && tplOkH size nInK rs cr sK' sE rC'
    | some .E, _, s :: sE' => okC && srcOkH r size nInK s && tplOkH size nInK rs cr sK sE' rC'
    | none, _, _ => okC && tplOkH size nInK rs cr sK sE rC'
    | _, _, _ => false

theorem tplOkH_eq (size nInK : ℕ) : ∀ (rs : List Row) (cr : List (Option ℕ)) (sK sE : List CSrc) (rC : ℕ),
    tplOkH size nInK rs cr sK sE rC = tplOk size nInK rs cr sK sE rC
  | [], _, _, _, _ => rfl
  | _ :: _, [], _, _, _ => rfl
  | r :: rs, c :: cr, sK, sE, rC => by
    simp only [tplOkH, tplOk, conOk_eq, srcOkH_eq, tplOkH_eq size nInK rs]
    rfl

/-- `blocksOkF` with the counts in one pass. -/
def blocksOkH (nInK : ℕ) (G : ℕ → List XChunk) : ℕ → ℕ → ℕ → List BLay → List Block → Bool
  | _, _, _, [], [] => true
  | b, sK, sE, B :: Bs, Bq :: Bqs =>
    let c := cntF Bq
    B.dims == Bq.dims && B.stK == sK && B.stE == sE && B.twK == c.1 && B.twE == c.2.1 &&
      tplOkH Bq.size nInK Bq.tpl B.cr B.srcK B.srcE 0 &&
      B.chK.all (chFits B.l .K) && B.chE.all (chFits B.l .E) &&
      chunksCover B.l (G b) 0 c.2.2 &&
      blocksOkH nInK G (b + 1) (sK + B.twK * Bq.size) (sE + B.twE * Bq.size) Bs Bqs
  | _, _, _, _, _ => false

theorem blocksOkH_eq (nInK : ℕ) (G : ℕ → List XChunk) : ∀ (b sK sE : ℕ) (Bs : List BLay) (Bqs : List Block),
    blocksOkH nInK G b sK sE Bs Bqs = blocksOkF nInK G b sK sE Bs Bqs
  | _, _, _, [], [] => rfl
  | b, sK, sE, B :: Bs, Bq :: Bqs => by
    simp only [blocksOkH, blocksOkF, blocksOkH_eq nInK G (b + 1) _ _ Bs Bqs, cntF_eq, tplOkH_eq]
  | _, _, _, [], _ :: _ => rfl
  | _, _, _, _ :: _, [] => rfl

/-- `aopFits l` with `m = 2^l - 1` given. -/
def aopFitsM (m : ℕ) : AOp → Bool
  | .word base stride => decide (base + stride * m < 2 ^ yVars)
  | _ => true

theorem aopFitsM_eq (l : ℕ) (o : AOp) : aopFitsM (2 ^ l - 1) o = aopFits l o := by
  cases o <;> rfl

/-- `auxOkF`, `2^l - 1` once per block. -/
def auxOkH (G : ℕ → List XChunk) : ℕ → List ABlk → Bool
  | _, [] => true
  | k, A :: As =>
    (let m := 2 ^ A.l - 1
     A.rows.all fun r ↦ r.ops.all fun e ↦ decide (e.1 < 4) && aopFitsM m e.2.1) &&
      chunksCover A.l (G k) 0 A.rows.length && auxOkH G (k + 1) As

theorem auxOkH_eq (G : ℕ → List XChunk) : ∀ (k : ℕ) (As : List ABlk), auxOkH G k As = auxOkF G k As
  | _, [] => rfl
  | k, A :: As => by simp only [auxOkH, auxOkF, aopFitsM_eq, auxOkH_eq G (k + 1) As]

/-- `cstMiss` on the regions' `(start, length)`. -/
def cstMissL (cl : List (ℕ × ℕ)) (lo hi : ℕ) : Bool := cl.all fun r ↦ hi < r.1 || r.1 + r.2 ≤ lo

theorem cstMissL_eq (cst : List (ℕ × List Lvm.FK)) (lo hi : ℕ) :
    cstMissL (cst.map fun r ↦ (r.1, r.2.length)) lo hi = cstMiss cst lo hi := by
  simp only [cstMissL, cstMiss, List.all_map, Function.comp_def]

/-- `cstOk`, the regions' lengths once, `loadE` by matching. -/
def cstOkH (cst : List (ℕ × List Lvm.FK)) (nInK : ℕ) (blocks : List BLay) (Qb : List Block) : Bool :=
  let cl := cst.map fun r ↦ (r.1, r.2.length)
  cl.all (fun r ↦ decide (r.1 + r.2 ≤ nInK)) &&
    (Qb.all fun B ↦ B.tpl.all fun r ↦ !isLoadE r.op || r.args.all fun a ↦
      cstMissL cl a.base (a.base + dot a.strides (B.dims.map fun d ↦ 2 ^ d - 1))) &&
    blocks.all fun B ↦ B.srcK.all fun s ↦ match s with
      | .alias tgt => tgt.all fun n ↦ cstMissL cl n n
      | _ => true

theorem cstOkH_eq (cst : List (ℕ × List Lvm.FK)) (nInK : ℕ) (blocks : List BLay) (Qb : List Block) :
    cstOkH cst nInK blocks Qb = cstOk cst nInK blocks Qb := by
  simp only [cstOkH, cstOk, ← cstMissL_eq, isLoadE_eq, List.all_map, Function.comp_def]
  rfl

/-- **`Lay.okB`, the counts in one pass** (the chunks grouped once, as `okBF`). -/
def okBH (lay : Lay) (Q : Program) : Bool :=
  let G := grpX lay.xs
  lay.nInK == Q.nInK && lay.nInE == Q.nInE && lay.blocks.length == Q.blocks.length &&
    blocksOkH lay.nInK (fun k ↦ G.getD k []) 0 Q.nInK Q.nInE lay.blocks Q.blocks &&
    auxOkH (fun k ↦ G.getD k []) lay.blocks.length lay.aux &&
    xsSorted lay.xs && yregsSorted lay.yregs &&
    lay.inp.all dregFits && lay.dense.all dregFits && decide (lay.one < 2 ^ yVars) &&
    cstOkH lay.cst lay.nInK lay.blocks Q.blocks

theorem okBH_eq (lay : Lay) (Q : Program) : okBH lay Q = lay.okB Q := by
  rw [← Lay.okBF_eq]
  simp only [okBH, Lay.okBF, Lay.okBG, blocksOkH_eq, auxOkH_eq, cstOkH_eq]

end Lvm6.Gsp
