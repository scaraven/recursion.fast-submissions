-- New for lvm2 (roll 8 = B1, B1-S0 skeleton; B-DES §1.1, §1.3, §2; B1-P1P2 §1–§3): the four sparse matrices
-- `W, A, B, D` of a program and its typed layout, the wiring relation, `Φ_Q` (their multilinear extension in
-- 43 variables), the operand class data and the fast evaluator's interface. B1-K owns the evaluator `PhiQC`,
-- its cache and the class check; L-A proves `PhiQC_eq`.
import LvmWiringKD
import LvmWiringKC
import LvmFieldCorrect
import LvmFields

/-!
# The wiring of a typed program

B-DES §1.1: every constraint row of `Q` (`muladd`, `lin`, `assert0`, `fixmul`) is one slot `x`, and the
relation is, for every slot, `(A z)(x)·(B z)(x) + (D z)(x) + (W z)(x) = 0` in `E` (characteristic 2: signs do
not matter). The matrices are static functions of `(Q, lay)`:

| row | `A` | `B` | `D` | `W` |
|---|---|---|---|---|
| `muladd [a, b, d]` | `a` | `b` | `d` | result |
| `lin k k' [a, b]` | | | `a + k·b + k'·1` | result |
| `assert0 [a, gate]` | `gate` | `a` | | |
| `fixmul [a, d]` | | | `F(j)·a + d` | result |

An operand naming cell `n` of memory `τ` is its words through the layout (`cellEnts`: one for `K`; three limbs
with weights `1, y, y²` for `E`, a virtual `loadE` cell through its operands' words). `loadE` and `readd` rows
have no slot. Auxiliary blocks (`BITS` rows, B1-Q) add their own rows.

* `Ent`, `instEnts`, `auxEnts`, **`ents Q lay`**: the matrices' entries `(o, x, y, c)`;
* `matZ`, **`WiringRel Q lay z`**: the relation; `matMleF`: one matrix's extension at `(r_x, r_y)`;
* **`PhiQF Q lay`** (native) / **`PhiQ Q lay`** (over `E`): `Φ_Q(o, x, y)`, the sparse multilinear extension of
  the four matrices in `phiVars = 2 + 20 + 21 = 43` variables, `o` lowest (the selector), then `x`, then `y`;
* **the operand class data** (B1-P1P2 §2: K1, K2 with the last-dimension shift, K3 record reads, sub-cube splits,
  points) as `OpClass`, one `CTerm` per term of a row, and **the class check** `PhiCache.okB` against
  `Addr.at` (by enumeration here; B1-K's affine-identity check replaces it);
* **`PhiQC`** (the fast evaluator; stub: the brute-force sum over the cache) and **`PhiQC_eq`** (L-A).
-/

set_option autoImplicit false

namespace Lvm.Typed

open Lvm.Loop LeanVM.Parameters

/-! ## Entries -/

namespace Lay

variable (lay : Lay)

/-- **The words of cell `n` of memory `τ`**, weight `w`: one word for `K` (a constant cell: the word `1`, weight
`w·value`); the three limbs, weights `w, w·y, w·y²`, for `E`. -/
def cellEnts (τ : Ty) (n : ℕ) (w : FE) : List (ℕ × FE) :=
  match τ with
  | .K => match lay.cst? n with
    | some v => [(lay.one, w * FE.ofK v)]
    | none => [(lay.wordK n, w)]
  | .E => [(lay.wordE n 0, w), (lay.wordE n 1, w * FE.y), (lay.wordE n 2, w * FE.y * FE.y)]

/-- Operand `k` of instance `i`, weight `w`. -/
def argEnts (i : Inst) (k : ℕ) (w : FE) : List (ℕ × FE) :=
  lay.cellEnts (i.row.args.getD k default).ty ((i.row.args.getD k default).at i.j) w

/-- The result cell of instance `i`. -/
def resEnts (i : Inst) : List (ℕ × FE) := lay.cellEnts i.row.ty (i.clock i.row.ty) 1

/-- An auxiliary operand at iteration `j`, weight `w`. -/
def aopEnts (j : ℕ) (w : FE) : AOp → List (ℕ × FE)
  | .word base stride => [(base + stride * j, w)]
  | .cell a => lay.cellEnts a.ty (a.at [j]) w
  | .one => [(lay.one, w)]

end Lay

/-- **The entries of one instance** (the table above; `loadE` and `readd` have none). -/
def instEnts (Q : Program) (lay : Lay) (i : Inst) : List Ent :=
  let x := lay.slot i.blk i.t i.jf
  match i.row.op with
  | .muladd => tagE 0 x (lay.argEnts i 0 1) ++ tagE 1 x (lay.argEnts i 1 1) ++ tagE 2 x (lay.argEnts i 2 1) ++
      tagE 3 x (lay.resEnts i)
  | .lin k k' => tagE 2 x (lay.argEnts i 0 1 ++ lay.argEnts i 1 (FE.ofK k) ++ [(lay.one, FE.ofK k')]) ++
      tagE 3 x (lay.resEnts i)
  | .assert0 => tagE 0 x (lay.argEnts i 1 1) ++ tagE 1 x (lay.argEnts i 0 1)
  | .fixmul => tagE 2 x (lay.argEnts i 0 (FE.ofK (Q.fixMat i.j)) ++ lay.argEnts i 1 1) ++ tagE 3 x (lay.resEnts i)
  | _ => []

/-- The entries of template row `t` of block `b` at iteration `jf`. -/
def rowEnts (Q : Program) (lay : Lay) (b t jf : ℕ) : List Ent := instEnts Q lay (Q.inst b jf t)

/-- The entries of row `r` of auxiliary block `k` at iteration `j`. -/
def auxRowEnts (lay : Lay) (k r j : ℕ) : List Ent :=
  ((lay.aux.getD k default).rows.getD r default).ops.flatMap fun e ↦
    tagE e.1 (lay.auxSlot k r j) (lay.aopEnts j e.2.2 e.2.1)

/-- The auxiliary blocks' entries. -/
def auxEnts (lay : Lay) : List Ent :=
  (List.range lay.aux.length).flatMap fun k ↦
    (List.range (2 ^ (lay.aux.getD k default).l)).flatMap fun j ↦
      (List.range (lay.aux.getD k default).rows.length).flatMap fun r ↦ auxRowEnts lay k r j

/-- **The matrices' entries** of `(Q, lay)`: every instance's, then the auxiliary rows'. -/
def ents (Q : Program) (lay : Lay) : List Ent := Q.insts.flatMap (instEnts Q lay) ++ auxEnts lay

/-! ## The relation -/

/-- **`(M_o z)(x)`**: matrix `o`'s row `x` against the words `z`. -/
def matZ (Q : Program) (lay : Lay) (o : ℕ) (z : ℕ → FK) (x : ℕ) : FE :=
  ((ents Q lay).filter fun e ↦ e.o == o && e.x == x).foldr (fun e acc ↦ e.c * FE.ofK (z e.y) + acc) 0

/-- `(A z)(x)`. -/
abbrev matA (Q : Program) (lay : Lay) (z : ℕ → FK) (x : ℕ) : FE := matZ Q lay 0 z x
/-- `(B z)(x)`. -/
abbrev matB (Q : Program) (lay : Lay) (z : ℕ → FK) (x : ℕ) : FE := matZ Q lay 1 z x
/-- `(D z)(x)`. -/
abbrev matD (Q : Program) (lay : Lay) (z : ℕ → FK) (x : ℕ) : FE := matZ Q lay 2 z x
/-- `(W z)(x)`. -/
abbrev matW (Q : Program) (lay : Lay) (z : ℕ → FK) (x : ℕ) : FE := matZ Q lay 3 z x

/-- **The wiring relation** (B-DES §1.1): `A z·B z + D z + W z = 0` at every slot. -/
def WiringRel (Q : Program) (lay : Lay) (z : ℕ → FK) : Prop :=
  ∀ x, matA Q lay z x * matB Q lay z x + matD Q lay z x + matW Q lay z x = 0

/-! ## `Φ_Q` -/

/-- `Φ_Q`'s variables: the selector `o` (2), `x` (20), `y` (21). -/
abbrev phiVars : ℕ := 2 + xVars + yVars

/-- The sparse multilinear sum `Σ_e c_e · eq(pt, idx e)`. -/
def phiSum (es : List Ent) (pt : List FE) : FE := es.foldr (fun e acc ↦ e.c * eqW pt e.idx + acc) 0

/-- **`Φ_Q` natively** (the brute-force sparse evaluator, B1-P1P2 §3's reference): at a point of `phiVars`
coordinates (`o ++ x ++ y`). -/
def PhiQF (Q : Program) (lay : Lay) (pt : List FE) : FE := phiSum (ents Q lay) pt

/-- **`Φ_Q` over `E`**: the `E`-valued multilinear map in `43` variables (the accumulator's `Φ`). -/
def PhiQ (Q : Program) (lay : Lay) (pt : List E) : E := FE.toExt3 (PhiQF Q lay (pt.map FE.ofExt3))

/-- **Matrix `o`'s extension at `(r_x, r_y)`** (natively; `rxy = r_x ++ r_y`, 41 coordinates): the value the
prover sends as `v_o` (B-DES §1.2 step 2). -/
def matMleF (Q : Program) (lay : Lay) (o : ℕ) (rxy : List FE) : FE :=
  ((ents Q lay).filter fun e ↦ e.o == o).foldr (fun e acc ↦ e.c * eqW rxy (e.x + 2 ^ xVars * e.y) + acc) 0

/-- Matrix `o`'s extension over `E`. -/
def matMle (Q : Program) (lay : Lay) (o : ℕ) (rxy : List E) : E :=
  FE.toExt3 (matMleF Q lay o (rxy.map FE.ofExt3))

/-! ## The evaluator (classes in `LvmWiringKT`, fitting in `LvmWiringKD`, kernels in `LvmWiringK`, compiler in
`LvmWiringKC`) -/

/-- **The evaluator's cache** of `(Q, lay)`: the class data (the terms) and the compiled evaluator. -/
structure PhiCache where
  /-- The terms. -/
  terms : List CTerm
  /-- The compiled evaluator (`LvmWiringK.Comp`) of the terms. -/
  comp : K.Comp
  deriving Inhabited

/-- A row's entries at an iteration. -/
def srcEnts (Q : Program) (lay : Lay) : TSrc → ℕ → List Ent
  | .row b t, jf => rowEnts Q lay b t jf
  | .aux k r, j => auxRowEnts lay k r j

/-- `log₂` of a row's iterations. -/
def srcL (Q : Program) (lay : Lay) : TSrc → ℕ
  | .row b _ => (Q.blk b).lsize
  | .aux k _ => (lay.aux.getD k default).l

/-- The rows of `(Q, lay)`: template rows block by block, then the auxiliary rows. -/
def rowsOf (Q : Program) (lay : Lay) : List TSrc :=
  (List.range Q.blocks.length).flatMap (fun b ↦ (List.range (Q.blk b).tpl.length).map (TSrc.row b)) ++
    (List.range lay.aux.length).flatMap fun k ↦ (List.range (lay.aux.getD k default).rows.length).map (TSrc.aux k)

/-- A row's entry count (it does not depend on the iteration; `entCount_eq`). -/
def entCount (Q : Program) (lay : Lay) : TSrc → ℕ
  | .row b t => K.rowEntCount ((Q.blk b).tpl.getD t default)
  | .aux k r => K.auxEntCount (((lay.aux.getD k default).rows).getD r default)

/-- The canonical term keys: every row's entry positions. -/
def termKeys (Q : Program) (lay : Lay) : List (TSrc × ℕ) :=
  (rowsOf Q lay).flatMap fun s ↦ (List.range (entCount Q lay s)).map (s, ·)

/-- **The class check** (decidable, against `Addr.at` through the layout): the terms are the canonical keys in
order; every term has its row's iteration count, a matrix `o < 4` and aligned slots below `2^xVars`
(`K.TermWF`); every term is its row's entry at every iteration (the cover check: the keys; the class check:
the enumeration, on the layout's array caches `K.FL`, `K.checkTerms`; `rowEnts_eq` relates them to `srcEnts`).
Natively about `3·10^6` entry comparisons at P20; it belongs with A24's static facts. -/
def PhiCache.okB (Q : Program) (lay : Lay) (c : PhiCache) : Bool :=
  let ls := Q.blocks.toArray.map (·.lsize)
  let srcLF : TSrc → ℕ := fun
    | .row b _ => ls.getD b 0
    | .aux k _ => (lay.aux.getD k default).l
  c.terms.map (fun t ↦ (t.src, t.idx)) == termKeys Q lay &&
    c.terms.all (fun t ↦ t.l == srcLF t.src && K.termWFB t) &&
    K.checkTerms Q lay c.terms.toArray

/-- **The cache of `(Q, lay)`**: the terms fitted to the entries (`K.deriveTerms`), compiled
(`K.compileT`). -/
def cacheW (Q : Program) (lay : Lay) : PhiCache :=
  let ts := K.deriveTerms Q lay
  ⟨ts.toList, K.compileT ts⟩

/-- **The fast evaluator**: the compiled tables, atoms and carry-automaton passes (`K.evalC`). -/
def PhiQC (c : PhiCache) (pt : List FE) : FE := K.evalC c.comp pt

/-! # WP L-A: `rowEnts_eq`, `entCount_eq` (helpers `fl_`) -/

namespace K

/-! ## Loops of `FL.ofLay` -/

theorem fl_getD_ge {α : Type} (l : List α) (i : ℕ) (d : α) (h : l.length ≤ i) : l.getD i d = d := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none h]; rfl

theorem fl_psum_loop (L : List ℕ) (out : Array ℕ) (s : ℕ) :
    (forIn (m := Id) L (out, s) fun x (st : Array ℕ × ℕ) => pure (ForInStep.yield (st.1.push st.2, st.2 + x))) =
      ((out.toList ++ (List.range L.length).map fun i ↦ s + (L.take i).sum).toArray, s + L.sum) := by
  induction L generalizing out s with
  | nil => simp; rfl
  | cons x L ih =>
    rw [List.forIn_cons]
    refine (ih (out.push s) (s + x)).trans ?_
    refine Prod.ext ?_ (by simp [Nat.add_assoc])
    simp only [Array.toList_push, List.length_cons]
    rw [List.range_succ_eq_map]
    simp [Nat.add_assoc]

theorem fl_psumA_toList (xs : Array ℕ) (a : ℕ) :
    (psumA xs a).toList = (List.range (xs.size + 1)).map fun i ↦ a + (xs.toList.take i).sum := by
  rcases xs with ⟨L⟩
  unfold psumA
  simp only [Id.run, List.forIn_toArray]
  rw [fl_psum_loop]
  change (Array.push _ _).toList = _
  simp [List.range_succ]

theorem fl_psumA_getD (xs : Array ℕ) (a i : ℕ) (hi : i ≤ xs.size) :
    (psumA xs a).getD i 0 = a + (xs.toList.take i).sum := by
  have h1 : i < (psumA xs a).size := by
    rw [← Array.length_toList, fl_psumA_toList]; simp; omega
  rw [Array.getD_eq_getD_getElem?, Array.getElem?_eq_getElem h1, Option.getD_some, ← Array.getElem_toList]
  simp only [fl_psumA_toList, List.getElem_map, List.getElem_range]

theorem fl_forIn_push {α β : Type} (L : List α) (out : Array β) (P : α → Prop) [DecidablePred P] (g : α → β) :
    (forIn (m := Id) L out fun b s ↦ if P b then pure (ForInStep.yield (s.push (g b))) else pure (ForInStep.yield s)) =
      (out.toList ++ L.filterMap fun b ↦ if P b then some (g b) else none).toArray := by
  induction L generalizing out with
  | nil => simp; rfl
  | cons x L ih =>
    rw [List.forIn_cons]
    by_cases h : P x
    · simp only [h, ↓reduceIte]; refine (ih (out.push (g x))).trans ?_; simp [h]
    · simp only [h, ↓reduceIte]; refine (ih out).trans ?_; simp [h]


/-- The owner intervals of the layout's blocks (nonempty ones). -/
def fl_ownL (lay : Lay) (τ : Ty) : List (ℕ × ℕ × ℕ) :=
  (List.range lay.blocks.length).filterMap fun b ↦
    if (lay.blocks.getD b default).tw τ > 0 then
      some ((lay.blocks.getD b default).st τ,
        (lay.blocks.getD b default).st τ + (lay.blocks.getD b default).tw τ * 2 ^ (lay.blocks.getD b default).l, b)
    else none

theorem fl_ownK (Q : Program) (lay : Lay) : (FL.ofLay Q lay).ownK = (fl_ownL lay .K).toArray := by
  conv => lhs; simp only [FL.ofLay, Id.run, Std.Legacy.Range.forIn_eq_forIn_range', bind_pure]
  rw [fl_forIn_push]
  simp [fl_ownL, List.range_eq_range']

theorem fl_ownE (Q : Program) (lay : Lay) : (FL.ofLay Q lay).ownE = (fl_ownL lay .E).toArray := by
  conv => lhs; simp only [FL.ofLay, Id.run, Std.Legacy.Range.forIn_eq_forIn_range', bind_pure]
  rw [fl_forIn_push]
  simp [fl_ownL, List.range_eq_range']

theorem fl_owner?_ownL (lay : Lay) (τ : Ty) (n : ℕ) :
    lay.owner? τ n = ((fl_ownL lay τ).find? fun x ↦ decide (x.1 ≤ n ∧ n < x.2.1)).map (·.2.2) := by
  unfold Lay.owner? fl_ownL
  generalize List.range lay.blocks.length = L
  induction L with
  | nil => rfl
  | cons b L ih =>
    rw [List.filterMap_cons, List.find?_cons]
    by_cases h : (lay.blocks.getD b default).tw τ > 0
    · rw [ite_eq_left_of_eq_true _ _ (eq_true h), List.find?_cons]
      by_cases hq : (lay.blocks.getD b default).st τ ≤ n ∧
          n < (lay.blocks.getD b default).st τ + (lay.blocks.getD b default).tw τ * 2 ^ (lay.blocks.getD b default).l
      · rw [decide_eq_true hq]; rfl
      · rw [decide_eq_false hq]; exact ih
    · have h0 : (lay.blocks.getD b default).tw τ = 0 := by omega
      have hq : ¬ ((lay.blocks.getD b default).st τ ≤ n ∧
          n < (lay.blocks.getD b default).st τ + (lay.blocks.getD b default).tw τ * 2 ^ (lay.blocks.getD b default).l) := by
        rw [h0]; omega
      rw [ite_eq_right_of_eq_false _ _ (eq_false h), decide_eq_false hq]; exact ih

theorem fl_forIn_modify (N : ℕ) (L : List XChunk) (out : Array (Array XChunk)) (hN : out.size = N) :
    (forIn (m := Id) L out fun c s ↦
      if c.blk < N then pure (ForInStep.yield (s.modify c.blk fun x ↦ x.push c)) else pure (ForInStep.yield s)).size = N ∧
    ∀ b < N, ((forIn (m := Id) L out fun c s ↦
      if c.blk < N then pure (ForInStep.yield (s.modify c.blk fun x ↦ x.push c)) else pure (ForInStep.yield s)).getD b #[]).toList =
      (out.getD b #[]).toList ++ L.filter (·.blk == b) := by
  induction L generalizing out with
  | nil => exact ⟨hN, fun b _ ↦ by simp; rfl⟩
  | cons c L ih =>
    rw [List.forIn_cons]
    by_cases h : c.blk < N
    · simp only [h, ↓reduceIte]
      obtain ⟨ih1, ih2⟩ := ih (out.modify c.blk fun x ↦ x.push c) (by simp [hN])
      refine ⟨ih1, fun b hb ↦ (ih2 b hb).trans ?_⟩
      by_cases hcb : c.blk = b
      · subst hcb; simp [Array.getD_eq_getD_getElem?, hN, h, Array.getElem_modify_self]
      · simp [Array.getD_eq_getD_getElem?, Array.getElem?_modify, hcb]
    · simp only [h, ↓reduceIte]
      obtain ⟨ih1, ih2⟩ := ih out hN
      refine ⟨ih1, fun b hb ↦ (ih2 b hb).trans ?_⟩
      have : (c.blk == b) = false := by simp; omega
      simp [this]

theorem fl_xch (Q : Program) (lay : Lay) (b : ℕ) (hb : b < lay.blocks.length + lay.aux.length) :
    ((FL.ofLay Q lay).xch.getD b #[]).toList = lay.xs.filter (·.blk == b) := by
  conv => lhs; simp only [FL.ofLay, Id.run, bind_pure]
  rw [(fl_forIn_modify _ lay.xs _ (by simp)).2 b (by simpa using hb)]
  simp [Array.getD_eq_getD_getElem?, hb]


/-! ## The owner search -/

def fl_bsLoop (a : Array (ℕ × ℕ × ℕ)) (n lo0 hi0 g0 : ℕ) : Option ℕ := Id.run do
  let mut lo := lo0
  let mut hi := hi0
  let mut guard := g0
  while lo < hi && guard > 0 do
    let mid := (lo + hi) / 2
    let (l, h, b) := a.getD mid (0, 0, 0)
    if n < l then hi := mid
    else if n ≥ h then lo := mid + 1
    else return some b
    guard := guard - 1
  return none

theorem fl_owner_bs (F : FL) (τ : Ty) (n : ℕ) :
    F.owner τ n = fl_bsLoop (if τ == .K then F.ownK else F.ownE) n 0 (if τ == .K then F.ownK else F.ownE).size
      ((if τ == .K then F.ownK else F.ownE).size + 1) := rfl

theorem fl_loop_unfold {β : Type} (b : β) (f : Unit → β → Id (ForInStep β)) :
    forIn (m := Id) Lean.Loop.mk b f =
      (match f () b with | .done v => pure v | .yield v => forIn (m := Id) Lean.Loop.mk v f) := by
  show Lean.Loop.forIn _ _ _ = _
  rw [Lean.Loop.forIn_eq_of_monadTail]
  rfl

theorem fl_bsLoop_eq (a : Array (ℕ × ℕ × ℕ)) (n lo hi g : ℕ) : fl_bsLoop a n lo hi g =
    if lo < hi ∧ 0 < g then
      (if n < (a.getD ((lo + hi) / 2) (0, 0, 0)).1 then fl_bsLoop a n lo ((lo + hi) / 2) (g - 1)
       else if (a.getD ((lo + hi) / 2) (0, 0, 0)).2.1 ≤ n then fl_bsLoop a n ((lo + hi) / 2 + 1) hi (g - 1)
       else some (a.getD ((lo + hi) / 2) (0, 0, 0)).2.2)
    else none := by
  have hg : a.getD ((lo + hi) / 2) (0, 0, 0) =
      (if h : (lo + hi) / 2 < a.size then a.getInternal ((lo + hi) / 2) h else (0, 0, 0)) := rfl
  rw [hg]
  conv_lhs => unfold fl_bsLoop
  dsimp only [Id.run]
  rw [fl_loop_unfold]
  dsimp only
  generalize (if h : (lo + hi) / 2 < a.size then a.getInternal ((lo + hi) / 2) h else (0, 0, 0)) = p
  obtain ⟨l, h, b⟩ := p
  by_cases h1 : lo < hi ∧ 0 < g
  · have h1' : (decide (lo < hi) && decide (g > 0)) = true := by simp [h1.1, h1.2]
    rw [ite_eq_left_of_eq_true _ _ (eq_true h1), ite_eq_left_of_eq_true _ _ (eq_true h1')]
    by_cases h2 : n < l
    · rw [ite_eq_left_of_eq_true _ _ (eq_true h2), ite_eq_left_of_eq_true _ _ (eq_true h2)]; rfl
    · rw [ite_eq_right_of_eq_false _ _ (eq_false h2), ite_eq_right_of_eq_false _ _ (eq_false h2)]
      by_cases h3 : h ≤ n
      · rw [ite_eq_left_of_eq_true _ _ (eq_true h3), ite_eq_left_of_eq_true _ _ (eq_true (show n ≥ h from h3))]; rfl
      · rw [ite_eq_right_of_eq_false _ _ (eq_false h3), ite_eq_right_of_eq_false _ _ (eq_false (show ¬ n ≥ h from h3))]; rfl
  · have h1' : (decide (lo < hi) && decide (g > 0)) = false := by
      simp only [Bool.and_eq_false_iff, decide_eq_false_iff_not]; omega
    rw [ite_eq_right_of_eq_false _ _ (eq_false h1), ite_eq_right_of_eq_false _ _ (by simp [h1'])]
    rfl

/-- The binary search finds the first interval holding `n` on sorted, disjoint intervals. -/
theorem fl_bsLoop_spec (a : Array (ℕ × ℕ × ℕ)) (n : ℕ) (hs : a.toList.Pairwise fun x y ↦ x.2.1 ≤ y.1)
    (hw : ∀ x ∈ a.toList, x.1 ≤ x.2.1) :
    fl_bsLoop a n 0 a.size (a.size + 1) = (a.toList.find? fun x ↦ decide (x.1 ≤ n ∧ n < x.2.1)).map (·.2.2) := by
  have hs' : ∀ i j (hij : i < j) (hj : j < a.size), a[i].2.1 ≤ a[j].1 := by
    intro i j hij hj
    have := List.pairwise_iff_getElem.mp hs i j (by simp; omega) (by simpa using hj) hij
    simpa using this
  have hw' : ∀ i (hi : i < a.size), a[i].1 ≤ a[i].2.1 := fun i hi ↦ hw _ (by simp)
  -- the holder of `n` is unique
  have huniq : ∀ i j (hi : i < a.size) (hj : j < a.size), a[i].1 ≤ n → n < a[i].2.1 → a[j].1 ≤ n →
      n < a[j].2.1 → i = j := by
    intro i j hi hj h1 h2 h3 h4
    rcases Nat.lt_trichotomy i j with h | h | h
    · have := hs' i j h hj; omega
    · exact h
    · have := hs' j i h hi; omega
  suffices H : ∀ g lo hi, hi ≤ a.size → hi - lo < g →
      (∀ i (h : i < a.size), a[i].1 ≤ n → n < a[i].2.1 → lo ≤ i ∧ i < hi) →
      fl_bsLoop a n lo hi g = (a.toList.find? fun x ↦ decide (x.1 ≤ n ∧ n < x.2.1)).map (·.2.2) from
    H _ _ _ le_rfl (by omega) (fun i h _ _ ↦ ⟨Nat.zero_le _, h⟩)
  intro g
  induction g with
  | zero => intro lo hi _ h; omega
  | succ g ih =>
    intro lo hi hhi hg hinv
    rw [fl_bsLoop_eq]
    by_cases h1 : lo < hi
    · rw [ite_eq_left_of_eq_true _ _ (eq_true ⟨h1, Nat.succ_pos g⟩)]
      have hm : (lo + hi) / 2 < a.size := by omega
      have hlm : lo ≤ (lo + hi) / 2 := by omega
      have hmh : (lo + hi) / 2 < hi := by omega
      rw [Array.getD_eq_getD_getElem?, Array.getElem?_eq_getElem hm, Option.getD_some, Nat.add_sub_cancel]
      by_cases h2 : n < a[(lo + hi) / 2].1
      · rw [ite_eq_left_of_eq_true _ _ (eq_true h2)]
        refine ih _ _ (by omega) (by omega) fun i hi' h3 h4 ↦ ⟨(hinv i hi' h3 h4).1, ?_⟩
        by_contra hc
        rcases Nat.lt_or_ge ((lo + hi) / 2) i with h5 | h5
        · have := hs' _ _ h5 hi'; have := hw' _ hm; omega
        · have : i = (lo + hi) / 2 := by omega
          subst this; omega
      · rw [ite_eq_right_of_eq_false _ _ (eq_false h2)]
        by_cases h3 : a[(lo + hi) / 2].2.1 ≤ n
        · rw [ite_eq_left_of_eq_true _ _ (eq_true h3)]
          refine ih _ _ hhi (by omega) fun i hi' h4 h5 ↦ ⟨?_, (hinv i hi' h4 h5).2⟩
          by_contra hc
          rcases Nat.lt_or_ge i ((lo + hi) / 2) with h6 | h6
          · have := hs' _ _ h6 hm; have := hw' _ hm; omega
          · have : i = (lo + hi) / 2 := by omega
            subst this; omega
        · rw [ite_eq_right_of_eq_false _ _ (eq_false h3)]
          have hP : a[(lo + hi) / 2].1 ≤ n ∧ n < a[(lo + hi) / 2].2.1 := ⟨by omega, by omega⟩
          have : a.toList.find? (fun x ↦ decide (x.1 ≤ n ∧ n < x.2.1)) = some a[(lo + hi) / 2] := by
            rw [List.find?_eq_some_iff_getElem]
            refine ⟨by simpa using hP, (lo + hi) / 2, by simpa using hm, by simp, fun j hj ↦ ?_⟩
            have hj' : j < a.size := by omega
            simp only [Array.getElem_toList, Bool.not_eq_eq_eq_not, Bool.not_true, decide_eq_false_iff_not]
            intro hc
            have := huniq _ _ hj' hm hc.1 hc.2 hP.1 hP.2
            omega
          rw [this]; rfl
    · rw [ite_eq_right_of_eq_false _ _ (eq_false fun h ↦ h1 h.1)]
      symm
      rw [Option.map_eq_none_iff, List.find?_eq_none]
      intro x hx
      obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.mp hx
      have hi' : i < a.size := by simpa using hi
      simp only [Array.getElem_toList, decide_eq_true_eq]
      intro hc
      have := hinv i hi' hc.1 hc.2
      omega


/-- `blocksOk` makes the blocks' cell ranges consecutive: each block's range ends before the next ones start. -/
theorem fl_blocksOk_chain (nInK : ℕ) (xs : List XChunk) (τ : Ty) :
    ∀ (Bs : List BLay) (Bqs : List Block) (b sK sE : ℕ), blocksOk nInK xs b sK sE Bs Bqs = true →
      (∀ B ∈ Bs, (match τ with | .K => sK | .E => sE) ≤ B.st τ) ∧
        Bs.Pairwise fun B B' ↦ B.st τ + B.tw τ * 2 ^ B.l ≤ B'.st τ := by
  intro Bs
  induction Bs with
  | nil => intro _ _ _ _ _; exact ⟨by simp, List.Pairwise.nil⟩
  | cons B Bs ih =>
    intro Bqs b sK sE h
    cases Bqs with
    | nil => simp [blocksOk] at h
    | cons Bq Bqs =>
      simp only [blocksOk, Bool.and_eq_true, beq_iff_eq] at h
      obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨hd, hK⟩, hE⟩, htK⟩, htE⟩, -⟩, -⟩, -⟩, -⟩, hrest⟩ := h
      obtain ⟨ih1, ih2⟩ := ih Bqs _ _ _ hrest
      have hl : 2 ^ B.l = Bq.size := by simp [BLay.l, Block.size, Block.lsize, hd]
      refine ⟨?_, List.Pairwise.cons ?_ ih2⟩
      · intro B' hB'
        rcases List.mem_cons.mp hB' with rfl | hB'
        · cases τ <;> simp [BLay.st, hK, hE]
        · have := ih1 B' hB'
          cases τ <;> simp only [BLay.st] at this ⊢ <;> omega
      · intro B' hB'
        have := ih1 B' hB'
        cases τ <;> simp only [BLay.st, BLay.tw, hl] at this ⊢ <;> omega

theorem fl_ownL_sorted (Q : Program) (lay : Lay) (hlay : lay.Ok Q) (τ : Ty) :
    (fl_ownL lay τ).Pairwise fun x y ↦ x.2.1 ≤ y.1 := by
  have hb : blocksOk lay.nInK lay.xs 0 Q.nInK Q.nInE lay.blocks Q.blocks = true := by
    have h := hlay
    simp only [Lay.Ok, Lay.okB, Bool.and_eq_true] at h
    exact h.1.1.1.1.1.1.1.2
  have hp := (fl_blocksOk_chain _ _ τ _ _ _ _ _ hb).2
  rw [List.pairwise_iff_getElem] at hp
  unfold fl_ownL
  refine List.Pairwise.filterMap (R := fun i j ↦ i < j ∧ j < lay.blocks.length) _ ?_ ?_
  · intro i j ⟨hij, hj⟩ x hx y hy
    split at hx <;> split at hy <;> simp only [Option.some.injEq, reduceCtorEq] at hx hy
    subst hx hy
    have := hp i j (by omega) hj hij
    simpa [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hj, List.getElem?_eq_getElem (show i < lay.blocks.length by omega)] using this
  · exact (List.pairwise_lt_range).imp_of_mem fun _ hb h ↦ ⟨h, List.mem_range.mp hb⟩

theorem fl_ownL_wf (lay : Lay) (τ : Ty) : ∀ x ∈ fl_ownL lay τ, x.1 ≤ x.2.1 := by
  intro x hx
  simp only [fl_ownL, List.mem_filterMap] at hx
  obtain ⟨b, -, hb⟩ := hx
  split at hb <;> simp only [Option.some.injEq, reduceCtorEq] at hb
  subst hb; simp


section
variable (Q : Program) (lay : Lay)

/-! ## The caches -/

theorem fl_bl_getD (b : ℕ) : (FL.ofLay Q lay).bl.getD b default = lay.blocks.getD b default := by
  simp [FL.ofLay, Array.getD_eq_getD_getElem?, List.getD_eq_getElem?_getD]

theorem fl_qb_getD (b : ℕ) : (FL.ofLay Q lay).qb.getD b default = Q.blk b := by
  simp [FL.ofLay, Program.blk, Array.getD_eq_getD_getElem?, List.getD_eq_getElem?_getD]

theorem fl_srcKA_getD (b i : ℕ) (d : CSrc) :
    ((FL.ofLay Q lay).srcKA.getD b #[]).getD i d = (lay.blocks.getD b default).srcK.getD i d := by
  simp only [FL.ofLay, Array.getD_eq_getD_getElem?, List.getD_eq_getElem?_getD, Array.getElem?_map,
    List.getElem?_toArray]
  cases lay.blocks[b]? with
  | none => rfl
  | some B => simp

theorem fl_srcEA_getD (b i : ℕ) (d : CSrc) :
    ((FL.ofLay Q lay).srcEA.getD b #[]).getD i d = (lay.blocks.getD b default).srcE.getD i d := by
  simp only [FL.ofLay, Array.getD_eq_getD_getElem?, List.getD_eq_getElem?_getD, Array.getElem?_map,
    List.getElem?_toArray]
  cases lay.blocks[b]? with
  | none => rfl
  | some B => simp

theorem fl_crA_getD (b t : ℕ) :
    ((FL.ofLay Q lay).crA.getD b #[]).getD t none = (lay.blocks.getD b default).cr.getD t none := by
  simp only [FL.ofLay, Array.getD_eq_getD_getElem?, List.getD_eq_getElem?_getD, Array.getElem?_map,
    List.getElem?_toArray]
  cases lay.blocks[b]? with
  | none => rfl
  | some B => simp

theorem fl_tpls_getD (b t : ℕ) :
    ((FL.ofLay Q lay).tpls.getD b #[]).getD t default = (Q.blk b).tpl.getD t default := by
  simp only [FL.ofLay, Program.blk, Array.getD_eq_getD_getElem?, List.getD_eq_getElem?_getD, Array.getElem?_map,
    List.getElem?_toArray]
  cases Q.blocks[b]? with
  | none => rfl
  | some B => simp

theorem fl_cst (n : ℕ) : (FL.ofLay Q lay).cst n = lay.cst? n := by
  simp only [FL.cst, Lay.cst?, FL.ofLay, List.find?_toArray, List.find?_map, Option.map_map]
  congr 1
  funext r; simp

theorem fl_dreg (τ : Ty) (n : ℕ) : (FL.ofLay Q lay).dreg τ n = lay.dreg? τ n := by
  simp only [FL.dreg, Lay.dreg?, FL.ofLay, List.find?_toArray]

theorem fl_wordD (τ : Ty) (n m : ℕ) : (FL.ofLay Q lay).wordD τ n m = lay.wordD τ n m := by
  unfold FL.wordD Lay.wordD; rw [fl_dreg]; rfl

theorem fl_wordC (B : BLay) (τ : Ty) (n s jf m : ℕ) :
    (FL.ofLay Q lay).wordC B τ n s jf m = lay.wordC B τ n s jf m := by
  unfold FL.wordC Lay.wordC; rw [fl_dreg]; rfl


theorem fl_owner_eq (hlay : lay.Ok Q) (τ : Ty) (n : ℕ) : (FL.ofLay Q lay).owner τ n = lay.owner? τ n := by
  rw [fl_owner_bs, fl_owner?_ownL]
  cases τ
  · rw [show (Ty.K == Ty.K) = true from rfl, ite_eq_left_of_eq_true _ _ (eq_self _), fl_ownK,
      fl_bsLoop_spec _ _ (by simpa using fl_ownL_sorted Q lay hlay .K) (by simpa using fl_ownL_wf lay .K)]
  · rw [show (Ty.E == Ty.K) = false from rfl, ite_eq_right_of_eq_false _ _ (eq_false Bool.false_ne_true), fl_ownE,
      fl_bsLoop_spec _ _ (by simpa using fl_ownL_sorted Q lay hlay .E) (by simpa using fl_ownL_wf lay .E)]

theorem fl_wordK (hlay : lay.Ok Q) (n : ℕ) : (FL.ofLay Q lay).wordK n = lay.wordK n := by
  unfold FL.wordK Lay.wordK
  rw [fl_owner_eq Q lay hlay]
  cases lay.owner? .K n with
  | none => exact fl_wordD Q lay _ _ _
  | some b =>
    simp only [fl_bl_getD, fl_srcKA_getD, fl_wordC, fl_wordD]
    rfl

theorem fl_wordE (hlay : lay.Ok Q) (n m : ℕ) : (FL.ofLay Q lay).wordE n m = lay.wordE n m := by
  unfold FL.wordE Lay.wordE
  rw [fl_owner_eq Q lay hlay]
  cases lay.owner? .E n with
  | none => exact fl_wordD Q lay _ _ _
  | some b =>
    simp only [fl_bl_getD, fl_srcEA_getD, fl_wordC, fl_wordK Q lay hlay]
    rfl

theorem fl_cellEnts (hlay : lay.Ok Q) : (FL.ofLay Q lay).cellEnts = lay.cellEnts := by
  funext τ n w
  cases τ
  · simp only [FL.cellEnts, Lay.cellEnts, fl_cst, fl_wordK Q lay hlay]; rfl
  · simp only [FL.cellEnts, Lay.cellEnts, fl_wordE Q lay hlay]

theorem fl_slotR (b r jf : ℕ) (hb : b < lay.blocks.length + lay.aux.length) :
    (FL.ofLay Q lay).slotR b r jf = lay.slotR b r jf := by
  unfold FL.slotR Lay.slotR Lay.xchunk?
  rw [← Array.find?_toList, fl_xch Q lay b hb, List.find?_filter]
  have : (fun c : XChunk ↦ decide ((c.blk == b) = true ∧ decide (c.r0 ≤ r ∧ r < c.r0 + c.n) = true)) =
      fun c ↦ c.blk == b && decide (c.r0 ≤ r ∧ r < c.r0 + c.n) := by
    funext c; by_cases h : c.blk = b <;> simp [h]
  rw [this]
  rfl

theorem fl_stK (b : ℕ) (hb : b ≤ Q.blocks.length) : (FL.ofLay Q lay).stK.getD b 0 = Q.start .K b := by
  simp only [FL.ofLay]
  rw [fl_psumA_getD _ _ _ (by simpa using hb)]
  simp [Program.start, Program.nIn, List.map_take]

theorem fl_stE (b : ℕ) (hb : b ≤ Q.blocks.length) : (FL.ofLay Q lay).stE.getD b 0 = Q.start .E b := by
  simp only [FL.ofLay]
  rw [fl_psumA_getD _ _ _ (by simpa using hb)]
  simp [Program.start, Program.nIn, List.map_take]

theorem fl_rkK (b t : ℕ) (hb : b < Q.blocks.length) (ht : t ≤ (Q.blk b).tpl.length) :
    ((FL.ofLay Q lay).rkK.getD b #[]).getD t 0 = (Q.blk b).rank .K t := by
  have hq : Q.blk b = Q.blocks[b] := by simp [Program.blk, List.getD_eq_getElem?_getD, hb]
  rw [hq] at ht ⊢
  simp only [FL.ofLay, Array.getD_eq_getD_getElem?, Array.getElem?_map, List.getElem?_toArray,
    List.getElem?_eq_getElem hb, Option.map_some, Option.getD_some]
  rw [← Array.getD_eq_getD_getElem?, fl_psumA_getD _ _ _ (by simpa using ht)]
  simp [Block.rank, List.map_take]

theorem fl_rkE (b t : ℕ) (hb : b < Q.blocks.length) (ht : t ≤ (Q.blk b).tpl.length) :
    ((FL.ofLay Q lay).rkE.getD b #[]).getD t 0 = (Q.blk b).rank .E t := by
  have hq : Q.blk b = Q.blocks[b] := by simp [Program.blk, List.getD_eq_getElem?_getD, hb]
  rw [hq] at ht ⊢
  simp only [FL.ofLay, Array.getD_eq_getD_getElem?, Array.getElem?_map, List.getElem?_toArray,
    List.getElem?_eq_getElem hb, Option.map_some, Option.getD_some]
  rw [← Array.getD_eq_getD_getElem?, fl_psumA_getD _ _ _ (by simpa using ht)]
  simp [Block.rank, List.map_take]

theorem fl_cellEnts_app (hlay : lay.Ok Q) (τ : Ty) (n : ℕ) (w : FE) :
    (FL.ofLay Q lay).cellEnts τ n w = lay.cellEnts τ n w := by
  rw [fl_cellEnts Q lay hlay]

theorem fl_lay : (FL.ofLay Q lay).lay = lay := rfl

theorem fl_Q : (FL.ofLay Q lay).Q = Q := rfl

theorem fl_bl_size : (FL.ofLay Q lay).bl.size = lay.blocks.length := by simp [FL.ofLay]

end

end K

/-- **The cached entries are the entries** (statement): on a checked layout. Owner L-A. -/
theorem rowEnts_eq (Q : Program) (lay : Lay) (hlay : lay.Ok Q) (s : TSrc) (jf : ℕ) :
    (K.FL.ofLay Q lay).srcEnts s jf = srcEnts Q lay s jf := by
  cases s with
  | row b t =>
    unfold K.FL.srcEnts srcEnts rowEnts K.FL.rowEnts instEnts Lay.slot
    simp only [K.fl_qb_getD, K.fl_tpls_getD, K.fl_crA_getD, K.fl_cellEnts_app Q lay hlay, K.fl_lay, K.fl_Q,
      Program.inst, Lay.argEnts, Lay.resEnts]
    have hsl : ∀ r, (lay.blocks.getD b default).cr.getD t none = some r →
        (K.FL.ofLay Q lay).slotR b r jf = lay.slotR b r jf := by
      intro r hr
      refine K.fl_slotR Q lay b r jf ?_
      by_contra hb
      rw [K.fl_getD_ge lay.blocks b default (by omega)] at hr
      cases hr
    have hbd : ((Q.blk b).tpl.getD t default).op ≠ .assert0 → b < Q.blocks.length ∧ t < (Q.blk b).tpl.length := by
      intro h
      by_contra hc
      apply h
      by_cases ht : t < (Q.blk b).tpl.length
      · have hb : ¬ b < Q.blocks.length := fun hb ↦ hc ⟨hb, ht⟩
        have : Q.blk b = default := K.fl_getD_ge Q.blocks b default (by omega)
        rw [this] at ht; cases ht
      · rw [K.fl_getD_ge _ t default (by omega)]; rfl
    have hck : ((Q.blk b).tpl.getD t default).op ≠ .assert0 →
        (K.FL.ofLay Q lay).stK.getD b 0 + (Q.blk b).tw Ty.K * jf + ((K.FL.ofLay Q lay).rkK.getD b #[]).getD t 0 =
          Q.start .K b + (Q.blk b).tw .K * jf + (Q.blk b).rank .K t := by
      intro h
      obtain ⟨hb, ht⟩ := hbd h
      rw [K.fl_stK Q lay b hb.le, K.fl_rkK Q lay b t hb ht.le]
    have hce : ((Q.blk b).tpl.getD t default).op ≠ .assert0 →
        (K.FL.ofLay Q lay).stE.getD b 0 + (Q.blk b).tw Ty.E * jf + ((K.FL.ofLay Q lay).rkE.getD b #[]).getD t 0 =
          Q.start .E b + (Q.blk b).tw .E * jf + (Q.blk b).rank .E t := by
      intro h
      obtain ⟨hb, ht⟩ := hbd h
      rw [K.fl_stE Q lay b hb.le, K.fl_rkE Q lay b t hb ht.le]
    clear hbd
    generalize hc : (lay.blocks.getD b default).cr.getD t none = c at hsl
    generalize (Q.blk b).tpl.getD t default = row at hck hce
    obtain ⟨op, ty, args⟩ := row
    rcases c with _ | r
    · cases op <;> cases ty <;> simp only [Inst.clock, ne_eq, reduceCtorEq, not_false_eq_true, hck, hce]
    · cases op <;> cases ty <;> simp only [Inst.clock, ne_eq, reduceCtorEq, not_false_eq_true, hck, hce, hsl r rfl]
  | aux k r =>
    unfold K.FL.srcEnts srcEnts auxRowEnts K.FL.auxEnts Lay.auxSlot
    simp only [K.fl_cellEnts_app Q lay hlay, K.fl_lay, K.fl_bl_size]
    by_cases hk : k < lay.aux.length
    · rw [K.fl_slotR Q lay _ r jf (by omega)]
      congr 1
    · rw [K.fl_getD_ge lay.aux k default (by omega)]
      rfl

theorem fl_cellEnts_length (lay : Lay) (τ : Ty) (n : ℕ) (w : FE) : (lay.cellEnts τ n w).length = τ.limbs := by
  cases τ
  · simp only [Lay.cellEnts]; split <;> rfl
  · rfl

/-- **A row's entry count does not depend on the iteration** (statement). Owner L-A. -/
theorem entCount_eq (Q : Program) (lay : Lay) (s : TSrc) (jf : ℕ) :
    (srcEnts Q lay s jf).length = entCount Q lay s := by
  cases s with
  | row b t =>
    unfold srcEnts rowEnts entCount instEnts K.rowEntCount
    simp only [Program.inst, Lay.argEnts, Lay.resEnts]
    generalize (Q.blk b).tpl.getD t default = row
    obtain ⟨op, ty, args⟩ := row
    cases op <;> simp [tagE, fl_cellEnts_length] <;> omega
  | aux k r =>
    unfold srcEnts auxRowEnts entCount K.auxEntCount
    rw [List.length_flatMap]
    congr 1
    apply List.map_congr_left
    intro e _
    obtain ⟨o, op, w⟩ := e
    cases op <;> simp [tagE, Lay.aopEnts, fl_cellEnts_length]

/-! ## Helpers for `PhiQC_eq` (prefix `phi_`) -/

theorem phi_id_bind {α β : Type} (x : Id α) (f : α → Id β) : x >>= f = f x := rfl

theorem phi_loop_inv {β : Type} (f : Unit → β → Id (ForInStep β)) (P R : β → Prop) (μ : β → ℕ)
    (hstep : ∀ b, P b → (∀ v, f () b = .done v → R v) ∧ (∀ v, f () b = .yield v → P v ∧ μ v < μ b)) :
    ∀ b, P b → R (forIn (m := Id) Lean.Loop.mk b f) := by
  intro b
  induction h : μ b using Nat.strong_induction_on generalizing b with
  | _ n ih =>
    intro hb
    change R (Lean.Loop.forIn Lean.Loop.mk b f)
    rw [Lean.Loop.forIn_eq_of_monadTail]
    obtain ⟨h1, h2⟩ := hstep b hb
    cases hf : f () b with
    | done v => exact h1 v hf
    | yield v =>
      obtain ⟨hv, hμ⟩ := h2 v hf
      exact ih (μ v) (h ▸ hμ) v rfl hv

theorem phi_forIn_early {α : Type} (l : List α)
    (f : α → Option Bool × Unit → Id (ForInStep (Option Bool × Unit)))
    (hf : ∀ a ∈ l, f a (none, ()) = .yield (none, ()) ∨ f a (none, ()) = .done (some false, ())) :
    ((forIn (m := Id) l (none, ()) f).1 = none → ∀ a ∈ l, f a (none, ()) = .yield (none, ())) ∧
      (forIn (m := Id) l (none, ()) f).1 ≠ some true := by
  induction l with
  | nil => simp
  | cons a l ih =>
    have ih' := ih fun a' ha' => hf a' (List.mem_cons_of_mem a ha')
    rw [List.forIn_cons]
    rcases hf a List.mem_cons_self with h | h
    · rw [h]
      refine ⟨fun hn a' ha' => ?_, ih'.2⟩
      rcases List.mem_cons.1 ha' with rfl | ha'
      · exact h
      · exact ih'.1 hn a' ha'
    · rw [h]
      refine ⟨fun hn => ?_, fun hn => ?_⟩ <;> cases hn

theorem phi_forIn_early' {α : Type} (l : List α)
    (f : α → Option Bool × Unit → Id (ForInStep (Option Bool × Unit))) (G : α → Prop) (C : Prop)
    (hC : (∀ a ∈ l, G a) → C)
    (hf : ∀ a ∈ l, (f a (none, ()) = .yield (none, ()) ∧ G a) ∨ f a (none, ()) = .done (some false, ())) :
    ((forIn (m := Id) l (none, ()) f).1 = none → C) ∧ (forIn (m := Id) l (none, ()) f).1 ≠ some true := by
  have h := phi_forIn_early l f fun a ha => (hf a ha).imp And.left id
  refine ⟨fun hn => hC fun a ha => ?_, h.2⟩
  rcases hf a ha with h' | h'
  · exact h'.2
  · have := h.1 hn a ha
    rw [h'] at this
    cases this

theorem phi_checkTerms (Q : Program) (lay : Lay) (ts : Array CTerm)
    (hl : ∀ k k', k < ts.size → k' < ts.size → (ts.getD k default).src = (ts.getD k' default).src →
      (ts.getD k default).l = (ts.getD k' default).l)
    (h : K.checkTerms Q lay ts = true) :
    ∀ k < ts.size, ∀ jf < 2 ^ (ts.getD k default).l,
      ((K.FL.ofLay Q lay).srcEnts (ts.getD k default).src jf).toArray.getD (ts.getD k default).idx default =
        (ts.getD k default).at jf := by
  unfold K.checkTerms at h
  dsimp only [Id.run] at h
  generalize hR : (forIn (m := Id) Lean.Loop.mk ((none : Option Bool), (0 : ℕ)) _) = R at h
  have hpost : (R.1 = none → ∀ k < ts.size, ∀ jf < 2 ^ (ts.getD k default).l,
      ((K.FL.ofLay Q lay).srcEnts (ts.getD k default).src jf).toArray.getD (ts.getD k default).idx default =
        (ts.getD k default).at jf) ∧ R.1 ≠ some true := by
    rw [← hR]
    refine phi_loop_inv _ (fun s : Option Bool × ℕ => s.1 = none ∧ s.2 ≤ ts.size ∧ ∀ k < s.2, ∀ jf < 2 ^ (ts.getD k default).l,
      ((K.FL.ofLay Q lay).srcEnts (ts.getD k default).src jf).toArray.getD (ts.getD k default).idx default =
        (ts.getD k default).at jf)
      (fun s : Option Bool × ℕ => (s.1 = none → ∀ k < ts.size, ∀ jf < 2 ^ (ts.getD k default).l,
      ((K.FL.ofLay Q lay).srcEnts (ts.getD k default).src jf).toArray.getD (ts.getD k default).idx default =
        (ts.getD k default).at jf) ∧ s.1 ≠ some true) (fun s : Option Bool × ℕ => ts.size - s.2) ?_ _ ⟨rfl, Nat.zero_le _, by simp⟩
    rintro ⟨o, i⟩ ⟨ho, hi, hgood⟩
    dsimp only at ho hi hgood ⊢
    subst ho
    by_cases hlt : i < ts.size
    · rw [ite_eq_left hlt]
      simp only [phi_id_bind]
      generalize hJd : (forIn (m := Id) Lean.Loop.mk i _) = J
      obtain ⟨J, rfl⟩ : ∃ J' : ℕ, J' = J := ⟨J, rfl⟩
      have hJ : i < J ∧ J ≤ ts.size ∧
          ∀ k, i ≤ k → k < J → (ts.getD k default).src = (ts.getD i default).src := by
        rw [← hJd]
        refine phi_loop_inv _ (fun j : ℕ => i ≤ j ∧ j ≤ ts.size ∧
            ∀ k, i ≤ k → k < j → (ts.getD k default).src = (ts.getD i default).src)
          (fun j : ℕ => i < j ∧ j ≤ ts.size ∧
            ∀ k, i ≤ k → k < j → (ts.getD k default).src = (ts.getD i default).src)
          (fun j => ts.size - j) ?_ i ⟨le_rfl, hi, fun k h1 h2 => absurd h2 (by omega)⟩
        rintro j ⟨h1, h2, h3⟩
        by_cases hc : (decide (j < ts.size) && (ts.getD j default).src == (ts.getD i default).src) = true
        · rw [ite_eq_left hc]
          simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at hc
          refine ⟨fun v hv => (by cases hv), fun v hv => ?_⟩
          cases hv
          refine ⟨⟨by omega, by omega, fun k hk1 hk2 => ?_⟩, by omega⟩
          rcases Nat.lt_succ_iff_lt_or_eq.1 hk2 with hk | rfl
          · exact h3 k hk1 hk
          · exact hc.2
        · rw [ite_eq_right hc]
          refine ⟨fun v hv => ?_, fun v hv => by cases hv⟩
          cases hv
          refine ⟨?_, h2, h3⟩
          rcases Nat.lt_or_eq_of_le h1 with h | rfl
          · exact h
          · exact absurd (by simp [hlt]) hc
      generalize hSd : (forIn (m := Id) [:2 ^ (ts.getD i default).l] ((none : Option Bool), ()) _) = S
      obtain ⟨S, rfl⟩ : ∃ S' : Option Bool × Unit, S' = S := ⟨S, rfl⟩
      have hS : (S.1 = none → ∀ jf < 2 ^ (ts.getD i default).l, ∀ k, i ≤ k → k < J →
          ((K.FL.ofLay Q lay).srcEnts (ts.getD i default).src jf).toArray.getD (ts.getD k default).idx default =
            (ts.getD k default).at jf) ∧ S.1 ≠ some true := by
        rw [← hSd, Std.Legacy.Range.forIn_eq_forIn_range']
        refine phi_forIn_early' _ _ (fun jf => ∀ k, i ≤ k → k < J →
          ((K.FL.ofLay Q lay).srcEnts (ts.getD i default).src jf).toArray.getD (ts.getD k default).idx default =
            (ts.getD k default).at jf) _ (fun H jf hjf => H jf (List.mem_range'_1.2 ⟨Nat.zero_le _, by simp only [Std.Legacy.Range.size]; omega⟩)) ?_
        intro jf _
        generalize hKd : (forIn (m := Id) [i:J] ((none : Option Bool), ()) _) = KR
        obtain ⟨KR, rfl⟩ : ∃ K' : Option Bool × Unit, K' = KR := ⟨KR, rfl⟩
        have hK : (KR.1 = none → ∀ k, i ≤ k → k < J →
            ((K.FL.ofLay Q lay).srcEnts (ts.getD i default).src jf).toArray.getD (ts.getD k default).idx default =
              (ts.getD k default).at jf) ∧ KR.1 ≠ some true := by
          rw [← hKd, Std.Legacy.Range.forIn_eq_forIn_range']
          refine phi_forIn_early' _ _ (fun k =>
            ((K.FL.ofLay Q lay).srcEnts (ts.getD i default).src jf).toArray.getD (ts.getD k default).idx default =
              (ts.getD k default).at jf) _
            (fun H k hk1 hk2 => H k (List.mem_range'_1.2 ⟨hk1, by simp only [Std.Legacy.Range.size]; omega⟩)) ?_
          intro k _
          by_cases hc : (!((K.FL.ofLay Q lay).srcEnts (ts.getD i default).src jf).toArray.getD
              (ts.getD k default).idx default == (ts.getD k default).at jf) = true
          · rw [ite_eq_left hc]; right; rfl
          · rw [ite_eq_right hc]
            left
            exact ⟨rfl, by simpa using hc⟩
        obtain ⟨o', u⟩ := KR
        cases o' with
        | none => exact Or.inl ⟨rfl, hK.1 rfl⟩
        | some r =>
          cases r
          · exact Or.inr rfl
          · exact absurd rfl hK.2
      obtain ⟨o'', u⟩ := S
      cases o'' with
      | none =>
        refine ⟨fun v hv => (by cases hv), fun v hv => ?_⟩
        cases hv
        refine ⟨⟨rfl, hJ.2.1, fun k hk jf hjf => ?_⟩, by dsimp only; omega⟩
        by_cases hki : k < i
        · exact hgood k hki jf hjf
        · have hsrc := hJ.2.2 k (by omega) hk
          have hlk := hl k i (by omega) hlt hsrc
          rw [hsrc]
          exact hS.1 rfl jf (hlk ▸ hjf) k (by omega) hk
      | some r =>
        refine ⟨fun v hv => ?_, fun v hv => by cases hv⟩
        cases hv
        exact ⟨fun hn => (by cases hn), hS.2⟩
    · rw [ite_eq_right hlt]
      refine ⟨fun v hv => ?_, fun v hv => ?_⟩
      · cases hv
        exact ⟨fun _ k hk => hgood k (by omega), by simp⟩
      · cases hv
  obtain ⟨o, n⟩ := R
  cases o with
  | none => exact hpost.1 rfl
  | some r =>
    cases r
    · change false = true at h
      cases h
    · exact absurd rfl hpost.2

theorem phi_foldr_eq_sum {α : Type} (f : α → FE) (l : List α) :
    l.foldr (fun x acc => f x + acc) 0 = (l.map f).sum := by
  induction l with
  | nil => rfl
  | cons a l ih => simp [List.foldr_cons, ih]

theorem phi_sum_flatMap {α β : Type} (l : List α) (f : α → List β) (h : β → FE) :
    ((l.flatMap f).map h).sum = (l.map fun a => ((f a).map h).sum).sum := by
  induction l with
  | nil => rfl
  | cons a l ih => simp [List.flatMap_cons, List.map_append, List.sum_append, ih]

theorem phi_sum_comm (m n : ℕ) (f : ℕ → ℕ → FE) :
    ((List.range m).map fun a => ((List.range n).map fun b => f a b).sum).sum =
      ((List.range n).map fun b => ((List.range m).map fun a => f a b).sum).sum := by
  induction m with
  | zero => simp
  | succ m ih => simp only [List.sum_range_succ, ih, List.sum_map_add]

theorem phi_sum_getD {α : Type} [Inhabited α] (l : List α) (h : α → FE) :
    ((List.range l.length).map fun i => h (l.getD i default)).sum = (l.map h).sum := by
  induction l with
  | nil => rfl
  | cons a l ih =>
    rw [List.length_cons, List.range_succ_eq_map, List.map_cons, List.map_map, List.sum_cons, List.map_cons,
      List.sum_cons, ← ih]
    rfl

theorem phi_tplInsts (b jf : ℕ) (j : List ℕ) : ∀ (rs : List Row) (t k e : ℕ),
    tplInsts b jf j t k e rs = (List.range rs.length).map fun m =>
      (⟨b, jf, j, t + m, rs.getD m default, k + ((rs.take m).map (Row.w .K)).sum,
        e + ((rs.take m).map (Row.w .E)).sum⟩ : Inst)
  | [], _, _, _ => rfl
  | r :: rs, t, k, e => by
    rw [tplInsts, phi_tplInsts b jf j rs, List.length_cons, List.range_succ_eq_map]
    simp only [List.map_cons, List.map_map]
    congr 1
    apply List.map_congr_left
    intro m _
    simp only [Function.comp, List.getD_cons_succ, List.take_succ_cons, List.map_cons, List.sum_cons,
      Inst.mk.injEq, true_and]
    refine ⟨by omega, by omega, by omega⟩

theorem phi_insts (Q : Program) : Q.insts = (List.range Q.blocks.length).flatMap fun b =>
    (List.range (2 ^ (Q.blk b).lsize)).flatMap fun jf => (List.range (Q.blk b).tpl.length).map (Q.inst b jf) := by
  unfold Program.insts Program.blockInsts
  congr 1; funext b; congr 1; funext jf
  rw [phi_tplInsts]
  apply List.map_congr_left
  intro m _
  simp only [Program.inst, Block.rank, Nat.zero_add]

theorem phi_phiSum (es : List Ent) (pt : List FE) :
    phiSum es pt = (es.map fun e => e.c * eqW pt e.idx).sum := by
  unfold phiSum
  exact phi_foldr_eq_sum (α := Ent) (fun e : Ent => e.c * eqW pt e.idx) es

theorem phi_termSum (t : CTerm) (pt : List FE) :
    K.termSum t pt = ((List.range (2 ^ t.l)).map (K.termAt t pt)).sum := by
  unfold K.termSum
  exact phi_foldr_eq_sum (K.termAt t pt) _

theorem phi_termSum_eq (Q : Program) (lay : Lay) (hlay : lay.Ok Q) (t : CTerm) (pt : List FE)
    (hl : t.l = srcL Q lay t.src)
    (hg : ∀ jf < 2 ^ t.l, ((K.FL.ofLay Q lay).srcEnts t.src jf).toArray.getD t.idx default = t.at jf) :
    K.termSum t pt = ((List.range (2 ^ srcL Q lay t.src)).map fun jf =>
      ((srcEnts Q lay t.src jf).getD t.idx default).c *
        eqW pt ((srcEnts Q lay t.src jf).getD t.idx default).idx).sum := by
  rw [phi_termSum, ← hl]
  congr 1
  apply List.map_congr_left
  intro jf hjf
  have hw : t.wAt jf = (t.at jf).c := rfl
  rw [K.termAt, hw, ← hg jf (List.mem_range.1 hjf), rowEnts_eq Q lay hlay, Array.getD_eq_getD_getElem?, List.getElem?_toArray,
    List.getD_eq_getElem?_getD]

theorem phi_sum_keys (Q : Program) (lay : Lay) (ts : List CTerm) (F : TSrc → ℕ → FE)
    (hkeys : ts.map (fun t => (t.src, t.idx)) = termKeys Q lay) :
    (ts.map fun t => F t.src t.idx).sum =
      ((rowsOf Q lay).map fun s => ((List.range (entCount Q lay s)).map (F s)).sum).sum := by
  have : (ts.map fun t => F t.src t.idx) = (ts.map fun t => (t.src, t.idx)).map fun p => F p.1 p.2 := by
    rw [List.map_map]; rfl
  rw [this, hkeys, termKeys, phi_sum_flatMap]
  simp only [List.map_map, Function.comp_def]

theorem phi_row_swap (Q : Program) (lay : Lay) (pt : List FE) (s : TSrc) :
    ((List.range (entCount Q lay s)).map fun i => ((List.range (2 ^ srcL Q lay s)).map fun jf =>
      ((srcEnts Q lay s jf).getD i default).c * eqW pt ((srcEnts Q lay s jf).getD i default).idx).sum).sum =
    ((List.range (2 ^ srcL Q lay s)).map fun jf =>
      ((srcEnts Q lay s jf).map fun e => e.c * eqW pt e.idx).sum).sum := by
  rw [phi_sum_comm (entCount Q lay s) (2 ^ srcL Q lay s) fun i jf =>
      ((srcEnts Q lay s jf).getD i default).c * eqW pt ((srcEnts Q lay s jf).getD i default).idx]
  apply congrArg
  apply List.map_congr_left
  intro jf _
  rw [← entCount_eq Q lay s jf]
  exact phi_sum_getD (srcEnts Q lay s jf) fun e => e.c * eqW pt e.idx

theorem phi_rows_sum (Q : Program) (lay : Lay) (pt : List FE) :
    ((rowsOf Q lay).map fun s => ((List.range (2 ^ srcL Q lay s)).map fun jf =>
      ((srcEnts Q lay s jf).map fun e => e.c * eqW pt e.idx).sum).sum).sum = PhiQF Q lay pt := by
  unfold PhiQF ents rowsOf auxEnts
  simp only [phi_phiSum, List.map_append, List.sum_append, phi_sum_flatMap, phi_insts, List.map_map,
    Function.comp_def, srcL, srcEnts, rowEnts]
  congr 1
  · apply congrArg
    apply List.map_congr_left
    intro b _
    exact phi_sum_comm _ _ _
  · apply congrArg
    apply List.map_congr_left
    intro k _
    exact phi_sum_comm _ _ _

theorem phi_getD_mem (ts : Array CTerm) (k : ℕ) (hk : k < ts.size) : ts.getD k default ∈ ts.toList := by
  rw [Array.getD_eq_getD_getElem?, Array.getElem?_eq_getElem hk]
  simp

theorem phi_mem_getD (ts : Array CTerm) (t : CTerm) (ht : t ∈ ts.toList) :
    ∃ k < ts.size, ts.getD k default = t := by
  obtain ⟨k, hk, rfl⟩ := List.mem_iff_getElem.1 ht
  refine ⟨k, by simpa using hk, ?_⟩
  rw [Array.getD_eq_getD_getElem?, Array.getElem?_eq_getElem (by simpa using hk)]
  simp

theorem phi_termWF (t : CTerm) (h : K.termWFB t = true) : K.TermWF t := by
  simp only [K.termWFB, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at h
  exact ⟨h.1.1, h.1.2, h.2⟩

theorem phi_lsize_getD (Q : Program) (b : ℕ) :
    (Array.map (fun x => x.lsize) Q.blocks.toArray).getD b 0 = (Q.blk b).lsize := by
  rw [Array.getD_eq_getD_getElem?, Program.blk, List.getD_eq_getElem?_getD]
  simp only [Array.getElem?_map, List.getElem?_toArray]
  cases Q.blocks[b]? <;> rfl

/-- **The fast evaluator is `Φ_Q`** (B-DES §2, as `lvmTabsC_eq` today): on a checked layout and a checked
cache, at every point of `phiVars` coordinates. Owner **L-A** (with B1-K's evaluator and check). -/
theorem PhiQC_eq (Q : Program) (lay : Lay) (hlay : lay.Ok Q) (hc : (cacheW Q lay).okB Q lay = true)
    (pt : List FE) (hpt : pt.length = phiVars) :
    PhiQC (cacheW Q lay) pt = PhiQF Q lay pt := by
  have hc' := hc
  unfold PhiCache.okB cacheW at hc'
  simp only [Bool.and_eq_true, beq_iff_eq, List.all_eq_true, Array.toArray_toList] at hc'
  obtain ⟨⟨hkeys, hall⟩, hchk⟩ := hc'
  have hl : ∀ t ∈ (K.deriveTerms Q lay).toList, t.l = srcL Q lay t.src := by
    intro t ht
    have h := (hall t ht).1
    revert h
    cases t.src with
    | row b r => intro h; rw [h]; exact phi_lsize_getD Q b
    | aux k r => intro h; exact h
  have hwf : ∀ t ∈ K.deriveTerms Q lay, K.TermWF t := fun t ht =>
    phi_termWF t (hall t (Array.mem_toList_iff.2 ht)).2
  have hg := phi_checkTerms Q lay (K.deriveTerms Q lay)
    (fun k k' hk hk' hs => by
      rw [hl _ (phi_getD_mem _ k hk), hl _ (phi_getD_mem _ k' hk'), hs]) hchk
  show K.evalC (K.compileT (K.deriveTerms Q lay)) pt = _
  rw [K.compileT_eq (K.deriveTerms Q lay) hwf pt hpt]
  rw [List.map_congr_left fun t ht => phi_termSum_eq Q lay hlay t pt (hl t ht) (by
    obtain ⟨k, hk, rfl⟩ := phi_mem_getD _ t ht
    exact hg k hk)]
  rw [phi_sum_keys Q lay _ (fun s i => ((List.range (2 ^ srcL Q lay s)).map fun jf =>
      ((srcEnts Q lay s jf).getD i default).c * eqW pt ((srcEnts Q lay s jf).getD i default).idx).sum) hkeys]
  simp only [phi_row_swap]
  exact phi_rows_sum Q lay pt

end Lvm.Typed
