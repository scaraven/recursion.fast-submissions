-- New for `flock-recursive` (PACK-4.4.1 §4.2, §5.2; IMP-RESULT §5.5; track ASK-P): the ask templates'
-- rows as a fold along the compile's trail, below `FRNodeRows4`, so that the node's M rows can hold them.
import FRVIRTplBuild
import FRNodeRows4AskStmt
import FRNodeRows4ArenaPlace
import FRVerifierC4

/-!
# Row generators along the compile's trail (the ask templates' rows, foldable into `nodeIRows4`)

B3's ask template `FRNodeRun4.AT` is a pair (`cov`, `rows`) and its rows are the fold `askRowsX`
along the compile's trail. Both live above `FRNodeRows4` (they import the soundness chain), so the
node's M rows cannot name them. This module restates the pair (**`TG`**) and the fold
(**`trailRows`**, `askRowsX` verbatim; `FRNodeRows4AskPosF.askRowsX_eq` proves them equal), so that
`FRNodeRows4` folds the node's template rows (`askTG`, `askRowsT`) into each slot's arena rows.

* **`trailMS`**: the same fold with the plan's template memo (`FRVIRTplBuild.compMSX`'s), accumulated
  in reverse (tail-recursive): the process start computes the rows once per prototype without
  rebuilding a template per op. **`trailMS_eq`**: it is `trailRows` (reversed onto the accumulator).
* **`inpTG X π`**: IMP's `input` template (`FRNodeRows4AskInp.AT.inp`, its rows `inpRowsT`), as a
  generator. Today's node template is it alone (`FRNodeRows4.askTG`); the other classes (ASK-T,
  IMPC) are added to `askTG` there (`TG.add`).
-/

namespace FR
namespace Rev4
open RecursionFast Circ TEval Tpl

/-- **A row generator along the trail** (B3's `AT`: the ops it covers besides the asks, and its rows
at a compile state, the previous op and the ask counter). -/
structure TG where
  cov : Op → Bool
  rows : Params → CS → Option Op → Op → ℕ → List Row

/-- The generator with no rows, covering nothing (`AT.none`). -/
def TG.none : TG := ⟨fun _ => false, fun _ _ _ _ _ => []⟩

/-- Two generators side by side (`AT.add`). -/
def TG.add (A B : TG) : TG :=
  ⟨fun op => A.cov op || B.cov op, fun P cs pre op k => A.rows P cs pre op k ++ B.rows P cs pre op k⟩

/-- **The generator's rows along the trail** (`FRNodeRun4.askRowsX`): at an ask or a covered op, its
rows at the aligned state; the ask counter `k` counts the asks before. -/
def trailRows (X : Ext) (P : Params) (G : TG) : CS → Option Op → ℕ → List Op → List Row
  | _, _, _, [] => []
  | cs, pre, k, op :: ops =>
    let c := cs.align (alignOf op ops)
    (if op.item?.isSome || G.cov op then G.rows P c pre op k else []) ++
      trailRows X P G (c.add op (stepOut X P c op)) (some op) (if op.item?.isSome then k + 1 else k) ops

/-- **The same fold with the template memo** (`compMSX`'s), the rows accumulated in reverse. -/
def trailMS (X : TCtx → Ext) (L : TLay) (P : Params) (G : TG) :
    List (TKey × Tpl) → CS → Option Op → ℕ → List Op → List Row → List Row
  | _, _, _, _, [], acc => acc
  | M, cs, pre, k, op :: ops, acc =>
    let c := cs.align (alignOf op ops)
    let acc := (if op.item?.isSome || G.cov op then G.rows P c pre op k else []).reverseAux acc
    let M := memoAdd M ((X ⟨fun _ => ⟨[], []⟩, L.cb⟩ P c op).bind (·.tin))
    let o := stepOut (X ⟨tlook M, L.cb⟩) P c op
    trailMS X L P G (memoAdd M o.tin) (c.add op o) (some op) (if op.item?.isSome then k + 1 else k) ops acc

/-- **`trailMS` is `trailRows`** (reversed onto the accumulator), for a memo of `tplOf`'s templates. -/
theorem trailMS_eq (X : TCtx → Ext) (L : TLay) (P : Params) (G : TG) :
    ∀ (ops : List Op) (M : List (TKey × Tpl)) (cs : CS) (pre : Option Op) (k : ℕ) (acc : List Row),
      MOk M → trailMS X L P G M cs pre k ops acc = (trailRows (X L.ctx) P G cs pre k ops).reverse ++ acc
  | [], _, _, _, _, _, _ => rfl
  | op :: ops, M, cs, pre, k, acc, h => by
    have hc : ∀ x, (⟨tlook (memoAdd M x), L.cb⟩ : TCtx) = L.ctx := fun x => by
      rw [tlook_eq (memoAdd_ok h x)]; rfl
    simp only [trailMS, trailRows, hc]
    rw [trailMS_eq X L P G ops _ _ _ _ _ (memoAdd_ok (memoAdd_ok h _) _), List.reverseAux_eq,
      List.reverse_append, List.append_assoc]

/-- **From a fresh state**: the rows in order. -/
theorem trailMS_T (X : TCtx → Ext) (L : TLay) (P : Params) (G : TG) (base : ℕ) (ops : List Op)
    {M : List (TKey × Tpl)} (h : MOk M) :
    (trailMS X L P G M (CS.init base) none 0 ops []).reverse = trailRows (X L.ctx) P G (CS.init base) none 0 ops := by
  rw [trailMS_eq X L P G ops M _ _ _ _ h, List.append_nil, List.reverse_reverse]

/-! ## The `input` generator (IMP's `AT.inp`) -/

/-- Prototype `π`'s `input` cell `h` of digest `j` (`FRNodeRows4AskInp.inC`). -/
def inCT (π j h : ℕ) : ℕ := π * slotM4 + W4.inOff + 2 * j + h

/-- A row no assignment with `one = 1` meets (`FRNodeRows4AskInp.failR`). -/
def failRT (P : Params) : Row := ⟨P.one, P.one, []⟩

/-- **The `input j` op's rows** (`FRNodeRows4AskInp.inpRowsT`): its digest slot's two cells are the
`input` cells, else `failRT`. -/
def inpRowsG (X : Ext) (π : ℕ) (P : Params) (cs : CS) (j : ℕ) : List Row :=
  match (stepOut X P cs (.input j)).slots with
  | [some (.d, [l₀, l₁])] =>
    [⟨P.one, l₀.sub (Lin.cell (inCT π (if j = 0 then 0 else 1) 0)), []⟩,
     ⟨P.one, l₁.sub (Lin.cell (inCT π (if j = 0 then 0 else 1) 1)), []⟩]
  | _ => [failRT P]

/-- **The `input` generator** of prototype `π` (extension `X`): covers the `input` ops. -/
def inpTG (X : Ext) (π : ℕ) : TG where
  cov op := match op with | .input _ => true | _ => false
  rows P cs _ op _ := match op with | .input j => inpRowsG X π P cs j | _ => []

/-! ## The reserve generator (SRA's `AT.rsv`, `FRNodeRsvLink`) -/

/-- Reserve cell `j` (`FRNodeRsvLink.rsvC`). -/
def rsvCT (j : ℕ) : ℕ := rsvRel.getD j 0

/-- The row point's entry `j` (`FRNodeRsvLink.tauC`). -/
def tauCT (j : ℕ) : ℕ := if j < 23 then rsvCT j else rsvCT (25 + j)

/-- The column point's entry `j` (`FRNodeRsvLink.sigC`). -/
def sigCT (j : ℕ) : ℕ := rsvCT (23 + j)

/-- `l` is the cell `c` (`FRNodeRsvLink.eqRowIf`). -/
def eqRowIfT (P : Params) (l : Lin) (c : ℕ) : List Row :=
  if l = Lin.cell c then [] else [⟨P.one, l.sub (Lin.cell c), []⟩]

/-- An `F`-array operand on the cells `f 0 … f (n−1)` (`FRNodeRsvLink.argRows`). -/
def argRowsT (P : Params) (s : Slot) (n : ℕ) (f : ℕ → ℕ) : List Row :=
  match s with
  | some (.af m, ls) =>
    if m = n ∧ ls.length = n then (ls.zipIdx).flatMap (fun p => eqRowIfT P p.1 (f p.2)) else [failRT P]
  | _ => [failRT P]

/-- Three `F` outputs on `rsvCT 57 … 59` (`FRNodeRsvLink.outRows`). -/
def outRowsT (P : Params) : List Slot → List Row
  | [some (.f, [l₀]), some (.f, [l₁]), some (.f, [l₂])] =>
    eqRowIfT P l₀ (rsvCT 57) ++ eqRowIfT P l₁ (rsvCT 58) ++ eqRowIfT P l₂ (rsvCT 59)
  | _ => [failRT P]

/-- The rows at an `evalM` op (`FRNodeRsvLink.rsvRowsT`). -/
def rsvRowsG (X : Ext) (P : Params) (cs : CS) : Op → List Row
  | .evalM t s => kinds.flatMap (fun κ => argRowsT P (cs.slotK t κ) 32 tauCT ++ argRowsT P (cs.slotK s κ) 25 sigCT) ++
      outRowsT P (stepOut X P cs (.evalM t s)).slots
  | _ => []

/-- Whether an op is an `evalM`. -/
def isEvalMT : Op → Bool
  | .evalM .. => true
  | _ => false

/-- **The reserve generator** of prototype `π` (SRA's `AT.rsv X π`): at prototype 0, the `evalM` ops. -/
def rsvTG (X : Ext) (π : ℕ) : TG where
  cov op := π == 0 && isEvalMT op
  rows P cs _ op _ := if π = 0 then rsvRowsG X P cs op else []

/-! ## Controls -/

/-- (+) Along `[input 0, accept]` the `input` generator emits its two rows (the `input` op compiles to
a digest slot), (−) the empty generator none; the ask counter does not move at a non-ask. -/
theorem trailRows_ctl :
    (trailRows noExt ⟨Lin.cell 0, fun _ => []⟩ (inpTG noExt 0) (CS.init 4) none 0 [.input 0, .accept]).length = 2 ∧
    trailRows noExt ⟨Lin.cell 0, fun _ => []⟩ TG.none (CS.init 4) none 0 [.input 0, .accept] = [] :=
  ⟨rfl, rfl⟩

end Rev4
end FR
