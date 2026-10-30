-- New for `flock-recursive` (track REPF; C1b-RESULT §5.2): the replay rows at process start, in the
-- ask rows' memoized pass, and their split into the frame and local parts the plan evaluates.
import FRNodeRows4

/-!
# The replay rows from the memoized trail (the fold lemma)

* **`trailMR`**: ASK-P's memoized trail (`trailMS`: the template memo of `compMSX`) carrying a second
  accumulator, the replay template's rows. One pass gives a prototype's ask rows and its replay rows,
  without C1's second (un-memoized) compile.
* **`trailMR_eq`**: its two accumulators are `trailRows` and `repRowsX` (reversed onto them). Hence
  **`repRowsP_trail`** (`repRowsP rt π` is the second component from a fresh state): the fold lemma
  the plan's rows need. It holds for every `RT`; no locality or SSA property of the templates is used.
* **`repLocF`/`repLocL`**: a replay row list in local coordinates (row `k`, cells below `2^20`): the
  frame part (cells `< repB`) and the local part (cells `≥ repB`, moved down by `repB`). The plan
  evaluates them once per call and combines them per kind (`FRNodeRows4Plan.repV0_eq`).
-/

namespace FR
namespace Rev4
open RecursionFast Circ TEval Tpl

/-- **The memoized trail with the replay rows** (`trailMS` plus a second accumulator). -/
def trailMR (X : TCtx → Ext) (L : TLay) (P : Params) (G : TG) (rt : RT) :
    List (TKey × Tpl) → CS → Option Op → ℕ → List Op → List Row → List Row → List Row × List Row
  | _, _, _, _, [], acc, acr => (acc, acr)
  | M, cs, pre, k, op :: ops, acc, acr =>
    let c := cs.align (alignOf op ops)
    let acc := (if op.item?.isSome || G.cov op then G.rows P c pre op k else []).reverseAux acc
    let M := memoAdd M ((X ⟨fun _ => ⟨[], []⟩, L.cb⟩ P c op).bind (·.tin))
    let o := stepOut (X ⟨tlook M, L.cb⟩) P c op
    let acr := (if rt.cov op then rt.rows P c op o.slots else []).reverseAux acr
    trailMR X L P G rt (memoAdd M o.tin) (c.add op o) (some op) (if op.item?.isSome then k + 1 else k) ops acc acr

/-- **`trailMR` is `trailRows` and `repRowsX`** (each reversed onto its accumulator), for a memo of
`tplOf`'s templates. -/
theorem trailMR_eq (X : TCtx → Ext) (L : TLay) (P : Params) (G : TG) (rt : RT) :
    ∀ (ops : List Op) (M : List (TKey × Tpl)) (cs : CS) (pre : Option Op) (k : ℕ) (acc acr : List Row),
      MOk M → trailMR X L P G rt M cs pre k ops acc acr =
        ((trailRows (X L.ctx) P G cs pre k ops).reverse ++ acc, (repRowsX (X L.ctx) P rt cs ops).reverse ++ acr)
  | [], _, _, _, _, _, _, _ => rfl
  | op :: ops, M, cs, pre, k, acc, acr, h => by
    have hc : ∀ x, (⟨tlook (memoAdd M x), L.cb⟩ : TCtx) = L.ctx := fun x => by
      rw [tlook_eq (memoAdd_ok h x)]; rfl
    simp only [trailMR, trailRows, repRowsX, hc]
    rw [trailMR_eq X L P G rt ops _ _ _ _ _ _ (memoAdd_ok (memoAdd_ok h _) _), List.reverseAux_eq,
      List.reverseAux_eq, List.reverse_append, List.reverse_append, List.append_assoc, List.append_assoc]

/-- **A prototype's ask rows and replay rows in one memoized pass** (the plan's). -/
def arRepOf (π : ℕ) : List Row × List Row :=
  let r := trailMR (N4s.XofC π) (protoLay π) (protoP π) (askTG π) (N4s.rtC1d π) []
    (CS.init (baseR π)) none 0 (protoProg π).ops [] []
  (r.1.reverse, r.2.reverse)

/-- **The fold lemma**: the pass gives `askRowsT π` and `repRowsP (rtC1d π) π`. -/
theorem arRepOf_eq (π : ℕ) : arRepOf π = (askRowsT π, N4s.repRowsP (N4s.rtC1d π) π) := by
  unfold arRepOf
  rw [trailMR_eq _ _ _ _ _ _ _ _ _ _ _ _ (by simp [MOk])]
  simp only [List.append_nil, List.reverse_reverse]
  rfl

/-- **`repRowsP` from the memoized trail** (for every replay template). -/
theorem repRowsP_trail (rt : RT) (π : ℕ) :
    N4s.repRowsP rt π = ((trailMR (N4s.XofC π) (protoLay π) (protoP π) TG.none rt []
      (CS.init (baseR π)) none 0 (protoProg π).ops [] []).2).reverse := by
  rw [trailMR_eq _ _ _ _ _ _ _ _ _ _ _ _ (by simp [MOk])]
  simp only [List.append_nil, List.reverse_reverse]
  rfl

/-! ## Local coordinates -/

/-- A form's frame part (cells below `repB`). -/
def linFr (l : Lin) : Lin := l.filter fun t => decide (t.1 < N4s.repB)

/-- A form's local part (cells at or above `repB`), moved down by `repB`. -/
def linLoc (l : Lin) : Lin := (l.filter fun t => !decide (t.1 < N4s.repB)).map fun t => (t.1 - N4s.repB, t.2)

def rowFr (r : Row) : Row := ⟨linFr r.a, linFr r.b, linFr r.c⟩
def rowLoc (r : Row) : Row := ⟨linLoc r.a, linLoc r.b, linLoc r.c⟩

/-- **The replay rows' frame part** at rows `k` (local coordinates). -/
def repLocF (rows : List Row) : List (ℕ × Row) := rows.zipIdx.map fun p => (p.2, rowFr p.1)

/-- **The replay rows' local part** at rows `k`, cells `c − repB`. -/
def repLocL (rows : List Row) : List (ℕ × Row) := rows.zipIdx.map fun p => (p.2, rowLoc p.1)

theorem r_rowFr (s : TEval.Mat) (r : Row) : s.r (rowFr r) = linFr (s.r r) := by cases s <;> rfl
theorem r_rowLoc (s : TEval.Mat) (r : Row) : s.r (rowLoc r) = linLoc (s.r r) := by cases s <;> rfl

/-- (+) A frame cell goes to the frame part, a local to the local part moved down; (−) neither part keeps
the other's term. -/
theorem linFr_ctl : linFr [(5, 2), (N4s.repB + 7, 3)] = [(5, 2)] ∧
    linLoc [(5, 2), (N4s.repB + 7, 3)] = [(7, 3)] := by
  simp only [linFr, linLoc, N4s.repB]; decide

end Rev4
end FR
