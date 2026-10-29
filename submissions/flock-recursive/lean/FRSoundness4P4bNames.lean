-- New for `flock-recursive` (BLUEPRINT revision 4.1, A.10 rows Lr1 … B′, §5.2; stage P4b): the
-- names of the soundness front's Lr, E, RS dooms and checks at `seq4`, fixed first so that R4 (the
-- program layer) can state its front checks against them. `FRSoundnessRows`, `FRSoundnessFrE`,
-- `FRSoundnessFrRS0`, `FRSoundnessFrW0` are the 3.x templates.
-- RET-2: import re-pointed at Core: `FRSoundnessFrPend` → `FRSoundnessCoreRows`.
import FRSoundness4Pos
import FRSoundnessCoreRows
import FRVIRTplEval

/-!
# P4b's names: the front's Lr, E and RS dooms and checks at revision 4.1

**The generalisation (S-G12′ F3, ruled as O1's restatement).** The 3.x row-Spartan unit reads its
matrices off a row list (`rowMat sel rows`), `f⁽⁰⁾` off 3.x's ladder (`fF (kindOf es)`), and the
log through 3.x's `Same`. Here each of the three is a parameter:

* **`ESrc`**, an **entries source**: the `A`, `B`, `C` entries (`Eval.Entries`); `entMat E a nc`
  is the matrix (`Eval.entry`). 3.x's row list is `ESrc.ofRows rows` (`rowMat_entMat`: `rfl`), and
  the **templated, indexed rows V evaluates** (`TEval.entriesI`, as `evalMS` reads
  `nodeIRows (planOf fin)`) are `ESrc.ofIRows rows` (O1).
* **`FSrc`**, what the front reads of `(L, es)`: an abstract `Same` relation and `f⁽⁰⁾`. 3.x is
  `src3` (`Same`, `fF (kindOf es)`); revision 4.1's is T4's (the Ligerito words at `CKind`'s
  ladder), so P4b's statements are parametric in it. **`ReadsS`** is `Reads` at an `FSrc`
  (`reads_iff_readsS`).
* **The generic unit** (`…G`): the 3.x unit's dooms without a kind gate, with the real row count
  `a` and the **slot** count `A` apart (the end absorb is at `b2 + 2A`): revision 4.1's phases have
  `seq4`'s slots (Lr2 17, E2 23, E4 25), a node kind's real rounds can be fewer (`N2`: 16, 22, 24).
  The rounds' dooms are 3.x's `D3`/`D2` with a **constant** round count, so they never read a kind.

**Revision 4.1** (`seq4`'s positions, `fsStarts4_eq`): Lr1 after 169 (9 squeezes), Lr2 from 179
(17 slots), Lrend 213, Lr3 (`κ_L`) 214, E1 after 214 (12), E2 from 227 (23), Eend 273, E3 (`κ_E`)
274, E4 from 275 (25), E4 end 325, RS0 326, RS1 327 … 330, B′ 331. A node kind `κ` has `lrR κ`
(`logL`: 16/17/17) Lr rows' bits, `e2R κ` (`logM`: 22/23/23) M rows' bits and `ncR κ` (`m − 7`:
24/25/25) cell bits = E4's real rounds. The gate is **`OnNode`**: the chain's kind (`kindOfC`) is
a node kind, and the doom at that kind's dims holds. The M and L rows per node kind are S-E's
(S-G13 F3), so they are parameters `srcE srcL : NodeKind → ESrc`.

**The checks R4 discharges on an accepted run** (each reads only the log): `RejEndLr4`,
`RejEndE4` (`finLr`/`finE` (ii)), `RejInE4` (E4's rounds), `RejFinE4` (`finE` (iv)), `RejRS4 ok`
(the RS claims' bindings at the slices' values, with `okRS4`).
-/

namespace FR.Snd.P4b
open RecursionFast FR.Merkle FR.Rev4 Finset

/-! ## What the front reads -/

/-- **What the front reads of a log pair**: an abstract `Same` (the entries before `p` and the
words of earlier caps) and `f⁽⁰⁾`, which reads the level-0 word (cap at position 2). -/
structure FSrc where
  Sm : Log → Log → Log → Log → ℕ → Prop
  agree : ∀ {L es L' es' : Log} {p : ℕ}, Sm L es L' es' p → Agree es es' p
  mono : ∀ {L es L' es' : Log} {p q : ℕ}, Sm L es L' es' p → q ≤ p → Sm L es L' es' q
  ofAgree : ∀ (L : Log) {es es' : Log} {p : ℕ}, Agree es es' p → Sm L es L es' p
  fz : Log → Log → ℕ → F
  fz_same : ∀ {L es L' es' : Log} {p : ℕ}, Sm L es L' es' p → 3 ≤ p → fz L es = fz L' es'

/-- **3.x's**: `Same` and `fF` at the log's kind. -/
noncomputable def src3 : FSrc where
  Sm := Same
  agree h := h.1
  mono h hq := h.mono hq
  ofAgree L _ _ _ h := same_of_agree L h
  fz L es := fF (kindOf es) L es
  fz_same h hp := by rw [h.kind (by omega)]; exact fF_same h hp _

/-- **`Reads` at an `FSrc`**: `P` reads only what lies before `p`. -/
def ReadsS (R : FSrc) (p : ℕ) (P : Log → Log → Prop) : Prop :=
  ∀ L es L' es', p ≤ es.length → p ≤ es'.length → R.Sm L es L' es' p → (P L es ↔ P L' es')

theorem reads_iff_readsS {p : ℕ} {P : Log → Log → Prop} : Reads p P ↔ ReadsS src3 p P := Iff.rfl

/-! ## Entries sources -/

/-- **An entries source**: the `A`, `B`, `C` entries `(row, cell, coefficient)`. -/
structure ESrc where
  ea : Eval.Entries
  eb : Eval.Entries
  ec : Eval.Entries

/-- The matrix of entries over `2^a` rows and `2^nc` cells. -/
def entMat (E : Eval.Entries) (a nc : ℕ) : Fin (2 ^ a) → Fin (2 ^ nc) → F :=
  fun x y => Eval.entry E x y

/-- 3.x's row list (`Eval.entriesOf`: row `i` at index `i`). -/
def ESrc.ofRows (rows : List Circ.Row) : ESrc :=
  ⟨Eval.entriesOf Circ.Row.a rows, Eval.entriesOf Circ.Row.b rows, Eval.entriesOf Circ.Row.c rows⟩

/-- **Indexed rows** (`TEval.entriesI`: row `(i, r)` at index `i`), as `evalMS` reads them. -/
def ESrc.ofIRows (rows : List (ℕ × Circ.Row)) : ESrc :=
  ⟨TEval.entriesI .a rows, TEval.entriesI .b rows, TEval.entriesI .c rows⟩

theorem rowMat_entMat (sel : Circ.Row → Circ.Lin) (rows : List Circ.Row) (a b : ℕ) :
    rowMat sel rows a b = entMat (Eval.entriesOf sel rows) a b := rfl

/-! ## The generic unit (no kind gate; `a` real rows, `A` slots) -/

section Unit
variable (R : FSrc) (E : ESrc) (a nc : ℕ)

/-- `f⁽⁰⁾` on `2^nc` cells. -/
def zCG (L es : Log) : Fin (2 ^ nc) → F := fun y => R.fz L es y

/-- **The unit's statement fails**: `f⁽⁰⁾` violates the source's R1CS. -/
def RowsBadG (L es : Log) : Prop :=
  ¬ Sat (entMat E.ea a nc) (entMat E.eb a nc) (entMat E.ec a nc) (zCG R nc L es)

variable (s0 b2 A : ℕ)

/-- **The zerocheck's final doom**: the residual's extension at the point is nonzero. -/
def ZCwG (L es : Log) : Prop :=
  mle (residual (entMat E.ea a nc) (entMat E.eb a nc) (entMat E.ec a nc) (zCG R nc L es))
    (ptOf a (tauS a s0 es)) ≠ 0

/-- The outer tables `eq(τ, ·)`, `Az`, `Bz`, `Cz`. -/
noncomputable def T3G (L es : Log) : Array (Array F) :=
  outerTables (tauS a s0 es) (entMat E.ea a nc) (entMat E.eb a nc) (entMat E.ec a nc)
    (zCG R nc L es)

/-- **The outer rounds' doom** (3.x's `D3`, `a` rounds from `b2`, claim `0`). -/
abbrev D3G : Log → Log → Prop :=
  D3 b2 (fun _ _ => 0) (fun _ => a) outerExpr (T3G R E a nc s0)

/-- The true triple at the outer rounds' point. -/
noncomputable def triTG (L es : Log) : F × F × F :=
  (mle (matVec (entMat E.ea a nc) (zCG R nc L es)) (ptOf a (rxs a b2 es)),
   mle (matVec (entMat E.eb a nc) (zCG R nc L es)) (ptOf a (rxs a b2 es)),
   mle (matVec (entMat E.ec a nc) (zCG R nc L es)) (ptOf a (rxs a b2 es)))

/-- **A wrong triple** after the end absorb (at `b2 + 2A`). -/
noncomputable def EndBadG (L es : Log) : Prop :=
  b2 + 2 * A < es.length ∧ (vEnd A b2 es 0, vEnd A b2 es 1, vEnd A b2 es 2) ≠ triTG R E a nc b2 L es

/-- The inner tables `M̃_κ(r, ·)` and `z`. -/
noncomputable def T4G (L es : Log) : Array (Array F) :=
  innerTables (ptOf a (rxs a b2 es)) (kapB A b2 es) (entMat E.ea a nc) (entMat E.eb a nc)
    (entMat E.ec a nc) (zCG R nc L es)

/-- **A false batched claim** after `κ` (at `b2 + 2A + 1`). -/
noncomputable def BatBadG (L es : Log) : Prop :=
  b2 + 2 * A + 1 < es.length ∧ c4 A b2 L es ≠ trueSum innerExpr (T4G R E a nc b2 A L es) nc

end Unit

/-- **The end check fails** (`finLr`/`finE` (ii)): the outer claim after `a` rounds is not
`eq(τ, r)·(â b̂ + ĉ)`, the triple absorbed at `b2 + 2A`. -/
def RejEndG (a s0 b2 A : ℕ) (L es : Log) : Prop :=
  b2 + 2 * A < es.length ∧
    clR b2 (fun _ _ => 0) L es a ≠ eq (ptOf a (tauS a s0 es)) (ptOf a (rxs a b2 es)) *
      (vEnd A b2 es 0 * vEnd A b2 es 1 + vEnd A b2 es 2)

/-! ## Revision 4.1: the node kinds' dims and the gate -/

/-- A node kind's Lr row bits (`logL`), M row bits (`logM`), cell bits (`m − 7`). -/
def lrR (κ : NodeKind) : ℕ := κ.dims.logL
def e2R (κ : NodeKind) : ℕ := κ.dims.logM
def ncR (κ : NodeKind) : ℕ := κ.m - 7

/-- **The node gate**: the chain's kind is a node kind `κ`, and `P κ` holds. -/
def OnNode (P : NodeKind → Log → Log → Prop) (L es : Log) : Prop :=
  ∃ κ, kindOfC es = .node κ ∧ P κ L es

/-! ## Lr (Lr1 after 169, Lr2 from 179, 17 slots; Lrend 213; Lr3 214) -/

section Lr
variable (R : FSrc) (srcL : NodeKind → ESrc)

def RowsBadLr4 : Log → Log → Prop := OnNode fun κ => RowsBadG R (srcL κ) (lrR κ) (ncR κ)
def ZCwLr4 : Log → Log → Prop := OnNode fun κ => ZCwG R (srcL κ) (lrR κ) (ncR κ) 169
def D3Lr4 : Log → Log → Prop := OnNode fun κ => D3G R (srcL κ) (lrR κ) (ncR κ) 169 179
def EndBadLr4 : Log → Log → Prop := OnNode fun κ => EndBadG R (srcL κ) (lrR κ) (ncR κ) 179 17
def BatBadLr4 : Log → Log → Prop := OnNode fun κ => BatBadG R (srcL κ) (lrR κ) (ncR κ) 179 17

end Lr

/-- **Lr's end check** (`finLr` (ii); Lrend at 213). -/
def RejEndLr4 : Log → Log → Prop := OnNode fun κ => RejEndG (lrR κ) 169 179 17

/-! ## E (E1 after 214, E2 from 227, 23 slots; Eend 273; E3 274; E4 from 275, 25 slots; 325) -/

section E
variable (R : FSrc) (srcE srcL : NodeKind → ESrc)

/-- **E's statement fails** (A.10 E1, O1): `f⁽⁰⁾` violates the node kind's M rows. -/
def nE4 : Log → Log → Prop := OnNode fun κ => RowsBadG R (srcE κ) (e2R κ) (ncR κ)
def ZCwE4 : Log → Log → Prop := OnNode fun κ => ZCwG R (srcE κ) (e2R κ) (ncR κ) 214
def D3E4 : Log → Log → Prop := OnNode fun κ => D3G R (srcE κ) (e2R κ) (ncR κ) 214 227
def EndBadE4 : Log → Log → Prop := OnNode fun κ => EndBadG R (srcE κ) (e2R κ) (ncR κ) 227 23

/-- **E4's initial claim** (`finE` (iii)): `â_M + κ_E b̂_M + κ_E² ĉ_M + κ_E³ v_L`. -/
def c4E4 (L es : Log) : F := c4 23 227 L es + kapB 23 227 es ^ 3 * c4 17 179 L es

/-- **E4's weight** (`evalM`, `evalL` at `r′`): M's batched by `κ_E`, plus `κ_E³` times Lr's batched
by `κ_L`. -/
noncomputable def wEb4 (κ : NodeKind) (es : Log) (y : Fin (2 ^ ncR κ)) : F :=
  wInn (entMat (srcE κ).ea (e2R κ) (ncR κ)) (entMat (srcE κ).eb (e2R κ) (ncR κ))
      (entMat (srcE κ).ec (e2R κ) (ncR κ)) (ptOf (e2R κ) (rxs (e2R κ) 227 es)) (kapB 23 227 es) y +
    kapB 23 227 es ^ 3 * wInn (entMat (srcL κ).ea (lrR κ) (ncR κ))
      (entMat (srcL κ).eb (lrR κ) (ncR κ)) (entMat (srcL κ).ec (lrR κ) (ncR κ))
      (ptOf (lrR κ) (rxs (lrR κ) 179 es)) (kapB 17 179 es) y

/-- E4's tables `[wEb4, z]`. -/
noncomputable def TEb4 (κ : NodeKind) (L es : Log) : Array (Array F) :=
  #[Array.ofFn (wEb4 srcE srcL κ es), Array.ofFn (zCG R (ncR κ) L es)]

/-- **E3's doom**: the batched claim is false after `κ_E`. -/
noncomputable def BatBadE4 : Log → Log → Prop :=
  OnNode fun κ L es => 274 < es.length ∧ c4E4 L es ≠ trueSum innerExpr (TEb4 R srcE srcL κ L es) (ncR κ)

/-- E4's rounds at node kind `κ` (F, degree 2, from 275, `ncR κ` real rounds). -/
abbrev D2Eb4 (κ : NodeKind) : Log → Log → Prop :=
  D2 275 16 readF (fun d => chF d 0) c4E4 (fun _ => ncR κ) innerExpr (TEb4 R srcE srcL κ)

/-- **E4's doom**. -/
def D4E4 : Log → Log → Prop := OnNode (D2Eb4 R srcE srcL)

end E

/-- **E's end check** (`finE` (ii); Eend at 273). -/
def RejEndE4 : Log → Log → Prop := OnNode fun κ => RejEndG (e2R κ) 214 227 23

/-- **E4's round checks fail** (`finE`'s rounds: `g(0) + g(1)` against the running claim). -/
def RejInE4 : Log → Log → Prop :=
  OnNode fun κ L es => ∃ l < ncR κ, 275 + 2 * l < es.length ∧
    ¬ Chk2 275 16 readF (fun d => chF d 0) c4E4 L es l

/-- The binding of E's RS claim (`finE` (v)): its value is E4 end's message. -/
def okE4 (es : Log) (v : F) : Prop := v = readF (msgAt es 325) 0

/-- E4's point `r′` (the real rounds' challenges). -/
def rPt4 (κ : NodeKind) (es : Log) : List F := rchs2 275 (fun d => chF d 0) es (ncR κ)

/-- **`finE` (iv) fails** (from 326): E4's last claim is not `W(r′)·α_E`. -/
noncomputable def RejFinE4 (srcE srcL : NodeKind → ESrc) : Log → Log → Prop :=
  OnNode fun κ L es => 326 ≤ es.length ∧
    clR2 275 16 readF (fun d => chF d 0) c4E4 L es (ncR κ) ≠
      mle (wEb4 srcE srcL κ es) (ptOf (ncR κ) (rPt4 κ es)) * readF (msgAt es 325) 0

/-- **E's pending claim is false** (after E4 end): its value is not `ẑ(r′)`. -/
noncomputable def PendE4 (R : FSrc) : Log → Log → Prop :=
  OnNode fun κ L es => 325 < es.length ∧ ¬ okE4 es (mle (zCG R (ncR κ) L es) (ptOf (ncR κ) (rPt4 κ es)))

/-! ## RS0 (326) and the claims' bindings -/

/-- Sh's low point: S2's challenges `m − 14 … m − 8`. -/
def xSL4 (κ : CKind) (es : Log) : List F := (List.range 7).map fun l => rch 114 es (κ.m - 14 + l)

/-- The inner weights `c_{j,i}` on the log (`cwF`). -/
def cwL4 (κ : CKind) (es : Log) (j i : ℕ) : F := cwF (fAt es 14 0) (xLL es) (xSL4 κ es) j i

/-- E4's claim point: its `n` real challenges. -/
def ePtL4 (n : ℕ) (es : Log) : List F := (List.range n).map (rch 275 es)

/-- **The RS claim points** (`gPfPts`' claims at the kind's `m`): Z, Lc, Sh; E4's `r′` on a node. -/
def rsPtsL4 (κ : CKind) (es : Log) : List (List F) :=
  [zPtL κ.m es, lcPtL κ.m es, shPtL κ.m es] ++
    match κ with
    | .node ν => [ePtL4 (ncR ν) es]
    | .seg _ => []

/-- Slice `i` of RS claim `j` (RS0's message at 326). -/
def sliceL4 (es : Log) (j i : ℕ) : F := readF (msgAt es 326) (rsOff j i)

/-- Claim `j`'s slices (`0` for a segment's fourth claim). -/
def sL4 (κ : CKind) (es : Log) (j : Fin 4) (i : Fin 128) : F :=
  if j.val < (rsPtsL4 κ es).length then sliceL4 es j i else 0

/-- **Claim `j`'s value from RS0's slices** (`rsAlpha`). -/
def alphaL4 (κ : CKind) (es : Log) (j : Fin 4) : F := ∑ i : Fin 128, cwL4 κ es j i * sL4 κ es j i

/-- **RS0's bindings**: Z's, Lc's, Sh's are parameters (P4a's `finZ`, `finLc`, `finSh`); E's is
`okE4`. -/
def okRS4 (oZ oLc oSh : CKind → Log → F → Prop) (κ : CKind) (es : Log) (j : ℕ) (v : F) : Prop :=
  match j with
  | 0 => oZ κ es v
  | 1 => oLc κ es v
  | 2 => oSh κ es v
  | _ => okE4 es v

/-- **`RejF`'s slice part** (from 327): some claim's binding fails at the slices' value. -/
def RejRS4 (ok : CKind → Log → ℕ → F → Prop) (_L es : Log) : Prop :=
  327 ≤ es.length ∧ ∃ j : Fin 4, j.val < (rsPtsL4 (kindOfC es) es).length ∧
    ¬ ok (kindOfC es) es j (alphaL4 (kindOfC es) es j)

/-! ## Controls -/

/-- (+) 3.x's end check is the generic one at `A = a`, under 3.x's gate. -/
theorem rejEnd_eq_G {a s0 b2 : ℕ} {on : Kind → Bool} (L es : Log) :
    RejEnd a on s0 b2 L es ↔ on (kindOf es) = true ∧ RejEndG a s0 b2 a L es := Iff.rfl

/-- (+) 3.x's wrong triple is the generic one at `src3` and its row list. -/
theorem endBad_eq_G {rows : List Circ.Row} {a nc b2 : ℕ} {on : Kind → Bool} (L es : Log) :
    EndBad rows a nc on b2 L es ↔
      on (kindOf es) = true ∧ EndBadG src3 (ESrc.ofRows rows) a nc b2 a L es := Iff.rfl

/-- (+) 3.x's statement doom is the generic one. -/
theorem rowsBad_eq_G {rows : List Circ.Row} {a nc : ℕ} {on : Kind → Bool} (L es : Log) :
    RowsBad rows a nc on L es ↔ on (kindOf es) = true ∧ RowsBadG src3 (ESrc.ofRows rows) a nc L es :=
  Iff.rfl

/-- (+) The dims per node kind (`coords_eq`, `NodeKind.dims`). -/
theorem dims_ctrl : (lrR .N2, e2R .N2, ncR .N2) = (16, 22, 24) ∧
    (lrR .N4, e2R .N4, ncR .N4) = (17, 23, 25) ∧ (lrR .N8, e2R .N8, ncR .N8) = (17, 23, 25) :=
  ⟨rfl, rfl, rfl⟩

/-- (+) Every real count fits `seq4`'s slots (Lr 17, E2 23, E4 25). -/
theorem dims_le (κ : NodeKind) : lrR κ ≤ seq4.lr ∧ e2R κ ≤ seq4.e2 ∧ ncR κ ≤ seq4.e4 := by
  rw [seq4_eq]; cases κ <;> decide

/-- (−) On a segment's chain every gated doom and check is false. -/
theorem not_onNode_seg {P : NodeKind → Log → Log → Prop} {L es : Log} {σ : SegKind}
    (h : kindOfC es = .seg σ) : ¬ OnNode P L es := by
  rintro ⟨κ, hk, -⟩; rw [h] at hk; cases hk

/-- (+) On a node's chain the gate is the kind's doom. -/
theorem onNode_iff {P : NodeKind → Log → Log → Prop} {L es : Log} {κ : NodeKind}
    (h : kindOfC es = .node κ) : OnNode P L es ↔ P κ L es :=
  ⟨fun ⟨ν, hν, hp⟩ => by rw [h] at hν; cases hν; exact hp, fun hp => ⟨κ, h, hp⟩⟩

/-- (+/−) A node's four RS claims, a segment's three. -/
theorem rsPtsL4_length (κ : CKind) (es : Log) :
    (rsPtsL4 κ es).length = if κ.isNode then 4 else 3 := by
  cases κ <;> rfl

/-- (+) E4's claim point has the kind's real count of coordinates (`N2`: 24, not `seq4`'s 25). -/
theorem rPt4_length (κ : NodeKind) (es : Log) : (rPt4 κ es).length = ncR κ := by
  simp [rPt4, rchs2]

end FR.Snd.P4b
