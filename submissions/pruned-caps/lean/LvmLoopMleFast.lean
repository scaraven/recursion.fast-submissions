-- new for lvm (INT-2): a linear-time evaluator of the fixed-column closed forms of the lvm tables,
-- proved equal to WP-10's `pieceEval` and WP-9's `grpEval` (`LvmM3LoopTab`); no Mathlib.
import LvmM3LoopTab
import LvmFieldCorrect

-- (GOLF2: 30 declarations that `certified` does not use moved verbatim to `LvmM3MidCertOff`, outside its import closure.)

/-!
# The fixed-column closed forms in linear time

`grpEval Q g` (WP-9) evaluates a group's fixed column from `Q.pieces` (rebuilt per member),
`Q.pieceEval` (WP-10), whose terms read `Q.start` (a sum over the earlier blocks), `Block.rank`
(a sum over the template), `p.ts.getD` and `B.tpl.getD` (list walks), and `fixFEval`, which
rebuilds `Q.glueCols` per call. The native verifier runs these at every group member's point, so the
cost grows with (program size) × (members): 15.5 s for every closed form of a synthetic P20
program of 76 blocks (INT-2; 43 ms here). Here the same formulas read a cache built once per program (`cache Q`): per block its
template as an array, its start cells and its rank prefix sums; the pieces with their template
rows as arrays; the glue columns (`cache`); then each piece's fixed-column coefficients
(`g^{base_i}`, `lin`'s constants) as arrays, so that a closed form is one fold with one product per
node (`mleF`) and no power (`cacheG`, `pieceEvalG`, `grpEvalG`).

* `pieceEvalF_eq`: `pieceEvalF (cache Q) (p, p.ts.toArray) c r = Q.pieceEval p c r`;
* `grpEvalF_eq`: `grpEvalF (cache Q) g = grpEval Q g`; `pieceEvalG_eq`, `fixFEvalG_eq`, `grpEvalG_eq`
  on `cacheG Q`;
* **`lvmTabsC_eq`**: `lvmTabsC (cacheG Q) pl groups arrs aux = lvmTabs Q pl groups arrs aux` (and
  `lvmTabsF`, the cache built in place): the tables the
  native verifier evaluates are WP-9's tables, so every statement about `lvmTabs` holds of them.
-/

namespace Lvm.M3

open Lvm.Loop

/-! ## Running sums -/

/-- `a, a + l₀, a + l₀ + l₁, …` (`l.length + 1` entries). -/
def psums : List Nat → Nat → List Nat
  | [], a => [a]
  | x :: xs, a => a :: psums xs (a + x)

theorem length_psums : ∀ (l : List Nat) (a : Nat), (psums l a).length = l.length + 1
  | [], _ => rfl
  | _ :: xs, a => by simp [psums, length_psums xs]

theorem psums_getD : ∀ (l : List Nat) (a i : Nat), i ≤ l.length →
    (psums l a).getD i 0 = a + (l.take i).sum
  | [], a, i, h => by
    have : i = 0 := by simpa using h
    subst this; simp [psums]
  | _ :: _, a, 0, _ => by simp [psums]
  | x :: xs, a, i + 1, h => by
    simp only [psums, List.getD_cons_succ, List.take_succ_cons, List.sum_cons]
    rw [psums_getD xs (a + x) i (by simp at h; omega)]; omega

theorem toArray_getD {α : Type} (l : List α) (i : Nat) (d : α) : l.toArray.getD i d = l.getD i d := by
  simp [Array.getD, List.getD_eq_getElem?_getD]
  split <;> simp_all

/-! ## The cache -/

/-- A block with its template as an array, its first cells and its rank prefix sums. -/
structure BC where
  /-- The block. -/
  B : Block
  /-- Its template. -/
  tpl : Array Row
  /-- `Q.start .K b`. -/
  sK : Nat
  /-- `Q.start .E b`. -/
  sE : Nat
  /-- `B.tw .K`. -/
  tK : Nat
  /-- `B.tw .E`. -/
  tE : Nat
  /-- `B.rank .K t` for `t ≤ |tpl|`. -/
  rK : Array Nat
  /-- `B.rank .E t` for `t ≤ |tpl|`. -/
  rE : Array Nat

/-- The cache entry of a block from its first cells. -/
def mkBC (B : Block) (sK sE : Nat) : BC :=
  ⟨B, B.tpl.toArray, sK, sE, B.tw .K, B.tw .E, (psums (B.tpl.map (Row.w .K)) 0).toArray,
    (psums (B.tpl.map (Row.w .E)) 0).toArray⟩

namespace BC

variable (c : BC)

/-- The first cell of memory `τ`. -/
def start : Ty → Nat
  | .K => c.sK
  | .E => c.sE

/-- `B.tw τ`. -/
def tw : Ty → Nat
  | .K => c.tK
  | .E => c.tE

/-- `B.rank τ t` (from the prefix sums inside the template). -/
def rank (τ : Ty) (t : Nat) : Nat :=
  if t ≤ c.B.tpl.length then (match τ with | .K => c.rK | .E => c.rE).getD t 0 else c.B.rank τ t

end BC

/-- The program cache. -/
structure PC where
  /-- The program. -/
  Q : Program
  /-- Its blocks. -/
  bcs : Array BC
  /-- Its pieces with their template rows as arrays. -/
  pcs : Array (Piece × Array Nat)
  /-- Its glue columns. -/
  glue : List (Piece × FCol)

/-- **The cache of a program** (built once). -/
def cache (Q : Program) : PC :=
  let sK := psums (Q.blocks.map fun B => B.tw .K * B.size) Q.nInK
  let sE := psums (Q.blocks.map fun B => B.tw .E * B.size) Q.nInE
  let ps := Q.pieces
  ⟨Q, ((Q.blocks.zip (sK.zip sE)).map fun (B, k, e) => mkBC B k e).toArray,
    (ps.map fun p => (p, p.ts.toArray)).toArray,
    (ps.filter fun p => Q.glue.contains p.blk).flatMap fun p =>
      (p.shape.fcols.filter (· != .F)).map fun c => (p, c)⟩

namespace PC

variable (C : PC)

/-- Block `b`'s entry (built from the program past the end). -/
def bc (b : Nat) : BC :=
  if h : b < C.bcs.size then C.bcs[b] else mkBC (C.Q.blk b) (C.Q.start .K b) (C.Q.start .E b)

/-- Piece `n` with its template rows as an array. -/
def pieceOf (n : Nat) : Piece × Array Nat :=
  if h : n < C.pcs.size then C.pcs[n] else (default, #[])

end PC

/-! ## The closed forms on the cache -/

/-- `lin`'s constant `k` or `k'` of an operation (else `0`). -/
def kOf (c : FCol) (op : Op) : FK :=
  match c, op with
  | .k, .lin k _ => k
  | .k', .lin _ k' => k'
  | .k, .e2 (.lin k _ _) _ => k
  | .k', .e2 (.lin _ k₀ k₁) h => if h then k₁ else k₀
  | _, _ => 0

/-- `Q.colAffine` from a block's cache entry. -/
def colAffineF (bc : BC) (c : FCol) (t : Nat) : Nat × List Nat :=
  let r := bc.tpl.getD t default
  match c with
  | .res => (bc.start r.ty + bc.rank r.ty t, scaledStrides bc.B.dims (bc.tw r.ty))
  | .arg o => ((r.args.getD o default).base, (r.args.getD o default).strides)
  | _ => (0, [])

/-- **`pieceEval` on the cache** (the piece with its template rows as an array). -/
def pieceEvalF (C : PC) (pc : Piece × Array Nat) (c : FCol) (r : List FE) : FE :=
  let bc := C.bc pc.1.blk
  let rJ := r.take bc.B.lsize
  let rI := r.drop bc.B.lsize
  match c with
  | .res | .arg _ => tplSum rI fun i =>
      let (base, s) := colAffineF bc c (pc.2.getD i 0)
      FE.ofK (FK.x ^ base) * boxEval bc.B.dims s rJ
  | .k | .k' => tplSum rI fun i => FE.ofK (kOf c (bc.tpl.getD (pc.2.getD i 0) default).op)
  | .F => 0

/-- A piece's log-height from the cache. -/
def heightF (C : PC) (p : Piece) : Nat := p.a + (C.bc p.blk).B.lsize

/-- `fixFEval` on the cache. -/
def fixFEvalF (C : PC) (p : Piece) (r : List FE) : FE :=
  let dims := (C.bc p.blk).B.dims
  let dc := dims.getD 0 0
  let dx := dims.getD 1 0
  let rc := r.take dc
  let rx := (r.drop dc).take dx
  let ec := eqKernel' rc
  ((C.glue.zipIdx).map fun ((gp, gc), c) ↦
    let h := heightF C gp
    ec.getD c 0 * pieceEvalF C (gp, gp.ts.toArray) gc (rx.take h ++ List.replicate (h - rx.length) 0) *
      ((rx.drop h).map (1 - ·)).foldl (· * ·) 1).foldl (· + ·) 0

/-- `pieceFixEval` on the cache. -/
def pieceFixEvalF (C : PC) (pc : Piece × Array Nat) (c : FCol) (r : List FE) : FE :=
  match c with
  | .F => fixFEvalF C pc.1 r
  | c => pieceEvalF C pc c r

/-- **`grpEval` on the cache.** -/
def grpEvalF (C : PC) (g : Grp) (c : FCol) (r : List FE) : FE :=
  (g.mem.map fun (n, off) ↦
    let pc := C.pieceOf n
    let h := heightF C pc.1
    eqSel (off >>> h) (r.drop h) * pieceFixEvalF C pc c (r.take h)).foldl (· + ·) 0

/-! ## Precomputed coefficients (the second stage of the cache)

A piece's closed form is `Σ_i eq(r_I, i)·coef_i·boxEval(s_i, r_J)` (`coef_i = g^{base_i}` or `lin`'s
constant): the coefficients do not depend on the point, so the cache holds them as arrays and the
native verifier only folds (one product per node, `mleF`). -/

/-- `mle` with one product per node: `(1 - r)·a + r·b = a + r·(b - a)`. -/
def mleF : List FE → (Nat → FE) → FE
  | [], f => f 0
  | r :: rs, f =>
    let a := mleF rs (fun x => f (2 * x))
    a + r * (mleF rs (fun x => f (2 * x + 1)) - a)

/-- `a · boxEval dims s r`, without the product when there is no loop dimension. -/
def boxMul (a : FE) (dims s : List Nat) (r : List FE) : FE :=
  match dims with
  | [] => a
  | _ :: _ => a * boxEval dims s r

/-- The coefficient of template row `i` of a piece for column `c`. -/
def coefS (bc : BC) (ts : Array Nat) (c : FCol) (i : Nat) : FE :=
  match c with
  | .res | .arg _ => FE.ofK (FK.x ^ (colAffineF bc c (ts.getD i 0)).1)
  | .k | .k' => FE.ofK (kOf c (bc.tpl.getD (ts.getD i 0) default).op)
  | .F => 0

/-- A piece with its template rows and its fixed columns' coefficients as arrays. -/
structure PE where
  /-- The piece. -/
  p : Piece
  /-- Its template rows. -/
  ts : Array Nat
  /-- Per fixed column (not `F`), its `2^a` coefficients. -/
  pre : List (FCol × Array FE)

/-- A piece's entry, its block's cache entry `bc`. -/
def mkPE (bc : BC) (p : Piece) : PE :=
  let ts := p.ts.toArray
  ⟨p, ts, (p.shape.fcols.filter (· != .F)).map fun c => (c, Array.ofFn (n := 2 ^ p.a) fun i => coefS bc ts c i.val)⟩

@[simp] theorem mkPE_p (bc : BC) (p : Piece) : (mkPE bc p).p = p := rfl
@[simp] theorem mkPE_ts (bc : BC) (p : Piece) : (mkPE bc p).ts = p.ts.toArray := rfl

/-- The coefficient from the arrays (computed when absent). -/
def coefF (bc : BC) (pe : PE) (c : FCol) (i : Nat) : FE :=
  match pe.pre.find? (fun x => x.1 == c) with
  | some (_, A) => if h : i < A.size then A[i] else coefS bc pe.ts c i
  | none => coefS bc pe.ts c i

theorem coefF_eq (bc : BC) (p : Piece) (c : FCol) (i : Nat) :
    coefF bc (mkPE bc p) c i = coefS bc p.ts.toArray c i := by
  unfold coefF
  split
  · rename_i c' A hf
    have hm := List.mem_of_find?_eq_some hf
    have hc : c' = c := by simpa using List.find?_some hf
    obtain ⟨c'', -, he⟩ := List.mem_map.mp hm
    simp only [Prod.mk.injEq] at he
    obtain ⟨rfl, rfl⟩ := he
    subst hc
    split
    · simp [mkPE]
    · rfl
  · rfl

/-- **The program cache with the coefficients.** -/
structure PG where
  /-- The first stage. -/
  C : PC
  /-- The pieces' entries. -/
  pes : Array PE
  /-- The glue columns' entries. -/
  glueE : List (PE × FCol)

/-- **The cache of a program** (build it once). -/
def cacheG (Q : Program) : PG :=
  let C := cache Q
  ⟨C, (Q.pieces.map fun p => mkPE (C.bc p.blk) p).toArray,
    Q.glueCols.map fun (p, c) => (mkPE (C.bc p.blk) p, c)⟩

/-- Piece `n`'s entry. -/
def PG.pe (G : PG) (n : Nat) : PE :=
  if h : n < G.pes.size then G.pes[n] else mkPE (G.C.bc (default : Piece).blk) default

/-- `pieceEval` on the coefficient cache. -/
def pieceEvalG (G : PG) (pe : PE) (c : FCol) (r : List FE) : FE :=
  let bc := G.C.bc pe.p.blk
  let rJ := r.take bc.B.lsize
  let rI := r.drop bc.B.lsize
  match c with
  | .res | .arg _ => mleF rI fun i =>
      boxMul (coefF bc pe c i) bc.B.dims (colAffineF bc c (pe.ts.getD i 0)).2 rJ
  | .k | .k' => mleF rI (coefF bc pe c)
  | .F => 0

/-- `fixFEval` on the coefficient cache. -/
def fixFEvalG (G : PG) (p : Piece) (r : List FE) : FE :=
  let dims := (G.C.bc p.blk).B.dims
  let dc := dims.getD 0 0
  let dx := dims.getD 1 0
  let rc := r.take dc
  let rx := (r.drop dc).take dx
  let ec := eqKernel' rc
  ((G.glueE.zipIdx).map fun ((pe, gc), c) ↦
    let h := heightF G.C pe.p
    ec.getD c 0 * pieceEvalG G pe gc (rx.take h ++ List.replicate (h - rx.length) 0) *
      ((rx.drop h).map (1 - ·)).foldl (· * ·) 1).foldl (· + ·) 0

/-- `pieceFixEval` on the coefficient cache. -/
def pieceFixEvalG (G : PG) (pe : PE) (c : FCol) (r : List FE) : FE :=
  match c with
  | .F => fixFEvalG G pe.p r
  | c => pieceEvalG G pe c r

/-- **`grpEval` on the coefficient cache.** -/
def grpEvalG (G : PG) (g : Grp) (c : FCol) (r : List FE) : FE :=
  (g.mem.map fun (n, off) ↦
    let pe := G.pe n
    let h := heightF G.C pe.p
    eqSel (off >>> h) (r.drop h) * pieceFixEvalG G pe c (r.take h)).foldl (· + ·) 0

/-- **The lvm tables with the cached closed forms**, on a cache `C` (build it once: `C = cache Q`). -/
def lvmTabsC (G : PG) (pl : Nat → Var → Bool × Nat) (groups : List Grp) (arrs : List InArr)
    (aux : List Tab) : List Tab :=
  (List.range groups.length).map (fun i ↦
    shapeTab (groups.getD i default).σ (groups.getD i default).τ (grpFix G.C.Q (groups.getD i default))
      (grpEvalG G (groups.getD i default)) (pl i)) ++
    arrs.map InArr.tab ++ aux

/-! ## Public input arrays (BLUEPRINT A19's `PUB`) -/

/-- The cells of a public `K` array from its public values (π's header lanes, in the circuit's
order): cell `x` is value `x`, `0` past the end. -/
def pubCell (vals : List FK) (x : Nat) : FK := vals.getD x 0

/-- **V's evaluator of a public column**: the extension of `pubCell vals` at `r` (one product per
node, `O(2^|r|)`; the values read from an array: QLT has ≈ 1.2 k lanes on `2^13` rows, AC-V). -/
def pubEval (vals : List FK) (r : List FE) : FE :=
  let a := vals.toArray
  mleF r fun x => FE.ofK (a.getD x 0)

/-- A public input array of `K` cells `base + stride·x` holding `vals` (one value column `val`,
which only fixes the limb count; `fin` places the finalize-count column). -/
def pubArr (τ base stride : Nat) (val fin : Bool × Nat) (vals : List FK) : InArr :=
  ⟨.K, τ, base, stride, [val], fin, some (pubCell vals, pubEval vals)⟩

end Lvm.M3
