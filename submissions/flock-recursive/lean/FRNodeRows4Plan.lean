-- G6: this module also holds the former modules `FRVIRTplCFF`, `FRNodeRows4RepCFW` (one section each, in import order).
import FRInitFuse
import FRVIRTplRun
import FRFlatPk

section G6_FRVIRTplCFF

-- New for `flock-recursive` (track CF2): the prepared segments' value, three matrices per pass.

/-!
# Prepared segments, three matrices per pass

`psVal` evaluates one matrix and rebuilds a repeated pattern's per-call sums (`Rep.ctx`) for each.
**`psVal3`** evaluates the three together: the row weights and carries once per row (`tmG3`,
`Rep.pass3`), the per-call sums once per pattern (`Rep.ctx3`). `ctx3` also evaluates each
placeholder's forms once for both carries, and skips the placeholders whose forms are `0` at the
wires: local-only ones when the locals are `0` (flag `zl`), input-only ones when `one` and the inputs
are `0` (flag `zi`). **`ctx3_eq`**: it is `ctx`; **`psVal3_eq`**: `psVal3` is `psVal`'s three values.
-/

namespace FR
namespace Tpl
open Circ TEval

/-- `c · v`, no product if `c = 1`. -/
@[inline] def mul1 (c v : F) : F := if c = 1 then v else c * v

theorem mul1_eq (c v : F) : mul1 c v = c * v := by unfold mul1; split_ifs with h <;> simp [h]

/-- `x * y`, no product if `y = 0`. -/
@[inline] def mulZ (x y : F) : F := if y = 0 then 0 else x * y

theorem mulZ_eq (x y : F) : mulZ x y = x * y := by unfold mulZ; split_ifs with h <;> simp [h]

/-- `LinT.ev` by a fold (no product for a coefficient `1` or a wire `0`). -/
def evF (e : Env) (l : LinT) : F :=
  l.foldl (fun a τ => let v := τ.1.ev e; if v = 0 then a else a + mul1 τ.2 v) 0

theorem evF_eq (e : Env) (l : LinT) : evF e l = l.ev e := by
  have : ∀ (l : LinT) (a : F), l.foldl (fun a τ => let v := τ.1.ev e; if v = 0 then a else a + mul1 τ.2 v) a =
      a + l.ev e := by
    intro l; induction l with
    | nil => intro a; simp [LinT.ev]
    | cons τ l ih =>
      intro a; rw [List.foldl_cons, ih]
      simp only [LinT.ev, List.map_cons, List.sum_cons, mul1_eq]
      split_ifs with h
      · rw [h, mul_zero, zero_add]
      · ring
  rw [evF, this, zero_add]

/-- `tm` of the three matrices in one pass (row weights `gt`). -/
def tmG3 (gt : ℕ → F) (e : Env) : ℕ → List RowT → F3
  | _, [] => (0, 0, 0)
  | X, r :: rows =>
    let a := evF e r.a
    let b := evF e r.b
    let c := evF e r.c
    if a = 0 ∧ b = 0 ∧ c = 0 then tmG3 gt e (X + 1) rows
    else let w := gt X; add3 (mulZ w a, mulZ w b, mulZ w c) (tmG3 gt e (X + 1) rows)

theorem tmG3_tm (gt t : ℕ → F) (e : Env) (hgt : ∀ x, gt x = gN 20 t x) : ∀ (X : ℕ) (rows : List RowT),
    tmG3 gt e X rows = (tm .a t e X rows, tm .b t e X rows, tm .c t e X rows)
  | _, [] => rfl
  | X, r :: rows => by
    rw [tmG3, tmG3_tm gt t e hgt (X + 1) rows]
    simp only [tm, Mat.t, add3, hgt, evF_eq, mulZ_eq]
    split_ifs with h
    · obtain ⟨ha, hb, hc⟩ := h
      rw [ha, hb, hc]; simp
    · rfl

theorem tmG3_eq (gt t : ℕ → F) (e : Env) (hgt : ∀ x, gt x = gN 20 t x) (X : ℕ) (rows : List RowT) :
    tmG3 gt e X rows = (tmG .a gt e X rows, tmG .b gt e X rows, tmG .c gt e X rows) := by
  rw [tmG3_tm gt t e hgt, tmG_eq _ gt t e hgt, tmG_eq _ gt t e hgt, tmG_eq _ gt t e hgt]

/-! ## Forms that vanish -/

/-- Every term of the form reads a local. -/
def locOnly (f : LinT) : Bool := f.all fun τ => match τ.1 with | .loc _ => true | _ => false

/-- No term of the form reads a local. -/
def inpOnly (f : LinT) : Bool := f.all fun τ => match τ.1 with | .loc _ => false | _ => true

theorem ev_locOnly {e : Env} (h : ∀ x, e.loc x = 0) : ∀ {f : LinT}, locOnly f = true → f.ev e = 0
  | [], _ => rfl
  | (w, c) :: f, hf => by
    simp only [locOnly, List.all_cons, Bool.and_eq_true] at hf
    have ih := ev_locOnly h (f := f) hf.2
    simp only [LinT.ev, List.map_cons, List.sum_cons] at ih ⊢
    rw [ih]
    cases w with
    | loc k => simp [Wire.ev, h]
    | _ => simp at hf

theorem ev_inpOnly {e : Env} (h1 : e.one = 0) (h : ∀ i, e.inp i = 0) : ∀ {f : LinT}, inpOnly f = true → f.ev e = 0
  | [], _ => rfl
  | (w, c) :: f, hf => by
    simp only [inpOnly, List.all_cons, Bool.and_eq_true] at hf
    have ih := ev_inpOnly h1 h (f := f) hf.2
    simp only [LinT.ev, List.map_cons, List.sum_cons] at ih ⊢
    rw [ih]
    cases w with
    | loc k => simp at hf
    | one => simp [Wire.ev, h1]
    | inp i => simp [Wire.ev, h]

/-- The form vanishes at the wires (by the flags). -/
def skipF (zl zi : Bool) (f : LinT) : Bool := (zl && locOnly f) || (zi && inpOnly f)

theorem ev_skip {e : Env} {zl zi : Bool} (hl : zl = true → ∀ x, e.loc x = 0)
    (hi : zi = true → e.one = 0 ∧ ∀ i, e.inp i = 0) {f : LinT} (h : skipF zl zi f = true) : f.ev e = 0 := by
  simp only [skipF, Bool.or_eq_true, Bool.and_eq_true] at h
  rcases h with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · exact ev_locOnly (hl h1) h2
  · exact ev_inpOnly (hi h1).1 (hi h1).2 h2

namespace Rep
variable (R : Rep)

/-- A placeholder's instance sums at both carries, its forms evaluated once (`0` if they vanish). -/
def zPair (A : Array F) (t : ℕ → F) (e : Env) (X : ℕ) (S0 S1 : F) (zl zi : Bool) : Ph → F × F
  | .cst f => if skipF zl zi f then (0, 0) else let v := evF e f; (v * S0, v * S1)
  | .var fs =>
    let vs := (Array.range R.n).map fun i => let f := fs.getD i []; if skipF zl zi f then 0 else evF e f
    (sumL (fun i => mulZ (R.tAt A t X i) (vs.getD i 0)) (List.range R.n),
      sumL (fun i => mulZ (R.tAt A t X (i + 1)) (vs.getD i 0)) (List.range R.n))

/-- **The per-call sums, placeholders evaluated once** (`ctx`'s). -/
def ctx3 (t u : ℕ → F) (e : Env) (cl X K : ℕ) (zl zi : Bool) : Cx :=
  let tA := R.tArr t X
  let uA := R.tArr u (cl + K)
  let S0 := R.sS tA t X 0
  let S1 := R.sS tA t X 1
  ⟨tA, uA, S0, S1,
    #[R.sD tA uA t u X (cl + K) 0 0, R.sD tA uA t u X (cl + K) 0 1, R.sD tA uA t u X (cl + K) 1 0,
      R.sD tA uA t u X (cl + K) 1 1],
    R.ph.map (R.zPair tA t e X S0 S1 zl zi), loTab R.p t, loTab R.p u⟩

theorem zPair_eq {zl zi : Bool} (t : ℕ → F) (e : Env) (X : ℕ) (hl : zl = true → ∀ x, e.loc x = 0)
    (hi : zi = true → e.one = 0 ∧ ∀ i, e.inp i = 0) (j : ℕ) :
    R.zPair (R.tArr t X) t e X (R.sS (R.tArr t X) t X 0) (R.sS (R.tArr t X) t X 1) zl zi (R.ph.getD j (.cst [])) =
      (R.sZ (R.tArr t X) t e X j 0, R.sZ (R.tArr t X) t e X j 1) := by
  unfold sZ
  cases hp : R.ph.getD j (.cst []) with
  | cst f =>
    simp only [zPair]
    split_ifs with h
    · rw [ev_skip hl hi h]; simp
    · rw [evF_eq]
  | var fs =>
    simp only [zPair]
    have hv : ∀ i ∈ List.range R.n, ((Array.range R.n).map fun i =>
        if skipF zl zi (fs.getD i []) then 0 else evF e (fs.getD i [])).getD i 0 = (fs.getD i []).ev e := fun i hi' => by
      rw [Array.getD_eq_getD_getElem?, Array.getElem?_map, Array.getElem?_range]
      simp only [List.mem_range.1 hi', if_true, Option.map_some, Option.getD_some]
      split_ifs with h
      · exact (ev_skip hl hi h).symm
      · exact evF_eq e _
    simp only [sumL_eq, Nat.add_zero, mulZ_eq]
    refine Prod.ext ?_ ?_ <;> refine congrArg List.sum (List.map_congr_left fun i hi' => ?_) <;> rw [hv i hi']

/-- **`ctx3` is `ctx`** (the flags' hypotheses: the locals vanish; `one` and the inputs vanish). -/
theorem ctx3_eq {zl zi : Bool} (t u : ℕ → F) (e : Env) (cl X K : ℕ) (hl : zl = true → ∀ x, e.loc x = 0)
    (hi : zi = true → e.one = 0 ∧ ∀ i, e.inp i = 0) : R.ctx3 t u e cl X K zl zi = R.ctx t u e cl X K := by
  simp only [ctx3, ctx, Cx.mk.injEq, true_and, and_true]
  apply Array.ext
  · simp
  · intro j h1 h2
    simp only [Array.getElem_map, Array.getElem_range]
    have := R.zPair_eq t e X hl hi j
    rw [Array.getD_eq_getD_getElem?, Array.getElem?_eq_getElem (by simpa using h1), Option.getD_some] at this
    exact this

/-- A pattern row's form from the context (V5: a local's term is skipped when `lam = 0`, where
`wv` is `0`; `fv_eq`). -/
def fv (cx : Cx) (t u : ℕ → F) (e : Env) (lam : F) (cl X K c : ℕ) (l : LinT) : F :=
  l.foldl (fun a τ => match τ.1 with
    | .loc k => if lam = 0 then a else a + mul1 τ.2 (R.wv cx t u e lam cl X K c (.loc k))
    | w => a + mul1 τ.2 (R.wv cx t u e lam cl X K c w)) 0

theorem fv_eq (cx : Cx) (t u : ℕ → F) (e : Env) (lam : F) (cl X K c : ℕ) (l : LinT) :
    R.fv cx t u e lam cl X K c l = sumL (fun τ => mul1 τ.2 (R.wv cx t u e lam cl X K c τ.1)) l := by
  unfold fv sumL
  suffices h : ∀ a : F, l.foldl (fun a τ => match τ.1 with
      | .loc k => if lam = 0 then a else a + mul1 τ.2 (R.wv cx t u e lam cl X K c (.loc k))
      | w => a + mul1 τ.2 (R.wv cx t u e lam cl X K c w)) a =
      l.foldl (fun a τ => a + mul1 τ.2 (R.wv cx t u e lam cl X K c τ.1)) a from h 0
  induction l with
  | nil => intro a; rfl
  | cons τ l ih =>
    intro a
    simp only [List.foldl_cons]
    rw [← ih]
    congr 1
    obtain ⟨w, d⟩ := τ
    cases w with
    | loc k =>
      dsimp only
      split_ifs with h
      · simp [wv, h, mul1_eq]
      · rfl
    | one => rfl
    | inp j => rfl

/-- **One pass over the pattern's rows, three matrices** (V5: `fv`, and no product for a row whose
form is `0`). -/
def pass3 (cx : Cx) (t u : ℕ → F) (e : Env) (lam : F) (cl X K : ℕ) : ℕ → List RowT → F3
  | _, [] => (0, 0, 0)
  | r, row :: rows =>
    let w := cx.tl.getD (R.low X r) 0
    let c := R.car X r
    let f := R.fv cx t u e lam cl X K c
    add3 (mulZ w (f row.a), mulZ w (f row.b), mulZ w (f row.c)) (pass3 cx t u e lam cl X K (r + 1) rows)

theorem pass3_eq (cx : Cx) (t u : ℕ → F) (e : Env) (lam : F) (cl X K : ℕ) : ∀ (r : ℕ) (rows : List RowT),
    R.pass3 cx t u e lam cl X K r rows =
      (R.pass .a cx t u e lam cl X K r rows, R.pass .b cx t u e lam cl X K r rows, R.pass .c cx t u e lam cl X K r rows)
  | _, [] => rfl
  | r, row :: rows => by
    rw [pass3, pass3_eq cx t u e lam cl X K (r + 1) rows]
    simp only [pass, Mat.t, add3, mulZ_eq, fv_eq, mul1_eq]

end Rep

/-- **The prepared segments' value, three matrices**, rows from `X0` on. -/
def psVal3 (gt t u : ℕ → F) (e : Env) (lam : F) (cl X0 : ℕ) (zl zi : Bool) : List PS → F3
  | [] => (0, 0, 0)
  | .rows X rs :: l => add3 (tmG3 gt e (X0 + X) rs) (psVal3 gt t u e lam cl X0 zl zi l)
  | .rep X K R pr :: l =>
    add3 (R.pass3 (R.ctx3 t u e cl (X0 + X) K zl zi) t u e lam cl (X0 + X) K 0 pr)
      (psVal3 gt t u e lam cl X0 zl zi l)

theorem psVal3_eq (gt t u : ℕ → F) (e : Env) (lam : F) (cl X0 : ℕ) {zl zi : Bool} (hgt : ∀ x, gt x = gN 20 t x)
    (hl : zl = true → ∀ x, e.loc x = 0) (hi : zi = true → e.one = 0 ∧ ∀ i, e.inp i = 0) :
    ∀ l : List PS, psVal3 gt t u e lam cl X0 zl zi l =
      (psVal .a gt t u e lam cl X0 l, psVal .b gt t u e lam cl X0 l, psVal .c gt t u e lam cl X0 l)
  | [] => rfl
  | .rows X rs :: l => by
    rw [psVal3, psVal3_eq gt t u e lam cl X0 hgt hl hi l, tmG3_eq gt t e hgt]; rfl
  | .rep X K R pr :: l => by
    rw [psVal3, psVal3_eq gt t u e lam cl X0 hgt hl hi l, R.ctx3_eq t u e cl _ K hl hi, Rep.pass3_eq]; rfl

end Tpl
end FR

end G6_FRVIRTplCFF

section G6_FRNodeRows4RepCFW

-- New for `flock-recursive` (track CF2): prototype 0's replay blocks split for the plan.

/-!
# Prototype 0's replay blocks, split for the plan

The plan keeps prototype 0's replay rows as **row blocks** (their rows at their indices, grouped
sparse) and **`rsWeight` ops prepared** (`kpOf`, at their first rows; their rows never built):
`blkGo` walks the blocks (`arBlk0`), the `rsWeight` op's row count from its preparation (`kpLen_eq`).
**`blkGo_val`**: the row blocks' value plus the ops' values is the rows' value (`rm`).
-/

namespace FR
namespace Rev4
open RecursionFast Circ TEval Tpl

/-- A prepared `rsWeight` op's row count. -/
def kpLen (kp : KP) : ℕ :=
  if kp.ok then (kp.subs.map fun p => p.2.2).sum + kp.mux.length + kp.copy.length else kp.alt.length

theorem copyRows_length (P : Params) (outs : List Slot) (o : List Lin) :
    (N4s.copyRows P outs o).length = (N4s.outF outs).length := by
  simp [N4s.copyRows]

/-- **The prepared op's row count is its rows'.** -/
theorem kpLen_eq (P : Params) (cs : CS) (op : Op) (outs : List Slot) :
    kpLen (kpOf P cs op outs) = (N4s.kRows N4s.kRS N4s.repB N4s.cbRS P cs op outs).length := by
  unfold kpOf N4s.kRows
  cases hbs : N4s.kBlocks N4s.kRS cs op with
  | none => simp [kpLen]
  | some bs =>
    simp only []
    by_cases hc : (N4s.outsOk N4s.kRS.tys outs && bs.all (fun b => N4s.kRS.inOk b.1) &&
        (N4s.kIns P bs ++ N4s.outF outs).all (linLt N4s.repB)) = true
    · rw [if_pos hc, if_pos hc]
      simp only [kpLen, ite_true, List.length_append, List.length_map, copyRows_length, N4s.rowsTR_eq]
      have hT : N4s.kTpl N4s.kRS op bs = kmuxT (N4s.kSig (bs.map fun b => b.2.length)) (bs.map fun b => b.2.length).sum 2
          ((rsTs bs).map fun T => (⟨sgGates T.1 0, T.2⟩ : Tpl)) := by
        simp only [N4s.kTpl, rsTs, List.map_cons, List.map_nil, ← rsT_segs]; rfl
      rw [hT]
      simp only [kmuxT, tpl_rows_eq, rowsAt_append, List.length_append, rowsAt_length, nrows_subsG,
        List.map_map, Function.comp_def, nrows_sgGates, subsG_two, nlocs_subsG, nlocs_sgGates]
      simp only [muxG, rsTs, List.length_cons, List.length_nil, List.map_cons, List.map_nil,
        show (0 + 1 + 1 + 1 : ℕ) = 3 from rfl]
    · rw [if_neg hc, if_neg hc]; simp [kpLen]

/-- **The blocks split**, from row `X` (accumulators reversed): the row blocks' rows at their
indices, the `rsWeight` ops prepared at their first rows. -/
def blkGo : ℕ → List RBlk → List (Row × ℕ) → List (ℕ × KP) → List (Row × ℕ) × List (ℕ × KP)
  | _, [], a, b => (a, b)
  | X, .sp l :: bs, a, b => blkGo (X + l.length) bs ((l.zipIdx X).reverseAux a) b
  | X, .rs P cs op outs :: bs, a, b =>
    let kp := kpOf P cs op outs
    blkGo (X + kpLen kp) bs a ((X, kp) :: b)

/-- Indexed rows' value (matrix `s`, row point `t`, cells at `w`). -/
def spV (s : Mat) (t : ℕ → F) (w : Asg) (l : List (Row × ℕ)) : F :=
  (l.map fun p => gN 20 t p.2 * (s.r p.1).ev w).sum

theorem spV_append (s : Mat) (t : ℕ → F) (w : Asg) (a b : List (Row × ℕ)) :
    spV s t w (a ++ b) = spV s t w a + spV s t w b := by simp [spV]

theorem spV_reverse (s : Mat) (t : ℕ → F) (w : Asg) (a : List (Row × ℕ)) :
    spV s t w a.reverse = spV s t w a := by simp [spV, List.sum_reverse]

theorem spV_zipIdx (s : Mat) (t : ℕ → F) (w : Asg) :
    ∀ (X : ℕ) (l : List Row), spV s t w (l.zipIdx X) = rm s t w X l
  | _, [] => rfl
  | X, r :: l => by
    rw [List.zipIdx_cons, rm, ← spV_zipIdx s t w (X + 1) l]
    simp [spV]

/-- **The split's value**: the row blocks' plus the prepared ops' (any `V` that is an op's rows' value
at its first row). -/
theorem blkGo_val (s : Mat) (t : ℕ → F) (w : Asg) (V : ℕ → KP → F)
    (hV : ∀ X P cs op outs, V X (kpOf P cs op outs) = rm s t w X (N4s.kRows N4s.kRS N4s.repB N4s.cbRS P cs op outs)) :
    ∀ (X : ℕ) (bs : List RBlk) (a : List (Row × ℕ)) (b : List (ℕ × KP)),
      spV s t w (blkGo X bs a b).1 + ((blkGo X bs a b).2.map fun q => V q.1 q.2).sum =
        spV s t w a + (b.map fun q => V q.1 q.2).sum + rm s t w X (bs.flatMap RBlk.rows)
  | _, [], a, b => by simp [blkGo, rm]
  | X, .sp l :: bs, a, b => by
    rw [blkGo, blkGo_val s t w V hV _ bs, List.flatMap_cons, rm_append, List.reverseAux_eq, spV_append,
      spV_reverse, spV_zipIdx]
    simp only [RBlk.rows]; ring
  | X, .rs P cs op outs :: bs, a, b => by
    rw [blkGo, blkGo_val s t w V hV _ bs, List.flatMap_cons, rm_append, List.map_cons, List.sum_cons, hV,
      kpLen_eq]
    simp only [RBlk.rows]; ring

/-- The split's row count. -/
theorem blkGo_len : ∀ (X : ℕ) (bs : List RBlk) (a : List (Row × ℕ)) (b : List (ℕ × KP)),
    (blkGo X bs a b).1.length + ((blkGo X bs a b).2.map fun q => kpLen q.2).sum =
      a.length + (b.map fun q => kpLen q.2).sum + (bs.flatMap RBlk.rows).length
  | _, [], a, b => by simp [blkGo]
  | X, .sp l :: bs, a, b => by
    rw [blkGo, blkGo_len _ bs, List.flatMap_cons, List.length_append, List.reverseAux_eq, List.length_append,
      List.length_reverse, List.length_zipIdx]
    simp only [RBlk.rows]; ring
  | X, .rs P cs op outs :: bs, a, b => by
    rw [blkGo, blkGo_len _ bs, List.flatMap_cons, List.length_append, List.map_cons, List.sum_cons, kpLen_eq]
    simp only [RBlk.rows]; ring

/-! ## The cell weights by split tables -/

/-- `wF` with an eq function. -/
def wFA (gu : ℕ → F) : Asg := fun c => if c < N4s.repB then gu c else 0

/-- `wL` with an eq function. -/
def wLA (gu : ℕ → F) : Asg := fun c => if c < N4s.repB then 0 else gu (c - N4s.repB)

theorem wFA_eq (gu u : ℕ → F) (h : ∀ x, gu x = gN 20 u x) : wFA gu = wF u := by
  funext c; simp only [wFA, wF, h]

theorem wLA_eq (gu u : ℕ → F) (h : ∀ x, gu x = gN 20 u x) : wLA gu = wL u := by
  funext c; simp only [wLA, wL, h]

theorem wF_cb (u : ℕ → F) (x : ℕ) : wF u (N4s.cbRS + x) = 0 * gN 20 u (2 ^ 16 + x) := by
  have h : ¬ N4s.cbRS + x < N4s.repB := by unfold N4s.cbRS; exact Nat.not_lt.2 (by omega)
  rw [wF, if_neg h, zero_mul]

theorem wL_cb (u : ℕ → F) (x : ℕ) : wL u (N4s.cbRS + x) = 1 * gN 20 u (2 ^ 16 + x) := by
  have h : ¬ N4s.cbRS + x < N4s.repB := by unfold N4s.cbRS; exact Nat.not_lt.2 (by omega)
  have e : N4s.cbRS + x - N4s.repB = 2 ^ 16 + x := by unfold N4s.cbRS; omega
  rw [wL, if_neg h, e, one_mul]

/-- The prepared ops' values, three matrices. -/
def kpsV3 (gt gu t u : ℕ → F) (w : Asg) (lam : F) (kps : List (ℕ × KP)) : F3 :=
  ((kps.map fun q => kopV .a gt gu t u w lam q.1 q.2).sum, (kps.map fun q => kopV .b gt gu t u w lam q.1 q.2).sum,
    (kps.map fun q => kopV .c gt gu t u w lam q.1 q.2).sum)

theorem rowsVal_spF (s : Mat) (t u : ℕ → F) (l : List (Row × ℕ)) :
    rowsVal (RingHom.id F) s 20 20 t u (l.map fun p => (p.2, rowFr p.1)) = spV s t (wF u) l := by
  simp only [rowsVal, spV, List.map_map, Function.comp_def, Mat.r_rowFr, linE_linFr]

theorem rowsVal_spL (s : Mat) (t u : ℕ → F) (l : List (Row × ℕ)) :
    rowsVal (RingHom.id F) s 20 20 t u (l.map fun p => (p.2, rowLoc p.1)) = spV s t (wL u) l := by
  simp only [rowsVal, spV, List.map_map, Function.comp_def, Mat.r_rowLoc, linE_linLoc]

/-- **The split's value at the plan's weights**: the row blocks' plus the ops' closed forms. -/
theorem blk_val (s : Mat) (t u : ℕ → F) (w : Asg) (lam : F) (hw : ∀ x, w (N4s.cbRS + x) = lam * gN 20 u (2 ^ 16 + x))
    (bs : List RBlk) :
    spV s t w (blkGo 0 bs [] []).1 + ((blkGo 0 bs [] []).2.map fun q => kopV s (gN 20 t) (gN 20 u) t u w lam q.1 q.2).sum =
      rm s t w 0 (bs.flatMap RBlk.rows) := by
  have h := blkGo_val s t w (fun X kp => kopV s (gN 20 t) (gN 20 u) t u w lam X kp)
    (fun X P cs op outs => kopV_eq s _ _ t u w lam (fun _ => rfl) (fun _ => rfl) hw P cs op outs X) 0 bs [] []
  simpa [spV] using h

/-! ## Prototype `π`'s ask rows and replay blocks (the plan's; `arBlk0` at `0`) -/

def arBlkN (π : ℕ) : List Row × List RBlk :=
  let r := trailMB (N4s.XofC π) (protoLay π) (protoP π) (askTG π) (N4s.rtC1c π) blk0 []
    (CS.init (baseR π)) none 0 (protoProg π).ops [] []
  (r.1.reverse, r.2.reverse)

theorem arBlkN_zero : arBlkN 0 = arBlk0 := rfl

/-! ## The structural fit (`RepFit` without the `rsWeight` rows)

A prepared op fits if its one and input forms' cells fit, its sub-templates' locals are below their
counts (`psLocOk`), the mux rows' locals and the sub-templates' total below `lRoom` (so the locals'
cells `cbRS + k` stay in `[repB, repB + 2^20)`), and its copy rows' cells fit. Sound, not complete:
the plan keeps the fallback. -/

/-- A form's cells fit prototype 0's replay. -/
def linCellOk (l : Lin) : Bool := l.all fun t => repCellOk 0 t.1

def rowCellOk (r : Row) : Bool := linCellOk r.a && linCellOk r.b && linCellOk r.c

theorem rowCellOk_iff (r : Row) : rowCellOk r = true ↔ ∀ t ∈ r.a ++ r.b ++ r.c, repCellOk 0 t.1 = true := by
  simp only [rowCellOk, linCellOk, Bool.and_eq_true, List.all_eq_true, List.mem_append]
  constructor
  · rintro ⟨⟨ha, hb⟩, hc⟩ t ((ht | ht) | ht)
    exacts [ha t ht, hb t ht, hc t ht]
  · intro h; exact ⟨⟨fun t ht => h t (Or.inl (Or.inl ht)), fun t ht => h t (Or.inl (Or.inr ht))⟩,
      fun t ht => h t (Or.inr ht)⟩

/-- The template locals' room above `cbRS`. -/
abbrev lRoom : ℕ := 2 ^ 20 - 2 ^ 16

theorem cb_cellOk {k : ℕ} (hk : k < lRoom) : repCellOk 0 (N4s.cbRS + k) = true := by
  have hM : slotM4 = 1048576 := rfl
  have hR : lRoom = 983040 := by norm_num [lRoom]
  have hk' : k < 983040 := hR ▸ hk
  have h1 : N4s.repB ≤ N4s.cbRS + k := by unfold N4s.cbRS; omega
  have h2 : N4s.cbRS + k < N4s.repB + slotM4 := by unfold N4s.cbRS; rw [hM]; omega
  unfold repCellOk
  rw [if_pos rfl, decide_eq_true h1, decide_eq_true h2, Bool.and_true, Bool.or_true]

theorem mem_smulC {c : F} {l : Lin} {t : ℕ × F} (h : t ∈ l.smul c) : ∃ t' ∈ l, t.1 = t'.1 := by
  simp only [Lin.smul, List.mem_map] at h
  obtain ⟨t', ht', rfl⟩ := h
  exact ⟨t', ht', rfl⟩

theorem instLin_cellOk {one : Lin} {ins : List Lin} (h1 : linCellOk one = true)
    (hi : ∀ x ∈ ins, linCellOk x = true) {l : LinT} (hl : locLt lRoom l = true) :
    linCellOk (instLin one ins N4s.cbRS l) = true := by
  have hl' := locLt_iff.1 hl
  unfold linCellOk at h1 ⊢
  rw [List.all_eq_true] at h1 ⊢
  intro t ht
  obtain ⟨⟨w, c⟩, hw, ht⟩ := List.mem_flatMap.1 ht
  cases w with
  | one =>
    obtain ⟨t', ht', he⟩ := mem_smulC ht
    rw [he]; exact h1 t' ht'
  | inp i =>
    obtain ⟨t', ht', he⟩ := mem_smulC ht
    rw [he]
    rw [List.getD_eq_getElem?_getD] at ht'
    cases hx : ins[i]? with
    | none => rw [hx] at ht'; simp at ht'
    | some x =>
      rw [hx] at ht'
      exact List.all_eq_true.1 (hi x (List.mem_of_getElem? hx)) t' ht'
  | loc k =>
    simp only [List.mem_singleton] at ht
    rw [ht]; exact cb_cellOk (hl' k c hw)

theorem instRow_cellOk {one : Lin} {ins : List Lin} (h1 : linCellOk one = true)
    (hi : ∀ x ∈ ins, linCellOk x = true) {r : RowT} (hr : rowLocLt lRoom r = true) :
    rowCellOk (instRow one ins N4s.cbRS r) = true := by
  simp only [rowLocLt, Bool.and_eq_true] at hr
  simp only [rowCellOk, instRow, Bool.and_eq_true]
  exact ⟨⟨instLin_cellOk h1 hi hr.1.1, instLin_cellOk h1 hi hr.1.2⟩, instLin_cellOk h1 hi hr.2⟩

theorem locLt_le {m M : ℕ} (h : m ≤ M) {l : LinT} (hl : locLt m l = true) : locLt M l = true :=
  locLt_iff.2 fun k c hk => lt_of_lt_of_le (locLt_iff.1 hl k c hk) h

/-- The sub-templates' rows (substituted, locals one after the other from `k`) read locals below
`k` plus their count. -/
theorem subsG_rows_loc (σ : ℕ → ℕ → LinT) (hσ : ∀ j i, locLt 0 (σ j i) = true) :
    ∀ (ts : List Tpl) (j k : ℕ), (∀ T ∈ ts, ∀ r ∈ rowsAt T.gates 0, rowLocLt (nlocs T.gates) r = true) →
      ∀ r ∈ rowsAt (subsG σ ts j k).1 k, rowLocLt (k + (ts.map fun T => nlocs T.gates).sum) r = true
  | [], _, _, _, r, hr => by simp [subsG] at hr
  | T :: ts, j, k, hT, r, hr => by
    simp only [subsG, rowsAt_append, List.mem_append, nlocs_subL] at hr
    rcases hr with hr | hr
    · have hs := rowsAt_sub (σ j) k T.gates 0
      rw [Nat.add_zero] at hs
      rw [hs] at hr
      obtain ⟨r0, hr0, rfl⟩ := List.mem_map.1 hr
      refine rowLocLt_mono ?_ (rowLocLt_sub (hT T List.mem_cons_self r0 hr0)
        (fun i => locLt_le (Nat.zero_le _) (hσ j i)) le_rfl)
      simp only [List.map_cons, List.sum_cons]; omega
    · have := subsG_rows_loc σ hσ ts (j + 1) (k + nlocs T.gates) (fun T' hT' => hT T' (List.mem_cons_of_mem _ hT')) r hr
      simpa [Nat.add_assoc] using this

theorem kSig_loc (ws : List ℕ) (j i : ℕ) : locLt 0 (N4s.kSig ws j i) = true := by
  unfold N4s.kSig; split_ifs <;> rfl

/-- **A prepared op's structural fit.** -/
def kpFit (kp : KP) : Bool :=
  if kp.ok then linCellOk kp.one && kp.ins.all linCellOk && kp.subs.all (fun x => psLocOk x.2.1 x.1) &&
    kp.mux.all (rowLocLt lRoom) && kp.copy.all rowCellOk && decide ((kp.subs.map fun x => x.2.1).sum ≤ lRoom)
  else kp.alt.all rowCellOk

/-- **A fitting prepared op's rows fit.** -/
theorem kpFit_rows (P : Params) (cs : CS) (op : Op) (outs : List Slot) (h : kpFit (kpOf P cs op outs) = true) :
    ∀ r ∈ N4s.kRows N4s.kRS N4s.repB N4s.cbRS P cs op outs, rowCellOk r = true := by
  unfold kpOf at h
  unfold N4s.kRows
  cases hbs : N4s.kBlocks N4s.kRS cs op with
  | none => simp only [hbs, kpFit] at h; simpa using h
  | some bs =>
    simp only [hbs] at h ⊢
    by_cases hc : (N4s.outsOk N4s.kRS.tys outs && bs.all (fun b => N4s.kRS.inOk b.1) &&
        (N4s.kIns P bs ++ N4s.outF outs).all (linLt N4s.repB)) = true
    · rw [if_pos hc] at h ⊢
      simp only [kpFit, ite_true, Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq] at h
      obtain ⟨⟨⟨⟨⟨h1, hins⟩, hsubs⟩, hmux⟩, hcopy⟩, hN⟩ := h
      have hT : N4s.kTpl N4s.kRS op bs = kmuxT (N4s.kSig (bs.map fun b => b.2.length)) (bs.map fun b => b.2.length).sum 2
          ((rsTs bs).map fun T => (⟨sgGates T.1 0, T.2⟩ : Tpl)) := by
        simp only [N4s.kTpl, rsTs, List.map_cons, List.map_nil, ← rsT_segs]; rfl
      rw [N4s.rowsTR_eq, hT]
      simp only [kmuxT, tpl_rows_eq, rowsAt_append, List.map_append, List.mem_append, List.mem_map]
      simp only [nlocs_subsG, subsG_two, List.map_map, Function.comp_def, nlocs_sgGates] at hmux hcopy hN ⊢
      have h3 : (List.map (fun T => ({ gates := sgGates T.1 0, outs := T.2 } : Tpl)) (rsTs bs)).length = 3 := by
        simp [rsTs]
      simp only [muxG] at hmux
      rw [h3, Nat.zero_add]
      rintro r ((⟨a, ha, rfl⟩ | ⟨a, ha, rfl⟩) | hr)
      · apply instRow_cellOk h1 hins
        have := subsG_rows_loc _ (kSig_loc _) _ 0 0 (fun T hT r hr => ?_) a ha
        · refine rowLocLt_mono ?_ this
          simpa [nlocs_sgGates, List.map_map, Function.comp_def] using hN
        · obtain ⟨T', hT', rfl⟩ := List.mem_map.1 hT
          rw [nlocs_sgGates]
          exact psLocOk_rows _ 0 0 T'.1 (hsubs _ (List.mem_map_of_mem hT')) r hr
      · exact instRow_cellOk h1 hins (hmux a ha)
      · exact hcopy r hr
    · rw [if_neg hc] at h ⊢
      simp only [kpFit] at h; simpa using h

theorem blkGo_sub : ∀ (X : ℕ) (bs : List RBlk) (a : List (Row × ℕ)) (b : List (ℕ × KP)),
    (∀ p ∈ a, p ∈ (blkGo X bs a b).1) ∧ ∀ x ∈ b, x ∈ (blkGo X bs a b).2
  | _, [], a, b => ⟨fun _ h => h, fun _ h => h⟩
  | X, .sp l :: bs, a, b => by
    obtain ⟨h1, h2⟩ := blkGo_sub (X + l.length) bs ((l.zipIdx X).reverseAux a) b
    refine ⟨fun p hp => h1 p ?_, h2⟩
    rw [List.reverseAux_eq]; exact List.mem_append_right _ hp
  | X, .rs P cs op outs :: bs, a, b => by
    obtain ⟨h1, h2⟩ := blkGo_sub (X + kpLen (kpOf P cs op outs)) bs a ((X, kpOf P cs op outs) :: b)
    exact ⟨h1, fun x hx => h2 x (List.mem_cons_of_mem _ hx)⟩

/-- Every replay row is a row block's (at some index) or a prepared op's. -/
theorem blkGo_mem : ∀ (X : ℕ) (bs : List RBlk) (a : List (Row × ℕ)) (b : List (ℕ × KP)),
    ∀ r ∈ bs.flatMap RBlk.rows, (∃ i, (r, i) ∈ (blkGo X bs a b).1) ∨
      ∃ Y P cs op outs, (Y, kpOf P cs op outs) ∈ (blkGo X bs a b).2 ∧
        r ∈ N4s.kRows N4s.kRS N4s.repB N4s.cbRS P cs op outs
  | _, [], _, _, r, hr => by simp only [List.flatMap_nil, List.not_mem_nil] at hr
  | X, .sp l :: bs, a, b, r, hr => by
    rw [List.flatMap_cons, List.mem_append] at hr
    rcases hr with hr | hr
    · left
      obtain ⟨i, hi⟩ : ∃ i, (r, i) ∈ l.zipIdx X := by
        obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem hr
        exact ⟨X + j, List.mk_mem_zipIdx_iff_le_and_getElem?_sub.2 ⟨by omega, by simp only [RBlk.rows] at hj ⊢; simp [hj]⟩⟩
      refine ⟨i, (blkGo_sub _ bs _ b).1 _ ?_⟩
      rw [List.reverseAux_eq]; exact List.mem_append_left _ (List.mem_reverse.2 hi)
    · exact blkGo_mem _ bs _ b r hr
  | X, .rs P cs op outs :: bs, a, b, r, hr => by
    rw [List.flatMap_cons, List.mem_append] at hr
    rcases hr with hr | hr
    · exact Or.inr ⟨X, P, cs, op, outs, (blkGo_sub _ bs a _).2 _ List.mem_cons_self, hr⟩
    · exact blkGo_mem _ bs _ _ r hr

/-- **The structural `RepFit` check** on the split (prototype 0). -/
def repFitS (q : List (Row × ℕ) × List (ℕ × KP)) : Bool :=
  decide (q.1.length + (q.2.map fun x => kpLen x.2).sum ≤ slotM4) && q.1.all (fun p => rowCellOk p.1) &&
    q.2.all fun x => kpFit x.2

theorem repFitS_spec (bs : List RBlk) (h : repFitS (blkGo 0 bs [] []) = true) :
    repFitB 0 (bs.flatMap RBlk.rows) = true := by
  simp only [repFitS, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true] at h
  obtain ⟨⟨hl, hsp⟩, hkp⟩ := h
  have hlen := blkGo_len 0 bs [] []
  simp only [List.length_nil, List.map_nil, List.sum_nil, Nat.zero_add] at hlen
  simp only [repFitB, ↓reduceIte, Bool.and_eq_true, decide_eq_true_eq]
  refine ⟨by omega, List.all_eq_true.2 fun r hr => List.all_eq_true.2 ((rowCellOk_iff r).1 ?_)⟩
  rcases blkGo_mem 0 bs [] [] r hr with ⟨i, hi⟩ | ⟨Y, P, cs, op, outs, hm, hr⟩
  · exact hsp _ hi
  · exact kpFit_rows P cs op outs (hkp _ hm) r hr

/-! ## The prepared op's value, three matrices in one pass (CF2 step 3)

The sub-templates' inputs from arrays (block `j`'s slice of the op's inputs: no `kSig`/`pullE` per
wire), `psVal3` (row weights and per-call sums once for the three matrices; vanishing placeholders
skipped: the frame part's locals are `0`, the local part's `one` and inputs are `0`). -/

/-- `rmG` of the three matrices in one pass. -/
def rmG3 (gt : ℕ → F) (w : Asg) (X : ℕ) (rows : List Row) : F3 :=
  (rmG .a gt w X rows, rmG .b gt w X rows, rmG .c gt w X rows)

/-- The sub-templates' value, three matrices; block `j`'s inputs `vin[off …]`. -/
def subsV3 (gt t u : ℕ → F) (one : F) (vin : Array F) (lam : F) (gu : ℕ → F) (zl zi : Bool) (ws : List ℕ) :
    List (List PS × ℕ × ℕ) → ℕ → ℕ → ℕ → ℕ → F3
  | [], _, _, _, _ => (0, 0, 0)
  | (ps, nl, nr) :: l, j, off, k, X =>
    let wj := ws.getD j 0
    let vj := (Array.range wj).map fun i => vin.getD (off + i) 0
    let e : Env := ⟨one, fun i => vj.getD i 0, fun x => if lam = 0 then 0 else mul1 lam (gu (2 ^ 16 + (k + x)))⟩
    add3 (psVal3 gt t u e lam (2 ^ 16 + k) X zl zi ps) (subsV3 gt t u one vin lam gu zl zi ws l (j + 1) (off + wj) (k + nl) (X + nr))

/-- **The prepared `rsWeight` op's value, three matrices.** -/
def kopV3 (gt gu t u : ℕ → F) (w : Asg) (lam : F) (X : ℕ) (kp : KP) : F3 :=
  if kp.ok then
    let vin := (kp.ins.map (Lin.ev w)).toArray
    let one := kp.one.ev w
    let zi := decide (one = 0) && vin.all fun v => decide (v = 0)
    let e : Env := ⟨one, fun i => vin.getD i 0, fun x => lam * gu (2 ^ 16 + x)⟩
    let R := (kp.subs.map fun p => p.2.2).sum
    add3 (add3 (subsV3 gt t u one vin lam gu (decide (lam = 0)) zi kp.ws kp.subs 0 0 0 X) (tmG3 gt e (X + R) kp.mux))
      (rmG3 gt w (X + R + kp.mux.length) kp.copy)
  else rmG3 gt w X kp.alt

theorem take_succ_sum (ws : List ℕ) (j : ℕ) : (ws.take (j + 1)).sum = (ws.take j).sum + ws.getD j 0 := by
  rw [List.take_succ, List.sum_append, List.getD_eq_getElem?_getD]
  cases ws[j]? <;> simp

theorem subsV3_eq (gt t u : ℕ → F) (one : F) (vin : Array F) (lam : F) (gu : ℕ → F) (zi : Bool) (ws : List ℕ)
    (hgt : ∀ x, gt x = gN 20 t x) (hzi : zi = true → one = 0 ∧ ∀ i, vin.getD i 0 = 0) :
    ∀ (l : List (List PS × ℕ × ℕ)) (j k X : ℕ),
      subsV3 gt t u one vin lam gu (decide (lam = 0)) zi ws l j (ws.take j).sum k X =
        (subsV .a gt t u ⟨one, fun i => vin.getD i 0, fun x => lam * gu (2 ^ 16 + x)⟩ lam (N4s.kSig ws) l j k X,
          subsV .b gt t u ⟨one, fun i => vin.getD i 0, fun x => lam * gu (2 ^ 16 + x)⟩ lam (N4s.kSig ws) l j k X,
          subsV .c gt t u ⟨one, fun i => vin.getD i 0, fun x => lam * gu (2 ^ 16 + x)⟩ lam (N4s.kSig ws) l j k X)
  | [], _, _, _ => rfl
  | (ps, nl, nr) :: l, j, k, X => by
    rw [subsV3, ← take_succ_sum, subsV3_eq gt t u one vin lam gu zi ws hgt hzi l (j + 1)]
    simp only [subsV, add3]
    have he : (⟨one, fun i => ((Array.range (ws.getD j 0)).map fun i => vin.getD ((ws.take j).sum + i) 0).getD i 0,
        fun x => if lam = 0 then 0 else mul1 lam (gu (2 ^ 16 + (k + x)))⟩ : Env) =
        pullE ⟨one, fun i => vin.getD i 0, fun x => lam * gu (2 ^ 16 + x)⟩ (N4s.kSig ws j) k := by
      simp only [pullE, Env.mk.injEq, true_and]
      refine ⟨?_, funext fun x => ?_⟩
      swap
      · rw [mul1_eq]; split_ifs with h0 <;> simp [h0]
      funext i
      rw [Array.getD_eq_getD_getElem?, Array.getElem?_map, Array.getElem?_range]
      unfold N4s.kSig
      split_ifs with h
      · simp [LinT.ev, I, Wire.ev]
      · simp [LinT.ev]
    have hl : decide (lam = 0) = true → ∀ x, (pullE ⟨one, fun i => vin.getD i 0, fun x => lam * gu (2 ^ 16 + x)⟩
        (N4s.kSig ws j) k).loc x = 0 := fun h x => by
      simp only [decide_eq_true_eq] at h; simp [pullE, h]
    have hi : zi = true → (pullE ⟨one, fun i => vin.getD i 0, fun x => lam * gu (2 ^ 16 + x)⟩
        (N4s.kSig ws j) k).one = 0 ∧ ∀ i, (pullE ⟨one, fun i => vin.getD i 0, fun x => lam * gu (2 ^ 16 + x)⟩
        (N4s.kSig ws j) k).inp i = 0 := fun h => by
      obtain ⟨h1, h2⟩ := hzi h
      refine ⟨h1, fun i => ?_⟩
      simp only [pullE]
      unfold N4s.kSig
      split_ifs <;> simp [LinT.ev, I, Wire.ev, h2]
    rw [he, psVal3_eq _ _ _ _ _ _ _ hgt hl hi]

theorem rmG3_eq (gt : ℕ → F) (w : Asg) (X : ℕ) (rows : List Row) :
    rmG3 gt w X rows = (rmG .a gt w X rows, rmG .b gt w X rows, rmG .c gt w X rows) := rfl

/-- **`kopV3` is `kopV`'s three values.** -/
theorem kopV3_eq (gt gu t u : ℕ → F) (w : Asg) (lam : F) (X : ℕ) (kp : KP) (hgt : ∀ x, gt x = gN 20 t x) :
    kopV3 gt gu t u w lam X kp = (kopV .a gt gu t u w lam X kp, kopV .b gt gu t u w lam X kp, kopV .c gt gu t u w lam X kp) := by
  unfold kopV3 kopV
  split_ifs with h
  · dsimp only
    have hzi : (decide (kp.one.ev w = 0) && (kp.ins.map (Lin.ev w)).toArray.all fun v => decide (v = 0)) = true →
        kp.one.ev w = 0 ∧ ∀ i, (kp.ins.map (Lin.ev w)).toArray.getD i 0 = 0 := fun hz => by
      simp only [Bool.and_eq_true, decide_eq_true_eq, Array.all_eq_true] at hz
      refine ⟨hz.1, fun i => ?_⟩
      rw [Array.getD_eq_getD_getElem?]
      by_cases hi : i < (kp.ins.map (Lin.ev w)).toArray.size
      · rw [Array.getElem?_eq_getElem hi]; simpa using hz.2 i hi
      · rw [Array.getElem?_eq_none (by omega)]; rfl
    have := subsV3_eq gt t u (kp.one.ev w) (kp.ins.map (Lin.ev w)).toArray lam gu _ kp.ws hgt hzi kp.subs 0 0 X
    simp only [List.take_zero, List.sum_nil] at this
    rw [this, tmG3_eq gt t _ hgt, rmG3_eq]
    simp only [add3]
  · rfl

/-- The prepared ops' values, one pass per op. -/
def kpsV3F (gt gu t u : ℕ → F) (w : Asg) (lam : F) (kps : List (ℕ × KP)) : F3 :=
  sum3 (fun q => kopV3 gt gu t u w lam q.1 q.2) kps

theorem kpsV3F_eq (gt gu t u : ℕ → F) (w : Asg) (lam : F) (kps : List (ℕ × KP)) (hgt : ∀ x, gt x = gN 20 t x) :
    kpsV3F gt gu t u w lam kps = kpsV3 gt gu t u w lam kps := by
  simp only [kpsV3F, kpsV3, sum3_eq, kopV3_eq _ _ _ _ _ _ _ _ hgt, sumL_eq]

end Rev4
end FR

end G6_FRNodeRows4RepCFW

section V2_runs

-- New for `flock-recursive` (stage V2 of `flock-x2`): the stage groups' run placeholders in closed form.

/-!
# Run placeholders in closed form

A stage group (`patA`, `patB`: 128 instances) reads each chain's stage values through a `var`
placeholder: from instance `1` on, instance `s` reads the chain's locals `b + 2·(s − 1)` (a **run**:
`runF`). `ctx3` evaluated each such placeholder's 128 forms and two 128-term instance sums. Here a
placeholder's descriptor (`phD`, computed once for the plan: `psdOf`, `kpdOf`) marks the runs, and
**`ctx3D`** sums a run in closed form: split each local `Y + a·j` at bit 8,

  `Σ_{j<m} T(j + 1 + c)·eq₂₀(u, Y + a j) = Σ_{κ<2} eq₁₂(u_hi, ⌊Y/2^8⌋ + κ)·V(c, κ, Y mod 2^8)`

(`runW_eq`), with `V` shared by every run whose base has the same low byte (one thunk per low part
and pattern: `runMk`). **`ctx3D_eq`**: `ctx3D` is `ctx`; **`kpsV3FD_eq`**: the plan's descriptors give
`kpsV3F`'s value.
-/

namespace FR
namespace Tpl
open Circ TEval Finset

/-! ## Runs: placeholders whose forms move by a constant stride -/

/-- A run's form at instance `s ≥ 1`: the locals `ts` moved up by `a·(s − 1)`. -/
def runF (a : ℕ) (ts : List (ℕ × F)) (s : ℕ) : LinT := ts.map fun τ => (Wire.loc (τ.1 + a * (s - 1)), τ.2)

/-- How a placeholder's instance sums are evaluated: generically, or as a run. -/
inductive PhD where
  | gen
  | run (a : ℕ) (ts : List (ℕ × F))

/-- The locals of a form all of whose terms read locals. -/
def locsOf : LinT → Option (List (ℕ × F))
  | [] => some []
  | (.loc k, c) :: l => (locsOf l).map ((k, c) :: ·)
  | _ :: _ => none

/-- **The run check**: `n ≥ 1` instances, the stride times `n` within `2^8`, and from instance `1` on
instance `s`'s form is `runF a ts s`. -/
def runOk (n a : ℕ) (ts : List (ℕ × F)) (fs : Array LinT) : Bool :=
  decide (1 ≤ n) && decide (a * n ≤ 2 ^ 8) &&
    (List.range n).all fun s => s == 0 || decide (fs.getD s [] = runF a ts s)

/-- The stride a run would have (instance `2`'s first local less instance `1`'s). -/
def strideOf (fs : Array LinT) (ts : List (ℕ × F)) : ℕ :=
  match fs.getD 2 [], ts with
  | (.loc k', _) :: _, (k, _) :: _ => k' - k
  | _, _ => 0

/-- **A placeholder's descriptor** (`n` instances). -/
def phD (n : ℕ) : Ph → PhD
  | .cst _ => .gen
  | .var fs =>
    match locsOf (fs.getD 1 []) with
    | some ts => if runOk n (strideOf fs ts) ts fs then .run (strideOf fs ts) ts else .gen
    | none => .gen

theorem phD_run {n a : ℕ} {ts : List (ℕ × F)} : ∀ {ph : Ph}, phD n ph = .run a ts →
    ∃ fs, ph = .var fs ∧ runOk n a ts fs = true
  | .cst f, h => by simp [phD] at h
  | .var fs, h => by
    simp only [phD] at h
    split at h
    · split_ifs at h with hok
      · cases h; exact ⟨fs, rfl, hok⟩
    · cases h

theorem runOk_spec {n a : ℕ} {ts : List (ℕ × F)} {fs : Array LinT} (h : runOk n a ts fs = true) :
    1 ≤ n ∧ a * n ≤ 2 ^ 8 ∧ ∀ s, 1 ≤ s → s < n → fs.getD s [] = runF a ts s := by
  simp only [runOk, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true, List.mem_range,
    Bool.or_eq_true, beq_iff_eq] at h
  refine ⟨h.1.1, h.1.2, fun s h1 h2 => ?_⟩
  rcases h.2 s h2 with h0 | h0
  · omega
  · exact h0

theorem ev_runF (e : Env) (a : ℕ) (ts : List (ℕ × F)) (s : ℕ) :
    (runF a ts s).ev e = (ts.map fun τ => τ.2 * e.loc (τ.1 + a * (s - 1))).sum := by
  simp only [runF, LinT.ev, List.map_map, Function.comp_def, Wire.ev]

/-! ## The run's sums in closed form -/

/-- `V(c, κ, y) = Σ_{j<m, ⌊(y + a j)/2^8⌋ = κ} T(j + 1 + c)·eq₈(u, (y + a j) mod 2^8)` (`u8` the table
`eq₈(u, ·)`). -/
def runV (T : ℕ → F) (u8 : Array F) (a m c κ y : ℕ) : F :=
  sumL (fun j => if (y + a * j) / 2 ^ 8 = κ then T (j + 1 + c) * u8.getD ((y + a * j) % 2 ^ 8) 0 else 0)
    (List.range m)

/-- The four sums at `y`. -/
def runV4 (T : ℕ → F) (u8 : Array F) (a m y : ℕ) : F × F × F × F :=
  (runV T u8 a m 0 0 y, runV T u8 a m 0 1 y, runV T u8 a m 1 0 y, runV T u8 a m 1 1 y)

/-- **The run's inner sum, split at bit 8**: `Σ_{j<m} T(j + 1 + c)·eq₂₀(u, Y + a j)` from the two
`V`s at `Y mod 2^8` and `eq₁₂(u_hi, ⌊Y/2^8⌋ + κ)`. -/
theorem runW_eq (T u : ℕ → F) (u8 : Array F) (hu8 : u8 = loTab 8 u) (hiE : ℕ → F)
    (hhi : ∀ h, hiE h = gN 12 (fun l => u (8 + l)) h) {a m : ℕ} (ham : a * m ≤ 2 ^ 8) (Y c : ℕ) :
    hiE (Y / 2 ^ 8) * runV T u8 a m c 0 (Y % 2 ^ 8) + hiE (Y / 2 ^ 8 + 1) * runV T u8 a m c 1 (Y % 2 ^ 8) =
      sumL (fun j => T (j + 1 + c) * gN 20 u (Y + a * j)) (List.range m) := by
  simp only [runV, sumL_eq, ← List.sum_map_mul_left, ← List.sum_map_add]
  refine congrArg List.sum (List.map_congr_left fun j hj => ?_)
  have hj' : a * j ≤ 2 ^ 8 := le_trans (Nat.mul_le_mul_left a (le_of_lt (List.mem_range.1 hj))) ham
  have hy : Y % 2 ^ 8 < 2 ^ 8 := Nat.mod_lt _ (by norm_num)
  have hk : (Y % 2 ^ 8 + a * j) / 2 ^ 8 < 2 := by omega
  have hs := gN_spl (p := 8) (by norm_num) u Y 0 (a * j)
  rw [Nat.zero_mul, Nat.add_zero, Nat.zero_add] at hs
  rw [hs, hu8, loTab_getD _ _ (Nat.mod_lt _ (by norm_num)), hhi, hhi]
  interval_cases hκ : (Y % 2 ^ 8 + a * j) / 2 ^ 8 <;> simp <;> ring

theorem sum_swap {α β : Type} (xs : List α) (ts : List β) (g : α → β → F) :
    (xs.map fun i => (ts.map fun τ => g i τ).sum).sum = (ts.map fun τ => (xs.map fun i => g i τ).sum).sum := by
  induction ts with
  | nil => simp
  | cons τ ts ih => simp only [List.map_cons, List.sum_cons, List.sum_map_add, ih]

/-- **A run placeholder's instance sums**: instance `0`'s form, then the run's terms. -/
theorem sZ_run (R : Rep) (A : Array F) (t : ℕ → F) (e : Env) (X j c : ℕ) {fs : Array LinT} {a : ℕ}
    {ts : List (ℕ × F)} (hj : R.ph.getD j (.cst []) = .var fs) (hok : runOk R.n a ts fs = true) :
    R.sZ A t e X j c = R.tAt A t X (0 + c) * (fs.getD 0 []).ev e +
      (ts.map fun τ => τ.2 * sumL (fun i => R.tAt A t X (i + 1 + c) * e.loc (τ.1 + a * i))
        (List.range (R.n - 1))).sum := by
  obtain ⟨h1, -, hs⟩ := runOk_spec hok
  unfold Rep.sZ
  rw [hj]
  simp only []
  obtain ⟨m, hm⟩ : ∃ m, R.n = m + 1 := ⟨R.n - 1, by omega⟩
  rw [hm, Nat.add_sub_cancel, List.range_succ_eq_map, sumL_eq, List.map_cons, List.sum_cons, List.map_map]
  congr 1
  have hr : ∀ i ∈ List.range m, (fun i => R.tAt A t X (i + c) * (fs.getD i []).ev e) (Nat.succ i) =
      (ts.map fun τ => R.tAt A t X (i + 1 + c) * (τ.2 * e.loc (τ.1 + a * i))).sum := fun i hi => by
    simp only []
    rw [hs (i + 1) (by omega) (by rw [hm]; have := List.mem_range.1 hi; omega), ev_runF, ← List.sum_map_mul_left,
      Nat.add_sub_cancel]
  rw [Function.comp_def, List.map_congr_left hr, sum_swap]
  refine congrArg List.sum (List.map_congr_left fun τ _ => ?_)
  rw [sumL_eq, ← List.sum_map_mul_left]
  exact congrArg List.sum (List.map_congr_left fun i _ => by ring)

/-! ## The evaluation -/

/-- The four sums at `y`, memoized for the stride `a₀` (one thunk per low part `y < 2^8`). -/
structure RunM where
  arr : Array (Thunk (F × F × F × F))
  T : ℕ → F
  u8 : Array F
  a₀ : ℕ
  m : ℕ

def runMk (T : ℕ → F) (u8 : Array F) (a₀ m : ℕ) : RunM :=
  ⟨(Array.range (2 ^ 8)).map fun y => Thunk.mk fun _ => runV4 T u8 a₀ m y, T, u8, a₀, m⟩

/-- The four sums at stride `a`, low part `y` (from the memo if it has them). -/
def RunM.get (M : RunM) (a y : ℕ) : F × F × F × F :=
  if a = M.a₀ then (match M.arr[y]? with | some th => th.get | none => runV4 M.T M.u8 a M.m y)
  else runV4 M.T M.u8 a M.m y

theorem thunk_mk_get {α : Type} (f : Unit → α) : (Thunk.mk f).get = f () := rfl

theorem runMk_arr (T : ℕ → F) (u8 : Array F) (a₀ m y : ℕ) :
    (runMk T u8 a₀ m).arr[y]? = if y < 2 ^ 8 then some (Thunk.mk fun _ => runV4 T u8 a₀ m y) else none := by
  unfold runMk
  dsimp only
  rw [Array.getElem?_map, Array.getElem?_range]
  split_ifs <;> rfl

-- (Kept to rewrites: unfolding `runMk` inside `RunM.get` makes the kernel evaluate the memo array.)
theorem runMk_get (T : ℕ → F) (u8 : Array F) (a₀ m a y : ℕ) : (runMk T u8 a₀ m).get a y = runV4 T u8 a m y := by
  unfold RunM.get
  rw [runMk_arr]
  by_cases h : a = a₀
  · rw [if_pos (show a = (runMk T u8 a₀ m).a₀ from h)]
    subst h
    by_cases hy : y < 2 ^ 8
    · rw [if_pos hy]; exact thunk_mk_get _
    · rw [if_neg hy]; rfl
  · rw [if_neg (show ¬ a = (runMk T u8 a₀ m).a₀ from h)]; rfl

/-- The carry-`c` pair of the four sums. -/
def runP (v : F × F × F × F) (c : ℕ) : F × F := if c = 0 then (v.1, v.2.1) else (v.2.2.1, v.2.2.2)

theorem runP_eq (T : ℕ → F) (u8 : Array F) (a m y : ℕ) {c : ℕ} (hc : c < 2) :
    runP (runV4 T u8 a m y) c = (runV T u8 a m c 0 y, runV T u8 a m c 1 y) := by
  interval_cases c <;> rfl

/-- **A run's part of the instance sums at carry `c`**: `lam · Σ_τ c_τ·(eq_hi(⌊Y/2^8⌋)·V(c,0) + eq_hi(⌊Y/2^8⌋+1)·V(c,1))`,
`Y = cl + b_τ`. -/
def runZ (hiE : ℕ → F) (memo : RunM) (lam : F) (cl a : ℕ) (ts : List (ℕ × F)) (c : ℕ) : F :=
  if lam = 0 then 0 else
    lam * sumL (fun τ => let Y := cl + τ.1; let v := runP (memo.get a (Y % 2 ^ 8)) c
      mul1 τ.2 (hiE (Y / 2 ^ 8) * v.1 + hiE (Y / 2 ^ 8 + 1) * v.2)) ts

theorem runZ_eq (T u : ℕ → F) (u8 : Array F) (hu8 : u8 = loTab 8 u) (hiE : ℕ → F)
    (hhi : ∀ h, hiE h = gN 12 (fun l => u (8 + l)) h) (a₀ m : ℕ) (e : Env) (lam : F) (cl : ℕ)
    (he : ∀ x, e.loc x = lam * gN 20 u (cl + x)) {a : ℕ} (ham : a * m ≤ 2 ^ 8) (ts : List (ℕ × F)) {c : ℕ}
    (hc : c < 2) :
    runZ hiE (runMk T u8 a₀ m) lam cl a ts c =
      (ts.map fun τ => τ.2 * sumL (fun i => T (i + 1 + c) * e.loc (τ.1 + a * i)) (List.range m)).sum := by
  have key : ∀ τ : ℕ × F, τ.2 * sumL (fun i => T (i + 1 + c) * e.loc (τ.1 + a * i)) (List.range m) =
      lam * mul1 τ.2 (hiE ((cl + τ.1) / 2 ^ 8) * (runP ((runMk T u8 a₀ m).get a ((cl + τ.1) % 2 ^ 8)) c).1 +
        hiE ((cl + τ.1) / 2 ^ 8 + 1) * (runP ((runMk T u8 a₀ m).get a ((cl + τ.1) % 2 ^ 8)) c).2) := fun τ => by
    rw [runMk_get, runP_eq _ _ _ _ _ hc, runW_eq T u u8 hu8 hiE hhi ham, mul1_eq]
    simp only [he, sumL_eq, ← List.sum_map_mul_left]
    refine congrArg List.sum (List.map_congr_left fun j _ => ?_)
    rw [show cl + τ.1 + a * j = cl + (τ.1 + a * j) from Nat.add_assoc _ _ _]; ring
  unfold runZ
  split_ifs with h0
  · rw [List.map_congr_left fun τ _ => key τ]; simp [h0]
  · rw [List.map_congr_left fun τ _ => key τ, sumL_eq, List.sum_map_mul_left]

namespace Rep
variable (R : Rep)

/-- **A placeholder's instance sums at both carries, by its descriptor** (`zPair`'s, a run in closed form). -/
def zPairD (A : Array F) (t : ℕ → F) (e : Env) (X : ℕ) (S0 S1 : F) (zl zi : Bool) (hiE : ℕ → F)
    (memo : RunM) (lam : F) (cl : ℕ) (ph : Ph) (d : PhD) : F × F :=
  match d with
  | .run a ts =>
    match ph with
    | .var fs =>
      let f0 := fs.getD 0 []
      let z0 := if skipF zl zi f0 then 0 else evF e f0
      (mulZ (R.tAt A t X 0) z0 + runZ hiE memo lam cl a ts 0, mulZ (R.tAt A t X 1) z0 + runZ hiE memo lam cl a ts 1)
    | ph => R.zPair A t e X S0 S1 zl zi ph
  | .gen => R.zPair A t e X S0 S1 zl zi ph

theorem zPairD_eq {zl zi : Bool} (t u : ℕ → F) (e : Env) (X : ℕ) (lam : F) (cl : ℕ)
    (hl : zl = true → ∀ x, e.loc x = 0) (hi : zi = true → e.one = 0 ∧ ∀ i, e.inp i = 0)
    (he : ∀ x, e.loc x = lam * gN 20 u (cl + x)) (u8 : Array F) (hu8 : u8 = loTab 8 u) (hiE : ℕ → F)
    (hhi : ∀ h, hiE h = gN 12 (fun l => u (8 + l)) h) (a₀ j : ℕ) :
    R.zPairD (R.tArr t X) t e X (R.sS (R.tArr t X) t X 0) (R.sS (R.tArr t X) t X 1) zl zi hiE
        (runMk (R.tAt (R.tArr t X) t X) u8 a₀ (R.n - 1)) lam cl (R.ph.getD j (.cst []))
        (phD R.n (R.ph.getD j (.cst []))) =
      (R.sZ (R.tArr t X) t e X j 0, R.sZ (R.tArr t X) t e X j 1) := by
  cases hd : phD R.n (R.ph.getD j (.cst [])) with
  | gen => exact R.zPair_eq t e X hl hi j
  | run a ts =>
    obtain ⟨fs, hph, hok⟩ := phD_run hd
    obtain ⟨-, ha, -⟩ := runOk_spec hok
    have ham : a * (R.n - 1) ≤ 2 ^ 8 := le_trans (Nat.mul_le_mul_left a (Nat.sub_le _ _)) ha
    have hz : (if skipF zl zi (fs.getD 0 []) then 0 else evF e (fs.getD 0 [])) = (fs.getD 0 []).ev e := by
      split_ifs with h
      · exact (ev_skip hl hi h).symm
      · exact evF_eq e _
    simp only [zPairD, hph, hz, mulZ_eq]
    rw [sZ_run R _ t e X j 0 hph hok, sZ_run R _ t e X j 1 hph hok,
      runZ_eq _ u u8 hu8 hiE hhi a₀ _ e lam cl he ham ts (by norm_num),
      runZ_eq _ u u8 hu8 hiE hhi a₀ _ e lam cl he ham ts (by norm_num)]

/-- **`tArr` by split tables** (V5): `eq(t_[p,20), y) = lo[y mod 2^6] · hi[⌊y/2^6⌋]`, one product per
entry and two tables of `2^6` and `2^(14 − p)` entries, not `20 − p` products per entry (`tArrS_eq`). -/
def tArrS (t : ℕ → F) (X : ℕ) : Array F :=
  if R.p + 6 ≤ 20 then
    let lo := loTab 6 fun l => t (R.p + l)
    let hi := loTab (20 - R.p - 6) fun l => t (R.p + (6 + l))
    (Array.range (R.n + 2)).map fun h => splitAt lo hi (2 ^ 6) (X / 2 ^ R.p + h)
  else R.tArr t X

theorem tArrS_eq (t : ℕ → F) (X : ℕ) : R.tArrS t X = R.tArr t X := by
  unfold tArrS tArr
  split_ifs with h
  · have e := splitE_eq (m := 20 - R.p) (s := 6) (by omega) (fun l => t (R.p + l))
    rw [gNL_eq, ← e]
    rfl
  · rfl

/-- **The per-call sums by the descriptors `D`** (`ctx3`'s; the run placeholders in closed form,
their sums memoized for the stride `a₀`; V5: `tArrS`). -/
def ctx3D (t u : ℕ → F) (e : Env) (lam : F) (cl X K : ℕ) (zl zi : Bool) (u8 : Array F) (hiE : ℕ → F)
    (D : Array PhD) (a₀ : ℕ) : Cx :=
  let tA := R.tArrS t X
  let uA := R.tArrS u (cl + K)
  let S0 := R.sS tA t X 0
  let S1 := R.sS tA t X 1
  let memo := runMk (R.tAt tA t X) u8 a₀ (R.n - 1)
  ⟨tA, uA, S0, S1,
    #[R.sD tA uA t u X (cl + K) 0 0, R.sD tA uA t u X (cl + K) 0 1, R.sD tA uA t u X (cl + K) 1 0,
      R.sD tA uA t u X (cl + K) 1 1],
    Array.zipWith (R.zPairD tA t e X S0 S1 zl zi hiE memo lam cl) R.ph D, loTab R.p t, loTab R.p u⟩

/-- **`ctx3D` is `ctx`** (the descriptors `R.ph`'s). -/
theorem ctx3D_eq {zl zi : Bool} (t u : ℕ → F) (e : Env) (lam : F) (cl X K : ℕ)
    (hl : zl = true → ∀ x, e.loc x = 0) (hi : zi = true → e.one = 0 ∧ ∀ i, e.inp i = 0)
    (he : ∀ x, e.loc x = lam * gN 20 u (cl + x)) (u8 : Array F) (hu8 : u8 = loTab 8 u) (hiE : ℕ → F)
    (hhi : ∀ h, hiE h = gN 12 (fun l => u (8 + l)) h) (a₀ : ℕ) :
    R.ctx3D t u e lam cl X K zl zi u8 hiE (R.ph.map (phD R.n)) a₀ = R.ctx t u e cl X K := by
  simp only [ctx3D, ctx, tArrS_eq, Cx.mk.injEq, true_and, and_true]
  apply Array.ext
  · simp
  · intro j h1 h2
    simp only [Array.getElem_zipWith, Array.getElem_map, Array.getElem_range]
    have := R.zPairD_eq t u e X lam cl hl hi he u8 hu8 hiE hhi a₀ j
    have hj : j < R.ph.size := by simpa using h1
    rw [Array.getD_eq_getD_getElem?, Array.getElem?_eq_getElem hj, Option.getD_some] at this
    exact this

end Rep

/-- A prepared segment with its placeholders' descriptors (and the memo's stride). -/
inductive PSD where
  | rows (X : ℕ) (rs : List RowT)
  | rep (X K : ℕ) (R : Rep) (pr : List RowT) (D : Array PhD) (a₀ : ℕ)

/-- The first run's stride. -/
def a0Of (D : Array PhD) : ℕ :=
  D.foldr (fun d a => match d with | .run b _ => b | .gen => a) 0

/-- **A prepared segment's descriptors.** -/
def psdOf : PS → PSD
  | .rows X rs => .rows X rs
  | .rep X K R pr => .rep X K R pr (R.ph.map (phD R.n)) (a0Of (R.ph.map (phD R.n)))

/-- **The prepared segments' value by the descriptors** (`psVal3`'s). -/
def psVal3D (gt t u : ℕ → F) (e : Env) (lam : F) (cl X0 : ℕ) (zl zi : Bool) (u8 : Array F) (hiE : ℕ → F) :
    List PSD → F3
  | [] => (0, 0, 0)
  | .rows X rs :: l => add3 (tmG3 gt e (X0 + X) rs) (psVal3D gt t u e lam cl X0 zl zi u8 hiE l)
  | .rep X K R pr D a₀ :: l =>
    add3 (R.pass3 (R.ctx3D t u e lam cl (X0 + X) K zl zi u8 hiE D a₀) t u e lam cl (X0 + X) K 0 pr)
      (psVal3D gt t u e lam cl X0 zl zi u8 hiE l)

theorem psVal3D_eq (gt t u : ℕ → F) (e : Env) (lam : F) (cl X0 : ℕ) {zl zi : Bool}
    (hl : zl = true → ∀ x, e.loc x = 0) (hi : zi = true → e.one = 0 ∧ ∀ i, e.inp i = 0)
    (he : ∀ x, e.loc x = lam * gN 20 u (cl + x)) (u8 : Array F) (hu8 : u8 = loTab 8 u) (hiE : ℕ → F)
    (hhi : ∀ h, hiE h = gN 12 (fun l => u (8 + l)) h) :
    ∀ l : List PS, psVal3D gt t u e lam cl X0 zl zi u8 hiE (l.map psdOf) = psVal3 gt t u e lam cl X0 zl zi l
  | [] => rfl
  | .rows X rs :: l => by
    rw [List.map_cons, psdOf, psVal3D, psVal3, psVal3D_eq gt t u e lam cl X0 hl hi he u8 hu8 hiE hhi l]
  | .rep X K R pr :: l => by
    rw [List.map_cons, psdOf, psVal3D, psVal3, psVal3D_eq gt t u e lam cl X0 hl hi he u8 hu8 hiE hhi l,
      R.ctx3D_eq t u e lam cl _ K hl hi he u8 hu8 hiE hhi, R.ctx3_eq t u e cl _ K hl hi]

end Tpl
end FR

namespace FR
namespace Rev4
open RecursionFast Circ TEval Tpl

/-- The sub-templates' value by the descriptors (`subsV3`'s). -/
def subsV3D (gt t u : ℕ → F) (one : F) (vin : Array F) (lam : F) (gu : ℕ → F) (zl zi : Bool) (ws : List ℕ)
    (u8 : Array F) (hiE : ℕ → F) : List (List PSD × ℕ × ℕ) → ℕ → ℕ → ℕ → ℕ → F3
  | [], _, _, _, _ => (0, 0, 0)
  | (ps, nl, nr) :: l, j, off, k, X =>
    let wj := ws.getD j 0
    let vj := (Array.range wj).map fun i => vin.getD (off + i) 0
    let e : Env := ⟨one, fun i => vj.getD i 0, fun x => if lam = 0 then 0 else mul1 lam (gu (2 ^ 16 + (k + x)))⟩
    add3 (psVal3D gt t u e lam (2 ^ 16 + k) X zl zi u8 hiE ps)
      (subsV3D gt t u one vin lam gu zl zi ws u8 hiE l (j + 1) (off + wj) (k + nl) (X + nr))

theorem subsV3D_eq (gt t u : ℕ → F) (one : F) (vin : Array F) (lam : F) (gu : ℕ → F) (zi : Bool) (ws : List ℕ)
    (hgu : ∀ x, gu x = gN 20 u x) (hzi : zi = true → one = 0 ∧ ∀ i, vin.getD i 0 = 0)
    (u8 : Array F) (hu8 : u8 = loTab 8 u) (hiE : ℕ → F) (hhi : ∀ h, hiE h = gN 12 (fun l => u (8 + l)) h) :
    ∀ (l : List (List PS × ℕ × ℕ)) (j off k X : ℕ),
      subsV3D gt t u one vin lam gu (decide (lam = 0)) zi ws u8 hiE (l.map fun x => (x.1.map psdOf, x.2)) j off k X =
        subsV3 gt t u one vin lam gu (decide (lam = 0)) zi ws l j off k X
  | [], _, _, _, _ => rfl
  | (ps, nl, nr) :: l, j, off, k, X => by
    rw [List.map_cons, subsV3D, subsV3, subsV3D_eq gt t u one vin lam gu zi ws hgu hzi u8 hu8 hiE hhi l]
    congr 1
    refine psVal3D_eq gt t u _ lam _ X (fun h x => ?_) (fun h => ⟨(hzi h).1, fun i => ?_⟩) (fun x => ?_) u8 hu8 hiE hhi ps
    · simp only [decide_eq_true_eq] at h; simp [h]
    · simp only [Array.getD_eq_getD_getElem?, Array.getElem?_map, Array.getElem?_range]
      split_ifs
      · have := (hzi h).2 (off + i); rw [Array.getD_eq_getD_getElem?] at this; simpa using this
      · rfl
    · simp only [mul1_eq, hgu]
      split_ifs with h0
      · rw [h0, zero_mul]
      · rw [Nat.add_assoc]

/-- A prepared `rsWeight` op with its segments' descriptors. -/
structure KPD where
  kp : KP
  sd : List (List PSD × ℕ × ℕ)

/-- **The descriptors of a prepared op.** -/
def kpdOf (kp : KP) : KPD := ⟨kp, kp.subs.map fun x => (x.1.map psdOf, x.2)⟩

/-- **The prepared `rsWeight` op's value by the descriptors** (`kopV3`'s). -/
def kopV3D (gt gu t u : ℕ → F) (w : Asg) (lam : F) (u8 : Array F) (hiE : ℕ → F) (X : ℕ) (d : KPD) : F3 :=
  if d.kp.ok then
    let vin := (d.kp.ins.map (Lin.ev w)).toArray
    let one := d.kp.one.ev w
    let zi := decide (one = 0) && vin.all fun v => decide (v = 0)
    let e : Env := ⟨one, fun i => vin.getD i 0, fun x => lam * gu (2 ^ 16 + x)⟩
    let R := (d.kp.subs.map fun p => p.2.2).sum
    add3 (add3 (subsV3D gt t u one vin lam gu (decide (lam = 0)) zi d.kp.ws u8 hiE d.sd 0 0 0 X)
        (tmG3 gt e (X + R) d.kp.mux))
      (rmG3 gt w (X + R + d.kp.mux.length) d.kp.copy)
  else rmG3 gt w X d.kp.alt

theorem kopV3D_eq (gt gu t u : ℕ → F) (w : Asg) (lam : F) (u8 : Array F) (hiE : ℕ → F) (X : ℕ) (kp : KP)
    (hgu : ∀ x, gu x = gN 20 u x) (hu8 : u8 = loTab 8 u) (hhi : ∀ h, hiE h = gN 12 (fun l => u (8 + l)) h) :
    kopV3D gt gu t u w lam u8 hiE X (kpdOf kp) = kopV3 gt gu t u w lam X kp := by
  unfold kopV3D kopV3 kpdOf
  dsimp only
  split_ifs with h
  · have hzi : (decide (kp.one.ev w = 0) && (kp.ins.map (Lin.ev w)).toArray.all fun v => decide (v = 0)) = true →
        kp.one.ev w = 0 ∧ ∀ i, (kp.ins.map (Lin.ev w)).toArray.getD i 0 = 0 := fun hz => by
      simp only [Bool.and_eq_true, decide_eq_true_eq, Array.all_eq_true] at hz
      refine ⟨hz.1, fun i => ?_⟩
      rw [Array.getD_eq_getD_getElem?]
      by_cases hi : i < (kp.ins.map (Lin.ev w)).toArray.size
      · rw [Array.getElem?_eq_getElem hi]; simpa using hz.2 i hi
      · rw [Array.getElem?_eq_none (by omega)]; rfl
    rw [subsV3D_eq gt t u _ _ lam gu _ kp.ws hgu hzi u8 hu8 hiE hhi]
  · rfl

/-- The prepared ops' values by the descriptors (`kpsV3F`'s). -/
def kpsV3FD (gt gu t u : ℕ → F) (w : Asg) (lam : F) (u8 : Array F) (hiE : ℕ → F) (kps : List (ℕ × KPD)) : F3 :=
  sum3 (fun q => kopV3D gt gu t u w lam u8 hiE q.1 q.2) kps

theorem kpsV3FD_eq (gt gu t u : ℕ → F) (w : Asg) (lam : F) (u8 : Array F) (hiE : ℕ → F) (kps : List (ℕ × KP))
    (hgu : ∀ x, gu x = gN 20 u x) (hu8 : u8 = loTab 8 u) (hhi : ∀ h, hiE h = gN 12 (fun l => u (8 + l)) h) :
    kpsV3FD gt gu t u w lam u8 hiE (kps.map fun q => (q.1, kpdOf q.2)) = kpsV3F gt gu t u w lam kps := by
  simp only [kpsV3FD, kpsV3F, sum3_eq, sumL_eq, List.map_map, Function.comp_def,
    kopV3D_eq _ _ _ _ _ _ _ _ _ _ hgu hu8 hhi]

end Rev4
end FR

end V2_runs

section V4_rows

-- New for `flock-recursive` (stage V4 of `flock-x2`): the `rsWeight` op's irregular rows on the flat evaluator.

/-!
# The `rsWeight` op's irregular rows, packed

A prepared op's sub-templates hold irregular rows (`PS.rows`: 9–13 k rows per kind) next to their
repeated patterns, and `kpsV3FD` evaluates them row by row (`tmG3`). Here they are instantiated once
for the plan (`kpsRows`: block `j`'s inputs, the sub-template's locals at `cbRS + k`) and packed with
the replay's row blocks (`Plan4.fF`, `fL`). **`kpsV3FD_split`**: `kpsV3FD` is the rest (`kpsV3FDR`:
the patterns, the mux and the copy rows) plus the instantiated rows' value at the cell weights.
-/

namespace FR
namespace Tpl
open Circ TEval

/-- `psVal3D` without the irregular rows. -/
def psVal3DR (gt t u : ℕ → F) (e : Env) (lam : F) (cl X0 : ℕ) (zl zi : Bool) (u8 : Array F) (hiE : ℕ → F) :
    List PSD → F3
  | [] => (0, 0, 0)
  | .rows _ _ :: l => psVal3DR gt t u e lam cl X0 zl zi u8 hiE l
  | .rep X K R pr D a₀ :: l =>
    add3 (R.pass3 (R.ctx3D t u e lam cl (X0 + X) K zl zi u8 hiE D a₀) t u e lam cl (X0 + X) K 0 pr)
      (psVal3DR gt t u e lam cl X0 zl zi u8 hiE l)

/-- **The irregular rows of prepared segments**, indexed (rows from `X0`). -/
def psRows (X0 : ℕ) : List PS → List (ℕ × RowT)
  | [] => []
  | .rows X rs :: l => (rs.zipIdx (X0 + X)).map (fun p => (p.2, p.1)) ++ psRows X0 l
  | .rep .. :: l => psRows X0 l

/-- Indexed template rows' value (matrix `s`, row point `t`, wires `e`). -/
def tmI (s : Mat) (t : ℕ → F) (e : Env) (l : List (ℕ × RowT)) : F := (l.map fun p => gN 20 t p.1 * (s.t p.2).ev e).sum

theorem tmI_append (s : Mat) (t : ℕ → F) (e : Env) (a b : List (ℕ × RowT)) :
    tmI s t e (a ++ b) = tmI s t e a + tmI s t e b := by simp [tmI]

theorem tm_zipIdx (s : Mat) (t : ℕ → F) (e : Env) : ∀ (X : ℕ) (rs : List RowT),
    tm s t e X rs = tmI s t e ((rs.zipIdx X).map fun p => (p.2, p.1))
  | _, [] => by simp [tm, tmI]
  | X, r :: rs => by rw [tm, tm_zipIdx s t e (X + 1) rs, List.zipIdx_cons]; simp [tmI]

theorem add3_comm3 (a b c : F3) : add3 a (add3 b c) = add3 b (add3 a c) := by
  simp only [add3]; refine Prod.ext ?_ (Prod.ext ?_ ?_) <;> simp only <;> abel

theorem add3_zero (a : F3) : add3 a (0, 0, 0) = a := by simp [add3]

/-- **The prepared segments' value is the rest plus the irregular rows'.** -/
theorem psVal3D_split (gt t u : ℕ → F) (e : Env) (lam : F) (cl X0 : ℕ) (zl zi : Bool) (u8 : Array F) (hiE : ℕ → F)
    (hgt : ∀ x, gt x = gN 20 t x) : ∀ l : List PS,
    psVal3D gt t u e lam cl X0 zl zi u8 hiE (l.map psdOf) =
      add3 (psVal3DR gt t u e lam cl X0 zl zi u8 hiE (l.map psdOf))
        (tmI .a t e (psRows X0 l), tmI .b t e (psRows X0 l), tmI .c t e (psRows X0 l))
  | [] => by simp [psVal3D, psVal3DR, psRows, tmI, add3]
  | .rows X rs :: l => by
    rw [List.map_cons, psdOf, psVal3D, psVal3DR, psVal3D_split gt t u e lam cl X0 zl zi u8 hiE hgt l,
      tmG3_tm gt t e hgt, psRows, tmI_append, tmI_append, tmI_append, tm_zipIdx, tm_zipIdx, tm_zipIdx]
    simp only [add3]; refine Prod.ext ?_ (Prod.ext ?_ ?_) <;> simp only <;> abel
  | .rep X K R pr :: l => by
    rw [List.map_cons, psdOf, psVal3D, psVal3DR, psVal3D_split gt t u e lam cl X0 zl zi u8 hiE hgt l, psRows]
    simp only [add3]; refine Prod.ext ?_ (Prod.ext ?_ ?_) <;> simp only <;> abel

end Tpl
end FR

namespace FR
namespace Rev4
open RecursionFast Circ TEval Tpl

/-- `subsV3D` without the irregular rows. -/
def subsV3DR (gt t u : ℕ → F) (one : F) (vin : Array F) (lam : F) (gu : ℕ → F) (zl zi : Bool) (ws : List ℕ)
    (u8 : Array F) (hiE : ℕ → F) : List (List PSD × ℕ × ℕ) → ℕ → ℕ → ℕ → ℕ → F3
  | [], _, _, _, _ => (0, 0, 0)
  | (ps, nl, nr) :: l, j, off, k, X =>
    let wj := ws.getD j 0
    let vj := (Array.range wj).map fun i => vin.getD (off + i) 0
    let e : Env := ⟨one, fun i => vj.getD i 0, fun x => if lam = 0 then 0 else mul1 lam (gu (2 ^ 16 + (k + x)))⟩
    add3 (psVal3DR gt t u e lam (2 ^ 16 + k) X zl zi u8 hiE ps)
      (subsV3DR gt t u one vin lam gu zl zi ws u8 hiE l (j + 1) (off + wj) (k + nl) (X + nr))

/-- **The sub-templates' irregular rows, instantiated**: block `j`'s inputs `ins[off …]`, the locals at
`cbRS + k`. -/
def subsRows (one : Lin) (ins : List Lin) (ws : List ℕ) : List (List PS × ℕ × ℕ) → ℕ → ℕ → ℕ → ℕ → List (ℕ × Row)
  | [], _, _, _, _ => []
  | (ps, nl, nr) :: l, j, off, k, X =>
    let wj := ws.getD j 0
    let insj := (List.range wj).map fun i => ins.getD (off + i) []
    (psRows X ps).map (fun p => (p.1, instRow one insj (N4s.cbRS + k) p.2)) ++
      subsRows one ins ws l (j + 1) (off + wj) (k + nl) (X + nr)

/-- An op's irregular rows (none if its checks failed). -/
def kpRows (kp : KP) (X : ℕ) : List (ℕ × Row) := if kp.ok then subsRows kp.one kp.ins kp.ws kp.subs 0 0 0 X else []

/-- **The ops' irregular rows.** -/
def kpsRows (kps : List (ℕ × KP)) : List (ℕ × Row) := kps.flatMap fun q => kpRows q.2 q.1

/-- Indexed rows' value (matrix `s`, row point `t`, cells at `w`). -/
def rmI (s : Mat) (t : ℕ → F) (w : Asg) (l : List (ℕ × Row)) : F := (l.map fun p => gN 20 t p.1 * (s.r p.2).ev w).sum

def rmI3 (t : ℕ → F) (w : Asg) (l : List (ℕ × Row)) : F3 := (rmI .a t w l, rmI .b t w l, rmI .c t w l)

theorem rmI_append (s : Mat) (t : ℕ → F) (w : Asg) (a b : List (ℕ × Row)) :
    rmI s t w (a ++ b) = rmI s t w a + rmI s t w b := by simp [rmI]

theorem tmI_inst (s : Mat) (t : ℕ → F) (w : Asg) (one : Lin) (ins : List Lin) (cb : ℕ) (l : List (ℕ × RowT)) :
    tmI s t (envOf w one ins cb) l = rmI s t w (l.map fun p => (p.1, instRow one ins cb p.2)) := by
  simp only [tmI, rmI, List.map_map, Function.comp_def, Mat.r_inst, instLin_ev]

theorem vin_get (w : Asg) (ins : List Lin) (n : ℕ) : (ins.map (Lin.ev w)).toArray.getD n 0 = (ins.getD n []).ev w := by
  rw [Array.getD_eq_getD_getElem?, List.getElem?_toArray, List.getElem?_map, List.getD_eq_getElem?_getD]
  cases ins[n]? <;> simp [Lin.ev]

/-- **The sub-templates' value is the rest plus their irregular rows'** (cells at `w`, the locals at
`lam · gu(2^16 + ·)`). -/
theorem subsV3D_split (gt t u : ℕ → F) (w : Asg) (one : Lin) (ins : List Lin) (lam : F) (gu : ℕ → F) (zl zi : Bool)
    (ws : List ℕ) (u8 : Array F) (hiE : ℕ → F) (hgt : ∀ x, gt x = gN 20 t x)
    (hw : ∀ y, w (N4s.cbRS + y) = lam * gu (2 ^ 16 + y)) :
    ∀ (l : List (List PS × ℕ × ℕ)) (j off k X : ℕ),
      subsV3D gt t u (one.ev w) (ins.map (Lin.ev w)).toArray lam gu zl zi ws u8 hiE
          (l.map fun x => (x.1.map psdOf, x.2)) j off k X =
        add3 (subsV3DR gt t u (one.ev w) (ins.map (Lin.ev w)).toArray lam gu zl zi ws u8 hiE
          (l.map fun x => (x.1.map psdOf, x.2)) j off k X) (rmI3 t w (subsRows one ins ws l j off k X))
  | [], _, _, _, _ => by simp [subsV3D, subsV3DR, subsRows, rmI3, rmI, add3]
  | (ps, nl, nr) :: l, j, off, k, X => by
    rw [List.map_cons, subsV3D, subsV3DR, subsRows,
      subsV3D_split gt t u w one ins lam gu zl zi ws u8 hiE hgt hw l]
    dsimp only
    have he : (⟨one.ev w, fun i => ((Array.range (ws.getD j 0)).map fun i =>
          (ins.map (Lin.ev w)).toArray.getD (off + i) 0).getD i 0,
        fun x => if lam = 0 then 0 else mul1 lam (gu (2 ^ 16 + (k + x)))⟩ : Env) =
        envOf w one ((List.range (ws.getD j 0)).map fun i => ins.getD (off + i) []) (N4s.cbRS + k) := by
      simp only [envOf, Env.mk.injEq, true_and]
      refine ⟨funext fun i => ?_, funext fun x => ?_⟩
      · generalize ws.getD j 0 = wj
        by_cases hi : i < wj
        · have h1 : ((Array.range wj).map fun i => (ins.map (Lin.ev w)).toArray.getD (off + i) 0).getD i 0 =
              (ins.map (Lin.ev w)).toArray.getD (off + i) 0 := by
            rw [Array.getD_eq_getD_getElem?, Array.getElem?_map, Array.getElem?_range, if_pos hi]; rfl
          have h2 : ((List.range wj).map fun i => ins.getD (off + i) []).getD i [] = ins.getD (off + i) [] := by
            rw [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range hi]; rfl
          rw [h1, h2, vin_get]
        · have h1 : ((Array.range wj).map fun i => (ins.map (Lin.ev w)).toArray.getD (off + i) 0).getD i 0 = 0 := by
            rw [Array.getD_eq_getD_getElem?, Array.getElem?_map, Array.getElem?_range, if_neg hi]; rfl
          have h2 : ((List.range wj).map fun i => ins.getD (off + i) []).getD i [] = [] := by
            rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by simp; omega)]; rfl
          rw [h1, h2]; simp [Lin.ev]
      · rw [Nat.add_assoc, hw, mul1_eq]
        split_ifs with h0
        · rw [h0, zero_mul]
        · rfl
    rw [he, psVal3D_split gt t u _ lam _ X zl zi u8 hiE hgt ps, tmI_inst, tmI_inst, tmI_inst]
    simp only [rmI3, rmI_append, add3]
    refine Prod.ext ?_ (Prod.ext ?_ ?_) <;> simp only <;> abel

/-- `kopV3D` without the irregular rows. -/
def kopV3DR (gt gu t u : ℕ → F) (w : Asg) (lam : F) (u8 : Array F) (hiE : ℕ → F) (X : ℕ) (d : KPD) : F3 :=
  if d.kp.ok then
    let vin := (d.kp.ins.map (Lin.ev w)).toArray
    let one := d.kp.one.ev w
    let zi := decide (one = 0) && vin.all fun v => decide (v = 0)
    let e : Env := ⟨one, fun i => vin.getD i 0, fun x => lam * gu (2 ^ 16 + x)⟩
    let R := (d.kp.subs.map fun p => p.2.2).sum
    add3 (add3 (subsV3DR gt t u one vin lam gu (decide (lam = 0)) zi d.kp.ws u8 hiE d.sd 0 0 0 X)
        (tmG3 gt e (X + R) d.kp.mux))
      (rmG3 gt w (X + R + d.kp.mux.length) d.kp.copy)
  else rmG3 gt w X d.kp.alt

theorem kopV3D_split (gt gu t u : ℕ → F) (w : Asg) (lam : F) (u8 : Array F) (hiE : ℕ → F) (X : ℕ) (kp : KP)
    (hgt : ∀ x, gt x = gN 20 t x) (hw : ∀ y, w (N4s.cbRS + y) = lam * gu (2 ^ 16 + y)) :
    kopV3D gt gu t u w lam u8 hiE X (kpdOf kp) = add3 (kopV3DR gt gu t u w lam u8 hiE X (kpdOf kp)) (rmI3 t w (kpRows kp X)) := by
  unfold kopV3D kopV3DR kpdOf kpRows
  dsimp only
  split_ifs with h
  · rw [subsV3D_split gt t u w kp.one kp.ins lam gu _ _ kp.ws u8 hiE hgt hw]
    simp only [add3]; refine Prod.ext ?_ (Prod.ext ?_ ?_) <;> simp only <;> abel
  · simp [rmI3, rmI, add3]

/-- `kpsV3FD` without the irregular rows. -/
def kpsV3FDR (gt gu t u : ℕ → F) (w : Asg) (lam : F) (u8 : Array F) (hiE : ℕ → F) (kps : List (ℕ × KPD)) : F3 :=
  sum3 (fun q => kopV3DR gt gu t u w lam u8 hiE q.1 q.2) kps

/-- **The ops' value is the rest plus their irregular rows'.** -/
theorem kpsV3FD_split (gt gu t u : ℕ → F) (w : Asg) (lam : F) (u8 : Array F) (hiE : ℕ → F) (kps : List (ℕ × KP))
    (hgt : ∀ x, gt x = gN 20 t x) (hw : ∀ y, w (N4s.cbRS + y) = lam * gu (2 ^ 16 + y)) :
    kpsV3FD gt gu t u w lam u8 hiE (kps.map fun q => (q.1, kpdOf q.2)) =
      add3 (kpsV3FDR gt gu t u w lam u8 hiE (kps.map fun q => (q.1, kpdOf q.2))) (rmI3 t w (kpsRows kps)) := by
  simp only [kpsV3FD, kpsV3FDR, sum3_eq, sumL_eq, List.map_map, Function.comp_def,
    kopV3D_split gt gu t u w lam u8 hiE _ _ hgt hw, add3, List.sum_map_add, rmI3, rmI, kpsRows,
    Flat.sum_map_flatMap]

theorem wFA_cb (gu : ℕ → F) (y : ℕ) : wFA gu (N4s.cbRS + y) = 0 * gu (2 ^ 16 + y) := by
  have h : ¬ N4s.cbRS + y < N4s.repB := by unfold N4s.cbRS; exact Nat.not_lt.2 (by omega)
  rw [wFA, if_neg h, zero_mul]

theorem wLA_cb (gu : ℕ → F) (y : ℕ) : wLA gu (N4s.cbRS + y) = 1 * gu (2 ^ 16 + y) := by
  have h : ¬ N4s.cbRS + y < N4s.repB := by unfold N4s.cbRS; exact Nat.not_lt.2 (by omega)
  have e : N4s.cbRS + y - N4s.repB = 2 ^ 16 + y := by unfold N4s.cbRS; omega
  rw [wLA, if_neg h, e, one_mul]

end Rev4
end FR

end V4_rows

section G6_FRNodeRows4Plan

-- New for `flock-recursive` (BLUEPRINT revision 4.1, B-16, §4.4; stage S-E12b, track L-circ).

/-!
# The 4.1 nodes' plan and `evalM`: one evaluation per prototype

**The plan** (`planOf4`, a closed constant built at process start, B-16) is the two prototypes'
proved pieces (S-E13's construction for one slot: `protoData`, `protoData_rows`), shared by `N2`,
`N4` and `N8`.

**`evalM`** (`evalMT4`). Every entry of slot `σ`'s rows has its row and its cell in region `σ`, so
for the prototype's rows moved to region `σ` and made absolute (`copy_val`):

  `MLE(slot σ)(τ, u) = eq(τ_[20,lm), σ) · eq(u_[20,lm), σ) · u_lm · u_lm+1 · MLE_lo(prototype)`

where `MLE_lo` is the prototype's value at the point restricted to region `π`'s low coordinates
(`starPt`): one evaluation per prototype, by the existing templated evaluator (21 row and 23 cell
coordinates), whatever the kind. The link region (S-E12c's ≤ 8 link rows, S-E13a's pack rows,
S-E13b's node rows, with H cells) is summed by split eq tables (`linkV4`) from data the plan prepares
once (B5): its rows grouped (`LkG`), the node rows coded against a cell dictionary (`crowsVal3`),
the pinned elements in runs and value classes whose inner sums the kinds share (`prIn`, `prVal`). The
region facts are checked once per process on the pieces (`pieceInB`, `pcIn_spec`), with the sparse
sum as the fallback. **`evalMT4_eq`**: `evalMT4` is the MLE of `nodeIRows4 κ`'s three matrices.

**The replay rows** (REPF, `FRNodeRows4.repAllRows`): the plan computes them in the template rows'
memoized pass (`arRepOf`, the fold lemma `arRepOf_eq`), checks their fit (`RepFit`, in `inR`) and keeps
slot 0's frame and local parts packed in local coordinates (`fF`, `fL`); per call `rvOf` evaluates
them once (shared by `N2` and `N4`) and `repV4` scales them by the regions' high factors (`repV0_eq`);
a segment slot's 8 rows are summed sparsely (`repIRowsWP`).
-/

namespace FR
namespace Rev4
open RecursionFast Circ TEval Tpl

/-! ## The two prototypes' pieces (S-E13's `planData`, two programs) -/

/-- Prototype `π`'s `one` form. -/
abbrev oneP (π : ℕ) : Lin := Lin.cell (oneR π)

theorem infoOf_map (ks : List TKey) (k : TKey) :
    infoOf (ks.map mkKM) k = ((tRows k).length, cregion k, tNlocs k) := by
  rw [infoOf, kmOf_map, mkKM_info]

/-- **The plan's data**: both prototypes compiled once at their layouts (`protoLay`, constants)
with one template memo, their proto-pieces, **one grouping** (so that the keys, and their
preparation in `evalM`, are shared), each prototype's checked pieces. -/
noncomputable def planData4 : Array GK × Array (List Lin) × Array (List Lin) × List Piece × List Piece :=
  let ops0 := (protoProg 0).ops
  let ops1 := (protoProg 1).ops
  let l0 := protoLay 0
  let l1 := protoLay 1
  let ks0 := l0.map Prod.fst
  let kms := (ks0 ++ (l1.map Prod.fst).filter (fun k => !ks0.contains k)).map mkKM
  let r0 := compMSX (N4s.XofC 0) l0 (protoP 0) [] (CS.init (baseR 0)) ops0 none []
  let r1 := compMSX (N4s.XofC 1) l1 (protoP 1) r0.2.2 (CS.init (baseR 1)) ops1 none []
  let p0 := slotRP (oneP 0) kms l0 0 r0.1 r0.2.1.reverse []
  let rps1 := (slotRP (oneP 1) kms l1 (1 * slotM4) r1.1 r1.2.1.reverse p0.2).1
  let g := groupRP p0.1 rps1
  (g.1, g.2.1, g.2.2.1, piecesOf g.1 g.2.1 (oneP 0) p0.1 g.2.2.2.1, piecesOf g.1 g.2.2.1 (oneP 1) rps1 g.2.2.2.2)

/-- **The pieces are the prototypes' rows.** -/
theorem planData4_rows :
    planData4.2.2.2.1.flatMap (Piece.rows (planData4.1.map mkKey) planData4.2.1 (oneP 0)) = protoRows 0 ∧
      planData4.2.2.2.2.flatMap (Piece.rows (planData4.1.map mkKey) planData4.2.2.1 (oneP 1)) = protoRows 1 := by
  simp only [planData4, piecesOf_rows]
  obtain ⟨hr0, mr0⟩ := compMSX_T (N4s.XofC 0) (protoLay 0) (protoP 0) (baseR 0)
    (protoProg 0).ops (M := []) (by simp [MOk])
  obtain ⟨hr1, -⟩ := compMSX_T (N4s.XofC 1) (protoLay 1) (protoP 1) (baseR 1) (protoProg 1).ops mr0
  rw [slotRP_rows, slotRP_rows, hr0, hr1, protoRows, protoRows, protoCS, protoCS]
  exact ⟨rfl, by rw [one_mul]; rfl⟩

/-! ## The region check -/

/-- **A piece stays in region `π`** (its rows below the link region, its cells in the region);
`shOk k`: key `k`'s shared input forms are in the region (checked once per key). -/
def pieceInB (keys : Array Key) (shOk : Array Bool) (one : Lin) (π : ℕ) : Piece → Bool
  | .sp rs => rs.all fun p => idxInB π p.1 && linInB π p.2.a && linInB π p.2.b && linInB π p.2.c
  | .ins k xh ch own =>
    decide (π * slotM4 ≤ 2 ^ (keys.getD k dkey).A * xh) &&
    decide (2 ^ (keys.getD k dkey).A * xh + (keys.getD k dkey).rows.length + linkN ≤ π * slotM4 + slotM4) &&
    decide (π * slotM4 ≤ 2 ^ (keys.getD k dkey).B * ch) &&
    decide (2 ^ (keys.getD k dkey).B * ch + 2 ^ (keys.getD k dkey).B ≤ π * slotM4 + slotM4) &&
    linInB π one && shOk.getD k false && own.all (linInB π)

/-- The shared forms' check, once per key. -/
def shInB (sh : Array (List Lin)) (π : ℕ) : Array Bool := sh.map fun l => l.all (linInB π)

theorem shInB_get {sh : Array (List Lin)} {π k : ℕ} (h : (shInB sh π).getD k false = true) :
    (sh.getD k []).all (linInB π) = true := by
  simp only [shInB, Array.getD_eq_getD_getElem?, Array.getElem?_map] at h ⊢
  cases e : sh[k]? <;> simp_all

theorem linInB_spec {π : ℕ} {l : Lin} (h : linInB π l = true) {t : ℕ × F} (ht : t ∈ l) :
    π * slotM4 ≤ t.1 ∧ t.1 < π * slotM4 + slotM4 := by
  have := List.all_eq_true.1 h t ht
  simpa [inSB] using this

theorem mem_smul {c : F} {l : Lin} {t : ℕ × F} (h : t ∈ l.smul c) : ∃ t' ∈ l, t.1 = t'.1 := by
  simp only [Lin.smul, List.mem_map] at h
  obtain ⟨t', ht', rfl⟩ := h
  exact ⟨t', ht', rfl⟩

theorem pieceInB_spec {keys : Array Key} {sh : Array (List Lin)} {one : Lin} {π : ℕ}
    (hk : keys.all (Key.ok 21) = true) {pc : Piece} (h : pieceInB keys (shInB sh π) one π pc = true) :
    InSlot π (Piece.rows keys sh one pc) := by
  cases pc with
  | sp rs =>
    intro p hp
    have := List.all_eq_true.1 h p hp
    simp only [Bool.and_eq_true] at this
    obtain ⟨⟨⟨hi, ha⟩, hb⟩, hc⟩ := this
    refine ⟨by simpa [idxInB] using hi, fun s t ht => ?_⟩
    cases s
    · exact linInB_spec ha ht
    · exact linInB_spec hb ht
    · exact linInB_spec hc ht
  | ins k xh ch own =>
    simp only [pieceInB, Bool.and_eq_true, decide_eq_true_eq] at h
    obtain ⟨⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6s⟩, h6o⟩ := h
    have h6 : (sh.getD k [] ++ own).all (linInB π) = true := by
      rw [List.all_append, shInB_get h6s, h6o]; rfl
    obtain ⟨-, -, -, hloc⟩ := Key.ok_spec (key_ok hk k)
    intro p hp
    simp only [Piece.rows, instIR, List.mem_map] at hp
    obtain ⟨⟨r, i⟩, hri, rfl⟩ := hp
    have hri' := List.mk_mem_zipIdx_iff_getElem?.1 hri
    obtain ⟨hil, hr⟩ := List.getElem?_eq_some_iff.1 hri'
    have hrm : r ∈ (keys.getD k dkey).rows := hr ▸ List.getElem_mem hil
    refine ⟨⟨by omega, by omega⟩, fun s t ht => ?_⟩
    rw [Mat.r_inst] at ht
    simp only [instLin, List.mem_flatMap] at ht
    obtain ⟨⟨w, c⟩, hw, ht⟩ := ht
    cases w with
    | one =>
      obtain ⟨t', ht', he⟩ := mem_smul ht
      rw [he]; exact linInB_spec h5 ht'
    | inp j =>
      obtain ⟨t', ht', he⟩ := mem_smul ht
      rw [he]
      have hm : (sh.getD k [] ++ own).getD j [] ∈ (sh.getD k [] ++ own) ∨
          (sh.getD k [] ++ own).getD j [] = [] := by
        rw [List.getD_eq_getElem?_getD]
        rcases hj : (sh.getD k [] ++ own)[j]? with _ | l
        · exact Or.inr rfl
        · exact Or.inl (List.mem_of_getElem? hj)
      rcases hm with hm | hm
      · exact linInB_spec (List.all_eq_true.1 h6 _ hm) ht'
      · rw [hm] at ht'; simp at ht'
    | loc j =>
      simp only [List.mem_singleton] at ht
      subst ht
      have := hloc s r hrm j c hw
      dsimp only
      constructor <;> omega

theorem pcIn_spec {keys : Array Key} {sh : Array (List Lin)} {one : Lin} {π : ℕ}
    (hk : keys.all (Key.ok 21) = true) {pc : List Piece}
    (h : pc.all (pieceInB keys (shInB sh π) one π) = true) :
    InSlot π (pc.flatMap (Piece.rows keys sh one)) := by
  intro p hp
  obtain ⟨q, hq, hp⟩ := List.mem_flatMap.1 hp
  exact pieceInB_spec hk (List.all_eq_true.1 h q hq) p hp

/-! ## Distinct row indices -/

/-- The indices `[s, s + n)`. -/
def ivIdx (iv : ℕ × ℕ) : List ℕ := (List.range iv.2).map (iv.1 + ·)

/-- **A piece's row indices as intervals** `(start, length)`: an instance's rows, or each sparse
row. -/
def ivOf (keys : Array Key) : Piece → List (ℕ × ℕ)
  | .sp rs => rs.map fun p => (p.1, 1)
  | .ins k xh _ _ => [(2 ^ (keys.getD k dkey).A * xh, (keys.getD k dkey).rows.length)]

theorem ivOf_idx (keys : Array Key) (sh : Array (List Lin)) (one : Lin) (pc : Piece) :
    (Piece.rows keys sh one pc).map Prod.fst = (ivOf keys pc).flatMap ivIdx := by
  cases pc with
  | sp rs =>
    simp only [Piece.rows, ivOf]
    induction rs with
    | nil => rfl
    | cons p rs ih => simp [ivIdx, ih]
  | ins k xh ch own =>
    simp only [Piece.rows, instIR, ivOf, ivIdx, List.flatMap_singleton, List.map_map, Function.comp_def]
    apply List.ext_getElem <;> simp

/-- Sorted intervals, each ending before the next starts. -/
def ivsOkB : List (ℕ × ℕ) → Bool
  | a :: b :: l => decide (a.1 + a.2 ≤ b.1) && ivsOkB (b :: l)
  | _ => true

theorem ivsOkB_pairwise : ∀ l : List (ℕ × ℕ), ivsOkB l = true → l.Pairwise fun a b => a.1 + a.2 ≤ b.1
  | [], _ => .nil
  | [_], _ => List.pairwise_singleton _ _
  | a :: b :: l, h => by
    simp only [ivsOkB, Bool.and_eq_true, decide_eq_true_eq] at h
    have ih := ivsOkB_pairwise (b :: l) h.2
    refine List.Pairwise.cons (fun c hc => ?_) ih
    rcases List.mem_cons.1 hc with rfl | hc
    · exact h.1
    · have := List.rel_of_pairwise_cons ih hc; omega

/-- **Disjoint intervals give distinct indices** (checked after sorting by start). -/
theorem ivs_nodup (l : List (ℕ × ℕ)) (h : ivsOkB (l.mergeSort fun a b => decide (a.1 ≤ b.1)) = true) :
    (l.flatMap ivIdx).Nodup := by
  have hp := (List.mergeSort_perm l fun a b => decide (a.1 ≤ b.1)).flatMap_right ivIdx
  refine hp.nodup_iff.1 (List.nodup_flatMap.2 ⟨fun iv _ => ?_, ?_⟩)
  · exact (List.nodup_range).map fun a b h => by simpa using h
  · refine (ivsOkB_pairwise _ h).imp fun {a b} hab => ?_
    show List.Disjoint (ivIdx a) (ivIdx b)
    rw [List.disjoint_left]
    intro x hxa hxb
    simp only [ivIdx, List.mem_map, List.mem_range] at hxa hxb
    omega

/-- The pieces' index check. -/
def idsOkB (keys : Array Key) (pc : List Piece) : Bool :=
  ivsOkB ((pc.flatMap (ivOf keys)).mergeSort fun a b => decide (a.1 ≤ b.1))

theorem idsOkB_spec {keys : Array Key} {sh : Array (List Lin)} {one : Lin} {pc : List Piece}
    (h : idsOkB keys pc = true) : ((pc.flatMap (Piece.rows keys sh one)).map Prod.fst).Nodup := by
  have e : (pc.flatMap (Piece.rows keys sh one)).map Prod.fst = (pc.flatMap (ivOf keys)).flatMap ivIdx := by
    rw [List.map_flatMap, List.flatMap_assoc]
    exact congrArg pc.flatMap (funext fun q => ivOf_idx keys sh one q)
  rw [e]; exact ivs_nodup _ h

/-! ## The fit, checked on rows (the fallback's) -/

/-- Strictly increasing. -/
def strictB : List ℕ → Bool
  | a :: b :: l => decide (a < b) && strictB (b :: l)
  | _ => true

theorem strictB_iff : ∀ l : List ℕ, strictB l = true ↔ l.Pairwise (· < ·)
  | [] => by simp [strictB]
  | [_] => by simp [strictB]
  | a :: b :: l => by
    rw [strictB, Bool.and_eq_true, decide_eq_true_eq, strictB_iff (b :: l)]
    constructor
    · rintro ⟨hab, hl⟩
      refine List.Pairwise.cons (fun c hc => ?_) hl
      rcases List.mem_cons.1 hc with rfl | hc
      · exact hab
      · exact lt_trans hab (List.rel_of_pairwise_cons hl hc)
    · intro h; exact ⟨List.rel_of_pairwise_cons h (List.mem_cons_self ..), h.of_cons⟩

/-- **Distinct indices**, checked by sorting. -/
def idxNodupB (rows : List (ℕ × Row)) : Bool := strictB ((rows.map Prod.fst).mergeSort fun a b => decide (a ≤ b))

theorem idxNodupB_iff (rows : List (ℕ × Row)) : idxNodupB rows = true ↔ (rows.map Prod.fst).Nodup := by
  have hp := List.mergeSort_perm (rows.map Prod.fst) fun a b => decide (a ≤ b)
  rw [idxNodupB, strictB_iff, ← hp.nodup_iff]
  constructor
  · exact fun h => h.imp (ne_of_lt)
  · intro hn
    have hs := List.pairwise_mergeSort (le := fun a b : ℕ => decide (a ≤ b))
      (fun a b c hab hbc => by simp only [decide_eq_true_eq] at *; omega)
      (fun a b => by simp only [Bool.or_eq_true, decide_eq_true_eq]; omega) (rows.map Prod.fst)
    exact (hs.and hn).imp fun ⟨h1, h2⟩ => lt_of_le_of_ne (by simpa using h1) h2

/-- Rows of region `π` (Bool). -/
def inSlotB (π : ℕ) (rows : List (ℕ × Row)) : Bool :=
  rows.all fun p => idxInB π p.1 && linInB π p.2.a && linInB π p.2.b && linInB π p.2.c

theorem linInB_iff {π : ℕ} {l : Lin} : linInB π l = true ↔ ∀ t ∈ l, π * slotM4 ≤ t.1 ∧ t.1 < π * slotM4 + slotM4 := by
  simp [linInB, inSB]

theorem inSlotB_iff (π : ℕ) (rows : List (ℕ × Row)) : inSlotB π rows = true ↔ InSlot π rows := by
  simp only [inSlotB, InSlot, List.all_eq_true, Bool.and_eq_true, linInB_iff]
  refine forall_congr' fun p => imp_congr_right fun _ => ?_
  simp only [idxInB, Bool.and_eq_true, decide_eq_true_eq]
  constructor
  · rintro ⟨⟨⟨hi, ha⟩, hb⟩, hc⟩; exact ⟨hi, fun s => by cases s <;> assumption⟩
  · rintro ⟨hi, hs⟩; exact ⟨⟨⟨hi, hs .a⟩, hs .b⟩, hs .c⟩

/-- **A prototype's fit** (Bool, on its rows). -/
def fitB (π : ℕ) (rows : List (ℕ × Row)) : Bool := inSlotB π rows && idxNodupB rows

theorem fitB_iff (π : ℕ) (rows : List (ℕ × Row)) :
    fitB π rows = true ↔ InSlot π rows ∧ (rows.map Prod.fst).Nodup := by
  rw [fitB, Bool.and_eq_true, inSlotB_iff, idxNodupB_iff]

theorem protoFit_iff : ProtoFit ↔ (fitB 0 (protoRows 0) && fitB 1 (protoRows 1)) = true := by
  rw [Bool.and_eq_true, fitB_iff, fitB_iff]
  constructor
  · intro h; exact ⟨h 0 (by norm_num), h 1 le_rfl⟩
  · rintro ⟨h0, h1⟩ π hπ
    rcases Nat.le_one_iff_eq_zero_or_eq_one.1 hπ with rfl | rfl
    exacts [h0, h1]

/-! ## The arena rows' checks (ASK-P) -/

/-- Template rows indexed in the binding's range (`askPI`'s form, at any rows). -/
def idxAr (π : ℕ) (l : List Row) : List (ℕ × Row) := l.zipIdx.map fun p => (π * slotM4 + arR2 + p.2, p.1)

theorem askPI_eq (π : ℕ) : askPI π = idxAr π (askRowsT π) := rfl

/-- **The arenas' fit of prototype `π`** (Bool, on its rows): its rows below the binding's range, its
template rows at most `arR2N` and in the region (`ArFit`'s conjuncts). -/
def arFitB (π : ℕ) (rows : List (ℕ × Row)) (ar : List Row) : Bool :=
  rows.all (fun p => decide (p.1 < π * slotM4 + arR2)) && decide (ar.length ≤ arR2N) && inSlotB π (idxAr π ar)

theorem arFitB_iff (π : ℕ) (rows : List (ℕ × Row)) (ar : List Row) :
    arFitB π rows ar = true ↔
      (∀ p ∈ rows, p.1 < π * slotM4 + arR2) ∧ ar.length ≤ arR2N ∧ InSlot π (idxAr π ar) := by
  simp only [arFitB, Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq, inSlotB_iff, and_assoc]

theorem arFit_iff : ArFit ↔ (arFitB 0 (protoRows 0) (askRowsT 0) && arFitB 1 (protoRows 1) (askRowsT 1)) = true := by
  rw [Bool.and_eq_true, arFitB_iff, arFitB_iff]
  constructor
  · intro h; exact ⟨h 0 (by norm_num), h 1 le_rfl⟩
  · rintro ⟨h0, h1⟩ π hπ
    rcases Nat.le_one_iff_eq_zero_or_eq_one.1 hπ with rfl | rfl
    exacts [h0, h1]

/-- **The pieces' row indices lie below `b`** (Bool, on the pieces' intervals: the plan's check). -/
def ivBelow (keys : Array Key) (pc : List Piece) (b : ℕ) : Bool :=
  (pc.flatMap (ivOf keys)).all fun iv => decide (iv.1 + iv.2 ≤ b)

theorem ivBelow_spec {keys : Array Key} {sh : Array (List Lin)} {one : Lin} {pc : List Piece} {b : ℕ}
    (h : ivBelow keys pc b = true) : ∀ p ∈ pc.flatMap (Piece.rows keys sh one), p.1 < b := by
  intro p hp
  have e : (pc.flatMap (Piece.rows keys sh one)).map Prod.fst = (pc.flatMap (ivOf keys)).flatMap ivIdx := by
    rw [List.map_flatMap, List.flatMap_assoc]
    exact congrArg pc.flatMap (funext fun q => ivOf_idx keys sh one q)
  have hm : p.1 ∈ (pc.flatMap (ivOf keys)).flatMap ivIdx := e ▸ List.mem_map_of_mem hp
  obtain ⟨iv, hiv, hx⟩ := List.mem_flatMap.1 hm
  have hb := List.all_eq_true.1 h iv hiv
  simp only [decide_eq_true_eq] at hb
  simp only [ivIdx, List.mem_map, List.mem_range] at hx
  obtain ⟨j, hj, hj'⟩ := hx
  omega

/-- **`t` restricted to region `π`'s low coordinates**: `t` below 20, `π`'s bit at 20, `0` above
(so that `eq(starPt t π, π·2^20 + j) = eq(t_<20, j)`). -/
def starPt (t : ℕ → F) (π : ℕ) (l : ℕ) : F := if l < 20 then t l else if l = 20 then (if π = 1 then 1 else 0) else 0

/-! ## The link regions' data, prepared once (B5)

A slot's link region (S-E12c's link rows, S-E13a's kind tie and pinned elements, S-E13b's node rows)
does not depend on the evaluation point. The plan holds, per kind and slot, the head rows and the
node rows grouped by row block (`lkGOf`, lever (a)), and, per distinct `(first row, stream block)`,
the pinned elements in runs of one row block and one cell block (`runsOf`, lever (b)). A run's inner
sums read only the low tables, which every kind shares, so `evalMX4` computes them once per call. -/

/-- The rows before the pinned elements: S-E12c's link rows and the kind tie. -/
def linkHead4 (κ : NodeKind) (σ : ℕ) : List Row := linkRowsB4 κ σ ++ packHead4 κ σ

/-- The link region's first row. -/
def linkBase (σ : ℕ) : ℕ := σ * slotM4 + slotM4 - linkN

/-- The number of pinned elements at slot `σ` (`(packWf4 κ σ).length`, without building the rows). -/
def wfLen (κ : NodeKind) (σ : ℕ) : ℕ :=
  match packB κ σ with
  | some _ => wfSeg.length
  | none => 0

theorem wfLen_eq (κ : NodeKind) (σ : ℕ) : wfLen κ σ = (packWf4 κ σ).length := by
  unfold wfLen packWf4; rcases packB κ σ with _ | ⟨b0, G⟩ <;> simp [wfRows]

/-! ### S-E13b's node rows over a cell dictionary (B5)

The node rows (≈ 8k per kind) have ≈ 36k terms over ≈ 11k distinct cells. Their forms are coded
against a sorted cell dictionary, so that each distinct cell's `eq` value is one product per
evaluation and a term is a lookup. The coding is checked once, at plan init, by decoding (`cokB`). -/

/-- A form coded against a dictionary: `(cell index, coefficient)`. -/
abbrev CForm := List (ℕ × F)

/-- Coded rows by row block: `(row block, [(row low, a, b, c)])`. -/
abbrev CRows := List (ℕ × List (ℕ × CForm × CForm × CForm))

/-- Binary search in a sorted array: the last index whose entry is `≤ x` (fuel-bounded; the coding
is checked). -/
def bsGo (a : Array ℕ) (x : ℕ) (lo hi : ℕ) : ℕ → ℕ
  | 0 => lo
  | f + 1 => if lo + 1 ≥ hi then lo else
    let m := (lo + hi) / 2
    if a.getD m 0 ≤ x then bsGo a x m hi f else bsGo a x lo m f

/-- Adjacent duplicates dropped. -/
def dedupS : List ℕ → List ℕ
  | a :: b :: l => if a = b then dedupS (b :: l) else a :: dedupS (b :: l)
  | l => l

/-- The rows' cells, sorted and distinct. -/
def cellsOf (rows : List (ℕ × Row)) : Array ℕ :=
  (dedupS (((rows.flatMap fun p => p.2.a ++ p.2.b ++ p.2.c).map (·.1)).mergeSort
    fun a b => decide (a ≤ b))).toArray

/-- A form coded against `cs`. -/
def encF (cs : Array ℕ) (l : Lin) : CForm := l.map fun t => (bsGo cs t.1 0 cs.size 64, t.2)

/-- **The coded rows**, grouped by row block. -/
def crowsOf (cs : Array ℕ) (rows : List (ℕ × Row)) : CRows :=
  rows.foldr (fun p G => let r := (p.1 % 2 ^ 11, encF cs p.2.a, encF cs p.2.b, encF cs p.2.c)
    match G with
    | g :: gs => if g.1 = p.1 / 2 ^ 11 then (g.1, r :: g.2) :: gs else (p.1 / 2 ^ 11, [r]) :: G
    | [] => [(p.1 / 2 ^ 11, [r])]) []

/-- A coded form decoded. -/
def decF (cs : Array ℕ) (f : CForm) : Lin := f.map fun e => (cs.getD e.1 0, e.2)

/-- A coded row decoded. -/
def decR (cs : Array ℕ) (h : ℕ) (r : ℕ × CForm × CForm × CForm) : ℕ × Row :=
  (h * 2 ^ 11 + r.1, ⟨decF cs r.2.1, decF cs r.2.2.1, decF cs r.2.2.2⟩)

/-- The coded rows decoded. -/
def decRows (cs : Array ℕ) (G : CRows) : List (ℕ × Row) := G.flatMap fun g => g.2.map (decR cs g.1)

/-- Row lows below `2^11`, cell indices in the dictionary. -/
def cbnd (cs : Array ℕ) (G : CRows) : Bool :=
  G.all fun g => g.2.all fun r => decide (r.1 < 2 ^ 11) &&
    (r.2.1 ++ r.2.2.1 ++ r.2.2.2).all fun e => decide (e.1 < cs.size)

/-- **The coding check**: in bounds, and decoding gives back the rows. -/
def cokB (cs : Array ℕ) (G : CRows) (rows : List (ℕ × Row)) : Bool := cbnd cs G && decide (decRows cs G = rows)

/-- Slot `σ`'s node rows, indexed. -/
def extIRows (κ : NodeKind) (σ : ℕ) : List (ℕ × Row) :=
  ((extRowsC κ σ).zipIdx ((linkHead4 κ σ).length + wfLen κ σ)).map fun p => (linkBase σ + p.2, p.1)

/-- **A slot's link rows, prepared** (lever (a)): the head's length, the head rows and S-E13b's node
rows grouped by row block (`ex`, a thunk: grouped only if the coding check fails), and the node rows
coded against their cell dictionary (`ec`, `eg`; used if `eok`, the coding check). -/
structure LkG where
  nh : ℕ
  hd : GRows
  ex : Thunk GRows
  ec : Array ℕ
  eg : CRows
  eok : Bool

/-- Slot `σ`'s prepared link rows. -/
def lkGOf (κ : NodeKind) (σ : ℕ) : LkG :=
  let rows := extIRows κ σ
  let cs := cellsOf rows
  let G := crowsOf cs rows
  ⟨(linkHead4 κ σ).length, grows (2 ^ 11) (2 ^ 12) ((linkHead4 κ σ).zipIdx.map fun p => (linkBase σ + p.2, p.1)),
    Thunk.mk fun _ => grows (2 ^ 11) (2 ^ 12) rows, cs, G, cokB cs G rows⟩

/-- A kind's grouped link rows, slot by slot (a closed constant per kind). -/
def lkArr (κ : NodeKind) : Array LkG := (Array.range κ.vslots).map (lkGOf κ)

/-- **A kind's link rows, packed** (V4: the flat evaluator, `Flat.pack`), slot by slot. -/
def flArr (κ : NodeKind) : Array Flat.Pk := (Array.range κ.vslots).map fun σ => Flat.pack (linkIRows4 κ σ)

/-- **A run of pinned elements** (lever (b)): `(row block, cell block, [(row low, cell low)])`, the
rows split at `2^11` and the cells at `2^12`, as `ltbOf`'s tables. -/
abbrev PRun := ℕ × ℕ × List (ℕ × ℕ)

/-- **The pinned elements by value** (`wfSeg` has 24 distinct values): `(value, [(row block, [row
low])])`. -/
abbrev PCls := List (F × List (ℕ × List ℕ))

/-- Put the pinned element at row `x`, cell `c` in front of runs. -/
def prStep (x c : ℕ) : List PRun → List PRun
  | r :: rs => if r.1 = x / 2 ^ 11 ∧ r.2.1 = c / 2 ^ 12 then (r.1, r.2.1, (x % 2 ^ 11, c % 2 ^ 12) :: r.2.2) :: rs
    else (x / 2 ^ 11, c / 2 ^ 12, [(x % 2 ^ 11, c % 2 ^ 12)]) :: r :: rs
  | [] => [(x / 2 ^ 11, c / 2 ^ 12, [(x % 2 ^ 11, c % 2 ^ 12)])]

/-- Put row `x` in front of a value's row blocks. -/
def blkIns (x : ℕ) : List (ℕ × List ℕ) → List (ℕ × List ℕ)
  | g :: gs => if g.1 = x / 2 ^ 11 then (g.1, x % 2 ^ 11 :: g.2) :: gs else (x / 2 ^ 11, [x % 2 ^ 11]) :: g :: gs
  | [] => [(x / 2 ^ 11, [x % 2 ^ 11])]

/-- Put the pinned element at row `x` with value `k` in its value's class. -/
def clsIns (k : F) (x : ℕ) : PCls → PCls
  | c :: cs => if c.1 = k then (c.1, blkIns x c.2) :: cs else c :: clsIns k x cs
  | [] => [(k, blkIns x [])]

/-- **The pinned elements `ps`** of a stream at block `b0`, at rows `j, j + 1, …`: in runs (for the
cells) and by value (for the constants). -/
def runsOf (b0 : ℕ) : ℕ → List (ℕ × F) → List PRun × PCls
  | _, [] => ([], [])
  | j, p :: ps => let r := runsOf b0 (j + 1) ps; (prStep j (sCell b0 p.1) r.1, clsIns p.2 j r.2)

/-- The distinct `(first row, stream block)` of the slots with pinned elements, over the three kinds
(`(0, 0)`-blocks of `N2`/`N4`/`N8`'s slot 0 coincide, and so do `N2`/`N4`'s slot 1). -/
def pinKeys : List (ℕ × ℕ) :=
  (NodeKind.all.flatMap fun κ => (List.range κ.vslots).filterMap fun σ =>
    (packB κ σ).map fun b => (linkBase σ + (linkHead4 κ σ).length, b.1)).eraseDups

/-! ## The plan -/

/-- Every key's rows and locals fit 20 bits (so its preparation reads coordinates below 20 only,
which both prototypes' points share: `kprep_star`). -/
def lowKeys (keys : Array Key) : Bool := keys.all fun K => decide (K.A ≤ 20) && decide (K.B ≤ 20)

/-- A segment slot's replay cell in its region's local coordinates (SEG-R2): a frame cell (region 1)
moved to region 0, a local at its band (`segCell`). -/
def segLocC (c : ℕ) : ℕ := if c < N4s.repB then c - slotM4 else N4s.segCell (c - N4s.repB)

/-- **Prototype 1's replay rows in a segment region's local coordinates** (SEG-R2): row `k` at `segRow k`,
cells by `segLocC`; every segment slot's rows are these, moved to its region (`repV1_eq`). -/
def seg1Loc (rows : List Row) : List (ℕ × Row) := rows.zipIdx.map fun p => (N4s.segRow p.2, rowMapC segLocC p.1)

/-- A slot's sparse pieces' rows (V5: packed with the template rows, `Plan4.fa0`, `fa1`). -/
def spOf : List Piece → List (ℕ × Row)
  | [] => []
  | .sp rs :: ps => rs ++ spOf ps
  | .ins .. :: ps => spOf ps

/-- A slot's instance pieces (V5: the keyed closed forms evaluate only these). -/
def insOf : List Piece → List Piece
  | [] => []
  | .sp _ :: ps => insOf ps
  | .ins k xh ch own :: ps => .ins k xh ch own :: insOf ps

/-! ### V5: the keys' rows, packed

A key's preparation (`kprep3`) reads its template rows once per evaluation; as nested lists they cost a
pointer chase per term. `kpkOf` packs them once for the plan: the local and `one` terms as flat families
(`FR.Flat`, at the key's row and cell tables), the input terms as one array per matrix. **`kprepP_eq`**: the
packed preparation is `kprep3`, for every key and tables (the tables' sizes are checked; else `kprep3`). -/

/-- A template form's local terms, as cells `k`. -/
def locsOf (l : LinT) : Lin := l.filterMap fun τ => match τ.1 with | .loc k => some (k, τ.2) | _ => none

/-- A template form's `one` terms, at cell `0`. -/
def onesOf (l : LinT) : Lin := l.filterMap fun τ => match τ.1 with | .one => some (0, τ.2) | _ => none

/-- Matrix `s`'s input terms `(row, input, coefficient)`, row by row. -/
def inpsL (s : Mat) (rs : List (RowT × ℕ)) : List (ℕ × ℕ × F) :=
  rs.flatMap fun p => (s.t p.1).filterMap fun τ => match τ.1 with | .inp i => some (p.2, i, τ.2) | _ => none

/-- **A key's rows, packed**: the local terms' and the `one` terms' flat families, each matrix's input terms
and input count. -/
structure KPk where
  loc : Flat.Pk
  one : Flat.Pk
  ia : Array (ℕ × ℕ × F)
  ib : Array (ℕ × ℕ × F)
  ic : Array (ℕ × ℕ × F)
  na : ℕ
  nb : ℕ
  nc : ℕ

/-- The packing of a key's rows (once for the plan). -/
def kpkOf (K : Key) : KPk :=
  ⟨Flat.pack (K.rows.zipIdx.map fun p => (p.2, ⟨locsOf p.1.a, locsOf p.1.b, locsOf p.1.c⟩)),
   Flat.pack (K.rows.zipIdx.map fun p => (p.2, ⟨onesOf p.1.a, onesOf p.1.b, onesOf p.1.c⟩)),
   (inpsL .a K.rows.zipIdx).toArray, (inpsL .b K.rows.zipIdx).toArray, (inpsL .c K.rows.zipIdx).toArray,
   inpNF .a K.rows, inpNF .b K.rows, inpNF .c K.rows⟩

/-- The dense input coefficients from the packed input terms (`inpU`'s additions, in its order). -/
def uOfA (E : Array F) (ins : Array (ℕ × ℕ × F)) (n : ℕ) : Array F :=
  ins.foldl (fun U x => U.modify x.2.1 (· + cmulF x.2.2 (E.getD x.1 0))) (Array.replicate n 0)

/-- **A key's three preparations from its packed rows** (`kprepP_eq`). -/
def kprepP (tb : Tb) (t u : ℕ → F) (K : Key) (q : KPk) : KP3 :=
  let E := tabOr tb.pt tb.lt t K.A; let S := tabOr tb.pu tb.lu u K.B
  if E.size ≤ 2 ^ 11 ∧ S.size ≤ 2 ^ 12 then
    let lv := Flat.evalPk ⟨E, #[1], S, #[1]⟩ q.loc
    let ov := Flat.evalPk ⟨E, #[1], #[1], #[1]⟩ q.one
    (⟨lv.1, ov.1, uOfA E q.ia q.na⟩, ⟨lv.2.1, ov.2.1, uOfA E q.ib q.nb⟩, ⟨lv.2.2, ov.2.2, uOfA E q.ic q.nc⟩)
  else kprep3 tb t u K

theorem splitAt_one {E : Array F} {p : ℕ} (hp : 0 < p) (h : E.size ≤ p) (x : ℕ) :
    splitAt E #[1] p x = E.getD x 0 := by
  unfold splitAt
  by_cases hx : x < p
  · rw [Nat.mod_eq_of_lt hx, Nat.div_eq_of_lt hx]; simp
  · have h1 : (#[1] : Array F).getD (x / p) 0 = 0 := by
      have : 1 ≤ x / p := (Nat.le_div_iff_mul_le hp).2 (by omega)
      rw [Array.getD_eq_getD_getElem?, Array.getElem?_eq_none (by simp; omega)]; rfl
    have h2 : E.getD x 0 = 0 := by
      rw [Array.getD_eq_getD_getElem?, Array.getElem?_eq_none (by omega)]; rfl
    rw [h1, h2, mul_zero]

theorem linEI_locs (g : ℕ → F) : ∀ l : LinT, linEI (RingHom.id F) g (locsOf l) = locRow g l
  | [] => rfl
  | (w, c) :: l => by
    have ih := linEI_locs g l
    simp only [linEI, locRow, sumL_eq, locsOf, cmul_eq, cmulF_eq, RingHom.id_apply] at ih ⊢
    cases w <;> simp [List.filterMap_cons, ih]

theorem linEI_ones (g : ℕ → F) (hg : g 0 = 1) : ∀ l : LinT, linEI (RingHom.id F) g (onesOf l) = oneRow l
  | [] => rfl
  | (w, c) :: l => by
    have ih := linEI_ones g hg l
    simp only [linEI, oneRow, sumL_eq, onesOf, cmul_eq, RingHom.id_apply] at ih ⊢
    cases w <;> simp [List.filterMap_cons, ih, hg]

theorem rowsVal_pk (s : Mat) (gt gs : ℕ → F) (f : LinT → Lin) (rs : List (RowT × ℕ)) :
    rowsValI (RingHom.id F) s gt gs (rs.map fun p => (p.2, (⟨f p.1.a, f p.1.b, f p.1.c⟩ : Row))) =
      sumL (fun p => gt p.2 * linEI (RingHom.id F) gs (f (s.t p.1))) rs := by
  cases s <;> simp only [rowsValI, sumL_eq, List.map_map, Function.comp_def, Mat.r, Mat.t]

theorem foldl_inps (E : Array F) (i0 : ℕ) : ∀ (l : LinT) (U : Array F),
    (l.filterMap fun τ => match τ.1 with | .inp i => some (i0, i, τ.2) | _ => none).foldl
        (fun U x => U.modify x.2.1 (· + cmulF x.2.2 (E.getD x.1 0))) U = l.foldl (uStep (getD0 E i0)) U
  | [], _ => rfl
  | (w, c) :: l, U => by
    cases w <;> simp only [List.filterMap_cons, List.foldl_cons, uStep, foldl_inps E i0 l] <;> rfl

theorem uOfA_eq (s : Mat) (E : Array F) (T : List RowT) :
    uOfA E (inpsL s T.zipIdx).toArray (inpNF s T) = inpU s T (getD0 E) := by
  rw [uOfA, List.foldl_toArray, inpsL, List.foldl_flatMap, inpU, inpNF_eq]
  exact congrArg (fun f => T.zipIdx.foldl f _) (funext fun U => funext fun p => foldl_inps E p.2 (s.t p.1) U)

/-- **The packed preparation is `kprep3`.** -/
theorem kprepP_eq (tb : Tb) (t u : ℕ → F) (K : Key) : kprepP tb t u K (kpkOf K) = kprep3 tb t u K := by
  unfold kprepP
  dsimp only
  split_ifs with h
  · have ht : splitAt (tabOr tb.pt tb.lt t K.A) #[1] (2 ^ 11) = getD0 (tabOr tb.pt tb.lt t K.A) :=
      funext (splitAt_one (by norm_num) h.1)
    have hs : splitAt (tabOr tb.pu tb.lu u K.B) #[1] (2 ^ 12) = getD0 (tabOr tb.pu tb.lu u K.B) :=
      funext (splitAt_one (by norm_num) h.2)
    have h1 : splitAt (#[1] : Array F) #[1] (2 ^ 12) 0 = 1 := by simp [splitAt]
    simp only [kpkOf, Flat.evalPk_pack, Flat.sum_termsOf, ht, hs, rowsVal_pk, linEI_locs,
      linEI_ones _ h1, uOfA_eq, kprep3, kprep3F_eq, kprepF, mulNZ_eq]
  · rfl

/-- (+) The sparse pieces' rows in order, the instances in order; (−) an instance's rows are not a sparse
piece's (its row 9 is not collected). -/
theorem spIns_ctl :
    (spOf [.sp [(1, ⟨[], [], []⟩)], .ins 3 0 0 [[(9, 1)]], .sp [(2, ⟨[], [], []⟩)]]).map Prod.fst = [1, 2] ∧
      ((insOf [.sp [(1, ⟨[], [], []⟩)], .ins 3 0 0 [[(9, 1)]], .sp [(2, ⟨[], [], []⟩)]]).map fun
        | .ins k .. => k | .sp _ => 0) = [3] ∧
      ¬ 9 ∈ (spOf [.ins 3 0 0 [[(9, 1)]], .sp [(2, ⟨[], [], []⟩)]]).map Prod.fst := by
  decide

/-- **The 4.1 nodes' plan** (all of `N2`, `N4`, `N8`): the shared keys, each prototype's shared
forms and pieces (its rows, `ok`), the prepared forms, and the checks. -/
structure Plan4 where
  keys : Array Key
  sh0 : Array (List Lin)
  sh1 : Array (List Lin)
  pc0 : List Piece
  pc1 : List Piece
  ok : keys.all (Key.ok 21) = true ∧ pc0.flatMap (Piece.rows keys sh0 (oneP 0)) = protoRows 0 ∧
    pc1.flatMap (Piece.rows keys sh1 (oneP 1)) = protoRows 1
  g0 : Array (List GForm)
  g1 : Array (List GForm)
  p0 : List PPc
  p1 : List PPc
  pats : Array (Array Pat)
  pbs : List ℕ
  hg0 : g0 = sh0.map (·.map (grp 4096))
  hg1 : g1 = sh1.map (·.map (grp 4096))
  hp0 : p0 = (insOf pc0).map (prepPiece pats)
  hp1 : p1 = (insOf pc1).map (prepPiece pats)
  inR : Bool
  hR : inR = true → ProtoFit ∧ lowKeys keys = true ∧ ArFit ∧ RepFit
  /-- Each kind's grouped link rows (B5). -/
  fl2 : Array Flat.Pk
  fl4 : Array Flat.Pk
  fl8 : Array Flat.Pk
  hfl2 : fl2 = flArr .N2
  hfl4 : fl4 = flArr .N4
  hfl8 : fl8 = flArr .N8
  /-- The pinned elements' runs, per `(first row, stream block)` (B5). -/
  pkr : List ((ℕ × ℕ) × (List PRun × PCls))
  hpkr : ∀ p ∈ pkr, p.2 = runsOf p.1.2 p.1.1 wfSeg
  /-- The prototypes' template rows (ASK-P; computed with the template memo, `arOf`). -/
  ar0 : List Row
  ar1 : List Row
  har : ar0 = askRowsT 0 ∧ ar1 = askRowsT 1
  /-- Their indexed rows with the slot's sparse pieces' rows, packed (the prototype's split eq tables). -/
  fa0 : Flat.Pk
  fa1 : Flat.Pk
  hfa : fa0 = Flat.pack (spOf pc0 ++ askPI 0) ∧ fa1 = Flat.pack (spOf pc1 ++ askPI 1)
  /-- The replay rows (REPF; the fallback's), recomputed on demand (`arRepOf`, the fold lemma
  `arRepOf_eq`): the plan is a persistent constant, and marking a 65,760-term form persistent
  overflowed the stack at process start. -/
  rp0 : Thunk (Array Row)
  rp1 : Thunk (Array Row)
  hrp : rp0.get.toList = N4s.repRowsP (N4s.rtC1d 0) 0 ∧ rp1.get.toList = N4s.repRowsP (N4s.rtC1d 1) 1
  /-- Prototype 1's replay rows in a segment region's local coordinates, grouped (SEG-R2, `seg1Loc`). -/
  f1 : Flat.Pk
  hf1 : f1 = Flat.pack (seg1Loc (N4s.repRowsP (N4s.rtC1d 1) 1))
  /-- Prototype 0's replay rows (CF2): its row blocks' rows in local coordinates, grouped (frame part,
  local part), and its `rsWeight` ops prepared at their first rows (`kpOf`; their rows not built). -/
  fF : Flat.Pk
  fL : Flat.Pk
  kps : List (ℕ × KP)
  hrg : ∃ bs : List RBlk, bs.flatMap RBlk.rows = N4s.repRowsP (N4s.rtC1c 0) 0 ∧
    fF = Flat.pack (((blkGo 0 bs [] []).1.map fun p => (p.2, rowFr p.1)) ++
      (kpsRows (blkGo 0 bs [] []).2).map fun p => (p.1, rowFr p.2)) ∧
    fL = Flat.pack (((blkGo 0 bs [] []).1.map fun p => (p.2, rowLoc p.1)) ++
      (kpsRows (blkGo 0 bs [] []).2).map fun p => (p.1, rowLoc p.2)) ∧
    kps = (blkGo 0 bs [] []).2
  /-- The ops with their run placeholders marked (V2: `kpdOf`). -/
  kpd : List (ℕ × KPD)
  hkpd : kpd = kps.map fun q => (q.1, kpdOf q.2)
  /-- The keys with their rows packed (V5: `kpkOf`). -/
  kq : Array (Key × KPk)
  hkq : kq = keys.map fun K => (K, kpkOf K)

/-- A plan from its pieces (the region and key checks computed here, once). -/
def mkPlan4 (keys : Array Key) (sh0 sh1 : Array (List Lin)) (pc0 pc1 : List Piece)
    (pats : Array (Array Pat))
    (ok : keys.all (Key.ok 21) = true ∧ pc0.flatMap (Piece.rows keys sh0 (oneP 0)) = protoRows 0 ∧
      pc1.flatMap (Piece.rows keys sh1 (oneP 1)) = protoRows 1) (ar0 ar1 : List Row)
    (har : ar0 = askRowsT 0 ∧ ar1 = askRowsT 1) (rl1 : List Row)
    (hrl : rl1 = N4s.repRowsP (N4s.rtC1d 1) 1) (rp0 rp1 : Thunk (Array Row))
    (hrp : rp0.get.toList = N4s.repRowsP (N4s.rtC1d 0) 0 ∧ rp1.get.toList = N4s.repRowsP (N4s.rtC1d 1) 1)
    (q : List (Row × ℕ) × List (ℕ × KP))
    (hq : ∃ bs : List RBlk, bs.flatMap RBlk.rows = N4s.repRowsP (N4s.rtC1c 0) 0 ∧ q = blkGo 0 bs [] []) : Plan4 where
  keys := keys
  sh0 := sh0
  sh1 := sh1
  pc0 := pc0
  pc1 := pc1
  ok := ok
  g0 := sh0.map (·.map (grp 4096))
  g1 := sh1.map (·.map (grp 4096))
  p0 := (insOf pc0).map (prepPiece pats)
  p1 := (insOf pc1).map (prepPiece pats)
  pats := pats
  pbs := patBits pats
  hg0 := rfl
  hg1 := rfl
  hp0 := rfl
  hp1 := rfl
  inR := pc0.all (pieceInB keys (shInB sh0 0) (oneP 0) 0) && pc1.all (pieceInB keys (shInB sh1 1) (oneP 1) 1) &&
    idsOkB keys pc0 && idsOkB keys pc1 && lowKeys keys &&
    (ivBelow keys pc0 (0 * slotM4 + arR2) && ivBelow keys pc1 (1 * slotM4 + arR2) &&
      decide (ar0.length ≤ arR2N) && decide (ar1.length ≤ arR2N) && inSlotB 0 (idxAr 0 ar0) &&
      inSlotB 1 (idxAr 1 ar1)) && (repFitS q && repFitB 1 rl1 && ivBelow keys pc1 (slotM4 + N4s.repA))
  hR := fun h => by
    simp only [Bool.and_eq_true, decide_eq_true_eq] at h
    obtain ⟨⟨⟨⟨⟨⟨h0, h1⟩, i0⟩, i1⟩, hk⟩, ⟨⟨⟨⟨⟨b0, b1⟩, l0⟩, l1⟩, s0⟩, s1⟩⟩, ⟨r0, r1⟩, rA⟩ := h
    refine ⟨fun π hπ => ?_, hk, fun π hπ => ?_, ⟨fun π hπ => ?_, ok.2.2 ▸ ivBelow_spec rA⟩⟩
    · rcases Nat.le_one_iff_eq_zero_or_eq_one.1 hπ with rfl | rfl
      · exact ⟨ok.2.1 ▸ pcIn_spec ok.1 h0, ok.2.1 ▸ idsOkB_spec i0⟩
      · exact ⟨ok.2.2 ▸ pcIn_spec ok.1 h1, ok.2.2 ▸ idsOkB_spec i1⟩
    · rcases Nat.le_one_iff_eq_zero_or_eq_one.1 hπ with rfl | rfl
      · rw [askPI_eq, ← har.1, ← ok.2.1, ← inSlotB_iff]
        exact ⟨ivBelow_spec b0, l0, s0⟩
      · rw [askPI_eq, ← har.2, ← ok.2.2, ← inSlotB_iff]
        exact ⟨ivBelow_spec b1, l1, s1⟩
    · rcases Nat.le_one_iff_eq_zero_or_eq_one.1 hπ with rfl | rfl
      · obtain ⟨bs, hb, rfl⟩ := hq; rw [N4s.rtC1d_zero, ← hb]; exact repFitS_spec bs r0
      · rw [← hrl]; exact r1
  fl2 := flArr .N2
  fl4 := flArr .N4
  fl8 := flArr .N8
  hfl2 := rfl
  hfl4 := rfl
  hfl8 := rfl
  pkr := pinKeys.map fun k => (k, runsOf k.2 k.1 wfSeg)
  hpkr := fun p hp => by
    obtain ⟨k, -, rfl⟩ := List.mem_map.1 hp
    dsimp only
  ar0 := ar0
  ar1 := ar1
  har := har
  fa0 := Flat.pack (spOf pc0 ++ idxAr 0 ar0)
  fa1 := Flat.pack (spOf pc1 ++ idxAr 1 ar1)
  hfa := by rw [har.1, har.2]; exact ⟨rfl, rfl⟩
  rp0 := rp0
  rp1 := rp1
  hrp := hrp
  f1 := Flat.pack (seg1Loc rl1)
  hf1 := by rw [hrl]
  fF := Flat.pack ((q.1.map fun p => (p.2, rowFr p.1)) ++ (kpsRows q.2).map fun p => (p.1, rowFr p.2))
  fL := Flat.pack ((q.1.map fun p => (p.2, rowLoc p.1)) ++ (kpsRows q.2).map fun p => (p.1, rowLoc p.2))
  kps := q.2
  hrg := by obtain ⟨bs, hb, rfl⟩ := hq; exact ⟨bs, hb, rfl, rfl, rfl⟩
  kpd := q.2.map fun x => (x.1, kpdOf x.2)
  hkpd := rfl
  kq := keys.map fun K => (K, kpkOf K)
  hkq := rfl

/-- **Prototype `π`'s template rows**, by the memoized trail (`trailMS`: each template built once). -/
def arOf (π : ℕ) : List Row :=
  (trailMS (N4s.XofC π) (protoLay π) (protoP π) (askTG π) [] (CS.init (baseR π)) none 0
    (protoProg π).ops []).reverse

theorem arOf_eq (π : ℕ) : arOf π = askRowsT π := trailMS_T _ _ _ _ _ _ (by simp [MOk])

theorem thunk_get' {α : Type} (f : Unit → α) : (Thunk.mk f).get = f () := rfl

/-- Prototype 1's replay rows as row blocks. -/
def spBlk (rt : RT) (P : Params) (c : CS) (op : Op) (o : List Slot) : RBlk := .sp (rt.rows P c op o)

/-- **The plan's data, the ask rows and the replay blocks, one walk per prototype** (CF2: INIT's
proposal 2 with the replay blocks, `compMSXB`; `planData4` is `noncomputable`, not built). -/
def planDataB : (Array GK × Array (List Lin) × Array (List Lin) × List Piece × List Piece) ×
    (List Row × List RBlk) × (List Row × List RBlk) :=
  let ops0 := (protoProg 0).ops
  let ops1 := (protoProg 1).ops
  let l0 := protoLay 0
  let l1 := protoLay 1
  let ks0 := l0.map Prod.fst
  let kms := (ks0 ++ (l1.map Prod.fst).filter (fun k => !ks0.contains k)).map mkKM
  let q0 := compMSXB (N4s.XofC 0) l0 (protoP 0) (askTG 0) (N4s.rtC1c 0) blk0 []
    (CS.init (baseR 0)) ops0 none [] none 0 [] []
  let r0 := q0.1
  let q1 := compMSXB (N4s.XofC 1) l1 (protoP 1) (askTG 1) (N4s.rtC1d 1) (spBlk (N4s.rtC1d 1))
    r0.2.2 (CS.init (baseR 1)) ops1 none [] none 0 [] []
  let r1 := q1.1
  let p0 := slotRP (oneP 0) kms l0 0 r0.1 r0.2.1.reverse []
  let rps1 := (slotRP (oneP 1) kms l1 (1 * slotM4) r1.1 r1.2.1.reverse p0.2).1
  let g := groupRP p0.1 rps1
  ((g.1, g.2.1, g.2.2.1, piecesOf g.1 g.2.1 (oneP 0) p0.1 g.2.2.2.1, piecesOf g.1 g.2.2.1 (oneP 1) rps1 g.2.2.2.2),
    (q0.2.1.reverse, q0.2.2.reverse), (q1.2.1.reverse, q1.2.2.reverse))

/-- The plan's facts about its data. -/
def DataOk (x : (Array GK × Array (List Lin) × Array (List Lin) × List Piece × List Piece) ×
    (List Row × List RBlk) × (List Row × List RBlk)) : Prop :=
  x.1 = planData4 ∧ x.2.1.1 = askRowsT 0 ∧ x.2.1.2.flatMap RBlk.rows = N4s.repRowsP (N4s.rtC1c 0) 0 ∧
    x.2.2.1 = askRowsT 1 ∧ x.2.2.2.flatMap RBlk.rows = N4s.repRowsP (N4s.rtC1d 1) 1

/-- **The one walk is the plan's data, the ask rows and the replay rows.** -/
theorem planDataB_eq : DataOk planDataB := by
  obtain ⟨-, mr0⟩ := compMSX_T (N4s.XofC 0) (protoLay 0) (protoP 0) (baseR 0)
    (protoProg 0).ops (M := []) (by simp [MOk])
  unfold DataOk planDataB
  simp only [compMSXB_eq]
  rw [trailMB_eq _ _ _ _ _ _ _ _ _ _ _ _ _ (by simp [MOk]), trailMB_eq _ _ _ _ _ _ _ _ _ _ _ _ _ mr0]
  simp only [List.append_nil, List.reverse_reverse]
  refine ⟨rfl, rfl, repBlkX_rows _ _ _ _ blk0_rows _ _, rfl, repBlkX_rows _ _ _ _ (fun _ _ _ _ => rfl) _ _⟩

def planOf4D (x : (Array GK × Array (List Lin) × Array (List Lin) × List Piece × List Piece) ×
    (List Row × List RBlk) × (List Row × List RBlk)) (hx : DataOk x) : Plan4 :=
  -- REPF/CF2: each prototype's ask rows and replay blocks from the compile's walk (`planDataB`). The
  -- fallback's thunks recompute the rows from `d` (so that the compiler does not hoist them into a
  -- closed constant). Prototype 0's `rsWeight` ops are prepared (`blkGo`), not built.
  let d := x.1
  have hd : d = planData4 := hx.1
  let k0 := d.1.size - d.1.size
  let b0 := x.2.1
  let b1 := x.2.2
  have hk : k0 = 0 := Nat.sub_self _
  let q := blkGo 0 b0.2 [] []
  have hq : ∃ bs : List RBlk, bs.flatMap RBlk.rows = N4s.repRowsP (N4s.rtC1c 0) 0 ∧ q = blkGo 0 bs [] [] :=
    ⟨b0.2, hx.2.2.1, rfl⟩
  let t0 : Thunk (Array Row) := Thunk.mk fun _ => (arRepOf k0).2.toArray
  let t1 : Thunk (Array Row) := Thunk.mk fun _ => (arRepOf (k0 + 1)).2.toArray
  have h0 : t0.get.toList = N4s.repRowsP (N4s.rtC1d 0) 0 := by
    show (arRepOf k0).2.toArray.toList = _; rw [hk, arRepOf_eq 0, List.toList_toArray]
  have h1 : t1.get.toList = N4s.repRowsP (N4s.rtC1d 1) 1 := by
    show (arRepOf (k0 + 1)).2.toArray.toList = _; rw [hk, arRepOf_eq 1, List.toList_toArray]
  if h : (d.1.map mkKey).all (Key.ok 21) = true then
    mkPlan4 (d.1.map mkKey) d.2.1 d.2.2.1 d.2.2.2.1 d.2.2.2.2
      (mkPats (d.1.map mkKey).size d.2.2.2.1)
      ⟨h, by rw [hd]; exact planData4_rows.1, by rw [hd]; exact planData4_rows.2⟩ b0.1 b1.1
      ⟨hx.2.1, hx.2.2.2.1⟩ (b1.2.flatMap RBlk.rows) hx.2.2.2.2 t0 t1 ⟨h0, h1⟩ q hq
  else
    -- the fallback's rows depend on `d` (`protoRows (k − k)`), so that the compiler does not hoist
    -- `protoRows 0` into a closed constant built at every process start (S-E13's kernel and init traps)
    mkPlan4 #[] #[] #[] [.sp (protoRows (d.1.size - d.1.size))] [.sp (protoRows (d.1.size - d.1.size + 1))] #[]
      ⟨by simp, by rw [Nat.sub_self]; exact List.flatMap_singleton .., by rw [Nat.sub_self]; exact List.flatMap_singleton ..⟩
      b0.1 b1.1 ⟨hx.2.1, hx.2.2.2.1⟩ (b1.2.flatMap RBlk.rows) hx.2.2.2.2 t0 t1 ⟨h0, h1⟩ q hq

/-- **The 4.1 nodes' plan, built once per process** (B-16): from proved pieces, no run-time row
comparison. -/
def planOf4 : Plan4 := planOf4D planDataB planDataB_eq

/-! ## A prototype's value -/

/-- The evaluation tables of a prototype's point. -/
def tb4 (pl : Plan4) (π : ℕ) (t u : ℕ → F) : Tb :=
  tbOf 21 t u (oneP π) (needAll pl.keys (·.A) 12) (needAll pl.keys (·.B) 13 pl.pbs)
    (needAll pl.keys (·.A) 22) (needAll pl.keys (·.B) 24 pl.pbs)

theorem loTab_congr {A : ℕ} {t t' : ℕ → F} (h : ∀ l < A, t l = t' l) : loTab A t = loTab A t' := by
  unfold loTab; congr 1; exact List.map_congr_left fun l hl => h l (List.mem_range.1 hl)

/-- **A key's preparation reads coordinates below its bits only.** -/
theorem kprep_star (s : Mat) (t u : ℕ → F) (π π' : ℕ) {K : Key} (hA : K.A ≤ 20) (hB : K.B ≤ 20) :
    kprep s (starPt t π) (starPt u π) K = kprep s (starPt t π') (starPt u π') K := by
  unfold kprep
  rw [loTab_congr (t := starPt t π) (t' := starPt t π') (fun l hl => by simp [starPt, show l < 20 by omega]),
    loTab_congr (t := starPt u π) (t' := starPt u π') (fun l hl => by simp [starPt, show l < 20 by omega])]

theorem kp_shared (pl : Plan4) (hk : lowKeys pl.keys = true) (t u : ℕ → F) :
    pl.keys.map (kprep3 (tb4 pl 0 (starPt t 0) (starPt u 0)) (starPt t 0) (starPt u 0)) =
      pl.keys.map (kprep3 (tb4 pl 1 (starPt t 1) (starPt u 1)) (starPt t 1) (starPt u 1)) := by
  refine Array.map_congr_left fun K hK => ?_
  have h := Array.all_eq_true_iff_forall_mem.1 hk K hK
  simp only [Bool.and_eq_true, decide_eq_true_eq] at h
  simp only [tb4, kprep3_eq, kprep_star _ t u 0 1 h.1 h.2]

/-- The three matrices of rows, sparse. -/
def rows3 (n m : ℕ) (t u : ℕ → F) (rows : List (ℕ × Row)) : F3 :=
  (rowsVal (RingHom.id F) .a n m t u rows, rowsVal (RingHom.id F) .b n m t u rows,
    rowsVal (RingHom.id F) .c n m t u rows)

/-- **The flat evaluator at the split eq tables is `rows3`** (V4; `Flat.evalPk_rows`). -/
theorem flat_rows3 {n m : ℕ} (hn : 11 ≤ n) (hm : 12 ≤ m) (t u : ℕ → F) (rows : List (ℕ × Row)) :
    Flat.evalPk (Flat.tabsOf n m t u) (Flat.pack rows) = rows3 n m t u rows :=
  Flat.evalPk_rows hn hm t u rows

/-- `flat_rows3` at the replay's 20 row and 20 cell coordinates. -/
theorem flat20 (t u : ℕ → F) (rows : List (ℕ × Row)) :
    Flat.evalPk ⟨loTab 11 t, loTab 9 fun l => t (11 + l), loTab 12 u, loTab 8 fun l => u (12 + l)⟩ (Flat.pack rows) =
      rows3 20 20 t u rows :=
  flat_rows3 (n := 20) (m := 20) (by norm_num) (by norm_num) t u rows

/-- The packed rows at a prototype's point, the low tables `t`'s and `u`'s (shared by both prototypes). -/
theorem askF_eq (π : ℕ) (t u : ℕ → F) (rows : List (ℕ × Row)) :
    Flat.evalPk ⟨loTab 11 t, loTab 10 (fun l => starPt t π (11 + l)), loTab 12 u,
      loTab 11 (fun l => starPt u π (12 + l))⟩ (Flat.pack rows) = rows3 21 23 (starPt t π) (starPt u π) rows := by
  rw [loTab_congr (t := t) (t' := starPt t π) (fun l hl => by simp [starPt, show l < 20 by omega]),
    loTab_congr (t := u) (t' := starPt u π) (fun l hl => by simp [starPt, show l < 20 by omega])]
  exact flat_rows3 (n := 21) (m := 23) (by norm_num) (by norm_num) _ _ rows

theorem rows3_append (n m : ℕ) (t u : ℕ → F) (a b : List (ℕ × Row)) :
    rows3 n m t u (a ++ b) = add3 (rows3 n m t u a) (rows3 n m t u b) := by
  simp [rows3, add3, rowsVal_append]

theorem add3_assoc (a b c : F3) : add3 (add3 a b) c = add3 a (add3 b c) := by
  simp only [add3]; refine Prod.ext ?_ (Prod.ext ?_ ?_) <;> simp only <;> abel

/-- **A slot's pieces' rows are its instances' rows and its sparse pieces' rows** (V5). -/
theorem rows3_pieces (n m : ℕ) (t u : ℕ → F) (keys : Array Key) (sh : Array (List Lin)) (one : Lin) :
    ∀ pcs : List Piece, rows3 n m t u (pcs.flatMap (Piece.rows keys sh one)) =
      add3 (rows3 n m t u ((insOf pcs).flatMap (Piece.rows keys sh one))) (rows3 n m t u (spOf pcs))
  | [] => by simp [rows3, rowsVal, add3, insOf, spOf]
  | .sp rs :: ps => by
    rw [List.flatMap_cons, rows3_append, rows3_pieces n m t u keys sh one ps, insOf, spOf, rows3_append,
      Piece.rows]
    simp only [add3]; refine Prod.ext ?_ (Prod.ext ?_ ?_) <;> simp only <;> abel
  | .ins k xh ch own :: ps => by
    rw [List.flatMap_cons, rows3_append, rows3_pieces n m t u keys sh one ps, insOf, spOf, List.flatMap_cons,
      rows3_append, add3_assoc]

/-- **Grouped rows' value at a prototype's point** (ASK-P: the template rows, `askPI`), by its split eq
tables over 21 row and 23 cell coordinates (sparse; one product per entry). -/
def askV (G : GRows) (t u : ℕ → F) : F3 :=
  growsVal3 (loTab 11 t) (loTab 10 fun l => t (11 + l)) (loTab 12 u) (loTab 11 fun l => u (12 + l)) G

theorem askV_eq (t u : ℕ → F) (rows : List (ℕ × Row)) :
    askV (grows (2 ^ 11) (2 ^ 12) rows) t u = rows3 21 23 t u rows := by
  have ht : splitAt (loTab 11 t) (loTab 10 fun l => t (11 + l)) (2 ^ 11) = gN 21 t :=
    splitE_eq (m := 21) (s := 11) (by norm_num) t
  have hu : splitAt (loTab 12 u) (loTab 11 fun l => u (12 + l)) (2 ^ 12) = gN 23 u :=
    splitE_eq (m := 23) (s := 12) (by norm_num) u
  unfold askV
  rw [growsVal3_eq, growsVal_grows, growsVal_grows, growsVal_grows, ht, hu, rowsValI_eq, rowsValI_eq,
    rowsValI_eq]
  rfl

/-! ### V5: prototype 1's tables from prototype 0's; the instances without zero products -/

theorem preTabs_getD (t : ℕ → F) (need : Array Bool) {A : ℕ} (h : A < need.size) :
    (preTabs t need).getD A #[] = if need.getD A false then loTab A t else #[] := by
  simp [preTabs, Array.getD_eq_getD_getElem?, h]

/-- **Prototype 1's tables from prototype 0's** (V5): the tables that read only coordinates below 20 are
prototype 0's (the points agree there, `starPt`); the others are recomputed (`tb4S_eq`). -/
def tb4S (tb0 : Tb) (t u : ℕ → F) : Tb :=
  let t1 := starPt t 1; let u1 := starPt u 1
  let shi := loTab (23 - 12) fun l => u1 (12 + l)
  { tb0 with
    thi := loTab (21 - 11) fun l => t1 (11 + l)
    shi := shi
    e1 := glVal tb0.slo shi (grp 4096 (oneP 1))
    pt := (Array.range tb0.lt.size).map fun A =>
      if A ≤ 20 then tb0.pt.getD A #[] else if tb0.lt.getD A false then loTab A t1 else #[]
    pu := (Array.range tb0.lu.size).map fun B =>
      if B ≤ 20 then tb0.pu.getD B #[] else if tb0.lu.getD B false then loTab B u1 else #[] }

theorem starPt_lo (t : ℕ → F) {l : ℕ} (h : l < 20) : starPt t 0 l = starPt t 1 l := by
  simp [starPt, h]

theorem preTabs_star (t : ℕ → F) (need : Array Bool) :
    ((Array.range need.size).map fun A =>
      if A ≤ 20 then (preTabs (starPt t 0) need).getD A #[] else if need.getD A false then loTab A (starPt t 1)
        else #[]) = preTabs (starPt t 1) need := by
  conv_rhs => unfold preTabs
  refine Array.map_congr_left fun A hA => ?_
  rw [preTabs_getD _ _ (Array.mem_range.1 hA)]
  split_ifs with h1 h2 <;> first | rfl | exact loTab_congr fun l hl => starPt_lo t (by omega)

theorem hiTabs_star (t : ℕ → F) (S : ℕ) (hS : S ≤ 20) (need : Array Bool) :
    hiTabs (starPt t 0) S need = hiTabs (starPt t 1) S need := by
  unfold hiTabs
  refine Array.map_congr_left fun A _ => ?_
  split_ifs
  · exact loTab_congr fun l hl => starPt_lo t (by omega)
  · rfl

/-- **`tb4S` is prototype 1's tables.** -/
theorem tb4S_eq (pl : Plan4) (t u : ℕ → F) : tb4S (tb4 pl 0 (starPt t 0) (starPt u 0)) t u = tb4 pl 1 (starPt t 1) (starPt u 1) := by
  have ht : loTab 11 (starPt t 0) = loTab 11 (starPt t 1) := loTab_congr fun l hl => starPt_lo t (by omega)
  have hu : loTab 12 (starPt u 0) = loTab 12 (starPt u 1) := loTab_congr fun l hl => starPt_lo u (by omega)
  unfold tb4S tb4 tbOf
  dsimp only
  rw [ht, hu, hiTabs_star t 11 (by norm_num), hiTabs_star u 12 (by norm_num), preTabs_star, preTabs_star]

/-- `x · y`, no product if `x = 0`. -/
@[inline] def mulZL (x y : F) : F := if x = 0 then 0 else x * y

theorem mulZL_eq (x y : F) : mulZL x y = x * y := by unfold mulZL; split_ifs with h <;> simp [h]

/-- **`ownSumP3` without zero products** (V5): an own input whose three coefficients are `0` is skipped, so is
a run whose inner sums are `0`; a `0` coefficient or inner sum costs no product (`ownSumP3Z_eq`). -/
def ownSumP3Z (Ua Ub Uc slo shi : Array F) (inr : Array F3) (hf : ℕ → ℕ → F) (ps : Array Pat) :
    ℕ → List OwnP → F3
  | _, [] => (0, 0, 0)
  | j, .g f :: os =>
    let a := Ua.getD j 0; let b := Ub.getD j 0; let c := Uc.getD j 0
    if a = 0 ∧ b = 0 ∧ c = 0 then ownSumP3Z Ua Ub Uc slo shi inr hf ps (j + 1) os
    else
      let e := glVal slo shi f
      add3 (mulZL a e, mulZL b e, mulZL c e) (ownSumP3Z Ua Ub Uc slo shi inr hf ps (j + 1) os)
  | j, .run i ch :: os =>
    let p := ps.getD i dpat
    let v := inr.getD i (0, 0, 0)
    if v = (0, 0, 0) then ownSumP3Z Ua Ub Uc slo shi inr hf ps (j + p.len) os
    else
      let h := hf p.B ch
      add3 (mulZ h v.1, mulZ h v.2.1, mulZ h v.2.2) (ownSumP3Z Ua Ub Uc slo shi inr hf ps (j + p.len) os)

theorem ownSumP3Z_eq (Ua Ub Uc slo shi : Array F) (inr : Array F3) (hf : ℕ → ℕ → F) (ps : Array Pat) :
    ∀ (j : ℕ) (os : List OwnP), ownSumP3Z Ua Ub Uc slo shi inr hf ps j os = ownSumP3 Ua Ub Uc slo shi inr hf ps j os
  | _, [] => rfl
  | j, .g f :: os => by
    rw [ownSumP3Z, ownSumP3, ownSumP3Z_eq Ua Ub Uc slo shi inr hf ps (j + 1) os]
    dsimp only
    split_ifs with h
    · obtain ⟨ha, hb, hc⟩ := h
      simp [ha, hb, hc, add3]
    · simp only [mulZL_eq]
  | j, .run i ch :: os => by
    rw [ownSumP3Z, ownSumP3, ownSumP3Z_eq Ua Ub Uc slo shi inr hf ps _ os]
    dsimp only
    split_ifs with h
    · simp [h, add3]
    · simp only [mulZ_eq]

/-- **`ppv3` without zero products** (V5: `ownSumP3Z`, and `h2 · loc` only for `loc ≠ 0`). -/
def ppv3Z (c : ECtx3) : PPc → F3
  | .sp g => growsVal3 c.tb.tlo c.tb.thi c.tb.slo c.tb.shi g
  | .ins k xh ch own =>
    let K := c.keys.getD k dkey; let P := c.kp.getD k c.dkp
    let h1 := hfac c.tb.ttab c.tb.nt c.tb.thi 11 c.n c.t K.A xh
    let h2 := hfac c.tb.stab c.tb.ns c.tb.shi 12 23 c.u K.B ch
    let sv := c.sv.getD k (0, 0, 0)
    let e := c.ce.getD k c.dce
    let o := ownSumP3Z P.1.u P.2.1.u P.2.2.u c.tb.slo c.tb.shi (c.inr.getD k #[]) (hfS c.tb c.u)
      (c.ps.getD k #[]) (c.nsh.getD k 0) own
    (h1 * (mulZ h2 P.1.loc + e.1 + sv.1 + o.1),
     h1 * (mulZ h2 P.2.1.loc + e.2.1 + sv.2.1 + o.2.1),
     h1 * (mulZ h2 P.2.2.loc + e.2.2 + sv.2.2 + o.2.2))

theorem ppv3Z_eq (c : ECtx3) (p : PPc) : ppv3Z c p = ppv3 c p := by
  cases p with
  | sp g => rfl
  | ins k xh ch own => simp only [ppv3Z, ppv3, ownSumP3Z_eq, mulZ_eq]

/-- A slot's pieces' values (V5: `ppv3Z`). -/
def slotV3Z (c : ECtx3) (pps : List PPc) : F3 := sum3 (ppv3Z c) pps

theorem slotV3Z_eq (c : ECtx3) (pps : List PPc) : slotV3Z c pps = slotV3 c pps := by
  rw [slotV3Z, slotV3, show ppv3Z c = ppv3 c from funext (ppv3Z_eq c)]

theorem kq_map (pl : Plan4) (tb : Tb) (t u : ℕ → F) :
    pl.kq.map (fun q => kprepP tb t u q.1 q.2) = pl.keys.map (kprep3 tb t u) := by
  rw [pl.hkq, Array.map_map]
  exact Array.map_congr_left fun K _ => kprepP_eq tb t u K

/-- **The two prototypes' values at `(t, u)`**: one key preparation, each prototype at its point, its
template rows added (ASK-P). V5: the keys' rows are packed (`kprepP`); the sparse pieces' rows are packed with the template rows, prototype 1's
tables are prototype 0's where they agree (`tb4S`), and the instances skip zero products (`slotV3Z`). -/
def protoV4 (pl : Plan4) (t u : ℕ → F) (node : Bool) : F3 × F3 :=
  let t0 := starPt t 0; let u0 := starPt u 0; let t1 := starPt t 1; let u1 := starPt u 1
  let tb0 := tb4 pl 0 t0 u0
  let kp := pl.kq.map fun q => kprepP tb0 t0 u0 q.1 q.2
  let tlo := loTab 11 t; let slo := loTab 12 u
  (if node then add3 (slotV3Z (ectx3 21 tb0 t0 u0 pl.keys kp pl.g0 pl.pats) pl.p0)
      (Flat.evalPk ⟨tlo, loTab 10 (fun l => t0 (11 + l)), slo, loTab 11 (fun l => u0 (12 + l))⟩ pl.fa0)
   else (0, 0, 0),
   add3 (slotV3Z (ectx3 21 (tb4S tb0 t u) t1 u1 pl.keys kp pl.g1 pl.pats) pl.p1)
     (Flat.evalPk ⟨tlo, loTab 10 (fun l => t1 (11 + l)), slo, loTab 11 (fun l => u1 (12 + l))⟩ pl.fa1))

theorem protoV4_eq (pl : Plan4) (hk : lowKeys pl.keys = true) (t u : ℕ → F) (node : Bool) :
    (protoV4 pl t u node).1 =
        (if node then rows3 21 23 (starPt t 0) (starPt u 0) (protoRows 0 ++ askPI 0) else (0, 0, 0)) ∧
      (protoV4 pl t u node).2 = rows3 21 23 (starPt t 1) (starPt u 1) (protoRows 1 ++ askPI 1) := by
  simp only [protoV4, tb4S_eq, slotV3Z_eq, kq_map]
  refine ⟨?_, ?_⟩
  · split_ifs
    · rw [pl.hfa.1, askF_eq, ← pl.ok.2.1, rows3_append, rows3_append, rows3_pieces, add3_assoc]
      refine congrArg (add3 · _) ?_
      simp only [tb4, slotV3_eq]
      rw [pl.hg0, pl.hp0]
      simp only [slotV_eq _ (by norm_num : 11 ≤ 21) _ _ _ _ _ _ _ _ _ _ pl.ok.1, rows3]
    · rfl
  · rw [kp_shared pl hk, pl.hfa.2, askF_eq, ← pl.ok.2.2, rows3_append, rows3_append, rows3_pieces, add3_assoc]
    refine congrArg (add3 · _) ?_
    simp only [tb4, slotV3_eq]
    rw [pl.hg1, pl.hp1]
    simp only [slotV_eq _ (by norm_num : 11 ≤ 21) _ _ _ _ _ _ _ _ _ _ pl.ok.1, rows3]

/-! ## The copy identity -/

theorem eqN_congr {n : ℕ} {t t' : ℕ → F} (h : ∀ l < n, t l = t' l) (x : ℕ) : eqN n t x = eqN n t' x :=
  Finset.prod_congr rfl fun l hl => by rw [h l (Finset.mem_range.1 hl)]

theorem gN_star {π n : ℕ} (hπ : π ≤ 1) (hn : 21 ≤ n) (t : ℕ → F) {j : ℕ} (hj : j < 2 ^ 20) :
    gN n (starPt t π) (π * slotM4 + j) = eqN 20 t j := by
  have e : π * slotM4 + j = 2 ^ 20 * π + j := by simp only [slotM4]; ring
  rw [e, gN_split (by omega) _ _ hj]
  have h1 : eqN 20 (starPt t π) j = eqN 20 t j := eqN_congr (fun l hl => by simp [starPt, hl]) j
  have h2 : gN (n - 20) (fun l => starPt t π (20 + l)) π = 1 := by
    have hp : π < 2 ^ (n - 20) := lt_of_le_of_lt hπ (Nat.one_lt_two_pow (by omega))
    rw [gN, if_pos hp]; unfold eqN
    refine Finset.prod_eq_one fun l _ => ?_
    rcases Nat.lt_or_ge l 1 with h0 | h0
    · obtain rfl : l = 0 := by omega
      interval_cases π <;> simp [starPt]
    · have hb : π.testBit l = false := Nat.testBit_lt_two_pow (lt_of_le_of_lt hπ
        (lt_of_lt_of_le (by norm_num : 1 < 2 ^ 1) (Nat.pow_le_pow_right (by norm_num) h0)))
      simp only [hb, Bool.false_eq_true, if_false, starPt, show ¬ 20 + l < 20 by omega,
        show 20 + l ≠ 20 by omega, sub_zero]
  rw [h1, h2, mul_one]

/-- The high factor of slot `σ`: `eq(t_[20,lm), σ)`. -/
def hiF (lm : ℕ) (t : ℕ → F) (σ : ℕ) : F := eqN (lm - 20) (fun l => t (20 + l)) σ

theorem gN_row {lm σ : ℕ} (hl : 20 ≤ lm) (hσ : σ < 2 ^ (lm - 20)) (t : ℕ → F) {j : ℕ} (hj : j < 2 ^ 20) :
    gN lm t (σ * slotM4 + j) = eqN 20 t j * hiF lm t σ := by
  have e : σ * slotM4 + j = 2 ^ 20 * σ + j := by simp only [slotM4]; ring
  rw [e, gN_split hl _ _ hj, gN, if_pos hσ, hiF]

theorem gN_two (v : ℕ → F) : gN 2 v 3 = v 0 * v 1 := by
  rw [gN, if_pos (by norm_num), eqN]
  simp only [Finset.prod_range_succ, Finset.prod_range_zero, one_mul]
  simp only [show (3 : ℕ).testBit 0 = true by decide, show (3 : ℕ).testBit 1 = true by decide, if_true]

theorem gN_cell {lm σ : ℕ} (hl : 20 ≤ lm) (hσ : σ < 2 ^ (lm - 20)) (u : ℕ → F) {x : ℕ} (hx : x < 2 ^ 20) :
    gN (lm + 2) u (σ * slotM4 + x + 3 * 2 ^ lm) = eqN 20 u x * (hiF lm u σ * (u lm * u (lm + 1))) := by
  have e : σ * slotM4 + x + 3 * 2 ^ lm = 2 ^ 20 * (2 ^ (lm - 20) * 3 + σ) + x := by
    rw [show 2 ^ lm = 2 ^ 20 * 2 ^ (lm - 20) by rw [← pow_add]; congr 1; omega]; simp only [slotM4]; ring
  rw [e, gN_split (by omega) _ _ hx, gN_split (by omega) _ _ hσ, hiF]
  have e2 : lm + 2 - 20 - (lm - 20) = 2 := by omega
  rw [e2, gN_two]
  have e3 : 20 + (lm - 20 + 0) = lm := by omega
  have e4 : 20 + (lm - 20 + 1) = lm + 1 := by omega
  simp only [e3, e4]

theorem r_rowMapC (s : Mat) (f : ℕ → ℕ) (r : Row) : s.r (rowMapC f r) = mapC f (s.r r) := by cases s <;> rfl

/-- One entry of a moved, absolute row against the prototype's. -/
theorem copy_term {π σ lm : ℕ} (hπ : π ≤ 1) (hl : 20 ≤ lm) (hσ : σ < 2 ^ (lm - 20)) (u : ℕ → F)
    {q : ℕ × F} (hq : π * slotM4 ≤ q.1 ∧ q.1 < π * slotM4 + slotM4) :
    q.2 * gN (lm + 2) u (mvC π σ q.1 + 3 * 2 ^ lm) =
      (hiF lm u σ * (u lm * u (lm + 1))) * (q.2 * gN 23 (starPt u π) q.1) := by
  obtain ⟨hq1, hq2⟩ := hq
  have hx : q.1 - π * slotM4 < 2 ^ 20 := by
    have : slotM4 = 2 ^ 20 := rfl
    omega
  have ec : mvC π σ q.1 + 3 * 2 ^ lm = σ * slotM4 + (q.1 - π * slotM4) + 3 * 2 ^ lm := by
    simp only [mvC]; omega
  have eq' : gN 23 (starPt u π) q.1 = gN 23 (starPt u π) (π * slotM4 + (q.1 - π * slotM4)) := by
    rw [Nat.add_sub_cancel' hq1]
  rw [ec, gN_cell hl hσ u hx, eq', gN_star hπ (by norm_num) u hx]
  ring

/-- **One moved, absolute row** against the prototype's. -/
theorem copy_row {π σ lm : ℕ} (hπ : π ≤ 1) (hl : 20 ≤ lm) (hσ : σ < 2 ^ (lm - 20)) (s : Mat) (t u : ℕ → F)
    {p : ℕ × Row} (hp : (π * slotM4 ≤ p.1 ∧ p.1 + linkN < π * slotM4 + slotM4) ∧
      ∀ s' : Mat, ∀ q ∈ s'.r p.2, π * slotM4 ≤ q.1 ∧ q.1 < π * slotM4 + slotM4) :
    gN lm t (mvC π σ p.1) * linE (RingHom.id F) (lm + 2) u
        (s.r (rowMapC (· + 3 * 2 ^ lm) (rowMapC (mvC π σ) p.2))) =
      (hiF lm t σ * (hiF lm u σ * (u lm * u (lm + 1)))) *
        (gN 21 (starPt t π) p.1 * linE (RingHom.id F) 23 (starPt u π) (s.r p.2)) := by
  obtain ⟨⟨h1, h2⟩, hc⟩ := hp
  have hj : p.1 - π * slotM4 < 2 ^ 20 := by
    have : slotM4 = 2 ^ 20 := rfl
    omega
  have er : mvC π σ p.1 = σ * slotM4 + (p.1 - π * slotM4) := by simp only [mvC]; omega
  have ep : gN 21 (starPt t π) p.1 = gN 21 (starPt t π) (π * slotM4 + (p.1 - π * slotM4)) := by
    rw [Nat.add_sub_cancel' h1]
  have hL : linE (RingHom.id F) (lm + 2) u (s.r (rowMapC (· + 3 * 2 ^ lm) (rowMapC (mvC π σ) p.2))) =
      (hiF lm u σ * (u lm * u (lm + 1))) * linE (RingHom.id F) 23 (starPt u π) (s.r p.2) := by
    rw [r_rowMapC, r_rowMapC]
    simp only [linE, mapC, List.map_map, Function.comp_def, RingHom.id_apply]
    rw [← List.sum_map_mul_left]
    refine congrArg List.sum (List.map_congr_left fun q hq => ?_)
    exact copy_term hπ hl hσ u (hc s q hq)
  rw [er, gN_row hl hσ t hj, hL, ep, gN_star hπ (le_refl _) t hj]
  ring

/-- **A slot's value is its prototype's, scaled** (the region facts given). -/
theorem copy_val {π σ lm : ℕ} (hπ : π ≤ 1) (hl : 20 ≤ lm) (hσ : σ < 2 ^ (lm - 20)) (s : Mat) (t u : ℕ → F)
    {rows : List (ℕ × Row)} (hR : InSlot π rows) :
    rowsVal (RingHom.id F) s lm (lm + 2) t u
        ((mvRows π σ rows).map fun p => (p.1, rowMapC (· + 3 * 2 ^ lm) p.2)) =
      (hiF lm t σ * (hiF lm u σ * (u lm * u (lm + 1)))) * rowsVal (RingHom.id F) s 21 23 (starPt t π) (starPt u π) rows := by
  simp only [rowsVal, mvRows, List.map_map, Function.comp_def]
  rw [← List.sum_map_mul_left]
  exact congrArg List.sum (List.map_congr_left fun p hp => copy_row hπ hl hσ s t u (hR p hp))

/-! ## The replay rows' value (REPF)

Slot 0's replay rows (`N2`, `N4`) sit at rows `κ.vslots·2^20 + k`; their frame cells at `oneCell + c`
(region 0), their locals at `oneCell + κ.vslots·2^20 + (c − repB)`. So their value is the local
coordinates' values of the frame part and the local part (`repLocF`, `repLocL`, kind-independent),
scaled by the regions' high factors (`repV0_eq`). -/

theorem gN_lo {x : ℕ} (hx : x < 2 ^ 20) (t : ℕ → F) : gN 20 t x = eqN 20 t x := by rw [gN, if_pos hx]

/-- The previous node's slot's spare region exists. -/
theorem vslots_lt {κ : NodeKind} (hp : κ.hasPrev = true) : κ.vslots < 2 ^ (κ.dims.logM - 20) := by
  cases κ <;> first | exact absurd hp (by decide) | decide

/-- One term of a replay form, moved by `repMapC κ 0`, against the local coordinates. -/
theorem repMapC_term {κ : NodeKind} (hp : κ.hasPrev = true) (u : ℕ → F) {q : ℕ × F}
    (hq : repCellOk 0 q.1 = true) :
    q.2 * gN (κ.dims.logM + 2) u (N4s.repMapC κ 0 q.1) =
      if q.1 < N4s.repB then (hiF κ.dims.logM u 0 * (u κ.dims.logM * u (κ.dims.logM + 1))) * (q.2 * gN 20 u q.1)
      else (hiF κ.dims.logM u κ.vslots * (u κ.dims.logM * u (κ.dims.logM + 1))) * (q.2 * gN 20 u (q.1 - N4s.repB)) := by
  have hl : 20 ≤ κ.dims.logM := by cases κ <;> decide
  have hv := vslots_lt hp
  have hM : slotM4 = 2 ^ 20 := rfl
  have hB : N4s.repB = 2 ^ 40 := rfl
  have h0 : (0 : ℕ) < 2 ^ (κ.dims.logM - 20) := Nat.two_pow_pos _
  simp only [repCellOk, if_true, Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq] at hq
  have hp0 : protoOf κ 0 = 0 := by simp [protoOf, isPrevSlot, hp]
  simp only [N4s.repMapC, hp0, mvC, oneCell_eq, eq_self_iff_true, if_true]
  split_ifs with h
  · have hx : q.1 < 2 ^ 20 := by rcases hq with hq | hq <;> omega
    have := gN_cell hl h0 u hx
    rw [show 0 * slotM4 + q.1 + 3 * 2 ^ κ.dims.logM = q.1 - 0 * slotM4 + 0 * slotM4 + 3 * 2 ^ κ.dims.logM by
      simp] at this
    rw [this, gN_lo hx]; ring
  · have hx : q.1 - N4s.repB < 2 ^ 20 := by rcases hq with hq | hq <;> omega
    rw [gN_cell hl hv u hx, gN_lo hx]; ring

/-- A replay form's value at the node, from its parts' local values. -/
theorem linE_rep {κ : NodeKind} (hp : κ.hasPrev = true) (u : ℕ → F) :
    ∀ (l : Lin), (∀ q ∈ l, repCellOk 0 q.1 = true) →
      linE (RingHom.id F) (κ.dims.logM + 2) u (mapC (N4s.repMapC κ 0) l) =
        (hiF κ.dims.logM u 0 * (u κ.dims.logM * u (κ.dims.logM + 1))) * linE (RingHom.id F) 20 u (linFr l) +
        (hiF κ.dims.logM u κ.vslots * (u κ.dims.logM * u (κ.dims.logM + 1))) *
          linE (RingHom.id F) 20 u (linLoc l)
  | [], _ => by simp [linE, mapC, linFr, linLoc]
  | q :: l, h => by
    have ih := linE_rep hp u l fun q' hq' => h q' (List.mem_cons_of_mem _ hq')
    have hq := repMapC_term hp u (h q (List.mem_cons_self ..))
    have ec : ∀ (m : ℕ) (v : ℕ → F) (x : ℕ × F) (l' : Lin),
        linE (RingHom.id F) m v (x :: l') = x.2 * gN m v x.1 + linE (RingHom.id F) m v l' := fun _ _ _ _ => by
      simp [linE]
    have em : mapC (N4s.repMapC κ 0) (q :: l) = (N4s.repMapC κ 0 q.1, q.2) :: mapC (N4s.repMapC κ 0) l := rfl
    by_cases h1 : q.1 < N4s.repB
    · rw [if_pos h1] at hq
      have e1 : linFr (q :: l) = q :: linFr l := List.filter_cons_of_pos (by simpa using h1)
      have e2 : linLoc (q :: l) = linLoc l := by
        simp only [linLoc]; rw [List.filter_cons_of_neg (by simpa using h1)]
      rw [em, e1, e2, ec, ec, ih]; dsimp only; rw [hq]; ring
    · rw [if_neg h1] at hq
      have e1 : linFr (q :: l) = linFr l := List.filter_cons_of_neg (by simpa using h1)
      have e2 : linLoc (q :: l) = (q.1 - N4s.repB, q.2) :: linLoc l := by
        simp only [linLoc]; rw [List.filter_cons_of_pos (by simpa using h1)]; rfl
      rw [em, e1, e2, ec, ec, ih]; dsimp only; rw [hq]; ring

/-- A replay row list's fit facts (`repFitB 0`). -/
theorem repFitB0_spec {rows : List Row} (h : repFitB 0 rows = true) :
    rows.length ≤ slotM4 ∧ ∀ r ∈ rows, ∀ t ∈ r.a ++ r.b ++ r.c, repCellOk 0 t.1 = true := by
  simp only [repFitB, if_true, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true] at h
  exact ⟨h.1, h.2⟩

/-- **Slot 0's replay rows' value, one matrix** (`N2`, `N4`): the frame and local parts' local values,
scaled by the regions' high factors. -/
theorem repV0_eq {κ : NodeKind} (hp : κ.hasPrev = true) (t u : ℕ → F) {rows : List Row}
    (hfit : repFitB 0 rows = true) (s : Mat) :
    rowsVal (RingHom.id F) s κ.dims.logM (κ.dims.logM + 2) t u
        (rows.zipIdx.map fun p => (κ.vslots * slotM4 + p.2, rowMapC (N4s.repMapC κ 0) p.1)) =
      (hiF κ.dims.logM t κ.vslots * (u κ.dims.logM * u (κ.dims.logM + 1))) *
        (hiF κ.dims.logM u 0 * rowsVal (RingHom.id F) s 20 20 t u (repLocF rows) +
          hiF κ.dims.logM u κ.vslots * rowsVal (RingHom.id F) s 20 20 t u (repLocL rows)) := by
  have hl : 20 ≤ κ.dims.logM := by cases κ <;> decide
  obtain ⟨hlen, hcell⟩ := repFitB0_spec hfit
  simp only [rowsVal, repLocF, repLocL, List.map_map, Function.comp_def]
  rw [← List.sum_map_mul_left, ← List.sum_map_mul_left, ← List.sum_map_add, ← List.sum_map_mul_left]
  refine congrArg List.sum (List.map_congr_left fun p hp' => ?_)
  obtain ⟨r, k⟩ := p
  obtain ⟨hkl, hr⟩ := List.getElem?_eq_some_iff.1 (List.mk_mem_zipIdx_iff_getElem?.1 hp')
  have hk : k < 2 ^ 20 := lt_of_lt_of_le hkl hlen
  have hrm : r ∈ rows := hr ▸ List.getElem_mem hkl
  have hc : ∀ q ∈ s.r r, repCellOk 0 q.1 = true := fun q hq =>
    hcell r hrm q (by cases s <;> simp only [Mat.r] at hq <;> simp [hq])
  dsimp only
  rw [r_rowMapC, linE_rep hp u _ hc, gN_row hl (vslots_lt hp) t hk, gN_lo hk, r_rowFr, r_rowLoc]
  ring

theorem segCell_lt' {j : ℕ} (hj : j < N4s.segCap) : N4s.segCell j < 2 ^ 20 := by
  have e : N4s.segCap = 52462 := rfl
  unfold N4s.segCell
  by_cases h1 : j < 2 ^ 12
  · rw [if_pos h1]; omega
  · rw [if_neg h1]; by_cases h2 : j < 39744
    · rw [if_pos h2]; omega
    · rw [if_neg h2]; omega

theorem segRow_lt' {k : ℕ} (hk : k < N4s.segRN) : N4s.segRow k < 2 ^ 20 := by
  have e1 : N4s.segRN = 57088 := rfl
  have e2 : N4s.segBN = 24320 := rfl
  have e3 : N4s.repSegB = 991488 := rfl
  have e4 : N4s.repA = 688128 := rfl
  unfold N4s.segRow
  by_cases h : k < N4s.segBN
  · rw [if_pos h]; omega
  · rw [if_neg h]; omega

/-- One term of a segment slot's replay form, moved by `repMapC κ v`, against the local coordinates
(SEG-R2). -/
theorem repMapC_term1 {κ : NodeKind} {v : ℕ} (h1 : protoOf κ v = 1) (hv : v < 2 ^ (κ.dims.logM - 20))
    (u : ℕ → F) {q : ℕ × F} (hq : repCellOk 1 q.1 = true) :
    q.2 * gN (κ.dims.logM + 2) u (N4s.repMapC κ v q.1) =
      (hiF κ.dims.logM u v * (u κ.dims.logM * u (κ.dims.logM + 1))) * (q.2 * gN 20 u (segLocC q.1)) := by
  have hl : 20 ≤ κ.dims.logM := by cases κ <;> decide
  have hM : slotM4 = 2 ^ 20 := rfl
  have hB : N4s.repB = 2 ^ 40 := rfl
  simp only [repCellOk, one_ne_zero, if_false, inSB, Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq,
    one_mul] at hq
  have hx : segLocC q.1 < 2 ^ 20 := by
    unfold segLocC; split_ifs with h
    · omega
    · have hj : q.1 - N4s.repB < N4s.segCap := by rcases hq with hq | hq <;> omega
      exact segCell_lt' hj
  have e : N4s.repMapC κ v q.1 = v * slotM4 + segLocC q.1 + 3 * 2 ^ κ.dims.logM := by
    simp only [N4s.repMapC, segLocC, h1, mvC, one_mul, oneCell_eq, one_ne_zero, if_false]
    split_ifs with h
    · rcases hq with hq | hq <;> omega
    · omega
  rw [e, gN_cell hl hv u hx, gN_lo hx]; ring

/-- A segment slot's replay form's value at the node, from its local value (SEG-R2). -/
theorem linE_rep1 {κ : NodeKind} {v : ℕ} (h1 : protoOf κ v = 1) (hv : v < 2 ^ (κ.dims.logM - 20)) (u : ℕ → F) :
    ∀ (l : Lin), (∀ q ∈ l, repCellOk 1 q.1 = true) →
      linE (RingHom.id F) (κ.dims.logM + 2) u (mapC (N4s.repMapC κ v) l) =
        (hiF κ.dims.logM u v * (u κ.dims.logM * u (κ.dims.logM + 1))) * linE (RingHom.id F) 20 u (mapC segLocC l) := by
  intro l hl
  simp only [linE, mapC, List.map_map, Function.comp_def, RingHom.id_apply]
  rw [← List.sum_map_mul_left]
  exact congrArg List.sum (List.map_congr_left fun q hq => repMapC_term1 h1 hv u (hl q hq))

/-- **A segment slot's replay rows' value, one matrix** (SEG-R2): prototype 1's local value (`seg1Loc`),
scaled by the slot's region's high factors. -/
theorem repV1_eq {κ : NodeKind} {v : ℕ} (h1 : protoOf κ v = 1) (hv : v < 2 ^ (κ.dims.logM - 20)) (t u : ℕ → F)
    {rows : List Row} (hfit : repFitB 1 rows = true) (s : Mat) :
    rowsVal (RingHom.id F) s κ.dims.logM (κ.dims.logM + 2) t u
        (rows.zipIdx.map fun p => (v * slotM4 + N4s.segRow p.2, rowMapC (N4s.repMapC κ v) p.1)) =
      (hiF κ.dims.logM t v * (hiF κ.dims.logM u v * (u κ.dims.logM * u (κ.dims.logM + 1)))) *
        rowsVal (RingHom.id F) s 20 20 t u (seg1Loc rows) := by
  have hl : 20 ≤ κ.dims.logM := by cases κ <;> decide
  simp only [repFitB, one_ne_zero, if_false, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true] at hfit
  obtain ⟨hlen, hcell⟩ := hfit
  simp only [rowsVal, seg1Loc, List.map_map, Function.comp_def]
  rw [← List.sum_map_mul_left]
  refine congrArg List.sum (List.map_congr_left fun p hp' => ?_)
  obtain ⟨r, k⟩ := p
  obtain ⟨hkl, hr⟩ := List.getElem?_eq_some_iff.1 (List.mk_mem_zipIdx_iff_getElem?.1 hp')
  have hrm : r ∈ rows := hr ▸ List.getElem_mem hkl
  have hk : N4s.segRow k < 2 ^ 20 := by
    exact segRow_lt' (lt_of_lt_of_le hkl hlen)
  have hc : ∀ q ∈ s.r r, repCellOk 1 q.1 = true := fun q hq =>
    hcell r hrm q (by cases s <;> simp only [Mat.r] at hq <;> simp [hq])
  dsimp only
  rw [r_rowMapC, linE_rep1 h1 hv u _ hc, gN_row hl hv t hk, gN_lo hk, r_rowMapC]
  ring

/-! ## `evalM` -/

/-- `c · x` over triples. -/
def smul3 (c : F) (x : F3) : F3 := (c * x.1, c * x.2.1, c * x.2.2)

/-- **The link regions' eq tables** (S-E13a; once per evaluation point): `eq(τ, ·)` over `lm` row
coordinates split at `2^11`, `eq(u, ·)` over `lm + 2` cell coordinates split at `2^12`. -/
structure LTb where
  tlo : Array F
  thi : Array F
  slo : Array F
  shi : Array F

/-- The tables at a point. -/
def ltbOf (lm : ℕ) (t u : ℕ → F) : LTb :=
  ⟨loTab 11 t, loTab (lm - 11) (fun l => t (11 + l)), loTab 12 u, loTab (lm + 2 - 12) (fun l => u (12 + l))⟩

/-- **The pinned elements' value** (S-E13a): the rows `pinRow one (sCell b0 e) c` of the list
`ps`, at indices `j, j + 1, …`: for each, the row factor `r = eq(τ, j)` times `E(one)` (matrix
`a`) and times `E(cell) − c·E(one)` (matrix `b`); one product per factor. -/
def wfSum (gt gs : ℕ → F) (e1 : F) (b0 : ℕ) : ℕ → List (ℕ × F) → F3
  | _, [] => (0, 0, 0)
  | j, p :: ps =>
    let r := gt j
    add3 (r * e1, r * (gs (sCell b0 p.1) - p.2 * e1), 0) (wfSum gt gs e1 b0 (j + 1) ps)

theorem rows3_nil (n m : ℕ) (t u : ℕ → F) : rows3 n m t u [] = (0, 0, 0) := by
  simp [rows3, rowsVal]

theorem rows3_cons (n m : ℕ) (t u : ℕ → F) (p : ℕ × Row) (l : List (ℕ × Row)) :
    rows3 n m t u (p :: l) = add3 (rows3 n m t u [p]) (rows3 n m t u l) := by
  rw [← rows3_append]; rfl

/-- **`wfSum` is the pin rows' sparse value.** -/
theorem wfSum_eq (n m : ℕ) (t u : ℕ → F) (one b0 base : ℕ) :
    ∀ (ps : List (ℕ × F)) (k : ℕ),
      rows3 n m t u (((ps.map fun p => pinRow one (sCell b0 p.1) p.2).zipIdx k).map
        fun q => (base + q.2, q.1)) = wfSum (gN n t) (gN m u) (gN m u one) b0 (base + k) ps
  | [], _ => by simp [wfSum, rows3_nil]
  | p :: ps, k => by
    rw [List.map_cons, List.zipIdx_cons, List.map_cons, rows3_cons, wfSum_eq n m t u one b0 base ps (k + 1),
      wfSum, show base + (k + 1) = base + k + 1 by omega]
    congr 1
    simp only [rows3, rowsVal, linE, pinRow, Mat.r, Lin.sub, Lin.cell, Lin.smul, List.map_cons,
      List.map_nil, List.sum_cons, List.sum_nil, List.cons_append, List.nil_append, RingHom.id_apply]
    refine Prod.ext ?_ (Prod.ext ?_ ?_) <;> simp only <;> ring

/-! ### The pinned elements by runs and by value (B5, lever (b)) -/

/-- The pinned elements' inner sums at the low tables: per run `Σ tlo[x]·slo[c]`, per value and row
block `Σ tlo[x]` (additions only). They read the low tables only, so the kinds share them. -/
abbrev PIn := List (ℕ × ℕ × F) × List (F × List (ℕ × F))

/-- The inner sums. -/
def prIn (tlo slo : Array F) (R : List PRun × PCls) : PIn :=
  (R.1.map fun r => (r.1, r.2.1, sumL (fun it => tlo.getD it.1 0 * slo.getD it.2 0) r.2.2),
   R.2.map fun c => (c.1, c.2.map fun g => (g.1, sumL (fun l => tlo.getD l 0) g.2)))

/-- **The pinned elements' value from the inner sums**: with `B = Σ_r thi[r]·shi[r]·ΣB`,
`A = Σ_{k, h} thi[h]·Σ_h` and `C = Σ_k k·Σ_h thi[h]·Σ_h`, the value `(e1·A, B − e1·C, 0)` (`wfSum`'s;
`prVal_runs`). Two products per run and one per value and row block, not five per element. -/
def prVal (thi shi : Array F) (e1 : F) (I : PIn) : F3 :=
  let b := sumL (fun r => thi.getD r.1 0 * shi.getD r.2.1 0 * r.2.2) I.1
  let ys := I.2.map fun c => (c.1, sumL (fun g => thi.getD g.1 0 * g.2) c.2)
  (e1 * sumL (fun y => y.2) ys, b - e1 * sumL (fun y => y.1 * y.2) ys, 0)

/-- The three sums, as plain sums (`prVal`'s specification). -/
def prA (tlo thi : Array F) (C : PCls) : F :=
  (C.map fun c => (c.2.map fun g => thi.getD g.1 0 * (g.2.map fun l => tlo.getD l 0).sum).sum).sum
def prB (tlo thi slo shi : Array F) (R : List PRun) : F :=
  (R.map fun r => thi.getD r.1 0 * shi.getD r.2.1 0 *
    (r.2.2.map fun it => tlo.getD it.1 0 * slo.getD it.2 0).sum).sum
def prC (tlo thi : Array F) (C : PCls) : F :=
  (C.map fun c => c.1 * (c.2.map fun g => thi.getD g.1 0 * (g.2.map fun l => tlo.getD l 0).sum).sum).sum

theorem prVal_eq (tlo thi slo shi : Array F) (e1 : F) (R : List PRun × PCls) :
    prVal thi shi e1 (prIn tlo slo R) =
      (e1 * prA tlo thi R.2, prB tlo thi slo shi R.1 - e1 * prC tlo thi R.2, 0) := by
  simp only [prVal, prIn, sumL_eq, List.map_map, Function.comp_def, prA, prB, prC]

theorem prStep_val (tlo thi slo shi : Array F) (x c : ℕ) (R : List PRun) :
    prB tlo thi slo shi (prStep x c R) =
      splitAt tlo thi (2 ^ 11) x * splitAt slo shi (2 ^ 12) c + prB tlo thi slo shi R := by
  cases R with
  | nil => simp only [prStep, prB, splitAt, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
      add_zero]; ring
  | cons r rs =>
    simp only [prStep]
    split_ifs with h
    · obtain ⟨h1, h2⟩ := h
      simp only [prB, splitAt, List.map_cons, List.sum_cons, h1, h2]
      ring
    · simp only [prB, splitAt, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero]
      ring

theorem blkIns_val (tlo thi : Array F) (x : ℕ) (G : List (ℕ × List ℕ)) :
    ((blkIns x G).map fun g => thi.getD g.1 0 * (g.2.map fun l => tlo.getD l 0).sum).sum =
      splitAt tlo thi (2 ^ 11) x + (G.map fun g => thi.getD g.1 0 * (g.2.map fun l => tlo.getD l 0).sum).sum := by
  cases G with
  | nil => simp only [blkIns, splitAt, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
      add_zero]; ring
  | cons g gs =>
    simp only [blkIns]
    split_ifs with h
    · simp only [splitAt, List.map_cons, List.sum_cons, h]; ring
    · simp only [splitAt, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero]; ring

theorem clsIns_val (tlo thi : Array F) (k : F) (x : ℕ) :
    ∀ C : PCls, prA tlo thi (clsIns k x C) = splitAt tlo thi (2 ^ 11) x + prA tlo thi C ∧
      prC tlo thi (clsIns k x C) = k * splitAt tlo thi (2 ^ 11) x + prC tlo thi C
  | [] => by
    simp only [clsIns, prA, prC, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero,
      blkIns_val]
    constructor <;> first | trivial | ring
  | c :: cs => by
    simp only [clsIns]
    split_ifs with h
    · simp only [prA, prC, List.map_cons, List.sum_cons, blkIns_val, h]
      constructor <;> ring
    · obtain ⟨hA, hC⟩ := clsIns_val tlo thi k x cs
      simp only [prA, prC, List.map_cons, List.sum_cons] at hA hC ⊢
      rw [hA, hC]; constructor <;> ring

/-- **The runs and classes give the pinned elements' value** (`wfSum`). -/
theorem prVal_runs (tlo thi slo shi : Array F) (e1 : F) (b0 : ℕ) :
    ∀ (j : ℕ) (ps : List (ℕ × F)), prVal thi shi e1 (prIn tlo slo (runsOf b0 j ps)) =
      wfSum (splitAt tlo thi (2 ^ 11)) (splitAt slo shi (2 ^ 12)) e1 b0 j ps
  | _, [] => by
    simp only [prVal_eq, runsOf, wfSum, prA, prB, prC, List.map_nil, List.sum_nil, mul_zero, sub_zero]
  | j, p :: ps => by
    have ih := prVal_runs tlo thi slo shi e1 b0 (j + 1) ps
    rw [prVal_eq] at ih ⊢
    obtain ⟨hA, hC⟩ := clsIns_val tlo thi p.2 j (runsOf b0 (j + 1) ps).2
    simp only [runsOf, prStep_val, hA, hC, wfSum, ← ih, add3]
    refine Prod.ext ?_ (Prod.ext ?_ ?_) <;> simp only <;> ring

/-! ### The node rows' value over the dictionary -/

/-- `w · Σ c·E[i]` of a coded form, no product for an empty form. -/
@[inline] def cfVal (E : Array F) (w : F) (f : CForm) : F :=
  match f with
  | [] => 0
  | _ => w * sumL (fun e => cmulF e.2 (E.getD e.1 0)) f

/-- **The coded rows' three values**, `E` the dictionary's cells' `eq` values. -/
def crowsVal3 (tlo thi E : Array F) (G : CRows) : F3 :=
  sum3 (fun h =>
    let x := sum3 (fun r => let w := tlo.getD r.1 0; (cfVal E w r.2.1, cfVal E w r.2.2.1, cfVal E w r.2.2.2)) h.2
    let y := thi.getD h.1 0
    (y * x.1, y * x.2.1, y * x.2.2)) G

theorem cfVal_eq (E : Array F) (w : F) (f : CForm) :
    cfVal E w f = w * (f.map fun e => e.2 * E.getD e.1 0).sum := by
  cases f with
  | nil => simp [cfVal]
  | cons _ _ => simp only [cfVal, sumL_eq, cmulF_eq]

theorem getD_map_lt (cs : Array ℕ) (g : ℕ → F) {i : ℕ} (h : i < cs.size) :
    (cs.map g).getD i 0 = g (cs.getD i 0) := by
  simp [Array.getD_eq_getD_getElem?, Array.getElem?_map, Array.getElem?_eq_getElem h]

theorem linEI_decF (cs : Array ℕ) (g : ℕ → F) (f : CForm) (hf : ∀ e ∈ f, e.1 < cs.size) :
    linEI (RingHom.id F) g (decF cs f) = (f.map fun e => e.2 * (cs.map g).getD e.1 0).sum := by
  simp only [linEI, decF, sumL_eq, List.map_map, Function.comp_def, cmul_eq, RingHom.id_apply]
  exact congrArg List.sum (List.map_congr_left fun e he => by rw [getD_map_lt cs g (hf e he)])

theorem sum_flatMap' {α : Type} (l : List α) (f : α → List F) :
    (l.flatMap f).sum = (l.map fun a => (f a).sum).sum := by
  induction l with
  | nil => simp
  | cons a l ih => simp [List.flatMap_cons, List.sum_append, ih]

/-- One matrix of the coded rows (`sel` its forms, `s` the decoded rows' matrix). -/
theorem crows_sel (tlo thi slo shi : Array F) (cs : Array ℕ) (G : CRows) (hb : cbnd cs G = true)
    (sel : ℕ × CForm × CForm × CForm → CForm) (s : Mat)
    (hs : ∀ h r, s.r (decR cs h r).2 = decF cs (sel r))
    (hsel : ∀ r, ∀ e ∈ sel r, e ∈ r.2.1 ++ r.2.2.1 ++ r.2.2.2) :
    (G.map fun g => thi.getD g.1 0 * (g.2.map fun r => cfVal (cs.map (splitAt slo shi (2 ^ 12)))
        (tlo.getD r.1 0) (sel r)).sum).sum =
      rowsValI (RingHom.id F) s (splitAt tlo thi (2 ^ 11)) (splitAt slo shi (2 ^ 12)) (decRows cs G) := by
  simp only [rowsValI, decRows, sumL_eq, List.map_flatMap, sum_flatMap', List.map_map,
    Function.comp_def]
  refine congrArg List.sum (List.map_congr_left fun g hg => ?_)
  rw [← List.sum_map_mul_left]
  refine congrArg List.sum (List.map_congr_left fun r hr => ?_)
  have hgb := List.all_eq_true.1 hb g hg
  have hrb := List.all_eq_true.1 hgb r hr
  simp only [Bool.and_eq_true, decide_eq_true_eq] at hrb
  obtain ⟨hlo, hix⟩ := hrb
  rw [hs, linEI_decF cs _ _ fun e he => by
    simpa using List.all_eq_true.1 hix e (hsel r e he), cfVal_eq]
  have e1 : (g.1 * 2 ^ 11 + r.1) % 2 ^ 11 = r.1 := by omega
  have e2 : (g.1 * 2 ^ 11 + r.1) / 2 ^ 11 = g.1 := by omega
  simp only [decR, splitAt, e1, e2]
  ring

/-- **The coded rows' value is the decoded rows'** (in bounds). -/
theorem crowsVal3_eq (tlo thi slo shi : Array F) (cs : Array ℕ) (G : CRows) (hb : cbnd cs G = true) :
    crowsVal3 tlo thi (cs.map (splitAt slo shi (2 ^ 12))) G =
      (rowsValI (RingHom.id F) .a (splitAt tlo thi (2 ^ 11)) (splitAt slo shi (2 ^ 12)) (decRows cs G),
       rowsValI (RingHom.id F) .b (splitAt tlo thi (2 ^ 11)) (splitAt slo shi (2 ^ 12)) (decRows cs G),
       rowsValI (RingHom.id F) .c (splitAt tlo thi (2 ^ 11)) (splitAt slo shi (2 ^ 12)) (decRows cs G)) := by
  rw [← crows_sel tlo thi slo shi cs G hb (·.2.1) .a (fun _ _ => rfl) (fun _ _ he => by simp [he]),
    ← crows_sel tlo thi slo shi cs G hb (·.2.2.1) .b (fun _ _ => rfl) (fun _ _ he => by simp [he]),
    ← crows_sel tlo thi slo shi cs G hb (·.2.2.2) .c (fun _ _ => rfl) (fun _ _ he => by simp [he])]
  simp only [crowsVal3, sum3_eq, sumL_eq]

/-! ### The link region's value -/

/-- **The link regions' per-call context**: the tables at the point, and the plan's pinned runs'
inner sums, each a thunk (computed by the first kind that reads it, shared with the others). -/
structure LCx where
  L : LTb
  ths : List ((ℕ × ℕ) × Thunk PIn)
  /-- The previous node's replay rows' frame and local values in local coordinates (REPF; once per
  call, shared by `N2` and `N4`). -/
  rv : Thunk (F3 × F3)
  /-- Prototype 1's replay rows' value in a segment region's local coordinates (SEG-R2; once per call,
  shared by every segment slot of every kind). -/
  rv1 : Thunk F3

/-- The thunks of the plan's runs at the low tables. -/
def thsOf (pl : Plan4) (tlo slo : Array F) : List ((ℕ × ℕ) × Thunk PIn) :=
  pl.pkr.map fun p => (p.1, Thunk.mk fun _ => prIn tlo slo p.2)

/-- The inner sums of the runs at `(first row, stream block)` (regrouped if the plan lacks the key). -/
def innAt (cx : LCx) (k : ℕ × ℕ) : PIn :=
  match cx.ths.find? fun p => decide (p.1 = k) with
  | some p => p.2.get
  | none => prIn cx.L.tlo cx.L.slo (runsOf k.2 k.1 wfSeg)

theorem thunk_get {α : Type} (f : Unit → α) : (Thunk.mk f).get = f () := rfl

theorem innAt_thsOf (pl : Plan4) (L : LTb) (rv : Thunk (F3 × F3)) (rv1 : Thunk F3) (k : ℕ × ℕ) :
    innAt ⟨L, thsOf pl L.tlo L.slo, rv, rv1⟩ k = prIn L.tlo L.slo (runsOf k.2 k.1 wfSeg) := by
  unfold innAt
  split
  · rename_i p hp
    have hk := List.find?_some hp
    simp only [decide_eq_true_eq] at hk
    obtain ⟨q, hq, rfl⟩ := List.mem_map.1 (List.mem_of_find?_eq_some hp)
    dsimp only at hk ⊢
    rw [thunk_get, pl.hpkr q hq, hk]
  · dsimp only

/-- **The replay rows' local values** (REPF): the frame and local parts of prototype 0's replay rows
at `(t, u)`'s low 20 coordinates (split tables `2^11 × 2^9`, `2^12 × 2^8`; the low halves shared).
CF2: the row blocks' grouped rows sparse, the `rsWeight` ops in closed form (`kopV`: frame part at
`wF`, locals `0`; local part at `wL`, locals `eq(u, 2^16 + ·)`). V2: the ops' run placeholders in closed
form (`kpsV3FD`, the tables `eq₈(u, ·)` and `eq₁₂(u_[8,20), ·)`). -/
def rvOf (pl : Plan4) (tlo slo : Array F) (t u : ℕ → F) : Thunk (F3 × F3) :=
  Thunk.mk fun _ =>
    let thi := loTab 9 fun l => t (11 + l)
    let shi := loTab 8 fun l => u (12 + l)
    let gt := splitAt tlo thi (2 ^ 11)
    let gu := splitAt slo shi (2 ^ 12)
    let u8 := loTab 8 u
    let hiE := splitAt (loTab 4 fun l => u (8 + l)) shi (2 ^ 4)
    let T : Flat.Tabs := ⟨tlo, thi, slo, shi⟩
    (add3 (Flat.evalPk T pl.fF) (kpsV3FDR gt gu t u (wFA gu) 0 u8 hiE pl.kpd),
      add3 (Flat.evalPk T pl.fL) (kpsV3FDR gt gu t u (wLA gu) 1 u8 hiE pl.kpd))

theorem repV_eq (t u : ℕ → F) (rows : List (ℕ × Row)) :
    growsVal3 (loTab 11 t) (loTab 9 fun l => t (11 + l)) (loTab 12 u) (loTab 8 fun l => u (12 + l))
      (grows (2 ^ 11) (2 ^ 12) rows) = rows3 20 20 t u rows := by
  have ht : splitAt (loTab 11 t) (loTab 9 fun l => t (11 + l)) (2 ^ 11) = gN 20 t :=
    splitE_eq (m := 20) (s := 11) (by norm_num) t
  have hu : splitAt (loTab 12 u) (loTab 8 fun l => u (12 + l)) (2 ^ 12) = gN 20 u :=
    splitE_eq (m := 20) (s := 12) (by norm_num) u
  rw [growsVal3_eq, growsVal_grows, growsVal_grows, growsVal_grows, ht, hu, rowsValI_eq, rowsValI_eq,
    rowsValI_eq]
  rfl

theorem rows3_kF (t u : ℕ → F) (l : List (ℕ × Row)) :
    rows3 20 20 t u (l.map fun p => (p.1, rowFr p.2)) = rmI3 t (wF u) l := by
  simp only [rows3, rmI3, rmI, rowsVal, List.map_map, Function.comp_def, Mat.r_rowFr, linE_linFr]

theorem rows3_kL (t u : ℕ → F) (l : List (ℕ × Row)) :
    rows3 20 20 t u (l.map fun p => (p.1, rowLoc p.2)) = rmI3 t (wL u) l := by
  simp only [rows3, rmI3, rmI, rowsVal, List.map_map, Function.comp_def, Mat.r_rowLoc, linE_linLoc]

theorem add3_swap (a b c : F3) : add3 (add3 a b) c = add3 a (add3 c b) := by
  simp only [add3]; refine Prod.ext ?_ (Prod.ext ?_ ?_) <;> simp only <;> abel

theorem rvOf_get (pl : Plan4) (t u : ℕ → F) : (rvOf pl (loTab 11 t) (loTab 12 u) t u).get =
    (rows3 20 20 t u (repLocF (N4s.repRowsP (N4s.rtC1c 0) 0)), rows3 20 20 t u (repLocL (N4s.repRowsP (N4s.rtC1c 0) 0))) := by
  obtain ⟨bs, hbs, hF, hL, hk⟩ := pl.hrg
  have ht : splitAt (loTab 11 t) (loTab 9 fun l => t (11 + l)) (2 ^ 11) = gN 20 t :=
    splitE_eq (m := 20) (s := 11) (by norm_num) t
  have hu : splitAt (loTab 12 u) (loTab 8 fun l => u (12 + l)) (2 ^ 12) = gN 20 u :=
    splitE_eq (m := 20) (s := 12) (by norm_num) u
  have hhi : ∀ h, splitAt (loTab 4 fun l => u (8 + l)) (loTab 8 fun l => u (12 + l)) (2 ^ 4) h =
      gN 12 (fun l => u (8 + l)) h := fun h => by
    have e := splitE_eq (m := 12) (s := 4) (by norm_num) fun l => u (8 + l)
    have e2 : (fun l => (fun l => u (8 + l)) (4 + l)) = fun l => u (12 + l) := funext fun l => by
      simp only [← Nat.add_assoc]
    rw [splitE, e2] at e
    exact congrFun e h
  rw [rvOf, thunk_get]
  dsimp only
  rw [pl.hkpd, hk, hF, hL, flat20, flat20, rows3_append, rows3_append, rows3_kF, rows3_kL,
    ← wFA_eq _ u (congrFun hu), ← wLA_eq _ u (congrFun hu), add3_swap, add3_swap,
    ← kpsV3FD_split _ _ _ _ _ _ _ _ _ (congrFun ht) (wFA_cb _), ← kpsV3FD_split _ _ _ _ _ _ _ _ _ (congrFun ht) (wLA_cb _),
    kpsV3FD_eq _ _ _ _ _ _ _ _ _ (congrFun hu) rfl hhi, kpsV3FD_eq _ _ _ _ _ _ _ _ _ (congrFun hu) rfl hhi,
    kpsV3F_eq _ _ _ _ _ _ _ (congrFun ht), kpsV3F_eq _ _ _ _ _ _ _ (congrFun ht), ht, hu, wFA_eq _ u (fun _ => rfl),
    wLA_eq _ u (fun _ => rfl), ← hbs]
  simp only [rows3, add3, kpsV3, rowsVal_spF, rowsVal_spL, repLocF, repLocL, spV_zipIdx,
    blk_val _ t u _ _ (wF_cb u), blk_val _ t u _ _ (wL_cb u)]

/-- **Prototype 1's replay rows' local value** (SEG-R2; V4: packed, `f1`) at the split tables. -/
def rv1Of (pl : Plan4) (tlo slo : Array F) (t u : ℕ → F) : Thunk F3 :=
  Thunk.mk fun _ => Flat.evalPk ⟨tlo, loTab 9 fun l => t (11 + l), slo, loTab 8 fun l => u (12 + l)⟩ pl.f1

theorem rv1Of_get (pl : Plan4) (t u : ℕ → F) : (rv1Of pl (loTab 11 t) (loTab 12 u) t u).get =
    rows3 20 20 t u (seg1Loc (N4s.repRowsP (N4s.rtC1d 1) 1)) := by
  rw [rv1Of, thunk_get, pl.hf1, flat20]

/-- **`cx` is the context at `(t, u)`** over `lm` row coordinates. -/
def CxAt (cx : LCx) (lm : ℕ) (t u : ℕ → F) : Prop :=
  cx.L = ltbOf lm t u ∧ (∀ k, innAt cx k = prIn cx.L.tlo cx.L.slo (runsOf k.2 k.1 wfSeg)) ∧
    cx.rv.get = (rows3 20 20 t u (repLocF (N4s.repRowsP (N4s.rtC1c 0) 0)),
      rows3 20 20 t u (repLocL (N4s.repRowsP (N4s.rtC1c 0) 0))) ∧
    cx.rv1.get = rows3 20 20 t u (seg1Loc (N4s.repRowsP (N4s.rtC1d 1) 1))

theorem ltbOf_lo (lm : ℕ) (t u : ℕ → F) : (ltbOf lm t u).tlo = loTab 11 t ∧ (ltbOf lm t u).slo = loTab 12 u := by
  simp only [ltbOf, and_self]

theorem cxAt_mk (pl : Plan4) (lm : ℕ) (t u : ℕ → F) (L : LTb) (hL : L = ltbOf lm t u) :
    CxAt ⟨L, thsOf pl L.tlo L.slo, rvOf pl L.tlo L.slo t u, rv1Of pl L.tlo L.slo t u⟩ lm t u := by
  refine ⟨hL, innAt_thsOf pl L (rvOf pl L.tlo L.slo t u) (rv1Of pl L.tlo L.slo t u), ?_⟩
  rw [(congrArg LTb.tlo hL).trans (ltbOf_lo lm t u).1, (congrArg LTb.slo hL).trans (ltbOf_lo lm t u).2]
  exact ⟨rvOf_get pl t u, rv1Of_get pl t u⟩

/-- `cxAt_mk` at a table literal (its low tables named, so that no `loTab` is unfolded). -/
theorem cxAt_lo (pl : Plan4) (lm : ℕ) (t u : ℕ → F) (lo so : Array F) (hi : Array F × Array F)
    (hL : (⟨lo, hi.1, so, hi.2⟩ : LTb) = ltbOf lm t u) :
    CxAt ⟨⟨lo, hi.1, so, hi.2⟩, thsOf pl lo so, rvOf pl lo so t u, rv1Of pl lo so t u⟩ lm t u :=
  cxAt_mk pl lm t u _ hL

theorem cxAt_of (pl : Plan4) (lm : ℕ) (t u : ℕ → F) :
    CxAt ⟨ltbOf lm t u, thsOf pl (ltbOf lm t u).tlo (ltbOf lm t u).slo,
      rvOf pl (ltbOf lm t u).tlo (ltbOf lm t u).slo t u, rv1Of pl (ltbOf lm t u).tlo (ltbOf lm t u).slo t u⟩ lm t u :=
  cxAt_mk pl lm t u _ rfl

/-- A kind's packed link rows. -/
def flK (pl : Plan4) : NodeKind → Array Flat.Pk
  | .N2 => pl.fl2
  | .N4 => pl.fl4
  | .N8 => pl.fl8

/-- **Slot `σ`'s packed link rows**, from the plan (packed here past the kind's slots). -/
def flAt (pl : Plan4) (κ : NodeKind) (σ : ℕ) : Flat.Pk :=
  match (flK pl κ)[σ]? with
  | some g => g
  | none => Flat.pack (linkIRows4 κ σ)

theorem flAt_eq (pl : Plan4) (κ : NodeKind) (σ : ℕ) : flAt pl κ σ = Flat.pack (linkIRows4 κ σ) := by
  have h : flK pl κ = flArr κ := by cases κ; exacts [pl.hfl2, pl.hfl4, pl.hfl8]
  unfold flAt
  rw [h, flArr, Array.getElem?_map, Array.getElem?_range]
  split_ifs <;> rfl

/-- **A link region's value** (S-E13a's link rows, the kind tie, the pinned elements, S-E13b's node
rows; V4: one packed family per kind and slot, `Flat.pack`) at the context's split tables. -/
def linkV4 (pl : Plan4) (cx : LCx) (κ : NodeKind) (σ : ℕ) : F3 :=
  Flat.evalPk ⟨cx.L.tlo, cx.L.thi, cx.L.slo, cx.L.shi⟩ (flAt pl κ σ)

/-- **`linkV4` is the link rows' sparse value.** -/
theorem linkV4_eq {lm : ℕ} (hl : 11 ≤ lm) (t u : ℕ → F) (pl : Plan4) {cx : LCx} (hc : CxAt cx lm t u)
    (κ : NodeKind) (σ : ℕ) : linkV4 pl cx κ σ = rows3 lm (lm + 2) t u (linkIRows4 κ σ) := by
  obtain ⟨hL, -, -⟩ := hc
  have hT : (⟨cx.L.tlo, cx.L.thi, cx.L.slo, cx.L.shi⟩ : Flat.Tabs) = Flat.tabsOf lm (lm + 2) t u := by
    rw [hL]; simp only [ltbOf, Flat.tabsOf]
  rw [linkV4, flAt_eq, hT]
  exact flat_rows3 hl (by omega) t u _

/-- **Slot `σ`'s arena₁ and bits** (ASK-P): their closed forms at the node's point (`a1V4`, `bitV4`:
a few automaton runs per slot). -/
def arV4 (κ : NodeKind) (t u : ℕ → F) (σ : ℕ) : F3 :=
  add3 (a1V4 κ.dims.logM (κ.dims.logM + 2) t u κ σ (slotB0 κ σ)) (bitV4 κ.dims.logM (κ.dims.logM + 2) t u κ σ)

theorem arV4_eq (κ : NodeKind) (t u : ℕ → F) (σ : ℕ) (hl : 20 ≤ κ.dims.logM) :
    arV4 κ t u σ = add3 (rows3 κ.dims.logM (κ.dims.logM + 2) t u (a1Rows4 κ σ (slotB0 κ σ)))
      (rows3 κ.dims.logM (κ.dims.logM + 2) t u (bitRows4 κ σ)) := by
  rw [arV4, a1V4_eq (n := κ.dims.logM) (m := κ.dims.logM + 2) (by omega) (by omega),
    bitV4_eq (n := κ.dims.logM) (m := κ.dims.logM + 2) (by omega) (by omega)]; rfl

/-- **Slot `σ`'s value** from its prototype's (`vN`, `vS`): the rest scaled, the link region by
`linkV4`. -/
def slotV4o (pl : Plan4) (κ : NodeKind) (t u : ℕ → F) (cx : LCx) (vN vS : F3) (σ : ℕ) : F3 :=
  let lm := κ.dims.logM
  add3 (add3 (smul3 (hiF lm t σ * (hiF lm u σ * (u lm * u (lm + 1)))) (if protoOf κ σ = 0 then vN else vS))
    (arV4 κ t u σ)) (linkV4 pl cx κ σ)

/-- Slot `v`'s replay rows from the plan's rows (`repIRowsW rtC1d`, `repIRowsWP_eq`). -/
def repIRowsWP (pl : Plan4) (κ : NodeKind) (v : ℕ) : List (ℕ × Row) :=
  (if protoOf κ v = 0 then pl.rp0 else pl.rp1).get.toList.zipIdx.map fun p =>
    (N4s.repRowI κ v p.2, rowMapC (N4s.repMapC κ v) p.1)

theorem repIRowsWP_eq (pl : Plan4) (κ : NodeKind) (v : ℕ) : repIRowsWP pl κ v = N4s.repIRowsW N4s.rtC1d κ v := by
  unfold repIRowsWP N4s.repIRowsW
  split_ifs with h
  · rw [h, pl.hrp.1]
  · have h1 : protoOf κ v = 1 := by
      have : protoOf κ v ≤ 1 := by unfold protoOf; split_ifs <;> omega
      omega
    rw [h1, pl.hrp.2]

/-- **Slot `σ`'s replay rows' value** (REPF): the previous node's slot from the context's shared local
values (`cx.rv`: frame and local parts, scaled by their regions' high factors); a segment slot's from the
context's shared local value of prototype 1's (`cx.rv1`, SEG-R2), scaled by its region's high factors. -/
def repV4 (pl : Plan4) (κ : NodeKind) (t u : ℕ → F) (cx : LCx) (σ : ℕ) : F3 :=
  let lm := κ.dims.logM
  if protoOf κ σ = 0 then
    let r := cx.rv.get
    smul3 (hiF lm t κ.vslots * (u lm * u (lm + 1)))
      (add3 (smul3 (hiF lm u 0) r.1) (smul3 (hiF lm u κ.vslots) r.2))
  else smul3 (hiF lm t σ * (hiF lm u σ * (u lm * u (lm + 1)))) cx.rv1.get

/-- **`repV4` is the slot's replay rows' sparse value** (the context at the point, the rows fit). -/
theorem repV4_eq (pl : Plan4) (κ : NodeKind) (t u : ℕ → F) {cx : LCx} (hc : CxAt cx κ.dims.logM t u)
    (hR : RepFit) {σ : ℕ} (hσ : σ < κ.vslots) :
    repV4 pl κ t u cx σ = rows3 κ.dims.logM (κ.dims.logM + 2) t u (N4s.repIRowsW N4s.rtC1d κ σ) := by
  unfold repV4
  split_ifs with h0
  · have hp : κ.hasPrev = true ∧ σ = 0 := by
      unfold protoOf isPrevSlot at h0
      split_ifs at h0 with h'
      simpa using h'
    obtain ⟨hp, rfl⟩ := hp
    have hf := hR.1 0 (by norm_num)
    rw [N4s.rtC1d_zero] at hf
    have e : N4s.repIRowsW N4s.rtC1d κ 0 = (N4s.repRowsP (N4s.rtC1c 0) 0).zipIdx.map fun p =>
        (κ.vslots * slotM4 + p.2, rowMapC (N4s.repMapC κ 0) p.1) := by
      simp only [N4s.repIRowsW, N4s.repRowI, N4s.repRow0, h0, if_true, N4s.rtC1d_zero]
    dsimp only
    rw [hc.2.2.1, e]
    simp only [rows3, smul3, add3, repV0_eq hp t u hf]
  · have h1 : protoOf κ σ = 1 := by simp only [protoOf] at h0 ⊢; split_ifs at h0 ⊢ <;> omega
    have hf := hR.1 1 le_rfl
    have hv : σ < 2 ^ (κ.dims.logM - 20) := lt_of_lt_of_le hσ (by cases κ <;> decide)
    have e : N4s.repIRowsW N4s.rtC1d κ σ = (N4s.repRowsP (N4s.rtC1d 1) 1).zipIdx.map fun p =>
        (σ * slotM4 + N4s.segRow p.2, rowMapC (N4s.repMapC κ σ) p.1) := by
      simp only [N4s.repIRowsW, N4s.repRowI, h1, one_ne_zero, ite_false]
    dsimp only
    rw [hc.2.2.2, e]
    simp only [rows3, smul3, repV1_eq h1 hv t u hf]

theorem sum3_add {α : Type*} (f g : α → F3) (l : List α) :
    sum3 (fun x => add3 (f x) (g x)) l = add3 (sum3 f l) (sum3 g l) := by
  simp only [sum3_eq, add3, sumL_eq, List.sum_map_add]

/-- **Slot `σ`'s value** (with its replay rows, REPF). -/
def slotV4 (pl : Plan4) (κ : NodeKind) (t u : ℕ → F) (cx : LCx) (vN vS : F3) (σ : ℕ) : F3 :=
  add3 (slotV4o pl κ t u cx vN vS σ) (repV4 pl κ t u cx σ)

/-- A prototype's rows from the plan's pieces (the fallback's; no closed `protoRows` constant in
the compiled code). -/
def protoRowsP (pl : Plan4) (π : ℕ) : List (ℕ × Row) :=
  if π = 0 then pl.pc0.flatMap (Piece.rows pl.keys pl.sh0 (oneP 0))
  else pl.pc1.flatMap (Piece.rows pl.keys pl.sh1 (oneP 1))

theorem protoRowsP_eq (pl : Plan4) (π : ℕ) (hπ : π ≤ 1) : protoRowsP pl π = protoRows π := by
  unfold protoRowsP; split_ifs with h
  · subst h; exact pl.ok.2.1
  · obtain rfl : π = 1 := by omega
    exact pl.ok.2.2

theorem protoOf_le (κ : NodeKind) (σ : ℕ) : protoOf κ σ ≤ 1 := by unfold protoOf; split_ifs <;> omega

/-- The arenas' fit on the plan's rows (the fallback's; `arFit_iff`). -/
def arFitP (pl : Plan4) : Bool := arFitB 0 (protoRowsP pl 0) pl.ar0 && arFitB 1 (protoRowsP pl 1) pl.ar1

/-- Prototype `π`'s template rows from the plan. -/
def arP (pl : Plan4) (π : ℕ) : List Row := if π = 0 then pl.ar0 else pl.ar1

theorem arP_eq (pl : Plan4) (π : ℕ) (hπ : π ≤ 1) : arP pl π = askRowsT π := by
  unfold arP; split_ifs with h
  · subst h; exact pl.har.1
  · obtain rfl : π = 1 := by omega
    exact pl.har.2

/-- `arIRows4` from the plan's rows (the fallback's). -/
def arIRowsP (pl : Plan4) (κ : NodeKind) (σ : ℕ) : List (ℕ × Row) :=
  if arFitP pl = true then
    a1Rows4 κ σ (slotB0 κ σ) ++ absRows4 κ (mvRows (protoOf κ σ) σ (idxAr (protoOf κ σ) (arP pl (protoOf κ σ)))) ++
      bitRows4 κ σ
  else [(arRej σ, rejR κ)]

theorem arIRowsP_eq (pl : Plan4) (κ : NodeKind) (σ : ℕ) : arIRowsP pl κ σ = arIRows4 κ σ := by
  have hf : arFitP pl = true ↔ ArFit := by
    rw [arFit_iff, arFitP, protoRowsP_eq pl 0 (by norm_num), protoRowsP_eq pl 1 le_rfl, pl.har.1, pl.har.2]
  unfold arIRowsP arIRows4
  by_cases hA : ArFit
  · rw [if_pos (hf.2 hA), if_pos hA, arP_eq pl _ (protoOf_le κ σ), ← askPI_eq]
  · rw [if_neg (mt hf.1 hA), if_neg hA]

/-- `repAllRows` from the plan's rows (the fallback's). -/
def repAllRowsP (pl : Plan4) (κ : NodeKind) : List (ℕ × Row) :=
  if arFitP pl = true then
    (if (repFitB 0 pl.rp0.get.toList && repFitB 1 pl.rp1.get.toList &&
        (protoRowsP pl 1).all fun p => decide (p.1 < slotM4 + N4s.repA)) = true then
      (List.range κ.vslots).flatMap (repIRowsWP pl κ)
      else [(N4s.repSegB, rejR κ)])
  else []

theorem repFit_iff (pl : Plan4) : (repFitB 0 pl.rp0.get.toList && repFitB 1 pl.rp1.get.toList &&
    (protoRowsP pl 1).all fun p => decide (p.1 < slotM4 + N4s.repA)) = true ↔ RepFit := by
  rw [pl.hrp.1, pl.hrp.2, protoRowsP_eq pl 1 le_rfl, Bool.and_eq_true, Bool.and_eq_true, List.all_eq_true]
  simp only [decide_eq_true_eq]
  constructor
  · rintro ⟨⟨h0, h1⟩, hA⟩
    refine ⟨fun π hπ => ?_, hA⟩
    rcases Nat.le_one_iff_eq_zero_or_eq_one.1 hπ with rfl | rfl
    exacts [h0, h1]
  · intro h; exact ⟨⟨h.1 0 (by norm_num), h.1 1 le_rfl⟩, h.2⟩

theorem repAllRowsP_eq (pl : Plan4) (κ : NodeKind) : repAllRowsP pl κ = repAllRows κ := by
  have hf : arFitP pl = true ↔ ArFit := by
    rw [arFit_iff, arFitP, protoRowsP_eq pl 0 (by norm_num), protoRowsP_eq pl 1 le_rfl, pl.har.1, pl.har.2]
  unfold repAllRowsP repAllRows
  by_cases hA : ArFit
  · rw [if_pos (hf.2 hA), if_pos hA]
    by_cases hR : RepFit
    · rw [if_pos ((repFit_iff pl).2 hR), if_pos hR]
      rw [show repIRowsWP pl κ = N4s.repIRowsW N4s.rtC1d κ from funext (repIRowsWP_eq pl κ)]
    · rw [if_neg (mt (repFit_iff pl).1 hR), if_neg hR]
  · rw [if_neg (mt hf.1 hA), if_neg hA]

/-- `nodeIRows4` from the plan's pieces, the fit checked on them (the fallback's). -/
def nodeIRowsP (pl : Plan4) (κ : NodeKind) : List (ℕ × Row) :=
  if (fitB 0 (protoRowsP pl 0) && fitB 1 (protoRowsP pl 1)) = true then
    ((List.range κ.vslots).flatMap fun σ =>
      absRows4 κ (mvRows (protoOf κ σ) σ (protoRowsP pl (protoOf κ σ))) ++ arIRowsP pl κ σ ++ linkIRows4 κ σ) ++
      repAllRowsP pl κ
  else rejectRows κ


theorem nodeIRowsP_eq (pl : Plan4) (κ : NodeKind) : nodeIRowsP pl κ = nodeIRows4 κ := by
  have h : ∀ σ, protoRowsP pl (protoOf κ σ) = protoRows (protoOf κ σ) := fun σ =>
    protoRowsP_eq pl _ (protoOf_le κ σ)
  unfold nodeIRowsP nodeIRows4
  rw [protoRowsP_eq pl 0 (by norm_num), protoRowsP_eq pl 1 le_rfl]
  by_cases hF : ProtoFit
  · rw [if_pos (protoFit_iff.1 hF), if_pos hF]
    simp only [slotRows4, h, arIRowsP_eq, repAllRowsP_eq]
  · rw [if_neg (mt protoFit_iff.2 hF), if_neg hF]

/-- **`evalM` of a 4.1 node** (S-E12b): the two prototypes' values once, every slot from them;
the sparse sum over `nodeIRows4 κ` if a check failed. -/
def evalMT4 (pl : Plan4) (κ : NodeKind) (τ σ : Array F) : F3 :=
  let t := fun l => τ.getD l 0; let u := fun l => σ.getD l 0
  if pl.inR then
    let v := protoV4 pl t u κ.hasPrev
    let L := ltbOf κ.dims.logM t u
    sum3 (slotV4 pl κ t u ⟨L, thsOf pl L.tlo L.slo, rvOf pl L.tlo L.slo t u, rv1Of pl L.tlo L.slo t u⟩ v.1 v.2)
      (List.range κ.vslots)
  else rows3 κ.dims.logM (κ.dims.logM + 2) t u (nodeIRowsP pl κ)

/-- **`evalM`'s specification**: the MLEs of `nodeIRows4 κ`'s matrices (`τ`: `logM` coordinates,
`σ`: `m − 7 = logM + 2`). -/
noncomputable def evalMS4 (κ : NodeKind) (τ σ : Array F) : F3 :=
  (Eval.matMLE (entriesI .a (nodeIRows4 κ)) (Eval.ptOf κ.dims.logM τ) (Eval.ptOf (κ.dims.logM + 2) σ),
   Eval.matMLE (entriesI .b (nodeIRows4 κ)) (Eval.ptOf κ.dims.logM τ) (Eval.ptOf (κ.dims.logM + 2) σ),
   Eval.matMLE (entriesI .c (nodeIRows4 κ)) (Eval.ptOf κ.dims.logM τ) (Eval.ptOf (κ.dims.logM + 2) σ))

theorem logM_ge (κ : NodeKind) : 20 ≤ κ.dims.logM ∧ κ.vslots ≤ 2 ^ (κ.dims.logM - 20) := by
  cases κ <;> decide

theorem sum3_congr {f g : ℕ → F3} {l : List ℕ} (h : ∀ x ∈ l, f x = g x) : sum3 f l = sum3 g l := by
  simp only [sum3_eq, sumL_eq]
  rw [List.map_congr_left fun x hx => congrArg Prod.fst (h x hx),
    List.map_congr_left fun x hx => congrArg (fun y : F3 => y.2.1) (h x hx),
    List.map_congr_left fun x hx => congrArg (fun y : F3 => y.2.2) (h x hx)]

theorem rows3_flatMap (n m : ℕ) (t u : ℕ → F) (l : List ℕ) (f : ℕ → List (ℕ × Row)) :
    rows3 n m t u (l.flatMap f) = sum3 (fun σ => rows3 n m t u (f σ)) l := by
  simp only [rows3, sum3_eq, sumL_eq, rowsVal_flatMap]

theorem rows3_spec (κ : NodeKind) (τ σ : Array F) :
    rows3 κ.dims.logM (κ.dims.logM + 2) (fun l => τ.getD l 0) (fun l => σ.getD l 0) (nodeIRows4 κ) =
      evalMS4 κ τ σ := by
  simp only [rows3, evalMS4, rowsVal_F, Eval.sparse_eq]

/-- **A kind's slot sums are its `evalM`** (the plan's checks passed): at any context at the point,
with the prototypes' values at `node = b`, `b` set if the kind replays the previous node. -/
theorem slots_val (pl : Plan4) (hR : pl.inR = true) (κ : NodeKind) (τ σ : Array F) {cx : LCx}
    (hc : CxAt cx κ.dims.logM (fun l => τ.getD l 0) (fun l => σ.getD l 0)) (b : Bool)
    (hb : κ.hasPrev = true → b = true) :
    sum3 (slotV4 pl κ (fun l => τ.getD l 0) (fun l => σ.getD l 0) cx
        (protoV4 pl (fun l => τ.getD l 0) (fun l => σ.getD l 0) b).1
        (protoV4 pl (fun l => τ.getD l 0) (fun l => σ.getD l 0) b).2) (List.range κ.vslots) =
      evalMS4 κ τ σ := by
  obtain ⟨hF, hk, hA, hRF⟩ := pl.hR hR
  rw [← rows3_spec, nodeIRows4, if_pos hF, rows3_append, rows3_flatMap, repAllRows, if_pos hA, if_pos hRF,
    rows3_flatMap]
  unfold slotV4
  rw [sum3_add]
  refine congrArg₂ add3 ?_ (sum3_congr fun s hs => repV4_eq pl κ _ _ hc hRF (List.mem_range.1 hs))
  obtain ⟨hR0, -⟩ := hF 0 (by norm_num)
  obtain ⟨hR1, -⟩ := hF 1 le_rfl
  obtain ⟨hl, hv⟩ := logM_ge κ
  obtain ⟨hv0, hv1⟩ := protoV4_eq pl hk (fun l => τ.getD l 0) (fun l => σ.getD l 0) b
  refine sum3_congr fun s hs => ?_
  have hs' : s < 2 ^ (κ.dims.logM - 20) := lt_of_lt_of_le (List.mem_range.1 hs) hv
  rw [rows3_append, rows3_append, slotV4o]
  rw [linkV4_eq (by omega) _ _ pl hc]
  refine congrArg (add3 · _) ?_
  have hcp : ∀ π : ℕ, π ≤ 1 → ∀ rows, InSlot π rows →
      smul3 (hiF κ.dims.logM (fun l => τ.getD l 0) s * (hiF κ.dims.logM (fun l => σ.getD l 0) s *
          (σ.getD κ.dims.logM 0 * σ.getD (κ.dims.logM + 1) 0)))
        (rows3 21 23 (starPt (fun l => τ.getD l 0) π) (starPt (fun l => σ.getD l 0) π) rows) =
      rows3 κ.dims.logM (κ.dims.logM + 2) (fun l => τ.getD l 0) (fun l => σ.getD l 0)
        (absRows4 κ (mvRows π s rows)) := by
    intro π hπ rows hr
    have hab : absRows4 κ (mvRows π s rows) =
        (mvRows π s rows).map fun p => (p.1, rowMapC (· + 3 * 2 ^ κ.dims.logM) p.2) := by
      simp only [absRows4, oneCell_eq]
    rw [hab]
    simp only [smul3, rows3, copy_val hπ hl hs' _ (fun l => τ.getD l 0) (fun l => σ.getD l 0) hr]
  have hin : ∀ π : ℕ, π ≤ 1 → InSlot π (protoRows π ++ askPI π) := fun π hπ p hp => by
    rcases List.mem_append.1 hp with hp | hp
    · exact (hF π hπ).1 p hp
    · exact (hA π hπ).2.2 p hp
  have hsm : ∀ (c : F) (x y : F3), smul3 c (add3 x y) = add3 (smul3 c x) (smul3 c y) := fun c x y => by
    simp only [smul3, add3, mul_add]
  have key : smul3 (hiF κ.dims.logM (fun l => τ.getD l 0) s * (hiF κ.dims.logM (fun l => σ.getD l 0) s *
          (σ.getD κ.dims.logM 0 * σ.getD (κ.dims.logM + 1) 0)))
        (rows3 21 23 (starPt (fun l => τ.getD l 0) (protoOf κ s)) (starPt (fun l => σ.getD l 0) (protoOf κ s))
          (protoRows (protoOf κ s) ++ askPI (protoOf κ s))) =
      add3 (rows3 κ.dims.logM (κ.dims.logM + 2) (fun l => τ.getD l 0) (fun l => σ.getD l 0) (slotRows4 κ s))
        (rows3 κ.dims.logM (κ.dims.logM + 2) (fun l => τ.getD l 0) (fun l => σ.getD l 0)
          (absRows4 κ (mvRows (protoOf κ s) s (askPI (protoOf κ s))))) := by
    rw [hcp _ (protoOf_le κ s) _ (hin _ (protoOf_le κ s)), ← rows3_append, slotRows4, absRows4, absRows4,
      absRows4, mvRows, mvRows, mvRows, List.map_append, List.map_append]
  have hvv : (if protoOf κ s = 0 then
        (protoV4 pl (fun l => τ.getD l 0) (fun l => σ.getD l 0) b).1
      else (protoV4 pl (fun l => τ.getD l 0) (fun l => σ.getD l 0) b).2) =
      rows3 21 23 (starPt (fun l => τ.getD l 0) (protoOf κ s)) (starPt (fun l => σ.getD l 0) (protoOf κ s))
        (protoRows (protoOf κ s) ++ askPI (protoOf κ s)) := by
    by_cases hp : protoOf κ s = 0
    · have hk' : κ.hasPrev = true := by
        by_contra hk'; simp [protoOf, isPrevSlot, hk'] at hp
      rw [if_pos hp, hv0, if_pos (hb hk'), hp]
    · have h1 : protoOf κ s = 1 := by
        simp only [protoOf] at hp ⊢; split_ifs at hp ⊢ <;> simp_all
      rw [if_neg hp, hv1, h1]
  rw [hvv, key, arV4_eq κ _ _ s hl, arIRows4, if_pos hA, rows3_append, rows3_append]
  simp only [add3]
  refine Prod.ext ?_ (Prod.ext ?_ ?_) <;> dsimp only <;> abel

/-- **`evalM_eq` for the 4.1 nodes.** -/
theorem evalMT4_eq (pl : Plan4) (κ : NodeKind) (τ σ : Array F) : evalMT4 pl κ τ σ = evalMS4 κ τ σ := by
  unfold evalMT4
  dsimp only
  by_cases hR : pl.inR = true
  · rw [if_pos hR]
    exact slots_val pl hR κ τ σ (cxAt_of pl _ _ _) κ.hasPrev id
  · rw [if_neg hR, nodeIRowsP_eq]; exact rows3_spec κ τ σ

/-! ## Controls -/

/-- (+) `starPt` keeps the low coordinates and sets coordinate 20 to the region's bit; (−) it drops
the coordinates above. -/
theorem star_ctl (t : ℕ → F) : starPt t 1 3 = t 3 ∧ starPt t 1 20 = 1 ∧ starPt t 0 20 = 0 ∧ starPt t 1 21 = 0 := by
  simp [starPt]

/-- (+) A piece inside region 1 passes the check; (−) one whose cell lies in region 0 fails. -/
theorem pieceInB_ctl :
    pieceInB #[] #[] [] 1 (.sp [(2 ^ 20, ⟨[(2 ^ 20 + 1, 1)], [], []⟩)]) = true ∧
      pieceInB #[] #[] [] 1 (.sp [(2 ^ 20, ⟨[(5, 1)], [], []⟩)]) = false := by
  constructor <;> decide

/-- (+) Sorted disjoint intervals pass the index check; (−) overlapping ones fail. -/
theorem ivsOkB_ctl : ivsOkB [(0, 5), (5, 3)] = true ∧ ivsOkB [(0, 5), (4, 1)] = false := by
  constructor <;> decide

/-- (+) Distinct indices pass `idxNodupB`, in any order; (−) a repeated index fails it. -/
theorem idxNodupB_ctl (r : Row) : idxNodupB [(3, r), (1, r)] = true ∧ idxNodupB [(1, r), (1, r)] ≠ true :=
  ⟨(idxNodupB_iff _).2 (by simp), fun h => by simpa using (idxNodupB_iff _).1 h⟩

/-- (+) Two pinned elements in one row block and one cell block share a run, and two with one value
share a class; (−) an element 200 stream elements on (cell block 1) starts a run, and one with
another value starts a class. -/
theorem runsOf_ctl :
    ((runsOf 0 0 [(0, 0), (1, 0)]).1.length, (runsOf 0 0 [(0, 0), (1, 0)]).2.length) = (1, 1) ∧
      ((runsOf 0 0 [(0, 0), (200, 1)]).1.length, (runsOf 0 0 [(0, 0), (200, 1)]).2.length) = (2, 2) := by
  decide

/-- (+) A coding that decodes to the rows passes `cokB`; (−) one whose index points at another cell,
or past the dictionary, fails it. -/
theorem cokB_ctl :
    cokB #[5, 9] [(0, [(1, [(0, 0)], [(1, 0)], [])])] [(1, ⟨[(5, 0)], [(9, 0)], []⟩)] = true ∧
      cokB #[5, 9] [(0, [(1, [(1, 0)], [(1, 0)], [])])] [(1, ⟨[(5, 0)], [(9, 0)], []⟩)] = false ∧
      cokB #[5, 9] [(0, [(1, [(2, 0)], [(1, 0)], [])])] [(1, ⟨[(0, 0)], [(9, 0)], []⟩)] = false := by
  decide

/-- (+) `crowsOf`'s coding against a sorted dictionary (`bsGo`) decodes to the rows (two rows, three
cells, one repeated); (−) against a dictionary missing a cell it does not. (`cellsOf` builds the
dictionary; it is not load-bearing: any dictionary is checked by `cokB`.) -/
theorem crowsOf_ctl :
    cokB #[2, 7, 9] (crowsOf #[2, 7, 9] [(3, ⟨[(7, 0)], [(2, 0)], []⟩), (4, ⟨[(2, 0)], [], [(9, 0)]⟩)])
      [(3, ⟨[(7, 0)], [(2, 0)], []⟩), (4, ⟨[(2, 0)], [], [(9, 0)]⟩)] = true ∧
    cokB #[2, 9] (crowsOf #[2, 9] [(3, ⟨[(7, 0)], [(2, 0)], []⟩), (4, ⟨[(2, 0)], [], [(9, 0)]⟩)])
      [(3, ⟨[(7, 0)], [(2, 0)], []⟩), (4, ⟨[(2, 0)], [], [(9, 0)]⟩)] = false := by
  decide

end Rev4
end FR

end G6_FRNodeRows4Plan
