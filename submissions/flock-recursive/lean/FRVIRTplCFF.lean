-- New for `flock-recursive` (track CF2): the prepared segments' value, three matrices per pass.
import FRVIRTplCFE
import FRVIRTplGrp

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

/-- **One pass over the pattern's rows, three matrices.** -/
def pass3 (cx : Cx) (t u : ℕ → F) (e : Env) (lam : F) (cl X K : ℕ) : ℕ → List RowT → F3
  | _, [] => (0, 0, 0)
  | r, row :: rows =>
    let w := cx.tl.getD (R.low X r) 0
    let c := R.car X r
    let f := fun l : LinT => sumL (fun τ => mul1 τ.2 (R.wv cx t u e lam cl X K c τ.1)) l
    add3 (w * f row.a, w * f row.b, w * f row.c) (pass3 cx t u e lam cl X K (r + 1) rows)

theorem pass3_eq (cx : Cx) (t u : ℕ → F) (e : Env) (lam : F) (cl X K : ℕ) : ∀ (r : ℕ) (rows : List RowT),
    R.pass3 cx t u e lam cl X K r rows =
      (R.pass .a cx t u e lam cl X K r rows, R.pass .b cx t u e lam cl X K r rows, R.pass .c cx t u e lam cl X K r rows)
  | _, [] => rfl
  | r, row :: rows => by
    rw [pass3, pass3_eq cx t u e lam cl X K (r + 1) rows]
    simp only [pass, Mat.t, add3, mul1_eq]

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
