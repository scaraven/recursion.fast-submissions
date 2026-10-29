-- New for `flock-recursive` (BLUEPRINT A.11, §4.3, stage S-E3; track L-circ).
import FRVIR

/-!
# Rows, linear forms and replay templates (the core)

BLUEPRINT A.11. Region M's R1CS rows `⟨a, w⟩ · ⟨b, w⟩ = ⟨c, w⟩` over linear forms of M's cells
(`Circ.Lin`, `Circ.Row`; moved here from `FRVIRCompile` so that the compiler can emit templates).

A **replay template** (`Tpl`) is a straight-line arithmetic circuit over **wires**: the constant
`one`, the op's **inputs** (`inp i`: the `F` components of its operands, in order) and its own
**locals** (`loc k`). Its gates are products (`mul a b`: a new local `a·b`, one row) and inverses
(`inv a`: two locals `i = a⁻¹`, `s = a·i`, three rows, as `FRVIRCompile.invF`). Its outputs are
linear forms over the wires. An **instance** of the template places local `k` at cell
`cellBase + inst·2^b + k` and row `j` at `rowBase + inst·2^a + j` (A.11's alignment), and reads
input `i` through the operand's linear form (`instLin`).

* `Tpl.eqns_of_rows`: if a template's rows hold (with `one = 1`), every gate's equation holds;
* `instLin_ev`: an instantiated form evaluates as the template form at the pulled-back wires.

Per-op templates and their correctness (`tplX_sound`) are in `FRVIRTemplates`; the closed-form
MLE of an aligned group of instances (`tpl_mle`) in `FRVIRTplEval`.
-/

namespace FR
namespace Circ

/-! ## Linear forms and rows -/

/-- A cell assignment of region M (element address ↦ `F`). -/
abbrev Asg := ℕ → F

/-- A linear form over M's cells: `(address, coefficient)` terms. -/
abbrev Lin := List (ℕ × F)

namespace Lin

/-- The value of a linear form. -/
def ev (w : Asg) (l : Lin) : F := (l.map fun t => t.2 * w t.1).sum

/-- The cell `i`. -/
def cell (i : ℕ) : Lin := [(i, 1)]

/-- `c · l`. -/
def smul (c : F) (l : Lin) : Lin := l.map fun t => (t.1, c * t.2)

/-- `a − b`. -/
def sub (a b : Lin) : Lin := a ++ b.smul (-1)

@[simp] theorem ev_nil (w : Asg) : ev w [] = 0 := rfl
@[simp] theorem ev_cons (w : Asg) (t : ℕ × F) (l : Lin) : ev w (t :: l) = t.2 * w t.1 + ev w l := by
  simp [ev]
@[simp] theorem ev_append (w : Asg) (a b : Lin) : ev w (a ++ b) = ev w a + ev w b := by
  simp [ev]
@[simp] theorem ev_cell (w : Asg) (i : ℕ) : ev w (cell i) = w i := by simp [ev, cell]
@[simp] theorem ev_smul (w : Asg) (c : F) (l : Lin) : ev w (smul c l) = c * ev w l := by
  induction l with
  | nil => simp [ev, smul]
  | cons t l ih => simp only [ev, smul, List.map_cons, List.sum_cons] at ih ⊢; rw [ih]; ring
@[simp] theorem ev_sub (w : Asg) (a b : Lin) : ev w (sub a b) = ev w a - ev w b := by
  simp [sub]; ring

end Lin

/-- An R1CS row `⟨a, w⟩ · ⟨b, w⟩ = ⟨c, w⟩`. -/
structure Row where
  a : Lin
  b : Lin
  c : Lin
  deriving DecidableEq

/-- The row holds at `w`. -/
def Row.Holds (w : Asg) (r : Row) : Prop := r.a.ev w * r.b.ev w = r.c.ev w

instance (w : Asg) (r : Row) : Decidable (r.Holds w) := inferInstanceAs (Decidable (_ = _))

end Circ

namespace Tpl
open Circ

/-! ## Wires, forms, rows -/

/-- A template wire. -/
inductive Wire where
  | one
  | inp (i : ℕ)
  | loc (k : ℕ)
  deriving DecidableEq, Inhabited, Hashable

/-- A linear form over wires. -/
abbrev LinT := List (Wire × F)

/-- The wires' values. -/
structure Env where
  one : F
  inp : ℕ → F
  loc : ℕ → F

def Wire.ev (e : Env) : Wire → F
  | .one => e.one
  | .inp i => e.inp i
  | .loc k => e.loc k

/-- The value of a form. -/
def LinT.ev (e : Env) (l : LinT) : F := (l.map fun t => t.2 * t.1.ev e).sum

/-- The local `k`, the input `i`, the constant `c`. -/
def L (k : ℕ) : LinT := [(.loc k, 1)]
def I (i : ℕ) : LinT := [(.inp i, 1)]
def C (c : F) : LinT := [(.one, c)]
/-- `c · l`. -/
def sc (c : F) (l : LinT) : LinT := l.map fun t => (t.1, c * t.2)

@[simp] theorem ev_nil (e : Env) : LinT.ev e [] = 0 := rfl
@[simp] theorem ev_append (e : Env) (a b : LinT) : (a ++ b).ev e = a.ev e + b.ev e := by
  simp [LinT.ev]
@[simp] theorem ev_L (e : Env) (k : ℕ) : (L k).ev e = e.loc k := by simp [LinT.ev, L, Wire.ev]
@[simp] theorem ev_I (e : Env) (i : ℕ) : (I i).ev e = e.inp i := by simp [LinT.ev, I, Wire.ev]
@[simp] theorem ev_C (e : Env) (c : F) : (C c).ev e = c * e.one := by simp [LinT.ev, C, Wire.ev]
@[simp] theorem ev_sc (e : Env) (c : F) (l : LinT) : (sc c l).ev e = c * l.ev e := by
  induction l with
  | nil => simp [LinT.ev, sc]
  | cons t l ih => simp only [LinT.ev, sc, List.map_cons, List.sum_cons] at ih ⊢; rw [ih]; ring

/-- A template row. -/
structure RowT where
  a : LinT
  b : LinT
  c : LinT
  deriving DecidableEq, Hashable

def RowT.Holds (e : Env) (r : RowT) : Prop := r.a.ev e * r.b.ev e = r.c.ev e

/-! ## Gates and templates -/

/-- A gate: a product (one new local, one row), an inverse (two locals, three rows), a product
plus a linear form (one local `a·b + c`, one row; S-E5), or **padding** (`r` empty rows and `l`
unused locals: the alignment of a block inside a template; S-E10). -/
inductive Gate where
  | mul (a b : LinT)
  | inv (a : LinT)
  | mulAdd (a b c : LinT)
  | pad (r l : ℕ)

/-- The locals a gate allocates. -/
def Gate.nloc : Gate → ℕ
  | .mul .. => 1
  | .inv _ => 2
  | .mulAdd .. => 1
  | .pad _ l => l

/-- A gate's rows, its first local at `k`. -/
def Gate.rows (k : ℕ) : Gate → List RowT
  | .mul a b => [⟨a, b, L k⟩]
  | .inv a => [⟨a, L k, L (k + 1)⟩, ⟨a, C 1 ++ sc (-1) (L (k + 1)), []⟩,
      ⟨L k, C 1 ++ sc (-1) (L (k + 1)), []⟩]
  | .mulAdd a b c => [⟨a, b, L k ++ sc (-1) c⟩]
  | .pad r _ => List.replicate r ⟨[], [], []⟩

/-- A gate's equation, its first local at `k`. -/
def Gate.Eqn (e : Env) (k : ℕ) : Gate → Prop
  | .mul a b => e.loc k = a.ev e * b.ev e
  | .inv a => e.loc k = (a.ev e)⁻¹
  | .mulAdd a b c => e.loc k = a.ev e * b.ev e + c.ev e
  | .pad .. => True

/-- The gates with their first locals, from `k`. -/
def gatesAt : List Gate → ℕ → List (ℕ × Gate)
  | [], _ => []
  | g :: gs, k => (k, g) :: gatesAt gs (k + g.nloc)

/-- The locals of a gate list. -/
def nlocs (gs : List Gate) : ℕ := (gs.map Gate.nloc).sum

theorem gatesAt_append (g₁ g₂ : List Gate) (k : ℕ) :
    gatesAt (g₁ ++ g₂) k = gatesAt g₁ k ++ gatesAt g₂ (k + nlocs g₁) := by
  induction g₁ generalizing k with
  | nil => simp [gatesAt, nlocs]
  | cons g gs ih => simp [gatesAt, ih, nlocs, Nat.add_assoc]

/-- The gate equations of a gate list from local `k`. -/
def Eqns (e : Env) (gs : List Gate) (k : ℕ) : Prop := ∀ p ∈ gatesAt gs k, p.2.Eqn e p.1

theorem Eqns.append {e : Env} {g₁ g₂ : List Gate} {k : ℕ} :
    Eqns e (g₁ ++ g₂) k ↔ Eqns e g₁ k ∧ Eqns e g₂ (k + nlocs g₁) := by
  simp only [Eqns, gatesAt_append, List.mem_append]
  exact ⟨fun h => ⟨fun p hp => h p (.inl hp), fun p hp => h p (.inr hp)⟩,
    fun h p hp => hp.elim (h.1 p) (h.2 p)⟩

theorem Eqns.cons {e : Env} {g : Gate} {gs : List Gate} {k : ℕ} :
    Eqns e (g :: gs) k ↔ g.Eqn e k ∧ Eqns e gs (k + g.nloc) := by
  simp [Eqns, gatesAt]

@[simp] theorem Eqns.nil {e : Env} {k : ℕ} : Eqns e [] k := by simp [Eqns, gatesAt]

/-- **A template**: gates (locals from `0`) and output forms (one per `F` component). -/
structure Tpl where
  gates : List Gate
  outs : List LinT

/-- The template's rows, in gate order. -/
def Tpl.rows (T : Tpl) : List RowT := (gatesAt T.gates 0).flatMap fun p => p.2.rows p.1

/-- The inverse rows force the inverse (`FRVIRCompile.inv_rows`'s argument). -/
theorem inv_of_rows {x i s : F} (h1 : x * i = s) (h2 : x * (1 - s) = 0) (h3 : i * (1 - s) = 0) :
    i = x⁻¹ := by
  by_cases hx : x = 0
  · subst hx; simp at h1; subst h1; simpa using h3
  · have : s = 1 := by have := (mul_eq_zero.1 h2).resolve_left hx; linear_combination -this
    subst this; exact (inv_eq_of_mul_eq_one_right h1).symm

theorem Gate.eqn_of_rows {e : Env} (h1 : e.one = 1) (k : ℕ) (g : Gate)
    (h : ∀ r ∈ g.rows k, r.Holds e) : g.Eqn e k := by
  cases g with
  | mul a b => simpa [Gate.rows, Gate.Eqn, RowT.Holds, eq_comm] using h
  | inv a =>
    simp only [Gate.rows, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq,
      RowT.Holds, ev_append, ev_L, ev_C, ev_sc, ev_nil, h1] at h
    exact inv_of_rows h.1 (by linear_combination h.2.1) (by linear_combination h.2.2)
  | mulAdd a b c =>
    simp only [Gate.rows, List.mem_singleton, forall_eq, RowT.Holds, ev_append, ev_L, ev_sc] at h
    simp only [Gate.Eqn]; linear_combination -h
  | pad => trivial

/-- **The rows give the gate equations** (generic, once for every template). -/
theorem Tpl.eqns_of_rows {e : Env} (h1 : e.one = 1) (T : Tpl) (h : ∀ r ∈ T.rows, r.Holds e) :
    Eqns e T.gates 0 := fun p hp =>
  Gate.eqn_of_rows h1 p.1 p.2 fun r hr => h r (List.mem_flatMap.2 ⟨p, hp, hr⟩)

/-- One step of `maxLoc`. -/
def mlStep (m : ℕ) (t : Wire × F) : ℕ := match t.1 with | .loc k => max m k | _ => m

/-- A form's largest local. -/
def LinT.maxLoc (l : LinT) : ℕ := l.foldl mlStep 0

/-- A template's largest local referenced by a row. -/
def Tpl.maxLoc (T : Tpl) : ℕ :=
  (T.rows.map fun r => max r.a.maxLoc (max r.b.maxLoc r.c.maxLoc)).foldl max 0

/-- **Cell bits**: an instance's locals fit in `2^cbits` cells. -/
def Tpl.cbits (T : Tpl) : ℕ := Nat.size (max T.maxLoc (nlocs T.gates - 1))

/-- **Row bits**: an instance's rows fit in `2^rbits` rows. -/
def Tpl.rbits (T : Tpl) : ℕ := Nat.size (T.rows.length - 1)

/-! ## Instances -/

/-- An instantiated form: `one ↦ one`, input `i ↦ ins[i]`, local `k ↦ cb + k`. -/
def instLin (one : Lin) (ins : List Lin) (cb : ℕ) (l : LinT) : Lin :=
  l.flatMap fun t => match t.1 with
    | .one => one.smul t.2
    | .inp i => (ins.getD i []).smul t.2
    | .loc k => [(cb + k, t.2)]

/-- An instantiated row. -/
def instRow (one : Lin) (ins : List Lin) (cb : ℕ) (r : RowT) : Row :=
  ⟨instLin one ins cb r.a, instLin one ins cb r.b, instLin one ins cb r.c⟩

/-- `instLin` with the inputs in an array (constant-time lookups; S-E11: the walk has `2^15`). -/
def instLinA (one : Lin) (ins : Array Lin) (cb : ℕ) (l : LinT) : Lin :=
  l.flatMap fun t => match t.1 with
    | .one => one.smul t.2
    | .inp i => (ins.getD i []).smul t.2
    | .loc k => [(cb + k, t.2)]

def instRowA (one : Lin) (ins : Array Lin) (cb : ℕ) (r : RowT) : Row :=
  ⟨instLinA one ins cb r.a, instLinA one ins cb r.b, instLinA one ins cb r.c⟩

theorem instRowA_eq (one : Lin) (ins : List Lin) (cb : ℕ) (r : RowT) :
    instRowA one ins.toArray cb r = instRow one ins cb r := by
  have : ∀ l, instLinA one ins.toArray cb l = instLin one ins cb l := fun l => by
    simp only [instLinA, instLin, Array.getD_eq_getD_getElem?, List.getElem?_toArray,
      List.getD_eq_getElem?_getD]
  simp only [instRowA, instRow, this]

/-- The wires pulled back along an instance. -/
def envOf (w : Asg) (one : Lin) (ins : List Lin) (cb : ℕ) : Env :=
  ⟨one.ev w, fun i => (ins.getD i []).ev w, fun k => w (cb + k)⟩

theorem instLin_ev (w : Asg) (one : Lin) (ins : List Lin) (cb : ℕ) (l : LinT) :
    (instLin one ins cb l).ev w = l.ev (envOf w one ins cb) := by
  induction l with
  | nil => rfl
  | cons t l ih =>
    obtain ⟨wr, c⟩ := t
    simp only [instLin, List.flatMap_cons, Lin.ev_append] at ih ⊢
    rw [ih]
    cases wr <;> simp [LinT.ev, Wire.ev, envOf, mul_comm]

theorem instRow_holds {w : Asg} {one : Lin} {ins : List Lin} {cb : ℕ} {r : RowT} :
    (instRow one ins cb r).Holds w ↔ r.Holds (envOf w one ins cb) := by
  simp only [Row.Holds, RowT.Holds, instRow, instLin_ev]

/-- **An instance's rows give the template's gate equations at the pulled-back wires.** -/
theorem inst_eqns {w : Asg} {one : Lin} (h1 : one.ev w = 1) (ins : List Lin) (cb : ℕ) (T : Tpl)
    (h : ∀ r ∈ T.rows, (instRow one ins cb r).Holds w) : Eqns (envOf w one ins cb) T.gates 0 :=
  T.eqns_of_rows h1 fun r hr => instRow_holds.1 (h r hr)

/-! ## Keys, contexts, auxiliary imports -/

/-- **The template keys**: a templated op and its operand shape (A.11's table). -/
inductive TKey where
  | eqPt (n m : ℕ)
  | shiftEq (n m : ℕ)
  | phiRS (n : ℕ)
  | eqTableK (v : ℕ)
  | dotKF (n : ℕ)
  | targetS (n : ℕ)
  | eqZ
  | rowW (n : ℕ)
  | lagrangeS (n m : ℕ)
  | slotW (s n m : ℕ)
  | maskRows (n m : ℕ)
  | zero
  | tensorW (n : ℕ)
  | rsWeight (n : ℕ) (ps : List ℕ) (m : ℕ)
  | kindInd (n : ℕ)
  | shiftMask (n m : ℕ)
  | walkAB (n m : ℕ)
  /-- Revision 4.1's segment `shiftMask` (`τ ‖ L`, `r`; S-E12e). -/
  | shiftSeg (n m : ℕ)
  /-- Revision 4.1's node `shiftMask` over `chainLk4`, kind-muxed: per selector index the kind's
  `(nb, chLen₀, chLen₁)` (S-E12e). -/
  | maskN (n m : ℕ) (ks : List (ℕ × ℕ × ℕ))
  deriving DecidableEq, Inhabited

/-- **The template context**: each key's template and each instance's cell base. -/
structure TCtx where
  tpl : TKey → Tpl
  cb : TKey → ℕ → ℕ

/-- The rows of a recorded instance `(key, instance, input forms)`. -/
def instRows (tc : TCtx) (one : Lin) (t : TKey × ℕ × List Lin) : List Row :=
  (tc.tpl t.1).rows.map (instRow one t.2.2 (tc.cb t.1 t.2.1))

/-- **An auxiliary import** (A.11's irregular entries): cells whose values are read off a register,
the trace cells of a byte string's `F` elements or the L bits of a natural. -/
inductive AuxK where
  | felems (n : ℕ)
  | bits (n : ℕ)

/-- The values an auxiliary import's cells hold. -/
def AuxK.val : AuxK → Val → List F
  | .felems n, v => (List.range n).map fun b => (FR.felems v.toB).getD b 0
  | .bits n, v => (List.range n).map fun i => if v.toN.testBit i then 1 else 0

end Tpl
end FR
