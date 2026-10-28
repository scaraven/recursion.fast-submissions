-- New for `flock-recursive` (BLUEPRINT §4.3, §7, stage S-E2; A.7, A.8).
import FRVIRTplCore

/-!
# Compiling the verifier IR to M rows: `compile`, `compile_sound`

BLUEPRINT §4.3 (the node circuit's region M), A.8 (row costs), §9 (FR-R3′).

The node's region M holds `F` elements; its R1CS rows read `⟨a, w⟩ · ⟨b, w⟩ = ⟨c, w⟩` over linear
forms `Lin` of M's cells `w : ℕ → F` (E2's relation, A.9 `finE`). `compile` walks a `VProg`'s op
list once and gives every register a **slot**: either untracked (`none`), or a static type `Ty`
and one linear form per `F` component of the value (`encV`: `F` one, `K` and digests two, arrays
their elements). The ops are classified:

* **arithmetic** (rows emitted here, A.8's costs): `const`, `mulF` (1), `addF` (0), `mulK` (3,
  Karatsuba), `addK` (0), `mulKF` (2), `invF` (3), `packF`, `packK`, `getF`, `getK`, `eqTable`
  (`2^v − 1`), `keep` and `selectHalf` (one per component, a select by a gate or a bit),
  `splitDigest` (0), `assertEq`, `assertZero` (one per component, gated), `assertOneHot` (3
  products + 1 linear), `assertBit`, `accept`;
* **imports**: ops whose value the circuit takes from elsewhere (the trace cells, the
  irregular entries, L bits, the replay templates of `FRVIREval`, and the cell-reading ops `eqPt`,
  `rowW`, `shiftEq`, `linkW` (revision 3.6) whose cells `final` fixes): fresh typed cells, recorded in
  `imp`; `compile_sound` takes their values as a hypothesis;
* **untracked**: byte strings and naturals (`piField`, `mkAbsorb`, `idx`, `shrN`) and the ops not
  yet arithmetised (`packFK`, `eqTableK`, `kindInd`, `maskRows`, and any op S-0 adds); an
  assertion over an untracked operand is **foreign** (recorded in `fors` with the register count
  at that point; its flag is a hypothesis).

Kind-dependent data (`KC`) are selector-linear: a constant `c` is `Σ_κ c_κ · sel_κ` and an
activity `act` is the gate `Σ_{κ active} sel_κ`, for selector forms `Params.sel`. A fixed kind uses
the constants `sel_κ' = [κ' = κ]·one`; the mux uses three cells (`FRVIRMux`). `compile_sound` is
proved once for any selector forms whose values are one-hot at the run's kind (`SelOk`).

**`compile_sound`**: if `exec` runs the ops to state `s`, every emitted row holds, every import's
cells hold its value and every foreign flag holds, then `s.ok = true` and every tracked register's
cells hold its value.
-/

namespace FR
namespace Circ
open RecursionFast

/-! ## Values as cells -/

/-- The static type of a tracked register. -/
inductive Ty where
  | f | k | bit | d | af (n : ℕ) | ak (n : ℕ)
  deriving DecidableEq

/-- The number of `F` components. -/
def Ty.len : Ty → ℕ
  | .f => 1 | .k => 2 | .bit => 1 | .d => 2 | .af n => n | .ak n => 2 * n

/-- The type of a value (`none`: bytes, naturals, digest arrays). -/
def tyOf : Val → Option Ty
  | .f _ => some .f | .k _ => some .k | .bit _ => some .bit | .d _ => some .d
  | .af x => some (.af x.size) | .ak x => some (.ak x.size) | _ => none

/-- A digest's two `F` halves (as `splitDigest`). -/
def dlo (x : Digest) : F := F.ofBytes (Vector.ofFn fun i : Fin 16 => x[i.1])
def dhi (x : Digest) : F := F.ofBytes (Vector.ofFn fun i : Fin 16 => x[16 + i.1])

/-- A bit as `0`/`1`. -/
def bitF (b : Bool) : F := if b then 1 else 0

/-- A `K` element's two coordinates. -/
def encK (x : K) : List F := [x.f₀, x.f₁]

/-- **The cell encoding of a value** (A.7: an `F` per cell). -/
def encV : Val → List F
  | .f x => [x] | .k x => encK x | .bit b => [bitF b] | .d x => [dlo x, dhi x]
  | .af x => x.toList | .ak x => x.toList.flatMap encK | _ => []

/-- A register's slot: untracked, or its type and one linear form per component. -/
abbrev Slot := Option (Ty × List Lin)

/-- **The slot represents the value at `w`.** -/
def RepS (w : Asg) : Slot → Val → Prop
  | none, _ => True
  | some (t, ls), v => tyOf v = some t ∧ ls.map (Lin.ev w) = encV v

/-- Component `j` of a slot. -/
def comp : Slot → ℕ → Lin
  | some (_, ls), j => ls.getD j []
  | none, _ => []

/-- A slot's type. -/
def Slot.ty? : Slot → Option Ty
  | some (t, _) => some t
  | none => none

/-- The `F` operand (`Val.toF`: `0` off type). -/
def asF (s : Slot) : Lin := if s.ty? = some .f then comp s 0 else []
/-- The `K` operand. -/
def asK (s : Slot) : Lin × Lin := if s.ty? = some .k then (comp s 0, comp s 1) else ([], [])
/-- The bit operand. -/
def asBit (s : Slot) : Lin := if s.ty? = some .bit then comp s 0 else []
/-- The `AF` operand's elements. -/
def asAF : Slot → List Lin
  | some (.af _, ls) => ls
  | _ => []
/-- The `AK` operand's coordinates. -/
def asAK : Slot → List Lin
  | some (.ak _, ls) => ls
  | _ => []

/-! ## Kind-dependent data -/

/-- The selector forms: a cell pinned to `1` and one form per kind. -/
structure Params where
  one : Lin
  sel : Kind → Lin

/-- The three kinds. -/
def kinds : List Kind := [.L32, .P30, .N30]

/-- `Σ_κ c_κ · sel_κ`: a kind-dependent constant (no row). -/
def Params.kc (P : Params) (c : Kind → F) : Lin := kinds.flatMap fun κ => (P.sel κ).smul (c κ)

/-- The activity gate `Σ_{κ active} sel_κ`. -/
def Params.gate (P : Params) (act : KC Bool) : Lin := P.kc fun κ => bitF (act κ)

/-- **The selector forms are one-hot at `κ`** (and `one` is `1`). -/
def SelOk (w : Asg) (P : Params) (κ : Kind) : Prop :=
  P.one.ev w = 1 ∧ ∀ κ', (P.sel κ').ev w = if κ' = κ then 1 else 0

/-- The constant selector forms of a fixed kind. -/
def fixedP (one : Lin) (κ : Kind) : Params := ⟨one, fun κ' => if κ' = κ then one else []⟩

/-! ## The compiler -/

/-- What one op contributes: its result slots, rows, fresh cells, import and foreign flags. -/
structure Out where
  slots : List Slot
  rows : List Row := []
  fresh : ℕ := 0
  imp : Bool := false
  foreign : Bool := false
  /-- A template instance (S-E3): its key and input forms; its rows are `Tpl.instRows`. -/
  tin : Option (Tpl.TKey × List Lin) := none
  /-- Auxiliary imports (S-E3): cells, the register they are read off, the reading. -/
  aux : List (List Lin × ℕ × Tpl.AuxK) := []

/-- The compiler's state. -/
structure CS where
  /-- The next free cell. -/
  next : ℕ
  /-- The slot of every register so far. -/
  slots : Array Slot
  /-- The rows, last first (`CS.rowList` is in program order; prepending keeps `compile` linear). -/
  rows : List Row
  /-- The import registers. -/
  imp : List ℕ
  /-- The foreign assertions, with the register count at that point. -/
  fors : List (Op × ℕ)
  /-- The template instances, last first: key, instance number, input forms (S-E3). -/
  tins : List (Tpl.TKey × ℕ × List Lin) := []
  /-- The auxiliary imports, with the register count at that point (S-E3). -/
  aux : List ((List Lin × ℕ × Tpl.AuxK) × ℕ) := []

/-- The rows in program order (row `i` is the `i`-th row emitted). -/
def CS.rowList (cs : CS) : List Row := cs.rows.reverse

/-- The slot of register `i`. -/
def CS.slot (cs : CS) (i : ℕ) : Slot := cs.slots.getD i none

/-- Fresh cell `j` of the current op. -/
def CS.cell (cs : CS) (j : ℕ) : Lin := Lin.cell (cs.next + j)

/-- The instances of template `k` so far (the next instance's number). -/
def CS.tcount (cs : CS) (k : Tpl.TKey) : ℕ := cs.tins.countP (·.1 == k)

/-- Append an op's contribution. -/
def CS.add (cs : CS) (op : Op) (o : Out) : CS :=
  -- every other field first, the slot array last, so that its append is in place
  let n := cs.slots.size
  let tins := match o.tin with
    | some t => (t.1, cs.tcount t.1, t.2) :: cs.tins
    | none => cs.tins
  let aux := o.aux.map (·, n) ++ cs.aux
  let imp := if o.imp then List.range' n o.slots.length ++ cs.imp else cs.imp
  let fors := if o.foreign then (op, n) :: cs.fors else cs.fors
  let rows := o.rows.reverseAux cs.rows
  let next := cs.next + o.fresh
  ⟨next, cs.slots ++ o.slots.toArray, rows, imp, fors, tins, aux⟩

/-- `n` untracked results. -/
def skip (n : ℕ) : Out := { slots := List.replicate n none }

/-- Imported results of the given types, on consecutive fresh cells. -/
def impSlots (cs : CS) : ℕ → List Ty → List Slot
  | _, [] => []
  | o, t :: ts => some (t, (List.range t.len).map fun j => cs.cell (o + j)) :: impSlots cs (o + t.len) ts

/-- An import. -/
def imports (cs : CS) (ts : List Ty) : Out :=
  { slots := impSlots cs 0 ts, fresh := (ts.map Ty.len).sum, imp := true }

/-- `x + g·(y − x)` per component of type `t`, on fresh cells `u_j = g·(y_j − x_j)`. -/
def muxOut (cs : CS) (g : Lin) (t : Ty) (sx sy : Slot) : Out where
  slots := [some (t, (List.range t.len).map fun j => comp sx j ++ cs.cell j)]
  rows := (List.range t.len).map fun j => ⟨g, (comp sy j).sub (comp sx j), cs.cell j⟩
  fresh := t.len

/-- Types whose `Val.eqv` is componentwise equality. -/
def Ty.eqOk : Ty → Bool
  | .f | .k | .bit | .d => true
  | _ => false

/-- The table `eq(x, ·)` doubling step on `t` (fresh cells `u_i = t_i · x` from offset `o`): the
low half `t_i − u_i`, the high half `u_i`, the rows. -/
def eqStep (cs : CS) (x : Lin) : List Lin → ℕ → List Lin × List Lin × List Row
  | [], _ => ([], [], [])
  | a :: t, o =>
    let r := eqStep cs x t (o + 1)
    (a.sub (cs.cell o) :: r.1, cs.cell o :: r.2.1, ⟨a, x, cs.cell o⟩ :: r.2.2)

/-- `eqTab` over the coordinates `xs` from the table `t` (fresh cells from `o`). -/
def eqRows (cs : CS) : List Lin → List Lin → ℕ → List Lin × List Row × ℕ
  | [], t, o => (t, [], o)
  | x :: xs, t, o =>
    let s := eqStep cs x t o
    let r := eqRows cs xs (s.1 ++ s.2.1) (o + t.length)
    (r.1, s.2.2 ++ r.2.1, r.2.2)

/-- Both operands tracked. -/
def both (a b : Slot) : Bool := a.isSome && b.isSome

/-- **One op's contribution.** -/
def opOut (P : Params) (cs : CS) : Op → Out
  | .input _ => imports cs [.d]
  | .const c =>
    match tyOf (c .L32) with
    | some t =>
      if tyOf (c .P30) = some t ∧ tyOf (c .N30) = some t then
        { slots := [some (t, (List.range t.len).map fun j => P.kc fun κ => (encV (c κ)).getD j 0)] }
      else skip 1
    | none => skip 1
  | .piElem .. => imports cs [.f]
  | .piElemK .. => imports cs [.k]
  | .piDigest .. | .piDigestAt .. => imports cs [.d]
  | .askSeed _ | .askAbsorb .. | .askSqueeze _ | .askNode .. | .askCol .. => imports cs [.d]
  | .chF .. => imports cs [.f]
  | .chK _ => imports cs [.k]
  | .bitOf .. => imports cs [.bit]
  | .mulF a b =>
    if both (cs.slot a) (cs.slot b) then
      { slots := [some (.f, [cs.cell 0])], rows := [⟨asF (cs.slot a), asF (cs.slot b), cs.cell 0⟩],
        fresh := 1 }
    else skip 1
  | .addF a b =>
    if both (cs.slot a) (cs.slot b) then
      { slots := [some (.f, [asF (cs.slot a) ++ asF (cs.slot b)])] }
    else skip 1
  | .mulK a b =>
    if both (cs.slot a) (cs.slot b) then
      let x := asK (cs.slot a); let y := asK (cs.slot b)
      { slots := [some (.k, [cs.cell 0 ++ (cs.cell 1).smul F.alpha, cs.cell 2 ++ cs.cell 0])]
        rows := [⟨x.1, y.1, cs.cell 0⟩, ⟨x.2, y.2, cs.cell 1⟩, ⟨x.1 ++ x.2, y.1 ++ y.2, cs.cell 2⟩]
        fresh := 3 }
    else skip 1
  | .addK a b =>
    if both (cs.slot a) (cs.slot b) then
      let x := asK (cs.slot a); let y := asK (cs.slot b)
      { slots := [some (.k, [x.1 ++ y.1, x.2 ++ y.2])] }
    else skip 1
  | .mulKF a b =>
    if both (cs.slot a) (cs.slot b) then
      let x := asK (cs.slot a); let c := asF (cs.slot b)
      { slots := [some (.k, [cs.cell 0, cs.cell 1])],
        rows := [⟨c, x.1, cs.cell 0⟩, ⟨c, x.2, cs.cell 1⟩], fresh := 2 }
    else skip 1
  | .invF a =>
    if (cs.slot a).isSome then
      let x := asF (cs.slot a); let s' := P.one.sub (cs.cell 1)
      { slots := [some (.f, [cs.cell 0])],
        rows := [⟨x, cs.cell 0, cs.cell 1⟩, ⟨x, s', []⟩, ⟨cs.cell 0, s', []⟩], fresh := 2 }
    else skip 1
  | .packF xs =>
    if xs.all fun x => (cs.slot x).isSome then
      { slots := [some (.af xs.length, xs.map fun x => asF (cs.slot x))] }
    else skip 1
  | .packK xs =>
    if xs.all fun x => (cs.slot x).isSome then
      { slots := [some (.ak xs.length, xs.flatMap fun x => [(asK (cs.slot x)).1, (asK (cs.slot x)).2])] }
    else skip 1
  | .getF a i =>
    if (cs.slot a).isSome then { slots := [some (.f, [(asAF (cs.slot a)).getD i []])] } else skip 1
  | .getK a i =>
    if (cs.slot a).isSome then
      { slots := [some (.k, [(asAK (cs.slot a)).getD (2 * i) [], (asAK (cs.slot a)).getD (2 * i + 1) []])] }
    else skip 1
  | .eqTable r =>
    if (cs.slot r).isSome then
      let e := eqRows cs (asAF (cs.slot r)) [P.one] 0
      { slots := [some (.af e.1.length, e.1)], rows := e.2.1, fresh := e.2.2 }
    else skip 1
  | .phiRS .. | .walkA .. | .walkB ..
  | .shiftTarget .. | .slotW .. | .kindFoldWeight .. => imports cs [.f]
  | .eqZ .. => imports cs [.af 128]
  | .rsWeight .. => imports cs [.k]
  | .evalMK .. => imports cs [.k, .k, .k]
  | .lagrangeS .. => imports cs [.f, .f]
  | .targetS .. => imports cs [.af 64]
  | .tensorW .. | .dotKF .. => imports cs [.k]
  | .evalM .. | .evalL .. => imports cs [.f, .f, .f]
  | .hashStmt _ => imports cs [.d]
  | .eqPt .. | .shiftEq .. | .linkW .. => imports cs [.f]
  | .rowW .. => imports cs [.af (2 ^ 14)]
  | .kindSel =>
    { slots := kinds.map fun κ => some (.bit, [P.sel κ]), imp := true }
  | .splitDigest d =>
    if (cs.slot d).ty? = some .d then
      { slots := [some (.f, [comp (cs.slot d) 0]), some (.f, [comp (cs.slot d) 1])] }
    else skip 2
  | .keep act n o =>
    match (cs.slot n).ty?, (cs.slot o).ty? with
    | some t, some t' =>
      if t = t' then
        if act .L32 = act .P30 ∧ act .P30 = act .N30 then
          { slots := [if act .L32 then cs.slot n else cs.slot o] }
        else muxOut cs (P.gate act) t (cs.slot o) (cs.slot n)
      else skip 1
    | _, _ => skip 1
  | .selectHalf b x y =>
    match (cs.slot b).ty?, (cs.slot x).ty?, (cs.slot y).ty? with
    | some _, some t, some t' =>
      if t = t' then muxOut cs (asBit (cs.slot b)) t (cs.slot x) (cs.slot y) else skip 1
    | _, _, _ => skip 1
  | .assertEq a b act =>
    match (cs.slot a).ty?, (cs.slot b).ty? with
    | some t, some t' =>
      if t = t' ∧ t.eqOk then
        { slots := [], rows := (List.range t.len).map fun j =>
            ⟨P.gate act, (comp (cs.slot a) j).sub (comp (cs.slot b) j), []⟩ }
      else { slots := [], rows := [⟨P.gate act, P.one, []⟩] }
    | _, _ => { slots := [], foreign := true }
  | .assertZero a act =>
    match (cs.slot a).ty? with
    | some t =>
      { slots := [], rows := (List.range t.len).map fun j => ⟨P.gate act, comp (cs.slot a) j, []⟩ }
    | none => { slots := [], foreign := true }
  | .assertOneHot a b c =>
    if (cs.slot a).isSome && (cs.slot b).isSome && (cs.slot c).isSome then
      let x := asBit (cs.slot a); let y := asBit (cs.slot b); let z := asBit (cs.slot c)
      { slots := [], rows := [⟨x, y, []⟩, ⟨x, z, []⟩, ⟨y, z, []⟩, ⟨P.one, x ++ y ++ z, P.one⟩] }
    else { slots := [], foreign := true }
  | .assertBit .. | .accept => { slots := [] }
  | .piField .. | .mkAbsorb _ | .idx .. | .shrN .. => skip 1
  | _ => { slots := [none], foreign := true }

/-- **A compiler extension** (S-E3): ops it handles (templates) and their contribution. -/
abbrev Ext := Params → CS → Op → Option Out

/-- No extension. -/
def noExt : Ext := fun _ _ _ => none

/-- One op's contribution under an extension. -/
def stepOut (X : Ext) (P : Params) (cs : CS) (op : Op) : Out := (X P cs op).getD (opOut P cs op)

/-- The compiler from a state. -/
def compileFromX (X : Ext) (P : Params) (cs : CS) (ops : List Op) : CS :=
  ops.foldl (fun cs op => cs.add op (stepOut X P cs op)) cs

/-- The compiler without templates. -/
abbrev compileFrom (P : Params) (cs : CS) (ops : List Op) : CS := compileFromX noExt P cs ops

/-- The initial state: fresh cells from `base`. -/
def CS.init (base : ℕ) : CS := ⟨base, #[], [], [], [], [], []⟩

/-- **`compile`**: the rows, slots, imports and foreign assertions of an op list. -/
def compile (P : Params) (base : ℕ) (ops : List Op) : CS := compileFrom P (CS.init base) ops

/-- **`compileX`**: `compile` with an extension (`compileT` is `compileX` with the templates). -/
def compileX (X : Ext) (P : Params) (base : ℕ) (ops : List Op) : CS :=
  compileFromX X P (CS.init base) ops

/-- The template instances' rows. -/
def CS.tplRows (tc : Tpl.TCtx) (one : Lin) (cs : CS) : List Row := cs.tins.flatMap (Tpl.instRows tc one)

/-- The flag an op contributes on a register file. -/
def flagOf (impl : OpImpl) (κ : Kind) (inp : Input) (regs : Array Val) (op : Op) : Bool :=
  match evalOp impl κ inp regs op with
  | .vals _ ok => ok
  | .ask _ => true

/-! ## Proof helpers: encodings -/

theorem comp_ev {w : Asg} {t : Ty} {ls : List Lin} {v : Val} (h : RepS w (some (t, ls)) v)
    (j : ℕ) : (comp (some (t, ls)) j).ev w = (encV v).getD j 0 := by
  rw [← h.2]; simp only [comp, List.getD_eq_getElem?_getD, List.getElem?_map]
  cases ls[j]? <;> rfl

theorem encV_length {v : Val} {t : Ty} (h : tyOf v = some t) : (encV v).length = t.len := by
  cases v <;> simp [tyOf] at h <;> subst h <;> simp [encV, Ty.len, encK, List.length_flatMap]
  ring

private theorem K_zero_f₀ : (0 : K).f₀ = 0 := rfl
private theorem K_zero_f₁ : (0 : K).f₁ = 0 := rfl

theorem asF_ev {w : Asg} {t : Ty} {ls : List Lin} {v : Val} (h : RepS w (some (t, ls)) v) :
    (asF (some (t, ls))).ev w = v.toF := by
  have h1 := h.1; have h2 := comp_ev h 0
  cases v <;> simp only [tyOf, reduceCtorEq, Option.some.injEq] at h1 <;> subst h1 <;>
    simp_all [asF, Slot.ty?, Val.toF, encV, encK]

theorem asK_ev {w : Asg} {t : Ty} {ls : List Lin} {v : Val} (h : RepS w (some (t, ls)) v) :
    (asK (some (t, ls))).1.ev w = v.toK.f₀ ∧ (asK (some (t, ls))).2.ev w = v.toK.f₁ := by
  have h1 := h.1; have h2 := comp_ev h 0; have h3 := comp_ev h 1
  cases v <;> simp only [tyOf, reduceCtorEq, Option.some.injEq] at h1 <;> subst h1 <;>
    simp_all [asK, Slot.ty?, Val.toK, encV, encK, K_zero_f₀, K_zero_f₁]

theorem asBit_ev {w : Asg} {t : Ty} {ls : List Lin} {v : Val} (h : RepS w (some (t, ls)) v) :
    (asBit (some (t, ls))).ev w = bitF v.toBit := by
  have h1 := h.1; have h2 := comp_ev h 0
  cases v <;> simp only [tyOf, reduceCtorEq, Option.some.injEq] at h1 <;> subst h1 <;>
    simp_all [asBit, Slot.ty?, Val.toBit, encV, encK, bitF] <;> rfl

theorem asAF_ev {w : Asg} {t : Ty} {ls : List Lin} {v : Val} (h : RepS w (some (t, ls)) v) :
    (asAF (some (t, ls))).map (Lin.ev w) = v.toAF.toList := by
  have h1 := h.1; have h2 := h.2
  cases v <;> simp only [tyOf, reduceCtorEq, Option.some.injEq] at h1 <;> subst h1 <;>
    simp_all [asAF, Val.toAF, encV]

theorem asAK_ev {w : Asg} {t : Ty} {ls : List Lin} {v : Val} (h : RepS w (some (t, ls)) v) :
    (asAK (some (t, ls))).map (Lin.ev w) = v.toAK.toList.flatMap encK := by
  have h1 := h.1; have h2 := h.2
  cases v <;> simp only [tyOf, reduceCtorEq, Option.some.injEq] at h1 <;> subst h1 <;>
    simp_all [asAK, Val.toAK, encV]

theorem getD_ev {w : Asg} {ls : List Lin} {xs : List F} (h : ls.map (Lin.ev w) = xs) (j : ℕ) :
    (ls.getD j []).ev w = xs.getD j 0 := by
  rw [← h]; simp only [List.getD_eq_getElem?_getD, List.getElem?_map]; cases ls[j]? <;> rfl

theorem flatMap_encK_getD (l : List K) (i : ℕ) :
    (l.flatMap encK).getD (2 * i) 0 = (l.getD i 0).f₀ ∧
    (l.flatMap encK).getD (2 * i + 1) 0 = (l.getD i 0).f₁ := by
  induction l generalizing i with
  | nil => simp [K_zero_f₀, K_zero_f₁]
  | cons a l ih =>
    cases i with
    | zero => simp [encK]
    | succ i =>
      have := ih i
      simp only [List.flatMap_cons, encK, List.cons_append, List.nil_append, List.getD_cons_succ,
        show 2 * (i + 1) = 2 * i + 1 + 1 by ring]
      exact ⟨this.1, this.2⟩

theorem kc_ev {w : Asg} {P : Params} {κ : Kind} (h : SelOk w P κ) (c : Kind → F) :
    (P.kc c).ev w = c κ := by
  cases κ <;> simp [Params.kc, kinds, h.2]

theorem gate_ev {w : Asg} {P : Params} {κ : Kind} (h : SelOk w P κ) (act : KC Bool) :
    (P.gate act).ev w = bitF (act κ) := kc_ev h _

/-- The fixed kind's selector forms are one-hot. -/
theorem fixedP_ok {w : Asg} {one : Lin} (h : one.ev w = 1) (κ : Kind) : SelOk w (fixedP one κ) κ :=
  ⟨h, fun κ' => by by_cases e : κ' = κ <;> simp [fixedP, e, h]⟩

theorem bitF_inj {a b : Bool} (h : bitF a = bitF b) : a = b := by
  cases a <;> cases b <;> simp_all [bitF]

theorem ofBytes_inj {u v : Vector UInt8 16} (h : F.ofBytes u = F.ofBytes v) : u = v := by
  simpa using congrArg F.toBytes h

theorem digest_ext {x y : Digest} (hl : dlo x = dlo y) (hh : dhi x = dhi y) : x = y := by
  have l := ofBytes_inj hl; have h := ofBytes_inj hh
  apply Vector.ext; intro i hi
  by_cases c : i < 16
  · simpa using congrArg (·[i]'c) l
  · have := congrArg (·[i - 16]'(by omega)) h
    simpa [show 16 + (i - 16) = i by omega] using this

theorem dlo_zero : dlo zeroD = 0 := by decide
theorem dhi_zero : dhi zeroD = 0 := by decide

/-- Componentwise equal encodings of one `eqOk` type are `eqv`. -/
theorem eqv_of_enc {va vb : Val} {t : Ty} (ha : tyOf va = some t) (hb : tyOf vb = some t)
    (ht : t.eqOk = true) (h : encV va = encV vb) : va.eqv vb = true := by
  rcases va with x | x | x | x | x | x | x | x | x <;>
    simp only [tyOf, Option.some.injEq, reduceCtorEq] at ha <;> subst ha <;>
    simp only [Ty.eqOk, Bool.false_eq_true] at ht <;>
    rcases vb with y | y | y | y | y | y | y | y | y <;>
    simp only [tyOf, Option.some.injEq, reduceCtorEq] at hb <;>
    simp only [encV, encK, List.cons.injEq, and_true] at h <;>
    simp only [Val.eqv, decide_eq_true_eq]
  · exact h
  · cases x; cases y; simp_all
  · exact digest_ext h.1 h.2
  · exact bitF_inj h

theorem K_eq_zero {y : K} (h0 : y.f₀ = 0) (h1 : y.f₁ = 0) : y = 0 := by
  cases y; simp_all; rfl

/-- An encoding of zeros is `isZero`. -/
theorem isZero_of_enc {v : Val} {t : Ty} (ht : tyOf v = some t) (h : ∀ x ∈ encV v, x = 0) :
    v.isZero = true := by
  rcases v with x | x | x | x | x | x | x | x | x <;> simp only [tyOf, reduceCtorEq] at ht <;>
    simp only [encV, encK, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp,
      forall_eq, Array.mem_toList_iff, List.mem_flatMap] at h <;>
    simp only [Val.isZero, decide_eq_true_eq, Bool.not_eq_true']
  · exact h
  · exact K_eq_zero h.1 h.2
  · exact digest_ext (h.1.trans dlo_zero.symm) (h.2.trans dhi_zero.symm)
  · cases x <;> simp_all [bitF]
  · simp only [Array.all_eq_true, decide_eq_true_eq]
    exact fun i hi => h _ (Array.getElem_mem hi)
  · simp only [Array.all_eq_true, decide_eq_true_eq]
    intro i hi
    have hm := Array.getElem_mem hi
    exact K_eq_zero (h _ ⟨x[i], hm, by simp⟩) (h _ ⟨x[i], hm, by simp⟩)

/-! ## Proof helpers: rows -/

theorem encV_ext {w : Asg} {t : Ty} {ls : List Lin} {v : Val} (h : RepS w (some (t, ls)) v)
    {xs : List F} (hl : xs.length = t.len) (hj : ∀ j < t.len, xs.getD j 0 = (comp (some (t, ls)) j).ev w) :
    xs = encV v := by
  apply List.ext_getElem (by rw [hl, encV_length h.1])
  intro j h1 h2
  rw [← List.getD_eq_getElem _ 0, ← List.getD_eq_getElem _ 0, hj j (hl ▸ h1), comp_ev h]

theorem muxOut_sound {w : Asg} {cs : CS} {g : Lin} {t : Ty} {lx ly : List Lin} {vx vy : Val}
    {c : Bool} (hx : RepS w (some (t, lx)) vx) (hy : RepS w (some (t, ly)) vy)
    (hg : g.ev w = bitF c)
    (hr : ∀ r ∈ (muxOut cs g t (some (t, lx)) (some (t, ly))).rows, r.Holds w) :
    List.Forall₂ (RepS w) (muxOut cs g t (some (t, lx)) (some (t, ly))).slots
      [if c then vy else vx] := by
  simp only [muxOut, List.forall₂_cons, List.Forall₂.nil, and_true]
  refine ⟨by cases c <;> simp [hx.1, hy.1], ?_⟩
  have key : ∀ j < t.len, (comp (some (t, lx)) j ++ cs.cell j).ev w =
      (comp (some (t, if c then ly else lx)) j).ev w := by
    intro j hj
    have := hr _ (List.mem_map.2 ⟨j, List.mem_range.2 hj, rfl⟩)
    simp only [Row.Holds, Lin.ev_sub, hg, Lin.ev_append] at this ⊢
    cases c <;> simp_all [bitF, CS.cell] <;> rw [← this] <;> ring
  have hc : RepS w (some (t, if c then ly else lx)) (if c then vy else vx) := by
    cases c <;> simpa
  refine encV_ext hc (by simp) fun j hj => ?_
  rw [← key j hj, ← getD_ev rfl j]; simp [hj]

/-- The number of results of an op. -/
def _root_.FR.Op.nOut : Op → ℕ
  | .evalM .. | .evalMK .. | .evalL .. | .kindSel => 3
  | .splitDigest _ | .lagrangeS .. => 2
  | .assertEq .. | .assertBit .. | .assertZero .. | .assertOneHot .. | .accept => 0
  | _ => 1

theorem eqStep_sound {w : Asg} {cs : CS} {x : Lin} {xv : F} (hx : x.ev w = xv) :
    ∀ (t : List Lin) (o : ℕ) (tv : List F), t.map (Lin.ev w) = tv →
    (∀ r ∈ (eqStep cs x t o).2.2, r.Holds w) →
    (eqStep cs x t o).1.map (Lin.ev w) = tv.map (· * (1 - xv)) ∧
    (eqStep cs x t o).2.1.map (Lin.ev w) = tv.map (· * xv)
  | [], o, tv, h, _ => by subst h; simp [eqStep]
  | a :: t, o, tv, h, hr => by
    subst h
    have ih := eqStep_sound (cs := cs) hx t (o + 1) _ rfl fun r hr' => hr r (List.mem_cons_of_mem _ hr')
    have h0 := hr ⟨a, x, cs.cell o⟩ (List.mem_cons_self ..)
    simp only [Row.Holds, hx, CS.cell, Lin.ev_cell] at h0
    simp only [eqStep, List.map_cons, Lin.ev_sub, CS.cell, Lin.ev_cell, ih.1, ih.2, ← h0]
    constructor <;> first | trivial | rfl | (congr 1; ring)

theorem eqRows_sound {w : Asg} {cs : CS} : ∀ (xs t : List Lin) (o : ℕ) (xv : List F) (tv : Array F),
    xs.map (Lin.ev w) = xv → t.map (Lin.ev w) = tv.toList →
    (∀ r ∈ (eqRows cs xs t o).2.1, r.Holds w) →
    (eqRows cs xs t o).1.map (Lin.ev w) =
      (xv.foldl (fun t x => t.map (· * (1 - x)) ++ t.map (· * x)) tv).toList
  | [], t, o, xv, tv, hx, ht, _ => by subst hx; simpa [eqRows] using ht
  | x :: xs, t, o, xv, tv, hx, ht, hr => by
    subst hx
    simp only [eqRows, List.mem_append, List.map_cons, List.foldl_cons] at hr ⊢
    have st := eqStep_sound rfl t o _ ht fun r h => hr r (Or.inl h)
    exact eqRows_sound xs _ _ (xs.map (Lin.ev w))
      (tv.map (· * (1 - x.ev w)) ++ tv.map (· * x.ev w)) rfl
      (by simp only [List.map_append, st.1, st.2, Array.toList_append, Array.toList_map])
      fun r h => hr r (Or.inr h)

theorem oneHot_sound {a b c : Bool} {one x y z : F} (h1 : one = 1) (hx : x = bitF a)
    (hy : y = bitF b) (hz : z = bitF c) (r1 : x * y = 0) (r2 : x * z = 0) (r3 : y * z = 0)
    (r4 : one * (x + y + z) = one) : ([a, b, c].count true == 1) = true := by
  subst h1 hx hy hz
  cases a <;> cases b <;> cases c <;> simp_all [bitF]

/-! ## Proof helpers: one op -/

section
variable {w : Asg} {cs : CS} {regs : Array Val}

theorem rep_of_some (hI : ∀ i, RepS w (cs.slot i) (rd regs i)) {a : ℕ} (h : (cs.slot a).isSome) :
    ∃ t ls, cs.slot a = some (t, ls) ∧ RepS w (some (t, ls)) (rd regs a) := by
  obtain ⟨⟨t, ls⟩, e⟩ := Option.isSome_iff_exists.1 h
  exact ⟨t, ls, e, e ▸ hI a⟩

theorem asF_slot (hI : ∀ i, RepS w (cs.slot i) (rd regs i)) {a : ℕ} (h : (cs.slot a).isSome) :
    (asF (cs.slot a)).ev w = (rd regs a).toF := by
  obtain ⟨t, ls, e, r⟩ := rep_of_some hI h; rw [e]; exact asF_ev r

theorem asK_slot (hI : ∀ i, RepS w (cs.slot i) (rd regs i)) {a : ℕ} (h : (cs.slot a).isSome) :
    (asK (cs.slot a)).1.ev w = (rd regs a).toK.f₀ ∧ (asK (cs.slot a)).2.ev w = (rd regs a).toK.f₁ := by
  obtain ⟨t, ls, e, r⟩ := rep_of_some hI h; rw [e]; exact asK_ev r

theorem asBit_slot (hI : ∀ i, RepS w (cs.slot i) (rd regs i)) {a : ℕ} (h : (cs.slot a).isSome) :
    (asBit (cs.slot a)).ev w = bitF (rd regs a).toBit := by
  obtain ⟨t, ls, e, r⟩ := rep_of_some hI h; rw [e]; exact asBit_ev r

end

theorem evalOp_len {impl : OpImpl} {κ : Kind} {inp : Input} {regs : Array Val} {op : Op}
    {vs : List Val} {ok : Bool} (h : evalOp impl κ inp regs op = .vals vs ok) :
    vs.length = op.nOut := by
  cases op <;> simp only [evalOp, Res.vals.injEq, reduceCtorEq] at h <;> obtain ⟨rfl, -⟩ := h <;> rfl

theorem impSlots_len (cs : CS) : ∀ (o : ℕ) (ts : List Ty), (impSlots cs o ts).length = ts.length
  | _, [] => rfl
  | o, _ :: ts => by simp [impSlots, impSlots_len cs _ ts]

theorem opOut_len (P : Params) (cs : CS) (op : Op) : (opOut P cs op).slots.length = op.nOut := by
  cases op <;> simp only [opOut, imports, impSlots_len, skip, muxOut] <;> (try split) <;>
    (try split) <;> (try split) <;> simp [Op.nOut, kinds]

theorem range_getD {l : List F} {n : ℕ} (h : l.length = n) : (List.range n).map (l.getD · 0) = l := by
  subst h; apply List.ext_getElem (by simp); intro j h1 h2; simp [List.getElem?_eq_getElem h2]

theorem slot_of_ty {s : Slot} {t : Ty} (h : s.ty? = some t) : ∃ ls, s = some (t, ls) := by
  rcases s with _ | ⟨t', ls⟩ <;> simp [Slot.ty?] at h; exact ⟨ls, by rw [h]⟩

theorem K_mul_f₀ (x y : K) : (x * y).f₀ = x.f₀ * y.f₀ + F.alpha * (x.f₁ * y.f₁) := by
  show (K.mul x y).f₀ = _; simp [K.mul, F.mulAlpha_eq]
theorem K_mul_f₁ (x y : K) : (x * y).f₁ = (x.f₀ + x.f₁) * (y.f₀ + y.f₁) + x.f₀ * y.f₀ := rfl

theorem inv_rows {x i s : F} (h1 : x * i = s) (h2 : x * (1 - s) = 0) (h3 : i * (1 - s) = 0) :
    i = x⁻¹ := by
  by_cases hx : x = 0
  · subst hx; simp at h1; subst h1; simpa using h3
  · have : s = 1 := by have := (mul_eq_zero.1 h2).resolve_left hx; linear_combination -this
    subst this; exact (inv_eq_of_mul_eq_one_right h1).symm

theorem enc_eq {w : Asg} {t : Ty} {la lb : List Lin} {va vb : Val} (ha : RepS w (some (t, la)) va)
    (hb : RepS w (some (t, lb)) vb)
    (h : ∀ j < t.len, (comp (some (t, la)) j).ev w = (comp (some (t, lb)) j).ev w) :
    encV va = encV vb :=
  encV_ext hb (encV_length ha.1) fun j hj => by rw [← h j hj, comp_ev ha]

theorem rows_range {w : Asg} {n : ℕ} {f : ℕ → Row} (h : ∀ r ∈ (List.range n).map f, r.Holds w) :
    ∀ j < n, (f j).Holds w := fun j hj => h _ (List.mem_map.2 ⟨j, List.mem_range.2 hj, rfl⟩)

/-! ## One op -/

/-- **One op is sound**: if its rows hold and the operands' slots represent the registers, a
non-import's result slots represent its results and a non-foreign op's flag is set. -/
theorem opOut_sound {impl : OpImpl} {κ : Kind} {inp : Input} {w : Asg} {P : Params} {cs : CS}
    {regs : Array Val} (hP : SelOk w P κ) (hI : ∀ i, RepS w (cs.slot i) (rd regs i)) (op : Op)
    (hr : ∀ r ∈ (opOut P cs op).rows, r.Holds w) {vs : List Val} {ok : Bool}
    (he : evalOp impl κ inp regs op = .vals vs ok) :
    ((opOut P cs op).imp = false → List.Forall₂ (RepS w) (opOut P cs op).slots vs) ∧
    ((opOut P cs op).foreign = false → ok = true) := by
  cases op <;> simp only [evalOp, Res.vals.injEq, reduceCtorEq] at he <;> obtain ⟨rfl, rfl⟩ := he
  all_goals first
    | (simp [opOut, imports, skip, RepS]; done)
    | skip
  case const c =>
    simp only [opOut]
    split
    · rename_i t ht
      split_ifs with h2
      · have hty : tyOf (c κ) = some t := by cases κ <;> simp_all
        simp only [List.forall₂_cons, List.Forall₂.nil, and_true, imp_self, implies_true,
          RepS, hty, List.map_map, true_and]
        intro _
        simp only [Function.comp_def, kc_ev hP]; exact range_getD (encV_length hty)
      · simp [skip, RepS]
    · simp [skip, RepS]
  case mulF a b =>
    simp only [opOut] at hr ⊢; split_ifs at hr ⊢ with hb
    · simp only [both, Bool.and_eq_true] at hb
      simp only [List.mem_singleton, forall_eq, Row.Holds, asF_slot hI hb.1, asF_slot hI hb.2,
        CS.cell, Lin.ev_cell] at hr
      simp [RepS, tyOf, encV, CS.cell, hr]
    · simp [skip, RepS]
  case addF a b =>
    simp only [opOut]; split_ifs with hb
    · simp only [both, Bool.and_eq_true] at hb
      simp [RepS, tyOf, encV, asF_slot hI hb.1, asF_slot hI hb.2]
    · simp [skip, RepS]
  case mulK a b =>
    simp only [opOut] at hr ⊢; split_ifs at hr ⊢ with hb
    · simp only [both, Bool.and_eq_true] at hb
      have ha := asK_slot hI hb.1; have hb' := asK_slot hI hb.2
      simp only [List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false, forall_eq_or_imp,
        forall_eq, Row.Holds, Lin.ev_append, ha.1, ha.2, hb'.1, hb'.2, CS.cell, Lin.ev_cell] at hr
      obtain ⟨h0, h1, h2⟩ := hr
      simp only [List.forall₂_cons, List.Forall₂.nil, and_true, RepS, tyOf, encV, encK,
        List.map_cons, List.map_nil, Lin.ev_append, Lin.ev_smul, CS.cell, Lin.ev_cell, K_mul_f₀,
        K_mul_f₁, ← h0, ← h1, ← h2, true_and]
      exact ⟨fun _ => trivial, fun _ => trivial⟩
    · simp [skip, RepS]
  case addK a b =>
    simp only [opOut]; split_ifs with hb
    · simp only [both, Bool.and_eq_true] at hb
      have ha := asK_slot hI hb.1; have hb' := asK_slot hI hb.2
      simp only [List.forall₂_cons, List.Forall₂.nil, and_true, RepS, tyOf, encV, encK,
        List.map_cons, List.map_nil, Lin.ev_append, ha.1, ha.2, hb'.1, hb'.2, true_and]
      exact ⟨fun _ => rfl, fun _ => trivial⟩
    · simp [skip, RepS]
  case mulKF a b =>
    simp only [opOut] at hr ⊢; split_ifs at hr ⊢ with hb
    · simp only [both, Bool.and_eq_true] at hb
      have ha := asK_slot hI hb.1
      simp only [List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false, forall_eq_or_imp,
        forall_eq, Row.Holds, ha.1, ha.2, asF_slot hI hb.2, CS.cell, Lin.ev_cell] at hr
      simp only [List.forall₂_cons, List.Forall₂.nil, and_true, RepS, tyOf, encV, encK,
        List.map_cons, List.map_nil, CS.cell, Lin.ev_cell, ← hr.1, ← hr.2, true_and]
      exact ⟨fun _ => rfl, fun _ => trivial⟩
    · simp [skip, RepS]
  case invF a =>
    simp only [opOut] at hr ⊢; split_ifs at hr ⊢ with ha
    · simp only [List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false, forall_eq_or_imp,
        forall_eq, Row.Holds, asF_slot hI ha, CS.cell, Lin.ev_cell, Lin.ev_sub, hP.1,
        Lin.ev_nil, add_zero] at hr
      simp [RepS, tyOf, encV, CS.cell, inv_rows hr.1 hr.2.1 hr.2.2]
    · simp [skip, RepS]
  case packF xs =>
    simp only [opOut]; split_ifs with hx
    · simp only [List.all_eq_true] at hx
      simp only [List.forall₂_cons, List.Forall₂.nil, and_true, RepS, tyOf, encV, List.size_toArray,
        List.length_map, List.toList_toArray, List.map_map, true_and]
      exact ⟨fun _ => List.map_congr_left fun x hx' => asF_slot hI (hx x hx'), fun _ => trivial⟩
    · simp [skip, RepS]
  case packK xs =>
    simp only [opOut]; split_ifs with hx
    · simp only [List.all_eq_true] at hx
      simp only [List.forall₂_cons, List.Forall₂.nil, and_true, RepS, tyOf, encV, List.size_toArray,
        List.length_map, List.toList_toArray, List.map_flatMap, List.flatMap_map, true_and]
      refine ⟨fun _ => List.flatMap_congr fun x hx' => ?_, fun _ => trivial⟩
      have := asK_slot hI (hx x hx'); simp [encK, this.1, this.2]
    · simp [skip, RepS]
  case getF a i =>
    simp only [opOut]; split_ifs with ha
    · obtain ⟨t, ls, e, r⟩ := rep_of_some hI ha
      simp only [RepS, tyOf, encV, e, List.map_cons, List.map_nil, List.forall₂_cons,
        List.Forall₂.nil, and_true, true_and]
      exact ⟨fun _ => by simpa using getD_ev (asAF_ev r) i, fun _ => trivial⟩
    · simp [skip, RepS]
  case getK a i =>
    simp only [opOut]; split_ifs with ha
    · obtain ⟨t, ls, e, r⟩ := rep_of_some hI ha
      have := flatMap_encK_getD (rd regs a).toAK.toList i
      simp only [RepS, tyOf, encV, encK, e, List.map_cons, List.map_nil, List.forall₂_cons,
        List.Forall₂.nil, and_true, true_and]
      refine ⟨fun _ => ?_, fun _ => trivial⟩
      have h0 := (getD_ev (asAK_ev r) (2 * i)).trans this.1
      have h1 := (getD_ev (asAK_ev r) (2 * i + 1)).trans this.2
      simp only [List.getD_eq_getElem?_getD, Array.getElem?_toList] at h0 h1
      simp [h0, h1]
    · simp [skip, RepS]
  case eqTable r =>
    simp only [opOut] at hr ⊢; split_ifs at hr ⊢ with ha
    · obtain ⟨t, ls, e, rr⟩ := rep_of_some hI ha
      rw [e] at hr ⊢
      have := eqRows_sound (cs := cs) _ [P.one] 0 _ #[1] (asAF_ev rr) (by simp [hP.1]) hr
      simp only [List.forall₂_cons, List.Forall₂.nil, and_true, RepS, tyOf, encV]
      refine ⟨fun _ => ⟨?_, ?_⟩, fun _ => trivial⟩
      · rw [← List.length_map (f := Lin.ev w), this]; simp [eqTab]
      · rw [this]; simp [eqTab]
    · simp [skip, RepS]
  case splitDigest d =>
    simp only [opOut]; split_ifs with hd
    · obtain ⟨ls, e⟩ := slot_of_ty hd
      have r := hI d; rw [e] at r
      have h0 := comp_ev r 0; have h1 := comp_ev r 1
      rw [e]; generalize rd regs d = v at r h0 h1
      have := r.1; rcases v with x | x | x | x | x | x | x | x | x <;> simp [tyOf] at this
      simp_all [RepS, tyOf, encV, Val.toD, dlo, dhi]
    · simp [skip, RepS]
  case keep act n o =>
    simp only [opOut] at hr ⊢
    rcases hn : (cs.slot n).ty? with _ | t <;> rcases ho : (cs.slot o).ty? with _ | t' <;>
      simp only [hn, ho] at hr ⊢
    all_goals try (simp [skip, RepS]; done)
    · obtain ⟨ln, en⟩ := slot_of_ty hn; obtain ⟨lo, eo⟩ := slot_of_ty ho
      have rn := hI n; have ro := hI o; rw [en] at rn; rw [eo] at ro
      by_cases htt : t = t'
      · subst htt
        by_cases hc : act .L32 = act .P30 ∧ act .P30 = act .N30
        · have : act κ = act .L32 := by cases κ <;> simp_all
          rw [ite_cond_eq_true _ _ (eq_true rfl), ite_cond_eq_true _ _ (eq_true hc), this]
          cases h : act .L32 <;> simp [en, eo, rn, ro]
        · simp only [↓reduceIte, hc] at hr ⊢; rw [en, eo] at hr ⊢
          exact ⟨fun _ => muxOut_sound ro rn (gate_ev hP act) hr, fun _ => trivial⟩
      · simp [htt, skip, RepS]
  case selectHalf b x y =>
    simp only [opOut] at hr ⊢
    rcases hb : (cs.slot b).ty? with _ | tb <;> rcases hx : (cs.slot x).ty? with _ | t <;>
      rcases hy : (cs.slot y).ty? with _ | t' <;> simp only [hb, hx, hy] at hr ⊢
    all_goals try (simp [skip, RepS]; done)
    · obtain ⟨lb, eb⟩ := slot_of_ty hb
      obtain ⟨lx, ex⟩ := slot_of_ty hx; obtain ⟨ly, ey⟩ := slot_of_ty hy
      have rx := hI x; have ry := hI y; rw [ex] at rx; rw [ey] at ry
      by_cases htt : t = t'
      · subst htt; simp only [↓reduceIte] at hr ⊢; rw [ex, ey] at hr ⊢
        exact ⟨fun _ => muxOut_sound rx ry (asBit_slot hI (by simp [eb])) hr, fun _ => trivial⟩
      · simp [htt, skip, RepS]
  case assertEq a b act =>
    simp only [opOut] at hr ⊢
    rcases ha : (cs.slot a).ty? with _ | t <;> rcases hb : (cs.slot b).ty? with _ | t' <;>
      simp only [ha, hb] at hr ⊢
    all_goals try (simp; done)
    · obtain ⟨la, ea⟩ := slot_of_ty ha; obtain ⟨lb, eb⟩ := slot_of_ty hb
      have ra := hI a; have rb := hI b; rw [ea] at ra; rw [eb] at rb
      refine ⟨fun _ => by split_ifs <;> exact List.Forall₂.nil, fun _ => ?_⟩
      cases hact : act κ
      · rfl
      have hg : (P.gate act).ev w = 1 := by simp [gate_ev hP, hact, bitF]
      split_ifs at hr with htt
      · obtain ⟨rfl, hok⟩ := htt
        have hrow := rows_range hr
        rw [ea, eb] at hrow
        simp only [Row.Holds, hg, one_mul, Lin.ev_sub, Lin.ev_nil, sub_eq_zero] at hrow
        simpa using eqv_of_enc ra.1 rb.1 hok (enc_eq ra rb hrow)
      · simp [Row.Holds, hg, hP.1] at hr
  case assertZero a act =>
    simp only [opOut] at hr ⊢
    rcases ha : (cs.slot a).ty? with _ | t <;> simp only [ha] at hr ⊢
    · simp
    · obtain ⟨la, ea⟩ := slot_of_ty ha
      have ra := hI a; rw [ea] at ra
      refine ⟨fun _ => List.Forall₂.nil, fun _ => ?_⟩
      cases hact : act κ
      · rfl
      have hg : (P.gate act).ev w = 1 := by simp [gate_ev hP, hact, bitF]
      have hrow := rows_range hr
      rw [ea] at hrow
      simp only [Row.Holds, hg, one_mul, Lin.ev_nil, comp_ev ra] at hrow
      simp only [Bool.not_true, Bool.false_or]
      refine isZero_of_enc ra.1 fun x hx => ?_
      obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem hx
      rw [← List.getD_eq_getElem _ 0]; exact hrow j (encV_length ra.1 ▸ hj)
  case assertOneHot a b c =>
    simp only [opOut] at hr ⊢
    split_ifs at hr ⊢ with hs
    · simp only [Bool.and_eq_true] at hs
      simp only [List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false, forall_eq_or_imp,
        forall_eq, Row.Holds, Lin.ev_append, Lin.ev_nil, asBit_slot hI hs.1.1,
        asBit_slot hI hs.1.2, asBit_slot hI hs.2] at hr
      exact ⟨fun _ => List.Forall₂.nil, fun _ =>
        oneHot_sound hP.1 rfl rfl rfl hr.1 hr.2.1 hr.2.2.1 hr.2.2.2⟩
    · simp

theorem opOut_tin (P : Params) (cs : CS) (op : Op) : (opOut P cs op).tin = none := by
  cases op <;> simp only [opOut, imports, skip, muxOut] <;> (try split) <;> (try split) <;>
    (try split) <;> rfl

theorem opOut_aux (P : Params) (cs : CS) (op : Op) : (opOut P cs op).aux = [] := by
  cases op <;> simp only [opOut, imports, skip, muxOut] <;> (try split) <;> (try split) <;>
    (try split) <;> rfl

theorem ask_imp {impl : OpImpl} {κ : Kind} {inp : Input} {regs : Array Val} {op : Op} {q : ByteArray}
    (P : Params) (cs : CS) (h : evalOp impl κ inp regs op = .ask q) : (opOut P cs op).imp = true := by
  cases op <;> simp only [evalOp, reduceCtorEq] at h <;> rfl

theorem ask_nOut {impl : OpImpl} {κ : Kind} {inp : Input} {regs : Array Val} {op : Op}
    {q : ByteArray} (h : evalOp impl κ inp regs op = .ask q) : op.nOut = 1 := by
  cases op <;> simp only [evalOp, reduceCtorEq] at h <;> rfl

/-! ## The program -/

/-- **The compiler's invariant**: one slot per register, each representing its register. -/
def Inv (w : Asg) (cs : CS) (regs : Array Val) : Prop :=
  cs.slots.size = regs.size ∧ ∀ i, RepS w (cs.slot i) (rd regs i)

theorem rd_append_left {a b : Array Val} {i : ℕ} (h : i < a.size) : rd (a ++ b) i = rd a i := by
  simp [rd, Array.getElem?_append_left h]

theorem rd_append_right (a : Array Val) (b : List Val) (c : Array Val) {j : ℕ} (h : j < b.length) :
    rd (a ++ b.toArray ++ c) (a.size + j) = b[j] := by
  rw [rd, Array.getElem?_append_left (by simp [h]), Array.getElem?_append_right (by omega)]
  simp [h]

theorem slot_append_right (a : Array Slot) (b : List Slot) (c : Array Slot) {j : ℕ}
    (h : j < b.length) : (a ++ b.toArray ++ c).getD (a.size + j) none = b[j] := by
  simp only [Array.getD_eq_getD_getElem?, Array.append_assoc]
  rw [Array.getElem?_append_right (by omega), Nat.add_sub_cancel_left,
    Array.getElem?_append_left (by simpa using h)]
  simp [h]

theorem inv_append {w : Asg} {cs : CS} {regs : Array Val} (h : Inv w cs regs) {ss : List Slot}
    {vs : List Val} (hl : ss.length = vs.length)
    (hr : ∀ j (hj : j < ss.length), RepS w ss[j] (vs[j]'(hl ▸ hj))) (o : Out) (op : Op)
    (hs : o.slots = ss) : Inv w (cs.add op o) (regs ++ vs.toArray) := by
  subst hs
  refine ⟨by simp [CS.add, h.1, hl], fun i => ?_⟩
  simp only [CS.slot, CS.add]
  by_cases h1 : i < cs.slots.size
  · rw [Array.getD_eq_getD_getElem?, Array.getElem?_append_left h1, rd_append_left (h.1 ▸ h1)]
    simpa [CS.slot] using h.2 i
  by_cases h2 : i < cs.slots.size + o.slots.length
  · obtain ⟨j, rfl⟩ : ∃ j, i = cs.slots.size + j := ⟨i - cs.slots.size, by omega⟩
    have := slot_append_right cs.slots o.slots #[] (by omega : j < o.slots.length)
    have h' := rd_append_right regs vs #[] (by omega : j < vs.length)
    simp only [Array.append_empty] at this h'
    rw [this, h.1, h']; exact hr j (by omega)
  · rw [Array.getD_eq_getD_getElem?, Array.getElem?_eq_none (by simp; omega)]; trivial

theorem exec_prefix {impl : OpImpl} {κ : Kind} {inp : Input} :
    ∀ (ops : List Op) (s : St) (tr : Trace) {s' : St} {tr' : Trace},
    exec impl κ inp ops s tr = some (s', tr') → ∃ more : Array Val, s'.regs = s.regs ++ more
  | [], s, tr, s', tr', h => by simp [exec] at h; exact ⟨#[], by simp [← h.1]⟩
  | op :: ops, s, tr, s', tr', h => by
    simp only [exec] at h
    split at h
    · obtain ⟨m, hm⟩ := exec_prefix ops _ _ h; exact ⟨_, by rw [hm, Array.append_assoc]⟩
    · split at h
      · simp at h
      · split at h
        · obtain ⟨m, hm⟩ := exec_prefix ops _ _ h
          exact ⟨_, by rw [hm, Array.push_eq_append, Array.append_assoc]⟩
        · simp at h

/-- **A sound extension** (S-E3): for every op it handles, the contribution has `op.nOut` results,
the op asks nothing, and the contribution's rows, its template instance's rows and its auxiliary
imports give its results (unless imported) and its flag (unless foreign). -/
def ExtOk (impl : OpImpl) (tc : Tpl.TCtx) (X : Ext) : Prop :=
  ∀ (P : Params) (cs : CS) (op : Op) (o : Out), X P cs op = some o →
    o.slots.length = op.nOut ∧
    ∀ (κ : Kind) (inp : Input) (w : Asg) (regs : Array Val), SelOk w P κ →
      (∀ i, RepS w (cs.slot i) (rd regs i)) →
      (∀ q, evalOp impl κ inp regs op ≠ .ask q) ∧
      ((∀ r ∈ o.rows, r.Holds w) →
       (∀ t ∈ o.tin, ∀ r ∈ Tpl.instRows tc P.one (t.1, cs.tcount t.1, t.2), r.Holds w) →
       (∀ a ∈ o.aux, a.1.map (Lin.ev w) = a.2.2.val (rd regs a.2.1)) →
       ∀ vs ok, evalOp impl κ inp regs op = .vals vs ok →
         (o.imp = false → List.Forall₂ (RepS w) o.slots vs) ∧ (o.foreign = false → ok = true))

theorem noExt_ok (impl : OpImpl) (tc : Tpl.TCtx) : ExtOk impl tc noExt := by
  intro _ _ _ _ h; simp [noExt] at h

theorem compileFromX_mono (X : Ext) (P : Params) : ∀ (ops : List Op) (cs : CS), ∃ ss rs,
    (compileFromX X P cs ops).slots = cs.slots ++ ss ∧ (compileFromX X P cs ops).rows = rs ++ cs.rows ∧
    cs.imp ⊆ (compileFromX X P cs ops).imp ∧ cs.fors ⊆ (compileFromX X P cs ops).fors ∧
    cs.tins ⊆ (compileFromX X P cs ops).tins ∧ cs.aux ⊆ (compileFromX X P cs ops).aux
  | [], cs => ⟨#[], [], by simp [compileFromX]⟩
  | op :: ops, cs => by
    obtain ⟨ss, rs, h1, h2, h3, h4, h5, h6⟩ :=
      compileFromX_mono X P ops (cs.add op (stepOut X P cs op))
    have e : compileFromX X P cs (op :: ops) =
        compileFromX X P (cs.add op (stepOut X P cs op)) ops := rfl
    rw [e]
    refine ⟨(stepOut X P cs op).slots.toArray ++ ss, rs ++ (stepOut X P cs op).rows.reverse,
      h1.trans (by simp [CS.add, Array.append_assoc]),
      h2.trans (by simp [CS.add, List.reverseAux_eq, List.append_assoc]),
      fun x hx => h3 ?_, fun x hx => h4 ?_, fun x hx => h5 ?_, fun x hx => h6 ?_⟩ <;>
      simp only [CS.add] <;> (try split) <;> simp [hx]

/-- The induction behind `compile_sound` (with an extension). -/
theorem compileFromX_sound {impl : OpImpl} {κ : Kind} {inp : Input} {w : Asg} {P : Params}
    {tc : Tpl.TCtx} {X : Ext} (hX : ExtOk impl tc X) (hP : SelOk w P κ) :
    ∀ (ops : List Op) (cs : CS) (s s' : St) (tr tr' : Trace),
    Inv w cs s.regs → exec impl κ inp ops s tr = some (s', tr') →
    (∀ r ∈ (compileFromX X P cs ops).rows, r.Holds w) →
    (∀ t ∈ (compileFromX X P cs ops).tins, ∀ r ∈ Tpl.instRows tc P.one t, r.Holds w) →
    (∀ a ∈ (compileFromX X P cs ops).aux,
      a.1.1.map (Lin.ev w) = a.1.2.2.val (rd (s'.regs.extract 0 a.2) a.1.2.1)) →
    (∀ i ∈ (compileFromX X P cs ops).imp, RepS w ((compileFromX X P cs ops).slot i) (rd s'.regs i)) →
    (∀ p ∈ (compileFromX X P cs ops).fors,
      flagOf impl κ inp (s'.regs.extract 0 p.2) p.1 = true) →
    s'.ok = s.ok ∧ Inv w (compileFromX X P cs ops) s'.regs
  | [], cs, s, s', tr, tr', hI, he, _, _, _, _, _ => by
    simp [exec] at he; obtain ⟨rfl, rfl⟩ := he; exact ⟨rfl, hI⟩
  | op :: ops, cs, s, s', tr, tr', hI, he, hr, ht, hx, hi, hf => by
    have e : compileFromX X P cs (op :: ops) =
        compileFromX X P (cs.add op (stepOut X P cs op)) ops := rfl
    rw [e] at hr ht hx hi hf ⊢
    set o := stepOut X P cs op with ho
    obtain ⟨ss, rs, hsl, hrw, himp, hfor, htin, haux⟩ := compileFromX_mono X P ops (cs.add op o)
    have hro : ∀ r ∈ o.rows, r.Holds w := fun r h =>
      hr r (by
        rw [hrw]; simp only [CS.add, List.reverseAux_eq]
        exact List.mem_append_right _ (List.mem_append_left _ (List.mem_reverse.2 h)))
    have hto : ∀ t ∈ o.tin, ∀ r ∈ Tpl.instRows tc P.one (t.1, cs.tcount t.1, t.2), r.Holds w :=
      fun t htm r hr' => ht _ (htin (by simp only [CS.add, Option.mem_def.1 htm]; simp)) r hr'
    have hpre : ∀ (m : Array Val), (s.regs ++ m).extract 0 cs.slots.size = s.regs := fun m => by
      rw [hI.1, Array.extract_append_left, Array.extract_size]
    -- the new registers' values, read off the final state
    have fin : ∀ (vs : List Val) (s1 : St), s1.regs = s.regs ++ vs.toArray →
        (∃ m, s'.regs = s1.regs ++ m) → o.imp = true →
        (hl : o.slots.length = vs.length) →
        ∀ j (hj : j < o.slots.length), RepS w o.slots[j] (vs[j]'(hl ▸ hj)) := by
      intro vs s1 hs1 ⟨m, hm⟩ hio hl j hj
      have := hi (cs.slots.size + j) (himp (by simp [CS.add, hio, List.mem_range'_1, hj]))
      have hs := slot_append_right cs.slots o.slots ss hj
      have hv := rd_append_right s.regs vs m (by omega : j < vs.length)
      rw [CS.slot, hsl] at this; simp only [CS.add] at this
      rw [hs, hm, hs1, hI.1, hv] at this; exact this
    have flag : ∀ (vs : List Val) (s1 : St), s1.regs = s.regs ++ vs.toArray →
        (∃ m, s'.regs = s1.regs ++ m) → o.foreign = true →
        flagOf impl κ inp s.regs op = true := by
      intro vs s1 hs1 ⟨m, hm⟩ hfo
      have := hf (op, cs.slots.size) (hfor (by simp [CS.add, hfo]))
      rwa [hm, hs1, Array.append_assoc, hpre] at this
    have hauxo : ∀ (vs : List Val) (s1 : St), s1.regs = s.regs ++ vs.toArray →
        (∃ m, s'.regs = s1.regs ++ m) →
        ∀ a ∈ o.aux, a.1.map (Lin.ev w) = a.2.2.val (rd s.regs a.2.1) := by
      intro vs s1 hs1 ⟨m, hm⟩ a ha
      have := hx (a, cs.slots.size) (haux (by simp [CS.add, ha]))
      rwa [hm, hs1, Array.append_assoc, hpre] at this
    -- the step's soundness: the extension's or `opOut`'s
    have hstep : (∀ q, evalOp impl κ inp s.regs op ≠ .ask q) ∨ X P cs op = none := by
      rcases hXo : X P cs op with _ | o'
      · exact .inr rfl
      · exact .inl ((hX P cs op o' hXo).2 κ inp w s.regs hP hI.2).1
    have hlen : o.slots.length = op.nOut := by
      rcases hXo : X P cs op with _ | o'
      · simp only [ho, stepOut, hXo, Option.getD_none]; exact opOut_len P cs op
      · simp only [ho, stepOut, hXo, Option.getD_some]; exact (hX P cs op o' hXo).1
    simp only [exec] at he
    split at he
    · rename_i vs ok hev
      have hl := hlen.trans (evalOp_len hev).symm
      have hm := exec_prefix ops _ _ he
      have hsnd : (o.imp = false → List.Forall₂ (RepS w) o.slots vs) ∧ (o.foreign = false → ok = true) := by
        rcases hXo : X P cs op with _ | o'
        · simp only [ho, stepOut, hXo, Option.getD_none] at hro ⊢
          exact opOut_sound hP hI.2 op hro hev
        · have eo : o = o' := by simp [ho, stepOut, hXo]
          rw [eo] at hro hto ⊢
          exact ((hX P cs op o' hXo).2 κ inp w s.regs hP hI.2).2 hro hto
            (eo ▸ hauxo vs _ rfl hm) vs ok hev
      have hnew : ∀ j (hj : j < o.slots.length), RepS w o.slots[j] (vs[j]'(hl ▸ hj)) := by
        cases hio : o.imp
        · exact fun j hj => (List.forall₂_iff_get.1 (hsnd.1 hio)).2 j hj _
        · exact fin vs _ rfl hm hio hl
      have hok : ok = true := by
        cases hfo : o.foreign
        · exact hsnd.2 hfo
        · have := flag vs _ rfl hm hfo; simpa [flagOf, hev] using this
      have ih := compileFromX_sound hX hP ops _ _ s' tr tr'
        (inv_append hI hl hnew _ op rfl) he hr ht hx hi hf
      exact ⟨by rw [ih.1, hok, Bool.and_true], ih.2⟩
    · rename_i q hev
      have hXn : X P cs op = none := hstep.resolve_left fun h => h q hev
      have ho' : o = opOut P cs op := by simp [ho, stepOut, hXn]
      split at he
      · simp at he
      · rename_i q' a tr0
        split at he
        · have hio : o.imp = true := ho' ▸ ask_imp P cs hev
          have hl : o.slots.length = [Val.d a].length := by
            rw [hlen, ask_nOut hev]; rfl
          have hm := exec_prefix ops _ _ he
          have hnew := fin [.d a] ⟨s.regs.push (.d a), s.ok⟩ rfl hm hio hl
          exact compileFromX_sound hX hP ops _ ⟨s.regs.push (.d a), s.ok⟩ s' tr0 tr'
            (inv_append hI hl hnew _ op rfl) he hr ht hx hi hf
        · simp at he

/-! ## `compile_sound` -/

/-- **`compile_sound`** (BLUEPRINT §4.3, FR-R3′): if the op list runs to state `s` on the trace
(kind `κ`), the selector forms are one-hot at `κ`, every compiled row holds, every import's cells
hold its value and every foreign assertion's flag is set, then the run accepts (`s.ok`) and every
tracked register's cells hold its value. -/
theorem compile_sound {impl : OpImpl} {κ : Kind} {inp : Input} {ops : List Op} {tr tr' : Trace}
    {s : St} {w : Asg} {P : Params} (base : ℕ) (hP : SelOk w P κ)
    (he : exec impl κ inp ops St.init tr = some (s, tr'))
    (hr : ∀ r ∈ (compile P base ops).rows, r.Holds w)
    (hi : ∀ i ∈ (compile P base ops).imp, RepS w ((compile P base ops).slot i) (rd s.regs i))
    (hf : ∀ p ∈ (compile P base ops).fors, flagOf impl κ inp (s.regs.extract 0 p.2) p.1 = true) :
    s.ok = true ∧ ∀ i, RepS w ((compile P base ops).slot i) (rd s.regs i) := by
  have hn : ∀ (ops : List Op) (cs : CS), cs.tins = [] → cs.aux = [] →
      (compileFrom P cs ops).tins = [] ∧ (compileFrom P cs ops).aux = [] := by
    intro ops; induction ops with
    | nil => intro cs h1 h2; exact ⟨h1, h2⟩
    | cons op ops ih =>
      intro cs h1 h2
      exact ih _ (by simp [CS.add, stepOut, noExt, opOut_tin, h1]) (by simp [CS.add, stepOut, noExt, opOut_aux, h2])
  have h0 := hn ops (CS.init base) rfl rfl
  have h := compileFromX_sound (noExt_ok impl ⟨fun _ => ⟨[], []⟩, fun _ _ => 0⟩) hP ops (CS.init base)
    St.init s tr tr' ⟨rfl, fun i => by simp [CS.slot, CS.init, RepS]⟩ he hr
    (by simp [compile] at h0 ⊢; simp [h0.1]) (by simp [compile] at h0 ⊢; simp [h0.2]) hi hf
  exact ⟨h.1, h.2.2⟩

/-- **`compileX_sound`** (S-E3's `compileT_sound` shape): `compile_sound` with a sound extension;
the template instances' rows and the auxiliary imports join the hypotheses. -/
theorem compileX_sound {impl : OpImpl} {κ : Kind} {inp : Input} {ops : List Op} {tr tr' : Trace}
    {s : St} {w : Asg} {P : Params} {tc : Tpl.TCtx} {X : Ext} (hX : ExtOk impl tc X) (base : ℕ)
    (hP : SelOk w P κ) (he : exec impl κ inp ops St.init tr = some (s, tr'))
    (hr : ∀ r ∈ (compileX X P base ops).rows, r.Holds w)
    (ht : ∀ r ∈ (compileX X P base ops).tplRows tc P.one, r.Holds w)
    (hx : ∀ a ∈ (compileX X P base ops).aux,
      a.1.1.map (Lin.ev w) = a.1.2.2.val (rd (s.regs.extract 0 a.2) a.1.2.1))
    (hi : ∀ i ∈ (compileX X P base ops).imp, RepS w ((compileX X P base ops).slot i) (rd s.regs i))
    (hf : ∀ p ∈ (compileX X P base ops).fors, flagOf impl κ inp (s.regs.extract 0 p.2) p.1 = true) :
    s.ok = true ∧ ∀ i, RepS w ((compileX X P base ops).slot i) (rd s.regs i) := by
  have h := compileFromX_sound hX hP ops (CS.init base) St.init s tr tr'
    ⟨rfl, fun i => by simp [CS.slot, CS.init, RepS]⟩ he hr
    (fun t htm r hr' => ht r (List.mem_flatMap.2 ⟨t, htm, hr'⟩)) hx hi hf
  exact ⟨h.1, h.2.2⟩

end Circ
end FR
