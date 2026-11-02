-- G6: this module also holds the former modules `FRBlake2sCircuit` (one section each, in import order).
import Mathlib.Algebra.CharP.Defs
import Mathlib.Data.ZMod.Basic
import Batteries.Data.BitVec.Lemmas
import Mathlib.Data.Nat.Bitwise

section G6_FRBlake2sCircuit

-- Copied from `submissions/spartan-srom/lean/SpartanSromBlake2sCircuit.lean` (this repository,
-- branch `v4/flock-recursive` at `783328c`), renamed to the namespace `FR`; no other change. That
-- file was ported from v3 `spartan-chain` (submissions repo, local `main` at `1f59b38`) to v4.

/-!
# Product-gate circuits and their R1CS with `C = I`

Provenance: copied from leanerVM (Apache-2.0, github.com/Verified-zkEVM/leanerVM, `main` at
`95957214d42b6d5e21d7066f760e5ec256514cf8`; the files are identical at `e715c49` and on the branch
`docs/protocol-headline-theorems` at `532ebb4`): `LeanerVM/Protocol/ToArkLib/Flock/Circuit.lean`
(all of it) and `LeanerVM/Protocol/ToArkLib/Flock/BlockR1CS.lean` (the structure, `Holds` and
`IsBool` only). Modified (Apache-2.0 §4(b)):
* the module-system annotations are dropped; the namespace is `FR`;
* a block is a function `Fin (2 ^ m) → R`, not CompPoly's `CMlPolynomialEval R m`;
* `BlockR1CS m` keeps only the two Boolean matrices (no ring parameter, no walks: the verifier's
  walk is `FRBlake2sWalk.lean`); `Holds` multiplies the matrices out naively;
* the batch layout, the linearity and adjoint lemmas of `BlockR1CS.lean` are not copied.

A Boolean circuit whose XOR wires are substituted into their consumers has one committed wire
per AND gate: position `k` of a block of `2 ^ m` positions holds the product of two GF(2) linear
forms of other positions. This is a rank-one constraint system `(A z) ∘ (B z) = z` whose rows are
the gates' forms.

* `Form m`, a linear form over the positions: a bitset, bit `j` set when position `j` is a term.
* `ProductCircuit m`: the constant position (holding `1`), the input positions, and the gates in
  evaluation order. `rowOf c k` is the row of position `k`: its gate if it has one, else
  `(1, 1)` at the constant, `(z_k, 1)` at an input, `(0, 0)` elsewhere.
* `toBlockR1CS c`: the circuit's two matrices.
* `traceF c inp` (a function) and `trace c inp` (a bitset, executable, `trace_getLsbD`): the
  honest block, the gates evaluated in order from the inputs and the constant.
* `Bounded c`: every gate reads only the inputs, the constant and earlier gates, and sits at a
  fresh position.

The two directions, over any nontrivial ring of characteristic two (`holds_iff_gates`):
`trace_satisfies` and `holds_eq_trace`, with `gates_of_holds`.
-/

namespace FR

/-! ## Blocks of an R1CS with `C = I` -/

/-- One block of an R1CS with `C = I` on `2 ^ m` positions: the Boolean matrices `A` and `B`,
`A k j` the entry at row `k` and column `j`. -/
structure BlockR1CS (m : ℕ) where
  /-- The left matrix. -/
  A : Fin (2 ^ m) → Fin (2 ^ m) → Bool
  /-- The right matrix. -/
  B : Fin (2 ^ m) → Fin (2 ^ m) → Bool

namespace BlockR1CS

variable {R : Type*} [CommRing R] {m : ℕ}

/-- Row `k` of the Boolean matrix `M` applied to the block `z`: `Σ_j M k j · z j`. -/
def mulVec (M : Fin (2 ^ m) → Fin (2 ^ m) → Bool) (z : Fin (2 ^ m) → R) (k : Fin (2 ^ m)) : R :=
  ∑ j, if M k j then z j else 0

/-- The block satisfies the constraints: `(A z)_k · (B z)_k = z_k` at every position. -/
def Holds (C : BlockR1CS m) (z : Fin (2 ^ m) → R) : Prop :=
  ∀ k : Fin (2 ^ m), mulVec C.A z k * mulVec C.B z k = z k

/-- A Boolean value: `0` or `1`. -/
def IsBool (x : R) : Prop := x = 0 ∨ x = 1

end BlockR1CS

namespace ProductCircuit

/-! ## Positions and forms -/

/-- A position of a block of `2 ^ m`. -/
abbrev Pos (m : ℕ) := Fin (2 ^ m)

/-- A linear form over GF(2) on the positions: bit `j` set means position `j` is a term. -/
abbrev Form (m : ℕ) := BitVec (2 ^ m)

variable {m : ℕ}

/-- The position `n`, reduced modulo the block size. -/
def pos (n : ℕ) : Pos m := ⟨n % 2 ^ m, Nat.mod_lt _ (Nat.two_pow_pos m)⟩

/-- The form of the single position `j`. -/
def Form.var (j : Pos m) : Form m := BitVec.twoPow _ j

/-- A Boolean in GF(2). -/
def toZ (b : Bool) : ZMod 2 := if b then 1 else 0

/-- The value of a form on a Boolean block, in GF(2): the sum of the selected positions. -/
def Form.evalZ (L : Form m) (z : Pos m → Bool) : ZMod 2 :=
  ∑ j : Pos m, if L.getLsbD j then toZ (z j) else 0

/-- The value of a form on a Boolean block. -/
def Form.eval (L : Form m) (z : Pos m → Bool) : Bool := decide (L.evalZ z = 1)

/-- Parity of a bitvector of width `2 ^ k`, by `k` halving steps. -/
def par : (k : ℕ) → BitVec (2 ^ k) → Bool
  | 0, x => x.getLsbD 0
  | k + 1, x => par k (x.setWidth (2 ^ k) ^^^ (x >>> 2 ^ k).setWidth (2 ^ k))

/-- The value of a form on a block given as a bitset: the parity of `L ∧ z`. -/
def Form.evalB (L z : Form m) : Bool := par m (L &&& z)

/-! ## Circuits -/

/-- A product gate: the two forms whose product the gate's position holds. -/
structure Gate (m : ℕ) where
  /-- The left form, the gate's row of `A`. -/
  a : Form m
  /-- The right form, the gate's row of `B`. -/
  b : Form m
  deriving Inhabited

end ProductCircuit

open ProductCircuit

/-- A block circuit of product gates: the constant position, the input positions, and the gates
in evaluation order, each at its position. -/
structure ProductCircuit (m : ℕ) where
  /-- The position holding `1`. -/
  cpos : Pos m
  /-- The input positions. -/
  inputs : Form m
  /-- The gates, in evaluation order. -/
  gates : Array (Pos m × Gate m)

namespace ProductCircuit

variable {m : ℕ}

/-- The row of position `k` given the gate list `l`: its gate (the first one) if it has one; else
`(1, 1)` at the constant, `(z_k, 1)` at an input, `(0, 0)` elsewhere. -/
def rowOfList (c : ProductCircuit m) (l : List (Pos m × Gate m)) (k : Pos m) : Gate m :=
  match l.lookup k with
  | some g => g
  | none =>
    if k = c.cpos then ⟨Form.var c.cpos, Form.var c.cpos⟩
    else if c.inputs.getLsbD k then ⟨Form.var k, Form.var c.cpos⟩
    else ⟨0, 0⟩

/-- The row of position `k`: its gate (the first one, in evaluation order) if it has one; else
`(1, 1)` at the constant, `(z_k, 1)` at an input, `(0, 0)` elsewhere. -/
def rowOf (c : ProductCircuit m) (k : Pos m) : Gate m := c.rowOfList c.gates.toList k

/-- The circuit's two matrices: row `k` of `A` (of `B`) is the left (right) form of `rowOf k`. -/
def toBlockR1CS (c : ProductCircuit m) : BlockR1CS m :=
  ⟨fun k j ↦ (c.rowOf k).a.getLsbD j, fun k j ↦ (c.rowOf k).b.getLsbD j⟩

/-! ## The honest block -/

/-- The block before any gate: `1` at the constant, the inputs at the input positions, `0`
elsewhere. -/
def initF (c : ProductCircuit m) (inp : Pos m → Bool) : Pos m → Bool :=
  fun j ↦ decide (j = c.cpos) || (c.inputs.getLsbD j && inp j)

/-- One gate: its position takes the product of its forms. -/
def stepF (z : Pos m → Bool) (kg : Pos m × Gate m) : Pos m → Bool :=
  Function.update z kg.1 (kg.2.a.eval z && kg.2.b.eval z)

/-- The honest block of the inputs `inp`: the gates evaluated in order. -/
def traceF (c : ProductCircuit m) (inp : Pos m → Bool) : Pos m → Bool :=
  c.gates.toList.foldl stepF (c.initF inp)

/-- Set bit `k` of a bitset to `b`. -/
def setBitB (z : Form m) (k : Pos m) (b : Bool) : Form m :=
  if b then z ||| Form.var k else z &&& ~~~(Form.var k)

/-- One gate, on bitsets. -/
def stepB (z : Form m) (kg : Pos m × Gate m) : Form m :=
  setBitB z kg.1 (kg.2.a.evalB z && kg.2.b.evalB z)

/-- The block before any gate, as a bitset. -/
def initB (c : ProductCircuit m) (inp : Form m) : Form m := (c.inputs &&& inp) ||| Form.var c.cpos

/-- The honest block of the inputs `inp`, as a bitset: the executable `traceF`. -/
def trace (c : ProductCircuit m) (inp : Form m) : Form m := c.gates.foldl stepB (c.initB inp)

/-! ## Bounded circuits -/

/-- `L` mentions only positions of `avail`. -/
def Sub (L avail : Form m) : Prop := L &&& ~~~avail = 0

instance (L avail : Form m) : Decidable (Sub L avail) := inferInstanceAs (Decidable (_ = _))

/-- A schedule is bounded from the available positions `avail`: each gate reads only available
positions and sits at a fresh one, which becomes available. -/
def BoundedFrom : Form m → List (Pos m × Gate m) → Prop
  | _, [] => True
  | avail, (k, g) :: rest =>
    Sub g.a avail ∧ Sub g.b avail ∧ avail.getLsbD k = false ∧
      BoundedFrom (avail ||| Form.var k) rest

/-- Every gate reads only the inputs, the constant and earlier gates, and the gate positions are
fresh: distinct, not inputs, not the constant. -/
def Bounded (c : ProductCircuit m) : Prop :=
  BoundedFrom (c.inputs ||| Form.var c.cpos) c.gates.toList

/-! ## Boolean blocks over a ring -/

/-- A Boolean as `0` or `1` of a ring. -/
def ofBool (R : Type*) [CommRing R] (b : Bool) : R := if b then 1 else 0

/-- A Boolean block over a ring. -/
def liftBlock (R : Type*) [CommRing R] (z : Pos m → Bool) : Pos m → R := fun k ↦ ofBool R (z k)

/-! ## Forms -/

theorem toZ_injective : Function.Injective toZ := by
  intro a b h
  cases a <;> cases b <;> simp_all [toZ]

theorem toZ_and (a b : Bool) : toZ (a && b) = toZ a * toZ b := by
  cases a <;> cases b <;> simp [toZ]

theorem toZ_xor (a b : Bool) : toZ (a ^^ b) = toZ a + toZ b := by
  cases a <;> cases b <;> decide

theorem toZ_eval (L : Form m) (z : Pos m → Bool) : toZ (L.eval z) = L.evalZ z := by
  unfold Form.eval toZ
  generalize L.evalZ z = x
  fin_cases x <;> rfl

/-- A form reads only the positions it selects. -/
theorem eval_congr {L : Form m} {z z' : Pos m → Bool}
    (h : ∀ j : Pos m, L.getLsbD j → z j = z' j) : L.eval z = L.eval z' := by
  have : L.evalZ z = L.evalZ z' := Finset.sum_congr rfl fun j _ ↦ by
    split_ifs with hj
    · rw [h j hj]
    · rfl
  rw [Form.eval, Form.eval, this]

@[simp] theorem eval_var (j : Pos m) (z : Pos m → Bool) : (Form.var j).eval z = z j := by
  apply toZ_injective
  rw [toZ_eval, Form.evalZ]
  simp only [Form.var, BitVec.getLsbD_twoPow, j.isLt, decide_true, Bool.true_and,
    decide_eq_true_eq, Fin.val_inj]
  rw [Finset.sum_ite_eq]
  simp

@[simp] theorem eval_zero (z : Pos m → Bool) : (0 : Form m).eval z = false := by
  apply toZ_injective
  rw [toZ_eval, Form.evalZ]
  simp [toZ]

/-- Forms are linear: the form of a sum evaluates to the sum. -/
theorem eval_xor (a b : Form m) (z : Pos m → Bool) :
    (a ^^^ b).eval z = (a.eval z ^^ b.eval z) := by
  apply toZ_injective
  rw [toZ_xor, toZ_eval, toZ_eval, toZ_eval, Form.evalZ, Form.evalZ, Form.evalZ,
    ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun j _ ↦ ?_
  rw [BitVec.getLsbD_xor]
  cases a.getLsbD j <;> cases b.getLsbD j <;> cases z j <;> decide

theorem getLsbD_var (k : Pos m) (j : ℕ) : (Form.var k).getLsbD j = decide ((k : ℕ) = j) := by
  simp [Form.var, BitVec.getLsbD_twoPow]

theorem pos_val {n : ℕ} (h : n < 2 ^ m) : ((pos n : Pos m) : ℕ) = n := Nat.mod_eq_of_lt h

theorem sub_getLsbD {L avail : Form m} (h : Sub L avail) {j : Pos m} (hj : L.getLsbD j) :
    avail.getLsbD j := by
  have := congrArg (·.getLsbD j) h
  simp only [BitVec.getLsbD_and, BitVec.getLsbD_not, j.isLt, decide_true, Bool.true_and,
    hj] at this
  simpa using this

theorem sub_iff {L a : Form m} : Sub L a ↔ ∀ j, L.getLsbD j = true → a.getLsbD j = true := by
  constructor
  · intro h j hj
    by_cases hlt : j < 2 ^ m
    · exact sub_getLsbD h (j := ⟨j, hlt⟩) hj
    · simp [BitVec.getLsbD_of_ge L j (by omega)] at hj
  · intro h
    apply BitVec.eq_of_getLsbD_eq
    intro j hj
    simp only [BitVec.getLsbD_and, BitVec.getLsbD_not, hj, decide_true, Bool.true_and]
    cases hL : L.getLsbD j
    · simp
    · simp [h j hL]

theorem Sub.or_right {L a : Form m} (b : Form m) (h : Sub L a) : Sub L (a ||| b) :=
  sub_iff.mpr fun j hj ↦ by rw [BitVec.getLsbD_or, sub_iff.mp h j hj, Bool.true_or]

/-! ## The executable evaluation -/

/-- Parity in GF(2), over the bit indices. -/
private def parZ {n : ℕ} (x : BitVec n) : ZMod 2 := ∑ i ∈ Finset.range n, toZ (x.getLsbD i)

private theorem toZ_par (k : ℕ) (x : BitVec (2 ^ k)) : toZ (par k x) = parZ x := by
  induction k with
  | zero => simp [par, parZ]
  | succ k ih =>
    rw [par, ih, parZ, parZ,
      show Finset.range (2 ^ (k + 1)) = Finset.range (2 ^ k + 2 ^ k) by rw [pow_succ, mul_two],
      Finset.sum_range_add, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun i hi ↦ ?_
    have hi : i < 2 ^ k := Finset.mem_range.mp hi
    simp [hi, toZ_xor, Nat.add_comm]

/-- The executable evaluation is the mathematical one. -/
theorem evalB_eq_eval (L z : Form m) : L.evalB z = L.eval (fun j ↦ z.getLsbD j) := by
  apply toZ_injective
  rw [Form.evalB, toZ_par, toZ_eval, parZ, Form.evalZ, ← Fin.sum_univ_eq_sum_range]
  refine Finset.sum_congr rfl fun j _ ↦ ?_
  simp only [BitVec.getLsbD_and, toZ_and]
  cases L.getLsbD j <;> simp [toZ]

/-! ## The R1CS of a circuit -/

section Ring

variable {R : Type*} [CommRing R]

theorem ofBool_and (a b : Bool) : ofBool R (a && b) = ofBool R a * ofBool R b := by
  cases a <;> cases b <;> simp [ofBool]

theorem ofBool_injective [Nontrivial R] : Function.Injective (ofBool R) := by
  intro a b h
  cases a <;> cases b <;> simp_all [ofBool]

variable [CharP R 2]

private theorem castHom_toZ (b : Bool) : ZMod.castHom (dvd_refl 2) R (toZ b) = ofBool R b := by
  cases b <;> simp [toZ, ofBool]

/-- A row of `0`/`1` entries applied to a Boolean block is the form's value. -/
theorem sum_liftBlock (L : Form m) (z : Pos m → Bool) :
    (∑ j : Pos m, if L.getLsbD j then liftBlock R z j else 0) = ofBool R (L.eval z) := by
  rw [← castHom_toZ, toZ_eval, Form.evalZ, map_sum]
  refine Finset.sum_congr rfl fun j _ ↦ ?_
  split_ifs
  · rw [castHom_toZ]
    simp [liftBlock]
  · simp

theorem mulVec_A_liftBlock (c : ProductCircuit m) (z : Pos m → Bool) (k : Pos m) :
    BlockR1CS.mulVec c.toBlockR1CS.A (liftBlock R z) k = ofBool R ((c.rowOf k).a.eval z) :=
  sum_liftBlock _ z

theorem mulVec_B_liftBlock (c : ProductCircuit m) (z : Pos m → Bool) (k : Pos m) :
    BlockR1CS.mulVec c.toBlockR1CS.B (liftBlock R z) k = ofBool R ((c.rowOf k).b.eval z) :=
  sum_liftBlock _ z

/-- Over a nontrivial ring of characteristic two, a Boolean block satisfies the R1CS of a circuit
if and only if every position holds the product of its row's two forms. -/
theorem holds_iff_gates [Nontrivial R] (c : ProductCircuit m) (z : Pos m → Bool) :
    c.toBlockR1CS.Holds (liftBlock R z) ↔
      ∀ k, z k = ((c.rowOf k).a.eval z && (c.rowOf k).b.eval z) := by
  refine forall_congr' fun k ↦ ?_
  rw [mulVec_A_liftBlock, mulVec_B_liftBlock, ← ofBool_and]
  exact ⟨fun h ↦ (ofBool_injective h).symm, fun h ↦ by simp only [liftBlock]; rw [← h]⟩

/-- The Boolean block a block of `0`/`1` entries holds: `true` where the entry is `1`. -/
def toBools [DecidableEq R] (z : Pos m → R) : Pos m → Bool := fun k ↦ decide (z k = 1)

omit [CharP R 2] in
/-- A block of `0`/`1` entries is the lift of the Boolean block it holds. -/
theorem eq_liftBlock_toBools [DecidableEq R] [Nontrivial R] {z : Pos m → R}
    (hz : ∀ k : Pos m, BlockR1CS.IsBool (z k)) : z = liftBlock R (toBools z) := by
  funext k
  simp only [liftBlock, toBools, ofBool]
  rcases hz k with h | h <;> simp [h]

end Ring

/-! ## Schedules -/

private theorem foldl_stepF_of_not_mem (L : List (Pos m × Gate m)) (z : Pos m → Bool) (k : Pos m)
    (hk : k ∉ L.map Prod.fst) : L.foldl stepF z k = z k := by
  induction L generalizing z with
  | nil => rfl
  | cons kg rest ih =>
    simp only [List.map_cons, List.mem_cons, not_or] at hk
    rw [List.foldl_cons, ih _ hk.2, stepF, Function.update_of_ne hk.1]

theorem boundedFrom_fresh {avail : Form m} {L : List (Pos m × Gate m)}
    (h : BoundedFrom avail L)
    {k : Pos m} (hk : k ∈ L.map Prod.fst) : avail.getLsbD k = false := by
  induction L generalizing avail with
  | nil => simp at hk
  | cons kg rest ih =>
    obtain ⟨k', g'⟩ := kg
    rw [BoundedFrom] at h
    obtain ⟨-, -, hk', hrest⟩ := h
    simp only [List.map_cons, List.mem_cons] at hk
    rcases hk with rfl | hk
    · exact hk'
    · have := ih hrest hk
      simp only [BitVec.getLsbD_or, Bool.or_eq_false_iff] at this
      exact this.1

theorem mem_of_lookup {L : List (Pos m × Gate m)} {k : Pos m} {g : Gate m}
    (h : L.lookup k = some g) : k ∈ L.map Prod.fst := by
  induction L with
  | nil => simp at h
  | cons kg rest ih =>
    rw [List.lookup_cons] at h
    by_cases hk : k = kg.1
    · simp [hk]
    · have : (k == kg.1) = false := by simpa using hk
      rw [this] at h
      exact List.mem_cons_of_mem _ (ih h)

theorem not_mem_of_lookup_none {L : List (Pos m × Gate m)} {k : Pos m}
    (h : L.lookup k = none) :
    k ∉ L.map Prod.fst := by
  rw [List.lookup_eq_none_iff] at h
  simp only [List.mem_map, not_exists, not_and]
  intro p hp hpk
  have := h p hp
  simp [hpk] at this

theorem lookup_of_mem {avail : Form m} {L : List (Pos m × Gate m)} (h : BoundedFrom avail L)
    {k : Pos m} {g : Gate m} (hm : (k, g) ∈ L) : L.lookup k = some g := by
  induction L generalizing avail with
  | nil => simp at hm
  | cons kg rest ih =>
    obtain ⟨k', g'⟩ := kg
    rw [BoundedFrom] at h
    obtain ⟨-, -, -, hrest⟩ := h
    rw [List.lookup_cons]
    by_cases hkk : k = k'
    · subst hkk
      rcases List.mem_cons.mp hm with he | hm'
      · simp only [Prod.mk.injEq, true_and] at he
        simp [he]
      · have := boundedFrom_fresh hrest (List.mem_map_of_mem (f := Prod.fst) hm')
        simp [Form.var] at this
    · have : (k == k') = false := by simpa using hkk
      rw [this]
      exact ih hrest (by simpa [hkk] using hm)

/-- Off the gate positions, the trace is the block before any gate. -/
theorem traceF_of_not_mem (c : ProductCircuit m) (inp : Pos m → Bool) {k : Pos m}
    (hk : k ∉ c.gates.toList.map Prod.fst) : c.traceF inp k = c.initF inp k :=
  foldl_stepF_of_not_mem _ _ _ hk

/-- Along a bounded schedule, every gate's position holds the product of its forms at the end. -/
private theorem foldl_gate {avail : Form m} {L : List (Pos m × Gate m)} (h : BoundedFrom avail L)
    (z : Pos m → Bool) {k : Pos m} {g : Gate m} (hk : L.lookup k = some g) :
    L.foldl stepF z k = (g.a.eval (L.foldl stepF z) && g.b.eval (L.foldl stepF z)) := by
  induction L generalizing avail z with
  | nil => simp at hk
  | cons kg rest ih =>
    obtain ⟨k', g'⟩ := kg
    rw [BoundedFrom] at h
    obtain ⟨ha, hb, hk', hrest⟩ := h
    rw [List.lookup_cons] at hk
    by_cases hkk : k = k'
    · subst hkk
      simp only [beq_self_eq_true, Option.some.injEq] at hk
      subst hk
      have hnot : k ∉ rest.map Prod.fst := fun hm ↦ by
        have := boundedFrom_fresh hrest hm
        simp [Form.var] at this
      -- positions available before the gate keep their values to the end
      have keep : ∀ j : Pos m, avail.getLsbD j → rest.foldl stepF (stepF z (k, g')) j = z j := by
        intro j hj
        have hjr : j ∉ rest.map Prod.fst := fun hm ↦ by
          have := boundedFrom_fresh hrest hm
          rw [BitVec.getLsbD_or, hj, Bool.true_or] at this
          exact Bool.noConfusion this
        have hjk : j ≠ k := by rintro rfl; rw [hj] at hk'; exact Bool.noConfusion hk'
        rw [foldl_stepF_of_not_mem _ _ _ hjr, stepF, Function.update_of_ne hjk]
      have hstep : stepF z (k, g') k = (g'.a.eval z && g'.b.eval z) := Function.update_self ..
      rw [List.foldl_cons, foldl_stepF_of_not_mem _ _ _ hnot, hstep,
        eval_congr fun j hj ↦ (keep j (sub_getLsbD ha hj)).symm,
        eval_congr (L := g'.b) fun j hj ↦ (keep j (sub_getLsbD hb hj)).symm]
    · have : (k == k') = false := by simpa using hkk
      rw [this] at hk
      exact ih hrest _ hk

/-- A block satisfying a bounded schedule's gates is the schedule's run from any block it agrees
with off the gate positions. -/
private theorem foldl_unique {avail : Form m} {L : List (Pos m × Gate m)} (h : BoundedFrom avail L)
    (z t : Pos m → Bool) (hagree : ∀ j, j ∉ L.map Prod.fst → z j = t j)
    (hgates : ∀ k g, L.lookup k = some g → z k = (g.a.eval z && g.b.eval z)) :
    z = L.foldl stepF t := by
  induction L generalizing avail t with
  | nil => funext j; exact hagree j (by simp)
  | cons kg rest ih =>
    obtain ⟨k, g⟩ := kg
    -- `z` and `t` agree on the available positions
    have hav : ∀ j : Pos m, avail.getLsbD j → z j = t j := fun j hj ↦
      hagree j fun hm ↦ by
        have := boundedFrom_fresh h hm
        rw [hj] at this
        exact Bool.noConfusion this
    rw [BoundedFrom] at h
    obtain ⟨ha, hb, hk, hrest⟩ := h
    refine ih hrest _ (fun j hj ↦ ?_) (fun k' g' hk' ↦ ?_)
    · by_cases hjk : j = k
      · subst hjk
        rw [stepF, Function.update_self, hgates j g (by simp),
          eval_congr fun i hi ↦ hav i (sub_getLsbD ha hi),
          eval_congr (L := g.b) fun i hi ↦ hav i (sub_getLsbD hb hi)]
      · rw [stepF, Function.update_of_ne hjk]
        exact hagree j (by simp [hjk, hj])
    · have hne : k' ≠ k := by
        rintro rfl
        have := boundedFrom_fresh hrest (mem_of_lookup hk')
        simp [Form.var] at this
      apply hgates
      rw [List.lookup_cons]
      have : (k' == k) = false := by simpa using hne
      rw [this]
      exact hk'

/-! ## The trace satisfies the circuit, and is the only block that does -/

/-- The trace holds `1` at the constant position. -/
theorem traceF_cpos {c : ProductCircuit m} (hc : c.Bounded) (inp : Pos m → Bool) :
    c.traceF inp c.cpos = true := by
  have : c.cpos ∉ c.gates.toList.map Prod.fst := fun hm ↦ by
    have := boundedFrom_fresh hc hm
    simp [Form.var] at this
  rw [traceF, foldl_stepF_of_not_mem _ _ _ this]
  simp [initF]

/-- The trace keeps the input at every input position. -/
theorem traceF_input {c : ProductCircuit m} (hc : c.Bounded) (inp : Pos m → Bool) {j : Pos m}
    (hj : c.inputs.getLsbD j = true) (hjc : j ≠ c.cpos) : c.traceF inp j = inp j := by
  have hnm : j ∉ c.gates.toList.map Prod.fst := fun hm ↦ by
    have := boundedFrom_fresh hc hm
    rw [BitVec.getLsbD_or, hj, Bool.true_or] at this
    exact Bool.noConfusion this
  rw [traceF, foldl_stepF_of_not_mem _ _ _ hnm, initF]
  simp [hjc, hj]

/-- The trace of a bounded circuit satisfies every row. -/
theorem trace_holds {c : ProductCircuit m} (hc : c.Bounded) (inp : Pos m → Bool) (k : Pos m) :
    c.traceF inp k = ((c.rowOf k).a.eval (c.traceF inp) && (c.rowOf k).b.eval (c.traceF inp)) := by
  unfold rowOf rowOfList
  split
  · next g hg => exact foldl_gate hc _ hg
  · next hg =>
    have hk := not_mem_of_lookup_none hg
    have h1 := traceF_cpos hc inp
    split_ifs with hkc hin
    · subst hkc; simp [h1]
    · rw [eval_var, eval_var, h1, Bool.and_true]
    · rw [eval_zero, Bool.and_false, traceF, foldl_stepF_of_not_mem _ _ _ hk, initF]
      simp at hin
      simp [hkc, hin]

/-- Completeness of the lowering: over a ring of characteristic two, the trace of a bounded
circuit satisfies its R1CS and holds `1` at the constant position. -/
theorem trace_satisfies {R : Type*} [CommRing R] [CharP R 2]
    {c : ProductCircuit m} (hc : c.Bounded) (inp : Pos m → Bool) :
    c.toBlockR1CS.Holds (liftBlock R (c.traceF inp)) ∧
      liftBlock R (c.traceF inp) c.cpos = 1 := by
  refine ⟨fun k ↦ ?_, ?_⟩
  · rw [mulVec_A_liftBlock, mulVec_B_liftBlock, ← ofBool_and, ← trace_holds hc inp k]
    rfl
  · simp [liftBlock, traceF_cpos hc, ofBool]

/-- Determinism: a Boolean block satisfying every row of a bounded circuit, with `1` at the
constant position, is the trace of its own inputs. -/
theorem holds_eq_trace {c : ProductCircuit m} (hc : c.Bounded) (z : Pos m → Bool)
    (hz : ∀ k, z k = ((c.rowOf k).a.eval z && (c.rowOf k).b.eval z)) (h1 : z c.cpos = true) :
    z = c.traceF z := by
  refine foldl_unique hc z (c.initF z) (fun j hj ↦ ?_) (fun k g hk ↦ ?_)
  · have hl : c.gates.toList.lookup j = none := by
      rw [List.lookup_eq_none_iff]
      intro p hp
      simp only [bne_iff_ne, ne_eq]
      rintro rfl
      exact hj (List.mem_map_of_mem hp)
    have := hz j
    simp only [rowOf, rowOfList, hl] at this
    unfold initF
    split_ifs at this with hjc hin
    · subst hjc; simp [h1]
    · simp [hjc, hin]
    · rw [eval_zero, Bool.and_false] at this
      simp [hjc, this]
  · have := hz k
    simp only [rowOf, rowOfList, hk] at this
    exact this

/-- In a bounded circuit, a block satisfying every row satisfies every recorded gate. -/
theorem gates_of_rows {c : ProductCircuit m} (hc : c.Bounded) (z : Pos m → Bool)
    (hz : ∀ k, z k = ((c.rowOf k).a.eval z && (c.rowOf k).b.eval z)) :
    ∀ kg ∈ c.gates, z kg.1 = (kg.2.a.eval z && kg.2.b.eval z) := by
  intro kg hkg
  have hl := lookup_of_mem hc (Array.mem_toList_iff.mpr hkg)
  have := hz kg.1
  simp only [rowOf, rowOfList, hl] at this
  exact this

/-- Soundness of the lowering: over a nontrivial ring of characteristic two, a Boolean block
satisfying the R1CS of a bounded circuit satisfies every recorded gate. -/
theorem gates_of_holds {R : Type*} [CommRing R] [CharP R 2] [Nontrivial R]
    {c : ProductCircuit m} (hc : c.Bounded) (z : Pos m → Bool)
    (hz : c.toBlockR1CS.Holds (liftBlock R z)) :
    ∀ kg ∈ c.gates, z kg.1 = (kg.2.a.eval z && kg.2.b.eval z) :=
  gates_of_rows hc z ((holds_iff_gates c z).mp hz)

/-- Determinism for a block of `0`/`1` entries: if it satisfies the R1CS of a bounded circuit and
holds `1` at the constant, it is the lift of the trace of its own inputs. -/
theorem eq_trace_of_holds_isBool {R : Type*} [CommRing R] [CharP R 2] [Nontrivial R]
    [DecidableEq R] {c : ProductCircuit m} (hc : c.Bounded) {z : Pos m → R}
    (hb : ∀ k : Pos m, BlockR1CS.IsBool (z k)) (hz : c.toBlockR1CS.Holds z)
    (h1 : z c.cpos = 1) : z = liftBlock R (c.traceF (toBools z)) := by
  have hz' := eq_liftBlock_toBools hb ▸ hz
  conv_lhs => rw [eq_liftBlock_toBools hb]
  rw [← holds_eq_trace hc _ ((holds_iff_gates c _).mp hz') (by simp [toBools, h1])]

/-- The executable trace computes the mathematical one. -/
theorem trace_getLsbD (c : ProductCircuit m) (inp : Form m) :
    (fun j : Pos m ↦ (c.trace inp).getLsbD j) = c.traceF (fun j ↦ inp.getLsbD j) := by
  rw [trace, traceF, ← Array.foldl_toList]
  have hinit : (fun j : Pos m ↦ (c.initB inp).getLsbD j) = c.initF (fun j ↦ inp.getLsbD j) := by
    funext j
    simp [initB, initF, Form.var, Bool.or_comm, Fin.val_inj]
  rw [← hinit]
  generalize c.initB inp = z0
  induction c.gates.toList generalizing z0 with
  | nil => rfl
  | cons kg rest ih =>
    rw [List.foldl_cons, List.foldl_cons, ih]
    congr 1
    funext j
    simp only [stepB, stepF, setBitB, evalB_eq_eval]
    by_cases hj : j = kg.1
    · subst hj
      split <;> simp_all [Form.var]
    · rw [Function.update_of_ne hj]
      have : (j : ℕ) ≠ kg.1 := fun h ↦ hj (Fin.ext h)
      split <;> simp [Form.var, this]

/-! ## Assembling bounded schedules -/

/-- The available positions after a schedule. -/
def availAfter (a : Form m) (L : List (Pos m × Gate m)) : Form m :=
  L.foldl (fun a kg ↦ a ||| Form.var kg.1) a

theorem boundedFrom_append (a : Form m) (l₁ l₂ : List (Pos m × Gate m)) :
    BoundedFrom a (l₁ ++ l₂) ↔ BoundedFrom a l₁ ∧ BoundedFrom (availAfter a l₁) l₂ := by
  induction l₁ generalizing a with
  | nil => simp [BoundedFrom, availAfter]
  | cons kg rest ih =>
    obtain ⟨k, g⟩ := kg
    simp only [List.cons_append, BoundedFrom, ih, availAfter, List.foldl_cons]
    tauto

theorem availAfter_append_singleton (a : Form m) (l : List (Pos m × Gate m))
    (kg : Pos m × Gate m) : availAfter a (l ++ [kg]) = availAfter a l ||| Form.var kg.1 := by
  simp [availAfter, List.foldl_append]

/-- Gates that read only `a`, at distinct positions fresh for `a`, are bounded from `a`. -/
theorem boundedFrom_of_nodup (L : List (Pos m × Gate m)) :
    ∀ a : Form m, (∀ kg ∈ L, Sub kg.2.a a ∧ Sub kg.2.b a) → (∀ kg ∈ L, a.getLsbD kg.1 = false) →
      (L.map Prod.fst).Nodup → BoundedFrom a L := by
  induction L with
  | nil => intros; trivial
  | cons kg rest ih =>
    intro a hsub hfresh hnd
    obtain ⟨k, g⟩ := kg
    rw [List.map_cons, List.nodup_cons] at hnd
    rw [BoundedFrom]
    refine ⟨(hsub _ List.mem_cons_self).1, (hsub _ List.mem_cons_self).2,
      hfresh _ List.mem_cons_self, ih _ (fun kg' h ↦ ?_) (fun kg' h ↦ ?_) hnd.2⟩
    · exact ⟨(hsub kg' (List.mem_cons_of_mem _ h)).1.or_right _,
        (hsub kg' (List.mem_cons_of_mem _ h)).2.or_right _⟩
    · rw [BitVec.getLsbD_or, hfresh kg' (List.mem_cons_of_mem _ h), getLsbD_var, Bool.false_or,
        decide_eq_false_iff_not]
      intro he
      have hm := List.mem_map_of_mem (f := Prod.fst) h
      rw [← Fin.ext he] at hm
      exact hnd.1 hm

end ProductCircuit

end FR

end G6_FRBlake2sCircuit

section G6_FRBlake2sWords

-- Copied from `submissions/spartan-srom/lean/SpartanSromBlake2sWords.lean` (this repository, branch
-- `v4/flock-recursive` at `783328c`), renamed to the namespace `FR`; no other change. That file was
-- ported from v3 `spartan-chain` (submissions repo, local `main` at `1f59b38`) to the v4 contract.

/-!
# Building product-gate circuits, and the 32-bit word gadgets

Provenance: copied from leanerVM (Apache-2.0, github.com/Verified-zkEVM/leanerVM, `main` at
`95957214d42b6d5e21d7066f760e5ec256514cf8`; identical at `e715c49` and on the branch
`docs/protocol-headline-theorems` at `532ebb4`): `LeanerVM/Protocol/ToArkLib/Flock/Builder.lean`
and `LeanerVM/Protocol/ToArkLib/Flock/Words.lean`, concatenated. Modified (Apache-2.0 §4(b)):
the module-system annotations are dropped, the namespace is `FR`, and the `private`
lemmas of the adders are public (the walk's simulation, `FRBlake2sWalk.lean`, uses
them). No statement and no definition is changed.

**The builder.** A gadget is a program in `Builder m`, a state monad over the next free position
and the gates recorded so far. Its one effect, `mul a b`, records the gate `(a, b)` at the next
position and returns that position's form. Linear operations need no effect: they are XORs of
forms. Two contracts compose through `bind`: `Sound w mb P` (whenever the gates a run of `mb`
records hold at the block `w`, its result satisfies `P`) and `Ok S n₀ mb k P` (run from a good
state, `mb` keeps it good, records exactly `k` gates, and returns a result satisfying `P`).

**Words.** A word is 32 forms, bit `i` at index `i`. `Den w x u` says the word `x` denotes the
value `u` on the block `w`. XOR, rotation, literals (`litW`, through the constant position) and
input words (`inW`) are linear: no gate. The ripple-carry adder `addW` records 31 gates, the fused
three-operand adder `add3W` 61; `sound_addW`, `sound_add3W` state their specifications against
`UInt32` arithmetic, `ok_addW`, `ok_add3W` their gate counts.
-/

namespace FR

namespace ProductCircuit

variable {m : ℕ}

/-! ## The builder -/

/-- The builder's state: the next free position and the gates recorded so far. -/
structure BuildState (m : ℕ) where
  /-- The next gate position. -/
  next : ℕ
  /-- The gates recorded so far, in evaluation order. -/
  gates : Array (Pos m × Gate m)

/-- A circuit-building program. -/
abbrev Builder (m : ℕ) := StateM (BuildState m)

/-- Record the gate `(a, b)` at the next position and return that position's form. -/
def mul (a b : Form m) : Builder m (Form m) :=
  modifyGet fun s ↦
    (Form.var (pos s.next), { next := s.next + 1, gates := s.gates.push (pos s.next, ⟨a, b⟩) })

/-- One `mul`: the gate at `next`, and `next` advanced. -/
theorem run_mul (a b : Form m) (σ : BuildState m) :
    (mul a b).run σ =
      (Form.var (pos σ.next), { next := σ.next + 1, gates := σ.gates.push (pos σ.next, ⟨a, b⟩) }) :=
  rfl

theorem run_bind' {α β : Type} (mb : Builder m α) (f : α → Builder m β) (σ : BuildState m) :
    (mb >>= f).run σ = (f (mb.run σ).1).run (mb.run σ).2 := rfl

theorem run_map' {α β : Type} (mb : Builder m α) (f : α → β) (σ : BuildState m) :
    (f <$> mb).run σ = (f (mb.run σ).1, (mb.run σ).2) := rfl

/-! ## Soundness -/

/-- Every gate recorded in the state holds at `z`. -/
def GatesHold (σ : BuildState m) (z : Pos m → Bool) : Prop :=
  ∀ kg ∈ σ.gates, z kg.1 = (kg.2.a.eval z && kg.2.b.eval z)

/-- A program only appends gates. -/
def Grows {α : Type} (mb : Builder m α) : Prop :=
  ∀ σ : BuildState m, ∀ kg ∈ σ.gates, kg ∈ (mb.run σ).2.gates

/-- Whenever the gates of a run of `mb` hold at `w`, its result satisfies `P`. -/
def Sound {α : Type} (w : Pos m → Bool) (mb : Builder m α) (P : α → Prop) : Prop :=
  ∀ σ : BuildState m, GatesHold (mb.run σ).2 w → P (mb.run σ).1

theorem grows_bind {α β : Type} {mb : Builder m α} {f : α → Builder m β} (hm : Grows mb)
    (hf : ∀ a, Grows (f a)) : Grows (mb >>= f) := by
  intro σ kg h
  rw [StateT.run_bind]
  exact hf _ _ _ (hm σ kg h)

theorem grows_pure {α : Type} (a : α) : Grows (pure a : Builder m α) := fun _ _ h ↦ h

theorem grows_map {α β : Type} {mb : Builder m α} (f : α → β) (hm : Grows mb) :
    Grows (f <$> mb) := fun σ kg h ↦ by rw [run_map']; exact hm σ kg h

theorem grows_mul (a b : Form m) : Grows (mul a b) := fun σ kg h ↦ by
  rw [run_mul]; exact Array.mem_push_of_mem _ h

theorem sound_bind {α β : Type} {w : Pos m → Bool} {mb : Builder m α} {f : α → Builder m β}
    {P : α → Prop} {Q : β → Prop} (hm : Sound w mb P) (hg : ∀ a, Grows (f a))
    (hf : ∀ a, P a → Sound w (f a) Q) : Sound w (mb >>= f) Q := by
  intro σ h
  rw [StateT.run_bind] at h ⊢
  exact hf _ (hm σ fun kg hkg ↦ h kg (hg _ _ kg hkg)) _ h

theorem sound_pure {α : Type} {w : Pos m → Bool} {a : α} {P : α → Prop} (h : P a) :
    Sound w (pure a : Builder m α) P := fun _ _ ↦ h

theorem sound_map {α β : Type} {w : Pos m → Bool} {mb : Builder m α} {f : α → β}
    {P : α → Prop} {Q : β → Prop} (hm : Sound w mb P) (hf : ∀ a, P a → Q (f a)) :
    Sound w (f <$> mb) Q := fun σ h ↦ by
  rw [run_map'] at h ⊢
  exact hf _ (hm σ h)

/-- The gate `mul` records holds: its result evaluates to the product of its forms. -/
theorem sound_mul {w : Pos m → Bool} (a b : Form m) :
    Sound w (mul a b) (fun o ↦ o.eval w = (a.eval w && b.eval w)) := fun σ h ↦ by
  rw [run_mul] at h ⊢
  rw [eval_var]
  exact h _ (Array.mem_push_self ..)

/-! ## Well-formedness -/

/-- Where a build starts: the positions available before any gate (the inputs and the
constant) and the first gate position, past every available one. -/
structure Start (m : ℕ) where
  /-- The positions available before any gate. -/
  avail : Form m
  /-- The first gate position. -/
  base : ℕ
  /-- No position from `base` on is available at the start. -/
  fresh : ∀ j, base ≤ j → avail.getLsbD j = false

namespace Start

variable (S : Start m)

/-- Position `j` is available once the gates below `n` are recorded. -/
def AvailAt (n j : ℕ) : Bool := S.avail.getLsbD j || (decide (S.base ≤ j) && decide (j < n))

/-- `L` mentions only positions available at `n`. -/
def SubN (L : Form m) (n : ℕ) : Prop := ∀ j, L.getLsbD j = true → S.AvailAt n j = true

/-- A good state: `next` is past the start, the recorded gates are bounded from the start
availability, and after them exactly the start availability and `[base, next)` are
available. -/
structure Inv (σ : BuildState m) : Prop where
  /-- Gate positions start at `base`. -/
  le : S.base ≤ σ.next
  /-- The recorded gates are bounded from the start availability. -/
  bounded : BoundedFrom S.avail σ.gates.toList
  /-- After them, exactly the start availability and `[base, next)` are available. -/
  avail : ∀ j, (availAfter S.avail σ.gates.toList).getLsbD j = S.AvailAt σ.next j

/-- Run from a good state at or after `n₀` with room for `k` gates, `mb` keeps the state good,
records exactly `k` gates, and returns a result satisfying `P` at the new `next`. -/
def Ok {α : Type} (n₀ : ℕ) (mb : Builder m α) (k : ℕ) (P : α → ℕ → Prop) : Prop :=
  ∀ σ : BuildState m, S.Inv σ → n₀ ≤ σ.next → σ.next + k ≤ 2 ^ m →
    S.Inv (mb.run σ).2 ∧ (mb.run σ).2.next = σ.next + k ∧ P (mb.run σ).1 (mb.run σ).2.next

variable {S}

theorem availAt_iff (n j : ℕ) :
    S.AvailAt n j = true ↔ S.avail.getLsbD j = true ∨ (S.base ≤ j ∧ j < n) := by
  simp [AvailAt]

theorem SubN.mono {L : Form m} {n n' : ℕ} (h : S.SubN L n) (hn : n ≤ n') : S.SubN L n' := by
  intro j hj
  rcases (availAt_iff n j).mp (h j hj) with h' | h'
  · exact (availAt_iff n' j).mpr (Or.inl h')
  · exact (availAt_iff n' j).mpr (Or.inr ⟨h'.1, by omega⟩)

theorem SubN.xor {L M : Form m} {n : ℕ} (hL : S.SubN L n) (hM : S.SubN M n) :
    S.SubN (L ^^^ M) n := by
  intro j hj
  rw [BitVec.getLsbD_xor] at hj
  cases hl : L.getLsbD j
  · rw [hl, Bool.false_xor] at hj; exact hM j hj
  · exact hL j hl

theorem subN_zero (n : ℕ) : S.SubN 0 n := by
  intro j hj
  simp at hj

theorem subN_var {k : Pos m} {n : ℕ} (h : S.AvailAt n k = true) : S.SubN (Form.var k) n := by
  intro j hj
  rw [getLsbD_var, decide_eq_true_eq] at hj
  rwa [← hj]

/-- A start position is available at every stage. -/
theorem subN_start {k : Pos m} (h : S.avail.getLsbD k = true) (n : ℕ) :
    S.SubN (Form.var k) n :=
  subN_var ((availAt_iff _ _).mpr (Or.inl h))

theorem sub_of_subN {L a : Form m} {n : ℕ} (ha : ∀ j, a.getLsbD j = S.AvailAt n j)
    (h : S.SubN L n) : Sub L a :=
  sub_iff.mpr fun j hj ↦ (ha j).trans (h j hj)

theorem inv_init : S.Inv ⟨S.base, #[]⟩ where
  le := le_rfl
  bounded := trivial
  avail j := by simp [availAfter, AvailAt]

/-- Recording one gate at `next`, with forms available at `next`, keeps the state good. -/
theorem inv_push {σ : BuildState m} (hσ : S.Inv σ) (hlt : σ.next < 2 ^ m) {a b : Form m}
    (ha : S.SubN a σ.next) (hb : S.SubN b σ.next) :
    S.Inv { next := σ.next + 1, gates := σ.gates.push (pos σ.next, ⟨a, b⟩) } where
  le := by dsimp only; have := hσ.le; omega
  bounded := by
    rw [Array.toList_push, boundedFrom_append]
    refine ⟨hσ.bounded, sub_of_subN hσ.avail ha, sub_of_subN hσ.avail hb, ?_, trivial⟩
    rw [hσ.avail, pos_val hlt, Bool.eq_false_iff, ne_eq, availAt_iff]
    have := hσ.le
    have := S.fresh σ.next hσ.le
    simp only [this, Bool.false_eq_true, false_or]
    omega
  avail j := by
    rw [Array.toList_push, availAfter_append_singleton, BitVec.getLsbD_or, hσ.avail,
      getLsbD_var, pos_val hlt, Bool.eq_iff_iff, Bool.or_eq_true, availAt_iff, availAt_iff,
      decide_eq_true_eq]
    have := hσ.le
    dsimp only
    constructor
    · rintro ((h | h) | h) <;> [exact Or.inl h; exact Or.inr ⟨h.1, by omega⟩;
        exact Or.inr ⟨by omega, by omega⟩]
    · rintro (h | h)
      · exact Or.inl (Or.inl h)
      · by_cases hj : j < σ.next
        · exact Or.inl (Or.inr ⟨h.1, hj⟩)
        · exact Or.inr (by omega)

/-- The gate count of a contract, up to equality. -/
theorem Ok.cast {α : Type} {n₀ k k' : ℕ} {mb : Builder m α} {P : α → ℕ → Prop}
    (h : S.Ok n₀ mb k P) (hk : k = k') : S.Ok n₀ mb k' P := hk ▸ h

theorem ok_bind {α β : Type} {n₀ k₁ k : ℕ} {mb : Builder m α} {f : α → Builder m β}
    {P : α → ℕ → Prop} {Q : β → ℕ → Prop} (hm : S.Ok n₀ mb k₁ P) (hk : k₁ ≤ k)
    (hf : ∀ a n, n₀ ≤ n → P a n → S.Ok n (f a) (k - k₁) Q) : S.Ok n₀ (mb >>= f) k Q := by
  intro σ hσ hn hle
  obtain ⟨h1, h2, h3⟩ := hm σ hσ hn (by omega)
  rw [run_bind']
  obtain ⟨h1', h2', h3'⟩ := hf _ _ (by omega) h3 _ h1 le_rfl (by omega)
  exact ⟨h1', by omega, h3'⟩

theorem ok_pure {α : Type} {n₀ k : ℕ} {a : α} {P : α → ℕ → Prop} (h : ∀ n, n₀ ≤ n → P a n)
    (hk : k = 0) : S.Ok n₀ (pure a : Builder m α) k P := by
  intro σ hσ hn _
  subst hk
  exact ⟨hσ, rfl, h _ hn⟩

theorem ok_map {α β : Type} {n₀ k : ℕ} {mb : Builder m α} {f : α → β} {P : α → ℕ → Prop}
    {Q : β → ℕ → Prop} (hm : S.Ok n₀ mb k P) (hf : ∀ a n, n₀ ≤ n → P a n → Q (f a) n) :
    S.Ok n₀ (f <$> mb) k Q := by
  intro σ hσ hn hle
  obtain ⟨h1, h2, h3⟩ := hm σ hσ hn hle
  rw [run_map']
  exact ⟨h1, h2, hf _ (mb.run σ).2.next (by omega) h3⟩

/-- `mul` records one gate, and its result is available after it. -/
theorem ok_mul {n₀ : ℕ} {a b : Form m} (ha : S.SubN a n₀) (hb : S.SubN b n₀) :
    S.Ok n₀ (mul a b) 1 (fun o n ↦ S.SubN o n) := by
  intro σ hσ hn hle
  rw [run_mul]
  refine ⟨inv_push hσ (by omega) (ha.mono hn) (hb.mono hn), rfl, subN_var ?_⟩
  rw [pos_val (by omega), availAt_iff]
  have := hσ.le
  dsimp only
  omega

/-- The schedule of a good state is bounded from the start availability. -/
theorem Inv.boundedFrom {σ : BuildState m} (h : S.Inv σ) : BoundedFrom S.avail σ.gates.toList :=
  h.bounded

/-- A circuit whose gates are those of a run from `base`, for a program with the contract, and
whose inputs and constant are the start availability, is bounded. -/
theorem bounded_of_ok {α : Type} {c : ProductCircuit m} {mb : Builder m α} {k : ℕ}
    {P : α → ℕ → Prop} (hav : c.inputs ||| Form.var c.cpos = S.avail) (h : S.Ok S.base mb k P)
    (hk : S.base + k ≤ 2 ^ m) (hg : c.gates = (mb.run ⟨S.base, #[]⟩).2.gates) : c.Bounded := by
  rw [Bounded, hav, hg]
  exact (h _ inv_init le_rfl hk).1.bounded

end Start

end ProductCircuit

namespace ProductCircuit

variable {m : ℕ}

/-! ## Words -/

/-- A 32-bit word of forms, bit `i` at index `i`. -/
abbrev Word (m : ℕ) := Vector (Form m) 32

/-- Bitwise XOR of words. -/
def xorW (x y : Word m) : Word m := Vector.ofFn fun i ↦ x[i] ^^^ y[i]

/-- Rotate right by `n`: bit `i` is bit `(i + n) mod 32`. -/
def rotrW (w : Word m) (n : ℕ) : Word m :=
  Vector.ofFn fun i ↦ w[(i.val + n) % 32]'(Nat.mod_lt _ (by decide))

/-- A literal word, through the constant position `cpos`: bit `i` is `cpos` if set, else `0`. -/
def litW (cpos : Pos m) (c : UInt32) : Word m :=
  Vector.ofFn fun i ↦ if c.toNat.testBit i then Form.var cpos else 0

/-- The input word at the positions `b, …, b + 31`, reduced modulo the block size (`subW_inW`
requires them in range). -/
def inW (b : ℕ) : Word m := Vector.ofFn fun i ↦ Form.var (pos (b + i))

/-- The carries of `x + y` from bit `31 - n` with carry `c`: carry `i + 1` is `c + g` with the gate
`g = (x_i + c)(y_i + c)`. Returns the carries `c_{31-n}, …, c_31`. -/
def addCarries (x y : Word m) : (n : ℕ) → Form m → Builder m (List (Form m))
  | 0, c => pure [c]
  | n + 1, c => do
    let i := 30 - n
    let g ← mul (x[i]'(by omega) ^^^ c) (y[i]'(by omega) ^^^ c)
    let rest ← addCarries x y n (c ^^^ g)
    pure (c :: rest)

/-- The sum of a ripple: bit `i` is `p_i + q_i + c_i`. -/
def sumW (p q : Word m) (cs : List (Form m)) : Word m :=
  Vector.ofFn fun i ↦ p[i] ^^^ q[i] ^^^ cs.getD i 0

/-- `x + y`, one gate per carry into bits `1, …, 31`. -/
def addW (x y : Word m) : Builder m (Word m) := sumW x y <$> addCarries x y 31 0

/-- The majority gates of `add3W` from bit `31 - n`: `g_i = (x_i + z_i)(y_i + z_i)`, returning the
majorities `g_i + z_i`. -/
def majorities (x y z : Word m) : (n : ℕ) → Builder m (List (Form m))
  | 0 => pure []
  | n + 1 => do
    let i := 30 - n
    let g ← mul (x[i]'(by omega) ^^^ z[i]'(by omega)) (y[i]'(by omega) ^^^ z[i]'(by omega))
    let rest ← majorities x y z n
    pure ((g ^^^ z[i]'(by omega)) :: rest)

/-- The ripple of `add3W` from bit `31 - n` with carry `c`: a gate for each of bits `1, …, 30`;
bit `0` of `q` is `0`, so bit `0` carries nothing and needs none. -/
def rippleCarries (p q : Word m) : (n : ℕ) → Form m → Builder m (List (Form m))
  | 0, c => pure [c]
  | n + 1, c => do
    let i := 30 - n
    if 1 ≤ i then
      let g ← mul (p[i]'(by omega) ^^^ c) (q[i]'(by omega) ^^^ c)
      let rest ← rippleCarries p q n (c ^^^ g)
      pure (c :: rest)
    else
      let rest ← rippleCarries p q n c
      pure (c :: rest)

/-- The XOR word `x ⊕ y ⊕ z`. -/
def xor3W (x y z : Word m) : Word m := Vector.ofFn fun i ↦ x[i] ^^^ y[i] ^^^ z[i]

/-- The majorities shifted up by one: bit `0` is `0`, bit `i ≥ 1` is majority `i - 1`. -/
def shiftW (ms : List (Form m)) : Word m :=
  Vector.ofFn fun i ↦ if i.val = 0 then 0 else ms.getD (i.val - 1) 0

/-- `x + y + z`: 31 majority gates, then 30 ripple gates adding `xor3W` and `shiftW`. -/
def add3W (x y z : Word m) : Builder m (Word m) :=
  majorities x y z 31 >>= fun ms ↦
    sumW (xor3W x y z) (shiftW ms) <$> rippleCarries (xor3W x y z) (shiftW ms) 31 0

/-! ## Denotation -/

/-- The word `x` denotes the value `u` on the block `w`. -/
def Den (w : Pos m → Bool) (x : Word m) (u : UInt32) : Prop :=
  ∀ i : Fin 32, x[i].eval w = u.toBitVec.getLsbD i

/-- A denotation, transported along an equality of values. -/
theorem den_congr {w : Pos m → Bool} {x : Word m} {u u' : UInt32} (h : Den w x u)
    (e : u = u') : Den w x u' := e ▸ h

/-- A word denotes at most one value. -/
theorem den_unique {w : Pos m → Bool} {x : Word m} {u u' : UInt32} (h : Den w x u)
    (h' : Den w x u') : u = u' := by
  apply UInt32.toBitVec_inj.mp
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  exact (h ⟨i, hi⟩).symm.trans (h' ⟨i, hi⟩)

theorem den_xorW {w : Pos m → Bool} {x y : Word m} {xu yu : UInt32} (hx : Den w x xu)
    (hy : Den w y yu) : Den w (xorW x y) (xu ^^^ yu) := by
  intro i
  rw [xorW, Fin.getElem_fin, Vector.getElem_ofFn, eval_xor, hx, hy]
  simp

theorem den_rotrW {w : Pos m → Bool} {x : Word m} {xu : UInt32} (hx : Den w x xu) {n : ℕ}
    (hn : n < 32) : Den w (rotrW x n) ⟨xu.toBitVec.rotateRight n⟩ := by
  intro i
  rw [rotrW, Fin.getElem_fin, Vector.getElem_ofFn]
  have := hx ⟨(i.val + n) % 32, Nat.mod_lt _ (by decide)⟩
  simp only [Fin.getElem_fin] at this
  rw [this, BitVec.getLsbD_rotateRight, Nat.mod_eq_of_lt hn]
  split_ifs with h
  · rw [show ((i : ℕ) + n) % 32 = n + i by omega]
  · rw [show ((i : ℕ) + n) % 32 = i - (32 - n) by omega]
    simp only [i.isLt, decide_true, Bool.true_and]

theorem den_litW {w : Pos m → Bool} {cpos : Pos m} (hc : w cpos = true) (u : UInt32) :
    Den w (litW cpos u) u := by
  intro i
  rw [litW, Fin.getElem_fin, Vector.getElem_ofFn]
  split_ifs with h
  · rw [eval_var, hc]; exact h.symm
  · rw [eval_zero]
    exact (Bool.eq_false_iff.mpr h).symm

/-- An input word denotes the value whose bits the block holds at its positions. -/
theorem den_inW {w : Pos m → Bool} {b : ℕ} {u : UInt32}
    (h : ∀ i : Fin 32, w (pos (b + i)) = u.toBitVec.getLsbD i) : Den w (inW b) u := by
  intro i
  rw [inW, Fin.getElem_fin, Vector.getElem_ofFn, eval_var]
  exact h i

/-- The word a block holds at the positions `b, …, b + 31`, low bit first. -/
def readWord (w : Pos m → Bool) (b : ℕ) : UInt32 := ⟨BitVec.ofFnLE fun i : Fin 32 ↦ w (pos (b + i))⟩

/-- The input word at `b` denotes the word the block holds there. -/
theorem den_readWord (w : Pos m → Bool) (b : ℕ) : Den w (inW b) (readWord w b) :=
  den_inW fun i ↦ by simp [readWord]

/-! ## The ripple adder -/

theorem run_addCarries_zero (x y : Word m) (c : Form m) (σ : BuildState m) :
    (addCarries x y 0 c).run σ = ([c], σ) := rfl

theorem run_addCarries_succ (x y : Word m) (n : ℕ) (c : Form m) (σ : BuildState m) :
    (addCarries x y (n + 1) c).run σ =
      let r := (addCarries x y n (c ^^^ Form.var (pos σ.next))).run
        { next := σ.next + 1,
          gates := σ.gates.push
            (pos σ.next, ⟨x[30 - n]'(by omega) ^^^ c, y[30 - n]'(by omega) ^^^ c⟩) }
      (c :: r.1, r.2) := rfl

theorem addCarries_grows (x y : Word m) (n : ℕ) (c : Form m) :
    Grows (addCarries x y n c) := by
  induction n generalizing c with
  | zero => intro σ kg h; rw [run_addCarries_zero]; exact h
  | succ n ih =>
    intro σ kg h
    rw [run_addCarries_succ]
    exact ih _ _ kg (Array.mem_push_of_mem _ h)

/-- The carry recursion: from bit `31 - n` with the right carry, the carry forms evaluate to the
carries of `xv + yv`, if the recorded gates hold. -/
theorem addCarries_spec (x y : Word m) (z : Pos m → Bool) (xv yv : BitVec 32)
    (hx : ∀ i : Fin 32, x[i].eval z = xv.getLsbD i) (hy : ∀ i : Fin 32, y[i].eval z = yv.getLsbD i)
    (n : ℕ) (c : Form m) (σ : BuildState m) (hn : n ≤ 31)
    (hc : c.eval z = BitVec.carry (31 - n) xv yv false)
    (hz : GatesHold ((addCarries x y n c).run σ).2 z) (j : ℕ) (hj : j ≤ n) :
    (((addCarries x y n c).run σ).1.getD j 0).eval z = BitVec.carry (31 - n + j) xv yv false := by
  induction n generalizing c σ j with
  | zero =>
    obtain rfl : j = 0 := by omega
    rw [run_addCarries_zero]
    exact hc
  | succ n ih =>
    rw [run_addCarries_succ] at hz ⊢
    have hg := hz _ (addCarries_grows x y n _ _ _ (Array.mem_push_self ..))
    have hxi := hx ⟨30 - n, by omega⟩
    have hyi := hy ⟨30 - n, by omega⟩
    simp only [Fin.getElem_fin] at hxi hyi
    rw [eval_xor, eval_xor, hxi, hyi, hc, show 31 - (n + 1) = 30 - n by omega] at hg
    have hc' : (c ^^^ Form.var (pos σ.next)).eval z = BitVec.carry (31 - n) xv yv false := by
      rw [eval_xor, eval_var, hg, hc, show 31 - n = (30 - n) + 1 by omega, BitVec.carry_succ,
        show 31 - (n + 1) = 30 - n by omega]
      cases xv.getLsbD (30 - n) <;> cases yv.getLsbD (30 - n) <;>
        cases BitVec.carry (30 - n) xv yv false <;> rfl
    rcases j with _ | j
    · exact hc
    · rw [List.getD_cons_succ, ih _ _ (by omega) hc' hz j (by omega),
        show 31 - n + j = 31 - (n + 1) + (j + 1) by omega]

theorem run_addW (x y : Word m) (σ : BuildState m) :
    (addW x y).run σ =
      (sumW x y ((addCarries x y 31 0).run σ).1, ((addCarries x y 31 0).run σ).2) := by
  rw [addW, StateT.run_map]
  rfl

theorem grows_addW (x y : Word m) : Grows (addW x y) := by
  intro σ kg h
  rw [run_addW]
  dsimp only
  exact addCarries_grows x y 31 0 σ kg h

/-- The ripple adder is sound: if its gates hold, its output denotes the sum of its inputs. -/
theorem sound_addW {w : Pos m → Bool} {x y : Word m} {xu yu : UInt32} (hx : Den w x xu)
    (hy : Den w y yu) : Sound w (addW x y) (fun o ↦ Den w o (xu + yu)) := by
  intro σ hz i
  rw [run_addW] at hz ⊢
  dsimp only at hz ⊢
  have h0 : (0 : Form m).eval w = BitVec.carry (31 - 31) xu.toBitVec yu.toBitVec false := by
    rw [eval_zero, Nat.sub_self, BitVec.carry_zero]
  have hcarry := addCarries_spec x y w _ _ hx hy 31 0 σ le_rfl h0 hz i (by omega)
  rw [Nat.sub_self, Nat.zero_add] at hcarry
  rw [sumW, Fin.getElem_fin, Vector.getElem_ofFn, eval_xor, eval_xor, hcarry, UInt32.toBitVec_add,
    BitVec.getLsbD_add i.isLt, ← hx, ← hy, Bool.xor_assoc]

/-! ## The fused three-operand adder -/

/-- Carry-save over the naturals: `a + b + c = (a ⊕ b ⊕ c) + 2 maj(a, b, c)`. -/
theorem nat_carry_save (k : ℕ) (a b c : ℕ) (ha : a < 2 ^ k) (hb : b < 2 ^ k)
    (hc : c < 2 ^ k) : a + b + c = (a ^^^ b ^^^ c) + 2 * (a &&& b ||| a &&& c ||| b &&& c) := by
  induction k generalizing a b c with
  | zero => simp_all
  | succ k ih =>
    obtain ⟨a0, a', rfl⟩ : ∃ a0 a', a = Nat.bit a0 a' :=
      ⟨_, _, (Nat.bit_testBit_zero_shiftRight_one a).symm⟩
    obtain ⟨b0, b', rfl⟩ : ∃ b0 b', b = Nat.bit b0 b' :=
      ⟨_, _, (Nat.bit_testBit_zero_shiftRight_one b).symm⟩
    obtain ⟨c0, c', rfl⟩ : ∃ c0 c', c = Nat.bit c0 c' :=
      ⟨_, _, (Nat.bit_testBit_zero_shiftRight_one c).symm⟩
    simp only [Nat.bit_lt_two_pow_succ_iff] at ha hb hc
    have := ih a' b' c' ha hb hc
    simp only [Nat.xor_bit, Nat.land_bit, Nat.lor_bit]
    simp only [Nat.bit_val]
    cases a0 <;> cases b0 <;> cases c0 <;> simp <;> omega

/-- Carry-save on words: `x + y + z = (x ⊕ y ⊕ z) + (maj(x, y, z) ≪ 1)`. -/
theorem carry_save (x y z : BitVec 32) :
    x + y + z = (x ^^^ y ^^^ z) + ((x &&& y ||| x &&& z ||| y &&& z) <<< 1) := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_add, BitVec.toNat_xor, BitVec.toNat_or, BitVec.toNat_and,
    BitVec.toNat_shiftLeft, Nat.shiftLeft_eq, pow_one]
  rw [Nat.mod_add_mod, nat_carry_save 32 _ _ _ x.isLt y.isLt z.isLt, Nat.mul_comm 2,
    Nat.add_mod_mod]

theorem run_majorities_zero (x y z : Word m) (σ : BuildState m) :
    (majorities x y z 0).run σ = ([], σ) := rfl

theorem run_majorities_succ (x y z : Word m) (n : ℕ) (σ : BuildState m) :
    (majorities x y z (n + 1)).run σ =
      let r := (majorities x y z n).run
        { next := σ.next + 1,
          gates := σ.gates.push (pos σ.next,
            ⟨x[30 - n]'(by omega) ^^^ z[30 - n]'(by omega),
              y[30 - n]'(by omega) ^^^ z[30 - n]'(by omega)⟩) }
      ((Form.var (pos σ.next) ^^^ z[30 - n]'(by omega)) :: r.1, r.2) := rfl

theorem majorities_grows (x y z : Word m) (n : ℕ) : Grows (majorities x y z n) := by
  induction n with
  | zero => intro σ kg h; rw [run_majorities_zero]; exact h
  | succ n ih =>
    intro σ kg h
    rw [run_majorities_succ]
    exact ih _ kg (Array.mem_push_of_mem _ h)

/-- The majority gates: from bit `31 - n`, entry `j` evaluates to the majority of bit
`31 - n + j`, if the recorded gates hold. -/
theorem majorities_spec (x y z : Word m) (w : Pos m → Bool) (xv yv zv : BitVec 32)
    (hx : ∀ i : Fin 32, x[i].eval w = xv.getLsbD i) (hy : ∀ i : Fin 32, y[i].eval w = yv.getLsbD i)
    (hz : ∀ i : Fin 32, z[i].eval w = zv.getLsbD i)
    (n : ℕ) (σ : BuildState m) (hn : n ≤ 31) (hw : GatesHold ((majorities x y z n).run σ).2 w)
    (j : ℕ) (hj : j < n) :
    (((majorities x y z n).run σ).1.getD j 0).eval w =
      (xv &&& yv ||| xv &&& zv ||| yv &&& zv).getLsbD (31 - n + j) := by
  induction n generalizing σ j with
  | zero => omega
  | succ n ih =>
    rw [run_majorities_succ] at hw ⊢
    have hg := hw _ (majorities_grows x y z n _ _ (Array.mem_push_self ..))
    have hxi := hx ⟨30 - n, by omega⟩
    have hyi := hy ⟨30 - n, by omega⟩
    have hzi := hz ⟨30 - n, by omega⟩
    simp only [Fin.getElem_fin] at hxi hyi hzi
    rcases j with _ | j
    · rw [List.getD_cons_zero, eval_xor, eval_var, hg, eval_xor, eval_xor, hxi, hyi, hzi,
        show 31 - (n + 1) + 0 = 30 - n by omega]
      simp only [BitVec.getLsbD_or, BitVec.getLsbD_and]
      cases xv.getLsbD (30 - n) <;> cases yv.getLsbD (30 - n) <;> cases zv.getLsbD (30 - n) <;> rfl
    · rw [List.getD_cons_succ, ih _ (by omega) hw j (by omega),
        show 31 - n + j = 31 - (n + 1) + (j + 1) by omega]

theorem run_rippleCarries_zero (p q : Word m) (c : Form m) (σ : BuildState m) :
    (rippleCarries p q 0 c).run σ = ([c], σ) := rfl

theorem run_rippleCarries_gate (p q : Word m) (n : ℕ) (c : Form m) (σ : BuildState m)
    (h : 1 ≤ 30 - n) :
    (rippleCarries p q (n + 1) c).run σ =
      let r := (rippleCarries p q n (c ^^^ Form.var (pos σ.next))).run
        { next := σ.next + 1,
          gates := σ.gates.push
            (pos σ.next, ⟨p[30 - n]'(by omega) ^^^ c, q[30 - n]'(by omega) ^^^ c⟩) }
      (c :: r.1, r.2) := by
  simp only [rippleCarries, h, ↓reduceIte]
  rfl

theorem run_rippleCarries_skip (p q : Word m) (n : ℕ) (c : Form m) (σ : BuildState m)
    (h : ¬ 1 ≤ 30 - n) :
    (rippleCarries p q (n + 1) c).run σ =
      let r := (rippleCarries p q n c).run σ
      (c :: r.1, r.2) := by
  simp only [rippleCarries, h, ↓reduceIte]
  rfl

theorem rippleCarries_grows (p q : Word m) (n : ℕ) (c : Form m) :
    Grows (rippleCarries p q n c) := by
  induction n generalizing c with
  | zero => intro σ kg h; rw [run_rippleCarries_zero]; exact h
  | succ n ih =>
    intro σ kg h
    by_cases hi : 1 ≤ 30 - n
    · rw [run_rippleCarries_gate _ _ _ _ _ hi]
      exact ih _ _ kg (Array.mem_push_of_mem _ h)
    · rw [run_rippleCarries_skip _ _ _ _ _ hi]
      exact ih _ _ kg h

/-- The ripple: from bit `31 - n` with the right carry, the carry forms evaluate to the carries of
`pv + qv`, if the recorded gates hold and bit `0` of `qv` is clear. -/
theorem rippleCarries_spec (p q : Word m) (w : Pos m → Bool) (pv qv : BitVec 32)
    (hp : ∀ i : Fin 32, p[i].eval w = pv.getLsbD i) (hq : ∀ i : Fin 32, q[i].eval w = qv.getLsbD i)
    (hq0 : qv.getLsbD 0 = false) (hc0 : BitVec.carry 0 pv qv false = false)
    (n : ℕ) (c : Form m) (σ : BuildState m) (hn : n ≤ 31)
    (hc : c.eval w = BitVec.carry (31 - n) pv qv false)
    (hw : GatesHold ((rippleCarries p q n c).run σ).2 w) (j : ℕ) (hj : j ≤ n) :
    (((rippleCarries p q n c).run σ).1.getD j 0).eval w =
      BitVec.carry (31 - n + j) pv qv false := by
  induction n generalizing c σ j with
  | zero =>
    obtain rfl : j = 0 := by omega
    rw [run_rippleCarries_zero]
    exact hc
  | succ n ih =>
    by_cases hi : 1 ≤ 30 - n
    · rw [run_rippleCarries_gate _ _ _ _ _ hi] at hw ⊢
      have hg := hw _ (rippleCarries_grows p q n _ _ _ (Array.mem_push_self ..))
      have hpi := hp ⟨30 - n, by omega⟩
      have hqi := hq ⟨30 - n, by omega⟩
      simp only [Fin.getElem_fin] at hpi hqi
      rw [eval_xor, eval_xor, hpi, hqi, hc, show 31 - (n + 1) = 30 - n by omega] at hg
      have hc' : (c ^^^ Form.var (pos σ.next)).eval w = BitVec.carry (31 - n) pv qv false := by
        rw [eval_xor, eval_var, hg, hc, show 31 - n = (30 - n) + 1 by omega, BitVec.carry_succ,
          show 31 - (n + 1) = 30 - n by omega]
        cases pv.getLsbD (30 - n) <;> cases qv.getLsbD (30 - n) <;>
          cases BitVec.carry (30 - n) pv qv false <;> rfl
      rcases j with _ | j
      · exact hc
      · rw [List.getD_cons_succ, ih _ _ (by omega) hc' hw j (by omega),
          show 31 - n + j = 31 - (n + 1) + (j + 1) by omega]
    · -- bit `0`: no gate, and the carry into bit `1` is the carry into bit `0`
      rw [run_rippleCarries_skip _ _ _ _ _ hi] at hw ⊢
      have hc' : c.eval w = BitVec.carry (31 - n) pv qv false := by
        rw [hc, show 31 - (n + 1) = 0 by omega, show 31 - n = 0 + 1 by omega, BitVec.carry_succ,
          hq0, hc0]
        cases pv.getLsbD 0 <;> rfl
      rcases j with _ | j
      · exact hc
      · rw [List.getD_cons_succ, ih _ _ (by omega) hc' hw j (by omega),
          show 31 - n + j = 31 - (n + 1) + (j + 1) by omega]

theorem run_add3W (x y z : Word m) (σ : BuildState m) :
    (add3W x y z).run σ =
      let r1 := (majorities x y z 31).run σ
      let r2 := (rippleCarries (xor3W x y z) (shiftW r1.1) 31 0).run r1.2
      (sumW (xor3W x y z) (shiftW r1.1) r2.1, r2.2) := by
  rw [add3W, StateT.run_bind]
  simp only [StateT.run_map]
  rfl

theorem grows_add3W (x y z : Word m) : Grows (add3W x y z) := by
  intro σ kg h
  rw [run_add3W]
  dsimp only
  exact rippleCarries_grows _ _ _ _ _ kg (majorities_grows x y z 31 σ kg h)

/-- The fused three-operand adder is sound: if its gates hold, its output denotes the sum of its
three inputs. -/
theorem sound_add3W {w : Pos m → Bool} {x y z : Word m} {xu yu zu : UInt32} (hx : Den w x xu)
    (hy : Den w y yu) (hz : Den w z zu) :
    Sound w (add3W x y z) (fun o ↦ Den w o (xu + yu + zu)) := by
  intro σ hw i
  rw [run_add3W] at hw ⊢
  dsimp only at hw ⊢
  generalize hr1 : (majorities x y z 31).run σ = r1 at hw ⊢
  -- the majority gates hold: they are a prefix of the gates
  have hw1 : GatesHold r1.2 w := fun kg hkg ↦ hw kg (rippleCarries_grows _ _ _ _ _ _ hkg)
  rw [UInt32.toBitVec_add, UInt32.toBitVec_add, carry_save]
  set xv := xu.toBitVec
  set yv := yu.toBitVec
  set zv := zu.toBitVec
  set mv := xv &&& yv ||| xv &&& zv ||| yv &&& zv
  have hp : ∀ i : Fin 32, (xor3W x y z)[i].eval w = (xv ^^^ yv ^^^ zv).getLsbD i := by
    intro i
    rw [xor3W, Fin.getElem_fin, Vector.getElem_ofFn, eval_xor, eval_xor, hx, hy, hz]
    simp [xv, yv, zv]
  have hq : ∀ i : Fin 32, (shiftW r1.1)[i].eval w = (mv <<< 1).getLsbD i := by
    intro i
    rw [shiftW, Fin.getElem_fin, Vector.getElem_ofFn, BitVec.getLsbD_shiftLeft]
    split_ifs with h0
    · rw [eval_zero]
      simp only at h0
      simp [h0]
    · simp only at h0
      have := majorities_spec x y z w xv yv zv hx hy hz 31 σ le_rfl (hr1 ▸ hw1) (i - 1)
        (by omega)
      rw [hr1] at this
      rw [this]
      simp [mv, i.isLt, show ¬ (i : ℕ) < 1 by omega]
  have h0 : (0 : Form m).eval w = BitVec.carry (31 - 31) (xv ^^^ yv ^^^ zv) (mv <<< 1) false := by
    rw [eval_zero, Nat.sub_self, BitVec.carry_zero]
  have hcarry := rippleCarries_spec _ _ w _ _ hp hq (by simp) (by simp) 31 0 r1.2 le_rfl h0 hw i
    (by omega)
  rw [Nat.sub_self, Nat.zero_add] at hcarry
  rw [sumW, Fin.getElem_fin, Vector.getElem_ofFn, eval_xor, eval_xor, hcarry, hp, hq,
    BitVec.getLsbD_add i.isLt, Bool.xor_assoc]

/-! ## Gate counts and availability -/

namespace Start

variable {S : Start m}

/-- Every bit of `x` reads only positions available at `n`. -/
def SubW (S : Start m) (x : Word m) (n : ℕ) : Prop := ∀ i : Fin 32, S.SubN x[i] n

theorem SubW.mono {x : Word m} {n n' : ℕ} (h : S.SubW x n) (hn : n ≤ n') : S.SubW x n' :=
  fun i ↦ (h i).mono hn

theorem subW_xorW {x y : Word m} {n : ℕ} (hx : S.SubW x n) (hy : S.SubW y n) :
    S.SubW (xorW x y) n := by
  intro i
  rw [xorW, Fin.getElem_fin, Vector.getElem_ofFn]
  exact (hx i).xor (hy i)

theorem subW_rotrW {x : Word m} {n : ℕ} (hx : S.SubW x n) (r : ℕ) : S.SubW (rotrW x r) n := by
  intro i
  rw [rotrW, Fin.getElem_fin, Vector.getElem_ofFn]
  exact hx ⟨_, Nat.mod_lt _ (by decide)⟩

theorem subW_litW {cpos : Pos m} (hc : S.avail.getLsbD cpos = true) (c : UInt32) (n : ℕ) :
    S.SubW (litW cpos c) n := by
  intro i
  rw [litW, Fin.getElem_fin, Vector.getElem_ofFn]
  split_ifs
  · exact subN_start hc n
  · exact subN_zero n

/-- An input word reads only start positions. -/
theorem subW_inW {b : ℕ} (hb : b + 32 ≤ 2 ^ m) (h : ∀ i < 32, S.avail.getLsbD (b + i) = true)
    (n : ℕ) : S.SubW (inW b) n := by
  intro i
  rw [inW, Fin.getElem_fin, Vector.getElem_ofFn]
  exact subN_start (by rw [pos_val (by omega)]; exact h i i.isLt) n

/-- The forms of a list read only positions available at `n`. -/
def SubL (S : Start m) (l : List (Form m)) (n : ℕ) : Prop := ∀ f ∈ l, S.SubN f n

theorem subN_getD {l : List (Form m)} {n : ℕ} (h : S.SubL l n) (i : ℕ) :
    S.SubN (l.getD i 0) n := by
  induction l generalizing i with
  | nil => exact subN_zero n
  | cons f l ih =>
    cases i with
    | zero => rw [List.getD_cons_zero]; exact h f List.mem_cons_self
    | succ i =>
      rw [List.getD_cons_succ]
      exact ih (fun g hg ↦ h g (List.mem_cons_of_mem _ hg)) i

theorem subW_sumW {p q : Word m} {cs : List (Form m)} {n : ℕ} (hp : S.SubW p n)
    (hq : S.SubW q n) (hc : S.SubL cs n) : S.SubW (sumW p q cs) n := by
  intro i
  rw [sumW, Fin.getElem_fin, Vector.getElem_ofFn]
  exact ((hp i).xor (hq i)).xor (subN_getD hc i)

theorem ok_addCarries (x y : Word m) (n : ℕ) :
    ∀ (c : Form m) (n₀ : ℕ), S.SubW x n₀ → S.SubW y n₀ → S.SubN c n₀ →
      S.Ok n₀ (addCarries x y n c) n S.SubL := by
  induction n with
  | zero =>
    intro c n₀ _ _ hc
    rw [addCarries]
    exact ok_pure (fun n hn f hf ↦ by rw [List.mem_singleton.mp hf]; exact hc.mono hn) rfl
  | succ n ih =>
    intro c n₀ hx hy hc
    rw [addCarries]
    refine ok_bind (ok_mul ((hx ⟨30 - n, by omega⟩).xor hc) ((hy ⟨30 - n, by omega⟩).xor hc))
      (by omega) fun g n₁ hn₁ hg ↦ ?_
    refine ok_bind (ih _ _ (hx.mono hn₁) (hy.mono hn₁) ((hc.mono hn₁).xor hg)) (by omega)
      fun rest n₂ hn₂ hrest ↦ ok_pure (fun n₃ hn₃ f hf ↦ ?_) (by omega)
    rcases List.mem_cons.mp hf with rfl | hf
    · exact hc.mono (by omega)
    · exact (hrest f hf).mono hn₃

/-- The ripple adder records `31` gates and its output reads only available positions. -/
theorem ok_addW {n₀ : ℕ} {x y : Word m} (hx : S.SubW x n₀) (hy : S.SubW y n₀) :
    S.Ok n₀ (addW x y) 31 S.SubW := by
  rw [addW]
  exact ok_map (ok_addCarries x y 31 0 n₀ hx hy (subN_zero _)) fun _ _ hn hcs ↦
    subW_sumW (hx.mono hn) (hy.mono hn) hcs

theorem ok_majorities (x y z : Word m) (n : ℕ) :
    ∀ n₀ : ℕ, S.SubW x n₀ → S.SubW y n₀ → S.SubW z n₀ → S.Ok n₀ (majorities x y z n) n S.SubL := by
  induction n with
  | zero =>
    intro n₀ _ _ _
    rw [majorities]
    exact ok_pure (fun _ _ f hf ↦ by simp at hf) rfl
  | succ n ih =>
    intro n₀ hx hy hz
    rw [majorities]
    have hi : 30 - n < 32 := by omega
    refine ok_bind (ok_mul ((hx ⟨30 - n, hi⟩).xor (hz ⟨30 - n, hi⟩))
      ((hy ⟨30 - n, hi⟩).xor (hz ⟨30 - n, hi⟩))) (by omega) fun g n₁ hn₁ hg ↦ ?_
    refine ok_bind (ih _ (hx.mono hn₁) (hy.mono hn₁) (hz.mono hn₁)) (by omega)
      fun rest n₂ hn₂ hrest ↦ ok_pure (fun n₃ hn₃ f hf ↦ ?_) (by omega)
    rcases List.mem_cons.mp hf with rfl | hf
    · exact (hg.mono (by omega)).xor ((hz ⟨30 - n, hi⟩).mono (by omega))
    · exact (hrest f hf).mono hn₃

theorem ok_rippleCarries (p q : Word m) (n : ℕ) :
    ∀ (c : Form m) (n₀ : ℕ), S.SubW p n₀ → S.SubW q n₀ → S.SubN c n₀ →
      S.Ok n₀ (rippleCarries p q n c) (min n 30) S.SubL := by
  induction n with
  | zero =>
    intro c n₀ _ _ hc
    rw [rippleCarries]
    exact ok_pure (fun n hn f hf ↦ by rw [List.mem_singleton.mp hf]; exact hc.mono hn) rfl
  | succ n ih =>
    intro c n₀ hp hq hc
    rw [rippleCarries]
    split
    · refine ok_bind (ok_mul ((hp ⟨30 - n, by omega⟩).xor hc) ((hq ⟨30 - n, by omega⟩).xor hc))
        (by omega) fun g n₁ hn₁ hg ↦ ?_
      refine ok_bind (ih _ _ (hp.mono hn₁) (hq.mono hn₁) ((hc.mono hn₁).xor hg)) (by omega)
        fun rest n₂ hn₂ hrest ↦ ok_pure (fun n₃ hn₃ f hf ↦ ?_) (by omega)
      rcases List.mem_cons.mp hf with rfl | hf
      · exact hc.mono (by omega)
      · exact (hrest f hf).mono hn₃
    · refine ok_bind (ih _ _ hp hq hc) (by omega)
        fun rest n₂ hn₂ hrest ↦ ok_pure (fun n₃ hn₃ f hf ↦ ?_) (by omega)
      rcases List.mem_cons.mp hf with rfl | hf
      · exact hc.mono (by omega)
      · exact (hrest f hf).mono hn₃

theorem subW_xor3W {x y z : Word m} {n : ℕ} (hx : S.SubW x n) (hy : S.SubW y n)
    (hz : S.SubW z n) : S.SubW (xor3W x y z) n := by
  intro i
  rw [xor3W, Fin.getElem_fin, Vector.getElem_ofFn]
  exact ((hx i).xor (hy i)).xor (hz i)

theorem subW_shiftW {ms : List (Form m)} {n : ℕ} (h : S.SubL ms n) : S.SubW (shiftW ms) n := by
  intro i
  rw [shiftW, Fin.getElem_fin, Vector.getElem_ofFn]
  split_ifs
  · exact subN_zero n
  · exact subN_getD h _

/-- The fused three-operand adder records `61` gates and its output reads only available
positions. -/
theorem ok_add3W {n₀ : ℕ} {x y z : Word m} (hx : S.SubW x n₀) (hy : S.SubW y n₀)
    (hz : S.SubW z n₀) : S.Ok n₀ (add3W x y z) 61 S.SubW := by
  rw [add3W]
  refine ok_bind (ok_majorities x y z 31 n₀ hx hy hz) (by omega) fun ms n₁ hn₁ hms ↦ ?_
  have hp := subW_xor3W (hx.mono hn₁) (hy.mono hn₁) (hz.mono hn₁)
  exact ok_map ((ok_rippleCarries _ _ 31 0 n₁ hp (subW_shiftW hms) (subN_zero _)).cast rfl)
    fun _ _ hn hcs ↦ subW_sumW (hp.mono hn) ((subW_shiftW hms).mono hn) hcs

end Start

end ProductCircuit

end FR

end G6_FRBlake2sWords
