-- G6: this module also holds the former modules `FRBlake2sWitness`, `FRBlockLayout`, `FRBlockChain`, `FRBlockStream` (one section each, in import order).
import FRBlake2sWalk
import RecursionFast.Contract.Relation
import Mathlib.Tactic.IntervalCases
import RecursionFast.Contract.Signature

section G6_FRBlake2sWitness

-- Copied from `submissions/spartan-srom/lean/SpartanSromBlake2sWitness.lean` (this repository,
-- branch `v4/flock-recursive` at `783328c`), renamed to the namespace `FR`, and **retargeted** from
-- spartan-srom's chain block to the block circuit of BLUEPRINT Appendix A.6 (`blake2sCircuit`,
-- re-based): `fastTrace` takes any input block, not a digest; the dump is of `blake2sCircuit`'s
-- rows. That file was ported from v3 `spartan-chain` (submissions repo, local `main` at `1f59b38`)
-- to the v4 contract.

/-!
# Witness generation for the block, and the circuit's rows

* `fastTrace inp`: the honest block of the inputs `inp` (`blake2sCircuit.traceF inp`) as an
  `Array Bool` of `2 ^ 14` bits, computed by the generic gadgets with Boolean values (`evalOps`:
  `xor` is `^^`, a product gate stores `a && b`), i.e. `O(|circuit|)` Boolean operations, not the
  bitset trace. `fastTrace_eq`: it is `blake2sCircuit.traceF inp` at every position (by the
  simulation of `FRBlake2sGeneric.lean` with `φ L = L.eval (traceF inp)`).
* `circuitRows`, `rowLine`: the row list of the block (`A₀`, `B₀`) for a known-answer harness: one
  line per position `k < 2 ^ 14`, `k <a-form> <b-form>`, each form as 256 chunks of 64 bits, lowest
  chunk first, each chunk as 16 lowercase hex digits (most significant first). The rows are
  `rowOf` of `blake2sCircuit` (`blockAt gateBase = blake2sCircuit`), the constant's row
  `(var 1152, var 1152)` included.
-/

namespace FR

open RecursionFast RecursionFast.Blake2s ProductCircuit Blake2sCircuit

/-! ## The evaluation interpretation -/

/-- Forms are their Boolean values on the honest block; a product gate at `k` returns `a && b`
and stores it at `k`. -/
def evalOps {m : ℕ} (inp : Pos m → Bool) : GOps m Bool (Array Bool) where
  zero := false
  xor a b := a ^^ b
  var := inp
  res _ a b := a && b
  upd arr k a b := arr.set! k (a && b)

theorem evalOps_res {m : ℕ} (inp : Pos m → Bool) (k : Pos m) (a b : Bool) :
    (evalOps inp).res k a b = (a && b) := rfl

theorem evalOps_upd {m : ℕ} (inp : Pos m → Bool) (arr : Array Bool) (k : Pos m) (a b : Bool) :
    (evalOps inp).upd arr k a b = arr.set! k (a && b) := rfl

theorem linear_eval {m : ℕ} (inp z : Pos m → Bool) :
    Generic.Linear (evalOps inp) (fun L : Form m ↦ L.eval z) where
  zero := eval_zero z
  xor a b := eval_xor a b z

/-- The block before the compression's gates: `1` at the constant, the inputs at the input
positions, `0` elsewhere (`blake2sCircuit.initF`, computably). -/
def blockInit (inp : Pos Blake2sCircuit.m → Bool) (k : Pos Blake2sCircuit.m) : Bool :=
  decide (k = constPos) || (inputs.getLsbD k && inp k)

theorem blockInit_eq (inp : Pos Blake2sCircuit.m → Bool) :
    blockInit inp = blake2sCircuit.initF inp := by
  funext k
  rw [blockInit, initF, blake2sCircuit_cpos, blake2sCircuit_inputs]

/-- The honest block of the inputs `inp`, computed with Boolean values. -/
def fastTrace (inp : Pos Blake2sCircuit.m → Bool) : Array Bool :=
  let i := blockInit inp
  let r := (evalOps i).compressW.run ⟨gateBase, Array.ofFn i⟩
  (outPairs r.1).foldl (fun a p ↦ a.set! p.1 p.2) r.2.acc

/-! ## Correctness -/

-- No unification may evaluate the compression.
attribute [local irreducible] compressW GOps.compressW

private theorem foldl_set {m : ℕ} (z : Pos m → Bool) (L : List (Pos m × Bool))
    (hL : ∀ p ∈ L, p.2 = z p.1) :
    ∀ (a : Array Bool), a.size = 2 ^ m → (L.foldl (fun a p ↦ a.set! p.1 p.2) a).size = 2 ^ m ∧
      ∀ j : Pos m, (L.foldl (fun a p ↦ a.set! p.1 p.2) a)[j.val]? =
        if j ∈ L.map Prod.fst then some (z j) else a[j.val]? := by
  induction L with
  | nil => intro a ha; simp [ha]
  | cons p L ih =>
    intro a ha
    have hs : (a.set! p.1 p.2).size = 2 ^ m := by simp [ha]
    obtain ⟨h1, h2⟩ := ih (fun q hq ↦ hL q (List.mem_cons_of_mem _ hq)) _ hs
    refine ⟨h1, fun j ↦ ?_⟩
    rw [List.foldl_cons, h2 j]
    by_cases hj : j ∈ L.map Prod.fst
    · simp [hj]
    · have hp := hL p List.mem_cons_self
      by_cases hpj : p.1 = j
      · subst hpj
        simp [hj, ha, hp]
      · have : (p.1 : ℕ) ≠ j := fun h ↦ hpj (Fin.ext h)
        simp [hj, this, Ne.symm hpj]

/-- The positions available after a schedule: the initial ones and every gate's. -/
theorem availAfter_getLsbD {m : ℕ} (a : Form m) (L : List (Pos m × Gate m)) (j : ℕ) :
    (availAfter a L).getLsbD j = (a.getLsbD j || L.any fun kg ↦ decide ((kg.1 : ℕ) = j)) := by
  induction L generalizing a with
  | nil => simp [availAfter]
  | cons kg L ih =>
    change (availAfter (a ||| Form.var kg.1) L).getLsbD j = _
    rw [ih, BitVec.getLsbD_or, getLsbD_var, List.any_cons, Bool.or_assoc]

/-- The gates of the compression sit in `[1280, 16000)`. -/
theorem compress_keys {kg : Pos Blake2sCircuit.m × Gate Blake2sCircuit.m}
    (h : kg ∈ (compressW.run ⟨gateBase, #[]⟩).2.gates.toList) :
    1280 ≤ kg.1.val ∧ kg.1.val < 16000 := by
  have hok := ok_compressW ⟨gateBase, #[]⟩ Start.inv_init le_rfl (by decide)
  have hav := hok.1.avail kg.1
  rw [hok.2.1, availAfter_getLsbD] at hav
  have hany : ((compressW.run ⟨gateBase, #[]⟩).2.gates.toList.any
      fun kg' ↦ decide ((kg'.1 : ℕ) = kg.1)) = true := List.any_eq_true.mpr ⟨kg, h, by simp⟩
  rw [hany, Bool.or_true] at hav
  have hfresh := boundedFrom_fresh hok.1.bounded (List.mem_map_of_mem (f := Prod.fst) h)
  have := (start_availAt _ _).mp hav.symm
  rw [start_avail] at hfresh
  simp only [decide_eq_false_iff_not] at hfresh
  simp only [gateBase] at this
  omega

section

variable (inp : Pos Blake2sCircuit.m → Bool)

private theorem trace_gates :
    ∀ kg ∈ blake2sCircuit.gates, blake2sCircuit.traceF inp kg.1 =
      (kg.2.a.eval (blake2sCircuit.traceF inp) && kg.2.b.eval (blake2sCircuit.traceF inp)) :=
  gates_of_rows bounded_blake2s _ (trace_holds bounded_blake2s inp)

private theorem trace_one : blake2sCircuit.traceF inp constPos = true := by
  rw [← blake2sCircuit_cpos]; exact traceF_cpos bounded_blake2s _

/-- The initial block agrees with the honest block outside the compression's gates and the output
rows. -/
private theorem init_eq (k : Pos Blake2sCircuit.m)
    (hk1 : k ∉ (compressW.run ⟨gateBase, #[]⟩).2.gates.toList.map Prod.fst)
    (hk2 : k ∉ (outRows (compressW.run ⟨gateBase, #[]⟩).1).map Prod.fst) :
    blockInit inp k = blake2sCircuit.traceF inp k := by
  rw [traceF_of_not_mem _ _ fun hm ↦ ?_, blockInit_eq]
  obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hm
  rw [Array.mem_toList_iff, blake2sCircuit_gates] at hp
  rcases Array.mem_append.mp hp with hp | hp
  · exact hk1 (List.mem_map_of_mem (Array.mem_toList_iff.mpr hp))
  · exact hk2 (List.mem_map_of_mem (List.mem_toArray.mp hp))

/-- **Witness generation.** The Boolean evaluation of the generic gadgets computes the honest
block of the inputs `inp` at every position. -/
theorem fastTrace_eq (k : Pos Blake2sCircuit.m) :
    (fastTrace inp)[k.val]? = some (blake2sCircuit.traceF inp k) := by
  set z := blake2sCircuit.traceF inp
  have hlin := linear_eval (blockInit inp) z
  have hsz : (Array.ofFn (blockInit inp)).size = 2 ^ Blake2sCircuit.m := Array.size_ofFn
  have hget : (Array.ofFn (blockInit inp))[k.val]? = some (blockInit inp k) := by
    rw [Array.getElem?_ofFn, dite_eq_left k.isLt]
  unfold fastTrace
  dsimp only
  generalize Array.ofFn (blockInit inp) = A at hsz hget ⊢
  have hgates : ∀ kg ∈ (compressW.run ⟨gateBase, #[]⟩).2.gates,
      z kg.1 = (kg.2.a.eval z && kg.2.b.eval z) := fun kg h ↦ trace_gates inp kg (by
    rw [blake2sCircuit_gates]
    exact Array.mem_append_left _ h)
  have hsim := Generic.sim_compressW (o := evalOps (blockInit inp)) (φ := fun L ↦ L.eval z)
    (s₀ := A) hlin (fun k hk ↦ by
      simp only [evalOps, eval_var]
      rw [start_avail] at hk
      simp only [decide_eq_true_eq] at hk
      refine init_eq inp k (fun h ↦ ?_) (fun h ↦ ?_)
      · obtain ⟨kg, hkg, rfl⟩ := List.mem_map.mp h
        have := compress_keys hkg
        omega
      · obtain ⟨kg, hkg, rfl⟩ := List.mem_map.mp h
        obtain ⟨w, i, rfl⟩ := mem_outRows hkg
        have := pos_out_val w i
        dsimp only at hk
        omega)
    ⟨gateBase, #[]⟩ ⟨gateBase, A⟩ ⟨rfl, List.foldl_nil.symm⟩
    (fun kg h ↦ by
      rw [evalOps_res]
      beta_reduce
      rw [eval_var]
      exact (hgates kg h).symm)
  obtain ⟨⟨-, hacc⟩, hvr⟩ := hsim
  -- the compression's gates, as stores of the honest values
  have hc : (Generic.accOf (evalOps (blockInit inp)) (fun L ↦ L.eval z) A
      (compressW.run ⟨gateBase, #[]⟩).2.gates.toList) =
      (((compressW.run ⟨gateBase, #[]⟩).2.gates.toList.map fun kg ↦ (kg.1, z kg.1)).foldl
        (fun a p ↦ a.set! p.1 p.2) A) := by
    rw [List.foldl_map, Generic.accOf]
    refine List.foldl_ext _ _ _ fun a kg hkg ↦ ?_
    rw [evalOps_upd]
    rw [hgates kg (Array.mem_toList_iff.mp hkg)]
  -- the output rows, as stores of the honest values
  set r := (evalOps (blockInit inp)).compressW.run ⟨gateBase, A⟩
  have hout : outPairs r.1 = (outRows (compressW.run ⟨gateBase, #[]⟩).1).map
      fun kg ↦ (kg.1, z kg.1) := by
    simp only [outPairs, outRows, List.map_flatMap, List.map_map]
    refine List.flatMap_congr fun w _ ↦ List.map_congr_left fun i _ ↦ ?_
    simp only [Function.comp_apply, Prod.mk.injEq, true_and]
    have h1 := hvr w i
    simp only [Fin.getElem_fin] at h1 ⊢
    rw [h1]
    have hrow := trace_gates inp (pos (256 + 32 * w.val + i.val),
      ⟨(compressW.run ⟨gateBase, #[]⟩).1[w][i], Form.var constPos⟩) (by
        rw [blake2sCircuit_gates]
        refine Array.mem_append_right _ (List.mem_toArray.mpr ?_)
        exact List.mem_flatMap.mpr ⟨w, List.mem_finRange w,
          List.mem_map.mpr ⟨i, List.mem_finRange i, rfl⟩⟩)
    simp only [eval_var, trace_one inp, Bool.and_true] at hrow
    exact hrow.symm
  obtain ⟨hs1, hg1⟩ := foldl_set z ((compressW.run ⟨gateBase, #[]⟩).2.gates.toList.map
    fun kg ↦ (kg.1, z kg.1)) (fun p hp ↦ by obtain ⟨kg, -, rfl⟩ := List.mem_map.mp hp; rfl) _ hsz
  obtain ⟨-, hg2⟩ := foldl_set z ((outRows (compressW.run ⟨gateBase, #[]⟩).1).map
    fun kg ↦ (kg.1, z kg.1)) (fun p hp ↦ by obtain ⟨kg, -, rfl⟩ := List.mem_map.mp hp; rfl) _ hs1
  rw [hacc, hc, hout, hg2, hg1, hget]
  have hf : ∀ L : List (Pos Blake2sCircuit.m × Gate Blake2sCircuit.m),
      (L.map fun kg ↦ (kg.1, z kg.1)).map Prod.fst = L.map Prod.fst := fun L ↦ by
    rw [List.map_map]; rfl
  rw [hf, hf]
  split_ifs with ho hg
  · rfl
  · rfl
  · exact congrArg some (init_eq inp k hg ho)

end

/-! ## The circuit's rows (known-answer harness) -/

/-- The block circuit with its compression gates recorded from `base`; `blockAt gateBase` is
`blake2sCircuit` (`blockAt_eq`). The argument keeps the compression out of the compiler's
closed-term extraction (it would otherwise run when an executable starts); `never_extract`
keeps the closed call `blockAt gateBase` from being extracted. -/
@[never_extract] def blockAt (base : ℕ) : ProductCircuit Blake2sCircuit.m :=
  let r := compressW.run ⟨base, #[]⟩
  { cpos := constPos, inputs := inputs, gates := r.2.gates ++ (outRows r.1).toArray }

theorem blockAt_eq : blockAt gateBase = blake2sCircuit := by
  unfold blockAt blake2sCircuit
  rfl

/-- 64 bits as 16 lowercase hex digits, most significant first. -/
def hex64 (x : ℕ) : String :=
  String.ofList ((List.range 16).reverse.map fun j ↦ Nat.digitChar ((x >>> (4 * j)) % 16))

/-- A form as 256 chunks of 64 bits, lowest chunk first, each as 16 hex digits. -/
def hexForm (L : Form Blake2sCircuit.m) : String :=
  String.join ((List.range 256).map fun i ↦ hex64 ((L.toNat >>> (64 * i)) % 2 ^ 64))

/-- The dump line of a row: `k <a-form> <b-form>`. -/
def rowLine (k : ℕ) (g : Gate Blake2sCircuit.m) : String :=
  toString k ++ " " ++ hexForm g.a ++ " " ++ hexForm g.b

/-- The rows of the block (`rowOf`, i.e. `A₀`, `B₀`), position by position. -/
def circuitRows (base : ℕ) : List (Gate Blake2sCircuit.m) :=
  let c := blockAt base
  let l := c.gates.toList
  (List.finRange (2 ^ Blake2sCircuit.m)).map fun k ↦ c.rowOfList l k

/-- The rows listed are the block's `rowOf`, position by position. -/
theorem circuitRows_eq :
    circuitRows gateBase = (List.finRange (2 ^ Blake2sCircuit.m)).map blake2sCircuit.rowOf := by
  unfold circuitRows
  rw [blockAt_eq]
  rfl

end FR

end G6_FRBlake2sWitness

section G6_FRBlockLayout

-- New for `flock-recursive` (BLUEPRINT Appendix A.6). `h0`, `leDigest`, the byte and digest readers
-- and `block_getLsbD` are copied from `submissions/spartan-srom/lean/SpartanSromBlake2sR1CS.lean`
-- (this repository, branch `v4/flock-recursive` at `783328c`), renamed to the namespace `FR`.

/-!
# The block layout and the block R1CS with its public target (BLUEPRINT §4, Appendix A.6)

One block of `2 ^ 14` bits is one BLAKE2s compression, laid out as A.6:

| bits | element (128 bits) | content |
|---|---|---|
| `0 … 255` | 0–1 | `h_in` (8 words, little-endian) |
| `256 … 511` | 2–3 | `h_out` (output rows `(out form, one)`) |
| `512 … 1023` | 4–7 | the 64-byte message, byte `p` bit `b` at `512 + 8 p + b` |
| `1024`, `1056` | 8 | the counter's words `t_lo`, `t_hi` |
| `1088`, `1120` | 8 | the flags `f0`, `f1` |
| `1152` | 9 | `one` |
| `1153 … 1279` | | zero rows |
| `1280 … 15999` | | the 14,720 product gates in leanVM's order |
| `16000 … 16383` | | zero rows |

**Two R1CS.** `circuitR1CS` is the R1CS of the re-based BLAKE2s circuit (`FRBlake2sCompress`):
every input (`h_in`, the message, `t`, `f`) has the row `(var k, var one)`, `one` the row
`(one, one)`, a gate its two forms, an output `(out form, one)`. It is the gate-level object the
soundness proofs run on (`compress_sound`).

The **block R1CS of the entry** (BLUEPRINT revision 3.1, §4 and P1-D2/D3) carries a **public
target** `E`: the constraint is `(A₀ z) ∘ (B₀ z) = z + E`, and the positions that hold per-block
public constants have the row `(0, 0)`, so there the constraint reads `z = E` (characteristic
two). A `Target` says which positions are pinned and to which bit (`tgt k = some b`);
`blockR1CS tgt` is `circuitR1CS` with the rows of the pinned positions replaced by `(0, 0)`,
`targetVal R tgt` is `E`, and `HoldsE` is the constraint with the target. Every target of the
entry pins `one` to `1` and otherwise only inputs (`TargetOk`); then a Boolean block satisfying
`HoldsE` satisfies `circuitR1CS`, has `one = 1` and holds the target's bits (`holdsE_sound`),
and conversely (`holdsE_complete`).

**The `one` bit (BP-C-M5).** The all-zero block satisfies `circuitR1CS` (`zero_holds`: every row
is a product of linear forms) with `one = 0`; the target excludes it (`zero_not_holdsE`).

**The walk** of `blockR1CS tgt` is the walk of `circuitR1CS` with the row weights of the pinned
positions set to `0` (`walkE_eq_sum`); the row weights are arbitrary (the verifier passes the
Lagrange weights of the skip coordinate at `λ` and the `eq` table of the other row bits).

Main results: `holdsE_sound`, `holdsE_complete`, `compress_sound`, the readers `hIn`, `hOut`,
`msgBytes`, `readDigest`, the rows of `circuitR1CS` (`rowOf_one`, `rowOf_input`, `rowOf_zero`),
the BLAKE2s facts `blake2sDigest_eq`, `block_congr`, and `walkE_eq_sum`.
-/

namespace FR

open RecursionFast RecursionFast.Blake2s ProductCircuit Blake2sCircuit

namespace Block

/-! ## Positions and the block R1CS -/

/-- A position of a block. -/
abbrev Pos := ProductCircuit.Pos Blake2sCircuit.m

/-- The position of `one` (bit `1152`, BLUEPRINT A.6). -/
def onePos : Pos := constPos

theorem onePos_val : (onePos : ℕ) = 1152 := rfl

/-- The R1CS of the re-based BLAKE2s circuit, `C = I`, no target: the gate-level object. -/
noncomputable def circuitR1CS : BlockR1CS Blake2sCircuit.m := blake2sCircuit.toBlockR1CS

/-! ## Rows of `circuitR1CS` -/

/-- The row of `one` is `(one, one)`. -/
theorem rowOf_one : blake2sCircuit.rowOf onePos = ⟨Form.var onePos, Form.var onePos⟩ := by
  have := rowOf_cpos bounded_blake2s
  rwa [blake2sCircuit_cpos] at this

/-- The row of an input of a bounded circuit is `(var k, var one)`. -/
theorem rowOf_input' {m : ℕ} {c : ProductCircuit m} (hc : c.Bounded) {k : ProductCircuit.Pos m}
    (hk : c.inputs.getLsbD k = true) (hkc : k ≠ c.cpos) :
    c.rowOf k = ⟨Form.var k, Form.var c.cpos⟩ := by
  have hnm : k ∉ c.gates.toList.map Prod.fst := fun hm ↦ by
    have := boundedFrom_fresh hc hm
    rw [BitVec.getLsbD_or, hk, Bool.true_or] at this
    exact Bool.noConfusion this
  have hl : c.gates.toList.lookup k = none :=
    Option.eq_none_iff_forall_ne_some.mpr fun _ h ↦ hnm (mem_of_lookup h)
  simp only [rowOf, rowOfList, hl, hkc, ↓reduceIte, hk]

/-- The row of an input of the block (`h_in`, the message, `t`, `f`): `(var k, var one)`. -/
theorem rowOf_input {k : Pos} (hk : k.val < 256 ∨ (512 ≤ k.val ∧ k.val < 1152)) :
    blake2sCircuit.rowOf k = ⟨Form.var k, Form.var onePos⟩ := by
  have := rowOf_input' bounded_blake2s (k := k)
    (by rw [blake2sCircuit_inputs, getLsbD_inputs]; exact decide_eq_true hk)
    (by rw [blake2sCircuit_cpos]; exact Fin.ne_of_val_ne (by rw [constPos_val]; omega))
  rwa [blake2sCircuit_cpos] at this

/-- The row of a position of a circuit that is no gate, no input and not the constant is
`(0, 0)`. -/
theorem rowOf_zero' {m : ℕ} {c : ProductCircuit m} {k : ProductCircuit.Pos m}
    (hnm : k ∉ c.gates.toList.map Prod.fst) (hk : c.inputs.getLsbD k = false) (hkc : k ≠ c.cpos) :
    c.rowOf k = ⟨0, 0⟩ := by
  have hl : c.gates.toList.lookup k = none :=
    Option.eq_none_iff_forall_ne_some.mpr fun _ h ↦ hnm (mem_of_lookup h)
  simp only [rowOf, rowOfList, hl, hkc, ↓reduceIte, hk, Bool.false_eq_true]

/-- The rows of `1153 … 1279` and `16000 …` are `(0, 0)`. -/
theorem rowOf_zero {k : Pos} (hk : (1152 < k.val ∧ k.val < 1280) ∨ 16000 ≤ k.val) :
    blake2sCircuit.rowOf k = ⟨0, 0⟩ := by
  have hnm : k ∉ blake2sCircuit.gates.toList.map Prod.fst := by
    intro hm
    obtain ⟨p, hp, hpk⟩ := List.mem_map.mp hm
    have hp' := Array.mem_toList_iff.mp hp
    rw [blake2sCircuit_gates] at hp'
    rcases Array.mem_append.mp hp' with hp | hp
    · have := compress_keys (Array.mem_toList_iff.mpr hp)
      rw [hpk] at this
      omega
    · obtain ⟨w, i, rfl⟩ := mem_outRows (List.mem_toArray.mp hp)
      have := pos_out_val w i
      rw [show (pos (256 + 32 * w.val + i.val) : Pos) = k from hpk] at this
      have := w.isLt
      have := i.isLt
      omega
  have hkc : k ≠ blake2sCircuit.cpos := by
    rw [blake2sCircuit_cpos]; exact Fin.ne_of_val_ne (by rw [constPos_val]; omega)
  have hin : blake2sCircuit.inputs.getLsbD k = false := by
    rw [blake2sCircuit_inputs, getLsbD_inputs]; exact decide_eq_false (by omega)
  exact rowOf_zero' hnm hin hkc

/-! ## The all-zero block and the `one` bit -/

/-- The all-zero block satisfies the circuit's R1CS (without target) over any ring. -/
theorem zero_holds {R : Type*} [CommRing R] : circuitR1CS.Holds (fun _ : Pos ↦ (0 : R)) := by
  intro k
  simp [BlockR1CS.mulVec]

/-! ## Reading a block -/

/-- The byte a block holds at the positions `b, …, b + 7`, low bit first. -/
def readByte (w : Pos → Bool) (b : ℕ) : UInt8 := ⟨BitVec.ofFnLE fun i : Fin 8 ↦ w (pos (b + i))⟩

/-- The digest a block holds from position `b`: byte `e` bit `b'` at `b + 8 e + b'`. -/
def readDigest (w : Pos → Bool) (b : ℕ) : Digest :=
  Vector.ofFn fun e : Fin 32 ↦ readByte w (b + 8 * e)

/-- The chaining value `h_in`, eight words. -/
def hIn (w : Pos → Bool) : Vector UInt32 8 := Vector.ofFn fun j : Fin 8 ↦ readWord w (32 * j)

/-- The output `h_out`, eight words. -/
def hOut (w : Pos → Bool) : Vector UInt32 8 :=
  Vector.ofFn fun j : Fin 8 ↦ readWord w (256 + 32 * j)

/-- The 64 message bytes, byte `p` at `512 + 8 p`. -/
def msgBytes (w : Pos → Bool) : List UInt8 :=
  List.ofFn fun p : Fin 64 ↦ readByte w (msgBase + 8 * p)

theorem readByte_getLsbD (w : Pos → Bool) (b : ℕ) {i : ℕ} (hi : i < 8) :
    (readByte w b).toBitVec.getLsbD i = w (pos (b + i)) := by
  simp [readByte, hi]

theorem readWord_getLsbD (w : Pos → Bool) (b : ℕ) {i : ℕ} (hi : i < 32) :
    (readWord w b).toBitVec.getLsbD i = w (pos (b + i)) := by
  simp [readWord, hi]

theorem readDigest_getLsbD (w : Pos → Bool) (b e : ℕ) (he : e < 32) {i : ℕ} (hi : i < 8) :
    (readDigest w b)[e].toBitVec.getLsbD i = w (pos (b + 8 * e + i)) := by
  rw [readDigest, Vector.getElem_ofFn, readByte_getLsbD _ _ hi]

/-- Two digests are equal when their bits are. -/
theorem digest_ext {d d' : Digest}
    (h : ∀ e (he : e < 32), ∀ i < 8, d[e].toBitVec.getLsbD i = d'[e].toBitVec.getLsbD i) :
    d = d' :=
  Vector.ext fun e he ↦ UInt8.toBitVec_inj.mp (BitVec.eq_of_getLsbD_eq fun i hi ↦ h e he i hi)

/-- The digest a block holds depends only on its positions. -/
theorem readDigest_congr {w w' : Pos → Bool} {b b' : ℕ}
    (h : ∀ e < 32, ∀ i < 8, w (pos (b + 8 * e + i)) = w' (pos (b' + 8 * e + i))) :
    readDigest w b = readDigest w' b' :=
  digest_ext fun e he i hi ↦ by
    rw [readDigest_getLsbD _ _ _ he hi, readDigest_getLsbD _ _ _ he hi, h e he i hi]

/-- Bit `j < 256` of a digest: bit `j mod 8` of byte `j / 8`. -/
def digestBit (d : Digest) (j : ℕ) : Bool :=
  if h : j < 256 then (d[j / 8]'(by omega)).toBitVec.getLsbD (j % 8) else false

/-- A block holds the digest `d` from `b` iff its 256 positions hold the bits of `d`. -/
theorem readDigest_eq_iff (w : Pos → Bool) (b : ℕ) (d : Digest) :
    readDigest w b = d ↔ ∀ j < 256, w (pos (b + j)) = digestBit d j := by
  constructor
  · rintro rfl j hj
    rw [digestBit, dite_eq_left hj, readDigest_getLsbD _ _ _ (by omega) (Nat.mod_lt _ (by omega))]
    congr 2
    omega
  · intro h
    refine digest_ext fun e he i hi ↦ ?_
    rw [readDigest_getLsbD _ _ _ he hi, show b + 8 * e + i = b + (8 * e + i) by omega,
      h _ (by omega), digestBit, dite_eq_left (by omega)]
    simp only [show (8 * e + i) / 8 = e by omega, show (8 * e + i) % 8 = i by omega]

/-! ## BLAKE2s facts -/

/-- The chaining value of an unkeyed 32-byte BLAKE2s (RFC 7693 §2.5, §3.3): `iv` with the parameter
block `0x0101kknn`, `kk = 0`, `nn = 32`, XORed into word `0`. -/
def h0 : Vector UInt32 8 :=
  iv.set 0 (iv[0] ^^^ (0x01010000 : UInt32) ^^^ (0 : ℕ).toUInt32 <<< 8 ^^^ (32 : ℕ).toUInt32)

/-- The 32-byte digest whose byte `e` is byte `e mod 4` of word `e / 4`, little-endian (the `le`
encoding of `blake2s`). -/
def leDigest (H : Vector UInt32 8) : Digest :=
  Vector.ofFn fun e : Fin 32 ↦ (H[e.val / 4] >>> (8 * (e.val % 4)).toUInt32).toUInt8

private theorem toList_eq_ofFn {α : Type} (H : Vector α 8) :
    H.toList = [H[0], H[1], H[2], H[3], H[4], H[5], H[6], H[7]] := by
  apply List.ext_getElem (by simp)
  intro i h1 h2
  simp only [Vector.length_toList] at h1
  interval_cases i <;> simp

/-- BLAKE2s-256 of any input is the block loop of RFC 7693 §3.3 from `h0`, encoded little-endian
and truncated to 32 bytes. -/
theorem blake2s256_eq (l : List UInt8) :
    blake2s256 l = ((compressInput h0 0 l ((l.length - 1) / 64)).toList.flatMap
      (fun w : UInt32 ↦ [w.toUInt8, (w >>> 8).toUInt8, (w >>> 16).toUInt8,
        (w >>> 24).toUInt8])).take 32 := by
  simp only [blake2s256, blake2s, List.length_nil, ↓reduceIte, List.nil_append]
  rfl

/-- The contract's digest of an input is the little-endian encoding of its final chaining
value. -/
theorem blake2sDigest_eq (l : List UInt8) :
    blake2sDigest l = leDigest (compressInput h0 0 l ((l.length - 1) / 64)) := by
  apply Vector.ext
  intro e he
  simp only [blake2sDigest, Vector.getElem_mk, List.getElem_toArray, blake2s256_eq, toList_eq_ofFn,
    leDigest, Vector.getElem_ofFn]
  interval_cases e <;> rfl

/-- Bit `b < 8` of a byte of a word is a bit of the word. -/
theorem toUInt8_shiftRight_getLsbD (w : UInt32) (q b : ℕ) (hq : q < 4) (hb : b < 8) :
    ((w >>> (8 * q).toUInt32).toUInt8).toBitVec.getLsbD b = w.toBitVec.getLsbD (8 * q + b) := by
  simp [hb, Nat.mod_eq_of_lt (show 8 * q < 32 by omega)]

/-- Bit `b` of byte `e` of `leDigest H` is bit `8 (e mod 4) + b` of word `e / 4`. -/
theorem leDigest_getLsbD (H : Vector UInt32 8) (e : ℕ) (he : e < 32) (b : ℕ) (hb : b < 8) :
    (leDigest H)[e].toBitVec.getLsbD b =
      (H[e / 4]'(by omega)).toBitVec.getLsbD (8 * (e % 4) + b) := by
  rw [leDigest, Vector.getElem_ofFn]
  exact toUInt8_shiftRight_getLsbD _ _ _ (by omega) hb

/-- The digest a block holds at `h_out` is the encoding of its output words. -/
theorem readDigest_hOut (w : Pos → Bool) : readDigest w 256 = leDigest (hOut w) := by
  refine digest_ext fun e he i hi ↦ ?_
  rw [readDigest_getLsbD _ _ _ he hi, leDigest_getLsbD _ _ he _ hi, hOut, Vector.getElem_ofFn,
    readWord_getLsbD _ _ (by omega)]
  show w (pos (256 + 8 * e + i)) = w (pos (256 + 32 * (e / 4) + (8 * (e % 4) + i)))
  congr 2
  omega

/-- Bit `i` of message word `j` is bit `i mod 8` of byte `4 j + i / 8` of the input (zero past
its end), for an input of at most 64 bytes. -/
theorem block_getLsbD (l : List UInt8) (hl : l.length ≤ 64) (j : Fin 16) (i : ℕ) (hi : i < 32) :
    (block l)[j].toBitVec.getLsbD i = (l.getD (4 * j.val + i / 8) 0).toBitVec.getLsbD (i % 8) := by
  simp only [block, List.take_of_length_le hl]
  simp [hi]
  have ge : ∀ k, 8 ≤ k → ∀ x : UInt8, x.toBitVec.getLsbD k = false :=
    fun k hk x ↦ BitVec.getLsbD_of_ge _ _ hk
  rcases (by omega : i < 8 ∨ (8 ≤ i ∧ i < 16) ∨ (16 ≤ i ∧ i < 24) ∨ 24 ≤ i) with h | h | h | h
  · simp [h, Nat.div_eq_of_lt h, Nat.mod_eq_of_lt h, show i < 16 by omega, show i < 24 by omega]
  · simp [ge i (by omega), show ¬ i < 8 by omega, h.2, show i < 24 by omega,
      show i / 8 = 1 by omega, show i % 8 = i - 8 by omega]
  · simp [ge i (by omega), ge (i - 8) (by omega), show ¬ i < 8 by omega, show ¬ i < 16 by omega,
      h.2, show i / 8 = 2 by omega, show i % 8 = i - 16 by omega]
  · simp [ge i (by omega), ge (i - 8) (by omega), ge (i - 16) (by omega), show ¬ i < 8 by omega,
      show ¬ i < 16 by omega, show ¬ i < 24 by omega, show i / 8 = 3 by omega,
      show i % 8 = i - 24 by omega]

/-- A message block depends only on the first 64 bytes of its input, zero past the end. -/
theorem block_congr {l l' : List UInt8} (h : ∀ p < 64, l.getD p 0 = l'.getD p 0) :
    block l = block l' := by
  have ht : ∀ l : List UInt8, block l = block (l.take 64) := fun l ↦ by
    simp only [block, List.take_take, Nat.min_self]
  have hg : ∀ (l : List UInt8) p, p < 64 → (l.take 64).getD p 0 = l.getD p 0 := fun l p hp ↦ by
    simp [List.getD_eq_getElem?_getD, hp]
  rw [ht l, ht l']
  refine Vector.ext fun j hj ↦ UInt32.toBitVec_inj.mp (BitVec.eq_of_getLsbD_eq fun i hi ↦ ?_)
  have e := block_getLsbD (l.take 64) (List.length_take_le _ _) ⟨j, hj⟩ i hi
  have e' := block_getLsbD (l'.take 64) (List.length_take_le _ _) ⟨j, hj⟩ i hi
  simp only [Fin.getElem_fin] at e e'
  rw [e, e', hg _ _ (by omega), hg _ _ (by omega), h _ (by omega)]

theorem msgBytes_getD (w : Pos → Bool) {p : ℕ} (hp : p < 64) :
    (msgBytes w).getD p 0 = readByte w (msgBase + 8 * p) := by
  rw [msgBytes, List.getD_eq_getElem?_getD, List.getElem?_ofFn]
  simp [hp]

/-! ## Soundness of one block -/

/-- **One block.** A Boolean block satisfying the block R1CS over a nontrivial ring of
characteristic two, with `one = 1`, carries at `h_out` the compression of its `h_in`, its message
bytes, its counter and its flags. -/
theorem compress_sound {R : Type*} [CommRing R] [CharP R 2] [Nontrivial R] {w : Pos → Bool}
    (hz : circuitR1CS.Holds (liftBlock R w)) (h1 : w onePos = true)
    {h : Vector UInt32 8} {msg : Vector UInt32 16} {t : UInt64} {f0 f1 : UInt32}
    (hh : hIn w = h) (hm : block (msgBytes w) = msg) (ht0 : readWord w counterLo = t.toUInt32)
    (ht1 : readWord w counterHi = (t >>> 32).toUInt32) (hf0 : readWord w finalFlag = f0)
    (hf1 : readWord w lastNodeFlag = f1) : hOut w = compress h msg t f0 f1 := by
  have hmw : ∀ k : Fin 16, Den w (msgW k) msg[k] := fun k ↦ by
    refine den_inW fun i ↦ ?_
    rw [← hm, block_getLsbD (msgBytes w) List.length_ofFn.le k i i.isLt,
      msgBytes_getD _ (by omega), readByte_getLsbD _ _ (Nat.mod_lt _ (by omega))]
    congr 2
    simp only [msgBase]
    omega
  have hout := blake2s_sound w hz h1 (h := h) (msg := msg) (t := t) (f0 := f0) (f1 := f1)
    (fun k ↦ den_congr (den_readWord w _) (by
      rw [← hh, hIn, Fin.getElem_fin, Vector.getElem_ofFn]))
    hmw (den_congr (den_readWord w _) ht0) (den_congr (den_readWord w _) ht1)
    (den_congr (den_readWord w _) hf0) (den_congr (den_readWord w _) hf1)
  refine Vector.ext fun k hk ↦ ?_
  rw [hOut, Vector.getElem_ofFn]
  exact den_unique (den_readWord w _) (hout ⟨k, hk⟩)

/-! ## The public target -/

/-- A public target on a block: `tgt k = some b` pins position `k` (row `(0, 0)`) to the bit
`b`; `none` leaves the circuit's row. -/
abbrev Target := Pos → Option Bool

/-- The block R1CS with the target's positions as `(0, 0)` rows: `A₀`, `B₀` of BLUEPRINT §4. -/
noncomputable def blockR1CS (tgt : Target) : BlockR1CS Blake2sCircuit.m :=
  ⟨fun k j ↦ (tgt k).isNone && circuitR1CS.A k j, fun k j ↦ (tgt k).isNone && circuitR1CS.B k j⟩

/-- The public target `E` as a block over `R`: the pinned bit, `0` where nothing is pinned. -/
def targetVal (R : Type*) [CommRing R] (tgt : Target) (k : Pos) : R := ofBool R ((tgt k).getD false)

/-- The constraint with a public target: `(A z)_k · (B z)_k = z_k + E_k` at every position. -/
def HoldsE {R : Type*} [CommRing R] (C : BlockR1CS Blake2sCircuit.m) (E z : Pos → R) : Prop :=
  ∀ k, BlockR1CS.mulVec C.A z k * BlockR1CS.mulVec C.B z k = z k + E k

/-- A Boolean block meets a target: every pinned position holds its bit. -/
def MeetsB (tgt : Target) (w : Pos → Bool) : Prop := ∀ k b, tgt k = some b → w k = b

/-- A target of the entry pins `one` to `1` and otherwise only inputs of the circuit. -/
def TargetOk (tgt : Target) : Prop :=
  tgt onePos = some true ∧
    ∀ k b, tgt k = some b → k = onePos ∨ k.val < 256 ∨ (512 ≤ k.val ∧ k.val < 1152)

section Target

variable {R : Type*} [CommRing R] {tgt : Target}

private theorem mulVec_pinned {k : Pos} {b : Bool} (hk : tgt k = some b) (z : Pos → R) :
    BlockR1CS.mulVec (blockR1CS tgt).A z k = 0 ∧ BlockR1CS.mulVec (blockR1CS tgt).B z k = 0 := by
  simp [BlockR1CS.mulVec, blockR1CS, hk]

private theorem mulVec_free {k : Pos} (hk : tgt k = none) (z : Pos → R) :
    BlockR1CS.mulVec (blockR1CS tgt).A z k = BlockR1CS.mulVec circuitR1CS.A z k ∧
      BlockR1CS.mulVec (blockR1CS tgt).B z k = BlockR1CS.mulVec circuitR1CS.B z k := by
  simp [BlockR1CS.mulVec, blockR1CS, hk]

variable [CharP R 2] [Nontrivial R]

/-- **The target, soundness.** A Boolean block satisfying the block R1CS with a target of the
entry satisfies the circuit's R1CS, has `one = 1` and holds the target's bits. -/
theorem holdsE_sound (ht : TargetOk tgt) {w : Pos → Bool}
    (h : HoldsE (blockR1CS tgt) (targetVal R tgt) (liftBlock R w)) :
    circuitR1CS.Holds (liftBlock R w) ∧ w onePos = true ∧ MeetsB tgt w := by
  have hm : MeetsB tgt w := fun k b hk ↦ by
    have e := h k
    rw [(mulVec_pinned hk _).1, (mulVec_pinned hk _).2, mul_zero, targetVal, hk,
      Option.getD_some] at e
    have := eq_neg_of_add_eq_zero_left e.symm
    rw [CharTwo.neg_eq] at this
    exact ofBool_injective this
  have h1 : w onePos = true := hm _ _ ht.1
  refine ⟨fun k ↦ ?_, h1, hm⟩
  rcases hk : tgt k with _ | b
  · have e := h k
    rw [(mulVec_free hk _).1, (mulVec_free hk _).2, targetVal, hk] at e
    simpa [ofBool] using e
  · rcases ht.2 k b hk with rfl | hin
    · simp only [circuitR1CS]
      rw [mulVec_A_liftBlock, mulVec_B_liftBlock, rowOf_one]
      simp [liftBlock, h1, ofBool]
    · simp only [circuitR1CS]
      rw [mulVec_A_liftBlock, mulVec_B_liftBlock, rowOf_input hin]
      simp [liftBlock, h1, ofBool]

omit [Nontrivial R] in
/-- **The target, completeness.** A Boolean block satisfying the circuit's R1CS and holding the
bits of a target satisfies the block R1CS with that target. -/
theorem holdsE_complete {w : Pos → Bool}
    (hz : circuitR1CS.Holds (liftBlock R w)) (hm : MeetsB tgt w) :
    HoldsE (blockR1CS tgt) (targetVal R tgt) (liftBlock R w) := fun k ↦ by
  rcases hk : tgt k with _ | b
  · rw [(mulVec_free hk _).1, (mulVec_free hk _).2, targetVal, hk, hz k]
    simp [ofBool]
  · rw [(mulVec_pinned hk _).1, (mulVec_pinned hk _).2, mul_zero, targetVal, hk, Option.getD_some,
      liftBlock, hm k b hk, CharTwo.add_self_eq_zero]

/-- **Negative control (BP-C-M5).** The all-zero block, which satisfies the circuit's R1CS with
`one = 0` (`zero_holds`), does not satisfy the block R1CS with a target of the entry. -/
theorem zero_not_holdsE (ht : TargetOk tgt) :
    ¬ HoldsE (blockR1CS tgt) (targetVal R tgt) (fun _ ↦ (0 : R)) := fun h ↦ by
  have e : liftBlock R (fun _ : Pos ↦ false) = fun _ ↦ (0 : R) := by
    funext k; simp [liftBlock, ofBool]
  have := (holdsE_sound (w := fun _ ↦ false) ht (e ▸ h)).2.1
  simp at this

end Target

/-- **The walk of the block R1CS with a target.** The walk of the circuit with the row weights of
the pinned positions set to `0` computes the bilinear forms of `blockR1CS tgt`, for any row
weights `e` and column weights `wt`. -/
theorem walkE_eq_sum {R : Type} [CommRing R] [CharP R 2] (tgt : Target) (e wt : Pos → R) :
    walkAB (fun k ↦ if (tgt k).isNone then e k else 0) wt =
      (∑ k, e k * BlockR1CS.mulVec (blockR1CS tgt).A wt k,
        ∑ k, e k * BlockR1CS.mulVec (blockR1CS tgt).B wt k) := by
  have key : ∀ k, (if (tgt k).isNone then e k else 0) * BlockR1CS.mulVec circuitR1CS.A wt k =
        e k * BlockR1CS.mulVec (blockR1CS tgt).A wt k ∧
      (if (tgt k).isNone then e k else 0) * BlockR1CS.mulVec circuitR1CS.B wt k =
        e k * BlockR1CS.mulVec (blockR1CS tgt).B wt k := fun k ↦ by
    rcases hk : tgt k with _ | b
    · rw [(mulVec_free hk wt).1, (mulVec_free hk wt).2]
      simp only [Option.isNone_none, ↓reduceIte, and_self]
    · rw [(mulVec_pinned hk wt).1, (mulVec_pinned hk wt).2]
      simp only [Option.isNone_some, Bool.false_eq_true, ↓reduceIte, zero_mul, mul_zero, and_self]
  have hA : (fun k ↦ (if (tgt k).isNone then e k else 0) *
      BlockR1CS.mulVec blake2sCircuit.toBlockR1CS.A wt k) =
      fun k ↦ e k * BlockR1CS.mulVec (blockR1CS tgt).A wt k := funext fun k ↦ (key k).1
  have hB : (fun k ↦ (if (tgt k).isNone then e k else 0) *
      BlockR1CS.mulVec blake2sCircuit.toBlockR1CS.B wt k) =
      fun k ↦ e k * BlockR1CS.mulVec (blockR1CS tgt).B wt k := funext fun k ↦ (key k).2
  rw [walk_eq_sum, hA, hB]

/-- A word pinned by a target, read off a block meeting it. -/
theorem readWord_of_meets {tgt : Target} {w : Pos → Bool} (hm : MeetsB tgt w) {b : ℕ} {u : UInt32}
    (hp : ∀ i < 32, tgt (pos (b + i)) = some (u.toBitVec.getLsbD i)) : readWord w b = u :=
  UInt32.toBitVec_inj.mp (BitVec.eq_of_getLsbD_eq fun i hi ↦ by
    rw [readWord_getLsbD _ _ hi, hm _ _ (hp i hi)])

/-- A byte pinned by a target, read off a block meeting it. -/
theorem readByte_of_meets {tgt : Target} {w : Pos → Bool} (hm : MeetsB tgt w) {b : ℕ} {u : UInt8}
    (hp : ∀ i < 8, tgt (pos (b + i)) = some (u.toBitVec.getLsbD i)) : readByte w b = u :=
  UInt8.toBitVec_inj.mp (BitVec.eq_of_getLsbD_eq fun i hi ↦ by
    rw [readByte_getLsbD _ _ hi, hm _ _ (hp i hi)])

/-- Bit `j` of the eight words `h`: bit `j mod 32` of word `j / 32` (`false` past `256`). -/
def wordsBit (h : Vector UInt32 8) (j : ℕ) : Bool :=
  if hj : j < 256 then (h[j / 32]'(by omega)).toBitVec.getLsbD (j % 32) else false

/-- The chaining value pinned by a target at `0 … 255`, read off a block meeting it. -/
theorem hIn_of_meets {tgt : Target} {w : Pos → Bool} (hm : MeetsB tgt w) {h : Vector UInt32 8}
    (hp : ∀ j < 256, tgt (pos j) = some (wordsBit h j)) : hIn w = h := by
  refine Vector.ext fun k hk ↦ ?_
  rw [hIn, Vector.getElem_ofFn]
  refine readWord_of_meets hm fun i hi ↦ ?_
  rw [hp _ (by omega), wordsBit, dite_eq_left (by omega)]
  simp only [show (32 * k + i) / 32 = k by omega, show (32 * k + i) % 32 = i by omega]

/-- The chaining value a block holds, from its bits. -/
theorem hIn_of_bits {w : Pos → Bool} {h : Vector UInt32 8}
    (hb : ∀ j < 256, w (pos j) = wordsBit h j) : hIn w = h :=
  hIn_of_meets (tgt := fun k ↦ some (w k)) (fun _ _ hk ↦ Option.some.inj hk)
    fun j hj ↦ congrArg some (hb j hj)

/-- Bit `j` of the output words is the block's bit `256 + j`. -/
theorem hOut_bit (w : Pos → Bool) {j : ℕ} (hj : j < 256) :
    wordsBit (hOut w) j = w (pos (256 + j)) := by
  rw [wordsBit, dite_eq_left hj, hOut, Vector.getElem_ofFn, readWord_getLsbD _ _ (by omega)]
  congr 2
  simp only
  omega

/-! ## Blocks over a ring -/

section Ring

variable {R : Type*} [CommRing R] [DecidableEq R] [Nontrivial R]

/-- A `0`/`1` entry equal to `ofBool R b` holds the bit `b`. -/
theorem toBools_of_eq {z : Pos → R} {k : Pos} {b : Bool} (h : z k = ofBool R b) :
    toBools z k = b := by
  cases b <;> simp [toBools, h, ofBool]

omit [Nontrivial R] in
/-- Two `0`/`1` entries that are equal hold the same bit. -/
theorem toBools_congr {z z' : Pos → R} {k k' : Pos} (h : z k = z' k') :
    toBools z k = toBools z' k' := by
  simp [toBools, h]

end Ring

end Block

end FR

end G6_FRBlockLayout

section G6_FRBlockChain

-- New for `flock-recursive` (BLUEPRINT §4.1, Appendix A.6, revision 3.1). `stepWords`,
-- `chainStep_eq`, `not_holds_flip` and the known-answer controls are adapted from
-- `submissions/spartan-srom/lean/SpartanSromBlake2sR1CS.lean` (this repository, branch
-- `v4/flock-recursive` at `783328c`): there the constants were rows `(one, one)` of the block,
-- here they are `(0, 0)` rows pinned by the public target.

/-!
# The chain block (BLUEPRINT §4.1)

The chain step of the contract, `chainStep d = blake2sDigest (0x43 ‖ d)` (33 bytes), is one
compression: chaining value `h0`, message block `0x43 ‖ d ‖ 0^31`, counter `33`, the last-block flag
`0xFFFFFFFF`, the last-node flag `0` (`chainStep_eq`). The chain block is the block R1CS of
`FRBlockLayout` with the **public target** `chainTarget`, whose `(0, 0)` rows pin:

* `h_in = h0` (`0 … 255`), the tag byte `0x43` (`512 … 519`), the zero message bytes `33 … 63`
  (`776 … 1023`), `t_lo = 33`, `t_hi = 0`, `f0 = 0xFFFFFFFF`, `f1 = 0` (`1024 … 1151`), and
  `one = 1` (`1152`);
* free: the digest `d` being hashed, message bytes `1 … 32`, bits `520 … 775` (`dBase`).

Results:
* `block_sound`: a Boolean block satisfying the chain block's R1CS with its target
  (`HoldsE (blockR1CS chainTarget) (targetVal R chainTarget)`) carries at `256 … 511` the chain
  step of the digest at `520 … 775`;
* `block_complete`: the honest block of a digest (`chainTrace`) satisfies it and carries the digest
  and its chain step;
* controls: `chainStep_zero_kat` and `chainTrace_zero_kat` (positive: the contract's BLAKE2s on
  one block), `not_holds_flip` (negative: an output bit flipped breaks the R1CS),
  `zero_control` (negative, BP-C-M5: the all-zero block, which satisfies the circuit's R1CS
  with `one = 0`, fails the target).
-/

namespace FR

open RecursionFast RecursionFast.Blake2s ProductCircuit Blake2sCircuit Block

namespace Chain

/-! ## The chain step as one compression -/

/-- The first position of the digest a chain block hashes: message byte `1`, bit `520`. -/
abbrev dBase : ℕ := 520

/-- The compression that a chain step is: chaining value `h0`, message block `0x43 ‖ d`, counter
`33`, the last-block flag set and the last-node flag clear. -/
def stepWords (d : Digest) : Vector UInt32 8 :=
  compress h0 (block (tagChain :: d.toList)) 33 0xFFFFFFFF 0

/-- The chain step of the contract is one compression (`(33 - 1) / 64 = 0` blocks before the
final one), encoded little-endian. -/
theorem chainStep_eq (d : Digest) : chainStep d = leDigest (stepWords d) := by
  have hlen : (tagChain :: d.toList).length = 33 := by simp
  rw [chainStep, blake2sDigest_eq, hlen, show (33 - 1) / 64 = 0 from rfl, compressInput, hlen]
  rfl

/-! ## The target -/

/-- The public target of a chain block: `h_in = h0`, message byte `0` is `0x43`, message bytes
`33 … 63` are `0`, `t_lo = 33`, `t_hi = 0`, `f0 = 0xFFFFFFFF`, `f1 = 0`, `one = 1`. -/
def chainTarget (k : Pos) : Option Bool :=
  if k.val < 256 then some (wordsBit h0 k.val)
  else if k.val < 512 then none
  else if k.val < 520 then some (tagChain.toBitVec.getLsbD (k.val - 512))
  else if k.val < 776 then none
  else if k.val < 1024 then some false
  else if k.val < 1056 then some ((33 : UInt32).toBitVec.getLsbD (k.val - 1024))
  else if k.val < 1088 then some false
  else if k.val < 1120 then some true
  else if k.val < 1152 then some false
  else if k.val = 1152 then some true
  else none

private theorem pv {v : ℕ} (h : v < 16384) : ((pos v : Pos) : ℕ) = v := pos_val h

theorem pat_h0 : ∀ j < 256, chainTarget (pos j) = some (wordsBit h0 j) := fun j hj ↦ by
  rw [chainTarget, pv (by omega), ite_eq_left hj]

theorem pat_tag : ∀ i < 8, chainTarget (pos (msgBase + i)) = some (tagChain.toBitVec.getLsbD i) :=
  fun i hi ↦ by
    simp (disch := omega) only [chainTarget, msgBase, pv (show 512 + i < 16384 by omega),
      ite_eq_left, ite_eq_right, Nat.add_sub_cancel_left]

theorem pat_pad {v : ℕ} (h1 : 776 ≤ v) (h2 : v < 1024) : chainTarget (pos v) = some false := by
  simp (disch := omega) only [chainTarget, pv (show v < 16384 by omega), ite_eq_left,
    ite_eq_right]

theorem pat_tlo : ∀ i < 32, chainTarget (pos (counterLo + i)) =
    some ((33 : UInt64).toUInt32.toBitVec.getLsbD i) := fun i hi ↦ by
  simp (disch := omega) only [chainTarget, counterLo, pv (show 1024 + i < 16384 by omega),
    ite_eq_left, ite_eq_right, Nat.add_sub_cancel_left]
  rfl

theorem pat_zero {b : ℕ} (hb : b = counterHi ∨ b = lastNodeFlag) :
    ∀ i < 32, chainTarget (pos (b + i)) = some ((0 : UInt32).toBitVec.getLsbD i) := fun i hi ↦ by
  simp only [counterHi, lastNodeFlag] at hb
  simp only [chainTarget, pv (show b + i < 16384 by omega), UInt32.toBitVec_zero,
    BitVec.getLsbD_zero]
  rcases hb with rfl | rfl
  · simp (disch := omega) only [ite_eq_left, ite_eq_right]
  · simp (disch := omega) only [ite_eq_left, ite_eq_right]

private theorem ones_getLsbD : ∀ i : Fin 32, (0xFFFFFFFF : UInt32).toBitVec.getLsbD i = true := by
  decide

theorem pat_f0 : ∀ i < 32, chainTarget (pos (finalFlag + i)) =
    some ((0xFFFFFFFF : UInt32).toBitVec.getLsbD i) := fun i hi ↦ by
  simp (disch := omega) only [chainTarget, finalFlag, pv (show 1088 + i < 16384 by omega),
    ones_getLsbD ⟨i, hi⟩, ite_eq_left, ite_eq_right]

/-- The target pins `one` to `1` and otherwise only inputs. -/
theorem chainTarget_ok : TargetOk chainTarget := by
  refine ⟨by rw [chainTarget, onePos_val]; rfl, fun k b h ↦ ?_⟩
  rw [← Fin.val_inj, onePos_val]
  by_contra hk
  rcases Nat.lt_or_ge k.val 512 with h2 | h2
  · rw [chainTarget, ite_eq_right (by omega), ite_eq_left h2] at h
    cases h
  · simp (disch := omega) only [chainTarget, ite_eq_right, reduceCtorEq] at h

/-- The target pins bit `0` to `1` (bit `0` of `h0`). -/
theorem chainTarget_zero : chainTarget (pos 0) = some true := by
  rw [pat_h0 0 (by omega)]
  rfl

/-! ## Soundness -/

/-- The gate-level form of `block_sound`: the circuit's R1CS, `one = 1`, the target's bits. -/
theorem block_sound_circuit {R : Type*} [CommRing R] [CharP R 2] [Nontrivial R] {w : Pos → Bool}
    (hz : circuitR1CS.Holds (liftBlock R w)) (h1 : w onePos = true) (hp : MeetsB chainTarget w) :
    readDigest w 256 = chainStep (readDigest w dBase) := by
  rw [readDigest_hOut, chainStep_eq, stepWords]
  congr 1
  refine compress_sound hz h1 (hIn_of_meets hp pat_h0) ?_ (readWord_of_meets hp pat_tlo)
    (readWord_of_meets hp (pat_zero (Or.inl rfl))) (readWord_of_meets hp pat_f0)
    (readWord_of_meets hp (pat_zero (Or.inr rfl)))
  refine block_congr fun p hp64 ↦ ?_
  rw [msgBytes_getD _ hp64]
  rcases Nat.eq_zero_or_pos p with rfl | hp0
  · rw [List.getD_cons_zero, Nat.mul_zero, Nat.add_zero]
    exact readByte_of_meets hp pat_tag
  · obtain ⟨q, rfl⟩ : ∃ q, p = q + 1 := ⟨p - 1, by omega⟩
    rw [List.getD_cons_succ]
    rcases Nat.lt_or_ge q 32 with hq | hq
    · rw [List.getD_eq_getElem _ _ (by simp; omega), Vector.getElem_toList, readDigest,
        Vector.getElem_ofFn]
      congr 1
      simp only [msgBase, dBase]
      omega
    · rw [List.getD_eq_default _ _ (by simp; omega)]
      exact readByte_of_meets hp fun i hi ↦ by
        rw [UInt8.toBitVec_zero, BitVec.getLsbD_zero]
        exact pat_pad (by simp only [msgBase]; omega) (by simp only [msgBase]; omega)

/-- **The chain block, soundness.** A Boolean block satisfying the chain block's R1CS with its
public target, over a nontrivial ring of characteristic two, carries at `256 … 511` the chain step
of the digest it carries at `520 … 775`. -/
theorem block_sound {R : Type*} [CommRing R] [CharP R 2] [Nontrivial R] {w : Pos → Bool}
    (h : HoldsE (blockR1CS chainTarget) (targetVal R chainTarget) (liftBlock R w)) :
    readDigest w 256 = chainStep (readDigest w dBase) :=
  have h' := holdsE_sound chainTarget_ok h
  block_sound_circuit h'.1 h'.2.1 h'.2.2

/-! ## Completeness -/

/-- The input block of the chain step from `d`: the target's bits where it pins, the digest's
bits at `520 … 775`, `0` elsewhere. -/
def chainInp (d : Digest) (k : Pos) : Bool :=
  match chainTarget k with
  | some b => b
  | none => if dBase ≤ k.val ∧ k.val < dBase + 256 then digestBit d (k.val - dBase) else false

/-- The honest chain block of `d`: the trace of the block circuit on `chainInp d`. -/
noncomputable def chainTrace (d : Digest) : Pos → Bool := blake2sCircuit.traceF (chainInp d)

/-- The trace keeps every input. -/
theorem chainTrace_input (d : Digest) {k : Pos} (hk : k.val < 256 ∨ (512 ≤ k.val ∧ k.val < 1152)) :
    chainTrace d k = chainInp d k :=
  traceF_input bounded_blake2s _
    (by rw [blake2sCircuit_inputs, getLsbD_inputs]; exact decide_eq_true hk)
    (by rw [blake2sCircuit_cpos]; exact Fin.ne_of_val_ne (by rw [constPos_val]; omega))

/-- **The chain block, completeness.** Over a nontrivial ring of characteristic two, the honest
block of a digest satisfies the chain block's R1CS with its target, carries the digest at
`520 … 775` and its chain step at `256 … 511`. -/
theorem block_complete {R : Type*} [CommRing R] [CharP R 2] [Nontrivial R] (d : Digest) :
    HoldsE (blockR1CS chainTarget) (targetVal R chainTarget) (liftBlock R (chainTrace d)) ∧
      readDigest (chainTrace d) dBase = d ∧ readDigest (chainTrace d) 256 = chainStep d := by
  have hs : circuitR1CS.Holds (liftBlock R (chainTrace d)) :=
    (trace_satisfies (R := R) bounded_blake2s (chainInp d)).1
  have h1 : chainTrace d onePos = true := by
    rw [chainTrace, onePos, ← blake2sCircuit_cpos]; exact traceF_cpos bounded_blake2s _
  have hp : MeetsB chainTarget (chainTrace d) := fun k b hk ↦ by
    rcases chainTarget_ok.2 k b hk with rfl | hin
    · exact Option.some.inj (chainTarget_ok.1.symm.trans hk) ▸ h1
    · rw [chainTrace_input d hin, chainInp, hk]
  have hd : readDigest (chainTrace d) dBase = d := by
    refine (readDigest_eq_iff _ _ _).mpr fun j hj ↦ ?_
    have hv : dBase + j < 16384 := by simp only [dBase]; omega
    rw [chainTrace_input d (by rw [pv hv]; simp only [dBase]; omega), chainInp]
    simp (disch := omega) only [chainTarget, pv hv, dBase, ite_eq_left, ite_eq_right,
      Nat.add_sub_cancel_left]
  refine ⟨holdsE_complete hs hp, hd, ?_⟩
  rw [block_sound_circuit hs h1 hp, hd]

/-! ## Controls -/

/-- **Positive control (kernel-checked).** The chain step of the zero digest, i.e. the contract's
BLAKE2s-256 of `0x43 ‖ 0^32` (Python's `hashlib.blake2s`). -/
theorem chainStep_zero_kat : chainStep (Vector.replicate 32 0) =
    #v[0x95, 0x4a, 0xc2, 0xa4, 0xd6, 0xa7, 0x90, 0x03, 0x28, 0x4c, 0x9e, 0x3f, 0x09, 0xf5, 0x9d,
        0x21,
      0x8e, 0xa7, 0x53, 0x8f, 0x69, 0x63, 0x1c, 0xab, 0x53, 0x12, 0x4a, 0xe6, 0xcd, 0x41, 0x8d,
          0x8d]
    := by decide +kernel

/-- **Positive control.** The honest chain block of the zero digest satisfies the block R1CS and
carries the known answer of the contract's BLAKE2s at its output positions. -/
theorem chainTrace_zero_kat {R : Type*} [CommRing R] [CharP R 2] [Nontrivial R] :
    HoldsE (blockR1CS chainTarget) (targetVal R chainTarget)
        (liftBlock R (chainTrace (Vector.replicate 32 0))) ∧
      readDigest (chainTrace (Vector.replicate 32 0)) 256 =
        #v[0x95, 0x4a, 0xc2, 0xa4, 0xd6, 0xa7, 0x90, 0x03, 0x28, 0x4c, 0x9e, 0x3f, 0x09, 0xf5,
          0x9d, 0x21, 0x8e, 0xa7, 0x53, 0x8f, 0x69, 0x63, 0x1c, 0xab, 0x53, 0x12, 0x4a, 0xe6, 0xcd,
          0x41, 0x8d, 0x8d] := by
  obtain ⟨h, -, ho⟩ := block_complete (R := R) (Vector.replicate 32 0)
  exact ⟨h, ho.trans chainStep_zero_kat⟩

/-- **Negative control.** Flipping any output bit of a block satisfying the chain block's R1CS
with its target breaks it (over a nontrivial ring of characteristic two). With `block_complete`,
this applies to every honest block. -/
theorem not_holds_flip {R : Type*} [CommRing R] [CharP R 2] [Nontrivial R] (w : Pos → Bool)
    (hz : HoldsE (blockR1CS chainTarget) (targetVal R chainTarget) (liftBlock R w))
    (k : Pos) (hk : 256 ≤ k.val ∧ k.val < 512) :
    ¬ HoldsE (blockR1CS chainTarget) (targetVal R chainTarget)
      (liftBlock R (Function.update w k (!w k))) := by
  intro hz'
  have hne : ∀ {j : Pos}, j.val < 256 ∨ 512 ≤ j.val → j ≠ k := fun hj h ↦ by
    rw [h] at hj; omega
  have hin : readDigest (Function.update w k (!w k)) dBase = readDigest w dBase :=
    readDigest_congr fun e he i hi ↦ by
      have hv : dBase + 8 * e + i < 16384 := by simp only [dBase]; omega
      rw [Function.update_of_ne (hne (by rw [pv hv]; simp only [dBase]; omega))]
  have hout := block_sound hz'
  rw [hin, ← block_sound hz] at hout
  have hb := congrArg (fun d : Digest ↦ (d[(k.val - 256) / 8]'(by omega)).toBitVec.getLsbD
    ((k.val - 256) % 8)) hout
  rw [readDigest_getLsbD _ _ _ (by omega) (Nat.mod_lt _ (by omega)),
    readDigest_getLsbD _ _ _ (by omega) (Nat.mod_lt _ (by omega))] at hb
  have hpk : (pos (256 + 8 * ((k.val - 256) / 8) + (k.val - 256) % 8) : Pos) = k :=
    Fin.ext (by rw [pv (by omega)]; omega)
  simp only [hpk, Function.update_self] at hb
  cases w k <;> simp at hb

/-- **Negative control (BP-C-M5).** The all-zero block satisfies the circuit's R1CS (with
`one = 0`) but not the chain block's R1CS with its target. -/
theorem zero_control {R : Type*} [CommRing R] [CharP R 2] [Nontrivial R] :
    circuitR1CS.Holds (fun _ : Pos ↦ (0 : R)) ∧
      ¬ HoldsE (blockR1CS chainTarget) (targetVal R chainTarget) (fun _ ↦ (0 : R)) :=
  ⟨zero_holds, zero_not_holdsE chainTarget_ok⟩

end Chain

end FR

end G6_FRBlockChain

section G6_FRBlockStream

-- New for `flock-recursive` (BLUEPRINT §1.2, §4.2, Appendix A.2, A.6, revision 3.1).

/-!
# The stream block and the digest chain (BLUEPRINT §4.2)

**The digest chain** of a byte string `B` of length `L` (`blake2s_chain`, kernel-checked against the
contract's BLAKE2s): `N = nBlocks L = ⌊(L − 1)/64⌋ + 1` compressions from `h0`,
`hᵢ₊₁ = compress hᵢ (block (B.drop 64i)) (ctrAt L i) (flagAt L i) 0`, where the counter is `64(i+1)`
and the flag `0` except at the last block (`L`, `0xFFFFFFFF`); `blake2sDigest B = le h_N`. The
contract's trace digest is the case `B = 0x54 ‖ traceBytes tr` (`traceDigest_chain`).

**The stream block** is the block R1CS of `FRBlockLayout` with the public target
`streamTarget L i` of block `i` of a stream of length `L` (BLUEPRINT revision 3.1, §4.2): `(0, 0)`
rows pin the counter `ctrAt L i` in `t_lo`, `t_hi`, the flag `flagAt L i` in `f0`, `f1 = 0` and
`one = 1`; `h_in` and the message are inputs. Block `i` holds stream bytes `[64i, 64i + 64)` in its
message slots: stream byte `p` is message byte `p mod 64` of block `⌊p/64⌋` (`streamBytes`), so the
stream's 16-byte element `e` is message slot `4 + e mod 4` of block `⌊e/4⌋` (`elem_slot`).

Results:
* `block_sound_gen`: a Boolean block satisfying the block R1CS with the target `blockTarget t fin`
  (any counter `t`, any final flag) carries the compression of its `h_in` and message with that
  counter and flag; `block_sound` is the case of block `i` of a stream (for the node's statement
  hash, the cases `(41, final)`, `(64, ¬ final)`, `(65, final)`);
* `stream_sound`: `N` such blocks, starting from `h_in = h0`, linked `h_out(i) = h_in(i+1)` (both
  the shift argument's content) and zero past `L` bytes (`Padded`: point claims on `f`), carry at
  the last block's `h_out` the contract's `blake2sDigest` of the bytes in their message slots;
  `stream_traceDigest`: when those bytes are `0x54 ‖ traceBytes tr`, it is `traceDigest tr`;
* `item_aligned`: with the first query `≡ 7 mod 16` and the others `≡ 8 mod 16`, every item after
  the first starts at an offset `≡ 0 mod 16` of `0x54 ‖ traceBytes` (item starts only, S-E1-m1);
* controls: `stream_complete` (the honest blocks of any stream meet every hypothesis of
  `stream_sound`), `zero_control` (the all-zero block fails the target).
-/

namespace FR

open RecursionFast RecursionFast.Blake2s ProductCircuit Blake2sCircuit Block

namespace Stream

/-! ## The digest chain of a byte string -/

/-- The number of compressions of an input of `L` bytes, `max 1 ⌈L/64⌉` (RFC 7693 §3.3). -/
def nBlocks (L : ℕ) : ℕ := (L - 1) / 64 + 1

/-- The counter of compression `i` of an input of `L` bytes: `64 (i + 1)`, or `L` at the last. -/
def ctrAt (L i : ℕ) : ℕ := if i + 1 = nBlocks L then L else 64 * (i + 1)

/-- The last-block flag of compression `i`: `0xFFFFFFFF` at the last, else `0`. -/
def flagAt (L i : ℕ) : UInt32 := if i + 1 = nBlocks L then 0xFFFFFFFF else 0

/-- The chaining value after `j` compressions of `B`. -/
def chainState (B : List UInt8) : ℕ → Vector UInt32 8
  | 0 => h0
  | j + 1 => compress (chainState B j) (block (B.drop (64 * j))) (ctrAt B.length j).toUInt64
      (flagAt B.length j) 0

/-- RFC 7693's block loop from compression `j` on is the chain from `j`. -/
theorem compressInput_eq (B : List UInt8) :
    ∀ n j, j + n + 1 = nBlocks B.length →
      compressInput (chainState B j) (64 * j) (B.drop (64 * j)) n = chainState B (j + n + 1) := by
  intro n
  induction n with
  | zero =>
    intro j hj
    have hL : 64 * j + (B.drop (64 * j)).length = B.length := by
      simp only [List.length_drop, nBlocks] at hj ⊢
      omega
    rw [compressInput, hL, Nat.add_zero, chainState, ctrAt, flagAt, ite_eq_left hj, ite_eq_left hj]
  | succ n ih =>
    intro j hj
    have hne : ¬ j + 1 = nBlocks B.length := by omega
    rw [compressInput, List.drop_drop, show 64 * j + 64 = 64 * (j + 1) by omega]
    have hs : compress (chainState B j) (block (B.drop (64 * j))) (64 * (j + 1)).toUInt64 0 0 =
        chainState B (j + 1) := by
      rw [chainState, ctrAt, flagAt, ite_eq_right hne, ite_eq_right hne]
    rw [hs, ih (j + 1) (by omega)]
    congr 1
    omega

/-- **The digest chain.** The contract's BLAKE2s-256 of a byte string is the little-endian encoding
of the chaining value after its `nBlocks` compressions. -/
theorem blake2s_chain (B : List UInt8) :
    blake2sDigest B = leDigest (chainState B (nBlocks B.length)) := by
  have h := compressInput_eq B ((B.length - 1) / 64) 0 (by simp [nBlocks])
  rw [show chainState B 0 = h0 from rfl, Nat.mul_zero, List.drop_zero, Nat.zero_add] at h
  rw [blake2sDigest_eq, h, nBlocks]

/-- **The trace digest** is the digest chain of `0x54 ‖ traceBytes tr`. -/
theorem traceDigest_chain (tr : Trace) :
    traceDigest tr = leDigest (chainState (tagTrace :: traceBytes tr)
      (nBlocks (tagTrace :: traceBytes tr).length)) :=
  blake2s_chain _

/-! ## The stream block -/

/-- The last-block flag word: `0xFFFFFFFF` for a final block, `0` otherwise. -/
def flagOf (fin : Bool) : UInt32 := if fin then 0xFFFFFFFF else 0

theorem flagAt_eq (L i : ℕ) : flagAt L i = flagOf (decide (i + 1 = nBlocks L)) := by
  unfold flagAt flagOf
  split_ifs <;> simp_all

/-- The public target of a stream block with counter `t` and final flag `fin`: `t` in `t_lo`,
`t_hi`, `flagOf fin` in `f0`, `f1 = 0`, `one = 1`; `h_in` and the message are inputs. Block `i` of
a stream of `L` bytes uses `(ctrAt L i, i + 1 = nBlocks L)` (`streamTarget`); the node's statement
hash uses `(41, final)`, `(64, ¬ final)`, `(65, final)` (BLUEPRINT §4.2). -/
def blockTarget (t : ℕ) (fin : Bool) (k : Pos) : Option Bool :=
  if k.val < 1024 then none
  else if k.val < 1056 then some (t.toUInt64.toUInt32.toBitVec.getLsbD (k.val - 1024))
  else if k.val < 1088 then some ((t.toUInt64 >>> 32).toUInt32.toBitVec.getLsbD (k.val - 1056))
  else if k.val < 1120 then some fin
  else if k.val < 1152 then some false
  else if k.val = 1152 then some true
  else none

/-- The public target of block `i` of a stream of `L` bytes. -/
def streamTarget (L i : ℕ) : Target := blockTarget (ctrAt L i) (decide (i + 1 = nBlocks L))

private theorem pv {v : ℕ} (h : v < 16384) : ((pos v : Pos) : ℕ) = v := pos_val h

section Pins

variable {t : ℕ} {fin : Bool}

theorem pat_tlo : ∀ j < 32, blockTarget t fin (pos (counterLo + j)) =
    some (t.toUInt64.toUInt32.toBitVec.getLsbD j) := fun j hj ↦ by
  simp (disch := omega) only [blockTarget, counterLo, pv (show 1024 + j < 16384 by omega),
    ite_eq_left, ite_eq_right, Nat.add_sub_cancel_left]

theorem pat_thi : ∀ j < 32, blockTarget t fin (pos (counterHi + j)) =
    some ((t.toUInt64 >>> 32).toUInt32.toBitVec.getLsbD j) := fun j hj ↦ by
  simp (disch := omega) only [blockTarget, counterHi, pv (show 1056 + j < 16384 by omega),
    ite_eq_left, ite_eq_right, Nat.add_sub_cancel_left]

private theorem ones_getLsbD : ∀ i : Fin 32, (0xFFFFFFFF : UInt32).toBitVec.getLsbD i = true := by
  decide

theorem pat_f0 : ∀ j < 32, blockTarget t fin (pos (finalFlag + j)) =
    some ((flagOf fin).toBitVec.getLsbD j) := fun j hj ↦ by
  simp (disch := omega) only [blockTarget, finalFlag, pv (show 1088 + j < 16384 by omega),
    ite_eq_left, ite_eq_right]
  cases fin
  · simp [flagOf]
  · rw [flagOf, ite_eq_left rfl, ones_getLsbD ⟨j, hj⟩]

theorem pat_f1 : ∀ j < 32, blockTarget t fin (pos (lastNodeFlag + j)) =
    some ((0 : UInt32).toBitVec.getLsbD j) := fun j hj ↦ by
  simp (disch := omega) only [blockTarget, lastNodeFlag, pv (show 1120 + j < 16384 by omega),
    UInt32.toBitVec_zero, BitVec.getLsbD_zero, ite_eq_left, ite_eq_right]

/-- The target pins `one` to `1` and otherwise only inputs (`t`, `f`). -/
theorem blockTarget_ok : TargetOk (blockTarget t fin) := by
  refine ⟨by rw [blockTarget, onePos_val]; rfl, fun k b h ↦ ?_⟩
  rw [← Fin.val_inj, onePos_val]
  by_contra hk
  rcases Nat.lt_or_ge k.val 1024 with h2 | h2
  · rw [blockTarget, ite_eq_left h2] at h
    cases h
  · simp (disch := omega) only [blockTarget, ite_eq_right, reduceCtorEq] at h

/-- The target pins no position below `1024` (`h_in`, `h_out`, the message). -/
theorem blockTarget_low {k : Pos} (hk : k.val < 1024) : blockTarget t fin k = none := by
  rw [blockTarget, ite_eq_left hk]

/-- **A stream block, soundness.** A Boolean block satisfying the block R1CS with the target of
counter `t` and final flag `fin`, over a nontrivial ring of characteristic two, carries at `h_out`
the compression of its `h_in` and its message with that counter and flag. -/
theorem block_sound_gen {R : Type*} [CommRing R] [CharP R 2] [Nontrivial R] {w : Pos → Bool}
    (h : HoldsE (blockR1CS (blockTarget t fin)) (targetVal R (blockTarget t fin)) (liftBlock R w)) :
    hOut w = compress (hIn w) (block (msgBytes w)) t.toUInt64 (flagOf fin) 0 :=
  have ⟨hz, h1, hp⟩ := holdsE_sound blockTarget_ok h
  compress_sound hz h1 rfl rfl (readWord_of_meets hp pat_tlo) (readWord_of_meets hp pat_thi)
    (readWord_of_meets hp pat_f0) (readWord_of_meets hp pat_f1)

end Pins

theorem streamTarget_ok {L i : ℕ} : TargetOk (streamTarget L i) := blockTarget_ok

theorem streamTarget_low {L i : ℕ} {k : Pos} (hk : k.val < 1024) : streamTarget L i k = none :=
  blockTarget_low hk

/-- **The stream block, soundness.** A Boolean block satisfying the block R1CS with the target of
block `i` of a stream of `L` bytes carries at `h_out` the compression of its `h_in` and its message
with that block's counter and flag. -/
theorem block_sound {R : Type*} [CommRing R] [CharP R 2] [Nontrivial R] {L i : ℕ} {w : Pos → Bool}
    (h : HoldsE (blockR1CS (streamTarget L i)) (targetVal R (streamTarget L i)) (liftBlock R w)) :
    hOut w = compress (hIn w) (block (msgBytes w)) (ctrAt L i).toUInt64 (flagAt L i) 0 := by
  rw [block_sound_gen h, flagAt_eq]

/-! ## A stream of blocks -/

/-- The stream a family of blocks holds in its message slots: byte `p < L` is message byte
`p mod 64` of block `⌊p / 64⌋`. -/
def streamBytes (w : ℕ → Pos → Bool) (L : ℕ) : List UInt8 :=
  (List.range L).map fun p ↦ readByte (w (p / 64)) (msgBase + 8 * (p % 64))

theorem streamBytes_length (w : ℕ → Pos → Bool) (L : ℕ) : (streamBytes w L).length = L := by
  simp [streamBytes]

/-- The 16-byte element `e` of the stream (bytes `16e … 16e + 15`) is message slot `4 + e mod 4`
(bits `128 (4 + e mod 4) …`) of block `⌊e / 4⌋`: the address rule of BLUEPRINT §4.2. -/
theorem elem_slot (e r : ℕ) (hr : r < 16) :
    (16 * e + r) / 64 = e / 4 ∧ msgBase + 8 * ((16 * e + r) % 64) = 128 * (4 + e % 4) + 8 * r := by
  simp only [msgBase]
  omega

/-- The stream's padding: the message bytes of its blocks past its `L` bytes are `0`. -/
def Padded (w : ℕ → Pos → Bool) (L : ℕ) : Prop :=
  ∀ p, L ≤ p → p < 64 * nBlocks L → readByte (w (p / 64)) (msgBase + 8 * (p % 64)) = 0

/-- The message bytes of block `i` of a padded stream are the stream's bytes from `64 i`, zero
past its end. -/
theorem msg_eq {L i : ℕ} {w : ℕ → Pos → Bool} (hpad : Padded w L) (hi : i < nBlocks L) :
    block (msgBytes (w i)) = block ((streamBytes w L).drop (64 * i)) := by
  refine block_congr fun p hp64 ↦ ?_
  rw [msgBytes_getD _ hp64, List.getD_eq_getElem?_getD, List.getElem?_drop]
  rcases Nat.lt_or_ge (64 * i + p) L with hlt | hge
  · rw [List.getElem?_eq_getElem (by rw [streamBytes_length]; omega), Option.getD_some]
    simp only [streamBytes, List.getElem_map, List.getElem_range]
    rw [show (64 * i + p) / 64 = i by omega, show (64 * i + p) % 64 = p by omega]
  · rw [List.getElem?_eq_none (by rw [streamBytes_length]; omega), Option.getD_none]
    have := hpad (64 * i + p) hge (by omega)
    rwa [show (64 * i + p) / 64 = i by omega, show (64 * i + p) % 64 = p by omega] at this

/-- **A stream of blocks.** `N = nBlocks L` Boolean blocks satisfying the block R1CS with their
stream targets, starting from `h_in = h0`, linked `h_out(i) = h_in(i + 1)` (the shift argument's
content) and padded with zeros past `L` bytes (point claims), carry at the last block's `h_out`
the contract's BLAKE2s-256 of the `L` bytes in their message slots. -/
theorem stream_sound {R : Type*} [CommRing R] [CharP R 2] [Nontrivial R] (L : ℕ)
    (w : ℕ → Pos → Bool)
    (hE : ∀ i < nBlocks L,
      HoldsE (blockR1CS (streamTarget L i)) (targetVal R (streamTarget L i)) (liftBlock R (w i)))
    (hstart : ∀ j < 256, w 0 (pos j) = wordsBit h0 j)
    (hl : ∀ i, i + 1 < nBlocks L → ∀ j < 256, w (i + 1) (pos j) = w i (pos (256 + j)))
    (hpad : Padded w L) :
    readDigest (w (nBlocks L - 1)) 256 = blake2sDigest (streamBytes w L) := by
  set B := streamBytes w L with hB
  have hBl : B.length = L := streamBytes_length w L
  have hs : ∀ j, chainState B (j + 1) =
      compress (chainState B j) (block (B.drop (64 * j))) (ctrAt L j).toUInt64 (flagAt L j) 0 :=
    fun j ↦ by rw [chainState, hBl]
  have key : ∀ i < nBlocks L, hIn (w i) = chainState B i ∧ hOut (w i) = chainState B (i + 1) := by
    intro i
    induction i with
    | zero =>
      intro h0'
      have hin : hIn (w 0) = chainState B 0 := hIn_of_bits hstart
      refine ⟨hin, ?_⟩
      rw [block_sound (hE 0 h0'), hin, msg_eq hpad h0', ← hB]
      exact (hs 0).symm
    | succ i ih =>
      intro hi
      have hin : hIn (w (i + 1)) = chainState B (i + 1) := hIn_of_bits fun j hj ↦ by
        rw [hl i hi j hj, ← hOut_bit (w i) hj, (ih (by omega)).2]
      refine ⟨hin, ?_⟩
      rw [block_sound (hE _ hi), hin, msg_eq hpad hi, ← hB]
      exact (hs (i + 1)).symm
  have hN : nBlocks L - 1 + 1 = nBlocks L := by simp [nBlocks]
  rw [readDigest_hOut, (key _ (by simp [nBlocks])).2, hN, blake2s_chain, hBl]

/-- **The trace digest of a stream.** When the stream in the blocks' message slots is
`0x54 ‖ traceBytes tr`, the last block's `h_out` carries `traceDigest tr`. -/
theorem stream_traceDigest {R : Type*} [CommRing R] [CharP R 2] [Nontrivial R] (L : ℕ)
    (w : ℕ → Pos → Bool)
    (hE : ∀ i < nBlocks L,
      HoldsE (blockR1CS (streamTarget L i)) (targetVal R (streamTarget L i)) (liftBlock R (w i)))
    (hstart : ∀ j < 256, w 0 (pos j) = wordsBit h0 j)
    (hl : ∀ i, i + 1 < nBlocks L → ∀ j < 256, w (i + 1) (pos j) = w i (pos (256 + j)))
    (hpad : Padded w L) (tr : Trace) (htr : streamBytes w L = tagTrace :: traceBytes tr) :
    readDigest (w (nBlocks L - 1)) 256 = traceDigest tr := by
  rw [stream_sound L w hE hstart hl hpad, htr, traceDigest]

/-! ## Alignment of the hashed trace (BLUEPRINT §1.2, A.2) -/

/-- The bytes of one trace item: `enc64 |q| ‖ q ‖ a`. -/
theorem traceBytes_cons (e : ByteArray × Digest) (tr : Trace) :
    traceBytes (e :: tr) = enc64 e.1.size ++ e.1.data.toList ++ e.2.toList ++ traceBytes tr := by
  simp [traceBytes, List.append_assoc]

theorem traceBytes_length_cons (e : ByteArray × Digest) (tr : Trace) :
    (traceBytes (e :: tr)).length = 8 + e.1.size + 32 + (traceBytes tr).length := by
  rw [traceBytes_cons]
  simp only [List.length_append, enc64, List.length_ofFn, Array.length_toList, ByteArray.size_data,
    Vector.length_toList]

/-- **Alignment of item starts.** If the first query has size `≡ 7 mod 16` and every other query
`≡ 8 mod 16`, then in the stream `0x54 ‖ traceBytes tr` every item after the first starts at an
offset `≡ 0 mod 16`. (The first conjunct is only the arithmetic `1 + 8 + 7 = 16`. Payload and
answer offsets follow from A.2's tag lengths, 7 then 8 bytes, which this lemma does not state;
those size facts are `FRFormat`/`FRVIRSpec` obligations, S-E1-m1.) -/
theorem item_aligned (e₀ : ByteArray × Digest) (rest : Trace) (h₀ : e₀.1.size % 16 = 7)
    (hr : ∀ e ∈ rest, e.1.size % 16 = 8) :
    1 + 8 + 7 = 16 ∧ ∀ k ≤ rest.length,
      (1 + (traceBytes (e₀ :: rest.take k)).length) % 16 = 0 := by
  refine ⟨rfl, fun k _ ↦ ?_⟩
  rw [traceBytes_length_cons]
  suffices h : ∀ (l : Trace), (∀ e ∈ l, e.1.size % 16 = 8) → (traceBytes l).length % 16 = 0 by
    have := h (rest.take k) fun e he ↦ hr e (List.mem_of_mem_take he)
    omega
  intro l hl
  induction l with
  | nil => simp [traceBytes]
  | cons e l ih =>
    rw [traceBytes_length_cons]
    have := hl e List.mem_cons_self
    have := ih fun e he ↦ hl e (List.mem_cons_of_mem _ he)
    omega

/-! ## Completeness of a stream (a control) -/

/-- The input of block `i` of the stream `B`: the target's bits where it pins; the chaining value
`chainState B i` at `h_in`; the stream's bytes `[64 i, 64 i + 64)` in the message, zero past its
end. -/
def streamInp (B : List UInt8) (i : ℕ) (k : Pos) : Bool :=
  match streamTarget B.length i k with
  | some b => b
  | none =>
    if k.val < 256 then wordsBit (chainState B i) k.val
    else if msgBase ≤ k.val ∧ k.val < msgBase + 512 then
      (B.getD (64 * i + (k.val - msgBase) / 8) 0).toBitVec.getLsbD ((k.val - msgBase) % 8)
    else false

/-- The honest block `i` of the stream `B`. -/
noncomputable def streamTrace (B : List UInt8) (i : ℕ) : Pos → Bool :=
  blake2sCircuit.traceF (streamInp B i)

private theorem streamTrace_input (B : List UInt8) (i : ℕ) {k : Pos}
    (hk : k.val < 256 ∨ (512 ≤ k.val ∧ k.val < 1152)) : streamTrace B i k = streamInp B i k :=
  traceF_input bounded_blake2s _
    (by rw [blake2sCircuit_inputs, getLsbD_inputs]; exact decide_eq_true hk)
    (by rw [blake2sCircuit_cpos]; exact Fin.ne_of_val_ne (by rw [constPos_val]; omega))

private theorem streamTrace_hIn_bit (B : List UInt8) (i : ℕ) {j : ℕ} (hj : j < 256) :
    streamTrace B i (pos j) = wordsBit (chainState B i) j := by
  have hv : ((pos j : Pos) : ℕ) = j := pv (by omega)
  rw [streamTrace_input _ _ (by rw [hv]; omega), streamInp,
    streamTarget_low (by rw [hv]; omega), hv, ite_eq_left hj]

private theorem streamTrace_byte (B : List UInt8) (i : ℕ) {p : ℕ} (hp : p < 64) :
    readByte (streamTrace B i) (msgBase + 8 * p) = B.getD (64 * i + p) 0 := by
  refine UInt8.toBitVec_inj.mp (BitVec.eq_of_getLsbD_eq fun b hb ↦ ?_)
  have hv : msgBase + 8 * p + b < 16384 := by simp only [msgBase]; omega
  rw [readByte_getLsbD _ _ hb, streamTrace_input _ _ (by rw [pv hv]; simp only [msgBase]; omega),
    streamInp, streamTarget_low (by rw [pv hv]; simp only [msgBase]; omega), pv hv,
    ite_eq_right (by simp only [msgBase]; omega), ite_eq_left (by simp only [msgBase]; omega)]
  have e1 : (msgBase + 8 * p + b - msgBase) / 8 = p := by simp only [msgBase]; omega
  have e2 : (msgBase + 8 * p + b - msgBase) % 8 = b := by simp only [msgBase]; omega
  rw [e1, e2]

/-- **Stream completeness (a control).** The honest blocks of a stream `B` satisfy every
hypothesis of `stream_sound` for `L = |B|` and hold `B` in their message slots; so
`stream_sound`'s hypotheses are satisfiable for every stream. -/
theorem stream_complete {R : Type*} [CommRing R] [CharP R 2] [Nontrivial R] (B : List UInt8) :
    (∀ i, HoldsE (blockR1CS (streamTarget B.length i)) (targetVal R (streamTarget B.length i))
        (liftBlock R (streamTrace B i))) ∧
      (∀ j < 256, streamTrace B 0 (pos j) = wordsBit h0 j) ∧
      (∀ i, ∀ j < 256, streamTrace B (i + 1) (pos j) = streamTrace B i (pos (256 + j))) ∧
      Padded (streamTrace B) B.length ∧ streamBytes (streamTrace B) B.length = B := by
  have hz : ∀ i, circuitR1CS.Holds (liftBlock R (streamTrace B i)) := fun i ↦
    (trace_satisfies (R := R) bounded_blake2s (streamInp B i)).1
  have h1 : ∀ i, streamTrace B i onePos = true := fun i ↦ by
    rw [streamTrace, onePos, ← blake2sCircuit_cpos]; exact traceF_cpos bounded_blake2s _
  have hp : ∀ i, MeetsB (streamTarget B.length i) (streamTrace B i) := fun i k b hk ↦ by
    rcases streamTarget_ok.2 k b hk with rfl | hin
    · exact Option.some.inj (streamTarget_ok.1.symm.trans hk) ▸ h1 i
    · rw [streamTrace_input B i hin, streamInp, hk]
  have hE : ∀ i, HoldsE (blockR1CS (streamTarget B.length i))
      (targetVal R (streamTarget B.length i)) (liftBlock R (streamTrace B i)) := fun i ↦
    holdsE_complete (hz i) (hp i)
  have hout : ∀ i, hOut (streamTrace B i) = chainState B (i + 1) := fun i ↦ by
    rw [block_sound (hE i), hIn_of_bits fun j hj ↦ streamTrace_hIn_bit B i hj]
    have hm : block (msgBytes (streamTrace B i)) = block (B.drop (64 * i)) :=
      block_congr fun p hp64 ↦ by
        rw [msgBytes_getD _ hp64, streamTrace_byte _ _ hp64, List.getD_eq_getElem?_getD,
          List.getD_eq_getElem?_getD, List.getElem?_drop]
    rw [hm]
    rfl
  refine ⟨hE, fun j hj ↦ streamTrace_hIn_bit B 0 hj, fun i j hj ↦ ?_, fun p hp _ ↦ ?_, ?_⟩
  · rw [streamTrace_hIn_bit B (i + 1) hj, ← hout i, hOut_bit _ hj]
  · rw [streamTrace_byte _ _ (Nat.mod_lt _ (by omega)), show 64 * (p / 64) + p % 64 = p by omega,
      List.getD_eq_default _ _ hp]
  · refine List.ext_getElem (streamBytes_length _ _) fun p hp _ ↦ ?_
    rw [streamBytes_length] at hp
    simp only [streamBytes, List.getElem_map, List.getElem_range]
    rw [streamTrace_byte _ _ (Nat.mod_lt _ (by omega)), show 64 * (p / 64) + p % 64 = p by omega,
      List.getD_eq_getElem _ _ hp]

/-- **Negative control (BP-C-M5).** The all-zero block satisfies the circuit's R1CS (with
`one = 0`) but not the block R1CS with a stream target. -/
theorem zero_control {R : Type*} [CommRing R] [CharP R 2] [Nontrivial R] {L i : ℕ} :
    circuitR1CS.Holds (fun _ : Pos ↦ (0 : R)) ∧
      ¬ HoldsE (blockR1CS (streamTarget L i)) (targetVal R (streamTarget L i)) (fun _ ↦ (0 : R)) :=
  ⟨zero_holds, zero_not_holdsE streamTarget_ok⟩

end Stream

end FR

end G6_FRBlockStream

section G6_FRBlockKinds

-- New for `flock-recursive` (BLUEPRINT revision 3.4, Appendix A.6's kind table; S-E1-M1, S-E1-M2).

/-!
# The block kinds of A.6

A **kind** is a public target of the block R1CS (`FRBlockLayout`): which inputs it pins and to
which bits, besides `one = 1` and slot 8. Every kind of A.6 is an instance of one shape
(`Kind`): `h_in` pinned to `h0` or free, some message bytes pinned (`msgPin p = some u`), and slot
8 (`t_lo`, `t_hi` = the counter `t`, `f0 = flagOf fin`, `f1 = 0`) as in `Stream.blockTarget`.

| kind | `h0` | pinned message bytes | `t` | final |
|---|---|---|---|---|
| `streamKind t fin` | no | — | `t` | `fin` |
| `streamStart` | yes | — | 64 | no |
| `streamEnd41` | no | `41…63 = 0` | 4,265 | yes |
| `hashA` | yes | `0 = 0x4C`, `41…63 = 0` | 41 | yes |
| `hashB1 tag` | yes | `0 = tag` (`0x4E`, `0x4B`, `0x4D`) | 64 | no |
| `hashB2` | no | `1…63 = 0` | 65 | yes |
| `w43 i s` | yes | `0 = 0x57`, `9 = i`, `10 = s`, `43…63 = 0` | 43 | yes |

A.6's `chain` kind is `Chain.chainTarget` (`FRBlockChain`, with its own `block_sound` and
`block_complete`, used by `leaf_sound`); `stream` is `Stream.blockTarget t fin`, equal to
`(streamKind t fin).target` (`streamKind_target`), so the digest chain's statements are
instances.

Results (generic, then per kind):
* `Kind.target_ok`: every kind pins `one` and otherwise only inputs;
* `Kind.block_sound` (`h_out` is the compression with the kind's counter and flag),
  `Kind.hIn_eq_h0`, `Kind.msgByte_eq` (the pinned values), `Kind.block_complete` (the honest block
  of any free inputs satisfies the kind);
* `one_block_sound`: a fresh-hash single-block kind (`h0`, `t = L ≤ 64`, final, zero bytes from
  `L`) outputs `blake2sDigest` of its first `L` message bytes; `two_block_sound`: a fresh first
  block (`t = 64`, not final) linked to a final second block (`t = L ∈ [65, 128]`, zero bytes from
  `L − 64`) outputs `blake2sDigest` of the `L` message bytes;
* for `hashStmt` (BLUEPRINT §4.2): `hashA_sound`, `hashA_leafStmt`, `hashB_sound`,
  `hashB_nodeStmt`. **`hashStmt_sound` itself** (the 8 element equalities with `stmt` and its parse
  into `h`, `n`, `c₁`, `c₂`) is S-E2's (`FRWots`), on top of these;
* the dump (A.6's KAT): `kindRows base tgt`, the rows of `A₀^kind`, `B₀^kind` and `E`
  (`kindRows_eq`), `kindLine`, `allKinds`. No evaluation happens in the entry.
-/

namespace FR

open RecursionFast RecursionFast.Blake2s ProductCircuit Blake2sCircuit Block FR.Stream

namespace Kinds

/-! ## The shape of a kind -/

/-- A block kind of A.6. -/
structure Kind where
  /-- `h_in` pinned to `h0` (a fresh hash). -/
  h0Pin : Bool
  /-- The pinned message bytes (`p < 64`). -/
  msgPin : ℕ → Option UInt8
  /-- The counter. -/
  t : ℕ
  /-- The last-block flag. -/
  fin : Bool

/-- The public target of a kind. -/
def Kind.target (κ : Kind) (k : Pos) : Option Bool :=
  if k.val < 256 then (if κ.h0Pin then some (wordsBit h0 k.val) else none)
  else if k.val < 512 then none
  else if k.val < 1024 then
    (κ.msgPin ((k.val - 512) / 8)).map fun u ↦ u.toBitVec.getLsbD ((k.val - 512) % 8)
  else blockTarget κ.t κ.fin k

private theorem pv {v : ℕ} (h : v < 16384) : ((pos v : Pos) : ℕ) = v := pos_val h

section Generic

variable (κ : Kind)

theorem Kind.target_ge {k : Pos} (hk : 1024 ≤ k.val) : κ.target k = blockTarget κ.t κ.fin k := by
  rw [Kind.target, ite_eq_right (by omega), ite_eq_right (by omega), ite_eq_right (by omega)]

theorem Kind.target_h0 (hp : κ.h0Pin = true) : ∀ j < 256, κ.target (pos j) = some (wordsBit h0 j) :=
  fun j hj ↦ by rw [Kind.target, pv (by omega), ite_eq_left hj, hp, ite_eq_left rfl]

theorem Kind.target_hfree (hp : κ.h0Pin = false) {j : ℕ} (hj : j < 256) :
    κ.target (pos j) = none := by
  rw [Kind.target, pv (by omega), ite_eq_left hj, hp]
  rfl

theorem Kind.target_msg {p : ℕ} (hp : p < 64) {i : ℕ} (hi : i < 8) :
    κ.target (pos (msgBase + 8 * p + i)) =
      (κ.msgPin p).map fun u ↦ u.toBitVec.getLsbD i := by
  have hv := pv (show msgBase + 8 * p + i < 16384 by simp only [msgBase]; omega)
  rw [Kind.target, hv, ite_eq_right (by simp only [msgBase]; omega),
    ite_eq_right (by simp only [msgBase]; omega), ite_eq_left (by simp only [msgBase]; omega)]
  simp only [msgBase, show (512 + 8 * p + i - 512) / 8 = p by omega,
    show (512 + 8 * p + i - 512) % 8 = i by omega]

/-- **Every kind is a target of the entry**: it pins `one` to `1` and otherwise only inputs. -/
theorem Kind.target_ok : TargetOk κ.target := by
  refine ⟨by rw [κ.target_ge (by rw [onePos_val]; omega)]; exact blockTarget_ok.1, fun k b h ↦ ?_⟩
  rcases Nat.lt_or_ge k.val 1024 with hk | hk
  · right
    unfold Kind.target at h
    split_ifs at h <;> omega
  · rw [κ.target_ge hk] at h
    exact blockTarget_ok.2 k b h

variable {R : Type*} [CommRing R] [CharP R 2] [Nontrivial R] {w : Pos → Bool}

/-- The kind's slot 8 as a `blockTarget`, met by a block meeting the kind. -/
private theorem meets_block (hm : MeetsB κ.target w) : MeetsB (blockTarget κ.t κ.fin) w :=
  fun k b hk ↦ hm k b (by
    rcases Nat.lt_or_ge k.val 1024 with h | h
    · rw [blockTarget_low h] at hk; cases hk
    · rwa [κ.target_ge h])

/-- **A kind, soundness.** A Boolean block satisfying the block R1CS with a kind's target carries
at `h_out` the compression of its `h_in` and its message with the kind's counter and flag. -/
theorem Kind.block_sound
    (h : HoldsE (blockR1CS κ.target) (targetVal R κ.target) (liftBlock R w)) :
    hOut w = compress (hIn w) (block (msgBytes w)) κ.t.toUInt64 (flagOf κ.fin) 0 :=
  have ⟨hz, h1, hm⟩ := holdsE_sound κ.target_ok h
  have hb := meets_block κ hm
  compress_sound hz h1 rfl rfl (readWord_of_meets hb pat_tlo) (readWord_of_meets hb pat_thi)
    (readWord_of_meets hb pat_f0) (readWord_of_meets hb pat_f1)

/-- A fresh-hash kind's block has `h_in = h0`. -/
theorem Kind.hIn_eq_h0 (hp : κ.h0Pin = true)
    (h : HoldsE (blockR1CS κ.target) (targetVal R κ.target) (liftBlock R w)) : hIn w = h0 :=
  hIn_of_meets (holdsE_sound κ.target_ok h).2.2 (κ.target_h0 hp)

/-- A pinned message byte holds its value. -/
theorem Kind.msgByte_eq {p : ℕ} (hp : p < 64) {u : UInt8} (hu : κ.msgPin p = some u)
    (h : HoldsE (blockR1CS κ.target) (targetVal R κ.target) (liftBlock R w)) :
    readByte w (msgBase + 8 * p) = u :=
  readByte_of_meets (holdsE_sound κ.target_ok h).2.2 fun i hi ↦ by
    rw [κ.target_msg hp hi, hu]
    rfl

end Generic

/-! ## Completeness -/

/-- The input block of a kind with free chaining value `h` and free message bytes `m`. -/
def Kind.inp (κ : Kind) (h : Vector UInt32 8) (m : List UInt8) (k : Pos) : Bool :=
  match κ.target k with
  | some b => b
  | none =>
    if k.val < 256 then wordsBit h k.val
    else if msgBase ≤ k.val ∧ k.val < msgBase + 512 then
      (m.getD ((k.val - msgBase) / 8) 0).toBitVec.getLsbD ((k.val - msgBase) % 8)
    else false

/-- The honest block of a kind. -/
noncomputable def Kind.trace (κ : Kind) (h : Vector UInt32 8) (m : List UInt8) : Pos → Bool :=
  blake2sCircuit.traceF (κ.inp h m)

private theorem trace_input (κ : Kind) (h : Vector UInt32 8) (m : List UInt8) {k : Pos}
    (hk : k.val < 256 ∨ (512 ≤ k.val ∧ k.val < 1152)) : κ.trace h m k = κ.inp h m k :=
  traceF_input bounded_blake2s _
    (by rw [blake2sCircuit_inputs, getLsbD_inputs]; exact decide_eq_true hk)
    (by rw [blake2sCircuit_cpos]; exact Fin.ne_of_val_ne (by rw [constPos_val]; omega))

/-- **A kind, completeness.** The honest block of any free inputs satisfies the kind's block R1CS
with its target, holds `h` as `h_in` if `h_in` is free, and the free message bytes of `m`. -/
theorem Kind.block_complete {R : Type*} [CommRing R] [CharP R 2] (κ : Kind) (h : Vector UInt32 8)
    (m : List UInt8) :
    HoldsE (blockR1CS κ.target) (targetVal R κ.target) (liftBlock R (κ.trace h m)) ∧
      (κ.h0Pin = false → hIn (κ.trace h m) = h) ∧
      ∀ p < 64, κ.msgPin p = none → readByte (κ.trace h m) (msgBase + 8 * p) = m.getD p 0 := by
  have h1 : κ.trace h m onePos = true := by
    rw [Kind.trace, onePos, ← blake2sCircuit_cpos]; exact traceF_cpos bounded_blake2s _
  refine ⟨holdsE_complete (trace_satisfies (R := R) bounded_blake2s (κ.inp h m)).1
    fun k b hk ↦ ?_, fun hp ↦ hIn_of_bits fun j hj ↦ ?_, fun p hp hu ↦ ?_⟩
  · rcases κ.target_ok.2 k b hk with rfl | hin
    · rw [κ.target_ok.1] at hk; cases hk; exact h1
    · rw [trace_input κ h m hin, Kind.inp, hk]
  · have hv : ((pos j : Pos) : ℕ) = j := pv (by omega)
    rw [trace_input _ _ _ (by rw [hv]; omega), Kind.inp, κ.target_hfree hp hj, hv, ite_eq_left hj]
  · refine UInt8.toBitVec_inj.mp (BitVec.eq_of_getLsbD_eq fun b hb ↦ ?_)
    have hv := pv (show msgBase + 8 * p + b < 16384 by simp only [msgBase]; omega)
    rw [readByte_getLsbD _ _ hb, trace_input _ _ _ (by rw [hv]; simp only [msgBase]; omega),
      Kind.inp, κ.target_msg hp hb, hu, Option.map_none, hv,
      ite_eq_right (by simp only [msgBase]; omega), ite_eq_left (by simp only [msgBase]; omega)]
    simp only [msgBase, show (512 + 8 * p + b - 512) / 8 = p by omega,
      show (512 + 8 * p + b - 512) % 8 = b by omega]

/-! ## The kinds of A.6 -/

/-- `stream`: digest-chain and key-leaf blocks after the first. -/
def streamKind (t : ℕ) (fin : Bool) : Kind := ⟨false, fun _ ↦ none, t, fin⟩

/-- `streamStart`: block 0 of a digest chain. -/
def streamStart : Kind := ⟨true, fun _ ↦ none, 64, false⟩

/-- `streamEnd41`: the key leaf's last block (a 41-byte tail). -/
def streamEnd41 : Kind := ⟨false, fun p ↦ if 41 ≤ p then some 0 else none, 4265, true⟩

/-- `hashA`: the leaf statement `tagLeaf ‖ h ‖ enc64 n` (41 bytes) in one block. -/
def hashA : Kind := ⟨true, fun p ↦ if p = 0 then some tagLeaf else if 41 ≤ p then some 0 else none,
  41, true⟩

/-- `hashB1`: the first block of a 65-byte hash with tag `tag` (`tagNode`, `tagWotsLeaf`,
`tagSigNode`). -/
def hashB1 (tag : UInt8) : Kind := ⟨true, fun p ↦ if p = 0 then some tag else none, 64, false⟩

/-- `hashB2`: the second block of a 65-byte hash (one byte, then zeros). -/
def hashB2 : Kind := ⟨false, fun p ↦ if 1 ≤ p then some 0 else none, 65, true⟩

/-- `w43`: a WOTS chain step `tagWots ‖ enc64 j ‖ i ‖ s ‖ x` (43 bytes), `i`, `s` per block. -/
def w43 (i s : UInt8) : Kind :=
  ⟨true, fun p ↦ if p = 0 then some tagWots else if p = 9 then some i else if p = 10 then some s
    else if 43 ≤ p then some 0 else none, 43, true⟩

theorem streamKind_target (t : ℕ) (fin : Bool) : (streamKind t fin).target = blockTarget t fin := by
  funext k
  rcases Nat.lt_or_ge k.val 1024 with h | h
  · rw [blockTarget_low h]
    simp only [Kind.target, streamKind, Bool.false_eq_true, ↓reduceIte, Option.map_none]
    split_ifs <;> rfl
  · exact (streamKind t fin).target_ge h

/-! ## Hashes of one and two blocks -/

private theorem msgBytes_length (w : Pos → Bool) : (msgBytes w).length = 64 := by
  simp [msgBytes]

/-- **One fresh block.** A block of a kind with `h_in = h0`, counter `L ∈ [1, 64]`, final, and the
message bytes from `L` pinned to `0` outputs the contract's BLAKE2s-256 of its first `L` message
bytes. -/
theorem one_block_sound {R : Type*} [CommRing R] [CharP R 2] [Nontrivial R] (κ : Kind)
    {L : ℕ} (hL : 1 ≤ L ∧ L ≤ 64) (hp : κ.h0Pin = true) (ht : κ.t = L) (hf : κ.fin = true)
    (hz : ∀ p, L ≤ p → p < 64 → κ.msgPin p = some 0) {w : Pos → Bool}
    (h : HoldsE (blockR1CS κ.target) (targetVal R κ.target) (liftBlock R w)) :
    readDigest w 256 = blake2sDigest ((msgBytes w).take L) := by
  have hl : ((msgBytes w).take L).length = L := by simp [msgBytes_length]; omega
  have hN : nBlocks L = 1 := by simp only [nBlocks]; omega
  rw [readDigest_hOut, κ.block_sound h, κ.hIn_eq_h0 hp h, blake2s_chain, hl, hN, chainState,
    chainState, hl, ctrAt, flagAt, hN, ite_eq_left rfl, ite_eq_left rfl, ht, hf, flagOf,
    ite_eq_left rfl,
    Nat.mul_zero, List.drop_zero]
  rw [block_congr (l := msgBytes w) (l' := (msgBytes w).take L) fun p hp64 ↦ ?_]
  rw [msgBytes_getD _ hp64, List.getD_eq_getElem?_getD, List.getElem?_take]
  rcases Nat.lt_or_ge p L with hpL | hpL
  · rw [ite_eq_left hpL, ← List.getD_eq_getElem?_getD, msgBytes_getD _ hp64]
  · rw [ite_eq_right (by omega)]
    exact κ.msgByte_eq hp64 (hz p hpL hp64) h

/-- **Two linked blocks.** A fresh first block (`h0`, counter `64`, not final) whose output is the
second block's `h_in`, the second block final with counter `L ∈ [65, 128]` and message bytes from
`L − 64` pinned to `0`: the second block outputs the contract's BLAKE2s-256 of the first block's
64 message bytes followed by the second's first `L − 64`. -/
theorem two_block_sound {R : Type*} [CommRing R] [CharP R 2] [Nontrivial R] (κ₁ κ₂ : Kind)
    {L : ℕ} (hL : 65 ≤ L ∧ L ≤ 128) (hp : κ₁.h0Pin = true) (ht₁ : κ₁.t = 64)
    (hf₁ : κ₁.fin = false) (ht₂ : κ₂.t = L) (hf₂ : κ₂.fin = true)
    (hz : ∀ p, L - 64 ≤ p → p < 64 → κ₂.msgPin p = some 0) {w₁ w₂ : Pos → Bool}
    (h₁ : HoldsE (blockR1CS κ₁.target) (targetVal R κ₁.target) (liftBlock R w₁))
    (h₂ : HoldsE (blockR1CS κ₂.target) (targetVal R κ₂.target) (liftBlock R w₂))
    (hl : ∀ j < 256, w₂ (pos j) = w₁ (pos (256 + j))) :
    readDigest w₂ 256 = blake2sDigest (msgBytes w₁ ++ (msgBytes w₂).take (L - 64)) := by
  set B := msgBytes w₁ ++ (msgBytes w₂).take (L - 64) with hB
  have hBl : B.length = L := by simp [hB, msgBytes_length]; omega
  have hN : nBlocks L = 2 := by simp only [nBlocks]; omega
  have hin : hIn w₂ = hOut w₁ :=
    hIn_of_bits fun j hj ↦ by rw [hl j hj, hOut_bit _ hj]
  have h1 : hOut w₁ = chainState B 1 := by
    rw [κ₁.block_sound h₁, κ₁.hIn_eq_h0 hp h₁]
    rw [chainState]
    rw [chainState]
    rw [ctrAt, flagAt]
    rw [hBl, hN]
    rw [ite_eq_right (by omega), ite_eq_right (by omega)]
    rw [ht₁, hf₁, flagOf, ite_eq_right Bool.false_ne_true, Nat.mul_zero, List.drop_zero,
      show 64 * (0 + 1) = 64 from rfl, block_congr (l := msgBytes w₁) (l' := B) fun p hp64 ↦ ?_]
    rw [hB, List.getD_append _ _ _ _ (by rw [msgBytes_length]; omega)]
  rw [readDigest_hOut, κ₂.block_sound h₂, hin, blake2s_chain, hBl, hN, chainState, h1, hBl,
    ctrAt, flagAt, hN, ite_eq_left rfl, ite_eq_left rfl, ht₂, hf₂, flagOf, ite_eq_left rfl,
    block_congr (l := msgBytes w₂) (l' := B.drop (64 * 1)) fun p hp64 ↦ ?_]
  rw [hB, Nat.mul_one, List.drop_left' (msgBytes_length w₁), msgBytes_getD _ hp64,
    List.getD_eq_getElem?_getD, List.getElem?_take]
  rcases Nat.lt_or_ge p (L - 64) with hpL | hpL
  · rw [ite_eq_left hpL, ← List.getD_eq_getElem?_getD, msgBytes_getD _ hp64]
  · rw [ite_eq_right (by omega)]
    exact κ₂.msgByte_eq hp64 (hz p hpL hp64) h₂

/-! ## The statement hash (`hashStmt`'s blocks) -/

section HashStmt

variable {R : Type*} [CommRing R] [CharP R 2] [Nontrivial R]

/-- **Block A.** A `hashA` block outputs the BLAKE2s-256 of its first 41 message bytes, whose
first is `tagLeaf`. -/
theorem hashA_sound {w : Pos → Bool}
    (h : HoldsE (blockR1CS hashA.target) (targetVal R hashA.target) (liftBlock R w)) :
    readDigest w 256 = blake2sDigest ((msgBytes w).take 41) ∧ readByte w msgBase = tagLeaf :=
  ⟨one_block_sound hashA (L := 41) (by omega) rfl rfl rfl
      (fun p hp _ ↦ by simp [hashA, show p ≠ 0 by omega, hp]) h,
    by simpa using hashA.msgByte_eq (p := 0) (by omega) rfl h⟩

/-- Block A with its message bytes `tagLeaf ‖ h ‖ enc64 n` outputs `leafStmt h n`. -/
theorem hashA_leafStmt {w : Pos → Bool}
    (h : HoldsE (blockR1CS hashA.target) (targetVal R hashA.target) (liftBlock R w))
    {d : Digest} {n : ℕ} (hm : (msgBytes w).take 41 = tagLeaf :: d.toList ++ enc64 n) :
    readDigest w 256 = leafStmt d n := by
  rw [(hashA_sound h).1, hm]
  rfl

/-- **Blocks B1, B2.** A `hashB1 tag` block linked to a `hashB2` block: the second outputs the
BLAKE2s-256 of the 64 message bytes of the first and the first message byte of the second; the
first message byte of B1 is `tag`. -/
theorem hashB_sound {tag : UInt8} {w₁ w₂ : Pos → Bool}
    (h₁ : HoldsE (blockR1CS (hashB1 tag).target) (targetVal R (hashB1 tag).target)
      (liftBlock R w₁))
    (h₂ : HoldsE (blockR1CS hashB2.target) (targetVal R hashB2.target) (liftBlock R w₂))
    (hl : ∀ j < 256, w₂ (pos j) = w₁ (pos (256 + j))) :
    readDigest w₂ 256 = blake2sDigest (msgBytes w₁ ++ (msgBytes w₂).take 1) ∧
      readByte w₁ msgBase = tag :=
  ⟨two_block_sound (hashB1 tag) hashB2 (L := 65) (by omega) rfl rfl rfl rfl rfl
      (fun p hp _ ↦ by simp [hashB2, show 1 ≤ p by omega]) h₁ h₂ hl,
    by simpa using (hashB1 tag).msgByte_eq (p := 0) (by omega) rfl h₁⟩

/-- Blocks B1, B2 with message bytes `tagNode ‖ c₁ ‖ c₂` output `nodeStmt c₁ c₂`. -/
theorem hashB_nodeStmt {w₁ w₂ : Pos → Bool}
    (h₁ : HoldsE (blockR1CS (hashB1 tagNode).target) (targetVal R (hashB1 tagNode).target)
      (liftBlock R w₁))
    (h₂ : HoldsE (blockR1CS hashB2.target) (targetVal R hashB2.target) (liftBlock R w₂))
    (hl : ∀ j < 256, w₂ (pos j) = w₁ (pos (256 + j))) {c₁ c₂ : Digest}
    (hm : msgBytes w₁ ++ (msgBytes w₂).take 1 = tagNode :: c₁.toList ++ c₂.toList) :
    readDigest w₂ 256 = nodeStmt c₁ c₂ := by
  rw [(hashB_sound h₁ h₂ hl).1, hm]
  rfl

end HashStmt

/-! ## The dump (A.6's KAT) -/

/-- The rows of `A₀^kind`, `B₀^kind` and the target bit `E`, position by position, with the
circuit's gates recorded from `base` (`gateBase` for the entry; the argument keeps the circuit out
of closed-term extraction). -/
def kindRows (base : ℕ) (tgt : Target) : List (Gate Blake2sCircuit.m × Bool) :=
  let c := blockAt base
  let l := c.gates.toList
  (List.finRange (2 ^ Blake2sCircuit.m)).map fun k ↦
    (if (tgt k).isSome then ⟨0, 0⟩ else c.rowOfList l k, (tgt k).getD false)

/-- The dumped rows are the kind's block matrices and target. -/
theorem kindRows_eq (tgt : Target) :
    kindRows gateBase tgt = (List.finRange (2 ^ Blake2sCircuit.m)).map fun k ↦
      (if (tgt k).isSome then ⟨0, 0⟩ else blake2sCircuit.rowOf k, (tgt k).getD false) := by
  unfold kindRows
  rw [blockAt_eq]
  rfl

/-- The matrices of `blockR1CS tgt` are the dumped rows' forms. -/
theorem blockR1CS_rows (tgt : Target) (k j : Pos) :
    (blockR1CS tgt).A k j =
        (if (tgt k).isSome then (⟨0, 0⟩ : Gate _) else blake2sCircuit.rowOf k).a.getLsbD j ∧
      (blockR1CS tgt).B k j =
        (if (tgt k).isSome then (⟨0, 0⟩ : Gate _) else blake2sCircuit.rowOf k).b.getLsbD j := by
  rcases h : tgt k with _ | b <;> simp [blockR1CS, circuitR1CS, toBlockR1CS, h]

/-- A dump line: `k <a-form> <b-form> <E bit>`. -/
def kindLine (k : ℕ) (r : Gate Blake2sCircuit.m × Bool) : String :=
  rowLine k r.1 ++ " " ++ (if r.2 then "1" else "0")

/-- Every kind of A.6 with one sample block (per-block values: the stream's `t = 64`, not final;
`w43`'s `i = s = 0`). -/
def allKinds : List (String × Target) :=
  [("chain", Chain.chainTarget), ("stream", blockTarget 64 false),
    ("streamStart", streamStart.target), ("streamEnd41", streamEnd41.target),
    ("hashA", hashA.target), ("hashB1", (hashB1 tagNode).target), ("hashB2", hashB2.target),
    ("w43", (w43 0 0).target)]

end Kinds

end FR

end G6_FRBlockKinds
