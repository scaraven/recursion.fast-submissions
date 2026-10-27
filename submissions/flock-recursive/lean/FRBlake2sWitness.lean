-- Copied from `submissions/spartan-srom/lean/SpartanSromBlake2sWitness.lean` (this repository,
-- branch `v4/flock-recursive` at `783328c`), renamed to the namespace `FR`, and **retargeted** from
-- spartan-srom's chain block to the block circuit of BLUEPRINT Appendix A.6 (`blake2sCircuit`,
-- re-based): `fastTrace` takes any input block, not a digest; the dump is of `blake2sCircuit`'s
-- rows. That file was ported from v3 `spartan-chain` (submissions repo, local `main` at `1f59b38`)
-- to the v4 contract.
import FRBlake2sWalk

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
