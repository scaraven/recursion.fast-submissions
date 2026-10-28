-- New for `flock-recursive` (BLUEPRINT §7, stage S-0; §3, B-7).
import FRVIR

/-!
# The verifier IR's semantics

BLUEPRINT §3, B-7.

* **Generic** (any program): `runSeq_runIR : (runIR impl P inp).runSeq tr = semIR impl P inp tr`
  (the oracle program on a trace is the trace semantics); `exec_append` (sequencing);
  `queries_runIR` (a run asks exactly the program's ask ops).
* **The item sequence**: `items_gen : (genWith fin m).ops.filterMap Op.item? = items` for every phase-final
  fragment that asks nothing, hence **`queries_gen : ((runIR impl (genWith fin m) inp).queries H).length =
  8874 ≤ qV`**, proved from the phase table's structure (never by evaluating `gen`).
* `semIR_mux`: the mux program is the fixed program of the proof's kind byte.
* **Per shape** (the phase table's shapes, `FRTranscriptDefs.Shape`): the exact registers and flag a
  shape's ops produce on a trace. **Phase Z** (Z1, Z2, Z3, Zend) is proved end to end
  (`exec_phaseZ`), with its final check `finZ` (`exec_finZ`); every shape is proved
  (`exec_genPhase`), and so is the whole skeleton (`exec_skeleton`).
-/

namespace FR
open RecursionFast

variable (impl : OpImpl) (κ : Kind) (inp : Input)

/-! ## Registers -/

theorem rd_append_left {a b : Array Val} {i : ℕ} (h : i < a.size) : rd (a ++ b) i = rd a i := by
  simp [rd, Array.getElem?_append_left h]

theorem rd_append_right (a b : Array Val) (j : ℕ) : rd (a ++ b) (a.size + j) = rd b j := by
  simp [rd, Array.getElem?_append_right]

theorem rd_push_size (a : Array Val) (v : Val) : rd (a.push v) a.size = v := by simp [rd]

theorem rd_push_left {a : Array Val} {i : ℕ} (v : Val) (h : i < a.size) :
    rd (a.push v) i = rd a i := by
  simp [rd, Array.getElem?_push, Nat.ne_of_lt h]

/-! ## Sequencing and the oracle program -/

theorem exec_nil (s : St) (tr : Trace) : exec impl κ inp [] s tr = some (s, tr) := rfl

theorem exec_append (o₁ o₂ : List Op) (s : St) (tr : Trace) :
    exec impl κ inp (o₁ ++ o₂) s tr = (exec impl κ inp o₁ s tr).bind fun p => exec impl κ inp o₂ p.1 p.2 := by
  induction o₁ generalizing s tr with
  | nil => rfl
  | cons op ops ih =>
    simp only [List.cons_append, exec]
    split
    · exact ih _ _
    · split
      · rfl
      · split
        · exact ih _ _
        · rfl

theorem runSeq_runOps (ops : List Op) (s : St) (tr : Trace) :
    (runOps impl κ inp ops s).runSeq tr =
      match exec impl κ inp ops s tr with
      | some (s', []) => some s'.ok
      | _ => none := by
  induction ops generalizing s tr with
  | nil => cases tr <;> rfl
  | cons op ops ih =>
    simp only [runOps, exec]
    split
    · exact ih _ _
    · rcases tr with _ | ⟨⟨q', a⟩, tr⟩
      · rfl
      · simp only [OProg.runSeq]
        split
        · exact ih _ _
        · rfl

/-- **`runSeq_runIR`**: the verifier's program on a trace is the trace semantics. -/
theorem runSeq_runIR (P : VProg) (tr : Trace) : (runIR impl P inp).runSeq tr = semIR impl P inp tr :=
  runSeq_runOps impl _ inp P.ops St.init tr

theorem item?_of_vals {regs : Array Val} {op : Op} {vs : List Val} {ok : Bool}
    (h : evalOp impl κ inp regs op = .vals vs ok) : op.item? = none := by
  cases op <;> simp_all [evalOp, Op.item?]

theorem item?_of_ask {regs : Array Val} {op : Op} {q : ByteArray}
    (h : evalOp impl κ inp regs op = .ask q) : op.item?.isSome := by
  cases op <;> simp_all [evalOp, Op.item?]

/-- A run asks exactly the program's ask ops, whatever the oracle answers. -/
theorem queries_runOps (H : ByteArray → Digest) (ops : List Op) (s : St) :
    ((runOps impl κ inp ops s).queries H).length = (ops.filterMap Op.item?).length := by
  induction ops generalizing s with
  | nil => rfl
  | cons op ops ih =>
    simp only [runOps]
    split
    · next h => rw [ih, List.filterMap_cons, item?_of_vals impl κ inp h]
    · next h =>
      obtain ⟨it, hit⟩ := Option.isSome_iff_exists.1 (item?_of_ask impl κ inp h)
      simp [OProg.queries, ih, List.filterMap_cons, hit]

theorem queries_runIR (H : ByteArray → Digest) (P : VProg) :
    ((runIR impl P inp).queries H).length = (P.ops.filterMap Op.item?).length :=
  queries_runOps impl _ inp H P.ops St.init

/-- **The mux is the fixed program of the proof's kind byte** (IR level; the circuit's
`compile_mux_sound` is L-circ's). -/
theorem semIR_mux (fin : FinOps) (k : Kind) (h : inp.π.data[0]? = some k.byte) (tr : Trace) :
    semIR impl (genWith fin .mux) inp tr = semIR impl (genWith fin (.fixed k)) inp tr := by
  simp [semIR, VProg.kindOn, genWith, byteAt?_eq, h, Kind.ofByte?_byte]

/-! ## The item sequence of `gen` -/

theorem flatMap_range_const {β : Type} (t : ℕ) (f : ℕ → List β) (l : List β) (hf : ∀ p, f p = l) :
    (List.range t).flatMap f = (List.replicate t l).flatten := by
  induction t with
  | zero => rfl
  | succ t ih => simp [List.range_succ, List.replicate_succ', ih, hf]

theorem items_sqzCoordOps (n st b : ℕ) :
    (sqzCoordOps n st b).filterMap Op.item? = List.replicate n .squeeze := by
  induction n generalizing st b with
  | zero => rfl
  | succ n ih => simp [sqzCoordOps, List.filterMap_cons, Op.item?, ih, List.replicate_succ]

theorem items_sqzOps (n st b : ℕ) : (sqzOps n st b).filterMap Op.item? = List.replicate n .squeeze := by
  induction n generalizing st b with
  | zero => rfl
  | succ n ih => simp [sqzOps, List.filterMap_cons, Op.item?, ih, List.replicate_succ]

theorem items_roundsOps (f o deg : ℕ) (inK : Bool) (real : KC ℕ) (n j st cl b : ℕ) :
    (roundsOps f o deg inK real n j st cl b).filterMap Op.item? =
      (List.replicate n [Item.absorb (roundBytes inK), .squeeze]).flatten := by
  induction n generalizing j st cl b with
  | zero => rfl
  | succ n ih =>
    rw [roundsOps, List.filterMap_append, ih, List.replicate_succ, List.flatten_cons]
    congr 1
    cases inK
    · by_cases h3 : deg = 3 <;> simp [roundOpsF, h3, List.filterMap_cons, Op.item?, roundBytes]
    · simp [roundOpsK, List.filterMap_cons, Op.item?, roundBytes]

theorem items_merkleOps (i j n h cur so b : ℕ) :
    (merkleOps i j n h cur so b).filterMap Op.item? = (List.range n).map fun k => .node i (h + k) := by
  induction n generalizing h cur so b with
  | zero => rfl
  | succ n ih =>
    simp only [merkleOps, List.filterMap_append, ih, List.range_succ_eq_map, List.map_cons,
      List.map_map]
    simp [List.filterMap_cons, Op.item?, Function.comp_def, Nat.add_assoc, Nat.add_comm 1]

theorem items_posOps (i co so : ℕ) (ans : List Reg) (w p b : ℕ) :
    (posOps i co so ans w p b).filterMap Op.item? = posItems i := by
  simp [posOps, posItems, List.filterMap_cons, Op.item?, items_merkleOps]

theorem items_genPhase (n : ℕ) (p : Phase) (c : GCtx) :
    (genPhase n p c).1.filterMap Op.item? = p.shape.items := by
  obtain ⟨name, sh⟩ := p
  cases sh with
  | seed => simp [genPhase, seedOps, List.filterMap_cons, Op.item?, Shape.items]
  | absorb f len =>
    simp only [genPhase, Shape.items]
    split_ifs <;> simp [absorbOps, stmtOps, finalOps, List.filterMap_cons, Op.item?]
  | squeezes k ch =>
    cases ch <;> simp [genPhase, Shape.items, items_sqzCoordOps, items_sqzOps, List.filterMap_cons, Op.item?]
  | uni f => simp [genPhase, uniOps, uniHead, uniElems, uniTail, Shape.items, List.filterMap_cons,
      Op.item?, Function.comp_def]
  | rounds f k deg inK real =>
    simp only [genPhase, Shape.items]
    rw [List.filterMap_append, items_roundsOps]
    rcases initClaim name with _ | _ | _ <;> cases inK <;>
      simp [initOps, List.filterMap_cons, Op.item?]
  | queries i =>
    simp only [genPhase, Shape.items]
    rw [List.filterMap_append, List.filterMap_flatMap]
    simp only [items_posOps]
    rw [flatMap_range_const _ _ _ fun _ => rfl]; rfl

theorem items_genPhases (ps : List Phase) (n : ℕ) (c : GCtx) :
    (genPhases ps n c).1.filterMap Op.item? = ps.flatMap fun p => p.shape.items := by
  induction ps generalizing n c with
  | nil => rfl
  | cons p ps ih => simp [genPhases, ih, items_genPhase]

/-- **`gen` asks the item sequence**, for every phase-final fragment that asks nothing. -/
theorem items_gen (fin : FinOps) (hfin : ∀ outs b, (fin outs b).filterMap Op.item? = [])
    (m : Mode) : (genWith fin m).ops.filterMap Op.item? = items := by
  simp [genWith, skeleton, items_genPhases, hfin, List.filterMap_cons, Op.item?, items]

/-- **`queries_gen`**: the verifier asks `8,891 ≤ qV` queries under every oracle (revision 3.13). -/
theorem queries_gen (fin : FinOps) (hfin : ∀ outs b, (fin outs b).filterMap Op.item? = [])
    (m : Mode) (H : ByteArray → Digest) :
    ((runIR impl (genWith fin m) inp).queries H).length = 8891 := by
  rw [queries_runIR, items_gen fin hfin, items_length]

/-! ## The interpreter step by step; the shapes of phase Z -/

/-- One query answered by the trace. -/
def ans1 (q : ByteArray) : Trace → Option (Digest × Trace)
  | (q', a) :: tr => if q' = q then some (a, tr) else none
  | [] => none

/-- `n` squeezes from `d` on the trace: the answers. -/
def sqzT : ℕ → Digest → Trace → Option (List Digest × Trace)
  | 0, _, tr => some ([], tr)
  | n + 1, d, tr => (ans1 (squeezeQ d) tr).bind fun p =>
    (sqzT n p.1 p.2).map fun r => (p.1 :: r.1, r.2)

theorem exec_vals {op : Op} {ops : List Op} {s : St} {tr : Trace} {vs : List Val} {ok : Bool}
    (h : evalOp impl κ inp s.regs op = .vals vs ok) :
    exec impl κ inp (op :: ops) s tr = exec impl κ inp ops ⟨s.regs ++ vs.toArray, s.ok && ok⟩ tr := by
  simp [exec, h]

theorem exec_ask {op : Op} {ops : List Op} {s : St} {tr : Trace} {q : ByteArray}
    (h : evalOp impl κ inp s.regs op = .ask q) :
    exec impl κ inp (op :: ops) s tr =
      (ans1 q tr).bind fun p => exec impl κ inp ops ⟨s.regs.push (.d p.1), s.ok⟩ p.2 := by
  rcases tr with _ | ⟨⟨q', a⟩, tr⟩
  · simp [exec, h, ans1]
  · simp only [exec, h, ans1]; split <;> rfl

/-- The registers of a squeeze with its two coordinates. -/
def coordVals (a : Digest) : List Val := [.d a, .f (chF a 0), .f (chF a 1)]

theorem exec_sqzCoordOps (n st b : ℕ) (s : St) (tr : Trace) (hb : s.regs.size = b) (hst : st < b) :
    exec impl κ inp (sqzCoordOps n st b) s tr =
      (sqzT n (rd s.regs st).toD tr).map fun p =>
        (⟨s.regs ++ (p.1.flatMap coordVals).toArray, s.ok⟩, p.2) := by
  induction n generalizing st b s tr with
  | zero => simp [sqzCoordOps, exec, sqzT]
  | succ n ih =>
    simp only [sqzCoordOps, List.cons_append]
    rw [exec_ask impl κ inp rfl]
    simp only [sqzT, Option.bind]
    rcases ans1 (squeezeQ (rd s.regs st).toD) tr with _ | ⟨a, tr'⟩
    · rfl
    · dsimp only
      have h1 : rd (s.regs.push (.d a)) b = .d a := hb ▸ rd_push_size _ _
      rw [exec_vals impl κ inp (vs := [.f (chF a 0)]) (ok := true) (by simp [evalOp, h1, Val.toD])]
      have h2 : rd ((s.regs.push (.d a)).push (.f (chF a 0))) b = .d a := by
        rw [rd_push_left _ (by simp [hb]), h1]
      rw [exec_vals impl κ inp (vs := [.f (chF a 1)]) (ok := true) (by simp [evalOp, h2, Val.toD])]
      simp only [List.nil_append, Bool.and_true]
      have e : ∀ (r : Array Val) (x : Val), r ++ [x].toArray = r.push x := fun r x => by simp
      simp only [e]
      rw [ih b (b + 3) _ _ (by simp [hb]) (by omega)]
      have h3 : rd (((s.regs.push (.d a)).push (.f (chF a 0))).push (.f (chF a 1))) b = .d a := by
        rw [rd_push_left _ (by simp [hb]), h2]
      simp only [h3, Val.toD, Option.map_map, Function.comp_def]
      congr 1; funext p; congr 2
      apply Array.ext'; simp [coordVals]

theorem rd_app (r : Array Val) (L : List Val) (k : ℕ) : rd (r ++ L.toArray) (r.size + k) = L.getD k default := by
  simp [rd, Array.getElem?_append_right, List.getD_eq_getElem?_getD]

theorem rd_app0 (r : Array Val) (L : List Val) : rd (r ++ L.toArray) r.size = L.getD 0 default := by
  simpa using rd_app r L 0

theorem toD_d (x : Digest) : (Val.d x).toD = x := rfl
theorem toF_f (x : F) : (Val.f x).toF = x := rfl
theorem toK_k (x : K) : (Val.k x).toK = x := rfl

theorem rd_app2 (r : Array Val) (L : List Val) (a b : ℕ) :
    rd (r ++ L.toArray) (r.size + a + b) = L.getD (a + b) default := by
  rw [Nat.add_assoc, rd_app]

theorem rd_app_left (r : Array Val) (L : List Val) {k : ℕ} (h : k < r.size) : rd (r ++ L.toArray) k = rd r k :=
  rd_append_left h

theorem push_app (r : Array Val) (L : List Val) (x : Val) : (r ++ L.toArray).push x = r ++ (L ++ [x]).toArray := by
  simp

theorem app_app (r : Array Val) (L M : List Val) : r ++ L.toArray ++ M.toArray = r ++ (L ++ M).toArray := by
  simp [Array.append_assoc]

/-- One op from registers `r ++ L` (the normal form the shape lemmas keep). -/
theorem exec_app (op : Op) (ops : List Op) (r : Array Val) (L : List Val) (ok : Bool) (tr : Trace) :
    exec impl κ inp (op :: ops) ⟨r ++ L.toArray, ok⟩ tr =
      match evalOp impl κ inp (r ++ L.toArray) op with
      | .vals vs ok' => exec impl κ inp ops ⟨r ++ (L ++ vs).toArray, ok && ok'⟩ tr
      | .ask q => match tr with
        | [] => none
        | (q', a) :: tr' => if q' = q then exec impl κ inp ops ⟨r ++ (L ++ [Val.d a]).toArray, ok⟩ tr'
          else none := by
  rw [exec]
  rcases evalOp impl κ inp (r ++ L.toArray) op with ⟨vs, ok'⟩ | q
  · simp only; congr 2; simp [Array.append_assoc]
  · rcases tr with _ | ⟨⟨q', a⟩, tr⟩
    · rfl
    · simp only; split <;> simp

theorem exec_app_vals {op : Op} {ops : List Op} {r : Array Val} {L : List Val} {ok : Bool} {tr : Trace}
    {vs : List Val} {ok' : Bool} (h : evalOp impl κ inp (r ++ L.toArray) op = .vals vs ok') :
    exec impl κ inp (op :: ops) ⟨r ++ L.toArray, ok⟩ tr = exec impl κ inp ops ⟨r ++ (L ++ vs).toArray, ok && ok'⟩ tr := by
  simp [exec, h, Array.append_assoc]

theorem exec_app_ask {op : Op} {ops : List Op} {r : Array Val} {L : List Val} {ok : Bool}
    {q q' : ByteArray} {a : Digest} {tr : Trace} (h : evalOp impl κ inp (r ++ L.toArray) op = .ask q) :
    exec impl κ inp (op :: ops) ⟨r ++ L.toArray, ok⟩ ((q', a) :: tr) =
      if q' = q then exec impl κ inp ops ⟨r ++ (L ++ [Val.d a]).toArray, ok⟩ tr else none := by
  simp only [exec, h]; split <;> simp [Array.append_assoc]

/-- The message of a round at `o` of field `f`, and its coefficient `i`. -/
def msgAt (f o len : ℕ) : ByteArray := inp.π.extract (absOff f o) (absOff f o + len)
def elemAt (f o : ℕ) : F := F.ofBytes (bytesAt inp.π (absOff f o) 16)

/-- The registers of one degree-3 F round (`roundOpsF … 3`). -/
def round3Vals (f o : ℕ) (real : Bool) (a₁ a₂ : Digest) (claim : F) : List Val :=
  let r := chF a₂ 0
  let c₀ := elemAt inp f o; let c₁ := elemAt inp f (o + 16); let c₂ := elemAt inp f (o + 32)
  let s := c₁ + c₂; let c₃ := claim + s
  let t₁ := r * c₃; let t₂ := c₂ + t₁; let t₃ := r * t₂; let t₄ := c₁ + t₃; let t₅ := r * t₄
  let g := c₀ + t₅
  [.b (msgAt inp f o 48), .d a₁, .d a₂, .f r, .f c₀, .f c₁, .f c₂, .f s, .f c₃, .f t₁, .f t₂, .f t₃,
   .f t₄, .f t₅, .f g, if real then .f g else .f claim]

theorem exec_round3 (f o : ℕ) (real : KC Bool) (st cl : ℕ) (r : Array Val) (ok : Bool) (ops : List Op)
    (d : Digest) (c : F) (hst : st < r.size) (hcl : cl < r.size) (hd : rd r st = .d d)
    (hc : rd r cl = .f c) (q₁ q₂ : ByteArray) (a₁ a₂ : Digest) (tr : Trace) :
    exec impl κ inp (roundOpsF f o 3 real st cl r.size ++ ops) ⟨r, ok⟩ ((q₁, a₁) :: (q₂, a₂) :: tr) =
      if q₁ = absorbQ d (msgAt inp f o 48) ∧ q₂ = squeezeQ a₁ then
        exec impl κ inp ops ⟨r ++ (round3Vals inp f o (real κ) a₁ a₂ c).toArray,
          ok && (real κ || (Val.b (msgAt inp f o 48)).isZero)⟩ tr
      else none := by
  rw [show (⟨r, ok⟩ : St) = ⟨r ++ ([] : List Val).toArray, ok⟩ by simp]
  simp only [roundOpsF, ite_true, List.cons_append, List.nil_append]
  simp only [exec_app, evalOp, rd_app_left _ _ hst, rd_app_left _ _ hcl, hd, hc, Val.toD, Val.toB,
    Val.toF, rd_app, rd_app0, List.nil_append, List.cons_append,
    List.getD_eq_getElem?_getD, List.getElem?_cons_succ, List.getElem?_cons_zero, Option.getD_some]
  by_cases h₁ : q₁ = absorbQ d (msgAt inp f o 48) <;> by_cases h₂ : q₂ = squeezeQ a₁ <;>
    simp_all [round3Vals, msgAt, elemAt]

theorem exec_regs {ops : List Op} {R R' : Array Val} {ok : Bool} {tr : Trace} (h : R = R') :
    exec impl κ inp ops ⟨R, ok⟩ tr = exec impl κ inp ops ⟨R', ok⟩ tr := by rw [h]

theorem exec_map_pure {α : Type} (xs : List α) (g : α → Op) (v : α → Val)
    (h : ∀ x regs, evalOp impl κ inp regs (g x) = .vals [v x] true) (ops : List Op) (r : Array Val)
    (ok : Bool) (tr : Trace) :
    exec impl κ inp (xs.map g ++ ops) ⟨r, ok⟩ tr = exec impl κ inp ops ⟨r ++ (xs.map v).toArray, ok⟩ tr := by
  induction xs generalizing r with
  | nil => simp
  | cons x xs ih =>
    rw [List.map_cons, List.cons_append, exec_vals impl κ inp (h x _)]
    simp only [Bool.and_true]
    rw [ih]; simp [Array.append_assoc]

/-- The univariate round's message values. -/
def uniEs (f o : ℕ) : List F := (List.range 127).map fun i => elemAt inp f (o + 16 * i)

/-- The registers of a univariate round (`uniOps`). -/
def uniVals (f o : ℕ) (pe : Array F) (a₁ a₂ : Digest) : List Val :=
  let x := impl.lagrangeS (uniEs inp f o).toArray (chF a₂ 0) pe
  [.b (msgAt inp f o uniBytes), .d a₁, .d a₂, .f (chF a₂ 0)] ++ (uniEs inp f o).map .f ++
    [.af (uniEs inp f o).toArray, .af pe, .f x.1, .f x.2, .b (msgAt inp f (o + 2032) 16)]

theorem exec_uni (f o st pt : ℕ) (r : Array Val) (ok : Bool) (ops : List Op) (d : Digest)
    (hst : st < r.size) (hpt : pt < r.size) (hd : (rd r st).toD = d) (q₁ q₂ : ByteArray)
    (a₁ a₂ : Digest) (tr : Trace) :
    exec impl κ inp (uniOps f o st pt r.size ++ ops) ⟨r, ok⟩ ((q₁, a₁) :: (q₂, a₂) :: tr) =
      if q₁ = absorbQ d (msgAt inp f o uniBytes) ∧ q₂ = squeezeQ a₁ then
        exec impl κ inp ops ⟨r ++ (uniVals impl inp f o (impl.targetS κ (rd r pt).toAF) a₁ a₂).toArray,
          ok && (Val.b (msgAt inp f (o + 2032) 16)).isZero⟩ tr
      else none := by
  rw [show (⟨r, ok⟩ : St) = ⟨r ++ ([] : List Val).toArray, ok⟩ by simp, uniOps, List.append_assoc,
    List.append_assoc]
  simp only [uniHead, List.cons_append, List.nil_append]
  generalize hM : uniElems f o ++ (uniTail f o pt r.size ++ ops) = M
  simp only [exec_app, evalOp, rd_app_left _ _ hst, hd, toD_d, Val.toB, rd_app,
    rd_app0, List.nil_append, List.cons_append, List.getD_eq_getElem?_getD, List.getElem?_cons_succ,
    List.getElem?_cons_zero, Option.getD_some]
  simp only [msgAt]
  by_cases h₁ : q₁ = absorbQ d (inp.π.extract (absOff f o) (absOff f o + uniBytes)) <;>
    by_cases h₂ : q₂ = squeezeQ a₁ <;>
    simp only [h₁, h₂, ite_true, ite_false, and_self, and_false, false_and, reduceCtorEq,
      Bool.and_true] <;> try rfl
  subst hM
  rw [uniElems, exec_map_pure impl κ inp _ _ (fun i => .f (elemAt inp f (o + 16 * i))) (fun _ _ => rfl)]
  obtain ⟨L, hL⟩ : ∃ L : List Val, L = [Val.b (inp.π.extract (absOff f o) (absOff f o + uniBytes)),
    Val.d a₁, Val.d a₂, Val.f (chF a₂ 0)] ++ (uniEs inp f o).map .f := ⟨_, rfl⟩
  have hLen : L.length = 131 := by simp [hL, uniEs]
  rw [exec_regs impl κ inp (R' := r ++ L.toArray) (by apply Array.ext'; simp [hL, uniEs])]
  have hpack : ((List.range 127).map (r.size + 4 + ·)).map (fun x => (rd (r ++ L.toArray) x).toF) =
      uniEs inp f o := by
    rw [List.map_map]
    refine List.ext_getElem (by simp [uniEs]) fun i h₁ h₂ => ?_
    have hi : i < 127 := by simpa using h₁
    simp only [uniEs, List.getElem_map, List.getElem_range, Function.comp_apply]
    rw [show r.size + 4 + i = r.size + (4 + i) by omega, rd_app, hL,
      List.getD_append_right _ _ _ _ (by simp), List.getD_eq_getElem _ _ (by simp; omega)]
    simp [Val.toF, uniEs]
  have h3 : ∀ X : List Val, rd (r ++ (L ++ X).toArray) (r.size + 3) = .f (chF a₂ 0) := by
    intro X; rw [rd_app, hL]; rfl
  have h131 : ∀ X : List Val, rd (r ++ (L ++ X).toArray) (r.size + 131) = X.getD 0 default := by
    intro X; rw [rd_app, List.getD_append_right _ _ _ _ (by omega), hLen]
  have h132 : ∀ X : List Val, rd (r ++ (L ++ X).toArray) (r.size + 132) = X.getD 1 default := by
    intro X; rw [rd_app, List.getD_append_right _ _ _ _ (by omega), hLen]
  have h135 : ∀ X : List Val, rd (r ++ (L ++ X).toArray) (r.size + 135) = X.getD 4 default := by
    intro X; rw [rd_app, List.getD_append_right _ _ _ _ (by omega), hLen]
  simp only [uniTail, List.cons_append, List.nil_append, exec_app, evalOp, hpack,
    List.append_assoc, List.cons_append, List.nil_append, rd_app_left _ _ hpt, h3, h131, h132, h135,
    List.getD_cons_succ, List.getD_cons_zero]
  simp [uniVals, hL, Val.toF, Val.toAF, msgAt, allK]

/-- A round's next claim. -/
def g3 (f o : ℕ) (a₂ : Digest) (claim : F) : F :=
  let r := chF a₂ 0
  let c₀ := elemAt inp f o; let c₁ := elemAt inp f (o + 16); let c₂ := elemAt inp f (o + 32)
  c₀ + r * (c₁ + r * (c₂ + r * (claim + (c₁ + c₂))))

/-- **Reference: `n` degree-3 F rounds** from round `j`, state `d`, claim `c`: the registers, the
flag, the final state and claim, the rest of the trace. -/
def rounds3T (f o real : ℕ) : ℕ → ℕ → Digest → F → Trace → Option (List Val × Bool × Digest × F × Trace)
  | 0, _, d, c, tr => some ([], true, d, c, tr)
  | n + 1, j, d, c, (q₁, a₁) :: (q₂, a₂) :: tr =>
    if q₁ = absorbQ d (msgAt inp f (o + j * 48) 48) ∧ q₂ = squeezeQ a₁ then
      let re := decide (j < real)
      (rounds3T f o real n (j + 1) a₂ (if re then g3 inp f (o + j * 48) a₂ c else c) tr).map fun x =>
        (round3Vals inp f (o + j * 48) re a₁ a₂ c ++ x.1,
          (re || (Val.b (msgAt inp f (o + j * 48) 48)).isZero) && x.2.1, x.2.2)
    else none
  | _ + 1, _, _, _, _ => none

theorem round3Vals_length (f o : ℕ) (re : Bool) (a₁ a₂ : Digest) (c : F) :
    (round3Vals inp f o re a₁ a₂ c).length = 16 := by simp [round3Vals]

theorem exec_rounds3 (f o : ℕ) (real : KC ℕ) (n j st cl : ℕ) (r : Array Val) (ok : Bool)
    (ops : List Op) (d : Digest) (c : F) (hst : st < r.size) (hcl : cl < r.size)
    (hd : rd r st = .d d) (hc : rd r cl = .f c) (tr : Trace) :
    exec impl κ inp (roundsOps f o 3 false real n j st cl r.size ++ ops) ⟨r, ok⟩ tr =
      (rounds3T inp f o (real κ) n j d c tr).bind fun x =>
        exec impl κ inp ops ⟨r ++ x.1.toArray, ok && x.2.1⟩ x.2.2.2.2 := by
  induction n generalizing j st cl r ok d c tr with
  | zero => simp [roundsOps, rounds3T]
  | succ n ih =>
    rcases tr with _ | ⟨⟨q₁, a₁⟩, _ | ⟨⟨q₂, a₂⟩, tr⟩⟩
    · simp [roundsOps, roundOpsF, roundW, exec, evalOp, rounds3T]
    · simp [roundsOps, roundOpsF, roundW, exec, evalOp, rounds3T]
    simp only [roundsOps, roundW, ite_true, Bool.false_eq_true, ite_false, List.append_assoc]
    rw [show o + j * roundBytes false = o + j * 48 from rfl,
      exec_round3 impl κ inp f (o + j * 48) _ st cl r ok _ d c hst hcl hd hc]
    simp only [rounds3T]
    by_cases h : q₁ = absorbQ d (msgAt inp f (o + j * 48) 48) ∧ q₂ = squeezeQ a₁
    · rw [if_pos h, if_pos h]
      have hs : (r ++ (round3Vals inp f (o + j * 48) (decide (j < real κ)) a₁ a₂ c).toArray).size =
          r.size + 16 := by simp [round3Vals_length]
      rw [show r.size + 16 - 1 = r.size + 15 from rfl, ← hs, ih (j + 1) (r.size + 2) (r.size + 15) _ _ a₂
        (if decide (j < real κ) then g3 inp f (o + j * 48) a₂ c else c) (by omega) (by omega)
        (by rw [rd_app]; rfl) (by rw [rd_app]; simp [round3Vals, g3]; split_ifs <;> rfl)]
      simp [Option.bind_map, Function.comp_def, Array.append_assoc, Bool.and_assoc]
    · rw [if_neg h, if_neg h]; rfl

theorem sqzT_spec {n : ℕ} {d : Digest} {tr : Trace} {x : List Digest × Trace}
    (h : sqzT n d tr = some x) : x.1.length = n := by
  induction n generalizing d tr x with
  | zero => simp [sqzT] at h; subst h; rfl
  | succ n ih =>
    simp only [sqzT, Option.bind_eq_some_iff, Option.map_eq_some_iff] at h
    obtain ⟨p, -, y, hy, rfl⟩ := h
    simp [ih hy]

theorem rounds3T_spec {f o real n j : ℕ} {d : Digest} {c : F} {tr : Trace}
    {x : List Val × Bool × Digest × F × Trace} (h : rounds3T inp f o real n j d c tr = some x) :
    x.1.length = 16 * n ∧ (0 < n → x.1.getD (16 * n - 14) default = .d x.2.2.1) ∧
      (0 < n → x.1.getD (16 * n - 1) default = .f x.2.2.2.1) := by
  induction n generalizing j d c tr x with
  | zero => simp [rounds3T] at h; subst h; simp
  | succ n ih =>
    rcases tr with _ | ⟨⟨q₁, a₁⟩, _ | ⟨⟨q₂, a₂⟩, tr⟩⟩ <;> simp only [rounds3T, reduceCtorEq] at h
    by_cases hq : q₁ = absorbQ d (msgAt inp f (o + j * 48) 48) ∧ q₂ = squeezeQ a₁
    swap; · rw [if_neg hq] at h; cases h
    rw [if_pos hq] at h
    simp only [Option.map_eq_some_iff] at h
    obtain ⟨y, hy, rfl⟩ := h
    obtain ⟨h1, h2, h3⟩ := ih hy
    refine ⟨by simp [round3Vals_length, h1]; ring, fun _ => ?_, fun _ => ?_⟩
    · rcases Nat.eq_zero_or_pos n with rfl | hn
      · simp [rounds3T] at hy; subst hy; simp [round3Vals]
      · rw [List.getD_append_right _ _ _ _ (by rw [round3Vals_length]; omega), round3Vals_length,
          show 16 * (n + 1) - 14 - 16 = 16 * n - 14 by omega, h2 hn]
    · rcases Nat.eq_zero_or_pos n with rfl | hn
      · simp [rounds3T] at hy; subst hy
        simp only [round3Vals]; split <;> simp_all [g3]
      · rw [List.getD_append_right _ _ _ _ (by rw [round3Vals_length]; omega), round3Vals_length,
          show 16 * (n + 1) - 1 - 16 = 16 * n - 1 by omega, h3 hn]

theorem exec_sqzC (n st : ℕ) (r : Array Val) (ok : Bool) (ops : List Op) (hst : st < r.size) (tr : Trace) :
    exec impl κ inp (sqzCoordOps n st r.size ++ ops) ⟨r, ok⟩ tr =
      (sqzT n (rd r st).toD tr).bind fun p => exec impl κ inp ops ⟨r ++ (p.1.flatMap coordVals).toArray, ok⟩ p.2 := by
  rw [exec_append, exec_sqzCoordOps impl κ inp n st r.size ⟨r, ok⟩ tr rfl hst, Option.bind_map]; rfl

theorem exec_absorb (f o len st : ℕ) (r : Array Val) (ok : Bool) (ops : List Op) (d : Digest)
    (hst : st < r.size) (hd : rd r st = .d d) (q : ByteArray) (a : Digest) (tr : Trace) :
    exec impl κ inp (absorbOps f o len st r.size ++ ops) ⟨r, ok⟩ ((q, a) :: tr) =
      if q = absorbQ d (msgAt inp f o len) then
        exec impl κ inp ops ⟨r ++ [Val.b (msgAt inp f o len), .d a].toArray, ok⟩ tr else none := by
  rw [show (⟨r, ok⟩ : St) = ⟨r ++ ([] : List Val).toArray, ok⟩ by simp]
  simp only [absorbOps, List.cons_append, List.nil_append, exec_app, evalOp, rd_app_left _ _ hst, hd,
    Val.toD, Val.toB, rd_app0, List.getD_cons_zero, Bool.and_true]
  by_cases h : q = absorbQ d (msgAt inp f o len) <;> simp_all [msgAt]

/-- The coordinates of `n` squeeze answers, two per answer. -/
def coordsOf (as : List Digest) : List F :=
  (List.range (2 * as.length)).map fun x => chF (as.getD (x / 2) zeroD) (x % 2)

theorem flatMap_coord_getD (as : List Digest) (i k : ℕ) (hi : i < as.length) (hk : k < 3) :
    (as.flatMap coordVals).getD (3 * i + k) default = (coordVals (as.getD i zeroD)).getD k default := by
  induction as generalizing i with
  | nil => simp at hi
  | cons a as ih =>
    rw [List.flatMap_cons]
    rcases i with _ | i
    · rw [List.getD_append _ _ _ _ (by simp [coordVals]; omega)]; simp
    · rw [List.getD_append_right _ _ _ _ (by simp [coordVals]; omega),
        show 3 * (i + 1) + k - (coordVals a).length = 3 * i + k by simp [coordVals]; omega,
        ih i (by simpa using hi)]
      simp

theorem pack_coords (as : List Digest) (r : Array Val) :
    ((List.range (2 * as.length)).map fun x => r.size + 3 * (x / 2) + 1 + x % 2).map
      (fun x => (rd (r ++ (as.flatMap coordVals).toArray) x).toF) = coordsOf as := by
  rw [List.map_map, coordsOf]
  refine List.map_congr_left fun x hx => ?_
  have hx' : x / 2 < as.length := by simp at hx; omega
  simp only [Function.comp_apply, show r.size + 3 * (x / 2) + 1 + x % 2 = r.size + (3 * (x / 2) + (1 + x % 2))
    by omega, rd_app, flatMap_coord_getD as (x / 2) (1 + x % 2) hx' (by omega)]
  rcases Nat.mod_two_eq_zero_or_one x with h | h <;> simp [coordVals, h, Val.toF]

theorem rd_coord_last (as : List Digest) (r : Array Val) (n : ℕ) (hn : as.length = n + 1) :
    rd (r ++ (as.flatMap coordVals ++ [Val.af (coordsOf as).toArray]).toArray) (r.size + 3 * n) =
      .d (as.getD n zeroD) := by
  rw [rd_app, List.getD_append _ _ _ _ (by simp [coordVals, List.length_flatMap, hn]; omega),
    show 3 * n = 3 * n + 0 from rfl, flatMap_coord_getD as n 0 (by omega) (by omega)]
  rfl

/-! ## Phase Z end to end -/

def phZ1 : Phase := ⟨"Z1", .squeezes 10 (.coords (mm 13))⟩
def phZ2 : Phase := ⟨"Z2", .uni fZ2⟩
def phZ3 : Phase := ⟨"Z3", .rounds fZ3 26 3 false (mm 6)⟩
def phZend : Phase := ⟨"Zend", .absorb fZend 32⟩

theorem phases_Z : (phases.drop 3).take 4 = [phZ1, phZ2, phZ3, phZend] := rfl

/-- Phase Z's ops (table phases 3–6) from a context. -/
def zOps (c : GCtx) : List Op :=
  let r₁ := genPhase 3 phZ1 c
  let r₂ := genPhase 4 phZ2 r₁.2
  let r₃ := genPhase 5 phZ3 r₂.2
  r₁.1 ++ r₂.1 ++ r₃.1 ++ (genPhase 6 phZend r₃.2).1

/-- **Reference semantics of phase Z** from the state `d`: Z1's ten squezes and their twenty
coordinates, Z2's univariate round and its value `lagrangeS(P, λ)` (the first claim), Z3's 26
degree-3 rounds (`rounds3T`, the last `26 − (m − 6)` dummies for `m = 30`), Zend's absorb of
`â ‖ b̂`; the registers, the flag, the rest of the trace. -/
def refZ (d : Digest) (tr : Trace) : Option (List Val × Bool × Trace) :=
  (sqzT 10 d tr).bind fun p =>
  let v₁ := p.1.flatMap coordVals ++ [.af (coordsOf p.1).toArray]
  match p.2 with
  | (q₁, a₁) :: (q₂, a₂) :: tr₂ =>
    if q₁ = absorbQ (p.1.getD 9 zeroD) (msgAt inp fZ2 (phaseOff 4 fZ2) uniBytes) ∧
        q₂ = squeezeQ a₁ then
      (rounds3T inp fZ3 (phaseOff 5 fZ3) (mm 6 κ) 26 0 a₂
          (impl.lagrangeS (uniEs inp fZ2 (phaseOff 4 fZ2)).toArray (chF a₂ 0)
            (impl.targetS κ (coordsOf p.1).toArray)).1 tr₂).bind fun x =>
        match x.2.2.2.2 with
        | (q, a) :: tr₄ =>
          if q = absorbQ x.2.2.1 (msgAt inp fZend (phaseOff 6 fZend) 32) then
            some (v₁ ++ uniVals impl inp fZ2 (phaseOff 4 fZ2) (impl.targetS κ (coordsOf p.1).toArray)
                a₁ a₂ ++ x.1 ++
                [.b (msgAt inp fZend (phaseOff 6 fZend) 32), .d a],
              (Val.b (msgAt inp fZ2 (phaseOff 4 fZ2 + 2032) 16)).isZero && x.2.1, tr₄)
          else none
        | [] => none
    else none
  | _ => none

/-- **Phase Z, end to end** (the S-0 kill test): Z's ops on a trace are `refZ`. -/
theorem exec_phaseZ (c : GCtx) (r : Array Val) (ok : Bool) (ops : List Op) (d : Digest)
    (hb : c.next = r.size) (hst : c.st < r.size) (hd : rd r c.st = .d d) (tr : Trace) :
    exec impl κ inp (zOps c ++ ops) ⟨r, ok⟩ tr =
      (refZ impl κ inp d tr).bind fun x => exec impl κ inp ops ⟨r ++ x.1.toArray, ok && x.2.1⟩ x.2.2 := by
  obtain ⟨b, st, u, pa, fr, pt, outs⟩ := c
  simp only at hb hst hd; subst hb
  simp only [zOps, genPhase, phZ1, phZ2, phZ3, phZend, List.append_assoc, initClaim, initOps,
    Init.width, roundW, ite_true, Bool.false_eq_true, ite_false, show fZend ≠ fStmt by decide,
    show fZend ≠ fFinal by decide, show ¬(fZend = fLrEnd ∨ fZend = fEEnd) by decide, List.nil_append,
    Nat.add_zero]
  rw [exec_sqzC impl κ inp 10 st r ok _ hst, hd, refZ]
  simp only [Val.toD]
  rcases hs : sqzT 10 d tr with _ | ⟨as, tr₁⟩
  · rfl
  have hlen : as.length = 10 := sqzT_spec hs
  simp only [Option.bind_some, List.singleton_append]
  rw [exec_vals impl κ inp (vs := [.af (coordsOf as).toArray]) (ok := true)
    (by simp only [evalOp, show 2 * 10 = 2 * as.length by rw [hlen], pack_coords])]
  simp only [Bool.and_true, app_app]
  set v₁ := as.flatMap coordVals ++ [Val.af (coordsOf as).toArray] with hv₁
  have hs₁ : (r ++ v₁.toArray).size = r.size + (3 * 10 + 1) := by
    simp [hv₁, List.length_flatMap, coordVals, hlen]
  have hst₁ : rd (r ++ v₁.toArray) (r.size + 3 * 10 - 3) = .d (as.getD 9 zeroD) :=
    rd_coord_last as r 9 hlen
  rw [← hs₁]
  rcases tr₁ with _ | ⟨⟨q₁, a₁⟩, _ | ⟨⟨q₂, a₂⟩, tr₂⟩⟩
  · simp [uniOps, uniHead, exec, evalOp]
  · simp [uniOps, uniHead, exec, evalOp]
  have hpt₁ : rd (r ++ v₁.toArray) (r.size + 3 * 10) = .af (coordsOf as).toArray := by
    rw [rd_app, hv₁, List.getD_append_right _ _ _ _ (by simp [List.length_flatMap, coordVals, hlen])]
    simp [List.length_flatMap, coordVals, hlen]
  rw [exec_uni impl κ inp fZ2 _ _ _ _ ok _ (as.getD 9 zeroD) (by rw [hs₁]; omega) (by rw [hs₁]; omega)
    (by rw [hst₁]; rfl), hpt₁]
  simp only
  by_cases h₁ : q₁ = absorbQ (as.getD 9 zeroD) (msgAt inp fZ2 (phaseOff 4 fZ2) uniBytes) ∧
    q₂ = squeezeQ a₁
  swap; · rw [if_neg h₁, if_neg h₁]; rfl
  rw [if_pos h₁, if_pos h₁]
  set r₁ := r ++ v₁.toArray
  set U := uniVals impl inp fZ2 (phaseOff 4 fZ2) (impl.targetS κ (coordsOf as).toArray) a₁ a₂ with hU
  have hUl : U.length = 136 := by simp [hU, uniVals, uniEs]
  have hs₂ : (r₁ ++ U.toArray).size = r.size + 167 := by simp [hUl, hs₁]
  have hst₂ : rd (r₁ ++ U.toArray) (r₁.size + 2) = .d a₂ := by rw [rd_app, hU]; rfl
  have hcl₂ : rd (r₁ ++ U.toArray) (r₁.size + 133) =
      .f (impl.lagrangeS (uniEs inp fZ2 (phaseOff 4 fZ2)).toArray (chF a₂ 0)
        (impl.targetS κ (coordsOf as).toArray)).1 := by
    rw [rd_app, hU, uniVals, List.getD_append_right _ _ _ _ (by simp [uniEs])]; simp [uniEs]
  rw [← hs₂]
  erw [exec_rounds3 impl κ inp fZ3 _ (mm 6) 26 0 _ _ _ _ _ a₂ _ (by rw [hs₂, hs₁]; omega)
    (by rw [hs₂, hs₁]; omega) hst₂ hcl₂]
  rcases hx : rounds3T inp fZ3 (phaseOff 5 fZ3) (mm 6 κ) 26 0 a₂
    (impl.lagrangeS (uniEs inp fZ2 (phaseOff 4 fZ2)).toArray (chF a₂ 0)
      (impl.targetS κ (coordsOf as).toArray)).1 tr₂ with _ | x
  · rfl
  obtain ⟨hxl, hxst, -⟩ := rounds3T_spec inp hx
  simp only [Option.bind_some]
  set r₂ := r₁ ++ U.toArray
  have hs₃ : (r₂ ++ x.1.toArray).size = r₁.size + 136 + (0 + 16 * 26) := by
    simp [hxl, r₂, hUl]
  have hst₃ : rd (r₂ ++ x.1.toArray) (r₂.size + 16 * 26 - 16 + 2) = .d x.2.2.1 := by
    rw [show r₂.size + 16 * 26 - 16 + 2 = r₂.size + (16 * 26 - 14) by omega, rd_app, hxst (by decide)]
  simp only [show (26 = 0) = False by decide, ite_false]
  rw [← hs₃]
  obtain ⟨l, okx, dx, cx, tr₃⟩ := x
  rcases tr₃ with _ | ⟨⟨q, a⟩, tr₄⟩
  · simp [absorbOps, exec, evalOp]
  rw [exec_absorb impl κ inp fZend _ 32 _ _ _ _ dx (by rw [hs₃]; omega) hst₃]
  simp only
  by_cases h₄ : q = absorbQ dx (msgAt inp fZend (phaseOff 6 fZend) 32)
  · rw [if_pos h₄, if_pos h₄]
    simp only [Option.bind_some, hv₁, r₁, r₂, app_app, List.append_assoc, Bool.and_assoc]
  · rw [if_neg h₄, if_neg h₄]; rfl

/-! ## The other phases: reference semantics, stated

The reference semantics of every shape, written as functions of the trace (the "structured Lean"
reading of each phase); `exec_genPhase` proves that a phase's ops are its reference. Phase Z's
instance is also proved directly above (`exec_phaseZ`). -/

/-- A degree-2 F round's next claim `c₀ + r(c₁ + r c₂)`. -/
def g2 (f o : ℕ) (a₂ : Digest) : F :=
  let r := chF a₂ 0
  elemAt inp f o + r * (elemAt inp f (o + 16) + r * elemAt inp f (o + 32))

/-- The registers of one degree-2 F round (`roundOpsF … 2`). -/
def round2Vals (f o : ℕ) (real : Bool) (a₁ a₂ : Digest) (claim : Val) : List Val :=
  let r := chF a₂ 0
  let c₀ := elemAt inp f o; let c₁ := elemAt inp f (o + 16); let c₂ := elemAt inp f (o + 32)
  [.b (msgAt inp f o 48), .d a₁, .d a₂, .f r, .f c₀, .f c₁, .f c₂, .f (c₁ + c₂), .f (r * c₂),
   .f (c₁ + r * c₂), .f (r * (c₁ + r * c₂)), .f (g2 inp f o a₂),
   if real then .f (g2 inp f o a₂) else claim]

/-- The registers of one degree-3 F round with the claim as a register value (`keep` copies it). -/
def round3V (f o : ℕ) (real : Bool) (a₁ a₂ : Digest) (claim : Val) : List Val :=
  let r := chF a₂ 0
  let c₀ := elemAt inp f o; let c₁ := elemAt inp f (o + 16); let c₂ := elemAt inp f (o + 32)
  let s := c₁ + c₂; let c₃ := claim.toF + s
  let t₁ := r * c₃; let t₂ := c₂ + t₁; let t₃ := r * t₂; let t₄ := c₁ + t₃; let t₅ := r * t₄
  let g := c₀ + t₅
  [.b (msgAt inp f o 48), .d a₁, .d a₂, .f r, .f c₀, .f c₁, .f c₂, .f s, .f c₃, .f t₁, .f t₂, .f t₃,
   .f t₄, .f t₅, .f g, if real then .f g else claim]

/-- The K coefficient at byte `o` of field `f`. -/
def elemKAt (f o : ℕ) : K := K.ofBytes (bytesAt inp.π (absOff f o) 32)

/-- A K round's next claim. -/
def gK (f o : ℕ) (a₂ : Digest) : K :=
  let r := chK a₂
  elemKAt inp f o + r * (elemKAt inp f (o + 32) + r * elemKAt inp f (o + 64))

/-- The registers of one K round (`roundOpsK`). -/
def roundKVals (f o : ℕ) (real : Bool) (a₁ a₂ : Digest) (claim : Val) : List Val :=
  let r := chK a₂
  let c₀ := elemKAt inp f o; let c₁ := elemKAt inp f (o + 32); let c₂ := elemKAt inp f (o + 64)
  [.b (msgAt inp f o 96), .d a₁, .d a₂, .k r, .k c₀, .k c₁, .k c₂, .k (c₁ + c₂), .k (r * c₂),
   .k (c₁ + r * c₂), .k (r * (c₁ + r * c₂)), .k (gK inp f o a₂),
   if real then .k (gK inp f o a₂) else claim]

/-- **Reference: `n` sumcheck rounds of degree `deg` (F) or in K**, from round `j`, state `d` and
claim `c` (a `Val`): degree 3 completes `c₃` from the claim; degree 2 and K check `c₁ + c₂ =
claim`; a dummy round (`j ≥ real`) has a zero message and keeps the claim. -/
def roundsT (f o deg : ℕ) (inK : Bool) (real : ℕ) :
    ℕ → ℕ → Digest → Val → Trace → Option (List Val × Bool × Trace)
  | 0, _, _, _, tr => some ([], true, tr)
  | n + 1, j, d, c, (q₁, a₁) :: (q₂, a₂) :: tr =>
    let rb := roundBytes inK
    let o' := o + j * rb
    if q₁ = absorbQ d (msgAt inp f o' rb) ∧ q₂ = squeezeQ a₁ then
      let re := decide (j < real)
      let vs := if inK then roundKVals inp f o' re a₁ a₂ c
        else if deg = 3 then round3V inp f o' re a₁ a₂ c else round2Vals inp f o' re a₁ a₂ c
      let chk := if inK then (Val.k (elemKAt inp f (o' + 32) + elemKAt inp f (o' + 64))).eqv c
        else if deg = 3 then true else (Val.f (elemAt inp f (o' + 16) + elemAt inp f (o' + 32))).eqv c
      (roundsT f o deg inK real n (j + 1) a₂ (vs.getLastD default) tr).map fun x =>
        (vs ++ x.1, (!re || chk) && (re || (Val.b (msgAt inp f o' rb)).isZero) && x.2.1, x.2.2)
    else none
  | _ + 1, _, _, _, _ => none

/-- The first claim's registers (`initOps`). -/
def initVals (init : Init) (f o : ℕ) (inK : Bool) : List Val :=
  match init with
  | .uni => []
  | .zero => [.f 0]
  | .free =>
    if inK then [.k (elemKAt inp f (o + 32)), .k (elemKAt inp f (o + 64)),
      .k (elemKAt inp f (o + 32) + elemKAt inp f (o + 64))]
    else [.f (elemAt inp f (o + 16)), .f (elemAt inp f (o + 32)),
      .f (elemAt inp f (o + 16) + elemAt inp f (o + 32))]

/-- **One sumcheck round, any kind** (degree 3 / 2 over F, or K), against its reference. -/
theorem exec_round (f o deg : ℕ) (inK : Bool) (real : KC Bool) (st cl : ℕ) (r : Array Val) (ok : Bool)
    (ops : List Op) (d : Digest) (c : Val) (hst : st < r.size) (hcl : cl < r.size)
    (hd : (rd r st).toD = d) (hc : rd r cl = c) (q₁ q₂ : ByteArray) (a₁ a₂ : Digest) (tr : Trace) :
    exec impl κ inp ((if inK then roundOpsK f o real st cl r.size else roundOpsF f o deg real st cl r.size)
        ++ ops) ⟨r, ok⟩ ((q₁, a₁) :: (q₂, a₂) :: tr) =
      if q₁ = absorbQ d (msgAt inp f o (roundBytes inK)) ∧ q₂ = squeezeQ a₁ then
        exec impl κ inp ops ⟨r ++ (if inK then roundKVals inp f o (real κ) a₁ a₂ c
          else if deg = 3 then round3V inp f o (real κ) a₁ a₂ c else round2Vals inp f o (real κ) a₁ a₂ c).toArray,
          ok && ((!real κ || (if inK then (Val.k (elemKAt inp f (o + 32) + elemKAt inp f (o + 64))).eqv c
            else if deg = 3 then true else (Val.f (elemAt inp f (o + 16) + elemAt inp f (o + 32))).eqv c)) &&
            (real κ || (Val.b (msgAt inp f o (roundBytes inK))).isZero))⟩ tr
      else none := by
  rw [show (⟨r, ok⟩ : St) = ⟨r ++ ([] : List Val).toArray, ok⟩ by simp]
  generalize hm : msgAt inp f o (roundBytes inK) = m
  by_cases h3 : deg = 3 <;> cases inK <;>
  simp only [roundOpsF, roundOpsK, roundBytes, h3, ite_true, ite_false, Bool.false_eq_true,
    List.cons_append, List.nil_append] at hm ⊢ <;>
  simp only [exec_app, evalOp, rd_app_left _ _ hst, rd_app_left _ _ hcl, hd, hc, toD_d, Val.toB,
    rd_app, rd_app0, List.nil_append, List.cons_append, List.getD_cons_succ, List.getD_cons_zero] <;>
  by_cases h₁ : q₁ = absorbQ d m <;> by_cases h₂ : q₂ = squeezeQ a₁ <;>
    simp_all [round3V, round2Vals, roundKVals, msgAt, elemAt, elemKAt, g2, gK, Bool.and_assoc, Val.toF,
      Val.toK]

/-- The registers of one round of any kind. -/
def roundV (f o deg : ℕ) (inK re : Bool) (a₁ a₂ : Digest) (c : Val) : List Val :=
  if inK then roundKVals inp f o re a₁ a₂ c
  else if deg = 3 then round3V inp f o re a₁ a₂ c else round2Vals inp f o re a₁ a₂ c

theorem roundV_spec (f o deg : ℕ) (inK re : Bool) (a₁ a₂ : Digest) (c : Val) :
    (roundV inp f o deg inK re a₁ a₂ c).length = (if inK then 13 else roundW deg) ∧
    (roundV inp f o deg inK re a₁ a₂ c).getD 2 default = .d a₂ ∧
    (roundV inp f o deg inK re a₁ a₂ c).getD ((if inK then 13 else roundW deg) - 1) default =
      (roundV inp f o deg inK re a₁ a₂ c).getLastD default := by
  by_cases h3 : deg = 3 <;> cases inK <;>
    simp [roundV, h3, roundW, round3V, round2Vals, roundKVals]

/-- **`n` rounds of any kind** against `roundsT`. -/
theorem exec_roundsT (f o deg : ℕ) (inK : Bool) (real : KC ℕ) (n j st cl : ℕ) (r : Array Val)
    (ok : Bool) (ops : List Op) (d : Digest) (c : Val) (hst : st < r.size) (hcl : cl < r.size)
    (hd : (rd r st).toD = d) (hc : rd r cl = c) (tr : Trace) :
    exec impl κ inp (roundsOps f o deg inK real n j st cl r.size ++ ops) ⟨r, ok⟩ tr =
      (roundsT inp f o deg inK (real κ) n j d c tr).bind fun x =>
        exec impl κ inp ops ⟨r ++ x.1.toArray, ok && x.2.1⟩ x.2.2 := by
  induction n generalizing j st cl r ok d c tr with
  | zero => simp [roundsOps, roundsT]
  | succ n ih =>
    rcases tr with _ | ⟨⟨q₁, a₁⟩, _ | ⟨⟨q₂, a₂⟩, tr⟩⟩
    · cases inK <;> simp [roundsOps, roundOpsF, roundOpsK, exec, evalOp, roundsT] <;> split <;> rfl
    · cases inK <;> simp [roundsOps, roundOpsF, roundOpsK, exec, evalOp, roundsT] <;> split <;> simp
    simp only [roundsOps, List.append_assoc]
    rw [exec_round impl κ inp f _ deg inK _ st cl r ok _ d c hst hcl hd hc]
    simp only [roundsT]
    have hv := roundV_spec inp f (o + j * roundBytes inK) deg inK (decide (j < real κ)) a₁ a₂ c
    simp only [roundV] at hv
    by_cases h : q₁ = absorbQ d (msgAt inp f (o + j * roundBytes inK) (roundBytes inK)) ∧
      q₂ = squeezeQ a₁
    · simp only [h, and_self, ite_true]
      obtain ⟨hl, h2, hL⟩ := hv
      set vs := (if inK then roundKVals inp f (o + j * roundBytes inK) (decide (j < real κ)) a₁ a₂ c
        else if deg = 3 then round3V inp f (o + j * roundBytes inK) (decide (j < real κ)) a₁ a₂ c
        else round2Vals inp f (o + j * roundBytes inK) (decide (j < real κ)) a₁ a₂ c) with hvs
      set w := (if inK then 13 else roundW deg) with hw
      have hw3 : 3 ≤ w := by simp only [hw, roundW]; split_ifs <;> omega
      have hs : (r ++ vs.toArray).size = r.size + w := by simp [hl]
      rw [show r.size + w = (r ++ vs.toArray).size from hs.symm,
        ih (j + 1) (r.size + 2) ((r ++ vs.toArray).size - 1) _ _ a₂ (vs.getLastD default) (by omega)
          (by omega) (by rw [rd_app, h2]; rfl)
          (by rw [hs, show r.size + w - 1 = r.size + (w - 1) by omega, rd_app, hL]),
        Option.bind_map]
      simp [Array.append_assoc, Bool.and_assoc]
    · simp only [h, ite_false, Option.bind_none]

theorem exec_roundsT' (f o deg : ℕ) (inK : Bool) (real : KC ℕ) (n j st cl b : ℕ) (r : Array Val)
    (ok : Bool) (ops : List Op) (d : Digest) (c : Val) (hb : b = r.size) (hst : st < r.size)
    (hcl : cl < r.size) (hd : (rd r st).toD = d) (hc : rd r cl = c) (tr : Trace) :
    exec impl κ inp (roundsOps f o deg inK real n j st cl b ++ ops) ⟨r, ok⟩ tr =
      (roundsT inp f o deg inK (real κ) n j d c tr).bind fun x =>
        exec impl κ inp ops ⟨r ++ x.1.toArray, ok && x.2.1⟩ x.2.2 := by
  subst hb; exact exec_roundsT impl κ inp f o deg inK real n j st cl r ok ops d c hst hcl hd hc tr

theorem exec_sqzOps (n st : ℕ) (r : Array Val) (ok : Bool) (ops : List Op) (hst : st < r.size)
    (tr : Trace) :
    exec impl κ inp (sqzOps n st r.size ++ ops) ⟨r, ok⟩ tr =
      (sqzT n (rd r st).toD tr).bind fun p => exec impl κ inp ops ⟨r ++ (p.1.map .d).toArray, ok⟩ p.2 := by
  induction n generalizing st r tr with
  | zero => simp [sqzOps, sqzT]
  | succ n ih =>
    rw [sqzOps, List.cons_append, exec_ask impl κ inp rfl, sqzT]
    rcases ans1 (squeezeQ (rd r st).toD) tr with _ | ⟨a, tr'⟩
    · rfl
    · simp only [Option.bind_some, Option.bind_map]
      have := ih r.size (r.push (.d a)) (by simp) tr'
      rw [show r.size + 1 = (r.push (.d a)).size by simp, this,
        show rd (r.push (.d a)) r.size = .d a from rd_push_size _ _]
      refine Option.bind_congr fun p _ => ?_
      simp only [Val.toD, Function.comp_apply, List.map_cons]
      congr 2; apply Array.ext'; simp

/-- **Reference: one Merkle step** at depth `h` of position `j`: the sibling slot, the bit, the
ordered halves, the node query (`0^64` for a depth the kind lacks), the kept digest. -/
def stepT (i h j so : ℕ) (cur : Digest) : Trace → Option (List Val × Bool × Digest × Trace)
  | (q, a) :: tr =>
    let act := decide (h < (lvl κ i).sib)
    let sib := bytesAt inp.π (absOff fSibs so) 32
    let b := j.testBit h
    let l := if b then sib else cur
    let r := if b then cur else sib
    if q = (if act then nodeQ i l r else nodeQ i zeroD zeroD) then
      some ([.d sib, .bit b, .d l, .d r, .d a, .d (if act then a else cur)],
        act || decide (sib = zeroD), if act then a else cur, tr)
    else none
  | [] => none

/-- `n` Merkle steps from depth `h`. -/
def stepsT (i j : ℕ) : ℕ → ℕ → ℕ → Digest → Trace → Option (List Val × Bool × Digest × Trace)
  | 0, _, _, cur, tr => some ([], true, cur, tr)
  | n + 1, h, so, cur, tr =>
    (stepT κ inp i h j so cur tr).bind fun x =>
      (stepsT i j n (h + 1) (so + 32) x.2.2.1 x.2.2.2).map fun y =>
        (x.1 ++ y.1, x.2.1 && y.2.1, y.2.2)

/-- **Reference: position `p` of level `i`** (answers `ans` of P2, fold weights `w`): the index,
the column query, the fold, the Merkle steps, the cap comparison. -/
def posT (i co so : ℕ) (ad : ℕ → Digest) (w : Array K) (p : ℕ) :
    Trace → Option (List Val × Bool × Trace)
  | (q, a) :: tr =>
    let L := lvlStar i
    let j := idxOf (lvl κ i).logN (ad (p / (lvl κ i).per)) (p % (lvl κ i).per)
    let col := inp.π.extract (absOff fCols (co + p * colBytes i))
      (absOff fCols (co + p * colBytes i) + colBytes i)
    if q = colQ i col then
      (stepsT κ inp i j L.sib 0 (so + p * L.sib * 32) a tr).map fun x =>
        let capIx := j >>> (lvl κ i).sib
        let capD := bytesAt inp.π (absOff fCaps (capOff i) + 32 * capIx) 32
        ([.n j, .b col, .d a, .k (dotKF w col)] ++ x.1 ++ [.n capIx, .d capD],
          x.2.1 && decide (x.2.2.1 = capD), x.2.2.2)
    else none
  | [] => none

/-- All positions of level `i`. -/
def posAllT (i co so : ℕ) (ad : ℕ → Digest) (w : Array K) :
    ℕ → ℕ → Trace → Option (List Val × Bool × Trace)
  | 0, _, tr => some ([], true, tr)
  | t + 1, p, tr =>
    (posT κ inp i co so ad w p tr).bind fun x =>
      (posAllT i co so ad w t (p + 1) x.2.2).map fun y => (x.1 ++ y.1, x.2.1 && y.2.1, y.2.2)

theorem stepT_spec {i h j so : ℕ} {cur : Digest} {tr : Trace} {y : List Val × Bool × Digest × Trace}
    (hy : stepT κ inp i h j so cur tr = some y) : y.1.length = 6 ∧ y.1.getD 5 default = .d y.2.2.1 := by
  rcases tr with _ | ⟨⟨q, a⟩, tr⟩
  · cases hy
  · simp only [stepT] at hy
    split_ifs at hy <;> cases hy <;> simp

theorem stepsT_spec {i j n h so : ℕ} {cur : Digest} {tr : Trace}
    {x : List Val × Bool × Digest × Trace} (hx : stepsT κ inp i j n h so cur tr = some x) :
    x.1.length = 6 * n ∧ (n = 0 → x.2.2.1 = cur) ∧ (0 < n → x.1.getD (6 * n - 1) default = .d x.2.2.1) := by
  induction n generalizing h so cur tr x with
  | zero => simp [stepsT] at hx; subst hx; simp
  | succ n ih =>
    simp only [stepsT, Option.bind_eq_some_iff, Option.map_eq_some_iff] at hx
    obtain ⟨y, hy, z, hz, rfl⟩ := hx
    obtain ⟨hl, h5⟩ := stepT_spec κ inp hy
    obtain ⟨h1, h2, h3⟩ := ih hz
    refine ⟨by simp [hl, h1]; ring, by omega, fun _ => ?_⟩
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · have hz0 : z.1 = [] := List.length_eq_zero_iff.1 (by simpa using h1)
      rw [hz0, h2 rfl]; simpa using h5
    · rw [List.getD_append_right _ _ _ _ (by omega), hl,
        show 6 * (n + 1) - 1 - 6 = 6 * n - 1 by omega, h3 hn]

/-- **The Merkle steps** of one position against `stepsT`. -/
theorem exec_merkleOps (i j jr n h curR so : ℕ) (r : Array Val) (ok : Bool) (ops : List Op)
    (cur : Digest) (hj : jr < r.size) (hjv : (rd r jr).toN = j) (hc : curR < r.size)
    (hcv : rd r curR = .d cur) (tr : Trace) :
    exec impl κ inp (merkleOps i jr n h curR so r.size ++ ops) ⟨r, ok⟩ tr =
      (stepsT κ inp i j n h so cur tr).bind fun x =>
        exec impl κ inp ops ⟨r ++ x.1.toArray, ok && x.2.1⟩ x.2.2.2 := by
  induction n generalizing h curR so r ok cur tr with
  | zero => simp [merkleOps, stepsT]
  | succ n ih =>
    rw [show (⟨r, ok⟩ : St) = ⟨r ++ ([] : List Val).toArray, ok⟩ by simp]
    simp only [merkleOps, stepsT, List.append_assoc, List.cons_append, List.nil_append]
    rcases tr with _ | ⟨⟨q, a⟩, tr⟩
    · simp only [exec_app, evalOp, List.nil_append, stepT, Option.bind_none]
    have hsel : ∀ (c : Bool) (x y : Digest), (if c then Val.d x else Val.d y) = Val.d (if c then x else y) :=
      fun c x y => by cases c <;> rfl
    simp only [exec_app, evalOp, rd_app, rd_app0, rd_app_left _ _ hj, rd_app_left _ _ hc, hjv, hcv,
      List.getD_cons_succ, List.getD_cons_zero, List.nil_append, List.cons_append, Val.toBit, toD_d,
      hsel, stepT, nodeQF_eq]
    generalize bytesAt inp.π (absOff fSibs so) 32 = sib
    generalize hQ : (if decide (h < (lvl κ i).sib) = true then
      nodeQ i (if j.testBit h = true then sib else cur) (if j.testBit h = true then cur else sib)
      else nodeQ i zeroD zeroD) = Q
    by_cases hq : q = Q
    · simp only [hq, ite_true, Option.bind_some, Option.bind_map]
      rw [show r.size + 6 = (r ++ [Val.d sib, Val.bit (j.testBit h),
          Val.d (if j.testBit h = true then sib else cur), Val.d (if j.testBit h = true then cur else sib),
          Val.d a, Val.d (if decide (h < (lvl κ i).sib) = true then a else cur)].toArray).size by simp,
        ih _ _ _ _ _ _ (by simp; omega) (by rw [rd_app_left _ _ hj, hjv]) (by simp) (by rw [rd_app]; rfl)]
      refine Option.bind_congr fun y _ => ?_
      simp [Array.append_assoc, Bool.and_assoc, Val.isZero]
    · simp [hq]

theorem exec_merkleOps' (i j jr n h curR so b : ℕ) (r : Array Val) (ok : Bool) (ops : List Op)
    (cur : Digest) (hb : b = r.size) (hj : jr < r.size) (hjv : (rd r jr).toN = j) (hc : curR < r.size)
    (hcv : rd r curR = .d cur) (tr : Trace) :
    exec impl κ inp (merkleOps i jr n h curR so b ++ ops) ⟨r, ok⟩ tr =
      (stepsT κ inp i j n h so cur tr).bind fun x =>
        exec impl κ inp ops ⟨r ++ x.1.toArray, ok && x.2.1⟩ x.2.2.2 := by
  subst hb; exact exec_merkleOps impl κ inp i j jr n h curR so r ok ops cur hj hjv hc hcv tr

/-- A position's first four registers. -/
def posHeadVals (j : ℕ) (col : ByteArray) (a : Digest) (wv : Array K) : List Val :=
  [.n j, .b col, .d a, .k (dotKF wv col)]

@[simp] theorem posHeadVals_length (j : ℕ) (col : ByteArray) (a : Digest) (wv : Array K) :
    (posHeadVals j col a wv).length = 4 := rfl

theorem posHead_size (r : Array Val) (j : ℕ) (col : ByteArray) (a : Digest) (wv : Array K) :
    (r ++ (posHeadVals j col a wv).toArray).size = r.size + 4 := by simp [posHeadVals]

theorem posHead_rd0 (r : Array Val) (j : ℕ) (col : ByteArray) (a : Digest) (wv : Array K) :
    rd (r ++ (posHeadVals j col a wv).toArray) r.size = .n j := by
  rw [rd_app0]; simp [posHeadVals]

theorem posHead_rd2 (r : Array Val) (j : ℕ) (col : ByteArray) (a : Digest) (wv : Array K) :
    rd (r ++ (posHeadVals j col a wv).toArray) (r.size + 2) = .d a := by
  rw [rd_app]; simp [posHeadVals]

theorem exec_posMid (i j n so : ℕ) (r : Array Val) (col : ByteArray) (a : Digest) (wv : Array K)
    (ok : Bool) (ops : List Op) (tr : Trace) :
    exec impl κ inp (merkleOps i r.size n 0 (r.size + 2) so (r.size + 4) ++ ops)
      ⟨r ++ (posHeadVals j col a wv).toArray, ok⟩ tr =
      (stepsT κ inp i j n 0 so a tr).bind fun x =>
        exec impl κ inp ops ⟨r ++ (posHeadVals j col a wv).toArray ++ x.1.toArray, ok && x.2.1⟩
          x.2.2.2 :=
  exec_merkleOps' impl κ inp i j r.size n 0 (r.size + 2) so (r.size + 4) _ ok ops a
    (posHead_size r j col a wv).symm (by rw [posHead_size]; omega) (by rw [posHead_rd0]; rfl)
    (by rw [posHead_size]; omega) (posHead_rd2 r j col a wv) tr

/-- A position's first four ops: the index, the column, its query, the fold. -/
theorem exec_posHead (i co : ℕ) (ans : List Reg) (w p : ℕ) (r : Array Val) (ok : Bool) (rest : List Op)
    (ad : ℕ → Digest) (wv : Array K) (hA : ∀ k, ans.getD k 0 < r.size)
    (had : ∀ k, (rd r (ans.getD k 0)).toD = ad k) (hw : w < r.size) (hwv : (rd r w).toAK = wv)
    (q : ByteArray) (a : Digest) (tr : Trace) :
    exec impl κ inp ([.idx (fun κ => ans.getD (p / (lvl κ i).per) 0) (fun κ => (lvl κ i).logN)
        (fun κ => p % (lvl κ i).per),
      .piField fCols (co + p * colBytes i) (colBytes i),
      .askCol i (r.size + 1), .dotKF w (r.size + 1)] ++ rest) ⟨r, ok⟩ ((q, a) :: tr) =
      let j := idxOf (lvl κ i).logN (ad (p / (lvl κ i).per)) (p % (lvl κ i).per)
      let col := inp.π.extract (absOff fCols (co + p * colBytes i))
        (absOff fCols (co + p * colBytes i) + colBytes i)
      if q = colQ i col then
        exec impl κ inp rest ⟨r ++ (posHeadVals j col a wv).toArray, ok⟩ tr
      else none := by
  rw [show (⟨r, ok⟩ : St) = ⟨r ++ ([] : List Val).toArray, ok⟩ by simp]
  simp only [List.cons_append, List.nil_append, exec_app, evalOp, rd_app_left _ _ (hA _), had,
    rd_app_left _ _ hw, hwv, rd_app, rd_app0, List.getD_cons_succ, List.getD_cons_zero, Val.toB,
    Bool.and_true, posHeadVals, dotKFF_eq, idxOfF_eq]

/-- A position's last three ops: the cap index, the cap entry, the comparison. -/
theorem exec_posTail (i jr curR e : ℕ) (R : Array Val) (ok : Bool) (ops : List Op) (j : ℕ)
    (cur : Digest) (he : e = R.size) (hjr : jr < R.size) (hj : rd R jr = .n j) (hcr : curR < R.size)
    (hc : rd R curR = .d cur) (tr : Trace) :
    exec impl κ inp ([.shrN jr (fun κ => (lvl κ i).sib), .piDigestAt fCaps (capOff i) e,
        .assertEq curR (e + 1) allK] ++ ops) ⟨R, ok⟩ tr =
      exec impl κ inp ops ⟨R ++ [Val.n (j >>> (lvl κ i).sib),
        .d (bytesAt inp.π (absOff fCaps (capOff i) + 32 * (j >>> (lvl κ i).sib)) 32)].toArray,
        ok && decide (cur = bytesAt inp.π (absOff fCaps (capOff i) + 32 * (j >>> (lvl κ i).sib)) 32)⟩ tr := by
  subst he
  rw [show (⟨R, ok⟩ : St) = ⟨R ++ ([] : List Val).toArray, ok⟩ by simp]
  simp only [List.cons_append, List.nil_append, exec_app, evalOp, rd_app_left _ _ hjr, hj,
    rd_app_left _ _ hcr, hc, rd_app, rd_app0, List.getD_cons_succ, List.getD_cons_zero, Val.toN,
    Val.eqv, allK, Bool.not_true, Bool.false_or, Bool.and_true, digestAt_eq]

/-- **One position** of level `i` against `posT` (`ad`, `wv`: the values of the answer and weight
registers). -/
theorem exec_posOps (i co so : ℕ) (ans : List Reg) (w p : ℕ) (r : Array Val) (ok : Bool) (ops : List Op)
    (ad : ℕ → Digest) (wv : Array K) (hA : ∀ k, ans.getD k 0 < r.size)
    (had : ∀ k, (rd r (ans.getD k 0)).toD = ad k) (hw : w < r.size) (hwv : (rd r w).toAK = wv)
    (tr : Trace) :
    exec impl κ inp (posOps i co so ans w p r.size ++ ops) ⟨r, ok⟩ tr =
      (posT κ inp i co so ad wv p tr).bind fun x =>
        exec impl κ inp ops ⟨r ++ x.1.toArray, ok && x.2.1⟩ x.2.2 := by
  simp only [posOps, List.append_assoc]
  rcases tr with _ | ⟨⟨q, a⟩, tr⟩
  · rw [show (⟨r, ok⟩ : St) = ⟨r ++ ([] : List Val).toArray, ok⟩ by simp]
    simp only [List.cons_append, List.nil_append, exec_app, evalOp, posT, Option.bind_none]
  rw [exec_posHead impl κ inp i co ans w p r ok _ ad wv hA had hw hwv]
  simp only [posT]
  generalize idxOf (lvl κ i).logN (ad (p / (lvl κ i).per)) (p % (lvl κ i).per) = j
  generalize inp.π.extract (absOff fCols (co + p * colBytes i))
    (absOff fCols (co + p * colBytes i) + colBytes i) = col
  by_cases hq : q = colQ i col
  swap; · simp [hq]
  simp only [hq, ite_true]
  rw [exec_posMid, Option.bind_map]
  refine Option.bind_congr fun x hx => ?_
  obtain ⟨hl, h0, hlast⟩ := stepsT_spec κ inp hx
  generalize hsb : (lvlStar i).sib = sb at *
  have hs4 : (r ++ (posHeadVals j col a wv).toArray).size = r.size + 4 := posHead_size r j col a wv
  rw [exec_posTail impl κ inp i (jr := r.size)
    (curR := if sb = 0 then r.size + 2 else r.size + 4 + 6 * sb - 1) (e := r.size + 4 + 6 * sb)
    (j := j) (cur := x.2.2.1) (he := by simp [hl]; omega)
    (hjr := by simp)
    (hj := by rw [rd_append_left (by rw [posHead_size]; omega), posHead_rd0])
    (hcr := by split_ifs <;> simp [hl] <;> omega) (hc := ?_)]
  · simp [Array.append_assoc, Bool.and_assoc, hsb, posHeadVals]
  · split_ifs with hs
    · rw [rd_append_left (by rw [posHead_size]; omega), posHead_rd2, h0 hs]
    · rw [show r.size + 4 + 6 * sb - 1 = (r ++ (posHeadVals j col a wv).toArray).size
          + (6 * sb - 1) by rw [hs4]; omega, rd_app, hlast (by omega)]

theorem posT_length {i co so p : ℕ} {ad : ℕ → Digest} {w : Array K} {tr : Trace}
    {x : List Val × Bool × Trace} (hx : posT κ inp i co so ad w p tr = some x) :
    x.1.length = posW i := by
  rcases tr with _ | ⟨⟨q, a⟩, tr⟩
  · cases hx
  simp only [posT] at hx
  split_ifs at hx
  obtain ⟨y, hy, rfl⟩ := Option.map_eq_some_iff.1 hx
  simp [(stepsT_spec κ inp hy).1, posW]; omega

/-- **The positions of a level**, from position `p` on, against `posAllT`. -/
theorem exec_posAll (i co so : ℕ) (ans : List Reg) (w b : ℕ) (ad : ℕ → Digest) (wv : Array K)
    (t : ℕ) : ∀ (p : ℕ) (r : Array Val) (ok : Bool) (ops : List Op) (tr : Trace),
    r.size = b + 2 + posW i * p → (∀ k, ans.getD k 0 < r.size) →
    (∀ k, (rd r (ans.getD k 0)).toD = ad k) → w < r.size → (rd r w).toAK = wv →
    exec impl κ inp (((List.range' p t).flatMap fun p => posOps i co so ans w p (b + 2 + posW i * p))
        ++ ops) ⟨r, ok⟩ tr =
      (posAllT κ inp i co so ad wv t p tr).bind fun x =>
        exec impl κ inp ops ⟨r ++ x.1.toArray, ok && x.2.1⟩ x.2.2 := by
  induction t with
  | zero => intro p r ok ops tr _ _ _ _ _; simp [posAllT]
  | succ t ih =>
    intro p r ok ops tr hs hA had hw hwv
    have h := exec_posOps impl κ inp i co so ans w p r ok
      (((List.range' (p + 1) t).flatMap fun p => posOps i co so ans w p (b + 2 + posW i * p)) ++ ops)
      ad wv hA had hw hwv tr
    rw [hs] at h
    rw [List.range'_succ, List.flatMap_cons, List.append_assoc, h]
    simp only [posAllT, Option.bind_assoc, Option.bind_map]
    refine Option.bind_congr fun x hx => ?_
    have hl := posT_length κ inp hx
    rw [ih (p + 1) (r ++ x.1.toArray) _ ops x.2.2 (by simp [hl, hs, Nat.mul_succ]; omega)
      (fun k => by simp; exact Nat.lt_add_right _ (hA k))
      (fun k => by rw [rd_append_left (hA k), had]) (by simp; exact Nat.lt_add_right _ hw)
      (by rw [rd_append_left hw, hwv])]
    simp [Function.comp_def, Array.append_assoc, Bool.and_assoc]

/-- The seed's registers and flag (`seedOps`). -/
def seedT (tr : Trace) : Option (List Val × Bool × Trace) :=
  match tr with
  | (q, a) :: tr =>
    let hdr := inp.π.extract (absOff fHdr 0) (absOff fHdr 0 + 48)
    if q = seedQ inp.vk inp.c hdr then
      let b := inp.π.data.getD 0 0
      let s := [b == Kind.L32.byte, b == Kind.P30.byte, b == Kind.N30.byte]
      let e := F.ofBytes (bytesAt inp.π (absOff fHdr 0) 16)
      let k := F.ofBytes (bytesAt (bytesOf (hdrBytes κ zeroD)) 0 16)
      some ([.b hdr, .d a] ++ s.map .bit ++ [.f e, .f k], s.count true == 1 && decide (e = k), tr)
    else none
  | [] => none

/-- **Reference semantics of a phase** (number `n`, context `c`, registers `r`). -/
def refPhase (n : ℕ) (p : Phase) (c : GCtx) (r : Array Val) (tr : Trace) :
    Option (List Val × Bool × Trace) :=
  let d := (rd r c.st).toD
  let o := phaseOff n
  match p.shape with
  | .seed => seedT κ inp tr
  | .absorb f len =>
    (ans1 (absorbQ d (msgAt inp f (o f) len)) tr).map fun x =>
      let m := msgAt inp f (o f) len
      let base := [Val.b m, .d x.1]
      if f = fStmt then
        let s0 := msgAt inp fStmt 0 1; let s1 := msgAt inp fStmt 33 8
        let s2 := msgAt inp fStmt 41 87; let s3 := msgAt inp fStmt 65 63
        let tag := bytesOf [if κ.isNode then RecursionFast.tagNode else tagLeaf]
        let nb := bytesOf (enc64 (leafN κ))
        let pub := bytesAt inp.π (absOff fHdr 16) 32
        (base ++ [.d (stmtDigest κ m), .d inp.c, .b s0, .b tag, .b s1, .b nb, .b s2, .b s3, .d pub,
            .d inp.vk],
          decide (stmtDigest κ m = inp.c) && decide (s0.data = tag.data) &&
            (κ.isNode || decide (s1.data = nb.data)) && (κ.isNode || (Val.b s2).isZero) &&
            (!κ.isNode || (Val.b s3).isZero) && (!κ.isNode || decide (pub = inp.vk)), x.2)
      else if f = fFinal then
        let z := msgAt inp fFinal (2 ^ 5 * 32) ((finalElems - 2 ^ 5) * 32)
        (base ++ [.b z], decide (κ = .L32) || (Val.b z).isZero, x.2)
      else if f = fLrEnd ∨ f = fEEnd then (base, κ.isNode || (Val.b m).isZero, x.2)
      else (base, true, x.2)
  | .squeezes k ch =>
    (sqzT k d tr).map fun x =>
      match ch with
      | .coords _ => (x.1.flatMap coordVals ++ [.af (coordsOf x.1).toArray], true, x.2)
      | .one _ => (x.1.map .d ++ [.f (chF (x.1.headD zeroD) 0)], true, x.2)
      | .pos _ => (x.1.map .d, true, x.2)
  | .uni f =>
    match tr with
    | (q₁, a₁) :: (q₂, a₂) :: tr =>
      if q₁ = absorbQ d (msgAt inp f (o f) uniBytes) ∧ q₂ = squeezeQ a₁ then
        some (uniVals impl inp f (o f) (impl.targetS κ (rd r c.pt).toAF) a₁ a₂,
          (Val.b (msgAt inp f (o f + 2032) 16)).isZero, tr)
      else none
    | _ => none
  | .rounds f k deg inK real =>
    let init := initClaim p.name
    let iv := initVals inp init f (o f) inK
    let cl := match init with | .uni => rd r c.uni | _ => iv.getLastD default
    (roundsT inp f (o f) deg inK (real κ) k 0 d cl tr).map fun x => (iv ++ x.1, x.2.1, x.2.2)
  | .queries i =>
    let fr := c.foldR.map fun x => (rd r x).toK
    let w := eqTab fr.toArray
    let ad := fun k => (rd r (c.posAns.getD k 0)).toD
    (posAllT κ inp i (o fCols) (o fSibs) ad w (lvlStar i).t 0 tr).map fun x =>
      ([.ak fr.toArray, .ak w] ++ x.1, x.2.1, x.2.2)

theorem seedT_length {tr : Trace} {x : List Val × Bool × Trace} (hx : seedT κ inp tr = some x) :
    x.1.length = 7 := by
  rcases tr with _ | ⟨⟨q, a⟩, tr⟩
  · cases hx
  simp only [seedT] at hx
  split_ifs at hx
  cases hx; simp

theorem roundsT_length {f o deg real n j : ℕ} {inK : Bool} {d : Digest} {c : Val} {tr : Trace}
    {x : List Val × Bool × Trace} (hx : roundsT inp f o deg inK real n j d c tr = some x) :
    x.1.length = (if inK then 13 else roundW deg) * n := by
  induction n generalizing j d c tr x with
  | zero => simp [roundsT] at hx; subst hx; simp
  | succ n ih =>
    rcases tr with _ | ⟨⟨q₁, a₁⟩, _ | ⟨⟨q₂, a₂⟩, tr⟩⟩
    · cases hx
    · cases hx
    simp only [roundsT] at hx
    split_ifs at hx <;>
    · obtain ⟨y, hy, rfl⟩ := Option.map_eq_some_iff.1 hx
      rw [List.length_append, ih hy]
      cases inK <;> simp_all [roundKVals, round3V, round2Vals, roundW, Nat.mul_succ] <;> omega

theorem posAllT_length {i co so t p : ℕ} {ad : ℕ → Digest} {w : Array K} {tr : Trace}
    {x : List Val × Bool × Trace} (hx : posAllT κ inp i co so ad w t p tr = some x) :
    x.1.length = posW i * t := by
  induction t generalizing p tr x with
  | zero => simp [posAllT] at hx; subst hx; simp
  | succ t ih =>
    simp only [posAllT, Option.bind_eq_some_iff, Option.map_eq_some_iff] at hx
    obtain ⟨y, hy, z, hz, rfl⟩ := hx
    simp only [List.length_append, posT_length κ inp hy, ih hz, Nat.mul_succ]; omega

theorem coordVals_length (as : List Digest) : (as.flatMap coordVals).length = 3 * as.length := by
  induction as with
  | nil => rfl
  | cons a as ih => simp [coordVals, ih]; omega

theorem initVals_length (init : Init) (f o : ℕ) (inK : Bool) :
    (initVals inp init f o inK).length = init.width := by
  cases init <;> cases inK <;> rfl

theorem uniVals_length (f o : ℕ) (pe : Array F) (a₁ a₂ : Digest) :
    (uniVals impl inp f o pe a₁ a₂).length = 136 := by
  simp [uniVals, uniEs]

/-- The registers a context points to are below the register file's size. -/
def CtxOk (c : GCtx) (r : Array Val) : Prop :=
  c.st < r.size ∧ c.uni < r.size ∧ (∀ x ∈ c.posAns, x < r.size) ∧ (∀ x ∈ c.foldR, x < r.size) ∧
    c.pt < r.size

theorem CtxOk.mono {c : GCtx} {r : Array Val} {m : ℕ} (h : CtxOk c r) (hm : r.size ≤ m) :
    c.st < m ∧ c.uni < m ∧ (∀ x ∈ c.posAns, x < m) ∧ (∀ x ∈ c.foldR, x < m) ∧ c.pt < m :=
  let ⟨h1, h2, h3, h4, h5⟩ := h
  ⟨Nat.lt_of_lt_of_le h1 hm, Nat.lt_of_lt_of_le h2 hm, fun x hx => Nat.lt_of_lt_of_le (h3 x hx) hm,
    fun x hx => Nat.lt_of_lt_of_le (h4 x hx) hm, Nat.lt_of_lt_of_le h5 hm⟩

/-- **Every phase's semantics**: a phase's ops on a trace are its
reference `refPhase`, for every phase of the table, kind and context. Phase Z is the proved
instance `exec_phaseZ` (Z1 `.coords`, Z2 `.uni`, Z3 `.rounds … 3`, Zend `.absorb`). -/
theorem exec_genPhase (n : ℕ) (p : Phase) (c : GCtx) (r : Array Val) (ok : Bool) (ops : List Op)
    (hb : c.next = r.size)
    (hwf : (p.shape = .seed ∧ CtxOk c #[default]) ∨ CtxOk c r) (tr : Trace) :
    exec impl κ inp ((genPhase n p c).1 ++ ops) ⟨r, ok⟩ tr =
      (refPhase impl κ inp n p c r tr).bind fun x =>
        exec impl κ inp ops ⟨r ++ x.1.toArray, ok && x.2.1⟩ x.2.2 := by
  obtain ⟨name, sh⟩ := p
  obtain ⟨b, st, u, pa, fr, pt, outs⟩ := c
  simp only at hb hwf; subst hb
  have e0 : ∀ ok', (⟨r, ok'⟩ : St) = ⟨r ++ ([] : List Val).toArray, ok'⟩ := fun _ => by simp
  cases sh with
  | seed =>
    simp only [genPhase, refPhase, seedOps, List.cons_append, List.nil_append]
    rw [e0]
    rcases tr with _ | ⟨⟨q, a⟩, tr⟩
    · simp only [exec_app, evalOp, List.nil_append, seedT, Option.bind_none]
    · simp only [exec_app, evalOp, seedT, rd_app, rd_app0, List.getD_cons_succ, List.getD_cons_zero,
        List.nil_append, List.cons_append, Val.toB, byteAt_eq]
      by_cases h : q = seedQ inp.vk inp.c (inp.π.extract (absOff fHdr 0) (absOff fHdr 0 + 48)) <;>
        simp [h, allK, Val.eqv, Val.toBit, Bool.and_assoc]
  | absorb f len =>
    have hst := (hwf.resolve_left (by simp)).1
    simp only [genPhase, refPhase]
    rcases tr with _ | ⟨⟨q, a⟩, tr⟩ <;> split_ifs <;> rw [e0] <;>
      simp only [absorbOps, stmtOps, finalOps, exec_app, evalOp, List.cons_append, List.nil_append,
        rd_app, rd_app0, rd_app2, rd_app_left _ _ hst, List.getD_cons_succ, List.getD_cons_zero, ans1,
        Nat.reduceAdd, msgAt, Option.map_none, Option.bind_none, Val.toB]
    all_goals (try (by_cases hq : q = absorbQ (rd r st).toD (inp.π.extract (absOff f (phaseOff n f)) (absOff f (phaseOff n f) + len))))
    all_goals simp_all [Val.eqv, Val.toB, Val.toD, allK, Bool.and_assoc]
  | squeezes k ch =>
    have hst := (hwf.resolve_left (by simp)).1
    cases ch with
    | coords _ =>
      simp only [genPhase, refPhase, List.append_assoc]
      rw [exec_sqzC impl κ inp k st r ok _ hst, Option.bind_map]
      refine Option.bind_congr fun x hx => ?_
      rw [show 2 * k = 2 * x.1.length by rw [sqzT_spec hx]]
      simp only [Function.comp_apply, List.singleton_append, exec_app, evalOp, pack_coords,
        Bool.and_true, List.nil_append]
    | one _ =>
      simp only [genPhase, refPhase, List.append_assoc]
      rw [exec_sqzOps impl κ inp k st r ok _ hst, Option.bind_map]
      refine Option.bind_congr fun x _ => ?_
      have h0 : ((x.1.map Val.d).getD 0 default).toD = x.1.headD zeroD := by
        cases x.1 <;> rfl
      simp only [Function.comp_apply, List.singleton_append, exec_app, evalOp, rd_app0, h0,
        Bool.and_true]
    | pos _ =>
      simp only [genPhase, refPhase]
      rw [exec_sqzOps impl κ inp k st r ok _ hst, Option.bind_map]
      simp
  | uni f =>
    obtain ⟨hst, -, -, -, hpt⟩ := hwf.resolve_left (by simp)
    replace hst : st < r.size := hst
    replace hpt : pt < r.size := hpt
    simp only [genPhase, refPhase]
    rcases tr with _ | ⟨⟨q₁, a₁⟩, _ | ⟨⟨q₂, a₂⟩, tr⟩⟩
    · rw [e0]; simp only [uniOps, uniHead, List.append_assoc, List.cons_append, exec_app, evalOp,
        List.nil_append, Option.bind_none]
    · rw [e0]; simp only [uniOps, uniHead, List.append_assoc, List.cons_append, exec_app, evalOp,
        List.nil_append, Option.bind_none]; split <;> simp
    · rw [exec_uni impl κ inp f _ st pt r ok ops _ hst hpt rfl]
      by_cases h : q₁ = absorbQ (rd r st).toD (msgAt inp f (phaseOff n f) uniBytes) ∧
        q₂ = squeezeQ a₁ <;> simp [h]
  | rounds f k deg inK real =>
    obtain ⟨hst, hu, -, -, -⟩ := hwf.resolve_left (by simp)
    replace hst : st < r.size := hst
    replace hu : u < r.size := hu
    simp only [genPhase, refPhase]
    rcases hi : initClaim name with _ | _ | _ <;>
      simp only [initOps, initVals, Init.width, List.nil_append, Nat.add_zero]
    · rw [exec_roundsT impl κ inp f _ deg inK real k 0 st u r ok ops _ _ hst hu rfl rfl, Option.bind_map]
      simp
    · rw [e0]
      simp only [List.singleton_append, List.cons_append, exec_app, evalOp, List.nil_append]
      rw [exec_roundsT' impl κ inp f _ deg inK real k 0 st r.size _ (r ++ [Val.f 0].toArray) _ ops _
        (.f 0) (by simp) (by simp; exact Nat.le_of_lt hst) (by simp) (by rw [rd_app_left _ _ hst])
        (by simpa using rd_app0 r [Val.f 0]), Option.bind_map]
      simp [Array.append_assoc]
    · rw [e0]
      cases inK <;>
      simp only [Bool.false_eq_true, ite_true, ite_false, List.cons_append, List.nil_append, exec_app,
        evalOp, rd_app, rd_app0, List.getD_cons_succ, List.getD_cons_zero, toF_f, toK_k] <;>
      rw [exec_roundsT' impl κ inp f _ deg _ real k 0 st (r.size + 2) _ _ _ ops (rd r st).toD _ ?_ ?_ ?_ ?_
          rfl,
        Option.bind_map] <;>
      first
        | (simp [Array.append_assoc, rd_app, List.getD_cons_succ, List.getD_cons_zero, elemAt,
            elemKAt]; done)
        | exact Nat.lt_of_lt_of_le hst (by simp)
        | (simp; done)
        | rw [rd_app_left _ _ hst]
  | queries i =>
    obtain ⟨hst, -, hpa, -, -⟩ := hwf.resolve_left (by simp)
    replace hst : st < r.size := hst
    replace hpa : ∀ x ∈ pa, x < r.size := hpa
    have hA : ∀ k, pa.getD k 0 < r.size := fun k => by
      rw [List.getD_eq_getElem?_getD]
      cases h : pa[k]? with
      | none => exact Nat.lt_of_le_of_lt (Nat.zero_le _) hst
      | some x => simpa using hpa x (List.mem_of_getElem? h)
    simp only [genPhase, refPhase]
    rw [e0]
    simp only [List.cons_append, List.nil_append, exec_app, evalOp]
    simp only [Array.append_empty, rd_app0, List.getD_cons_zero, List.range_eq_range', Val.toAK]
    generalize hX : (fr.map fun x => (rd r x).toK).toArray = X
    rw [exec_posAll impl κ inp i _ _ pa (r.size + 1) r.size (fun k => (rd r (pa.getD k 0)).toD)
      (eqTab X) _ 0 (r ++ #[Val.ak X, Val.ak (eqTab X)]) _ ops tr (by simp)
      (fun k => Nat.lt_of_lt_of_le (hA k) (by simp)) (fun k => by rw [rd_app_left _ _ (hA k)])
      (by simp) (by rw [rd_app _ _ 1]; rfl), Option.bind_map]
    simp [Function.comp_def, Array.append_assoc]

/-- **The context a phase hands on** (S-0-M3): the next free register is
past the phase's registers, the next context's registers point into them, and the phase's outputs
are pushed. -/
theorem genPhase_ctx (n : ℕ) (p : Phase) (c : GCtx) (r : Array Val) (tr : Trace)
    (x : List Val × Bool × Trace) (hb : c.next = r.size)
    (hwf : (p.shape = .seed ∧ CtxOk c #[default]) ∨ CtxOk c r)
    (hx : refPhase impl κ inp n p c r tr = some x) :
    (genPhase n p c).2.next = (r ++ x.1.toArray).size ∧
      CtxOk (genPhase n p c).2 (r ++ x.1.toArray) ∧
      (genPhase n p c).2.outs.size = c.outs.size + 1 := by
  obtain ⟨name, sh⟩ := p
  obtain ⟨b, st, u, pa, fr, pt, outs⟩ := c
  simp only at hb hwf; subst hb
  have hm : ∀ m, r.size ≤ m → 1 ≤ m →
      st < m ∧ u < m ∧ (∀ x ∈ pa, x < m) ∧ (∀ x ∈ fr, x < m) ∧ pt < m := fun m h1 h2 => by
    rcases hwf with ⟨-, h⟩ | h
    · exact h.mono (by simpa using h2)
    · exact h.mono h1
  have hm4 : ∀ m, r.size ≤ m → 1 ≤ m →
      u < m ∧ (∀ x ∈ pa, x < m) ∧ (∀ x ∈ fr, x < m) ∧ pt < m := fun m h1 h2 => (hm m h1 h2).2
  have hpos : sh ≠ .seed → 0 < r.size := fun h => by
    rcases hwf with ⟨h', -⟩ | h
    · exact absurd h' h
    · exact Nat.lt_of_le_of_lt (Nat.zero_le _) h.1
  cases sh with
  | seed =>
    simp only [refPhase] at hx
    have hl := seedT_length κ inp hx
    obtain ⟨-, h2, h3, h4, h5⟩ := hm (r.size + 7) (by omega) (by omega)
    simp only [genPhase, CtxOk, Array.size_append, List.size_toArray, hl, Array.size_push]
    refine ⟨trivial, ⟨?_, h2, h3, h4, h5⟩, trivial⟩
    dsimp only [Reg]; omega
  | absorb f len =>
    simp only [refPhase] at hx
    obtain ⟨y, -, rfl⟩ := Option.map_eq_some_iff.1 hx
    have hp := hpos (by simp)
    simp only [genPhase]
    split_ifs <;> simp [CtxOk]
    all_goals repeat' apply And.intro
    all_goals try dsimp only [Reg] at *
    all_goals first
      | trivial | omega
      | exact (hm _ (by omega) (by omega)).1
      | exact (hm4 _ (by omega) (by omega)).1 | exact (hm4 _ (by omega) (by omega)).2.1
      | exact (hm4 _ (by omega) (by omega)).2.2.1 | exact (hm4 _ (by omega) (by omega)).2.2.2
      | (intro a ha; simp at ha; omega)
  | squeezes k ch =>
    simp only [refPhase] at hx
    obtain ⟨y, hy, rfl⟩ := Option.map_eq_some_iff.1 hx
    have hk := sqzT_spec hy
    have hc := coordVals_length y.1
    simp only [List.length_flatMap] at hc
    have hp := hpos (by simp)
    cases ch <;> simp [genPhase, CtxOk, hc, hk]
    all_goals repeat' apply And.intro
    all_goals try dsimp only [Reg] at *
    all_goals first
      | trivial | omega
      | exact (hm _ (by omega) (by omega)).1
      | exact (hm4 _ (by omega) (by omega)).1 | exact (hm4 _ (by omega) (by omega)).2.1
      | exact (hm4 _ (by omega) (by omega)).2.2.1 | exact (hm4 _ (by omega) (by omega)).2.2.2
      | (intro a ha; simp at ha; omega)
  | uni f =>
    simp only [refPhase] at hx
    have hp := hpos (by simp)
    rcases tr with _ | ⟨⟨q₁, a₁⟩, _ | ⟨⟨q₂, a₂⟩, tr⟩⟩
    · cases hx
    · cases hx
    simp only at hx
    split_ifs at hx
    cases hx
    simp [genPhase, CtxOk, uniVals_length]
    all_goals repeat' apply And.intro
    all_goals try dsimp only [Reg] at *
    all_goals first
      | trivial | omega
      | exact (hm _ (by omega) (by omega)).1
      | exact (hm4 _ (by omega) (by omega)).1 | exact (hm4 _ (by omega) (by omega)).2.1
      | exact (hm4 _ (by omega) (by omega)).2.2.1 | exact (hm4 _ (by omega) (by omega)).2.2.2
      | (intro a ha; simp at ha; omega)
  | rounds f k deg inK real =>
    simp only [refPhase] at hx
    obtain ⟨y, hy, rfl⟩ := Option.map_eq_some_iff.1 hx
    have hk := roundsT_length inp hy
    have hp := hpos (by simp)
    have hw : 13 ≤ roundW deg := by unfold roundW; split <;> omega
    have hwk : 0 < k → roundW deg ≤ roundW deg * k := Nat.le_mul_of_pos_right _
    have hst : st < r.size := (hm r.size le_rfl hp).1
    simp only [genPhase]
    rcases initClaim name with _ | _ | _ <;> cases inK <;>
      simp [initOps, initVals_length, hk, CtxOk, Init.width]
    all_goals repeat' apply And.intro
    all_goals try dsimp only [Reg] at *
    all_goals first
      | trivial | omega
      | (split_ifs with hk0 <;> first | omega | (have := hwk (by omega); omega))
      | exact (hm _ (by omega) (by omega)).1
      | exact (hm4 _ (by omega) (by omega)).1 | exact (hm4 _ (by omega) (by omega)).2.1
      | exact (hm4 _ (by omega) (by omega)).2.2.1 | exact (hm4 _ (by omega) (by omega)).2.2.2
      | (intro a ha; simp at ha; omega)
  | queries i =>
    simp only [refPhase] at hx
    obtain ⟨y, hy, rfl⟩ := Option.map_eq_some_iff.1 hx
    have hk := posAllT_length κ inp hy
    have hp := hpos (by simp)
    simp [genPhase, CtxOk, hk]
    all_goals repeat' apply And.intro
    all_goals try dsimp only [Reg] at *
    all_goals first
      | trivial | omega
      | exact (hm _ (by omega) (by omega)).1
      | exact (hm4 _ (by omega) (by omega)).1 | exact (hm4 _ (by omega) (by omega)).2.1
      | exact (hm4 _ (by omega) (by omega)).2.2.1 | exact (hm4 _ (by omega) (by omega)).2.2.2
      | (intro a ha; simp at ha; omega)

/-- **Reference semantics of a run of phases**: the registers, each phase's flag, the rest. -/
def refPhases : List Phase → ℕ → GCtx → Array Val → Trace → Option (List Val × List Bool × Trace)
  | [], _, _, _, tr => some ([], [], tr)
  | p :: ps, n, c, r, tr =>
    (refPhase impl κ inp n p c r tr).bind fun x =>
      (refPhases ps (n + 1) (genPhase n p c).2 (r ++ x.1.toArray) x.2.2).map fun y =>
        (x.1 ++ y.1, x.2.1 :: y.2.1, y.2.2)

/-- A run of phases may start: the first is the seed, or the context is well formed. -/
def StartOk (ps : List Phase) (c : GCtx) (r : Array Val) : Prop :=
  CtxOk c r ∨ ∃ p ps', ps = p :: ps' ∧ p.shape = .seed ∧ CtxOk c #[default]

/-- **`exec_genPhases`** (S-0-M3): a run of phases on a trace is `refPhases`; the flag is the
conjunction of the phases' flags. -/
theorem exec_genPhases (ps : List Phase) (n : ℕ) (c : GCtx) (r : Array Val) (ok : Bool)
    (ops : List Op) (hb : c.next = r.size) (hs : StartOk ps c r) (tr : Trace) :
    exec impl κ inp ((genPhases ps n c).1 ++ ops) ⟨r, ok⟩ tr =
      (refPhases impl κ inp ps n c r tr).bind fun y =>
        exec impl κ inp ops ⟨r ++ y.1.toArray, ok && y.2.1.all id⟩ y.2.2 := by
  induction ps generalizing n c r ok tr with
  | nil => simp [genPhases, refPhases]
  | cons p ps ih =>
    have hwf : (p.shape = .seed ∧ CtxOk c #[default]) ∨ CtxOk c r := by
      rcases hs with h | ⟨q, qs, he, hq, h0⟩
      · exact .inr h
      · cases he; exact .inl ⟨hq, h0⟩
    simp only [genPhases, List.append_assoc]
    rw [exec_genPhase impl κ inp n p c r ok _ hb hwf, refPhases, Option.bind_assoc]
    refine Option.bind_congr fun x hx => ?_
    obtain ⟨h1, h2, -⟩ := genPhase_ctx impl κ inp n p c r tr x hb hwf hx
    rw [ih (n + 1) _ _ _ h1 (.inl h2), Option.bind_map]
    refine Option.bind_congr fun y _ => ?_
    simp [Array.append_assoc, Bool.and_assoc, List.all_cons]

/-- The initial context. -/
def ctx₀ : GCtx := ⟨0, 0, 0, [], [], 0, #[]⟩

/-- **`exec_skeleton`** (S-0-M3): the whole skeleton on a trace is `refPhases phases`. -/
theorem exec_skeleton (ok : Bool) (ops : List Op) (tr : Trace) :
    exec impl κ inp (skeleton.1 ++ ops) ⟨#[], ok⟩ tr =
      (refPhases impl κ inp phases 0 ctx₀ #[] tr).bind fun y =>
        exec impl κ inp ops ⟨#[] ++ y.1.toArray, ok && y.2.1.all id⟩ y.2.2 :=
  exec_genPhases impl κ inp phases 0 ctx₀ #[] ok ops rfl (.inr ⟨_, _, rfl, rfl, by simp [CtxOk, ctx₀]⟩) tr

/-- **Every phase's flag** (S-0-M3): an accepted skeleton has every phase's check passing. -/
theorem skeleton_ok {y : List Val × List Bool × Trace} (h : y.2.1.all id = true) :
    ∀ b ∈ y.2.1, b = true := by
  simpa using h

/-! ## Controls (a toy program: the input `vk`, one squeeze, one assertion) -/

/-- A toy program: `r0 := vk`, `r1 := H(squeeze r0)`, assert `r0 = r1` or `r0 = r0`. -/
def toyProg (bad : Bool) : VProg :=
  ⟨.fixed .L32, [.input 0, .askSqueeze 0, .assertEq 0 (if bad then 1 else 0) allK, .accept]⟩

def toyIn : Input := ⟨zeroD, zeroD, ByteArray.empty⟩

/-- Positive: on its own query, the toy program accepts. -/
theorem toy_accept (impl : OpImpl) (a : Digest) :
    semIR impl (toyProg false) toyIn [(squeezeQ zeroD, a)] = some true := by
  simp [semIR, toyProg, VProg.kindOn, exec, evalOp, St.init, rd, toyIn, Val.toD, Val.eqv, allK]

/-- Negative: a trace whose query is not the program's is rejected (`runSeq`'s mismatch). -/
theorem toy_wrong_query (impl : OpImpl) (a : Digest) :
    semIR impl (toyProg false) toyIn [(squeezeQ a, a)] = if a = zeroD then some true else none := by
  by_cases h : a = zeroD
  · subst h; simp [semIR, toyProg, VProg.kindOn, exec, evalOp, St.init, rd, toyIn, Val.toD,
      Val.eqv, allK]
  · have : squeezeQ a ≠ squeezeQ zeroD := by
      intro e; apply h; have := congrArg (fun q : ByteArray => q.data.toList.drop 8) e
      exact Vector.toList_inj.1 (by simpa [squeezeQ, bytesOf, tagSqz] using this)
    simp [semIR, toyProg, VProg.kindOn, exec, evalOp, St.init, rd, toyIn, Val.toD, this, h]

/-- Negative: a failed assertion makes the flag `false` (the run still uses the whole trace). -/
theorem toy_reject (impl : OpImpl) (a : Digest) (ha : a ≠ zeroD) :
    semIR impl (toyProg true) toyIn [(squeezeQ zeroD, a)] = some false := by
  simp [semIR, toyProg, VProg.kindOn, exec, evalOp, St.init, rd, toyIn, Val.toD, Val.eqv, allK,
    Ne.symm ha]

/-- Negative: a trace with an entry left over is rejected (`runSeq` uses the trace up exactly). -/
theorem toy_extra (impl : OpImpl) (a : Digest) (e : ByteArray × Digest) :
    semIR impl (toyProg false) toyIn [(squeezeQ zeroD, a), e] = none := by
  simp [semIR, toyProg, VProg.kindOn, exec, evalOp, St.init, rd, toyIn, Val.toD, Val.eqv, allK]

end FR
