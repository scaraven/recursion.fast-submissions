-- New for `flock-recursive` (BLUEPRINT §10 changes 27 (B) step 4; stage RET-3): the declarations of
-- the 3.x verifier-shape modules that the revision 4 certificate reads, moved here verbatim (same
-- names, statements and proofs) from `FRVerifier` (1), `FRVIRSpec` (69), `FRVIRChain` (22).
-- Content: the IR semantics revision 4 reads: `FRVIRSpec`'s generic run lemmas (`exec_append`,
-- `exec_app`, `runSeq_runIR`, …) and shape lemmas, `FRVIRChain`'s reference chain (`ChainOK`,
-- `qOf`, …). The 3.x modules import this one.
import FRVIR
import RecursionFast.Library.WitnessSending

/-! ## From `FRVerifier` (1 declaration) -/

section

namespace FR

open RecursionFast

open RecursionFast.WitnessSending (encode decode decode_encode decodeF encodeF decodeF_eq encodeF_eq
  size_child_lt)

/-- A witness-sending proof's first byte is its tag word's: `0` or `1`. -/
theorem encode_byte0 (w : Wit) : (encode w).data[0]? = some 0 ∨ (encode w).data[0]? = some 1 := by
  cases w <;> simp [encode, witWords, wordsBytes, wordBytes, enc64, toWord]

end FR

end

/-! ## From `FRVIRSpec` (69 declarations) -/

section

namespace FR

open RecursionFast

variable (impl : OpImpl) (κ : Kind) (inp : Input)

theorem rd_append_left {a b : Array Val} {i : ℕ} (h : i < a.size) : rd (a ++ b) i = rd a i := by
  simp [rd, Array.getElem?_append_left h]

theorem rd_append_right (a b : Array Val) (j : ℕ) : rd (a ++ b) (a.size + j) = rd b j := by
  simp [rd, Array.getElem?_append_right]

theorem rd_push_size (a : Array Val) (v : Val) : rd (a.push v) a.size = v := by simp [rd]

theorem rd_push_left {a : Array Val} {i : ℕ} (v : Val) (h : i < a.size) :
    rd (a.push v) i = rd a i := by
  simp [rd, Array.getElem?_push, Nat.ne_of_lt h]

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
  cases op <;> first | rfl | simp [evalOp] at h

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

theorem rd_app_left (r : Array Val) (L : List Val) {k : ℕ} (h : k < r.size) : rd (r ++ L.toArray) k = rd r k :=
  rd_append_left h

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
  ([.b (msgAt inp f o uniBytes), .d a₁, .d a₂, .f (chF a₂ 0)] : List Val) ++
    ((uniEs inp f o).map .f : List Val) ++
    ([.af (uniEs inp f o).toArray, .af pe, .f x.1, .f x.2,
      .b (msgAt inp f (o + 2032) 16)] : List Val)

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

theorem sqzT_spec {n : ℕ} {d : Digest} {tr : Trace} {x : List Digest × Trace}
    (h : sqzT n d tr = some x) : x.1.length = n := by
  induction n generalizing d tr x with
  | zero => simp [sqzT] at h; subst h; rfl
  | succ n ih =>
    simp only [sqzT, Option.bind_eq_some_iff, Option.map_eq_some_iff] at h
    obtain ⟨p, -, y, hy, rfl⟩ := h
    simp [ih hy]

theorem exec_sqzC (n st : ℕ) (r : Array Val) (ok : Bool) (ops : List Op) (hst : st < r.size) (tr : Trace) :
    exec impl κ inp (sqzCoordOps n st r.size ++ ops) ⟨r, ok⟩ tr =
      (sqzT n (rd r st).toD tr).bind fun p => exec impl κ inp ops ⟨r ++ (p.1.flatMap coordVals).toArray, ok⟩ p.2 := by
  rw [exec_append, exec_sqzCoordOps impl κ inp n st r.size ⟨r, ok⟩ tr rfl hst, Option.bind_map]; rfl

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

end FR

end

/-! ## From `FRVIRChain` (22 declarations) -/

section

namespace FR

open RecursionFast

variable (inp : Input)

/-- The query of message `m` at Fiat–Shamir position `p` from state `st` (`fsQ`'s body). -/
def qOf (p : ℕ) (m : Option (ℕ × ℕ)) (st : Digest) : ByteArray :=
  match m with
  | some (o, len) => if p = 0 then seedQ inp.vk inp.c (inp.π.extract o (o + len))
      else absorbQ st (inp.π.extract o (o + len))
  | none => squeezeQ st

/-- **`ChainOK es ms p st`**: the entries ask the chain of the messages `ms` from position `p`. -/
def ChainOK : Trace → List (Option (ℕ × ℕ)) → ℕ → Digest → Prop
  | [], [], _, _ => True
  | (q, a) :: es, m :: ms, p, st => q = qOf inp p m st ∧ ChainOK es ms (p + 1) a
  | _, _, _, _ => False

/-- The last answer of `es` (`d` if empty). -/
def lastAns (es : Trace) (d : Digest) : Digest := (es.getLast?.map (·.2)).getD d

/-- The entries of `seg` at the Fiat–Shamir items of `its`. -/
def fsOf (seg : Trace) (its : List Item) : Trace := ((seg.zip its).filter (·.2.isFS)).map (·.1)

theorem ChainOK_length {es : Trace} {ms : List (Option (ℕ × ℕ))} {p : ℕ} {st : Digest}
    (h : ChainOK inp es ms p st) : es.length = ms.length := by
  induction es generalizing ms p st with
  | nil => cases ms <;> simp_all [ChainOK]
  | cons e es ih =>
    obtain ⟨q, a⟩ := e
    cases ms with
    | nil => simp [ChainOK] at h
    | cons m ms => simp only [ChainOK] at h; simp [ih h.2]

theorem lastAns_append (a b : Trace) (d : Digest) :
    lastAns (a ++ b) d = lastAns b (lastAns a d) := by
  cases b using List.reverseRecOn <;> simp [lastAns, List.getLast?_append]

theorem lastAns_cons (q : ByteArray) (a : Digest) (es : Trace) (d : Digest) :
    lastAns ((q, a) :: es) d = lastAns es a := by
  rw [show (q, a) :: es = [(q, a)] ++ es from rfl, lastAns_append]; rfl

theorem ChainOK_append {a b : Trace} {ma mb : List (Option (ℕ × ℕ))} {p : ℕ} {st : Digest}
    (hl : a.length = ma.length) :
    ChainOK inp (a ++ b) (ma ++ mb) p st ↔
      ChainOK inp a ma p st ∧ ChainOK inp b mb (p + a.length) (lastAns a st) := by
  induction a generalizing ma p st with
  | nil => cases ma <;> simp_all [ChainOK, lastAns]
  | cons e a ih =>
    obtain ⟨q, x⟩ := e
    cases ma with
    | nil => simp at hl
    | cons m ma =>
      simp only [List.cons_append, ChainOK, List.length_cons, lastAns_cons]
      rw [ih (by simpa using hl), show p + (a.length + 1) = p + 1 + a.length by omega, and_assoc]

theorem fsOf_append {s₁ s₂ : Trace} {i₁ i₂ : List Item} (h : s₁.length = i₁.length) :
    fsOf (s₁ ++ s₂) (i₁ ++ i₂) = fsOf s₁ i₁ ++ fsOf s₂ i₂ := by
  simp [fsOf, List.zip_append h]

theorem fsOf_all {seg : Trace} {its : List Item} (h : ∀ it ∈ its, it.isFS = true)
    (hl : seg.length = its.length) : fsOf seg its = seg := by
  induction seg generalizing its with
  | nil => simp [fsOf]
  | cons e seg ih =>
    cases its with
    | nil => simp at hl
    | cons it its =>
      have h1 := h it (List.mem_cons_self ..)
      have := ih (fun x hx => h x (List.mem_cons_of_mem _ hx)) (by simpa using hl)
      simp only [fsOf, List.zip_cons_cons, List.filter_cons, h1, ite_true, List.map_cons] at this ⊢
      rw [this]

theorem fsOf_none {seg : Trace} {its : List Item} (h : ∀ it ∈ its, it.isFS = false) :
    fsOf seg its = [] := by
  simp only [fsOf, List.map_eq_nil_iff, List.filter_eq_nil_iff]
  intro x hx; simp [h _ (List.of_mem_zip hx).2]

theorem fieldOffA_getD {f : ℕ} (hf : f ≤ nFields) : fieldOffA.getD f 0 = fieldOff f := by
  simp [fieldOffA, Array.getD_eq_getD_getElem?, List.getElem?_range (by omega : f < nFields + 1)]

variable (κ : Kind)

theorem sqzT_chain {k : ℕ} {d : Digest} {tr : Trace} {y : List Digest × Trace}
    (hy : sqzT k d tr = some y) (p : ℕ) :
    ∃ seg, tr = seg ++ y.2 ∧ seg.length = k ∧ ChainOK inp seg (List.replicate k none) p d ∧
      seg.map (·.2) = y.1 := by
  induction k generalizing d tr y p with
  | zero => simp [sqzT] at hy; subst hy; exact ⟨[], by simp, rfl, by simp [ChainOK], rfl⟩
  | succ k ih =>
    rcases tr with _ | ⟨⟨q, a⟩, tr⟩
    · simp [sqzT, ans1] at hy
    simp only [sqzT, ans1, Option.bind_eq_some_iff, Option.map_eq_some_iff] at hy
    obtain ⟨z, hz, w, hw, rfl⟩ := hy
    split_ifs at hz with hq
    cases hz
    obtain ⟨seg, h1, h2, h3, h4⟩ := ih hw (p + 1)
    refine ⟨(q, a) :: seg, by simpa using h1, by simp [h2], ?_, by simp [h4]⟩
    exact ⟨by simp [qOf, hq], h3⟩

theorem lastAns_map {seg : Trace} {as : List Digest} (h : seg.map (·.2) = as) (d : Digest) :
    lastAns seg d = as.getLastD d := by
  subst h; simp [lastAns, List.getLastD_eq_getLast?, List.getLast?_map]

/-- One round's two messages from round `j` (the absorbed range at `A + o + j·rb`). -/
def roundMsgs (A o rb j k : ℕ) : List (Option (ℕ × ℕ)) :=
  (List.range' j k).flatMap fun j => [some (A + o + j * rb, rb), none]

theorem roundsT_chain {f o deg real k j : ℕ} {inK : Bool} {d : Digest} {cl : Val} {tr : Trace}
    {x : List Val × Bool × Trace} (hx : roundsT inp f o deg inK real k j d cl tr = some x)
    {p : ℕ} (hp : p ≠ 0) :
    ∃ seg, tr = seg ++ x.2.2 ∧ seg.length = 2 * k ∧
      ChainOK inp seg (roundMsgs (fieldOffA.getD f 0) o (roundBytes inK) j k) p d ∧
      lastAns seg d = if k = 0 then d else
        (x.1.getD ((if inK then 13 else roundW deg) * k - (if inK then 13 else roundW deg) + 2)
          default).toD := by
  induction k generalizing j d cl tr x p with
  | zero =>
    simp [roundsT] at hx; subst hx
    exact ⟨[], by simp, rfl, by simp [ChainOK, roundMsgs], by simp [lastAns]⟩
  | succ k ih =>
    rcases tr with _ | ⟨⟨q₁, a₁⟩, _ | ⟨⟨q₂, a₂⟩, tr⟩⟩
    · cases hx
    · cases hx
    simp only [roundsT] at hx
    by_cases hq : q₁ = absorbQ d (msgAt inp f (o + j * roundBytes inK) (roundBytes inK)) ∧
      q₂ = squeezeQ a₁
    swap; · rw [if_neg hq] at hx; cases hx
    rw [if_pos hq] at hx
    obtain ⟨y, hy, rfl⟩ := Option.map_eq_some_iff.1 hx
    obtain ⟨seg, h1, h2, h3, h4⟩ := ih hy (p := p + 2) (by omega)
    have hv := roundV_spec inp f (o + j * roundBytes inK) deg inK (decide (j < real)) a₁ a₂ cl
    simp only [roundV] at hv
    have hW3 : 3 ≤ (if inK = true then 13 else roundW deg) := by unfold roundW; split_ifs <;> omega
    generalize hW : (if inK = true then 13 else roundW deg) = W at hv h4 hW3 ⊢
    generalize hV : (if inK = true then roundKVals inp f (o + j * roundBytes inK) (decide (j < real)) a₁ a₂ cl
      else if deg = 3 then round3V inp f (o + j * roundBytes inK) (decide (j < real)) a₁ a₂ cl
      else round2Vals inp f (o + j * roundBytes inK) (decide (j < real)) a₁ a₂ cl) = V at hv ⊢
    obtain ⟨hvl, hv2, -⟩ := hv
    refine ⟨(q₁, a₁) :: (q₂, a₂) :: seg, by simp [h1], by simp [h2]; omega, ?_, ?_⟩
    · simp only [roundMsgs, List.range'_succ, List.flatMap_cons, List.cons_append, List.nil_append,
        ChainOK, qOf, if_neg hp]
      refine ⟨?_, hq.2, ?_⟩
      · rw [hq.1, msgAt]; simp [absOff, Nat.add_assoc]
      · simpa [roundMsgs, show p + 1 + 1 = p + 2 by omega] using h3
    · rw [lastAns_cons, lastAns_cons, h4, if_neg (Nat.succ_ne_zero k)]
      rcases Nat.eq_zero_or_pos k with rfl | hk
      · rw [if_pos rfl, show W * (0 + 1) - W + 2 = 2 by omega, List.getD_eq_getElem?_getD,
          List.getElem?_append_left (by omega), ← List.getD_eq_getElem?_getD, hv2]; rfl
      · have hW1 : W ≤ W * k := Nat.le_mul_of_pos_right _ hk
        have key : ∀ (A B : List Val) (m : ℕ), (A ++ B).getD (A.length + m) default = B.getD m default :=
          fun A B m => by simp [List.getD_eq_getElem?_getD, List.getElem?_append_right]
        dsimp only
        rw [if_neg (by omega),
          show W * (k + 1) - W + 2 = V.length + (W * k - W + 2) by rw [hvl, Nat.mul_succ]; omega, key]

theorem getD_app (A B : List Val) (m : ℕ) : (A ++ B).getD (A.length + m) default = B.getD m default := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_append_right]

theorem getD_last_coords {as : List Digest} (h : as ≠ []) (L : List Val) :
    (as.flatMap coordVals ++ L).getD (3 * as.length - 3) default = .d (as.getLastD zeroD) := by
  obtain ⟨ini, a, rfl⟩ := List.eq_nil_or_concat as |>.resolve_left h
  have := getD_app (ini.flatMap coordVals) (coordVals a ++ L) 0
  rw [coordVals_length] at this
  simpa [List.flatMap_append, List.append_assoc, Nat.mul_succ, coordVals] using this

theorem getD_last_map {as : List Digest} (h : as ≠ []) (L : List Val) :
    (as.map Val.d ++ L).getD (as.length - 1) default = .d (as.getLastD zeroD) := by
  obtain ⟨ini, a, rfl⟩ := List.eq_nil_or_concat as |>.resolve_left h
  have := getD_app (ini.map Val.d) (Val.d a :: L) 0
  simpa [List.append_assoc] using this

theorem getLastD_ne {as : List Digest} (h : as ≠ []) (d d' : Digest) : as.getLastD d = as.getLastD d' := by
  obtain ⟨ini, a, rfl⟩ := List.eq_nil_or_concat as |>.resolve_left h
  simp

variable (impl : OpImpl)

theorem fsOf_prefix {seg rest : Trace} {its : List Item} (h : seg.length = its.length) :
    fsOf (seg ++ rest) its = fsOf seg its := by
  have := fsOf_append (s₂ := rest) (i₂ := []) h
  simpa [fsOf] using this

theorem ChainOK_getD : ∀ {es : Trace} {ms : List (Option (ℕ × ℕ))} {p : ℕ} {st : Digest},
    ChainOK inp es ms p st → ∀ i < es.length,
      (es.getD i default).1 = qOf inp (p + i) (ms.getD i none)
        (if i = 0 then st else (es.getD (i - 1) default).2)
  | [], _, _, _, _, i, hi => by simp at hi
  | (q, a) :: es, [], _, _, h, _, _ => by simp [ChainOK] at h
  | (q, a) :: es, m :: ms, p, st, h, i, hi => by
    simp only [ChainOK] at h
    rcases i with _ | i
    · simpa using h.1
    · have := ChainOK_getD h.2 i (by simpa using hi)
      rw [show p + (i + 1) = p + 1 + i by omega]
      simp only [List.getD_cons_succ, this, Nat.add_sub_cancel]
      rcases i with _ | i <;> simp

end FR

end
