-- New for `flock-recursive` (BLUEPRINT §3, §3.3, §5.5, §7; stage S-F).
-- RET-3: the declarations revision 4 reads moved to `FRVIRSpecCore`.
import FRVIRFinalsSF
import RecursionFast.Library.WitnessSending
import FRVIRSpecCore

/-!
# The verifier `V`, `accWith`, `acc_eq`

BLUEPRINT §3: `V vk c π` reads the proof's kind (`FRFormat.kindOf`):

* `snark k` (kind byte `L`/`P`/`N` and `|π| = piSize`): `runIR impl (gen fin (.fixed k))`, the IR
  program with every phase-final check (`FRVIRFinals.gen`);
* `bad` (a kind byte with another size): reject, no query;
* `W` (any other first byte): the witness-sending decision of the library's strict format, with
  **this** verifier's acceptance for a node's children (`accWith`, by well-founded recursion on
  `|π|`; §3.3: no size cap, the `W` branch asks nothing).

`Vwith impl fin` is parametric in the op implementations and the finals; the submission's `V` is
`Vwith impl (sfFinals finP finPf)` once S-G's fields and the concrete `impl` exist (RESULT, open 1).

* **`acc_eq`**: the contract's `Submission.acc` of a submission whose verifier is `Vwith impl fin`
  and whose query bound is `qV` is `accV impl fin` (`accWith` with `Vwith` inlined). This is the
  predicate `node_sound` (S-E2) concludes and `Rel` is stated with.
* **`V_W_sound`**: an accepted `W` proof is the canonical encoding of a witness of
  `Rel (accV impl fin vk)`; **`complete`**: `P := encode` is accepted on every witness of the relation
  (§5.5, `δ = 0` by `complete_withError_zero`).
* **`runSeq_length`**: an accepting run uses the trace up exactly, one entry per ask op of
  `gen` (a truncated or extended trace is rejected).
* Controls: a leaf witness's proof is accepted (`ctrl_W_leaf`); a kind byte with the wrong size
  is rejected with no query (`ctrl_bad_size`); a non-kind first byte that does not decode is
  rejected with no query (`ctrl_bad_byte`); a truncated trace is rejected (`ctrl_truncated`).
-/

namespace FR
open RecursionFast
open RecursionFast.WitnessSending (encode decode decode_encode decodeF encodeF decodeF_eq encodeF_eq
  size_child_lt)

/-- The verifier's query bound: `items_length = 8,854 ≤ qV` (revision 3.8: 8,870). -/
def qV : ℕ := 10240

/-- **Acceptance of a signed proof under `vk`**, the verifier's program on its proof being `v ()`:
`Submission.acc` with `qV` and the fast hashes (`v` delayed so that compiled code builds the
child's program only after the cheap checks). The first conjunct is the contract's (core PR #20:
the proof's length fits a 64-bit word; `proofCap` is gone). -/
def accWith (vk : Digest) (p : Signed) (v : Unit → OProg Bool) : Bool :=
  decide (p.π.size < 2 ^ 64) && decide (p.tr.length ≤ qV) &&
    decide (∀ e ∈ p.tr, e.1.size ≤ queryCap) && SigOkF vk (traceDigestF p.tr) p.σ &&
    decide ((v ()).runSeq p.tr = some true)

/-- **The verifier** with op implementations `impl` and finals `fin` (§3). -/
def Vwith (impl : OpImpl) (fin : Finals) (vk c : Digest) (π : Proof) : OProg Bool :=
  match kindOf π with
  | .snark k => runIR impl (gen fin (.fixed k)) ⟨vk, c, π⟩
  | .bad => .ret false
  | .W =>
    match decodeF π with
    | some (.leaf s n) =>
      .ret (decide (encodeF (.leaf s n) = π) && decide (n ≤ chainCap) &&
        decide (c = leafStmtF (chainEndF s n) n))
    | some (.node c₁ c₂ p₁ p₂) =>
      if _h : encodeF (.node c₁ c₂ p₁ p₂) = π then
        .ret (decide (c = nodeStmtF c₁ c₂) && accWith vk p₁ (fun _ => Vwith impl fin vk c₁ p₁.π) &&
          accWith vk p₂ (fun _ => Vwith impl fin vk c₂ p₂.π))
      else .ret false
    | none => .ret false
termination_by π.size
decreasing_by
  · rw [← _h, encodeF_eq]; exact (size_child_lt _ _ _ _).1
  · rw [← _h, encodeF_eq]; exact (size_child_lt _ _ _ _).2

/-- **The acceptance predicate of the relation**: `accWith` with `Vwith impl fin`. `node_sound`
targets `accV impl fin vk c p = true`. -/
def accV (impl : OpImpl) (fin : Finals) (vk c : Digest) (p : Signed) : Bool :=
  accWith vk p fun _ => Vwith impl fin vk c p.π

/-- **`acc_eq`**: `Submission.acc` is `accV` for a submission with verifier `Vwith impl fin` and
query bound `qV`. -/
theorem acc_eq (impl : OpImpl) (fin : Finals) (S : Submission) (hV : S.V = Vwith impl fin)
    (hq : S.qV = qV) : S.acc = accV impl fin := by
  funext vk c p
  rw [Submission.acc, accV, accWith, hV, hq, SigOkF_eq, traceDigestF_eq]

section Branches
variable (impl : OpImpl) (fin : Finals) (vk c : Digest) (π : Proof)

theorem V_bad (h : kindOf π = .bad) : Vwith impl fin vk c π = .ret false := by rw [Vwith, h]

theorem V_snark {k : Kind} (h : kindOf π = .snark k) :
    Vwith impl fin vk c π = runIR impl (gen fin (.fixed k)) ⟨vk, c, π⟩ := by rw [Vwith, h]

/-- The `W` branch, with the specification functions. -/
theorem V_W (h : kindOf π = .W) : Vwith impl fin vk c π = .ret (
    match decode π with
    | some (.leaf s n) =>
      decide (encode (.leaf s n) = π) && decide (n ≤ chainCap) && decide (c = leafStmt (chainEnd s n) n)
    | some (.node c₁ c₂ p₁ p₂) =>
      if encode (.node c₁ c₂ p₁ p₂) = π then
        decide (c = nodeStmt c₁ c₂) && accV impl fin vk c₁ p₁ && accV impl fin vk c₂ p₂
      else false
    | none => false) := by
  rw [Vwith, h]; simp only [decodeF_eq, encodeF_eq, leafStmtF_eq, chainEndF_eq, nodeStmtF_eq, accV]
  split <;> (try split) <;> simp_all

/-- **An accepted `W` proof is the canonical encoding of a witness of the relation.** -/
theorem V_W_sound (h : kindOf π = .W) (hacc : Vwith impl fin vk c π = .ret true) :
    ∃ w, decode π = some w ∧ encode w = π ∧ Rel (accV impl fin vk) c w := by
  rw [V_W impl fin vk c π h, OProg.ret.injEq] at hacc
  split at hacc
  next s n hd =>
    simp only [Bool.and_eq_true, decide_eq_true_eq] at hacc
    exact ⟨.leaf s n, hd, hacc.1.1, hacc.1.2, hacc.2⟩
  next c₁ c₂ p₁ p₂ hd =>
    split at hacc
    · simp only [Bool.and_eq_true, decide_eq_true_eq] at hacc
      exact ⟨.node c₁ c₂ p₁ p₂, hd, ‹_›, hacc.1.1, hacc.1.2, hacc.2⟩
    · cases hacc
  · cases hacc

end Branches

/-! ## Completeness (§5.5) -/

theorem kindOf_encode (w : Wit) : kindOf (encode w) = .W := by
  rcases encode_byte0 w with h | h
  · exact kindOf_W h (.inl rfl)
  · exact kindOf_W h (.inr rfl)

/-- An accepted child fits the output format. -/
theorem fits_of_accWith {vk : Digest} {p : Signed} {v : Unit → OProg Bool}
    (h : accWith vk p v = true) : p.Fits := by
  simp only [accWith, Bool.and_eq_true, decide_eq_true_eq, SigOkF_eq, SigOk] at h
  obtain ⟨⟨⟨⟨hπ, htr⟩, hq⟩, ⟨⟨hi, ho⟩, hp⟩, -⟩, -⟩ := h
  exact ⟨hπ, htr.trans_lt (by decide), fun e he => (hq e he).trans_lt (by decide),
    hi.trans (by decide), ho, hp⟩

theorem fits_of_rel {impl : OpImpl} {fin : Finals} {vk c : Digest} {w : Wit}
    (h : Rel (accV impl fin vk) c w) : w.Fits := by
  cases w with
  | leaf s n => exact h.1.trans_lt (by decide)
  | node c₁ c₂ p₁ p₂ => exact ⟨fits_of_accWith h.2.1, fits_of_accWith h.2.2⟩

/-- **The honest proof of a witness of the relation is accepted, with no query.** -/
theorem V_encode (impl : OpImpl) (fin : Finals) {vk c : Digest} {w : Wit}
    (hR : Rel (accV impl fin vk) c w) : Vwith impl fin vk c (encode w) = .ret true := by
  rw [V_W impl fin vk c _ (kindOf_encode w), decode_encode w (fits_of_rel hR)]
  cases w with
  | leaf s n => simp [hR.1, hR.2]
  | node c₁ c₂ p₁ p₂ => simp [hR.1, hR.2.1, hR.2.2]

/-- **Perfect completeness** of `P vk c w := ret (encodeF w)` (§5.5), for every oracle and key. -/
theorem complete (impl : OpImpl) (fin : Finals) (S : Submission) (hV : S.V = Vwith impl fin)
    (hq : S.qV = qV) (hP : S.P = fun _ _ w => .ret (encodeF w)) (vk : Digest) :
    CompleteWithError (Rel (S.acc vk)) (S.P vk) (S.V vk) 0 := by
  refine complete_withError_zero fun H c w hR => ?_
  rw [acc_eq impl fin S hV hq] at hR
  rw [hP, hV]
  show (Vwith impl fin vk c (encodeF w)).run H = true
  rw [encodeF_eq, V_encode impl fin hR]; rfl

/-! ## Exact consumption of the trace -/

theorem exec_length (impl : OpImpl) (κ : Kind) (inp : Input) : ∀ (ops : List Op) (s : St) (tr : Trace)
    (s' : St) (tr' : Trace), exec impl κ inp ops s tr = some (s', tr') →
    tr.length = (ops.filterMap Op.item?).length + tr'.length
  | [], _, _, _, _, h => by simp [exec] at h; obtain ⟨-, rfl⟩ := h; simp
  | op :: ops, s, tr, s', tr', h => by
    simp only [exec] at h
    split at h
    · next vs ok hv =>
      rw [exec_length impl κ inp ops _ tr s' tr' h, List.filterMap_cons,
        item?_of_vals impl κ inp hv]
    · next q hq =>
      obtain ⟨it, hit⟩ := Option.isSome_iff_exists.1 (item?_of_ask impl κ inp hq)
      rcases tr with _ | ⟨⟨q', a⟩, tr⟩
      · cases h
      · simp only at h; split at h
        · rw [List.filterMap_cons, hit, List.length_cons, List.length_cons,
            exec_length impl κ inp ops _ tr s' tr' h]; omega
        · cases h

/-- **An accepting SNARK run uses one trace entry per ask op of `gen`.** -/
theorem runSeq_length (impl : OpImpl) (fin : Finals) {vk c : Digest} {π : Proof} {k : Kind}
    (hk : kindOf π = .snark k) {tr : Trace} (h : (Vwith impl fin vk c π).runSeq tr = some true) :
    tr.length = ((gen fin (.fixed k)).ops.filterMap Op.item?).length := by
  rw [V_snark impl fin vk c π hk, runSeq_runIR, semIR] at h
  split at h
  · next s hs => simpa using exec_length impl _ _ _ _ _ _ _ hs
  · cases h

/-! ## Controls (§5.6, format) -/

section Controls
variable (impl : OpImpl) (fin : Finals) (vk : Digest)

/-- Positive: the honest proof of a one-step leaf witness is accepted, with no query. -/
theorem ctrl_W_leaf (s : Digest) :
    Vwith impl fin vk (leafStmt (chainEnd s 1) 1) (encode (.leaf s 1)) = .ret true :=
  V_encode impl fin ⟨by decide, rfl⟩

/-- Negative: a kind byte with the wrong size is rejected, with no query. -/
theorem ctrl_bad_size (c : Digest) : Vwith impl fin vk c ⟨#[Kind.N30.byte]⟩ = .ret false :=
  V_bad impl fin vk c _ (kindOf_bad (k := .N30) rfl (by rw [piSize_eq]; decide))

/-- Negative: a first byte that is neither a kind byte nor a witness tag is rejected (the `W`
branch's decoder fails), with no query. -/
theorem ctrl_bad_byte (c : Digest) : Vwith impl fin vk c ⟨#[2, 0, 0, 0, 0, 0, 0, 0]⟩ = .ret false := by
  rw [V_W impl fin vk c _ (by rfl)]
  rfl

/-- Negative: a SNARK-kind proof against a trace shorter than its item sequence is rejected
(in particular the empty trace). -/
theorem ctrl_truncated {c : Digest} {π : Proof} {k : Kind} (hk : kindOf π = .snark k) {tr : Trace}
    (hlt : tr.length < ((gen fin (.fixed k)).ops.filterMap Op.item?).length) :
    (Vwith impl fin vk c π).runSeq tr ≠ some true := fun h =>
  (Nat.ne_of_lt hlt) (runSeq_length impl fin hk h)

end Controls

end FR
