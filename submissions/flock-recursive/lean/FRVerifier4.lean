-- New for `flock-recursive` (BLUEPRINT revision 4.0, B-11, B-13, B-17; §3; stage S-0′).
import FRAgg
import FRNodeLayout4
import FRVerifier

/-!
# Revision 4.1's verifier `V4`: the top-level dispatch over `W`, `A`, `N2`, `N4`, `N8`

BLUEPRINT §3 with revision 4.1's kinds (B-11, B-13). `V4with Vseg Vnode vk c π` reads byte 0:

* `'A'` (`aggByte`): the aggregate leaf, `V_A` (`FRAgg.VAwith`) with segment proofs of
  `piSizeOf seq4 = 798,192` bytes and the segment programs `Vseg`;
* a node kind byte (`N2` `'M'`, `N4` `'N'`, `N8` `'O'`) with `|π| = piSizeOf seq4 = 798,192`: the node program
  `Vnode κ`; another size: reject (`bad`), no query. A node's children are verified inside its
  circuit, not by `V4with`: the check a node of kind `κ` applies to an aggregate child is
  `childOk4 κ` (at most `κ.maxK` segments: `N2` refuses `k > 2`, R-4-m2), a row of the node circuit
  (S-E) and a truth of its soundness (S-G);
* a segment kind byte (`L30`, `L31`, `L32`): reject (`bad`): a segment is never a child of the relation,
  only a part of an aggregate leaf;
* anything else: the witness-sending branch (`W`, completeness, `P := encode`), with **this**
  verifier for a node's children (`accWith4`, well-founded on `|π|`), as 3.x's `Vwith`.

`Vseg` and `Vnode` are parameters (the concrete programs are `FRVerifierC4`'s `VsegC`/`VnodeC`).
`qV4 = 36,000` (B-17).

* **`acc_eq4`**: the contract's `Submission.acc` with `V = V4with Vseg Vnode` and `qV = qV4` is
  `accV4`.
* **`V4_W_sound`**, **`V4_encode`**, **`complete4`**: as 3.x's (`δ = 0`). `complete4` is the
  contract's completeness for `P := encode` (the `W` path); it holds for every `Vseg`/`Vnode` and
  is no evidence for the `A`/node path, whose completeness is `FRAgg.VA_complete` (R-4 Q3).
* **`V4_agg_extract`**: an accepted `A` proof yields its leaf witness (`FRAgg.VA_extract`).
* **`V4_queries_le`**, **`ks_queries4`**: `V4with` asks at most `qV4` queries on every input and
  oracle, given per-program bounds (`A`: `4 ×` a segment program's; a node: its program's; `W`:
  none): `KS`'s first conjunct (R-4-m4).
* Controls: `ctrl4_W_leaf` (accepted), `ctrl4_bad_node_size`, `ctrl4_seg_top`, `ctrl4_bad_byte`
  (rejected, no query); `childOk4_ctrl` (`N2` takes an aggregate child of 2 segments and refuses 3;
  `N4` takes 3).
-/

namespace FR
namespace Rev4
open RecursionFast
open RecursionFast.WitnessSending (encode decode decode_encode decodeF encodeF decodeF_eq encodeF_eq
  size_child_lt)

/-- What `V4` does with a proof. -/
inductive PKind4 where
  | W | bad | agg
  | node (κ : NodeKind)
  deriving DecidableEq, Repr

/-- **The kind of a proof** (byte 0, and the size for a node kind). -/
def kindOf4 (π : Proof) : PKind4 :=
  let b := byteAt π 0
  if b = aggByte then .agg
  else match NodeKind.ofByte? b with
    | some κ => if π.size = piSizeOf seq4 then .node κ else .bad
    | none => if (SegKind.ofByte? b).isSome then .bad else .W

/-- **Acceptance of a signed proof** with the verifier's program `v ()` (`Submission.acc` with
`qV4` and the fast hashes; the first conjunct is core PR #20's). -/
def accWith4 (vk : Digest) (p : Signed) (v : Unit → OProg Bool) : Bool :=
  decide (p.π.size < 2 ^ 64) && decide (p.tr.length ≤ qV4) &&
    decide (∀ e ∈ p.tr, e.1.size ≤ queryCap) && SigOkF vk (traceDigestF p.tr) p.σ &&
    decide ((v ()).runSeq p.tr = some true)

/-- The segment programs' type. -/
abbrev SegProgs := SegKind → Digest → Digest → Proof → OProg Bool
/-- The node programs' type. -/
abbrev NodeProgs := NodeKind → Digest → Digest → Proof → OProg Bool

/-- **The verifier** of revision 4.1. -/
def V4with (Vseg : SegProgs) (Vnode : NodeProgs) (vk c : Digest) (π : Proof) : OProg Bool :=
  match kindOf4 π with
  | .agg => VAwith (piSizeOf seq4) Vseg vk c π
  | .node κ => Vnode κ vk c π
  | .bad => .ret false
  | .W =>
    match decodeF π with
    | some (.leaf s n) =>
      .ret (decide (encodeF (.leaf s n) = π) && decide (n ≤ chainCap) &&
        decide (c = leafStmtF (chainEndF s n) n))
    | some (.node c₁ c₂ p₁ p₂) =>
      if _h : encodeF (.node c₁ c₂ p₁ p₂) = π then
        .ret (decide (c = nodeStmtF c₁ c₂) && accWith4 vk p₁ (fun _ => V4with Vseg Vnode vk c₁ p₁.π) &&
          accWith4 vk p₂ (fun _ => V4with Vseg Vnode vk c₂ p₂.π))
      else .ret false
    | none => .ret false
termination_by π.size
decreasing_by
  · rw [← _h, encodeF_eq]; exact (size_child_lt _ _ _ _).1
  · rw [← _h, encodeF_eq]; exact (size_child_lt _ _ _ _).2

/-- **The acceptance predicate of the relation** (revision 4.1). -/
def accV4 (Vseg : SegProgs) (Vnode : NodeProgs) (vk c : Digest) (p : Signed) : Bool :=
  accWith4 vk p fun _ => V4with Vseg Vnode vk c p.π

/-- **`acc_eq4`**: `Submission.acc` is `accV4` for a submission with verifier `V4with Vseg Vnode`
and query bound `qV4`. -/
theorem acc_eq4 (Vseg : SegProgs) (Vnode : NodeProgs) (S : Submission)
    (hV : S.V = V4with Vseg Vnode) (hq : S.qV = qV4) : S.acc = accV4 Vseg Vnode := by
  funext vk c p
  rw [Submission.acc, accV4, accWith4, hV, hq, SigOkF_eq, traceDigestF_eq]

section Branches
variable (Vseg : SegProgs) (Vnode : NodeProgs) (vk c : Digest) (π : Proof)

theorem V4_bad (h : kindOf4 π = .bad) : V4with Vseg Vnode vk c π = .ret false := by
  rw [V4with, h]

theorem V4_agg (h : kindOf4 π = .agg) :
    V4with Vseg Vnode vk c π = VAwith (piSizeOf seq4) Vseg vk c π := by rw [V4with, h]

theorem V4_node {κ : NodeKind} (h : kindOf4 π = .node κ) : V4with Vseg Vnode vk c π = Vnode κ vk c π := by
  rw [V4with, h]

/-- The `W` branch, with the specification functions. -/
theorem V4_W (h : kindOf4 π = .W) : V4with Vseg Vnode vk c π = .ret (
    match decode π with
    | some (.leaf s n) =>
      decide (encode (.leaf s n) = π) && decide (n ≤ chainCap) && decide (c = leafStmt (chainEnd s n) n)
    | some (.node c₁ c₂ p₁ p₂) =>
      if encode (.node c₁ c₂ p₁ p₂) = π then
        decide (c = nodeStmt c₁ c₂) && accV4 Vseg Vnode vk c₁ p₁ && accV4 Vseg Vnode vk c₂ p₂
      else false
    | none => false) := by
  rw [V4with, h]; simp only [decodeF_eq, encodeF_eq, leafStmtF_eq, chainEndF_eq, nodeStmtF_eq, accV4]
  split <;> (try split) <;> simp_all

/-- **An accepted `W` proof is the canonical encoding of a witness of the relation.** -/
theorem V4_W_sound (h : kindOf4 π = .W) (hacc : V4with Vseg Vnode vk c π = .ret true) :
    ∃ w, decode π = some w ∧ encode w = π ∧ Rel (accV4 Vseg Vnode vk) c w := by
  rw [V4_W Vseg Vnode vk c π h, OProg.ret.injEq] at hacc
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

/-- **An accepted aggregate leaf yields its leaf witness**, given sound segment programs. -/
theorem V4_agg_extract (h : kindOf4 π = .agg) (hS : SegSound Vseg vk) {tr : Trace}
    (hacc : (V4with Vseg Vnode vk c π).runSeq tr = some true) :
    ∃ s n, aggWit (piSizeOf seq4) π = some (s, n) ∧ n ≤ chainCap ∧ c = leafStmt (chainEnd s n) n := by
  rw [V4_agg Vseg Vnode vk c π h] at hacc; exact VA_extract hS hacc

end Branches

/-! ## Queries (`KS`'s first conjunct) -/

/-- **`V4with`'s queries** under `H`: at most `qV4`, given a bound `qS` on every segment program's
with `4 · qS ≤ qV4` (`A`: `k ≤ 4` is checked before any query) and `qV4` on every node program's.
`W` and `bad` ask none. -/
theorem V4_queries_le (Vseg : SegProgs) (Vnode : NodeProgs) (H : ByteArray → Digest) {qS : ℕ}
    (hS : ∀ κ vk c π, ((Vseg κ vk c π).queries H).length ≤ qS)
    (hN : ∀ κ vk c π, ((Vnode κ vk c π).queries H).length ≤ qV4) (hq : 4 * qS ≤ qV4)
    (vk c : Digest) (π : Proof) : ((V4with Vseg Vnode vk c π).queries H).length ≤ qV4 := by
  rcases h : kindOf4 π with _ | _ | _ | κ
  · rw [V4_W Vseg Vnode vk c π h]; exact Nat.zero_le _
  · rw [V4_bad Vseg Vnode vk c π h]; exact Nat.zero_le _
  · rw [V4_agg Vseg Vnode vk c π h]; exact (VA_queries_le H hS vk c π).trans hq
  · rw [V4_node Vseg Vnode vk c π h]; exact hN _ _ _ _

/-- **`KS`'s first conjunct** for a submission with verifier `V4with Vseg Vnode` and `qV = qV4`. -/
theorem ks_queries4 (Vseg : SegProgs) (Vnode : NodeProgs) (S : Submission)
    (hV : S.V = V4with Vseg Vnode) (hq : S.qV = qV4) {qS : ℕ}
    (hS : ∀ H κ vk c π, ((Vseg κ vk c π).queries H).length ≤ qS)
    (hN : ∀ H κ vk c π, ((Vnode κ vk c π).queries H).length ≤ qV4) (h4 : 4 * qS ≤ qV4) (vk : Digest) :
    ∀ H c π, ((S.V vk c π).queries H).length ≤ S.qV := fun H c π => by
  rw [hV, hq]; exact V4_queries_le Vseg Vnode H (hS H) (hN H) h4 vk c π

/-! ## A node's aggregate child (R-4-m2) -/

/-- **The check a node of kind `κ` applies to a child proof**: an aggregate leaf (`'A'`) has at most
`κ.maxK` segments (`N2`: 2; `N4`/`N8`: 4), so its digest chain fits H (`childOk4_chain`). Any other
child is unaffected. The node circuit enforces it (S-E); `V4with` does not see a node's children. -/
def childOk4 (κ : NodeKind) (π : Proof) : Bool :=
  match kindOf4 π with
  | .agg => decide ((byteAt π 1).toNat ≤ κ.maxK)
  | _ => true

/-- An aggregate child that passes `childOk4 κ` has a chain of at most H's `aggChainLen κ.maxK`
blocks. -/
theorem childOk4_chain {κ : NodeKind} {π : Proof} (h : childOk4 κ π = true) (ha : kindOf4 π = .agg) :
    aggChainLen (byteAt π 1).toNat ≤ aggChainLen κ.maxK := by
  simp only [childOk4, ha, decide_eq_true_eq] at h; exact aggChainLen_le h

/-- **The check binds only `N2`**: for `N4`/`N8` (`maxK = 4`) every proof `V4with` accepts passes it
(`V_A` checks `k ≤ 4`). -/
theorem childOk4_of_accept {κ : NodeKind} (hκ : κ.maxK = 4) {Vseg : SegProgs} {Vnode : NodeProgs}
    {vk c : Digest} {π : Proof} {tr : Trace} (h : (V4with Vseg Vnode vk c π).runSeq tr = some true) :
    childOk4 κ π = true := by
  unfold childOk4
  split
  · next ha =>
    rw [V4_agg Vseg Vnode vk c π ha] at h
    simpa [hκ] using (VA_k_range h).2
  · rfl

/-- Controls: `N2` takes an aggregate child of 2 segments and refuses 3; `N4` takes 3; a
witness-sending proof is unaffected. -/
theorem childOk4_ctrl : childOk4 .N2 ⟨#[aggByte, 2]⟩ = true ∧ childOk4 .N2 ⟨#[aggByte, 3]⟩ = false ∧
    childOk4 .N4 ⟨#[aggByte, 3]⟩ = true ∧ childOk4 .N2 ⟨#[1, 3]⟩ = true := by
  decide

/-! ## Completeness (§5.5) -/

theorem kindOf4_encode (w : Wit) : kindOf4 (encode w) = .W := by
  rcases encode_byte0 w with h | h
  · have hb : byteAt (encode w) 0 = 0 := by rw [byteAt_eq, Array.getD_eq_getD_getElem?, h]; rfl
    unfold kindOf4; simp only [hb]; rfl
  · have hb : byteAt (encode w) 0 = 1 := by rw [byteAt_eq, Array.getD_eq_getD_getElem?, h]; rfl
    unfold kindOf4; simp only [hb]; rfl

theorem fits_of_accWith4 {vk : Digest} {p : Signed} {v : Unit → OProg Bool}
    (h : accWith4 vk p v = true) : p.Fits := by
  simp only [accWith4, Bool.and_eq_true, decide_eq_true_eq, SigOkF_eq, SigOk] at h
  obtain ⟨⟨⟨⟨hπ, htr⟩, hq⟩, ⟨⟨hi, ho⟩, hp⟩, -⟩, -⟩ := h
  exact ⟨hπ, htr.trans_lt (by decide), fun e he => (hq e he).trans_lt (by decide),
    hi.trans (by decide), ho, hp⟩

theorem fits_of_rel4 {Vseg : SegProgs} {Vnode : NodeProgs} {vk c : Digest} {w : Wit}
    (h : Rel (accV4 Vseg Vnode vk) c w) : w.Fits := by
  cases w with
  | leaf s n => exact h.1.trans_lt (by decide)
  | node c₁ c₂ p₁ p₂ => exact ⟨fits_of_accWith4 h.2.1, fits_of_accWith4 h.2.2⟩

/-- **The honest proof of a witness of the relation is accepted, with no query.** -/
theorem V4_encode (Vseg : SegProgs) (Vnode : NodeProgs) {vk c : Digest} {w : Wit}
    (hR : Rel (accV4 Vseg Vnode vk) c w) : V4with Vseg Vnode vk c (encode w) = .ret true := by
  rw [V4_W Vseg Vnode vk c _ (kindOf4_encode w), decode_encode w (fits_of_rel4 hR)]
  cases w with
  | leaf s n => simp [hR.1, hR.2]
  | node c₁ c₂ p₁ p₂ => simp [hR.1, hR.2.1, hR.2.2]

/-- **Perfect completeness** of `P vk c w := ret (encodeF w)` (§5.5), for every key. -/
theorem complete4 (Vseg : SegProgs) (Vnode : NodeProgs) (S : Submission)
    (hV : S.V = V4with Vseg Vnode) (hq : S.qV = qV4) (hP : S.P = fun _ _ w => .ret (encodeF w))
    (vk : Digest) : CompleteWithError (Rel (S.acc vk)) (S.P vk) (S.V vk) 0 := by
  refine complete_withError_zero fun H c w hR => ?_
  rw [acc_eq4 Vseg Vnode S hV hq] at hR
  rw [hP, hV]
  show (V4with Vseg Vnode vk c (encodeF w)).run H = true
  rw [encodeF_eq, V4_encode Vseg Vnode hR]; rfl

/-! ## Controls -/

section Controls
variable (Vseg : SegProgs) (Vnode : NodeProgs) (vk : Digest)

/-- Positive: the honest proof of a one-step leaf witness is accepted, with no query. -/
theorem ctrl4_W_leaf (s : Digest) :
    V4with Vseg Vnode vk (leafStmt (chainEnd s 1) 1) (encode (.leaf s 1)) = .ret true :=
  V4_encode Vseg Vnode ⟨by decide, rfl⟩

/-- Negative: a node kind byte with the wrong size is rejected, with no query. -/
theorem ctrl4_bad_node_size (c : Digest) : V4with Vseg Vnode vk c ⟨#[NodeKind.N4.byte]⟩ = .ret false :=
  V4_bad Vseg Vnode vk c _ (by rw [kindOf4, piSizeOf_seq4]; decide)

/-- Negative: a bare segment proof is not a top-level proof (rejected, no query). -/
theorem ctrl4_seg_top (c : Digest) : V4with Vseg Vnode vk c ⟨#[SegKind.L32.byte]⟩ = .ret false :=
  V4_bad Vseg Vnode vk c _ (by decide)

/-- Negative: a first byte that is no kind byte and no witness tag is rejected (the `W` decoder
fails), with no query. -/
theorem ctrl4_bad_byte (c : Digest) : V4with Vseg Vnode vk c ⟨#[2, 0, 0, 0, 0, 0, 0, 0]⟩ = .ret false := by
  rw [V4_W Vseg Vnode vk c _ (by decide)]
  rfl

/-- Positive: the `A` byte reaches `V_A`. -/
theorem ctrl4_agg (c : Digest) (π : Proof) (h : byteAt π 0 = aggByte) :
    V4with Vseg Vnode vk c π = VAwith (piSizeOf seq4) Vseg vk c π :=
  V4_agg Vseg Vnode vk c π (by unfold kindOf4; simp only [h, ite_true])

end Controls

end Rev4
end FR
