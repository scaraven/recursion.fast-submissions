-- New for `flock-recursive` (BLUEPRINT revision 4.1, §3, §5.5, §9; stage S-I, items 1–2): the
-- revision 4.1 `Submission` term, compiled for the badge, its completeness and `δ`.
import FRSubmission4V
import FRXNd4

/-!
# The revision 4.1 submission `sub4`

The fields (X4-RESULT §3):

* `V := V4F` (`FRSubmission4V`), which is `VC4 implB (NI4F.implN4F fun _ => implB) N4c.cells4`
  (`V4F_eq`), `implB := Impl.implCN`, every program and op set a closed constant.
* `P := fun _ _ w => ret (encodeF w)`: the witness-sending prover of `complete4`.
* `E := E4X nd acc` and `ext := ext4With nd`: S-H3's extractor with S-H4's node branch `nd`
  (`FRXNd4`: the decode `decF04 κ`, then the output `outIR4 κ`, per node kind).
* `ε := epsRQ`, the cast of the rational `15/2^124` (`epsRQ_eq`: it is `epsR`), so that the
  structure has compiled code (AGENTS.md: the badge compiles the whole `submission`).
* `δ := 0`, `qV := qV4 = 36000`, `fuel := X.fuel` (`3 · 2^46 + 2^13 t`).

**Completeness (residuals 8 and 9 of X4).** `complete4` (`FRVerifier4`) proves the contract's
`CompleteWithError` at `δ = 0` for every verifier `V4with Vseg Vnode` and the prover `encodeF`,
under every key: the honest proof of a witness is its witness-sending encoding, which `V4with`
accepts with no query (`V4_encode`). The contract's `Certificate.complete` asks exactly that for
the submission's own `P`, `V` and `δ` (`.contract/RecursionFast/Contract/Certificate.lean`,
`complete`), so **`complete_rev4`** and **`delta_rev4`** close both residuals with no hypothesis.
The completeness of the aggregate and node proofs that `prover.s` sends is not part of the
contract's certificate; the harness checks it concretely (`acc` of every stream output).
-/

namespace FR.Sub4
open RecursionFast FR.Rev4
open RecursionFast.WitnessSending (encodeF)
open scoped NNReal

/-! ## The submission -/

/-- The submission without its extractor specification (whose `acc` it reads). -/
def sub0 : Submission where
  V := V4F
  P := fun _ _ w => .ret (encodeF w)
  E := fun _ _ _ => none
  ext := X.X4.ext4With X.X4.nd
  ε := epsRQ
  δ := 0
  qV := qV4
  fuel := X.fuel

/-- **The revision 4.1 submission**: `sub0` with `E := E4X nd sub0.acc`. -/
def sub4 : Submission := { sub0 with E := X.X4.E4X X.X4.nd sub0.acc }

/-- `acc` reads only `V` and `qV`. -/
theorem sub4_acc : sub4.acc = sub0.acc := rfl

theorem sub4_V : sub4.V = VC4 implB (NI4F.implN4F fun _ => implB) N4c.cells4 := V4F_eq
theorem sub4_qV : sub4.qV = qV4 := rfl
theorem sub4_E : sub4.E = X.X4.E4X X.X4.nd sub4.acc := rfl
theorem sub4_ε : sub4.ε = Snd.epsR := epsRQ_eq
theorem sub4_ext : sub4.ext = X.X4.ext4With X.X4.nd := rfl
theorem sub4_fuel : sub4.fuel = X.fuel := rfl
theorem sub4_P : sub4.P = fun _ _ w => .ret (encodeF w) := rfl

/-! ## Completeness: X4's residuals 8 and 9 -/

/-- **Residual 8, closed**: the contract's completeness of `sub4` under every key, at `δ = 0`
(`complete4`: the witness-sending path). -/
theorem complete_rev4 (vk : Digest) :
    CompleteWithError (Rel (sub4.acc vk)) (sub4.P vk) (sub4.V vk) sub4.δ :=
  complete4 VsegF VnodeF sub4 rfl rfl rfl vk

/-- **Residual 9, closed**: `δ = 0 ≤ completenessCap`. -/
theorem delta_rev4 : sub4.δ ≤ completenessCap := zero_le

/-! ## Controls -/

/-- (+) The honest proof of a one-step leaf witness is accepted with no query; (−) a node kind byte
with the wrong size is rejected with no query. -/
theorem sub4_ctrl (vk s c : Digest) :
    sub4.V vk (leafStmt (chainEnd s 1) 1) (WitnessSending.encode (.leaf s 1)) = .ret true ∧
      sub4.V vk c ⟨#[NodeKind.N4.byte]⟩ = .ret false :=
  ⟨ctrl4_W_leaf VsegF VnodeF vk s, ctrl4_bad_node_size VsegF VnodeF vk c⟩

/-- (+) `δ = 0` is the completeness error, and (−) it is not the knowledge error's bound: the
claim's `ε` is positive. -/
theorem sub4_numbers : sub4.δ = 0 ∧ 0 < sub4.ε := by
  refine ⟨rfl, ?_⟩
  rw [sub4_ε, Snd.epsR]; positivity

end FR.Sub4
