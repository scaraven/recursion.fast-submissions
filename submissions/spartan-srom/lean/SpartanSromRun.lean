-- Ported from v3 `spartan-chain` (submissions repo, local `main` at `1f59b38`) to the v4 contract.
import SpartanSromFinal
import RecursionFast.Library.Blake2sFast

/-!
# The compiled runner's functions (BLUEPRINT §8; v3 BLUEPRINT-R1 §10 `Run.lean`, §11.3)

Plain functions for a compiled executable (which lives outside the root). They call **exactly the
certified objects** (v3 review S2b-m2):

* `accRun vk c p` is the entry's acceptance of a signed proof, the contract's
  `Submission.acc SpartanSrom.submission vk c p` (`accRun_eq`); it runs `V` with its fast twins
  (`SpartanSromNode`), and `SigOk`, `traceDigest` with the library's (`SigOkF`, `traceDigestF`).
* `proveWith H vk c w` is the entry's honest prover `P` run under an oracle **function** `H`
  (`proveWith_eq`): a known-answer test against the native prover passes a deterministic test
  oracle, e.g. `katOracleF` (`= katOracle`, BLAKE2s-256 of `0x52 ‖ q`, v3's contract oracle).
* `honestTrace H vk c π`: the verifier's queries on `π` under `H`, with `H`'s answers (the trace
  the service would sign; `OProg.runSeq_queries` of the library: `V` accepts on it iff it
  accepts under `H`).
* `parseSigned`: the signed-proof file of `harness/FORMAT.md`, read strictly (a length running
  past the end or bytes after the last path digest: `none`); `encodeSigned` writes it.
No `main` and no elaboration-time code here.
-/

namespace SpartanSrom

namespace Run

open RecursionFast

/-- **The entry's acceptance of a signed proof** under `vk` (`accRun_eq`). -/
def accRun (vk c : Digest) (p : Signed) : Bool := accV leafVerifier vk c p

/-- `accRun` is the contract's `acc` of the entry's submission. -/
theorem accRun_eq : accRun = submission.acc := (acc_eq leafVerifier proveLeafR1).symm

/-- **The entry's honest prover** run under the oracle function `H`. -/
def proveWith (H : ByteArray → Digest) (vk c : Digest) (w : Wit) : Proof :=
  (P proveLeafR1 vk c w).run H

/-- `proveWith` is the submission's `P` under `H`. -/
theorem proveWith_eq (H : ByteArray → Digest) (vk c : Digest) (w : Wit) :
    proveWith H vk c w = (submission.P vk c w).run H := rfl

/-- The test oracle `katOracle` through the byte-array BLAKE2s (`katOracleF_eq`). -/
def katOracleF (q : ByteArray) : Digest := Blake2s.digestL (0x52 :: q.data.toList)

theorem katOracleF_eq : katOracleF = katOracle := funext fun _ => Blake2s.digestL_eq _

/-- The honest trace of the verifier on `π` under the oracle function `H`. -/
def honestTrace (H : ByteArray → Digest) (vk c : Digest) (π : Proof) : Trace :=
  ((V leafVerifier vk c π).queries H).map fun q => (q, H q)

/-! ## The signed-proof file (harness/FORMAT.md) -/

/-- The little-endian 64-bit number at byte `o`. -/
def u64At (b : ByteArray) (o : ℕ) : ℕ := ofLE (b.extract o (o + 8)).toList

/-- `m` trace entries from byte `o` (`|q| ‖ q ‖ a` each), accumulated in reverse in `acc`; the
entries and the offset after them, or `none` if one runs past the end. -/
def parseEntries (b : ByteArray) : ℕ → ℕ → Trace → Option (Trace × ℕ)
  | 0, o, acc => some (acc.reverse, o)
  | m + 1, o, acc =>
    if o + 8 ≤ b.size then
      if o + 8 + u64At b o + 32 ≤ b.size then
        parseEntries b m (o + 8 + u64At b o + 32)
          ((b.extract (o + 8) (o + 8 + u64At b o), digestFrom b (o + 8 + u64At b o)) :: acc)
      else none
    else none

/-- **A signed-proof file**, read strictly: `|π| ‖ π ‖ m ‖ entries ‖ j ‖ 133 chain values ‖ 16
path digests`, ending exactly there. -/
def parseSigned (b : ByteArray) : Option Signed :=
  if 16 + u64At b 0 ≤ b.size then
    match parseEntries b (u64At b (8 + u64At b 0)) (16 + u64At b 0) [] with
    | some (tr, o) =>
      if o + 8 + 32 * (wotsLen + sigHeight) = b.size then
        some ⟨b.extract 8 (8 + u64At b 0), tr,
          ⟨u64At b o, (List.range wotsLen).map fun i => digestFrom b (o + 8 + 32 * i),
            (List.range sigHeight).map fun i => digestFrom b (o + 8 + 32 * (wotsLen + i))⟩⟩
      else none
    | none => none
  else none

/-- The 8 little-endian bytes of `n`. -/
def u64Bytes (n : ℕ) : ByteArray := ⟨(enc64 n).toArray⟩

/-- **The signed-proof file of `p`** (harness/FORMAT.md). -/
def encodeSigned (p : Signed) : ByteArray :=
  let tr := p.tr.foldl (fun b e => b ++ u64Bytes e.1.size ++ e.1 ++ ⟨e.2.toArray⟩) ByteArray.empty
  let ds := (p.σ.ots ++ p.σ.path).foldl (fun b d => b ++ ⟨d.toArray⟩) ByteArray.empty
  u64Bytes p.π.size ++ p.π ++ u64Bytes p.tr.length ++ tr ++ u64Bytes p.σ.idx ++ ds

end Run

end SpartanSrom
