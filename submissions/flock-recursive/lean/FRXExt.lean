-- New for `flock-recursive` (BLUEPRINT §6.4; stage S-H2, track L-ext).
import FRXDec
import FRXNode
import FRXSearch

/-!
# The extractor `ext`, its specification `E`, and `computes`

`ext := extWith decSnark` with the SNARK branch delivered so far. **`E` (B-15, revision 4.0)** is
`if InDomE then Ed else Eout`:
* `Ed`, the decoded denotation of `ext`'s program (B-8, revision 3.17), on the contract's
  `Computes` domain `InDomE`: proofs of at most `8 · outCap` bytes, queries below `2^64` bytes, a
  tape of at most `2^64` words;
* `Eout` outside it, by the proof's kind: a `W` proof is decoded (`WitnessSending.decode`), a node
  SNARK is searched (`FRXSearch.search` with the acceptance `A` under the key `vkOf π` that the
  proof carries), a leaf SNARK keeps the denotation (domain-free, `FRXLeaf.E_leaf`), a `bad` proof
  has none.

`E` is parametric in `A`, the acceptance the search tests: the verifier is still parametric
(`finPf`, `lRows`), and the certificate instantiates `A := S.acc`. `computes` holds for every `A`,
since `E = Ed` on the domain. Every branch is a compiled `def`: the badge compiles `E`, it does not
run it.

*Why the dispatch (deviation from B-15's text "else `E_search`").* The search's key is `vkOf π`,
which is the verifier's key only on an accepted node run (`vkOf_of_run`). A `W` proof's bytes
`16 … 47` are arbitrary, and for a leaf SNARK the search could return a node witness for the
wrong key; both have a domain-free witness instead.
-/

namespace FR.X

open RecursionFast

/-! ## The program delivered: `ext`, `E`, `computes` -/

/-- **The SNARK branch delivered so far**: a leaf (`'L'`, `'P'`) outputs its witness from the
header (§6.2 step 1, `FRXLeaf.E_leaf`); a node (`'N'`) runs the log index and the ladder read of
level 0 (§6.2 steps 2–3, `read_spec`), replays the Fiat–Shamir chain from the seed it carries
(`FRXDec.chain_dec`), decodes the five levels into `f⁽⁰⁾`'s rows (§6.2 step 4,
`FRXNode.decLevels_sem`), and outputs the node witness read off `f⁽⁰⁾` (§6.2 step 5,
`FRXOutRun.outIR_out`, `FRXNodeRun.E_node`). -/
def decSnark : XIR := decLN3

theorem decOk_decSnark : DecOk decSnark := decOk_decLN3

/-- **The extractor program** `ext := toProg 2^26 3 extIR` (§6.4). -/
def ext : XProg := extWith decSnark

/-- **The in-domain extractor** (B-8, revision 3.17): the decoded denotation of `ext`'s program,
`Ed c π L = decodeWit (semXIR extIR …).o` on the tape `extractorInput c π L`, a total computable
function on every log (no fuel). On the domain it is `ext`'s output (`computesWith`). -/
def Ed : Digest → Proof → Log → Option Wit := Eden memX mpwX (extIRWith decSnark)

/-- **The contract's `Computes` domain**: a proof of at most `8 · outCap` bytes, queries below
`2^64` bytes, a tape of at most `2^64` words. -/
def InDomE (c : Digest) (π : Proof) (L : Log) : Prop :=
  π.size ≤ 8 * outCap ∧ (∀ e ∈ L, e.1.size < 2 ^ 64) ∧ (extractorInput c π L).length ≤ 2 ^ 64

instance (c : Digest) (π : Proof) (L : Log) : Decidable (InDomE c π L) :=
  inferInstanceAs (Decidable (_ ∧ _ ∧ _))

/-- **The extractor outside the domain** (B-15), by the proof's kind: `W` decoded, a node SNARK
searched under the key it carries, a leaf SNARK's denotation, `bad` none. -/
def Eout (A : Digest → Digest → Signed → Bool) (c : Digest) (π : Proof) (L : Log) : Option Wit :=
  match kindOf π with
  | .W => WitnessSending.decode π
  | .snark k => if k.isNode then search A (vkOf π) c else Ed c π L
  | .bad => none

/-- **The extractor specification** (B-15, revision 4.0): `Ed` on the domain, `Eout` outside it;
`A` is the acceptance the search tests (the certificate's `S.acc`). -/
def E (A : Digest → Digest → Signed → Bool) (c : Digest) (π : Proof) (L : Log) : Option Wit :=
  if InDomE c π L then Ed c π L else Eout A c π L

variable {A : Digest → Digest → Signed → Bool} {c : Digest} {π : Proof} {L : Log}

theorem E_of_dom (h : InDomE c π L) : E A c π L = Ed c π L := if_pos h

theorem E_of_not_dom (h : ¬ InDomE c π L) : E A c π L = Eout A c π L := if_neg h

/-- A SNARK proof has `piSize` bytes. -/
theorem size_snarkX {k : Kind} (hk : kindOf π = .snark k) : π.size = piSize := by
  by_contra hne
  simp only [kindOf, byteAt?_eq, hne, if_false] at hk
  split at hk <;> simp at hk

/-- A SNARK proof is within the domain's proof bound. -/
theorem size_snark_le {k : Kind} (hk : kindOf π = .snark k) : π.size ≤ 8 * outCap := by
  rw [size_snarkX hk, piSize_eq, outCap]; norm_num

/-- **A leaf SNARK's extractor is the denotation, on every log.** -/
theorem E_snark_leaf {k : Kind} (hk : kindOf π = .snark k) (hkn : k.isNode = false) :
    E A c π L = Ed c π L := by
  by_cases h : InDomE c π L
  · exact E_of_dom h
  · rw [E_of_not_dom h, Eout]; simp [hk, hkn]

/-- **A node SNARK outside the domain is searched** under the key it carries. -/
theorem E_snark_node {k : Kind} (hk : kindOf π = .snark k) (hkN : k.isNode = true)
    (h : ¬ InDomE c π L) : E A c π L = search A (vkOf π) c := by
  rw [E_of_not_dom h, Eout]; simp [hk, hkN]

/-- **`Computes ext (E A) fuel`**, for every `A`: the certificate's `computes` conjunct (on the
domain `E A = Ed`, `computesWith`). -/
theorem computes (A : Digest → Digest → Signed → Bool) : Computes ext (E A) fuel :=
  fun c π L h1 h2 h3 => by
    obtain ⟨o, ho, hl, hd⟩ := computesWith decOk_decSnark c π L h1 h2 h3
    exact ⟨o, ho, hl, hd.trans (E_of_dom ⟨h1, h2, h3⟩).symm⟩

/-- The certificate's caps on the extractor: the fuel within `B`, the program within `progCap`. -/
theorem ext_caps : (∀ t, fuel t ≤ extractorBudget t) ∧ ext.body.size ≤ progCap :=
  ⟨fuel_le_budget, size_extWith decOk_decSnark.size⟩

end FR.X
