/-
# The top-level statements of lvm6 and the certificate's assembly (WP S; BLUEPRINT §5 T5–T9)

The programs are written by later work packages (`prog6` and `VS` by V1, `EX` and `extX` by X2,
the circuit's relation by CA–CD), so each statement here is a `Prop` about them, named as the
theorem that will prove it (`Stmt.node6V` is what `node6` proves, and so on). **Load-bearing**:
everything in this file; the certificate depends on exactly the fields of `Open6`.

* **`schemeOf prog sh vk`** (decision of 2026-11-22, WP ASM): the compiled scheme of `FORMAT6.md`
  v2.4 is V1's `Lvm6.V.schemeP (toV sh) vk (prog sh vk)`: V1's specified scheme `scheme6V`
  (statements are the header's bytes, the seed is `a₀ ‖ HDR`, v2.5, the check `hdrOkWith` (magic, `b`, `n`,
  `c'`, `vk`, statement), read widths `rwOf (sched6 sh)`, challenges `chalOf`: `chal6` and the PoW
  lane are its lanes 0–1 and 2, `e2OfE_chalOf`, `powOK6_iff`) with the interactive program `prog`
  in place of the schedule walk. WP ASM instantiates `prog` with the composed phase programs
  `Lvm6.prog6` (`Lvm6AsmProg`); V1's `replay_refines` turns the executable walk into this scheme.
* **`Stmt.refines6`** (T7): `V_S` accepting on a log implies the compiled verifier accepting.
* **`Stmt.VS_queries`**: `V_S` asks at most `qS` queries.
* **`Stmt.node6V`** (T6): a header the executable checks accept (statement `c`, key `vk`) and a
  stack satisfying the good relation give the relation for the witness read from the stack (`witOf6`: the blocks in leaf
  mode; in node mode the left child from `STREAM` and the right `W` leaf with `σ_leaf`).
  `Good6 rest = TreeOk ∧ rest`: the tree part is frozen, `rest` (sponge, typed, mini-bus,
  `STREAM`), `childOf` and `sigLeafOf` are §T parameters. **`node6_leaf`** proves the leaf case now.
* **`ExtEq6 EX K`** (T8 `ext_eq6`): on every available log (`Avail`), the extractor is the
  specification extractor `Eideal K` of the knowledge certificate `K` (T5 `kcert6`).
* **`Stmt.computes6`** (T8): `extX` computes `EX` within `2^47 + 8192·t`.
* **`submissionOf VS EX extX`**, **`declared6`**, **`Open6`** and **`certified_of`** (T9): the
  certificate against `declared6` from the six obligations of `Open6`, proved here.

**Constants** (decision of 2026-11-22): `qV = qVlvm = 16384` everywhere (`claim.json`,
`LvmVerifier`); `declared6`'s fuel `2^47 + 8192·t` is the value `claim.json` takes at CERT.
The static guard of BLUEPRINT §2.4 (`V = W ∘ guard ∘ V_S`) is CERT's: instantiate `VS` with the
guarded program.
-/
import Lvm6StmtPhase
import Lvm6VReplay
import LvmCertSGen

set_option autoImplicit false

namespace Lvm6

open RecursionFast Lvm.T LeanVM.Parameters
open RecursionFast.WitnessSending (encode decode encodeF)
open LeanVM.Protocol.Compile hiding Proof Bytes Word
open scoped NNReal

/-! ## The compiled scheme (T5's object) -/

/-- **The compiled scheme** of the interactive program `prog` (of the header's bytes) at the shape
`sh` under the key `vk`: V1's specified scheme of `sched6 sh` with `P := prog sh vk`. -/
def schemeOf (prog : Shape → Digest → List UInt8 → VerifierProgram Bool) (sh : Shape)
    (vk : Digest) : Lvm.FS.Scheme :=
  V.schemeP (toV sh) vk (prog sh vk)

/-- The scheme's program is `prog`. -/
theorem schemeOf_P (prog : Shape → Digest → List UInt8 → VerifierProgram Bool) (sh : Shape)
    (vk : Digest) (x : List UInt8) : (schemeOf prog sh vk).P x = prog sh vk x := rfl

/-- The compiled verifier of a family of schemes, as an `S` branch. -/
def schemeV (sc : Digest → Lvm.FS.Scheme) : SProg := fun vk c π => (sc vk).V c π

/-- **`V_S` refines `V'`**: every `S` proof `V_S` accepts on a log, `V'` accepts on it. -/
def Refines (VS V' : SProg) : Prop :=
  ∀ vk L c π, isS π = true → (VS vk c π).runLog L = some true → (V' vk c π).runLog L = some true

/-- **T7 `refines6`**. -/
def Stmt.refines6 (VS : Shape → SProg)
    (prog : Shape → Digest → List UInt8 → VerifierProgram Bool) : Prop :=
  ∀ sh, Refines (VS sh) (schemeV (schemeOf prog sh))

/-- **`VS_queries`**: at most `qS` queries, on every proof and oracle. -/
def Stmt.VS_queries (VS : Shape → SProg) : Prop :=
  ∀ sh vk c π (H : ByteArray → Digest), ((VS sh vk c π).queries H).length ≤ sh.qS

/-! ## T6: rows give the relation -/

/-- **The witness an accepted `S` proof proves** (BLUEPRINT §2.1): the stack's blocks in leaf
mode; in node mode the left child and the right `W` leaf `⟨encode (leaf blocks), [], σ_leaf⟩`. -/
def witOf6 (x : Hdr) (q : Stack) (child : Signed) (σl : Sig) : Wit :=
  if x.b = 0 then .leaf (blocksOf q)
  else .node x.c' (leafStmt x.h x.n.toNat) child ⟨encode (.leaf (blocksOf q)), [], σl⟩

/-- **The good relation**: the tree relation for the header's root, and the rest (`rest`: sponge,
typed phases, mini-bus, `STREAM`; `FORMAT6.md` §T). -/
def Good6 (rest : Hdr → Stack → Prop) (x : Hdr) (q : Stack) : Prop := TreeOk q x.h ∧ rest x q

/-- **Node soundness** for `V_S`, key pinned (NODE §3): a well-formed header whose statement is `c`
and whose key is `vk` (the circuit checks the child's signature under the header's key), and a good
stack, give the relation for the witness read from the stack. -/
def NodeSound6V (VS : SProg) (vk : Digest) (Good : Hdr → Stack → Prop) (child : Stack → Signed)
    (sigLeaf : Stack → Sig) : Prop :=
  ∀ c x q, HdrWF P17 x → stmtOk c x = true → x.vk = vk → Good x q →
    Rel (accV VS vk) c (witOf6 x q (child q) (sigLeaf q))

/-- **The bridge from the scheme's header check to `node6`'s view** (open; V1 part 2 or F1): a
header the scheme accepts (`hdrOkWith` on its bytes) has a well-formed view whose statement is
`c` and whose key is `vk`. `kcert6`'s extraction uses it to apply `node6V` to the scheme's
statements. -/
def Stmt.hdrView_okV : Prop :=
  ∀ (vk c : Digest) (x : List UInt8), x.length = hdrLen P17 →
    V.hdrOkWith leafStmt nodeStmt (2 ^ P17.logN) vk c ⟨x.toArray⟩ = true →
    HdrWF P17 (hdrView P17 x) ∧ stmtOk c (hdrView P17 x) = true ∧ (hdrView P17 x).vk = vk

/-- **T6 `node6`, key pinned**, at the node's shape `P17` (PORT17; was `P18`), for the circuit's relation
`rest` and readers of `STREAM`. -/
def Stmt.node6V (VS : Shape → SProg) (rest : Hdr → Stack → Prop) (childOf : Stack → Signed)
    (sigLeafOf : Stack → Sig) : Prop :=
  ∀ vk, NodeSound6V (VS P17) vk (Good6 rest) childOf sigLeafOf

/-- **`node6` in leaf mode** (proved): the tree relation alone gives the leaf relation. -/
theorem node6_leaf (VS : SProg) (vk : Digest) (rest : Hdr → Stack → Prop)
    (child : Stack → Signed) (sigLeaf : Stack → Sig) {c : Digest} {x : Hdr} {q : Stack}
    (hwf : HdrWF P17 x) (hok : stmtOk c x = true) (hb : x.b = 0) (hg : Good6 rest x q) :
    Rel (accV VS vk) c (witOf6 x q (child q) (sigLeaf q)) := by
  have hc : c = stmtOf x := of_decide_eq_true hok
  rw [witOf6, ite_eq_left hb]
  refine ⟨by simp [length_blocksOfAt, leafCap], ?_⟩
  rw [length_blocksOfAt, treeOk_sound hg.1, hc, stmtOf, ite_eq_left hb, leafStmtF_eq, hwf.n_eq]
  rfl

/-! ## T5, T8: the knowledge certificate and the extractor -/

section Ext

variable {S : Lvm.FS.Scheme} {R : Digest → Wit → Prop}

/-- **An available log** for an `S` proof: within `logCap`, of potential below `1` (no bad entry,
outside doom and luck), and the compiled verifier accepts on it. -/
def Avail (K : Lvm.FS.KCert S R) (c : Digest) (π : Proof) (L : Log) : Prop :=
  isS π = true ∧ L.length ≤ logCap ∧ Lvm.FS.Scheme.μ K L < 1 ∧ (S.V c π).runLog L = some true

/-- **The ideal extractor** of a knowledge certificate: replay, then its extraction map. -/
def Eideal (K : Lvm.FS.KCert S R) : Digest → Proof → Log → Option Wit := S.Ex K.ext

/-- **T8 `ext_eq6`**: on every available log, the extractor is the ideal one. -/
def ExtEq6 (EX : Digest → Proof → Log → Option Wit) (K : Lvm.FS.KCert S R) : Prop :=
  ∀ c π L, Avail K c π L → EX c π L = Eideal K c π L

end Ext

/-- The declared fuel `2^47 + 8192·t`. -/
def fuel6 (t : ℕ) : ℕ := 2 ^ 47 + 8192 * t

/-- **T8 `computes6`**. -/
def Stmt.computes6 (extX : XProg) (EX : Digest → Proof → Log → Option Wit) : Prop :=
  Computes extX EX fuel6

/-! ## T9: the submission and its certificate -/

/-- **The submission** with `S` branch `VS`: `'S'` → `VS`, otherwise witness sending; the honest
prover sends the witness (`δ = 0`); `ε = 2^-128`; fuel `2^47 + 8192·t`. -/
def submissionOf (VS : SProg) (EX : Digest → Proof → Log → Option Wit) (extX : XProg) :
    Submission where
  V := Vwith VS
  P := fun _ _ w => .ret (encodeF w)
  E := EX
  ext := extX
  ε := ((1 / 2 ^ 128 : ℚ≥0) : ℝ≥0)
  δ := ((0 : ℚ≥0) : ℝ≥0)
  qV := qVlvm
  fuel := fuel6

/-- **The declared claim** of lvm6, in `render-challenge.py`'s rendered form. -/
noncomputable def declared6 : Declared where
  ε := (1 : ℝ≥0) / 340282366920938463463374607431768211456
  δ := (0 : ℝ≥0) / 1
  qV := qVlvm
  fuel t := 140737488355328 + 8192 * t

/-- **The six obligations of the certificate** at `P17` (BLUEPRINT T5–T8). -/
structure Open6 (VS : Shape → SProg) (prog : Shape → Digest → List UInt8 → VerifierProgram Bool)
    (EX : Digest → Proof → Log → Option Wit) (extX : XProg) : Prop where
  /-- `VS_queries` at `P17`. -/
  queries : ∀ vk c π (H : ByteArray → Digest), ((VS P17 vk c π).queries H).length ≤ P17.qS
  /-- `refines6` at `P17`. -/
  refines : Refines (VS P17) (schemeV (schemeOf prog P17))
  /-- `kcert6`, `εFS_kcert6` and `ext_eq6` (T5, T8). -/
  sound : ∀ vk, ∃ K : Lvm.FS.KCert (schemeOf prog P17 vk) (Rel (accV (VS P17) vk)),
    Lvm.FS.Scheme.εFS K ≤ (2 : ℝ≥0)⁻¹ ^ 128 ∧ ExtEq6 EX K
  /-- The extractor decodes `W` proofs. -/
  wBranch : ∀ c π L, isS π = false → EX c π L = decode π
  /-- `computes6`. -/
  computes : Computes extX EX fuel6
  /-- The program within `progCap` statements. -/
  size : extX.body.size ≤ progCap

section Assembly

variable (VS : SProg) (EX : Digest → Proof → Log → Option Wit) (extX : XProg)

theorem submissionOf_acc : (submissionOf VS EX extX).acc = accV VS := acc_eq VS _ rfl rfl

theorem submissionOf_ε : (submissionOf VS EX extX).ε = (2 : ℝ≥0)⁻¹ ^ 128 := by
  simp only [submissionOf]; push_cast; rw [one_div, inv_pow]

theorem submissionOf_δ : (submissionOf VS EX extX).δ = 0 := by simp [submissionOf]

end Assembly

/-- **T9 assembly** (`certified`'s shape): the six obligations give the certificate against
`declared6`. -/
theorem certified_of {VS : Shape → SProg}
    {prog : Shape → Digest → List UInt8 → VerifierProgram Bool}
    {EX : Digest → Proof → Log → Option Wit} {extX : XProg} (h : Open6 VS prog EX extX) :
    CertificateR declared6 (submissionOf (VS P17) EX extX) := by
  have hq : ∀ H vk c π, isS π = true → ((VS P17 vk c π).queries H).length ≤ qVlvm :=
    fun H vk c π _ => (h.queries vk c π H).trans (by decide)
  refine ⟨⟨fun vk => ?_, fun vk => ?_, h.computes, ?_⟩, ?_⟩
  · obtain ⟨K, hε, hE⟩ := h.sound vk
    rw [submissionOf_acc, submissionOf_ε]
    have k := (Lvm.FS.KState.congr (Lvm.FS.Scheme.kstate_of_kcert K)
      (V' := Vwith (VS P17) vk) (E' := EX) (by
        intro L c π hl hμ hacc
        cases hs : isS π
        · left
          obtain ⟨w, hw, hR⟩ := V_W_runLog (VS P17) vk c π hs hacc
          exact ⟨w, by rw [h.wBranch c π L hs, hw], hR⟩
        · rw [V_S (VS P17) vk c π hs] at hacc
          have hv := h.refines vk L c π hs hacc
          exact .inr ⟨hv, hE c π L ⟨hs, hl, hμ, hv⟩⟩)).mono hε
    exact k.ks fun H c π => V_queries_le (VS P17) H (hq H) vk c π
  · rw [submissionOf_δ]; exact complete (VS P17) _ rfl rfl rfl vk
  · refine ⟨by rw [submissionOf_ε]; rfl, by rw [submissionOf_δ]; exact zero_le,
      show qVlvm ≤ 2 ^ 16 by decide, fun t => ?_, h.size⟩
    simp only [submissionOf, fuel6, extractorBudget]; omega
  · refine ⟨?_, by simp [submissionOf, declared6], le_rfl, fun t => ⟨le_of_eq ?_, ?_⟩⟩
    · simp only [submissionOf, declared6]; push_cast; norm_num
    · simp [submissionOf, declared6, fuel6]
    · simp only [declared6, extractorBudget]; omega

end Lvm6
