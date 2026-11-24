/-
# The phase specifications of the lvm6 verifier (WP S; BLUEPRINT §5 T2, T3, T4, T4')

Claims on the stack at `E = GF(2^128)` and the frozen *shapes* of the phase specifications. Each
statement is a `Prop` about a program that a later work package writes (`treeProg` K1, `ringProg`
RS, `whirProg` W1, `typedProgE` Y1/CD); that package proves it at its program. They are
**plan-level**: the certificate (`Lvm6Stmt`) needs only `kcert6`, which these compose into.

* `StackClaim6`, `StackClaim6.Holds`: a weighted claim `Σ_x w(x)·q(x) = v` on the stack;
  `SliceClaim`, `SliceClaim.Holds`: the 64 bit-slice values `s_z = Σ_x eq(r, x)·bit_z(q(x))` that
  an input opening hands to ring switching (BLUEPRINT §2.3 step 7).
* **`DoomSpec p Good Holds`**, the shape every phase meets (season 1's doom transfer, as
  `typedSpecT`): for every candidate map `C` fixed during the phase and with at most one candidate
  on the histories of `G` (the OOD sample of §6.1 pins the list: `commitSpec6`) and every carried
  relation `R`, a `Spec` from "no candidate
  satisfies `Good ∧ R`" to "no candidate satisfies `Holds out ∧ R`", each group's escape at most
  `εI = 7·2^-131` (PARAM's per-group cap, grind included), lead `0`, follower lead `0` (every
  phase starts with a prover message).
* **`Stmt.treeSpec`** (T2): from `TreeOk q h` to the tree's output claims;
  **`Stmt.ringSpec6`** (T4'): from the slice and stack claims to one batched claim, over a list of
  at most `L₀` candidates;
  **`Stmt.typedSpecE`** (T4): from the typed relation (parameter, `FORMAT6.md` §T) to its claims;
  **`Stmt.commitSpec6`** (T3a): the commitment and its OOD sample (§6.1) establish `I.pinned`, one
  commitment and `Tied c₀` (claim 0 ties the candidates to the level-0 list) at the OOD group's
  escape; **`doomed_ball`** moves doom from the candidates to the list; **`OpeningIface.stackedSpec`**
  / **`Stmt.openSpec6`** (T3): from one commitment and a claim no list member satisfies, to
  rejection; `Stmt.noCommit`: a phase commits nothing (`CAND-decision.md`).

**Vacuity hazard (for the reviewer).** `openSpec6` is stated against an `OpeningIface`, whose
candidate map is a parameter (the seam for FB-PCS). With a degenerate map (e.g. every stack) the
precondition is false for every satisfiable claim and the statement is nearly trivial. W1 must
instantiate it as RV3 §3 states (Johnson-radius candidates of the level-0 word with the OOD pair;
`commitSpec6` at the same `I`); the certificate itself does not depend on this choice (`kcert6`
with `ext_eq6` binds extraction to the program extractor).
-/
import Lvm6Format
import Lvm6StmtTree
import LvmSpecRulesBasic
import LvmFrontMech

set_option autoImplicit false

namespace Lvm6

open LeanVM.Parameters LeanVM.Protocol.EndToEnd.Front
open LeanVM.Protocol.Compile hiding Proof Bytes Word
open scoped ENNReal

/-! ## Claims at `E` -/

/-- A claim on the stack: a weight function on points of `E^μ` and a value. -/
abbrev StackClaim6 : Type := (List E2 → E2) × E2

/-- The cube point of index `x`, bit `0` first. -/
def boolPt (μ x : ℕ) : List E2 := (List.range μ).map fun i => if x.testBit i then 1 else 0

/-- **A stack claim holds**: the weights on the cube, paired with the stack, give the value. -/
def StackClaim6.Holds (μ : ℕ) (c : StackClaim6) (q : Stack) : Prop :=
  ∑ x : Fin (2 ^ μ), c.1 (boolPt μ x) * algebraMap K E2 (q x) = c.2

/-- `eq(a, b) = Π (a_i b_i + (1 + a_i)(1 + b_i))` (characteristic 2). -/
def eqPt (a b : List E2) : E2 := (List.zipWith (fun r t => r * t + (1 + r) * (1 + t)) a b).prod

/-- **A claim's weight is multiaffine** on `μ` variables: at every point it is the multilinear
extension of its cube values (the opening's terminal check evaluates it at a random point). -/
def StackClaim6.Multiaffine (μ : ℕ) (c : StackClaim6) : Prop :=
  ∀ pt : List E2, pt.length = μ → c.1 pt = ∑ x : Fin (2 ^ μ), c.1 (boolPt μ x) * eqPt (boolPt μ x) pt

/-- Bit `z` of a word, in `E`. -/
def bitE (w : K) (z : ℕ) : E2 := if (K.lane w).toNat.testBit z then 1 else 0

/-- The 64 slice values of the stack at a point (the input of ring switching). -/
structure SliceClaim where
  /-- The point, `μ` coordinates. -/
  pt : List E2
  /-- The claimed value of each bit-slice. -/
  s : Fin 64 → E2

/-- **A slice claim holds**: slice `z` of the stack's multilinear extension at `pt` is `s z`. -/
def SliceClaim.Holds (μ : ℕ) (c : SliceClaim) (q : Stack) : Prop :=
  ∀ z : Fin 64, ∑ x : Fin (2 ^ μ), eqPt c.pt (boolPt μ x) * bitE (q x) z = c.s z

/-! ## The shape of a phase specification -/

/-- PARAM's per-group escape cap `εI = 7·2^-131`. -/
noncomputable def εI : ℝ≥0∞ := 7 * (2 : ℝ≥0∞)⁻¹ ^ 131

/-- **The doom transfer of a phase** (see the module docstring). -/
def DoomSpec {α Cand : Type} (p : VerifierProgram α) (Good : Cand → Prop)
    (Holds : α → Cand → Prop) : Prop :=
  ∀ (C : List Ev → Set Cand) (R : Cand → Prop) (G : List Ev → Prop),
    (∀ h₀ l, G h₀ → C (h₀ ++ l) = C h₀) → (∀ h, G h → (C h).Subsingleton) →
    Nonempty (Spec p (fun h => G h ∧ Doomed C (fun q => Good q ∧ R q) h)
      (fun out h => Doomed C (fun q => Holds out q ∧ R q) h) εI 0 0)

/-! ## T2: the tree wiring and reduction -/

/-- What the tree phase returns: the 64 slice claims of its input opening, and its stack claims
(`c_out`, the eight wiring claims, the four root claims). -/
structure TreeOut where
  /-- The input opening's slices (to ring switching). -/
  slices : SliceClaim
  /-- The column claims on the stack. -/
  claims : List StackClaim6

/-- The tree phase's claims hold of a stack. -/
def TreeOut.Holds (μ : ℕ) (o : TreeOut) (q : Stack) : Prop :=
  o.slices.Holds μ q ∧ ∀ c ∈ o.claims, c.Holds μ q

/-- **T2 `treeSpec`**: the tree phase of header `x` (§6.2) transfers doom from `TreeOk q x.h` to
its claims. -/
def Stmt.treeSpec (treeProg : Shape → Hdr → VerifierProgram TreeOut) : Prop :=
  ∀ sh x, DoomSpec (treeProg sh x) (fun q => TreeOkAt sh.logN q x.h) (fun o q => o.Holds sh.M q)

/-! ## T4': ring switching and batching -/

/-- **T4' `ringSpec6`**: ring switching and batching (§6.5) transfer doom from every slice and
stack claim (claim 0 `c₀` at the head of `st`) to the one batched claim, for at most two slice sets
and at most `J₀` stacked claims in all (`V_S` rejects more before the call), over any candidate map
fixed during the phase with at most `L₀` members on `G` (the level-0 list, `CAND-decision.md`).
The stack claims' weights are multiaffine, and so is the batched claim's (W1 F-3). -/
def Stmt.ringSpec6
    (ringProg : Shape → List SliceClaim → List StackClaim6 → VerifierProgram StackClaim6) : Prop :=
  ∀ sh sl st, sl.length ≤ 2 → sl.length + st.length ≤ sh.J₀ → (∀ c ∈ st, c.Multiaffine sh.M) →
    ∀ (C : List Ev → Set Stack) (G : List Ev → Prop), (∀ h₀ l, G h₀ → C (h₀ ++ l) = C h₀) →
      (∀ h, G h → (C h).Finite ∧ (C h).ncard ≤ sh.L₀) →
      Nonempty (Spec (ringProg sh sl st)
        (fun h => G h ∧ Doomed C (fun q => (∀ c ∈ sl, c.Holds sh.M q) ∧ ∀ c ∈ st, c.Holds sh.M q) h)
        (fun out h => out.Multiaffine sh.M ∧ Doomed C (fun q => out.Holds sh.M q) h) εI 0 0)

/-! ## T4: the typed phases (`FORMAT6.md` §T) -/

/-- **T4 `typedSpecE`**: the typed phases and mini-bus of an instance `i` (§6.4, not frozen)
transfer doom from the typed relation `TGood i` to their claims. `TGood` and the program are CD's
and MB's. -/
def Stmt.typedSpecE {ι : Type} (typedProgE : Shape → ι → VerifierProgram (List StackClaim6))
    (TGood : ι → Stack → Prop) : Prop :=
  ∀ sh i, DoomSpec (typedProgE sh i) (TGood i) (fun out q => ∀ c ∈ out, c.Holds sh.M q)

/-! ## T3: the opening -/

/-- **The seam between the phases and the PCS** (BLUEPRINT §5, `CAND-decision.md`): the level-0
list `ball` (at most `L₀` stacks) and its members `cands` that satisfy the OOD claim, and when they
are pinned. W1 supplies the decoded Johnson list; the fallback FB-PCS season 1's candidates. -/
structure OpeningIface where
  /-- The candidate stacks of a history. -/
  cands : List Ev → Set Stack
  /-- The history is pinned: the OOD answer is in it and the candidates are at most one. -/
  pinned : List Ev → Prop
  /-- Pinned histories stay pinned. -/
  pinned_append : ∀ h l, pinned h → pinned (h ++ l)
  /-- On a pinned history there is at most one candidate. -/
  pinned_sub : ∀ h, pinned h → (cands h).Subsingleton
  /-- The level-0 list of a history. -/
  ball : List Ev → Set Stack
  /-- The list bound. -/
  L₀ : ℕ
  /-- On a pinned history the list is finite and at most `L₀`. -/
  ball_card : ∀ h, pinned h → (ball h).Finite ∧ (ball h).ncard ≤ L₀
  /-- The list is fixed once pinned. -/
  ball_append : ∀ h l, pinned h → ball (h ++ l) = ball h
  /-- The candidates are fixed once pinned. -/
  cands_append : ∀ h l, pinned h → cands (h ++ l) = cands h
  /-- The candidates are list members. -/
  cands_sub : ∀ h, cands h ⊆ ball h

/-- **Claim 0 ties the candidates to the list**: a list member satisfies `c₀` exactly when it is a
candidate. -/
def OpeningIface.Tied (I : OpeningIface) (μ : ℕ) (c₀ : StackClaim6) (h : List Ev) : Prop :=
  ∀ q ∈ I.ball h, (c₀.Holds μ q ↔ q ∈ I.cands h)

/-- **Doom moves from the candidates to the list** with claim 0 (the bridge before §6.5). -/
theorem OpeningIface.doomed_ball {I : OpeningIface} {μ : ℕ} {c₀ : StackClaim6} {h : List Ev}
    {A : Stack → Prop} (ht : I.Tied μ c₀ h) (hd : Doomed I.cands A h) :
    Doomed I.ball (fun q => c₀.Holds μ q ∧ A q) h :=
  fun q hq ⟨h0, ha⟩ => hd q ((ht q hq).1 h0) ha

/-- `Tied` survives extension of a pinned history. -/
theorem OpeningIface.Tied.append {I : OpeningIface} {μ : ℕ} {c₀ : StackClaim6} {h : List Ev}
    (l : List Ev) (hp : I.pinned h) (ht : I.Tied μ c₀ h) : I.Tied μ c₀ (h ++ l) := by
  intro q hq
  rw [I.cands_append h l hp]
  exact ht q (by rwa [I.ball_append h l hp] at hq)

/-- **A phase commits nothing** (so frames carry the commitment count across it). -/
def Stmt.noCommit {α : Type} (p : VerifierProgram α) : Prop :=
  ∀ h₀ l, p.Reach h₀ l → commits l = []

/-- **The stacked opening's specification**: for a claim with a multiaffine weight (W1 F-3), from
a history with one commitment where no list member satisfies the claim, to rejection, each
group's escape at most `εI`. -/
def OpeningIface.stackedSpec (I : OpeningIface) (μ : ℕ)
    (whirProg : StackClaim6 → VerifierProgram Bool) : Prop :=
  ∀ cl, cl.Multiaffine μ → Nonempty (Spec (whirProg cl)
    (fun h => (commits h).length = 1 ∧ Doomed I.ball (fun q => cl.Holds μ q) h)
    (fun b _ => b = false) εI 0 0)

/-- **T3a `commitSpec6`**: the commitment and its OOD sample (§6.1, returning claim 0 `c₀`) reach,
from the empty history, a pinned history with one commitment on which `c₀` ties the candidates to
the list, the OOD group's escape (the pin's collision) at most `εI`. -/
def Stmt.commitSpec6 (I : Shape → OpeningIface)
    (commitProg : Shape → VerifierProgram StackClaim6) : Prop :=
  ∀ sh, Nonempty (Spec (commitProg sh) (fun h => h = [])
    (fun c₀ h => (I sh).pinned h ∧ (commits h).length = 1 ∧ (I sh).Tied sh.M c₀ h) εI 0 0)

/-- **T3 `openSpec6`**: the opening of §6.6 meets `stackedSpec` at every shape. -/
def Stmt.openSpec6 (I : Shape → OpeningIface)
    (whirProg : Shape → StackClaim6 → VerifierProgram Bool) : Prop :=
  ∀ sh, (I sh).stackedSpec sh.M (whirProg sh)

/-- A shape has `P18`'s opening constants (stack, lanes, levels, final polynomial, tail, grinds, level-0 list bound;
C3: `L₀`, so that W1's seam `I18` meets `PhaseSpecs.listL`). -/
def openKey (sh : Shape) : Bool :=
  decide (sh.M = P18.M) && decide (sh.lanes = P18.lanes) && decide (sh.levels = P18.levels) &&
    decide (sh.finalLen = P18.finalLen) && decide (sh.tail = P18.tail) && decide (sh.gr = P18.gr) &&
    decide (sh.L₀ = P18.L₀)

/-- **The opening program at every shape** from `P18`'s (W1 F-4): `whirP18` on shapes with
`P18`'s opening constants, rejection elsewhere. -/
def whirAt (whirP18 : StackClaim6 → VerifierProgram Bool) (sh : Shape) :
    StackClaim6 → VerifierProgram Bool :=
  fun cl => if openKey sh = true then whirP18 cl else .fail

/-- `openSpec6` for `whirAt` reduces to the shapes with `P18`'s opening constants (rejection meets
every specification). -/
theorem Stmt.openSpec6_whirAt {I : Shape → OpeningIface}
    {whirP18 : StackClaim6 → VerifierProgram Bool}
    (h : ∀ sh, openKey sh = true → (I sh).stackedSpec sh.M whirP18) :
    Stmt.openSpec6 I (whirAt whirP18) := by
  intro sh cl hcl
  by_cases hk : openKey sh = true
  · have e : whirAt whirP18 sh cl = whirP18 cl := ite_eq_left hk
    rw [e]
    exact h sh hk cl hcl
  · have e : whirAt whirP18 sh cl = .fail := ite_eq_right hk
    rw [e]
    exact ⟨Spec.fail⟩

end Lvm6
