-- New for lvm6 (WP CD). The frozen statements of the child-verification circuit's typed family:
-- the typed phases, the mini-bus and the `Φ_Q` accumulator re-executed in the node circuit, the
-- `STREAM` layout and the two windows (`docs/lvm6/stages/CD-circuit.md`). CB's HAR pattern
-- (`Lvm6QKStmt`: `layItems`, `EvMatch`, `PowLay`) on Y1's programs (`Lvm6TyProg`, `Lvm6MbProg`).
import Lvm6QKRun
import Lvm6QFormat
import Lvm6TyProg
import Lvm6QStmt
import Lvm6Stmt

/-!
# CD's frozen statements

**The `V` side is Y1's DSL programs** (FORMAT6 v2.3 §6.4): `zeroProgE`, `wireProgE`, `relayProgE`,
`accProgE` (the phases of `typedProgE`) and `lvmBusProgG miniDepth` (the mini-bus of
`miniBusLProg6`). The node circuit re-executes the child's run of them from the stream lanes.

* **`STREAM` and the windows** (FORMAT6 §T, §6.4 claims): `STREAM` is slot 33 (`recSlot`), stream
  word `w` is stack word `w + 2^19·33` (`streamIdx`), column stride 1 (contiguous); the trace from
  word `tB = 0`, `σ'` from `sB = 2^18`, `σ_leaf` from `sLB = sB + 597`, **both in `readSig`'s
  order**; slot 34 is a free zero lane. `C_rec`'s window is slot 33 (`recWin = ⟨19, 33·2^19⟩`),
  `C_main`'s the whole stack (`mainWin = ⟨25, 0⟩`): `mainOf q`, `recOf q`, `layD = ⟨25, 19⟩`.
  `StreamRegs6 Ti`: the instance reads `S_flat` as the identity on slot 33 and `σ` (both
  signatures) at `sB` (so the relayout kernel and the two `C_rec` claims factor, no carry automaton).
* **Item lists** (`zeroItems` … `mbItems`, FORMAT6 §6.4a, §6.4b): 84 draws / 3,488 B and 53 draws /
  3,448 B (`ty_counts`, `mb_counts`, kernel).
* **HARs** (`HarIn`: CB's `Har` for a program that reads input cells): `ZeroHarStmt` (CD-1),
  `WireHarStmt` (CD-2, `PUB` from cells, no `QLT` region), `RelayHarStmt` (CD-3), `AccHarStmt`
  (CD-4: under the promise that `Φ_Q` holds at the node's own `accIn` cells, `accProgE` runs, and the
  gadget ties the child's `accOut` to them), `MbHarStmt` (CD-5).
* **The accumulator rule** (FORMAT6 v2 §2.1, §T; season 1's `LvmE2TAcc`/A23, RV3): `accIn0` (honest
  at `b = 0`), `accIn0_ok`; `accOut6`; **`acc_child_of_tie`**: `AccOkE` at the node's `accIn` and
  the tie give the child's own last check in `V_S` `Φ_Q(accOut) = accOut.y`.
* **`TyRest6`**: CD's conjunct of `node6`'s `rest`: the typed relation on `(mainOf q, recOf q)` with
  the node's `PUB` words and `AccOkE` at its `accIn`. **`PhiBudget`** (CD-8 **v4**, WP NODE3) is in the leaf
  module `Lvm6QDBudget` (INT3: v3 imported `Lvm6PhiClsS` here and closed an import cycle).

Like CB's, every HAR is vacuous for a generator whose gated assertions cannot hold (`HsA`
quantifies over memories where they hold): the honest witness's rows (R3's KAT) close that gap.
`C_main`'s window is the whole stack, so it overlaps `STREAM` (both read the same `q`); the `σ`
region is `σ' ‖ σ_leaf ‖` zero padding. When composing (CD's `node6` part): `AccHarStmt`'s `Q`
is the node's `Ti.Q` and `own`/`ownY` are the cells of the node's `accIn` words; `WireHarStmt`'s
`pubC y` is the cell of `PUB` lane `y − pubBase Ti` (`pwOf`).

Category A (specification of intent, CD): the constants, `StreamRegs6`, `TyLayOk`, the Rep
relations, `TyRest6` (`PhiBudget`: `Lvm6QDBudget`). The programs are Y1's (frozen there).
-/

set_option autoImplicit false

namespace Lvm6.QD

open LeanVM.Parameters LeanVM.Protocol LeanVM.Protocol.Compile LeanVM.Protocol.Verifier
open Lvm Lvm.Loop Lvm.Loop.Build Lvm.Q2 Lvm.Har Lvm.E2V Lvm.Typed
open Lvm6 (Item rep rnd)
open Lvm6.QK (LEv layItems EvMatch PowLay ev2 kv lk)
open Lvm6.Ty (TInst6 zeroProgE wireProgE relayProgE accProgE lineE hEvalE AccOkE PhiQE TGoodE
  phiVarsE relayRounds gTau gZero gGamma gWire gKappa gT entsE)
open Lvm6.Mb (LBusG lvmBusProgG miniDepth gAB gLam gRd gY gYl)

/-! ## `STREAM` and the two windows (FORMAT6 §T; frozen here) -/

/-- The stack slot of `STREAM` (`C_rec`'s window). -/
def recSlot : ℕ := 33

/-- The stream word of the trace's first byte (the `0x54` tag). -/
def tB : ℕ := 0

/-- The stream word of `σ'` (597 words, `readSig`'s order). -/
def sB : ℕ := 2 ^ 18

/-- The stream word of `σ_leaf` (597 words, `readSig`'s order; adjacent to `σ'`). -/
def sLB : ℕ := sB + 597

/-- `log₂` of the `σ` region (`σ'` and `σ_leaf`: 1,194 ≤ 2^11 words). -/
def sigLog : ℕ := 11

/-- **The stack word of stream word `w`** (column stride 1). -/
def streamIdx (w : ℕ) : ℕ := w + 2 ^ 19 * recSlot

/-- **`C_rec`'s window**: slot 33, a block of `2^19` words at stack word `33·2^19` (`Placement.index`
is a word offset; its selector is `index >>> 19 = 33`, bits `1,0,0,0,0,1`). -/
def recWin : LeanVM.Protocol.Verifier.Placement := ⟨19, 2 ^ 19 * recSlot⟩

/-- **`C_main`'s window**: the whole stack (no selector). -/
def mainWin : LeanVM.Protocol.Verifier.Placement := ⟨25, 0⟩

/-- The two windows' sizes as season 1's `Lay`. -/
def layD : Lvm.M3.Lay := ⟨25, 19⟩

/-- `C_main` of a stack: the whole stack. -/
def mainOf (q : Stack) : LeanVM.Protocol.Column 25 := ⟨Vector.ofFn fun x ↦ q x.val⟩

/-- `C_rec` of a stack: `STREAM`'s slot. -/
def recOf (q : Stack) : LeanVM.Protocol.Column 19 := ⟨Vector.ofFn fun x ↦ q (streamIdx x.val)⟩

/-- CA's `STREAM` map at the season's shape: `σ'` at stream word `sB` (`sb` is the circuit cell of
stream word 0, the generator's). -/
def streamMap6 (sb : ℕ) : Lvm6.Q.StreamMap6 := ⟨sb, sB⟩

/-- **The trace fits below `σ'`** (static, kernel): the hashed stream of the plan, in words. -/
theorem traceFits_P18 : (Lvm6.Q.hashedLen6 (Lvm6.Q.planOf P18) + 7) / 8 ≤ sB := by decide +kernel

/-! ## The instance's stream regions -/

/-- **The instance reads the stream as frozen here**: one `S_flat` region of `2^19` words at `bs`,
read as the identity on `C_rec` (`sflatW (bs + p) = p`); one `σ` region of `2^11` words at `bg`,
`sigmaW (bg + j) = sB + j`; no other region of either source. -/
def StreamRegs6 (Ti : TInst6) : Prop :=
  ∃ bs bg, Ti.lay.yregs.filter (fun r ↦ r.src == .sflat) = [⟨bs, relayRounds, .sflat⟩] ∧
    Ti.lay.yregs.filter (fun r ↦ r.src == .sigma) = [⟨bg, sigLog, .sigma⟩] ∧
    (∀ p < 2 ^ relayRounds, Ti.sflatW (bs + p) = p) ∧ (∀ j < 2 ^ sigLog, Ti.sigmaW (bg + j) = sB + j)

/-- The base of the (first) `PUB` region. -/
def pubBase (Ti : TInst6) : ℕ := ((Ti.lay.yregs.find? fun r ↦ r.src == .pub).map (·.base)).getD 0

/-- **The layout conditions the typed gadgets take** (season 1's B1-Q assumptions, v6 form): the
stream regions above; one `PUB` region, of `2^10` words; no `QLT` region (its cells are constants
of `Φ_Q`). -/
def TyLayOk (Ti : TInst6) : Prop :=
  StreamRegs6 Ti ∧ Ti.lay.yregs.filter (fun r ↦ r.src == .pub) = [⟨pubBase Ti, 10, .pub⟩] ∧
    ∀ r ∈ Ti.lay.yregs, r.src ≠ .qlt

/-- The public word `y` of a header's bytes `H` (lane `y − pubBase`, little-endian). -/
def pwOf (Ti : TInst6) (H : List UInt8) (y : ℕ) : Lvm.FK :=
  Lvm.QSig.w64 (Lvm6.Q.le8 H (8 * (y - pubBase Ti))).toUInt64

/-! ## The item lists (FORMAT6 v2.3 §6.4) -/

/-- §6.4a rows 1–3: `τ`, 20 equality-mode rounds, `A, B, C`. -/
def zeroItems : List Item := rep xVars [.G gTau] ++ rep xVars (rnd 2 gZero) ++ [.E 3]

/-- §6.4a rows 4–7: `γ`, 21 plain rounds, matrix and region values. -/
def wireItems : List Item := [.G gGamma] ++ rep yVars (rnd 2 gWire) ++ [.E 4, .E 4]

/-- §6.4a rows 8–9: 19 plain rounds, `v_R`. -/
def relayItems : List Item := rep relayRounds (rnd 2 gWire) ++ [.E 1]

/-- §6.4a rows 10–12: `κ`, `h`, `t`. -/
def accItems : List Item := rep 2 [.G gKappa] ++ [.E (phiVarsE + 1), .G gT]

/-- §6.4a. -/
def tyItems : List Item := zeroItems ++ wireItems ++ relayItems ++ accItems

/-- §6.4b row 15, step `k` (`2k` equality-mode rounds of count 5; the last step's `y` at `gYl`). -/
def mbStep (k : ℕ) : List Item :=
  [.G gLam] ++ rep (2 * k) (rnd 4 gRd) ++ [.E 4, .E 4, .E 4, .G (if k = 5 then gYl else gY), .D 1]

/-- §6.4b. -/
def mbItems : List Item := [.G gAB, .D 4, .E 2] ++ (List.range 6).flatMap mbStep

/-- Draws of an item list (`G` one, `D k` `k`). -/
def drawsOf (its : List Item) : ℕ :=
  (its.map fun | .G _ => 1 | .D k => k | _ => 0).sum

/-- Bytes of an item list (`E` 16, `K` 8, a nonce 8). -/
def bytesOf (its : List Item) : ℕ :=
  (its.map fun | .E k => 16 * k | .K k => 8 * k | .G _ => 8 | _ => 0).sum

/-- **§6.4a's counts**: 84 draws, 3,488 bytes. -/
theorem ty_counts : drawsOf tyItems = 84 ∧ bytesOf tyItems = 3488 := by decide +kernel

/-- **§6.4b's counts**: 53 draws, 3,448 bytes. -/
theorem mb_counts : drawsOf mbItems = 53 ∧ bytesOf mbItems = 3448 := by decide +kernel

/-! ## A HAR whose program reads input cells -/

/-- **`HarIn`** (CB's `Har` with the program a function of the memory: its inputs are cells). -/
def HarIn {α β : Type} (gate : Cell) (g : BM α) (prog : Mem → VerifierProgram β) (lay : List LEv)
    (Rep : Mem → α → β → Prop) : Prop :=
  ∀ (c : Ctx) (M : Mem), gate.val M = 1 → HsA c M g fun o ↦
    PowLay M lay → ∀ evs, EvMatch M lay evs → ∃ out, (prog M).after evs = some (.ret out) ∧ Rep M o out

/-! ## Outputs -/

/-- The zerocheck gadget's outputs: `r_x`, `A, B, C`. -/
structure ZeroOutC where
  rx : List C2
  abc : List C2

/-- The wiring gadget's outputs: `r_y`, the matrix values, the region values. -/
structure WireOutC where
  ry : List C2
  vs : List C2
  rv : List C2

/-- The relayout gadget's outputs: `r`, `v_R`. -/
structure RelayOutC where
  rr : List C2
  vR : C2

/-- The mini-bus gadget's outputs: `α`, `β`, the point, the three values. -/
structure MbOutC where
  alphas : List C2
  beta : C2
  point : List C2
  values : List C2

def ZeroRep (M : Mem) (o : ZeroOutC) (out : List E2 × List E2) : Prop :=
  out.1 = o.rx.map (ev2 M) ∧ out.2 = o.abc.map (ev2 M)

def WireRep (M : Mem) (o : WireOutC) (out : List E2 × List E2 × List E2) : Prop :=
  out.1 = o.ry.map (ev2 M) ∧ out.2.1 = o.vs.map (ev2 M) ∧ out.2.2 = o.rv.map (ev2 M)

def RelayRep (M : Mem) (o : RelayOutC) (out : List E2 × E2) : Prop :=
  out.1 = o.rr.map (ev2 M) ∧ out.2 = ev2 M o.vR

def MbRep (M : Mem) (o : MbOutC) (out : LBusG) : Prop :=
  out.alphas = o.alphas.map (ev2 M) ∧ out.beta = ev2 M o.beta ∧ out.point = o.point.map (ev2 M) ∧
    out.values = o.values.map (ev2 M)

/-! ## The accumulator (A23 at `Φ_Q`, 43 variables) -/

/-- **The child's `accOut`** from its `accIn`, `κ ‖ r_x ‖ r_y`, `h` and `t` (`V_S` computes it,
never sent; FORMAT6 §6.4a: `accOut = (line(t), h(t))`). -/
def accOut6 (ain : List E2 × E2) (κ rxy hs : List E2) (t : E2) : List E2 × E2 :=
  (lineE ain.1 (κ ++ rxy) t, hEvalE hs t)

/-- **The honest `accIn` at `b = 0`** (FORMAT6 §2.1): `(0^v, Φ_Q(0^v))`. -/
noncomputable def accIn0 (Ti : TInst6) : List E2 × E2 :=
  (List.replicate phiVarsE 0, PhiQE Ti.Q Ti.lay (List.replicate phiVarsE 0))

/-- The honest `accIn` at `b = 0` holds. -/
theorem accIn0_ok (Ti : TInst6) : AccOkE Ti (accIn0 Ti) := rfl

/-- **The accumulator argument at a node** (RV3): if `Φ_Q` holds at the node's `accIn` and the
circuit tied it to the child's `accOut`, the child's own last check in `V_S` holds. -/
theorem acc_child_of_tie (Ti : TInst6) {accIn accOut : List E2 × E2} (hok : AccOkE Ti accIn)
    (htie : accOut = accIn) : PhiQE Ti.Q Ti.lay accOut.1 = accOut.2 := htie ▸ hok

/-! ## The frozen HAR statements -/

/-- **CD-1, the zerocheck** (statement): `G a gate` re-executes `zeroProgE` on the lanes laid out by
`zeroItems` from `a`. -/
def ZeroHarStmt (G : ℕ → Cell → BM ZeroOutC) : Prop :=
  ∀ (a : ℕ) (gate : Cell), Lvm6.QK.Har gate (G a gate) zeroProgE (layItems zeroItems a) ZeroRep

/-- **CD-2, the wiring** (statement): `G Ti pubC v a gate` re-executes `wireProgE Ti pw v` where the
child's public words are cells (`pw y` = cell `pubC y`'s word) and `v` the zerocheck's `A, B, C`. -/
def WireHarStmt (G : TInst6 → (ℕ → Cell) → List C2 → ℕ → Cell → BM WireOutC) : Prop :=
  ∀ (Ti : TInst6), Ti.Ok → TyLayOk Ti → ∀ (pubC : ℕ → Cell) (v : List C2), v.length = 3 →
    ∀ (a : ℕ) (gate : Cell),
      HarIn gate (G Ti pubC v a gate) (fun M ↦ wireProgE Ti (fun y ↦ ((pubC y).val M).c₀) (v.map (ev2 M)))
        (layItems wireItems a) WireRep

/-- **CD-3, the relayout** (statement): `G Ti ry vS a gate` re-executes `relayProgE Ti ry vS`. -/
def RelayHarStmt (G : TInst6 → List C2 → C2 → ℕ → Cell → BM RelayOutC) : Prop :=
  ∀ (Ti : TInst6), Ti.Ok → TyLayOk Ti → ∀ (ry : List C2), ry.length = yVars → ∀ (vS : C2) (a : ℕ)
    (gate : Cell),
      HarIn gate (G Ti ry vS a gate) (fun M ↦ relayProgE Ti (ry.map (ev2 M)) (ev2 M vS))
        (layItems relayItems a) RelayRep

/-- **CD-4, A23 and the `accIn` tie** (statement): `G Q lay ain yIn rxy vs own ownY a gate`, with the
child's `accIn` cells `(ain, yIn)` (from the stream), `r_x ‖ r_y`, the four matrix values and the
node's own `accIn` cells `(own, ownY)`: where its rows and gated assertions hold, (i) the child's
`accOut` (`accOut6` on the stream lanes of `κ`, `h`, `t`) **is** the node's `accIn` (the tie), and
(ii) under the promise `Φ_Q(own) = ownY` (the node's `AccOkE`), `accProgE` returns. -/
def AccHarStmt (G : Program → Lay → List C2 → C2 → List C2 → List C2 → List C2 → C2 → ℕ → Cell →
    BM Unit) : Prop :=
  ∀ (Q : Program) (lay : Lay) (ain : List C2) (yIn : C2) (rxy vs own : List C2) (ownY : C2),
    ain.length = phiVarsE → rxy.length = xVars + yVars → vs.length = 4 → own.length = phiVarsE →
    ∀ (a : ℕ) (gate : Cell) (c : Ctx) (M : Mem), gate.val M = 1 →
      HsA c M (G Q lay ain yIn rxy vs own ownY a gate) fun _ ↦
        accOut6 (ain.map (ev2 M), ev2 M yIn) (Lvm6.QK.gdraws M a 2) (rxy.map (ev2 M))
            (Lvm6.QK.scal M (a + 20) (phiVarsE + 1)) (ev2 M (ld2 (a + 20 + 2 * (phiVarsE + 1) + 1))) =
          (own.map (ev2 M), ev2 M ownY) ∧
        (PhiQE Q lay (own.map (ev2 M)) = ev2 M ownY →
          PowLay M (layItems accItems a) → ∀ evs, EvMatch M (layItems accItems a) evs →
            (accProgE Q lay (ev2 M yIn) (ain.map (ev2 M)) (rxy.map (ev2 M)) (vs.map (ev2 M))).after evs =
              some (.ret ()))

/-- **CD-5, the mini-bus's GKR walk** (statement): `G a gate` re-executes `lvmBusProgG miniDepth`. -/
def MbHarStmt (G : ℕ → Cell → BM MbOutC) : Prop :=
  ∀ (a : ℕ) (gate : Cell), Lvm6.QK.Har gate (G a gate) (lvmBusProgG miniDepth) (layItems mbItems a) MbRep

/-! ## CD's conjunct of `node6`'s relation -/

/-- **The typed part of the good relation** at a node with header bytes `H` and `accIn`: the typed
relation at `E` on `(mainOf q, recOf q)` with the node's public words, the mini-bus balances
(`TGoodE`), and `Φ_Q` at `accIn` (`AccOkE`). -/
def TyRest6 (Ti : TInst6) (hτ : ∀ t ∈ Ti.mbT, t.τ ≤ layD.μ) (H : List UInt8) (accIn : List E2 × E2)
    (q : Stack) : Prop :=
  TGoodE Ti layD hτ (pwOf Ti H) (mainOf q, recOf q) ∧ AccOkE Ti accIn

end Lvm6.QD
