-- lvm6 EXF phase 2 (F-EXG-2): the fill block (at `P17` since PORT17 X2). After the front, `fillIR` copies the
-- round challenges (chain answers) and the high parts and final scalars (proof words on the tape) into EXG's `FrontA`
-- cells `FDep` in `[2^25, 2^26)`; `fill_front`/`frontIn` (in `Lvm6XFrontIn`): the heap then holds them as the
-- opening's runs return them. PORT17 X2: the deployed names are `Lvm6XFill17`'s `P17` fill (`F17`, `N17`,
-- `reqs17`, `fillTab17`), each tied by a proved equation; the facts are `fill17_ok`'s. New.
import Lvm6XFill
import Lvm6XFill17

/-!
# The fill block (at `P17`)

* **`FDep`**: the `FrontA` cells (`F17`): `ch i k = 2^25 + 32i + 4k` (`α` at `+0`, `β` at `+2`),
  `hi i = 2^25 + 256 + 16i`, `s = 2^25 + 512`.
* **`ND`** (`= N17 = 4983`, the opening's first event), **`tlD i`** (tail `i`'s events, `tails17`), **`baseD i`**
  (level `i`'s offset in the opening). **`reqs`**: the requests `(event index, cell)`: round `k` of level `i` draws
  `α`, `β` at events `ND + baseD i + 7k + 5, + 6`; tail `i`'s high part `k` is event `ND + baseD i + 7 rndD i +
  k`; the final scalar `k < 8` is event `ND + baseD 4 + 28 + k`. **`fillTab`**: two word copies a request, from
  the chain answer (`srcsD`'s `.smp p`) or from the tape (`.rd off 16`). **`fillIR := cpsIR fillTab`**.
* **The ties to `Lvm6XFill17`**: `baseD_eq : baseD = fg17.base`, `reqs_eq : reqs = reqs17`,
  `fillTab_eq : fillTab = fillTab17`, `fillIR_eq : fillIR = fillIR17`, `reqOK_eq` (`srcOKAt` at `pz6` and
  the chain's 1,055 targets).
* **`fill_ok`** (`fill17_ok` through the ties): the copies' static facts, the requests' sources, the counts
  (**140** copies). Kernel-cheap: `Lvm6XFill17` evaluates `srcs17` once (KDX's memo pattern).
-/

set_option autoImplicit false

namespace Lvm6.X

open RecursionFast Lvm Lvm.X Lvm.FS Lvm6.Whir
open LeanVM.Protocol.Compile (Ev VerifierProgram commits)
open LeanVM.Parameters (E E2 e2OfE)

/-! ## The cells and the requests -/

/-- **The cells the front fills** (EXG's `FrontA`), in `[2^25, 2^26)`: `F17`. -/
def FDep : FrontA := F17

/-- The events of tail `i` (`tails17`: `(nh, ht, ko, kq)` = `(6, 19, 17, 18)`, `(4, 18, 13, 7)`, `(4, 17, 9, 3)`,
`(4, 16, 5, 2)`). -/
def tlD (i : ℕ) : ℕ := (tails17 i).length

/-- Level `i`'s first event in the opening's log. -/
def baseD : ℕ → ℕ
  | 0 => 0
  | i + 1 => baseD i + 7 * rndD i + tlD i

/-- The opening's first event in the history (`N17`). -/
def ND : ℕ := N17

/-- **The requests**: `(event index, cell)`. -/
def reqs : List (ℕ × ℕ) :=
  ((List.range 5).flatMap fun i ↦ (List.range (rndD i)).flatMap fun k ↦
    [(ND + baseD i + 7 * k + 5, FDep.ch i k), (ND + baseD i + 7 * k + 6, FDep.ch i k + 2)]) ++
  ((List.range 4).flatMap fun i ↦ (List.range (rndD i)).map fun k ↦
    (ND + baseD i + 7 * rndD i + k, FDep.hi i + 2 * k)) ++
  ((List.range 8).map fun k ↦ (ND + baseD 4 + 7 * 4 + k, FDep.s + 2 * k))

/-- **The copies.** -/
def fillTab : List (Bool × ℕ × ℕ) := reqs.flatMap fun r ↦ cpOf (srcsD.getD r.1 default) r.2

/-- **The fill block.** -/
def fillIR : XIR := cpsIR fillTab

/-- A request's source: a draw inside the chain, or a 16-byte read of π, word-aligned. -/
def reqOK (r : ℕ × ℕ) : Bool :=
  match srcsD.getD r.1 default with
  | .smp p => decide (p < nCh6 P17)
  | .rd off w => decide (w = 16) && decide (off % 8 = 0) && decide (off + 16 ≤ pz6)
  | _ => false

/-! ## The ties to `Lvm6XFill17` -/

theorem baseD_eq : baseD = fg17.base := by
  funext i
  induction i with
  | zero => rfl
  | succ i ih => rw [baseD, FillGeo.base, ih]; rfl

theorem ND_eq : ND = 4983 := srcs17_facts.1

/-- `reqs17`'s fields in `reqs`'s spelling, rewritten one by one: a bare `rfl` makes the elaborator evaluate
`N17 = |ops| − |ops17|` (Nat offset unification) and exceed the recursion depth. -/
theorem reqs_eq : reqs = reqs17 := by
  have hN : fg17.N = ND := rfl
  have hr : fg17.rnd = rndD := rfl
  have hn : fg17.nFin = 8 := rfl
  have hr4 : rndD 4 = 4 := rfl
  have hF : F17 = FDep := rfl
  rw [reqs17, reqsOf, ← baseD_eq, hN, hr, hn, hr4, hF]
  rfl

theorem fillTab_eq : fillTab = fillTab17 := by
  rw [fillTab, reqs_eq, fillTab17, fillTabOf, reqs17]
  rfl

theorem fillIR_eq : fillIR = fillIR17 := by
  rw [fillIR, fillTab_eq]
  unfold fillIR17
  rfl

theorem reqOK_eq : reqOK = fun r => srcOKAt xg17.pz (nCh6 P17) (srcs17.getD r.1 default) := by
  funext r
  unfold reqOK srcOKAt
  rfl

/-! ## The static facts -/

/-- **The fill block's static facts** (`fill17_ok` through the ties). -/
theorem fill_ok : fillTab.all (cpOK 33554432 67108864) = true ∧ (fillTab.map fun e ↦ e.2.2).Nodup ∧
    reqs.all reqOK = true ∧ srcsD.length = (opsOf P17.levs (sched6 P17)).length ∧
    0 < opsD.length ∧ opsD.length ≤ (opsOf P17.levs (sched6 P17)).length ∧ fillTab.length = 140 := by
  rw [fillTab_eq, reqs_eq, reqOK_eq]
  exact fill17_ok

theorem wf_fillIR : WF fillIR := by unfold fillIR; generalize fillTab = tab; exact wf_cpsIR tab
theorem noLoopT_fillIR : NoLoopT fillIR := by unfold fillIR; generalize fillTab = tab; exact noLoopT_cpsIR tab
theorem outs_fillIR (t : ℕ) : outs fillIR t = 0 := by unfold fillIR; exact outs_cpsIR t fillTab
theorem hasOut_fillIR : hasOut fillIR = false := by unfold fillIR; exact hasOut_cpsIR fillTab

/-- **The fill block's cost**: at most `2,944` steps. -/
theorem cost_fillIR (t : ℕ) : cost fillIR t ≤ 2944 := by
  have h := cost_cpsIR t fillTab
  rw [fill_ok.2.2.2.2.2.2] at h
  unfold fillIR
  exact h

/-- **The fill block's size**: at most `2,944` statements. -/
theorem sizeIR_fillIR : sizeIR fillIR ≤ 2944 := by
  have h := sizeIR_cpsIR fillTab
  rw [fill_ok.2.2.2.2.2.2] at h
  unfold fillIR
  exact h

end Lvm6.X
