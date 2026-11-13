-- New for lvm2 (roll 8 = B1, B1-IX): the B program at `P20` and `P8` on its frozen data (`LvmQAsmDataB20`/`B8`, the
-- `qasm genb` fixpoint), V_S's typed instances, and the typed path's static guard (A24, as CR-X's `staticOkB`).
import LvmQAsmDataB20
import LvmQTypedGuard

/-!
# The B program's instances and the typed static guard

* **The instances** (closed constants: computed once per process): `tdata20` (the circuit's static data at the
  frozen placements), `QB20` (the B program, built with V-PERF's linear-time phases 4–7 on `segs20`, `QB20_eq`),
  `layT20` (the typed layout on the frozen dense intervals: `layBD`, `layT20_eq`), `cacheT20` (`Φ_Q`'s cache:
  `cacheT20_eq : cacheT20 = cacheW QB20 layT20`; its terms and their entry check `phi20` read one table of the
  entries, B1-IX-S), `NT20` (V_S's `TNat`, `NT20_eq`). `P8`'s are in `LvmQTypedInst8` (not in the badge's import closure: closed constants are
  initialised at start-up by every executable that imports them).
* **`staticOkT20`** (A24): the program check (QL's one pass, `toProgram_wf`), `Lay.okB`, `PhiCache.okB` (the class
  and cover checks, ≈ 3.7·10^6 entry comparisons), `TNat.okB` and `layOk`, the mini-bus's record (`fitsMiniB`),
  the layout's fit of the read tables (`mbFitB`), QLT's constants (`lay.cst = qltCst`), the cell bound. Natively,
  once per process; `staticFactsT20` turns it into the facts' consumers' forms (`StaticFactsT`).
* **Kernel facts**: `capBlocksOk` at `P20` and `P8`; the typed phases end where the tape starts (`typedEnd`);
  `accVars = phiVarsN`.

**Where wave L reads them.** `typed_sound`'s `Inputs` obligation needs QLT's input cells to be the layout's
constants: `StaticFactsT.cst : layT20.cst = qltCst cfg20`, for L-D's `NodeSound` on `GoodT` (with `hwf`, `hlay`,
`hinj` the same structure's `wf`, `hlay`, `inj`); `PhiQC_eq`'s `hc` is `StaticFactsT.cache` (rewritten by
`cacheT20_eq`); the mini-bus's
`MbFit` is `mbFitB`'s (`StaticFactsT.mbFit`).
-/

set_option autoImplicit false

namespace Lvm.QTyped

open Lvm Lvm.Loop Lvm.Loop.Build Lvm.QAsm Lvm.Typed
open Lvm.M3 (Tab pushLeavesR)

/-! ## `P20` -/

/-- The mini-bus's tables at `P20` (shared by `tdata20` and `NT20`). -/
def mbT20 : List Tab := mbTOf cfg20 frz20
/-- The circuit's static data at `P20` (`tdataOf cfg20 frz20` on the shared tables, `tdata20_eq`). -/
def tdata20 : TData :=
  let ts := mbT20
  ⟨frz20.com, frz20.ks, frz20.sig, frz20.sflat, frz20.pub, frz20.one, none, ts.map Tab.shape,
    (ts.map (·.τ)).foldl max 0, mbFixOf cfg20, log2Ceil (pushLeavesR ts)⟩
/-- The B program's segments at `P20` (one run of the builder, shared by `QB20` and the guard's one pass). -/
def segs20 : List Seg := (qprogBF cfg20 tdata20 ⟨nK cfg20, 0⟩).2
/-- **The B program at `P20`** (`toProgram` on `segs20`). -/
def QB20 : Program :=
  let bs := group segs20
  ⟨nK cfg20, 0, bs, (List.range bs.length).filter fun b => (bs.getD b default).dims.isEmpty⟩
/-- The typed layout at `P20` on the frozen dense intervals. -/
def layT20 : Typed.Lay := (mkLayD QB20 (specQ cfg20 QB20) dints20).1
/-- `Φ_Q`'s terms at `P20` and their entry check, on one table of the entries (B1-IX-S: `K.termsChecked`, one
enumeration for both). -/
def phi20 : Array CTerm × Bool := K.termsChecked (K.FLF.ofLay QB20 layT20)
/-- `Φ_Q`'s cache at `P20` (it is `cacheW QB20 layT20`: `cacheT20_eq`). -/
def cacheT20 : PhiCache := cacheOfTerms phi20.1
/-- **V_S's typed instance at `P20`** (`tnatOf cfg20 layT20 frz20 cacheT20` on the shared tables, `NT20_eq`). -/
def NT20 : TypedV.TNat := ⟨nregsOf layT20 frz20, PhiQC cacheT20, mbT20⟩
/-- **The typed static guard at `P20`** (`staticOkTOf` on the shared segments and `phi20`'s entry check:
`staticOkT20_eq`). -/
def staticOkT20 : Bool := staticOkTC cfg20 frz20 segs20 QB20 layT20 cacheT20 NT20 phi20.2

theorem cacheT20_eq : cacheT20 = cacheW QB20 layT20 := by
  unfold cacheT20 cacheOfTerms phi20 cacheW
  rw [K.compileTF_eq, K.termsChecked_fst]

-- (by rewriting only: `simp` or a definitional check on these terms reduces `phi20`'s projections, i.e. runs the
-- computation in the elaborator)
theorem phi20_snd : phi20.2 = K.checkTerms QB20 layT20 phi20.1 := by
  unfold phi20
  exact K.termsChecked_snd QB20 layT20

theorem cacheT20_terms : cacheT20.terms.toArray = phi20.1 := by
  rw [show cacheT20 = cacheOfTerms phi20.1 from rfl]
  exact cacheOfTerms_terms _

theorem phi20_check : phi20.2 = K.checkTerms QB20 layT20 cacheT20.terms.toArray := by
  rw [cacheT20_terms]
  exact phi20_snd

theorem tdata20_eq : tdata20 = tdataOf cfg20 frz20 := rfl
theorem NT20_eq : NT20 = tnatOf cfg20 layT20 frz20 cacheT20 := rfl
theorem QB20_eq : QB20 = QB cfg20 tdata20 := (QB_eqF _ _).symm
theorem layT20_eq : layT20 = layBD cfg20 tdata20 dints20 := by rw [layBD, ← QB20_eq]; rfl
theorem staticOkT20_eq : staticOkT20 = staticOkTOf cfg20 tdata20 frz20 QB20 layT20 cacheT20 NT20 := by
  unfold staticOkT20 staticOkTOf staticOkTS
  rw [phi20_check, K.checkTermsF_eq, segs20]

theorem staticFactsT20 (h : staticOkT20 = true) :
    StaticFactsT cfg20 tdata20 frz20 QB20 layT20 cacheT20 NT20 :=
  staticFactsTC QB20_eq rfl phi20_check h

end Lvm.QTyped
