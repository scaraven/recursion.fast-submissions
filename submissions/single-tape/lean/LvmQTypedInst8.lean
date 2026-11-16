-- New for lvm2 (roll 8 = B1, B1-IX): the B program's instance at `P8` (the test set), apart from `P20`'s
-- (`LvmQTypedInst`) so that the badge, which imports only `P20`'s, does not initialise it. B1-IX: on `P20`'s fast
-- start-up path (B1-IX-S's pattern: one builder run `segs8` shared by `QB8` and the guard, one enumeration of `Φ_Q`'s
-- entries `phi8` for the terms and their entry check, the mini-bus tables `mbT8` shared by `tdata8` and `NT8`). It
-- imports the generic guard (`LvmQTypedGuard`), not `P20`'s instance, so a `P8` process does not initialise `P20`'s.
import LvmQTypedGuard
import LvmQAsmDataB8

set_option autoImplicit false

namespace Lvm.QTyped

open Lvm Lvm.Loop Lvm.Loop.Build Lvm.QAsm Lvm.Typed
open Lvm.M3 (Tab pushLeavesR)

/-! ## `P8` -/

/-- The mini-bus's tables at `P8` (shared by `tdata8` and `NT8`). -/
def mbT8 : List Tab := mbTOf cfg8 frz8
/-- The circuit's static data at `P8` (`tdataOf cfg8 frz8` on the shared tables, `tdata8_eq`). -/
def tdata8 : TData :=
  let ts := mbT8
  ⟨frz8.com, frz8.ks, frz8.sig, frz8.sflat, frz8.pub, frz8.one, none, ts.map Tab.shape,
    (ts.map (·.τ)).foldl max 0, mbFixOf cfg8, log2Ceil (pushLeavesR ts)⟩
/-- The B program's segments at `P8` (one run of the builder, shared by `QB8` and the guard's one pass). -/
def segs8 : List Seg := (qprogBF cfg8 tdata8 ⟨nK cfg8, 0⟩).2
/-- **The B program at `P8`** (`toProgram` on `segs8`). -/
def QB8 : Program :=
  let bs := group segs8
  ⟨nK cfg8, 0, bs, (List.range bs.length).filter fun b => (bs.getD b default).dims.isEmpty⟩
/-- The typed layout at `P8` on the frozen dense intervals. -/
def layT8 : Typed.Lay := (mkLayD QB8 (specQ cfg8 QB8) dints8).1
/-- `Φ_Q`'s terms at `P8` and their entry check, on one table of the entries (`K.termsChecked`). -/
def phi8 : Array CTerm × Bool := K.termsChecked (K.FLF.ofLay QB8 layT8)
/-- `Φ_Q`'s cache at `P8` (it is `cacheW QB8 layT8`: `cacheT8_eq`). -/
def cacheT8 : PhiCache := cacheOfTerms phi8.1
/-- **V_S's typed instance at `P8`** (`tnatOf cfg8 layT8 frz8 cacheT8` on the shared tables, `NT8_eq`). -/
def NT8 : TypedV.TNat := ⟨nregsOf layT8 frz8, PhiQC cacheT8, mbT8⟩
/-- **The typed static guard at `P8`** (`staticOkTOf` on the shared segments and `phi8`'s entry check:
`staticOkT8_eq`). -/
def staticOkT8 : Bool := staticOkTC cfg8 frz8 segs8 QB8 layT8 cacheT8 NT8 phi8.2

theorem cacheT8_eq : cacheT8 = cacheW QB8 layT8 := by
  unfold cacheT8 cacheOfTerms phi8 cacheW
  rw [K.compileTF_eq, K.termsChecked_fst]

-- (by rewriting only: `simp` or a definitional check on these terms reduces `phi8`'s projections, i.e. runs the
-- computation in the elaborator)
theorem phi8_snd : phi8.2 = K.checkTerms QB8 layT8 phi8.1 := by
  unfold phi8
  exact K.termsChecked_snd QB8 layT8

theorem cacheT8_terms : cacheT8.terms.toArray = phi8.1 := by
  rw [show cacheT8 = cacheOfTerms phi8.1 from rfl]
  exact cacheOfTerms_terms _

theorem phi8_check : phi8.2 = K.checkTerms QB8 layT8 cacheT8.terms.toArray := by
  rw [cacheT8_terms]
  exact phi8_snd

theorem tdata8_eq : tdata8 = tdataOf cfg8 frz8 := rfl
theorem NT8_eq : NT8 = tnatOf cfg8 layT8 frz8 cacheT8 := rfl
theorem QB8_eq : QB8 = QB cfg8 tdata8 := (QB_eqF _ _).symm
theorem layT8_eq : layT8 = layBD cfg8 tdata8 dints8 := by rw [layBD, ← QB8_eq]; rfl
theorem staticOkT8_eq : staticOkT8 = staticOkTOf cfg8 tdata8 frz8 QB8 layT8 cacheT8 NT8 := by
  unfold staticOkT8 staticOkTOf staticOkTS
  rw [phi8_check, K.checkTermsF_eq, segs8]

theorem staticFactsT8 (h : staticOkT8 = true) :
    StaticFactsT cfg8 tdata8 frz8 QB8 layT8 cacheT8 NT8 :=
  staticFactsTC QB8_eq rfl phi8_check h

end Lvm.QTyped
