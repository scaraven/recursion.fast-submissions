-- New for lvm2 (roll 8 = B1, L-H): the typed HAR's static checks, as computable `Bool`s for the typed guard (L-W's
-- `staticOkB20`, as roll 7's `okClaims20`/`okZ20`): the B program's claim list is well formed in both shapes, and
-- the circuit's static data `TData` names V_S's regions. Definitions only (the badge's `verify` imports the guard);
-- the soundness lemmas are `tdOk_of` (`LvmQTypedHarB`) and `harChk_sound` (`LvmQTypedHarS`).
import LvmQTypedGuard

/-!
# The typed HAR's static checks

* **`qarithBParts C T o`**: the B program's Q_arith up to its openings (`qarithB`'s text), returning the zero cell
  and the claim lists the openings read: the typed phases' claims on `C_rec` and on `C_main` (`typedClaimsC`), the
  tape's (`tapeClaimsC`), `KS`'s (`kClaimsC`), `KS`'s outputs (`ksOutC`), the `KS` link's (`ksLinkG`). `csB` is
  `qarithB`'s list `cs`.
* **`claimsOkB C r`**: `ClaimsWF` on both commitments' claims (roll 7's `hwr`, `hwm`), every `C_main` claim of the
  static form `ZWF` (`hwz`'s second half), and every claim but the tape's tail-free by its form (`noDRB`, `hwz`'s
  first half).
* **`tdMatchB T N`**: the circuit's regions (`TData`: `com`, `ks`, `σ′`, `S_flat`, `PUB`, the word `1`) are V_S's
  (`TNat.regs` of each source, in order, with the same base, size and target); no `QLT` region.
* **`harChkB C T N`**: both, on the claim list at Q_arith's pointer `p2C C` (phases 4–7 by the fast builder
  `phases47S`, `phases47S_eq`). At `P20`: `harChkB cfg20 tdata20 NT20`.
-/

set_option autoImplicit false

namespace Lvm.QTyped

open Lvm Lvm.Loop Lvm.Loop.Build Lvm.QAsm Lvm.Har

/-- The zero cell and the claim lists of the B program's Q_arith: the typed claims on `C_rec`, on `C_main`, the
tape's, `KS`'s, `KS`'s outputs, the `KS` link's. -/
abbrev PartsB : Type :=
  Cell × List CClaim × List CClaim × List CClaim × List CClaim × List CClaim × List CClaim

/-- **The B program's Q_arith up to the openings** (`qarithB`'s text up to `cs`). -/
def qarithBParts (C : QCfg) (T : TData) (o : P47Out) : BM PartsB := do
  let p := C.p
  let z ← const .E 0 (kc 0)
  let one ← const .E 1 (kc 0)
  let ksB : Placement := ⟨p.ksLog + slotLog, (layout0 p).ks⟩
  let t ← typedG T (pbB C) (typedPos p) z one
  let tc ← typedClaimsC z one T p.nuMain t
  let rgK ← ringGkr (p.ksLog - 4) (Lvm.Har.aLane p 6) z.n
  let clK ← ksLinkG p (Lvm.Har.aLane p 7) z.n one.n
  pure (z, tc.1, tc.2, tapeClaimsC p z.n one.n o, kClaimsC ksB o.kko rgK, ksOutC p o.rk o.vk z.n one.n, clK)

/-- `qarithB`'s claim list `cs` from the parts. -/
def csB (r : PartsB) : List CClaim :=
  r.2.1 ++ r.2.2.1 ++ (r.2.2.2.1 ++ r.2.2.2.2.1) ++ r.2.2.2.2.2.1 ++ r.2.2.2.2.2.2

/-- A claim whose tail is `0` by its form (`LvmQAsmHarMain.noDR`'s text). -/
def noDRB (cc : CClaim) : Bool :=
  match cc.cw with
  | .point blk _ => blk != ⟨22, 0⟩
  | .ring blk _ _ => blk != ⟨CMain.nu20, 0⟩
  | .sum _ _ => true

/-- **The B program's claims are well formed in both shapes**: `ClaimsWF` on each commitment, `ZWF` on `C_main`'s,
every claim off the tape tail-free by its form. -/
def claimsOkB (C : QCfg) (r : PartsB) : Bool :=
  let cs := csB r
  ClaimsWF C.p.nuRec (onCom cs .crec) && ClaimsWF C.p.nuMain (onCom cs .main) &&
    (onCom cs .main).all (Lvm.QShape.ZWF r.1) &&
    (r.2.1 ++ r.2.2.1 ++ r.2.2.2.2.1 ++ r.2.2.2.2.2.1 ++ r.2.2.2.2.2.2).all noDRB

/-- A native region's base, size and target. -/
def nTrip (g : TypedV.NReg) : Nat × Nat × Nat := (g.base, g.log, g.dst)

/-- A circuit region's base, size and target. -/
def tTrip (R : TReg) : Nat × Nat × Nat := (R.base, R.log, R.off)

/-- **The circuit's regions are V_S's**: per source, the same regions in the same order; one `S_flat` region of
`2^19` words from position 0, one `PUB` region of `2^10` lanes from lane 0, one word `1`; no `QLT` region. -/
def tdMatchB (T : TData) (N : TypedV.TNat) : Bool :=
  (N.regsOf .com).map nTrip == T.com.map tTrip && (N.regsOf .ks).map nTrip == T.ks.map tTrip &&
    (N.regsOf .sigma).map nTrip == T.sig.map tTrip &&
    (N.regsOf .sflat).map nTrip == [(T.sflat, 19, 0)] && (N.regsOf .pub).map nTrip == [(T.pub, 10, 0)] &&
    (N.regsOf .one).map (fun g => (g.base, g.log)) == [(T.one, 0)] && T.qlt.isNone

/-- **The typed HAR's static check** of a configuration: the claim list at Q_arith's pointer, the regions. -/
def harChkB (C : QCfg) (T : TData) (N : TypedV.TNat) : Bool :=
  let p2 := p2C C
  let ph := phases47S C p2
  claimsOkB C (qarithBParts C T ph.1 (p2.adv ph.2)).1 && tdMatchB T N

end Lvm.QTyped
