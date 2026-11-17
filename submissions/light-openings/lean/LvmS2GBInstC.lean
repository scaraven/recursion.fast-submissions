-- New for lvm2 MP-B cap pruning (CAP-C2, 2026-11-17): the S2GB node program's instance on its frozen data
-- (`LvmE2QAsmDataB20`, the genb fixpoint of blob B), and Q_arith's opening on the S2GB stream (copies with `cp`).
import LvmE2QAsmDataB20
import LvmE2QAsmS
import LvmE2QTypedGuard
import LvmTypedVInst
import LvmS2GBSched
import LvmQCapLink

/-!
# The S2GB instance (blob B)

* **Q_arith's opening at S2GB** (copies of `lvPre`, `levelsG`, `lvOk`, `stackGWG`, `LayOk`, `openGF`, `qarithS`,
  `qaS` that pass `cp = some p` to `lvLanes`/`chLanes`: the next level's sent cap is `2^capSendBits` nodes, the
  level's heap node entries follow its openings): `lvPreB`, `levelsGB`, `lvOkB`, `stackGWGB`, `LayOkB`, `openGFB`,
  `qarithSB`, `qaSB`. With `cp = none` each is its original.
* `cfgB20` (`cfg20` at `P20B`), `mbTB20`, `tdataB20`: the mini-bus's tables and the circuit's static data at the
  frozen placements `frzB20`.
* `qaB20`, `segsB20`, **`QB20`**: Q_link at S2GB (`qlinkB`: the heap, layer and cap checks), Q_sig, then Q_arith
  on the S2GB stream; the program's segments and the program.
* `powB20` (`powU P20B`), **`layB20`** (`mkLayD` with `specQU` on `dintsB20`), **`cacheB20`** (the fast
  coordinate-split cache), `NTB20N` (the record of the regions and tables; `Φ_Q` unused by the guard).
* **`staticOkTB20`**: the S2GB typed guard (`staticOkTXc` at the S2GB instance).
-/

set_option autoImplicit false

namespace Lvm.Har

open Lvm Lvm.Loop Lvm.Loop.Build

/-! ## Q_arith's opening on the S2GB stream -/

/-- **`lvPre` on the stream `cp`** (`lvLanes … cp`). -/
def lvPreB (C : SCfg) (cp : Option Params) (pc : Nat) (zc oc g : Cell) (zk : Nat) (L : Level) (nxt : Option Level)
    (i f V : Nat) (q : Cell × Cell × Cell) : BM ((Cell × Cell × Cell) × List (Cell × Cell)) := do
  let ll := lvLanes C.g C.ood L nxt V cp
  let q ← roundsG pc f V L.fold q
  let lam ← ldEW (ll.V3 + 5)
  let lp ← pows (Nat.clog 2 (pw (C.pch i))) lam oc zc
  let er0 ← eqTab (fun j => ec (pc + f + j)) zc oc (decide (L.level = 0)) L.fold
  -- A level-0 leaf of `w < 2^ℓ` words (the stack's occupied lanes) is folded by the window `er0 + z`
  -- of the reversed table and the `z = 2^ℓ − w` zero cells after it: word `k < w` meets
  -- `eq[w − 1 − k]`, and the `z` lanes the loop reads past the leaf meet zero cells.
  let er ← if L.level = 0 ∧ L.row / 8 < 2 ^ L.fold then do
      let _ ← seqAll ((List.range (2 ^ L.fold - L.row / 8)).map fun _ => lin .E 0 0 zc zc)
      pure (er0 + (2 ^ L.fold - L.row / 8))
    else pure er0
  let enf ← foldsG (decide (L.level = 0)) L.fold (ll.V4 + 1) (oStr L) er lp L.t zc 0 (C.pch i)
  let it ← rdQ ll.V5 enf
  let cp ← getPtr
  iwConsts L.kappa g
  let W ← colWG (C.cch i) (pc + (f + L.fold)) (cp.k + L.kappa) cp.k lp (C.pb i) L.t zc zk 0 (C.pch i)
  powG C ll.V2 i g
  if C.ood && nxt.isSome then do
    let zb ← preloadG ((List.range L.kappa).map fun j => ll.Vc + 9 * j + 5)
    let y ← ldEW (ll.Vc + 9 * L.kappa + 5)
    let io ← rdQ (ll.Vc + 9 * L.kappa + 3) y
    let lam2 ← mulAdd .E lam lam zc
    let q ← glueG lam q io
    let q ← glueG lam2 q it
    let Wo ← eqZG zc ((List.range L.kappa).map fun j => (ec (zb + j), ec (pc + (f + L.fold) + j))) oc
    pure (q, [(lam, Wo), (lam2, W)])
  else do
    let q ← glueG lam q it
    pure (q, [(lam, W)])

/-- **`levelsG` on the stream `cp`.** -/
def levelsGB (C : SCfg) (cp : Option Params) (pc : Nat) (zc oc g : Cell) (zk : Nat) (bas : Cell) :
    List Level → Nat → Nat → Nat → Cell × Cell × Cell → List (Cell × Cell) → BM Unit
  | [], _, _, _, _, _ => pure ()
  | L :: rest, i, f, V, q, gl => do
    let r ← lvPreB C cp pc zc oc g zk L rest.head? i f V q
    match rest with
    | [] => do
      let ll := lvLanes C.g C.ood L none V cp
      let tgt ← tailG pc (f + L.fold) ll.V6 L.kappa r.1
      let mle ← mleFold L.kappa (ll.V1 + 5) (fun j => ec (pc + (f + L.fold) + j))
      let w ← wsumG bas (gl ++ r.2)
      terminalCheck w mle tgt g
    | N :: rest' =>
      levelsGB C cp pc zc oc g zk bas (N :: rest') (i + 1) (f + L.fold) (lvLanes C.g C.ood L (some N) V cp).V6 r.1
        (gl ++ r.2)

/-- **`lvOk` on the stream `cp`.** -/
def lvOkB (C : SCfg) (cp : Option Params) (T : Nat) : List Level → Nat → Nat → Nat → Bool
  | [], _, _, _ => false
  | L :: rest, i, f, V =>
    let ll := lvLanes C.g C.ood L rest.head? V cp
    decide (f + L.fold + L.kappa = C.nu) && decide (L.row % 8 = 0) &&
    decide (L.level ≠ 0 ∨ (0 < L.fold ∧ L.row / 8 ≤ 2 ^ L.fold)) && decide (1 ≤ L.t) &&
    decide (L.t ≤ pw (C.pch i)) &&
    (List.range (C.pch i).length).all (fun k => decide (pw ((C.pch i).take k) < L.t)) &&
    decide (csum (C.cch i) = L.kappa) &&
    decide (ll.V4 + 1 + oStr L * (L.t - 1) + 3 * 2 ^ L.fold + 2 < T) &&
    decide (ll.V6 + 15 * (L.kappa - 1) + 8 < T) && decide (1 ≤ L.kappa) && decide (C.g ≤ 64) &&
    match rest with
    | [] => true
    | N :: rest' => lvOkB C cp T (N :: rest') (i + 1) (f + L.fold) ll.V6

/-- **`stackGWG` on the stream `cp`.** -/
def stackGWGB {β : Type} (C : SCfg) (cp : Option Params) (n : Nat) (pre : BM β) (tg : β → Nat → BM Cell)
    (bg : β → Nat → Nat → BM Cell) (zc oc g : Cell) : BM Unit := do
  let w ← pre
  let pc ← preloadG (chLanes C.g C.ood C.levels (C.U + 15) cp)
  let sb ← ldEW (C.U + 5)
  let sp ← pows (Nat.clog 2 n) sb oc zc
  let tgt ← tg w sp
  let pt := (List.range C.nu).map fun k => ec (pc + k)
  let xb ← copiesG (pt.drop C.lf ++ pt.take C.lf)
  let bas ← bg w sp xb
  let zk ← const .K 0 g
  let q ← rdQ (C.U + 9) tgt
  levelsGB C cp pc zc oc g zk.n bas C.levels 0 0 (C.U + 15) q []

/-- **`LayOk` on the stream `cp`.** -/
def LayOkB (C : SCfg) (cp : Option Params) (T : Nat) : Bool :=
  lvOkB C cp T C.levels 0 0 (C.U + 15) && (chLanes C.g C.ood C.levels (C.U + 15) cp).all (fun v => decide (v + 2 < T)) &&
    decide (C.U + 20 < T) && decide (C.lf ≤ C.nu)

end Lvm.Har

namespace Lvm.Q2

open Lvm Lvm.Loop Lvm.Loop.Build Lvm.Har Lvm.QShape

/-- **`openGF` on the stream `cp`.** -/
def openGFB (Cm : SCfg) (cp : Option Params) (zon : Bool) (F : FCtx) (pin : CClaim) (cs : List FClaim) (mb : List Cell) (sK g : Cell) :
    BM Unit :=
  if zon then
    stackGWGB Cm cp (cs.length + 1)
      (do
        let σ ← sigmaG mb F.z
        let pz ← pinZG σ pin
        let ps ← prepZs F σ sK cs
        pure (σ, (PF.e3 pz.1 false, pz.1.value) :: ps))
      (fun w sp => targetG (w.2.map fun e => (⟨.main, .point ⟨0, 0⟩ [], e.2⟩ : CClaim)) sp F.z)
      (fun w sp xb => do
        let ms ← muxPtG w.1 xb (List.range CMain.nu20)
        let xs ← copiesG ms
        basisZF F (w.2.map (·.1)) sp xs w.1)
      F.z F.o g
  else
    stackGWGB Cm cp (cs.length + 1)
      (pure ((PF.e3 pin false, pin.value) :: cs.map (prepB F)))
      (fun w sp => targetG (w.map fun e => (⟨.main, .point ⟨0, 0⟩ [], e.2⟩ : CClaim)) sp F.z)
      (fun w sp xb => basisGF F Cm.nu (w.map (·.1)) sp xb)
      F.z F.o g

end Lvm.Q2

namespace Lvm.E2Q

open Lvm Lvm.Loop Lvm.Loop.Build Lvm.QAsm Lvm.Typed Lvm.Har Lvm.M3 Lvm.QLink Lvm.QSig Lvm.QTyped Lvm.Q2

/-- **`qarithS` at S2GB**: the opening on the S2GB stream (`openGFB … (some p)`). -/
def qarithSB (C : QCfg) (T : TData) (pin : CClaim) (o : FrontF) : BM Unit := do
  let g := kc (pbB C)
  let p := C.p
  let z ← const .E 0 (kc 0)
  let one ← const .E 1 (kc 0)
  let zk ← const .K 0 (kc 0)
  let ok ← const .K 1 (kc 0)
  let t ← typedGS T p (pbB C) (pubLanesS p) z one zk ok
  let tc ← typedClaimsGL z ⟨zk, zk⟩ ⟨ok, zk⟩ T (layout0 p).s t.1 t.2
  let a ← addK (o.mb.getD 18 default) 1
  let b ← addK (o.mb.getD 19 default) 1
  let sK ← mulAdd .K a b zk
  let F : Lvm.Q2.FCtx := ⟨z, one, zk, ⟨zk, zk⟩, ⟨ok, zk⟩, true⟩
  Lvm.Q2.openGFB (cfgMainF p (posBase C) (pwBase C)) (some p) (p.logN == 20 && p.nuMain == CMain.nu20) F pin (tc ++ o.cs)
    o.mb sK g

/-- **What follows Q_link and Q_sig at S2GB**. -/
def qaSB (C : QCfg) (T : TData) : BM Unit := do
  let pin ← pinF C.p
  let o ← frontS C
  qarithSB C T pin o

/-! ## The instance of blob B -/

open Lvm.M3 (Tab pushLeavesR)

/-- **S2GB's configuration**: `cfg20` at `P20B`. -/
def cfgB20 : QCfg := { cfg20 with p := P20B }

/-- The mini-bus's tables at S2GB (the heap-bottom regions' seeds: `capRegions` at `capPrune`). -/
def mbTB20 : List Tab := mbTOf cfgB20 frzB20

/-- The circuit's static data at S2GB. -/
def tdataB20 : TData :=
  let ts := mbTB20
  ⟨frzB20.com, frzB20.ks, frzB20.sig, frzB20.sflat, frzB20.pub, frzB20.one, none, ts.map Tab.shape,
    (ts.map (·.τ)).foldl max 0, mbFixOf cfgB20, log2Ceil (pushLeavesR ts)⟩

/-- **Q_arith at S2GB** (what follows Q_link and Q_sig): the pin, the front, the typed phases with the mini-bus's three
claims, the opening on the S2GB stream. -/
def qaB20 : BM Unit := qaSB cfgB20 tdataB20

/-- The S2GB program's segments (one run of the builder): Q_link at S2GB (`qlinkB`), Q_sig, Q_arith. -/
def segsB20 : List Seg :=
  ((do qlinkB cfgB20.p (lay cfgB20); let _ ← Lvm.QSig.qsigSC (sigIn cfgB20) (sigInLC cfgB20); qaB20 : BM Unit)
    ⟨nK cfgB20, 0⟩).2

/-- **The S2GB node program.** -/
def QB20 : Program :=
  let bs := VF.groupF segsB20
  ⟨nK cfgB20, 0, bs, (List.range bs.length).filter fun b => (bs.getD b default).dims.isEmpty⟩

theorem QB20_eq : QB20 = toProgram (nK cfgB20) 0
    (do qlinkB cfgB20.p (lay cfgB20); let _ ← Lvm.QSig.qsigSC (sigIn cfgB20) (sigInLC cfgB20); qaB20 : BM Unit) := by
  unfold QB20; rw [VF.groupF_eq]; rfl

/-- The ground challenges' lanes at S2GB (the front's and the typed phases'). -/
def powB20 : List (Nat × Nat) := powU P20B

/-- **The typed layout at S2GB** on the frozen dense intervals. -/
def layB20 : Typed.Lay := (mkLayD QB20 (specQU cfgB20 QB20 powB20) dintsB20).1

/-- **`Φ_Q`'s coordinate-split cache at S2GB** (evaluated at `E2` points by V_S's `PhiQGC`). -/
def cacheB20 : PhiCacheX := cacheWXF QB20 layB20

/-- The record of S2GB's regions and tables (the guard reads no `Φ_Q`). -/
def NTB20N : TypedV.TNat := ⟨nregsOf layB20 frzB20, fun _ => 0, mbTB20⟩

/-- **The S2GB typed guard** (`staticOkTXc` on `cacheB20`). -/
def staticOkTB20 : Bool := staticOkTXc cfgB20 frzB20 segsB20 QB20 layB20 NTB20N cacheB20

end Lvm.E2Q
