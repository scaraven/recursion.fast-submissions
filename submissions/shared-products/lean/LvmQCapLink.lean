-- New for lvm2 MP-B (cap pruning, stage S2GB): Q_link at S2GB, with the heap, layer and cap gadgets.
import LvmQLinkSound
import LvmQCap

/-!
# Q_link at S2GB (`qlinkB`)

`openLoopsB`: per chunk of positions the layer check (`layerLoop`, `capLoop`'s place) and the node checks
(unchanged), then the level's heap check (`heapLoop`) and cap check (`capChk`). The heap of an opening starts
right after its `t` paths (`heapLane`). `qlinkB`: `qlink` with `openLoopsB`.
-/

set_option autoImplicit false

namespace Lvm.QLink

open RecursionFast Lvm Lvm.Replay Lvm.Loop Lvm.Loop.Build

/-- The first stream lane of an opening's heap: after its `t` paths. -/
def heapLane (p : Params) (o : OpenInfo) : Nat := eLane p o.i0 + o.L.t * posStride o.L

/-- **The loops of one opening at S2GB** (`zo` the step array, `bo` the opening's bit region). -/
def openLoopsB (p : Params) (lay : Layout) (zo bo : Nat) (o : OpenInfo) : BM Unit := do
  let L := o.L
  let ℓO := eLane p o.i0
  let Sj := posStride L
  let capL := eLane p o.ce + 1 + o.co / 8
  let m := L.height - L.path
  let c := p.capSendBits L.level L.cap
  let H := lay.sb + heapLane p o
  let _ ← seqAll ((pchunks L.t).map fun ch => do
    let gz := zo + 2 ^ lay.K - realCount L.t ch.1 ch.2
    layerLoop [ch.2] (lay.sb + ℓO + Sj * ch.1) L.row (lay.sb + ℓO + Sj * ch.1 + slotOff L L.path + 9)
      (layerLo H m) lay.sb lay.m [Sj] (bo + L.height * ch.1 + L.path) [L.height] m gz [1]
    let _ ← seqAll ((chunks L.path).map fun d =>
      nodeLoop [d.2, ch.2] (lay.sb + ℓO + Sj * ch.1 + slotOff L (d.1 + 1))
        (lay.sb + ℓO + Sj * ch.1 + slotOff L (d.1 + 1) + 1) (lay.sb + ℓO + Sj * ch.1 + slotOff L (d.1 + 1) + 5)
        (lay.sb + ℓO + Sj * ch.1 + slotOff L (d.1 + 1) - 4) [13, Sj]
        (bo + L.height * ch.1 + d.1) [1, L.height] gz [0, 1])
    pure ())
  heapLoop m H (zo + 2 ^ lay.K - (2 ^ (m - 1) - 2 ^ c))
  capChk H m c (lay.sb + capL) lay.fg

/-- Q_link after the position cells at S2GB. -/
def qlinkCoreB (p : Params) (lay : Layout) : BM Unit := do
  let zo ← stepArr lay.K (kc lay.fg)
  qltLoop lay.aQ lay.qt lay.sb lay.m (kc lay.fg)
  let _ ← seqAll ((List.range (opens p).length).map fun k =>
    openLoopsB p lay zo (bitBase p lay k) ((opens p).getD k default))
  pure ()

/-- **Q_link at S2GB**: the position cells, then the checks. -/
def qlinkB (p : Params) (lay : Layout) : BM Unit := do
  let _ ← posLoop lay.pa lay.fl (lay.fl + 2 ^ lay.pa)
  qlinkCoreB p lay

end Lvm.QLink
