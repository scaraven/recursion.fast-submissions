-- New for lvm2 E2-FT (E2F-C): a candidate pair's memory for a typed instance with twin `E2` rows (S2GF), and its rows'
-- `Holds`/`Asserts` from the coordinate-split wiring relation (`holds_of_wiringX`); generic in the instance and in the
-- statement's public data (S2GF: `pubXF`).
import LvmTypedX
import LvmNodeSoundT

/-!
# The pair's memory at S2GF

* **`zTX Ti pb x qm qr`**, **`memTX`**: the pair's words `Ti.zOf lay26 (pb x) qm qr` and the memory read off them
  (roll 11's `zT`/`memT` for any instance `Ti` and public-data map `pb`).
* **`holds_memTX`**: with the guard's facts on `Ti.Q` (well-formed, twins adjacent, the layout's check), the word `1`
  in a `1` region, the coordinate-split wiring relation and `ReaddOk`, the program's rows hold and assert.
-/

set_option autoImplicit false

namespace Lvm.E2Q

open Lvm Lvm.Loop Lvm.Typed LeanVM.Protocol

section
variable (Ti : TInst) (pb : List UInt8 → Lvm.Pub)

/-- **A candidate pair's words** for the instance `Ti` (statement `x`, public data `pb x`). -/
noncomputable def zTX (x : List UInt8) (qm : Column CMain.nu20) (qr : Column 19) : ℕ → FK :=
  Ti.zOf Lvm.M3.lay26 (pb x) qm qr

/-- **The memory read off a candidate pair's words.** -/
noncomputable def memTX (x : List UInt8) (qm : Column CMain.nu20) (qr : Column 19) : Mem :=
  memOf Ti.lay (zTX Ti pb x qm qr)

end

/-- **The rows hold and assert on the pair's memory** (`holds_of_wiringX` on `Ti`'s program and layout). -/
theorem holds_memTX {Ti : TInst} {pb : List UInt8 → Lvm.Pub} (hwf : Ti.Q.wf = true) (htw : Ti.Q.twinsOk = true)
    (hlay : Ti.lay.Ok Ti.Q) (hone : Ti.src? Ti.lay.one = some .one) {x : List UInt8} {qm : Column CMain.nu20}
    {qr : Column 19} (hW : WiringRelX Ti.Q Ti.lay (zTX Ti pb x qm qr))
    (hrd : ReaddOk Ti.Q (memTX Ti pb x qm qr)) :
    Ti.Q.Holds (memTX Ti pb x qm qr) ∧ Ti.Q.Asserts (memTX Ti pb x qm qr) :=
  holds_of_wiringX Ti.Q Ti.lay _ hwf htw hlay (Lvm.NS.zOf_one Ti hone Lvm.M3.lay26 (pb x) qm qr) hW hrd

end Lvm.E2Q
