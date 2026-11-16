-- New for lvm2 E2-FT (E2F-V2): the public values with A23's incoming accumulator at a stage's variable count
-- (`acc_in` has `accV` coordinates: `accVars = 43` at S2GM, `accVF = 44` at S2GF).
import LvmVEqMid
import LvmScheduleF

/-!
# The public values at a stage

* **`pubOfA accV vk c sig`**: `pubOf` with `acc_in` read as `accV` coordinates and the value (at `accVars` it reads
  what `pubOf` reads). V_S at a stage `p` reads `pubOfA p.accV`.
* `RS.startH hb`, `DM.runOnH hb`: the stream cursor after `q₀` and a seed over a header of `hb` bytes.
* `pubOfW rd ew accV`: the width-parametric form (`acc_in` entries of `ew` bytes read by `rd`; `fe16At`: 16-B `E2`
  scalars as `⟨re, im, 0⟩`); **`pubXT x`**: S2GT's (45 coordinates of 16 B, `c₂_pubXT`).
* **`pubXF x`**: the statement's public values at S2GF (`pubX` with `acc_in` of `accVF = 44` coordinates); every
  field but `accIn` is `pubX`'s (`pubXF_eq`).
-/

set_option autoImplicit false

namespace Lvm

/-- **The public values with `acc_in` of `accV` coordinates** (`pubOf` reads `accVars`). -/
def pubOfA (accV : Nat) (vk c : Vector UInt8 32) (sig : ByteArray) : Pub :=
  { pubOf vk c sig with
    accIn := ⟨(List.range accV).map fun i => feAt sig (headerAt (offAcc + eBytes * i)),
      feAt sig (headerAt (offAcc + eBytes * accV))⟩ }

/-- **The cursor after `q₀` and the seed** for a header of `hb` bytes (`RS.start` at `headerBytes`; S2GF's first
schedule entry is 24 bytes later than S2GM's). -/
def RS.startH (hb : Nat) : RS := ⟨1 + 47 + (8 + (32 + hb - 8) + 32), 0, true⟩

theorem RS.startH_headerBytes : RS.startH headerBytes = RS.start := rfl

/-- Run a decision on the stream from the cursor after a header of `hb` bytes (`DM.runOn` at `headerBytes`). -/
def DM.runOnH {α : Type} (hb : Nat) (m : DM α) (sig : ByteArray) : α × RS := (m sig).run (RS.startH hb)

/-- An `E2` scalar of the header read into `E`: 16 bytes, `re` then `im`, `c₂ = 0`. -/
def fe16At (b : ByteArray) (o : Nat) : FE := ⟨kAt b o, kAt b (o + 8), 0⟩

/-- **The public values with `acc_in` of `accV` entries of `ew` bytes each, read by `rd`** (the width-parametric
path: `pubOfA accV` is `pubOfW feAt eBytes accV`, `pubOfA_eq_W`; S2GT's 16-B entries `pubOfW fe16At 16`). -/
def pubOfW (rd : ByteArray → Nat → FE) (ew accV : Nat) (vk c : Vector UInt8 32) (sig : ByteArray) : Pub :=
  { pubOf vk c sig with
    accIn := ⟨(List.range accV).map fun i => rd sig (headerAt (offAcc + ew * i)),
      rd sig (headerAt (offAcc + ew * accV))⟩ }

theorem pubOfA_eq_W (accV : Nat) : pubOfA accV = pubOfW feAt eBytes accV := rfl

@[simp] theorem length_pubOfW (rd : ByteArray → Nat → FE) (ew accV : Nat) (vk c : Vector UInt8 32)
    (sig : ByteArray) : (pubOfW rd ew accV vk c sig).accIn.pt.length = accV := by
  simp [pubOfW]

/-- **16-B entries have `c₂ = 0`**: every coordinate of `acc_in` and its value. -/
theorem c₂_pubOfW_fe16 (ew accV : Nat) (vk c : Vector UInt8 32) (sig : ByteArray) :
    (∀ e ∈ (pubOfW fe16At ew accV vk c sig).accIn.pt, e.c₂ = 0) ∧ (pubOfW fe16At ew accV vk c sig).accIn.y.c₂ = 0 := by
  refine ⟨fun e he ↦ ?_, rfl⟩
  simp only [pubOfW, List.mem_map] at he
  obtain ⟨i, -, rfl⟩ := he
  rfl

@[simp] theorem length_pubOfA (accV : Nat) (vk c : Vector UInt8 32) (sig : ByteArray) :
    (pubOfA accV vk c sig).accIn.pt.length = accV := by
  simp [pubOfA]

end Lvm

namespace Lvm.VEq

/-- **The statement's public values at S2GF**: `acc_in` of `accVF = 44` coordinates. -/
def pubXF (x : List UInt8) : Pub := pubOfA accVF (hdX x).vk (hdX x).stmt (sigOfX x)

@[simp] theorem length_pubXF (x : List UInt8) : (pubXF x).accIn.pt.length = 44 :=
  length_pubOfA _ _ _ _

/-- A23's variables at S2GT (`Φ_Q` on 45 variables; the header's `acc_in` is 46 scalars of 16 B). -/
def accVT : Nat := 45

/-- **The statement's public values at S2GT**: `acc_in` of `accVT = 45` coordinates read from 16-B scalars
(`⟨re, im, 0⟩`, `c₂_pubXT`). -/
def pubXT (x : List UInt8) : Pub := pubOfW fe16At 16 accVT (hdX x).vk (hdX x).stmt (sigOfX x)

@[simp] theorem length_pubXT (x : List UInt8) : (pubXT x).accIn.pt.length = 45 :=
  length_pubOfW _ _ _ _ _ _

/-- **S2GT's `acc_in` has `c₂ = 0`** in every coordinate and in its value. -/
theorem c₂_pubXT (x : List UInt8) :
    (∀ e ∈ (pubXT x).accIn.pt, e.c₂ = 0) ∧ (pubXT x).accIn.y.c₂ = 0 :=
  c₂_pubOfW_fe16 _ _ _ _ _

/-- Every field of `pubXF x` but `acc_in` is `pubX x`'s. -/
theorem pubXF_eq (x : List UInt8) : pubXF x = { pubX x with accIn := (pubXF x).accIn } := rfl

end Lvm.VEq
