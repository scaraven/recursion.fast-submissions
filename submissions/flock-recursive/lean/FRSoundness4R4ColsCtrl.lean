-- New for `flock-recursive` (BLUEPRINT revision 4.1; track R4g): controls of R4g's definitions.
import FRSoundness4R4LinkP
import FRVerifierImplNode4F

/-!
# Controls for R4g (`posOps4`'s reference, the folds, the kind levels)

| Definition | Positive | Negative |
|---|---|---|
| `stepT4` | `stepT4_ok` (the expected node query: registers and a true flag at an active depth) | `stepT4_wrong` (another query: `none`), `stepT4_nil` |
| `posT4`, `posAllT4` | `posAllT4_zero` (no position: no registers, flag true); `exec_posOps4`, `posAllT4_path` | `posT4_nil`, `posT4_wrong` (a query that is not the column's: `none`) |
| `yReg4`, `yv4` | `cols4_of_run`, `link4_of_fields` (they are the folds `FinRest4` reads) | `yv4_ctl` (a register file holding `.k 1` there reads `1`, one holding `.k 0` reads `0`) |
| `seq4.lvK` vs `seq4.lv` | `lvK_eq4` (the program's kind level is T4's `lvOf`) | `lvK_ne_star4` (an `m = 30` kind's level 0 has 18 position bits, the star's 20: `posOps4` must index with the kind's) |
| `finPLow_reloc` | `finPLow_reloc` | `relocF_moves` (R4's: relocation moves a π read) |
| the op parameter `hphi` | `phiRS_segC`, `phiRS_nodeC`, `phiRS_nodeF` (INT-9's final node ops `implN4F`) | — (an equation) |
-/

namespace FR.Snd.R4
open RecursionFast Rev4 FR.Merkle

variable (inp : Input)

/-- (+) **The expected node query** at an active depth: six registers, flag true. -/
theorem stepT4_ok (sib i h j so : ℕ) (cur a : Digest) (tr : Trace) (hh : h < sib) :
    let s := bytesAt inp.π (absOff 0 so) 32
    let l := if j.testBit h then s else cur
    let r := if j.testBit h then cur else s
    stepT4 inp sib i h j so cur ((nodeQ i l r, a) :: tr) =
      some ([.d s, .bit (j.testBit h), .d l, .d r, .d a, .d a], true, a, tr) := by
  simp [stepT4, hh]

/-- (−) **Another query** fails the step. -/
theorem stepT4_wrong (sib i h j so : ℕ) (cur a : Digest) (tr : Trace) (q : ByteArray)
    (hq : q ≠ (if decide (h < sib) then nodeQ i (if j.testBit h then bytesAt inp.π (absOff 0 so) 32 else cur)
      (if j.testBit h then cur else bytesAt inp.π (absOff 0 so) 32) else nodeQ i zeroD zeroD)) :
    stepT4 inp sib i h j so cur ((q, a) :: tr) = none := by
  simp only [stepT4]; exact if_neg hq

theorem stepT4_nil (sib i h j so : ℕ) (cur : Digest) : stepT4 inp sib i h j so cur [] = none := rfl

/-- (+) **No position**: no registers, flag true, the trace untouched. -/
theorem posAllT4_zero (Lk : Level) (sL i co so capO : ℕ) (ad : ℕ → Digest) (w : Array K) (p : ℕ)
    (tr : Trace) : posAllT4 inp Lk sL i co so capO ad w 0 p tr = some ([], true, tr) := rfl

theorem posT4_nil (Lk : Level) (sL i co so capO : ℕ) (ad : ℕ → Digest) (w : Array K) (p : ℕ) :
    posT4 inp Lk sL i co so capO ad w p [] = none := rfl

/-- (−) **A query that is not the column's** fails the position. -/
theorem posT4_wrong (Lk : Level) (sL i co so capO : ℕ) (ad : ℕ → Digest) (w : Array K) (p : ℕ)
    (q : ByteArray) (a : Digest) (tr : Trace)
    (hq : q ≠ colQ i (inp.π.extract (absOff 0 (co + p * colBytes i)) (absOff 0 (co + p * colBytes i) + colBytes i))) :
    posT4 inp Lk sL i co so capO ad w p ((q, a) :: tr) = none := by
  simp only [posT4]; exact if_neg hq

/-- (−) **The kind's level is not the star's**: at `m = 30`, level 0 has 18 position bits. -/
theorem lvK_ne_star4 : (seq4.lvK 30 0).logN = 18 ∧ (seq4.lv 0).logN = 20 := by
  rw [seq4_eq]; exact ⟨rfl, rfl⟩

/-- (+/−) **`yv4` reads its register**: `.k 1` reads `1`, `.k 0` reads `0`. -/
theorem yv4_ctl (p : KindP) (i q : ℕ) :
    yv4 p ((Array.replicate (yReg4 p i q + 1) (Val.k 0)).set! (yReg4 p i q) (.k 1)) i q = 1 ∧
      yv4 p (Array.replicate (yReg4 p i q + 1) (Val.k 0)) i q = 0 := by
  constructor <;> simp [yv4, rd, Val.toK]

/-- (+) **INT-9's final node ops meet `hphi`** (`implN4F` keeps `implN4T`'s `phiRS`). -/
theorem phiRS_nodeF (fin : Finals) (lRows : List Circ.Row) (κs₀ : F) (ν : NodeKind) :
    ∀ r a, r.size = 7 → (NI4F.implN4F (fun _ => Impl.implC fin lRows κs₀) ν).phiRS r a = Impl.phiRSS r a :=
  phiRS_nodeC fin lRows κs₀ ν

end FR.Snd.R4
