-- New for lvm6 (PORT17 L1). FORMAT6 v2.6 §6's fixed part at `P17` as CA items, and the kernel's check of its counts
-- (`Lvm6QP18`'s form).
import Lvm6QP18

/-!
# The plan of FORMAT6's fixed schedule at `P17` (CA-1 instance)

`sched17 mid`: FORMAT6 v2.6 §6.1, §6.2, the §6.3 core, then `mid` (the §T sub-schedules), then §6.5 and §6.6,
transcribed from v2.6 (P17-freeze §2.2) with `P18`'s blocks (`R`, `rep`, `layer`, `core`, `s63`, `s65`). `lv17` is
v2.6 §5's table. Kernel checks (`plan17_ok`): with `mid = []` the walk's static conditions hold, every link points
backwards, and the plan has `2 + 3,626 + 298` entries (v2.6 §7's `qS` without `Q_sp + Q_ty + Q_mb`); `body17`: the
fixed `BODY` is 197,784 + 23,688 = 221,472 bytes.
-/

set_option autoImplicit false

namespace Lvm6.Q

/-- FORMAT6 v2.6 §5's levels (`gap`: `λ` between the positions and the openings at levels 0–3). -/
def lv17 : ℕ → Lv
  | 0 => ⟨20, 7, 368, 110, 1⟩
  | 1 => ⟨19, 6, 256, 45, 1⟩
  | 2 => ⟨18, 5, 256, 28, 1⟩
  | 3 => ⟨17, 5, 256, 21, 1⟩
  | _ => ⟨16, 5, 256, 18, 0⟩

/-- §6.1 at `P17`: the commitment (`z₀ ∈ E^24`). -/
def s61P17 : List It := [.cap 0, .B, .G 18, .D 23, .E 1]

/-- §6.2 at `P17`: the tree batch (`ρ ∈ E^17`, 15 eq-mode rounds a layer). -/
def s62P17 : List It := [.K 4, .G 5, .D 16, .E 8, .G 1, .E 21] ++ core 15 11

/-- §6.6 at `P17`, level `i < 4` (fold `ℓ`, OOD point `ν`, query grind `gq`; `lv17`'s draws). -/
def lvlMid17 (i ℓ ν gq : ℕ) : List It :=
  rep ℓ [.E 4, .G 10, .D 1] ++
    [.E ℓ, .cap (i + 1), .B, .G 18, .D (ν - 1), .E 1, .G gq, .D ((lv17 i).d - 1), .D 1, .open i]

/-- §6.6 at `P17`, level 4 (final polynomial of 8 scalars, position grind 18, three draws, two tail rounds). -/
def lvlEnd17 : List It := rep 4 [.E 4, .G 10, .D 1] ++ [.E 8, .G 18, .D 2, .open 4] ++ rep 2 (R 2 2)

/-- §6.6 at `P17`: the opening. -/
def s66P17 : List It :=
  lvlMid17 0 6 18 19 ++ lvlMid17 1 4 14 17 ++ lvlMid17 2 4 10 18 ++ lvlMid17 3 4 6 17 ++ lvlEnd17

/-- **FORMAT6 v2.6 §6 at `P17`**, with the §T sub-schedules `mid`. -/
def sched17 (mid : List It) : List It := s61P17 ++ s62P17 ++ s63 ++ mid ++ s65 ++ s66P17

/-- **FORMAT6 v2.6 §7's fixed `BODY`**: 197,784 + 23,688 = 221,472 bytes (the seed carries `HDR`). -/
theorem body17 : bodyBytes (walk lv17 w06 (sched17 [])).1 = 221472 := by decide +kernel

/-- **FORMAT6 v2.6's fixed schedule is a well-formed plan of `2 + 3,626 + 298` entries** (any `|HDR|`). -/
theorem plan17_ok (v : ℕ) :
    walkOK lv17 (sched17 []) = true ∧ refsOK (plan6 lv17 (hdrLen v) (sched17 [])) = true ∧
      (plan6 lv17 (hdrLen v) (sched17 [])).length = 2 + 3626 + 298 := by
  have hr : refsFrom 2 (walk lv17 w06 (sched17 [])).1 = true := by decide +kernel
  have hl : (walk lv17 w06 (sched17 [])).1.length = 3626 + 298 := by decide +kernel
  refine ⟨by decide +kernel, ?_, ?_⟩
  · simp only [refsOK, plan6, refsFrom, refsOK1, hr, hdrLen]; simp
  · simp only [plan6, List.length_cons, hl]

end Lvm6.Q
