-- New for lvm6 (WP CA). FORMAT6 v2.2 §6's fixed part as CA items, and the kernel's check of its counts.
import Lvm6QPlan

/-!
# The plan of FORMAT6's fixed schedule at `P18` (CA-1 instance)

`sched18 mid`: FORMAT6 §6.1, §6.2, the §6.3 core, then `mid` (the sub-schedules of §T: sponge
caller and link, typed phases, mini-bus, owned by CB/CD), then §6.5 and §6.6. `lv18` is §5's table.
Kernel checks (`plan18_ok`): with `mid = []` the walk's static conditions hold, every link points
backwards, and the plan has `2 + 3,868 + 298` entries (FORMAT6 §7's `qS` without `Q_sp + Q_ty + Q_mb`).
WP-S's `sched6 P18` is to equal `sched18 mid` item for item (its own kernel check).
-/

set_option autoImplicit false

namespace Lvm6.Q

/-- FORMAT6 §5's levels (`gap`: `λ` between the positions and the openings at levels 0–3). -/
def lv18 : ℕ → Lv
  | 0 => ⟨21, 7, 368, 110, 1⟩
  | 1 => ⟨20, 6, 256, 45, 1⟩
  | 2 => ⟨19, 5, 256, 28, 1⟩
  | 3 => ⟨18, 5, 256, 21, 1⟩
  | _ => ⟨17, 5, 256, 18, 0⟩

/-- A sumcheck round `R(n, g)`: `E(n)` then `G(g)`. -/
def R (n g : ℕ) : List It := [.E n, .G g]

/-- `k` copies of a list of items. -/
def rep (k : ℕ) (l : List It) : List It := (List.replicate k l).flatten

/-- §6.1: the commitment. -/
def s61 : List It := [.cap 0, .B, .G 18, .D 24, .E 1]

/-- One layer of `verify_layer` with `e` eq-mode rounds (§6.2 row 8). -/
def layer (e : ℕ) : List It := [.E 47, .G 6] ++ rep e (R 2 2) ++ rep 11 (R 3 2) ++ [.E 3, .G 2]

/-- §6.2 rows 6–10 at `e` eq-mode rounds and `r` input-opening rounds. -/
def core (e r : ℕ) : List It :=
  [.G 3, .D 5, .E 1] ++ rep 12 (layer e) ++ rep 6 (R 2 2) ++ [.E 1] ++ rep r (R 2 2) ++ [.E 64]

/-- §6.2: the tree batch. -/
def s62 : List It := [.K 4, .G 5, .D 17, .E 8, .G 1, .E 21] ++ core 16 11

/-- §6.3: the sponge batch's reduction core (`κ_s = 13`). -/
def s63 : List It := core 10 10

/-- §6.5: ring switching and batching. -/
def s65 : List It := [.B, .G 17, .D 32]

/-- §6.6, level `i < 4` (fold `ℓ`, OOD point `ν`, query grind `gq`). -/
def lvlMid (i ℓ ν gq : ℕ) : List It :=
  rep ℓ [.E 4, .G 10, .D 1] ++
    [.E ℓ, .cap (i + 1), .B, .G 18, .D (ν - 1), .E 1, .G gq, .D ((lv18 i).d - 1), .D 1, .open i]

/-- §6.6, level 4. -/
def lvlEnd : List It := rep 4 [.E 4, .G 10, .D 1] ++ [.E 12, .G 13, .D 2, .open 4] ++ rep 3 (R 2 2)

/-- §6.6: the opening. -/
def s66 : List It := lvlMid 0 6 19 19 ++ lvlMid 1 4 15 17 ++ lvlMid 2 4 11 18 ++ lvlMid 3 4 7 17 ++ lvlEnd

/-- **FORMAT6 §6 at `P18`**, with the §T sub-schedules `mid`. -/
def sched18 (mid : List It) : List It := s61 ++ s62 ++ s63 ++ mid ++ s65 ++ s66

/-- The `BODY` bytes the entries carry (`contrib6`'s lengths): a chain query its message, a leaf
its bytes, a node query its sibling. -/
def bodyBytes (P : List PE6) : ℕ :=
  (P.map fun e => match e.k with
    | .fs _ _ => e.len - 32
    | .leaf => e.len
    | .node .. => 32
    | _ => 0).sum

/-- **FORMAT6 §7's fixed `BODY`**: 205,472 + 23,688 = 229,160 bytes (the seed carries `HDR`). -/
theorem body18 : bodyBytes (walk lv18 w06 (sched18 [])).1 = 229160 := by decide +kernel

/-- `|HDR|` at `v` accumulator variables (FORMAT6 v2.2 §2). -/
def hdrLen (v : ℕ) : ℕ := 136 + 16 * v

/-- **FORMAT6's fixed schedule is a well-formed plan of `2 + 3,868 + 298` entries** (any `|HDR|`). -/
theorem plan18_ok (v : ℕ) :
    walkOK lv18 (sched18 []) = true ∧ refsOK (plan6 lv18 (hdrLen v) (sched18 [])) = true ∧
      (plan6 lv18 (hdrLen v) (sched18 [])).length = 2 + 3868 + 298 := by
  have hr : refsFrom 2 (walk lv18 w06 (sched18 [])).1 = true := by decide +kernel
  have hl : (walk lv18 w06 (sched18 [])).1.length = 3868 + 298 := by decide +kernel
  refine ⟨by decide +kernel, ?_, ?_⟩
  · simp only [refsOK, plan6, refsFrom, refsOK1, hr, hdrLen]; simp
  · simp only [plan6, List.length_cons, hl]

end Lvm6.Q
