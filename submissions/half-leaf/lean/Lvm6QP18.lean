-- New for lvm6 (WP CA). FORMAT6 v2.2 §6's fixed part as CA items, and the kernel's check of its counts.
import Lvm6QPlan

/-!
# The plan of FORMAT6's fixed schedule at `P18` (CA-1 instance)

`sched18 mid`: FORMAT6 §6.1, §6.2, the §6.3 core, then `mid` (the sub-schedules of §T: sponge
caller and link, typed phases, mini-bus, owned by CB/CD), then §6.5 and §6.6. `lv18` is §5's table. `lv18`, `s61`, `s62`, `s66`, `sched18` and the checks are (in `Lvm6P18Park` since INT11); the
pieces `R`, `rep`, `layer`, `core`, `s63`, `s65`, `hdrLen` stay here (`Lvm6QP17` uses them).
Kernel checks (`plan18_ok`): with `mid = []` the walk's static conditions hold, every link points
backwards, and the plan has `2 + 3,868 + 298` entries (FORMAT6 §7's `qS` without `Q_sp + Q_ty + Q_mb`).
WP-S's `sched6 P18` is to equal `sched18 mid` item for item (its own kernel check).
-/

set_option autoImplicit false

namespace Lvm6.Q

/-- A sumcheck round `R(n, g)`: `E(n)` then `G(g)`. -/
def R (n g : ℕ) : List It := [.E n, .G g]

/-- `k` copies of a list of items. -/
def rep (k : ℕ) (l : List It) : List It := (List.replicate k l).flatten

/-- One layer of `verify_layer` with `e` eq-mode rounds (§6.2 row 8). -/
def layer (e : ℕ) : List It := [.E 47, .G 6] ++ rep e (R 2 2) ++ rep 11 (R 3 2) ++ [.E 3, .G 2]

/-- §6.2 rows 6–10 at `e` eq-mode rounds and `r` input-opening rounds. -/
def core (e r : ℕ) : List It :=
  [.G 3, .D 5, .E 1] ++ rep 12 (layer e) ++ rep 6 (R 2 2) ++ [.E 1] ++ rep r (R 2 2) ++ [.E 64]

/-- §6.3: the sponge batch's reduction core (`κ_s = 13`). -/
def s63 : List It := core 10 10

/-- §6.5: ring switching and batching. -/
def s65 : List It := [.B, .G 17, .D 32]

/-- The `BODY` bytes the entries carry (`contrib6`'s lengths): a chain query its message, a leaf
its bytes, a node query its sibling. -/
def bodyBytes (P : List PE6) : ℕ :=
  (P.map fun e => match e.k with
    | .fs _ _ => e.len - 32
    | .leaf => e.len
    | .node .. => 32
    | _ => 0).sum

/-- `|HDR|` at `v` accumulator variables (FORMAT6 v2.2 §2). -/
def hdrLen (v : ℕ) : ℕ := 136 + 16 * v

end Lvm6.Q
