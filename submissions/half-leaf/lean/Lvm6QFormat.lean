-- New for lvm6 (WP CA; WP CA2: V1's items with `B` and `pos`, FORMAT6 v2.5's seed). CA's plan of WP-S's
-- schedule: `Lvm6.Item` → `It`, `Lvm6.Level` → `Lv`, and the kernel's cross-check of the two counts at `P18`.
import Lvm6QP18
import Lvm6Format

/-!
# The plan of the frozen schedule (CA-1 on WP-S's `sched6`)

`planOf sh` is the plan of `sched6 sh` (WP-S, `Lvm6Format`; its items are V1's `Lvm6.V.Item`): items
mapped by `itOfs` (one to one, except the position group `pos i g`, which is CA's `G(g)` then
`D(d − 1)`, `d` the level's position draws), levels from `sh.levels` (`lvOf`: the positions end one
draw before the openings, `λ`, except at the last level). **FORMAT6 v2.5**: the seed is `a₀ ‖ HDR`,
which is a chain query on `q₀`'s answer, so `planOf` plans it as the entry `fs 0 0` of `32 + |HDR|`
bytes (`Good6`: it starts with `a₀`; `contrib6`: it carries `HDR`); the `seed` class (v2.2's
`a₀ ‖ c ‖ HDR`) is no longer used by `planOf`. **`planOf_P18`** (in `Lvm6P18Park` since INT11): the walk's static conditions hold,
every link points backwards, the plan has `qSOf P18` entries and carries `bodyLen P18` bytes of
`BODY` (two independent counts agree), and every query fits `queryCap`.
-/

set_option autoImplicit false

namespace Lvm6.Q

/-- WP-S's levels as CA's (`gap 1` except at the last level). -/
def lvOf (sh : Lvm6.Shape) (i : ℕ) : Lv :=
  let L := sh.levels.getD i default
  ⟨L.ht, L.lv, L.leafB, L.nOpen, if i + 1 < sh.levels.length then 1 else 0⟩

/-- WP-S's items as CA's: one to one, except level `i`'s position group `pos i g` (FORMAT6 §6.6:
the ground draw `G(g)`, then the level's further position draws). -/
def itOfs (lv : ℕ → Lv) : Lvm6.Item → List It
  | .E k => [.E k]
  | .K k => [.K k]
  | .cap i => [.cap i]
  | .G g => [.G g]
  | .D k => [.D k]
  | .B => [.B]
  | .pos i g => [.G g, .D ((lv i).d - 1)]
  | .open i => [.open i]

/-- A shape's schedule as CA's items. -/
def itsOf (sh : Lvm6.Shape) : List It := (Lvm6.sched6 sh).flatMap (itOfs (lvOf sh))

/-- **The plan of a shape's schedule** (FORMAT6 v2.5): `q₀`, the seed `a₀ ‖ HDR` (a chain query on
entry 0, `Lvm6.seedLen sh` bytes), then the items' entries. -/
def planOf (sh : Lvm6.Shape) : List PE6 :=
  ⟨.q0, 7⟩ :: ⟨.fs 0 0, Lvm6.seedLen sh⟩ :: (walk (lvOf sh) w06 (itsOf sh)).1

theorem q06_eq : q06 = Lvm6.V.q06 := rfl

end Lvm6.Q
