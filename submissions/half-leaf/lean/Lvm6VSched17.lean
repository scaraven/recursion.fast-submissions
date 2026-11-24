-- New for lvm6 (PORT17 L1): V1's FORMAT6 tables (`Lvm6VSched`) at the shape `P17` (FORMAT6 v2.6, P17-freeze §1.3,
-- §2.2): the levels, the fixed sub-schedules §6.1, §6.2, §6.6 at `M = 24`, and their counts, kernel-checked.
import Lvm6VQueries

/-!
# The lvm6 schedule at `P17` (FORMAT6 v2.6 §5, §6) as data

`P17` has `N★ = 2^17` blocks, the tree batch `κ = 18` and the stack `M = 24`. The building blocks are `P18`'s
(`layer`, `R`, `foldR`, `lvl`, `s63core`, `s65`, `Lvm6VSched`); what `n` moves is written out here, transcribed
from FORMAT6 v2.6 (P17-freeze §2.2), not derived from `P18`'s:

* `levs17`: §5's levels `ht = 20, 19, 18, 17, 16`, caps `2^7, 2^6, 2^5, 2^5, 2^5`, the same openings;
* `s61P17`: §6.1 with `z₀ ∈ E^24` (`D(23)`);
* `s62P17`: §6.2 with `ρ ∈ E^17` (`D(16)`) and 15 eq-mode rounds a layer;
* `s66P17`: §6.6 with `ν = 18, 14, 10, 6`, level 4's final polynomial of 8 scalars, its position group at grind 18
  (no bind, freeze §2.3) and two tail rounds;
* `sched17 mid`: `s61P17 ++ s62P17 ++ mid ++ s65 ++ s66P17`.

The counts are FORMAT6 v2.6's table (P17-freeze §1.3), checked by `decide +kernel` (`counts_*_17`), with the
draws (`draws_17`), the level lookup (`levsOK_17`), the length rule (`fsLenOK_17`) and the static query count of
the fixed part with §6.3's core (`qOf_17`: 3,924).
-/

namespace Lvm6.V

/-- The levels of `P17` (FORMAT6 v2.6 §5). -/
def levs17 : List Lev :=
  [⟨20, 7, 64, 46, 110⟩, ⟨19, 6, 32, 32, 45⟩, ⟨18, 5, 32, 32, 28⟩, ⟨17, 5, 32, 32, 21⟩, ⟨16, 5, 32, 32, 18⟩]

/-- §6.1 at `P17`: the cap of level 0, a bind, the OOD point `z₀ ∈ E^24`, its value `y₀`. -/
def s61P17 : List Item := [.cap 0, .B, .G 18, .D 23, .E 1]

/-- §6.2 at `P17`: the tree batch, `ρ ∈ E^17`, 15 eq-mode rounds a layer (`κ − 3`, `κ = 18`). -/
def s62P17 : List Item :=
  [.K 4, .G 5, .D 16, .E 8, .G 1, .E 21, .G 3, .D 5, .E 1] ++ rep 12 (layer 15) ++
    rep 6 (R 2 2) ++ [.E 1] ++ rep 11 (R 2 2) ++ [.E 64]

/-- §6.6 at `P17`: levels 0–3 (`ν = 18, 14, 10, 6`), then level 4 (four fold rounds, the final polynomial of
`2^2 + 4` scalars, its position group at grind 18, the openings, two tail rounds). -/
def s66P17 : List Item :=
  lvl 0 6 18 19 ++ lvl 1 4 14 17 ++ lvl 2 4 10 18 ++ lvl 3 4 6 17 ++
    rep 4 foldR ++ [.E 8, .pos 4 18, .open 4] ++ rep 2 (R 2 2)

/-- **The `P17` schedule**, with the sub-schedules of FORMAT6 §T (`mid`) between §6.2 and §6.5. -/
def sched17 (mid : List Item) : List Item := s61P17 ++ s62P17 ++ mid ++ s65 ++ s66P17

theorem levsOK_17 : levsOK levs17 = true := by decide +kernel

/-! ## FORMAT6 v2.6's table (§6, §7), checked -/

theorem counts_61_17 :
    bytesOf levs17 s61P17 = 4120 ∧ queriesOf levs17 s61P17 = 25 ∧ noncesOf s61P17 = 1 := by decide +kernel
theorem counts_62_17 :
    bytesOf levs17 s62P17 = 26640 ∧ queriesOf levs17 s62P17 = 377 ∧ noncesOf s62P17 = 356 := by decide +kernel
theorem counts_63core_17 :
    bytesOf levs17 s63core = 23688 ∧ queriesOf levs17 s63core = 298 ∧ noncesOf s63core = 293 := by decide +kernel
theorem counts_65_17 : bytesOf levs17 s65 = 8 ∧ queriesOf levs17 s65 = 34 ∧ noncesOf s65 = 1 := by decide +kernel
theorem counts_66_level0_17 :
    bytesOf levs17 (lvl 0 6 18 19) = 88848 ∧ queriesOf levs17 (lvl 0 6 18 19) = 1591 := by decide +kernel
theorem counts_66_17 :
    bytesOf levs17 s66P17 = 167016 ∧ queriesOf levs17 s66P17 = 3190 ∧ noncesOf s66P17 = 33 := by decide +kernel

/-- **The fixed part at `P17`** (FORMAT6 v2.6 §6's last table): 197,784 bytes, 3,626 queries, 391 nonces. -/
theorem counts_fixed_17 : bytesOf levs17 (sched17 []) = 197784 ∧ queriesOf levs17 (sched17 []) = 3626 ∧
    noncesOf (sched17 []) = 391 := by decide +kernel

/-- The draws of the five levels' positions (FORMAT6 v2.6 §5): 19, 8, 4, 3, 3. -/
theorem draws_17 : levs17.map Lev.draws = [19, 8, 4, 3, 3] := by decide +kernel

/-- The length rule holds for `P17`'s fixed part with §6.3's core in place of `mid`. -/
theorem fsLenOK_17 : fsLenOK levs17 (sched17 s63core) = true := by decide +kernel

/-- **`P17`'s count** (FORMAT6 v2.6 §7): the fixed part with §6.3's core asks 3,924 chain and opening
queries (`3,626 + 298`). -/
theorem qOf_17 : qOf levs17 (sched17 s63core) = 3924 := by decide +kernel

end Lvm6.V
