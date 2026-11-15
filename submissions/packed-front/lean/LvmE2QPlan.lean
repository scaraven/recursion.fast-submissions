-- New for lvm2 E2-FT (E2F-QH3): the stream plan of a schedule, item by item (stage S2GF: `schedule P20F`).
import LvmScheduleF

/-!
# The stream lanes of the schedule's items

The stream is `tagTrace ‖ traceBytes`: byte 0 the tag, then per trace entry an 8-byte length word, the query
and the 32-byte answer. An FS query is the 32-byte state then the pending message bytes, so a value read at
pending byte `o` of the entry that starts at byte `b` is at lane `(b + 40 + o) / 8`, and the entry's answer
starts right after its pending bytes (an `E` answer: three lanes; an `E2` challenge: answer lanes 0–1, lane 2
the proof of work). Every pending width (24, 16, 8, 32 B) is whole lanes.

* **`itemLanes p`**: per item of `schedule p`, its lane: a `read`/`readW`/`cap`'s first data lane, a
  `sample`'s or `positions`' (first query's) answer lane, an `opening`'s first leaf entry (its length word).
* `laneOf p k`, `phaseItem0 p ph` (the index of the first item of phase `ph`), `phaseLane p ph j` (the lane of
  item `j` of phase `ph`).

The gadgets take lanes as plain `Nat` arguments; the assembly reads them from here.
-/

set_option autoImplicit false

namespace Lvm.E2Q

open Lvm

/-- The byte offset of the first schedule entry: the tag, `q₀`'s entry (`40 + 7`), the seed's (`40 + seedLenP`). -/
def startByte (p : Params) : Nat := 1 + (40 + 7) + (40 + seedLenP p)

/-- The lanes of `items` from the entry at byte `b` with `pend` bytes pending. -/
def itemLanesAux (p : Params) : Nat → Nat → List Item → List Nat
  | _, _, [] => []
  | b, pend, it :: r =>
    match it with
    | .read m => (b + 40 + pend) / 8 :: itemLanesAux p b (pend + eBytes * m) r
    | .readW m w => (b + 40 + pend) / 8 :: itemLanesAux p b (pend + w * m) r
    | .cap c _ => (b + 40 + pend) / 8 :: itemLanesAux p b (pend + nodeBytes * 2 ^ c) r
    | .sample => (b + 40 + pend) / 8 :: itemLanesAux p (b + 72 + pend) 0 r
    | .positions ref =>
      (b + 40 + pend) / 8 :: itemLanesAux p (b + 72 + pend + ((p.level ref).nPosQ - 1) * 72) 0 r
    | .opening ref =>
      let L := p.level ref
      b / 8 :: itemLanesAux p (b + L.t * (40 + L.row) + L.t * L.path * 104) pend r

/-- **The lane of every item** of `schedule p`. -/
def itemLanes (p : Params) : List Nat := itemLanesAux p (startByte p) 0 (schedule p)

/-- The lane of item `k`. -/
def laneOf (p : Params) (k : Nat) : Nat := (itemLanes p).getD k 0

/-- The index of the first item of phase `ph` in `schedule p` (the length of the schedule if absent). -/
def phaseItem0 (p : Params) (ph : Phase) : Nat :=
  (((phases p).takeWhile (·.1 != ph)).map (·.2.length)).sum

/-- The lane of item `j` of phase `ph`. -/
def phaseLane (p : Params) (ph : Phase) (j : Nat) : Nat := laneOf p (phaseItem0 p ph + j)

end Lvm.E2Q
