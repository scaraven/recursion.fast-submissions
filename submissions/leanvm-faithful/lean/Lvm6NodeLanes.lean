-- New for lvm6 (WP NODE, coordinator's request). The circuit's lane geometry (`QK.layItems`/`layEnd`) against
-- the stream geometry of the plan of `sched6 P18` (CA's `planOf`, FORMAT6 v2.5.3 §3–§5), item by item, by the kernel.
import Lvm6QKStmt
import Lvm6QFormat
import Lvm6QLinkBridge

/-!
# The circuit's lanes are the schedule's (`laneChk_P18`)

**Decision (layout disagreement).** FORMAT6 v2.5.3 and V1's walk (`Lvm6VSched`: `queriesI (.pos i _) = draws`,
`fsLensAux (.pos i _) = (32 + b + 8) :: replicate (draws − 1) 32`, one nonce) read `pos i g` as the ground group
`G g` followed by `D(draws − 1)`; CA2's `itOfs` maps it to `[G g, D (d − 1)]`. So CB's form (two slots, the
nonce and the first draw, then the next buffer) and CD's (no slot) both miscount when `draws > 1`. `QK.layItems`
now lays `pos i g` as `G g, D (posD i)` (`posD i = draws − 1` of level `i` of `P18`), and a cap `cap i` as its
`4·2^lv` lanes (its bytes are buffered into the next query, `fsLensAux`), with no event.

**The check.** `laneWalk` walks `sched6 P18` and, in step, the plan's entries from entry 2 (after `q₀` and the
seed): `off` is the stream byte offset of the current chain entry (`40 + len` bytes each: length word, query,
answer; `bOff6`), `pend` the lanes buffered since the last draw. At every item it asks that the circuit's lane
(`layEnd` of the items before it, from the first buffer) is the stream's: `off / 8 + 5 + pend`. A draw (`G`, `D`,
`B`, `pos`) consumes `queriesI` entries; `E k`, `K k`, `cap i` add `2k`, `k`, `capL i` pending lanes; an opening
consumes its `t·(1 + path)` entries and the walk resynchronises after it; there it also asks (LAY2, CC8's
request) that the lane after the openings is CC's `a + t·openStride` (`openStrideV`: the leaf entry's `lb/8 + 5`
lanes and `path` node entries of 13), from the opening's lane `a`, and at the final level that `a` is CC-8's
cursor `finOpenAt = aL + 27ℓ + 2nf + 10 + 9kq` (`finOff18`: `ℓ = 4`, `nf = 12`, `kq = 2`, i.e. `aL + 160`) from
the level's first lane `aL` (the lane after level 3's openings). So `layFin`'s tail rounds `R(2, gT)` start at
the lane the stream puts them (they are then checked item by item as before).
**`laneChk_P18`**: the walk accepts the whole schedule (`decide +kernel`).
-/

set_option autoImplicit false

namespace Lvm6.Node

open Lvm6.Q (planOf eLane6 bOff6 lens6 PE6)
open Lvm.QLink (slenS)
open Lvm6.QK (layEnd capL)

/-- **CC's `openStride`** on V's level (CC §2): the leaf entry (`lb/8 + 5` lanes) and `path` node entries of
13 lanes each. -/
def openStrideV (l : V.Lev) : ℕ := l.lb / 8 + 5 + 13 * l.path

/-- **CC-8's cursor offset** at `fin18` (`finOpenAt nf kq ℓ a = a + 27ℓ + 2nf + 10 + 9kq`; `ℓ = 4`, `nf = 12`,
`kq = 2`). -/
def finOff18 : ℕ := 27 * 4 + 2 * 12 + 10 + 9 * 2

/-- **The lane walk** (see the module doc); `aL` is the lane after the last opening (the current level's first). -/
def laneWalk (L : List V.Lev) : List V.Item → List ℕ → ℕ → ℕ → ℕ → ℕ → Bool
  | [], _, _, _, _, _ => true
  | it :: its, lens, a, off, pend, aL =>
    (a == off / 8 + 5 + pend) &&
      match it with
      | .E k => laneWalk L its lens (layEnd [it] a) off (pend + 2 * k) aL
      | .K k => laneWalk L its lens (layEnd [it] a) off (pend + k) aL
      | .cap i => laneWalk L its lens (layEnd [it] a) off (pend + capL i) aL
      | .open i =>
        let n := V.queriesI L (.open i)
        let off' := off + slenS (lens.take n)
        let lv := L.getD i default
        (off' / 8 + 5 == a + lv.t * openStrideV lv) && (i + 1 != L.length || a == aL + finOff18) &&
          laneWalk L its (lens.drop n) (off' / 8 + 5) off' 0 (off' / 8 + 5)
      | _ =>
        let n := V.queriesI L it
        laneWalk L its (lens.drop n) (layEnd [it] a) (off + slenS (lens.take n)) 0 aL

/-- The plan's lengths from entry 2, and entry 2's stream offset. -/
def lens2 : List ℕ := (lens6 (planOf P18)).drop 2

def off2 : ℕ := bOff6 (planOf P18) 2

/-- **The check**: the walk accepts `sched6 P18` from entry 2's buffer, and every entry of the plan is used. -/
def laneChk : Bool :=
  laneWalk P18.levs (sched6 P18) lens2 (off2 / 8 + 5) off2 0 (off2 / 8 + 5) &&
    (V.queriesOf P18.levs (sched6 P18) == lens2.length)

/-- **The circuit's lanes are the schedule's** at `P18` (kernel). -/
theorem laneChk_P18 : laneChk = true := by decide +kernel

end Lvm6.Node
