-- New for lvm6 (WP-V1, part 1): the executable `V_S` front: FORMAT6's header check, `q₀`, the seed and the
-- schedule driven over the proof bytes (offsets into `π`, byte-array queries, the Merkle climbs and the cap
-- comparison), handing a transcript of offsets and answers to a decision `F`.
import Lvm6VSpec

/-!
# The executable driver of `V_S`

The driver's state `NS`: the next unread byte of `π` (`off`), the absorbed bytes not yet in a query
(`buf`), the chain state (`st`), the caps read so far (`π` offset, height, width), the positions, and
the transcript `acc` (`NV`, newest first): a read is its offset and width, a draw its answer, a cap its shape, an
opening its index, positions and leaf offsets. **`PN π L`** gives the seven primitives of `Lvm6VSpec` over `π`; `driveN` is `Prims.walk` at
`PN`, the same expansion of the schedule as the specification's.

* `rd w`: reject unless `w` bytes remain; append them to `buf`; count the read.
* `draw chk upd`: ask `st ‖ buf` (reject first if it exceeds `queryCap`); the answer `a` is the new
  state; `N = answerBits a` (lanes 0–2); reject unless `chk N`; positions `upd ps N`.
* `cap ht w`: the `32 · 2^capOfL ht w` cap bytes appended to `buf`; the offset recorded.
* `opn i`: for each position `p` the leaf query (the next `8 · min (occ) w` bytes), then `ht − lv` node
  queries `d ‖ s` (bit of `p` zero) or `s ‖ d`, `s` the next 32 bytes, and the top compared with cap
  entry `(p mod 2^ht) / 2^(ht − lv)` read from `π` at the cap's offset.

**`VS6 sh F vk c π`**: `|π| ≥ hdrLen`, the header check (with `HDR.vk = vk`) with the Library's fast hashes on the
header bytes, `q₀`, the seed `a₀ ‖ HDR` (v2.5), the schedule from byte `hdrLen`; at the end
`F π acc && |π| ≤ off`.
-/

set_option autoImplicit false

namespace Lvm6.V

open RecursionFast

/-- A transcript entry of the driver. -/
inductive NV
  /-- A read of `w` bytes at this offset of `π`. -/
  | rd (o w : Nat)
  /-- A draw's answer. -/
  | draw (a : Digest)
  /-- A cap of a commitment of `2^ht` rows of `w` words. -/
  | cap (ht w : Nat)
  /-- An opening of commitment `i` at `ps`: rows of `wd` words carrying `oc`, leaves of `lb` bytes at these
  offsets. -/
  | rows (i : Nat) (ps : List Nat) (wd oc lb : Nat) (os : List Nat)

/-- The driver's state. -/
structure NS where
  off : Nat
  buf : ByteArray
  st : Digest
  caps : List (Nat × Nat × Nat)
  ps : List Nat
  acc : List NV
  /-- Reads so far (the index of the next read). -/
  nr : Nat

/-- A step of the driver. -/
abbrev NStep : Type := NS → (NS → OProg Bool) → OProg Bool

/-- Climb `n` levels from `d` at position `q`, one sibling (the next 32 bytes) a level. -/
def climbN (π : ByteArray) : Nat → Digest → Nat → Nat → (Digest → Nat → OProg Bool) → OProg Bool
  | 0, d, _, off, k => k d off
  | n + 1, d, q, off, k =>
    if π.size < off + 32 then .ret false else
    .query (if q % 2 = 0 then Lvm.digestBytes d ++ π.extract off (off + 32)
      else π.extract off (off + 32) ++ Lvm.digestBytes d)
      fun d' => climbN π n d' (q / 2) (off + 32) k

/-- The cap entry above position `p` is `top`. -/
def capHit (π : ByteArray) (co ht lv p : Nat) (top : Digest) : Bool :=
  let idx := p % 2 ^ ht / 2 ^ (ht - lv)
  decide (idx < 2 ^ lv) && decide (Lvm.digestAt π (co + 32 * idx) = top)

/-- Open the positions in order: leaf query, climb, cap comparison; the leaf offsets to `k`. -/
def openN (π : ByteArray) (co ht lv lb : Nat) : List Nat → Nat → (Nat → List Nat → OProg Bool) → OProg Bool
  | [], off, k => k off []
  | p :: ps, off, k =>
    if π.size - off < lb then .ret false else
    .query (π.extract off (off + lb)) fun d₀ =>
      climbN π (ht - lv) d₀ (p % 2 ^ ht) (off + lb) fun top off' =>
        if capHit π co ht lv p top then openN π co ht lv lb ps off' fun off'' os => k off'' (off :: os)
        else .ret false

/-- **The driver's primitives** over the proof `π`. -/
def PN (π : ByteArray) (L : List Lev) : Prims NStep where
  skip := fun ns k => k ns
  seq := fun f g ns k => f ns fun ns' => g ns' k
  rd := fun w ns k =>
    if π.size - ns.off < w then .ret false else
    k { ns with off := ns.off + w, buf := ns.buf ++ π.extract ns.off (ns.off + w), acc := .rd ns.off w :: ns.acc,
                nr := ns.nr + 1 }
  draw := fun chk upd ns k =>
    if 32 + ns.buf.size ≤ queryCap then
      .query (Lvm.digestBytes ns.st ++ ns.buf) fun a =>
        let N := Lvm.answerBits a
        if chk N then k { ns with st := a, buf := ByteArray.empty, ps := upd ns.ps N, acc := .draw a :: ns.acc }
        else .ret false
    else .ret false
  cap := fun ht w ns k =>
    if π.size < ns.off + 32 * 2 ^ capOfL L ht w then .ret false else
    k { ns with off := ns.off + 32 * 2 ^ capOfL L ht w,
                buf := ns.buf ++ π.extract ns.off (ns.off + 32 * 2 ^ capOfL L ht w),
                caps := ns.caps ++ [(ns.off, ht, w)], acc := .cap ht w :: ns.acc }
  reset := fun ns k => k { ns with ps := [] }
  opn := fun i ns k =>
    match ns.caps[i]? with
    | none => .ret false
    | some (co, ht, w) =>
      openN π co ht (capOfL L ht w) (8 * min (occL L ht w) w) ns.ps ns.off fun off' os =>
        k { ns with off := off', acc := .rows i ns.ps w (occL L ht w) (8 * min (occL L ht w) w) os :: ns.acc }

/-- **The driver** of a schedule. -/
def driveN (π : ByteArray) (L : List Lev) (s : List Item) : NStep := (PN π L).walk L s

/-- The first query. -/
def q0Q : ByteArray := ⟨q06.toArray⟩

/-- **The executable `V_S`** for the decision `F` on the proof and the driver's transcript. -/
def VS6 (sh : VShape) (F : ByteArray → List NV → Bool) (vk c : Digest) (π : Proof) : OProg Bool :=
  if hdrLen sh ≤ π.size then
    if hdrOkWith leafStmtF nodeStmtF sh.nStar vk c (π.extract 0 (hdrLen sh)) &&
        decide (32 + hdrLen sh ≤ queryCap) then
      .query q0Q fun a₀ =>
        .query (Lvm.digestBytes a₀ ++ π.extract 0 (hdrLen sh))
          fun st => driveN π sh.levs sh.sched ⟨hdrLen sh, ByteArray.empty, st, [], [], [], 0⟩ fun ns =>
            .ret (F π ns.acc && decide (π.size ≤ ns.off))
    else .ret false
  else .ret false

end Lvm6.V
