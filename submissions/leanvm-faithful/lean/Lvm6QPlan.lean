-- New for lvm6 (WP CA). Re-targets season 1's trace plan (`LvmReassemble`: `plan`, `Good`, `contrib`,
-- `reassemble`) to FORMAT6 v2.2 §3–§6: the `q₀` of lvm6, the seed `a₀ ‖ c ‖ HDR`, binds, grinds on the
-- ground draws, positions `⌊128/ht⌋` per draw from `N = c₀ + 2^64·c₁`, caps absorbed and never hashed.
import LvmReassemble

/-!
# The lvm6 trace plan (CA-1)

`V_S` (FORMAT6 §6) asks a fixed sequence of oracle queries. **The plan** describes that sequence
entry by entry, with no trace and no oracle: the entry's class (FORMAT6 §3), its query length, and
what links it to earlier entries. It is computed by a walk (`walk`) over the schedule's items
(`It`, FORMAT6 §S's `Item`) and the level geometry (`Lv`, FORMAT6 §5).

* `q0`: the 7 bytes `"lvm6/1", 0`;
* `seed`: `a₀ ‖ c ‖ HDR` (`vk` is a field of `HDR`, checked by `V_S`'s parse: `ChildHdr6`);
* `fs st g`: a chain query `st ‖ buf` (§4), `st` the answer of entry `st`; `g ≥ 1` on a ground draw
  (`PowOK6`: its PoW lane, bytes 16–23 of the answer, is `< 2^(64-g)`; checked by the decision `F`),
  `g = 0` on a further draw or a bind `B`;
* `leaf`: an opened leaf;
* `node pd sh h lvl cap`: a node query `left ‖ right` at height `lvl` of the position
  `(N(a_pd) >> sh) mod 2^h` (§5: `N` the draw's 128-bit value); the current node is the left half iff
  bit `lvl` of the position is `0`; on the last height `cap = some (ce, co, path)`: the answer is the
  cap node `pos >> path`, the 32 bytes at `co + 32·(pos >> path)` of entry `ce`'s query (the chain
  query that absorbed the cap).

**`Good6 c tr i e`** is what `Q_link` asserts of entry `i` (CA-1); **`LinkOk6`** says every entry
is good and the trace has the plan's length. **`reassemble6`** is the proof the trace carries:
the seed's `HDR`, then every message, leaf and sibling in trace order. **`drive6`** is the
plan-driven query program: it builds every query from `π` and the earlier answers, checks every
cap, and at the end returns the decision `F tr` if `π` is used up (`Lvm6QDrive`:
`replay6`, a linked trace replays it).
-/

set_option autoImplicit false

namespace Lvm6.Q

open RecursionFast Lvm Lvm.Replay

/-! ## Bytes of an answer (FORMAT6 §1, §4, §5) -/

/-- `q₀`: `"lvm6/1"`, 0 (FORMAT6 §3). -/
def q06 : List UInt8 := [0x6C, 0x76, 0x6D, 0x36, 0x2F, 0x31, 0x00]

/-- The first query as a byte array. -/
def q06Query : ByteArray := ⟨q06.toArray⟩

/-- The draw value `N = c₀ + 2^64·c₁` of an answer (lanes 0–1; FORMAT6 §5 positions). -/
def drawN (a : Digest) : ℕ := u64At (digestBytes a) 0 + 2 ^ 64 * u64At (digestBytes a) 8

/-- The PoW lane of an answer (lane 2, FORMAT6 §4). -/
def powLane (a : Digest) : ℕ := u64At (digestBytes a) 16

/-- The ground-draw rule at grind `g` (`g = 0`: no condition). -/
def powOK (g : ℕ) (a : Digest) : Bool := decide (powLane a < 2 ^ (64 - g))

/-- The positions per draw at `h` bits (FORMAT6 §5: `⌊128/h⌋`). -/
def ppa (h : ℕ) : ℕ := 128 / h

/-! ## The schedule's items and the level geometry -/

/-- FORMAT6 §S's `Item` (CA's copy; WP-S's `Lvm6.Item` maps onto it constructor for constructor).
`E k`: `k` scalars (16 B); `K k`: `k` words (8 B); `cap i`: level `i`'s cap; `G g`: a nonce (8 B)
then one draw at grind `g`; `D k`: `k` further draws; `B`: a bind (one draw, value ignored; FORMAT6
v2.2 §4); `open i`: level `i`'s openings. -/
inductive It where
  | E (k : ℕ)
  | K (k : ℕ)
  | cap (i : ℕ)
  | G (g : ℕ)
  | D (k : ℕ)
  | B
  | «open» (i : ℕ)
  deriving DecidableEq, Repr, Inhabited

/-- A Merkle level (FORMAT6 §5): `2^ht` positions, a cap of `2^lv` nodes, leaves of `leaf` bytes,
`t` openings; its positions are the `⌈t/⌊128/ht⌋⌉` draws that end `gap` draws before the opening
(`gap = 1` at levels 0–3, where `λ` is drawn in between; `0` at level 4). -/
structure Lv where
  ht : ℕ
  lv : ℕ
  leaf : ℕ
  t : ℕ
  gap : ℕ
  deriving DecidableEq, Repr, Inhabited

/-- The number of position draws of a level. -/
def Lv.d (L : Lv) : ℕ := (L.t + ppa L.ht - 1) / ppa L.ht

/-- The path length (node queries per opening). -/
def Lv.path (L : Lv) : ℕ := L.ht - L.lv

/-! ## The plan -/

/-- What an entry is and what links it to earlier entries. -/
inductive EK6 where
  | q0
  | seed
  | fs (st g : ℕ)
  | leaf
  | node (pd sh h lvl : ℕ) (cap : Option (ℕ × ℕ × ℕ))
  deriving DecidableEq, Repr, Inhabited

/-- A planned entry: what it is, its query's length in bytes. -/
structure PE6 where
  k : EK6
  len : ℕ
  deriving DecidableEq, Repr, Inhabited

/-- The walk's state. -/
structure WS6 where
  /-- The next entry. -/
  i : ℕ
  /-- Bytes read since the last draw. -/
  pend : ℕ
  /-- The entry whose answer is the chain state. -/
  st : ℕ
  /-- Caps read, not yet absorbed: level, offset in the pending bytes, bytes. -/
  pcaps : List (ℕ × ℕ × ℕ)
  /-- Caps absorbed: level, entry, offset in its query, bytes. -/
  caps : List (ℕ × ℕ × ℕ × ℕ)
  /-- The draws of the current group so far (its ground draw `G` and the further draws after it; 0 after a
  bind or an opening): the positions of an opening are exactly the last group's first `d` draws. -/
  run : ℕ
  /-- Every static condition so far. -/
  ok : Bool
  deriving Repr

/-- A draw at entry `i` absorbs the pending caps. -/
def WS6.settle (w : WS6) : WS6 :=
  { w with caps := w.pcaps.map (fun c => (c.1, w.i, 32 + c.2.1, c.2.2)) ++ w.caps, pcaps := [] }

/-- The entries of the openings of level `L`: positions from entry `pd0` on, cap `(ce, co)`. -/
def openPlan6 (L : Lv) (pd0 ce co : ℕ) : List PE6 :=
  (List.range L.t).flatMap fun j => ⟨.leaf, L.leaf⟩ :: (List.range L.path).map fun lvl =>
    ⟨.node (pd0 + j / ppa L.ht) (j % ppa L.ht * L.ht) L.ht lvl
      (if lvl + 1 = L.path then some (ce, co, L.path) else none), 64⟩

/-- **One item of the walk**: its entries and the next state. -/
def walkIt (lv : ℕ → Lv) (w : WS6) : It → List PE6 × WS6
  | .E k => ([], { w with pend := w.pend + 16 * k })
  | .K k => ([], { w with pend := w.pend + 8 * k })
  | .cap i => ([], { w with pcaps := (i, w.pend, 32 * 2 ^ (lv i).lv) :: w.pcaps,
                             pend := w.pend + 32 * 2 ^ (lv i).lv })
  | .G g => ([⟨.fs w.st g, 40 + w.pend⟩],
      { w.settle with i := w.i + 1, pend := 0, st := w.i, run := 1,
                      ok := w.ok && decide (1 ≤ g) && decide (g ≤ 23) })
  | .B => ([⟨.fs w.st 0, 32 + w.pend⟩],
      { w.settle with i := w.i + 1, pend := 0, st := w.i, run := 0 })
  | .D k => ((List.range k).map (fun m => ⟨.fs (if m = 0 then w.st else w.i + m - 1) 0, 32⟩),
      { w with i := w.i + k, st := if k = 0 then w.st else w.i + k - 1, run := w.run + k,
               ok := w.ok && w.pend == 0 && w.pcaps.isEmpty && decide (1 ≤ w.run) })
  | .open i =>
    let L := lv i
    match w.caps.find? (·.1 == i) with
    | none => ([], { w with ok := false })
    | some (_, ce, co, nb) =>
      (openPlan6 L (w.i - 1 - L.gap - (L.d - 1)) ce co,
        { w with i := w.i + L.t * (1 + L.path), run := 0,
                 ok := w.ok && w.pend == 0 && w.pcaps.isEmpty && decide (1 ≤ L.d) &&
                   decide (L.d + L.gap = w.run) && decide (1 ≤ L.path) &&
                   decide (L.lv ≤ L.ht) && decide (1 ≤ L.ht) && decide (L.ht ≤ 128) &&
                   decide (nb = 32 * 2 ^ L.lv) })

/-- The walk over a list of items. -/
def walk (lv : ℕ → Lv) : WS6 → List It → List PE6 × WS6
  | w, [] => ([], w)
  | w, it :: its =>
    let a := walkIt lv w it
    let b := walk lv a.2 its
    (a.1 ++ b.1, b.2)

/-- The walk's start: entry 2 (after `q₀` and the seed), state = the seed's answer. -/
def w06 : WS6 := ⟨2, 0, 1, [], [], 0, true⟩

/-- **The plan** of a schedule: `q₀`, the seed (`64 + |HDR|` bytes), then the items' entries. -/
def plan6 (lv : ℕ → Lv) (hdrLen : ℕ) (its : List It) : List PE6 :=
  ⟨.q0, 7⟩ :: ⟨.seed, 64 + hdrLen⟩ :: (walk lv w06 its).1

/-- **The walk's static conditions**: every check held, nothing is pending at the end (FORMAT6 §4:
after the last draw nothing is read). -/
def walkOK (lv : ℕ → Lv) (its : List It) : Bool :=
  let w := (walk lv w06 its).2
  w.ok && w.pend == 0 && w.pcaps.isEmpty

/-! ## References point backwards -/

/-- Entry `i`'s links name only earlier entries (and an entry after the seed has a predecessor). -/
def refsOK1 (i : ℕ) (e : PE6) : Bool :=
  match e.k with
  | .q0 => i == 0 && e.len == 7
  | .seed => i == 1 && decide (64 ≤ e.len)
  | .fs st _ => decide (st < i) && decide (32 ≤ e.len)
  | .leaf => decide (1 ≤ i)
  | .node pd _ h _ cap => decide (pd < i) && decide (1 ≤ i) && e.len == 64 && decide (1 ≤ h) &&
      match cap with
      | none => true
      | some (ce, _, path) => decide (ce < i) && decide (path ≤ h)

/-- The entries `es` from index `i` on: every link points backwards. -/
def refsFrom : ℕ → List PE6 → Bool
  | _, [] => true
  | i, e :: es => refsOK1 i e && refsFrom (i + 1) es

/-- **Every link of the plan points backwards** (decided per `Shape`). -/
def refsOK (P : List PE6) : Bool := refsFrom 0 P

theorem refsFrom_get : ∀ (P : List PE6) (i k : ℕ), refsFrom i P = true → k < P.length →
    refsOK1 (i + k) (P.getD k default) = true
  | [], _, _, _, hk => absurd hk (Nat.not_lt_zero _)
  | e :: es, i, 0, h, _ => by
    simp only [refsFrom, Bool.and_eq_true] at h; simpa using h.1
  | e :: es, i, k + 1, h, hk => by
    simp only [refsFrom, Bool.and_eq_true] at h
    have := refsFrom_get es (i + 1) k h.2 (by simpa using hk)
    rw [show i + (k + 1) = i + 1 + k by omega]; simpa using this

theorem refsOK_get {P : List PE6} (h : refsOK P = true) {k : ℕ} (hk : k < P.length) :
    refsOK1 k (P.getD k default) = true := by
  simpa using refsFrom_get P 0 k h hk

/-! ## What `Q_link` asserts, what an entry carries -/

/-- The position of a node entry: `(N(a_pd) >> sh) mod 2^h`. -/
def posOf (tr : Trace) (pd sh h : ℕ) : ℕ := (drawN (aOf tr pd) >>> sh) % 2 ^ h

/-- **Entry `i` of `tr` meets its plan** (FORMAT6 §3–§5), for the statement `c` the trace's verifier
was run on. -/
def Good6 (c : Digest) (tr : Trace) (i : ℕ) (e : PE6) : Prop :=
  (qOf tr i).size = e.len ∧
  match e.k with
  | .q0 => bl (qOf tr i) = q06
  | .seed => (bl (qOf tr i)).take 64 = (aOf tr 0).toList ++ c.toList
  | .fs st _ => (bl (qOf tr i)).take 32 = (aOf tr st).toList
  | .leaf => True
  | .node pd sh h lvl cap =>
    (if (posOf tr pd sh h >>> lvl) % 2 = 0 then (bl (qOf tr i)).take 32 else (bl (qOf tr i)).drop 32) =
        (aOf tr (i - 1)).toList ∧
      match cap with
      | none => True
      | some (ce, co, path) => aOf tr i = digestAt (qOf tr ce) (co + 32 * (posOf tr pd sh h >>> path))

/-- **Every grind of the trace holds** (FORMAT6 §4; part of the decision `F`, not of `Q_link`). -/
def PowOK6 (P : List PE6) (tr : Trace) : Prop :=
  ∀ i < P.length, ∀ st g, (P.getD i default).k = .fs st g → powOK g (aOf tr i) = true

/-- **The trace is a trace of the plan** (CA-1): the plan's length, every entry good. -/
def LinkOk6 (P : List PE6) (c : Digest) (tr : Trace) : Prop :=
  tr.length = P.length ∧ ∀ i < tr.length, Good6 c tr i (P.getD i default)

/-- **The proof bytes entry `i` carries**: the seed its `HDR`, a chain query its message, a leaf
its bytes, a node query its sibling (the compare rule: the right half if the left half is the
previous answer, else the left half). -/
def contrib6 (tr : Trace) (i : ℕ) (e : PE6) : List UInt8 :=
  match e.k with
  | .q0 => []
  | .seed => (bl (qOf tr i)).drop 64
  | .fs _ _ => (bl (qOf tr i)).drop 32
  | .leaf => bl (qOf tr i)
  | .node .. =>
    if (bl (qOf tr i)).take 32 = (aOf tr (i - 1)).toList then (bl (qOf tr i)).drop 32
    else (bl (qOf tr i)).take 32

/-- The contributions of the first `k` entries of `P`. -/
def bodyTo (tr : Trace) (P : List PE6) (k : ℕ) : List UInt8 :=
  (List.range k).flatMap fun i => contrib6 tr i (P.getD i default)

/-- **`reassemble6 P tr`**: the proof the trace carries, `HDR ‖ BODY` (FORMAT6 §2). -/
def reassemble6 (P : List PE6) (tr : Trace) : ByteArray := ⟨(bodyTo tr P P.length).toArray⟩

/-! ## The plan-driven query program -/

/-- The query entry `i` asks, from `π` at the cursor `off` and the earlier entries `tr`, with the
next cursor. -/
def mkQ (c : Digest) (π : ByteArray) (off : ℕ) (tr : Trace) (i : ℕ) (e : PE6) : ByteArray × ℕ :=
  match e.k with
  | .q0 => (q06Query, off)
  | .seed => (digestBytes (aOf tr 0) ++ digestBytes c ++ π.extract off (off + (e.len - 64)),
      off + (e.len - 64))
  | .fs st _ => (digestBytes (aOf tr st) ++ π.extract off (off + (e.len - 32)), off + (e.len - 32))
  | .leaf => (π.extract off (off + e.len), off + e.len)
  | .node pd sh h lvl _ =>
    let sib := π.extract off (off + 32)
    let cur := digestBytes (aOf tr (i - 1))
    (if (posOf tr pd sh h >>> lvl) % 2 = 0 then cur ++ sib else sib ++ cur, off + 32)

/-- The check after entry `i`'s answer (the last entry of `tr`): a cap. (Grinds are the decision's,
`PowOK6`, as in season 1, where the PoW rows are the typed backend's.) -/
def postOK (tr : Trace) (i : ℕ) (e : PE6) : Bool :=
  match e.k with
  | .node pd sh h _ (some (ce, co, path)) =>
    aOf tr i == digestAt (qOf tr ce) (co + 32 * (posOf tr pd sh h >>> path))
  | _ => true

/-- Run the entries `es` from entry `i`, cursor `off`, earlier entries `tr` (in order). -/
def drv (c : Digest) (π : ByteArray) (F : Trace → Bool) : List PE6 → ℕ → ℕ → Trace → OProg Bool
  | [], _, off, tr => .ret (off == π.size && F tr)
  | e :: es, i, off, tr =>
    let qo := mkQ c π off tr i e
    .query qo.1 fun a =>
      if postOK (tr ++ [(qo.1, a)]) i e then drv c π F es (i + 1) qo.2 (tr ++ [(qo.1, a)])
      else .ret false

/-- **The plan-driven query program**: every entry of `P` in order, then `F` on the trace if `π` is
used up. -/
def drive6 (P : List PE6) (c : Digest) (π : ByteArray) (F : Trace → Bool) : OProg Bool :=
  drv c π F P 0 0 []

end Lvm6.Q
