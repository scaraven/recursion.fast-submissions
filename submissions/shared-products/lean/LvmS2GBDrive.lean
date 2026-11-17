-- New for lvm2 MP-B cap pruning (CAP-L, 2026-11-17): `V_S`'s parse and query driver at S2GB (lead freeze P0 (2)–(6),
-- RE-FREEZE P1). Phase 1 (G0-2): the definitions; S2GS's driver (`LvmDriver`) is untouched.
import LvmS2GBSched
import LvmDriver

/-!
# The S2GB driver (`capPrune`)

Per opened level `L` (cap exponent `m = L.cap`, path `D = L.path`, sent cap exponent `c = capSendBits`), in the order
of the frozen protocol:

* **paths** (`pathsB`): for each sampled position `q`, in sample order, the leaf query and `D` node queries (siblings
  inline in π, as S2GS); no cap check inline;
* **layer** (`layerB`): `X = {q >> D}`; for `x < 2^m` ascending, `L[x]` is the top of the first path with `q >> D = x`,
  else the next 32 bytes of the π tail; `V` rejects unless every path's top is `L[q >> D]`;
* **heap** (`heapB`): for `k = 2^m − 1` down to `2^c`, one node query `node (2k) ‖ node (2k+1)`, its answer `A[k]`
  (`node k` is `L[k − 2^m]` for `k ≥ 2^m`, else `A[k]`);
* **cap check**: `node (2^c + i)` is the sent cap node `i` for `i < 2^c`.

The tail cursor starts at `piStatic p`; at the end the body cursor is `piStatic p` and the tail cursor `|π|`.
`parseOkB` checks `piStatic ≤ |π| ≤ piStatic + tailMax` (the exact length is the driver's end check).
-/

set_option autoImplicit false

namespace Lvm

open RecursionFast

/-- The paths of an opening: per position the leaf query and the climb; the tops in sample order. -/
def pathsB (π : ByteArray) (L : Level) : List Nat → DSt → List Digest → (DSt → List Digest → OProg Bool) → OProg Bool
  | [], s, acc, k => k s acc.reverse
  | q :: qs, s, acc, k =>
    ask (π.extract s.off (s.off + L.row)) { s with off := s.off + L.row } fun s leaf =>
      climb π q L.path 0 leaf s fun s top => pathsB π L qs s (top :: acc) k

/-- **The cap layer** `L[0 … 2^m)` from the (position, top) pairs and the π tail from `tail`: the first path's top
at a covered `x`, else the next tail node; with the tail cursor after it. -/
def layerB (π : ByteArray) (m D : Nat) (qt : List (Nat × Digest)) (tail : Nat) : Array Digest × Nat :=
  (List.range (2 ^ m)).foldl (fun acc x =>
    match qt.find? (fun e => e.1 >>> D == x) with
    | some e => (acc.1.push e.2, acc.2)
    | none => (acc.1.push (digestAt π acc.2), acc.2 + nodeBytes)) (#[], tail)

/-- Heap node `k`: the layer node `L[k − 2^m]` for `k ≥ 2^m`, else the heap answer `A[k]`. -/
def nodeB (lay A : Array Digest) (m k : Nat) : Digest :=
  if 2 ^ m ≤ k then lay.getD (k - 2 ^ m) zeroDigest else A.getD k zeroDigest

/-- **The heap**: `n` node queries for `k = kk, kk − 1, …`, each `node (2k) ‖ node (2k+1)`, `A[k]` its answer. -/
def heapB (lay : Array Digest) (m : Nat) :
    (n kk : Nat) → Array Digest → DSt → (DSt → Array Digest → OProg Bool) → OProg Bool
  | 0, _, A, s, k => k s A
  | n + 1, kk, A, s, k =>
    ask (digestBytes (nodeB lay A m (2 * kk)) ++ digestBytes (nodeB lay A m (2 * kk + 1))) s fun s a =>
      heapB lay m n (kk - 1) (A.set! kk a) s k

/-- **One S2GB opening**: paths, layer (tail from `tail`), covered check, heap (`k = 2^m − 1` down to `2^c`), cap
check against the `2^c` sent nodes at `capOff`; then `k` with the tail cursor after the level's tail nodes. -/
def openLoopB (π : ByteArray) (L : Level) (c capOff : Nat) (s : DSt) (tail : Nat)
    (k : DSt → Nat → OProg Bool) : OProg Bool :=
  let qs := s.pos
  pathsB π L qs s [] fun s tops =>
    let qt := qs.zip tops
    let lt := layerB π L.cap L.path qt tail
    if qt.all (fun e => e.2 == lt.1.getD (e.1 >>> L.path) zeroDigest) then
      heapB lt.1 L.cap (2 ^ L.cap - 2 ^ c) (2 ^ L.cap - 1) (Array.replicate (2 ^ L.cap) zeroDigest) s fun s A =>
        if (List.range (2 ^ c)).all (fun i => nodeB lt.1 A L.cap (2 ^ c + i) == digestAt π (capOff + nodeBytes * i))
        then k s lt.2 else .ret false
    else .ret false

/-- **Run the items at S2GB** (`driveItems` with the tail cursor `t`): a cap item moves the body cursor by its
`2^capSendBits` nodes; an opening is `openLoopB`. -/
def driveItemsB (p : Params) (π : ByteArray) :
    List Item → DSt → Nat → (DSt → Nat → OProg Bool) → OProg Bool
  | [], s, t, k => k s t
  | .read m :: rest, s, t, k => driveItemsB p π rest { s with off := s.off + eBytes * m } t k
  | .readW m w :: rest, s, t, k => driveItemsB p π rest { s with off := s.off + w * m } t k
  | .cap c r :: rest, s, t, k =>
    driveItemsB p π rest
      { s with caps := (r, s.off) :: s.caps, off := s.off + nodeBytes * 2 ^ p.capSendBits r.lv c } t k
  | .sample :: rest, s, t, k => fsQuery π s fun s _ => driveItemsB p π rest s t k
  | .positions r :: rest, s, t, k =>
    let L := p.level r
    posLoop π L.height L.nPosQ L.t { s with pos := [] } fun s => driveItemsB p π rest s t k
  | .opening r :: rest, s, t, k =>
    match capOffset s r with
    | none => .ret false
    | some capOff =>
      if (p.level r).row ≤ queryCap then
        openLoopB π (p.level r) (p.capSendBits r.lv (p.level r).cap) capOff s t fun s t =>
          driveItemsB p π rest { s with pend := s.off } t k
      else .ret false

/-- **The S2GB driver**: `drive` with the tail cursor from `piStatic p`; at the end the body cursor is `piStatic p`,
the tail cursor `|π|`, and the decision `F` holds on the stream. -/
def driveB (p : Params) (π : ByteArray) (F : ByteArray → Bool) : OProg Bool :=
  .query q0Query fun a₀ =>
    let sq := seedQuery π a₀ (headerBytesP p)
    .query sq fun st₀ =>
      driveItemsB p π (schedule p)
        ⟨headerBytesP p, headerBytesP p, st₀, [(sq, st₀), (q0Query, a₀)], [], []⟩ (piStatic p)
        fun s t => .ret (s.off == piStatic p && t == π.size && F (streamOf s.log))

/-- **`V_S`'s native checks at S2GB**: `parseOkS` with the size check `piStatic ≤ |π| ≤ piStatic + tailMax`. -/
def parseOkB (p : Params) (vk c : Digest) (π : ByteArray) : Bool :=
  piStatic p ≤ π.size && π.size ≤ piStatic p + tailMax p && π.get! 0 == 0x53 && zeroBytes π 1 7 &&
    let hd := Header.ofProof π
    (hd.b == 0 || hd.b == 1) && hd.vk == vk && 1 ≤ hd.n && hd.n ≤ chainCap && hd.n ≤ 2 ^ p.logN &&
    (if hd.b = 0 then hd.cL == zeroDigest && c == hd.stmt else c == hd.stmt)

end Lvm
