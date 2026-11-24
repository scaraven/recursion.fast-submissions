-- New for lvm6 (WP CA). The frozen interface of the child-verification phases CA owns (stage doc
-- `docs/lvm6/stages/CA-circuit.md`): the stream as a trace, what `Q_link` and `Q_sig` conclude.
import Lvm6QDrive
import LvmQLinkSound
import LvmQSigDefs

/-!
# CA's frozen statements

The node circuit reads the child's signed trace from the committed `STREAM` block (FORMAT6 §T,
slots 33–34) as stream words `ws`: the bytes `Σ = 0x54 ‖ traceBytes tr'` packed 8 to a word
(season 1's stream; with `|q₀| = 7` every query after `q₀` starts on a word, FORMAT6 §3).

* **`decode6 P ws`**: the trace the stream holds, entry lengths from the plan.
* **`QLinkConcl P c ws`** (CA-2, what `qlink6_sound` concludes): the decoded trace meets its plan
  for the child's statement `c` (`LinkOk6`: the hash chain, the seed, every Merkle path and
  cap) and the trace sponge's last block is padded (`PadOkB`, the hypothesis of CB's trace digest).
* **`ChildHdr6 vk c tr`** (CA-3, from `qsig6_sound`): the child's `HDR` (the seed's bytes from 32: the
  seed is `a₀ ‖ HDR`, FORMAT6 v2.5) passes `V_S`'s header and statement checks (FORMAT6 §2) for `vk`
  and statement `c`.
* **`StreamMap6`**: CA's proposal for the three `STREAM` base offsets CD fixes (FORMAT6 §T).
-/

set_option autoImplicit false

namespace Lvm6.Q

open RecursionFast Lvm Lvm.Replay Lvm.QLink

/-! ## The stream as a trace -/

/-- **The trace the stream words hold**: entries `enc64 |q| ‖ q ‖ a` from byte 1 (after the tag). -/
def decode6 (P : List PE6) (ws : List Word) : Trace := readEntries (wordsBytes ws) 1 (P.map PE6.len)

/-- The hashed length of the stream: the tag, then every entry's `8 + |q| + 32` bytes. -/
def hashedLen6 (P : List PE6) : ℕ := 1 + (P.map fun e => 40 + e.len).sum

/-- **What `Q_link` concludes** (CA-2): the stream's trace is a trace of the plan for `c`,
and the trace sponge's padding is in place. -/
def QLinkConcl (P : List PE6) (c : Digest) (ws : List Word) : Prop :=
  LinkOk6 P c (decode6 P ws) ∧ Lvm.QLink.PadOkB (wordsBytes ws) (hashedLen6 P)

/-! ## The child's header (FORMAT6 §2) -/

/-- The magic word `"Slvm6", 0, 0, 1` (FORMAT6 §2, bytes 0–7 of `π`). -/
def magic6 : List UInt8 := [0x53, 0x6C, 0x76, 0x6D, 0x36, 0x00, 0x00, 0x01]

/-- The little-endian number of the 8 bytes of `l` at `o`. -/
def le8 (l : List UInt8) (o : ℕ) : ℕ := ((List.range 8).map fun t => (l.getD (o + t) 0).toNat * 2 ^ (8 * t)).sum

/-- The 32 bytes of `l` at `o` as a digest. -/
def dig32 (l : List UInt8) (o : ℕ) : Digest := Vector.ofFn fun x : Fin 32 => l.getD (o + x.val) 0

/-- The child's `HDR`: the seed's bytes from 32 (FORMAT6 v2.5: the seed is `a₀ ‖ HDR`). -/
def hdrOf6 (tr : Trace) : List UInt8 := (bl (qOf tr 1)).drop 32

/-- **The child's header passes `V_S`'s parse checks for `vk` and statement `c`** (CA-3): magic,
`b ∈ {0, 1}`, `n = 2^18`, `b = 0 → c' = 0`, the `vk` field, and `c = leafStmt h n` (`b = 0`) or
`nodeStmt c' (leafStmt h n)`. -/
def ChildHdr6 (vk c : Digest) (tr : Trace) : Prop :=
  let H := hdrOf6 tr
  let b := le8 H 8
  let n := le8 H 16
  H.take 8 = magic6 ∧ (b = 0 ∨ b = 1) ∧ n = 2 ^ 18 ∧ (b = 0 → dig32 H 56 = zeroDigest) ∧ dig32 H 88 = vk ∧
    c = (if b = 0 then leafStmt (dig32 H 24) n else nodeStmt (dig32 H 56) (leafStmt (dig32 H 24) n))

/-! ## The `STREAM` map (CA's proposal; CD fixes the constants) -/

/-- Where the child's data sits in the stream: stream word `w` is the `K` cell `sb + w`
(`w = r + 2^19·(slot − 33)` in the committed stack); the trace from word 0; `σ'` from word `oSig`
in `readSig`'s order (index, 133 × 4, 16 × 4); `σ_leaf` from word `oSig + 597`, its chain values in
`permC` order (`sigAtP`: chain `i` at `1 + 4·posC i`), as roll #33. -/
structure StreamMap6 where
  sb : ℕ
  oSig : ℕ
  deriving DecidableEq, Repr, Inhabited

/-- The stream word of the seed query's first byte (entry 1 starts at byte `1 + 8 + 7 + 32 = 48`,
its query at byte 56). -/
def seedW : ℕ := 7

/-- The stream word of `HDR` word `k` (FORMAT6 v2.5: the seed is `a₀ ‖ HDR`, 4 words before `HDR`). -/
def hdrW (k : ℕ) : ℕ := seedW + 4 + k

end Lvm6.Q
