-- New for `flock-recursive` (BLUEPRINT revision 4.1, B-12; stage R4, P4a's F1).
import FRSoundness4Qry
import FRSegment

/-!
# P4a's F1: the segment program and `V_A` read the same `n`

A segment's length `n` is read twice:

* `V_A` reads it through `segView`: `rdLE64 π 81`, the 8 little-endian bytes at 81
  (`stmt` bytes 33–40, `stmt` at offset 48);
* the segment program's `lastOps` (in the `stmt` phase, number 1 of `phasesOf seq4`) reads
  `idxOfF 24 (digestAt π (so + 33)) 0`, the 24 low bits of the digest at `so + 33`, with
  `so = fieldOffOf seq4 fStmt + phaseOffOf seq4 1 fStmt`.

**`stmtOff4`**: `so = 48` (a certificate on `seq4`'s format). **`lastN_eq`**: the program's index is
`rdLE64 π 81 mod 2^24`. **`lastN_of_le`**: on `V_A`'s range (`n ≤ cap ≤ 2^18`) the two are equal.
So `V_A`'s `1 ≤ nᵢ ≤ cap` is a fact about the very `n` the segment program's last block reads:
no soundness gap.
-/

namespace FR.Snd.R4
open RecursionFast Rev4

/-- **The statement field's offset** in `seq4`'s format, as `genPhase4` computes it for phase 1. -/
theorem stmtOff4 : fieldOffOf seq4 fStmt + phaseOffOf seq4 1 fStmt = 48 := by
  rw [seq4_eq]; decide +kernel

theorem dByte_bytesAt (π : ByteArray) (o k : ℕ) (hk : k < 32) :
    dByte (bytesAt π o 32) k = (byteAt π (o + k)).toNat := by
  rw [dByte, dif_pos hk]; simp [bytesAt]

/-- **The program's index is `V_A`'s length mod `2^24`.** -/
theorem lastN_eq (π : ByteArray) :
    idxOfF 24 (digestAt π (48 + 33)) 0 = rdLE64 π 81 % 2 ^ 24 := by
  rw [digestAt_eq, idxOfF, if_pos (by norm_num), dWin, dByte_bytesAt _ _ _ (by norm_num),
    dByte_bytesAt _ _ _ (by norm_num), dByte_bytesAt _ _ _ (by norm_num),
    dByte_bytesAt _ _ _ (by norm_num)]
  simp only [rdLE64, List.range_succ, List.range_zero, List.map_append, List.map_cons, List.map_nil,
    List.sum_append, List.sum_cons, List.sum_nil, List.nil_append]
  have h := fun k => UInt8.toNat_lt (byteAt π (81 + k))
  have h0 := h 0; have h1 := h 1; have h2 := h 2; have h3 := h 3
  simp only [Nat.one_shiftLeft]
  norm_num
  omega

/-- **On `V_A`'s range the two readings agree.** -/
theorem lastN_of_le (π : ByteArray) (h : rdLE64 π 81 ≤ 2 ^ 18) :
    idxOfF 24 (digestAt π (fieldOffOf seq4 fStmt + phaseOffOf seq4 1 fStmt + 33)) 0 = rdLE64 π 81 := by
  rw [stmtOff4, lastN_eq, Nat.mod_eq_of_lt (by omega)]

/-- **`segView`'s `n` is the segment program's last-block index** on every view `V_A` accepts
(`n ≤ cap ≤ 2^18`). -/
theorem segView_lastN {π : Proof} {v : SegView} (hv : segView π = some v) (hcap : v.n ≤ v.kind.cap) :
    idxOfF 24 (digestAt π (fieldOffOf seq4 fStmt + phaseOffOf seq4 1 fStmt + 33)) 0 = v.n := by
  simp only [segView, Option.map_eq_some_iff] at hv
  obtain ⟨κ, -, rfl⟩ := hv
  have hc : κ.cap ≤ 2 ^ 18 := by cases κ <;> decide
  exact lastN_of_le π (le_trans hcap hc)

/-! ## Controls -/

/-- Control (negative): beyond `2^24` the readings differ (`n = 2^24` is read as index `0`), so
the range hypothesis of `lastN_of_le` is needed. -/
theorem lastN_wrap (π : ByteArray) (h : rdLE64 π 81 = 2 ^ 24) : idxOfF 24 (digestAt π (48 + 33)) 0 = 0 := by
  rw [lastN_eq, h, Nat.mod_self]

/-- Control (positive): `n = 5` is read as `5` by both. -/
theorem lastN_five (π : ByteArray) (h : rdLE64 π 81 = 5) : idxOfF 24 (digestAt π (48 + 33)) 0 = 5 := by
  rw [lastN_eq, h]; norm_num

end FR.Snd.R4
