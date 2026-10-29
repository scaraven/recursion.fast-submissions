-- New for `flock-recursive` (stage S-H4, pass 11, item 6): controls for the node output's programs and
-- for `nd`. Outside the certificate's closure (imported by `FR` only).
import FRXNd4

/-!
# Controls for the node output (`outIR4`) and the node branch (`nd`)

Each control shows a definition the decode law relies on doing what its statement says, and not
something weaker:

* the chain loader's **redirect** (`ldIx`, `dV`): only the stream's last block is read from the
  candidate final block, and only when the aggregate has fewer than `maxK` segments;
* the **ladder** (`mOfB_eq`): `'P'`, `'K'`/`'M'` and the rest give three different ladders;
* the **path offset** (`offB`): bit `t` of the index picks the `l` (`0`) or `r` (`4`) field;
* the **segment count** (`kc`): it stops at the first failing sub-slot (a later selected one does
  not count);
* the **node branch** is not empty and outputs at most `outCap` words.
-/

namespace FR.X.OutCtrl

open RecursionFast FR.X FR.X.X4 FR.Rev4

/-- (+/−) **The redirect**: at `N2`'s aggregate with one segment, chain word `8·jL` (the stream's last
block) is read from the candidate final block `finB .N2 0` (`blkOf`'s), word `8·jL − 1` (the block
before) from the main chain; with `maxK = 2` segments there is no redirect (`dV = 0`). -/
theorem redirect_ctl :
    ldIx (8 * N4c.chBase .N2 1) (1 * (N4c.segB - 1) / 2 ^ 6) (dV .N2 0 1) (8 * (1 * (N4c.segB - 1) / 2 ^ 6)) =
      8 * N4c.finB .N2 0 ∧
    ldIx (8 * N4c.chBase .N2 1) (1 * (N4c.segB - 1) / 2 ^ 6) (dV .N2 0 1) (8 * (1 * (N4c.segB - 1) / 2 ^ 6) - 1) =
      8 * N4c.chBase .N2 1 + 8 * (1 * (N4c.segB - 1) / 2 ^ 6) - 1 ∧
    dV .N2 0 2 = 0 := by decide

/-- (+/−) **The ladder** of a low byte: `L30`'s byte reads `30`, `L31`'s and `N2`'s `31`, `N4`'s `32`. -/
theorem ladder_ctl : mOfB 0x50 = 30 ∧ mOfB 0x4B = 31 ∧ mOfB 0x4D = 31 ∧ mOfB 0x4E = 32 := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> rw [mOfB_eq] <;> decide

/-- (+/−) **The path offset**: index `5 = 0b101`: level `0`'s bit is `1` (the `l` field, offset `0`),
level `1`'s is `0` (the `r` field, offset `4`). -/
theorem offB_ctl : offB (toWord 5) 0 = 0 ∧ offB (toWord 5) 1 = 4 := by decide

/-- (+/−) **The segment count stops at the first failing sub-slot**: flags `1, 1, 0, 1` count `2`
(not `3`); all set count `4`; none, `0`. -/
theorem kc_ctl : kc (fun i => i != 2) 4 = 2 ∧ kc (fun _ => true) 4 = 4 ∧ kc (fun _ => false) 4 = 0 := by decide

/-- (+) **The node branch outputs at most `outCap` words** and (−) is not the empty branch. -/
theorem nd_ctl : (∀ t, outs nd t ≤ outCap) ∧ nd ≠ ndNone := ⟨decOk4_nd.outs, nd_ne_ndNone⟩

end FR.X.OutCtrl
