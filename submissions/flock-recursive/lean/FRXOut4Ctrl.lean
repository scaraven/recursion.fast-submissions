-- New for `flock-recursive` (stage S-H4, pass 11, item 6): controls for the node output's programs and
-- for `nd`. Outside the certificate's closure (imported by `FR` only).
import FRXNd4

/-!
# Controls for the node output (`outIR4`) and the node branch (`nd`)

Each control shows a definition the decode law relies on doing what its statement says, and not
something weaker:

* the chain loader's **redirect** (`ldIx`, `dV`): only the stream's last block is read from the
  candidate final block, and only when the aggregate has fewer than `maxK` segments;
* the **spacer entry** (`spW`, `spPre`) and the aggregate trace's count (one entry per spacer);
* the **ladder** (`mOfB_eq`): `'P'`, `'K'`/`'M'` and the rest give three different ladders;
* the **path offset** (`offB`): bit `t` of the index picks the `l` (`0`) or `r` (`4`) field;
* the **segment count** (`kc`): it stops at the first failing sub-slot (a later selected one does
  not count);
* the **node branch** is not empty and outputs at most `outCap` words.
-/

namespace FR.X.OutCtrl

open RecursionFast FR.X FR.X.X4 FR.Rev4 FR.Snd

/-- (+/−) **The redirect**: at `N2`'s aggregate with one segment, chain word `8·jL` (the stream's last
block, `jLv 1 = sBlk − 3`) is read from the candidate final block `finB .N2 0` (`blkOf`'s), word
`8·jL − 1` (the block before) from the main chain; with `maxK = 2` segments there is no redirect (`dV = 0`). -/
theorem redirect_ctl :
    ldIx (8 * N4c.chBase .N2 1) (jLv 1) (dV .N2 0 1) (8 * jLv 1) = 8 * N4c.finB .N2 0 ∧
    ldIx (8 * N4c.chBase .N2 1) (jLv 1) (dV .N2 0 1) (8 * jLv 1 - 1) = 8 * N4c.chBase .N2 1 + 8 * jLv 1 - 1 ∧
    dV .N2 0 2 = 0 := by decide

/-- (+/−) **The spacer entry** (revision 4.4.1, R-A′): its query's words are 13 (the length `89`, then 12
words), so the traces' prefix emits 17 words (with the answer's 4) at `i ≥ 1`; (−) the aggregate's trace
count is not `k·|items|` (`k = 2`: one spacer entry more). -/
theorem spacer_ctl (κ : NodeKind) (σ : ℕ) (w : Circ.Asg) (ans : ℕ → Digest) :
    spW.length = 13 ∧ spW.head? = some (toWord 89) ∧ outs (spPre κ) 0 = 17 ∧
      (aggTrace ans ((List.range 2).map fun i => N4s.segTr κ σ 2 i w)).length ≠ 2 * (itemsOf seq4).length := by
  refine ⟨by decide, by decide, (cso_spPre κ).2.1, ?_⟩
  rw [aggTr_count, itemsOf_seq4_len]; decide

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
