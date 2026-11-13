-- New for lvm2 roll 11 (M′, R11-X, `ext_eqM20` step (iv)): the schedule's view of `C_main`'s opening at `P20`, as
-- B1's `openRec_P20` (ff8902c2, `LvmCertSExq2Run`) was for `C_rec`'s: the replay's slices, offsets and kinds.
import LvmMPXExtSplit
import LvmMPXLayout

/-!
# `openMain_P20`: the replay of M′'s history up to the residual

The history (`mainPrefix_splitK`) is replayed (`trun_simK2`, `trun_query`) in five segments of reads, samples and
commitments, cut at the two openings:

* `A1` (`midItems ++ mainHeadA1`): the middle phases, `ρ`, the intro, level 0's six fold rounds, from π byte `14176`
  (the root's cap pending from `5984`);
* `A2` (`mainHeadA2`): level 1's cap (at `capOffM 1 = 141856`), `pre0`; then level 0's opening (`115` positions of
  `728` bytes);
* `B1` (`mainHeadB1`): the opening's intro, level 1's four fold rounds;
* `A3` (`mainHeadA3`): level 2's cap (at `capOffM 2 = 230008`), `pre1`; then level 1's opening (`77` positions of
  `672` bytes);
* `B2` (`mainHeadB2`): the opening's intro, level 2's four fold rounds, up to the residual at `resOffM = 286184`.

**`openMain_P20`** (by evaluation): the slices `fsPreK2` the segments' samples absorb are the chain's messages
`fsMsgs` of positions `2–1249`, `1250–1284`, `1285–1288`, `1289–1314`, `1315–1318`; the offsets; the kinds.
-/

set_option autoImplicit false

namespace Lvm.ASM

open RecursionFast Lvm.FS
open LeanVM.Parameters

/-- `C_main`'s commitment shapes `(ht, w)` at M′ (level 1: `2^16` rows of `3 · 2^4` words, level 2: `2^13`). -/
def shMain : Ref → ℕ × ℕ
  | ⟨.main, 1⟩ => (16, 48)
  | ⟨.main, 2⟩ => (13, 48)
  | _ => (19, 64)

/-- The schedule's `openMain` phase at `P20`. -/
def mainOpenI : List Item := ((phases P20).getD 7 default).2

/-- `ρ`, the intro round, level 0's six fold rounds. -/
def mainHeadA1 : List Item := mainOpenI.take 14
/-- Level 1's cap, the OOD point, its answer and intro, level 0's proof of work, positions and `λ`. -/
def mainHeadA2 : List Item := (mainOpenI.drop 14).take 25
/-- After level 0's opening: its intro, level 1's four fold rounds. -/
def mainHeadB1 : List Item := (mainOpenI.drop 40).take 9
/-- Level 2's cap, the OOD point, its answer and intro, level 1's proof of work, positions and `λ`. -/
def mainHeadA3 : List Item := (mainOpenI.drop 49).take 21
/-- After level 1's opening: its intro, level 2's four fold rounds. -/
def mainHeadB2 : List Item := (mainOpenI.drop 71).take 9

/-- The kinds of a level's intro and `n` fold rounds. -/
def foldKinds (n : ℕ) : List EvK := [.read, .read] ++ (List.replicate n [EvK.sample, .read, .read]).flatten

/-- **`openMain_P20`**: the replay's slices, offsets and kinds at `P20` (by evaluation). -/
theorem openMain_P20 :
    fsPreK2 (itemK2 P20 shMain (midItems ++ mainHeadA1)) 14176 5984 = ((Lvm.X.fsMsgs P20).drop 1).take 1248 ∧
    offK2 (itemK2 P20 shMain (midItems ++ mainHeadA1)) 14176 = 141856 ∧
    pendK2 (itemK2 P20 shMain (midItems ++ mainHeadA1)) 14176 5984 = 141808 ∧
    fsPreK2 (itemK2 P20 shMain mainHeadA2) 141856 141808 = ((Lvm.X.fsMsgs P20).drop 1249).take 35 ∧
    offK2 (itemK2 P20 shMain mainHeadA2) 141856 = 146048 ∧
    pendK2 (itemK2 P20 shMain mainHeadA2) 141856 141808 = 146048 ∧
    fsPreK2 (itemK2 P20 shMain mainHeadB1) 229768 229768 = ((Lvm.X.fsMsgs P20).drop 1284).take 4 ∧
    offK2 (itemK2 P20 shMain mainHeadB1) 229768 = 230008 ∧
    pendK2 (itemK2 P20 shMain mainHeadB1) 229768 229768 = 229960 ∧
    fsPreK2 (itemK2 P20 shMain mainHeadA3) 230008 229960 = ((Lvm.X.fsMsgs P20).drop 1288).take 26 ∧
    offK2 (itemK2 P20 shMain mainHeadA3) 230008 = 234200 ∧
    pendK2 (itemK2 P20 shMain mainHeadA3) 230008 229960 = 234200 ∧
    fsPreK2 (itemK2 P20 shMain mainHeadB2) 285944 285944 = ((Lvm.X.fsMsgs P20).drop 1314).take 4 ∧
    offK2 (itemK2 P20 shMain mainHeadB2) 285944 = 286184 ∧
    pendK2 (itemK2 P20 shMain mainHeadB2) 285944 285944 = 286136 ∧
    (itemKinds midItems).count .sample = 1241 ∧ RSItems midItems = true ∧
    itemK2 P20 shMain mainHeadA1 = ([EvK.sample] ++ foldKinds 6).map toK2 ∧
    itemK2 P20 shMain mainHeadA2 = .commit 16 48 4096 :: (preKinds 17 15).map toK2 ∧
    itemK2 P20 shMain mainHeadB1 = (foldKinds 4).map toK2 ∧
    itemK2 P20 shMain mainHeadA3 = .commit 13 48 4096 :: (preKinds 13 10).map toK2 ∧
    itemK2 P20 shMain mainHeadB2 = (foldKinds 4).map toK2 ∧
    Lvm.X.capOffM P20 1 = 141856 ∧ Lvm.X.capOffM P20 2 = 230008 ∧ Lvm.X.resOffM P20 = 286184 := by
  decide +kernel

end Lvm.ASM
