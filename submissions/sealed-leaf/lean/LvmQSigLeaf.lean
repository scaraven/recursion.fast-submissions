-- New for lvm2 σ_LEAF (SLF-C, stage S2GS, lead decision D2 variant A): the node's own leaf signature walk. DEV (G0):
-- the gadget and its `BITS` classes; the soundness lemma comes after G0.
import LvmSigBits
import LvmQSigLeafPerm

/-!
# `Q_sig` at S2GS: no `σ_leaf'` check, and a second WOTS walk (the node's own `σ_leaf`)

* **`qsigNoSl`**: `qsig` without `gSl` (the child's header no longer carries `σ_leaf'`).
* **`qsigW I pre`**: the WOTS walk of `qsig` alone (chains, checksum, path, the root `= vk`, `idx < 2^16`, the key
  leaf's and the path's messages and their equality with the `KS` input lanes `I.xs`), on `qsig`'s constants and table
  `pre`: no header, no statement hashes. Its `KS` rows: 399 chain steps, 32 key-leaf blocks, 16 path nodes (447).
* **`qsigS I I2 md`**: `qsigNoSl I`, then four constant cells holding the message `md` (the lanes of
  `traceDigest []`), then `qsigW` on `I2` with `I2.md` those cells.
* **`sigSpecsW`**: the walk's `BITS` classes (`idx`, `md`, `cs`, step inputs, chain ends and path halves).
-/

set_option autoImplicit false

namespace Lvm.QSig

open Lvm Lvm.Loop Lvm.Loop.Build Lvm.Bits Lvm.BitsTab

/-- **`Q_sig` without `σ_leaf'`'s check** (S2GS). -/
def qsigNoSl (I : SigIn) : BM SigOut := do
  let pre ← gPre I
  let cm ← loop [7] (chainM I pre.1.n pre.2.1.n)
  let cc ← forN 5 fun u => loop [] (chainC I pre.1.n pre.2.1.n u)
  let ck ← gCheck I pre.1 pre.2.1
  let pa ← loop [4] (pathTpl I)
  header I pre.1 pre.2.1
  assert0 (kc (I.bi + 17)) (kc I.flag)
  let px ← getPtr
  let msg ← gMsg I pre.1.n (Tbase pre)
  gXeq I px.k
  pure ⟨pre, cm, cc, ck, pa, msg, px.k⟩

/-- The walk's messages, in `KS` row order: 399 chain steps, the key leaf (544 lanes), 16 path nodes. -/
def gMsgW (I : SigIn) (Zn Tb : Nat) : BM MsgOut := do
  let xm ← loop [7] (stepsTpl I Zn (oS Tb 1) (fun s => (s.toUInt64 <<< (16 : Nat).toUInt64)) I.bx 24)
  let xc ← forN 5 fun u => loop [] (stepsTpl I Zn (oA Zn)
    (fun s => ((128 + u).toUInt64 <<< (8 : Nat).toUInt64) ^^^ (s.toUInt64 <<< (16 : Nat).toUInt64))
    (I.bx + 24 * (128 + u)) 0)
  let la ← loop [] (leafA I)
  let lb ← loop [9] (leafB I)
  let lc ← loop [] (leafC I Zn)
  let xp ← loop [4] (twoLanes Zn 0x4D I.bp (I.bp + 8) 16)
  pure ⟨xm, xc, la, lb, lc, xp, dLoop, dLoop⟩

/-- **The walk's message lanes are the `KS` inputs**: `x[x0 + j] = xs[j]`, gated, for `j < 7599 = 447·17`
(`4096 + 2048 + 1024 + 256 + 128 + 32 + 8 + 4 + 2 + 1`). -/
def gXeqW (I : SigIn) (x0 : Nat) : BM Unit := do
  let _ ← loop [12] (xeqTpl I x0 0)
  let _ ← loop [11] (xeqTpl I x0 4096)
  let _ ← loop [10] (xeqTpl I x0 6144)
  let _ ← loop [8] (xeqTpl I x0 7168)
  let _ ← loop [7] (xeqTpl I x0 7424)
  let _ ← loop [5] (xeqTpl I x0 7552)
  let _ ← loop [3] (xeqTpl I x0 7584)
  let _ ← loop [2] (xeqTpl I x0 7592)
  let _ ← loop [1] (xeqTpl I x0 7596)
  let _ ← loop [0] (xeqTpl I x0 7598)
  pure ()

/-- **The WOTS walk alone** on `qsig`'s constants and table `pre`: the chains, the checksum, the path, the root is
`vk`, `idx < 2^16`, the messages and their equality with `I.xs`. -/
def qsigW (I : SigIn) (pre : Cell × Cell × List LoopOut) : BM SigOut := do
  let cm ← loop [7] (chainM I pre.1.n pre.2.1.n)
  let cc ← forN 5 fun u => loop [] (chainC I pre.1.n pre.2.1.n u)
  let ck ← gCheck I pre.1 pre.2.1
  let pa ← loop [4] (pathTpl I)
  let g := kc I.flag
  let _ ← forN 4 fun l => assertEq (kc (I.yc + 64 + l)) (kc (I.vk + l)) g
  assert0 (kc (I.bi + 17)) g
  let px ← getPtr
  let msg ← gMsgW I pre.1.n (Tbase pre)
  gXeqW I px.k
  pure ⟨pre, cm, cc, ck, pa, msg, px.k⟩

/-- The four lanes of a digest (lane `l`: bytes `8l … 8l + 7`, little-endian). -/
def digLanes (d : RecursionFast.Digest) : List UInt64 :=
  (List.range 4).map fun l => (List.range 8).foldl (fun a t => a ||| ((d.toList.getD (8 * l + t) 0).toUInt64 <<< (8 * t).toUInt64)) 0

/-- The lanes of `traceDigest []`: the message of every right leaf's signature. -/
def mdLeaf : List UInt64 := digLanes (RecursionFast.traceDigest [])

/-- **`Q_sig` at S2GS**: `qsigNoSl I`; four constant cells `md`; the walk on `I2` (its `md` those cells). -/
def qsigS (I I2 : SigIn) (md : List UInt64) : BM (SigOut × SigOut) := do
  let o1 ← qsigNoSl I
  let ms ← forN 4 fun l => const .K (w64 (md.getD l 0)) (kc I.flag)
  let o2 ← qsigW { I2 with md := (ms.headD (kc 0)).n } o1.pre
  pure (o1, o2)

/-! ## The walk's `BITS` classes -/

section Specs

variable (I : SigIn) (o : SigOut) (pl : Nat → Bool × Nat)

/-- The one-byte shifts of the walk: the chain ends (532), the path halves (128). -/
def s8W : BSpec :=
  ⟨10, 660, [.shl 8, .shr 56], true,
    fun x => if x < 532 then endc o (x / 4) (x % 4)
      else (o.pa.cell (4 + 4 * ((x - 532) / 4 % 2) + (x - 532) % 4) ((x - 532) / 8)).n,
    fun j x => if x < 532 then I.be + 2 * x + j else I.bp + 2 * (x - 532) + j, pl, 2,
    by intros; split_ifs <;> omega⟩

/-- **The walk's `BITS` tables**, class `k` placed by `bpl k`: `idx`, `md`, `cs`, step inputs, `s8W`. -/
def sigSpecsW (bpl : Nat → Nat → Bool × Nat) : List BSpec :=
  [SigBits.sIdx I (bpl 0), SigBits.sMd I (bpl 1), SigBits.sCs I (bpl 2), SigBits.s24 I o (bpl 3), s8W I o (bpl 4)]

end Specs

/-! ## Variant C (DEV, G0 s-dev2): the walk specialised to the constant digits of `traceDigest []`

The 133 chains are taken in the order `permC` (digit `0` first, then `1`, `2`, `3`; `σ_leaf`'s chain values are
stored in that order). Group `d < 3` (`n_d` chains, padded to `2^gLogC d` iterations) hashes steps `d … 2` of each of
its chains: one loop whose template is `3 − d` step messages; step `t`'s input is the signed value (`t = 0`) or the
previous `KS` row's digest. No checksum, no digit bits, no muxes. `KS` rows: the groups' padded steps, the key
leaf (32), the path (16). -/

/-- `⌈log₂ n⌉`. -/
def clogC (n : Nat) : Nat := if n ≤ 1 then 0 else (n - 1).log2 + 1

/-- Group `d`'s iterations (log). -/
def gLogC (d : Nat) : Nat := clogC (grpC d).length

/-- Group `d`'s first `KS` row (from the walk's first row): `Σ_{e<d} 2^gLog e·(3 − e)`. -/
def gRowC (d : Nat) : Nat := ((List.range d).map fun e => 2 ^ gLogC e * (3 - e)).sum

/-- The steps' `KS` rows, padded (the key leaf's first row). -/
def nStepRowsC : Nat := gRowC 3

/-- Group `d`'s first step-input `BITS` output (from `I.bx`): `8·(3 − e)` per padded iteration of the groups before. -/
def gBxC (d : Nat) : Nat := ((List.range d).map fun e => 2 ^ gLogC e * 8 * (3 - e)).sum

/-- **The step messages of group `d`** (`3 − d` steps per iteration; chain index from the constants `cT`). -/
def gStepsTplC (I : SigIn) (Zn cT d : Nat) : List LRow :=
  (List.range (3 - d)).flatMap fun t =>
    stepLanes I Zn (oS (cT + gOffC d) 1) ((d + t).toUInt64 <<< (16 : Nat).toUInt64) (I.bx + gBxC d + 8 * t) (8 * (3 - d))

/-- The walk's message lanes are the `KS` inputs: `x[x0 + j] = xs[j]` for `j < n` (`n`'s binary digits, high first). -/
def gXeqN (I : SigIn) (x0 n : Nat) : BM Unit := do
  let bs := ((List.range 14).reverse).filter fun b => n / 2 ^ b % 2 == 1
  let _ ← forN bs.length fun q =>
    let b := bs.getD q 0
    let off := ((bs.take q).map fun c => 2 ^ c).sum
    loop [b] (xeqTpl I x0 off)
  pure ()

/-- What the specialised walk returns. -/
structure WalkC where
  cT : Nat
  pa : LoopOut
  gs : List LoopOut
  la : LoopOut
  lb : LoopOut
  lc : LoopOut
  xp : LoopOut
  x0 : Nat

/-- **The specialised walk**: the chain-index constants, the path, the root is `vk`, `idx < 2^16`, the messages
(groups' steps, key leaf, path), their equality with `I.xs`. -/
def qsigC (I : SigIn) (Zn : Nat) : BM WalkC := do
  let tc ← forN 133 fun k => const .K (w64 ((permC.getD k 0).toUInt64 <<< (8 : Nat).toUInt64)) (kc I.flag)
  let cT := (tc.headD (kc 0)).n
  let pa ← loop [4] (pathTpl I)
  let g := kc I.flag
  let _ ← forN 4 fun l => assertEq (kc (I.yc + 64 + l)) (kc (I.vk + l)) g
  assert0 (kc (I.bi + 17)) g
  let px ← getPtr
  let gs ← forN 3 fun d => loop [gLogC d] (gStepsTplC I Zn cT d)
  let la ← loop [] (leafA I)
  let lb ← loop [9] (leafB I)
  let lc ← loop [] (leafC I Zn)
  let xp ← loop [4] (twoLanes Zn 0x4D I.bp (I.bp + 8) 16)
  gXeqN I px.k (17 * (nStepRowsC + 48))
  pure ⟨cT, pa, gs, la, lb, lc, xp, px.k⟩

/-- **`Q_sig` at S2GS, variant C**: `qsigNoSl I`, then the specialised walk on `I2`. -/
def qsigSC (I I2 : SigIn) : BM (SigOut × WalkC) := do
  let o1 ← qsigNoSl I
  let o2 ← qsigC I2 o1.pre.1.n
  pure (o1, o2)

/-- The cell of chain `i`'s end, lane `l` (`ys` the walk's digests from its first row): the last step's digest, or
the signed value (digit `3`). -/
def endC (I : SigIn) (ys i l : Nat) : Nat :=
  let d := dLeaf.getD i 0
  let k := posC i - gOffC d
  if d = 3 then I.sg + 1 + 4 * posC i + l else ys + 4 * (gRowC d + (3 - d) * k + (2 - d)) + l

/-- The real step inputs `(d, k, t)` in order. -/
def stepsC : List (Nat × Nat × Nat) :=
  (List.range 3).flatMap fun d => (List.range (grpC d).length).flatMap fun k =>
    (List.range (3 - d)).map fun t => (d, k, t)

/-- The real step input `x / 4` (`stepsC` order), lane `x % 4`: its word cell. -/
def s24wcC (I : SigIn) (ys : Nat) (S : Array (Nat × Nat × Nat)) (x : Nat) : Nat :=
  match S.getD (x / 4) (0, 0, 0) with
  | (d, k, t) => if t = 0 then I.sg + 1 + 4 * (gOffC d + k) + x % 4 else ys + 4 * (gRowC d + (3 - d) * k + t - 1) + x % 4

/-- Its first output cell. -/
def s24ocC (I : SigIn) (S : Array (Nat × Nat × Nat)) (x : Nat) : Nat :=
  match S.getD (x / 4) (0, 0, 0) with
  | (d, k, t) => I.bx + gBxC d + 8 * (3 - d) * k + 8 * t + 2 * (x % 4)

/-- **The specialised walk's `BITS` tables**: `idx`, the real steps' inputs (`shl 24`, `shr 40`), the chain ends and
path halves (`shl 8`, `shr 56`). -/
def sigSpecsC (I : SigIn) (ys : Nat) (pa : LoopOut) (bpl : Nat → Nat → Bool × Nat) : List BSpec :=
  let S := stepsC.toArray
  [SigBits.sIdx I (bpl 0),
   ⟨clogC (4 * S.size), 4 * S.size, [.shl 24, .shr 40], true, s24wcC I ys S, fun j x => s24ocC I S x + j, bpl 1, 2,
    by intros; omega⟩,
   ⟨10, 660, [.shl 8, .shr 56], true,
    fun x => if x < 532 then endC I ys (x / 4) (x % 4)
      else (pa.cell (4 + 4 * ((x - 532) / 4 % 2) + (x - 532) % 4) ((x - 532) / 8)).n,
    fun j x => if x < 532 then I.be + 2 * x + j else I.bp + 2 * (x - 532) + j, bpl 2, 2,
    by intros; split_ifs <;> omega⟩]

end Lvm.QSig
