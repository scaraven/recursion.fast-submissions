-- lvm6 X1 (BLUEPRINT §3 `FD1`): the decoder as an `XIR` program of season 1's extractor language.
-- New; it calls season 1's NTT programs `wtabNIR`, `bflyNIR`, `fwdNIR` (`LvmMPXNtt`) unchanged.
import Lvm6FDSpec

/-!
# `FD1` as an extractor program

Two programs, so that the extractor builds `Λ` once per fold round and decodes every lane of the
round against it:

* `lamIR N ℓ m B`: the basis table, the leaves, the `ℓ` tree levels and `Λ⁻¹` on the coset
  (`LamOk` afterwards: the state `laneIR` needs);
* `laneIR N ℓ m B`: one lane: the syndromes, the correction, the `f·Λ` step; the message's
  `2^ℓ` coefficients are left at `outA B ℓ`.

All loops are `loopK` with constant counts, so the cost is a constant (`Lvm6FDCost`).

## Layout (base `B`, `n = 2^ℓ`)

| region | address | words |
|---|---|---|
| basis table (`N × N`, `N ≤ 64`) | `tbA B = B` | `4096` |
| `S` (one position per word) | `sA B` | `n` |
| the lane's values `y` (by position) | `yA B ℓ` | `n` |
| lane workspace; the output is its high half `outA` | `gA B ℓ` | `2n` |
| the tree, then `Λ` on `ptK [0, 2n)` | `tA B ℓ` | `2n` |
| `Λ⁻¹` on the coset | `iA B ℓ` | `n` |
| two child workspaces | `xA B ℓ`, `wA B ℓ` | `2n` each |

`laneIR` writes only `[gA, gA + 2n)` of the heap; `lamIR` leaves `[sA, tA)` (that is `S`, `y` and
the lane workspace) alone.

## Registers

`190 … 207` (`z*`). Season 1's NTT programs write only registers below `187` (`bflyNIR_nw_hi`);
the field blocks use the scratch `5 … 11`.
-/

namespace Lvm6.FD

open RecursionFast Lvm.X Lvm.Nb

/-! ## Layout -/

/-- The basis table. -/ def tbA (B : ℕ) : ℕ := B
/-- The positions `S`. -/ def sA (B : ℕ) : ℕ := B + 4096
/-- The lane's values. -/ def yA (B ℓ : ℕ) : ℕ := B + 4096 + 2 ^ ℓ
/-- The lane workspace. -/ def gA (B ℓ : ℕ) : ℕ := B + 4096 + 2 * 2 ^ ℓ
/-- The output: the lane workspace's high half. -/ def outA (B ℓ : ℕ) : ℕ := B + 4096 + 3 * 2 ^ ℓ
/-- The tree and `Λ`. -/ def tA (B ℓ : ℕ) : ℕ := B + 4096 + 4 * 2 ^ ℓ
/-- `Λ⁻¹` on the coset. -/ def iA (B ℓ : ℕ) : ℕ := B + 4096 + 6 * 2 ^ ℓ
/-- Child workspace `X`. -/ def xA (B ℓ : ℕ) : ℕ := B + 4096 + 7 * 2 ^ ℓ
/-- Child workspace `W`. -/ def wA (B ℓ : ℕ) : ℕ := B + 4096 + 9 * 2 ^ ℓ
/-- The end of the layout. -/ def fdEnd (B ℓ : ℕ) : ℕ := B + 4096 + 11 * 2 ^ ℓ

/-! ## Registers -/

/-- Index. -/ def zI : ℕ := 190
/-- Address. -/ def zA : ℕ := 191
/-- Address. -/ def zB : ℕ := 192
/-- Address. -/ def zC : ℕ := 193
/-- Scratch. -/ def zT : ℕ := 194
/-- Value. -/ def zU : ℕ := 195
/-- Value. -/ def zV : ℕ := 196
/-- Value. -/ def zW : ℕ := 197
/-- `s₀`. -/ def zS0 : ℕ := 198
/-- `s₁`. -/ def zS1 : ℕ := 199
/-- Parent address. -/ def zP : ℕ := 200
/-- Outer loop counter. -/ def zC1 : ℕ := 201
/-- Outer loop count. -/ def zN1 : ℕ := 202
/-- Inner loop counter. -/ def zC2 : ℕ := 203
/-- Inner loop count. -/ def zN2 : ℕ := 204
/-- A constant. -/ def zK : ℕ := 205
/-- Scratch. -/ def zD : ℕ := 206
/-- Address. -/ def zE : ℕ := 207

/-! ## `lamIR` -/

/-- Leaf `j`: `T[2j] := j`, `T[2j+1] := j xor 1` (the values of `X − ptK j` at `0`, `1`). -/
def leafBody : XIR :=
  .seq (.store zA zI) (.seq (.blk [.op .xor zT zI cOne, .op .add zB zA cOne])
    (.seq (.store zB zT) (.blk [.op .add zI zI cOne, .op .add zA zA cOne, .op .add zA zA cOne])))

/-- The `2^ℓ` leaves. -/
def leavesIR (ℓ B : ℕ) : XIR :=
  .seq (.blk [.const zI 0, .const zA (toWord (tA B ℓ)), .const zN1 (toWord (2 ^ ℓ))])
    (.loopK zC1 zN1 (toWord (2 ^ ℓ)) leafBody)

/-- Dummy leaf `S[i]`: `T[2j] := 1`, `T[2j+1] := 1`. -/
def dummyBody (ℓ B : ℕ) : XIR :=
  .seq (.load zI zC) (.seq (.blk [.op .add zA zI zI, .const zD (toWord (tA B ℓ)), .op .add zA zA zD,
    .op .add zB zA cOne]) (.seq (.store zA cOne) (.seq (.store zB cOne) (.blk [.op .add zC zC cOne]))))

/-- The `m` dummy leaves. -/
def dummiesIR (ℓ m B : ℕ) : XIR :=
  .seq (.blk [.const zC (toWord (sA B)), .const zN1 (toWord m)]) (.loopK zC1 zN1 (toWord m) (dummyBody ℓ B))

/-- Copy one entry of each child of size `c` into the workspaces and zero the entry `c` on. -/
def copyBody (c : ℕ) : XIR :=
  .seq (.load zU zA) (.seq (.store zC zU) (.seq (.load zU zB) (.seq (.store zE zU)
    (.seq (.blk [.const zV 0, .const zD (toWord c), .op .add zT zC zD]) (.seq (.store zT zV)
      (.seq (.blk [.op .add zT zE zD]) (.seq (.store zT zV)
        (.blk [.op .add zA zA cOne, .op .add zB zB cOne, .op .add zC zC cOne, .op .add zE zE cOne]))))))))

/-- One entry of the parent: `T[p + i] := X[i] · W[i]`. -/
def prodBody : XIR :=
  .seq (.load zU zC) (.seq (.load zV zE) (.seq (mulK zW zU zV) (.seq (.store zA zW)
    (.blk [.op .add zA zA cOne, .op .add zC zC cOne, .op .add zE zE cOne]))))

/-- One parent of level `h` at `zP`: copy and pad both children, extend them (inverse NTT of size
`2^(h+1)`, forward NTT of size `2^(h+2)`), multiply. -/
def parentBody (N ℓ B h : ℕ) : XIR :=
  .seq (.blk [.op .or zA zP zP, .const zD (toWord (2 ^ (h + 1))), .op .add zB zP zD,
      .const zC (toWord (xA B ℓ)), .const zE (toWord (wA B ℓ)), .const zN2 (toWord (2 ^ (h + 1)))])
    (.seq (.loopK zC2 zN2 (toWord (2 ^ (h + 1))) (copyBody (2 ^ (h + 1))))
    (.seq (.blk [.const rA0 (toWord (xA B ℓ))]) (.seq (bflyNIR N (h + 1) (tbA B))
    (.seq (fwdNIR N (h + 2) (tbA B)) (.seq (.blk [.const rA0 (toWord (wA B ℓ))])
    (.seq (bflyNIR N (h + 1) (tbA B)) (.seq (fwdNIR N (h + 2) (tbA B))
    (.seq (.blk [.op .or zA zP zP, .const zC (toWord (xA B ℓ)), .const zE (toWord (wA B ℓ)),
      .const zN2 (toWord (2 ^ (h + 2)))])
    (.seq (.loopK zC2 zN2 (toWord (2 ^ (h + 2))) prodBody)
    (.blk [.const zD (toWord (2 ^ (h + 2))), .op .add zP zP zD]))))))))))

/-- **Tree level** `h`: its `2^(ℓ−h−1)` parents. -/
def tLevelIR (N ℓ B h : ℕ) : XIR :=
  .seq (.blk [.const zP (toWord (tA B ℓ)), .const zN1 (toWord (2 ^ (ℓ - h - 1)))])
    (.loopK zC1 zN1 (toWord (2 ^ (ℓ - h - 1))) (parentBody N ℓ B h))

/-- Tree levels `0 … h − 1`. -/
def treeIR (N ℓ B : ℕ) : ℕ → XIR
  | 0 => .blk []
  | h + 1 => .seq (treeIR N ℓ B h) (tLevelIR N ℓ B h)

/-- `Λ⁻¹` at coset point `j`. -/
def invBody : XIR :=
  .seq (.load zU zA) (.seq (invK zW zU) (.seq (.store zB zW)
    (.blk [.op .add zA zA cOne, .op .add zB zB cOne])))

/-- `Λ⁻¹` on the coset. -/
def invsIR (ℓ B : ℕ) : XIR :=
  .seq (.blk [.const zA (toWord (tA B ℓ + 2 ^ ℓ)), .const zB (toWord (iA B ℓ)), .const zN1 (toWord (2 ^ ℓ))])
    (.loopK zC1 zN1 (toWord (2 ^ ℓ)) invBody)

/-- **`lamIR`**: the basis table, the leaves, the tree, `Λ⁻¹` on the coset. -/
def lamIR (N ℓ m B : ℕ) : XIR :=
  .seq (wtabNIR N (tbA B)) (.seq (leavesIR ℓ B) (.seq (dummiesIR ℓ m B) (.seq (treeIR N ℓ B ℓ) (invsIR ℓ B))))

/-! ## `laneIR` -/

/-- Zero one cell of the lane workspace. -/
def zeroBodyG : XIR := .seq (.store zA zV) (.blk [.op .add zA zA cOne])

/-- Zero the lane workspace. -/
def zeroGIR (ℓ B : ℕ) : XIR :=
  .seq (.blk [.const zA (toWord (gA B ℓ)), .const zV 0, .const zN1 (toWord (2 ^ (ℓ + 1)))])
    (.loopK zC1 zN1 (toWord (2 ^ (ℓ + 1))) zeroBodyG)

/-- Position `j = S[i]`: `G[j] := y_j Λ_j`, `s₀ += y_j Λ_j`, `s₁ += y_j Λ_j ptK j`. -/
def synBody (ℓ B : ℕ) : XIR :=
  .seq (.load zI zC) (.seq (.blk [.const zD (toWord (yA B ℓ)), .op .add zA zD zI,
    .const zD (toWord (tA B ℓ)), .op .add zB zD zI, .const zD (toWord (gA B ℓ)), .op .add zE zD zI])
    (.seq (.load zU zA) (.seq (.load zV zB) (.seq (mulK zW zU zV) (.seq (.store zE zW)
      (.seq (.blk [.op .xor zS0 zS0 zW]) (.seq (mulK zU zW zI)
        (.blk [.op .xor zS1 zS1 zU, .op .add zC zC cOne]))))))))

/-- The syndromes and `G` on `S`. -/
def synIR (ℓ m B : ℕ) : XIR :=
  .seq (.blk [.const zC (toWord (sA B)), .const zS0 0, .const zS1 0, .const zN1 (toWord m)])
    (.loopK zC1 zN1 (toWord m) (synBody ℓ B))

/-- The correction: if `s₀ ≠ 0` and `idx = s₁/s₀ < n`, `G[idx] += s₀`. -/
def corrIR (ℓ B : ℕ) : XIR :=
  .ite zS0 (.seq (invK zW zS0) (.seq (mulK zU zS1 zW)
      (.seq (.blk [.const zK (toWord (2 ^ ℓ)), .op .ltu zT zU zK])
        (.ite zT (.seq (.blk [.const zD (toWord (gA B ℓ)), .op .add zA zD zU])
            (.seq (.load zV zA) (.seq (.blk [.op .xor zV zV zS0]) (.store zA zV))))
          (.blk [])))))
    (.blk [])

/-- Coset point `j`: `G[j] := 0`, `G[n + j] := G[n + j] · Λ⁻¹_j`. -/
def cosBody : XIR :=
  .seq (.store zA zV) (.seq (.load zU zB) (.seq (.load zW zC) (.seq (mulK zE zU zW) (.seq (.store zB zE)
    (.blk [.op .add zA zA cOne, .op .add zB zB cOne, .op .add zC zC cOne])))))

/-- `f` on the coset, `0` on `V`. -/
def cosIR (ℓ B : ℕ) : XIR :=
  .seq (.blk [.const zA (toWord (gA B ℓ)), .const zB (toWord (outA B ℓ)), .const zC (toWord (iA B ℓ)),
      .const zV 0, .const zN1 (toWord (2 ^ ℓ))])
    (.loopK zC1 zN1 (toWord (2 ^ ℓ)) cosBody)

/-- **`laneIR`**: one lane, the message's coefficients at `outA B ℓ`. -/
def laneIR (N ℓ m B : ℕ) : XIR :=
  .seq (zeroGIR ℓ B) (.seq (synIR ℓ m B) (.seq (corrIR ℓ B)
    (.seq (.blk [.const rA0 (toWord (gA B ℓ))]) (.seq (bflyNIR N ℓ (tbA B)) (.seq (fwdNIR N (ℓ + 1) (tbA B))
    (.seq (cosIR ℓ B) (.seq (.blk [.const rA0 (toWord (gA B ℓ))]) (bflyNIR N (ℓ + 1) (tbA B)))))))))

/-- One decoding: `lamIR`, then `laneIR`. -/
def fd1IR (N ℓ m B : ℕ) : XIR := .seq (lamIR N ℓ m B) (laneIR N ℓ m B)

/-! ## The state after `lamIR` -/

/-- **`LamOk`**: the basis table, `S`, `Λ` on `ptK [0, 2^(ℓ+1))` and `Λ⁻¹` on the coset are in
place: the state `laneIR` decodes from. -/
def LamOk (N ℓ B : ℕ) (S : List ℕ) (M : Mem) : Prop :=
  (∀ v < N, ∀ i < N, rdK M (tbA B + N * v + i) = (wRow ptK N v).getD i 0) ∧
  (∀ i < S.length, rd M (sA B + i) = toWord (S.getD i 0)) ∧
  (∀ i < 2 ^ (ℓ + 1), rdK M (tA B ℓ + i) = lam N S ℓ i) ∧
  (∀ j < 2 ^ ℓ, rdK M (iA B ℓ + j) = (lam N S ℓ (2 ^ ℓ + j))⁻¹)

end Lvm6.FD
