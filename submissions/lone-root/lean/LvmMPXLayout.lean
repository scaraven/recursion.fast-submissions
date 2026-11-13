-- New for lvm2 roll 11 (M′, R11-X, part 2(b)): the extractor's static layout of `C_main`'s WHIR opening at `S2GM`
-- (R11-E's schedule: one commitment, no `openRec`), read off `V_S`'s schedule as `LvmXLayout` does for `C_rec`
-- (`nPre`, `alphaPos`, `alpha1Pos`, `capRec1Off`, `f2Off`, `nChain`, adapted to `C_main`'s three levels).
import LvmXChainL

/-!
# `C_main`'s opening in the chain and in π (`S2GM`)

The `openMain` phase is `ρ`, the intro round (2 scalars), then `C_main`'s three levels (`levelIJ`): level `i`'s
`fold_i` fold rounds (a sample, 2 scalars), the next cap, the OOD point (`κ_i` samples, 1 + 2 scalars), the proof of
work (2 samples), the positions (`nPosQ_i` queries), `λ`, the opening, the intro round; the last level ends with the
residual (`2^9` scalars) and the tail. Chain position `k ≥ 1` absorbs `fsMsgs` entry `k − 1`.

* `nPreM p`: the FS queries before `openMain`; `foldPosM p i j`: the chain position of level `i`'s fold challenge
  `α_{i,j}`; `nChainM p`: the chain's targets through the last fold challenge.
* `capOffM p i`: the π offset of level `i`'s cap (level 0's right after the header); `resOffM p`: of the residual.
* `readDepthM p i`: the tree levels between level `i`'s cap and its leaves (`11, 9, 6`).
* **`layoutM_P20`** (`decide +kernel`): the values at `P20` and the checks that each fold challenge absorbs exactly
  the previous round's 2 scalars, each next cap its 2 scalars and `2^cap` nodes, the residual its 2 scalars and
  `2^9` scalars.
-/

namespace Lvm.X

open RecursionFast Lvm

/-- The FS queries before `openMain` (phases `commit … ksLink`). -/
def nPreM (p : Params) : ℕ := (fsPre p (((phases p).take 7).flatMap (·.2)) headerBytes headerBytes).length

/-- `C_main`'s level `i`. -/
def mainL (p : Params) (i : ℕ) : Level := p.level ⟨.main, i⟩

/-- The FS queries of a non-final level: the fold samples, the OOD point, the proof of work, the positions, `λ`. -/
def lvlFsM (p : Params) (i : ℕ) : ℕ :=
  (mainL p i).fold + (if p.mainOod then (mainL p i).kappa else 0) + gQs p + (mainL p i).nPosQ + 1

/-- **The chain position of level `i`'s fold challenge `α_{i,j}`** (`i < 3`). -/
def foldPosM (p : Params) (i j : ℕ) : ℕ :=
  nPreM p + 3 + (if i = 0 then 0 else if i = 1 then lvlFsM p 0 else lvlFsM p 0 + lvlFsM p 1) + j

/-- The chain position of fold challenge `k < 14` (`6 + 4 + 4`, `mainDataM`'s order). -/
def foldPosK (p : Params) (k : ℕ) : ℕ :=
  if k < 6 then foldPosM p 0 k else if k < 10 then foldPosM p 1 (k - 6) else foldPosM p 2 (k - 10)

/-- **The chain's targets** `0 … nChainM p − 1`: through the last fold challenge of level 2. -/
def nChainM (p : Params) : ℕ := foldPosM p 2 ((mainL p 2).fold - 1) + 1

/-- **The π offset of level `i`'s cap**: level 0's right after the header; level `i + 1`'s after level `i`'s last
fold round's 2 scalars. -/
def capOffM (p : Params) : ℕ → ℕ
  | 0 => headerBytes
  | 1 => ((fsMsgs p).getD (foldPosM p 0 ((mainL p 0).fold - 1)) (0, 0)).1 + 2 * eBytes
  | _ => ((fsMsgs p).getD (foldPosM p 1 ((mainL p 1).fold - 1)) (0, 0)).1 + 2 * eBytes

/-- **The π offset of the residual** (`2^9` `E` scalars, after level 2's last fold round's 2 scalars). -/
def resOffM (p : Params) : ℕ := ((fsMsgs p).getD (nChainM p - 1) (0, 0)).1 + 2 * eBytes

/-- The tree levels between level `i`'s cap and its leaves (level 0: `2^19` positions, levels 1, 2: `2^16`, `2^13`). -/
def readDepthM (p : Params) (i : ℕ) : ℕ := (mainL p i).kappa + (if i = 0 then 2 else if i = 1 then 3 else 4) -
  (mainL p i).cap

/-- **The layout at `P20`** (`S2GM`). -/
theorem layoutM_P20 :
    nPreM pX = 1241 ∧ foldPosM pX 0 0 = 1244 ∧ foldPosM pX 1 0 = 1285 ∧ foldPosM pX 2 0 = 1315 ∧
    nChainM pX = 1319 ∧ capOffM pX 0 = 5984 ∧ capOffM pX 1 = 141856 ∧ capOffM pX 2 = 230008 ∧
    resOffM pX = 286184 ∧ (fsMsgs pX).length = 1338 ∧
    (mainL pX 0).cap = 8 ∧ (mainL pX 1).cap = 7 ∧ (mainL pX 2).cap = 7 ∧
    readDepthM pX 0 = 11 ∧ readDepthM pX 1 = 9 ∧ readDepthM pX 2 = 6 ∧
    (mainL pX 0).fold = 6 ∧ (mainL pX 1).fold = 4 ∧ (mainL pX 2).fold = 4 ∧ (mainL pX 0).row = 376 ∧
    (mainL pX 1).row = 384 ∧ (mainL pX 2).row = 384 ∧ pX.mainFinalLog = 9 ∧
    -- each fold challenge absorbs the previous round's 2 scalars
    (∀ k < 14, ((fsMsgs pX).getD (foldPosK pX k - 1) (0, 0)).2 = 2 * eBytes) ∧
    -- the next caps and the residual follow 2 scalars
    ((fsMsgs pX).getD (foldPosM pX 0 5) (0, 0)).2 = 2 * eBytes + nodeBytes * 2 ^ 7 ∧
    ((fsMsgs pX).getD (foldPosM pX 1 3) (0, 0)).2 = 2 * eBytes + nodeBytes * 2 ^ 7 ∧
    ((fsMsgs pX).getD (nChainM pX - 1) (0, 0)).2 = 2 * eBytes + eBytes * 2 ^ 9 ∧
    -- every chain message is lane-aligned, inside π, within `queryCap`
    ((fsMsgs pX).take (nChainM pX - 1)).all msgOkL = true := by
  decide +kernel

theorem nChainM_eq : nChainM pX = 1319 := layoutM_P20.2.2.2.2.1

theorem foldPosK_lt {k : ℕ} (hk : k < 14) : foldPosK pX k < nChainM pX := by
  have h := layoutM_P20
  simp only [foldPosK, foldPosM, h.1, nChainM_eq] at *
  have e0 : lvlFsM pX 0 = 41 := by decide +kernel
  have e1 : lvlFsM pX 1 = 30 := by decide +kernel
  rw [e0, e1]
  split_ifs <;> simp <;> omega

/-! ## The chain table (`chTabL` through `C_main`'s folds) -/

/-- **The chain table** for `C_main`'s chain: entries `0 … nChainM`. -/
def chTabM : List Word := (List.range (nChainM pX + 1)).flatMap tabEntL

theorem chTabM_length : chTabM.length = 4 * (nChainM pX + 1) := by
  have h : ∀ n : ℕ, ((List.range n).flatMap tabEntL).length = 4 * n := fun n => by
    rw [List.length_flatMap]
    simp only [tabEntL_length, List.map_const', List.length_range, List.sum_replicate, smul_eq_mul]
    ring
  rw [chTabM]
  exact h _

theorem chTabM_len : chTabM.length = 5280 := by rw [chTabM_length, nChainM_eq]

/-- **The chain scan through `C_main`'s fold challenges.** -/
def chainLM : XIR := chainIR (posL (piSize pX)) (nChainM pX) chTabM sdL

end Lvm.X
