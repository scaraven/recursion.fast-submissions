-- New for lvm2 E2F (E2F-L, 2026-11-13): the node output generic in the stage (`outIR` of `LvmXNodeIR` with the
-- stage's trace blocks, entry count and `|π|`). Definitions; the facts go to `LvmXSOut*`.
import LvmXSLayout
import LvmXTop
import LvmQSigLeafPerm

/-!
# The node output at a stage

`pSegS`, `trSegS`: the proof's and the trace's segments over `blocksS st`; **`outIRS st mB`**: `outIR mB` with them
and `|π| = st.pz`. With `st.p.leafOut` (lvm2 σ_LEAF, S2GS) the right leaf's signature is not in π's header: `rsigIR`
copies it from the decoded window (stream-block words `17·2^14 + 1024 …`, the chains in `permC` order, `slSegC`;
`sigOfP` reads such a signature).
-/

set_option autoImplicit false

namespace Lvm.XS

open RecursionFast Lvm Lvm.X

/-! ## The node output -/

/-- **The proof's segment**: `'S' ‖ 0⁷`, then the blocks' contributions. -/
def pSegS (st : XStage) : Seg := .cat (.wd (toWord 0x53)) (blkPSegs 6 (blocksS st))

/-- **The trace's segment**: the count, `q₀`'s entry, the blocks from lane 6. -/
def trSegS (st : XStage) : Seg :=
  .cat (.wd (toWord (qSS st))) (.cat (.wd (toWord 7)) (.cat (.sh8 1) (.cat (.cp 2 4) (blkTSegs 6 (blocksS st)))))

/-- Chain `k`'s 4 words for every `k` of the list, at `1 + 4·posC k` (`σ_leaf`'s chains in `permC` order). -/
def slChains : List ℕ → Seg
  | [] => .nil
  | k :: ks => .cat (.cp (1 + 4 * Lvm.QSig.posC k) 4) (slChains ks)

/-- **`σ_leaf`'s segment** from its first window word: the index, the 133 chains in order, the 16 path digests. -/
def slSegC : Seg := .cat (.cp 0 1) (.cat (slChains (List.range 133)) (.cp 533 64))

/-- **The right leaf's signature**: from the window (`slSegC` at `sigB mB + 1024`) with `st.p.leafOut`, else π's
header words `19 …` on the tape. -/
def rsigIR (st : XStage) (mB : ℕ) : XIR :=
  if st.p.leafOut then .seq (setR (sigB mB + 1024)) (segIR apC 0 slSegC) else tcpIR 24 597

/-- **The node output at a stage** (`outIR`). -/
def outIRS (st : XStage) (mB : ℕ) : XIR :=
  .seq (emitIR (toWord 1)) (.seq (tcpIR 11 4) (.seq (leafStmtIR 20 19)
  (.seq (emitIR (toWord st.pz)) (.seq (copyIR mB)
  (.seq (setR sgB) (.seq (segIR apC 0 (pSegS st)) (.seq (segIR apC 0 (trSegS st))
  (.seq (setR (sigB mB)) (.seq (segIR apC 0 (.cp 0 597))
  (.seq (emitIR (toWord 48)) (.seq (emitIR (toWord 0)) (.seq (tcpIR 15 5)
  (.seq (emitIR (toWord 0)) (rsigIR st mB))))))))))))))

end Lvm.XS

namespace Lvm.CT

open RecursionFast

/-- **A signature stored in `permC` order** (RE-FREEZE R1, variant C): the index at word `0`, chain `i`'s value at
words `1 + 4·posC i …`, the 16 path digests at `1 + 4·133 + 4k …` (`sigOfF` with the chains permuted). -/
def sigOfP (f : ℕ → Word) : Sig :=
  ⟨(f 0).toNat, (List.range wotsLen).map fun i => Lvm.X.digW (Lvm.X.wsAt f (1 + 4 * Lvm.QSig.posC i) 4),
    (List.range sigHeight).map fun k => Lvm.X.digW (Lvm.X.wsAt f (1 + 4 * wotsLen + 4 * k) 4)⟩

end Lvm.CT
