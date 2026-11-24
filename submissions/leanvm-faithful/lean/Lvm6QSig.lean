-- New for lvm6 (WP CA). `Q_sig` at v6: season 1's two walks (roll #33's `qsigSC`: the child's
-- signature `σ'` on its trace digest, then the node's own `σ_leaf` on `traceDigest []`, both read from
-- `STREAM`), after a header copy that puts the child's v6 `HDR` words where season 1's `header` reads them.
import Lvm6QStmt
import LvmQSigLeafSound

/-!
# `Q_sig` at v6 (CA-3)

Season 1's child walk `qsigNoSl I` checks the child's header at the cells `I.hd + {0, 1…4, 5…8, 13,
14…17}` (`b`, `vk`, `c'`, `n`, `h`: season 1's header layout, `ChildOkS`). At v6 the child's header is
the seed query's `HDR` (FORMAT6 §2), at other stream words. **`hdrCopy6`** asserts, gated by the node
flag, that those cells equal the stream words of the seed's `HDR` (FORMAT6 v2.5: stream word `hdrW k = 11 + k`
for `HDR` word `k`; the same cells `Q_link` reads as the seed entry's words, `seedLane_hdrW`): `b` (word 1), `n`
(word 2), `h` (words 3–6), `c'` (words 7–10), `vk` (words 11–14); and that `HDR` word 0 is the magic and
`n = 2^18`. Then **`qsig6`** runs `qsigSC` (both walks, unchanged).

**`qsig6_sound`**: with the gate on and the walks' `KS` and `BITS` hypotheses (CB's sponge batch,
CD's `BITS` table), the child's signature verifies on the digest cells, `σ_leaf` verifies on
`traceDigest []`, `ChildOkS` holds on the copy, and the copies, the magic and `n = 2^18` hold.
No proof of the walks is redone: `qsigNoSl_sound` and `qSigLeaf_sound` are season 1's.
-/

set_option autoImplicit false

namespace Lvm6.Q

open RecursionFast Lvm Lvm.Loop Lvm.Loop.Build Lvm.QSig

/-- The magic word as a `K` constant (bytes `53 6C 76 6D 36 00 00 01`, little-endian). -/
def magicK : FK := w64 0x010000366D766C53

/-- `n = 2^18` as a `K` constant. -/
def nStarK : FK := w64 0x40000

/-- The copies `(cell of season 1's header, stream cell)`: `b`, `vk`, `c'`, `n`, `h`. -/
def hdrPairs6 (hd sb : ℕ) : List (ℕ × ℕ) :=
  [(hd, sb + hdrW 1)] ++ (List.range 4).map (fun l => (hd + 1 + l, sb + hdrW 11 + l)) ++
    (List.range 4).map (fun l => (hd + 5 + l, sb + hdrW 7 + l)) ++ [(hd + 13, sb + hdrW 2)] ++
    (List.range 4).map (fun l => (hd + 14 + l, sb + hdrW 3 + l))

/-- **The header copy**, gated by the flag `fg`: the copies, the magic, `n = 2^18`. -/
def hdrCopy6 (hd sb fg : ℕ) : BM Unit := do
  let _ ← seqAll ((hdrPairs6 hd sb).map fun pr => assertEq (kc pr.1) (kc pr.2) (kc fg))
  assertEqK (kc (sb + hdrW 0)) magicK (kc fg)
  assertEqK (kc (hd + 13)) nStarK (kc fg)

/-- **`Q_sig` at v6**: the header copy (stream cells from `sb`), then both walks. -/
def qsig6 (I Il : SigIn) (sb : ℕ) : BM (SigOut × WalkC) := do
  hdrCopy6 I.hd sb I.flag
  qsigSC I Il

/-! ## The header copy's rows -/

section
variable {c : Ctx} {M : Mem}

theorem assertEqK_spec' {a g : ℕ} {k : FK} {p : Ptr} (h : Ok c M (assertEqK (kc a) k (kc g)) p)
    (hg : M.k g = 1) : M.k a = k := by
  obtain ⟨h, hA⟩ := h
  rw [assertEqK, hold_bind] at h
  rw [assertEqK, assert_bind] at hA
  have h1 := linK_spec h.1
  have h2 := assert0K_spec (a := p.k) hA.2
  rw [hg, one_mul, h1, zero_mul, add_zero] at h2
  have := congrArg (· + k) h2
  simpa [add_assoc, FK.add_self] using this

theorem hdrCopy6_spec {hd sb fg : ℕ} {p : Ptr} (h : Ok c M (hdrCopy6 hd sb fg) p) (hg : M.k fg = 1) :
    (∀ pr ∈ hdrPairs6 hd sb, M.k pr.1 = M.k pr.2) ∧ M.k (sb + hdrW 0) = magicK ∧ M.k (hd + 13) = nStarK := by
  unfold hdrCopy6 at h
  obtain ⟨q1, h1, h2⟩ := ok_bind h
  obtain ⟨q2, h2, h3⟩ := ok_bind h2
  refine ⟨fun pr hpr => ?_, assertEqK_spec' h2 hg, assertEqK_spec' h3 hg⟩
  obtain ⟨q, hq⟩ := ok_seqAll _ _ h1 _ (List.mem_map.mpr ⟨pr, hpr, rfl⟩)
  exact assertEqKK_spec hq.1 hq.2 hg

end

/-! ## Soundness -/

theorem qsig6_out (I Il : SigIn) (sb : ℕ) (p : Ptr) :
    (qsig6 I Il sb p).1 = (qsigSC I Il (p.adv (hdrCopy6 I.hd sb I.flag p).2)).1 := by
  simp only [qsig6, out_bind_eq]

/-- **`Q_sig` at v6 is sound** (CA-3, cell level). -/
theorem qsig6_sound {c : Ctx} {M : Mem} {p : Ptr} {I Il : SigIn} {sb : ℕ}
    (hln : 1 ≤ I.ln ∧ I.ln ≤ 62) (h : Ok c M (qsig6 I Il sb) p) (hg : M.k I.flag = 1)
    (hks : SigKSin I M.k) (hbits : SigBits I (qsig6 I Il sb p).1.1 M.k)
    (hinj : ∀ a b, a < 1024 → b < 1024 → FK.x ^ a = FK.x ^ b → a = b)
    (hgl : M.k Il.flag = 1) (hksL : SigKSinC Il M.k) (hbitsL : SigBitsC Il (qsig6 I Il sb p).1.2.pa M.k) :
    SigOk (digAt M.k I.vk) (digAt M.k I.md) (sigAt' M.k I.sg) = true ∧
      SigOk (digAt M.k Il.vk) (traceDigest []) (sigAtP M.k Il.sg) = true ∧ ChildOkS I M.k ∧
      (∀ pr ∈ hdrPairs6 I.hd sb, M.k pr.1 = M.k pr.2) ∧ M.k (sb + hdrW 0) = magicK ∧
      M.k (I.hd + 13) = nStarK := by
  unfold qsig6 at h
  obtain ⟨hc, hS, -⟩ := ok_bind' h
  rw [qsig6_out] at hbits hbitsL
  set p1 := p.adv (hdrCopy6 I.hd sb I.flag p).2 with hp1
  unfold qsigSC at hS hbits hbitsL
  obtain ⟨h1, h2, -⟩ := ok_bind' hS
  obtain ⟨h2, -, -⟩ := ok_bind' h2
  simp only [out_bind_eq, pure_apply_eq] at hbits hbitsL
  obtain ⟨hsig, hchild⟩ := qsigNoSl_sound hln h1 hg hks hbits hinj
  have hZ : M.k (qsigNoSl I p1).1.pre.1.n = 0 := by
    obtain ⟨⟨q, hq, e⟩, -⟩ := qsigNoSl_parts h1
    have := gPre_spec hq.1
    rw [e] at this
    exact this.2.2.1
  have hleaf := qSigLeaf_sound h2 hgl hZ hksL hbitsL
  exact ⟨hsig, hleaf, hchild, hdrCopy6_spec hc hg⟩

end Lvm6.Q
