-- lvm2 X-REC2 (helper DEC): the agreement scan of `C_rec`'s level-1 decoder. Adapted from this entry's
-- `LvmXAgree.lean` (v1's `agreeIR`, itself from rf-k FRXAgree@8bff272b): the scan loop, the comparison
-- and the append are v1's with `2^12` positions; the fold multiplies `E` lanes (three leaf words, loaded by
-- `LvmXEqT.eqtLdE`) by `E` weights with `mulE` (new), where v1's multiplied `K` words by `E` weights.
import LvmXDec1
import LvmXEqT

-- (GOLF2: 14 declarations that `certified` does not use moved verbatim to `LvmNodeSoundCircOff`, outside its import closure.)

/-!
# The level-1 agreement set on the machine

* `agree1IR wB qB eB agB`: for every position `q < 2^12`, the fold
  `Σ_{u<16} E[qB + 3u] · E[wB + 48q + 3u]` (`fold1IR`, `E` products), compared with the three
  coordinates of `Enc₁(f₂)[q]` at `eB + c·2^12 + q` (`test1IR`); the position is appended to the
  list at `agB` (v1's `appendIR`) when they agree (`agree1IR_sem`: the count is `|agree1M|` and
  the list is `agree1M`).
* **`agree1M_eq_agree1L`**: with the table of `eq(α, ·)` and `Enc₁(f₂)`'s coordinates, `agree1M`
  is the pure decoder's `agree1L`.

Registers: v1's scalars `188 … 205` (`gQ` … `gN2`), the `E` registers `34 … 45` (`h1A`
accumulator, `h1S` weight, `h1W` lane, `h1T` product); `mulE`'s scratch `5 … 24`.
-/

namespace Lvm.X

open RecursionFast Finset Lvm.Nb CompPoly.Extension BF64

attribute [local irreducible] entryK storeM

/-! ## Registers -/

/-- The fold's accumulator (`E`, `34 … 36`). -/ def h1A : ℕ := 34
/-- A weight `eq(α, u)` (`E`, `37 … 39`). -/ def h1S : ℕ := 37
/-- A lane (`E`, `40 … 42`). -/ def h1W : ℕ := 40
/-- A product (`E`, `43 … 45`). -/ def h1T : ℕ := 43

/-! ## The programs -/

/-- **One lane `u`**: the weight at `M[gPe]`, the lane at `M[gPw]` (both `+= 3`), their product
added to the accumulator. -/
def lane1Body : XIR :=
  .seq (eqtLdE h1S gPe) (.seq (eqtLdE h1W gPw) (.seq (mulE h1T h1S h1W)
    (.blk [.op .xor h1A h1A h1T, .op .xor (h1A + 1) (h1A + 1) (h1T + 1),
      .op .xor (h1A + 2) (h1A + 2) (h1T + 2)])))

/-- **The fold at the position `gQ`**: `h1A := Σ_{u<16} E[qB + 3u] · E[wB + 48q + 3u]`. -/
def fold1IR (wB qB : ℕ) : XIR :=
  .seq (.blk [.const h1A 0, .const (h1A + 1) 0, .const (h1A + 2) 0, .const gK 48,
      .op .mul gPw gQ gK, .const gK (toWord wB), .op .add gPw gPw gK, .const gPe (toWord qB),
      .const gN2 16])
    (.loopK gC2 gN2 16 lane1Body)

/-- **The comparison** with `Enc₁(f₂)[q]`'s coordinates at `eB + c·2^12 + q`:
`gZ := [all three equal]`. -/
def test1IR (eB : ℕ) : XIR :=
  .seq (.blk [.const gK (toWord eB), .op .add gX gQ gK]) (.seq (.load gE gX)
    (.seq (.blk [.op .eq gZ gE h1A, .const gK (toWord (2 ^ 12)), .op .add gX gX gK])
      (.seq (.load gE gX) (.seq (.blk [.op .eq gZ2 gE (h1A + 1), .op .and gZ gZ gZ2,
        .op .add gX gX gK])
        (.seq (.load gE gX) (.blk [.op .eq gZ2 gE (h1A + 2), .op .and gZ gZ gZ2]))))))

/-- **One position**: the fold, the comparison, the append, `q += 1`. -/
def pos1Body (wB qB eB agB : ℕ) : XIR :=
  .seq (fold1IR wB qB) (.seq (test1IR eB) (.seq (.ite gZ (appendIR agB) (.blk []))
    (.blk [.op .add gQ gQ cOne])))

/-- **The level-1 agreement scan** over the positions `q < 2^12`. -/
def agree1IR (wB qB eB agB : ℕ) : XIR :=
  .seq (.blk [.const gQ 0, .const gCnt 0, .const gN1 (toWord (2 ^ 12))])
    (.loopK gC1 gN1 (toWord (2 ^ 12)) (pos1Body wB qB eB agB))

/-! ## The machine's agreement list -/

/-- The fold at position `q` over the lanes `u < j` on the heap `M`. -/
def fold1PM (M : Mem) (wB qB q j : ℕ) : Ext3 :=
  ∑ u ∈ range j, rdE M (qB + 3 * u) * rdE M (wB + 48 * q + 3 * u)

/-! ## Well formed, no tape loop, no output, cost -/

-- adapted from LvmXAgree.lean (`wf_agreeIR`, `noLoopT_agreeIR`, `outs_agreeIR`, `cost_posBody`,
-- `cost_agreeIR`)
theorem wf_agree1IR (wB qB eB agB : ℕ) : WF (agree1IR wB qB eB agB) := by
  simp +decide [agree1IR, pos1Body, fold1IR, lane1Body, eqtLdE, eqtLd1, mulE, mulEC, redC, test1IR,
    appendIR, WF, Writes, Prim.dst, gQ, gPw, gPe, h1A, h1S, h1W, h1T, gE, gX, gZ, gZ2, gCnt, gK,
    gC1, gN1, gC2, gN2, cOne]

theorem noLoopT_agree1IR (wB qB eB agB : ℕ) : NoLoopT (agree1IR wB qB eB agB) := by
  simp [agree1IR, pos1Body, fold1IR, lane1Body, eqtLdE, eqtLd1, mulE, test1IR, appendIR, NoLoopT]

theorem outs_agree1IR (wB qB eB agB t : ℕ) : outs (agree1IR wB qB eB agB) t = 0 := by
  simp [agree1IR, pos1Body, fold1IR, lane1Body, eqtLdE, eqtLd1, mulE, test1IR, appendIR, outs]

theorem cost_pos1Body (wB qB eB agB t : ℕ) : cost (pos1Body wB qB eB agB) t = 2146 := by
  simp only [pos1Body, fold1IR, lane1Body, eqtLdE, eqtLd1, test1IR, appendIR, cost, cost_mulE,
    blkSteps, List.length_cons, List.length_nil]
  norm_num

/-- **The scan's exact cost**: `2^12` positions of `2,146` steps (`≈ 2^23.07`). -/
theorem cost_agree1IR (wB qB eB agB t : ℕ) : cost (agree1IR wB qB eB agB) t = 8802318 := by
  simp only [agree1IR, cost, cost_pos1Body, blkSteps, List.length_cons, List.length_nil,
    toNat_toWord (show 2 ^ 12 < 2 ^ 64 by norm_num)]
  norm_num

/-! ## The fold: one lane, the lane loop -/

/-- `mulE h1T h1S h1W` writes `mulE`'s scratch and the product, nothing else. -/
theorem mulE1_frame {I : Array Word} {s : St} {i : ℕ} (hi : i < 5 ∨ 25 ≤ i)
    (hT : i < h1T ∨ h1T + 3 ≤ i) : rd (semXIR I (mulE h1T h1S h1W) s).M i = rd s.M i := by
  rw [mulE, sem_blk]
  refine rd_runPrims_of_not_writes (fun p hp => ?_) s.M
  have := mulEC_dst h1T h1S h1W p hp
  simp only [h1T] at this hT
  (clear * - hi hT this; omega)

/-- The accumulate block: `h1A += h1T` in `E` (three xors, characteristic 2). -/
theorem acc1_sem (I : Array Word) (s : St) (hM : Inv s.M) :
    rdE (semXIR I (.blk [.op .xor h1A h1A h1T, .op .xor (h1A + 1) (h1A + 1) (h1T + 1),
      .op .xor (h1A + 2) (h1A + 2) (h1T + 2)]) s).M h1A = rdE s.M h1A + rdE s.M h1T ∧
    (∀ i, (i < h1A ∨ h1A + 3 ≤ i) → rd (semXIR I (.blk [.op .xor h1A h1A h1T,
      .op .xor (h1A + 1) (h1A + 1) (h1T + 1), .op .xor (h1A + 2) (h1A + 2) (h1T + 2)]) s).M i =
      rd s.M i) ∧
    Inv (semXIR I (.blk [.op .xor h1A h1A h1T, .op .xor (h1A + 1) (h1A + 1) (h1T + 1),
      .op .xor (h1A + 2) (h1A + 2) (h1T + 2)]) s).M := by
  have hs := hM.1
  simp only [regs] at hs
  refine ⟨?_, fun i hi => rd_blk_of_not_dst I _ s ?_,
    inv_sem I (by simp +decide [WF]) hM⟩
  · simp only [rdE, rdK, sem_blk, runPrims, List.foldl, Prim.run]
    simp (disch := first | decide | (simp only [size_set, h1A, h1T]; omega)) only
      [rd_set_self, rd_set_ne]
    simp only [eval_xor, wK_xor]
    rw [mkE_add]
  · simp only [List.mem_cons, List.mem_nil_iff, or_false]
    rintro p (rfl | rfl | rfl) <;> simp only [Prim.dst, h1A] at hi ⊢ <;> (clear * - hi; omega)

/-- **One lane**: the weight at `pe` and the lane at `pw` (`E`, three words each), their product
added to the accumulator; `gPe := pe + 3`, `gPw := pw + 3`. -/
theorem lane1Body_sem (I : Array Word) (s : St) (hM : Inv s.M) {pw pe : ℕ} (hpwR : regs ≤ pw)
    (hpw : pw + 3 < 2 ^ 64) (hpeR : regs ≤ pe) (hpe : pe + 3 < 2 ^ 64)
    (hW : rd s.M gPw = toWord pw) (hP : rd s.M gPe = toWord pe) :
    rdE (semXIR I lane1Body s).M h1A = rdE s.M h1A + rdE s.M pe * rdE s.M pw ∧
    rd (semXIR I lane1Body s).M gPw = toWord (pw + 3) ∧
    rd (semXIR I lane1Body s).M gPe = toWord (pe + 3) ∧
    (∀ i, (i < 5 ∨ 46 ≤ i) → i ≠ gPe → i ≠ gPw → rd (semXIR I lane1Body s).M i = rd s.M i) ∧
    Inv (semXIR I lane1Body s).M := by
  have hs := hM.1
  simp only [regs] at hs hpwR hpeR
  rw [lane1Body, semXIR_seq]
  obtain ⟨l1, l2, l3, hM1⟩ := eqtLdE_sem I s hM (d := h1S) (p := gPe) (x := pe) (by decide)
    (by decide) (by decide) (by decide) (by decide) hP (by simp only [regs]; omega) hpe
  generalize semXIR I (eqtLdE h1S gPe) s = s1 at l1 l2 l3 hM1
  rw [semXIR_seq]
  obtain ⟨m1, m2, m3, hM2⟩ := eqtLdE_sem I s1 hM1 (d := h1W) (p := gPw) (x := pw) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by rw [l3 _ (by decide) (by decide), hW])
    (by simp only [regs]; omega) hpw
  generalize semXIR I (eqtLdE h1W gPw) s1 = s2 at m1 m2 m3 hM2
  rw [semXIR_seq]
  have p3 : rdE (semXIR I (mulE h1T h1S h1W) s2).M h1T = rdE s2.M h1S * rdE s2.M h1W :=
    mulE_sem hM2 (by decide) (by decide) (by decide) (by decide)
  have f3 : ∀ i, (i < 5 ∨ 25 ≤ i) → (i < h1T ∨ h1T + 3 ≤ i) →
      rd (semXIR I (mulE h1T h1S h1W) s2).M i = rd s2.M i := fun i h1 h2 => mulE1_frame h1 h2
  have hM3 := inv_sem I (wf_mulE h1T h1S h1W (by decide)) hM2
  generalize semXIR I (mulE h1T h1S h1W) s2 = s3 at p3 f3 hM3
  obtain ⟨a1, a2, hM4⟩ := acc1_sem I s3 hM3
  generalize semXIR I (.blk [.op .xor h1A h1A h1T, .op .xor (h1A + 1) (h1A + 1) (h1T + 1),
    .op .xor (h1A + 2) (h1A + 2) (h1T + 2)]) s3 = s4 at a1 a2 hM4
  have kA : rdE s3.M h1A = rdE s.M h1A := eqt_rdE_eq
    (by rw [f3 _ (by decide) (by decide), m3 _ (by decide) (by decide), l3 _ (by decide) (by decide)])
    (by rw [f3 _ (by decide) (by decide), m3 _ (by decide) (by decide), l3 _ (by decide) (by decide)])
    (by rw [f3 _ (by decide) (by decide), m3 _ (by decide) (by decide), l3 _ (by decide) (by decide)])
  have kS : rdE s2.M h1S = rdE s.M pe := by
    rw [← l1]
    exact eqt_rdE_eq (m3 _ (by decide) (by decide)) (m3 _ (by decide) (by decide))
      (m3 _ (by decide) (by decide))
  have kW : rdE s1.M pw = rdE s.M pw := eqt_rdE_eq
    (l3 _ (by simp only [h1S]; (clear * - hpwR hpw; omega)) (by simp only [gPe]; (clear * - hpwR hpw; omega)))
    (l3 _ (by simp only [h1S]; (clear * - hpwR hpw; omega)) (by simp only [gPe]; (clear * - hpwR hpw; omega)))
    (l3 _ (by simp only [h1S]; (clear * - hpwR hpw; omega)) (by simp only [gPe]; (clear * - hpwR hpw; omega)))
  refine ⟨?_, ?_, ?_, fun i i1 i2 i3 => ?_, hM4⟩
  · rw [a1, kA, p3, kS, m1, kW]
  · rw [a2 _ (by decide), f3 _ (by decide) (by decide), m2]
  · rw [a2 _ (by decide), f3 _ (by decide) (by decide), m3 _ (by decide) (by decide), l2]
  · simp only [h1A, h1T, h1W, h1S] at *
    rw [a2 i (by (clear * - i1 i2 i3; omega)), f3 i (by (clear * - i1 i2 i3; omega)) (by (clear * - i1 i2 i3; omega)), m3 i (by (clear * - i1 i2 i3; omega)) i3, l3 i (by (clear * - i1 i2 i3; omega)) i2]

/-- The registers and cells `fold1IR` keeps. -/
def Keep1F (r : ℕ) : Prop :=
  (r < 5 ∨ 46 ≤ r) ∧ r ≠ gPe ∧ r ≠ gPw ∧ r ≠ gK ∧ r ≠ gC2 ∧ r ≠ gN2 ∧ r ≠ cTmp

theorem keep1F_of_regs {r : ℕ} (h : regs ≤ r) : Keep1F r := by
  simp only [Keep1F, regs, gPe, gPw, gK, gC2, gN2, cTmp] at *; omega

/-! ## The comparison -/

-- adapted from LvmXAgree.lean (`lo_testIR`, `testIR_sem`)
/-! ## One position and the scan -/

theorem keep1F_gQ : Keep1F gQ := by unfold Keep1F; decide
theorem keep1F_gCnt : Keep1F gCnt := by unfold Keep1F; decide

theorem mkE_eq_iff {a₀ a₁ a₂ b₀ b₁ b₂ : BF64} :
    mkE a₀ a₁ a₂ = mkE b₀ b₁ b₂ ↔ a₀ = b₀ ∧ a₁ = b₁ ∧ a₂ = b₂ :=
  ⟨mkE_inj, fun ⟨h0, h1, h2⟩ => by rw [h0, h1, h2]⟩

-- adapted from LvmXAgree.lean (`posBody_sem`)
-- adapted from LvmXAgree.lean (`agreeM_succ`, `length_agreeM_le`, `agreeP_congr`)
/-! ## Semantics -/

-- adapted from LvmXAgree.lean (`agreeIR_sem`)
-- adapted from LvmXDecBr.lean (`agreeP_iff`, `agreeM_eq_filter`)
end Lvm.X
