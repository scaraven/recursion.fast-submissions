-- New for `flock-recursive` (BLUEPRINT revision 4.1; stage R4e): controls of R4e's statements.
import FRSoundness4R4FrRS
import FRVerifierImplNode4T

/-!
# Controls for R4e (`Fields4`, the front's op parameters, the claim switches)

| Definition / parameter | Positive | Negative |
|---|---|---|
| `Fields4` | `fields4_of_accept` (every accepted run has one) | `not_fields4_nil` (no run on an empty trace) |
| the segment's op parameters (`hZ hLS hTS hST hSM hSW hLW hW hR` of `not_rejZ_seg4`, `not_rejS2_seg4`, `not_rejLc_seg4`, `not_rejRS4_seg`) | `segC_params` (the concrete segment ops `implSeg (implC …)` meet all of them) | `clR2_c0_dep` (the claim switch `clR2_c0_eq` needs its hypothesis: round 0's claim is `c0`'s) |
| the node's op parameters (`not_rejZ_node4`, `not_rejS2_node4`, `not_rejLc_node4`, `not_rejRS4_node`) | `nodeC_params` (S-CN4b's `implN4T` over 3.x's ops meets all of them; `targetS` by `targetSNode4_meets`) | as above |
| `lastAt_pad19` | `lastAt_pad19_ctl` (`lastBits` after 19 entries reads back `lastL`) | — (an equation) |
-/

namespace FR.Snd.R4
open RecursionFast Rev4 FR.Impl

variable {impl : OpImpl} {p : KindP} {inp : Input}

/-- (−) **No fields on an empty trace** (an accepted run's chain has 482 entries). -/
theorem not_fields4_nil {P : FinP} {y : List Val × List Bool × Trace} {zh : List Reg}
    {Rs : ℕ → Array Val} {Ex : ℕ → Array (List Reg)} : ¬ Fields4 impl p inp [] P y zh Rs Ex :=
  fun hF => by have := hF.sk.len; simp [fsOf] at this

/-- (+) **The concrete segment ops meet every op parameter of R4e's segment statements.** -/
theorem segC_params (fin : Finals) (lRows : List Circ.Row) (κs₀ : F) (σ : SegKind) :
    let impl := implSeg (implC fin lRows κs₀)
    (∀ a b, impl.eqZ a b = eqZS a b) ∧
      (∀ v l pe, v.size = 127 → impl.lagrangeS v l pe = lagrangeSS v l pe) ∧
      (∀ r, impl.targetS (KindP.ofSeg σ).tix r = targetSSegS r) ∧
      (∀ k a b c, c.size = 22 → impl.shiftTarget k a b c = shiftTargetS k a b c) ∧
      (∀ a b, impl.shiftMask a b = shiftSegS a b) ∧ (∀ κ s a b, impl.slotW κ s a b = slotWS s a b) ∧
      (∀ tt rr, impl.linkWAll (KindP.ofSeg σ).tix tt rr = Array.replicate nLinkFam 0) ∧
      (∀ rw cw, rw.size = 2 ^ 14 → cw.size = 2 ^ 14 →
        impl.walkAB rw cw = (Eval.walkSpecA rw cw, Eval.walkSpecB rw cw)) ∧
      ∀ l a, impl.rowW l a = rowWS l a := by
  intro impl
  have hm := implSegC_meets fin lRows κs₀
  obtain ⟨hST, hSM, hSW, hLW⟩ := segOps_of_meets hm σ
  obtain ⟨h1, h2, h3, -, -, -, h7, -, -, -, -, -, -, -, -, h16, -⟩ := hm
  refine ⟨fun a b => ?_, fun v l pe hv => ?_, fun r => ?_, hST, hSM, hSW, hLW, fun rw cw h1' h2' => ?_,
    fun l a => ?_⟩
  · rw [h3]; simp only [specSeg, Impl.specC, Impl.specCWith]
  · rw [h1 v l pe hv]; simp only [specSeg, Impl.specC, Impl.specCWith]
  · rw [h2]; simp only [specSeg, Impl.specC, Impl.specCWith]; rfl
  · rw [h7 rw cw h1' h2']; simp only [specSeg, Impl.specC, Impl.specCWith]
  · rw [h16]; simp only [specSeg, Impl.specC, Impl.specCWith]

/-- (−) **The claim switch needs its hypothesis**: round 0's claim is `c0`'s, so two different
first claims give different round-0 claims. -/
theorem clR2_c0_dep (L es : Log) :
    clR2 0 16 readF (fun d => chF d 0) (fun _ _ => (0 : F)) L es 0 ≠
      clR2 0 16 readF (fun d => chF d 0) (fun _ _ => (1 : F)) L es 0 := by
  simp [clR2]

/-- (+) `lastAt` reads back `lastL` from `lastBits` placed after 19 entries. -/
theorem lastAt_pad19_ctl (es : Log) :
    lastAt ((List.replicate 19 (0 : F)) ++ P4a.lastBits es).toArray 19 = P4a.lastL es :=
  lastAt_pad19 es _ (by simp)

/-- (+) **S-CN4b's node ops (`implN4T` over 3.x's `implC`) meet every op parameter of R4e's node
statements** (`targetS` through `implN4T_meets`, i.e. `targetSNode4_meets`). -/
theorem nodeC_params (fin : Finals) (lRows : List Circ.Row) (κs₀ : F) (ν : NodeKind) :
    let impl := NI4T.implN4T (fun _ => implC fin lRows κs₀) ν
    (∀ a b, impl.eqZ a b = eqZS a b) ∧
      (∀ v l pe, v.size = 127 → impl.lagrangeS v l pe = lagrangeSS v l pe) ∧
      (∀ r, impl.targetS (KindP.ofNode ν).tix r = NT4.targetSNode4S ν r) ∧
      (∀ k a b c, c.size = 22 → impl.shiftTarget k a b c = shiftTargetS k a b c) ∧
      (∀ a b, impl.shiftMask a b = NT4.shiftMask4S ν a b) ∧ (∀ κ s a b, impl.slotW κ s a b = slotWS s a b) ∧
      (∀ tt rr, impl.linkWAll (KindP.ofNode ν).tix tt rr = NT4.linkWAll4S ν tt rr) ∧
      (∀ rw cw, rw.size = 2 ^ 14 → cw.size = 2 ^ 14 →
        impl.walkAB rw cw = (Eval.walkSpecA rw cw, Eval.walkSpecB rw cw)) ∧
      ∀ l a, impl.rowW l a = rowWS l a := by
  intro impl
  have hm : impl.Meets (NI4.specN4 (fun _ => specC fin lRows κs₀) ν) :=
    NI4T.implN4T_meets ν (implC_meets fin lRows κs₀)
  obtain ⟨hST, hSM, hSW, hLW⟩ := nodeOps_of_meets hm rfl
  obtain ⟨h1, h2, h3, -, -, -, h7, -, -, -, -, -, -, -, -, h16, -⟩ := hm
  refine ⟨fun a b => ?_, fun v l pe hv => ?_, fun r => ?_, hST, hSM, hSW, hLW, fun rw cw h1' h2' => ?_,
    fun l a => ?_⟩
  · rw [h3]; simp only [NI4.specN4, Impl.withRS4S, Impl.specC, Impl.specCWith]
  · rw [h1 v l pe hv]; simp only [NI4.specN4, Impl.withRS4S, Impl.specC, Impl.specCWith]
  · rw [h2]; simp only [NI4.specN4, Impl.withRS4S, Impl.specC, Impl.specCWith]; rfl
  · rw [h7 rw cw h1' h2']; simp only [NI4.specN4, Impl.withRS4S, Impl.specC, Impl.specCWith]
  · rw [h16]; simp only [NI4.specN4, Impl.withRS4S, Impl.specC, Impl.specCWith]

end FR.Snd.R4
