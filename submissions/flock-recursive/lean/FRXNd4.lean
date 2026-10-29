-- New for `flock-recursive` (BLUEPRINT revision 4.1, §6.2 steps 1–5, B-14; stage S-H4, pass 11, item 5: the
-- node branch `nd` and its decode law). 3.x analogue: `FRXNode.decNode`, `FRXNodeRun.ext_node`.
import FRXOut4O
import FRX4Ext

/-!
# The revision 4.1 node branch `nd`

**`nd`** dispatches on the node byte (`ndK4`) and runs, at node kind `κ`, the decode `decF04 κ`
(index, level 0's read, the chain, the five levels: `f⁽⁰⁾`'s rows `1 … 7` on the heap) and then the
output `outIR4 κ` (the node witness's words).

* **`decOk4_nd`**: `DecOk4 nd` — well formed, the loop bounds on every domain tape of a proof of
  `piSizeOf seq4` bytes (`safe_decF04`; the output has no tape loop), the cost within `decBudget4`
  (`cost_le_decF04` and `cso_outIR4`), at most `outCap` output words, at most `2^19` statements.
* **`nodeDec4_nd`**: the decode law `NodeDec4 nd` with links **`LinksD4`** (exactly `decF04_sem`'s
  hypotheses on the log and its transcript) and witness **`readW4 sigH`**: on a node proof in the
  domain whose links hold, `nd` outputs `witWords (readW4 sigH κ L es)` (`decF04_wF`, `outIR4_sem`),
  and the witness fits the output format (`readW4_fits`).

S-L4's `links4_sigH` discharges `Links4 nd nodeDec4_nd` from `Gaps4`.
-/

namespace FR.X.X4

open RecursionFast FR.X FR.Rev4 FR.Snd

/-! ## The node branch -/

/-- **The revision 4.1 node branch**: per node kind, the decode then the output. -/
def nd : XIR :=
  ndK4 (.seq (decF04 .N2) (outIR4 .N2)) (.seq (decF04 .N4) (outIR4 .N4)) (.seq (decF04 .N8) (outIR4 .N8))

/-! ## `DecOk4 nd` -/

theorem noLoopT_kindNd4 : NoLoopT kindNd4 := by simp [NoLoopT, kindNd4, readAt]

theorem cost_kindNd4 (t : ℕ) : cost kindNd4 t = 15 := by
  rw [cost_noLoopT _ noLoopT_kindNd4 t]; decide

theorem outs_kindNd4 (t : ℕ) : outs kindNd4 t = 0 := by
  rw [outs_noLoopT _ noLoopT_kindNd4 t]; decide

theorem sizeIR_decF04 : sizeIR (decF04 .N2) = 57067 ∧ sizeIR (decF04 .N4) = 57067 ∧ sizeIR (decF04 .N8) = 57067 := by
  decide +kernel

theorem cost_outIR4 (κ : NodeKind) (t : ℕ) : cost (outIR4 κ) t ≤ 600000000 := by
  rw [cost_noLoopT _ (noLoopT_outIR4 κ) t]; exact (cso_outIR4 κ).1

theorem outs_outIR4 (κ : NodeKind) (t : ℕ) : outs (outIR4 κ) t ≤ 2300000 := by
  rw [outs_noLoopT _ (noLoopT_outIR4 κ) t]; exact (cso_outIR4 κ).2.1

/-- **The node branch meets `DecOk4`.** -/
theorem decOk4_nd : DecOk4 nd where
  wf := ⟨wf_kindNd4, ⟨wf_decF04 .N2, wf_outIR4 .N2⟩, ⟨wf_decF04 .N4, wf_outIR4 .N4⟩, ⟨wf_decF04 .N8, wf_outIR4 .N8⟩⟩
  safe := fun c π L hs hq ht => .seq (safe_of_noLoopT noLoopT_kindNd4)
    (.ite (.seq (safe_decF04 .N2 c π L hs hq ht) (safe_of_noLoopT (noLoopT_outIR4 _)))
      (.ite (.seq (safe_decF04 .N4 c π L hs hq ht) (safe_of_noLoopT (noLoopT_outIR4 _)))
        (.seq (safe_decF04 .N8 c π L hs hq ht) (safe_of_noLoopT (noLoopT_outIR4 _)))))
  cost := fun t => by
    obtain ⟨d2, d4, d8⟩ := cost_le_decF04 t
    have o2 := cost_outIR4 .N2 t
    have o4 := cost_outIR4 .N4 t
    have o8 := cost_outIR4 .N8 t
    simp only [nd, ndK4, cost, cost_kindNd4, decBudget4, fuelBase, fuelPerWord]
    omega
  outs := fun t => by
    have o2 := outs_outIR4 .N2 t
    have o4 := outs_outIR4 .N4 t
    have o8 := outs_outIR4 .N8 t
    simp only [nd, ndK4, outs, outs_kindNd4, outs_decF04, outCap]
    omega
  size := by
    obtain ⟨z2, z4, z8⟩ := sizeIR_decF04
    have o2 := (cso_outIR4 .N2).2.2
    have o4 := (cso_outIR4 .N4).2.2
    have o8 := (cso_outIR4 .N8).2.2
    have k : sizeIR kindNd4 = 15 := by decide
    simp only [nd, ndK4, sizeIR, z2, z4, z8, k]
    omega

/-! ## The decode law -/

theorem pickNd_eq (κ : NodeKind) :
    pickNd κ (.seq (decF04 .N2) (outIR4 .N2)) (.seq (decF04 .N4) (outIR4 .N4)) (.seq (decF04 .N8) (outIR4 .N8)) =
      .seq (decF04 κ) (outIR4 κ) := by cases κ <;> rfl

/-- **The node branch outputs the node witness** read off `f⁽⁰⁾` (`readW4 sigH`), on a node proof in
the domain whose log and transcript meet the links `LinksD4`. -/
theorem nd_out {κ : NodeKind} {c : Digest} {π : Proof} {L es : Log} (hN : kindOf4 π = .node κ) (hD : InDomE c π L)
    (hl : LinksD4 κ L es π c) :
    (semXIR (extractorInput c π L).toArray nd (st1 c π L)).o.toList = witWords (readW4 sigH κ L es) := by
  obtain ⟨hb, hz⟩ := kindOf4_node hN
  obtain ⟨hS, ⟨st₀, hfm⟩, hcap, hfin, hfar, hA⟩ := hl
  have hps : π.size = piSizeOf seq4 := hz.trans piSizeOf_seq4.symm
  have hpL : pL4 = 99779 := fmt4_vals.1
  have hD4 : Dom4 pL4 c π L := ⟨by rw [hz, hpL], hD.2.1, hD.2.2⟩
  have hM := inv_st1 c π L
  have hsz0 : (st1 c π L).M.size = memX4 + mpwX * (extractorInput c π L).length := by
    simp [st1, initSt]
  have hlen : memX4 + L.length + L.length ≤ memX4 + mpwX * (extractorInput c π L).length := by
    have h1 := tape_entries_end4 c π L hD4.hs
    have h2 := len_entries L
    simp only [mpwX]; omega
  have hπ : 0 < π.size := by omega
  rw [nd, ndK4_sem c π L hb hπ _ _ _ _ hM, pickNd_eq, semXIR_seq]
  obtain ⟨-, -, -, hM1, ho1, hz1⟩ := kindNd4_sem c π L hπ (st1 c π L) hM
  generalize semXIR (tp c π L) kindNd4 (st1 c π L) = s1 at hM1 ho1 hz1
  have hsz1 : memX4 + L.length + L.length ≤ s1.M.size := by rw [hz1, hsz0]; exact hlen
  have hW := decF04_wF κ c π L hD4 hps hS st₀ hfm hcap hfin hfar hA s1 hM1 hsz1
  have hB : BoundsOk (tp c π L) (extractorInput c π L).length (decF04 κ) s1 :=
    boundsOk_of_safe (safe_decF04 κ c π L hps hD.2.1 hD.2.2) (wf_decF04 κ) _ hM1
  have ho := outs_le (extractorInput c π L).length (decF04 κ) s1 (wf_decF04 κ) hM1 hB
  rw [outs_decF04, ho1, st1_o] at ho
  have hM2 := inv_sem (tp c π L) (wf_decF04 κ) hM1
  have hz2 := size_sem (tp c π L) (decF04 κ) s1
  generalize semXIR (tp c π L) (decF04 κ) s1 = s2 at hW ho hM2 hz2
  have ho2 : s2.o = #[] := by simpa using ho
  rw [outIR4_sem (tp c π L) κ hM2 (by rw [hz2, hz1, hsz0]; simp only [memX4, bufB]; omega) hW, ho2,
    Array.toList_empty, List.nil_append]

/-- **The revision 4.1 decode law** of `nd`: links `LinksD4`, witness `readW4 sigH`. -/
noncomputable def nodeDec4_nd : NodeDec4 nd :=
  ⟨LinksD4, readW4 sigH, fun _ _ _ _ _ hN hD hl => ⟨nd_out hN hD hl, readW4_fits _ _ _⟩⟩

/-! ## Controls -/

/-- (+) `nd` is a different branch from `ndNone` (it outputs on a node proof), and (−) its size is not
`ndNone`'s. -/
theorem nd_ne_ndNone : nd ≠ ndNone := fun h => by
  have := congrArg sizeIR h
  obtain ⟨z2, -, -⟩ := sizeIR_decF04
  simp only [ndNone, nd, ndK4, sizeIR, z2, blkSteps, List.length_nil, ↓reduceIte] at this
  omega

end FR.X.X4
