-- New for `flock-recursive` (BLUEPRINT revision 4.1, B-12, B-13, §5; stage X4, items 2–3): the segment
-- law and the node truths from the composed front, T4's tail and the program layer's run facts.
import FRSoundness4XFront
import FRNodeCircuit4Dig

/-!
# The per-kind laws at revision 4.1

On a good log (`GoodX`: within `logCap`, potential `muT` of the composed front below `1`), an
accepted run whose chain has T4's `AcceptTail` has no composed doom on any prefix
(`T4.tail_of_accept`). Phase 2's doom on the three-entry prefix is the split statement
(`stmt_split4X`), so **the prefix meets `Stmt4`** (`stmt4_of_tail`):
* a segment's Z and S truths, hence its chain step (`chainEnd_of_truths`): **`segSound_X`**;
* a node's `StmtN4` on `f⁽⁰⁾` at the log's public digests: **`nodeRun_X`**, the per-run input of
  S-E12a's `nodeLaws4C'`.

What the program layer must still deliver for an accepted run is one named residual,
**`RunFacts4`**: the run's chain is an `AcceptTail` of the composed front (R4's
`acceptTail4_of_run` with `FinRest4`'s `pf0`/`enc`/`fin`, R4h's), and the log's statement reads
are the run's (`SegLog`, `NodeLog`; R4's statement views).
-/

namespace FR.Snd.X4
open RecursionFast FR.Merkle FR.Rev4 Finset

set_option linter.constructorNameAsVariable false

/-- **The good logs** for the composed front: within `logCap`, below potential `1`. -/
def GoodX (DFhi : ℕ → Log → Log → Prop) (L : Log) : Prop :=
  L.length ≤ logCap ∧ T4.muT (T4.RejC RejFX c0X) (T4.DkC (DFX DFhi) W0X c0X) L < 1

/-- **A segment's statement on the log**: the chain's kind, start digest, end digest and count. -/
def SegLog (v : SegView) (es : Log) : Prop :=
  kindOfC es = .seg v.kind ∧ bytesAt (entAt es 0).1 87 32 = v.start ∧
    bytesAt (msgAt es 1) 1 32 = v.h ∧ P4a.nStmt es = v.n

/-- **A node's statement on the log**: the chain's kind, the key it carries and the absorbed
statement digests. -/
def NodeLog (κ : NodeKind) (vk c : Digest) (π : Proof) (es : Log) : Prop :=
  kindOfC es = .node κ ∧ X.vkOf π = vk ∧ vkL es = vk ∧ c = nodeStmt (stL es 0) (stL es 1)

/-- **The program layer's residual**: every accepted run on a log without collisions or state hits
has a chain that is an `AcceptTail` of the composed front and whose statement reads are the
run's. A segment run is asked for only on the proofs `V_A` runs (INT-10, R4i's F1): `π` of
`piSizeOf seq4` bytes (`VAwith`'s size check, `piSize_aggSegs`) and `n ≤ cap` (`aggChecks`). -/
structure RunFacts4 (Vseg : SegProgs) (Vnode : NodeProgs) (vk : Digest) : Prop where
  seg : ∀ L π v, ¬ Bad L → segView π = some v → π.size = piSizeOf seq4 → v.n ≤ v.kind.cap →
    (Vseg v.kind vk (segC v) π).runLog L = some true →
    ∃ j, T4.AcceptTail RejFX W0X c0X L j ∧ SegLog v (entriesOf L (pathOf L j))
  node : ∀ κ L c π, ¬ Bad L → kindOf4 π = .node κ → (Vnode κ vk c π).runLog L = some true →
    ∃ j, T4.AcceptTail RejFX W0X c0X L j ∧ NodeLog κ vk c π (entriesOf L (pathOf L j))

theorem agree_take3 {es : Log} (h : 3 ≤ es.length) : Agree (es.take 3) es 3 := by
  have e := agree_append (es.take 3) (es.drop 3) (n := 3) (by simp; omega)
  rw [List.take_append_drop] at e
  exact fun p hp => (e p hp).symm

/-- **The three-entry prefix of an accepted chain meets the statement**. -/
theorem stmt4_of_tail {DFhi : ℕ → Log → Log → Prop} (hH : FrontHi DFhi) {L : Log} {j : ℕ}
    (hG : GoodX DFhi L) (hT : T4.AcceptTail RejFX W0X c0X L j) :
    3 ≤ (entriesOf L (pathOf L j)).length ∧
      P4a.Stmt4 src4 T4.zW lRows4 nodeIRows4 pvL L ((entriesOf L (pathOf L j)).take 3) := by
  have hlen : 3 ≤ (entriesOf L (pathOf L j)).length := by
    have := hT.len; rw [T4.pfStart_eq] at this; omega
  refine ⟨hlen, ?_⟩
  by_contra h
  obtain ⟨hnd, -⟩ := T4.tail_of_accept (frontObl_X hH).loc (frontChainStab_X hH) hG.2 hT
  apply hnd 2 (by omega)
  refine .inr ?_
  have hl : ((entriesOf L (pathOf L j)).take (2 + 1)).length - 1 = 2 := by
    rw [List.length_take]; omega
  unfold DPos T4.Dp
  rw [hl, P4a.ph_vals4a.1, T4.DkC, if_pos (by norm_num), DFX_lo (by norm_num)]
  exact stmt_split4X h

/-! ## The segment law -/

/-- **`SegSoundLog` at revision 4.1** (B-12): an accepted segment run on a good log proves its
chain step, given the program layer's `RunFacts4.seg` and the front's `FrontHi`. -/
theorem segSound_X {DFhi : ℕ → Log → Log → Prop} (hH : FrontHi DFhi) {Vseg : SegProgs}
    {Vnode : NodeProgs} {vk : Digest} (hR : RunFacts4 Vseg Vnode vk) :
    SegSoundLog Vseg vk (GoodX DFhi) := by
  intro L π v hG hv hπ hn hcap hrun
  obtain ⟨hb, -, -⟩ := T4.muT_lt_one hG.2
  obtain ⟨j, hT, hk, hst, hh, hnS⟩ := hR.seg L π v hb hv hπ hcap hrun
  obtain ⟨hlen, hSt⟩ := stmt4_of_tail hH hG hT
  set es := entriesOf L (pathOf L j)
  have hA := agree_take3 hlen
  have hk3 : kindOfC (es.take 3) = .seg v.kind := (kindOfC_congr (hA.mono (by norm_num))).trans hk
  have hn3 : P4a.nStmt (es.take 3) = v.n := (P4a.nStmt_congr hA (by norm_num)).trans hnS
  have hcap' : v.n ≤ 2 ^ P4a.nbC (.seg v.kind) := hcap
  have hL := P4a.lastL_eq hn3 hn
    (le_trans hcap' (Nat.pow_le_pow_right (by norm_num) (P4a.nbC_le (.seg v.kind))))
  rw [P4a.stmt4_seg_iff hk3] at hSt
  obtain ⟨hZ, hS⟩ := hSt
  have hS' : P4a.ShHoldsSeg (P4a.nbC (.seg v.kind)) (v.n - 1) (P4a.zNodeC T4.zW (.seg v.kind) L (es.take 3))
      (P4a.sbL (.seg v.kind) (es.take 3)) (P4a.hbL (.seg v.kind) (es.take 3)) := by
    unfold P4a.truthS at hS
    rw [hk3, if_neg (by simp [CKind.isNode]), hL] at hS
    exact hS (by omega)
  have e := P4a.chainEnd_of_truths hk3 (fun b => P4a.witBits_zW _ _ _ b) hn hcap hL hZ hS'
  rw [hA 0 (by norm_num), msgAt_congr hA (by norm_num : 1 < 3), hst, hh] at e
  exact e

/-! ## The node truths -/

/-- **An accepted node run on a good log meets `StmtN4`** on `f⁽⁰⁾` (the per-run input `hRun` of
`nodeLaws4C'`), at the L rows `lRows4` and the M rows `nodeIRows4`. -/
theorem nodeRun_X {DFhi : ℕ → Log → Log → Prop} (hH : FrontHi DFhi) {Vseg : SegProgs}
    {Vnode : NodeProgs} {vk : Digest} (hR : RunFacts4 Vseg Vnode vk) :
    ∀ κ L c π, GoodX DFhi L → kindOf4 π = .node κ → (Vnode κ vk c π).runLog L = some true →
      X.vkOf π = vk ∧ ∃ w c₁ c₂, c = nodeStmt c₁ c₂ ∧
        N4c.StmtN4 κ (lRows4 κ) (nodeIRows4 κ) vk c₁ c₂ w := by
  intro κ L c π hG hk hrun
  obtain ⟨hb, -, -⟩ := T4.muT_lt_one hG.2
  obtain ⟨j, hT, hkC, hvk, hvkL, hc⟩ := hR.node κ L c π hb hk hrun
  obtain ⟨hlen, hSt⟩ := stmt4_of_tail hH hG hT
  set es := entriesOf L (pathOf L j)
  have hA := agree_take3 hlen
  have hk3 : kindOfC (es.take 3) = .node κ := (kindOfC_congr (hA.mono (by norm_num))).trans hkC
  rw [P4a.stmt4_node_iff hk3] at hSt
  have hp : pvL (es.take 3) = (vk, stL es 0, stL es 1) := by
    simp only [pvL, vkL, stL, hA 0 (by norm_num), msgAt_congr hA (by norm_num : 1 < 3)]
    rw [← hvkL]; rfl
  rw [hp] at hSt
  exact ⟨hvk, _, _, _, hc, hSt⟩

end FR.Snd.X4
