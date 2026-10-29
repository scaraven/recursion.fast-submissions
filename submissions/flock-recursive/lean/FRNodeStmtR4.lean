-- New for `flock-recursive` (revision 4.4.2, the reserve in RSV2's stacked form, §2.4; track RSV-S2b):
-- the node statement with the reserve's child claim (`StmtN4R`), its per-run input from the front
-- (`nodeRunR_X`), and the value form of slot 0's `evalM` discharge (`evalM_childV`).
import FRSoundness4P4fObl
import FRSoundness4RsvCtrl

/-!
# The node statement with the reserve's child claim

A node `P` with a previous node `C` replays `V(C)` in slot 0; `V(C)`'s one stacked `evalM` call has
three output registers, imports of `P`'s circuit (RSV2 §2.4). They are bound by three facts about
`P`'s own log, all of which an accepted run of `V(P)` on a good log gives:

* **`PubCellsR4`**: `f⁽⁰⁾` at `Rev4.rsvCells` is `P`'s child claim `ch = p_x ‖ p_y ‖ s ‖ X₃` (60
  values of Lrend's message; RS0's `Pub`, `PubRX`, refuted on the accepted prefix);
* **`truthChild4`**: `X = Σ_i s_i·M̃_i(p)` (E1's entry doom `D16X` refuted on the prefix);
* **`RsvZero`**: `X₃[1] = X₃[2] = 0` (`V(P)`'s two zero asserts, `RunFacts4.node`).

* **`truthChildV`**, **`StmtN4R`**: the two last facts on the value list `ch`, and `StmtN4 ∧
  PubCellsR4 ∧ truthChildV` (`StmtN4`'s signature is kept; `ch` is a binder). On `N8` the list is
  empty and both hold trivially (`truthChildV_nil`).
* **`nodeRunR_X`**: `nodeRun_X` with the reserve: an accepted node run on a good log meets
  `StmtN4R` at its own child claim.
* **`evalM_childV`**: the value form of the discharge: on a 32-entry row point and a column point
  whose entries are `ch`'s `p_x ‖ s` and `p_y`, the node's `evalM` returns `ch`'s `X₃` (`implN4F_hMX`).
-/

namespace FR.N4c
open RecursionFast Rev4 Circ Finset

/-! ## The child claim on its values -/

/-- The stacked extension at the claim's own values (`p_x = ch[0, 23)`, `p_y = ch[23, 48)`,
`s = ch[48, 57)`). -/
noncomputable def mStackV (srcE : NodeKind → Snd.P4b.ESrc) (ch : List F) : F :=
  Snd.P4b.mStack srcE (fun i => ch.getD (48 + i) 0) (fun j => ch.getD j 0) (fun j => ch.getD (23 + j) 0)

/-- **The child claim is true on its values**: `X = Σ_i s_i·M̃_i(p)` and `X₃[1] = X₃[2] = 0`. -/
def truthChildV (srcE : NodeKind → Snd.P4b.ESrc) (ch : List F) : Prop :=
  ch.getD 57 0 = mStackV srcE ch ∧ ch.getD 58 0 = 0 ∧ ch.getD 59 0 = 0

/-- **`StmtN4` with the reserve** (RSV2 §2.4): the node's truths, its reserve cells holding the child
claim `ch`, and the claim true (INT-9's M-row sources `srcE4`). -/
def StmtN4R (κ : NodeKind) (lr : List Circ.Row) (er : List (ℕ × Circ.Row)) (vk c₁ c₂ : Digest) (w : Asg)
    (ch : List F) : Prop :=
  StmtN4 κ lr er vk c₁ c₂ w ∧ PubCellsR4 κ w ch ∧ truthChildV NI4F.srcE4 ch

/-- (+) The empty claim (`N8`: no reserve cells) is true. -/
theorem truthChildV_nil (srcE : NodeKind → Snd.P4b.ESrc) : truthChildV srcE [] := by
  refine ⟨?_, rfl, rfl⟩
  simp only [mStackV, List.getD_nil, Snd.P4b.mStack, NodeKind.all, List.map_cons, List.map_nil,
    List.sum_cons, List.sum_nil, zero_mul, add_zero]

/-- `mStack` reads `s` below 9, `p` below 23 and `q` below 25. -/
theorem mStack_congr (srcE : NodeKind → Snd.P4b.ESrc) {s s' p p' q q' : ℕ → F}
    (hs : ∀ i < 9, s i = s' i) (hp : ∀ j < 23, p j = p' j) (hq : ∀ j < 25, q j = q' j) :
    Snd.P4b.mStack srcE s p q = Snd.P4b.mStack srcE s' p' q' := by
  have hlp : ∀ κ : NodeKind, Snd.Rsv.lowA (Snd.P4b.e2R κ) p = Snd.Rsv.lowA (Snd.P4b.e2R κ) p' :=
    fun κ => funext fun j => hp j (lt_of_lt_of_le j.isLt (Snd.P4b.dims_le' κ).2.1)
  have hlq : ∀ κ : NodeKind, Snd.Rsv.lowA (Snd.P4b.ncR κ) q = Snd.Rsv.lowA (Snd.P4b.ncR κ) q' :=
    fun κ => funext fun j => hq j (lt_of_lt_of_le j.isLt (Snd.P4b.dims_le' κ).2.2.1)
  simp only [Snd.P4b.mStack, NodeKind.all, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    hlp, hlq, NodeKind.ix]
  rw [hs 0 (by norm_num), hs 1 (by norm_num), hs 2 (by norm_num), hs 3 (by norm_num), hs 4 (by norm_num),
    hs 5 (by norm_num), hs 6 (by norm_num), hs 7 (by norm_num), hs 8 (by norm_num)]

/-- **The log's claim on its values**: a true `truthChild4` and the two zero outputs give
`truthChildV` of the reserve's values (`rsvL`; on `N8` the empty list). -/
theorem truthChildV_rsvL (srcE : NodeKind → Snd.P4b.ESrc) (κ : NodeKind) {es : Log}
    (ht : Snd.P4b.truthChild4 srcE es) (h58 : Snd.P4b.rsvV es 58 = 0) (h59 : Snd.P4b.rsvV es 59 = 0) :
    truthChildV srcE (Snd.P4b.rsvL (.node κ) es) := by
  cases hp : κ.hasPrev
  · have : Snd.P4b.rsvL (.node κ) es = [] := by simp [Snd.P4b.rsvL, Snd.P4b.nRsv, hp]
    rw [this]; exact truthChildV_nil srcE
  · have hg : ∀ i < 60, (Snd.P4b.rsvL (.node κ) es).getD i 0 = Snd.P4b.rsvV es i := fun i hi => by
      rw [List.getD_eq_getElem _ _ (by simp [Snd.P4b.rsvL, Snd.P4b.nRsv, hp, hi])]
      simp [Snd.P4b.rsvL]
    obtain ⟨hx, hy, hs, hX⟩ := Snd.P4b.child_rsvV es
    refine ⟨?_, by rw [hg 58 (by norm_num), h58], by rw [hg 59 (by norm_num), h59]⟩
    rw [hg 57 (by norm_num), ← hX, ht, mStackV]
    exact mStack_congr srcE (fun i hi => by rw [hs, hg _ (by omega)])
      (fun j hj => by rw [hx, hg _ (by omega)]) (fun j hj => by rw [hy, hg _ (by omega)])

/-! ## Slot 0's `evalM`, in values -/

/-- **The value form of slot 0's `evalM` discharge** (RSV2 §2.4, step 3): if the stacked call's row
point (32 entries) holds `ch`'s `p_x ‖ s` and its column point `ch`'s `p_y`, the node's `evalM` returns
`ch`'s `X₃` whenever the claim is true (`implN4F_hMX`, and `mStack`'s reads). -/
theorem evalM_childV (base : NodeKind → OpImpl) (ν : NodeKind) {ch : List F}
    (hT : truthChildV NI4F.srcE4 ch) {τ σ : Array F} (hτ : τ.size = 32)
    (hx : ∀ j < 23, τ.getD j 0 = ch.getD j 0) (hs : ∀ i < 9, τ.getD (23 + i) 0 = ch.getD (48 + i) 0)
    (hy : ∀ j < 25, σ.getD j 0 = ch.getD (23 + j) 0) :
    (NI4F.implN4F base ν).evalM τ σ = (ch.getD 57 0, ch.getD 58 0, ch.getD 59 0) := by
  have hpt : ∀ n (r : Array F), FR.Impl.ptA n r = Snd.Rsv.lowA n (fun j => r.getD j 0) := fun _ _ => rfl
  have key : (NodeKind.all.map fun κ => NI4F.dot3 (NI4F.sOf τ κ.ix)
      (Eval.matMLE (NI4F.srcE4 κ).ea (FR.Impl.ptA (Snd.P4b.e2R κ) τ) (FR.Impl.ptA (Snd.P4b.ncR κ) σ),
       Eval.matMLE (NI4F.srcE4 κ).eb (FR.Impl.ptA (Snd.P4b.e2R κ) τ) (FR.Impl.ptA (Snd.P4b.ncR κ) σ),
       Eval.matMLE (NI4F.srcE4 κ).ec (FR.Impl.ptA (Snd.P4b.e2R κ) τ) (FR.Impl.ptA (Snd.P4b.ncR κ) σ))).sum =
      ch.getD 57 0 := by
    rw [hT.1, mStackV, ← mStack_congr NI4F.srcE4 (s := fun i => τ.getD (23 + i) 0)
      (p := fun j => τ.getD j 0) (q := fun j => σ.getD j 0) hs hx hy]
    simp only [Snd.P4b.mStack, NodeKind.all, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
      NI4F.dot3, NI4F.sOf, NodeKind.ix, hpt]
  rw [NI4F.implN4F_hMX base ν τ σ hτ, key, hT.2.1, hT.2.2]

end FR.N4c

namespace FR.Snd.X4
open RecursionFast FR.Merkle FR.Rev4 Finset

/-! ## The per-run input with the reserve -/

theorem agree_takeN {es : Log} {n : ℕ} (h : n ≤ es.length) : Agree (es.take n) es n := by
  have e := agree_append (es.take n) (es.drop n) (n := n) (by simp; omega)
  rw [List.take_append_drop] at e
  exact fun p hp => (e p hp).symm

/-- The phase of positions 214 (Lr3's squeeze: E1's entry, `D16X`) and 326 (RS0's absorb, `DRS0X`). -/
theorem phOf4_214_326 : phOf4 214 = 16 ∧ phOf4 326 = 23 := by
  obtain ⟨-, -, -, -, h16, h17, -, -, -, -, -, h23, h24, -, -⟩ := P4f.phStart_hi
  exact ⟨P4a.phOf4_eq (by norm_num) (by rw [h16]) (by rw [h17]; norm_num),
    P4a.phOf4_eq (by norm_num) (by rw [h23]) (by rw [h24]; norm_num)⟩

/-- **An accepted chain's prefixes are not doomed at phases 16 and 23** (`tail_of_accept`): the child
claim is true after Lrend, and RS0's `Pub` (the nine public cells and the reserve's) holds. -/
theorem rsv_of_tail {L : Log} {j : ℕ} (hG : GoodX P4f.DFhi L) (hT : T4.AcceptTail RejFX W0X c0X L j)
    {κ : NodeKind} (hk : kindOfC (entriesOf L (pathOf L j)) = .node κ) :
    Snd.P4b.truthChild4 NI4F.srcE4 (entriesOf L (pathOf L j)) ∧
      Snd.P4b.PubOKR4 src4 Rev4.rsvCells L ((entriesOf L (pathOf L j)).take 327) := by
  have hlen : 327 ≤ (entriesOf L (pathOf L j)).length := by
    have := hT.len; rw [T4.capPh_pos.2.2.2] at this; omega
  obtain ⟨hnd, -⟩ := T4.tail_of_accept (frontObl_X P4f.frontHi_X).loc
    (frontChainStab_X P4f.frontHi_X) hG.2 hT
  generalize entriesOf L (pathOf L j) = es at hlen hnd hk ⊢
  obtain ⟨p214, p326⟩ := phOf4_214_326
  have hA : ∀ n, n ≤ es.length → Agree (es.take n) es n := fun n hn => agree_takeN hn
  have hkn : ∀ n, 3 ≤ n → n ≤ es.length → kindOfC (es.take n) = .node κ := fun n h3 hn =>
    (kindOfC_congr ((hA n hn).mono (by omega))).trans hk
  refine ⟨?_, ?_⟩
  · by_contra hc
    apply hnd 214 (by omega)
    refine .inr ?_
    have hl : (es.take (214 + 1)).length - 1 = 214 := by rw [List.length_take]; omega
    unfold DPos T4.Dp
    rw [hl, p214, T4.DkC, if_pos (by norm_num), DFX_hi (by norm_num)]
    refine .inr (.inr ⟨κ, hkn 215 (by norm_num) (by omega), by simp; omega, fun ht => hc ?_⟩)
    obtain ⟨h1, h2, h3, h4⟩ := Snd.P4b.child_agree (hA 215 (by omega)) (by norm_num)
    simpa only [Snd.P4b.truthChild4, h1, h2, h3, h4] using ht
  · by_contra hc
    apply hnd 326 (by omega)
    refine .inr ?_
    have hl : (es.take (326 + 1)).length - 1 = 326 := by rw [List.length_take]; omega
    unfold DPos T4.Dp
    rw [hl, p326, T4.DkC, if_pos (by norm_num), DFX_hi (by norm_num)]
    exact .inr (.inl fun h => hc h.2)

/-- **`nodeRun_X` with the reserve**: an accepted node run on a good log meets `StmtN4R` on `f⁽⁰⁾`,
at the log's child claim `ch = rsvL` (empty on `N8`). -/
theorem nodeRunR_X {Vseg : SegProgs} {Vnode : NodeProgs} {vk : Digest} (hR : RunFacts4 Vseg Vnode vk) :
    ∀ κ L c π, GoodX P4f.DFhi L → kindOf4 π = .node κ → (Vnode κ vk c π).runLog L = some true →
      X.vkOf π = vk ∧ ∃ (w : Circ.Asg) (c₁ c₂ : Digest) (ch : List F), c = nodeStmt c₁ c₂ ∧
        N4c.StmtN4R κ (lRows4 κ) (nodeIRows4 κ) vk c₁ c₂ w ch := by
  intro κ L c π hG hk hrun
  obtain ⟨hb, -, -⟩ := T4.muT_lt_one hG.2
  obtain ⟨j, hT, ⟨hkC, hvk, hvkL, hc⟩, hZ⟩ := hR.node κ L c π hb hk hrun
  obtain ⟨hlen3, hSt⟩ := stmt4_of_tail P4f.frontHi_X hG hT
  have hlen : 327 ≤ (entriesOf L (pathOf L j)).length := by
    have := hT.len; rw [T4.capPh_pos.2.2.2] at this; omega
  obtain ⟨htc, hpub⟩ := rsv_of_tail hG hT hkC
  generalize entriesOf L (pathOf L j) = es at hlen hlen3 hSt htc hpub hkC hvkL hc hZ ⊢
  have hA := agree_take3 hlen3
  have hA' := agree_takeN (es := es) hlen
  have hk3 : kindOfC (es.take 3) = .node κ := (kindOfC_congr (hA.mono (by norm_num))).trans hkC
  rw [P4a.stmt4_node_iff hk3] at hSt
  have hp : pvL (es.take 3) = (vk, stL es 0, stL es 1) := by
    simp only [pvL, vkL, stL, hA 0 (by norm_num), msgAt_congr hA (by norm_num : 1 < 3)]
    rw [← hvkL]; rfl
  rw [hp] at hSt
  have h33 : Agree (es.take 3) (es.take 327) 3 := fun p hp => (hA p hp).trans (hA' p (by omega)).symm
  have hfz : src4.fz L (es.take 3) = src4.fz L (es.take 327) := src4.fz_same (src4.ofAgree L h33) le_rfl
  have hk327 : kindOfC (es.take 327) = .node κ := (kindOfC_congr (hA'.mono (by norm_num))).trans hkC
  refine ⟨hvk, _, _, _, Snd.P4b.rsvL (.node κ) es, hc, hSt, ?_,
    N4c.truthChildV_rsvL _ κ htc hZ.1 hZ.2⟩
  unfold N4c.PubCellsR4
  rw [hfz, hpub κ hk327, Snd.P4b.rsvL_congr hA' (by norm_num)]

/-! ## The node law and `KS` with the reserve -/

section KSR
open FR.X.X4

/-- **The node laws from `StmtN4R`** (`nodeLaws4C'` at `St := ∃ ch, StmtN4R`): the residual `hRes` may
use the reserve's cells and the true child claim (`gap4Imp_of_rsv`'s inputs). -/
theorem nodeSoundR_X (impl₀ : OpImpl) (implN : NodeKind → OpImpl) (S : Submission) (vk : Digest)
    (hV : S.V = VC4 impl₀ implN N4c.cells4) (hq : S.qV = qV4)
    (hRun : RunFacts4 (VsegC impl₀) (VnodeC implN N4c.cells4) vk)
    (I : N4c.SlotIface4 (VsegC impl₀) (VnodeC implN N4c.cells4)) (rd : N4c.Read4)
    (hI : I.lrows = lRows4 ∧ I.irows = nodeIRows4)
    (hRes : ∀ κ w c₁ c₂ ch, N4c.StmtN4R κ (lRows4 κ) (nodeIRows4 κ) vk c₁ c₂ w ch →
      N4c.NodeResid4 I rd κ vk c₁ c₂ w) :
    NodeSoundLog (VnodeC implN N4c.cells4) vk (GoodX P4f.DFhi) (Rel (S.acc vk)) := by
  obtain ⟨hl, hi⟩ := hI
  refine (N4c.nodeLaws4C' impl₀ implN N4c.cells4 S vk hV hq I rd
    (St := fun κ w c₁ c₂ => ∃ ch, N4c.StmtN4R κ (lRows4 κ) (nodeIRows4 κ) vk c₁ c₂ w ch)
    (fun κ w c₁ c₂ ⟨_, h⟩ => by rw [hl, hi]; exact h.1) ?_ fun κ w c₁ c₂ ⟨ch, h⟩ => hRes κ w c₁ c₂ ch h).1
  intro κ L c π hG hk h
  obtain ⟨hvk, w, c₁, c₂, ch, hc, hS⟩ := nodeRunR_X hRun κ L c π hG hk h
  exact ⟨hvk, w, c₁, c₂, hc, ch, hS⟩

/-- **`KS` with the reserve** (`ks_rev4` at the concrete front `P4f.DFhi`, `frontHi_X`): the residual
`hRes` is over `StmtN4R`, which carries the reserve's cells and the true child claim. -/
theorem ks_rev4R (impl₀ : OpImpl) (base : NodeKind → OpImpl) (S : Submission) (vk : Digest)
    (hV : S.V = VC4 impl₀ (NI4F.implN4F base) N4c.cells4) (hq : S.qV = qV4)
    {nd : X.XIR} (hE : S.E = E4X nd S.acc) (hε : S.ε = epsR)
    (hRun : RunFacts4 (VsegC impl₀) (VnodeC (NI4F.implN4F base) N4c.cells4) vk)
    (I : N4c.SlotIface4 (VsegC impl₀) (VnodeC (NI4F.implN4F base) N4c.cells4)) (rd : N4c.Read4)
    (hI : I.lrows = lRows4 ∧ I.irows = nodeIRows4)
    (hRes : ∀ κ w c₁ c₂ ch, N4c.StmtN4R κ (lRows4 κ) (nodeIRows4 κ) vk c₁ c₂ w ch →
      N4c.NodeResid4 I rd κ vk c₁ c₂ w)
    (D : NodeDec4 nd)
    (hL : ∀ κ L c π, GoodX P4f.DFhi L → kindOf4 π = .node κ → X.InDomE c π L →
      (VnodeC (NI4F.implN4F base) N4c.cells4 κ vk c π).runLog L = some true →
      ∃ es, D.Links κ L es π c ∧ Rel (S.acc vk) c (D.readW κ L es)) :
    KS (Rel (S.acc vk)) (S.V vk) S.E S.ε S.qV := by
  have hF := T4.muT_laws_of_front (frontObl_X P4f.frontHi_X)
  rw [hε]
  exact ks4_E4X impl₀ (NI4F.implN4F base) N4c.cells4 S vk hV hq D hE _ hF.1 hF.2
    (segSound_X P4f.frontHi_X hRun) (nodeSoundR_X impl₀ _ S vk hV hq hRun I rd hI hRes) hL

end KSR

end FR.Snd.X4
