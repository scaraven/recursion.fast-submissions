-- New for `flock-recursive` (BLUEPRINT revision 4.1, §5.1–§5.2, A.10; stage X4, item 1): the front
-- of revision 4.1 composed from P4a's phases 0 … 12 and P4b's checks and readers.
import FRSoundness4P4aCtrl5
import FRSoundness4P4bB
import FRSoundness4TailLig
import FRVerifierImplNode4F
import FRNodeRows4Fit

/-!
# The composed front at revision 4.1

* **`src4`**: P4b's front source at revision 4.1 (T4's `Same`, `f⁽⁰⁾ = fF` at the log's kind).
* **`BgA4`**: the background that phases 0 … 12 carry and 13 … 25 reduce: level 0 far, a false
  public cell, a false L row, a false M row (3.x's `far0 ∨ nPub ∨ nLr ∨ nE`), at INT-9's row sources
  `srcL4`/`srcE4` and S-E's public cells `cells4`. **`bgA4_cover`**: a node's rest of the statement
  (`NodeRest4`: L rows, M rows, public cells) fails only under `BgA4` (O1: `lRows4_fit`, `hfit4`).
* **`P4X`** := `front4 zW BgA4`; **`stmt_split4X`**: a false `Stmt4` dooms phase 2.
* **`RejF4b`**: P4b's checks (Lr's and E's end checks, E4's rounds, `finE` (iv), RS0's slices);
  **`RejFX`** := `RejF4a ∨ RejF4b`; **`rejOK_X`**.
* **`DFX DFhi`**: `DF4a P4X k` for `k ≤ 12`, `DFhi k` above (phases 13 … 25 are P4b's).
* **`FrontHi`**: `FrontObl`'s fields at positions `≥ 170` / phases 13 … 25 over the composed
  `DFX`/`RejFX`: the named residual of P4b's unrun item 2. **`frontObl_X`**: `FrontHi` and P4a's
  lemmas give T4's `FrontObl`; **`frontChainStab_X`** likewise.
-/

namespace FR.Snd.X4
open RecursionFast FR.Merkle FR.Rev4 Finset

set_option linter.constructorNameAsVariable false

/-! ## The front source and the public digests -/

/-- **P4b's front source at revision 4.1**: T4's `Same`, `f⁽⁰⁾` at the log's kind. -/
noncomputable def src4 : P4b.FSrc where
  Sm := T4.Same
  agree h := h.1
  mono h hq := h.mono hq
  ofAgree L _ _ _ h := T4.same_of_agree L h
  fz L es := T4.fF (kindOfC es) L es
  fz_same h hp := by
    rw [h.kind (by omega)]
    funext e
    simp only [T4.fF, T4.fTab_same h (i := 0) (by norm_num) _ (by rw [P4a.capPos_zero4]; omega)]

theorem witOf_src4 : P4a.WitOf src4 T4.zW := P4a.witOf_of fun _ _ => rfl

/-- The statement's public digests read off the log: `vk` (entry 0) and `c₁`, `c₂` (entry 1). -/
def pvL (es : Log) : Digest × Digest × Digest := (vkL es, stL es 0, stL es 1)

/-! ## The background `BgA4` -/

/-- **The background of phases 0 … 12**: level 0 far, a false public cell, L row or M row. -/
def BgA4 (L es : Log) : Prop :=
  T4.farL (kindOfC es) L es 0 ∨ ¬ P4b.PubOK4 src4 N4c.cells4 L es ∨
    P4b.RowsBadLr4 src4 NI4F.srcL4 L es ∨ P4b.nE4 src4 NI4F.srcE4 L es

theorem bgA4_reads : T4.Reads 3 BgA4 := fun L es L' es' h1 h2 hS => by
  have hk : kindOfC es = kindOfC es' := hS.kind (by norm_num)
  refine or_congr ?_ (or_congr ((P4b.pubOK4_reads src4 N4c.cells4 L es L' es' h1 h2 hS).not)
    (or_congr ?_ ?_))
  · rw [hk]; exact T4.farL_same hS (i := 0) (by norm_num) _ (by rw [P4a.capPos_zero4]; omega)
  · exact P4b.readsS_onNode (R := src4) (by norm_num)
      (fun κ => P4b.rowsBadG_reads src4 (NI4F.srcL4 κ) (P4b.lrR κ) (P4b.ncR κ)) L es L' es' h1 h2 hS
  · exact P4b.readsS_onNode (R := src4) (by norm_num)
      (fun κ => P4b.rowsBadG_reads src4 (NI4F.srcE4 κ) (P4b.e2R κ) (P4b.ncR κ)) L es L' es' h1 h2 hS

/-- **The L rows fit** `evalL`'s `lrR κ` row and `ncR κ` cell variables (3.x's `RowsFit`). -/
theorem lRows4_fit (ν : NodeKind) : RowsFit (lRows4 ν) (P4b.lrR ν) (P4b.ncR ν) := by
  refine ⟨?_, ?_⟩
  · cases ν <;> simp [lRows4, lBitCells4, List.length_flatMap, P4b.lrR] <;> decide
  · intro r hr t ht
    simp only [lRows4, List.mem_map, List.mem_flatMap, List.mem_range, lBitCells4] at hr
    obtain ⟨b, ⟨σ, hσ, j, hj, rfl⟩, rfl⟩ := hr
    simp [Circ.Lin.cell, Circ.Lin.sub, Circ.Lin.smul] at ht
    have hc : ν.lBase * 128 + ν.vslots * 16384 ≤ 2 ^ P4b.ncR ν ∧ ν.oneCell < 2 ^ P4b.ncR ν := by
      obtain ⟨-, r2, r3, r4⟩ := regions_fit ν
      have l := lSlots_fit ν
      have hm := mSlots_fit ν
      have hv : 1 ≤ ν.vslots := by cases ν <;> decide
      have h7 : 7 ≤ ν.dims.logL := by cases ν <;> decide
      obtain ⟨q, hq⟩ : 2 ^ 7 ∣ ν.nL := pow_dvd_pow 2 h7
      have e : 2 ^ P4b.ncR ν = ν.blocks * 128 := r4
      rw [e, NodeKind.oneCell]
      simp only [slotM4] at hm
      norm_num at l hm hq
      omega
    have h1 : σ * 16384 + 16384 ≤ ν.vslots * 16384 := by nlinarith
    rcases ht with rfl | rfl | ⟨_, rfl⟩ <;> dsimp only <;> omega

/-- **O1 for the node's rest**: a node whose L rows, M rows or public cells fail is in `BgA4`. -/
theorem bgA4_cover {L es : Log} (ν : NodeKind) (hk : kindOfC es = .node ν)
    (h : ¬ P4a.NodeRest4 src4 lRows4 nodeIRows4 pvL ν L es) : BgA4 L es := by
  unfold P4a.NodeRest4 at h
  by_cases hl : ∀ r ∈ lRows4 ν, r.Holds (src4.fz L es)
  · by_cases he : P4b.truthEI (nodeIRows4 ν) (src4.fz L es)
    · refine .inr (.inl fun hp => h ⟨hl, he, ?_⟩)
      exact hp ν hk
    · exact .inr (.inr (.inr ⟨ν, hk, fun hs =>
        he ((P4b.sat_entMatI_iff (nodeIRows4 ν) (hfit4 ν) (src4.fz L es)).mp hs)⟩))
  · exact .inr (.inr (.inl ⟨ν, hk, fun hs =>
      hl ((P4b.sat_ofRows_iff (lRows4 ν) (lRows4_fit ν) (src4.fz L es)).mp hs)⟩))

/-! ## The front's parameters and the statement split -/

/-- **The front's parameters** at T4's witness and `BgA4`. -/
noncomputable def P4X : P4a.Front4a := P4a.front4 T4.zW BgA4

theorem P4X_ok : P4X.OK := P4a.front4_ok P4a.witBits_zW P4a.zwSame_zW bgA4_reads

/-- **A false statement dooms phase 2** (`stmt_split4` with the cover). -/
theorem stmt_split4X {L es : Log} (h : ¬ P4a.Stmt4 src4 T4.zW lRows4 nodeIRows4 pvL L es) :
    P4a.DF4a P4X 2 L es :=
  P4a.stmt_split4 witOf_src4 P4a.witBits_zW (fun ν hk hr => bgA4_cover ν hk hr) h

/-! ## The checks `RejFX` -/

/-- RS0's bindings: Z's `oZ`, Lc's `oLc4`, Sh's `oSh4 wNS4`, E's `okE4` (what R4 refutes). -/
def okX : CKind → Log → ℕ → F → Prop := P4b.okRS4 P4a.oZ P4a.oLc4 (P4a.oSh4 P4a.wNS4)

theorem rbL_congrX {es es' : Log} (h : Agree es es' 326) (κ : CKind) :
    P4a.rbL κ es = P4a.rbL κ es' ∧ P4a.rpL κ es = P4a.rpL κ es' := by
  have := P4a.nbC_le κ
  exact ⟨List.map_congr_left fun l hl => rch_congr h (by simp at hl; omega),
    List.map_congr_left fun l hl => rch_congr h (by simp at hl; omega)⟩

theorem okReads_X : P4b.OkReads4 okX := by
  refine P4b.okRS4_reads (fun κ es es' h => ?_) (fun κ es es' h => ?_) (fun κ es es' h => ?_)
  · funext v; simp only [P4a.oZ, pzStar_agree (h.mono (by norm_num))]
  · funext v; simp only [P4a.oLc4, (P4a.vBetaL_agree4 (h.mono (by norm_num))).1]
  · have hk : kindOfC es = kindOfC es' := kindOfC_congr (h.mono (by norm_num))
    have hc : P4a.claimSL4 κ es = P4a.claimSL4 κ es' := by
      have := P4a.nrS_le4 κ
      exact clR2_same (P4a.c0S_agree4 h (by norm_num)) (h.mono (by omega))
    obtain ⟨hb, hp⟩ := rbL_congrX h κ
    have hw : P4a.wSumL4 P4a.wNS4 κ es = P4a.wSumL4 P4a.wNS4 κ es' := by
      obtain ⟨h1, h2, h3⟩ := P4a.s1_congr4 h (by norm_num) κ
      unfold P4a.wSumL4
      split_ifs
      · simp only [P4a.wNS4, hb, hp, P4a.wNLocal4 κ es es' (h.mono (by norm_num))]
      · simp only [P4a.wSumSeg, P4a.tauLL, hb, hp, h1, h2, h3, P4a.lastBits,
          P4a.nStmt_congr h (by norm_num)]
    funext v; simp only [P4a.oSh4, hc, hw]

/-- **P4b's checks** (phases 13 … 25): Lr's and E's end checks, E4's rounds, `finE` (iv) at INT-9's
row sources, RS0's slices against `okX`. -/
def RejF4b (L es : Log) : Prop :=
  P4b.RejEndLr4 L es ∨ P4b.RejEndE4 L es ∨ P4b.RejInE4 L es ∨
    P4b.RejFinE4 NI4F.srcE4 NI4F.srcL4 L es ∨ P4b.RejRS4 okX L es

/-- **The front's checks**: P4a's and P4b's. -/
def RejFX (L es : Log) : Prop := P4a.RejF4a P4X.M L es ∨ RejF4b L es

/-- A log-only check is a `T4.RejOK`. -/
theorem rejOK_of_log4 {Rej : Log → Log → Prop} (h : P4b.RejLog4 Rej) : T4.RejOK Rej where
  mono := h.mono
  sq := h.sq
  stab _ _ _ _ X _ := h.log _ _ X

theorem rejF4b_log : P4b.RejLog4 RejF4b where
  mono L es x h := h.imp (P4b.rejEndLr4_log.mono L es x) (Or.imp (P4b.rejEndE4_log.mono L es x)
    (Or.imp (P4b.rejInE4_log.mono L es x) (Or.imp ((P4b.rejFinE4_log _ _).mono L es x)
      ((P4b.rejRS4_log okReads_X).mono L es x))))
  sq L es x hs := or_congr (P4b.rejEndLr4_log.sq L es x hs) (or_congr (P4b.rejEndE4_log.sq L es x hs)
    (or_congr (P4b.rejInE4_log.sq L es x hs) (or_congr ((P4b.rejFinE4_log _ _).sq L es x hs)
      ((P4b.rejRS4_log okReads_X).sq L es x hs))))
  log L L' es := or_congr (P4b.rejEndLr4_log.log L L' es) (or_congr (P4b.rejEndE4_log.log L L' es)
    (or_congr (P4b.rejInE4_log.log L L' es) (or_congr ((P4b.rejFinE4_log _ _).log L L' es)
      ((P4b.rejRS4_log okReads_X).log L L' es))))

theorem rejOK_X : T4.RejOK RejFX := T4.rejOK_or (P4a.rejF4a_ok P4X_ok.et) (rejOK_of_log4 rejF4b_log)

/-- The front's checks read the same off two logs that agree on `X` (`FrontChainStab`'s part). -/
theorem ss_rejFX : P4a.SameStab4 0 RejFX := fun L L' X _ hS => by
  have hZ : P4a.RejZ P4X.M L X ↔ P4a.RejZ P4X.M L' X := by
    by_cases hx : 68 ≤ X.length
    · exact and_congr Iff.rfl (P4a.rejZ_reads4 P4X_ok.et L X L' X hx hx (hS.mono hx))
    · exact ⟨fun h => absurd h.1 hx, fun h => absurd h.1 hx⟩
  have hLc : ∀ b, (98 ≤ X.length ∧ P4a.PLc P4X.M b L X) ↔ (98 ≤ X.length ∧ P4a.PLc P4X.M b L' X) :=
    fun b => by
    by_cases hx : 98 ≤ X.length
    · exact and_congr Iff.rfl (P4a.pLc_reads4 b L X L' X hx hx (hS.mono hx))
    · exact ⟨fun h => absurd h.1 hx, fun h => absurd h.1 hx⟩
  have hL2 : RejL2 L X ↔ RejL2 L' X := by simp only [RejL2, Chk2, clR2L_log L L' X]
  have hS2 : P4a.RejS2 L X ↔ P4a.RejS2 L' X := by
    unfold P4a.RejS2 Chk2
    exact exists_congr fun l => and_congr_right fun _ => and_congr_right fun _ => not_congr (by
      cases l <;> exact Iff.rfl)
  exact or_congr (or_congr hZ (or_congr hL2 (or_congr (hLc false) (or_congr (hLc true) hS2))))
    (rejF4b_log.log L L' X)

/-! ## The composed dooms and the residual of phases 13 … 25 -/

/-- **The front's phase dooms**: P4a's for phases `≤ 12`, `DFhi` (P4b's, to be defined) above. -/
noncomputable def DFX (DFhi : ℕ → Log → Log → Prop) (k : ℕ) : Log → Log → Prop :=
  if k ≤ 12 then P4a.DF4a P4X k else DFhi k

/-- **The cells B′ batches** (revision 4.4.2, RSV2 §2.2): a node kind's nine public cells, then its
60 reserve cells (`Rev4.rsvCells`, none on `N8`), at `κ′² … κ′^{70}` (`finPf`'s two cell chains). -/
def cellsX (ν : NodeKind) : List ℕ := N4c.cells4 ν ++ Rev4.rsvCells ν

/-- The level-0 weight and claim the front hands the tail (P4b's readers at S-E's maps). -/
noncomputable def W0X : Log → Log → ℕ → K := P4b.W₀L4 N4c.kf4 cellsX

/-- The front's claim `c₀ = ι v*`. -/
noncomputable def c0X : Log → Log → K := P4b.c₀L4

open Classical in
/-- **The residual of phases 13 … 25** (P4b's handover item 2, not yet run): `FrontObl`'s fields at
positions `≥ 170` and phases `13 … 25`, over the composed dooms and checks (so the boundary at 170,
where Lr1's `msD` reads `DF4a P4X 12`, is here), and `FrontChainStab`'s part at those phases. -/
structure FrontHi (DFhi : ℕ → Log → Log → Prop) : Prop where
  ms : ∀ s0 r, (s0, r) ∈ fsRanges4 → 170 ≤ s0 + 1 → s0 + 1 < T4.p1Start 0 →
    ∃ fin, DFX DFhi (phOf4 (s0 + 1)) = msD (DFX DFhi (phOf4 s0)) fin s0 r
  habs : ∀ L es x len, G.Matches (es ++ [x]) → fsItems4[es.length]? = some (.absorb len) →
    170 ≤ es.length → es.length < T4.p1Start 0 → ¬ T4.RejC RejFX c0X L es →
      DFX DFhi (phOf4 (es.length - 1)) L es →
        T4.RejC RejFX c0X L (es ++ [x]) ∨ DFX DFhi (phOf4 es.length) L (es ++ [x])
  handoff : ∀ L es x len, G.Matches (es ++ [x]) → fsItems4[es.length]? = some (.absorb len) →
    es.length = T4.p1Start 0 → ¬ T4.RejC RejFX c0X L es → DFX DFhi 25 L es →
      T4.RejC RejFX c0X L (es ++ [x]) ∨ T4.D1 W0X c0X 0 L (es ++ [x])
  hsingle : ∀ L es, G.Matches es → fsItems4[es.length]? = some .squeeze → fsRnd4 es.length = none →
    170 ≤ es.length → es.length < T4.p1Start 0 → ¬ T4.RejC RejFX c0X L es →
      (univ.filter fun a => DFX DFhi (phOf4 (es.length - 1)) L es ∧
        ¬ DFX DFhi (phOf4 es.length) L (ext1 es a)).card ≤ 239 * 2 ^ 128
  hfin : ∀ s0 r, (s0, r) ∈ fsRanges4 → 170 ≤ s0 + 1 → s0 + 1 < T4.p1Start 0 → ∀ L es₀,
    G.Matches es₀ → es₀.length = s0 + 1 → ¬ T4.RejC RejFX c0X L es₀ →
      condCount (DPos (T4.Dp (DFX DFhi))) L es₀ r [] ≤ deltaR
  hstab : ∀ k, 12 < k → k < 26 → ∀ L i, ¬ Bad L → G.IsChain L i → ∀ X,
    StabExt fsRnd4 (entriesOf L (pathOf L i)) X → phOf4 (X.length - 1) = k →
      (DFhi k (L.take i) X ↔ DFhi k L X)
  chain : ∀ L j, ¬ Bad L → G.IsChain L j → ∀ k, 12 < k → k < 26 →
    phOf4 ((entriesOf L (pathOf L j)).length - 1) = k →
      (DFhi k (L.take j) (entriesOf L (pathOf L j)) ↔ DFhi k L (entriesOf L (pathOf L j)))

/-! ## The composition -/

theorem phStart4_13 : phStart4 13 = 170 := by simp only [phStart4, fsStarts4_eq]; rfl

theorem p1Start_zero4 : T4.p1Start 0 = 332 := by simp only [T4.p1Start, phStart4, fsStarts4_eq]; rfl

/-- Below 170 the phase is at most 12. -/
theorem phOf4_le12 {p : ℕ} (hp : p < 170) : phOf4 p ≤ 12 := by
  obtain ⟨b1, b2, -⟩ := T4.phOf_bounds p
  by_contra h
  have := P4a.phStart4_mono (show 13 ≤ phOf4 p by omega) b2
  rw [phStart4_13] at this; omega

theorem DFX_lo {DFhi : ℕ → Log → Log → Prop} {k : ℕ} (hk : k ≤ 12) : DFX DFhi k = P4a.DF4a P4X k := by
  rw [DFX, if_pos hk]

theorem DFX_hi {DFhi : ℕ → Log → Log → Prop} {k : ℕ} (hk : 12 < k) : DFX DFhi k = DFhi k := by
  rw [DFX, if_neg (by omega)]

/-- **T4's `FrontObl` at revision 4.1**: P4a's lemmas below 170, `FrontHi` above. -/
theorem frontObl_X {DFhi : ℕ → Log → Log → Prop} (hH : FrontHi DFhi) :
    T4.FrontObl RejFX (DFX DFhi) W0X c0X where
  loc L es L' es' p hS hp :=
    P4b.frontLocal4 N4c.kf4 cellsX L L' (hS.1.mono (by rw [← p1Start_zero4]; exact hp))
  rej := rejOK_X
  ms s0 r hm hp := by
    by_cases hlo : s0 + 1 < 170
    · rw [DFX_lo (phOf4_le12 hlo), DFX_lo (phOf4_le12 (by omega))]
      exact P4a.ms4a P4X s0 r hm hlo
    · exact hH.ms s0 r hm (by omega) hp
  habs L es x len hM hit hp hr hd := by
    by_cases hlo : es.length < 170
    · rw [DFX_lo (phOf4_le12 (by omega))] at hd
      rw [DFX_lo (phOf4_le12 hlo)]
      rcases P4a.habs4a P4X_ok (P4a.sNode4 P4a.zwSame_zW) L es x len hit hlo hd with h | h
      · exact .inl (.inl (.inl h))
      · exact .inr h
    · exact hH.habs L es x len hM hit (by omega) hp hr hd
  handoff := hH.handoff
  hsingle L es hM hit hrnd hp hr := by
    by_cases hlo : es.length < 170
    · rw [DFX_lo (phOf4_le12 (by omega)), DFX_lo (phOf4_le12 hlo)]
      exact P4a.hsingle4a P4X_ok (P4a.sNode4 P4a.zwSame_zW) L es hit hrnd hlo
        fun h => hr (.inl (.inl h))
    · exact hH.hsingle L es hM hit hrnd (by omega) hp hr
  hfin s0 r hm hp L es₀ hM hl hr := by
    by_cases hlo : s0 + 1 < 170
    · obtain ⟨p2, p3, p98, p99⟩ := P4a.ph_vals4a
      have hP := P4X_ok
      have hN := P4a.sNode4 (zw := T4.zW) P4a.zwSame_zW
      rcases P4a.fsRanges4_front hm hlo with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · exact P4a.z1_hfin4 hP.bits hP.wbits hP.same hP.et (Bg := P4a.bgZ4 P4X) (P4a.rd_bgZ4 hP hN)
          (fun L es h => by rw [p2, DFX_lo (by norm_num)] at h; exact h)
          (by rw [p3, p2, DFX_lo (by norm_num), DFX_lo (by norm_num)]; rfl) (fun _ _ h => h) L es₀ hl
      · exact P4a.s1_hfin4 hN hP.same (Bg := P4a.bg10_4 P4X) (P4a.rd_bg10_4 hP)
          (by rw [p98, DFX_lo (by norm_num)]; rfl)
          (by rw [p99, p98, DFX_lo (by norm_num), DFX_lo (by norm_num)]; rfl) L es₀ hl
    · exact hH.hfin s0 r hm (by omega) hp L es₀ hM hl hr
  hstab k hk L i hb hci X hX hph := by
    by_cases hlo : k ≤ 12
    · rw [DFX_lo hlo]
      exact P4a.hstab4a P4X_ok (P4a.sNode4 P4a.zwSame_zW) k hlo L i hb hci X hX hph
    · rw [DFX_hi (by omega)]
      exact hH.hstab k (by omega) hk L i hb hci X hX hph

/-- **`FrontChainStab` at revision 4.1**: P4a's dooms by `df_ss4a`, the checks by `ss_rejFX`,
phases 13 … 25 by `FrontHi.chain`. -/
theorem frontChainStab_X {DFhi : ℕ → Log → Log → Prop} (hH : FrontHi DFhi) :
    T4.FrontChainStab RejFX (DFX DFhi) := by
  intro L j hb hci
  have hS := T4.same_chain hb hci
  refine ⟨ss_rejFX _ _ _ (Nat.zero_le _) hS, fun k hk hph => ?_⟩
  by_cases hlo : k ≤ 12
  · rw [DFX_lo hlo]
    have h1 : 1 ≤ (entriesOf L (pathOf L j)).length :=
      List.length_pos_iff.mpr (G.matches_ne_nil hci.2)
    obtain ⟨b1, -, -⟩ := T4.phOf_bounds ((entriesOf L (pathOf L j)).length - 1)
    rw [hph] at b1
    exact P4a.df_ss4a P4X_ok (P4a.sNode4 P4a.zwSame_zW) k hlo _ _ _ (by omega) hS
  · rw [DFX_hi (by omega)]
    exact hH.chain L j hb hci k (by omega) hk hph

end FR.Snd.X4
