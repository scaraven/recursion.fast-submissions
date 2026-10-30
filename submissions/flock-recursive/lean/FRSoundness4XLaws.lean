-- G6: this module also holds the former modules `FRSoundness4P4aCtrl4`, `FRSoundness4P4aSplit`, `FRSoundness4XFront`, `FRSoundness4P4fDF` (one section each, in import order).
import FRSoundness4P4aNS
import FRSoundness4R4W0
import FRSoundness4TailLig
import FRVerifierImplNode4F
import FRNodeRows4Fit
import FRNodeCircuit4Dig

section G6_FRSoundness4P4aCtrl4

-- New for `flock-recursive` (stage P4a pass 4 (P4d)): controls for `FRSoundness4P4aZ`/`L`/`T`/`DF`.

/-!
# Controls for pass 4

* `ZLM4.EtLocal`: P4a's `zlm4` meets it (`zlm4_etLocal`, +); a target reading the log's length
  does not (`not_etLocal_len`, −).
* `WitBits`: T4's `zW` meets it (`witBits_zW`, +); a constant non-bit witness does not
  (`not_witBits`, −).
* `rejOK_at4`: Z's check is one (`rejZ_ok4`, +); a check from an absorb position's squeeze
  successor is refused (`not_rejOK_at_sq`, −: position 3 is Z1's squeeze).
* `RejF4a`: no check fails before Zend's absorb (`not_rejF4a_short`, −); S2's failed round check is
  one (`rejF4a_of_rejS2`, +).
* `L3BadN`/`PendLcN`: never on a segment (`not_l3BadN_seg`, `not_pendLcN_seg`, −); on a node, a
  wrong masked value is L3's doom (`l3BadN_of`, +).
* `DF4a`: the background dooms every non-`msD` phase 2 … 12 (`DF4a_of_bgA`, +); phases 0, 1 and
  13 on are `False` (`not_DF4a_out`, −).
* `frontCls4a`: Zend's absorb (67) is no squeeze class and Z3's first squeeze (16) no absorb class
  (`frontCls4a_neg`, −); both are classified by their items (`frontCls4a_pos`, +).
* `SameStab4`: a predicate of `L` itself is not stable (`not_ss_log4`, −); `False` is (+).
* `WitOf`: T4's witness is the unpacked `fF` (`witOf_of`, +, for any source with `fz = fF`).
-/

namespace FR.Snd.P4a
open RecursionFast FR.Merkle Finset FR.Impl

/-! ## `EtLocal`, `WitBits` -/

/-- Control (negative): a target reading the log's length does not read before 2. -/
theorem not_etLocal_len :
    ¬ ZLM4.EtLocal ⟨0, 0, 0, fun _ es _ _ => if es.length ≤ 2 then 0 else 1⟩ := fun h => by
  have hA : Agree (List.replicate 2 default ++ [default]) (List.replicate 2 default) 2 :=
    agree_append _ _ (by simp)
  have := congrFun (congrFun (h (.seg .L32) _ _ hA) 0) 0
  simp at this

open Classical in
theorem exists_not_bit : ∃ x : F, ¬ IsBitF x := by
  by_contra h
  push Not at h
  have hs : (univ : Finset F) ⊆ {0, 1} := fun x _ => by
    rcases h x with hx | hx <;> simp [hx]
  have h1 := card_le_card hs
  rw [card_univ, F.card_F] at h1
  have h2 := h1.trans (card_insert_le _ _)
  simp at h2

/-- Control (negative): a constant non-bit witness is not bit-valued. -/
theorem not_witBits : ∃ zw : Wit, ¬ WitBits zw := by
  obtain ⟨x, hx⟩ := exists_not_bit
  exact ⟨fun _ _ _ _ => x, fun h => hx (h (.seg .L32) [] [] 0)⟩

/-- Control (positive): any source whose `fz` is `fF` at the log's kind has T4's `zW` as its
unpacked witness. -/
theorem witOf_of {R : P4b.FSrc} (h : ∀ L es, R.fz L es = T4.fF (kindOfC es) L es) :
    WitOf R T4.zW := fun L es b => by simp only [T4.zW, h]

/-! ## Checks -/

/-- Control (negative): `rejOK_at4` needs a non-squeeze: a check from Z1's first squeeze's
successor on is not a `T4.RejOK` (it changes at the squeeze). -/
theorem not_rejOK_at_sq : ¬ T4.RejOK fun (_ : Log) (es : Log) => 3 + 1 ≤ es.length := fun h => by
  have hsq : fsItems4[3]? = some .squeeze := by
    have := T4.sq_of_fsRnd (p := 3) (s0 := 2) (r := 10) (by
      rw [fsRnd4, fsRanges4_eq]; decide)
    exact this
  have := (h.sq [] (List.replicate 3 default) default (by simpa using hsq)).mp (by simp)
  simp at this

theorem not_rejF4a_short {M : ZLM4} {L es : Log} (hl : es.length < 68) : ¬ RejF4a M L es := by
  rintro (h | ⟨l, -, hl', -⟩ | h | h | ⟨l, -, hl', -⟩)
  · exact absurd h.1 (by omega)
  · omega
  · exact absurd h.1 (by omega)
  · exact absurd h.1 (by omega)
  · omega

theorem rejF4a_of_rejS2 {M : ZLM4} {L es : Log} (h : RejS2 L es) : RejF4a M L es :=
  Or.inr (Or.inr (Or.inr (Or.inr h)))

/-! ## The node's L dooms -/

theorem not_l3BadN_seg {M : ZLM4} {zw : Wit} {L es : Log} (hn : (kindOfC es).isNode = false) :
    ¬ L3BadN M zw L es := fun h => by rw [h.2.1] at hn; exact Bool.noConfusion hn

theorem not_pendLcN_seg {M : ZLM4} {zw : Wit} {L es : Log} (hn : (kindOfC es).isNode = false) :
    ¬ PendLcN M zw L es := fun h => by rw [h.2.1] at hn; exact Bool.noConfusion hn

theorem l3BadN_of {M : ZLM4} {zw : Wit} {L es : Log} (hl : 98 ≤ es.length)
    (hn : (kindOfC es).isNode = true) {j : Fin 9} (hj : vM (kindOfC es) es j ≠ zfL M zw L es j) :
    L3BadN M zw L es := ⟨hl, hn, j, hj⟩

/-! ## `DF4a` -/

/-- Control (positive): the background dooms every non-`msD` phase from 2 to 12. -/
theorem DF4a_of_bgA {P : Front4a} {L es : Log} (h : P.BgA L es) :
    ∀ k, 2 ≤ k → k ≤ 12 → k ≠ 3 → k ≠ 11 → DF4a P k L es := by
  intro k h1 h2 h3 h11
  interval_cases k <;> simp_all [DF4a, D2F4, D10F4, bgZ4, bg5_4, bg10_4]

/-- Control (negative): phases 0, 1 and those past S2 are not P4a's. -/
theorem not_DF4a_out {P : Front4a} {L es : Log} {k : ℕ} (hk : k < 2 ∨ 13 ≤ k) :
    ¬ DF4a P k L es := by
  rcases hk with hk | hk
  · interval_cases k <;> simp [DF4a]
  · obtain ⟨j, rfl⟩ : ∃ j, k = j + 13 := ⟨k - 13, by omega⟩
    simp [DF4a]

/-- Control (negative): the classification separates the items. -/
theorem frontCls4a_neg : frontCls4a 67 .squeeze = false ∧ frontCls4a 16 (.absorb 48) = false := by
  unfold frontCls4a rndCls4a absPts4a sqPts4a rndPh4a fsRnd4
  rw [fsRanges4_eq]; decide +kernel

/-- Control (positive): Z3's first squeeze and Zend's absorb are classified. -/
theorem frontCls4a_pos : frontCls4a 16 .squeeze = true ∧ frontCls4a 67 (.absorb 48) = true := by
  unfold frontCls4a rndCls4a absPts4a sqPts4a rndPh4a fsRnd4
  rw [fsRanges4_eq]; decide +kernel

/-! ## `SameStab4` -/

/-- Control (negative): a predicate of the charging log itself is not stable. -/
theorem not_ss_log4 : ¬ SameStab4 0 fun L _ => L = [] := fun h => by
  have := (h [] [(ByteArray.empty, 0)] [] (Nat.zero_le _)
    ⟨fun _ h => absurd h (Nat.not_lt_zero _), fun _ _ _ h => absurd h (Nat.not_lt_zero _)⟩).mp rfl
  simp at this

theorem ss_false4_ctrl : SameStab4 3 fun _ _ => False := ss_false4 3

end FR.Snd.P4a

end G6_FRSoundness4P4aCtrl4

section G6_FRSoundness4P4aSplit

-- New for `flock-recursive` (BLUEPRINT revision 4.1, §5.1–§5.2, A.10 phase 2; stage P4a pass 5
-- (P4e)): 3.x's `stmt_split` (`FRSoundnessFrDF`) at S-E12a's node statement `StmtN4` (deviation D6).

/-!
# The front's parameters at revision 4.1 and the statement split

* **`front4 zw BgA`**: `Front4a` at S-E12a's maps (`zlm4 indN4 etN4`, the node's S2 weight
  `wN4` and truth `truthSN4`); **`front4_ok`**: its hypotheses from the witness's (`WitBits`,
  `ZwSame`) and the background's reads.
* **`Stmt4`**: revision 4.1's statement on a log: a node's S-E12a `StmtN4` on `f⁽⁰⁾` (with its L
  rows, indexed M rows and public digests as parameters), a segment's Z and S truths (what
  `segHolds_of_truths` reads).
* **`stmt_split4`**: a false statement is phase 2's doom `DF4a 2 = (BgA ∨ ¬ truthS) ∨ ¬ ZHolds`,
  when `BgA` carries the node's L rows, M rows and public cells (P4b's parts).
-/

namespace FR.Snd.P4a
open RecursionFast FR.Merkle Finset FR.Impl

set_option linter.constructorNameAsVariable false

/-- **The front's parameters at S-E12a's maps.** -/
noncomputable def front4 (zw : Wit) (BgA : Log → Log → Prop) : Front4a :=
  ⟨zlm4 N4c.indN4 N4c.etN4, zw, wN4, truthSN4 zw, BgA⟩

theorem front4_ok {zw : Wit} {BgA : Log → Log → Prop} (hb : WitBits zw) (hz : ZwSame zw)
    (hBg : T4.Reads 3 BgA) : (front4 zw BgA).OK :=
  ⟨zlm4_bits4, N4c.zlm4_indKinds, zlm4_etLocal _ _, hb, hz, wNLocal4, hBg⟩

/-- **Revision 4.1's statement on a log**: a node's `StmtN4` on `f⁽⁰⁾` (L rows `lr`, indexed M rows
`er`, public digests `pv es = (vk, c₁, c₂)`), a segment's Z and S truths. -/
def Stmt4 (R : P4b.FSrc) (zw : Wit) (lr : Rev4.NodeKind → List Circ.Row)
    (er : Rev4.NodeKind → List (ℕ × Circ.Row)) (pv : Log → Digest × Digest × Digest) (L es : Log) :
    Prop :=
  match kindOfC es with
  | .node ν => N4c.StmtN4 ν (lr ν) (er ν) (pv es).1 (pv es).2.1 (pv es).2.2 (R.fz L es)
  | .seg _ => ZHolds (zlm4 N4c.indN4 N4c.etN4) zw L es ∧ truthS (truthSN4 zw) zw L es

/-- The node's parts that phases 13 … 25 reduce (P4b's): the L rows, the M rows, the public cells. -/
def NodeRest4 (R : P4b.FSrc) (lr : Rev4.NodeKind → List Circ.Row)
    (er : Rev4.NodeKind → List (ℕ × Circ.Row)) (pv : Log → Digest × Digest × Digest) (ν : Rev4.NodeKind)
    (L es : Log) : Prop :=
  (∀ r ∈ lr ν, r.Holds (R.fz L es)) ∧ P4b.truthEI (er ν) (R.fz L es) ∧
    N4c.PubCells4 ν (R.fz L es) (pv es).1 (pv es).2.1 (pv es).2.2

/-- **A false statement is phase 2's doom** (3.x's `stmt_split`, D6): the node's Z and S parts
are `ZHolds`/`truthS` (`zHolds_iff_truthZ4`, `truthS4_iff`), its other parts are in `BgA`. -/
theorem stmt_split4 {R : P4b.FSrc} {zw : Wit} (hzw : WitOf R zw) (hb : WitBits zw)
    {BgA : Log → Log → Prop} {lr : Rev4.NodeKind → List Circ.Row}
    {er : Rev4.NodeKind → List (ℕ × Circ.Row)} {pv : Log → Digest × Digest × Digest} {L es : Log}
    (hBg : ∀ ν, kindOfC es = .node ν → ¬ NodeRest4 R lr er pv ν L es → BgA L es)
    (h : ¬ Stmt4 R zw lr er pv L es) : DF4a (front4 zw BgA) 2 L es := by
  show (BgA L es ∨ ¬ truthS (truthSN4 zw) zw L es) ∨ ¬ ZHolds (zlm4 N4c.indN4 N4c.etN4) zw L es
  unfold Stmt4 at h
  cases hk : kindOfC es with
  | seg σ =>
    rw [hk] at h
    rcases not_and_or.mp h with h | h
    · exact .inr h
    · exact .inl (.inr h)
  | node ν =>
    rw [hk] at h
    unfold N4c.StmtN4 at h
    have hS : truthS (truthSN4 zw) zw L es ↔ N4c.truthS4 ν (R.fz L es) := by
      rw [truthS4_iff hzw hk, truthS, hk]; rfl
    by_cases hZ : N4c.truthZ4 ν (R.fz L es)
    · by_cases hS' : N4c.truthS4 ν (R.fz L es)
      · exact .inl (.inl (hBg ν hk fun hr => h ⟨hZ, hS', hr⟩))
      · exact .inl (.inr (hS.not.mpr hS'))
    · exact .inr ((zHolds_iff_truthZ4 hzw hb hk).not.mpr hZ)

/-! ## Controls -/

/-- (+) On a segment the statement is its Z and S truths. -/
theorem stmt4_seg_iff {R : P4b.FSrc} {zw : Wit} {lr : Rev4.NodeKind → List Circ.Row}
    {er : Rev4.NodeKind → List (ℕ × Circ.Row)} {pv : Log → Digest × Digest × Digest} {L es : Log}
    {σ : Rev4.SegKind} (hk : kindOfC es = .seg σ) :
    Stmt4 R zw lr er pv L es ↔
      ZHolds (zlm4 N4c.indN4 N4c.etN4) zw L es ∧ truthS (truthSN4 zw) zw L es := by
  unfold Stmt4; rw [hk]

/-- (+) On a node the statement is S-E12a's `StmtN4`. -/
theorem stmt4_node_iff {R : P4b.FSrc} {zw : Wit} {lr : Rev4.NodeKind → List Circ.Row}
    {er : Rev4.NodeKind → List (ℕ × Circ.Row)} {pv : Log → Digest × Digest × Digest} {L es : Log}
    {ν : Rev4.NodeKind} (hk : kindOfC es = .node ν) :
    Stmt4 R zw lr er pv L es ↔
      N4c.StmtN4 ν (lr ν) (er ν) (pv es).1 (pv es).2.1 (pv es).2.2 (R.fz L es) := by
  unfold Stmt4; rw [hk]

/-- (−) A segment whose Z rows fail does not meet the statement, and is doomed at phase 2. -/
theorem not_stmt4_seg {R : P4b.FSrc} {zw : Wit} {lr : Rev4.NodeKind → List Circ.Row}
    {er : Rev4.NodeKind → List (ℕ × Circ.Row)} {pv : Log → Digest × Digest × Digest} {L es : Log}
    {σ : Rev4.SegKind} (hk : kindOfC es = .seg σ) (hz : ¬ ZHolds (zlm4 N4c.indN4 N4c.etN4) zw L es) :
    ¬ Stmt4 R zw lr er pv L es := fun h => hz ((stmt4_seg_iff hk).mp h).1

end FR.Snd.P4a

end G6_FRSoundness4P4aSplit

section G6_FRSoundness4XFront

-- New for `flock-recursive` (BLUEPRINT revision 4.1, §5.1–§5.2, A.10; stage X4, item 1): the front
-- of revision 4.1 composed from P4a's phases 0 … 12 and P4b's checks and readers.

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

end G6_FRSoundness4XFront

section G6_FRSoundness4P4fDF

-- New for `flock-recursive` (BLUEPRINT revision 4.1, A.10 rows Lr1 … B′, §5.1–§5.2; stage P4f):
-- the front's phase dooms 13 … 25 at `seq4`, over X4's composed doom `DFX` and checks `RejFX`.
-- 3.x's `FRSoundnessFrDF` (`DF 13 … 25`) is the template, P4a's `FRSoundness4P4aDF` the form.

/-!
# The front's phases 13 … 25 at revision 4.1: the dooms `DFhi`

* **S2's pending claim on every segment** (`endS4U`, `pendS4U`): P4a's `endS4`/`pendS4_pendBad4`
  assume a segment's last block is among its blocks (`lastL < 2^nb`, `V_A`'s `n ≤ cap`, which no
  final of the segment program asserts). The assumption is not needed: past the blocks both the
  doom's weight and `finSh` (ii)'s `wSumSeg` lose their end term (`final_segU`, `wSumSegU`), so the
  pending S claim is RS0's `PendBad4` on every log. Without this, a segment log with `n > cap` and a
  false S2 claim could not be carried past RS0.
* **The backgrounds** (3.x's `bg20`, `bg12`, `bg16` at revision 4.1): `bg20X` (far, a false
  public cell, the pending Z, Lc (both kinds) and S claims), `bg12X` (and the M rows, until E1),
  `bg16X` (and Lr's pending batch, Lr3 … E end). X4's `BgA4` (far, public, L rows, M rows) is
  carried by phase 12's doom; Lr1 reduces its L rows, E1 its M rows, RS0 the pending claims.
* **`DFhi`**: phases 13 … 25 (3.x's `DF 13 … 25`): Lr1 `msD` over phase 12's doom, Lr2's outer
  rounds, Lrend's triple, Lr3's batch, E1 … E4 end, then P4b's `DRS0_4`, `msD DRS0_4 DRS1_4`,
  `DB4` at `far0X` and `PubOK4 src4 cells4`.
* **`dPend_X`**: E4 end's doom is P4b's `DPend4` at RS0 (the five pending-claim bridges).
* **`dfhi_ss`**: phase `k`'s doom reads the same off two logs whose words agree, on `X` of at least
  `phStart4 k + 1` entries (`hstab`, `chain`).
-/

namespace FR.Snd.P4f
open RecursionFast FR.Merkle FR.Rev4 Finset FR.Impl

set_option linter.constructorNameAsVariable false

/-! ## S2's pending claim on every segment -/

/-- **A segment's final value without the block bound** (P4a's `final_seg` with `Lb < 2^18` for
`Lb < 2^nb`): past the blocks the end term is `0` on both sides. -/
theorem final_segU {nb : ℕ} (hnb : nb ≤ 18) (τs rb bits : List F) (hτ : τs.length = nb)
    (hrb : rb.length = nb) {Lb : ℕ} (hL : Lb < 2 ^ 18)
    (hbits : Rev4.lastAt (τs ++ List.replicate (18 - nb) 0 ++ bits).toArray 18 = Lb)
    (θ rp : Array F) (κ : F) :
    ∑ q ∈ range (2 ^ 10), ∑ y ∈ range (2 ^ nb),
        eqAtR (ptOf nb rb) y * eqAtR (ptA 10 rp) q * P4a.wSeg (ptOf nb τs) (ptA 10 θ) κ Lb y q =
      (Rev4.shiftSegS (τs ++ List.replicate (18 - nb) 0 ++ bits).toArray
          (rb ++ List.replicate (18 - nb) 0).toArray).1 * slotWS 0 θ rp +
        ((Rev4.shiftSegS (τs ++ List.replicate (18 - nb) 0 ++ bits).toArray
            (rb ++ List.replicate (18 - nb) 0).toArray).2.1 +
          κ * (Rev4.shiftSegS (τs ++ List.replicate (18 - nb) 0 ++ bits).toArray
            (rb ++ List.replicate (18 - nb) 0).toArray).2.2) * slotWS 1 θ rp := by
  set τP := τs ++ List.replicate (18 - nb) 0
  set rP := rb ++ List.replicate (18 - nb) 0
  have hτP : τP.length = 18 := by simp [τP, hτ]; omega
  have hrP : rP.length = 18 := by simp [rP, hrb]; omega
  have hA : ptA 18 (τP ++ bits).toArray = ptOf 18 τP := funext fun l => by
    simp only [ptA, ptOf, Array.getD_eq_getD_getElem?, List.getElem?_toArray,
      List.getD_eq_getElem?_getD, List.getElem?_append_left (show l.val < τP.length by omega)]
  have hB : ptA 18 rP.toArray = ptOf 18 rP := ptA_toArray _ _
  have h1 : (Rev4.shiftSegS (τP ++ bits).toArray rP.toArray).1 = eqPoint τP.toArray rP.toArray := by
    rw [eqPoint_eq, List.size_toArray, hτP, ptA_toArray, ptA_toArray]
    simp only [Rev4.shiftSegS, hA, hB]
  have hmle : shiftMle 18 (ptOf 18 τP) (ptOf 18 rP) = shiftEqS τP.toArray rP.toArray := by
    rw [← shiftEq_meets _ _ (by simp [hτP, hrP]), shiftEqI, List.toList_toArray, List.toList_toArray,
      shiftPair_eq 18 τP rP hτP hrP]
  -- the only change against `final_seg`: the end term without `Lb < 2^nb`
  have hc : (if Lb + 1 < 2 ^ 18 then eqAtR (ptOf 18 τP) Lb * eqAtR (ptOf 18 rP) (Lb + 1) else 0) =
      if Lb + 1 < 2 ^ nb then eqAtR (ptOf nb τs) Lb * eqAtR (ptOf nb rb) (Lb + 1) else 0 := by
    have h18 : 2 ^ nb ≤ 2 ^ 18 := Nat.pow_le_pow_right (by norm_num) hnb
    rw [P4a.eqAtR_padN hnb τs hτ hL]
    by_cases h : Lb + 1 < 2 ^ nb
    · rw [if_pos (show Lb + 1 < 2 ^ 18 by omega), if_pos (show Lb < 2 ^ nb by omega),
        P4a.eqAtR_padN hnb rb hrb (by omega), if_pos h, if_pos h]
    · rw [if_neg h]
      by_cases h' : Lb + 1 < 2 ^ 18
      · rw [if_pos h', P4a.eqAtR_padN hnb rb hrb h', if_neg h, mul_zero]
      · rw [if_neg h']
  have h2 : (Rev4.shiftSegS (τP ++ bits).toArray rP.toArray).2.1 = shiftEqS τP.toArray rP.toArray +
      if Lb + 1 < 2 ^ nb then eqAtR (ptOf nb τs) Lb * eqAtR (ptOf nb rb) (Lb + 1) else 0 := by
    simp only [Rev4.shiftSegS, hA, hB, hbits, hmle]
    rw [← hc]
  have h3 : (Rev4.shiftSegS (τP ++ bits).toArray rP.toArray).2.2 =
      eqPoint (Array.replicate 18 0) rP.toArray := by
    rw [P4a.eqPoint_zero18 rP hrP]; simp only [Rev4.shiftSegS, hB]
  rw [h1, h2, h3]
  have hw : ∀ y q, P4a.wSeg (ptOf nb τs) (ptA 10 θ) κ Lb y q = wLeaf (ptOf nb τs) (ptA 10 θ) κ y q +
      (if y = Lb + 1 then eqAtR (ptOf nb τs) Lb else 0) * slotT (ptA 10 θ) 520 q := fun y q => by
    simp only [P4a.wSeg, wLeaf, P4a.shSeg_eq]; ring
  simp only [hw, mul_add, sum_add_distrib]
  rw [final_leaf hnb τs rb hτ hrb θ rp κ]
  have hlink : ∑ q ∈ range (2 ^ 10), ∑ y ∈ range (2 ^ nb), eqAtR (ptOf nb rb) y *
      eqAtR (ptA 10 rp) q * ((if y = Lb + 1 then eqAtR (ptOf nb τs) Lb else 0) *
        slotT (ptA 10 θ) 520 q) =
      (if Lb + 1 < 2 ^ nb then eqAtR (ptOf nb τs) Lb * eqAtR (ptOf nb rb) (Lb + 1) else 0) *
        slotWS 1 θ rp := by
    have e : ∀ q ∈ range (2 ^ 10), ∑ y ∈ range (2 ^ nb), eqAtR (ptOf nb rb) y *
        eqAtR (ptA 10 rp) q * ((if y = Lb + 1 then eqAtR (ptOf nb τs) Lb else 0) *
          slotT (ptA 10 θ) 520 q) =
        (if Lb + 1 < 2 ^ nb then eqAtR (ptOf nb τs) Lb * eqAtR (ptOf nb rb) (Lb + 1) else 0) *
          (eqAtR (ptA 10 rp) q * slotT (ptA 10 θ) 520 q) := fun q _ => by
      simp only [mul_ite, mul_zero, ite_mul, zero_mul, sum_ite_eq', mem_range]
      split_ifs <;> ring
    rw [sum_congr rfl e, ← mul_sum, sum_slot_eqAtR _ _ (by norm_num), slotWS_eq]
    rfl
  rw [hlink]
  ring

/-- **A segment's weight value is the extension of `wS`** (P4a's `wSumSeg_eq` on every segment). -/
theorem wSumSegU (wN : CKind → Log → ℕ → ℕ → F) {es : Log} (hn : (kindOfC es).isNode = false) :
    P4a.wSumSeg (kindOfC es) es = ∑ q ∈ range (2 ^ 10), ∑ y ∈ range (2 ^ P4a.nbC (kindOfC es)),
      eqAtR (ptOf (P4a.nbC (kindOfC es)) (P4a.rbL (kindOfC es) es)) y *
        eqAtR (ptOf 10 (P4a.rpL (kindOfC es) es)) q * P4a.wS wN (kindOfC es) es y q := by
  generalize hκ : kindOfC es = κ at hn
  have hθ : ptA 10 (thL es).toArray = ptOf 10 (thL es) := ptA_toArray _ _
  have hr : ptA 10 (P4a.rpL κ es).toArray = ptOf 10 (P4a.rpL κ es) := ptA_toArray _ _
  have hτ : (P4a.tauL κ es).length = P4a.nbC κ := by simp [P4a.tauL]
  have hrb : (P4a.rbL κ es).length = P4a.nbC κ := by simp [P4a.rbL]
  have e := final_segU (P4a.nbC_le κ) (P4a.tauL κ es) (P4a.rbL κ es) (P4a.lastBits es) hτ hrb
    (P4a.lastL_lt es) (P4a.lastAt_tauLL κ es) (thL es).toArray (P4a.rpL κ es).toArray (ksL es)
  rw [hθ, hr] at e
  simp only [P4a.wS, hn, Bool.false_eq_true, if_false]
  rw [e]
  rfl

/-- **At S2's end its doom is the Sh binding failing at `ẑ`** (P4a's `endS4` on every segment). -/
theorem endS4U {wN : CKind → Log → ℕ → ℕ → F} {zw : P4a.Wit} {wNS : CKind → Log → F} {L es : Log}
    (hNS : (kindOfC es).isNode = true → wNS (kindOfC es) es =
      ∑ q ∈ range (2 ^ 10), ∑ y ∈ range (2 ^ P4a.nbC (kindOfC es)),
        eqAtR (ptOf (P4a.nbC (kindOfC es)) (P4a.rbL (kindOfC es) es)) y *
          eqAtR (ptOf 10 (P4a.rpL (kindOfC es) es)) q * wN (kindOfC es) es y q)
    (h : P4a.D2S wN zw L es) (hl : 170 ≤ es.length) :
    ¬ P4a.oSh4 wNS (kindOfC es) es (P4a.zS2 zw L es) := by
  obtain ⟨-, hw⟩ := h
  have ha : T4.ans3 114 P4a.nrS es = P4a.nrS (kindOfC es) := by
    have := P4a.nrS_le4 (kindOfC es); unfold T4.ans3; simp; omega
  rw [ha] at hw
  unfold T4.Wrong2 at hw
  rw [Nat.sub_self, trueSum_bindAll' _ _ _ (by simp [rchs2]) (P4a.TS_size4 L es), innerExpr_eval2,
    P4a.TS, arrGetD_pair0, arrGetD_pair1, P4a.nrS, mle_tab, mle_tab,
    (P4a.rchsS_pts4 _ es).1, (P4a.rchsS_pts4 _ es).2] at hw
  intro hok
  apply hw
  have hW : P4a.wSumL4 wNS (kindOfC es) es = ∑ q ∈ range (2 ^ 10),
      ∑ y ∈ range (2 ^ P4a.nbC (kindOfC es)),
      eqAtR (ptOf (P4a.nbC (kindOfC es)) (P4a.rbL (kindOfC es) es)) y *
        eqAtR (ptOf 10 (P4a.rpL (kindOfC es) es)) q * P4a.wS wN (kindOfC es) es y q := by
    unfold P4a.wSumL4
    cases hn : (kindOfC es).isNode
    · simp only [Bool.false_eq_true, if_false]; exact wSumSegU wN hn
    · simp only [if_true]; rw [hNS hn]
      simp only [P4a.wS, hn, if_true]
  rw [P4a.oSh4, P4a.claimSL4, hW, P4a.zS2] at hok
  rw [show clR2 114 16 readF (fun d => chF d 0) P4a.c0SL L es (P4a.nbC (kindOfC es) + 10) =
    P4a.claimSL4 (kindOfC es) es from clR2_same rfl (fun _ _ => rfl), P4a.claimSL4]
  exact hok

/-- **S2's doom at its end is RS0's `PendBad4` at claim 3** on every log (P4a's `pendS4_pendBad4`
without its segment bound). -/
theorem pendS4U (R : P4b.FSrc) (kf : NodeKind → F → ℕ → F)
    {oZ oLc : CKind → Log → F → Prop} {wN : CKind → Log → ℕ → ℕ → F} {zw : P4a.Wit}
    {wNS : CKind → Log → F} (hzw : P4a.WitOf R zw) {L es : Log}
    (hNS : (kindOfC es).isNode = true → wNS (kindOfC es) es =
      ∑ q ∈ range (2 ^ 10), ∑ y ∈ range (2 ^ P4a.nbC (kindOfC es)),
        eqAtR (ptOf (P4a.nbC (kindOfC es)) (P4a.rbL (kindOfC es) es)) y *
          eqAtR (ptOf 10 (P4a.rpL (kindOfC es) es)) q * wN (kindOfC es) es y q)
    (h : P4a.D2S wN zw L es) (hl : 170 ≤ es.length) :
    P4b.PendBad4 R kf (P4b.okRS4 oZ oLc (P4a.oSh4 wNS)) L es := by
  refine ⟨2, by rw [P4b.rsPtsL4_length]; split_ifs <;> norm_num, fun ho => endS4U hNS h hl ?_⟩
  have ho' : P4a.oSh4 wNS (kindOfC es) es (P4b.trueL4 R kf (kindOfC es) L es 2) := ho
  rwa [P4a.trueL4_two R kf hzw] at ho'

/-! ## The background parts and the dooms -/

/-- The level-0 word is far (`BgA4`'s first part). -/
def far0X (L es : Log) : Prop := T4.farL (kindOfC es) L es 0

/-- The node's public cells hold (`BgA4`'s second part, S-E's `cells4`). -/
def PubX : Log → Log → Prop := P4b.PubOK4 X4.src4 N4c.cells4

/-- **From E3 on**: far, a false public cell, the pending Z, Lc (both kinds) and S claims (3.x's
`bg20`). -/
def bg20X (L es : Log) : Prop :=
  far0X L es ∨ ¬ PubX L es ∨ P4a.PendZ X4.P4X.zw L es ∨ P4a.PendLc X4.P4X.M X4.P4X.zw L es ∨
    P4a.PendLcN X4.P4X.M X4.P4X.zw L es ∨ P4a.D2S X4.P4X.wN X4.P4X.zw L es

/-- **S2 … Lr end**: and the M rows (E1 reduces them; 3.x's `bg12`). -/
def bg12X (L es : Log) : Prop := bg20X L es ∨ P4b.nE4 X4.src4 NI4F.srcE4 L es

/-- **Lr3 … E end**: and Lr's pending batch (E3 reduces it; 3.x's `bg16`). -/
def bg16X (L es : Log) : Prop := bg20X L es ∨ P4b.BatBadLr4 X4.src4 NI4F.srcL4 L es

/-- **Lr3's doom** (E1's entry; 3.x's `D16F`; revision 4.4.2, RSV2 §2.6: or a false child claim,
which E1's `η·D` term reduces). -/
def D16X (L es : Log) : Prop :=
  bg16X L es ∨ P4b.nE4 X4.src4 NI4F.srcE4 L es ∨ P4b.ChildBad4 NI4F.srcE4 L es

/-- **The reserve's cells hold** (revision 4.4.2, RSV2 §2.4): `f⁽⁰⁾` at `Rev4.rsvCells` is the node's
own child claim (Lrend's message, 213). It enters only RS0's and RS1's `Pub` (`PubRSX`): RS0's doom
is a post-doom (read at 327 > 214), so the backgrounds of phases 16 … 22 keep `PubX` alone. -/
def PubRX : Log → Log → Prop := P4b.PubOKR4 X4.src4 Rev4.rsvCells

/-- RS0's and RS1's `Pub`: the nine public cells and the 60 reserve cells. -/
def PubRSX (L es : Log) : Prop := PubX L es ∧ PubRX L es

/-- RS0's, RS1's and B′'s dooms at `far0X`, `PubRSX` and S-E's kind factor; B′ batches `X4.cellsX`
(the nine public cells and the reserve's). -/
noncomputable def DRS0X : Log → Log → Prop := P4b.DRS0_4 X4.src4 N4c.kf4 far0X PubRSX
noncomputable def DRS1X : Log → Log → Prop := P4b.DRS1_4 X4.src4 N4c.kf4 far0X PubRSX
noncomputable def DBX : Log → Log → Prop := P4b.DB4 X4.src4 N4c.kf4 X4.cellsX far0X

/-- **The front's phase dooms 13 … 25** (3.x's `DF 13 … 25`): Lr1 is `msD` over phase 12's doom
(P4a's `DF4a P4X 12`, which carries `BgA4`). -/
noncomputable def DFhi : ℕ → Log → Log → Prop
  | 13 => msD (P4a.DF4a X4.P4X 12)
      (fun L es => bg12X L es ∨ P4b.ZCwLr4 X4.src4 NI4F.srcL4 L es) 169 9
  | 14 => fun L es => bg12X L es ∨ P4b.D3Lr4 X4.src4 NI4F.srcL4 L es
  | 15 => fun L es => bg12X L es ∨ P4b.EndBadLr4 X4.src4 NI4F.srcL4 L es
  | 16 => D16X
  | 17 => msD D16X (fun L es => bg16X L es ∨ P4b.ZCwE4 X4.src4 NI4F.srcE4 L es) 214 12
  | 18 => fun L es => bg16X L es ∨ P4b.D3E4 X4.src4 NI4F.srcE4 L es
  | 19 => fun L es => bg16X L es ∨ P4b.EndBadE4 X4.src4 NI4F.srcE4 L es
  | 20 => fun L es => bg20X L es ∨ P4b.BatBadE4 X4.src4 NI4F.srcE4 NI4F.srcL4 L es
  | 21 => fun L es => bg20X L es ∨ P4b.D4E4 X4.src4 NI4F.srcE4 NI4F.srcL4 L es
  | 22 => fun L es => bg20X L es ∨ P4b.PendE4 X4.src4 L es
  | 23 => DRS0X
  | 24 => msD DRS0X DRS1X 326 4
  | 25 => DBX
  | _ => fun _ _ => False

/-! ## Reads -/

theorem rd_far0X : T4.Reads 3 far0X := fun L es L' es' _ _ hS => by
  unfold far0X; rw [hS.kind (by norm_num)]
  exact T4.farL_same hS (i := 0) (by norm_num) _ (by rw [P4a.capPos_zero4]; omega)

theorem rd_PubX : T4.Reads 3 PubX := P4b.pubOK4_reads X4.src4 N4c.cells4

theorem rd_PubRX : T4.Reads 214 PubRX := P4b.pubOKR4_reads X4.src4 Rev4.rsvCells

theorem rd_PubRSX : T4.Reads 214 PubRSX :=
  P4b.ReadsS.and (R := X4.src4) (rd_PubX.mono (by norm_num)) rd_PubRX

theorem rd_bg20X : T4.Reads 170 bg20X :=
  (rd_far0X.mono (by norm_num)).or ((rd_PubX.not.mono (by norm_num)).or
    (((P4a.pendZ_reads4 P4a.zwSame_zW).mono (by norm_num)).or
    (((P4a.pendLc_reads4 P4a.zwSame_zW).mono (by norm_num)).or
    (((P4a.pendLcN_reads4 P4a.zwSame_zW).mono (by norm_num)).or
      (P4a.D2S_reads4 P4a.wNLocal4 P4a.zwSame_zW)))))

theorem rd_nE4X : T4.Reads 3 (P4b.nE4 X4.src4 NI4F.srcE4) :=
  P4b.readsS_onNode (R := X4.src4) (by norm_num)
    (fun κ => P4b.rowsBadG_reads X4.src4 (NI4F.srcE4 κ) (P4b.e2R κ) (P4b.ncR κ))

theorem rd_bg12X : T4.Reads 170 bg12X := rd_bg20X.or (rd_nE4X.mono (by norm_num))

theorem rd_batLr : T4.Reads 215 (P4b.BatBadLr4 X4.src4 NI4F.srcL4) :=
  P4b.readsS_onNode (R := X4.src4) (by norm_num) fun κ =>
    P4b.batBadG_reads X4.src4 (NI4F.srcL4 κ) (P4b.lrR κ) (P4b.ncR κ) 179 17 (by norm_num)
      (P4b.dims_le' κ).1

theorem rd_bg16X : T4.Reads 215 bg16X := (rd_bg20X.mono (by norm_num)).or rd_batLr

/-- A false child claim reads Lrend's message (213). -/
theorem rd_childX : T4.Reads 214 (P4b.ChildBad4 NI4F.srcE4) := fun L es L' es' h1 h2 hS => by
  have hA : Agree es es' 214 := hS.1
  obtain ⟨hx, hy, hs, hX⟩ := P4b.child_agree hA le_rfl
  simp only [P4b.ChildBad4, P4b.OnNode, P4b.truthChild4, hx, hy, hs, hX,
    kindOfC_congr (hA.mono (by norm_num))]
  exact ⟨fun ⟨κ, hk, _, h⟩ => ⟨κ, hk, h2, h⟩, fun ⟨κ, hk, _, h⟩ => ⟨κ, hk, h1, h⟩⟩

theorem rd_D16X : T4.Reads 215 D16X :=
  rd_bg16X.or ((rd_nE4X.mono (by norm_num)).or (rd_childX.mono (by norm_num)))

/-! ## E4 end's doom is RS0's `DPend4` -/

/-- **E4 end's doom is `DPend4` at RS0** (3.x's `dPend_of`): far and the public cells carry over;
the pending Z, Lc (both kinds), S and E claims fail their bindings (`okX`) at their true values. -/
theorem dPend_X {L es : Log} (hl : 170 ≤ es.length) (h : DFhi 22 L es) :
    P4b.DPend4 X4.src4 N4c.kf4 X4.okX far0X PubX L es := by
  simp only [DFhi, bg20X] at h
  rcases h with (h | h | h | h | h | h) | h
  · exact .inl h
  · exact .inr (.inl h)
  · exact .inr (.inr (P4a.pendZ4_pendBad4 X4.src4 N4c.kf4 X4.witOf_src4 h))
  · exact .inr (.inr (P4a.pendLc4_pendBad4 X4.src4 N4c.kf4 (P4a.segInd_zlm4 _ _) X4.witOf_src4 h))
  · exact .inr (.inr (P4a.pendLcN4_pendBad4 X4.src4 P4a.kfInd4 X4.witOf_src4 h))
  · exact .inr (.inr (pendS4U X4.src4 N4c.kf4 X4.witOf_src4 P4a.hNS4 h hl))
  · exact .inr (.inr (P4b.pendE4_pendBad4 h))

/-! ## `hstab`: the dooms read `L` only through the words -/

/-- The phase starts 12 … 26. -/
theorem phStart_hi : phStart4 12 = 114 ∧ phStart4 13 = 170 ∧ phStart4 14 = 179 ∧
    phStart4 15 = 213 ∧ phStart4 16 = 214 ∧ phStart4 17 = 215 ∧ phStart4 18 = 227 ∧
    phStart4 19 = 273 ∧ phStart4 20 = 274 ∧ phStart4 21 = 275 ∧ phStart4 22 = 325 ∧
    phStart4 23 = 326 ∧ phStart4 24 = 327 ∧ phStart4 25 = 331 ∧ phStart4 26 = 332 := by
  obtain ⟨-, -, -, h13, h14, h15, h16, h17, h18, h19, h20, h21, h22, h23, h24, h25, h26⟩ :=
    P4b.p4b_pos
  exact ⟨P4a.phStart_vals4a.2.2.2.2.2.2.2.2.2.2, h13, h14, h15, h16, h17, h18, h19, h20, h21, h22,
    h23, h24, h25, h26⟩

section SS
variable {L L' X : Log}

theorem ss_D3Lr4 : P4a.SameStab4 180 (P4b.D3Lr4 X4.src4 NI4F.srcL4) := fun L L' X hx hS =>
  P4b.onNode_congr rfl fun κ _ => P4b.D3G_same X4.src4 (NI4F.srcL4 κ) (P4b.lrR κ) (P4b.ncR κ) 169
    179 hS (by omega) (by have := (P4b.dims_le' κ).1; omega)

theorem ss_D3E4 : P4a.SameStab4 228 (P4b.D3E4 X4.src4 NI4F.srcE4) := fun L L' X hx hS =>
  P4b.onNode_congr rfl fun κ _ => P4b.D3E4_same X4.src4 NI4F.srcE4 κ hS (by omega)

theorem ss_batE4 : P4a.SameStab4 275 (P4b.BatBadE4 X4.src4 NI4F.srcE4 NI4F.srcL4) :=
  fun L L' X hx hS => P4b.onNode_congr rfl fun κ _ => by
    simp only [P4b.c4E4_agree (L := L) (L' := L') (fun _ _ => rfl : Agree X X 275) le_rfl,
      P4b.TEb4_same X4.src4 NI4F.srcE4 NI4F.srcL4 κ hS (by omega)]

theorem ss_D4E4 : P4a.SameStab4 276 (P4b.D4E4 X4.src4 NI4F.srcE4 NI4F.srcL4) :=
  fun L L' X hx hS => P4b.onNode_congr rfl fun κ _ =>
    D2_congrL (P4b.TEb4_same X4.src4 NI4F.srcE4 NI4F.srcL4 κ hS (by omega))
      (P4b.c4E4_agree (fun _ _ => rfl : Agree X X 275) le_rfl)

theorem ss_pendE4 : P4a.SameStab4 326 (P4b.PendE4 X4.src4) := fun L L' X hx hS =>
  P4b.onNode_congr rfl fun κ _ => by
    simp only [P4b.zCG_same X4.src4 (P4b.ncR κ) hS (show 3 ≤ X.length by omega)]

theorem rd_zcwLr : T4.Reads 179 (P4b.ZCwLr4 X4.src4 NI4F.srcL4) :=
  P4b.readsS_onNode (R := X4.src4) (by norm_num) fun κ =>
    (P4b.zcwG_reads X4.src4 (NI4F.srcL4 κ) (P4b.lrR κ) (P4b.ncR κ) 169 (by omega)).mono
      (by have := (P4b.dims_le' κ).1; omega)

theorem rd_zcwE : T4.Reads 227 (P4b.ZCwE4 X4.src4 NI4F.srcE4) :=
  P4b.readsS_onNode (R := X4.src4) (by norm_num) fun κ => P4b.zcwE4_reads X4.src4 NI4F.srcE4 κ

theorem rd_endLr : T4.Reads 214 (P4b.EndBadLr4 X4.src4 NI4F.srcL4) :=
  P4b.readsS_onNode (R := X4.src4) (by norm_num) fun κ =>
    P4b.endBadG_reads X4.src4 (NI4F.srcL4 κ) (P4b.lrR κ) (P4b.ncR κ) 179 17 (by norm_num)
      (P4b.dims_le' κ).1

theorem rd_endE : T4.Reads 274 (P4b.EndBadE4 X4.src4 NI4F.srcE4) :=
  P4b.readsS_onNode (R := X4.src4) (by norm_num) fun κ => P4b.endBadE4_reads X4.src4 NI4F.srcE4 κ

theorem rd_DRS0X : T4.Reads 327 DRS0X :=
  P4b.dRS0_4_reads (R := X4.src4) rd_far0X (rd_PubRSX.mono (by norm_num))
theorem rd_DRS1X : T4.Reads 331 DRS1X :=
  P4b.dRS1_4_reads (R := X4.src4) rd_far0X (rd_PubRSX.mono (by norm_num))
theorem rd_DBX : T4.Reads 332 DBX := P4b.dB4_reads (R := X4.src4) rd_far0X

theorem ss_df12 : P4a.SameStab4 170 (P4a.DF4a X4.P4X 12) := by
  have h := P4a.df_ss4a X4.P4X_ok (P4a.sNode4 P4a.zwSame_zW) 12 le_rfl
  rw [phStart_hi.1] at h
  exact h.up 170

/-- **Phase `k`'s doom reads the same off two logs whose words agree**, on `X` of at least
`phStart4 k + 1` entries (`13 ≤ k ≤ 25`). -/
theorem dfhi_ss : ∀ k, 12 < k → k ≤ 25 → P4a.SameStab4 (phStart4 k + 1) (DFhi k) := by
  obtain ⟨-, h13, h14, h15, h16, h17, h18, h19, h20, h21, h22, h23, h24, h25, -⟩ := phStart_hi
  have b20 := P4a.ss_reads4 rd_bg20X
  have b12 := P4a.ss_reads4 rd_bg12X
  have b16 := P4a.ss_reads4 rd_bg16X
  have d16 := P4a.ss_reads4 rd_D16X
  intro k hk1 hk2
  interval_cases k
  · rw [h13]
    exact (P4a.ss_msD4 ss_df12 ((b12.up 179).or (P4a.ss_reads4 rd_zcwLr)) (by norm_num)).up _
  · rw [h14]; exact (b12.up 180).or ss_D3Lr4
  · rw [h15]; exact (b12.up 214).or (P4a.ss_reads4 rd_endLr)
  · rw [h16]; exact d16
  · rw [h17]
    exact (P4a.ss_msD4 d16 ((b16.up 227).or (P4a.ss_reads4 rd_zcwE)) (by norm_num)).up _
  · rw [h18]; exact (b16.up 228).or ss_D3E4
  · rw [h19]; exact (b16.up 274).or (P4a.ss_reads4 rd_endE)
  · rw [h20]; exact (b20.up 275).or ss_batE4
  · rw [h21]; exact (b20.up 276).or ss_D4E4
  · rw [h22]; exact (b20.up 326).or ss_pendE4
  · rw [h23]; exact P4a.ss_reads4 rd_DRS0X
  · rw [h24]
    exact (P4a.ss_msD4 (P4a.ss_reads4 rd_DRS0X) (P4a.ss_reads4 rd_DRS1X) (by norm_num)).up _
  · rw [h25]; exact P4a.ss_reads4 rd_DBX

end SS

end FR.Snd.P4f

end G6_FRSoundness4P4fDF

section G6_FRSoundness4XLaws

-- New for `flock-recursive` (BLUEPRINT revision 4.1, B-12, B-13, §5; stage X4, items 2–3): the segment
-- law and the node truths from the composed front, T4's tail and the program layer's run facts.

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

/-- **The good logs** for the composed front: within `logCap`, below potential `1` (revision 4.4.1:
the composed checks guarded by the cap truth, `T4.RejG`). -/
def GoodX (DFhi : ℕ → Log → Log → Prop) (L : Log) : Prop :=
  L.length ≤ logCap ∧ T4.muT (T4.RejG RejFX c0X) (T4.DkC (DFX DFhi) W0X c0X) L < 1

/-- **A segment's statement on the log**: the chain's kind, start digest, end digest and count. -/
def SegLog (v : SegView) (es : Log) : Prop :=
  kindOfC es = .seg v.kind ∧ bytesAt (entAt es 0).1 87 32 = v.start ∧
    bytesAt (msgAt es 1) 1 32 = v.h ∧ P4a.nStmt es = v.n

/-- **A node's statement on the log**: the chain's kind, the key it carries and the absorbed
statement digests. -/
def NodeLog (κ : NodeKind) (vk c : Digest) (π : Proof) (es : Log) : Prop :=
  kindOfC es = .node κ ∧ X.vkOf π = vk ∧ vkL es = vk ∧ c = nodeStmt (stL es 0) (stL es 1)

/-- **The reserve's zero outputs on the log** (revision 4.4.2, RSV2 §2.2): the child claim's
`X₃[1]`, `X₃[2]` (Lrend's message, values 58 and 59) are `0`, as `finE` asserts on every node kind.
`RunFacts4.node` carries them with `NodeLog`. -/
def RsvZero (es : Log) : Prop := P4b.rsvV es 58 = 0 ∧ P4b.rsvV es 59 = 0

/-- **The program layer's residual**: every accepted run on a log without collisions or state hits
has a chain that is an `AcceptTail` of the composed front and whose statement reads are the
run's. A segment run is asked for only on the proofs `V_A` runs (INT-10, R4i's F1): `π` of
`piSizeOf seq4` bytes (`VAwith`'s size check, `piSize_aggSegs`) and `n ≤ cap` (`aggChecks`). -/
structure RunFacts4 (Vseg : SegProgs) (Vnode : NodeProgs) (vk : Digest) : Prop where
  seg : ∀ L π v, ¬ Bad L → segView π = some v → π.size = piSizeOf seq4 → v.n ≤ v.kind.cap →
    (Vseg v.kind vk (segC v) π).runLog L = some true →
    ∃ j, T4.AcceptTail RejFX W0X c0X L j ∧ SegLog v (entriesOf L (pathOf L j))
  node : ∀ κ L c π, ¬ Bad L → kindOf4 π = .node κ → (Vnode κ vk c π).runLog L = some true →
    ∃ j, T4.AcceptTail RejFX W0X c0X L j ∧ NodeLog κ vk c π (entriesOf L (pathOf L j)) ∧
      RsvZero (entriesOf L (pathOf L j))

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
    have := hT.len; rw [T4.capPh_pos.2.2.2] at this; omega
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
  obtain ⟨j, hT, ⟨hkC, hvk, hvkL, hc⟩, -⟩ := hR.node κ L c π hb hk hrun
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

end G6_FRSoundness4XLaws
