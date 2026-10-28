-- New for `flock-recursive` (BLUEPRINT revision 4.1, A.10 S2; stage P4a pass 3 (P4c)).
import FRSoundness4P4aFin

/-!
# S2's obligations at `seq4` (positions 114 … 169), against T4's foundation

3.x's `FrS` S2 part over T4's `D2`, `Same`, `RejOK`, `Reads` and P4a's revision 4.1 tables:

* **`p4a_abs`**: Z's, L's and S's absorb positions are not squeezes (one `seq4` certificate).
* `wS_agree`, `TS_same4`, **`TS_local4`**, `TS_size4`: S2's tables read the log before 114 (a
  node's weight `wN` is assumed to, `WNLocal`).
* **`habs_S2_4`** (S1's final doom is S2's doom at its first absorb), **`single_S2_4`**
  (`≤ 2·2^128` per squeeze), `append_S2_4`, **`rejS2_ok4`** (`T4.RejOK RejS2`),
  **`D2S_reads4`** (`T4.Reads 170`).
* **`endS4`**: at S2's end its doom is the Sh binding `oSh4` failing at `ẑ(r_blk, r_pos)` (a
  node's weight value `wNS` is assumed to be its weight's extension).
-/

namespace FR.Snd.P4a
open RecursionFast FR.Merkle Finset FR.Impl

set_option linter.constructorNameAsVariable false

/-! ## The front's absorb positions (a `seq4` certificate) -/

/-- Z's end (67), L2's rounds (69 + 2j), L3 (97) and S2's rounds (114 + 2j) are absorbs. -/
def absOKP4a : Bool :=
  ([67, 97] ++ (List.range 14).map (fun j => 69 + 2 * j) ++
    (List.range 28).map (fun j => 114 + 2 * j)).all fun p => fsItems4[p]? != some Item.squeeze

theorem absOKP4a_eq : absOKP4a = true := by
  rw [absOKP4a, fsItems4, Rev4.seq4_eq]; decide +kernel

theorem p4a_abs : fsItems4[67]? ≠ some .squeeze ∧ fsItems4[97]? ≠ some .squeeze ∧
    (∀ j < 14, fsItems4[69 + 2 * j]? ≠ some .squeeze) ∧
    ∀ j < 28, fsItems4[114 + 2 * j]? ≠ some .squeeze := by
  have h := absOKP4a_eq
  simp only [absOKP4a, List.all_eq_true, List.mem_append, List.mem_cons, List.mem_map,
    List.mem_range, bne_iff_ne, ne_eq] at h
  exact ⟨h _ (.inl (.inl (.inl rfl))), h _ (.inl (.inl (.inr (.inl rfl)))),
    fun j hj => h _ (.inl (.inr ⟨j, hj, rfl⟩)), fun j hj => h _ (.inr ⟨j, hj, rfl⟩)⟩

/-! ## S2's tables read before 114 -/

/-- **A node's S2 weight reads the log before 114** (S1's challenges; S-E's, a hypothesis). -/
def WNLocal (wN : CKind → Log → ℕ → ℕ → F) : Prop :=
  ∀ κ es es', Agree es es' 114 → wN κ es = wN κ es'

section S2
variable {wN : CKind → Log → ℕ → ℕ → F} {zw : Wit} (hw : WNLocal wN) (hz : ZwSame zw)
variable {L es L' es' : Log} {p : ℕ}

include hw in
theorem wS_agree (h : Agree es es' p) (hp : 114 ≤ p) (κ : CKind) : wS wN κ es = wS wN κ es' := by
  obtain ⟨h1, h2, h3⟩ := s1_congr4 h hp κ
  funext y q
  simp only [wS, h1, h2, h3, lastL_congr h (by omega), hw κ es es' (h.mono hp)]

include hw hz in
theorem TS_same4 (h : T4.Same L es L' es' p) (hp : 114 ≤ p) : TS wN zw L es = TS wN zw L' es' := by
  have hk := h.kind (by omega)
  rw [TS, TS, hk, wS_agree hw h.1 hp, zNodeC_same hz h (by omega)]

include hw hz in
theorem TS_local4 : TruthLocal2 114 c0SL (TS wN zw) := fun L es es' h =>
  ⟨TS_same4 hw hz (T4.same_of_agree L h) le_rfl, c0S_agree4 h le_rfl⟩

theorem TS_size4 (L es : Log) : ∀ t ∈ TS wN zw L es, t.size = 2 ^ nrS (kindOfC es) := by
  simp [TS, nrS]

theorem nrS_le4 (κ : CKind) : nrS κ ≤ 28 := by have := nbC_le κ; unfold nrS; omega

include hw hz in
/-- **Into S2** (`habs` at 114): S1's final doom is S2's doom at its first absorb. -/
theorem habs_S2_4 (x : ByteArray × Digest) (hl : es.length = 114) (hb : S2Bad wN zw L es) :
    D2S wN zw L (es ++ [x]) := by
  have hS := T4.same_append L es [x]
  have hk : kindOfC (es ++ [x]) = kindOfC es := hS.kind (by omega)
  refine ⟨by simp; omega, ?_⟩
  have ha0 : T4.ans3 114 nrS (es ++ [x]) = 0 := by
    simp only [T4.ans3, List.length_append, List.length_singleton, hl]; simp
  rw [ha0]
  simp only [T4.Wrong2, clR2, rchs2, List.range_zero, List.map_nil, bindAll, Nat.sub_zero]
  rw [TS_same4 hw hz (hl ▸ hS) le_rfl, hk, c0SL, c0S_agree4 (hl ▸ hS).1 le_rfl]
  exact hb

include hw hz in
open Classical in
/-- **S2's squeezes** (A.10 S2: `2·2^128`). -/
theorem single_S2_4 (L es : Log)
    (hchk : ∀ j, es.length = 114 + 2 * j + 1 → j < nrS (kindOfC es) →
      Chk2 114 16 readF (fun d => chF d 0) c0SL L es j) :
    (univ.filter fun d => D2S wN zw L es ∧ ¬ D2S wN zw L (ext1 es d)).card ≤ 2 * 2 ^ 128 :=
  T4.D2_single (by omega) (TS_local4 hw hz) innerExpr_deg card_chF_fiber TS_size4 L es hchk

theorem chk_of_not_rejS2_4 (hr : ¬ RejS2 L es) (j : ℕ) (hj : es.length = 114 + 2 * j + 1)
    (hjn : j < nrS (kindOfC es)) : Chk2 114 16 readF (fun d => chF d 0) c0SL L es j := by
  by_contra hc; exact hr ⟨j, hjn, by omega, hc⟩

include hw hz in
/-- An S2 round's absorb keeps the doom. -/
theorem append_S2_4 (x : ByteArray × Digest) (hlen : 114 < es.length)
    (hc : (es.length - 114) % 2 = 0 ∨ nrS (kindOfC es) ≤ (es.length - 114) / 2) :
    D2S wN zw L (es ++ [x]) ↔ D2S wN zw L es :=
  T4.D2_append_iff (by omega) (TS_local4 hw hz) x hlen hc

end S2

/-! ## S2's round checks -/

section Rej
variable {L es L' es' : Log} {p : ℕ}

theorem chkS_same4 (h : T4.Same L es L' es' p) {j : ℕ} (hj : 114 + 2 * j < p) :
    Chk2 114 16 readF (fun d => chF d 0) c0SL L es j ↔
      Chk2 114 16 readF (fun d => chF d 0) c0SL L' es' j := by
  have hg : g2At 114 16 readF es j = g2At 114 16 readF es' j := by
    simp only [g2At, msgAt, h.1 (114 + 2 * j) hj]
  have hc0 : c0SL L es = c0SL L' es' := c0S_agree4 (h.1.mono (by omega)) (le_refl 114)
  have hc := clR2_same (b := 114) (wd := 16) (rd := readF) (ch := fun d => chF d 0)
    (c0 := c0SL) hc0 (l := j) (h.1.mono (by omega))
  simp only [Chk2, hg, hc]

theorem rejS2_mono4 (x : ByteArray × Digest) (h : RejS2 L es) : RejS2 L (es ++ [x]) := by
  obtain ⟨j, hj, hlt, hc⟩ := h
  have hS := T4.same_append L es [x]
  refine ⟨j, by rw [hS.kind (by omega)]; exact hj, by simp; omega, fun h' => hc ?_⟩
  exact (chkS_same4 hS (by omega)).mp h'

/-- **`T4.RejOK` for S2's round checks.** -/
theorem rejS2_ok4 : T4.RejOK RejS2 where
  mono L es x := rejS2_mono4 x
  sq L es x hit := by
    refine ⟨fun ⟨j, hj, hlt, hc⟩ => ?_, rejS2_mono4 x⟩
    simp only [List.length_append, List.length_singleton] at hlt
    have hS := T4.same_append L es [x]
    rw [hS.kind (by omega)] at hj
    by_cases he : 114 + 2 * j = es.length
    · exact absurd (he ▸ hit) (p4a_abs.2.2.2 j (lt_of_lt_of_le hj (nrS_le4 _)))
    exact ⟨j, hj, by omega, fun h' => hc ((chkS_same4 hS (by omega)).mpr h')⟩
  stab L i hb hci X hX := by
    have hS := T4.same_stabX hb hci hX
    by_cases h0 : X.length = 0
    · constructor <;> rintro ⟨j, -, hlt, -⟩ <;> omega
    unfold RejS2
    rw [hS.kind (by omega)]
    exact exists_congr fun j => and_congr_right fun _ => and_congr_right fun _ =>
      not_congr (chkS_same4 hS (by omega))

end Rej

section Reads
variable {wN : CKind → Log → ℕ → ℕ → F} {zw : Wit} (hw : WNLocal wN) (hz : ZwSame zw)

include hw hz in
/-- **Once every S2 round is answered, S2's doom reads before 170.** -/
theorem D2S_reads4 : T4.Reads 170 (D2S wN zw) := fun L es L' es' h1 h2 h => by
  have hk := h.kind (by omega)
  have hans : ∀ Y : Log, 170 ≤ Y.length → T4.ans3 114 nrS Y = nrS (kindOfC Y) :=
    fun Y hY => by have := nrS_le4 (kindOfC Y); unfold T4.ans3; simp; omega
  unfold D2S T4.D2 T4.Wrong2
  rw [hans es (by omega), hans es' (by omega), hk, TS_same4 hw hz h (by omega),
    clR2_same (c0 := c0SL) (L' := L') (es' := es') (c0S_agree4 h.1 (by omega))
      (h.1.mono (by have := nrS_le4 (kindOfC es'); omega)),
    rchs2_congr (h.1.mono (by have := nrS_le4 (kindOfC es'); omega))]
  exact and_congr_left fun _ => ⟨fun _ => by omega, fun _ => by omega⟩

end Reads

/-! ## S2's end: the Sh binding -/

theorem rchsS_pts4 (κ : CKind) (es : Log) :
    ptOf (nbC κ) (rchs2 114 (fun d => chF d 0) es (nbC κ + 10)) = ptOf (nbC κ) (rbL κ es) ∧
      ptOf 10 ((rchs2 114 (fun d => chF d 0) es (nbC κ + 10)).drop (nbC κ)) =
        ptOf 10 (rpL κ es) := by
  refine ⟨funext fun l => ?_, funext fun l => ?_⟩
  · have := l.isLt
    simp [ptOf, rchs2, rbL, List.getD_eq_getElem?_getD, this, show l.val < nbC κ + 10 by omega]
    rfl
  · have := l.isLt
    simp [ptOf, rchs2, rpL, List.getD_eq_getElem?_getD, this]
    rfl

/-- `ẑ` at S2's point `(r_blk, r_pos)` over the block positions `< 2^10` (RS claim 3's true
value; P4b's `trueL4` at claim 3 is this, 3.x's `trueL_two`). -/
def zS2 (zw : Wit) (L es : Log) : F :=
  ∑ q ∈ range (2 ^ 10), ∑ y ∈ range (2 ^ nbC (kindOfC es)),
    eqAtR (ptOf (nbC (kindOfC es)) (rbL (kindOfC es) es)) y *
      eqAtR (ptOf 10 (rpL (kindOfC es) es)) q * zNodeC zw (kindOfC es) L es y q

/-- **At S2's end its doom is the Sh binding failing at `ẑ`** (a segment's `L` among its blocks; a
node's weight value is its weight's extension). -/
theorem endS4 {wN : CKind → Log → ℕ → ℕ → F} {zw : Wit} {wNS : CKind → Log → F} {L es : Log}
    (hNS : (kindOfC es).isNode = true → wNS (kindOfC es) es =
      ∑ q ∈ range (2 ^ 10), ∑ y ∈ range (2 ^ nbC (kindOfC es)),
        eqAtR (ptOf (nbC (kindOfC es)) (rbL (kindOfC es) es)) y *
          eqAtR (ptOf 10 (rpL (kindOfC es) es)) q * wN (kindOfC es) es y q)
    (hL : (kindOfC es).isNode = false → lastL es < 2 ^ nbC (kindOfC es))
    (h : D2S wN zw L es) (hl : 170 ≤ es.length) : ¬ oSh4 wNS (kindOfC es) es (zS2 zw L es) := by
  obtain ⟨-, hw⟩ := h
  have ha : T4.ans3 114 nrS es = nrS (kindOfC es) := by
    have := nrS_le4 (kindOfC es); unfold T4.ans3; simp; omega
  rw [ha] at hw
  unfold T4.Wrong2 at hw
  rw [Nat.sub_self, trueSum_bindAll' _ _ _ (by simp [rchs2]) (TS_size4 L es), innerExpr_eval2,
    TS, arrGetD_pair0, arrGetD_pair1, nrS, mle_tab, mle_tab,
    (rchsS_pts4 _ es).1, (rchsS_pts4 _ es).2] at hw
  intro hok
  apply hw
  have hW : wSumL4 wNS (kindOfC es) es = ∑ q ∈ range (2 ^ 10), ∑ y ∈ range (2 ^ nbC (kindOfC es)),
      eqAtR (ptOf (nbC (kindOfC es)) (rbL (kindOfC es) es)) y *
        eqAtR (ptOf 10 (rpL (kindOfC es) es)) q * wS wN (kindOfC es) es y q := by
    unfold wSumL4
    cases hn : (kindOfC es).isNode
    · simp only [Bool.false_eq_true, if_false]; exact wSumSeg_eq wN hn (hL hn)
    · simp only [if_true]; rw [hNS hn]
      simp only [wS, hn, if_true]
  rw [oSh4, claimSL4, hW, zS2] at hok
  rw [show clR2 114 16 readF (fun d => chF d 0) c0SL L es (nbC (kindOfC es) + 10) =
    claimSL4 (kindOfC es) es from clR2_same rfl (fun _ _ => rfl), claimSL4]
  exact hok

end FR.Snd.P4a
