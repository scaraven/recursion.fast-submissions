-- New for `flock-recursive` (BLUEPRINT A.10, §5.1–§5.2; stage S-G9).
import FRSoundnessFrZM

/-!
# The front's doom `DF`, its checks `RejF`, the node's L hypothesis

* **`SLeaf`**: the leaf statement (ruling S-G7): `ShHoldsL` on the chain and `ZHolds zlmFR`.
* **`okF oLc`**: RS0's four bindings with Lc's (claim 2) a parameter `oLc` (blueprint 3.16, INT-5);
  `okF_pendZ`, `okF_pendS`, `okF_pendE` (the pending Z, S, E claims fail their bindings).
* **`NodeLF`**: what the node's L (L3, L3β, the Lc claim) must supply, as one hypothesis; the
  leaf's binding is `oLc ↔ v_β` (`NodeLF.leaf`), so the leaf's `PendLc` fails it (`okF_pendLc`).
* **`DF`**: the 26 phase dooms, `DF k = Bg_k ∨ U_k` (journal §3): `DF 2 = far₀ ∨ ¬ Stmt`, the
  background carrying the not-yet-reduced statement parts and the pending claims to RS0 (`DF 23 =
  DRS0`); **`stmt_split`** (`¬ Stmt` is one of the parts) and **`dPend_of`** (E4 end's doom is
  `DPend` at 312).
* **`RejF`**: the asserted checks, `rejF_ok`.
-/

namespace FR.Snd
open RecursionFast FR.Merkle Finset

set_option linter.constructorNameAsVariable false

/-! ## The leaf statement -/

/-- **The leaf statement** (ruling S-G7): consecutive chain blocks link and the boundary digests
are the header's and statement's (`ShHoldsL`), and Z's R1CS holds (`ZHolds zlmFR`). -/
def SLeaf (κ : Kind) (L es : Log) : Prop :=
  ShHoldsL (nbS κ) (zNode κ L es) (sbL κ es) (hbL κ es) ∧ ZHolds zlmFR L es

theorem truthS_same {L es L' es' : Log} {p : ℕ} (h : Same L es L' es' p) (hp : 3 ≤ p) :
    truthS L es ↔ truthS L' es' := by
  have hk := h.kind (by omega)
  have hb : ∀ κ, bndL κ es = bndL κ es' := fun κ => bndL_congr h.1 (by omega) κ
  have hs : ∀ κ, sbL κ es = sbL κ es' := fun κ => by funext σ; simp only [sbL, hb]
  have ht : ∀ κ, hbL κ es = hbL κ es' := fun κ => by funext σ; simp only [hbL, hb]
  simp only [truthS, truthSK, truthS1N, hk, zNode_same h hp, hs, ht]

theorem sLeaf_reads (κ : Kind) : Reads 3 (SLeaf κ) := fun L es L' es' h1 h2 h => by
  have hb : bndL κ es = bndL κ es' := bndL_congr h.1 (by omega) κ
  have hs : sbL κ es = sbL κ es' := by funext σ; simp only [sbL, hb]
  have ht : hbL κ es = hbL κ es' := by funext σ; simp only [hbL, hb]
  simp only [SLeaf, zNode_same h le_rfl, hs, ht, zHolds_reads L es L' es' h1 h2 h]

/-! ## RS0's bindings with Lc's a parameter -/

/-- **RS0's bindings**: Z's `oZ`, Lc's the parameter `oLc`, S's `oSh`, E's `okE`. -/
def okF (oLc : Kind → Log → F → Prop) (κ : Kind) (es : Log) (j : ℕ) (v : F) : Prop :=
  match j with
  | 0 => oZ κ es v
  | 1 => oLc κ es v
  | 2 => oSh κ es v
  | _ => okE es v

theorem okF_reads {oLc : Kind → Log → F → Prop}
    (hLc : ∀ κ es es', Agree es es' 312 → oLc κ es = oLc κ es') : OkReads (okF oLc) := by
  intro κ es es' h
  have he : okE es = okE es' := by
    funext v; simp only [okE, msgAt_congr h (show 311 < 312 by norm_num)]
  funext j v
  rcases j with _ | _ | _ | j
  · simp only [okF, oZ_reads κ es es' h]
  · simp only [okF, hLc κ es es' h]
  · simp only [okF, oSh_reads κ es es' h]
  · simp only [okF, he]

theorem rsPts_one (κ : Kind) (es : Log) : ((1 : Fin 4) : ℕ) < (rsPtsL κ es).length := by
  rw [rsPtsL_length]; split_ifs <;> decide

section Bind
variable {oLc : Kind → Log → F → Prop} {L es : Log}

theorem okF_pendZ (h : PendZ L es) : PendBad (okF oLc) L es :=
  ⟨0, by rw [rsPtsL_length]; split_ifs <;> decide, fun ho => h.2 (by
    have ho' : trueL (kindOf es) L es 0 = pzStar es := ho
    rw [← trueL_zero, ho'])⟩

theorem okF_pendS (h : D2S L es) (hl : 170 ≤ es.length) : PendBad (okF oLc) L es :=
  ⟨2, by rw [rsPtsL_length]; split_ifs <;> decide, endS h hl⟩

theorem okF_pendE (h : PendE L es) : PendBad (okF oLc) L es := by
  obtain ⟨hn, -, hne⟩ := h
  have hn' : (kindOf es).isNode = true := hn
  refine ⟨3, by rw [rsPtsL_length, if_pos hn']; decide, ?_⟩
  show ¬ okE es (trueL (kindOf es) L es 3)
  rw [trueL_three hn']; exact hne

/-- On a leaf, the pending Lc claim `v_β` is not RS claim 2's true value. -/
theorem pendLc_ne (h : PendLc zlmFR L es) : trueL (kindOf es) L es 1 ≠ vBetaL es := by
  obtain ⟨-, hn, hne⟩ := h
  intro ho
  have ht : ∑ i : Fin 8, fAt es 98 0 ^ i.val * tL zlmFR L es i = zfL zlmFR L es 0 := by
    rw [Fin.sum_univ_succ]; simp [tL]
  exact hne (by rw [ht, zfL_leaf hn, ho])

/-! ## The node's L: one hypothesis -/

open Classical in
/-- **What the node's L must supply** (L3 at 97, L3β at 98, the Lc claim into RS0), with Lc's
binding `oLc` (blueprint 3.16, INT-5): its checks `RejN` (a node's, from 98), L3's doom `L3N`,
the pending claim `PendN`; on a leaf `oLc` is the binding `v = v_β` of `finLc` (iii). The
accepted run's part is `NodeL.front` (`FRSoundnessFrK`). -/
structure NodeLF (oLc : Kind → Log → F → Prop) (RejN L3N PendN : Log → Log → Prop) : Prop where
  rej : RejOK RejN
  rejReads : Reads 98 RejN
  rejLen : ∀ L es : Log, RejN L es → 98 ≤ es.length
  l3Reads : Reads 98 L3N
  pendReads : Reads 99 PendN
  habs : ∀ (L es : Log) (x : ByteArray × Digest), es.length = 97 → (kindOf es).isNode = true →
    D2L zlmFR L es → RejN L (es ++ [x]) ∨ L3N L (es ++ [x])
  single : ∀ L es : Log, es.length = 98 →
    (univ.filter fun a => L3N L es ∧ ¬ PendN L (ext1 es a)).card ≤ 8 * 2 ^ 128
  pend : ∀ L es : Log, PendN L es → ¬ oLc (kindOf es) es (trueL (kindOf es) L es 1)
  okReads : ∀ κ es es', Agree es es' 312 → oLc κ es = oLc κ es'
  leaf : ∀ (es : Log) (v : F), (kindOf es).isNode = false → (oLc (kindOf es) es v ↔ v = vBetaL es)

variable {RejN L3N PendN : Log → Log → Prop}

theorem okF_pendLc (hN : NodeLF oLc RejN L3N PendN) (h : PendLc zlmFR L es) :
    PendBad (okF oLc) L es :=
  ⟨1, rsPts_one _ _, fun ho => pendLc_ne h ((hN.leaf es _ h.2.1).mp ho)⟩

theorem okF_pendN (hN : NodeLF oLc RejN L3N PendN) (h : PendN L es) : PendBad (okF oLc) L es :=
  ⟨1, rsPts_one _ _, hN.pend L es h⟩

end Bind

/-! ## The background parts -/

/-- The level-0 word is far. -/
def far0 (L es : Log) : Prop := farL (kindOf es) L es 0
/-- A public cell is false. -/
def nPub (L es : Log) : Prop := ¬ PubOK (kindOf es) L es
/-- S's truth fails. -/
def nS (L es : Log) : Prop := ¬ truthS L es
/-- L's rows fail (a node). -/
def nLr (L es : Log) : Prop := RowsBad Layout.lRows 15 23 lrOn L es
/-- The M rows fail (a node). -/
def nE (fin : Finals) (L es : Log) : Prop := RowsBad (Layout.nodeRows fin) 21 23 lrOn L es

section Doom
variable (fin : Finals) (L3N PendN : Log → Log → Prop)

/-- Z1's background: far, a public cell, Lr's or E's rows, S's truth. -/
def bgZ (L es : Log) : Prop := (far0 L es ∨ nPub L es ∨ nLr L es ∨ nE fin L es) ∨ nS L es
/-- From Z3 on: and the pending c-claim. -/
def bg5 (L es : Log) : Prop := bgZ fin L es ∨ PendZ L es
/-- At L3β: S's truth leaves the background (S1 reduces it); the pending Lc claims join. -/
def bg10 (L es : Log) : Prop :=
  (far0 L es ∨ nPub L es ∨ nLr L es ∨ nE fin L es) ∨ PendZ L es ∨ PendLc zlmFR L es ∨ PendN L es
/-- From E3 on: far, a public cell and the four pending claims. -/
def bg20 (L es : Log) : Prop :=
  far0 L es ∨ nPub L es ∨ PendZ L es ∨ PendLc zlmFR L es ∨ PendN L es ∨ D2S L es
/-- S2 … Lr end: and E's rows. -/
def bg12 (L es : Log) : Prop := bg20 PendN L es ∨ nE fin L es
/-- Lr3 … E end: and Lr's pending batch. -/
def bg16 (L es : Log) : Prop := bg20 PendN L es ∨ BatBad Layout.lRows 15 23 lrOn 178 L es

/-- Lr2's outer rounds' doom. -/
abbrev D3Lr : Log → Log → Prop :=
  D3 178 (fun _ _ => 0) (nr3 15 lrOn) outerExpr (T3 Layout.lRows 15 23 lrOn 169)
/-- E2's outer rounds' doom. -/
abbrev D3E : Log → Log → Prop :=
  D3 221 (fun _ _ => 0) (nr3 21 lrOn) outerExpr (T3 (Layout.nodeRows fin) 21 23 lrOn 209)

/-- Phase 2's doom (`cap₀`). -/
def D2F (L es : Log) : Prop := far0 L es ∨ ¬ Stmt fin SLeaf L es
/-- L3β's doom (S1's entry). -/
def D10F (L es : Log) : Prop := bg10 fin PendN L es ∨ nS L es
/-- S2's doom (Lr1's entry). -/
def D12F (L es : Log) : Prop := bg12 fin PendN L es ∨ nLr L es
/-- Lr3's doom (E1's entry). -/
def D16F (L es : Log) : Prop := bg16 PendN L es ∨ nE fin L es

/-- **The front's phase dooms** (journal §3). -/
def DF : ℕ → Log → Log → Prop
  | 2 => D2F fin
  | 3 => msD (D2F fin) (fun L es => bgZ fin L es ∨ ZEnd zlmFR L es) 2 10
  | 4 => fun L es => bgZ fin L es ∨ Z2D zlmFR L es
  | 5 => fun L es => bg5 fin L es ∨ D3Z zlmFR L es
  | 6 => fun L es => bg5 fin L es ∨ ZendBad zlmFR L es
  | 7 => fun L es => bg5 fin L es ∨ L1Bad zlmFR L es
  | 8 => fun L es => bg5 fin L es ∨ D2L zlmFR L es
  | 9 => fun L es => bg5 fin L es ∨ (L3Bad zlmFR L es ∨ L3N L es)
  | 10 => D10F fin PendN
  | 11 => msD (D10F fin PendN) (fun L es => bg10 fin PendN L es ∨ S2Bad L es) 98 15
  | 12 => D12F fin PendN
  | 13 => msD (D12F fin PendN)
      (fun L es => bg12 fin PendN L es ∨ ZCw Layout.lRows 15 23 lrOn 169 L es) 169 8
  | 14 => fun L es => bg12 fin PendN L es ∨ D3Lr L es
  | 15 => fun L es => bg12 fin PendN L es ∨ EndBad Layout.lRows 15 23 lrOn 178 L es
  | 16 => D16F fin PendN
  | 17 => msD (D16F fin PendN)
      (fun L es => bg16 PendN L es ∨ ZCw (Layout.nodeRows fin) 21 23 lrOn 209 L es) 209 11
  | 18 => fun L es => bg16 PendN L es ∨ D3E fin L es
  | 19 => fun L es => bg16 PendN L es ∨ EndBad (Layout.nodeRows fin) 21 23 lrOn 221 L es
  | 20 => fun L es => bg20 PendN L es ∨ BatBadE (Layout.nodeRows fin) L es
  | 21 => fun L es => bg20 PendN L es ∨ D4E (Layout.nodeRows fin) L es
  | 22 => fun L es => bg20 PendN L es ∨ PendE L es
  | 23 => DRS0
  | 24 => msD DRS0 DRS1 312 4
  | 25 => DB
  | _ => fun _ _ => False

/-! ## `¬ Stmt` is one of the parts; E4 end's doom is `DPend` -/

variable {fin L3N PendN} {oLc : Kind → Log → F → Prop} {RejN : Log → Log → Prop} {L es : Log}

/-- **`¬ Stmt` splits into the parts the phases reduce** (a node's E part needs the M rows to fit
their `2^21 × 2^23` matrices, `truthE_iff`). -/
theorem stmt_split (hfit : RowsFit (Layout.nodeRows fin) 21 23) (h : ¬ Stmt fin SLeaf L es) :
    ¬ ZHolds zlmFR L es ∨ nS L es ∨ nLr L es ∨ nE fin L es ∨ nPub L es := by
  unfold Stmt at h
  split_ifs at h with hn
  · have hN : kindOf es = .N30 := by
      rcases hk : kindOf es with _ | _ | _ <;> simp_all [Kind.isNode]
    simp only [StmtN, not_and_or] at h
    rcases h with h | h | h | h | h
    · exact Or.inl ((zHolds_iff_truthZN hN).not.mpr h)
    · refine Or.inr (Or.inl ?_)
      simp only [nS, truthS, truthSK, if_pos hn]; exact h
    · exact Or.inr (Or.inr (Or.inl ⟨by simp [lrOn, hn], fun hs =>
        h ((sat_rowMat_iff _ lRows_fit _).mp hs)⟩))
    · exact Or.inr (Or.inr (Or.inr (Or.inl ⟨by simp [lrOn, hn], fun hs =>
        h ((truthE_iff fin hfit _ L es).mpr hs)⟩)))
    · exact Or.inr (Or.inr (Or.inr (Or.inr h)))
  · simp only [SLeaf, not_and_or] at h
    rcases h with h | h
    · refine Or.inr (Or.inl ?_)
      simp only [nS, truthS, truthSK, if_neg hn]; exact h
    · exact Or.inl h

/-- **E4 end's doom is `DPend` at RS0** (the four pending-claim bridges). -/
theorem dPend_of (hN : NodeLF oLc RejN L3N PendN) (hl : 170 ≤ es.length)
    (h : DF fin L3N PendN 22 L es) : DPend (okF oLc) L es := by
  simp only [DF, bg20] at h
  rcases h with (h | h | h | h | h | h) | h
  · exact Or.inl h
  · exact Or.inr (Or.inl h)
  · exact Or.inr (Or.inr (okF_pendZ h))
  · exact Or.inr (Or.inr (okF_pendLc hN h))
  · exact Or.inr (Or.inr (okF_pendN hN h))
  · exact Or.inr (Or.inr (okF_pendS h hl))
  · exact Or.inr (Or.inr (okF_pendE h))

/-! ## The asserted checks -/

end Doom

variable (fin : Finals) (oLc : Kind → Log → F → Prop) (RejN : Log → Log → Prop)

/-- **`finE` (iv)'s failure** (`RejE4`) is a check from 312. -/
theorem rejE4_ok (hp : fsItems[311]? ≠ some .squeeze) : RejOK (RejE4 (Layout.nodeRows fin)) := by
  have h := rejOK_at (p := 311) (P := fun L es => lrOn (kindOf es) = true ∧
      clR2 265 16 readF (fun d => chF d 0) c4E L es 23 ≠
        mle (wE4 (Layout.nodeRows fin) es) (ptOf 23 (rE4 es)) * readF (msgAt es 311) 0)
    (fun L es L' es' h1 h2 hS => by
      have hk := hS.kind (by norm_num)
      beta_reduce
      rw [hk, clR2_same (b := 265) (wd := 16) (rd := readF) (ch := fun d => chF d 0)
        (c0 := c4E) (L := L) (L' := L') (c4E_agree hS.1 (by norm_num)) (l := 23)
        (hS.1.mono (by norm_num)), wE_congr (hS.1.mono (by norm_num)),
        rE4_agree hS.1 (by norm_num), msgAt_congr hS.1 (show 311 < 312 by norm_num)]) hp
  exact h

/-- **The front's asserted checks**: Z's, L2's, the leaf's `finLc` (ii), S2's, Lr's and E's end
checks, E4's rounds and `finE` (iv), RS0's bindings, and the node's L checks. -/
def RejF (L es : Log) : Prop :=
  RejZ zlmFR L es ∨ RejL2 L es ∨ RejLc2 zlmFR L es ∨ RejS2 L es ∨
    RejEnd 15 lrOn 169 178 L es ∨ RejEnd 21 lrOn 209 221 L es ∨ RejInE L es ∨
    RejE4 (Layout.nodeRows fin) L es ∨ RejRS (okF oLc) L es ∨ RejN L es

/-! ## Controls -/

section Controls
variable {fin : Finals} {oLc : Kind → Log → F → Prop} {RejN L3N PendN : Log → Log → Prop}
  {L es : Log}

/-- Control (positive): a leaf's statement is exactly S's truth and Z's (`Stmt`'s leaf part). -/
theorem stmt_leaf_iff (hn : (kindOf es).isNode = false) :
    Stmt fin SLeaf L es ↔ truthS L es ∧ ZHolds zlmFR L es := by
  simp only [Stmt, hn, SLeaf, truthS, truthSK, Bool.false_eq_true, ite_false]

/-- Control (negative): a leaf whose Z rows fail does not meet its statement. -/
theorem not_stmt_leaf_of (hn : (kindOf es).isNode = false) (hz : ¬ ZHolds zlmFR L es) :
    ¬ Stmt fin SLeaf L es := fun h => hz ((stmt_leaf_iff hn).mp h).2

/-- Control (positive): claim 2's binding is the parameter, claim 1's is `P^z*(λ)`. -/
theorem okF_one_iff (κ : Kind) (v : F) : okF oLc κ es 1 v ↔ oLc κ es v := Iff.rfl
theorem okF_zero_iff (κ : Kind) (v : F) : okF oLc κ es 0 v ↔ v = pzStar es := Iff.rfl

/-- Control (negative): claim 4's binding refuses any value but E4 end's. -/
theorem not_okF_three (κ : Kind) {v : F} (h : v ≠ readF (msgAt es 311) 0) :
    ¬ okF oLc κ es 3 v := h

theorem kindOf_nil : kindOf [] = .L32 := rfl

open Classical in
/-- Control (positive, satisfiability): a node L with no checks, whose L3 doom is "a node past
97" and whose pending claim is "a node past 98", with a node binding that refuses everything,
meets `NodeLF` (the interface is not contradictory). -/
theorem nodeLF_ex : NodeLF (fun κ es v => κ.isNode = false ∧ v = vBetaL es) (fun _ _ => False)
    (fun _ es => (kindOf es).isNode = true ∧ 97 < es.length)
    (fun _ es => (kindOf es).isNode = true ∧ 98 < es.length) where
  rej := rejOK_false
  rejReads := reads_false 98
  rejLen _ _ h := h.elim
  l3Reads L es L' es' h1 h2 h := by
    simp only [h.kind (by norm_num)]; exact and_congr_right fun _ => ⟨fun _ => by omega,
      fun _ => by omega⟩
  pendReads L es L' es' h1 h2 h := by
    simp only [h.kind (by norm_num)]; exact and_congr_right fun _ => ⟨fun _ => by omega,
      fun _ => by omega⟩
  habs L es x hl hn _ := Or.inr ⟨by rw [kindOf_append x (by omega)]; exact hn, by simp; omega⟩
  single L es hl := by
    refine le_trans (card_le_card (show _ ⊆ (∅ : Finset Digest) from fun a ha => ?_)) (by simp)
    simp only [mem_filter, mem_univ, true_and] at ha
    have hk : kindOf (ext1 es a) = kindOf es := kindOf_append _ (by omega)
    have hl' : 98 < (ext1 es a).length := by simp [ext1]; omega
    exact (ha.2 ⟨hk ▸ ha.1.1, hl'⟩).elim
  pend L es h ho := by rw [h.1] at ho; exact Bool.noConfusion ho.1
  okReads κ es es' h := by
    have hv : vBetaL es = vBetaL es' := by
      simp only [vBetaL, fAt_congr h (show 98 < 312 by norm_num),
        msgAt_congr h (show 97 < 312 by norm_num)]
    simp only [hv]
  leaf es v hn := by simp [hn]

/-- Control (negative): a binding that accepts everything is no `NodeLF` (on a leaf it must be
`v = v_β`). -/
theorem not_nodeLF_true : ¬ NodeLF (fun _ _ _ => True) RejN L3N PendN := fun h => by
  have := (h.leaf [] (vBetaL [] + 1) (by rw [kindOf_nil]; rfl)).mp trivial
  simp at this

/-- Control (positive): a far level-0 word dooms every phase from 2 to 22 (the background is
live). -/
theorem DF_of_far (h : far0 L es) : ∀ k, 2 ≤ k → k ≤ 22 → k ≠ 3 → k ≠ 11 → k ≠ 13 → k ≠ 17 →
    DF fin L3N PendN k L es := by
  intro k h1 h2 h3 h11 h13 h17
  interval_cases k <;> simp_all [DF, D2F, D10F, D12F, D16F, bgZ, bg5, bg10, bg12, bg16, bg20]

/-- Control (negative): B′'s doom fails on a close word with a true claim. -/
theorem not_DF25 (hnf : ¬ farL (kindOf es) L es 0)
    (hc : c₀L L es = trueSum e2 (lvT W₀L 0 L es) (nrP 0 (kindOf es))) :
    ¬ DF fin L3N PendN 25 L es := not_DB_true hnf hc

/-- Control (positive): the node's checks are `RejF`'s. -/
theorem rejF_of_rejN (h : RejN L es) : RejF fin oLc RejN L es :=
  Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))))

/-- Control (negative): no check of the verifier's fails before Zend's absorb is answered. -/
theorem not_rejF_short (hl : es.length < 68) : ¬ RejF fin oLc (fun _ _ => False) L es := by
  rintro (h | ⟨l, -, hl', -⟩ | h | ⟨l, -, hl', -⟩ | h | h | ⟨l, -, hl', -⟩ | h | h | h)
  · exact absurd h.1 (by omega)
  · omega
  · exact absurd h.1 (by omega)
  · omega
  · exact absurd h.2.1 (by omega)
  · exact absurd h.2.1 (by omega)
  · omega
  · exact absurd h.1 (by omega)
  · exact absurd h.1 (by omega)
  · exact h

end Controls

end FR.Snd
