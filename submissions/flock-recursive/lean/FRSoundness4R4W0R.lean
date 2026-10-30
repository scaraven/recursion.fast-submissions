-- G6: this module also holds the former modules `FRSoundness4R4Full`, `FRSoundness4R4Wt` (one section each, in import order).
import FRSoundness4R4PfFin

section G6_FRSoundness4R4Full

-- New for `flock-recursive` (BLUEPRINT revision 4.1, A.9, A.10; track R4h): the assembly of
-- `FinRest4` and T4's `AcceptTail` from an accepted run, per kind.

/-!
# `FinRest4` and `AcceptTail` from an accepted run, per kind

**`finRest4_full`**: on an accepted run's fields, `FinRest4` holds with `start`, `cols`, `link`
(R4g), `pf0`, `enc` (`FRSoundness4R4P4`, the zero tail from `finPf`'s tail flag) and `fin`
(`FRSoundness4R4PfFin`) proved; the hypotheses left are the op parameters (`phiRS`, `tensorW` at
their specs), the program's table facts (`FinTabs4`: discharged for every kind by `finTabs4_seg`,
`finTabs4_node`) and **`hW`**: `finPf`'s `Ŵ₄(P₄)` (`wV4`, its level steps from `Ŵ₀(P₀)`) is
`wHatL W₀ L es 4`.

**`acceptTail4_seg`**, **`acceptTail4_node`**: an accepted run of a kind's program gives
`T4.AcceptTail RejF W₀ c₀L4 L j`, given `¬ RejF` on accepted runs and `hW` on their fields.
-/

namespace FR.Snd.R4
open RecursionFast Rev4 Finset

/-- **The finals' table facts `finPf` needs** at `P` for the program kind `κ` whose chain has kind
`κc`. -/
structure FinTabs4 (P : FinP) (κ : Kind) (κc : CKind) : Prop where
  S : P.S = seq4
  ck : P.ck = true
  nc : 0 < P.nc
  nf : 0 < P.fams.length
  ix : ∀ j ∈ P.kv.ptIx κ, j < 8 + 8 * P.fams.length + P.e4s.length
  pad : (P.kv.selA κ = true ∧ κc.m = 32) ∨ (P.kv.selA κ = false ∧ P.fams.getD (famI P κ) 0 = κc.m)
  km : P.kv.m κ = κc.m
  tl : κc.m < 32 → κc.m ∈ P.tails
  node : P.kv.node κ = κc.isNode
  /-- The program's reserve is the kind's (revision 4.4.2: 60 cells on `N2`/`N4`, none else). -/
  rsv : P4b.nRsv κc = if (P.rsvOps && P.rsv) = true then rsvN else 0

theorem finTabs4_seg (σ : SegKind) (κ : Kind) : FinTabs4 (segFinP σ) κ (.seg σ) := by
  cases σ <;> refine ⟨rfl, rfl, ?_, ?_, ?_, ?_, rfl, ?_, rfl, rfl⟩ <;>
    simp (config := { decide := true }) [segFinP, kvOf, segFams, famI, selI, seq4_eq, SegKind.m, CKind.m]

theorem finTabs4_node (ν : NodeKind) (cells : List ℕ) (κ : Kind) : FinTabs4 (nodeFinP ν cells) κ (.node ν) := by
  cases ν <;> refine ⟨rfl, rfl, ?_, ?_, ?_, ?_, rfl, ?_, rfl, rfl⟩ <;>
    simp (config := { decide := true }) [nodeFinP, kvOf, nodeFams, nodeE4s, famI, selI, seq4_eq, NodeKind.m, CKind.m]

section Acc
variable {impl : OpImpl} {p : KindP} {inp : Input} {tr : Trace} {y : List Val × List Bool × Trace}
  {P : FinP} {zh : List Reg} {Rs : ℕ → Array Val} {Ex : ℕ → Array (List Reg)}

/-- **`FinRest4` on the fields** with every field proved; `hW` (`Ŵ₄(P₄)` at the spec) left. -/
theorem finRest4_full (hphi : ∀ r a, r.size = 7 → impl.phiRS r a = Impl.phiRSS r a)
    (ht : ∀ j r, impl.tensorW j r = Impl.tensorWS j r)
    (hF : Fields4 impl p inp tr P y zh Rs Ex) (hT : FinTabs4 P p.tix (kindOfC (fsOf tr (itemsOf seq4))))
    (hm : p.d.m = (kindOfC (fsOf tr (itemsOf seq4))).m) {L : Log} (hb : ¬ Bad L) (hin : ∀ e ∈ tr, e ∈ L)
    (hπ : inp.π.size = piSizeOf seq4) {W₀ : Log → Log → ℕ → K}
    (hW : wV4 impl p.tix ⟨(skeleton4 seq4 p).2.outs, zh, Ex 11⟩ (Rs 11) P =
      T4.wHatL W₀ L (fsOf tr (itemsOf seq4)) 4) :
    FinRest4 W₀ P4b.c₀L4 L (fsOf tr (itemsOf seq4)) (yv4 p (#[] ++ y.1.toArray)) := by
  have hix : ∀ j ∈ P.kv.ptIx p.tix, j < (gPfPts P ⟨(skeleton4 seq4 p).2.outs, zh, Ex 11⟩).length := by
    rw [gPfPts_length]; exact hT.ix
  exact finRest4_of_fields hphi hF hT.S hT.node hT.rsv hm hb hin hπ (pf04_of_fields hF _ L)
    (enc4_of_fields hF hT.S ht hb hin hm (hz_of_fields hF hT.S hT.ck hT.nc hT.nf hix hT.km hT.tl))
    (fin4_of_fields hF hT.S hT.ck hT.nc hT.nf hix hT.pad hW _)

end Acc

/-- **`AcceptTail` from an accepted segment run** (`acceptTail4_of_run` with `finRest4_full`). -/
theorem acceptTail4_seg {impl : OpImpl} {σ : SegKind} {inp : Input} {RejF : Log → Log → Prop}
    {W₀ : Log → Log → ℕ → K} {L : Log}
    (hphi : ∀ r a, r.size = 7 → impl.phiRS r a = Impl.phiRSS r a)
    (ht : ∀ j r, impl.tensorW j r = Impl.tensorWS j r)
    (hb : ¬ Bad L) (hπ : inp.π.size = piSizeOf seq4)
    (hrun : (runIR impl (gen4 seq4 (.ofSeg σ) (finOps4 (segFinP σ))) inp).runLog L = some true)
    (hR : ∀ tr, semIR impl (gen4 seq4 (.ofSeg σ) (finOps4 (segFinP σ))) inp tr = some true → (∀ e ∈ tr, e ∈ L) →
      ¬ RejF L (fsOf tr (itemsOf seq4)))
    (hW : ∀ tr y zh Rs Ex, semIR impl (gen4 seq4 (.ofSeg σ) (finOps4 (segFinP σ))) inp tr = some true →
      (∀ e ∈ tr, e ∈ L) → Fields4 impl (.ofSeg σ) inp tr (segFinP σ) y zh Rs Ex →
      wV4 impl (KindP.ofSeg σ).tix ⟨(skeleton4 seq4 (.ofSeg σ)).2.outs, zh, Ex 11⟩ (Rs 11) (segFinP σ) =
        T4.wHatL W₀ L (fsOf tr (itemsOf seq4)) 4) :
    ∃ j, T4.AcceptTail RejF W₀ P4b.c₀L4 L j := by
  refine acceptTail4_of_run _ hb hπ hrun fun tr hsem hin => ?_
  obtain ⟨y, zh, Rs, Ex, hF⟩ := fields4_of_accept (segFinP σ) hsem
  have hk := kindOfC_acc_seg hsem
  exact ⟨y, hF.sk, hR tr hsem hin, _, finRest4_full hphi ht hF (by rw [hk]; exact finTabs4_seg σ _)
    (dm_seg4 hF.sk) hb hin hπ (hW tr y zh Rs Ex hsem hin hF)⟩

/-- **`AcceptTail` from an accepted node run.** -/
theorem acceptTail4_node {impl : OpImpl} {ν : NodeKind} {cells : List ℕ} {inp : Input}
    {RejF : Log → Log → Prop} {W₀ : Log → Log → ℕ → K} {L : Log}
    (hphi : ∀ r a, r.size = 7 → impl.phiRS r a = Impl.phiRSS r a)
    (ht : ∀ j r, impl.tensorW j r = Impl.tensorWS j r)
    (hb : ¬ Bad L) (hπ : inp.π.size = piSizeOf seq4)
    (hrun : (runIR impl (gen4 seq4 (.ofNode ν) (finOps4 (nodeFinP ν cells))) inp).runLog L = some true)
    (hR : ∀ tr, semIR impl (gen4 seq4 (.ofNode ν) (finOps4 (nodeFinP ν cells))) inp tr = some true →
      (∀ e ∈ tr, e ∈ L) → ¬ RejF L (fsOf tr (itemsOf seq4)))
    (hW : ∀ tr y zh Rs Ex, semIR impl (gen4 seq4 (.ofNode ν) (finOps4 (nodeFinP ν cells))) inp tr = some true →
      (∀ e ∈ tr, e ∈ L) → Fields4 impl (.ofNode ν) inp tr (nodeFinP ν cells) y zh Rs Ex →
      wV4 impl (KindP.ofNode ν).tix ⟨(skeleton4 seq4 (.ofNode ν)).2.outs, zh, Ex 11⟩ (Rs 11) (nodeFinP ν cells) =
        T4.wHatL W₀ L (fsOf tr (itemsOf seq4)) 4) :
    ∃ j, T4.AcceptTail RejF W₀ P4b.c₀L4 L j := by
  refine acceptTail4_of_run _ hb hπ hrun fun tr hsem hin => ?_
  obtain ⟨y, zh, Rs, Ex, hF⟩ := fields4_of_accept (nodeFinP ν cells) hsem
  have hk := kindOfC_acc_node hsem
  exact ⟨y, hF.sk, hR tr hsem hin, _, finRest4_full hphi ht hF (by rw [hk]; exact finTabs4_node ν cells _)
    (dm_node4 hF.sk) hb hin hπ (hW tr y zh Rs Ex hsem hin hF)⟩

/-! ## Controls -/

/-- (−) **The tables are the kind's**: `L30`'s pad family is not `m*`'s, and `L32`'s chain is not
`L30`'s (`FinTabs4` fails at the wrong chain kind). -/
theorem finTabs4_ctl : (segFinP .L30).kv.selA .L32 = false ∧ ¬ FinTabs4 (segFinP .L30) .L32 (.seg .L32) :=
  ⟨rfl, fun h => by have := h.km; revert this; decide⟩

/-- (+/−) **`selI`**: the last selected index, `0` when none is. -/
theorem selI_ctl : selI (fun i => decide (i = 1)) 1 = 1 ∧ selI (fun _ => false) 3 = 0 := ⟨rfl, rfl⟩

/-- (+/−) **`padF4`**: `m*`'s family has the empty pad; `m = 30` has two factors. -/
theorem padF4_ctl (sfv : ℕ → K) : padF4 sfv 7 32 = 1 ∧ padF4 sfv 7 30 = (1 + sfv 5) * (1 + sfv 6) := by
  simp [padF4, List.range_succ]

/-- (+/−) **`tailOk4`**: with no tails it holds; it is the `and` of the tails' gated checks. -/
theorem tailOk4_ctl (P : FinP) (κ : Kind) (inp : Input) (hP : P.tails = []) : tailOk4 P κ inp = true := by
  simp [tailOk4, hP]

end FR.Snd.R4

end G6_FRSoundness4R4Full

section G6_FRSoundness4R4Wt

-- New for `flock-recursive` (BLUEPRINT revision 4.1, A.9 `finPf`'s level steps; track R4i). The 3.x
-- templates are `FRSoundnessAccW` (`tail_vals`, `lvStepV_eq`, `wV_eq`).

/-!
# `finPf`'s level steps at revision 4.1: `wV4` from `w0V4`

* **The kind's points** (`slot_tl4`, `slot_p04`): slot `s` of `gPfPts` (`slotIx`) is the tail
  `gTailRegs seq4 fi m (s + 1)` (`s < 4`) or `gP0Regs seq4 fi m` (`s = 4`) at the family's `m`
  (`pfFamM`), which `FinTabs4.pad` makes the chain kind's.
* **`tail_vals4`**: the tail registers hold `T4.ptL es k (v + 1)`, `v < T4.mLog κ (k − 1)`
  (`tailList4_eq`: T4's `ptL` recursion; 3.x's `tail_vals`).
* **`lvStepV_eq4`**: with `tensorW` at the spec, `lvStepV … (k + 1) W` is `T4.wHatL`'s step.
* **`wV_eq4`**: `wV4 = T4.wHatL W₀ L es 4` once `w0V4 = T4.wHatL W₀ L es 0`.
-/

namespace FR.Snd.R4
open RecursionFast Rev4 Finset

/-! ## The kind's points in `gPfPts` -/

theorem getD_flatMap4 {α : Type} (f : ℕ → List α) (hf : ∀ m, (f m).length = 4) (d : α) :
    ∀ (l : List ℕ) (i s : ℕ), i < l.length → s < 4 →
      (l.flatMap f).getD (4 * i + s) d = (f (l.getD i 0)).getD s d
  | [], _, _, hi, _ => absurd hi (by simp)
  | m :: l, 0, s, _, hs => by
    rw [List.flatMap_cons, List.getD_append _ _ _ _ (by rw [hf]; omega)]; simp
  | m :: l, i + 1, s, hi, hs => by
    rw [List.flatMap_cons, List.getD_append_right _ _ _ _ (by rw [hf]; omega), hf,
      show 4 * (i + 1) + s - 4 = 4 * i + s by omega]
    exact getD_flatMap4 f hf d l i s (by simpa using hi) hs

/-- The family's `m` of kind `κ`'s points (`m*` if `selA`). -/
def pfFamM (P : FinP) (κ : Kind) : ℕ := if P.kv.selA κ then P.S.mStar else P.fams.getD (famI P κ) 0

section Slots
variable (P : FinP) (fi : FinIn)

/-- The tails of family `m`. -/
private def tlF (m : ℕ) : List (List PtSrc) := (List.range 4).map fun k => (gTailRegs P.S fi m (k + 1)).map .k

/-- The claims' part of `gPfPts`. -/
private def clF : List (List PtSrc) :=
  [zSrc fi P.S.mStar] ++ P.fams.map (zSrc fi) ++ [gLcSrc P.S fi P.S.mStar] ++ P.fams.map (gLcSrc P.S fi) ++
    [gShSrc P.S fi P.S.mStar] ++ P.fams.map (gShSrc P.S fi) ++ P.e4s.map (fun e => (chals fi "E4" e).map .f)

private theorem clF_length : (clF P fi).length = 3 + 3 * P.fams.length + P.e4s.length := by
  simp [clF]; ring

private theorem gPfPts_split : gPfPts P fi = clF P fi ++ (tlF P fi P.S.mStar ++ (P.fams.flatMap (tlF P fi) ++
    ((gP0Regs P.S fi P.S.mStar).map .k :: P.fams.map (fun m => (gP0Regs P.S fi m).map .k)))) := by
  simp only [gPfPts, clF, tlF, List.append_assoc, List.singleton_append]
  rfl

private theorem tlF_length (m : ℕ) : (tlF P fi m).length = 4 := by simp [tlF]

private theorem tlF_getD (m : ℕ) {s : ℕ} (hs : s < 4) :
    (tlF P fi m).getD s [] = (gTailRegs P.S fi m (s + 1)).map .k := by
  rw [tlF, List.getD_eq_getElem _ _ (by simpa using hs)]; simp

theorem slotA_tl4 {s : ℕ} (hs : s < 4) :
    (gPfPts P fi).getD (candAIx P s) [] = (gTailRegs P.S fi P.S.mStar (s + 1)).map .k := by
  rw [gPfPts_split, candAIx, if_pos hs, List.getD_append_right _ _ _ _ (by rw [clF_length]; omega),
    clF_length, show 3 + 3 * P.fams.length + P.e4s.length + s - (3 + 3 * P.fams.length + P.e4s.length) = s by omega,
    List.getD_append _ _ _ _ (by rw [tlF_length]; omega), tlF_getD P fi _ hs]

theorem slotA_p04 : (gPfPts P fi).getD (candAIx P 4) [] = (gP0Regs P.S fi P.S.mStar).map .k := by
  rw [gPfPts_split, candAIx, if_neg (by omega), List.getD_append_right _ _ _ _ (by rw [clF_length]; omega),
    clF_length, List.getD_append_right _ _ _ _ (by rw [tlF_length]; omega), tlF_length,
    List.getD_append_right _ _ _ _ (by rw [List.length_flatMap]; simp [tlF_length]; omega)]
  rw [List.length_flatMap]
  simp only [tlF_length, List.map_const', List.sum_replicate, smul_eq_mul]
  rw [show 7 + 7 * P.fams.length + P.e4s.length - (3 + 3 * P.fams.length + P.e4s.length) - 4 -
    P.fams.length * 4 = 0 by omega]
  rfl

theorem slotI_tl4 {i : ℕ} (hi : i < P.fams.length) {s : ℕ} (hs : s < 4) :
    (gPfPts P fi).getD (candIx P i s) [] = (gTailRegs P.S fi (P.fams.getD i 0) (s + 1)).map .k := by
  rw [gPfPts_split, candIx, if_pos hs, List.getD_append_right _ _ _ _ (by rw [clF_length]; omega),
    clF_length, List.getD_append_right _ _ _ _ (by rw [tlF_length]; omega), tlF_length,
    List.getD_append _ _ _ _ (by rw [List.length_flatMap]; simp [tlF_length]; omega),
    show 7 + 3 * P.fams.length + P.e4s.length + 4 * i + s - (3 + 3 * P.fams.length + P.e4s.length) - 4 =
      4 * i + s by omega, getD_flatMap4 _ (tlF_length P fi) _ _ i s hi hs, tlF_getD P fi _ hs]

theorem slotI_p04 {i : ℕ} (hi : i < P.fams.length) :
    (gPfPts P fi).getD (candIx P i 4) [] = (gP0Regs P.S fi (P.fams.getD i 0)).map .k := by
  rw [gPfPts_split, candIx, if_neg (by omega), List.getD_append_right _ _ _ _ (by rw [clF_length]; omega),
    clF_length, List.getD_append_right _ _ _ _ (by rw [tlF_length]; omega), tlF_length,
    List.getD_append_right _ _ _ _ (by rw [List.length_flatMap]; simp [tlF_length]; omega)]
  rw [List.length_flatMap]
  simp only [tlF_length, List.map_const', List.sum_replicate, smul_eq_mul]
  rw [show 8 + 7 * P.fams.length + P.e4s.length + i - (3 + 3 * P.fams.length + P.e4s.length) - 4 -
    P.fams.length * 4 = i + 1 by omega, List.getD_cons_succ, List.getD_eq_getElem _ _ (by simpa using hi),
    List.getElem_map, List.getD_eq_getElem _ _ hi]

/-- **Slot `s < 4` of kind `κ` is the tail `Pₛ₊₁[1..]` at the family's `m`.** -/
theorem slot_tl4 (κ : Kind) (hnf : 0 < P.fams.length) {s : ℕ} (hs : s < 4) :
    (gPfPts P fi).getD (slotIx P κ s) [] = (gTailRegs P.S fi (pfFamM P κ) (s + 1)).map .k := by
  unfold slotIx pfFamM; split_ifs
  · exact slotA_tl4 P fi hs
  · exact slotI_tl4 P fi (famI_lt P κ hnf) hs

/-- **Slot `4` of kind `κ` is `P₀` at the family's `m`.** -/
theorem slot_p04 (κ : Kind) (hnf : 0 < P.fams.length) :
    (gPfPts P fi).getD (slotIx P κ 4) [] = (gP0Regs P.S fi (pfFamM P κ)).map .k := by
  unfold slotIx pfFamM; split_ifs
  · exact slotA_p04 P fi
  · exact slotI_p04 P fi (famI_lt P κ hnf)

end Slots

/-- **The tables' family is the chain kind's** (`FinTabs4.pad`). -/
theorem pfFamM_eq {P : FinP} {κ : Kind} {κc : CKind} (hT : FinTabs4 P κ κc) : pfFamM P κ = κc.m := by
  unfold pfFamM
  rcases hT.pad with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · rw [if_pos h1, hT.S, h2, seq4_eq]
  · rw [if_neg (by simp [h1]), h2]

/-! ## The tail points (3.x's `tailList`, at T4's reads) -/

/-- `Pₖ[1..]`'s values: `sⱼ[1..]` for `j = k … 4`, then Pf's first `m − 25` challenges. -/
def tailList4 (es : Log) (m k : ℕ) : List K :=
  (List.range' k (5 - k)).flatMap (fun j => (List.range (hEll j - 1)).map fun t => T4.sAt es j (t + 1)) ++
    (List.range (m - 25)).map (T4.pfP es)

theorem tailList4_four_eq (es : Log) (m : ℕ) :
    tailList4 es m 4 = (List.range (tLen m 4)).map (fun v => T4.ptL es 4 (v + 1)) := by
  have h4 : hEll 4 = 4 := by simp [hEll, lvlStar, lvl, ladder, ladder32]
  have hl : tailList4 es m 4 = (List.range 3).map (fun t => T4.sAt es 4 (t + 1)) ++
      (List.range (m - 25)).map (T4.pfP es) := by
    simp [tailList4, h4]
  have h3 : tLen m 4 = 3 + (m - 25) := by simp [tLen, hEll, lvlStar, lvl, ladder, ladder32]
  rw [hl, h3, map_range_append]
  refine List.map_congr_left fun v _ => ?_
  unfold T4.ptL T4.ptD
  simp only [show 4 - 4 = 0 from rfl, h4]
  split_ifs with h1 h2 h2 <;> first | omega | exact congrArg _ (by omega)

theorem tailList4_step (es : Log) (m : ℕ) {k : ℕ} (hk1 : 1 ≤ k) (hk : k < 4)
    (ih : tailList4 es m (k + 1) = (List.range (tLen m (k + 1))).map (fun v => T4.ptL es (k + 1) (v + 1))) :
    tailList4 es m k = (List.range (tLen m k)).map (fun v => T4.ptL es k (v + 1)) := by
  have hr : List.range' k (5 - k) = k :: List.range' (k + 1) (5 - (k + 1)) := by
    rw [show 5 - k = (5 - (k + 1)) + 1 by omega, List.range'_succ]
  have hl : tailList4 es m k = (List.range (hEll k - 1)).map (fun t => T4.sAt es k (t + 1)) ++
      tailList4 es m (k + 1) := by
    rw [tailList4, tailList4, hr, List.flatMap_cons, List.append_assoc]
  have hlen : tLen m k = (hEll k - 1) + tLen m (k + 1) := by
    simp only [tLen, hr, List.map_cons, List.sum_cons]; omega
  rw [hl, ih, map_range_append, hlen]
  refine List.map_congr_left fun v _ => ?_
  have he := hEll_pos (i := k) (by omega)
  rw [T4.ptL_lt (k := k) hk]
  beta_reduce
  by_cases h1 : v < hEll k - 1
  · simp only [h1, show v + 1 < hEll k by omega, ite_true]
  · rw [show v - (hEll k - 1) + 1 = v + 1 - hEll k + 1 by omega]
    simp only [h1, show ¬ v + 1 < hEll k by omega, ite_false]

theorem tailList4_eq (es : Log) (m : ℕ) {k : ℕ} (hk1 : 1 ≤ k) (hk4 : k ≤ 4) :
    tailList4 es m k = (List.range (tLen m k)).map (fun v => T4.ptL es k (v + 1)) := by
  have h4 := tailList4_four_eq es m
  have h3 := tailList4_step es m (k := 3) (by norm_num) (by norm_num) h4
  have h2 := tailList4_step es m (k := 2) (by norm_num) (by norm_num) h3
  have h1 := tailList4_step es m (k := 1) (by norm_num) (by norm_num) h2
  obtain rfl | rfl | rfl | rfl : k = 1 ∨ k = 2 ∨ k = 3 ∨ k = 4 := by omega
  exacts [h1, h2, h3, h4]

/-- The tails' lengths are T4's `mLog` (every chain kind). -/
theorem tail_len4 (κ : CKind) {k : ℕ} (hk1 : 1 ≤ k) (hk4 : k ≤ 4) : tLen κ.m k = T4.mLog κ (k - 1) := by
  rcases κ with σ | ν <;> [cases σ; cases ν] <;> interval_cases k <;> decide

theorem T4_ptL_zero {es : Log} {k : ℕ} (hk : k ≤ 4) : T4.ptL es k 0 = T4.sAt es k 0 := by
  rcases Nat.lt_or_ge k 4 with h | h
  · rw [T4.ptL_lt h]; simp [hEll_pos (i := k) (by omega)]
  · obtain rfl : k = 4 := by omega
    exact T4.ptL_four_lt es (hEll_pos (by norm_num))

section Run
variable {impl : OpImpl} {p : KindP} {inp : Input} {tr : Trace} {y : List Val × List Bool × Trace}
  (h : SkRun4 impl p inp tr y) {fi : FinIn} (hfi : fi.outs = (skeleton4 seq4 p).2.outs)
  {R : Array Val} (hR : ExtA (#[] ++ y.1.toArray) R)
include h hfi hR

/-- **`sᵢ`'s registers** (`gSRegs seq4`, 3.x's `sRegs`) hold T4's `sAt`. -/
theorem gSRegs_view4 {i : ℕ} (hi : i < 5) :
    ∃ b, gSRegs seq4 fi i = (List.range (hEll i)).map (fun j => b + 13 * j + 6) ∧
      sRegs fi i = gSRegs seq4 fi i ∧
      (∀ j < hEll i, rd R (b + 13 * j + 6) = .k (T4.sAt (fsOf tr (itemsOf seq4)) i j)) ∧
      ∀ x ∈ gSRegs seq4 fi i, x < (#[] ++ y.1.toArray).size := by
  obtain ⟨b, hout, hsv, -, -, hlt, -⟩ := p1_view4 h hfi hi
  have hs : gSRegs seq4 fi i = (List.range (hEll i)).map (fun j => b + 13 * j + 6) := by
    rw [gSRegs, hout, seq4_ell hi, List.cons_append, List.drop_one, List.tail_cons,
      List.take_append_of_le_length (by simp), List.take_of_length_le (by simp)]
  have hlt' : ∀ x ∈ gSRegs seq4 fi i, x < (#[] ++ y.1.toArray).size := fun x hx =>
    hlt x (by rw [gSRegs] at hx; exact List.mem_of_mem_drop (List.mem_of_mem_take hx))
  refine ⟨b, hs, by rw [sRegs, gSRegs, seq4_ell hi]; rfl, fun j hj => ?_, hlt'⟩
  rw [hR.rd (hlt' _ (by rw [hs]; exact List.mem_map.2 ⟨j, List.mem_range.2 hj, rfl⟩)), hsv j hj]

/-- **The tail registers hold `T4.ptL`** (`k = 1 … 4`; 3.x's `tail_vals`). -/
theorem tail_vals4 (κ : CKind) {k : ℕ} (hk1 : 1 ≤ k) (hk4 : k ≤ 4) :
    (gTailRegs seq4 fi κ.m k).map (fun x => (rd R x).toK) =
        (List.range (T4.mLog κ (k - 1))).map (fun v => T4.ptL (fsOf tr (itemsOf seq4)) k (v + 1)) ∧
      ∀ x ∈ gTailRegs seq4 fi κ.m k, x < (#[] ++ y.1.toArray).size := by
  obtain ⟨hpv, hpl, -, -, hpo, -⟩ := pf_view4 h hfi
  have hm : κ.m - 25 ≤ 7 := by have := CKind.m_mem κ; omega
  have hS : ∀ j < 5, ((gSRegs seq4 fi j).drop 1).map (fun x => (rd R x).toK) =
      (List.range (hEll j - 1)).map (fun t => T4.sAt (fsOf tr (itemsOf seq4)) j (t + 1)) ∧
      ∀ x ∈ (gSRegs seq4 fi j).drop 1, x < (#[] ++ y.1.toArray).size := fun j hj => by
    obtain ⟨b, hs, -, hsv, hlt⟩ := gSRegs_view4 h hfi hR hj
    refine ⟨?_, fun x hx => hlt x (List.mem_of_mem_drop hx)⟩
    rw [hs, drop_one_map_range, List.map_map]
    refine List.map_congr_left fun t ht => ?_
    have ht' := List.mem_range.1 ht
    simp only [Function.comp_apply]
    rw [hsv _ (by omega)]
    rfl
  have hch : ∀ x ∈ chals fi "Pf" 7, x ∈ outsOf fi "Pf" := fun x hx => by
    unfold chals at hx; exact List.mem_of_mem_drop (List.mem_of_mem_take hx)
  have hP : ((chals fi "Pf" seq4.pf).take (κ.m - 25)).map (fun x => (rd R x).toK) =
      (List.range (κ.m - 25)).map (T4.pfP (fsOf tr (itemsOf seq4))) := by
    rw [seq4_pf]
    refine List.ext_getElem (by simp [hpl]; omega) fun v h1 h2 => ?_
    simp only [List.length_map, List.length_take, hpl] at h1
    simp only [List.getElem_map, List.getElem_take, List.getElem_range]
    have hv : v < 7 := by omega
    have hmem : (chals fi "Pf" 7)[v] ∈ outsOf fi "Pf" := hch _ (List.getElem_mem _)
    rw [hR.rd (hpo _ hmem), ← List.getD_eq_getElem _ 0, hpv v hv]; rfl
  refine ⟨?_, fun x hx => ?_⟩
  · rw [gTailRegs, List.map_append, List.map_flatMap, hP, ← tail_len4 κ hk1 hk4,
      ← tailList4_eq _ _ hk1 hk4, tailList4,
      List.flatMap_congr fun j hj => (hS j (by have := List.mem_range'.1 hj; omega)).1]
  · rw [gTailRegs, List.mem_append, List.mem_flatMap] at hx
    rcases hx with ⟨j, hj, hx⟩ | hx
    · exact (hS j (by have := List.mem_range'.1 hj; omega)).2 x hx
    · rw [seq4_pf] at hx
      exact hpo x (hch x (List.mem_of_mem_take hx))

/-- **Q.k's position registers and count**: `ysOf fi k` has the kind's `t` registers; query `q`'s
position register holds `qPos`. -/
theorem ys_view4 {L : Log} (hL : (L.map Prod.fst).Nodup) (hin : ∀ e ∈ tr, e ∈ L)
    (hm : p.d.m = (kindOfC (fsOf tr (itemsOf seq4))).m) {k : ℕ} (hk : k < 5) :
    (ysOf fi k).length = (CKind.lv (kindOfC (fsOf tr (itemsOf seq4))) k).t ∧
      ∀ q < (CKind.lv (kindOfC (fsOf tr (itemsOf seq4))) k).t,
        (ysOf fi k).getD q 0 - 3 < (#[] ++ y.1.toArray).size ∧
        rd R ((ysOf fi k).getD q 0 - 3) =
          .n (T4.qPos (kindOfC (fsOf tr (itemsOf seq4))) (fsOf tr (itemsOf seq4)) k q) := by
  have hys : ysOf fi k = (skeleton4 seq4 p).2.outs.getD (29 + 5 * k) [] := by
    rw [ysOf, lvOuts, hfi, phaseIx_P1, show 26 + 5 * k + 3 = 29 + 5 * k by ring]
  obtain ⟨hnQ, eQ⟩ := ph4 (phases4_lvl (i := k) hk).2.2
  have hT := (lv_facts4 (CKind.m_mem (kindOfC (fsOf tr (itemsOf seq4)))) (i := k) hk).1
  have hysE : (ysOf fi k).length = (CKind.lv (kindOfC (fsOf tr (itemsOf seq4))) k).t := by
    rw [hys, skeleton4_outs seq4 p hnQ, eQ, genPhase4_queries_outs, List.length_map, List.length_range, ← hT]; rfl
  refine ⟨hysE, fun q hq => ?_⟩
  have hyq : (ysOf fi k).getD q 0 = yReg4 p k q := by rw [yReg4, ← hys]
  have hmem : yReg4 p k q ∈ ysOf fi k := by
    rw [← hyq, List.getD_eq_getElem _ _ (by rw [hysE]; exact hq)]; exact List.getElem_mem _
  have hylt : yReg4 p k q < (#[] ++ y.1.toArray).size :=
    skeleton4_out_lt p h.ref _ _ (by rw [← hys]; exact hmem)
  have hlt : yReg4 p k q - 3 < (#[] ++ y.1.toArray).size := lt_of_le_of_lt (Nat.sub_le _ _) hylt
  exact ⟨by rw [hyq]; exact hlt, by rw [hyq, hR.rd hlt, posReg4 h hL hin hm hk hq]⟩

/-- **One level step of `finPf` at the spec** (`k + 1 = 1 … 4`; 3.x's `lvStepV_eq`): `lvStepV` is
`T4.wHatL`'s step, given the tail array `tl (k + 1)` of the kind's tail registers. -/
theorem lvStepV_eq4 {L : Log} (hL : (L.map Prod.fst).Nodup) (hin : ∀ e ∈ tr, e ∈ L)
    (hm : p.d.m = (kindOfC (fsOf tr (itemsOf seq4))).m)
    (ht : ∀ j r, impl.tensorW j r = Impl.tensorWS j r) {tl : ℕ → Array K} {k : ℕ} (hk : k < 4)
    (htl : tl (k + 1) =
      ((gTailRegs seq4 fi (kindOfC (fsOf tr (itemsOf seq4))).m (k + 1)).map fun x => (rd R x).toK).toArray)
    (W : K) :
    lvStepV impl fi (rd R) tl (k + 1) W =
      uHat (T4.ptL (fsOf tr (itemsOf seq4)) (k + 1) 0) * (W +
        ∑ q ∈ range (CKind.lv (kindOfC (fsOf tr (itemsOf seq4))) k).t,
          algebraMap F K (eqBits (T4.kcAt (fsOf tr (itemsOf seq4)) k) 9 q) *
            tensorTwin D logNMax (T4.mLog (kindOfC (fsOf tr (itemsOf seq4))) k)
              (fun v => if v < T4.mLog (kindOfC (fsOf tr (itemsOf seq4))) k then
                T4.ptL (fsOf tr (itemsOf seq4)) (k + 1) (v + 1) else 0)
              (T4.qPos (kindOfC (fsOf tr (itemsOf seq4))) (fsOf tr (itemsOf seq4)) k q)) := by
  obtain ⟨b, hs, hsr, hsv, -⟩ := gSRegs_view4 h hfi hR (i := k + 1) (by omega)
  obtain ⟨-, hkc⟩ := kc_view4 h hfi (i := k) (by omega) hR
  obtain ⟨hyl, hyv⟩ := ys_view4 h hfi hR hL hin hm (k := k) (by omega)
  obtain ⟨htv, -⟩ := tail_vals4 h hfi hR (kindOfC (fsOf tr (itemsOf seq4))) (k := k + 1) (by omega) (by omega)
  rw [Nat.add_sub_cancel] at htv
  have hT : (CKind.lv (kindOfC (fsOf tr (itemsOf seq4))) k).t = (seq4.lv k).t :=
    (lv_facts4 (CKind.m_mem (kindOfC (fsOf tr (itemsOf seq4)))) (i := k) (by omega)).1
  have ht9 := t_lt4 (i := k) (by omega)
  unfold lvStepV
  simp only [Nat.add_sub_cancel]
  have hE0 := hEll_pos (i := k + 1) (by omega)
  have hhead : (sRegs fi (k + 1)).headD 0 = b + 13 * 0 + 6 := by
    rw [hsr, hs]; obtain ⟨e, he⟩ : ∃ e, hEll (k + 1) = e + 1 := ⟨hEll (k + 1) - 1, by omega⟩
    rw [he, List.range_succ_eq_map]; rfl
  rw [hhead, hsv 0 hE0, Val.toK, T4_ptL_zero (by omega)]
  congr 1
  have hkc' : (kcOf fi k).map (fun x => (rd R x).toF) = (List.range 9).map (T4.kcAt (fsOf tr (itemsOf seq4)) k) :=
    hkc
  rw [hkc', accVal_eq, List.length_map, List.length_range, hyl,
    ← List.sum_toFinset _ List.nodup_range, List.toFinset_range]
  congr 1
  refine sum_congr rfl fun q hq => ?_
  have hq' := mem_range.1 hq
  rw [Nat.zero_add, eqTab_getD _ (by simp; omega), K.smulF_eq_mul, ← K.algebraMap_eq_ofF]
  simp only [List.size_toArray, List.length_map, List.length_range]
  rw [eqBits_congr (r' := T4.kcAt (fsOf tr (itemsOf seq4)) k) (fun v hv => by
    simp [Array.getD_eq_getD_getElem?, hv])]
  congr 1
  rw [List.getD_eq_getElem _ _ (by simpa using hq'), List.getElem_map, List.getElem_range,
    (hyv q hq').2, Val.toN, ht, Impl.tensorWS,
    tensorTwin, tensorTwin]
  have hsz : (tl (k + 1)).size = T4.mLog (kindOfC (fsOf tr (itemsOf seq4))) k := by
    rw [htl, List.size_toArray, htv]; simp
  rw [hsz]
  refine prod_congr rfl fun v hv => ?_
  have hv' := mem_range.1 hv
  have hg : (tl (k + 1)).getD v 0 = T4.ptL (fsOf tr (itemsOf seq4)) (k + 1) (v + 1) := by
    rw [htl, Array.getD_eq_getD_getElem?, List.getElem?_toArray, htv]; simp [hv']
  rw [hg, if_pos hv']

/-- **`finPf`'s `Ŵ₄(P₄)` at the spec is `T4.wHatL … 4`**, from `Ŵ₀(P₀)` (3.x's `wV_eq`). -/
theorem wV_eq4 {L : Log} (hL : (L.map Prod.fst).Nodup) (hin : ∀ e ∈ tr, e ∈ L)
    (hm : p.d.m = (kindOfC (fsOf tr (itemsOf seq4))).m)
    (ht : ∀ j r, impl.tensorW j r = Impl.tensorWS j r) {tl : ℕ → Array K}
    (htl : ∀ k < 4, tl (k + 1) =
      ((gTailRegs seq4 fi (kindOfC (fsOf tr (itemsOf seq4))).m (k + 1)).map fun x => (rd R x).toK).toArray)
    (W₀ : Log → Log → ℕ → K) {w0 : K} (hw0 : w0 = T4.wHatL W₀ L (fsOf tr (itemsOf seq4)) 0) :
    lvsV impl fi (rd R) tl [1, 2, 3, 4] w0 = T4.wHatL W₀ L (fsOf tr (itemsOf seq4)) 4 := by
  have key : ∀ k ≤ 4, lvsV impl fi (rd R) tl ((List.range k).map (· + 1)) w0 =
      T4.wHatL W₀ L (fsOf tr (itemsOf seq4)) k := by
    intro k hk4
    induction k with
    | zero => exact hw0
    | succ k ih =>
      rw [List.range_succ, List.map_append, List.map_singleton, lvsV_snoc, ih (by omega),
        lvStepV_eq4 h hfi hR hL hin hm ht (by omega) (htl k (by omega)), T4.wHatL]
  exact key 4 le_rfl

end Run

end FR.Snd.R4

end G6_FRSoundness4R4Wt

section G6_FRSoundness4R4W0R

-- New for `flock-recursive` (BLUEPRINT revision 4.1, A.9 `finPf`'s `Ŵ₀(P₀)`; track R4i). The 3.x
-- template is `FRSoundnessFrW0V` (`zSrc_val` … `eSrc_val`, `p0_vals`, `w0V_run`).

/-!
# `finPf`'s `Ŵ₀(P₀)` on the run is T4's `wHatL … 0`

* **The claim points** (`rsSrc4_val`): the kind's claim sources (`rsSrc4`: Z, Lc, Sh at the kind's
  `m`, a node's E4 `r′`) read the log's `rsPtsL4` (`zSrc_val4`, `lcSrc_val4`, `shSrc_val4`,
  `eSrc_val4`); the tables pick them (`ptIx_seg4`, `ptIx_node4`).
* **`P₀`** (`p0_vals4`): `gP0Regs` holds `T4.ptL es 0`.
* **The cells** (`cellsVal4_sum`, `eqCellK4_eq`): `gCellsOpsK`'s accumulator over `nc = 25`
  coordinates is `Σ_k κ′^(k+2)·eq(P₀, cell_k)` over the kind's `m − 7`: a coordinate past `m − 7`
  has bit `0` and `ρ_v = 0`, factor `1`.
* **`w0V4_eq4`**: with `rsWeight` at the kind's spec (`rsSpec4`), `w0V4 = T4.wHatL W₀ L es 0` at
  `W₀ := P4b.W₀L4 N4c.kf4 cells` (`wHat0_spec4`).
-/

namespace FR.Snd.R4
open RecursionFast Rev4 Finset

/-! ## Windows of a rounds phase's challenges -/

theorem rchs_drop (b : ℕ) (es : Log) (n d : ℕ) :
    (rchs b es n).drop d = (List.range (n - d)).map (fun l => rch b es (d + l)) := by
  apply List.ext_getElem (by simp [rchs])
  intro j h1 h2; simp [rchs]

theorem rchs_take (b : ℕ) (es : Log) {n t : ℕ} (h : t ≤ n) : (rchs b es n).take t = rchs b es t := by
  apply List.ext_getElem (by simp [rchs]; omega)
  intro j h1 h2; simp [rchs]

theorem srcF_map (R : Array Val) (l : List Reg) :
    (l.map PtSrc.f).map (srcVal R) = (l.map (fv R)).map (algebraMap F K) := by
  simp [srcVal, K.smulF_one]

/-! ## The claim sources -/

/-- **The kind's claim sources** (`gPfPts`' claims at the kind's `m`; `rsPtsL4`'s order). -/
def rsSrc4 (κ : CKind) (fi : FinIn) : List (List PtSrc) :=
  [zSrc fi κ.m, gLcSrc seq4 fi κ.m, gShSrc seq4 fi κ.m] ++
    match κ with
    | .node ν => [(chals fi "E4" (P4b.ncR ν)).map .f]
    | .seg _ => []

theorem seq4_mStar : seq4.mStar = 32 := by rw [seq4_eq]

/-- **A segment's tables pick its claim sources.** -/
theorem ptIx_seg4 (σ : SegKind) (κ : Kind) (fi : FinIn) :
    ((segFinP σ).kv.ptIx κ).map (fun j => (gPfPts (segFinP σ) fi).getD j []) = rsSrc4 (.seg σ) fi := by
  cases σ <;> simp (config := { decide := true }) [segFinP, kvOf, segFams, gPfPts, rsSrc4, seq4_mStar,
    SegKind.m, CKind.m]

/-- **A node's tables pick its claim sources** (E4's point of length `m − 7`). -/
theorem ptIx_node4 (ν : NodeKind) (cells : List ℕ) (κ : Kind) (fi : FinIn) :
    ((nodeFinP ν cells).kv.ptIx κ).map (fun j => (gPfPts (nodeFinP ν cells) fi).getD j []) =
      rsSrc4 (.node ν) fi := by
  cases ν <;> simp (config := { decide := true }) [nodeFinP, kvOf, nodeFams, nodeE4s, gPfPts, rsSrc4,
    seq4_mStar, NodeKind.m, CKind.m, P4b.ncR]

section Run
variable {impl : OpImpl} {p : KindP} {inp : Input} {tr : Trace} {y : List Val × List Bool × Trace}
  (h : SkRun4 impl p inp tr y) {fi : FinIn} (hfi : fi.outs = (skeleton4 seq4 p).2.outs)
  {R : Array Val} (hR : ExtA (#[] ++ y.1.toArray) R)
include h hfi hR

theorem chalsK_view4 {name : String} {n f k : ℕ} (hn : n < (phasesOf seq4).length)
    (hsh : (phasesOf seq4)[n].2 = .rounds f k 2 false) (hix : phaseIx name = n) :
    (chals fi name k).map (fv R) = rchs (phStart4 n) (fsOf tr (itemsOf seq4)) k :=
  chals_view4 h hfi hR hn hsh hix le_rfl

theorem zSrc_val4 {m : ℕ} (hm : m ≤ 32) :
    (zSrc fi m).map (srcVal R) = (zPtL m (fsOf tr (itemsOf seq4))).map (algebraMap F K) := by
  obtain ⟨hn3, e3⟩ := ph4 (n := 3) (x := ("Z1", Sh.squeezes 10 .coords)) (by rw [seq4_eq]; rfl)
  have hco := coordsR_view4 h hfi hR hn3 (by rw [e3]) (by norm_num) phaseIx_vals.1 (a := m - 13) (by omega)
  rw [show phStart4 3 = 3 by rw [phStart4, fsStarts4_eq]; rfl] at hco
  rw [zSrc, zPtL, List.map_append, List.map_append, srcF_map, hco, List.map_map, List.map_map, List.map_map]
  rfl

theorem lcSrc_val4 {m : ℕ} (hm1 : 14 ≤ m) (hm : m ≤ 32) :
    (gLcSrc seq4 fi m).map (srcVal R) = (lcPtL m (fsOf tr (itemsOf seq4))).map (algebraMap F K) := by
  obtain ⟨hn8, e8⟩ := ph4 (n := 8) (x := ("L2", Sh.rounds fL2 14 2 false)) (by rw [seq4_eq]; rfl)
  obtain ⟨hn5, e5⟩ := ph4 (n := 5) (x := ("Z3", Sh.rounds fZ3 26 3 false)) (by rw [seq4_eq]; rfl)
  have hL := chalsK_view4 h hfi hR hn8 (by rw [e8]) phaseIx_vals.2.2.2.2.1
  have hZ := chals_view4 h hfi hR hn5 (by rw [e5]) phaseIx_vals.2.2.1 (a := 26) le_rfl
  rw [show phStart4 8 = 69 by rw [phStart4, fsStarts4_eq]; rfl] at hL
  rw [show phStart4 5 = 15 by rw [phStart4, fsStarts4_eq]; rfl] at hZ
  have e1 : ((chals fi "L2" 14).drop 7).map (fv R) =
      (List.range 7).map (fun l => rch 69 (fsOf tr (itemsOf seq4)) (7 + l)) := by
    rw [List.map_drop, hL, rchs_drop]
  have e2 : (((chals fi "Z3" 26).take (m - 6)).drop 8).map (fv R) =
      (List.range (m - 14)).map (fun l => rch 15 (fsOf tr (itemsOf seq4)) (8 + l)) := by
    rw [List.map_drop, List.map_take, hZ, rchs_take _ _ (by omega), rchs_drop, show m - 6 - 8 = m - 14 by omega]
  rw [gLcSrc, lcPtL, show seq4.z3 = 26 by rw [seq4_eq], List.map_append, List.map_append, srcF_map,
    srcF_map, e1, e2]

theorem shSrc_val4 {m : ℕ} (hm1 : 14 ≤ m) (hm : m ≤ 32) :
    (gShSrc seq4 fi m).map (srcVal R) = (shPtL m (fsOf tr (itemsOf seq4))).map (algebraMap F K) := by
  obtain ⟨hn12, e12⟩ := ph4 (n := 12) (x := ("S2", Sh.rounds fS2 28 2 false)) (by rw [seq4_eq]; rfl)
  have hS := chalsK_view4 h hfi hR hn12 (by rw [e12]) phaseIx_vals.2.2.2.2.2.2.2.1
  rw [show phStart4 12 = 114 by rw [phStart4, fsStarts4_eq]; rfl] at hS
  have e1 : (((chals fi "S2" 28).drop (m - 7)).take 3).map (fv R) =
      (List.range 3).map fun l => rch 114 (fsOf tr (itemsOf seq4)) (m - 7 + l) := by
    rw [List.map_take, List.map_drop, hS, rchs_drop, ← List.map_take, List.take_range,
      show min 3 (28 - (m - 7)) = 3 by omega]
  have e2 : ((chals fi "S2" 28).take (m - 14)).map (fv R) =
      (List.range (m - 14)).map (rch 114 (fsOf tr (itemsOf seq4))) := by
    rw [List.map_take, hS, rchs_take _ _ (by omega)]; rfl
  rw [gShSrc, shPtL, show seq4.s2 = 28 by rw [seq4_eq], List.map_append, List.map_append,
    List.map_append, List.map_append, srcF_map, srcF_map, e1, e2]
  simp [srcVal]

theorem eSrc_val4 (ν : NodeKind) :
    ((chals fi "E4" (P4b.ncR ν)).map PtSrc.f).map (srcVal R) =
      (P4b.ePtL4 (P4b.ncR ν) (fsOf tr (itemsOf seq4))).map (algebraMap F K) := by
  obtain ⟨hn21, e21⟩ := ph4 (n := 21) (x := ("E4", Sh.rounds fE 25 2 false)) (by rw [seq4_eq]; rfl)
  have hE := chals_view4 h hfi hR hn21 (by rw [e21]) phaseIx_vals.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
    (a := P4b.ncR ν) (by cases ν <;> decide)
  rw [show phStart4 21 = 275 by rw [phStart4, fsStarts4_eq]; rfl] at hE
  rw [srcF_map, hE]
  rfl

/-- **The claim sources read the log's claim points** (every chain kind). -/
theorem rsSrc4_val (κ : CKind) :
    (rsSrc4 κ fi).map (fun s => (s.map (srcVal R)).toArray) =
      (P4b.rsPtsL4 κ (fsOf tr (itemsOf seq4))).map fun l => (l.map (algebraMap F K)).toArray := by
  have hm := CKind.m_mem κ
  have hz := zSrc_val4 h hfi hR (m := κ.m) (by omega)
  have hl := lcSrc_val4 h hfi hR (m := κ.m) (by omega) (by omega)
  have hs := shSrc_val4 h hfi hR (m := κ.m) (by omega) (by omega)
  cases κ with
  | seg σ => simp only [rsSrc4, P4b.rsPtsL4, List.map_append, List.map_cons, List.map_nil, hz, hl, hs]
  | node ν =>
    simp only [rsSrc4, P4b.rsPtsL4, List.map_append, List.map_cons, List.map_nil, hz, hl, hs,
      eSrc_val4 h hfi hR ν]

/-- **`P₀`'s registers hold `T4.ptL es 0`** (3.x's `p0_vals`). -/
theorem p0_vals4 (κ : CKind) :
    ((gP0Regs seq4 fi κ.m).map fun x => (rd R x).toK).length = κ.m - 7 ∧
      ∀ v < κ.m - 7, ((gP0Regs seq4 fi κ.m).map fun x => (rd R x).toK).getD v 0 =
        T4.ptL (fsOf tr (itemsOf seq4)) 0 v := by
  obtain ⟨b, hs, -, hv, -⟩ := gSRegs_view4 h hfi hR (i := 0) (by norm_num)
  have ht := (tail_vals4 h hfi hR κ (k := 1) le_rfl (by norm_num)).1
  have hA : (gSRegs seq4 fi 0).map (fun x => (rd R x).toK) =
      (List.range (hEll 0)).map (T4.sAt (fsOf tr (itemsOf seq4)) 0) := by
    rw [hs, List.map_map]
    refine List.map_congr_left fun j hj => ?_
    simp only [Function.comp, hv j (List.mem_range.mp hj)]
    rfl
  have hn : κ.m - 7 = hEll 0 + T4.mLog κ 0 := by
    rw [← nrP_zero4, T4.nrP, T4.lvl_ell κ (by norm_num)]
  rw [gP0Regs, List.map_append, hA, ht]
  refine ⟨by simp [hn], fun v hv' => ?_⟩
  rw [T4.ptL_lt (k := 0) (by norm_num)]
  dsimp only
  by_cases h0 : v < hEll 0
  · rw [List.getD_append _ _ _ _ (by simpa using h0), if_pos h0,
      List.getD_eq_getElem _ _ (by simpa using h0)]
    simp
  · rw [List.getD_append_right _ _ _ _ (by simpa using h0), if_neg h0]
    simp only [List.length_map, List.length_range]
    rw [List.getD_eq_getElem _ _ (by simp; omega)]
    simp only [List.getElem_map, List.getElem_range, zero_add]

end Run

/-! ## The cells -/

theorem cellsVal4_sum (nc : ℕ) (ρ : Array K) (kp : F) (cell : ℕ → ℕ) :
    ∀ (n j : ℕ) (pw : F) (A : K), cellsVal4 nc ρ kp cell n j pw A =
      A + ∑ k ∈ range n, algebraMap F K (pw * kp ^ k) * eqCellK4 nc ρ (cell (j + k))
  | 0, _, _, A => by simp [cellsVal4]
  | n + 1, j, pw, A => by
    rw [cellsVal4, cellsVal4_sum nc ρ kp cell n (j + 1), sum_range_succ', K.smulF_eq_mul,
      ← K.algebraMap_eq_ofF, pow_zero, mul_one, add_zero]
    have e : ∀ k ∈ range n, algebraMap F K (pw * kp * kp ^ k) * eqCellK4 nc ρ (cell (j + 1 + k)) =
        algebraMap F K (pw * kp ^ (k + 1)) * eqCellK4 nc ρ (cell (j + (k + 1))) := fun k _ => by
      rw [pow_succ, mul_assoc pw, mul_comm (kp ^ k) kp, show j + 1 + k = j + (k + 1) by ring]
    rw [sum_congr rfl e]
    ring

/-- **`finPf`'s two cell chains** (the public cells from `κ′²`, then, gated, the reserve's from
`κ′^{2+n₁}`) sum `Σ_k κ′^{k+2}·eq(cell_k, ρ)` over the cells `cs ++ rs` (revision 4.4.2; with the gate
off the reserve's list is empty). -/
theorem cells2_sum (nc : ℕ) (ρ : Array K) (kp : F) (cs rs : List ℕ) (g : Bool) (n1 n2 : ℕ)
    (h1 : n1 = cs.length) (h2 : rs.length = if g = true then n2 else 0) :
    (if g = true then cellsVal4 nc ρ kp (fun j => rs.getD j 0) n2 0 (kp * kp * kp ^ n1)
        (cellsVal4 nc ρ kp (fun j => cs.getD j 0) n1 0 (kp * kp) 0)
      else cellsVal4 nc ρ kp (fun j => cs.getD j 0) n1 0 (kp * kp) 0) =
      ∑ k ∈ range (cs ++ rs).length, algebraMap F K (kp ^ (k + 2)) * eqCellK4 nc ρ ((cs ++ rs).getD k 0) := by
  have hA : cellsVal4 nc ρ kp (fun j => cs.getD j 0) n1 0 (kp * kp) 0 =
      ∑ k ∈ range cs.length, algebraMap F K (kp ^ (k + 2)) * eqCellK4 nc ρ ((cs ++ rs).getD k 0) := by
    rw [cellsVal4_sum, zero_add, h1]
    refine sum_congr rfl fun k hk => ?_
    rw [zero_add, List.getD_append _ _ _ _ (mem_range.1 hk), show kp * kp * kp ^ k = kp ^ (k + 2) by ring]
  rw [List.length_append, sum_range_add, ← hA]
  split_ifs at h2 ⊢ with hg
  · rw [cellsVal4_sum, h2]
    refine congrArg₂ (· + ·) rfl (sum_congr rfl fun k _ => ?_)
    rw [zero_add, List.getD_append_right _ _ _ _ (by omega), Nat.add_sub_cancel_left, h1]
    congr 2; ring
  · rw [h2, range_zero, sum_empty, add_zero]

/-- **`eqCellK4` over `nc` coordinates is `eq(cell, ρ)` over `ρ`'s `n ≤ nc`** for a cell below `2^n`
(characteristic 2; the zero-padded coordinates give `1`). -/
theorem eqCellK4_eq {nc n : ℕ} (ρ : List K) (hρ : ρ.length = n) (hn : n ≤ nc) {c : ℕ} (hc : c < 2 ^ n) :
    eqCellK4 nc ρ.toArray c = eqCell (FR.ptOf n ρ) c := by
  have h1 : ∀ x : K, 1 + x = 1 - x := fun x => by rw [sub_eq_add_neg, CharTwo.neg_eq]
  have hl : ∀ (l : List K), l.foldl (· * ·) 1 = l.prod := fun l => by
    rw [← List.prod_eq_foldl]
  rw [eqCellK4, hl, list_prod_range, ← prod_range_mul_prod_Ico _ hn]
  have hhi : ∏ v ∈ Ico n nc, (if c.testBit v then ρ.toArray.getD v 0 else 1 + ρ.toArray.getD v 0) = 1 := by
    refine prod_eq_one fun v hv => ?_
    have hv' := (mem_Ico.1 hv).1
    have hb : c.testBit v = false := Nat.testBit_eq_false_of_lt (lt_of_lt_of_le hc (Nat.pow_le_pow_right (by norm_num) hv'))
    have hz : ρ.toArray.getD v 0 = 0 := by
      rw [Array.getD_eq_getD_getElem?, List.getElem?_toArray, List.getElem?_eq_none (by omega)]; rfl
    simp [hb, hz]
  rw [hhi, mul_one, eqCell, ← Fin.prod_univ_eq_prod_range]
  refine prod_congr rfl fun v _ => ?_
  have hg : ρ.toArray.getD v 0 = FR.ptOf n ρ v := by
    rw [Array.getD_eq_getD_getElem?, List.getElem?_toArray, FR.ptOf, List.getD_eq_getElem?_getD]
  rw [hg, h1]

/-! ## `Ŵ₀(P₀)` -/

/-- **The kind's `rsWeight` specification** (a node's `rsWeightS4 ν`, a segment's `rsWeightS`). -/
noncomputable def rsSpec4 : CKind → Array F → List (Array K) → F → F → Array K → K
  | .node ν => Impl.rsWeightS4 ν
  | .seg _ => Impl.rsWeightS

/-- **`finPf`'s `Ŵ₀(P₀)` on an accepted run is T4's `wHatL … 0`** (3.x's `w0V_run`), for tables `P`
whose claim indices pick the kind's sources (`ptIx_seg4`, `ptIx_node4`), whose cells are the kind's
(`nc = 25` coordinates), with `rsWeight` at the kind's spec. -/
theorem w0V4_eq4 {impl : OpImpl} {p : KindP} {inp : Input} {tr : Trace} {y : List Val × List Bool × Trace}
    (h : SkRun4 impl p inp tr y) {fi : FinIn} (hfi : fi.outs = (skeleton4 seq4 p).2.outs)
    {R : Array Val} (hR : ExtA (#[] ++ y.1.toArray) R) {κc : CKind} (hk : kindOfC (fsOf tr (itemsOf seq4)) = κc)
    {P : FinP} (hT : FinTabs4 P p.tix κc)
    (hpts : (P.kv.ptIx p.tix).map (fun j => (gPfPts P fi).getD j []) = rsSrc4 κc fi)
    {cells : NodeKind → List ℕ} (hc : ∀ ν, ∀ c ∈ cells ν, c < 2 ^ P4b.ncR ν)
    (hcl : P.cells ++ P.rcells = P4b.cellsC cells κc) (hncell : P.ncell = P.cells.length)
    (hrc : P.rcells.length = if (P.rsvOps && P.rsv) = true then P.nrcell else 0) (hnc : P.nc = 25)
    (hrs : ∀ r ps k β ρ, r.size = 7 → 23 ≤ ρ.size → impl.rsWeight r ps k β ρ = rsSpec4 κc r ps k β ρ)
    (L : Log) :
    w0V4 impl p.tix fi R P = T4.wHatL (P4b.W₀L4 N4c.kf4 cells) L (fsOf tr (itemsOf seq4)) 0 := by
  obtain ⟨hρl, hρv⟩ := p0_vals4 h hfi hR κc
  rw [wHat0_spec4 cells hc L _ _ (by rw [hk]; exact hρl) (by rw [hk]; exact hρv), hk]
  have hrho : rho4 p.tix fi R P = ((gP0Regs seq4 fi κc.m).map fun x => (rd R x).toK).toArray := by
    rw [rho4, ptPf, slot_p04 P fi _ hT.nf, pfFamM_eq hT, hT.S]
    simp [ptV, srcVal]
  have hpts' : (P.kv.ptIx p.tix).map (ptPf fi R P) =
      (P4b.rsPtsL4 κc (fsOf tr (itemsOf seq4))).map fun l => (l.map (algebraMap F K)).toArray := by
    rw [← rsSrc4_val h hfi hR, ← hpts, List.map_map]; rfl
  have hr7 : ptF R ((List.range 7).map fun q => (coordsR fi "RS1").getD q 0) =
      (P4b.rsRL4 (fsOf tr (itemsOf seq4))).toArray := by
    simp only [ptF, P4b.rsRL4, List.map_map]
    exact congrArg List.toArray (List.map_congr_left fun q hq =>
      rs1_val4 h hfi hR (by simp at hq; omega))
  have hκ7 : fv R ((coordsR fi "RS1").getD 7 0) = P4b.rsKL4 (fsOf tr (itemsOf seq4)) :=
    rs1_val4 h hfi hR (by norm_num)
  have h23 : 23 ≤ (((gP0Regs seq4 fi κc.m).map fun x => (rd R x).toK).toArray).size := by
    rw [List.size_toArray, hρl]; have := CKind.m_mem κc; omega
  unfold w0V4 cv4
  rw [hrho, hpts', hr7, hκ7, hrs _ _ _ _ _ (by simp [P4b.rsRL4]) h23, hT.node]
  cases κc with
  | seg σ =>
    simp only [CKind.isNode, Bool.false_eq_true, if_false, add_zero, P4b.cellsC, List.length_nil,
      range_zero, sum_empty]
    simp only [rsSpec4, rsWS4]
  | node ν =>
    simp only [CKind.isNode, if_true]
    obtain ⟨hn10, e10⟩ := ph4 (n := 10) (x := ("L3β", Sh.squeezes 1 .one)) rfl
    obtain ⟨-, hβ⟩ := one_name_view4 h hfi hR hn10 (by rw [e10]) phaseIx_vals.2.2.2.2.2.1
    rw [show phStart4 10 = 98 by rw [phStart4, fsStarts4_eq]; rfl] at hβ
    obtain ⟨hn25, e25⟩ := ph4 (n := 25) (x := ("B'", Sh.squeezes 1 .one)) (by rw [seq4_eq]; rfl)
    obtain ⟨-, hkp⟩ := one_name_view4 h hfi hR hn25 (by rw [e25]) phaseIx_vals.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2
    rw [show phStart4 25 = 331 by rw [phStart4, fsStarts4_eq]; rfl] at hkp
    have hkp' : kp4 fi R = P4b.kpL4 (fsOf tr (itemsOf seq4)) := hkp
    rw [hβ, hkp', hnc, cells2_sum _ _ _ _ _ _ _ _ hncell hrc, hcl]
    refine congrArg₂ (· + ·) (by simp only [rsSpec4, rsWS4]) (sum_congr rfl fun k hk' => ?_)
    have hkl := mem_range.1 hk'
    simp only [P4b.cellsC] at hkl ⊢
    have hmem : (cells ν).getD k 0 ∈ cells ν := by
      rw [List.getD_eq_getElem _ _ hkl]; exact List.getElem_mem _
    rw [eqCellK4_eq _ hρl (by simp only [CKind.m]; cases ν <;> decide) (hc ν _ hmem)]

/-! ## `hW` on an accepted run's fields -/

/-- **`finPf`'s `Ŵ₄(P₄)` on an accepted run's fields is `T4.wHatL W₀ L es 4`** (`hW` of
`finRest4_full`), at `W₀ := P4b.W₀L4 N4c.kf4 cells`: the level steps (`wV_eq4`) from `Ŵ₀(P₀)`
(`w0V4_eq4`). -/
theorem wV4_of_fields {impl : OpImpl} {p : KindP} {inp : Input} {tr : Trace}
    {y : List Val × List Bool × Trace} {P : FinP} {zh : List Reg} {Rs : ℕ → Array Val}
    {Ex : ℕ → Array (List Reg)} (hF : Fields4 impl p inp tr P y zh Rs Ex) {κc : CKind}
    (hk : kindOfC (fsOf tr (itemsOf seq4)) = κc) (hT : FinTabs4 P p.tix κc)
    (hpts : (P.kv.ptIx p.tix).map (fun j => (gPfPts P ⟨(skeleton4 seq4 p).2.outs, zh, Ex 11⟩).getD j []) =
      rsSrc4 κc ⟨(skeleton4 seq4 p).2.outs, zh, Ex 11⟩)
    {cells : NodeKind → List ℕ} (hc : ∀ ν, ∀ c ∈ cells ν, c < 2 ^ P4b.ncR ν)
    (hcl : P.cells ++ P.rcells = P4b.cellsC cells κc) (hncell : P.ncell = P.cells.length)
    (hrc : P.rcells.length = if (P.rsvOps && P.rsv) = true then P.nrcell else 0) (hnc : P.nc = 25)
    (hrs : ∀ r ps k β ρ, r.size = 7 → 23 ≤ ρ.size → impl.rsWeight r ps k β ρ = rsSpec4 κc r ps k β ρ)
    (ht : ∀ j r, impl.tensorW j r = Impl.tensorWS j r) {L : Log} (hb : ¬ Bad L) (hin : ∀ e ∈ tr, e ∈ L)
    (hm : p.d.m = (kindOfC (fsOf tr (itemsOf seq4))).m) :
    wV4 impl p.tix ⟨(skeleton4 seq4 p).2.outs, zh, Ex 11⟩ (Rs 11) P =
      T4.wHatL (P4b.W₀L4 N4c.kf4 cells) L (fsOf tr (itemsOf seq4)) 4 := by
  have hL : (L.map Prod.fst).Nodup := by by_contra hr; exact hb (.inr (.inr (.inr hr)))
  have hE := hF.ext 11 (by omega)
  have hw0 := w0V4_eq4 hF.sk (fi := ⟨(skeleton4 seq4 p).2.outs, zh, Ex 11⟩) rfl hE hk hT hpts hc hcl hncell
    hrc hnc hrs L
  have htl : ∀ k < 4, tl4 p.tix ⟨(skeleton4 seq4 p).2.outs, zh, Ex 11⟩ (Rs 11) P (k + 1) =
      ((gTailRegs seq4 ⟨(skeleton4 seq4 p).2.outs, zh, Ex 11⟩ (kindOfC (fsOf tr (itemsOf seq4))).m (k + 1)).map
        fun x => (rd (Rs 11) x).toK).toArray := fun k hk4 => by
    rw [tl4, Nat.add_sub_cancel, ptPf, slot_tl4 P _ _ hT.nf hk4, pfFamM_eq hT, hT.S, hk]
    simp [ptV, srcVal]
  unfold wV4
  exact wV_eq4 hF.sk (fi := ⟨(skeleton4 seq4 p).2.outs, zh, Ex 11⟩) rfl hE hL hin hm ht htl _ hw0

end FR.Snd.R4

end G6_FRSoundness4R4W0R
