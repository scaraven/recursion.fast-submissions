-- New for `flock-recursive` (BLUEPRINT revision 4.1, §5.4, A.9 finals; track R4f). The 3.x template is
-- `FRSoundnessAccFin` (`FinLog`, `acceptTail_of_finLog`) and the round half of
-- `FRSoundnessAccLog.finLog_of_run`.
import FRSoundness4R4RndK

/-!
# T4's `AcceptTail` from an accepted `gen4` run (`FinLog4`)

`FinLog4 W₀ c₀ L es y` is what the accepted verifier's checks say about the chain `es` (3.x's
`FinLog`, at T4's revision 4.1 reads: `kindOfC`, `CKind.lv`, `T4.p1Start`, `T4.pfStart`, `T4.sAt`,
`T4.qPos`, `T4.capDig`, `T4.kcAt`, `T4.encAt`, `T4.finalAt`), the verifier's column folds being
`y i q`:

* `rnd`, `rndPf`: P1.i's and Pf's in-phase round checks, rounds `l ≥ 1` (**proved from the run**:
  `rounds_of_run4`, through `p1_view4`/`pf_view4`);
* `start`: P1.0's first claim is `c₀`;
* `cols`: P2.i's opened columns (a path to the cap entry, `y_q` their fold at `sᵢ`);
* `link`: `finP i`, `i < 4`; `pf0`: `finP 4`'s assert; `enc`: `finP 4`'s direct checks;
* `fin`: `finPf`'s `relPf` at the spec.

**`acceptTail4_of_finLog`** (3.x's `acceptTail_of_finLog`): on a log without bad events, a chain of
482 entries with `FinLog4` and `¬ RejF` is a `T4.AcceptTail`. **`acceptTail4_of_run`**: an accepted
run of `gen4 seq4 p fin` on a log without bad events has a chain `j` (`runLog_chain4`) whose entries
are the run's, so `chain`, `len`, `rnd`, `rndPf` come from the run; `¬ RejF` and the remaining
`FinLog4` fields are its hypotheses, stated on the run's own entries `fsOf tr (itemsOf seq4)`.
-/

namespace FR.Snd.R4
open RecursionFast Rev4 FR.Merkle Finset

/-- **What the accepted verifier's checks say on the log** (3.x's `FinLog` at revision 4.1). -/
structure FinLog4 (W₀ : Log → Log → ℕ → K) (c₀ : Log → Log → K) (L es : Log)
    (y : ℕ → ℕ → K) : Prop where
  /-- P1.i's rounds `l ≥ 1`: `g_l(0) + g_l(1) = g_{l−1}(r_{l−1})`. -/
  rnd : ∀ i < 5, ∀ l, l + 1 < hEll i → rSum (T4.p1Start i) es (l + 1) = rVal (T4.p1Start i) es l
  /-- Pf's rounds `l ≥ 1`. -/
  rndPf : ∀ l, l + 1 < 7 → rSum T4.pfStart es (l + 1) = rVal T4.pfStart es l
  /-- P1.0's first claim is the front's `c₀`. -/
  start : rSum (T4.p1Start 0) es 0 = c₀ L es
  /-- P2.i's opened columns: a path to the cap entry, and `y_q` their fold at `sᵢ`. -/
  cols : ∀ i < 5, ∀ q < (CKind.lv (kindOfC es) i).t, ∃ col : ByteArray, ∃ ss : List Digest,
    ss.length = (CKind.lv (kindOfC es) i).sib ∧
    (openPath (frEnc i) col (T4.qPos (kindOfC es) es i q) ss).runLog L =
      some (T4.capDig es i (T4.qPos (kindOfC es) es i q / 2 ^ (CKind.lv (kindOfC es) i).sib)) ∧
    y i q = ∑ r : Fin (CKind.lv (kindOfC es) i).rows,
      eqBits (T4.sAt es i) (CKind.lv (kindOfC es) i).ell r * algebraMap F K (readF col (16 * r))
  /-- `finP i`, `i < 4`: P1.(i+1)'s first claim is P1.i's last plus the batched folds. -/
  link : ∀ i < 4, rSum (T4.p1Start (i + 1)) es 0 = T4.c1 c₀ i L es +
    ∑ q ∈ range (CKind.lv (kindOfC es) i).t, K.smulF (eqBits (T4.kcAt es i) 9 q) (y i q)
  /-- `finP 4`'s assert: Pf's first claim is P1.4's last. -/
  pf0 : rSum T4.pfStart es 0 = T4.c1 c₀ 4 L es
  /-- `finP 4`'s direct checks: `y_q = Enc₄(final)[p_q]`. -/
  enc : ∀ q < (CKind.lv (kindOfC es) 4).t,
    y 4 q = T4.encAt (kindOfC es) 4 (T4.finalAt es) (T4.qPos (kindOfC es) es 4 q)
  /-- `finPf`'s `relPf` at the spec. -/
  fin : clR2 T4.pfStart 32 readK chK (T4.lvC c₀ 5) L es 7 = T4.wHatL W₀ L es 4 *
    (∏ v ∈ Ico (T4.mLog (kindOfC es) 4) 7, (1 - T4.pfP es v)) * mleN 7 (T4.finalAt es) (T4.pfPt es)

variable {W₀ : Log → Log → ℕ → K} {c₀ : Log → Log → K}

/-! ## From `FinLog4` to the tail's checks -/

/-- **The verifier's fold of a query is `foldAtN`** (the column is the committed one). -/
theorem y_eq_foldAtN4 {L es : Log} {y : ℕ → ℕ → K} (hc : ¬ Collision L) (h : FinLog4 W₀ c₀ L es y)
    {i : ℕ} (hi : i < 5) {q : ℕ} (hq : q < (CKind.lv (kindOfC es) i).t) :
    y i q = T4.foldAtN (kindOfC es) L es i (T4.qPos (kindOfC es) es i q) := by
  obtain ⟨col, ss, hss, hpath, hy⟩ := h.cols i hi q hq
  have hlt : T4.qPos (kindOfC es) es i q < 2 ^ (CKind.lv (kindOfC es) i).logN := idx_lt _ _ _
  rw [T4.foldAtN, dite_eq_left_of_eq_true (eq_true hlt), hy,
    T4.foldAt_of_cols (j := ⟨_, hlt⟩) hc hss hpath]

/-- **P1.i's round checks** from `FinLog4` (round 0: `start` for `i = 0`, `link` and the folds for
`i ≥ 1`). -/
theorem p1_of_finLog4 {L es : Log} {y : ℕ → ℕ → K} (hc : ¬ Collision L) (h : FinLog4 W₀ c₀ L es y) :
    ∀ i < 5, ∀ l < hEll i, Chk2 (T4.p1Start i) 32 readK chK (T4.lvC c₀ i) L es l := by
  intro i hi l hl
  rcases l with _ | l
  · rw [chk2_zero]
    rcases i with _ | i
    · exact h.start
    · rw [T4.lvC_succ c₀ (by omega), h.link i (by omega), T4.vNext]
      refine congrArg (T4.c1 c₀ i L es + ·) (sum_congr rfl fun q hq => ?_)
      rw [y_eq_foldAtN4 hc h (by omega) (mem_range.mp hq)]
  · exact (chk2_succ _ _ _ _ _).2 (h.rnd i hi l hl)

/-- **Pf's round checks** from `FinLog4` (round 0: `pf0`, `pf_round0_agree`). -/
theorem pf_of_finLog4 {L es : Log} {y : ℕ → ℕ → K} (h : FinLog4 W₀ c₀ L es y) :
    ∀ l < 7, Chk2 T4.pfStart 32 readK chK (T4.lvC c₀ 5) L es l := by
  intro l hl
  rcases l with _ | l
  · exact (T4.pf_round0_agree (c₀ := c₀) L es).2 h.pf0
  · exact (chk2_succ _ _ _ _ _).2 (h.rndPf l hl)

/-- **Level 4's consistency** from `FinLog4` (`truthP3_four_of_cols`). -/
theorem lvl4_of_finLog4 {L es : Log} {y : ℕ → ℕ → K} (hc : ¬ Collision L) (h : FinLog4 W₀ c₀ L es y) :
    T4.truthP3 (kindOfC es) L es 4 := by
  refine T4.truthP3_four_of_cols hc fun q hq => ?_
  obtain ⟨col, ss, hss, hpath, hy⟩ := h.cols 4 (by norm_num) q hq
  exact ⟨col, ss, hss, hpath, hy ▸ h.enc q hq⟩

/-- **`AcceptTail` from the finals on the log** (3.x's `acceptTail_of_finLog`). -/
theorem acceptTail4_of_finLog {RejF : Log → Log → Prop} {L : Log} {j : ℕ} {y : ℕ → ℕ → K}
    (hb : ¬ Bad L) (hci : G.IsChain L j) (hlen : (entriesOf L (pathOf L j)).length = 482)
    (hR : ¬ RejF L (entriesOf L (pathOf L j))) (h : FinLog4 W₀ c₀ L (entriesOf L (pathOf L j)) y) :
    T4.AcceptTail RejF W₀ c₀ L j := by
  have hc : ¬ Collision L := fun hc => hb (.inl hc)
  exact ⟨hci, by rw [hlen, T4.pfStart_eq], hR, p1_of_finLog4 hc h, pf_of_finLog4 h,
    lvl4_of_finLog4 hc h, h.fin⟩

/-! ## From the run -/

variable {impl : OpImpl} {p : KindP} {inp : Input}

/-- **The K rounds' in-phase checks of an accepted run** (`FinLog4.rnd`, `rndPf`). -/
theorem rounds_of_run4 {tr : Trace} {y : List Val × List Bool × Trace} (h : SkRun4 impl p inp tr y) :
    (∀ i < 5, ∀ l, l + 1 < hEll i → rSum (T4.p1Start i) (fsOf tr (itemsOf seq4)) (l + 1) =
      rVal (T4.p1Start i) (fsOf tr (itemsOf seq4)) l) ∧
    ∀ l, l + 1 < 7 → rSum T4.pfStart (fsOf tr (itemsOf seq4)) (l + 1) =
      rVal T4.pfStart (fsOf tr (itemsOf seq4)) l :=
  ⟨fun _ hi => (p1_view4 h (fi := ⟨(skeleton4 seq4 p).2.outs, [], #[]⟩) rfl hi).choose_spec.2.2.2.2.2,
    (pf_view4 h (fi := ⟨(skeleton4 seq4 p).2.outs, [], #[]⟩) rfl).2.2.2.2.2⟩

/-- **The run's remaining checks on its own entries** (`FinLog4` without its round fields). -/
structure FinRest4 (W₀ : Log → Log → ℕ → K) (c₀ : Log → Log → K) (L es : Log)
    (y : ℕ → ℕ → K) : Prop where
  start : rSum (T4.p1Start 0) es 0 = c₀ L es
  cols : ∀ i < 5, ∀ q < (CKind.lv (kindOfC es) i).t, ∃ col : ByteArray, ∃ ss : List Digest,
    ss.length = (CKind.lv (kindOfC es) i).sib ∧
    (openPath (frEnc i) col (T4.qPos (kindOfC es) es i q) ss).runLog L =
      some (T4.capDig es i (T4.qPos (kindOfC es) es i q / 2 ^ (CKind.lv (kindOfC es) i).sib)) ∧
    y i q = ∑ r : Fin (CKind.lv (kindOfC es) i).rows,
      eqBits (T4.sAt es i) (CKind.lv (kindOfC es) i).ell r * algebraMap F K (readF col (16 * r))
  link : ∀ i < 4, rSum (T4.p1Start (i + 1)) es 0 = T4.c1 c₀ i L es +
    ∑ q ∈ range (CKind.lv (kindOfC es) i).t, K.smulF (eqBits (T4.kcAt es i) 9 q) (y i q)
  pf0 : rSum T4.pfStart es 0 = T4.c1 c₀ 4 L es
  enc : ∀ q < (CKind.lv (kindOfC es) 4).t,
    y 4 q = T4.encAt (kindOfC es) 4 (T4.finalAt es) (T4.qPos (kindOfC es) es 4 q)
  fin : clR2 T4.pfStart 32 readK chK (T4.lvC c₀ 5) L es 7 = T4.wHatL W₀ L es 4 *
    (∏ v ∈ Ico (T4.mLog (kindOfC es) 4) 7, (1 - T4.pfP es v)) * mleN 7 (T4.finalAt es) (T4.pfPt es)

/-- **`AcceptTail` from an accepted run** (`chain`, `len` by `runLog_chain4`; the K rounds by
`rounds_of_run4`): for every run trace `tr` of `gen4 seq4 p fin` inside the log whose entries carry
`¬ RejF` and `FinRest4`, the run's chain is an `AcceptTail`. -/
theorem acceptTail4_of_run {RejF : Log → Log → Prop} (fin : FinOps) {L : Log}
    (hb : ¬ Bad L) (hπ : inp.π.size = piSizeOf seq4)
    (hrun : (runIR impl (gen4 seq4 p fin) inp).runLog L = some true)
    (hacc : ∀ tr, semIR impl (gen4 seq4 p fin) inp tr = some true → (∀ e ∈ tr, e ∈ L) →
      ∃ y, SkRun4 impl p inp tr y ∧ ¬ RejF L (fsOf tr (itemsOf seq4)) ∧
        ∃ yv, FinRest4 W₀ c₀ L (fsOf tr (itemsOf seq4)) yv) :
    ∃ j, T4.AcceptTail RejF W₀ c₀ L j := by
  obtain ⟨tr, hsem, hin, j, hci, hes, hlen⟩ := runLog_chain4 impl p fin hb hπ hrun
  obtain ⟨y, hS, hR, yv, hF⟩ := hacc tr hsem hin
  obtain ⟨hrnd, hrndPf⟩ := rounds_of_run4 hS
  refine ⟨j, acceptTail4_of_finLog (y := yv) hb hci hlen (hes ▸ hR) ?_⟩
  rw [hes]
  exact ⟨hrnd, hrndPf, hF.start, hF.cols, hF.link, hF.pf0, hF.enc, hF.fin⟩

/-! ## `rejF`: P4a's checks (phases 0 … 12) on an accepted run -/

/-- **`RejF4a` never holds on an accepted segment run** (R4d's and R4e's `not_rej*`; the op
parameters are the front statements', `segC_params` discharges them for `implSeg (implC …)`). -/
theorem not_rejF4a_seg4 {σ : SegKind} {tr : Trace}
    (hLS : ∀ v l pe, v.size = 127 → impl.lagrangeS v l pe = Impl.lagrangeSS v l pe)
    (hTS : ∀ r, impl.targetS (KindP.ofSeg σ).tix r = Rev4.targetSSegS r)
    (hW : ∀ rw cw, rw.size = 2 ^ 14 → cw.size = 2 ^ 14 →
      impl.walkAB rw cw = (Eval.walkSpecA rw cw, Eval.walkSpecB rw cw))
    (hR : ∀ l a, impl.rowW l a = Impl.rowWS l a) (hZ : ∀ a b, impl.eqZ a b = Impl.eqZS a b)
    (hST : ∀ k a b c, c.size = 22 → impl.shiftTarget k a b c = FR.Impl.shiftTargetS k a b c)
    (indN : NodeKind → Fin 9 → ℕ → F) (etN : NodeKind → ℕ → Fin (2 ^ 14) → F)
    (h : semIR impl (gen4 seq4 (.ofSeg σ) (finOps4 (segFinP σ))) inp tr = some true) (L : Log) :
    ¬ P4a.RejF4a (P4a.zlm4 indN etN) L (fsOf tr (itemsOf seq4)) := by
  rintro (hz | hl2 | hlc | hlcn | hs)
  · exact not_rejZ_seg4 hLS hTS indN etN h L hz
  · exact not_rejL2_4 (segFinP σ) rfl h L hl2
  · exact (not_rejLc_seg4 hW hR hZ indN etN h L).1 hlc
  · exact (not_rejLc_seg4 hW hR hZ indN etN h L).2 hlcn
  · exact not_rejS2_seg4 hST h L hs

/-- **… nor on an accepted node run** (at the node maps `zlm4 indN4 etN4`, `peL_node4`'s). -/
theorem not_rejF4a_node4 {ν : NodeKind} {cells : List ℕ} {tr : Trace}
    (hLS : ∀ v l pe, v.size = 127 → impl.lagrangeS v l pe = Impl.lagrangeSS v l pe)
    (hTS : ∀ r, impl.targetS (KindP.ofNode ν).tix r = NT4.targetSNode4S ν r)
    (hW : ∀ rw cw, rw.size = 2 ^ 14 → cw.size = 2 ^ 14 →
      impl.walkAB rw cw = (Eval.walkSpecA rw cw, Eval.walkSpecB rw cw))
    (hR : ∀ l a, impl.rowW l a = Impl.rowWS l a) (hZ : ∀ a b, impl.eqZ a b = Impl.eqZS a b)
    (hST : ∀ k a b c, c.size = 22 → impl.shiftTarget k a b c = FR.Impl.shiftTargetS k a b c)
    (h : semIR impl (gen4 seq4 (.ofNode ν) (finOps4 (nodeFinP ν cells))) inp tr = some true) (L : Log) :
    ¬ P4a.RejF4a (P4a.zlm4 N4c.indN4 N4c.etN4) L (fsOf tr (itemsOf seq4)) := by
  rintro (hz | hl2 | hlc | hlcn | hs)
  · exact not_rejZ_node4 hLS hTS h L hz
  · exact not_rejL2_4 (nodeFinP ν cells) rfl h L hl2
  · exact (not_rejLc_node4 hW hR hZ N4c.indN4 N4c.etN4 h L).1 hlc
  · exact (not_rejLc_node4 hW hR hZ N4c.indN4 N4c.etN4 h L).2 hlcn
  · exact not_rejS2_node4 hST h L hs

/-! ## Controls -/

/-- **Control (converse on the round fields)**: a `T4.AcceptTail` gives back `FinLog4`'s round
fields, `start`, `pf0` and `fin`; they ask no more than the tail reads. -/
theorem finLog4_rounds_of_acceptTail {RejF : Log → Log → Prop} {L : Log} {j : ℕ}
    (h : T4.AcceptTail RejF W₀ c₀ L j) :
    let es := entriesOf L (pathOf L j)
    (∀ i < 5, ∀ l, l + 1 < hEll i → rSum (T4.p1Start i) es (l + 1) = rVal (T4.p1Start i) es l) ∧
    (∀ l, l + 1 < 7 → rSum T4.pfStart es (l + 1) = rVal T4.pfStart es l) ∧
    rSum (T4.p1Start 0) es 0 = c₀ L es ∧ rSum T4.pfStart es 0 = T4.c1 c₀ 4 L es ∧
    clR2 T4.pfStart 32 readK chK (T4.lvC c₀ 5) L es 7 = T4.wHatL W₀ L es 4 *
      (∏ v ∈ Ico (T4.mLog (kindOfC es) 4) 7, (1 - T4.pfP es v)) * mleN 7 (T4.finalAt es) (T4.pfPt es) :=
  ⟨fun i hi l hl => h.p1 i hi (l + 1) hl, fun l hl => h.pf (l + 1) hl, h.p1 0 (by norm_num) 0
    (by unfold hEll; decide), (T4.pf_round0_agree (c₀ := c₀) _ _).1 (h.pf 0 (by norm_num)), h.fin⟩

/-- **Control (negative)**: a wrong first claim refutes `FinLog4` and `FinRest4`, whatever the rest. -/
theorem not_finLog4_of_start {L es : Log} {y : ℕ → ℕ → K} (h : rSum (T4.p1Start 0) es 0 ≠ c₀ L es) :
    ¬ FinLog4 W₀ c₀ L es y ∧ ¬ FinRest4 W₀ c₀ L es y := ⟨fun hF => h hF.start, fun hF => h hF.start⟩

/-- **Control (negative)**: on the empty log no level-0 column opens, so `FinLog4` fails as soon as
level 0 has a query. -/
theorem not_finLog4_nil {es : Log} {y : ℕ → ℕ → K} (ht : 0 < (CKind.lv (kindOfC es) 0).t) :
    ¬ FinLog4 W₀ c₀ [] es y := by
  intro hF
  obtain ⟨col, ss, -, hpath, -⟩ := hF.cols 0 (by norm_num) 0 ht
  simp [openPath, OProg.runLog] at hpath

/-- **Control**: `clValK` reads the K first claim: `.zero`'s is `F` zero, not `K` zero (+/−), `.uni`'s
the register (+). -/
theorem clValK_ctl (inp : Input) (o : ℕ) (r : Array Val) (u : Reg) :
    clValK inp .zero o r u = .f 0 ∧ clValK inp .zero o r u ≠ .k 0 ∧ clValK inp .uni o r u = rd r u :=
  ⟨rfl, by simp [clValK, initVals], rfl⟩

/-- **Control (+)**: one claim `[]` at index 0 with `r″ = []` (`Φ = id`) weighs every cell `1`. -/
theorem wTab_one (κ' : F) (fac : ℕ → F) (y : ℕ) : wTab [] κ' fac [[]] 0 y = 1 := by
  simp [wTab, eqPts]; rfl

/-- **Control (−)**: no claims, no weight. -/
theorem wTab_nil (r : List F) (κ' : F) (fac : ℕ → F) (i₀ y : ℕ) : wTab r κ' fac [] i₀ y = 0 := by
  simp [wTab]

/-- **Control**: `rsWS4` is the node's `rsWeightS4` (+) and, on a segment, 3.x's `rsWeightS` at
`β = 1` (+); claim 2's stage weight at a node is not 3.x's (`KW4.kwS4_ne_3x`, −). -/
theorem rsWS4_ctl (ν : NodeKind) (σ : SegKind) (es : Log) (ρ : List K) :
    rsWS4 (.node ν) es ρ = Impl.rsWeightS4 ν (P4b.rsRL4 es).toArray
      ((P4b.rsPtsL4 (.node ν) es).map fun p => (p.map (algebraMap F K)).toArray)
      (P4b.rsKL4 es) (fAt es 98 0) ρ.toArray ∧
    rsWS4 (.seg σ) es ρ = Impl.rsWeightS (P4b.rsRL4 es).toArray
      ((P4b.rsPtsL4 (.seg σ) es).map fun p => (p.map (algebraMap F K)).toArray)
      (P4b.rsKL4 es) 1 ρ.toArray ∧
    KW4.kwS4 .N4 18 0 (cube KW4.tS4) (cube KW4.tS4) ≠ KW.kwS 18 0 (cube KW4.tS4) (cube KW4.tS4) :=
  ⟨rfl, rfl, KW4.kwS4_ne_3x⟩

end FR.Snd.R4
