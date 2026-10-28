-- New for `flock-recursive` (BLUEPRINT §3, A.4, A.9; stage S-G4, `hFin` step 2b).
import FRSoundnessAccSeg

/-!
# `hFin`, step 2b: the skeleton's registers by shape, read on the log

On an accepted skeleton (`SkRun`: `refPhases` ran, every flag is up, and the run's Fiat–Shamir
entries `es = fsOf tr items` are `fsQ`'s chain), the registers that the finals read hold the
log's values:

* **`.rounds` over K** (P1.i, Pf; **`rounds_view`**): the out list is
  `cl :: rs ++ [last]`; `cl` holds round 0's `c₁ + c₂` (`rSum … 0`), `rs[j]` round `j`'s
  challenge (`chK` of its squeeze's answer), `last` the last round's `g(r)` (`rVal … (K − 1)`),
  and the in-phase checks hold (`rSum (l + 1) = rVal l`). `roundsT_vals` reads the 13 registers
  of a K round.
* `cAt_succ`: the context after phase `n` is `genPhase`'s; a rounds phase over K sets `foldR`.
-/

namespace FR.Snd
open RecursionFast

/-! ## The K rounds' registers -/

theorem sqAns_succ (q₁ q₂ : ByteArray) (a₁ a₂ : Digest) (tr : Trace) (l : ℕ) :
    sqAns ((q₁, a₁) :: (q₂, a₂) :: tr) (l + 1) = sqAns tr l := by
  simp only [sqAns, show 2 * (l + 1) + 1 = 2 * l + 1 + 1 + 1 by ring, List.getD_cons_succ]

/-- **`roundsT_vals`**: `n` K rounds leave 13 registers each; register `3` of round `l` is its
challenge `chK a₂`, register `12` (a real round) its `g(r)`. -/
theorem roundsT_vals (inp : Input) (f o real : ℕ) :
    ∀ (n j : ℕ) (d : Digest) (cv : Val) (tr : Trace) (x : List Val × Bool × Trace),
      roundsT inp f o 2 true real n j d cv tr = some x →
      x.1.length = 13 * n ∧ ∀ l < n, x.1.getD (13 * l + 3) default = .k (chK (sqAns tr l)) ∧
        (j + l < real → x.1.getD (13 * l + 12) default =
          .k (gK inp f (o + (j + l) * 96) (sqAns tr l)))
  | 0, _, _, _, _, x, h => by
    simp only [roundsT, Option.some.injEq] at h; subst h
    exact ⟨rfl, fun l hl => absurd hl (by omega)⟩
  | n + 1, j, d, cv, (q₁, a₁) :: (q₂, a₂) :: tr, x, h => by
    simp only [roundsT, ite_true] at h
    split_ifs at h with hq
    obtain ⟨x', hx', rfl⟩ := Option.map_eq_some_iff.mp h
    obtain ⟨ih1, ih2⟩ := roundsT_vals inp f o real n (j + 1) a₂ _ tr x' hx'
    have hl13 : (roundKVals inp f (o + j * roundBytes true) (decide (j < real)) a₁ a₂ cv).length =
      13 := rfl
    refine ⟨by rw [List.length_append, hl13, ih1]; ring, fun l hl => ?_⟩
    rcases l with _ | l
    · refine ⟨rfl, fun hj => ?_⟩
      simp [roundKVals, sqAns, roundBytes, show j < real by omega]
    · obtain ⟨i1, i2⟩ := ih2 l (by omega)
      rw [show 13 * (l + 1) + 3 = 13 + (13 * l + 3) by ring,
        show 13 * (l + 1) + 12 = 13 + (13 * l + 12) by ring,
        List.getD_append_right _ _ _ _ (by omega), List.getD_append_right _ _ _ _ (by omega), hl13,
        Nat.add_sub_cancel_left, Nat.add_sub_cancel_left, sqAns_succ]
      refine ⟨i1, fun hj => ?_⟩
      rw [i2 (by omega), show j + 1 + l = j + (l + 1) by omega]
  | _ + 1, _, _, _, [], _, h => by simp [roundsT] at h
  | _ + 1, _, _, _, [_], _, h => by simp [roundsT] at h

variable {impl : OpImpl} {κ : Kind} {inp : Input}

/-- A rounds phase over K with a free first claim, unfolded. -/
theorem refPhase_roundsK {n : ℕ} {p : Phase} {c : GCtx} {r : Array Val} {tr : Trace}
    {x : List Val × Bool × Trace} {f K : ℕ} {real : KC ℕ}
    (hsh : p.shape = .rounds f K 2 true real) (hnm : initClaim p.name = .free)
    (hx : refPhase impl κ inp n p c r tr = some x) :
    ∃ xr, roundsT inp f (phaseOff n f) 2 true (real κ) K 0 (rd r c.st).toD
        (.k (elemKAt inp f (phaseOff n f + 32) + elemKAt inp f (phaseOff n f + 64))) tr = some xr ∧
      x = (initVals inp .free f (phaseOff n f) true ++ xr.1, xr.2.1, xr.2.2) := by
  obtain ⟨name, sh⟩ := p
  simp only at hsh hnm; subst hsh
  simp only [refPhase, hnm] at hx
  obtain ⟨xr, h1, rfl⟩ := Option.map_eq_some_iff.1 hx
  exact ⟨xr, by simpa [initVals] using h1, rfl⟩

/-- A rounds phase over K with a free first claim: its out list and its fold registers. -/
theorem genPhase_roundsK {n : ℕ} {p : Phase} (c : GCtx) {f K : ℕ} {real : KC ℕ}
    (hsh : p.shape = .rounds f K 2 true real) (hnm : initClaim p.name = .free) :
    (genPhase n p c).2.outs.back?.getD [] = (c.next + 2) ::
        (List.range K).map (fun j => c.next + 13 * j + 6) ++
          [if K = 0 then c.next + 2 else c.next + 13 * K + 2] ∧
      (genPhase n p c).2.foldR = (List.range K).map (fun j => c.next + 13 * j + 6) := by
  obtain ⟨name, sh⟩ := p
  simp only at hsh hnm; subst hsh
  have e1 : ∀ j, c.next + 3 + 13 * j + 3 = c.next + 13 * j + 6 := fun j => by ring
  have e2 : c.next + 3 + 13 * K - 1 = c.next + 13 * K + 2 := by omega
  simp [genPhase, hnm, initOps, Init.width, e1, e2]

theorem genPhases_append : ∀ (l₁ l₂ : List Phase) (n : ℕ) (c : GCtx),
    (genPhases (l₁ ++ l₂) n c).2 = (genPhases l₂ (n + l₁.length) (genPhases l₁ n c).2).2
  | [], _, _, _ => rfl
  | p :: l₁, l₂, n, c => by
    simp only [List.cons_append, genPhases, List.length_cons]
    rw [genPhases_append l₁ l₂ (n + 1), show n + 1 + l₁.length = n + (l₁.length + 1) by omega]

/-- The context after phase `n` is `genPhase`'s at `cAt n`. -/
theorem cAt_succ {n : ℕ} (hn : n < phases.length) :
    cAt (n + 1) = (genPhase n phases[n] (cAt n)).2 := by
  rw [cAt, List.take_add_one, List.getElem?_eq_getElem hn, Option.toList_some, genPhases_append,
    List.length_take, min_eq_left (by omega), Nat.zero_add]
  rfl

/-! ## The run's Fiat–Shamir entries per phase -/

/-- **An accepted skeleton**: its `refPhases` run, every flag up, its Fiat–Shamir entries the
chain of `fsQ` (`fsQ_gen`). -/
structure SkRun (impl : OpImpl) (κ : Kind) (inp : Input) (tr : Trace)
    (y : List Val × List Bool × Trace) : Prop where
  ref : refPhases impl κ inp phases 0 ctx₀ #[] tr = some y
  flags : ∀ b ∈ y.2.1, b = true
  len : (fsOf tr items).length = 468
  hq : ∀ p < 468, ((fsOf tr items).getD p default).1 =
    X.fsQ inp.vk inp.c inp.π p ((fsOf tr items).getD (p - 1) default).2

/-- Control (positive): an accepted run of `gen fin (.fixed κ)` whose fields ask nothing is a
`SkRun` (`accept_fields`, `fsQ_gen`). -/
theorem skRun_of_accept {impl : OpImpl} {κ : Kind} {inp : Input} (fin : Finals) {tr : Trace}
    (hna : ∀ f ∈ fin.finRS :: fin.rest, ∀ fi b, (f fi b).1.filterMap Op.item? = [])
    (h : semIR impl (gen fin (.fixed κ)) inp tr = some true) :
    ∃ y, SkRun impl κ inp tr y := by
  obtain ⟨y, hy, hf, -⟩ := accept_fields impl κ inp fin hna h
  obtain ⟨hl, hq⟩ := fsQ_gen inp impl fin _ h
  exact ⟨y, hy, hf, hl, hq⟩

/-- Control (negative): the empty trace is no accepted skeleton (it has no Fiat–Shamir entries). -/
theorem not_skRun_nil {impl : OpImpl} {κ : Kind} {inp : Input} (y : List Val × List Bool × Trace) :
    ¬ SkRun impl κ inp [] y := fun h => by
  have := h.len; simp [fsOf] at this

/-- On an all-Fiat–Shamir phase, the trace's entries are the chain's from `phStart`. -/
theorem seg_entries {es trk seg rest : Trace} {s : ℕ} {its more : List Item}
    (hdrop : es.drop s = fsOf trk (its ++ more)) (htrk : trk = seg ++ rest)
    (hl : seg.length = its.length) (hfs : ∀ it ∈ its, it.isFS = true) (hne : 0 < its.length) :
    s + its.length ≤ es.length ∧ ∀ m < its.length, trk.getD m default = es.getD (s + m) default := by
  rw [htrk, fsOf_append hl, fsOf_all hfs hl] at hdrop
  have hlen := congrArg List.length hdrop
  simp only [List.length_drop, List.length_append] at hlen
  refine ⟨by omega, fun m hm => ?_⟩
  have := congrArg (fun l => l.getD m default) hdrop
  simp only [List.getD_eq_getElem?_getD, List.getElem?_drop] at this
  rw [htrk, List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD,
    List.getElem?_append_left (by omega), this, List.getElem?_append_left (by omega)]

theorem rounds_items_fs (f K deg : ℕ) (inK : Bool) (real : KC ℕ) :
    ∀ it ∈ (Shape.rounds f K deg inK real).items, it.isFS = true := by
  intro it hit
  simp only [Shape.items, List.mem_flatten, List.mem_replicate] at hit
  obtain ⟨l, ⟨-, rfl⟩, hit⟩ := hit
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hit
  rcases hit with rfl | rfl <;> rfl

theorem phStart_pos {n : ℕ} (hn0 : 0 < n) (hn : n < phases.length) : 0 < phStart n := by
  rw [phStart_eq_sum hn]
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  have h0 : phases = ⟨"seed", .seed⟩ :: phases.tail := rfl
  rw [h0, List.take_succ_cons, List.map_cons, List.sum_cons]
  simp [Shape.items, Item.isFS]

/-- **Phase `n`'s entries on the log** (an all-Fiat–Shamir phase): its trace segment is the
chain's entries from `phStart n`. -/
theorem phase_entries {tr : Trace} {n : ℕ}
    (hn : n < phases.length) {trk seg rest : Trace}
    (hdrop : (fsOf tr items).drop (phStart n) = fsOf trk (psItems (phases.drop n)))
    (htrk : trk = seg ++ rest) (hl : seg.length = phases[n].shape.items.length)
    (hfs : ∀ it ∈ phases[n].shape.items, it.isFS = true) (hne : 0 < phases[n].shape.items.length) :
    phStart n + phases[n].shape.items.length ≤ (fsOf tr items).length ∧
      ∀ m < phases[n].shape.items.length,
        trk.getD m default = (fsOf tr items).getD (phStart n + m) default := by
  rw [List.drop_eq_getElem_cons hn] at hdrop
  exact seg_entries hdrop htrk hl hfs hne

/-! ## The K rounds on the log -/

theorem rounds_items_length (f K deg : ℕ) (inK : Bool) (real : KC ℕ) :
    (Shape.rounds f K deg inK real).items.length = 2 * K := by
  simp [Shape.items, List.sum_replicate]; ring

/-- **A K rounds phase of the accepted skeleton, on the log** (a free first claim, every round
real). With `b` its first register: `outs[n] = (b + 2) :: rs ++ [b + 13K + 2]`, `rs[j] = b + 13j + 6`
is the next context's `foldR`; `b + 2` holds `rSum … 0`, `rs[j]` round `j`'s challenge, the last
register `rVal … (K − 1)`; the in-phase checks hold. -/
theorem rounds_view {tr : Trace} {y : List Val × List Bool × Trace} (h : SkRun impl κ inp tr y)
    {n : ℕ} (hn : n < phases.length) {f K : ℕ} {real : KC ℕ}
    (hsh : phases[n].shape = .rounds f K 2 true real) (hnm : initClaim phases[n].name = .free)
    (hf : f ≤ nFields) (hK : 0 < K) (hr : K ≤ real κ) (hn0 : 0 < n) :
    ∃ b, skeleton.2.outs.getD n [] = (b + 2) ::
        (List.range K).map (fun j => b + 13 * j + 6) ++ [b + 13 * K + 2] ∧
      (cAt (n + 1)).foldR = (List.range K).map (fun j => b + 13 * j + 6) ∧
      b + 13 * K + 3 ≤ (#[] ++ y.1.toArray).size ∧
      rd (#[] ++ y.1.toArray) (b + 2) = .k (rSum (phStart n) (fsOf tr items) 0) ∧
      (∀ j < K, rd (#[] ++ y.1.toArray) (b + 13 * j + 6) =
        .k (chK (ansAt (fsOf tr items) (phStart n + 2 * j + 1)))) ∧
      rd (#[] ++ y.1.toArray) (b + 13 * K + 2) = .k (rVal (phStart n) (fsOf tr items) (K - 1)) ∧
      ∀ l, l + 1 < K → rSum (phStart n) (fsOf tr items) (l + 1) = rVal (phStart n) (fsOf tr items) l := by
  obtain ⟨trk, M, x, hx, hb, hwf, hext, hflag, hdrop, -⟩ := phase_at impl κ inp h.ref hn
  have hst : (cAt n).st < (#[] ++ M.toArray).size := by
    rcases hwf with ⟨h', -⟩ | h'
    · rw [hsh] at h'; cases h'
    · exact h'.1
  obtain ⟨seg, hseg, hsl, -⟩ := refPhase_chain inp κ impl hx (by simpa using hb)
    (by rw [hsh]; exact decide_eq_true hf) (q0 := 1) (by simp [hsh, isSeed]) (.inr hst)
  obtain ⟨xr, hxr, rfl⟩ := refPhase_roundsK hsh hnm hx
  obtain ⟨hv1, hv2⟩ := roundsT_vals inp f (phaseOff n f) (real κ) K 0 _ _ trk xr hxr
  obtain ⟨hpos, hent⟩ := phase_entries hn hdrop hseg hsl
    (by rw [hsh]; exact rounds_items_fs _ _ _ _ _) (by rw [hsh, rounds_items_length]; omega)
  rw [hsh, rounds_items_length] at hpos hent
  rw [h.len] at hpos
  have hp0 := phStart_pos hn0 hn
  have hsq : ∀ l < K, sqAns trk l = ansAt (fsOf tr items) (phStart n + 2 * l + 1) := fun l hl => by
    rw [sqAns, hent _ (by omega)]; rfl
  have hiv : (initVals inp .free f (phaseOff n f) true).length = 3 := rfl
  -- reading the phase's registers on the skeleton's
  have hrd : ∀ m < 3 + 13 * K, rd (#[] ++ y.1.toArray) (M.length + m) =
      (initVals inp .free f (phaseOff n f) true ++ xr.1).getD m default := fun m hm => by
    have hlt : M.length + m < (#[] ++ (M ++ (initVals inp .free f (phaseOff n f) true ++
        xr.1)).toArray).size := by simp [hiv, hv1]; omega
    rw [hext.2 _ hlt, show (#[] : Array Val) ++ (M ++ _).toArray =
      (#[] ++ M.toArray) ++ (initVals inp .free f (phaseOff n f) true ++ xr.1).toArray by simp,
      show M.length = (#[] ++ M.toArray).size by simp, rd_app]
  have hsz : M.length + 3 + 13 * K ≤ (#[] ++ y.1.toArray).size := by
    have := hext.1; simp [hiv, hv1] at this ⊢; omega
  refine ⟨M.length, ?_, ?_, by omega, ?_, ?_, ?_, ?_⟩
  · rw [skeleton_outs hn, (genPhase_roundsK (cAt n) hsh hnm).1, hb, if_neg (by omega)]
  · rw [cAt_succ hn, (genPhase_roundsK (cAt n) hsh hnm).2, hb]
  · rw [hrd 2 (by omega), rSum_fsQ h.hq hn hsh hf hK (by omega) (by omega)]
    simp [initVals]
  · intro j hj
    rw [show M.length + 13 * j + 6 = M.length + (3 + (13 * j + 3)) by ring, hrd _ (by omega),
      List.getD_append_right _ _ _ _ (by omega), hiv, Nat.add_sub_cancel_left, (hv2 j hj).1,
      hsq j hj]
  · obtain ⟨k, rfl⟩ : ∃ k, K = k + 1 := ⟨K - 1, by omega⟩
    rw [show M.length + 13 * (k + 1) + 2 = M.length + (3 + (13 * k + 12)) by ring,
      hrd _ (by omega), List.getD_append_right _ _ _ _ (by omega), hiv, Nat.add_sub_cancel_left,
      (hv2 k (by omega)).2 (by omega), hsq k (by omega), Nat.add_sub_cancel,
      rVal_fsQ h.hq hn hsh hf (by omega) (by omega) (by omega), Nat.zero_add]
  · intro l hl
    have hflag' : xr.2.1 = true := h.flags _ hflag
    have hc := (roundsT_chk inp f (phaseOff n f) (real κ) K 0 _ _ trk xr hxr hflag' (by omega)).2 l hl
    rw [rSum_fsQ h.hq hn hsh hf hl (by omega) (by omega), rVal_fsQ h.hq hn hsh hf (by omega)
      (by omega) (by omega), ← hsq l (by omega)]
    simpa [Nat.add_assoc] using hc

end FR.Snd
