-- New for `flock-recursive` (BLUEPRINT §3, A.4, A.9; stage S-G12′, S-G11 handover §7 item 1a).
-- RET-2: the declarations revision 4.1 reads moved to `FRSoundnessCoreAcc`.
import FRSoundnessFrRnd
import FRSoundness4P4aSeg

/-!
# The front's degree-2 F rounds: the claims on the skeleton's registers

The view S-G11's handover (§7, 1a) names as missing: a degree-2 F rounds phase's (L2, S2) first
and last claim registers. On an accepted skeleton (`SkRun`), for a phase `n` of shape
`.rounds f K 2 false real` with a free first claim and every round real (`K ≤ real κ`):

* **`roundsF2_view`**: register `claim0` (`b + 2`) holds `rSumF (phStart n) es 0` (round 0's
  `g(0) + g(1)`, i.e. `c₁ + c₂` in characteristic 2), the last register holds
  `rValF (phStart n) es (K − 1)` (the last round's `g(r)`), and for `l + 1 < K` the round checks
  `rSumF … (l + 1) = rValF … l` hold.

`rSumF`/`rValF` are `clR2`'s pieces at `wd = 16`, `rd = readF`, `ch = chF · 0` (`rValF_eq_clR2`,
`chk2_iff`).
-/

namespace FR.Snd
open RecursionFast Finset FR.Impl

/-- Round `l`'s `g(0) + g(1)` on the log (F, `wd = 16`). -/
def rSumF (b : ℕ) (es : Log) (l : ℕ) : F :=
  peval (g2At b 16 readF es l) 0 + peval (g2At b 16 readF es l) 1

/-- Round `l`'s `g(r_l)` on the log. -/
def rValF (b : ℕ) (es : Log) (l : ℕ) : F :=
  peval (g2At b 16 readF es l) (rch2 b (fun d => chF d 0) es l)

theorem rSumF_eq (b : ℕ) (es : Log) (l : ℕ) :
    rSumF b es l = readF (msgAt es (b + 2 * l)) 16 + readF (msgAt es (b + 2 * l)) 32 := by
  rw [rSumF, g2At, charTwo_peval01F]

theorem rValF_eq (b : ℕ) (es : Log) (l : ℕ) :
    rValF b es l = readF (msgAt es (b + 2 * l)) 0 + chF (ansAt es (b + 2 * l + 1)) 0 *
      (readF (msgAt es (b + 2 * l)) 16 + chF (ansAt es (b + 2 * l + 1)) 0 *
        readF (msgAt es (b + 2 * l)) 32) := by
  rw [rValF, g2At, rch2, peval_three]; ring

/-- `clR2` after `l + 1` rounds is round `l`'s `g(r)`. -/
theorem rValF_eq_clR2 (b : ℕ) (c0 : Log → Log → F) (L es : Log) (l : ℕ) :
    clR2 b 16 readF (fun d => chF d 0) c0 L es (l + 1) = rValF b es l := rfl

/-- Round `l + 1`'s check is `rSumF (l + 1) = rValF l`. -/
theorem chk2_iff (b : ℕ) (c0 : Log → Log → F) (L es : Log) (l : ℕ) :
    Chk2 b 16 readF (fun d => chF d 0) c0 L es (l + 1) ↔ rSumF b es (l + 1) = rValF b es l := Iff.rfl

theorem readF_fsQ {vk c : Digest} {π : Proof} {es : Log}
    (hq : ∀ p < 468, (es.getD p default).1 = X.fsQ vk c π p (es.getD (p - 1) default).2)
    {p o len off : ℕ} (hp : p < 468) (hp0 : 0 < p) (hm : X.fsMsgs.getD p none = some (o, len))
    (hoff : off + 16 ≤ len) :
    readF (msgAt es p) off = F.ofBytes (bytesAt π (o + off) 16) := by
  rw [readF, msgAt_fsQ hq hp hp0 hm, bytesAt_extract_of_le16 π hoff]

/-! ## The degree-2 F rounds' registers and flags -/

/-- **`roundsT2F_vals`**: `n` degree-2 F rounds leave 13 registers each; register `12` of a real
round `l` is its `g(r)`. -/
theorem roundsT2F_vals (inp : Input) (f o real : ℕ) :
    ∀ (n j : ℕ) (d : Digest) (cv : Val) (tr : Trace) (x : List Val × Bool × Trace),
      roundsT inp f o 2 false real n j d cv tr = some x →
      x.1.length = 13 * n ∧ ∀ l < n, j + l < real →
        x.1.getD (13 * l + 12) default = .f (g2 inp f (o + (j + l) * 48) (sqAns tr l))
  | 0, _, _, _, _, x, h => by
    simp only [roundsT, Option.some.injEq] at h; subst h
    exact ⟨rfl, fun l hl => absurd hl (by omega)⟩
  | n + 1, j, d, cv, (q₁, a₁) :: (q₂, a₂) :: tr, x, h => by
    simp only [roundsT, Bool.false_eq_true, ite_false, show (2 = 3) = False by decide] at h
    split_ifs at h with hq
    obtain ⟨x', hx', rfl⟩ := Option.map_eq_some_iff.mp h
    obtain ⟨ih1, ih2⟩ := roundsT2F_vals inp f o real n (j + 1) a₂ _ tr x' hx'
    have hl13 : (round2Vals inp f (o + j * roundBytes false) (decide (j < real)) a₁ a₂ cv).length =
      13 := rfl
    refine ⟨by rw [List.length_append, hl13, ih1]; ring, fun l hl hj => ?_⟩
    rcases l with _ | l
    · simp [round2Vals, sqAns, roundBytes, show j < real by omega]
    · rw [show 13 * (l + 1) + 12 = 13 + (13 * l + 12) by ring,
        List.getD_append_right _ _ _ _ (by omega), hl13, Nat.add_sub_cancel_left, sqAns_succ,
        ih2 l (by omega) (by omega), show j + 1 + l = j + (l + 1) by omega]
  | _ + 1, _, _, _, [], _, h => by simp [roundsT] at h
  | _ + 1, _, _, _, [_], _, h => by simp [roundsT] at h

/-- **An accepted run of real degree-2 F rounds checks each round against the previous one**:
round `l + 1`'s `c₁ + c₂` is round `l`'s `g(r)`, and round `0`'s is the claim. -/
theorem roundsT2F_chk (inp : Input) (f o real : ℕ) :
    ∀ (n j : ℕ) (d : Digest) (cv : Val) (tr : Trace) (x : List Val × Bool × Trace),
      roundsT inp f o 2 false real n j d cv tr = some x → x.2.1 = true → j + n ≤ real →
      (0 < n → (Val.f (elemAt inp f (o + j * 48 + 16) + elemAt inp f (o + j * 48 + 32))).eqv cv
        = true) ∧
      ∀ l, l + 1 < n → elemAt inp f (o + (j + l + 1) * 48 + 16) +
          elemAt inp f (o + (j + l + 1) * 48 + 32) = g2 inp f (o + (j + l) * 48) (sqAns tr l)
  | 0, _, _, _, _, _, _, _, _ => ⟨fun h => absurd h (by omega), fun l hl => by omega⟩
  | n + 1, j, d, cv, (q₁, a₁) :: (q₂, a₂) :: tr, x, h, hx, hr => by
    simp only [roundsT, Bool.false_eq_true, ite_false, show (2 = 3) = False by decide] at h
    split_ifs at h with hq
    obtain ⟨x', hx', rfl⟩ := Option.map_eq_some_iff.mp h
    simp only [show decide (j < real) = true from decide_eq_true (by omega), Bool.not_true,
      Bool.false_or, Bool.true_or, Bool.and_true, Bool.and_eq_true] at hx
    have ih := roundsT2F_chk inp f o real n (j + 1) a₂ _ tr x' hx' hx.2 (by omega)
    refine ⟨fun _ => by simpa [roundBytes] using hx.1, fun l hl => ?_⟩
    rcases l with _ | l
    · have h0 := ih.1 (by omega)
      simp only [round2Vals, List.getLastD_eq_getLast?, List.getLast?_cons_cons,
        List.getLast?_singleton, Option.getD_some] at h0
      rw [ite_pos' (decide_eq_true (by omega)), eqv_f] at h0
      simpa [sqAns, roundBytes, Nat.add_assoc] using h0
    · have := ih.2 l (by omega)
      simpa [sqAns, Nat.add_assoc, Nat.add_comm 1, Nat.mul_add, Nat.add_mul] using this
  | _ + 1, _, _, _, [], _, h, _, _ => by simp [roundsT] at h
  | _ + 1, _, _, _, [_], _, h, _, _ => by simp [roundsT] at h

/-! ## On the log -/

theorem rSumF_fsQ {vk c : Digest} {π : Proof} {es : Log}
    (hq : ∀ p < 468, (es.getD p default).1 = X.fsQ vk c π p (es.getD (p - 1) default).2)
    {n f K deg : ℕ} {real : KC ℕ} (hn : n < phases.length)
    (hsh : (phases[n]'hn).shape = .rounds f K deg false real) (hf : f ≤ nFields) {l : ℕ}
    (hl : l < K) (hp : phStart n + 2 * l < 468) (hp0 : 0 < phStart n + 2 * l) :
    rSumF (phStart n) es l = elemAt ⟨vk, c, π⟩ f (phaseOff n f + l * 48 + 16) +
      elemAt ⟨vk, c, π⟩ f (phaseOff n f + l * 48 + 32) := by
  have hm := (fsMsgs_round hn hsh hl).1
  simp only [roundBytes, Bool.false_eq_true, ite_false] at hm
  rw [rSumF_eq, readF_fsQ hq hp hp0 hm (by norm_num), readF_fsQ hq hp hp0 hm (by norm_num)]
  simp only [elemAt, absOff_eq hf, Nat.add_assoc]

theorem rValF_fsQ {vk c : Digest} {π : Proof} {es : Log}
    (hq : ∀ p < 468, (es.getD p default).1 = X.fsQ vk c π p (es.getD (p - 1) default).2)
    {n f K deg : ℕ} {real : KC ℕ} (hn : n < phases.length)
    (hsh : (phases[n]'hn).shape = .rounds f K deg false real) (hf : f ≤ nFields) {l : ℕ}
    (hl : l < K) (hp : phStart n + 2 * l < 468) (hp0 : 0 < phStart n + 2 * l) :
    rValF (phStart n) es l =
      g2 ⟨vk, c, π⟩ f (phaseOff n f + l * 48) (ansAt es (phStart n + 2 * l + 1)) := by
  have hm := (fsMsgs_round hn hsh hl).1
  simp only [roundBytes, Bool.false_eq_true, ite_false] at hm
  rw [rValF_eq, readF_fsQ hq hp hp0 hm (by norm_num), readF_fsQ hq hp hp0 hm (by norm_num),
    readF_fsQ hq hp hp0 hm (by norm_num)]
  simp only [g2, elemAt, absOff_eq hf, Nat.add_assoc, Nat.add_zero]

variable {impl : OpImpl} {κ : Kind} {inp : Input}

/-- A degree-2 F rounds phase with a free first claim: its out list. -/
theorem genPhase_roundsF2 {n : ℕ} {p : Phase} (c : GCtx) {f K : ℕ} {real : KC ℕ}
    (hsh : p.shape = .rounds f K 2 false real) (hnm : initClaim p.name = .free) (hK : 0 < K) :
    (genPhase n p c).2.outs.back?.getD [] = (c.next + 2) ::
        (List.range K).map (fun j => c.next + 13 * j + 6) ++ [c.next + 13 * K + 2] := by
  obtain ⟨name, sh⟩ := p
  simp only at hsh hnm; subst hsh
  have e1 : ∀ j, c.next + 3 + 13 * j + 3 = c.next + 13 * j + 6 := fun j => by ring
  have e2 : c.next + 3 + 13 * K - 1 = c.next + 13 * K + 2 := by omega
  simp [genPhase, hnm, initOps, Init.width, roundW, e1, e2, show K ≠ 0 by omega]

/-- **A degree-2 F rounds phase's claims on the skeleton's registers** (every round real, a free
first claim). With `b` its first register: `outs[n] = (b + 2) :: rs ++ [b + 13K + 2]`; `b + 2`
holds round 0's `g(0) + g(1)`, the last register the last round's `g(r)`; the round checks hold. -/
theorem roundsF2_view {tr : Trace} {y : List Val × List Bool × Trace} (h : SkRun impl κ inp tr y)
    {n : ℕ} (hn : n < phases.length) {f K : ℕ} {real : KC ℕ}
    (hsh : phases[n].shape = .rounds f K 2 false real) (hnm : initClaim phases[n].name = .free)
    (hf : f ≤ nFields) (hK : 0 < K) (hr : K ≤ real κ) (hn0 : 0 < n) :
    ∃ b, skeleton.2.outs.getD n [] = (b + 2) ::
        (List.range K).map (fun j => b + 13 * j + 6) ++ [b + 13 * K + 2] ∧
      b + 13 * K + 3 ≤ (#[] ++ y.1.toArray).size ∧
      rd (#[] ++ y.1.toArray) (b + 2) = .f (rSumF (phStart n) (fsOf tr items) 0) ∧
      rd (#[] ++ y.1.toArray) (b + 13 * K + 2) = .f (rValF (phStart n) (fsOf tr items) (K - 1)) ∧
      ∀ l, l + 1 < K → rSumF (phStart n) (fsOf tr items) (l + 1) = rValF (phStart n) (fsOf tr items) l := by
  obtain ⟨trk, M, x, hx, hb, hwf, hext, hflag, hdrop, -⟩ := phase_at impl κ inp h.ref hn
  have hst : (cAt n).st < (#[] ++ M.toArray).size := by
    rcases hwf with ⟨h', -⟩ | h'
    · rw [hsh] at h'; cases h'
    · exact h'.1
  obtain ⟨seg, hseg, hsl, -⟩ := refPhase_chain inp κ impl hx (by simpa using hb)
    (by rw [hsh]; exact decide_eq_true hf) (q0 := 1) (by simp [hsh, isSeed]) (.inr hst)
  obtain ⟨cl, xr, hxr, rfl⟩ := refPhase_roundsF hsh hx
  rw [hnm] at hext
  obtain ⟨hv1, hv2⟩ := roundsT2F_vals inp f (phaseOff n f) (real κ) K 0 _ _ trk xr hxr
  obtain ⟨hpos, hent⟩ := phase_entries hn hdrop hseg hsl
    (by rw [hsh]; exact rounds_items_fs _ _ _ _ _) (by rw [hsh, rounds_items_length]; omega)
  rw [hsh, rounds_items_length] at hpos hent
  rw [h.len] at hpos
  have hp0 := phStart_pos hn0 hn
  have hsq : ∀ l < K, sqAns trk l = ansAt (fsOf tr items) (phStart n + 2 * l + 1) := fun l hl => by
    rw [sqAns, hent _ (by omega)]; rfl
  have hiv : (initVals inp .free f (phaseOff n f) false).length = 3 := rfl
  have hrd : ∀ m < 3 + 13 * K, rd (#[] ++ y.1.toArray) (M.length + m) =
      (initVals inp .free f (phaseOff n f) false ++ xr.1).getD m default := fun m hm => by
    have hlt : M.length + m < (#[] ++ (M ++ (initVals inp .free f (phaseOff n f) false ++
        xr.1)).toArray).size := by simp [hiv, hv1]; omega
    rw [hext.2 _ hlt, show (#[] : Array Val) ++ (M ++ _).toArray =
      (#[] ++ M.toArray) ++ (initVals inp .free f (phaseOff n f) false ++ xr.1).toArray by simp,
      show M.length = (#[] ++ M.toArray).size by simp, rd_app]
  have hsz : M.length + 3 + 13 * K ≤ (#[] ++ y.1.toArray).size := by
    have := hext.1; simp [hiv, hv1] at this ⊢; omega
  refine ⟨M.length, ?_, by omega, ?_, ?_, ?_⟩
  · rw [skeleton_outs hn, genPhase_roundsF2 (cAt n) hsh hnm hK, hb]
  · rw [hrd 2 (by omega), rSumF_fsQ h.hq hn hsh hf hK (by omega) (by omega)]
    simp [initVals]
  · obtain ⟨k, rfl⟩ : ∃ k, K = k + 1 := ⟨K - 1, by omega⟩
    rw [show M.length + 13 * (k + 1) + 2 = M.length + (3 + (13 * k + 12)) by ring,
      hrd _ (by omega), List.getD_append_right _ _ _ _ (by omega), hiv, Nat.add_sub_cancel_left,
      hv2 k (by omega) (by omega), hsq k (by omega), Nat.add_sub_cancel,
      rValF_fsQ h.hq hn hsh hf (by omega) (by omega) (by omega), Nat.zero_add]
  · intro l hl
    have hflag' : xr.2.1 = true := h.flags _ hflag
    have hc := (roundsT2F_chk inp f (phaseOff n f) (real κ) K 0 _ _ trk xr hxr hflag' (by omega)).2 l hl
    rw [rSumF_fsQ h.hq hn hsh hf hl (by omega) (by omega), rValF_fsQ h.hq hn hsh hf (by omega)
      (by omega) (by omega), ← hsq l (by omega)]
    simpa [Nat.add_assoc] using hc

/-! ## Z2's challenge `λ` -/

theorem genPhase_uni {n : ℕ} {p : Phase} (c : GCtx) {f : ℕ} (hsh : p.shape = .uni f) :
    (genPhase n p c).2.outs.back?.getD [] = [c.next + 3, c.next + 133, c.next + 134] := by
  obtain ⟨name, sh⟩ := p
  simp only at hsh; subst hsh
  simp [genPhase]

/-- **The univariate phase's challenge on the skeleton's registers** (Z2): its first out register
holds `fAt es (phStart n + 1) 0`, the squeeze's F challenge `λ`. -/
theorem uni_view {tr : Trace} {y : List Val × List Bool × Trace} (h : SkRun impl κ inp tr y)
    {n : ℕ} (hn : n < phases.length) {f : ℕ} (hsh : phases[n].shape = .uni f) (hf : f ≤ nFields) :
    ∃ b, (skeleton.2.outs.getD n []).headD 0 = b + 3 ∧ b + 3 < (#[] ++ y.1.toArray).size ∧
      rd (#[] ++ y.1.toArray) (b + 3) = .f (fAt (fsOf tr items) (phStart n + 1) 0) := by
  obtain ⟨trk, M, x, hx, hb, hwf, hext, -, hdrop, -⟩ := phase_at impl κ inp h.ref hn
  have hst : (cAt n).st < (#[] ++ M.toArray).size := by
    rcases hwf with ⟨h', -⟩ | h'
    · rw [hsh] at h'; cases h'
    · exact h'.1
  obtain ⟨seg, hseg, hsl, -⟩ := refPhase_chain inp κ impl hx (by simpa using hb)
    (by rw [hsh]; exact decide_eq_true hf) (q0 := 1) (by simp [hsh, isSeed]) (.inr hst)
  have hit : phases[n].shape.items.length = 2 := by rw [hsh]; rfl
  obtain ⟨-, hent⟩ := phase_entries hn hdrop hseg hsl
    (by rw [hsh]; simp [Shape.items, Item.isFS]) (by omega)
  rw [hit] at hent
  have hout : skeleton.2.outs.getD n [] = [M.length + 3, M.length + 133, M.length + 134] := by
    rw [skeleton_outs hn, genPhase_uni (cAt n) hsh, hb]
  have hx' : refPhase impl κ inp n ⟨phases[n].name, .uni f⟩ (cAt n) (#[] ++ M.toArray) trk =
      some x := by rw [← hsh]; exact hx
  clear hx
  simp only [refPhase] at hx'
  rcases trk with _ | ⟨⟨q₁, a₁⟩, _ | ⟨⟨q₂, a₂⟩, trk⟩⟩
  · cases hx'
  · cases hx'
  simp only at hx'
  split_ifs at hx'
  cases hx'
  have h1 := hent 1 (by norm_num)
  simp only [List.getD_cons_succ, List.getD_cons_zero] at h1
  have hsz := size_le_of_ext hext
  simp only [uniVals, uniEs, List.length_append, List.length_cons, List.length_map,
    List.length_range, List.length_nil] at hsz
  refine ⟨M.length, ?_, ?_, ?_⟩
  · rw [hout]; rfl
  · exact Nat.lt_of_lt_of_le (Nat.add_lt_add_left (by norm_num) _) hsz
  · rw [rd_phase hext (m := 3) (by simp [uniVals, uniEs])]
    simp only [uniVals, List.cons_append, List.getD_cons_succ, List.getD_cons_zero]
    rw [fAt, ansAt, entAt, ← h1]

end FR.Snd
