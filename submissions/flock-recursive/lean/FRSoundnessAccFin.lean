-- New for `flock-recursive` (BLUEPRINT §5.4, A.9 finals, A.10 rows; stage S-G3).
import FRSoundnessAccRun

/-!
# The finals on the log: `FinLog` and `AcceptTail` (`hAcc`'s SNARK branch, the bridges)

`FinLog W₀ c₀ L es y` is what the accepted verifier's checks say about the chain `es` of the log
`L`, written with the log's reads (`msgAt`, `ansAt`, `sAt`, `kcAt`, `qPos`, `finalAt`, `capDig`),
the verifier's column folds being `y i q`. Each field is one check of A.9 (or of a `.rounds`
phase, `FRVIRSpec.roundsT`):

* `rnd`, `rndPf`: the in-phase round checks of P1.i and Pf, rounds `l ≥ 1`: `g_l(0) + g_l(1)` is
  the previous round's `g_{l−1}(r_{l−1})` (`roundsT`'s `chk`; round 0's claim is `free`);
* `start`: P1.0's first claim is `c₀` (the front's `v*`; `finRS`/`finB′`, parametric here);
* `cols`: P2.i's opened columns: a path to the cap entry (`posAllT`'s Merkle checks) and
  `y_q = Σ_r eq(sᵢ, r)·col_q[r]` (`dotKF` with `eqTable` of P1.i's challenges);
* `link`: `finP i`, `i < 4`: P1.(i+1)'s first claim is `claimN(P1.i) + Σ_q eq(κ_c, bits₉ q)·y_q`;
* `pf0`: `finP 4`'s assert `claim0 Pf = claimN P1.4`;
* `enc`: `finP 4`'s direct checks `y_q = Enc₄(final)[p_q]`;
* `fin`: `finPf`'s `relPf`, at the spec (`DPf_end_chain`'s form).

**`acceptTail_of_finLog`**: on a log without bad events, a chain with `FinLog` and `¬ RejF` is an
`AcceptTail`. The bridges are `foldAt_of_cols` (P1.i, `i ≥ 1`), `pf_round0_agree` (Pf),
`truthP3_four_of_cols` (level 4).

**`finLog_of_acceptTail`** (control, converse on the round fields): `AcceptTail` gives back
`rnd`, `rndPf`, `start`, `pf0`'s round form and `fin`, so these fields ask no more than the tail
uses.

Register-side bridges (Part C): `padV`, `finHat`, the round checks and `relP4`'s assert, read on
registers holding the log's values.
-/

namespace FR.Snd
open RecursionFast FR.Merkle Finset

variable {W₀ : Log → Log → ℕ → K} {c₀ : Log → Log → K}

/-- `g(0) + g(1)` of round `l`'s message of the K rounds starting at `b`. -/
def rSum (b : ℕ) (es : Log) (l : ℕ) : K :=
  peval (g2At b 32 readK es l) 0 + peval (g2At b 32 readK es l) 1

/-- `g_l(r_l)`: round `l`'s message at its challenge. -/
def rVal (b : ℕ) (es : Log) (l : ℕ) : K := peval (g2At b 32 readK es l) (rch2 b chK es l)

/-- **What the accepted verifier's checks say on the log** (A.9's `finP i`, `finPf` and the K
rounds), the verifier's column folds being `y i q`. -/
structure FinLog (W₀ : Log → Log → ℕ → K) (c₀ : Log → Log → K) (L es : Log)
    (y : ℕ → ℕ → K) : Prop where
  /-- P1.i's rounds `l ≥ 1`: `g_l(0) + g_l(1) = g_{l−1}(r_{l−1})`. -/
  rnd : ∀ i < 5, ∀ l, l + 1 < hEll i → rSum (p1Start i) es (l + 1) = rVal (p1Start i) es l
  /-- Pf's rounds `l ≥ 1`. -/
  rndPf : ∀ l, l + 1 < 7 → rSum pfStart es (l + 1) = rVal pfStart es l
  /-- P1.0's first claim is the front's `c₀`. -/
  start : rSum (p1Start 0) es 0 = c₀ L es
  /-- P2.i's opened columns: a path to the cap entry, and `y_q` their fold at `sᵢ`. -/
  cols : ∀ i < 5, ∀ q < (lvl (kindOf es) i).t, ∃ col : ByteArray, ∃ ss : List Digest,
    ss.length = (lvl (kindOf es) i).sib ∧
    (openPath (frEnc i) col (qPos (kindOf es) es i q) ss).runLog L =
      some (capDig es i (qPos (kindOf es) es i q / 2 ^ (lvl (kindOf es) i).sib)) ∧
    y i q = ∑ r : Fin (lvl (kindOf es) i).rows, eqBits (sAt es i) (lvl (kindOf es) i).ell r *
      algebraMap F K (readF col (16 * r))
  /-- `finP i`, `i < 4`: P1.(i+1)'s first claim is P1.i's last plus the batched folds. -/
  link : ∀ i < 4, rSum (p1Start (i + 1)) es 0 = c1 c₀ i L es +
    ∑ q ∈ range (lvl (kindOf es) i).t, K.smulF (eqBits (kcAt es i) 9 q) (y i q)
  /-- `finP 4`'s assert: Pf's first claim is P1.4's last. -/
  pf0 : rSum pfStart es 0 = c1 c₀ 4 L es
  /-- `finP 4`'s direct checks: `y_q = Enc₄(final)[p_q]`. -/
  enc : ∀ q < (lvl (kindOf es) 4).t, y 4 q = encAt (kindOf es) 4 (finalAt es) (qPos (kindOf es) es 4 q)
  /-- `finPf`'s `relPf` at the spec. -/
  fin : clR2 pfStart 32 readK chK (lvC c₀ 5) L es 7 = wHatL W₀ L es 4 *
    (∏ v ∈ Ico (mLog (kindOf es) 4) 7, (1 - pfP es v)) * mleN 7 (finalAt es) (pfPt es)

/-! ## Part A: from `FinLog` to the tail's checks -/

theorem chk2_succ (b : ℕ) (c0 : Log → Log → K) (L es : Log) (l : ℕ) :
    Chk2 b 32 readK chK c0 L es (l + 1) ↔ rSum b es (l + 1) = rVal b es l := Iff.rfl

theorem chk2_zero (b : ℕ) (c0 : Log → Log → K) (L es : Log) :
    Chk2 b 32 readK chK c0 L es 0 ↔ rSum b es 0 = c0 L es := Iff.rfl

/-- **The verifier's fold of a query is `foldAtN`** (the column is the committed one). -/
theorem y_eq_foldAtN {L es : Log} {y : ℕ → ℕ → K} (hc : ¬ Collision L) (h : FinLog W₀ c₀ L es y)
    {i : ℕ} (hi : i < 5) {q : ℕ} (hq : q < (lvl (kindOf es) i).t) :
    y i q = foldAtN (kindOf es) L es i (qPos (kindOf es) es i q) := by
  obtain ⟨col, ss, hss, hpath, hy⟩ := h.cols i hi q hq
  have hlt : qPos (kindOf es) es i q < 2 ^ (lvl (kindOf es) i).logN := idx_lt _ _ _
  rw [foldAtN, dite_eq_left_of_eq_true (eq_true hlt), hy,
    foldAt_of_cols (j := ⟨_, hlt⟩) hc hss hpath]

/-- **P1.i's round checks** from `FinLog` (round 0: `start` for `i = 0`, `link` and the folds for
`i ≥ 1`). -/
theorem p1_of_finLog {L es : Log} {y : ℕ → ℕ → K} (hc : ¬ Collision L) (h : FinLog W₀ c₀ L es y) :
    ∀ i < 5, ∀ l < hEll i, Chk2 (p1Start i) 32 readK chK (lvC c₀ i) L es l := by
  intro i hi l hl
  rcases l with _ | l
  · rw [chk2_zero]
    rcases i with _ | i
    · exact h.start
    · rw [lvC_succ c₀ (by omega), h.link i (by omega), vNext]
      refine congrArg (c1 c₀ i L es + ·) (sum_congr rfl fun q hq => ?_)
      rw [y_eq_foldAtN hc h (by omega) (mem_range.mp hq)]
  · exact (chk2_succ _ _ _ _ _).2 (h.rnd i hi l hl)

/-- **Pf's round checks** from `FinLog` (round 0: `pf0`, `pf_round0_agree`). -/
theorem pf_of_finLog {L es : Log} {y : ℕ → ℕ → K} (h : FinLog W₀ c₀ L es y) :
    ∀ l < 7, Chk2 pfStart 32 readK chK (lvC c₀ 5) L es l := by
  intro l hl
  rcases l with _ | l
  · exact (pf_round0_agree L es).2 h.pf0
  · exact (chk2_succ _ _ _ _ _).2 (h.rndPf l hl)

/-- **Level 4's consistency** from `FinLog` (`truthP3_four_of_cols`). -/
theorem lvl4_of_finLog {L es : Log} {y : ℕ → ℕ → K} (hc : ¬ Collision L) (h : FinLog W₀ c₀ L es y) :
    truthP3 (kindOf es) L es 4 := by
  refine truthP3_four_of_cols hc fun q hq => ?_
  obtain ⟨col, ss, hss, hpath, hy⟩ := h.cols 4 (by norm_num) q hq
  exact ⟨col, ss, hss, hpath, hy ▸ h.enc q hq⟩

/-- **`AcceptTail` from the finals on the log**: a chain of a log without bad events, on which
the front's asserts pass and the verifier's checks hold (`FinLog`), is an `AcceptTail`. -/
theorem acceptTail_of_finLog {RejF : Log → Log → Prop} {L : Log} {j : ℕ} {y : ℕ → ℕ → K}
    (hb : ¬ Bad L) (hci : IsChain L j) (hlen : (entriesOf L (pathOf L j)).length = 468)
    (hR : ¬ RejF L (entriesOf L (pathOf L j))) (h : FinLog W₀ c₀ L (entriesOf L (pathOf L j)) y) :
    AcceptTail RejF W₀ c₀ L j := by
  have hc : ¬ Collision L := fun hc => hb (.inl hc)
  exact ⟨hci, (chain_len_468 hlen).2, hR, p1_of_finLog hc h, pf_of_finLog h, lvl4_of_finLog hc h,
    h.fin⟩

/-! ## Part B: controls -/

/-- **Control (converse on the round fields)**: an `AcceptTail` gives back `FinLog`'s round
fields, `start`, `pf0` and `fin`; they ask no more than the tail reads. -/
theorem finLog_rounds_of_acceptTail {RejF : Log → Log → Prop} {L : Log} {j : ℕ}
    (h : AcceptTail RejF W₀ c₀ L j) :
    let es := entriesOf L (pathOf L j)
    (∀ i < 5, ∀ l, l + 1 < hEll i → rSum (p1Start i) es (l + 1) = rVal (p1Start i) es l) ∧
    (∀ l, l + 1 < 7 → rSum pfStart es (l + 1) = rVal pfStart es l) ∧
    rSum (p1Start 0) es 0 = c₀ L es ∧ rSum pfStart es 0 = c1 c₀ 4 L es ∧
    clR2 pfStart 32 readK chK (lvC c₀ 5) L es 7 = wHatL W₀ L es 4 *
      (∏ v ∈ Ico (mLog (kindOf es) 4) 7, (1 - pfP es v)) * mleN 7 (finalAt es) (pfPt es) :=
  ⟨fun i hi l hl => h.p1 i hi (l + 1) hl, fun l hl => h.pf (l + 1) hl, h.p1 0 (by norm_num) 0
    (by unfold hEll; decide), (pf_round0_agree _ _).1 (h.pf 0 (by norm_num)), h.fin⟩

/-- Control (value): on the empty chain every round message is zero, so `rSum = rVal = 0`. -/
theorem rSum_nil (b l : ℕ) : rSum b [] l = 0 ∧ rVal b [] l = 0 := by
  simp [rSum, rVal, g2At, readK_nil, peval]

/-- **Control (negative)**: a wrong first claim refutes `FinLog`, whatever the rest. -/
theorem not_finLog_of_start {L es : Log} {y : ℕ → ℕ → K} (h : rSum (p1Start 0) es 0 ≠ c₀ L es) :
    ¬ FinLog W₀ c₀ L es y := fun hF => h hF.start

/-- **Control (negative)**: on the empty log, no level-0 column opens (`runLog` of a query on `[]`
is `none`), so `FinLog` fails as soon as level 0 has a query. -/
theorem not_finLog_nil {es : Log} {y : ℕ → ℕ → K} (ht : 0 < (lvl (kindOf es) 0).t) :
    ¬ FinLog W₀ c₀ [] es y := by
  intro hF
  obtain ⟨col, ss, -, hpath, -⟩ := hF.cols 0 (by norm_num) 0 ht
  simp [openPath, OProg.runLog] at hpath

/-! ## Part C: register-side bridges

The verifier reads π and the trace; the tail reads the log's chain. On the run's Fiat–Shamir
entries (`fsQ_gen`) an absorb's message is π's bytes at its `fsMsgs` range (`msgAt_fsQ`), so a K
element the tail reads (`readK`) is the one the verifier reads (`readK_fsQ`). `padV` at Pf's
challenges is the tail's padding (`padV_eq`). -/

theorem extract40_absorbQ (st : Digest) (m : ByteArray) :
    (absorbQ st m).extract 40 (absorbQ st m).size = m := by
  have h : ((absorbQ st m).extract 40 (absorbQ st m).size).data.toList = m.data.toList := by
    rw [toList_extract, absorbQ_data, absorbQ_size]
    simp [tagAbs]
  have h2 := Array.ext' h
  calc (absorbQ st m).extract 40 (absorbQ st m).size
      = ⟨((absorbQ st m).extract 40 (absorbQ st m).size).data⟩ := rfl
    _ = ⟨m.data⟩ := by rw [h2]
    _ = m := rfl

/-- **The log's message at an absorb position is π's bytes there** (on the run's Fiat–Shamir
entries, `fsQ_gen`'s form). -/
theorem msgAt_fsQ {vk c : Digest} {π : Proof} {es : Log}
    (hq : ∀ p < 468, (es.getD p default).1 = X.fsQ vk c π p (es.getD (p - 1) default).2)
    {p o len : ℕ} (hp : p < 468) (hp0 : 0 < p) (hm : X.fsMsgs.getD p none = some (o, len)) :
    msgAt es p = π.extract o (o + len) := by
  unfold msgAt entAt
  rw [hq p hp]
  unfold X.fsQ
  rw [hm]
  dsimp only
  rw [ite_neg' (by omega)]
  exact extract40_absorbQ _ _

theorem bytesAt_extract_of_le (π : Proof) {o len off : ℕ} (h : off + 32 ≤ len) :
    bytesAt (π.extract o (o + len)) off 32 = bytesAt π (o + off) 32 := by
  ext k hk
  rw [getElem_bytesAt _ _ _ _ hk, getElem_bytesAt _ _ _ _ hk, toList_extract,
    Nat.add_sub_cancel_left, List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD,
    List.getElem?_take_of_lt (by omega), List.getElem?_drop, Nat.add_assoc]

/-- **A K element read on the log is π's** (at offset `off` of the absorb at `p`). -/
theorem readK_fsQ {vk c : Digest} {π : Proof} {es : Log}
    (hq : ∀ p < 468, (es.getD p default).1 = X.fsQ vk c π p (es.getD (p - 1) default).2)
    {p o len off : ℕ} (hp : p < 468) (hp0 : 0 < p) (hm : X.fsMsgs.getD p none = some (o, len))
    (hoff : off + 32 ≤ len) :
    readK (msgAt es p) off = K.ofBytes (bytesAt π (o + off) 32) := by
  rw [readK, msgAt_fsQ hq hp hp0 hm, bytesAt_extract_of_le π hoff]

theorem mLog_four (κ : Kind) : mLog κ 4 = if κ = .L32 then 7 else 5 := by cases κ <;> decide

/-- **`finPf`'s padding is the tail's**: with Pf's challenge registers holding `pfP`,
`padV = Π_{mLog₄ ≤ v < 7} (1 − ρ_v)` (characteristic 2: `1 + x = 1 − x`). -/
theorem padV_eq (κ : Kind) (fi : FinIn) (r : Array Val) (es : Log)
    (hx : ∀ v < 7, (rd r ((chals fi "Pf" 7).getD v 0)).toK = pfP es v) :
    padV κ fi r = ∏ v ∈ Ico (mLog κ 4) 7, (1 - pfP es v) := by
  have h1 : ∀ x : K, 1 + x = 1 - x := fun x => by rw [sub_eq_add_neg, CharTwo.neg_eq]
  rw [mLog_four, padV]
  split_ifs with h
  · simp
  · rw [hx 5 (by norm_num), hx 6 (by norm_num), h1, h1,
      show Ico 5 7 = {5, 6} from by decide, prod_pair (by norm_num)]

/-- Control: at the L32 kind there is no padding. -/
theorem padV_L32 (fi : FinIn) (r : Array Val) : padV .L32 fi r = 1 := by simp [padV]

/-- Control: at another kind the padding reads Pf's last two challenges (it is `0` when one of
them is `1`). -/
theorem padV_P30_one (fi : FinIn) (r : Array Val)
    (h : rd r ((chals fi "Pf" 7).getD 5 0) = .k 1) : padV .P30 fi r = 0 := by
  have h2 : (1 : K) + 1 = 0 := CharTwo.add_self_eq_zero 1
  unfold padV
  rw [ite_neg' (by decide), h]
  simp only [Val.toK, h2, zero_mul]

end FR.Snd
