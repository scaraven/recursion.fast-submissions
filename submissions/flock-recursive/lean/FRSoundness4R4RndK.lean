-- New for `flock-recursive` (BLUEPRINT revision 4.1, A.9 P1.i and Pf, the K sumcheck rounds; track
-- R4f). The 3.x templates are `FRSoundnessAccVal.rounds_view` and `FRSoundnessAccPf`.
import FRSoundness4R4FrCtrlB
import FRSoundness4R4W0

/-!
# The K rounds of an accepted `gen4` run, on the log (P1.i, Pf)

A K rounds phase `n` of `phasesOf seq4` (`.rounds f k 2 true`, first claim `.free`) runs `k` real rounds
(`realRounds p name k = k` for every name but the F ones). On the log the phase's entries sit at
`P = phStart4 n`, and a round's query is `absorbQ d msg`, so the log's message *is* π's
(`msgAt_of_q`); no message table is needed.

* **`roundsK_log`**: from claim `clR2 P 32 readK chK c₀ … j`, the claim after `n` real rounds is
  `clR2 … (j + n)`, and on a passing run every round's check `Chk2 P …` holds;
* **`roundsK_view4`** (3.x's `rounds_view`): on the skeleton's registers, `outs[n]` is
  `(b + 2) :: (b + 13j + 6)_j ++ [b + 13k + 2]`; `b + 2` holds `rSum P es 0`, `b + 13j + 6` round
  `j`'s challenge `rch2 P chK es j`, `b + 13k + 2` the last claim `rVal P es (k − 1)`; every round
  `l + 1`'s check `rSum P es (l + 1) = rVal P es l` holds;
* **`p1_view4`**, **`pf_view4`**: P1.i (phase `26 + 5i`, `hEll i` rounds) and Pf (phase 51, 7
  rounds) by name (`lvOuts`, `outsOf`, `chals`, `claim0`, `claimN`).
-/

namespace FR.Snd.R4
open RecursionFast Rev4 FR.Impl

/-! ## Real K rounds on the log -/

theorem readK_piMsg (inp : Input) (o off : ℕ) {len : ℕ} (h : off + 32 ≤ len) :
    readK (FR.msgAt inp 0 o len) off = elemKAt inp 0 (o + off) := by
  simp only [readK, FR.msgAt, elemKAt, absOff_zero]
  rw [bytesAt_extract_le _ h]

/-- A K round's two entries on the log: its message is π's, its challenge the answer's. -/
theorem round_entriesK {inp : Input} {o P j : ℕ} {es : Log} {q₁ q₂ : ByteArray} {a₁ a₂ d : Digest}
    {tr : Trace} (hq : q₁ = absorbQ d (FR.msgAt inp 0 (o + j * roundBytes true) (roundBytes true)))
    (he : ∀ m < 2, ((q₁, a₁) :: (q₂, a₂) :: tr).getD m default = es.getD (P + 2 * j + m) default) :
    (∀ off, off + 32 ≤ 96 → readK (Snd.msgAt es (P + 2 * j)) off = elemKAt inp 0 (o + j * 96 + off)) ∧
      ansAt es (P + 2 * j + 1) = a₂ := by
  have e0 := he 0 (by norm_num); have e1 := he 1 (by norm_num)
  simp only [List.getD_cons_zero, List.getD_cons_succ, Nat.add_zero] at e0 e1
  refine ⟨fun off hoff => ?_, by rw [ansAt, entAt, ← e1]⟩
  rw [msgAt_of_q (p := P + 2 * j) (by rw [← e0]; exact hq)]
  exact readK_piMsg inp _ off hoff

/-- **K rounds on the log** (all real): from claim `clR2 P … j`, the claim after `n` rounds is
`clR2 P … (j + n)`; on a passing run every round's check holds. -/
theorem roundsK_log (inp : Input) (o real P : ℕ) (es : Log) (c0 : Log → Log → K) (L : Log) :
    ∀ (n j : ℕ) (d : Digest) (cv : Val) (tr : Trace) (x : List Val × Bool × Trace),
      roundsT inp 0 o 2 true real n j d cv tr = some x →
      (∀ m < 2 * n, tr.getD m default = es.getD (P + 2 * j + m) default) →
      j + n ≤ real → cv = .k (clR2 P 32 readK chK c0 L es j) →
      x.1.getLastD cv = .k (clR2 P 32 readK chK c0 L es (j + n)) ∧
        (x.2.1 = true → ∀ l < n, Chk2 P 32 readK chK c0 L es (j + l))
  | 0, j, _, cv, _, x, h, _, _, hc => by
    simp only [roundsT, Option.some.injEq] at h; subst h
    exact ⟨by rw [Nat.add_zero]; exact hc, fun _ l hl => absurd hl (by omega)⟩
  | n + 1, j, d, cv, (q₁, a₁) :: (q₂, a₂) :: tr, x, h, he, hj, hc => by
    simp only [roundsT, ite_true] at h
    split_ifs at h with hq
    obtain ⟨x', hx', rfl⟩ := Option.map_eq_some_iff.mp h
    obtain ⟨hm, ha⟩ := round_entriesK hq.1 (fun m hm => he m (by omega))
    have hjr : j < real := by omega
    have hne : roundKVals inp 0 (o + j * roundBytes true) (decide (j < real)) a₁ a₂ cv ≠ [] := by
      simp [roundKVals]
    have hg : (roundKVals inp 0 (o + j * roundBytes true) (decide (j < real)) a₁ a₂ cv).getLastD
        default = .k (clR2 P 32 readK chK c0 L es (j + 1)) := by
      simp only [roundKVals, decide_eq_true hjr, ite_true, List.getLastD_eq_getLast?,
        List.getLast?_cons_cons, List.getLast?_singleton, Option.getD_some, clR2, g2At, rch2, ha,
        peval_three, gK, roundBytes]
      rw [hm 0 (by norm_num), hm 32 (by norm_num), show 2 * 32 = 64 by norm_num,
        hm 64 (by norm_num), Nat.add_zero]
      exact congrArg Val.k (by ring_nf)
    obtain ⟨ih1, ih2⟩ := roundsK_log inp o real P es c0 L n (j + 1) a₂ _ tr x' (hg ▸ hx')
      (shift_entries he) (by omega) rfl
    refine ⟨?_, fun hx l hl => ?_⟩
    · rw [getLastD_append', getLastD_of_ne hne cv default, hg, ih1,
        show j + 1 + n = j + (n + 1) by omega]
    · simp only [decide_eq_true hjr, Bool.not_true, Bool.false_or, Bool.true_or, Bool.and_true,
        Bool.and_eq_true] at hx
      rcases l with _ | l
      · have h0 := hx.1
        simp only [roundBytes, ite_true, hc, eqv_k] at h0
        rw [Nat.add_zero, Chk2, g2At, charTwo_peval01, hm 32 (by norm_num),
          show 2 * 32 = 64 by norm_num, hm 64 (by norm_num)]
        exact h0
      · rw [show j + (l + 1) = j + 1 + l by omega]
        exact ih2 hx.2 l (by omega)
  | _ + 1, _, _, _, [], _, h, _, _, _ => by simp [roundsT] at h
  | _ + 1, _, _, _, [_], _, h, _, _, _ => by simp [roundsT] at h

/-! ## A K rounds phase of the accepted skeleton -/

/-- The claim register's value a K rounds phase starts from (`refPhase4`'s `cl` at `inK = true`). -/
def clValK (inp : Input) (init : Init) (o : ℕ) (r : Array Val) (u : Reg) : Val :=
  match init with
  | .uni => rd r u
  | _ => (initVals inp init 0 o true).getLastD default

/-- **A K rounds phase's out list** (`genPhase4`, first claim `.free`): the first claim, the `k` challenges,
the last claim. -/
theorem genPhase4_roundsK (S : Seq) (p : KindP) (n : ℕ) (name : String) (f k : ℕ) (c : GCtx)
    (hnm : initClaim name = .free) (hk : 0 < k) :
    (genPhase4 S p n (name, .rounds f k 2 true) c).2.outs.back?.getD [] =
      (c.next + 2) :: (List.range k).map (fun j => c.next + 13 * j + 6) ++ [c.next + 13 * k + 2] := by
  simp only [genPhase4]
  rw [hnm]
  simp only [initOps, Init.width, Array.back?_push, Option.getD_some,
    Nat.pos_iff_ne_zero.mp hk, ↓reduceIte]
  have e : (fun j => c.next + 3 + 13 * j + 3) = (fun j => c.next + 13 * j + 6) := funext fun j => by omega
  rw [e, show c.next + 3 + 13 * k - 1 = c.next + 13 * k + 2 by omega]

variable {impl : OpImpl} {p : KindP} {inp : Input}

/-- **A K rounds phase of an accepted run** (`.rounds f k 2 true`): `rounds_at4` for the K rounds. -/
theorem rounds_atK4 {tr : Trace} {y : List Val × List Bool × Trace} (h : SkRun4 impl p inp tr y)
    {n : ℕ} (hn : n < (phasesOf seq4).length) {f k : ℕ}
    (hsh : (phasesOf seq4)[n].2 = .rounds f k 2 true) :
    ∃ (M : List Val) (xr : List Val × Bool × Trace) (trk : Trace),
      (cAt4 seq4 p n).next = M.length ∧
      roundsT inp 0 (fieldOffOf seq4 f + phaseOffOf seq4 n f) 2 true
        (realRounds p (phasesOf seq4)[n].1 k) k 0 (rd (#[] ++ M.toArray) (cAt4 seq4 p n).st).toD
        (clValK inp (initClaim (phasesOf seq4)[n].1) (fieldOffOf seq4 f + phaseOffOf seq4 n f)
          (#[] ++ M.toArray) (cAt4 seq4 p n).uni) trk = some xr ∧
      ExtA (#[] ++ (M ++ (initVals inp (initClaim (phasesOf seq4)[n].1) 0
        (fieldOffOf seq4 f + phaseOffOf seq4 n f) true ++ xr.1)).toArray) (#[] ++ y.1.toArray) ∧
      xr.2.1 = true ∧
      ∀ m < 2 * k, trk.getD m default = (fsOf tr (itemsOf seq4)).getD (phStart4 n + m) default := by
  obtain ⟨trk, M, x, hx, hb, hwf, hext, hflag, hdrop, -⟩ := phase_at4 impl p.tix inp p h.ref hn
  have hok : CtxOk (cAt4 seq4 p n) (#[] ++ M.toArray) := by
    rcases hwf with ⟨h', -⟩ | h'
    · rw [hsh] at h'; cases h'
    · exact h'
  obtain ⟨seg, hseg, hsl, -⟩ := refPhase4_chain impl p.tix inp seq4 p hx (by simpa using hb)
    (by rw [hsh]; rfl) (q0 := 1) (by simp [hsh, isSeed4]) (.inr hok.1)
  generalize hph : (phasesOf seq4)[n] = ph at hx hsh hsl
  obtain ⟨name, sh⟩ := ph
  simp only at hsh; subst hsh
  simp only [refPhase4] at hx
  obtain ⟨xr, hxr, rfl⟩ := Option.map_eq_some_iff.1 hx
  refine ⟨M, xr, trk, hb, ?_, hext, h.flags _ hflag, fun m hm => ?_⟩
  · convert hxr using 2; simp only [clValK]; generalize initClaim name = ic; cases ic <;> rfl
  · have hit : (phasesOf seq4)[n].2.itemsL seq4.lv = (Sh.rounds f k 2 true).itemsL seq4.lv := by
      rw [hph]
    rw [List.drop_eq_getElem_cons hn, psItems4, List.flatMap_cons, hit] at hdrop
    rw [rounds_itemsL_length] at hsl
    obtain ⟨-, hent⟩ := seg_entries hdrop hseg (by rw [hsl, rounds_itemsL_length])
      (itemsL_allFS _ (by simp)) (by rw [rounds_itemsL_length]; omega)
    exact hent m (by rw [rounds_itemsL_length]; exact hm)

/-- **A K rounds phase on the skeleton's registers** (first claim `.free`, all `k` rounds real; 3.x's
`rounds_view`). -/
theorem roundsK_view4 {tr : Trace} {y : List Val × List Bool × Trace} (h : SkRun4 impl p inp tr y)
    {n : ℕ} (hn : n < (phasesOf seq4).length) {f k : ℕ}
    (hsh : (phasesOf seq4)[n].2 = .rounds f k 2 true)
    (hnm : initClaim (phasesOf seq4)[n].1 = .free) (hr : realRounds p (phasesOf seq4)[n].1 k = k)
    (hk : 0 < k) :
    ∃ b : ℕ, (skeleton4 seq4 p).2.outs.getD n [] =
        (b + 2) :: (List.range k).map (fun j => b + 13 * j + 6) ++ [b + 13 * k + 2] ∧
      b + 13 * k + 3 ≤ (#[] ++ y.1.toArray).size ∧
      rd (#[] ++ y.1.toArray) (b + 2) = .k (rSum (phStart4 n) (fsOf tr (itemsOf seq4)) 0) ∧
      (∀ j < k, rd (#[] ++ y.1.toArray) (b + 13 * j + 6) =
        .k (rch2 (phStart4 n) chK (fsOf tr (itemsOf seq4)) j)) ∧
      rd (#[] ++ y.1.toArray) (b + 13 * k + 2) =
        .k (rVal (phStart4 n) (fsOf tr (itemsOf seq4)) (k - 1)) ∧
      ∀ l, l + 1 < k → rSum (phStart4 n) (fsOf tr (itemsOf seq4)) (l + 1) =
        rVal (phStart4 n) (fsOf tr (itemsOf seq4)) l := by
  obtain ⟨M, xr, trk, hb, hxr, hext, hfl, hent⟩ := rounds_atK4 h hn hsh
  have hout := skeleton4_outs seq4 p hn
  generalize hph : (phasesOf seq4)[n] = ph at hsh hxr hext hout hnm hr
  obtain ⟨name, sh⟩ := ph
  simp only at hsh hnm hr; subst hsh
  simp only at hxr hext ⊢
  rw [hr] at hxr
  rw [genPhase4_roundsK seq4 p n name f k _ hnm hk, hb] at hout
  generalize hes : fsOf tr (itemsOf seq4) = es at hent ⊢
  generalize fieldOffOf seq4 f + phaseOffOf seq4 n f = o at hxr hext ⊢
  generalize hR0 : #[] ++ y.1.toArray = R0 at hext ⊢
  rw [hnm] at hxr hext
  -- the first claim is round 0's `c₁ + c₂`
  have he0 : ∀ m < 2 * k, trk.getD m default = es.getD (phStart4 n + 2 * 0 + m) default :=
    fun m hm => by rw [Nat.mul_zero, Nat.add_zero]; exact hent m hm
  have hc0 : clValK inp .free o (#[] ++ M.toArray) (cAt4 seq4 p n).uni =
      .k (clR2 (phStart4 n) 32 readK chK (fun _ es => rSum (phStart4 n) es 0) [] es 0) := by
    obtain ⟨k', rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
    match trk, hxr, he0 with
    | (q₁, a₁) :: (q₂, a₂) :: tr', hxr, he0 =>
      simp only [roundsT, ite_true] at hxr
      split_ifs at hxr with hq
      obtain ⟨hm, -⟩ := round_entriesK (j := 0) (by simpa using hq.1) (fun m hm => he0 m (by omega))
      simp only [Nat.mul_zero, Nat.add_zero, Nat.zero_mul] at hm
      simp only [clValK, initVals, ite_true, List.getLastD_eq_getLast?, List.getLast?_cons_cons,
        List.getLast?_singleton, Option.getD_some, clR2, rSum_eq, Nat.mul_zero, Nat.add_zero]
      rw [hm 32 (by norm_num), hm 64 (by norm_num)]
    | [], hxr, _ => simp [roundsT] at hxr
    | [_], hxr, _ => simp [roundsT] at hxr
  rw [hc0] at hxr
  obtain ⟨hl1, hl2⟩ := roundsK_log inp o k (phStart4 n) es (fun _ es => rSum (phStart4 n) es 0) []
    k 0 _ _ trk xr hxr he0 (by omega) rfl
  obtain ⟨hv1, hv2⟩ := roundsT_vals inp 0 o k k 0 _ _ trk xr hxr
  have hiv : (initVals inp .free 0 o true).length = 3 := rfl
  have hsz := size_le_of_ext hext
  simp only [List.length_append, hiv, hv1] at hsz
  have hrd : ∀ m < 3 + 13 * k, rd R0 (M.length + m) = (initVals inp .free 0 o true ++ xr.1).getD m default :=
    fun m hm => rd_phase4 hext (by simp [hiv, hv1]; omega)
  refine ⟨M.length, hout, by omega, ?_, fun j hj => ?_, ?_, fun l hl => ?_⟩
  · rw [hrd 2 (by omega)]
    have e2 : (initVals inp .free 0 o true ++ xr.1).getD 2 default =
        clValK inp .free o (#[] ++ M.toArray) (cAt4 seq4 p n).uni := by
      simp [initVals, clValK]
    rw [e2, hc0]; rfl
  · rw [show M.length + 13 * j + 6 = M.length + (3 + (13 * j + 3)) by ring, hrd _ (by omega),
      List.getD_append_right _ _ _ _ (by omega), hiv, Nat.add_sub_cancel_left, (hv2 j hj).1, sqAns,
      hent _ (by omega), rch2]
    rfl
  · obtain ⟨k', rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
    have hne : xr.1 ≠ [] := by intro he; rw [he] at hv1; simp at hv1
    rw [show M.length + 13 * (k' + 1) + 2 = M.length + (3 + (13 * k' + 12)) by ring,
      hrd _ (by omega), List.getD_append_right _ _ _ _ (by omega), hiv, Nat.add_sub_cancel_left]
    have hl := hl1
    rw [getLastD_of_ne hne _ default, List.getLastD_eq_getLast?, List.getLast?_eq_getElem?, hv1,
      Nat.zero_add] at hl
    rw [show 13 * (k' + 1) - 1 = 13 * k' + 12 by omega] at hl
    rw [← List.getD_eq_getElem?_getD] at hl
    rw [hl, Nat.add_sub_cancel]
    rfl
  · have := (hl2 hfl (l + 1) hl)
    rw [Nat.zero_add] at this
    exact this

/-! ## P1.i and Pf by name -/

theorem phases4_p1 (S : Seq) {i : ℕ} (hi : i < 5) :
    (phasesOf S)[26 + 5 * i]? = some ("P1", .rounds fP1 (S.lv i).ell 2 true) := by
  interval_cases i <;> rfl

theorem phases4_pf (S : Seq) : (phasesOf S)[51]? = some ("Pf", .rounds fPf S.pf 2 true) := rfl

theorem seq4_ell {i : ℕ} (hi : i < 5) : (seq4.lv i).ell = hEll i := by
  rw [seq4_eq]; interval_cases i <;> rfl

theorem seq4_pf : seq4.pf = 7 := by rw [seq4_eq]

theorem lvOuts_eq4 {fi : FinIn} (hfi : fi.outs = (skeleton4 seq4 p).2.outs) (i : ℕ) :
    lvOuts fi i 0 = (skeleton4 seq4 p).2.outs.getD (26 + 5 * i) [] := by
  rw [lvOuts, hfi, phaseIx_P1, Nat.add_zero]

/-- **P1.i's registers on the log** (3.x's `p1_facts`): its challenges are `sAt es i j`, its first
claim `rSum (p1Start i) es 0`, its last `rVal … (hEll i − 1)`, and every round `l + 1`'s check
holds. -/
theorem p1_view4 {tr : Trace} {y : List Val × List Bool × Trace} (h : SkRun4 impl p inp tr y)
    {fi : FinIn} (hfi : fi.outs = (skeleton4 seq4 p).2.outs) {i : ℕ} (hi : i < 5) :
    ∃ b, lvOuts fi i 0 = (b + 2) :: (List.range (hEll i)).map (fun j => b + 13 * j + 6) ++
        [b + 13 * hEll i + 2] ∧
      (∀ j < hEll i, rd (#[] ++ y.1.toArray) (b + 13 * j + 6) = .k (T4.sAt (fsOf tr (itemsOf seq4)) i j)) ∧
      rd (#[] ++ y.1.toArray) (p1Claim0 fi i) = .k (rSum (T4.p1Start i) (fsOf tr (itemsOf seq4)) 0) ∧
      rd (#[] ++ y.1.toArray) (p1ClaimN fi i) =
        .k (rVal (T4.p1Start i) (fsOf tr (itemsOf seq4)) (hEll i - 1)) ∧
      (∀ x ∈ lvOuts fi i 0, x < (#[] ++ y.1.toArray).size) ∧
      ∀ l, l + 1 < hEll i → rSum (T4.p1Start i) (fsOf tr (itemsOf seq4)) (l + 1) =
        rVal (T4.p1Start i) (fsOf tr (itemsOf seq4)) l := by
  obtain ⟨hn, e⟩ := ph4 (phases4_p1 seq4 hi)
  have hsh : (phasesOf seq4)[26 + 5 * i].2 = .rounds fP1 (hEll i) 2 true := by rw [e, seq4_ell hi]
  have hnm : initClaim (phasesOf seq4)[26 + 5 * i].1 = .free := by rw [e]; rfl
  have hr : realRounds p (phasesOf seq4)[26 + 5 * i].1 (hEll i) = hEll i := by rw [e]; rfl
  obtain ⟨b, hout, -, h0, hrs, hlast, hchk⟩ :=
    roundsK_view4 h hn hsh hnm hr (by interval_cases i <;> decide)
  have hl0 := (lvOuts_eq4 hfi i).trans hout
  refine ⟨b, hl0, fun j hj => ?_, ?_, ?_, ?_, hchk⟩
  · rw [hrs j hj]; simp only [rch2, T4.sAt, kAt]
  · rw [p1Claim0, hl0, List.cons_append, List.headD_cons, h0]; rfl
  · rw [p1ClaimN, hl0, List.cons_append, List.getLastD_cons, List.getLastD_eq_getLast?,
      List.getLast?_append, List.getLast?_singleton]
    simpa [T4.p1Start] using hlast
  · rw [lvOuts_eq4 hfi]; exact skeleton4_out_lt p h.ref _

/-- **Pf's registers on the log** (3.x's `pf_facts`). -/
theorem pf_view4 {tr : Trace} {y : List Val × List Bool × Trace} (h : SkRun4 impl p inp tr y)
    {fi : FinIn} (hfi : fi.outs = (skeleton4 seq4 p).2.outs) :
    (∀ v < 7, rd (#[] ++ y.1.toArray) ((chals fi "Pf" 7).getD v 0) =
        .k (T4.pfP (fsOf tr (itemsOf seq4)) v)) ∧
      (chals fi "Pf" 7).length = 7 ∧
      rd (#[] ++ y.1.toArray) (claim0 fi "Pf") = .k (rSum T4.pfStart (fsOf tr (itemsOf seq4)) 0) ∧
      rd (#[] ++ y.1.toArray) (claimN fi "Pf") = .k (rVal T4.pfStart (fsOf tr (itemsOf seq4)) 6) ∧
      (∀ x ∈ outsOf fi "Pf", x < (#[] ++ y.1.toArray).size) ∧
      ∀ l, l + 1 < 7 → rSum T4.pfStart (fsOf tr (itemsOf seq4)) (l + 1) =
        rVal T4.pfStart (fsOf tr (itemsOf seq4)) l := by
  obtain ⟨hn, e⟩ := ph4 (phases4_pf seq4)
  have hsh : (phasesOf seq4)[51].2 = .rounds fPf 7 2 true := by rw [e, seq4_pf]
  have hnm : initClaim (phasesOf seq4)[51].1 = .free := by rw [e]; rfl
  have hr : realRounds p (phasesOf seq4)[51].1 7 = 7 := by rw [e]; rfl
  obtain ⟨b, hout, -, h0, hrs, hlast, hchk⟩ := roundsK_view4 h hn hsh hnm hr (by norm_num)
  have ho : outsOf fi "Pf" = (b + 2) :: (List.range 7).map (fun j => b + 13 * j + 6) ++
      [b + 13 * 7 + 2] := by rw [outsOf, hfi, phaseIx_Pf, hout]
  have hc : chals fi "Pf" 7 = (List.range 7).map (fun j => b + 13 * j + 6) := by
    rw [chals, ho, List.cons_append, List.drop_one, List.tail_cons]; exact take_rs b 7 _
  refine ⟨fun v hv => ?_, by rw [hc]; simp, ?_, ?_, ?_, hchk⟩
  · rw [hc, List.getD_eq_getElem _ _ (by simpa using hv), List.getElem_map, List.getElem_range,
      hrs v hv]
    simp [T4.pfP, rchs2, List.getD_eq_getElem?_getD, hv, T4.pfStart]
  · rw [claim0, ho, List.cons_append, List.headD_cons, h0]; rfl
  · rw [claimN, ho, List.cons_append, List.getLastD_cons, List.getLastD_eq_getLast?,
      List.getLast?_append, List.getLast?_singleton]
    simpa [T4.pfStart] using hlast
  · rw [outsOf, hfi, phaseIx_Pf]; exact skeleton4_out_lt p h.ref _

end FR.Snd.R4
