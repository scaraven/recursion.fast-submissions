-- G6: this module also holds the former modules `FRSoundness4R4FrCtrlB`, `FRSoundness4R4RndK`, `FRSoundness4R4Tail`, `FRSoundness4R4Start`, `FRSoundness4R4PosT` (one section each, in import order).
import FRSoundness4R4FrRS
import FRVIRTplRepT
import FRSoundness4R4W0

section G6_FRSoundness4R4FrCtrlB

-- New for `flock-recursive` (BLUEPRINT revision 4.1; stage R4e): controls of R4e's statements.

/-!
# Controls for R4e (`Fields4`, the front's op parameters, the claim switches)

| Definition / parameter | Positive | Negative |
|---|---|---|
| `Fields4` | `fields4_of_accept` (every accepted run has one) | `not_fields4_nil` (no run on an empty trace) |
| the segment's op parameters (`hZ hLS hTS hST hSM hSW hLW hW hR` of `not_rejZ_seg4`, `not_rejS2_seg4`, `not_rejLc_seg4`, `not_rejRS4_seg`) | `segC_params` (the concrete segment ops `implSeg (implC …)` meet all of them) | `clR2_c0_dep` (the claim switch `clR2_c0_eq` needs its hypothesis: round 0's claim is `c0`'s) |
| the node's op parameters (`not_rejZ_node4`, `not_rejS2_node4`, `not_rejLc_node4`, `not_rejRS4_node`) | `nodeC_params` (S-CN4b's `implN4T` over 3.x's ops meets all of them; `targetS` by `targetSNode4_meets`) | as above |
| `lastAt_pad19` | `lastAt_pad19_ctl` (`lastBits` after 19 entries reads back `lastL`) | — (an equation) |
-/

namespace FR.Snd.R4
open RecursionFast Rev4 FR.Impl

variable {impl : OpImpl} {p : KindP} {inp : Input}

/-- (−) **No fields on an empty trace** (an accepted run's chain has 482 entries). -/
theorem not_fields4_nil {P : FinP} {y : List Val × List Bool × Trace} {zh : List Reg}
    {Rs : ℕ → Array Val} {Ex : ℕ → Array (List Reg)} : ¬ Fields4 impl p inp [] P y zh Rs Ex :=
  fun hF => by have := hF.sk.len; simp [fsOf] at this

/-- (+) **The concrete segment ops meet every op parameter of R4e's segment statements.** -/
theorem segC_params (fin : Finals) (lRows : List Circ.Row) (κs₀ : F) (σ : SegKind) :
    let impl := implSeg (implC fin lRows κs₀)
    (∀ a b, impl.eqZ a b = eqZS a b) ∧
      (∀ v l pe, v.size = 127 → impl.lagrangeS v l pe = lagrangeSS v l pe) ∧
      (∀ r, impl.targetS (KindP.ofSeg σ).tix r = targetSSegS r) ∧
      (∀ k a b c, c.size = 22 → impl.shiftTarget k a b c = shiftTargetS k a b c) ∧
      (∀ a b, impl.shiftMask a b = shiftSegS a b) ∧ (∀ κ s a b, impl.slotW κ s a b = slotWS s a b) ∧
      (∀ tt rr, impl.linkWAll (KindP.ofSeg σ).tix tt rr = Array.replicate nLinkFam 0) ∧
      (∀ rw cw, rw.size = 2 ^ 14 → cw.size = 2 ^ 14 →
        impl.walkAB rw cw = (Eval.walkSpecA rw cw, Eval.walkSpecB rw cw)) ∧
      ∀ l a, impl.rowW l a = rowWS l a := by
  intro impl
  have hm := implSegC_meets fin lRows κs₀
  obtain ⟨hST, hSM, hSW, hLW⟩ := segOps_of_meets hm σ
  obtain ⟨h1, h2, h3, -, -, -, h7, -, -, -, -, -, -, -, -, h16, -⟩ := hm
  refine ⟨fun a b => ?_, fun v l pe hv => ?_, fun r => ?_, hST, hSM, hSW, hLW, fun rw cw h1' h2' => ?_,
    fun l a => ?_⟩
  · rw [h3]; simp only [specSeg, Impl.specC, Impl.specCWith]
  · rw [h1 v l pe hv]; simp only [specSeg, Impl.specC, Impl.specCWith]
  · rw [h2]; simp only [specSeg, Impl.specC, Impl.specCWith]; rfl
  · rw [h7 rw cw h1' h2']; simp only [specSeg, Impl.specC, Impl.specCWith]
  · rw [h16]; simp only [specSeg, Impl.specC, Impl.specCWith]

/-- (−) **The claim switch needs its hypothesis**: round 0's claim is `c0`'s, so two different
first claims give different round-0 claims. -/
theorem clR2_c0_dep (L es : Log) :
    clR2 0 16 readF (fun d => chF d 0) (fun _ _ => (0 : F)) L es 0 ≠
      clR2 0 16 readF (fun d => chF d 0) (fun _ _ => (1 : F)) L es 0 := by
  simp [clR2]

/-- (+) `lastAt` reads back `lastL` from `lastBits` placed after 19 entries. -/
theorem lastAt_pad19_ctl (es : Log) :
    lastAt ((List.replicate 19 (0 : F)) ++ P4a.lastBits es).toArray 19 = P4a.lastL es :=
  lastAt_pad19 es _ (by simp)

/-- (+) **S-CN4b's node ops (`implN4T` over 3.x's `implC`) meet every op parameter of R4e's node
statements** (`targetS` through `implN4T_meets`, i.e. `targetSNode4_meets`). -/
theorem nodeC_params (fin : Finals) (lRows : List Circ.Row) (κs₀ : F) (ν : NodeKind) :
    let impl := NI4T.implN4T (fun _ => implC fin lRows κs₀) ν
    (∀ a b, impl.eqZ a b = eqZS a b) ∧
      (∀ v l pe, v.size = 127 → impl.lagrangeS v l pe = lagrangeSS v l pe) ∧
      (∀ r, impl.targetS (KindP.ofNode ν).tix r = NT4.targetSNode4S ν r) ∧
      (∀ k a b c, c.size = 22 → impl.shiftTarget k a b c = shiftTargetS k a b c) ∧
      (∀ a b, impl.shiftMask a b = NT4.shiftMask4S ν a b) ∧ (∀ κ s a b, impl.slotW κ s a b = slotWS s a b) ∧
      (∀ tt rr, impl.linkWAll (KindP.ofNode ν).tix tt rr = NT4.linkWAll4S ν tt rr) ∧
      (∀ rw cw, rw.size = 2 ^ 14 → cw.size = 2 ^ 14 →
        impl.walkAB rw cw = (Eval.walkSpecA rw cw, Eval.walkSpecB rw cw)) ∧
      ∀ l a, impl.rowW l a = rowWS l a := by
  intro impl
  have hm : impl.Meets (NI4.specN4 (fun _ => specC fin lRows κs₀) ν) :=
    NI4T.implN4T_meets ν (implC_meets fin lRows κs₀)
  obtain ⟨hST, hSM, hSW, hLW⟩ := nodeOps_of_meets hm rfl
  obtain ⟨h1, h2, h3, -, -, -, h7, -, -, -, -, -, -, -, -, h16, -⟩ := hm
  refine ⟨fun a b => ?_, fun v l pe hv => ?_, fun r => ?_, hST, hSM, hSW, hLW, fun rw cw h1' h2' => ?_,
    fun l a => ?_⟩
  · rw [h3]; simp only [NI4.specN4, Impl.withRS4S, Impl.specC, Impl.specCWith]
  · rw [h1 v l pe hv]; simp only [NI4.specN4, Impl.withRS4S, Impl.specC, Impl.specCWith]
  · rw [h2]; simp only [NI4.specN4, Impl.withRS4S, Impl.specC, Impl.specCWith]; rfl
  · rw [h7 rw cw h1' h2']; simp only [NI4.specN4, Impl.withRS4S, Impl.specC, Impl.specCWith]
  · rw [h16]; simp only [NI4.specN4, Impl.withRS4S, Impl.specC, Impl.specCWith]

end FR.Snd.R4

end G6_FRSoundness4R4FrCtrlB

section G6_FRSoundness4R4RndK

-- New for `flock-recursive` (BLUEPRINT revision 4.1, A.9 P1.i and Pf, the K sumcheck rounds; track
-- R4f). The 3.x templates are `FRSoundnessAccVal.rounds_view` and `FRSoundnessAccPf`.

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

end G6_FRSoundness4R4RndK

section G6_FRSoundness4R4Tail

-- New for `flock-recursive` (BLUEPRINT revision 4.1, §5.4, A.9 finals; track R4f). The 3.x template is
-- `FRSoundnessAccFin` (`FinLog`, `acceptTail_of_finLog`) and the round half of
-- `FRSoundnessAccLog.finLog_of_run`.

/-!
# T4's `AcceptTail` from an accepted `gen4` run (`FinLog4`)

`FinLog4 W₀ c₀ L es y` is what the accepted verifier's checks say about the chain `es` (3.x's
`FinLog`, at T4's revision 4.1 reads: `kindOfC`, `CKind.lv`, `T4.p1Start`, `T4.pfStart`, `T4.sAt`,
`T4.qPos`, `T4.capDig`, `T4.kcAt`, `T4.encAt`, `T4.finalAt`), the verifier's column folds being
`y i q`:

* `rnd`, `rndPf`: P1.i's and Pf's in-phase round checks, rounds `l ≥ 1` (**proved from the run**:
  `rounds_of_run4`, through `p1_view4`/`pf_view4`);
* `start`: P1.0's first claim is `c₀`;
* `cols`: P2.i's opened columns (revision 4.4.1, (β′): a path to the committed digest `D_r =
  T4.dAt es i q`, `y_q` their fold at `sᵢ`);
* `cap`: the batched cap check's three asserts (`T4.capChk4`);
* `link`: `finP i`, `i < 4`; `pf0`: `finP 4`'s assert; `enc`: `finP 4`'s direct checks;
* `fin`: `finPf`'s `relPf` at the spec.

**`acceptTail4_of_finLog`** (3.x's `acceptTail_of_finLog`): on a log without bad events, a chain of
486 entries with `FinLog4` and `¬ RejF` is a `T4.AcceptTail` (the checks that read the committed words
given `T4.truthCap`). **`acceptTail4_of_run`**: an accepted
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
  /-- P2.i's opened columns: a path to the committed digest `D_r`, and `y_q` their fold at `sᵢ`. -/
  cols : ∀ i < 5, ∀ q < (CKind.lv (kindOfC es) i).t, ∃ col : ByteArray, ∃ ss : List Digest,
    ss.length = (CKind.lv (kindOfC es) i).sib ∧
    (openPath (frEnc i) col (T4.qPos (kindOfC es) es i q) ss).runLog L = some (T4.dAt es i q) ∧
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
  /-- The batched cap check's three asserts (revision 4.4.1). -/
  cap : T4.capChk4 es

variable {W₀ : Log → Log → ℕ → K} {c₀ : Log → Log → K}

/-! ## From `FinLog4` to the tail's checks -/

/-- **The verifier's fold of a query is `foldAtN`** (with `D` true the column is the committed one). -/
theorem y_eq_foldAtN4 {L es : Log} {y : ℕ → ℕ → K} (hc : ¬ Collision L) (ht : T4.truthCap es)
    (h : FinLog4 W₀ c₀ L es y) {i : ℕ} (hi : i < 5) {q : ℕ} (hq : q < (CKind.lv (kindOfC es) i).t) :
    y i q = T4.foldAtN (kindOfC es) L es i (T4.qPos (kindOfC es) es i q) := by
  obtain ⟨col, ss, hss, hpath, hy⟩ := h.cols i hi q hq
  rw [hy, T4.foldAt_of_dcols hc ht hi hq hss hpath]

/-- **P1.i's round checks** from `FinLog4` (round 0: `start` for `i = 0`, `link` and the folds for
`i ≥ 1`). -/
theorem p1_of_finLog4 {L es : Log} {y : ℕ → ℕ → K} (hc : ¬ Collision L) (ht : T4.truthCap es)
    (h : FinLog4 W₀ c₀ L es y) :
    ∀ i < 5, ∀ l < hEll i, Chk2 (T4.p1Start i) 32 readK chK (T4.lvC c₀ i) L es l := by
  intro i hi l hl
  rcases l with _ | l
  · rw [chk2_zero]
    rcases i with _ | i
    · exact h.start
    · rw [T4.lvC_succ c₀ (by omega), h.link i (by omega), T4.vNext]
      refine congrArg (T4.c1 c₀ i L es + ·) (sum_congr rfl fun q hq => ?_)
      rw [y_eq_foldAtN4 hc ht h (by omega) (mem_range.mp hq)]
  · exact (chk2_succ _ _ _ _ _).2 (h.rnd i hi l hl)

/-- **Pf's round checks** from `FinLog4` (round 0: `pf0`, `pf_round0_agree`). -/
theorem pf_of_finLog4 {L es : Log} {y : ℕ → ℕ → K} (h : FinLog4 W₀ c₀ L es y) :
    ∀ l < 7, Chk2 T4.pfStart 32 readK chK (T4.lvC c₀ 5) L es l := by
  intro l hl
  rcases l with _ | l
  · exact (T4.pf_round0_agree (c₀ := c₀) L es).2 h.pf0
  · exact (chk2_succ _ _ _ _ _).2 (h.rndPf l hl)

/-- **Level 4's consistency** from `FinLog4` (`truthP3_four_of_dcols`, with `D` true). -/
theorem lvl4_of_finLog4 {L es : Log} {y : ℕ → ℕ → K} (hc : ¬ Collision L) (ht : T4.truthCap es)
    (h : FinLog4 W₀ c₀ L es y) : T4.truthP3 (kindOfC es) L es 4 := by
  refine T4.truthP3_four_of_dcols hc ht fun q hq => ?_
  obtain ⟨col, ss, hss, hpath, hy⟩ := h.cols 4 (by norm_num) q hq
  exact ⟨col, ss, hss, hpath, hy ▸ h.enc q hq⟩

/-- **`AcceptTail` from the finals on the log** (3.x's `acceptTail_of_finLog`). -/
theorem acceptTail4_of_finLog {RejF : Log → Log → Prop} {L : Log} {j : ℕ} {y : ℕ → ℕ → K}
    (hb : ¬ Bad L) (hci : G.IsChain L j) (hlen : (entriesOf L (pathOf L j)).length = 486)
    (hR : ¬ RejF L (entriesOf L (pathOf L j))) (h : FinLog4 W₀ c₀ L (entriesOf L (pathOf L j)) y) :
    T4.AcceptTail RejF W₀ c₀ L j := by
  have hc : ¬ Collision L := fun hc => hb (.inl hc)
  exact ⟨hci, by rw [hlen, T4.capPh_pos.2.2.2], hR, fun ht => p1_of_finLog4 hc ht h, pf_of_finLog4 h,
    fun ht => lvl4_of_finLog4 hc ht h, h.fin, h.cap⟩

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
    (openPath (frEnc i) col (T4.qPos (kindOfC es) es i q) ss).runLog L = some (T4.dAt es i q) ∧
    y i q = ∑ r : Fin (CKind.lv (kindOfC es) i).rows,
      eqBits (T4.sAt es i) (CKind.lv (kindOfC es) i).ell r * algebraMap F K (readF col (16 * r))
  link : ∀ i < 4, rSum (T4.p1Start (i + 1)) es 0 = T4.c1 c₀ i L es +
    ∑ q ∈ range (CKind.lv (kindOfC es) i).t, K.smulF (eqBits (T4.kcAt es i) 9 q) (y i q)
  pf0 : rSum T4.pfStart es 0 = T4.c1 c₀ 4 L es
  enc : ∀ q < (CKind.lv (kindOfC es) 4).t,
    y 4 q = T4.encAt (kindOfC es) 4 (T4.finalAt es) (T4.qPos (kindOfC es) es 4 q)
  fin : clR2 T4.pfStart 32 readK chK (T4.lvC c₀ 5) L es 7 = T4.wHatL W₀ L es 4 *
    (∏ v ∈ Ico (T4.mLog (kindOfC es) 4) 7, (1 - T4.pfP es v)) * mleN 7 (T4.finalAt es) (T4.pfPt es)
  cap : T4.capChk4 es

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
  exact ⟨hrnd, hrndPf, hF.start, hF.cols, hF.link, hF.pf0, hF.enc, hF.fin, hF.cap⟩

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

/-- **Control (converse on the round fields)**: a `T4.AcceptTail` with `D` true gives back
`FinLog4`'s round fields, `start`, `pf0` and `fin`; they ask no more than the tail reads. -/
theorem finLog4_rounds_of_acceptTail {RejF : Log → Log → Prop} {L : Log} {j : ℕ}
    (h : T4.AcceptTail RejF W₀ c₀ L j) (ht : T4.truthCap (entriesOf L (pathOf L j))) :
    let es := entriesOf L (pathOf L j)
    (∀ i < 5, ∀ l, l + 1 < hEll i → rSum (T4.p1Start i) es (l + 1) = rVal (T4.p1Start i) es l) ∧
    (∀ l, l + 1 < 7 → rSum T4.pfStart es (l + 1) = rVal T4.pfStart es l) ∧
    rSum (T4.p1Start 0) es 0 = c₀ L es ∧ rSum T4.pfStart es 0 = T4.c1 c₀ 4 L es ∧
    clR2 T4.pfStart 32 readK chK (T4.lvC c₀ 5) L es 7 = T4.wHatL W₀ L es 4 *
      (∏ v ∈ Ico (T4.mLog (kindOfC es) 4) 7, (1 - T4.pfP es v)) * mleN 7 (T4.finalAt es) (T4.pfPt es) :=
  ⟨fun i hi l hl => h.p1 ht i hi (l + 1) hl, fun l hl => h.pf (l + 1) hl, h.p1 ht 0 (by norm_num) 0
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

end G6_FRSoundness4R4Tail

section G6_FRSoundness4R4Start

-- New for `flock-recursive` (BLUEPRINT revision 4.1, A.9 `finRS`/`finB′`, §5.4; track R4g). The 3.x
-- template is `FRSoundnessFrRun`'s `start_run` (`rsV_eq`, `vkL_fsQ`, `stL_fsQ`).

/-!
# `FinRest4.start`: P1.0's first claim is the front's `c₀L4` on an accepted `gen4` run

`finB′`'s relation `relB4` says `ι v* = ` P1.0's first claim, with `v*` (`vStar4`) read on the
registers: `finRS`'s `v_RS` export (the `zhat` register `nRS`), B′'s `κ′` and the public values
(`vk`, the statement's `c₁`, `c₂`, read from π). On an accepted run every one of them is the log's:

* **`rsV4_zh`**: the `zhat nRS` register holds `rsV4` (`exec_gFinRS`'s third conjunct);
* **`rsV4_eq`**: `rsV4 = vRSL4` (RS1's `r″`, `κ` by `rs1_val4`; RS0's slices by `msg_abs4` at 326;
  `phiRS` at its specification `phiRSS`, a new op parameter `hphi`, which `Meets` gives:
  `phiRS_segC`, `phiRS_nodeC`);
* `kp = kpL4` (B′ at 331, `one_name_view4`); **`pubH4_eq`**: `pubH4 = pubHL` (`vkL_eq4` by
  `seedQ4`, `stL_eq4` by `stmt_msg4`).

**`start4_of_fields`** puts them together with P1.0's first claim (`p1_view4`);
**`start4_seg`**, **`start4_node`**: on an accepted run of the kind's program.
-/

namespace FR.Snd.R4
open RecursionFast Rev4 FR.Impl

variable {impl : OpImpl} {p : KindP} {inp : Input}

/-! ## The public values on the log -/

section Pub
variable {tr : Trace} {y : List Val × List Bool × Trace} (h : SkRun4 impl p inp tr y)
include h

/-- **The seed's `vk` on the log is the input's.** -/
theorem vkL_eq4 : vkL (fsOf tr (itemsOf seq4)) = inp.vk := by
  unfold vkL
  rw [seedQ4 h]
  refine Vector.ext fun k hk => ?_
  rw [getElem_bytesAt _ _ _ _ hk, X.seedQ_data', List.getD_append_right _ _ _ _ (by simp [tagSeed]),
    show 7 + k - tagSeed.length = k by simp [tagSeed],
    List.getD_append _ _ _ _ (by simpa using hk), List.getD_eq_getElem _ _ (by simpa using hk),
    Vector.getElem_toList]

/-- **The statement's digests on the log are π's** (bytes `1`, `33` of the `stmt` field). -/
theorem stL_eq4 :
    stL (fsOf tr (itemsOf seq4)) 0 = bytesAt inp.π (fieldOffOf seq4 fStmt + 1) 32 ∧
      stL (fsOf tr (itemsOf seq4)) 1 = bytesAt inp.π (fieldOffOf seq4 fStmt + 33) 32 := by
  rw [fieldOff_hdr_stmt4.2]
  exact ⟨by rw [stL, stmt_msg4 h]; exact bytesAt_extract_of_le inp.π (by norm_num),
    by rw [stL, stmt_msg4 h]; exact bytesAt_extract_of_le inp.π (by norm_num)⟩

/-- **`pubH` at `P` is the log's `pubHL`** (`P.S = seq4`). -/
theorem pubH4_eq {P : FinP} (hPS : P.S = seq4) (kp : F) :
    pubH4 inp P kp = pubHL (fsOf tr (itemsOf seq4)) kp := by
  obtain ⟨h0, h1⟩ := stL_eq4 h
  simp only [pubH4, pubHL, hPS, h0, h1, vkL_eq4 h]

end Pub

/-! ## `v_RS` -/

section RS
variable {tr : Trace} {y : List Val × List Bool × Trace}

/-- **RS1's coordinates by name** are `rsCoL4` (`coordAt es 326`). -/
theorem rs1_val4 (h : SkRun4 impl p inp tr y) {fi : FinIn} (hfi : fi.outs = (skeleton4 seq4 p).2.outs)
    {R : Array Val} (hR : ExtA (#[] ++ y.1.toArray) R) {q : ℕ} (hq : q < 8) :
    fv R ((coordsR fi "RS1").getD q 0) = P4b.rsCoL4 (fsOf tr (itemsOf seq4)) q := by
  obtain ⟨hn24, e24⟩ := ph4 (n := 24) (x := ("RS1", Sh.squeezes 4 .coords)) (by rw [seq4_eq]; rfl)
  have hco := coordsR_view4 h hfi hR hn24 (by rw [e24]) (by norm_num)
    phaseIx_vals.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 (a := 8) (by norm_num)
  rw [show phStart4 24 = 327 by rw [phStart4, fsStarts4_eq]; rfl] at hco
  obtain ⟨hlen, hget⟩ := take_map_getElem hco
  rw [List.getD_eq_getElem _ _ (by omega), hget q (by omega) hq, P4b.rsCoL4, coordAt]

/-- **`finRS`'s `v_RS` export** holds `rsV4` on the skeleton's file. -/
theorem rsV4_zh {P : FinP} {zh : List Reg} {Rs : ℕ → Array Val} {Ex : ℕ → Array (List Reg)}
    (hF : Fields4 impl p inp tr P y zh Rs Ex) :
    fv (Rs 0) (zh.getD nRS 0) =
      rsV4 impl p.tix inp ⟨(skeleton4 seq4 p).2.outs, [], #[]⟩ (#[] ++ y.1.toArray) P := by
  obtain ⟨L₀, hL₀, h0⟩ := hF.rs
  obtain ⟨L, hL, -, hv⟩ := exec_gFinRS impl p.tix inp ⟨(skeleton4 seq4 p).2.outs, [], #[]⟩
    (#[] ++ y.1.toArray) P (hin_RS (fun name x hx => outsOf_lt4 hF.sk [] #[] name x hx)
      (skel_pos4 hF.sk) _ P)
  obtain ⟨rfl, -⟩ := Prod.mk.inj (Option.some.inj (hL₀.symm.trans hL))
  rw [h0, hF.zh_eq]
  exact hv

/-- **`v_RS` on the skeleton's registers is `vRSL4`** (`phiRS` at its specification; the finals'
node flag is the chain's kind's). -/
theorem rsV4_eq (hphi : ∀ r a, r.size = 7 → impl.phiRS r a = phiRSS r a)
    (h : SkRun4 impl p inp tr y) {P : FinP} (hPS : P.S = seq4)
    (hnode : P.kv.node p.tix = (kindOfC (fsOf tr (itemsOf seq4))).isNode) :
    rsV4 impl p.tix inp ⟨(skeleton4 seq4 p).2.outs, [], #[]⟩ (#[] ++ y.1.toArray) P =
      P4b.vRSL4 (kindOfC (fsOf tr (itemsOf seq4))) (fsOf tr (itemsOf seq4)) := by
  set es := fsOf tr (itemsOf seq4)
  set fi : FinIn := ⟨(skeleton4 seq4 p).2.outs, [], #[]⟩
  have hR := extA_refl (#[] ++ y.1.toArray)
  have hpt : ptF (#[] ++ y.1.toArray) (rsFsRegs fi) = (P4b.rsRL4 es).toArray := by
    simp only [ptF, rsFsRegs, P4b.rsRL4, List.map_map]
    exact congrArg List.toArray (List.map_congr_left fun q hq =>
      rs1_val4 h (fi := fi) rfl hR (by simp at hq; omega))
  have hT : ∀ j < 4, rsTv4 impl inp fi (#[] ++ y.1.toArray) P j = P4b.rsTvL4 es j := by
    intro j hj
    simp only [rsTv4, P4b.rsTvL4]
    refine Finset.sum_congr rfl fun i hi => ?_
    have hi' := Finset.mem_range.1 hi
    rw [hpt, hphi _ _ (by simp [P4b.rsRL4]), phiRSS, List.toList_toArray, P4b.sliceL4,
      msg_abs4 h (by norm_num) (by norm_num) fsMsgs4_ends.2.2.2 (by simp only [rsOff]; omega), sv4, hPS]
  unfold rsV4 P4b.vRSL4 P4b.rsKL4
  rw [hT 0 (by norm_num), hT 1 (by norm_num), hT 2 (by norm_num), hT 3 (by norm_num),
    rs1_val4 h (fi := fi) rfl hR (show 7 < 8 by norm_num), hnode]

end RS

/-! ## `finB′` on the fields -/

theorem rest_gFinB' (P : FinP) :
    (finalsOf P).rest[5]'(by rw [rest_finalsOf_length]; decide) = gFinB' P := by
  simp only [Finals.rest, finalsOf, List.cons_append, List.getElem_cons_succ, List.getElem_cons_zero]

/-- **`FinRest4.start` on the fields**: P1.0's first claim is `c₀L4 = ι v*` (`relB4` with every
input of `v*` the log's). -/
theorem start4_of_fields (hphi : ∀ r a, r.size = 7 → impl.phiRS r a = phiRSS r a)
    {tr : Trace} {P : FinP} {y : List Val × List Bool × Trace} {zh : List Reg}
    {Rs : ℕ → Array Val} {Ex : ℕ → Array (List Reg)} (hF : Fields4 impl p inp tr P y zh Rs Ex)
    (hPS : P.S = seq4) (hnode : P.kv.node p.tix = (kindOfC (fsOf tr (itemsOf seq4))).isNode)
    (hrsv : P4b.nRsv (kindOfC (fsOf tr (itemsOf seq4))) = if (P.rsvOps && P.rsv) = true then rsvN else 0)
    (L : Log) :
    rSum (T4.p1Start 0) (fsOf tr (itemsOf seq4)) 0 = P4b.c₀L4 L (fsOf tr (itemsOf seq4)) := by
  set es := fsOf tr (itemsOf seq4)
  set fi : FinIn := ⟨(skeleton4 seq4 p).2.outs, zh, Ex 5⟩
  have hfi : fi.outs = (skeleton4 seq4 p).2.outs := rfl
  have hE := hF.ext 5 (by decide)
  have hpos := hF.pos (k := 5) (by decide)
  obtain ⟨-, L5, hL5, -, -⟩ := hF.fld 5 (by decide)
  rw [rest_gFinB'] at hL5
  obtain ⟨hn25, e25⟩ := ph4 (n := 25) (x := ("B'", Sh.squeezes 1 .one)) (by rw [seq4_eq]; rfl)
  obtain ⟨hk1, hk2⟩ := one_name_view4 hF.sk hfi hE hn25 (by rw [e25])
    phaseIx_vals.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2
  have hc0 : claim0 fi "P1" < (Rs 5).size := headD_lt (hF.sk_lt (by decide) _ "P1") hpos
  have hin1 : (outsOf fi "B'").headD 0 < (Rs 5).size := lt_of_lt_of_le hk1 hE.1
  have hin2 : fi.zhat.getD nRS 0 < (Rs 5).size := getD_lt hpos (hF.zlt' (by decide)) _
  have hex : ∀ x ∈ (fi.ex.getD exE []).drop 1, x < (Rs 5).size := by
    obtain ⟨hs4, L4, hL4, he4, hx4⟩ := hF.fld 4 (by decide)
    rw [rest_gFinE] at hL4 hx4
    have hl4 := pureRun_len impl p.tix inp _ _ [] _ _ hL4
    rw [List.length_nil, Nat.zero_add] at hl4
    have hfx : fi.ex.getD exE [] = (gFinE P ⟨(skeleton4 seq4 p).2.outs, zh, Ex 4⟩ (Rs 4).size).2 := by
      rw [show fi.ex = Ex 5 from rfl, hx4, exE, Array.getD_eq_getD_getElem?, Array.getElem?_push, hs4,
        if_pos rfl, Option.getD_some]
    rw [hfx]
    exact gFinE_ex_lt P _ he4 hl4
  obtain ⟨L', hL', -⟩ := flag_gFinB' (impl := impl) (κ := p.tix) (inp := inp) (fi := fi) (r := Rs 5)
    (P := P) (List.forall_mem_cons.2 ⟨hin1, List.forall_mem_cons.2 ⟨hin2,
      List.forall_mem_cons.2 ⟨hc0, fun _ h => absurd h List.not_mem_nil⟩⟩⟩) hex
  have h1 := val_eqv_k (pureRun_det hL5 hL')
  obtain ⟨b, hout, -, h0, -, hlt, -⟩ := p1_view4 hF.sk hfi (i := 0) (by norm_num)
  have hlt0 : p1Claim0 fi 0 < (#[] ++ y.1.toArray).size := by
    rw [p1Claim0, hout, List.cons_append, List.headD_cons]
    exact hlt _ (by rw [hout, List.cons_append]; exact List.mem_cons_self ..)
  have he : p1Claim0 fi 0 = claim0 fi "P1" := by
    simp only [p1Claim0, claim0, lvOuts, outsOf, Nat.mul_zero, Nat.add_zero]
  rw [← he, hE.rd hlt0, h0] at h1
  rw [P4b.c₀L4, Val.k.inj h1, K.smulF_one]
  refine congrArg (algebraMap F K) ?_
  have hz : fv (Rs 5) (fi.zhat.getD nRS 0) = P4b.vRSL4 (kindOfC es) es := by
    rw [show fi.zhat = zh from rfl, hF.fv_zh (by decide), rsV4_zh hF, rsV4_eq hphi hF.sk hPS hnode]
  have hv0 : vStar4o p.tix inp fi (Rs 5) P = P4b.vRSL4 (kindOfC es) es +
      if (kindOfC es).isNode then P4b.kpL4 es * P4b.kpL4 es * pubHL es (P4b.kpL4 es) else 0 := by
    simp only [vStar4o, hz, hk2, hnode, pubH4_eq hF.sk hPS, P4b.kpL4,
      show phStart4 25 = 331 by rw [phStart4, fsStarts4_eq]; rfl]
    rfl
  have hkp : fv (Rs 5) ((outsOf fi "B'").headD 0) = P4b.kpL4 es := by
    rw [hk2, P4b.kpL4, show phStart4 25 = 331 by rw [phStart4, fsStarts4_eq]; rfl]
  simp only [vStar4, P4b.vStarL4]
  by_cases hc : (P.rsvOps && P.rsv) = true
  · have h60 : P4b.nRsv (kindOfC es) = 60 := by rw [hrsv, if_pos hc]; rfl
    have hnd : (kindOfC es).isNode = true := by
      cases hk : kindOfC es with
      | node ν => rfl
      | seg σ => rw [hk] at h60; simp [P4b.nRsv] at h60
    have hro : P.rsvOps = true := by simp only [Bool.and_eq_true] at hc; exact hc.1
    rw [if_pos hc, hv0, if_pos hnd, if_pos hnd, P4b.rsvHL, h60, hkp]
    have hs : ∀ i ∈ Finset.range rsvN, P4b.kpL4 es ^ i * fv (Rs 5) (((fi.ex.getD exE []).drop 1).getD i 0) =
        P4b.kpL4 es ^ i * P4b.rsvV es i := fun i hi => by
      rw [Finset.mem_range] at hi
      rw [show fi.ex = Ex 5 from rfl, rsvEx_of_fields hF i hi hro, P4b.rsvV,
        child_vals4 hF.sk (show i < 60 from hi), hPS]
    rw [Finset.sum_congr rfl hs]
    simp only [rsvN]; ring
  · have h0 : P4b.nRsv (kindOfC es) = 0 := by rw [hrsv, if_neg hc]
    rw [if_neg hc, hv0, P4b.rsvHL, h0]
    split_ifs <;> simp

/-! ## On an accepted run of the kind's program -/

/-- **`FinRest4.start` for a segment** (`phiRS` at its specification). -/
theorem start4_seg (hphi : ∀ r a, r.size = 7 → impl.phiRS r a = phiRSS r a) {σ : SegKind} {tr : Trace}
    (h : semIR impl (gen4 seq4 (.ofSeg σ) (finOps4 (segFinP σ))) inp tr = some true) (L : Log) :
    rSum (T4.p1Start 0) (fsOf tr (itemsOf seq4)) 0 = P4b.c₀L4 L (fsOf tr (itemsOf seq4)) := by
  obtain ⟨y, zh, Rs, Ex, hF⟩ := fields4_of_accept (segFinP σ) h
  exact start4_of_fields hphi hF rfl (by rw [kindOfC_acc_seg h]; rfl) (by rw [kindOfC_acc_seg h]; rfl) L

/-- **`FinRest4.start` for a node.** -/
theorem start4_node (hphi : ∀ r a, r.size = 7 → impl.phiRS r a = phiRSS r a) {ν : NodeKind}
    {cells : List ℕ} {tr : Trace}
    (h : semIR impl (gen4 seq4 (.ofNode ν) (finOps4 (nodeFinP ν cells))) inp tr = some true) (L : Log) :
    rSum (T4.p1Start 0) (fsOf tr (itemsOf seq4)) 0 = P4b.c₀L4 L (fsOf tr (itemsOf seq4)) := by
  obtain ⟨y, zh, Rs, Ex, hF⟩ := fields4_of_accept (nodeFinP ν cells) h
  exact start4_of_fields hphi hF rfl (by rw [kindOfC_acc_node h]; rfl)
    (by rw [kindOfC_acc_node h]; cases ν <;> rfl) L

/-! ## The op parameter `hphi` (controls) -/

/-- (+) **The concrete segment ops meet `hphi`** (`implSegC_meets`). -/
theorem phiRS_segC (fin : Finals) (lRows : List Circ.Row) (κs₀ : F) :
    ∀ r a, r.size = 7 → (implSeg (implC fin lRows κs₀)).phiRS r a = phiRSS r a := fun r a hr => by
  rw [(implSegC_meets fin lRows κs₀).2.2.2.2.2.1 r a hr]
  simp only [specSeg, Impl.specC, Impl.specCWith]

/-- (+) **… and the node's** (`implN4T` over 3.x's ops). -/
theorem phiRS_nodeC (fin : Finals) (lRows : List Circ.Row) (κs₀ : F) (ν : NodeKind) :
    ∀ r a, r.size = 7 → (NI4T.implN4T (fun _ => implC fin lRows κs₀) ν).phiRS r a = phiRSS r a :=
  fun r a hr => by
    have hm : (NI4T.implN4T (fun _ => implC fin lRows κs₀) ν).Meets
        (NI4.specN4 (fun _ => specC fin lRows κs₀) ν) := NI4T.implN4T_meets ν (implC_meets fin lRows κs₀)
    rw [hm.2.2.2.2.2.1 r a hr]
    simp only [NI4.specN4, Impl.withRS4S, Impl.specC, Impl.specCWith]

end FR.Snd.R4

end G6_FRSoundness4R4Start

section G6_FRSoundness4R4PosT

-- New for `flock-recursive` (BLUEPRINT revision 4.1, A.4, A.9, §5.1; track R4g). The 3.x templates are
-- `FRVIRSpec`'s `stepT`/`stepsT`/`posT`/`posAllT` with `exec_merkleOps`/`exec_posOps`/`exec_posAll`,
-- and `FRSoundnessAccQry`'s `stepsT_path`/`posT_path`/`posAllT_path`.

/-!
# `posOps4` on a trace, and its Merkle paths on the log

`genPhase4`'s `.queries i` runs `posOps4` per position (the kind's level `K = S.lvK m i` for the
index, its depth `Lk.sib` and its cap; `sL = (S.lv i).sib` Merkle slots; absolute π offsets). This
module is 3.x's reference of a position at those parameters:

* **`stepT4`/`stepsT4`/`posT4`/`posAllT4`**: the registers, flag and remaining trace of the Merkle
  steps, one position, `t` positions;
* **`exec_merkleOps4`**, **`exec_posOps4`**, **`exec_posAll4`**: `exec` of the ops is the
  reference (the 3.x proofs at the 4.1 ops);
* **`posAllT4_path`**: on a log that contains the trace and repeats no query, every position's
  column has a path to its **committed digest** `D_r`, π's 32 bytes at `dO + 32·p` (revision 4.4.1,
  (β′): V asserts the root equal to the static read of field `fD`; `stepsT4_path`, `posT4_path`), and
  the position's cap index `j >>> Lk.sib` and `D_r` are its registers `4 + 6·sL`, `4 + 6·sL + 1`.
-/

namespace FR.Snd.R4
open RecursionFast Rev4 FR.Merkle

/-! ## The reference -/

section Ref
variable (inp : Input)

/-- **One Merkle step** at depth `h` of position `j` (`sib`: the kind's depth). -/
def stepT4 (sib i h j so : ℕ) (cur : Digest) : Trace → Option (List Val × Bool × Digest × Trace)
  | (q, a) :: tr =>
    let act := decide (h < sib)
    let s := bytesAt inp.π (absOff 0 so) 32
    let b := j.testBit h
    let l := if b then s else cur
    let r := if b then cur else s
    if q = (if act then nodeQ i l r else nodeQ i zeroD zeroD) then
      some ([.d s, .bit b, .d l, .d r, .d a, .d (if act then a else cur)],
        act || decide (s = zeroD), if act then a else cur, tr)
    else none
  | [] => none

/-- `n` Merkle steps from depth `h`. -/
def stepsT4 (sib i j : ℕ) : ℕ → ℕ → ℕ → Digest → Trace → Option (List Val × Bool × Digest × Trace)
  | 0, _, _, cur, tr => some ([], true, cur, tr)
  | n + 1, h, so, cur, tr =>
    (stepT4 inp sib i h j so cur tr).bind fun x =>
      (stepsT4 sib i j n (h + 1) (so + 32) x.2.2.1 x.2.2.2).map fun y =>
        (x.1 ++ y.1, x.2.1 && y.2.1, y.2.2)

/-- **Position `p` of level `i`** (`Lk`: the kind's level; `sL` Merkle slots; `ad`, `w`: the answer
and weight values; `dO`: the level's first committed digest, absolute). Revision 4.4.1 (β′): after
the cap index, the static read of `D_r` (π at `dO + 32·p`) and the check `cur = D_r`. -/
def posT4 (Lk : Level) (sL i co so dO : ℕ) (ad : ℕ → Digest) (w : Array K) (p : ℕ) :
    Trace → Option (List Val × Bool × Trace)
  | (q, a) :: tr =>
    let j := idxOf Lk.logN (ad (p / Lk.per)) (p % Lk.per)
    let col := inp.π.extract (absOff 0 (co + p * colBytes i)) (absOff 0 (co + p * colBytes i) + colBytes i)
    if q = colQ i col then
      (stepsT4 inp Lk.sib i j sL 0 (so + p * sL * 32) a tr).map fun x =>
        let capIx := j >>> Lk.sib
        let dr := bytesAt inp.π (absOff 0 (dO + 32 * p)) 32
        ([.n j, .b col, .d a, .k (dotKF w col)] ++ x.1 ++ [.n capIx, .d dr],
          x.2.1 && decide (x.2.2.1 = dr), x.2.2.2)
    else none
  | [] => none

/-- All positions from `p`. -/
def posAllT4 (Lk : Level) (sL i co so dO : ℕ) (ad : ℕ → Digest) (w : Array K) :
    ℕ → ℕ → Trace → Option (List Val × Bool × Trace)
  | 0, _, tr => some ([], true, tr)
  | t + 1, p, tr =>
    (posT4 inp Lk sL i co so dO ad w p tr).bind fun x =>
      (posAllT4 Lk sL i co so dO ad w t (p + 1) x.2.2).map fun y => (x.1 ++ y.1, x.2.1 && y.2.1, y.2.2)

theorem stepT4_spec {sib i h j so : ℕ} {cur : Digest} {tr : Trace} {y : List Val × Bool × Digest × Trace}
    (hy : stepT4 inp sib i h j so cur tr = some y) : y.1.length = 6 ∧ y.1.getD 5 default = .d y.2.2.1 := by
  rcases tr with _ | ⟨⟨q, a⟩, tr⟩
  · cases hy
  · simp only [stepT4] at hy
    split_ifs at hy <;> cases hy <;> simp

theorem stepsT4_spec {sib i j n h so : ℕ} {cur : Digest} {tr : Trace}
    {x : List Val × Bool × Digest × Trace} (hx : stepsT4 inp sib i j n h so cur tr = some x) :
    x.1.length = 6 * n ∧ (n = 0 → x.2.2.1 = cur) ∧ (0 < n → x.1.getD (6 * n - 1) default = .d x.2.2.1) := by
  induction n generalizing h so cur tr x with
  | zero => simp [stepsT4] at hx; subst hx; simp
  | succ n ih =>
    simp only [stepsT4, Option.bind_eq_some_iff, Option.map_eq_some_iff] at hx
    obtain ⟨y, hy, z, hz, rfl⟩ := hx
    obtain ⟨hl, h5⟩ := stepT4_spec inp hy
    obtain ⟨h1, h2, h3⟩ := ih hz
    refine ⟨by simp [hl, h1]; ring, by omega, fun _ => ?_⟩
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · have hz0 : z.1 = [] := List.length_eq_zero_iff.1 (by simpa using h1)
      rw [hz0, h2 rfl]; simpa using h5
    · rw [List.getD_append_right _ _ _ _ (by omega), hl,
        show 6 * (n + 1) - 1 - 6 = 6 * n - 1 by omega, h3 hn]

/-- The steps consume `n` entries. -/
theorem stepsT4_len {sib i j n h so : ℕ} {cur : Digest} {tr : Trace}
    {x : List Val × Bool × Digest × Trace} (hx : stepsT4 inp sib i j n h so cur tr = some x) :
    ∃ seg, tr = seg ++ x.2.2.2 ∧ seg.length = n := by
  induction n generalizing h so cur tr x with
  | zero => simp [stepsT4] at hx; subst hx; exact ⟨[], by simp, rfl⟩
  | succ n ih =>
    simp only [stepsT4, Option.bind_eq_some_iff, Option.map_eq_some_iff] at hx
    obtain ⟨y, hy, z, hz, rfl⟩ := hx
    rcases tr with _ | ⟨e, tr⟩
    · cases hy
    have hy2 : y.2.2.2 = tr := by
      simp only [stepT4] at hy; split_ifs at hy <;> cases hy <;> rfl
    obtain ⟨seg, h1, h2⟩ := ih hz
    exact ⟨e :: seg, by simp [← hy2, h1], by simp [h2]⟩

theorem posT4_length {Lk : Level} {sL i co so dO p : ℕ} {ad : ℕ → Digest} {w : Array K} {tr : Trace}
    {x : List Val × Bool × Trace} (hx : posT4 inp Lk sL i co so dO ad w p tr = some x) :
    x.1.length = 4 + 6 * sL + 2 := by
  rcases tr with _ | ⟨⟨q, a⟩, tr⟩
  · cases hx
  simp only [posT4] at hx
  split_ifs at hx
  obtain ⟨y, hy, rfl⟩ := Option.map_eq_some_iff.1 hx
  simp [(stepsT4_spec inp hy).1]; omega

theorem posAllT4_length {Lk : Level} {sL i co so dO t p : ℕ} {ad : ℕ → Digest} {w : Array K}
    {tr : Trace} {x : List Val × Bool × Trace} (hx : posAllT4 inp Lk sL i co so dO ad w t p tr = some x) :
    x.1.length = (4 + 6 * sL + 2) * t := by
  induction t generalizing p tr x with
  | zero => simp [posAllT4] at hx; subst hx; simp
  | succ t ih =>
    simp only [posAllT4, Option.bind_eq_some_iff, Option.map_eq_some_iff] at hx
    obtain ⟨y, hy, z, hz, rfl⟩ := hx
    simp only [List.length_append, posT4_length inp hy, ih hz, Nat.mul_succ]; omega

end Ref

/-! ## `exec` of the ops is the reference -/

section Exec
variable (impl : OpImpl) (κ : Kind) (inp : Input)

theorem exec_merkleOps4 (sib i j jr n h curR so : ℕ) (r : Array Val) (ok : Bool) (ops : List Op)
    (cur : Digest) (hj : jr < r.size) (hjv : (rd r jr).toN = j) (hc : curR < r.size)
    (hcv : rd r curR = .d cur) (tr : Trace) :
    exec impl κ inp (merkleOps4 sib i jr n h curR so r.size ++ ops) ⟨r, ok⟩ tr =
      (stepsT4 inp sib i j n h so cur tr).bind fun x =>
        exec impl κ inp ops ⟨r ++ x.1.toArray, ok && x.2.1⟩ x.2.2.2 := by
  induction n generalizing h curR so r ok cur tr with
  | zero => simp [merkleOps4, stepsT4]
  | succ n ih =>
    rw [show (⟨r, ok⟩ : St) = ⟨r ++ ([] : List Val).toArray, ok⟩ by simp]
    simp only [merkleOps4, stepsT4, List.cons_append, List.nil_append]
    rcases tr with _ | ⟨⟨q, a⟩, tr⟩
    · simp only [exec_app, evalOp, List.nil_append, stepT4, Option.bind_none]
    have hsel : ∀ (c : Bool) (x y : Digest), (if c then Val.d x else Val.d y) = Val.d (if c then x else y) :=
      fun c x y => by cases c <;> rfl
    simp only [exec_app, evalOp, rd_app, rd_app0, rd_app_left _ _ hj, rd_app_left _ _ hc, hjv, hcv,
      List.getD_cons_succ, List.getD_cons_zero, List.nil_append, List.cons_append, Val.toBit, toD_d,
      hsel, stepT4, nodeQF_eq, digestAt_eq]
    generalize bytesAt inp.π (absOff 0 so) 32 = sb
    generalize hQ : (if decide (h < sib) = true then
      nodeQ i (if j.testBit h = true then sb else cur) (if j.testBit h = true then cur else sb)
      else nodeQ i zeroD zeroD) = Q
    by_cases hq : q = Q
    · simp only [hq, ite_true, Option.bind_some, Option.bind_map]
      rw [show r.size + 6 = (r ++ [Val.d sb, Val.bit (j.testBit h),
          Val.d (if j.testBit h = true then sb else cur), Val.d (if j.testBit h = true then cur else sb),
          Val.d a, Val.d (if decide (h < sib) = true then a else cur)].toArray).size by simp,
        ih _ _ _ _ _ _ (by simp; omega) (by rw [rd_app_left _ _ hj, hjv]) (by simp) (by rw [rd_app]; rfl)]
      refine Option.bind_congr fun y _ => ?_
      simp [Array.append_assoc, Bool.and_assoc, Val.isZero]
    · simp [hq]

theorem exec_merkleOps4' (sib i j jr n h curR so b : ℕ) (r : Array Val) (ok : Bool) (ops : List Op)
    (cur : Digest) (hb : b = r.size) (hj : jr < r.size) (hjv : (rd r jr).toN = j) (hc : curR < r.size)
    (hcv : rd r curR = .d cur) (tr : Trace) :
    exec impl κ inp (merkleOps4 sib i jr n h curR so b ++ ops) ⟨r, ok⟩ tr =
      (stepsT4 inp sib i j n h so cur tr).bind fun x =>
        exec impl κ inp ops ⟨r ++ x.1.toArray, ok && x.2.1⟩ x.2.2.2 := by
  subst hb; exact exec_merkleOps4 impl κ inp sib i j jr n h curR so r ok ops cur hj hjv hc hcv tr

/-- A position's first four registers. -/
theorem exec_posHead4 (Lk : Level) (i co : ℕ) (ans : List Reg) (w p : ℕ) (r : Array Val) (ok : Bool)
    (rest : List Op) (ad : ℕ → Digest) (wv : Array K) (hA : ∀ k, ans.getD k 0 < r.size)
    (had : ∀ k, (rd r (ans.getD k 0)).toD = ad k) (hw : w < r.size) (hwv : (rd r w).toAK = wv)
    (q : ByteArray) (a : Digest) (tr : Trace) :
    exec impl κ inp ([.idx (fun _ => ans.getD (p / Lk.per) 0) (fun _ => Lk.logN) (fun _ => p % Lk.per),
      .piField 0 (co + p * colBytes i) (colBytes i), .askCol i (r.size + 1), .dotKF w (r.size + 1)] ++ rest)
      ⟨r, ok⟩ ((q, a) :: tr) =
      let j := idxOf Lk.logN (ad (p / Lk.per)) (p % Lk.per)
      let col := inp.π.extract (absOff 0 (co + p * colBytes i)) (absOff 0 (co + p * colBytes i) + colBytes i)
      if q = colQ i col then
        exec impl κ inp rest ⟨r ++ (posHeadVals j col a wv).toArray, ok⟩ tr
      else none := by
  rw [show (⟨r, ok⟩ : St) = ⟨r ++ ([] : List Val).toArray, ok⟩ by simp]
  simp only [List.cons_append, List.nil_append, exec_app, evalOp, rd_app_left _ _ (hA _), had,
    rd_app_left _ _ hw, hwv, rd_app, List.getD_cons_succ, List.getD_cons_zero, Val.toB,
    Bool.and_true, posHeadVals, dotKFF_eq, idxOfF_eq]

/-- A position's last three ops (revision 4.4.1: the static read of `D_r` at `o`). -/
theorem exec_posTail4 (Lk : Level) (o jr curR e : ℕ) (R : Array Val) (ok : Bool) (ops : List Op) (j : ℕ)
    (cur : Digest) (he : e = R.size) (hjr : jr < R.size) (hj : rd R jr = .n j) (hcr : curR < R.size)
    (hc : rd R curR = .d cur) (tr : Trace) :
    exec impl κ inp ([.shrN jr (fun _ => Lk.sib), .piDigest 0 o, .assertEq curR (e + 1) allK] ++ ops)
      ⟨R, ok⟩ tr =
      exec impl κ inp ops ⟨R ++ [Val.n (j >>> Lk.sib), .d (bytesAt inp.π (absOff 0 o) 32)].toArray,
        ok && decide (cur = bytesAt inp.π (absOff 0 o) 32)⟩ tr := by
  subst he
  rw [show (⟨R, ok⟩ : St) = ⟨R ++ ([] : List Val).toArray, ok⟩ by simp]
  simp only [List.cons_append, List.nil_append, exec_app, evalOp, rd_app_left _ _ hjr, hj,
    rd_app_left _ _ hcr, hc, rd_app, rd_app0, List.getD_cons_succ, List.getD_cons_zero, Val.toN,
    Val.eqv, allK, Bool.not_true, Bool.false_or, Bool.and_true, digestAt_eq]

/-- A position's Merkle steps after its first four registers. -/
theorem exec_posMid4 (sib i j n so : ℕ) (r : Array Val) (col : ByteArray) (a : Digest) (wv : Array K)
    (ok : Bool) (ops : List Op) (tr : Trace) :
    exec impl κ inp (merkleOps4 sib i r.size n 0 (r.size + 2) so (r.size + 4) ++ ops)
      ⟨r ++ (posHeadVals j col a wv).toArray, ok⟩ tr =
      (stepsT4 inp sib i j n 0 so a tr).bind fun x =>
        exec impl κ inp ops ⟨r ++ (posHeadVals j col a wv).toArray ++ x.1.toArray, ok && x.2.1⟩ x.2.2.2 :=
  exec_merkleOps4' impl κ inp sib i j r.size n 0 (r.size + 2) so (r.size + 4) _ ok ops a
    (posHead_size r j col a wv).symm (by rw [posHead_size]; omega) (by rw [posHead_rd0]; rfl)
    (by rw [posHead_size]; omega) (posHead_rd2 r j col a wv) tr

/-- **One position** against `posT4`. -/
theorem exec_posOps4 (S : Seq) (k : KindP) (i co so dO : ℕ) (ans : List Reg) (w p : ℕ) (r : Array Val)
    (ok : Bool) (ops : List Op) (ad : ℕ → Digest) (wv : Array K) (hA : ∀ k, ans.getD k 0 < r.size)
    (had : ∀ k, (rd r (ans.getD k 0)).toD = ad k) (hw : w < r.size) (hwv : (rd r w).toAK = wv)
    (tr : Trace) :
    exec impl κ inp (posOps4 S k i co so dO ans w p r.size ++ ops) ⟨r, ok⟩ tr =
      (posT4 inp (S.lvK k.d.m i) (S.lv i).sib i co so dO ad wv p tr).bind fun x =>
        exec impl κ inp ops ⟨r ++ x.1.toArray, ok && x.2.1⟩ x.2.2 := by
  simp only [posOps4, List.append_assoc]
  rcases tr with _ | ⟨⟨q, a⟩, tr⟩
  · rw [show (⟨r, ok⟩ : St) = ⟨r ++ ([] : List Val).toArray, ok⟩ by simp]
    simp only [List.cons_append, List.nil_append, exec_app, evalOp, posT4, Option.bind_none]
  rw [exec_posHead4 impl κ inp (S.lvK k.d.m i) i co ans w p r ok _ ad wv hA had hw hwv]
  simp only [posT4]
  generalize idxOf (S.lvK k.d.m i).logN (ad (p / (S.lvK k.d.m i).per)) (p % (S.lvK k.d.m i).per) = j
  generalize inp.π.extract (absOff 0 (co + p * colBytes i)) (absOff 0 (co + p * colBytes i) + colBytes i) = col
  by_cases hq : q = colQ i col
  swap; · simp [hq]
  simp only [hq, ite_true]
  have hs4 : (r ++ (posHeadVals j col a wv).toArray).size = r.size + 4 := posHead_size r j col a wv
  rw [exec_posMid4, Option.bind_map]
  · refine Option.bind_congr fun x hx => ?_
    obtain ⟨hl, h0, hlast⟩ := stepsT4_spec inp hx
    generalize hsb : (S.lv i).sib = sb at *
    rw [exec_posTail4 impl κ inp (S.lvK k.d.m i) (dO + 32 * p) (jr := r.size)
      (curR := curOfY sb (r.size + 3)) (e := r.size + 4 + 6 * sb)
      (j := j) (cur := x.2.2.1) (he := by simp [hl]; omega)
      (hjr := by simp)
      (hj := by rw [rd_append_left (by rw [posHead_size]; omega), posHead_rd0])
      (hcr := by unfold curOfY; split_ifs <;> simp [hl] <;> omega) (hc := ?_)]
    · simp [Array.append_assoc, Bool.and_assoc, posHeadVals]
    · by_cases hs : sb = 0
      · rw [curOfY, if_pos hs, show r.size + 3 - 1 = r.size + 2 by omega,
          rd_append_left (by rw [posHead_size]; omega), posHead_rd2, h0 hs]
      · have hsb0 : 0 < sb := Nat.pos_of_ne_zero hs
        have e : curOfY sb (r.size + 3) = (r ++ (posHeadVals j col a wv).toArray).size + (6 * sb - 1) := by
          rw [curOfY, if_neg hs, hs4]; exact (by omega : r.size + 3 + 6 * sb = r.size + 4 + (6 * sb - 1))
        rw [e, rd_app, hlast hsb0]

/-- **The positions of a level** from `p` on, against `posAllT4`. -/
theorem exec_posAll4 (S : Seq) (k : KindP) (i co so dO : ℕ) (ans : List Reg) (w b : ℕ) (ad : ℕ → Digest)
    (wv : Array K) (t : ℕ) : ∀ (p : ℕ) (r : Array Val) (ok : Bool) (ops : List Op) (tr : Trace),
    r.size = b + 2 + posW4 S i * p → (∀ k, ans.getD k 0 < r.size) →
    (∀ k, (rd r (ans.getD k 0)).toD = ad k) → w < r.size → (rd r w).toAK = wv →
    exec impl κ inp (((List.range' p t).flatMap fun q =>
        posOps4 S k i co so dO ans w q (b + 2 + posW4 S i * q)) ++ ops) ⟨r, ok⟩ tr =
      (posAllT4 inp (S.lvK k.d.m i) (S.lv i).sib i co so dO ad wv t p tr).bind fun x =>
        exec impl κ inp ops ⟨r ++ x.1.toArray, ok && x.2.1⟩ x.2.2 := by
  induction t with
  | zero => intro p r ok ops tr _ _ _ _ _; simp [posAllT4]
  | succ t ih =>
    intro p r ok ops tr hs hA had hw hwv
    have h := exec_posOps4 impl κ inp S k i co so dO ans w p r ok
      (((List.range' (p + 1) t).flatMap fun q => posOps4 S k i co so dO ans w q (b + 2 + posW4 S i * q)) ++ ops)
      ad wv hA had hw hwv tr
    rw [hs] at h
    rw [List.range'_succ, List.flatMap_cons, List.append_assoc, h]
    simp only [posAllT4, Option.bind_assoc, Option.bind_map]
    refine Option.bind_congr fun x hx => ?_
    have hl := posT4_length inp hx
    rw [ih (p + 1) (r ++ x.1.toArray) _ ops x.2.2 (by simp [hl, hs, posW4, Nat.mul_succ]; omega)
      (fun k => by simp; exact Nat.lt_add_right _ (hA k))
      (fun k => by rw [rd_append_left (hA k), had]) (by simp; exact Nat.lt_add_right _ hw)
      (by rw [rd_append_left hw, hwv])]
    simp [Array.append_assoc, Bool.and_assoc]

end Exec

/-! ## The Merkle paths on the log -/

section Path
variable (inp : Input)

/-- **The Merkle steps are a climb on the log** (3.x's `stepsT_path`). -/
theorem stepsT4_path {L : Log} (hL : (L.map Prod.fst).Nodup) {sib i j : ℕ} :
    ∀ (n h so : ℕ) (cur : Digest) (tr : Trace) (x : List Val × Bool × Digest × Trace),
      stepsT4 inp sib i j n h so cur tr = some x → (∀ e ∈ tr, e ∈ L) → sib ≤ h + n →
      ∃ ss : List Digest, ss.length = sib - h ∧ (climb (frEnc i) j h cur ss).runLog L = some x.2.2.1
  | 0, h, _, cur, tr, x, hx, _, hs => by
    simp only [stepsT4, Option.some.injEq] at hx; subst hx
    exact ⟨[], by simp; omega, rfl⟩
  | n + 1, h, so, cur, (q, a) :: tr, x, hx, hin, hs => by
    simp only [stepsT4, Option.bind_eq_some_iff, Option.map_eq_some_iff] at hx
    obtain ⟨z, hz, y, hy, rfl⟩ := hx
    simp only [stepT4, Option.ite_none_right_eq_some] at hz
    obtain ⟨hq, hz⟩ := hz
    simp only [Option.some.injEq] at hz; subst hz
    have hin' : ∀ e ∈ tr, e ∈ L := fun e he => hin e (List.mem_cons_of_mem _ he)
    have hmem : (q, a) ∈ L := hin _ (List.mem_cons_self ..)
    by_cases hact : h < sib
    · simp only [hact, decide_true, ite_true] at hq hy ⊢
      obtain ⟨ss, hl, hr⟩ := stepsT4_path hL n (h + 1) _ a tr y hy hin' (by omega)
      refine ⟨bytesAt inp.π (absOff 0 so) 32 :: ss, by simp [hl]; omega, ?_⟩
      have hm' : (stepQ (frEnc i) j h cur (bytesAt inp.π (absOff 0 so) 32), a) ∈ L := by
        convert hmem using 2; rw [hq]; simp only [stepQ, frEnc]; split_ifs <;> rfl
      rw [climb, runLog_query_mem hL hm']
      exact hr
    · simp only [hact, decide_false, Bool.false_eq_true, ite_false] at hy ⊢
      obtain ⟨ss, hl, hr⟩ := stepsT4_path hL n (h + 1) _ cur tr y hy hin' (by omega)
      have hss : ss = [] := List.eq_nil_of_length_eq_zero (by omega)
      subst hss
      exact ⟨[], by simp; omega, by simpa [climb] using hr⟩
  | _ + 1, _, _, _, [], x, hx, _, _ => by simp [stepsT4, stepT4] at hx

/-- **One position on the log** (3.x's `posT_path`; revision 4.4.1: the path to the committed
digest `D_r`, the cap index and `D_r` in registers `4 + 6·sL`, `4 + 6·sL + 1`). -/
theorem posT4_path {L : Log} (hL : (L.map Prod.fst).Nodup) {Lk : Level} {sL i co so dO p : ℕ}
    {ad : ℕ → Digest} {w : Array K} {tr : Trace} {x : List Val × Bool × Trace}
    (hx : posT4 inp Lk sL i co so dO ad w p tr = some x) (hin : ∀ e ∈ tr, e ∈ L)
    (hsib : Lk.sib ≤ sL) (hok : x.2.1 = true) :
    let j := idxOf Lk.logN (ad (p / Lk.per)) (p % Lk.per)
    let col := inp.π.extract (absOff 0 (co + p * colBytes i)) (absOff 0 (co + p * colBytes i) + colBytes i)
    x.1.getD 0 default = .n j ∧ x.1.getD 3 default = .k (dotKF w col) ∧
      x.1.getD (4 + 6 * sL) default = .n (j >>> Lk.sib) ∧
      x.1.getD (4 + 6 * sL + 1) default = .d (bytesAt inp.π (absOff 0 (dO + 32 * p)) 32) ∧
      (∃ ss : List Digest, ss.length = Lk.sib ∧ (openPath (frEnc i) col j ss).runLog L =
        some (bytesAt inp.π (absOff 0 (dO + 32 * p)) 32)) ∧
      ∃ seg, tr = seg ++ x.2.2 := by
  intro j col
  rcases tr with _ | ⟨⟨q, a⟩, tr⟩
  · cases hx
  simp only [posT4] at hx
  split_ifs at hx with hq
  obtain ⟨y, hy, rfl⟩ := Option.map_eq_some_iff.1 hx
  simp only [Bool.and_eq_true, decide_eq_true_eq] at hok
  obtain ⟨ss, hl, hr⟩ := stepsT4_path inp hL _ 0 _ a tr y hy
    (fun e he => hin e (List.mem_cons_of_mem _ he)) (by omega)
  obtain ⟨seg, hseg, -⟩ := stepsT4_len inp hy
  have hl6 := (stepsT4_spec inp hy).1
  have hpre : ([Val.n j, .b col, .d a, .k (dotKF w col)] ++ y.1).length = 4 + 6 * sL := by
    simp only [List.length_append, List.length_cons, List.length_nil, hl6]
  refine ⟨rfl, rfl, ?_, ?_, ⟨ss, by simpa using hl, ?_⟩, ⟨(q, a) :: seg, by simp [hseg]⟩⟩
  · rw [List.getD_append_right _ _ _ _ (by rw [hpre]), hpre, Nat.sub_self]; rfl
  · rw [List.getD_append_right _ _ _ _ (by rw [hpre]; omega), hpre,
      show 4 + 6 * sL + 1 - (4 + 6 * sL) = 1 by omega]; rfl
  · have hmem : (q, a) ∈ L := hin _ (List.mem_cons_self ..)
    rw [openPath, runLog_query_mem hL (show ((frEnc i).colQ col, a) ∈ L by rw [hq] at hmem; exact hmem),
      hr, hok.2]

/-- **All positions on the log** (3.x's `posAllT_path`; revision 4.4.1: as `posT4_path`). -/
theorem posAllT4_path {L : Log} (hL : (L.map Prod.fst).Nodup) {Lk : Level} {sL i co so dO : ℕ}
    {ad : ℕ → Digest} {w : Array K} (hsib : Lk.sib ≤ sL) :
    ∀ (t p : ℕ) (tr : Trace) (x : List Val × Bool × Trace),
      posAllT4 inp Lk sL i co so dO ad w t p tr = some x → (∀ e ∈ tr, e ∈ L) → x.2.1 = true →
      ∀ q < t,
        x.1.getD ((4 + 6 * sL + 2) * q) default = .n (idxOf Lk.logN (ad ((p + q) / Lk.per)) ((p + q) % Lk.per)) ∧
        x.1.getD ((4 + 6 * sL + 2) * q + 3) default = .k (dotKF w (inp.π.extract
          (absOff 0 (co + (p + q) * colBytes i)) (absOff 0 (co + (p + q) * colBytes i) + colBytes i))) ∧
        x.1.getD ((4 + 6 * sL + 2) * q + (4 + 6 * sL)) default =
          .n (idxOf Lk.logN (ad ((p + q) / Lk.per)) ((p + q) % Lk.per) >>> Lk.sib) ∧
        x.1.getD ((4 + 6 * sL + 2) * q + (4 + 6 * sL + 1)) default =
          .d (bytesAt inp.π (absOff 0 (dO + 32 * (p + q))) 32) ∧
        ∃ ss : List Digest, ss.length = Lk.sib ∧
          (openPath (frEnc i) (inp.π.extract (absOff 0 (co + (p + q) * colBytes i))
            (absOff 0 (co + (p + q) * colBytes i) + colBytes i))
            (idxOf Lk.logN (ad ((p + q) / Lk.per)) ((p + q) % Lk.per)) ss).runLog L =
          some (bytesAt inp.π (absOff 0 (dO + 32 * (p + q))) 32)
  | 0, _, _, _, _, _, _, q, hq => absurd hq (by omega)
  | t + 1, p, tr, x, hx, hin, hok, q, hq => by
    simp only [posAllT4, Option.bind_eq_some_iff, Option.map_eq_some_iff] at hx
    obtain ⟨z, hz, y, hy, rfl⟩ := hx
    simp only [Bool.and_eq_true] at hok
    obtain ⟨h0, h3, hk, hd, hpath, seg, hseg⟩ := posT4_path inp hL hz hin hsib hok.1
    have hzl := posT4_length inp hz
    rcases q with _ | q
    · refine ⟨?_, ?_, ?_, ?_, ?_⟩
      · rw [Nat.mul_zero, List.getD_append _ _ _ _ (by rw [hzl]; omega)]; simpa using h0
      · rw [Nat.mul_zero, Nat.zero_add, List.getD_append _ _ _ _ (by rw [hzl]; omega)]
        simpa using h3
      · rw [Nat.mul_zero, Nat.zero_add, List.getD_append _ _ _ _ (by rw [hzl]; omega)]
        simpa using hk
      · rw [Nat.mul_zero, Nat.zero_add, List.getD_append _ _ _ _ (by rw [hzl]; omega)]
        simpa using hd
      · simpa using hpath
    · obtain ⟨i0, i3, ik, id, ip⟩ := posAllT4_path hL hsib t (p + 1) _ y hy
        (fun e he => hin e (by rw [hseg]; exact List.mem_append_right _ he)) hok.2 q (by omega)
      rw [show p + (q + 1) = p + 1 + q by omega]
      refine ⟨?_, ?_, ?_, ?_, ip⟩
      · rw [show (4 + 6 * sL + 2) * (q + 1) = z.1.length + (4 + 6 * sL + 2) * q by rw [hzl]; ring,
          List.getD_append_right _ _ _ _ (by omega), Nat.add_sub_cancel_left, i0]
      · rw [show (4 + 6 * sL + 2) * (q + 1) + 3 = z.1.length + ((4 + 6 * sL + 2) * q + 3) by rw [hzl]; ring,
          List.getD_append_right _ _ _ _ (by omega), Nat.add_sub_cancel_left, i3]
      · rw [show (4 + 6 * sL + 2) * (q + 1) + (4 + 6 * sL) =
            z.1.length + ((4 + 6 * sL + 2) * q + (4 + 6 * sL)) by rw [hzl]; ring,
          List.getD_append_right _ _ _ _ (by omega), Nat.add_sub_cancel_left, ik]
      · rw [show (4 + 6 * sL + 2) * (q + 1) + (4 + 6 * sL + 1) =
            z.1.length + ((4 + 6 * sL + 2) * q + (4 + 6 * sL + 1)) by rw [hzl]; ring,
          List.getD_append_right _ _ _ _ (by omega), Nat.add_sub_cancel_left, id]

end Path

end FR.Snd.R4

end G6_FRSoundness4R4PosT

section G6_FRSoundness4R4Qv

-- New for `flock-recursive` (BLUEPRINT revision 4.1, A.4, A.9, §5.1; track R4g). The 3.x templates are
-- `FRSoundnessAccLvl`'s `pos_view` and `queries_view`.

/-!
# P2.i's answers and Q.i's positions on an accepted `gen4` run

* **The context along a level** (abstract `S`): a K rounds phase sets `foldR` to its challenge
  registers (`genPhase4_roundsK_foldR`); an absorb keeps `foldR` and `posAns`
  (`genPhase4_absorb_ctx`); a `.pos` squeeze keeps `foldR` and sets `posAns` (`genPhase4_pos_ctx`).
* **`exec_queries4`**: the queries phase's ops are `packK`, `eqTableK`, then `posAllT4`.
* **`pos_view4`**: a `.pos` squeeze leaves its answers in the skeleton's registers.
* **`queries_view4`** (3.x's `queries_view`): per position `q`, the index register, the fold
  register holding `dotKF (eqTab fr) col_q`, the cap-index and committed-digest registers
  (revision 4.4.1, (β′)), and a path on the log from `col_q` to its committed digest `D_r`, π's
  32 bytes at `dOff4 seq4 i + 32·q`.
-/

namespace FR.Snd.R4
open RecursionFast Rev4 FR.Merkle

/-! ## The generator's context (abstract `S`) -/

section Gen
variable (S : Seq) (p : KindP) (n : ℕ) (name : String) (c : GCtx)

theorem genPhase4_roundsK_foldR {f k : ℕ} (hnm : initClaim name = .free) :
    (genPhase4 S p n (name, .rounds f k 2 true) c).2.foldR =
      (List.range k).map (fun j => c.next + 13 * j + 6) := by
  simp only [genPhase4]
  rw [hnm]
  simp only [initOps, Init.width, ↓reduceIte]
  exact List.map_congr_left fun j _ => by omega

theorem genPhase4_absorb_ctx {f len : ℕ} :
    (genPhase4 S p n (name, .absorb f len) c).2.foldR = c.foldR ∧
      (genPhase4 S p n (name, .absorb f len) c).2.posAns = c.posAns := by
  simp only [genPhase4]; split_ifs <;> exact ⟨rfl, rfl⟩

theorem genPhase4_pos_ctx {k i : ℕ} :
    (genPhase4 S p n (name, .squeezes k (.pos i)) c).2.foldR = c.foldR ∧
      (genPhase4 S p n (name, .squeezes k (.pos i)) c).2.posAns = (List.range k).map (c.next + ·) ∧
      (genPhase4 S p n (name, .squeezes k (.pos i)) c).2.outs.back?.getD [] =
        (List.range k).map (c.next + ·) := by
  simp [genPhase4]

theorem genPhase4_queries_ops (i : ℕ) :
    (genPhase4 S p n (name, .queries i) c).1 = [.packK c.foldR, .eqTableK c.next] ++
      (List.range' 0 (S.lv i).t).flatMap fun q =>
        posOps4 S p i (fieldOffOf S fCols + phaseOffOf S n fCols) (fieldOffOf S fSibs + phaseOffOf S n fSibs)
          (dOff4 S i) c.posAns (c.next + 1) q (c.next + 2 + posW4 S i * q) := by
  simp only [genPhase4, List.range_eq_range']

theorem genPhase4_queries_outs (i : ℕ) :
    (genPhase4 S p n (name, .queries i) c).2.outs.back?.getD [] =
      (List.range (S.lv i).t).map fun q => c.next + 2 + posW4 S i * q + 3 := by
  simp [genPhase4]

end Gen

/-! ## `exec` of the queries phase -/

theorem exec_queries4 (impl : OpImpl) (κ : Kind) (inp : Input) (S : Seq) (p : KindP) (n : ℕ)
    (name : String) (i : ℕ) (c : GCtx) (r : Array Val) (ok : Bool) (tr : Trace) (hb : c.next = r.size)
    (hc : CtxOk c r) :
    let fr := (c.foldR.map fun x => (rd r x).toK).toArray
    exec impl κ inp (genPhase4 S p n (name, .queries i) c).1 ⟨r, ok⟩ tr =
      (posAllT4 inp (S.lvK p.d.m i) (S.lv i).sib i (fieldOffOf S fCols + phaseOffOf S n fCols)
          (fieldOffOf S fSibs + phaseOffOf S n fSibs) (dOff4 S i)
          (fun k => (rd r (c.posAns.getD k 0)).toD) (eqTab fr) (S.lv i).t 0 tr).map fun x =>
        (⟨r ++ ([Val.ak fr, .ak (eqTab fr)] ++ x.1).toArray, ok && x.2.1⟩, x.2.2) := by
  intro fr
  have hpos : 0 < r.size := lt_of_le_of_lt (Nat.zero_le _) hc.1
  rw [genPhase4_queries_ops, hb, show (⟨r, ok⟩ : St) = ⟨r ++ ([] : List Val).toArray, ok⟩ by simp]
  have hfr : (c.foldR.map fun x => (rd (r ++ ([] : List Val).toArray) x).toK) = c.foldR.map fun x => (rd r x).toK :=
    List.map_congr_left fun x hx => by rw [rd_app_left _ _ (hc.2.2.2.1 x hx)]
  have hrd : rd (r ++ #[Val.ak fr]) r.size = .ak fr := by simpa using rd_app0 r [Val.ak fr]
  simp only [List.cons_append, List.nil_append, exec_app, evalOp, hfr, Bool.and_true]
  rw [hrd]
  set r' := r ++ ([Val.ak fr, Val.ak (eqTab fr)] : List Val).toArray with hr'
  have hsz : r'.size = r.size + 2 := by simp [hr']
  have hA0 : ∀ k, c.posAns.getD k 0 < r.size := fun k => by
    rw [List.getD_eq_getElem?_getD]
    rcases hk : c.posAns[k]? with _ | z
    · simpa using hpos
    · simpa using hc.2.2.1 z (List.mem_of_getElem? hk)
  have hA : ∀ k, c.posAns.getD k 0 < r'.size := fun k => by rw [hsz]; exact Nat.lt_add_right 2 (hA0 k)
  have e := exec_posAll4 impl κ inp S p i (fieldOffOf S fCols + phaseOffOf S n fCols)
      (fieldOffOf S fSibs + phaseOffOf S n fSibs) (dOff4 S i) c.posAns (r.size + 1) r.size
      (fun k => (rd r (c.posAns.getD k 0)).toD) (eqTab fr) (S.lv i).t 0 r' ok [] tr (by rw [hsz]; ring)
      hA (fun k => by rw [hr', rd_app_left _ _ (hA0 k)]) (by rw [hsz]; omega) (by rw [hr', rd_app]; rfl)
  rw [List.append_nil] at e
  show exec impl κ inp _ ⟨r', ok⟩ tr = _
  rw [e, Option.map_eq_bind]
  refine Option.bind_congr fun x _ => ?_
  simp [exec, hr', Array.append_assoc]

/-! ## The views -/

section V
variable {impl : OpImpl} {p : KindP} {inp : Input} {tr : Trace} {y : List Val × List Bool × Trace}

/-- **A `.pos` squeeze on the skeleton's registers** (P2.i): its registers are `next + l`, holding
the log's answers from `phStart4 n`. -/
theorem pos_view4 (h : SkRun4 impl p inp tr y) {n : ℕ} (hn : n < (phasesOf seq4).length) {k i : ℕ}
    (hsh : (phasesOf seq4)[n].2 = .squeezes k (.pos i)) (hk : 0 < k) :
    (skeleton4 seq4 p).2.outs.getD n [] = (List.range k).map ((cAt4 seq4 p n).next + ·) ∧
      (cAt4 seq4 p n).next + k ≤ (#[] ++ y.1.toArray).size ∧
      ∀ l < k, rd (#[] ++ y.1.toArray) ((cAt4 seq4 p n).next + l) =
        .d (ansAt (fsOf tr (itemsOf seq4)) (phStart4 n + l)) := by
  obtain ⟨trk, M, x, hx, hb, -, hext, -, hdrop, -⟩ := phase_at4 impl p.tix inp p h.ref hn
  generalize hph : (phasesOf seq4)[n] = ph at hx hsh
  obtain ⟨name, sh⟩ := ph
  simp only at hsh; subst hsh
  simp only [refPhase4] at hx
  obtain ⟨xs, hxs, rfl⟩ := Option.map_eq_some_iff.1 hx
  obtain ⟨hl, hans⟩ := sqz_entries4 hn (by rw [hph]) hk hxs hdrop
  dsimp only at hext
  have hsz := hext.1
  simp only [Array.size_append, List.size_toArray, List.length_append, List.length_map, hl] at hsz
  refine ⟨?_, by rw [hb]; simpa using hsz, fun l hl' => ?_⟩
  · rw [skeleton4_outs seq4 p hn, hph, (genPhase4_pos_ctx seq4 p n name _).2.2]
  · rw [hb, rd_phase4 hext (by simp [hl]; omega), List.getD_eq_getElem _ _ (by simp [hl]; omega),
      List.getElem_map, ← hans l hl', List.getD_eq_getElem _ _ (by omega)]

/-- **Q.i on the skeleton's registers and the log** (3.x's `queries_view`): with `fr` the context's
`foldR` values and `ad` its `posAns` answers, per position `q` the index register
`b + 2 + posW4·q`, the fold register `+ 3` holding `dotKF (eqTab fr) col_q`, the cap index
`j >>> sib` (`kOfY`) and the committed digest `D_r` (`dOfY`), and a path on `L` from `col_q` to `D_r`
(revision 4.4.1, (β′)). -/
theorem queries_view4 (h : SkRun4 impl p inp tr y) {L : Log} (hL : (L.map Prod.fst).Nodup)
    (hin : ∀ e ∈ tr, e ∈ L) {n : ℕ} (hn : n < (phasesOf seq4).length) {i : ℕ}
    (hsh : (phasesOf seq4)[n].2 = .queries i) (hsib : (seq4.lvK p.d.m i).sib ≤ (seq4.lv i).sib) :
    ∃ b, (skeleton4 seq4 p).2.outs.getD n [] =
        (List.range (seq4.lv i).t).map (fun q => b + 2 + posW4 seq4 i * q + 3) ∧
      b + 2 + posW4 seq4 i * (seq4.lv i).t ≤ (#[] ++ y.1.toArray).size ∧
      ∀ q < (seq4.lv i).t,
        let fr := ((cAt4 seq4 p n).foldR.map fun x => (rd (#[] ++ y.1.toArray) x).toK).toArray
        let ad := fun k => (rd (#[] ++ y.1.toArray) ((cAt4 seq4 p n).posAns.getD k 0)).toD
        let Lk := seq4.lvK p.d.m i
        let co := fieldOffOf seq4 fCols + phaseOffOf seq4 n fCols
        let col := inp.π.extract (absOff 0 (co + q * colBytes i)) (absOff 0 (co + q * colBytes i) + colBytes i)
        let j := idxOf Lk.logN (ad (q / Lk.per)) (q % Lk.per)
        rd (#[] ++ y.1.toArray) (b + 2 + posW4 seq4 i * q) = .n j ∧
        rd (#[] ++ y.1.toArray) (b + 2 + posW4 seq4 i * q + 3) = .k (dotKF (eqTab fr) col) ∧
        rd (#[] ++ y.1.toArray) (kOfY (seq4.lv i).sib (b + 2 + posW4 seq4 i * q + 3)) = .n (j >>> Lk.sib) ∧
        rd (#[] ++ y.1.toArray) (dOfY (seq4.lv i).sib (b + 2 + posW4 seq4 i * q + 3)) =
          .d (bytesAt inp.π (absOff 0 (dOff4 seq4 i + 32 * q)) 32) ∧
        ∃ ss : List Digest, ss.length = Lk.sib ∧ (openPath (frEnc i) col j ss).runLog L =
          some (bytesAt inp.π (absOff 0 (dOff4 seq4 i + 32 * q)) 32) := by
  obtain ⟨trk, M, x, hx, hb, hwf, hext, hflag, -, A, hA⟩ := phase_at4 impl p.tix inp p h.ref hn
  have hc : CtxOk (cAt4 seq4 p n) (#[] ++ M.toArray) := by
    rcases hwf with ⟨h', -⟩ | h'
    · rw [hsh] at h'; cases h'
    · exact h'
  generalize hph : (phasesOf seq4)[n] = ph at hx hsh
  obtain ⟨name, sh⟩ := ph
  simp only at hsh; subst hsh
  simp only [refPhase4] at hx
  rw [exec_queries4 impl p.tix inp seq4 p n name i _ _ true trk (by rw [hb]; simp) hc, Option.map_map] at hx
  obtain ⟨xq, hxq, rfl⟩ := Option.map_eq_some_iff.1 hx
  have hok : xq.2.1 = true := by simpa using h.flags _ hflag
  have hql := posAllT4_length inp hxq
  have hdrop : ((#[] ++ M.toArray) ++ ([Val.ak ((cAt4 seq4 p n).foldR.map fun x =>
      (rd (#[] ++ M.toArray) x).toK).toArray, .ak (eqTab ((cAt4 seq4 p n).foldR.map fun x =>
      (rd (#[] ++ M.toArray) x).toK).toArray)] ++ xq.1).toArray).toList.drop (#[] ++ M.toArray).size =
      [Val.ak ((cAt4 seq4 p n).foldR.map fun x => (rd (#[] ++ M.toArray) x).toK).toArray,
        .ak (eqTab ((cAt4 seq4 p n).foldR.map fun x => (rd (#[] ++ M.toArray) x).toK).toArray)] ++ xq.1 := by
    simp
  simp only [Function.comp, hdrop] at hext
  have hsz := hext.1
  simp only [Array.size_append, List.size_toArray, List.length_append, hql, List.length_cons,
    List.length_nil] at hsz
  have hpre : ∀ z < M.length, rd (#[] ++ M.toArray) z = rd (#[] ++ y.1.toArray) z := fun z hz => by
    rw [hext.rd (x := z) (by simp; omega), ← List.append_toArray, ← Array.append_assoc,
      rd_append_left (a := #[] ++ M.toArray) (by simpa using hz)]
  have hM0 : 0 < M.length := lt_of_le_of_lt (Nat.zero_le _) (by simpa using hc.1)
  have hfr : (cAt4 seq4 p n).foldR.map (fun x => (rd (#[] ++ M.toArray) x).toK) =
      (cAt4 seq4 p n).foldR.map (fun x => (rd (#[] ++ y.1.toArray) x).toK) :=
    List.map_congr_left fun x hx => by rw [hpre x (by simpa using hc.2.2.2.1 x hx)]
  have had : (fun k => (rd (#[] ++ M.toArray) ((cAt4 seq4 p n).posAns.getD k 0)).toD) =
      fun k => (rd (#[] ++ y.1.toArray) ((cAt4 seq4 p n).posAns.getD k 0)).toD := by
    funext k
    rw [hpre _ (by
      rw [List.getD_eq_getElem?_getD]
      rcases hk : (cAt4 seq4 p n).posAns[k]? with _ | z
      · simpa using hM0
      · simpa using hc.2.2.1 z (List.mem_of_getElem? hk))]
  rw [hfr, had] at hxq
  have hin' : ∀ e ∈ trk, e ∈ L := fun e he => hin e (by rw [hA]; exact List.mem_append_right _ he)
  have hpath := posAllT4_path inp hL hsib _ 0 trk xq hxq hin' hok
  refine ⟨M.length, ?_, by simp only [posW4]; simp at hsz ⊢; omega, fun q hq => ?_⟩
  · rw [skeleton4_outs seq4 p hn, hph, genPhase4_queries_outs, hb]
  · obtain ⟨p0, p3, pk, pd, pp⟩ := hpath q hq
    simp only [Nat.zero_add] at p0 p3 pk pd pp
    have hq' : (4 + 6 * (seq4.lv i).sib + 2) * q + 3 < (4 + 6 * (seq4.lv i).sib + 2) * (seq4.lv i).t := by
      have : q + 1 ≤ (seq4.lv i).t := hq
      nlinarith
    refine ⟨?_, ?_, ?_, ?_, pp⟩
    · rw [show M.length + 2 + posW4 seq4 i * q = M.length + (2 + posW4 seq4 i * q) by ring,
        rd_phase4 hext (by simp [hql, posW4]; nlinarith), List.getD_append_right _ _ _ _ (by simp),
        show 2 + posW4 seq4 i * q - [Val.ak _, Val.ak _].length = posW4 seq4 i * q by simp, posW4, p0]
    · rw [show M.length + 2 + posW4 seq4 i * q + 3 = M.length + (2 + (posW4 seq4 i * q + 3)) by ring,
        rd_phase4 hext (by simp [hql, posW4]; omega), List.getD_append_right _ _ _ _ (by simp),
        show 2 + (posW4 seq4 i * q + 3) - [Val.ak _, Val.ak _].length = posW4 seq4 i * q + 3 by simp, posW4, p3]
    · have e : kOfY (seq4.lv i).sib (M.length + 2 + posW4 seq4 i * q + 3) =
          M.length + (2 + ((4 + 6 * (seq4.lv i).sib + 2) * q + (4 + 6 * (seq4.lv i).sib))) := by
        simp only [kOfY, posW4]; ring
      rw [e, rd_phase4 hext (by simp [hql]; nlinarith), List.getD_append_right _ _ _ _ (by simp),
        show 2 + ((4 + 6 * (seq4.lv i).sib + 2) * q + (4 + 6 * (seq4.lv i).sib)) - [Val.ak _, Val.ak _].length =
          (4 + 6 * (seq4.lv i).sib + 2) * q + (4 + 6 * (seq4.lv i).sib) by simp, pk]
    · have e : dOfY (seq4.lv i).sib (M.length + 2 + posW4 seq4 i * q + 3) =
          M.length + (2 + ((4 + 6 * (seq4.lv i).sib + 2) * q + (4 + 6 * (seq4.lv i).sib + 1))) := by
        simp only [dOfY, posW4]; ring
      rw [e, rd_phase4 hext (by simp [hql]; nlinarith), List.getD_append_right _ _ _ _ (by simp),
        show 2 + ((4 + 6 * (seq4.lv i).sib + 2) * q + (4 + 6 * (seq4.lv i).sib + 1)) - [Val.ak _, Val.ak _].length =
          (4 + 6 * (seq4.lv i).sib + 2) * q + (4 + 6 * (seq4.lv i).sib + 1) by simp, pd]

end V

end FR.Snd.R4

end G6_FRSoundness4R4Qv
