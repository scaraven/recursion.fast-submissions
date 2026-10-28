-- New for `flock-recursive` (BLUEPRINT revision 4.1, A.4, A.9; stage R4b).
import FRSoundness4R4View
import FRSoundnessFrRndV

/-!
# The F rounds of an accepted `gen4` run, on the log (real round counts, every init)

A rounds phase `n` of `phasesOf seq4` (`.rounds f k deg false`, `deg ∈ {2, 3}`) runs `k` slots of
which the first `realRounds p name k` are real; a dummy round keeps the claim. On the log the
phase's entries sit at `P = phStart4 n` (`rounds_at4`), and the program's registers are the log's
running claims (no message table is needed: a round's query is `absorbQ d msg`, so the log's
`msgAt` *is* the program's message, `msgAt_of_q`):

* **`rounds3_log`** (degree 3): the claim after the run is `clR P c₀ … (min real (j + n))`;
* **`rounds2_log`** (degree 2): the claim after the run is `clR2 P … (min real (j + n))`, and every
  real round's check `Chk2 P …` holds (the program's `c₁ + c₂ = claim` assert);
* **`roundsF3_view4`**, **`roundsF2_view4`**: on the skeleton's registers. `outs[n]` is
  `cl :: rs ++ [last]` (`genPhase4_roundsF`), `cl` holds the initial claim (`.free`: round 0's
  `c₁ + c₂`; `.zero`: `0`; `.uni`: Z2's register, a hypothesis), `rs[j]` round `j`'s challenge
  `rch P es j`, `last` the claim after the real rounds.
-/

namespace FR.Snd.R4
open RecursionFast Rev4 FR.Impl

/-! ## The log's messages are the program's -/

theorem getLastD_append' (l l' : List α) (a : α) : (l ++ l').getLastD a = l'.getLastD (l.getLastD a) := by
  simp only [List.getLastD_eq_getLast?, List.getLast?_append]
  cases l'.getLast? <;> rfl

/-- A logged absorb's message is the absorbed bytes. -/
theorem msgAt_of_q {es : Log} {p : ℕ} {d : Digest} {m : ByteArray}
    (h : (es.getD p default).1 = absorbQ d m) : Snd.msgAt es p = m := by
  unfold Snd.msgAt entAt; rw [h]; exact extract40_absorbQ _ _

theorem readF_piMsg (inp : Input) (o off : ℕ) {len : ℕ} (h : off + 16 ≤ len) :
    readF (FR.msgAt inp 0 o len) off = elemAt inp 0 (o + off) := by
  simp only [readF, FR.msgAt, elemAt, absOff_zero]
  rw [bytesAt_extract_of_le16 _ h]

/-! ## Dummy rounds keep the claim -/

theorem getLastD_of_ne {l : List α} (h : l ≠ []) (a b : α) : l.getLastD a = l.getLastD b := by
  rw [List.getLastD_eq_getLast?, List.getLastD_eq_getLast?, List.getLast?_eq_getLast h]; rfl

theorem roundsT_dummy (inp : Input) (o deg real : ℕ) :
    ∀ (n j : ℕ) (d : Digest) (cv : Val) (tr : Trace) (x : List Val × Bool × Trace),
      roundsT inp 0 o deg false real n j d cv tr = some x → real ≤ j → x.1.getLastD cv = cv
  | 0, _, _, _, _, x, h, _ => by
    simp only [roundsT, Option.some.injEq] at h; subst h; rfl
  | n + 1, j, d, cv, (q₁, a₁) :: (q₂, a₂) :: tr, x, h, hj => by
    simp only [roundsT, Bool.false_eq_true, ite_false] at h
    have hre : decide (j < real) = false := decide_eq_false (by omega)
    split_ifs at h with hq hd <;>
    · obtain ⟨x', hx', rfl⟩ := Option.map_eq_some_iff.mp h
      have ih := roundsT_dummy inp o deg real n (j + 1) a₂ _ tr x' hx' (by omega)
      rw [getLastD_append']
      simp only [hre, round3V, round2Vals, Bool.false_eq_true, ite_false, List.getLastD_eq_getLast?,
        List.getLast?_cons_cons, List.getLast?_singleton, Option.getD_some] at ih ⊢
      exact ih
  | _ + 1, _, _, _, [], _, h, _ => by simp [roundsT] at h
  | _ + 1, _, _, _, [_], _, h, _ => by simp [roundsT] at h

/-! ## Real rounds on the log -/

/-- A round's two entries on the log: its message is π's, its challenge the answer's. -/
theorem round_entries {inp : Input} {o P j : ℕ} {es : Log} {q₁ q₂ : ByteArray} {a₁ a₂ d : Digest}
    {tr : Trace} (hq : q₁ = absorbQ d (FR.msgAt inp 0 (o + j * roundBytes false) (roundBytes false)))
    (he : ∀ m < 2, ((q₁, a₁) :: (q₂, a₂) :: tr).getD m default = es.getD (P + 2 * j + m) default) :
    (∀ off, off + 16 ≤ 48 → readF (Snd.msgAt es (P + 2 * j)) off = elemAt inp 0 (o + j * 48 + off)) ∧
      ansAt es (P + 2 * j + 1) = a₂ := by
  have e0 := he 0 (by norm_num); have e1 := he 1 (by norm_num)
  simp only [List.getD_cons_zero, List.getD_cons_succ, Nat.add_zero] at e0 e1
  refine ⟨fun off hoff => ?_, by rw [ansAt, entAt, ← e1]⟩
  rw [msgAt_of_q (p := P + 2 * j) (by rw [← e0]; exact hq)]
  exact readF_piMsg inp _ off hoff

theorem shift_entries {es : Log} {P j n : ℕ} {e₁ e₂ : ByteArray × Digest} {tr : Trace}
    (he : ∀ m < 2 * (n + 1), (e₁ :: e₂ :: tr).getD m default = es.getD (P + 2 * j + m) default) :
    ∀ m < 2 * n, tr.getD m default = es.getD (P + 2 * (j + 1) + m) default := fun m hm => by
  have := he (m + 2) (by omega)
  rw [List.getD_cons_succ, List.getD_cons_succ] at this
  rw [this]; congr 1; ring

/-- **Degree-3 F rounds on the log**: from claim `clR P c₀ … j` at round `j ≤ real`, the claim
after `n` rounds is `clR P c₀ … (min real (j + n))` (dummies keep it). -/
theorem rounds3_log (inp : Input) (o real P : ℕ) (es : Log) (c0 : Log → Log → F) (L : Log) :
    ∀ (n j : ℕ) (d : Digest) (cv : Val) (tr : Trace) (x : List Val × Bool × Trace),
      roundsT inp 0 o 3 false real n j d cv tr = some x →
      (∀ m < 2 * n, tr.getD m default = es.getD (P + 2 * j + m) default) →
      j ≤ real → cv = .f (clR P c0 L es j) →
      x.1.getLastD cv = .f (clR P c0 L es (min real (j + n)))
  | 0, j, _, cv, _, x, h, _, hj, hc => by
    simp only [roundsT, Option.some.injEq] at h; subst h
    rw [Nat.add_zero, Nat.min_eq_right hj]; exact hc
  | n + 1, j, d, cv, (q₁, a₁) :: (q₂, a₂) :: tr, x, h, he, hj, hc => by
    simp only [roundsT, Bool.false_eq_true, ite_false, ite_true] at h
    split_ifs at h with hq
    obtain ⟨x', hx', rfl⟩ := Option.map_eq_some_iff.mp h
    obtain ⟨hm, ha⟩ := round_entries hq.1 (fun m hm => he m (by omega))
    have hne : round3V inp 0 (o + j * roundBytes false) (decide (j < real)) a₁ a₂ cv ≠ [] := by
      simp [round3V]
    rw [getLastD_append', getLastD_of_ne hne cv default]
    rcases Nat.lt_or_ge j real with hjr | hjr
    · have hg : (round3V inp 0 (o + j * roundBytes false) (decide (j < real)) a₁ a₂ cv).getLastD
          default = .f (clR P c0 L es (j + 1)) := by
        simp only [round3V, decide_eq_true hjr, ite_true, List.getLastD_eq_getLast?,
          List.getLast?_cons_cons, List.getLast?_singleton, Option.getD_some, clR, g3At, rch, fAt, ha,
          peval_four, hc, Val.toF, roundBytes, Bool.false_eq_true, ite_false]
        rw [hm 0 (by norm_num), hm 16 (by norm_num), hm 32 (by norm_num), Nat.add_zero]; rfl
      rw [hg, rounds3_log inp o real P es c0 L n (j + 1) a₂ _ tr x' (hg ▸ hx') (shift_entries he)
        (by omega) rfl, show j + 1 + n = j + (n + 1) by omega]
    · have hjr' : j = real := by omega
      have hk : (round3V inp 0 (o + j * roundBytes false) (decide (j < real)) a₁ a₂ cv).getLastD
          default = cv := by
        simp [round3V, show ¬ j < real by omega]
      rw [hk, roundsT_dummy inp o 3 real n (j + 1) a₂ cv tr x' (hk ▸ hx') (by omega), hc, hjr',
        Nat.min_eq_left (by omega)]
  | _ + 1, _, _, _, [], _, h, _, _, _ => by simp [roundsT] at h
  | _ + 1, _, _, _, [_], _, h, _, _, _ => by simp [roundsT] at h

/-- **Degree-2 F rounds on the log**: from claim `clR2 P … j` at round `j ≤ real`, the claim
after `n` rounds is `clR2 P … (min real (j + n))`; on a passing run every real round's check holds. -/
theorem rounds2_log (inp : Input) (o real P : ℕ) (es : Log) (c0 : Log → Log → F) (L : Log) :
    ∀ (n j : ℕ) (d : Digest) (cv : Val) (tr : Trace) (x : List Val × Bool × Trace),
      roundsT inp 0 o 2 false real n j d cv tr = some x →
      (∀ m < 2 * n, tr.getD m default = es.getD (P + 2 * j + m) default) →
      j ≤ real → cv = .f (clR2 P 16 readF (fun d => chF d 0) c0 L es j) →
      x.1.getLastD cv = .f (clR2 P 16 readF (fun d => chF d 0) c0 L es (min real (j + n))) ∧
        (x.2.1 = true → ∀ l < n, j + l < real → Chk2 P 16 readF (fun d => chF d 0) c0 L es (j + l))
  | 0, j, _, cv, _, x, h, _, hj, hc => by
    simp only [roundsT, Option.some.injEq] at h; subst h
    exact ⟨by rw [Nat.add_zero, Nat.min_eq_right hj]; exact hc, fun _ l hl => absurd hl (by omega)⟩
  | n + 1, j, d, cv, (q₁, a₁) :: (q₂, a₂) :: tr, x, h, he, hj, hc => by
    simp only [roundsT, Bool.false_eq_true, ite_false, show (2 = 3) = False by decide] at h
    split_ifs at h with hq
    obtain ⟨x', hx', rfl⟩ := Option.map_eq_some_iff.mp h
    obtain ⟨hm, ha⟩ := round_entries hq.1 (fun m hm => he m (by omega))
    have hne : round2Vals inp 0 (o + j * roundBytes false) (decide (j < real)) a₁ a₂ cv ≠ [] := by
      simp [round2Vals]
    rcases Nat.lt_or_ge j real with hjr | hjr
    · have hg : (round2Vals inp 0 (o + j * roundBytes false) (decide (j < real)) a₁ a₂ cv).getLastD
          default = .f (clR2 P 16 readF (fun d => chF d 0) c0 L es (j + 1)) := by
        simp only [round2Vals, decide_eq_true hjr, ite_true, List.getLastD_eq_getLast?,
          List.getLast?_cons_cons, List.getLast?_singleton, Option.getD_some, clR2, g2At, rch2, ha,
          peval_three, g2, roundBytes, Bool.false_eq_true, ite_false]
        rw [hm 0 (by norm_num), hm 16 (by norm_num), show 2 * 16 = 32 by norm_num,
          hm 32 (by norm_num), Nat.add_zero]
        exact congrArg Val.f (by ring)
      obtain ⟨ih1, ih2⟩ := rounds2_log inp o real P es c0 L n (j + 1) a₂ _ tr x' (hg ▸ hx')
        (shift_entries he) (by omega) rfl
      refine ⟨?_, fun hx l hl hjl => ?_⟩
      · rw [getLastD_append', getLastD_of_ne hne cv default, hg, ih1,
          show j + 1 + n = j + (n + 1) by omega]
      · simp only [decide_eq_true hjr, Bool.not_true, Bool.false_or, Bool.true_or, Bool.and_true,
          Bool.and_eq_true] at hx
        rcases l with _ | l
        · have h0 := hx.1
          simp only [roundBytes, Bool.false_eq_true, ite_false, hc, eqv_f] at h0
          rw [Nat.add_zero, Chk2, g2At, charTwo_peval01F, hm 16 (by norm_num),
            show 2 * 16 = 32 by norm_num, hm 32 (by norm_num)]
          exact h0
        · rw [show j + (l + 1) = j + 1 + l by omega]
          exact ih2 hx.2 l (by omega) (by omega)
    · have hjr' : j = real := by omega
      have hk : (round2Vals inp 0 (o + j * roundBytes false) (decide (j < real)) a₁ a₂ cv).getLastD
          default = cv := by
        simp [round2Vals, show ¬ j < real by omega]
      refine ⟨?_, fun _ l _ hjl => absurd hjl (by omega)⟩
      rw [getLastD_append', getLastD_of_ne hne cv default, hk,
        roundsT_dummy inp o 2 real n (j + 1) a₂ cv tr x' (hk ▸ hx') (by omega), hc, hjr',
        Nat.min_eq_left (by omega)]
  | _ + 1, _, _, _, [], _, h, _, _, _ => by simp [roundsT] at h
  | _ + 1, _, _, _, [_], _, h, _, _, _ => by simp [roundsT] at h

/-! ## A rounds phase of the accepted skeleton -/

theorem rounds_itemsL_length (lv : ℕ → Level) (f k deg : ℕ) (inK : Bool) :
    ((Sh.rounds f k deg inK).itemsL lv).length = 2 * k := by
  simp [Sh.itemsL, Nat.mul_comm]

/-- The claim register's value a rounds phase starts from (`refPhase4`'s `cl`). -/
def clVal (inp : Input) (init : Init) (o : ℕ) (r : Array Val) (u : Reg) : Val :=
  match init with
  | .uni => rd r u
  | _ => (initVals inp init 0 o false).getLastD default

variable {impl : OpImpl} {p : KindP} {inp : Input}

/-- **A rounds phase of an accepted run** (`.rounds f k deg false`): before it the registers are
`#[] ++ M`; its `k` slots run `roundsT` with `realRounds p name k` real rounds from the claim
`clVal …`; its values `initVals ++ xr.1` extend into the run's registers; its `2k` entries are the
log's from `phStart4 n`. -/
theorem rounds_at4 {tr : Trace} {y : List Val × List Bool × Trace} (h : SkRun4 impl p inp tr y)
    {n : ℕ} (hn : n < (phasesOf seq4).length) {f k deg : ℕ}
    (hsh : (phasesOf seq4)[n].2 = .rounds f k deg false) :
    ∃ (M : List Val) (xr : List Val × Bool × Trace) (trk : Trace),
      (cAt4 seq4 p n).next = M.length ∧ CtxOk (cAt4 seq4 p n) (#[] ++ M.toArray) ∧
      roundsT inp 0 (fieldOffOf seq4 f + phaseOffOf seq4 n f) deg false
        (realRounds p (phasesOf seq4)[n].1 k) k 0 (rd (#[] ++ M.toArray) (cAt4 seq4 p n).st).toD
        (clVal inp (initClaim (phasesOf seq4)[n].1) (fieldOffOf seq4 f + phaseOffOf seq4 n f)
          (#[] ++ M.toArray) (cAt4 seq4 p n).uni) trk = some xr ∧
      ExtA (#[] ++ (M ++ (initVals inp (initClaim (phasesOf seq4)[n].1) 0
        (fieldOffOf seq4 f + phaseOffOf seq4 n f) false ++ xr.1)).toArray) (#[] ++ y.1.toArray) ∧
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
  refine ⟨M, xr, trk, hb, hok, ?_, hext, h.flags _ hflag, fun m hm => ?_⟩
  · convert hxr using 2; simp only [clVal]; generalize initClaim name = ic; cases ic <;> rfl
  · have hit : (phasesOf seq4)[n].2.itemsL seq4.lv = (Sh.rounds f k deg false).itemsL seq4.lv := by
      rw [hph]
    rw [List.drop_eq_getElem_cons hn, psItems4, List.flatMap_cons, hit] at hdrop
    rw [rounds_itemsL_length] at hsl
    obtain ⟨-, hent⟩ := seg_entries hdrop hseg (by rw [hsl, rounds_itemsL_length])
      (itemsL_allFS _ (by simp)) (by rw [rounds_itemsL_length]; omega)
    exact hent m (by rw [rounds_itemsL_length]; exact hm)

theorem lt_reg {a b : ℕ} (h : a < b) : (a : Reg) < b := h

/-- The register of a rounds phase's first claim (`initOps`' second component). -/
def clReg (init : Init) (u b : Reg) : Reg :=
  match init with
  | .uni => u
  | .zero => b
  | .free => b + 2

/-- **A rounds phase's out list** (`genPhase4`): the first claim, the `k` challenges, the last claim. -/
theorem genPhase4_rounds (S : Seq) (p : KindP) (n : ℕ) (name : String) (f k deg : ℕ) (c : GCtx) :
    (genPhase4 S p n (name, .rounds f k deg false) c).2.outs.back?.getD [] =
      clReg (initClaim name) c.uni c.next ::
        (List.range k).map (fun j => c.next + (initClaim name).width + roundW deg * j + 3) ++
        [if k = 0 then clReg (initClaim name) c.uni c.next
          else c.next + (initClaim name).width + roundW deg * k - 1] := by
  simp only [genPhase4]
  generalize initClaim name = ic
  cases ic <;> simp [initOps, Init.width, clReg]

/-- **A rounds phase on the skeleton's registers** (any degree, any init): `outs[n]` is
`cl :: rs ++ [last]`; `cl` holds `clVal` (the claim the rounds start from), `rs[j]` round `j`'s
challenge `rch P es j`; the rounds' run `xr` passes, reads the log from `P`, and `last` holds its
last claim. -/
theorem rounds_core4 {tr : Trace} {y : List Val × List Bool × Trace} (h : SkRun4 impl p inp tr y)
    {n : ℕ} (hn : n < (phasesOf seq4).length) {f k deg : ℕ}
    (hsh : (phasesOf seq4)[n].2 = .rounds f k deg false) :
    ∃ b : ℕ, (skeleton4 seq4 p).2.outs.getD n [] =
        clReg (initClaim (phasesOf seq4)[n].1) (cAt4 seq4 p n).uni b ::
          (List.range k).map (fun j => b + (initClaim (phasesOf seq4)[n].1).width + roundW deg * j + 3) ++
          [if k = 0 then clReg (initClaim (phasesOf seq4)[n].1) (cAt4 seq4 p n).uni b
            else b + (initClaim (phasesOf seq4)[n].1).width + roundW deg * k - 1] ∧
      b + (initClaim (phasesOf seq4)[n].1).width + roundW deg * k ≤ (#[] ++ y.1.toArray).size ∧
      clReg (initClaim (phasesOf seq4)[n].1) (cAt4 seq4 p n).uni b < (#[] ++ y.1.toArray).size ∧
      rd (#[] ++ y.1.toArray) (clReg (initClaim (phasesOf seq4)[n].1) (cAt4 seq4 p n).uni b) =
        clVal inp (initClaim (phasesOf seq4)[n].1) (fieldOffOf seq4 f + phaseOffOf seq4 n f)
          (#[] ++ y.1.toArray) (cAt4 seq4 p n).uni ∧
      (∀ j < k, rd (#[] ++ y.1.toArray) (b + (initClaim (phasesOf seq4)[n].1).width + roundW deg * j + 3) =
        .f (rch (phStart4 n) (fsOf tr (itemsOf seq4)) j)) ∧
      ∃ (xr : List Val × Bool × Trace) (d : Digest) (trk : Trace),
        roundsT inp 0 (fieldOffOf seq4 f + phaseOffOf seq4 n f) deg false
          (realRounds p (phasesOf seq4)[n].1 k) k 0 d
          (clVal inp (initClaim (phasesOf seq4)[n].1) (fieldOffOf seq4 f + phaseOffOf seq4 n f)
            (#[] ++ y.1.toArray) (cAt4 seq4 p n).uni) trk = some xr ∧ xr.2.1 = true ∧
        (∀ m < 2 * k, trk.getD m default = (fsOf tr (itemsOf seq4)).getD (phStart4 n + 2 * 0 + m) default) ∧
        (0 < k → rd (#[] ++ y.1.toArray) (b + (initClaim (phasesOf seq4)[n].1).width + roundW deg * k - 1) =
          xr.1.getLastD (clVal inp (initClaim (phasesOf seq4)[n].1)
            (fieldOffOf seq4 f + phaseOffOf seq4 n f) (#[] ++ y.1.toArray) (cAt4 seq4 p n).uni)) := by
  obtain ⟨M, xr, trk, hb, hok, hxr, hext, hfl, hent⟩ := rounds_at4 h hn hsh
  have hout := skeleton4_outs seq4 p hn
  generalize hph : (phasesOf seq4)[n] = ph at hsh hxr hext hout ⊢
  obtain ⟨name, sh⟩ := ph
  simp only at hsh; subst hsh
  simp only at hxr hext ⊢
  rw [genPhase4_rounds, hb] at hout
  have huM : (cAt4 seq4 p n).uni < M.length := by simpa using hok.2.1
  generalize fieldOffOf seq4 f + phaseOffOf seq4 n f = o at hxr hext ⊢
  generalize hR0 : #[] ++ y.1.toArray = R0 at hext ⊢
  obtain ⟨u, hu'⟩ : ∃ u : ℕ, (cAt4 seq4 p n).uni = u := ⟨_, rfl⟩
  rw [hu'] at hxr hout huM ⊢
  replace huM : u < M.length := huM
  obtain ⟨hv1, hv2⟩ := roundsT_chalF inp 0 o deg _ k 0 _ _ trk xr hxr
  have hiv := initValsF_length (inp := inp) (initClaim name) 0 o
  have hsz := size_le_of_ext hext
  simp only [List.length_append, hiv, hv1] at hsz
  have hrd : ∀ m < (initClaim name).width + roundW deg * k,
      rd R0 (M.length + m) = (initVals inp (initClaim name) 0 o false ++ xr.1).getD m default :=
    fun m hm => rd_phase4 hext (by simp [hiv, hv1]; omega)
  have hu : rd (#[] ++ M.toArray) u = rd R0 u := by
    have hlt : u < (#[] ++ (M ++ (initVals inp (initClaim name) 0 o false ++ xr.1)).toArray).size := by
      simp only [Array.size_append, List.size_toArray, List.length_append, Array.size_empty, List.length_nil]; omega
    rw [hext.2 _ hlt, show (#[] : Array Val) ++ (M ++ (initVals inp (initClaim name) 0 o false ++
      xr.1)).toArray = (#[] ++ M.toArray) ++ (initVals inp (initClaim name) 0 o false ++ xr.1).toArray
      by simp, rd_app_left (#[] ++ M.toArray) _ (by simpa using huM)]
  have hcv : clVal inp (initClaim name) o (#[] ++ M.toArray) u = clVal inp (initClaim name) o R0 u := by
    simp only [clVal]; generalize initClaim name = ic; cases ic
    exacts [hu, rfl, rfl]
  rw [hcv] at hxr
  have hw : 4 ≤ roundW deg := by unfold roundW; split <;> omega
  refine ⟨M.length, hout, by omega, ?_, ?_, fun j hj => ?_, xr, _, trk, hxr, hfl,
    fun m hm => by simpa using hent m hm, fun hk => ?_⟩
  · simp only [clReg]; generalize hic : initClaim name = ic at hsz ⊢
    cases ic <;> simp only [Init.width] at hsz ⊢ <;> dsimp only [Reg] <;> omega
  · simp only [clReg, clVal]
    generalize hic : initClaim name = ic at hrd hiv
    cases ic
    · rfl
    · rw [show M.length = M.length + 0 from rfl, hrd 0 (by simp [Init.width] <;> omega)]; rfl
    · rw [hrd 2 (by simp [Init.width] <;> omega)]; rfl
  · have hlt : roundW deg * j + 3 < xr.1.length := by
      rw [hv1]
      have : roundW deg * j + roundW deg ≤ roundW deg * k := by
        rw [← Nat.mul_succ]; exact Nat.mul_le_mul_left _ hj
      omega
    rw [show M.length + (initClaim name).width + roundW deg * j + 3 =
        M.length + ((initClaim name).width + (roundW deg * j + 3)) by ring,
      hrd _ (by omega), List.getD_append_right _ _ _ _ (by omega), hiv, Nat.add_sub_cancel_left,
      hv2 j hj, sqAns, hent _ (by omega)]
    rfl
  · have hne : xr.1 ≠ [] := by
      intro he; rw [he] at hv1; simp at hv1; have := Nat.mul_pos (by omega : 0 < roundW deg) hk; omega
    rw [show M.length + (initClaim name).width + roundW deg * k - 1 =
        M.length + ((initClaim name).width + (roundW deg * k - 1)) by
          have := Nat.mul_pos (by omega : 0 < roundW deg) hk; omega,
      hrd _ (by have := Nat.mul_pos (by omega : 0 < roundW deg) hk; omega),
      List.getD_append_right _ _ _ _ (by omega), hiv, Nat.add_sub_cancel_left,
      getLastD_of_ne hne _ default, List.getLastD_eq_getLast?, List.getLast?_eq_getElem?,
      List.getD_eq_getElem?_getD, hv1]

/-- The first round's message on the log (any degree). -/
theorem roundsT_first (inp : Input) (o deg real P : ℕ) (es : Log) {n j : ℕ} {d : Digest} {cv : Val}
    {tr : Trace} {x : List Val × Bool × Trace} (h : roundsT inp 0 o deg false real (n + 1) j d cv tr = some x)
    (he : ∀ m < 2 * (n + 1), tr.getD m default = es.getD (P + 2 * j + m) default) :
    ∀ off, off + 16 ≤ 48 → readF (Snd.msgAt es (P + 2 * j)) off = elemAt inp 0 (o + j * 48 + off) := by
  rcases tr with _ | ⟨⟨q₁, a₁⟩, _ | ⟨⟨q₂, a₂⟩, tr⟩⟩
  · simp [roundsT] at h
  · simp [roundsT] at h
  simp only [roundsT] at h
  split_ifs at h with hq <;> exact (round_entries hq.1 (fun m hm => he m (by omega))).1

/-- **A degree-3 F rounds phase on the skeleton's registers** (Z3, Lr2, E2): with `cl = outs[n]`'s
head holding `c`, its `j`-th challenge register holds `rch P es j`, and its last register the claim
after the real rounds, `clR P c … (min real k)`. -/
theorem roundsF3_view4 {tr : Trace} {y : List Val × List Bool × Trace} (h : SkRun4 impl p inp tr y)
    {n : ℕ} (hn : n < (phasesOf seq4).length) {f k : ℕ}
    (hsh : (phasesOf seq4)[n].2 = .rounds f k 3 false) (L : Log) :
    ((skeleton4 seq4 p).2.outs.getD n []).headD 0 < (#[] ++ y.1.toArray).size ∧
      rd (#[] ++ y.1.toArray) (((skeleton4 seq4 p).2.outs.getD n []).headD 0) =
        clVal inp (initClaim (phasesOf seq4)[n].1) (fieldOffOf seq4 f + phaseOffOf seq4 n f)
          (#[] ++ y.1.toArray) (cAt4 seq4 p n).uni ∧
      (∀ j < k, ((skeleton4 seq4 p).2.outs.getD n []).getD (j + 1) 0 < (#[] ++ y.1.toArray).size ∧
        rd (#[] ++ y.1.toArray) (((skeleton4 seq4 p).2.outs.getD n []).getD (j + 1) 0) =
          .f (rch (phStart4 n) (fsOf tr (itemsOf seq4)) j)) ∧
      ((skeleton4 seq4 p).2.outs.getD n []).getLastD 0 < (#[] ++ y.1.toArray).size ∧
      ∀ c : F, rd (#[] ++ y.1.toArray) (((skeleton4 seq4 p).2.outs.getD n []).headD 0) = .f c →
        rd (#[] ++ y.1.toArray) (((skeleton4 seq4 p).2.outs.getD n []).getLastD 0) =
          .f (clR (phStart4 n) (fun _ _ => c) L (fsOf tr (itemsOf seq4))
            (min (realRounds p (phasesOf seq4)[n].1 k) k)) := by
  obtain ⟨b, hout, hsz, hcl, hcv, hch, xr, d, trk, hxr, -, hent, hlast⟩ := rounds_core4 h hn hsh
  rw [hout]
  have hw : roundW 3 = 16 := rfl
  rw [hw] at hsz hch
  refine ⟨hcl, hcv, fun j hj => ?_, ?_, fun c hc => ?_⟩
  · rw [List.cons_append, List.getD_cons_succ, List.getD_append _ _ _ _ (by simpa using hj),
      List.getD_eq_getElem _ _ (by simpa using hj), List.getElem_map, List.getElem_range]
    exact ⟨lt_reg (by rw [hw]; omega), hch j hj⟩
  · rw [List.cons_append, List.getLastD_cons, List.getLastD_eq_getLast?, List.getLast?_append,
      List.getLast?_singleton]
    split_ifs with hk
    · simpa using hcl
    · simp only [Option.some_or, Option.getD_some, hw]; exact lt_reg (by omega)
  · simp only [List.cons_append, List.headD_cons] at hc
    rw [hcv] at hc
    rw [List.cons_append, List.getLastD_cons, List.getLastD_eq_getLast?, List.getLast?_append,
      List.getLast?_singleton]
    split_ifs with hk
    · subst hk; simp only [Option.some_or, Option.getD_some, Nat.min_zero]
      rw [hcv, hc]; rfl
    · simp only [Option.some_or, Option.getD_some]
      rw [hlast (by omega), rounds3_log inp _ _ (phStart4 n) _ (fun _ _ => c) L k 0 d _ trk xr hxr hent
        (Nat.zero_le _) hc, Nat.zero_add]

/-- **A degree-2 F rounds phase on the skeleton's registers** (L2, S2, E4): as `roundsF3_view4`,
with the claims `clR2`; and every real round's check `Chk2 P …` holds from the head's claim `c`. -/
theorem roundsF2_view4 {tr : Trace} {y : List Val × List Bool × Trace} (h : SkRun4 impl p inp tr y)
    {n : ℕ} (hn : n < (phasesOf seq4).length) {f k : ℕ}
    (hsh : (phasesOf seq4)[n].2 = .rounds f k 2 false) (L : Log) :
    ((skeleton4 seq4 p).2.outs.getD n []).headD 0 < (#[] ++ y.1.toArray).size ∧
      rd (#[] ++ y.1.toArray) (((skeleton4 seq4 p).2.outs.getD n []).headD 0) =
        clVal inp (initClaim (phasesOf seq4)[n].1) (fieldOffOf seq4 f + phaseOffOf seq4 n f)
          (#[] ++ y.1.toArray) (cAt4 seq4 p n).uni ∧
      (∀ j < k, ((skeleton4 seq4 p).2.outs.getD n []).getD (j + 1) 0 < (#[] ++ y.1.toArray).size ∧
        rd (#[] ++ y.1.toArray) (((skeleton4 seq4 p).2.outs.getD n []).getD (j + 1) 0) =
          .f (rch (phStart4 n) (fsOf tr (itemsOf seq4)) j)) ∧
      ((skeleton4 seq4 p).2.outs.getD n []).getLastD 0 < (#[] ++ y.1.toArray).size ∧
      ∀ c : F, rd (#[] ++ y.1.toArray) (((skeleton4 seq4 p).2.outs.getD n []).headD 0) = .f c →
        rd (#[] ++ y.1.toArray) (((skeleton4 seq4 p).2.outs.getD n []).getLastD 0) =
          .f (clR2 (phStart4 n) 16 readF (fun d => chF d 0) (fun _ _ => c) L (fsOf tr (itemsOf seq4))
            (min (realRounds p (phasesOf seq4)[n].1 k) k)) ∧
        ∀ l < min (realRounds p (phasesOf seq4)[n].1 k) k,
          Chk2 (phStart4 n) 16 readF (fun d => chF d 0) (fun _ _ => c) L (fsOf tr (itemsOf seq4)) l := by
  obtain ⟨b, hout, hsz, hcl, hcv, hch, xr, d, trk, hxr, hfl, hent, hlast⟩ := rounds_core4 h hn hsh
  rw [hout]
  have hw : roundW 2 = 13 := rfl
  rw [hw] at hsz hch
  refine ⟨hcl, hcv, fun j hj => ?_, ?_, fun c hc => ?_⟩
  · rw [List.cons_append, List.getD_cons_succ, List.getD_append _ _ _ _ (by simpa using hj),
      List.getD_eq_getElem _ _ (by simpa using hj), List.getElem_map, List.getElem_range]
    exact ⟨lt_reg (by rw [hw]; omega), hch j hj⟩
  · rw [List.cons_append, List.getLastD_cons, List.getLastD_eq_getLast?, List.getLast?_append,
      List.getLast?_singleton]
    split_ifs with hk
    · simpa using hcl
    · simp only [Option.some_or, Option.getD_some, hw]; exact lt_reg (by omega)
  · simp only [List.cons_append, List.headD_cons] at hc
    rw [hcv] at hc
    obtain ⟨h1, h2⟩ := rounds2_log inp _ _ (phStart4 n) _ (fun _ _ => c) L k 0 d _ trk xr hxr hent
      (Nat.zero_le _) hc
    refine ⟨?_, fun l hl => by
      simpa using h2 hfl l (by omega) (by simp only [Nat.zero_add]; omega)⟩
    rw [List.cons_append, List.getLastD_cons, List.getLastD_eq_getLast?, List.getLast?_append,
      List.getLast?_singleton]
    split_ifs with hk
    · subst hk; simp only [Option.some_or, Option.getD_some, Nat.min_zero]
      rw [hcv, hc]; rfl
    · simp only [Option.some_or, Option.getD_some]
      rw [hlast (by omega), h1, Nat.zero_add]

/-! ## Z2's univariate round -/

/-- **The univariate phase (Z2) on the skeleton's registers.** With `s = 0` for a node and `1` for a
segment, `outs[n] = [b + s + 3, b + s + 133, b + s + 134]`: register `b + s + 3` holds `λ`
(`fAt es (P + 1) 0`), `b + s + 133`/`b + s + 134` the two values of `lagrangeS` on the 127
coefficients (the log's message at `P`, `uniEs_log`) at `λ` with the target `targetS κ pe`. A node's
`pe` is the `pt` register's array; a segment's is the packed operand in register `b`, the
`segPtRegs` registers (`hpt`: when they precede the phase). -/
theorem uni_view4 {tr : Trace} {y : List Val × List Bool × Trace} (h : SkRun4 impl p inp tr y)
    {n : ℕ} (hn : n < (phasesOf seq4).length) {f : ℕ} (hsh : (phasesOf seq4)[n].2 = .uni f) :
    ∃ (b : ℕ) (pe : Array F),
      let s := if p.d.node then 0 else 1
      let es := fsOf tr (itemsOf seq4)
      let o := fieldOffOf seq4 f + phaseOffOf seq4 n f
      (skeleton4 seq4 p).2.outs.getD n [] = [b + s + 3, b + s + 133, b + s + 134] ∧
      b + s + 136 ≤ (#[] ++ y.1.toArray).size ∧
      rd (#[] ++ y.1.toArray) (b + s + 3) = .f (fAt es (phStart4 n + 1) 0) ∧
      rd (#[] ++ y.1.toArray) (b + s + 133) =
        .f (impl.lagrangeS (uniEs inp 0 o).toArray (fAt es (phStart4 n + 1) 0) (impl.targetS p.tix pe)).1 ∧
      rd (#[] ++ y.1.toArray) (b + s + 134) =
        .f (impl.lagrangeS (uniEs inp 0 o).toArray (fAt es (phStart4 n + 1) 0) (impl.targetS p.tix pe)).2 ∧
      (∀ i < 127, readF (Snd.msgAt es (phStart4 n)) (16 * i) = elemAt inp 0 (o + 16 * i)) ∧
      (p.d.node = true → pe = (rd (#[] ++ y.1.toArray) (cAt4 seq4 p n).pt).toAF) ∧
      (p.d.node = false → rd (#[] ++ y.1.toArray) b = .af pe ∧
        ((∀ x ∈ segPtRegs seq4 p (cAt4 seq4 p n).outs, x < (cAt4 seq4 p n).next) →
          pe = ((segPtRegs seq4 p (cAt4 seq4 p n).outs).map fun x => (rd (#[] ++ y.1.toArray) x).toF).toArray)) := by
  obtain ⟨trk, M, x, hx, hb, hwf, hext, -, hdrop, -⟩ := phase_at4 impl p.tix inp p h.ref hn
  have hok : CtxOk (cAt4 seq4 p n) (#[] ++ M.toArray) := by
    rcases hwf with ⟨h', -⟩ | h'
    · rw [hsh] at h'; cases h'
    · exact h'
  obtain ⟨seg, hseg, hsl, -⟩ := refPhase4_chain impl p.tix inp seq4 p hx (by simpa using hb)
    (by rw [hsh]; rfl) (q0 := 1) (by simp [hsh, isSeed4]) (.inr hok.1)
  have hout := skeleton4_outs seq4 p hn
  have hit : (phasesOf seq4)[n].2.itemsL seq4.lv = [.absorb uniBytes, .squeeze] := by rw [hsh]; rfl
  rw [List.drop_eq_getElem_cons hn, psItems4, List.flatMap_cons, hit] at hdrop
  rw [hit] at hsl
  obtain ⟨-, hent⟩ := seg_entries hdrop hseg hsl (by simp [Item.isFS]) (by simp)
  simp only [List.length_cons, List.length_nil] at hent
  generalize hph : (phasesOf seq4)[n] = ph at hx hsh hout
  obtain ⟨name, sh⟩ := ph
  simp only at hsh; subst hsh
  have hrM : ∀ z < M.length, rd (#[] ++ y.1.toArray) z = rd (#[] ++ M.toArray) z := fun z hz => by
    have hlt : z < (#[] ++ (M ++ x.1).toArray).size := by simp; omega
    rw [hext.2 _ hlt, show (#[] : Array Val) ++ (M ++ x.1).toArray = (#[] ++ M.toArray) ++ x.1.toArray
      by simp, rd_app_left (#[] ++ M.toArray) _ (by simpa using hz)]
  simp only [refPhase4] at hx
  rcases trk with _ | ⟨⟨q₁, a₁⟩, _ | ⟨⟨q₂, a₂⟩, trk⟩⟩
  · cases hx
  · cases hx
  simp only at hx
  split_ifs at hx with hq hnd <;> cases hx
  all_goals
    have e0 := hent 0 (by norm_num); have e1 := hent 1 (by norm_num)
    simp only [List.getD_cons_zero, List.getD_cons_succ, Nat.add_zero] at e0 e1
    have hlam : fAt (fsOf tr (itemsOf seq4)) (phStart4 n + 1) 0 = chF a₂ 0 := by
      rw [fAt, ansAt, entAt, ← e1]
    have hmsg : ∀ i < 127, readF (Snd.msgAt (fsOf tr (itemsOf seq4)) (phStart4 n)) (16 * i) =
        elemAt inp 0 (fieldOffOf seq4 f + phaseOffOf seq4 n f + 16 * i) := fun i hi => by
      rw [msgAt_of_q (p := phStart4 n) (by rw [← e0]; exact hq.1)]
      exact readF_piMsg inp _ _ (by simp only [uniBytes]; omega)
    have hsz := size_le_of_ext hext
    simp only [uniVals, List.length_append, List.length_cons, List.length_map, List.length_range,
      List.length_nil, uniEs] at hsz
  · -- a node
    refine ⟨M.length, (rd (#[] ++ M.toArray) (cAt4 seq4 p n).pt).toAF, ?_⟩
    dsimp only; rw [if_pos hnd]; simp only [Nat.add_zero]
    refine ⟨by rw [hout]; simp [genPhase4, hnd, hb], by omega, ?_, ?_, ?_, hmsg,
      fun _ => by rw [hrM _ (by simpa using hok.2.2.2.2)], fun h => by rw [hnd] at h; cases h⟩
    · rw [rd_phase4 hext (by simp [uniVals, uniEs]), hlam]; rfl
    · rw [rd_phase4 hext (by simp [uniVals, uniEs]), hlam]; rfl
    · rw [rd_phase4 hext (by simp [uniVals, uniEs]), hlam]; rfl
  · -- a segment
    refine ⟨M.length, ((segPtRegs seq4 p (cAt4 seq4 p n).outs).map fun z =>
      (rd (#[] ++ M.toArray) z).toF).toArray, ?_⟩
    dsimp only; rw [if_neg hnd]
    refine ⟨by rw [hout]; simp [genPhase4, hnd, hb], by omega, ?_, ?_, ?_, hmsg,
      fun h => absurd h hnd, fun _ => ⟨?_, fun hpt => ?_⟩⟩
    · rw [show M.length + 1 + 3 = M.length + 4 by ring, rd_phase4 hext (by simp [uniVals, uniEs]), hlam]; rfl
    · rw [show M.length + 1 + 133 = M.length + 134 by ring, rd_phase4 hext (by simp [uniVals, uniEs]),
        hlam]; rfl
    · rw [show M.length + 1 + 134 = M.length + 135 by ring, rd_phase4 hext (by simp [uniVals, uniEs]),
        hlam]; rfl
    · rw [show M.length = M.length + 0 from rfl, rd_phase4 hext (by simp)]; rfl
    · exact congrArg List.toArray (List.map_congr_left fun z hz => by
        rw [hrM z (by rw [← hb]; exact hpt z hz)])

/-! ## The front's rounds phases by name -/

/-- **The front's univariate and rounds phases of `seq4`** (index, name, shape), and the phase
numbers 3.x's `phaseIx` gives their names, which the finals read through `outsOf`. -/
theorem phases4_rounds (S : Seq) :
    (phasesOf S)[4]? = some ("Z2", Sh.uni fZ2) ∧ (phasesOf S)[5]? = some ("Z3", Sh.rounds fZ3 S.z3 3 false) ∧
    (phasesOf S)[8]? = some ("L2", Sh.rounds fL2 14 2 false) ∧
    (phasesOf S)[12]? = some ("S2", Sh.rounds fS2 S.s2 2 false) ∧
    (phasesOf S)[14]? = some ("Lr2", Sh.rounds fLr S.lr 3 false) ∧
    (phasesOf S)[18]? = some ("E2", Sh.rounds fE S.e2 3 false) ∧
    (phasesOf S)[21]? = some ("E4", Sh.rounds fE S.e4 2 false) :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

theorem phaseIx4_rounds : phaseIx "Z2" = 4 ∧ phaseIx "Z3" = 5 ∧ phaseIx "L2" = 8 ∧ phaseIx "S2" = 12 ∧
    phaseIx "Lr2" = 14 ∧ phaseIx "E2" = 18 ∧ phaseIx "E4" = 21 := by
  obtain ⟨-, h4, h5, -, h8, -, -, h12, -, h14, -, -, h18, -, h21, -, -⟩ := phaseIx_vals
  exact ⟨h4, h5, h8, h12, h14, h18, h21⟩

/-- The real round counts by name: the kind's (`Z3`, `S2`, `Lr2`, `E2`, `E4`); L2's are its 14. -/
theorem realRounds_vals (p : KindP) (k : ℕ) : realRounds p "Z3" k = p.d.seq.z3 ∧
    realRounds p "S2" k = p.d.seq.s2 ∧ realRounds p "Lr2" k = p.d.seq.lr ∧ realRounds p "E2" k = p.d.seq.e2 ∧
    realRounds p "E4" k = p.d.seq.e4 ∧ realRounds p "L2" k = k := ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- The rounds phases' first claims: Z3's is Z2's register, Lr2's and E2's are `0`, the rest free. -/
theorem initClaim_vals : initClaim "Z3" = .uni ∧ initClaim "Lr2" = .zero ∧ initClaim "E2" = .zero ∧
    initClaim "L2" = .free ∧ initClaim "S2" = .free ∧ initClaim "E4" = .free := ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- **The finals' names read the skeleton's phases** (`outsOf`, `claim0`, `claimN`, `chals`). -/
theorem outsOf_skel {fi : FinIn} (hfi : fi.outs = (skeleton4 seq4 p).2.outs) (name : String) :
    outsOf fi name = (skeleton4 seq4 p).2.outs.getD (phaseIx name) [] ∧
      claim0 fi name = ((skeleton4 seq4 p).2.outs.getD (phaseIx name) []).headD 0 ∧
      claimN fi name = ((skeleton4 seq4 p).2.outs.getD (phaseIx name) []).getLastD 0 :=
  ⟨by rw [outsOf, hfi], by rw [claim0, outsOf, hfi], by rw [claimN, outsOf, hfi]⟩

theorem chals_getD {fi : FinIn} (name : String) {k j : ℕ} (hj : j < k) :
    (chals fi name k).getD j 0 = (outsOf fi name).getD (j + 1) 0 := by
  rw [chals, List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, List.getElem?_take_of_lt hj,
    List.getElem?_drop, Nat.add_comm]

/-! ## Controls -/

/-- Control (+/−): a free claim sits at `b + 2`, a zero claim at `b`, Z3's at Z2's register. -/
theorem clReg_ctl : clReg .free 7 10 = 12 ∧ clReg .zero 7 10 = 10 ∧ clReg .uni 7 10 = 7 ∧
    clReg .uni 7 10 ≠ 12 := by decide

/-- Control (+/−): a zero claim is `0` whatever the registers; Z3's reads its register. -/
theorem clVal_ctl (inp : Input) (o u : ℕ) (r : Array Val) :
    clVal inp .zero o r u = .f 0 ∧ clVal inp .uni o r u = rd r u ∧
      clVal inp .free o r u = .f (elemAt inp 0 (o + 16) + elemAt inp 0 (o + 32)) := ⟨rfl, rfl, rfl⟩

/-- Control (−): no rounds, no claim change, and a run of `0` rounds needs no entries. -/
theorem roundsT_zero_ctl (inp : Input) (o deg real : ℕ) (d : Digest) (cv : Val) :
    roundsT inp 0 o deg false real 0 0 d cv [] = some ([], true, []) := rfl

end FR.Snd.R4
