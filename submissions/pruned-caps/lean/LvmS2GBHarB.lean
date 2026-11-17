-- New for lvm2 MP-B cap pruning (CAP-C5, 2026-11-17): Q_arith at S2GB (`harithB20H`, `harithS20H`'s twin): `P20B`'s
-- literals and positions, the stream lemmas on `StreamOkB` (the S2GB plan has heap entries, `StreamOk P20B` is false),
-- the position cells on `qlinkB`, the pair lemmas at blob B and `harithB20H`.
import LvmS2GBHar
import LvmS2GBGuardC
import LvmQCapSound
import LvmQCapFacts

/-!
# Q_arith at S2GB (`harithB20H`)

* `P20B`'s literals (`phasesB20`: S2GS's with the bus GKR at depth 13), **`posB20`**, **`frontPF_P20B`**,
  **`ivsB20`** (`contIvSB aSP`), **`contIvSB_ok`**.
* The stream on `StreamOkB` (**`stream_of_laneLinkB`**, **`traceBytesB_decodeB`**, **`streamed_childB`**) and the
  position cells on `qlinkB` (**`qlinkB_pos`**, **`posVal_onCB`**, **`posOk_ofGB`**, from the plan facts `posFB20`).
* The pair lemmas at S2GB and **`harithB20H`** (`harithS20H`'s proof with `qaSB`, `open_phaseB`, `core_of_phasesB`,
  `decideFSB_of` at `pTB`).
-/

set_option autoImplicit false

/-! ## `P20B`'s literals (proof help) -/

namespace Lvm

/-- `P20B` with its WHIR levels written out. -/
private def P20BL : Params := { P20B with mainLevels := P20UL.mainLevels }

/-- `P20B` is `P20BL`. -/
private theorem P20B_eqL : P20B = P20BL := by
  have h : P20B.mainLevels = P20BL.mainLevels := by
    show withRow0 P20.mainLevels 46 = _
    rw [Lvm.Replay.P20_eq]; rfl
  show P20B = { P20B with mainLevels := P20BL.mainLevels }
  rw [← h]

end Lvm

namespace Lvm.E2Q

open Lvm Lvm.Loop Lvm.Loop.Build Lvm.Har Lvm.QSig Lvm.QAsm Lvm.Typed Lvm.QTyped

/-! ## Positions at `P20B` -/

set_option maxRecDepth 100000 in
/-- The first items of `P20B`'s phases (proof help). -/
private theorem phaseItem0_P20B : phaseItem0 P20B .commit = 0 ∧ phaseItem0 P20B .bus = 25 ∧
    phaseItem0 P20B .tape = 372 ∧ phaseItem0 P20B .wire = 2538 ∧ phaseItem0 P20B .openMain = 2659 := by
  simp only [phaseItem0, phases_P20B_lit]; decide +kernel

/-- The phases' suffixes at `P20B` from one another (proof help). -/
private theorem drop_chainB (l : List Nat) :
    l.drop 2659 = ((l.drop 372).drop 2166).drop 121 ∧ l.drop 2538 = (l.drop 372).drop 2166 := by
  constructor <;> simp only [List.drop_drop]

set_option maxRecDepth 200000 in
/-- **`P20B`'s positions** (`posS20`'s twin on the S2GB stream: the `L0` cap sends `2^capSendBits` nodes). -/
theorem posB20 : startByte P20B + nodeBytes * 2 ^ P20B.capSendBits 0 (P20B.level ⟨.main, 0⟩).cap = posOf P20B 1 ∧
    posOf P20B 1 + 40 = 8 * phaseLane P20B .commit 1 ∧
    phaseLane P20B .commit (P20B.nuMain + 1) = phaseLane P20B .commit 1 + 9 * P20B.nuMain ∧
    posOf P20B 1 + 72 * P20B.nuMain + 24 = typedPosF P20B ∧ busLanesB P20B = true ∧
    ((∀ i < 20, 8 * phaseLane P20B .tape (2 + 2 * i) = posOf P20B (phaseItem0 P20B .tape) + 120 + 80 * i) ∧
      8 * phaseLane P20B .tape 41 = posOf P20B (phaseItem0 P20B .tape) + 1712 ∧
      8 * phaseLane P20B .tape 43 = posOf P20B (phaseItem0 P20B .tape) + 2520 ∧
      8 * phaseLane P20B .tape 45 = posOf P20B (phaseItem0 P20B .tape) + 2600 ∧
      posOf P20B (phaseItem0 P20B .wire) = 8 * Lvm.Q1.tapeEnd2 15 (phaseLane P20B .tape 45) - 40 ∧
      8 * phaseLane P20B .wire 0 = posOf P20B (phaseItem0 P20B .wire) + 40 ∧
      posOf P20B (phaseItem0 P20B .openMain) = posOf P20B (phaseItem0 P20B .wire) + 8216 ∧
      posOf P20B (phaseItem0 P20B .tape) % 8 = 0) := by
  simp only [posOf_drop, phaseLane_drop, typedPosF, busLanesB, busL_drop, phaseItem0_P20B.1, phaseItem0_P20B.2.1,
    phaseItem0_P20B.2.2.1, phaseItem0_P20B.2.2.2.1, phaseItem0_P20B.2.2.2.2]
  rw [itemLanes, schedule_P20B_litA, P20B_eqL, (drop_chainB _).1, (drop_chainB _).2, itemLanesAux_eq_R]
  simp only [← dropLN_eq, ← getDLN_eq, iZR, iWR, iRR, getDLN_add]
  decide +kernel

theorem hbB : Lvm.Har.pos (RS.startH (headerBytesP P20B)) +
    nodeBytes * 2 ^ P20B.capSendBits 0 (P20B.level ⟨.main, 0⟩).cap = posOf P20B 1 := by
  rw [pos_startH]; exact posB20.1

theorem pinHPB : posOf P20B 1 + 40 = 8 * phaseLane P20B .commit 1 := posB20.2.1

theorem pinQaB : phaseLane P20B .commit (P20B.nuMain + 1) = phaseLane P20B .commit 1 + 9 * P20B.nuMain :=
  posB20.2.2.1

theorem pinEndB : posOf P20B 1 + 72 * P20B.nuMain + 24 = typedPosF P20B := posB20.2.2.2.1

theorem busLanesB_P20B : busLanesB P20B = true := posB20.2.2.2.2.1

/-- **`P20B`'s front facts** (`frontPF_P20S`'s twin). -/
theorem frontPF_P20B : FrontPF P20B :=
  ⟨rfl, rfl, rfl, rfl, rfl, by rw [sizes_P20B.1.2.2.2.2.1]; norm_num, posB20.2.2.2.2.2⟩

/-- **The wire's `cont` intervals at S2GB are V_S's** (`contIvSB aSP`). -/
theorem ivsB20 : (1, spongeBlocks P20B - 1) :: (ksKs P20B).map (fun K => (K + 1, K + 31)) =
    Lvm.E2S.contIvSB Lvm.E2S.aSP := by
  rw [sizes_P20B.1.2.2.2.2.1]
  simp only [ksKs, frontPF_P20B.ksSplit_eq, nStepRowsC_eq, show P20B.leafOut = true from rfl, if_true]
  rfl

end Lvm.E2Q

namespace Lvm.E2S

open Lvm Lvm.E2U

/-- `contIvSB aSP`'s row facts (`contIvS_ok`'s twin with the trace's rows `1 … bB`). -/
theorem contIvSB_ok : contL (contIvSB aSP) 0 = false ∧ (∀ i, 0 < i → i ≤ bB → contL (contIvSB aSP) i = true) ∧
    (∀ r, r < 449 → ¬ (400 ≤ r ∧ r ≤ 430) → contL (contIvSB aSP) (ksSplit P20 + r) = false) ∧
    (∀ r, 400 ≤ r → r ≤ 430 → contL (contIvSB aSP) (ksSplit P20 + r) = true) ∧
    (∀ u, 0 < u → u < 32 → contL (contIvSB aSP) (aSP + u) = true) ∧ contL (contIvSB aSP) aSP = false ∧
    bB + 1 < aSP ∧ aSP + 32 ≤ ksSplit P20 := by
  have hk : ksSplit P20 = 7680 := ksSplit_P20
  rw [hk]
  refine ⟨by decide, fun i h1 h2 => ?_, fun r h1 h2 => ?_, fun r h1 h2 => ?_, fun u h1 h2 => ?_, by decide, by decide,
    by decide⟩
  all_goals
    unfold bB aSP at *
    simp only [contL, contIvSB, List.any_cons, List.any_nil, Bool.or_false, Bool.or_eq_true, Bool.or_eq_false_iff,
      decide_eq_true_eq, decide_eq_false_iff_not, bB]
    omega

end Lvm.E2S

/-! ## The stream on `StreamOkB` -/

namespace Lvm.QLink

open RecursionFast Lvm Lvm.Replay Lvm.Loop Lvm.Loop.Build

section
variable {p : Params} {ws : List Word}

theorem hashedLen_geB (hS : StreamOkB p) : 48 ≤ hashedLen p := by
  rw [hS.2]; simp [lens, plan, slenS]; omega

theorem take16B (hS : StreamOkB p) (hL : LaneLink p ws) :
    (wordsBytes ws).take 16 = enc64 lane0C ++ enc64 lane1C := by
  have h2 : 2 ≤ ws.length := by have := hL.size; have := hashedLen_geB hS; omega
  have e : ws.take 2 = [ws.getD 0 0, ws.getD 1 0] := by
    rcases ws with _ | ⟨a, _ | ⟨b, ws⟩⟩ <;> simp_all
  rw [show (16 : Nat) = 8 * 2 from rfl, wordsBytes_take, e, ← hL.c0, ← hL.c1]
  rfl

theorem byte0B (hS : StreamOkB p) (hL : LaneLink p ws) : (wordsBytes ws).head? = some tagTrace := by
  have h := congrArg List.head? (take16B hS hL)
  rw [first16, List.head?_take] at h
  simpa [tagTrace] using h

theorem wf0B (hS : StreamOkB p) (hL : LaneLink p ws) : ((wordsBytes ws).drop 1).take 8 = enc64 7 := by
  rw [drop_take_of_take (m := 16) (by omega), take16B hS hL, first16]; decide

/-- **The stream is the trace it encodes** (`stream_of_laneLink` on `StreamOkB`). -/
theorem stream_of_laneLinkB (hS : StreamOkB p) (hL : LaneLink p ws) :
    (wordsBytes ws).take (hashedLen p) = tagTrace :: traceBytes (decode p ws) := by
  have hlen : hashedLen p ≤ (wordsBytes ws).length := by rw [wordsBytes_length]; exact hL.size
  have hw : WfAt (wordsBytes ws) 1 (lens p) := by
    refine wfAt_of _ _ _ fun i hi => ?_
    rw [lens_length] at hi
    rw [lens_getD]
    by_cases h0 : i = 0
    · subst h0
      rw [plan_zero]
      simpa [slenS] using wf0B hS hL
    · have e := bOff_eqB hS.1 (i := i) (by omega) (by omega)
      simp only [bOff] at e
      rw [e, show (8 : Nat) = 8 * 1 from rfl, wordsBytes_slice]
      have hb := hL.len i (by omega) hi
      have hle : eLane p i < ws.length := by
        have := entry_end p hi; rw [← hS.2] at this
        have := hL.size; have := bOff_eqB hS.1 (i := i) (by omega) (by omega); omega
      rw [List.take_one, List.head?_drop, List.getElem?_eq_getElem hle, Option.toList_some]
      show wordBytes _ ++ [] = _
      rw [List.append_nil, wordBytes, ← hb, lw, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hle,
        Option.getD_some]
  have ht := take_readEntries (wordsBytes ws) (lens p) 1 hw (by rw [← hS.2]; exact hlen)
  rw [hS.2, List.take_add, List.take_one, byte0B hS hL, Option.toList_some, ht]
  rfl

theorem traceBytesB_decodeB (hS : StreamOkB p) (hL : LaneLink p ws) :
    traceBytesB (decode p ws) = sigma p ws := by
  apply ba_ext
  rw [sigma, bl_mk, stream_of_laneLinkB hS hL]
  exact traceBytesB_data _

theorem ansLane_boundB (hS : StreamOkB p) (hw : hashedLen p ≤ 8 * ws.length) {e : Nat} (he : e < (plan p).length) :
    ansLane p e + 4 ≤ ws.length := by
  by_cases h0 : e = 0
  · subst h0
    have := entry_end p (i := 0) he
    rw [← hS.2] at this
    simp only [ansLane, ite_true]
    have : bOff p 0 = 1 := rfl
    rw [plan_zero] at *; simp at *; omega
  · have h8 := streamOkB_len hS.1 (i := e) (by omega) he
    have hb := bOff_eqB hS.1 (i := e + 1) (by omega) (by omega)
    have := entry_end p he
    rw [← bOff_succ p he, ← hS.2] at this
    have := eLane_succB hS.1 (i := e) (by omega) he
    simp only [ansLane, h0, ite_false]
    omega

theorem ansLane_predB (hS : streamOkLB (plan p) = true) {i : Nat} (h2 : 2 ≤ i) (hi : i < (plan p).length) :
    ansLane p (i - 1) = eLane p i - 4 := by
  have := eLane_succB hS (i := i - 1) (by (clear * - h2; omega)) (by (clear * - h2 hi; omega))
  rw [show i - 1 + 1 = i by (clear * - h2; omega)] at this
  simp only [ansLane, show i - 1 ≠ 0 by (clear * - h2; omega), ite_false]
  (clear * - this; omega)

theorem aOf_lanesB (hS : StreamOkB p) (hw : hashedLen p ≤ 8 * ws.length) {i : Nat} (hi : i < (plan p).length) :
    (aOf (decode p ws) i).toList = wordsBytes ((ws.drop (ansLane p i)).take 4) := by
  have hB : bOff p i + 40 + ((plan p).getD i default).len ≤ (wordsBytes ws).length := by
    rw [wordsBytes_length]; have := entry_end p hi; rw [← hS.2] at this; (clear * - hw this; omega)
  rw [aOf_toList p ws hi hB, ← wordsBytes_slice]
  congr 2
  by_cases h0 : i = 0
  · subst h0
    simp only [ansLane, ite_true, bOff, List.take_zero, slenS, List.map_nil, List.sum_nil]
    rw [plan_zero]; rfl
  · have := bOff_eqB hS.1 (i := i) (by (clear * - h0; omega)) (by (clear * - hi; omega))
    have h8 := streamOkB_len hS.1 (i := i) (by (clear * - h0; omega)) hi
    simp only [ansLane, h0, ite_false]
    (clear * - this h8; omega)


theorem qOf_take32B (hS : StreamOkB p) (hw : hashedLen p ≤ 8 * ws.length) {i : Nat} (h1 : 1 ≤ i)
    (hi : i < (plan p).length) (h32 : 32 ≤ ((plan p).getD i default).len) :
    (bl (qOf (decode p ws) i)).take 32 = wordsBytes ((ws.drop (eLane p i + 1)).take 4) := by
  rw [bl_qOf p ws hi, List.take_take, Nat.min_eq_left h32, ← wordsBytes_slice, bOff_eqB hS.1 h1 (by (clear * - hi; omega))]
  congr 2


theorem qOf_drop32B (hS : StreamOkB p) (hw : hashedLen p ≤ 8 * ws.length) {i : Nat} (h1 : 1 ≤ i)
    (hi : i < (plan p).length) (h64 : ((plan p).getD i default).len = 64) :
    (bl (qOf (decode p ws) i)).drop 32 = wordsBytes ((ws.drop (eLane p i + 5)).take 4) := by
  have hB : bOff p i + 40 + ((plan p).getD i default).len ≤ (wordsBytes ws).length := by
    rw [wordsBytes_length]; have := entry_end p hi; rw [← hS.2] at this; (clear * - hw h64 this; omega)
  rw [bl_qOf p ws hi, h64, List.drop_take, ← wordsBytes_slice, List.drop_drop, bOff_eqB hS.1 h1 (by (clear * - hi; omega))]
  congr 2 <;> omega


theorem qOf_getB (hS : StreamOkB p) (hw : hashedLen p ≤ 8 * ws.length) {i : Nat} (h1 : 1 ≤ i)
    (hi : i < (plan p).length) {x : Nat} (hx : x < ((plan p).getD i default).len) :
    (qOf (decode p ws) i).get! x = (wordsBytes ws).getD (8 * eLane p i + 8 + x) 0 := by
  rw [get!_bl, bl_qOf p ws hi, List.getD_eq_getElem?_getD, List.getElem?_take, if_pos hx,
    List.getElem?_drop, ← List.getD_eq_getElem?_getD, bOff_eqB hS.1 h1 (by (clear * - hi; omega)), Nat.add_assoc]


theorem answerBits_lanesB (hS : StreamOkB p) (hw : hashedLen p ≤ 8 * ws.length) {e : Nat}
    (he : e < (plan p).length) :
    answerBits (aOf (decode p ws) e) =
      lw ws (ansLane p e) + 2 ^ 64 * lw ws (ansLane p e + 1) + 2 ^ 128 * lw ws (ansLane p e + 2) := by
  have hb := ansLane_boundB hS hw he
  have hlen : ((ws.drop (ansLane p e)).take 4).length = 4 := by simp; (clear * - hb; omega)
  have ha := aOf_lanesB hS hw he
  have u := fun k hk => u64At_digest hlen ha (k := k) hk
  simp only [answerBits]
  rw [show (0 : Nat) = 8 * 0 from rfl, u 0 (by (clear * -; first | decide | (simp only [Nat.add_comm, Nat.add_left_comm, Nat.add_assoc]; done) | ring1 | omega)), show (8 : Nat) = 8 * 1 from rfl, u 1 (by (clear * -; first | decide | (simp only [Nat.add_comm, Nat.add_left_comm, Nat.add_assoc]; done) | ring1 | omega)),
    show (16 : Nat) = 8 * 2 from rfl, u 2 (by (clear * -; first | decide | (simp only [Nat.add_comm, Nat.add_left_comm, Nat.add_assoc]; done) | ring1 | omega))]
  simp only [lw, lw_of_slice (by (clear * -; first | decide | (simp only [Nat.add_comm, Nat.add_left_comm, Nat.add_assoc]; done) | ring1 | omega) : 0 < 4) (by (clear * - hb; omega)), lw_of_slice (by (clear * -; first | decide | (simp only [Nat.add_comm, Nat.add_left_comm, Nat.add_assoc]; done) | ring1 | omega) : 1 < 4) (by (clear * - hb; omega)),
    lw_of_slice (by (clear * -; first | decide | (simp only [Nat.add_comm, Nat.add_left_comm, Nat.add_assoc]; done) | ring1 | omega) : 2 < 4) (by (clear * - hb; omega)), Nat.add_zero]


theorem testBit_answerBitsB (hS : StreamOkB p) (hw : hashedLen p ≤ 8 * ws.length) {e : Nat}
    (he : e < (plan p).length) {n : Nat} (hn : n < 192) :
    (answerBits (aOf (decode p ws) e)).testBit n = ansBit p ws e n := by
  rw [answerBits_lanesB hS hw he, testBit_three _ _ _ (lw_lt _ _) (lw_lt _ _), ansBit]
  split_ifs with h1 h2
  · rw [Nat.div_eq_of_lt h1, Nat.mod_eq_of_lt h1, Nat.add_zero]
  · rw [show n / 64 = 1 by (clear * - hn h1 h2; omega), show n % 64 = n - 64 by (clear * - hn h1 h2; omega)]
  · rw [show n / 64 = 2 by (clear * - hn h1 h2; omega), show n % 64 = n - 128 by (clear * - hn h1 h2; omega)]


theorem eLane_boundB (hS : StreamOkB p) (hL : LaneLink p ws) {i : Nat} (h1 : 1 ≤ i) (hi : i < (plan p).length) :
    8 * eLane p i + 40 + ((plan p).getD i default).len ≤ 8 * ws.length := by
  have := entry_end p hi; rw [← hS.2, bOff_eqB hS.1 h1 (by (clear * - hi; omega))] at this; have := hL.size; omega

/-- **CAP-FRZ C2** (RE-FREEZE R4(5); C5): **Q_link's S2GB lane conditions make the decoded trace a trace of the
schedule** (`linkOk_of_laneLink`'s twin on `StreamOkB`; the heap entries' `Good` from `LaneLinkB.bot`/`inner`/`cap`). -/
theorem linkOk_of_laneLinkB (hS : StreamOkB p) (hL : LaneLinkB p ws) : LinkOk p (decode p ws) := by
  refine ⟨decode_length p ws, fun i hi => ?_⟩
  rw [decode_length] at hi
  have hw := hL.base.size
  have hB : bOff p i + 40 + ((plan p).getD i default).len ≤ (wordsBytes ws).length := by
    rw [wordsBytes_length]; have := entry_end p hi; rw [← hS.2] at this; (clear * - hw this; omega)
  have hE := streamOkB_entry hS.1 hi
  refine ⟨qOf_size p ws hi hB, ?_⟩
  rcases he : (plan p).getD i default with ⟨k, len⟩
  rw [he] at hE
  cases k with
  | q0 =>
    simp only [entryOkB, entryOk, Bool.and_eq_true, beq_iff_eq] at hE
    obtain ⟨rfl, rfl⟩ := hE
    show qOf (decode p ws) 0 = q0Query
    apply ba_ext
    rw [bl_qOf p ws hi, plan_zero]
    show ((wordsBytes ws).drop 9).take 7 = q0Bytes
    rw [drop_take_of_take (m := 16) (by omega), take16B hS hL.base, first16]; decide
  | fs st =>
    simp only [entryOkB, entryOk, Bool.and_eq_true, decide_eq_true_eq] at hE
    obtain ⟨⟨h32, hst⟩, h1⟩ := hE
    show (bl (qOf (decode p ws) i)).take 32 = (aOf (decode p ws) st).toList
    rw [qOf_take32B hS hw h1 hi (by rw [he]; exact h32), aOf_lanesB hS hw (by (clear * - hi hst; omega))]
    congr 1
    have := eLane_boundB hS hL.base h1 hi; rw [he] at this
    exact slice_eq (by (clear * - this; omega)) (ansLane_boundB hS hw (by (clear * - hi hst; omega)))
      (hL.base.fs i hi st (by rw [he]))
  | leaf => trivial
  | heap pe h t path i0 m k cap =>
    simp only [entryOkB, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at hE
    obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨h64, hi0⟩, ht1⟩, hp1⟩, hpm⟩, h24⟩, hpe1⟩, hpet⟩, hk1⟩, hkm⟩, hix⟩, hcap⟩ := hE
    subst h64
    rcases m with _ | m
    · simp at hkm; (clear * - hk1 hkm; omega)
    have hpow : 2 ^ (m + 1) = 2 * 2 ^ m := by rw [Nat.pow_succ]; (clear * -; omega)
    simp only [Nat.add_sub_cancel] 
    have h1 : 1 ≤ i := by (clear * - hix hi0; omega)
    have hb8 := eLane_boundB hS hL.base h1 hi; rw [he] at hb8; simp only at hb8
    refine ⟨?_, ?_⟩
    · split_ifs with hkb
      · intro b hb j hj hpos
        have hjt : (j + 1) * (1 + path) ≤ t * (1 + path) := Nat.mul_le_mul_right _ (by (clear * - hj; omega))
        have hjs : (j + 1) * (1 + path) = j * (1 + path) + (1 + path) := Nat.succ_mul j (1 + path)
        have hej : i0 + j * (1 + path) + path < (plan p).length := by (clear * - hix hjt hjs hi; omega)
        have hj8 : j % 8 * h ≤ 7 * h := Nat.mul_le_mul_right h (by (clear * -; omega))
        have hjd : j / 8 ≤ (t - 1) / 8 := Nat.div_le_div_right (by (clear * - hj; omega))
        have hidx : posVal (decode p ws) pe h j >>> path = posL p ws (pe + j / 8) (j % 8 * h + path) (h - path) := by
          rw [posVal_shift _ _ _ _ _ (by (clear * - hpm; omega))]
          symm
          apply posL_eq
          intro n hn1 hn2
          exact (testBit_answerBitsB hS hw (e := pe + j / 8) (by (clear * - hjd hpet hix hi; omega)) (by (clear * - hn2 hj8 h24 hpm; omega))).symm
        rw [hidx] at hpos
        have hl := hL.bot i hi pe h t path i0 (m + 1) k cap (by rw [he]) (by simpa using hkb) b hb j hj hpos
        rw [aOf_lanesB hS hw hej]
        rcases b with _ | _ | b
        · rw [if_pos rfl, qOf_take32B hS hw h1 hi (by rw [he]; simp)]
          congr 1
          exact slice_eq (by (clear * - hb8; omega)) (ansLane_boundB hS hw hej) (fun l hl' => by simpa using hl l hl')
        · rw [if_neg (by decide), qOf_drop32B hS hw h1 hi (by rw [he])]
          congr 1
          exact slice_eq (by (clear * - hb8; omega)) (ansLane_boundB hS hw hej)
            (fun l hl' => by have := hl l hl'; rw [show eLane p i + 1 + 4 * 1 + l = eLane p i + 5 + l by (clear * -; omega)] at this; exact this)
        · (clear * - hb; omega)
      · have hkb' : k < 2 ^ m := by simpa using hkb
        have hea : i0 + t * (1 + path) + (2 ^ (m + 1) - 1 - 2 * k) < (plan p).length := by (clear * - hix hk1 hkb' hpow hi; omega)
        have heb : i0 + t * (1 + path) + (2 ^ (m + 1) - 1 - (2 * k + 1)) < (plan p).length := by (clear * - hix hk1 hkb' hpow hi; omega)
        have hl := hL.inner i hi pe h t path i0 (m + 1) k cap (by rw [he]) (by simpa using hkb)
        refine ⟨?_, ?_⟩
        · rw [qOf_take32B hS hw h1 hi (by rw [he]; simp), aOf_lanesB hS hw hea]
          congr 1
          exact slice_eq (by (clear * - hb8; omega)) (ansLane_boundB hS hw hea) (fun l hl' => (hl l hl').1)
        · rw [qOf_drop32B hS hw h1 hi (by rw [he]), aOf_lanesB hS hw heb]
          congr 1
          exact slice_eq (by (clear * - hb8; omega)) (ansLane_boundB hS hw heb) (fun l hl' => (hl l hl').2)
    · rcases cap with _ | ⟨ce, co, c⟩
      · trivial
      · simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at hcap
        obtain ⟨⟨⟨⟨⟨⟨hco8, hco32⟩, hck⟩, hkc⟩, hcob⟩, hce1⟩, hcei⟩ := hcap
        show aOf (decode p ws) i =
          Vector.ofFn fun x => (qOf (decode p ws) ce).get! (co + nodeBytes * (k - 2 ^ c) + x.val)
        have hpc : 2 ^ (c + 1) = 2 * 2 ^ c := by rw [Nat.pow_succ]; (clear * -; omega)
        have hcb := eLane_boundB hS hL.base (i := ce) hce1 (by (clear * - hcei hix hi; omega))
        have hlt : nodeBytes * (k - 2 ^ c) + 32 ≤ 32 * 2 ^ c := by simp only [nodeBytes]; (clear * - hck hkc hpc; omega)
        apply digest_ext
        rw [aOf_lanesB hS hw hi, Vector.toList_ofFn]
        have hq : (List.ofFn fun x : Fin 32 => (qOf (decode p ws) ce).get! (co + nodeBytes * (k - 2 ^ c) + x.val)) =
            wordsBytes ((ws.drop (eLane p ce + 1 + co / 8 + 4 * (k - 2 ^ c))).take 4) := by
          rw [← wordsBytes_slice]
          refine List.ext_getElem (by simp [wordsBytes_length]; simp only [nodeBytes] at hlt; (clear * - hco8 hcob hlt hcb hck hkc hpc; omega)) fun x hx1 hx2 => ?_
          simp only [List.length_ofFn] at hx1
          have hxb : co + nodeBytes * (k - 2 ^ c) + x < ((plan p).getD ce default).len := by
            simp only [nodeBytes] at hlt ⊢; (clear * - hcob hlt hx1; omega)
          rw [List.getElem_ofFn, qOf_getB hS hw hce1 (by (clear * - hcei hix hi; omega)) hxb, List.getElem_take, List.getElem_drop,
            List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by rw [wordsBytes_length]; simp [nodeBytes] at hlt; (clear * - hco8 hcb hxb; omega)),
            Option.getD_some]
          congr 1; simp only [nodeBytes]; (clear * - hco8; omega)
        rw [hq]
        congr 1
        exact slice_eq (by have := ansLane_boundB hS hw (e := i) hi; (clear * - this; omega))
          (by simp [nodeBytes] at hlt; (clear * - hco8 hcob hlt hcb; omega)) (hL.cap i hi pe h t path i0 (m + 1) k ce co c (by rw [he]))
  | node pe h j lvl cap =>
    simp only [entryOkB, entryOk, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at hE
    obtain ⟨⟨⟨⟨⟨⟨h64, h2⟩, hlvl⟩, h192⟩, hpe⟩, hpe1⟩, hcap⟩ := hE
    subst h64
    have hb8 := eLane_boundB hS hL.base (i := i) (by (clear * - h2; omega)) hi; rw [he] at hb8; simp only at hb8
    have hprev := ansLane_predB hS.1 h2 hi
    have hpb := ansLane_boundB hS hw (e := i - 1) (by (clear * - hi h2; omega))
    refine ⟨?_, ?_⟩
    · show (if (posVal (decode p ws) pe h j >>> lvl) % 2 = 0 then (bl (qOf (decode p ws) i)).take 32
        else (bl (qOf (decode p ws) i)).drop 32) = (aOf (decode p ws) (i - 1)).toList
      have hbit := posVal_bit (decode p ws) pe h j lvl hlvl
      rw [testBit_answerBitsB hS hw (by (clear * - hi hpe; omega)) (by (clear * - h192 hlvl; omega))] at hbit
      have hn := hL.base.node i hi pe h j lvl cap (by rw [he])
      rw [aOf_lanesB hS hw (by (clear * - hi h2; omega)), hprev]
      by_cases hab : ansBit p ws (pe + j / 8) (j % 8 * h + lvl)
      · rw [if_neg (by rw [hbit, hab]; decide), qOf_drop32B hS hw (by (clear * - h2; omega)) hi (by rw [he])]
        congr 1
        simp only [hab, ite_true] at hn
        exact slice_eq (by (clear * - hb8; omega)) (by (clear * - hprev hpb; omega)) hn
      · rw [if_pos (by rw [hbit]; simpa using hab), qOf_take32B hS hw (by (clear * - h2; omega)) hi (by rw [he]; simp)]
        congr 1
        simp only [hab, Bool.false_eq_true, ite_false] at hn
        exact slice_eq (by (clear * - hb8; omega)) (by (clear * - hprev hpb; omega)) hn
    · rcases cap with _ | ⟨ce, co, path⟩
      · trivial
      · simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at hcap
        obtain ⟨⟨⟨⟨⟨hco8, hph⟩, hco32⟩, hcob⟩, hce1⟩, hcei⟩ := hcap
        show aOf (decode p ws) i =
          Vector.ofFn fun x => (qOf (decode p ws) ce).get! (co + nodeBytes * (posVal (decode p ws) pe h j >>> path) + x.val)
        -- the index
        have hidx : posVal (decode p ws) pe h j >>> path = posL p ws (pe + j / 8) (j % 8 * h + path) (h - path) := by
          rw [posVal_shift _ _ _ _ _ hph]
          symm
          apply posL_eq
          intro n h1 h2
          exact (testBit_answerBitsB hS hw (e := pe + j / 8) (by (clear * - hi hpe; omega)) (by (clear * - h192 hph h2; omega))).symm
        have hidxlt : posL p ws (pe + j / 8) (j % 8 * h + path) (h - path) < 2 ^ (h - path) := by
          rw [← hidx]; exact shiftRight_lt_pow (posVal_lt _ _ _ _) hph
        have hcb := eLane_boundB hS hL.base (i := ce) hce1 (by (clear * - hi hcei; omega))
        have hlt : nodeBytes * posL p ws (pe + j / 8) (j % 8 * h + path) (h - path) + 32 ≤ 32 * 2 ^ (h - path) := by
          simp only [nodeBytes]
          have := Nat.mul_le_mul_left 32 (show posL p ws (pe + j / 8) (j % 8 * h + path) (h - path) + 1 ≤ 2 ^ (h - path) by (clear * - hidxlt; omega))
          (clear * - this; omega)
        apply digest_ext
        rw [aOf_lanesB hS hw hi, Vector.toList_ofFn, hidx]
        have hq : (List.ofFn fun x : Fin 32 => (qOf (decode p ws) ce).get!
            (co + nodeBytes * posL p ws (pe + j / 8) (j % 8 * h + path) (h - path) + x.val)) =
            wordsBytes ((ws.drop (eLane p ce + 1 + co / 8 + 4 * posL p ws (pe + j / 8) (j % 8 * h + path) (h - path))).take 4) := by
          rw [← wordsBytes_slice]
          refine List.ext_getElem (by simp [wordsBytes_length]; (clear * - hcob hco8 hidxlt hcb; omega)) fun x h1 h2 => ?_
          simp only [List.length_ofFn] at h1
          have hxb : co + nodeBytes * posL p ws (pe + j / 8) (j % 8 * h + path) (h - path) + x <
              ((plan p).getD ce default).len := by simp only [nodeBytes] at hlt ⊢; (clear * - hcob hco8 hidxlt h1; omega)
          rw [List.getElem_ofFn, qOf_getB hS hw hce1 (by (clear * - hi hcei; omega)) hxb, List.getElem_take, List.getElem_drop,
            List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by rw [wordsBytes_length]; simp [nodeBytes] at hlt; (clear * - hco8 hcb hxb; omega)),
            Option.getD_some]
          congr 1; simp only [nodeBytes]; (clear * - hco8; omega)
        rw [hq]
        congr 1
        refine slice_eq (by have := ansLane_boundB hS hw (e := i) hi; (clear * - this; omega)) (by simp [nodeBytes] at hlt; (clear * - hcob hco8 hidxlt hcb; omega)) ?_
        intro l hl
        have := hL.base.cap i hi pe h j lvl ce co path (by rw [he]) l hl
        simp only [ansLane, show i ≠ 0 by (clear * - h2; omega), ite_false, he]
        exact this

end

/-! ## The position cells at S2GB -/

section
variable {p : Params} {lay : Layout}

/-- An opening's positions answers at S2GB: their bits lie in three lanes, inside the plan (`open_pos_facts`). -/
theorem open_pos_factsB (hS : StreamOkB p) (hcp : p.capPrune = true)
    (hlv : (∀ lv < p.mainLevels.length, (p.mainLevels.getD lv default).level = lv) ∧
      ∀ lv < p.recLevels.length, (p.recLevels.getD lv default).level = lv)
    {o : OpenInfo} (ho : o ∈ opens p) (hp1 : 1 ≤ o.L.path) {j : Nat} (hj : j < o.L.t) :
    j % 8 * o.L.height + o.L.height ≤ 192 ∧ 1 ≤ o.pe + j / 8 ∧ o.pe + j / 8 < (plan p).length := by
  have hal := opens_alB' hcp hlv ho hp1
  have hxN : j * (1 + o.L.path) + 1 < (openPlanN o.L o.pe).length := by
    rw [openPlanN_length]; nlinarith
  have hx : j * (1 + o.L.path) + 1 < (openPlanB p o.L.level o).length := by
    rw [openPlanB_length]; rw [openPlanN_length] at hxN; omega
  have hi := hal.2 _ hx
  rw [openPlanB, List.getD_append _ _ _ _ hxN, openPlanN_getD _ _ hj (by omega), if_neg (by omega)] at hi
  have hilt : o.i0 + (j * (1 + o.L.path) + 1) < (plan p).length := by have := hal.1; omega
  have he := streamOkB_entry hS.1 hilt
  rw [hi] at he
  simp only [entryOkB, entryOk, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at he
  obtain ⟨⟨⟨⟨⟨⟨-, -⟩, -⟩, h192⟩, hlt⟩, h1⟩, -⟩ := he
  exact ⟨h192, h1, by omega⟩

theorem posIdx_ltB (hpos : ((opens p).map fun o => o.L.t).sum ≤ 2 ^ lay.pa) {k j : Nat} (hk : k < (opens p).length)
    (hj : j < ((opens p).getD k default).L.t) : posIdx p k j < 2 ^ lay.pa := by
  have := sum_take_add_lt ((opens p).map fun o => o.L.t) (k := k) (by simpa using hk)
  rw [← List.map_take] at this
  simp only [List.getElem_map] at this
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hk, Option.getD_some] at hj
  simp only [posIdx]; omega

/-- **The position cells at S2GB** (`qlink_pos` for `qlinkB`). -/
theorem qlinkB_pos {c : Ctx} {M : Mem} (hpos : ((opens p).map fun o => o.L.t).sum ≤ 2 ^ lay.pa)
    {pt : Ptr} (h : SegsHold c M pt (qlinkB p lay pt).2) {k j : Nat}
    (hk : k < (opens p).length) (hj : j < ((opens p).getD k default).L.t) :
    M.k (pt.k + posIdx p k j) = M.k (lay.fl + posIdx p k j) + M.k (lay.fl + 2 ^ lay.pa + posIdx p k j) := by
  simp only [qlinkB] at h
  rw [hold_bind] at h
  exact posLoop_spec h.1 _ (posIdx_ltB hpos hk hj)

end

end Lvm.QLink

/-! ## The position cells' values and `PosOkB` on `StreamOkB` -/

namespace Lvm.NS

open RecursionFast Lvm Lvm.T Lvm.ASM Lvm.Replay Lvm.Loop Lvm.Loop.Build Lvm.QLink Lvm.QSig Lvm.M3
open Lvm.QAsm Lvm.QTyped Lvm.Typed Lvm.TypedV Lvm.BitsTab Lvm.Bits Lvm.SigBits Lvm.Har LeanVM.Protocol

/-- `posVal_on` on `StreamOkB` (the S2GB plan; `QOk`'s path facts and stream bound as hypotheses). -/
theorem posVal_onB {v : ℕ → FK} (C : QCfg)
    (hout : ∀ {k l x : ℕ} {o : OpenInfo}, k < (opens C.p).length → (opens C.p).getD k default = o →
      l < QAsm.nLanes o.L.height → x < nRows o → ∀ {e : BOut × ℕ × ℕ}, e ∈ laneOuts o.L.height l →
      e.1.Valid → Out1 v (ansLane C.p (o.pe + x) + l) e.1 (posCell C k o x e))
    (hS : StreamOkB C.p) (hcp : C.p.capPrune = true)
    (hlv : (∀ lv < C.p.mainLevels.length, (C.p.mainLevels.getD lv default).level = lv) ∧
      ∀ lv < C.p.recLevels.length, (C.p.recLevels.getD lv default).level = lv)
    (hpo : ∀ o ∈ opens C.p, 1 ≤ o.L.path ∧ o.L.path < o.L.height) (hT : hashedLen C.p / 8 + 17 ≤ 2 ^ (lay C).m)
    {ws : List Word}
    (hs : ∀ l < 2 ^ (lay C).m, v ((lay C).sb + l) = laneK ws l)
    {k : ℕ} (hk : k < (opens C.p).length) (hH : ((opens C.p).getD k default).L.height ≤ 64)
    {j : ℕ} (hj : j < ((opens C.p).getD k default).L.t) :
    v ((lay C).fl + posIdx C.p k j) + v ((lay C).fl + 2 ^ (lay C).pa + posIdx C.p k j) =
      kOf (posL C.p ws (((opens C.p).getD k default).pe + j / 8)
        (j % 8 * ((opens C.p).getD k default).L.height) ((opens C.p).getD k default).L.height) := by
  generalize hoD : (opens C.p).getD k default = o at hH hj ⊢
  have ho : o ∈ opens C.p := by
    rw [← hoD, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hk]; exact List.getElem_mem hk
  obtain ⟨hp1, hp2⟩ := hpo _ ho
  obtain ⟨h192, h1, hlt⟩ := open_pos_factsB hS hcp hlv ho hp1 hj
  have hin := lanes_inB hS h1 hlt
  have hx : j / 8 < nRows o := by
    have := lt_padT' hj; unfold nRows; (clear * - this; omega)
  have hj8 : j % 8 < 8 := Nat.mod_lt _ (by norm_num)
  have hji : 8 * (j / 8) + j % 8 = j := by (clear * -; omega)
  have hsH : j % 8 * o.L.height ≤ 7 * o.L.height := Nat.mul_le_mul_right _ (by (clear * -; omega))
  -- the two field entries, their lanes and validity
  have hl1 : (fields o.L.height (j % 8)).1.1 < QAsm.nLanes o.L.height := by
    simp only [fields, QAsm.nLanes]; (clear * - h192 hp1 hp2 hsH; omega)
  have hl2 : (fields o.L.height (j % 8)).2.1 < QAsm.nLanes o.L.height := by
    simp only [fields, QAsm.nLanes]; split_ifs with hc <;> (clear * - hc hH h192 hp1 hp2 hsH hj8; omega)
  have hv1 : (BOut.fld (fields o.L.height (j % 8)).1.2.1 (fields o.L.height (j % 8)).1.2.2.1
      (fields o.L.height (j % 8)).1.2.2.2).Valid := by
    show _ < 64 ∧ _ ∧ _
    simp only [fields]; split_ifs with hc <;> (clear * - hc hH h192 hp1 hp2 hsH hj8; omega)
  have hv2 : (BOut.fld (fields o.L.height (j % 8)).2.2.1 (fields o.L.height (j % 8)).2.2.2.1
      (fields o.L.height (j % 8)).2.2.2.2).Valid := by
    show _ < 64 ∧ _ ∧ _
    simp only [fields]; split_ifs with hc <;> (clear * - hc hH h192 hp1 hp2 hsH hj8; omega)
  have o1 := hout hk hoD hl1 hx (Lvm.Fin.lo_mem o.L.height hj8) hv1
  have o2 := hout hk hoD hl2 hx (Lvm.Fin.hi_mem o.L.height hj8) hv2
  have c1 : posCell C k o (j / 8) ((BOut.fld (fields o.L.height (j % 8)).1.2.1
      (fields o.L.height (j % 8)).1.2.2.1 (fields o.L.height (j % 8)).1.2.2.2), 1, j % 8) =
      (lay C).fl + posIdx C.p k j := by
    simp only [posCell, hji, if_pos hj, ↓reduceIte, Nat.add_zero]; rfl
  have c2 : posCell C k o (j / 8) ((BOut.fld (fields o.L.height (j % 8)).2.2.1
      (fields o.L.height (j % 8)).2.2.2.1 (fields o.L.height (j % 8)).2.2.2.2), 2, j % 8) =
      (lay C).fl + 2 ^ (lay C).pa + posIdx C.p k j := by
    simp only [posCell, hji, if_pos hj]; rfl
  have hlane : ∀ l ≤ 2, ansLane C.p (o.pe + j / 8) + l < 2 ^ (lay C).m := by
    intro l hl
    simp only [ansLane, if_neg (show o.pe + j / 8 ≠ 0 by (clear * - h1; omega))]; (clear * - hin hT hl; omega)
  have hl1' : (fields o.L.height (j % 8)).1.1 ≤ 2 := by
    simp only [fields]; (clear * - h192 hsH; omega)
  have hl2' : (fields o.L.height (j % 8)).2.1 ≤ 2 := by
    simp only [fields]; split_ifs with hc <;> (clear * - hc hH h192 hp1 hp2 hsH hj8; omega)
  have hs' : ∀ l < 2 ^ (lay C).m, v l = laneK ws l := fun l hl => by
    have := hs l hl; rwa [show (lay C).sb = 0 from rfl, Nat.zero_add] at this
  unfold Out1 at o1 o2
  rw [← c1, ← c2, o1, o2, hs' _ (hlane _ hl1'), hs' _ (hlane _ hl2')]
  exact Lvm.Fin.fields_posL C.p ws (o.pe + j / 8) (by (clear * - hH hp1 hp2; omega)) hH h192

end Lvm.NS

namespace Lvm.Har

open RecursionFast Lvm Lvm.T Lvm.ASM Lvm.Replay Lvm.Loop Lvm.Loop.Build Lvm.QLink Lvm.QSig Lvm.QAsm Lvm.NS Lvm.Typed
open Lvm.QTyped Lvm.Bits Lvm.BitsTab Lvm.Har

/-- `posVal_onC` on `StreamOkB`. -/
theorem posVal_onCB {C : QCfg} {v : ℕ → FK} (hv : OutsOnC C v) (hS : StreamOkB C.p) (hcp : C.p.capPrune = true)
    (hlv : (∀ lv < C.p.mainLevels.length, (C.p.mainLevels.getD lv default).level = lv) ∧
      ∀ lv < C.p.recLevels.length, (C.p.recLevels.getD lv default).level = lv)
    (hpo : ∀ o ∈ opens C.p, 1 ≤ o.L.path ∧ o.L.path < o.L.height) (hT : hashedLen C.p / 8 + 17 ≤ 2 ^ (lay C).m)
    {ws : List Word} (hs : ∀ l < 2 ^ (lay C).m, v ((lay C).sb + l) = laneK ws l)
    {k : ℕ} (hk : k < (opens C.p).length) (hH : ((opens C.p).getD k default).L.height ≤ 64)
    {j : ℕ} (hj : j < ((opens C.p).getD k default).L.t) :
    v ((lay C).fl + posIdx C.p k j) + v ((lay C).fl + 2 ^ (lay C).pa + posIdx C.p k j) =
      kOf (posL C.p ws (((opens C.p).getD k default).pe + j / 8)
        (j % 8 * ((opens C.p).getD k default).L.height) ((opens C.p).getD k default).L.height) :=
  posVal_onB C (Lvm.E2Q.out1_entryC hv) hS hcp hlv hpo hT hs hk hH hj

/-- **`PosOkB` from the position cells' values** (`posOk_ofG` on `StreamOkB`, the opening's lanes on the stream `cp`). -/
theorem posOk_ofGB (p : Params) (Cq : QCfg) (hp : Cq.p = p) (C : SCfg) (k0 : ℕ) (cp : Option Params)
    (hpb : ∀ i, C.pb i = posBase Cq (k0 + i)) {Ls : List Level} {V : ℕ}
    (hPL : Lvm.Fin.PosLanes p C.g C.ood Ls V k0 cp) {M : Mem} {ws : List Word} (hS : StreamOkB p) (hL : LaneLink p ws)
    (hcp : p.capPrune = true)
    (hlv : (∀ lv < p.mainLevels.length, (p.mainLevels.getD lv default).level = lv) ∧
      ∀ lv < p.recLevels.length, (p.recLevels.getD lv default).level = lv)
    (hp1 : ∀ o ∈ opens p, 1 ≤ o.L.path)
    (hcell : ∀ k < (opens p).length, ((opens p).getD k default).L.height ≤ 64 →
      ∀ j < ((opens p).getD k default).L.t, M.k (nK Cq + posIdx p k j) =
        kOf (posL p ws (((opens p).getD k default).pe + j / 8) (j % 8 * ((opens p).getD k default).L.height)
          ((opens p).getD k default).L.height)) :
    Lvm.Har.PosOkB C cp M (traceBytesB (decode p ws)) 0 Ls V := by
  intro i hi j hj
  obtain ⟨hk, hLeq, hH, hP⟩ := hPL i hi
  rw [traceBytesB_decodeB hS hL, hpb, Nat.zero_add]
  have hjt : j < ((opens p).getD (k0 + i) default).L.t := by rw [hLeq]; exact hj
  have ho : (opens p).getD (k0 + i) default ∈ opens p := by
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hk, Option.getD_some]; exact List.getElem_mem hk
  obtain ⟨h192, h1, hlt⟩ := open_pos_factsB hS hcp hlv ho (hp1 _ ho) hjt
  have hin := lanes_inB hS h1 hlt
  have hab := ansLane_boundB hS hL.size hlt
  have e1 : posBase Cq (k0 + i) + j = nK Cq + posIdx p (k0 + i) j := by
    simp only [posBase, posIdx, hp]; (clear * -; first | decide | (simp only [Nat.add_comm, Nat.add_left_comm, Nat.add_assoc]; done) | ring1 | omega)
  rw [e1, hcell _ hk (by rw [hLeq]; exact hH) j hjt]
  have hx : j / 8 < nAns ((opens p).getD (k0 + i) default) := by unfold nAns; (clear * - hjt e1; omega)
  have hb : j % 8 * (Ls.getD i default).height + (Ls.getD i default).height ≤ 192 := by rw [← hLeq]; exact h192
  have hlen : 8 * ansLane p (((opens p).getD (k0 + i) default).pe + j / 8) + 24 ≤ hashedLen p := by
    simp only [ansLane, if_neg (show ((opens p).getD (k0 + i) default).pe + j / 8 ≠ 0 by (clear * - h1; omega))]
    (clear * - hin; omega)
  rw [Lvm.Har.qsAt_posL p ws _ _ _ j hj (hP _ hx) hb hlen (by (clear * - hab; omega)), hLeq]
  rfl

/-- **`Σ'` is the stream cells' bytes at S2GB** (`streamed_child` on `StreamOkB`). -/
theorem streamed_childB (C : QCfg) {M : Mem} {ws : List Word} (hS : StreamOkB C.p) (hL : LaneLink C.p ws)
    (hst : ∀ j < 2 ^ (lay C).m, M.k ((lay C).sb + j) = laneK ws j) {T : Nat} (hTm : T ≤ 2 ^ (lay C).m)
    (hT : 8 * T ≤ hashedLen C.p) (hl : T ≤ ws.length) :
    Lvm.Q1.Streamed M (traceBytesB (decode C.p ws)) T := by
  rw [traceBytesB_decodeB hS hL]
  exact streamed_sigma C.p ws (N := 2 ^ (lay C).m) (fun j hj => by simpa [lay] using hst j hj) hTm hT hl

end Lvm.Har

/-! ## `LayOkB` does not read the position or PoW cells -/

namespace Lvm.Har

theorem lvOkB_congr {C C' : SCfg} (cp : Option Params) (h1 : C.nu = C'.nu) (h2 : C.pch = C'.pch)
    (h3 : C.cch = C'.cch) (h4 : C.g = C'.g) (h5 : C.ood = C'.ood) (T : Nat) :
    ∀ (Ls : List Level) (i f V : Nat), lvOkB C cp T Ls i f V = lvOkB C' cp T Ls i f V
  | [], _, _, _ => rfl
  | [L], i, f, V => by rw [lvOkB, lvOkB, h1, h2, h3, h4, h5]
  | L :: N :: rest, i, f, V => by
    rw [lvOkB, lvOkB, h1, h2, h3, h4, h5, lvOkB_congr cp h1 h2 h3 h4 h5 T (N :: rest)]

end Lvm.Har

namespace Lvm.E2Q

open Lvm Lvm.QAsm

/-- `stackEndL` at `cfgMainF` on the stream `cp` (`stackEnd_cfgMainF`'s twin). -/
theorem stackEnd_cfgMainFB (p : Params) (pb pw : Nat → Nat) (cp : Option Params) :
    Lvm.Har.stackEndL (cfgMainF p pb pw).g (cfgMainF p pb pw).ood (cfgMainF p pb pw).levels
      ((cfgMainF p pb pw).U + 15) cp =
      Lvm.Har.stackEndL p.grind p.mainOod p.mainLevels (phaseLane p .openMain 0 - 5 + 15) cp := rfl

/-- `LayOkB` at `cfgMainF` does not read the position or PoW bases (`layOkF_pb`'s twin). -/
theorem layOkB_pbF (p : Params) (cp : Option Params) (pb pw pb' pw' : Nat → Nat) (T : Nat) :
    Lvm.Har.LayOkB (cfgMainF p pb pw) cp T = Lvm.Har.LayOkB (cfgMainF p pb' pw') cp T := by
  unfold Lvm.Har.LayOkB
  rw [Lvm.Har.lvOkB_congr (C := cfgMainF p pb pw) (C' := cfgMainF p pb' pw') cp rfl rfl rfl rfl rfl]
  rfl

end Lvm.E2Q

/-! ## The plan's facts at `P20B` -/

namespace Lvm.E2Q

open RecursionFast Lvm Lvm.QAsm Lvm.QLink Lvm.Replay

open Lvm.PlanChk in
/-- The cap entries at `P20B` and their lengths (the FS queries that absorb the caps; a probe evaluation of the plan). -/
def tblB20 : List (ℕ × ℕ) := [(2, 96), (981, 112), (2654, 112)]

open Lvm.PlanChk in
set_option maxRecDepth 200000 in
/-- **The plan's facts at `P20B`** in one kernel evaluation (the S2GB walk over `schedB20` at `P20BL`): the one pass
(`StreamOkB`), `PlanOkB` with the walk's last entry, and Q_link's `qOkCB` at `lay cfgB20`. -/
private theorem planFactsB :
    passRB (capLk tblB20) 4134 269328 575207 (plan P20B) tblB20 0 0 0 = true ∧
      (PlanOkB P20B ∧ (planAll P20B).2.i = 4134) ∧ qOkCB P20B (lay cfgB20) = true :=
  planFacts_ofB (fun L => passRB (capLk tblB20) 4134 269328 575207 L tblB20 0 0 0 = true) schedule_P20B_litA
    P20B_eqL sizes_P20B.1.2.2.1 rfl (by decide +kernel)

/-- **R2: the S2GB plan's stream facts.** -/
theorem streamOkB_P20B : StreamOkB P20B := streamOkB_ofR planFactsB.1 sizes_P20B.1.2.2.1

open Lvm.PlanChk in
/-- The one S2GB pass at `P20B` (`planFactsB`'s first part; the node lengths, `Σ clen`, the query caps). -/
theorem passRB_P20B : passRB (capLk tblB20) 4134 269328 575207 (plan P20B) tblB20 0 0 0 = true := planFactsB.1

/-- `PlanOkB P20B` (`planFactsB`'s second part; the S2GB replay's static conditions). -/
theorem planOkB_P20B : PlanOkB P20B := planFactsB.2.1.1

/-- **Q_link's static checks at S2GB** (`qlinkB_sound`'s `hQ`). -/
theorem hQB20 : QOkB P20B (lay cfgB20) := qOkB_of streamOkB_P20B planFactsB.2.2

theorem hlvB20 : (∀ lv < P20B.mainLevels.length, (P20B.mainLevels.getD lv default).level = lv) ∧
    ∀ lv < P20B.recLevels.length, (P20B.recLevels.getD lv default).level = lv := hQB20.lvIdx
theorem hpoB20 : ∀ o ∈ opens P20B, 1 ≤ o.L.path ∧ o.L.path < o.L.height :=
  fun o ho => ⟨(hQB20.opens o ho).1, (hQB20.opens o ho).2.1⟩
theorem hTB20 : hashedLen P20B / 8 + 17 ≤ 2 ^ (lay cfgB20).m := hQB20.hT
theorem hposB20 : ((opens P20B).map fun o => o.L.t).sum ≤ 2 ^ (lay cfgB20).pa := hQB20.pos

end Lvm.E2Q

/-! ## Q_arith at S2GB (`harithS20H`'s proof at `cfgB20`) -/

namespace Lvm.E2Q

open RecursionFast Lvm Lvm.T Lvm.ASM Lvm.Replay Lvm.Loop Lvm.Loop.Build Lvm.QLink Lvm.QSig Lvm.QAsm Lvm.NS
open Lvm.Typed Lvm.QTyped Lvm.Bits Lvm.BitsTab Lvm.Har LeanVM.Protocol
open Lvm.E2T (TNatT PhiQGC)
open Lvm.E2U (SBlkU YqU MqU)
open Lvm.E2S (VSSB decideFBX THypSB GoodTSB)

/-- Q_arith's pointer at S2GS (after Q_link and `qsigSC`; `LvmS2GSStmtC`'s `p2S20`). -/
def p2B20H : Ptr :=
  let p1 := (⟨nK cfgB20, 0⟩ : Ptr).adv (qlinkB cfgB20.p (lay cfgB20) ⟨nK cfgB20, 0⟩).2
  p1.adv (qsigSC (sigIn cfgB20) (sigInLC cfgB20) p1).2

/-- **Q_sig's first walk's bits after `qlinkB`** (`hbitsCS` at Q_sig's S2GB pointer `p1PB`; any configuration with
`capPrune`, where `p1C` is `p1PB`). -/
theorem hbitsCSB {C : QCfg} {v : ℕ → FK} (hv : OutsOnC C v) (hln : C.ln = 20) (hcp : C.p.capPrune = true) :
    SigBits (sigIn C) (qsigNoSl (sigIn C) (p1PB (lay C) (nK C) 0 C.p)).1 v := by
  have h := sigBits_ofC C hv ⟨by omega, by omega⟩
  rw [sigOut, p1C_of_pr C hcp] at h
  exact sigBits_noSl h

section PairSH

variable {x : List UInt8} {qm : Column CMain.nu20} {qr : Column 19}

/-- The trace bytes of the child at S2GS have `hashedLen P20B` bytes. -/
theorem sigB_size (hL : LaneLink P20B (wsC qr)) : (traceBytesB (decode P20B (wsC qr))).size = hashedLen P20B := by
  rw [traceBytesB_decodeB streamOkB_P20B hL, Lvm.Har.sigma_sizeT hL.size]

/-- **The node memory streams the child's trace at S2GS** (`streamed_child` at `cfgB20`). -/
theorem streamedB {M : Mem} (hst : ∀ j < 2 ^ (lay cfgB20).m, M.k ((lay cfgB20).sb + j) = laneK (wsC qr) j)
    (hL : LaneLink P20B (wsC qr)) : Lvm.Q1.Streamed M (traceBytesB (decode P20B (wsC qr))) (streamLanes P20B) := by
  have hh : hashedLen P20B = 575208 := sizes_P20B.1.2.2.1
  have hw : (wsC qr).length = 17 * 2 ^ 14 := by rw [wsC, wsOf, List.length_map, List.length_range]
  exact Lvm.Har.streamed_childB cfgB20 streamOkB_P20B hL hst (T := streamLanes P20B)
    (by rw [streamLanes, hh]; decide) (by rw [show cfgB20.p = P20B from rfl, streamLanes]; omega)
    (by rw [streamLanes, hh, hw]; norm_num)

theorem hWB (S : NodeGB) (H : THypSB TiB20) (hG : GoodTSB TiB20 H x qm qr) :
    WiringRelX QB20 layB20 (zTX (NTB20.toN.instL Pub.hdrLanesT QB20 layB20) Lvm.pubXTS x qm qr) :=
  (wiringRelT_iff QB20 layB20 S.st.hlay _).mp hG.1.1.1.1

/-- **The three row switches' words at S2GS** (the `rowAux` blocks of `specQU` on `tBu cfgB20 i`). -/
theorem rowWordsB (S : NodeGB) (H : THypSB TiB20) (hG : GoodTSB TiB20 H x qm qr) :
    (∀ j < 128, (memTX TiB20 Lvm.pubXTS x qm qr).k (tBu cfgB20 0 + j) =
      rowWordD (Lvm.Q2.slicesOf (memTX TiB20 Lvm.pubXTS x qm qr) (wlUG P20B).slicesD) j) ∧
    (∀ j < 128, (memTX TiB20 Lvm.pubXTS x qm qr).k (tBu cfgB20 1 + j) =
      rowWordD (Lvm.Q2.slicesOf (memTX TiB20 Lvm.pubXTS x qm qr) (wlUG P20B).slicesY) j) ∧
    (∀ j < 128, (memTX TiB20 Lvm.pubXTS x qm qr).k (tBu cfgB20 2 + j) =
      rowWordD (Lvm.Q2.slicesOf (memTX TiB20 Lvm.pubXTS x qm qr) (wlUG P20B).slicesM) j) := by
  obtain ⟨f, hf⟩ := Lvm.QTyped.aux_mkLayD QB20 (specQU cfgB20 QB20 powB20) dintsB20
  have hmem : ∀ B, B ∈ Lvm.Q2.rowAuxL (f (specQ cfgB20 QB20).auxWords.length) (tBu cfgB20 0) (wlUG P20B).slicesD ++
      Lvm.Q2.rowAuxL (f ((specQ cfgB20 QB20).auxWords.length + 1)) (tBu cfgB20 1) (wlUG P20B).slicesY ++
      Lvm.Q2.rowAuxL (f ((specQ cfgB20 QB20).auxWords.length + 2)) (tBu cfgB20 2) (wlUG P20B).slicesM →
      B ∈ layB20.aux := fun B hB => by
    show B ∈ (mkLayD QB20 (specQU cfgB20 QB20 powB20) dintsB20).1.aux
    rw [hf]
    show B ∈ (specQ cfgB20 QB20).auxOf f ++ _ ++ _
    exact List.mem_append_left _ (List.mem_append_right _ hB)
  have hone := zOf_one (NTB20.toN.instL Pub.hdrLanesT QB20 layB20) H.ok.2 Lvm.M3.lay26 (Lvm.pubXTS x) qm qr
  exact ⟨fun j hj => rowWords_of_aux S.st.hlay hone (hWB S H hG)
      (fun B hB => hmem B (List.mem_append_left _ (List.mem_append_left _ hB))) hj,
    fun j hj => rowWords_of_aux S.st.hlay hone (hWB S H hG)
      (fun B hB => hmem B (List.mem_append_left _ (List.mem_append_right _ hB))) hj,
    fun j hj => rowWords_of_aux S.st.hlay hone (hWB S H hG) (fun B hB => hmem B (List.mem_append_right _ hB)) hj⟩

/-- **V's proof-of-work checks at S2GS** (`powOk_of_blksU` at `cfgB20`). -/
theorem powOkB (S : NodeGB) (H : THypSB TiB20) (hG : GoodTSB TiB20 H x qm qr) {sig : ByteArray} {T : ℕ}
    (hS : Lvm.Q1.Streamed (memTX TiB20 Lvm.pubXTS x qm qr) sig T) {L : List (ℕ × ℕ)} (hL : ∀ a ∈ L, a ∈ powB20)
    (hpw : ∀ a ∈ L, a.1 + 2 < T ∧ a.2 ≤ 64) : Lvm.Q1.PowOkV (feAt sig) L :=
  powOk_of_blksU cfgB20 (Q := QB20) (tl := layB20) (d := dintsB20) rfl S.st.hlay
    (zOf_one (NTB20.toN.instL Pub.hdrLanesT QB20 layB20) H.ok.2 Lvm.M3.lay26 (Lvm.pubXTS x) qm qr) (hWB S H hG)
    hS hL hpw

/-- **Q_sig's `ChildOkS` at S2GS** (`childOkL`'s twin: the first walk `qsigNoSl`, the `KS` facts from the merged
tape over `contIvS aSP`). -/
theorem childOkB (S : NodeGB) (H : THypSB TiB20) {vk c : RecursionFast.Digest} (hok : okSL vk c x = true)
    (hb : (hdrOf x).b = 1) (hG : GoodTSB TiB20 H x qm qr ∧ SBlkU qm qr) :
    ChildOkS (sigIn cfgB20) (memTX TiB20 Lvm.pubXTS x qm qr).k := by
  have hone : (NTB20.toN.instL Pub.hdrLanesT QB20 layB20).src? layB20.one = some .one := H.ok.2
  obtain ⟨hH, hA⟩ := hholdsCS S Pub.hdrLanesT Lvm.pubXTS cfgU_B20 hone (hWB S H hG.1) H.hτ H.layOk
    hG.1.1.1.1.2 hG.2
  have hH' : QB20.Holds (memTX TiB20 Lvm.pubXTS x qm qr) := hH
  have hA' : QB20.Asserts (memTX TiB20 Lvm.pubXTS x qm qr) := hA
  rw [QB20_eq] at hH' hA'
  have P := parts_of_holdsB hH' hA'
  have h1 := (Lvm.Har.okb P.2.1).1
  have mp := inMapB20 S H vk c x qm qr hok hb hG
  have hk : ksSplit cfgB20.p = ksSplit P20 := frontPF_P20B.ksSplit_eq.trans ksSplit_P20.symm
  have hx : ∀ r < 449, ∀ l < 17, (memTX TiB20 Lvm.pubXTS x qm qr).k ((sigIn cfgB20).xs + 17 * r + l) =
      FK.ofBF64 (MqU qm (ksSplit P20 + r) l) := fun r hr l hl ↦ by rw [mp.xs r hr l hl, hk]
  have hy : ∀ r < 449, ∀ l < 4, (memTX TiB20 Lvm.pubXTS x qm qr).k ((sigIn cfgB20).ys + 4 * r + l) =
      FK.ofBF64 (YqU qm (ksSplit P20 + r) l) := fun r hr l hl ↦ by rw [mp.ys r hr l hl, hk]
  have hks := Lvm.E2U.sigKSin_of_GkL Lvm.E2S.contIvSB_ok.1 Lvm.E2S.contIvSB_ok.2.2.1 Lvm.E2S.contIvSB_ok.2.2.2.1 hG.1.2
    hx (fun r hr l hl ↦ hy r (by omega) l hl)
    (fun t ht l hl ↦ by
      rw [show (sigIn cfgB20).yc + 4 * t + l = (sigIn cfgB20).ys + 4 * (430 + t) + l by
        show ysQ cfgB20 + 4 * 430 + 4 * t + l = ysQ cfgB20 + 4 * (430 + t) + l; ring, hy _ (by omega) l hl,
        Nat.add_assoc])
    (fun l hl ↦ by
      rw [show (sigIn cfgB20).yls + l = (sigIn cfgB20).ys + 4 * 447 + l from rfl, hy _ (by omega) l hl])
    (fun l hl ↦ by
      rw [show (sigIn cfgB20).yns + l = (sigIn cfgB20).ys + 4 * 448 + l from rfl, hy _ (by omega) l hl])
  exact (qsigNoSl_sound (by rw [show (sigIn cfgB20).ln = 20 from rfl]; omega) h1 mp.flag hks
    (hbitsCSB (outsOnCS S Pub.hdrLanesT Lvm.pubXTS hone (hWB S H hG.1)) rfl rfl)
    fun a b ha hb h => FK.FKx_pow_inj (by omega) (by omega) h).2

/-- **Q_link's position cells at S2GS** (`posCellsU`'s twin). -/
theorem posCellsB (S : NodeGB) (H : THypSB TiB20) {vk c : RecursionFast.Digest} (hok : okSL vk c x = true)
    (hb : (hdrOf x).b = 1) (hG : GoodTSB TiB20 H x qm qr ∧ SBlkU qm qr) :
    ∀ k < (opens P20B).length, ((opens P20B).getD k default).L.height ≤ 64 →
      ∀ j < ((opens P20B).getD k default).L.t,
      (memTX TiB20 Lvm.pubXTS x qm qr).k (nK cfgB20 + posIdx P20B k j) =
        kOf (posL P20B (wsC qr) (((opens P20B).getD k default).pe + j / 8)
          (j % 8 * ((opens P20B).getD k default).L.height) ((opens P20B).getD k default).L.height) := by
  intro k hk hH j hj
  have hone : (NTB20.toN.instL Pub.hdrLanesT QB20 layB20).src? layB20.one = some .one := H.ok.2
  obtain ⟨hH', hA⟩ := hholdsCS S Pub.hdrLanesT Lvm.pubXTS cfgU_B20 hone (hWB S H hG.1) H.hτ H.layOk
    hG.1.1.1.1.2 hG.2
  have hH'' : QB20.Holds (memTX TiB20 Lvm.pubXTS x qm qr) := hH'
  have hA' : QB20.Asserts (memTX TiB20 Lvm.pubXTS x qm qr) := hA
  rw [QB20_eq] at hH'' hA'
  have P := parts_of_holdsB hH'' hA'
  have mp := inMapB20 S H vk c x qm qr hok hb hG
  have hp : cfgB20.p = P20B := rfl
  have hk' : k < (opens cfgB20.p).length := by rw [hp]; exact hk
  have hH2 : ((opens cfgB20.p).getD k default).L.height ≤ 64 := by rw [hp]; exact hH
  have hj' : j < ((opens cfgB20.p).getD k default).L.t := by rw [hp]; exact hj
  have hv := Lvm.Har.posVal_onCB (C := cfgB20) (outsOnCS S Pub.hdrLanesT Lvm.pubXTS hone (hWB S H hG.1))
    (by rw [hp]; exact streamOkB_P20B) (by rw [hp]; rfl) (by rw [hp]; exact hlvB20)
    (by rw [hp]; exact hpoB20) (by rw [hp]; exact hTB20) mp.stream hk' hH2 hj'
  rw [hp] at hv
  have hq := Lvm.QLink.qlinkB_pos (pt := p0 (nK cfgB20) 0) hposB20 P.1.1 hk hj
  exact hq.trans hv

/-- The current proof's `vk` cells at S2GS (`vk_cellsU` at `cfgB20`). -/
theorem vk_cellsB {M : Mem} {vk : RecursionFast.Digest}
    (hpub : ∀ j < pubLanesS P20B, M.k ((sigIn cfgB20).flag + j) = hdrLane x j) (hvk : (hdrOf x).vk = vk) :
    ∀ i < 4, M.k (pbB cfgB20 + 1 + i) = (digestLanes vk).getD i 0 := by
  intro i hi
  have hj : 1 + i < pubLanes := by rw [pubLanes_eq]; omega
  have e1 : M.k (pbB cfgB20 + 1 + i) = (Lvm.NS.hdrLanes x).getD (1 + i) 0 := by
    rw [Nat.add_assoc, show pbB cfgB20 = (sigIn cfgB20).flag from rfl, hpub _ (lt_of_lt_of_le (show 1 + i < 18 by
        omega) (by decide)),
      Lvm.NS.hdrLanes, List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range hj, Option.map_some,
      Option.getD_some]
  have hv : (Lvm.VEq.pubX x).vk = digestLanes vk := by rw [← hvk]; rfl
  have hl : i < (digestLanes vk).length := by simp only [digestLanes, List.length_map, List.length_range]; omega
  rw [e1, Lvm.NS.hdrLanes_eq_pubX, Pub.hdrLanes, hv]
  simp only [List.append_assoc, List.singleton_append]
  rw [Nat.add_comm, List.getD_append _ _ _ _ (by rw [List.length_cons]; omega), List.getD_cons_succ]

/-- **`Φ_Q` at `E2` holds at the folded accumulator at S2GS** (`phiU20_acc`'s twin). -/
theorem phiB20_acc (S : NodeGB) (hlin : Lvm.Typed.KT.linOkX cacheB20 = true) (H : THypSB TiB20)
    (hG : GoodTSB TiB20 H x qm qr) {M : Mem}
    (hpub : ∀ j < pubLanesS P20B, M.k ((sigIn cfgB20).flag + j) = hdrLane x j) :
    NTB20.phiT ((accCS M (pbB cfgB20)).pt.map Lvm.e2OfFE) = Lvm.e2OfFE (accCS M (pbB cfgB20)).y := by
  have hacc : Lvm.E2T.AccOkTT TiB20 (Lvm.pubXTS x) := hG.1.2
  have hn : pubLanesS P20B = 18 + 2 * (45 + 1) := by decide
  have hl : ∀ j < 46, (Lvm.Q2.ld2 (pbB cfgB20 + 18 + 2 * j)).val M =
      Lvm.e2OfFE (fe16At (Lvm.VEq.sigOfX x) (headerAt (hdrFixS + 16 * j))) := by
    intro j hj
    have hpb : (sigIn cfgB20).flag = pbB cfgB20 := rfl
    have e1 := hpub (18 + 2 * j) (by rw [hn]; omega)
    have e2 := hpub (18 + 2 * j + 1) (by rw [hn]; omega)
    rw [hpb, hdrLane_eq_kAt, show headerAt 8 + 8 * (18 + 2 * j) = headerAt (hdrFixS + 16 * j) by
      simp only [headerAt, hdrFixS]; omega] at e1
    rw [hpb, hdrLane_eq_kAt, show headerAt 8 + 8 * (18 + 2 * j + 1) = headerAt (hdrFixS + 16 * j) + 8 by
      simp only [headerAt, hdrFixS]; omega] at e2
    show (⟨(FE.ofK (M.k (pbB cfgB20 + 18 + 2 * j))).c₀, (FE.ofK (M.k (pbB cfgB20 + 18 + 2 * j + 1))).c₀⟩ : FE2) = _
    rw [Nat.add_assoc (pbB cfgB20), e1, Nat.add_assoc (pbB cfgB20) (18 + 2 * j), e2]
    rfl
  have hpt : (accCS M (pbB cfgB20)).pt.map Lvm.e2OfFE = (Lvm.pubXTS x).accIn.pt.map Lvm.e2OfFE := by
    simp only [accCS, Lvm.pubXTS, Lvm.pubOfWS, List.map_map]
    refine List.map_congr_left fun j hj => ?_
    have hj' : j < 45 := List.mem_range.mp hj
    exact hl j (by omega)
  have hy : Lvm.e2OfFE (accCS M (pbB cfgB20)).y = Lvm.e2OfFE (Lvm.pubXTS x).accIn.y := by
    simp only [accCS, Lvm.pubXTS, Lvm.pubOfWS]
    exact hl Lvm.VEq.accVT (by decide)
  rw [hpt, hy]
  have hc : cacheB20 = Lvm.Typed.cacheWX QB20 layB20 := cacheWXF_eq QB20 layB20 S.st.hlay
  show Lvm.E2T.PhiQGC cacheB20 _ = _
  rw [hc, Lvm.E2T.PhiQGC, Lvm.Typed.KT.PhiQGC_eqW QB20 layB20 S.st.hlay S.st.cache (hc ▸ hlin) _
    (by rw [List.length_map]; exact H.acc x)]
  have hpt' : Lvm.E2T.accPtT (Lvm.pubXTS x) = ((Lvm.pubXTS x).accIn.pt.map Lvm.e2OfFE).map FE2.toE2 := by
    rw [Lvm.E2T.accPtT, List.map_map]; rfl
  have hy' : Lvm.E2T.accYT (Lvm.pubXTS x) = FE2.toE2 (Lvm.e2OfFE (Lvm.pubXTS x).accIn.y) := rfl
  have hof : ∀ z : FE2, Lvm.Typed.ofE2 (FE2.toE2 z) = z := fun _ => rfl
  rw [Lvm.E2T.AccOkTT, Lvm.Typed.PhiQT, hpt', hy', List.map_map] at hacc
  simp only [Function.comp_def, hof, List.map_id'] at hacc
  exact FE2.toE2_injective hacc

end PairSH

/-- The mini-bus's table rounds at S2GS lie within the bus's point (`T.mbR = 6 ≤ 12`, `mbLinG_ok`'s `hpt`). -/
theorem mbR_leB20 (S : NodeGB) : tdataB20.mbR ≤ P20B.busDepth := by
  have hsc : Lvm.M3.sumcheckTabs (mbTOf cfgB20 frzB20) = mbTOf cfgB20 frzB20 := Lvm.Har.mbT_sumcheck cfgB20 _ _ _
  have hm := S.st.mini
  rw [S.mb] at hm
  simp only [TypedV.fitsMiniB, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at hm
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨-, -⟩, -⟩, -⟩, hR⟩, -⟩, -⟩, -⟩, -⟩ := hm
  rw [hsc] at hR
  obtain ⟨-, t2, -, -⟩ := Lvm.Har.tdataOf_mb cfgB20 frzB20
  show (Lvm.QTyped.tdataOf cfgB20 frzB20).mbR ≤ _
  rw [t2, ← hR, show cfgB20.p = P20B from rfl]
  decide

/-- **Q_arith is `V_S`'s decision at S2GS** (`harithL20`'s twin; SLF-STMT 7e's text at RE-FREEZE R2, closed in
`LvmS2GSStmtC` by this lemma): the program's segments after Q_sig on a good S2GS pair whose `qr` is `qm`'s stream
block. -/
theorem harithB20H (S : NodeGB) (hhar : harChkBB20 = true) (hlin : Lvm.Typed.KT.linOkX cacheB20 = true)
    (H : THypSB TiB20) (vk : RecursionFast.Digest) :
    ∀ c x qm qr, okSL vk c x = true → (hdrOf x).b = 1 →
      GoodTSB TiB20 H x qm qr ∧ SBlkU qm qr →
      InMapMBS (spongeBlocks P20B) (pubLanesS P20B) cfgB20 (memTX TiB20 Lvm.pubXTS x qm qr) vk x qm qr →
      LaneLink P20B (wsC qr) → LinkOk P20B (decode P20B (wsC qr)) →
      Ok (ctxOf TiB20.Q) (memTX TiB20 Lvm.pubXTS x qm qr) qaB20 p2B20H →
      decideFBX NTB20 vk (hdrOf x).cL (traceBytesB (decode P20B (wsC qr))) = true := by
  intro c x qm qr hok hb hG hin hLL hlink hrun
  obtain ⟨sig, hsig⟩ : ∃ s, traceBytesB (decode P20B (wsC qr)) = s := ⟨_, rfl⟩
  rw [hsig]
  -- the program's three parts after Q_sig: the pin, the front, `qarithS`
  have hrun' : Lvm.QSig.Ok (ctxOf TiB20.Q) (memTX TiB20 Lvm.pubXTS x qm qr)
      (pinF cfgB20.p >>= fun pin ↦ frontS cfgB20 >>= fun o ↦ qarithSB cfgB20 tdataB20 pin o)
      (p2B20H) := hrun
  obtain ⟨hPin, hR⟩ := Lvm.Har.okb hrun'
  obtain ⟨q1, hq1⟩ : ∃ q1, (p2B20H).adv
      (pinF cfgB20.p (p2B20H)).2 = q1 := ⟨_, rfl⟩
  obtain ⟨pin, hpinE⟩ : ∃ pin, (pinF cfgB20.p (p2B20H)).1 = pin :=
    ⟨_, rfl⟩
  rw [hq1, hpinE] at hR
  obtain ⟨hFr, hQa⟩ := Lvm.Har.okb hR
  obtain ⟨o, hfr⟩ : ∃ o, (frontS cfgB20 q1).1 = o := ⟨_, rfl⟩
  obtain ⟨q2, hq2⟩ : ∃ q2, q1.adv (frontS cfgB20 q1).2 = q2 := ⟨_, rfl⟩
  rw [hfr, hq2] at hQa
  -- the static facts, the stream, the gate, `vk`
  obtain ⟨htd, hTE, hTT, hTO, hPW, hOU, hLY, hSE, hML, hGR, hPL, hTR⟩ := harChkB20_sound hhar
  have hS : Lvm.Q1.Streamed (memTX TiB20 Lvm.pubXTS x qm qr) sig (streamLanes P20B) := hsig ▸ streamedB hin.stream hLL
  have hTl : streamLanes P20B = 71901 := sizes_P20B.1.2.2.2.1
  have hg : (memTX TiB20 Lvm.pubXTS x qm qr).k (pbB cfgB20) = 1 := hin.flag
  have hvk := vk_cellsB hin.pub (okSL_vk hok)
  -- `qarithS`: the constants
  unfold qarithSB at hQa
  obtain ⟨hZ, hR⟩ := Lvm.Har.okb hQa
  have ez : (const .E 0 (kc 0) q2).1 = ec q2.e := rfl
  have hzv := (Lvm.Har.constE_val hZ.1).trans ofK_zero
  rw [ez] at hzv
  rw [ez, Lvm.Loop.QRing.constE_adv] at hR
  obtain ⟨hO, hR⟩ := Lvm.Har.okb hR
  have eo : (const .E 1 (kc 0) ⟨q2.k, q2.e + 1⟩).1 = ec (q2.e + 1) := rfl
  have hov := (Lvm.Har.constE_val hO.1).trans ofK_one
  rw [eo] at hov
  rw [eo, Lvm.Loop.QRing.constE_adv] at hR
  obtain ⟨hZK, hR⟩ := Lvm.Har.okb hR
  rw [show (const .K 0 (kc 0) ⟨q2.k, q2.e + 1 + 1⟩).1 = kc q2.k from rfl, Lvm.Har.constK_adv] at hR
  obtain ⟨hOK, hR⟩ := Lvm.Har.okb hR
  rw [show (const .K 1 (kc 0) ⟨q2.k + 1, q2.e + 1 + 1⟩).1 = kc (q2.k + 1) from rfl, Lvm.Har.constK_adv] at hR
  have hzkv : (kc q2.k).val (memTX TiB20 Lvm.pubXTS x qm qr) = 0 := by
    have e := const_val hZK.1
    rw [show (const .K 0 (kc 0) ⟨q2.k, q2.e + 1 + 1⟩).1 = kc q2.k from rfl, ofK_zero] at e
    exact e
  have hokv : (kc (q2.k + 1)).val (memTX TiB20 Lvm.pubXTS x qm qr) = 1 := by
    have e := const_val hOK.1
    rw [show (const .K 1 (kc 0) ⟨q2.k + 1, q2.e + 1 + 1⟩).1 = kc (q2.k + 1) from rfl, ofK_one] at e
    exact e
  -- the typed phases (`typed_phaseTS` at `P20B`), their claims, the shape cell
  obtain ⟨t, q3, ht, hq3e, hTy, hR⟩ := ok_bindV hR
  obtain ⟨tc, q4, htc, hq4e, hTC, hR⟩ := ok_bindV hR
  obtain ⟨ka, q5, hka, hq5e, hKA, hR⟩ := ok_bindV hR
  obtain ⟨kb, q6, hkb, hq6e, hKB, hR⟩ := ok_bindV hR
  obtain ⟨sK, q7, hsKe, hq7e, hSK, hOpen⟩ := ok_bindV hR
  obtain ⟨hsc, hSs, hDd, hfix⟩ := miniB20 S
  have hpowA := powOkB S H hG.1 hS (L := powB20) (fun a ha => ha) hPW
  have hpowT : Lvm.Q1.PowOkV (feAt sig) (typedChalsT P20B) := fun a ha =>
    hpowA a (List.mem_append_right _ ha)
  have hpowF : Lvm.Q1.PowOkV (feAt sig) (powFrontU P20B) := fun a ha => hpowA a (List.mem_append_left _ ha)
  have hDL : tdataB20.mbD = Lvm.E2S.pTB.busDepth := by
    rw [show tdataB20.mbD = cfgB20.p.busDepth from hDd]
    rfl
  have htyped := typed_phaseTS P20B rfl rfl (c := ctxOf TiB20.Q) vk (hdrOf x).cL hS hg hvk (z := ec q2.e)
    (o := ec (q2.e + 1)) (zk := kc q2.k) (ok := kc (q2.k + 1)) rfl rfl hzv hov rfl rfl hzkv hokv htd Lvm.E2S.pTB rfl hDL
    (Lvm.E2T.m3G NTB20 P20B) (busLanes_of busLanesB_P20B) hpowT (by rw [hTl] at hTT ⊢; exact hTT)
    (by rw [hTl]; decide) _ (by simp) hTy (fun _ => rfl) (Lvm.E2T.typedItemsND NTB20 P20B)
  rw [show cfgB20.p = P20B from rfl] at ht
  -- the typed gadget's shape and its three claims (7c at the bus's outputs, `mbLinG_ok`)
  have hpbE : Lvm.pubOfWS vk (hdrOf x).cL sig = Lvm.pubOfWS vk (hdrOf x).cL sig := rfl
  have hfxL : tdataB20.mbFix = mbFixOf cfgB20 := (Lvm.Har.tdataOf_mb cfgB20 frzB20).2.2.2
  have hsh := Lvm.Har.soundG_ok (typedGS_shape (c := ctxOf TiB20.Q) (M := memTX TiB20 Lvm.pubXTS x qm qr) tdataB20
      P20B (pbB cfgB20)
    (pubLanesS P20B) (ec q2.e) (ec (q2.e + 1)) (kc q2.k) (kc (q2.k + 1)) (hDd.trans rfl)
    (fun bc cs => cs.map (Lvm.Har.CClaim.val (memTX TiB20 Lvm.pubXTS x qm qr)) = (Lvm.M3.mbClaimsN CMain.nu20
        NTB20.toN.mbT
      ⟨Lvm.Har.vs (memTX TiB20 Lvm.pubXTS x qm qr) bc.al, bc.be.val (memTX TiB20 Lvm.pubXTS x qm qr), bc.cnt.val
          (memTX TiB20 Lvm.pubXTS x qm qr),
        Lvm.Har.vs (memTX TiB20 Lvm.pubXTS x qm qr) bc.pt, Lvm.Har.vs (memTX TiB20 Lvm.pubXTS x qm qr) bc.vals, [0],
        Lvm.pubOfWS vk (hdrOf x).cL sig⟩).map (fun b => (Com.main, b)) ∧
      ∀ cc ∈ cs, cOkB (ec q2.e) cc = true ∧ cc.com = .main)
    (fun bc h1 h2 h3 h4 => by
      have hal2 : 2 ≤ (Lvm.Har.vs (memTX TiB20 Lvm.pubXTS x qm qr) bc.al).length := by
        show 2 ≤ (bc.al.map _).length
        rw [List.length_map, h1]; decide
      have hA := mbLinG_sound' (c := ctxOf TiB20.Q) hzv hov rfl rfl NTB20.toN.mbT tdataB20 hsc hSs hfix H.lin bc
        ⟨Lvm.Har.vs (memTX TiB20 Lvm.pubXTS x qm qr) bc.al, bc.be.val (memTX TiB20 Lvm.pubXTS x qm qr), bc.cnt.val
            (memTX TiB20 Lvm.pubXTS x qm qr),
          Lvm.Har.vs (memTX TiB20 Lvm.pubXTS x qm qr) bc.pt, Lvm.Har.vs (memTX TiB20 Lvm.pubXTS x qm qr) bc.vals, [0],
          Lvm.pubOfWS vk (hdrOf x).cL sig⟩ rfl rfl rfl rfl hal2 h2 h3
        (by rw [S.mb]; exact mbT_slots cfgB20 frzB20.wordK _ _ hal2)
        (by rw [S.mb]; exact mbT_cnt cfgB20 frzB20.wordK _ _)
        (by rw [S.mb, hfxL]; exact mbFixOf_exact cfgB20 frzB20.wordK _ _)
      have hB := mbLinG_ok (c := ctxOf TiB20.Q) (M := memTX TiB20 Lvm.pubXTS x qm qr) (zc := ec q2.e) (z := ec q2.e)
        (o := ec (q2.e + 1)) (bc := bc) hTR (by rw [h4]; exact mbR_leB20 S)
      exact fun q hH hA' => ⟨hA q hH hA', hB q hH⟩)) hTy
  rw [ht] at hsh htyped
  obtain ⟨⟨⟨hry, hryK⟩, ⟨hrr, hrrK⟩, hvR, hrvK⟩, htab, hcs, hcok⟩ := hsh
  rw [hTE] at htyped
  have hle : typedPosF P20B ≤ typedEndL tdataB20 P20B := by
    have h1 := mbPT_leL tdataB20 P20B
    have h2 := (busLanes_of busLanesB_P20B).mb
    -- by the equation lemma: `rfl` made the kernel evaluate `busL P20B iMB` (3.9 M hb)
    have h3 : mbPT P20B = 8 * busL P20B iMB - 40 := mbPT.eq_1 P20B
    omega
  -- the pin (`pin_phase`)
  have hnu : P20B.nuMain = 23 := rfl
  have hpb := pinHPB
  have hpe := pinEndB
  have hqa := pinQaB
  rw [hnu] at hpe hqa
  have epin : pinF cfgB20.p = Lvm.Q2.pinG 23 (phaseLane P20B .commit 1) (phaseLane P20B .commit (23 + 1)) := rfl
  rw [epin] at hPin hpinE
  obtain ⟨hpin, hpinV⟩ := Lvm.Q2.pin_phase hS (nu := 23) (by norm_num) hpb.symm hqa
    (by rw [hTl] at hTT ⊢; omega) (by rw [hqa]; rw [hTl] at hTT ⊢; omega) hPin.1
  rw [hpe] at hpin
  rw [hpinE] at hpinV
  obtain ⟨zP, aP, hzP, hzL⟩ := pinG_fst 23 (phaseLane P20B .commit 1) (phaseLane P20B .commit (23 + 1))
    (p2B20H)
  rw [hpinE] at hzP
  have hpinB : (Lvm.pinD 23 sig ⟨posOf P20B 1, 0, true⟩).1 =
      BlockClaim.point ⟨23, 0⟩ (Lvm.Har.vs (memTX TiB20 Lvm.pubXTS x qm qr) zP) (aP.val (memTX TiB20 Lvm.pubXTS x qm
          qr)) := by
    rw [hzP, cclaim_point] at hpinV
    exact (Prod.mk.inj hpinV).2.symm
  rw [hpinB] at hpin
  -- the front's inputs and its phases (`front_phasesS` at `cfgB20`, V_S's intervals `contIvS aSP`)
  have hT29 : 29 ≤ streamLanes P20B := by rw [hTl]; norm_num
  obtain ⟨hrD, hrY, hrM⟩ := rowWordsB S H hG.1
  have hch := childOkB S H hok hb hG
  have hone : (NTB20.toN.instL Pub.hdrLanesT QB20 layB20).src? layB20.one = some .one := H.ok.2
  have hon := outsOnCS S Pub.hdrLanesT Lvm.pubXTS hone (hWB S H hG.1)
  have hsb := sBits_onC hon
  obtain ⟨hnb, hn, hsbv⟩ := frontInsS hS hT29 (sigBits_ofC cfgB20 hon ⟨by decide, by decide⟩)
    hch hsb Lvm.VEq.accVT vk (hdrOf x).cL rfl rfl
  have hh : (Lvm.pubOfWS vk (hdrOf x).cL sig).h =
      (List.range 4).map fun l => (memTX TiB20 Lvm.pubXTS x qm qr).k (Lvm.Har.hLane l) := Lvm.Har.pub_h hS hT29 vk
          (hdrOf x).cL
  have hsmE : TypedV.smallT P20B (Lvm.pubOfWS vk (hdrOf x).cL sig) =
      decide ((Lvm.pubOfWS vk (hdrOf x).cL sig).n ≤ 2 ^ 18) := rfl
  obtain ⟨tp, htape, hfrel, hmbv⟩ := front_phasesS (p := P20B) cfgB20 rfl frontPF_P20B (Lvm.E2S.contIvSB Lvm.E2S.aSP)
      ivsB20 hS hTO hg hpowF hrD hrY hrM
    (Lvm.pubOfWS vk (hdrOf x).cL sig) hnb hn hsbv hh (ec q2.e)
    (TypedV.smallT P20B (Lvm.pubOfWS vk (hdrOf x).cL sig))
    (fun h => by rw [hsmE] at h; exact of_decide_eq_true h) hFr
  rw [hfr] at hfrel hmbv
  -- the shape: `σ` from `n' − 1`'s bits 18, 19, the `K` cell `sK`
  have hσ := Lvm.Har.sigma_val o.mb _ hmbv hn.1 hn.2
  rw [← hsmE] at hσ
  have hsK : sK.val (memTX TiB20 Lvm.pubXTS x qm qr) =
      if TypedV.smallT P20B (Lvm.pubOfWS vk (hdrOf x).cL sig) then 1 else 0 := by
    rw [← hsKe, mulAdd_spec hSK.1, ← hka, ← hkb, Lvm.Har.addK_val hKA.1, Lvm.Har.addK_val hKB.1, hzkv, ofK_one,
      add_zero, ← hσ]
    ring
  -- the opening's context, the pin as `FRel`
  have hF : Lvm.Q2.FCtxOk (memTX TiB20 Lvm.pubXTS x qm qr)
      ⟨ec q2.e, ec (q2.e + 1), kc q2.k, ⟨kc q2.k, kc q2.k⟩, ⟨kc (q2.k + 1), kc q2.k⟩, true⟩ := by
    refine ⟨hzv, hov, hzkv, rfl, rfl, ?_, ⟨rfl, rfl⟩, ?_⟩
    · show (⟨((kc (q2.k + 1)).val (memTX TiB20 Lvm.pubXTS x qm qr)).c₀, ((kc q2.k).val (memTX TiB20 Lvm.pubXTS x qm
        qr)).c₀⟩ : FE2) = 1
      rw [hokv, hzkv]; rfl
    · show (⟨((kc q2.k).val (memTX TiB20 Lvm.pubXTS x qm qr)).c₀, ((kc q2.k).val (memTX TiB20 Lvm.pubXTS x qm
        qr)).c₀⟩ : FE2) = 0
      rw [hzkv]; rfl
  have hzl : zP.length = 23 := by
    rw [hzL]; simp
  have hpt : pin.cw = .point ⟨CMain.nu20, 0⟩ (Lvm.Q2.pinPt pin) := by rw [hzP]; rfl
  have hpinR : Lvm.Q2.FRel (memTX TiB20 Lvm.pubXTS x qm qr) CMain.nu20 (.e3 pin)
      (BlockClaim.point ⟨23, 0⟩ (Lvm.Har.vs (memTX TiB20 Lvm.pubXTS x qm qr) zP) (aP.val (memTX TiB20 Lvm.pubXTS x qm
          qr))) := by
    refine ⟨?_, ?_⟩
    · rw [hzP]; simp [Lvm.Har.WF1, hzl]
    · rw [hzP, cclaim_point]
  -- the claims: the typed phases' (S2GT's halves, no table claims), the three claims (7c), then the front's
  have hz2 : (⟨kc q2.k, kc q2.k⟩ : C2).val (memTX TiB20 Lvm.pubXTS x qm qr) = 0 := by
    show (⟨((kc q2.k).val _).c₀, ((kc q2.k).val _).c₀⟩ : FE2) = 0; rw [hzkv]; rfl
  have ho2 : (⟨kc (q2.k + 1), kc q2.k⟩ : C2).val (memTX TiB20 Lvm.pubXTS x qm qr) = 1 := by
    show (⟨((kc (q2.k + 1)).val _).c₀, ((kc q2.k).val _).c₀⟩ : FE2) = 1; rw [hokv, hzkv]; rfl
  have hrelT := typed_relT (c := ctxOf TiB20.Q) (M := memTX TiB20 Lvm.pubXTS x qm qr) (zc := ec q2.e)
    (b := TypedV.smallT P20B (Lvm.pubOfWS vk (hdrOf x).cL sig)) (N := NTB20) (p := P20B)
    (m := Lvm.E2T.m3G NTB20 P20B) (pub := Lvm.pubOfWS vk (hdrOf x).cL sig) (T := tdataB20)
    (sOff := (layout0 cfgB20.p).s) (t := t.1) (z := ec q2.e) hzv hz2 ⟨rfl, rfl⟩ ho2 ⟨rfl, rfl⟩ htd hTR rfl rfl rfl
    hry hryK hrr hrrK hvR hrvK (by rw [htab]; simp)
    (st := Lvm.M3.sumcheckTabs NTB20.mbT) (by rw [show NTB20.mbT = NTB20.toN.mbT from rfl, hsc]; exact hSs)
    (m3G_tableClaimsT _ _ _ _)
  have hlinR := lin_rel (M := memTX TiB20 Lvm.pubXTS x qm qr) (zc := ec q2.e)
    (b := TypedV.smallT P20B (Lvm.pubOfWS vk (hdrOf x).cL sig)) (tabs := Lvm.M3.sumcheckTabs NTB20.mbT)
    (by rw [show NTB20.mbT = NTB20.toN.mbT from rfl, hsc]; exact hcs) (fun cc hc => (hcok cc hc).1)
  have hTC' := hTC.1
  unfold typedClaimsGL at hTC' htc
  obtain ⟨l, -, hl, -, hl1, -⟩ := ok_bindV hTC
  have htcE : tc = l ++ t.2.map Lvm.Q2.FClaim.e3 := by rw [← htc, bind_apply, hl]; rfl
  have hrl := hrelT q3 hl1.1
  rw [hl, htab] at hrl
  simp only [List.map_nil, m3G_tableClaimsT, Lvm.M3.tableClaimsR, List.zip_nil_right, Shape.zeroTails,
    List.map_nil, List.flatMap_nil, List.append_nil] at hrl
  have htrel := List.rel_append hrl hlinR
  beta_reduce at htrel
  rw [← htcE] at htrel
  have hrel := List.rel_append htrel hfrel
  -- the opening's static inputs
  have hopenU : posOf P20B (phaseItem0 P20B .openMain) =
      8 * (cfgMainF P20B (Lvm.Har.posBase cfgB20) (Lvm.Har.pwBase cfgB20)).U := by
    rw [cfgMainF_U]; exact hOU
  have hlayO : Lvm.Har.LayOkB (cfgMainF P20B (Lvm.Har.posBase cfgB20) (Lvm.Har.pwBase cfgB20)) (some P20B)
      (streamLanes P20B) =
      true := by
    rw [layOkB_pbF P20B (some P20B) _ _ (fun _ => 0) (fun _ => 0)]; exact hLY
  have hposO : Lvm.Har.PosOkB (cfgMainF P20B (Lvm.Har.posBase cfgB20) (Lvm.Har.pwBase cfgB20)) (some P20B)
      (memTX TiB20 Lvm.pubXTS x qm qr)
      sig 0 (cfgMainF P20B (Lvm.Har.posBase cfgB20) (Lvm.Har.pwBase cfgB20)).levels
      ((cfgMainF P20B (Lvm.Har.posBase cfgB20) (Lvm.Har.pwBase cfgB20)).U + 15) := by
    have hPL' : Lvm.Fin.PosLanes P20B (cfgMainF P20B (Lvm.Har.posBase cfgB20) (Lvm.Har.pwBase cfgB20)).g
        (cfgMainF P20B (Lvm.Har.posBase cfgB20) (Lvm.Har.pwBase cfgB20)).ood
        (cfgMainF P20B (Lvm.Har.posBase cfgB20) (Lvm.Har.pwBase cfgB20)).levels
        ((cfgMainF P20B (Lvm.Har.posBase cfgB20) (Lvm.Har.pwBase cfgB20)).U + 15) 0 (some P20B) := by
      rw [cfgMainF_g, cfgMainF_ood, cfgMainF_levels, cfgMainF_U]; exact hPL
    rw [← hsig]
    exact Lvm.Har.posOk_ofGB P20B cfgB20 rfl _ 0 (some P20B) (fun i => by rw [Nat.zero_add, cfgMainF_pb]) hPL'
      streamOkB_P20B hLL rfl hlvB20 (fun o ho => (hpoB20 o ho).1)
      (posCellsB S H hok hb hG)
  have hpwO : Lvm.Har.PwOk (cfgMainF P20B (Lvm.Har.posBase cfgB20) (Lvm.Har.pwBase cfgB20)) (memTX TiB20 Lvm.pubXTS x
      qm qr) 0
      (cfgMainF P20B (Lvm.Har.posBase cfgB20) (Lvm.Har.pwBase cfgB20)).levels := by
    intro i hi _
    rw [cfgMainF_levels] at hi
    rw [cfgMainF_pw, cfgMainF_g, Nat.zero_add]
    exact pw_onC hon hGR i (lt_of_lt_of_le hi hML)
  have hendO : 8 * Lvm.Har.stackEndL (cfgMainF P20B (Lvm.Har.posBase cfgB20) (Lvm.Har.pwBase cfgB20)).g
      (cfgMainF P20B (Lvm.Har.posBase cfgB20) (Lvm.Har.pwBase cfgB20)).ood
      (cfgMainF P20B (Lvm.Har.posBase cfgB20) (Lvm.Har.pwBase cfgB20)).levels
      ((cfgMainF P20B (Lvm.Har.posBase cfgB20) (Lvm.Har.pwBase cfgB20)).U + 15) (some P20B) = sig.size := by
    rw [← hsig, sigB_size hLL, stackEnd_cfgMainFB]; exact hSE
  have hq7 : 1 ≤ q7.e := by
    have h3 : 1 ≤ q3.e := le_trans (by simp) hq3e
    omega
  rw [show cfgB20.p = P20B from rfl] at hOpen
  -- `core_of_phasesL`, the opening by `open_phase`
  refine Lvm.Har.decideFSB_of P20B Lvm.E2S.pTB (Lvm.E2S.contIvSB Lvm.E2S.aSP) NTB20 vk (hdrOf x).cL sig ?_ (phiB20_acc S hlin H hG.1 hin.pub)
  refine Lvm.Har.core_of_phasesB P20B Lvm.E2S.pTB (Lvm.E2S.contIvSB Lvm.E2S.aSP) NTB20 vk (hdrOf x).cL sig hbB hpin htyped htape ?_
  intro s hs hsok
  rw [Lvm.E2T.typedItemsND_flat]
  dsimp only
  rw [show (Lvm.E2T.m3G NTB20 P20B).busFinal = Lvm.M3.busFinalR (Lvm.M3.sumcheckTabs NTB20.mbT) from rfl,
    show P20B.nuMain = CMain.nu20 from rfl]
  have key := Lvm.Q2.open_phaseB P20B (cfgMainF P20B (Lvm.Har.posBase cfgB20) (Lvm.Har.pwBase cfgB20)) rfl rfl rfl
    rfl rfl hF pin hpt _ _ hpinR _ _ _ hrel o.mb hσ sK (kc (pbB cfgB20)) hsK hS hlayO
    (by rw [Cell.val_K, hg, ofK_one]) rfl hposO hpwO hendO hq7 hOpen s (hs.trans hopenU) hsok
  beta_reduce at key
  rw [hnu] at key
  dsimp only at key
  exact key

end Lvm.E2Q