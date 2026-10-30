-- G6: this module also holds the former modules `FRSoundness4R4Cols` (one section each, in import order).
import FRSoundness4R4Qv

section G6_FRSoundness4R4Cols

-- New for `flock-recursive` (BLUEPRINT revision 4.1, A.3, A.9, §5.1; track R4g). The 3.x template is
-- `FRSoundnessAccCol` (`capDig_eq`, `ys_facts`) with `FRSoundnessAccPf.lvl_facts`.

/-!
# `FinRest4.cols`: P2.i's opened columns on the log

* **`lv_facts4`**: the kind's ladder against `seq4`'s (the same `t` and `ell`, no deeper Merkle
  path, no larger cap, the P2 squeezes cover the positions); **`lvK_eq4`**: the program's kind
  level `seq4.lvK m i` is T4's `lvOf m i`.
* Table certificates (`decide +kernel` on `seq4`'s tables): the level phases (`phases4_lvl`),
  the cap messages (`capMsg4`), the columns inside π (`colsEnd4`).
* **`capDig_eq4`**: level `i`'s cap entry on the log is π's 32 bytes where `posOps4` compares.
* **`dAt_eq4`** (revision 4.4.1): read `(i, q)`'s committed digest on the log (`T4.dAt`, `CapD`'s
  message) is π's 32 bytes where `posOps4` reads it (`dOff4 seq4 i + 32·q`).
* **`ys_facts4`** (3.x's `ys_facts`): the fold registers `yReg4 p i q` hold
  `Σ_r eq(sᵢ, r)·col_q[r]`, with a path on the log from `col_q` at `qPos` to its committed digest
  `D_r` (revision 4.4.1, (β′); `D_r` is the cap entry under `T4.truthCap`).
* **`cols4_of_run`**: `FinRest4.cols` for `yv4`, the fold registers' values.
-/

namespace FR.Snd.R4
open RecursionFast Rev4 FR.Merkle Finset

/-! ## Levels and tables -/

theorem lvK_eq4 (m i : ℕ) : seq4.lvK m i = lvOf m i := by
  rw [seq4_eq]; rfl

theorem lv_facts4 {m : ℕ} (hm : m = 30 ∨ m = 31 ∨ m = 32) {i : ℕ} (hi : i < 5) :
    (lvOf m i).t = (seq4.lv i).t ∧ (lvOf m i).sib ≤ (seq4.lv i).sib ∧
      (lvOf m i).cap ≤ (lvOf m i).logN ∧ (lvOf m i).cap ≤ (seq4.lv i).cap ∧
      ((lvOf m i).t - 1) / (lvOf m i).per < (seq4.lv i).sq ∧ 0 < (lvOf m i).per ∧
      (lvOf m i).ell = hEll i ∧ 2 ^ hEll i ≤ colBytes i / 16 ∧ 0 < (seq4.lv i).sq ∧
      0 < (lvOf m i).t := by
  rw [seq4_eq]; rcases hm with rfl | rfl | rfl <;> interval_cases i <;> decide

/-- Level `i`'s phases P1, C, P2, Q in `seq4`'s table. -/
theorem phases4_lvl {i : ℕ} (hi : i < 5) :
    (phasesOf seq4)[27 + 5 * i]? = some ("C", .absorb (capField i) (capBytesOf seq4 i)) ∧
      (phasesOf seq4)[28 + 5 * i]? = some ("P2", .squeezes (seq4.lv i).sq (.pos i)) ∧
      (phasesOf seq4)[29 + 5 * i]? = some ("Q", .queries i) := by
  interval_cases i <;> exact ⟨rfl, rfl, rfl⟩

theorem phStart4_P2 {i : ℕ} (hi : i < 5) : phStart4 (28 + 5 * i) = phStart4 (27 + 5 * i) + 1 := by
  rw [phStart4, phStart4, fsStarts4_eq]; interval_cases i <;> rfl

/-- **The cap messages** (a table certificate): level `i`'s cap is absorbed at `capPos i`, from
the caps field at `capOff4 seq4 i`. -/
theorem capMsg4 {i : ℕ} (hi : i < 5) :
    (fsMsgs4 seq4).getD (T4.capPos i) none =
      some (fieldOffOf seq4 fCaps + capOff4 seq4 i, 2 ^ (seq4.lv i).cap * 32) := by
  rw [T4.capPos, phStart4, phStart4, fsStarts4_eq, fsMsgs4, capOff4, fieldOffOf, seq4_eq]
  interval_cases i <;> decide +kernel

/-- **The columns lie inside π** (a table certificate). -/
theorem colsEnd4 {i : ℕ} (hi : i < 5) :
    fieldOffOf seq4 fCols + phaseOffOf seq4 (29 + 5 * i) fCols + (seq4.lv i).t * colBytes i ≤
      piSizeOf seq4 := by
  rw [fieldOffOf, phaseOffOf, piSizeOf, seq4_eq]
  interval_cases i <;> decide +kernel

/-! ## The caps and the folds on an accepted run -/

section Run
variable {impl : OpImpl} {p : KindP} {inp : Input} {tr : Trace} {y : List Val × List Bool × Trace}

/-- **Level `i`'s cap entry on the log is π's** where `posOps4` compares (3.x's `capDig_eq`). -/
theorem capDig_eq4 (h : SkRun4 impl p inp tr y) {i : ℕ} (hi : i < 5) {e : ℕ}
    (he : e < 2 ^ (seq4.lv i).cap) :
    T4.capDig (fsOf tr (itemsOf seq4)) i e =
      bytesAt inp.π (fieldOffOf seq4 fCaps + capOff4 seq4 i + 32 * e) 32 := by
  have hp : T4.capPos i < 482 ∧ T4.capPos i ≠ 0 := by
    rw [T4.capPos, phStart4, phStart4, fsStarts4_eq]; interval_cases i <;> decide
  have e1 := h.hq (T4.capPos i) (by omega)
  rw [capMsg4 hi] at e1
  simp only [qOf, hp.2, if_false] at e1
  have h32 := Nat.mul_le_mul_right 32 (Nat.succ_le_of_lt he)
  rw [T4.capDig, msgAt_of_q e1, bytesAt_extract_of_le inp.π (by rw [Nat.succ_mul] at h32; omega)]

/-- **`D`'s message** (a table certificate): `CapD` absorbs field `fD`, all `dBytes` of it. -/
theorem dMsg4 : (fsMsgs4 seq4).getD (phStart4 52) none = some (fieldOffOf seq4 fD, dBytes seq4) := by
  rw [phStart4, fsStarts4_eq, fsMsgs4, fieldOffOf, dBytes, seq4_eq]; decide +kernel

/-- **Read `(i, q)`'s committed digest on the log is π's** where `posOps4` reads it. -/
theorem dAt_eq4 (h : SkRun4 impl p inp tr y) {i q : ℕ} (hi : i < 5) (hq : q < T4.tq i) :
    T4.dAt (fsOf tr (itemsOf seq4)) i q = bytesAt inp.π (dOff4 seq4 i + 32 * q) 32 := by
  obtain ⟨p52, -⟩ := T4.capPh_pos
  have e1 := h.hq (phStart4 52) (by omega)
  rw [dMsg4] at e1
  simp only [qOf, show phStart4 52 ≠ 0 by omega, if_false] at e1
  have hr := T4.rdIx_le hi hq
  have hdb : dBytes seq4 = 27872 := by rw [dBytes, seq4_eq]; decide +kernel
  have e2 : fieldOffOf seq4 fD + 32 * T4.rdIx i q = dOff4 seq4 i + 32 * q := by
    rw [dOff4, T4.rdIx, Nat.mul_add, Nat.add_assoc]
  rw [T4.dAt, msgAt_of_q e1, bytesAt_extract_of_le inp.π (by rw [hdb]; omega), e2]

/-- The fold register of query `q` of level `i` (Q.i's outs). -/
def yReg4 (p : KindP) (i q : ℕ) : Reg := ((skeleton4 seq4 p).2.outs.getD (29 + 5 * i) []).getD q 0

/-- **The column folds** (`FinRest4`'s `y`): the fold registers' values. -/
def yv4 (p : KindP) (R : Array Val) (i q : ℕ) : K := (rd R (yReg4 p i q)).toK

/-- **Q.i's folds on the log** (3.x's `ys_facts`): the fold register of query `q` holds
`Σ_r eq(sᵢ, r)·col_q[r]`, and `col_q` has a path on `L` from `qPos` to its committed digest `D_r`
(revision 4.4.1). -/
theorem ys_facts4 (h : SkRun4 impl p inp tr y) {L : Log} (hL : (L.map Prod.fst).Nodup)
    (hin : ∀ e ∈ tr, e ∈ L) (hπ : inp.π.size = piSizeOf seq4)
    (hm : p.d.m = (kindOfC (fsOf tr (itemsOf seq4))).m) {i : ℕ} (hi : i < 5) :
    ∀ q < (CKind.lv (kindOfC (fsOf tr (itemsOf seq4))) i).t, ∃ col : ByteArray, ∃ ss : List Digest,
      ss.length = (CKind.lv (kindOfC (fsOf tr (itemsOf seq4))) i).sib ∧
      (openPath (frEnc i) col (T4.qPos (kindOfC (fsOf tr (itemsOf seq4))) (fsOf tr (itemsOf seq4)) i q) ss).runLog L =
        some (T4.dAt (fsOf tr (itemsOf seq4)) i q) ∧
      rd (#[] ++ y.1.toArray) (yReg4 p i q) =
        .k (∑ r : Fin (CKind.lv (kindOfC (fsOf tr (itemsOf seq4))) i).rows,
          eqBits (T4.sAt (fsOf tr (itemsOf seq4)) i) (CKind.lv (kindOfC (fsOf tr (itemsOf seq4))) i).ell r *
            algebraMap F K (readF col (16 * r))) := by
  set es := fsOf tr (itemsOf seq4)
  set κ := kindOfC es
  set R := #[] ++ y.1.toArray with hRd
  have hLk : CKind.lv κ i = lvOf κ.m i := rfl
  obtain ⟨hT, hsib, hcapN, hcap, hper, hper0, hell, hcol, hsq0, -⟩ := lv_facts4 (CKind.m_mem κ) hi
  rw [← hLk] at hT hsib hcapN hcap hper hper0 hell
  have hK : seq4.lvK p.d.m i = CKind.lv κ i := by rw [hm, lvK_eq4]; rfl
  obtain ⟨hC, hP2, hQ⟩ := phases4_lvl hi
  obtain ⟨hnC, eC⟩ := ph4 hC
  obtain ⟨hnP, eP⟩ := ph4 hP2
  obtain ⟨hnQ, eQ⟩ := ph4 hQ
  obtain ⟨hn1, e1⟩ := ph4 (phases4_p1 seq4 hi)
  -- P1.i: its challenge registers
  set fi0 : FinIn := ⟨(skeleton4 seq4 p).2.outs, [], #[]⟩
  have hfi0 : fi0.outs = (skeleton4 seq4 p).2.outs := rfl
  obtain ⟨b1, hout1, hsv, -⟩ := p1_view4 h hfi0 hi
  have hb1 : b1 = (cAt4 seq4 p (26 + 5 * i)).next := by
    rw [lvOuts_eq4 hfi0, skeleton4_outs seq4 p hn1, e1, genPhase4_roundsK seq4 p _ "P1" fP1 _ _ rfl
      (by rw [seq4_ell hi]; unfold hEll; interval_cases i <;> decide)] at hout1
    have := congrArg List.head? hout1
    simp only [List.cons_append, List.head?_cons, Option.some.injEq] at this
    omega
  -- the context at Q.i
  have hcQ : cAt4 seq4 p (29 + 5 * i) =
      (genPhase4 seq4 p (28 + 5 * i) ("P2", .squeezes (seq4.lv i).sq (.pos i)) (cAt4 seq4 p (28 + 5 * i))).2 := by
    rw [show 29 + 5 * i = 28 + 5 * i + 1 by ring, cAt4_succ seq4 p hnP, eP]
  have hcP : cAt4 seq4 p (28 + 5 * i) =
      (genPhase4 seq4 p (27 + 5 * i) ("C", .absorb (capField i) (capBytesOf seq4 i)) (cAt4 seq4 p (27 + 5 * i))).2 := by
    rw [show 28 + 5 * i = 27 + 5 * i + 1 by ring, cAt4_succ seq4 p hnC, eC]
  have hc1 : cAt4 seq4 p (27 + 5 * i) =
      (genPhase4 seq4 p (26 + 5 * i) ("P1", .rounds fP1 (seq4.lv i).ell 2 true) (cAt4 seq4 p (26 + 5 * i))).2 := by
    rw [show 27 + 5 * i = 26 + 5 * i + 1 by ring, cAt4_succ seq4 p hn1, e1]
  have hfR : (cAt4 seq4 p (29 + 5 * i)).foldR = (List.range (hEll i)).map (fun j => b1 + 13 * j + 6) := by
    rw [hcQ, (genPhase4_pos_ctx ..).1, hcP, (genPhase4_absorb_ctx ..).1, hc1,
      genPhase4_roundsK_foldR _ _ _ _ _ rfl, seq4_ell hi, hb1]
  have hpA : (cAt4 seq4 p (29 + 5 * i)).posAns = (List.range (seq4.lv i).sq).map ((cAt4 seq4 p (28 + 5 * i)).next + ·) := by
    rw [hcQ, (genPhase4_pos_ctx ..).2.1]
  obtain ⟨-, -, hans⟩ := pos_view4 h hnP (by rw [eP]) hsq0
  obtain ⟨bQ, houtQ, -, hQv⟩ := queries_view4 h hL hin hnQ (by rw [eQ]) (by rw [hK]; exact hsib)
  intro q hq
  have hq' : q < (seq4.lv i).t := hT ▸ hq
  obtain ⟨hidx, hy, -, -, ss, hss, hpath⟩ := hQv q hq'
  have hgy : yReg4 p i q = bQ + 2 + posW4 seq4 i * q + 3 := by
    rw [yReg4, houtQ, List.getD_eq_getElem _ _ (by simpa using hq'), List.getElem_map, List.getElem_range]
  have hfr : ((cAt4 seq4 p (29 + 5 * i)).foldR.map fun x => (rd R x).toK) =
      (List.range (hEll i)).map (T4.sAt es i) := by
    rw [hfR, List.map_map]
    exact List.map_congr_left fun j hj => by
      simp only [Function.comp_apply]; rw [hsv j (List.mem_range.1 hj)]; rfl
  have hqp : q / (CKind.lv κ i).per < (seq4.lv i).sq :=
    lt_of_le_of_lt (Nat.div_le_div_right (by omega)) hper
  have hj : idxOf (CKind.lv κ i).logN ((rd R ((cAt4 seq4 p (29 + 5 * i)).posAns.getD
      (q / (CKind.lv κ i).per) 0)).toD) (q % (CKind.lv κ i).per) = T4.qPos κ es i q := by
    rw [hpA, List.getD_eq_getElem _ _ (by simpa using hqp), List.getElem_map, List.getElem_range,
      hans _ hqp, T4.qPos, posAt, phStart4_P2 hi]
    rfl
  simp only [hK, ← hRd] at hidx hy hpath hss
  simp only [hj, hfr] at hy hpath
  set col := inp.π.extract (absOff 0 (fieldOffOf seq4 fCols + phaseOffOf seq4 (29 + 5 * i) fCols +
      q * colBytes i)) (absOff 0 (fieldOffOf seq4 fCols + phaseOffOf seq4 (29 + 5 * i) fCols +
      q * colBytes i) + colBytes i) with hcold
  have hsz : col.size = colBytes i := by
    have h1 := colsEnd4 hi
    have h2 : q * colBytes i + colBytes i ≤ (seq4.lv i).t * colBytes i := by
      have := Nat.mul_le_mul_right (colBytes i) (show q + 1 ≤ (seq4.lv i).t by omega)
      rwa [Nat.add_mul, one_mul] at this
    rw [hcold, ByteArray.size_extract, absOff_zero, hπ]; omega
  refine ⟨col, ss, hss, ?_, ?_⟩
  · rw [hpath, absOff_zero, dAt_eq4 h hi hq']
  · clear_value col
    have hs : ((List.range (hEll i)).map (T4.sAt es i)).toArray.size = hEll i := by simp
    have e1 := dotKF_eq_sum ((List.range (hEll i)).map (T4.sAt es i)).toArray col
      (by rw [hs, hsz]; exact hcol)
    rw [hs] at e1
    have e2 : (∑ r : Fin (CKind.lv κ i).rows, eqBits (T4.sAt es i) (CKind.lv κ i).ell r *
        algebraMap F K (readF col (16 * r))) = ∑ r ∈ range (2 ^ hEll i),
          eqBits (fun v => ((List.range (hEll i)).map (T4.sAt es i)).toArray.getD v 0)
            (hEll i) r * algebraMap F K (readF col (16 * r)) := by
      rw [Fin.sum_univ_eq_sum_range (fun r => eqBits (T4.sAt es i) (CKind.lv κ i).ell r *
        algebraMap F K (readF col (16 * r))), Level.rows, hell]
      refine sum_congr rfl fun r _ => ?_
      rw [eqBits_congr (r' := fun v => ((List.range (hEll i)).map (T4.sAt es i)).toArray.getD
        v 0) (fun v hv => by simp [Array.getD_eq_getD_getElem?, hv])]
    rw [hgy, hy, e1, ← e2]

/-- **`FinRest4.cols`** for the fold registers' values `yv4` (the log repeats no query; revision
4.4.1: the paths end at the committed digests). -/
theorem cols4_of_run (h : SkRun4 impl p inp tr y) {L : Log} (hb : ¬ Bad L) (hin : ∀ e ∈ tr, e ∈ L)
    (hπ : inp.π.size = piSizeOf seq4) (hm : p.d.m = (kindOfC (fsOf tr (itemsOf seq4))).m) :
    ∀ i < 5, ∀ q < (CKind.lv (kindOfC (fsOf tr (itemsOf seq4))) i).t, ∃ col : ByteArray, ∃ ss : List Digest,
      ss.length = (CKind.lv (kindOfC (fsOf tr (itemsOf seq4))) i).sib ∧
      (openPath (frEnc i) col (T4.qPos (kindOfC (fsOf tr (itemsOf seq4))) (fsOf tr (itemsOf seq4)) i q) ss).runLog L =
        some (T4.dAt (fsOf tr (itemsOf seq4)) i q) ∧
      yv4 p (#[] ++ y.1.toArray) i q = ∑ r : Fin (CKind.lv (kindOfC (fsOf tr (itemsOf seq4))) i).rows,
        eqBits (T4.sAt (fsOf tr (itemsOf seq4)) i) (CKind.lv (kindOfC (fsOf tr (itemsOf seq4))) i).ell r *
          algebraMap F K (readF col (16 * r)) := by
  have hL : (L.map Prod.fst).Nodup := by by_contra hr; exact hb (.inr (.inr (.inr hr)))
  intro i hi q hq
  obtain ⟨col, ss, hss, hpath, hy⟩ := ys_facts4 h hL hin hπ hm hi q hq
  exact ⟨col, ss, hss, hpath, by rw [yv4, hy]; rfl⟩

/-- The program's kind is the chain's: a segment's. -/
theorem dm_seg4 {σ : SegKind} (h : SkRun4 impl (.ofSeg σ) inp tr y) :
    (KindP.ofSeg σ).d.m = (kindOfC (fsOf tr (itemsOf seq4))).m := by
  rw [kindOfC_seg4 h]; cases σ <;> rfl

/-- … and a node's. -/
theorem dm_node4 {ν : NodeKind} (h : SkRun4 impl (.ofNode ν) inp tr y) :
    (KindP.ofNode ν).d.m = (kindOfC (fsOf tr (itemsOf seq4))).m := by
  rw [kindOfC_node4 h]; cases ν <;> rfl

end Run

end FR.Snd.R4

end G6_FRSoundness4R4Cols

section G6_FRSoundness4R4Cap

-- New for `flock-recursive` (PACK-4.4 §11.4–§11.5; track A3′ run 2): the batched cap check's run
-- (`FRVIRFinals4.capChkOps`) on an accepted `gen4 seq4` run, read on the log (`T4.capChk4`).

/-!
# The batched cap check on an accepted run (revision 4.4.1, (β′))

`finOps4` ends with `capChkOps seq4` (the field `capF`, `Fields4.cap`). This module runs it:

* **the constants** of `seq4` (`cap_consts`) and **`reloc_capChk`** (its π reads are absolute: the
  relocation changes nothing);
* **the register families** (`run_powChain`, `run_bitPow`, `run_macD`, `run_macA`): each a run of
  equal-width blocks, its values in closed form;
* **`capChk_run`**: the three asserts are V's (I) per F half and (II) on the registers' values;
* **`capChk4_of_fields`**: on the log, `T4.capChk4` (the reads' digests and cap indices are
  `queries_view4`'s, `ζ`/`z` the `CapZeta`/`CapChkZ` answers, `A` and the caps π's absorbed fields).
-/

namespace FR.Snd.R4
open RecursionFast Rev4 Finset

/-! ## `seq4`'s constants -/

theorem cap_consts : seq4.capChk = true ∧ (phasesOf seq4).length = 56 ∧ capMax seq4 = 9 ∧
    capEntries seq4 = 1536 ∧ fieldOffOf seq4 0 = 0 := by
  rw [seq4_eq]; refine ⟨rfl, ?_, ?_, ?_, ?_⟩ <;> decide +kernel

/-! ## The relocation is the identity on the cap check -/

/-- A π read of field `0` (or no π read): what `reloc` keeps when field `0` is at offset `0`. -/
def F0 : Op → Bool
  | .piField f _ _ => f == 0
  | .piElem f _ => f == 0
  | .piElemK f _ => f == 0
  | .piDigest f _ => f == 0
  | .piDigestAt f _ _ => f == 0
  | _ => true

theorem reloc_F0 {S : Seq} (h0 : fieldOffOf S 0 = 0) : ∀ op, F0 op = true → reloc S op = op := by
  intro op h
  cases op <;> simp_all [F0, reloc]

theorem F0_capChk (S : Seq) (outs : Array (List Reg)) (b : ℕ) :
    ∀ op ∈ capChkOps S outs b, F0 op = true := by
  rw [← List.all_eq_true]
  unfold capChkOps
  split
  · simp [List.all_eq_true, F0, powChainOps, bitPowOps, macDOps, macAOps]
  · rfl

theorem reloc_capChk (outs : Array (List Reg)) (b : ℕ) :
    (capChkOps seq4 outs b).map (reloc seq4) = capChkOps seq4 outs b := by
  conv_rhs => rw [← List.map_id (capChkOps seq4 outs b)]
  exact List.map_congr_left fun op h => reloc_F0 cap_consts.2.2.2.2 op (F0_capChk seq4 outs b op h)

/-! ## Running straight-line blocks -/

section Run
variable (impl : OpImpl) (κ : Kind) (inp : Input)

/-- **A block of value ops**: op `j` appends `vss[j]` with its flag up. -/
theorem pureRun_vals (X : Array Val) :
    ∀ (ops : List Op) (vss : List (List Val)) (L : List Val), ops.length = vss.length →
      (∀ j (hj : j < ops.length), evalOp impl κ inp (X ++ (L ++ (vss.take j).flatten).toArray) ops[j] =
        .vals (vss.getD j []) true) →
      pureRun impl κ inp ops X L = some (L ++ vss.flatten, true)
  | [], [], L, _, _ => by simp [pureRun]
  | op :: ops, vs :: vss, L, hl, h => by
    have h0 := h 0 (by simp)
    simp only [List.getElem_cons_zero, List.take_zero, List.flatten_nil, List.append_nil,
      List.getD_cons_zero] at h0
    simp only [pureRun, h0]
    have ih := pureRun_vals X ops vss (L ++ vs) (by simpa using hl) fun j hj => by
      have := h (j + 1) (by simp; omega)
      simpa [List.take_succ_cons, List.flatten_cons, List.append_assoc, List.getD_cons_succ] using this
    rw [ih]; simp [List.append_assoc]
  | [], _ :: _, _, hl, _ => by simp at hl
  | _ :: _, [], _, hl, _ => by simp at hl

/-- The `k`-th value of a run of equal-width blocks. -/
theorem flatMap_getD {g : ℕ → List Val} {w : ℕ} (hg : ∀ k, (g k).length = w) {n k j : ℕ} (hk : k < n)
    (hj : j < w) : ((List.range n).flatMap g).getD (w * k + j) default = (g k).getD j default :=
  P4a.getD_flatMap hg n k j hk hj

theorem flatMap_length {g : ℕ → List Val} {w : ℕ} (hg : ∀ k, (g k).length = w) (n : ℕ) :
    ((List.range n).flatMap g).length = w * n :=
  P4a.length_flatMap_const hg n

theorem arr_app_nil (A : Array Val) : A ++ ([] : List Val).toArray = A := by simp

theorem flatMap1_getD (f : ℕ → Val) {n k : ℕ} (hk : k < n) :
    ((List.range n).flatMap fun t => [f t]).getD k default = f k := by
  have := flatMap_getD (g := fun t => [f t]) (w := 1) (fun _ => rfl) hk (show 0 < 1 by norm_num)
  simpa using this

/-- Reading a register of an appended block. -/
theorem rd_blk (X : Array Val) (V : List Val) {i : ℕ} (hi : X.size ≤ i) :
    rd (X ++ V.toArray) i = V.getD (i - X.size) default := by
  rw [show i = X.size + (i - X.size) by omega, rd_app, Nat.add_sub_cancel_left]

/-- **A power chain** `g^1 … g^n` (`powChainOps`). -/
theorem run_powChain (X : Array Val) (one g : ℕ) (G : K) (n : ℕ) (ho : one < X.size) (hg : g < X.size)
    (h1 : rd X one = .k 1) (hG : rd X g = .k G) :
    pureRun impl κ inp (powChainOps one g n X.size) X [] =
      some ((List.range n).flatMap fun r => [Val.k (G ^ (r + 1))], true) := by
  have e : powChainOps one g n X.size = (List.range n).flatMap fun r =>
      [Op.mulK (if r = 0 then one else X.size + r - 1) g] := by
    rw [powChainOps, List.map_eq_flatMap]
  rw [e]
  have hP := P4a.pureRun_flatMap impl κ inp X []
    (fun r => [Op.mulK (if r = 0 then one else X.size + r - 1) g]) (fun r => [Val.k (G ^ (r + 1))]) n ?_
  · simpa using hP
  intro k hk
  rw [List.nil_append]
  refine pureRun_vals impl κ inp _ _ [[Val.k (G ^ (k + 1))]] [] rfl fun j hj => ?_
  have hj0 : j = 0 := by simpa using hj
  subst hj0
  simp only [List.getElem_cons_zero, List.take_zero, List.flatten_nil, List.nil_append, List.append_nil,
    evalOp, List.getD_cons_zero, arr_app_nil]
  have hgr : rd (X ++ ((List.range k).flatMap fun r => [Val.k (G ^ (r + 1))]).toArray) g = .k G := by
    rw [rd_app_left _ _ hg, hG]
  rw [hgr]
  split_ifs with h0
  · subst h0; rw [rd_app_left _ _ ho, h1]; simp [Val.toK]
  · rw [show X.size + k - 1 = X.size + (k - 1) by omega, rd_app]
    have := flatMap_getD (g := fun r => [Val.k (G ^ (r + 1))]) (w := 1) (fun _ => rfl) (show k - 1 < k by omega)
      (show 0 < 1 by norm_num)
    rw [one_mul, add_zero] at this
    rw [this]; simp only [List.getD_cons_zero, Val.toK]
    rw [show k - 1 + 1 = k by omega, ← pow_succ]

/-- `x mod 2^(t+1)` adds bit `t` of `x`. -/
theorem mod_two_pow_succ (x t : ℕ) :
    x % 2 ^ (t + 1) = x % 2 ^ t + (if x.testBit t then 2 ^ t else 0) := by
  rw [Nat.mod_pow_succ, Nat.testBit_eq_decide_div_mod_eq]
  rcases Nat.mod_two_eq_zero_or_one (x / 2 ^ t) with h | h <;> simp [h]

theorem pow_mod_two_pow_succ (z : K) (x t : ℕ) :
    z ^ (x % 2 ^ t) * (if x.testBit t then z ^ 2 ^ t else 1) = z ^ (x % 2 ^ (t + 1)) := by
  rw [mod_two_pow_succ]; split_ifs <;> simp [pow_add]

/-- One step of a read's bit power: bit `t`, `z^{2^t}` or `1`, the running product. -/
def bitVals (z W : K) (kk t : ℕ) : List Val :=
  [.bit (kk.testBit t), if kk.testBit t then .k (z ^ 2 ^ t) else .k 1, .k (W * z ^ (kk % 2 ^ (t + 1)))]

/-- **The bit power of one read** (`bitPowOps`): its `3·nb` registers; the last holds
`W·z^{kk mod 2^nb}` (`W` the level's weight, `kk` the cap index). -/
theorem run_bitPow (X : Array Val) (one : ℕ) (zp : ℕ → ℕ) (nb : ℕ) (rdc : CapRead) (z W : K) (kk : ℕ)
    (ho : one < X.size) (h1 : rd X one = .k 1)
    (hzp : ∀ t < nb, zp t < X.size ∧ rd X (zp t) = .k (z ^ 2 ^ t))
    (hk : rdc.k < X.size) (hkv : rd X rdc.k = .n kk) (hw : rdc.w < X.size) (hwv : rd X rdc.w = .k W) :
    pureRun impl κ inp (bitPowOps one zp nb rdc X.size) X [] =
      some ((List.range nb).flatMap (bitVals z W kk), true) := by
  have hP := P4a.pureRun_flatMap impl κ inp X [] (fun t => [Op.bitOf rdc.k t,
    Op.selectHalf (X.size + 3 * t) one (zp t),
    Op.mulK (if t = 0 then rdc.w else X.size + 3 * t - 1) (X.size + 3 * t + 1)]) (bitVals z W kk) nb ?_
  · simpa [bitPowOps] using hP
  intro t ht
  rw [List.nil_append]
  set P := (List.range t).flatMap (bitVals z W kk) with hPd
  have hPl : P.length = 3 * t := flatMap_length (g := bitVals z W kk) (fun _ => rfl) t
  have hX : (X ++ P.toArray).size = X.size + 3 * t := by simp [hPl]
  have rl : ∀ (V : List Val) {i : ℕ}, i < X.size → rd (X ++ P.toArray ++ V.toArray) i = rd X i :=
    fun V i hi => by rw [rd_app_left _ _ (by rw [hX]; omega), rd_app_left _ _ hi]
  refine pureRun_vals impl κ inp _ _ [[.bit (kk.testBit t)],
    [if kk.testBit t then .k (z ^ 2 ^ t) else .k 1], [.k (W * z ^ (kk % 2 ^ (t + 1)))]] [] rfl
    fun j hj => ?_
  simp only [List.length_cons, List.length_nil] at hj
  interval_cases j
  · show evalOp impl κ inp (X ++ P.toArray ++ ([] : List Val).toArray) (Op.bitOf rdc.k t) =
      .vals [.bit (kk.testBit t)] true
    simp only [evalOp, arr_app_nil]
    rw [rd_app_left _ _ hk, hkv]; rfl
  · show evalOp impl κ inp (X ++ P.toArray ++ [Val.bit (kk.testBit t)].toArray)
      (Op.selectHalf (X.size + 3 * t) one (zp t)) =
      .vals [if kk.testBit t then .k (z ^ 2 ^ t) else .k 1] true
    simp only [evalOp]
    rw [show X.size + 3 * t = (X ++ P.toArray).size + 0 by rw [hX, Nat.add_zero], rd_app, rl _ ho, h1,
      rl _ (hzp t ht).1, (hzp t ht).2]
    simp only [List.getD_cons_zero, Val.toBit]
  · show evalOp impl κ inp (X ++ P.toArray ++ [Val.bit (kk.testBit t),
        if kk.testBit t then Val.k (z ^ 2 ^ t) else Val.k 1].toArray)
      (Op.mulK (if t = 0 then rdc.w else X.size + 3 * t - 1) (X.size + 3 * t + 1)) =
      .vals [.k (W * z ^ (kk % 2 ^ (t + 1)))] true
    simp only [evalOp]
    rw [show X.size + 3 * t + 1 = (X ++ P.toArray).size + 1 by rw [hX], rd_app]
    simp only [List.getD_cons_succ, List.getD_cons_zero]
    have hprev : (rd (X ++ P.toArray ++ [Val.bit (kk.testBit t),
        if kk.testBit t then Val.k (z ^ 2 ^ t) else Val.k 1].toArray)
        (if t = 0 then rdc.w else X.size + 3 * t - 1)).toK = W * z ^ (kk % 2 ^ t) := by
      by_cases h0 : t = 0
      · rw [if_pos h0, rl _ hw, hwv, h0]; simp [Val.toK, Nat.mod_one]
      · rw [if_neg h0, rd_app_left _ _ (by rw [hX]; omega),
          show X.size + 3 * t - 1 = X.size + (3 * (t - 1) + 2) by omega, rd_app,
          flatMap_getD (g := bitVals z W kk) (fun _ => rfl) (show t - 1 < t by omega)
            (show 2 < 3 by norm_num)]
        simp only [bitVals, List.getD_cons_succ, List.getD_cons_zero, Val.toK]
        rw [show t - 1 + 1 = t by omega]
    rw [hprev, mul_assoc, ← pow_mod_two_pow_succ]
    by_cases hb : kk.testBit t <;> simp [hb, Val.toK]

/-- One read's MAC values: `D_r`'s halves, `ζ^r·lo`, the `lo` sum, `ζ^r·hi`, the `hi` sum, `ζ^r·zk`,
the `z` sum. -/
def macDVals (D : Digest) (P ZK SL SH SZ : K) : List Val :=
  [.f (T4.loD D), .f (T4.hiD D), .k (K.smulF (T4.loD D) P), .k (SL + K.smulF (T4.loD D) P),
   .k (K.smulF (T4.hiD D) P), .k (SH + K.smulF (T4.hiD D) P), .k (P * ZK), .k (SZ + P * ZK)]

/-- **One read's MACs** (`macDOps`). -/
theorem run_macD (X : Array Val) (rdc : CapRead) (p zk aL aH aZ : ℕ) (D : Digest) (P ZK SL SH SZ : K)
    (hd : rdc.d < X.size) (hdv : rd X rdc.d = .d D) (hp : p < X.size) (hpv : rd X p = .k P)
    (hz : zk < X.size) (hzv : rd X zk = .k ZK) (hL : aL < X.size) (hLv : rd X aL = .k SL)
    (hH : aH < X.size) (hHv : rd X aH = .k SH) (hZ : aZ < X.size) (hZv : rd X aZ = .k SZ) :
    pureRun impl κ inp (macDOps rdc p zk aL aH aZ X.size) X [] =
      some (macDVals D P ZK SL SH SZ, true) := by
  refine pureRun_vals impl κ inp X _ [[.f (T4.loD D), .f (T4.hiD D)], [.k (K.smulF (T4.loD D) P)],
    [.k (SL + K.smulF (T4.loD D) P)], [.k (K.smulF (T4.hiD D) P)], [.k (SH + K.smulF (T4.hiD D) P)],
    [.k (P * ZK)], [.k (SZ + P * ZK)]] [] rfl fun j hj => ?_
  simp only [macDOps, List.length_cons, List.length_nil] at hj
  interval_cases j <;>
    simp only [macDOps, List.getElem_cons_succ, List.getElem_cons_zero, List.take_succ_cons, List.take_zero,
      List.flatten_cons, List.flatten_nil, List.append_nil, List.nil_append, List.cons_append,
      List.getD_cons_succ, List.getD_cons_zero, evalOp, arr_app_nil] <;>
    simp only [rd_app_left _ _ hd, hdv, rd_app_left _ _ hp, hpv, rd_app_left _ _ hz, hzv,
      rd_app_left _ _ hL, hLv, rd_app_left _ _ hH, hHv, rd_app_left _ _ hZ, hZv, rd_app,
      List.getD_cons_succ, List.getD_cons_zero, Val.toK, Val.toF, Val.toD, rd_app0, T4.loD, T4.hiD]

/-- One cap entry's MAC values: `A_k`, the entry's halves, `A_k·lo`, the `lo` sum, `A_k·hi`, the `hi`
sum, `A_k·z^k`, the `z` sum. -/
def macAVals (A : K) (clo chi : F) (ZK SL SH SZ : K) : List Val :=
  [.k A, .f clo, .f chi, .k (K.smulF clo A), .k (SL + K.smulF clo A), .k (K.smulF chi A),
   .k (SH + K.smulF chi A), .k (A * ZK), .k (SZ + A * ZK)]

/-- **One cap entry's MACs** (`macAOps`; π read at absolute offsets). -/
theorem run_macA (X : Array Val) (aO cO k zk sL sH sZ : ℕ) (ZK SL SH SZ : K)
    (hz : zk < X.size) (hzv : rd X zk = .k ZK) (hL : sL < X.size) (hLv : rd X sL = .k SL)
    (hH : sH < X.size) (hHv : rd X sH = .k SH) (hZ : sZ < X.size) (hZv : rd X sZ = .k SZ) :
    pureRun impl κ inp (macAOps aO cO k zk sL sH sZ X.size) X [] =
      some (macAVals (K.ofBytes (bytesAt inp.π (aO + 32 * k) 32)) (F.ofBytes (bytesAt inp.π (cO + 32 * k) 16))
        (F.ofBytes (bytesAt inp.π (cO + 32 * k + 16) 16)) ZK SL SH SZ, true) := by
  refine pureRun_vals impl κ inp X _ [[.k (K.ofBytes (bytesAt inp.π (aO + 32 * k) 32))],
    [.f (F.ofBytes (bytesAt inp.π (cO + 32 * k) 16))], [.f (F.ofBytes (bytesAt inp.π (cO + 32 * k + 16) 16))],
    [.k (K.smulF (F.ofBytes (bytesAt inp.π (cO + 32 * k) 16)) (K.ofBytes (bytesAt inp.π (aO + 32 * k) 32)))],
    [.k (SL + K.smulF (F.ofBytes (bytesAt inp.π (cO + 32 * k) 16)) (K.ofBytes (bytesAt inp.π (aO + 32 * k) 32)))],
    [.k (K.smulF (F.ofBytes (bytesAt inp.π (cO + 32 * k + 16) 16)) (K.ofBytes (bytesAt inp.π (aO + 32 * k) 32)))],
    [.k (SH + K.smulF (F.ofBytes (bytesAt inp.π (cO + 32 * k + 16) 16))
      (K.ofBytes (bytesAt inp.π (aO + 32 * k) 32)))],
    [.k (K.ofBytes (bytesAt inp.π (aO + 32 * k) 32) * ZK)],
    [.k (SZ + K.ofBytes (bytesAt inp.π (aO + 32 * k) 32) * ZK)]] [] rfl fun j hj => ?_
  simp only [macAOps, List.length_cons, List.length_nil] at hj
  interval_cases j <;>
    simp only [macAOps, List.getElem_cons_succ, List.getElem_cons_zero, List.take_succ_cons, List.take_zero,
      List.flatten_cons, List.flatten_nil, List.append_nil, List.nil_append, List.cons_append,
      List.getD_cons_succ, List.getD_cons_zero, evalOp, arr_app_nil, absOff_zero] <;>
    simp only [rd_app_left _ _ hz, hzv, rd_app_left _ _ hL, hLv, rd_app_left _ _ hH, hHv,
      rd_app_left _ _ hZ, hZv, rd_app, rd_app0, List.getD_cons_succ, List.getD_cons_zero, Val.toK, Val.toF]

/-- The cap check's head values: `1`, `0`, `ζ`, `z`, `z^{2^{t+1}}` (`t < 9`), `z^{offᵢ₊₁}` (`i < 4`). -/
def headVals (ζ z : K) : List Val :=
  [.k 1, .k 0, .k ζ, .k z] ++ ((List.range 9).flatMap fun t => [Val.k (z ^ 2 ^ (t + 1))]) ++
    ((List.range 4).flatMap fun i => [Val.k (z ^ T4.cOff (i + 1))])

theorem headVals_length (ζ z : K) : (headVals ζ z).length = 17 := by
  simp [headVals, flatMap_length (g := fun t => [Val.k (z ^ 2 ^ (t + 1))]) (w := 1) (fun _ => rfl),
    flatMap_length (g := fun i => [Val.k (z ^ T4.cOff (i + 1))]) (w := 1) (fun _ => rfl)]

theorem run_head0 (X : Array Val) (zr zzr : ℕ) (aζ az : Digest) (hzr : zr < X.size)
    (hzv : rd X zr = .d aζ) (hzzr : zzr < X.size) (hzzv : rd X zzr = .d az) :
    pureRun impl κ inp [Op.const (fun _ => Val.k 1), Op.const (fun _ => Val.k 0), Op.chK zr, Op.chK zzr] X [] =
      some ([.k 1, .k 0, .k (chK aζ), .k (chK az)], true) := by
  refine pureRun_vals impl κ inp X _ [[.k 1], [.k 0], [.k (chK aζ)], [.k (chK az)]] [] rfl fun j hj => ?_
  simp only [List.length_cons, List.length_nil] at hj
  interval_cases j <;>
    simp only [List.getElem_cons_succ, List.getElem_cons_zero, List.take_succ_cons, List.take_zero,
      List.flatten_cons, List.flatten_nil, List.append_nil, List.nil_append, List.cons_append,
      List.getD_cons_succ, List.getD_cons_zero, evalOp, arr_app_nil, rd_app_left _ _ hzr, hzv,
      rd_app_left _ _ hzzr, hzzv, Val.toD]

/-- The squarings `z^{2^{t+1}}` (`t < 9`). -/
theorem run_sq (X0 : Array Val) (b : ℕ) (z : K) (hs : X0.size = b + 4) (h3 : rd X0 (b + 3) = .k z) :
    pureRun impl κ inp ((List.range 9).map (fun t => Op.mulK (b + 3 + t) (b + 3 + t))) X0 [] =
      some ((List.range 9).flatMap fun t => [Val.k (z ^ 2 ^ (t + 1))], true) := by
  rw [List.map_eq_flatMap]
  have hP := P4a.pureRun_flatMap impl κ inp X0 [] (fun t => [Op.mulK (b + 3 + t) (b + 3 + t)])
    (fun t => [Val.k (z ^ 2 ^ (t + 1))]) 9 ?_
  · simpa using hP
  intro t ht
  rw [List.nil_append]
  refine pureRun_vals impl κ inp _ _ [[Val.k (z ^ 2 ^ (t + 1))]] [] rfl fun j hj => ?_
  have hj0 : j = 0 := by simpa using hj
  subst hj0
  simp only [List.getElem_cons_zero, List.take_zero, List.flatten_nil, List.append_nil, evalOp,
    List.getD_cons_zero, arr_app_nil]
  have hr : rd (X0 ++ ((List.range t).flatMap fun t => [Val.k (z ^ 2 ^ (t + 1))]).toArray)
      (b + 3 + t) = .k (z ^ 2 ^ t) := by
    rcases Nat.eq_zero_or_pos t with rfl | ht0
    · rw [rd_app_left _ _ (by omega), Nat.add_zero, h3, pow_zero, pow_one]
    · rw [show b + 3 + t = X0.size + (t - 1) by omega, rd_app,
        flatMap1_getD (fun t => Val.k (z ^ 2 ^ (t + 1))) (show t - 1 < t by omega)]
      rw [show t - 1 + 1 = t by omega]
  rw [hr]
  simp only [Val.toK, ← pow_add, ← two_mul, ← pow_succ']

/-- The level weights `z^{offᵢ₊₁}` (`i < 4`). -/
theorem run_wts (X1 : Array Val) (b : ℕ) (z : K) (hs : X1.size = b + 13) (h1 : rd X1 b = .k 1)
    (hzp : ∀ t ≤ 9, rd X1 (b + 3 + t) = .k (z ^ 2 ^ t)) :
    pureRun impl κ inp ((List.range 4).map (fun i => Op.mulK (if i = 0 then b else b + 4 + 9 + (i - 1))
        (b + 3 + (seq4.lv i).cap))) X1 [] =
      some ((List.range 4).flatMap fun i => [Val.k (z ^ T4.cOff (i + 1))], true) := by
  rw [List.map_eq_flatMap]
  have hP := P4a.pureRun_flatMap impl κ inp X1 [] (fun i => [Op.mulK (if i = 0 then b else b + 4 + 9 + (i - 1))
      (b + 3 + (seq4.lv i).cap)]) (fun i => [Val.k (z ^ T4.cOff (i + 1))]) 4 ?_
  · simpa using hP
  intro i hi
  rw [List.nil_append]
  refine pureRun_vals impl κ inp _ _ [[Val.k (z ^ T4.cOff (i + 1))]] [] rfl fun j hj => ?_
  have hj0 : j = 0 := by simpa using hj
  subst hj0
  simp only [List.getElem_cons_zero, List.take_zero, List.flatten_nil, List.append_nil, evalOp,
    List.getD_cons_zero, arr_app_nil]
  obtain ⟨-, -, hstep, -, hc9⟩ := T4.ladder_vals (show i < 5 by omega)
  have hc : rd (X1 ++ ((List.range i).flatMap fun i => [Val.k (z ^ T4.cOff (i + 1))]).toArray)
      (b + 3 + (seq4.lv i).cap) = .k (z ^ 2 ^ (seq4.lv i).cap) := by
    rw [rd_app_left _ _ (by omega), hzp _ hc9]
  have hw : rd (X1 ++ ((List.range i).flatMap fun i => [Val.k (z ^ T4.cOff (i + 1))]).toArray)
      (if i = 0 then b else b + 4 + 9 + (i - 1)) = .k (z ^ T4.cOff i) := by
    by_cases h0 : i = 0
    · rw [if_pos h0, rd_app_left _ _ (by omega), h1, h0, T4.cOff_vals.1, pow_zero]
    · rw [if_neg h0, show b + 4 + 9 + (i - 1) = X1.size + (i - 1) by omega, rd_app,
        flatMap1_getD (fun i => Val.k (z ^ T4.cOff (i + 1))) (show i - 1 < i by omega)]
      rw [show i - 1 + 1 = i by omega]
  rw [hc, hw]
  simp only [Val.toK, ← pow_add, hstep]

/-- **The cap check's head** (`capChkOps`' first 17 ops at `seq4`). -/
theorem run_head (X : Array Val) (zr zzr : ℕ) (aζ az : Digest) (hzr : zr < X.size)
    (hzv : rd X zr = .d aζ) (hzzr : zzr < X.size) (hzzv : rd X zzr = .d az) :
    pureRun impl κ inp ([Op.const (fun _ => Val.k 1), Op.const (fun _ => Val.k 0), Op.chK zr, Op.chK zzr] ++
      (List.range 9).map (fun t => Op.mulK (X.size + 3 + t) (X.size + 3 + t)) ++
      (List.range 4).map (fun i => Op.mulK (if i = 0 then X.size else X.size + 4 + 9 + (i - 1))
        (X.size + 3 + (seq4.lv i).cap))) X [] = some (headVals (chK aζ) (chK az), true) := by
  have h0 := run_head0 impl κ inp X zr zzr aζ az hzr hzv hzzr hzzv
  have h1 := run_sq impl κ inp (X ++ ([Val.k 1, .k 0, .k (chK aζ), .k (chK az)] : List Val).toArray)
    X.size (chK az) (by simp) (by rw [rd_app]; rfl)
  have hs1 : (X ++ ([Val.k 1, .k 0, .k (chK aζ), .k (chK az)] : List Val).toArray ++
      ((List.range 9).flatMap fun t => [Val.k (chK az ^ 2 ^ (t + 1))]).toArray).size = X.size + 13 := by
    simp only [Array.size_append, List.size_toArray, List.length_cons, List.length_nil,
      flatMap_length (g := fun t => [Val.k (chK az ^ 2 ^ (t + 1))]) (w := 1) (fun _ => rfl)]
  have h2 := run_wts impl κ inp _ X.size (chK az) hs1 (by
      rw [rd_app_left _ _ (by simp), rd_app0]; rfl) (fun t ht => by
      rcases Nat.eq_zero_or_pos t with rfl | ht0
      · rw [rd_app_left _ _ (by simp), Nat.add_zero, rd_app]; simp
      · rw [show X.size + 3 + t = (X ++ ([Val.k 1, .k 0, .k (chK aζ), .k (chK az)] : List Val).toArray).size +
            (t - 1) by simp; omega, rd_app,
          flatMap1_getD (fun t => Val.k (chK az ^ 2 ^ (t + 1))) (show t - 1 < 9 by omega)]
        rw [show t - 1 + 1 = t by omega])
  rw [app_app] at h2
  have := pureRun_seq impl κ inp (pureRun_seq impl κ inp h0 h1) h2
  rw [Bool.and_self, Bool.and_self] at this
  rw [headVals]
  exact this

/-! ### The register families over all reads and entries -/

instance : Inhabited CapRead := ⟨⟨0, 0, 0⟩⟩

theorem zipIdx_flatMap {β : Type} (l : List CapRead) (F : CapRead → ℕ → List β) :
    l.zipIdx.flatMap (fun x => F x.1 x.2) = (List.range l.length).flatMap (fun r => F (l.getD r default) r) := by
  induction l using List.reverseRecOn with
  | nil => rfl
  | append_singleton l a ih =>
    rw [List.zipIdx_append, List.flatMap_append, ih, List.length_append, List.length_singleton,
      List.range_succ, List.flatMap_append]
    congr 1
    · refine List.flatMap_congr fun r hr => ?_
      rw [List.getD_append _ _ _ _ (List.mem_range.1 hr)]
    · simp [List.getD_append_right]

/-- **Every read's bit power** (`bitPowOps` over the reads, stride `3·nb`). -/
theorem run_bitPows (X : Array Val) (one : ℕ) (zp : ℕ → ℕ) (nb : ℕ) (rds : List CapRead) (z : K)
    (W : ℕ → K) (Kv : ℕ → ℕ) (ho : one < X.size) (h1 : rd X one = .k 1)
    (hzp : ∀ t < nb, zp t < X.size ∧ rd X (zp t) = .k (z ^ 2 ^ t))
    (hr : ∀ r < rds.length, (rds.getD r default).k < X.size ∧ rd X (rds.getD r default).k = .n (Kv r) ∧
      (rds.getD r default).w < X.size ∧ rd X (rds.getD r default).w = .k (W r)) :
    pureRun impl κ inp (rds.zipIdx.flatMap fun x => bitPowOps one zp nb x.1 (X.size + 3 * nb * x.2)) X [] =
      some ((List.range rds.length).flatMap fun r => (List.range nb).flatMap (bitVals z (W r) (Kv r)), true) := by
  rw [zipIdx_flatMap rds (fun a r => bitPowOps one zp nb a (X.size + 3 * nb * r))]
  have hP := P4a.pureRun_flatMap impl κ inp X []
    (fun r => bitPowOps one zp nb (rds.getD r default) (X.size + 3 * nb * r))
    (fun r => (List.range nb).flatMap (bitVals z (W r) (Kv r))) rds.length ?_
  · simpa using hP
  intro r hrl
  rw [List.nil_append]
  set P := (List.range r).flatMap fun r => (List.range nb).flatMap (bitVals z (W r) (Kv r)) with hPd
  have hPl : P.length = 3 * nb * r := by
    rw [hPd, flatMap_length (w := 3 * nb) (fun r' => by
      rw [flatMap_length (g := bitVals z (W r') (Kv r')) (w := 3) (fun _ => rfl)]) r]
  have hsz : (X ++ P.toArray).size = X.size + 3 * nb * r := by simp [hPl]
  obtain ⟨hk, hkv, hw, hwv⟩ := hr r hrl
  rw [← hsz]
  have hle : X.size ≤ (X ++ P.toArray).size := by rw [hsz]; omega
  exact run_bitPow impl κ inp _ one zp nb _ z (W r) (Kv r) (lt_of_lt_of_le ho hle)
    (by rw [rd_app_left _ _ ho, h1]) (fun t ht => ⟨lt_of_lt_of_le (hzp t ht).1 hle,
      by rw [rd_app_left _ _ (hzp t ht).1, (hzp t ht).2]⟩)
    (lt_of_lt_of_le hk hle) (by rw [rd_app_left _ _ hk, hkv]) (lt_of_lt_of_le hw hle)
    (by rw [rd_app_left _ _ hw, hwv])

/-- The running `lo`, `hi`, `z` sums of the reads' MACs. -/
def sumLo (D : ℕ → Digest) (P : ℕ → K) (r : ℕ) : K := ∑ r' ∈ range r, K.smulF (T4.loD (D r')) (P r')
def sumHi (D : ℕ → Digest) (P : ℕ → K) (r : ℕ) : K := ∑ r' ∈ range r, K.smulF (T4.hiD (D r')) (P r')
def sumZ (P ZK : ℕ → K) (r : ℕ) : K := ∑ r' ∈ range r, P r' * ZK r'

theorem sumLo_succ (D : ℕ → Digest) (P : ℕ → K) (r : ℕ) :
    sumLo D P (r + 1) = sumLo D P r + K.smulF (T4.loD (D r)) (P r) := Finset.sum_range_succ _ _
theorem sumHi_succ (D : ℕ → Digest) (P : ℕ → K) (r : ℕ) :
    sumHi D P (r + 1) = sumHi D P r + K.smulF (T4.hiD (D r)) (P r) := Finset.sum_range_succ _ _
theorem sumZ_succ (P ZK : ℕ → K) (r : ℕ) : sumZ P ZK (r + 1) = sumZ P ZK r + P r * ZK r :=
  Finset.sum_range_succ _ _

/-- **Every read's MACs** (`macDOps`, stride 8; the sums start at the zero register `z0`). -/
theorem run_macDs (X : Array Val) (z0 : ℕ) (rdc : ℕ → CapRead) (p zk : ℕ → ℕ) (n : ℕ)
    (D : ℕ → Digest) (P ZK : ℕ → K) (hz0 : z0 < X.size) (hz0v : rd X z0 = .k 0)
    (hr : ∀ r < n, (rdc r).d < X.size ∧ rd X (rdc r).d = .d (D r) ∧ p r < X.size ∧ rd X (p r) = .k (P r) ∧
      zk r < X.size ∧ rd X (zk r) = .k (ZK r)) :
    pureRun impl κ inp ((List.range n).flatMap fun r => macDOps (rdc r) (p r) (zk r)
      (if r = 0 then z0 else X.size + 8 * (r - 1) + 3) (if r = 0 then z0 else X.size + 8 * (r - 1) + 5)
      (if r = 0 then z0 else X.size + 8 * (r - 1) + 7) (X.size + 8 * r)) X [] =
      some ((List.range n).flatMap fun r => macDVals (D r) (P r) (ZK r) (sumLo D P r) (sumHi D P r)
        (sumZ P ZK r), true) := by
  have hP := P4a.pureRun_flatMap impl κ inp X [] (fun r => macDOps (rdc r) (p r) (zk r)
      (if r = 0 then z0 else X.size + 8 * (r - 1) + 3) (if r = 0 then z0 else X.size + 8 * (r - 1) + 5)
      (if r = 0 then z0 else X.size + 8 * (r - 1) + 7) (X.size + 8 * r))
    (fun r => macDVals (D r) (P r) (ZK r) (sumLo D P r) (sumHi D P r) (sumZ P ZK r)) n ?_
  · simpa using hP
  intro r hrl
  rw [List.nil_append]
  set Q := (List.range r).flatMap fun r => macDVals (D r) (P r) (ZK r) (sumLo D P r) (sumHi D P r)
    (sumZ P ZK r) with hQd
  have hQl : Q.length = 8 * r := flatMap_length (g := fun r => macDVals (D r) (P r) (ZK r) (sumLo D P r)
    (sumHi D P r) (sumZ P ZK r)) (fun _ => rfl) r
  have hsz : (X ++ Q.toArray).size = X.size + 8 * r := by simp [hQl]
  obtain ⟨hd, hdv, hp, hpv, hz, hzv⟩ := hr r hrl
  have hacc : ∀ j, j < 8 → (j = 3 ∨ j = 5 ∨ j = 7) →
      (if r = 0 then z0 else X.size + 8 * (r - 1) + j) < (X ++ Q.toArray).size := by
    intro j hj _; split_ifs <;> rw [hsz] <;> omega
  have hval : ∀ j, j < 8 → r ≠ 0 →
      rd (X ++ Q.toArray) (X.size + 8 * (r - 1) + j) =
        (macDVals (D (r - 1)) (P (r - 1)) (ZK (r - 1)) (sumLo D P (r - 1)) (sumHi D P (r - 1))
          (sumZ P ZK (r - 1))).getD j default := by
    intro j hj hr0
    rw [Nat.add_assoc, rd_app, hQd]
    exact flatMap_getD (g := fun r => macDVals (D r) (P r) (ZK r) (sumLo D P r) (sumHi D P r) (sumZ P ZK r))
      (w := 8) (fun _ => rfl) (show r - 1 < r by omega) hj
  have hle : X.size ≤ (X ++ Q.toArray).size := by rw [hsz]; omega
  rw [← hsz]
  refine run_macD impl κ inp _ _ _ _ _ _ _ (D r) (P r) (ZK r) (sumLo D P r) (sumHi D P r) (sumZ P ZK r)
    (lt_of_lt_of_le hd hle) (by rw [rd_app_left _ _ hd, hdv]) (lt_of_lt_of_le hp hle)
    (by rw [rd_app_left _ _ hp, hpv])
    (lt_of_lt_of_le hz hle) (by rw [rd_app_left _ _ hz, hzv]) (hacc 3 (by norm_num) (by simp)) ?_
    (hacc 5 (by norm_num) (by simp)) ?_ (hacc 7 (by norm_num) (by simp)) ?_
  all_goals
    by_cases hr0 : r = 0
    · subst hr0; simp only [if_true]; rw [rd_app_left _ _ hz0, hz0v]; simp [sumLo, sumHi, sumZ]
    · rw [if_neg hr0, hval _ (by norm_num) hr0]
      obtain ⟨r', rfl⟩ : ∃ r', r = r' + 1 := ⟨r - 1, by omega⟩
      simp [macDVals, sumLo, sumHi, sumZ, Finset.sum_range_succ]

def sumAL (A : ℕ → K) (clo : ℕ → F) (k : ℕ) : K := ∑ k' ∈ range k, K.smulF (clo k') (A k')
def sumAZ (A ZK : ℕ → K) (k : ℕ) : K := ∑ k' ∈ range k, A k' * ZK k'

theorem sumAL_succ (A : ℕ → K) (clo : ℕ → F) (k : ℕ) :
    sumAL A clo (k + 1) = sumAL A clo k + K.smulF (clo k) (A k) := Finset.sum_range_succ _ _
theorem sumAZ_succ (A ZK : ℕ → K) (k : ℕ) : sumAZ A ZK (k + 1) = sumAZ A ZK k + A k * ZK k :=
  Finset.sum_range_succ _ _

/-- **Every cap entry's MACs** (`macAOps`, stride 9; `A_k` and the entry's halves from π). -/
theorem run_macAs (X : Array Val) (z0 aO cO : ℕ) (zk : ℕ → ℕ) (n : ℕ) (ZK : ℕ → K)
    (hz0 : z0 < X.size) (hz0v : rd X z0 = .k 0)
    (hr : ∀ k < n, zk k < X.size ∧ rd X (zk k) = .k (ZK k)) :
    pureRun impl κ inp ((List.range n).flatMap fun k => macAOps aO cO k (zk k)
      (if k = 0 then z0 else X.size + 9 * (k - 1) + 4) (if k = 0 then z0 else X.size + 9 * (k - 1) + 6)
      (if k = 0 then z0 else X.size + 9 * (k - 1) + 8) (X.size + 9 * k)) X [] =
      some ((List.range n).flatMap fun k => macAVals (K.ofBytes (bytesAt inp.π (aO + 32 * k) 32))
        (F.ofBytes (bytesAt inp.π (cO + 32 * k) 16)) (F.ofBytes (bytesAt inp.π (cO + 32 * k + 16) 16)) (ZK k)
        (sumAL (fun k => K.ofBytes (bytesAt inp.π (aO + 32 * k) 32)) (fun k => F.ofBytes (bytesAt inp.π (cO + 32 * k) 16)) k)
        (sumAL (fun k => K.ofBytes (bytesAt inp.π (aO + 32 * k) 32)) (fun k => F.ofBytes (bytesAt inp.π (cO + 32 * k + 16) 16)) k)
        (sumAZ (fun k => K.ofBytes (bytesAt inp.π (aO + 32 * k) 32)) ZK k), true) := by
  set A := fun k => K.ofBytes (bytesAt inp.π (aO + 32 * k) 32) with hA
  set clo := fun k => F.ofBytes (bytesAt inp.π (cO + 32 * k) 16) with hclo
  set chi := fun k => F.ofBytes (bytesAt inp.π (cO + 32 * k + 16) 16) with hchi
  set g := fun k => macAVals (A k) (clo k) (chi k) (ZK k) (sumAL A clo k) (sumAL A chi k) (sumAZ A ZK k) with hg
  have hP := P4a.pureRun_flatMap impl κ inp X [] (fun k => macAOps aO cO k (zk k)
      (if k = 0 then z0 else X.size + 9 * (k - 1) + 4) (if k = 0 then z0 else X.size + 9 * (k - 1) + 6)
      (if k = 0 then z0 else X.size + 9 * (k - 1) + 8) (X.size + 9 * k)) g n ?_
  · simpa using hP
  intro k hkl
  rw [List.nil_append]
  set Q := (List.range k).flatMap g with hQd
  have hQl : Q.length = 9 * k := flatMap_length (g := g) (fun _ => rfl) k
  have hsz : (X ++ Q.toArray).size = X.size + 9 * k := by simp [hQl]
  obtain ⟨hz, hzv⟩ := hr k hkl
  have hacc : ∀ j, j < 9 → (if k = 0 then z0 else X.size + 9 * (k - 1) + j) < (X ++ Q.toArray).size := by
    intro j hj; split_ifs <;> rw [hsz] <;> omega
  have hval : ∀ j, j < 9 → k ≠ 0 → rd (X ++ Q.toArray) (X.size + 9 * (k - 1) + j) = (g (k - 1)).getD j default := by
    intro j hj hk0
    rw [Nat.add_assoc, rd_app, hQd]
    exact flatMap_getD (g := g) (w := 9) (fun _ => rfl) (show k - 1 < k by omega) hj
  have hle : X.size ≤ (X ++ Q.toArray).size := by rw [hsz]; omega
  rw [← hsz]
  refine run_macA impl κ inp _ aO cO k _ _ _ _ (ZK k) (sumAL A clo k) (sumAL A chi k) (sumAZ A ZK k)
    (lt_of_lt_of_le hz hle) (by rw [rd_app_left _ _ hz, hzv]) (hacc 4 (by norm_num)) ?_ (hacc 6 (by norm_num)) ?_
    (hacc 8 (by norm_num)) ?_
  all_goals
    by_cases hk0 : k = 0
    · subst hk0; simp only [if_true]; rw [rd_app_left _ _ hz0, hz0v]; simp [sumAL, sumAZ]
    · rw [if_neg hk0, hval _ (by norm_num) hk0]
      obtain ⟨k', rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
      simp [hg, macAVals, sumAL, sumAZ, Finset.sum_range_succ]

/-- **The three asserts**: their flag is the three `K` equalities. -/
theorem run_asserts (X : Array Val) (a1 b1 a2 b2 a3 b3 : ℕ) (x1 y1 x2 y2 x3 y3 : K)
    (h1 : rd X a1 = .k x1) (h1' : rd X b1 = .k y1) (h2 : rd X a2 = .k x2) (h2' : rd X b2 = .k y2)
    (h3 : rd X a3 = .k x3) (h3' : rd X b3 = .k y3) :
    pureRun impl κ inp [Op.assertEq a1 b1 allK, Op.assertEq a2 b2 allK, Op.assertEq a3 b3 allK] X [] =
      some ([], decide (x1 = y1) && (decide (x2 = y2) && decide (x3 = y3))) := by
  simp [pureRun, evalOp, arr_app_nil, h1, h1', h2, h2', h3, h3', allK, Val.eqv]

end Run

/-! ## The reads, flat (item order) -/

/-- The level of read `r` (item order: level `i`'s reads are `rdIx i 0 … rdIx i 0 + tᵢ − 1`). -/
def lvR (r : ℕ) : ℕ :=
  if r < T4.rdIx 1 0 then 0 else if r < T4.rdIx 2 0 then 1 else if r < T4.rdIx 3 0 then 2
  else if r < T4.rdIx 4 0 then 3 else 4

/-- The query of read `r` in its level. -/
def qR (r : ℕ) : ℕ := r - T4.rdIx (lvR r) 0

theorem rd_vals4 : T4.rdIx 0 0 = 0 ∧ T4.rdIx 1 0 = 290 ∧ T4.rdIx 2 0 = 468 ∧ T4.rdIx 3 0 = 613 ∧
    T4.rdIx 4 0 = 745 ∧ T4.tq 0 = 290 ∧ T4.tq 1 = 178 ∧ T4.tq 2 = 145 ∧ T4.tq 3 = 132 ∧ T4.tq 4 = 126 := by
  unfold T4.rdIx T4.tq; rw [seq4_eq]; decide

theorem rdIx_add (i q : ℕ) : T4.rdIx i q = T4.rdIx i 0 + q := by simp [T4.rdIx]

theorem lvR_spec {r : ℕ} (hr : r < 871) :
    lvR r < 5 ∧ qR r < T4.tq (lvR r) ∧ T4.rdIx (lvR r) (qR r) = r := by
  obtain ⟨e0, e1, e2, e3, e4, t0, t1, t2, t3, t4⟩ := rd_vals4
  unfold qR lvR
  rw [e1, e2, e3, e4]
  split_ifs <;> simp only [rdIx_add _ (r - _), e0, e1, e2, e3, e4, t0, t1, t2, t3, t4] <;> omega

theorem lvR_rdIx {i q : ℕ} (hi : i < 5) (hq : q < T4.tq i) : lvR (T4.rdIx i q) = i ∧ qR (T4.rdIx i q) = q := by
  obtain ⟨e0, e1, e2, e3, e4, t0, t1, t2, t3, t4⟩ := rd_vals4
  have h : lvR (T4.rdIx i q) = i := by
    unfold lvR
    rw [rdIx_add, e1, e2, e3, e4]
    interval_cases i <;> simp only [e0, e1, e2, e3, e4, t0, t1, t2, t3, t4] at hq ⊢ <;> split_ifs <;> omega
  refine ⟨h, ?_⟩
  unfold qR; rw [h, rdIx_add]; omega

/-- **A sum over the reads in item order is `sumR`** (`rdIx` a bijection onto `[0, 871)`). -/
theorem sum_reads {M : Type*} [AddCommMonoid M] (G : ℕ → M) :
    ∑ r ∈ range 871, G r = T4.sumR fun i q => G (T4.rdIx i q) := by
  rw [T4.sumR_sigma]
  symm
  refine Finset.sum_bij' (fun x _ => T4.rdIx x.1 x.2) (fun r _ => ⟨lvR r, qR r⟩) ?_ ?_ ?_ ?_ ?_
  · rintro ⟨i, q⟩ h
    simp only [mem_sigma, mem_range] at h
    show T4.rdIx i q ∈ range 871
    exact mem_range.2 (Nat.lt_succ_of_le (T4.rdIx_le h.1 h.2))
  · intro r hr
    have := lvR_spec (mem_range.1 hr)
    simp only [mem_sigma, mem_range]; exact ⟨this.1, this.2.1⟩
  · rintro ⟨i, q⟩ h
    simp only [mem_sigma, mem_range] at h
    obtain ⟨h1, h2⟩ := lvR_rdIx h.1 h.2
    simp [h1, h2]
  · intro r hr; exact (lvR_spec (mem_range.1 hr)).2.2
  · intro _ _; rfl

theorem ranges_length {α : Type} (t : ℕ → ℕ) (f : ℕ → ℕ → α) (n : ℕ) :
    ((List.range n).flatMap fun i => (List.range (t i)).map (f i)).length = ((List.range n).map t).sum := by
  induction n with
  | zero => rfl
  | succ m ih => simp [List.range_succ, List.flatMap_append, ih]

/-- Reading a flattened list of ranges at level `i`'s query `q`. -/
theorem ranges_getD {α : Type} [Inhabited α] (t : ℕ → ℕ) (f : ℕ → ℕ → α) :
    ∀ n i q, i < n → q < t i →
      ((List.range n).flatMap fun i => (List.range (t i)).map (f i)).getD
        (((List.range i).map t).sum + q) default = f i q
  | 0, _, _, hi, _ => absurd hi (Nat.not_lt_zero _)
  | n + 1, i, q, hi, hq => by
    have hlen : ∀ m, ((List.range m).flatMap fun i => (List.range (t i)).map (f i)).length =
        ((List.range m).map t).sum := by
      intro m; induction m with
      | zero => rfl
      | succ m ih => simp [List.range_succ, List.flatMap_append, ih]
    rw [List.range_succ, List.flatMap_append]
    by_cases hin : i < n
    · rw [List.getD_append _ _ _ _ (by
        rw [hlen]
        have : ((List.range (i + 1)).map t).sum ≤ ((List.range n).map t).sum := by
          have mono : ∀ m k, ((List.range m).map t).sum ≤ ((List.range (m + k)).map t).sum := by
            intro m k; induction k with
            | zero => rfl
            | succ k ih => rw [← Nat.add_assoc, List.range_succ, List.map_append, List.sum_append]; omega
          have := mono (i + 1) (n - (i + 1)); rwa [show i + 1 + (n - (i + 1)) = n by omega] at this
        rw [List.range_succ, List.map_append, List.sum_append] at this
        simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil] at this
        omega)]
      exact ranges_getD t f n i q hin hq
    · have : i = n := by omega
      subst this
      rw [List.getD_append_right _ _ _ _ (by rw [hlen]; omega), hlen, Nat.add_sub_cancel_left]
      simp [hq]


/-! ## The whole cap check -/

section Main
variable (impl : OpImpl) (κ : Kind) (inp : Input)

theorem zipIdx_flatMap' {β : Type} (l : List CapRead) (G : CapRead × ℕ → List β) :
    l.zipIdx.flatMap G = (List.range l.length).flatMap (fun r => G (l.getD r default, r)) :=
  zipIdx_flatMap l fun a r => G (a, r)

theorem rd_pre (X : Array Val) (A B : List Val) {i : ℕ} (hi : i < A.length) :
    rd (X ++ (A ++ B).toArray) (X.size + i) = A.getD i default := by
  rw [rd_app, List.getD_append _ _ _ _ hi]

theorem rd_seg (X : Array Val) (A B C : List Val) {j : ℕ} (hj : j < B.length) :
    rd (X ++ (A ++ B ++ C).toArray) (X.size + A.length + j) = B.getD j default := by
  rw [Nat.add_assoc, rd_app, List.append_assoc, List.getD_append_right _ _ _ _ (by omega),
    Nat.add_sub_cancel_left, List.getD_append _ _ _ _ hj]

theorem headVals_getD (ζ z : K) : (headVals ζ z).getD 0 default = .k 1 ∧ (headVals ζ z).getD 1 default = .k 0 ∧
    (headVals ζ z).getD 2 default = .k ζ ∧ (∀ t ≤ 9, (headVals ζ z).getD (3 + t) default = .k (z ^ 2 ^ t)) ∧
    ∀ i < 5, (headVals ζ z).getD (if i = 0 then 0 else 13 + (i - 1)) default = .k (z ^ T4.cOff i) := by
  have hl9 : ((List.range 9).flatMap fun t => [Val.k (z ^ 2 ^ (t + 1))]).length = 9 :=
    by simpa using flatMap_length (g := fun t => [Val.k (z ^ 2 ^ (t + 1))]) (w := 1) (fun _ => rfl) 9
  refine ⟨rfl, rfl, rfl, fun t ht => ?_, fun i hi => ?_⟩
  · rcases Nat.eq_zero_or_pos t with rfl | ht0
    · simp [headVals]
    · rw [headVals, List.append_assoc, List.getD_append_right _ _ _ _ (by simp; omega),
        List.getD_append _ _ _ _ (by simp [hl9]; omega)]
      simp only [List.length_cons, List.length_nil]
      rw [show 3 + t - 4 = t - 1 by omega, flatMap1_getD (fun t => Val.k (z ^ 2 ^ (t + 1))) (by omega),
        show t - 1 + 1 = t by omega]
  · by_cases h0 : i = 0
    · subst h0; simp [headVals, T4.cOff_vals.1]
    · rw [if_neg h0, headVals, List.getD_append_right _ _ _ _ (by simp [hl9])]
      simp only [List.length_append, List.length_cons, List.length_nil, hl9]
      rw [show 13 + (i - 1) - (4 + 9) = i - 1 by omega,
        flatMap1_getD (fun i => Val.k (z ^ T4.cOff (i + 1))) (by omega), show i - 1 + 1 = i by omega]

/-- `run_macDs` over the reads' `zipIdx` (as `capChkOps` writes it). -/
theorem run_macDsZ (X : Array Val) (z0 : ℕ) (rds : List CapRead) (p zk : ℕ → ℕ)
    (D : ℕ → Digest) (P ZK : ℕ → K) (hz0 : z0 < X.size) (hz0v : rd X z0 = .k 0)
    (hr : ∀ r < rds.length, (rds.getD r default).d < X.size ∧ rd X (rds.getD r default).d = .d (D r) ∧
      p r < X.size ∧ rd X (p r) = .k (P r) ∧ zk r < X.size ∧ rd X (zk r) = .k (ZK r)) :
    pureRun impl κ inp (rds.zipIdx.flatMap fun x => macDOps x.1 (p x.2) (zk x.2)
      (if x.2 = 0 then z0 else X.size + 8 * (x.2 - 1) + 3) (if x.2 = 0 then z0 else X.size + 8 * (x.2 - 1) + 5)
      (if x.2 = 0 then z0 else X.size + 8 * (x.2 - 1) + 7) (X.size + 8 * x.2)) X [] =
      some ((List.range rds.length).flatMap fun r => macDVals (D r) (P r) (ZK r) (sumLo D P r) (sumHi D P r)
        (sumZ P ZK r), true) := by
  rw [zipIdx_flatMap']
  exact run_macDs impl κ inp X z0 (fun r => rds.getD r default) p zk rds.length D P ZK hz0 hz0v hr

/-- **The batched cap check on the registers' values** (V's three asserts): with `ζ`, `z` the two
squeeze answers' `chK`, the reads' digests `Dv` and cap indices `Kv` (levels `i`, queries `q`), and `A`,
the caps from π: (I) per F half and (II). -/
theorem capChk_run (X : Array Val) (outs : Array (List Reg)) {L : List Val}
    (hrun : pureRun impl κ inp (capChkOps seq4 outs X.size) X [] = some (L, true))
    {aζ az : Digest} (hζ : (outs.getD 53 []).headD 0 - 1 < X.size)
    (hζv : rd X ((outs.getD 53 []).headD 0 - 1) = .d aζ)
    (hz : (outs.getD 55 []).headD 0 - 1 < X.size) (hzv : rd X ((outs.getD 55 []).headD 0 - 1) = .d az)
    (Y : ℕ → ℕ → ℕ) (Dv : ℕ → ℕ → Digest) (Kv : ℕ → ℕ → ℕ)
    (hY : ∀ i < 5, outs.getD (phaseIx "P1" + 5 * i + 3) [] = (List.range (T4.tq i)).map (Y i))
    (hRd : ∀ i < 5, ∀ q < T4.tq i, dOfY (seq4.lv i).sib (Y i q) < X.size ∧
      rd X (dOfY (seq4.lv i).sib (Y i q)) = .d (Dv i q) ∧ kOfY (seq4.lv i).sib (Y i q) < X.size ∧
      rd X (kOfY (seq4.lv i).sib (Y i q)) = .n (Kv i q) ∧ Kv i q < 2 ^ (seq4.lv i).cap) :
    T4.sumR (fun i q => K.smulF (T4.loD (Dv i q)) (chK aζ ^ T4.rdIx i q)) =
        ∑ k ∈ range 1536, K.smulF (F.ofBytes (bytesAt inp.π (fieldOffOf seq4 fCaps + 32 * k) 16))
          (K.ofBytes (bytesAt inp.π (fieldOffOf seq4 fA + 32 * k) 32)) ∧
      T4.sumR (fun i q => K.smulF (T4.hiD (Dv i q)) (chK aζ ^ T4.rdIx i q)) =
        ∑ k ∈ range 1536, K.smulF (F.ofBytes (bytesAt inp.π (fieldOffOf seq4 fCaps + 32 * k + 16) 16))
          (K.ofBytes (bytesAt inp.π (fieldOffOf seq4 fA + 32 * k) 32)) ∧
      ∑ k ∈ range 1536, K.ofBytes (bytesAt inp.π (fieldOffOf seq4 fA + 32 * k) 32) * chK az ^ k =
        T4.sumR (fun i q => chK aζ ^ T4.rdIx i q * chK az ^ (T4.cOff i + Kv i q)) := by
  set ζ := chK aζ with hζd
  set z := chK az with hzd
  set w : ℕ → ℕ := fun i => if i = 0 then X.size else X.size + 4 + 9 + (i - 1) with hwd
  -- the reads, flat
  set rds := capReads seq4 ⟨outs, [], #[]⟩ w with hrdsd
  have hrds : rds = (List.range 5).flatMap fun i => (List.range (T4.tq i)).map fun q =>
      (⟨dOfY (seq4.lv i).sib (Y i q), kOfY (seq4.lv i).sib (Y i q), w i⟩ : CapRead) := by
    rw [hrdsd, capReads, show nLevels = 5 from rfl]
    refine List.flatMap_congr fun i hi => ?_
    rw [ysOf, lvOuts, hY i (List.mem_range.1 hi), List.map_map]; rfl
  have hlen : rds.length = 871 := by
    rw [hrds, ranges_length, T4.tq_eq.1]; rfl
  have hget : ∀ r < 871, rds.getD r default =
      ⟨dOfY (seq4.lv (lvR r)).sib (Y (lvR r) (qR r)), kOfY (seq4.lv (lvR r)).sib (Y (lvR r) (qR r)), w (lvR r)⟩ := by
    intro r hr
    obtain ⟨h1, h2, h3⟩ := lvR_spec hr
    have := ranges_getD T4.tq (fun i q => (⟨dOfY (seq4.lv i).sib (Y i q), kOfY (seq4.lv i).sib (Y i q), w i⟩ :
      CapRead)) 5 (lvR r) (qR r) h1 h2
    rw [show ((List.range (lvR r)).map T4.tq).sum + qR r = r from h3] at this
    rw [hrds]; exact this
  unfold capChkOps at hrun
  rw [if_pos cap_consts.1] at hrun
  simp only [cap_consts.2.1, cap_consts.2.2.1, cap_consts.2.2.2.1, show nLevels = 5 from rfl] at hrun
  rw [← hwd, ← hrdsd, hlen] at hrun
  simp only [Nat.reduceSub] at hrun
  -- the head
  set V0 := headVals (chK aζ) (chK az) with hV0
  have h0 : pureRun impl κ inp ([Op.const (fun _ => Val.k 1), Op.const (fun _ => Val.k 0),
      Op.chK ((outs.getD 53 []).headD 0 - 1), Op.chK ((outs.getD 55 []).headD 0 - 1)] ++
      (List.range 9).map (fun t => Op.mulK (X.size + 3 + t) (X.size + 3 + t)) ++
      (List.range 4).map (fun i => Op.mulK (if i = 0 then X.size else X.size + 4 + 9 + (i - 1))
        (X.size + 3 + (seq4.lv i).cap))) X [] = some (V0, true) :=
    run_head impl κ inp X _ _ aζ az hζ hζv hz hzv
  obtain ⟨g0, g1, g2, gz, gw⟩ := headVals_getD (chK aζ) (chK az)
  have hl0 : V0.length = 17 := headVals_length _ _
  have rH : ∀ (B : List Val) (j : ℕ), j < 17 → rd (X ++ (V0 ++ B).toArray) (X.size + j) = V0.getD j default :=
    fun B j hj => rd_pre X _ B (by rw [hl0]; exact hj)
  have rH0 : ∀ B : List Val, rd (X ++ (V0 ++ B).toArray) X.size = .k 1 := fun B => by
    rw [show X.size = X.size + 0 from rfl, rH B 0 (by norm_num), g0]
  -- the ζ chain
  set V1 := (List.range 870).flatMap fun r => [Val.k (chK aζ ^ (r + 1))] with hV1
  have hl1 : V1.length = 870 :=
    (flatMap_length (g := fun r => [Val.k (chK aζ ^ (r + 1))]) (w := 1) (fun _ => rfl) 870).trans (one_mul _)
  have h1 : pureRun impl κ inp (powChainOps X.size (X.size + 2) 870 (X.size + 4 + 9 + 4))
      (X ++ V0.toArray) [] = some (V1, true) := by
    have := run_powChain impl κ inp (X ++ V0.toArray) X.size (X.size + 2) (chK aζ) 870 (by simp [hl0])
      (by simp [hl0]) (by rw [rd_app0, g0]) (by rw [rd_app, g2])
    rwa [show (X ++ V0.toArray).size = X.size + 4 + 9 + 4 by
      simp only [Array.size_append, List.size_toArray]; omega] at this
  -- the z chain
  set V2 := (List.range 1535).flatMap fun k => [Val.k (chK az ^ (k + 1))] with hV2
  have hl2 : V2.length = 1535 :=
    (flatMap_length (g := fun k => [Val.k (chK az ^ (k + 1))]) (w := 1) (fun _ => rfl) 1535).trans (one_mul _)
  have h2 : pureRun impl κ inp (powChainOps X.size (X.size + 3) 1535 (X.size + 4 + 9 + 4 + 870))
      (X ++ (V0 ++ V1).toArray) [] = some (V2, true) := by
    have := run_powChain impl κ inp (X ++ (V0 ++ V1).toArray) X.size (X.size + 3) (chK az) 1535
      (by simp [hl0]) (by simp [hl0]; omega) (rH0 V1) (by
        have e := gz 0 (by norm_num)
        rw [Nat.add_zero, pow_zero, pow_one] at e
        rw [rH V1 3 (by norm_num), e])
    rwa [show (X ++ (V0 ++ V1).toArray).size = X.size + 4 + 9 + 4 + 870 by
      simp only [Array.size_append, List.size_toArray, List.length_append]; omega] at this
  -- the level weights' registers
  have hwr : ∀ i < 5, w i < X.size + 17 ∧ ∀ B : List Val, rd (X ++ (V0 ++ B).toArray) (w i) =
      .k (chK az ^ T4.cOff i) := by
    intro i hi
    by_cases h0 : i = 0
    · subst h0
      refine ⟨by simp [hwd], fun B => ?_⟩
      rw [show w 0 = X.size + 0 from rfl, rH B 0 (by norm_num)]
      simpa using gw 0 (by norm_num)
    · refine ⟨by simp only [hwd, if_neg h0]; omega, fun B => ?_⟩
      rw [show w i = X.size + (13 + (i - 1)) by simp only [hwd, if_neg h0]; omega, rH B _ (by omega)]
      simpa [h0] using gw i hi
  -- the bit powers
  set W : ℕ → K := fun r => chK az ^ T4.cOff (lvR r) with hW
  set Kr : ℕ → ℕ := fun r => Kv (lvR r) (qR r) with hKr
  set V3 := (List.range rds.length).flatMap fun r => (List.range 9).flatMap (bitVals (chK az) (W r) (Kr r))
    with hV3
  have hl3 : V3.length = 27 * 871 := by
    rw [hV3, flatMap_length (w := 27) (fun r => by
      rw [flatMap_length (g := bitVals (chK az) (W r) (Kr r)) (w := 3) (fun _ => rfl)]), hlen]
  have hs3 : (X ++ (V0 ++ V1 ++ V2).toArray).size = X.size + 4 + 9 + 4 + 870 + 1535 := by
    simp only [Array.size_append, List.size_toArray, List.length_append]; omega
  have rH3 : ∀ j < 17, rd (X ++ (V0 ++ V1 ++ V2).toArray) (X.size + j) = V0.getD j default := by
    intro j hj; rw [List.append_assoc]; exact rH _ j hj
  have h3 : pureRun impl κ inp (rds.zipIdx.flatMap fun x => bitPowOps X.size (fun t => X.size + 3 + t) 9 x.1
      (X.size + 4 + 9 + 4 + 870 + 1535 + 3 * 9 * x.2)) (X ++ (V0 ++ V1 ++ V2).toArray) [] = some (V3, true) := by
    have hle : X.size + 17 ≤ (X ++ (V0 ++ V1 ++ V2).toArray).size := by rw [hs3]; omega
    have := run_bitPows impl κ inp (X ++ (V0 ++ V1 ++ V2).toArray) X.size (fun t => X.size + 3 + t) 9 rds
      (chK az) W Kr (by omega) (by rw [show X.size = X.size + 0 from rfl, rH3 0 (by norm_num), g0])
      (fun t ht => ⟨by omega, by rw [Nat.add_assoc, rH3 _ (by omega), gz t (by omega)]⟩)
      (fun r hr => by
        rw [hlen] at hr
        rw [hget r hr]
        obtain ⟨l1, l2, -⟩ := lvR_spec hr
        obtain ⟨-, -, hk, hkv, -⟩ := hRd _ l1 _ l2
        obtain ⟨hw1, hw2⟩ := hwr _ l1
        refine ⟨lt_of_lt_of_le hk (le_trans (Nat.le_add_right _ 17) hle), by rw [rd_app_left _ _ hk, hkv],
          lt_of_lt_of_le hw1 hle, ?_⟩
        rw [List.append_assoc]; exact hw2 _)
    rwa [hs3] at this
  -- the reads' MACs
  set D : ℕ → Digest := fun r => Dv (lvR r) (qR r) with hDd
  set P : ℕ → K := fun r => chK aζ ^ r with hPd
  set ZK : ℕ → K := fun r => W r * chK az ^ (Kr r % 2 ^ (8 + 1)) with hZKd
  set V4 := (List.range rds.length).flatMap fun r => macDVals (D r) (P r) (ZK r) (sumLo D P r) (sumHi D P r)
    (sumZ P ZK r) with hV4
  have hl4 : V4.length = 8 * 871 := by
    rw [hV4, flatMap_length (w := 8) (fun r => rfl), hlen]
  have hs4 : (X ++ (V0 ++ V1 ++ V2 ++ V3).toArray).size = X.size + 4 + 9 + 4 + 870 + 1535 + 3 * 9 * 871 := by
    simp only [Array.size_append, List.size_toArray, List.length_append]; omega
  have h4 : pureRun impl κ inp (rds.zipIdx.flatMap fun x => macDOps x.1 (powReg X.size (X.size + 4 + 9 + 4) x.2)
      (X.size + 4 + 9 + 4 + 870 + 1535 + 3 * 9 * x.2 + 3 * 9 - 1)
      (if x.2 = 0 then X.size + 1 else X.size + 4 + 9 + 4 + 870 + 1535 + 3 * 9 * 871 + 8 * (x.2 - 1) + 3)
      (if x.2 = 0 then X.size + 1 else X.size + 4 + 9 + 4 + 870 + 1535 + 3 * 9 * 871 + 8 * (x.2 - 1) + 5)
      (if x.2 = 0 then X.size + 1 else X.size + 4 + 9 + 4 + 870 + 1535 + 3 * 9 * 871 + 8 * (x.2 - 1) + 7)
      (X.size + 4 + 9 + 4 + 870 + 1535 + 3 * 9 * 871 + 8 * x.2)) (X ++ (V0 ++ V1 ++ V2 ++ V3).toArray) [] =
      some (V4, true) := by
    have hle : X.size + 17 ≤ (X ++ (V0 ++ V1 ++ V2 ++ V3).toArray).size := by rw [hs4]; omega
    have rH4 : ∀ j < 17, rd (X ++ (V0 ++ V1 ++ V2 ++ V3).toArray) (X.size + j) = V0.getD j default := by
      intro j hj; simp only [List.append_assoc]; exact rH _ j hj
    have := run_macDsZ impl κ inp (X ++ (V0 ++ V1 ++ V2 ++ V3).toArray) (X.size + 1) rds
      (fun r => powReg X.size (X.size + 4 + 9 + 4) r)
      (fun r => X.size + 4 + 9 + 4 + 870 + 1535 + 3 * 9 * r + 3 * 9 - 1) D P ZK (by omega)
      (by rw [rH4 1 (by norm_num), g1]) (fun r hr => by
        have hr' : r < 871 := hlen ▸ hr
        obtain ⟨l1, l2, -⟩ := lvR_spec hr'
        obtain ⟨hd, hdv, -⟩ := hRd _ l1 _ l2
        refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
        · rw [hget r hr']; exact lt_of_lt_of_le hd (le_trans (Nat.le_add_right _ 17) hle)
        · rw [hget r hr']; exact (rd_app_left _ _ hd).trans hdv
        · simp only [powReg]; split_ifs <;> rw [hs4] <;> omega
        · simp only [powReg, hPd]
          split_ifs with h0
          · have e0 := rH4 0 (by norm_num)
            rw [Nat.add_zero] at e0
            rw [e0, g0, h0, pow_zero]
          · rw [show V0 ++ V1 ++ V2 ++ V3 = V0 ++ V1 ++ (V2 ++ V3) by simp,
              show X.size + 4 + 9 + 4 + r - 1 = X.size + V0.length + (r - 1) by rw [hl0]; omega,
              rd_seg _ _ _ _ (by rw [hl1]; omega), hV1,
              flatMap1_getD (fun r => Val.k (chK aζ ^ (r + 1))) (show r - 1 < 870 by omega),
              show r - 1 + 1 = r by omega]
        · rw [hs4]; omega
        · rw [show X.size + 4 + 9 + 4 + 870 + 1535 + 3 * 9 * r + 3 * 9 - 1 =
              X.size + (V0 ++ V1 ++ V2).length + (27 * r + 26) by simp [hl0, hl1, hl2]; omega,
            show V0 ++ V1 ++ V2 ++ V3 = (V0 ++ V1 ++ V2) ++ V3 ++ [] by simp,
            rd_seg _ _ _ _ (by rw [hl3]; omega), hV3,
            flatMap_getD (g := fun r => (List.range 9).flatMap (bitVals (chK az) (W r) (Kr r))) (w := 27)
              (fun r => by rw [flatMap_length (g := bitVals (chK az) (W r) (Kr r)) (w := 3) (fun _ => rfl)])
              (show r < rds.length by omega) (show 26 < 27 by norm_num),
            show (26 : ℕ) = 3 * 8 + 2 from rfl,
            flatMap_getD (g := bitVals (chK az) (W r) (Kr r)) (w := 3) (fun _ => rfl)
              (show 8 < 9 by norm_num) (show 2 < 3 by norm_num)]
          rfl)
    rwa [hs4] at this
  -- the cap entries' MACs
  set A : ℕ → K := fun k => K.ofBytes (bytesAt inp.π (fieldOffOf seq4 fA + 32 * k) 32) with hAd
  set clo : ℕ → F := fun k => F.ofBytes (bytesAt inp.π (fieldOffOf seq4 fCaps + 32 * k) 16) with hclod
  set chi : ℕ → F := fun k => F.ofBytes (bytesAt inp.π (fieldOffOf seq4 fCaps + 32 * k + 16) 16) with hchid
  set ZA : ℕ → K := fun k => chK az ^ k with hZAd
  set V5 := (List.range 1536).flatMap fun k => macAVals (A k) (clo k) (chi k) (ZA k) (sumAL A clo k)
    (sumAL A chi k) (sumAZ A ZA k) with hV5
  have hl5 : V5.length = 9 * 1536 := by rw [hV5, flatMap_length (w := 9) (fun r => rfl)]
  have hs5 : (X ++ (V0 ++ V1 ++ V2 ++ V3 ++ V4).toArray).size =
      X.size + 4 + 9 + 4 + 870 + 1535 + 3 * 9 * 871 + 8 * 871 := by
    simp only [Array.size_append, List.size_toArray, List.length_append]; omega
  have h5 : pureRun impl κ inp ((List.range 1536).flatMap fun k => macAOps (fieldOffOf seq4 fA)
      (fieldOffOf seq4 fCaps) k (powReg X.size (X.size + 4 + 9 + 4 + 870) k)
      (if k = 0 then X.size + 1 else X.size + 4 + 9 + 4 + 870 + 1535 + 3 * 9 * 871 + 8 * 871 + 9 * (k - 1) + 4)
      (if k = 0 then X.size + 1 else X.size + 4 + 9 + 4 + 870 + 1535 + 3 * 9 * 871 + 8 * 871 + 9 * (k - 1) + 6)
      (if k = 0 then X.size + 1 else X.size + 4 + 9 + 4 + 870 + 1535 + 3 * 9 * 871 + 8 * 871 + 9 * (k - 1) + 8)
      (X.size + 4 + 9 + 4 + 870 + 1535 + 3 * 9 * 871 + 8 * 871 + 9 * k))
      (X ++ (V0 ++ V1 ++ V2 ++ V3 ++ V4).toArray) [] = some (V5, true) := by
    have rH5 : ∀ j < 17, rd (X ++ (V0 ++ V1 ++ V2 ++ V3 ++ V4).toArray) (X.size + j) = V0.getD j default := by
      intro j hj; simp only [List.append_assoc]; exact rH _ j hj
    have := run_macAs impl κ inp (X ++ (V0 ++ V1 ++ V2 ++ V3 ++ V4).toArray) (X.size + 1) (fieldOffOf seq4 fA)
      (fieldOffOf seq4 fCaps) (fun k => powReg X.size (X.size + 4 + 9 + 4 + 870) k) 1536 ZA
      (by rw [hs5]; omega) (by rw [rH5 1 (by norm_num), g1]) (fun k hk => by
        refine ⟨by simp only [powReg]; split_ifs <;> rw [hs5] <;> omega, ?_⟩
        simp only [powReg, hZAd]
        split_ifs with h0
        · have e0 := rH5 0 (by norm_num)
          rw [Nat.add_zero] at e0
          rw [e0, g0, h0, pow_zero]
        · rw [show V0 ++ V1 ++ V2 ++ V3 ++ V4 = (V0 ++ V1) ++ V2 ++ (V3 ++ V4) by simp,
            show X.size + 4 + 9 + 4 + 870 + k - 1 = X.size + (V0 ++ V1).length + (k - 1) by
              simp only [List.length_append]; omega,
            rd_seg _ _ _ _ (by rw [hl2]; omega), hV2,
            flatMap1_getD (fun k => Val.k (chK az ^ (k + 1))) (show k - 1 < 1535 by omega),
            show k - 1 + 1 = k by omega])
    rwa [hs5] at this
  -- the three asserts
  have hs6 : (X ++ (V0 ++ V1 ++ V2 ++ V3 ++ V4 ++ V5).toArray).size =
      X.size + 4 + 9 + 4 + 870 + 1535 + 3 * 9 * 871 + 8 * 871 + 9 * 1536 := by
    simp only [Array.size_append, List.size_toArray, List.length_append]; omega
  have rD : ∀ j < 8, rd (X ++ (V0 ++ V1 ++ V2 ++ V3 ++ V4 ++ V5).toArray)
      (X.size + 4 + 9 + 4 + 870 + 1535 + 3 * 9 * 871 + 8 * 870 + j) =
        (macDVals (D 870) (P 870) (ZK 870) (sumLo D P 870) (sumHi D P 870) (sumZ P ZK 870)).getD j default := by
    intro j hj
    rw [show X.size + 4 + 9 + 4 + 870 + 1535 + 3 * 9 * 871 + 8 * 870 + j =
        X.size + (V0 ++ V1 ++ V2 ++ V3).length + (8 * 870 + j) by simp only [List.length_append]; omega,
      rd_seg _ _ _ _ (by rw [hl4]; omega), hV4,
      flatMap_getD (g := fun r => macDVals (D r) (P r) (ZK r) (sumLo D P r) (sumHi D P r) (sumZ P ZK r))
        (w := 8) (fun _ => rfl) (show 870 < rds.length by omega) hj]
  have rA : ∀ j < 9, rd (X ++ (V0 ++ V1 ++ V2 ++ V3 ++ V4 ++ V5).toArray)
      (X.size + 4 + 9 + 4 + 870 + 1535 + 3 * 9 * 871 + 8 * 871 + 9 * 1535 + j) =
        (macAVals (A 1535) (clo 1535) (chi 1535) (ZA 1535) (sumAL A clo 1535) (sumAL A chi 1535)
          (sumAZ A ZA 1535)).getD j default := by
    intro j hj
    rw [show X.size + 4 + 9 + 4 + 870 + 1535 + 3 * 9 * 871 + 8 * 871 + 9 * 1535 + j =
        X.size + (V0 ++ V1 ++ V2 ++ V3 ++ V4).length + (9 * 1535 + j) by simp only [List.length_append]; omega,
      show V0 ++ V1 ++ V2 ++ V3 ++ V4 ++ V5 = (V0 ++ V1 ++ V2 ++ V3 ++ V4) ++ V5 ++ [] by simp,
      rd_seg _ _ _ _ (by rw [hl5]; omega), hV5,
      flatMap_getD (g := fun k => macAVals (A k) (clo k) (chi k) (ZA k) (sumAL A clo k) (sumAL A chi k)
        (sumAZ A ZA k)) (w := 9) (fun _ => rfl) (show 1535 < 1536 by omega) hj]
  have h6 := run_asserts impl κ inp (X ++ (V0 ++ V1 ++ V2 ++ V3 ++ V4 ++ V5).toArray)
    (if 871 = 0 then X.size + 1 else X.size + 4 + 9 + 4 + 870 + 1535 + 3 * 9 * 871 + 8 * 870 + 3)
    (if 1536 = 0 then X.size + 1 else X.size + 4 + 9 + 4 + 870 + 1535 + 3 * 9 * 871 + 8 * 871 + 9 * 1535 + 4)
    (if 871 = 0 then X.size + 1 else X.size + 4 + 9 + 4 + 870 + 1535 + 3 * 9 * 871 + 8 * 870 + 5)
    (if 1536 = 0 then X.size + 1 else X.size + 4 + 9 + 4 + 870 + 1535 + 3 * 9 * 871 + 8 * 871 + 9 * 1535 + 6)
    (if 871 = 0 then X.size + 1 else X.size + 4 + 9 + 4 + 870 + 1535 + 3 * 9 * 871 + 8 * 870 + 7)
    (if 1536 = 0 then X.size + 1 else X.size + 4 + 9 + 4 + 870 + 1535 + 3 * 9 * 871 + 8 * 871 + 9 * 1535 + 8)
    (sumLo D P 870 + K.smulF (T4.loD (D 870)) (P 870)) (sumAL A clo 1535 + K.smulF (clo 1535) (A 1535))
    (sumHi D P 870 + K.smulF (T4.hiD (D 870)) (P 870)) (sumAL A chi 1535 + K.smulF (chi 1535) (A 1535))
    (sumZ P ZK 870 + P 870 * ZK 870) (sumAZ A ZA 1535 + A 1535 * ZA 1535)
    (by rw [if_neg (by norm_num), rD 3 (by norm_num)]; simp only [macDVals, List.getD_cons_succ, List.getD_cons_zero])
    (by rw [if_neg (by norm_num), rA 4 (by norm_num)]; simp only [macAVals, List.getD_cons_succ, List.getD_cons_zero])
    (by rw [if_neg (by norm_num), rD 5 (by norm_num)]; simp only [macDVals, List.getD_cons_succ, List.getD_cons_zero])
    (by rw [if_neg (by norm_num), rA 6 (by norm_num)]; simp only [macAVals, List.getD_cons_succ, List.getD_cons_zero])
    (by rw [if_neg (by norm_num), rD 7 (by norm_num)]; simp only [macDVals, List.getD_cons_succ, List.getD_cons_zero])
    (by rw [if_neg (by norm_num), rA 8 (by norm_num)]; simp only [macAVals, List.getD_cons_succ, List.getD_cons_zero])
  -- the whole run, against `hrun`
  have hc := pureRun_seq impl κ inp (pureRun_seq impl κ inp (pureRun_seq impl κ inp (pureRun_seq impl κ inp
    (pureRun_seq impl κ inp (pureRun_seq impl κ inp h0 h1) h2) h3) h4) h5) h6
  rw [hc] at hrun
  simp only [Option.some.injEq, Prod.mk.injEq, Bool.and_true, Bool.true_and, Bool.and_eq_true,
    decide_eq_true_eq] at hrun
  obtain ⟨-, e1, e2, e3⟩ := hrun
  rw [← sumLo_succ, ← sumAL_succ] at e1
  rw [← sumHi_succ, ← sumAL_succ] at e2
  rw [← sumZ_succ, ← sumAZ_succ] at e3
  -- back to the levels
  have hconv : ∀ (G : ℕ → ℕ → K) (H : ℕ → K), (∀ i < 5, ∀ q < T4.tq i, G i q = H (T4.rdIx i q)) →
      T4.sumR G = ∑ r ∈ range 871, H r := by
    intro G H hG
    rw [sum_reads]
    unfold T4.sumR
    exact sum_congr rfl fun i hi => sum_congr rfl fun q hq => hG i (mem_range.1 hi) q (mem_range.1 hq)
  refine ⟨?_, ?_, ?_⟩
  · rw [hconv _ (fun r => K.smulF (T4.loD (D r)) (P r)) fun i hi q hq => by
      simp only [hDd, hPd, (lvR_rdIx hi hq).1, (lvR_rdIx hi hq).2, hζd]]
    exact e1
  · rw [hconv _ (fun r => K.smulF (T4.hiD (D r)) (P r)) fun i hi q hq => by
      simp only [hDd, hPd, (lvR_rdIx hi hq).1, (lvR_rdIx hi hq).2, hζd]]
    exact e2
  · rw [hconv _ (fun r => P r * ZK r) fun i hi q hq => by
      obtain ⟨-, -, -, -, hK⟩ := hRd i hi q hq
      have hc9 := (T4.ladder_vals hi).2.2.2.2
      have hm : Kv i q % 2 ^ (8 + 1) = Kv i q :=
        Nat.mod_eq_of_lt (lt_of_lt_of_le hK (Nat.pow_le_pow_right (by norm_num) hc9))
      simp only [hPd, hZKd, hW, hKr, (lvR_rdIx hi hq).1, (lvR_rdIx hi hq).2, hζd, hzd]
      rw [hm, pow_add]]
    exact e3.symm

end Main

/-! ## On an accepted run: the cap check on the log -/

section Log
variable {impl : OpImpl} {p : KindP} {inp : Input} {tr : Trace} {y : List Val × List Bool × Trace}

/-- **A one-challenge squeeze's answer register** (`CapZeta`, `CapChkZ`): its out is `[b + 1]`, register
`b` the answer. -/
theorem one_ans4 (h : SkRun4 impl p inp tr y) {n : ℕ} (hn : n < (phasesOf seq4).length)
    (hsh : (phasesOf seq4)[n].2 = .squeezes 1 .one) :
    ∃ b, (skeleton4 seq4 p).2.outs.getD n [] = [b + 1] ∧ b < (#[] ++ y.1.toArray).size ∧
      rd (#[] ++ y.1.toArray) b = .d (ansAt (fsOf tr (itemsOf seq4)) (phStart4 n)) := by
  obtain ⟨trk, M, x, hx, hb, -, hext, -, hdrop, -⟩ := phase_at4 impl p.tix inp p h.ref hn
  generalize hph : (phasesOf seq4)[n] = ph at hx hsh
  obtain ⟨name, sh⟩ := ph
  simp only at hsh; subst hsh
  simp only [refPhase4] at hx
  obtain ⟨xs, hxs, rfl⟩ := Option.map_eq_some_iff.1 hx
  obtain ⟨hl, hans⟩ := sqz_entries4 hn (by rw [hph]) (by norm_num) hxs hdrop
  dsimp only at hext
  have hsz := hext.1
  simp only [Array.size_append, List.size_toArray, List.length_append, List.length_map, hl,
    List.length_singleton] at hsz
  refine ⟨M.length, ?_, by simp at hsz ⊢; omega, ?_⟩
  · rw [skeleton4_outs seq4 p hn, hph]; simp [genPhase4, hb]
  · rw [show M.length = M.length + 0 from rfl, rd_phase4 hext (by simp [hl]),
      List.getD_append _ _ _ _ (by simp [hl])]
    obtain ⟨a, ha⟩ : ∃ a, xs.1 = [a] := List.length_eq_one_iff.1 hl
    have h0 := hans 0 (by norm_num)
    rw [ha, Nat.add_zero, List.getD_cons_zero] at h0
    rw [ha]; simp [h0]

theorem phaseIx_P1 : phaseIx "P1" = 26 := by decide

/-- **Level `i`'s reads on the skeleton's registers** (from `queries_view4`, as `ys_facts4`): Q.i's outs
`Y q`, each read's cap-index register holding `kCap` and its committed-digest register `dAt`. -/
theorem reads_view4 (h : SkRun4 impl p inp tr y) {L : Log} (hL : (L.map Prod.fst).Nodup)
    (hin : ∀ e ∈ tr, e ∈ L) (hm : p.d.m = (kindOfC (fsOf tr (itemsOf seq4))).m) {i : ℕ} (hi : i < 5) :
    ∃ bQ, (skeleton4 seq4 p).2.outs.getD (29 + 5 * i) [] =
        (List.range (T4.tq i)).map (fun q => bQ + 2 + posW4 seq4 i * q + 3) ∧
      ∀ q < T4.tq i, kOfY (seq4.lv i).sib (bQ + 2 + posW4 seq4 i * q + 3) < (#[] ++ y.1.toArray).size ∧
        rd (#[] ++ y.1.toArray) (kOfY (seq4.lv i).sib (bQ + 2 + posW4 seq4 i * q + 3)) =
          .n (T4.kCap (fsOf tr (itemsOf seq4)) i q) ∧
        dOfY (seq4.lv i).sib (bQ + 2 + posW4 seq4 i * q + 3) < (#[] ++ y.1.toArray).size ∧
        rd (#[] ++ y.1.toArray) (dOfY (seq4.lv i).sib (bQ + 2 + posW4 seq4 i * q + 3)) =
          .d (T4.dAt (fsOf tr (itemsOf seq4)) i q) := by
  set es := fsOf tr (itemsOf seq4)
  set κ := kindOfC es
  set R := #[] ++ y.1.toArray with hRd
  have hLk : CKind.lv κ i = lvOf κ.m i := rfl
  obtain ⟨hT, hsib, hcapN, hcap, hper, hper0, hell, hcol, hsq0, -⟩ := lv_facts4 (CKind.m_mem κ) hi
  rw [← hLk] at hT hsib hcapN hcap hper hper0 hell
  have hK : seq4.lvK p.d.m i = CKind.lv κ i := by rw [hm, lvK_eq4]; rfl
  obtain ⟨hC, hP2, hQ⟩ := phases4_lvl hi
  obtain ⟨hnP, eP⟩ := ph4 hP2
  obtain ⟨hnQ, eQ⟩ := ph4 hQ
  have hcQ : cAt4 seq4 p (29 + 5 * i) =
      (genPhase4 seq4 p (28 + 5 * i) ("P2", .squeezes (seq4.lv i).sq (.pos i)) (cAt4 seq4 p (28 + 5 * i))).2 := by
    rw [show 29 + 5 * i = 28 + 5 * i + 1 by ring, cAt4_succ seq4 p hnP, eP]
  have hpA : (cAt4 seq4 p (29 + 5 * i)).posAns =
      (List.range (seq4.lv i).sq).map ((cAt4 seq4 p (28 + 5 * i)).next + ·) := by
    rw [hcQ, (genPhase4_pos_ctx ..).2.1]
  obtain ⟨-, -, hans⟩ := pos_view4 h hnP (by rw [eP]) hsq0
  obtain ⟨bQ, houtQ, hbnd, hQv⟩ := queries_view4 h hL hin hnQ (by rw [eQ]) (by rw [hK]; exact hsib)
  refine ⟨bQ, by rw [houtQ], fun q hq => ?_⟩
  have hq' : q < (seq4.lv i).t := hq
  obtain ⟨-, -, hk, hd, -⟩ := hQv q hq'
  have hqp : q / (CKind.lv κ i).per < (seq4.lv i).sq :=
    lt_of_le_of_lt (Nat.div_le_div_right (by omega)) hper
  have hj : idxOf (CKind.lv κ i).logN ((rd R ((cAt4 seq4 p (29 + 5 * i)).posAns.getD
      (q / (CKind.lv κ i).per) 0)).toD) (q % (CKind.lv κ i).per) = T4.qPos κ es i q := by
    rw [hpA, List.getD_eq_getElem _ _ (by simpa using hqp), List.getElem_map, List.getElem_range,
      hans _ hqp, T4.qPos, posAt, phStart4_P2 hi]
    rfl
  simp only [hK, ← hRd] at hk hd
  simp only [hj] at hk
  have hlt : (4 + 6 * (seq4.lv i).sib + 2) * q + (4 + 6 * (seq4.lv i).sib + 2) ≤
      (4 + 6 * (seq4.lv i).sib + 2) * (seq4.lv i).t := by
    have := Nat.mul_le_mul_left (4 + 6 * (seq4.lv i).sib + 2) (show q + 1 ≤ (seq4.lv i).t by omega)
    rw [Nat.mul_succ] at this; exact this
  have hb2 : bQ + 2 + posW4 seq4 i * q + 3 + 6 * (seq4.lv i).sib + 2 < R.size := by
    rw [← hRd] at hbnd
    simp only [posW4] at hbnd ⊢
    generalize (4 + 6 * (seq4.lv i).sib + 2) * q = A at hlt ⊢
    generalize (4 + 6 * (seq4.lv i).sib + 2) * (seq4.lv i).t = B at hlt hbnd
    omega
  refine ⟨lt_of_le_of_lt (Nat.le_succ _) hb2, ?_, hb2, ?_⟩
  · rw [hk, T4.kCap, Nat.shiftRight_eq_div_pow]
  · rw [hd, absOff_zero, dAt_eq4 h hi hq]

/-- **`A`'s message** (a table certificate): `CapChk` absorbs field `fA`, all `aBytes` of it. -/
theorem aMsg4 : (fsMsgs4 seq4).getD (phStart4 54) none = some (fieldOffOf seq4 fA, aBytes seq4) := by
  rw [phStart4, fsStarts4_eq, fsMsgs4, fieldOffOf, aBytes, seq4_eq]; decide +kernel

theorem aAt_eq4 (h : SkRun4 impl p inp tr y) {k : ℕ} (hk : k < 1536) :
    T4.aAt (fsOf tr (itemsOf seq4)) k = K.ofBytes (bytesAt inp.π (fieldOffOf seq4 fA + 32 * k) 32) := by
  obtain ⟨-, -, p54, -⟩ := T4.capPh_pos
  have e1 := h.hq (phStart4 54) (by omega)
  rw [aMsg4] at e1
  simp only [qOf, show phStart4 54 ≠ 0 by omega, if_false] at e1
  have hab : aBytes seq4 = 49152 := by rw [aBytes, seq4_eq]; decide +kernel
  rw [T4.aAt, msgAt_of_q e1, bytesAt_extract_of_le inp.π (by rw [hab]; omega)]

theorem capOff4_eq (i : ℕ) : capOff4 seq4 i = 32 * T4.cOff i := by
  rw [capOff4, T4.cOff, capEntriesBelow, ← List.sum_map_mul_left]
  congr 1
  exact List.map_congr_left fun _ _ => Nat.mul_comm _ _

theorem capG_eq4 (h : SkRun4 impl p inp tr y) {k : ℕ} (hk : k < 1536) :
    T4.capG (fsOf tr (itemsOf seq4)) k = bytesAt inp.π (fieldOffOf seq4 fCaps + 32 * k) 32 := by
  obtain ⟨h1, h2, h3⟩ := T4.lvOfE_spec (show k < T4.nE by rw [T4.cOff_vals.2.2.2.2.2.2]; exact hk)
  rw [T4.capG, capDig_eq4 h h1 h3, capOff4_eq]
  congr 1
  rw [Nat.add_assoc, ← Nat.mul_add, Nat.add_sub_cancel' h2]

theorem loD_bytesAt (π : ByteArray) (o : ℕ) : T4.loD (bytesAt π o 32) = F.ofBytes (bytesAt π o 16) := by
  unfold T4.loD
  refine congrArg F.ofBytes ?_
  refine Vector.ext fun j hj => ?_
  rw [Vector.getElem_ofFn, getElem_bytesAt _ _ _ _ (by omega), getElem_bytesAt _ _ _ _ hj]

theorem hiD_bytesAt (π : ByteArray) (o : ℕ) :
    T4.hiD (bytesAt π o 32) = F.ofBytes (bytesAt π (o + 16) 16) := by
  unfold T4.hiD
  refine congrArg F.ofBytes ?_
  refine Vector.ext fun j hj => ?_
  rw [Vector.getElem_ofFn, getElem_bytesAt _ _ _ _ (by omega), getElem_bytesAt _ _ _ _ hj, Nat.add_assoc]

/-- **`capChk4` on an accepted run** (PACK-4.4 §11.5): the cap check's three asserts are V's (I) per F
half and (II) on the log's committed digests, cap indices, caps, `A`, `ζ` and `z`. -/
theorem capChk4_of_fields {P : FinP} {zh : List Reg} {Rs : ℕ → Array Val} {Ex : ℕ → Array (List Reg)}
    (hF : Fields4 impl p inp tr P y zh Rs Ex) (hS : P.S = seq4) {L : Log} (hL : (L.map Prod.fst).Nodup)
    (hin : ∀ e ∈ tr, e ∈ L) (hm : p.d.m = (kindOfC (fsOf tr (itemsOf seq4))).m) :
    T4.capChk4 (fsOf tr (itemsOf seq4)) := by
  set es := fsOf tr (itemsOf seq4)
  have h := hF.sk
  obtain ⟨Lc, hLc⟩ := hF.cap
  rw [hS, reloc_capChk] at hLc
  have hE := hF.ext 12 (by norm_num)
  -- `ζ` and `z`
  obtain ⟨h53, e53⟩ := ph4 (n := 53) (x := ("CapZeta", Sh.squeezes 1 .one)) (by rw [seq4_eq]; decide +kernel)
  obtain ⟨h55, e55⟩ := ph4 (n := 55) (x := ("CapChkZ", Sh.squeezes 1 .one)) (by rw [seq4_eq]; decide +kernel)
  obtain ⟨b53, o53, l53, r53⟩ := one_ans4 h h53 (by rw [e53])
  obtain ⟨b55, o55, l55, r55⟩ := one_ans4 h h55 (by rw [e55])
  -- the reads
  have hR : ∀ i < 5, ∃ bQ, (skeleton4 seq4 p).2.outs.getD (29 + 5 * i) [] =
        (List.range (T4.tq i)).map (fun q => bQ + 2 + posW4 seq4 i * q + 3) ∧
      ∀ q < T4.tq i, kOfY (seq4.lv i).sib (bQ + 2 + posW4 seq4 i * q + 3) < (#[] ++ y.1.toArray).size ∧
        rd (#[] ++ y.1.toArray) (kOfY (seq4.lv i).sib (bQ + 2 + posW4 seq4 i * q + 3)) = .n (T4.kCap es i q) ∧
        dOfY (seq4.lv i).sib (bQ + 2 + posW4 seq4 i * q + 3) < (#[] ++ y.1.toArray).size ∧
        rd (#[] ++ y.1.toArray) (dOfY (seq4.lv i).sib (bQ + 2 + posW4 seq4 i * q + 3)) = .d (T4.dAt es i q) :=
    fun i hi => reads_view4 h hL hin hm hi
  choose! bQ hbQ using hR
  have hrun := capChk_run impl p.tix inp (Rs 12) (skeleton4 seq4 p).2.outs hLc
    (aζ := ansAt es (phStart4 53)) (az := ansAt es (phStart4 55))
    (by rw [o53]; simp only [List.headD_cons, Nat.add_sub_cancel]; exact lt_of_lt_of_le l53 hE.1)
    (by rw [o53]; simp only [List.headD_cons, Nat.add_sub_cancel]; rw [hE.rd l53, r53])
    (by rw [o55]; simp only [List.headD_cons, Nat.add_sub_cancel]; exact lt_of_lt_of_le l55 hE.1)
    (by rw [o55]; simp only [List.headD_cons, Nat.add_sub_cancel]; rw [hE.rd l55, r55])
    (fun i q => bQ i + 2 + posW4 seq4 i * q + 3) (T4.dAt es) (T4.kCap es)
    (fun i hi => by rw [phaseIx_P1, show 26 + 5 * i + 3 = 29 + 5 * i by ring]; exact (hbQ i hi).1)
    (fun i hi q hq => by
      obtain ⟨k1, k2, d1, d2⟩ := (hbQ i hi).2 q hq
      exact ⟨lt_of_lt_of_le d1 hE.1, by rw [hE.rd d1, d2], lt_of_lt_of_le k1 hE.1, by rw [hE.rd k1, k2],
        T4.kCap_lt es hi q⟩)
  obtain ⟨e1, e2, e3⟩ := hrun
  have hnE : T4.nE = 1536 := T4.cOff_vals.2.2.2.2.2.2
  have hA : ∀ k ∈ range T4.nE, T4.aAt es k = K.ofBytes (bytesAt inp.π (fieldOffOf seq4 fA + 32 * k) 32) :=
    fun k hk => aAt_eq4 h (by rw [← hnE]; exact mem_range.1 hk)
  have hC : ∀ k ∈ range T4.nE, T4.capG es k = bytesAt inp.π (fieldOffOf seq4 fCaps + 32 * k) 32 :=
    fun k hk => capG_eq4 h (by rw [← hnE]; exact mem_range.1 hk)
  refine ⟨?_, ?_, ?_⟩
  · rw [T4.capIL, T4.capIR, sum_congr rfl fun k hk => by rw [hA k hk, hC k hk, loD_bytesAt], hnE]
    exact e1
  · rw [T4.capIL, T4.capIR, sum_congr rfl fun k hk => by rw [hA k hk, hC k hk, hiD_bytesAt], hnE]
    exact e2
  · rw [T4.capIIL, T4.capIIR, sum_congr rfl fun k hk => by rw [hA k hk], hnE]
    exact e3

end Log

end FR.Snd.R4

end G6_FRSoundness4R4Cap
