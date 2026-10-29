-- New for `flock-recursive` (BLUEPRINT revision 4.1, A.4, A.9, §5.1; track R4g). The 3.x templates are
-- `FRSoundnessAccLvl`'s `pos_view` and `queries_view`.
import FRSoundness4R4PosT

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
