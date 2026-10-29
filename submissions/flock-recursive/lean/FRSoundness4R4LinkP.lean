-- New for `flock-recursive` (BLUEPRINT revision 4.1, A.9 `finP i`, `i < 4`, A.10 P3.i → P1.(i+1);
-- track R4g). The 3.x template is the `link` case of `FRSoundnessAccLog.finLog_of_run` (`kc_facts`,
-- `flag_finPLow`, `accVal_kc`, `c1_eq`).
import FRSoundness4R4Cols

/-!
# `FinRest4.link`: P1.(i+1)'s first claim is P1.i's last plus the batched folds (`i < 4`)

`finP i` for `i < 4` is 3.x's `finPLow i` (`gFinP`), unchanged by INT-8. It reads no π
(`finPLow_reloc`: the relocation is the identity), so its relation is `relPLow` on field `6 + i`'s
registers. On an accepted run every register it reads is the log's:

* P3.i's `κ_c` (`kc_view4`: `coords_view4` at phase `30 + 5i`; T4's `kcAt`);
* the fold registers `yReg4` (Q.i's outs; their values `yv4`, as `FinRest4.cols` reads them);
* P1.i's last claim and P1.(i+1)'s first (`p1_view4`; `c1_eq4`).

**`link4_of_fields`**, and `link4_seg`/`link4_node` on an accepted run of the kind's program.
-/

namespace FR.Snd.R4
open RecursionFast Rev4 Finset

theorem accOps_reloc (S : Seq) (e : Reg) :
    ∀ (ys : List Reg) (q acc b : ℕ), (accOps e ys q acc b).map (reloc S) = accOps e ys q acc b
  | [], _, _, _ => rfl
  | _ :: ys, q, _, b => by rw [accOps, List.map_append, accOps_reloc S e ys]; rfl

/-- `finPLow` reads no π: the relocation leaves it unchanged. -/
theorem finPLow_reloc (S : Seq) (i : ℕ) (fi : FinIn) (b : ℕ) :
    (finPLow i fi b).1.map (reloc S) = (finPLow i fi b).1 := by
  simp only [finPLow, List.map_append, accOps_reloc]; rfl

theorem rest_gFinP (P : FinP) {i : ℕ} (hi : i < 4) :
    (finalsOf P).rest[6 + i]'(by rw [rest_finalsOf_length]; omega) = finPLow i := by
  have hl : i < ((List.range nLevels).map (gFinP P)).length := by simp [nLevels]; omega
  simp only [Finals.rest, finalsOf, List.cons_append, show 6 + i = i + 1 + 1 + 1 + 1 + 1 + 1 by omega,
    List.getElem_cons_succ, List.nil_append]
  rw [List.getElem_append_left hl, List.getElem_map, List.getElem_range, gFinP, if_pos hi]

theorem c1_eq4 (c₀ : Log → Log → K) {i : ℕ} (hi : i < 5) (L es : Log) :
    T4.c1 c₀ i L es = rVal (T4.p1Start i) es (hEll i - 1) := by
  obtain ⟨e, he⟩ : ∃ e, hEll i = e + 1 := ⟨hEll i - 1, by have := hEll_pos hi; omega⟩
  rw [T4.c1, he, Nat.add_sub_cancel]; rfl

theorem phases4_P3 {i : ℕ} (hi : i < 5) : (phasesOf seq4)[30 + 5 * i]? = some ("P3", .squeezes 5 .coords) := by
  interval_cases i <;> rfl

theorem t_lt4 {i : ℕ} (hi : i < 5) : (seq4.lv i).t < 2 ^ 9 := by
  rw [seq4_eq]; interval_cases i <;> decide

variable {impl : OpImpl} {p : KindP} {inp : Input} {tr : Trace} {y : List Val × List Bool × Trace}

/-- **P3.i's `κ_c` by register** (3.x's `kc_facts`): `kcOf`'s nine registers hold T4's `kcAt`. -/
theorem kc_view4 (h : SkRun4 impl p inp tr y) {fi : FinIn} (hfi : fi.outs = (skeleton4 seq4 p).2.outs)
    {i : ℕ} (hi : i < 5) {R : Array Val} (hR : ExtA (#[] ++ y.1.toArray) R) :
    (∀ x ∈ kcOf fi i, x < (#[] ++ y.1.toArray).size) ∧
      (kcOf fi i).map (fv R) = (List.range 9).map (T4.kcAt (fsOf tr (itemsOf seq4)) i) := by
  obtain ⟨hn, e⟩ := ph4 (phases4_P3 hi)
  obtain ⟨b, hout, hsz, hv⟩ := coords_view4 h hn (by rw [e]) (by norm_num : 0 < 5)
  have hk : kcOf fi i = (List.range 9).map (fun x => b + 3 * (x / 2) + 1 + x % 2) := by
    rw [kcOf, lvOuts, hfi, phaseIx_P1, show 26 + 5 * i + 4 = 30 + 5 * i by ring, hout, List.drop_one,
      List.tail_cons, ← List.map_take, List.take_range, show min 9 (2 * 5) = 9 from rfl]
  rw [hk]
  rw [List.map_map]
  refine ⟨fun x hx => ?_, List.map_congr_left fun x hx => ?_⟩
  · obtain ⟨v, hv9, rfl⟩ := List.mem_map.1 hx
    have := List.mem_range.1 hv9
    show b + 3 * (v / 2) + 1 + v % 2 < _; omega
  · have hx9 := List.mem_range.1 hx
    have hp : 1 ≤ phStart4 (30 + 5 * i) := by
      rw [phStart4, fsStarts4_eq]; interval_cases i <;> decide
    show (rd R (b + 3 * (x / 2) + 1 + x % 2)).toF = _
    rw [hR.rd (by omega), hv x (by omega), T4.kcAt, coordAt, Nat.sub_add_cancel hp]; rfl

/-- **`FinRest4.link` on the fields** (`i < 4`), the folds being `yv4`. -/
theorem link4_of_fields {P : FinP} {zh : List Reg} {Rs : ℕ → Array Val} {Ex : ℕ → Array (List Reg)}
    (hF : Fields4 impl p inp tr P y zh Rs Ex) (c₀ : Log → Log → K) (L : Log) {i : ℕ} (hi : i < 4) :
    rSum (T4.p1Start (i + 1)) (fsOf tr (itemsOf seq4)) 0 = T4.c1 c₀ i L (fsOf tr (itemsOf seq4)) +
      ∑ q ∈ range (CKind.lv (kindOfC (fsOf tr (itemsOf seq4))) i).t,
        K.smulF (eqBits (T4.kcAt (fsOf tr (itemsOf seq4)) i) 9 q) (yv4 p (#[] ++ y.1.toArray) i q) := by
  set es := fsOf tr (itemsOf seq4)
  set R0 := #[] ++ y.1.toArray
  set fi : FinIn := ⟨(skeleton4 seq4 p).2.outs, zh, Ex (6 + i)⟩
  have hfi : fi.outs = (skeleton4 seq4 p).2.outs := rfl
  have hE := hF.ext (6 + i) (by omega)
  have hpos0 := skel_pos4 hF.sk
  have hpos := hF.pos (k := 6 + i) (by omega)
  obtain ⟨-, Lk, hLk, -, -⟩ := hF.fld (6 + i) (by omega)
  rw [rest_gFinP P hi, finPLow_reloc] at hLk
  obtain ⟨hkc, hkv⟩ := kc_view4 hF.sk hfi (i := i) (by omega) hE
  obtain ⟨b0, hout0, -, -, hN0, hlt0, -⟩ := p1_view4 hF.sk hfi (i := i) (by omega)
  obtain ⟨b1, hout1, -, h01, -, hlt1, -⟩ := p1_view4 hF.sk hfi (i := i + 1) (by omega)
  have hys : ysOf fi i = (skeleton4 seq4 p).2.outs.getD (29 + 5 * i) [] := by
    rw [ysOf, lvOuts, hfi, phaseIx_P1, show 26 + 5 * i + 3 = 29 + 5 * i by ring]
  have hysl : ∀ x ∈ ysOf fi i, x < R0.size := fun x hx =>
    skeleton4_out_lt p hF.sk.ref _ x (by rw [← hys]; exact hx)
  have hcN : p1ClaimN fi i < R0.size := getLastD_lt hlt0 hpos0
  have hc0 : p1Claim0 fi (i + 1) < R0.size := headD_lt hlt1 hpos0
  obtain ⟨L', hL', -⟩ := flag_finPLow (impl := impl) (κ := p.tix) (inp := inp) (r := Rs (6 + i)) (fi := fi) i
    (by
      intro x hx
      simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hx
      refine lt_of_lt_of_le ?_ hE.1
      rcases hx with (hx | hx) | hx | hx
      · exact hkc x hx
      · exact hysl x hx
      · rw [hx]; exact hcN
      · rw [hx]; exact hc0)
  have hrel := pureRun_det hLk hL'
  unfold relPLow at hrel
  rw [hE.rd hc0, h01, eqv_k] at hrel
  obtain ⟨hnQ, eQ⟩ := ph4 (phases4_lvl (i := i) (by omega)).2.2
  have hysE : (ysOf fi i).length = (seq4.lv i).t := by
    rw [hys, skeleton4_outs seq4 p hnQ, eQ, genPhase4_queries_outs, List.length_map, List.length_range]
  have hT : (CKind.lv (kindOfC es) i).t = (seq4.lv i).t :=
    (lv_facts4 (CKind.m_mem (kindOfC es)) (i := i) (by omega)).1
  have hsum : ∀ q < (seq4.lv i).t,
      (((ysOf fi i).map fun y => (rd (Rs (6 + i)) y).toK).getD q 0) = yv4 p R0 i q := by
    intro q hq'
    have hmem : (ysOf fi i).getD q 0 ∈ ysOf fi i := by
      rw [List.getD_eq_getElem _ _ (by omega)]; exact List.getElem_mem _
    have hy' : (ysOf fi i).getD q 0 = yReg4 p i q := by rw [yReg4, ← hys]
    rw [List.getD_eq_getElem _ _ (by rw [List.length_map]; omega), List.getElem_map,
      ← List.getD_eq_getElem _ 0 (by omega), hE.rd (hysl _ hmem), hy']
    rfl
  rw [← hrel, FR.vNext, kcTab, hkv, accVal_kc _ _ (by rw [List.length_map, hysE]; exact t_lt4 (by omega)),
    hE.rd hcN, hN0, c1_eq4 c₀ (by omega), List.length_map, hysE, hT,
    sum_congr rfl fun q hq => by rw [hsum q (mem_range.1 hq)]]
  rfl

/-- **`FinRest4` from the fields** with the folds `yv4` and the front's `c₀L4`: `start`
(`start4_of_fields`), `cols` (`cols4_of_run`), `link` (`link4_of_fields`) are proved; `pf0`,
`enc` (`gFinP 4`) and `fin` (`gFinPf`) are the hypotheses left (INT-8's final field). -/
theorem finRest4_of_fields (hphi : ∀ r a, r.size = 7 → impl.phiRS r a = Impl.phiRSS r a)
    {P : FinP} {zh : List Reg} {Rs : ℕ → Array Val} {Ex : ℕ → Array (List Reg)}
    (hF : Fields4 impl p inp tr P y zh Rs Ex) (hPS : P.S = seq4)
    (hnode : P.kv.node p.tix = (kindOfC (fsOf tr (itemsOf seq4))).isNode)
    (hm : p.d.m = (kindOfC (fsOf tr (itemsOf seq4))).m) {L : Log} (hb : ¬ Bad L) (hin : ∀ e ∈ tr, e ∈ L)
    (hπ : inp.π.size = piSizeOf seq4) {W₀ : Log → Log → ℕ → K}
    (hpf0 : rSum T4.pfStart (fsOf tr (itemsOf seq4)) 0 = T4.c1 P4b.c₀L4 4 L (fsOf tr (itemsOf seq4)))
    (henc : ∀ q < (CKind.lv (kindOfC (fsOf tr (itemsOf seq4))) 4).t,
      yv4 p (#[] ++ y.1.toArray) 4 q = T4.encAt (kindOfC (fsOf tr (itemsOf seq4))) 4
        (T4.finalAt (fsOf tr (itemsOf seq4))) (T4.qPos (kindOfC (fsOf tr (itemsOf seq4))) (fsOf tr (itemsOf seq4)) 4 q))
    (hfin : clR2 T4.pfStart 32 readK chK (T4.lvC P4b.c₀L4 5) L (fsOf tr (itemsOf seq4)) 7 =
      T4.wHatL W₀ L (fsOf tr (itemsOf seq4)) 4 *
        (∏ v ∈ Ico (T4.mLog (kindOfC (fsOf tr (itemsOf seq4))) 4) 7, (1 - T4.pfP (fsOf tr (itemsOf seq4)) v)) *
          mleN 7 (T4.finalAt (fsOf tr (itemsOf seq4))) (T4.pfPt (fsOf tr (itemsOf seq4)))) :
    FinRest4 W₀ P4b.c₀L4 L (fsOf tr (itemsOf seq4)) (yv4 p (#[] ++ y.1.toArray)) :=
  ⟨start4_of_fields hphi hF hPS hnode L, cols4_of_run hF.sk hb hin hπ hm,
    fun _ hi => link4_of_fields hF P4b.c₀L4 L hi, hpf0, henc, hfin⟩

end FR.Snd.R4
