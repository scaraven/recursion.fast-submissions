-- G6: this module also holds the former modules `FRSoundness4R4LinkP`, `FRSoundness4R4ColsCtrl`, `FRSoundness4R4P4`, `FRSoundness4R4PfRun`, `FRSoundness4R4PfFlag` (one section each, in import order).
import FRSoundness4R4Cap
import FRVerifierImplNode4F

section G6_FRSoundness4R4LinkP

-- New for `flock-recursive` (BLUEPRINT revision 4.1, A.9 `finP i`, `i < 4`, A.10 P3.i → P1.(i+1);
-- track R4g). The 3.x template is the `link` case of `FRSoundnessAccLog.finLog_of_run` (`kc_facts`,
-- `flag_finPLow`, `accVal_kc`, `c1_eq`).

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
(`start4_of_fields`), `cols` (`cols4_of_run`), `link` (`link4_of_fields`) and (revision 4.4.1) `cap`
(`capChk4_of_fields`) are proved; `pf0`, `enc` (`gFinP 4`) and `fin` (`gFinPf`) are the hypotheses
left (INT-8's final field). -/
theorem finRest4_of_fields (hphi : ∀ r a, r.size = 7 → impl.phiRS r a = Impl.phiRSS r a)
    {P : FinP} {zh : List Reg} {Rs : ℕ → Array Val} {Ex : ℕ → Array (List Reg)}
    (hF : Fields4 impl p inp tr P y zh Rs Ex) (hPS : P.S = seq4)
    (hnode : P.kv.node p.tix = (kindOfC (fsOf tr (itemsOf seq4))).isNode)
    (hrsv : P4b.nRsv (kindOfC (fsOf tr (itemsOf seq4))) = if (P.rsvOps && P.rsv) = true then rsvN else 0)
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
  ⟨start4_of_fields hphi hF hPS hnode hrsv L, cols4_of_run hF.sk hb hin hπ hm,
    fun _ hi => link4_of_fields hF P4b.c₀L4 L hi, hpf0, henc, hfin,
    capChk4_of_fields hF hPS (by by_contra hr; exact hb (.inr (.inr (.inr hr)))) hin hm⟩

end FR.Snd.R4

end G6_FRSoundness4R4LinkP

section G6_FRSoundness4R4ColsCtrl

-- New for `flock-recursive` (BLUEPRINT revision 4.1; track R4g): controls of R4g's definitions.

/-!
# Controls for R4g (`posOps4`'s reference, the folds, the kind levels)

| Definition | Positive | Negative |
|---|---|---|
| `stepT4` | `stepT4_ok` (the expected node query: registers and a true flag at an active depth) | `stepT4_wrong` (another query: `none`), `stepT4_nil` |
| `posT4`, `posAllT4` | `posAllT4_zero` (no position: no registers, flag true); `exec_posOps4`, `posAllT4_path` | `posT4_nil`, `posT4_wrong` (a query that is not the column's: `none`) |
| `yReg4`, `yv4` | `cols4_of_run`, `link4_of_fields` (they are the folds `FinRest4` reads) | `yv4_ctl` (a register file holding `.k 1` there reads `1`, one holding `.k 0` reads `0`) |
| `seq4.lvK` vs `seq4.lv` | `lvK_eq4` (the program's kind level is T4's `lvOf`) | `lvK_ne_star4` (an `m = 30` kind's level 0 has 18 position bits, the star's 20: `posOps4` must index with the kind's) |
| `finPLow_reloc` | `finPLow_reloc` | `relocF_moves` (R4's: relocation moves a π read) |
| the op parameter `hphi` | `phiRS_segC`, `phiRS_nodeC`, `phiRS_nodeF` (INT-9's final node ops `implN4F`) | — (an equation) |
-/

namespace FR.Snd.R4
open RecursionFast Rev4 FR.Merkle

variable (inp : Input)

/-- (+) **The expected node query** at an active depth: six registers, flag true. -/
theorem stepT4_ok (sib i h j so : ℕ) (cur a : Digest) (tr : Trace) (hh : h < sib) :
    let s := bytesAt inp.π (absOff 0 so) 32
    let l := if j.testBit h then s else cur
    let r := if j.testBit h then cur else s
    stepT4 inp sib i h j so cur ((nodeQ i l r, a) :: tr) =
      some ([.d s, .bit (j.testBit h), .d l, .d r, .d a, .d a], true, a, tr) := by
  simp [stepT4, hh]

/-- (−) **Another query** fails the step. -/
theorem stepT4_wrong (sib i h j so : ℕ) (cur a : Digest) (tr : Trace) (q : ByteArray)
    (hq : q ≠ (if decide (h < sib) then nodeQ i (if j.testBit h then bytesAt inp.π (absOff 0 so) 32 else cur)
      (if j.testBit h then cur else bytesAt inp.π (absOff 0 so) 32) else nodeQ i zeroD zeroD)) :
    stepT4 inp sib i h j so cur ((q, a) :: tr) = none := by
  simp only [stepT4]; exact if_neg hq

theorem stepT4_nil (sib i h j so : ℕ) (cur : Digest) : stepT4 inp sib i h j so cur [] = none := rfl

/-- (+) **No position**: no registers, flag true, the trace untouched. -/
theorem posAllT4_zero (Lk : Level) (sL i co so capO : ℕ) (ad : ℕ → Digest) (w : Array K) (p : ℕ)
    (tr : Trace) : posAllT4 inp Lk sL i co so capO ad w 0 p tr = some ([], true, tr) := rfl

theorem posT4_nil (Lk : Level) (sL i co so capO : ℕ) (ad : ℕ → Digest) (w : Array K) (p : ℕ) :
    posT4 inp Lk sL i co so capO ad w p [] = none := rfl

/-- (−) **A query that is not the column's** fails the position. -/
theorem posT4_wrong (Lk : Level) (sL i co so capO : ℕ) (ad : ℕ → Digest) (w : Array K) (p : ℕ)
    (q : ByteArray) (a : Digest) (tr : Trace)
    (hq : q ≠ colQ i (inp.π.extract (absOff 0 (co + p * colBytes i)) (absOff 0 (co + p * colBytes i) + colBytes i))) :
    posT4 inp Lk sL i co so capO ad w p ((q, a) :: tr) = none := by
  simp only [posT4]; exact if_neg hq

/-- (−) **The kind's level is not the star's**: at `m = 30`, level 0 has 18 position bits. -/
theorem lvK_ne_star4 : (seq4.lvK 30 0).logN = 18 ∧ (seq4.lv 0).logN = 20 := by
  rw [seq4_eq]; exact ⟨rfl, rfl⟩

/-- (+/−) **`yv4` reads its register**: `.k 1` reads `1`, `.k 0` reads `0`. -/
theorem yv4_ctl (p : KindP) (i q : ℕ) :
    yv4 p ((Array.replicate (yReg4 p i q + 1) (Val.k 0)).set! (yReg4 p i q) (.k 1)) i q = 1 ∧
      yv4 p (Array.replicate (yReg4 p i q + 1) (Val.k 0)) i q = 0 := by
  constructor <;> simp [yv4, rd, Val.toK]

/-- (+) **INT-9's final node ops meet `hphi`** (`implN4F` keeps `implN4T`'s `phiRS`). -/
theorem phiRS_nodeF (fin : Finals) (lRows : List Circ.Row) (κs₀ : F) (ν : NodeKind) :
    ∀ r a, r.size = 7 → (NI4F.implN4F (fun _ => Impl.implC fin lRows κs₀) ν).phiRS r a = Impl.phiRSS r a :=
  phiRS_nodeC fin lRows κs₀ ν

end FR.Snd.R4

end G6_FRSoundness4R4ColsCtrl

section G6_FRSoundness4R4P4

-- New for `flock-recursive` (BLUEPRINT revision 4.1, A.9 `finP 4`; track R4h). The 3.x templates are
-- `FRVIRFinalsSG.flag_finP4` (`run_encOps`, `run_positions`), `FRSoundnessAccEq.encVal_eq_encAt` and
-- the `pf0`/`enc` cases of `FRSoundnessAccLog.finLog_of_run`.

/-!
# `FinRest4.pf0` and `FinRest4.enc`: `finP 4` (`gFinPTop`) on an accepted run

`gFinP P 4 = gFinPTop P` (field `10` of the rest) is 3.x's `finP 4` over `2^P.S.pf` final
elements. Its relocated run (`reloc P.S`: the final message's reads become absolute,
`fieldOffOf P.S fFinal + 32 c`) has the flag **`relP44`** (**`flag_gFinP4`**): every level-4
query's fold is `encVal4` (Horner over the final elements with the weights `tensorW p e_v`) at its
position, and Pf's first claim is P1.4's last.

* **`pf04_of_fields`**: `FinRest4.pf0` (`rSum pfStart es 0 = c1 c₀ 4 L es`, any `c₀`).
* **`encVal4_eq`** (spec side, 3.x's `encVal_eq_encAt` for any `n ≤ 7`): with `tensorW` at
  `tensorWS`, `encVal4` is `encF n m p` when the final elements agree with `m` below `2^n` and are
  zero from `2^n` to `2^7`.
* **`enc4_of_fields`**: `FinRest4.enc` for the folds `yv4`, given the final message's zero tail
  beyond `2^mLog` (the kind's exact tail check, at the end of `finPf`: `FRSoundness4R4PfRun`).
-/

namespace FR.Snd.R4
open RecursionFast Rev4 Finset

/-! ## The relocation leaves `gEncOps` unchanged -/

theorem layerOps_reloc (S : Seq) (w : Reg) (xs : List Reg) (n b : ℕ) :
    ∀ k, (layerOps w xs n b k).map (reloc S) = layerOps w xs n b k
  | 0 => rfl
  | k + 1 => by rw [layerOps, List.map_append, layerOps_reloc S w xs n b k]; rfl

theorem hornerKOps_reloc (S : Seq) (ws : List Reg) :
    ∀ v xs b, (hornerKOps ws v xs b).map (reloc S) = hornerKOps ws v xs b
  | 0, _, _ => rfl
  | v + 1, xs, b => by
    rw [hornerKOps, List.map_append, layerOps_reloc, hornerKOps_reloc S ws v]

theorem gEncOps_reloc (S : Seq) (pf : ℕ) (units fin : List Reg) (j y b : ℕ) :
    (gEncOps pf units fin j y b).map (reloc S) = gEncOps pf units fin j y b := by
  rw [gEncOps, List.map_append, List.map_append, hornerKOps_reloc, List.map_map]; rfl

theorem rest_gFinP4 (P : FinP) :
    (finalsOf P).rest[10]'(by rw [rest_finalsOf_length]; omega) = gFinPTop P := by
  have hl : 4 < ((List.range nLevels).map (gFinP P)).length := by simp [nLevels]
  simp only [Finals.rest, finalsOf, show 10 = 4 + 1 + 1 + 1 + 1 + 1 + 1 by omega,
    List.getElem_cons_succ, List.nil_append, List.cons_append]
  rw [List.getElem_append_left hl, List.getElem_map, List.getElem_range, gFinP, if_neg (by omega)]

/-! ## The flag of the relocated `finP 4` -/

/-- The final message's element `c` in `S`'s format. -/
def finV4 (S : Seq) (inp : Input) (c : ℕ) : K := K.ofBytes (bytesAt inp.π (fieldOffOf S fFinal + 32 * c) 32)

/-- `Enc(final)[p]` as `gEncOps` computes it (Horner over `2^S.pf` elements, `W_v = tensorW p e_v`). -/
def encVal4 (impl : OpImpl) (S : Seq) (inp : Input) (p : ℕ) : K :=
  hornerVal (fun v => impl.tensorW p (gUnitK S.pf v)) S.pf (finV4 S inp)

section Run
variable (impl : OpImpl) (κ : Kind) (inp : Input) (r : Array Val)

/-- **One position at level 4** over `2^pf` final elements `X` (3.x's `run_encOps`). -/
theorem run_gEncOps (pf : ℕ) (units fin : List Reg) (j y : Reg) (X : ℕ → K) (L : List Val)
    (hj : j < r.size) (hy : y < r.size)
    (hu : ∀ v < pf, units.getD v 0 < r.size + L.length ∧
      rd (r ++ L.toArray) (units.getD v 0) = .ak (gUnitK pf v))
    (hf : ∀ c < 2 ^ pf, fin.getD c 0 < r.size + L.length ∧
      rd (r ++ L.toArray) (fin.getD c 0) = .k (X c)) :
    ∃ M, pureRun impl κ inp (gEncOps pf units fin j y (r.size + L.length)) r L =
      some (L ++ M, (Val.k (hornerVal (fun v => impl.tensorW (rd r j).toN (gUnitK pf v)) pf X)).eqv
        (rd r y)) ∧ M.length = gEncW pf := by
  set tws : List Op := (List.range pf).map fun v => .tensorW j (units.getD v 0)
  have h1 := run_frozen impl κ inp r L (twVal impl r L) tws [] (fun op hop Y => by
    obtain ⟨v, hv, rfl⟩ := List.mem_map.mp hop
    have hv' := (hu v (List.mem_range.mp hv)).1
    simp only [evalOp, twVal, rd_app_left _ _ hj, FR.rd_pre r hv'])
  simp only [List.append_nil] at h1
  set M₁ := tws.map (twVal impl r L)
  have hl1 : M₁.length = pf := by simp [M₁, tws]
  have hM₁ : ∀ v < pf, rd (r ++ (L ++ M₁).toArray) ((r.size + L.length) + v) =
      .k (impl.tensorW (rd r j).toN (gUnitK pf v)) := by
    intro v hv
    rw [show (r.size + L.length) + v = r.size + (L.length + v) by omega, rd_app,
      List.getD_append_right _ _ _ _ (by omega)]
    have hu2 := (hu v hv).2
    simp only [List.getD_eq_getElem?_getD] at hu2
    simp [M₁, tws, twVal, hv, hu2]; rfl
  obtain ⟨M₂, h2, hl2, hv2⟩ :=
    run_horner impl κ inp r ((List.range pf).map ((r.size + L.length) + ·))
    (fun v => impl.tensorW (rd r j).toN (gUnitK pf v)) pf fin X (L ++ M₁)
    (fun u hu' => by
      simp only [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range hu',
        Option.map_some, Option.getD_some, List.length_append, hl1]
      exact ⟨by rw [← Nat.add_assoc]; exact Nat.add_lt_add_left hu' _, hM₁ u hu'⟩)
    (fun c hc => by
      obtain ⟨a, a'⟩ := hf c hc
      exact ⟨Nat.lt_of_lt_of_le a (by simp only [List.length_append]; omega),
        by rw [FR.rd_pre r a, a']⟩)
  have hb7 : r.size + (L ++ M₁).length = (r.size + L.length) + pf := by
    rw [List.length_append, hl1]; omega
  rw [hb7] at h2 hv2
  refine ⟨M₁ ++ M₂, ?_, by simp [hl1, hl2, gEncW]⟩
  simp only [gEncOps]
  rw [List.append_assoc, pureRun_append, h1, Option.bind_some, pureRun_append, h2,
    Option.bind_some]
  simp only [pureRun, evalOp, allK, Bool.not_true, Bool.false_or, ← List.append_assoc]
  rw [hv2, rd_app_left _ _ hy]
  simp

/-- The flag of position `q` at level 4 (`S`'s format). -/
def encFlag4 (S : Seq) (ys : List Reg) (q : ℕ) : Bool :=
  (Val.k (encVal4 impl S inp (rd r (ys.getD q 0 - 3)).toN)).eqv (rd r (ys.getD q 0))

/-- **The `T` first positions at level 4** (3.x's `run_positions`). -/
theorem run_gPositions (S : Seq) (units fin ys : List Reg) (L : List Val) (hys : ∀ y ∈ ys, y < r.size)
    (hu : ∀ v < S.pf, units.getD v 0 < r.size + L.length ∧
      rd (r ++ L.toArray) (units.getD v 0) = .ak (gUnitK S.pf v))
    (hf : ∀ c < 2 ^ S.pf, fin.getD c 0 < r.size + L.length ∧
      rd (r ++ L.toArray) (fin.getD c 0) = .k (finV4 S inp c)) :
    ∀ T ≤ ys.length, ∃ M, pureRun impl κ inp ((List.range T).flatMap fun q =>
        gEncOps S.pf units fin (ys.getD q 0 - 3) (ys.getD q 0) (r.size + L.length + gEncW S.pf * q)) r L =
      some (L ++ M, (List.range T).all (encFlag4 impl inp r S ys)) ∧ M.length = gEncW S.pf * T
  | 0, _ => ⟨[], by simp [pureRun], by simp⟩
  | T + 1, hT => by
    obtain ⟨M, hM, hl⟩ := run_gPositions S units fin ys L hys hu hf T (by omega)
    have hyT : ys.getD T 0 < r.size := by
      have := hys _ (List.getElem_mem (show T < ys.length by omega))
      simpa [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (show T < ys.length by omega)]
    obtain ⟨M', hM', hl'⟩ := run_gEncOps impl κ inp r S.pf units fin (ys.getD T 0 - 3) (ys.getD T 0)
      (finV4 S inp) (L ++ M) (Nat.lt_of_le_of_lt (Nat.sub_le _ _) hyT) hyT
      (fun v hv => by
        obtain ⟨a, a'⟩ := hu v hv
        exact ⟨Nat.lt_of_lt_of_le a (by simp), by rw [FR.rd_pre r a, a']⟩)
      (fun c hc => by
        obtain ⟨a, a'⟩ := hf c hc
        exact ⟨Nat.lt_of_lt_of_le a (by simp), by rw [FR.rd_pre r a, a']⟩)
    have hb : r.size + (L ++ M).length = r.size + L.length + gEncW S.pf * T := by
      rw [List.length_append, hl]; omega
    rw [hb] at hM'
    refine ⟨M ++ M', ?_, by simp [hl, hl']; ring⟩
    rw [List.range_succ, List.flatMap_append, pureRun_append, hM, Option.bind_some]
    simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil, hM', Option.map_some,
      List.all_append, List.all_cons, List.all_nil, Bool.and_true, List.append_assoc]
    rfl

/-- **`finP 4`'s relation at `S`** (3.x's `relP4`): every `y_q = Enc(final)[p_q]`, and Pf's first
claim is P1.4's last. -/
def relP44 (S : Seq) (fi : FinIn) : Bool :=
  (List.range (ysOf fi 4).length).all (encFlag4 impl inp r S (ysOf fi 4)) &&
    (rd r (claim0 fi "Pf")).eqv (rd r (p1ClaimN fi 4))

/-- **`flag_gFinP4`** (3.x's `flag_finP4`): the relocated `gFinPTop` asks nothing; its flag is
`relP44`. -/
theorem flag_gFinP4 (P : FinP) (fi : FinIn)
    (hin : ∀ x ∈ ysOf fi 4 ++ [claim0 fi "Pf", p1ClaimN fi 4], x < r.size) :
    ∃ L, pureRun impl κ inp ((gFinPTop P fi r.size).1.map (reloc P.S)) r [] =
      some (L, relP44 impl inp r P.S fi) := by
  simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hin
  have hys : ∀ y ∈ ysOf fi 4, y < r.size := fun y hy => hin y (.inl hy)
  have hP := hin _ (.inr (.inl rfl)); have hN := hin _ (.inr (.inr rfl))
  set A : List Op := (List.range (2 ^ P.S.pf)).map fun c => .piElemK 0 (fieldOffOf P.S fFinal + 32 * c)
  set B : List Op := (List.range P.S.pf).map fun v => .const fun _ => .ak (gUnitK P.S.pf v)
  have hAB := run_indep impl κ inp r (p4Val κ inp) (A ++ B) [] (fun op hop regs => by
    rcases List.mem_append.mp hop with h | h
    · obtain ⟨c, -, rfl⟩ := List.mem_map.mp h; rfl
    · obtain ⟨v, -, rfl⟩ := List.mem_map.mp h; rfl)
  simp only [List.nil_append] at hAB
  set L₀ := (A ++ B).map (p4Val κ inp)
  have hl0 : L₀.length = 2 ^ P.S.pf + P.S.pf := by simp [L₀, A, B]
  obtain ⟨M, hM, -⟩ := run_gPositions impl κ inp r P.S ((List.range P.S.pf).map (r.size + 2 ^ P.S.pf + ·))
    ((List.range (2 ^ P.S.pf)).map (r.size + ·)) (ysOf fi 4) L₀ hys
    (fun v hv => by
      have hg : ((List.range P.S.pf).map (r.size + 2 ^ P.S.pf + ·)).getD v 0 = r.size + 2 ^ P.S.pf + v := by
        simp [hv]
      refine ⟨?_, ?_⟩
      · rw [hg, hl0, Nat.add_assoc]; exact Nat.add_lt_add_left (Nat.add_lt_add_left hv _) _
      rw [hg, Nat.add_assoc, rd_app]
      simp only [L₀, A, B, List.getD_eq_getElem?_getD, List.map_append, List.map_map]
      rw [List.getElem?_append_right (by simp)]
      simp [hv, p4Val])
    (fun c hc => by
      have hg : ((List.range (2 ^ P.S.pf)).map (r.size + ·)).getD c 0 = r.size + c := by simp [hc]
      refine ⟨?_, ?_⟩
      · rw [hg, hl0]; exact Nat.add_lt_add_left (Nat.lt_of_lt_of_le hc (Nat.le_add_right _ _)) _
      rw [hg, rd_app]
      simp only [L₀, A, B, List.getD_eq_getElem?_getD, List.map_append, List.map_map]
      rw [List.getElem?_append_left (by simp; omega)]
      simp [hc, p4Val, finV4, absOff_zero])
    (ysOf fi 4).length le_rfl
  rw [hl0] at hM
  have hfz : fFinal < 19 := by decide
  have eA : ((List.range (2 ^ P.S.pf)).map fun c => Op.piElemK fFinal (32 * c)).map (reloc P.S) = A := by
    simp only [A, List.map_map]
    exact List.map_congr_left fun c _ => by simp only [Function.comp_apply, reloc, if_pos hfz]
  have eB : ((List.range P.S.pf).map fun v => Op.const fun _ => Val.ak (gUnitK P.S.pf v)).map (reloc P.S) = B := by
    simp only [B, List.map_map]; rfl
  have eC : ((List.range (ysOf fi 4).length).flatMap fun q =>
      gEncOps P.S.pf ((List.range P.S.pf).map (r.size + 2 ^ P.S.pf + ·)) ((List.range (2 ^ P.S.pf)).map (r.size + ·))
        ((ysOf fi 4).getD q 0 - 3) ((ysOf fi 4).getD q 0) (r.size + (2 ^ P.S.pf + P.S.pf) + gEncW P.S.pf * q)).map
      (reloc P.S) = (List.range (ysOf fi 4).length).flatMap fun q =>
      gEncOps P.S.pf ((List.range P.S.pf).map (r.size + 2 ^ P.S.pf + ·)) ((List.range (2 ^ P.S.pf)).map (r.size + ·))
        ((ysOf fi 4).getD q 0 - 3) ((ysOf fi 4).getD q 0) (r.size + (2 ^ P.S.pf + P.S.pf) + gEncW P.S.pf * q) := by
    rw [List.map_flatMap]; exact List.flatMap_congr fun q _ => gEncOps_reloc _ _ _ _ _ _ _
  refine ⟨L₀ ++ M, ?_⟩
  simp only [gFinPTop, List.map_append, List.map_cons, List.map_nil]
  rw [eA, eB, eC, ← Nat.add_assoc] at *
  rw [pureRun_append, pureRun_append, hAB, Option.bind_some, hM]
  simp only [Option.map_some, Option.bind_some, pureRun, evalOp, allK, Bool.not_true, Bool.false_or,
    rd_app_left _ _ hP, rd_app_left _ _ hN, Bool.true_and, Bool.and_true, relP44, List.append_nil,
    reloc]

end Run

/-! ## Level 4's encoding at the spec -/

theorem gUnitK_seven (v : ℕ) : gUnitK 7 v = unitK v := rfl

/-- **`encVal4` is `Enc(m)[p]`** (3.x's `encVal_eq_encAt` for any `n ≤ 7`): with `tensorW` at
`tensorWS`, Horner over `seq4`'s `2^7` final elements is the encoding of a message `m` equal to
them below `2^n`, when they are zero from `2^n` on. -/
theorem encVal4_eq (impl : OpImpl) (ht : ∀ j r, impl.tensorW j r = Impl.tensorWS j r) (inp : Input)
    {n : ℕ} (hle : n ≤ 7) (m : ℕ → K) (p : ℕ) (hm : ∀ c < 2 ^ n, finV4 seq4 inp c = m c)
    (hz : ∀ c, 2 ^ n ≤ c → c < 2 ^ 7 → finV4 seq4 inp c = 0) :
    encVal4 impl seq4 inp p = encF n (fun x => m x) p := by
  rw [encVal4, seq4_pf, hornerVal_eq, encF]
  simp only [gUnitK_seven]
  set X := finV4 seq4 inp
  rw [← Fin.sum_univ_eq_sum_range (fun c => X c * ∏ u ∈ range 7,
    (if c.testBit u then impl.tensorW p (unitK u) else 1)) (2 ^ 7)]
  have hsplit : ∑ c : Fin (2 ^ 7), X c * ∏ u ∈ range 7,
      (if (c : ℕ).testBit u then impl.tensorW p (unitK u) else 1) =
      ∑ c ∈ range (2 ^ n), X c * ∏ u ∈ range 7,
        (if c.testBit u then impl.tensorW p (unitK u) else 1) := by
    rw [Fin.sum_univ_eq_sum_range (fun c => X c * ∏ u ∈ range 7,
      (if c.testBit u then impl.tensorW p (unitK u) else 1)) (2 ^ 7)]
    symm
    refine sum_subset (range_subset_range.2 (Nat.pow_le_pow_right (by norm_num) hle))
      fun c hc hnc => ?_
    rw [hz c (by simpa using hnc) (by simpa using hc), zero_mul]
  rw [hsplit, ← Fin.sum_univ_eq_sum_range (fun c => X c * ∏ u ∈ range 7,
    (if c.testBit u then impl.tensorW p (unitK u) else 1)) (2 ^ n)]
  refine Fintype.sum_congr _ _ fun x => ?_
  rw [hm x x.2, bitProd, bitSel]
  congr 1
  rw [← prod_range_mul_prod_Ico _ hle]
  have hhi : ∏ u ∈ Ico n 7, (if (x : ℕ).testBit u then impl.tensorW p (unitK u) else 1) = 1 :=
    prod_eq_one fun u hu => by
      rw [Nat.testBit_lt_two_pow (lt_of_lt_of_le x.2
        (Nat.pow_le_pow_right (by norm_num) (mem_Ico.1 hu).1))]; rfl
  rw [hhi, mul_one]
  refine prod_congr rfl fun u hu => ?_
  have hu7 : u < 7 := by have := mem_range.1 hu; omega
  split_ifs <;> simp [ht, tensorWS_unit p hu7]

theorem toN_n4 (x : ℕ) : (Val.n x).toN = x := rfl

theorem mLog4_eq (κ : CKind) : T4.mLog κ 4 = κ.m - 25 := by
  cases κ <;> rename_i k <;> cases k <;> decide

/-! ## On an accepted run -/

/-- The final message's absorb (a table certificate): at `phStart4 47`, π's `fFinal` field. -/
theorem finalMsg4 : (fsMsgs4 seq4).getD (phStart4 47) none = some (fieldOffOf seq4 fFinal, 4096) := by
  rw [phStart4, fsStarts4_eq, fsMsgs4, fieldOffOf, seq4_eq]; decide +kernel

section Acc
variable {impl : OpImpl} {p : KindP} {inp : Input} {tr : Trace} {y : List Val × List Bool × Trace}

/-- **The final message on the log is π's** (`finV4` at `seq4`). -/
theorem finalAt_eq4 (h : SkRun4 impl p inp tr y) {e : ℕ} (he : e < 128) :
    T4.finalAt (fsOf tr (itemsOf seq4)) e = finV4 seq4 inp e := by
  have hp : phStart4 47 < 482 ∧ phStart4 47 ≠ 0 := by
    rw [phStart4, fsStarts4_eq]; decide
  have e1 := h.hq (phStart4 47) (by omega)
  rw [finalMsg4] at e1
  simp only [qOf, hp.2, if_false] at e1
  rw [T4.finalAt, msgAt_of_q e1, readK, bytesAt_extract_of_le inp.π (by omega), finV4]

/-- **Query `q`'s position register** (`yReg4 p i q − 3`) holds its position `qPos`. -/
theorem posReg4 (h : SkRun4 impl p inp tr y) {L : Log} (hL : (L.map Prod.fst).Nodup)
    (hin : ∀ e ∈ tr, e ∈ L) (hm : p.d.m = (kindOfC (fsOf tr (itemsOf seq4))).m) {i : ℕ} (hi : i < 5)
    {q : ℕ} (hq : q < (CKind.lv (kindOfC (fsOf tr (itemsOf seq4))) i).t) :
    rd (#[] ++ y.1.toArray) (yReg4 p i q - 3) =
      .n (T4.qPos (kindOfC (fsOf tr (itemsOf seq4))) (fsOf tr (itemsOf seq4)) i q) := by
  set es := fsOf tr (itemsOf seq4)
  set κ := kindOfC es
  set R := #[] ++ y.1.toArray with hRd
  have hLk : CKind.lv κ i = lvOf κ.m i := rfl
  obtain ⟨hT, hsib, -, -, hper, hper0, -, -, hsq0, -⟩ := lv_facts4 (CKind.m_mem κ) hi
  rw [← hLk] at hT hsib hper hper0
  have hK : seq4.lvK p.d.m i = CKind.lv κ i := by rw [hm, lvK_eq4]; rfl
  obtain ⟨-, hP2, hQ⟩ := phases4_lvl hi
  obtain ⟨hnP, eP⟩ := ph4 hP2
  obtain ⟨hnQ, eQ⟩ := ph4 hQ
  have hcQ : cAt4 seq4 p (29 + 5 * i) =
      (genPhase4 seq4 p (28 + 5 * i) ("P2", .squeezes (seq4.lv i).sq (.pos i)) (cAt4 seq4 p (28 + 5 * i))).2 := by
    rw [show 29 + 5 * i = 28 + 5 * i + 1 by ring, cAt4_succ seq4 p hnP, eP]
  have hpA : (cAt4 seq4 p (29 + 5 * i)).posAns = (List.range (seq4.lv i).sq).map ((cAt4 seq4 p (28 + 5 * i)).next + ·) := by
    rw [hcQ, (genPhase4_pos_ctx ..).2.1]
  obtain ⟨-, -, hans⟩ := pos_view4 h hnP (by rw [eP]) hsq0
  obtain ⟨bQ, houtQ, -, hQv⟩ := queries_view4 h hL hin hnQ (by rw [eQ]) (by rw [hK]; exact hsib)
  have hq' : q < (seq4.lv i).t := hT ▸ hq
  obtain ⟨hidx, -⟩ := hQv q hq'
  have hgy : yReg4 p i q - 3 = bQ + 2 + posW4 seq4 i * q := by
    rw [yReg4, houtQ, List.getD_eq_getElem _ _ (by simpa using hq'), List.getElem_map, List.getElem_range]
    exact Nat.add_sub_cancel _ _
  have hqp : q / (CKind.lv κ i).per < (seq4.lv i).sq :=
    lt_of_le_of_lt (Nat.div_le_div_right (by omega)) hper
  have hj : idxOf (CKind.lv κ i).logN ((rd R ((cAt4 seq4 p (29 + 5 * i)).posAns.getD
      (q / (CKind.lv κ i).per) 0)).toD) (q % (CKind.lv κ i).per) = T4.qPos κ es i q := by
    rw [hpA, List.getD_eq_getElem _ _ (by simpa using hqp), List.getElem_map, List.getElem_range,
      hans _ hqp, T4.qPos, posAt, phStart4_P2 hi]
    rfl
  simp only [hK, ← hRd] at hidx
  rw [hgy, hidx, hj]

variable {P : FinP} {zh : List Reg} {Rs : ℕ → Array Val} {Ex : ℕ → Array (List Reg)}

/-- `finP 4`'s relation on an accepted run's fields (field 10). -/
theorem relP44_of_fields (hF : Fields4 impl p inp tr P y zh Rs Ex) :
    relP44 impl inp (Rs 10) P.S ⟨(skeleton4 seq4 p).2.outs, zh, Ex 10⟩ = true := by
  set fi : FinIn := ⟨(skeleton4 seq4 p).2.outs, zh, Ex 10⟩
  have hfi : fi.outs = (skeleton4 seq4 p).2.outs := rfl
  have hE := hF.ext 10 (by omega)
  have hpos0 := skel_pos4 hF.sk
  obtain ⟨-, Lk, hLk, -, -⟩ := hF.fld 10 (by omega)
  rw [rest_gFinP4 P] at hLk
  obtain ⟨b0, -, -, -, -, hlt0, -⟩ := p1_view4 hF.sk hfi (i := 4) (by omega)
  have hpo := (pf_view4 hF.sk hfi).2.2.2.2.1
  have hys : ysOf fi 4 = (skeleton4 seq4 p).2.outs.getD 49 [] := by
    rw [ysOf, lvOuts, hfi, phaseIx_P1]
  obtain ⟨L', hL'⟩ := flag_gFinP4 impl p.tix inp (Rs 10) P fi (by
    intro x hx
    simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hx
    refine lt_of_lt_of_le ?_ hE.1
    rcases hx with hx | hx | hx
    · exact skeleton4_out_lt p hF.sk.ref _ x (by rw [← hys]; exact hx)
    · rw [hx]; exact headD_lt hpo hpos0
    · rw [hx]; exact getLastD_lt hlt0 hpos0)
  exact pureRun_det hLk hL'

/-- **`FinRest4.pf0`** on the fields (any `c₀`: P1.4's last claim is `c1 c₀ 4`). -/
theorem pf04_of_fields (hF : Fields4 impl p inp tr P y zh Rs Ex) (c₀ : Log → Log → K) (L : Log) :
    rSum T4.pfStart (fsOf tr (itemsOf seq4)) 0 = T4.c1 c₀ 4 L (fsOf tr (itemsOf seq4)) := by
  set fi : FinIn := ⟨(skeleton4 seq4 p).2.outs, zh, Ex 10⟩
  have hfi : fi.outs = (skeleton4 seq4 p).2.outs := rfl
  have hE := hF.ext 10 (by omega)
  have hpos0 := skel_pos4 hF.sk
  have hrel := relP44_of_fields hF
  obtain ⟨b0, -, -, -, hN0, hlt0, -⟩ := p1_view4 hF.sk hfi (i := 4) (by omega)
  obtain ⟨-, -, h0, -, hpo, -⟩ := pf_view4 hF.sk hfi
  simp only [relP44, Bool.and_eq_true] at hrel
  have hc := hrel.2
  rw [hE.rd (x := claim0 fi "Pf") (headD_lt hpo hpos0), hE.rd (x := p1ClaimN fi 4) (getLastD_lt hlt0 hpos0),
    h0, hN0, eqv_k] at hc
  rw [hc, c1_eq4 c₀ (by omega)]

/-- **`FinRest4.enc`** on the fields, for the folds `yv4`: with `tensorW` at the spec and the final
message zero beyond `2^mLog` (π's elements; the kind's tail check in `finPf`). -/
theorem enc4_of_fields (hF : Fields4 impl p inp tr P y zh Rs Ex) (hPS : P.S = seq4)
    (ht : ∀ j r, impl.tensorW j r = Impl.tensorWS j r) {L : Log} (hb : ¬ Bad L)
    (hin : ∀ e ∈ tr, e ∈ L) (hm : p.d.m = (kindOfC (fsOf tr (itemsOf seq4))).m)
    (hz : ∀ c, 2 ^ T4.mLog (kindOfC (fsOf tr (itemsOf seq4))) 4 ≤ c → c < 2 ^ 7 → finV4 seq4 inp c = 0) :
    ∀ q < (CKind.lv (kindOfC (fsOf tr (itemsOf seq4))) 4).t,
      yv4 p (#[] ++ y.1.toArray) 4 q = T4.encAt (kindOfC (fsOf tr (itemsOf seq4))) 4
        (T4.finalAt (fsOf tr (itemsOf seq4))) (T4.qPos (kindOfC (fsOf tr (itemsOf seq4))) (fsOf tr (itemsOf seq4)) 4 q) := by
  have hL : (L.map Prod.fst).Nodup := by by_contra hr; exact hb (.inr (.inr (.inr hr)))
  set fi : FinIn := ⟨(skeleton4 seq4 p).2.outs, zh, Ex 10⟩
  have hfi : fi.outs = (skeleton4 seq4 p).2.outs := rfl
  have hE := hF.ext 10 (by omega)
  intro q hq
  have hrel := relP44_of_fields hF
  simp only [relP44, Bool.and_eq_true, List.all_eq_true] at hrel
  have hT : (CKind.lv (kindOfC (fsOf tr (itemsOf seq4))) 4).t = (seq4.lv 4).t := (lv_facts4 (CKind.m_mem (kindOfC (fsOf tr (itemsOf seq4)))) (i := 4) (by omega)).1
  obtain ⟨hnQ, eQ⟩ := ph4 (phases4_lvl (i := 4) (by omega)).2.2
  have hys : ysOf fi 4 = (skeleton4 seq4 p).2.outs.getD (29 + 5 * 4) [] := by
    rw [ysOf, lvOuts, hfi, phaseIx_P1]
  have hysE : (ysOf fi 4).length = (seq4.lv 4).t := by
    rw [hys, skeleton4_outs seq4 p hnQ, eQ, genPhase4_queries_outs, List.length_map, List.length_range]
  have hf := hrel.1 q (List.mem_range.2 (by rw [hysE, ← hT]; exact hq))
  have hyq : (ysOf fi 4).getD q 0 = yReg4 p 4 q := by rw [yReg4, ← hys]
  have hmem : yReg4 p 4 q ∈ ysOf fi 4 := by
    rw [← hyq, List.getD_eq_getElem _ _ (by rw [hysE, ← hT]; exact hq)]; exact List.getElem_mem _
  have hylt : yReg4 p 4 q < (#[] ++ y.1.toArray).size :=
    skeleton4_out_lt p hF.sk.ref _ _ (by rw [← hys]; exact hmem)
  unfold encFlag4 at hf
  rw [hyq, hE.rd (lt_of_le_of_lt (Nat.sub_le _ _) hylt), posReg4 hF.sk hL hin hm (by omega) hq,
    hE.rd hylt, hPS, toN_n4] at hf
  have hle : T4.mLog (kindOfC (fsOf tr (itemsOf seq4))) 4 ≤ 7 := by rw [mLog4_eq]; have := CKind.m_mem (kindOfC (fsOf tr (itemsOf seq4))); omega
  rw [encVal4_eq impl ht inp hle (T4.finalAt (fsOf tr (itemsOf seq4))) _ (fun c hc => (finalAt_eq4 hF.sk
    (lt_of_lt_of_le hc (le_trans (Nat.pow_le_pow_right (by norm_num) hle) (by norm_num)))).symm) hz] at hf
  have hv := val_eqv_k hf
  rw [yv4, hv, toK_k, T4.encAt]

end Acc

end FR.Snd.R4

end G6_FRSoundness4R4P4

section G6_FRSoundness4R4PfRun

-- New for `flock-recursive` (BLUEPRINT revision 4.1, A.9 `finPf`; revision 4.3's uniform `finPf`,
-- INT-8; track R4h). The 3.x template is `FRVIRFinalsSG.flag_finPf` (`run_cellsOps`, `run_fhOps`,
-- `run_lvsOps`).

/-!
# The run kit of INT-8's `finPf` (`gFinPf`), relocated

INT-8's `finPf` computes every point family of the group and selects the kind's by kind tables
(`selOps`: a chain of `keep`s), reads the cells' bits through `keep` (`gCellsOpsK`), computes one pad
chain per family (`padsOps`) and checks the kind's exact final zero tail at the end (`gTailOps`). Its
relocated run (`reloc P.S`) reads the final message at `fieldOffOf P.S fFinal` (`fhOps`, `gTailOps`).
This module has the run lemma of each block:

* **`run_selOps`**: the chain leaves candidate `selI sel (n − 1)` (the last `i < n` the table
  selects, else `0`);
* **`run_gCellsOpsK`**: the cells' sum `cellsVal4` (`eq(cell, ρ)` over `nc` coordinates,
  `eqCellK4`);
* **`run_fhOps4`**: `final̂` over the relocated final elements (`fhVal4`, `finV4`);
* **`run_padsOps`**: family `i`'s pad `Π_{x ∈ sf[m_i − 25 ..]} (1 + x)` (`padF4`);
* **`run_gTailOps`**: the tails' flag `tailOk4`;
* **`gLvsOps_4`**: at `seq4` (whose ladder is 3.x's `lvlStar`) the level steps are 3.x's `lvsOps`.
-/

namespace FR.Snd.R4
open RecursionFast Rev4 Finset

/-! ## Values -/

/-- `selI sel n`: the last `i ≤ n`, `i ≥ 1`, with `sel i`; else `0`. -/
def selI (sel : ℕ → Bool) : ℕ → ℕ
  | 0 => 0
  | i + 1 => if sel (i + 1) then i + 1 else selI sel i

theorem selI_le (sel : ℕ → Bool) : ∀ n, selI sel n ≤ n
  | 0 => le_rfl
  | i + 1 => by
    unfold selI; split_ifs
    · exact le_rfl
    · exact (selI_le sel i).trans (Nat.le_succ i)

/-- `eq(cell, ρ)` over `nc` coordinates, the product from the left (`gCellOpsK`'s). -/
def eqCellK4 (nc : ℕ) (ρ : Array K) (c : ℕ) : K :=
  ((List.range nc).map fun v => if c.testBit v then ρ.getD v 0 else 1 + ρ.getD v 0).foldl (· * ·) 1

/-- `A + Σ_{k < n} pw·κ′^k·eq(cell_{j+k}, ρ)` (as `gCellsOpsK` accumulates it). -/
def cellsVal4 (nc : ℕ) (ρ : Array K) (kp : F) (cell : ℕ → ℕ) : ℕ → ℕ → F → K → K
  | 0, _, _, A => A
  | n + 1, j, pw, A => cellsVal4 nc ρ kp cell n (j + 1) (pw * kp) (A + K.smulF pw (eqCellK4 nc ρ (cell j)))

/-- `A + Σ_c final[c]·E[c]` over `S`'s final elements (relocated `fhOps`). -/
def fhVal4 (S : Seq) (inp : Input) (E : Array K) : List ℕ → K → K
  | [], A => A
  | c :: cs, A => fhVal4 S inp E cs (A + finV4 S inp c * E.getD c 0)

/-- The pad of family `m`: `Π_{i < pf − (m − 25)} (1 + sf[m − 25 + i])`. -/
def padF4 (sfv : ℕ → K) (pf m : ℕ) : K :=
  ((List.range (pf - (m - 25))).map fun i => 1 + sfv (m - 25 + i)).prod

/-- The final message's bytes from `2^(t − 25)` K elements on (`gTailOps`' read, `S`'s format). -/
def tailBytes4 (S : Seq) (inp : Input) (t : ℕ) : ByteArray :=
  inp.π.extract (fieldOffOf S fFinal + 2 ^ (t - 25) * 32)
    (fieldOffOf S fFinal + 2 ^ (t - 25) * 32 + (2 ^ S.pf - 2 ^ (t - 25)) * 32)

/-- **The tails' flag**: for each `t`, the bytes past `2^(t − 25)` elements are zero when the kind's
`m` is `t`. -/
def tailOk4 (P : FinP) (κ : Kind) (inp : Input) : Bool :=
  P.tails.all fun t => !decide (P.kv.m κ = t) || (tailBytes4 P.S inp t).data.all (· == 0)

theorem foldl_mul_eq {α : Type} (f : α → K) : ∀ (l : List α) (A : K),
    l.foldl (fun a x => a * f x) A = A * (l.map f).prod
  | [], A => by simp
  | x :: l, A => by rw [List.foldl_cons, foldl_mul_eq f l, List.map_cons, List.prod_cons, mul_assoc]

/-! ## The relocation -/

theorem prodKOps_reloc (S : Seq) : ∀ (xs : List Reg) (acc b : ℕ),
    (prodKOps xs acc b).map (reloc S) = prodKOps xs acc b
  | [], _, _ => rfl
  | _ :: xs, _, b => by rw [prodKOps, List.map_cons, prodKOps_reloc S xs]; rfl

theorem srcOp_reloc (S : Seq) (one z0 : Reg) (s : PtSrc) : reloc S (srcOp one z0 s) = srcOp one z0 s := by
  cases s <;> rfl

theorem ptsOps_reloc (S : Seq) (one z0 : Reg) : ∀ (ss : List (List PtSrc)) (b : ℕ),
    (ptsOps one z0 ss b).map (reloc S) = ptsOps one z0 ss b
  | [], _ => rfl
  | s :: ss, b => by
    rw [ptsOps, List.map_append, ptsOps_reloc S one z0 ss, ptOps, List.map_append, List.map_map]
    congr 2
    · exact List.map_congr_left fun x _ => srcOp_reloc S one z0 x

theorem selOps_reloc (S : Seq) (sel : ℕ → KC Bool) (cand : ℕ → Reg) (n pb : ℕ) :
    (selOps sel cand n pb).map (reloc S) = selOps sel cand n pb := by
  rw [selOps, List.map_map]; rfl

theorem gCellsOpsK_reloc (S : Seq) (nc : ℕ) (one g h kp : Reg) (cells : ℕ → KC ℕ) :
    ∀ n j acc pw b, (gCellsOpsK nc one g h kp cells n j acc pw b).map (reloc S) =
      gCellsOpsK nc one g h kp cells n j acc pw b
  | 0, _, _, _, _ => rfl
  | n + 1, j, acc, pw, b => by
    rw [gCellsOpsK, List.map_append, gCellsOpsK_reloc S nc one g h kp cells n, gCellOpsK,
      List.map_append, List.map_append, prodKOps_reloc, List.map_map]
    rfl

theorem gLvsOps_reloc (S S' : Seq) (fi : FinIn) (one cu Ts : Reg) :
    ∀ (ks : List ℕ) (W b : ℕ), (gLvsOps S' fi one cu Ts ks W b).map (reloc S) = gLvsOps S' fi one cu Ts ks W b
  | [], _, _ => rfl
  | k :: ks, W, b => by
    rw [gLvsOps, List.map_append, gLvsOps_reloc S S' fi one cu Ts ks, gLvOps]
    simp only [List.map_append, accOps_reloc, List.map_map, List.map_cons, List.map_nil]
    rfl

theorem padsOps_reloc (S : Seq) (one : Reg) (sf : List Reg) (pf : ℕ) :
    ∀ (ms : List ℕ) (pd : ℕ), (padsOps one sf pf ms pd).map (reloc S) = padsOps one sf pf ms pd
  | [], _ => rfl
  | m :: ms, pd => by
    rw [padsOps, List.map_append, padsOps_reloc S one sf pf ms, padOps, List.map_append,
      prodKOps_reloc, List.map_map]
    rfl

/-- `seq4`'s levels have 3.x's fold rounds `ell` (revision 4.4.1 changes level 4's cap only). -/
theorem seq4_ell_star (k : ℕ) : (seq4.lv k).ell = (lvlStar k).ell := by
  unfold Seq.lv Seq.lvK lvlStar lvl
  rw [seq4_eq]
  match k with
  | 0 | 1 | 2 | 3 | 4 => rfl
  | _ + 5 => rfl

/-- At `seq4` the level steps are 3.x's (they read only the levels' `ell`, `seq4_ell_star`). -/
theorem gLvsOps_4 (fi : FinIn) (one cu Ts : Reg) : ∀ (ks : List ℕ) (W b : ℕ),
    gLvsOps seq4 fi one cu Ts ks W b = lvsOps fi one cu Ts ks W b
  | [], _, _ => rfl
  | k :: ks, W, b => by
    rw [gLvsOps, lvsOps, gLvsOps_4 fi one cu Ts ks]
    simp only [gLvOps, lvOps, gSRegs, sRegs, seq4_ell_star]

/-! ## The blocks' runs -/

section Run
variable (impl : OpImpl) (κ : Kind) (inp : Input)

/-- **`selOps`**: the chain of `keep`s leaves the selected candidate. -/
theorem run_selOps (sel : ℕ → KC Bool) (cand : ℕ → Reg) (n : ℕ) (R : Array Val)
    (hc : ∀ i < n, cand i < R.size) :
    ∃ M, pureRun impl κ inp (selOps sel cand n R.size) R [] = some (M, true) ∧ M.length = n - 1 ∧
      (0 < n → selOut cand n R.size < R.size + M.length ∧
        rd (R ++ M.toArray) (selOut cand n R.size) = rd R (cand (selI (fun i => sel i κ) (n - 1)))) := by
  set s : ℕ → Bool := fun i => sel i κ
  set g : ℕ → Op := fun i => .keep (sel (i + 1)) (cand (i + 1)) (if i = 0 then cand 0 else R.size + (i - 1))
  have key : ∀ k, k ≤ n - 1 → pureRun impl κ inp ((List.range k).map g) R [] =
      some ((List.range k).map (fun i => rd R (cand (selI s (i + 1)))), true) := by
    intro k hk
    induction k with
    | zero => rfl
    | succ k ih =>
      rw [List.range_succ, List.map_append, pureRun_append, ih (by omega), Option.bind_some,
        List.map_singleton]
      have hv : evalOp impl κ inp (R ++ ((List.range k).map (fun i => rd R (cand (selI s (i + 1))))).toArray)
          (g k) = .vals [rd R (cand (selI s (k + 1)))] true := by
        simp only [g, evalOp]
        rw [rd_app_left _ _ (hc (k + 1) (by omega))]
        congr 2
        by_cases hk0 : k = 0
        · subst hk0
          rw [if_pos rfl, rd_app_left _ _ (hc 0 (by omega))]
          simp only [selI, s]; split_ifs <;> rfl
        · rw [if_neg hk0, rd_app]
          obtain ⟨k', rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
          rw [show k' + 1 - 1 = k' by omega, List.getD_eq_getElem _ _ (by simp), List.getElem_map,
            List.getElem_range]
          conv_rhs => rw [selI]
          simp only [s]; split_ifs <;> rfl
      simp only [pureRun, hv, Option.map_some, Bool.and_true, List.map_append, List.map_cons,
        List.map_nil]
  refine ⟨_, key (n - 1) le_rfl, by simp, fun hn => ?_⟩
  simp only [List.length_map, List.length_range]
  rcases Nat.lt_or_ge n 2 with h2 | h2
  · have hn1 : n = 1 := by omega
    subst hn1
    have h0 := hc 0 (by omega)
    simp only [selOut, le_refl, if_true, selI, Nat.sub_self, List.range_zero, List.map_nil]
    exact ⟨by omega, by rw [show (([] : List Val).toArray) = #[] from rfl, Array.append_empty]⟩
  · have hlt : n - 2 < (List.map (fun i => rd R (cand (selI s (i + 1)))) (List.range (n - 1))).length := by
      simp only [List.length_map, List.length_range]; omega
    rw [selOut, if_neg (by omega), rd_app, List.getD_eq_getElem _ _ hlt, List.getElem_map,
      List.getElem_range, show n - 2 + 1 = n - 1 by omega]
    refine ⟨?_, rfl⟩
    exact Nat.add_lt_add_left (show n - 2 < n - 1 by omega) _

theorem foldl_selK (r : Array Val) (nc : ℕ) (ρ : Array K) (b : ℕ) (c : ℕ)
    (hv : ∀ v < nc, (rd r (b + v)).toK = if c.testBit v then ρ.getD v 0 else 1 + ρ.getD v 0) :
    ((List.range nc).map (b + ·)).foldl (fun a x => a * (rd r x).toK) 1 = eqCellK4 nc ρ c := by
  rw [eqCellK4, foldl_mul_eq, List.map_map]
  have : ∀ (l : List K) (A : K), l.foldl (· * ·) A = A * l.prod := by
    intro l; induction l with
    | nil => simp
    | cons x l ih => intro A; rw [List.foldl_cons, ih, List.prod_cons, mul_assoc]
  rw [this]
  congr 2
  exact List.map_congr_left fun v hv' => hv v (List.mem_range.1 hv')

/-- The register of `gCellsOpsK`'s last power `pw·κ′ⁿ` (`pw` itself after no cell). -/
def gCellsPwK (nc : ℕ) : ℕ → ℕ → ℕ → ℕ
  | 0, pw, _ => pw
  | n + 1, _, b => gCellsPwK nc n (b + (2 * nc + 2)) (b + (2 * nc + 3))

/-- With `pw` just below the chain, its last power sits at the chain's last register. -/
theorem gCellsPwK_eq (nc : ℕ) : ∀ (n pw : ℕ), gCellsPwK nc n pw (pw + 1) = pw + 1 + (2 * nc + 3) * n - 1
  | 0, pw => by simp [gCellsPwK]
  | n + 1, pw => by
    rw [gCellsPwK, show pw + 1 + (2 * nc + 3) = pw + 1 + (2 * nc + 2) + 1 by omega, gCellsPwK_eq nc n]
    rw [Nat.mul_succ]; omega

/-- **`gCellsOpsK`** (3.x's `run_cellsOps` with the cells' bits by `keep`); also the last power
register (`gCellsPwK`), from which a second chain continues. -/
theorem run_gCellsOpsK (nc : ℕ) (one g h kp : ℕ) (cells : ℕ → KC ℕ) (ρ : Array K) (kpv : F)
    (r : Array Val) (h1 : one < r.size) (hv1 : rd r one = .k 1) (hk : kp < r.size) (hkv : (rd r kp).toF = kpv)
    (hg0 : ∀ v < nc, g + v < r.size ∧ rd r (g + v) = .k (ρ.getD v 0))
    (hh0 : ∀ v < nc, h + v < r.size ∧ rd r (h + v) = .k (1 + ρ.getD v 0)) (hnc : 0 < nc) :
    ∀ (n j acc pw : ℕ) (A : K) (Pw : F) (L : List Val),
    acc < r.size + L.length → rd (r ++ L.toArray) acc = .k A →
    pw < r.size + L.length → (rd (r ++ L.toArray) pw).toF = Pw →
    ∃ M, pureRun impl κ inp (gCellsOpsK nc one g h kp cells n j acc pw (r.size + L.length)) r L =
        some (L ++ M, true) ∧ M.length = (2 * nc + 3) * n ∧
      rd (r ++ (L ++ M).toArray) (gCellsAccK nc n acc (r.size + L.length)) =
        .k (cellsVal4 nc ρ kpv (fun j => cells j κ) n j Pw A) ∧
      (rd (r ++ (L ++ M).toArray) (gCellsPwK nc n pw (r.size + L.length))).toF = Pw * kpv ^ n
  | 0, _, acc, pw, A, Pw, L, _, hA, _, hP =>
    ⟨[], by simp [gCellsOpsK, pureRun], by simp, by simpa [gCellsAccK, cellsVal4] using hA,
      by simpa [gCellsPwK] using hP⟩
  | n + 1, j, acc, pw, A, Pw, L, hacc, hA, hpw, hP => by
    set b := r.size + L.length with hb
    set c := cells j κ
    -- the keeps
    set ks : List Op := (List.range nc).map fun v => .keep (fun κ => (cells j κ).testBit v) (g + v) (h + v)
    set kv : ℕ → Val := fun v => if c.testBit v then .k (ρ.getD v 0) else .k (1 + ρ.getD v 0)
    have h₀ := run_frozen impl κ inp r L (fun op => match op with
      | .keep _ x _ => kv (x - g) | _ => default) ks [] (fun op hop Y => by
        obtain ⟨v, hv, rfl⟩ := List.mem_map.mp hop
        have hv' := List.mem_range.mp hv
        simp only [evalOp, rd_app_left _ _ (hg0 v hv').1, rd_app_left _ _ (hh0 v hv').1, (hg0 v hv').2,
          (hh0 v hv').2, kv, c, Nat.add_sub_cancel_left])
    simp only [List.append_nil] at h₀
    set M₀ := ks.map fun op => match op with | .keep _ x _ => kv (x - g) | _ => default
    have hl₀ : M₀.length = nc := by simp [M₀, ks]
    have hM₀ : ∀ v < nc, rd (r ++ (L ++ M₀).toArray) (b + v) = kv v := by
      intro v hv
      rw [hb, Nat.add_assoc, rd_app, List.getD_append_right _ _ _ _ (by omega)]
      simp [M₀, ks, hv, kv]
    have hR0 : (r ++ (L ++ M₀).toArray).size = b + nc := by simp [hb, hl₀]; omega
    obtain ⟨M₁, h₁, hl₁, hv₁⟩ := run_prodKOps impl κ inp (r ++ (L ++ M₀).toArray)
      ((List.range nc).map (b + ·)) one 1 []
      (fun x hx => by
        obtain ⟨v, hv, rfl⟩ := List.mem_map.mp hx
        have := List.mem_range.mp hv
        rw [hR0]; omega)
      (by rw [hR0]; simp; omega)
      (by simp [rd_app_left _ _ h1, hv1])
    simp only [List.length_nil, Nat.add_zero, hR0, List.nil_append] at h₁ hv₁
    rw [foldl_selK (r ++ (L ++ M₀).toArray) nc ρ b c (fun v hv => by
      rw [hM₀ v hv]; simp only [kv]; split_ifs <;> rfl),
      prodKOut_eq _ _ _ (by simp; omega)] at hv₁
    have hl₁' : M₁.length = nc := by rw [hl₁]; simp
    have h₁' : pureRun impl κ inp (prodKOps ((List.range nc).map (b + ·)) one (b + nc)) r (L ++ M₀) =
        some (L ++ M₀ ++ M₁, true) := by
      have := pureRun_rebase impl κ inp (prodKOps ((List.range nc).map (b + ·)) one (b + nc)) r (L ++ M₀) []
      rw [List.append_nil] at this; rw [this, h₁]; rfl
    have hv₁' : rd (r ++ (L ++ M₀ ++ M₁).toArray) (b + nc + (nc - 1)) = .k (eqCellK4 nc ρ c) := by
      rw [← hv₁]; simp only [List.length_map, List.length_range]
      rw [show b + nc + nc - 1 = b + nc + (nc - 1) by omega]; simp [Array.append_assoc]
    set e := eqCellK4 nc ρ c
    set u₁ : Val := .k (K.smulF Pw e)
    set u₂ : Val := .k (A + K.smulF Pw e)
    set u₃ : Val := .f (Pw * kpv)
    have hlen1 : r.size + (L ++ M₀ ++ M₁).length = b + 2 * nc := by simp [hb, hl₀, hl₁']; omega
    have e1 : evalOp impl κ inp (r ++ (L ++ M₀ ++ M₁).toArray) (.mulKF (b + nc + (nc - 1)) pw) =
        .vals [u₁] true := by
      simp only [evalOp]
      rw [hv₁', show L ++ M₀ ++ M₁ = L ++ (M₀ ++ M₁) by simp, FR.rd_pre r hpw, hP]; rfl
    have e2 : evalOp impl κ inp (r ++ (L ++ M₀ ++ M₁ ++ [u₁]).toArray) (.addK acc (b + 2 * nc)) =
        .vals [u₂] true := by
      simp only [evalOp]
      rw [← hlen1, rd_new1, show L ++ M₀ ++ M₁ ++ [u₁] = L ++ (M₀ ++ M₁ ++ [u₁]) by simp,
        FR.rd_pre r hacc, hA]; rfl
    have e3 : evalOp impl κ inp (r ++ (L ++ M₀ ++ M₁ ++ [u₁] ++ [u₂]).toArray) (.mulF pw kp) =
        .vals [u₃] true := by
      simp only [evalOp]
      rw [show L ++ M₀ ++ M₁ ++ [u₁] ++ [u₂] = L ++ (M₀ ++ M₁ ++ [u₁] ++ [u₂]) by simp,
        FR.rd_pre r hpw, hP, rd_app_left _ _ hk, hkv]
    set L' := L ++ M₀ ++ M₁ ++ [u₁] ++ [u₂] ++ [u₃]
    have hL' : r.size + L'.length = b + (2 * nc + 3) := by
      simp only [L', List.length_append, List.length_singleton]; omega
    obtain ⟨M, hM, hl, hv, hpv⟩ := run_gCellsOpsK nc one g h kp cells ρ kpv r h1 hv1 hk hkv hg0 hh0 hnc n (j + 1)
      (b + (2 * nc + 1)) (b + (2 * nc + 2)) (A + K.smulF Pw e) (Pw * kpv) L' (by rw [hL']; omega)
      (by
        have : b + (2 * nc + 1) = r.size + (L ++ M₀ ++ M₁ ++ [u₁]).length := by
          simp only [List.length_append, List.length_singleton]; omega
        rw [this, show L' = L ++ M₀ ++ M₁ ++ [u₁] ++ (u₂ :: [u₃]) by simp [L'], rd_new])
      (by rw [hL']; omega)
      (by
        have : b + (2 * nc + 2) = r.size + (L ++ M₀ ++ M₁ ++ [u₁] ++ [u₂]).length := by
          simp only [List.length_append, List.length_singleton]; omega
        rw [this, rd_new1]; rfl)
    rw [hL'] at hM hv hpv
    refine ⟨M₀ ++ M₁ ++ [u₁, u₂, u₃] ++ M, ?_, by simp [hl, hl₁', hl₀]; ring, ?_, ?_⟩
    · rw [gCellsOpsK, gCellOpsK, List.append_assoc, List.append_assoc, pr_app impl κ inp r (M := M₀) h₀,
        pr_app impl κ inp r (M := M₁) h₁']
      simp only [List.cons_append, List.nil_append]
      rw [show L ++ M₀ ++ M₁ = L ++ M₀ ++ M₁ from rfl, pr_op impl κ inp r e1, pr_op impl κ inp r e2,
        pr_op impl κ inp r e3, show L ++ M₀ ++ M₁ ++ [u₁] ++ [u₂] ++ [u₃] = L' from rfl, hM]
      simp [L']
    · simp only [gCellsAccK, cellsVal4]
      rw [show L ++ (M₀ ++ M₁ ++ [u₁, u₂, u₃] ++ M) = L' ++ M by simp [L']]
      exact hv
    · simp only [gCellsPwK]
      rw [show L ++ (M₀ ++ M₁ ++ [u₁, u₂, u₃] ++ M) = L' ++ M by simp [L'], hpv, pow_succ']; ring

/-- **`fhOps`, relocated** (3.x's `run_fhOps` at `S`'s final elements). -/
theorem run_fhOps4 (S : Seq) (r : Array Val) (E : ℕ) (Ev : Array K) (hE : E < r.size) (hEv : (rd r E).toAK = Ev) :
    ∀ (cs : List ℕ) (acc : ℕ) (A : K) (L : List Val),
    acc < r.size + L.length → rd (r ++ L.toArray) acc = .k A →
    ∃ M, pureRun impl κ inp ((fhOps E cs acc (r.size + L.length)).map (reloc S)) r L = some (L ++ M, true) ∧
      M.length = 4 * cs.length ∧
      rd (r ++ (L ++ M).toArray) (fhOut cs acc (r.size + L.length)) = .k (fhVal4 S inp Ev cs A)
  | [], acc, A, L, _, hA => ⟨[], by simp [fhOps, pureRun], rfl, by simpa [fhOut, fhVal4] using hA⟩
  | c :: cs, acc, A, L, hacc, hA => by
    set b := r.size + L.length with hb
    set u₁ : Val := .k (finV4 S inp c)
    set u₂ : Val := .k (Ev.getD c 0)
    set u₃ : Val := .k (finV4 S inp c * Ev.getD c 0)
    set u₄ : Val := .k (A + finV4 S inp c * Ev.getD c 0)
    have e1 : evalOp impl κ inp (r ++ L.toArray) (reloc S (.piElemK fFinal (32 * c))) = .vals [u₁] true :=
      (evalOp_reloc impl κ inp _ S (by decide : fFinal < 19) (32 * c) 0 0).2.2.1
    have e2 : evalOp impl κ inp (r ++ (L ++ [u₁]).toArray) (reloc S (.getK E c)) = .vals [u₂] true := by
      simp only [reloc, evalOp, rd_app_left _ _ hE, hEv]; rfl
    have e3 : evalOp impl κ inp (r ++ (L ++ [u₁] ++ [u₂]).toArray) (reloc S (.mulK b (b + 1))) =
        .vals [u₃] true := by
      have x2 : b + 1 = r.size + (L ++ [u₁]).length := by
        simp only [hb, List.length_append, List.length_singleton]; omega
      simp only [reloc, evalOp]
      rw [x2, rd_new1, List.append_assoc, List.singleton_append, rd_new]; rfl
    have e4 : evalOp impl κ inp (r ++ (L ++ [u₁] ++ [u₂] ++ [u₃]).toArray) (reloc S (.addK acc (b + 2))) =
        .vals [u₄] true := by
      have x3 : b + 2 = r.size + (L ++ [u₁] ++ [u₂]).length := by
        simp only [hb, List.length_append, List.length_singleton]; omega
      simp only [reloc, evalOp]
      rw [x3, rd_new1, List.append_assoc, List.append_assoc, FR.rd_pre r hacc, hA]; rfl
    set L' := L ++ [u₁] ++ [u₂] ++ [u₃] ++ [u₄]
    have hL' : r.size + L'.length = b + 4 := by
      simp only [L', hb, List.length_append, List.length_singleton]; omega
    obtain ⟨M, hM, hl, hv⟩ := run_fhOps4 S r E Ev hE hEv cs (b + 3) (A + finV4 S inp c * Ev.getD c 0) L'
      (by rw [hL']; omega)
      (by
        have x4 : b + 3 = r.size + (L ++ [u₁] ++ [u₂] ++ [u₃]).length := by
          simp only [hb, List.length_append, List.length_singleton]; omega
        rw [x4, rd_new1])
    rw [hL'] at hM hv
    refine ⟨[u₁, u₂, u₃, u₄] ++ M, ?_, by simp [hl]; ring, ?_⟩
    · rw [fhOps]
      simp only [List.map_append, List.map_cons, List.map_nil, List.cons_append, List.nil_append]
      rw [pr_op impl κ inp r e1, pr_op impl κ inp r e2, pr_op impl κ inp r e3,
        pr_op impl κ inp r e4, show L ++ [u₁] ++ [u₂] ++ [u₃] ++ [u₄] = L' from rfl, hM]
      simp [L']
    · simp only [fhOut, fhVal4]
      rw [show L ++ ([u₁, u₂, u₃, u₄] ++ M) = L' ++ M by simp [L']]
      exact hv

theorem prod_range_succ_list (f : ℕ → K) (k : ℕ) :
    ((List.range (k + 1)).map f).prod = f 0 * ((List.range k).map fun i => f (i + 1)).prod := by
  rw [List.range_succ_eq_map, List.map_cons, List.prod_cons, List.map_map]; rfl

/-- **One pad chain** (`padOps` at `μ`, `k` factors, from `pd = R.size`). -/
theorem run_padOps (one : Reg) (sf : List Reg) (sfv : ℕ → K) (μ k : ℕ) (R : Array Val)
    (h1 : one < R.size) (hv1 : rd R one = .k 1)
    (hs : ∀ i < k, sf.getD (μ + i) 0 < R.size ∧ (rd R (sf.getD (μ + i) 0)).toK = sfv (μ + i)) :
    ∃ M, pureRun impl κ inp (padOps one R.size μ k sf) R [] = some (M, true) ∧ M.length = k + (k - 1) ∧
      padReg one R.size k < R.size + M.length ∧
      rd (R ++ M.toArray) (padReg one R.size k) = .k (((List.range k).map fun i => 1 + sfv (μ + i)).prod) := by
  have hB := run_base impl κ inp R ((List.range k).map fun i => Op.addK one (sf.getD (μ + i) 0)) []
    (fun op hop Y => by
      obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hop
      simp only [evalOp, rd_app_left _ _ h1, rd_app_left _ _ (hs i (List.mem_range.mp hi)).1])
    (fun op hop => by obtain ⟨i, -, rfl⟩ := List.mem_map.mp hop; exact ⟨_, rfl⟩)
  set M₀ : List Val := (List.range k).map fun i => .k (1 + sfv (μ + i))
  have hM₀ : ((List.range k).map fun i => Op.addK one (sf.getD (μ + i) 0)).map (baseVal impl κ inp R) = M₀ := by
    simp only [List.map_map, M₀]
    refine List.map_congr_left fun i hi => ?_
    simp only [Function.comp_apply, baseVal, evalOp, hv1, (hs i (List.mem_range.mp hi)).2, toK_k]
  rw [hM₀, List.nil_append] at hB
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · refine ⟨[], by simp [padOps, prodKOps, pureRun], rfl, ?_, ?_⟩
    · simp [padReg]; omega
    · simp [padReg, hv1]
  have hl₀ : M₀.length = k := by simp [M₀]
  have hR0 : (R ++ M₀.toArray).size = R.size + k := by simp [hl₀]
  set xs := (List.range (k - 1)).map (R.size + 1 + ·)
  obtain ⟨M₁, h₁, hl₁, hv₁⟩ := run_prodKOps impl κ inp (R ++ M₀.toArray) xs R.size (1 + sfv μ) []
    (fun x hx => by
      obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hx
      have := List.mem_range.mp hi
      rw [hR0]; omega)
    (by simp; omega)
    (by
      rw [show (([] : List Val).toArray) = #[] from rfl, Array.append_empty, rd_app0]
      simp [M₀, hk])
  simp only [List.length_nil, Nat.add_zero, hR0, List.nil_append] at h₁ hv₁
  have hfold : xs.foldl (fun a x => a * (rd (R ++ M₀.toArray) x).toK) (1 + sfv μ) =
      ((List.range k).map fun i => 1 + sfv (μ + i)).prod := by
    rw [foldl_mul_eq, show k = (k - 1) + 1 by omega, prod_range_succ_list, Nat.add_zero]
    congr 1
    simp only [xs, List.map_map]
    congr 1
    refine List.map_congr_left fun i hi => ?_
    have hi' := List.mem_range.mp hi
    simp only [Function.comp_apply]
    rw [show R.size + 1 + i = R.size + (i + 1) by omega, rd_app]
    simp [M₀, show i + 1 < k by omega, Nat.add_assoc, toK_k]
  rw [hfold] at hv₁
  have hpr : prodKOut xs R.size (R.size + k) = padReg one R.size k := by
    rw [padReg, if_neg (by omega)]
    rcases Nat.lt_or_ge k 2 with h2 | h2
    · have : k = 1 := by omega
      subst this; simp [xs, prodKOut]
    · rw [prodKOut_eq _ _ _ (by simp [xs]; omega)]; simp [xs]; omega
  rw [hpr] at hv₁
  refine ⟨M₀ ++ M₁, ?_, by simp [hl₀, hl₁, xs], ?_, ?_⟩
  · rw [padOps]; exact pr_seq impl κ inp hB h₁
  · rw [padReg, if_neg (by omega)]; simp [hl₀, hl₁, xs]; omega
  · rw [← hv₁]; simp [Array.append_assoc]

theorem padsReg_cons (one : Reg) (pf m : ℕ) (ms : List ℕ) (pd i : ℕ) :
    padsReg one pf (m :: ms) pd (i + 1) = padsReg one pf ms (pd + padW pf m) i := by
  simp only [padsReg, List.take_succ_cons, List.map_cons, List.sum_cons, List.getD_cons_succ, Nat.add_assoc]

/-- **The pad chains** (`padsOps`, from `pd = R.size`): family `i`'s product in `padsReg`. -/
theorem run_padsOps (one : Reg) (sf : List Reg) (sfv : ℕ → K) (pf : ℕ) :
    ∀ (ms : List ℕ) (R : Array Val), one < R.size → rd R one = .k 1 →
    (∀ v < pf, sf.getD v 0 < R.size ∧ (rd R (sf.getD v 0)).toK = sfv v) →
    ∃ M, pureRun impl κ inp (padsOps one sf pf ms R.size) R [] = some (M, true) ∧
      M.length = (ms.map (padW pf)).sum ∧ ∀ i < ms.length,
        padsReg one pf ms R.size i < R.size + M.length ∧
        rd (R ++ M.toArray) (padsReg one pf ms R.size i) = .k (padF4 sfv pf (ms.getD i 0))
  | [], R, _, _, _ => ⟨[], by simp [padsOps, pureRun], rfl, fun i hi => absurd hi (by simp)⟩
  | m :: ms, R, h1, hv1, hs => by
    obtain ⟨M₁, h₁, hl₁, hb₁, hv₁⟩ := run_padOps impl κ inp one sf sfv (m - 25) (pf - (m - 25)) R h1 hv1
      (fun i hi => hs _ (by omega))
    have hl₁' : M₁.length = padW pf m := by rw [hl₁, padW]
    obtain ⟨M, hM, hl, hv⟩ := run_padsOps one sf sfv pf ms (R ++ M₁.toArray) (Nat.lt_of_lt_of_le h1 (by simp))
      (by rw [rd_app_left _ _ h1, hv1])
      (fun v hv => ⟨Nat.lt_of_lt_of_le (hs v hv).1 (by simp), by rw [rd_app_left _ _ (hs v hv).1, (hs v hv).2]⟩)
    have hsz : (R ++ M₁.toArray).size = R.size + padW pf m := by simp [hl₁']
    rw [hsz] at hM hv
    refine ⟨M₁ ++ M, ?_, by simp [hl, hl₁'], fun i hi => ?_⟩
    · rw [padsOps, ← hsz]; exact pr_seq impl κ inp h₁ (by rw [hsz]; exact hM)
    · rcases i with _ | i
      · have e : padsReg one pf (m :: ms) R.size 0 = padReg one R.size (pf - (m - 25)) := by
          simp [padsReg]
        rw [e]
        refine ⟨Nat.lt_of_lt_of_le hb₁ (by simp), ?_⟩
        rw [show R ++ (M₁ ++ M).toArray = R ++ M₁.toArray ++ M.toArray by simp [Array.append_assoc],
          rd_append_left (by rw [Array.size_append, List.size_toArray]; exact hb₁), hv₁]
        rfl
      · rw [padsReg_cons]
        obtain ⟨hb, hv'⟩ := hv i (by simpa using hi)
        refine ⟨by
          rw [List.length_append, hl₁', ← Nat.add_assoc]; exact hb, ?_⟩
        rw [show R ++ (M₁ ++ M).toArray = R ++ M₁.toArray ++ M.toArray by simp [Array.append_assoc], hv']
        rfl

/-- **The kind's final zero tails** (relocated `gTailOps`, from `R.size`): the flag is the tails'. -/
theorem run_gTailOps (S : Seq) (P : FinP) : ∀ (ts : List ℕ) (R : Array Val),
    ∃ M, pureRun impl κ inp ((gTailOps (fun _ => P) S.pf ts R.size).map (reloc S)) R [] =
      some (M, ts.all fun t => !decide (P.kv.m κ = t) || (tailBytes4 S inp t).data.all (· == 0))
  | [], _ => ⟨[], rfl⟩
  | t :: ts, R => by
    set u : Val := .b (tailBytes4 S inp t)
    obtain ⟨M, hM⟩ := run_gTailOps S P ts (R ++ [u].toArray)
    have e1 : evalOp impl κ inp (R ++ ([] : List Val).toArray)
        (reloc S (.piField fFinal (2 ^ (t - 25) * 32) ((2 ^ S.pf - 2 ^ (t - 25)) * 32))) = .vals [u] true :=
      (evalOp_reloc impl κ inp _ S (by decide : fFinal < 19) _ _ 0).1
    have hsz : (R ++ [u].toArray).size = R.size + 1 := by simp
    refine ⟨u :: M, ?_⟩
    rw [gTailOps, List.map_append, List.map_cons, List.map_cons, List.map_nil, List.cons_append,
      List.cons_append, List.nil_append, pr_op impl κ inp R e1]
    simp only [pureRun, reloc, evalOp, List.nil_append, rd_app0, List.getD_cons_zero]
    rw [hsz] at hM
    have hM' := pureRun_rebase impl κ inp ((gTailOps (fun _ => P) S.pf ts (R.size + 1)).map (reloc S)) R [u] []
    rw [List.append_nil] at hM'
    rw [List.append_nil, hM', hM]
    simp [u, Val.isZero, List.all_cons]

end Run

end FR.Snd.R4

end G6_FRSoundness4R4PfRun

section G6_FRSoundness4R4PfFlag

-- New for `flock-recursive` (BLUEPRINT revision 4.1, A.9 `finPf`; revision 4.3's uniform `finPf`,
-- INT-8; track R4h). The 3.x template is `FRVIRFinalsSG.flag_finPf`.

/-!
# The flag of INT-8's relocated `finPf` (`flag_gFinPf4`)

For a fixed-kind program (`Q := fun _ => P`) with kind-table cells (`P.ck`), the relocated
`gFinPf P` asks nothing and its flag is **`relPf4`**: `claimN(Pf) = Ŵ₄(P₄)·pad·final̂(sf)`, with

* the kind's points by the tables: slot `s` (tails `P₁ … P₄`, then `P₀`) is point `slotIx P κ s` of
  `gPfPts` (`m*`'s if `selA`, else family `famI`'s);
* `Ŵ₀(P₀) = rsWeight(r″, the kind's claim points (ptIx), κ, β, P₀)` plus, on a node, the cells' sum
  over `nc` coordinates (`w0V4`); the four level steps are 3.x's `lvsV` (`wV4`);
* the kind's pad (`padV4`: `1` for `m*`, else its family's `padF4`) and `final̂` over the relocated
  final elements (`finHat4`);

and the tails' flag `tailOk4` (the final message's exact zero tail of the kind).
-/

namespace FR.Snd.R4
open RecursionFast Rev4 Finset

/-! ## The kind's points -/

/-- Family `i`'s candidate point for slot `s` (`pfCand`'s index into `gPfPts`). -/
def candIx (P : FinP) (i s : ℕ) : ℕ :=
  if s < 4 then 7 + 3 * P.fams.length + P.e4s.length + 4 * i + s else 8 + 7 * P.fams.length + P.e4s.length + i

/-- The `m*` family's (`pfCandA`'s index). -/
def candAIx (P : FinP) (s : ℕ) : ℕ :=
  if s < 4 then 3 + 3 * P.fams.length + P.e4s.length + s else 7 + 7 * P.fams.length + P.e4s.length

/-- The kind's family among `fams` (the one `selOps` leaves). -/
def famI (P : FinP) (κ : Kind) : ℕ := selI (fun i => decide (P.kv.fsel κ = i)) (P.fams.length - 1)

/-- **Slot `s`'s point** (tails `s < 4`, `P₀` at `4`) for kind `κ`. -/
def slotIx (P : FinP) (κ : Kind) (s : ℕ) : ℕ := if P.kv.selA κ then candAIx P s else candIx P (famI P κ) s

theorem pfCand_eq (P : FinP) (Pp : ℕ → ℕ) (i s : ℕ) : pfCand P Pp i s = Pp (candIx P i s) := by
  unfold pfCand candIx; split_ifs <;> rfl

theorem pfCandA_eq (P : FinP) (Pp : ℕ → ℕ) (s : ℕ) : pfCandA P Pp s = Pp (candAIx P s) := by
  unfold pfCandA candAIx; split_ifs <;> rfl

theorem gPfPts_length (P : FinP) (fi : FinIn) :
    (gPfPts P fi).length = 8 + 8 * P.fams.length + P.e4s.length := by
  simp only [gPfPts, List.length_append, List.length_cons, List.length_nil, List.length_map,
    List.length_range, List.length_flatMap]
  simp only [List.map_const', List.sum_replicate, smul_eq_mul]
  ring

theorem candIx_lt (P : FinP) (fi : FinIn) {i : ℕ} (hi : i < P.fams.length) (s : ℕ) :
    candIx P i s < (gPfPts P fi).length := by
  rw [gPfPts_length, candIx]; split_ifs <;> omega

theorem candAIx_lt (P : FinP) (fi : FinIn) (s : ℕ) : candAIx P s < (gPfPts P fi).length := by
  rw [gPfPts_length, candAIx]; split_ifs <;> omega

theorem famI_lt (P : FinP) (κ : Kind) (hnf : 0 < P.fams.length) : famI P κ < P.fams.length :=
  lt_of_le_of_lt (selI_le _ _) (by omega)

theorem slotIx_lt (P : FinP) (κ : Kind) (fi : FinIn) (hnf : 0 < P.fams.length) (s : ℕ) :
    slotIx P κ s < (gPfPts P fi).length := by
  unfold slotIx; split_ifs
  · exact candAIx_lt P fi s
  · exact candIx_lt P fi (famI_lt P κ hnf) s

/-! ## The relocated op list -/

/-- **INT-8's `finPf` relocated** (fixed kind, `ck`): `gFinPf`'s blocks, the final message's reads
(`fhOps`, `gTailOps`) relocated to `P.S`'s format. -/
def gFinPfR (P : FinP) (fi : FinIn) (b : ℕ) : List Op :=
  let S := P.S; let nc := P.nc; let nf := P.fams.length
  let one := b
  let cu := b + 1
  let z0 := b + 2
  let pts := gPfPts P fi
  let Pp := ptsOut pts (b + 3)
  let pb := b + 3 + ptsW pts
  let sb := pb + 5 * (nf - 1)
  let wb := sb + 5
  let rs1 := coordsR fi "RS1"
  let kp := (outsOf fi "B'").headD 0
  let cb := wb + (2 + 2 * nc)
  let c9 := cb + 1 + (2 * nc + 3) * P.ncell
  let acc9 := gCellsAccK nc P.ncell z0 (cb + 1)
  let cr := c9 + (2 * nc + 3) * P.nrcell
  let ce := cond P.rsvOps (cr + 1) c9
  let lb := ce + 2
  let fb := lb + lvsW fi [1, 2, 3, 4]
  let pd := fb + 2 + 4 * 2 ^ S.pf
  let sf := chals fi "Pf" S.pf
  let pe := pd + (P.fams.map (padW S.pf)).sum
  let sel : ℕ → KC Bool := fun i κ => decide (P.kv.fsel κ = i)
  let selA : KC Bool := fun κ => P.kv.selA κ
  let node : KC Bool := fun κ => P.kv.node κ
  ([.const (fun _ => .k 1), .const (fun _ => .k (1 + K.u)), .const (fun _ => .k 0)] : List Op) ++
   ptsOps one z0 pts (b + 3) ++
   (List.range 5).flatMap (fun s => selOps sel (fun i => pfCand P Pp i s) nf (pb + s * (nf - 1))) ++
   (List.range 5).map (fun s =>
     .keep selA (pfCandA P Pp s) (selOut (fun i => pfCand P Pp i s) nf (pb + s * (nf - 1)))) ++
   ([.packF ((List.range 7).map fun p => rs1.getD p 0),
    .rsWeight wb (fun κ => (P.kv.ptIx κ).map Pp) (rs1.getD 7 0) ((outsOf fi "L3β").headD 0)
      node (sb + 4)] : List Op) ++
   ((List.range nc).map (fun v => .getK (sb + 4) v) : List Op) ++
   ((List.range nc).map (fun v => .addK one (wb + 2 + v)) : List Op) ++
   ([.mulF kp kp] : List Op) ++
   (gCellsOpsK nc one (wb + 2) (wb + (nc + 2)) kp (fun j _ => P.cells.getD j 0) P.ncell 0 z0 cb (cb + 1) ++
     cond P.rsvOps (gCellsOpsK nc one (wb + 2) (wb + (nc + 2)) kp (fun j _ => P.rcells.getD j 0)
       P.nrcell 0 acc9 (c9 - 1) c9 ++ [.keep (fun _ => P.rsv) (gCellsAccK nc P.nrcell acc9 c9) acc9]) []) ++
   ([.keep node (cond P.rsvOps cr acc9) z0, .addK (wb + 1) ce] : List Op) ++
   gLvsOps S fi one cu sb [1, 2, 3, 4] (ce + 1) lb ++
   ([.packK sf, .eqTableK fb] : List Op) ++ (fhOps (fb + 1) (List.range (2 ^ S.pf)) z0 (fb + 2)).map (reloc S) ++
   padsOps one sf S.pf P.fams pd ++
   selOps sel (padsReg one S.pf P.fams pd) nf pe ++
   ([.keep selA one (selOut (padsReg one S.pf P.fams pd) nf pe),
    .mulK (lvsOut fi [1, 2, 3, 4] (ce + 1) lb) (pe + (nf - 1)),
    .mulK (pe + nf) (fhOut (List.range (2 ^ S.pf)) z0 (fb + 2)),
    .assertEq (pe + nf + 1) (claimN fi "Pf") allK] : List Op) ++
   (gTailOps (fun _ => P) S.pf P.tails (pe + nf + 2)).map (reloc S)

theorem map_reloc_of (S : Seq) {l : List Op} (h : ∀ op ∈ l, reloc S op = op) : l.map (reloc S) = l := by
  conv_rhs => rw [← List.map_id l]
  exact List.map_congr_left h

theorem map_cond {α β : Type} (f : α → β) (c : Bool) (l l' : List α) :
    (cond c l l').map f = cond c (l.map f) (l'.map f) := by cases c <;> rfl

theorem gFinPf_reloc (P : FinP) (hck : P.ck = true) (fi : FinIn) (b : ℕ) :
    (gFinPf P fi b).1.map (reloc P.S) = gFinPfR P fi b := by
  delta gFinPfR
  simp only [gFinPf, hck, cond_true, List.map_append, map_cond, ptsOps_reloc, selOps_reloc,
    gCellsOpsK_reloc, gLvsOps_reloc, padsOps_reloc, List.map_flatMap]
  rw [map_reloc_of P.S (l := [.const (fun _ => .k 1), .const (fun _ => .k (1 + K.u)), .const (fun _ => .k 0)])
    (List.forall_mem_cons.2 ⟨rfl, List.forall_mem_cons.2 ⟨rfl, List.forall_mem_cons.2 ⟨rfl, fun _ h => absurd h (List.not_mem_nil)⟩⟩⟩)]
  simp only [List.map_map, List.map_cons, List.map_nil]
  rfl

/-! ## The relation -/

section Val
variable (impl : OpImpl) (κ : Kind) (inp : Input) (fi : FinIn) (r : Array Val) (P : FinP)

/-- Point `j` of `gPfPts`. -/
def ptPf (j : ℕ) : Array K := ptV r ((gPfPts P fi).getD j [])

/-- The kind's tail `Pₖ[1..]` (`k = 1 … 4`). -/
def tl4 (k : ℕ) : Array K := ptPf fi r P (slotIx P κ (k - 1))

/-- The kind's `P₀`. -/
def rho4 : Array K := ptPf fi r P (slotIx P κ 4)

/-- The `κ′` register's value. -/
def kp4 : F := fv r ((outsOf fi "B'").headD 0)

/-- The public cells' sum `Σ_{k < ncell} κ′^{k+2}·eq(cell_k, P₀)` (`finPf`'s first chain). -/
def cv4 : K := cellsVal4 P.nc (rho4 κ fi r P) (kp4 fi r) (fun j => P.cells.getD j 0) P.ncell 0
  (kp4 fi r * kp4 fi r) 0

/-- **`Ŵ₀(P₀)`** (INT-8's): `rsWeight` at the kind's claim points, and on a node the cells' sum; with
the reserve on (`rsvOps ∧ rsv`, revision 4.4.2) the second chain continues it over the reserve's
cells, `Σ_{i < nrcell} κ′^{2+ncell+i}·eq(rcell_i, P₀)`. -/
def w0V4 : K :=
  impl.rsWeight (ptF r ((List.range 7).map fun p => (coordsR fi "RS1").getD p 0))
      ((P.kv.ptIx κ).map (ptPf fi r P)) (fv r ((coordsR fi "RS1").getD 7 0))
      (if P.kv.node κ then fv r ((outsOf fi "L3β").headD 0) else 1) (rho4 κ fi r P) +
    (if P.kv.node κ then
      (if (P.rsvOps && P.rsv) = true then cellsVal4 P.nc (rho4 κ fi r P) (kp4 fi r)
        (fun j => P.rcells.getD j 0) P.nrcell 0 (kp4 fi r * kp4 fi r * kp4 fi r ^ P.ncell) (cv4 κ fi r P)
       else cv4 κ fi r P) else 0)

/-- **`Ŵ₄(P₄)`**: 3.x's four level steps at the kind's tails. -/
def wV4 : K := lvsV impl fi (rd r) (tl4 κ fi r P) [1, 2, 3, 4] (w0V4 impl κ fi r P)

/-- Pf's challenge `v`. -/
def sfv4 (v : ℕ) : K := (rd r ((chals fi "Pf" P.S.pf).getD v 0)).toK

/-- **The kind's pad**: `1` for `m*`, else its family's. -/
def padV4 : K := if P.kv.selA κ then 1 else padF4 (sfv4 fi r P) P.S.pf (P.fams.getD (famI P κ) 0)

/-- `final̂(sf)` over the relocated final elements. -/
def finHat4 : K :=
  fhVal4 P.S inp (eqTab ((chals fi "Pf" P.S.pf).map fun x => (rd r x).toK).toArray) (List.range (2 ^ P.S.pf)) 0

/-- **INT-8's `finPf` relation**: `claimN(Pf) = Ŵ₄(P₄)·pad·final̂(sf)`, and the kind's exact tail. -/
def relPf4 : Bool :=
  (Val.k (wV4 impl κ fi r P * padV4 κ fi r P * finHat4 inp fi r P)).eqv (rd r (claimN fi "Pf")) &&
    tailOk4 P κ inp

end Val

/-! ## The run -/

section Run
variable (impl : OpImpl) (κ : Kind) (inp : Input)

/-- Two blocks, the second from the first's registers, flags joined. -/
theorem pr_seq2 {A B : List Op} {R : Array Val} {M M' : List Val} {f g : Bool}
    (hA : pureRun impl κ inp A R [] = some (M, f))
    (hB : pureRun impl κ inp B (R ++ M.toArray) [] = some (M', g)) :
    pureRun impl κ inp (A ++ B) R [] = some (M ++ M', f && g) := by
  rw [pureRun_append, hA, Option.bind_some]
  have := pureRun_rebase impl κ inp B R M []
  simp only [List.append_nil] at this
  rw [this, hB]; rfl

/-- A run from `M` on, seen from the file `R ++ M`. -/
theorem pr_rebase {os : List Op} {R : Array Val} {M M' : List Val} {f : Bool}
    (h : pureRun impl κ inp os R M = some (M ++ M', f)) :
    pureRun impl κ inp os (R ++ M.toArray) [] = some (M', f) := by
  have e := pureRun_rebase impl κ inp os R M []
  rw [List.append_nil] at e
  rw [e] at h
  cases h' : pureRun impl κ inp os (R ++ M.toArray) [] with
  | none => rw [h'] at h; cases h
  | some p =>
    rw [h'] at h
    obtain ⟨p1, p2⟩ := p
    simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq, List.append_cancel_left_eq] at h
    rw [h.1, h.2]

/-- **The reserve's cell chain** (`finPf`'s second chain, revision 4.4.2): gated by `o` (`rsvOps`),
`n` more cells from the first chain's accumulator `acc` (value `A`) and last power (the register just
below, value `Pw`), then a `keep` by `sv` (`rsv`) between the continued sum and `A`. -/
theorem run_rsvChain (nc one g h kp : ℕ) (cells : ℕ → KC ℕ) (ρ : Array K) (kpv : F)
    (r : Array Val) (h1 : one < r.size) (hv1 : rd r one = .k 1) (hk : kp < r.size) (hkv : (rd r kp).toF = kpv)
    (hg0 : ∀ v < nc, g + v < r.size ∧ rd r (g + v) = .k (ρ.getD v 0))
    (hh0 : ∀ v < nc, h + v < r.size ∧ rd r (h + v) = .k (1 + ρ.getD v 0)) (hnc : 0 < nc)
    (o : Bool) (sv : KC Bool) (n acc : ℕ) (A : K) (Pw : F) (L : List Val)
    (hacc : acc < r.size + L.length) (hA : rd (r ++ L.toArray) acc = .k A)
    (hpw : 0 < r.size + L.length) (hP : (rd (r ++ L.toArray) (r.size + L.length - 1)).toF = Pw) :
    ∃ M, pureRun impl κ inp (cond o (gCellsOpsK nc one g h kp cells n 0 acc (r.size + L.length - 1)
        (r.size + L.length) ++ [.keep sv (gCellsAccK nc n acc (r.size + L.length)) acc]) [])
        (r ++ L.toArray) [] = some (M, true) ∧
      M.length = cond o ((2 * nc + 3) * n + 1) 0 ∧
      rd (r ++ L.toArray ++ M.toArray) (cond o (r.size + L.length + (2 * nc + 3) * n) acc) =
        .k (if (o && sv κ) = true then cellsVal4 nc ρ kpv (fun j => cells j κ) n 0 Pw A else A) := by
  cases o with
  | false => exact ⟨[], rfl, rfl, by simpa using hA⟩
  | true =>
    obtain ⟨M, hM, hl, hv, -⟩ := run_gCellsOpsK impl κ inp nc one g h kp cells ρ kpv r h1 hv1 hk hkv hg0 hh0
      hnc n 0 acc (r.size + L.length - 1) A Pw L hacc hA (by omega) hP
    set w : Val := if sv κ then .k (cellsVal4 nc ρ kpv (fun j => cells j κ) n 0 Pw A) else .k A
    have hkeep : evalOp impl κ inp (r ++ (L ++ M).toArray)
        (.keep sv (gCellsAccK nc n acc (r.size + L.length)) acc) = .vals [w] true := by
      simp only [evalOp, hv, FR.rd_pre r (M := M) hacc, hA, w]
    have hrun : pureRun impl κ inp (gCellsOpsK nc one g h kp cells n 0 acc (r.size + L.length - 1)
        (r.size + L.length) ++ [.keep sv (gCellsAccK nc n acc (r.size + L.length)) acc]) r L =
        some (L ++ (M ++ [w]), true) := by
      rw [pr_app impl κ inp r hM, pr_op impl κ inp r hkeep]; simp [pureRun]
    refine ⟨M ++ [w], pr_rebase impl κ inp hrun, by simp [hl], ?_⟩
    rw [show r ++ L.toArray ++ (M ++ [w]).toArray = r ++ (L ++ M ++ [w]).toArray by
        simp [Array.append_assoc],
      show cond true (r.size + L.length + (2 * nc + 3) * n) acc = r.size + (L ++ M).length by
        simp [hl]; omega, rd_new1 r (L ++ M) w]
    simp only [Bool.true_and, w]; split <;> rfl

/-- **The slots' selections** (`selOps` for slots `0 … T − 1`, each from the previous' registers). -/
theorem run_selSlots (sel : ℕ → KC Bool) (cand : ℕ → ℕ → Reg) (n : ℕ) (R : Array Val)
    (hc : ∀ s i, i < n → cand s i < R.size) : ∀ T, ∃ M,
    pureRun impl κ inp ((List.range T).flatMap fun s => selOps sel (cand s) n (R.size + s * (n - 1))) R [] =
      some (M, true) ∧ M.length = T * (n - 1) ∧ ∀ s < T, 0 < n →
        selOut (cand s) n (R.size + s * (n - 1)) < R.size + M.length ∧
        rd (R ++ M.toArray) (selOut (cand s) n (R.size + s * (n - 1))) =
          rd R (cand s (selI (fun i => sel i κ) (n - 1)))
  | 0 => ⟨[], rfl, by simp, fun s hs => absurd hs (Nat.not_lt_zero _)⟩
  | T + 1 => by
    obtain ⟨M, hM, hl, hv⟩ := run_selSlots sel cand n R hc T
    have hsz : (R ++ M.toArray).size = R.size + T * (n - 1) := by simp [hl]
    obtain ⟨M', hM', hl', hv'⟩ := run_selOps impl κ inp sel (cand T) n (R ++ M.toArray)
      (fun i hi => Nat.lt_of_lt_of_le (hc T i hi) (by simp))
    rw [hsz] at hM' hv'
    refine ⟨M ++ M', ?_, by simp [hl, hl']; ring, fun s hs hn => ?_⟩
    · rw [List.range_succ, List.flatMap_append, List.flatMap_singleton]
      exact pr_seq impl κ inp hM hM'
    · rcases Nat.lt_succ_iff_lt_or_eq.1 hs with hs | rfl
      · obtain ⟨hb, hr⟩ := hv s hs hn
        refine ⟨Nat.lt_of_lt_of_le hb (by simp), ?_⟩
        rw [show R ++ (M ++ M').toArray = R ++ M.toArray ++ M'.toArray by simp [Array.append_assoc],
          rd_append_left (by simpa using hb), hr]
      · obtain ⟨hb, hr⟩ := hv' hn
        refine ⟨by rw [List.length_append, hl, ← Nat.add_assoc]; exact hb, ?_⟩
        rw [show R ++ (M ++ M').toArray = R ++ M.toArray ++ M'.toArray by simp [Array.append_assoc], hr,
          rd_append_left (hc s _ (lt_of_le_of_lt (selI_le _ _) (by omega)))]

/-- **`finPf` from the level steps on** (blocks 11–17): from a file `R` holding the constants, the
kind's tails at `sb …` and `Ŵ₀(P₀)` at `ce + 1`. -/
theorem flag_pfTail4 (r R : Array Val) (P : FinP) (hS : P.S = seq4) (hnf : 0 < P.fams.length) (fi : FinIn)
    (b sb ce : ℕ) (w0 : K) (hpos : 0 < r.size) (hO : ∀ n, ∀ x ∈ fi.outs.getD n [], x < r.size)
    (hlv : ∀ k ∈ [1, 2, 3, 4], ∀ x ∈ lvRefs fi k, x < r.size) (eR : ExtA r R) (hR : R.size = ce + 2)
    (hb : b + 2 < R.size) (r1one : rd R b = .k 1) (r1cu : rd R (b + 1) = .k (1 + K.u))
    (r1z : rd R (b + 2) = .k 0)
    (hT : ∀ k ∈ [1, 2, 3, 4], sb + (k - 1) < R.size ∧ rd R (sb + (k - 1)) = .ak (tl4 κ fi r P k))
    (hW : rd R (ce + 1) = .k w0) :
    ∃ L, pureRun impl κ inp
      (lvsOps fi b (b + 1) sb [1, 2, 3, 4] (ce + 1) (ce + 2) ++
       ([.packK (chals fi "Pf" P.S.pf), .eqTableK (ce + 2 + lvsW fi [1, 2, 3, 4])] ++
       ((fhOps (ce + 2 + lvsW fi [1, 2, 3, 4] + 1) (List.range (2 ^ P.S.pf)) (b + 2)
          (ce + 2 + lvsW fi [1, 2, 3, 4] + 2)).map (reloc P.S) ++
       (padsOps b (chals fi "Pf" P.S.pf) P.S.pf P.fams (ce + 2 + lvsW fi [1, 2, 3, 4] + 2 + 4 * 2 ^ P.S.pf) ++
       (selOps (fun i κ => decide (P.kv.fsel κ = i))
          (padsReg b P.S.pf P.fams (ce + 2 + lvsW fi [1, 2, 3, 4] + 2 + 4 * 2 ^ P.S.pf)) P.fams.length
          (ce + 2 + lvsW fi [1, 2, 3, 4] + 2 + 4 * 2 ^ P.S.pf + (P.fams.map (padW P.S.pf)).sum) ++
       ([.keep (fun κ => P.kv.selA κ) b (selOut (padsReg b P.S.pf P.fams
            (ce + 2 + lvsW fi [1, 2, 3, 4] + 2 + 4 * 2 ^ P.S.pf)) P.fams.length
            (ce + 2 + lvsW fi [1, 2, 3, 4] + 2 + 4 * 2 ^ P.S.pf + (P.fams.map (padW P.S.pf)).sum)),
         .mulK (lvsOut fi [1, 2, 3, 4] (ce + 1) (ce + 2))
           (ce + 2 + lvsW fi [1, 2, 3, 4] + 2 + 4 * 2 ^ P.S.pf + (P.fams.map (padW P.S.pf)).sum +
             (P.fams.length - 1)),
         .mulK (ce + 2 + lvsW fi [1, 2, 3, 4] + 2 + 4 * 2 ^ P.S.pf + (P.fams.map (padW P.S.pf)).sum +
             P.fams.length) (fhOut (List.range (2 ^ P.S.pf)) (b + 2) (ce + 2 + lvsW fi [1, 2, 3, 4] + 2)),
         .assertEq (ce + 2 + lvsW fi [1, 2, 3, 4] + 2 + 4 * 2 ^ P.S.pf + (P.fams.map (padW P.S.pf)).sum +
             P.fams.length + 1) (claimN fi "Pf") allK] ++
       (gTailOps (fun _ => P) P.S.pf P.tails (ce + 2 + lvsW fi [1, 2, 3, 4] + 2 + 4 * 2 ^ P.S.pf +
          (P.fams.map (padW P.S.pf)).sum + P.fams.length + 2)).map (reloc P.S)))))))
      R [] = some (L, (Val.k (lvsV impl fi (rd r) (tl4 κ fi r P) [1, 2, 3, 4] w0 * padV4 κ fi r P *
        finHat4 inp fi r P)).eqv (rd r (claimN fi "Pf")) && tailOk4 P κ inp) := by
  have app0 : ∀ X : Array Val, X ++ ([] : List Val).toArray = X := fun X => by simp
  have hcNr : claimN fi "Pf" < r.size := getLastD_lt (outsOf_lt hpos hO "Pf") hpos
  have hsfm : ∀ x ∈ chals fi "Pf" P.S.pf, x < r.size := chals_lt hpos hO "Pf" _
  have hsf : ∀ v, (chals fi "Pf" P.S.pf).getD v 0 < r.size := getD_lt hpos hsfm
  generalize hlw : lvsW fi [1, 2, 3, 4] = lw
  -- B11: the levels
  obtain ⟨M11, hB11, hl11, hv11⟩ := run_lvsOps impl κ inp fi b (b + 1) sb (tl4 κ fi r P) R
    (by omega) r1one (by omega) r1cu [1, 2, 3, 4] (ce + 1) w0 R le_rfl (fun _ _ => rfl)
    (fun k hk => ⟨fun x hx => Nat.lt_of_lt_of_le (hlv k hk x hx) eR.1, hT k hk⟩) (by omega) hW
  rw [hR] at hB11 hv11
  rw [lvsV_congr impl fi (tl4 κ fi r P) r.size (fun x hx => eR.rd hx) [1, 2, 3, 4] _ hlv] at hv11
  set R11 := R ++ M11.toArray with hR11
  have sR11 : R11.size = ce + 2 + lw := by simp [R11, hR, hl11, hlw]
  have e011 : ExtA r R11 := eR.trans (ExtA.app R M11)
  have eR11 : ExtA R R11 := ExtA.app R M11
  -- B12: `sf` and `eq(sf, ·)`
  set sfV := ((chals fi "Pf" P.S.pf).map fun x => (rd r x).toK).toArray
  set V12 : List Val := [.ak sfV, .ak (eqTab sfV)]
  have hB12 : pureRun impl κ inp [.packK (chals fi "Pf" P.S.pf), .eqTableK (ce + 2 + lw)] R11 [] =
      some (V12, true) := by
    have hm : (chals fi "Pf" P.S.pf).map (fun x => (rd R11 x).toK) =
        (chals fi "Pf" P.S.pf).map (fun x => (rd r x).toK) :=
      List.map_congr_left fun x hx => by rw [e011.rd (hsfm x hx)]
    rw [← sR11]
    simp only [pureRun, evalOp, List.nil_append, app0, rd_app0, hm, Option.map_some, Bool.and_true]
    rfl
  set R12 := R11 ++ V12.toArray with hR12
  have sR12 : R12.size = ce + 2 + lw + 2 := by simp [R12, sR11, V12]
  have eR12 : ExtA R R12 := eR11.trans (ExtA.app R11 V12)
  -- B13: `final̂(sf)`
  obtain ⟨M13, hB13, hl13, hv13⟩ := run_fhOps4 impl κ inp P.S R12 (ce + 2 + lw + 1) (eqTab sfV)
    (by rw [sR12]; omega) (by rw [hR12, ← sR11, rd_app]; rfl) (List.range (2 ^ P.S.pf)) (b + 2) 0 []
    (by rw [List.length_nil, Nat.add_zero, sR12]; omega)
    (by rw [app0, eR12.rd (by omega), r1z])
  simp only [List.length_nil, Nat.add_zero, List.nil_append, sR12, List.length_range] at hB13 hv13 hl13
  set R13 := R12 ++ M13.toArray with hR13
  have sR13 : R13.size = ce + 2 + lw + 2 + 4 * 2 ^ P.S.pf := by simp [R13, sR12, hl13]
  have eR13 : ExtA R R13 := eR12.trans (ExtA.app R12 M13)
  have e013 : ExtA r R13 := eR.trans eR13
  -- B14: the pad chains
  obtain ⟨M14, hB14, hl14, hv14⟩ := run_padsOps impl κ inp b (chals fi "Pf" P.S.pf) (sfv4 fi r P) P.S.pf
    P.fams R13 (Nat.lt_of_lt_of_le (by omega : b < R.size) eR13.1)
    (by rw [eR13.rd (by clear * - hb; omega), r1one])
    (fun v _ => ⟨Nat.lt_of_lt_of_le (hsf v) e013.1, by rw [e013.rd (hsf v)]; rfl⟩)
  rw [sR13] at hB14 hv14
  set R14 := R13 ++ M14.toArray with hR14
  have sR14 : R14.size = ce + 2 + lw + 2 + 4 * 2 ^ P.S.pf + (P.fams.map (padW P.S.pf)).sum := by
    simp [R14, sR13, hl14]
  have e1314 : ExtA R13 R14 := ExtA.app R13 M14
  -- B15: the kind's pad
  have hv14' : ∀ i < P.fams.length, padsReg b P.S.pf P.fams (ce + 2 + lw + 2 + 4 * 2 ^ P.S.pf) i < R14.size ∧
      rd R14 (padsReg b P.S.pf P.fams (ce + 2 + lw + 2 + 4 * 2 ^ P.S.pf) i) =
        .k (padF4 (sfv4 fi r P) P.S.pf (P.fams.getD i 0)) := fun i hi => by
    obtain ⟨h1, h2⟩ := hv14 i hi
    exact ⟨by rw [sR14, ← hl14]; exact h1, h2⟩
  obtain ⟨M15, hB15, hl15, hv15⟩ := run_selOps impl κ inp (fun i κ => decide (P.kv.fsel κ = i))
    (padsReg b P.S.pf P.fams (ce + 2 + lw + 2 + 4 * 2 ^ P.S.pf)) P.fams.length R14
    (fun i hi => (hv14' i hi).1)
  rw [sR14] at hB15 hv15
  obtain ⟨-, hr15⟩ := hv15 hnf
  set pe := ce + 2 + lw + 2 + 4 * 2 ^ P.S.pf + (P.fams.map (padW P.S.pf)).sum with hpe
  set R15 := R14 ++ M15.toArray with hR15
  have sR15 : R15.size = pe + (P.fams.length - 1) := by simp [R15, sR14, hl15, hpe]
  have e1415 : ExtA R14 R15 := ExtA.app R14 M15
  have eR15 : ExtA R R15 := eR13.trans (e1314.trans e1415)
  have r15pad : rd R15 (selOut (padsReg b P.S.pf P.fams (ce + 2 + lw + 2 + 4 * 2 ^ P.S.pf)) P.fams.length pe) =
      .k (padF4 (sfv4 fi r P) P.S.pf (P.fams.getD (famI P κ) 0)) := by
    rw [hr15]; exact (hv14' _ (famI_lt P κ hnf)).2
  have hWo : lvsOut fi [1, 2, 3, 4] (ce + 1) (ce + 2) < R11.size := by
    by_contra hc'
    have h0 := hv11; rw [rd, Array.getElem?_eq_none (by simpa [R11] using hc')] at h0; cases h0
  have hFo : fhOut (List.range (2 ^ P.S.pf)) (b + 2) (ce + 2 + lw + 2) < R13.size := by
    by_contra hc'
    have h0 := hv13; rw [rd, Array.getElem?_eq_none (by simpa [R13] using hc')] at h0; cases h0
  have e1115 : ExtA R11 R15 := (ExtA.app R11 V12).trans ((ExtA.app R12 M13).trans (e1314.trans e1415))
  have e1315 : ExtA R13 R15 := e1314.trans e1415
  have r15W : rd R15 (lvsOut fi [1, 2, 3, 4] (ce + 1) (ce + 2)) =
      .k (lvsV impl fi (rd r) (tl4 κ fi r P) [1, 2, 3, 4] w0) := by rw [e1115.rd hWo, hv11]
  have r15F : rd R15 (fhOut (List.range (2 ^ P.S.pf)) (b + 2) (ce + 2 + lw + 2)) = .k (finHat4 inp fi r P) := by
    rw [e1315.rd hFo, hv13]; rfl
  have r15one : rd R15 b = .k 1 := by rw [eR15.rd (by clear * - hb; omega), r1one]
  have hsel : selOut (padsReg b P.S.pf P.fams (ce + 2 + lw + 2 + 4 * 2 ^ P.S.pf)) P.fams.length pe < R15.size := by
    by_contra hc'
    have h0 := r15pad; rw [rd, Array.getElem?_eq_none (by simpa using hc')] at h0; cases h0
  obtain ⟨V16, hB16⟩ : ∃ V16, pureRun impl κ inp
      [.keep (fun κ => P.kv.selA κ) b (selOut (padsReg b P.S.pf P.fams
          (ce + 2 + lw + 2 + 4 * 2 ^ P.S.pf)) P.fams.length pe),
       .mulK (lvsOut fi [1, 2, 3, 4] (ce + 1) (ce + 2)) (pe + (P.fams.length - 1)),
       .mulK (pe + P.fams.length) (fhOut (List.range (2 ^ P.S.pf)) (b + 2) (ce + 2 + lw + 2)),
       .assertEq (pe + P.fams.length + 1) (claimN fi "Pf") allK] R15 [] =
      some (V16, (Val.k (lvsV impl fi (rd r) (tl4 κ fi r P) [1, 2, 3, 4] w0 * padV4 κ fi r P *
        finHat4 inp fi r P)).eqv (rd r (claimN fi "Pf"))) := by
    rw [show pe + P.fams.length + 1 = R15.size + 2 by rw [sR15]; clear * - hnf; omega,
      show pe + P.fams.length = R15.size + 1 by rw [sR15]; clear * - hnf; omega,
      show pe + (P.fams.length - 1) = R15.size from sR15.symm]
    simp only [pureRun, evalOp, List.nil_append, List.cons_append, app0, rd_app, rd_app0,
      rd_app_left _ _ (show b < R15.size by have := eR15.1; clear * - this hb; omega), r15one,
      rd_app_left _ _ hsel, r15pad,
      rd_app_left _ _ (Nat.lt_of_lt_of_le hcNr (eR.trans eR15).1), (eR.trans eR15).rd hcNr,
      rd_app_left _ _ (Nat.lt_of_lt_of_le hWo e1115.1), rd_app_left _ _ (Nat.lt_of_lt_of_le hFo e1315.1),
      r15W, r15F, List.getD_cons_succ, List.getD_cons_zero, Option.map_some, allK, Bool.not_true,
      Bool.false_or, Bool.true_and, Bool.and_true]
    refine ex_some ?_
    refine congrArg (fun z : K => (Val.k z).eqv (rd r (claimN fi "Pf"))) ?_
    simp only [padV4]
    split_ifs <;> simp [toK_k]
  set R16 := R15 ++ V16.toArray with hR16
  obtain ⟨M17, hB17⟩ := run_gTailOps impl κ inp P.S P P.tails R16
  have hl16 : V16.length = 3 := by
    have := pureRun_len impl κ inp R15 _ [] V16 _ hB16; simpa [opsOut, Op.outs] using this
  have sR16 : R16.size = pe + P.fams.length + 2 := by
    simp [R16, sR15, hl16]; clear * - hnf; omega
  rw [sR16] at hB17
  exact ⟨_, pr_seq impl κ inp hB11 (pr_seq impl κ inp hB12 (pr_seq impl κ inp hB13
    (pr_seq impl κ inp hB14 (pr_seq impl κ inp hB15 (pr_seq2 impl κ inp hB16 hB17)))))⟩


set_option maxHeartbeats 1000000 in
/-- **`flag_gFinPf4`** (3.x's `flag_finPf` at INT-8's uniform `finPf`): the relocated field of a
fixed-kind program with kind-table cells asks nothing; its flag is `relPf4`. -/
theorem flag_gFinPf4 (r : Array Val) (P : FinP) (hS : P.S = seq4) (hnc : 0 < P.nc)
    (hnf : 0 < P.fams.length) (fi : FinIn) (hpos : 0 < r.size)
    (hO : ∀ n, ∀ x ∈ fi.outs.getD n [], x < r.size)
    (hpts : ∀ s ∈ gPfPts P fi, ∀ x ∈ s, x.Ok r.size)
    (hix : ∀ j ∈ P.kv.ptIx κ, j < (gPfPts P fi).length)
    (hlv : ∀ k ∈ [1, 2, 3, 4], ∀ x ∈ lvRefs fi k, x < r.size) :
    ∃ L, pureRun impl κ inp (gFinPfR P fi r.size) r [] = some (L, relPf4 impl κ inp fi r P) := by
  have app0 : ∀ X : Array Val, X ++ ([] : List Val).toArray = X := fun X => by simp
  have hrs : ∀ p, (coordsR fi "RS1").getD p 0 < r.size := getD_lt hpos (coordsR_lt hpos hO "RS1")
  have hkpr : (outsOf fi "B'").headD 0 < r.size := headD_lt (outsOf_lt hpos hO "B'") hpos
  have hcNr : claimN fi "Pf" < r.size := getLastD_lt (outsOf_lt hpos hO "Pf") hpos
  have hβr : (outsOf fi "L3β").headD 0 < r.size := headD_lt (outsOf_lt hpos hO "L3β") hpos
  have hsfm : ∀ x ∈ chals fi "Pf" P.S.pf, x < r.size := chals_lt hpos hO "Pf" _
  have hsf : ∀ v, (chals fi "Pf" P.S.pf).getD v 0 < r.size := getD_lt hpos hsfm
  have hlvs : ∀ (one cu Ts W b' : ℕ), gLvsOps P.S fi one cu Ts [1, 2, 3, 4] W b' =
      lvsOps fi one cu Ts [1, 2, 3, 4] W b' := fun _ _ _ _ _ => by rw [hS, gLvsOps_4]
  delta gFinPfR
  simp only [hlvs, List.append_assoc]
  generalize hpw : ptsW (gPfPts P fi) = pw
  set b := r.size with hb
  set kp := (outsOf fi "B'").headD 0 with hkp
  set kpv := kp4 fi r with hkpv
  set Pp := ptsOut (gPfPts P fi) (b + 3)
  -- B1: the constants
  set V1 : List Val := [.k 1, .k (1 + K.u), .k 0]
  have hB1 : pureRun impl κ inp [Op.const fun _ => Val.k 1, Op.const fun _ => Val.k (1 + K.u),
      Op.const fun _ => Val.k 0] r [] = some (V1, true) := rfl
  set R1 := r ++ V1.toArray with hR1
  have sR1 : R1.size = b + 3 := by simp [R1, V1, hb]
  have r1one : rd R1 b = .k 1 := by rw [hR1, hb, rd_app0]; rfl
  have r1cu : rd R1 (b + 1) = .k (1 + K.u) := by rw [hR1, hb, rd_app]; rfl
  have r1z : rd R1 (b + 2) = .k 0 := by rw [hR1, hb, rd_app]; rfl
  have e01 : ExtA r R1 := ExtA.app r V1
  -- B2: the points
  obtain ⟨M2, hB2, hl2, hv2⟩ := run_ptsOps impl κ inp R1 b (b + 2) (by omega) r1one (by omega) r1z
    (gPfPts P fi) [] (fun s hs x hx => by
      have := hpts s hs x hx
      cases x with
      | f y => exact Nat.lt_of_lt_of_le this e01.1
      | k y => exact Nat.lt_of_lt_of_le this e01.1
      | c v => trivial)
  simp only [List.length_nil, Nat.add_zero, List.nil_append, sR1] at hB2 hv2
  set R2 := R1 ++ M2.toArray with hR2
  have sR2 : R2.size = b + 3 + pw := by simp [R2, sR1, hl2, hpw]
  have e12 : ExtA R1 R2 := ExtA.app R1 M2
  have hPv : ∀ j < (gPfPts P fi).length, rd R2 (Pp j) = .ak (ptPf fi r P j) ∧ Pp j < R2.size := by
    intro j hj
    refine ⟨?_, ?_⟩
    · rw [hv2 j hj, hR1, ptV_app r V1 _ (hpts _ (by
        rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hj]; exact List.getElem_mem _))]; rfl
    · rw [sR2, ← hpw]; exact ptsOut_lt _ _ _ hj
  -- B3: the families' selections
  obtain ⟨M3, hB3, hl3, hv3⟩ := run_selSlots impl κ inp (fun i κ => decide (P.kv.fsel κ = i))
    (fun s i => pfCand P Pp i s) P.fams.length R2
    (fun s i hi => by rw [pfCand_eq]; exact (hPv _ (candIx_lt P fi hi s)).2) 5
  rw [sR2] at hB3 hv3
  set R3 := R2 ++ M3.toArray with hR3
  have sR3 : R3.size = b + 3 + pw + 5 * (P.fams.length - 1) := by simp [R3, sR2, hl3]
  have e23 : ExtA R2 R3 := ExtA.app R2 M3
  have r3sel : ∀ s < 5, selOut (fun i => pfCand P Pp i s) P.fams.length (b + 3 + pw + s * (P.fams.length - 1)) < R3.size ∧
      rd R3 (selOut (fun i => pfCand P Pp i s) P.fams.length (b + 3 + pw + s * (P.fams.length - 1))) =
        .ak (ptPf fi r P (candIx P (famI P κ) s)) := by
    intro s hs
    obtain ⟨hb3, hr3⟩ := hv3 s hs hnf
    refine ⟨by rw [sR3]; simpa [hl3] using hb3, ?_⟩
    rw [hr3, pfCand_eq]; exact (hPv _ (candIx_lt P fi (famI_lt P κ hnf) s)).1
  -- B4: the kind's slots
  have hB4 := run_base impl κ inp R3 ((List.range 5).map fun s =>
      Op.keep (fun κ => P.kv.selA κ) (pfCandA P Pp s)
        (selOut (fun i => pfCand P Pp i s) P.fams.length (b + 3 + pw + s * (P.fams.length - 1)))) []
    (fun op hop Y => by
      obtain ⟨s, hs, rfl⟩ := List.mem_map.mp hop
      have hs' := List.mem_range.mp hs
      have hA : pfCandA P Pp s < R3.size := by
        rw [pfCandA_eq]; exact Nat.lt_of_lt_of_le (hPv _ (candAIx_lt P fi s)).2 e23.1
      simp only [evalOp, rd_app_left _ _ hA, rd_app_left _ _ (r3sel s hs').1])
    (fun op hop => by obtain ⟨s, -, rfl⟩ := List.mem_map.mp hop; exact ⟨_, rfl⟩)
  set V4 : List Val := (List.range 5).map fun s => .ak (ptPf fi r P (slotIx P κ s))
  have hV4 : ((List.range 5).map fun s =>
      Op.keep (fun κ => P.kv.selA κ) (pfCandA P Pp s)
        (selOut (fun i => pfCand P Pp i s) P.fams.length (b + 3 + pw + s * (P.fams.length - 1)))).map (baseVal impl κ inp R3) = V4 := by
    simp only [List.map_map, V4]
    refine List.map_congr_left fun s hs => ?_
    have hs' := List.mem_range.mp hs
    simp only [Function.comp_apply, baseVal, evalOp, (r3sel s hs').2, slotIx]
    rw [pfCandA_eq, e23.rd (hPv _ (candAIx_lt P fi s)).2, (hPv _ (candAIx_lt P fi s)).1]
    split_ifs <;> rfl
  rw [hV4, List.nil_append] at hB4
  set sb := b + 3 + pw + 5 * (P.fams.length - 1) with hsb
  set R4 := R3 ++ V4.toArray with hR4
  have sR4 : R4.size = sb + 5 := by simp [R4, sR3, V4]
  have e34 : ExtA R3 R4 := ExtA.app R3 V4
  have r4T : ∀ s < 5, rd R4 (sb + s) = .ak (ptPf fi r P (slotIx P κ s)) := by
    intro s hs; rw [hR4, ← sR3, rd_app]; simp [V4, hs]
  -- B5: `rsWeight`
  have e03 : ExtA r R3 := e01.trans (e12.trans e23)
  have e04 : ExtA r R4 := e03.trans e34
  have rr : ∀ x < r.size, ∀ L : List Val, rd (R4 ++ L.toArray) x = rd r x := fun x hx L => by
    rw [rd_app_left R4 L (Nat.lt_of_lt_of_le hx e04.1), e04.rd hx]
  have hPr : ∀ j ∈ P.kv.ptIx κ, Pp j < R4.size := fun j hj =>
    Nat.lt_of_lt_of_le (hPv j (hix j hj)).2 (e23.trans e34).1
  have hptsL : ∀ L : List Val, (P.kv.ptIx κ).map (fun x => (rd (R4 ++ L.toArray) (Pp x)).toAK) =
      (P.kv.ptIx κ).map (ptPf fi r P) := fun L => List.map_congr_left fun j hj => by
    rw [rd_app_left _ _ (hPr j hj), (e23.trans e34).rd (hPv j (hix j hj)).2, (hPv j (hix j hj)).1]; rfl
  have hP4 : sb + 4 < R4.size := by rw [sR4]; omega
  have r4P : rd R4 (sb + 4) = .ak (rho4 κ fi r P) := r4T 4 (by omega)
  set rsW := impl.rsWeight (ptF r ((List.range 7).map fun p => (coordsR fi "RS1").getD p 0))
      ((P.kv.ptIx κ).map (ptPf fi r P)) (fv r ((coordsR fi "RS1").getD 7 0))
      (if P.kv.node κ then fv r ((outsOf fi "L3β").headD 0) else 1) (rho4 κ fi r P)
  set V5 : List Val := [.af (ptF r ((List.range 7).map fun p => (coordsR fi "RS1").getD p 0)), .k rsW]
  have hB5 : pureRun impl κ inp
      [.packF ((List.range 7).map fun p => (coordsR fi "RS1").getD p 0),
       .rsWeight (sb + 5) (fun κ => (P.kv.ptIx κ).map Pp) ((coordsR fi "RS1").getD 7 0)
         ((outsOf fi "L3β").headD 0) (fun κ => P.kv.node κ) (sb + 4)] R4 [] = some (V5, true) := by
    have hrpp : (List.range 7).map (fun x => (rd R4 ((coordsR fi "RS1").getD x 0)).toF) =
        (List.range 7).map (fun x => fv r ((coordsR fi "RS1").getD x 0)) :=
      List.map_congr_left fun p _ => by rw [e04.rd (hrs p)]
    rw [show sb + 5 = R4.size from sR4.symm]
    simp only [pureRun, evalOp, List.nil_append, List.cons_append, rd_app, rd_app0,
      rd_app_left _ _ hP4, r4P, List.map_map, Function.comp_def, hptsL,
      rr _ (hrs 7), rr _ hβr, List.getD_cons_succ, List.getD_cons_zero, Option.map_some, Bool.and_true,
      Array.append_empty, hrpp]
    rfl
  set R5 := R4 ++ V5.toArray with hR5
  have sR5 : R5.size = sb + 5 + 2 := by simp [R5, sR4, V5]
  have e45 : ExtA R4 R5 := ExtA.app R4 V5
  -- B6, B7: `ρ_v` and `1 + ρ_v`
  have hB6 := run_base impl κ inp R5 ((List.range P.nc).map fun v => Op.getK (sb + 4) v) []
    (fun op hop Y => by
      obtain ⟨v, -, rfl⟩ := List.mem_map.mp hop
      simp only [evalOp, rd_app_left _ _ (show sb + 4 < R5.size by rw [sR5]; omega)])
    (fun op hop => by obtain ⟨v, -, rfl⟩ := List.mem_map.mp hop; exact ⟨_, rfl⟩)
  set V6 : List Val := (List.range P.nc).map fun v => .k ((rho4 κ fi r P).getD v 0)
  have hV6 : ((List.range P.nc).map fun v => Op.getK (sb + 4) v).map (baseVal impl κ inp R5) = V6 := by
    simp only [List.map_map, V6]
    refine List.map_congr_left fun v _ => ?_
    simp only [Function.comp_apply, baseVal, evalOp, e45.rd hP4, r4P, Val.toAK]
  rw [hV6, List.nil_append] at hB6
  set R6 := R5 ++ V6.toArray with hR6
  have sR6 : R6.size = sb + 5 + 2 + P.nc := by simp [R6, sR5, V6]
  have e56 : ExtA R5 R6 := ExtA.app R5 V6
  have r6 : ∀ v < P.nc, rd R6 (sb + 5 + 2 + v) = .k ((rho4 κ fi r P).getD v 0) := fun v hv => by
    rw [hR6, ← sR5, rd_app]; simp [V6, hv]
  have e16 : ExtA R1 R6 := e12.trans (e23.trans (e34.trans (e45.trans e56)))
  have r6one : rd R6 b = .k 1 := by rw [e16.rd (by rw [sR1]; omega), r1one]
  have hB7 := run_base impl κ inp R6 ((List.range P.nc).map fun v => Op.addK b (sb + 5 + 2 + v)) []
    (fun op hop Y => by
      obtain ⟨v, hv, rfl⟩ := List.mem_map.mp hop
      have : sb + 5 + 2 + v < R6.size := by rw [sR6]; simp at hv; omega
      simp only [evalOp, rd_app_left _ _ this, rd_app_left _ _ (show b < R6.size by rw [sR6]; omega)])
    (fun op hop => by obtain ⟨v, -, rfl⟩ := List.mem_map.mp hop; exact ⟨_, rfl⟩)
  set V7 : List Val := (List.range P.nc).map fun v => .k (1 + (rho4 κ fi r P).getD v 0)
  have hV7 : ((List.range P.nc).map fun v => Op.addK b (sb + 5 + 2 + v)).map (baseVal impl κ inp R6) = V7 := by
    simp only [List.map_map, V7]
    refine List.map_congr_left fun v hv => ?_
    simp only [Function.comp_apply, baseVal, evalOp, r6one, r6 v (List.mem_range.mp hv), toK_k]
  rw [hV7, List.nil_append] at hB7
  set R7 := R6 ++ V7.toArray with hR7
  have sR7 : R7.size = sb + 5 + (2 + 2 * P.nc) := by simp [R7, sR6, V7]; omega
  have e67 : ExtA R6 R7 := ExtA.app R6 V7
  -- B8: `κ′²`
  have e07 : ExtA r R7 := e04.trans (e45.trans (e56.trans e67))
  have hB8 : pureRun impl κ inp [.mulF kp kp] R7 [] = some ([.f (kpv * kpv)], true) := by
    simp only [pureRun, evalOp, List.nil_append, Array.append_empty, e07.rd hkpr]; rfl
  set R8 := R7 ++ [Val.f (kpv * kpv)].toArray with hR8
  have sR8 : R8.size = sb + 5 + (2 + 2 * P.nc) + 1 := by simp [R8, sR7]
  have e78 : ExtA R7 R8 := ExtA.app R7 _
  -- B9: the cells
  have e18 : ExtA R1 R8 := e16.trans (e67.trans e78)
  have e58 : ExtA R5 R8 := e56.trans (e67.trans e78)
  have h8one : b < R8.size := by rw [sR8]; omega
  have r8one : rd R8 b = .k 1 := by rw [e18.rd (by rw [sR1]; omega), r1one]
  have h8kp : kp < R8.size := Nat.lt_of_lt_of_le hkpr (e07.trans e78).1
  have r8kp : (rd R8 kp).toF = kpv := by rw [(e07.trans e78).rd hkpr]; rfl
  have r8g : ∀ v < P.nc, sb + 5 + 2 + v < R8.size ∧ rd R8 (sb + 5 + 2 + v) = .k ((rho4 κ fi r P).getD v 0) :=
    fun v hv => ⟨by rw [sR8]; clear * - hv; omega,
      by rw [(e67.trans e78).rd (by rw [sR6]; clear * - hv; omega), r6 v hv]⟩
  have r8h : ∀ v < P.nc, sb + 5 + (P.nc + 2) + v < R8.size ∧
      rd R8 (sb + 5 + (P.nc + 2) + v) = .k (1 + (rho4 κ fi r P).getD v 0) :=
    fun v hv => ⟨by rw [sR8]; clear * - hv; omega, by
      rw [show sb + 5 + (P.nc + 2) + v = R6.size + v by rw [sR6]; clear * -; omega,
        e78.rd (by rw [sR7, sR6]; clear * - hv; omega), hR7, rd_app]; simp [V7, hv]⟩
  obtain ⟨M9, hB9, hl9, hv9, hp9⟩ := run_gCellsOpsK impl κ inp P.nc b (sb + 5 + 2) (sb + 5 + (P.nc + 2)) kp
    (fun j _ => P.cells.getD j 0) (rho4 κ fi r P) kpv R8 h8one r8one h8kp r8kp r8g r8h hnc
    P.ncell 0 (b + 2) (sb + 5 + (2 + 2 * P.nc)) 0 (kpv * kpv) []
    (by rw [List.length_nil, Nat.add_zero, sR8, hsb]; clear * -; omega)
    (by rw [app0, e18.rd (by rw [sR1]; omega), r1z])
    (by rw [List.length_nil, Nat.add_zero, sR8, hsb]; clear * -; omega)
    (by rw [app0, hR8, ← sR7, rd_app0]; rfl)
  simp only [List.length_nil, Nat.add_zero, List.nil_append, sR8] at hB9 hv9 hp9
  rw [gCellsPwK_eq] at hp9
  set R9 := R8 ++ M9.toArray with hR9
  set c9 := sb + 5 + (2 + 2 * P.nc) + 1 + (2 * P.nc + 3) * P.ncell with hc9
  have sR9 : R9.size = c9 := by simp [R9, sR8, hl9, hc9]
  have hsz9 : R8.size + M9.length = c9 := by rw [sR8, hl9]
  have e89 : ExtA R8 R9 := ExtA.app R8 M9
  set cv := cellsVal4 P.nc (rho4 κ fi r P) kpv (fun j => P.cells.getD j 0) P.ncell 0 (kpv * kpv) 0
  set acc9 := gCellsAccK P.nc P.ncell (b + 2) (sb + 5 + (2 + 2 * P.nc) + 1) with hacc9
  have hca : acc9 < R9.size := by
    by_contra hc'
    have h0 := hv9; rw [rd, Array.getElem?_eq_none (by simpa using hc')] at h0; cases h0
  -- B9′: the reserve's chain (revision 4.4.2), gated by `rsvOps`, kept by `rsv`
  obtain ⟨Mr, hBr, hlr, hvr⟩ := run_rsvChain impl κ inp P.nc b (sb + 5 + 2) (sb + 5 + (P.nc + 2)) kp
    (fun j _ => P.rcells.getD j 0) (rho4 κ fi r P) kpv R8 h8one r8one h8kp r8kp r8g r8h hnc
    P.rsvOps (fun _ => P.rsv) P.nrcell acc9 cv (kpv * kpv * kpv ^ P.ncell) M9
    (by rw [hsz9, ← sR9]; exact hca) hv9 (by rw [hsz9]; omega) (by rw [hsz9]; exact hp9)
  rw [hsz9] at hBr hvr
  set ce := cond P.rsvOps (c9 + (2 * P.nc + 3) * P.nrcell + 1) c9 with hce
  set R9r := R9 ++ Mr.toArray with hR9r
  have sR9r : R9r.size = ce := by
    simp only [R9r, Array.size_append, List.size_toArray, hlr, sR9, hce]
    cases P.rsvOps <;> simp only [cond_true, cond_false] <;> omega
  have hc9ce : c9 ≤ ce := by rw [hce]; cases P.rsvOps <;> simp only [cond_true, cond_false] <;> omega
  have e99 : ExtA R9 R9r := ExtA.app R9 Mr
  -- B10: `Ŵ₀(P₀)`
  have e59 : ExtA R5 R9r := (e58.trans e89).trans e99
  have r9w : rd R9r (sb + 5 + 1) = .k rsW := by
    rw [e59.rd (by rw [sR5]; omega), hR5, ← sR4, rd_app]; rfl
  have r9z : rd R9r (b + 2) = .k 0 := by rw [((e18.trans e89).trans e99).rd (by rw [sR1]; omega), r1z]
  set cvT : K := if (P.rsvOps && P.rsv) = true then cellsVal4 P.nc (rho4 κ fi r P) kpv
    (fun j => P.rcells.getD j 0) P.nrcell 0 (kpv * kpv * kpv ^ P.ncell) cv else cv with hcvT
  have hcr : cond P.rsvOps (c9 + (2 * P.nc + 3) * P.nrcell) acc9 < R9r.size := by
    by_contra hc'
    have h0 := hvr; rw [rd, Array.getElem?_eq_none (by simpa using hc')] at h0; cases h0
  set V10 : List Val := [if P.kv.node κ then .k cvT else .k 0, .k (w0V4 impl κ fi r P)]
  have hB10 : pureRun impl κ inp
      [.keep (fun κ => P.kv.node κ) (cond P.rsvOps (c9 + (2 * P.nc + 3) * P.nrcell) acc9) (b + 2),
       .addK (sb + 5 + 1) ce] R9r [] = some (V10, true) := by
    rw [← sR9r]
    simp only [pureRun, evalOp, List.nil_append, List.cons_append, rd_app, rd_app0, app0,
      rd_app_left _ _ (show sb + 5 + 1 < R9r.size by rw [sR9r]; have := hc9ce; clear * - this hc9; omega),
      rd_app_left _ _ (show b + 2 < R9r.size by rw [sR9r]; have := hc9ce; clear * - this hc9 hsb; omega),
      rd_app_left _ _ hcr, r9w, r9z, hvr,
      List.getD_cons_succ, List.getD_cons_zero, Option.map_some, Bool.and_true]
    simp only [V10, w0V4, cv4, cv, cvT, toK_k, rsW, kpv, kp4]
    cases P.kv.node κ <;> simp <;> rfl
  set R10 := R9r ++ V10.toArray with hR10
  have sR10 : R10.size = ce + 2 := by simp [R10, sR9r, V10]
  have e910 : ExtA R9r R10 := ExtA.app R9r V10
  have r10w : rd R10 (ce + 1) = .k (w0V4 impl κ fi r P) := by rw [hR10, ← sR9r, rd_app]; rfl
  have e010 : ExtA r R10 := e07.trans (e78.trans (e89.trans (e99.trans e910)))
  have e410 : ExtA R4 R10 := e45.trans (e59.trans e910)
  have e110 : ExtA R1 R10 := e18.trans (e89.trans (e99.trans e910))
  obtain ⟨LT, hT⟩ := flag_pfTail4 impl κ inp r R10 P hS hnf fi b sb ce (w0V4 impl κ fi r P) hpos hO hlv
    e010 sR10 (by have := e110.1; rw [sR1] at this; exact this)
    (by rw [e110.rd (by rw [sR1]; omega), r1one])
    (by rw [e110.rd (by rw [sR1]; omega), r1cu]) (by rw [e110.rd (by rw [sR1]; omega), r1z])
    (fun k hk => by
      have hk' : k - 1 < 5 := by simp at hk; omega
      refine ⟨by rw [sR10]; have := hc9ce; clear * - hk' this hc9; omega, ?_⟩
      rw [e410.rd (by rw [sR4]; omega), r4T (k - 1) hk']; rfl) r10w
  exact ⟨_, pr_seq impl κ inp hB1 (pr_seq impl κ inp hB2 (pr_seq impl κ inp hB3
    (pr_seq impl κ inp hB4 (pr_seq impl κ inp hB5 (pr_seq impl κ inp hB6 (pr_seq impl κ inp hB7
    (pr_seq impl κ inp hB8 (pr_seq impl κ inp hB9 (pr_seq impl κ inp hBr (pr_seq impl κ inp hB10 hT))))))))))⟩

end Run

end FR.Snd.R4

end G6_FRSoundness4R4PfFlag

section G6_FRSoundness4R4PfFin

-- New for `flock-recursive` (BLUEPRINT revision 4.1, A.9 `finPf`, `relPf`; track R4h). The 3.x
-- templates are the `enc`/`fin` cases of `FRSoundnessAccLog.finLog_of_run`, `fhVal_mle`, `padV_eq`,
-- `finV_zero`, `pfRefs_lt`.

/-!
# `FinRest4.fin` from INT-8's `finPf`, and `FinRest4.enc`'s zero tail

On an accepted run's fields (field 11), `flag_gFinPf4` gives **`relPf4`** (`relPf4_of_fields`).
Its parts at the spec:

* `claimN(Pf)` is `clR2 pfStart … 7` (`pf_view4`);
* **`finHat4_eq`**: `final̂(sf) = mleN 7 finalAt (pfPt es)` (`fhVal4_eq`, `eqTab_getD`, `finalAt_eq4`);
* **`padV4_eq`**: the kind's pad is `Π_{mLog ≤ v < 7} (1 − ρ_v)` (characteristic 2);
* **`tail_zero4`**: the kind's tail flag makes the final message zero beyond `2^mLog` (π's
  elements), which is `enc4_of_fields`' hypothesis.

**`fin4_of_fields`** is `FinRest4.fin` given `Ŵ₄(P₄) = wHatL W₀ L es 4` (`hW`: the level steps and
`Ŵ₀(P₀)`, handover).
-/

namespace FR.Snd.R4
open RecursionFast Rev4 Finset

/-! ## Registers -/

section Refs
variable {fi : FinIn} {N : ℕ} (hN : 0 < N) (hO : ∀ n, ∀ x ∈ fi.outs.getD n [], x < N)
include hN hO

theorem gSRegs_lt (S : Seq) (i : ℕ) : ∀ x ∈ gSRegs S fi i, x < N :=
  sub_lt (lvOuts_lt hN hO i 0) fun _ hx => List.mem_of_mem_drop (List.mem_of_mem_take hx)

theorem gTailRegs_lt (S : Seq) (m k : ℕ) : ∀ x ∈ gTailRegs S fi m k, x < N := by
  intro x hx
  rw [gTailRegs, List.mem_append, List.mem_flatMap] at hx
  rcases hx with ⟨j, -, hx⟩ | hx
  · exact gSRegs_lt hN hO S j x (List.mem_of_mem_drop hx)
  · exact chals_lt hN hO "Pf" S.pf x (List.mem_of_mem_take hx)

theorem gP0Regs_lt (S : Seq) (m : ℕ) : ∀ x ∈ gP0Regs S fi m, x < N := by
  intro x hx
  rw [gP0Regs, List.mem_append] at hx
  rcases hx with hx | hx
  · exact gSRegs_lt hN hO S 0 x hx
  · exact gTailRegs_lt hN hO S m 1 x hx

/-- **`gPfPts` reads only the skeleton's registers** (3.x's `pfPts_lt`, every family). -/
theorem gPfPts_lt (P : FinP) : ∀ s ∈ gPfPts P fi, ∀ p ∈ s, ∀ x ∈ p.regs, x < N := by
  have hz : ∀ m, ∀ p ∈ zSrc fi m, ∀ x ∈ p.regs, x < N := fun m => srcs_app
    (by simpa [List.map_map] using srcs_c (N := N) ((List.ofFn pinnedRho).drop 1) K.ofF)
    (srcs_f (sub_lt (coordsR_lt hN hO "Z1") fun _ hx => List.mem_of_mem_take hx))
  have hlc : ∀ m, ∀ p ∈ gLcSrc P.S fi m, ∀ x ∈ p.regs, x < N := fun m => srcs_app
    (srcs_f (sub_lt (chals_lt hN hO "L2" 14) fun _ hx => List.mem_of_mem_drop hx))
    (srcs_f (sub_lt (chals_lt hN hO "Z3" P.S.z3) fun _ hx =>
      List.mem_of_mem_take (List.mem_of_mem_drop hx)))
  have hsh : ∀ m, ∀ p ∈ gShSrc P.S fi m, ∀ x ∈ p.regs, x < N := fun m => srcs_app (srcs_app
    (srcs_f (sub_lt (chals_lt hN hO "S2" P.S.s2) fun _ hx =>
      List.mem_of_mem_drop (List.mem_of_mem_take hx)))
    (by
      intro p hp x hx
      rw [List.eq_of_mem_replicate hp] at hx; simp [PtSrc.regs] at hx))
    (srcs_f (sub_lt (chals_lt hN hO "S2" P.S.s2) fun _ hx => List.mem_of_mem_take hx))
  have htl : ∀ m, ∀ s ∈ (List.range 4).map (fun k => (gTailRegs P.S fi m (k + 1)).map PtSrc.k),
      ∀ p ∈ s, ∀ x ∈ p.regs, x < N := fun m s hs => by
    obtain ⟨k, -, rfl⟩ := List.mem_map.1 hs; exact srcs_k (gTailRegs_lt hN hO P.S m (k + 1))
  intro s hs
  simp only [gPfPts, List.mem_append, List.mem_cons, List.mem_map, List.mem_flatMap,
    List.not_mem_nil, or_false] at hs
  rcases hs with ((((((((((rfl | ⟨m, -, rfl⟩) | rfl) | ⟨m, -, rfl⟩) | rfl) | ⟨m, -, rfl⟩) |
    ⟨e, -, rfl⟩) | hs) | ⟨m, -, hs⟩) | rfl) | ⟨m, -, rfl⟩)
  · exact hz _
  · exact hz m
  · exact hlc _
  · exact hlc m
  · exact hsh _
  · exact hsh m
  · exact srcs_f (chals_lt hN hO "E4" e)
  · exact htl _ s (List.mem_map.2 hs)
  · exact htl m s (List.mem_map.2 hs)
  · exact srcs_k (gP0Regs_lt hN hO P.S _)
  · exact srcs_k (gP0Regs_lt hN hO P.S m)

theorem gPfPts_ok (P : FinP) : ∀ s ∈ gPfPts P fi, ∀ x ∈ s, x.Ok N := by
  intro s hs x hx
  have h := gPfPts_lt hN hO P s hs x hx
  cases x with
  | f y => exact h y (by simp [PtSrc.regs])
  | k y => exact h y (by simp [PtSrc.regs])
  | c v => trivial

theorem lvRefs_lt4 : ∀ k ∈ [1, 2, 3, 4], ∀ x ∈ lvRefs fi k, x < N := by
  intro k _ x hx
  simp only [lvRefs, List.mem_cons, List.mem_append] at hx
  rcases hx with (rfl | hx) | hx
  · exact headD_lt (sRegs_lt hN hO k) hN
  · exact kcOf_lt hN hO _ x hx
  · exact ysOf_lt hN hO _ x hx

end Refs

theorem rest_gFinPf (P : FinP) :
    (finalsOf P).rest[11]'(by rw [rest_finalsOf_length]; omega) = fun fi b => gFinPf P fi b := by
  simp only [Finals.rest, finalsOf, show 11 = 5 + 1 + 1 + 1 + 1 + 1 + 1 from rfl,
    List.getElem_cons_succ, List.nil_append, List.cons_append]
  rw [List.getElem_append_right (by simp [nLevels])]
  simp [nLevels]

/-! ## The flag on an accepted run -/

section Acc
variable {impl : OpImpl} {p : KindP} {inp : Input} {tr : Trace} {y : List Val × List Bool × Trace}
  {P : FinP} {zh : List Reg} {Rs : ℕ → Array Val} {Ex : ℕ → Array (List Reg)}

/-- **`finPf`'s relation on an accepted run's fields** (field 11). -/
theorem relPf4_of_fields (hF : Fields4 impl p inp tr P y zh Rs Ex) (hPS : P.S = seq4) (hck : P.ck = true)
    (hnc : 0 < P.nc) (hnf : 0 < P.fams.length)
    (hix : ∀ j ∈ P.kv.ptIx p.tix, j < (gPfPts P ⟨(skeleton4 seq4 p).2.outs, zh, Ex 11⟩).length) :
    relPf4 impl p.tix inp ⟨(skeleton4 seq4 p).2.outs, zh, Ex 11⟩ (Rs 11) P = true := by
  set fi : FinIn := ⟨(skeleton4 seq4 p).2.outs, zh, Ex 11⟩
  have hE := hF.ext 11 (by omega)
  have hpos := hF.pos (k := 11) (by omega)
  have hO : ∀ n, ∀ x ∈ fi.outs.getD n [], x < (Rs 11).size := fun n x hx =>
    lt_of_lt_of_le (skeleton4_out_lt p hF.sk.ref n x hx) hE.1
  obtain ⟨-, Lk, hLk, -, -⟩ := hF.fld 11 (by omega)
  rw [rest_gFinPf P] at hLk
  simp only at hLk
  rw [gFinPf_reloc P hck] at hLk
  obtain ⟨L', hL'⟩ := flag_gFinPf4 impl p.tix inp (Rs 11) P hPS hnc hnf fi hpos hO
    (gPfPts_ok hpos hO P) hix (lvRefs_lt4 hpos hO)
  exact pureRun_det hLk hL'

end Acc

/-! ## The parts at the spec -/

theorem fhVal4_eq (S : Seq) (inp : Input) (E : Array K) : ∀ (cs : List ℕ) (A : K),
    fhVal4 S inp E cs A = A + (cs.map fun c => finV4 S inp c * E.getD c 0).sum
  | [], A => by simp [fhVal4]
  | c :: cs, A => by rw [fhVal4, fhVal4_eq S inp E cs, List.map_cons, List.sum_cons, add_assoc]

/-- `final̂` over `seq4`'s final elements at `sf` (3.x's `fhVal_mle`). -/
theorem fhVal4_mle (inp : Input) (sf : Array K) (hs : sf.size = 7) :
    fhVal4 seq4 inp (eqTab sf) (List.range (2 ^ seq4.pf)) 0 = mleN 7 (finV4 seq4 inp) (fun v => sf.getD v 0) := by
  rw [fhVal4_eq, zero_add, mleN, mle, ← List.sum_toFinset _ (List.nodup_range), seq4_pf]
  · rw [List.toFinset_range, ← Fin.sum_univ_eq_sum_range]
    refine Fintype.sum_congr _ _ fun u => ?_
    rw [eqTab_getD sf (by rw [hs]; exact u.2), eq_cube, mul_comm, hs]
    congr 1

theorem list_prod_range (g : ℕ → K) : ∀ k, ((List.range k).map g).prod = ∏ i ∈ range k, g i
  | 0 => by simp
  | k + 1 => by rw [List.range_succ, List.map_append, List.prod_append, list_prod_range g k, prod_range_succ]; simp

/-- **The kind's pad at Pf's challenges** (characteristic 2: `1 + x = 1 − x`). -/
theorem padF4_eq (sfv : ℕ → K) (m : ℕ) :
    padF4 sfv 7 m = ∏ v ∈ Ico (m - 25) 7, (1 - sfv v) := by
  have h1 : ∀ x : K, 1 + x = 1 - x := fun x => by rw [sub_eq_add_neg, CharTwo.neg_eq]
  rw [padF4, list_prod_range, prod_Ico_eq_prod_range]
  exact prod_congr rfl fun i _ => h1 _

/-- **The kind's tail flag zeroes the final message beyond `2^(t − 25)`** (3.x's `finV_zero`). -/
theorem tail_zero4 {inp : Input} {P : FinP} {κ : Kind} (h : tailOk4 P κ inp = true) (hS : P.S = seq4)
    {t : ℕ} (ht : t ∈ P.tails) (hm : P.kv.m κ = t) :
    ∀ c, 2 ^ (t - 25) ≤ c → c < 2 ^ 7 → finV4 seq4 inp c = 0 := by
  intro c hc1 hc2
  have hz := (List.all_eq_true.1 h) t ht
  simp only [hm, decide_true, Bool.not_true, Bool.false_or] at hz
  rw [hS] at hz
  have hz' := allZero_mem hz
  have hle : 2 ^ (t - 25) ≤ 2 ^ 7 := le_trans hc1 hc2.le
  have hb : bytesAt inp.π (fieldOffOf seq4 fFinal + 32 * c) 32 = Vector.replicate 32 0 := by
    refine Vector.ext fun k hk => ?_
    rw [getElem_bytesAt _ _ _ _ hk, Vector.getElem_replicate]
    by_cases hlt : fieldOffOf seq4 fFinal + 32 * c + k < inp.π.size
    · refine hz' _ ?_
      rw [tailBytes4, toList_extract, seq4_pf]
      set o := fieldOffOf seq4 fFinal
      have hoff : o + 32 * c + k = o + 2 ^ (t - 25) * 32 + (32 * c - 2 ^ (t - 25) * 32 + k) := by omega
      rw [hoff] at hlt ⊢
      rw [List.getD_eq_getElem _ _ (by simpa using hlt)]
      refine List.mem_iff_getElem.2 ⟨32 * c - 2 ^ (t - 25) * 32 + k, ?_, ?_⟩
      · simp only [List.length_take, List.length_drop, Array.length_toList, ByteArray.size_data]
        generalize 2 ^ (t - 25) = A at hc1 hle hlt ⊢
        refine lt_min ?_ (by omega)
        rw [Nat.add_sub_cancel_left]; norm_num at hc2 hle ⊢; omega
      · simp
    · rw [List.getD_eq_default _ _ (by simpa using not_lt.1 hlt)]
  rw [finV4, hb]; decide

section Acc
variable {impl : OpImpl} {p : KindP} {inp : Input} {tr : Trace} {y : List Val × List Bool × Trace}
  {P : FinP} {zh : List Reg} {Rs : ℕ → Array Val} {Ex : ℕ → Array (List Reg)}

/-- **`final̂(sf)` on the run is `mleN 7 finalAt (pfPt es)`**. -/
theorem finHat4_eq (hF : Fields4 impl p inp tr P y zh Rs Ex) (hPS : P.S = seq4) {k : ℕ} (hk : k ≤ 12) (ex : Array (List Reg)) :
    finHat4 inp ⟨(skeleton4 seq4 p).2.outs, zh, ex⟩ (Rs k) P =
      mleN 7 (T4.finalAt (fsOf tr (itemsOf seq4))) (T4.pfPt (fsOf tr (itemsOf seq4))) := by
  set fi : FinIn := ⟨(skeleton4 seq4 p).2.outs, zh, ex⟩
  have hE := hF.ext k hk
  obtain ⟨hpv, hpl, -, -, hpo, -⟩ := pf_view4 hF.sk (fi := fi) rfl
  have hch : ∀ x ∈ chals fi "Pf" 7, x ∈ outsOf fi "Pf" := fun x hx => by
    unfold chals at hx; exact List.mem_of_mem_drop (List.mem_of_mem_take hx)
  rw [finHat4, hPS, fhVal4_mle _ _ (by simp [seq4_pf, hpl])]
  unfold mleN
  have e1 : (fun u : Fin (2 ^ 7) => finV4 seq4 inp u) = fun u : Fin (2 ^ 7) => T4.finalAt (fsOf tr (itemsOf seq4)) u := by
    funext u; exact (finalAt_eq4 hF.sk u.2).symm
  have e2 : (fun v : Fin 7 => (((chals fi "Pf" seq4.pf).map fun x => (rd (Rs k) x).toK).toArray).getD v 0) =
      T4.pfPt (fsOf tr (itemsOf seq4)) := by
    funext v
    have hv := v.2
    rw [seq4_pf]
    have hmem : (chals fi "Pf" 7)[v.val]'(by rw [hpl]; exact hv) ∈ outsOf fi "Pf" := hch _ (List.getElem_mem _)
    simp only [Array.getD_eq_getD_getElem?, List.getElem?_toArray, List.getElem?_map,
      List.getElem?_eq_getElem (by rw [hpl]; exact hv : (v : ℕ) < _), Option.map_some, Option.getD_some]
    have := hpv v hv
    rw [List.getD_eq_getElem _ _ (by rw [hpl]; exact hv)] at this
    rw [hE.rd (hpo _ hmem), this]; rfl
  rw [e1, e2]

/-- **`FinRest4.fin`** on the fields, given `Ŵ₄(P₄)` at the spec (`hW`) and the kind's pad family
(`hpad`: `m*` with no pad, or the family `m` of the chain's kind). -/
theorem fin4_of_fields (hF : Fields4 impl p inp tr P y zh Rs Ex) (hPS : P.S = seq4) (hck : P.ck = true)
    (hnc : 0 < P.nc) (hnf : 0 < P.fams.length)
    (hix : ∀ j ∈ P.kv.ptIx p.tix, j < (gPfPts P ⟨(skeleton4 seq4 p).2.outs, zh, Ex 11⟩).length)
    (hpad : (P.kv.selA p.tix = true ∧ (kindOfC (fsOf tr (itemsOf seq4))).m = 32) ∨
      (P.kv.selA p.tix = false ∧ P.fams.getD (famI P p.tix) 0 = (kindOfC (fsOf tr (itemsOf seq4))).m))
    {W₀ : Log → Log → ℕ → K} {L : Log}
    (hW : wV4 impl p.tix ⟨(skeleton4 seq4 p).2.outs, zh, Ex 11⟩ (Rs 11) P =
      T4.wHatL W₀ L (fsOf tr (itemsOf seq4)) 4) (c₀ : Log → Log → K) :
    clR2 T4.pfStart 32 readK chK (T4.lvC c₀ 5) L (fsOf tr (itemsOf seq4)) 7 =
      T4.wHatL W₀ L (fsOf tr (itemsOf seq4)) 4 *
        (∏ v ∈ Ico (T4.mLog (kindOfC (fsOf tr (itemsOf seq4))) 4) 7, (1 - T4.pfP (fsOf tr (itemsOf seq4)) v)) *
          mleN 7 (T4.finalAt (fsOf tr (itemsOf seq4))) (T4.pfPt (fsOf tr (itemsOf seq4))) := by
  set fi : FinIn := ⟨(skeleton4 seq4 p).2.outs, zh, Ex 11⟩
  have hE := hF.ext 11 (by omega)
  have hpos0 := skel_pos4 hF.sk
  have hrel := relPf4_of_fields hF hPS hck hnc hnf hix
  obtain ⟨hpv, hpl, -, hpN, hpo, -⟩ := pf_view4 hF.sk (fi := fi) rfl
  simp only [relPf4, Bool.and_eq_true] at hrel
  have h1 := hrel.1
  rw [hE.rd (x := claimN fi "Pf") (getLastD_lt hpo hpos0), hpN, eqv_k] at h1
  have hch : ∀ x ∈ chals fi "Pf" 7, x ∈ outsOf fi "Pf" := fun x hx => by
    unfold chals at hx; exact List.mem_of_mem_drop (List.mem_of_mem_take hx)
  have hsf : ∀ v < 7, sfv4 fi (Rs 11) P v = T4.pfP (fsOf tr (itemsOf seq4)) v := fun v hv => by
    have hlt : v < (chals fi "Pf" 7).length := by rw [hpl]; exact hv
    rw [sfv4, hPS, seq4_pf, hE.rd (hpo _ (hch _ (by
      rw [List.getD_eq_getElem _ _ hlt]; exact List.getElem_mem _))), hpv v hv]; rfl
  have hpadv : padV4 p.tix fi (Rs 11) P = ∏ v ∈ Ico (T4.mLog (kindOfC (fsOf tr (itemsOf seq4))) 4) 7,
      (1 - T4.pfP (fsOf tr (itemsOf seq4)) v) := by
    rw [padV4, mLog4_eq]
    rcases hpad with ⟨hA, hm⟩ | ⟨hA, hm⟩
    · rw [if_pos hA, hm]; simp
    · rw [if_neg (by simp [hA]), hm, hPS, seq4_pf, padF4_eq]
      have := CKind.m_mem (kindOfC (fsOf tr (itemsOf seq4)))
      refine prod_congr rfl fun v hv => ?_
      rw [hsf v (mem_Ico.1 hv).2]
  rw [hW, hpadv, finHat4_eq hF hPS (k := 11) (by omega) (Ex 11)] at h1
  rw [show clR2 T4.pfStart 32 readK chK (T4.lvC c₀ 5) L (fsOf tr (itemsOf seq4)) 7 =
    rVal T4.pfStart (fsOf tr (itemsOf seq4)) 6 from rfl, h1]

/-- **`enc`'s zero tail from `finPf`'s tail flag** (the kind's `m` is `m*`, or one of the tails). -/
theorem hz_of_fields (hF : Fields4 impl p inp tr P y zh Rs Ex) (hPS : P.S = seq4) (hck : P.ck = true)
    (hnc : 0 < P.nc) (hnf : 0 < P.fams.length)
    (hix : ∀ j ∈ P.kv.ptIx p.tix, j < (gPfPts P ⟨(skeleton4 seq4 p).2.outs, zh, Ex 11⟩).length)
    (hmk : P.kv.m p.tix = (kindOfC (fsOf tr (itemsOf seq4))).m)
    (htl : (kindOfC (fsOf tr (itemsOf seq4))).m < 32 → (kindOfC (fsOf tr (itemsOf seq4))).m ∈ P.tails) :
    ∀ c, 2 ^ T4.mLog (kindOfC (fsOf tr (itemsOf seq4))) 4 ≤ c → c < 2 ^ 7 → finV4 seq4 inp c = 0 := by
  intro c hc1 hc2
  have hrel := relPf4_of_fields hF hPS hck hnc hnf hix
  simp only [relPf4, Bool.and_eq_true] at hrel
  rw [mLog4_eq] at hc1
  rcases Nat.lt_or_ge (kindOfC (fsOf tr (itemsOf seq4))).m 32 with h | h
  · exact tail_zero4 hrel.2 hPS (htl h) hmk c hc1 hc2
  · have := CKind.m_mem (kindOfC (fsOf tr (itemsOf seq4)))
    have h7 : (kindOfC (fsOf tr (itemsOf seq4))).m - 25 = 7 := by omega
    rw [h7] at hc1; omega

end Acc

end FR.Snd.R4

end G6_FRSoundness4R4PfFin
