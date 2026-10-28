-- New for `flock-recursive` (BLUEPRINT revision 4.1, A.9–A.10; stage R4d).
import FRSoundness4R4Ex
import FRSoundness4R4Rnd
import FRSoundness4R4View
import FRSoundness4P4bE
import FRSoundness4P4aNames
import FRSoundness4R4Link

/-!
# The front's Lr and E checks on an accepted run (P4b's `RejEndLr4`, `RejEndE4`, …)

Generic views by name, for a `fi` whose `outs` are the skeleton's and a file `R` extending the
skeleton's registers: **`coordsR_view4`** (a coordinates phase's registers hold the log's
coordinates), **`chals_view4`** (a rounds phase's challenge registers hold `rchs`),
**`claimN3z_view4`** (a degree-3 rounds phase from claim `0`: its last register holds `clR … 0`),
**`msg_abs4`** (an absorbed message's reads are π's, through the program's query table). Then each
check: `relLr4`/`relE4` (the flags at `FinP`) read through the views is the log's equation.
-/

namespace FR.Snd.R4
open RecursionFast Rev4

variable {impl : OpImpl} {p : KindP} {inp : Input}

theorem ph4 {n : ℕ} {x : String × Sh} (h : (phasesOf seq4)[n]? = some x) :
    ∃ hn : n < (phasesOf seq4).length, (phasesOf seq4)[n] = x := List.getElem?_eq_some_iff.1 h

theorem val_eqv_f4 {a : F} {v : Val} (h : (Val.f a).eqv v = true) : v = .f a := by
  cases v <;> simp_all [Val.eqv]

/-- **The absorbs' messages read by the front** (one table certificate): Lr end (213), E end
(273), E4 end (325), RS0 (326). -/
theorem fsMsgs4_ends : (fsMsgs4 seq4).getD 213 none = some (fieldOffOf seq4 fLrEnd, 48) ∧
    (fsMsgs4 seq4).getD 273 none = some (fieldOffOf seq4 fEEnd, 48) ∧
    (fsMsgs4 seq4).getD 325 none = some (fieldOffOf seq4 fE + gOE4end seq4, 32) ∧
    (fsMsgs4 seq4).getD 326 none = some (fieldOffOf seq4 fRS0, 4 * 128 * 16) := by
  rw [fsMsgs4, gOE4end, seq4_eq]; decide +kernel

section V
variable {tr : Trace} {y : List Val × List Bool × Trace} (h : SkRun4 impl p inp tr y)

include h in
/-- **An absorbed message's reads are π's** (`SkRun4.hq` at a message of the program's table). -/
theorem msg_abs4 {q o len : ℕ} (hq : q < 482) (hq0 : q ≠ 0)
    (hm : (fsMsgs4 seq4).getD q none = some (o, len)) {off : ℕ} (hoff : off + 16 ≤ len) :
    readF (Snd.msgAt (fsOf tr (itemsOf seq4)) q) off = F.ofBytes (bytesAt inp.π (o + off) 16) := by
  have e := h.hq q hq
  rw [hm] at e
  simp only [qOf, hq0, if_false] at e
  rw [msgAt_of_q e, readF, bytesAt_extract_of_le16 _ hoff]

variable {fi : FinIn} (hfi : fi.outs = (skeleton4 seq4 p).2.outs)
  {R : Array Val} (hR : ExtA (#[] ++ y.1.toArray) R)
include h hfi hR

/-- **A coordinates phase by name**: the first `a ≤ 2k` registers after its head hold the log's
coordinates `fAt es (P + j/2) (j % 2)`. -/
theorem coordsR_view4 {name : String} {n k : ℕ} (hn : n < (phasesOf seq4).length)
    (hsh : (phasesOf seq4)[n].2 = .squeezes k .coords) (hk : 0 < k) (hix : phaseIx name = n)
    {a : ℕ} (ha : a ≤ 2 * k) :
    ((coordsR fi name).take a).map (fv R) =
      (List.range a).map (fun j => fAt (fsOf tr (itemsOf seq4)) (phStart4 n + j / 2) (j % 2)) := by
  obtain ⟨b, hout, hsz, hv⟩ := coords_view4 h hn hsh hk
  rw [coordsR, (outsOf_skel hfi name).1, hix, hout, List.drop_one, List.tail_cons]
  apply List.ext_getElem (by simp; omega)
  intro j h1 h2
  simp only [List.length_map, List.length_range] at h2
  simp only [List.getElem_map, List.getElem_take, List.getElem_range]
  have hlt : b + 3 * (j / 2) + 1 + j % 2 < (#[] ++ y.1.toArray).size := by omega
  show (rd R _).toF = _
  rw [hR.rd hlt, hv j (by omega)]; rfl

/-- **A rounds phase's challenges by name**: its first `a ≤ k` challenge registers hold
`rchs P es a`. -/
theorem chals_view4 {name : String} {n f k deg : ℕ} (hn : n < (phasesOf seq4).length)
    (hsh : (phasesOf seq4)[n].2 = .rounds f k deg false) (hix : phaseIx name = n) {a : ℕ} (ha : a ≤ k) :
    (chals fi name a).map (fv R) = rchs (phStart4 n) (fsOf tr (itemsOf seq4)) a := by
  obtain ⟨b, hout, hsz, -, -, hch, -⟩ := rounds_core4 h hn hsh
  rw [chals, (outsOf_skel hfi name).1, hix, hout, List.cons_append, List.drop_one, List.tail_cons,
    List.take_append_of_le_length (by simp; omega)]
  apply List.ext_getElem (by simp [rchs]; omega)
  intro j h1 h2
  simp only [rchs, List.length_map, List.length_range] at h2
  simp only [List.getElem_map, List.getElem_take, List.getElem_range, rchs]
  have hw : 4 ≤ roundW deg := by unfold roundW; split <;> omega
  have hm : roundW deg * j + roundW deg ≤ roundW deg * k := by
    rw [← Nat.mul_succ]; exact Nat.mul_le_mul_left _ (by omega)
  have hlt : b + (initClaim (phasesOf seq4)[n].1).width + roundW deg * j + 3 <
      (#[] ++ y.1.toArray).size := by omega
  show (rd R _).toF = _
  rw [hR.rd hlt, hch j (by omega)]; rfl

/-- **A degree-3 rounds phase from claim `0`, by name** (Lr2, E2): its last register holds the
claim after the real rounds. -/
theorem claimN3z_view4 {name : String} {n f k : ℕ} (hn : n < (phasesOf seq4).length)
    (hsh : (phasesOf seq4)[n].2 = .rounds f k 3 false) (hix : phaseIx name = n)
    (hnm : (phasesOf seq4)[n].1 = name) (hz : initClaim name = .zero) (L : Log) :
    claimN fi name < (#[] ++ y.1.toArray).size ∧
      rd R (claimN fi name) =
        .f (clR (phStart4 n) (fun _ _ => 0) L (fsOf tr (itemsOf seq4)) (min (realRounds p name k) k)) := by
  obtain ⟨-, hcv, -, hlt, hlast⟩ := roundsF3_view4 h hn hsh L
  rw [hnm, hz] at hcv
  rw [hnm] at hlast
  rw [(outsOf_skel hfi name).2.2, hix]
  exact ⟨hlt, by rw [hR.rd hlt]; exact hlast 0 hcv⟩

/-- **A one-challenge squeeze by name** (`Lr3`, `E3`, …): its register holds `fAt es P 0`. -/
theorem one_name_view4 {name : String} {n : ℕ} (hn : n < (phasesOf seq4).length)
    (hsh : (phasesOf seq4)[n].2 = .squeezes 1 .one) (hix : phaseIx name = n) :
    (outsOf fi name).headD 0 < (#[] ++ y.1.toArray).size ∧
      fv R ((outsOf fi name).headD 0) = fAt (fsOf tr (itemsOf seq4)) (phStart4 n) 0 := by
  obtain ⟨b, hout, hlt, hv⟩ := one_view4 h hn hsh
  rw [(outsOf_skel hfi name).1, hix, hout, List.headD_cons]
  refine ⟨hlt, ?_⟩
  show (rd R b).toF = _
  rw [hR.rd hlt, hv]; rfl

end V

/-! ## The kind of an accepted run's chain -/

theorem kindOfC_acc_node {ν : NodeKind} {P : FinP} {tr : Trace}
    (h : semIR impl (gen4 seq4 (.ofNode ν) (finOps4 P)) inp tr = some true) :
    kindOfC (fsOf tr (itemsOf seq4)) = .node ν := by
  obtain ⟨y, hS, -⟩ := fields_of_accept4 P h
  exact kindOfC_node4 hS

theorem kindOfC_acc_seg {σ : SegKind} {P : FinP} {tr : Trace}
    (h : semIR impl (gen4 seq4 (.ofSeg σ) (finOps4 P)) inp tr = some true) :
    kindOfC (fsOf tr (itemsOf seq4)) = .seg σ := by
  obtain ⟨y, hS, -⟩ := fields_of_accept4 P h
  exact kindOfC_seg4 hS

/-! ## Lr's end check (`finLr` (ii)) -/

/-- Lr's end message: its three values are the relocated reads of `fLrEnd`. -/
theorem vEnd_lr4 {tr : Trace} {y : List Val × List Bool × Trace} (h : SkRun4 impl p inp tr y) :
    vEnd 17 179 (fsOf tr (itemsOf seq4)) 0 = pe4 seq4 inp fLrEnd 0 ∧
    vEnd 17 179 (fsOf tr (itemsOf seq4)) 1 = pe4 seq4 inp fLrEnd 16 ∧
    vEnd 17 179 (fsOf tr (itemsOf seq4)) 2 = pe4 seq4 inp fLrEnd 32 := by
  have hm := fsMsgs4_ends.1
  refine ⟨?_, ?_, ?_⟩ <;> rw [vEnd, show 179 + 2 * 17 = 213 from rfl,
    msg_abs4 h (by norm_num) (by norm_num) hm (by norm_num)] <;> rfl

/-- **Lr's end equation on an accepted node run** (`finLr` (ii) through the views). -/
theorem lr_end4 {ν : NodeKind} {cells : List ℕ} {tr : Trace}
    (h : semIR impl (gen4 seq4 (.ofNode ν) (finOps4 (nodeFinP ν cells))) inp tr = some true) (L : Log) :
    clR 179 (fun _ _ => 0) L (fsOf tr (itemsOf seq4)) (P4b.lrR ν) =
      eq (ptOf (P4b.lrR ν) (tauS (P4b.lrR ν) 169 (fsOf tr (itemsOf seq4))))
          (ptOf (P4b.lrR ν) (rxs (P4b.lrR ν) 179 (fsOf tr (itemsOf seq4)))) *
        (vEnd 17 179 (fsOf tr (itemsOf seq4)) 0 * vEnd 17 179 (fsOf tr (itemsOf seq4)) 1 +
          vEnd 17 179 (fsOf tr (itemsOf seq4)) 2) := by
  obtain ⟨y, hS, fi, R, hfi, hE, hrel⟩ := relLr4_of_accept (nodeFinP ν cells) h
  have hnode : (nodeFinP ν cells).kv.node (KindP.ofNode ν).tix = true := rfl
  have hlr : (nodeFinP ν cells).lrR = P4b.lrR ν := rfl
  have hS4 : (nodeFinP ν cells).S = seq4 := rfl
  simp only [relLr4, hnode, ite_true, hlr, hS4] at hrel
  have hc := val_eqv_f4 hrel
  obtain ⟨hn14, e14⟩ := ph4 (n := 14) (x := ("Lr2", Sh.rounds fLr seq4.lr 3 false)) rfl
  obtain ⟨hn13, e13⟩ := ph4 (n := 13) (x := ("Lr1", Sh.squeezes 9 .coords)) (by rw [seq4_eq]; rfl)
  have hle := P4b.dims_le ν
  obtain ⟨-, hcl⟩ := claimN3z_view4 hS hfi hE hn14 (by rw [e14]) phaseIx4_rounds.2.2.2.2.1
    (by rw [e14]) rfl L
  rw [hc, (realRounds_vals _ _).2.2.1, (dims_node4 ν).2.2.2.1, Nat.min_eq_left hle.1,
    show phStart4 14 = 179 by rw [phStart4, fsStarts4_eq]; rfl] at hcl
  have hco := coordsR_view4 hS hfi hE hn13 (by rw [e13]) (by norm_num) phaseIx_vals.2.2.2.2.2.2.2.2.1
    (a := P4b.lrR ν) (by cases ν <;> decide)
  have hch := chals_view4 hS hfi hE hn14 (by rw [e14]) phaseIx4_rounds.2.2.2.2.1 hle.1
  rw [hco, hch, show phStart4 13 = 170 by rw [phStart4, fsStarts4_eq]; rfl,
    show phStart4 14 = 179 by rw [phStart4, fsStarts4_eq]; rfl, FR.Impl.eqPoint_eq] at hcl
  obtain ⟨v0, v1, v2⟩ := vEnd_lr4 hS
  rw [v0, v1, v2, ← Val.f.inj hcl]
  have hl : ∀ l : List F, l.toArray.size = l.length := fun _ => rfl
  rw [hl, List.length_map, List.length_range, FR.Impl.ptA_toArray, FR.Impl.ptA_toArray]
  rfl

/-- **`RejEndLr4` never holds on an accepted node run.** -/
theorem not_rejEndLr4_node {ν : NodeKind} {cells : List ℕ} {tr : Trace}
    (h : semIR impl (gen4 seq4 (.ofNode ν) (finOps4 (nodeFinP ν cells))) inp tr = some true) (L : Log) :
    ¬ P4b.RejEndLr4 L (fsOf tr (itemsOf seq4)) := by
  rw [P4b.RejEndLr4, P4b.onNode_iff (kindOfC_acc_node h)]
  exact fun ⟨_, hne⟩ => hne (lr_end4 h L)

/-- **… nor on an accepted segment run** (the gate). -/
theorem not_rejEndLr4_seg {σ : SegKind} {P : FinP} {tr : Trace}
    (h : semIR impl (gen4 seq4 (.ofSeg σ) (finOps4 P)) inp tr = some true) (L : Log) :
    ¬ P4b.RejEndLr4 L (fsOf tr (itemsOf seq4)) :=
  P4b.not_onNode_seg (kindOfC_acc_seg h)

/-! ## `finE` on an accepted run, with `finLr`'s exports -/

/-- `finE`'s registers are named, output or `zhat` registers (abstract `fi`). -/
theorem hin_E {fi : FinIn} {n : ℕ} (hsk : ∀ name, ∀ x ∈ outsOf fi name, x < n) (hn : 0 < n)
    (P : FinP) (hz : ∀ x ∈ fi.zhat, x < n) (h0 : lrEx fi 0 < n) (h1 : lrEx fi 1 < n) :
    ∀ x ∈ (coordsR fi "E1").take P.e2R ++ chals fi "E2" P.e2R ++ chals fi "E4" P.e4R ++
      [(outsOf fi "E3").headD 0, claimN fi "E2", claim0 fi "E4", claimN fi "E4",
       fi.zhat.getD 3 0, (outsOf fi "Lr3").headD 0, lrEx fi 0, lrEx fi 1], x < n := by
  intro x hx
  simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hx
  rcases hx with ((hx | hx) | hx) | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact hsk "E1" x (List.mem_of_mem_drop (List.mem_of_mem_take hx))
  · exact hsk "E2" x (List.mem_of_mem_drop (List.mem_of_mem_take hx))
  · exact hsk "E4" x (List.mem_of_mem_drop (List.mem_of_mem_take hx))
  · exact headD_lt (hsk "E3") hn
  · exact getLastD_lt (hsk "E2") hn
  · exact headD_lt (hsk "E4") hn
  · exact getLastD_lt (hsk "E4") hn
  · exact getD_lt hn hz 3
  · exact headD_lt (hsk "Lr3") hn
  · exact h0
  · exact h1

theorem rest_gFinLr (P : FinP) :
    (finalsOf P).rest[3]'(by rw [rest_finalsOf_length]; decide) = gFinLr P := by
  simp only [Finals.rest, finalsOf, List.cons_append, List.getElem_cons_succ, List.getElem_cons_zero]
theorem rest_gFinE (P : FinP) :
    (finalsOf P).rest[4]'(by rw [rest_finalsOf_length]; decide) = gFinE P := by
  simp only [Finals.rest, finalsOf, List.cons_append, List.getElem_cons_succ, List.getElem_cons_zero]

theorem opsOut_gFinLr (P : FinP) (fi : FinIn) (b : ℕ) :
    opsOut ((gFinLr P fi b).1.map (reloc P.S)) = 14 := by
  rw [opsOut_reloc]; cases hc : P.ck <;> simp [gFinLr, opsOut, Op.outs, hc]

/-- **`finE`'s relation on an accepted run**, with `lrEx`'s values: `v_L` (`vLv4` on `finLr`'s
file `R3`) and Lr2's challenges. -/
theorem relE4_of_accept (P : FinP) {tr : Trace}
    (h : semIR impl (gen4 seq4 p (finOps4 P)) inp tr = some true) :
    ∃ y, SkRun4 impl p inp tr y ∧ ∃ (fi : FinIn) (R3 R : Array Val),
      fi.outs = (skeleton4 seq4 p).2.outs ∧ ExtA (#[] ++ y.1.toArray) R3 ∧ ExtA R3 R ∧
      (∀ x ∈ fi.zhat, x < R.size) ∧
      relE4 impl p.tix inp fi R P = true ∧ fv R (lrEx fi 0) = vLv4 inp fi R3 P ∧
      (rd R (lrEx fi 1)).toAF = ((chals fi "Lr2" P.lrR).map (fv R3)).toArray := by
  obtain ⟨y, hS, zh, Rs, Ex, hext, hzh, hf⟩ := fields_ex4 P h
  obtain ⟨hs3, L3, hL3, he3, hx3⟩ := hf 3 (by decide)
  obtain ⟨-, L4, hL4, -, -⟩ := hf 4 (by decide)
  have hch : ∀ k < 12, ExtA (Rs k) (Rs (k + 1)) := fun k hk => by
    obtain ⟨-, L, -, he, -⟩ := hf k hk; rw [he]; exact ExtA.app _ _
  rw [rest_gFinLr] at hL3 hx3
  rw [rest_gFinE] at hL4
  have hpos := skel_pos4 hS
  have hE3 := hext 3 (by decide)
  have hE4 := hext 4 (by decide)
  have h34 : ExtA (Rs 3) (Rs 4) := hch 3 (by decide)
  have h04 : ExtA (Rs 0) (Rs 4) := chain_ext hch (by decide) (by decide)
  have hsk3 : ∀ name, ∀ x ∈ outsOf ⟨(skeleton4 seq4 p).2.outs, zh, Ex 3⟩ name, x < (Rs 3).size :=
    fun name x hx => Nat.lt_of_lt_of_le (outsOf_lt4 (p := p) hS zh (Ex 3) name x hx) hE3.1
  obtain ⟨L', hL', hv0, hv1⟩ := flag_gFinLr impl p.tix inp ⟨(skeleton4 seq4 p).2.outs, zh, Ex 3⟩ (Rs 3) P
    (hin_Lr hsk3 (lt_of_lt_of_le hpos hE3.1) P)
  obtain ⟨rfl, -⟩ := Prod.mk.inj (Option.some.inj (hL3.symm.trans hL'))
  rw [← he3] at hv0 hv1
  have hl3 := pureRun_len impl p.tix inp _ _ [] _ _ hL3
  rw [opsOut_gFinLr, List.length_nil, Nat.zero_add] at hl3
  have hsz4 : (Rs 4).size = (Rs 3).size + 14 := by rw [he3]; simp [hl3]
  set fi : FinIn := ⟨(skeleton4 seq4 p).2.outs, zh, Ex 4⟩
  have hlr : ∀ j, lrEx fi j = (gFinLr P ⟨(skeleton4 seq4 p).2.outs, zh, Ex 3⟩ (Rs 3).size).2.getD j 0 :=
    lrEx_eq4 hs3 _ fi hx3
  have hsk4 : ∀ name, ∀ x ∈ outsOf fi name, x < (Rs 4).size :=
    fun name x hx => Nat.lt_of_lt_of_le (outsOf_lt4 (p := p) hS zh (Ex 4) name x hx) hE4.1
  have hz4 : ∀ x ∈ fi.zhat, x < (Rs 4).size := fun x hx => Nat.lt_of_lt_of_le (hzh x hx) h04.1
  obtain ⟨LE, hLE, -⟩ := flag_gFinE impl p.tix inp fi (Rs 4) P
    (hin_E hsk4 (lt_of_lt_of_le hpos hE4.1) P hz4
      (by rw [hlr]; show (Rs 3).size + 13 < _; omega) (by rw [hlr]; show (Rs 3).size + 4 < _; omega))
  exact ⟨y, hS, fi, Rs 3, Rs 4, rfl, hE3, h34, hz4, pureRun_det hL4 hLE,
    by rw [hlr]; exact hv0, by rw [hlr]; exact hv1⟩

/-! ## E's end check (`finE` (ii)) and E4's rounds -/

theorem vEnd_e4 {tr : Trace} {y : List Val × List Bool × Trace} (h : SkRun4 impl p inp tr y) :
    vEnd 23 227 (fsOf tr (itemsOf seq4)) 0 = pe4 seq4 inp fEEnd 0 ∧
    vEnd 23 227 (fsOf tr (itemsOf seq4)) 1 = pe4 seq4 inp fEEnd 16 ∧
    vEnd 23 227 (fsOf tr (itemsOf seq4)) 2 = pe4 seq4 inp fEEnd 32 := by
  have hm := fsMsgs4_ends.2.1
  refine ⟨?_, ?_, ?_⟩ <;> rw [vEnd, show 227 + 2 * 23 = 273 from rfl,
    msg_abs4 h (by norm_num) (by norm_num) hm (by norm_num)] <;> rfl

/-- **E's end equation on an accepted node run** (`finE` (ii) through the views). -/
theorem e_end4 {ν : NodeKind} {cells : List ℕ} {tr : Trace}
    (h : semIR impl (gen4 seq4 (.ofNode ν) (finOps4 (nodeFinP ν cells))) inp tr = some true) (L : Log) :
    clR 227 (fun _ _ => 0) L (fsOf tr (itemsOf seq4)) (P4b.e2R ν) =
      eq (ptOf (P4b.e2R ν) (tauS (P4b.e2R ν) 214 (fsOf tr (itemsOf seq4))))
          (ptOf (P4b.e2R ν) (rxs (P4b.e2R ν) 227 (fsOf tr (itemsOf seq4)))) *
        (vEnd 23 227 (fsOf tr (itemsOf seq4)) 0 * vEnd 23 227 (fsOf tr (itemsOf seq4)) 1 +
          vEnd 23 227 (fsOf tr (itemsOf seq4)) 2) := by
  obtain ⟨y, hS, fi, R3, R, hfi, hE3, h3R, -, hrel, -, -⟩ := relE4_of_accept (nodeFinP ν cells) h
  have hE := hE3.trans h3R
  have hnode : (nodeFinP ν cells).kv.node (KindP.ofNode ν).tix = true := rfl
  have he2 : (nodeFinP ν cells).e2R = P4b.e2R ν := rfl
  have hS4 : (nodeFinP ν cells).S = seq4 := rfl
  simp only [relE4, hnode, ite_true, he2, hS4, Bool.and_eq_true] at hrel
  have hc := val_eqv_f4 hrel.1
  obtain ⟨hn18, e18⟩ := ph4 (n := 18) (x := ("E2", Sh.rounds fE seq4.e2 3 false)) rfl
  obtain ⟨hn17, e17⟩ := ph4 (n := 17) (x := ("E1", Sh.squeezes 12 .coords)) (by rw [seq4_eq]; rfl)
  have hle := P4b.dims_le ν
  obtain ⟨-, hcl⟩ := claimN3z_view4 hS hfi hE hn18 (by rw [e18]) phaseIx4_rounds.2.2.2.2.2.1
    (by rw [e18]) rfl L
  rw [hc, (realRounds_vals _ _).2.2.2.1, (dims_node4 ν).2.2.2.2.1, Nat.min_eq_left hle.2.1,
    show phStart4 18 = 227 by rw [phStart4, fsStarts4_eq]; rfl] at hcl
  have hco := coordsR_view4 hS hfi hE hn17 (by rw [e17]) (by norm_num)
    phaseIx_vals.2.2.2.2.2.2.2.2.2.2.2.1 (a := P4b.e2R ν) (by cases ν <;> decide)
  have hch := chals_view4 hS hfi hE hn18 (by rw [e18]) phaseIx4_rounds.2.2.2.2.2.1 hle.2.1
  rw [hco, hch, show phStart4 17 = 215 by rw [phStart4, fsStarts4_eq]; rfl,
    show phStart4 18 = 227 by rw [phStart4, fsStarts4_eq]; rfl, FR.Impl.eqPoint_eq] at hcl
  obtain ⟨v0, v1, v2⟩ := vEnd_e4 hS
  rw [v0, v1, v2, ← Val.f.inj hcl]
  have hl : ∀ l : List F, l.toArray.size = l.length := fun _ => rfl
  rw [hl, List.length_map, List.length_range, FR.Impl.ptA_toArray, FR.Impl.ptA_toArray]
  rfl

theorem not_rejEndE4_node {ν : NodeKind} {cells : List ℕ} {tr : Trace}
    (h : semIR impl (gen4 seq4 (.ofNode ν) (finOps4 (nodeFinP ν cells))) inp tr = some true) (L : Log) :
    ¬ P4b.RejEndE4 L (fsOf tr (itemsOf seq4)) := by
  rw [P4b.RejEndE4, P4b.onNode_iff (kindOfC_acc_node h)]
  exact fun ⟨_, hne⟩ => hne (e_end4 h L)

theorem not_rejEndE4_seg {σ : SegKind} {P : FinP} {tr : Trace}
    (h : semIR impl (gen4 seq4 (.ofSeg σ) (finOps4 P)) inp tr = some true) (L : Log) :
    ¬ P4b.RejEndE4 L (fsOf tr (itemsOf seq4)) :=
  P4b.not_onNode_seg (kindOfC_acc_seg h)

/-- A round check reads its initial claim only at round `0`, and there only its value. -/
theorem chk2F_c0 {c0 c0' : Log → Log → F} {L es : Log} (hc : c0 L es = c0' L es) (b l : ℕ) :
    Chk2 b 16 readF (fun d => chF d 0) c0 L es l ↔ Chk2 b 16 readF (fun d => chF d 0) c0' L es l := by
  cases l <;> simp only [Chk2, clR2, hc]

/-- **E4's round checks on an accepted node run** hold from `c4E4` (`finE` (iii) gives the first
claim, `lrEx` gives `v_L`). -/
theorem e_in4 {ν : NodeKind} {cells : List ℕ} {tr : Trace}
    (h : semIR impl (gen4 seq4 (.ofNode ν) (finOps4 (nodeFinP ν cells))) inp tr = some true) (L : Log) :
    ∀ l < P4b.ncR ν, Chk2 275 16 readF (fun d => chF d 0) P4b.c4E4 L (fsOf tr (itemsOf seq4)) l := by
  obtain ⟨y, hS, fi, R3, R, hfi, hE3, h3R, -, hrel, hv0, -⟩ := relE4_of_accept (nodeFinP ν cells) h
  have hE := hE3.trans h3R
  have hnode : (nodeFinP ν cells).kv.node (KindP.ofNode ν).tix = true := rfl
  have hS4 : (nodeFinP ν cells).S = seq4 := rfl
  simp only [relE4, hnode, ite_true, hS4, Bool.and_eq_true] at hrel
  have hc := val_eqv_f4 hrel.2.1
  rw [hv0] at hc
  obtain ⟨hn21, e21⟩ := ph4 (n := 21) (x := ("E4", Sh.rounds fE seq4.e4 2 false)) rfl
  obtain ⟨hn20, e20⟩ := ph4 (n := 20) (x := ("E3", Sh.squeezes 1 .one)) rfl
  obtain ⟨hn16, e16⟩ := ph4 (n := 16) (x := ("Lr3", Sh.squeezes 1 .one)) rfl
  obtain ⟨-, hkE⟩ := one_name_view4 hS hfi hE hn20 (by rw [e20]) phaseIx_vals.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  obtain ⟨-, hkL⟩ := one_name_view4 hS hfi hE3 hn16 (by rw [e16]) phaseIx_vals.2.2.2.2.2.2.2.2.2.2.1
  have hle := P4b.dims_le ν
  obtain ⟨hcl, -, -, -, hlast⟩ := roundsF2_view4 hS hn21 (by rw [e21]) L
  rw [(outsOf_skel hfi "E4").2.1, phaseIx4_rounds.2.2.2.2.2.2] at hc
  rw [← hE.rd hcl, hc] at hlast
  obtain ⟨-, hchk⟩ := hlast _ rfl
  rw [e21, (realRounds_vals _ _).2.2.2.2.1, (dims_node4 ν).2.2.2.2.2, Nat.min_eq_left hle.2.2,
    show phStart4 21 = 275 by rw [phStart4, fsStarts4_eq]; rfl] at hchk
  intro l hl
  refine (chk2F_c0 ?_ 275 l).1 (hchk l hl)
  obtain ⟨v0, v1, v2⟩ := vEnd_e4 hS
  obtain ⟨w0, w1, w2⟩ := vEnd_lr4 hS
  rw [show phStart4 20 = 274 by rw [phStart4, fsStarts4_eq]; rfl] at hkE
  rw [show phStart4 16 = 214 by rw [phStart4, fsStarts4_eq]; rfl] at hkL
  simp only [vLv4, hS4, hkE, hkL, P4b.c4E4, c4, kapB, v0, v1, v2, w0, w1, w2]
  ring

theorem not_rejInE4_node {ν : NodeKind} {cells : List ℕ} {tr : Trace}
    (h : semIR impl (gen4 seq4 (.ofNode ν) (finOps4 (nodeFinP ν cells))) inp tr = some true) (L : Log) :
    ¬ P4b.RejInE4 L (fsOf tr (itemsOf seq4)) := by
  rw [P4b.RejInE4, P4b.onNode_iff (kindOfC_acc_node h)]
  exact fun ⟨l, hl, _, hne⟩ => hne (e_in4 h L l hl)

theorem not_rejInE4_seg {σ : SegKind} {P : FinP} {tr : Trace}
    (h : semIR impl (gen4 seq4 (.ofSeg σ) (finOps4 P)) inp tr = some true) (L : Log) :
    ¬ P4b.RejInE4 L (fsOf tr (itemsOf seq4)) :=
  P4b.not_onNode_seg (kindOfC_acc_seg h)

/-! ## `finE` (iv): E4's last claim (node matrix facts are parameters) -/

theorem clR2_c0_succ {c0 c0' : Log → Log → F} (b : ℕ) (L es : Log) (n : ℕ) :
    clR2 b 16 readF (fun d => chF d 0) c0 L es (n + 1) = clR2 b 16 readF (fun d => chF d 0) c0' L es (n + 1) :=
  rfl

/-- **`finE` (iv) on an accepted node run**: E4's last claim is `W(r′)·α_E`, for `evalM`/`evalL`
meeting the node kind's M and L rows' matrix MLEs (`hM`, `hL`: the node op spec, a parameter). -/
theorem e_fin4 (srcE srcL : NodeKind → P4b.ESrc) {ν : NodeKind} {cells : List ℕ} {tr : Trace}
    (hM : ∀ r2 r4 : Array F, r2.size = P4b.e2R ν → r4.size = P4b.ncR ν → impl.evalM r2 r4 =
      (Eval.matMLE (srcE ν).ea (FR.Impl.ptA (P4b.e2R ν) r2) (FR.Impl.ptA (P4b.ncR ν) r4),
       Eval.matMLE (srcE ν).eb (FR.Impl.ptA (P4b.e2R ν) r2) (FR.Impl.ptA (P4b.ncR ν) r4),
       Eval.matMLE (srcE ν).ec (FR.Impl.ptA (P4b.e2R ν) r2) (FR.Impl.ptA (P4b.ncR ν) r4)))
    (hL : ∀ rL r4 : Array F, rL.size = P4b.lrR ν → r4.size = P4b.ncR ν → impl.evalL rL r4 =
      (Eval.matMLE (srcL ν).ea (FR.Impl.ptA (P4b.lrR ν) rL) (FR.Impl.ptA (P4b.ncR ν) r4),
       Eval.matMLE (srcL ν).eb (FR.Impl.ptA (P4b.lrR ν) rL) (FR.Impl.ptA (P4b.ncR ν) r4),
       Eval.matMLE (srcL ν).ec (FR.Impl.ptA (P4b.lrR ν) rL) (FR.Impl.ptA (P4b.ncR ν) r4)))
    (h : semIR impl (gen4 seq4 (.ofNode ν) (finOps4 (nodeFinP ν cells))) inp tr = some true) (L : Log) :
    clR2 275 16 readF (fun d => chF d 0) P4b.c4E4 L (fsOf tr (itemsOf seq4)) (P4b.ncR ν) =
      mle (P4b.wEb4 srcE srcL ν (fsOf tr (itemsOf seq4))) (ptOf (P4b.ncR ν) (P4b.rPt4 ν (fsOf tr (itemsOf seq4)))) *
        readF (msgAt (fsOf tr (itemsOf seq4)) 325) 0 := by
  obtain ⟨y, hS, fi, R3, R, hfi, hE3, h3R, -, hrel, -, hv1⟩ := relE4_of_accept (nodeFinP ν cells) h
  have hE := hE3.trans h3R
  have hnode : (nodeFinP ν cells).kv.node (KindP.ofNode ν).tix = true := rfl
  have hS4 : (nodeFinP ν cells).S = seq4 := rfl
  have he2 : (nodeFinP ν cells).e2R = P4b.e2R ν := rfl
  have he4 : (nodeFinP ν cells).e4R = P4b.ncR ν := rfl
  have hlr : (nodeFinP ν cells).lrR = P4b.lrR ν := rfl
  simp only [relE4, hnode, ite_true, hS4, he2, he4, Bool.and_eq_true] at hrel
  rw [hlr] at hv1
  obtain ⟨-, h2, h3, h4, -⟩ := hrel
  have hc0 := val_eqv_f4 h2
  have hc := val_eqv_f4 h3
  have hz := val_eqv_f4 h4
  obtain ⟨hn21, e21⟩ := ph4 (n := 21) (x := ("E4", Sh.rounds fE seq4.e4 2 false)) rfl
  obtain ⟨hn20, e20⟩ := ph4 (n := 20) (x := ("E3", Sh.squeezes 1 .one)) rfl
  obtain ⟨hn16, e16⟩ := ph4 (n := 16) (x := ("Lr3", Sh.squeezes 1 .one)) rfl
  obtain ⟨hn18, e18⟩ := ph4 (n := 18) (x := ("E2", Sh.rounds fE seq4.e2 3 false)) rfl
  obtain ⟨hn14, e14⟩ := ph4 (n := 14) (x := ("Lr2", Sh.rounds fLr seq4.lr 3 false)) rfl
  have hle := P4b.dims_le ν
  obtain ⟨-, hkE⟩ := one_name_view4 hS hfi hE hn20 (by rw [e20]) phaseIx_vals.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  obtain ⟨-, hkL⟩ := one_name_view4 hS hfi hE hn16 (by rw [e16]) phaseIx_vals.2.2.2.2.2.2.2.2.2.2.1
  have hc2 := chals_view4 hS hfi hE hn18 (by rw [e18]) phaseIx4_rounds.2.2.2.2.2.1 hle.2.1
  have hc4 := chals_view4 hS hfi hE hn21 (by rw [e21]) phaseIx4_rounds.2.2.2.2.2.2 hle.2.2
  have hcL := chals_view4 hS hfi hE3 hn14 (by rw [e14]) phaseIx4_rounds.2.2.2.2.1 hle.1
  -- E4's last claim register holds the rounds' last claim
  obtain ⟨hcl, -, -, hlt, hlast⟩ := roundsF2_view4 hS hn21 (by rw [e21]) L
  rw [(outsOf_skel hfi "E4").2.1, phaseIx4_rounds.2.2.2.2.2.2] at hc0
  rw [(outsOf_skel hfi "E4").2.2, phaseIx4_rounds.2.2.2.2.2.2] at hc
  rw [← hE.rd hcl, hc0] at hlast
  obtain ⟨hN, -⟩ := hlast _ rfl
  rw [← hE.rd hlt, hc, e21, (realRounds_vals _ _).2.2.2.2.1, (dims_node4 ν).2.2.2.2.2,
    Nat.min_eq_left hle.2.2, show phStart4 21 = 275 by rw [phStart4, fsStarts4_eq]; rfl] at hN
  have hpos : P4b.ncR ν ≠ 0 := by cases ν <;> decide
  obtain ⟨n, hn⟩ : ∃ n, P4b.ncR ν = n + 1 := ⟨P4b.ncR ν - 1, by omega⟩
  rw [hn, clR2_c0_succ (c0' := P4b.c4E4), ← hn] at hN
  rw [← Val.f.inj hN]
  -- the right-hand side through `mle_wEb4`
  have hrP : P4b.rPt4 ν (fsOf tr (itemsOf seq4)) = rchs 275 (fsOf tr (itemsOf seq4)) (P4b.ncR ν) := rfl
  have hα : readF (msgAt (fsOf tr (itemsOf seq4)) 325) 0 = (rd R (fi.zhat.getD 3 0)).toF := by
    rw [hz, msg_abs4 hS (by norm_num) (by norm_num) fsMsgs4_ends.2.2.1 (by norm_num), Nat.add_zero]; rfl
  rw [P4b.mle_wEb4, hα, hrP]
  have hl : ∀ l : List F, l.toArray.size = l.length := fun _ => rfl
  rw [hc2, hc4, show phStart4 18 = 227 by rw [phStart4, fsStarts4_eq]; rfl,
    show phStart4 21 = 275 by rw [phStart4, fsStarts4_eq]; rfl] at *
  rw [hv1, hcL, show phStart4 14 = 179 by rw [phStart4, fsStarts4_eq]; rfl,
    hM _ _ (by rw [hl]; simp [rxs, rchs]) (by rw [hl]; simp [rchs]),
    hL _ _ (by rw [hl]; simp [rxs, rchs]) (by rw [hl]; simp [rchs]),
]
  simp only [FR.Impl.ptA_toArray]
  have hk1 : kapB 23 227 (fsOf tr (itemsOf seq4)) = fv R ((outsOf fi "E3").headD 0) := by
    rw [hkE, show phStart4 20 = 274 by rw [phStart4, fsStarts4_eq]; rfl]; rfl
  have hk2 : kapB 17 179 (fsOf tr (itemsOf seq4)) = fv R ((outsOf fi "Lr3").headD 0) := by
    rw [hkL, show phStart4 16 = 214 by rw [phStart4, fsStarts4_eq]; rfl]; rfl
  rw [hk1, hk2, rxs, rxs]
  ring

/-- **`RejFinE4` never holds on an accepted node run** (for `evalM`/`evalL` at the spec). -/
theorem not_rejFinE4_node (srcE srcL : NodeKind → P4b.ESrc) {ν : NodeKind} {cells : List ℕ} {tr : Trace}
    (hM : ∀ r2 r4 : Array F, r2.size = P4b.e2R ν → r4.size = P4b.ncR ν → impl.evalM r2 r4 =
      (Eval.matMLE (srcE ν).ea (FR.Impl.ptA (P4b.e2R ν) r2) (FR.Impl.ptA (P4b.ncR ν) r4),
       Eval.matMLE (srcE ν).eb (FR.Impl.ptA (P4b.e2R ν) r2) (FR.Impl.ptA (P4b.ncR ν) r4),
       Eval.matMLE (srcE ν).ec (FR.Impl.ptA (P4b.e2R ν) r2) (FR.Impl.ptA (P4b.ncR ν) r4)))
    (hL : ∀ rL r4 : Array F, rL.size = P4b.lrR ν → r4.size = P4b.ncR ν → impl.evalL rL r4 =
      (Eval.matMLE (srcL ν).ea (FR.Impl.ptA (P4b.lrR ν) rL) (FR.Impl.ptA (P4b.ncR ν) r4),
       Eval.matMLE (srcL ν).eb (FR.Impl.ptA (P4b.lrR ν) rL) (FR.Impl.ptA (P4b.ncR ν) r4),
       Eval.matMLE (srcL ν).ec (FR.Impl.ptA (P4b.lrR ν) rL) (FR.Impl.ptA (P4b.ncR ν) r4)))
    (h : semIR impl (gen4 seq4 (.ofNode ν) (finOps4 (nodeFinP ν cells))) inp tr = some true) (L : Log) :
    ¬ P4b.RejFinE4 srcE srcL L (fsOf tr (itemsOf seq4)) := by
  rw [P4b.RejFinE4, P4b.onNode_iff (kindOfC_acc_node h)]
  exact fun ⟨_, hne⟩ => hne (e_fin4 srcE srcL hM hL h L)

theorem not_rejFinE4_seg (srcE srcL : NodeKind → P4b.ESrc) {σ : SegKind} {P : FinP} {tr : Trace}
    (h : semIR impl (gen4 seq4 (.ofSeg σ) (finOps4 P)) inp tr = some true) (L : Log) :
    ¬ P4b.RejFinE4 srcE srcL L (fsOf tr (itemsOf seq4)) :=
  P4b.not_onNode_seg (kindOfC_acc_seg h)

/-! ## `finLc` on an accepted run; L2's round checks (`RejL2`) -/

/-- **The front's earlier absorbs** (one table certificate): Zend (67), L3 (97). -/
theorem fsMsgs4_front : (fsMsgs4 seq4).getD 67 none = some (fieldOffOf seq4 fZend, 32) ∧
    (fsMsgs4 seq4).getD 97 none = some (fieldOffOf seq4 fL2 + phaseOffOf seq4 9 fL2, 128) := by
  rw [fsMsgs4, seq4_eq]; decide +kernel

theorem rest_gFinLc (P : FinP) :
    (finalsOf P).rest[1]'(by rw [rest_finalsOf_length]; decide) = gFinLc P := by
  simp only [Finals.rest, finalsOf, List.cons_append, List.getElem_cons_succ, List.getElem_cons_zero]

/-- `finLc`'s registers are named or `zhat` registers (abstract `fi`). -/
theorem hin_Lc {fi : FinIn} {n : ℕ} (hsk : ∀ name, ∀ x ∈ outsOf fi name, x < n) (hn : 0 < n)
    (P : FinP) (hz : ∀ x ∈ fi.zhat, x < n) :
    ∀ x ∈ (chals fi "Z3" P.S.z3).take 8 ++ chals fi "L2" 14 ++
      [(outsOf fi "L1").headD 0, (outsOf fi "L3β").headD 0, (outsOf fi "Z2").headD 0,
       claim0 fi "L2", claimN fi "L2", fi.zhat.getD 1 0], x < n := by
  intro x hx
  simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hx
  rcases hx with (hx | hx) | rfl | rfl | rfl | rfl | rfl | rfl
  · exact hsk "Z3" x (List.mem_of_mem_drop (List.mem_of_mem_take (List.mem_of_mem_take hx)))
  · exact hsk "L2" x (List.mem_of_mem_drop (List.mem_of_mem_take hx))
  · exact headD_lt (hsk "L1") hn
  · exact headD_lt (hsk "L3β") hn
  · exact headD_lt (hsk "Z2") hn
  · exact headD_lt (hsk "L2") hn
  · exact getLastD_lt (hsk "L2") hn
  · exact getD_lt hn hz 1

/-- **`finLc`'s relation on an accepted run.** -/
theorem relLc4_of_accept (P : FinP) {tr : Trace}
    (h : semIR impl (gen4 seq4 p (finOps4 P)) inp tr = some true) :
    ∃ y, SkRun4 impl p inp tr y ∧ ∃ (fi : FinIn) (R : Array Val),
      fi.outs = (skeleton4 seq4 p).2.outs ∧ ExtA (#[] ++ y.1.toArray) R ∧ (∀ x ∈ fi.zhat, x < R.size) ∧
      relLc4 impl p.tix inp fi R P = true := by
  obtain ⟨y, hS, zh, Rs, Ex, hext, hzh, hf⟩ := fields_ex4 P h
  obtain ⟨-, L1, hL1, -, -⟩ := hf 1 (by decide)
  obtain ⟨-, L0, -, he0, -⟩ := hf 0 (by decide)
  rw [rest_gFinLc] at hL1
  have hpos := skel_pos4 hS
  have hE1 := hext 1 (by decide)
  have h01 : ExtA (Rs 0) (Rs 1) := by rw [he0]; exact ExtA.app _ _
  have hsk : ∀ name, ∀ x ∈ outsOf ⟨(skeleton4 seq4 p).2.outs, zh, Ex 1⟩ name, x < (Rs 1).size :=
    fun name x hx => Nat.lt_of_lt_of_le (outsOf_lt4 (p := p) hS zh (Ex 1) name x hx) hE1.1
  have hz : ∀ x ∈ zh, x < (Rs 1).size := fun x hx => Nat.lt_of_lt_of_le (hzh x hx) h01.1
  obtain ⟨L', hL'⟩ := flag_gFinLc impl p.tix inp ⟨(skeleton4 seq4 p).2.outs, zh, Ex 1⟩ (Rs 1) P
    (hin_Lc hsk (lt_of_lt_of_le hpos hE1.1) P hz)
  exact ⟨y, hS, ⟨(skeleton4 seq4 p).2.outs, zh, Ex 1⟩, Rs 1, rfl, hE1, hz, pureRun_det hL1 hL'⟩

/-- **L2's round checks on an accepted run** (any kind): `finLc` (i) gives L2's first claim
`â + α b̂` (Zend's message at 67, L1's `α`). -/
theorem l2_chk4 (P : FinP) (hP : P.S = seq4) {tr : Trace}
    (h : semIR impl (gen4 seq4 p (finOps4 P)) inp tr = some true) (L : Log) :
    ∀ l < 14, Chk2 69 16 readF (fun d => chF d 0) (fun _ es => c0L es) L (fsOf tr (itemsOf seq4)) l := by
  obtain ⟨y, hS, fi, R, hfi, hE, -, hrel⟩ := relLc4_of_accept P h
  simp only [relLc4, Bool.and_eq_true] at hrel
  have hc0 := val_eqv_f4 hrel.1.1
  obtain ⟨hn8, e8⟩ := ph4 (n := 8) (x := ("L2", Sh.rounds fL2 14 2 false)) rfl
  obtain ⟨hn7, e7⟩ := ph4 (n := 7) (x := ("L1", Sh.squeezes 1 .one)) rfl
  obtain ⟨-, hα⟩ := one_name_view4 hS hfi hE hn7 (by rw [e7]) phaseIx_vals.2.2.2.1
  obtain ⟨hcl, -, -, -, hlast⟩ := roundsF2_view4 hS hn8 (by rw [e8]) L
  rw [(outsOf_skel hfi "L2").2.1, phaseIx4_rounds.2.2.1] at hc0
  rw [← hE.rd hcl, hc0] at hlast
  obtain ⟨-, hchk⟩ := hlast _ rfl
  rw [e8, (realRounds_vals _ _).2.2.2.2.2, Nat.min_self,
    show phStart4 8 = 69 by rw [phStart4, fsStarts4_eq]; rfl] at hchk
  intro l hl
  refine (chk2F_c0 ?_ 69 l).1 (hchk l hl)
  have hm := fsMsgs4_front.1
  rw [hα, show phStart4 7 = 68 by rw [phStart4, fsStarts4_eq]; rfl, c0L, alL, vZ, vZ,
    msg_abs4 hS (by norm_num) (by norm_num) hm (by norm_num),
    msg_abs4 hS (by norm_num) (by norm_num) hm (by norm_num), hP]
  rfl

/-- **`RejL2` never holds on an accepted run** (either kind). -/
theorem not_rejL2_4 (P : FinP) (hP : P.S = seq4) {tr : Trace}
    (h : semIR impl (gen4 seq4 p (finOps4 P)) inp tr = some true) (L : Log) :
    ¬ P4a.RejL2 L (fsOf tr (itemsOf seq4)) :=
  fun ⟨l, hl, _, hne⟩ => hne (l2_chk4 P hP h L l hl)

/-! ## `relSh4`'s link term on a segment -/

/-- **A segment's `relSh4` link term is its accumulator** (R4c's D7): for an implementation meeting
the segment's specification, `linkWAll` is `0^8` (`linkWAll_seg_of_meets`), so `linkSum` adds
nothing (`linkSum_zero`): `w_in = (sh + κ_s e₀)·s_in`. -/
theorem linkSum_seg4 {fin : Finals} {lRows : List Circ.Row} {κs₀ : F}
    (hm : impl.Meets (specSeg (Impl.specC fin lRows κs₀))) (σ : SegKind) (tt rr : Array F)
    (ks acc pow : F) :
    linkSum (impl.linkWAll (KindP.ofSeg σ).tix tt rr) ks nLinkFam acc pow = acc := by
  rw [linkWAll_seg_of_meets hm σ, linkSum_zero]

end FR.Snd.R4
