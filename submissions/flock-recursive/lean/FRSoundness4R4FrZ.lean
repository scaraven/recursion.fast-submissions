-- New for `flock-recursive` (BLUEPRINT revision 4.1, A.9 `finZ`, A.10 Z1–Zend, B-12; stage R4e).
import FRSoundness4R4FrS

/-!
# Z3's last claim on an accepted run (P4a's `RejZ`)

* **`coords_pt_view4`**: a coordinates phase's packed register holds the log's coordinates; Z1's
  is the context's `pt` at Z2 (**`pt_cAt4`**), Z2's second output the context's `uni` at Z3
  (**`uni_cAt5`**).
* **`z3_head_seg4`**, **`z3_head_node4`**: Z3's first claim (Z2's `lagrangeS` at the target
  `targetS pe`) is P4a's `c0Z M` — `lagrangeS` at `lagrangeSS` (parameter `hLS`), the target at
  the kind's specification (segment `targetSSegS`, through P4c's `peL_seg` with `lastOps`' bits;
  node `targetSNode4S`, through S-CN4's `peL_node4`; parameter `hTS`).
* **`z_end4`**: `relZ4` (i) through the views is `RejZ`'s equation; **`not_rejZ_seg4`**,
  **`not_rejZ_node4`**.
-/

namespace FR.Snd.R4
open RecursionFast Rev4

variable {impl : OpImpl} {p : KindP} {inp : Input}

/-! ## Z1's packed point and Z2's claim register in the contexts -/

/-- **A coordinates phase's packed register** (`outs[n]`'s head) holds the log's coordinates. -/
theorem coords_pt_view4 {tr : Trace} {y : List Val × List Bool × Trace} (h : SkRun4 impl p inp tr y)
    {n : ℕ} (hn : n < (phasesOf seq4).length) {k : ℕ}
    (hsh : (phasesOf seq4)[n].2 = .squeezes k .coords) (hk : 0 < k) :
    ((skeleton4 seq4 p).2.outs.getD n []).headD 0 < (#[] ++ y.1.toArray).size ∧
      ∀ l < 2 * k, ((rd (#[] ++ y.1.toArray) (((skeleton4 seq4 p).2.outs.getD n []).headD 0)).toAF).getD l 0 =
        fAt (fsOf tr (itemsOf seq4)) (phStart4 n + l / 2) (l % 2) := by
  obtain ⟨trk, M, x, hx, hb, -, hext, -, hdrop, -⟩ := phase_at4 impl p.tix inp p h.ref hn
  have hout := skeleton4_outs seq4 p hn
  generalize hph : (phasesOf seq4)[n] = ph at hx hsh hout
  obtain ⟨name, sh⟩ := ph
  simp only at hsh; subst hsh
  simp only [refPhase4] at hx
  obtain ⟨xs, hxs, rfl⟩ := Option.map_eq_some_iff.1 hx
  obtain ⟨hl, hans⟩ := sqz_entries4 hn (by rw [hph]) hk hxs hdrop
  dsimp only at hext
  have hsz := hext.1
  simp only [Array.size_append, List.size_toArray, List.length_append, coordVals_length, hl,
    List.length_singleton, List.size_toArray] at hsz
  have hpt : ((skeleton4 seq4 p).2.outs.getD n []).headD 0 = M.length + 3 * k := by
    rw [hout]; simp [genPhase4, hb]
  rw [hpt]
  refine ⟨lt_reg (by simp only [List.length_nil, Nat.zero_add] at hsz; simp; omega), fun l hl2 => ?_⟩
  have hfl : (xs.1.flatMap coordVals).length = 3 * k := by rw [coordVals_length, hl]
  rw [rd_phase4 hext (by simp only [List.length_append, List.length_singleton]; omega),
    List.getD_append_right _ _ _ _ (by omega), hfl, Nat.sub_self, List.getD_cons_zero]
  simp only [Val.toAF, FR.coordsOf, Array.getD_eq_getD_getElem?, List.getElem?_toArray,
    List.getElem?_map, List.getElem?_range, show l < 2 * xs.1.length by omega, Option.map_some,
    Option.getD_some]
  rw [fAt, ← hans _ (by omega)]

/-- **The context at Z2 points at Z1's packed register.** -/
theorem pt_cAt4 : (cAt4 seq4 p 4).pt = ((skeleton4 seq4 p).2.outs.getD 3 []).headD 0 := by
  rw [cAt4_succ seq4 p (k := 3) (by decide), skeleton4_outs seq4 p (k := 3) (by decide)]
  have e : (phasesOf seq4)[3] = ("Z1", .squeezes (half seq4.z1) .coords) := rfl
  rw [e]
  simp [genPhase4]

/-- **The context at Z3 points at Z2's second output** (`P^{ab}*(λ)`). -/
theorem uni_cAt5 : (cAt4 seq4 p 5).uni = ((skeleton4 seq4 p).2.outs.getD 4 []).getD 1 0 := by
  rw [cAt4_succ seq4 p (k := 4) (by decide), skeleton4_outs seq4 p (k := 4) (by decide)]
  have e : (phasesOf seq4)[4] = ("Z2", .uni fZ2) := rfl
  rw [e]
  cases hn : p.d.node <;> simp [genPhase4, hn]

/-! ## Z3's first claim is `c0Z` -/

theorem extA_refl (R : Array Val) : ExtA R R := ⟨le_rfl, fun _ _ => rfl⟩

/-- `lastAt` of a point whose entries from 19 are `lastBits` is `lastL`. -/
theorem lastAt_pad19 (es : Log) (xs : List F) (hxs : xs.length = 19) :
    Rev4.lastAt (xs ++ P4a.lastBits es).toArray 19 = P4a.lastL es := by
  unfold Rev4.lastAt
  have e : ∀ l ∈ Finset.range 18, (if (xs ++ P4a.lastBits es).toArray.getD (19 + l) 0 = 1 then 2 ^ l else 0) =
      if (P4a.lastL es).testBit l then 2 ^ l else 0 := fun l hl => by
    have hl' := Finset.mem_range.1 hl
    have hg : (xs ++ P4a.lastBits es).toArray.getD (19 + l) 0 = (P4a.lastBits es).getD l 0 := by
      simp only [Array.getD_eq_getD_getElem?, List.getElem?_toArray, List.getD_eq_getElem?_getD,
        List.getElem?_append_right (show xs.length ≤ 19 + l by omega), hxs, Nat.add_sub_cancel_left]
    rw [hg, P4a.lastBits_getD es hl']
    split_ifs <;> simp_all
  rw [Finset.sum_congr rfl e, P4a.sum_bits_self 18 _ (P4a.lastL_lt es)]

/-- Z2's `lagrangeS` value at a target `P^e` table is `c0Z`'s interpolant. -/
theorem lag_c0Z {tr : Trace} {y : List Val × List Bool × Trace} (h : SkRun4 impl p inp tr y)
    (hLS : ∀ v l pe, v.size = 127 → impl.lagrangeS v l pe = Impl.lagrangeSS v l pe)
    (M : P4a.ZLM4) {pe : Array F}
    (hpe : impl.targetS p.tix pe = Array.ofFn (P4a.peL M (fsOf tr (itemsOf seq4)))) :
    (impl.lagrangeS (uniEs inp 0 (fieldOffOf seq4 fZ2 + phaseOffOf seq4 4 fZ2)).toArray
      (fAt (fsOf tr (itemsOf seq4)) (phStart4 4 + 1) 0) (impl.targetS p.tix pe)).1 =
      P4a.c0Z M (fsOf tr (itemsOf seq4)) := by
  obtain ⟨hn4, e4⟩ := ph4 (n := 4) (x := ("Z2", Sh.uni fZ2)) rfl
  obtain ⟨-, -, -, -, -, -, -, hmsg, -, -⟩ := uni_view4 h hn4 (by rw [e4])
  have h13 : phStart4 4 = 13 := by rw [phStart4, fsStarts4_eq]; rfl
  rw [h13] at hmsg
  rw [hpe, hLS _ _ _ (by simp [uniEs]), Impl.lagrangeSS, P4a.c0Z, h13]
  have hv : ∀ i < 127, (uniEs inp 0 (fieldOffOf seq4 fZ2 + phaseOffOf seq4 4 fZ2)).toArray.getD i 0 =
      readF (msgAt (fsOf tr (itemsOf seq4)) 13) (16 * i) := fun i hi => by
    rw [hmsg i hi]
    simp [uniEs, Array.getD_eq_getD_getElem?, hi]
  have e1 : (fun k : Fin 64 => (uniEs inp 0 (fieldOffOf seq4 fZ2 + phaseOffOf seq4 4 fZ2)).toArray.getD k 0) =
      pzL (fsOf tr (itemsOf seq4)) := funext fun k => hv k (by omega)
  have e2 : (fun k : Fin 63 =>
      (uniEs inp 0 (fieldOffOf seq4 fZ2 + phaseOffOf seq4 4 fZ2)).toArray.getD (64 + k.val) 0) =
      pabL (fsOf tr (itemsOf seq4)) := funext fun k => hv (64 + k) (by omega)
  have e3 : (fun σ : Fin 64 => (Array.ofFn (P4a.peL M (fsOf tr (itemsOf seq4)))).getD σ 0) =
      P4a.peL M (fsOf tr (itemsOf seq4)) := funext fun σ => by simp [Array.getD_eq_getD_getElem?]
  rw [e1, e2, e3]
  rfl

/-- **A segment's Z3 first claim is `c0Z`** (`targetS` at `targetSSegS`: the point is Z1's
coordinates, zeros, then `lastOps`' bits, so P4c's `peL_seg` applies). -/
theorem z3_head_seg4 {σ : SegKind} {tr : Trace} {y : List Val × List Bool × Trace}
    (h : SkRun4 impl (.ofSeg σ) inp tr y)
    (hLS : ∀ v l pe, v.size = 127 → impl.lagrangeS v l pe = Impl.lagrangeSS v l pe)
    (hTS : ∀ r, impl.targetS (KindP.ofSeg σ).tix r = Rev4.targetSSegS r)
    (indN : NodeKind → Fin 9 → ℕ → F) (etN : NodeKind → ℕ → Fin (2 ^ 14) → F) :
    rd (#[] ++ y.1.toArray) (cAt4 seq4 (.ofSeg σ) 5).uni =
      .f (P4a.c0Z (P4a.zlm4 indN etN) (fsOf tr (itemsOf seq4))) := by
  obtain ⟨hn4, e4⟩ := ph4 (n := 4) (x := ("Z2", Sh.uni fZ2)) rfl
  obtain ⟨b, pe, hout, -, -, h133, -, -, -, hseg⟩ := uni_view4 h hn4 (by rw [e4])
  have hnode : (KindP.ofSeg σ).d.node = false := by cases σ <;> rfl
  obtain ⟨-, hpe⟩ := hseg hnode
  have hpe' := hpe (segPt_lt _ h.ref (by norm_num) (by decide))
  rw [uni_cAt5, hout]
  simp only [hnode, Bool.false_eq_true, ite_false, List.getD_cons_succ, List.getD_cons_zero] at h133 ⊢
  rw [h133]
  refine congrArg Val.f (lag_c0Z h hLS _ ?_)
  -- the point
  set fi : FinIn := ⟨(skeleton4 seq4 (.ofSeg σ)).2.outs, [], #[]⟩
  have hfi : fi.outs = (skeleton4 seq4 (.ofSeg σ)).2.outs := rfl
  have hR := extA_refl (#[] ++ y.1.toArray)
  have hsp : segPtRegs seq4 (.ofSeg σ) (cAt4 seq4 (.ofSeg σ) 4).outs =
      (coordsR fi "Z1").take ((KindP.ofSeg σ).d.m - 13) ++
        List.replicate (seq4.mStar - (KindP.ofSeg σ).d.m) (zeroReg fi) ++ lastRegs fi := by
    rw [segPtRegs, cAt4_outs seq4 _ (by norm_num) (by decide), cAt4_outs seq4 _ (by norm_num) (by decide)]
    rfl
  have hk := kindOfC_seg4 h
  have hm : (KindP.ofSeg σ).d.m = σ.m := (dims_seg4 σ).2.2
  have hmS : seq4.mStar = 32 := by rw [seq4_eq]
  obtain ⟨hn3, e3⟩ := ph4 (n := 3) (x := ("Z1", Sh.squeezes 10 .coords)) (by rw [seq4_eq]; rfl)
  have hle : σ.m - 13 ≤ 2 * 10 := by cases σ <;> decide
  have hco := coordsR_view4 h hfi hR hn3 (by rw [e3]) (by norm_num) phaseIx_vals.1 hle
  rw [show phStart4 3 = 3 by rw [phStart4, fsStarts4_eq]; rfl] at hco
  obtain ⟨hL, hz⟩ := lastRegs_view4 h hfi hR
  have hpe2 : pe = ((List.range (σ.m - 13)).map (coordAt (fsOf tr (itemsOf seq4)) 2) ++
      List.replicate (32 - σ.m) 0 ++ P4a.lastBits (fsOf tr (itemsOf seq4))).toArray := by
    rw [hpe', hsp, hm, hmS]
    simp only [List.map_append, List.map_replicate]
    rw [show (fun x => (rd (#[] ++ y.1.toArray) x).toF) = fv (#[] ++ y.1.toArray) from rfl, hco, show (rd (#[] ++ y.1.toArray) (zeroReg fi)).toF = 0 from hz, hL]
    rfl
  rw [hTS, hpe2]
  have hlen : ((List.range (σ.m - 13)).map (coordAt (fsOf tr (itemsOf seq4)) 2) ++
      List.replicate (32 - σ.m) 0).length = 19 := by simp; cases σ <;> rfl
  refine P4a.peL_seg (by rw [hk]; rfl) (fun l hl => ?_) (fun l h1 h2 => ?_) ?_
  · rw [hk] at hl; change l < σ.m - 13 at hl
    rw [Array.getD_eq_getD_getElem?, List.getElem?_toArray, List.append_assoc,
      List.getElem?_append_left (by simpa using hl), List.getElem?_map, List.getElem?_range hl]
    rfl
  · rw [hk] at h1; change σ.m - 13 ≤ l at h1
    rw [Array.getD_eq_getD_getElem?, List.getElem?_toArray,
      List.getElem?_append_left (by rw [hlen]; exact h2),
      List.getElem?_append_right (by simpa using h1), List.getElem?_replicate]
    split_ifs <;> rfl
  · exact lastAt_pad19 _ _ hlen

/-- **A node's Z3 first claim is `c0Z`** (`targetS` at `targetSNode4S`, S-CN4's `peL_node4`; the
point is Z1's packed register). -/
theorem z3_head_node4 {ν : NodeKind} {tr : Trace} {y : List Val × List Bool × Trace}
    (h : SkRun4 impl (.ofNode ν) inp tr y)
    (hLS : ∀ v l pe, v.size = 127 → impl.lagrangeS v l pe = Impl.lagrangeSS v l pe)
    (hTS : ∀ r, impl.targetS (KindP.ofNode ν).tix r = NT4.targetSNode4S ν r) :
    rd (#[] ++ y.1.toArray) (cAt4 seq4 (.ofNode ν) 5).uni =
      .f (P4a.c0Z (P4a.zlm4 N4c.indN4 N4c.etN4) (fsOf tr (itemsOf seq4))) := by
  obtain ⟨hn4, e4⟩ := ph4 (n := 4) (x := ("Z2", Sh.uni fZ2)) rfl
  obtain ⟨b, pe, hout, -, -, h133, -, -, hnd, -⟩ := uni_view4 h hn4 (by rw [e4])
  have hnode : (KindP.ofNode ν).d.node = true := by cases ν <;> rfl
  have hpe := hnd hnode
  rw [uni_cAt5, hout]
  simp only [hnode, ite_true, List.getD_cons_succ, List.getD_cons_zero] at h133 ⊢
  rw [h133]
  refine congrArg Val.f (lag_c0Z h hLS _ ?_)
  obtain ⟨hn3, e3⟩ := ph4 (n := 3) (x := ("Z1", Sh.squeezes 10 .coords)) (by rw [seq4_eq]; rfl)
  obtain ⟨-, hco⟩ := coords_pt_view4 h hn3 (by rw [e3]) (by norm_num)
  rw [hTS, hpe, pt_cAt4]
  refine CN4.peL_node4 (kindOfC_node4 h) fun l hl => ?_
  have hl' : l < 2 * 10 := by have : NT4.nbN ν ≤ 18 := by cases ν <;> decide
                              omega
  rw [hco l hl', show phStart4 3 = 3 by rw [phStart4, fsStarts4_eq]; rfl]
  rfl

/-! ## `finZ` on the fields; Z3's last claim (`RejZ`) -/

theorem rest_gFinZ (P : FinP) :
    (finalsOf P).rest[0]'(by rw [rest_finalsOf_length]; decide) = gFinZ P := by
  simp only [Finals.rest, finalsOf, List.cons_append, List.getElem_cons_zero]

/-- `finZ`'s registers are named or `zhat` registers (abstract `fi`). -/
theorem hin_Z {fi : FinIn} {n : ℕ} (hsk : ∀ name, ∀ x ∈ outsOf fi name, x < n) (hn : 0 < n)
    (P : FinP) (hz : ∀ x ∈ fi.zhat, x < n) :
    ∀ x ∈ coordsR fi "Z1" ++ chals fi "Z3" P.S.z3 ++
      [claimN fi "Z3", (outsOf fi "Z2").getD 2 0, fi.zhat.getD 0 0], x < n := by
  intro x hx
  simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hx
  rcases hx with (hx | hx) | rfl | rfl | rfl
  · exact hsk "Z1" x (List.mem_of_mem_drop hx)
  · exact hsk "Z3" x (List.mem_of_mem_drop (List.mem_of_mem_take hx))
  · exact getLastD_lt (hsk "Z3") hn
  · exact getD_lt hn (hsk "Z2") 2
  · exact getD_lt hn hz 0

/-- **`finZ`'s relation on the fields of an accepted run** (field 0, file `Rs 0`). -/
theorem relZ4_of_fields {tr : Trace} {P : FinP} {y : List Val × List Bool × Trace} {zh : List Reg}
    {Rs : ℕ → Array Val} {Ex : ℕ → Array (List Reg)} (hF : Fields4 impl p inp tr P y zh Rs Ex) :
    relZ4 p.tix inp ⟨(skeleton4 seq4 p).2.outs, zh, Ex 0⟩ (Rs 0) P = true := by
  obtain ⟨-, L0, hL0, -, -⟩ := hF.fld 0 (by decide)
  rw [rest_gFinZ] at hL0
  obtain ⟨L', hL'⟩ := flag_gFinZ impl p.tix inp ⟨(skeleton4 seq4 p).2.outs, zh, Ex 0⟩ (Rs 0) P
    (hin_Z (hF.sk_lt (by decide) _) (hF.pos (by decide)) P (hF.zlt' (by decide)))
  exact pureRun_det hL0 hL'

theorem clR_c0_eq {c0 c0' : Log → Log → F} {L es : Log} (hc : c0 L es = c0' L es) (b : ℕ) :
    ∀ n, clR b c0 L es n = clR b c0' L es n
  | 0 => hc
  | n + 1 => by simp only [clR, clR_c0_eq hc b n]

/-- **Z3's last claim on the fields** (`relZ4` (i) through the views), for any kind whose `m` the
finals and the chain agree on, from Z3's first claim `c0Z M`. -/
theorem z_chk4 {tr : Trace} {P : FinP} {y : List Val × List Bool × Trace} {zh : List Reg}
    {Rs : ℕ → Array Val} {Ex : ℕ → Array (List Reg)} (hF : Fields4 impl p inp tr P y zh Rs Ex)
    (hPS : P.S = seq4) (hm : P.kv.m p.tix = (kindOfC (fsOf tr (itemsOf seq4))).m)
    (hz3 : p.d.seq.z3 = (kindOfC (fsOf tr (itemsOf seq4))).m - 6)
    (M : P4a.ZLM4) (hc : rd (#[] ++ y.1.toArray) (cAt4 seq4 p 5).uni = .f (P4a.c0Z M (fsOf tr (itemsOf seq4))))
    (L : Log) :
    clR 15 (fun _ es => P4a.c0Z M es) L (fsOf tr (itemsOf seq4)) (P4a.mC 6 (kindOfC (fsOf tr (itemsOf seq4)))) =
      eq (ptOf (P4a.mC 6 (kindOfC (fsOf tr (itemsOf seq4)))) (P4a.zrL (fsOf tr (itemsOf seq4))))
          (ptOf (P4a.mC 6 (kindOfC (fsOf tr (itemsOf seq4)))) (P4a.rZ (fsOf tr (itemsOf seq4)))) *
        (vZ (fsOf tr (itemsOf seq4)) 0 * vZ (fsOf tr (itemsOf seq4)) 1) := by
  have hrel := relZ4_of_fields hF
  simp only [relZ4, hm, hPS, Bool.and_eq_true] at hrel
  have h1 := val_eqv_f4 hrel.1
  set es := fsOf tr (itemsOf seq4)
  set κ := kindOfC es
  set fi : FinIn := ⟨(skeleton4 seq4 p).2.outs, zh, Ex 0⟩
  have hfi : fi.outs = (skeleton4 seq4 p).2.outs := rfl
  have hE := hF.ext 0 (by decide)
  have hκ := CKind.m_mem κ
  obtain ⟨hn5, e5⟩ := ph4 (n := 5) (x := ("Z3", Sh.rounds fZ3 seq4.z3 3 false)) rfl
  obtain ⟨hcl, hcv, -, hlt, hlast⟩ := roundsF3_view4 hF.sk hn5 (by rw [e5]) L
  rw [e5, (initClaim_vals).1] at hcv
  rw [hcv] at hlast
  have hN := hlast _ hc
  have hle : p.d.seq.z3 ≤ seq4.z3 := by rw [hz3, seq4_eq]; show κ.m - 6 ≤ 26; omega
  rw [e5, (realRounds_vals _ _).1, Nat.min_eq_left hle, hz3,
    show phStart4 5 = 15 by rw [phStart4, fsStarts4_eq]; rfl] at hN
  rw [(outsOf_skel hfi "Z3").2.2, phaseIx4_rounds.2.1, hE.rd hlt, hN] at h1
  rw [P4a.mC, clR_c0_eq (c0' := fun _ _ => P4a.c0Z M es) rfl, Val.f.inj h1]
  -- the right-hand side
  obtain ⟨hn3, e3⟩ := ph4 (n := 3) (x := ("Z1", Sh.squeezes 10 .coords)) (by rw [seq4_eq]; rfl)
  have hco := coordsR_view4 hF.sk hfi hE hn3 (by rw [e3]) (by norm_num) phaseIx_vals.1
    (a := κ.m - 13) (by omega)
  rw [show phStart4 3 = 3 by rw [phStart4, fsStarts4_eq]; rfl] at hco
  have hch := chals_view4 hF.sk hfi hE hn5 (by rw [e5]) phaseIx4_rounds.2.1 (a := κ.m - 6)
    (by rw [seq4_eq]; show κ.m - 6 ≤ 26; omega)
  rw [show phStart4 5 = 15 by rw [phStart4, fsStarts4_eq]; rfl] at hch
  have htk : (chals fi "Z3" seq4.z3).take (κ.m - 6) = chals fi "Z3" (κ.m - 6) := by
    rw [chals, chals, List.take_take, Nat.min_eq_left (by rw [seq4_eq]; show κ.m - 6 ≤ 26; omega)]
  have hm1 := fsMsgs4_front.1
  have hv : ∀ j < 2, vZ es j = pe4 seq4 inp fZend (16 * j) := fun j hj => by
    rw [vZ, msg_abs4 hF.sk (by norm_num) (by norm_num) hm1 (by omega)]; rfl
  rw [htk, hco, hch, FR.Impl.eqPoint_eq, hv 0 (by norm_num), hv 1 (by norm_num)]
  have hl : ∀ l : List F, l.toArray.size = l.length := fun _ => rfl
  rw [hl, FR.Impl.ptA_toArray, FR.Impl.ptA_toArray, List.length_append, List.length_ofFn,
    List.length_map, List.length_range, show 7 + (κ.m - 13) = κ.m - 6 by omega, mul_assoc]
  rfl

/-- **`RejZ` never holds on an accepted segment run** (`lagrangeS`, `targetS` at their
specifications; `M` the segment's `zlm4`). -/
theorem not_rejZ_seg4 {σ : SegKind} {tr : Trace}
    (hLS : ∀ v l pe, v.size = 127 → impl.lagrangeS v l pe = Impl.lagrangeSS v l pe)
    (hTS : ∀ r, impl.targetS (KindP.ofSeg σ).tix r = Rev4.targetSSegS r)
    (indN : NodeKind → Fin 9 → ℕ → F) (etN : NodeKind → ℕ → Fin (2 ^ 14) → F)
    (h : semIR impl (gen4 seq4 (.ofSeg σ) (finOps4 (segFinP σ))) inp tr = some true) (L : Log) :
    ¬ P4a.RejZ (P4a.zlm4 indN etN) L (fsOf tr (itemsOf seq4)) := by
  obtain ⟨y, zh, Rs, Ex, hF⟩ := fields4_of_accept (segFinP σ) h
  have hk := kindOfC_seg4 hF.sk
  exact fun ⟨_, hne⟩ => hne (z_chk4 hF rfl (by rw [hk]; rfl) (by rw [hk, (dims_seg4 σ).1]) _
    (z3_head_seg4 hF.sk hLS hTS indN etN) L)

/-- **… nor on an accepted node run** (`targetS` at `targetSNode4S`: the node's `tS`, a parameter
until `targetSNode4I`). -/
theorem not_rejZ_node4 {ν : NodeKind} {cells : List ℕ} {tr : Trace}
    (hLS : ∀ v l pe, v.size = 127 → impl.lagrangeS v l pe = Impl.lagrangeSS v l pe)
    (hTS : ∀ r, impl.targetS (KindP.ofNode ν).tix r = NT4.targetSNode4S ν r)
    (h : semIR impl (gen4 seq4 (.ofNode ν) (finOps4 (nodeFinP ν cells))) inp tr = some true) (L : Log) :
    ¬ P4a.RejZ (P4a.zlm4 N4c.indN4 N4c.etN4) L (fsOf tr (itemsOf seq4)) := by
  obtain ⟨y, zh, Rs, Ex, hF⟩ := fields4_of_accept (nodeFinP ν cells) h
  have hk := kindOfC_node4 hF.sk
  exact fun ⟨_, hne⟩ => hne (z_chk4 hF rfl (by rw [hk]; rfl) (by rw [hk, (dims_node4 ν).1]) _
    (z3_head_node4 hF.sk hLS hTS) L)

end FR.Snd.R4
