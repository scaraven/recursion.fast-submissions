-- New for `flock-recursive` (BLUEPRINT revision 4.1, A.9 `finSh` (i), A.10 S2, B-12; stage R4e).
import FRSoundness4R4FrE
import FRSoundness4R4FinSh
import FRSoundness4R4Stmt
import FRSoundness4P4aLast
import FRSoundness4R4Ctrl
import FRSoundness4R4Fld
import FRNodeTarget4W
import FRVerifierImplNode4
import FRVerifierC4

/-!
# S2's round checks on an accepted run (P4a's `RejS2`)

* **The log's public reads**: the seed query is `seedQ vk c (π[0, 48))` (**`seedQ4`**), so its bytes
  `71 + o` are π's `o` (**`seed_bytesAt4`**); the `stmt` message is `π[48, 176)` (**`stmt_msg4`**),
  so the log's `n` is π's (**`nStmt_eq4`**). `bndL`'s four values are the program's `pe4` reads
  (**`bnd_seg4`**).
* **A segment's last block on the registers** (**`last_view4`**): the `stmt` phase's outputs after
  its state register are `lastOuts b₂`, and `lastOps` (P4a's `run_lastOps`) left `0` at `b₂ + 2` and
  `L`'s bits `bF (lb n k)` at `b₂ + 40 + 3k`.
* **`relSh4_of_accept`**: `finSh`'s relation holds on an accepted run (field 2 of the rest).
* **`s2_chk_seg4`**, **`s2_chk_node4`**: `relSh4` (i) through the views is `c0S` (for `shiftTarget`
  at its specification `shiftTargetS`, the parameter `hST`), so every real S2 round check holds;
  **`not_rejS2_seg4`**, **`not_rejS2_node4`**.
-/

namespace FR.Snd.R4
open RecursionFast Rev4

variable {impl : OpImpl} {p : KindP} {inp : Input}

/-! ## The seed and the statement on the log -/

theorem fieldOff_hdr_stmt4 : fieldOffOf seq4 fHdr = 0 ∧ fieldOffOf seq4 fStmt = 48 := by
  rw [seq4_eq]; decide +kernel


section Log
variable {tr : Trace} {y : List Val × List Bool × Trace} (h : SkRun4 impl p inp tr y)
include h

/-- **The seed entry's query** is `seedQ vk c hdr`, `hdr` π's first 48 bytes. -/
theorem seedQ4 : (entAt (fsOf tr (itemsOf seq4)) 0).1 = seedQ inp.vk inp.c (inp.π.extract 0 48) := by
  have h0 := h.hq 0 (by decide)
  obtain ⟨ms, hms⟩ := fsMsgs4_head seq4
  rw [hms] at h0
  simp only [List.getD_cons_zero, qOf, ite_true] at h0
  rw [entAt, h0]

theorem seed_byte4' {k : ℕ} (hk : k < 48) :
    (entAt (fsOf tr (itemsOf seq4)) 0).1.data.toList.getD (71 + k) 0 = inp.π.data.toList.getD k 0 := by
  rw [seedQ4 h, X.seedQ_data', List.getD_append_right _ _ _ _ (by simp [tagSeed]; omega),
    List.getD_append_right _ _ _ _ (by simp [tagSeed]; omega),
    List.getD_append_right _ _ _ _ (by simp [tagSeed]; omega), toList_extract]
  simp only [tagSeed, List.length_cons, List.length_nil, Vector.length_toList, Nat.sub_zero,
    List.drop_zero]
  rw [show 71 + k - 7 - 32 - 32 = k by omega, List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD,
    List.getElem?_take_of_lt hk]

/-- **The seed query's bytes `71 + o`** are π's bytes `o` (`o + n ≤ 48`). -/
theorem seed_bytesAt4 {o n : ℕ} (hon : o + n ≤ 48) :
    bytesAt (entAt (fsOf tr (itemsOf seq4)) 0).1 (71 + o) n = bytesAt inp.π o n := by
  ext k hk
  rw [getElem_bytesAt _ _ _ _ hk, getElem_bytesAt _ _ _ _ hk, Nat.add_assoc, seed_byte4' h (by omega)]

/-- **The `stmt` message on the log** is π's bytes `48 … 175`. -/
theorem stmt_msg4 : Snd.msgAt (fsOf tr (itemsOf seq4)) 1 = inp.π.extract 48 (48 + 128) := by
  have e := h.hq 1 (by decide)
  rw [fsMsgs4_ctl.1] at e
  simp only [qOf, one_ne_zero, if_false] at e
  exact msgAt_of_q e

/-- **The log's `n` is the program's** (the 24-bit index at π's byte 81). -/
theorem nStmt_eq4 : P4a.nStmt (fsOf tr (itemsOf seq4)) = idxOfF 24 (digestAt inp.π 81) 0 := by
  rw [P4a.nStmt, stmt_msg4 h, digestAt_eq, digestAt_eq, bytesAt_extract_of_le _ (by norm_num)]

/-- **A segment's boundary reads** (`bndL`'s four values) are the program's `pe4` reads. -/
theorem bnd_seg4 :
    [readF (entAt (fsOf tr (itemsOf seq4)) 0).1 87, readF (entAt (fsOf tr (itemsOf seq4)) 0).1 103,
      readF (Snd.msgAt (fsOf tr (itemsOf seq4)) 1) 1, readF (Snd.msgAt (fsOf tr (itemsOf seq4)) 1) 17] =
    [pe4 seq4 inp fHdr 16, pe4 seq4 inp fHdr 32, pe4 seq4 inp fStmt 1, pe4 seq4 inp fStmt 17] := by
  obtain ⟨h0, h1⟩ := fieldOff_hdr_stmt4
  simp only [readF, pe4, h0, h1, stmt_msg4 h, bytesAt_extract_of_le16 _ (show 1 + 16 ≤ 128 by norm_num),
    bytesAt_extract_of_le16 _ (show 17 + 16 ≤ 128 by norm_num),
    show (87 : ℕ) = 71 + 16 from rfl, show (103 : ℕ) = 71 + 32 from rfl,
    seed_bytesAt4 h (show 16 + 16 ≤ 48 by norm_num), seed_bytesAt4 h (show 32 + 16 ≤ 48 by norm_num)]

end Log

/-! ## A segment's last block on the registers -/

theorem phaseIx_stmt : phaseIx "stmt" = 1 := by decide

/-- **The `stmt` phase of an accepted segment run**: its outputs after the state register are
`lastOuts b₂`; `lastOps` left `0` at `b₂ + 2` and bit `k` of `L = n − 1` at `b₂ + 40 + 3k`
(`n` the index at π's byte 81). -/
theorem last_view4 {σ : SegKind} {tr : Trace} {y : List Val × List Bool × Trace}
    (h : SkRun4 impl (.ofSeg σ) inp tr y) :
    ∃ b₂, ((skeleton4 seq4 (.ofSeg σ)).2.outs.getD 1 []).drop 1 = lastOuts b₂ ∧
      b₂ + 94 ≤ (#[] ++ y.1.toArray).size ∧ rd (#[] ++ y.1.toArray) (b₂ + 2) = .f 0 ∧
      ∀ k < 18, rd (#[] ++ y.1.toArray) (b₂ + 40 + 3 * k) =
        .f (P4a.bF (P4a.lb (idxOfF 24 (digestAt inp.π 81) 0) k)) := by
  obtain ⟨trk, M, x, hx, hb, -, hext, -, -, -⟩ := phase_at4 impl _ inp _ h.ref (k := 1) (by decide)
  have hph : (phasesOf seq4)[1] = ("stmt", .absorb fStmt 128) := rfl
  have hnode : (KindP.ofSeg σ).d.node = false := by cases σ <;> rfl
  have hout := skeleton4_outs seq4 (KindP.ofSeg σ) (k := 1) (by decide)
  rw [hph] at hx hout
  simp only [refPhase4] at hx
  obtain ⟨⟨a, trk'⟩, -, hx⟩ := Option.bind_eq_some_iff.1 hx
  obtain ⟨z, hz, rfl⟩ := Option.map_eq_some_iff.1 hx
  simp only [absTail4, ite_true, hnode, Bool.false_eq_true, ite_false] at hz
  generalize ho : fieldOffOf seq4 fStmt + phaseOffOf seq4 1 fStmt = o at hz hout
  have ho' : o = 48 := by rw [← ho, stmtOff4]
  rw [pureRun_append] at hz
  obtain ⟨⟨L1, f1⟩, h1, hz⟩ := Option.bind_eq_some_iff.1 hz
  obtain ⟨⟨L2, f2⟩, h2, rfl⟩ := Option.map_eq_some_iff.1 hz
  have hl1 := pureRun_len impl _ inp _ _ _ _ _ h1
  simp only [List.length_cons, List.length_nil] at hl1
  set b₂ := (#[] ++ M.toArray).size + 2 + opsOut (stmtOps4 (.ofSeg σ) o (#[] ++ M.toArray).size
    ((#[] ++ M.toArray).size + 2)) with hb₂
  have hs : (#[] ++ M.toArray ++ L1.toArray).size = b₂ := by simp [hl1, hb₂]; omega
  have hrun := P4a.run_lastOps impl (KindP.ofSeg σ).tix inp o (#[] ++ M.toArray ++ L1.toArray)
  rw [hs] at hrun
  have hreb := pureRun_rebase impl (KindP.ofSeg σ).tix inp (lastOps o b₂) (#[] ++ M.toArray) L1 []
  rw [List.append_nil, hrun, h2] at hreb
  obtain ⟨rfl, -⟩ := Prod.mk.inj (Option.some.inj hreb)
  have hl := pureRun_len impl _ inp _ _ _ _ _ hrun
  rw [opsOut_lastOps, List.length_nil, Nat.zero_add] at hl
  have hML : (M ++ L1).length = b₂ := by simpa using hs
  dsimp only at hext
  rw [← List.append_assoc] at hext
  have hD : digestAt inp.π (absOff 0 (o + 33)) = digestAt inp.π 81 := by rw [absOff_zero, ho']
  refine ⟨b₂, ?_, ?_, ?_, fun k hk => ?_⟩
  · rw [hout]; simp [genPhase4, hb, hnode, hb₂, ho]
  · have := hext.1; simp only [Array.size_append, List.size_toArray, List.length_append] at this ⊢
    simp only [List.length_append] at hML; omega
  · rw [← hML, rd_phase4 hext (by omega), P4a.lastVals_zero]
  · rw [← hML, Nat.add_assoc, rd_phase4 hext (by omega), P4a.lastVals_bit _ hk, hD]

/-! ## `finSh`'s relation on an accepted run -/

theorem rest_gFinSh (P : FinP) :
    (finalsOf P).rest[2]'(by rw [rest_finalsOf_length]; decide) = gFinSh P := by
  simp only [Finals.rest, finalsOf, List.cons_append, List.getElem_cons_succ, List.getElem_cons_zero]

/-- `finSh`'s registers are named or `zhat` registers (abstract `fi`). -/
theorem hin_Sh {fi : FinIn} {n : ℕ} (hsk : ∀ name, ∀ x ∈ outsOf fi name, x < n) (hn : 0 < n)
    (P : FinP) (hz : ∀ x ∈ fi.zhat, x < n) :
    ∀ x ∈ coordsR fi "S1" ++ chals fi "S2" P.S.s2 ++ lastRegs fi ++
      [claim0 fi "S2", claimN fi "S2", fi.zhat.getD 2 0, zeroReg fi,
       (coordsR fi "S1").getD (P.S.mStar - 14 + 10) 0], x < n := by
  intro x hx
  simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hx
  rcases hx with ((hx | hx) | hx) | rfl | rfl | rfl | rfl | rfl
  · exact hsk "S1" x (List.mem_of_mem_drop hx)
  · exact hsk "S2" x (List.mem_of_mem_drop (List.mem_of_mem_take hx))
  · exact hsk "stmt" x (List.mem_of_mem_drop hx)
  · exact headD_lt (hsk "S2") hn
  · exact getLastD_lt (hsk "S2") hn
  · exact getD_lt hn hz 2
  · exact getD_lt hn (hsk "stmt") 1
  · exact getD_lt hn (fun x hx => hsk "S1" x (List.mem_of_mem_drop hx)) _

/-- **`finSh`'s relation on the fields of an accepted run** (field 2, file `Rs 2`). -/
theorem relSh4_of_fields {tr : Trace} {P : FinP} {y : List Val × List Bool × Trace} {zh : List Reg}
    {Rs : ℕ → Array Val} {Ex : ℕ → Array (List Reg)} (hF : Fields4 impl p inp tr P y zh Rs Ex) :
    relSh4 impl p.tix inp ⟨(skeleton4 seq4 p).2.outs, zh, Ex 2⟩ (Rs 2) P = true := by
  obtain ⟨-, L2, hL2, -, -⟩ := hF.fld 2 (by decide)
  rw [rest_gFinSh] at hL2
  obtain ⟨L', hL'⟩ := flag_gFinSh impl p.tix inp ⟨(skeleton4 seq4 p).2.outs, zh, Ex 2⟩ (Rs 2) P
    (hin_Sh (hF.sk_lt (by decide) _) (hF.pos (by decide)) P (hF.zlt' (by decide)))
  exact pureRun_det hL2 hL'

/-- **`finSh`'s relation on an accepted run.** -/
theorem relSh4_of_accept (P : FinP) {tr : Trace}
    (h : semIR impl (gen4 seq4 p (finOps4 P)) inp tr = some true) :
    ∃ y, SkRun4 impl p inp tr y ∧ ∃ (fi : FinIn) (R : Array Val),
      fi.outs = (skeleton4 seq4 p).2.outs ∧ ExtA (#[] ++ y.1.toArray) R ∧ (∀ x ∈ fi.zhat, x < R.size) ∧
      relSh4 impl p.tix inp fi R P = true := by
  obtain ⟨y, zh, Rs, Ex, hF⟩ := fields4_of_accept P h
  exact ⟨y, hF.sk, ⟨(skeleton4 seq4 p).2.outs, zh, Ex 2⟩, Rs 2, rfl, hF.ext 2 (by decide), hF.zlt' (by decide),
    relSh4_of_fields hF⟩

/-! ## S1's coordinates and S2's challenges by name -/

/-- A list mapped to `g` on `range N`: its length is `N`, its entries `g j`. -/
theorem map_getElem_of {α β : Type} {co : List α} {f : α → β} {g : ℕ → β} {N : ℕ}
    (hco : co.map f = (List.range N).map g) :
    co.length = N ∧ ∀ j (hj : j < co.length), f co[j] = g j := by
  have hl := congrArg List.length hco
  simp only [List.length_map, List.length_range] at hl
  refine ⟨hl, fun j hj => ?_⟩
  have := congrArg (fun l => l[j]?) hco
  simp only [List.getElem?_map, List.getElem?_range, show j < N by omega,
    List.getElem?_eq_getElem hj, Option.map_some, Option.some.injEq] at this
  exact this

/-- The first `N` entries mapped to `g`: `N ≤` the length, entries `j < N` are `g j`. -/
theorem take_map_getElem {α β : Type} {co : List α} {f : α → β} {g : ℕ → β} {N : ℕ}
    (hco : (co.take N).map f = (List.range N).map g) :
    N ≤ co.length ∧ ∀ j (hj : j < co.length), j < N → f co[j] = g j := by
  obtain ⟨hl, hg⟩ := map_getElem_of hco
  simp only [List.length_take] at hl
  refine ⟨by omega, fun j hj hjN => ?_⟩
  have := hg j (by simp; omega)
  rwa [List.getElem_take] at this

section S1
variable {tr : Trace} {y : List Val × List Bool × Trace} (h : SkRun4 impl p inp tr y)
  {fi : FinIn} (hfi : fi.outs = (skeleton4 seq4 p).2.outs) {R : Array Val} (hR : ExtA (#[] ++ y.1.toArray) R)
include h hfi hR

/-- **S1's coordinates by name** (`coS`): `κ_s` at 28, `τ`'s first `n ≤ 18`, `θ` at 18 … 27. -/
theorem s1_view4 :
    fv R ((coordsR fi "S1").getD 28 0) = ksL (fsOf tr (itemsOf seq4)) ∧
      (∀ n ≤ 18, ((coordsR fi "S1").take n).map (fv R) = (List.range n).map (coS (fsOf tr (itemsOf seq4)))) ∧
      (((coordsR fi "S1").drop 18).take 10).map (fv R) = thL (fsOf tr (itemsOf seq4)) := by
  obtain ⟨hn11, e11⟩ := ph4 (n := 11) (x := ("S1", Sh.squeezes 15 .coords)) (by rw [seq4_eq]; rfl)
  have hco := coordsR_view4 h hfi hR hn11 (by rw [e11]) (by norm_num) phaseIx_vals.2.2.2.2.2.2.1
    (a := 29) (by norm_num)
  rw [show phStart4 11 = 99 by rw [phStart4, fsStarts4_eq]; rfl] at hco
  obtain ⟨hlen, hget⟩ := take_map_getElem hco
  refine ⟨?_, fun n hn => ?_, ?_⟩
  · rw [List.getD_eq_getElem _ _ (by omega), hget 28 (by omega) (by norm_num)]; rfl
  · apply List.ext_getElem (by simp; omega)
    intro j h1 h2
    simp only [List.getElem_map, List.getElem_take, List.getElem_range]
    simp only [List.length_map, List.length_range] at h2
    rw [hget j (by omega) (by omega)]; rfl
  · apply List.ext_getElem (by simp [thL]; omega)
    intro j h1 h2
    simp only [List.getElem_map, List.getElem_take, List.getElem_drop, List.getElem_range, thL]
    simp only [thL, List.length_map, List.length_range] at h2
    rw [hget _ (by omega) (by omega)]; rfl

/-- **S2's challenges by name**: the block part (`n ≤ 18`) and the 10 position coordinates after
it are the log's `rch 114`. -/
theorem s2r_view4 {n : ℕ} (hn : n ≤ 18) :
    ((chals fi "S2" seq4.s2).take n).map (fv R) = (List.range n).map (rch 114 (fsOf tr (itemsOf seq4))) ∧
      (((chals fi "S2" seq4.s2).drop n).take 10).map (fv R) =
        (List.range 10).map (fun l => rch 114 (fsOf tr (itemsOf seq4)) (n + l)) := by
  obtain ⟨hn12, e12⟩ := ph4 (n := 12) (x := ("S2", Sh.rounds fS2 seq4.s2 2 false)) rfl
  have hch := chals_view4 h hfi hR hn12 (by rw [e12]) phaseIx4_rounds.2.2.2.1 le_rfl
  rw [show phStart4 12 = 114 by rw [phStart4, fsStarts4_eq]; rfl, rchs] at hch
  obtain ⟨hlen, hget⟩ := map_getElem_of hch
  have h28 : seq4.s2 = 28 := by rw [seq4_eq]
  replace hlen := hlen.trans h28
  constructor
  · apply List.ext_getElem (by simp; omega)
    intro j h1 h2
    simp only [List.getElem_map, List.getElem_take, List.getElem_range]
    simp only [List.length_map, List.length_range] at h2
    rw [hget j (by omega)]
  · apply List.ext_getElem (by simp; omega)
    intro j h1 h2
    simp only [List.getElem_map, List.getElem_take, List.getElem_drop, List.getElem_range]
    simp only [List.length_map, List.length_range] at h2
    rw [hget _ (by omega)]

/-- **S2 from its head claim**: the real rounds' checks hold from `c`, and S2's last claim register
holds the claim after them. -/
theorem s2_from_head4 (hle : p.d.seq.s2 ≤ seq4.s2) {c : F} (hc : rd R (claim0 fi "S2") = .f c) (L : Log) :
    (∀ l < p.d.seq.s2, Chk2 114 16 readF (fun d => chF d 0) (fun _ _ => c) L (fsOf tr (itemsOf seq4)) l) ∧
      rd R (claimN fi "S2") =
        .f (clR2 114 16 readF (fun d => chF d 0) (fun _ _ => c) L (fsOf tr (itemsOf seq4)) p.d.seq.s2) := by
  obtain ⟨hn12, e12⟩ := ph4 (n := 12) (x := ("S2", Sh.rounds fS2 seq4.s2 2 false)) rfl
  obtain ⟨hcl, -, -, hlt, hlast⟩ := roundsF2_view4 h hn12 (by rw [e12]) L
  rw [(outsOf_skel hfi "S2").2.1, phaseIx4_rounds.2.2.2.1] at hc
  rw [← hR.rd hcl, hc] at hlast
  obtain ⟨hN, hchk⟩ := hlast _ rfl
  rw [e12, (realRounds_vals _ _).2.1, Nat.min_eq_left hle,
    show phStart4 12 = 114 by rw [phStart4, fsStarts4_eq]; rfl] at hchk hN
  refine ⟨hchk, ?_⟩
  rw [(outsOf_skel hfi "S2").2.2, phaseIx4_rounds.2.2.2.1, hR.rd hlt, hN]

end S1

/-! ## S2's head and last claims on the fields -/

section Head
variable {tr : Trace} {y : List Val × List Bool × Trace} {zh : List Reg} {Rs : ℕ → Array Val}
  {Ex : ℕ → Array (List Reg)}

/-- **A segment's `stmt` registers in a field's input**: `lastRegs` hold `lastBits`, `zeroReg`
holds `0`. -/
theorem lastRegs_view4 {σ : SegKind} (h : SkRun4 impl (.ofSeg σ) inp tr y) {fi : FinIn}
    (hfi : fi.outs = (skeleton4 seq4 (.ofSeg σ)).2.outs) {R : Array Val} (hR : ExtA (#[] ++ y.1.toArray) R) :
    (lastRegs fi).map (fv R) = P4a.lastBits (fsOf tr (itemsOf seq4)) ∧ fv R (zeroReg fi) = 0 := by
  obtain ⟨b₂, hout, hsz, hz, hbits⟩ := last_view4 h
  have e : outsOf fi "stmt" = (outsOf fi "stmt").take 1 ++ lastOuts b₂ := by
    rw [← hout, (outsOf_skel hfi "stmt").1, phaseIx_stmt, List.take_append_drop]
  constructor
  · rw [lastRegs, e, List.drop_append, List.length_take]
    rw [(outsOf_skel hfi "stmt").1, phaseIx_stmt] at e ⊢
    have h1 : ((skeleton4 seq4 (.ofSeg σ)).2.outs.getD 1 []).length = 20 := by
      have := congrArg List.length e
      simp only [List.length_append, List.length_take, lastOuts, List.length_cons, List.length_map,
        List.length_range] at this
      omega
    rw [h1, show min 1 20 = 1 from rfl, show 2 - 1 = 1 from rfl, List.drop_of_length_le (by simp),
      List.nil_append]
    simp only [lastOuts, List.drop_succ_cons, List.drop_zero, List.map_map, P4a.lastBits, nStmt_eq4 h]
    apply List.map_congr_left
    intro k hk
    simp only [List.mem_range] at hk
    show (rd R (b₂ + 40 + 3 * k)).toF = _
    rw [hR.rd (by omega), hbits k hk]; rfl
  · rw [zeroReg, e]
    have h1 : ((outsOf fi "stmt").take 1).length = 1 := by
      rw [(outsOf_skel hfi "stmt").1, phaseIx_stmt]
      have := congrArg List.length (show (skeleton4 seq4 (.ofSeg σ)).2.outs.getD 1 [] = _ from
        (List.take_append_drop 1 _).symm)
      rw [hout] at this
      simp only [List.length_append, lastOuts, List.length_cons, List.length_map, List.length_range] at this
      simp only [List.length_take]; omega
    rw [List.getD_append_right _ _ _ _ (by omega), h1]
    show (rd R (b₂ + 2)).toF = _
    rw [hR.rd (by omega), hz]; rfl

/-- **A segment's S2 head claim is `c0S`** (`relSh4` (i) through the views; `shiftTarget` at
`shiftTargetS`). -/
theorem sh_head_seg4 {σ : SegKind}
    (hST : ∀ k a b c, c.size = 22 → impl.shiftTarget k a b c = FR.Impl.shiftTargetS k a b c)
    (hF : Fields4 impl (.ofSeg σ) inp tr (segFinP σ) y zh Rs Ex) :
    rd (Rs 2) (claim0 ⟨(skeleton4 seq4 (.ofSeg σ)).2.outs, zh, Ex 2⟩ "S2") =
      .f (P4a.c0S (fsOf tr (itemsOf seq4))) := by
  have hrel := relSh4_of_fields hF
  have hm : (segFinP σ).kv.m (KindP.ofSeg σ).tix = σ.m := rfl
  have hnode : (segFinP σ).kv.node (KindP.ofSeg σ).tix = false := rfl
  have hvn : (segFinP σ).vn = true := rfl
  have hS4 : (segFinP σ).S = seq4 := rfl
  have hmS : seq4.mStar = 32 := by rw [seq4_eq]
  simp only [relSh4, hm, hnode, hvn, hS4, hmS, Bool.and_eq_true, Bool.false_eq_true, ite_false,
    if_true, Nat.reduceSub, Nat.reduceAdd] at hrel
  rw [val_eqv_f4 hrel.1]
  congr 1
  set fi : FinIn := ⟨(skeleton4 seq4 (.ofSeg σ)).2.outs, zh, Ex 2⟩
  have hfi : fi.outs = (skeleton4 seq4 (.ofSeg σ)).2.outs := rfl
  have hE := hF.ext 2 (by decide)
  have hk := kindOfC_seg4 hF.sk
  obtain ⟨hks, hτ, hθ⟩ := s1_view4 hF.sk hfi hE
  obtain ⟨hL, -⟩ := lastRegs_view4 hF.sk hfi hE
  simp only [P4a.c0S, hk, P4a.bndL, P4a.endBits, CKind.isNode, Bool.false_eq_true,
    ite_false, bnd_seg4 hF.sk, P4a.pad18, P4a.tauL, P4a.nbC, CKind.m]
  have hle18 : σ.m - 14 ≤ 18 := by cases σ <;> decide
  rw [hL, hST _ _ _ _ (by simp [P4a.lastBits]), hks, hτ _ hle18, hθ,
    show 32 - σ.m = 18 - (σ.m - 14) by cases σ <;> rfl]

/-- **A node's S2 head claim is `c0S`** (boundary `0⁴ ‖ lastPad`). -/
theorem sh_head_node4 {ν : NodeKind} {cells : List ℕ}
    (hST : ∀ k a b c, c.size = 22 → impl.shiftTarget k a b c = FR.Impl.shiftTargetS k a b c)
    (hF : Fields4 impl (.ofNode ν) inp tr (nodeFinP ν cells) y zh Rs Ex) :
    rd (Rs 2) (claim0 ⟨(skeleton4 seq4 (.ofNode ν)).2.outs, zh, Ex 2⟩ "S2") =
      .f (P4a.c0S (fsOf tr (itemsOf seq4))) := by
  have hrel := relSh4_of_fields hF
  have hm : (nodeFinP ν cells).kv.m (KindP.ofNode ν).tix = ν.m := rfl
  have hnode : (nodeFinP ν cells).kv.node (KindP.ofNode ν).tix = true := rfl
  have hvn : (nodeFinP ν cells).vn = false := rfl
  have hS4 : (nodeFinP ν cells).S = seq4 := rfl
  have hmS : seq4.mStar = 32 := by rw [seq4_eq]
  simp only [relSh4, hm, hnode, hvn, hS4, hmS, Bool.and_eq_true, Bool.false_eq_true, ite_false,
    if_true, Nat.reduceSub, Nat.reduceAdd] at hrel
  rw [val_eqv_f4 hrel.1]
  congr 1
  set fi : FinIn := ⟨(skeleton4 seq4 (.ofNode ν)).2.outs, zh, Ex 2⟩
  have hfi : fi.outs = (skeleton4 seq4 (.ofNode ν)).2.outs := rfl
  have hk := kindOfC_node4 hF.sk
  obtain ⟨hks, hτ, hθ⟩ := s1_view4 hF.sk hfi (hF.ext 2 (by decide))
  simp only [P4a.c0S, hk, P4a.bndL, P4a.endBits, CKind.isNode, ite_true, P4a.pad18,
    P4a.tauL, P4a.nbC, CKind.m, Impl.lastPad]
  have hle18 : ν.m - 14 ≤ 18 := by cases ν <;> decide
  rw [hST _ _ _ _ (by simp; cases ν <;> rfl), hks, hτ _ hle18, hθ,
    show 32 - ν.m = 18 - (ν.m - 14) by cases ν <;> rfl]

end Head

/-! ## `RejS2` -/

theorem s2_chk_seg4 {σ : SegKind} {tr : Trace}
    (hST : ∀ k a b c, c.size = 22 → impl.shiftTarget k a b c = FR.Impl.shiftTargetS k a b c)
    (h : semIR impl (gen4 seq4 (.ofSeg σ) (finOps4 (segFinP σ))) inp tr = some true) (L : Log) :
    ∀ l < P4a.nrS (kindOfC (fsOf tr (itemsOf seq4))),
      Chk2 114 16 readF (fun d => chF d 0) P4a.c0SL L (fsOf tr (itemsOf seq4)) l := by
  obtain ⟨y, zh, Rs, Ex, hF⟩ := fields4_of_accept (segFinP σ) h
  have hle : (KindP.ofSeg σ).d.seq.s2 ≤ seq4.s2 := by cases σ <;> decide
  obtain ⟨hchk, -⟩ := s2_from_head4 hF.sk (fi := ⟨(skeleton4 seq4 (.ofSeg σ)).2.outs, zh, Ex 2⟩) rfl
    (hF.ext 2 (by decide)) hle (sh_head_seg4 hST hF) L
  rw [(dims_seg4 σ).2.1] at hchk
  intro l hl
  rw [kindOfC_seg4 hF.sk] at hl
  exact (chk2F_c0 (c0 := fun _ _ => P4a.c0S (fsOf tr (itemsOf seq4))) (c0' := P4a.c0SL) rfl 114 l).1
    (hchk l hl)

theorem s2_chk_node4 {ν : NodeKind} {cells : List ℕ} {tr : Trace}
    (hST : ∀ k a b c, c.size = 22 → impl.shiftTarget k a b c = FR.Impl.shiftTargetS k a b c)
    (h : semIR impl (gen4 seq4 (.ofNode ν) (finOps4 (nodeFinP ν cells))) inp tr = some true) (L : Log) :
    ∀ l < P4a.nrS (kindOfC (fsOf tr (itemsOf seq4))),
      Chk2 114 16 readF (fun d => chF d 0) P4a.c0SL L (fsOf tr (itemsOf seq4)) l := by
  obtain ⟨y, zh, Rs, Ex, hF⟩ := fields4_of_accept (nodeFinP ν cells) h
  have hle : (KindP.ofNode ν).d.seq.s2 ≤ seq4.s2 := by cases ν <;> decide
  obtain ⟨hchk, -⟩ := s2_from_head4 hF.sk (fi := ⟨(skeleton4 seq4 (.ofNode ν)).2.outs, zh, Ex 2⟩) rfl
    (hF.ext 2 (by decide)) hle (sh_head_node4 hST hF) L
  rw [(dims_node4 ν).2.1] at hchk
  intro l hl
  rw [kindOfC_node4 hF.sk] at hl
  exact (chk2F_c0 (c0 := fun _ _ => P4a.c0S (fsOf tr (itemsOf seq4))) (c0' := P4a.c0SL) rfl 114 l).1
    (hchk l hl)

/-- **`RejS2` never holds on an accepted segment run** (`shiftTarget` at its specification). -/
theorem not_rejS2_seg4 {σ : SegKind} {tr : Trace}
    (hST : ∀ k a b c, c.size = 22 → impl.shiftTarget k a b c = FR.Impl.shiftTargetS k a b c)
    (h : semIR impl (gen4 seq4 (.ofSeg σ) (finOps4 (segFinP σ))) inp tr = some true) (L : Log) :
    ¬ P4a.RejS2 L (fsOf tr (itemsOf seq4)) :=
  fun ⟨l, hl, _, hne⟩ => hne (s2_chk_seg4 hST h L l hl)

/-- **… nor on an accepted node run.** -/
theorem not_rejS2_node4 {ν : NodeKind} {cells : List ℕ} {tr : Trace}
    (hST : ∀ k a b c, c.size = 22 → impl.shiftTarget k a b c = FR.Impl.shiftTargetS k a b c)
    (h : semIR impl (gen4 seq4 (.ofNode ν) (finOps4 (nodeFinP ν cells))) inp tr = some true) (L : Log) :
    ¬ P4a.RejS2 L (fsOf tr (itemsOf seq4)) :=
  fun ⟨l, hl, _, hne⟩ => hne (s2_chk_node4 hST h L l hl)

/-- **`hST` from an op specification** whose `shiftTarget` is `shiftTargetS` (`specC`, `specSeg`,
`specN4` over `specC`). -/
theorem shiftTarget_of_meets {spec : OpSpec} (hm : impl.Meets spec)
    (hs : spec.shiftTarget = FR.Impl.shiftTargetS) :
    ∀ k a b c, c.size = 22 → impl.shiftTarget k a b c = FR.Impl.shiftTargetS k a b c :=
  fun k a b c hc => (hm.2.2.2.2.2.2.2.2.2.2.1 k a b c hc).trans (by rw [hs])

/-! ## `finSh` (ii): S2's last claim binds RS claim 2 (`oSh4`) -/

theorem clR2_c0_eq {c0 c0' : Log → Log → F} {L es : Log} (hc : c0 L es = c0' L es) (b n : ℕ) :
    clR2 b 16 readF (fun d => chF d 0) c0 L es n = clR2 b 16 readF (fun d => chF d 0) c0' L es n := by
  cases n <;> simp only [clR2, hc]

section Bind
variable {tr : Trace} {y : List Val × List Bool × Trace} {zh : List Reg} {Rs : ℕ → Array Val}
  {Ex : ℕ → Array (List Reg)}

/-- **A segment's S2 binding** (`relSh4` (ii) through the views): S2's last claim is
`wSumSeg · v`, `v` the `zhat` register of RS claim 2 (for `shiftMask`, `slotW`, `linkWAll` at the
segment's specifications). -/
theorem sh_bind_seg4 {σ : SegKind}
    (hST : ∀ k a b c, c.size = 22 → impl.shiftTarget k a b c = FR.Impl.shiftTargetS k a b c)
    (hSM : ∀ a b, impl.shiftMask a b = shiftSegS a b)
    (hSW : ∀ κ s a b, impl.slotW κ s a b = Impl.slotWS s a b)
    (hLW : ∀ tt rr, impl.linkWAll (KindP.ofSeg σ).tix tt rr = Array.replicate nLinkFam 0)
    (hF : Fields4 impl (.ofSeg σ) inp tr (segFinP σ) y zh Rs Ex) (wNS : CKind → Log → F) :
    P4a.oSh4 wNS (kindOfC (fsOf tr (itemsOf seq4))) (fsOf tr (itemsOf seq4)) (fv (Rs 2) (zh.getD 2 0)) := by
  have hrel := relSh4_of_fields hF
  have hm : (segFinP σ).kv.m (KindP.ofSeg σ).tix = σ.m := rfl
  have hnode : (segFinP σ).kv.node (KindP.ofSeg σ).tix = false := rfl
  have hvn : (segFinP σ).vn = true := rfl
  have hS4 : (segFinP σ).S = seq4 := rfl
  have hmS : seq4.mStar = 32 := by rw [seq4_eq]
  simp only [relSh4, hm, hnode, hvn, hS4, hmS, Bool.and_eq_true, Bool.false_eq_true, ite_false,
    if_true, Nat.reduceSub, Nat.reduceAdd, Bool.true_or, hSM, hSW, hLW, linkSum_zero] at hrel
  have h2 := val_eqv_f4 hrel.2
  set fi : FinIn := ⟨(skeleton4 seq4 (.ofSeg σ)).2.outs, zh, Ex 2⟩
  have hfi : fi.outs = (skeleton4 seq4 (.ofSeg σ)).2.outs := rfl
  have hE := hF.ext 2 (by decide)
  have hle : (KindP.ofSeg σ).d.seq.s2 ≤ seq4.s2 := by cases σ <;> decide
  obtain ⟨-, hN⟩ := s2_from_head4 hF.sk hfi hE hle (sh_head_seg4 hST hF) []
  have e := Val.f.inj (h2.symm.trans hN)
  have hk := kindOfC_seg4 hF.sk
  simp only [P4a.oSh4, P4a.claimSL4, P4a.wSumL4, hk, CKind.isNode, Bool.false_eq_true, ite_false]
  rw [show P4a.nrS (.seg σ) = (KindP.ofSeg σ).d.seq.s2 by rw [(dims_seg4 σ).2.1]; rfl,
    clR2_c0_eq (c0' := fun _ _ => P4a.c0S (fsOf tr (itemsOf seq4))) rfl, ← e]
  refine congrArg (· * fv (Rs 2) (zh.getD 2 0)) ?_
  obtain ⟨hks, hτ, hθ⟩ := s1_view4 hF.sk hfi hE
  obtain ⟨hL, hz⟩ := lastRegs_view4 hF.sk hfi hE
  have hle18 : σ.m - 14 ≤ 18 := by cases σ <;> decide
  obtain ⟨hrb, hrp⟩ := s2r_view4 hF.sk hfi hE hle18
  have h32 : 32 - σ.m = 18 - (σ.m - 14) := by cases σ <;> rfl
  rw [hks, hτ _ hle18, hθ, hz, hL, hrb, hrp, h32]
  simp only [P4a.wSumSeg, P4a.tauLL, P4a.pad18, P4a.tauL, P4a.rbL, P4a.rpL, P4a.nbC, CKind.m]

/-- **A node's S2 binding** (`relSh4` (ii) with the node ops at `specN4`): S2's last claim is
`wNS4 · v` (`wSumNode4`, S-CN4's `wNS4_node4`). -/
theorem sh_bind_node4 {ν : NodeKind} {cells : List ℕ}
    (hST : ∀ k a b c, c.size = 22 → impl.shiftTarget k a b c = FR.Impl.shiftTargetS k a b c)
    (hSM : ∀ a b, impl.shiftMask a b = NT4.shiftMask4S ν a b)
    (hSW : ∀ κ s a b, impl.slotW κ s a b = Impl.slotWS s a b)
    (hLW : ∀ tt rr, impl.linkWAll (KindP.ofNode ν).tix tt rr = NT4.linkWAll4S ν tt rr)
    (hF : Fields4 impl (.ofNode ν) inp tr (nodeFinP ν cells) y zh Rs Ex) :
    P4a.oSh4 P4a.wNS4 (kindOfC (fsOf tr (itemsOf seq4))) (fsOf tr (itemsOf seq4)) (fv (Rs 2) (zh.getD 2 0)) := by
  have hrel := relSh4_of_fields hF
  have hm : (nodeFinP ν cells).kv.m (KindP.ofNode ν).tix = ν.m := rfl
  have hnode : (nodeFinP ν cells).kv.node (KindP.ofNode ν).tix = true := rfl
  have hvn : (nodeFinP ν cells).vn = false := rfl
  have hS4 : (nodeFinP ν cells).S = seq4 := rfl
  have hmS : seq4.mStar = 32 := by rw [seq4_eq]
  simp only [relSh4, hm, hnode, hvn, hS4, hmS, Bool.and_eq_true, Bool.false_eq_true, ite_false,
    if_true, Nat.reduceSub, Nat.reduceAdd, Bool.or_true, hSM, hSW, hLW] at hrel
  have h2 := val_eqv_f4 hrel.2
  set fi : FinIn := ⟨(skeleton4 seq4 (.ofNode ν)).2.outs, zh, Ex 2⟩
  have hfi : fi.outs = (skeleton4 seq4 (.ofNode ν)).2.outs := rfl
  have hE := hF.ext 2 (by decide)
  have hle : (KindP.ofNode ν).d.seq.s2 ≤ seq4.s2 := by cases ν <;> decide
  obtain ⟨-, hN⟩ := s2_from_head4 hF.sk hfi hE hle (sh_head_node4 hST hF) []
  have e := Val.f.inj (h2.symm.trans hN)
  have hk := kindOfC_node4 hF.sk
  simp only [P4a.oSh4, P4a.claimSL4, P4a.wSumL4, hk, CKind.isNode, ite_true]
  rw [show P4a.nrS (.node ν) = (KindP.ofNode ν).d.seq.s2 by rw [(dims_node4 ν).2.1]; rfl,
    clR2_c0_eq (c0' := fun _ _ => P4a.c0S (fsOf tr (itemsOf seq4))) rfl, ← e, CN4.wNS4_node4]
  refine congrArg (· * fv (Rs 2) (zh.getD 2 0)) ?_
  obtain ⟨hks, hτ, hθ⟩ := s1_view4 hF.sk hfi hE
  have hle18 : ν.m - 14 ≤ 18 := by cases ν <;> decide
  obtain ⟨hrb, hrp⟩ := s2r_view4 hF.sk hfi hE hle18
  have h32 : 32 - ν.m = 18 - (ν.m - 14) := by cases ν <;> rfl
  simp only [List.map_append]
  rw [hks, hτ _ hle18, hθ, hrb, hrp, h32]
  simp only [CN4.wSumNode4, P4a.pad18, P4a.tauL, P4a.rbL, P4a.rpL, P4a.nbC, CKind.m]

end Bind

/-- **The segment ops' facts from `implSegC_meets`'s form** (`specSeg` over `specC`). -/
theorem segOps_of_meets {fin : Finals} {lRows : List Circ.Row} {κs₀ : F}
    (hm : impl.Meets (specSeg (Impl.specC fin lRows κs₀))) (σ : SegKind) :
    (∀ k a b c, c.size = 22 → impl.shiftTarget k a b c = FR.Impl.shiftTargetS k a b c) ∧
      (∀ a b, impl.shiftMask a b = shiftSegS a b) ∧ (∀ κ s a b, impl.slotW κ s a b = Impl.slotWS s a b) ∧
      ∀ tt rr, impl.linkWAll (KindP.ofSeg σ).tix tt rr = Array.replicate nLinkFam 0 :=
  ⟨hm.2.2.2.2.2.2.2.2.2.2.1, hm.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1, hm.2.2.2.2.2.2.2.2.2.2.2.1,
    linkWAll_seg_of_meets hm σ⟩

/-- **The node ops' facts from `implN4_meets`'s form** (`specN4` over a base whose `shiftTarget`
is `shiftTargetS`). -/
theorem nodeOps_of_meets {spec : NodeKind → OpSpec} {ν : NodeKind} (hm : impl.Meets (NI4.specN4 spec ν))
    (hs : (spec ν).shiftTarget = FR.Impl.shiftTargetS) :
    (∀ k a b c, c.size = 22 → impl.shiftTarget k a b c = FR.Impl.shiftTargetS k a b c) ∧
      (∀ a b, impl.shiftMask a b = NT4.shiftMask4S ν a b) ∧
      (∀ κ s a b, impl.slotW κ s a b = Impl.slotWS s a b) ∧
      ∀ tt rr, impl.linkWAll (KindP.ofNode ν).tix tt rr = NT4.linkWAll4S ν tt rr :=
  ⟨shiftTarget_of_meets hm hs, hm.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1, hm.2.2.2.2.2.2.2.2.2.2.2.1,
    fun tt rr => (hm.2.2.2.2.2.2.2.2.2.2.2.2.2.1 _ tt rr).trans (by simp only [NI4.specN4, show (KindP.ofNode ν).tix.isNode = true from rfl, if_true])⟩

end FR.Snd.R4
