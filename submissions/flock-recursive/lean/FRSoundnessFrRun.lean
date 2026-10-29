-- New for `flock-recursive` (BLUEPRINT §5.1, A.9 `finRS`/`finB′`, A.10 B′ → P1.0; stage S-G10).
-- RET-2: the declarations revision 4.1 reads moved to `FRSoundnessCoreAcc`.
import FRSoundnessFrK
import FRSoundnessCoreAcc

/-!
# The front's run facts, step 1: the fields' register chain and the readers on the log

* **`accept_chain`** (`accept_fields` with the register files kept): on an accepted run, `finRS`
  runs from the skeleton's registers `R₀` exactly (to `L₀`), and the rest's field `k` runs from
  `Rs k`, with `Rs 0 = R₀ ++ L₀` and `Rs (k + 1) = Rs k ++ L_k`. So a field reads `finRS`'s
  exports and the exports of the fields before it at the values those fields computed
  (`ExtA (Rs j) (Rs k)`, `j ≤ k`).
* **`one_view`**: a one-challenge squeeze phase (L1, L3β, Lr3, E3, B′) leaves one register, the
  challenge `fAt es (phStart n) 0`.
* **The log's public values are the input's** (`fsQ_gen`'s chain): `vkL_fsQ` (the seed's `vk`),
  `stL_fsQ` (the statement's digests), `msgAt_abs` (an absorb's message is π's bytes there),
  `sliceL_fsQ` (RS0's slices are `sv`).
-/

namespace FR.Snd
open RecursionFast Finset FR.Impl

/-! ## The fields' register chain -/

section Chain
variable (impl : OpImpl) (κ : Kind) (inp : Input)

/-- **An accepted run, with its register files** (`accept_fields` keeping the files): the
skeleton's registers `R₀ = #[] ++ y.1`; `finRS` runs from `R₀` itself to `L₀`; the rest's field
`k` runs from `Rs k`, `Rs 0 = R₀ ++ L₀`, `Rs (k + 1) = Rs k ++ L_k`, with `zhat` = `finRS`'s
exports and `ex` = `exAt …` (the verifier's own fold). -/
theorem accept_chain (fin : Finals) {tr : Trace}
    (hna : ∀ f ∈ fin.finRS :: fin.rest, ∀ fi b, (f fi b).1.filterMap Op.item? = [])
    (h : semIR impl (gen fin (.fixed κ)) inp tr = some true) :
    ∃ y, refPhases impl κ inp phases 0 ctx₀ #[] tr = some y ∧ (∀ b ∈ y.2.1, b = true) ∧
      skeleton.2.next = (#[] ++ y.1.toArray).size ∧
      ∃ L₀, pureRun impl κ inp (fin.finRS ⟨skeleton.2.outs, [], #[]⟩ skeleton.2.next).1
          (#[] ++ y.1.toArray) [] = some (L₀, true) ∧
        ∃ Rs : ℕ → Array Val, Rs 0 = (#[] ++ y.1.toArray) ++ L₀.toArray ∧
          ∀ k (hk : k < fin.rest.length), ∃ L, pureRun impl κ inp ((fin.rest[k]'hk)
            ⟨skeleton.2.outs, (fin.finRS ⟨skeleton.2.outs, [], #[]⟩ skeleton.2.next).2,
              exAt skeleton.2.outs (fin.finRS ⟨skeleton.2.outs, [], #[]⟩ skeleton.2.next).2
                fin.rest
                (skeleton.2.next + opsOut (fin.finRS ⟨skeleton.2.outs, [], #[]⟩ skeleton.2.next).1)
                #[(fin.finRS ⟨skeleton.2.outs, [], #[]⟩ skeleton.2.next).2] k⟩ (Rs k).size).1
            (Rs k) [] = some (L, true) ∧ Rs (k + 1) = Rs k ++ L.toArray := by
  unfold semIR at h
  split at h
  · next s hs =>
    simp only [Option.some.injEq] at h
    rw [show (gen fin (.fixed κ)).ops =
        skeleton.1 ++ (fin.ops skeleton.2.outs skeleton.2.next ++ [.accept]) by
      simp [gen, genWith], show (gen fin (.fixed κ)).kindOn inp = κ from rfl, St.init,
      exec_skeleton] at hs
    obtain ⟨y, hy, hs'⟩ := Option.bind_eq_some_iff.1 hs
    have hn := genPhases_next impl κ inp phases 0 ctx₀ #[] tr y hy rfl
      (.inr ⟨_, _, rfl, rfl, by simp [CtxOk, ctx₀]⟩)
    have hsk : genPhases phases 0 ctx₀ = skeleton := by rw [skeleton]; rfl
    rw [hsk] at hn
    rw [hn, finals_ops_eq] at hs'
    simp only [List.append_assoc] at hs'
    obtain ⟨hok, -⟩ := fields_ok impl κ inp skeleton.2.outs [] [fin.finRS] _ #[] _ _ _ s []
      (fun f hf => hna f (by simp_all)) hs' h
    obtain ⟨L, hL, -, h2⟩ := field_flag impl κ inp
      (hna _ (List.mem_cons_self ..) _ _) (by simpa only [runFields, List.append_nil] using hs') h
    have hsz : ((#[] ++ y.1.toArray) ++ L.toArray).size = (#[] ++ y.1.toArray).size +
        opsOut (fin.finRS ⟨skeleton.2.outs, [], #[]⟩ (#[] ++ y.1.toArray).size).1 := by
      have hl := pureRun_len impl κ inp _ _ [] L true hL
      simp [hl]
    rw [← hsz] at h2
    obtain ⟨Rs, h0, hrest⟩ := fields_chain impl κ inp skeleton.2.outs _ fin.rest _ _ true _ _ s []
      (fun f hf => hna f (List.mem_cons_of_mem _ hf)) h2 h
    refine ⟨y, hy, by simpa using hok, hn, L, by rw [hn]; exact hL, Rs, h0, fun k hk => ?_⟩
    obtain ⟨Lk, hp, he⟩ := hrest k hk
    rw [hsz] at hp
    rw [hn]
    exact ⟨Lk, hp, he⟩
  · cases h

end Chain

/-! ## One-challenge squeezes -/

section Views
variable {impl : OpImpl} {κ : Kind} {inp : Input}

theorem genPhase_one {n : ℕ} {p : Phase} (c : GCtx) {k : ℕ} {act : Kind → Bool}
    (hsh : p.shape = .squeezes k (.one act)) :
    (genPhase n p c).2.outs.back?.getD [] = [c.next + k] := by
  obtain ⟨name, sh⟩ := p
  simp only at hsh; subst hsh
  simp [genPhase]

/-- **A one-challenge squeeze on the skeleton's registers** (L1, L3β, Lr3, E3, B′): its one out
register holds `fAt es (phStart n) 0`. -/
theorem one_view {tr : Trace} {y : List Val × List Bool × Trace} (h : SkRun impl κ inp tr y)
    {n : ℕ} (hn : n < phases.length) {act : Kind → Bool}
    (hsh : phases[n].shape = .squeezes 1 (.one act)) :
    ∃ b, skeleton.2.outs.getD n [] = [b] ∧ b < (#[] ++ y.1.toArray).size ∧
      rd (#[] ++ y.1.toArray) b = .f (fAt (fsOf tr items) (phStart n) 0) := by
  obtain ⟨trk, M, x, hx, hb, -, hext, -, hdrop, -⟩ := phase_at impl κ inp h.ref hn
  simp only [refPhase, hsh] at hx
  obtain ⟨xs, hxs, rfl⟩ := Option.map_eq_some_iff.1 hx
  obtain ⟨hl, hans⟩ := sqz_entries hn hsh (by norm_num) hxs hdrop
  have hsz := size_le_of_ext hext
  simp only [List.length_append, List.length_map, hl, List.length_singleton] at hsz
  refine ⟨M.length + 1, ?_, ?_, ?_⟩
  · rw [skeleton_outs hn, genPhase_one (cAt n) hsh, hb]
  · exact (by omega : M.length + 1 < (#[] ++ y.1.toArray).size)
  · rw [rd_phase hext (by simp [hl]), List.getD_append_right _ _ _ _ (by simp [hl]),
      List.length_map, hl, Nat.sub_self, List.getD_cons_zero, fAt]
    obtain ⟨a, ha⟩ : ∃ a, xs.1 = [a] := List.length_eq_one_iff.1 hl
    have h0 := hans 0 (by norm_num)
    rw [ha, Nat.add_zero, List.getD_cons_zero] at h0
    rw [ha, List.headD_cons, h0]

end Views

/-! ## The log's public values are the input's -/

section Pub

theorem bytesAt_extract_n (π : ByteArray) {o len off n : ℕ} (h : off + n ≤ len) :
    bytesAt (π.extract o (o + len)) off n = bytesAt π (o + off) n := by
  ext k hk
  rw [getElem_bytesAt _ _ _ _ hk, getElem_bytesAt _ _ _ _ hk, toList_extract,
    Nat.add_sub_cancel_left, List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD,
    List.getElem?_take_of_lt (by omega), List.getElem?_drop, Nat.add_assoc]

theorem phaseOff_stmt : phaseOff 1 fStmt = 0 := by decide

theorem phaseOff_rs0 : phaseOff 23 fRS0 = 0 := by decide

variable {vk c : Digest} {π : Proof} {es : Log}
  (hq : ∀ p < 468, (es.getD p default).1 = X.fsQ vk c π p (es.getD (p - 1) default).2)
include hq

/-- **An absorb phase's message on the log is π's bytes there.** -/
theorem msgAt_abs {n f len : ℕ} (hn : n < phases.length) (hsh : phases[n].shape = .absorb f len)
    (hn0 : 0 < n) :
    msgAt es (phStart n) =
      π.extract (fieldOff f + phaseOff n f) (fieldOff f + phaseOff n f + len) := by
  have hm : X.fsMsgs.getD (phStart n) none = some (fieldOff f + phaseOff n f, len) := by
    rw [← Nat.add_zero (phStart n), fsMsgs_phase hn (by rw [hsh]; simp [X.phaseMsgs]), hsh]
    simp [X.phaseMsgs]
  exact msgAt_fsQ hq (lt_468_of_some hm) (phStart_pos hn0 hn) hm

/-- **The seed's `vk` on the log is the input's.** -/
theorem vkL_fsQ : vkL es = vk := by
  have h0 := hq 0 (by norm_num)
  unfold X.fsQ at h0
  rw [X.fsMsgs_ctl.1] at h0
  simp only [ite_true] at h0
  unfold vkL entAt
  rw [h0]
  refine Vector.ext fun k hk => ?_
  rw [getElem_bytesAt _ _ _ _ hk, X.seedQ_data', List.getD_append_right _ _ _ _ (by simp [tagSeed]),
    show 7 + k - tagSeed.length = k by simp [tagSeed],
    List.getD_append _ _ _ _ (by simpa using hk), List.getD_eq_getElem _ _ (by simpa using hk),
    Vector.getElem_toList]

/-- **The statement's digests on the log are π's** (bytes `1 + 32σ` of the statement field). -/
theorem stL_fsQ {σ : ℕ} (hσ : σ ≤ 1) : stL es σ = bytesAt π (absOff fStmt (1 + 32 * σ)) 32 := by
  have hn : 1 < phases.length := by rw [phases_length]; omega
  have hsh : phases[1].shape = .absorb fStmt 128 := rfl
  have h1 : phStart 1 = 1 := by simp only [phStart, fsStarts_eq]; decide
  have hm := msgAt_abs hq hn hsh (by norm_num)
  rw [h1, phaseOff_stmt, Nat.add_zero] at hm
  rw [stL, hm, bytesAt_extract_n π (by omega), absOff_eq (by decide)]

/-- **RS0's slices on the log are π's** (`sv`). -/
theorem sliceL_fsQ {j i : ℕ} (hj : j < 4) (hi : i < 128) :
    sliceL es j i = sv ⟨vk, c, π⟩ j i := by
  have hn : 23 < phases.length := by rw [phases_length]; omega
  have hsh : phases[23].shape = .absorb fRS0 (4 * 128 * 16) := rfl
  have hm := msgAt_abs hq hn hsh (by norm_num)
  rw [frW0_starts.2.2.2.2.2.1, phaseOff_rs0, Nat.add_zero] at hm
  rw [sliceL, readF, hm, bytesAt_extract_n π (by simp only [rsOff]; omega), sv,
    absOff_eq (by decide)]

end Pub

/-! ## The phase numbers of the names the finals read -/

/-! ## Register views by name -/

section ViewsR
variable {impl : OpImpl} {κ : Kind} {inp : Input} {tr : Trace} {y : List Val × List Bool × Trace}

theorem getD_lt_of {l : List ℕ} {n : ℕ} (h : ∀ x ∈ l, x < n) (hn : 0 < n) (p : ℕ) :
    l.getD p 0 < n := by
  rw [List.getD_eq_getElem?_getD]
  rcases hp : l[p]? with _ | x
  · exact hn
  · exact h x (List.mem_of_getElem? hp)

/-- The skeleton's register file is not empty (the seed's registers). -/
theorem skel_pos (h : SkRun impl κ inp tr y) : 0 < (#[] ++ y.1.toArray).size := by
  obtain ⟨b, -, hb, -⟩ := one_view h (n := 25) (by rw [phases_length]; omega) rfl
  exact Nat.lt_of_le_of_lt (Nat.zero_le _) hb

/-- Every register of a phase's outs (by name) is a skeleton register. -/
theorem outsR_lt (h : SkRun impl κ inp tr y) {fi : FinIn} (hfi : fi.outs = skeleton.2.outs)
    (name : String) : ∀ x ∈ outsOf fi name, x < (#[] ++ y.1.toArray).size := by
  intro x hx; rw [outsOf, hfi] at hx; exact skeleton_out_lt h.ref _ x hx

/-- **A coordinates phase by name**: coordinate `p` (`p < 2k`) of `coordsR fi name` is a skeleton
register holding `fAt es (phStart n + p/2) (p % 2)`, on any file extending the skeleton's. -/
theorem coordsR_view (h : SkRun impl κ inp tr y) {n k : ℕ} {nf : Kind → ℕ}
    (hn : n < phases.length) (hsh : phases[n].shape = .squeezes k (.coords nf)) (hk : 0 < k)
    {fi : FinIn} (hfi : fi.outs = skeleton.2.outs) {name : String} (hix : phaseIx name = n)
    {R : Array Val} (hR : ExtA (#[] ++ y.1.toArray) R) {p : ℕ} (hp : p < 2 * k) :
    (coordsR fi name).getD p 0 < (#[] ++ y.1.toArray).size ∧
      rd R ((coordsR fi name).getD p 0) = .f (fAt (fsOf tr items) (phStart n + p / 2) (p % 2)) := by
  obtain ⟨b, hout, hsz, hv⟩ := coords_view h hn hsh hk
  have hc : (coordsR fi name).getD p 0 = b + 3 * (p / 2) + 1 + p % 2 := by
    rw [coordsR, outsOf, hfi, hix, hout, List.drop_one, List.tail_cons,
      List.getD_eq_getElem _ _ (by simpa using hp), List.getElem_map, List.getElem_range]
  have hlt : b + 3 * (p / 2) + 1 + p % 2 < (#[] ++ y.1.toArray).size := by omega
  rw [hc]
  exact ⟨hlt, by rw [hR.rd hlt, hv p hp]; rfl⟩

/-- **A one-challenge squeeze by name**: its out register holds `fAt es (phStart n) 0`. -/
theorem oneR_view (h : SkRun impl κ inp tr y) {n : ℕ} {act : Kind → Bool}
    (hn : n < phases.length) (hsh : phases[n].shape = .squeezes 1 (.one act))
    {fi : FinIn} (hfi : fi.outs = skeleton.2.outs) {name : String} (hix : phaseIx name = n)
    {R : Array Val} (hR : ExtA (#[] ++ y.1.toArray) R) :
    (outsOf fi name).headD 0 < (#[] ++ y.1.toArray).size ∧
      rd R ((outsOf fi name).headD 0) = .f (fAt (fsOf tr items) (phStart n) 0) := by
  obtain ⟨b, hout, hlt, hv⟩ := one_view h hn hsh
  rw [outsOf, hfi, hix, hout, List.headD_cons]
  exact ⟨hlt, by rw [hR.rd hlt, hv]⟩

end ViewsR

/-! ## `finRS`'s exports are its registers -/

/-- `finRS` appends `7 + 4·(1 + 128·8) + 10` registers. -/
theorem opsOut_finRS (fi : FinIn) (b : ℕ) : opsOut (finRS fi b).1 = 4117 := by
  simp only [finRS, opsOut_append]
  rw [opsOut_claimOps, opsOut_claimOps, opsOut_claimOps, opsOut_claimOps]
  · simp [opsOut, rsTail, Op.outs, elemW]
  all_goals intro; rfl

/-- **`finRS`'s exports are among its registers.** -/
theorem finRS_ex_lt (fi : FinIn) (b : ℕ) :
    ∀ x ∈ (finRS fi b).2, x < b + opsOut (finRS fi b).1 := by
  rw [opsOut_finRS]
  simp only [Reg]
  intro x hx
  simp only [finRS, elemW, List.mem_append, List.mem_map, List.mem_range, List.mem_cons,
    List.not_mem_nil, or_false, Nat.reduceMul, Nat.reduceAdd] at hx
  rcases hx with ⟨j, hj, rfl⟩ | rfl
  · have : j * 1025 ≤ 3 * 1025 := Nat.mul_le_mul_right _ (by omega)
    omega
  · omega

/-! ## `hStart`: P1.0's claim register holds `c₀L` -/

section Start
variable {impl : OpImpl} {κ : Kind} {inp : Input} {tr : Trace} {y : List Val × List Bool × Trace}

theorem rest_get {k : ℕ} {f : FinField} (h : (sfFinals finP finPf).rest[k]? = some f)
    (hk : k < (sfFinals finP finPf).rest.length) : (sfFinals finP finPf).rest[k]'hk = f := by
  rw [List.getElem?_eq_getElem hk] at h; exact Option.some.inj h

/-- RS1's coordinates on the skeleton's registers are `coordAt es 312` (`rsCoL`). -/
theorem rs1_val (h : SkRun impl κ inp tr y) {fi : FinIn} (hfi : fi.outs = skeleton.2.outs)
    {R : Array Val} (hR : ExtA (#[] ++ y.1.toArray) R) {p : ℕ} (hp : p < 8) :
    (coordsR fi "RS1").getD p 0 < (#[] ++ y.1.toArray).size ∧
      fv R ((coordsR fi "RS1").getD p 0) = rsCoL (fsOf tr items) p := by
  obtain ⟨h1, h2⟩ := coordsR_view h (n := 24) (by rw [phases_length]; omega) rfl (by norm_num)
    hfi phaseIx_vals.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 hR (k := 4) hp
  refine ⟨h1, ?_⟩
  rw [fv, h2, frW0_starts.2.2.2.2.2.2.1]
  rfl

/-- **`v_RS` on the skeleton's registers is `vRSL`** (`rsV` with `phiRS` at its spec). -/
theorem rsV_eq (h : SkRun impl κ inp tr y) (hphi : ∀ r a, r.size = 7 → impl.phiRS r a = phiRSS r a)
    {vk c : Digest} {π : Proof} (hinp : inp = ⟨vk, c, π⟩) {fi : FinIn}
    (hfi : fi.outs = skeleton.2.outs) :
    rsV impl κ inp fi (#[] ++ y.1.toArray) = vRSL κ (fsOf tr items) := by
  subst hinp
  have hE : ExtA (#[] ++ y.1.toArray) (#[] ++ y.1.toArray) := ⟨le_rfl, fun _ _ => rfl⟩
  have hpt : ptF (#[] ++ y.1.toArray) (rsFsRegs fi) = (rsRL (fsOf tr items)).toArray := by
    simp only [ptF, rsFsRegs, rsRL, List.map_map]
    exact congrArg List.toArray (List.map_congr_left fun p hp =>
      (rs1_val h hfi hE (by simp at hp; omega)).2)
  have hT : ∀ j < 4, rsTv impl ⟨vk, c, π⟩ fi (#[] ++ y.1.toArray) j = rsTvL (fsOf tr items) j := by
    intro j hj
    simp only [rsTv, rsTvL]
    refine sum_congr rfl fun i hi => ?_
    rw [hpt, hphi _ _ (by simp [rsRL]), phiRSS, List.toList_toArray,
      sliceL_fsQ h.hq hj (mem_range.1 hi)]
  unfold rsV vRSL rsKL
  rw [hT 0 (by norm_num), hT 1 (by norm_num), hT 2 (by norm_num), hT 3 (by norm_num),
    (rs1_val h hfi hE (show 7 < 8 by norm_num)).2]

/-- **`hStart`** (S-G5 §5 item 9): on an accepted run of `gen (sfFinals finP finPf)` with
`phiRS` at its spec, P1.0's claim register holds `c₀L L es = ι v*`. From `finB′`'s relation
`relB` (`v* = P1.0's claim`), `finRS`'s `v_RS` export (`exec_finRS`, `rsV_eq`), B′'s `κ′`
(`oneR_view`) and the public values on the log (`vkL_fsQ`, `stL_fsQ`). -/
theorem start_run (hphi : ∀ r a, r.size = 7 → impl.phiRS r a = phiRSS r a) (vk : Digest) :
    ∀ (k : Kind) (c : Digest) (π : Proof) (L tr : Log) (y : List Val × List Bool × Trace),
      FR.kindOf π = .snark k →
      semIR impl (gen (sfFinals finP finPf) (.fixed k)) ⟨vk, c, π⟩ tr = some true →
      refPhases impl k ⟨vk, c, π⟩ phases 0 ctx₀ #[] tr = some y →
      rd (#[] ++ y.1.toArray) (claim0 ⟨skeleton.2.outs, [], #[]⟩ "P1") =
        .k (c₀L L (fsOf tr items)) := by
  intro k c π L tr y hk hsem hy
  obtain ⟨y', hy', hfl, hn, L₀, hRS, Rs, h0, hrest⟩ :=
    accept_chain impl k ⟨vk, c, π⟩ _ noAsk_sf hsem
  obtain rfl : y' = y := Option.some.inj (hy'.symm.trans hy)
  obtain ⟨hl, hq⟩ := fsQ_gen ⟨vk, c, π⟩ impl _ _ hsem
  have hS : SkRun impl k ⟨vk, c, π⟩ tr y' := ⟨hy', hfl, hl, hq⟩
  have hkind : kindOf (fsOf tr items) = k := kindOf_fsQ hq hk
  set R0 := #[] ++ y'.1.toArray with hR0
  set fi₀ : FinIn := ⟨skeleton.2.outs, [], #[]⟩
  have hpos := skel_pos hS
  -- `finRS`: its `v_RS` export
  obtain ⟨L₁, hL₁, -, hvRS⟩ := exec_finRS impl k ⟨vk, c, π⟩ fi₀ R0 (by
    intro x hx
    simp only [rsRefs, List.mem_append, List.mem_map, List.mem_range, List.mem_cons,
      List.not_mem_nil, or_false] at hx
    have ho := outsR_lt hS (fi := fi₀) rfl
    rcases hx with (((⟨p, -, rfl⟩ | rfl) | hx) | hx)
    · exact getD_lt_of (fun x hx => ho "RS1" x (List.mem_of_mem_drop hx)) hpos p
    · exact headD_lt (ho "Z2") hpos
    · have hx' := List.mem_of_mem_take hx
      unfold chals at hx'
      exact ho "L2" x (List.mem_of_mem_drop (List.mem_of_mem_take hx'))
    · have hx' := List.mem_of_mem_drop (List.mem_of_mem_take hx)
      unfold chals at hx'
      exact ho "S2" x (List.mem_of_mem_drop (List.mem_of_mem_take hx')))
  rw [hn] at hRS
  have hRS' : pureRun impl k ⟨vk, c, π⟩ (finRS fi₀ R0.size).1 R0 [] = some (L₀, true) := hRS
  have hLL : L₁ = L₀ := by rw [hRS'] at hL₁; exact (Prod.mk.inj (Option.some.inj hL₁)).1.symm
  rw [hLL] at hvRS
  -- the chain's files
  have hext : ∀ j < (sfFinals finP finPf).rest.length, ExtA (Rs j) (Rs (j + 1)) := fun j hj => by
    obtain ⟨L, -, he⟩ := hrest j hj; rw [he]; exact ExtA.app _ _
  have h5 : 5 < (sfFinals finP finPf).rest.length := by rw [rest_eq]; simp
  have hE05 : ExtA (Rs 0) (Rs 5) := chain_ext hext (by norm_num) h5.le
  have hE5 : ExtA R0 (Rs 5) := by rw [h0] at hE05; exact (ExtA.app R0 L₀).trans hE05
  rw [h0] at hE05
  obtain ⟨L5, hp5, -⟩ := hrest 5 h5
  rw [rest_get (by rw [rest_eq]; rfl : (sfFinals finP finPf).rest[5]? = some finB')] at hp5
  have hl₀ := pureRun_len impl k ⟨vk, c, π⟩ R0 _ [] L₀ true hRS'
  suffices H : ∀ fi : FinIn, fi.outs = skeleton.2.outs → fi.zhat = (finRS fi₀ R0.size).2 →
      pureRun impl k ⟨vk, c, π⟩ (finB' fi (Rs 5).size).1 (Rs 5) [] = some (L5, true) →
      rd R0 (claim0 ⟨skeleton.2.outs, [], #[]⟩ "P1") = .k (c₀L L (fsOf tr items)) from
    H _ rfl (by rw [← hn]; rfl) hp5
  intro fi hfi hzh hp
  have hzlt : fi.zhat.getD nRS 0 < (R0 ++ L₀.toArray).size := by
    have hsz : (R0 ++ L₀.toArray).size = R0.size + opsOut (finRS fi₀ R0.size).1 := by
      simp [hl₀]
    rw [hzh, hsz]
    exact getD_lt_of (finRS_ex_lt fi₀ R0.size) (Nat.lt_of_lt_of_le hpos (Nat.le_add_right _ _)) nRS
  obtain ⟨hk1, hk2⟩ := oneR_view hS (n := 25) (by rw [phases_length]; omega) rfl hfi
    phaseIx_vals.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2 hE5
  have hc0 : claim0 fi "P1" < R0.size := headD_lt (outsR_lt hS hfi "P1") hpos
  obtain ⟨L', hL', -⟩ := flag_finB' impl k ⟨vk, c, π⟩ fi (Rs 5) (by
    intro x hx
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl | rfl
    · exact lt_of_lt_of_le hk1 hE5.1
    · exact lt_of_lt_of_le hzlt hE05.1
    · exact lt_of_lt_of_le hc0 hE5.1)
  have hrel : relB k ⟨vk, c, π⟩ fi (Rs 5) = true := pureRun_det hp hL'
  unfold relB at hrel
  have h1 := val_eqv_k hrel
  rw [hE5.rd hc0] at h1
  rw [show claim0 ⟨skeleton.2.outs, [], #[]⟩ "P1" = claim0 fi "P1" by
    simp only [claim0, outsOf, hfi], h1, K.smulF_one, c₀L, hkind]
  suffices hv : vStar k ⟨vk, c, π⟩ fi (Rs 5) = vStarL k (fsOf tr items) by rw [hv]
  have hz : fv (Rs 5) (fi.zhat.getD nRS 0) = vRSL k (fsOf tr items) := by
    rw [fv, hE05.rd hzlt, hzh, hvRS, rsV_eq hS hphi rfl rfl]
  have hkp : fv (Rs 5) ((outsOf fi "B'").headD 0) = kpL (fsOf tr items) := by
    rw [fv, hk2, frW0_starts.2.2.2.2.2.2.2.1]; rfl
  have hs0 : stL (fsOf tr items) 0 = bytesAt π (absOff fStmt 1) 32 := stL_fsQ hq (by norm_num)
  have hs1 : stL (fsOf tr items) 1 = bytesAt π (absOff fStmt 33) 32 := stL_fsQ hq (by norm_num)
  unfold vStar vStarL pubH pubHL
  rw [hz, hkp, hs0, hs1, vkL_fsQ hq]

end Start

end FR.Snd
