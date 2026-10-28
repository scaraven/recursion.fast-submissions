-- New for `flock-recursive` (BLUEPRINT §5.4, A.9, A.10; stage S-G4, `hFin` assembled).
import FRSoundnessAccW
import FRSoundnessAcc
import FRNodeCircuit

/-!
# `hFin` discharged: an accepted run's finals are `FinLog`

For the verifier `gen (sfFinals finP finPf) (.fixed κ)` with `tensorW` at its spec
(`Impl.tensorWS`, which `implC_meets` gives for `implC`):

* **`finLog_of_run`**: on an accepted SNARK run whose trace lies in a log without bad events,
  `FinLog W₀ c₀ L (fsOf tr items) y` holds with `y i q` the fold registers' values, given the
  front's two register facts: `claim0 "P1"` holds `c₀ L es` (`start`, what `finB′` asserts) and
  `w0V` is `wHatL W₀ L es 0` (`Ŵ₀(P₀)`, the front's weight; on any registers extending the
  skeleton's).
* **`hAcc_of_fin`**: `hAcc` for `S.V = Vwith impl (sfFinals finP finPf)` with only `hStart`,
  `hW0` (the front's) and `hFront` (`¬ RejF`) left as hypotheses.

Steps: `accept_fields` (every flag and field up) → the flag lemmas (`flag_finPLow`, `flag_finP4`,
`flag_finPf`) on the fields' registers → the registers' values on the log (`p1_facts`,
`pf_facts`, `kc_facts`, `ys_facts`, `tail_vals`, `wV_eq`, `final_view`) → `FinLog`'s fields.
-/

namespace FR.Snd
open RecursionFast FR.Merkle Finset

/-! ## S-0's fields ask nothing -/

theorem noAsk_finZ (fi : FinIn) (b : ℕ) : (finZ fi b).1.filterMap Op.item? = [] := by
  simp [finZ, pinOps, Op.item?]

theorem noAsk_finLc (fi : FinIn) (b : ℕ) : (finLc fi b).1.filterMap Op.item? = [] := by
  simp only [finLc, List.filterMap_append, dotOps_noAsk, List.append_nil]
  simp [lcHead, lcTail, hornerOps, Op.item?]
  aesop

theorem noAsk_finSh (fi : FinIn) (b : ℕ) : (finSh fi b).1.filterMap Op.item? = [] := by
  simp [finSh, bndOps, linkOps, Op.item?]
  aesop

theorem noAsk_finLr (fi : FinIn) (b : ℕ) : (finLr fi b).1.filterMap Op.item? = [] := by
  simp [finLr, Op.item?]

theorem rest_eq : (sfFinals finP finPf).rest =
    [finZ, finLc, finSh, finLr, finE, finB', finP 0, finP 1, finP 2, finP 3, finP 4, finPf] := by
  simp [Finals.rest, sfFinals, s0Finals, nLevels, List.range_succ]

theorem noAsk_sf : ∀ f ∈ (sfFinals finP finPf).finRS :: (sfFinals finP finPf).rest,
    ∀ fi b, (f fi b).1.filterMap Op.item? = [] := by
  intro f hf fi b
  rw [rest_eq] at hf
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hf
  rcases hf with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  exacts [noAsk_finRS fi b, noAsk_finZ fi b, noAsk_finLc fi b, noAsk_finSh fi b, noAsk_finLr fi b,
    noAsk_finE fi b, noAsk_finB' fi b, noAsk_finP 0 fi b, noAsk_finP 1 fi b, noAsk_finP 2 fi b,
    noAsk_finP 3 fi b, noAsk_finP 4 fi b, noAsk_finPf fi b]

/-! ## The chain's kind -/

/-- **The chain's kind is the proof's**: entry 0 is the seed query, whose header byte 0 is π's
kind byte. -/
theorem kindOf_fsQ {vk c : Digest} {π : Proof} {es : Log} {k : Kind}
    (hq : ∀ p < 468, (es.getD p default).1 = X.fsQ vk c π p (es.getD (p - 1) default).2)
    (hk : FR.kindOf π = .snark k) : kindOf es = k := by
  have h0 := hq 0 (by norm_num)
  unfold X.fsQ at h0
  rw [X.fsMsgs_ctl.1] at h0
  try simp only [ite_true] at h0
  have hb := FR.Node.byte_of_kindOf hk
  have h71 : (es.getD 0 default).1.data[71]? = π.data[0]? := by
    rw [h0, ← Array.getElem?_toList, X.seedQ_data']
    try simp only [List.append_assoc]
    rw [List.getElem?_append_right (by simp [tagSeed]), List.getElem?_append_right (by simp [tagSeed]),
      List.getElem?_append_right (by simp [tagSeed])]
    simp only [tagSeed, List.length_cons, List.length_nil, Vector.length_toList]
    rw [show 71 - 7 - 32 - 32 = 0 from rfl, toList_extract, ← Array.getElem?_toList]
    rcases hπ : π.data.toList with _ | ⟨a, l⟩
    · rfl
    · rfl
  unfold kindOf entAt
  rw [h71, hb]
  simp [Kind.ofByte?_byte]

/-! ## Small list facts -/

theorem headD_lt {l : List ℕ} {n : ℕ} (h : ∀ x ∈ l, x < n) (hn : 0 < n) : l.headD 0 < n := by
  cases l with
  | nil => exact hn
  | cons a l => exact h a (List.mem_cons_self ..)

theorem getLastD_lt {l : List ℕ} {n : ℕ} (h : ∀ x ∈ l, x < n) (hn : 0 < n) : l.getLastD 0 < n := by
  rcases List.eq_nil_or_concat l with rfl | ⟨L, b, rfl⟩
  · exact hn
  · rw [List.concat_eq_append, List.getLastD_concat]; exact h b (by simp)

theorem c1_eq (c₀ : Log → Log → K) {i : ℕ} (hi : i < 5) (L es : Log) :
    c1 c₀ i L es = rVal (p1Start i) es (hEll i - 1) := by
  obtain ⟨e, he⟩ : ∃ e, hEll i = e + 1 := ⟨hEll i - 1, by have := hEll_pos hi; omega⟩
  rw [c1, he, Nat.add_sub_cancel]; rfl

theorem lt_468_of_some {p : ℕ} {x : ℕ × ℕ} (h : X.fsMsgs.getD p none = some x) : p < 468 := by
  by_contra hp
  rw [List.getD_eq_default _ _ (by rw [X.fsMsgs_length]; omega)] at h
  cases h

/-- The final message's offset inside its field (row 47 is field `final`'s first contributor;
`decide` on the 47 rows' byte counts toward field 15). -/
theorem phaseOff_47 : phaseOff 47 fFinal = 0 := by decide

/-- **The final message on the log is π's** (row 47's absorb). -/
theorem finalAt_fsQ {vk c : Digest} {π : Proof} {es : Log}
    (hq : ∀ p < 468, (es.getD p default).1 = X.fsQ vk c π p (es.getD (p - 1) default).2)
    {e : ℕ} (he : e < 128) : finalAt es e = finV ⟨vk, c, π⟩ e := by
  have hn : 47 < phases.length := by rw [phases_length]; omega
  have hsh : phases[47].shape = .absorb fFinal 4096 := by
    have := phase_lvl_shape (i := 4) (k := 1) (by norm_num) (by norm_num)
    rw [this]; rfl
  have hm : X.fsMsgs.getD (phStart 47) none = some (fieldOff fFinal, 4096) := by
    rw [← Nat.add_zero (phStart 47), fsMsgs_phase hn (by rw [hsh]; simp [X.phaseMsgs]),
      hsh]
    simp [X.phaseMsgs, phaseOff_47]
  have hp := lt_468_of_some hm
  have hp0 := phStart_pos (n := 47) (by norm_num) hn
  rw [finalAt, readK_fsQ hq hp hp0 hm (by omega), finV, absOff_eq (by decide)]

/-! ## The flags of `finP i` and `finPf` from `accept_fields` -/

theorem pureRun_det {impl : OpImpl} {κ : Kind} {inp : Input} {o : List Op} {r : Array Val}
    {L L' : List Val} {f : Bool} (h1 : pureRun impl κ inp o r [] = some (L, true))
    (h2 : pureRun impl κ inp o r [] = some (L', f)) : f = true := by
  rw [h1] at h2; cases h2; rfl

variable {impl : OpImpl} {κ : Kind} {inp : Input} {tr : Trace} {y : List Val × List Bool × Trace}

/-- The field at position `k` of `rest` from `accept_fields`' family. -/
theorem rest_at {P : FinField → Prop} (hall : ∀ k (hk : k < (sfFinals finP finPf).rest.length),
    P ((sfFinals finP finPf).rest[k]'hk)) {k : ℕ} {f : FinField}
    (h : (sfFinals finP finPf).rest[k]? = some f) : P f := by
  obtain ⟨hk, rfl⟩ := List.getElem?_eq_some_iff.1 h
  exact hall k hk

/-! ## The registers the fields read are the skeleton's -/

section Refs
variable {fi : FinIn} {N : ℕ}

theorem sub_lt {l l' : List ℕ} (h : ∀ x ∈ l, x < N) (hs : ∀ x ∈ l', x ∈ l) : ∀ x ∈ l', x < N :=
  fun x hx => h x (hs x hx)

theorem getD_lt (hN : 0 < N) {l : List ℕ} (h : ∀ x ∈ l, x < N) (n : ℕ) : l.getD n 0 < N := by
  rw [List.getD_eq_getElem?_getD]
  rcases hl : l[n]? with _ | z
  · exact hN
  · exact h z (List.mem_of_getElem? hl)

variable (hN : 0 < N) (hO : ∀ n, ∀ x ∈ fi.outs.getD n [], x < N)
include hN hO

theorem outsOf_lt (s : String) : ∀ x ∈ outsOf fi s, x < N := hO _
theorem chals_lt (s : String) (k : ℕ) : ∀ x ∈ chals fi s k, x < N :=
  sub_lt (outsOf_lt hN hO s) fun _ hx => List.mem_of_mem_drop (List.mem_of_mem_take hx)
theorem coordsR_lt (s : String) : ∀ x ∈ coordsR fi s, x < N :=
  sub_lt (outsOf_lt hN hO s) fun _ hx => List.mem_of_mem_drop hx
theorem lvOuts_lt (i k : ℕ) : ∀ x ∈ lvOuts fi i k, x < N := hO _
theorem sRegs_lt (i : ℕ) : ∀ x ∈ sRegs fi i, x < N :=
  sub_lt (lvOuts_lt hN hO i 0) fun _ hx => List.mem_of_mem_drop (List.mem_of_mem_take hx)
theorem kcOf_lt (i : ℕ) : ∀ x ∈ kcOf fi i, x < N :=
  sub_lt (lvOuts_lt hN hO i 4) fun _ hx => List.mem_of_mem_drop (List.mem_of_mem_take hx)
theorem ysOf_lt (i : ℕ) : ∀ x ∈ ysOf fi i, x < N := lvOuts_lt hN hO i 3
theorem tailRegs_lt (m k : ℕ) : ∀ x ∈ tailRegs fi m k, x < N := by
  intro x hx
  rw [tailRegs, List.mem_append, List.mem_flatMap] at hx
  rcases hx with ⟨j, -, hx⟩ | hx
  · exact sRegs_lt hN hO j x (List.mem_of_mem_drop hx)
  · exact chals_lt hN hO "Pf" 7 x (List.mem_of_mem_take hx)
theorem p0Regs_lt (m : ℕ) : ∀ x ∈ p0Regs fi m, x < N := by
  intro x hx
  rw [p0Regs, List.mem_append] at hx
  rcases hx with hx | hx
  · exact sRegs_lt hN hO 0 x hx
  · exact tailRegs_lt hN hO m 1 x hx

omit hN hO in
theorem srcs_f {l : List ℕ} (h : ∀ x ∈ l, x < N) : ∀ p ∈ l.map PtSrc.f, ∀ x ∈ p.regs, x < N := by
  intro p hp x hx
  obtain ⟨z, hz, rfl⟩ := List.mem_map.1 hp
  simp only [PtSrc.regs, List.mem_singleton] at hx; subst hx; exact h _ hz

omit hN hO in
theorem srcs_k {l : List ℕ} (h : ∀ x ∈ l, x < N) : ∀ p ∈ l.map PtSrc.k, ∀ x ∈ p.regs, x < N := by
  intro p hp x hx
  obtain ⟨z, hz, rfl⟩ := List.mem_map.1 hp
  simp only [PtSrc.regs, List.mem_singleton] at hx; subst hx; exact h _ hz

omit hN hO in
theorem srcs_c {α : Type} (l : List α) (g : α → K) :
    ∀ p ∈ l.map (fun a => PtSrc.c (g a)), ∀ x ∈ p.regs, x < N := by
  intro p hp x hx
  obtain ⟨z, -, rfl⟩ := List.mem_map.1 hp
  simp [PtSrc.regs] at hx

omit hN hO in
theorem srcs_app {a b : List PtSrc} (ha : ∀ p ∈ a, ∀ x ∈ p.regs, x < N)
    (hb : ∀ p ∈ b, ∀ x ∈ p.regs, x < N) : ∀ p ∈ a ++ b, ∀ x ∈ p.regs, x < N := by
  intro p hp
  rcases List.mem_append.1 hp with h | h
  exacts [ha p h, hb p h]

theorem pfPts_lt : ∀ s ∈ pfPts fi, ∀ p ∈ s, ∀ x ∈ p.regs, x < N := by
  have hz : ∀ m, ∀ p ∈ zSrc fi m, ∀ x ∈ p.regs, x < N := fun m => srcs_app
    (by simpa [List.map_map] using srcs_c (N := N) ((List.ofFn pinnedRho).drop 1) K.ofF)
    (srcs_f (sub_lt (coordsR_lt hN hO "Z1") fun _ hx => List.mem_of_mem_take hx))
  have hlc : ∀ m, ∀ p ∈ lcSrc fi m, ∀ x ∈ p.regs, x < N := fun m => srcs_app
    (srcs_f (sub_lt (chals_lt hN hO "L2" 14) fun _ hx => List.mem_of_mem_drop hx))
    (srcs_f (sub_lt (chals_lt hN hO "Z3" 26) fun _ hx =>
      List.mem_of_mem_take (List.mem_of_mem_drop hx)))
  have hsh : ∀ m, ∀ p ∈ shSrc fi m, ∀ x ∈ p.regs, x < N := fun m => srcs_app (srcs_app
    (srcs_f (sub_lt (chals_lt hN hO "S2" 28) fun _ hx =>
      List.mem_of_mem_drop (List.mem_of_mem_take hx)))
    (by
      intro p hp x hx
      rw [List.eq_of_mem_replicate hp] at hx; simp [PtSrc.regs] at hx))
    (srcs_f (sub_lt (chals_lt hN hO "S2" 28) fun _ hx => List.mem_of_mem_take hx))
  intro s hs
  simp only [pfPts, List.mem_append, List.mem_cons, List.mem_map, List.mem_range,
    List.not_mem_nil, or_false] at hs
  rcases hs with ((((rfl | rfl | rfl | rfl | rfl | rfl | rfl) | ⟨k, -, rfl⟩) | ⟨k, -, rfl⟩) |
    rfl | rfl)
  · exact hz 32
  · exact hz 30
  · exact hlc 32
  · exact hlc 30
  · exact hsh 32
  · exact hsh 30
  · exact srcs_f (chals_lt hN hO "E4" 23)
  · exact srcs_k (tailRegs_lt hN hO 32 (k + 1))
  · exact srcs_k (tailRegs_lt hN hO 30 (k + 1))
  · exact srcs_k (p0Regs_lt hN hO 32)
  · exact srcs_k (p0Regs_lt hN hO 30)

/-- **`finPf` reads only the skeleton's registers.** -/
theorem pfRefs_lt : ∀ x ∈ pfRefs fi, x < N := by
  intro x hx
  simp only [pfRefs, List.mem_append, List.mem_flatMap, List.mem_map, List.mem_range,
    List.mem_cons, List.not_mem_nil, or_false] at hx
  rcases hx with (((⟨s, hs, p, hp, hx⟩ | ⟨q, -, rfl⟩) | (rfl | rfl | rfl | rfl | rfl)) | hx) |
    ⟨k, -, hx⟩
  · exact pfPts_lt hN hO s hs p hp x hx
  · exact getD_lt hN (coordsR_lt hN hO "RS1") q
  · exact headD_lt (outsOf_lt hN hO "B'") hN
  · exact getLastD_lt (outsOf_lt hN hO "Pf") hN
  · exact getD_lt hN (chals_lt hN hO "Pf" 7) 5
  · exact getD_lt hN (chals_lt hN hO "Pf" 7) 6
  · exact headD_lt (outsOf_lt hN hO "L3β") hN
  · exact chals_lt hN hO "Pf" 7 x hx
  · simp only [lvRefs, List.mem_cons, List.mem_append] at hx
    rcases hx with (rfl | hx) | hx
    · exact headD_lt (sRegs_lt hN hO k) hN
    · exact kcOf_lt hN hO _ x hx
    · exact ysOf_lt hN hO _ x hx

end Refs

theorem accVal_kc {g : ℕ → F} (Ys : List K) (A : K) (ht : Ys.length < 2 ^ 9) :
    accVal (eqTab ((List.range 9).map g).toArray) Ys 0 A =
      A + ∑ q ∈ range Ys.length, K.smulF (eqBits g 9 q) (Ys.getD q 0) := by
  rw [accVal_eq, ← List.sum_toFinset _ List.nodup_range, List.toFinset_range]
  refine congrArg (A + ·) (sum_congr rfl fun q hq => ?_)
  have hq' := mem_range.1 hq
  rw [Nat.zero_add, eqTab_getD _ (by simp; omega)]
  simp only [List.size_toArray, List.length_map, List.length_range]
  rw [eqBits_congr (r' := g) (fun v hv => by simp [Array.getD_eq_getD_getElem?, hv])]

/-! ## `FinLog` on an accepted run -/

/-- **The finals read off the log** (`hFin`): an accepted SNARK run of
`gen (sfFinals finP finPf) (.fixed k)`, `tensorW` at its spec, on a trace inside a log without
bad events, satisfies `FinLog` on its Fiat–Shamir entries, the column folds being the fold
registers' values. The front supplies `start` (`claim0 "P1"` holds `c₀`) and `Ŵ₀(P₀)`. -/
theorem finLog_of_run {W₀ : Log → Log → ℕ → K} {c₀ : Log → Log → K}
    (ht : ∀ j r, impl.tensorW j r = Impl.tensorWS j r)
    {vk c : Digest} {π : Proof} {k : Kind} {L tr : Log}
    (hb : ¬ Bad L) (hπ : π.size = piSize) (hk : FR.kindOf π = .snark k)
    (hsem : semIR impl (gen (sfFinals finP finPf) (.fixed k)) ⟨vk, c, π⟩ tr = some true)
    (hin : ∀ e ∈ tr, e ∈ L)
    (hStart : ∀ y, refPhases impl k ⟨vk, c, π⟩ phases 0 ctx₀ #[] tr = some y →
      rd (#[] ++ y.1.toArray) (claim0 ⟨skeleton.2.outs, [], #[]⟩ "P1") = .k (c₀ L (fsOf tr items)))
    (hW0 : ∀ y, refPhases impl k ⟨vk, c, π⟩ phases 0 ctx₀ #[] tr = some y →
      ∀ (fi : FinIn) (r' : Array Val), fi.outs = skeleton.2.outs → ExtA (#[] ++ y.1.toArray) r' →
        w0V impl k fi r' = wHatL W₀ L (fsOf tr items) 0) :
    ∃ yv, FinLog W₀ c₀ L (fsOf tr items) yv := by
  obtain ⟨y, hy, hfl, -, hrest'⟩ :=
    accept_fields impl k ⟨vk, c, π⟩ (sfFinals finP finPf) noAsk_sf hsem
  obtain ⟨zh, hrest⟩ : ∃ zh, ∀ j (hj : j < (sfFinals finP finPf).rest.length), ∃ Rk exk Lk,
      ExtA (#[] ++ y.1.toArray) Rk ∧ pureRun impl k ⟨vk, c, π⟩
        (((sfFinals finP finPf).rest[j]'hj) ⟨skeleton.2.outs, zh, exk⟩ Rk.size).1 Rk [] =
          some (Lk, true) :=
    ⟨_, fun j hj => let ⟨Rk, Lk, hE, hp⟩ := hrest' j hj; ⟨Rk, _, Lk, hE, hp⟩⟩
  obtain ⟨hl, hq⟩ := fsQ_gen ⟨vk, c, π⟩ impl (sfFinals finP finPf) _ hsem
  have h : SkRun impl k ⟨vk, c, π⟩ tr y := ⟨hy, hfl, hl, hq⟩
  have hL : (L.map Prod.fst).Nodup := by
    by_contra hr; exact hb (.inr (.inr (.inr hr)))
  have hkind : kindOf (fsOf tr items) = k := kindOf_fsQ hq hk
  have hO : ∀ n, ∀ x ∈ skeleton.2.outs.getD n [], x < (#[] ++ y.1.toArray).size :=
    skeleton_out_lt h.ref
  have hOf : ∀ fi : FinIn, fi.outs = skeleton.2.outs →
      ∀ n, ∀ x ∈ fi.outs.getD n [], x < (#[] ++ y.1.toArray).size :=
    fun fi hfi n x hx => hO n x (hfi ▸ hx)
  -- the skeleton's registers are not empty (Pf's challenges are among them)
  obtain ⟨hpv, hpl, hp0, hpN, hpo, hpchk⟩ := pf_facts h (fi := ⟨skeleton.2.outs, [], #[]⟩) rfl
  have hN : 0 < (#[] ++ y.1.toArray).size := by
    have hm := List.getElem_mem (l := chals ⟨skeleton.2.outs, [], #[]⟩ "Pf" 7)
      (by rw [hpl]; norm_num : 0 < _)
    unfold chals at hm
    exact lt_of_le_of_lt (Nat.zero_le _) (hpo _ (List.mem_of_mem_drop (List.mem_of_mem_take hm)))
  have hfield : ∀ (j : ℕ) (f : FinField), (sfFinals finP finPf).rest[j]? = some f →
      ∃ Rk exk Lk, ExtA (#[] ++ y.1.toArray) Rk ∧ pureRun impl k ⟨vk, c, π⟩
        (f ⟨skeleton.2.outs, zh, exk⟩ Rk.size).1 Rk [] = some (Lk, true) :=
    fun j f hj => rest_at (P := fun f => ∃ Rk exk Lk, ExtA (#[] ++ y.1.toArray) Rk ∧
      pureRun impl k ⟨vk, c, π⟩ (f ⟨skeleton.2.outs, zh, exk⟩ Rk.size).1 Rk [] = some (Lk, true))
      hrest hj
  -- the column folds
  let yv : ℕ → ℕ → K := fun i q =>
    (rd (#[] ++ y.1.toArray) ((ysOf ⟨skeleton.2.outs, [], #[]⟩ i).getD q 0)).toK
  refine ⟨yv, ?_⟩
  -- facts on a field's registers `Rk`
  have hkcRk : ∀ {Rk : Array Val} (exk : Array (List Reg)), ExtA (#[] ++ y.1.toArray) Rk →
      ∀ i < 5, (kcOf ⟨skeleton.2.outs, zh, exk⟩ i).map (fv Rk) =
        (List.range 9).map (kcAt (fsOf tr items) i) := by
    intro Rk exk hE i hi
    obtain ⟨hkc, hkcl⟩ := kc_facts h (fi := ⟨skeleton.2.outs, zh, exk⟩) rfl hi
    rw [← hkc]; exact List.map_congr_left fun x hx => by rw [fv, hE.rd (hkcl x hx)]
  have hysRk : ∀ {Rk : Array Val} (exk : Array (List Reg)), ExtA (#[] ++ y.1.toArray) Rk →
      ∀ i < 5, (ysOf ⟨skeleton.2.outs, zh, exk⟩ i).map (fun x => (rd Rk x).toK) =
        (List.range (lvl k i).t).map (yv i) := by
    intro Rk exk hE i hi
    obtain ⟨hyl, hylt, -⟩ := ys_facts h hL hin hπ (fi := ⟨skeleton.2.outs, zh, exk⟩) rfl hi
    refine List.ext_getElem (by simp [hyl]) fun q h1 h2 => ?_
    simp only [List.getElem_map, List.getElem_range, yv]
    rw [hE.rd (hylt _ (List.getElem_mem _)), ← List.getD_eq_getElem _ 0]; rfl
  -- `finP 4`: its relation on its registers
  obtain ⟨R4, ex4, L4, hE4, hp4⟩ := hfield 10 (finP 4) rfl
  have hO4 := hOf ⟨skeleton.2.outs, zh, ex4⟩ rfl
  have hN4 : 0 < R4.size := lt_of_lt_of_le hN hE4.1
  have hO4' : ∀ n, ∀ x ∈ (⟨skeleton.2.outs, zh, ex4⟩ : FinIn).outs.getD n [], x < R4.size :=
    fun n x hx => lt_of_lt_of_le (hO4 n x hx) hE4.1
  obtain ⟨L4', hL4'⟩ := flag_finP4 (impl := impl) (κ := k) (inp := ⟨vk, c, π⟩) (r := R4)
    (fi := ⟨skeleton.2.outs, zh, ex4⟩) (by
      intro x hx
      simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with hx | rfl | rfl
      · exact ysOf_lt hN4 hO4' 4 x hx
      · exact headD_lt (outsOf_lt hN4 hO4' "Pf") hN4
      · exact getLastD_lt (lvOuts_lt hN4 hO4' 4 0) hN4)
  have hrel4 := pureRun_det hp4 (by simpa [finP] using hL4')
  unfold relP4 at hrel4
  rw [Bool.and_eq_true, List.all_eq_true] at hrel4
  obtain ⟨hall4, hpf4⟩ := hrel4
  obtain ⟨-, -, hP0, -, -, -⟩ := pf_facts h (fi := ⟨skeleton.2.outs, zh, ex4⟩) rfl
  refine ⟨?rnd, hpchk, ?start, ?cols, ?link, ?pf0, ?enc, ?fin⟩
  case rnd =>
    intro i hi l hl
    obtain ⟨-, -, -, -, -, -, -, hc⟩ := p1_facts h (fi := ⟨skeleton.2.outs, [], #[]⟩) rfl hi
    exact hc l hl
  case start =>
    obtain ⟨-, -, -, -, h0, -, -, -⟩ :=
      p1_facts h (fi := ⟨skeleton.2.outs, [], #[]⟩) rfl (i := 0) (by norm_num)
    have hs := hStart y hy
    have he : p1Claim0 ⟨skeleton.2.outs, [], #[]⟩ 0 = claim0 ⟨skeleton.2.outs, [], #[]⟩ "P1" := by
      simp [p1Claim0, claim0, lvOuts, outsOf]
    rw [he, hs] at h0
    exact (Val.k.inj h0).symm
  case cols =>
    intro i hi q hq
    rw [hkind] at hq ⊢
    obtain ⟨-, -, hv⟩ := ys_facts h hL hin hπ (fi := ⟨skeleton.2.outs, [], #[]⟩) rfl hi
    obtain ⟨-, col, ss, hss, hpath, hy⟩ := hv q hq
    exact ⟨col, ss, hss, hpath, by simp only [yv]; rw [hy]; rfl⟩
  case link =>
    intro i hi
    obtain ⟨Rk, exk, Lk, hE, hp⟩ := hfield (6 + i) (finP i) (by rw [rest_eq]; interval_cases i <;> rfl)
    have hO' : ∀ n, ∀ x ∈ (⟨skeleton.2.outs, zh, exk⟩ : FinIn).outs.getD n [], x < Rk.size :=
      fun n x hx => lt_of_lt_of_le (hO n x hx) hE.1
    have hN' : 0 < Rk.size := lt_of_lt_of_le hN hE.1
    obtain ⟨L', hL'⟩ := flag_finPLow (impl := impl) (κ := k) (inp := ⟨vk, c, π⟩) (r := Rk)
      (fi := ⟨skeleton.2.outs, zh, exk⟩) i (by
      intro x hx
      simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with (hx | hx) | rfl | rfl
      · exact kcOf_lt hN' hO' i x hx
      · exact ysOf_lt hN' hO' i x hx
      · exact getLastD_lt (lvOuts_lt hN' hO' i 0) hN'
      · exact headD_lt (lvOuts_lt hN' hO' (i + 1) 0) hN')
    have hfp : finP i ⟨skeleton.2.outs, zh, exk⟩ Rk.size = finPLow i ⟨skeleton.2.outs, zh, exk⟩ Rk.size := by
      simp [finP, hi]
    rw [hfp] at hp
    have hrel := pureRun_det hp hL'.1
    obtain ⟨-, -, -, -, h0', -, -, -⟩ := p1_facts h (fi := ⟨skeleton.2.outs, zh, exk⟩) rfl
      (i := i + 1) (by omega)
    obtain ⟨-, -, -, -, -, hN0, -, -⟩ := p1_facts h (fi := ⟨skeleton.2.outs, zh, exk⟩) rfl (i := i)
      (by omega)
    unfold relPLow at hrel
    have hO1 := hOf ⟨skeleton.2.outs, zh, exk⟩ rfl
    rw [hE.rd (x := p1Claim0 ⟨skeleton.2.outs, zh, exk⟩ (i + 1))
      (headD_lt (lvOuts_lt hN hO1 (i + 1) 0) hN), h0', eqv_k] at hrel
    rw [← hrel, FR.vNext, kcTab, hkcRk exk hE i (by omega), hysRk exk hE i (by omega),
      accVal_kc _ _ (by simpa using (lvl_facts k (i := i) (by omega)).2.2.2.2.2.2.2.1),
      hE.rd (x := p1ClaimN ⟨skeleton.2.outs, zh, exk⟩ i) (getLastD_lt (lvOuts_lt hN hO1 i 0) hN), hN0, Val.toK, ← c1_eq c₀ (by omega), hkind]
    refine congrArg (_ + ·) (sum_congr (by simp) fun q hq => ?_)
    rw [List.getD_eq_getElem _ _ (by simpa using hq), List.getElem_map, List.getElem_range]
  case pf0 =>
    obtain ⟨-, -, -, -, -, hN0, -, -⟩ := p1_facts h (fi := ⟨skeleton.2.outs, zh, ex4⟩) rfl (i := 4)
      (by norm_num)
    rw [hE4.rd (x := claim0 ⟨skeleton.2.outs, zh, ex4⟩ "Pf") (headD_lt (outsOf_lt hN hO4 "Pf") hN),
      hE4.rd (x := p1ClaimN ⟨skeleton.2.outs, zh, ex4⟩ 4) (getLastD_lt (lvOuts_lt hN hO4 4 0) hN),
      hP0, hN0, eqv_k] at hpf4
    rw [hpf4, c1_eq c₀ (by norm_num)]
  case enc =>
    intro q hq
    rw [hkind] at hq ⊢
    obtain ⟨hyl, hylt, hv⟩ := ys_facts h hL hin hπ (fi := ⟨skeleton.2.outs, zh, ex4⟩) rfl (i := 4)
      (by norm_num)
    obtain ⟨hidx, col, ss, -, -, hy⟩ := hv q hq
    have hf := hall4 q (List.mem_range.2 (by rw [hyl]; exact hq))
    unfold encFlag at hf
    have hm : (ysOf ⟨skeleton.2.outs, zh, ex4⟩ 4).getD q 0 ∈ ysOf ⟨skeleton.2.outs, zh, ex4⟩ 4 := by
      rw [List.getD_eq_getElem _ _ (by rw [hyl]; exact hq)]; exact List.getElem_mem _
    rw [hE4.rd (lt_of_le_of_lt (α := ℕ) (Nat.sub_le _ _) (hylt _ hm)), hidx, Val.toN,
      hE4.rd (hylt _ hm), hy, eqv_k] at hf
    have hyv : yv 4 q = ∑ r : Fin (lvl k 4).rows, eqBits (sAt (fsOf tr items) 4) (lvl k 4).ell r *
        algebraMap F K (readF col (16 * r)) := by
      simp only [yv]; rw [show ysOf ⟨skeleton.2.outs, [], #[]⟩ 4 = ysOf ⟨skeleton.2.outs, zh, ex4⟩ 4
        from rfl, hy]; rfl
    rw [hyv, ← hf]
    have hle : mLog k 4 ≤ 7 := by rw [mLog_four]; split <;> norm_num
    refine encVal_eq_encAt impl ht ⟨vk, c, π⟩ k _ _ (fun e he => (finalAt_fsQ h.hq ?_).symm) ?_
    · exact lt_of_lt_of_le he (le_trans (Nat.pow_le_pow_right (by norm_num) hle) (by norm_num))
    · intro e he1 he2
      have hn : 26 + 5 * 4 + 1 < phases.length := by rw [phases_length]; omega
      have hsh : phases[26 + 5 * 4 + 1].shape = .absorb fFinal 4096 := by
        rw [phase_lvl_shape (by norm_num) (by norm_num)]; rfl
      rcases final_view h hn hsh with hL32 | hz
      · subst hL32; rw [mLog_four] at he1; simp at he1; omega
      · refine finV_zero hπ hz ?_ he2
        rw [mLog_four] at he1; split at he1 <;> omega
  case fin =>
    obtain ⟨Rf, exf, Lf, hEf, hpf⟩ := hfield 11 finPf rfl
    have hOf' := hOf ⟨skeleton.2.outs, zh, exf⟩ rfl
    have hNf : 0 < Rf.size := lt_of_lt_of_le hN hEf.1
    obtain ⟨Lf', hLf'⟩ := flag_finPf impl k ⟨vk, c, π⟩ ⟨skeleton.2.outs, zh, exf⟩ Rf
      (pfRefs_lt hNf fun n x hx => lt_of_lt_of_le (hOf' n x hx) hEf.1)
    have hrel := (relPf_iff impl k ⟨vk, c, π⟩ _ _).1 (pureRun_det hpf hLf')
    obtain ⟨hpvf, hplf, -, hpNf, hpof, -⟩ := pf_facts h (fi := ⟨skeleton.2.outs, zh, exf⟩) rfl
    rw [hEf.rd (x := claimN ⟨skeleton.2.outs, zh, exf⟩ "Pf") (getLastD_lt (outsOf_lt hN hOf' "Pf") hN),
      hpNf] at hrel
    have hrv := Val.k.inj hrel
    have hch : ∀ v < 7, (rd Rf ((chals ⟨skeleton.2.outs, zh, exf⟩ "Pf" 7).getD v 0)).toK =
        pfP (fsOf tr items) v := fun v hv => by
      rw [hEf.rd (getD_lt hN (chals_lt hN hOf' "Pf" 7) v), hpvf v hv]; rfl
    rw [wV_eq h hL hin hπ (fi := ⟨skeleton.2.outs, zh, exf⟩) rfl hEf ht W₀ hkind
        (hW0 y hy _ Rf rfl hEf), padV_eq k _ Rf (fsOf tr items) hch, ← hkind] at hrv
    have hfin : finHat ⟨vk, c, π⟩ ⟨skeleton.2.outs, zh, exf⟩ Rf =
        mleN 7 (finalAt (fsOf tr items)) (pfPt (fsOf tr items)) := by
      rw [finHat, fhVal_mle _ _ (by simp [hplf])]
      unfold mleN
      have e1 : (fun u : Fin (2 ^ 7) => finV ⟨vk, c, π⟩ u) =
          fun u : Fin (2 ^ 7) => finalAt (fsOf tr items) u := by
        funext u; exact (finalAt_fsQ hq u.2).symm
      have e2 : (fun v : Fin 7 => (((chals ⟨skeleton.2.outs, zh, exf⟩ "Pf" 7).map fun x =>
          (rd Rf x).toK).toArray).getD v 0) = pfPt (fsOf tr items) := by
        funext v
        have hv := v.2
        have := hch v hv
        rw [List.getD_eq_getElem _ _ (by rw [hplf]; exact hv)] at this
        simp only [Array.getD_eq_getD_getElem?, List.getElem?_toArray, List.getElem?_map,
          List.getElem?_eq_getElem (by rw [hplf]; exact hv : (v : ℕ) < _), Option.map_some,
          Option.getD_some]
        rw [this]; rfl
      rw [e1, e2]
    rw [show clR2 pfStart 32 readK chK (lvC c₀ 5) L (fsOf tr items) 7 =
      rVal pfStart (fsOf tr items) 6 from rfl, hrv, hfin]

/-! ## `hAcc` with `hFin` discharged -/

/-- **`implC`'s `tensorW` is the spec's** (`implC_meets`, the `tensorW` field; `specC`'s
`tensorW` is `Impl.tensorWS`). -/
theorem tensorW_implC (fin : Finals) (lRows : List Circ.Row) (κs₀ : F) :
    ∀ j r, (Impl.implC fin lRows κs₀).tensorW j r = Impl.tensorWS j r :=
  (Impl.implC_meets fin lRows κs₀).2.2.2.1

/-- **`hAcc` for `Vwith impl (sfFinals finP finPf)`**, `tensorW` at the spec: `hAcc_of`'s
`hFin` is `finLog_of_run`; what is left is the front's: `hStart` (`claim0 "P1"` holds `c₀`),
`hW0` (`Ŵ₀(P₀)` is `wHatL … 0`) and `hFront` (`¬ RejF`). -/
theorem hAcc_of_fin (impl : OpImpl) (S : Submission) (vk : Digest)
    {W₀ : Log → Log → ℕ → K} {c₀ : Log → Log → K} {RejF : Log → Log → Prop}
    (hV : S.V = Vwith impl (sfFinals finP finPf)) (hq : S.qV = qV)
    (ht : ∀ j r, impl.tensorW j r = Impl.tensorWS j r)
    (hE : ∀ c π L, FR.kindOf π = .W → π.size < 2 ^ 64 → S.E c π L = WitnessSending.decode π)
    (hStart : ∀ (k : Kind) (c : Digest) (π : Proof) (L tr : Log) (y : List Val × List Bool × Trace),
      ¬ Bad L → π.size = piSize → FR.kindOf π = .snark k →
      semIR impl (gen (sfFinals finP finPf) (.fixed k)) ⟨vk, c, π⟩ tr = some true →
      (∀ e ∈ tr, e ∈ L) → refPhases impl k ⟨vk, c, π⟩ phases 0 ctx₀ #[] tr = some y →
      rd (#[] ++ y.1.toArray) (claim0 ⟨skeleton.2.outs, [], #[]⟩ "P1") = .k (c₀ L (fsOf tr items)))
    (hW0 : ∀ (k : Kind) (c : Digest) (π : Proof) (L tr : Log) (y : List Val × List Bool × Trace),
      ¬ Bad L → π.size = piSize → FR.kindOf π = .snark k →
      semIR impl (gen (sfFinals finP finPf) (.fixed k)) ⟨vk, c, π⟩ tr = some true →
      (∀ e ∈ tr, e ∈ L) → refPhases impl k ⟨vk, c, π⟩ phases 0 ctx₀ #[] tr = some y →
      ∀ (fi : FinIn) (r' : Array Val), fi.outs = skeleton.2.outs → ExtA (#[] ++ y.1.toArray) r' →
        w0V impl k fi r' = wHatL W₀ L (fsOf tr items) 0)
    (hFront : ∀ (k : Kind) (c : Digest) (π : Proof) (L tr : Log) (j : ℕ), ¬ Bad L →
      π.size = piSize → semIR impl (gen (sfFinals finP finPf) (.fixed k)) ⟨vk, c, π⟩ tr = some true →
      (∀ e ∈ tr, e ∈ L) → IsChain L j → entriesOf L (pathOf L j) = fsOf tr items →
      ¬ RejF L (entriesOf L (pathOf L j))) :
    ∀ L c π, L.length ≤ logCap → ¬ Bad L → (S.V vk c π).runLog L = some true →
      (∃ w, S.E c π L = some w ∧ Rel (S.acc vk) c w) ∨ ∃ j, AcceptTail RejF W₀ c₀ L j := by
  intro L c π _ hb hrun
  rcases hk : FR.kindOf π with _ | _ | k
  · exact .inl (acc_W impl _ S hV hq hE hk hrun)
  · exact absurd (hV ▸ hrun) (not_acc_bad impl _ hk)
  · have hπ := size_of_snark hk
    rw [hV, V_snark impl _ vk c π hk] at hrun
    obtain ⟨tr, hsem, hin, j, hci, hes, hlen⟩ := runLog_chain impl _ hb hπ hrun
    obtain ⟨y, hy⟩ := finLog_of_run ht hb hπ hk hsem hin
      (fun y hy' => hStart k c π L tr y hb hπ hk hsem hin hy')
      (fun y hy' => hW0 k c π L tr y hb hπ hk hsem hin hy')
    rw [← hes] at hy
    exact .inr ⟨j, acceptTail_of_finLog hb hci hlen (hFront k c π L tr j hb hπ hsem hin hci hes) hy⟩

end FR.Snd
