-- New for `flock-recursive` (BLUEPRINT §5.4, A.10 "What `final` then gets"; stage S-G3).
import FRSoundnessLigFinal
import FRVIRChain
import FRVerifier

/-!
# An accepted run's chain (`runLog_chain`) and the `W` branch of `hAcc`

* **`runLog_trace`**: a program accepted on a log is accepted on a trace of the log's entries (the
  first entry for each query, in the order asked).
* **`path_of_links`**: on a log without bad events, entries of the log linked state to previous
  answer, from a seed, are the forest path of the last one (`entriesOf L (pathOf L j) = es`).
* **`matches_fsQ`**: the 468 Fiat–Shamir entries of an accepted SNARK run (`fsQ_gen`) match the
  items (`Matches`).
* **`runLog_chain`**: an accepted SNARK run on a log without bad events has a chain `j`
  (`IsChain L j`) whose entries are the run's Fiat–Shamir entries, 468 of them; so
  `p3S0 4 < |es|` and `pfStart + 14 ≤ |es|`.
* **`acc_W`**: the `W` branch: an accepted `W` proof of fewer than `2^64` bytes is extracted (`E`
  copies it) to a witness of `Rel (S.acc vk)`.
* **`WBeyond`** (INT-6, core PR #20): `acc` bounds a child's proof by the word (`|π| < 2^64`), no
  longer by `proofCap`, so an accepted `W` node proof (two children of up to `2^64 − 1` bytes) may
  itself have `2^64` bytes or more, where the extractor's 64-bit length word is ambiguous and
  `FRXSpec.E_W` does not apply. `WBeyond S vk` is the `final` law on those proofs, a residual
  until B-15's `E := if InDom then E_den else E_search` (S-H2n); **`acc_W_all`** is the whole `W`
  branch from `acc_W` and `WBeyond`. Control: `wBeyond_of_decode` (an `E` whose `W` case is
  `decode` on every size meets it, as the contract's witness-sending `E` does).
-/

namespace FR.Snd
open RecursionFast FR.Merkle

/-! ## A run on a log is a run on a trace of its entries -/

/-- **`runLog_trace`**: a verdict on the log is a verdict on a trace of the log's entries. -/
theorem runLog_trace {α : Type} {L : Log} :
    ∀ (p : OProg α) {b : α}, p.runLog L = some b → ∃ tr : Trace, p.runSeq tr = some b ∧ ∀ e ∈ tr, e ∈ L
  | .ret a, b, h => ⟨[], h, by simp⟩
  | .query q k, b, h => by
    obtain ⟨e, he, rfl, hk⟩ := runLog_query h
    obtain ⟨tr, h1, h2⟩ := runLog_trace (k e.2) hk
    refine ⟨e :: tr, ?_, ?_⟩
    · rw [show e = (e.1, e.2) from rfl, OProg.runSeq_query]; exact h1
    · intro x hx
      rcases List.mem_cons.mp hx with rfl | hx
      · exact he
      · exact h2 x hx

/-! ## Linked entries are a forest path -/

/-- **Entries linked to the previous answer, from an entry with no state, are the forest path of
the last one** (on a log without bad events, every entry in the log). -/
theorem path_of_links {L : Log} (hb : ¬ Bad L) {es : Log} (hin : ∀ e ∈ es, e ∈ L)
    (h0 : ∀ h : 0 < es.length, stateIn (es[0]'h).1 = none)
    (hs : ∀ n (h : n + 1 < es.length), stateIn (es[n + 1]'h).1 = some (es[n]'(by omega)).2) :
    ∀ n (h : n < es.length), ∃ j, ∃ hj : j < L.length, L[j] = es[n] ∧
      entriesOf L (pathOf L j) = es.take (n + 1) := by
  intro n
  induction n with
  | zero =>
    intro h
    obtain ⟨j, hj, hje⟩ := List.getElem_of_mem (hin _ (List.getElem_mem h))
    refine ⟨j, hj, hje, ?_⟩
    have hp : predIdx L j = none := by
      simp only [predIdx, List.getElem?_eq_getElem hj, Option.bind_some, hje, h0 h,
        Option.bind_none]
    rw [pathOf, back, hp]
    dsimp only
    simp only [entriesOf, List.map_cons, List.map_nil, getElem!_pos L j hj, hje]
    rw [List.take_add_one, List.take_zero, List.nil_append, List.getElem?_eq_getElem h]; rfl
  | succ n ih =>
    intro h
    obtain ⟨i, hi, hie, hpi⟩ := ih (by omega)
    obtain ⟨j, hj, hje⟩ := List.getElem_of_mem (hin _ (List.getElem_mem h))
    have hp : predIdx L j = some i := by
      simp only [predIdx, List.getElem?_eq_getElem hj, Option.bind_some, hje, hs n h, ← hie,
        ansIdx_self hb hi]
    have hij : i < j := predIdx_lt hb hp
    refine ⟨j, hj, hje, ?_⟩
    rw [pathOf, back, hp]
    dsimp only
    rw [ite_pos' hij, back_fuel L j i hij, ← pathOf]
    simp only [entriesOf, List.map_append, List.map_cons, List.map_nil] at hpi ⊢
    rw [hpi, getElem!_pos L j hj, hje]
    conv_rhs => rw [List.take_add_one, List.getElem?_eq_getElem h]
    rfl

/-! ## The Fiat–Shamir entries of a run match the items -/

theorem mem_fsOf {seg : Trace} {its : List Item} {e : ByteArray × Digest} (h : e ∈ fsOf seg its) :
    e ∈ seg := by
  simp only [fsOf, List.mem_map, List.mem_filter] at h
  obtain ⟨⟨e', it⟩, ⟨hm, -⟩, rfl⟩ := h
  exact (List.of_mem_zip hm).1

theorem fsItems_getElem {p : ℕ} (hp : p < fsItems.length) :
    fsItems[p] = X.msgItem p (X.fsMsgs.getD p none) := by
  have h := congrArg (fun l => l[p]?) X.fsMsgs_items
  simp only [List.getElem?_map, List.getElem?_range (show p < 468 by rw [← fsItems_length]; exact hp),
    Option.map_some, List.getElem?_eq_getElem hp, Option.some.injEq] at h
  exact h.symm

theorem msgOk_getD {p o len : ℕ} (h : X.fsMsgs.getD p none = some (o, len)) :
    o + len ≤ 797904 := by
  have hp : p < X.fsMsgs.length := by
    by_contra hp; rw [List.getD_eq_default _ _ (by omega)] at h; cases h
  have hm := List.all_eq_true.mp X.fsMsgs_aligned _ (List.getElem_mem hp)
  rw [List.getD_eq_getElem _ _ hp] at h
  rw [h] at hm
  simp only [X.msgOk, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at hm
  exact hm.2

theorem size_extract_of_le {π : Proof} {o len : ℕ} (h : o + len ≤ π.size) :
    (π.extract o (o + len)).size = len := by
  rw [ByteArray.size_extract]; omega

theorem fsCheck_absorbQ (st : Digest) (msg : ByteArray) :
    fsCheck (.absorb msg.size) (absorbQ st msg) = true := by
  have hc : (absorbQ st msg).data.toList.take 8 = tagAbs := by rw [absorbQ_data]; simp [tagAbs]
  simp [fsCheck, hc, absorbQ_size]

theorem fsCheck_squeezeQ (st : Digest) : fsCheck .squeeze (squeezeQ st) = true := by
  have hc : (squeezeQ st).data.toList.take 8 = tagSqz := by rw [squeezeQ_data]; simp [tagSqz]
  simp [fsCheck, hc, squeezeQ_size]

theorem fsCheck_seedQ (vk c : Digest) (hdr : ByteArray) (hh : hdr.size = 48) :
    fsCheck .seed (seedQ vk c hdr) = true := by
  have h := (matches_seed vk c hdr hh zeroD).1
  simpa using h

/-- **The query of position `p` passes position `p`'s item check** on a proof of `piSize` bytes. -/
theorem fsCheck_fsQ (vk c : Digest) {π : Proof} (hπ : π.size = piSize) {p : ℕ} (hp : p < 468)
    (st : Digest) :
    fsCheck (fsItems[p]'(by rw [fsItems_length]; exact hp)) (X.fsQ vk c π p st) = true := by
  rw [fsItems_getElem]
  unfold X.fsQ
  rcases hm : X.fsMsgs.getD p none with _ | ⟨o, len⟩
  · rcases p with _ | p
    · rw [X.fsMsgs_ctl.1] at hm; cases hm
    · exact fsCheck_squeezeQ st
  · have hs := size_extract_of_le (π := π) (o := o) (len := len)
      (by rw [hπ, piSize_eq]; exact msgOk_getD hm)
    dsimp only
    rcases p with _ | p
    · rw [ite_pos' rfl]
      rw [X.fsMsgs_ctl.1, Option.some.injEq, Prod.mk.injEq] at hm
      obtain ⟨rfl, rfl⟩ := hm
      exact fsCheck_seedQ vk c _ hs
    · rw [ite_neg' (by omega), X.msgItem]
      have := fsCheck_absorbQ st (π.extract o (o + len))
      rwa [hs] at this

/-- **The run's Fiat–Shamir entries match the items** (`Matches`), and are linked. -/
theorem matches_fsQ (vk c : Digest) {π : Proof} (hπ : π.size = piSize) {es : Log}
    (hl : es.length = 468)
    (hq : ∀ p < 468, (es.getD p default).1 = X.fsQ vk c π p (es.getD (p - 1) default).2) :
    Matches es ∧ (∀ h : 0 < es.length, stateIn (es[0]'h).1 = none) ∧
      ∀ n (h : n + 1 < es.length), stateIn (es[n + 1]'h).1 = some (es[n]'(by omega)).2 := by
  have hq' : ∀ p (h : p < es.length), (es[p]'h).1 = X.fsQ vk c π p (es.getD (p - 1) default).2 :=
    fun p h => by rw [← hq p (by omega), List.getD_eq_getElem _ _ h]
  have hck : ∀ p (h : p < es.length), fsCheck (fsItems[p]'(by rw [fsItems_length]; omega))
      (es[p]'h).1 = true := fun p h => by rw [hq' p h]; exact fsCheck_fsQ vk c hπ (by omega) _
  have hlink : ∀ n (h : n + 1 < es.length), stateIn (es[n + 1]'h).1 = some (es[n]'(by omega)).2 :=
    fun n h => by
      rw [hq' _ h, X.stateIn_fsQ vk c π (by omega), Nat.add_sub_cancel,
        List.getD_eq_getElem _ _ (by omega)]
  have h0 : ∀ h : 0 < es.length, fsCheck .seed (es[0]'h).1 = true := fun h => by
    have := hck 0 h
    rwa [fsItems_getElem, X.msgItem] at this
  refine ⟨⟨?_, ⟨by rw [hl, fsItems_length], fun i hi => ⟨hlink i hi, hck (i + 1) hi⟩⟩⟩,
    fun h => stateIn_of_seed (h0 h), hlink⟩
  rcases es with _ | ⟨e, es⟩
  · simp at hl
  · simp only [List.head?_cons, Option.map_some]
    exact congrArg some (h0 (by simp))

/-! ## `runLog_chain` -/

/-- **`runLog_chain`**: an accepted SNARK run on a log without bad events has a chain `j` whose
entries are the run's 468 Fiat–Shamir entries (`fsQ_gen` on a trace of the log's entries). -/
theorem runLog_chain (impl : OpImpl) (fin : Finals) {k : Kind} {vk c : Digest} {π : Proof}
    {L : Log} (hb : ¬ Bad L) (hπ : π.size = piSize)
    (hrun : (runIR impl (gen fin (.fixed k)) ⟨vk, c, π⟩).runLog L = some true) :
    ∃ tr : Trace, semIR impl (gen fin (.fixed k)) ⟨vk, c, π⟩ tr = some true ∧
      (∀ e ∈ tr, e ∈ L) ∧ ∃ j, IsChain L j ∧ entriesOf L (pathOf L j) = fsOf tr items ∧
        (entriesOf L (pathOf L j)).length = 468 := by
  obtain ⟨tr, h1, h2⟩ := runLog_trace _ hrun
  rw [runSeq_runIR] at h1
  obtain ⟨hl, hq⟩ := fsQ_gen ⟨vk, c, π⟩ impl fin _ h1
  obtain ⟨hm, h0, hs⟩ := matches_fsQ vk c hπ hl hq
  have hin : ∀ e ∈ fsOf tr items, e ∈ L := fun e he => h2 e (mem_fsOf he)
  obtain ⟨j, hj, -, hp⟩ := path_of_links hb hin h0 hs 467 (by omega)
  rw [show 467 + 1 = (fsOf tr items).length by omega, List.take_length] at hp
  exact ⟨tr, h1, h2, j, ⟨hj, hp ▸ hm⟩, hp, by rw [hp, hl]⟩

/-- The chain's length covers P3.4 and Pf. -/
theorem chain_len_468 {es : Log} (h : es.length = 468) :
    p3S0 4 < es.length ∧ pfStart + 14 ≤ es.length := by
  have hp := pfStart_eq
  have h4 := (tail_pos (show 4 < 5 by norm_num)).2.2.2.2
  have hnx : nxStart 4 = pfStart := rfl
  omega

/-! ## The `W` branch -/

theorem length_flatMap_le {α β : Type} (l : List α) (f : α → List β) {B : ℕ}
    (h : ∀ a ∈ l, (f a).length ≤ B) : (l.flatMap f).length ≤ l.length * B := by
  induction l with
  | nil => simp
  | cons a l ih =>
    simp only [List.flatMap_cons, List.length_append, List.length_cons]
    have := h a (List.mem_cons_self ..)
    have := ih fun x hx => h x (List.mem_cons_of_mem _ hx)
    nlinarith

/-- An accepted child's output words are fewer than `2^62` (core PR #20: its proof is below the
word, `2^61` words; v4's `proofCap` gave `2^32`). -/
theorem signedWords_length_lt {vk : Digest} {p : Signed} {v : Unit → OProg Bool}
    (h : accWith vk p v = true) : (signedWords p).length < 2 ^ 62 := by
  have hf := fits_of_accWith h
  simp only [accWith, Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨⟨⟨hπ, htr⟩, hq⟩, -⟩, -⟩ := h
  have ho := hf.2.2.2.2.1
  have hpa := hf.2.2.2.2.2
  have hlog : (logWords p.tr).length ≤ 1 + p.tr.length * (2 ^ 17 + 6) := by
    simp only [logWords, List.length_cons]
    have := length_flatMap_le p.tr (fun e => bytesWords e.1.data.toList ++ packBytes e.2.toList)
      (B := 2 ^ 17 + 6) fun e he => by
        have := hq e he
        simp only [List.length_append, bytesWords, List.length_cons, packBytes_length,
          Vector.length_toList, Array.length_toList]
        change (e.1.size + 7) / 8 + 1 + (32 + 7) / 8 ≤ _
        rw [queryCap] at this; omega
    omega
  have hsig : (sigWords p.σ).length ≤ 1 + 133 * 4 + 16 * 4 := by
    simp only [sigWords, List.length_cons, List.length_append]
    have h1 := length_flatMap_le p.σ.ots (fun d => packBytes d.toList) (B := 4) fun d _ => by
      simp [packBytes_length]
    have h2 := length_flatMap_le p.σ.path (fun d => packBytes d.toList) (B := 4) fun d _ => by
      simp [packBytes_length]
    rw [ho, wotsLen] at h1; rw [hpa, sigHeight] at h2
    omega
  simp only [signedWords, List.length_append, bytesWords, List.length_cons, packBytes_length,
    Array.length_toList]
  change (p.π.size + 7) / 8 + 1 + (logWords p.tr).length + (sigWords p.σ).length < _
  rw [qV] at htr
  have : p.tr.length * (2 ^ 17 + 6) ≤ 10240 * (2 ^ 17 + 6) := Nat.mul_le_mul_right _ htr
  omega

/-- An accepted `W` proof decodes to a witness of `Rel (S.acc vk)`. -/
theorem acc_W_dec (impl : OpImpl) (fin : Finals) (S : Submission) (hV : S.V = Vwith impl fin)
    (hq : S.qV = qV) {vk c : Digest} {π : Proof} {L : Log} (hW : FR.kindOf π = .W)
    (hrun : (S.V vk c π).runLog L = some true) :
    ∃ w, WitnessSending.decode π = some w ∧ Rel (S.acc vk) c w := by
  rw [hV, V_W impl fin vk c π hW] at hrun
  simp only [OProg.runLog, Option.some.injEq] at hrun
  have hret : Vwith impl fin vk c π = .ret true := by rw [V_W impl fin vk c π hW, hrun]
  obtain ⟨w, hd, -, hR⟩ := V_W_sound impl fin vk c π hW hret
  exact ⟨w, hd, by rw [acc_eq impl fin S hV hq]; exact hR⟩

/-- **The `W` branch of `hAcc`**: an accepted `W` proof of fewer than `2^64` bytes is extracted,
by `E` copying it, to a witness of `Rel (S.acc vk)`. `E` is any extractor whose `W` case below
the word is `decode` (`FRXSpec.E_W`). -/
theorem acc_W (impl : OpImpl) (fin : Finals) (S : Submission) (hV : S.V = Vwith impl fin)
    (hq : S.qV = qV)
    (hE : ∀ c π L, FR.kindOf π = .W → π.size < 2 ^ 64 → S.E c π L = WitnessSending.decode π)
    {vk c : Digest} {π : Proof} {L : Log} (hW : FR.kindOf π = .W) (hπ : π.size < 2 ^ 64)
    (hrun : (S.V vk c π).runLog L = some true) :
    ∃ w, S.E c π L = some w ∧ Rel (S.acc vk) c w := by
  obtain ⟨w, hd, hR⟩ := acc_W_dec impl fin S hV hq hW hrun
  exact ⟨w, by rw [hE c π L hW hπ, hd], hR⟩

/-- **The `W` proofs beyond the word** (core PR #20): every accepted `W` proof of `2^64` bytes or
more is extracted to a witness of `Rel (S.acc vk)`. The residual of the `W` branch until B-15. -/
def WBeyond (S : Submission) (vk : Digest) : Prop :=
  ∀ L c π, FR.kindOf π = .W → 2 ^ 64 ≤ π.size → (S.V vk c π).runLog L = some true →
    ∃ w, S.E c π L = some w ∧ Rel (S.acc vk) c w

/-- **The whole `W` branch of `hAcc`**: `acc_W` below the word, `WBeyond` above it. -/
theorem acc_W_all (impl : OpImpl) (fin : Finals) (S : Submission) (hV : S.V = Vwith impl fin)
    (hq : S.qV = qV)
    (hE : ∀ c π L, FR.kindOf π = .W → π.size < 2 ^ 64 → S.E c π L = WitnessSending.decode π)
    {vk c : Digest} (hWB : WBeyond S vk) {π : Proof} {L : Log} (hW : FR.kindOf π = .W)
    (hrun : (S.V vk c π).runLog L = some true) :
    ∃ w, S.E c π L = some w ∧ Rel (S.acc vk) c w :=
  if hπ : π.size < 2 ^ 64 then acc_W impl fin S hV hq hE hW hπ hrun
  else hWB L c π hW (Nat.le_of_not_lt hπ) hrun

/-- Control (positive): an extractor whose `W` case is `decode` on every size (the contract's
witness-sending `E`) meets `WBeyond`. -/
theorem wBeyond_of_decode (impl : OpImpl) (fin : Finals) (S : Submission)
    (hV : S.V = Vwith impl fin) (hq : S.qV = qV)
    (hE : ∀ c π L, FR.kindOf π = .W → S.E c π L = WitnessSending.decode π) (vk : Digest) :
    WBeyond S vk := fun L c π hW _ hrun => by
  obtain ⟨w, hd, hR⟩ := acc_W_dec impl fin S hV hq hW hrun
  exact ⟨w, by rw [hE c π L hW, hd], hR⟩

/-- **A `bad` proof is never accepted** (it is rejected with no query). -/
theorem not_acc_bad (impl : OpImpl) (fin : Finals) {vk c : Digest} {π : Proof} {L : Log}
    (hb : FR.kindOf π = .bad) : (Vwith impl fin vk c π).runLog L ≠ some true := by
  rw [V_bad impl fin vk c π hb]; simp [OProg.runLog]

end FR.Snd
