-- New for `flock-recursive` (BLUEPRINT §4.2 `stmtOk`, §5.4, A.9; stage S-N1).
-- RET-2: the declarations revision 4.1 reads moved to `FRSoundnessCoreAcc`.
import FRSoundnessExtR
import FRSoundness4P4aSeg

/-!
# The accepted run's statement check, and the chain's public values

On an accepted skeleton run (`SkRun`), phase 1 (`stmt`'s absorb, `stmtOps`) passed its flag
(`refPhase`'s absorb case for `fStmt`):

* **`stmt_view`**: `stmtDigest κ stmt = c`; a leaf kind's `stmt` bytes `33 … 40` are
  `enc64 (leafN κ)`; a node's `hdr.pub` (bytes 16–47) is `vk`.

On the run's Fiat–Shamir chain (`SkRun.hq`):

* **`stLog_eq`**: the statement's digests on the log (`stL es σ`) are π's `stmt` bytes;
* **`seedHdr_eq`**: the seed query's bytes `71 …` are π's `hdr`, so the chain's kind
  (`kindOf es`, byte 71) is π's kind (**`kindOf_chain`**), and the seed's start digest (bytes
  87 … 118, `bndL`) is `bytesAt π 16 32`;
* **`c_node_of_run`**, **`c_leaf_of_run`**: the statement `c` in the chain's terms.
-/

namespace FR.Snd
open RecursionFast Finset

set_option linter.constructorNameAsVariable false

variable {impl : OpImpl} {κ : Kind} {inp : Input} {tr : Trace} {y : List Val × List Bool × Trace}

theorem phase1_shape : (phases[1]'(by rw [phases_length]; omega)).shape = .absorb fStmt 128 := rfl

theorem phaseOff_stmt1 : phaseOff 1 fStmt = 0 := by decide

/-- **The run's statement check** (phase 1's flag, `stmtOps`). -/
theorem stmt_view (h : SkRun impl κ inp tr y) :
    stmtDigest κ (FR.msgAt inp fStmt 0 128) = inp.c ∧
      (κ.isNode = false →
        (FR.msgAt inp fStmt 33 8).data = (bytesOf (enc64 (leafN κ))).data) ∧
      (κ.isNode = true → bytesAt inp.π (absOff fHdr 16) 32 = inp.vk) := by
  have hn : 1 < phases.length := by rw [phases_length]; omega
  obtain ⟨trk, M, x, hx, -, -, -, hfl, -⟩ := phase_at impl κ inp h.ref hn
  have hflag := h.flags _ hfl
  simp only [refPhase, phase1_shape, phaseOff_stmt1] at hx
  obtain ⟨a, -, rfl⟩ := Option.map_eq_some_iff.1 hx
  simp only [↓reduceIte, Bool.and_eq_true, decide_eq_true_eq, Bool.or_eq_true] at hflag
  obtain ⟨⟨⟨⟨⟨h1, -⟩, h2⟩, -⟩, -⟩, h3⟩ := hflag
  refine ⟨h1, fun hk => ?_, fun hk => ?_⟩
  · rcases h2 with h2 | h2
    · rw [hk] at h2; cases h2
    · exact h2
  · rcases h3 with h3 | h3
    · rw [hk] at h3; cases h3
    · exact h3

/-! ## The chain's public values -/

variable {vk c : Digest} {π : Proof} {es : Log}

/-- **The log's statement digests are π's** (bytes `1 + 32σ` of `stmt`). -/
theorem stLog_eq (hq : ∀ p < 468, (es.getD p default).1 = X.fsQ vk c π p (es.getD (p - 1) default).2)
    {σ : ℕ} (hσ : σ ≤ 1) : stL es σ = bytesAt π (absOff fStmt (1 + 32 * σ)) 32 := by
  have hn : 1 < phases.length := by rw [phases_length]; omega
  have hm : X.fsMsgs.getD 1 none = some (fieldOff fStmt + phaseOff 1 fStmt, 128) := by
    have h1 : phStart 1 = 1 := by simp only [phStart, fsStarts_eq]; decide
    have := fsMsgs_phase (k := 0) hn (by rw [phase1_shape]; simp [X.phaseMsgs])
    rw [Nat.add_zero, h1] at this
    rw [this, phase1_shape]; simp [X.phaseMsgs]
  rw [phaseOff_stmt1, Nat.add_zero] at hm
  rw [stL, msgAt_fsQ hq (by norm_num) (by norm_num) hm, bytesAt_extract_le π (by omega),
    absOff_eq (by decide)]

/-- **The seed entry's query is `seedQ vk c hdr`** with `hdr` π's first 48 bytes. -/
theorem seed_query (hq : ∀ p < 468, (es.getD p default).1 = X.fsQ vk c π p (es.getD (p - 1) default).2) :
    (entAt es 0).1 = seedQ vk c (π.extract 0 48) := by
  have h0 := hq 0 (by norm_num)
  unfold X.fsQ at h0
  rw [X.fsMsgs_ctl.1] at h0
  simpa only [ite_true, entAt] using h0

/-- Byte `71 + k` of the seed query is π's byte `k` (`k < 48`). -/
theorem seed_byte (hq : ∀ p < 468, (es.getD p default).1 = X.fsQ vk c π p (es.getD (p - 1) default).2)
    {k : ℕ} (hk : k < 48) :
    (entAt es 0).1.data.toList.getD (71 + k) 0 = π.data.toList.getD k 0 := by
  rw [seed_query hq, X.seedQ_data', List.getD_append_right _ _ _ _ (by simp [tagSeed]; omega),
    List.getD_append_right _ _ _ _ (by simp [tagSeed]; omega),
    List.getD_append_right _ _ _ _ (by simp [tagSeed]; omega), toList_extract]
  simp only [tagSeed, List.length_cons, List.length_nil, Vector.length_toList, Nat.sub_zero,
    List.drop_zero]
  rw [show 71 + k - 7 - 32 - 32 = k by omega, List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD,
    List.getElem?_take_of_lt hk]

/-- The seed's bytes `87 …`: `bytesAt` of the seed query at `71 + o` is π's at `o`. -/
theorem seed_bytesAt (hq : ∀ p < 468, (es.getD p default).1 = X.fsQ vk c π p (es.getD (p - 1) default).2)
    {o n : ℕ} (h : o + n ≤ 48) : bytesAt (entAt es 0).1 (71 + o) n = bytesAt π o n := by
  ext k hk
  rw [getElem_bytesAt _ _ _ _ hk, getElem_bytesAt _ _ _ _ hk, Nat.add_assoc,
    seed_byte hq (by omega)]

/-- **The chain's kind is π's kind.** -/
theorem kindOf_chain (hq : ∀ p < 468, (es.getD p default).1 = X.fsQ vk c π p (es.getD (p - 1) default).2)
    {k : Kind} (hk : FR.kindOf π = .snark k) : kindOf es = k := by
  have hb := Node.byte_of_kindOf hk
  have hs := size_of_snark hk
  have e : (entAt es 0).1.data[71]? = π.data[0]? := by
    have h0 : 0 < π.data.toList.length := by
      rw [Array.length_toList]; change 0 < π.size; rw [hs, piSize_eq]; norm_num
    rw [seed_query hq, ← Array.getElem?_toList, X.seedQ_data', ← Array.getElem?_toList]
    simp only [tagSeed, toList_extract]
    simp [List.getElem?_append_right, h0]
  unfold kindOf
  rw [e, hb]
  simp [Kind.ofByte?_byte]

/-! ## The statement in the chain's terms -/

/-- **A node's statement on its run** is the node statement of the log's digests. -/
theorem c_node_of_run (h : SkRun impl .N30 ⟨vk, c, π⟩ tr y) :
    c = nodeStmt (stL (fsOf tr items) 0) (stL (fsOf tr items) 1) := by
  have h1 : stmtDigest .N30 (FR.msgAt ⟨vk, c, π⟩ fStmt 0 128) = c := (stmt_view h).1
  rw [stLog_eq h.hq (by norm_num), stLog_eq h.hq (by norm_num)]
  rw [← h1, stmtDigest, nodeStmtF_eq, FR.msgAt, bytesAt_extract_le _ (by omega),
    bytesAt_extract_le _ (by omega)]
  simp only [absOff_eq (show fStmt ≤ nFields by decide)]

/-- **A node's `hdr.pub` is `vk`** on its run. -/
theorem vkOf_of_run (h : SkRun impl .N30 ⟨vk, c, π⟩ tr y) : X.vkOf π = vk := by
  have := (stmt_view h).2.2 rfl
  rwa [absOff_eq (show fHdr ≤ nFields by decide)] at this

end FR.Snd
