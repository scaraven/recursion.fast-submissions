-- New for `flock-recursive` (BLUEPRINT §6.2, A.4, §10 changes 14: the fold challenges; stage
-- S-H2, track L-ext).
import FRXChainTop

/-!
# The chain scan for Flock's verifier: the targets, the table, `chain_spec`

* `fsMsgs`: per Fiat–Shamir position (A.4's 468 items), the π byte range `(o, len)` of the
  absorbed message (the seed's: `hdr`, bytes `0 … 47`), `none` for a squeeze. It is read off the
  phase table exactly as `FRVIR.genPhase` asks (`phaseOff n f`, `j · roundBytes` per round).
  Controls: `fsMsgs_length` (468), `fsMsgs_items` (the kinds and lengths are `fsItems`),
  `fsMsgs_aligned` (every message is 8-byte aligned inside `piSize`).
* `fsQ vk c π p st`: the query at position `p` when the previous answer is `st` (A.2).
* `chTab`: the table words, `tabW_chTab`: they realise `fsQ` on every SNARK tape.
* **`chain_spec`**: on a log with no state hit, the machine's answer at position `p < nRep`
  (`nRep = 442`: through P1.4's last round) is the first-match chain's (`fmAns`), i.e. `runLog`'s.
  The seed block is a parameter (`SeedOK`): the seed `"FRSEED0" ‖ vk ‖ c ‖ hdr` carries `vk`,
  which the extractor is not given (V4-6); see S-H2-RESULT Part 13, Q1.
-/

namespace FR.X

open RecursionFast FR.Snd

/-! ## The Fiat–Shamir messages -/

/-- A phase's Fiat–Shamir positions: the absorbed π range, or `none` for a squeeze. -/
def phaseMsgs (n : ℕ) : Shape → List (Option (ℕ × ℕ))
  | .seed => [some (fieldOff fHdr, 48)]
  | .absorb f len => [some (fieldOff f + phaseOff n f, len)]
  | .squeezes k _ => List.replicate k none
  | .uni f => [some (fieldOff f + phaseOff n f, uniBytes), none]
  | .rounds f k _ inK _ => (List.range k).flatMap fun j =>
      [some (fieldOff f + phaseOff n f + j * roundBytes inK, roundBytes inK), none]
  | .queries _ => []

/-- **The Fiat–Shamir messages** in item order. -/
def fsMsgs : List (Option (ℕ × ℕ)) :=
  ((List.range phases.length).zip phases).flatMap fun np => phaseMsgs np.1 np.2.shape

/-- The item kind of a message entry (position `0` is the seed). -/
def msgItem : ℕ → Option (ℕ × ℕ) → Item
  | 0, _ => .seed
  | _ + 1, some (_, len) => .absorb len
  | _ + 1, none => .squeeze

/-- Control: 468 positions. -/
theorem fsMsgs_length : fsMsgs.length = 468 := by decide +kernel

/-- **Control: the kinds and lengths are A.4's Fiat–Shamir items.** -/
theorem fsMsgs_items : (List.range 468).map (fun p => msgItem p (fsMsgs.getD p none)) = fsItems := by
  decide +kernel

/-- Every message's check: 8-byte aligned, inside `piSize`. -/
def msgOk : Option (ℕ × ℕ) → Bool
  | some (o, len) => o % 8 == 0 && len % 8 == 0 && decide (o + len ≤ 797904)
  | none => true

/-- **Control: every message is aligned and inside π.** -/
theorem fsMsgs_aligned : fsMsgs.all msgOk = true := by decide +kernel

/-- Control: the seed's message is `hdr` (bytes `0 … 47`), position 2's is `cap₀` (the caps field
at offset `19,584`, `16,384` bytes; `capOff`). -/
theorem fsMsgs_ctl : fsMsgs.getD 0 none = some (0, 48) ∧ fsMsgs.getD 2 none = some (19584, 16384) ∧
    fsMsgs.getD 3 none = none := by decide +kernel

/-- **The query at Fiat–Shamir position `p`**, the previous answer being `st` (A.2). -/
def fsQ (vk c : Digest) (π : Proof) (p : ℕ) (st : Digest) : ByteArray :=
  match fsMsgs.getD p none with
  | some (o, len) => if p = 0 then seedQ vk c (π.extract o (o + len))
      else absorbQ st (π.extract o (o + len))
  | none => squeezeQ st

/-- The positions replayed: through P1.4's last round (`phStart 45 + 2·4`). -/
def nRep : ℕ := 442

/-- Control: P1.4 (phase 46) starts at Fiat–Shamir position 434 and has 4 rounds (8 items), so
`nRep = 434 + 8`: every P1.i challenge (`sAt es i l`, position `phStart (26 + 5i) + 2l + 1`) sits
below `nRep`. -/
theorem nRep_ctl : ((phases.take 46).map fun p => (p.shape.items.filter Item.isFS).length).sum = 434 ∧
    ((phases.getD 46 finalPhase).shape.items.filter Item.isFS).length = 8 ∧ 434 + 8 = nRep := by
  decide +kernel

theorem stateIn_fsQ (vk c : Digest) (π : Proof) {p : ℕ} (hp : 0 < p) (st : Digest) :
    stateIn (fsQ vk c π p st) = some st := by
  unfold fsQ
  split
  · rw [if_neg (by omega)]; exact stateIn_absorbQ st _
  · exact stateIn_squeezeQ st

/-! ## The table -/

/-- The tag words. -/
def tagAbsW : Word := toWord (ofLE tagAbs)
/-- The squeeze tag word. -/
def tagSqzW : Word := toWord (ofLE tagSqz)

/-- One table entry: `tl`, the tape offset of the message, the tag word, `0`. -/
def tabEnt (p : ℕ) : List Word :=
  match fsMsgs.getD p none with
  | some (o, len) => [toWord (40 + len), toWord (5 + o / 8), tagAbsW, 0]
  | none => [toWord 40, 0, tagSqzW, 0]

/-- **The table**: entries `0 … nRep`. -/
def chTab : List Word := (List.range (nRep + 1)).flatMap tabEnt

theorem tabEnt_length (p : ℕ) : (tabEnt p).length = 4 := by
  unfold tabEnt; split <;> rfl

theorem getD_flatMap4 (f : ℕ → List Word) (hf : ∀ p, (f p).length = 4) :
    ∀ (n p k : ℕ), p < n → k < 4 → ((List.range n).flatMap f).getD (4 * p + k) 0 = (f p).getD k 0
  | 0, p, _, hp, _ => absurd hp (Nat.not_lt_zero _)
  | n + 1, p, k, hp, hk => by
    rw [List.range_succ, List.flatMap_append, List.flatMap_singleton]
    have hl : ((List.range n).flatMap f).length = 4 * n := by
      rw [List.length_flatMap]
      simp only [hf, List.map_const', List.length_range, List.sum_replicate, smul_eq_mul]; ring
    rcases Nat.lt_succ_iff_lt_or_eq.mp hp with h | rfl
    · rw [List.getD_append _ _ _ _ (by omega), getD_flatMap4 f hf n p k h hk]
    · rw [List.getD_append_right _ _ _ _ (by omega), hl, Nat.add_sub_cancel_left]

theorem chTab_length : chTab.length = 4 * (nRep + 1) := by
  rw [chTab, List.length_flatMap]
  simp only [tabEnt_length, List.map_const', List.length_range, List.sum_replicate, smul_eq_mul]
  ring

theorem chTab_getD {p k : ℕ} (hp : p ≤ nRep) (hk : k < 4) :
    chTab.getD (4 * p + k) 0 = (tabEnt p).getD k 0 :=
  getD_flatMap4 tabEnt tabEnt_length _ p k (by omega) hk

/-! ## Packed words of the queries -/

theorem packBytes_append8 (a b : List UInt8) {k : ℕ} (ha : a.length = 8 * k) (j : ℕ) :
    (packBytes (a ++ b)).getD j 0 =
      if j < k then (packBytes a).getD j 0 else (packBytes b).getD (j - k) 0 := by
  split_ifs with hj
  · rw [← packBytes_take8 (a ++ b) hj, List.take_left' ha]
  · have := packBytes_drop8 (a ++ b) k (j - k)
    rw [List.drop_left' ha, show k + (j - k) = j by omega] at this
    exact this.symm

theorem tag_word (t l : List UInt8) (ht : t.length = 8) :
    (packBytes (t ++ l)).getD 0 0 = toWord (ofLE t) := by
  rw [packBytes_getD0 _ (by simp; omega), List.take_left' ht]

theorem absorb_words (st : Digest) (msg : ByteArray) (j : ℕ) :
    (packBytes (absorbQ st msg).data.toList).getD j 0 =
      if j < 5 then (if j = 0 then tagAbsW else (packBytes st.toList).getD (j - 1) 0)
      else (packBytes msg.data.toList).getD (j - 5) 0 := by
  rw [absorbQ_data, packBytes_append8 _ _ (k := 5) (by simp [tagAbs])]
  split_ifs with h5 h0
  · subst h0; exact tag_word _ _ rfl
  · rw [packBytes_append8 _ _ (k := 1) (by rfl), if_neg (by omega)]
  · rfl

theorem squeeze_words (st : Digest) {j : ℕ} (hj : j < 5) :
    (packBytes (squeezeQ st).data.toList).getD j 0 =
      if j = 0 then tagSqzW else (packBytes st.toList).getD (j - 1) 0 := by
  rw [squeezeQ_data, packBytes_append8 _ _ (k := 1) rfl]
  by_cases h0 : j = 0
  · subst h0
    rw [if_pos (by omega), if_pos rfl, packBytes_getD0 _ (by simp [tagSqz])]
    rfl
  · rw [if_neg (by omega), if_neg h0]

/-- An aligned message's packed words are π's. -/
theorem extract_words (π : Proof) {a n : ℕ} (h : 8 * a + 8 * n ≤ π.size) {j : ℕ} (hj : j < n) :
    (packBytes (π.extract (8 * a) (8 * a + 8 * n)).data.toList).getD j 0 =
      (packBytes π.data.toList).getD (a + j) 0 := by
  rw [ByteArray.data_extract, Array.toList_extract, List.extract_eq_take_drop,
    show 8 * a + 8 * n - 8 * a = 8 * n by omega, packBytes_take8 _ hj, packBytes_drop8]

theorem extract_size (π : Proof) {o len : ℕ} (h : o + len ≤ π.size) :
    (π.extract o (o + len)).size = len := by
  rw [ByteArray.size_extract]; omega

/-! ## The table realises the targets -/

theorem msgOk_of {p o len : ℕ} (h : fsMsgs.getD p none = some (o, len)) :
    o % 8 = 0 ∧ len % 8 = 0 ∧ o + len ≤ 797904 := by
  have hp : p < fsMsgs.length := by
    by_contra hc
    rw [List.getD_eq_default _ _ (by omega)] at h; cases h
  have hm := List.all_eq_true.mp fsMsgs_aligned _ (List.getElem_mem hp)
  rw [List.getD_eq_getElem _ _ hp] at h
  rw [h] at hm
  simp only [msgOk, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at hm
  exact ⟨hm.1.1, hm.1.2, hm.2⟩

/-- **The table realises Flock's targets** on every tape of a proof of `piSize` bytes. -/
theorem tabW_chTab (vk c : Digest) (π : Proof) (L : Log) (hs : π.size = piSize) :
    TabW (extractorInput c π L).toArray (fsQ vk c π) nRep chTab := by
  have hp : π.size = 797904 := hs.trans piSize_eq
  refine ⟨chTab_length, fun p hp0 hpN => ⟨?_, fun hpN' st => ?_⟩⟩
  · rw [show 4 * p + 1 = 4 * p + 1 from rfl, chTab_getD hpN (by norm_num), tabEnt]
    split
    · next o len h =>
      have := msgOk_of h
      show (toWord (5 + o / 8)).toNat < 2 ^ 62
      rw [toNat_toWord (by omega)]; omega
    · show (0 : Word).toNat < 2 ^ 62; decide
  · have e0 := chTab_getD hpN (k := 0) (by norm_num)
    have e1 := chTab_getD hpN (k := 1) (by norm_num)
    have e2 := chTab_getD hpN (k := 2) (by norm_num)
    rw [Nat.add_zero] at e0
    rw [e0, e1, e2]
    unfold fsQ tabEnt
    split
    · next o len h =>
      obtain ⟨ho, hl, hol⟩ := msgOk_of h
      rw [if_neg (by omega)]
      have hsz := extract_size π (o := o) (len := len) (by omega)
      refine ⟨by rw [absorbQ_size, hsz]; rfl, by rw [absorbQ_size, hsz]; omega, fun j hj => ?_⟩
      rw [absorbQ_size, hsz] at hj
      rw [absorb_words]
      show _ = if j < 5 then (if j = 0 then tagAbsW else _) else
        (extractorInput c π L).toArray.getD ((toWord (5 + o / 8)).toNat + (j - 5)) 0
      split_ifs with h5 h0
      · rfl
      · rfl
      · rw [toNat_toWord (by omega), getD_toArray, show 5 + o / 8 + (j - 5) = 5 + (o / 8 + (j - 5))
          by omega, tape_getD_proof c π L (by rw [hp]; omega), ← List.getD_eq_getElem _ 0,
          show o = 8 * (o / 8) by omega, show 8 * (o / 8) + len = 8 * (o / 8) + 8 * (len / 8) by
          omega, extract_words π (by omega) (by omega), show 8 * (o / 8) / 8 = o / 8 by omega]
    · refine ⟨by rw [squeezeQ_size]; rfl, by rw [squeezeQ_size]; norm_num, fun j hj => ?_⟩
      rw [squeezeQ_size] at hj
      rw [squeeze_words st (by omega), if_pos (show j < 5 by omega)]
      rfl

/-! ## The specification -/

/-- **`chain_spec`**: on a domain tape of a SNARK proof whose log has no state hit, for every
position `p < nRep` that the first-match chain answers with `a`, the machine's answer at
`ansB + 4p` is `a`'s four words. The seed block `sd` must write the seed's words (`SeedOK`). -/
theorem chain_spec (vk c : Digest) (π : Proof) (L : Log) (hs : π.size = piSize)
    (hq : ∀ e ∈ L, e.1.size < 2 ^ 64) (ht : (extractorInput c π L).length ≤ 2 ^ 64)
    (hS : ¬ StateHit L) {sd : XIR}
    (hsd : SeedOK sd (extractorInput c π L).toArray (fsQ vk c π 0 zeroD))
    (s : St) (hM : Inv s.M) (hsz : chEnd ≤ s.M.size) {p : ℕ} (hp : p < nRep) {a : Digest}
    (ha : fmAns (fsQ vk c π) zeroD L p = some a) {m : ℕ} (hm : m < 4) :
    rd (semXIR (extractorInput c π L).toArray (chainIR posL nRep chTab sd) s).M (ansB + 4 * p + m) =
      (packBytes a.toList).getD m 0 := by
  have h119 : (fsQ vk c π 0 zeroD).size = 119 := by
    have hp' : π.size = 797904 := hs.trans piSize_eq
    unfold fsQ
    rw [fsMsgs_ctl.1]
    simp only [if_true]
    rw [seedQ, ByteArray.size_append, extract_size π (by omega),
      show (bytesOf (tagSeed ++ vk.toList ++ c.toList)).size = 71 by
        simp [bytesOf, ByteArray.size, tagSeed]]
  obtain ⟨-, hans, -⟩ := chainIR_sem c π L (hs_posL hs) hq ht (N := nRep) (by decide)
    (tabW_chTab vk c π L hs) hsd h119 s hM hsz
  have hsc := scanC_answers (N := nRep) (st₀ := zeroD) (fun p st hp => stateIn_fsQ vk c π hp st)
    hS hp
  rw [ha] at hsc
  have hlen := (scanC_fm (N := nRep) (st₀ := zeroD) (L := L) (T := fsQ vk c π)
    (fun p st hp => stateIn_fsQ vk c π hp st) hS).1
  have hpl : p < (scanC (fsQ vk c π) nRep zeroD L).1 := by
    rw [← hlen]; exact (List.getElem?_eq_some_iff.mp hsc).1
  have hg : (scanC (fsQ vk c π) nRep zeroD L).2.2.getD p default = a := by
    rw [List.getD_eq_getElem?_getD, hsc, Option.getD_some]
  rw [hans p hpl m hm, hg]

end FR.X
