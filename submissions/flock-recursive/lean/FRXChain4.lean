-- New for `flock-recursive` (BLUEPRINT revision 4.1, §6.2 step 2, A.4; stage S-H4, pass 6, item 2).
import FRXDec
import FRXLevel
import FRVIR4
import FRSoundness4TailTruths

/-!
# The chain scan at revision 4.1: the targets of an item sequence, the table, `chain_spec4`

3.x's `FRXChainFlock` with the item sequence a parameter `S : Seq` (rev44's `seq4` has 486
Fiat–Shamir items; another revision's sequence is another `S`):

* `fsMsgs4 S`: per Fiat–Shamir position, the π byte range `(o, len)` of the absorbed message, read
  off `phasesOf S` exactly as `FRVIR4.genPhase4` asks (`fieldOffOf S f + phaseOffOf S n f`,
  `j · roundBytes` per round); `none` for a squeeze. Controls at `seq4`: `fsMsgs4_items` (the kinds
  and lengths are `fsItems4`), `fsMsgs4_aligned` (8-byte aligned inside `piSizeOf seq4`).
* `fsQ4 S vk c π p st`: the query at position `p` (A.2); position 0 is the seed
  `seedQ vk c hdr` (`fsQ4_zero`).
* `chTab4 S N`, **`tabW_chTab4`**: the table realises `fsQ4 S` on every tape of a proof of
  `piSizeOf S` bytes whose messages are aligned (`hA`, a decided check per sequence).
* **`chain_spec4`**: on a log with no state hit, the answer at `ansB + 4p` (`p < N`) is the
  first-match chain's (`fmAns`); **`chain_dec4`** for the seed block `seedIR` (`vkOf π`).
* At `seq4`: `nRep4 = 456` (through P1.4's last round, `phStart4 47`), the P1 challenges' words
  **`cbS4 i`** and **`sAt4_words`** (they hold `T4.sAt es i`).
-/

namespace FR.X

open RecursionFast FR.Snd FR.Rev4

/-! ## The Fiat–Shamir messages of an item sequence -/

/-- A phase's Fiat–Shamir positions in `S`'s format: the absorbed π range, or `none` for a squeeze. -/
def phaseMsgs4 (S : Seq) (n : ℕ) : Sh → List (Option (ℕ × ℕ))
  | .seed => [some (0, 48)]
  | .absorb f len => [some (fieldOffOf S f + phaseOffOf S n f, len)]
  | .squeezes k _ => List.replicate k none
  | .uni f => [some (fieldOffOf S f + phaseOffOf S n f, uniBytes), none]
  | .rounds f k _ inK => (List.range k).flatMap fun j =>
      [some (fieldOffOf S f + phaseOffOf S n f + j * roundBytes inK, roundBytes inK), none]
  | .queries _ => []

/-- **The Fiat–Shamir messages of `S`** in item order. -/
def fsMsgs4 (S : Seq) : List (Option (ℕ × ℕ)) :=
  ((List.range (phasesOf S).length).zip (phasesOf S)).flatMap fun np => phaseMsgs4 S np.1 np.2.2

/-- A message is 8-byte aligned and inside a proof of `P` bytes. -/
def msgOkB (P : ℕ) : Option (ℕ × ℕ) → Bool
  | some (o, len) => o % 8 == 0 && len % 8 == 0 && decide (o + len ≤ P)
  | none => true

/-- Position 0 is the seed's `hdr` (bytes `0 … 47`), in every sequence. -/
theorem fsMsgs4_zero (S : Seq) : (fsMsgs4 S).getD 0 none = some (0, 48) := by
  have h : (phasesOf S).length = (phasesOf S).length - 1 + 1 := by simp [phasesOf]
  unfold fsMsgs4; rw [h, List.range_succ_eq_map]; rfl

/-- **The query at Fiat–Shamir position `p`** of `S`, the previous answer being `st` (A.2). -/
def fsQ4 (S : Seq) (vk c : Digest) (π : Proof) (p : ℕ) (st : Digest) : ByteArray :=
  match (fsMsgs4 S).getD p none with
  | some (o, len) => if p = 0 then seedQ vk c (π.extract o (o + len))
      else absorbQ st (π.extract o (o + len))
  | none => squeezeQ st

theorem fsQ4_zero (S : Seq) (vk c : Digest) (π : Proof) (st : Digest) :
    fsQ4 S vk c π 0 st = seedQ vk c (π.extract 0 48) := by
  unfold fsQ4; rw [fsMsgs4_zero]; rfl

theorem stateIn_fsQ4 (S : Seq) (vk c : Digest) (π : Proof) {p : ℕ} (hp : 0 < p) (st : Digest) :
    stateIn (fsQ4 S vk c π p st) = some st := by
  unfold fsQ4
  split
  · rw [if_neg (by omega)]; exact stateIn_absorbQ st _
  · exact stateIn_squeezeQ st

/-! ## The table -/

/-- One table entry of the message list `ms`: `tl`, the tape offset of the message, the tag word, `0`. -/
def tabEntM (ms : List (Option (ℕ × ℕ))) (p : ℕ) : List Word :=
  match ms.getD p none with
  | some (o, len) => [toWord (40 + len), toWord (5 + o / 8), tagAbsW, 0]
  | none => [toWord 40, 0, tagSqzW, 0]

/-- One table entry of `S` (`tabEntM` at `fsMsgs4 S`). -/
def tabEnt4 (S : Seq) (p : ℕ) : List Word := tabEntM (fsMsgs4 S) p

/-- **The table** of `S`: entries `0 … N` (`= (List.range (N + 1)).flatMap (tabEnt4 S)`, `chTab4_eq`;
written with `fsMsgs4 S` outside the entries so the compiled table computes it once: INIT, 7 s of
the badge's start-up). -/
def chTab4 (S : Seq) (N : ℕ) : List Word := (List.range (N + 1)).flatMap (tabEntM (fsMsgs4 S))

theorem chTab4_eq (S : Seq) (N : ℕ) : chTab4 S N = (List.range (N + 1)).flatMap (tabEnt4 S) := rfl

theorem tabEnt4_length (S : Seq) (p : ℕ) : (tabEnt4 S p).length = 4 := by
  unfold tabEnt4 tabEntM; split <;> rfl

theorem chTab4_length (S : Seq) (N : ℕ) : (chTab4 S N).length = 4 * (N + 1) := by
  rw [chTab4_eq, List.length_flatMap]
  simp only [tabEnt4_length, List.map_const', List.length_range, List.sum_replicate, smul_eq_mul]
  ring

theorem chTab4_getD (S : Seq) {N p k : ℕ} (hp : p ≤ N) (hk : k < 4) :
    (chTab4 S N).getD (4 * p + k) 0 = (tabEnt4 S p).getD k 0 :=
  getD_flatMap4 (tabEnt4 S) (tabEnt4_length S) _ p k (by omega) hk

theorem msgOkB_of {S : Seq} {P p o len : ℕ} (hA : (fsMsgs4 S).all (msgOkB P) = true)
    (h : (fsMsgs4 S).getD p none = some (o, len)) : o % 8 = 0 ∧ len % 8 = 0 ∧ o + len ≤ P := by
  have hp : p < (fsMsgs4 S).length := by
    by_contra hc
    rw [List.getD_eq_default _ _ (by omega)] at h; cases h
  have hm := List.all_eq_true.mp hA _ (List.getElem_mem hp)
  rw [List.getD_eq_getElem _ _ hp] at h
  rw [h] at hm
  simp only [msgOkB, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at hm
  exact ⟨hm.1.1, hm.1.2, hm.2⟩

/-- **The table realises `S`'s targets** on every tape of a proof inside which every message of
`S` lies 8-byte aligned (`hA`). -/
theorem tabW_chTab4 (S : Seq) (N : ℕ) (vk c : Digest) (π : Proof) (L : Log) (hπ : π.size < 2 ^ 60)
    (hA : (fsMsgs4 S).all (msgOkB π.size) = true) :
    TabW (extractorInput c π L).toArray (fsQ4 S vk c π) N (chTab4 S N) := by
  refine ⟨chTab4_length S N, fun p hp0 hpN => ⟨?_, fun hpN' st => ?_⟩⟩
  · rw [chTab4_getD S hpN (by norm_num), tabEnt4, tabEntM]
    split
    · next o len h =>
      have := msgOkB_of hA h
      show (toWord (5 + o / 8)).toNat < 2 ^ 62
      rw [toNat_toWord (by omega)]; omega
    · show (0 : Word).toNat < 2 ^ 62; decide
  · have e0 := chTab4_getD S hpN (k := 0) (by norm_num)
    have e1 := chTab4_getD S hpN (k := 1) (by norm_num)
    have e2 := chTab4_getD S hpN (k := 2) (by norm_num)
    rw [Nat.add_zero] at e0
    rw [e0, e1, e2]
    unfold fsQ4 tabEnt4 tabEntM
    split
    · next o len h =>
      obtain ⟨ho, hl, hol⟩ := msgOkB_of hA h
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
          by omega, tape_getD_proof c π L (by omega), ← List.getD_eq_getElem _ 0,
          show o = 8 * (o / 8) by omega, show 8 * (o / 8) + len = 8 * (o / 8) + 8 * (len / 8) by
          omega, extract_words π (by omega) (by omega), show 8 * (o / 8) / 8 = o / 8 by omega]
    · refine ⟨by rw [squeezeQ_size]; rfl, by rw [squeezeQ_size]; norm_num, fun j hj => ?_⟩
      rw [squeezeQ_size] at hj
      rw [squeeze_words st (by omega), if_pos (show j < 5 by omega)]
      rfl

/-! ## The specification -/

/-- The seed query is 119 bytes. -/
theorem seedQ_size (vk c : Digest) (π : Proof) (h48 : 48 ≤ π.size) :
    (seedQ vk c (π.extract 0 48)).size = 119 := by
  rw [seedQ, ByteArray.size_append, extract_size π (o := 0) (len := 48) (by omega),
    show (bytesOf (tagSeed ++ vk.toList ++ c.toList)).size = 71 by
      simp [bytesOf, ByteArray.size, tagSeed]]

/-- **`chain_spec4`**: on a domain tape of a proof inside which `S`'s messages lie aligned, whose
log has no state hit, for every position `p < N` that the first-match chain of `S`'s targets
answers with `a`, the machine's answer at `ansB + 4p` is `a`'s four words; the chain keeps the
heap outside `[chB, chEnd)`. The seed block `sd` must write the seed's words (`SeedOK`). -/
theorem chain_spec4 (S : Seq) {pL N : ℕ} (hN : N < 2 ^ 9) (vk c : Digest) (π : Proof) (L : Log)
    (hs : 5 + (π.size + 7) / 8 = pL) (h48 : 48 ≤ π.size) (hπ : π.size < 2 ^ 60)
    (hA : (fsMsgs4 S).all (msgOkB π.size) = true)
    (hq : ∀ e ∈ L, e.1.size < 2 ^ 64) (ht : (extractorInput c π L).length ≤ 2 ^ 64)
    (hS : ¬ StateHit L) {sd : XIR} {st₀ : Digest}
    (hsd : SeedOK sd (extractorInput c π L).toArray (fsQ4 S vk c π 0 st₀))
    (s : St) (hM : Inv s.M) (hsz : chEnd ≤ s.M.size) :
    (∀ p < N, ∀ a, fmAns (fsQ4 S vk c π) st₀ L p = some a → ∀ m < 4,
      rd (semXIR (extractorInput c π L).toArray (chainIR pL N (chTab4 S N) sd) s).M (ansB + 4 * p + m) =
        (packBytes a.toList).getD m 0) ∧
    (∀ y, regs ≤ y → (y < chB ∨ chEnd ≤ y) →
      rd (semXIR (extractorInput c π L).toArray (chainIR pL N (chTab4 S N) sd) s).M y = rd s.M y) := by
  have h119 : (fsQ4 S vk c π 0 st₀).size = 119 := by rw [fsQ4_zero]; exact seedQ_size vk c π h48
  obtain ⟨-, hans, hfr⟩ := chainIR_sem c π L hs hq ht hN (tabW_chTab4 S N vk c π L hπ hA) hsd h119
    s hM hsz
  refine ⟨fun p hp a ha m hm => ?_, hfr⟩
  have hsc := scanC_answers (N := N) (st₀ := st₀) (fun p st hp => stateIn_fsQ4 S vk c π hp st)
    hS hp
  rw [ha] at hsc
  have hlen := (scanC_fm (N := N) (st₀ := st₀) (L := L) (T := fsQ4 S vk c π)
    (fun p st hp => stateIn_fsQ4 S vk c π hp st) hS).1
  have hpl : p < (scanC (fsQ4 S vk c π) N st₀ L).1 := by
    rw [← hlen]; exact (List.getElem?_eq_some_iff.mp hsc).1
  have hg : (scanC (fsQ4 S vk c π) N st₀ L).2.2.getD p default = a := by
    rw [List.getD_eq_getElem?_getD, hsc, Option.getD_some]
  rw [hans p hpl m hm, hg]

/-- **The replayed answers for the seed block** `seedIR`: the first-match chain from the seed
`"FRSEED0" ‖ vkOf π ‖ c ‖ hdr`. -/
theorem chain_dec4 (S : Seq) {pL N : ℕ} (hN : N < 2 ^ 9) (c : Digest) (π : Proof) (L : Log)
    (hs : 5 + (π.size + 7) / 8 = pL) (h48 : 48 ≤ π.size) (hπ : π.size < 2 ^ 60)
    (hA : (fsMsgs4 S).all (msgOkB π.size) = true)
    (hq : ∀ e ∈ L, e.1.size < 2 ^ 64) (ht : (extractorInput c π L).length ≤ 2 ^ 64)
    (hS : ¬ StateHit L) (st₀ : Digest) (s : St) (hM : Inv s.M) (hsz : chEnd ≤ s.M.size) :
    (∀ p < N, ∀ a, fmAns (fsQ4 S (vkOf π) c π) st₀ L p = some a → ∀ m < 4,
      rd (semXIR (extractorInput c π L).toArray (chainIR pL N (chTab4 S N) seedIR) s).M
        (ansB + 4 * p + m) = (packBytes a.toList).getD m 0) ∧
    (∀ y, regs ≤ y → (y < chB ∨ chEnd ≤ y) →
      rd (semXIR (extractorInput c π L).toArray (chainIR pL N (chTab4 S N) seedIR) s).M y = rd s.M y) :=
  chain_spec4 S hN (vkOf π) c π L hs h48 hπ hA hq ht hS
    (by rw [fsQ4_zero]; exact seedOK_seedIR4 c π L h48) s hM hsz

/-! ## At `seq4`: the controls, the positions replayed, the P1 challenges -/

/-- Control: `seq4` has 486 Fiat–Shamir positions (revision 4.4.1: the cap check's four after `Pf`). -/
theorem fsMsgs4_length : (fsMsgs4 seq4).length = 486 := by decide +kernel

/-- The item kind of a message entry (position `0` is the seed). -/
def msgItem4 : ℕ → Option (ℕ × ℕ) → Item
  | 0, _ => .seed
  | _ + 1, some (_, len) => .absorb len
  | _ + 1, none => .squeeze

/-- **Control: the kinds and lengths are `seq4`'s Fiat–Shamir items** (`T4.fsItems4`). -/
theorem fsMsgs4_items :
    (List.range 486).map (fun p => msgItem4 p ((fsMsgs4 seq4).getD p none)) = fsItems4 := by
  rw [← fsMsgs4_length, map_range_getD]; decide +kernel

/-- **Control: every message of `seq4` is aligned and inside a proof of `piSizeOf seq4` bytes.** -/
theorem fsMsgs4_aligned : (fsMsgs4 seq4).all (msgOkB (piSizeOf seq4)) = true := by
  rw [piSizeOf_seq4, seq4_eq]; decide +kernel

/-- The positions replayed at `seq4`: through P1.4's last round. -/
def nRep4 : ℕ := 456

/-- Control: P1.4 (phase 46) starts at position 448 and has 4 rounds (8 items), and the final
message's absorb (phase 47) is at `nRep4`: every P1.i challenge (`T4.sAt es i l`, position
`phStart4 (26 + 5i) + 2l + 1`, `l < 4` for `i ≥ 1`, `l < 6` for `i = 0`) sits below `nRep4`. -/
theorem nRep4_ctl : phStart4 46 = 448 ∧ phStart4 47 = nRep4 ∧
    (List.range 5).map (fun i => phStart4 (26 + 5 * i)) = [332, 375, 402, 426, 448] := by
  simp only [phStart4, fsStarts4_eq, nRep4]; decide

/-- **The P1.i challenges' words** in the chain's answers: `ansB + 4 (phStart4 (26 + 5i) + 1)`. -/
def cbS4 (i : ℕ) : ℕ := ansB + 4 * (phStart4 (26 + 5 * i) + 1)

/-- The challenges' words are `T4.sAt` (3.x's `sAt_words` at `phStart4`). -/
theorem sAt4_words {M : Mem} {es : Log} {i ℓ : ℕ}
    (h : ∀ v < ℓ, ∀ m < 4, rd M (ansB + 4 * (phStart4 (26 + 5 * i) + 2 * v + 1) + m) =
      (packBytes (ansAt es (phStart4 (26 + 5 * i) + 2 * v + 1)).toList).getD m 0) :
    ∀ v < ℓ, rdK M (cbS4 i + 8 * v) = T4.sAt es i v := by
  intro v hv
  rw [T4.sAt, kAt]
  refine rdK_of_words fun m hm => ?_
  rw [← h v hv m hm, cbS4]
  congr 1
  ring

/-- The challenges' region at every level: inside the answers, above the basis table, below the
levels' regions (`map4`'s `fb = 2^24`), and their positions below `nRep4`. -/
theorem cbS4_bounds {i : ℕ} (hi : i < 5) {ℓ : ℕ} (hℓ : ℓ ≤ (if i = 0 then 6 else 4)) :
    2 ^ 20 + 800 ≤ cbS4 i ∧ cbS4 i + 8 * ℓ + 4 ≤ chEnd ∧ phStart4 (26 + 5 * i) + 2 * ℓ ≤ nRep4 := by
  have e := nRep4_ctl.2.2
  simp only [List.map, List.range_succ, List.range_zero, List.nil_append, List.cons_append,
    List.cons.injEq] at e
  obtain ⟨e0, e1, e2, e3, e4, -⟩ := e
  simp only [cbS4, ansB, chEnd, nRep4]
  interval_cases i <;> simp_all <;> omega

/-! ## Controls -/

/-- (−) **`msgOkB` rejects** a misaligned message and one past the proof's end; (+) it accepts the
seed's `hdr`. -/
theorem msgOkB_ctl : msgOkB 876304 (some (4, 8)) = false ∧ msgOkB 100 (some (96, 8)) = false ∧
    msgOkB 876304 (some (0, 48)) = true := by decide

/-- (value) **`seq4`'s targets at positions 2 and 3**: `cap₀`'s absorb of π's bytes
`20,896 … + 16,384`, then a squeeze (`Z1`'s first). -/
theorem fsMsgs4_ctl : (fsMsgs4 seq4).getD 2 none = some (20896, 16384) ∧
    (fsMsgs4 seq4).getD 3 none = none := by
  rw [seq4_eq]; decide +kernel

/-- (+/−) **The queries**: position 2 absorbs `cap₀` into the state, position 3 squeezes it (and
is not an absorb). -/
theorem fsQ4_ctl (vk c : Digest) (π : Proof) (st : Digest) :
    fsQ4 seq4 vk c π 2 st = absorbQ st (π.extract 20896 (20896 + 16384)) ∧
    fsQ4 seq4 vk c π 3 st = squeezeQ st := by
  constructor <;> unfold fsQ4 <;> simp only [fsMsgs4_ctl] <;> rfl

/-- (value) **The table's entry for `cap₀`**: the query length `40 + 16,384`, the tape word
`5 + 20,896/8`, the absorb tag. -/
theorem tabEnt4_ctl : tabEnt4 seq4 2 = [toWord (40 + 16384), toWord (5 + 20896 / 8), tagAbsW, 0] := by
  unfold tabEnt4 tabEntM; simp only [fsMsgs4_ctl]

/-- (value/−) **The P1 challenges' words** per level; they differ between levels. -/
theorem cbS4_ctl : (List.range 5).map cbS4 = [ansB + 1332, ansB + 1504, ansB + 1612, ansB + 1708,
    ansB + 1796] ∧ cbS4 4 ≠ cbS4 3 := by
  simp only [cbS4, phStart4, fsStarts4_eq]; decide +kernel

end FR.X
