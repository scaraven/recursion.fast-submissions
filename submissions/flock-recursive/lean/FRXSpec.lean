-- New for `flock-recursive` (BLUEPRINT §6.5, §5.4; stage S-H2, track L-ext).
import FRXExt

/-!
# What `ext` outputs: the `W` and `bad` cases of `ext_good_tape`

BLUEPRINT §6.5, §5.4 ("`W` is `Rel` by definition and `E` copies the proof (§6.2, any size)").

* `parse_isK`: the parse's kind flag is `kindFlag` of tape word 5, which is `0` exactly when the
  word's low byte is not a kind byte (`kindFlag_eq_zero`);
* **`E_W`**: on a proof of the `W` kind (`kindOf π = .W`, `FRFormat`) of fewer than `2^64` bytes,
  `Eden … c π L = WitnessSending.decode π`, for every SNARK branch with `DecOk`, **on every log**
  (no domain hypothesis): the program halts within `fuel` on every such tape, and its output is
  the denotation (`den_of_run`);
* **`ext_W`** (B-15): `E A c π L = WitnessSending.decode π` on **every** `W` proof and log: `E_W`
  on the domain, `Eout`'s `W` branch outside it (proofs above `8 · outCap` bytes included);
* **`E_bad`**: on a kind byte with `|π| ≠ piSize` (`kindOf π = .bad`), `Eden … c π L = none` (no
  output; the negative control: an ill-formed tape halts within the fuel); `ext_bad` for `E`.

The SNARK case (`kindOf π = .snark k`) is the decoder's (§6.2 steps 2–5), not delivered here.
-/

namespace FR.X

open RecursionFast

/-- The parse's kind flag: `1` if the low byte of `w` is `'L'`, `'P'` or `'N'`, else `0`. -/
def kindFlag (w : Word) : Word :=
  ((if w &&& 0xFF = 0x4C then 1 else 0) ||| (if w &&& 0xFF = 0x50 then 1 else 0)) |||
    (if w &&& 0xFF = 0x4E then 1 else 0)

theorem parse_isK (I : Array Word) (s : St) (hM : Inv s.M) :
    rd (semXIR I parseIR s).M rIsK = kindFlag (I.getD 5 0) := by
  have hs := hM.1
  simp only [regs] at hs
  simp only [parseIR, readAt, kindPs, semXIR, runPrims, List.foldl, Prim.run, rA, rLen, rK, rB0,
    rIsK, rT, rIsSz]
  simp (disch := first | decide | omega | (simp only [size_set]; omega))
    [rd_set_self, rd_set_ne, XOp.eval, kindFlag]

theorem kindFlag_eq_zero (w : Word) :
    kindFlag w = 0 ↔ (w &&& 0xFF ≠ 0x4C ∧ w &&& 0xFF ≠ 0x50 ∧ w &&& 0xFF ≠ 0x4E) := by
  unfold kindFlag
  by_cases h1 : w &&& 0xFF = 0x4C <;> by_cases h2 : w &&& 0xFF = 0x50 <;>
    by_cases h3 : w &&& 0xFF = 0x4E <;> simp_all <;> decide

/-- The low byte of a word. -/
theorem lowByte (w : Word) : (w &&& 0xFF).toNat = w.toNat % 256 := by
  rw [BitVec.toNat_and, show (0xFF : Word).toNat = 2 ^ 8 - 1 from rfl,
    Nat.and_two_pow_sub_one_eq_mod]

theorem toNat_toUInt8 (n : ℕ) : n.toUInt8.toNat = n % 256 := by
  rw [Nat.toUInt8_eq, UInt8.toNat_ofNat']

/-- The low byte of tape word 5 is the proof's first byte. -/
theorem tape_byte0 (c : Digest) (π : Proof) (L : Log) {b : UInt8} (h0 : π.data[0]? = some b) :
    ((extractorInput c π L).getD 5 0).toNat.toUInt8 = b := by
  have hpos : 0 < π.size := by
    rcases Nat.eq_zero_or_pos π.size with h | h
    · simp [ByteArray.size, Array.size_eq_zero_iff.mp h] at h0
    · exact h
  have := tape_getD_proof c π L (j := 0) (by omega)
  rw [Nat.add_zero] at this
  rw [this]
  have hw := wordByte_packBytes π.data.toList 0
  simp only [wordByte, Nat.zero_div, Nat.zero_mod, pow_zero, Nat.div_one] at hw
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by
    rw [packBytes_length, ← WitnessSending.size_eq_length]; omega), Option.getD_some] at hw
  rw [hw, List.getD_eq_getElem?_getD, Array.getElem?_toList, h0, Option.getD_some]

/-- A first byte that is a kind byte, as `kindFlag` sees it. -/
theorem kindFlag_byte (w : Word) :
    kindFlag w = 0 ↔ Kind.ofByte? w.toNat.toUInt8 = none := by
  have A : ∀ v : Word, v.toNat < 256 → (w &&& 0xFF = v ↔ w.toNat % 256 = v.toNat) :=
    fun v _ => by rw [← BitVec.toNat_inj, lowByte]
  have B : ∀ u : UInt8, (w.toNat.toUInt8 = u ↔ w.toNat % 256 = u.toNat) := fun u => by
    rw [← UInt8.toNat_inj, toNat_toUInt8]
  rw [kindFlag_eq_zero]
  simp only [ne_eq]
  rw [A _ (by decide), A _ (by decide), A _ (by decide)]
  simp only [Kind.ofByte?, B, UInt8.reduceToNat]
  split_ifs <;> simp_all

/-! ## The run on a tape whose proof is not a SNARK proof -/

/-- **The run when the kind flag is clear or the length is not `piSize`**: on a tape whose word 4
is `a < 2^64` followed by `⌈a/8⌉` words, if `a ≠ 0` forces a clear kind flag, the program halts
within the fuel and outputs the `⌈a/8⌉` words from word 5. -/
theorem run_W_tape {dec : XIR} (hd : DecOk dec) (inp : List Word) (a : ℕ) (ha : a < 2 ^ 64)
    (h4 : inp.toArray.getD 4 0 = toWord a) (hlen : (a + 7) / 8 + 6 ≤ inp.length)
    (hk : a ≠ 0 → kindFlag (inp.toArray.getD 5 0) = 0) :
    (extWith dec).run inp (fuel inp.length) =
      some ((List.range ((a + 7) / 8)).map fun j => inp.toArray.getD (5 + j) 0) := by
  have hwf := wf_extIRWith hd.wf
  have hreg : regs ≤ memX := by simp only [regs, memX]; norm_num
  have h0 : Inv (initSt (memX + mpwX * inp.length)).M := inv_initSt (Nat.le_add_right_of_le hreg)
  generalize hs0 : initSt (memX + mpwX * inp.length) = s0 at h0
  generalize hI : inp.toArray = I at h4 hk ⊢
  have h1 : Inv (semXIR I parseIR s0).M := inv_sem I hwf.1 h0
  have hz0 : a = 0 → rd (semXIR I parseIR s0).M rIsSz = 0 := by
    intro h
    rw [parse_regs I s0 h0, h4, h, if_neg]
    intro he
    have := congrArg BitVec.toNat he
    rw [toNat_toWord (by omega), BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by rw [piSize_eq]; omega),
      piSize_eq] at this
    omega
  have hk' : a ≠ 0 → rd (semXIR I parseIR s0).M rIsK = 0 := fun h => by
    rw [parse_isK I s0 h0]; exact hk h
  have hpo : (semXIR I parseIR s0).o = #[] := by rw [parse_o, ← hs0, initSt_o]
  have hw : (ceil8 (I.getD 4 0)).toNat = (a + 7) / 8 := by rw [h4, toNat_ceil8 ha]
  generalize hs1 : semXIR I parseIR s0 = s1 at h1 hz0 hk' hpo
  have hB : BoundsOk I inp.length (extIRWith dec) s0 := by
    rw [extIRWith, boundsOk_seq]
    refine ⟨boundsOk_of_safe (safe_parseIR _ _) hwf.1 _ h0, ?_⟩
    rw [hs1, boundsOk_ite]
    by_cases hk1 : rd s1.M rIsK = 0
    · rw [if_pos hk1]
      exact boundsOk_of_safe (safe_wIR ha h4 (by omega)) hwf.2.2 _ h1
    · have ha0 : a = 0 := by by_contra h; exact hk1 (hk' h)
      rw [if_neg hk1, boundsOk_ite, if_pos (hz0 ha0)]; trivial
  have hrun := run_toProg (P := extIRWith dec) (input := inp) (f := fuel inp.length) hreg hwf
    (by rw [hs0, hI]; exact hB) (fuel_covers hd.cost _)
  rw [hs0, hI] at hrun
  refine hrun.trans (congrArg some ?_)
  by_cases hk1 : rd s1.M rIsK = 0
  · have e : semXIR I (extIRWith dec) s0 = semXIR I wIR s1 := by
      rw [extIRWith, semXIR_seq, hs1, semXIR_ite, if_pos hk1]
    rw [congrArg (fun s' : St => s'.o.toList) e, wIR_sem I _ h1 (by omega), hpo, hw]
    rfl
  · have ha0 : a = 0 := by by_contra h; exact hk1 (hk' h)
    have e : semXIR I (extIRWith dec) s0 = semXIR I (.blk []) s1 := by
      rw [extIRWith, semXIR_seq, hs1, semXIR_ite, if_neg hk1, semXIR_ite, if_pos (hz0 ha0)]
    rw [congrArg (fun s' : St => s'.o.toList) e, ha0]
    simp [semXIR, hpo]

/-- **The `W` case**: on a `W` proof of fewer than `2^64` bytes, any size above the contract's
domain `8 · outCap` included, the program outputs the proof's packed words within the fuel. -/
theorem run_W {dec : XIR} (hd : DecOk dec) (c : Digest) (π : Proof) (L : Log)
    (hW : kindOf π = .W) (hπ : π.size < 2 ^ 64) :
    (extWith dec).run (extractorInput c π L) (fuel (extractorInput c π L).length) =
      some (packBytes π.data.toList) := by
  rw [run_W_tape hd _ π.size hπ (by rw [getD_toArray, tape_getD4]) (tape_length c π L)]
  · congr 1
    refine List.ext_getElem (by
      simp only [List.length_map, List.length_range, packBytes_length]
      rw [WitnessSending.size_eq_length]) fun j _ h2 => ?_
    simp only [List.getElem_map, List.getElem_range, getD_toArray]
    exact tape_getD_proof c π L (by rwa [packBytes_length, ← WitnessSending.size_eq_length] at h2)
  · intro hne
    obtain ⟨b, hb⟩ : ∃ b, π.data[0]? = some b := by
      rcases h : π.data[0]? with _ | b
      · rw [Array.getElem?_eq_none_iff] at h; exact (hne (Nat.le_zero.mp h)).elim
      · exact ⟨b, rfl⟩
    rw [kindFlag_byte, getD_toArray, tape_byte0 c π L hb]
    simp only [kindOf, byteAt?_eq, hb, Option.bind_some] at hW
    revert hW; cases Kind.ofByte? b
    · intro; rfl
    · intro h; by_cases hs : π.size = piSize <;> simp [hs] at h

/-- **`E` on a `W` proof is `WitnessSending.decode`** (§5.4: "`E` copies the proof"). -/
theorem E_W {dec : XIR} (hd : DecOk dec) (c : Digest) (π : Proof) (L : Log)
    (hW : kindOf π = .W) (hπ : π.size < 2 ^ 64) :
    Eden memX mpwX (extIRWith dec) c π L = WitnessSending.decode π := by
  rw [Eden, ← den_of_run (by simp only [regs, memX]; norm_num) (wf_extIRWith hd.wf)
    (run_W hd c π L hW hπ)]
  rfl

/-- The run on a tape whose kind flag is set and whose word 4 is not `piSize`: no output. -/
theorem run_bad_tape {dec : XIR} (hd : DecOk dec) (inp : List Word) (a : ℕ) (ha : a < 2 ^ 64)
    (h4 : inp.toArray.getD 4 0 = toWord a) (hs : a ≠ piSize)
    (hk : kindFlag (inp.toArray.getD 5 0) ≠ 0) :
    (extWith dec).run inp (fuel inp.length) = some [] := by
  have hwf := wf_extIRWith hd.wf
  have hreg : regs ≤ memX := by simp only [regs, memX]; norm_num
  have h0 : Inv (initSt (memX + mpwX * inp.length)).M := inv_initSt (Nat.le_add_right_of_le hreg)
  generalize hs0 : initSt (memX + mpwX * inp.length) = s0 at h0
  generalize hI : inp.toArray = I at h4 hk ⊢
  have h1 : Inv (semXIR I parseIR s0).M := inv_sem I hwf.1 h0
  have hz : rd (semXIR I parseIR s0).M rIsSz = 0 := by
    rw [parse_regs I s0 h0, h4, if_neg]
    intro he
    have := congrArg BitVec.toNat he
    rw [toNat_toWord ha, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by rw [piSize_eq]; omega)] at this
    exact hs this
  have hk1 : rd (semXIR I parseIR s0).M rIsK ≠ 0 := by rw [parse_isK I s0 h0]; exact hk
  have hpo : (semXIR I parseIR s0).o = #[] := by rw [parse_o, ← hs0, initSt_o]
  generalize hs1 : semXIR I parseIR s0 = s1 at h1 hz hk1 hpo
  have hB : BoundsOk I inp.length (extIRWith dec) s0 := by
    rw [extIRWith, boundsOk_seq]
    refine ⟨boundsOk_of_safe (safe_parseIR _ _) hwf.1 _ h0, ?_⟩
    rw [hs1, boundsOk_ite, if_neg hk1, boundsOk_ite, if_pos hz]; trivial
  have hrun := run_toProg (P := extIRWith dec) (input := inp) (f := fuel inp.length) hreg hwf
    (by rw [hs0, hI]; exact hB) (fuel_covers hd.cost _)
  rw [hs0, hI] at hrun
  refine hrun.trans (congrArg some ?_)
  have e : semXIR I (extIRWith dec) s0 = semXIR I (.blk []) s1 := by
    rw [extIRWith, semXIR_seq, hs1, semXIR_ite, if_neg hk1, semXIR_ite, if_pos hz]
  rw [congrArg (fun s' : St => s'.o.toList) e]
  simp [semXIR, hpo]

/-- **The `bad` case** (the ill-formed control): a kind byte with `|π| ≠ piSize` makes no output
within the fuel, so `E` is `none`. -/
theorem E_bad {dec : XIR} (hd : DecOk dec) (c : Digest) (π : Proof) (L : Log)
    (hb : kindOf π = .bad) (hπ : π.size < 2 ^ 64) :
    (extWith dec).run (extractorInput c π L) (fuel (extractorInput c π L).length) = some [] ∧
      Eden memX mpwX (extIRWith dec) c π L = none := by
  obtain ⟨b, hb0⟩ : ∃ b, π.data[0]? = some b := by
    rcases h : π.data[0]? with _ | b
    · simp [kindOf, byteAt?_eq, h] at hb
    · exact ⟨b, rfl⟩
  have hk : kindFlag ((extractorInput c π L).toArray.getD 5 0) ≠ 0 := by
    rw [Ne, kindFlag_byte, getD_toArray, tape_byte0 c π L hb0]
    simp only [kindOf, byteAt?_eq, hb0, Option.bind_some] at hb
    intro h; rw [h] at hb; cases hb
  have hs : π.size ≠ piSize := by
    intro h
    simp only [kindOf, byteAt?_eq, hb0, Option.bind_some, h, ↓reduceIte] at hb
    revert hb; cases Kind.ofByte? b <;> simp
  have hr := run_bad_tape hd _ π.size hπ (by rw [getD_toArray, tape_getD4]) hs hk
  exact ⟨hr, by
    rw [Eden, ← den_of_run (by simp only [regs, memX]; norm_num) (wf_extIRWith hd.wf) hr]; rfl⟩

/-- **`E` on a `W` proof is `WitnessSending.decode`, on every size and log** (B-15: `E_W` on the
domain, `Eout`'s `W` branch outside it). -/
theorem ext_W (A : Digest → Digest → Signed → Bool) (c : Digest) (π : Proof) (L : Log)
    (hW : kindOf π = .W) : E A c π L = WitnessSending.decode π := by
  by_cases h : InDomE c π L
  · rw [E_of_dom h]
    exact E_W decOk_decSnark c π L hW (by have := h.1; rw [outCap] at this; omega)
  · rw [E_of_not_dom h, Eout]; simp [hW]

/-- **`E` on a `bad` proof is `none`**, on every size and log (`E_bad` on the domain). -/
theorem ext_bad (A : Digest → Digest → Signed → Bool) (c : Digest) (π : Proof) (L : Log)
    (hb : kindOf π = .bad) : E A c π L = none := by
  by_cases h : InDomE c π L
  · rw [E_of_dom h]
    exact (E_bad decOk_decSnark c π L hb (by have := h.1; rw [outCap] at this; omega)).2
  · rw [E_of_not_dom h, Eout]; simp [hb]

/-! ## Controls

* Positive (every witness-sending witness): `ext_encode`: `E A c (encode w) L = some w` for every
  `w` that fits the output format, on every statement and log.
* Negative (ill-formed, `E_bad`/`ext_bad`): a kind byte with another length halts within the
  fuel with no output.
* Kernel runs of the compiled code (the parse and the `W` branch with a 260-word memory, the
  program's statement unchanged): a toy `W` tape outputs its two proof words (`toy_W`); a toy tape
  whose first byte is `'N'` and whose length is not `piSize` outputs nothing (`toy_bad`); with the
  run takes exactly `260 + 80` fuel (`toy_W_exact`).
-/

/-- A witness-sending proof's first byte is its tag word's: `0` or `1`. -/
theorem encode_byte0 (w : Wit) :
    (WitnessSending.encode w).data[0]? = some 0 ∨ (WitnessSending.encode w).data[0]? = some 1 := by
  cases w <;> simp [WitnessSending.encode, witWords, wordsBytes, wordBytes, enc64, toWord]

/-- **Positive control**: `ext` recovers every witness-sending witness. -/
theorem ext_encode (A : Digest → Digest → Signed → Bool) (c : Digest) (L : Log) (w : Wit)
    (hw : w.Fits) : E A c (WitnessSending.encode w) L = some w := by
  have hk : kindOf (WitnessSending.encode w) = .W := by
    rcases encode_byte0 w with h | h
    · exact kindOf_W h (.inl rfl)
    · exact kindOf_W h (.inr rfl)
  rw [ext_W A c _ L hk, WitnessSending.decode_encode w hw]

namespace Controls

/-- The program with a 260-word memory (the toy runs; `ext`'s memory is `2^26`). -/
def toyP : XProg := toProg 260 0 (extIRWith decSnark)

/-- A toy `W` tape: statement, `|π| = 9`, two proof words (first byte `0x00`), `|L| = 0`. -/
def tapeW : List Word := [0, 0, 0, 0, 9, 0x1100, 0x22, 0]

/-- A toy ill-formed tape: first byte `'N'`, `|π| = 9 ≠ piSize`. -/
def tapeBad : List Word := [0, 0, 0, 0, 9, 0x114E, 0x22, 0]

theorem toy_W : toyP.run tapeW 400 = some [0x1100, 0x22] := by
  simp only [toyP, extIRWith, parseIR, kindPs, piSize_eq]; decide +kernel

/-- Exactly `260 + 80` steps: `340` suffices, `339` does not. -/
theorem toy_W_exact : toyP.run tapeW 340 = some [0x1100, 0x22] ∧ toyP.run tapeW 339 = none := by
  simp only [toyP, extIRWith, parseIR, kindPs, piSize_eq]; decide +kernel

theorem toy_bad : toyP.run tapeBad 400 = some [] := by
  simp only [toyP, extIRWith, parseIR, kindPs, piSize_eq]; decide +kernel

end Controls

end FR.X
