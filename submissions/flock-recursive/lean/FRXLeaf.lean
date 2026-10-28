-- New for `flock-recursive` (BLUEPRINT §6.2 step 1, §6.5; stage S-H2, track L-ext).
import FRXSpec
import FRXRead

/-!
# The leaf case of `ext_good_tape`: `E` reads the leaf witness off the header

A leaf proof (`'L'`, `'P'`) carries its chain start `s` in the clear: header bytes `16 … 47`
(`hdrBytes k s`; S-0's `finSh` reads it as the shift argument's boundary, and the circuit pins
the chain's start to it). Its chain length is `n = leafN k = 2^(m − 14)` (checked against the
statement by the verifier). So the SNARK branch, on a kind byte other than `'N'`, outputs
`witWords (.leaf s n)` and decodes nothing.

**`E_leaf`**: on a domain tape of a leaf proof of `piSize` bytes,
`E c π L = some (.leaf (bytesAt π 16 32) (leafN k))`.
-/

namespace FR.X

open RecursionFast

theorem kindIR_regs (I : Array Word) (s : St) (hM : Inv s.M) :
    rd (semXIR I kindIR s).M rKN = (if I.getD 5 0 &&& 0xFF = 0x4E then 1 else 0) ∧
    rd (semXIR I kindIR s).M rKL = (if I.getD 5 0 &&& 0xFF = 0x4C then 1 else 0) ∧
    (semXIR I kindIR s).o = s.o := by
  have hs := hM.1
  simp only [regs] at hs
  simp only [kindIR, readAt, semXIR, runPrims, List.foldl, Prim.run]
  refine ⟨?_, ?_, trivial⟩ <;>
  simp (disch := first | decide | (simp only [size_set, rA, rB, rK2, rKN, rKL]; omega)) only
    [rd_set_self, rd_set_ne] <;>
  simp [XOp.eval]

/-- **The leaf output**: the tag, tape words `7 … 10`, and `2^18` or `2^16` by `rKL`. -/
theorem leafIR_out (I : Array Word) (s : St) (hM : Inv s.M) :
    (semXIR I leafIR s).o.toList = s.o.toList ++ [0, I.getD 7 0, I.getD 8 0, I.getD 9 0,
      I.getD 10 0, if rd s.M rKL = 0 then 2 ^ 16 else 2 ^ 18] := by
  have hs := hM.1
  simp only [regs] at hs
  simp only [leafIR, outAt, readAt, semXIR, runPrims, List.foldl, Prim.run]
  simp (disch := first | decide | (simp only [size_set, rA, rK2, rV2]; omega)) only
    [rd_set_self, rd_set_ne]
  split <;> simp

/-- The chain start's packed words are tape words `7 … 10`. -/
theorem tape_leafS (c : Digest) (π : Proof) (L : Log) (hs : π.size = piSize) :
    packBytes (bytesAt π 16 32).toList = [(extractorInput c π L).getD 7 0,
      (extractorInput c π L).getD 8 0, (extractorInput c π L).getD 9 0,
      (extractorInput c π L).getD 10 0] := by
  have hp : π.size = 797904 := hs.trans piSize_eq
  have w : ∀ m < 4, (packBytes (bytesAt π (8 * 2) 32).toList).getD m 0 =
      (extractorInput c π L).getD (5 + (2 + m)) 0 := fun m hm => by
    rw [packBytes_bytesAt _ (by omega) hm, tape_getD_proof c π L (by omega),
      List.getD_eq_getElem _ _]
  rw [packBytes_digest_eq4, show (16 : ℕ) = 8 * 2 from rfl, w 0 (by decide), w 1 (by decide),
    w 2 (by decide), w 3 (by decide)]

/-- The first proof byte of a leaf kind, as the low byte of tape word 5. -/
theorem leaf_byte (c : Digest) (π : Proof) (L : Log) {k : Kind} (hk : kindOf π = .snark k) :
    ∃ b, π.data[0]? = some b ∧ Kind.ofByte? b = some k ∧
      ((extractorInput c π L).getD 5 0 &&& 0xFF).toNat = b.toNat := by
  rcases h : π.data[0]? with _ | b
  · simp [kindOf, byteAt?_eq, h] at hk
  · refine ⟨b, rfl, ?_, ?_⟩
    · simp only [kindOf, byteAt?_eq, h, Option.bind_some] at hk
      revert hk; cases Kind.ofByte? b <;> intro hk
      · cases hk
      · by_cases hs : π.size = piSize
        · simp only [hs, if_true, PKind.snark.injEq] at hk; rw [hk]
        · simp [hs] at hk
    · rw [lowByte, ← toNat_toUInt8, tape_byte0 c π L h]

theorem lowByte_eq {w : Word} {b : UInt8} (h : (w &&& 0xFF).toNat = b.toNat) (v : Word)
    (u : UInt8) (hvu : v.toNat = u.toNat) : w &&& 0xFF = v ↔ b = u := by
  rw [← BitVec.toNat_inj, h, hvu, UInt8.toNat_inj]

/-- **The run on a leaf proof**: the program halts within the fuel and outputs
`witWords (.leaf s n)`, `s` header bytes `16 … 47`, `n = leafN k`. -/
theorem run_leaf (c : Digest) (π : Proof) (L : Log) (hq : ∀ e ∈ L, e.1.size < 2 ^ 64)
    (ht : (extractorInput c π L).length ≤ 2 ^ 64) {k : Kind} (hk : kindOf π = .snark k)
    (hkn : k ≠ .N30) :
    ext.run (extractorInput c π L) (fuel (extractorInput c π L).length) =
      some (witWords (.leaf (bytesAt π 16 32) (leafN k))) := by
  have hs : π.size = piSize := by
    by_contra hne
    simp only [kindOf, byteAt?_eq, hne, if_false] at hk
    split at hk <;> simp at hk
  obtain ⟨b, -, hbk, hlow⟩ := leaf_byte c π L hk
  set inp := extractorInput c π L with hinp
  have hd := decOk_decSnark
  have hwf := wf_extIRWith hd.wf
  have hreg : regs ≤ memX := by simp only [regs, memX]; norm_num
  have h0 : Inv (initSt (memX + mpwX * inp.length)).M := inv_initSt (Nat.le_add_right_of_le hreg)
  generalize hs0 : initSt (memX + mpwX * inp.length) = s0 at h0
  have hIj : ∀ j, inp.toArray.getD j 0 = inp.getD j 0 := fun j => getD_toArray _ _
  have hI5 := hIj 5
  generalize hI : inp.toArray = I at hI5 hIj ⊢
  have hsafe := hd.safe c π L hs hq ht
  rw [← hinp, hI] at hsafe
  have h1 : Inv (semXIR I parseIR s0).M := inv_sem I hwf.1 h0
  have hz : rd (semXIR I parseIR s0).M rIsSz ≠ 0 := by
    rw [parse_regs I s0 h0, hIj, hinp, tape_getD4, hs]
    show (if BitVec.ofNat 64 piSize = BitVec.ofNat 64 piSize then (1 : Word) else 0) ≠ 0
    rw [if_pos rfl]; decide
  have hk1 : rd (semXIR I parseIR s0).M rIsK ≠ 0 := by
    rw [parse_isK I s0 h0, Ne, kindFlag_byte, hIj, hinp,
      tape_byte0 c π L (leaf_byte c π L hk).choose_spec.1, (leaf_byte c π L hk).choose_spec.2.1]
    simp
  have hpo : (semXIR I parseIR s0).o = #[] := by rw [parse_o, ← hs0, initSt_o]
  generalize hs1 : semXIR I parseIR s0 = s1 at h1 hz hk1 hpo
  have hB : BoundsOk I inp.length (extIRWith decSnark) s0 := by
    rw [extIRWith, boundsOk_seq]
    refine ⟨boundsOk_of_safe (safe_parseIR _ _) hwf.1 _ h0, ?_⟩
    rw [hs1, boundsOk_ite, if_neg hk1, boundsOk_ite, if_neg hz]
    exact boundsOk_of_safe hsafe hd.wf _ h1
  have hrun := run_toProg (P := extIRWith decSnark) (input := inp) (f := fuel inp.length) hreg hwf
    (by rw [hs0, hI]; exact hB) (fuel_covers hd.cost _)
  rw [hs0, hI] at hrun
  refine hrun.trans (congrArg some ?_)
  have e : semXIR I (extIRWith decSnark) s0 = semXIR I (.ite rKN decNode leafIR)
      (semXIR I kindIR s1) := by
    rw [extIRWith, semXIR_seq, hs1, semXIR_ite, if_neg hk1, semXIR_ite, if_neg hz, decSnark, decLN3,
      semXIR_seq]
  obtain ⟨n1, n2, n3⟩ := kindIR_regs I s1 h1
  have hM2 := inv_sem I decOk_decLN3.wf.1 h1
  rw [congrArg (fun s' : St => s'.o.toList) e]
  generalize semXIR I kindIR s1 = s2 at n1 n2 n3 hM2
  have hN : I.getD 5 0 &&& 0xFF ≠ 0x4E := by
    rw [hI5]; intro h
    have := (lowByte_eq hlow 0x4E 0x4E rfl).1 h
    subst this; exact hkn (by simpa [Kind.ofByte?] using hbk.symm)
  rw [semXIR_ite, n1, if_neg hN, if_pos rfl, leafIR_out I s2 hM2, n3, hpo, n2, hI5, hIj, hIj,
    hIj, hIj]
  simp only [List.nil_append, witWords, leafN]
  rw [tape_leafS c π L hs, ← hinp]
  have hb : b = k.byte := by cases k <;> simp_all [Kind.ofByte?, Kind.byte] <;> split_ifs at hbk <;> simp_all
  cases k with
  | N30 => exact absurd rfl hkn
  | L32 =>
    rw [if_pos ((lowByte_eq hlow 0x4C 0x4C rfl).2 (by rw [hb]; rfl)), if_neg (by decide)]
    simp only [List.cons_append, List.nil_append, List.cons.injEq, and_true]
    exact ⟨by decide, by decide⟩
  | P30 =>
    have hL : ¬ (inp.getD 5 0 &&& 0xFF = 0x4C) := fun h => by
      have := (lowByte_eq hlow 0x4C 0x4C rfl).1 h; rw [hb] at this; cases this
    rw [if_neg hL, if_pos rfl]
    simp only [List.cons_append, List.nil_append, List.cons.injEq, and_true]
    exact ⟨by decide, by decide⟩

/-- **`E` on a leaf proof** (the leaf case of `ext_good_tape`): the witness `.leaf s n` with
`s` the header's chain start and `n = leafN k`. -/
theorem E_leaf (c : Digest) (π : Proof) (L : Log) (hq : ∀ e ∈ L, e.1.size < 2 ^ 64)
    (ht : (extractorInput c π L).length ≤ 2 ^ 64) {k : Kind} (hk : kindOf π = .snark k)
    (hkn : k ≠ .N30) :
    E c π L = some (.leaf (bytesAt π 16 32) (leafN k)) := by
  show (ext.run (extractorInput c π L) (fuel (extractorInput c π L).length)).bind decodeWit = _
  rw [run_leaf c π L hq ht hk hkn, Option.bind_some, decodeWit_witWords]
  show leafN k < 2 ^ 64
  cases k <;> simp [leafN, Kind.m]

end FR.X
