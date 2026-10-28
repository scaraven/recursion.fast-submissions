-- New for `flock-recursive` (BLUEPRINT §6.5, the node case of `ext_good_tape`; stage S-H2,
-- track L-ext, S-H2j).
import FRXLeaf
import FRXNode

/-!
# The node case of `ext_good_tape`, up to the output

On a domain tape of a node proof (`kindOf π = .snark .N30`), `ext` takes the node branch
`decNode` (`FRXNode`), halts within its fuel, and leaves `f⁽⁰⁾`'s rows at `ob0` (`ext_node`).
The output step (`f⁽⁰⁾` to `witWords (.node c₁ c₂ p₁ p₂)`, BLUEPRINT §6.2 step 5) is not
delivered: until it is, `ext` outputs nothing on a node proof, so `E c π L = none` there
(`ext_node`'s first conjunct).

The hypotheses of `ext_node` beyond the domain are what `final` (`FinalLaw`) holds about the
log's transcript `es` when the verifier accepts: the chain link (`fmAns … = ansAt es`), the
absorbed caps and final message are π's fields, no state hit, and at each level a close word with
`A_c = jointAgree` (`ligerito_final`).
-/

namespace FR.X

open RecursionFast FR FR.Snd FR.Merkle

/-- **The node case of `ext_good_tape`, up to the output.** On a domain tape of a node proof, with
the transcript facts `final` holds, the program halts within the fuel with no output yet, and
its final heap holds `f⁽⁰⁾`: at `ob0 + 2^18 r + 2x`, coefficient `x` of row `r` of
`msgOf .N30 L es 0` as an `F` value. -/
theorem ext_node (c : Digest) (π : Proof) (L : Log) (hq : ∀ e ∈ L, e.1.size < 2 ^ 64)
    (ht : (extractorInput c π L).length ≤ 2 ^ 64) (hk : kindOf π = .snark .N30)
    (hS : ¬ StateHit L) (st₀ : Digest) {es : Log}
    (hfm : ∀ p < nRep, fmAns (fsQ (vkOf π) c π) st₀ L p = some (ansAt es p))
    (hcap0 : ∀ e < 2 ^ 9, capDig es 0 e = capPi π e)
    (hcap : ∀ i, 1 ≤ i → i ≤ 4 → ∀ e < 2 ^ capLogL i, capDig es i e = capPiL i π e)
    (hfin : ∀ x < 32, finalAt es x = finPi π x)
    (hfar : ∀ i < 5, ¬ farL .N30 L es i)
    (hA : ∀ i < 5, consSet .N30 L es i = jointAgree (wordK .N30 L es i) (decodeL .N30 L es i)) :
    ext.run (extractorInput c π L) (fuel (extractorInput c π L).length) = some [] ∧
    ∀ r < (lvl .N30 0).rows, ∀ x < 2 ^ mLog .N30 0,
      algebraMap F K (rdF (semXIR (extractorInput c π L).toArray (extIRWith decSnark)
        (initSt (memX + mpwX * (extractorInput c π L).length))).M
          (ob0 + 2 * 2 ^ mLog .N30 0 * r + 2 * x)) = msgOf .N30 L es 0 r x := by
  have hs : π.size = piSize := by
    by_contra hne
    simp only [kindOf, byteAt?_eq, hne, if_false] at hk
    split at hk <;> simp at hk
  have hD : Dom c π L := ⟨hs, hq, ht⟩
  obtain ⟨b, -, hbk, hlow⟩ := leaf_byte c π L hk
  have hb : b = 0x4E := by
    simp only [Kind.ofByte?] at hbk; split_ifs at hbk <;> simp_all
  set inp := extractorInput c π L with hinp
  have hd := decOk_decSnark
  have hwf := wf_extIRWith hd.wf
  have hreg : regs ≤ memX := by simp only [regs, memX]; norm_num
  have hlen : memX + L.length + L.length ≤ memX + mpwX * inp.length := by
    have h1 := tape_entries_end c π L hs
    have h2 := len_entries L
    simp only [mpwX]
    generalize entryOff L L.length = E at h1 h2
    generalize inp.length = T at h1
    omega
  have h0 : Inv (initSt (memX + mpwX * inp.length)).M := inv_initSt (Nat.le_add_right_of_le hreg)
  have hz0 : (initSt (memX + mpwX * inp.length)).M.size = memX + mpwX * inp.length := by
    simp [initSt]
  generalize hs0 : initSt (memX + mpwX * inp.length) = s0 at h0 hz0
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
  have hz1 := size_sem I parseIR s0
  generalize hs1 : semXIR I parseIR s0 = s1 at h1 hz hk1 hpo hz1
  have hB : BoundsOk I inp.length (extIRWith decSnark) s0 := by
    rw [extIRWith, boundsOk_seq]
    refine ⟨boundsOk_of_safe (safe_parseIR _ _) hwf.1 _ h0, ?_⟩
    rw [hs1, boundsOk_ite, if_neg hk1, boundsOk_ite, if_neg hz]
    exact boundsOk_of_safe hsafe hd.wf _ h1
  have hrun := run_toProg (P := extIRWith decSnark) (input := inp) (f := fuel inp.length) hreg hwf
    (by rw [hs0, hI]; exact hB) (fuel_covers hd.cost _)
  rw [hs0, hI] at hrun
  have e : semXIR I (extIRWith decSnark) s0 = semXIR I (.ite rKN decNode leafIR)
      (semXIR I kindIR s1) := by
    rw [extIRWith, semXIR_seq, hs1, semXIR_ite, if_neg hk1, semXIR_ite, if_neg hz, decSnark, decLN3,
      semXIR_seq]
  obtain ⟨n1, -, n3⟩ := kindIR_regs I s1 h1
  have hM2 := inv_sem I decOk_decLN3.wf.1 h1
  have hz2 := size_sem I kindIR s1
  -- the node byte
  have hN : I.getD 5 0 &&& 0xFF = 0x4E := by
    rw [hI5]; exact (lowByte_eq hlow 0x4E 0x4E rfl).2 hb
  have e2 : semXIR I (.ite rKN decNode leafIR) (semXIR I kindIR s1) =
      semXIR I decNode (semXIR I kindIR s1) := by
    rw [semXIR_ite, n1, if_pos hN, if_neg (by decide : (1 : Word) ≠ 0)]
  -- the branch's output is empty
  have hBn : BoundsOk I inp.length decNode (semXIR I kindIR s1) := by
    have := boundsOk_of_safe hsafe hd.wf _ h1
    rw [decSnark, decLN3, boundsOk_seq, boundsOk_ite, n1, if_pos hN, if_neg (by decide : (1 : Word) ≠ 0)] at this
    exact this.2
  have ho := outs_le inp.length decNode _ decOk_decLN3.wf.2.1 hM2 hBn
  rw [outs_decNode, n3, hpo] at ho
  refine ⟨hrun.trans ?_, fun r hr x hx => ?_⟩
  · rw [e, e2]
    simp only [Array.size_empty, Nat.add_zero, Nat.le_zero, Array.size_eq_zero_iff] at ho
    rw [ho]
  · rw [e, e2]
    have hszK : memX + L.length + L.length ≤ (semXIR I kindIR s1).M.size := by
      rw [hz2, hz1, hz0]; exact hlen
    rw [← hI] at hM2 hszK ⊢
    exact decNode_sem c π L hD hS st₀ hfm hcap0 hcap hfin hfar hA _ hM2 hszK r hr x hx

end FR.X
