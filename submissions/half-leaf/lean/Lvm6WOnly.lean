-- lvm6 A0: the witness-sending-only submission on the season-1 frame, at the v6 relation.
import LvmCertSGen
import Lvm6VWFast

/-!
# The `W`-only submission (S branch off)

The season-1 frame `subWith VS E ext` (`LvmCertSGen`) with:

* the verifier runs as `Lvm6VTw.VwithT VSoff`, proved equal to `Vwith VSoff` (`submissionW_eq`);
* **`VSoff`**: the SNARK branch rejects every proof (`.ret false`, no query);
* **`schemeW`**: a compiled scheme whose header parser accepts no proof, with the trivial knowledge
  certificate `kcertW` (no doom, no luck), so `SSound VSoff E vk` holds for every `E` and `vk`;
* **`extW`**: the season-1 extractor program `extWith pzW decW` with the empty SNARK decoder
  `decW = .blk []`; on a `W` proof its denotation is `WitnessSending.decode π` (`eden_W`), the leaf
  being the v6 `Wit.leaf xs` through the Library's encoding;
* **`EW`**: the program's denotation on the contract's domain, outside it `decode π` for a `W`
  proof and nothing for an `S` proof.

`certifiedW` is the certificate against `claim.json`'s numbers (`certificateR_claim`): knowledge
error `2^-128` per query (the Fiat–Shamir bound of the empty scheme), perfect completeness of the
witness-sending prover for every leaf `|xs| ≤ leafCap` and every accepted node, `qV = 16384`, fuel
`2^46 + 2^13 t`.
-/

set_option autoImplicit false

namespace Lvm6.W

open RecursionFast Lvm.T Lvm.FS Lvm.X
open RecursionFast.WitnessSending (encode decode)
open LeanVM.Protocol.Compile hiding Proof Bytes Word
open scoped NNReal ENNReal

/-! ## The scheme that accepts nothing, and its certificate -/

/-- A compiled scheme whose header parser rejects every proof. -/
def schemeW : Scheme where
  Stmt := List UInt8
  P := fun _ => .ret false
  enc := id
  enc_inj := Function.injective_id
  hdr := fun _ => none
  ok := fun _ _ => false
  capOf := fun _ _ => 0
  q0 := Lvm.q0Bytes
  q0_short := by decide
  decE := eOfBytes
  decK := kOfBytes
  chal := chalOf
  chal_sum := chalOf_sum

theorem after_ret_false {h : List Ev} {p : VerifierProgram Bool}
    (hp : (VerifierProgram.ret false : VerifierProgram Bool).after h = some p) : p = .ret false := by
  cases h with
  | nil => simpa [VerifierProgram.after] using hp.symm
  | cons e es => cases e <;> simp [VerifierProgram.after] at hp

/-- The empty doom certificate of `.ret false`. -/
noncomputable def certW : Cert (VerifierProgram.ret false : VerifierProgram Bool) where
  D _ := False
  ε _ := 0
  read _ _ _ hD := hD.elim
  grind _ _ hD := hD.elim
  commit _ _ _ _ hD := hD.elim
  group _ _ _ _ hD := hD.elim
  final _ _ hD := hD

/-- **The trivial knowledge certificate** of `schemeW`, for any relation. -/
noncomputable def kcertW (R : Digest → Wit → Prop) : KCert schemeW R where
  cert _ := certW
  ε := 0
  cert_ε _ _ _ _ hD := hD.elim
  ε_lt_one := zero_lt_one
  B _ _ := False
  εB := 0
  εB_lt_one := zero_lt_one
  B_nil _ := id
  B_read _ _ _ _ := id
  B_commit _ _ _ _ _ := id
  B_group _ _ hp hk _ := by
    have := after_ret_false hp
    subst this
    rcases hk with ⟨k, hk⟩ | ⟨i, ps, k, hk⟩ <;> cases hk
  ext _ _ _ := .leaf []
  extract _ _ hp _ _ _ := by have := after_ret_false hp; cases this

theorem εFS_kcertW (R : Digest → Wit → Prop) : Scheme.εFS (kcertW R) ≤ (2 : ℝ≥0)⁻¹ ^ 128 := by
  unfold Scheme.εFS
  show (0 : ℝ≥0) + 0 + (badCount : ℝ≥0) / 2 ^ 256 ≤ _
  rw [zero_add, zero_add]
  exact badCount_div_le.trans (pow_le_pow_of_le_one (by norm_num) (by norm_num) (by norm_num))

/-- `schemeW`'s compiled verifier accepts nothing. -/
theorem schemeW_rejects (c : Digest) (π : Proof) (L : Log) : (schemeW.V c π).runLog L ≠ some true := by
  rw [Scheme.runLog_V]
  simp [schemeW]

/-- **The SNARK branch off.** -/
def VSoff : SProg := fun _ _ _ => .ret false

/-- **`SSound` with the SNARK branch off**, for every extractor. -/
theorem sSound_off (E : Digest → Proof → Log → Option Wit) (vk : Digest) : SSound VSoff E vk :=
  ⟨schemeW, kcertW (Rel (accV VSoff vk)), εFS_kcertW _,
    fun L c π _ h => by simp [VSoff, OProg.runLog] at h,
    fun L c π _ _ _ h => (schemeW_rejects c π L h).elim⟩

/-! ## The extractor -/

/-- The SNARK decoder: nothing. -/
def decW : XIR := .blk []

/-- The SNARK proof size the parse tests (irrelevant: both branches are `decW`-free). -/
def pzW : ℕ := 0

theorem decOk_decW : DecOk pzW decW where
  pz_lt := by decide
  wf := by simp [decW, WF]
  safe := fun _ _ _ _ _ _ => Safe.blk []
  cost := fun t => by simp [decW, cost, blkSteps, decBudget, fuelBase, fuelPerWord]; omega
  outs := fun t => by simp [decW, outs]
  size := by simp [decW, sizeIR, blkSteps]

/-- **The extractor program.** -/
def extW : XProg := extWith pzW decW

/-- The contract's `Computes` domain. -/
def InDomW (c : Digest) (π : Proof) (L : Log) : Prop :=
  π.size ≤ 8 * outCap ∧ (∀ e ∈ L, e.1.size < 2 ^ 64) ∧ (extractorInput c π L).length ≤ 2 ^ 64

instance (c : Digest) (π : Proof) (L : Log) : Decidable (InDomW c π L) :=
  inferInstanceAs (Decidable (_ ∧ _ ∧ _))

/-- **The extractor specification**: the denotation on the domain; outside it a `W` proof decoded
and nothing for an `S` proof. -/
def EW (c : Digest) (π : Proof) (L : Log) : Option Wit :=
  if InDomW c π L then Eden memX mpwX (extIRWith pzW decW) c π L
  else if isS π then none else decode π

theorem computesW : Computes extW EW fuel := fun c π L h1 h2 h3 => by
  obtain ⟨o, ho, hl, hd⟩ := computesWith decOk_decW c π L h1 h2 h3
  exact ⟨o, ho, hl, hd.trans (if_pos ⟨h1, h2, h3⟩).symm⟩

theorem lowByte (w : Word) : (w &&& 0xFF).toNat = w.toNat % 256 := by
  rw [BitVec.toNat_and, show (0xFF : Word).toNat = 2 ^ 8 - 1 from rfl, Nat.and_two_pow_sub_one_eq_mod]

/-- The low byte of tape word 5 is the proof's first byte. -/
theorem tape_byte0 (c : Digest) (π : Proof) (L : Log) {b : UInt8} (h0 : π.data[0]? = some b) :
    ((extractorInput c π L).getD 5 0).toNat % 256 = b.toNat := by
  have hpos : 0 < π.size := by
    rcases Nat.eq_zero_or_pos π.size with h | h
    · simp [Array.size_eq_zero_iff.mp h] at h0
    · exact h
  have := tape_getD_proof c π L (j := 0) (by (clear * - hpos; omega))
  rw [Nat.add_zero] at this
  rw [this]
  have hw := wordByte_packBytes π.data.toList 0
  simp only [wordByte, Nat.zero_div, Nat.zero_mod, pow_zero, Nat.div_one] at hw
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by
    rw [packBytes_length, ← WitnessSending.size_eq_length]; (clear * - hpos; omega)), Option.getD_some] at hw
  have h1 : π.data.toList.getD 0 0 = b := by
    rw [List.getD_eq_getElem?_getD, Array.getElem?_toList, h0, Option.getD_some]
  rw [h1] at hw
  rw [← hw, Nat.toUInt8_eq, UInt8.toNat_ofNat']

theorem parse_isK (pz : ℕ) (I : Array Word) (s : St) (hM : Inv s.M) :
    rd (semXIR I (parseIR pz) s).M rIsK = (if I.getD 5 0 &&& 0xFF = kindS then 1 else 0) := by
  have hs := hM.1
  simp only [regs] at hs
  simp only [parseIR, readAt, kindPs, semXIR, runPrims, List.foldl, Prim.run, rA, rLen, rK, rB0,
    rIsK, rIsSz]
  simp (disch := first | decide | (clear * - s hs; omega) | (simp only [size_set]; (clear * - s hs; omega))) [rd_set_self, rd_set_ne, XOp.eval]

/-- **The extractor on a `W` proof** is the witness-sending decoder, on every log. -/
theorem eden_W (c : Digest) (π : Proof) (L : Log) (hπ : π.size < 2 ^ 64) (hW : isS π = false) :
    Eden memX mpwX (extIRWith pzW decW) c π L = decode π := by
  have hwf := wf_extIRWith (pz := pzW) decOk_decW.wf
  have hreg : regs ≤ memX := by simp only [regs, memX]; norm_num
  have h0 : Inv (initSt (memX + mpwX * (extractorInput c π L).length)).M :=
    inv_initSt (Nat.le_add_right_of_le hreg)
  have h4 : (extractorInput c π L).toArray.getD 4 0 = toWord π.size := by
    rw [getD_toArray, tape_getD4]
  have hw : (ceil8 ((extractorInput c π L).toArray.getD 4 0)).toNat = (π.size + 7) / 8 := by
    rw [h4, toNat_ceil8 hπ]
  have hso := initSt_o (memX + mpwX * (extractorInput c π L).length)
  rw [Eden, den]
  generalize initSt (memX + mpwX * (extractorInput c π L).length) = s0 at h0 hso
  have h1 : Inv (semXIR (extractorInput c π L).toArray (parseIR pzW) s0).M := inv_sem _ hwf.1 h0
  have hk5 := parse_isK pzW (extractorInput c π L).toArray s0 h0
  have hpo : (semXIR (extractorInput c π L).toArray (parseIR pzW) s0).o = s0.o := parse_o _ _ _
  rw [extIRWith, semXIR_seq, semXIR_ite]
  generalize semXIR (extractorInput c π L).toArray (parseIR pzW) s0 = s1 at h1 hk5 hpo
  rw [hso] at hpo
  by_cases hk : rd s1.M rIsK = 0
  · rw [if_pos hk, wIR_sem _ _ h1 (by rw [hw]; (clear * - hπ; omega)), hpo, hw, WitnessSending.decode]
    congr 1
    refine List.ext_getElem (by
      simp only [List.nil_append, List.length_map, List.length_range, packBytes_length]
      rw [WitnessSending.size_eq_length]) fun j _ h2 => ?_
    simp only [List.nil_append, List.getElem_map, List.getElem_range, getD_toArray]
    exact tape_getD_proof c π L (by rwa [packBytes_length, ← WitnessSending.size_eq_length] at h2)
  · rw [if_neg hk, semXIR_ite, show decW = .blk [] from rfl, ite_self]
    have he : π.data.toList = [] := by
      rcases h : π.data[0]? with _ | b
      · rw [Array.getElem?_eq_none_iff] at h
        exact List.eq_nil_of_length_eq_zero (by rw [Array.length_toList]; omega)
      · exfalso
        have hK : (extractorInput c π L).toArray.getD 5 0 &&& 0xFF = kindS := by
          by_contra hn; rw [if_neg hn] at hk5; exact hk hk5
        have h2 := congrArg BitVec.toNat hK
        rw [lowByte, getD_toArray, tape_byte0 c π L h] at h2
        have hb : b = sByte := UInt8.toNat_inj.mp h2
        have hg : π.data.getD 0 0 = b := by rw [Array.getD_eq_getD_getElem?, h]; rfl
        simp [isS, hg, hb] at hW
    simp [semXIR, hpo, WitnessSending.decode, he, packBytes]

/-- **`EW` on a `W` proof** is the witness-sending decoder, on every log. -/
theorem EW_W (c : Digest) (π : Proof) (L : Log) (hW : isS π = false) : EW c π L = decode π := by
  by_cases hD : InDomW c π L
  · rw [EW, if_pos hD]
    exact eden_W c π L (lt_of_le_of_lt hD.1 (by simp only [outCap]; norm_num)) hW
  · rw [EW, if_neg hD, if_neg (by simp [hW])]

/-! ## The submission and its certificate -/

/-- **The `W`-only submission**: `subWith VSoff EW extW` with its verifier run as the byte-level
twin `VwithT VSoff` (`Lvm6VWFast`; `VwithT_eq`: the same function as `Vwith VSoff`). -/
def submissionW : Submission := { subWith VSoff EW extW with V := Lvm6.VTw.VwithT VSoff }

/-- The twin changes nothing: `submissionW` is `subWith VSoff EW extW`. -/
theorem submissionW_eq : submissionW = subWith VSoff EW extW := by
  simp only [submissionW, Lvm6.VTw.VwithT_eq]
  rfl

/-- The certificate of `subWith VSoff EW extW` against `claim.json`'s numbers. -/
theorem certifiedW0 :
    CertificateR ⟨(1 : ℝ≥0) / 340282366920938463463374607431768211456, (0 : ℝ≥0) / 1, 16384,
      fun t => 70368744177664 + 8192 * t⟩ (subWith VSoff EW extW) :=
  certificateR_claim _ _ _
    ⟨fun H vk c π _ => by simp [VSoff, OProg.queries], computesW, size_extWith decOk_decW.size,
      fun c π L h => EW_W c π L h, fun vk => sSound_off EW vk⟩

/-- **The certificate of the `W`-only submission** against `claim.json`'s numbers. -/
theorem certifiedW :
    CertificateR ⟨(1 : ℝ≥0) / 340282366920938463463374607431768211456, (0 : ℝ≥0) / 1, 16384,
      fun t => 70368744177664 + 8192 * t⟩ submissionW := by
  rw [submissionW_eq]
  exact certifiedW0

end Lvm6.W
