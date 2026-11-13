-- New for lvm2 roll 11 (M′, R11-X, part 2(b)): `Computes` for M′'s extractor with the static memory `memM = 2^26`.
-- Adapted from `LvmXComputes.lean` (`DecOk`, `extWith`, `fuel_covers`, `halts_of_tape`, `halts_with`,
-- `computesWith`), `LvmXTop.lean` (`decOk_decX`, `EdX`, `EX`, `computesX`, `extX_caps`) and `LvmXSpec.lean`
-- (`run_W_tape`, `EX_W`): the memory `memX = 2^25` becomes `memM`, the SNARK branch's budget `decBudget` becomes
-- `decBudgetM` (`2^27` held back, for the memory); the declared fuel `fuel t = 2^46 + 2^13 t` is unchanged.
import LvmMPXTop
import LvmXSpec

/-!
# `Computes extXM (EXM A) fuel`

* `decBudgetM t = 2^46 − 2^27 + (2^13 − 16) t`; `DecOkM pz dec`: `DecOk` with that budget.
* `extWithM pz dec = toProg memM mpwX (extIRWith pz dec)`: the shipped parse and `W` copy, M′'s memory.
* **`decOk_decXM`**: M′'s SNARK branch meets it (`cost_decXM ≤ 2^45 + …`).
* `EdXM`, **`EXM A`** (the specification: the denotation on the domain, the shipped `EoutX A` outside),
  **`computesXM`**, `extXM_caps`, **`EXM_W`** (witness-sending proofs decode).
-/

namespace Lvm.X

open RecursionFast

/-- What M′'s SNARK branch may cost: the fuel less the memory (`2^26` and the margin), the parse and the `W`
branch. -/
def decBudgetM (t : ℕ) : ℕ := fuelBase - 2 ^ 27 + (fuelPerWord - 16) * t

/-- **The obligations on M′'s SNARK branch** (as `DecOk`, budget `decBudgetM`). -/
structure DecOkM (pz : ℕ) (dec : XIR) : Prop where
  pz_lt : pz < 2 ^ 64
  wf : WF dec
  safe : ∀ c (π : Proof) (L : Log), π.size = pz → (∀ e ∈ L, e.1.size < 2 ^ 64) →
    (extractorInput c π L).length ≤ 2 ^ 64 →
    Safe (extractorInput c π L).toArray (extractorInput c π L).length dec
  cost : ∀ t, cost dec t ≤ decBudgetM t
  outs : ∀ t, outs dec t ≤ outCap
  size : sizeIR dec ≤ 2 ^ 19

/-- The program at M′'s memory. -/
def extWithM (pz : ℕ) (dec : XIR) : XProg := toProg memM mpwX (extIRWith pz dec)

theorem fuel_coversM {pz : ℕ} {dec : XIR} (h : ∀ t, cost dec t ≤ decBudgetM t) (t : ℕ) :
    memM + mpwX * t + cost (extIRWith pz dec) t + 8 ≤ fuel t := by
  have := h t
  rw [cost_extIRWith]
  simp only [memM, mpwX, fuel, fuelBase, fuelPerWord, decBudgetM] at *
  omega

theorem size_extWithM {pz : ℕ} {dec : XIR} (h : sizeIR dec ≤ 2 ^ 19) :
    (extWithM pz dec).body.size ≤ progCap := by
  simp only [extWithM, toProg, size_compile, sizeIR, sizeIR_extIRWith, initPs, blkSteps,
    List.length_cons, List.length_nil, progCap]
  norm_num; omega

theorem halts_of_tapeM {pz : ℕ} {dec : XIR} (hd : DecOkM pz dec) (inp : List Word) (a : ℕ)
    (ha : a ≤ 8 * outCap)
    (h4 : inp.toArray.getD 4 0 = toWord a) (hlen : (a + 7) / 8 + 6 ≤ inp.length)
    (hsafe : a = pz → Safe inp.toArray inp.length dec) :
    ∃ o, (extWithM pz dec).run inp (fuel inp.length) = some o ∧ o.length ≤ outCap := by
  rw [outCap] at ha
  have hwf := wf_extIRWith (pz := pz) hd.wf
  have hreg : regs ≤ memM := by simp only [regs, memM]; norm_num
  have h0 : Inv (initSt (memM + mpwX * inp.length)).M := inv_initSt (Nat.le_add_right_of_le hreg)
  generalize hs0 : initSt (memM + mpwX * inp.length) = s0 at h0
  generalize hI : inp.toArray = I at h4 hsafe
  have h1 : Inv (semXIR I (parseIR pz) s0).M := inv_sem I hwf.1 h0
  have hpi : rd (semXIR I (parseIR pz) s0).M rIsSz ≠ 0 → a = pz := by
    intro h
    rw [parse_regs pz I s0 h0, h4] at h
    by_contra hne
    refine h (if_neg fun he => hne ?_)
    have := congrArg BitVec.toNat he
    rwa [toNat_toWord (by omega), BitVec.toNat_ofNat,
      Nat.mod_eq_of_lt hd.pz_lt] at this
  have hpo : (semXIR I (parseIR pz) s0).o = #[] := by rw [parse_o, ← hs0, initSt_o]
  generalize hs1 : semXIR I (parseIR pz) s0 = s1 at h1 hpi hpo
  have hB : BoundsOk I inp.length (extIRWith pz dec) s0 := by
    rw [extIRWith, boundsOk_seq]
    refine ⟨boundsOk_of_safe (safe_parseIR pz _ _) hwf.1 _ h0, ?_⟩
    rw [hs1, boundsOk_ite]
    by_cases hk : rd s1.M rIsK = 0
    · rw [if_pos hk]
      exact boundsOk_of_safe (safe_wIR (by omega) h4 (by omega)) hwf.2.2 _ h1
    · rw [if_neg hk, boundsOk_ite]
      by_cases hz : rd s1.M rIsSz = 0
      · rw [if_pos hz]; trivial
      · rw [if_neg hz]
        exact boundsOk_of_safe (hsafe (hpi hz)) hd.wf _ h1
  have hrun := run_toProg (P := extIRWith pz dec) (input := inp) (f := fuel inp.length) hreg hwf
    (by rw [hs0, hI]; exact hB) (fuel_coversM hd.cost _)
  rw [hs0, hI] at hrun
  refine ⟨_, hrun, ?_⟩
  by_cases hk : rd s1.M rIsK = 0
  · have e : semXIR I (extIRWith pz dec) s0 = semXIR I wIR s1 := by
      rw [extIRWith, semXIR_seq, hs1, semXIR_ite, if_pos hk]
    have hw : (ceil8 (I.getD 4 0)).toNat = (a + 7) / 8 := by rw [h4, toNat_ceil8 (by omega)]
    have := congrArg List.length ((congrArg (fun s' : St => s'.o.toList) e).trans
      (wIR_sem I _ h1 (by omega)))
    simp only [hpo, hw, Array.toList_empty, List.nil_append, List.length_map,
      List.length_range] at this
    rw [this, outCap]
    omega
  · by_cases hz : rd s1.M rIsSz = 0
    · have e : semXIR I (extIRWith pz dec) s0 = semXIR I (.blk []) s1 := by
        rw [extIRWith, semXIR_seq, hs1, semXIR_ite, if_neg hk, semXIR_ite, if_pos hz]
      have hl : (semXIR I (extIRWith pz dec) s0).o.toList.length = 0 := by
        rw [e]; simp [semXIR, hpo]
      rw [hl]; exact Nat.zero_le _
    · have e : semXIR I (extIRWith pz dec) s0 = semXIR I dec s1 := by
        rw [extIRWith, semXIR_seq, hs1, semXIR_ite, if_neg hk, semXIR_ite, if_neg hz]
      have := outs_le (I := I) inp.length dec _ hd.wf h1
        (boundsOk_of_safe (hsafe (hpi hz)) hd.wf _ h1)
      rw [hpo, ← e] at this
      have h2 := hd.outs inp.length
      simp only [Array.size_empty, Nat.zero_add] at this
      rw [Array.length_toList]; exact this.trans h2

theorem computesWithM {pz : ℕ} {dec : XIR} (hd : DecOkM pz dec) :
    Computes (extWithM pz dec) (Eden memM mpwX (extIRWith pz dec)) fuel :=
  computes_Eof fuel (by simp only [regs, memM]; norm_num) (wf_extIRWith (pz := pz) hd.wf)
    fun c π L h1 h2 h3 => halts_of_tapeM hd _ π.size h1 (by rw [getD_toArray, tape_getD4])
      (tape_length c π L) fun h => hd.safe c π L h h2 h3

/-! ## M′'s extractor -/

/-- **M′'s SNARK branch meets `DecOkM`.** -/
theorem decOk_decXM : DecOkM (piSize pX) decXM where
  pz_lt := by rw [piSize_eq]; norm_num
  wf := wf_decXM
  safe := fun c π L hs hq ht => safe_decXM c π L hs hq ht
  cost := fun t => by
    have := cost_decXM t
    simp only [decBudgetM, fuelBase, fuelPerWord]
    omega
  outs := outs_decXM
  size := sizeIR_decXM

/-- **M′'s extractor program.** -/
def extXM : XProg := extWithM (piSize pX) decXM

/-- The in-domain extractor: the program's decoded denotation. -/
def EdXM : Digest → Proof → Log → Option Wit := Eden memM mpwX (extIRWith (piSize pX) decXM)

/-- **M′'s extractor specification**: `EdXM` on the domain, the shipped `EoutX A` outside (`A`: the certificate's
`S.acc`). -/
def EXM (A : Digest → Digest → Signed → Bool) (c : Digest) (π : Proof) (L : Log) : Option Wit :=
  if InDomE c π L then EdXM c π L else EoutX A c π L

/-- **`Computes extXM (EXM A) fuel`** with the declared fuel `2^46 + 2^13 t`. -/
theorem computesXM (A : Digest → Digest → Signed → Bool) : Computes extXM (EXM A) fuel :=
  fun c π L h1 h2 h3 => by
    obtain ⟨o, ho, hl, hd⟩ := computesWithM decOk_decXM c π L h1 h2 h3
    exact ⟨o, ho, hl, hd.trans (if_pos ⟨h1, h2, h3⟩).symm⟩

/-- The certificate's caps on M′'s extractor: the fuel within `B`, the program within `progCap`. -/
theorem extXM_caps : (∀ t, fuel t ≤ extractorBudget t) ∧ extXM.body.size ≤ progCap :=
  ⟨fuel_le_budget, size_extWithM decOk_decXM.size⟩

/-! ## The `W` kind -/

theorem run_W_tapeM (inp : List Word) (a : ℕ) (ha : a < 2 ^ 64)
    (h4 : inp.toArray.getD 4 0 = toWord a) (hlen : (a + 7) / 8 + 6 ≤ inp.length)
    (hk : a ≠ 0 → ¬ (inp.toArray.getD 5 0 &&& 0xFF = kindS)) :
    extXM.run inp (fuel inp.length) =
      some ((List.range ((a + 7) / 8)).map fun j => inp.toArray.getD (5 + j) 0) := by
  have hd := decOk_decXM
  have hwf := wf_extIRWith (pz := piSize pX) hd.wf
  have hreg : regs ≤ memM := by simp only [regs, memM]; norm_num
  have h0 : Inv (initSt (memM + mpwX * inp.length)).M := inv_initSt (Nat.le_add_right_of_le hreg)
  generalize hs0 : initSt (memM + mpwX * inp.length) = s0 at h0
  generalize hI : inp.toArray = I at h4 hk ⊢
  have h1 : Inv (semXIR I (parseIR (piSize pX)) s0).M := inv_sem I hwf.1 h0
  have hz0 : a = 0 → rd (semXIR I (parseIR (piSize pX)) s0).M rIsSz = 0 := by
    intro h
    rw [parse_regs _ I s0 h0, h4, h, if_neg]
    intro he
    have := congrArg BitVec.toNat he
    rw [toNat_toWord (by omega), BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by rw [piSize_eq]; omega),
      piSize_eq] at this
    omega
  have hk' : a ≠ 0 → rd (semXIR I (parseIR (piSize pX)) s0).M rIsK = 0 := fun h => by
    rw [parse_isK _ I s0 h0, if_neg (hk h)]
  have hpo : (semXIR I (parseIR (piSize pX)) s0).o = #[] := by rw [parse_o, ← hs0, initSt_o]
  have hw : (ceil8 (I.getD 4 0)).toNat = (a + 7) / 8 := by rw [h4, toNat_ceil8 ha]
  generalize hs1 : semXIR I (parseIR (piSize pX)) s0 = s1 at h1 hz0 hk' hpo
  have hB : BoundsOk I inp.length (extIRWith (piSize pX) decXM) s0 := by
    rw [extIRWith, boundsOk_seq]
    refine ⟨boundsOk_of_safe (safe_parseIR _ _ _) hwf.1 _ h0, ?_⟩
    rw [hs1, boundsOk_ite]
    by_cases hk1 : rd s1.M rIsK = 0
    · rw [if_pos hk1]
      exact boundsOk_of_safe (safe_wIR ha h4 (by omega)) hwf.2.2 _ h1
    · have ha0 : a = 0 := by by_contra h; exact hk1 (hk' h)
      rw [if_neg hk1, boundsOk_ite, if_pos (hz0 ha0)]; trivial
  have hrun := run_toProg (P := extIRWith (piSize pX) decXM) (input := inp) (f := fuel inp.length) hreg hwf
    (by rw [hs0, hI]; exact hB) (fuel_coversM hd.cost _)
  rw [hs0, hI] at hrun
  refine hrun.trans (congrArg some ?_)
  by_cases hk1 : rd s1.M rIsK = 0
  · have e : semXIR I (extIRWith (piSize pX) decXM) s0 = semXIR I wIR s1 := by
      rw [extIRWith, semXIR_seq, hs1, semXIR_ite, if_pos hk1]
    rw [congrArg (fun s' : St => s'.o.toList) e, wIR_sem I _ h1 (by omega), hpo, hw]
    rfl
  · have ha0 : a = 0 := by by_contra h; exact hk1 (hk' h)
    have e : semXIR I (extIRWith (piSize pX) decXM) s0 = semXIR I (.blk []) s1 := by
      rw [extIRWith, semXIR_seq, hs1, semXIR_ite, if_neg hk1, semXIR_ite, if_pos (hz0 ha0)]
    rw [congrArg (fun s' : St => s'.o.toList) e, ha0]
    simp [semXIR, hpo]

/-- **`EXM` on a `W` proof** (first byte not `'S'`), on every log: `WitnessSending.decode π`. -/
theorem EXM_W (A : Digest → Digest → Signed → Bool) (c : Digest) (π : Proof) (L : Log)
    (hW : π.data[0]? ≠ some 0x53) : EXM A c π L = WitnessSending.decode π := by
  by_cases hD : InDomE c π L
  · rw [EXM, if_pos hD, EdXM]
    have hπ : π.size < 2 ^ 64 := by have := hD.1; rw [outCap] at this; omega
    have hrun := run_W_tapeM (extractorInput c π L) π.size hπ (by rw [getD_toArray, tape_getD4])
      (tape_length c π L) (fun hne he => by
        obtain ⟨b, hb⟩ : ∃ b, π.data[0]? = some b := by
          rcases h : π.data[0]? with _ | b
          · rw [Array.getElem?_eq_none_iff] at h; exact (hne (Nat.le_zero.mp h)).elim
          · exact ⟨b, rfl⟩
        have h1 := tape_byte0 c π L hb
        have h2 := congrArg BitVec.toNat he
        rw [lowByte, getD_toArray, h1] at h2
        exact hW (by rw [hb]; congr 1; exact UInt8.toNat_inj.mp h2))
    rw [Eden, ← den_of_run (by simp only [regs, memM]; norm_num) (wf_extIRWith decOk_decXM.wf) hrun,
      WitnessSending.decode]
    congr 1
    refine List.ext_getElem (by
      simp only [List.length_map, List.length_range, packBytes_length]
      rw [WitnessSending.size_eq_length]) fun j _ h2 => ?_
    simp only [List.getElem_map, List.getElem_range, getD_toArray]
    exact tape_getD_proof c π L (by rwa [packBytes_length, ← WitnessSending.size_eq_length] at h2)
  · rw [EXM, if_neg hD, EoutX, if_neg hW]

end Lvm.X
