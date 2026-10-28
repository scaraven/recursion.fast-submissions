-- New for `flock-recursive` (BLUEPRINT §6.1, §6.4; stage S-H2, track L-ext).
import FRXProg
import RecursionFast.Library.WitnessSending

/-!
# `ext` halts within its fuel: `Computes`

BLUEPRINT §6.1 (B-8, revision 3.17). The extractor specification is the program's **denotation**,
`Eden mem mpw P c π L = decodeWit (den mem mpw P (extractorInput c π L))`, with `den` the output
of `semXIR` from the prologue's state: a total, computable Lean function on every tape, with no
fuel. On every tape on which the machine halts, its output is the denotation (`den_of_run`), so
`Computes (toProg mem mpw P) (Eden mem mpw P) fuel` asks only that the program halt within `fuel`
with at most `outCap` words on every domain tape (`computes_Eof`).

* `parse_regs`: what the parse leaves in `rIsSz` (the `|π| = piSize` flag).
* `wIR_sem`: **the `W` branch's output** is the tape words `5 … 5 + ⌈w/8⌉ − 1`, `w` tape word 4.
* `computesWith`: for every SNARK branch with `DecOk dec`, `Computes (extWith dec) (Eden …) fuel`.
* `E_W` (`FRXSpec`): on a `W` proof (`kindOf π = .W`) of fewer than `2^64` bytes, on every log,
  `extWith dec` outputs `packBytes π`, so `Eden` is `WitnessSending.decode π` (the `W` case of
  `ext_good_tape`, on every size below the word, BP-C-R2-M2).
* The domain (core PR #20, V4-A11): proofs of at most `8 · outCap` bytes (`proofCap` is gone); the
  `W` copy of such a proof is at most `outCap` words (`halts_of_tape`).
-/

namespace FR.X

open RecursionFast

/-- **The denotation of `toProg mem mpw P`** on a tape (revision 3.17): the output of `semXIR`
from the prologue's state on `mem + mpw · t` words. A total function of the tape: no fuel. -/
def den (mem mpw : ℕ) (P : XIR) (inp : List Word) : List Word :=
  (semXIR inp.toArray P (initSt (mem + mpw * inp.length))).o.toList

/-- **B-8 (revision 3.17)**: the extractor specification as the decoded denotation. -/
def Eden (mem mpw : ℕ) (P : XIR) : Digest → Proof → Log → Option Wit :=
  fun c π L => decodeWit (den mem mpw P (extractorInput c π L))

/-- **A halting run outputs the denotation**, with any fuel: the compiled code runs to
`semXIR`'s state in `steps + 8` steps (`runs_body`, no loop bound needed), and more fuel does not
change a halting run (`exec_mono`). -/
theorem den_of_run {mem mpw : ℕ} {P : XIR} {inp : List Word} {f : ℕ} {o : List Word}
    (hmem : regs ≤ mem) (hP : WF P) (h : (toProg mem mpw P).run inp f = some o) :
    o = den mem mpw P inp := by
  have hr := runs_body (I := inp.toArray) P (m := mem + mpw * inp.length) (by omega) hP
  have hm : (toProg mem mpw P).memFor inp.length = mem + mpw * inp.length := rfl
  have hle : (toProg mem mpw P).memFor inp.length ≤ f := by
    by_contra hlt
    rw [XProg.run_lt_mem (by omega)] at h; cases h
  generalize steps inp.toArray P (initSt (mem + mpw * inp.length)) + 8 = n at hr
  have h1 : (toProg mem mpw P).run inp (f + (mem + mpw * inp.length + n)) =
      some (den mem mpw P inp) :=
    XProg.run_of_runs (p := toProg mem mpw P) (by rw [hm]; exact hr) (by omega)
  rw [XProg.run_eq hle] at h
  rw [XProg.run_eq (by omega), show f + (mem + mpw * inp.length + n) -
      (toProg mem mpw P).memFor inp.length = f - (toProg mem mpw P).memFor inp.length +
        (mem + mpw * inp.length + n) by omega, XStmt.exec_mono h] at h1
  exact Option.some.inj h1

/-- **`Computes` for the denotation** (B-8, `compile_runs` + the fuel): it is halting within the
fuel with at most `outCap` words on the domain, since a halting run's output is `den`. -/
theorem computes_Eof {mem mpw : ℕ} {P : XIR} (fuel : ℕ → ℕ) (hmem : regs ≤ mem) (hP : WF P)
    (h : ∀ c (π : Proof) (L : Log), π.size ≤ 8 * outCap → (∀ e ∈ L, e.1.size < 2 ^ 64) →
      (extractorInput c π L).length ≤ 2 ^ 64 →
      ∃ o, (toProg mem mpw P).run (extractorInput c π L) (fuel (extractorInput c π L).length) =
        some o ∧ o.length ≤ outCap) :
    Computes (toProg mem mpw P) (Eden mem mpw P) fuel := by
  intro c π L h1 h2 h3
  obtain ⟨o, ho, hl⟩ := h c π L h1 h2 h3
  exact ⟨o, ho, hl, by rw [den_of_run hmem hP ho]; rfl⟩

/-! ## Words -/

theorem toNat_ceil8 {a : ℕ} (h : a < 2 ^ 64) : (ceil8 (toWord a)).toNat = (a + 7) / 8 := by
  have h7 : (toWord a &&& 7).toNat = a % 8 := by
    rw [BitVec.toNat_and, toNat_toWord h, show (7 : Word).toNat = 2 ^ 3 - 1 from rfl,
      Nat.and_two_pow_sub_one_eq_mod]
  have hs : (toWord a >>> 3).toNat = a / 8 := by
    rw [BitVec.toNat_ushiftRight, toNat_toWord h, Nat.shiftRight_eq_div_pow]
  have hlt : ((0 : Word) < toWord a &&& 7) ↔ 0 < a % 8 := by
    rw [BitVec.lt_def, h7]; rfl
  unfold ceil8
  by_cases h0 : 0 < a % 8
  · rw [if_pos (hlt.2 h0), BitVec.toNat_add, hs, show (1 : Word).toNat = 1 from rfl]; omega
  · rw [if_neg (fun h' => h0 (hlt.1 h')), BitVec.toNat_add, hs, show (0 : Word).toNat = 0 from rfl]
    omega

/-! ## The domain tape -/

section Tape

variable (c : Digest) (π : Proof) (L : Log)

theorem tape_eq : extractorInput c π L =
    (packBytes c.toList ++ [toWord π.size]) ++ packBytes π.data.toList ++ logWords L :=
  WitnessSending.extractorInput_eq c π L

theorem tape_len5 : (packBytes c.toList ++ [toWord π.size]).length = 5 := by
  simp [packBytes_digest_length]

theorem tape_getD4 : (extractorInput c π L).getD 4 0 = toWord π.size := by
  rw [tape_eq, List.append_assoc, List.append_assoc, List.singleton_append,
    show 4 = (packBytes c.toList).length from (packBytes_digest_length c).symm, getD_append_length]

theorem tape_length : (π.size + 7) / 8 + 6 ≤ (extractorInput c π L).length := by
  rw [tape_eq]
  simp only [List.length_append, logWords, List.length_cons, packBytes_length,
    ← WitnessSending.size_eq_length, Vector.length_toList]
  omega

theorem tape_getD_proof {j : ℕ} (hj : j < (π.size + 7) / 8) :
    (extractorInput c π L).getD (5 + j) 0 = (packBytes π.data.toList)[j]'(by
      rw [packBytes_length, ← WitnessSending.size_eq_length]; exact hj) := by
  rw [tape_eq, show 5 + j = (packBytes c.toList ++ [toWord π.size]).length + j by
    rw [tape_len5]]
  exact getD_append_mid _ _ _ _

end Tape

/-! ## The parse -/

theorem parse_regs (I : Array Word) (s : St) (hM : Inv s.M) :
    rd (semXIR I parseIR s).M rIsSz =
      (if I.getD 4 0 = BitVec.ofNat 64 piSize then 1 else 0) := by
  have hs := hM.1
  simp only [regs] at hs
  simp only [parseIR, readAt, kindPs, semXIR, runPrims, List.foldl, Prim.run, rA, rLen, rK, rB0,
    rIsK, rT, rIsSz]
  simp (disch := first | decide | omega | (simp only [size_set]; omega)) [rd_set_self, rd_set_ne, XOp.eval]

/-- What `wPre` leaves: the count `⌈w/8⌉` (`w` tape word 4) and the start position `5`. -/
theorem wPre_regs (I : Array Word) (s : St) (hM : Inv s.M) :
    rd (semXIR I wPre s).M rCnt = ceil8 (I.getD 4 0) ∧ rd (semXIR I wPre s).M rPos = 5 := by
  have hs := hM.1
  simp only [regs] at hs
  simp only [wPre, readAt, wCntPs, semXIR, runPrims, List.foldl, Prim.run, rA, rLen, rK, rCnt, rT,
    rPos]
  refine ⟨?_, ?_⟩ <;>
    simp (disch := first | decide | omega | (simp only [size_set]; omega)) [rd_set_self, rd_set_ne, XOp.eval, ceil8]

theorem wf_wBody : WF wBody := by
  simp [wBody, WF, Prim.dst, rW, rPos]

theorem wf_wPre : WF wPre := by
  simp [wPre, readAt, wCntPs, WF, Prim.dst, rA, rLen, rK, rCnt, rT, rPos]

theorem parse_o (I : Array Word) (s : St) : (semXIR I parseIR s).o = s.o := by
  simp [parseIR, readAt, semXIR]

theorem wf_wIR : WF wIR := by
  simp [wIR, wPre, readAt, wCntPs, wBody, WF, Writes, Prim.dst, rA, rLen, rK, rCnt, rT, rW, rPos,
    rC, regs, cTmp]

/-- **The `W` loop's run**: `k` iterations from position `p` output tape words `p … p + k − 1`. -/
theorem wLoop (I : Array Word) : ∀ (k p : ℕ) (s : St), Inv s.M → rd s.M rPos = toWord p →
    p + k < 2 ^ 64 →
    (iterL (semXIR I wBody) rC k s).o.toList = s.o.toList ++ (List.range k).map
      (fun j => I.getD (p + j) 0)
  | 0, _, _, _, _, _ => by simp [iterL]
  | k + 1, p, s, hM, hp, hk => by
    have hs := hM.1
    simp only [regs] at hs
    have h1 : rd s.M cOne = 1 := hM.2 0 (by decide)
    have hf : Inv (decS rC (semXIR I wBody s)).M := inv_of_frame (inv_sem I wf_wBody hM)
      (size_decS ..) fun i hi => rd_decS (by simp only [rC]; omega) _
    have hpos : rd (decS rC (semXIR I wBody s)).M rPos = toWord (p + 1) := by
      simp only [decS, wBody, semXIR, runPrims, List.foldl, Prim.run, rC, rPos, rW, cOne] at hp h1 ⊢
      simp (disch := first | decide | omega | (simp only [size_set]; omega)) [rd_set_self, rd_set_ne, XOp.eval, hp, h1]
      exact toWord_add_one p
    have ho : (decS rC (semXIR I wBody s)).o.toList = s.o.toList ++ [I.getD p 0] := by
      simp only [decS, wBody, semXIR, runPrims, List.foldl, Prim.run, rC, rPos, rW] at hp ⊢
      simp (disch := first | decide | omega | (simp only [size_set]; omega)) [rd_set_self, rd_set_ne, hp,
        toNat_toWord (show p < 2 ^ 64 by omega)]
    simp only [iterL]
    rw [wLoop I k (p + 1) _ hf hpos (by omega), ho, List.range_succ_eq_map]
    simp [Function.comp_def, Nat.add_assoc, Nat.add_comm 1]

/-- **The `W` branch's output**: the `⌈w/8⌉` tape words from word 5, `w` tape word 4. -/
theorem wIR_sem (I : Array Word) (s : St) (hM : Inv s.M)
    (hw : (ceil8 (I.getD 4 0)).toNat + 5 < 2 ^ 64) :
    (semXIR I wIR s).o.toList = s.o.toList ++ (List.range (ceil8 (I.getD 4 0)).toNat).map
      (fun j => I.getD (5 + j) 0) := by
  have hM' := inv_sem I wf_wPre hM
  obtain ⟨hcnt, hpos⟩ := wPre_regs I s hM
  have hs := hM'.1
  simp only [regs] at hs
  have h0 : Inv (entryT rC rCnt (semXIR I wPre s).M) := inv_of_frame hM' (size_entryT ..)
    fun i hi => entryT_frame _ (by simp only [rC]; omega)
  have hc : rC < (semXIR I wPre s).M.size := by simp only [rC]; omega
  have hp : rd (entryT rC rCnt (semXIR I wPre s).M) rPos = toWord 5 := by
    rw [entryT_frame _ (by simp only [rC, rPos]; omega), hpos]; exact (toWord_add_one 4).trans rfl
  have ho : (semXIR I wPre s).o = s.o := by simp [wPre, readAt, semXIR]
  have e : semXIR I wIR s = iterL (semXIR I wBody) rC (ceil8 (I.getD 4 0)).toNat
      ⟨entryT rC rCnt (semXIR I wPre s).M, (semXIR I wPre s).o⟩ := by
    simp only [wIR, semXIR, rd_entryT hc, hcnt]
  refine (congrArg (fun s' : St => s'.o.toList) e).trans ?_
  rw [ho]
  generalize entryT rC rCnt (semXIR I wPre s).M = M0 at h0 hp
  exact wLoop I _ 5 ⟨M0, s.o⟩ h0 hp (by omega)

/-! ## Loop bounds and output on the domain -/

theorem boundsOk_seq {I : Array Word} {t : ℕ} {p q : XIR} {s : St} :
    BoundsOk I t (.seq p q) s ↔ BoundsOk I t p s ∧ BoundsOk I t q (semXIR I p s) := Iff.rfl

theorem boundsOk_ite {I : Array Word} {t c : ℕ} {p q : XIR} {s : St} :
    BoundsOk I t (.ite c p q) s ↔ if rd s.M c = 0 then BoundsOk I t q s else BoundsOk I t p s :=
  Iff.rfl

theorem semXIR_seq (I : Array Word) (p q : XIR) (s : St) :
    semXIR I (.seq p q) s = semXIR I q (semXIR I p s) := rfl

theorem semXIR_ite (I : Array Word) (c : ℕ) (p q : XIR) (s : St) :
    semXIR I (.ite c p q) s = if rd s.M c = 0 then semXIR I q s else semXIR I p s := rfl

/-- The `W` branch's loop bound, when tape word 4 is `a` and the tape has `⌈a/8⌉` words. -/
theorem safe_wIR {I : Array Word} {t a : ℕ} (ha : a < 2 ^ 64) (h4 : I.getD 4 0 = toWord a)
    (hlen : (a + 7) / 8 ≤ t) : Safe I t wIR := by
  refine .loopT (.seq (.seq (.blk _) (.input _ _)) (.blk _)) (fun s hM => ?_) (.seq (.input _ _)
    (.seq (.out _) (.blk _)))
  rw [(wPre_regs _ s hM).1, h4, toNat_ceil8 ha]
  simp only [Aff.eval, Nat.div_one]; omega

theorem safe_parseIR (I : Array Word) (t : ℕ) : Safe I t parseIR :=
  .seq (.seq (.blk _) (.input _ _)) (.seq (.seq (.blk _) (.input _ _)) (.blk _))

/-- **The program halts within the fuel with at most `outCap` words** on a tape whose word 4 is a
length `a ≤ 8 · outCap` (the contract's domain since core PR #20) followed by at least `⌈a/8⌉`
words, when the SNARK branch satisfies `DecOk` and its loop bounds hold on the tape whenever
`a = piSize`. -/
theorem halts_of_tape {dec : XIR} (hd : DecOk dec) (inp : List Word) (a : ℕ) (ha : a ≤ 8 * outCap)
    (h4 : inp.toArray.getD 4 0 = toWord a) (hlen : (a + 7) / 8 + 6 ≤ inp.length)
    (hsafe : a = piSize → Safe inp.toArray inp.length dec) :
    ∃ o, (extWith dec).run inp (fuel inp.length) = some o ∧ o.length ≤ outCap := by
  rw [outCap] at ha
  have hwf := wf_extIRWith hd.wf
  have hreg : regs ≤ memX := by simp only [regs, memX]; norm_num
  have h0 : Inv (initSt (memX + mpwX * inp.length)).M := inv_initSt (Nat.le_add_right_of_le hreg)
  generalize hs0 : initSt (memX + mpwX * inp.length) = s0 at h0
  generalize hI : inp.toArray = I at h4 hsafe
  have h1 : Inv (semXIR I parseIR s0).M := inv_sem I hwf.1 h0
  have hpi : rd (semXIR I parseIR s0).M rIsSz ≠ 0 → a = piSize := by
    intro h
    rw [parse_regs I s0 h0, h4] at h
    by_contra hne
    refine h (if_neg fun he => hne ?_)
    have := congrArg BitVec.toNat he
    rwa [toNat_toWord (by omega), BitVec.toNat_ofNat,
      Nat.mod_eq_of_lt (by rw [piSize_eq]; omega)] at this
  have hpo : (semXIR I parseIR s0).o = #[] := by rw [parse_o, ← hs0, initSt_o]
  generalize hs1 : semXIR I parseIR s0 = s1 at h1 hpi hpo
  -- the loop bounds
  have hB : BoundsOk I inp.length (extIRWith dec) s0 := by
    rw [extIRWith, boundsOk_seq]
    refine ⟨boundsOk_of_safe (safe_parseIR _ _) hwf.1 _ h0, ?_⟩
    rw [hs1, boundsOk_ite]
    by_cases hk : rd s1.M rIsK = 0
    · rw [if_pos hk]
      exact boundsOk_of_safe (safe_wIR (by omega) h4 (by omega)) hwf.2.2 _ h1
    · rw [if_neg hk, boundsOk_ite]
      by_cases hz : rd s1.M rIsSz = 0
      · rw [if_pos hz]; trivial
      · rw [if_neg hz]
        exact boundsOk_of_safe (hsafe (hpi hz)) hd.wf _ h1
  have hrun := run_toProg (P := extIRWith dec) (input := inp) (f := fuel inp.length) hreg hwf
    (by rw [hs0, hI]; exact hB) (fuel_covers hd.cost _)
  rw [hs0, hI] at hrun
  refine ⟨_, hrun, ?_⟩
  -- the output
  by_cases hk : rd s1.M rIsK = 0
  · have e : semXIR I (extIRWith dec) s0 = semXIR I wIR s1 := by
      rw [extIRWith, semXIR_seq, hs1, semXIR_ite, if_pos hk]
    have hw : (ceil8 (I.getD 4 0)).toNat = (a + 7) / 8 := by rw [h4, toNat_ceil8 (by omega)]
    have := congrArg List.length ((congrArg (fun s' : St => s'.o.toList) e).trans
      (wIR_sem I _ h1 (by omega)))
    simp only [hpo, hw, Array.toList_empty, List.nil_append, List.length_map,
      List.length_range] at this
    rw [this, outCap]
    omega
  · by_cases hz : rd s1.M rIsSz = 0
    · have e : semXIR I (extIRWith dec) s0 = semXIR I (.blk []) s1 := by
        rw [extIRWith, semXIR_seq, hs1, semXIR_ite, if_neg hk, semXIR_ite, if_pos hz]
      have hl : (semXIR I (extIRWith dec) s0).o.toList.length = 0 := by
        rw [e]; simp [semXIR, hpo]
      rw [hl]; exact Nat.zero_le _
    · have e : semXIR I (extIRWith dec) s0 = semXIR I dec s1 := by
        rw [extIRWith, semXIR_seq, hs1, semXIR_ite, if_neg hk, semXIR_ite, if_neg hz]
      have := outs_le (I := I) inp.length dec _ hd.wf h1
        (boundsOk_of_safe (hsafe (hpi hz)) hd.wf _ h1)
      rw [hpo, ← e] at this
      have h2 := hd.outs inp.length
      simp only [Array.size_empty, Nat.zero_add] at this
      rw [Array.length_toList]; exact this.trans h2

/-- **The program halts within the fuel** with at most `outCap` words on every domain tape, for
every SNARK branch satisfying `DecOk`. -/
theorem halts_with {dec : XIR} (hd : DecOk dec) (c : Digest) (π : Proof) (L : Log)
    (hπ : π.size ≤ 8 * outCap) (hq : ∀ e ∈ L, e.1.size < 2 ^ 64)
    (ht : (extractorInput c π L).length ≤ 2 ^ 64) :
    ∃ o, (extWith dec).run (extractorInput c π L) (fuel (extractorInput c π L).length) = some o ∧
      o.length ≤ outCap :=
  halts_of_tape hd _ π.size hπ (by rw [getD_toArray, tape_getD4]) (tape_length c π L)
    fun h => hd.safe c π L h hq ht

/-- **`Computes`** for every SNARK branch with `DecOk`. -/
theorem computesWith {dec : XIR} (hd : DecOk dec) :
    Computes (extWith dec) (Eden memX mpwX (extIRWith dec)) fuel :=
  computes_Eof fuel (by simp only [regs, memX]; norm_num) (wf_extIRWith hd.wf)
    fun c π L h1 h2 h3 => halts_with hd c π L h1 h2 h3

end FR.X
