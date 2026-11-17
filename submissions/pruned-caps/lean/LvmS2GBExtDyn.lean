-- New for lvm2 MP-B cap pruning (CAP-X, 2026-11-17): S2GB's log reads with the log position computed from `|π|`
-- (the S2GS reads take it as a constant), and their simulation of the S2GS reads (`LvmS2GBExtSim`).
import LvmS2GBExtSim
import LvmXChainL
import LvmMPXRead

/-!
# The log position from the tape

The S2GS reads use the log position `pL = posL |π|` as a program constant in seven places (the prefixes of the walk,
the sort's passes, the sort, the lookup, the chain's count and start). At S2GB `|π|` varies, so each such prefix is
replaced by one that reads `|π|` (tape word 4) and computes `pL = 5 + (|π| + 7) / 8` (`pLIR`), writing only the
registers the S2GS prefix writes, and leaving them with the same values (`*_sim`). The parents (`walkIR4D`, `idxIR4D`,
`lookIR4D`, `crNodeD`, `crLeafD`, `readGIRD`, `cntIRD`, `chainIRD`) are the S2GS programs with these prefixes, and
simulate them (`Sim`).
-/

set_option autoImplicit false

namespace Lvm.XB

open RecursionFast Lvm.X

/-! ## The log position -/

/-- `r := 5 + ((tape[4] + 7) >> 3)`, with `k` as constant scratch (`k = 5` after). -/
def pLIR (r k : ℕ) : XIR :=
  .seq (.blk [.const r 4]) (.seq (.input r r)
    (.blk [.const k 7, .op .add r r k, .const k 3, .op .shr r r k, .const k 5, .op .add r r k]))

/-- The word `pLIR` computes from tape word 4. -/
def pLW (I : Array Word) : Word := XOp.eval .add (XOp.eval .shr (XOp.eval .add (I.getD 4 0) 7) 3) 5

/-- **`pLW` is the log position** on a tape whose word 4 is `|π|`. -/
theorem pLW_eq {I : Array Word} {sz : ℕ} (h4 : I.getD 4 0 = toWord sz) (hsz : sz + 7 < 2 ^ 64) :
    pLW I = BitVec.ofNat 64 (posL sz) := by
  rw [pLW, h4, posL]
  simp only [XOp.eval]
  apply BitVec.eq_of_toNat_eq
  have h3 : (3 : Word).toNat % 64 = 3 := rfl
  have e7 : BitVec.toNat (7 : Word) = 7 := rfl
  have e5 : BitVec.toNat (5 : Word) = 5 := rfl
  rw [h3, BitVec.toNat_add, BitVec.toNat_ushiftRight, BitVec.toNat_add, toNat_toWord (by omega), e7, e5,
    BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega), Nat.shiftRight_eq_div_pow]
  rw [Nat.mod_eq_of_lt (show sz + 7 < 2 ^ 64 by omega), Nat.mod_eq_of_lt (show 5 + (sz + 7) / 8 < 2 ^ 64 by omega)]
  omega

/-- Two memories with the same size and the same cells are equal. -/
theorem mem_ext {M M' : Mem} (hs : M.size = M'.size) (h : ∀ i, Lvm.X.rd M i = Lvm.X.rd M' i) : M = M' := by
  apply Array.ext hs
  intro i h1 h2
  have := h i
  simp only [Lvm.X.rd, Array.getD_eq_getD_getElem?, Array.getElem?_eq_getElem h1, Array.getElem?_eq_getElem h2,
    Option.getD_some] at this
  exact this

/-! ## The walk's prefix -/

/-- **The walk's prefix from the tape** (`walkPre4` with `pL` from `|π|`). -/
def walkPre4D (bX : ℕ) : XIR :=
  .seq (pLIR rA rN) (.seq (.blk [.op .add rP rA cOne, .const rXA (BitVec.ofNat 64 bX)]) (.input rN rA))

theorem walkPre4D_sim {I : Array Word} {pL : ℕ} (hv : pLW I = BitVec.ofNat 64 pL) (bX : ℕ) :
    Sim I (walkPre4 bX pL) (walkPre4D bX) := by
  refine .leaf (fun s hs => ?_) (by simp +decide [walkPre4D, pLIR, WF, Prim.dst, rA, rN, rP, rXA])
    (fun i hi => ?_) (by simp [walkPre4, readAt, NoLoopT]) (by simp [walkPre4D, pLIR, NoLoopT])
  · obtain ⟨M, o⟩ := s
    obtain ⟨hsz, hk⟩ := hs
    have h1 : Lvm.X.rd M cOne = 1 := hk 0 (by decide)
    simp only [regs] at hsz
    simp only [walkPre4D, walkPre4, pLIR, readAt, semXIR, runPrims, List.foldl, Prim.run, St.mk.injEq, and_true]
    apply mem_ext (by simp)
    intro i
    simp only [pLW, Array.getD_eq_getD_getElem?] at hv
    simp only [rA, rN, rP, rXA, cOne] at h1 ⊢
    have h4 : (4 : Word).toNat = 4 := rfl
    have hv' : XOp.add.eval (XOp.shr.eval (XOp.add.eval (I[4]?.getD 0#64) 7#64) 3#64) 5#64 = BitVec.ofNat 64 pL := hv
    by_cases e1 : i = 64
    · subst e1; simp (disch := ((try simp only [size_set, ne_eq]); omega)) [rd_set_self, rd_set_ne, h4, hv', BitVec.ofNat_add]
    by_cases e2 : i = 75
    · subst e2; simp (disch := ((try simp only [size_set, ne_eq]); omega)) [rd_set_self, rd_set_ne, h4, hv', BitVec.ofNat_add]
    by_cases e3 : i = 76
    · subst e3; simp (disch := ((try simp only [size_set, ne_eq]); omega)) [rd_set_self, rd_set_ne, hv', h1, BitVec.ofNat_add]; rfl
    by_cases e4 : i = 77
    · subst e4; simp (disch := ((try simp only [size_set, ne_eq]); omega)) [rd_set_self, rd_set_ne]
    simp (disch := ((try simp only [size_set, ne_eq]); omega)) only [rd_set_ne]
  · simp only [walkPre4D, pLIR, walkPre4, readAt, Writes, List.mem_cons, List.mem_nil_iff, Prim.dst] at hi ⊢
    aesop

/-- The chain count's prefix from the tape (`rP := pL + 1`, `rN := |L|`). -/
def cntPreD : XIR :=
  .seq (pLIR rA rN) (.seq (.blk [.op .add rP rA cOne]) (.input rN rA))

theorem cntPreD_sim {I : Array Word} {pL : ℕ} (hv : pLW I = BitVec.ofNat 64 pL) :
    Sim I (.seq (.blk [.const rP (toWord (pL + 1))]) (readAt rN pL)) (cntPreD) := by
  refine .leaf (fun s hs => ?_) (by simp +decide [cntPreD, pLIR, WF, Prim.dst, rA, rN, rP, cOne])
    (fun i hi => ?_) (by simp [readAt, NoLoopT]) (by simp [cntPreD, pLIR, NoLoopT])
  · obtain ⟨M, o⟩ := s
    obtain ⟨hsz, hk⟩ := hs
    have h1 : Lvm.X.rd M cOne = 1 := hk 0 (by decide)
    simp only [regs] at hsz
    simp only [cntPreD, pLIR, readAt, semXIR, runPrims, List.foldl, Prim.run, St.mk.injEq, and_true]
    apply mem_ext (by simp)
    intro i
    simp only [pLW, Array.getD_eq_getD_getElem?] at hv
    have hv' : XOp.add.eval (XOp.shr.eval (XOp.add.eval (I[4]?.getD 0#64) 7#64) 3#64) 5#64 = BitVec.ofNat 64 pL := hv
    simp only [rA, rN, rP, rP, rN, cOne, toWord] at h1 ⊢
    by_cases erA : i = 64
    · subst erA; (simp (disch := ((try simp only [size_set, ne_eq]); omega)) [rd_set_self, rd_set_ne, hv', h1,
        BitVec.ofNat_add]) <;> rfl
    by_cases erN : i = 75
    · subst erN; (simp (disch := ((try simp only [size_set, ne_eq]); omega)) [rd_set_self, rd_set_ne, hv', h1,
        BitVec.ofNat_add]) <;> rfl
    by_cases erP : i = 76
    · subst erP; (simp (disch := ((try simp only [size_set, ne_eq]); omega)) [rd_set_self, rd_set_ne, hv', h1,
        BitVec.ofNat_add]) <;> rfl
    simp (disch := ((try simp only [size_set, ne_eq]); omega)) only [rd_set_ne]
  · simp only [cntPreD, pLIR, readAt, Writes, List.mem_cons, List.mem_nil_iff, Prim.dst] at hi ⊢
    aesop

/-- The chain count's suffix from the tape (`rCn5 := rP − pL − 1`). -/
def cntPostD : XIR :=
  .seq (pLIR rKd rCn5) (.blk [.op .add rKd rKd cOne, .op .sub rCn5 rP rKd])

theorem cntPostD_sim {I : Array Word} {pL : ℕ} (hv : pLW I = BitVec.ofNat 64 pL) :
    Sim I (.blk [.const rKd (toWord (pL + 1)), .op .sub rCn5 rP rKd]) (cntPostD) := by
  refine .leaf (fun s hs => ?_) (by simp +decide [cntPostD, pLIR, WF, Prim.dst, rKd, rCn5, cOne])
    (fun i hi => ?_) (by simp [readAt, NoLoopT]) (by simp [cntPostD, pLIR, NoLoopT])
  · obtain ⟨M, o⟩ := s
    obtain ⟨hsz, hk⟩ := hs
    have h1 : Lvm.X.rd M cOne = 1 := hk 0 (by decide)
    simp only [regs] at hsz
    simp only [cntPostD, pLIR, readAt, semXIR, runPrims, List.foldl, Prim.run, St.mk.injEq, and_true]
    apply mem_ext (by simp)
    intro i
    simp only [pLW, Array.getD_eq_getD_getElem?] at hv
    have hv' : XOp.add.eval (XOp.shr.eval (XOp.add.eval (I[4]?.getD 0#64) 7#64) 3#64) 5#64 = BitVec.ofNat 64 pL := hv
    simp only [rKd, rCn5, rP, rN, cOne, toWord] at h1 ⊢
    by_cases erKd : i = 210
    · subst erKd; (simp (disch := ((try simp only [size_set, ne_eq]); omega)) [rd_set_self, rd_set_ne, hv', h1,
        BitVec.ofNat_add]) <;> rfl
    by_cases erCn5 : i = 209
    · subst erCn5; (simp (disch := ((try simp only [size_set, ne_eq]); omega)) [rd_set_self, rd_set_ne, hv', h1,
        BitVec.ofNat_add]) <;> rfl
    simp (disch := ((try simp only [size_set, ne_eq]); omega)) only [rd_set_ne]
  · simp only [cntPostD, pLIR, readAt, Writes, List.mem_cons, List.mem_nil_iff, Prim.dst] at hi ⊢
    aesop

/-- The chain's start from the tape (`startPs`). -/
def startD : XIR :=
  .seq (pLIR rWp rEo) (.blk [.op .add rWp rWp cOne, .const rEo 0, .const rPi 0, .const rTl 7, .const rTh 1, .const rTo 0, .const rMt 0])

theorem startD_sim {I : Array Word} {pL : ℕ} (hv : pLW I = BitVec.ofNat 64 pL) :
    Sim I (.blk (startPs pL)) (startD) := by
  refine .leaf (fun s hs => ?_) (by simp +decide [startD, pLIR, WF, Prim.dst, rWp, rEo, rPi, rTl, rTh, rTo, rMt, cOne])
    (fun i hi => ?_) (by simp [startPs, readAt, NoLoopT]) (by simp [startD, pLIR, NoLoopT])
  · obtain ⟨M, o⟩ := s
    obtain ⟨hsz, hk⟩ := hs
    have h1 : Lvm.X.rd M cOne = 1 := hk 0 (by decide)
    simp only [regs] at hsz
    simp only [startD, startPs, pLIR, readAt, semXIR, runPrims, List.foldl, Prim.run, St.mk.injEq, and_true]
    apply mem_ext (by simp)
    intro i
    simp only [pLW, Array.getD_eq_getD_getElem?] at hv
    have hv' : XOp.add.eval (XOp.shr.eval (XOp.add.eval (I[4]?.getD 0#64) 7#64) 3#64) 5#64 = BitVec.ofNat 64 pL := hv
    simp only [rWp, rEo, rPi, rTl, rTh, rTo, rMt, rP, rN, cOne, toWord] at h1 ⊢
    by_cases erWp : i = 191
    · subst erWp; (simp (disch := ((try simp only [size_set, ne_eq]); omega)) [rd_set_self, rd_set_ne, hv', h1,
        BitVec.ofNat_add]) <;> rfl
    by_cases erEo : i = 192
    · subst erEo; (simp (disch := ((try simp only [size_set, ne_eq]); omega)) [rd_set_self, rd_set_ne, hv', h1,
        BitVec.ofNat_add]) <;> rfl
    by_cases erPi : i = 198
    · subst erPi; (simp (disch := ((try simp only [size_set, ne_eq]); omega)) [rd_set_self, rd_set_ne, hv', h1,
        BitVec.ofNat_add]) <;> rfl
    by_cases erTl : i = 195
    · subst erTl; (simp (disch := ((try simp only [size_set, ne_eq]); omega)) [rd_set_self, rd_set_ne, hv', h1,
        BitVec.ofNat_add]) <;> rfl
    by_cases erTh : i = 196
    · subst erTh; (simp (disch := ((try simp only [size_set, ne_eq]); omega)) [rd_set_self, rd_set_ne, hv', h1,
        BitVec.ofNat_add]) <;> rfl
    by_cases erTo : i = 197
    · subst erTo; (simp (disch := ((try simp only [size_set, ne_eq]); omega)) [rd_set_self, rd_set_ne, hv', h1,
        BitVec.ofNat_add]) <;> rfl
    by_cases erMt : i = 194
    · subst erMt; (simp (disch := ((try simp only [size_set, ne_eq]); omega)) [rd_set_self, rd_set_ne, hv', h1,
        BitVec.ofNat_add]) <;> rfl
    simp (disch := ((try simp only [size_set, ne_eq]); omega)) only [rd_set_ne]
  · simp only [startD, startPs, pLIR, readAt, Writes, List.mem_cons, List.mem_nil_iff, Prim.dst] at hi ⊢
    aesop

/-- A merge pass's prefix from the tape (`passPre4`). -/
def passPre4D : XIR :=
  .seq (.blk [.const rI 0, .const rIE 0, .const rJ 0, .const rJE 0, .const rKk 0]) (.seq (pLIR rA rNS) (.input rNS rA))

theorem passPre4D_sim {I : Array Word} {pL : ℕ} (hv : pLW I = BitVec.ofNat 64 pL) :
    Sim I (passPre4 pL) (passPre4D) := by
  refine .leaf (fun s hs => ?_) (by simp +decide [passPre4D, pLIR, WF, Prim.dst, rI, rIE, rJ, rJE, rKk, rA, rNS, cOne])
    (fun i hi => ?_) (by simp [passPre4, readAt, NoLoopT]) (by simp [passPre4D, pLIR, NoLoopT])
  · obtain ⟨M, o⟩ := s
    obtain ⟨hsz, hk⟩ := hs
    have h1 : Lvm.X.rd M cOne = 1 := hk 0 (by decide)
    simp only [regs] at hsz
    simp only [passPre4D, passPre4, pLIR, readAt, semXIR, runPrims, List.foldl, Prim.run, St.mk.injEq, and_true]
    apply mem_ext (by simp)
    intro i
    simp only [pLW, Array.getD_eq_getD_getElem?] at hv
    have hv' : XOp.add.eval (XOp.shr.eval (XOp.add.eval (I[4]?.getD 0#64) 7#64) 3#64) 5#64 = BitVec.ofNat 64 pL := hv
    simp only [rI, rIE, rJ, rJE, rKk, rA, rNS, rP, rN, cOne, toWord] at h1 ⊢
    by_cases erI : i = 86
    · subst erI; (simp (disch := ((try simp only [size_set, ne_eq]); omega)) [rd_set_self, rd_set_ne, hv', h1,
        BitVec.ofNat_add]) <;> rfl
    by_cases erIE : i = 87
    · subst erIE; (simp (disch := ((try simp only [size_set, ne_eq]); omega)) [rd_set_self, rd_set_ne, hv', h1,
        BitVec.ofNat_add]) <;> rfl
    by_cases erJ : i = 88
    · subst erJ; (simp (disch := ((try simp only [size_set, ne_eq]); omega)) [rd_set_self, rd_set_ne, hv', h1,
        BitVec.ofNat_add]) <;> rfl
    by_cases erJE : i = 89
    · subst erJE; (simp (disch := ((try simp only [size_set, ne_eq]); omega)) [rd_set_self, rd_set_ne, hv', h1,
        BitVec.ofNat_add]) <;> rfl
    by_cases erKk : i = 90
    · subst erKk; (simp (disch := ((try simp only [size_set, ne_eq]); omega)) [rd_set_self, rd_set_ne, hv', h1,
        BitVec.ofNat_add]) <;> rfl
    by_cases erA : i = 64
    · subst erA; (simp (disch := ((try simp only [size_set, ne_eq]); omega)) [rd_set_self, rd_set_ne, hv', h1,
        BitVec.ofNat_add]) <;> rfl
    by_cases erNS : i = 104
    · subst erNS; (simp (disch := ((try simp only [size_set, ne_eq]); omega)) [rd_set_self, rd_set_ne, hv', h1,
        BitVec.ofNat_add]) <;> rfl
    simp (disch := ((try simp only [size_set, ne_eq]); omega)) only [rd_set_ne]
  · simp only [passPre4D, passPre4, pLIR, readAt, Writes, List.mem_cons, List.mem_nil_iff, Prim.dst] at hi ⊢
    aesop

/-- The sort's prefix from the tape (`sortPre4`). -/
def sortPre4D (bX : ℕ) : XIR :=
  .seq (pLIR rA rN) (.seq (.input rN rA) (.blk [.const rW2 1, .const rSrc (BitVec.ofNat 64 bX), .op .add rDst rSrc rN, .const rNP 64]))

theorem sortPre4D_sim {I : Array Word} {pL : ℕ} (hv : pLW I = BitVec.ofNat 64 pL) (bX : ℕ) :
    Sim I (sortPre4 bX pL) (sortPre4D bX) := by
  refine .leaf (fun s hs => ?_) (by simp +decide [sortPre4D, pLIR, WF, Prim.dst, rA, rN, rW2, rSrc, rDst, rNP, cOne])
    (fun i hi => ?_) (by simp [sortPre4, readAt, NoLoopT]) (by simp [sortPre4D, pLIR, NoLoopT])
  · obtain ⟨M, o⟩ := s
    obtain ⟨hsz, hk⟩ := hs
    have h1 : Lvm.X.rd M cOne = 1 := hk 0 (by decide)
    simp only [regs] at hsz
    simp only [sortPre4D, sortPre4, pLIR, readAt, semXIR, runPrims, List.foldl, Prim.run, St.mk.injEq, and_true]
    apply mem_ext (by simp)
    intro i
    simp only [pLW, Array.getD_eq_getD_getElem?] at hv
    have hv' : XOp.add.eval (XOp.shr.eval (XOp.add.eval (I[4]?.getD 0#64) 7#64) 3#64) 5#64 = BitVec.ofNat 64 pL := hv
    simp only [rA, rN, rW2, rSrc, rDst, rNP, rP, rN, cOne, toWord] at h1 ⊢
    by_cases erA : i = 64
    · subst erA; (simp (disch := ((try simp only [size_set, ne_eq]); omega)) [rd_set_self, rd_set_ne, hv', h1,
        BitVec.ofNat_add]) <;> rfl
    by_cases erN : i = 75
    · subst erN; (simp (disch := ((try simp only [size_set, ne_eq]); omega)) [rd_set_self, rd_set_ne, hv', h1,
        BitVec.ofNat_add]) <;> rfl
    by_cases erW2 : i = 83
    · subst erW2; (simp (disch := ((try simp only [size_set, ne_eq]); omega)) [rd_set_self, rd_set_ne, hv', h1,
        BitVec.ofNat_add]) <;> rfl
    by_cases erSrc : i = 84
    · subst erSrc; (simp (disch := ((try simp only [size_set, ne_eq]); omega)) [rd_set_self, rd_set_ne, hv', h1,
        BitVec.ofNat_add]) <;> rfl
    by_cases erDst : i = 85
    · subst erDst; (simp (disch := ((try simp only [size_set, ne_eq]); omega)) [rd_set_self, rd_set_ne, hv', h1,
        BitVec.ofNat_add]) <;> rfl
    by_cases erNP : i = 102
    · subst erNP; (simp (disch := ((try simp only [size_set, ne_eq]); omega)) [rd_set_self, rd_set_ne, hv', h1,
        BitVec.ofNat_add]) <;> rfl
    simp (disch := ((try simp only [size_set, ne_eq]); omega)) only [rd_set_ne]
  · simp only [sortPre4D, sortPre4, pLIR, readAt, Writes, List.mem_cons, List.mem_nil_iff, Prim.dst] at hi ⊢
    aesop

/-- The lookup's prefix from the tape (`lookPre4`). -/
def lookPre4D : XIR :=
  .seq (pLIR rA rN) (.seq (.input rN rA) (.blk [.const rLo 0, .op .or rLn rN rN, .const rNB 64]))

theorem lookPre4D_sim {I : Array Word} {pL : ℕ} (hv : pLW I = BitVec.ofNat 64 pL) :
    Sim I (lookPre4 pL) (lookPre4D) := by
  refine .leaf (fun s hs => ?_) (by simp +decide [lookPre4D, pLIR, WF, Prim.dst, rA, rN, rLo, rLn, rNB, cOne])
    (fun i hi => ?_) (by simp [lookPre4, readAt, NoLoopT]) (by simp [lookPre4D, pLIR, NoLoopT])
  · obtain ⟨M, o⟩ := s
    obtain ⟨hsz, hk⟩ := hs
    have h1 : Lvm.X.rd M cOne = 1 := hk 0 (by decide)
    simp only [regs] at hsz
    simp only [lookPre4D, lookPre4, pLIR, readAt, semXIR, runPrims, List.foldl, Prim.run, St.mk.injEq, and_true]
    apply mem_ext (by simp)
    intro i
    simp only [pLW, Array.getD_eq_getD_getElem?] at hv
    have hv' : XOp.add.eval (XOp.shr.eval (XOp.add.eval (I[4]?.getD 0#64) 7#64) 3#64) 5#64 = BitVec.ofNat 64 pL := hv
    simp only [rA, rN, rLo, rLn, rNB, rP, rN, cOne, toWord] at h1 ⊢
    by_cases erA : i = 64
    · subst erA; (simp (disch := ((try simp only [size_set, ne_eq]); omega)) [rd_set_self, rd_set_ne, hv', h1,
        BitVec.ofNat_add]) <;> rfl
    by_cases erN : i = 75
    · subst erN; (simp (disch := ((try simp only [size_set, ne_eq]); omega)) [rd_set_self, rd_set_ne, hv', h1,
        BitVec.ofNat_add]) <;> rfl
    by_cases erLo : i = 110
    · subst erLo; (simp (disch := ((try simp only [size_set, ne_eq]); omega)) [rd_set_self, rd_set_ne, hv', h1,
        BitVec.ofNat_add]) <;> rfl
    by_cases erLn : i = 111
    · subst erLn; (simp (disch := ((try simp only [size_set, ne_eq]); omega)) [rd_set_self, rd_set_ne, hv', h1,
        BitVec.ofNat_add]) <;> rfl
    by_cases erNB : i = 115
    · subst erNB; (simp (disch := ((try simp only [size_set, ne_eq]); omega)) [rd_set_self, rd_set_ne, hv', h1,
        BitVec.ofNat_add]) <;> rfl
    simp (disch := ((try simp only [size_set, ne_eq]); omega)) only [rd_set_ne]
  · simp only [lookPre4D, lookPre4, pLIR, readAt, Writes, List.mem_cons, List.mem_nil_iff, Prim.dst] at hi ⊢
    aesop

/-! ## The parents -/

/-- **The walk** with the prefix from the tape. -/
def walkIR4D (bX : ℕ) : XIR := .seq (walkPre4D bX) (.loopT rCW rN ⟨0, 1, 5⟩ walkBody)

/-- **One merge pass** with the prefix from the tape. -/
def passIR4D : XIR := .seq (.seq passPre4D (.loopT rCS rNS ⟨0, 1, 5⟩ stepIR)) (.blk swapPs)

/-- **The sort** with the prefixes from the tape. -/
def sortIR4D (bX : ℕ) : XIR := .seq (sortPre4D bX) (.loopK rCP rNP 64 passIR4D)

/-- **Walk and sort** with the prefixes from the tape. -/
def idxIR4D (bX : ℕ) : XIR := .seq (walkIR4D bX) (sortIR4D bX)

/-- **The lookup** with the prefix from the tape. -/
def lookIR4D (bX : ℕ) : XIR := .seq lookPre4D (.seq (.loopK rCB rNB 64 (bsBody4 bX)) (foundIR4 bX))

/-- **One step down** with the lookup's prefix from the tape. -/
def crNodeD (bX : ℕ) : XIR :=
  .ite crOk (.seq (lookIR4D bX) (.ite rFd (.seq (crGet bX) (.seq (.blk crChkPs)
    (.ite crB (.seq (.blk crChildPs) crLd4) (.blk [.const crOk 0])))) (.blk [.const crOk 0])))
    (.blk [])

/-- **The leaf** with the lookup's prefix from the tape. -/
def crLeafD (bX : ℕ) : XIR :=
  .seq (.blk [.const crQe 0]) (.ite crOk (.seq (lookIR4D bX) (.ite rFd (.seq (crGet bX)
    (.blk [.op .or crQe crQn crQn])) (.blk []))) (.blk []))

/-- **One position** of the column reads with the lookups' prefixes from the tape. -/
def crPosGD (bX capW D z occ : ℕ) : XIR :=
  .seq (.seq (.blk (crCapGPs capW D)) crLd4) (.seq (.blk [.const crOk 1, .const crNH (toWord D)])
    (.seq (.loopK crHc crNH (toWord D) (crNodeD bX)) (.seq (crLeafD bX) (.seq (crCopyG z occ)
      (.blk [.op .add crP crP cOne])))))

/-- **The column reads** with the lookups' prefixes from the tape. -/
def readGIRD (bX capW wB nPos D z occ : ℕ) : XIR :=
  .seq (.blk [.const crP 0, .const crWA (toWord wB), .const crNp (toWord nPos)])
    (.loopK crCp crNp (toWord nPos) (crPosGD bX capW D z occ))

/-- **The chain's count** with its prefix and suffix from the tape. -/
def cntIRD : XIR := .seq (.seq cntPreD (.loopT rCW rN ⟨0, 1, 5⟩ cntBody)) cntPostD

/-- **The chain scan** with the count and the start from the tape. -/
def chainIRD (N : ℕ) (tab : List Word) (sd : XIR) : XIR :=
  .seq (.seq cntIRD (.seq (storesIR chB tab) (.seq sd startD))) (.loopT rCC rCn5 ⟨0, 1, 1⟩ (wordIR N))

section Sims

variable {I : Array Word} {pL : ℕ} (hv : pLW I = BitVec.ofNat 64 pL)
include hv

theorem walkIR4D_sim (bX : ℕ) : Sim I (walkIR4 bX pL) (walkIR4D bX) := .seq (walkPre4D_sim hv bX) (.refl _)

theorem passIR4D_sim : Sim I (passIR4 pL) passIR4D := .seq (.seq (passPre4D_sim hv) (.refl _)) (.refl _)

theorem sortIR4D_sim (bX : ℕ) : Sim I (sortIR4 bX pL) (sortIR4D bX) :=
  .seq (sortPre4D_sim hv bX) (.loopK (passIR4D_sim hv))

theorem idxIR4D_sim (bX : ℕ) : Sim I (idxIR4 bX pL) (idxIR4D bX) := .seq (walkIR4D_sim hv bX) (sortIR4D_sim hv bX)

theorem lookIR4D_sim (bX : ℕ) : Sim I (lookIR4 bX pL) (lookIR4D bX) := by
  rw [lookIR4_eq]
  exact .seq (lookPre4D_sim hv) (.refl _)

theorem crNodeD_sim (bX : ℕ) : Sim I (crNode bX pL) (crNodeD bX) :=
  .ite (.seq (lookIR4D_sim hv bX) (.refl _)) (.refl _)

theorem crLeafD_sim (bX : ℕ) : Sim I (crLeaf bX pL) (crLeafD bX) :=
  .seq (.refl _) (.ite (.seq (lookIR4D_sim hv bX) (.refl _)) (.refl _))

theorem crPosGD_sim (bX capW D z occ : ℕ) : Sim I (crPosG bX pL capW D z occ) (crPosGD bX capW D z occ) :=
  .seq (.refl _) (.seq (.refl _) (.seq (.loopK (crNodeD_sim hv bX)) (.seq (crLeafD_sim hv bX) (.refl _))))

theorem readGIRD_sim (bX capW wB nPos D z occ : ℕ) :
    Sim I (readGIR bX pL capW wB nPos D z occ) (readGIRD bX capW wB nPos D z occ) :=
  .seq (.refl _) (.loopK (crPosGD_sim hv bX capW D z occ))

theorem cntIRD_sim : Sim I (cntIR pL) cntIRD := .seq (.seq (cntPreD_sim hv) (.refl _)) (cntPostD_sim hv)

theorem chainIRD_sim (N : ℕ) (tab : List Word) (sd : XIR) : Sim I (chainIR pL N tab sd) (chainIRD N tab sd) :=
  .seq (.seq (cntIRD_sim hv) (.seq (.refl _) (.seq (.refl _) (startD_sim hv)))) (.refl _)

end Sims

end Lvm.XB
