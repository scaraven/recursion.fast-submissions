/- `LvmNodeSoundCircOff` (GOLF2 off-path move, group 17 of 48): declarations that the certificate `certified`
   does not use, moved here verbatim (same names, same namespaces and context) from LvmXComputes, LvmXLookup, LvmXAgree, LvmXDecBr, LvmXDec1, LvmXDec1Agree, LvmNodeSoundCirc,
   so that `Solution`'s import closure need not elaborate them. Import this module where they are needed;
   the name -> module map is GOLF2's moved.tsv. -/
import LvmXComputes
import LvmXLookup
import LvmXAgree
import LvmXDecBr
import LvmXDec1
import LvmXDec1Agree
import LvmNodeSoundCirc
import LvmMPCertOff
import LvmQAsmHar47Off
import LvmJBMutual
import LvmMlListLemmas
import LvmSpecRulesCert

-- ===== from `LvmXComputes` =====

section
section LvmXProg
namespace Lvm.X
open RecursionFast

theorem memX_eq : memX = 2 ^ 25 := rfl

end Lvm.X
end LvmXProg
end

section
section LvmXComputesS
namespace Lvm.X
open RecursionFast

theorem wf_wIR : WF wIR := by
  simp [wIR, wPre, readAt, wCntPs, wBody, WF, Writes, Prim.dst, rA, rLen, rK, rCnt, rT, rW, rPos,
    rC, regs, cTmp]

end Lvm.X
end LvmXComputesS
end

-- ===== from `LvmXLookup` =====

section
section
section LvmXSortSim
namespace Lvm.X
open RecursionFast
attribute [local irreducible] entryK storeM

/-- Controls for `Lo`: a store, or a block writing a heap cell, is not `Lo`. -/
theorem not_lo_store : ¬ Lo (.store rAd rV) := id

theorem not_lo_heap : ¬ Lo (.blk [.const regs 0]) := by simp +decide only [Lo, Prim.dst]

end Lvm.X
end LvmXSortSim
end
end

section
section
section LvmXSortSim
namespace Lvm.X
open RecursionFast
attribute [local irreducible] entryK storeM

theorem lo_advIR : Lo advIR := by simp +decide only [Lo, advIR, Prim.dst, regs, rAd, rI, rJ,
  and_true]
theorem wf_advIR : WF advIR := by simp +decide only [WF, advIR, Prim.dst, rAd, rI, rJ, and_true]

end Lvm.X
end LvmXSortSim
end
end

section
section
section LvmXSortSim
namespace Lvm.X
open RecursionFast
attribute [local irreducible] entryK storeM
section Idx
variable (bX pL : ℕ)

theorem baseX4_ctl (n : ℕ) : baseX4 bX n 0 = bX ∧ baseX4 bX n 1 = bX + n := ⟨rfl, rfl⟩

end Idx
end Lvm.X
end LvmXSortSim
end
end

section
namespace Lvm.X
open RecursionFast
attribute [local irreducible] entryK storeM

/-- Controls for the search: on a prefix predicate it finds the prefix's end; on a predicate that
is not a prefix (true only at `7`) it misses, so `bsRun_spec`'s monotonicity hypothesis is
needed. -/
theorem bsRun_ctl : (bsRun (fun a => decide (a < 3)) 64 (0, 10)).1 = 3 ∧
    (bsRun (fun a => decide (a = 7)) 64 (0, 10)).1 = 0 := by decide +kernel

theorem lexW_asymm {A B : List Word} (h : lexW A B = true) : lexW B A = false := by
  cases e : lexW B A
  · rfl
  · have := lexW_trans _ _ _ h e
    rw [lexW_irrefl] at this
    exact absurd this (by decide)

end Lvm.X
end

section
namespace Lvm.X
open RecursionFast
attribute [local irreducible] entryK storeM

theorem lo_cmpTWord (w r : ℕ) : Lo (cmpTWord w r) := by
  simp +decide only [cmpTWord, Lo, Prim.dst, regs, rKc, rAd, rKa, rG, rH, rF, List.mem_cons,
    List.mem_nil_iff, forall_eq_or_imp, forall_eq, or_false, and_true]

end Lvm.X
end

section
namespace Lvm.X
open RecursionFast
attribute [local irreducible] entryK storeM

theorem lo_ansLtIR : Lo ansLtIR := by
  simp +decide only [ansLtIR, aposIR, ceil8Ps, cmpTWord, Lo, Prim.dst, regs, rQL, rKc, rT2, rPa,
    rAd, rKa, rG, rH, rF, and_true, List.cons_append, List.nil_append]

end Lvm.X
end

section
namespace Lvm.X
open RecursionFast
attribute [local irreducible] entryK storeM
section Idx
variable (bX pL : ℕ)
variable {bX pL} (hbX : regs ≤ bX) (hbX2 : bX ≤ 2 ^ 60) (hpL : pL ≤ 2 ^ 60)
include hbX hbX2 hpL

/-- **`lookup_spec`**, parametric in the target `t`. On a domain tape of a SNARK proof, take a
state `s₂` whose `X[0..|L|)` is the one `idxIR4` left and whose `rQ0 … rQ3` hold
`packBytes t`. If `t` is the answer of some log entry, `(lookIR4 bX pL)` sets `rFd = 1` and `rLo` to a
slot `b` whose `X[b]` is the tape position of the **first** such entry (`ansIdx`);
otherwise `rFd = 0`. `X` is unchanged, so it is still the sorted index. -/
theorem idx_lookup4 (c : Digest) (π : Proof) (L : Log) (hs : 5 + (π.size + 7) / 8 = pL)
    (hq : ∀ e ∈ L, e.1.size < 2 ^ 64) (ht : (extractorInput c π L).length ≤ 2 ^ 64)
    (s : St) (hM : Inv s.M) (hsz : bX + L.length + L.length ≤ s.M.size) (t : Digest)
    (s₂ : St) (hM₂ : Inv s₂.M)
    (hX₂ : ∀ a < L.length, rd s₂.M (bX + a) =
      rd (semXIR (extractorInput c π L).toArray (idxIR4 bX pL) s).M (bX + a))
    (hT : [rd s₂.M rQ0, rd s₂.M rQ1, rd s₂.M rQ2, rd s₂.M rQ3] = packBytes t.toList) :
    (∀ k, ansIdx L t = some k → ∃ b < L.length,
      rd (semXIR (extractorInput c π L).toArray (lookIR4 bX pL) s₂).M rLo = toWord b ∧
      rd (semXIR (extractorInput c π L).toArray (lookIR4 bX pL) s₂).M rFd = 1 ∧
      rd (semXIR (extractorInput c π L).toArray (lookIR4 bX pL) s₂).M (bX + b) = toWord (posE4 pL L k)) ∧
    (ansIdx L t = none →
      rd (semXIR (extractorInput c π L).toArray (lookIR4 bX pL) s₂).M rFd = 0) ∧
    Sorted4 pL (extractorInput c π L).toArray L
      (fun a => rd (semXIR (extractorInput c π L).toArray (lookIR4 bX pL) s₂).M (bX + a)) := by
  set I := (extractorInput c π L).toArray with hI
  have hend := tape_entries_end4 c π L hs
  have h5 : 5 * L.length ≤ entryOff L L.length := by
    have := length_logEntries L
    rwa [entries_length, ← entryOff_length] at this
  obtain ⟨r1, r2, r3⟩ := idxIR4_sorted hbX hbX2 hpL c π L hs hq ht s hM hsz
  generalize semXIR I (idxIR4 bX pL) s = s1 at r1 r2 r3 hX₂
  set X : ℕ → Word := fun a => rd s1.M (bX + a) with hXd
  have hSX : Sorted4 pL I L X := ⟨r1, r2, r3⟩
  have hX₂' : ∀ a < L.length, rd s₂.M (bX + a) = X a := hX₂
  obtain ⟨l1, l2, l3⟩ := lookIR4_sem hbX hbX2 hpL I s₂ hM₂ (n := L.length) (X := X)
    (by rw [hI, getD_toArray, tape_getD_posL4 c π L hs]) (by (clear * - hs ht hend h5; omega)) hT hX₂'
  obtain ⟨hmono, hpure⟩ := lookup_pure4 c π L hs hq ht hSX t
  obtain ⟨b1, b2, b3⟩ := bsRun_spec (p := ltT I X (packBytes t.toList)) (n := L.length)
    (by (clear * - hs ht hend h5; omega)) hmono
  obtain ⟨hsome, hnone⟩ := hpure _ b1 b2 b3
  have hXb : ∀ a < L.length, rd (semXIR I (lookIR4 bX pL) s₂).M (bX + a) = X a := fun a ha => by
    rw [l3 _ (by simp only [regs] at hbX ⊢; (clear * - hbX hbX2; omega)), hX₂' a ha]
  refine ⟨fun k hk => ?_, fun hk => ?_, ⟨fun a b hab hb => ?_, fun a ha => ?_, fun k hk => ?_⟩⟩
  · obtain ⟨hb, e⟩ := hsome k hk
    obtain ⟨hkl, hkc⟩ := ansIdx_lt hk
    refine ⟨_, hb, l1, ?_, by rw [hXb _ hb, e]⟩
    rw [l2, hX₂' _ hb, e, ansW_entry4 c π L hs hq ht hkl, hkc]
    simp [hb, bW]
  · rw [l2]
    by_cases hb : (bsRun (ltT I X (packBytes t.toList)) 64 (0, L.length)).1 < L.length
    · rw [hX₂' _ hb]
      have := hnone hk _ hb
      simp [hb, bW]
      exact this
    · simp [hb, bW]
  · rw [hXb a (by (clear * - hab hb; omega)), hXb b hb]; exact r1 a b hab hb
  · rw [hXb a ha]; exact r2 a ha
  · obtain ⟨a, ha, e⟩ := r3 k hk
    exact ⟨a, ha, by rw [hXb a ha]; exact e⟩

end Idx
end Lvm.X
end

-- ===== from `LvmXAgree` =====

section
namespace Lvm.X
open RecursionFast Finset Lvm.Nb CompPoly.Extension BF64
attribute [local irreducible] entryK storeM

theorem rdK_zero : wK 0 = 0 := rfl

end Lvm.X
end

section
namespace Lvm.X
open RecursionFast Finset Lvm.Nb CompPoly.Extension BF64
attribute [local irreducible] entryK storeM

theorem length_agreeM_le (M : Mem) (wB qB eB n : ℕ) : (agreeM M wB qB eB n).length ≤ n :=
  (List.length_filter_le _ _).trans (by simp)

end Lvm.X
end

section
namespace Lvm.X
open RecursionFast Finset Lvm.Nb CompPoly.Extension BF64
attribute [local irreducible] entryK storeM

theorem agreeP_congr {M M' : Mem} {wB qB eB agB q : ℕ} (hq : q < 2 ^ 15) (hwB : regs ≤ wB)
    (hqB : regs ≤ qB) (heB : regs ≤ eB) (hR : ReadsOut wB qB eB agB)
    (h : ∀ x, regs ≤ x → (x < agB ∨ agB + 2 ^ 15 ≤ x) → rd M' x = rd M x) :
    AgreeP M' wB qB eB q ↔ AgreeP M wB qB eB q := by
  obtain ⟨r1, r2, r3⟩ := hR
  simp only [regs] at hwB hqB heB
  have hF : ∀ c < 3, foldPM M' wB qB q c 64 = foldPM M wB qB q c 64 := fun c hc =>
    Finset.sum_congr rfl fun l hl => by
      have hl' := mem_range.1 hl
      simp only [rdK]
      rw [h (qB + 3 * l + c) (by simp only [regs]; (clear * - hqB hc hl'; omega)) (by (clear * - r2 r3 hc hl'; omega)),
        h (wB + 64 * q + (63 - l)) (by simp only [regs]; (clear * - hq hwB; omega)) (by (clear * - hq r1 r2 r3 hl'; omega))]
  simp only [AgreeP]
  rw [hF 0 (by norm_num), hF 1 (by norm_num), hF 2 (by norm_num),
    h (eB + q) (by simp only [regs]; (clear * - hq heB; omega)) (by (clear * - hq r3; omega)),
    h (eB + 2 ^ 15 + q) (by simp only [regs]; (clear * - hq heB; omega)) (by (clear * - hq r3; omega)),
    h (eB + 2 * 2 ^ 15 + q) (by simp only [regs]; (clear * - hq heB; omega)) (by (clear * - hq r3; omega))]

/-- **The agreement scan**: the count is `|agreeM|` and `agB + t` holds the `t`-th agreeing
position (`agreeM s.M wB qB eB (2^15)`, the positions in increasing order); the heap outside
`[agB, agB + 2^15)` is kept. -/
theorem agreeIR_sem (I : Array Word) (s : St) (hM : Inv s.M) {wB qB eB agB : ℕ}
    (hwB : regs ≤ wB) (hwB2 : wB + 2 ^ 21 < 2 ^ 64) (hqB : regs ≤ qB) (hqB2 : qB + 192 < 2 ^ 64)
    (heB : regs ≤ eB) (heB2 : eB + 3 * 2 ^ 15 < 2 ^ 64)
    (hagB : regs ≤ agB) (hag2 : agB + 2 ^ 15 < 2 ^ 64) (hags : agB + 2 ^ 15 ≤ s.M.size)
    (hR : ReadsOut wB qB eB agB) :
    rd (semXIR I (agreeIR wB qB eB agB) s).M gCnt =
      toWord (agreeM s.M wB qB eB (2 ^ 15)).length ∧
    (∀ t < (agreeM s.M wB qB eB (2 ^ 15)).length,
      rd (semXIR I (agreeIR wB qB eB agB) s).M (agB + t) =
        toWord ((agreeM s.M wB qB eB (2 ^ 15)).getD t 0)) ∧
    (∀ x, regs ≤ x → (x < agB ∨ agB + 2 ^ 15 ≤ x) →
      rd (semXIR I (agreeIR wB qB eB agB) s).M x = rd s.M x) ∧
    Inv (semXIR I (agreeIR wB qB eB agB) s).M := by
  have hs := hM.1
  simp only [regs] at hs hwB hqB heB hagB
  have w0 : WF (.blk [.const gQ 0, .const gCnt 0, .const gN1 (toWord (2 ^ 15))]) := by
    simp +decide [WF, Prim.dst, gQ, gCnt, gN1]
  have hM0 := inv_sem I w0 hM
  have z0 := size_sem I (.blk [.const gQ 0, .const gCnt 0, .const gN1 (toWord (2 ^ 15))]) s
  have r0 : rd (semXIR I (.blk [.const gQ 0, .const gCnt 0, .const gN1 (toWord (2 ^ 15))]) s).M gQ =
        toWord 0 ∧
      rd (semXIR I (.blk [.const gQ 0, .const gCnt 0, .const gN1 (toWord (2 ^ 15))]) s).M gCnt =
        toWord 0 ∧
      rd (semXIR I (.blk [.const gQ 0, .const gCnt 0, .const gN1 (toWord (2 ^ 15))]) s).M gN1 =
        toWord (2 ^ 15) := by
    rw [sem_blk']; simp only [runPrims, List.foldl, Prim.run]
    refine ⟨?_, ?_, ?_⟩ <;>
    simp (disch := first | decide | (simp only [size_set, gQ, gCnt, gN1]; omega)) only [rd_set_self, rd_set_ne] <;> rfl
  have k0 : ∀ x, regs ≤ x → rd (semXIR I (.blk [.const gQ 0, .const gCnt 0,
      .const gN1 (toWord (2 ^ 15))]) s).M x = rd s.M x := fun x hx => by
    simp only [regs] at hx
    refine rd_blk_of_not_dst I _ s ?_
    simp only [List.mem_cons, List.mem_nil_iff, or_false]
    rintro p (rfl | rfl | rfl) <;> simp only [Prim.dst, gQ, gCnt, gN1] <;> (clear * - hx; omega)
  rw [agreeIR, semXIR_seq]
  generalize semXIR I (.blk [.const gQ 0, .const gCnt 0, .const gN1 (toWord (2 ^ 15))]) s = s0
    at hM0 z0 r0 k0
  obtain ⟨q0, c0, n0⟩ := r0
  set L := fun j => agreeM s.M wB qB eB j with hL
  let P : ℕ → St → Prop := fun j s' => Inv s'.M ∧ s'.M.size = s.M.size ∧
    rd s'.M gQ = toWord j ∧ rd s'.M gCnt = toWord (L j).length ∧
    (∀ t < (L j).length, rd s'.M (agB + t) = toWord ((L j).getD t 0)) ∧
    (∀ x, regs ≤ x → (x < agB ∨ agB + 2 ^ 15 ≤ x) → rd s'.M x = rd s.M x)
  have hE : ∀ i, i ≠ gC1 → i ≠ cTmp → rd (entryK gC1 gN1 (toWord (2 ^ 15)) s0.M) i = rd s0.M i :=
    fun i h1 h2 => entryK_frame _ (Ne.symm h1) (Ne.symm h2)
  have h0 : P 0 ⟨entryK gC1 gN1 (toWord (2 ^ 15)) s0.M, s0.o⟩ := by
    refine ⟨inv_entryK hM0 (by decide), by simp only [size_entryK, z0], ?_, ?_,
      fun t ht => absurd ht (by simp [hL, agreeM]), fun x hx _ => ?_⟩ <;> dsimp only
    · rw [hE _ (by decide) (by decide), q0]
    · rw [hE _ (by decide) (by decide), c0]; simp [hL, agreeM]
    · simp only [regs] at hx
      rw [hE _ (by simp only [gC1]; (clear * - hx; omega)) (by simp only [cTmp]; (clear * - hx; omega)), k0 x (by simp only [regs]; omega)]
  have hstep : ∀ j s', j < 2 ^ 15 → P j s' →
      P (j + 1) (decS gC1 (semXIR I (posBody wB qB eB agB) s')) := by
    rintro j s' hj ⟨i1, i2, i3, i4, i5, i6⟩
    have hlen := length_agreeM_le s.M wB qB eB j
    have hlenL : (L j).length ≤ j := hlen
    obtain ⟨e1, e2, e3⟩ := posBody_sem I s' i1 (wB := wB) (qB := qB) (eB := eB) (agB := agB)
      (c := (L j).length) (by simp only [regs]; omega) hwB2 (by simp only [regs]; omega) hqB2
      (by simp only [regs]; omega) heB2 (by simp only [regs]; omega) hag2 (by (clear * - hags z0 h0 i2; omega)) hj hlen i3 i4
    have hd : ∀ x, x ≠ gC1 → rd (decS gC1 (semXIR I (posBody wB qB eB agB) s')).M x =
        rd (semXIR I (posBody wB qB eB agB) s').M x := fun x hx => rd_decS (Ne.symm hx) _
    have hM' := inv_decS e3 (show 4 ≤ gC1 by decide)
    have hz' : (decS gC1 (semXIR I (posBody wB qB eB agB) s')).M.size = s.M.size := by
      rw [size_decS, size_sem, i2]
    have hA : AgreeP s'.M wB qB eB j ↔ AgreeP s.M wB qB eB j :=
      agreeP_congr hj (by simp only [regs]; omega) (by simp only [regs]; omega)
        (by simp only [regs]; omega) hR i6
    dsimp only [P]
    rw [hL]
    dsimp only
    rw [agreeM_succ]
    by_cases hb : AgreeP s.M wB qB eB j
    · rw [if_pos (hA.2 hb)] at e2
      obtain ⟨g1, g2, g3⟩ := e2
      rw [if_pos hb]
      have hlen1 : (agreeM s.M wB qB eB j ++ [j]).length = (L j).length + 1 := by
        rw [List.length_append, List.length_singleton]
      refine ⟨hM', hz', by rw [hd _ (by decide), e1], by rw [hd _ (by decide), g1, hlen1],
        fun t ht => ?_, fun x hx hx2 => ?_⟩
      · rw [hd _ (by simp only [gC1, regs] at *; (clear * - hagB hag2; omega))]
        rw [hlen1] at ht
        by_cases htc : t = (L j).length
        · subst htc
          rw [g2, List.getD_append_right _ _ _ _ (by simp [hL])]
          simp [hL]
        · rw [g3 _ (by simp only [regs]; (clear * - hagB hag2; omega)) (by (clear * - hlen1 htc; omega)), i5 t (by (clear * - hlen1 ht htc; omega)),
            List.getD_append _ _ _ _ (by simp only [hL] at *; (clear * - hlen1 ht htc; omega))]
      · rw [hd _ (by simp only [gC1, regs] at *; (clear * - hx; omega)), g3 x hx (by (clear * - hagB hag2 hj hlenL hlen1 hx2; omega)), i6 x hx hx2]
    · rw [if_neg (fun h => hb (hA.1 h))] at e2
      obtain ⟨g1, g2⟩ := e2
      rw [if_neg hb, List.append_nil]
      refine ⟨hM', hz', by rw [hd _ (by decide), e1], by rw [hd _ (by decide), g1],
        fun t ht => ?_, fun x hx hx2 => ?_⟩
      · rw [hd _ (by simp only [gC1, regs] at *; (clear * - hagB hag2; omega)), g2 _ (by simp only [regs]; (clear * - hagB hag2; omega)), i5 t ht]
      · rw [hd _ (by simp only [gC1, regs] at *; (clear * - hx; omega)), g2 x hx, i6 x hx hx2]
  have := loopK_run I (posBody wB qB eB agB) P s0 hM0 (c := gC1) (n := gN1) (K := 2 ^ 15)
    (by decide) (by decide) (by decide) n0 (by norm_num) h0 hstep
  exact ⟨this.2.2.2.1, this.2.2.2.2.1, this.2.2.2.2.2, this.1⟩

theorem lo_macC (a : ℕ) (ha : a = gA0 ∨ a = gA1 ∨ a = gA2) : LoK (macC a) := by
  rcases ha with rfl | rfl | rfl <;>
  simp +decide [macC, LoK, mulKC, redC, Prim.dst, gE, gPe, gT, gA0, gA1, gA2, regs]

theorem lo_laneBody : LoK laneBody := by
  simp +decide [laneBody, macC, LoK, mulKC, redC, Prim.dst, gE, gPe, gT, gA0, gA1, gA2, gV, gPw,
    regs]

end Lvm.X
end

-- ===== from `LvmXDecBr` =====

section
namespace Lvm.X
open Finset Lvm.Nb CompPoly.Extension BF64

/-- **`Enc₀` in coordinates.** -/
theorem enc0_coords (f₁ : ℕ → Ext3) (g : ℕ → ℕ → BF64)
    (hg : ∀ v < 2 ^ 13, f₁ v = mkE (g 0 v) (g 1 v) (g 2 v)) (q : ℕ) :
    enc0 f₁ q = mkE (encN ptK (fun x : Fin (2 ^ 13) => g 0 x) q)
      (encN ptK (fun x : Fin (2 ^ 13) => g 1 x) q) (encN ptK (fun x : Fin (2 ^ 13) => g 2 x) q) := by
  have e : ∀ c, encN ptK (fun x : Fin (2 ^ 13) => g c x) q = ∑ v ∈ range (2 ^ 13), g c v * nbAt v q :=
    fun c => by
      rw [encN, ← Fin.sum_univ_eq_sum_range (fun v => g c v * nbAt v q)]; rfl
  rw [e, e, e, ← mkE_sum, enc0]
  exact sum_congr rfl fun v hv => by rw [hg v (mem_range.1 hv), mkE_mul_ofK]

end Lvm.X
end

-- ===== from `LvmXDec1` =====

section
namespace Lvm.X
open Finset Lvm.Nb CompPoly.Extension BF64

/-- **Correctness in the unique-decoding regime**: closeness at `udThr 9 3 = 2304`. -/
theorem decodeRec1_correct_ud (wd : ℕ → ℕ → BF64) (α f₂ : ℕ → Ext3) (msg : ℕ → Ext3)
    (hclose : LeanVM.Protocol.Whir.udThr 9 3 ≤ (close1Set wd msg).card)
    (hf : ∀ v < 2 ^ 9, f₂ v = ∑ u ∈ range 16, eqA1 α u * msg (u + 16 * v))
    (hluck : ∀ q < 2 ^ 12, fold1At α wd q = enc1 f₂ q → ∀ u < 16, row1 wd u q = cw1 msg u q) :
    decodeRec1 wd α f₂ = some fun i => if i < 2 ^ 13 then msg i else 0 :=
  decodeRec1_correct wd α f₂ msg
    (le_trans (by norm_num [LeanVM.Protocol.Whir.udThr]) hclose) hf hluck

/-- **Non-vacuity**: the zero word with `α = 0`, `f₂ = 0` meets the hypotheses of
`decodeRec1_correct` and decodes to the zero message. -/
theorem decodeRec1_correct_zero :
    decodeRec1 (fun _ _ => 0) (fun _ => 0) (fun _ => 0) = some fun _ => 0 := by
  have hcw : ∀ u q, cw1 (fun _ => (0 : Ext3)) u q = 0 := fun u q => by simp [cw1]
  have hrow : ∀ u q, row1 (fun _ _ => (0 : BF64)) u q = 0 := fun u q => mkE_zero
  have h := decodeRec1_correct (fun _ _ => 0) (fun _ => 0) (fun _ => 0) (fun _ => 0) ?_ ?_ ?_
  · rw [h]; simp only [ite_self]
  · have : close1Set (fun _ _ => (0 : BF64)) (fun _ => 0) = range (2 ^ 12) := by
      ext q; simp [close1Set, hrow, hcw]
    rw [this, card_range]; norm_num
  · intro v _; simp
  · intro q _ _ u _; rw [hrow, hcw]

end Lvm.X
end

-- ===== from `LvmXDec1Agree` =====

section
namespace Lvm.X
open RecursionFast Finset Lvm.Nb CompPoly.Extension BF64
attribute [local irreducible] entryK storeM

/-- The fold and `Enc₁(f₂)`'s coordinates agree at `q` (the machine's test). -/
abbrev Agree1P (M : Mem) (wB qB eB q : ℕ) : Prop :=
  mkE (rdK M (eB + q)) (rdK M (eB + 2 ^ 12 + q)) (rdK M (eB + 2 * 2 ^ 12 + q)) =
    fold1PM M wB qB q 16

/-- **The machine's agreement list** below `n`. -/
def agree1M (M : Mem) (wB qB eB n : ℕ) : List ℕ :=
  (List.range n).filter fun q => decide (Agree1P M wB qB eB q)

/-- The cells the test reads, outside the list's region. -/
def Reads1Out (wB qB eB agB : ℕ) : Prop :=
  (agB + 2 ^ 12 ≤ wB ∨ wB + 48 * 2 ^ 12 ≤ agB) ∧ (agB + 2 ^ 12 ≤ qB ∨ qB + 48 ≤ agB) ∧
    (agB + 2 ^ 12 ≤ eB ∨ eB + 3 * 2 ^ 12 ≤ agB)

end Lvm.X
end

section
namespace Lvm.X
open RecursionFast Finset Lvm.Nb CompPoly.Extension BF64
attribute [local irreducible] entryK storeM

/-- **The scan's cost** (`2^12` positions). -/
theorem cost_agree1IR_le (wB qB eB agB t : ℕ) : cost (agree1IR wB qB eB agB) t ≤ 2 ^ 24 := by
  rw [cost_agree1IR]; norm_num

end Lvm.X
end

section
namespace Lvm.X
open RecursionFast Finset Lvm.Nb CompPoly.Extension BF64
attribute [local irreducible] entryK storeM

/-- **The fold at the position `q`** (`gQ = q`): the accumulator holds `fold1PM … 16`; the heap
and the registers outside the fold's are kept. -/
theorem fold1IR_sem (I : Array Word) (s : St) (hM : Inv s.M) {wB qB q : ℕ} (hwB : regs ≤ wB)
    (hq : q < 2 ^ 12) (hwB2 : wB + 48 * 2 ^ 12 < 2 ^ 64) (hqB : regs ≤ qB) (hqB2 : qB + 48 < 2 ^ 64)
    (hQ : rd s.M gQ = toWord q) :
    rdE (semXIR I (fold1IR wB qB) s).M h1A = fold1PM s.M wB qB q 16 ∧
    (∀ r, Keep1F r → rd (semXIR I (fold1IR wB qB) s).M r = rd s.M r) ∧
    Inv (semXIR I (fold1IR wB qB) s).M := by
  have hs := hM.1
  simp only [regs] at hs hwB hqB
  have w0 : WF (.blk [.const h1A 0, .const (h1A + 1) 0, .const (h1A + 2) 0, .const gK 48,
      .op .mul gPw gQ gK, .const gK (toWord wB), .op .add gPw gPw gK, .const gPe (toWord qB),
      .const gN2 16]) := by
    simp +decide [WF, Prim.dst, h1A, gK, gPw, gPe, gN2]
  have hM0 := inv_sem I w0 hM
  rw [fold1IR, semXIR_seq]
  have r0 : rd (semXIR I (.blk [.const h1A 0, .const (h1A + 1) 0, .const (h1A + 2) 0, .const gK 48,
        .op .mul gPw gQ gK, .const gK (toWord wB), .op .add gPw gPw gK, .const gPe (toWord qB),
        .const gN2 16]) s).M gPw = toWord (wB + 48 * q + 3 * 0) ∧
      rd (semXIR I (.blk [.const h1A 0, .const (h1A + 1) 0, .const (h1A + 2) 0, .const gK 48,
        .op .mul gPw gQ gK, .const gK (toWord wB), .op .add gPw gPw gK, .const gPe (toWord qB),
        .const gN2 16]) s).M gPe = toWord (qB + 3 * 0) ∧
      rd (semXIR I (.blk [.const h1A 0, .const (h1A + 1) 0, .const (h1A + 2) 0, .const gK 48,
        .op .mul gPw gQ gK, .const gK (toWord wB), .op .add gPw gPw gK, .const gPe (toWord qB),
        .const gN2 16]) s).M gN2 = toWord 16 ∧
      rdE (semXIR I (.blk [.const h1A 0, .const (h1A + 1) 0, .const (h1A + 2) 0, .const gK 48,
        .op .mul gPw gQ gK, .const gK (toWord wB), .op .add gPw gPw gK, .const gPe (toWord qB),
        .const gN2 16]) s).M h1A = 0 := by
    rw [sem_blk']
    simp only [rdE, rdK, runPrims, List.foldl, Prim.run]
    refine ⟨?_, ?_, ?_, ?_⟩ <;>
    simp (disch := first | decide | (simp only [size_set, h1A, gK, gPw, gPe, gN2]; omega))
      only [rd_set_self, rd_set_ne]
    · rw [hQ, show (48 : Word) = toWord 48 from rfl, mul_toWord, add_toWord]
      congr 1; ring
    · rfl
    · rfl
    · rw [eqt_wK_zero, mkE_zero]
  have k0 : ∀ r, Keep1F r → rd (semXIR I (.blk [.const h1A 0, .const (h1A + 1) 0,
      .const (h1A + 2) 0, .const gK 48, .op .mul gPw gQ gK, .const gK (toWord wB),
      .op .add gPw gPw gK, .const gPe (toWord qB), .const gN2 16]) s).M r = rd s.M r :=
    fun r hr => by
    simp only [Keep1F, gPe, gPw, gK, gC2, gN2, cTmp] at hr
    refine rd_blk_of_not_dst I _ s ?_
    simp only [List.mem_cons, List.mem_nil_iff, or_false]
    rintro p (rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl) <;>
      simp only [Prim.dst, h1A, gPe, gPw, gK, gN2] <;> (clear * - hr; omega)
  generalize semXIR I (.blk [.const h1A 0, .const (h1A + 1) 0, .const (h1A + 2) 0, .const gK 48,
    .op .mul gPw gQ gK, .const gK (toWord wB), .op .add gPw gPw gK, .const gPe (toWord qB),
    .const gN2 16]) s = s0 at hM0 r0 k0
  obtain ⟨p0, e0, n0, a0⟩ := r0
  let P : ℕ → St → Prop := fun j s' => Inv s'.M ∧
    rd s'.M gPw = toWord (wB + 48 * q + 3 * j) ∧ rd s'.M gPe = toWord (qB + 3 * j) ∧
    rdE s'.M h1A = fold1PM s.M wB qB q j ∧ (∀ r, Keep1F r → rd s'.M r = rd s.M r)
  have hE : ∀ i, i ≠ gC2 → i ≠ cTmp → rd (entryK gC2 gN2 (toWord 16) s0.M) i = rd s0.M i :=
    fun i h1 h2 => entryK_frame _ (Ne.symm h1) (Ne.symm h2)
  have h0 : P 0 ⟨entryK gC2 gN2 (toWord 16) s0.M, s0.o⟩ := by
    refine ⟨inv_entryK hM0 (by decide), ?_, ?_, ?_, fun r hr => ?_⟩ <;> dsimp only
    · rw [hE _ (by decide) (by decide), p0]
    · rw [hE _ (by decide) (by decide), e0]
    · rw [eqt_rdE_eq (hE _ (by decide) (by decide)) (hE _ (by decide) (by decide))
        (hE _ (by decide) (by decide)), a0, fold1PM, Finset.sum_range_zero]
    · rw [hE _ hr.2.2.2.2.1 hr.2.2.2.2.2.2, k0 r hr]
  have hstep : ∀ j s', j < 16 → P j s' → P (j + 1) (decS gC2 (semXIR I lane1Body s')) := by
    rintro j s' hj ⟨i1, i2, i3, i4, i5⟩
    have hK : ∀ x, regs ≤ x → rdE s'.M x = rdE s.M x := fun x hx => eqt_rdE_eq
      (i5 x (keep1F_of_regs hx)) (i5 _ (keep1F_of_regs (by (clear * - hx; omega))))
      (i5 _ (keep1F_of_regs (by (clear * - hx; omega))))
    obtain ⟨l1, l2, l3, l4, hM'⟩ := lane1Body_sem I s' i1 (pw := wB + 48 * q + 3 * j)
      (pe := qB + 3 * j) (by simp only [regs]; (clear * - hwB hq hwB2 hj; omega)) (by (clear * - hwB hq hwB2 hj; omega)) (by simp only [regs]; (clear * - hqB hqB2 hj; omega))
      (by (clear * - hqB hqB2 hj; omega)) i2 i3
    have hd : ∀ x, x ≠ gC2 → rd (decS gC2 (semXIR I lane1Body s')).M x =
        rd (semXIR I lane1Body s').M x := fun x hx => rd_decS (Ne.symm hx) _
    refine ⟨inv_decS hM' (by decide), ?_, ?_, ?_, fun r hr => ?_⟩
    · rw [hd _ (by decide), l2, show wB + 48 * q + 3 * j + 3 = wB + 48 * q + 3 * (j + 1) by ring]
    · rw [hd _ (by decide), l3, show qB + 3 * j + 3 = qB + 3 * (j + 1) by ring]
    · rw [eqt_rdE_decS _ (.inr (by decide)), l1, i4, fold1PM, fold1PM, Finset.sum_range_succ,
        hK _ (by simp only [regs]; (clear * - hqB hqB2 hj; omega)), hK _ (by simp only [regs]; (clear * - hwB hq hwB2 hj; omega))]
    · have hr' := hr
      obtain ⟨r0, r1, r2, -, r4, -, -⟩ := hr'
      rw [hd _ r4, l4 r r0 r1 r2, i5 r hr]
  have hfin := loopK_run I lane1Body P s0 hM0 (c := gC2) (n := gN2) (K := 16) (by decide)
    (by decide) (by decide) n0 (by norm_num) h0 hstep
  exact ⟨hfin.2.2.2.1, hfin.2.2.2.2, hfin.1⟩

theorem lo_test1IR (eB : ℕ) : LoK (test1IR eB) := by
  simp +decide [test1IR, LoK, Prim.dst, gK, gX, gE, gZ, gZ2, regs]

/-- **The comparison**: `gZ` is `1` iff the accumulator's three words equal the three words of
`Enc₁(f₂)[q]`'s coordinates (`eB + c·2^12 + q`); only `gK, gX, gE, gZ, gZ2` change. -/
theorem test1IR_sem (I : Array Word) (s : St) (hM : Inv s.M) {eB q : ℕ} (heB : regs ≤ eB)
    (hq : q < 2 ^ 12) (heB2 : eB + 3 * 2 ^ 12 < 2 ^ 64) (hQ : rd s.M gQ = toWord q) :
    rd (semXIR I (test1IR eB) s).M gZ =
      bW (decide (rd s.M (eB + q) = rd s.M h1A) &&
        decide (rd s.M (eB + 2 ^ 12 + q) = rd s.M (h1A + 1)) &&
        decide (rd s.M (eB + 2 * 2 ^ 12 + q) = rd s.M (h1A + 2))) ∧
    (∀ r, r ≠ gK → r ≠ gX → r ≠ gE → r ≠ gZ → r ≠ gZ2 →
      rd (semXIR I (test1IR eB) s).M r = rd s.M r) ∧
    Inv (semXIR I (test1IR eB) s).M := by
  have hs := hM.1
  simp only [regs] at hs heB
  have hw : WF (test1IR eB) := by simp +decide [test1IR, WF, Prim.dst, gK, gX, gE, gZ, gZ2]
  refine ⟨?_, fun r r1 r2 r3 r4 r5 => ?_, inv_sem I hw hM⟩
  · simp only [test1IR, semXIR, runPrims, List.foldl, Prim.run]
    simp (disch := first | decide |
      (simp only [size_set, gK, gX, gE, gZ, gZ2, gQ, h1A]; omega)) only [rd_set_self, rd_set_ne]
    rw [hQ, add_toWord, toNat_toWord (by (clear * - heB hq heB2; omega)), add_toWord, toNat_toWord (by (clear * - heB hq heB2; omega)), add_toWord,
      toNat_toWord (by (clear * - heB hq heB2; omega))]
    simp (disch := first | decide |
      (simp only [size_set, gK, gX, gE, gZ, gZ2, gQ, h1A]; omega)) only [rd_set_ne]
    rw [eq_bW, eq_bW, eq_bW, bW_and, bW_and]
    congr 3 <;> ring_nf
  · by_cases hr : r < regs
    · refine frame I (test1IR eB) s hw hM r hr ?_
      simp only [test1IR, Writes, Prim.dst, List.mem_cons, List.mem_nil_iff, or_false,
        exists_eq_or_imp, exists_eq_left]
      (clear * - r1 r2 r3 r4 r5; omega)
    · exact hframeK I (test1IR eB) s (lo_test1IR eB) r (by (clear * - hr; omega))

end Lvm.X
end

section
namespace Lvm.X
open RecursionFast Finset Lvm.Nb CompPoly.Extension BF64
attribute [local irreducible] entryK storeM

/-- **One position**: `q` is listed at `agB + c` iff the fold agrees with `Enc₁(f₂)` at `q`;
`gQ := q + 1`; the heap outside the listed cell is kept. -/
theorem pos1Body_sem (I : Array Word) (s : St) (hM : Inv s.M) {wB qB eB agB q c : ℕ}
    (hwB : regs ≤ wB) (hwB2 : wB + 48 * 2 ^ 12 < 2 ^ 64) (hqB : regs ≤ qB)
    (hqB2 : qB + 48 < 2 ^ 64) (heB : regs ≤ eB) (heB2 : eB + 3 * 2 ^ 12 < 2 ^ 64)
    (hagB : regs ≤ agB) (hag2 : agB + 2 ^ 12 < 2 ^ 64) (hags : agB + 2 ^ 12 ≤ s.M.size)
    (hq : q < 2 ^ 12) (hcq : c ≤ q) (hQ : rd s.M gQ = toWord q) (hC : rd s.M gCnt = toWord c) :
    rd (semXIR I (pos1Body wB qB eB agB) s).M gQ = toWord (q + 1) ∧
    (if Agree1P s.M wB qB eB q then
      rd (semXIR I (pos1Body wB qB eB agB) s).M gCnt = toWord (c + 1) ∧
        rd (semXIR I (pos1Body wB qB eB agB) s).M (agB + c) = toWord q ∧
        ∀ x, regs ≤ x → x ≠ agB + c → rd (semXIR I (pos1Body wB qB eB agB) s).M x = rd s.M x
    else
      rd (semXIR I (pos1Body wB qB eB agB) s).M gCnt = toWord c ∧
        ∀ x, regs ≤ x → rd (semXIR I (pos1Body wB qB eB agB) s).M x = rd s.M x) ∧
    Inv (semXIR I (pos1Body wB qB eB agB) s).M := by
  have hs := hM.1
  simp only [regs] at hs hwB hqB heB hagB
  rw [pos1Body, semXIR_seq]
  obtain ⟨f1, f2, hM1⟩ := fold1IR_sem I s hM (wB := wB) (qB := qB) (by simp only [regs]; omega)
    hq hwB2 (by simp only [regs]; omega) hqB2 hQ
  have z1 := size_sem I (fold1IR wB qB) s
  generalize semXIR I (fold1IR wB qB) s = s1 at f1 f2 hM1 z1
  have q1 : rd s1.M gQ = toWord q := (f2 gQ keep1F_gQ).trans hQ
  have c1 : rd s1.M gCnt = toWord c := (f2 gCnt keep1F_gCnt).trans hC
  have h1 : ∀ x, regs ≤ x → rd s1.M x = rd s.M x := fun x hx => f2 x (keep1F_of_regs hx)
  rw [semXIR_seq]
  obtain ⟨t1, t2, hM2⟩ := test1IR_sem I s1 hM1 (eB := eB) (by simp only [regs]; omega) hq heB2 q1
  have z2 := size_sem I (test1IR eB) s1
  generalize semXIR I (test1IR eB) s1 = s2 at t1 t2 hM2 z2
  -- the flag is the test
  have e : ∀ a b, regs ≤ a → (rd s1.M a = rd s1.M b ↔ rdK s.M a = rdK s1.M b) := fun a b ha => by
    rw [rdK, rdK, wK_inj, h1 a ha]
  have hiff : Agree1P s.M wB qB eB q ↔ (rd s1.M (eB + q) = rd s1.M h1A ∧
      rd s1.M (eB + 2 ^ 12 + q) = rd s1.M (h1A + 1) ∧
      rd s1.M (eB + 2 * 2 ^ 12 + q) = rd s1.M (h1A + 2)) := by
    simp only [Agree1P]
    rw [← f1, rdE, mkE_eq_iff, e _ _ (by simp only [regs]; (clear * - heB heB2 hq; omega)),
      e _ _ (by simp only [regs]; (clear * - heB heB2 hq; omega)), e _ _ (by simp only [regs]; (clear * - heB heB2 hq; omega))]
  have hZ : rd s2.M gZ = bW (decide (Agree1P s.M wB qB eB q)) := by
    rw [t1]
    congr 1
    rw [Bool.eq_iff_iff]
    simp only [Bool.and_eq_true, decide_eq_true_eq, and_assoc]
    exact hiff.symm
  have q2 : rd s2.M gQ = toWord q := (t2 gQ (by decide) (by decide) (by decide) (by decide)
    (by decide)).trans q1
  have c2 : rd s2.M gCnt = toWord c := (t2 gCnt (by decide) (by decide) (by decide) (by decide)
    (by decide)).trans c1
  have h2 : ∀ x, regs ≤ x → rd s2.M x = rd s.M x := fun x hx => by
    simp only [regs] at hx
    rw [t2 x (by simp only [gK]; (clear * - hx; omega)) (by simp only [gX]; (clear * - hx; omega)) (by simp only [gE]; (clear * - hx; omega))
      (by simp only [gZ]; (clear * - hx; omega)) (by simp only [gZ2]; (clear * - hx; omega)), h1 x (by simp only [regs]; omega)]
  -- `q += 1`
  have fin : ∀ s3 : St, Inv s3.M → rd s3.M gQ = toWord q →
      rd (semXIR I (.blk [.op .add gQ gQ cOne]) s3).M gQ = toWord (q + 1) ∧
      (∀ x, x ≠ gQ → rd (semXIR I (.blk [.op .add gQ gQ cOne]) s3).M x = rd s3.M x) ∧
      Inv (semXIR I (.blk [.op .add gQ gQ cOne]) s3).M := fun s3 h3 hq3 => by
    have := h3.1; simp only [regs] at this
    refine ⟨?_, fun x hx => rd_blk_of_not_dst I _ s3 (by simp [Prim.dst]; exact Ne.symm hx),
      inv_sem I (P := .blk [.op .add gQ gQ cOne]) (by simp +decide [WF]) h3⟩
    rw [sem_blk']; simp only [runPrims, List.foldl, Prim.run]
    rw [rd_set_self (by simp only [gQ]; (clear * - this; omega)), hq3, show rd s3.M cOne = 1 from h3.2 0 (by decide),
      add_one_toWord]
  rw [semXIR_seq, semXIR_ite, hZ]
  by_cases hb : Agree1P s.M wB qB eB q
  · rw [decide_eq_true hb, if_neg bW_true_ne, if_pos hb]
    obtain ⟨a1, a2, a3, hM3⟩ := appendIR_sem I s2 hM2 (agB := agB) (c := c)
      (by simp only [regs]; omega) (by (clear * - hagB hag2 hq hcq; omega)) (by (clear * - hags hq hcq z1 z2; omega)) (by (clear * - hq hcq; omega)) c2
    generalize semXIR I (appendIR agB) s2 = s3 at a1 a2 a3 hM3
    have hagc : ∀ r, r < regs → r ≠ agB + c := fun r hr => by simp only [regs] at hr; (clear * - hagB hag2 hq hcq hr; omega)
    obtain ⟨g1, g2, hM4⟩ := fin s3 hM3 (by
      rw [a3 gQ (by decide) (by decide) (by decide) (by decide) (hagc _ (by decide)), q2])
    refine ⟨g1, ⟨?_, ?_, fun x hx hx2 => ?_⟩, hM4⟩
    · rw [g2 _ (by decide), a2]
    · rw [g2 _ (Ne.symm (hagc _ (by decide))), a1, q2]
    · simp only [regs] at hx
      rw [g2 x (by simp only [gQ]; (clear * - hx; omega)), a3 x (by simp only [gK]; (clear * - hx; omega))
        (by simp only [gX]; (clear * - hx; omega)) (by simp only [gCnt]; (clear * - hx; omega)) (by simp only [cTmp]; (clear * - hx; omega)) hx2,
        h2 x (by simp only [regs]; omega)]
  · rw [decide_eq_false hb, bW_false_eq, if_pos rfl, if_neg hb]
    have e3 : semXIR I (.blk []) s2 = s2 := by cases s2; rfl
    rw [e3]
    obtain ⟨g1, g2, hM4⟩ := fin s2 hM2 q2
    refine ⟨g1, ⟨by rw [g2 _ (by decide), c2], fun x hx => ?_⟩, hM4⟩
    simp only [regs] at hx
    rw [g2 x (by simp only [gQ]; (clear * - hx; omega)), h2 x (by simp only [regs]; omega)]

theorem agree1M_succ (M : Mem) (wB qB eB n : ℕ) : agree1M M wB qB eB (n + 1) =
    agree1M M wB qB eB n ++ if Agree1P M wB qB eB n then [n] else [] := by
  rw [agree1M, agree1M, List.range_succ, List.filter_append]
  congr 1
  by_cases h : Agree1P M wB qB eB n
  · rw [if_pos h]; simp only [List.filter_cons, List.filter_nil, decide_eq_true h, ite_true]
  · rw [if_neg h]; simp only [List.filter_cons, List.filter_nil, decide_eq_false h]; rfl

theorem length_agree1M_le (M : Mem) (wB qB eB n : ℕ) : (agree1M M wB qB eB n).length ≤ n :=
  (List.length_filter_le _ _).trans (by simp)

theorem agree1P_congr {M M' : Mem} {wB qB eB agB q : ℕ} (hq : q < 2 ^ 12) (hwB : regs ≤ wB)
    (hqB : regs ≤ qB) (heB : regs ≤ eB) (hR : Reads1Out wB qB eB agB)
    (h : ∀ x, regs ≤ x → (x < agB ∨ agB + 2 ^ 12 ≤ x) → rd M' x = rd M x) :
    Agree1P M' wB qB eB q ↔ Agree1P M wB qB eB q := by
  obtain ⟨r1, r2, r3⟩ := hR
  simp only [regs] at hwB hqB heB
  have hF : fold1PM M' wB qB q 16 = fold1PM M wB qB q 16 :=
    Finset.sum_congr rfl fun u hu => by
      have hu' := mem_range.1 hu
      have hq' : q + 1 ≤ 2 ^ 12 := hq
      have hq48 : 48 * q + 48 ≤ 48 * 2 ^ 12 := by (clear * - hq; omega)
      rw [eqt_rdE_eq (h (qB + 3 * u) (by simp only [regs]; (clear * - hqB hu'; omega)) (by (clear * - r2 r3 hu'; omega)))
          (h (qB + 3 * u + 1) (by simp only [regs]; (clear * - hqB hu'; omega)) (by (clear * - r2 r3 hu'; omega)))
          (h (qB + 3 * u + 2) (by simp only [regs]; (clear * - hqB hu'; omega)) (by (clear * - r2 r3 hu'; omega))),
        eqt_rdE_eq (h (wB + 48 * q + 3 * u) (by simp only [regs]; (clear * - hq hwB hu'; omega)) (by (clear * - hq r1 r2 r3 hu'; omega)))
          (h (wB + 48 * q + 3 * u + 1) (by simp only [regs]; (clear * - hq hwB hu'; omega)) (by (clear * - hq r1 r2 r3 hu'; omega)))
          (h (wB + 48 * q + 3 * u + 2) (by simp only [regs]; (clear * - hq hwB hu'; omega)) (by (clear * - hq r1 r2 r3 hu'; omega)))]
  simp only [Agree1P, hF, rdK]
  rw [h (eB + q) (by simp only [regs]; (clear * - hq heB; omega)) (by (clear * - hq r3; omega)),
    h (eB + 2 ^ 12 + q) (by simp only [regs]; (clear * - hq heB; omega)) (by (clear * - hq r3; omega)),
    h (eB + 2 * 2 ^ 12 + q) (by simp only [regs]; (clear * - hq heB; omega)) (by (clear * - hq r3; omega))]

/-- **The level-1 agreement scan**: the count is `|agree1M|` and `agB + t` holds the `t`-th
agreeing position (`agree1M s.M wB qB eB (2^12)`, increasing); the heap outside
`[agB, agB + 2^12)` is kept. -/
theorem agree1IR_sem (I : Array Word) (s : St) (hM : Inv s.M) {wB qB eB agB : ℕ}
    (hwB : regs ≤ wB) (hwB2 : wB + 48 * 2 ^ 12 < 2 ^ 64) (hqB : regs ≤ qB) (hqB2 : qB + 48 < 2 ^ 64)
    (heB : regs ≤ eB) (heB2 : eB + 3 * 2 ^ 12 < 2 ^ 64)
    (hagB : regs ≤ agB) (hag2 : agB + 2 ^ 12 < 2 ^ 64) (hags : agB + 2 ^ 12 ≤ s.M.size)
    (hR : Reads1Out wB qB eB agB) :
    rd (semXIR I (agree1IR wB qB eB agB) s).M gCnt =
      toWord (agree1M s.M wB qB eB (2 ^ 12)).length ∧
    (∀ t < (agree1M s.M wB qB eB (2 ^ 12)).length,
      rd (semXIR I (agree1IR wB qB eB agB) s).M (agB + t) =
        toWord ((agree1M s.M wB qB eB (2 ^ 12)).getD t 0)) ∧
    (∀ x, regs ≤ x → (x < agB ∨ agB + 2 ^ 12 ≤ x) →
      rd (semXIR I (agree1IR wB qB eB agB) s).M x = rd s.M x) ∧
    Inv (semXIR I (agree1IR wB qB eB agB) s).M := by
  have hs := hM.1
  simp only [regs] at hs hwB hqB heB hagB
  have w0 : WF (.blk [.const gQ 0, .const gCnt 0, .const gN1 (toWord (2 ^ 12))]) := by
    simp +decide [WF]
  have hM0 := inv_sem I w0 hM
  have z0 := size_sem I (.blk [.const gQ 0, .const gCnt 0, .const gN1 (toWord (2 ^ 12))]) s
  have r0 : rd (semXIR I (.blk [.const gQ 0, .const gCnt 0, .const gN1 (toWord (2 ^ 12))]) s).M
        gQ = toWord 0 ∧
      rd (semXIR I (.blk [.const gQ 0, .const gCnt 0, .const gN1 (toWord (2 ^ 12))]) s).M gCnt =
        toWord 0 ∧
      rd (semXIR I (.blk [.const gQ 0, .const gCnt 0, .const gN1 (toWord (2 ^ 12))]) s).M gN1 =
        toWord (2 ^ 12) := by
    rw [sem_blk']; simp only [runPrims, List.foldl, Prim.run]
    refine ⟨?_, ?_, ?_⟩ <;>
    simp (disch := first | decide | (simp only [size_set, gQ, gCnt, gN1]; omega)) only
      [rd_set_self, rd_set_ne] <;> rfl
  have k0 : ∀ x, regs ≤ x → rd (semXIR I (.blk [.const gQ 0, .const gCnt 0,
      .const gN1 (toWord (2 ^ 12))]) s).M x = rd s.M x := fun x hx => by
    simp only [regs] at hx
    refine rd_blk_of_not_dst I _ s ?_
    simp only [List.mem_cons, List.mem_nil_iff, or_false]
    rintro p (rfl | rfl | rfl) <;> simp only [Prim.dst, gQ, gCnt, gN1] <;> (clear * - hx; omega)
  rw [agree1IR, semXIR_seq]
  generalize semXIR I (.blk [.const gQ 0, .const gCnt 0, .const gN1 (toWord (2 ^ 12))]) s = s0
    at hM0 z0 r0 k0
  obtain ⟨q0, c0, n0⟩ := r0
  set L := fun j => agree1M s.M wB qB eB j with hL
  let P : ℕ → St → Prop := fun j s' => Inv s'.M ∧ s'.M.size = s.M.size ∧
    rd s'.M gQ = toWord j ∧ rd s'.M gCnt = toWord (L j).length ∧
    (∀ t < (L j).length, rd s'.M (agB + t) = toWord ((L j).getD t 0)) ∧
    (∀ x, regs ≤ x → (x < agB ∨ agB + 2 ^ 12 ≤ x) → rd s'.M x = rd s.M x)
  have hE : ∀ i, i ≠ gC1 → i ≠ cTmp →
      rd (entryK gC1 gN1 (toWord (2 ^ 12)) s0.M) i = rd s0.M i :=
    fun i h1 h2 => entryK_frame _ (Ne.symm h1) (Ne.symm h2)
  have h0 : P 0 ⟨entryK gC1 gN1 (toWord (2 ^ 12)) s0.M, s0.o⟩ := by
    refine ⟨inv_entryK hM0 (by decide), by simp only [size_entryK, z0], ?_, ?_,
      fun t ht => absurd ht (by simp [hL, agree1M]), fun x hx _ => ?_⟩ <;> dsimp only
    · rw [hE _ (by decide) (by decide), q0]
    · rw [hE _ (by decide) (by decide), c0]; simp [hL, agree1M]
    · simp only [regs] at hx
      rw [hE _ (by simp only [gC1]; (clear * - hx; omega)) (by simp only [cTmp]; (clear * - hx; omega)),
        k0 x (by simp only [regs]; omega)]
  have hstep : ∀ j s', j < 2 ^ 12 → P j s' →
      P (j + 1) (decS gC1 (semXIR I (pos1Body wB qB eB agB) s')) := by
    rintro j s' hj ⟨i1, i2, i3, i4, i5, i6⟩
    have hlen := length_agree1M_le s.M wB qB eB j
    have hlenL : (L j).length ≤ j := hlen
    obtain ⟨e1, e2, e3⟩ := pos1Body_sem I s' i1 (wB := wB) (qB := qB) (eB := eB) (agB := agB)
      (c := (L j).length) (by simp only [regs]; omega) hwB2 (by simp only [regs]; omega) hqB2
      (by simp only [regs]; omega) heB2 (by simp only [regs]; omega) hag2 (by (clear * - hags z0 h0 i2; omega)) hj hlen i3 i4
    have hd : ∀ x, x ≠ gC1 → rd (decS gC1 (semXIR I (pos1Body wB qB eB agB) s')).M x =
        rd (semXIR I (pos1Body wB qB eB agB) s').M x := fun x hx => rd_decS (Ne.symm hx) _
    have hM' := inv_decS e3 (show 4 ≤ gC1 by decide)
    have hz' : (decS gC1 (semXIR I (pos1Body wB qB eB agB) s')).M.size = s.M.size := by
      rw [size_decS, size_sem, i2]
    have hA : Agree1P s'.M wB qB eB j ↔ Agree1P s.M wB qB eB j :=
      agree1P_congr hj (by simp only [regs]; omega) (by simp only [regs]; omega)
        (by simp only [regs]; omega) hR i6
    dsimp only [P]
    rw [hL]
    dsimp only
    rw [agree1M_succ]
    by_cases hb : Agree1P s.M wB qB eB j
    · rw [if_pos (hA.2 hb)] at e2
      obtain ⟨g1, g2, g3⟩ := e2
      rw [if_pos hb]
      have hlen1 : (agree1M s.M wB qB eB j ++ [j]).length = (L j).length + 1 := by
        rw [List.length_append, List.length_singleton]
      refine ⟨hM', hz', by rw [hd _ (by decide), e1], by rw [hd _ (by decide), g1, hlen1],
        fun t ht => ?_, fun x hx hx2 => ?_⟩
      · rw [hd _ (by simp only [gC1, regs] at *; (clear * - hagB hag2; omega))]
        rw [hlen1] at ht
        by_cases htc : t = (L j).length
        · subst htc
          rw [g2, List.getD_append_right _ _ _ _ (by simp [hL])]
          simp [hL]
        · rw [g3 _ (by simp only [regs]; (clear * - hagB hag2; omega)) (by (clear * - hlen1 htc; omega)), i5 t (by (clear * - hlen1 ht htc; omega)),
            List.getD_append _ _ _ _ (by simp only [hL] at *; (clear * - hlen1 ht htc; omega))]
      · rw [hd _ (by simp only [gC1, regs] at *; (clear * - hx; omega)), g3 x hx (by (clear * - hagB hag2 hj hlenL hlen1 hx2; omega)), i6 x hx hx2]
    · rw [if_neg (fun h => hb (hA.1 h))] at e2
      obtain ⟨g1, g2⟩ := e2
      rw [if_neg hb, List.append_nil]
      refine ⟨hM', hz', by rw [hd _ (by decide), e1], by rw [hd _ (by decide), g1],
        fun t ht => ?_, fun x hx hx2 => ?_⟩
      · rw [hd _ (by simp only [gC1, regs] at *; (clear * - hagB hag2; omega)), g2 _ (by simp only [regs]; (clear * - hagB hag2; omega)),
          i5 t ht]
      · rw [hd _ (by simp only [gC1, regs] at *; (clear * - hx; omega)), g2 x hx, i6 x hx hx2]
  have := loopK_run I (pos1Body wB qB eB agB) P s0 hM0 (c := gC1) (n := gN1) (K := 2 ^ 12)
    (by decide) (by decide) (by decide) n0 (by norm_num) h0 hstep
  exact ⟨this.2.2.2.1, this.2.2.2.2.1, this.2.2.2.2.2, this.1⟩

/-- The test at one position is the decoder's. -/
theorem agree1P_iff {M : Mem} {wB qB eB q : ℕ} (wd : ℕ → ℕ → BF64) (α f₂ : ℕ → Ext3)
    (hq : q < 2 ^ 12)
    (hW : ∀ q < 2 ^ 12, ∀ t < 48, rdK M (wB + 48 * q + t) = wd q t)
    (hQ : ∀ u < 16, rdE M (qB + 3 * u) = eqA1 α u)
    (hE : ∀ q < 2 ^ 12, enc1 f₂ q =
      mkE (rdK M (eB + q)) (rdK M (eB + 2 ^ 12 + q)) (rdK M (eB + 2 * 2 ^ 12 + q))) :
    Agree1P M wB qB eB q ↔ fold1At α wd q = enc1 f₂ q := by
  have hF : fold1At α wd q = fold1PM M wB qB q 16 := by
    rw [fold1At, fold1PM]
    refine sum_congr rfl fun u hu => ?_
    have hu' := mem_range.1 hu
    rw [hQ u hu', row1, rdE, ← hW q hq (3 * u) (by (clear * - hu'; omega)), ← hW q hq (3 * u + 1) (by (clear * - hu'; omega)),
      ← hW q hq (3 * u + 2) (by (clear * - hu'; omega))]
    rfl
  simp only [Agree1P]
  rw [← hF, ← hE q hq]
  exact eq_comm

/-- **The machine's list is the decoder's**: the word at `wB + 48q + t`, the `eq(α, ·)` table at
`qB + 3u` (`rdE`), and `Enc₁(f₂)[q]`'s coordinates at `eB + c·2^12 + q`. -/
theorem agree1M_eq_agree1L {M : Mem} {wB qB eB : ℕ} (wd : ℕ → ℕ → BF64) (α f₂ : ℕ → Ext3)
    (hW : ∀ q < 2 ^ 12, ∀ t < 48, rdK M (wB + 48 * q + t) = wd q t)
    (hQ : ∀ u < 16, rdE M (qB + 3 * u) = eqA1 α u)
    (hE : ∀ q < 2 ^ 12, enc1 f₂ q =
      mkE (rdK M (eB + q)) (rdK M (eB + 2 ^ 12 + q)) (rdK M (eB + 2 * 2 ^ 12 + q))) :
    agree1M M wB qB eB (2 ^ 12) = agree1L wd α f₂ := by
  unfold agree1M agree1L
  refine List.filter_congr fun q hq => ?_
  exact decide_eq_decide.2 (agree1P_iff wd α f₂ (List.mem_range.1 hq) hW hQ hE)

end Lvm.X
end

-- ===== from `LvmNodeSoundCirc` =====

section
set_option autoImplicit false
namespace Lvm.NS
open RecursionFast Lvm Lvm.T Lvm.Replay Lvm.Loop Lvm.Loop.Build Lvm.QLink Lvm.QSig Lvm.M3 Lvm.SigBits
section Parts
variable {α : Type} (lay : Layout) (I : SigIn) (qa : BM α) (nK nE : ℕ)
variable (pl : ℕ → Var → Bool × ℕ) (groups : List Grp) (arrs : List InArr) (aux : List Tab) (L : Lay)
  (hτ : ∀ t ∈ lvmTabs (Qn lay I qa nK nE) pl groups arrs aux, t.τ ≤ L.μ)

/-- The interpreter's memory on the inputs read off the stack `q`. -/
noncomputable def memN (q : LeanVM.Protocol.Column L.μ) : Mem :=
  (Qn lay I qa nK nE).interpMem (inKOf (Qn lay I qa nK nE) pl groups arrs aux L hτ q)
    (inEOf (Qn lay I qa nK nE) pl groups arrs aux L hτ q)

end Parts
end Lvm.NS
end

section
set_option autoImplicit false
namespace Lvm.NS
open RecursionFast Lvm Lvm.T Lvm.Replay Lvm.Loop Lvm.Loop.Build Lvm.QLink Lvm.QSig Lvm.M3 Lvm.SigBits
section Parts
variable {α : Type} (lay : Layout) (I : SigIn) (qa : BM α) (nK nE : ℕ)
variable (pl : ℕ → Var → Bool × ℕ) (groups : List Grp) (arrs : List InArr) (aux : List Tab) (L : Lay)
  (hτ : ∀ t ∈ lvmTabs (Qn lay I qa nK nE) pl groups arrs aux, t.τ ≤ L.μ)
variable {lay I qa nK nE pl groups arrs aux L hτ}

/-- **Every segment holds and asserts** in the interpreter's memory (`loopir_sound`). -/
theorem segs_of_aux {q : LeanVM.Protocol.Column L.μ}
    (H : AuxHyps (Qn lay I qa nK nE) pl groups arrs aux L hτ q) :
    SegsHold (ctxOf (Qn lay I qa nK nE)) (memN lay I qa nK nE pl groups arrs aux L hτ q) (p0 nK nE)
        (qprog lay I qa (p0 nK nE)).2 ∧
      SegsAssert (memN lay I qa nK nE pl groups arrs aux L hτ q) (p0 nK nE) (qprog lay I qa (p0 nK nE)).2 := by
  have hsz := And.intro (inKOf_size (Qn lay I qa nK nE) pl groups arrs aux L hτ q)
    (inEOf_size (Qn lay I qa nK nE) pl groups arrs aux L hτ q)
  obtain ⟨-, hok⟩ := Program.loopir_sound _ H.wf _ _ hsz _ (loop_cons _ pl groups arrs aux L hτ H.grp q H.holds)
    (loop_bus _ pl groups arrs aux L hτ H.grp H.inOk H.auxSeeds H.cnt H.len q H.holds) H.inj H.inb
  obtain ⟨hh, hiff, -⟩ := toProgram_interp nK nE (qprog lay I qa) H.wf _ _ hsz H.inj H.inb
  exact ⟨hh, hiff.mp hok⟩

/-- The three parts' segments, at their pointers. -/
theorem parts_of_aux {q : LeanVM.Protocol.Column L.μ}
    (H : AuxHyps (Qn lay I qa nK nE) pl groups arrs aux L hτ q) :
    Ok (ctxOf (Qn lay I qa nK nE)) (memN lay I qa nK nE pl groups arrs aux L hτ q) (qlink P20 lay) (p0 nK nE) ∧
      Ok (ctxOf (Qn lay I qa nK nE)) (memN lay I qa nK nE pl groups arrs aux L hτ q) (qsig I) (p1 lay nK nE) ∧
      Ok (ctxOf (Qn lay I qa nK nE)) (memN lay I qa nK nE pl groups arrs aux L hτ q) qa (p2 lay I nK nE) := by
  obtain ⟨hh, ha⟩ := segs_of_aux H
  have e : qprog lay I qa = (qlink P20 lay >>= fun _ => (qsig I >>= fun _ => qa)) := rfl
  rw [e, hold_bind, hold_bind] at hh
  rw [e, assert_bind, assert_bind] at ha
  exact ⟨⟨hh.1, ha.1⟩, ⟨hh.2.1, ha.2.1⟩, ⟨hh.2.2, ha.2.2⟩⟩

/-- **Q_link's conclusion** on the committed pair. -/
theorem link_of_aux {q : LeanVM.Protocol.Column L.μ}
    (H : AuxHyps (Qn lay I qa nK nE) pl groups arrs aux L hτ q) {ws : List Word}
    (hS : StreamOk P20) (hQ : QOk P20 lay) (hin : QIn P20 lay ws (memN lay I qa nK nE pl groups arrs aux L hτ q))
    (hws : 2 ^ lay.m ≤ ws.length)
    (hNs : lay.sb + 2 ^ lay.m ≤ max ((Qn lay I qa nK nE).cells .K) ((Qn lay I qa nK nE).cells .E)) :
    LaneLink P20 ws ∧ LinkOk P20 (decode P20 ws) ∧ PadOkB (wordsBytes ws) (hashedLen P20) := by
  obtain ⟨hl, -, -⟩ := parts_of_aux H
  have hN : (ctxOf (Qn lay I qa nK nE)).cells .K ≤
      max ((Qn lay I qa nK nE).cells .K) ((Qn lay I qa nK nE).cells .E) := by
    rw [ctxOf_cells]; exact le_max_left _ _
  obtain ⟨hL, hP⟩ := qlink_sound hS hQ hin hws H.inj hN hNs hl.1 hl.2
  exact ⟨hL, linkOk_of_laneLink hS hL, hP⟩

/-- **Q_sig's conclusion** on the committed pair (`qsig_sound_in`, `BITS` by `sigBitsOk`). -/
theorem sig_of_aux {q : LeanVM.Protocol.Column L.μ}
    (H : AuxHyps (Qn lay I qa nK nE) pl groups arrs aux L hτ q)
    (hg : (memN lay I qa nK nE pl groups arrs aux L hτ q).k I.flag = 1)
    (hks : SigKSin I (memN lay I qa nK nE pl groups arrs aux L hτ q).k)
    (bpl : ℕ → ℕ → Bool × ℕ) (hT : SigTabsIn I (qsig I (p1 lay nK nE)).1 bpl aux)
    (hC : SigCellsLt (Qn lay I qa nK nE) I (qsig I (p1 lay nK nE)).1 bpl) (hln : I.ln = 20) :
    SigOk (digAt (memN lay I qa nK nE pl groups arrs aux L hτ q).k I.vk)
        (digAt (memN lay I qa nK nE pl groups arrs aux L hτ q).k I.md)
        (sigAt' (memN lay I qa nK nE pl groups arrs aux L hτ q).k I.sg) = true ∧
      ChildOk I (memN lay I qa nK nE pl groups arrs aux L hτ q).k := by
  obtain ⟨-, hs, -⟩ := parts_of_aux H
  exact qsig_sound_in ⟨by omega, by omega⟩ hs hg hks
    (sigBitsOk _ pl groups arrs aux L hτ q H I _ bpl hT hC ⟨by omega, by omega⟩)
    fun a b ha hb h => FK.FKx_pow_inj (by omega) (by omega) h

end Parts
end Lvm.NS
end
