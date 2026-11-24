-- lvm6 EXI phase 2: the descent's machine inputs at `P17` (EXG's `LvD`, `finX`) from the front's heap facts.
-- Per level: the glue (`glueIR_cols`) or the start (`startIR_cols`) gives the start columns, X9's `trIR_sem` /
-- `tr0IR_sem` the chain and the tables, the start columns survive the transition (`lvRun_post`), EXG's `grpsOK`
-- the groups once the agreement holds (it is supplied by `lens_back`). `FrontIn`: the one open input (EXF's), the
-- heap after `parse ; front6 ; fill`. New.
import Lvm6XDescProg6
import Lvm6XLv18

/-!
# The descent at `P17` from the front's facts

* **`lvRun_post`**: a level's `LvRun` from the start program's facts (`s1`), the transition's facts after it, and
  disjointness of the start columns and of `[regs, lo)` from what the transition writes.
* **`ChOK`**, **`SclOK`**, **`CellsOK F`** (FrontA's cells lie in `[regs, wB6 0)`), **`FrontHeap`** (the rows of the
  five commitments, the challenge pairs, the high parts, the final scalars), **`bDep`** (`331350016`: levels 4–1
  write nothing below it).
* **`glueD`**, **`lvRunD`** (levels 1–4), **`lvRunD_0`** (level 0): the levels' inputs; **`mach_of`**:
  `FrontHeap` for every decomposition of the log ⟹ `Mach … (LvD F) 67 bDep`.
* **`finOut`**: `FinOut finX (LvD F 0) 67` (`decD_of_rep`, `finIR_heapHolds`).
* **`FrontIn Φ fill F`** (open, EXF), **`descIn`**, **`descProg6`**, **`open6XFront`**.
-/

set_option autoImplicit false

namespace Lvm6.X

open RecursionFast Lvm.X Lvm.Nb Lvm6.FD Finset Lvm6.Whir LeanVM.Parameters LeanVM.Protocol.Whir
  LeanVM.Protocol.Whir.AffineCombiner
open LeanVM.Protocol.Compile (Ev)

/-! ## A level's inputs from its start and its transition -/

/-- **A level's `LvRun`** from the start program's facts at `s1`, the transition's facts (chain, tables, `Inv`,
output, frame `Out`) and the disjointness of the start columns and of `[regs, lo)` from the transition's writes. -/
theorem lvRun_post (I : Array Word) (i : ℕ) (L : LevelX) (s s1 : St) {h d tb tS J : ℕ} {nc : ℕ → ℕ}
    {nO lo : ℕ} (hh : ht6 i = h) (hh64 : h ≤ 64) {bf : ℕ → ℕ} {rs : List (Rnd E2)} {Q : Wd E2 (2 ^ h) (0 + J)}
    {Tc : CT E2 0} (Out : ℕ → Prop) (hG2 : s1.o = s.o)
    (hG3 : ColsRep d (fun q x ↦ rdK s1.M (L.colB + L.str * q + x)) Tc)
    (hG4 : ∀ x, regs ≤ x → x < lo → rd s1.M x = rd s.M x)
    (hT1 : ChainW (semXIR I L.tr s).M h hh64 0 J bf (rs.map fun r ↦ (r.α, r.β)) Q)
    (hT2 : TabW (semXIR I L.tr s).M J 0 tb tS bf J) (hT3 : Inv (semXIR I L.tr s).M)
    (hT4 : (semXIR I L.tr s).o = s1.o)
    (hT5 : ∀ x, regs ≤ x → Out x → rd (semXIR I L.tr s).M x = rd s1.M x)
    (hcolO : ∀ x, L.colB ≤ x → x < L.colB + 2 * L.str → Out x) (hcolR : regs ≤ L.colB)
    (hloO : ∀ x, x < lo → Out x) (hbf : ∀ k ≤ J, bf k < 2 ^ 64) (hJ63 : J < 63)
    (hN64 : ht6 i + 1 ≤ 64) (hNN : (ht6 i + 1) * (ht6 i + 1) ≤ 8 * 2 ^ ht6 i) (hB : regs ≤ L.B)
    (hE : fdEnd L.B (ht6 i) < 2 ^ 64) (hd : d + 3 ≤ 2 ^ ht6 i) (hcol : fdEnd L.B (ht6 i) ≤ L.colB)
    (hstr : 2 ^ ht6 i ≤ L.str) (htb : regs ≤ tb) (htS : regs ≤ tS) (hlo : lo ≤ L.B)
    (hgs : (∀ r < J, (sbList (semXIR I L.tr s).M (ht6 i + 1) (ht6 i) d tS r (colsL (semXIR I L.tr s).M (ht6 i + 1)
      (ht6 i) d tb tS (fun q x ↦ rdK (semXIR I L.tr s).M (L.colB + L.str * q + x)) r)).length = d + 3) →
      GrpsOK (semXIR I L.tr s).M (ht6 i + 1) (ht6 i) L.B L.colB L.str d tb tS
        (fun q x ↦ rdK (semXIR I L.tr s).M (L.colB + L.str * q + x)) nc (semXIR I L.tr s).M.size L.gs 0)
    (hJ : (L.gs.map GroupX.nr).sum = J) (hnc : nO ≤ nc J) :
    LvRun I i L s h d tb tS 0 J nc nO lo (domE h hh64) rs Q Tc := by
  refine ⟨hh, hN64, hNN, hB, hE, hd, hcol, hstr, htb, htS, hT3, hT4.trans hG2, hgs, hJ, hnc,
    tblOK_of_chain hh64 J bf _ Q hT1 fun r hr ↦ TabW.entries hT2 hbf (by omega) hr hr, ?_, hlo,
    fun x hx hlx ↦ (hT5 x hx (hloO x hlx)).trans (hG4 x hx hlx)⟩
  intro u i' x hx
  have hu : bitsToNat u = 0 := bitsToNat_fin0 u
  have hi2 := i'.isLt
  have hc : L.str * (2 * bitsToNat u + (i' : ℕ)) + x < 2 * L.str := by
    rw [hu]; rcases (show (i' : ℕ) = 0 ∨ (i' : ℕ) = 1 by omega) with e | e <;> rw [e] <;> omega
  show wK (rd (semXIR I L.tr s).M (L.colB + L.str * (2 * bitsToNat u + i') + x)) = _
  rw [hT5 _ (by omega) (hcolO _ (by omega) (by omega))]
  exact hG3 u i' x hx

/-! ## The front's facts -/

/-- Levels 4–1 write nothing below `bDep` (the rows of commitments 0–4 and the front's cells lie below it). -/
def bDep : ℕ := 331350016

/-- **The challenge pairs** of a level's `J` rounds at the cells `c k`. -/
def ChOK (M : Mem) (c : ℕ → ℕ) (J : ℕ) (rs : List (Rnd E2)) : Prop :=
  ∀ k < J, rdE2 M (c k) = ((rs.map fun r ↦ (r.α, r.β)).getD k (0, 0)).1 ∧
    rdE2 M (c k + 2) = ((rs.map fun r ↦ (r.α, r.β)).getD k (0, 0)).2

/-- **`n` scalars** at `a + 2k`. -/
def SclOK (M : Mem) (a n : ℕ) (v : List E2) : Prop := ∀ k < n, rdE2 M (a + 2 * k) = v.getD k 0

/-- **FrontA's cells** lie in `[regs, wB6 0)` (below every region the descent writes). -/
def CellsOK (F : FrontA) : Prop :=
  (∀ i < 5, ∀ k < rndD i, regs ≤ F.ch i k ∧ F.ch i k + 4 ≤ wB6 0) ∧
    (∀ i < 4, regs ≤ F.hi i ∧ F.hi i + 2 * rndD i + 1 ≤ wB6 0) ∧ regs ≤ F.s ∧ F.s + 2 * (2 ^ 2 + 4) + 1 ≤ wB6 0

/-- **The heap the descent starts from** for the opening's witnesses: level 0's rows (W1's `wordE true 0`), levels
1–4's words position-major at `wB6 i`, the challenge pairs, the high parts, the final scalars at FrontA's cells. -/
structure FrontHeap (F : FrontA) (M : Mem) (cs : List (ℕ × ℕ × LeanVM.Protocol.Compile.Word))
    (rs0 : List (Rnd E2)) (o0 : TailOut E2 mid0.L.ko mid0.L.t (2 ^ 20)) (rs1 : List (Rnd E2))
    (o1 : TailOut E2 mid1.L.ko mid1.L.t (2 ^ 19)) (rs2 : List (Rnd E2)) (o2 : TailOut E2 mid2.L.ko mid2.L.t (2 ^ 18))
    (rs3 : List (Rnd E2)) (o3 : TailOut E2 mid3.L.ko mid3.L.t (2 ^ 17)) (rs4 : List (Rnd E2)) (sc : List E2) :
    Prop where
  rows0 : ∃ (row : ℕ → List BF64) (c : ℕ × ℕ × LeanVM.Protocol.Compile.Word), c.1 = 20 ∧
    (∀ p < 2 ^ 20, c.2.2 p = List.replicate 18 0 ++ row p) ∧
    wordE true 0 (0 + 6) 20 [c] = wordE true 0 (0 + 6) 20 cs ∧
    ∀ p < 2 ^ 20, ∀ t < 46, rdK M (wB6 0 + 46 * p + t) = (row p).getD t 0
  w1 : HoldsW M (wB6 1) 19 (0 + 4) (mid1.word (cs.take (mid1.i + 1)))
  w2 : HoldsW M (wB6 2) 18 (0 + 4) (mid2.word (cs.take (mid2.i + 1)))
  w3 : HoldsW M (wB6 3) 17 (0 + 4) (mid3.word (cs.take (mid3.i + 1)))
  w4 : HoldsW M (wB6 4) 16 (0 + 4) (finD.word (cs.take (finD.i + 1)))
  ch0 : ChOK M (F.ch 0) 6 rs0
  ch1 : ChOK M (F.ch 1) 4 rs1
  ch2 : ChOK M (F.ch 2) 4 rs2
  ch3 : ChOK M (F.ch 3) 4 rs3
  ch4 : ChOK M (F.ch 4) 4 rs4
  hi0 : SclOK M (F.hi 0) 6 o0.hi
  hi1 : SclOK M (F.hi 1) 4 o1.hi
  hi2 : SclOK M (F.hi 2) 4 o2.hi
  hi3 : SclOK M (F.hi 3) 4 o3.hi
  sc : SclOK M F.s (2 ^ 2 + 4) sc

theorem rdE2_agree {s₀ s : St} {b a : ℕ} (hA : Agree s₀ s b) (ha : regs ≤ a) (hb : a + 2 ≤ b) :
    rdE2 s.M a = rdE2 s₀.M a :=
  rdE2_of_frame (hA a ha (by omega)) (hA (a + 1) (by omega) (by omega))

theorem ChOK.agree {s₀ s : St} {b J : ℕ} {c : ℕ → ℕ} {rs : List (Rnd E2)} (h : ChOK s₀.M c J rs)
    (hA : Agree s₀ s b) (hc : ∀ k < J, regs ≤ c k ∧ c k + 4 ≤ b) : ChOK s.M c J rs := fun k hk ↦ by
  obtain ⟨c1, c2⟩ := hc k hk
  rw [rdE2_agree hA c1 (by omega), rdE2_agree hA (by omega) (by omega)]
  exact h k hk

theorem SclOK.agree {s₀ s : St} {b a n : ℕ} {v : List E2} (h : SclOK s₀.M a n v) (hA : Agree s₀ s b)
    (ha : regs ≤ a) (hb : a + 2 * n ≤ b) : SclOK s.M a n v := fun k hk ↦ by
  rw [rdE2_agree hA (by omega) (by omega)]
  exact h k hk

/-! ## Numbers -/

theorem num {i : ℕ} (h1 : 1 ≤ i) (h5 : i < 5) :
    rndD i = 4 ∧ ((gsD i).map GroupX.nr).sum = 4 ∧ 2 * 2 ^ 4 ≤ ncD i 4 ∧ 1 ≤ dD i ∧
    (∀ k ≤ 4, regs ≤ bfD i k ∧ bfD i k + bsz (ht6 i) 0 4 k ≤ 2 ^ 30 ∧ wB6 0 ≤ bfD i k) ∧
    (∀ k ≤ 4, ∀ k' ≤ 4, k ≠ k' → bfD i k + bsz (ht6 i) 0 4 k ≤ bfD i k' ∨
      bfD i k' + bsz (ht6 i) 0 4 k' ≤ bfD i k) ∧
    (∀ k ≤ 4, 1 ≤ k → bDep ≤ bfD i k ∧ bfD i k + bsz (ht6 i) 0 4 k ≤ colBD i) ∧
    (∀ k ≤ 4, (tbD i + 2 * 4 ≤ bfD i k ∨ bfD i k + bsz (ht6 i) 0 4 k ≤ tbD i) ∧
      (tSD i + 2 * 4 ≤ bfD i k ∨ bfD i k + bsz (ht6 i) 0 4 k ≤ tSD i)) ∧
    bDep ≤ tbD i ∧ tbD i + 2 * 4 ≤ tSD i ∧ tSD i + 2 * 4 ≤ colBD i ∧ bDep ≤ BD i ∧
    colBD i + 2 * strD i ≤ 2 ^ 30 ∧ bfD i 0 = wB6 i ∧ wB6 i + 2 * 2 ^ (ht6 i + (0 + 4)) ≤ bDep ∧
    wB6 0 ≤ wB6 i := by
  interval_cases i <;> decide +kernel

theorem num_0 :
    (∀ k ≤ 6, regs ≤ bfD 0 k ∧ bfD 0 k + bsz 20 0 6 k ≤ 2 ^ 30 ∧ wB6 0 + 48234496 ≤ bfD 0 k ∧
      bfD 0 k + bsz 20 0 6 k ≤ colBD 0) ∧
    (∀ k ≤ 6, ∀ k' ≤ 6, k ≠ k' → bfD 0 k + bsz 20 0 6 k ≤ bfD 0 k' ∨ bfD 0 k' + bsz 20 0 6 k' ≤ bfD 0 k) ∧
    (∀ k ≤ 6, (tbD 0 + 2 * 6 ≤ bfD 0 k ∨ bfD 0 k + bsz 20 0 6 k ≤ tbD 0) ∧
      (tSD 0 + 2 * 6 ≤ bfD 0 k ∨ bfD 0 k + bsz 20 0 6 k ≤ tSD 0)) ∧
    wB6 0 + 48234496 ≤ tbD 0 ∧ tbD 0 + 2 * 6 ≤ tSD 0 ∧ tSD 0 + 2 * 6 ≤ colBD 0 ∧ regs ≤ wB6 0 ∧
    ((gsD 0).map GroupX.nr).sum = 6 ∧ 67 ≤ ncD 0 6 ∧ wB6 0 + 48234496 ≤ bDep := by
  decide +kernel

/-! ## Levels 1–4 after their start -/

/-- **Levels 1–4**: the start program's facts at `s1` and the level's word and challenges in `s` give `LvRun`. -/
theorem lvRunD (I : Array Word) (F : FrontA) (hF : CellsOK F) {i : ℕ} (h1 : 1 ≤ i) (h5 : i < 5) (L : LevelX)
    (hL : L = ⟨L.tr, gsD i, BD i, colBD i, strD i⟩) {h : ℕ} (hh : ht6 i = h) (hh64 : h ≤ 64)
    (s s1 : St) (hsz : 2 ^ 30 ≤ s.M.size) (G : XIR)
    (htrE : L.tr = .seq G (trIR (ht6 i) 0 4 (bfD i) (F.ch i) (tbD i) (tSD i))) (hs1e : semXIR I G s = s1)
    (hG1 : Inv s1.M) (hG2 : s1.o = s.o) {Tc : CT E2 0}
    (hG3 : ColsRep (dD i) (fun q x ↦ rdK s1.M (colBD i + strD i * q + x)) Tc)
    (hG4 : ∀ x, regs ≤ x → (x < colBD i ∨ colBD i + 2 * strD i ≤ x) → rd s1.M x = rd s.M x)
    {rs : List (Rnd E2)} {Q : Wd E2 (2 ^ h) (0 + 4)}
    (hW : HoldsW s.M (wB6 i) h (0 + 4) Q) (hch : ChOK s.M (F.ch i) 4 rs) :
    LvRun I i L s h (dD i) (tbD i) (tSD i) 0 4 (ncD i) (2 * 2 ^ 4) bDep (domE h hh64) rs Q Tc := by
  subst hh
  have htr : semXIR I L.tr s = semXIR I (trIR (ht6 i) 0 4 (bfD i) (F.ch i) (tbD i) (tSD i)) s1 := by
    rw [htrE, semXIR_seq, hs1e]
  obtain ⟨tr, gs, B, colB, str⟩ := L
  cases hL
  have hw0 : wB6 0 = 134217728 := rfl
  have hreg : regs = 256 := rfl
  have hb18 : bDep = 331350016 := rfl
  have e30 : (2 : ℕ) ^ 30 = 1073741824 := by norm_num
  have e64 : (2 : ℕ) ^ 64 = 18446744073709551616 := by norm_num
  obtain ⟨n1, n2, n3, -, n5, n6, n7, n8, n9, n10, n11, n12, n13, n14, n15, n16⟩ := num h1 h5
  obtain ⟨l1, l2, l3, l4, l5, l6, l7, l8, l9, -, -, -⟩ := layoutD h5
  have hs1 : s1.M.size = s.M.size := by
    have := congrArg (fun t : St ↦ t.M.size) htr
    simp only [size_sem] at this
    exact this.symm
  have hcF : ∀ k < 4, regs ≤ F.ch i k ∧ F.ch i k + 4 ≤ wB6 0 := fun k hk ↦ hF.1 i h5 k (by rw [n1]; exact hk)
  have hW1 : HoldsW s1.M (bfD i 0) (ht6 i) (0 + 4) Q := by
    rw [n14]
    exact hW.of_frame fun x hx1 hx2 ↦ hG4 x (by omega) (Or.inl (by omega))
  have hch1 : ∀ k < 4, rdE2 s1.M (F.ch i k) = ((rs.map fun r ↦ (r.α, r.β)).getD k (0, 0)).1 ∧
      rdE2 s1.M (F.ch i k + 2) = ((rs.map fun r ↦ (r.α, r.β)).getD k (0, 0)).2 := fun k hk ↦ by
    obtain ⟨c1, c2⟩ := hcF k hk
    rw [rdE2_of_frame (hG4 _ c1 (Or.inl (by omega))) (hG4 _ (by omega) (Or.inl (by omega))),
      rdE2_of_frame (hG4 _ (by omega) (Or.inl (by omega))) (hG4 _ (by omega) (Or.inl (by omega)))]
    exact hch k hk
  obtain ⟨t1, t2, t3, t4, -, t6⟩ := trIR_sem I hh64 (m := 0) (j := 4) (bf := bfD i) (ch := F.ch i)
    (tb := tbD i) (tS := tSD i) (rs.map fun r ↦ (r.α, r.β)) Q s1 hG1 (by norm_num)
    (fun k hk ↦ ⟨(n5 k hk).1, by have := (n5 k hk).2.1; omega, by have := (n5 k hk).2.1; omega⟩)
    (fun k hk ↦ ⟨(hcF k hk).1, by have := (hcF k hk).2; omega⟩) n6
    (fun k hk k' hk1 hk2 ↦ Or.inl (le_trans (hcF k hk).2 (n5 k' hk2).2.2)) l8 l9 (Or.inl n10) (by omega)
    (by omega) (by omega) (by omega) n8 hW1 hch1
  rw [← htr] at t1 t2 t3 t4 t6
  have hM0 : 2 ^ 30 ≤ (semXIR I tr s).M.size := by rw [size_sem]; exact hsz
  refine lvRun_post I i ⟨tr, gsD i, BD i, colBD i, strD i⟩ s s1 rfl hh64
    (fun x ↦ (∀ k, 1 ≤ k → k ≤ 4 → x < bfD i k ∨ bfD i k + bsz (ht6 i) 0 4 k ≤ x) ∧
      (x < tbD i ∨ tbD i + 2 * 4 ≤ x) ∧ (x < tSD i ∨ tSD i + 2 * 4 ≤ x))
    hG2 hG3 (fun x hx hlx ↦ hG4 x hx (Or.inl (by have := n9; omega))) t1 t2 t3 t4
    (fun x hx ho ↦ t6 x hx ho.1 ho.2.1 ho.2.2)
    (fun x (hx1 : colBD i ≤ x) _ ↦ ⟨fun k k1 k2 ↦ Or.inr (by have := (n7 k k2 k1).2; omega), Or.inr (by omega),
      Or.inr (by omega)⟩) (show regs ≤ colBD i by omega)
    (fun x hx ↦ ⟨fun k k1 k2 ↦ Or.inl (by have := (n7 k k2 k1).1; omega), Or.inl (by omega), Or.inl (by omega)⟩)
    (fun k hk ↦ by have := (n5 k hk).2.1; omega) (by norm_num) l1 l4 l2 l3 l5 l6 l7 l8 l9 n12
    (fun hL' ↦ grpsOK h5 _ hM0 (by rw [n1]; exact t2) (fun r hr ↦ hL' r (by rw [n1] at hr; exact hr))) n2 n3

/-! ## The glue of levels 0–3 -/

/-- **The glue at level `i < 4`**: from level `i + 1`'s first 32 columns representing `Tc'` and the high part at
`F.hi i`, the start columns hold `candC (kapD i) Tc' hv`; the heap outside them is kept. -/
theorem glueD (I : Array Word) (F : FrontA) (hF : CellsOK F) {i : ℕ} (hi : i < 4) (s : St) (hM : Inv s.M)
    (hsz : 2 ^ 30 ≤ s.M.size) {Tc' : CT E2 4} {hv : List E2}
    (hsrc : ColsRepN (2 ^ kapD (i + 1) - 1 + 4) (2 * 2 ^ 4)
      (fun q x ↦ rdK s.M (colBD (i + 1) + strD (i + 1) * q + x)) Tc')
    (hhi : SclOK s.M (F.hi i) (rndD i) hv) :
    ColsRep (dD i) (fun q x ↦ rdK (semXIR I (glueIR (kapD (i + 1)) 4 (rndD i) (colBD (i + 1)) (strD (i + 1))
        (F.hi i) (colBD i) (strD i)) s).M (colBD i + strD i * q + x)) (candC (kapD i) Tc' hv) ∧
      (∀ x, regs ≤ x → (x < colBD i ∨ colBD i + 2 * strD i ≤ x) →
        rd (semXIR I (glueIR (kapD (i + 1)) 4 (rndD i) (colBD (i + 1)) (strD (i + 1)) (F.hi i) (colBD i)
          (strD i)) s).M x = rd s.M x) ∧
      Inv (semXIR I (glueIR (kapD (i + 1)) 4 (rndD i) (colBD (i + 1)) (strD (i + 1)) (F.hi i) (colBD i)
        (strD i)) s).M ∧
      (semXIR I (glueIR (kapD (i + 1)) 4 (rndD i) (colBD (i + 1)) (strD (i + 1)) (F.hi i) (colBD i)
        (strD i)) s).o = s.o := by
  obtain ⟨g0, g1, g2, g3, g4, g5, g6, g7, g8⟩ := glueLay hi
  have hw0 : wB6 0 = 134217728 := rfl
  have e30 : (2 : ℕ) ^ 30 = 1073741824 := by norm_num
  have e64 : (2 : ℕ) ^ 64 = 18446744073709551616 := by norm_num
  have e4 : (2 : ℕ) ^ 4 = 16 := by norm_num
  have hcw : wB6 0 ≤ colBD i := by interval_cases i <;> decide +kernel
  obtain ⟨hA1, hA2⟩ := hF.2.1 i hi
  obtain ⟨a1, a2, a3, a4⟩ := glueIR_cols I s hM (κ' := kapD (i + 1)) (ℓ' := 4) (ℓ := rndD i)
    (colB' := colBD (i + 1)) (str' := strD (i + 1)) (hA := F.hi i) (colB := colBD i) (str := strD i)
    g1 g2 hA1 g3 g4 g5 g6 (by omega) (by omega) g8 (Or.inr (by omega)) (Tc := Tc') (hi := hv)
    (fun u i' y hy ↦ hsrc u i' (by have := bitsToNat_lt u; have := i'.isLt; omega) y
      (by have := Nat.one_le_two_pow (n := kapD (i + 1)); omega)) hhi
  refine ⟨fun u i' x hx ↦ ?_, a2, a3, a4⟩
  have hx' : x < 2 ^ (4 + kapD (i + 1)) + rndD i := by
    have := Nat.one_le_two_pow (n := kapD i)
    simp only [dD] at hx; rw [g0] at hx this; omega
  rw [g0]
  exact a1 u i' x hx'

/-! ## Level 0 after its glue -/

/-- **Level 0**: the glue's facts at `s1`, the committed rows of commitment 0 and the challenges in `s` give
`LvRun` (X9's `tr0IR`: the expansion, the folds, the tables). -/
theorem lvRunD_0 (I : Array Word) (F : FrontA) (hF : CellsOK F) (L : LevelX)
    (hL : L = ⟨L.tr, gsD 0, BD 0, colBD 0, strD 0⟩) (s s1 : St) (hsz : 2 ^ 30 ≤ s.M.size) (G : XIR)
    (htrE : L.tr = .seq G (tr0IR 20 (wB6 0) (bfD 0) (F.ch 0) (tbD 0) (tSD 0))) (hs1e : semXIR I G s = s1)
    (hG1 : Inv s1.M) (hG2 : s1.o = s.o) {Tc : CT E2 0}
    (hG3 : ColsRep (dD 0) (fun q x ↦ rdK s1.M (colBD 0 + strD 0 * q + x)) Tc)
    (hG4 : ∀ x, regs ≤ x → (x < colBD 0 ∨ colBD 0 + 2 * strD 0 ≤ x) → rd s1.M x = rd s.M x)
    {cs : List (ℕ × ℕ × LeanVM.Protocol.Compile.Word)} {rs : List (Rnd E2)}
    (hrows : ∃ (row : ℕ → List BF64) (c : ℕ × ℕ × LeanVM.Protocol.Compile.Word), c.1 = 20 ∧
      (∀ p < 2 ^ 20, c.2.2 p = List.replicate 18 0 ++ row p) ∧
      wordE true 0 (0 + 6) 20 [c] = wordE true 0 (0 + 6) 20 cs ∧
      ∀ p < 2 ^ 20, ∀ t < 46, rdK s.M (wB6 0 + 46 * p + t) = (row p).getD t 0)
    (hch : ChOK s.M (F.ch 0) 6 rs) :
    LvRun I 0 L s 20 (dD 0) (tbD 0) (tSD 0) 0 6 (ncD 0) 67 0 (domE 20 (by norm_num)) rs
      (mid0.word (cs.take (mid0.i + 1))) Tc := by
  have htr : semXIR I L.tr s = semXIR I (tr0IR 20 (wB6 0) (bfD 0) (F.ch 0) (tbD 0) (tSD 0)) s1 := by
    rw [htrE, semXIR_seq, hs1e]
  obtain ⟨tr, gs, B, colB, str⟩ := L
  cases hL
  have hw0 : wB6 0 = 134217728 := rfl
  have hreg : regs = 256 := rfl
  have e30 : (2 : ℕ) ^ 30 = 1073741824 := by norm_num
  have e64 : (2 : ℕ) ^ 64 = 18446744073709551616 := by norm_num
  have e20 : (2 : ℕ) ^ 20 = 1048576 := by norm_num
  have hc0 : colBD 0 = 805306368 := rfl
  have hs0 : strD 0 = 1048576 := by norm_num [strD, ht6]
  have e46 : 46 * 2 ^ 20 = 48234496 := by norm_num
  obtain ⟨n1, n2, n3, -, n5, n6, -, -, -, -⟩ := num_0
  obtain ⟨l1, l2, l3, l4, l5, l6, l7, l8, l9, -, -, l12⟩ := layoutD (i := 0) (by norm_num)
  have hs1 : s1.M.size = s.M.size := by
    have := congrArg (fun t : St ↦ t.M.size) htr
    simp only [size_sem] at this
    exact this.symm
  have hcF : ∀ k < 6, regs ≤ F.ch 0 k ∧ F.ch 0 k + 4 ≤ wB6 0 := fun k hk ↦ hF.1 0 (by norm_num) k hk
  obtain ⟨row, c, hc1, hcr, hweq, hrow⟩ := hrows
  have hrow1 : ∀ p < 2 ^ 20, ∀ t < 46, rdK s1.M (wB6 0 + 46 * p + t) = (row p).getD t 0 := fun p hp t ht ↦ by
    rw [← hrow p hp t ht]
    simp only [rdK]
    rw [hG4 _ (by omega) (Or.inl (by omega))]
  have hch1 : ∀ k < 6, rdE2 s1.M (F.ch 0 k) = ((rs.map fun r ↦ (r.α, r.β)).getD k (0, 0)).1 ∧
      rdE2 s1.M (F.ch 0 k + 2) = ((rs.map fun r ↦ (r.α, r.β)).getD k (0, 0)).2 := fun k hk ↦ by
    obtain ⟨c1, c2⟩ := hcF k hk
    rw [rdE2_of_frame (hG4 _ c1 (Or.inl (by omega))) (hG4 _ (by omega) (Or.inl (by omega))),
      rdE2_of_frame (hG4 _ (by omega) (Or.inl (by omega))) (hG4 _ (by omega) (Or.inl (by omega)))]
    exact hch k hk
  obtain ⟨t1, t2, t3, t4, -, t6⟩ := tr0IR_sem I (h := 20) (by norm_num) (base := wB6 0) (bf := bfD 0)
    (ch := F.ch 0) (tb := tbD 0) (tS := tSD 0) (rs.map fun r ↦ (r.α, r.β)) s1 hG1 (by omega)
    (by rw [e46, hw0]; norm_num) (Or.inl (by rw [e46]; exact (n1 0 (by norm_num)).2.2.1)) row hrow1
    (cs := [c]) rfl hc1 hcr
    (fun k hk ↦ ⟨(n1 k hk).1, by have := (n1 k hk).2.1; omega, by have := (n1 k hk).2.1; omega⟩)
    (fun k hk ↦ ⟨(hcF k hk).1, by have := (hcF k hk).2; omega⟩) n2
    (fun k hk k' hk' ↦ Or.inl (by have := (hcF k hk).2; have := (n1 k' hk').2.2.1; omega)) l8 l9 (Or.inl n5)
    (by omega) (by omega) (by omega) (by omega) n3 hch1
  rw [hweq, ← ladD_word_take cs] at t1
  rw [← htr] at t1 t2 t3 t4 t6
  have hM0 : 2 ^ 30 ≤ (semXIR I tr s).M.size := by rw [size_sem]; exact hsz
  refine lvRun_post I 0 ⟨tr, gsD 0, BD 0, colBD 0, strD 0⟩ s s1 (h := 20) rfl (by norm_num)
    (fun x ↦ (∀ k ≤ 6, x < bfD 0 k ∨ bfD 0 k + bsz 20 0 6 k ≤ x) ∧
      (x < tbD 0 ∨ tbD 0 + 2 * 6 ≤ x) ∧ (x < tSD 0 ∨ tSD 0 + 2 * 6 ≤ x))
    hG2 hG3 (fun x _ hlx ↦ absurd hlx (Nat.not_lt_zero x)) t1 t2 t3 t4
    (fun x hx ho ↦ t6 x hx ho.1 ho.2.1 ho.2.2)
    (fun x (hx1 : colBD 0 ≤ x) _ ↦ ⟨fun k hk ↦ Or.inr (by have := (n1 k hk).2.2.2; omega), Or.inr (by omega),
      Or.inr (by omega)⟩) (show regs ≤ colBD 0 by omega) (fun x hx ↦ absurd hx (Nat.not_lt_zero x))
    (fun k hk ↦ by have := (n1 k hk).2.1; omega) (by norm_num) l1 l4 l2 l3 l5 l6 l7 l8 l9 (Nat.zero_le _)
    (fun hL' ↦ grpsOK (i := 0) (by norm_num) _ hM0 t2 hL') num_0.2.2.2.2.2.2.2.1 num_0.2.2.2.2.2.2.2.2.1

/-! ## The descent's inputs from the front -/

theorem lvRun_size (I : Array Word) (Lv : ℕ → LevelX) (s₀ : St) : ∀ j, (lvRun I Lv s₀ j).M.size = s₀.M.size
  | 0 => rfl
  | j + 1 => by simp only [lvRun, size_sem]; exact lvRun_size I Lv s₀ j

/-- **A mid level `1 ≤ i < 4`'s inputs** from the front's facts (below `bDep`, still the front's) and the next level's
columns. -/
theorem glueRun (I : Array Word) (F : FrontA) (hF : CellsOK F) {i : ℕ} (h1 : 1 ≤ i) (hi : i < 4) {h : ℕ}
    (hh : ht6 i = h) (hh64 : h ≤ 64) (s₀ s : St) (hA : Agree s₀ s bDep) (hI : Inv s.M) (hsz : 2 ^ 30 ≤ s.M.size)
    {Tc' : CT E2 4} (hsrc : ColsRepN (2 ^ kapD (i + 1) - 1 + 4) (2 * 2 ^ 4)
      (fun q x ↦ rdK s.M (colBD (i + 1) + strD (i + 1) * q + x)) Tc')
    {hv : List E2} (hhi : SclOK s₀.M (F.hi i) 4 hv) {rs : List (Rnd E2)} {Q : Wd E2 (2 ^ h) (0 + 4)}
    (hW : HoldsW s₀.M (wB6 i) h (0 + 4) Q) (hch : ChOK s₀.M (F.ch i) 4 rs)
    (hL : LvD F i = ⟨(LvD F i).tr, gsD i, BD i, colBD i, strD i⟩)
    (htrE : (LvD F i).tr = .seq (glueIR (kapD (i + 1)) 4 (rndD i) (colBD (i + 1)) (strD (i + 1)) (F.hi i)
      (colBD i) (strD i)) (trIR (ht6 i) 0 4 (bfD i) (F.ch i) (tbD i) (tSD i))) :
    LvRun I i (LvD F i) s h (dD i) (tbD i) (tSD i) 0 4 (ncD i) (2 * 2 ^ 4) bDep (domE h hh64) rs Q
      (candC (kapD i) Tc' hv) := by
  obtain ⟨n1, -, -, -, -, -, -, -, -, -, -, -, -, -, n15, n16⟩ := num h1 (by omega)
  have hw0 : wB6 0 = 134217728 := rfl
  have hreg : regs = 256 := rfl
  have hb18 : bDep = 331350016 := rfl
  have hhi' : SclOK s.M (F.hi i) (rndD i) hv := by
    rw [n1]; have := hF.2.1 i hi; rw [n1] at this
    exact hhi.agree hA this.1 (by omega)
  obtain ⟨g1, g2, g3, g4⟩ := glueD I F hF hi s hI hsz hsrc hhi'
  subst hh
  exact lvRunD I F hF h1 (by omega) (LvD F i) hL rfl hh64 s _ hsz _ htrE rfl g3 g4 g1 g2
    (hW.of_frame fun x hx1 hx2 ↦ hA x (by omega) (by omega))
    (hch.agree hA fun k hk ↦ by have := hF.1 i (by omega) k (by rw [n1]; exact hk); omega)

/-- **The descent's machine inputs at `P17`** from the front's heap facts, for every decomposition of the log. -/
theorem mach_of (I : Array Word) (F : FrontA) (hF : CellsOK F) (s₀ : St) (hM : Inv s₀.M)
    (hsz : 2 ^ 30 ≤ s₀.M.size) (cs : List (ℕ × ℕ × LeanVM.Protocol.Compile.Word)) (l : List Ev)
    (hH : ∀ rs0 o0 l1 rs1 o1 l2 rs2 o2 l3 rs3 o3 l4 rs4 sc,
      RunMid mid0 l rs0 o0 l1 → RunMid mid1 l1 rs1 o1 l2 → RunMid mid2 l2 rs2 o2 l3 → RunMid mid3 l3 rs3 o3 l4 →
      RunFin finD l4 rs4 sc → FrontHeap F s₀.M cs rs0 o0 rs1 o1 rs2 o2 rs3 o3 rs4 sc) :
    Mach I (LvD F) 67 bDep s₀ cs l := by
  intro rs0 o0 l1 rs1 o1 l2 rs2 o2 l3 rs3 o3 l4 rs4 sc r0 r1 r2 r3 r4
  have H := hH rs0 o0 l1 rs1 o1 l2 rs2 o2 l3 rs3 o3 l4 rs4 sc r0 r1 r2 r3 r4
  have hw0 : wB6 0 = 134217728 := rfl
  have hreg : regs = 256 := rfl
  have hb18 : bDep = 331350016 := rfl
  have e30 : (2 : ℕ) ^ 30 = 1073741824 := by norm_num
  have e64 : (2 : ℕ) ^ 64 = 18446744073709551616 := by norm_num
  have hS : ∀ j, 2 ^ 30 ≤ (lvRun I (LvD F) s₀ j).M.size := fun j ↦ by rw [lvRun_size]; exact hsz
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · -- level 4: the start `s`
    obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, n15, n16⟩ := num (i := 4) (by norm_num) (by norm_num)
    obtain ⟨-, -, -, -, -, -, -, -, -, -, -, l12⟩ := layoutD (i := 4) (by norm_num)
    have hc4 : colBD 4 = 470696192 := rfl
    have hs4 : strD 4 = 65536 := by norm_num [strD, ht6]
    obtain ⟨hs1, hs2⟩ := hF.2.2
    obtain ⟨a1, a2, a3, a4⟩ := startIR_cols I s₀ hM (κ := 2) (ℓ := 4) (sA := F.s) (colB := colBD 4)
      (str := strD 4) (by omega) hs1 (by norm_num [hs4]) (by omega) (by omega) (by omega) (Or.inr (by omega))
      H.sc
    refine ⟨tbD 4, tSD 4, ncD 4, fun _ x ↦ sc.getD x 0, rep_start_4 sc, ?_⟩
    exact lvRunD I F hF (i := 4) (by norm_num) (by norm_num) (LvD F 4) rfl rfl (by decide) s₀ _ hsz _ rfl rfl a3 a4
      (fun u i' x hx ↦ a1 u i' x (by have : dD 4 = 2 ^ 2 - 1 + 4 := rfl; omega)) a2 H.w4 H.ch4
  · intro U ⟨Tc', hR', hcols⟩ hA hI
    exact ⟨tbD 3, tSD 3, ncD 3, candC (kapD 3) Tc' o3.hi, rep_start_3 hR' o3.hi,
      glueRun I F hF (i := 3) (by norm_num) (by norm_num) rfl (by decide) s₀ _ hA hI (hS 1) hcols H.hi3 H.w3
        H.ch3 rfl rfl⟩
  · intro U ⟨Tc', hR', hcols⟩ hA hI
    exact ⟨tbD 2, tSD 2, ncD 2, candC (kapD 2) Tc' o2.hi, rep_start_2 hR' o2.hi,
      glueRun I F hF (i := 2) (by norm_num) (by norm_num) rfl (by decide) s₀ _ hA hI (hS 2) hcols H.hi2 H.w2
        H.ch2 rfl rfl⟩
  · intro U ⟨Tc', hR', hcols⟩ hA hI
    exact ⟨tbD 1, tSD 1, ncD 1, candC (kapD 1) Tc' o1.hi, rep_start_1 hR' o1.hi,
      glueRun I F hF (i := 1) (by norm_num) (by norm_num) rfl (by decide) s₀ _ hA hI (hS 3) hcols H.hi1 H.w1
        H.ch1 rfl rfl⟩
  · intro U ⟨Tc', hR', hcols⟩ hA hI
    have hhi : SclOK (lvRun I (LvD F) s₀ 4).M (F.hi 0) (rndD 0) o0.hi :=
      H.hi0.agree hA (hF.2.1 0 (by norm_num)).1 (by have := (hF.2.1 0 (by norm_num)).2; omega)
    obtain ⟨g1, g2, g3, g4⟩ := glueD I F hF (i := 0) (by norm_num) _ hI (hS 4) hcols hhi
    obtain ⟨row, c, hc1, hcr, hweq, hrow⟩ := H.rows0
    have e20 : (2 : ℕ) ^ 20 = 1048576 := by norm_num
    refine ⟨tbD 0, tSD 0, ncD 0, candC (kapD 0) Tc' o0.hi, rep_start_0 hR' o0.hi, ?_⟩
    exact lvRunD_0 I F hF (LvD F 0) rfl _ _ (hS 4) _ rfl rfl g3 g4 g1 g2
      ⟨row, c, hc1, hcr, hweq, fun p hp t ht ↦ by
        rw [← hrow p hp t ht]; simp only [rdK]; rw [hA _ (by omega) (by omega)]⟩
      (H.ch0.agree hA fun k hk ↦ by have := hF.1 0 (by norm_num) k hk; omega)

/-! ## The output map -/

/-- **`finX` writes `decD U`** from level 0's first 67 columns representing `U`. -/
theorem finOut (F : FrontA) : FinOut finX (LvD F 0) 67 := by
  intro I s U ⟨Tc, hR, hC⟩ hI hO hsz
  have hc0 : colBD 0 = 805306368 := rfl
  have hs0 : strD 0 = 1048576 := by norm_num [strD, ht6]
  have hst : stride6 = 262144 := rfl
  have hcb : colB6 = 67108864 := rfl
  have hreg : regs = 256 := rfl
  have e64 : (2 : ℕ) ^ 64 = 18446744073709551616 := by norm_num
  have e30 : (2 : ℕ) ^ 30 = 1073741824 := by norm_num
  have hsrc : ∀ m < 34, regs ≤ colBD 0 + strD 0 * (2 * m) ∧ colBD 0 + strD 0 * (2 * m) + stride6 < 2 ^ 64 ∧
      (colBD 0 + strD 0 * (2 * m) + stride6 ≤ colB6 ∨ colB6 + 34 * stride6 ≤ colBD 0 + strD 0 * (2 * m)) :=
    fun m hm ↦ by rw [hs0]; omega
  obtain ⟨-, -, f3, f4⟩ := finIR_sem I (fun m ↦ colBD 0 + strD 0 * (2 * m)) hsrc 34 le_rfl s hI (by omega)
  refine ⟨f3, f4.trans hO, finIR_heapHolds I _ hsrc s hI (by omega) _ fun m hm r hr ↦ ?_⟩
  let u : Fin (0 + 6) → Bool := fun i ↦ m.testBit i
  have hu : bitsToNat u = m := bitsToNat_testBit (κ := 0 + 6) (by norm_num; omega)
  have e1 : (fun i : Fin (0 + 6) ↦ (m * stride6 + r).testBit (18 + i)) = u := funext fun i ↦ by
    rw [show 18 + (i : ℕ) = i + 18 by omega, ← Nat.testBit_div_two_pow,
      show (m * stride6 + r) / 2 ^ 18 = m by rw [hst]; omega]
  have e2 : bitsToNat (fun i : Fin 18 ↦ (m * stride6 + r).testBit i) = r := by
    have : (fun i : Fin 18 ↦ (m * stride6 + r).testBit i) = fun i : Fin 18 ↦ r.testBit i := funext fun i ↦ by
      have hr' : (m * stride6 + r) % 2 ^ 18 = r := by rw [hst]; omega
      conv_rhs => rw [← hr']
      rw [Nat.testBit_mod_two_pow, decide_eq_true i.isLt, Bool.true_and]
    rw [this]
    exact bitsToNat_testBit (by rw [hst] at hr; omega)
  have hc := hC u 0 (by rw [hu]; show 2 * m + 0 < 67; omega) r (by rw [hst] at hr; norm_num; omega)
  rw [hu, coord0_E2] at hc
  have hc2 : rdK s.M (colBD 0 + strD 0 * (2 * m) + r) = (Tc u r).re := hc
  simp only [stW]
  rw [decD_of_rep hR, e1, e2]
  exact congrArg BF64.toBitVec hc2

/-! ## `FrontIn` and the assembly -/

section Assembly

open Lvm Lvm.T Lvm.FS
open scoped NNReal ENNReal

/-- The state after the front and the fill (`parse ; front6 ; fill`). -/
def fillStG (fill : XIR) (c : Digest) (π : Proof) (L : Log) : St :=
  semXIR (extractorInput c π L).toArray fill (front6St c π L)

/-- **The front's facts** (EXF; open): on an `S` proof of `pz6` bytes of the composed scheme whose history has the
opening at `N₀`, the state after `parse ; front6 ; fill` has `Inv`, no output, and, for every
decomposition of the opening's log `h.drop N₀` into the levels' runs, the rows of the five commitments, the
challenge pairs, the high parts and the final scalars at FrontA's cells (`FrontHeap`). -/
def FrontIn (Φ : Phases) (fill : XIR) (F : FrontA) : Prop :=
  ∀ vk c π L x h, (schemeOf (prog6 Φ) P17 vk).Ex (fun _ x h ↦ (x, h)) c π L = some (x, h) → π.size = pz6 →
    ∀ N₀ (cl : StackClaim6), (whirP cl).after (h.drop N₀) = some (.ret true) →
      Inv (fillStG fill c π L).M ∧ (fillStG fill c π L).o = #[] ∧
      ∀ rs0 o0 l1 rs1 o1 l2 rs2 o2 l3 rs3 o3 l4 rs4 sc,
        RunMid mid0 (h.drop N₀) rs0 o0 l1 → RunMid mid1 l1 rs1 o1 l2 → RunMid mid2 l2 rs2 o2 l3 →
        RunMid mid3 l3 rs3 o3 l4 → RunFin finD l4 rs4 sc →
        FrontHeap F (fillStG fill c π L).M (LeanVM.Protocol.Compile.commits h) rs0 o0 rs1 o1 rs2 o2 rs3 o3 rs4 sc

/-- **`DescIn` at `P17`** from the front's facts (EXG's levels and glue discharged). -/
theorem descIn {Φ : Phases} {fill : XIR} {F : FrontA} (hFr : FrontIn Φ fill F) (hF : CellsOK F) :
    DescIn Φ fill (LvD F) 67 bDep := by
  intro vk c π L x h hE hl N₀ cl h1
  obtain ⟨hI, hO, hH⟩ := hFr vk c π L x h hE hl N₀ cl h1
  have hsz : 2 ^ 30 ≤ (fillStG fill c π L).M.size := by
    simp only [fillStG, size_sem]; exact front6St_size c π L
  exact ⟨hI, hO, mach_of _ F hF _ hI hsz _ _ hH⟩

/-- **`DescProg6` at `P17`** from the front's facts. -/
theorem descProg6 {Φ : Phases} {fill : XIR} {F : FrontA} (hFr : FrontIn Φ fill F) (hF : CellsOK F) :
    DescProg6 Φ (.seq fill (descX6 (LvD F) finX)) :=
  descProg6_of (descIn hFr hF) (finOut F)

variable {Φ : Phases} {SGood TGood : Hdr → Stack → Prop} (H : PhaseSpecs Φ Whir.I6 SGood TGood)
  (HG : Stmt.openGoodC Whir.GWDc Φ.whir) (hPF : PhasesFollow Φ P17) {VS : Shape → SProg}
  (Xe : ∀ vk, Ext6 (schemeOf (prog6 Φ) P17 vk) (Rel (accV (VS P17) vk)) (G6 SGood TGood))

include H HG hPF in
/-- **The extractor's fields of `Open6` at `P17`**: from the front's facts (`FrontIn`, EXF) with FrontA's cells in
`[regs, wB6 0)`, and the structure and size of `fill ; descX6 (LvD F) finX` (EXG's `descOk6`,
`sizeIR_desc` with EXF's `fill`). -/
theorem open6XFront (hw : Φ.whir = whirAt Whir.whirP) {fill : XIR} {F : FrontA}
    (hX : ∀ vk, (Xe vk).ext = ExtSpec6 (Whir.I6 P17)) (hFr : FrontIn Φ fill F) (hF : CellsOK F)
    (hok : DescOk6 (.seq fill (descX6 (LvD F) finX)))
    (hsz : sizeIR (.seq fill (descX6 (LvD F) finX)) ≤ 2 ^ 19) :
    (∀ vk, ∃ K : KCert (schemeOf (prog6 Φ) P17 vk) (Rel (accV (VS P17) vk)),
      Scheme.εFS K ≤ (2 : ℝ≥0)⁻¹ ^ 128 ∧ ExtEq6 (EX6 (.seq fill (descX6 (LvD F) finX))) K) ∧
    (∀ c π L, isS π = false → EX6 (.seq fill (descX6 (LvD F) finX)) c π L =
      RecursionFast.WitnessSending.decode π) ∧
    Computes (extX6 (.seq fill (descX6 (LvD F) finX))) (EX6 (.seq fill (descX6 (LvD F) finX))) fuel6 ∧
    (extX6 (.seq fill (descX6 (LvD F) finX))).body.size ≤ progCap :=
  open6XI H HG hPF Xe hw hX (descIn hFr hF) (finOut F) hok hsz

end Assembly

end Lvm6.X
