-- G6: this module also holds the former modules `FRXFlag`, `FRXReadLv` (one section each, in import order).
import FRXEqT
import FRXLag
import FRXRead
import FRXChainFlock

section G6_FRXFlag

-- New for `flock-recursive` (BLUEPRINT §6.2 step 4, the K-folds and the agreement set; stage
-- S-H2, track L-ext).

/-!
# The column folds and the agreement flags on the machine

Level `i`'s agreement flag at position `j` tests `j ∈ consSet` in `F` coordinates
(`FRXLevel.mem_consSet_iff`):

`Σ_r W[r][j]·E[r].f_c = Enc(f⁽ⁱ⁺¹⁾.f_c)[j]` for `c = 0, 1`.

* the word `W[r][j]` sits at `cb + cs·j + 2r` (`readLv_spec_F`; level 0: `colBase`, `cs = 128`);
* the `eq` table `E[r]` (K) at `eb + 4r` (`eqtIR_sem`): `f₀` at `eb + 4r`, `f₁` at `eb + 4r + 2`;
* the encodings `Enc₀[j]`, `Enc₁[j]` at `xb + 2j` and `yb + 2j` (`fwdIR_enc`).

The program `flagIR n R cs cb eb xb yb fb` writes the flag word `[both equal]` at `fb + j` for
`j < n`, the input of `scanIR`.

* `fBody_sem`: one row's two products;
* `cmp_word`: the zero test of the four word differences is the two `F` equalities;
* `fEnt_sem`: one position (the row loop, the comparison, the store at `fb + j`);
* **`flagIR_sem`**: the flags `flagV` of the initial heap, and the heap outside `[fb, fb + n)` kept;
* **`flagV_consSet`**: the flag is nonzero iff `j ∈ A_c` (`mem_consSet_iff`);
* control `toyFlag_run` (a kernel run: one agreeing and one disagreeing position).

Registers `190 … 213` (the chain's, free after the replay; the `eq` table's are not live here).
-/

namespace FR.X

open RecursionFast FR Finset

attribute [local irreducible] entryK storeM runPrims

/-! ## Registers and the program -/

/-- The accumulator of `f₀`. -/ def fa0 : ℕ := 190
/-- The accumulator of `f₁`. -/ def fa1 : ℕ := 192
/-- `W[r][j]`. -/ def fw : ℕ := 194
/-- A loaded element. -/ def fe : ℕ := 196
/-- A product. -/ def fp : ℕ := 198
/-- The address of `W[r][j]`. -/ def gW : ℕ := 202
/-- The address of `E[r]`. -/ def gE : ℕ := 203
/-- The loads' scratch. -/ def gA1 : ℕ := 204
/-- A second address. -/ def gT : ℕ := 205
/-- Constant scratch. -/ def gK : ℕ := 206
/-- The position `j`. -/ def gJ : ℕ := 207
/-- The flag. -/ def gZ : ℕ := 208
/-- A second flag. -/ def gZ2 : ℕ := 209
/-- Counter of the position loop. -/ def gC1 : ℕ := 210
/-- Its count. -/ def gN1 : ℕ := 211
/-- Counter of the row loop. -/ def gC2 : ℕ := 212
/-- Its count. -/ def gN2 : ℕ := 213

/-- `gT := gE + 2`. -/
def tPs : List Prim := [.const gK 2, .op .add gT gE gK]

/-- `gW += 2`, `gE += 4`. -/
def stepPs : List Prim := [.const gK 2, .op .add gW gW gK, .const gK 4, .op .add gE gE gK]

/-- **One row** `r`: `acc₀ += W·E.f₀`, `acc₁ += W·E.f₁`. -/
def fBody : XIR :=
  .seq (ldF fw gW gA1) (.seq (ldF fe gE gA1) (.seq (mulF fp fw fe) (.seq (addF fa0 fa0 fp)
    (.seq (.blk tPs) (.seq (ldF fe gT gA1) (.seq (mulF fp fw fe) (.seq (addF fa1 fa1 fp)
      (.blk stepPs))))))))

/-! ## Block lemmas -/

theorem tPs_sem (I : Array Word) (s : St) (hM : Inv s.M) {e : ℕ} (hE : rd s.M gE = toWord e) :
    rd (semXIR I (.blk tPs) s).M gT = toWord (e + 2) ∧
    (∀ i, i ≠ gK → i ≠ gT → rd (semXIR I (.blk tPs) s).M i = rd s.M i) ∧
    Inv (semXIR I (.blk tPs) s).M := by
  have hs := hM.1
  simp only [regs] at hs
  have e0 : semXIR I (.blk tPs) s = ⟨runPrims tPs s.M, s.o⟩ := rfl
  simp only [e0]
  refine ⟨?_, fun i h1 h2 => rd_runPrims_of_not_writes (by
    intro p hp
    simp only [tPs, List.mem_cons, List.mem_nil_iff, or_false] at hp
    rcases hp with rfl | rfl <;> simp only [Prim.dst] <;>
      first | exact Ne.symm h1 | exact Ne.symm h2) _,
    inv_runPrims (by simp [tPs, Prim.dst, gK, gT]) hM⟩
  simp only [tPs, runPrims, List.foldl, Prim.run]
  simp (disch := first | decide | (simp only [size_set, gK, gT]; omega)) only
    [rd_set_self, rd_set_ne]
  rw [hE, show (2 : Word) = toWord 2 from rfl, add_toWord]

theorem stepPs_sem (I : Array Word) (s : St) (hM : Inv s.M) {w e : ℕ} (hW : rd s.M gW = toWord w)
    (hE : rd s.M gE = toWord e) :
    rd (semXIR I (.blk stepPs) s).M gW = toWord (w + 2) ∧
    rd (semXIR I (.blk stepPs) s).M gE = toWord (e + 4) ∧
    (∀ i, i ≠ gK → i ≠ gW → i ≠ gE → rd (semXIR I (.blk stepPs) s).M i = rd s.M i) ∧
    Inv (semXIR I (.blk stepPs) s).M := by
  have hs := hM.1
  simp only [regs] at hs
  have e0 : semXIR I (.blk stepPs) s = ⟨runPrims stepPs s.M, s.o⟩ := rfl
  simp only [e0]
  refine ⟨?_, ?_, fun i h1 h2 h3 => rd_runPrims_of_not_writes (by
    intro p hp
    simp only [stepPs, List.mem_cons, List.mem_nil_iff, or_false] at hp
    rcases hp with rfl | rfl | rfl | rfl <;> simp only [Prim.dst] <;>
      first | exact Ne.symm h1 | exact Ne.symm h2 | exact Ne.symm h3) _,
    inv_runPrims (by simp [stepPs, Prim.dst, gK, gW, gE]) hM⟩
  all_goals simp only [stepPs, runPrims, List.foldl, Prim.run]
  all_goals simp (disch := first | decide | (simp only [size_set, gK, gW, gE]; omega)) only
    [rd_set_self, rd_set_ne]
  · rw [hW, show (2 : Word) = toWord 2 from rfl, add_toWord]
  · rw [hE, show (4 : Word) = toWord 4 from rfl, add_toWord]

/-! ## One row -/

/-- **One row**: with `W` at `w = M[gW]` and `E` at `e = M[gE]`, the accumulators gain
`W·E.f₀` and `W·E.f₁`; `gW += 2`, `gE += 4`; the heap and the loop registers are kept. -/
theorem fBody_sem (I : Array Word) (s : St) (hM : Inv s.M) {w e : ℕ}
    (hw : regs ≤ w) (hw2 : w + 2 < 2 ^ 64) (he : regs ≤ e) (he2 : e + 4 < 2 ^ 64)
    (hW : rd s.M gW = toWord w) (hE : rd s.M gE = toWord e) :
    rdF (semXIR I fBody s).M fa0 = rdF s.M fa0 + rdF s.M w * rdF s.M e ∧
    rdF (semXIR I fBody s).M fa1 = rdF s.M fa1 + rdF s.M w * rdF s.M (e + 2) ∧
    rd (semXIR I fBody s).M gW = toWord (w + 2) ∧
    rd (semXIR I fBody s).M gE = toWord (e + 4) ∧
    (∀ i, (regs ≤ i ∨ i = gJ ∨ i = gC1 ∨ i = gN1 ∨ i = gC2 ∨ i = gN2) →
      rd (semXIR I fBody s).M i = rd s.M i) ∧
    Inv (semXIR I fBody s).M := by
  have hs := hM.1
  simp only [regs] at hs hw he
  -- `W`
  rw [fBody, semXIR_seq]
  obtain ⟨u1, -, u3⟩ := ldF_sem I s hM (d := fw) (p := gW) (p1 := gA1) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) hW (by simp only [regs]; omega) (by omega)
  have hM1 := inv_sem I (P := ldF fw gW gA1) (by simp +decide only [ldF, WF, Prim.dst, fw, gA1,
    and_true]) hM
  generalize semXIR I (ldF fw gW gA1) s = s1 at u1 u3 hM1
  -- `E.f₀`
  rw [semXIR_seq]
  obtain ⟨v1, -, v3⟩ := ldF_sem I s1 hM1 (d := fe) (p := gE) (p1 := gA1) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide)
    ((u3 _ (by decide) (by decide) (by decide)).trans hE) (by simp only [regs]; omega) (by omega)
  have hM2 := inv_sem I (P := ldF fe gE gA1) (by simp +decide only [ldF, WF, Prim.dst, fe, gA1,
    and_true]) hM1
  generalize semXIR I (ldF fe gE gA1) s1 = s2 at v1 v3 hM2
  -- the frame so far: cells other than `fw, fe, gA1` and their successors
  have e2 : ∀ i, i ≠ fw → i ≠ fw + 1 → i ≠ fe → i ≠ fe + 1 → i ≠ gA1 → rd s2.M i = rd s.M i :=
    fun i h1 h2 h3 h4 h5 => by rw [v3 i h3 h4 h5, u3 i h1 h2 h5]
  have hw2' : rdF s2.M fw = rdF s.M w :=
    (rdF_eq (v3 _ (by decide) (by decide) (by decide)) (v3 _ (by decide) (by decide) (by decide))).trans u1
  have he2' : rdF s2.M fe = rdF s.M e := by
    rw [v1]; exact rdF_eq (u3 _ (by simp only [fw]; omega) (by simp only [fw]; omega)
      (by simp only [gA1]; omega)) (u3 _ (by simp only [fw]; omega) (by simp only [fw]; omega)
      (by simp only [gA1]; omega))
  -- `acc₀ += W·E.f₀`
  rw [semXIR_seq, semXIR_seq]
  have m3 := mulF_sem (I := I) (s := s2) hM2 (d := fp) (a := fw) (b := fe) (by decide) (by decide)
    (by decide) (by decide)
  have f3 : ∀ i, 15 ≤ i → i ≠ fp → i ≠ fp + 1 → rd (semXIR I (mulF fp fw fe) s2).M i = rd s2.M i :=
    fun i h0 h1 h2 => fr_mulF h0 h1 h2
  have hH3 := hframe I (mulF fp fw fe) s2 (lo_mulF (by decide))
  have hM3 := inv_sem I (wf_mulF fp fw fe (by decide)) hM2
  generalize semXIR I (mulF fp fw fe) s2 = s3 at m3 f3 hH3 hM3
  have a4 := addF_sem (I := I) (s := s3) hM3 (d := fa0) (a := fa0) (b := fp) (by decide) (by decide)
    (by decide)
  have f4 : ∀ i, i ≠ fa0 → i ≠ fa0 + 1 → rd (semXIR I (addF fa0 fa0 fp) s3).M i = rd s3.M i :=
    fun i h1 h2 => fr_addF h1 h2
  have hM4 := inv_sem I (wf_addF fa0 fa0 fp (by decide)) hM3
  generalize semXIR I (addF fa0 fa0 fp) s3 = s4 at a4 f4 hM4
  have acc0 : rdF s4.M fa0 = rdF s.M fa0 + rdF s.M w * rdF s.M e := by
    rw [a4, m3, hw2', he2', rdF_eq (f3 _ (by decide) (by decide) (by decide))
      (f3 _ (by decide) (by decide) (by decide)), rdF_eq (e2 _ (by decide) (by decide) (by decide)
      (by decide) (by decide)) (e2 _ (by decide) (by decide) (by decide) (by decide) (by decide))]
  -- the frame through `s4`
  have e4 : ∀ i, 15 ≤ i → i ≠ fw → i ≠ fw + 1 → i ≠ fe → i ≠ fe + 1 → i ≠ gA1 → i ≠ fp →
      i ≠ fp + 1 → i ≠ fa0 → i ≠ fa0 + 1 → rd s4.M i = rd s.M i :=
    fun i h0 h1 h2 h3 h4 h5 h6 h7 h8 h9 => by rw [f4 i h8 h9, f3 i h0 h6 h7, e2 i h1 h2 h3 h4 h5]
  -- `E.f₁`
  rw [semXIR_seq]
  obtain ⟨t1, t2, hM5⟩ := tPs_sem I s4 hM4 (e := e)
    ((e4 _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide)).trans hE)
  generalize semXIR I (.blk tPs) s4 = s5 at t1 t2 hM5
  rw [semXIR_seq]
  obtain ⟨y1, -, y3⟩ := ldF_sem I s5 hM5 (d := fe) (p := gT) (p1 := gA1) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) t1 (by simp only [regs]; omega) (by omega)
  have hM6 := inv_sem I (P := ldF fe gT gA1) (by simp +decide only [ldF, WF, Prim.dst, fe, gA1,
    and_true]) hM5
  generalize semXIR I (ldF fe gT gA1) s5 = s6 at y1 y3 hM6
  have e6 : ∀ i, 15 ≤ i → i ≠ fw → i ≠ fw + 1 → i ≠ fe → i ≠ fe + 1 → i ≠ gA1 → i ≠ fp →
      i ≠ fp + 1 → i ≠ fa0 → i ≠ fa0 + 1 → i ≠ gK → i ≠ gT → rd s6.M i = rd s.M i :=
    fun i h0 h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 => by
      rw [y3 i h3 h4 h5, t2 i h10 h11, e4 i h0 h1 h2 h3 h4 h5 h6 h7 h8 h9]
  have hw6 : rdF s6.M fw = rdF s.M w := by
    rw [← hw2']
    exact rdF_eq ((y3 _ (by decide) (by decide) (by decide)).trans ((t2 _ (by decide) (by decide)).trans
      ((f4 _ (by decide) (by decide)).trans (f3 _ (by decide) (by decide) (by decide)))))
      ((y3 _ (by decide) (by decide) (by decide)).trans ((t2 _ (by decide) (by decide)).trans
      ((f4 _ (by decide) (by decide)).trans (f3 _ (by decide) (by decide) (by decide)))))
  have hh5 : ∀ i, regs ≤ i → rd s5.M i = rd s.M i := fun i hi => by
    simp only [regs] at hi
    rw [t2 i (by simp only [gK]; omega) (by simp only [gT]; omega)]
    exact e4 i (by omega) (by simp only [fw]; omega) (by simp only [fw]; omega)
      (by simp only [fe]; omega) (by simp only [fe]; omega) (by simp only [gA1]; omega)
      (by simp only [fp]; omega) (by simp only [fp]; omega) (by simp only [fa0]; omega)
      (by simp only [fa0]; omega)
  have he6 : rdF s6.M fe = rdF s.M (e + 2) := by
    rw [y1]
    exact rdF_eq (hh5 _ (by simp only [regs]; omega)) (hh5 _ (by simp only [regs]; omega))
  -- `acc₁ += W·E.f₁`
  rw [semXIR_seq, semXIR_seq]
  have m7 := mulF_sem (I := I) (s := s6) hM6 (d := fp) (a := fw) (b := fe) (by decide) (by decide)
    (by decide) (by decide)
  have f7 : ∀ i, 15 ≤ i → i ≠ fp → i ≠ fp + 1 → rd (semXIR I (mulF fp fw fe) s6).M i = rd s6.M i :=
    fun i h0 h1 h2 => fr_mulF h0 h1 h2
  have hM7 := inv_sem I (wf_mulF fp fw fe (by decide)) hM6
  generalize semXIR I (mulF fp fw fe) s6 = s7 at m7 f7 hM7
  have a8 := addF_sem (I := I) (s := s7) hM7 (d := fa1) (a := fa1) (b := fp) (by decide) (by decide)
    (by decide)
  have f8 : ∀ i, i ≠ fa1 → i ≠ fa1 + 1 → rd (semXIR I (addF fa1 fa1 fp) s7).M i = rd s7.M i :=
    fun i h1 h2 => fr_addF h1 h2
  have hM8 := inv_sem I (wf_addF fa1 fa1 fp (by decide)) hM7
  generalize semXIR I (addF fa1 fa1 fp) s7 = s8 at a8 f8 hM8
  have e8 : ∀ i, 15 ≤ i → i ≠ fw → i ≠ fw + 1 → i ≠ fe → i ≠ fe + 1 → i ≠ gA1 → i ≠ fp →
      i ≠ fp + 1 → i ≠ fa0 → i ≠ fa0 + 1 → i ≠ gK → i ≠ gT → i ≠ fa1 → i ≠ fa1 + 1 →
      rd s8.M i = rd s.M i := fun i h0 h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13 => by
    rw [f8 i h12 h13, f7 i h0 h6 h7, e6 i h0 h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11]
  have acc1 : rdF s8.M fa1 = rdF s.M fa1 + rdF s.M w * rdF s.M (e + 2) := by
    rw [a8, m7, hw6, he6, rdF_eq (f7 _ (by decide) (by decide) (by decide))
      (f7 _ (by decide) (by decide) (by decide)),
      rdF_eq (e6 _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
        (by decide) (by decide) (by decide) (by decide) (by decide) (by decide))
        (e6 _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
        (by decide) (by decide) (by decide) (by decide) (by decide) (by decide))]
  have acc0' : rdF s8.M fa0 = rdF s.M fa0 + rdF s.M w * rdF s.M e := by
    rw [← acc0]
    exact rdF_eq ((f8 _ (by decide) (by decide)).trans ((f7 _ (by decide) (by decide) (by decide)).trans
      ((y3 _ (by decide) (by decide) (by decide)).trans (t2 _ (by decide) (by decide)))))
      ((f8 _ (by decide) (by decide)).trans ((f7 _ (by decide) (by decide) (by decide)).trans
      ((y3 _ (by decide) (by decide) (by decide)).trans (t2 _ (by decide) (by decide)))))
  -- the pointers
  obtain ⟨p1, p2, p3, hM9⟩ := stepPs_sem I s8 hM8 (w := w) (e := e)
    ((e8 _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans hW)
    ((e8 _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans hE)
  refine ⟨?_, ?_, p1, p2, fun i hi => ?_, hM9⟩
  · rw [← acc0']
    exact rdF_eq (p3 _ (by decide) (by decide) (by decide)) (p3 _ (by decide) (by decide) (by decide))
  · rw [← acc1]
    exact rdF_eq (p3 _ (by decide) (by decide) (by decide)) (p3 _ (by decide) (by decide) (by decide))
  · have hne : 15 ≤ i ∧ i ≠ fw ∧ i ≠ fw + 1 ∧ i ≠ fe ∧ i ≠ fe + 1 ∧ i ≠ gA1 ∧ i ≠ fp ∧
        i ≠ fp + 1 ∧ i ≠ fa0 ∧ i ≠ fa0 + 1 ∧ i ≠ gK ∧ i ≠ gT ∧ i ≠ fa1 ∧ i ≠ fa1 + 1 ∧
        i ≠ gW ∧ i ≠ gE := by
      rcases hi with hi | rfl | rfl | rfl | rfl | rfl
      · simp only [regs, fw, fe, gA1, fp, fa0, gK, gT, fa1, gW, gE] at *; omega
      all_goals decide
    obtain ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15⟩ := hne
    rw [p3 i h10 h14 h15, e8 i h0 h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13]

/-! ## One position and the flag program -/

/-- `acc₀ := 0`, `acc₁ := 0`, `gE := eb`, the row count. -/
def zPs (R eb : ℕ) : List Prim :=
  [.const fa0 0, .const (fa0 + 1) 0, .const fa1 0, .const (fa1 + 1) 0, .const gE (toWord eb),
   .const gN2 (toWord R)]

/-- `gZ := [acc₀ ≠ fe]` as a word (`0` iff equal). -/
def cmpPs : List Prim :=
  [.op .xor fp fa0 fe, .op .xor (fp + 1) (fa0 + 1) (fe + 1), .op .or gZ fp (fp + 1)]

/-- `gZ := [gZ = 0 ∧ acc₁ = fe]`. -/
def cmpPs2 : List Prim :=
  [.op .xor fp fa1 fe, .op .xor (fp + 1) (fa1 + 1) (fe + 1), .op .or gZ2 fp (fp + 1),
   .op .or gZ gZ gZ2, .const gK 0, .op .eq gZ gZ gK]

/-- **One position** `j` (in `gJ`): the two folds over the `R` rows, the comparison with
`Enc₀[j]`, `Enc₁[j]`, the flag stored at `fb + j`; `j += 1`. -/
def fEnt (R cs cb eb xb yb fb : ℕ) : XIR :=
  .seq (.blk (zPs R eb)) (.seq (.blk (addrPs gW gJ cb cs)) (.seq (.loopK gC2 gN2 (toWord R) fBody)
    (.seq (.blk (addrPs gT gJ xb 2)) (.seq (ldF fe gT gA1) (.seq (.blk cmpPs)
      (.seq (.blk (addrPs gT gJ yb 2)) (.seq (ldF fe gT gA1) (.seq (.blk cmpPs2)
        (.seq (.blk (addrPs gT gJ fb 1)) (.seq (.store gT gZ) (.blk [.op .add gJ gJ cOne])))))))))))

/-- **The flags** `[fold(j) = Enc(j)]` at `fb + j` for the positions `j < n`. -/
def flagIR (n R cs cb eb xb yb fb : ℕ) : XIR :=
  .seq (.blk [.const gJ 0, .const gN1 (toWord n)])
    (.loopK gC1 gN1 (toWord n) (fEnt R cs cb eb xb yb fb))

/-! ## Well formed, no tape loop, no output, cost -/

theorem nw_fBody {r : ℕ} (hr : r = gJ ∨ r = gC1 ∨ r = gN1 ∨ r = gC2 ∨ r = gN2) :
    ¬ Writes fBody r := by
  have hr' : 15 ≤ r ∧ r ≠ fp ∧ r ≠ fp + 1 ∧ r ≠ fa0 ∧ r ≠ fa0 + 1 ∧ r ≠ fa1 ∧ r ≠ fa1 + 1 := by
    rcases hr with rfl | rfl | rfl | rfl | rfl <;> decide
  have n1 := nw_mulF (a := fw) (b := fe) hr'.1 hr'.2.1 hr'.2.2.1
  simp only [fBody, ldF, tPs, stepPs, addF, addFC, Writes, Prim.dst, List.mem_cons,
    List.mem_nil_iff, n1]
  rcases hr with rfl | rfl | rfl | rfl | rfl <;>
    simp [fw, fe, fp, fa0, fa1, gW, gE, gA1, gT, gK, gJ, gC1, gN1, gC2, gN2]

theorem wf_fBody : WF fBody := by
  have m1 := wf_mulF fp fw fe (by decide)
  simp only [fBody, ldF, tPs, stepPs, addF, addFC, WF, Prim.dst, List.mem_cons,
    List.mem_nil_iff, m1]
  simp [fw, fe, fp, fa0, fa1, gW, gE, gA1, gT, gK]

theorem wf_fEnt (R cs cb eb xb yb fb : ℕ) : WF (fEnt R cs cb eb xb yb fb) := by
  have n1 := nw_fBody (r := gC2) (by simp)
  simp only [fEnt, zPs, cmpPs, cmpPs2, addrPs, ldF, WF, Writes, Prim.dst, List.mem_cons,
    List.mem_nil_iff, wf_fBody, n1]
  simp [fa0, fa1, fe, fp, gW, gE, gA1, gT, gK, gJ, gZ, gZ2, gC2, gN2, bK, cTmp, regs]

theorem nw_fEnt {r : ℕ} (hr : r = gC1 ∨ r = gN1) (R cs cb eb xb yb fb : ℕ) :
    ¬ Writes (fEnt R cs cb eb xb yb fb) r := by
  have n1 := nw_fBody (r := r) (by rcases hr with rfl | rfl <;> simp)
  simp only [fEnt, zPs, cmpPs, cmpPs2, addrPs, ldF, Writes, Prim.dst, List.mem_cons,
    List.mem_nil_iff, n1]
  rcases hr with rfl | rfl <;>
    simp [fa0, fa1, fe, fp, gW, gE, gA1, gT, gK, gJ, gZ, gZ2, gC1, gN1, gC2, gN2, bK, cTmp]

theorem wf_flagIR (n R cs cb eb xb yb fb : ℕ) : WF (flagIR n R cs cb eb xb yb fb) := by
  have n1 := nw_fEnt (r := gC1) (by simp) R cs cb eb xb yb fb
  simp only [flagIR, WF, Prim.dst, List.mem_cons, List.mem_nil_iff, wf_fEnt, n1]
  simp [gJ, gC1, gN1, cTmp, regs]

theorem noLoopT_flagIR (n R cs cb eb xb yb fb : ℕ) : NoLoopT (flagIR n R cs cb eb xb yb fb) := by
  simp [flagIR, fEnt, fBody, ldF, mulF, addF, NoLoopT]

theorem outs_flagIR (n R cs cb eb xb yb fb t : ℕ) : outs (flagIR n R cs cb eb xb yb fb) t = 0 := by
  simp [flagIR, fEnt, fBody, ldF, mulF, addF, outs]

theorem cost_flagIR (n R cs cb eb xb yb fb t : ℕ) (hn : n < 2 ^ 64) (hR : R < 2 ^ 64) :
    cost (flagIR n R cs cb eb xb yb fb) t = 12 + n * (92 + 156 * R) := by
  have a1 : (toWord n).toNat = n := toNat_toWord hn
  have a2 : (toWord R).toNat = R := toNat_toWord hR
  simp only [flagIR, fEnt, zPs, cmpPs, cmpPs2, addrPs, fBody, tPs, stepPs, ldF, mulF, addF,
    cost, blkSteps, len_mulFC, len_addFC, List.length_cons, List.length_nil, a1, a2]
  norm_num
  ring

/-! ## The comparison on words -/

theorem xor_eq_zero_w (a b : Word) : XOp.xor.eval a b = 0 ↔ a = b := by
  simp only [XOp.eval]
  constructor
  · intro h
    have := congrArg (· ^^^ b) h
    simpa [BitVec.xor_assoc] using this
  · rintro rfl; exact BitVec.xor_self

theorem wB_inj {a b : Word} : wB a = wB b ↔ a = b :=
  ⟨fun h => by simp only [wB, B64.mk.injEq] at h; exact congrArg UInt64.toBitVec h,
   fun h => h ▸ rfl⟩

/-- **The flag word**: the zero test of the four word differences is `[a = e ∧ b = f]` in `F`. -/
theorem cmp_word (a0 a1 e0 e1 b0 b1 f0 f1 : Word) :
    XOp.eq.eval (XOp.or.eval (XOp.or.eval (XOp.xor.eval a0 e0) (XOp.xor.eval a1 e1))
      (XOp.or.eval (XOp.xor.eval b0 f0) (XOp.xor.eval b1 f1))) 0 =
    bW (decide ((⟨wB a0, wB a1⟩ : F) = ⟨wB e0, wB e1⟩ ∧ (⟨wB b0, wB b1⟩ : F) = ⟨wB f0, wB f1⟩)) := by
  rw [eq_bW]
  congr 1
  apply decide_eq_decide.mpr
  simp only [or_eq_zero_w, xor_eq_zero_w, F.mk.injEq, wB_inj]

/-! ## Block lemmas of one position -/

theorem zPs_sem (I : Array Word) (s : St) (hM : Inv s.M) (R eb : ℕ) :
    rdF (semXIR I (.blk (zPs R eb)) s).M fa0 = 0 ∧ rdF (semXIR I (.blk (zPs R eb)) s).M fa1 = 0 ∧
    rd (semXIR I (.blk (zPs R eb)) s).M gE = toWord eb ∧
    rd (semXIR I (.blk (zPs R eb)) s).M gN2 = toWord R ∧
    (∀ i, i ≠ fa0 → i ≠ fa0 + 1 → i ≠ fa1 → i ≠ fa1 + 1 → i ≠ gE → i ≠ gN2 →
      rd (semXIR I (.blk (zPs R eb)) s).M i = rd s.M i) ∧
    Inv (semXIR I (.blk (zPs R eb)) s).M := by
  have hs := hM.1
  simp only [regs] at hs
  have e0 : semXIR I (.blk (zPs R eb)) s = ⟨runPrims (zPs R eb) s.M, s.o⟩ := rfl
  simp only [e0]
  refine ⟨?_, ?_, ?_, ?_, fun i h1 h2 h3 h4 h5 h6 => rd_runPrims_of_not_writes (by
    intro p hp
    simp only [zPs, List.mem_cons, List.mem_nil_iff, or_false] at hp
    rcases hp with rfl | rfl | rfl | rfl | rfl | rfl <;> simp only [Prim.dst] <;>
      first | exact Ne.symm h1 | exact Ne.symm h2 | exact Ne.symm h3 | exact Ne.symm h4 |
        exact Ne.symm h5 | exact Ne.symm h6) _,
    inv_runPrims (by simp [zPs, Prim.dst, fa0, fa1, gE, gN2]) hM⟩
  · simp only [rdF, rdB, zPs, runPrims, List.foldl, Prim.run]
    simp (disch := first | decide | (simp only [size_set, fa0, fa1, gE, gN2]; omega)) only
      [rd_set_self, rd_set_ne]
    rfl
  · simp only [rdF, rdB, zPs, runPrims, List.foldl, Prim.run]
    simp (disch := first | decide | (simp only [size_set, fa0, fa1, gE, gN2]; omega)) only
      [rd_set_self, rd_set_ne]
    rfl
  all_goals simp only [zPs, runPrims, List.foldl, Prim.run]
  all_goals simp (disch := first | decide | (simp only [size_set, fa0, fa1, gE, gN2]; omega)) only
      [rd_set_self, rd_set_ne]

theorem cmpPs_sem (M : Mem) (hM : Inv M) :
    rd (runPrims cmpPs M) gZ = XOp.or.eval (XOp.xor.eval (rd M fa0) (rd M fe))
      (XOp.xor.eval (rd M (fa0 + 1)) (rd M (fe + 1))) ∧
    (∀ i, i ≠ fp → i ≠ fp + 1 → i ≠ gZ → rd (runPrims cmpPs M) i = rd M i) ∧
    Inv (runPrims cmpPs M) := by
  have hs := hM.1
  simp only [regs] at hs
  refine ⟨?_, fun i h1 h2 h3 => rd_runPrims_of_not_writes (by
    intro p hp
    simp only [cmpPs, List.mem_cons, List.mem_nil_iff, or_false] at hp
    rcases hp with rfl | rfl | rfl <;> simp only [Prim.dst] <;>
      first | exact Ne.symm h1 | exact Ne.symm h2 | exact Ne.symm h3) _,
    inv_runPrims (by simp [cmpPs, Prim.dst, fp, gZ]) hM⟩
  simp only [cmpPs, runPrims, List.foldl, Prim.run]
  simp (disch := first | decide | (simp only [size_set, fp, gZ]; omega)) only
    [rd_set_self, rd_set_ne]

theorem cmpPs2_sem (M : Mem) (hM : Inv M) :
    rd (runPrims cmpPs2 M) gZ = XOp.eq.eval (XOp.or.eval (rd M gZ)
      (XOp.or.eval (XOp.xor.eval (rd M fa1) (rd M fe))
        (XOp.xor.eval (rd M (fa1 + 1)) (rd M (fe + 1))))) 0 ∧
    (∀ i, i ≠ fp → i ≠ fp + 1 → i ≠ gZ2 → i ≠ gZ → i ≠ gK → rd (runPrims cmpPs2 M) i = rd M i) ∧
    Inv (runPrims cmpPs2 M) := by
  have hs := hM.1
  simp only [regs] at hs
  refine ⟨?_, fun i h1 h2 h3 h4 h5 => rd_runPrims_of_not_writes (by
    intro p hp
    simp only [cmpPs2, List.mem_cons, List.mem_nil_iff, or_false] at hp
    rcases hp with rfl | rfl | rfl | rfl | rfl | rfl <;> simp only [Prim.dst] <;>
      first | exact Ne.symm h1 | exact Ne.symm h2 | exact Ne.symm h3 | exact Ne.symm h4 |
        exact Ne.symm h5) _,
    inv_runPrims (by simp [cmpPs2, Prim.dst, fp, gZ, gZ2, gK]) hM⟩
  simp only [cmpPs2, runPrims, List.foldl, Prim.run]
  simp (disch := first | decide | (simp only [size_set, fp, gZ, gZ2, gK]; omega)) only
    [rd_set_self, rd_set_ne]

/-! ## One position -/

/-- The cells the tail of a position keeps: the heap but the flag, the position and loop
registers, the accumulators. -/
def TK (fb j i : ℕ) : Prop :=
  (regs ≤ i ∧ i ≠ fb + j) ∨ i = gJ ∨ i = gC1 ∨ i = gN1 ∨ i = fa0 ∨ i = fa0 + 1 ∨ i = fa1 ∨
    i = fa1 + 1

theorem TK_ne {fb j i : ℕ} (h : TK fb j i) :
    i ≠ gT ∧ i ≠ bK ∧ i ≠ fe ∧ i ≠ fe + 1 ∧ i ≠ gA1 ∧ i ≠ fp ∧ i ≠ fp + 1 ∧ i ≠ gZ ∧ i ≠ gZ2 ∧
      i ≠ gK ∧ i ≠ cTmp ∧ 15 ≤ i := by
  rcases h with ⟨h, -⟩ | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · simp only [regs, gT, bK, fe, gA1, fp, gZ, gZ2, gK, cTmp] at *; omega
  all_goals decide

/-- **One position**: with `j` in `gJ`, `fEnt` stores at `fb + j` the flag
`[Σ_r W[r]·E[r].f₀ = X[j] ∧ Σ_r W[r]·E[r].f₁ = Y[j]]`, `W[r]` at `cb + cs·j + 2r`, `E[r]` at
`eb + 4r` (K), `X[j]`, `Y[j]` at `xb + 2j`, `yb + 2j`; `j += 1`; the heap but the flag and the
position loop's registers are kept. -/
theorem fEnt_sem (I : Array Word) (s : St) (hM : Inv s.M) {R cs cb eb xb yb fb j : ℕ}
    (hR : R < 2 ^ 64) (hJ : rd s.M gJ = toWord j)
    (hcb : regs ≤ cb) (hcb2 : cb + cs * j + 2 * R + 2 < 2 ^ 64)
    (heb : regs ≤ eb) (heb2 : eb + 4 * R + 4 < 2 ^ 64)
    (hxb : regs ≤ xb) (hxb2 : xb + 2 * j + 2 < 2 ^ 64)
    (hyb : regs ≤ yb) (hyb2 : yb + 2 * j + 2 < 2 ^ 64)
    (hfb : regs ≤ fb) (hfb2 : fb + j < 2 ^ 64) (hfs : fb + j < s.M.size) :
    rd (semXIR I (fEnt R cs cb eb xb yb fb) s).M (fb + j) =
      bW (decide (∑ r ∈ range R, rdF s.M (cb + cs * j + 2 * r) * rdF s.M (eb + 4 * r) =
          rdF s.M (xb + 2 * j) ∧
        ∑ r ∈ range R, rdF s.M (cb + cs * j + 2 * r) * rdF s.M (eb + 4 * r + 2) =
          rdF s.M (yb + 2 * j))) ∧
    rd (semXIR I (fEnt R cs cb eb xb yb fb) s).M gJ = toWord (j + 1) ∧
    (∀ i, (regs ≤ i ∧ i ≠ fb + j) ∨ i = gC1 ∨ i = gN1 →
      rd (semXIR I (fEnt R cs cb eb xb yb fb) s).M i = rd s.M i) ∧
    Inv (semXIR I (fEnt R cs cb eb xb yb fb) s).M := by
  have hs := hM.1
  simp only [regs] at hs hcb heb hxb hyb hfb
  -- the accumulators
  rw [fEnt, semXIR_seq]
  obtain ⟨z1, z2, z3, z4, z5, hM1⟩ := zPs_sem I s hM R eb
  have sz1 := size_sem I (.blk (zPs R eb)) s
  generalize semXIR I (.blk (zPs R eb)) s = s1 at z1 z2 z3 z4 z5 hM1 sz1
  have k1 : ∀ i, (regs ≤ i ∨ i = gJ ∨ i = gC1 ∨ i = gN1) → rd s1.M i = rd s.M i := by
    intro i hi
    have : i ≠ fa0 ∧ i ≠ fa0 + 1 ∧ i ≠ fa1 ∧ i ≠ fa1 + 1 ∧ i ≠ gE ∧ i ≠ gN2 := by
      rcases hi with hi | rfl | rfl | rfl
      · simp only [regs, fa0, fa1, gE, gN2] at *; omega
      all_goals decide
    exact z5 i this.1 this.2.1 this.2.2.1 this.2.2.2.1 this.2.2.2.2.1 this.2.2.2.2.2
  -- the row pointer
  rw [semXIR_seq]
  have e2 : semXIR I (.blk (addrPs gW gJ cb cs)) s1 =
      ⟨runPrims (addrPs gW gJ cb cs) s1.M, s1.o⟩ := rfl
  obtain ⟨w1, w2⟩ := addrPs_sem s1.M hM1.1 (d := gW) (i := gJ) (b := cb) (m := cs) (x := j)
    (by decide) (by decide) (by decide) ((k1 _ (.inr (.inl rfl))).trans hJ)
  have hM2 : Inv (runPrims (addrPs gW gJ cb cs) s1.M) :=
    inv_runPrims (by simp [addrPs, Prim.dst, gW, bK]) hM1
  have sz2 : (runPrims (addrPs gW gJ cb cs) s1.M).size = s1.M.size := size_runPrims _ _
  rw [e2, semXIR_seq]
  generalize runPrims (addrPs gW gJ cb cs) s1.M = M2 at w1 w2 hM2 sz2
  -- the row loop
  let Q : ℕ → St → Prop := fun r s' => Inv s'.M ∧ s'.M.size = s.M.size ∧
    rdF s'.M fa0 = ∑ t ∈ range r, rdF s.M (cb + cs * j + 2 * t) * rdF s.M (eb + 4 * t) ∧
    rdF s'.M fa1 = ∑ t ∈ range r, rdF s.M (cb + cs * j + 2 * t) * rdF s.M (eb + 4 * t + 2) ∧
    rd s'.M gW = toWord (cb + cs * j + 2 * r) ∧ rd s'.M gE = toWord (eb + 4 * r) ∧
    ∀ i, (regs ≤ i ∨ i = gJ ∨ i = gC1 ∨ i = gN1) → rd s'.M i = rd s.M i
  have hE : ∀ i, i ≠ gC2 → i ≠ cTmp → rd (entryK gC2 gN2 (toWord R) M2) i = rd M2 i :=
    fun i h1 h2 => entryK_frame _ (Ne.symm h1) (Ne.symm h2)
  have q0 : Q 0 ⟨entryK gC2 gN2 (toWord R) M2, s1.o⟩ := by
    refine ⟨inv_entryK hM2 (by decide), by simp only [size_entryK, sz2, sz1], ?_, ?_, ?_, ?_,
      fun i hi => ?_⟩
    · dsimp only
      rw [sum_range_zero, ← z1]
      exact rdF_eq ((hE _ (by decide) (by decide)).trans (w2 _ (by decide) (by decide)))
        ((hE _ (by decide) (by decide)).trans (w2 _ (by decide) (by decide)))
    · dsimp only
      rw [sum_range_zero, ← z2]
      exact rdF_eq ((hE _ (by decide) (by decide)).trans (w2 _ (by decide) (by decide)))
        ((hE _ (by decide) (by decide)).trans (w2 _ (by decide) (by decide)))
    · dsimp only; rw [hE _ (by decide) (by decide), w1, Nat.mul_zero, Nat.add_zero]
    · dsimp only
      rw [hE _ (by decide) (by decide), w2 _ (by decide) (by decide), z3, Nat.mul_zero,
        Nat.add_zero]
    · dsimp only
      have : i ≠ gC2 ∧ i ≠ cTmp ∧ i ≠ gW ∧ i ≠ bK := by
        rcases hi with hi | rfl | rfl | rfl
        · simp only [regs, gC2, cTmp, gW, bK] at *; omega
        all_goals decide
      rw [hE _ this.1 this.2.1, w2 _ this.2.2.1 this.2.2.2, k1 i hi]
  have qstep : ∀ r s', r < R → Q r s' → Q (r + 1) (decS gC2 (semXIR I fBody s')) := by
    rintro r s' hr ⟨i1, i2, i3, i4, i5, i6, i7⟩
    obtain ⟨b1, b2, b3, b4, b5, hMb⟩ := fBody_sem I s' i1 (w := cb + cs * j + 2 * r)
      (e := eb + 4 * r) (by simp only [regs]; omega) (by omega) (by simp only [regs]; omega)
      (by omega) i5 i6
    have hd : ∀ i, i ≠ gC2 → rd (decS gC2 (semXIR I fBody s')).M i =
        rd (semXIR I fBody s').M i := fun i h => rd_decS (Ne.symm h) _
    have hW : rdF s'.M (cb + cs * j + 2 * r) = rdF s.M (cb + cs * j + 2 * r) :=
      rdF_eq (i7 _ (.inl (by simp only [regs]; omega))) (i7 _ (.inl (by simp only [regs]; omega)))
    refine ⟨inv_decS hMb (by decide), by rw [size_decS, size_sem, i2], ?_, ?_, ?_, ?_,
      fun i hi => ?_⟩
    · rw [rdF_eq (hd _ (by decide)) (hd _ (by decide)), b1, i3, sum_range_succ, hW,
        rdF_eq (i7 _ (.inl (by simp only [regs]; omega))) (i7 _ (.inl (by simp only [regs]; omega)))]
    · rw [rdF_eq (hd _ (by decide)) (hd _ (by decide)), b2, i4, sum_range_succ, hW,
        rdF_eq (i7 _ (.inl (by simp only [regs]; omega))) (i7 _ (.inl (by simp only [regs]; omega)))]
    · rw [hd _ (by decide), b3]; exact congrArg toWord (by ring)
    · rw [hd _ (by decide), b4]; exact congrArg toWord (by ring)
    · have : i ≠ gC2 := by
        rcases hi with hi | rfl | rfl | rfl
        · simp only [regs, gC2] at *; omega
        all_goals decide
      rw [hd _ this, b5 i (hi.imp_right fun h => h.imp_right fun h => h.imp_right Or.inl),
        i7 i hi]
  have hN2 : rd M2 gN2 = toWord R := (w2 _ (by decide) (by decide)).trans z4
  have hq := loopK_run I fBody Q ⟨M2, s1.o⟩ hM2 (by decide) (by decide) (by decide) hN2 hR q0 qstep
  generalize semXIR I (.loopK gC2 gN2 (toWord R) fBody) ⟨M2, s1.o⟩ = s3 at hq
  obtain ⟨j1, j2, j3, j4, -, -, j7⟩ := hq
  have hJ3 : rd s3.M gJ = toWord j := (j7 _ (.inr (.inl rfl))).trans hJ
  have hs3 := j1.1
  simp only [regs] at hs3
  -- `X[j]`
  rw [semXIR_seq]
  have e4 : semXIR I (.blk (addrPs gT gJ xb 2)) s3 = ⟨runPrims (addrPs gT gJ xb 2) s3.M, s3.o⟩ :=
    rfl
  obtain ⟨x1, x2⟩ := addrPs_sem s3.M j1.1 (d := gT) (i := gJ) (b := xb) (m := 2) (x := j)
    (by decide) (by decide) (by decide) hJ3
  have hM4 : Inv (runPrims (addrPs gT gJ xb 2) s3.M) :=
    inv_runPrims (by simp [addrPs, Prim.dst, gT, bK]) j1
  have sz4 : (runPrims (addrPs gT gJ xb 2) s3.M).size = s.M.size := by rw [size_runPrims, j2]
  rw [e4, semXIR_seq]
  generalize runPrims (addrPs gT gJ xb 2) s3.M = M4 at x1 x2 hM4 sz4
  obtain ⟨l1, -, l3⟩ := ldF_sem I ⟨M4, s3.o⟩ hM4 (d := fe) (p := gT) (p1 := gA1) (x := xb + 2 * j)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) x1
    (by simp only [regs]; omega) (by omega)
  have hM5 := inv_sem I (P := ldF fe gT gA1) (s := ⟨M4, s3.o⟩)
    (by simp +decide only [ldF, WF, Prim.dst, fe, gA1, and_true]) hM4
  have sz5 : (semXIR I (ldF fe gT gA1) ⟨M4, s3.o⟩).M.size = s.M.size := by rw [size_sem]; exact sz4
  generalize semXIR I (ldF fe gT gA1) ⟨M4, s3.o⟩ = s5 at l1 l3 hM5 sz5
  have hX5 : rdF s5.M fe = rdF s.M (xb + 2 * j) := by
    rw [l1]
    exact rdF_eq ((x2 _ (by simp only [gT]; omega) (by simp only [bK]; omega)).trans
        (j7 _ (.inl (by simp only [regs]; omega))))
      ((x2 _ (by simp only [gT]; omega) (by simp only [bK]; omega)).trans
        (j7 _ (.inl (by simp only [regs]; omega))))
  have f5 : ∀ i, TK fb j i → rd s5.M i = rd s3.M i := fun i hi => by
    obtain ⟨n1, n2, n3, n4, n5, -⟩ := TK_ne hi
    rw [l3 i n3 n4 n5, x2 i n1 n2]
  -- the first comparison
  rw [semXIR_seq]
  have e6 : semXIR I (.blk cmpPs) s5 = ⟨runPrims cmpPs s5.M, s5.o⟩ := rfl
  obtain ⟨c1, c2, hM6⟩ := cmpPs_sem s5.M hM5
  have sz6 : (runPrims cmpPs s5.M).size = s.M.size := by rw [size_runPrims, sz5]
  rw [e6, semXIR_seq]
  generalize runPrims cmpPs s5.M = M6 at c1 c2 hM6 sz6
  have f6 : ∀ i, TK fb j i → rd M6 i = rd s3.M i := fun i hi => by
    obtain ⟨-, -, -, -, -, n6, n7, n8, -⟩ := TK_ne hi
    rw [c2 i n6 n7 n8, f5 i hi]
  -- `Y[j]`
  have hJ6 : rd M6 gJ = toWord j := (f6 _ (.inr (.inl rfl))).trans hJ3
  have e7 : semXIR I (.blk (addrPs gT gJ yb 2)) ⟨M6, s5.o⟩ =
      ⟨runPrims (addrPs gT gJ yb 2) M6, s5.o⟩ := rfl
  obtain ⟨y1, y2⟩ := addrPs_sem M6 hM6.1 (d := gT) (i := gJ) (b := yb) (m := 2) (x := j)
    (by decide) (by decide) (by decide) hJ6
  have hM7 : Inv (runPrims (addrPs gT gJ yb 2) M6) :=
    inv_runPrims (by simp [addrPs, Prim.dst, gT, bK]) hM6
  have sz7 : (runPrims (addrPs gT gJ yb 2) M6).size = s.M.size := by rw [size_runPrims, sz6]
  rw [e7, semXIR_seq]
  generalize runPrims (addrPs gT gJ yb 2) M6 = M7 at y1 y2 hM7 sz7
  obtain ⟨m1, -, m3⟩ := ldF_sem I ⟨M7, s5.o⟩ hM7 (d := fe) (p := gT) (p1 := gA1) (x := yb + 2 * j)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) y1
    (by simp only [regs]; omega) (by omega)
  have hM8 := inv_sem I (P := ldF fe gT gA1) (s := ⟨M7, s5.o⟩)
    (by simp +decide only [ldF, WF, Prim.dst, fe, gA1, and_true]) hM7
  have sz8 : (semXIR I (ldF fe gT gA1) ⟨M7, s5.o⟩).M.size = s.M.size := by rw [size_sem]; exact sz7
  generalize semXIR I (ldF fe gT gA1) ⟨M7, s5.o⟩ = s8 at m1 m3 hM8 sz8
  have hY8 : rdF s8.M fe = rdF s.M (yb + 2 * j) := by
    have h7 : ∀ i, regs ≤ i → rd M7 i = rd s.M i := fun i hi => by
      have hT : TK fb j i ∨ i = fb + j := by
        by_cases h : i = fb + j
        · exact .inr h
        · exact .inl (.inl ⟨hi, h⟩)
      simp only [regs] at hi
      rw [y2 i (by simp only [gT]; omega) (by simp only [bK]; omega)]
      rcases hT with hT | rfl
      · rw [f6 i hT]; exact j7 _ (.inl (by simp only [regs]; omega))
      · rw [c2 _ (by simp only [fp]; omega) (by simp only [fp]; omega) (by simp only [gZ]; omega),
          l3 _ (by simp only [fe]; omega) (by simp only [fe]; omega) (by simp only [gA1]; omega),
          x2 _ (by simp only [gT]; omega) (by simp only [bK]; omega)]
        exact j7 _ (.inl (by simp only [regs]; omega))
    rw [m1]
    exact rdF_eq (h7 _ (by simp only [regs]; omega)) (h7 _ (by simp only [regs]; omega))
  have f8 : ∀ i, TK fb j i → rd s8.M i = rd s3.M i := fun i hi => by
    obtain ⟨n1, n2, n3, n4, n5, -⟩ := TK_ne hi
    rw [m3 i n3 n4 n5, y2 i n1 n2, f6 i hi]
  have gz8 : rd s8.M gZ = rd M6 gZ := by
    rw [m3 _ (by decide) (by decide) (by decide), y2 _ (by decide) (by decide)]
  -- the second comparison
  rw [semXIR_seq]
  have e9 : semXIR I (.blk cmpPs2) s8 = ⟨runPrims cmpPs2 s8.M, s8.o⟩ := rfl
  obtain ⟨d1, d2, hM9⟩ := cmpPs2_sem s8.M hM8
  have sz9 : (runPrims cmpPs2 s8.M).size = s.M.size := by rw [size_runPrims, sz8]
  rw [e9, semXIR_seq]
  generalize runPrims cmpPs2 s8.M = M9 at d1 d2 hM9 sz9
  have hZ : rd M9 gZ = bW (decide
      (∑ r ∈ range R, rdF s.M (cb + cs * j + 2 * r) * rdF s.M (eb + 4 * r) = rdF s.M (xb + 2 * j) ∧
       ∑ r ∈ range R, rdF s.M (cb + cs * j + 2 * r) * rdF s.M (eb + 4 * r + 2) =
        rdF s.M (yb + 2 * j))) := by
    rw [d1, gz8, c1, cmp_word, ← j3, ← j4, ← hX5, ← hY8]
    have a0 : rd s5.M fa0 = rd s3.M fa0 := f5 _ (.inr (.inr (.inr (.inr (.inl rfl)))))
    have a1 : rd s5.M (fa0 + 1) = rd s3.M (fa0 + 1) :=
      f5 _ (.inr (.inr (.inr (.inr (.inr (.inl rfl))))))
    have b0 : rd s8.M fa1 = rd s3.M fa1 := f8 _ (.inr (.inr (.inr (.inr (.inr (.inr (.inl rfl)))))))
    have b1 : rd s8.M (fa1 + 1) = rd s3.M (fa1 + 1) :=
      f8 _ (.inr (.inr (.inr (.inr (.inr (.inr (.inr rfl)))))))
    simp only [rdF, rdB, a0, a1, b0, b1]
    congr 1
  have f9 : ∀ i, TK fb j i → rd M9 i = rd s3.M i := fun i hi => by
    obtain ⟨-, -, -, -, -, n6, n7, n8, n9, n10, -⟩ := TK_ne hi
    rw [d2 i n6 n7 n9 n8 n10, f8 i hi]
  -- the flag
  have hJ9 : rd M9 gJ = toWord j := (f9 _ (.inr (.inl rfl))).trans hJ3
  have e10 : semXIR I (.blk (addrPs gT gJ fb 1)) ⟨M9, s8.o⟩ =
      ⟨runPrims (addrPs gT gJ fb 1) M9, s8.o⟩ := rfl
  obtain ⟨g1, g2⟩ := addrPs_sem M9 hM9.1 (d := gT) (i := gJ) (b := fb) (m := 1) (x := j)
    (by decide) (by decide) (by decide) hJ9
  have hM10 : Inv (runPrims (addrPs gT gJ fb 1) M9) :=
    inv_runPrims (by simp [addrPs, Prim.dst, gT, bK]) hM9
  have sz10 : (runPrims (addrPs gT gJ fb 1) M9).size = s.M.size := by rw [size_runPrims, sz9]
  rw [e10, semXIR_seq]
  generalize runPrims (addrPs gT gJ fb 1) M9 = M10 at g1 g2 hM10 sz10
  rw [Nat.one_mul] at g1
  have st : ∀ i, i ≠ cTmp → rd (storeM M10 gT gZ) i = if i = fb + j then rd M10 gZ else rd M10 i :=
    fun i hi => rd_storeM hM10 g1 (by simp only [regs]; omega) hfb2 (by omega) (by decide)
      (by decide) hi
  have hM11 : Inv (storeM M10 gT gZ) := inv_of_frame hM10 (size_storeM ..) fun i hi => by
    rw [st i (by simp only [cTmp]; omega), if_neg (by omega)]
  have e11 : semXIR I (.store gT gZ) ⟨M10, s8.o⟩ = ⟨storeM M10 gT gZ, s8.o⟩ := rfl
  have hJ11 : rd (storeM M10 gT gZ) gJ = toWord j := by
    rw [st _ (by decide), if_neg (by simp only [gJ]; omega), g2 _ (by decide) (by decide), hJ9]
  rw [e11]
  have e12 : semXIR I (.blk [.op .add gJ gJ cOne]) ⟨storeM M10 gT gZ, s8.o⟩ =
      ⟨runPrims [.op .add gJ gJ cOne] (storeM M10 gT gZ), s8.o⟩ := rfl
  rw [e12]
  obtain ⟨n1, n2⟩ := incr_sem _ hM11 (r := gJ) (by decide) (by decide) hJ11
  refine ⟨?_, n1, fun i hi => ?_, inv_runPrims (by simp [Prim.dst, gJ]) hM11⟩
  · rw [n2 _ (by simp only [gJ]; omega), st _ (by simp only [cTmp]; omega), if_pos rfl,
      g2 _ (by decide) (by decide), hZ]
  · have hT : TK fb j i := by
      rcases hi with h | h | h
      · exact .inl h
      · exact .inr (.inr (.inl h))
      · exact .inr (.inr (.inr (.inl h)))
    obtain ⟨n1', n2', -, -, -, -, -, -, -, -, n11, -⟩ := TK_ne hT
    have hne : i ≠ gJ ∧ i ≠ fb + j := by
      rcases hi with ⟨h1, h2⟩ | rfl | rfl
      · simp only [regs, gJ] at *; omega
      · simp only [gC1, gJ]; omega
      · simp only [gN1, gJ]; omega
    rw [n2 _ hne.1, st _ n11, if_neg hne.2, g2 _ n1' n2', f9 i hT]
    refine j7 i ?_
    rcases hi with h | h | h
    · exact .inl h.1
    · exact .inr (.inr (.inl h))
    · exact .inr (.inr (.inr h))

/-! ## The flag program -/

/-- **The flag** of position `j` on the heap `M`: `[Σ_r W[r][j]·E[r].f₀ = X[j] ∧
Σ_r W[r][j]·E[r].f₁ = Y[j]]`, with `W[r][j]` at `cb + cs·j + 2r`, `E[r]` at `eb + 4r` (K: `f₀`
then `f₁`), `X[j]` at `xb + 2j`, `Y[j]` at `yb + 2j`. -/
def flagV (M : Mem) (R cs cb eb xb yb j : ℕ) : Word :=
  bW (decide (∑ r ∈ range R, rdF M (cb + cs * j + 2 * r) * rdF M (eb + 4 * r) = rdF M (xb + 2 * j) ∧
    ∑ r ∈ range R, rdF M (cb + cs * j + 2 * r) * rdF M (eb + 4 * r + 2) = rdF M (yb + 2 * j)))

/-- **The flags on the machine**: `flagIR n R cs cb eb xb yb fb` stores `flagV` of the initial
heap at `fb + j` for every `j < n`, and keeps the heap outside `[fb, fb + n)`. The rows of a
position fit its stride (`2R ≤ cs`); the inputs are disjoint from the flags. -/
theorem flagIR_sem (I : Array Word) (s : St) (hM : Inv s.M) {n R cs cb eb xb yb fb : ℕ}
    (hn : n < 2 ^ 64) (hR : R < 2 ^ 64) (hRc : 2 * R ≤ cs)
    (hcb : regs ≤ cb) (hcb2 : cb + cs * n + 2 < 2 ^ 64)
    (heb : regs ≤ eb) (heb2 : eb + 4 * R + 4 < 2 ^ 64)
    (hxb : regs ≤ xb) (hxb2 : xb + 2 * n + 2 < 2 ^ 64)
    (hyb : regs ≤ yb) (hyb2 : yb + 2 * n + 2 < 2 ^ 64)
    (hfb : regs ≤ fb) (hfb2 : fb + n < 2 ^ 64) (hfs : fb + n ≤ s.M.size)
    (hdW : cb + cs * n ≤ fb ∨ fb + n ≤ cb) (hdE : eb + 4 * R ≤ fb ∨ fb + n ≤ eb)
    (hdX : xb + 2 * n ≤ fb ∨ fb + n ≤ xb) (hdY : yb + 2 * n ≤ fb ∨ fb + n ≤ yb) :
    (∀ j < n, rd (semXIR I (flagIR n R cs cb eb xb yb fb) s).M (fb + j) =
      flagV s.M R cs cb eb xb yb j) ∧
    (∀ i, regs ≤ i → (i < fb ∨ fb + n ≤ i) →
      rd (semXIR I (flagIR n R cs cb eb xb yb fb) s).M i = rd s.M i) ∧
    Inv (semXIR I (flagIR n R cs cb eb xb yb fb) s).M := by
  have hs := hM.1
  simp only [regs] at hs hcb heb hxb hyb hfb
  have e0 : semXIR I (.blk [.const gJ 0, .const gN1 (toWord n)]) s =
      ⟨runPrims [.const gJ 0, .const gN1 (toWord n)] s.M, s.o⟩ := rfl
  obtain ⟨r1, r2, r3, hM0⟩ := pre2_sem s.M hM (r := gJ) (n := gN1) 0 (toWord n) (by decide)
    (by decide) (by decide) (by decide) (by decide)
  rw [flagIR, semXIR_seq, e0]
  generalize hM0e : runPrims [.const gJ 0, .const gN1 (toWord n)] s.M = M0 at r1 r2 r3 hM0
  have z0 : M0.size = s.M.size := by rw [← hM0e]; exact size_runPrims _ _
  let P : ℕ → St → Prop := fun j s' => Inv s'.M ∧ s'.M.size = s.M.size ∧ rd s'.M gJ = toWord j ∧
    (∀ x < j, rd s'.M (fb + x) = flagV s.M R cs cb eb xb yb x) ∧
    ∀ i, regs ≤ i → (i < fb ∨ fb + j ≤ i) → rd s'.M i = rd s.M i
  have hE : ∀ i, i ≠ gC1 → i ≠ cTmp → rd (entryK gC1 gN1 (toWord n) M0) i = rd M0 i :=
    fun i h1 h2 => entryK_frame _ (Ne.symm h1) (Ne.symm h2)
  have p0 : P 0 ⟨entryK gC1 gN1 (toWord n) M0, s.o⟩ := by
    refine ⟨inv_entryK hM0 (by decide), by simp only [size_entryK, z0], ?_,
      fun x hx => absurd hx (Nat.not_lt_zero _), fun i hi _ => ?_⟩
    · dsimp only; rw [hE _ (by decide) (by decide), r1, toWord_zero']
    · dsimp only
      rw [hE _ (by simp only [gC1, regs] at *; omega) (by simp only [cTmp, regs] at *; omega),
        r3 _ (by simp only [gJ, regs] at *; omega) (by simp only [gN1, regs] at *; omega)]
  have step : ∀ j s', j < n → P j s' →
      P (j + 1) (decS gC1 (semXIR I (fEnt R cs cb eb xb yb fb) s')) := by
    rintro j s' hj ⟨i1, i2, i3, i4, i5⟩
    have hcs : cs * j + 2 * R ≤ cs * n := by
      have := Nat.mul_le_mul_left cs (show j + 1 ≤ n by omega)
      rw [Nat.mul_succ] at this; omega
    have hR' : ∀ y, regs ≤ y → (y < fb ∨ fb + n ≤ y) → rd s'.M y = rd s.M y :=
      fun y h1 h2 => i5 y h1 (h2.imp_right fun h => by omega)
    obtain ⟨e1, e2, e3, e4⟩ := fEnt_sem I s' i1 (R := R) (cs := cs) (cb := cb) (eb := eb)
      (xb := xb) (yb := yb) (fb := fb) (j := j) hR i3 (by simp only [regs]; omega) (by omega)
      (by simp only [regs]; omega) (by omega) (by simp only [regs]; omega) (by omega)
      (by simp only [regs]; omega) (by omega) (by simp only [regs]; omega) (by omega)
      (by rw [i2]; omega)
    have hd : ∀ i, i ≠ gC1 → rd (decS gC1 (semXIR I (fEnt R cs cb eb xb yb fb) s')).M i =
        rd (semXIR I (fEnt R cs cb eb xb yb fb) s').M i := fun i h => rd_decS (Ne.symm h) _
    refine ⟨inv_decS e4 (by decide), by rw [size_decS, size_sem, i2], by rw [hd _ (by decide), e2],
      fun x hx => ?_, fun i hi hi2 => ?_⟩
    · rw [hd _ (by simp only [gC1]; omega)]
      rcases Nat.lt_succ_iff_lt_or_eq.mp hx with h | rfl
      · rw [← i4 x h]
        exact e3 _ (.inl ⟨by simp only [regs]; omega, by omega⟩)
      · have hW : ∀ r ∈ range R, rdF s'.M (cb + cs * x + 2 * r) = rdF s.M (cb + cs * x + 2 * r) :=
          fun r hr => by
            have := mem_range.1 hr
            exact rdF_eq (hR' _ (by simp only [regs]; omega) (by omega))
              (hR' _ (by simp only [regs]; omega) (by omega))
        have hE0 : ∀ r ∈ range R, rdF s'.M (eb + 4 * r) = rdF s.M (eb + 4 * r) := fun r hr => by
          have := mem_range.1 hr
          exact rdF_eq (hR' _ (by simp only [regs]; omega) (by omega))
            (hR' _ (by simp only [regs]; omega) (by omega))
        have hE1 : ∀ r ∈ range R, rdF s'.M (eb + 4 * r + 2) = rdF s.M (eb + 4 * r + 2) :=
          fun r hr => by
            have := mem_range.1 hr
            exact rdF_eq (hR' _ (by simp only [regs]; omega) (by omega))
              (hR' _ (by simp only [regs]; omega) (by omega))
        have s0 : ∑ r ∈ range R, rdF s'.M (cb + cs * x + 2 * r) * rdF s'.M (eb + 4 * r) =
            ∑ r ∈ range R, rdF s.M (cb + cs * x + 2 * r) * rdF s.M (eb + 4 * r) :=
          sum_congr rfl fun r hr => by rw [hW r hr, hE0 r hr]
        have s1 : ∑ r ∈ range R, rdF s'.M (cb + cs * x + 2 * r) * rdF s'.M (eb + 4 * r + 2) =
            ∑ r ∈ range R, rdF s.M (cb + cs * x + 2 * r) * rdF s.M (eb + 4 * r + 2) :=
          sum_congr rfl fun r hr => by rw [hW r hr, hE1 r hr]
        have hX : rdF s'.M (xb + 2 * x) = rdF s.M (xb + 2 * x) :=
          rdF_eq (hR' _ (by simp only [regs]; omega) (by omega))
            (hR' _ (by simp only [regs]; omega) (by omega))
        have hY : rdF s'.M (yb + 2 * x) = rdF s.M (yb + 2 * x) :=
          rdF_eq (hR' _ (by simp only [regs]; omega) (by omega))
            (hR' _ (by simp only [regs]; omega) (by omega))
        rw [e1, s0, s1, hX, hY]
        rfl
    · rw [hd _ (by simp only [gC1, regs] at *; omega),
        e3 _ (.inl ⟨hi, by omega⟩), i5 i hi (hi2.imp_right fun h => by omega)]
  have := loopK_run I (fEnt R cs cb eb xb yb fb) P ⟨M0, s.o⟩ hM0 (by decide) (by decide)
    (by decide) r2 hn p0 step
  exact ⟨this.2.2.2.1, fun i hi hi2 => this.2.2.2.2 i hi hi2, this.1⟩

/-! ## The flags are `A_c` -/

theorem bW_dec_ne_zero (p : Prop) [Decidable p] : bW (decide p) ≠ 0 ↔ p := by
  by_cases h : p <;> simp [bW, h]

open FR.Snd in
/-- **The flags mark `A_c`** (`mem_consSet_iff`): with level `i`'s word at `cb + cs·j + 2r`, the
`eq` table of P1.i's challenges at `eb`, and `Enc` of the next message's two coordinates at `xb`
and `yb`, the flag of position `j` is nonzero iff `j ∈ A_c`. -/
theorem flagV_consSet {M : Mem} {κ : Kind} {L es : Log} {i cs cb eb xb yb : ℕ}
    (hW : ∀ j (hj : j < 2 ^ (lvl κ i).logN) (r : Fin (lvl κ i).rows),
      rdF M (cb + cs * j + 2 * r) = wordOf κ L es i r ⟨j, hj⟩)
    (hE : ∀ r < (lvl κ i).rows, rdK M (eb + 4 * r) = eqBits (sAt es i) (lvl κ i).ell r)
    (hX : ∀ j < 2 ^ (lvl κ i).logN,
      rdF M (xb + 2 * j) = encF (mLog κ i) (fun x => (nextMsg κ L es i x).f₀) j)
    (hY : ∀ j < 2 ^ (lvl κ i).logN,
      rdF M (yb + 2 * j) = encF (mLog κ i) (fun x => (nextMsg κ L es i x).f₁) j) :
    ∀ j < 2 ^ (lvl κ i).logN,
      (j ∈ consN κ L es i ↔ flagV M (lvl κ i).rows cs cb eb xb yb j ≠ 0) := by
  intro j hj
  rw [flagV, bW_dec_ne_zero, mem_consN]
  have s0 : ∑ r ∈ range (lvl κ i).rows, rdF M (cb + cs * j + 2 * r) * rdF M (eb + 4 * r) =
      ∑ r : Fin (lvl κ i).rows, wordOf κ L es i r ⟨j, hj⟩ * (eqBits (sAt es i) (lvl κ i).ell r).f₀ := by
    rw [← Fin.sum_univ_eq_sum_range]
    refine sum_congr rfl fun r _ => ?_
    rw [hW j hj r, ← hE r r.2]
    rfl
  have s1 : ∑ r ∈ range (lvl κ i).rows, rdF M (cb + cs * j + 2 * r) * rdF M (eb + 4 * r + 2) =
      ∑ r : Fin (lvl κ i).rows, wordOf κ L es i r ⟨j, hj⟩ * (eqBits (sAt es i) (lvl κ i).ell r).f₁ := by
    rw [← Fin.sum_univ_eq_sum_range]
    refine sum_congr rfl fun r _ => ?_
    rw [hW j hj r, ← hE r r.2]
    rfl
  rw [s0, s1, hX j hj, hY j hj]
  constructor
  · rintro ⟨h, hm⟩; exact (mem_consSet_iff κ L es i _).1 hm
  · intro h; exact ⟨hj, (mem_consSet_iff κ L es i ⟨j, hj⟩).2 h⟩

end FR.X

end G6_FRXFlag

section G6_FRXReadLv

-- New for `flock-recursive` (BLUEPRINT §6.2 step 3, levels 1–4; stage S-H2, track L-ext).

/-!
# The ladder read of levels 1–4

`readIR` is parametric in the level (`FRXReadDefs`): the level byte of the node and column tags,
the tape word of the cap's entry 0, the store's base and the words a column. This module fixes
Flock's `P30` instances of levels 1–4 (BLUEPRINT §2.2, revision 3.13):

| level | `log₂ n` | cap | `sib` | cap field offset (π) |
|---|---|---|---|---|
| 1 | 16 | `2^8` | 8 | 35,968 |
| 2 | 14 | `2^8` | 6 | 44,160 |
| 3 | 12 | `2^8` | 4 | 52,352 |
| 4 | 10 | `2^7` | 3 | 60,544 |

(Revision 3.13 offsets.) A column of levels 1–4 is 304 bytes: 16 `F` elements (256 bytes) and 48 zero bytes (3.12's
padding). The read copies the first 32 words, the 16 `F` elements, to `stB + 32 p` (`stB = 2^24`:
the level-0 output rows' region, free until level 0's interpolation). The offsets are those
of `FRXChainFlock.fsMsgs` at the C phases (`capOffL_ctl`).

**`readLv_spec`**: after `readLv i`, cell `stB + 32 q + w` holds word `w` of the column that
`colL (frEnc i)` reads under π's cap entry `q / 2^sib` of level `i`.
-/

namespace FR.X

open RecursionFast FR.Merkle

/-- The byte offset of level `i`'s cap in π (`i ≤ 4`; level 0 is `capOff`). -/
def capOffL : ℕ → ℕ
  | 0 => 19584
  | 1 => 35968
  | 2 => 44160
  | 3 => 52352
  | _ => 60544

/-- `log₂` of level `i`'s cap. -/
def capLogL (i : ℕ) : ℕ := if i = 0 then 9 else if i = 4 then 7 else 8

/-- `log₂ nᵢ` (`P30`). -/
def logNL (i : ℕ) : ℕ := 18 - 2 * i

/-- The Merkle height under a cap entry (`P30`): `9, 8, 6, 4, 3`. -/
def sibL (i : ℕ) : ℕ := logNL i - capLogL i

/-- **Cap entry `e` of level `i`**: the 32 bytes at `capOffL i + 32 e` of π. -/
def capPiL (i : ℕ) (π : Proof) (e : ℕ) : Digest := bytesAt π (capOffL i + 32 * e) 32

/-- The tape word of cap entry 0 of level `i`. -/
def capWL (i : ℕ) : ℕ := 5 + capOffL i / 8

/-- The store base of levels 1–4. -/
def stB : ℕ := 16777216

/-- **The read of level `i`** (`1 ≤ i ≤ 4`): `2^(logNL i)` positions, 32 words each at `stB`. -/
def readLv (i : ℕ) : XIR := readIR i (capWL i) stB 32 (sibL i) (2 ^ logNL i)

/-- The offsets are the C phases' messages (`fsMsgs`, positions `capPos 1 … 4`) and level 0's. -/
theorem capOffL_ctl : (List.range 5).map capOffL = [19584, 35968, 44160, 52352, 60544] ∧
    (List.range 5).map sibL = [9, 8, 6, 4, 3] ∧ capPiL 0 = capPi := by
  refine ⟨by decide, by decide, ?_⟩
  funext π e; simp only [capPiL, capPi, capOffL, capOff_eq]

theorem capPiL_zero (π : Proof) : capPiL 0 π = capPi π := by
  funext e; simp only [capPiL, capPi, capOffL, capOff_eq]

/-- **The tape at a cap entry** of any 8-aligned cap field inside π. -/
theorem tape_capL (c : Digest) (π : Proof) (L : Log) {off e m : ℕ} (h8 : off % 8 = 0)
    (he : off + 32 * e + 32 ≤ π.size) (hm : m < 4) :
    (extractorInput c π L).getD (5 + off / 8 + 4 * e + m) 0 =
      (packBytes (bytesAt π (off + 32 * e) 32).toList).getD m 0 := by
  rw [show off + 32 * e = 8 * (off / 8 + 4 * e) by omega, packBytes_bytesAt _ (by omega) hm,
    show 5 + off / 8 + 4 * e + m = 5 + (off / 8 + 4 * e + m) by omega,
    tape_getD_proof c π L (by omega), List.getD_eq_getElem _ _]

theorem capOffL_mod (i : ℕ) : capOffL i % 8 = 0 := by
  unfold capOffL; split <;> decide

theorem capOffL_le (i : ℕ) : capOffL i ≤ 60544 := by
  unfold capOffL; split <;> decide

theorem capLogL_le (i : ℕ) : capLogL i ≤ 9 := by
  unfold capLogL; split_ifs <;> decide

/-- The cap fields lie inside π: level `i`'s `2^(capLogL i)` entries end by byte 64,640. -/
theorem capOffL_fit {i : ℕ} (hi : i ≤ 4) :
    capOffL i + 32 * 2 ^ capLogL i ≤ 64640 := by
  interval_cases i <;> decide

variable {c : Digest} {π : Proof} {L : Log}

/-- **The read of level `i ∈ [1, 4]`** (any state with the sorted index at `memX`). -/
theorem readLv_spec (hD : Dom c π L) {Xi : ℕ → Word} (hX : Sorted (tp c π L) L Xi) (s : St)
    (hM : Inv s.M) (hXs : ∀ a < L.length, rd s.M (memX + a) = Xi a) (hsz : memX ≤ s.M.size)
    {i : ℕ} (hi1 : 1 ≤ i) (hi : i ≤ 4) :
    (∀ q < 2 ^ logNL i, ∀ w < 32, rd (semXIR (tp c π L) (readLv i) s).M (stB + 32 * q + w) =
      colWord (colL (frEnc i) L (capPiL i π (q / 2 ^ sibL i)) (sibL i) q) w) ∧
    (∀ a < L.length, rd (semXIR (tp c π L) (readLv i) s).M (memX + a) = Xi a) ∧
    Inv (semXIR (tp c π L) (readLv i) s).M := by
  have hps : π.size = 797904 := hD.hs.trans piSize_eq
  have hfit := capOffL_fit hi
  have hlog := capLogL_le i
  have hoff := capOffL_le i
  have hmod := capOffL_mod i
  have hcl : 2 ^ capLogL i ≤ 2 ^ 9 := Nat.pow_le_pow_right (by norm_num) hlog
  have hnp : 2 ^ logNL i ≤ 2 ^ 16 := Nat.pow_le_pow_right (by norm_num) (by unfold logNL; omega)
  have hcapn : 2 ^ logNL i ≤ 2 ^ capLogL i * 2 ^ sibL i := by
    rw [← Nat.pow_add]; refine Nat.pow_le_pow_right (by norm_num) ?_
    unfold sibL logNL capLogL; split_ifs <;> omega
  have hsib : sibL i < 64 := by unfold sibL logNL; omega
  exact readIR_sem hD hX s hM hXs (i := i) (cw := capWL i) (nw := 32) (ncap := 2 ^ capLogL i)
    (sb := stB) (cap := capPiL i π) (by unfold capWL; omega)
    (fun e he m hm => by
      simp only [tp, getD_toArray]
      exact tape_capL c π L hmod (by
        have : 32 * e + 32 ≤ 32 * 2 ^ capLogL i := by omega
        omega) hm)
    (by norm_num) hsib (by omega) (by simp only [stB, memX]; omega)
    (by simp only [regs, stB]; omega) hcapn hsz

/-- **The `F` reading of level `i ∈ [1, 4]`**: `rdF` at `stB + 32 q + 2 r` (`r < 16`) is the
column's `F` element `r` (`readF col (16 r)`), `0` where `colL` reads nothing: S-G's `wordOf`
with π's cap entries. -/
theorem readLv_spec_F (hD : Dom c π L) {Xi : ℕ → Word} (hX : Sorted (tp c π L) L Xi) (s : St)
    (hM : Inv s.M) (hXs : ∀ a < L.length, rd s.M (memX + a) = Xi a) (hsz : memX ≤ s.M.size)
    {i : ℕ} (hi1 : 1 ≤ i) (hi : i ≤ 4) {q r : ℕ} (hq : q < 2 ^ logNL i) (hr : r < 16) :
    rdF (semXIR (tp c π L) (readLv i) s).M (stB + 32 * q + 2 * r) =
      ((colL (frEnc i) L (capPiL i π (q / 2 ^ sibL i)) (sibL i) q).map
        fun col => F.ofBytes (bytesAt col (16 * r) 16)).getD 0 := by
  have h := (readLv_spec hD hX s hM hXs hsz hi1 hi).1 q hq
  rw [rdF, rdB, rdB, h (2 * r) (by omega),
    show stB + 32 * q + 2 * r + 1 = stB + 32 * q + (2 * r + 1) by omega, h (2 * r + 1) (by omega)]
  cases colL (frEnc i) L (capPiL i π (q / 2 ^ sibL i)) (sibL i) q with
  | none => rfl
  | some col => rw [Option.map_some, Option.getD_some, F_ofBytes_words]; rfl

/-- **The read's cost** for any level parameters. -/
theorem cost_readIR (i cw sb nw sib np t : ℕ) (h1 : sib < 2 ^ 64) (h2 : nw < 2 ^ 64)
    (h3 : np < 2 ^ 64) :
    cost (readIR i cw sb nw sib np) t = 14 + np * 6576 + np * sib * 6544 + np * nw * 25 :=
  cost_readIR4 memX posL i cw sb nw sib np t h3 h1 h2

/-- The four reads cost `3,914,334,222 + 764,149,774 + 137,429,006 + 27,656,206 ≈ 2^32.17`. -/
theorem cost_readLv (t : ℕ) :
    cost (readLv 1) t = 3914334222 ∧ cost (readLv 2) t = 764149774 ∧
    cost (readLv 3) t = 137429006 ∧ cost (readLv 4) t = 27656206 := by
  simp only [readLv]
  refine ⟨?_, ?_, ?_, ?_⟩ <;> rw [cost_readIR _ _ _ _ _ _ _ (by decide) (by norm_num) (by decide)] <;> decide

theorem wf_readLv (i : ℕ) : WF (readLv i) := wf_readIR ..
theorem noLoopT_readLv (i : ℕ) : NoLoopT (readLv i) := noLoopT_readIR ..
theorem outs_readLv (i t : ℕ) : outs (readLv i) t = 0 := outs_readIR ..

/-! ## Controls -/

open ReadControls in
/-- **The level byte is read** (positive and negative): a level-1 node query is a level-1 step,
and the level-0 query of `toyN` is none at level 1 (`nodeStepP_toy` is its level-0 twin). -/
theorem nodeStepP_lv1 : nodeStepP 1 [(nodeQ 1 (dg 1) (dg 2), dg 3)] 0 0 (dg 3) = some (dg 1) ∧
    nodeStepP 1 toyN 0 0 (dg 3) = none := by decide +kernel

/-- **The cap offsets are the C phases' messages**: `fsMsgs` at FS positions `330, 369, 396, 420`
(`capPos 1 … 4`, revision 3.13) absorbs π's bytes `capOffL i … + 32·2^(capLogL i)`. -/
theorem capOffL_fsMsgs :
    fsMsgs.getD 330 none = some (capOffL 1, 32 * 2 ^ capLogL 1) ∧
    fsMsgs.getD 369 none = some (capOffL 2, 32 * 2 ^ capLogL 2) ∧
    fsMsgs.getD 396 none = some (capOffL 3, 32 * 2 ^ capLogL 3) ∧
    fsMsgs.getD 420 none = some (capOffL 4, 32 * 2 ^ capLogL 4) := by decide +kernel

/-- The level tag words differ (`"FRMNOD" ‖ 1` against level 0's). -/
theorem tagNWl_one_ne : tagNWl 1 ≠ tagNW ∧ tagCWl 1 ≠ tagCW := by decide

end FR.X

end G6_FRXReadLv

section G6_FRXMsg

-- New for `flock-recursive` (BLUEPRINT §6.2 step 4, the next level's message; stage S-H2,
-- track L-ext).

/-!
# The next message's two coordinate rows on the machine

Level `i`'s flags compare the fold with `Enc(f⁽ⁱ⁺¹⁾)` in `F` coordinates
(`FRXLevel.mem_consSet_iff`). `fwdIR` computes `Enc` of a zero-padded `F` row, so the next
message `nextMsg κ L es i` is laid out as two rows, `X[x] = (nextMsg x).f₀` at `xb + 2x` and
`Y[x] = (nextMsg x).f₁` at `yb + 2x`, zero from the message's length on.

* `zeroIR n b`: the words `b … b + n − 1` are zero (`zeroIR_sem`);
* `finIR k tw xb yb` (level 4): K element `x < k` from the tape words `tw + 4x … tw + 4x + 3`
  (`finIR_sem`); with `tw = finW = 5 + 64,640/8`, π's final field (A.3 field 13, revision 3.13),
  `tapeF_fin`, and with the chain link `finalAt es = finPi π`, `nextMsg 4` (`msg4_next`);
* `gathIR k ob xb yb` (levels 0–3): K element `x < 8k` from the decoded rows of the next level
  (row `c` at `ob + 2kc`): rows `2(x mod 8)` and `2(x mod 8) + 1`, column `x div 8`
  (`FRXLevel.nextMsg_coords`), `gathIR_sem`, and `nextMsg i` (`msgH_next`).
* `msgTIR`, `msgHIR`: both rows zeroed (`2^n` entries), then the tape or the gathered elements.

Registers `190 … 207` (free at this point of the decoder).
-/

namespace FR.X

open RecursionFast FR Finset

attribute [local irreducible] entryK storeM runPrims

/-! ## Registers -/

/-- A store pointer. -/ def mP : ℕ := 190
/-- A zero word. -/ def mZ : ℕ := 191
/-- Loop counter. -/ def mC : ℕ := 192
/-- Its count. -/ def mN : ℕ := 193
/-- The tape position. -/ def mA : ℕ := 194
/-- The `X` pointer. -/ def mX : ℕ := 195
/-- The `Y` pointer. -/ def mY : ℕ := 196
/-- The stores' scratch. -/ def mX1 : ℕ := 197
/-- Constant scratch. -/ def mK : ℕ := 198
/-- Address scratch. -/ def mT : ℕ := 199
/-- Address scratch. -/ def mU : ℕ := 200
/-- The source address. -/ def mS : ℕ := 201
/-- The loads' scratch. -/ def mS1 : ℕ := 202
/-- The position `x`. -/ def mJ : ℕ := 203
/-- The four words of a K element. -/ def mV : ℕ := 204

/-! ## Zeroing -/

/-- `mP := b`, `mZ := 0`, the count. -/
def zPre (n b : ℕ) : List Prim := [.const mP (toWord b), .const mZ 0, .const mN (toWord n)]

/-- `M[mP] := 0`, `mP += 1`. -/
def zBody : XIR := .seq (.store mP mZ) (.blk [.op .add mP mP cOne])

/-- **The words `b … b + n − 1` set to zero.** -/
def zeroIR (n b : ℕ) : XIR := .seq (.blk (zPre n b)) (.loopK mC mN (toWord n) zBody)

theorem wf_zeroIR (n b : ℕ) : WF (zeroIR n b) := by
  simp +decide only [zeroIR, zPre, zBody, WF, Writes, Prim.dst, mP, mZ, mC, mN, cTmp, regs,
    List.mem_cons, List.mem_nil_iff, forall_eq_or_imp, forall_eq, or_false, and_true]

theorem noLoopT_zeroIR (n b : ℕ) : NoLoopT (zeroIR n b) := by simp [zeroIR, zBody, NoLoopT]

theorem outs_zeroIR (n b t : ℕ) : outs (zeroIR n b) t = 0 := by simp [zeroIR, zBody, outs]

theorem cost_zeroIR (n b t : ℕ) (hn : n < 2 ^ 64) : cost (zeroIR n b) t = 14 + 9 * n := by
  have a : (toWord n).toNat = n := toNat_toWord hn
  simp only [zeroIR, zPre, zBody, cost, blkSteps, List.length_cons, List.length_nil, a]
  norm_num; ring

theorem zPre_sem (I : Array Word) (s : St) (hM : Inv s.M) (n b : ℕ) :
    rd (semXIR I (.blk (zPre n b)) s).M mP = toWord b ∧ rd (semXIR I (.blk (zPre n b)) s).M mZ = 0 ∧
    rd (semXIR I (.blk (zPre n b)) s).M mN = toWord n ∧
    (∀ i, i ≠ mP → i ≠ mZ → i ≠ mN → rd (semXIR I (.blk (zPre n b)) s).M i = rd s.M i) ∧
    Inv (semXIR I (.blk (zPre n b)) s).M := by
  have hs := hM.1
  simp only [regs] at hs
  have e0 : semXIR I (.blk (zPre n b)) s = ⟨runPrims (zPre n b) s.M, s.o⟩ := rfl
  simp only [e0]
  refine ⟨?_, ?_, ?_, fun i h1 h2 h3 => rd_runPrims_of_not_writes (by
    intro p hp
    simp only [zPre, List.mem_cons, List.mem_nil_iff, or_false] at hp
    rcases hp with rfl | rfl | rfl <;> simp only [Prim.dst] <;>
      first | exact Ne.symm h1 | exact Ne.symm h2 | exact Ne.symm h3) _,
    inv_runPrims (by simp [zPre, Prim.dst, mP, mZ, mN]) hM⟩
  all_goals simp only [zPre, runPrims, List.foldl, Prim.run]
  all_goals simp (disch := first | decide | (simp only [size_set, mP, mZ, mN]; omega)) only
      [rd_set_self, rd_set_ne]

/-- **Zeroing**: `zeroIR n b` leaves `0` at `b + w` for every `w < n` and keeps the heap
outside `[b, b + n)`. -/
theorem zeroIR_sem (I : Array Word) (s : St) (hM : Inv s.M) {n b : ℕ} (hn : n < 2 ^ 64)
    (hb : regs ≤ b) (hb2 : b + n < 2 ^ 64) (hsz : b + n ≤ s.M.size) :
    (∀ w < n, rd (semXIR I (zeroIR n b) s).M (b + w) = 0) ∧
    (∀ i, regs ≤ i → (i < b ∨ b + n ≤ i) → rd (semXIR I (zeroIR n b) s).M i = rd s.M i) ∧
    Inv (semXIR I (zeroIR n b) s).M := by
  have hs := hM.1
  simp only [regs] at hs hb
  obtain ⟨r1, r2, r3, r4, hM0⟩ := zPre_sem I s hM n b
  have z0 := size_sem I (.blk (zPre n b)) s
  rw [zeroIR, semXIR_seq]
  generalize semXIR I (.blk (zPre n b)) s = s0 at r1 r2 r3 r4 hM0 z0
  let P : ℕ → St → Prop := fun w s' => Inv s'.M ∧ s'.M.size = s.M.size ∧
    rd s'.M mP = toWord (b + w) ∧ rd s'.M mZ = 0 ∧ (∀ v < w, rd s'.M (b + v) = 0) ∧
    ∀ i, regs ≤ i → (i < b ∨ b + w ≤ i) → rd s'.M i = rd s.M i
  have hE : ∀ i, i ≠ mC → i ≠ cTmp → rd (entryK mC mN (toWord n) s0.M) i = rd s0.M i :=
    fun i h1 h2 => entryK_frame _ (Ne.symm h1) (Ne.symm h2)
  have p0 : P 0 ⟨entryK mC mN (toWord n) s0.M, s0.o⟩ := by
    refine ⟨inv_entryK hM0 (by decide), by simp only [size_entryK, z0], ?_, ?_,
      fun v hv => absurd hv (Nat.not_lt_zero _), fun i hi _ => ?_⟩
    · dsimp only; rw [hE _ (by decide) (by decide), r1, Nat.add_zero]
    · dsimp only; rw [hE _ (by decide) (by decide), r2]
    · dsimp only
      rw [hE _ (by simp only [mC, regs] at *; omega) (by simp only [cTmp, regs] at *; omega),
        r4 _ (by simp only [mP, regs] at *; omega) (by simp only [mZ, regs] at *; omega)
          (by simp only [mN, regs] at *; omega)]
  have step : ∀ w s', w < n → P w s' → P (w + 1) (decS mC (semXIR I zBody s')) := by
    rintro w s' hw ⟨i1, i2, i3, i4, i5, i6⟩
    have st : ∀ i, i ≠ cTmp → rd (storeM s'.M mP mZ) i =
        if i = b + w then rd s'.M mZ else rd s'.M i :=
      fun i hi => rd_storeM i1 i3 (by simp only [regs]; omega) (by omega) (by omega) (by decide)
        (by decide) hi
    have hM1 : Inv (storeM s'.M mP mZ) := inv_of_frame i1 (size_storeM ..) fun i hi => by
      rw [st i (by simp only [cTmp]; omega), if_neg (by omega)]
    have e1 : semXIR I zBody s' = ⟨runPrims [.op .add mP mP cOne] (storeM s'.M mP mZ), s'.o⟩ := rfl
    have hP1 : rd (storeM s'.M mP mZ) mP = toWord (b + w) := by
      rw [st _ (by decide), if_neg (by simp only [mP]; omega), i3]
    obtain ⟨n1, n2⟩ := incr_sem _ hM1 (r := mP) (by decide) (by decide) hP1
    have hd : ∀ i, i ≠ mC → rd (decS mC (semXIR I zBody s')).M i = rd (semXIR I zBody s').M i :=
      fun i h => rd_decS (Ne.symm h) _
    rw [e1] at hd ⊢
    refine ⟨inv_decS (inv_runPrims (by simp [Prim.dst, mP]) hM1) (by decide),
      by rw [size_decS, size_runPrims, size_storeM, i2], ?_, ?_, fun v hv => ?_, fun i hi hi2 => ?_⟩
    · rw [hd _ (by decide), n1, Nat.add_assoc]
    · rw [hd _ (by decide), n2 _ (by decide), st _ (by decide), if_neg (by simp only [mZ]; omega), i4]
    · rw [hd _ (by simp only [mC]; omega), n2 _ (by simp only [mP]; omega),
        st _ (by simp only [cTmp]; omega)]
      rcases Nat.lt_succ_iff_lt_or_eq.mp hv with h | rfl
      · rw [if_neg (by omega), i5 v h]
      · rw [if_pos rfl, i4]
    · simp only [regs] at hi
      rw [hd _ (by simp only [mC]; omega), n2 _ (by simp only [mP]; omega),
        st _ (by simp only [cTmp]; omega), if_neg (by omega), i6 i (by simp only [regs]; omega)
        (hi2.imp_right fun h => by omega)]
  have hN : rd s0.M mN = toWord n := r3
  have := loopK_run I zBody P s0 hM0 (by decide) (by decide) (by decide) hN hn p0 step
  exact ⟨this.2.2.2.2.1, fun i hi hi2 => this.2.2.2.2.2 i hi hi2, this.1⟩

/-! ## The final message from the tape (level 4) -/

/-- `mA := tw`, `mX := xb`, `mY := yb`, the count. -/
def finPre (k tw xb yb : ℕ) : List Prim :=
  [.const mA (toWord tw), .const mX (toWord xb), .const mY (toWord yb), .const mN (toWord k)]

/-- One tape word from `mA` into `d`; `mA += 1`. -/
def inW (d : ℕ) : XIR := .seq (.input d mA) (.blk [.op .add mA mA cOne])

/-- The four tape words from `mA` into `mV … mV + 3`; `mA += 4`. -/
def finIn : XIR := .seq (inW mV) (.seq (inW (mV + 1)) (.seq (inW (mV + 2)) (inW (mV + 3))))

/-- One K element: `f₀` to `X`, `f₁` to `Y`; `mX += 2`, `mY += 2`. -/
def finBody : XIR :=
  .seq finIn (.seq (stF mX mX1 mV) (.seq (stF mY mX1 (mV + 2))
    (.blk [.const mK 2, .op .add mX mX mK, .op .add mY mY mK])))

/-- **`k` K elements from the tape** at `tw`: element `x` from words `tw + 4x … tw + 4x + 3`,
`f₀` to `xb + 2x`, `f₁` to `yb + 2x`. -/
def finIR (k tw xb yb : ℕ) : XIR := .seq (.blk (finPre k tw xb yb)) (.loopK mC mN (toWord k) finBody)

theorem wf_finIR (k tw xb yb : ℕ) : WF (finIR k tw xb yb) := by
  simp +decide only [finIR, finPre, finBody, finIn, inW, stF, WF, Writes, Prim.dst, mA, mX, mY, mX1,
    mK, mV, mC, mN, cTmp, regs, List.mem_cons, List.mem_nil_iff, forall_eq_or_imp, forall_eq,
    or_false, and_true]

theorem noLoopT_finIR (k tw xb yb : ℕ) : NoLoopT (finIR k tw xb yb) := by
  simp [finIR, finBody, finIn, inW, stF, NoLoopT]

theorem outs_finIR (k tw xb yb t : ℕ) : outs (finIR k tw xb yb) t = 0 := by
  simp [finIR, finBody, finIn, inW, stF, outs]

theorem cost_finIR (k tw xb yb t : ℕ) (hk : k < 2 ^ 64) : cost (finIR k tw xb yb) t = 16 + 48 * k := by
  have a : (toWord k).toNat = k := toNat_toWord hk
  simp only [finIR, finPre, finBody, finIn, inW, stF, cost, blkSteps, List.length_cons,
    List.length_nil, a]
  norm_num; ring

theorem inW_sem (I : Array Word) (s : St) (hM : Inv s.M) {d a : ℕ} (hd4 : 4 ≤ d) (hdr : d < regs)
    (hdA : d ≠ mA) (ha : a + 1 < 2 ^ 64) (hA : rd s.M mA = toWord a) :
    rd (semXIR I (inW d) s).M d = I.getD a 0 ∧ rd (semXIR I (inW d) s).M mA = toWord (a + 1) ∧
    (∀ i, i ≠ d → i ≠ mA → rd (semXIR I (inW d) s).M i = rd s.M i) ∧
    Inv (semXIR I (inW d) s).M := by
  have hs := hM.1
  have h1 : rd s.M cOne = 1 := hM.2 0 (by decide)
  simp only [regs] at hs hdr
  have t0 : (toWord a).toNat = a := toNat_toWord (by omega)
  have e : semXIR I (inW d) s = ⟨runPrims [.op .add mA mA cOne]
      (s.M.setIfInBounds d (I.getD (rd s.M mA).toNat 0)), s.o⟩ := rfl
  rw [e]
  generalize hM1 : s.M.setIfInBounds d (I.getD (rd s.M mA).toNat 0) = M1
  have a1 : rd M1 d = I.getD a 0 := by rw [← hM1, rd_set_self (by omega), hA, t0]
  have a2 : ∀ i, i ≠ d → rd M1 i = rd s.M i := fun i hi => by rw [← hM1, rd_set_ne (Ne.symm hi)]
  have hI1 : Inv M1 := inv_of_frame hM (by rw [← hM1, size_set]) fun i hi => a2 i (by omega)
  obtain ⟨n1, n2⟩ := incr_sem M1 hI1 (r := mA) (by decide) (by decide) ((a2 _ (Ne.symm hdA)).trans hA)
  exact ⟨by rw [n2 _ hdA, a1], n1, fun i h1 h2 => by rw [n2 _ h2, a2 _ h1],
    inv_runPrims (by simp [Prim.dst, mA]) hI1⟩

theorem finIn_sem (I : Array Word) (s : St) (hM : Inv s.M) {a : ℕ} (ha : a + 4 < 2 ^ 64)
    (hA : rd s.M mA = toWord a) :
    rd (semXIR I finIn s).M mV = I.getD a 0 ∧ rd (semXIR I finIn s).M (mV + 1) = I.getD (a + 1) 0 ∧
    rd (semXIR I finIn s).M (mV + 2) = I.getD (a + 2) 0 ∧
    rd (semXIR I finIn s).M (mV + 3) = I.getD (a + 3) 0 ∧
    rd (semXIR I finIn s).M mA = toWord (a + 4) ∧
    (∀ i, i ≠ mV → i ≠ mV + 1 → i ≠ mV + 2 → i ≠ mV + 3 → i ≠ mA →
      rd (semXIR I finIn s).M i = rd s.M i) ∧
    Inv (semXIR I finIn s).M := by
  rw [finIn, semXIR_seq]
  obtain ⟨a1, a2, a3, hM1⟩ := inW_sem I s hM (d := mV) (by decide) (by decide) (by decide)
    (by omega) hA
  generalize semXIR I (inW mV) s = s1 at a1 a2 a3 hM1
  rw [semXIR_seq]
  obtain ⟨b1, b2, b3, hM2⟩ := inW_sem I s1 hM1 (d := mV + 1) (by decide) (by decide) (by decide)
    (by omega) a2
  generalize semXIR I (inW (mV + 1)) s1 = s2 at b1 b2 b3 hM2
  rw [semXIR_seq]
  obtain ⟨c1, c2, c3, hM3⟩ := inW_sem I s2 hM2 (d := mV + 2) (by decide) (by decide) (by decide)
    (by omega) b2
  generalize semXIR I (inW (mV + 2)) s2 = s3 at c1 c2 c3 hM3
  obtain ⟨d1, d2, d3, hM4⟩ := inW_sem I s3 hM3 (d := mV + 3) (by decide) (by decide) (by decide)
    (by omega) c2
  generalize semXIR I (inW (mV + 3)) s3 = s4 at d1 d2 d3 hM4
  refine ⟨?_, ?_, ?_, d1, d2, fun i i1 i2 i3 i4 i5 => ?_, hM4⟩
  · rw [d3 _ (by decide) (by decide), c3 _ (by decide) (by decide), b3 _ (by decide) (by decide),
      a1]
  · rw [d3 _ (by decide) (by decide), c3 _ (by decide) (by decide), b1]
  · rw [d3 _ (by decide) (by decide), c1]
  · rw [d3 _ i4 i5, c3 _ i3 i5, b3 _ i2 i5, a3 _ i1 i5]

/-- `mX += 2`, `mY += 2`. -/
theorem stepXY_sem (I : Array Word) (s : St) (hM : Inv s.M) {x y : ℕ} (hX : rd s.M mX = toWord x)
    (hY : rd s.M mY = toWord y) :
    rd (semXIR I (.blk [.const mK 2, .op .add mX mX mK, .op .add mY mY mK]) s).M mX = toWord (x + 2) ∧
    rd (semXIR I (.blk [.const mK 2, .op .add mX mX mK, .op .add mY mY mK]) s).M mY = toWord (y + 2) ∧
    (∀ i, i ≠ mK → i ≠ mX → i ≠ mY →
      rd (semXIR I (.blk [.const mK 2, .op .add mX mX mK, .op .add mY mY mK]) s).M i = rd s.M i) ∧
    Inv (semXIR I (.blk [.const mK 2, .op .add mX mX mK, .op .add mY mY mK]) s).M := by
  have hs := hM.1
  simp only [regs] at hs
  have e0 : semXIR I (.blk [.const mK 2, .op .add mX mX mK, .op .add mY mY mK]) s =
      ⟨runPrims [.const mK 2, .op .add mX mX mK, .op .add mY mY mK] s.M, s.o⟩ := rfl
  simp only [e0]
  refine ⟨?_, ?_, fun i h1 h2 h3 => rd_runPrims_of_not_writes (by
    intro p hp
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hp
    rcases hp with rfl | rfl | rfl <;> simp only [Prim.dst] <;>
      first | exact Ne.symm h1 | exact Ne.symm h2 | exact Ne.symm h3) _,
    inv_runPrims (by simp [Prim.dst, mK, mX, mY]) hM⟩
  all_goals simp only [runPrims, List.foldl, Prim.run]
  all_goals simp (disch := first | decide | (simp only [size_set, mK, mX, mY]; omega)) only
    [rd_set_self, rd_set_ne]
  · rw [hX, show (2 : Word) = toWord 2 from rfl, add_toWord]
  · rw [hY, show (2 : Word) = toWord 2 from rfl, add_toWord]

/-- The `F` pair of tape words `a`, `a + 1`. -/
def tapeF (I : Array Word) (a : ℕ) : F := ⟨wB (I.getD a 0), wB (I.getD (a + 1) 0)⟩

/-- **The final message's rows**: `finIR k tw xb yb` leaves at `xb + 2x` and `yb + 2x` the
`F` pairs of tape words `tw + 4x` and `tw + 4x + 2` (`x < k`), and keeps the heap outside the
two rows. -/
theorem finIR_sem (I : Array Word) (s : St) (hM : Inv s.M) {k tw xb yb : ℕ} (hk : k < 2 ^ 64)
    (htw : tw + 4 * k < 2 ^ 64) (hxb : regs ≤ xb) (hxb2 : xb + 2 * k < 2 ^ 64)
    (hyb : regs ≤ yb) (hyb2 : yb + 2 * k < 2 ^ 64) (hxs : xb + 2 * k ≤ s.M.size)
    (hys : yb + 2 * k ≤ s.M.size) (hd : xb + 2 * k ≤ yb ∨ yb + 2 * k ≤ xb) :
    (∀ x < k, rdF (semXIR I (finIR k tw xb yb) s).M (xb + 2 * x) = tapeF I (tw + 4 * x) ∧
      rdF (semXIR I (finIR k tw xb yb) s).M (yb + 2 * x) = tapeF I (tw + 4 * x + 2)) ∧
    (∀ i, regs ≤ i → (i < xb ∨ xb + 2 * k ≤ i) → (i < yb ∨ yb + 2 * k ≤ i) →
      rd (semXIR I (finIR k tw xb yb) s).M i = rd s.M i) ∧
    Inv (semXIR I (finIR k tw xb yb) s).M := by
  have hs := hM.1
  simp only [regs] at hs hxb hyb
  have hw0 : WF (.blk (finPre k tw xb yb)) := by simp +decide only [finPre, WF, Prim.dst, mA, mX,
    mY, mN, List.mem_cons, List.mem_nil_iff, forall_eq_or_imp, forall_eq, or_false, and_true]
  have e0 : semXIR I (.blk (finPre k tw xb yb)) s = ⟨runPrims (finPre k tw xb yb) s.M, s.o⟩ := rfl
  have r0 : rd (runPrims (finPre k tw xb yb) s.M) mA = toWord tw ∧
      rd (runPrims (finPre k tw xb yb) s.M) mX = toWord xb ∧
      rd (runPrims (finPre k tw xb yb) s.M) mY = toWord yb ∧
      rd (runPrims (finPre k tw xb yb) s.M) mN = toWord k := by
    simp only [finPre, runPrims, List.foldl, Prim.run]
    refine ⟨?_, ?_, ?_, ?_⟩ <;>
      simp (disch := first | decide | (simp only [size_set, mA, mX, mY, mN]; omega)) only
        [rd_set_self, rd_set_ne]
  have r4 : ∀ i, regs ≤ i → rd (runPrims (finPre k tw xb yb) s.M) i = rd s.M i := fun i hi =>
    rd_runPrims_of_not_writes (by
      simp only [finPre, List.mem_cons, List.mem_nil_iff, or_false]
      simp only [regs] at hi
      rintro p (rfl | rfl | rfl | rfl) <;> simp only [Prim.dst, mA, mX, mY, mN] <;> omega) _
  have hM0 : Inv (runPrims (finPre k tw xb yb) s.M) := by
    have h := inv_sem I hw0 hM; rwa [e0] at h
  have z0 : (runPrims (finPre k tw xb yb) s.M).size = s.M.size := size_runPrims _ _
  rw [finIR, semXIR_seq, e0]
  generalize runPrims (finPre k tw xb yb) s.M = M0 at r0 r4 hM0 z0
  obtain ⟨r1, r2, r3, rN⟩ := r0
  let P : ℕ → St → Prop := fun x s' => Inv s'.M ∧ s'.M.size = s.M.size ∧
    rd s'.M mA = toWord (tw + 4 * x) ∧ rd s'.M mX = toWord (xb + 2 * x) ∧
    rd s'.M mY = toWord (yb + 2 * x) ∧
    (∀ v < x, rdF s'.M (xb + 2 * v) = tapeF I (tw + 4 * v) ∧
      rdF s'.M (yb + 2 * v) = tapeF I (tw + 4 * v + 2)) ∧
    ∀ i, regs ≤ i → (i < xb ∨ xb + 2 * x ≤ i) → (i < yb ∨ yb + 2 * x ≤ i) → rd s'.M i = rd s.M i
  have hE : ∀ i, i ≠ mC → i ≠ cTmp → rd (entryK mC mN (toWord k) M0) i = rd M0 i :=
    fun i h1 h2 => entryK_frame _ (Ne.symm h1) (Ne.symm h2)
  have p0 : P 0 ⟨entryK mC mN (toWord k) M0, s.o⟩ := by
    refine ⟨inv_entryK hM0 (by decide), by simp only [size_entryK, z0], ?_, ?_, ?_,
      fun v hv => absurd hv (Nat.not_lt_zero _), fun i hi _ _ => ?_⟩
    · dsimp only; rw [hE _ (by decide) (by decide), r1, Nat.mul_zero, Nat.add_zero]
    · dsimp only; rw [hE _ (by decide) (by decide), r2, Nat.mul_zero, Nat.add_zero]
    · dsimp only; rw [hE _ (by decide) (by decide), r3, Nat.mul_zero, Nat.add_zero]
    · dsimp only
      rw [hE _ (by simp only [mC, regs] at *; omega) (by simp only [cTmp, regs] at *; omega),
        r4 i hi]
  have step : ∀ x s', x < k → P x s' → P (x + 1) (decS mC (semXIR I finBody s')) := by
    rintro x s' hx ⟨i1, i2, i3, i4, i5, i6, i7⟩
    rw [finBody, semXIR_seq]
    obtain ⟨a1, a2, a3, a4, a5, a6, hM1⟩ := finIn_sem I s' i1 (a := tw + 4 * x) (by omega) i3
    have z1 := size_sem I finIn s'
    generalize semXIR I finIn s' = s1 at a1 a2 a3 a4 a5 a6 hM1 z1
    rw [semXIR_seq]
    have hX1 : rd s1.M mX = toWord (xb + 2 * x) := (a6 _ (by decide) (by decide) (by decide)
      (by decide) (by decide)).trans i4
    obtain ⟨b1, b2, hM2⟩ := stF_sem I s1 hM1 (p := mX) (p1 := mX1) (v := mV) (x := xb + 2 * x)
      (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) hX1 (by simp only [regs]; omega) (by omega) (by omega)
    have z2 := size_sem I (stF mX mX1 mV) s1
    generalize semXIR I (stF mX mX1 mV) s1 = s2 at b1 b2 hM2 z2
    rw [semXIR_seq]
    have hY2 : rd s2.M mY = toWord (yb + 2 * x) :=
      (b2 _ (by simp only [mY]; omega) (by simp only [mY]; omega) (by decide) (by decide)).trans
        ((a6 _ (by decide) (by decide) (by decide) (by decide) (by decide)).trans i5)
    obtain ⟨c1, c2, hM3⟩ := stF_sem I s2 hM2 (p := mY) (p1 := mX1) (v := mV + 2) (x := yb + 2 * x)
      (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) hY2 (by simp only [regs]; omega) (by omega) (by omega)
    have z3 := size_sem I (stF mY mX1 (mV + 2)) s2
    generalize semXIR I (stF mY mX1 (mV + 2)) s2 = s3 at c1 c2 hM3 z3
    have hX3 : rd s3.M mX = toWord (xb + 2 * x) :=
      (c2 _ (by simp only [mX]; omega) (by simp only [mX]; omega) (by decide) (by decide)).trans
        ((b2 _ (by simp only [mX]; omega) (by simp only [mX]; omega) (by decide) (by decide)).trans hX1)
    have hY3 : rd s3.M mY = toWord (yb + 2 * x) :=
      (c2 _ (by simp only [mY]; omega) (by simp only [mY]; omega) (by decide) (by decide)).trans hY2
    obtain ⟨d1, d2, d3, hM4⟩ := stepXY_sem I s3 hM3 hX3 hY3
    have z4 := size_sem I (.blk [.const mK 2, .op .add mX mX mK, .op .add mY mY mK]) s3
    generalize semXIR I (.blk [.const mK 2, .op .add mX mX mK, .op .add mY mY mK]) s3 = s4
      at d1 d2 d3 hM4 z4
    have hd : ∀ i, i ≠ mC → rd (decS mC s4).M i = rd s4.M i := fun i h => rd_decS (Ne.symm h) _
    -- the heap of `s4`
    have h4 : ∀ i, regs ≤ i → i ≠ xb + 2 * x → i ≠ xb + 2 * x + 1 → i ≠ yb + 2 * x →
        i ≠ yb + 2 * x + 1 → rd s4.M i = rd s'.M i := fun i hi j1 j2 j3 j4 => by
      simp only [regs] at hi
      rw [d3 i (by simp only [mK]; omega) (by simp only [mX]; omega) (by simp only [mY]; omega),
        c2 i j3 j4 (by simp only [mX1]; omega) (by simp only [cTmp]; omega),
        b2 i j1 j2 (by simp only [mX1]; omega) (by simp only [cTmp]; omega),
        a6 i (by simp only [mV]; omega) (by simp only [mV]; omega) (by simp only [mV]; omega)
          (by simp only [mV]; omega) (by simp only [mA]; omega)]
    have hX4 : rdF s4.M (xb + 2 * x) = tapeF I (tw + 4 * x) := by
      have e1 : rdF s4.M (xb + 2 * x) = rdF s2.M (xb + 2 * x) :=
        rdF_eq ((d3 _ (by simp only [mK]; omega) (by simp only [mX]; omega)
          (by simp only [mY]; omega)).trans (c2 _ (by omega) (by omega) (by simp only [mX1]; omega)
          (by simp only [cTmp]; omega)))
          ((d3 _ (by simp only [mK]; omega) (by simp only [mX]; omega)
          (by simp only [mY]; omega)).trans (c2 _ (by omega) (by omega) (by simp only [mX1]; omega)
          (by simp only [cTmp]; omega)))
      rw [e1, b1, tapeF]
      simp only [rdF, rdB, a1, a2]
    have hY4 : rdF s4.M (yb + 2 * x) = tapeF I (tw + 4 * x + 2) := by
      have e1 : rdF s4.M (yb + 2 * x) = rdF s3.M (yb + 2 * x) :=
        rdF_eq (d3 _ (by simp only [mK]; omega) (by simp only [mX]; omega)
          (by simp only [mY]; omega)) (d3 _ (by simp only [mK]; omega) (by simp only [mX]; omega)
          (by simp only [mY]; omega))
      have e2 : rd s2.M (mV + 2) = rd s1.M (mV + 2) := b2 _ (by simp only [mV]; omega)
        (by simp only [mV]; omega) (by decide) (by decide)
      have e3 : rd s2.M (mV + 2 + 1) = rd s1.M (mV + 3) := b2 _ (by simp only [mV]; omega)
        (by simp only [mV]; omega) (by decide) (by decide)
      rw [e1, c1, tapeF]
      simp only [rdF, rdB, e2, e3, a3, a4]
    refine ⟨inv_decS hM4 (by decide), by rw [size_decS, z4, z3, z2, z1, i2], ?_, ?_, ?_,
      fun v hv => ?_, fun i hi hi2 hi3 => ?_⟩
    · rw [hd _ (by decide), d3 _ (by decide) (by decide) (by decide), c2 _ (by simp only [mA]; omega)
        (by simp only [mA]; omega) (by decide) (by decide), b2 _ (by simp only [mA]; omega)
        (by simp only [mA]; omega) (by decide) (by decide), a5]
      exact congrArg toWord (by ring)
    · rw [hd _ (by decide), d1]; exact congrArg toWord (by ring)
    · rw [hd _ (by decide), d2]; exact congrArg toWord (by ring)
    · rcases Nat.lt_succ_iff_lt_or_eq.mp hv with h | rfl
      · have g := i6 v h
        constructor
        · rw [← g.1]
          exact rdF_eq ((hd _ (by simp only [mC]; omega)).trans
            (h4 _ (by simp only [regs]; omega) (by omega) (by omega) (by omega) (by omega)))
            ((hd _ (by simp only [mC]; omega)).trans
            (h4 _ (by simp only [regs]; omega) (by omega) (by omega) (by omega) (by omega)))
        · rw [← g.2]
          exact rdF_eq ((hd _ (by simp only [mC]; omega)).trans
            (h4 _ (by simp only [regs]; omega) (by omega) (by omega) (by omega) (by omega)))
            ((hd _ (by simp only [mC]; omega)).trans
            (h4 _ (by simp only [regs]; omega) (by omega) (by omega) (by omega) (by omega)))
      · exact ⟨(rdF_eq (hd _ (by simp only [mC]; omega)) (hd _ (by simp only [mC]; omega))).trans hX4,
          (rdF_eq (hd _ (by simp only [mC]; omega)) (hd _ (by simp only [mC]; omega))).trans hY4⟩
    · simp only [regs] at hi
      rw [hd _ (by simp only [mC]; omega), h4 i (by simp only [regs]; omega) (by omega) (by omega)
        (by omega) (by omega), i7 i (by simp only [regs]; omega) (hi2.imp_right fun h => by omega)
        (hi3.imp_right fun h => by omega)]
  have := loopK_run I finBody P ⟨M0, s.o⟩ hM0 (by decide) (by decide) (by decide) rN hk p0 step
  exact ⟨this.2.2.2.2.2.1, this.2.2.2.2.2.2, this.1⟩

/-! ## Level 4's message rows -/

/-- **The rows of a tape message**: both rows of `2^n` entries zeroed, then `k` K elements from
the tape at `tw`. -/
def msgTIR (n k tw xb yb : ℕ) : XIR :=
  .seq (zeroIR (2 * 2 ^ n) xb) (.seq (zeroIR (2 * 2 ^ n) yb) (finIR k tw xb yb))

theorem wf_msgTIR (n k tw xb yb : ℕ) : WF (msgTIR n k tw xb yb) :=
  ⟨wf_zeroIR _ _, wf_zeroIR _ _, wf_finIR _ _ _ _⟩

theorem noLoopT_msgTIR (n k tw xb yb : ℕ) : NoLoopT (msgTIR n k tw xb yb) :=
  ⟨noLoopT_zeroIR _ _, noLoopT_zeroIR _ _, noLoopT_finIR _ _ _ _⟩

theorem outs_msgTIR (n k tw xb yb t : ℕ) : outs (msgTIR n k tw xb yb) t = 0 := by
  simp only [msgTIR, outs, outs_zeroIR, outs_finIR]

theorem cost_msgTIR (n k tw xb yb t : ℕ) (hn : 2 * 2 ^ n < 2 ^ 64) (hk : k < 2 ^ 64) :
    cost (msgTIR n k tw xb yb) t = 46 + 36 * 2 ^ n + 48 * k := by
  simp only [msgTIR, cost, cost_zeroIR _ _ _ hn, cost_finIR _ _ _ _ _ hk]; ring

/-- `F`'s zero from two zero words. -/
theorem rdF_zero_of {M : Mem} {a : ℕ} (h0 : rd M a = 0) (h1 : rd M (a + 1) = 0) : rdF M a = 0 := by
  simp only [rdF, rdB, h0, h1]; rfl

/-- **A tape message's rows**: entry `j < 2^n` of `X` (`Y`) is the tape pair at `tw + 4j`
(`tw + 4j + 2`) for `j < k`, and `0` from `k` on; the heap outside the rows is kept. -/
theorem msgTIR_sem (I : Array Word) (s : St) (hM : Inv s.M) {n k tw xb yb : ℕ} (hn : n ≤ 20)
    (hk : k ≤ 2 ^ n) (htw : tw + 4 * k < 2 ^ 64) (hxb : regs ≤ xb) (hyb : regs ≤ yb)
    (hxb2 : xb + 2 * 2 ^ n < 2 ^ 64) (hyb2 : yb + 2 * 2 ^ n < 2 ^ 64)
    (hxs : xb + 2 * 2 ^ n ≤ s.M.size) (hys : yb + 2 * 2 ^ n ≤ s.M.size)
    (hd : xb + 2 * 2 ^ n ≤ yb ∨ yb + 2 * 2 ^ n ≤ xb) :
    (∀ j < 2 ^ n, rdF (semXIR I (msgTIR n k tw xb yb) s).M (xb + 2 * j) =
        (if j < k then tapeF I (tw + 4 * j) else 0) ∧
      rdF (semXIR I (msgTIR n k tw xb yb) s).M (yb + 2 * j) =
        (if j < k then tapeF I (tw + 4 * j + 2) else 0)) ∧
    (∀ i, regs ≤ i → (i < xb ∨ xb + 2 * 2 ^ n ≤ i) → (i < yb ∨ yb + 2 * 2 ^ n ≤ i) →
      rd (semXIR I (msgTIR n k tw xb yb) s).M i = rd s.M i) ∧
    Inv (semXIR I (msgTIR n k tw xb yb) s).M := by
  have hP : 2 ^ n ≤ 2 ^ 20 := Nat.pow_le_pow_right (by norm_num) hn
  have hs := hM.1
  simp only [regs] at hs hxb hyb
  rw [msgTIR, semXIR_seq]
  obtain ⟨a1, a2, hM1⟩ := zeroIR_sem I s hM (n := 2 * 2 ^ n) (b := xb) (by omega)
    (by simp only [regs]; omega) hxb2 hxs
  have z1 := size_sem I (zeroIR (2 * 2 ^ n) xb) s
  generalize semXIR I (zeroIR (2 * 2 ^ n) xb) s = s1 at a1 a2 hM1 z1
  rw [semXIR_seq]
  obtain ⟨b1, b2, hM2⟩ := zeroIR_sem I s1 hM1 (n := 2 * 2 ^ n) (b := yb) (by omega)
    (by simp only [regs]; omega) hyb2 (by omega)
  have z2 := size_sem I (zeroIR (2 * 2 ^ n) yb) s1
  generalize semXIR I (zeroIR (2 * 2 ^ n) yb) s1 = s2 at b1 b2 hM2 z2
  obtain ⟨c1, c2, hM3⟩ := finIR_sem I s2 hM2 (k := k) (tw := tw) (xb := xb) (yb := yb) (by omega)
    htw (by simp only [regs]; omega) (by omega) (by simp only [regs]; omega) (by omega) (by omega)
    (by omega) (by omega)
  refine ⟨fun j hj => ?_, fun i hi hi2 hi3 => ?_, hM3⟩
  · by_cases hjk : j < k
    · rw [if_pos hjk, if_pos hjk]; exact c1 j hjk
    · rw [if_neg hjk, if_neg hjk]
      have hx : rdF s2.M (xb + 2 * j) = 0 := rdF_zero_of
        ((b2 _ (by simp only [regs]; omega) (by omega)).trans (a1 _ (by omega)))
        ((b2 _ (by simp only [regs]; omega) (by omega)).trans
          (by rw [show xb + 2 * j + 1 = xb + (2 * j + 1) by omega]; exact a1 _ (by omega)))
      have hy : rdF s2.M (yb + 2 * j) = 0 := rdF_zero_of (b1 _ (by omega))
        (by rw [show yb + 2 * j + 1 = yb + (2 * j + 1) by omega]; exact b1 _ (by omega))
      constructor
      · rw [← hx]
        exact rdF_eq (c2 _ (by simp only [regs]; omega) (by omega) (by omega))
          (c2 _ (by simp only [regs]; omega) (by omega) (by omega))
      · rw [← hy]
        exact rdF_eq (c2 _ (by simp only [regs]; omega) (by omega) (by omega))
          (c2 _ (by simp only [regs]; omega) (by omega) (by omega))
  · rw [c2 i hi (hi2.imp_right fun h => by omega) (hi3.imp_right fun h => by omega),
      b2 i hi hi3, a2 i hi hi2]

/-- The byte offset of the final message in π (A.3 field 13, revision 3.13). -/
def finOff : ℕ := 64640

/-- Its first tape word. -/
def finW : ℕ := 5 + finOff / 8

/-- **The final message's element `x` as π carries it**: the 32 bytes at `finOff + 32x`. -/
def finPi (π : Proof) (x : ℕ) : K := chK (bytesAt π (finOff + 32 * x) 32)

/-- **Value control of the offset** (A.3, revision 3.13): the final message follows level 4's
cap (`2^7` entries of 32 bytes) and ends where the columns start (68,736). -/
theorem finOff_ctl : finOff = capOffL 4 + 32 * 2 ^ capLogL 4 ∧ finOff + 32 * 128 = 68736 ∧
    finW = 8085 := by decide

/-- **The tape at the final message**: the two tape pairs of element `x < 128` are `finPi`. -/
theorem tapeF_fin (c : Digest) (π : Proof) (L : Log) (hs : π.size = piSize) {x : ℕ}
    (hx : x < 128) :
    (⟨tapeF (tp c π L) (finW + 4 * x), tapeF (tp c π L) (finW + 4 * x + 2)⟩ : K) = finPi π x := by
  have hp : π.size = 797904 := hs.trans piSize_eq
  have T : ∀ m < 4, (tp c π L).getD (finW + 4 * x + m) 0 =
      (packBytes (bytesAt π (finOff + 32 * x) 32).toList).getD m 0 := fun m hm => by
    rw [tp, getD_toArray]
    exact tape_capL c π L (off := finOff) (by decide) (by rw [hp]; simp only [finOff]; omega) hm
  rw [finPi, chK_words, tapeF, tapeF, ← T 0 (by norm_num), ← T 1 (by norm_num),
    ← T 2 (by norm_num), ← T 3 (by norm_num)]
  rfl

/-! ## The message rows from the next level's decoded rows (levels 0–3) -/

/-- `mS := ob + 4k (x mod 8) + 2 (x div 8)` (`x` in `mJ`): row `2 (x mod 8)` of `2k` cells,
column `x div 8`. -/
def gAd (k ob : ℕ) : List Prim :=
  [.const mK 7, .op .and mT mJ mK, .const mK (toWord (4 * k)), .op .mul mT mT mK, .const mK 3,
   .op .shr mU mJ mK, .op .add mU mU mU, .op .add mT mT mU, .const mK (toWord ob),
   .op .add mS mT mK]

/-- `mS += 2k`: the next row. -/
def gNx (k : ℕ) : List Prim := [.const mK (toWord (2 * k)), .op .add mS mS mK]

/-- The pointers: `mX += 2`, `mY += 2`. -/
def stepXY : List Prim := [.const mK 2, .op .add mX mX mK, .op .add mY mY mK]

/-- One K element: `X[x] :=` row `2 (x mod 8)`, `Y[x] :=` row `2 (x mod 8) + 1`, column `x div 8`. -/
def gBody (k ob : ℕ) : XIR :=
  .seq (.blk (gAd k ob)) (.seq (ldF mV mS mS1) (.seq (stF mX mX1 mV) (.seq (.blk (gNx k))
    (.seq (ldF mV mS mS1) (.seq (stF mY mX1 mV) (.seq (.blk stepXY)
      (.blk [.op .add mJ mJ cOne])))))))

/-- The start: `x := 0`, the pointers, the count `8k`. -/
def gPre (k xb yb : ℕ) : List Prim :=
  [.const mJ 0, .const mX (toWord xb), .const mY (toWord yb), .const mN (toWord (8 * k))]

/-- **The next message's rows from the decoded rows** (row `c` at `ob + 2kc`, `k` entries):
`8k` K elements. -/
def gathIR (k ob xb yb : ℕ) : XIR :=
  .seq (.blk (gPre k xb yb)) (.loopK mC mN (toWord (8 * k)) (gBody k ob))

theorem wf_gathIR (k ob xb yb : ℕ) : WF (gathIR k ob xb yb) := by
  simp +decide only [gathIR, gPre, gBody, gAd, gNx, stepXY, ldF, stF, WF, Writes, Prim.dst, mJ, mX,
    mY, mN, mK, mT, mU, mS, mS1, mV, mX1, mC, cTmp, regs, List.mem_cons, List.mem_nil_iff,
    forall_eq_or_imp, exists_eq_or_imp, forall_eq, exists_eq_left, or_false, and_true]

theorem noLoopT_gathIR (k ob xb yb : ℕ) : NoLoopT (gathIR k ob xb yb) := by
  simp [gathIR, gBody, ldF, stF, NoLoopT]

theorem outs_gathIR (k ob xb yb t : ℕ) : outs (gathIR k ob xb yb) t = 0 := by
  simp [gathIR, gBody, ldF, stF, outs]

theorem cost_gathIR (k ob xb yb t : ℕ) (hk : 8 * k < 2 ^ 64) :
    cost (gathIR k ob xb yb) t = 16 + 8 * k * 70 := by
  have a : (toWord (8 * k)).toNat = 8 * k := toNat_toWord hk
  simp only [gathIR, gPre, gBody, gAd, gNx, stepXY, ldF, stF, cost, blkSteps, List.length_cons,
    List.length_nil, a]
  norm_num; ring

theorem and7_toWord {a : ℕ} (ha : a < 2 ^ 64) : XOp.and.eval (toWord a) 7 = toWord (a % 8) := by
  apply BitVec.eq_of_toNat_eq
  simp only [XOp.eval]
  rw [BitVec.toNat_and, toNat_toWord ha, show (7 : Word).toNat = 2 ^ 3 - 1 from rfl,
    Nat.and_two_pow_sub_one_eq_mod, toNat_toWord (by omega)]

theorem gAd_sem (I : Array Word) (s : St) (hM : Inv s.M) {k ob x : ℕ} (hx : x < 2 ^ 64)
    (hJ : rd s.M mJ = toWord x) :
    rd (semXIR I (.blk (gAd k ob)) s).M mS = toWord (ob + 4 * k * (x % 8) + 2 * (x / 8)) ∧
    (∀ i, i ≠ mK → i ≠ mT → i ≠ mU → i ≠ mS → rd (semXIR I (.blk (gAd k ob)) s).M i = rd s.M i) ∧
    Inv (semXIR I (.blk (gAd k ob)) s).M := by
  have hs := hM.1
  simp only [regs] at hs
  have e0 : semXIR I (.blk (gAd k ob)) s = ⟨runPrims (gAd k ob) s.M, s.o⟩ := rfl
  simp only [e0]
  refine ⟨?_, fun i h1 h2 h3 h4 => rd_runPrims_of_not_writes (by
    intro p hp
    simp only [gAd, List.mem_cons, List.mem_nil_iff, or_false] at hp
    rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      simp only [Prim.dst] <;>
      first | exact Ne.symm h1 | exact Ne.symm h2 | exact Ne.symm h3 | exact Ne.symm h4) _,
    inv_runPrims (by simp [gAd, Prim.dst, mK, mT, mU, mS]) hM⟩
  simp only [gAd, runPrims, List.foldl, Prim.run]
  simp (disch := first | decide | (simp only [size_set, mK, mT, mU, mS]; omega)) only
    [rd_set_self, rd_set_ne]
  rw [hJ, and7_toWord hx, mul_toWord, show (3 : Word) = toWord 3 from rfl, shr_toWord hx (by norm_num),
    add_toWord, add_toWord, add_toWord]
  exact congrArg toWord (by rw [show (2 : ℕ) ^ 3 = 8 from rfl]; ring)

theorem gNx_sem (I : Array Word) (s : St) (hM : Inv s.M) {k a : ℕ} (hS : rd s.M mS = toWord a) :
    rd (semXIR I (.blk (gNx k)) s).M mS = toWord (a + 2 * k) ∧
    (∀ i, i ≠ mK → i ≠ mS → rd (semXIR I (.blk (gNx k)) s).M i = rd s.M i) ∧
    Inv (semXIR I (.blk (gNx k)) s).M := by
  have hs := hM.1
  simp only [regs] at hs
  have e0 : semXIR I (.blk (gNx k)) s = ⟨runPrims (gNx k) s.M, s.o⟩ := rfl
  simp only [e0]
  refine ⟨?_, fun i h1 h2 => rd_runPrims_of_not_writes (by
    intro p hp
    simp only [gNx, List.mem_cons, List.mem_nil_iff, or_false] at hp
    rcases hp with rfl | rfl <;> simp only [Prim.dst] <;>
      first | exact Ne.symm h1 | exact Ne.symm h2) _,
    inv_runPrims (by simp [gNx, Prim.dst, mK, mS]) hM⟩
  simp only [gNx, runPrims, List.foldl, Prim.run]
  simp (disch := first | decide | (simp only [size_set, mK, mS]; omega)) only
    [rd_set_self, rd_set_ne]
  rw [hS, add_toWord]

/-- **The gathered rows**: for `x < 8k`, `X[x]` is the `F` element of row `2 (x mod 8)` (rows of
`2k` cells from `ob`) at column `x div 8`, `Y[x]` that of row `2 (x mod 8) + 1`; the heap outside
the two rows is kept. -/
theorem gathIR_sem (I : Array Word) (s : St) (hM : Inv s.M) {k ob xb yb : ℕ}
    (hk : 8 * k < 2 ^ 64) (hob : regs ≤ ob) (hob2 : ob + 32 * k < 2 ^ 64)
    (hxb : regs ≤ xb) (hxb2 : xb + 16 * k < 2 ^ 64) (hyb : regs ≤ yb) (hyb2 : yb + 16 * k < 2 ^ 64)
    (hxs : xb + 16 * k ≤ s.M.size) (hys : yb + 16 * k ≤ s.M.size)
    (hd : xb + 16 * k ≤ yb ∨ yb + 16 * k ≤ xb) (hdx : ob + 32 * k ≤ xb ∨ xb + 16 * k ≤ ob)
    (hdy : ob + 32 * k ≤ yb ∨ yb + 16 * k ≤ ob) :
    (∀ x < 8 * k, rdF (semXIR I (gathIR k ob xb yb) s).M (xb + 2 * x) =
        rdF s.M (ob + 4 * k * (x % 8) + 2 * (x / 8)) ∧
      rdF (semXIR I (gathIR k ob xb yb) s).M (yb + 2 * x) =
        rdF s.M (ob + 4 * k * (x % 8) + 2 * (x / 8) + 2 * k)) ∧
    (∀ i, regs ≤ i → (i < xb ∨ xb + 16 * k ≤ i) → (i < yb ∨ yb + 16 * k ≤ i) →
      rd (semXIR I (gathIR k ob xb yb) s).M i = rd s.M i) ∧
    Inv (semXIR I (gathIR k ob xb yb) s).M := by
  have hs := hM.1
  simp only [regs] at hs hxb hyb hob
  have hw0 : WF (.blk (gPre k xb yb)) := by simp +decide only [gPre, WF, Prim.dst, mJ, mX, mY, mN,
    List.mem_cons, List.mem_nil_iff, forall_eq_or_imp, forall_eq, or_false, and_true]
  have e0 : semXIR I (.blk (gPre k xb yb)) s = ⟨runPrims (gPre k xb yb) s.M, s.o⟩ := rfl
  have r0 : rd (runPrims (gPre k xb yb) s.M) mJ = toWord 0 ∧
      rd (runPrims (gPre k xb yb) s.M) mX = toWord xb ∧
      rd (runPrims (gPre k xb yb) s.M) mY = toWord yb ∧
      rd (runPrims (gPre k xb yb) s.M) mN = toWord (8 * k) := by
    simp only [gPre, runPrims, List.foldl, Prim.run]
    refine ⟨?_, ?_, ?_, ?_⟩ <;>
      simp (disch := first | decide | (simp only [size_set, mJ, mX, mY, mN]; omega)) only
        [rd_set_self, rd_set_ne] <;> rfl
  have r4 : ∀ i, regs ≤ i → rd (runPrims (gPre k xb yb) s.M) i = rd s.M i := fun i hi =>
    rd_runPrims_of_not_writes (by
      simp only [gPre, List.mem_cons, List.mem_nil_iff, or_false]
      simp only [regs] at hi
      rintro p (rfl | rfl | rfl | rfl) <;> simp only [Prim.dst, mJ, mX, mY, mN] <;> omega) _
  have hM0 : Inv (runPrims (gPre k xb yb) s.M) := by
    have h := inv_sem I hw0 hM; rwa [e0] at h
  have z0 : (runPrims (gPre k xb yb) s.M).size = s.M.size := size_runPrims _ _
  rw [gathIR, semXIR_seq, e0]
  generalize runPrims (gPre k xb yb) s.M = M0 at r0 r4 hM0 z0
  obtain ⟨r1, r2, r3, rN⟩ := r0
  let P : ℕ → St → Prop := fun x s' => Inv s'.M ∧ s'.M.size = s.M.size ∧
    rd s'.M mJ = toWord x ∧ rd s'.M mX = toWord (xb + 2 * x) ∧ rd s'.M mY = toWord (yb + 2 * x) ∧
    (∀ v < x, rdF s'.M (xb + 2 * v) = rdF s.M (ob + 4 * k * (v % 8) + 2 * (v / 8)) ∧
      rdF s'.M (yb + 2 * v) = rdF s.M (ob + 4 * k * (v % 8) + 2 * (v / 8) + 2 * k)) ∧
    ∀ i, regs ≤ i → (i < xb ∨ xb + 2 * x ≤ i) → (i < yb ∨ yb + 2 * x ≤ i) → rd s'.M i = rd s.M i
  have hE : ∀ i, i ≠ mC → i ≠ cTmp → rd (entryK mC mN (toWord (8 * k)) M0) i = rd M0 i :=
    fun i h1 h2 => entryK_frame _ (Ne.symm h1) (Ne.symm h2)
  have p0 : P 0 ⟨entryK mC mN (toWord (8 * k)) M0, s.o⟩ := by
    refine ⟨inv_entryK hM0 (by decide), by simp only [size_entryK, z0], ?_, ?_, ?_,
      fun v hv => absurd hv (Nat.not_lt_zero _), fun i hi _ _ => ?_⟩
    · dsimp only; rw [hE _ (by decide) (by decide), r1]
    · dsimp only; rw [hE _ (by decide) (by decide), r2, Nat.mul_zero, Nat.add_zero]
    · dsimp only; rw [hE _ (by decide) (by decide), r3, Nat.mul_zero, Nat.add_zero]
    · dsimp only
      rw [hE _ (by simp only [mC, regs] at *; omega) (by simp only [cTmp, regs] at *; omega),
        r4 i hi]
  have step : ∀ x s', x < 8 * k → P x s' → P (x + 1) (decS mC (semXIR I (gBody k ob) s')) := by
    rintro x s' hx ⟨i1, i2, i3, i4, i5, i6, i7⟩
    have hm8 : 4 * k * (x % 8) ≤ 4 * k * 7 := Nat.mul_le_mul_left _ (by omega)
    have hd8 : x / 8 < k := (Nat.div_lt_iff_lt_mul (by norm_num)).2 (by omega)
    -- the source address
    rw [gBody, semXIR_seq]
    obtain ⟨a1, a2, hM1⟩ := gAd_sem I s' i1 (k := k) (ob := ob) (by omega) i3
    have z1 := size_sem I (.blk (gAd k ob)) s'
    generalize semXIR I (.blk (gAd k ob)) s' = s1 at a1 a2 hM1 z1
    generalize ha : ob + 4 * k * (x % 8) + 2 * (x / 8) = a at a1
    have ha2 : a + 2 * k + 2 ≤ ob + 32 * k := by omega
    have h1 : ∀ i, regs ≤ i → rd s1.M i = rd s'.M i := fun i hi => by
      simp only [regs] at hi
      exact a2 i (by simp only [mK]; omega) (by simp only [mT]; omega) (by simp only [mU]; omega)
        (by simp only [mS]; omega)
    -- `X[x]`
    rw [semXIR_seq]
    obtain ⟨b1, b2, b3⟩ := ldF_sem I s1 hM1 (d := mV) (p := mS) (p1 := mS1) (x := a) (by decide)
      (by decide) (by decide) (by decide) (by decide) (by decide) a1 (by simp only [regs]; omega)
      (by omega)
    have hM2 := inv_sem I (P := ldF mV mS mS1) (s := s1) (by simp +decide only [ldF, WF, Prim.dst,
      mV, mS1, and_true]) hM1
    have z2 := size_sem I (ldF mV mS mS1) s1
    generalize semXIR I (ldF mV mS mS1) s1 = s2 at b1 b2 b3 hM2 z2
    rw [semXIR_seq]
    have hX2 : rd s2.M mX = toWord (xb + 2 * x) := by
      rw [b3 _ (by decide) (by decide) (by decide), a2 _ (by decide) (by decide) (by decide)
        (by decide), i4]
    obtain ⟨c1, c2, hM3⟩ := stF_sem I s2 hM2 (p := mX) (p1 := mX1) (v := mV) (x := xb + 2 * x)
      (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) hX2 (by simp only [regs]; omega) (by omega) (by omega)
    have z3 := size_sem I (stF mX mX1 mV) s2
    generalize semXIR I (stF mX mX1 mV) s2 = s3 at c1 c2 hM3 z3
    -- the next row
    rw [semXIR_seq]
    have hS3 : rd s3.M mS = toWord a := by
      rw [c2 _ (by simp only [mS]; omega) (by simp only [mS]; omega) (by decide) (by decide),
        b3 _ (by decide) (by decide) (by decide), a1]
    obtain ⟨d1, d2, hM4⟩ := gNx_sem I s3 hM3 (k := k) hS3
    have z4 := size_sem I (.blk (gNx k)) s3
    generalize semXIR I (.blk (gNx k)) s3 = s4 at d1 d2 hM4 z4
    -- `Y[x]`
    rw [semXIR_seq]
    obtain ⟨f1, f2, f3⟩ := ldF_sem I s4 hM4 (d := mV) (p := mS) (p1 := mS1) (x := a + 2 * k)
      (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) d1
      (by simp only [regs]; omega) (by omega)
    have hM5 := inv_sem I (P := ldF mV mS mS1) (s := s4) (by simp +decide only [ldF, WF, Prim.dst,
      mV, mS1, and_true]) hM4
    have z5 := size_sem I (ldF mV mS mS1) s4
    generalize semXIR I (ldF mV mS mS1) s4 = s5 at f1 f2 f3 hM5 z5
    rw [semXIR_seq]
    have hY5 : rd s5.M mY = toWord (yb + 2 * x) := by
      rw [f3 _ (by decide) (by decide) (by decide), d2 _ (by decide) (by decide),
        c2 _ (by simp only [mY]; omega) (by simp only [mY]; omega) (by decide) (by decide),
        b3 _ (by decide) (by decide) (by decide), a2 _ (by decide) (by decide) (by decide)
        (by decide), i5]
    obtain ⟨g1, g2, hM6⟩ := stF_sem I s5 hM5 (p := mY) (p1 := mX1) (v := mV) (x := yb + 2 * x)
      (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) hY5 (by simp only [regs]; omega) (by omega) (by omega)
    have z6 := size_sem I (stF mY mX1 mV) s5
    generalize semXIR I (stF mY mX1 mV) s5 = s6 at g1 g2 hM6 z6
    -- the pointers
    rw [semXIR_seq]
    have hX6 : rd s6.M mX = toWord (xb + 2 * x) := by
      rw [g2 _ (by simp only [mX]; omega) (by simp only [mX]; omega) (by decide) (by decide),
        f3 _ (by decide) (by decide) (by decide), d2 _ (by decide) (by decide),
        c2 _ (by simp only [mX]; omega) (by simp only [mX]; omega) (by decide) (by decide), hX2]
    have hY6 : rd s6.M mY = toWord (yb + 2 * x) := by
      rw [g2 _ (by simp only [mY]; omega) (by simp only [mY]; omega) (by decide) (by decide), hY5]
    obtain ⟨k1, k2, k3, hM7⟩ := stepXY_sem I s6 hM6 hX6 hY6
    have z7 := size_sem I (.blk [.const mK 2, .op .add mX mX mK, .op .add mY mY mK]) s6
    have estep : (.blk stepXY : XIR) = .blk [.const mK 2, .op .add mX mX mK, .op .add mY mY mK] :=
      rfl
    rw [estep]
    generalize semXIR I (.blk [.const mK 2, .op .add mX mX mK, .op .add mY mY mK]) s6 = s7
      at k1 k2 k3 hM7 z7
    have hJ7 : rd s7.M mJ = toWord x := by
      rw [k3 _ (by decide) (by decide) (by decide),
        g2 _ (by simp only [mJ]; omega) (by simp only [mJ]; omega) (by decide) (by decide),
        f3 _ (by decide) (by decide) (by decide), d2 _ (by decide) (by decide),
        c2 _ (by simp only [mJ]; omega) (by simp only [mJ]; omega) (by decide) (by decide),
        b3 _ (by decide) (by decide) (by decide), a2 _ (by decide) (by decide) (by decide)
        (by decide), i3]
    have e8 : semXIR I (.blk [.op .add mJ mJ cOne]) s7 = ⟨runPrims [.op .add mJ mJ cOne] s7.M, s7.o⟩ :=
      rfl
    rw [e8]
    obtain ⟨n1, n2⟩ := incr_sem s7.M hM7 (r := mJ) (by decide) (by decide) hJ7
    have hd : ∀ i, i ≠ mC → rd (decS mC ⟨runPrims [.op .add mJ mJ cOne] s7.M, s7.o⟩).M i =
        rd (runPrims [.op .add mJ mJ cOne] s7.M) i := fun i h => rd_decS (Ne.symm h) _
    -- the heap
    have h8 : ∀ i, regs ≤ i → i ≠ xb + 2 * x → i ≠ xb + 2 * x + 1 → i ≠ yb + 2 * x →
        i ≠ yb + 2 * x + 1 → rd (runPrims [.op .add mJ mJ cOne] s7.M) i = rd s'.M i :=
      fun i hi j1 j2 j3 j4 => by
        simp only [regs] at hi
        rw [n2 _ (by simp only [mJ]; omega),
          k3 i (by simp only [mK]; omega) (by simp only [mX]; omega) (by simp only [mY]; omega),
          g2 i j3 j4 (by simp only [mX1]; omega) (by simp only [cTmp]; omega),
          f3 i (by simp only [mV]; omega) (by simp only [mV]; omega) (by simp only [mS1]; omega),
          d2 i (by simp only [mK]; omega) (by simp only [mS]; omega),
          c2 i j1 j2 (by simp only [mX1]; omega) (by simp only [cTmp]; omega),
          b3 i (by simp only [mV]; omega) (by simp only [mV]; omega) (by simp only [mS1]; omega),
          h1 i (by simp only [regs]; omega)]
    have hcell : ∀ i, regs ≤ i → (i < xb ∨ xb + 16 * k ≤ i) → (i < yb ∨ yb + 16 * k ≤ i) →
        rd s'.M i = rd s.M i := fun i hi j1 j2 =>
      i7 i hi (j1.imp_right fun h => by omega) (j2.imp_right fun h => by omega)
    have hX8 : rdF (runPrims [.op .add mJ mJ cOne] s7.M) (xb + 2 * x) =
        rdF s.M (ob + 4 * k * (x % 8) + 2 * (x / 8)) := by
      have e1 : rdF (runPrims [.op .add mJ mJ cOne] s7.M) (xb + 2 * x) = rdF s3.M (xb + 2 * x) := by
        refine rdF_eq ?_ ?_
        · rw [n2 _ (by simp only [mJ]; omega), k3 _ (by simp only [mK]; omega)
            (by simp only [mX]; omega) (by simp only [mY]; omega),
            g2 _ (by omega) (by omega) (by simp only [mX1]; omega) (by simp only [cTmp]; omega),
            f3 _ (by simp only [mV]; omega) (by simp only [mV]; omega) (by simp only [mS1]; omega),
            d2 _ (by simp only [mK]; omega) (by simp only [mS]; omega)]
        · rw [n2 _ (by simp only [mJ]; omega), k3 _ (by simp only [mK]; omega)
            (by simp only [mX]; omega) (by simp only [mY]; omega),
            g2 _ (by omega) (by omega) (by simp only [mX1]; omega) (by simp only [cTmp]; omega),
            f3 _ (by simp only [mV]; omega) (by simp only [mV]; omega) (by simp only [mS1]; omega),
            d2 _ (by simp only [mK]; omega) (by simp only [mS]; omega)]
      rw [e1, c1, b1, ← ha]
      exact rdF_eq ((h1 _ (by simp only [regs]; omega)).trans
          (hcell _ (by simp only [regs]; omega) (by omega) (by omega)))
        ((h1 _ (by simp only [regs]; omega)).trans
          (hcell _ (by simp only [regs]; omega) (by omega) (by omega)))
    have hY8 : rdF (runPrims [.op .add mJ mJ cOne] s7.M) (yb + 2 * x) =
        rdF s.M (ob + 4 * k * (x % 8) + 2 * (x / 8) + 2 * k) := by
      have e1 : rdF (runPrims [.op .add mJ mJ cOne] s7.M) (yb + 2 * x) = rdF s6.M (yb + 2 * x) := by
        refine rdF_eq ?_ ?_
        · rw [n2 _ (by simp only [mJ]; omega), k3 _ (by simp only [mK]; omega)
            (by simp only [mX]; omega) (by simp only [mY]; omega)]
        · rw [n2 _ (by simp only [mJ]; omega), k3 _ (by simp only [mK]; omega)
            (by simp only [mX]; omega) (by simp only [mY]; omega)]
      have e2 : ∀ i, regs ≤ i → i ≠ xb + 2 * x → i ≠ xb + 2 * x + 1 → rd s4.M i = rd s'.M i :=
        fun i hi j1 j2 => by
          simp only [regs] at hi
          rw [d2 i (by simp only [mK]; omega) (by simp only [mS]; omega),
            c2 i j1 j2 (by simp only [mX1]; omega) (by simp only [cTmp]; omega),
            b3 i (by simp only [mV]; omega) (by simp only [mV]; omega) (by simp only [mS1]; omega),
            h1 i (by simp only [regs]; omega)]
      rw [e1, g1, f1, ← ha]
      exact rdF_eq ((e2 _ (by simp only [regs]; omega) (by omega) (by omega)).trans
          (hcell _ (by simp only [regs]; omega) (by omega) (by omega)))
        ((e2 _ (by simp only [regs]; omega) (by omega) (by omega)).trans
          (hcell _ (by simp only [regs]; omega) (by omega) (by omega)))
    refine ⟨inv_decS (inv_runPrims (by simp [Prim.dst, mJ]) hM7) (by decide),
      by rw [size_decS, size_runPrims, z7, z6, z5, z4, z3, z2, z1, i2], ?_, ?_, ?_,
      fun v hv => ?_, fun i hi hi2 hi3 => ?_⟩
    · rw [hd _ (by decide), n1]
    · rw [hd _ (by decide), n2 _ (by decide), k1]; exact congrArg toWord (by ring)
    · rw [hd _ (by decide), n2 _ (by decide), k2]; exact congrArg toWord (by ring)
    · rcases Nat.lt_succ_iff_lt_or_eq.mp hv with h | rfl
      · have g := i6 v h
        constructor
        · rw [← g.1]
          exact rdF_eq ((hd _ (by simp only [mC]; omega)).trans
            (h8 _ (by simp only [regs]; omega) (by omega) (by omega) (by omega) (by omega)))
            ((hd _ (by simp only [mC]; omega)).trans
            (h8 _ (by simp only [regs]; omega) (by omega) (by omega) (by omega) (by omega)))
        · rw [← g.2]
          exact rdF_eq ((hd _ (by simp only [mC]; omega)).trans
            (h8 _ (by simp only [regs]; omega) (by omega) (by omega) (by omega) (by omega)))
            ((hd _ (by simp only [mC]; omega)).trans
            (h8 _ (by simp only [regs]; omega) (by omega) (by omega) (by omega) (by omega)))
      · exact ⟨(rdF_eq (hd _ (by simp only [mC]; omega)) (hd _ (by simp only [mC]; omega))).trans hX8,
          (rdF_eq (hd _ (by simp only [mC]; omega)) (hd _ (by simp only [mC]; omega))).trans hY8⟩
    · simp only [regs] at hi
      rw [hd _ (by simp only [mC]; omega), h8 i (by simp only [regs]; omega) (by omega) (by omega)
        (by omega) (by omega), i7 i (by simp only [regs]; omega) (hi2.imp_right fun h => by omega)
        (hi3.imp_right fun h => by omega)]
  have := loopK_run I (gBody k ob) P ⟨M0, s.o⟩ hM0 (by decide) (by decide) (by decide) rN hk p0 step
  exact ⟨this.2.2.2.2.2.1, fun i hi h2 h3 => this.2.2.2.2.2.2 i hi
    (h2.imp_right fun h => by omega) (h3.imp_right fun h => by omega), this.1⟩

/-- **The rows of the next level's message** (levels 0–3): both rows of `2^n` entries zeroed,
then the `8k` K elements gathered from the decoded rows at `ob`. -/
def msgHIR (n k ob xb yb : ℕ) : XIR :=
  .seq (zeroIR (2 * 2 ^ n) xb) (.seq (zeroIR (2 * 2 ^ n) yb) (gathIR k ob xb yb))

theorem wf_msgHIR (n k ob xb yb : ℕ) : WF (msgHIR n k ob xb yb) :=
  ⟨wf_zeroIR _ _, wf_zeroIR _ _, wf_gathIR _ _ _ _⟩

theorem noLoopT_msgHIR (n k ob xb yb : ℕ) : NoLoopT (msgHIR n k ob xb yb) :=
  ⟨noLoopT_zeroIR _ _, noLoopT_zeroIR _ _, noLoopT_gathIR _ _ _ _⟩

theorem outs_msgHIR (n k ob xb yb t : ℕ) : outs (msgHIR n k ob xb yb) t = 0 := by
  simp only [msgHIR, outs, outs_zeroIR, outs_gathIR]

theorem cost_msgHIR (n k ob xb yb t : ℕ) (hn : 2 * 2 ^ n < 2 ^ 64) (hk : 8 * k < 2 ^ 64) :
    cost (msgHIR n k ob xb yb) t = 46 + 36 * 2 ^ n + 560 * k := by
  simp only [msgHIR, cost, cost_zeroIR _ _ _ hn, cost_gathIR _ _ _ _ _ hk]; ring

theorem msgHIR_sem (I : Array Word) (s : St) (hM : Inv s.M) {n k ob xb yb : ℕ} (hn : n ≤ 20)
    (hk : 8 * k ≤ 2 ^ n) (hob : regs ≤ ob) (hob2 : ob + 32 * k < 2 ^ 64)
    (hxb : regs ≤ xb) (hyb : regs ≤ yb)
    (hxb2 : xb + 2 * 2 ^ n < 2 ^ 64) (hyb2 : yb + 2 * 2 ^ n < 2 ^ 64)
    (hxs : xb + 2 * 2 ^ n ≤ s.M.size) (hys : yb + 2 * 2 ^ n ≤ s.M.size)
    (hd : xb + 2 * 2 ^ n ≤ yb ∨ yb + 2 * 2 ^ n ≤ xb) (hdx : ob + 32 * k ≤ xb ∨ xb + 2 * 2 ^ n ≤ ob)
    (hdy : ob + 32 * k ≤ yb ∨ yb + 2 * 2 ^ n ≤ ob) :
    (∀ j < 2 ^ n, rdF (semXIR I (msgHIR n k ob xb yb) s).M (xb + 2 * j) =
        (if j < 8 * k then rdF s.M (ob + 4 * k * (j % 8) + 2 * (j / 8)) else 0) ∧
      rdF (semXIR I (msgHIR n k ob xb yb) s).M (yb + 2 * j) =
        (if j < 8 * k then rdF s.M (ob + 4 * k * (j % 8) + 2 * (j / 8) + 2 * k) else 0)) ∧
    (∀ i, regs ≤ i → (i < xb ∨ xb + 2 * 2 ^ n ≤ i) → (i < yb ∨ yb + 2 * 2 ^ n ≤ i) →
      rd (semXIR I (msgHIR n k ob xb yb) s).M i = rd s.M i) ∧
    Inv (semXIR I (msgHIR n k ob xb yb) s).M := by
  have hP : 2 ^ n ≤ 2 ^ 20 := Nat.pow_le_pow_right (by norm_num) hn
  have hs := hM.1
  simp only [regs] at hs hxb hyb hob
  rw [msgHIR, semXIR_seq]
  obtain ⟨a1, a2, hM1⟩ := zeroIR_sem I s hM (n := 2 * 2 ^ n) (b := xb) (by omega)
    (by simp only [regs]; omega) hxb2 hxs
  have z1 := size_sem I (zeroIR (2 * 2 ^ n) xb) s
  generalize semXIR I (zeroIR (2 * 2 ^ n) xb) s = s1 at a1 a2 hM1 z1
  rw [semXIR_seq]
  obtain ⟨b1, b2, hM2⟩ := zeroIR_sem I s1 hM1 (n := 2 * 2 ^ n) (b := yb) (by omega)
    (by simp only [regs]; omega) hyb2 (by omega)
  have z2 := size_sem I (zeroIR (2 * 2 ^ n) yb) s1
  generalize semXIR I (zeroIR (2 * 2 ^ n) yb) s1 = s2 at b1 b2 hM2 z2
  have h2 : ∀ i, regs ≤ i → (i < xb ∨ xb + 2 * 2 ^ n ≤ i) → (i < yb ∨ yb + 2 * 2 ^ n ≤ i) →
      rd s2.M i = rd s.M i := fun i hi h1 h2 => by rw [b2 i hi h2, a2 i hi h1]
  obtain ⟨c1, c2, hM3⟩ := gathIR_sem I s2 hM2 (k := k) (ob := ob) (xb := xb) (yb := yb) (by omega)
    (by simp only [regs]; omega) hob2 (by simp only [regs]; omega) (by omega)
    (by simp only [regs]; omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
  have hsrc : ∀ j < 8 * k, ob + 4 * k * (j % 8) + 2 * (j / 8) + 2 * k + 2 ≤ ob + 32 * k := by
    intro j hj
    have hm8 : 4 * k * (j % 8) ≤ 4 * k * 7 := Nat.mul_le_mul_left _ (by omega)
    have hd8 : j / 8 < k := (Nat.div_lt_iff_lt_mul (by norm_num)).2 (by omega)
    omega
  refine ⟨fun j hj => ?_, fun i hi hi2 hi3 => ?_, hM3⟩
  · by_cases hjk : j < 8 * k
    · rw [if_pos hjk, if_pos hjk, (c1 j hjk).1, (c1 j hjk).2]
      have := hsrc j hjk
      constructor
      · exact rdF_eq (h2 _ (by simp only [regs]; omega) (by omega) (by omega))
          (h2 _ (by simp only [regs]; omega) (by omega) (by omega))
      · exact rdF_eq (h2 _ (by simp only [regs]; omega) (by omega) (by omega))
          (h2 _ (by simp only [regs]; omega) (by omega) (by omega))
    · rw [if_neg hjk, if_neg hjk]
      have hx : rdF s2.M (xb + 2 * j) = 0 := rdF_zero_of
        ((b2 _ (by simp only [regs]; omega) (by omega)).trans (a1 _ (by omega)))
        ((b2 _ (by simp only [regs]; omega) (by omega)).trans
          (by rw [show xb + 2 * j + 1 = xb + (2 * j + 1) by omega]; exact a1 _ (by omega)))
      have hy : rdF s2.M (yb + 2 * j) = 0 := rdF_zero_of (b1 _ (by omega))
        (by rw [show yb + 2 * j + 1 = yb + (2 * j + 1) by omega]; exact b1 _ (by omega))
      constructor
      · rw [← hx]
        exact rdF_eq (c2 _ (by simp only [regs]; omega) (by omega) (by omega))
          (c2 _ (by simp only [regs]; omega) (by omega) (by omega))
      · rw [← hy]
        exact rdF_eq (c2 _ (by simp only [regs]; omega) (by omega) (by omega))
          (c2 _ (by simp only [regs]; omega) (by omega) (by omega))
  · rw [c2 i hi (hi2.imp_right fun h => by omega) (hi3.imp_right fun h => by omega), h2 i hi hi2 hi3]

/-! ## The rows are the next message's coordinates -/

open FR.Snd

theorem nextMsg_four (L es : Log) (x : ℕ) : nextMsg .N30 L es 4 x = finalAt es x := by
  rw [nextMsg, if_neg (by decide)]

/-- **Level 4's rows** (`msgTIR 10 32 finW`): with the chain link `finalAt es x = finPi π x`
(C.4's absorb is π's final field), entry `j < 2^10` of `X` (`Y`) is `(nextMsg 4 j).f₀` (`.f₁`)
for `j < 2^mLog = 32`, and `0` above: the input of `fwdIR_enc`. -/
theorem msg4_next (c : Digest) (π : Proof) (L es : Log) (hs : π.size = piSize)
    (hfin : ∀ x < 32, finalAt es x = finPi π x) (s : St) (hM : Inv s.M) {xb yb : ℕ}
    (hxb : regs ≤ xb) (hyb : regs ≤ yb) (hxb2 : xb + 2 * 2 ^ 10 < 2 ^ 64)
    (hyb2 : yb + 2 * 2 ^ 10 < 2 ^ 64) (hxs : xb + 2 * 2 ^ 10 ≤ s.M.size)
    (hys : yb + 2 * 2 ^ 10 ≤ s.M.size) (hd : xb + 2 * 2 ^ 10 ≤ yb ∨ yb + 2 * 2 ^ 10 ≤ xb) :
    ∀ j < 2 ^ 10,
      rdF (semXIR (tp c π L) (msgTIR 10 32 finW xb yb) s).M (xb + 2 * j) =
        (if j < 2 ^ mLog .N30 4 then (nextMsg .N30 L es 4 j).f₀ else 0) ∧
      rdF (semXIR (tp c π L) (msgTIR 10 32 finW xb yb) s).M (yb + 2 * j) =
        (if j < 2 ^ mLog .N30 4 then (nextMsg .N30 L es 4 j).f₁ else 0) := by
  intro j hj
  have hm : 2 ^ mLog .N30 4 = 32 := by decide
  obtain ⟨h1, h2⟩ := (msgTIR_sem (tp c π L) s hM (n := 10) (k := 32) (tw := finW) (xb := xb)
    (yb := yb) (by norm_num) (by norm_num) (by simp only [finW, finOff]; norm_num) hxb hyb hxb2 hyb2
    hxs hys hd).1 j hj
  rw [h1, h2, hm]
  by_cases hj32 : j < 32
  · rw [if_pos hj32, if_pos hj32, if_pos hj32, if_pos hj32, nextMsg_four, hfin j hj32,
      ← tapeF_fin c π L hs (x := j) (by omega)]
    exact ⟨rfl, rfl⟩
  · rw [if_neg hj32, if_neg hj32, if_neg hj32, if_neg hj32]
    exact ⟨rfl, rfl⟩

/-- **The rows of levels 0–3** (`msgHIR`): if level `i + 1`'s decoded row `r` sits at
`ob + 2kr` (`k = 2^mLog (i + 1)`) as the `F` values of `msgOf (i + 1) r`, entry `j < 2^n` of `X`
(`Y`) is `(nextMsg i j).f₀` (`.f₁`) for `j < 8k = 2^mLog i`, and `0` above. -/
theorem msgH_next {L es : Log} {i : ℕ} (hi : i < 4) (I : Array Word) (s : St) (hM : Inv s.M)
    {ob xb yb : ℕ}
    (hdec : ∀ r < 16, ∀ x < 2 ^ mLog .N30 (i + 1),
      algebraMap F K (rdF s.M (ob + 2 * 2 ^ mLog .N30 (i + 1) * r + 2 * x)) =
        msgOf .N30 L es (i + 1) r x)
    (hF : ∀ r x, msgOf .N30 L es (i + 1) r x = algebraMap F K (msgOf .N30 L es (i + 1) r x).f₀)
    (hob : regs ≤ ob) (hob2 : ob + 32 * 2 ^ mLog .N30 (i + 1) < 2 ^ 64)
    (hxb : regs ≤ xb) (hyb : regs ≤ yb)
    (hxb2 : xb + 2 * 2 ^ (lvl .N30 i).logN < 2 ^ 64) (hyb2 : yb + 2 * 2 ^ (lvl .N30 i).logN < 2 ^ 64)
    (hxs : xb + 2 * 2 ^ (lvl .N30 i).logN ≤ s.M.size) (hys : yb + 2 * 2 ^ (lvl .N30 i).logN ≤ s.M.size)
    (hd : xb + 2 * 2 ^ (lvl .N30 i).logN ≤ yb ∨ yb + 2 * 2 ^ (lvl .N30 i).logN ≤ xb)
    (hdx : ob + 32 * 2 ^ mLog .N30 (i + 1) ≤ xb ∨ xb + 2 * 2 ^ (lvl .N30 i).logN ≤ ob)
    (hdy : ob + 32 * 2 ^ mLog .N30 (i + 1) ≤ yb ∨ yb + 2 * 2 ^ (lvl .N30 i).logN ≤ ob) :
    ∀ j < 2 ^ (lvl .N30 i).logN,
      rdF (semXIR I (msgHIR (lvl .N30 i).logN (2 ^ mLog .N30 (i + 1)) ob xb yb) s).M (xb + 2 * j) =
        (if j < 2 ^ mLog .N30 i then (nextMsg .N30 L es i j).f₀ else 0) ∧
      rdF (semXIR I (msgHIR (lvl .N30 i).logN (2 ^ mLog .N30 (i + 1)) ob xb yb) s).M (yb + 2 * j) =
        (if j < 2 ^ mLog .N30 i then (nextMsg .N30 L es i j).f₁ else 0) := by
  intro j hj
  have hm : 2 ^ mLog .N30 i = 8 * 2 ^ mLog .N30 (i + 1) := by interval_cases i <;> decide
  have hn : (lvl .N30 i).logN ≤ 20 := by interval_cases i <;> decide
  have hk : 8 * 2 ^ mLog .N30 (i + 1) ≤ 2 ^ (lvl .N30 i).logN := by interval_cases i <;> decide
  obtain ⟨h1, h2⟩ := (msgHIR_sem I s hM (k := 2 ^ mLog .N30 (i + 1)) hn hk hob hob2 hxb hyb hxb2
    hyb2 hxs hys hd hdx hdy).1 j hj
  rw [h1, h2, hm]
  by_cases hjk : j < 8 * 2 ^ mLog .N30 (i + 1)
  · rw [if_pos hjk, if_pos hjk, if_pos hjk, if_pos hjk,
      nextMsg_coords (by simp only [nLevels]; omega) hF]
    have hd8 : j / 8 < 2 ^ mLog .N30 (i + 1) := (Nat.div_lt_iff_lt_mul (by norm_num)).2 (by omega)
    have r0 := hdec (2 * (j % 8)) (by omega) (j / 8) hd8
    have r1 := hdec (2 * (j % 8) + 1) (by omega) (j / 8) hd8
    constructor
    · show _ = (msgOf .N30 L es (i + 1) (2 * (j % 8)) (j / 8)).f₀
      rw [← r0]
      show _ = rdF s.M (ob + 2 * 2 ^ mLog .N30 (i + 1) * (2 * (j % 8)) + 2 * (j / 8))
      congr 1; ring
    · show _ = (msgOf .N30 L es (i + 1) (2 * (j % 8) + 1) (j / 8)).f₀
      rw [← r1]
      show _ = rdF s.M (ob + 2 * 2 ^ mLog .N30 (i + 1) * (2 * (j % 8) + 1) + 2 * (j / 8))
      congr 1; ring
  · rw [if_neg hjk, if_neg hjk, if_neg hjk, if_neg hjk]
    exact ⟨rfl, rfl⟩

end FR.X

end G6_FRXMsg
