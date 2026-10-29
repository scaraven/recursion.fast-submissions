-- New for `flock-recursive` (BLUEPRINT §6.2 step 4, the K-folds and the agreement set; stage
-- S-H2, track L-ext).
import FRXEqT
import FRXBaryTop

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

/-! ## Controls (a kernel run on a toy memory) -/

namespace FlagControls

/-- Store the words `ws` at `256 …` (scratch registers `200`, `201`). -/
def putWords : List Word → ℕ → XIR
  | [], _ => .blk []
  | w :: ws, j => .seq (.blk [.const 200 (toWord (256 + j)), .const 201 w])
      (.seq (.store 200 201) (putWords ws (j + 1)))

/-- One row, two positions: `W[0][0] = W[0][1] = 1` at `256`, `E[0] = 1` at `260`, `X = (1, 0)`
at `264`, `Y = (0, 0)` at `268`; the flags at `272`, then output. -/
def toyFlag : XIR :=
  .seq (putWords [1, 0, 1, 0, 1, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0] 0)
    (.seq (flagIR 2 1 2 256 260 264 268 272)
      (.seq (.blk [.const 200 272]) (.seq (.load 201 200) (.seq (.out 201)
        (.seq (.blk [.const 200 273]) (.seq (.load 201 200) (.out 201)))))))

/-- **Positive and negative**: position `0` agrees (`1·1 = X[0]`, `1·0 = Y[0]`), position `1`
does not (`1·1 ≠ X[1] = 0`). -/
theorem toyFlag_run : (toProg 300 0 toyFlag).run [] 1400 = some [1, 0] := by
  decide +kernel

end FlagControls

end FR.X
