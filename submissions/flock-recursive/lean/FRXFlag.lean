-- New for `flock-recursive` (BLUEPRINT §6.2 step 4, the K-folds and the agreement set; stage
-- S-H2, track L-ext).
import FRXEqT

/-!
# The column folds and the agreement flags on the machine

Level `i`'s agreement flag at position `j` tests `j ∈ consSet` in `F` coordinates
(`FRXLevel.mem_consSet_iff`):

`Σ_r W[r][j]·E[r].f_c = Enc(f⁽ⁱ⁺¹⁾.f_c)[j]` for `c = 0, 1`.

* the word `W[r][j]` sits at `cb + cs·j + 2r` (`readLv_spec_F`; level 0: `colBase`, `cs = 128`);
* the `eq` table `E[r]` (K) at `eb + 4r` (`eqtIR_sem`): `f₀` at `eb + 4r`, `f₁` at `eb + 4r + 2`;
* the encodings `Enc₀[j]`, `Enc₁[j]` at `xb + 2j` and `yb + 2j` (`fwdIR_enc`).

The program `flagIR n R cs cb eb xb yb fb` (next part) writes the flag word `[both equal]` at `fb + j` for `j < n`, the
input of `scanIR`.

* **`fBody_sem`**: one row's two products (delivered);
* still to come (S-H2 Part 17): the row loop, the comparison and store of one position (`fEnt`),
  and `flagIR` with `flagIR_sem` (the flags, the heap outside `[fb, fb + n)` kept).

Registers `190 … 213` (the chain's, free after the replay; the `eq` table's are not live here).
-/

namespace FR.X

open RecursionFast FR Finset

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
  have hM1 := inv_sem I (P := ldF fw gW gA1) (by simp [ldF, WF, Prim.dst, fw, gA1]) hM
  generalize semXIR I (ldF fw gW gA1) s = s1 at u1 u3 hM1
  -- `E.f₀`
  rw [semXIR_seq]
  obtain ⟨v1, -, v3⟩ := ldF_sem I s1 hM1 (d := fe) (p := gE) (p1 := gA1) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide)
    ((u3 _ (by decide) (by decide) (by decide)).trans hE) (by simp only [regs]; omega) (by omega)
  have hM2 := inv_sem I (P := ldF fe gE gA1) (by simp [ldF, WF, Prim.dst, fe, gA1]) hM1
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
  have hM6 := inv_sem I (P := ldF fe gT gA1) (by simp [ldF, WF, Prim.dst, fe, gA1]) hM5
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

end FR.X
