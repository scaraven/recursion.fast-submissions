-- New for lvm2 roll 11 (M′, R11-X): the level-0 decoder program `decMP0IR N nL kL lo C` computes
-- `decodeG0 N nL kL lo C`. Adapted from `LvmXDecIR2.lean` (`DecLay`), `LvmXCopy.lean` (`msgRow_sem`, `rowsIR_sem`),
-- `LvmXDecIR3.lean` (`decTail_sem`), `LvmXDecIR4.lean` (`decIR_sem`) and this slice's `LvmMPXDec1Sem` (`enc1MC_sem`,
-- `enc1MIR_sem`): `2^15` positions → `2^nL`, `2^13` coefficients → `2^kL`, 64 decoded rows → the window `[lo, lo + C)`.
import LvmMPXDec1Sem

/-!
# The level-0 decoder on the machine, generic in the shape

**`decMP0IR_sem`**: on a memory holding the word `wd` at `wB + 64 q + t` (`q < 2^nL`), `α_i` at `aB + 3i` (`i < 6`)
and `f(v)` at `fB + 3v` (`rdE`), with the layout `DecM0Lay`:

* the cell `okM dB` holds `[2^kL ≤ |agreeG nL kL wd α f|]`, i.e. `decodeG0 N nL kL lo C wd α f ≠ none`;
* if `decodeG0 N nL kL lo C wd α f = some out`, the `C·2^kL` cells at `mM` hold `out`;
* the heap outside the workspace is kept.

`decMP0IRW_sem`: M′'s level 0 (`decodeMP0`, lanes 40–47); `decMP0Lay_example`: a layout below `2^26`.
-/

namespace Lvm.X

open RecursionFast Finset Lvm.Nb CompPoly.Extension BF64

attribute [local irreducible] entryK storeM

/-- **The level-0 decoder's memory layout** at `(N, nL, kL, lo, C)`: the workspace `[dB, dB + wsM nL kL C)`; the
word (`wB`, `64·2^nL` words, plus the interpolation's overreach of `64` words), `α` (`aB`, 18 words) and `f` (`fB`,
`3·2^kL`) outside it; addresses below `2^60`. -/
structure DecM0Lay (N nL kL lo C dB wB aB fB sz : ℕ) : Prop where
  hN : N ≤ 64
  hN1 : 1 ≤ N
  hkn : kL ≤ nL
  hnN : nL ≤ N
  hlo : lo + C ≤ 64
  r : regs ≤ dB
  t : dB + wsM nL kL C < 2 ^ 60
  z : dB + wsM nL kL C ≤ sz
  rW : regs ≤ wB
  tW : wB + 64 * 2 ^ nL + 64 < 2 ^ 60
  dW : wB + 64 * 2 ^ nL + 64 ≤ dB ∨ dB + wsM nL kL C ≤ wB
  rA : regs ≤ aB
  tA : aB + 18 < 2 ^ 60
  dA : aB + 18 ≤ dB ∨ dB + wsM nL kL C ≤ aB
  rF : regs ≤ fB
  tF : fB + 3 * 2 ^ kL < 2 ^ 60
  dF : fB + 3 * 2 ^ kL ≤ dB ∨ dB + wsM nL kL C ≤ fB

/-- The arithmetic facts of the layout, as linear facts on the atoms `2^kL`, `2^nL`, `C·2^kL`. -/
theorem DecM0Lay.facts {N nL kL lo C dB wB aB fB sz : ℕ} (hL : DecM0Lay N nL kL lo C dB wB aB fB sz) :
    0 < 2 ^ kL ∧ 2 ^ kL ≤ 2 ^ nL ∧ 2 ^ (kL + 1) = 2 * 2 ^ kL ∧ C * 2 ^ kL ≤ 64 * 2 ^ kL ∧
      N * N ≤ 2 ^ 12 ∧ kL < 61 ∧ nL < 61 ∧ wsM nL kL C = 2 ^ 13 + 2 * 2 ^ kL + 5 * 2 ^ nL + 2 * (C * 2 ^ kL) := by
  have h1 := hL.hN
  have hkn := hL.hkn
  have hk := Nat.pow_le_pow_right (show 0 < 2 by norm_num) hL.hkn
  have hNN : N * N ≤ 64 * 64 := Nat.mul_le_mul h1 h1
  have hn : nL < 61 := by
    have := hL.tW
    by_contra h
    have : 2 ^ 61 ≤ 2 ^ nL := Nat.pow_le_pow_right (by norm_num) (by omega)
    omega
  refine ⟨by positivity, hk, by ring, Nat.mul_le_mul_right _ (by have := hL.hlo; omega), by omega, by omega,
    hn, ?_⟩
  rw [wsM, pow_succ]; ring

/-! ## `Enc(f)` (the programs are `LvmMPXDec1Sem`'s with the level-0 layout) -/

/-- **One coordinate of `Enc(f)`** at `encM + c·2^nL`. -/
theorem encMC_sem (I : Array Word) (s : St) (hM : Inv s.M) {N nL kL lo C dB wB aB fB c : ℕ}
    (hL : DecM0Lay N nL kL lo C dB wB aB fB s.M.size) (hc : c < 3) (hT : TabOkN N s.M dB) :
    (∀ j < 2 ^ nL, rdK (semXIR I (encMC N nL kL dB fB c) s).M (encM nL kL dB + c * 2 ^ nL + j) =
      encN ptK (fun x : Fin (2 ^ kL) => rdK s.M (fB + 3 * x + c)) j) ∧
    (∀ x, regs ≤ x → (x < encM nL kL dB + c * 2 ^ nL ∨ encM nL kL dB + c * 2 ^ nL + 2 ^ nL ≤ x) →
      rd (semXIR I (encMC N nL kL dB fB c) s).M x = rd s.M x) ∧
    Inv (semXIR I (encMC N nL kL dB fB c) s).M := by
  obtain ⟨k0, hkn', e1, hCK, hNN, hk61, hn61, hws⟩ := hL.facts
  obtain ⟨hN, hN1, hkn, hnN, hlo, r, t, z, rW, tW, dW, rA, tA, dA, rF, tF, dF⟩ := hL
  have hs := hM.1
  simp only [regs] at r rW rA rF hs
  have hc2 : c * 2 ^ nL + 2 ^ nL ≤ 3 * 2 ^ nL := by
    rw [← Nat.succ_mul]; exact Nat.mul_le_mul_right _ (by omega)
  set A := encM nL kL dB + c * 2 ^ nL with hA
  have hAd : dB + 2 ^ 12 ≤ A ∧ A + 2 ^ nL ≤ dB + wsM nL kL C := by
    simp only [hA, encM, agM]; constructor <;> omega
  rw [encMC, tbM, semXIR_seq]
  obtain ⟨m1, m2, hM1⟩ := mcpIR_sem I s hM (n := 2 ^ kL) (src := fB + c) (str := 3) (dst := A)
    (pow_lt64 (by omega)) (by omega) (by norm_num) (by simp only [regs]; omega) (by omega) (by omega)
    (fun i hi => by omega) (fun i hi => by simp only [regs]; omega)
  have z1 := size_sem I (mcpIR (2 ^ kL) (fB + c) 3 A) s
  generalize semXIR I (mcpIR (2 ^ kL) (fB + c) 3 A) s = s1 at m1 m2 hM1 z1
  rw [semXIR_seq]
  obtain ⟨n1, n2, hM2⟩ := zeroIR_sem I s1 hM1 (n := 2 ^ nL - 2 ^ kL) (dst := A + 2 ^ kL)
    (by omega) (by simp only [regs]; omega) (by omega) (by omega)
  have z2 := size_sem I (zeroIR (2 ^ nL - 2 ^ kL) (A + 2 ^ kL)) s1
  generalize semXIR I (zeroIR (2 ^ nL - 2 ^ kL) (A + 2 ^ kL)) s1 = s2 at n1 n2 hM2 z2
  rw [semXIR_seq]
  have a3 : rd (semXIR I (.blk [.const rA0 (toWord A)]) s2).M rA0 = toWord A := by
    rw [sem_blk']; simp only [runPrims, List.foldl, Prim.run]
    rw [rd_set_self (by simp only [rA0]; omega)]
  have k3 : ∀ x, regs ≤ x → rd (semXIR I (.blk [.const rA0 (toWord A)]) s2).M x = rd s2.M x :=
    fun x hx => rd_blk_of_not_dst I _ s2 (by simp [Prim.dst, rA0]; simp only [regs] at hx; omega)
  have hM3 := inv_sem I (P := .blk [.const rA0 (toWord A)]) (by simp +decide [WF, Prim.dst, rA0]) hM2
  have z3 := size_sem I (.blk [.const rA0 (toWord A)]) s2
  generalize semXIR I (.blk [.const rA0 (toWord A)]) s2 = s3 at a3 k3 hM3 z3
  have h3 : ∀ x, regs ≤ x → (x < A ∨ A + 2 ^ nL ≤ x) → rd s3.M x = rd s.M x := fun x hx hx2 => by
    rw [k3 x hx, n2 x hx (by omega), m2 x hx (by omega)]
  have hT3 : TabOkN N s3.M dB := tabOkN_congr hT fun x h1 h2 => h3 x (by simp only [regs] at *; omega)
    (by omega)
  have hY : ∀ i < 2 ^ nL, rdK s3.M (A + i) =
      if h : i < 2 ^ kL then (fun x : Fin (2 ^ kL) => rdK s.M (fB + 3 * x + c)) ⟨i, h⟩ else 0 := by
    intro i hi
    simp only [rdK]
    rw [k3 _ (by simp only [regs]; omega)]
    by_cases h : i < 2 ^ kL
    · rw [dif_pos h, n2 _ (by simp only [regs]; omega) (by omega), m1 i h]
      congr 2; ring
    · rw [dif_neg h, show A + i = A + 2 ^ kL + (i - 2 ^ kL) by omega, n1 _ (by omega)]; rfl
  have hfe := fwdNIR_enc I s3 hM3 hN (A := A) (tb := dB) (ℓ := nL) (m := kL) hnN hkn
    (by simp only [regs]; omega) (by omega) (by omega) (by simp only [regs]; omega)
    (by omega) (by omega) a3 hT3 (fun x : Fin (2 ^ kL) => rdK s.M (fB + 3 * x + c)) hY
  obtain ⟨-, f2, f3⟩ := fwdNIR_sem I s3 hM3 hN (A := A) (tb := dB) (ℓ := nL)
    (Y := fun i => rdK s3.M (A + i)) hnN (by simp only [regs]; omega) (by omega) (by omega)
    (by simp only [regs]; omega) (by omega) (by omega) a3 hT3 (fun i _ => rfl)
  exact ⟨hfe, fun x hx hx2 => (f2 x hx hx2).trans (h3 x hx hx2), f3⟩

/-- **`Enc(f)`'s three coordinates** at `encM + c·2^nL + j`. -/
theorem encMIR_sem (I : Array Word) (s : St) (hM : Inv s.M) {N nL kL lo C dB wB aB fB : ℕ}
    (hL : DecM0Lay N nL kL lo C dB wB aB fB s.M.size) (hT : TabOkN N s.M dB) :
    (∀ c < 3, ∀ j < 2 ^ nL, rdK (semXIR I (encMIR N nL kL dB fB) s).M (encM nL kL dB + c * 2 ^ nL + j) =
      encN ptK (fun x : Fin (2 ^ kL) => rdK s.M (fB + 3 * x + c)) j) ∧
    (∀ x, regs ≤ x → (x < encM nL kL dB ∨ encM nL kL dB + 3 * 2 ^ nL ≤ x) →
      rd (semXIR I (encMIR N nL kL dB fB) s).M x = rd s.M x) ∧
    Inv (semXIR I (encMIR N nL kL dB fB) s).M := by
  have hL' := hL
  obtain ⟨k0, hkn', e1, hCK, hNN, hk61, hn61, hws⟩ := hL.facts
  obtain ⟨hN, hN1, hkn, hnN, hlo, r, t, z, rW, tW, dW, rA, tA, dA, rF, tF, dF⟩ := hL'
  simp only [regs] at r rF
  rw [encMIR, semXIR_seq]
  obtain ⟨a1, a2, hM1⟩ := encMC_sem I s hM hL (c := 0) (by norm_num) hT
  have z1 := size_sem I (encMC N nL kL dB fB 0) s
  generalize semXIR I (encMC N nL kL dB fB 0) s = s1 at a1 a2 hM1 z1
  have hL1 : DecM0Lay N nL kL lo C dB wB aB fB s1.M.size := by rw [z1]; exact hL
  have hF1 : ∀ x, regs ≤ x → (x < encM nL kL dB ∨ encM nL kL dB + 2 ^ nL ≤ x) → rd s1.M x = rd s.M x :=
    fun x hx hx2 => a2 x hx (by simpa using hx2)
  have hT1 : TabOkN N s1.M dB := tabOkN_congr hT fun x h1 h2 =>
    hF1 x (by simp only [regs] at *; omega) (by simp only [encM, agM] at *; omega)
  rw [semXIR_seq]
  obtain ⟨b1, b2, hM2⟩ := encMC_sem I s1 hM1 hL1 (c := 1) (by norm_num) hT1
  have z2 := size_sem I (encMC N nL kL dB fB 1) s1
  generalize semXIR I (encMC N nL kL dB fB 1) s1 = s2 at b1 b2 hM2 z2
  have hL2 : DecM0Lay N nL kL lo C dB wB aB fB s2.M.size := by rw [z2]; exact hL1
  have hT2 : TabOkN N s2.M dB := tabOkN_congr hT1 fun x h1 h2 =>
    b2 x (by simp only [regs] at *; omega) (by simp only [encM, agM] at *; omega)
  obtain ⟨c1, c2, hM3⟩ := encMC_sem I s2 hM2 hL2 (c := 2) (by norm_num) hT2
  have hfB : ∀ x c, x < 2 ^ kL → c < 3 → regs ≤ fB + 3 * x + c ∧
      (fB + 3 * x + c < encM nL kL dB ∨ encM nL kL dB + 3 * 2 ^ nL ≤ fB + 3 * x + c) := fun x c hx hc => by
    simp only [regs, encM, agM] at *; omega
  have ee1 : ∀ x : Fin (2 ^ kL), ∀ c < 3, rdK s1.M (fB + 3 * x + c) = rdK s.M (fB + 3 * x + c) :=
    fun x c hc => by
      obtain ⟨h1, h2⟩ := hfB x c x.isLt hc
      simp only [rdK]; rw [a2 _ h1 (by omega)]
  have ee2 : ∀ x : Fin (2 ^ kL), ∀ c < 3, rdK s2.M (fB + 3 * x + c) = rdK s.M (fB + 3 * x + c) :=
    fun x c hc => by
      obtain ⟨h1, h2⟩ := hfB x c x.isLt hc
      simp only [rdK]; rw [b2 _ h1 (by omega)]; exact ee1 x c hc
  refine ⟨fun c hc j hj => ?_, fun x hx hx2 => ?_, hM3⟩
  · interval_cases c
    · simp only [rdK]
      rw [c2 _ (by simp only [regs, encM, agM] at *; omega) (by simp only [encM, agM] at *; omega),
        b2 _ (by simp only [regs, encM, agM] at *; omega) (by simp only [encM, agM] at *; omega)]
      exact a1 j hj
    · simp only [rdK]
      rw [c2 _ (by simp only [regs, encM, agM] at *; omega) (by simp only [encM, agM] at *; omega)]
      rw [show wK (rd s2.M (encM nL kL dB + 1 * 2 ^ nL + j)) = rdK s2.M (encM nL kL dB + 1 * 2 ^ nL + j)
        from rfl, b1 j hj]
      congr 1; funext x; exact ee1 x 1 (by norm_num)
    · rw [c1 j hj]
      congr 1; funext x; exact ee2 x 2 (by norm_num)
  · rw [c2 x hx (by omega), b2 x hx (by omega), a2 x hx (by omega)]

/-! ## The reorder -/

/-- **One message row** `l < C`: `mB + l·2^kL + v := oB + (C − 1 − l)·2^kL + v`, `yL := l + 1`. -/
theorem msgRowM_sem (I : Array Word) (s : St) (hM : Inv s.M) {kL C oB mB l : ℕ} (hk : kL < 64) (hC : C < 2 ^ 64) (hl : l < C)
    (hoB : regs ≤ oB) (hoB2 : oB + C * 2 ^ kL < 2 ^ 64) (hmB : regs ≤ mB) (hmB2 : mB + C * 2 ^ kL < 2 ^ 64)
    (hms : mB + C * 2 ^ kL ≤ s.M.size) (hdisj : oB + C * 2 ^ kL ≤ mB ∨ mB + C * 2 ^ kL ≤ oB)
    (hL : rd s.M yL = toWord l) :
    (∀ v < 2 ^ kL, rd (semXIR I (msgRowM kL C oB mB) s).M (mB + l * 2 ^ kL + v) =
      rd s.M (oB + (C - 1 - l) * 2 ^ kL + v)) ∧
    rd (semXIR I (msgRowM kL C oB mB) s).M yL = toWord (l + 1) ∧
    (∀ r, regs ≤ r → (r < mB + l * 2 ^ kL ∨ mB + l * 2 ^ kL + 2 ^ kL ≤ r) →
      rd (semXIR I (msgRowM kL C oB mB) s).M r = rd s.M r) ∧
    Inv (semXIR I (msgRowM kL C oB mB) s).M := by
  have hs := hM.1
  simp only [regs] at hs hoB hmB
  have hK0 : 0 < 2 ^ kL := by positivity
  have hl2 : l * 2 ^ kL + 2 ^ kL ≤ C * 2 ^ kL := by
    rw [← Nat.succ_mul]; exact Nat.mul_le_mul_right _ hl
  have hl3 : (C - 1 - l) * 2 ^ kL + 2 ^ kL ≤ C * 2 ^ kL := by
    rw [← Nat.succ_mul]; exact Nat.mul_le_mul_right _ (by omega)
  rw [msgRowM, semXIR_seq]
  set ps : List Prim := [.const yK (toWord (C - 1)), .op .sub ySr yK yL, .const yK (toWord (2 ^ kL)),
    .op .mul ySr ySr yK, .const yK (toWord oB), .op .add ySr ySr yK, .const yK (toWord (2 ^ kL)),
    .op .mul yDs yL yK, .const yK (toWord mB), .op .add yDs yDs yK, .const yStr 1] with hps
  have w0 : WF (.blk ps) := by simp +decide [hps, WF, Prim.dst, yK, ySr, yDs, yStr]
  have hM0 := inv_sem I w0 hM
  have z0 := size_sem I (.blk ps) s
  have r0 : rd (semXIR I (.blk ps) s).M ySr = toWord (oB + (C - 1 - l) * 2 ^ kL) ∧
      rd (semXIR I (.blk ps) s).M yDs = toWord (mB + l * 2 ^ kL) ∧
      rd (semXIR I (.blk ps) s).M yStr = toWord 1 ∧ rd (semXIR I (.blk ps) s).M yL = toWord l := by
    rw [sem_blk', hps]; simp only [runPrims, List.foldl, Prim.run]
    refine ⟨?_, ?_, ?_, ?_⟩ <;>
    simp (disch := first | decide | (simp only [size_set, yK, ySr, yDs, yStr, yL]; omega)) only [rd_set_self, rd_set_ne]
    · rw [hL, sub_toWord (by omega) (by omega),
        mul_toWord, add_toWord, Nat.add_comm]
    · rw [hL, mul_toWord, add_toWord, Nat.add_comm]
    · rfl
    · exact hL
  have k0 : ∀ r, regs ≤ r → rd (semXIR I (.blk ps) s).M r = rd s.M r := fun r hr => by
    simp only [regs] at hr
    refine rd_blk_of_not_dst I _ s ?_
    simp only [hps, List.mem_cons, List.mem_nil_iff, or_false]
    rintro p (rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl) <;>
      simp only [Prim.dst, yK, ySr, yDs, yStr] <;> omega
  generalize semXIR I (.blk ps) s = s0 at hM0 z0 r0 k0
  obtain ⟨p1, p2, p3, p4⟩ := r0
  rw [semXIR_seq]
  obtain ⟨m1, m2, hM1⟩ := mcpLoop_sem I s0 hM0 (n := 2 ^ kL) (src := oB + (C - 1 - l) * 2 ^ kL)
    (str := 1) (dst := mB + l * 2 ^ kL) (pow_lt64 hk) (by omega) (by simp only [regs]; omega)
    (by omega) (by omega) (fun i hi => by omega) (fun i hi => by simp only [regs]; omega) p1 p2 p3
  have z1 := size_sem I (mcpLoop (2 ^ kL)) s0
  have l1 : rd (semXIR I (mcpLoop (2 ^ kL)) s0).M yL = toWord l := by
    rw [frame I _ s0 (by simp +decide [mcpLoop, mcpBody, WF, Writes, Prim.dst, ySr, yDs, yV, yN,
      yC, cTmp, regs]) hM0 yL (by decide) (by simp +decide [mcpLoop, mcpBody, Writes, Prim.dst,
        ySr, yDs, yV, yN, yC, yL, cTmp]), p4]
  generalize semXIR I (mcpLoop (2 ^ kL)) s0 = s1 at m1 m2 hM1 z1 l1
  have b2 : ∀ r, r ≠ yL → rd (semXIR I (.blk [.op .add yL yL cOne]) s1).M r = rd s1.M r :=
    fun r hr => rd_blk_of_not_dst I _ s1 (by simp [Prim.dst]; exact Ne.symm hr)
  have hx : ∀ x, regs ≤ x → x ≠ yL := fun x hx => by simp only [regs, yL] at *; omega
  refine ⟨fun v hv => ?_, ?_, fun r hr hr2 => ?_, inv_sem I (P := .blk [.op .add yL yL cOne])
    (by simp +decide [WF, Prim.dst, yL]) hM1⟩
  · rw [b2 _ (hx _ (by simp only [regs]; omega)), m1 v hv, Nat.one_mul,
      k0 _ (by simp only [regs]; omega)]
  · have hs1 := hM1.1
    simp only [regs] at hs1
    rw [sem_blk']; simp only [runPrims, List.foldl, Prim.run]
    rw [rd_set_self (by simp only [yL]; omega), l1, show rd s1.M cOne = 1 from hM1.2 0 (by decide),
      add_one_toWord]
  · rw [b2 _ (hx r hr), m2 r (keepC_of_regs hr) hr2, k0 r hr]

/-- **The message reorder**: row `l < C` of the message at `mB + l·2^kL` is row `C − 1 − l` at
`oB`; the heap outside `[mB, mB + 2^19)` is kept. -/
theorem rowsMIR_sem (I : Array Word) (s : St) (hM : Inv s.M) {kL C oB mB : ℕ} (hk : kL < 64) (hC : C < 2 ^ 64)
    (hoB : regs ≤ oB) (hoB2 : oB + C * 2 ^ kL < 2 ^ 64) (hmB : regs ≤ mB) (hmB2 : mB + C * 2 ^ kL < 2 ^ 64)
    (hms : mB + C * 2 ^ kL ≤ s.M.size) (hdisj : oB + C * 2 ^ kL ≤ mB ∨ mB + C * 2 ^ kL ≤ oB) :
    (∀ l < C, ∀ v < 2 ^ kL, rd (semXIR I (rowsMIR kL C oB mB) s).M (mB + l * 2 ^ kL + v) =
      rd s.M (oB + (C - 1 - l) * 2 ^ kL + v)) ∧
    (∀ r, regs ≤ r → (r < mB ∨ mB + C * 2 ^ kL ≤ r) → rd (semXIR I (rowsMIR kL C oB mB) s).M r = rd s.M r) ∧
    Inv (semXIR I (rowsMIR kL C oB mB) s).M := by
  have hs := hM.1
  have hK0 : 0 < 2 ^ kL := by positivity
  simp only [regs] at hs hoB hmB
  rw [rowsMIR, semXIR_seq]
  have w0 : WF (.blk [.const yL 0, .const yN2 (toWord C)]) := by simp +decide [WF, Prim.dst, yL, yN2]
  have hM0 := inv_sem I w0 hM
  have z0 := size_sem I (.blk [.const yL 0, .const yN2 (toWord C)]) s
  have r0 : rd (semXIR I (.blk [.const yL 0, .const yN2 (toWord C)]) s).M yL = toWord 0 ∧
      rd (semXIR I (.blk [.const yL 0, .const yN2 (toWord C)]) s).M yN2 = toWord C := by
    rw [sem_blk']; simp only [runPrims, List.foldl, Prim.run]
    refine ⟨?_, ?_⟩ <;>
    simp (disch := first | decide | (simp only [size_set, yL, yN2]; omega)) only [rd_set_self, rd_set_ne] <;> rfl
  have k0 : ∀ r, regs ≤ r → rd (semXIR I (.blk [.const yL 0, .const yN2 (toWord C)]) s).M r = rd s.M r :=
    fun r hr => by
      simp only [regs] at hr
      refine rd_blk_of_not_dst I _ s ?_
      simp only [List.mem_cons, List.mem_nil_iff, or_false]
      rintro p (rfl | rfl) <;> simp only [Prim.dst, yL, yN2] <;> omega
  generalize semXIR I (.blk [.const yL 0, .const yN2 (toWord C)]) s = s0 at hM0 z0 r0 k0
  obtain ⟨l0, n0⟩ := r0
  let P : ℕ → St → Prop := fun j s' => Inv s'.M ∧ s'.M.size = s.M.size ∧ rd s'.M yL = toWord j ∧
    (∀ l < j, ∀ v < 2 ^ kL, rd s'.M (mB + l * 2 ^ kL + v) = rd s.M (oB + (C - 1 - l) * 2 ^ kL + v)) ∧
    (∀ r, regs ≤ r → (r < mB ∨ mB + j * 2 ^ kL ≤ r) → rd s'.M r = rd s.M r)
  have hE : ∀ i, i ≠ yC2 → i ≠ cTmp → rd (entryK yC2 yN2 (toWord C) s0.M) i = rd s0.M i :=
    fun i h1 h2 => entryK_frame _ (Ne.symm h1) (Ne.symm h2)
  have h0 : P 0 ⟨entryK yC2 yN2 (toWord C) s0.M, s0.o⟩ := by
    refine ⟨inv_entryK hM0 (by decide), by simp only [size_entryK, z0], ?_,
      fun l hl => absurd hl (by omega), fun r hr _ => ?_⟩ <;> dsimp only
    · rw [hE _ (by decide) (by decide), l0]
    · simp only [regs] at hr
      rw [hE _ (by simp only [yC2]; omega) (by simp only [cTmp]; omega), k0 r (by simp only [regs]; omega)]
  have hstep : ∀ j s', j < C → P j s' → P (j + 1) (decS yC2 (semXIR I (msgRowM kL C oB mB) s')) := by
    rintro j s' hj ⟨i1, i2, i3, i4, i5⟩
    obtain ⟨b1, b2, b3, hM'⟩ := msgRowM_sem I s' i1 (oB := oB) (mB := mB) hk hC hj
      (by simp only [regs]; omega) hoB2 (by simp only [regs]; omega) hmB2 (by omega) hdisj i3
    have hd : ∀ x, x ≠ yC2 → rd (decS yC2 (semXIR I (msgRowM kL C oB mB) s')).M x =
        rd (semXIR I (msgRowM kL C oB mB) s').M x := fun x hx => rd_decS (Ne.symm hx) _
    have hx : ∀ x, regs ≤ x → x ≠ yC2 := fun x hx => by simp only [regs, yC2] at *; omega
    refine ⟨inv_decS hM' (by decide), by rw [size_decS, size_sem, i2], by rw [hd _ (by decide), b2],
      fun l hl v hv => ?_, fun r hr hr2 => ?_⟩
    · rw [hd _ (hx _ (by simp only [regs]; omega))]
      by_cases hlj : l = j
      · subst hlj
        have h1 := Nat.mul_le_mul_right (2 ^ kL) (show C - 1 - l + 1 ≤ C by omega)
        have h2 := Nat.mul_le_mul_right (2 ^ kL) (show l ≤ C by omega)
        rw [Nat.succ_mul] at h1
        rw [b1 v hv, i5 _ (by simp only [regs]; omega) (by omega)]
      · rw [b3 _ (by simp only [regs]; omega) (by
          rcases Nat.lt_or_gt_of_ne hlj with h | h
          · left
            have := Nat.mul_le_mul_right (2 ^ kL) (show l + 1 ≤ j by omega)
            rw [Nat.succ_mul] at this; omega
          · right
            have := Nat.mul_le_mul_right (2 ^ kL) (show j + 1 ≤ l by omega)
            rw [Nat.succ_mul] at this; omega), i4 l (by omega) v hv]
    · have e : (j + 1) * 2 ^ kL = j * 2 ^ kL + 2 ^ kL := Nat.succ_mul _ _
      rw [e] at hr2
      rw [hd _ (hx r hr), b3 r hr (by omega), i5 r hr (by omega)]
  have hfin := loopK_run I (msgRowM kL C oB mB) P s0 hM0 (c := yC2) (n := yN2) (K := C) (by decide)
    (by decide) (by decide) n0 hC h0 hstep
  exact ⟨hfin.2.2.2.1, fun r hr hr2 => hfin.2.2.2.2 r hr (by omega), hfin.1⟩

/-! ## The decoding proper -/

/-- **The decoding proper**: on a list of `≥ 2^kL` agreeing positions at `agM`, the window's words at `mM`
(`decWordG` of the window's stack words `lo·2^kL + i`). -/
theorem decMP0Tail_sem (I : Array Word) (s : St) (hM : Inv s.M) {N nL kL lo C dB wB aB fB : ℕ}
    (hL : DecM0Lay N nL kL lo C dB wB aB fB s.M.size) (hT : TabOkN N s.M dB) (wd : ℕ → ℕ → BF64)
    (α f : ℕ → Ext3) (hW : ∀ q < 2 ^ nL, ∀ t < 64, rdK s.M (wB + 64 * q + t) = wd q t)
    (hlen : 2 ^ kL ≤ (agreeG nL kL wd α f).length)
    (hJ : ∀ t < 2 ^ kL, rd s.M (agM kL dB + t) = toWord ((agreeG nL kL wd α f).getD t 0)) :
    (∀ i < C * 2 ^ kL, rdK (semXIR I (decMP0Tail N nL kL lo C dB wB) s).M (mM nL kL C dB + i) =
      decWordG N nL kL wd α f (lo * 2 ^ kL + i)) ∧
    (∀ x, regs ≤ x → (x < wbM dB ∨ dB + wsM nL kL C ≤ x) →
      rd (semXIR I (decMP0Tail N nL kL lo C dB wB) s).M x = rd s.M x) ∧
    Inv (semXIR I (decMP0Tail N nL kL lo C dB wB) s).M := by
  have hL' := hL
  obtain ⟨k0, hkn', e1, hCK, hNN, hk61, hn61, hws⟩ := hL.facts
  have n0 : 0 < 2 ^ nL := by positivity
  obtain ⟨hN, hN1, hkn, hnN, hlo, r, t, z, rW, tW, dW, rA, tA, dA, rF, tF, dF⟩ := hL'
  simp only [regs] at r rW
  have hkC : 2 ^ kL * C = C * 2 ^ kL := Nat.mul_comm _ _
  set Jl := (agreeG nL kL wd α f).take (2 ^ kL) with hJl
  have hJlen : Jl.length = 2 ^ kL := by
    rw [hJl, List.length_take, Nat.min_eq_left hlen]
  have hJnd : Jl.Nodup := (nodup_filter_range _ _).sublist (List.take_sublist _ _)
  have hJlt : ∀ j ∈ Jl, j < 2 ^ nL := fun j hj => by
    have := List.mem_of_mem_take hj
    rw [agreeG, List.mem_filter, List.mem_range] at this
    exact this.1
  have hBL : BaryLayP (2 ^ nL) (2 ^ kL) C (agM kL dB) (wbM dB) (ebM kL dB) (wB + (64 - lo - C)) 64
      (oM nL kL dB) s.M.size := by
    refine ⟨by omega, by omega, hkn', by omega, ?_, ?_, ?_, ?_, by simp only [regs]; omega, ?_, ?_, ?_, ?_,
      ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      (try simp only [regs, agM, wbM, ebM, oM, encM]) <;> omega
  have hget : ∀ t < 2 ^ kL, Jl.getD t 0 < 2 ^ nL := fun t ht => by
    rw [List.getD_eq_getElem _ _ (by omega)]
    exact hJlt _ (List.getElem_mem (l := Jl) (n := t) (by omega))
  rw [decMP0Tail, semXIR_seq]
  obtain ⟨b1, b2, hM1⟩ := baryIR_semP I s hM (Jl := Jl) hBL hget (fun t ht => by
    rw [hJ t ht, hJl, getD_take_lt ht])
  have z1 := size_sem I (baryIR (2 ^ kL) C (agM kL dB) (wbM dB) (ebM kL dB) (wB + (64 - lo - C)) 64
    (oM nL kL dB)) s
  generalize semXIR I (baryIR (2 ^ kL) C (agM kL dB) (wbM dB) (ebM kL dB) (wB + (64 - lo - C)) 64
    (oM nL kL dB)) s = s1 at b1 b2 hM1 z1
  have hT1 : TabOkN N s1.M dB := tabOkN_congr hT fun x h1 h2 => by
    exact b2 x (by simp only [regs]; omega) (by simp only [wbM]; omega)
      (by simp only [ebM]; omega) (by simp only [oM, encM, agM]; omega)
  rw [semXIR_seq]
  obtain ⟨c1, c2, hM2⟩ := bflyAllM_sem I s1 hM1 hN (kL := kL) (R := C) (tb := tbM dB) (ob := oM nL kL dB)
    (by omega) (by omega) (by simp only [regs, oM, encM, agM]; omega)
    (by simp only [oM, encM, agM]; omega) (by rw [z1]; simp only [oM, encM, agM]; omega)
    (by simp only [regs, tbM]; omega) (by simp only [tbM]; omega) (by simp only [tbM, oM, encM, agM]; omega) hT1
    (fun t i => rdK s1.M (oM nL kL dB + t * 2 ^ kL + i)) (fun _ _ _ _ => rfl)
  have z2 := size_sem I (bflyAllM N kL C (tbM dB) (oM nL kL dB)) s1
  generalize semXIR I (bflyAllM N kL C (tbM dB) (oM nL kL dB)) s1 = s2 at c1 c2 hM2 z2
  obtain ⟨d1, d2, hM3⟩ := rowsMIR_sem I s2 hM2 (kL := kL) (C := C) (oB := oM nL kL dB) (mB := mM nL kL C dB)
    (by omega) (by omega) (by simp only [regs, oM, encM, agM]; omega) (by simp only [oM, encM, agM]; omega)
    (by simp only [regs, mM, oM, encM, agM]; omega) (by simp only [mM, oM, encM, agM]; omega)
    (by rw [z2, z1]; simp only [mM, oM, encM, agM]; omega) (by simp only [mM]; omega)
  generalize semXIR I (rowsMIR kL C (oM nL kL dB) (mM nL kL C dB)) s2 = s3 at d1 d2 hM3
  refine ⟨fun i hi => ?_, fun x hx hx2 => ?_, hM3⟩
  · -- the window word `i = r·2^kL + v`: row `lo + r`, interpolated as output row `C − 1 − r`
    have hr : i / 2 ^ kL < C := by rw [Nat.div_lt_iff_lt_mul k0]; exact hi
    have hv : i % 2 ^ kL < 2 ^ kL := Nat.mod_lt _ k0
    have hdm := Nat.div_add_mod' i (2 ^ kL)
    have e1' : (lo * 2 ^ kL + i) / 2 ^ kL = lo + i / 2 ^ kL := by
      rw [Nat.add_comm, Nat.add_mul_div_right _ _ k0, Nat.add_comm]
    have e2' : (lo * 2 ^ kL + i) % 2 ^ kL = i % 2 ^ kL := by
      rw [Nat.add_comm, Nat.add_mul_mod_self_right]
    have hi' : mM nL kL C dB + i = mM nL kL C dB + i / 2 ^ kL * 2 ^ kL + i % 2 ^ kL := by omega
    rw [decWordG, e1', e2']
    generalize i / 2 ^ kL = rr at *
    generalize i % 2 ^ kL = v at *
    simp only [rdK]
    rw [hi', d1 rr hr v hv,
      show wK (rd s2.M (oM nL kL dB + (C - 1 - rr) * 2 ^ kL + v)) =
        rdK s2.M (oM nL kL dB + (C - 1 - rr) * 2 ^ kL + v) from rfl,
      c1 (C - 1 - rr) (by omega) v hv, ← hJl]
    refine coeffsAt_congr ptK N kL 0 _ _ (fun j hj => ?_) v hv
    rw [show oM nL kL dB + (C - 1 - rr) * 2 ^ kL + j = oM nL kL dB + 2 ^ kL * (C - 1 - rr) + j by ring,
      b1 j hj _ (by omega), show (2 : ℕ) ^ kL = Jl.length from hJlen.symm,
      baryValK_eqP (P := 2 ^ nL) (by omega) hJnd hJlt (by omega)]
    refine interpF_congr ptK _ (fun q hq => ?_) j
    have hq' := hJlt q (List.mem_toFinset.1 hq)
    rw [show wB + (64 - lo - C) + 64 * q + (C - 1 - rr) = wB + 64 * q + (63 - (lo + rr)) by omega,
      hW q hq' _ (by omega)]
    rfl
  · simp only [regs] at hx
    rw [d2 x (by simp only [regs]; omega) (by simp only [mM, oM, encM, agM, wbM] at *; omega),
      c2 x (by simp only [regs]; omega) (by simp only [oM, encM, agM, wbM] at *; omega),
      b2 x (by simp only [regs]; omega) (by simp only [wbM] at *; omega)
        (by simp only [ebM, wbM] at *; omega) (by simp only [oM, encM, agM, wbM] at *; omega)]

/-! ## The whole program -/

/-- **The level-0 decoder program computes `decodeG0 N nL kL lo C`.** -/
theorem decMP0IR_sem (I : Array Word) (s : St) (hM : Inv s.M) {N nL kL lo C dB wB aB fB : ℕ}
    (hL : DecM0Lay N nL kL lo C dB wB aB fB s.M.size) (wd : ℕ → ℕ → BF64) (α f : ℕ → Ext3)
    (hW : ∀ q < 2 ^ nL, ∀ t < 64, rdK s.M (wB + 64 * q + t) = wd q t)
    (hA : ∀ i < 6, rdE s.M (aB + 3 * i) = α i)
    (hF : ∀ v < 2 ^ kL, rdE s.M (fB + 3 * v) = f v) :
    rd (semXIR I (decMP0IR N nL kL lo C dB wB aB fB) s).M (okM dB) =
      bW (decide (2 ^ kL ≤ (agreeG nL kL wd α f).length)) ∧
    (∀ out, decodeG0 N nL kL lo C wd α f = some out →
      ∀ i < C * 2 ^ kL, rdK (semXIR I (decMP0IR N nL kL lo C dB wB aB fB) s).M (mM nL kL C dB + i) =
        out.getD i 0) ∧
    (∀ x, regs ≤ x → (x < dB ∨ dB + wsM nL kL C ≤ x) →
      rd (semXIR I (decMP0IR N nL kL lo C dB wB aB fB) s).M x = rd s.M x) ∧
    Inv (semXIR I (decMP0IR N nL kL lo C dB wB aB fB) s).M := by
  have hL' := hL
  obtain ⟨k0, hkn', e1, hCK, hNN, hk61, hn61, hws⟩ := hL.facts
  have n0 : 0 < 2 ^ nL := by positivity
  obtain ⟨hN, hN1, hkn, hnN, hlo, r, t, z, rW, tW, dW, rA, tA, dA, rF, tF, dF⟩ := hL'
  have hs := hM.1
  simp only [regs] at r rW rA rF hs
  -- 1. the basis table
  rw [decMP0IR, semXIR_seq]
  obtain ⟨w1, w2, hM1, z1⟩ := wtabNIR_sem I s hM hN hN1 (tb := tbM dB) (by simp only [regs, tbM]; omega)
    (by simp only [tbM]; omega) (by simp only [tbM]; omega)
  generalize semXIR I (wtabNIR N (tbM dB)) s = s1 at w1 w2 hM1 z1
  have hT1 : TabOkN N s1.M dB := w1
  -- 2. the `eq` table
  rw [semXIR_seq]
  obtain ⟨q1, q2, hM2⟩ := eqtIR_eqA I s1 hM1 (aB := aB) (qB := qM dB) (by simp only [regs]; omega)
    (by omega) (by simp only [regs, qM]; omega) (by simp only [qM]; omega)
    (by rw [z1]; simp only [qM]; omega) (by simp only [qM]; omega)
  have z2 := size_sem I (eqtIR 6 aB (qM dB)) s1
  generalize semXIR I (eqtIR 6 aB (qM dB)) s1 = s2 at q1 q2 hM2 z2
  have hT2 : TabOkN N s2.M dB := tabOkN_congr hT1 fun x h1 h2 => by
    exact q2 x (by simp only [regs]; omega) (by simp only [qM]; omega)
  have hQ2 : ∀ l < 64, rdE s2.M (qM dB + 3 * l) = eqA α l := fun l hl => by
    rw [q1 l hl]
    refine eqA_congr (fun i hi => ?_) l
    rw [← hA i hi]
    exact rdE_congr fun k hk => w2 _ (by simp only [regs]; omega) (by simp only [tbM]; omega)
  have hL2 : DecM0Lay N nL kL lo C dB wB aB fB s2.M.size := by rw [z2, z1]; exact hL
  -- 3. `Enc(f)`
  rw [semXIR_seq]
  obtain ⟨ee1, ee2, hM3⟩ := encMIR_sem I s2 hM2 hL2 hT2
  have z3 := size_sem I (encMIR N nL kL dB fB) s2
  generalize semXIR I (encMIR N nL kL dB fB) s2 = s3 at ee1 ee2 hM3 z3
  have hout : ∀ x, regs ≤ x → (x < dB ∨ dB + wsM nL kL C ≤ x) → rd s2.M x = rd s.M x := fun x hx hx2 => by
    rw [q2 x hx (by simp only [qM]; omega), w2 x hx (by simp only [tbM]; omega)]
  have hfB : ∀ v < 2 ^ kL, ∀ c < 3, rdK s2.M (fB + 3 * v + c) = rdK s.M (fB + 3 * v + c) :=
    fun v hv c hc => by simp only [rdK]; rw [hout _ (by simp only [regs]; omega) (by omega)]
  have hW3 : ∀ q < 2 ^ nL, ∀ t < 64, rdK s3.M (wB + 64 * q + t) = wd q t := fun q hq t ht => by
    have : 64 * q + t < 64 * 2 ^ nL := by omega
    rw [← hW q hq t ht]; simp only [rdK]
    rw [ee2 _ (by simp only [regs]; omega) (by simp only [encM, agM]; omega),
      hout _ (by simp only [regs]; omega) (by omega)]
  have hQ3 : ∀ l < 64, rdE s3.M (qM dB + 3 * l) = eqA α l := fun l hl => by
    rw [← hQ2 l hl]
    exact rdE_congr fun k hk => ee2 _ (by simp only [regs, qM]; omega)
      (by simp only [qM, encM, agM]; omega)
  have hE3 : ∀ q < 2 ^ nL, encG kL f q = mkE (rdK s3.M (encM nL kL dB + q))
      (rdK s3.M (encM nL kL dB + 2 ^ nL + q)) (rdK s3.M (encM nL kL dB + 2 * 2 ^ nL + q)) := by
    intro q hq
    rw [encG_coords kL f (fun c v => rdK s.M (fB + 3 * v + c)) (fun v hv => by rw [← hF v hv]; rfl) q]
    have hc : ∀ c < 3, encN ptK (fun x : Fin (2 ^ kL) => rdK s.M (fB + 3 * x + c)) q =
        rdK s3.M (encM nL kL dB + c * 2 ^ nL + q) := fun c hc => by
      rw [ee1 c hc q hq]
      exact congrArg (fun g => encN ptK g q) (funext fun x => (hfB x x.isLt c hc).symm)
    rw [hc 0 (by norm_num), hc 1 (by norm_num), hc 2 (by norm_num), Nat.zero_mul, Nat.add_zero,
      Nat.one_mul]
  have hAg : agreeNM s3.M (2 ^ nL) wB (qM dB) (encM nL kL dB) (2 ^ nL) = agreeG nL kL wd α f :=
    agreeNM_eq_agreeG wd α f hW3 hQ3 hE3
  -- 4. the agreement scan
  rw [semXIR_seq]
  obtain ⟨g1, g2, g3, hM4⟩ := agreeNIR_sem I s3 hM3 (st := 2 ^ nL) (wB := wB) (qB := qM dB)
    (eB := encM nL kL dB) (agB := agM kL dB) (by simp only [regs]; omega) (by omega)
    (by simp only [regs, qM]; omega) (by simp only [qM]; omega)
    (by simp only [regs, encM, agM]; omega) (by simp only [encM, agM]; omega)
    (by simp only [regs, agM]; omega) (by simp only [agM]; omega)
    (by rw [z3, z2, z1]; simp only [agM]; omega)
    ⟨by simp only [agM]; omega, by simp only [agM, qM]; omega, by simp only [agM, encM]; omega⟩
  rw [hAg] at g1 g2
  have z4 := size_sem I (agreeNIR (2 ^ nL) wB (qM dB) (encM nL kL dB) (agM kL dB)) s3
  generalize semXIR I (agreeNIR (2 ^ nL) wB (qM dB) (encM nL kL dB) (agM kL dB)) s3 = s4
    at g1 g2 g3 hM4 z4
  have hlenL : (agreeG nL kL wd α f).length ≤ 2 ^ nL := by
    rw [agreeG]; exact (List.length_filter_le _ _).trans (by simp)
  have hlen64 : (agreeG nL kL wd α f).length < 2 ^ 64 := by omega
  -- 5. the flag
  rw [semXIR_seq]
  obtain ⟨o1, o2, o3, hM5⟩ := okMIR_sem I s4 hM4 (kL := kL) (ok := okM dB)
    (n := (agreeG nL kL wd α f).length) (by omega) (by simp only [regs, okM]; omega)
    (by simp only [okM]; omega) (by rw [z4, z3, z2, z1]; simp only [okM]; omega) hlen64 g1
  have z5 := size_sem I (okMIR kL (okM dB)) s4
  generalize semXIR I (okMIR kL (okM dB)) s4 = s5 at o1 o2 o3 hM5 z5
  -- the heap of `s5`
  have hT5 : TabOkN N s5.M dB := tabOkN_congr hT2 fun x h1 h2 => by
    rw [o3 x (by simp only [regs]; omega) (by simp only [okM]; omega),
      g3 x (by simp only [regs]; omega) (by simp only [agM]; omega),
      ee2 x (by simp only [regs]; omega) (by simp only [encM, agM]; omega)]
  have h5 : ∀ x, regs ≤ x → (x < dB ∨ dB + wsM nL kL C ≤ x) → rd s5.M x = rd s.M x := fun x hx hx2 => by
    rw [o3 x hx (by simp only [okM]; omega), g3 x hx (by simp only [agM]; omega),
      ee2 x hx (by simp only [encM, agM]; omega), hout x hx hx2]
  -- 6. the branch
  rw [semXIR_ite, o1]
  by_cases hk : 2 ^ kL ≤ (agreeG nL kL wd α f).length
  · rw [decide_eq_true hk, if_neg bW_true_ne]
    have hL5 : DecM0Lay N nL kL lo C dB wB aB fB s5.M.size := by rw [z5, z4, z3, z2, z1]; exact hL
    have hW5 : ∀ q < 2 ^ nL, ∀ t < 64, rdK s5.M (wB + 64 * q + t) = wd q t := fun q hq t ht => by
      have : 64 * q + t < 64 * 2 ^ nL := by omega
      rw [← hW q hq t ht]; simp only [rdK]; rw [h5 _ (by simp only [regs]; omega) (by omega)]
    have hJ5 : ∀ t < 2 ^ kL, rd s5.M (agM kL dB + t) = toWord ((agreeG nL kL wd α f).getD t 0) :=
      fun t ht => by
        rw [o3 _ (by simp only [regs, agM]; omega) (by simp only [agM, okM]; omega), g2 t (by omega)]
    obtain ⟨d1, d2, hM6⟩ := decMP0Tail_sem I s5 hM5 hL5 hT5 wd α f hW5 hk hJ5
    refine ⟨?_, fun out hout' i hi => ?_, fun x hx hx2 => ?_, hM6⟩
    · rw [d2 _ (by simp only [regs, okM]; omega) (by simp only [okM, wbM]; omega), o2, decide_eq_true hk]
    · rw [decodeG0, if_pos hk, Option.some.injEq] at hout'
      rw [← hout', d1 i hi, List.getD_eq_getElem _ _ (by simpa using hi), List.getElem_map,
        List.getElem_range]
    · rw [d2 x hx (by simp only [wbM]; omega), h5 x hx hx2]
  · rw [decide_eq_false hk, if_pos bW_false_eq]
    have e6 : semXIR I (.blk []) s5 = s5 := by cases s5; rfl
    rw [e6]
    refine ⟨by rw [o2, decide_eq_false hk], fun out hout' => ?_, h5, hM5⟩
    rw [decodeG0, if_neg hk] at hout'
    exact absurd hout' (by simp)

/-! ## M′'s level 0 -/

/-- **M′'s level-0 decoder program computes `decodeMP0`** (`2^19` positions, `k = 2^17`, lanes 40–47): the
window's `8·2^17` words at `mM`. -/
theorem decMP0IRW_sem (I : Array Word) (s : St) (hM : Inv s.M) {dB wB aB fB : ℕ}
    (hL : DecM0Lay 19 19 17 40 8 dB wB aB fB s.M.size) (wd : ℕ → ℕ → BF64) (α f : ℕ → Ext3)
    (hW : ∀ q < 2 ^ 19, ∀ t < 64, rdK s.M (wB + 64 * q + t) = wd q t)
    (hA : ∀ i < 6, rdE s.M (aB + 3 * i) = α i)
    (hF : ∀ v < 2 ^ 17, rdE s.M (fB + 3 * v) = f v) :
    rd (semXIR I (decMP0IRW dB wB aB fB) s).M (okM dB) =
      bW (decide (2 ^ 17 ≤ (agreeG 19 17 wd α f).length)) ∧
    (∀ out, decodeMP0 wd α f = some out →
      ∀ i < 8 * 2 ^ 17, rdK (semXIR I (decMP0IRW dB wB aB fB) s).M (mM 19 17 8 dB + i) = out.getD i 0) ∧
    (∀ x, regs ≤ x → (x < dB ∨ dB + wsM 19 17 8 ≤ x) →
      rd (semXIR I (decMP0IRW dB wB aB fB) s).M x = rd s.M x) ∧
    Inv (semXIR I (decMP0IRW dB wB aB fB) s).M :=
  decMP0IR_sem I s hM hL wd α f hW hA hF

/-- **A level-0 layout exists** below `2^26` (non-vacuity): workspace at `2^23`, word at `2^24`, `α` at `2^20`, `f`
at `2^20 + 64`. -/
theorem decMP0Lay_example (sz : ℕ) (hsz : 2 ^ 26 ≤ sz) :
    DecM0Lay 19 19 17 40 8 (2 ^ 23) (2 ^ 24) (2 ^ 20) (2 ^ 20 + 64) sz := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    (try simp only [regs, wsM]) <;> norm_num <;> omega

end Lvm.X
