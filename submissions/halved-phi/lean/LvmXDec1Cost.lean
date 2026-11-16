-- lvm2 X-REC2 (helper DEC): the level-1 decoder's well-formedness, cost, a concrete layout and the
-- non-vacuity checks. Adapted from this entry's `LvmXDecCost.lean`.
import LvmXRead1Defs
import LvmXDecCost
import LvmXDec1Agree
import LvmXDecIR4

-- ===== merged from `LvmXDec1IR` (GOLF module merge: `LvmXDec1IR.lean` is now a stub importing `LvmXDec1Cost`) =====
section
-- lvm2 X-REC2 (helper DEC): the phases of `C_rec`'s level-1 decoder on the machine. Adapted from this
-- entry's `LvmXDecIR.lean`/`LvmXDecIR2.lean` (v1's `encC`, `bflyAll`, `okIR` and their semantics) at
-- `ℓ = 12`/`9` and 48 lanes, and `LvmXCopy.lean` (`msgRow`/`rowsIR`, as the transpose `tr1Row`/`tr1IR`).

/-!
# The level-1 decoder's phases

**Workspace** `[d1B, d1B + 2^16)`: basis table `tbB d1B = d1B` (225 words, v1's), `eq` table
`q1B = d1B + 256` (48), the flag `ok1B = d1B + 512`, the weights `wb1B = d1B + 2^10` and the `E`
row `eb1B = d1B + 2^11` (`2^9` each), the agreement list `ag1B = d1B + 2^12` (`2^12`), `Enc₁(f₂)`'s
coordinates `enc1B = d1B + 2^13` (`3·2^12`), the interpolated lanes `ob1B = d1B + 2^15`
(`48·2^9`). The inputs (word `w1B`, `α` at `a1B`, `f₂` at `f2B`) and the output `oB` lie outside.

* `enc1C c`: `f₂`'s coordinate `c` (`f2B + 3v + c`, `v < 2^9`) zero-padded to `2^12`, then the
  forward NTT (`fwdIR 12`): `enc1C_sem`, `Enc` over `K` of the coordinate at every position.
* `bfly1All`: the inverse NTT (`bflyIR 9`) on each of the 48 lanes at `ob1B` (`bfly1All_sem`).
* `ok1IR`: the flag `[2^9 ≤ |A|]` in `rOk` and at `ok1B`.
* `tr1IR ob oB`: the transpose `M[oB + 48 v + t] := M[ob + 2^9 t + v]` (`v < 2^9`, `t < 48`), so
  that `rdE (oB + 3 (u + 16 v))` is row `u`'s coefficient `v`.

Registers: v1's `rA0`, `rOk`, `zT`, `zK`, `zC`, `zN`, the copy's `64 … 73`.
-/

namespace Lvm.X

open RecursionFast Finset Lvm.Nb

attribute [local irreducible] entryK storeM

/-! ## Layout -/

/-- The `eq(α₁, ·)` table. -/ def q1B (dB : ℕ) : ℕ := dB + 256
/-- The success flag. -/ def ok1B (dB : ℕ) : ℕ := dB + 512
/-- The interpolation weights. -/ def wb1B (dB : ℕ) : ℕ := dB + 2 ^ 10
/-- The interpolation's `E` row. -/ def eb1B (dB : ℕ) : ℕ := dB + 2 ^ 11
/-- The agreement list. -/ def ag1B (dB : ℕ) : ℕ := dB + 2 ^ 12
/-- `Enc₁(f₂)`'s coordinates. -/ def enc1B (dB : ℕ) : ℕ := dB + 2 ^ 13
/-- The interpolated lanes (`2^9` each). -/ def ob1B (dB : ℕ) : ℕ := dB + 2 ^ 15

/-- **The level-1 decoder's memory layout**: the workspace `[d1B, d1B + 2^16)` inside the memory;
the word (`w1B`, read over `48·2^15` words by the interpolation's layout `BaryLay`), `α₁` (`a1B`,
12 words) and `f₂` (`f2B`, `3·2^9` words) outside it; the output (`oB`, `3·2^13` words) inside the
memory and outside the workspace; every address below `2^60`. -/
structure Dec1Lay (dB wB aB fB oB sz : ℕ) : Prop where
  r : regs ≤ dB
  t : dB + 2 ^ 16 < 2 ^ 60
  z : dB + 2 ^ 16 ≤ sz
  rW : regs ≤ wB
  tW : wB + 48 * 2 ^ 15 < 2 ^ 60
  dW : wB + 48 * 2 ^ 15 ≤ dB ∨ dB + 2 ^ 16 ≤ wB
  rA : regs ≤ aB
  tA : aB + 12 < 2 ^ 60
  dA : aB + 12 ≤ dB ∨ dB + 2 ^ 16 ≤ aB
  rF : regs ≤ fB
  tF : fB + 3 * 2 ^ 9 < 2 ^ 60
  dF : fB + 3 * 2 ^ 9 ≤ dB ∨ dB + 2 ^ 16 ≤ fB
  rO : regs ≤ oB
  tO : oB + 3 * 2 ^ 13 < 2 ^ 60
  zO : oB + 3 * 2 ^ 13 ≤ sz
  dO : oB + 3 * 2 ^ 13 ≤ dB ∨ dB + 2 ^ 16 ≤ oB

/-! ## The programs -/

/-- **`Enc₁(f₂)`'s coordinate `c`** at `enc1B + c·2^12`: copy, zero padding, forward NTT. -/
def enc1C (dB fB c : ℕ) : XIR :=
  .seq (mcpIR (2 ^ 9) (fB + c) 3 (enc1B dB + c * 2 ^ 12))
    (.seq (zeroIR (2 ^ 12 - 2 ^ 9) (enc1B dB + c * 2 ^ 12 + 2 ^ 9))
      (.seq (.blk [.const rA0 (toWord (enc1B dB + c * 2 ^ 12))]) (fwdIR 12 (tbB dB))))

/-- The three coordinates. -/
def enc1IR (dB fB : ℕ) : XIR := .seq (enc1C dB fB 0) (.seq (enc1C dB fB 1) (enc1C dB fB 2))

/-- One lane `t`: `rA0 := ob1B + t·2^9`, the inverse NTT, `t += 1`. -/
def bfly1Row (dB : ℕ) : XIR :=
  .seq (.blk [.const zK (toWord (2 ^ 9)), .op .mul rA0 zT zK, .const zK (toWord (ob1B dB)),
      .op .add rA0 rA0 zK]) (.seq (bflyIR 9 (tbB dB)) (.blk [.op .add zT zT cOne]))

/-- **The inverse NTT of the 48 lanes.** -/
def bfly1All (dB : ℕ) : XIR :=
  .seq (.blk [.const zT 0, .const zN 48]) (.loopK zC zN 48 (bfly1Row dB))

/-- **The flag** `rOk := [2^9 ≤ cnt]`, stored at `ok1B`. -/
def ok1IR (dB : ℕ) : XIR :=
  .seq (.blk [.const zK (toWord (2 ^ 9)), .op .ltu rOk gCnt zK, .op .xor rOk rOk cOne,
    .const zK (toWord (ok1B dB))]) (.store zK rOk)

/-- One transposed row `v` (`yL`): `M[oB + 48 v + t] := M[ob + v + 2^9 t]`, `t < 48`; `v += 1`. -/
def tr1Row (ob oB : ℕ) : XIR :=
  .seq (.blk [.const yK (toWord ob), .op .add ySr yL yK, .const yK 48, .op .mul yDs yL yK,
      .const yK (toWord oB), .op .add yDs yDs yK, .const yStr (toWord (2 ^ 9))])
    (.seq (mcpLoop 48) (.blk [.op .add yL yL cOne]))

/-- **The transpose** of the `48 × 2^9` lanes at `ob` into `2^9` rows of 48 words at `oB`. -/
def tr1IR (ob oB : ℕ) : XIR :=
  .seq (.blk [.const yL 0, .const yN2 (toWord (2 ^ 9))]) (.loopK yC2 yN2 (toWord (2 ^ 9)) (tr1Row ob oB))

/-- **The decoding proper** (on success): interpolation of the 48 lanes on the first `2^9`
listed positions, the inverse NTT per lane, the transpose into the output. -/
def dec1Tail (dB wB oB : ℕ) : XIR :=
  .seq (baryIR (2 ^ 9) 48 (ag1B dB) (wb1B dB) (eb1B dB) wB 48 (ob1B dB))
    (.seq (bfly1All dB) (tr1IR (ob1B dB) oB))

/-! ## Semantics of the phases -/

/-- **One coordinate of `Enc₁(f₂)`.** -/
theorem enc1C_sem (I : Array Word) (s : St) (hM : Inv s.M) {dB wB aB fB oB c : ℕ}
    (hL : Dec1Lay dB wB aB fB oB s.M.size) (hc : c < 3) (hT : TabOk s.M (tbB dB)) :
    (∀ j < 2 ^ 12, rdK (semXIR I (enc1C dB fB c) s).M (enc1B dB + c * 2 ^ 12 + j) =
      encN ptK (fun x : Fin (2 ^ 9) => rdK s.M (fB + 3 * x + c)) j) ∧
    (∀ x, regs ≤ x → (x < enc1B dB + c * 2 ^ 12 ∨ enc1B dB + c * 2 ^ 12 + 2 ^ 12 ≤ x) →
      rd (semXIR I (enc1C dB fB c) s).M x = rd s.M x) ∧
    Inv (semXIR I (enc1C dB fB c) s).M := by
  obtain ⟨r, t, z, rW, tW, dW, rA, tA, dA, rF, tF, dF, rO, tO, zO, dO⟩ := hL
  have hs := hM.1
  simp only [regs] at r rW rA rF hs
  set A := enc1B dB + c * 2 ^ 12 with hA
  have hAd : dB + 2 ^ 13 ≤ A ∧ A + 2 ^ 12 ≤ dB + 2 ^ 15 := by
    simp only [hA, enc1B]; constructor <;> omega
  rw [enc1C, semXIR_seq]
  obtain ⟨m1, m2, hM1⟩ := mcpIR_sem I s hM (n := 2 ^ 9) (src := fB + c) (str := 3) (dst := A)
    (by norm_num) (by omega) (by norm_num) (by simp only [regs]; omega) (by omega) (by omega)
    (fun i hi => by omega) (fun i hi => by simp only [regs]; omega)
  have z1 := size_sem I (mcpIR (2 ^ 9) (fB + c) 3 A) s
  generalize semXIR I (mcpIR (2 ^ 9) (fB + c) 3 A) s = s1 at m1 m2 hM1 z1
  rw [semXIR_seq]
  obtain ⟨n1, n2, hM2⟩ := zeroIR_sem I s1 hM1 (n := 2 ^ 12 - 2 ^ 9) (dst := A + 2 ^ 9)
    (by norm_num) (by simp only [regs]; omega) (by omega) (by omega)
  have z2 := size_sem I (zeroIR (2 ^ 12 - 2 ^ 9) (A + 2 ^ 9)) s1
  generalize semXIR I (zeroIR (2 ^ 12 - 2 ^ 9) (A + 2 ^ 9)) s1 = s2 at n1 n2 hM2 z2
  rw [semXIR_seq]
  have a3 : rd (semXIR I (.blk [.const rA0 (toWord A)]) s2).M rA0 = toWord A := by
    rw [sem_blk']; simp only [runPrims, List.foldl, Prim.run]
    rw [rd_set_self (by simp only [rA0]; omega)]
  have k3 : ∀ x, regs ≤ x → rd (semXIR I (.blk [.const rA0 (toWord A)]) s2).M x = rd s2.M x :=
    fun x hx => rd_blk_of_not_dst I _ s2 (by simp [Prim.dst, rA0]; simp only [regs] at hx; omega)
  have hM3 := inv_sem I (P := .blk [.const rA0 (toWord A)]) (by simp +decide [WF, Prim.dst, rA0]) hM2
  have z3 := size_sem I (.blk [.const rA0 (toWord A)]) s2
  generalize semXIR I (.blk [.const rA0 (toWord A)]) s2 = s3 at a3 k3 hM3 z3
  -- the heap of `s3`
  have h3 : ∀ x, regs ≤ x → (x < A ∨ A + 2 ^ 12 ≤ x) → rd s3.M x = rd s.M x := fun x hx hx2 => by
    rw [k3 x hx, n2 x hx (by omega), m2 x hx (by omega)]
  have hT3 : TabOk s3.M (tbB dB) := tabOk_congr hT fun x h1 h2 => h3 x (by simp only [regs, tbB] at *; omega)
    (by simp only [tbB] at *; omega)
  have hY : ∀ i < 2 ^ 12, rdK s3.M (A + i) =
      if h : i < 2 ^ 9 then (fun x : Fin (2 ^ 9) => rdK s.M (fB + 3 * x + c)) ⟨i, h⟩ else 0 := by
    intro i hi
    simp only [rdK]
    rw [k3 _ (by simp only [regs]; omega)]
    by_cases h : i < 2 ^ 9
    · rw [dif_pos h, n2 _ (by simp only [regs]; omega) (by omega), m1 i h]
      congr 2; ring
    · rw [dif_neg h, show A + i = A + 2 ^ 9 + (i - 2 ^ 9) by omega, n1 _ (by omega)]; rfl
  have hfe := fwdIR_enc I s3 hM3 (A := A) (tb := tbB dB) (ℓ := 12) (m := 9) (by decide) (by norm_num)
    (by simp only [regs]; omega) (by omega) (by omega) (by simp only [regs, tbB]; omega)
    (by simp only [tbB]; omega) (by simp only [tbB]; omega) a3 hT3
    (fun x : Fin (2 ^ 9) => rdK s.M (fB + 3 * x + c)) hY
  obtain ⟨-, f2, f3⟩ := fwdIR_sem I s3 hM3 (A := A) (tb := tbB dB) (ℓ := 12) (Y := fun i => rdK s3.M (A + i))
    (by decide) (by simp only [regs]; omega) (by omega) (by omega) (by simp only [regs, tbB]; omega)
    (by simp only [tbB]; omega) (by simp only [tbB]; omega) a3 hT3 (fun i _ => rfl)
  exact ⟨hfe, fun x hx hx2 => (f2 x hx hx2).trans (h3 x hx hx2), f3⟩

/-- **`Enc₁(f₂)`'s three coordinates** at `enc1B + c·2^12 + j`. -/
theorem enc1IR_sem (I : Array Word) (s : St) (hM : Inv s.M) {dB wB aB fB oB : ℕ}
    (hL : Dec1Lay dB wB aB fB oB s.M.size) (hT : TabOk s.M (tbB dB)) :
    (∀ c < 3, ∀ j < 2 ^ 12, rdK (semXIR I (enc1IR dB fB) s).M (enc1B dB + c * 2 ^ 12 + j) =
      encN ptK (fun x : Fin (2 ^ 9) => rdK s.M (fB + 3 * x + c)) j) ∧
    (∀ x, regs ≤ x → (x < enc1B dB ∨ enc1B dB + 3 * 2 ^ 12 ≤ x) →
      rd (semXIR I (enc1IR dB fB) s).M x = rd s.M x) ∧
    Inv (semXIR I (enc1IR dB fB) s).M := by
  have hL' := hL
  obtain ⟨r, t, z, rW, tW, dW, rA, tA, dA, rF, tF, dF, rO, tO, zO, dO⟩ := hL'
  simp only [regs] at r rF
  rw [enc1IR, semXIR_seq]
  obtain ⟨a1, a2, hM1⟩ := enc1C_sem I s hM hL (c := 0) (by norm_num) hT
  have z1 := size_sem I (enc1C dB fB 0) s
  generalize semXIR I (enc1C dB fB 0) s = s1 at a1 a2 hM1 z1
  have hL1 : Dec1Lay dB wB aB fB oB s1.M.size := by rw [z1]; exact hL
  have hF1 : ∀ x, regs ≤ x → (x < enc1B dB ∨ enc1B dB + 2 ^ 12 ≤ x) → rd s1.M x = rd s.M x :=
    fun x hx hx2 => a2 x hx (by simpa using hx2)
  have hT1 : TabOk s1.M (tbB dB) := tabOk_congr hT fun x h1 h2 =>
    hF1 x (by simp only [regs, tbB] at *; omega) (by simp only [tbB, enc1B] at *; omega)
  rw [semXIR_seq]
  obtain ⟨b1, b2, hM2⟩ := enc1C_sem I s1 hM1 hL1 (c := 1) (by norm_num) hT1
  have z2 := size_sem I (enc1C dB fB 1) s1
  generalize semXIR I (enc1C dB fB 1) s1 = s2 at b1 b2 hM2 z2
  have hL2 : Dec1Lay dB wB aB fB oB s2.M.size := by rw [z2]; exact hL1
  have hT2 : TabOk s2.M (tbB dB) := tabOk_congr hT1 fun x h1 h2 =>
    b2 x (by simp only [regs, tbB] at *; omega) (by simp only [tbB, enc1B] at *; omega)
  obtain ⟨c1, c2, hM3⟩ := enc1C_sem I s2 hM2 hL2 (c := 2) (by norm_num) hT2
  have hfB : ∀ x c, x < 2 ^ 9 → c < 3 → regs ≤ fB + 3 * x + c ∧
      (fB + 3 * x + c < enc1B dB ∨ enc1B dB + 3 * 2 ^ 12 ≤ fB + 3 * x + c) := fun x c hx hc => by
    simp only [regs, enc1B] at *; omega
  have e1 : ∀ x : Fin (2 ^ 9), ∀ c < 3, rdK s1.M (fB + 3 * x + c) = rdK s.M (fB + 3 * x + c) :=
    fun x c hc => by
      obtain ⟨h1, h2⟩ := hfB x c x.isLt hc
      simp only [rdK]; rw [a2 _ h1 (by omega)]
  have e2 : ∀ x : Fin (2 ^ 9), ∀ c < 3, rdK s2.M (fB + 3 * x + c) = rdK s.M (fB + 3 * x + c) :=
    fun x c hc => by
      obtain ⟨h1, h2⟩ := hfB x c x.isLt hc
      simp only [rdK]; rw [b2 _ h1 (by omega)]; exact e1 x c hc
  refine ⟨fun c hc j hj => ?_, fun x hx hx2 => ?_, hM3⟩
  · interval_cases c
    · simp only [rdK]
      rw [c2 _ (by simp only [regs, enc1B] at *; omega) (by simp only [enc1B] at *; omega),
        b2 _ (by simp only [regs, enc1B] at *; omega) (by simp only [enc1B] at *; omega)]
      exact a1 j hj
    · simp only [rdK]
      rw [c2 _ (by simp only [regs, enc1B] at *; omega) (by simp only [enc1B] at *; omega)]
      rw [show wK (rd s2.M (enc1B dB + 1 * 2 ^ 12 + j)) = rdK s2.M (enc1B dB + 1 * 2 ^ 12 + j) from rfl,
        b1 j hj]
      congr 1; funext x; exact e1 x 1 (by norm_num)
    · rw [c1 j hj]
      congr 1; funext x; exact e2 x 2 (by norm_num)
  · rw [c2 x hx (by omega), b2 x hx (by omega), a2 x hx (by omega)]

/-- **The inverse NTT of the 48 lanes** at `ob1B`. -/
theorem bfly1All_sem (I : Array Word) (s : St) (hM : Inv s.M) {dB wB aB fB oB : ℕ}
    (hL : Dec1Lay dB wB aB fB oB s.M.size) (hT : TabOk s.M (tbB dB)) (Y : ℕ → ℕ → BF64)
    (hY : ∀ t < 48, ∀ i < 2 ^ 9, rdK s.M (ob1B dB + t * 2 ^ 9 + i) = Y t i) :
    (∀ t < 48, ∀ i < 2 ^ 9, rdK (semXIR I (bfly1All dB) s).M (ob1B dB + t * 2 ^ 9 + i) =
      coeffsAt ptK nLog 9 0 (Y t) i) ∧
    (∀ x, regs ≤ x → (x < ob1B dB ∨ ob1B dB + 48 * 2 ^ 9 ≤ x) →
      rd (semXIR I (bfly1All dB) s).M x = rd s.M x) ∧
    Inv (semXIR I (bfly1All dB) s).M := by
  obtain ⟨r, t, z, rW, tW, dW, rA, tA, dA, rF, tF, dF, rO, tO, zO, dO⟩ := hL
  have hs := hM.1
  simp only [regs] at r hs
  rw [bfly1All, semXIR_seq]
  have w0 : WF (.blk [.const zT 0, .const zN 48]) := by simp +decide [WF, Prim.dst, zT, zN]
  have hM0 := inv_sem I w0 hM
  have z0 := size_sem I (.blk [.const zT 0, .const zN 48]) s
  have r0 : rd (semXIR I (.blk [.const zT 0, .const zN 48]) s).M zT = toWord 0 ∧
      rd (semXIR I (.blk [.const zT 0, .const zN 48]) s).M zN = toWord 48 := by
    rw [sem_blk']; simp only [runPrims, List.foldl, Prim.run]
    refine ⟨?_, ?_⟩ <;>
    simp (disch := first | decide | (simp only [size_set, zT, zN]; omega)) only [rd_set_self, rd_set_ne] <;> rfl
  have k0 : ∀ x, regs ≤ x → rd (semXIR I (.blk [.const zT 0, .const zN 48]) s).M x = rd s.M x :=
    fun x hx => rd_blk_of_not_dst I _ s (by
      simp only [List.mem_cons, List.mem_nil_iff, or_false]
      rintro p (rfl | rfl) <;> simp only [Prim.dst, zT, zN] <;> simp only [regs] at hx <;> omega)
  generalize semXIR I (.blk [.const zT 0, .const zN 48]) s = s0 at hM0 z0 r0 k0
  obtain ⟨t0, n0⟩ := r0
  let P : ℕ → St → Prop := fun j s' => Inv s'.M ∧ s'.M.size = s.M.size ∧ rd s'.M zT = toWord j ∧
    (∀ t < j, ∀ i < 2 ^ 9, rdK s'.M (ob1B dB + t * 2 ^ 9 + i) = coeffsAt ptK nLog 9 0 (Y t) i) ∧
    (∀ x, regs ≤ x → (x < ob1B dB ∨ ob1B dB + j * 2 ^ 9 ≤ x) → rd s'.M x = rd s.M x)
  have hoB : ob1B dB = dB + 2 ^ 15 := rfl
  have hE : ∀ i, i ≠ zC → i ≠ cTmp → rd (entryK zC zN (toWord 48) s0.M) i = rd s0.M i :=
    fun i h1 h2 => entryK_frame _ (Ne.symm h1) (Ne.symm h2)
  have h0 : P 0 ⟨entryK zC zN (toWord 48) s0.M, s0.o⟩ := by
    refine ⟨inv_entryK hM0 (by decide), by simp only [size_entryK, z0], ?_,
      fun t ht => absurd ht (by omega), fun x hx _ => ?_⟩ <;> dsimp only
    · rw [hE _ (by decide) (by decide), t0]
    · simp only [regs] at hx
      rw [hE _ (by simp only [zC]; omega) (by simp only [cTmp]; omega), k0 x (by simp only [regs]; omega)]
  have hstep : ∀ j s', j < 48 → P j s' → P (j + 1) (decS zC (semXIR I (bfly1Row dB) s')) := by
    rintro j s' hj ⟨i1, i2, i3, i4, i5⟩
    rw [bfly1Row, semXIR_seq]
    set A := ob1B dB + j * 2 ^ 9 with hA
    have hs' := i1.1
    simp only [regs] at hs'
    have a1 : rd (semXIR I (.blk [.const zK (toWord (2 ^ 9)), .op .mul rA0 zT zK,
        .const zK (toWord (ob1B dB)), .op .add rA0 rA0 zK]) s').M rA0 = toWord A := by
      rw [sem_blk']; simp only [runPrims, List.foldl, Prim.run]
      simp (disch := first | decide | (simp only [size_set, zK, rA0, zT]; omega)) only [rd_set_self, rd_set_ne]
      rw [i3, mul_toWord, add_toWord, hA, Nat.add_comm]
    have a2 : ∀ x, x ≠ zK → x ≠ rA0 → rd (semXIR I (.blk [.const zK (toWord (2 ^ 9)),
        .op .mul rA0 zT zK, .const zK (toWord (ob1B dB)), .op .add rA0 rA0 zK]) s').M x = rd s'.M x :=
      fun x h1 h2 => rd_blk_of_not_dst I _ s' (by
        simp only [List.mem_cons, List.mem_nil_iff, or_false, forall_eq_or_imp, forall_eq, Prim.dst]
        exact ⟨Ne.symm h1, Ne.symm h2, Ne.symm h1, Ne.symm h2⟩)
    have hM1 := inv_sem I (P := .blk [.const zK (toWord (2 ^ 9)), .op .mul rA0 zT zK,
      .const zK (toWord (ob1B dB)), .op .add rA0 rA0 zK]) (by simp +decide [WF, Prim.dst, zK, rA0]) i1
    have z1 := size_sem I (.blk [.const zK (toWord (2 ^ 9)), .op .mul rA0 zT zK,
      .const zK (toWord (ob1B dB)), .op .add rA0 rA0 zK]) s'
    generalize semXIR I (.blk [.const zK (toWord (2 ^ 9)), .op .mul rA0 zT zK,
      .const zK (toWord (ob1B dB)), .op .add rA0 rA0 zK]) s' = s1 at a1 a2 hM1 z1
    rw [semXIR_seq]
    have hAv : A = dB + 2 ^ 15 + j * 2 ^ 9 := by simp only [hA, ob1B]
    have hx1 : ∀ x, regs ≤ x → x ≠ zK ∧ x ≠ rA0 := fun x hx => by
      simp only [regs, zK, rA0] at *; omega
    have h1 : ∀ x, regs ≤ x → rd s1.M x = rd s'.M x := fun x hx => a2 x (hx1 x hx).1 (hx1 x hx).2
    have hT1 : TabOk s1.M (tbB dB) := tabOk_congr hT fun x hx1' hx2' => by
      simp only [tbB] at hx1' hx2'
      rw [h1 x (by simp only [regs]; omega)]
      exact i5 x (by simp only [regs]; omega) (by omega)
    have hY1 : ∀ i < 2 ^ 9, rdK s1.M (A + i) = Y j i := fun i hi => by
      simp only [rdK]
      rw [h1 _ (by simp only [regs]; omega), hAv,
        show dB + 2 ^ 15 + j * 2 ^ 9 + i = ob1B dB + j * 2 ^ 9 + i by rw [hoB],
        i5 _ (by simp only [regs, hoB] at *; omega) (Or.inr (by omega))]
      exact hY j hj i hi
    have hjb : j * 2 ^ 9 + 2 ^ 9 ≤ 48 * 2 ^ 9 := by omega
    obtain ⟨-, b2, hM2⟩ := bflyIR_sem I s1 hM1 (A := A) (tb := tbB dB) (ℓ := 9) (Y := Y j) (by decide)
      (by simp only [regs, hA, ob1B]; omega) (by simp only [hA, ob1B]; omega)
      (by simp only [hA, ob1B]; omega) (by simp only [regs, tbB]; omega) (by simp only [tbB]; omega)
      (by simp only [tbB, hA, ob1B]; omega) a1 hT1 hY1
    have b1 := bflyIR_coeffs I s1 hM1 (A := A) (tb := tbB dB) (ℓ := 9) (Y := Y j) (by decide)
      (by simp only [regs, hA, ob1B]; omega) (by simp only [hA, ob1B]; omega)
      (by simp only [hA, ob1B]; omega) (by simp only [regs, tbB]; omega) (by simp only [tbB]; omega)
      (by simp only [tbB, hA, ob1B]; omega) a1 hT1 hY1
    have q2 : rd (semXIR I (bflyIR 9 (tbB dB)) s1).M zT = toWord j := by
      rw [frame I _ s1 (by simp +decide [bflyIR, lvlStep, levelIR, pairBody, pairPs, alphaIR,
        alphaBody, arithIR, addK, mulK, mulKC, redC, WF, Writes, Prim.dst, rLv, rTr, rN3, rC3, rQ,
        rP2, rN1, rC1, uT1, uX, uT2, rBs, rAL, rAH, rA0, rBit, uI, rTa, rN2, rC2, fAl, fG, fU, fW,
        fH, fT, fN, cTmp, regs]) hM1 zT (by decide) (bflyIR_nw_hi 9 _ (by decide)),
        a2 _ (by decide) (by decide), i3]
    have z2 := size_sem I (bflyIR 9 (tbB dB)) s1
    generalize semXIR I (bflyIR 9 (tbB dB)) s1 = s2 at b1 b2 hM2 q2 z2
    have hd : ∀ x, x ≠ zC → rd (decS zC (semXIR I (.blk [.op .add zT zT cOne]) s2)).M x =
        rd (semXIR I (.blk [.op .add zT zT cOne]) s2).M x := fun x hx => rd_decS (Ne.symm hx) _
    have c2 : ∀ x, x ≠ zT → rd (semXIR I (.blk [.op .add zT zT cOne]) s2).M x = rd s2.M x :=
      fun x hx => rd_blk_of_not_dst I _ s2 (by simp [Prim.dst]; exact Ne.symm hx)
    have hM3 := inv_sem I (P := .blk [.op .add zT zT cOne]) (by simp +decide [WF, Prim.dst, zT]) hM2
    have hx3 : ∀ x, regs ≤ x → x ≠ zC ∧ x ≠ zT := fun x hx => by
      simp only [regs, zC, zT] at *; omega
    refine ⟨inv_decS hM3 (by decide), by rw [size_decS, size_sem, z2, z1, i2], ?_,
      fun t ht i hi => ?_, fun x hx hx2 => ?_⟩
    · have hs2 := hM2.1
      simp only [regs] at hs2
      rw [hd _ (by decide), sem_blk']; simp only [runPrims, List.foldl, Prim.run]
      rw [rd_set_self (by simp only [zT]; omega), q2, show rd s2.M cOne = 1 from hM2.2 0 (by decide),
        add_one_toWord]
    · have hxr : regs ≤ ob1B dB + t * 2 ^ 9 + i := by simp only [regs, ob1B] at *; omega
      simp only [rdK]
      rw [hd _ (hx3 _ hxr).1, c2 _ (hx3 _ hxr).2]
      by_cases htj : t = j
      · subst htj; exact b1 i hi
      · have ht' : t < j := by omega
        have : t * 2 ^ 9 + 2 ^ 9 ≤ j * 2 ^ 9 := by
          have h := Nat.mul_le_mul_right (2 ^ 9) (Nat.succ_le_of_lt ht'); rwa [Nat.succ_mul] at h
        rw [b2 _ hxr (by left; omega), h1 _ hxr]
        exact i4 t ht' i hi
    · have e : (j + 1) * 2 ^ 9 = j * 2 ^ 9 + 2 ^ 9 := by ring
      rw [e] at hx2
      have hx4 : x < A ∨ A + 2 ^ 9 ≤ x := by
        rcases hx2 with h | h
        · exact Or.inl (Nat.lt_of_lt_of_le h (Nat.le_add_right (ob1B dB) (j * 2 ^ 9)))
        · rw [← Nat.add_assoc] at h; exact Or.inr h
      have hx5 : x < ob1B dB ∨ ob1B dB + j * 2 ^ 9 ≤ x := by
        rcases hx2 with h | h
        · exact Or.inl h
        · exact Or.inr (le_trans (by rw [← Nat.add_assoc]; exact Nat.le_add_right _ _) h)
      rw [hd _ (hx3 x hx).1, c2 _ (hx3 x hx).2, b2 x hx hx4, h1 x hx, i5 x hx hx5]
  have hfin := loopK_run I (bfly1Row dB) P s0 hM0 (c := zC) (n := zN) (K := 48) (by decide)
    (by decide) (by decide) n0 (by norm_num) h0 hstep
  exact ⟨hfin.2.2.2.1, fun x hx hx2 => hfin.2.2.2.2 x hx hx2, hfin.1⟩

/-- **The flag**: `rOk` and `ok1B`'s cell `= [2^9 ≤ cnt]`. -/
theorem ok1IR_sem (I : Array Word) (s : St) (hM : Inv s.M) {dB n : ℕ} (hdB : regs ≤ dB)
    (hdB2 : ok1B dB < 2 ^ 64) (hdBs : ok1B dB < s.M.size) (hn : n < 2 ^ 64)
    (hC : rd s.M gCnt = toWord n) :
    rd (semXIR I (ok1IR dB) s).M rOk = bW (decide (2 ^ 9 ≤ n)) ∧
    rd (semXIR I (ok1IR dB) s).M (ok1B dB) = bW (decide (2 ^ 9 ≤ n)) ∧
    (∀ x, regs ≤ x → x ≠ ok1B dB → rd (semXIR I (ok1IR dB) s).M x = rd s.M x) ∧
    Inv (semXIR I (ok1IR dB) s).M := by
  have hs := hM.1
  simp only [regs] at hs hdB
  rw [ok1IR, semXIR_seq]
  set ps : List Prim := [.const zK (toWord (2 ^ 9)), .op .ltu rOk gCnt zK, .op .xor rOk rOk cOne,
    .const zK (toWord (ok1B dB))] with hps
  have hM1 := inv_sem I (P := .blk ps) (by simp +decide [hps, WF, Prim.dst, zK, rOk]) hM
  have v1 : rd (semXIR I (.blk ps) s).M rOk = bW (decide (2 ^ 9 ≤ n)) ∧
      rd (semXIR I (.blk ps) s).M zK = toWord (ok1B dB) := by
    rw [sem_blk', hps]; simp only [runPrims, List.foldl, Prim.run]
    refine ⟨?_, ?_⟩ <;>
    simp (disch := first | decide | (simp only [size_set, zK, rOk]; omega)) only [rd_set_self, rd_set_ne]
    rw [hC, ltW_toWord hn (by norm_num), show rd s.M cOne = 1 from hM.2 0 (by decide), eval_xor,
      bW_xor_one]
    congr 1
    rw [← decide_not]
    simp only [Nat.not_lt]
  have k1 : ∀ x, regs ≤ x → rd (semXIR I (.blk ps) s).M x = rd s.M x := fun x hx => by
    simp only [regs] at hx
    refine rd_blk_of_not_dst I _ s ?_
    simp only [hps, List.mem_cons, List.mem_nil_iff, or_false]
    rintro p (rfl | rfl | rfl | rfl) <;> simp only [Prim.dst, zK, rOk] <;> omega
  have z1 := size_sem I (.blk ps) s
  generalize semXIR I (.blk ps) s = s1 at hM1 v1 k1 z1
  obtain ⟨st1, st2, hM2⟩ := store_sem I s1 hM1 (p := zK) (v := rOk) (x := ok1B dB) (by decide)
    (by decide) v1.2 (by simp only [regs, ok1B]; omega) hdB2 (by omega)
  refine ⟨?_, by rw [st1, v1.1], fun x hx hx2 => by
    rw [st2 x hx2 (by simp only [regs, cTmp] at *; omega), k1 x hx], hM2⟩
  rw [st2 _ (by simp only [rOk, ok1B]; omega) (by decide), v1.1]

/-- `mcpBody_sem` with only the read address below `2^64` (the source pointer may wrap after it). -/
theorem tr1Body_sem (I : Array Word) (s : St) (hM : Inv s.M) {a d k : ℕ} (ha : a < 2 ^ 64)
    (hd : regs ≤ d) (hd2 : d + 1 < 2 ^ 64) (hds : d < s.M.size)
    (hS : rd s.M ySr = toWord a) (hD : rd s.M yDs = toWord d) (hK : rd s.M yStr = toWord k) :
    rd (semXIR I mcpBody s).M d = rd s.M a ∧
    rd (semXIR I mcpBody s).M ySr = toWord (a + k) ∧
    rd (semXIR I mcpBody s).M yDs = toWord (d + 1) ∧
    (∀ r, r ≠ yV → r ≠ ySr → r ≠ yDs → r ≠ cTmp → r ≠ d → rd (semXIR I mcpBody s).M r = rd s.M r) ∧
    Inv (semXIR I mcpBody s).M := by
  have hs := hM.1
  simp only [regs] at hs hd
  rw [mcpBody, semXIR_seq]
  obtain ⟨l1, l2, hM1⟩ := load_sem I s hM (d := yV) (p := ySr) (by decide) (by decide) hS ha
  have z1 := size_sem I (.load yV ySr) s
  generalize semXIR I (.load yV ySr) s = s1 at l1 l2 hM1 z1
  rw [semXIR_seq]
  obtain ⟨c1, c2, hM2⟩ := store_sem I s1 hM1 (p := yDs) (v := yV) (x := d) (by decide) (by decide)
    (by rw [l2 _ (by decide), hD]) (by simp only [regs]; omega) (by omega) (by omega)
  have z2 := size_sem I (.store yDs yV) s1
  generalize semXIR I (.store yDs yV) s1 = s2 at c1 c2 hM2 z2
  have hdr : ∀ r, r < regs → r ≠ d := fun r hr => by simp only [regs] at hr; omega
  have e2 : ∀ r, r ≠ yV → r ≠ cTmp → r ≠ d → rd s2.M r = rd s.M r := fun r h1 h2 h3 =>
    (c2 r h3 h2).trans (l2 r h1)
  have h1 : rd s2.M cOne = 1 := hM2.2 0 (by decide)
  refine ⟨?_, ?_, ?_, fun r r1 r2 r3 r4 r5 => ?_, inv_sem I (P := .blk [.op .add ySr ySr yStr,
    .op .add yDs yDs cOne]) (by simp +decide [WF, Prim.dst, ySr, yDs]) hM2⟩
  · rw [rd_blk_of_not_dst I _ s2 (by simp [Prim.dst, ySr, yDs]; omega), c1, l1]
  · rw [sem_blk']; simp only [runPrims, List.foldl, Prim.run]
    rw [rd_set_ne (by decide), rd_set_self (by simp only [ySr]; omega),
      e2 _ (by decide) (by decide) (hdr _ (by decide)), e2 _ (by decide) (by decide)
        (hdr _ (by decide)), hS, hK, add_toWord]
  · rw [sem_blk']; simp only [runPrims, List.foldl, Prim.run]
    rw [rd_set_self (by simp only [size_set, yDs]; omega), rd_set_ne (by decide),
      rd_set_ne (by decide), e2 _ (by decide) (by decide) (hdr _ (by decide)), hD, h1,
      add_one_toWord]
  · rw [rd_blk_of_not_dst I _ s2 (by simp [Prim.dst]; exact ⟨Ne.symm r2, Ne.symm r3⟩),
      e2 r r1 r4 r5]

/-- `mcpLoop_sem` with only the read addresses below `2^64`. -/
theorem tr1Loop_sem (I : Array Word) (s : St) (hM : Inv s.M) {n src str dst : ℕ}
    (hn : n < 2 ^ 64) (hsrc2 : ∀ i < n, src + str * i < 2 ^ 64) (hdst : regs ≤ dst)
    (hdst2 : dst + n < 2 ^ 64) (hdsts : dst + n ≤ s.M.size)
    (hdisj : ∀ i < n, src + str * i < dst ∨ dst + n ≤ src + str * i)
    (hsrcR : ∀ i < n, regs ≤ src + str * i)
    (hS : rd s.M ySr = toWord src) (hD : rd s.M yDs = toWord dst) (hK : rd s.M yStr = toWord str) :
    (∀ i < n, rd (semXIR I (mcpLoop n) s).M (dst + i) = rd s.M (src + str * i)) ∧
    (∀ r, KeepC r → (r < dst ∨ dst + n ≤ r) → rd (semXIR I (mcpLoop n) s).M r = rd s.M r) ∧
    Inv (semXIR I (mcpLoop n) s).M := by
  have hs := hM.1
  simp only [regs] at hs hdst
  rw [mcpLoop, semXIR_seq]
  have hM0 := inv_sem I (P := .blk [.const yN (toWord n)]) (by simp +decide [WF, Prim.dst, yN]) hM
  have n0 : rd (semXIR I (.blk [.const yN (toWord n)]) s).M yN = toWord n := by
    rw [sem_blk']; simp only [runPrims, List.foldl, Prim.run]
    rw [rd_set_self (by simp only [yN]; omega)]
  have k0 : ∀ r, r ≠ yN → rd (semXIR I (.blk [.const yN (toWord n)]) s).M r = rd s.M r :=
    fun r hr => rd_blk_of_not_dst I _ s (by simp [Prim.dst]; exact Ne.symm hr)
  have z0 := size_sem I (.blk [.const yN (toWord n)]) s
  generalize semXIR I (.blk [.const yN (toWord n)]) s = s0 at hM0 n0 k0 z0
  let P : ℕ → St → Prop := fun j s' => Inv s'.M ∧ s'.M.size = s.M.size ∧
    rd s'.M ySr = toWord (src + str * j) ∧ rd s'.M yDs = toWord (dst + j) ∧
    rd s'.M yStr = toWord str ∧ (∀ i < j, rd s'.M (dst + i) = rd s.M (src + str * i)) ∧
    (∀ r, KeepC r → (r < dst ∨ dst + j ≤ r) → rd s'.M r = rd s.M r)
  have hE : ∀ i, i ≠ yC → i ≠ cTmp → rd (entryK yC yN (toWord n) s0.M) i = rd s0.M i :=
    fun i h1 h2 => entryK_frame _ (Ne.symm h1) (Ne.symm h2)
  have h0 : P 0 ⟨entryK yC yN (toWord n) s0.M, s0.o⟩ := by
    refine ⟨inv_entryK hM0 (by decide), by simp only [size_entryK, z0], ?_, ?_, ?_,
      fun i hi => absurd hi (by omega), fun r hr _ => ?_⟩ <;> dsimp only
    · rw [hE _ (by decide) (by decide), k0 _ (by decide), hS, Nat.mul_zero, Nat.add_zero]
    · rw [hE _ (by decide) (by decide), k0 _ (by decide), hD, Nat.add_zero]
    · rw [hE _ (by decide) (by decide), k0 _ (by decide), hK]
    · obtain ⟨r1, r2, r3, r4, r5, r6⟩ := hr
      rw [hE _ r4 r6, k0 _ r5]
  have hstep : ∀ j s', j < n → P j s' → P (j + 1) (decS yC (semXIR I mcpBody s')) := by
    rintro j s' hj ⟨i1, i2, i3, i4, i5, i6, i7⟩
    obtain ⟨b1, b2, b3, b4, hM'⟩ := tr1Body_sem I s' i1 (a := src + str * j) (d := dst + j)
      (k := str) (hsrc2 j hj) (by simp only [regs]; omega) (by omega) (by omega) i3 i4 i5
    have hd : ∀ x, x ≠ yC → rd (decS yC (semXIR I mcpBody s')).M x =
        rd (semXIR I mcpBody s').M x := fun x hx => rd_decS (Ne.symm hx) _
    refine ⟨inv_decS hM' (by decide), by rw [size_decS, size_sem, i2], ?_, ?_, ?_,
      fun i hi => ?_, fun r hr hr2 => ?_⟩
    · rw [hd _ (by decide), b2, Nat.mul_succ, Nat.add_assoc]
    · rw [hd _ (by decide), b3, Nat.add_assoc]
    · rw [hd _ (by decide), b4 _ (by decide) (by decide) (by decide) (by decide)
        (by simp only [yStr, regs] at *; omega), i5]
    · have hdx : ∀ x, regs ≤ x → x ≠ yC := fun x hx => by simp only [yC, regs] at *; omega
      rw [hd _ (hdx _ (by simp only [regs]; omega))]
      by_cases hij : i = j
      · subst hij
        rw [b1, i7 _ (keepC_of_regs (hsrcR i (by omega)))
          ((hdisj i hj).imp_right (fun h => by omega))]
      · have hk := keepC_of_regs (show regs ≤ dst + i by simp only [regs]; omega)
        rw [b4 _ hk.1 hk.2.1 hk.2.2.1 hk.2.2.2.2.2 (by omega), i6 i (by omega)]
    · obtain ⟨r1, r2, r3, r4, r5, r6⟩ := hr
      rw [hd _ r4, b4 r r1 r2 r3 r6 (by omega), i7 r ⟨r1, r2, r3, r4, r5, r6⟩ (by omega)]
  have hfin := loopK_run I mcpBody P s0 hM0 (c := yC) (n := yN) (K := n) (by decide) (by decide)
    (by decide) n0 hn h0 hstep
  exact ⟨hfin.2.2.2.2.2.1, fun r hr hr2 => hfin.2.2.2.2.2.2 r hr hr2, hfin.1⟩

/-- **One transposed row** `v < 2^9`: `oB + 48 v + t := ob + v + 2^9 t` (`t < 48`), `yL := v + 1`. -/
theorem tr1Row_sem (I : Array Word) (s : St) (hM : Inv s.M) {ob oB v : ℕ} (hv : v < 2 ^ 9)
    (hob : regs ≤ ob) (hob2 : ob + 48 * 2 ^ 9 < 2 ^ 64) (hoB : regs ≤ oB)
    (hoB2 : oB + 48 * 2 ^ 9 < 2 ^ 64) (hoBs : oB + 48 * 2 ^ 9 ≤ s.M.size)
    (hdisj : ob + 48 * 2 ^ 9 ≤ oB ∨ oB + 48 * 2 ^ 9 ≤ ob) (hL : rd s.M yL = toWord v) :
    (∀ t < 48, rd (semXIR I (tr1Row ob oB) s).M (oB + 48 * v + t) = rd s.M (ob + v + 2 ^ 9 * t)) ∧
    rd (semXIR I (tr1Row ob oB) s).M yL = toWord (v + 1) ∧
    (∀ r, regs ≤ r → (r < oB + 48 * v ∨ oB + 48 * v + 48 ≤ r) →
      rd (semXIR I (tr1Row ob oB) s).M r = rd s.M r) ∧
    Inv (semXIR I (tr1Row ob oB) s).M := by
  have hs := hM.1
  simp only [regs] at hs hob hoB
  rw [tr1Row, semXIR_seq]
  set ps : List Prim := [.const yK (toWord ob), .op .add ySr yL yK, .const yK 48, .op .mul yDs yL yK,
      .const yK (toWord oB), .op .add yDs yDs yK, .const yStr (toWord (2 ^ 9))] with hps
  have w0 : WF (.blk ps) := by simp +decide [hps, WF, Prim.dst, yK, ySr, yDs, yStr]
  have hM0 := inv_sem I w0 hM
  have z0 := size_sem I (.blk ps) s
  have r0 : rd (semXIR I (.blk ps) s).M ySr = toWord (ob + v) ∧
      rd (semXIR I (.blk ps) s).M yDs = toWord (oB + 48 * v) ∧
      rd (semXIR I (.blk ps) s).M yStr = toWord (2 ^ 9) ∧ rd (semXIR I (.blk ps) s).M yL = toWord v := by
    rw [sem_blk', hps]; simp only [runPrims, List.foldl, Prim.run]
    refine ⟨?_, ?_, ?_, ?_⟩ <;>
    simp (disch := first | decide | (simp only [size_set, yK, ySr, yDs, yStr, yL]; omega)) only [rd_set_self, rd_set_ne]
    · rw [hL, add_toWord, Nat.add_comm]
    · rw [hL, show (48 : Word) = toWord 48 from rfl, mul_toWord, add_toWord, Nat.add_comm,
        Nat.mul_comm]
    · exact hL
  have k0 : ∀ r, regs ≤ r → rd (semXIR I (.blk ps) s).M r = rd s.M r := fun r hr => by
    simp only [regs] at hr
    refine rd_blk_of_not_dst I _ s ?_
    simp only [hps, List.mem_cons, List.mem_nil_iff, or_false]
    rintro p (rfl | rfl | rfl | rfl | rfl | rfl | rfl) <;>
      simp only [Prim.dst, yK, ySr, yDs, yStr] <;> omega
  generalize semXIR I (.blk ps) s = s0 at hM0 z0 r0 k0
  obtain ⟨p1, p2, p3, p4⟩ := r0
  rw [semXIR_seq]
  obtain ⟨m1, m2, hM1⟩ := tr1Loop_sem I s0 hM0 (n := 48) (src := ob + v) (str := 2 ^ 9)
    (dst := oB + 48 * v) (by norm_num) (fun i hi => by omega) (by simp only [regs]; omega)
    (by omega) (by omega) (fun i hi => by omega) (fun i hi => by simp only [regs]; omega) p1 p2 p3
  have z1 := size_sem I (mcpLoop 48) s0
  have l1 : rd (semXIR I (mcpLoop 48) s0).M yL = toWord v := by
    rw [frame I _ s0 (by simp +decide [mcpLoop, mcpBody, WF, Writes, Prim.dst, ySr, yDs, yV, yN,
      yC, cTmp, regs]) hM0 yL (by decide) (by simp +decide [mcpLoop, mcpBody, Writes, Prim.dst,
        ySr, yDs, yV, yN, yC, yL, cTmp]), p4]
  generalize semXIR I (mcpLoop 48) s0 = s1 at m1 m2 hM1 z1 l1
  have b2 : ∀ r, r ≠ yL → rd (semXIR I (.blk [.op .add yL yL cOne]) s1).M r = rd s1.M r :=
    fun r hr => rd_blk_of_not_dst I _ s1 (by simp [Prim.dst]; exact Ne.symm hr)
  have hx : ∀ x, regs ≤ x → x ≠ yL := fun x hx => by simp only [regs, yL] at *; omega
  refine ⟨fun t ht => ?_, ?_, fun r hr hr2 => ?_, inv_sem I (P := .blk [.op .add yL yL cOne])
    (by simp +decide [WF, Prim.dst, yL]) hM1⟩
  · rw [b2 _ (hx _ (by simp only [regs]; omega)), m1 t ht, k0 _ (by simp only [regs]; omega)]
  · have hs1 := hM1.1
    simp only [regs] at hs1
    rw [sem_blk']; simp only [runPrims, List.foldl, Prim.run]
    rw [rd_set_self (by simp only [yL]; omega), l1, show rd s1.M cOne = 1 from hM1.2 0 (by decide),
      add_one_toWord]
  · rw [b2 _ (hx r hr), m2 r (keepC_of_regs hr) hr2, k0 r hr]

/-- **The transpose**: `M[oB + 48 v + t] = M[ob + 2^9 t + v]`; the heap outside
`[oB, oB + 48·2^9)` is kept. -/
theorem tr1IR_sem (I : Array Word) (s : St) (hM : Inv s.M) {ob oB : ℕ}
    (hob : regs ≤ ob) (hob2 : ob + 48 * 2 ^ 9 < 2 ^ 64) (hoB : regs ≤ oB)
    (hoB2 : oB + 48 * 2 ^ 9 < 2 ^ 64) (hoBs : oB + 48 * 2 ^ 9 ≤ s.M.size)
    (hd : ob + 48 * 2 ^ 9 ≤ oB ∨ oB + 48 * 2 ^ 9 ≤ ob) :
    (∀ v < 2 ^ 9, ∀ t < 48, rd (semXIR I (tr1IR ob oB) s).M (oB + 48 * v + t) =
      rd s.M (ob + 2 ^ 9 * t + v)) ∧
    (∀ x, regs ≤ x → (x < oB ∨ oB + 48 * 2 ^ 9 ≤ x) → rd (semXIR I (tr1IR ob oB) s).M x = rd s.M x) ∧
    Inv (semXIR I (tr1IR ob oB) s).M := by
  have hs := hM.1
  simp only [regs] at hs hob hoB
  rw [tr1IR, semXIR_seq]
  have w0 : WF (.blk [.const yL 0, .const yN2 (toWord (2 ^ 9))]) := by
    simp +decide [WF, Prim.dst, yL, yN2]
  have hM0 := inv_sem I w0 hM
  have z0 := size_sem I (.blk [.const yL 0, .const yN2 (toWord (2 ^ 9))]) s
  have r0 : rd (semXIR I (.blk [.const yL 0, .const yN2 (toWord (2 ^ 9))]) s).M yL = toWord 0 ∧
      rd (semXIR I (.blk [.const yL 0, .const yN2 (toWord (2 ^ 9))]) s).M yN2 = toWord (2 ^ 9) := by
    rw [sem_blk']; simp only [runPrims, List.foldl, Prim.run]
    refine ⟨?_, ?_⟩ <;>
    simp (disch := first | decide | (simp only [size_set, yL, yN2]; omega)) only [rd_set_self, rd_set_ne] <;> rfl
  have k0 : ∀ r, regs ≤ r →
      rd (semXIR I (.blk [.const yL 0, .const yN2 (toWord (2 ^ 9))]) s).M r = rd s.M r :=
    fun r hr => by
      simp only [regs] at hr
      refine rd_blk_of_not_dst I _ s ?_
      simp only [List.mem_cons, List.mem_nil_iff, or_false]
      rintro p (rfl | rfl) <;> simp only [Prim.dst, yL, yN2] <;> omega
  generalize semXIR I (.blk [.const yL 0, .const yN2 (toWord (2 ^ 9))]) s = s0 at hM0 z0 r0 k0
  obtain ⟨l0, n0⟩ := r0
  let P : ℕ → St → Prop := fun j s' => Inv s'.M ∧ s'.M.size = s.M.size ∧ rd s'.M yL = toWord j ∧
    (∀ v < j, ∀ t < 48, rd s'.M (oB + 48 * v + t) = rd s.M (ob + 2 ^ 9 * t + v)) ∧
    (∀ r, regs ≤ r → (r < oB ∨ oB + 48 * j ≤ r) → rd s'.M r = rd s.M r)
  have hE : ∀ i, i ≠ yC2 → i ≠ cTmp → rd (entryK yC2 yN2 (toWord (2 ^ 9)) s0.M) i = rd s0.M i :=
    fun i h1 h2 => entryK_frame _ (Ne.symm h1) (Ne.symm h2)
  have h0 : P 0 ⟨entryK yC2 yN2 (toWord (2 ^ 9)) s0.M, s0.o⟩ := by
    refine ⟨inv_entryK hM0 (by decide), by simp only [size_entryK, z0], ?_,
      fun v hv => absurd hv (by omega), fun r hr _ => ?_⟩ <;> dsimp only
    · rw [hE _ (by decide) (by decide), l0]
    · simp only [regs] at hr
      rw [hE _ (by simp only [yC2]; omega) (by simp only [cTmp]; omega), k0 r (by simp only [regs]; omega)]
  have hstep : ∀ j s', j < 2 ^ 9 → P j s' → P (j + 1) (decS yC2 (semXIR I (tr1Row ob oB) s')) := by
    rintro j s' hj ⟨i1, i2, i3, i4, i5⟩
    obtain ⟨b1, b2, b3, hM'⟩ := tr1Row_sem I s' i1 (ob := ob) (oB := oB) hj
      (by simp only [regs]; omega) hob2 (by simp only [regs]; omega) hoB2 (by omega) hd i3
    have hd' : ∀ x, x ≠ yC2 → rd (decS yC2 (semXIR I (tr1Row ob oB) s')).M x =
        rd (semXIR I (tr1Row ob oB) s').M x := fun x hx => rd_decS (Ne.symm hx) _
    have hx : ∀ x, regs ≤ x → x ≠ yC2 := fun x hx => by simp only [regs, yC2] at *; omega
    refine ⟨inv_decS hM' (by decide), by rw [size_decS, size_sem, i2], by rw [hd' _ (by decide), b2],
      fun v hv t ht => ?_, fun r hr hr2 => ?_⟩
    · rw [hd' _ (hx _ (by simp only [regs]; omega))]
      by_cases hvj : v = j
      · subst hvj
        rw [b1 t ht, i5 _ (by simp only [regs]; omega) (by omega), Nat.add_right_comm]
      · rw [b3 _ (by simp only [regs]; omega) (by omega), i4 v (by omega) t ht]
    · rw [hd' _ (hx r hr), b3 r hr (by omega), i5 r hr (by omega)]
  have hfin := loopK_run I (tr1Row ob oB) P s0 hM0 (c := yC2) (n := yN2) (K := 2 ^ 9) (by decide)
    (by decide) (by decide) n0 (by norm_num) h0 hstep
  exact ⟨hfin.2.2.2.1, fun r hr hr2 => hfin.2.2.2.2 r hr (by omega), hfin.1⟩

end Lvm.X
end
-- ===== end of `LvmXDec1IR` =====

-- ===== merged from `LvmXDec1IR2` (GOLF module merge: `LvmXDec1IR2.lean` is now a stub importing `LvmXDec1Cost`) =====
section
-- lvm2 X-REC2 (helper DEC): the level-1 decoder program `dec1IR` and its semantics. Adapted from this
-- entry's `LvmXDecIR3.lean`/`LvmXDecIR4.lean` (v1's `decTail_sem`, `decIR`, `decIR_sem`).

/-!
# The level-1 decoder of `C_rec` on the machine

`dec1IR dB wB aB fB oB`: the basis table (`wtabIR`); `eq(α₁, ·)` (`eqtIR 4`); `Enc₁(f₂)`
(`enc1IR`); the agreement scan (`agree1IR`); the flag (`ok1IR`); on success the interpolation
of the 48 lanes, their inverse NTTs and the transpose into the output (`dec1Tail`).

**`dec1IR_sem`**: on a memory holding the level-1 word `wd` at `wB + 48q + t` (`q < 2^12`,
`t < 48`), `α_i` at `aB + 3i` (`i < 4`) and `f₂(v)` at `fB + 3v` (`v < 2^9`, `rdE`), with the
layout `Dec1Lay`:
* the cell `ok1B dB` holds `[2^9 ≤ |agree1L wd α f₂|]`, i.e. `decodeRec1 wd α f₂ ≠ none`;
* if `decodeRec1 wd α f₂ = some f₁`, then `rdE (oB + 3v) = f₁ v` for every `v < 2^13`: the
  layout v1's `decIR` reads its `f₁` from (`fB := oB`);
* the heap outside the workspace `[dB, dB + 2^16)` and the output `[oB, oB + 3·2^13)` is kept.
-/

namespace Lvm.X

open RecursionFast Finset Lvm.Nb CompPoly.Extension BF64

attribute [local irreducible] entryK storeM

/-- **The level-1 decoder program.** -/
def dec1IR (dB wB aB fB oB : ℕ) : XIR :=
  .seq (wtabIR (tbB dB)) (.seq (eqtIR 4 aB (q1B dB)) (.seq (enc1IR dB fB)
    (.seq (agree1IR wB (q1B dB) (enc1B dB) (ag1B dB)) (.seq (ok1IR dB)
      (.ite rOk (dec1Tail dB wB oB) (.blk []))))))

theorem eqA1_congr {α α' : ℕ → Ext3} (h : ∀ i < 4, α i = α' i) (u : ℕ) : eqA1 α u = eqA1 α' u := by
  simp only [eqA1, eqBits, bitSel]
  refine Finset.prod_congr rfl fun i hi => ?_
  rw [h i (mem_range.1 hi)]

/-- **The decoding proper**: on a list of `≥ 2^9` agreeing positions at `ag1B`, the decoded
message at `oB`. -/
theorem dec1Tail_sem (I : Array Word) (s : St) (hM : Inv s.M) {dB wB aB fB oB : ℕ}
    (hL : Dec1Lay dB wB aB fB oB s.M.size) (hT : TabOk s.M (tbB dB)) (wd : ℕ → ℕ → BF64)
    (α f₂ : ℕ → Ext3) (hW : ∀ q < 2 ^ 12, ∀ t < 48, rdK s.M (wB + 48 * q + t) = wd q t)
    (hlen : 2 ^ 9 ≤ (agree1L wd α f₂).length)
    (hJ : ∀ t < 2 ^ 9, rd s.M (ag1B dB + t) = toWord ((agree1L wd α f₂).getD t 0)) :
    (∀ v < 2 ^ 13, rdE (semXIR I (dec1Tail dB wB oB) s).M (oB + 3 * v) = dec1At wd α f₂ v) ∧
    (∀ x, regs ≤ x → (x < dB + 2 ^ 10 ∨ dB + 2 ^ 16 ≤ x) → (x < oB ∨ oB + 3 * 2 ^ 13 ≤ x) →
      rd (semXIR I (dec1Tail dB wB oB) s).M x = rd s.M x) ∧
    Inv (semXIR I (dec1Tail dB wB oB) s).M := by
  have hL' := hL
  obtain ⟨r, t, z, rW, tW, dW, rA, tA, dA, rF, tF, dF, rO, tO, zO, dO⟩ := hL'
  simp only [regs] at r rW rO
  set Jl := sel1J wd α f₂ with hJl
  have hJlen : Jl.length = 2 ^ 9 := by
    rw [hJl, sel1J, List.length_take, Nat.min_eq_left hlen]
  have hJnd : Jl.Nodup := (nodup_agree1L wd α f₂).sublist (List.take_sublist _ _)
  have hJlt : ∀ j ∈ Jl, j < 2 ^ 12 := fun j hj => (mem_agree1L.1 (List.mem_of_mem_take hj)).1
  have hBL : BaryLay (2 ^ 9) 48 (ag1B dB) (wb1B dB) (eb1B dB) wB 48 (ob1B dB) s.M.size := by
    refine ⟨by norm_num, le_rfl, ?_, ?_, ?_, ?_, rW, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
      ?_, ?_, ?_, ?_, ?_⟩ <;> (try simp only [regs, ag1B, wb1B, eb1B, ob1B]) <;> omega
  have hget : ∀ t < 2 ^ 9, Jl.getD t 0 < 2 ^ 15 := fun t ht => by
    rw [List.getD_eq_getElem _ _ (by omega)]
    have := hJlt _ (List.getElem_mem (l := Jl) (n := t) (by omega)); omega
  rw [dec1Tail, semXIR_seq]
  obtain ⟨b1, b2, hM1⟩ := baryIR_sem I s hM (Jl := Jl) hBL hget (fun t ht => by
    rw [hJ t ht, hJl, sel1J, getD_take_lt ht])
  have z1 := size_sem I (baryIR (2 ^ 9) 48 (ag1B dB) (wb1B dB) (eb1B dB) wB 48 (ob1B dB)) s
  generalize semXIR I (baryIR (2 ^ 9) 48 (ag1B dB) (wb1B dB) (eb1B dB) wB 48 (ob1B dB)) s = s1
    at b1 b2 hM1 z1
  have hL1 : Dec1Lay dB wB aB fB oB s1.M.size := by rw [z1]; exact hL
  have hT1 : TabOk s1.M (tbB dB) := tabOk_congr hT fun x h1 h2 => by
    simp only [tbB] at h1 h2
    exact b2 x (by simp only [regs]; omega) (by simp only [wb1B]; omega) (by simp only [eb1B]; omega)
      (by simp only [ob1B]; omega)
  rw [semXIR_seq]
  obtain ⟨c1, c2, hM2⟩ := bfly1All_sem I s1 hM1 hL1 hT1
    (fun t i => rdK s1.M (ob1B dB + t * 2 ^ 9 + i)) (fun _ _ _ _ => rfl)
  have z2 := size_sem I (bfly1All dB) s1
  generalize semXIR I (bfly1All dB) s1 = s2 at c1 c2 hM2 z2
  obtain ⟨d1, d2, hM3⟩ := tr1IR_sem I s2 hM2 (ob := ob1B dB) (oB := oB)
    (by simp only [regs, ob1B]; omega) (by simp only [ob1B]; omega) (by simp only [regs]; omega)
    (by omega) (by rw [z2, z1]; omega) (by simp only [ob1B]; omega)
  generalize semXIR I (tr1IR (ob1B dB) oB) s2 = s3 at d1 d2 hM3
  refine ⟨fun v hv => ?_, fun x hx hx2 hx3 => ?_, hM3⟩
  · -- the decoded entry `v = u + 16 v'`
    have hval : ∀ c < 3, rdK s3.M (oB + 3 * v + c) = coef1 wd α f₂ (3 * (v % 16) + c) (v / 16) := by
      intro c hc
      have hu : v % 16 < 16 := Nat.mod_lt _ (by norm_num)
      have hv' : v / 16 < 2 ^ 9 := by omega
      have e : oB + 3 * v + c = oB + 48 * (v / 16) + (3 * (v % 16) + c) := by omega
      simp only [rdK]
      rw [e, d1 (v / 16) hv' (3 * (v % 16) + c) (by omega),
        show ob1B dB + 2 ^ 9 * (3 * (v % 16) + c) + v / 16 =
          ob1B dB + (3 * (v % 16) + c) * 2 ^ 9 + v / 16 by ring,
        show wK (rd s2.M (ob1B dB + (3 * (v % 16) + c) * 2 ^ 9 + v / 16)) =
          rdK s2.M (ob1B dB + (3 * (v % 16) + c) * 2 ^ 9 + v / 16) from rfl,
        c1 (3 * (v % 16) + c) (by omega) (v / 16) hv', coef1]
      refine coeffsAt_congr ptK nLog 9 0 _ _ (fun j hj => ?_) (v / 16) hv'
      rw [show ob1B dB + (3 * (v % 16) + c) * 2 ^ 9 + j = ob1B dB + 2 ^ 9 * (3 * (v % 16) + c) + j
        by ring, b1 j hj _ (by omega), show (2 : ℕ) ^ 9 = Jl.length from hJlen.symm,
        baryValK_eq hJnd (fun j hj => by have := hJlt j hj; omega) (by omega)]
      refine interpF_congr ptK _ (fun q hq => ?_) j
      have hq' := hJlt q (List.mem_toFinset.1 hq)
      rw [hW q hq' _ (by omega), lane1]
    have h0 := hval 0 (by norm_num)
    rw [Nat.add_zero, Nat.add_zero] at h0
    rw [rdE, h0, hval 1 (by norm_num), hval 2 (by norm_num), dec1At]
  · simp only [regs] at hx
    rw [d2 x (by simp only [regs]; omega) (by omega),
      c2 x (by simp only [regs]; omega) (by simp only [ob1B]; omega),
      b2 x (by simp only [regs]; omega) (by simp only [wb1B]; omega) (by simp only [eb1B]; omega)
        (by simp only [ob1B]; omega)]

/-- **The level-1 decoder computes `decodeRec1`.** -/
theorem dec1IR_sem (I : Array Word) (s : St) (hM : Inv s.M) {dB wB aB fB oB : ℕ}
    (hL : Dec1Lay dB wB aB fB oB s.M.size) (wd : ℕ → ℕ → BF64) (α f₂ : ℕ → Ext3)
    (hW : ∀ q < 2 ^ 12, ∀ t < 48, rdK s.M (wB + 48 * q + t) = wd q t)
    (hA : ∀ i < 4, rdE s.M (aB + 3 * i) = α i)
    (hF : ∀ v < 2 ^ 9, rdE s.M (fB + 3 * v) = f₂ v) :
    rd (semXIR I (dec1IR dB wB aB fB oB) s).M (ok1B dB) =
      bW (decide (2 ^ 9 ≤ (agree1L wd α f₂).length)) ∧
    (∀ f₁, decodeRec1 wd α f₂ = some f₁ →
      ∀ v < 2 ^ 13, rdE (semXIR I (dec1IR dB wB aB fB oB) s).M (oB + 3 * v) = f₁ v) ∧
    (∀ x, regs ≤ x → (x < dB ∨ dB + 2 ^ 16 ≤ x) → (x < oB ∨ oB + 3 * 2 ^ 13 ≤ x) →
      rd (semXIR I (dec1IR dB wB aB fB oB) s).M x = rd s.M x) ∧
    Inv (semXIR I (dec1IR dB wB aB fB oB) s).M := by
  have hL' := hL
  obtain ⟨r, t, z, rW, tW, dW, rA, tA, dA, rF, tF, dF, rO, tO, zO, dO⟩ := hL'
  have hs := hM.1
  simp only [regs] at r rW rA rF rO hs
  -- 1. the basis table
  rw [dec1IR, semXIR_seq]
  obtain ⟨w1, w2, hM1, z1⟩ := wtabIR_sem I s hM (tb := tbB dB) (by simp only [regs, tbB]; omega)
    (by simp only [tbB]; omega) (by simp only [tbB]; omega)
  generalize semXIR I (wtabIR (tbB dB)) s = s1 at w1 w2 hM1 z1
  have hT1 : TabOk s1.M (tbB dB) := w1
  -- 2. the `eq` table
  rw [semXIR_seq]
  obtain ⟨q1, q2, hM2⟩ := eqtIR_sem I s1 hM1 (ℓ := 4) (aB := aB) (qB := q1B dB) (by norm_num)
    (by simp only [regs]; omega) (by omega) (by simp only [regs, q1B]; omega)
    (by simp only [q1B]; omega) (by rw [z1]; simp only [q1B]; omega) (by simp only [q1B]; omega)
  have z2 := size_sem I (eqtIR 4 aB (q1B dB)) s1
  generalize semXIR I (eqtIR 4 aB (q1B dB)) s1 = s2 at q1 q2 hM2 z2
  have q2' : ∀ x, regs ≤ x → (x < q1B dB ∨ q1B dB + 48 ≤ x) → rd s2.M x = rd s1.M x :=
    fun x hx hx2 => q2 x (.inr (lt_of_lt_of_le (by decide) hx)) (by omega)
  have hT2 : TabOk s2.M (tbB dB) := tabOk_congr hT1 fun x h1 h2 => by
    simp only [tbB] at h1 h2
    exact q2' x (by simp only [regs]; omega) (by simp only [q1B]; omega)
  have hQ2 : ∀ u < 16, rdE s2.M (q1B dB + 3 * u) = eqA1 α u := fun u hu => by
    rw [q1 u hu]
    refine eqA1_congr (fun i hi => ?_) u
    rw [← hA i hi]
    exact rdE_congr fun k hk => w2 _ (by simp only [regs]; omega) (by simp only [tbB]; omega)
  have hL2 : Dec1Lay dB wB aB fB oB s2.M.size := by rw [z2, z1]; exact hL
  -- 3. `Enc₁(f₂)`
  rw [semXIR_seq]
  obtain ⟨e1, e2, hM3⟩ := enc1IR_sem I s2 hM2 hL2 hT2
  have z3 := size_sem I (enc1IR dB fB) s2
  generalize semXIR I (enc1IR dB fB) s2 = s3 at e1 e2 hM3 z3
  have hout : ∀ x, regs ≤ x → (x < dB ∨ dB + 2 ^ 16 ≤ x) → rd s2.M x = rd s.M x := fun x hx hx2 => by
    rw [q2' x hx (by simp only [q1B]; omega), w2 x hx (by simp only [tbB]; omega)]
  have hfB : ∀ v < 2 ^ 9, ∀ c < 3, rdK s2.M (fB + 3 * v + c) = rdK s.M (fB + 3 * v + c) :=
    fun v hv c hc => by simp only [rdK]; rw [hout _ (by simp only [regs]; omega) (by omega)]
  have hW3 : ∀ q < 2 ^ 12, ∀ t < 48, rdK s3.M (wB + 48 * q + t) = wd q t := fun q hq t ht => by
    rw [← hW q hq t ht]; simp only [rdK]
    rw [e2 _ (by simp only [regs]; omega) (by simp only [enc1B]; omega),
      hout _ (by simp only [regs]; omega) (by omega)]
  have hQ3 : ∀ u < 16, rdE s3.M (q1B dB + 3 * u) = eqA1 α u := fun u hu => by
    rw [← hQ2 u hu]
    exact rdE_congr fun k hk => e2 _ (by simp only [regs, q1B]; omega)
      (by simp only [q1B, enc1B]; omega)
  have hE3 : ∀ q < 2 ^ 12, enc1 f₂ q = mkE (rdK s3.M (enc1B dB + q))
      (rdK s3.M (enc1B dB + 2 ^ 12 + q)) (rdK s3.M (enc1B dB + 2 * 2 ^ 12 + q)) := fun q hq => by
    have hc : ∀ c < 3, ∑ v ∈ range (2 ^ 9), rdK s.M (fB + 3 * v + c) * nbAt v q =
        rdK s3.M (enc1B dB + c * 2 ^ 12 + q) := fun c hc => by
      rw [e1 c hc q hq, sum_nbAt_eq_encN]
      exact congrArg (fun g => encN ptK g q) (funext fun x => (hfB x x.isLt c hc).symm)
    have hc0 := hc 0 (by norm_num)
    have hc1 := hc 1 (by norm_num)
    have hc2 := hc 2 (by norm_num)
    rw [Nat.zero_mul, Nat.add_zero] at hc0
    rw [Nat.one_mul] at hc1
    rw [enc1, ← hc0, ← hc1, ← hc2, ← mkE_sum]
    refine Finset.sum_congr rfl fun v hv => ?_
    rw [← mkE_mul_ofK, ← hF v (mem_range.1 hv)]
    rfl
  have hAg : agree1M s3.M wB (q1B dB) (enc1B dB) (2 ^ 12) = agree1L wd α f₂ :=
    agree1M_eq_agree1L wd α f₂ hW3 hQ3 hE3
  -- 4. the agreement scan
  rw [semXIR_seq]
  obtain ⟨g1, g2, g3, hM4⟩ := agree1IR_sem I s3 hM3 (wB := wB) (qB := q1B dB) (eB := enc1B dB)
    (agB := ag1B dB) (by simp only [regs]; omega) (by omega) (by simp only [regs, q1B]; omega)
    (by simp only [q1B]; omega) (by simp only [regs, enc1B]; omega) (by simp only [enc1B]; omega)
    (by simp only [regs, ag1B]; omega) (by simp only [ag1B]; omega)
    (by rw [z3, z2, z1]; simp only [ag1B]; omega)
    ⟨by simp only [ag1B]; omega, by simp only [ag1B, q1B]; omega, by simp only [ag1B, enc1B]; omega⟩
  rw [hAg] at g1 g2
  have z4 := size_sem I (agree1IR wB (q1B dB) (enc1B dB) (ag1B dB)) s3
  generalize semXIR I (agree1IR wB (q1B dB) (enc1B dB) (ag1B dB)) s3 = s4 at g1 g2 g3 hM4 z4
  have hlen64 : (agree1L wd α f₂).length < 2 ^ 64 := by
    have : (agree1L wd α f₂).length ≤ 2 ^ 12 := by
      rw [agree1L]; exact (List.length_filter_le _ _).trans (by simp)
    omega
  -- 5. the flag
  rw [semXIR_seq]
  obtain ⟨o1, o2, o3, hM5⟩ := ok1IR_sem I s4 hM4 (dB := dB) (n := (agree1L wd α f₂).length)
    (by simp only [regs]; omega) (by simp only [ok1B]; omega)
    (by rw [z4, z3, z2, z1]; simp only [ok1B]; omega) hlen64 g1
  have z5 := size_sem I (ok1IR dB) s4
  generalize semXIR I (ok1IR dB) s4 = s5 at o1 o2 o3 hM5 z5
  -- the heap of `s5`
  have hT5 : TabOk s5.M (tbB dB) := tabOk_congr hT2 fun x h1 h2 => by
    simp only [tbB] at h1 h2
    rw [o3 x (by simp only [regs]; omega) (by simp only [ok1B]; omega),
      g3 x (by simp only [regs]; omega) (by simp only [ag1B]; omega),
      e2 x (by simp only [regs]; omega) (by simp only [enc1B]; omega)]
  have h5 : ∀ x, regs ≤ x → (x < dB ∨ dB + 2 ^ 16 ≤ x) → rd s5.M x = rd s.M x := fun x hx hx2 => by
    rw [o3 x hx (by simp only [ok1B]; omega), g3 x hx (by simp only [ag1B]; omega),
      e2 x hx (by simp only [enc1B]; omega), hout x hx hx2]
  -- 6. the branch
  rw [semXIR_ite, o1]
  by_cases hk : 2 ^ 9 ≤ (agree1L wd α f₂).length
  · rw [decide_eq_true hk, if_neg bW_true_ne]
    have hL5 : Dec1Lay dB wB aB fB oB s5.M.size := by rw [z5, z4, z3, z2, z1]; exact hL
    have hW5 : ∀ q < 2 ^ 12, ∀ t < 48, rdK s5.M (wB + 48 * q + t) = wd q t := fun q hq t ht => by
      rw [← hW q hq t ht]; simp only [rdK]; rw [h5 _ (by simp only [regs]; omega) (by omega)]
    have hJ5 : ∀ t < 2 ^ 9, rd s5.M (ag1B dB + t) = toWord ((agree1L wd α f₂).getD t 0) :=
      fun t ht => by
        rw [o3 _ (by simp only [regs, ag1B]; omega) (by simp only [ag1B, ok1B]; omega), g2 t (by omega)]
    obtain ⟨d1, d2, hM6⟩ := dec1Tail_sem I s5 hM5 hL5 hT5 wd α f₂ hW5 hk hJ5
    refine ⟨?_, fun f₁ hout' v hv => ?_, fun x hx hx2 hx3 => ?_, hM6⟩
    · rw [d2 _ (by simp only [regs, ok1B]; omega) (by simp only [ok1B]; omega)
        (by simp only [ok1B]; omega), o2, decide_eq_true hk]
    · rw [decodeRec1, if_pos hk, Option.some.injEq] at hout'
      rw [← hout', d1 v hv]
      exact (if_pos hv).symm
    · rw [d2 x hx (by omega) hx3, h5 x hx hx2]
  · rw [decide_eq_false hk, if_pos bW_false_eq]
    have e6 : semXIR I (.blk []) s5 = s5 := by cases s5; rfl
    rw [e6]
    refine ⟨by rw [o2, decide_eq_false hk], fun f₁ hout' => ?_, fun x hx hx2 _ => h5 x hx hx2, hM5⟩
    rw [decodeRec1, if_neg hk] at hout'
    exact absurd hout' (by simp)

end Lvm.X
end
-- ===== end of `LvmXDec1IR2` =====

/-!
# The level-1 decoder's cost and layout

* `wf_dec1IR`, `noLoopT_dec1IR`, `outs_dec1IR`, `dec1IR_o` (no output statement).
* **`cost_dec1IR_le`**: the level-1 decoder is below `2^31` steps; with the level-1 reads
  (`cost_read1IR_le`) the level adds below `2^32` to v1's `2^37.95`.
* **`dec1Lay_example`**: `w1B = 2^23`, `d1B = 2^23 + 2^21`, `f2B = 2^23 + 2^22`,
  `a1B = 2^19 + 24`, `oB = 2^19 + 64` (v1's `fB`): everything below `2^24` (`memX = 2^25` is
  untouched), disjoint from v1's `decLay_example` (`dB = 2^22` workspace `[2^22, 3·2^21)`, word
  `[2^20, 3·2^20)`, `α₀` `[2^19, 2^19 + 18)`) except the output, which is v1's `f₁` input.
-/

namespace Lvm.X

open RecursionFast Finset Lvm.Nb CompPoly.Extension BF64

theorem wf_dec1IR (dB wB aB fB oB : ℕ) : WF (dec1IR dB wB aB fB oB) := by
  have h1 := wf_wtabIR (tbB dB)
  have h2 := wf_eqtIR 4 aB (q1B dB)
  have h3 := fun c => wf_mcpIR (2 ^ 9) (fB + c) 3 (enc1B dB + c * 2 ^ 12)
  have h4 := fun c => wf_zeroIR (2 ^ 12 - 2 ^ 9) (enc1B dB + c * 2 ^ 12 + 2 ^ 9)
  have h5 := wf_fwdIR 12 (tbB dB)
  have h6 := wf_agree1IR wB (q1B dB) (enc1B dB) (ag1B dB)
  have h7 := wf_baryIR (2 ^ 9) 48 (ag1B dB) (wb1B dB) (eb1B dB) wB 48 (ob1B dB)
  have h8 := wf_bflyIR 9 (tbB dB)
  have n8 := bflyIR_nw_hi 9 (tbB dB) (r := zC) (by decide)
  simp only [dec1IR, enc1IR, enc1C, ok1IR, dec1Tail, bfly1All, bfly1Row, tr1IR, tr1Row, WF, Writes,
    Prim.dst, h1, h2, h3, h4, h5, h6, h7, h8, n8, List.mem_cons, List.mem_nil_iff, forall_eq_or_imp,
    forall_eq, exists_eq_or_imp, exists_eq_left, or_false, false_or, true_and, and_true]
  simp +decide [mcpLoop, mcpBody, WF, Writes, Prim.dst, rA0, zK, rOk, zT, zN, zC, cTmp, regs, ySr,
    yDs, yStr, yV, yC, yN, yL, yK, yC2, yN2]

theorem noLoopT_dec1IR (dB wB aB fB oB : ℕ) : NoLoopT (dec1IR dB wB aB fB oB) := by
  simp only [dec1IR, enc1IR, enc1C, ok1IR, dec1Tail, bfly1All, bfly1Row, tr1IR, tr1Row, mcpLoop,
    mcpBody, NoLoopT, noLoopT_wtabIR, noLoopT_eqtIR, noLoopT_mcpIR, noLoopT_zeroIR, noLoopT_fwdIR,
    noLoopT_agree1IR, noLoopT_baryIR, noLoopT_bflyIR, and_self]

theorem outs_dec1IR (dB wB aB fB oB t : ℕ) : outs (dec1IR dB wB aB fB oB) t = 0 := by
  simp only [dec1IR, enc1IR, enc1C, ok1IR, dec1Tail, bfly1All, bfly1Row, tr1IR, tr1Row, mcpLoop,
    mcpBody, outs, outs_wtabIR, outs_eqtIR, outs_mcpIR, outs_zeroIR, outs_fwdIR, outs_agree1IR,
    outs_baryIR, outs_bflyIR]
  norm_num

theorem hasOut_dec1IR (dB wB aB fB oB : ℕ) : hasOut (dec1IR dB wB aB fB oB) = false := rfl

/-- **`dec1IR` writes no output.** -/
theorem dec1IR_o (I : Array Word) (s : St) (dB wB aB fB oB : ℕ) :
    (semXIR I (dec1IR dB wB aB fB oB) s).o = s.o := sem_o I _ s (hasOut_dec1IR dB wB aB fB oB)

/-! ## Costs -/

theorem cost_enc1C (dB fB c t : ℕ) : cost (enc1C dB fB c) t = 9058676 := by
  simp only [enc1C, cost, cost_mcpIR _ _ _ _ _ (show 2 ^ 9 < 2 ^ 64 by norm_num),
    cost_zeroIR _ _ _ (show 2 ^ 12 - 2 ^ 9 < 2 ^ 64 by norm_num),
    cost_fwdIR 12 _ _ (by norm_num) (by norm_num), blkSteps, List.length_cons, List.length_nil]
  norm_num

theorem cost_bfly1All (dB t : ℕ) : cost (bfly1All dB) t = 40598508 := by
  simp only [bfly1All, bfly1Row, cost, cost_bflyIR 9 _ _ (by norm_num) (by norm_num), blkSteps,
    List.length_cons, List.length_nil]
  norm_num

theorem cost_tr1IR (ob oB t : ℕ) : cost (tr1IR ob oB) t = 334348 := by
  simp only [tr1IR, tr1Row, mcpLoop, mcpBody, cost, blkSteps, List.length_cons, List.length_nil,
    toNat_toWord (show 2 ^ 9 < 2 ^ 64 by norm_num), toNat_toWord (show 48 < 2 ^ 64 by norm_num)]
  norm_num

/-- **The level-1 decoder's cost**: `925,440,493` steps (`≈ 2^29.79`; interpolation
`848,495,641`, inverse NTTs `40,598,508`, `Enc₁` `27,176,030`, agreement `8,802,318`). -/
theorem cost_dec1IR (dB wB aB fB oB t : ℕ) : cost (dec1IR dB wB aB fB oB) t = 925440493 := by
  simp only [dec1IR, enc1IR, ok1IR, dec1Tail, cost, cost_wtabIR, cost_eqtIR 4 _ _ _ (by norm_num),
    cost_enc1C, cost_agree1IR, cost_baryIR (2 ^ 9) 48 _ _ _ _ _ _ _ (by norm_num) (by norm_num),
    cost_bfly1All, cost_tr1IR, blkSteps, List.length_cons, List.length_nil]
  norm_num

/-- **The level-1 decoder is below `2^31`** (in fact `2^29.79`). -/
theorem cost_dec1IR_le (dB wB aB fB oB t : ℕ) : cost (dec1IR dB wB aB fB oB) t ≤ 2 ^ 31 := by
  rw [cost_dec1IR]; norm_num

/-- **The level-1 reads and decoder together are below `2^32`.** -/
theorem dec1_fixed_le (bX pL capW wB dB aB fB oB t : ℕ) :
    cost (read1IR bX pL capW wB) t + cost (dec1IR dB wB aB fB oB) t ≤ 2 ^ 32 := by
  have h1 := cost_read1IR_le bX pL capW wB t
  have h2 := cost_dec1IR_le dB wB aB fB oB t
  omega

/-- **A layout** below `2^24` (see the module header). -/
theorem dec1Lay_example (sz : ℕ) (hsz : 2 ^ 25 ≤ sz) :
    Dec1Lay (2 ^ 23 + 2 ^ 21) (2 ^ 23) (2 ^ 19 + 24) (2 ^ 23 + 2 ^ 22) (2 ^ 19 + 64) sz := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    (try simp only [regs]) <;> omega

end Lvm.X
