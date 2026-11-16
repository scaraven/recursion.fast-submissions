-- WP-13b: the whole decoder's semantics `decIR_sem` (new composition; on the model of
-- rf-k/submissions/flock-recursive/lean/FRXDec4F0.lean@8bff272b).
import LvmXNtt3
import LvmXNtt4
import LvmXInterp4
import LvmXCopy
import LvmXDecBr
import LvmXEqT

-- ===== merged from `LvmXNtt5` (GOLF module merge: `LvmXNtt5.lean` is now a stub importing `LvmXDecIR4`) =====
section
-- adapted from rf-k/submissions/flock-recursive/lean/FRXFwd.lean@8bff272b (section G6_FRXBfly:
-- bflyIR_decode, as `bflyIR_decode`).
-- New for lvm (WP-13b): the table and the NTTs composed (`wtab_bflyIR_coeffs`,
-- `wtab_fwdIR_enc`) and the link to the pure decoder `LvmXDec.decWord` (`bflyIR_decWord`).

/-!
# The NTT programs composed with the basis table and the decoder

* `wtabIR_nw`: the table program does not touch the row pointer `rA0` or the forward NTT's
  registers.
* **`wtab_bflyIR_coeffs`**, **`wtab_fwdIR_enc`**: `wtabIR tb` then `bflyIR ℓ tb` (resp.
  `fwdIR ℓ tb`) from any state with the row pointer set: the table hypothesis of
  `bflyIR_sem`/`fwdIR_sem` is discharged by `wtabIR_sem`.
* **`bflyIR_decode`**: a row holding `interpF ptK J u` with `u = Enc(c)` on `J` (`|J| = 2^ℓ`)
  decodes to `c` (`Lvm.Nb.decode_row`).
* **`bflyIR_decWord`**: the row of `C_rec`'s decoder (`LvmXDec.decWord`, `ℓ = 13`).
-/

namespace Lvm.X

open RecursionFast Finset Lvm.Nb

/-- The table program writes neither the row pointer nor the forward NTT's registers. -/
theorem wtabIR_nw {r : ℕ} (hr : r = rA0 ∨ r = rKf ∨ r = rTbf) (tb : ℕ) :
    ¬ Writes (wtabIR tb) r := by
  have hr12 : 12 ≤ r ∧ r ≠ fH ∧ r ≠ fN ∧ r ≠ fAl := by
    rcases hr with rfl | rfl | rfl <;> decide
  have n1 : ¬ Writes (mulK fH fU fW) r := (mulK_writes_iff (by have := hr12.1; omega) hr12.2.1).1
  have n2 : ¬ Writes (mulK fN fH fAl) r :=
    (mulK_writes_iff (by have := hr12.1; omega) hr12.2.2.1).1
  have n3 : ¬ Writes (invK fAl fH) r := (invK_writes_iff hr12.1 hr12.2.2.2).1
  simp only [wtabIR, row0IR, row0Body, rowIR, rowBody, Writes, Prim.dst, List.mem_cons,
    List.mem_nil_iff, n1, n2, n3]
  rcases hr with rfl | rfl | rfl <;>
  simp [rA0, rKf, rTbf, rTr, uI, rTa, rN2, rC2, fG, rLv, rN3, rC3, uT1, fU, fW, rAH, cTmp]

/-- **The table, then the inverse NTT**: the row ends holding the novel-basis coefficients of its
values. -/
theorem wtab_bflyIR_coeffs (I : Array Word) (s : St) (hM : Inv s.M) {A tb ℓ : ℕ} {Y : ℕ → BF64}
    (hℓ : ℓ ≤ nLog) (hA : regs ≤ A) (hA2 : A + 2 ^ ℓ < 2 ^ 64) (hsz : A + 2 ^ ℓ ≤ s.M.size)
    (htb : regs ≤ tb) (htb2 : tb + 225 < 2 ^ 64) (hszt : tb + 225 ≤ s.M.size)
    (hdisj : tb + 225 ≤ A ∨ A + 2 ^ ℓ ≤ tb) (hA0 : rd s.M rA0 = toWord A)
    (hY : ∀ i < 2 ^ ℓ, rdK s.M (A + i) = Y i) :
    ∀ i < 2 ^ ℓ, rdK (semXIR I (.seq (wtabIR tb) (bflyIR ℓ tb)) s).M (A + i) =
      coeffsAt ptK nLog ℓ 0 Y i := by
  have hA' : 256 ≤ A := hA
  obtain ⟨t1, t2, t3, t4⟩ := wtabIR_sem I s hM htb htb2 hszt
  rw [semXIR_seq]
  refine bflyIR_coeffs I _ t3 hℓ hA hA2 (by rw [t4]; exact hsz) htb htb2 hdisj ?_ t1 ?_
  · rw [frame I _ s (wf_wtabIR tb) hM _ (by decide) (wtabIR_nw (.inl rfl) tb), hA0]
  · intro i hi
    rw [← hY i hi]
    exact rdK_eq (t2 _ (by simp only [regs]; omega) (by omega))

/-- **The table, then the forward NTT**: on a zero-padded message the row ends holding `Enc`. -/
theorem wtab_fwdIR_enc (I : Array Word) (s : St) (hM : Inv s.M) {A tb ℓ m : ℕ}
    (hℓ : ℓ ≤ nLog) (hmℓ : m ≤ ℓ) (hA : regs ≤ A) (hA2 : A + 2 ^ ℓ < 2 ^ 64)
    (hsz : A + 2 ^ ℓ ≤ s.M.size) (htb : regs ≤ tb) (htb2 : tb + 225 < 2 ^ 64)
    (hszt : tb + 225 ≤ s.M.size) (hdisj : tb + 225 ≤ A ∨ A + 2 ^ ℓ ≤ tb)
    (hA0 : rd s.M rA0 = toWord A) (c : Fin (2 ^ m) → BF64)
    (hY : ∀ i < 2 ^ ℓ, rdK s.M (A + i) = if h : i < 2 ^ m then c ⟨i, h⟩ else 0) :
    ∀ j < 2 ^ ℓ, rdK (semXIR I (.seq (wtabIR tb) (fwdIR ℓ tb)) s).M (A + j) = encN ptK c j := by
  have hA' : 256 ≤ A := hA
  obtain ⟨t1, t2, t3, t4⟩ := wtabIR_sem I s hM htb htb2 hszt
  rw [semXIR_seq]
  refine fwdIR_enc I _ t3 hℓ hmℓ hA hA2 (by rw [t4]; exact hsz) htb htb2 hdisj ?_ t1 c ?_
  · rw [frame I _ s (wf_wtabIR tb) hM _ (by decide) (wtabIR_nw (.inl rfl) tb), hA0]
  · intro i hi
    rw [← hY i hi]
    exact rdK_eq (t2 _ (by simp only [regs]; omega) (by omega))

/-- **The machine decodes a row** (`Lvm.Nb.decode_row`): if the row at `A` holds the interpolated
values `interpF ptK J u` on `ptK [0, 2^ℓ)` and `u` agrees with `Enc(c)` on `J` (`|J| = 2^ℓ`,
`J ⊆ [0, 2^15)`), the inverse NTT leaves the message `c` in the row. -/
theorem bflyIR_decode (I : Array Word) (s : St) (hM : Inv s.M) {A tb ℓ : ℕ}
    (hℓ : ℓ ≤ nLog) (hA : regs ≤ A) (hA2 : A + 2 ^ ℓ < 2 ^ 64) (hsz : A + 2 ^ ℓ ≤ s.M.size)
    (htb : regs ≤ tb) (htb2 : tb + 225 < 2 ^ 64) (hdisj : tb + 225 ≤ A ∨ A + 2 ^ ℓ ≤ tb)
    (hA0 : rd s.M rA0 = toWord A)
    (hW : ∀ v < nLog, ∀ i < nLog, rdK s.M (tb + 15 * v + i) = (wRow ptK nLog v).getD i 0)
    {J : Finset ℕ} (hJN : ∀ i ∈ J, i < 2 ^ nLog) (hJc : J.card = 2 ^ ℓ) (c : Fin (2 ^ ℓ) → BF64)
    (u : ℕ → BF64) (hu : ∀ i ∈ J, u i = encN ptK c i)
    (hY : ∀ i < 2 ^ ℓ, rdK s.M (A + i) = interpF ptK J u i) (i : Fin (2 ^ ℓ)) :
    rdK (semXIR I (bflyIR ℓ tb) s).M (A + i) = c i := by
  rw [(bflyIR_sem I s hM hℓ hA hA2 hsz htb htb2 hdisj hA0 hW hY).1 i i.2, bflyRun_coeffs]
  exact congrFun (decode_row ptK_xor ptK_injOn15 hℓ
    (fun a ha b hb h => ptK_injOn15 (hJN a ha) (hJN b hb) h) hJc c u hu) i

open CompPoly.Extension BF64 in
/-- **`C_rec`'s decoder word on the machine** (`LvmXDec.decWord`): a row holding the interpolated
values `interpF ptK (selJ wd α f₁) (rowW wd l)` on `ptK [0, 2^13)` is turned by `bflyIR 13 tb`
into the words `decWord wd α f₁ (l·2^13 + v)`, `v < 2^13`. -/
theorem bflyIR_decWord (I : Array Word) (s : St) (hM : Inv s.M) {A tb : ℕ}
    (hA : regs ≤ A) (hA2 : A + 2 ^ 13 < 2 ^ 64) (hsz : A + 2 ^ 13 ≤ s.M.size)
    (htb : regs ≤ tb) (htb2 : tb + 225 < 2 ^ 64) (hdisj : tb + 225 ≤ A ∨ A + 2 ^ 13 ≤ tb)
    (hA0 : rd s.M rA0 = toWord A)
    (hW : ∀ v < nLog, ∀ i < nLog, rdK s.M (tb + 15 * v + i) = (wRow ptK nLog v).getD i 0)
    (wd : ℕ → ℕ → BF64) (α f₁ : ℕ → Ext3) (l : ℕ)
    (hY : ∀ i < 2 ^ 13, rdK s.M (A + i) = interpF ptK (selJ wd α f₁).toFinset (rowW wd l) i) :
    ∀ v < 2 ^ 13, rdK (semXIR I (bflyIR 13 tb) s).M (A + v) =
      decWord wd α f₁ (l * 2 ^ 13 + v) := by
  intro v hv
  rw [bflyIR_coeffs I s hM (by decide) hA hA2 hsz htb htb2 hdisj hA0 hW hY v hv, decWord,
    show (l * 2 ^ 13 + v) / 2 ^ 13 = l by omega, show (l * 2 ^ 13 + v) % 2 ^ 13 = v by omega]

end Lvm.X
end
-- ===== end of `LvmXNtt5` =====

-- ===== merged from `LvmXDecIR` (GOLF module merge: `LvmXDecIR.lean` is now a stub importing `LvmXDecIR4`) =====
section
-- WP-13b: the decoder's phases on the machine (new composition, on the model of
-- rf-k/submissions/flock-recursive/lean/FRXDec4F0.lean@8bff272b: `Enc` of the next level by the forward
-- butterflies, the agreement scan, interpolation, the butterflies per row; FR's ladder of levels is one level
-- here).

/-!
# The decoder's phases: `Enc₀(f₁)`, the inverse NTT of the 64 rows

**Workspace** `[dB, dB + 2^21)` (below `memX = 2^25`): basis table `tbB = dB` (225 words), `eq`
table `qB = dB + 256` (192), the flag `okB = dB + 512`, the weights `wbB = dB + 2^13` and the
`E` row `ebB = dB + 2^14` (2^13 each), the agreement list `agB = dB + 2^15` (2^15), `Enc₀(f₁)`'s
coordinates `encB = dB + 2^16` (3·2^15), the interpolated rows `oB = dB + 2^19` (2^19), the
message `mB = dB + 2^20` (2^19). The inputs (word `wB`, `α` at `aB`, `f₁` at `fB`) lie outside.

* `encC c`: `f₁`'s coordinate `c` (`fB + 3v + c`, `v < 2^13`) zero-padded to `2^15`, then the
  forward NTT (`fwdIR 15`): `encC_sem`, `Enc` over `K` of the coordinate at every position.
* `bflyAll`: the inverse NTT (`bflyIR 13`) on each of the 64 rows at `oB` (`bflyAll_sem`).
* `okIR`: the flag `[2^13 ≤ |A|]` in `rOk` and at `okB`.

Registers `251 … 255`.
-/

namespace Lvm.X

open RecursionFast Finset Lvm.Nb

attribute [local irreducible] entryK storeM

/-! ## Layout and registers -/

/-- The basis table. -/ def tbB (dB : ℕ) : ℕ := dB
/-- The `eq(α, ·)` table. -/ def qB (dB : ℕ) : ℕ := dB + 256
/-- The success flag. -/ def okB (dB : ℕ) : ℕ := dB + 512
/-- The interpolation weights. -/ def wbB (dB : ℕ) : ℕ := dB + 2 ^ 13
/-- The interpolation's `E` row. -/ def ebB (dB : ℕ) : ℕ := dB + 2 ^ 14
/-- The agreement list. -/ def agB (dB : ℕ) : ℕ := dB + 2 ^ 15
/-- `Enc₀(f₁)`'s coordinates. -/ def encB (dB : ℕ) : ℕ := dB + 2 ^ 16
/-- The interpolated rows (leaf-word order). -/ def oB (dB : ℕ) : ℕ := dB + 2 ^ 19
/-- **The decoded message** (`2^19` words, natural order). -/ def mB (dB : ℕ) : ℕ := dB + 2 ^ 20

/-- The flag. -/ def rOk : ℕ := 251
/-- The row index. -/ def zT : ℕ := 252
/-- Scratch. -/ def zK : ℕ := 253
/-- The row loop's counter. -/ def zC : ℕ := 254
/-- Its count. -/ def zN : ℕ := 255

/-! ## The programs -/

/-- **`Enc₀(f₁)`'s coordinate `c`** at `encB + c·2^15`: copy, zero padding, forward NTT. -/
def encC (dB fB c : ℕ) : XIR :=
  .seq (mcpIR (2 ^ 13) (fB + c) 3 (encB dB + c * 2 ^ 15))
    (.seq (zeroIR (2 ^ 15 - 2 ^ 13) (encB dB + c * 2 ^ 15 + 2 ^ 13))
      (.seq (.blk [.const rA0 (toWord (encB dB + c * 2 ^ 15))]) (fwdIR 15 (tbB dB))))

/-- The three coordinates. -/
def encIR (dB fB : ℕ) : XIR := .seq (encC dB fB 0) (.seq (encC dB fB 1) (encC dB fB 2))

/-- One row `t`: `rA0 := oB + t·2^13`, the inverse NTT, `t += 1`. -/
def bflyRow (dB : ℕ) : XIR :=
  .seq (.blk [.const zK (toWord (2 ^ 13)), .op .mul rA0 zT zK, .const zK (toWord (oB dB)),
      .op .add rA0 rA0 zK]) (.seq (bflyIR 13 (tbB dB)) (.blk [.op .add zT zT cOne]))

/-- **The inverse NTT of the 64 rows.** -/
def bflyAll (dB : ℕ) : XIR :=
  .seq (.blk [.const zT 0, .const zN 64]) (.loopK zC zN 64 (bflyRow dB))

/-- **The flag** `rOk := [2^13 ≤ cnt]`, stored at `okB`. -/
def okIR (dB : ℕ) : XIR :=
  .seq (.blk [.const zK (toWord (2 ^ 13)), .op .ltu rOk gCnt zK, .op .xor rOk rOk cOne,
    .const zK (toWord (okB dB))]) (.store zK rOk)

/-- **The decoding proper** (on success): interpolation on the first `2^13` listed positions,
the inverse NTT per row, the reorder into the message. -/
def decTail (dB wB : ℕ) : XIR :=
  .seq (baryIR (2 ^ 13) 64 (agB dB) (wbB dB) (ebB dB) wB 64 (oB dB))
    (.seq (bflyAll dB) (rowsIR (oB dB) (mB dB)))

/-! ## Costs -/

theorem cost_encC (dB fB c t : ℕ) : cost (encC dB fB c) t = 90522053 := by
  simp only [encC, cost, cost_mcpIR _ _ _ _ _ (show 2 ^ 13 < 2 ^ 64 by norm_num),
    cost_zeroIR _ _ _ (show 2 ^ 15 - 2 ^ 13 < 2 ^ 64 by norm_num), cost_fwdIR_15, blkSteps,
    List.length_cons, List.length_nil]
  norm_num

theorem cost_bflyAll (dB t : ℕ) : cost (bflyAll dB) t = 1250709900 := by
  simp only [bflyAll, bflyRow, cost, cost_bflyIR_13, blkSteps, List.length_cons, List.length_nil]
  norm_num

end Lvm.X
end
-- ===== end of `LvmXDecIR` =====

-- ===== merged from `LvmXDecIR2` (GOLF module merge: `LvmXDecIR2.lean` is now a stub importing `LvmXDecIR4`) =====
section
-- WP-13b: the decoder's phases composed (new; on the model of
-- rf-k/submissions/flock-recursive/lean/FRXDec4F0.lean@8bff272b, one level here).

/-!
# The decoder after the `eq` table: semantics of the phases and of `decMain`

* `encC_sem`, `encIR_sem`: `Enc₀(f₁)`'s three coordinates at `encB + c·2^15 + q`.
* `bflyAll_sem`: the 64 rows at `oB` become their novel-basis coefficients.
* `decTail_sem`: on a list of `≥ 2^13` agreeing positions at `agB`, the message at `mB`.
* **`decMain_sem`**: `encIR ; agreeIR ; okIR ; (decTail if ok)`: the flag at `okB` is
  `[2^13 ≤ |agreeL|]`, and on success the `2^19` words at `mB` are `decodeRec`'s.

`DecLay dB wB aB fB sz`: the workspace `[dB, dB + 2^21)` inside the memory, the inputs (word at
`wB`, `2^21` words; `α` at `aB`, 18; `f₁` at `fB`, `3·2^13`) outside it, every address below `2^60`.
-/

namespace Lvm.X

open RecursionFast Finset Lvm.Nb CompPoly.Extension BF64

attribute [local irreducible] entryK storeM

/-- The decoder's memory layout. -/
structure DecLay (dB wB aB fB sz : ℕ) : Prop where
  r : regs ≤ dB
  t : dB + 2 ^ 21 < 2 ^ 60
  z : dB + 2 ^ 21 ≤ sz
  rW : regs ≤ wB
  tW : wB + 2 ^ 21 < 2 ^ 60
  dW : wB + 2 ^ 21 ≤ dB ∨ dB + 2 ^ 21 ≤ wB
  rA : regs ≤ aB
  tA : aB + 18 < 2 ^ 60
  dA : aB + 18 ≤ dB ∨ dB + 2 ^ 21 ≤ aB
  rF : regs ≤ fB
  tF : fB + 3 * 2 ^ 13 < 2 ^ 60
  dF : fB + 3 * 2 ^ 13 ≤ dB ∨ dB + 2 ^ 21 ≤ fB

/-- The table hypothesis of the NTTs. -/
def TabOk (M : Mem) (tb : ℕ) : Prop :=
  ∀ v < nLog, ∀ i < nLog, rdK M (tb + 15 * v + i) = (wRow ptK nLog v).getD i 0

theorem tabOk_congr {M M' : Mem} {tb : ℕ} (h : TabOk M tb)
    (hf : ∀ x, tb ≤ x → x < tb + 225 → rd M' x = rd M x) : TabOk M' tb := fun v hv i hi => by
  have : 15 * v + i < 225 := by simp only [nLog] at hv hi; omega
  simp only [rdK]; rw [hf _ (by omega) (by omega)]; exact h v hv i hi

/-! ## `Enc₀(f₁)` -/

/-- **One coordinate of `Enc₀(f₁)`.** -/
theorem encC_sem (I : Array Word) (s : St) (hM : Inv s.M) {dB wB aB fB c : ℕ}
    (hL : DecLay dB wB aB fB s.M.size) (hc : c < 3) (hT : TabOk s.M (tbB dB)) :
    (∀ j < 2 ^ 15, rdK (semXIR I (encC dB fB c) s).M (encB dB + c * 2 ^ 15 + j) =
      encN ptK (fun x : Fin (2 ^ 13) => rdK s.M (fB + 3 * x + c)) j) ∧
    (∀ x, regs ≤ x → (x < encB dB + c * 2 ^ 15 ∨ encB dB + c * 2 ^ 15 + 2 ^ 15 ≤ x) →
      rd (semXIR I (encC dB fB c) s).M x = rd s.M x) ∧
    Inv (semXIR I (encC dB fB c) s).M := by
  obtain ⟨r, t, z, rW, tW, dW, rA, tA, dA, rF, tF, dF⟩ := hL
  have hs := hM.1
  simp only [regs] at r rW rA rF hs
  set A := encB dB + c * 2 ^ 15 with hA
  have hAd : dB + 2 ^ 16 ≤ A ∧ A + 2 ^ 15 ≤ dB + 2 ^ 18 := by
    simp only [hA, encB]; constructor <;> omega
  rw [encC, semXIR_seq]
  obtain ⟨m1, m2, hM1⟩ := mcpIR_sem I s hM (n := 2 ^ 13) (src := fB + c) (str := 3) (dst := A)
    (by norm_num) (by omega) (by norm_num) (by simp only [regs]; omega) (by omega) (by omega)
    (fun i hi => by omega) (fun i hi => by simp only [regs]; omega)
  have z1 := size_sem I (mcpIR (2 ^ 13) (fB + c) 3 A) s
  generalize semXIR I (mcpIR (2 ^ 13) (fB + c) 3 A) s = s1 at m1 m2 hM1 z1
  rw [semXIR_seq]
  obtain ⟨n1, n2, hM2⟩ := zeroIR_sem I s1 hM1 (n := 2 ^ 15 - 2 ^ 13) (dst := A + 2 ^ 13)
    (by norm_num) (by simp only [regs]; omega) (by omega) (by omega)
  have z2 := size_sem I (zeroIR (2 ^ 15 - 2 ^ 13) (A + 2 ^ 13)) s1
  generalize semXIR I (zeroIR (2 ^ 15 - 2 ^ 13) (A + 2 ^ 13)) s1 = s2 at n1 n2 hM2 z2
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
  have h3 : ∀ x, regs ≤ x → (x < A ∨ A + 2 ^ 15 ≤ x) → rd s3.M x = rd s.M x := fun x hx hx2 => by
    rw [k3 x hx, n2 x hx (by omega), m2 x hx (by omega)]
  have hT3 : TabOk s3.M (tbB dB) := tabOk_congr hT fun x h1 h2 => h3 x (by simp only [regs, tbB] at *; omega)
    (by simp only [tbB] at *; omega)
  have hY : ∀ i < 2 ^ 15, rdK s3.M (A + i) =
      if h : i < 2 ^ 13 then (fun x : Fin (2 ^ 13) => rdK s.M (fB + 3 * x + c)) ⟨i, h⟩ else 0 := by
    intro i hi
    simp only [rdK]
    rw [k3 _ (by simp only [regs]; omega)]
    by_cases h : i < 2 ^ 13
    · rw [dif_pos h, n2 _ (by simp only [regs]; omega) (by omega), m1 i h]
      congr 2; ring
    · rw [dif_neg h, show A + i = A + 2 ^ 13 + (i - 2 ^ 13) by omega, n1 _ (by omega)]; rfl
  have hfe := fwdIR_enc I s3 hM3 (A := A) (tb := tbB dB) (ℓ := 15) (m := 13) (by decide) (by norm_num)
    (by simp only [regs]; omega) (by omega) (by omega) (by simp only [regs, tbB]; omega)
    (by simp only [tbB]; omega) (by simp only [tbB]; omega) a3 hT3
    (fun x : Fin (2 ^ 13) => rdK s.M (fB + 3 * x + c)) hY
  obtain ⟨-, f2, f3⟩ := fwdIR_sem I s3 hM3 (A := A) (tb := tbB dB) (ℓ := 15) (Y := fun i => rdK s3.M (A + i))
    (by decide) (by simp only [regs]; omega) (by omega) (by omega) (by simp only [regs, tbB]; omega)
    (by simp only [tbB]; omega) (by simp only [tbB]; omega) a3 hT3 (fun i _ => rfl)
  exact ⟨hfe, fun x hx hx2 => (f2 x hx hx2).trans (h3 x hx hx2), f3⟩

/-- **`Enc₀(f₁)`'s three coordinates** at `encB + c·2^15 + j`. -/
theorem encIR_sem (I : Array Word) (s : St) (hM : Inv s.M) {dB wB aB fB : ℕ}
    (hL : DecLay dB wB aB fB s.M.size) (hT : TabOk s.M (tbB dB)) :
    (∀ c < 3, ∀ j < 2 ^ 15, rdK (semXIR I (encIR dB fB) s).M (encB dB + c * 2 ^ 15 + j) =
      encN ptK (fun x : Fin (2 ^ 13) => rdK s.M (fB + 3 * x + c)) j) ∧
    (∀ x, regs ≤ x → (x < encB dB ∨ encB dB + 3 * 2 ^ 15 ≤ x) →
      rd (semXIR I (encIR dB fB) s).M x = rd s.M x) ∧
    Inv (semXIR I (encIR dB fB) s).M := by
  have hL' := hL
  obtain ⟨r, t, z, rW, tW, dW, rA, tA, dA, rF, tF, dF⟩ := hL'
  simp only [regs] at r rF
  rw [encIR, semXIR_seq]
  obtain ⟨a1, a2, hM1⟩ := encC_sem I s hM hL (c := 0) (by norm_num) hT
  have z1 := size_sem I (encC dB fB 0) s
  generalize semXIR I (encC dB fB 0) s = s1 at a1 a2 hM1 z1
  have hL1 : DecLay dB wB aB fB s1.M.size := by rw [z1]; exact hL
  have hF1 : ∀ x, regs ≤ x → (x < encB dB ∨ encB dB + 2 ^ 15 ≤ x) → rd s1.M x = rd s.M x :=
    fun x hx hx2 => a2 x hx (by simpa using hx2)
  have hT1 : TabOk s1.M (tbB dB) := tabOk_congr hT fun x h1 h2 =>
    hF1 x (by simp only [regs, tbB] at *; omega) (by simp only [tbB, encB] at *; omega)
  rw [semXIR_seq]
  obtain ⟨b1, b2, hM2⟩ := encC_sem I s1 hM1 hL1 (c := 1) (by norm_num) hT1
  have z2 := size_sem I (encC dB fB 1) s1
  generalize semXIR I (encC dB fB 1) s1 = s2 at b1 b2 hM2 z2
  have hL2 : DecLay dB wB aB fB s2.M.size := by rw [z2]; exact hL1
  have hT2 : TabOk s2.M (tbB dB) := tabOk_congr hT1 fun x h1 h2 =>
    b2 x (by simp only [regs, tbB] at *; omega) (by simp only [tbB, encB] at *; omega)
  obtain ⟨c1, c2, hM3⟩ := encC_sem I s2 hM2 hL2 (c := 2) (by norm_num) hT2
  have hfB : ∀ x c, x < 2 ^ 13 → c < 3 → regs ≤ fB + 3 * x + c ∧
      (fB + 3 * x + c < encB dB ∨ encB dB + 3 * 2 ^ 15 ≤ fB + 3 * x + c) := fun x c hx hc => by
    simp only [regs, encB] at *; omega
  have e1 : ∀ x : Fin (2 ^ 13), ∀ c < 3, rdK s1.M (fB + 3 * x + c) = rdK s.M (fB + 3 * x + c) :=
    fun x c hc => by
      obtain ⟨h1, h2⟩ := hfB x c x.isLt hc
      simp only [rdK]; rw [a2 _ h1 (by omega)]
  have e2 : ∀ x : Fin (2 ^ 13), ∀ c < 3, rdK s2.M (fB + 3 * x + c) = rdK s.M (fB + 3 * x + c) :=
    fun x c hc => by
      obtain ⟨h1, h2⟩ := hfB x c x.isLt hc
      simp only [rdK]; rw [b2 _ h1 (by omega)]; exact e1 x c hc
  refine ⟨fun c hc j hj => ?_, fun x hx hx2 => ?_, hM3⟩
  · interval_cases c
    · simp only [rdK]
      rw [c2 _ (by simp only [regs, encB] at *; omega) (by simp only [encB] at *; omega),
        b2 _ (by simp only [regs, encB] at *; omega) (by simp only [encB] at *; omega)]
      exact a1 j hj
    · simp only [rdK]
      rw [c2 _ (by simp only [regs, encB] at *; omega) (by simp only [encB] at *; omega)]
      rw [show wK (rd s2.M (encB dB + 1 * 2 ^ 15 + j)) = rdK s2.M (encB dB + 1 * 2 ^ 15 + j) from rfl,
        b1 j hj]
      congr 1; funext x; exact e1 x 1 (by norm_num)
    · rw [c1 j hj]
      congr 1; funext x; exact e2 x 2 (by norm_num)
  · rw [c2 x hx (by omega), b2 x hx (by omega), a2 x hx (by omega)]

theorem bflyIR_nw_hi (ℓ tb : ℕ) {r : ℕ} (hr : 187 ≤ r) : ¬ Writes (bflyIR ℓ tb) r := by
  intro hw
  simp only [bflyIR, lvlStep, levelIR, pairBody, pairPs, alphaIR, alphaBody, arithIR, addK, mulK,
    mulKC, redC, Writes, Prim.dst, List.mem_cons, List.mem_nil_iff, List.cons_append,
    List.nil_append, exists_eq_or_imp, exists_eq_left, or_false, false_or] at hw
  simp only [rLv, rTr, rN3, rC3, rQ, rP2, rN1, rC1, uT1, uX, uT2, rBs, rAL, rAH, rA0, rBit, uI,
    rTa, rN2, rC2, fAl, fG, fU, fW, fH, fT, fN, cTmp] at hw
  omega

/-- **The inverse NTT of the 64 rows** at `oB`. -/
theorem bflyAll_sem (I : Array Word) (s : St) (hM : Inv s.M) {dB wB aB fB : ℕ}
    (hL : DecLay dB wB aB fB s.M.size) (hT : TabOk s.M (tbB dB)) (Y : ℕ → ℕ → BF64)
    (hY : ∀ t < 64, ∀ i < 2 ^ 13, rdK s.M (oB dB + t * 2 ^ 13 + i) = Y t i) :
    (∀ t < 64, ∀ i < 2 ^ 13, rdK (semXIR I (bflyAll dB) s).M (oB dB + t * 2 ^ 13 + i) =
      coeffsAt ptK nLog 13 0 (Y t) i) ∧
    (∀ x, regs ≤ x → (x < oB dB ∨ oB dB + 2 ^ 19 ≤ x) → rd (semXIR I (bflyAll dB) s).M x = rd s.M x) ∧
    Inv (semXIR I (bflyAll dB) s).M := by
  obtain ⟨r, t, z, rW, tW, dW, rA, tA, dA, rF, tF, dF⟩ := hL
  have hs := hM.1
  simp only [regs] at r hs
  rw [bflyAll, semXIR_seq]
  have w0 : WF (.blk [.const zT 0, .const zN 64]) := by simp +decide [WF, Prim.dst, zT, zN]
  have hM0 := inv_sem I w0 hM
  have z0 := size_sem I (.blk [.const zT 0, .const zN 64]) s
  have r0 : rd (semXIR I (.blk [.const zT 0, .const zN 64]) s).M zT = toWord 0 ∧
      rd (semXIR I (.blk [.const zT 0, .const zN 64]) s).M zN = toWord 64 := by
    rw [sem_blk']; simp only [runPrims, List.foldl, Prim.run]
    refine ⟨?_, ?_⟩ <;>
    simp (disch := first | decide | (simp only [size_set, zT, zN]; omega)) only [rd_set_self, rd_set_ne] <;> rfl
  have k0 : ∀ x, regs ≤ x → rd (semXIR I (.blk [.const zT 0, .const zN 64]) s).M x = rd s.M x :=
    fun x hx => rd_blk_of_not_dst I _ s (by
      simp only [List.mem_cons, List.mem_nil_iff, or_false]
      rintro p (rfl | rfl) <;> simp only [Prim.dst, zT, zN] <;> simp only [regs] at hx <;> omega)
  generalize semXIR I (.blk [.const zT 0, .const zN 64]) s = s0 at hM0 z0 r0 k0
  obtain ⟨t0, n0⟩ := r0
  let P : ℕ → St → Prop := fun j s' => Inv s'.M ∧ s'.M.size = s.M.size ∧ rd s'.M zT = toWord j ∧
    (∀ t < j, ∀ i < 2 ^ 13, rdK s'.M (oB dB + t * 2 ^ 13 + i) = coeffsAt ptK nLog 13 0 (Y t) i) ∧
    (∀ x, regs ≤ x → (x < oB dB ∨ oB dB + j * 2 ^ 13 ≤ x) → rd s'.M x = rd s.M x)
  have hoB : oB dB = dB + 2 ^ 19 := rfl
  have hE : ∀ i, i ≠ zC → i ≠ cTmp → rd (entryK zC zN (toWord 64) s0.M) i = rd s0.M i :=
    fun i h1 h2 => entryK_frame _ (Ne.symm h1) (Ne.symm h2)
  have h0 : P 0 ⟨entryK zC zN (toWord 64) s0.M, s0.o⟩ := by
    refine ⟨inv_entryK hM0 (by decide), by simp only [size_entryK, z0], ?_,
      fun t ht => absurd ht (by omega), fun x hx _ => ?_⟩ <;> dsimp only
    · rw [hE _ (by decide) (by decide), t0]
    · simp only [regs] at hx
      rw [hE _ (by simp only [zC]; omega) (by simp only [cTmp]; omega), k0 x (by simp only [regs]; omega)]
  have hstep : ∀ j s', j < 64 → P j s' → P (j + 1) (decS zC (semXIR I (bflyRow dB) s')) := by
    rintro j s' hj ⟨i1, i2, i3, i4, i5⟩
    rw [bflyRow, semXIR_seq]
    set A := oB dB + j * 2 ^ 13 with hA
    have hs' := i1.1
    simp only [regs] at hs'
    have a1 : rd (semXIR I (.blk [.const zK (toWord (2 ^ 13)), .op .mul rA0 zT zK,
        .const zK (toWord (oB dB)), .op .add rA0 rA0 zK]) s').M rA0 = toWord A := by
      rw [sem_blk']; simp only [runPrims, List.foldl, Prim.run]
      simp (disch := first | decide | (simp only [size_set, zK, rA0, zT]; omega)) only [rd_set_self, rd_set_ne]
      rw [i3, mul_toWord, add_toWord, hA, Nat.add_comm]
    have a2 : ∀ x, x ≠ zK → x ≠ rA0 → rd (semXIR I (.blk [.const zK (toWord (2 ^ 13)),
        .op .mul rA0 zT zK, .const zK (toWord (oB dB)), .op .add rA0 rA0 zK]) s').M x = rd s'.M x :=
      fun x h1 h2 => rd_blk_of_not_dst I _ s' (by
        simp only [List.mem_cons, List.mem_nil_iff, or_false, forall_eq_or_imp, forall_eq, Prim.dst]
        exact ⟨Ne.symm h1, Ne.symm h2, Ne.symm h1, Ne.symm h2⟩)
    have hM1 := inv_sem I (P := .blk [.const zK (toWord (2 ^ 13)), .op .mul rA0 zT zK,
      .const zK (toWord (oB dB)), .op .add rA0 rA0 zK]) (by simp +decide [WF, Prim.dst, zK, rA0]) i1
    have z1 := size_sem I (.blk [.const zK (toWord (2 ^ 13)), .op .mul rA0 zT zK,
      .const zK (toWord (oB dB)), .op .add rA0 rA0 zK]) s'
    generalize semXIR I (.blk [.const zK (toWord (2 ^ 13)), .op .mul rA0 zT zK,
      .const zK (toWord (oB dB)), .op .add rA0 rA0 zK]) s' = s1 at a1 a2 hM1 z1
    rw [semXIR_seq]
    have hAv : A = dB + 2 ^ 19 + j * 2 ^ 13 := by simp only [hA, oB]
    have hx1 : ∀ x, regs ≤ x → x ≠ zK ∧ x ≠ rA0 := fun x hx => by
      simp only [regs, zK, rA0] at *; omega
    have h1 : ∀ x, regs ≤ x → rd s1.M x = rd s'.M x := fun x hx => a2 x (hx1 x hx).1 (hx1 x hx).2
    have hT1 : TabOk s1.M (tbB dB) := tabOk_congr hT fun x hx1' hx2' => by
      simp only [tbB] at hx1' hx2'
      rw [h1 x (by simp only [regs]; omega)]
      exact i5 x (by simp only [regs]; omega) (by omega)
    have hY1 : ∀ i < 2 ^ 13, rdK s1.M (A + i) = Y j i := fun i hi => by
      simp only [rdK]
      rw [h1 _ (by simp only [regs]; omega), hAv,
        show dB + 2 ^ 19 + j * 2 ^ 13 + i = oB dB + j * 2 ^ 13 + i by rw [hoB],
        i5 _ (by simp only [regs, hoB] at *; omega) (Or.inr (by omega))]
      exact hY j hj i hi
    have hjb : j * 2 ^ 13 + 2 ^ 13 ≤ 2 ^ 19 := by omega
    obtain ⟨-, b2, hM2⟩ := bflyIR_sem I s1 hM1 (A := A) (tb := tbB dB) (ℓ := 13) (Y := Y j) (by decide)
      (by simp only [regs, hA, oB]; omega) (by simp only [hA, oB]; omega)
      (by simp only [hA, oB]; omega) (by simp only [regs, tbB]; omega) (by simp only [tbB]; omega)
      (by simp only [tbB, hA, oB]; omega) a1 hT1 hY1
    have b1 := bflyIR_coeffs I s1 hM1 (A := A) (tb := tbB dB) (ℓ := 13) (Y := Y j) (by decide)
      (by simp only [regs, hA, oB]; omega) (by simp only [hA, oB]; omega)
      (by simp only [hA, oB]; omega) (by simp only [regs, tbB]; omega) (by simp only [tbB]; omega)
      (by simp only [tbB, hA, oB]; omega) a1 hT1 hY1
    have q2 : rd (semXIR I (bflyIR 13 (tbB dB)) s1).M zT = toWord j := by
      rw [frame I _ s1 (by simp +decide [bflyIR, lvlStep, levelIR, pairBody, pairPs, alphaIR,
        alphaBody, arithIR, addK, mulK, mulKC, redC, WF, Writes, Prim.dst, rLv, rTr, rN3, rC3, rQ,
        rP2, rN1, rC1, uT1, uX, uT2, rBs, rAL, rAH, rA0, rBit, uI, rTa, rN2, rC2, fAl, fG, fU, fW,
        fH, fT, fN, cTmp, regs]) hM1 zT (by decide) (bflyIR_nw_hi 13 _ (by decide)),
        a2 _ (by decide) (by decide), i3]
    have z2 := size_sem I (bflyIR 13 (tbB dB)) s1
    generalize semXIR I (bflyIR 13 (tbB dB)) s1 = s2 at b1 b2 hM2 q2 z2
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
    · have hxr : regs ≤ oB dB + t * 2 ^ 13 + i := by simp only [regs, oB] at *; omega
      simp only [rdK]
      rw [hd _ (hx3 _ hxr).1, c2 _ (hx3 _ hxr).2]
      by_cases htj : t = j
      · subst htj; exact b1 i hi
      · have ht' : t < j := by omega
        have : t * 2 ^ 13 + 2 ^ 13 ≤ j * 2 ^ 13 := by nlinarith
        rw [b2 _ hxr (by left; omega), h1 _ hxr]
        exact i4 t ht' i hi
    · have e : (j + 1) * 2 ^ 13 = j * 2 ^ 13 + 2 ^ 13 := by ring
      rw [e] at hx2
      have hx4 : x < A ∨ A + 2 ^ 13 ≤ x := by
        rcases hx2 with h | h
        · exact Or.inl (Nat.lt_of_lt_of_le h (Nat.le_add_right (oB dB) (j * 2 ^ 13)))
        · rw [← Nat.add_assoc] at h; exact Or.inr h
      have hx5 : x < oB dB ∨ oB dB + j * 2 ^ 13 ≤ x := by
        rcases hx2 with h | h
        · exact Or.inl h
        · exact Or.inr (le_trans (by rw [← Nat.add_assoc]; exact Nat.le_add_right _ _) h)
      rw [hd _ (hx3 x hx).1, c2 _ (hx3 x hx).2, b2 x hx hx4, h1 x hx, i5 x hx hx5]
  have hfin := loopK_run I (bflyRow dB) P s0 hM0 (c := zC) (n := zN) (K := 64) (by decide)
    (by decide) (by decide) n0 (by norm_num) h0 hstep
  exact ⟨hfin.2.2.2.1, fun x hx hx2 => hfin.2.2.2.2 x hx
    (by rw [show 64 * 2 ^ 13 = 2 ^ 19 by norm_num]; exact hx2), hfin.1⟩

end Lvm.X
end
-- ===== end of `LvmXDecIR2` =====

-- ===== merged from `LvmXDecIR3` (GOLF module merge: `LvmXDecIR3.lean` is now a stub importing `LvmXDecIR4`) =====
section
-- WP-13b: the whole decoder program `decIR` and its semantics (new composition; on the model of
-- rf-k/submissions/flock-recursive/lean/FRXDec4F0.lean@8bff272b).

/-!
# The decoder of `C_rec` on the machine

`decIR dB wB aB fB`: the basis table; `eq(α, ·)` (`eqtIR`); `Enc₀(f₁)` (`encIR`); the agreement
scan (`agreeIR`); the flag (`okIR`); on success the interpolation, the inverse NTT per row and the
reorder (`decTail`).

**`decIR_sem`**: on a memory holding the word `wd` at `wB + 64q + t`, `α_i` at `aB + 3i` and
`f₁(v)` at `fB + 3v` (`rdE`), with the layout `DecLay`:
* the cell `okB dB` holds `[2^13 ≤ |agreeL wd α f₁|]`, i.e. `decodeRec wd α f₁ ≠ none`;
* if `decodeRec wd α f₁ = some out`, the `2^19` cells at `mB dB` hold `out`;
* the heap outside the workspace `[dB, dB + 2^21)` is kept.

With `decodeRec_correct`/`decodeRec_of_ud`, the cells at `mB dB` are `C_rec`'s message.
**`cost_decIR`**: `≈ 2^37.95` steps, all but `2^31.6` in the interpolation.
-/

namespace Lvm.X

open RecursionFast Finset Lvm.Nb CompPoly.Extension BF64

attribute [local irreducible] entryK storeM

/-- **The decoder program.** -/
def decIR (dB wB aB fB : ℕ) : XIR :=
  .seq (wtabIR (tbB dB)) (.seq (eqtIR 6 aB (qB dB)) (.seq (encIR dB fB)
    (.seq (agreeIR wB (qB dB) (encB dB) (agB dB)) (.seq (okIR dB) (.ite rOk (decTail dB wB) (.blk []))))))

/-! ## Pure helpers -/

theorem coeffsAt_congr {L M : Type*} [Field L] [Field M] [Algebra L M] (pt : ℕ → L) (N : ℕ) :
    ∀ ℓ s (y y' : ℕ → M), (∀ j < 2 ^ ℓ, y j = y' j) →
      ∀ x < 2 ^ ℓ, coeffsAt pt N ℓ s y x = coeffsAt pt N ℓ s y' x
  | 0, _, _, _, h, x, hx => by simp only [coeffsAt]; exact h x hx
  | ℓ + 1, s, y, y', h, x, hx => by
    have hp : 2 ^ (ℓ + 1) = 2 ^ ℓ + 2 ^ ℓ := by rw [pow_succ]; ring
    have hu := coeffsAt_congr pt N ℓ s y y' (fun j hj => h j (by omega))
    have hw := coeffsAt_congr pt N ℓ (s + 2 ^ ℓ) (fun j => y (2 ^ ℓ + j)) (fun j => y' (2 ^ ℓ + j))
      (fun j hj => h _ (by omega))
    simp only [coeffsAt]
    split_ifs with hx'
    · rw [hu x hx', hw x hx']
    · rw [hu _ (by omega), hw _ (by omega)]

theorem getD_take_lt {L : List ℕ} {n t : ℕ} (ht : t < n) : (L.take n).getD t 0 = L.getD t 0 := by
  simp only [List.getD_eq_getElem?_getD, List.getElem?_take_of_lt ht]

theorem eqA_congr {α α' : ℕ → Ext3} (h : ∀ i < 6, α i = α' i) (l : ℕ) : eqA α l = eqA α' l := by
  simp only [eqA, eqBits, bitSel]
  refine Finset.prod_congr rfl fun i hi => ?_
  rw [h i (mem_range.1 hi)]

theorem decWord_split (wd : ℕ → ℕ → BF64) (α f₁ : ℕ → Ext3) {l v : ℕ} (hv : v < 2 ^ 13) :
    decWord wd α f₁ (l * 2 ^ 13 + v) =
      coeffsAt ptK nLog 13 0 (interpF ptK (selJ wd α f₁).toFinset (rowW wd l)) v := by
  rw [decWord]
  have h1 : (l * 2 ^ 13 + v) / 2 ^ 13 = l := by omega
  have h2 : (l * 2 ^ 13 + v) % 2 ^ 13 = v := by omega
  rw [h1, h2]

/-! ## The decoding proper -/

/-- **The decoding proper**: on a list of `≥ 2^13` agreeing positions at `agB`, the message of
`decodeRec` at `mB`. -/
theorem decTail_sem (I : Array Word) (s : St) (hM : Inv s.M) {dB wB aB fB : ℕ}
    (hL : DecLay dB wB aB fB s.M.size) (hT : TabOk s.M (tbB dB)) (wd : ℕ → ℕ → BF64)
    (α f₁ : ℕ → Ext3) (hW : ∀ q < 2 ^ 15, ∀ t < 64, rdK s.M (wB + 64 * q + t) = wd q t)
    (hlen : 2 ^ 13 ≤ (agreeL wd α f₁).length)
    (hJ : ∀ t < 2 ^ 13, rd s.M (agB dB + t) = toWord ((agreeL wd α f₁).getD t 0)) :
    (∀ i < 2 ^ 19, rdK (semXIR I (decTail dB wB) s).M (mB dB + i) = decWord wd α f₁ i) ∧
    (∀ x, regs ≤ x → (x < dB + 2 ^ 13 ∨ dB + 2 ^ 21 ≤ x) →
      rd (semXIR I (decTail dB wB) s).M x = rd s.M x) ∧
    Inv (semXIR I (decTail dB wB) s).M := by
  have hL' := hL
  obtain ⟨r, t, z, rW, tW, dW, rA, tA, dA, rF, tF, dF⟩ := hL'
  simp only [regs] at r rW
  set Jl := selJ wd α f₁ with hJl
  have hJlen : Jl.length = 2 ^ 13 := by
    rw [hJl, selJ, List.length_take, Nat.min_eq_left hlen]
  have hJnd : Jl.Nodup := (nodup_agreeL wd α f₁).sublist (List.take_sublist _ _)
  have hJlt : ∀ j ∈ Jl, j < 2 ^ 15 := fun j hj => (mem_agreeL.1 (List.mem_of_mem_take hj)).1
  have hBL : BaryLay (2 ^ 13) 64 (agB dB) (wbB dB) (ebB dB) wB 64 (oB dB) s.M.size := by
    refine ⟨by norm_num, le_rfl, ?_, ?_, ?_, ?_, rW, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
      ?_, ?_, ?_, ?_, ?_⟩ <;> (try simp only [regs, agB, wbB, ebB, oB]) <;> omega
  rw [decTail, semXIR_seq]
  obtain ⟨b1, b2, hM1⟩ := baryIR_lvm I s hM (Jl := Jl) hJlen hJnd hJlt hBL (fun t ht => by
    rw [hJ t ht, hJl, selJ, getD_take_lt ht])
  have z1 := size_sem I (baryIR (2 ^ 13) 64 (agB dB) (wbB dB) (ebB dB) wB 64 (oB dB)) s
  generalize semXIR I (baryIR (2 ^ 13) 64 (agB dB) (wbB dB) (ebB dB) wB 64 (oB dB)) s = s1
    at b1 b2 hM1 z1
  have hL1 : DecLay dB wB aB fB s1.M.size := by rw [z1]; exact hL
  have hT1 : TabOk s1.M (tbB dB) := tabOk_congr hT fun x h1 h2 => by
    simp only [tbB] at h1 h2
    exact b2 x (by simp only [regs]; omega) (by simp only [wbB]; omega) (by simp only [ebB]; omega)
      (by simp only [oB]; omega)
  rw [semXIR_seq]
  obtain ⟨c1, c2, hM2⟩ := bflyAll_sem I s1 hM1 hL1 hT1 (fun t i => rdK s1.M (oB dB + t * 2 ^ 13 + i))
    (fun _ _ _ _ => rfl)
  have z2 := size_sem I (bflyAll dB) s1
  generalize semXIR I (bflyAll dB) s1 = s2 at c1 c2 hM2 z2
  obtain ⟨d1, d2, hM3⟩ := rowsIR_sem I s2 hM2 (oB := oB dB) (mB := mB dB)
    (by simp only [regs, oB]; omega) (by simp only [oB]; omega) (by simp only [regs, mB]; omega)
    (by simp only [mB]; omega) (by rw [z2, z1]; simp only [mB]; omega)
    (by simp only [oB, mB]; omega)
  refine ⟨fun i hi => ?_, fun x hx hx2 => ?_, hM3⟩
  · -- the message word
    have hl : i / 2 ^ 13 < 64 := by omega
    have hv : i % 2 ^ 13 < 2 ^ 13 := Nat.mod_lt _ (by norm_num)
    have hi' : mB dB + i = mB dB + i / 2 ^ 13 * 2 ^ 13 + i % 2 ^ 13 := by
      have := Nat.div_add_mod' i (2 ^ 13); omega
    set l := i / 2 ^ 13
    set v := i % 2 ^ 13
    have ht : 63 - l < 64 := by omega
    simp only [rdK]
    rw [hi', d1 l hl v hv]
    rw [show wK (rd s2.M (oB dB + (63 - l) * 2 ^ 13 + v)) = rdK s2.M (oB dB + (63 - l) * 2 ^ 13 + v)
      from rfl, c1 (63 - l) ht v hv, show i = l * 2 ^ 13 + v by omega, decWord_split wd α f₁ hv]
    refine coeffsAt_congr ptK nLog 13 0 _ _ (fun j hj => ?_) v hv
    rw [show oB dB + (63 - l) * 2 ^ 13 + j = oB dB + 2 ^ 13 * (63 - l) + j by ring, b1 j hj _ ht]
    refine interpF_congr ptK _ (fun q hq => ?_) j
    have hq' := hJlt q (List.mem_toFinset.1 hq)
    rw [hW q hq' _ ht, rowW]
  · simp only [regs] at hx
    rw [d2 x (by simp only [regs]; omega) (by simp only [mB]; omega),
      c2 x (by simp only [regs]; omega) (by simp only [oB]; omega),
      b2 x (by simp only [regs]; omega) (by simp only [wbB]; omega) (by simp only [ebB]; omega)
        (by simp only [oB]; omega)]

end Lvm.X
end
-- ===== end of `LvmXDecIR3` =====

/-!
# `decIR_sem`: the decoder program computes `decodeRec`

See `LvmXDecIR3` for the program. On a memory holding the word, `α` and `f₁` outside the workspace:
the flag at `okB dB` is `[2^13 ≤ |agreeL|]`; on `decodeRec … = some out` the message at `mB dB` is
`out`; the heap outside the workspace is kept.
-/

namespace Lvm.X

open RecursionFast Finset Lvm.Nb CompPoly.Extension BF64

attribute [local irreducible] entryK storeM

theorem rdE_congr {M M' : Mem} {a : ℕ} (h : ∀ k < 3, rd M' (a + k) = rd M (a + k)) :
    rdE M' a = rdE M a := by
  simp only [rdE, rdK]
  rw [show a = a + 0 from rfl, h 0 (by norm_num), h 1 (by norm_num), h 2 (by norm_num)]

theorem bW_xor_one (b : Bool) : bW b ^^^ 1 = bW (!b) := by cases b <;> decide

/-- **The flag**: `rOk = okB`'s cell `= [2^13 ≤ cnt]`. -/
theorem okIR_sem (I : Array Word) (s : St) (hM : Inv s.M) {dB n : ℕ} (hdB : regs ≤ dB)
    (hdB2 : okB dB < 2 ^ 64) (hdBs : okB dB < s.M.size) (hn : n < 2 ^ 64)
    (hC : rd s.M gCnt = toWord n) :
    rd (semXIR I (okIR dB) s).M rOk = bW (decide (2 ^ 13 ≤ n)) ∧
    rd (semXIR I (okIR dB) s).M (okB dB) = bW (decide (2 ^ 13 ≤ n)) ∧
    (∀ x, regs ≤ x → x ≠ okB dB → rd (semXIR I (okIR dB) s).M x = rd s.M x) ∧
    Inv (semXIR I (okIR dB) s).M := by
  have hs := hM.1
  simp only [regs] at hs hdB
  rw [okIR, semXIR_seq]
  set ps : List Prim := [.const zK (toWord (2 ^ 13)), .op .ltu rOk gCnt zK, .op .xor rOk rOk cOne,
    .const zK (toWord (okB dB))] with hps
  have hM1 := inv_sem I (P := .blk ps) (by simp +decide [hps, WF, Prim.dst, zK, rOk]) hM
  have v1 : rd (semXIR I (.blk ps) s).M rOk = bW (decide (2 ^ 13 ≤ n)) ∧
      rd (semXIR I (.blk ps) s).M zK = toWord (okB dB) := by
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
  obtain ⟨st1, st2, hM2⟩ := store_sem I s1 hM1 (p := zK) (v := rOk) (x := okB dB) (by decide)
    (by decide) v1.2 (by simp only [regs, okB]; omega) hdB2 (by omega)
  refine ⟨?_, by rw [st1, v1.1], fun x hx hx2 => by
    rw [st2 x hx2 (by simp only [regs, cTmp] at *; omega), k1 x hx], hM2⟩
  rw [st2 _ (by simp only [rOk, okB]; omega) (by decide), v1.1]

/-- **The decoder computes `decodeRec`.** -/
theorem decIR_sem (I : Array Word) (s : St) (hM : Inv s.M) {dB wB aB fB : ℕ}
    (hL : DecLay dB wB aB fB s.M.size) (wd : ℕ → ℕ → BF64) (α f₁ : ℕ → Ext3)
    (hW : ∀ q < 2 ^ 15, ∀ t < 64, rdK s.M (wB + 64 * q + t) = wd q t)
    (hA : ∀ i < 6, rdE s.M (aB + 3 * i) = α i)
    (hF : ∀ v < 2 ^ 13, rdE s.M (fB + 3 * v) = f₁ v) :
    rd (semXIR I (decIR dB wB aB fB) s).M (okB dB) =
      bW (decide (2 ^ 13 ≤ (agreeL wd α f₁).length)) ∧
    (∀ out, decodeRec wd α f₁ = some out →
      ∀ i < 2 ^ 19, rdK (semXIR I (decIR dB wB aB fB) s).M (mB dB + i) = out.getD i 0) ∧
    (∀ x, regs ≤ x → (x < dB ∨ dB + 2 ^ 21 ≤ x) →
      rd (semXIR I (decIR dB wB aB fB) s).M x = rd s.M x) ∧
    Inv (semXIR I (decIR dB wB aB fB) s).M := by
  have hL' := hL
  obtain ⟨r, t, z, rW, tW, dW, rA, tA, dA, rF, tF, dF⟩ := hL'
  have hs := hM.1
  simp only [regs] at r rW rA rF hs
  -- 1. the basis table
  rw [decIR, semXIR_seq]
  obtain ⟨w1, w2, hM1, z1⟩ := wtabIR_sem I s hM (tb := tbB dB) (by simp only [regs, tbB]; omega)
    (by simp only [tbB]; omega) (by simp only [tbB]; omega)
  generalize semXIR I (wtabIR (tbB dB)) s = s1 at w1 w2 hM1 z1
  have hT1 : TabOk s1.M (tbB dB) := w1
  -- 2. the `eq` table
  rw [semXIR_seq]
  obtain ⟨q1, q2, hM2⟩ := eqtIR_eqA I s1 hM1 (aB := aB) (qB := qB dB) (by simp only [regs]; omega)
    (by omega) (by simp only [regs, qB]; omega) (by simp only [qB]; omega)
    (by rw [z1]; simp only [qB]; omega) (by simp only [qB]; omega)
  have z2 := size_sem I (eqtIR 6 aB (qB dB)) s1
  generalize semXIR I (eqtIR 6 aB (qB dB)) s1 = s2 at q1 q2 hM2 z2
  have hT2 : TabOk s2.M (tbB dB) := tabOk_congr hT1 fun x h1 h2 => by
    simp only [tbB] at h1 h2
    exact q2 x (by simp only [regs]; omega) (by simp only [qB]; omega)
  have hQ2 : ∀ l < 64, rdE s2.M (qB dB + 3 * l) = eqA α l := fun l hl => by
    rw [q1 l hl]
    refine eqA_congr (fun i hi => ?_) l
    rw [← hA i hi]
    exact rdE_congr fun k hk => w2 _ (by simp only [regs]; omega) (by simp only [tbB]; omega)
  -- the inputs outside the workspace are kept by every phase
  have hL2 : DecLay dB wB aB fB s2.M.size := by rw [z2, z1]; exact hL
  -- 3. `Enc₀(f₁)`
  rw [semXIR_seq]
  obtain ⟨e1, e2, hM3⟩ := encIR_sem I s2 hM2 hL2 hT2
  have z3 := size_sem I (encIR dB fB) s2
  generalize semXIR I (encIR dB fB) s2 = s3 at e1 e2 hM3 z3
  have hout : ∀ x, regs ≤ x → (x < dB ∨ dB + 2 ^ 21 ≤ x) → rd s2.M x = rd s.M x := fun x hx hx2 => by
    rw [q2 x hx (by simp only [qB]; omega), w2 x hx (by simp only [tbB]; omega)]
  have hfB : ∀ v < 2 ^ 13, ∀ c < 3, rdK s2.M (fB + 3 * v + c) = rdK s.M (fB + 3 * v + c) :=
    fun v hv c hc => by simp only [rdK]; rw [hout _ (by simp only [regs]; omega) (by omega)]
  have hW3 : ∀ q < 2 ^ 15, ∀ t < 64, rdK s3.M (wB + 64 * q + t) = wd q t := fun q hq t ht => by
    rw [← hW q hq t ht]; simp only [rdK]
    rw [e2 _ (by simp only [regs]; omega) (by simp only [encB]; omega),
      hout _ (by simp only [regs]; omega) (by omega)]
  have hQ3 : ∀ l < 64, rdE s3.M (qB dB + 3 * l) = eqA α l := fun l hl => by
    rw [← hQ2 l hl]
    exact rdE_congr fun k hk => e2 _ (by simp only [regs, qB]; omega) (by simp only [qB, encB]; omega)
  have hE3 : ∀ q < 2 ^ 15, enc0 f₁ q = mkE (rdK s3.M (encB dB + q)) (rdK s3.M (encB dB + 2 ^ 15 + q))
      (rdK s3.M (encB dB + 2 * 2 ^ 15 + q)) := fun q hq => by
    rw [enc0_coords f₁ (fun c v => rdK s.M (fB + 3 * v + c)) (fun v hv => by rw [← hF v hv]; rfl) q]
    have hc : ∀ c < 3, encN ptK (fun x : Fin (2 ^ 13) => rdK s.M (fB + 3 * x + c)) q =
        rdK s3.M (encB dB + c * 2 ^ 15 + q) := fun c hc => by
      rw [e1 c hc q hq]
      exact congrArg (fun g => encN ptK g q) (funext fun x => (hfB x x.isLt c hc).symm)
    rw [hc 0 (by norm_num), hc 1 (by norm_num), hc 2 (by norm_num), Nat.zero_mul, Nat.add_zero,
      Nat.one_mul]
  have hAg : agreeM s3.M wB (qB dB) (encB dB) (2 ^ 15) = agreeL wd α f₁ :=
    agreeM_eq_agreeL wd α f₁ hW3 hQ3 hE3
  -- 4. the agreement scan
  rw [semXIR_seq]
  obtain ⟨g1, g2, g3, hM4⟩ := agreeIR_sem I s3 hM3 (wB := wB) (qB := qB dB) (eB := encB dB)
    (agB := agB dB) (by simp only [regs]; omega) (by omega) (by simp only [regs, qB]; omega)
    (by simp only [qB]; omega) (by simp only [regs, encB]; omega) (by simp only [encB]; omega)
    (by simp only [regs, agB]; omega) (by simp only [agB]; omega)
    (by rw [z3, z2, z1]; simp only [agB]; omega)
    ⟨by simp only [agB]; omega, by simp only [agB, qB]; omega, by simp only [agB, encB]; omega⟩
  rw [hAg] at g1 g2
  have z4 := size_sem I (agreeIR wB (qB dB) (encB dB) (agB dB)) s3
  generalize semXIR I (agreeIR wB (qB dB) (encB dB) (agB dB)) s3 = s4 at g1 g2 g3 hM4 z4
  have hlen64 : (agreeL wd α f₁).length < 2 ^ 64 := by
    have : (agreeL wd α f₁).length ≤ 2 ^ 15 := by
      rw [agreeL]; exact (List.length_filter_le _ _).trans (by simp)
    omega
  -- 5. the flag
  rw [semXIR_seq]
  obtain ⟨o1, o2, o3, hM5⟩ := okIR_sem I s4 hM4 (dB := dB) (n := (agreeL wd α f₁).length)
    (by simp only [regs]; omega) (by simp only [okB]; omega)
    (by rw [z4, z3, z2, z1]; simp only [okB]; omega) hlen64 g1
  have z5 := size_sem I (okIR dB) s4
  generalize semXIR I (okIR dB) s4 = s5 at o1 o2 o3 hM5 z5
  -- the heap of `s5`
  have hT5 : TabOk s5.M (tbB dB) := tabOk_congr hT2 fun x h1 h2 => by
    simp only [tbB] at h1 h2
    rw [o3 x (by simp only [regs]; omega) (by simp only [okB]; omega),
      g3 x (by simp only [regs]; omega) (by simp only [agB]; omega),
      e2 x (by simp only [regs]; omega) (by simp only [encB]; omega)]
  have h5 : ∀ x, regs ≤ x → (x < dB ∨ dB + 2 ^ 21 ≤ x) → rd s5.M x = rd s.M x := fun x hx hx2 => by
    rw [o3 x hx (by simp only [okB]; omega), g3 x hx (by simp only [agB]; omega),
      e2 x hx (by simp only [encB]; omega), hout x hx hx2]
  -- 6. the branch
  rw [semXIR_ite, o1]
  by_cases hk : 2 ^ 13 ≤ (agreeL wd α f₁).length
  · rw [decide_eq_true hk, if_neg bW_true_ne]
    have hL5 : DecLay dB wB aB fB s5.M.size := by rw [z5, z4, z3, z2, z1]; exact hL
    have hW5 : ∀ q < 2 ^ 15, ∀ t < 64, rdK s5.M (wB + 64 * q + t) = wd q t := fun q hq t ht => by
      rw [← hW q hq t ht]; simp only [rdK]; rw [h5 _ (by simp only [regs]; omega) (by omega)]
    have hJ5 : ∀ t < 2 ^ 13, rd s5.M (agB dB + t) = toWord ((agreeL wd α f₁).getD t 0) := fun t ht => by
      rw [o3 _ (by simp only [regs, agB]; omega) (by simp only [agB, okB]; omega), g2 t (by omega)]
    obtain ⟨d1, d2, hM6⟩ := decTail_sem I s5 hM5 hL5 hT5 wd α f₁ hW5 hk hJ5
    refine ⟨?_, fun out hout' i hi => ?_, fun x hx hx2 => ?_, hM6⟩
    · rw [d2 _ (by simp only [regs, okB]; omega) (by simp only [okB]; omega), o2, decide_eq_true hk]
    · rw [decodeRec, if_pos hk, Option.some.injEq] at hout'
      rw [← hout', d1 i hi, List.getD_eq_getElem _ _ (by simpa using hi), List.getElem_map,
        List.getElem_range]
    · rw [d2 x hx (by omega), h5 x hx hx2]
  · rw [decide_eq_false hk, if_pos bW_false_eq]
    have e6 : semXIR I (.blk []) s5 = s5 := by cases s5; rfl
    rw [e6]
    refine ⟨by rw [o2, decide_eq_false hk], fun out hout' => ?_, h5, hM5⟩
    rw [decodeRec, if_neg hk] at hout'
    exact absurd hout' (by simp)

end Lvm.X
