-- New for lvm2 roll 11 (M′, R11-X): the semantics of the decoders' shape-generic phases. Adapted from
-- `LvmXDec1IR.lean` (`ok1IR_sem`, `bfly1All_sem`, `tr1Row_sem`, `tr1IR_sem`) and `LvmXDecIR2.lean` (`TabOk`,
-- `tabOk_congr`): the flag at `2^kL`, the inverse NTTs of `R` rows of `2^kL` at table dimension `N`, the
-- transpose of `48 × 2^kL`; `tr1Body_sem`, `tr1Loop_sem` are reused.
import LvmMPXNtt5
import LvmMPXCost

/-!
# The generic phases' semantics

* `TabOkN N M tb`: the basis table of dimension `N` at `tb` (`wtabNIR_sem`'s output).
* `okMIR_sem`: the flag `[2^kL ≤ cnt]`.
* **`bflyAllM_sem`**: `R` rows of `2^kL` at `ob` become their novel-basis coefficients (`coeffsAt ptK N kL 0`).
* **`tr1MIR_sem`**: the transpose `M[oB + 48 v + t] = M[ob + 2^kL t + v]`.
-/

namespace Lvm.X

open RecursionFast Finset Lvm.Nb

attribute [local irreducible] entryK storeM

/-- The transpose's address bound. -/
theorem trB {k v i : ℕ} (hv : v < k) (hi : i < 48) : v + k * i < 48 * k := by
  have h := Nat.mul_le_mul_left k (show i + 1 ≤ 48 by omega)
  rw [Nat.mul_succ, Nat.mul_comm k 48] at h; omega

/-- The table hypothesis of the NTTs at dimension `N`. -/
def TabOkN (N : ℕ) (M : Mem) (tb : ℕ) : Prop :=
  ∀ v < N, ∀ i < N, rdK M (tb + N * v + i) = (wRow ptK N v).getD i 0

theorem tabOkN_congr {N : ℕ} {M M' : Mem} {tb : ℕ} (h : TabOkN N M tb)
    (hf : ∀ x, tb ≤ x → x < tb + N * N → rd M' x = rd M x) : TabOkN N M' tb := fun v hv i hi => by
  have : N * v + i < N * N := by
    have := Nat.mul_le_mul_left N (show v + 1 ≤ N by omega); rw [Nat.mul_succ] at this; omega
  simp only [rdK]; rw [hf _ (by omega) (by omega)]; exact h v hv i hi

/-- **The flag**: `rOk` and `ok1B`'s cell `= [2^9 ≤ cnt]`. -/
theorem okMIR_sem (I : Array Word) (s : St) (hM : Inv s.M) {kL ok n : ℕ} (hk : kL < 64) (hdB : regs ≤ ok)
    (hdB2 : ok < 2 ^ 64) (hdBs : ok < s.M.size) (hn : n < 2 ^ 64)
    (hC : rd s.M gCnt = toWord n) :
    rd (semXIR I (okMIR kL ok) s).M rOk = bW (decide (2 ^ kL ≤ n)) ∧
    rd (semXIR I (okMIR kL ok) s).M (ok) = bW (decide (2 ^ kL ≤ n)) ∧
    (∀ x, regs ≤ x → x ≠ ok → rd (semXIR I (okMIR kL ok) s).M x = rd s.M x) ∧
    Inv (semXIR I (okMIR kL ok) s).M := by
  have hs := hM.1
  simp only [regs] at hs hdB
  rw [okMIR, semXIR_seq]
  set ps : List Prim := [.const zK (toWord (2 ^ kL)), .op .ltu rOk gCnt zK, .op .xor rOk rOk cOne,
    .const zK (toWord (ok))] with hps
  have hM1 := inv_sem I (P := .blk ps) (by simp +decide [hps, WF, Prim.dst, zK, rOk]) hM
  have v1 : rd (semXIR I (.blk ps) s).M rOk = bW (decide (2 ^ kL ≤ n)) ∧
      rd (semXIR I (.blk ps) s).M zK = toWord (ok) := by
    rw [sem_blk', hps]; simp only [runPrims, List.foldl, Prim.run]
    refine ⟨?_, ?_⟩ <;>
    simp (disch := first | decide | (simp only [size_set, zK, rOk]; omega)) only [rd_set_self, rd_set_ne]
    rw [hC, ltW_toWord hn (pow_lt64 hk), show rd s.M cOne = 1 from hM.2 0 (by decide), eval_xor,
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
  obtain ⟨st1, st2, hM2⟩ := store_sem I s1 hM1 (p := zK) (v := rOk) (x := ok) (by decide)
    (by decide) v1.2 (by simp only [regs, ok1B]; omega) hdB2 (by omega)
  refine ⟨?_, by rw [st1, v1.1], fun x hx hx2 => by
    rw [st2 x hx2 (by simp only [regs, cTmp] at *; omega), k1 x hx], hM2⟩
  rw [st2 _ (by simp only [rOk, ok1B]; omega) (by decide), v1.1]


/-- **One transposed row** `v < 2^9`: `oB + 48 v + t := ob + v + 2^9 t` (`t < 48`), `yL := v + 1`. -/
theorem tr1RowM_sem (I : Array Word) (s : St) (hM : Inv s.M) {kL ob oB v : ℕ} (hk : kL < 64) (hv : v < 2 ^ kL)
    (hob : regs ≤ ob) (hob2 : ob + 48 * 2 ^ kL < 2 ^ 64) (hoB : regs ≤ oB)
    (hoB2 : oB + 48 * 2 ^ kL < 2 ^ 64) (hoBs : oB + 48 * 2 ^ kL ≤ s.M.size)
    (hdisj : ob + 48 * 2 ^ kL ≤ oB ∨ oB + 48 * 2 ^ kL ≤ ob) (hL : rd s.M yL = toWord v) :
    (∀ t < 48, rd (semXIR I (tr1RowM kL ob oB) s).M (oB + 48 * v + t) = rd s.M (ob + v + 2 ^ kL * t)) ∧
    rd (semXIR I (tr1RowM kL ob oB) s).M yL = toWord (v + 1) ∧
    (∀ r, regs ≤ r → (r < oB + 48 * v ∨ oB + 48 * v + 48 ≤ r) →
      rd (semXIR I (tr1RowM kL ob oB) s).M r = rd s.M r) ∧
    Inv (semXIR I (tr1RowM kL ob oB) s).M := by
  have hs := hM.1
  simp only [regs] at hs hob hoB
  rw [tr1RowM, semXIR_seq]
  set ps : List Prim := [.const yK (toWord ob), .op .add ySr yL yK, .const yK 48, .op .mul yDs yL yK,
      .const yK (toWord oB), .op .add yDs yDs yK, .const yStr (toWord (2 ^ kL))] with hps
  have w0 : WF (.blk ps) := by simp +decide [hps, WF, Prim.dst, yK, ySr, yDs, yStr]
  have hM0 := inv_sem I w0 hM
  have z0 := size_sem I (.blk ps) s
  have r0 : rd (semXIR I (.blk ps) s).M ySr = toWord (ob + v) ∧
      rd (semXIR I (.blk ps) s).M yDs = toWord (oB + 48 * v) ∧
      rd (semXIR I (.blk ps) s).M yStr = toWord (2 ^ kL) ∧ rd (semXIR I (.blk ps) s).M yL = toWord v := by
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
  obtain ⟨m1, m2, hM1⟩ := tr1Loop_sem I s0 hM0 (n := 48) (src := ob + v) (str := 2 ^ kL)
    (dst := oB + 48 * v) (by norm_num) (fun i hi => by have := trB hv hi; omega) (by simp only [regs]; omega)
    (by omega) (by omega) (fun i hi => by have := trB hv hi; omega) (fun i hi => by simp only [regs]; omega) p1 p2 p3
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
theorem tr1MIR_sem (I : Array Word) (s : St) (hM : Inv s.M) {kL ob oB : ℕ} (hk : kL < 64)
    (hob : regs ≤ ob) (hob2 : ob + 48 * 2 ^ kL < 2 ^ 64) (hoB : regs ≤ oB)
    (hoB2 : oB + 48 * 2 ^ kL < 2 ^ 64) (hoBs : oB + 48 * 2 ^ kL ≤ s.M.size)
    (hd : ob + 48 * 2 ^ kL ≤ oB ∨ oB + 48 * 2 ^ kL ≤ ob) :
    (∀ v < 2 ^ kL, ∀ t < 48, rd (semXIR I (tr1MIR kL ob oB) s).M (oB + 48 * v + t) =
      rd s.M (ob + 2 ^ kL * t + v)) ∧
    (∀ x, regs ≤ x → (x < oB ∨ oB + 48 * 2 ^ kL ≤ x) → rd (semXIR I (tr1MIR kL ob oB) s).M x = rd s.M x) ∧
    Inv (semXIR I (tr1MIR kL ob oB) s).M := by
  have hs := hM.1
  simp only [regs] at hs hob hoB
  rw [tr1MIR, semXIR_seq]
  have w0 : WF (.blk [.const yL 0, .const yN2 (toWord (2 ^ kL))]) := by
    simp +decide [WF, Prim.dst, yL, yN2]
  have hM0 := inv_sem I w0 hM
  have z0 := size_sem I (.blk [.const yL 0, .const yN2 (toWord (2 ^ kL))]) s
  have r0 : rd (semXIR I (.blk [.const yL 0, .const yN2 (toWord (2 ^ kL))]) s).M yL = toWord 0 ∧
      rd (semXIR I (.blk [.const yL 0, .const yN2 (toWord (2 ^ kL))]) s).M yN2 = toWord (2 ^ kL) := by
    rw [sem_blk']; simp only [runPrims, List.foldl, Prim.run]
    refine ⟨?_, ?_⟩ <;>
    simp (disch := first | decide | (simp only [size_set, yL, yN2]; omega)) only [rd_set_self, rd_set_ne] <;> rfl
  have k0 : ∀ r, regs ≤ r →
      rd (semXIR I (.blk [.const yL 0, .const yN2 (toWord (2 ^ kL))]) s).M r = rd s.M r :=
    fun r hr => by
      simp only [regs] at hr
      refine rd_blk_of_not_dst I _ s ?_
      simp only [List.mem_cons, List.mem_nil_iff, or_false]
      rintro p (rfl | rfl) <;> simp only [Prim.dst, yL, yN2] <;> omega
  generalize semXIR I (.blk [.const yL 0, .const yN2 (toWord (2 ^ kL))]) s = s0 at hM0 z0 r0 k0
  obtain ⟨l0, n0⟩ := r0
  let P : ℕ → St → Prop := fun j s' => Inv s'.M ∧ s'.M.size = s.M.size ∧ rd s'.M yL = toWord j ∧
    (∀ v < j, ∀ t < 48, rd s'.M (oB + 48 * v + t) = rd s.M (ob + 2 ^ kL * t + v)) ∧
    (∀ r, regs ≤ r → (r < oB ∨ oB + 48 * j ≤ r) → rd s'.M r = rd s.M r)
  have hE : ∀ i, i ≠ yC2 → i ≠ cTmp → rd (entryK yC2 yN2 (toWord (2 ^ kL)) s0.M) i = rd s0.M i :=
    fun i h1 h2 => entryK_frame _ (Ne.symm h1) (Ne.symm h2)
  have h0 : P 0 ⟨entryK yC2 yN2 (toWord (2 ^ kL)) s0.M, s0.o⟩ := by
    refine ⟨inv_entryK hM0 (by decide), by simp only [size_entryK, z0], ?_,
      fun v hv => absurd hv (by omega), fun r hr _ => ?_⟩ <;> dsimp only
    · rw [hE _ (by decide) (by decide), l0]
    · simp only [regs] at hr
      rw [hE _ (by simp only [yC2]; omega) (by simp only [cTmp]; omega), k0 r (by simp only [regs]; omega)]
  have hstep : ∀ j s', j < 2 ^ kL → P j s' → P (j + 1) (decS yC2 (semXIR I (tr1RowM kL ob oB) s')) := by
    rintro j s' hj ⟨i1, i2, i3, i4, i5⟩
    obtain ⟨b1, b2, b3, hM'⟩ := tr1RowM_sem I s' i1 (ob := ob) (oB := oB) hk hj
      (by simp only [regs]; omega) hob2 (by simp only [regs]; omega) hoB2 (by omega) hd i3
    have hd' : ∀ x, x ≠ yC2 → rd (decS yC2 (semXIR I (tr1RowM kL ob oB) s')).M x =
        rd (semXIR I (tr1RowM kL ob oB) s').M x := fun x hx => rd_decS (Ne.symm hx) _
    have hx : ∀ x, regs ≤ x → x ≠ yC2 := fun x hx => by simp only [regs, yC2] at *; omega
    refine ⟨inv_decS hM' (by decide), by rw [size_decS, size_sem, i2], by rw [hd' _ (by decide), b2],
      fun v hv t ht => ?_, fun r hr hr2 => ?_⟩
    · rw [hd' _ (hx _ (by simp only [regs]; omega))]
      by_cases hvj : v = j
      · subst hvj
        have := trB hj ht
        rw [b1 t ht, i5 _ (by simp only [regs]; omega) (by omega), Nat.add_right_comm]
      · rw [b3 _ (by simp only [regs]; omega) (by omega), i4 v (by omega) t ht]
    · rw [hd' _ (hx r hr), b3 r hr (by omega), i5 r hr (by omega)]
  have hfin := loopK_run I (tr1RowM kL ob oB) P s0 hM0 (c := yC2) (n := yN2) (K := 2 ^ kL) (by decide)
    (by decide) (by decide) n0 (pow_lt64 hk) h0 hstep
  exact ⟨hfin.2.2.2.1, fun r hr hr2 => hfin.2.2.2.2 r hr (by omega), hfin.1⟩


/-- **The inverse NTT of `R` rows** of `2^kL` coefficients at `ob` (table dimension `N`). -/
theorem bflyAllM_sem (I : Array Word) (s : St) (hM : Inv s.M) {N kL R tb ob : ℕ} (hN : N ≤ 64)
    (hkN : kL ≤ N) (hR : R < 2 ^ 64) (hob : regs ≤ ob) (hob2 : ob + R * 2 ^ kL < 2 ^ 64)
    (hsz : ob + R * 2 ^ kL ≤ s.M.size) (htb : regs ≤ tb) (htb2 : tb + N * N < 2 ^ 64)
    (hdisj : tb + N * N ≤ ob ∨ ob + R * 2 ^ kL ≤ tb) (hT : TabOkN N s.M tb) (Y : ℕ → ℕ → BF64)
    (hY : ∀ t < R, ∀ i < 2 ^ kL, rdK s.M (ob + t * 2 ^ kL + i) = Y t i) :
    (∀ t < R, ∀ i < 2 ^ kL, rdK (semXIR I (bflyAllM N kL R tb ob) s).M (ob + t * 2 ^ kL + i) =
      coeffsAt ptK N kL 0 (Y t) i) ∧
    (∀ x, regs ≤ x → (x < ob ∨ ob + R * 2 ^ kL ≤ x) →
      rd (semXIR I (bflyAllM N kL R tb ob) s).M x = rd s.M x) ∧
    Inv (semXIR I (bflyAllM N kL R tb ob) s).M := by
  have hs := hM.1
  have hK0 : 0 < 2 ^ kL := by positivity
  simp only [regs] at hob hs htb
  rw [bflyAllM, semXIR_seq]
  have w0 : WF (.blk [.const zT 0, .const zN (toWord R)]) := by simp +decide [WF, Prim.dst, zT, zN]
  have hM0 := inv_sem I w0 hM
  have z0 := size_sem I (.blk [.const zT 0, .const zN (toWord R)]) s
  have r0 : rd (semXIR I (.blk [.const zT 0, .const zN (toWord R)]) s).M zT = toWord 0 ∧
      rd (semXIR I (.blk [.const zT 0, .const zN (toWord R)]) s).M zN = toWord R := by
    rw [sem_blk']; simp only [runPrims, List.foldl, Prim.run]
    refine ⟨?_, ?_⟩ <;>
    simp (disch := first | decide | (simp only [size_set, zT, zN]; omega)) only [rd_set_self, rd_set_ne] <;> rfl
  have k0 : ∀ x, regs ≤ x → rd (semXIR I (.blk [.const zT 0, .const zN (toWord R)]) s).M x = rd s.M x :=
    fun x hx => rd_blk_of_not_dst I _ s (by
      simp only [List.mem_cons, List.mem_nil_iff, or_false]
      rintro p (rfl | rfl) <;> simp only [Prim.dst, zT, zN] <;> simp only [regs] at hx <;> omega)
  generalize semXIR I (.blk [.const zT 0, .const zN (toWord R)]) s = s0 at hM0 z0 r0 k0
  obtain ⟨t0, n0⟩ := r0
  let P : ℕ → St → Prop := fun j s' => Inv s'.M ∧ s'.M.size = s.M.size ∧ rd s'.M zT = toWord j ∧
    (∀ t < j, ∀ i < 2 ^ kL, rdK s'.M (ob + t * 2 ^ kL + i) = coeffsAt ptK N kL 0 (Y t) i) ∧
    (∀ x, regs ≤ x → (x < ob ∨ ob + j * 2 ^ kL ≤ x) → rd s'.M x = rd s.M x)
  have hE : ∀ i, i ≠ zC → i ≠ cTmp → rd (entryK zC zN (toWord R) s0.M) i = rd s0.M i :=
    fun i h1 h2 => entryK_frame _ (Ne.symm h1) (Ne.symm h2)
  have h0 : P 0 ⟨entryK zC zN (toWord R) s0.M, s0.o⟩ := by
    refine ⟨inv_entryK hM0 (by decide), by simp only [size_entryK, z0], ?_,
      fun t ht => absurd ht (by omega), fun x hx _ => ?_⟩ <;> dsimp only
    · rw [hE _ (by decide) (by decide), t0]
    · simp only [regs] at hx
      rw [hE _ (by simp only [zC]; omega) (by simp only [cTmp]; omega), k0 x (by simp only [regs]; omega)]
  have hstep : ∀ j s', j < R → P j s' → P (j + 1) (decS zC (semXIR I (bflyRowM N kL tb ob) s')) := by
    rintro j s' hj ⟨i1, i2, i3, i4, i5⟩
    rw [bflyRowM, semXIR_seq]
    set A := ob + j * 2 ^ kL with hA
    have hjR : j * 2 ^ kL + 2 ^ kL ≤ R * 2 ^ kL := by
      rw [← Nat.succ_mul]; exact Nat.mul_le_mul_right _ hj
    have hs' := i1.1
    simp only [regs] at hs'
    have a1 : rd (semXIR I (.blk [.const zK (toWord (2 ^ kL)), .op .mul rA0 zT zK,
        .const zK (toWord ob), .op .add rA0 rA0 zK]) s').M rA0 = toWord A := by
      rw [sem_blk']; simp only [runPrims, List.foldl, Prim.run]
      simp (disch := first | decide | (simp only [size_set, zK, rA0, zT]; omega)) only [rd_set_self, rd_set_ne]
      rw [i3, mul_toWord, add_toWord, hA, Nat.add_comm]
    have a2 : ∀ x, x ≠ zK → x ≠ rA0 → rd (semXIR I (.blk [.const zK (toWord (2 ^ kL)),
        .op .mul rA0 zT zK, .const zK (toWord ob), .op .add rA0 rA0 zK]) s').M x = rd s'.M x :=
      fun x h1 h2 => rd_blk_of_not_dst I _ s' (by
        simp only [List.mem_cons, List.mem_nil_iff, or_false, forall_eq_or_imp, forall_eq, Prim.dst]
        exact ⟨Ne.symm h1, Ne.symm h2, Ne.symm h1, Ne.symm h2⟩)
    have hM1 := inv_sem I (P := .blk [.const zK (toWord (2 ^ kL)), .op .mul rA0 zT zK,
      .const zK (toWord ob), .op .add rA0 rA0 zK]) (by simp +decide [WF, Prim.dst, zK, rA0]) i1
    have z1 := size_sem I (.blk [.const zK (toWord (2 ^ kL)), .op .mul rA0 zT zK,
      .const zK (toWord ob), .op .add rA0 rA0 zK]) s'
    generalize semXIR I (.blk [.const zK (toWord (2 ^ kL)), .op .mul rA0 zT zK,
      .const zK (toWord ob), .op .add rA0 rA0 zK]) s' = s1 at a1 a2 hM1 z1
    rw [semXIR_seq]
    have hx1 : ∀ x, regs ≤ x → x ≠ zK ∧ x ≠ rA0 := fun x hx => by
      simp only [regs, zK, rA0] at *; omega
    have h1 : ∀ x, regs ≤ x → rd s1.M x = rd s'.M x := fun x hx => a2 x (hx1 x hx).1 (hx1 x hx).2
    have hT1 : TabOkN N s1.M tb := tabOkN_congr hT fun x hx1' hx2' => by
      rw [h1 x (by simp only [regs]; omega)]
      exact i5 x (by simp only [regs]; omega) (by omega)
    have hY1 : ∀ i < 2 ^ kL, rdK s1.M (A + i) = Y j i := fun i hi => by
      simp only [rdK]
      rw [h1 _ (by simp only [regs]; omega), hA, i5 _ (by simp only [regs]; omega) (Or.inr (by omega))]
      exact hY j hj i hi
    obtain ⟨-, b2, hM2⟩ := bflyNIR_sem I s1 hM1 hN (A := A) (tb := tb) (ℓ := kL) (Y := Y j) hkN
      (by simp only [regs]; omega) (by omega) (by omega) (by simp only [regs]; omega) htb2
      (by omega) a1 hT1 hY1
    have b1 := bflyNIR_coeffs I s1 hM1 hN (A := A) (tb := tb) (ℓ := kL) (Y := Y j) hkN
      (by simp only [regs]; omega) (by omega) (by omega) (by simp only [regs]; omega) htb2
      (by omega) a1 hT1 hY1
    have q2 : rd (semXIR I (bflyNIR N kL tb) s1).M zT = toWord j := by
      rw [frame I _ s1 (wf_bflyNIR N kL tb) hM1 zT (by decide) (bflyNIR_nw_hi N kL tb (by decide)),
        a2 _ (by decide) (by decide), i3]
    have z2 := size_sem I (bflyNIR N kL tb) s1
    generalize semXIR I (bflyNIR N kL tb) s1 = s2 at b1 b2 hM2 q2 z2
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
    · have hxr : regs ≤ ob + t * 2 ^ kL + i := by simp only [regs] at *; omega
      simp only [rdK]
      rw [hd _ (hx3 _ hxr).1, c2 _ (hx3 _ hxr).2]
      by_cases htj : t = j
      · subst htj; exact b1 i hi
      · have ht' : t < j := by omega
        have : t * 2 ^ kL + 2 ^ kL ≤ j * 2 ^ kL := by
          rw [← Nat.succ_mul]; exact Nat.mul_le_mul_right _ ht'
        rw [b2 _ hxr (by left; omega), h1 _ hxr]
        exact i4 t ht' i hi
    · have e : (j + 1) * 2 ^ kL = j * 2 ^ kL + 2 ^ kL := by ring
      rw [e] at hx2
      have hx4 : x < A ∨ A + 2 ^ kL ≤ x := by omega
      have hx5 : x < ob ∨ ob + j * 2 ^ kL ≤ x := by omega
      rw [hd _ (hx3 x hx).1, c2 _ (hx3 x hx).2, b2 x hx hx4, h1 x hx, i5 x hx hx5]
  have hfin := loopK_run I (bflyRowM N kL tb ob) P s0 hM0 (c := zC) (n := zN) (K := R) (by decide)
    (by decide) (by decide) n0 hR h0 hstep
  exact ⟨hfin.2.2.2.1, fun x hx hx2 => hfin.2.2.2.2 x hx hx2, hfin.1⟩

end Lvm.X
