/- `LvmXCopyOff` (GOLF2 off-path move, group 23 of 48): declarations that the certificate `certified`
   does not use, moved here verbatim (same names, same namespaces and context) from LvmXCopy,
   so that `Solution`'s import closure need not elaborate them. Import this module where they are needed;
   the name -> module map is GOLF2's moved.tsv. -/
import LvmXCopy

-- ===== from `LvmXCopy` =====

section
namespace Lvm.X
open RecursionFast
attribute [local irreducible] entryK storeM

/-- **One message row** `l < 64`: `mB + l·2^13 + v := oB + (63 − l)·2^13 + v`, `yL := l + 1`. -/
theorem msgRow_sem (I : Array Word) (s : St) (hM : Inv s.M) {oB mB l : ℕ} (hl : l < 64)
    (hoB : regs ≤ oB) (hoB2 : oB + 2 ^ 19 < 2 ^ 64) (hmB : regs ≤ mB) (hmB2 : mB + 2 ^ 19 < 2 ^ 64)
    (hms : mB + 2 ^ 19 ≤ s.M.size) (hdisj : oB + 2 ^ 19 ≤ mB ∨ mB + 2 ^ 19 ≤ oB)
    (hL : rd s.M yL = toWord l) :
    (∀ v < 2 ^ 13, rd (semXIR I (msgRow oB mB) s).M (mB + l * 2 ^ 13 + v) =
      rd s.M (oB + (63 - l) * 2 ^ 13 + v)) ∧
    rd (semXIR I (msgRow oB mB) s).M yL = toWord (l + 1) ∧
    (∀ r, regs ≤ r → (r < mB + l * 2 ^ 13 ∨ mB + l * 2 ^ 13 + 2 ^ 13 ≤ r) →
      rd (semXIR I (msgRow oB mB) s).M r = rd s.M r) ∧
    Inv (semXIR I (msgRow oB mB) s).M := by
  have hs := hM.1
  simp only [regs] at hs hoB hmB
  have hl2 : l * 2 ^ 13 + 2 ^ 13 ≤ 2 ^ 19 := by (clear * - hl; omega)
  have hl3 : (63 - l) * 2 ^ 13 + 2 ^ 13 ≤ 2 ^ 19 :=
    calc (63 - l) * 2 ^ 13 + 2 ^ 13 ≤ 63 * 2 ^ 13 + 2 ^ 13 := by gcongr; exact Nat.sub_le 63 l
      _ = 2 ^ 19 := by norm_num
  rw [msgRow, semXIR_seq]
  set ps : List Prim := [.const yK 63, .op .sub ySr yK yL, .const yK (toWord (2 ^ 13)),
    .op .mul ySr ySr yK, .const yK (toWord oB), .op .add ySr ySr yK, .const yK (toWord (2 ^ 13)),
    .op .mul yDs yL yK, .const yK (toWord mB), .op .add yDs yDs yK, .const yStr 1] with hps
  have w0 : WF (.blk ps) := by simp +decide [hps, WF, Prim.dst, yK, ySr, yDs, yStr]
  have hM0 := inv_sem I w0 hM
  have z0 := size_sem I (.blk ps) s
  have r0 : rd (semXIR I (.blk ps) s).M ySr = toWord (oB + (63 - l) * 2 ^ 13) ∧
      rd (semXIR I (.blk ps) s).M yDs = toWord (mB + l * 2 ^ 13) ∧
      rd (semXIR I (.blk ps) s).M yStr = toWord 1 ∧ rd (semXIR I (.blk ps) s).M yL = toWord l := by
    rw [sem_blk', hps]; simp only [runPrims, List.foldl, Prim.run]
    refine ⟨?_, ?_, ?_, ?_⟩ <;>
    simp (disch := first | decide | (simp only [size_set, yK, ySr, yDs, yStr, yL]; omega)) only [rd_set_self, rd_set_ne]
    · rw [hL, show (63 : Word) = toWord 63 from rfl, sub_toWord (by norm_num) (by (clear * - hl; omega)),
        mul_toWord, add_toWord, Nat.add_comm]
    · rw [hL, mul_toWord, add_toWord, Nat.add_comm]
    · rfl
    · exact hL
  have k0 : ∀ r, regs ≤ r → rd (semXIR I (.blk ps) s).M r = rd s.M r := fun r hr => by
    simp only [regs] at hr
    refine rd_blk_of_not_dst I _ s ?_
    simp only [hps, List.mem_cons, List.mem_nil_iff, or_false]
    rintro p (rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl) <;>
      simp only [Prim.dst, yK, ySr, yDs, yStr] <;> (clear * - hr; omega)
  generalize semXIR I (.blk ps) s = s0 at hM0 z0 r0 k0
  obtain ⟨p1, p2, p3, p4⟩ := r0
  rw [semXIR_seq]
  obtain ⟨m1, m2, hM1⟩ := mcpLoop_sem I s0 hM0 (n := 2 ^ 13) (src := oB + (63 - l) * 2 ^ 13)
    (str := 1) (dst := mB + l * 2 ^ 13) (by norm_num) (by (clear * - hoB hoB2 hl3; omega)) (by simp only [regs]; (clear * - hl hmB hmB2; omega))
    (by (clear * - hl hmB hmB2; omega)) (by (clear * - hl hms z0; omega)) (fun i hi => by (clear * - hl hoB hoB2 hmB hmB2 hdisj hi; omega)) (fun i hi => by simp only [regs]; (clear * - hoB hoB2 hl3 hi; omega)) p1 p2 p3
  have z1 := size_sem I (mcpLoop (2 ^ 13)) s0
  have l1 : rd (semXIR I (mcpLoop (2 ^ 13)) s0).M yL = toWord l := by
    rw [frame I _ s0 (by simp +decide [mcpLoop, mcpBody, WF, Writes, Prim.dst, ySr, yDs, yV, yN,
      yC, cTmp, regs]) hM0 yL (by decide) (by simp +decide [mcpLoop, mcpBody, Writes, Prim.dst,
        ySr, yDs, yV, yN, yC, yL, cTmp]), p4]
  generalize semXIR I (mcpLoop (2 ^ 13)) s0 = s1 at m1 m2 hM1 z1 l1
  have b2 : ∀ r, r ≠ yL → rd (semXIR I (.blk [.op .add yL yL cOne]) s1).M r = rd s1.M r :=
    fun r hr => rd_blk_of_not_dst I _ s1 (by simp [Prim.dst]; exact Ne.symm hr)
  have hx : ∀ x, regs ≤ x → x ≠ yL := fun x hx => by simp only [regs, yL] at *; (clear * - hx; omega)
  refine ⟨fun v hv => ?_, ?_, fun r hr hr2 => ?_, inv_sem I (P := .blk [.op .add yL yL cOne])
    (by simp +decide [WF, Prim.dst, yL]) hM1⟩
  · rw [b2 _ (hx _ (by simp only [regs]; (clear * - hl hmB hmB2 hv; omega))), m1 v hv, Nat.one_mul,
      k0 _ (by simp only [regs]; (clear * - hoB hoB2 hl3 hv; omega))]
  · have hs1 := hM1.1
    simp only [regs] at hs1
    rw [sem_blk']; simp only [runPrims, List.foldl, Prim.run]
    rw [rd_set_self (by simp only [yL]; (clear * - hs z0 z1; omega)), l1, show rd s1.M cOne = 1 from hM1.2 0 (by decide),
      add_one_toWord]
  · rw [b2 _ (hx r hr), m2 r (keepC_of_regs hr) hr2, k0 r hr]

/-- **The message reorder**: row `l < 64` of the message at `mB + l·2^13` is row `63 − l` at
`oB`; the heap outside `[mB, mB + 2^19)` is kept. -/
theorem rowsIR_sem (I : Array Word) (s : St) (hM : Inv s.M) {oB mB : ℕ}
    (hoB : regs ≤ oB) (hoB2 : oB + 2 ^ 19 < 2 ^ 64) (hmB : regs ≤ mB) (hmB2 : mB + 2 ^ 19 < 2 ^ 64)
    (hms : mB + 2 ^ 19 ≤ s.M.size) (hdisj : oB + 2 ^ 19 ≤ mB ∨ mB + 2 ^ 19 ≤ oB) :
    (∀ l < 64, ∀ v < 2 ^ 13, rd (semXIR I (rowsIR oB mB) s).M (mB + l * 2 ^ 13 + v) =
      rd s.M (oB + (63 - l) * 2 ^ 13 + v)) ∧
    (∀ r, regs ≤ r → (r < mB ∨ mB + 2 ^ 19 ≤ r) → rd (semXIR I (rowsIR oB mB) s).M r = rd s.M r) ∧
    Inv (semXIR I (rowsIR oB mB) s).M := by
  have hs := hM.1
  simp only [regs] at hs hoB hmB
  rw [rowsIR, semXIR_seq]
  have w0 : WF (.blk [.const yL 0, .const yN2 64]) := by simp +decide [WF, Prim.dst, yL, yN2]
  have hM0 := inv_sem I w0 hM
  have z0 := size_sem I (.blk [.const yL 0, .const yN2 64]) s
  have r0 : rd (semXIR I (.blk [.const yL 0, .const yN2 64]) s).M yL = toWord 0 ∧
      rd (semXIR I (.blk [.const yL 0, .const yN2 64]) s).M yN2 = toWord 64 := by
    rw [sem_blk']; simp only [runPrims, List.foldl, Prim.run]
    refine ⟨?_, ?_⟩ <;>
    simp (disch := first | decide | (simp only [size_set, yL, yN2]; omega)) only [rd_set_self, rd_set_ne] <;> rfl
  have k0 : ∀ r, regs ≤ r → rd (semXIR I (.blk [.const yL 0, .const yN2 64]) s).M r = rd s.M r :=
    fun r hr => by
      simp only [regs] at hr
      refine rd_blk_of_not_dst I _ s ?_
      simp only [List.mem_cons, List.mem_nil_iff, or_false]
      rintro p (rfl | rfl) <;> simp only [Prim.dst, yL, yN2] <;> (clear * - hr; omega)
  generalize semXIR I (.blk [.const yL 0, .const yN2 64]) s = s0 at hM0 z0 r0 k0
  obtain ⟨l0, n0⟩ := r0
  let P : ℕ → St → Prop := fun j s' => Inv s'.M ∧ s'.M.size = s.M.size ∧ rd s'.M yL = toWord j ∧
    (∀ l < j, ∀ v < 2 ^ 13, rd s'.M (mB + l * 2 ^ 13 + v) = rd s.M (oB + (63 - l) * 2 ^ 13 + v)) ∧
    (∀ r, regs ≤ r → (r < mB ∨ mB + j * 2 ^ 13 ≤ r) → rd s'.M r = rd s.M r)
  have hE : ∀ i, i ≠ yC2 → i ≠ cTmp → rd (entryK yC2 yN2 (toWord 64) s0.M) i = rd s0.M i :=
    fun i h1 h2 => entryK_frame _ (Ne.symm h1) (Ne.symm h2)
  have h0 : P 0 ⟨entryK yC2 yN2 (toWord 64) s0.M, s0.o⟩ := by
    refine ⟨inv_entryK hM0 (by decide), by simp only [size_entryK, z0], ?_,
      fun l hl => absurd hl (by (clear * - hl; omega)), fun r hr _ => ?_⟩ <;> dsimp only
    · rw [hE _ (by decide) (by decide), l0]
    · simp only [regs] at hr
      rw [hE _ (by simp only [yC2]; (clear * - hr; omega)) (by simp only [cTmp]; (clear * - hr; omega)), k0 r (by simp only [regs]; omega)]
  have hstep : ∀ j s', j < 64 → P j s' → P (j + 1) (decS yC2 (semXIR I (msgRow oB mB) s')) := by
    rintro j s' hj ⟨i1, i2, i3, i4, i5⟩
    obtain ⟨b1, b2, b3, hM'⟩ := msgRow_sem I s' i1 (oB := oB) (mB := mB) hj
      (by simp only [regs]; omega) hoB2 (by simp only [regs]; omega) hmB2 (by (clear * - hms z0 h0 i2; omega)) hdisj i3
    have hd : ∀ x, x ≠ yC2 → rd (decS yC2 (semXIR I (msgRow oB mB) s')).M x =
        rd (semXIR I (msgRow oB mB) s').M x := fun x hx => rd_decS (Ne.symm hx) _
    have hx : ∀ x, regs ≤ x → x ≠ yC2 := fun x hx => by simp only [regs, yC2] at *; (clear * - hx; omega)
    refine ⟨inv_decS hM' (by decide), by rw [size_decS, size_sem, i2], by rw [hd _ (by decide), b2],
      fun l hl v hv => ?_, fun r hr hr2 => ?_⟩
    · rw [hd _ (hx _ (by simp only [regs]; (clear * - hmB hmB2 hj hl hv; omega)))]
      by_cases hlj : l = j
      · subst hlj
        rw [b1 v hv, i5 _ (by simp only [regs]; (clear * - hoB hoB2 hv; omega)) (by (clear * - hdisj hv hj; omega))]
      · rw [b3 _ (by simp only [regs]; (clear * - hmB hmB2 hj hl hv; omega)) (by
          rcases Nat.lt_or_gt_of_ne hlj with h | h
          · left; nlinarith
          · (clear * - hl h; omega)), i4 l (by (clear * - hl hlj; omega)) v hv]
    · rw [hd _ (hx r hr), b3 r hr (by rcases hr2 with h | h <;> [left; right] <;> nlinarith),
        i5 r hr (by rcases hr2 with h | h <;> [left; right] <;> nlinarith)]
  have hfin := loopK_run I (msgRow oB mB) P s0 hM0 (c := yC2) (n := yN2) (K := 64) (by decide)
    (by decide) (by decide) n0 (by norm_num) h0 hstep
  exact ⟨hfin.2.2.2.1, fun r hr hr2 => hfin.2.2.2.2 r hr (by omega), hfin.1⟩

end Lvm.X
end
