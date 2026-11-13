-- New for lvm2 roll 11 (M′, R11-X): the level-≥1 decoder program `dec1MPIR N nL kL` computes `decode1G N nL kL`.
-- Adapted from `LvmXDec1IR.lean` (`Dec1Lay`, `enc1C_sem`, `enc1IR_sem`) and `LvmXDec1IR2.lean` (`dec1Tail_sem`,
-- `dec1IR_sem`) at a generic shape: `2^nL` positions, `2^kL` coefficients, table dimension `N`, the workspace of
-- `LvmMPXDecIR` (`q1M`, `ok1M`, `wb1M`, `eb1M`, `ag1M`, `enc1M`, `ob1M`).
import LvmMPXDecSem
import LvmMPXAgree1
import LvmMPXInterp

/-!
# The level-≥1 decoder on the machine, generic in the shape

**`dec1MPIR_sem`**: on a memory holding the word `wd` at `wB + 48 q + t` (`q < 2^nL`), `α_i` at `aB + 3i` and
`f(v)` at `fB + 3v` (`rdE`), with the layout `Dec1MLay`:

* the cell `ok1M dB` holds `[2^kL ≤ |agree1G nL kL wd α f|]`, i.e. `decode1G N nL kL wd α f ≠ none`;
* if `decode1G N nL kL wd α f = some g`, then `rdE (oB + 3v) = g v` for `v < 2^(kL+4)`;
* the heap outside the workspace and the output is kept.

`decMP2IR_sem`, `decMP1IR_sem`: M′'s levels 2 and 1 (`decodeMP2`, `decodeMP1`).
-/

namespace Lvm.X

open RecursionFast Finset Lvm.Nb CompPoly.Extension BF64

attribute [local irreducible] entryK storeM

/-- **The level-≥1 decoder's memory layout** at the shape `(N, nL, kL)`: the workspace
`[dB, dB + ws1M nL kL)`; the word (`wB`, `48·2^nL` words), `α` (`aB`, 12 words) and `f` (`fB`, `3·2^kL`) outside
it; the output (`oB`, `3·2^(kL+4)`) inside the memory and outside the workspace; addresses below `2^60`. -/
structure Dec1MLay (N nL kL dB wB aB fB oB sz : ℕ) : Prop where
  hN : N ≤ 64
  hN1 : 1 ≤ N
  hkn : kL ≤ nL
  hnN : nL ≤ N
  r : regs ≤ dB
  t : dB + ws1M nL kL < 2 ^ 60
  z : dB + ws1M nL kL ≤ sz
  rW : regs ≤ wB
  tW : wB + 48 * 2 ^ nL < 2 ^ 60
  dW : wB + 48 * 2 ^ nL ≤ dB ∨ dB + ws1M nL kL ≤ wB
  rA : regs ≤ aB
  tA : aB + 12 < 2 ^ 60
  dA : aB + 12 ≤ dB ∨ dB + ws1M nL kL ≤ aB
  rF : regs ≤ fB
  tF : fB + 3 * 2 ^ kL < 2 ^ 60
  dF : fB + 3 * 2 ^ kL ≤ dB ∨ dB + ws1M nL kL ≤ fB
  rO : regs ≤ oB
  tO : oB + 3 * 2 ^ (kL + 4) < 2 ^ 60
  zO : oB + 3 * 2 ^ (kL + 4) ≤ sz
  dO : oB + 3 * 2 ^ (kL + 4) ≤ dB ∨ dB + ws1M nL kL ≤ oB

/-- The arithmetic facts of the layout, as linear facts on the atoms `2^kL`, `2^nL`. -/
theorem Dec1MLay.facts {N nL kL dB wB aB fB oB sz : ℕ} (hL : Dec1MLay N nL kL dB wB aB fB oB sz) :
    0 < 2 ^ kL ∧ 2 ^ kL ≤ 2 ^ nL ∧ 2 ^ (kL + 1) = 2 * 2 ^ kL ∧ 2 ^ (kL + 4) = 16 * 2 ^ kL ∧
      N * N ≤ 2 ^ 12 ∧ kL < 61 ∧ nL < 61 ∧ ws1M nL kL = 2 ^ 13 + 2 * 2 ^ kL + 5 * 2 ^ nL + 48 * 2 ^ kL := by
  have h1 := hL.hN
  have hkn := hL.hkn
  have hk := Nat.pow_le_pow_right (show 0 < 2 by norm_num) hL.hkn
  have hNN : N * N ≤ 64 * 64 := Nat.mul_le_mul h1 h1
  have hn : nL < 61 := by
    have := hL.tW
    by_contra h
    have : 2 ^ 61 ≤ 2 ^ nL := Nat.pow_le_pow_right (by norm_num) (by omega)
    omega
  refine ⟨by positivity, hk, by ring, by ring, by omega, by omega, hn, ?_⟩
  rw [ws1M, pow_succ]; ring

/-! ## `Enc(f)` -/

/-- **One coordinate of `Enc(f)`** at `enc1M + c·2^nL`. -/
theorem enc1MC_sem (I : Array Word) (s : St) (hM : Inv s.M) {N nL kL dB wB aB fB oB c : ℕ}
    (hL : Dec1MLay N nL kL dB wB aB fB oB s.M.size) (hc : c < 3) (hT : TabOkN N s.M dB) :
    (∀ j < 2 ^ nL, rdK (semXIR I (enc1MC N nL kL dB fB c) s).M (enc1M nL kL dB + c * 2 ^ nL + j) =
      encN ptK (fun x : Fin (2 ^ kL) => rdK s.M (fB + 3 * x + c)) j) ∧
    (∀ x, regs ≤ x → (x < enc1M nL kL dB + c * 2 ^ nL ∨ enc1M nL kL dB + c * 2 ^ nL + 2 ^ nL ≤ x) →
      rd (semXIR I (enc1MC N nL kL dB fB c) s).M x = rd s.M x) ∧
    Inv (semXIR I (enc1MC N nL kL dB fB c) s).M := by
  obtain ⟨k0, hkn', e1, e4, hNN, hk61, hn61, hws⟩ := hL.facts
  obtain ⟨hN, hN1, hkn, hnN, r, t, z, rW, tW, dW, rA, tA, dA, rF, tF, dF, rO, tO, zO, dO⟩ := hL
  have hs := hM.1
  simp only [regs] at r rW rA rF hs
  have hc2 : c * 2 ^ nL + 2 ^ nL ≤ 3 * 2 ^ nL := by
    rw [← Nat.succ_mul]; exact Nat.mul_le_mul_right _ (by omega)
  set A := enc1M nL kL dB + c * 2 ^ nL with hA
  have hAd : dB + 2 ^ 12 ≤ A ∧ A + 2 ^ nL ≤ dB + ws1M nL kL := by
    simp only [hA, enc1M, ag1M]; constructor <;> omega
  rw [enc1MC, semXIR_seq]
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

/-- **`Enc(f)`'s three coordinates** at `enc1M + c·2^nL + j`. -/
theorem enc1MIR_sem (I : Array Word) (s : St) (hM : Inv s.M) {N nL kL dB wB aB fB oB : ℕ}
    (hL : Dec1MLay N nL kL dB wB aB fB oB s.M.size) (hT : TabOkN N s.M dB) :
    (∀ c < 3, ∀ j < 2 ^ nL, rdK (semXIR I (enc1MIR N nL kL dB fB) s).M (enc1M nL kL dB + c * 2 ^ nL + j) =
      encN ptK (fun x : Fin (2 ^ kL) => rdK s.M (fB + 3 * x + c)) j) ∧
    (∀ x, regs ≤ x → (x < enc1M nL kL dB ∨ enc1M nL kL dB + 3 * 2 ^ nL ≤ x) →
      rd (semXIR I (enc1MIR N nL kL dB fB) s).M x = rd s.M x) ∧
    Inv (semXIR I (enc1MIR N nL kL dB fB) s).M := by
  have hL' := hL
  obtain ⟨k0, hkn', e1, e4, hNN, hk61, hn61, hws⟩ := hL.facts
  obtain ⟨hN, hN1, hkn, hnN, r, t, z, rW, tW, dW, rA, tA, dA, rF, tF, dF, rO, tO, zO, dO⟩ := hL'
  simp only [regs] at r rF
  rw [enc1MIR, semXIR_seq]
  obtain ⟨a1, a2, hM1⟩ := enc1MC_sem I s hM hL (c := 0) (by norm_num) hT
  have z1 := size_sem I (enc1MC N nL kL dB fB 0) s
  generalize semXIR I (enc1MC N nL kL dB fB 0) s = s1 at a1 a2 hM1 z1
  have hL1 : Dec1MLay N nL kL dB wB aB fB oB s1.M.size := by rw [z1]; exact hL
  have hF1 : ∀ x, regs ≤ x → (x < enc1M nL kL dB ∨ enc1M nL kL dB + 2 ^ nL ≤ x) → rd s1.M x = rd s.M x :=
    fun x hx hx2 => a2 x hx (by simpa using hx2)
  have hT1 : TabOkN N s1.M dB := tabOkN_congr hT fun x h1 h2 =>
    hF1 x (by simp only [regs] at *; omega) (by simp only [enc1M, ag1M] at *; omega)
  rw [semXIR_seq]
  obtain ⟨b1, b2, hM2⟩ := enc1MC_sem I s1 hM1 hL1 (c := 1) (by norm_num) hT1
  have z2 := size_sem I (enc1MC N nL kL dB fB 1) s1
  generalize semXIR I (enc1MC N nL kL dB fB 1) s1 = s2 at b1 b2 hM2 z2
  have hL2 : Dec1MLay N nL kL dB wB aB fB oB s2.M.size := by rw [z2]; exact hL1
  have hT2 : TabOkN N s2.M dB := tabOkN_congr hT1 fun x h1 h2 =>
    b2 x (by simp only [regs] at *; omega) (by simp only [enc1M, ag1M] at *; omega)
  obtain ⟨c1, c2, hM3⟩ := enc1MC_sem I s2 hM2 hL2 (c := 2) (by norm_num) hT2
  have hfB : ∀ x c, x < 2 ^ kL → c < 3 → regs ≤ fB + 3 * x + c ∧
      (fB + 3 * x + c < enc1M nL kL dB ∨ enc1M nL kL dB + 3 * 2 ^ nL ≤ fB + 3 * x + c) := fun x c hx hc => by
    simp only [regs, enc1M, ag1M] at *; omega
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
      rw [c2 _ (by simp only [regs, enc1M, ag1M] at *; omega) (by simp only [enc1M, ag1M] at *; omega),
        b2 _ (by simp only [regs, enc1M, ag1M] at *; omega) (by simp only [enc1M, ag1M] at *; omega)]
      exact a1 j hj
    · simp only [rdK]
      rw [c2 _ (by simp only [regs, enc1M, ag1M] at *; omega) (by simp only [enc1M, ag1M] at *; omega)]
      rw [show wK (rd s2.M (enc1M nL kL dB + 1 * 2 ^ nL + j)) = rdK s2.M (enc1M nL kL dB + 1 * 2 ^ nL + j)
        from rfl, b1 j hj]
      congr 1; funext x; exact ee1 x 1 (by norm_num)
    · rw [c1 j hj]
      congr 1; funext x; exact ee2 x 2 (by norm_num)
  · rw [c2 x hx (by omega), b2 x hx (by omega), a2 x hx (by omega)]

/-! ## The decoding proper -/

theorem coef1G_getD_take {L : List ℕ} {n t : ℕ} (ht : t < n) : (L.take n).getD t 0 = L.getD t 0 :=
  getD_take_lt ht

/-- **The decoding proper**: on a list of `≥ 2^kL` agreeing positions at `ag1M`, the decoded message at `oB`. -/
theorem dec1MTail_sem (I : Array Word) (s : St) (hM : Inv s.M) {N nL kL dB wB aB fB oB : ℕ}
    (hL : Dec1MLay N nL kL dB wB aB fB oB s.M.size) (hT : TabOkN N s.M dB) (wd : ℕ → ℕ → BF64)
    (α f : ℕ → Ext3) (hW : ∀ q < 2 ^ nL, ∀ t < 48, rdK s.M (wB + 48 * q + t) = wd q t)
    (hlen : 2 ^ kL ≤ (agree1G nL kL wd α f).length)
    (hJ : ∀ t < 2 ^ kL, rd s.M (ag1M kL dB + t) = toWord ((agree1G nL kL wd α f).getD t 0)) :
    (∀ v < 2 ^ (kL + 4), rdE (semXIR I (dec1MTail N nL kL dB wB oB) s).M (oB + 3 * v) =
      dec1G N nL kL wd α f v) ∧
    (∀ x, regs ≤ x → (x < wb1M dB ∨ dB + ws1M nL kL ≤ x) → (x < oB ∨ oB + 3 * 2 ^ (kL + 4) ≤ x) →
      rd (semXIR I (dec1MTail N nL kL dB wB oB) s).M x = rd s.M x) ∧
    Inv (semXIR I (dec1MTail N nL kL dB wB oB) s).M := by
  have hL' := hL
  obtain ⟨k0, hkn', e1, e4, hNN, hk61, hn61, hws⟩ := hL.facts
  have n0 : 0 < 2 ^ nL := by positivity
  obtain ⟨hN, hN1, hkn, hnN, r, t, z, rW, tW, dW, rA, tA, dA, rF, tF, dF, rO, tO, zO, dO⟩ := hL'
  simp only [regs] at r rW rO
  set Jl := (agree1G nL kL wd α f).take (2 ^ kL) with hJl
  have hJlen : Jl.length = 2 ^ kL := by
    rw [hJl, List.length_take, Nat.min_eq_left hlen]
  have hJnd : Jl.Nodup := (nodup_filter_range _ _).sublist (List.take_sublist _ _)
  have hJlt : ∀ j ∈ Jl, j < 2 ^ nL := fun j hj => by
    have := List.mem_of_mem_take hj
    rw [agree1G, List.mem_filter, List.mem_range] at this
    exact this.1
  have hBL : BaryLayP (2 ^ nL) (2 ^ kL) 48 (ag1M kL dB) (wb1M dB) (eb1M kL dB) wB 48 (ob1M nL kL dB)
      s.M.size := by
    refine ⟨by omega, by norm_num, hkn', le_rfl, ?_, ?_, ?_, ?_, rW, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
      ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> (try simp only [regs, ag1M, wb1M, eb1M, ob1M, enc1M]) <;> omega
  have hget : ∀ t < 2 ^ kL, Jl.getD t 0 < 2 ^ nL := fun t ht => by
    rw [List.getD_eq_getElem _ _ (by omega)]
    exact hJlt _ (List.getElem_mem (l := Jl) (n := t) (by omega))
  rw [dec1MTail, semXIR_seq]
  obtain ⟨b1, b2, hM1⟩ := baryIR_semP I s hM (Jl := Jl) hBL hget (fun t ht => by
    rw [hJ t ht, hJl, getD_take_lt ht])
  have z1 := size_sem I (baryIR (2 ^ kL) 48 (ag1M kL dB) (wb1M dB) (eb1M kL dB) wB 48 (ob1M nL kL dB)) s
  generalize semXIR I (baryIR (2 ^ kL) 48 (ag1M kL dB) (wb1M dB) (eb1M kL dB) wB 48 (ob1M nL kL dB)) s
    = s1 at b1 b2 hM1 z1
  have hT1 : TabOkN N s1.M dB := tabOkN_congr hT fun x h1 h2 => by
    exact b2 x (by simp only [regs]; omega) (by simp only [wb1M]; omega)
      (by simp only [eb1M]; omega) (by simp only [ob1M, enc1M, ag1M]; omega)
  rw [semXIR_seq]
  obtain ⟨c1, c2, hM2⟩ := bflyAllM_sem I s1 hM1 hN (kL := kL) (R := 48) (tb := dB) (ob := ob1M nL kL dB)
    (by omega) (by norm_num) (by simp only [regs, ob1M, enc1M, ag1M]; omega)
    (by simp only [ob1M, enc1M, ag1M]; omega) (by rw [z1]; simp only [ob1M, enc1M, ag1M]; omega)
    (by simp only [regs]; omega) (by omega) (by simp only [ob1M, enc1M, ag1M]; omega) hT1
    (fun t i => rdK s1.M (ob1M nL kL dB + t * 2 ^ kL + i)) (fun _ _ _ _ => rfl)
  have z2 := size_sem I (bflyAllM N kL 48 dB (ob1M nL kL dB)) s1
  generalize semXIR I (bflyAllM N kL 48 dB (ob1M nL kL dB)) s1 = s2 at c1 c2 hM2 z2
  obtain ⟨d1, d2, hM3⟩ := tr1MIR_sem I s2 hM2 (kL := kL) (ob := ob1M nL kL dB) (oB := oB) (by omega)
    (by simp only [regs, ob1M, enc1M, ag1M]; omega) (by simp only [ob1M, enc1M, ag1M]; omega)
    (by simp only [regs]; omega) (by omega) (by rw [z2, z1]; omega)
    (by simp only [ob1M, enc1M, ag1M]; omega)
  generalize semXIR I (tr1MIR kL (ob1M nL kL dB) oB) s2 = s3 at d1 d2 hM3
  refine ⟨fun v hv => ?_, fun x hx hx2 hx3 => ?_, hM3⟩
  · -- the decoded entry `v = u + 16 v'`
    have hval : ∀ c < 3, rdK s3.M (oB + 3 * v + c) = coef1G N nL kL wd α f (3 * (v % 16) + c) (v / 16) := by
      intro c hc
      have hu : v % 16 < 16 := Nat.mod_lt _ (by norm_num)
      have hv' : v / 16 < 2 ^ kL := by omega
      have e : oB + 3 * v + c = oB + 48 * (v / 16) + (3 * (v % 16) + c) := by omega
      simp only [rdK]
      rw [e, d1 (v / 16) hv' (3 * (v % 16) + c) (by omega),
        show ob1M nL kL dB + 2 ^ kL * (3 * (v % 16) + c) + v / 16 =
          ob1M nL kL dB + (3 * (v % 16) + c) * 2 ^ kL + v / 16 by ring,
        show wK (rd s2.M (ob1M nL kL dB + (3 * (v % 16) + c) * 2 ^ kL + v / 16)) =
          rdK s2.M (ob1M nL kL dB + (3 * (v % 16) + c) * 2 ^ kL + v / 16) from rfl,
        c1 (3 * (v % 16) + c) (by omega) (v / 16) hv', coef1G, ← hJl]
      refine coeffsAt_congr ptK N kL 0 _ _ (fun j hj => ?_) (v / 16) hv'
      rw [show ob1M nL kL dB + (3 * (v % 16) + c) * 2 ^ kL + j =
          ob1M nL kL dB + 2 ^ kL * (3 * (v % 16) + c) + j by ring,
        b1 j hj _ (by omega), show (2 : ℕ) ^ kL = Jl.length from hJlen.symm,
        baryValK_eqP (P := 2 ^ nL) (by omega) hJnd hJlt (by omega)]
      refine interpF_congr ptK _ (fun q hq => ?_) j
      have hq' := hJlt q (List.mem_toFinset.1 hq)
      rw [hW q hq' _ (by omega), lane1]
    have h0 := hval 0 (by norm_num)
    rw [Nat.add_zero, Nat.add_zero] at h0
    rw [rdE, h0, hval 1 (by norm_num), hval 2 (by norm_num), dec1G]
  · simp only [regs] at hx
    rw [d2 x (by simp only [regs]; omega) (by omega),
      c2 x (by simp only [regs]; omega) (by simp only [ob1M, enc1M, ag1M, wb1M] at *; omega),
      b2 x (by simp only [regs]; omega) (by simp only [wb1M] at *; omega)
        (by simp only [eb1M, wb1M] at *; omega) (by simp only [ob1M, enc1M, ag1M, wb1M] at *; omega)]

/-! ## The whole program -/

/-- **The level-≥1 decoder program computes `decode1G N nL kL`.** -/
theorem dec1MPIR_sem (I : Array Word) (s : St) (hM : Inv s.M) {N nL kL dB wB aB fB oB : ℕ}
    (hL : Dec1MLay N nL kL dB wB aB fB oB s.M.size) (wd : ℕ → ℕ → BF64) (α f : ℕ → Ext3)
    (hW : ∀ q < 2 ^ nL, ∀ t < 48, rdK s.M (wB + 48 * q + t) = wd q t)
    (hA : ∀ i < 4, rdE s.M (aB + 3 * i) = α i)
    (hF : ∀ v < 2 ^ kL, rdE s.M (fB + 3 * v) = f v) :
    rd (semXIR I (dec1MPIR N nL kL dB wB aB fB oB) s).M (ok1M dB) =
      bW (decide (2 ^ kL ≤ (agree1G nL kL wd α f).length)) ∧
    (∀ g, decode1G N nL kL wd α f = some g →
      ∀ v < 2 ^ (kL + 4), rdE (semXIR I (dec1MPIR N nL kL dB wB aB fB oB) s).M (oB + 3 * v) = g v) ∧
    (∀ x, regs ≤ x → (x < dB ∨ dB + ws1M nL kL ≤ x) → (x < oB ∨ oB + 3 * 2 ^ (kL + 4) ≤ x) →
      rd (semXIR I (dec1MPIR N nL kL dB wB aB fB oB) s).M x = rd s.M x) ∧
    Inv (semXIR I (dec1MPIR N nL kL dB wB aB fB oB) s).M := by
  have hL' := hL
  obtain ⟨k0, hkn', e1, e4, hNN, hk61, hn61, hws⟩ := hL.facts
  have n0 : 0 < 2 ^ nL := by positivity
  obtain ⟨hN, hN1, hkn, hnN, r, t, z, rW, tW, dW, rA, tA, dA, rF, tF, dF, rO, tO, zO, dO⟩ := hL'
  have hs := hM.1
  simp only [regs] at r rW rA rF rO hs
  -- 1. the basis table
  rw [dec1MPIR, semXIR_seq]
  obtain ⟨w1, w2, hM1, z1⟩ := wtabNIR_sem I s hM hN hN1 (tb := dB) (by simp only [regs]; omega)
    (by omega) (by omega)
  generalize semXIR I (wtabNIR N dB) s = s1 at w1 w2 hM1 z1
  have hT1 : TabOkN N s1.M dB := w1
  -- 2. the `eq` table
  rw [semXIR_seq]
  obtain ⟨q1, q2, hM2⟩ := eqtIR_sem I s1 hM1 (ℓ := 4) (aB := aB) (qB := q1M dB) (by norm_num)
    (by simp only [regs]; omega) (by omega) (by simp only [regs, q1M]; omega)
    (by simp only [q1M]; omega) (by rw [z1]; simp only [q1M]; omega) (by simp only [q1M]; omega)
  have z2 := size_sem I (eqtIR 4 aB (q1M dB)) s1
  generalize semXIR I (eqtIR 4 aB (q1M dB)) s1 = s2 at q1 q2 hM2 z2
  have q2' : ∀ x, regs ≤ x → (x < q1M dB ∨ q1M dB + 48 ≤ x) → rd s2.M x = rd s1.M x :=
    fun x hx hx2 => q2 x (.inr (lt_of_lt_of_le (by decide) hx)) (by omega)
  have hT2 : TabOkN N s2.M dB := tabOkN_congr hT1 fun x h1 h2 => by
    exact q2' x (by simp only [regs]; omega) (by simp only [q1M]; omega)
  have hQ2 : ∀ u < 16, rdE s2.M (q1M dB + 3 * u) = eqA1 α u := fun u hu => by
    rw [q1 u hu]
    refine eqA1_congr (fun i hi => ?_) u
    rw [← hA i hi]
    exact rdE_congr fun k hk => w2 _ (by simp only [regs]; omega) (by omega)
  have hL2 : Dec1MLay N nL kL dB wB aB fB oB s2.M.size := by rw [z2, z1]; exact hL
  -- 3. `Enc(f)`
  rw [semXIR_seq]
  obtain ⟨ee1, ee2, hM3⟩ := enc1MIR_sem I s2 hM2 hL2 hT2
  have z3 := size_sem I (enc1MIR N nL kL dB fB) s2
  generalize semXIR I (enc1MIR N nL kL dB fB) s2 = s3 at ee1 ee2 hM3 z3
  have hout : ∀ x, regs ≤ x → (x < dB ∨ dB + ws1M nL kL ≤ x) → rd s2.M x = rd s.M x := fun x hx hx2 => by
    rw [q2' x hx (by simp only [q1M]; omega), w2 x hx (by omega)]
  have hfB : ∀ v < 2 ^ kL, ∀ c < 3, rdK s2.M (fB + 3 * v + c) = rdK s.M (fB + 3 * v + c) :=
    fun v hv c hc => by simp only [rdK]; rw [hout _ (by simp only [regs]; omega) (by omega)]
  have hW3 : ∀ q < 2 ^ nL, ∀ t < 48, rdK s3.M (wB + 48 * q + t) = wd q t := fun q hq t ht => by
    have : 48 * q + t < 48 * 2 ^ nL := by omega
    rw [← hW q hq t ht]; simp only [rdK]
    rw [ee2 _ (by simp only [regs]; omega) (by simp only [enc1M, ag1M]; omega),
      hout _ (by simp only [regs]; omega) (by omega)]
  have hQ3 : ∀ u < 16, rdE s3.M (q1M dB + 3 * u) = eqA1 α u := fun u hu => by
    rw [← hQ2 u hu]
    exact rdE_congr fun k hk => ee2 _ (by simp only [regs, q1M]; omega)
      (by simp only [q1M, enc1M, ag1M]; omega)
  have hE3 : ∀ q < 2 ^ nL, encG kL f q = mkE (rdK s3.M (enc1M nL kL dB + q))
      (rdK s3.M (enc1M nL kL dB + 2 ^ nL + q)) (rdK s3.M (enc1M nL kL dB + 2 * 2 ^ nL + q)) := by
    intro q hq
    rw [encG_coords kL f (fun c v => rdK s.M (fB + 3 * v + c)) (fun v hv => by rw [← hF v hv]; rfl) q]
    have hc : ∀ c < 3, encN ptK (fun x : Fin (2 ^ kL) => rdK s.M (fB + 3 * x + c)) q =
        rdK s3.M (enc1M nL kL dB + c * 2 ^ nL + q) := fun c hc => by
      rw [ee1 c hc q hq]
      exact congrArg (fun g => encN ptK g q) (funext fun x => (hfB x x.isLt c hc).symm)
    rw [hc 0 (by norm_num), hc 1 (by norm_num), hc 2 (by norm_num), Nat.zero_mul, Nat.add_zero,
      Nat.one_mul]
  have hAg : agree1NM s3.M (2 ^ nL) wB (q1M dB) (enc1M nL kL dB) (2 ^ nL) = agree1G nL kL wd α f :=
    agree1NM_eq_agree1G wd α f hW3 hQ3 hE3
  -- 4. the agreement scan
  rw [semXIR_seq]
  obtain ⟨g1, g2, g3, hM4⟩ := agree1NIR_sem I s3 hM3 (st := 2 ^ nL) (wB := wB) (qB := q1M dB)
    (eB := enc1M nL kL dB) (agB := ag1M kL dB) (by simp only [regs]; omega) (by omega)
    (by simp only [regs, q1M]; omega) (by simp only [q1M]; omega)
    (by simp only [regs, enc1M, ag1M]; omega) (by simp only [enc1M, ag1M]; omega)
    (by simp only [regs, ag1M]; omega) (by simp only [ag1M]; omega)
    (by rw [z3, z2, z1]; simp only [ag1M]; omega)
    ⟨by simp only [ag1M]; omega, by simp only [ag1M, q1M]; omega, by simp only [ag1M, enc1M]; omega⟩
  rw [hAg] at g1 g2
  have z4 := size_sem I (agree1NIR (2 ^ nL) wB (q1M dB) (enc1M nL kL dB) (ag1M kL dB)) s3
  generalize semXIR I (agree1NIR (2 ^ nL) wB (q1M dB) (enc1M nL kL dB) (ag1M kL dB)) s3 = s4
    at g1 g2 g3 hM4 z4
  have hlenL : (agree1G nL kL wd α f).length ≤ 2 ^ nL := by
    rw [agree1G]; exact (List.length_filter_le _ _).trans (by simp)
  have hlen64 : (agree1G nL kL wd α f).length < 2 ^ 64 := by omega
  -- 5. the flag
  rw [semXIR_seq]
  obtain ⟨o1, o2, o3, hM5⟩ := okMIR_sem I s4 hM4 (kL := kL) (ok := ok1M dB)
    (n := (agree1G nL kL wd α f).length) (by omega) (by simp only [regs, ok1M]; omega)
    (by simp only [ok1M]; omega) (by rw [z4, z3, z2, z1]; simp only [ok1M]; omega) hlen64 g1
  have z5 := size_sem I (okMIR kL (ok1M dB)) s4
  generalize semXIR I (okMIR kL (ok1M dB)) s4 = s5 at o1 o2 o3 hM5 z5
  -- the heap of `s5`
  have hT5 : TabOkN N s5.M dB := tabOkN_congr hT2 fun x h1 h2 => by
    rw [o3 x (by simp only [regs]; omega) (by simp only [ok1M]; omega),
      g3 x (by simp only [regs]; omega) (by simp only [ag1M]; omega),
      ee2 x (by simp only [regs]; omega) (by simp only [enc1M, ag1M]; omega)]
  have h5 : ∀ x, regs ≤ x → (x < dB ∨ dB + ws1M nL kL ≤ x) → rd s5.M x = rd s.M x := fun x hx hx2 => by
    rw [o3 x hx (by simp only [ok1M]; omega), g3 x hx (by simp only [ag1M]; omega),
      ee2 x hx (by simp only [enc1M, ag1M]; omega), hout x hx hx2]
  -- 6. the branch
  rw [semXIR_ite, o1]
  by_cases hk : 2 ^ kL ≤ (agree1G nL kL wd α f).length
  · rw [decide_eq_true hk, if_neg bW_true_ne]
    have hL5 : Dec1MLay N nL kL dB wB aB fB oB s5.M.size := by rw [z5, z4, z3, z2, z1]; exact hL
    have hW5 : ∀ q < 2 ^ nL, ∀ t < 48, rdK s5.M (wB + 48 * q + t) = wd q t := fun q hq t ht => by
      have : 48 * q + t < 48 * 2 ^ nL := by omega
      rw [← hW q hq t ht]; simp only [rdK]; rw [h5 _ (by simp only [regs]; omega) (by omega)]
    have hJ5 : ∀ t < 2 ^ kL, rd s5.M (ag1M kL dB + t) = toWord ((agree1G nL kL wd α f).getD t 0) :=
      fun t ht => by
        rw [o3 _ (by simp only [regs, ag1M]; omega) (by simp only [ag1M, ok1M]; omega), g2 t (by omega)]
    obtain ⟨d1, d2, hM6⟩ := dec1MTail_sem I s5 hM5 hL5 hT5 wd α f hW5 hk hJ5
    refine ⟨?_, fun g hout' v hv => ?_, fun x hx hx2 hx3 => ?_, hM6⟩
    · rw [d2 _ (by simp only [regs, ok1M]; omega) (by simp only [ok1M, wb1M]; omega)
        (by simp only [ok1M]; omega), o2, decide_eq_true hk]
    · rw [decode1G, if_pos hk, Option.some.injEq] at hout'
      rw [← hout', d1 v hv]
      exact (if_pos hv).symm
    · rw [d2 x hx (by simp only [wb1M]; omega) hx3, h5 x hx hx2]
  · rw [decide_eq_false hk, if_pos bW_false_eq]
    have e6 : semXIR I (.blk []) s5 = s5 := by cases s5; rfl
    rw [e6]
    refine ⟨by rw [o2, decide_eq_false hk], fun g hout' => ?_, fun x hx hx2 _ => h5 x hx hx2, hM5⟩
    rw [decode1G, if_neg hk] at hout'
    exact absurd hout' (by simp)

/-! ## M′'s levels 2 and 1 -/

/-- **M′'s level-2 decoder program computes `decodeMP2`** (`2^13` positions, `k = 2^9`). -/
theorem decMP2IR_sem (I : Array Word) (s : St) (hM : Inv s.M) {dB wB aB fB oB : ℕ}
    (hL : Dec1MLay 19 13 9 dB wB aB fB oB s.M.size) (wd : ℕ → ℕ → BF64) (α f : ℕ → Ext3)
    (hW : ∀ q < 2 ^ 13, ∀ t < 48, rdK s.M (wB + 48 * q + t) = wd q t)
    (hA : ∀ i < 4, rdE s.M (aB + 3 * i) = α i)
    (hF : ∀ v < 2 ^ 9, rdE s.M (fB + 3 * v) = f v) :
    rd (semXIR I (decMP2IR dB wB aB fB oB) s).M (ok1M dB) =
      bW (decide (2 ^ 9 ≤ (agree1G 13 9 wd α f).length)) ∧
    (∀ g, decodeMP2 wd α f = some g →
      ∀ v < 2 ^ 13, rdE (semXIR I (decMP2IR dB wB aB fB oB) s).M (oB + 3 * v) = g v) ∧
    (∀ x, regs ≤ x → (x < dB ∨ dB + ws1M 13 9 ≤ x) → (x < oB ∨ oB + 3 * 2 ^ 13 ≤ x) →
      rd (semXIR I (decMP2IR dB wB aB fB oB) s).M x = rd s.M x) ∧
    Inv (semXIR I (decMP2IR dB wB aB fB oB) s).M :=
  dec1MPIR_sem I s hM hL wd α f hW hA hF

/-- **M′'s level-1 decoder program computes `decodeMP1`** (`2^16` positions, `k = 2^13`). -/
theorem decMP1IR_sem (I : Array Word) (s : St) (hM : Inv s.M) {dB wB aB fB oB : ℕ}
    (hL : Dec1MLay 19 16 13 dB wB aB fB oB s.M.size) (wd : ℕ → ℕ → BF64) (α f : ℕ → Ext3)
    (hW : ∀ q < 2 ^ 16, ∀ t < 48, rdK s.M (wB + 48 * q + t) = wd q t)
    (hA : ∀ i < 4, rdE s.M (aB + 3 * i) = α i)
    (hF : ∀ v < 2 ^ 13, rdE s.M (fB + 3 * v) = f v) :
    rd (semXIR I (decMP1IR dB wB aB fB oB) s).M (ok1M dB) =
      bW (decide (2 ^ 13 ≤ (agree1G 16 13 wd α f).length)) ∧
    (∀ g, decodeMP1 wd α f = some g →
      ∀ v < 2 ^ 17, rdE (semXIR I (decMP1IR dB wB aB fB oB) s).M (oB + 3 * v) = g v) ∧
    (∀ x, regs ≤ x → (x < dB ∨ dB + ws1M 16 13 ≤ x) → (x < oB ∨ oB + 3 * 2 ^ 17 ≤ x) →
      rd (semXIR I (decMP1IR dB wB aB fB oB) s).M x = rd s.M x) ∧
    Inv (semXIR I (decMP1IR dB wB aB fB oB) s).M :=
  dec1MPIR_sem I s hM hL wd α f hW hA hF

/-- **A level-2 layout exists** (non-vacuity): workspace at `2^22`, word at `2^23`, `α` at `2^20`, `f` at
`2^20 + 64`, output at `2^21`. -/
theorem decMP2Lay_example (sz : ℕ) (hsz : 2 ^ 24 ≤ sz) :
    Dec1MLay 19 13 9 (2 ^ 22) (2 ^ 23) (2 ^ 20) (2 ^ 20 + 64) (2 ^ 21) sz := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    (try simp only [regs, ws1M]) <;> norm_num <;> omega

/-- **A level-1 layout exists** (non-vacuity), same placement. -/
theorem decMP1Lay_example (sz : ℕ) (hsz : 2 ^ 24 ≤ sz) :
    Dec1MLay 19 16 13 (2 ^ 22) (2 ^ 23) (2 ^ 20) (2 ^ 20 + 64) (2 ^ 21) sz := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    (try simp only [regs, ws1M]) <;> norm_num <;> omega

end Lvm.X
