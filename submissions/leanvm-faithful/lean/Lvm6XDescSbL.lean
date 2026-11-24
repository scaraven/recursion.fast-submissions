-- lvm6 X8a (X7b §3 item 1): the agreement-set builder's lanes on the machine. A `loopK` whose count
-- register holds `m ≤ K` runs `m` times (`loopK_runLe`); one lane `q` of `sbIR` ORs `word(q, j) ⊕ enc_q(j)` into
-- flag `j` (`laneB_sem`), so after `q` lanes flag `j` is zero iff lanes `< q` agree at `j` (`FlagInv`). New.
import Lvm6XDescBuild

/-!
# The builder's lanes

* **`entryK_min`**, **`loopK_runLe`**: the `loopK` counter is `min(M[n], K)`; with `M[n] = m ≤ K` the loop runs
  `m` times (the builder's lane loop: `occ ≤ K` lanes, `K` charged).
* **`cmpLoop_sem`**: the comparison loop of a lane, `flag[j] := flag[j] ||| (word[j] ⊕ row[j])`.
* **`laneB_sem`**: one lane (copy of the column's `d + 1` coefficients, zero pad, `fwdNIR`, comparison) keeps
  `SrcEq` (the heap outside `[sA B, fdEnd B ℓ)`), the basis table, and advances `FlagInv` from `q` to `q + 1`.
-/

set_option autoImplicit false

namespace Lvm6.X

open RecursionFast Lvm.X Lvm.Nb Lvm6.FD Finset

/-! ## `loopK` with a count below its bound -/

/-- The `loopK` counter when the count register holds `m ≤ K`. -/
theorem entryK_min {c n m K : ℕ} {M : Mem} (hM : Inv M) (hc : 4 < c) (hcr : c < regs) (hn : n ≠ c)
    (hnT : n ≠ cTmp) (hN : rd M n = toWord m) (hmK : m ≤ K) (hK : K < 2 ^ 64) :
    rd (entryK c n (toWord K) M) c = toWord m := by
  have hs := hM.1
  simp only [regs] at hs hcr
  have hm : m < 2 ^ 64 := lt_of_le_of_lt hmK hK
  unfold entryK; dsimp only
  have h1 : rd (M.setIfInBounds c (toWord K)) n = toWord m := by rw [rd_set_ne (Ne.symm hn), hN]
  have h2 : rd (M.setIfInBounds c (toWord K)) c = toWord K := rd_set_self (by omega)
  rw [h1, h2]
  have hsz : cTmp < (M.setIfInBounds c (toWord K)).size := by simp only [size_set, cTmp]; omega
  rcases Nat.lt_or_ge m K with h | h
  · have hl : XOp.ltu.eval (toWord m) (toWord K) = 1 := by
      simp only [XOp.eval, (toWord_lt_toWord hm hK).2 h, if_true]
    have h3 : rd ((M.setIfInBounds c (toWord K)).setIfInBounds cTmp 1) cTmp = 1 := rd_set_self hsz
    have h4 : rd ((M.setIfInBounds c (toWord K)).setIfInBounds cTmp 1) n = toWord m := by
      rw [rd_set_ne (by simp only [cTmp] at hnT ⊢; omega), h1]
    rw [hl, h3, if_neg (by decide), h4, rd_set_self (by simp only [size_set]; omega)]
    simp only [XOp.eval, BitVec.or_self]
  · have e : m = K := le_antisymm hmK h
    subst e
    have hl : XOp.ltu.eval (toWord m) (toWord m) = 0 := by simp [XOp.eval]
    rw [hl, rd_set_self hsz, if_pos rfl, rd_set_ne (by simp only [cTmp]; omega), h2]

attribute [local irreducible] entryK storeM

/-- **A `loopK` run `m ≤ K` times**: an invariant preserved by the body for `j < m` holds after the loop. -/
theorem loopK_runLe (I : Array Word) {c n m K : ℕ} (b : XIR) (P : ℕ → St → Prop) (s : St)
    (hM : Inv s.M) (hc : 4 < c) (hcr : c < regs) (hn : n ≠ c) (hnT : n ≠ cTmp) (hN : rd s.M n = toWord m)
    (hmK : m ≤ K) (hK : K < 2 ^ 64) (h0 : P 0 ⟨entryK c n (toWord K) s.M, s.o⟩)
    (hstep : ∀ j s, j < m → P j s → P (j + 1) (decS c (semXIR I b s))) :
    P m (semXIR I (.loopK c n (toWord K) b) s) := by
  have e : semXIR I (.loopK c n (toWord K) b) s =
      iterL (semXIR I b) c m ⟨entryK c n (toWord K) s.M, s.o⟩ := by
    simp only [semXIR, entryK_min hM hc hcr hn hnT hN hmK hK, toNat_toWord (lt_of_le_of_lt hmK hK)]
  rw [e]
  simpa using iterL_ind P hstep m 0 _ (by omega) h0

/-! ## The kit: registers not written -/

theorem sRun_frame (H : ℕ → Word) : ∀ (os : List SOp) (f : ℕ → Word) (r : ℕ), (∀ o ∈ os, o.dst ≠ r) →
    sRun H os f r = f r
  | [], _, _, _ => rfl
  | o :: os, f, r, h => by
    rw [sRun, sRun_frame H os _ r (fun o' ho' ↦ h o' (List.mem_cons_of_mem _ ho'))]
    have := h o List.mem_cons_self
    cases o <;> simp only [SOp.step, SOp.dst] at this ⊢ <;> rw [Function.update_apply, if_neg (Ne.symm this)]

theorem trkB {r : ℕ} (h1 : 9 ≤ r) (h2 : r < 256) : Trk r := ⟨h2, Or.inr h1⟩

/-- A program writing only registers below `187` keeps the builder's registers. -/
theorem keepHi (I : Array Word) {P : XIR} (hw : WF P) (ha : AllBelow 187 P) (s : St) (hM : Inv s.M) {i : ℕ}
    (hi : 187 ≤ i) (hi2 : i < 256) : rd (semXIR I P s).M i = rd s.M i :=
  frame I P s hw hM i hi2 (nw_of_allBelow hi ha)

/-! ## The builder's state -/

/-- The heap outside the builder's scratch `[sA B, fdEnd B ℓ)` is `M₀`'s. -/
def SrcEq (M₀ : Mem) (B ℓ : ℕ) (M : Mem) : Prop :=
  ∀ x, regs ≤ x → (x < sA B ∨ fdEnd B ℓ ≤ x) → rd M x = rd M₀ x

/-- A source address: a heap word outside the scratch. -/
def OutB (B ℓ x : ℕ) : Prop := regs ≤ x ∧ (x < sA B ∨ fdEnd B ℓ ≤ x)

/-- The basis table at `tbA' B ℓ`. -/
def TabOk (N B ℓ : ℕ) (M : Mem) : Prop :=
  ∀ v < N, ∀ i < N, rdK M (tbA' B ℓ + N * v + i) = (wRow ptK N v).getD i 0

/-- **The flags after `q` lanes**: flag `j` is zero iff lanes `q' < q` agree with the word at `j`. -/
def FlagInv (M₀ : Mem) (N ℓ B colB str d tS r q : ℕ) (M : Mem) : Prop :=
  ∀ j < 2 ^ ℓ, (rd M (flA B ℓ + j) = 0 ↔
    ∀ q' < q, encRow M₀ N ℓ colB str d q' j = rdK M₀ (tbBase M₀ tS r + q' + tbOcc M₀ tS r * j))

/-! ## Pure runs of the lane's straight-line pieces -/

theorem lnPre_run (H f : ℕ → Word) {ℓ B colB str q : ℕ} (hQ : f bQ = toWord q) :
    let L : List SOp := [.cst bU (toWord str), .op .mul bT bQ bU, .cst bU (toWord colB), .op .add ySr bT bU,
      .cst yStr (toWord 1), .cst yDs (toWord (rwA B ℓ))]
    sLd H L f ∧ sRun H L f ySr = toWord (q * str + colB) ∧ sRun H L f yStr = toWord 1 ∧
      sRun H L f yDs = toWord (rwA B ℓ) := by
  intro L
  replace hQ : f 194 = toWord q := hQ
  refine ⟨by simp [L, sLd, SOp.LdOk], ?_, ?_, ?_⟩ <;>
    simp only [↓reduceIte, Nat.reduceEqDiff, L, sRun, SOp.step, Function.update_apply, bU, bT, bQ, ySr, yStr,
      yDs, hQ, mul_toWord, add_toWord]

theorem cmpPre_run (H f : ℕ → Word) {ℓ B base q : ℕ} (hQ : f bQ = toWord q) (hB : f bBase = toWord base) :
    let L : List SOp := [.op .add bP bBase bQ, .cst bF (toWord (flA B ℓ)), .cst bR (toWord (rwA B ℓ)),
      .cst bN2 (toWord (2 ^ ℓ))]
    sLd H L f ∧ sRun H L f bP = toWord (base + q) ∧ sRun H L f bF = toWord (flA B ℓ) ∧
      sRun H L f bR = toWord (rwA B ℓ) ∧ sRun H L f bN2 = toWord (2 ^ ℓ) := by
  intro L
  replace hQ : f 194 = toWord q := hQ
  replace hB : f 192 = toWord base := hB
  refine ⟨by simp [L, sLd, SOp.LdOk], ?_, ?_, ?_, ?_⟩ <;>
    simp only [↓reduceIte, Nat.reduceEqDiff, L, sRun, SOp.step, Function.update_apply, bP, bBase, bQ, bF, bR,
      bN2, hQ, hB, add_toWord]

/-- The comparison's loads and flag. -/
def cmpA : List SOp := [.ld bv bP, .ld be bR, .op .xor bv bv be, .ld bf bF, .op .or bf bf bv]

/-- The comparison's pointer steps. -/
def cmpB : List SOp := [.op .add bP bP bOcc, .op .add bR bR cOne, .op .add bF bF cOne]

theorem cmpBody_eq : cmpBody = .seq (sIR cmpA) (.seq (.store bF bf) (sIR cmpB)) := rfl

theorem cmpA_run (H f : ℕ → Word) {P R F : ℕ} (hP : f bP = toWord P) (hR : f bR = toWord R)
    (hF : f bF = toWord F) (hP2 : P < 2 ^ 64) (hR2 : R < 2 ^ 64) (hF2 : F < 2 ^ 64) (hPr : regs ≤ P)
    (hRr : regs ≤ R) (hFr : regs ≤ F) :
    sLd H cmpA f ∧ sRun H cmpA f bf = H F ||| (H P ^^^ H R) := by
  replace hP : f 195 = toWord P := hP
  replace hR : f 196 = toWord R := hR
  replace hF : f 197 = toWord F := hF
  simp only [regs] at hPr hRr hFr
  have t0 : (toWord P).toNat = P := toNat_toWord hP2
  have t1 : (toWord R).toNat = R := toNat_toWord hR2
  have t2 : (toWord F).toNat = F := toNat_toWord hF2
  refine ⟨?_, ?_⟩
  · simp only [↓reduceIte, Nat.reduceEqDiff, sLd, cmpA, SOp.LdOk, SOp.step, Function.update_apply, bv, bP, be,
      bR, bf, bF, hP, hR, hF, t0, t1, t2, regs]
    try simp
    try omega
  · simp only [↓reduceIte, Nat.reduceEqDiff, sRun, cmpA, SOp.step, Function.update_apply, bv, bP, be, bR, bf,
      bF, hP, hR, hF, t0, t1, t2, XOp.eval]

theorem cmpB_run (H f : ℕ → Word) {P R F occ : ℕ} (hP : f bP = toWord P) (hR : f bR = toWord R)
    (hF : f bF = toWord F) (hO : f bOcc = toWord occ) (h1 : f cOne = 1) :
    sLd H cmpB f ∧ sRun H cmpB f bP = toWord (P + occ) ∧ sRun H cmpB f bR = toWord (R + 1) ∧
      sRun H cmpB f bF = toWord (F + 1) := by
  replace hP : f 195 = toWord P := hP
  replace hR : f 196 = toWord R := hR
  replace hF : f 197 = toWord F := hF
  replace hO : f 193 = toWord occ := hO
  replace h1 : f 0 = 1 := h1
  refine ⟨by simp [sLd, cmpB, SOp.LdOk], ?_, ?_, ?_⟩ <;>
    simp only [↓reduceIte, Nat.reduceEqDiff, sRun, cmpB, SOp.step, Function.update_apply, bP, bR, bF, bOcc, cOne,
      hP, hR, hF, hO, h1, add_toWord, add_one_toWord]

theorem ok_cmpA : ∀ o ∈ cmpA, o.Ok := by
  simp +decide [cmpA, SOp.Ok, Trk, regs, bv, bP, be, bR, bf, bF]

theorem ok_cmpB : ∀ o ∈ cmpB, o.Ok := by
  simp +decide [cmpB, SOp.Ok, Trk, regs, bP, bR, bF, bOcc, cOne]

/-! ## The comparison loop -/

/-- **A lane's comparison loop**: `flag[j] := flag[j] ||| (word[j] ⊕ row[j])` for `j < 2^ℓ`, the word at
`P0 + occ·j`, the row at `rwA B ℓ`; the rest of the heap and the lane registers kept. -/
theorem cmpLoop_sem (I : Array Word) (s : St) (hM : Inv s.M) {ℓ B P0 occ : ℕ} (hB : regs ≤ B)
    (hE : fdEnd B ℓ < 2 ^ 64) (hsz : fdEnd B ℓ ≤ s.M.size) (hP0 : rd s.M bP = toWord P0)
    (hO : rd s.M bOcc = toWord occ) (hR0 : rd s.M bR = toWord (rwA B ℓ)) (hF0 : rd s.M bF = toWord (flA B ℓ))
    (hN2 : rd s.M bN2 = toWord (2 ^ ℓ))
    (hW : ∀ j < 2 ^ ℓ, regs ≤ P0 + occ * j ∧ P0 + occ * j < 2 ^ 64 ∧
      (P0 + occ * j < flA B ℓ ∨ flA B ℓ + 2 ^ ℓ ≤ P0 + occ * j)) :
    let s' := semXIR I (.loopK bC2 bN2 (toWord (2 ^ ℓ)) cmpBody) s
    Inv s'.M ∧ s'.M.size = s.M.size ∧
      (∀ j < 2 ^ ℓ, rd s'.M (flA B ℓ + j) = rd s.M (flA B ℓ + j) ||| (rd s.M (P0 + occ * j) ^^^
        rd s.M (rwA B ℓ + j))) ∧
      (∀ x, regs ≤ x → (x < flA B ℓ ∨ flA B ℓ + 2 ^ ℓ ≤ x) → rd s'.M x = rd s.M x) ∧
      rd s'.M bQ = rd s.M bQ ∧ rd s'.M bBase = rd s.M bBase ∧ rd s'.M bOcc = rd s.M bOcc := by
  intro s'
  have hs := hM.1
  have eF : flA B ℓ = B + 4096 + 2 ^ ℓ := rfl
  have eR : rwA B ℓ = B + 4096 + 2 ^ ℓ + 2 ^ ℓ := rfl
  have eE : fdEnd B ℓ = B + 4096 + 11 * 2 ^ ℓ := rfl
  have hL : 2 ^ ℓ < 2 ^ 64 := by omega
  simp only [regs] at hB hs
  let Pinv : ℕ → St → Prop := fun j t ↦ Inv t.M ∧ t.M.size = s.M.size ∧
    rd t.M bP = toWord (P0 + occ * j) ∧ rd t.M bR = toWord (rwA B ℓ + j) ∧ rd t.M bF = toWord (flA B ℓ + j) ∧
    rd t.M bOcc = toWord occ ∧ rd t.M bQ = rd s.M bQ ∧ rd t.M bBase = rd s.M bBase ∧
    (∀ j' < j, rd t.M (flA B ℓ + j') = rd s.M (flA B ℓ + j') ||| (rd s.M (P0 + occ * j') ^^^
      rd s.M (rwA B ℓ + j'))) ∧
    (∀ x, regs ≤ x → (x < flA B ℓ ∨ flA B ℓ + j ≤ x) → rd t.M x = rd s.M x)
  have hE0 : ∀ i, i ≠ bC2 → i ≠ cTmp → rd (entryK bC2 bN2 (toWord (2 ^ ℓ)) s.M) i = rd s.M i :=
    fun i h1 h2 ↦ entryK_frame _ (Ne.symm h1) (Ne.symm h2)
  have h0 : Pinv 0 ⟨entryK bC2 bN2 (toWord (2 ^ ℓ)) s.M, s.o⟩ := by
    refine ⟨inv_entryK hM (by decide), by simp only [size_entryK], ?_, ?_, ?_, ?_, ?_, ?_,
      fun j' hj' ↦ absurd hj' (Nat.not_lt_zero _), fun x hx _ ↦ ?_⟩ <;> dsimp only
    · rw [hE0 _ (by decide) (by decide), hP0, Nat.mul_zero, Nat.add_zero]
    · rw [hE0 _ (by decide) (by decide), hR0, Nat.add_zero]
    · rw [hE0 _ (by decide) (by decide), hF0, Nat.add_zero]
    · rw [hE0 _ (by decide) (by decide), hO]
    · rw [hE0 _ (by decide) (by decide)]
    · rw [hE0 _ (by decide) (by decide)]
    · simp only [regs] at hx
      rw [hE0 _ (by simp only [bC2]; omega) (by simp only [cTmp]; omega)]
  have hstep : ∀ j t, j < 2 ^ ℓ → Pinv j t → Pinv (j + 1) (decS bC2 (semXIR I cmpBody t)) := by
    rintro j t hj ⟨i1, i2, i3, i4, i5, i6, i7, i8, i9, i10⟩
    have ht := i1.1
    obtain ⟨w1, w2, w3⟩ := hW j hj
    simp only [regs] at w1 ht
    have hRj : rwA B ℓ + j < 2 ^ 64 := by omega
    have hFj : flA B ℓ + j < 2 ^ 64 := by omega
    obtain ⟨pr0, pr1⟩ := cmpA_run (rd t.M) (rd t.M) i3 i4 i5 w2 hRj hFj (by simp only [regs]; omega)
      (by simp only [regs]; omega) (by simp only [regs]; omega)
    rw [cmpBody_eq, semXIR_seq]
    obtain ⟨a1, a2, a3, -⟩ := sIR_sem I (rd t.M) cmpA t (rd t.M) i1 ok_cmpA (fun _ _ ↦ rfl) (fun _ _ ↦ rfl) pr0
    have z1 := size_sIR I cmpA t
    generalize semXIR I (sIR cmpA) t = t1 at a1 a2 a3 z1
    have nA : ∀ r, Trk r → r ≠ bv → r ≠ be → r ≠ bf → rd t1.M r = rd t.M r := fun r hr h1 h2 h3 ↦ by
      rw [a1 r hr, sRun_frame _ _ _ _ (by simp [cmpA, SOp.dst]; omega)]
    rw [semXIR_seq]
    obtain ⟨c1, c2, hM2⟩ := store_sem I t1 a3 (p := bF) (v := bf) (x := flA B ℓ + j) (by decide) (by decide)
      ((nA _ (trkB (by decide) (by decide)) (by decide) (by decide) (by decide)).trans i5)
      (by simp only [regs]; omega) hFj (by rw [z1, i2]; omega)
    have z2 := size_sem I (.store bF bf) t1
    generalize semXIR I (.store bF bf) t1 = t2 at c1 c2 hM2 z2
    have r2 : ∀ r, Trk r → r ≠ bv → r ≠ be → r ≠ bf → rd t2.M r = rd t.M r := fun r hr h1 h2 h3 ↦ by
      have := hr.1
      simp only [regs] at this
      rw [c2 r (by omega) (by rcases hr.2 with h | h <;> simp only [cTmp] <;> omega), nA r hr h1 h2 h3]
    obtain ⟨po0, po1, po2, po3⟩ := cmpB_run (rd t2.M) (rd t2.M) (P := P0 + occ * j) (R := rwA B ℓ + j)
      (F := flA B ℓ + j) (occ := occ)
      ((r2 _ (trkB (by decide) (by decide)) (by decide) (by decide) (by decide)).trans i3)
      ((r2 _ (trkB (by decide) (by decide)) (by decide) (by decide) (by decide)).trans i4)
      ((r2 _ (trkB (by decide) (by decide)) (by decide) (by decide) (by decide)).trans i5)
      ((r2 _ (trkB (by decide) (by decide)) (by decide) (by decide) (by decide)).trans i6)
      (hM2.2 0 (by decide))
    obtain ⟨e1, e2, e3, -⟩ := sIR_sem I (rd t2.M) cmpB t2 (rd t2.M) hM2 ok_cmpB (fun _ _ ↦ rfl) (fun _ _ ↦ rfl)
      po0
    have z3 := size_sIR I cmpB t2
    generalize semXIR I (sIR cmpB) t2 = t3 at e1 e2 e3 z3
    have hd : ∀ x, x ≠ bC2 → rd (decS bC2 t3).M x = rd t3.M x := fun x hx ↦ rd_decS (Ne.symm hx) _
    have nB : ∀ r, Trk r → r ≠ bP → r ≠ bR → r ≠ bF → rd t3.M r = rd t2.M r := fun r hr h1 h2 h3 ↦ by
      rw [e1 r hr, sRun_frame _ _ _ _ (by simp [cmpB, SOp.dst]; omega)]
    have hH : ∀ x, regs ≤ x → x ≠ flA B ℓ + j → rd (decS bC2 t3).M x = rd t.M x := fun x hx hx' ↦ by
      simp only [regs] at hx
      rw [hd x (by simp only [bC2]; omega), e2 x (by simp only [regs]; omega),
        c2 x hx' (by simp only [cTmp]; omega), a2 x (by simp only [regs]; omega)]
    have v0 : rd (decS bC2 t3).M (flA B ℓ + j) = rd t.M (flA B ℓ + j) |||
        (rd t.M (P0 + occ * j) ^^^ rd t.M (rwA B ℓ + j)) := by
      rw [hd _ (by simp only [bC2]; omega), e2 _ (by simp only [regs]; omega), c1, a1 _ (trkB (by decide)
        (by decide)), pr1]
    have g1 : rd t.M (flA B ℓ + j) = rd s.M (flA B ℓ + j) := i10 _ (by simp only [regs]; omega) (by omega)
    have g2 : rd t.M (P0 + occ * j) = rd s.M (P0 + occ * j) := i10 _ (by simp only [regs]; omega) (by omega)
    have g3 : rd t.M (rwA B ℓ + j) = rd s.M (rwA B ℓ + j) := i10 _ (by simp only [regs]; omega) (by omega)
    refine ⟨inv_decS e3 (by decide), by rw [size_decS, z3, z2, z1, i2], ?_, ?_, ?_, ?_, ?_, ?_,
      fun j' hj' ↦ ?_, fun x hx hx' ↦ ?_⟩
    · rw [hd _ (by decide), e1 _ (trkB (by decide) (by decide)), po1]; congr 1; ring
    · rw [hd _ (by decide), e1 _ (trkB (by decide) (by decide)), po2]; congr 1
    · rw [hd _ (by decide), e1 _ (trkB (by decide) (by decide)), po3]; congr 1
    · rw [hd _ (by decide), e1 _ (trkB (by decide) (by decide)),
        sRun_frame _ _ _ _ (by simp [cmpB, SOp.dst, bP, bR, bF, bOcc]),
        r2 _ (trkB (by decide) (by decide)) (by decide) (by decide) (by decide), i6]
    · rw [hd _ (by decide), nB _ (trkB (by decide) (by decide)) (by decide) (by decide) (by decide),
        r2 _ (trkB (by decide) (by decide)) (by decide) (by decide) (by decide), i7]
    · rw [hd _ (by decide), nB _ (trkB (by decide) (by decide)) (by decide) (by decide) (by decide),
        r2 _ (trkB (by decide) (by decide)) (by decide) (by decide) (by decide), i8]
    · rcases Nat.lt_succ_iff_lt_or_eq.1 hj' with hj' | rfl
      · rw [hH _ (by simp only [regs]; omega) (by omega), i9 j' hj']
      · rw [v0, g1, g2, g3]
    · rw [hH x hx (by omega), i10 x hx (by omega)]
  have hfin := loopK_run I cmpBody Pinv s hM (c := bC2) (n := bN2) (K := 2 ^ ℓ) (by decide) (by decide)
    (by decide) hN2 hL h0 hstep
  obtain ⟨f1, f2, -, -, -, f6, f7, f8, f9, f10⟩ := hfin
  exact ⟨f1, f2, f9, fun x hx hx' ↦ f10 x hx hx', f7, f8, f6.trans hO.symm⟩

/-! ## One lane -/

theorem keepC_of {r : ℕ} (h : 80 ≤ r) : KeepC r := by
  simp only [KeepC, yV, ySr, yDs, yC, yN, cTmp]; omega

/-- The flag update: `a ||| (w ⊕ v)` is zero iff `a` is and the values agree. -/
theorem flag_step {a w v : Word} {A : Prop} {e c : BF64} (ha : a = 0 ↔ A) (he : wK v = e) (hc : wK w = c) :
    (a ||| (w ^^^ v)) = 0 ↔ A ∧ e = c := by
  rw [show ((a ||| (w ^^^ v)) = 0) ↔ (a = 0 ∧ (w ^^^ v) = 0) from BitVec.or_eq_zero_iff,
    show ((w ^^^ v) = 0) ↔ w = v from BitVec.xor_eq_zero_iff, ha, ← he, ← hc, wK_inj]
  exact and_congr_right fun _ ↦ eq_comm

theorem forall_lt_succ' {P : ℕ → Prop} {q : ℕ} : ((∀ q' < q, P q') ∧ P q) ↔ ∀ q' < q + 1, P q' :=
  ⟨fun ⟨h1, h2⟩ q' hq' ↦ (Nat.lt_succ_iff_lt_or_eq.1 hq').elim (h1 q') (fun e ↦ e ▸ h2),
    fun h ↦ ⟨fun q' hq' ↦ h q' (by omega), h q (by omega)⟩⟩

/-- The lane's prologue. -/
def lnPre (ℓ B colB str : ℕ) : List SOp := [.cst bU (toWord str), .op .mul bT bQ bU, .cst bU (toWord colB),
  .op .add ySr bT bU, .cst yStr (toWord 1), .cst yDs (toWord (rwA B ℓ))]

/-- The comparison's prologue. -/
def cmpPre (ℓ B : ℕ) : List SOp := [.op .add bP bBase bQ, .cst bF (toWord (flA B ℓ)), .cst bR (toWord (rwA B ℓ)),
  .cst bN2 (toWord (2 ^ ℓ))]

theorem laneB_eq (N ℓ B colB str d : ℕ) : laneB N ℓ B colB str d =
    .seq (sIR (lnPre ℓ B colB str)) (.seq (mcpLoop (d + 1)) (.seq (zeroIR (2 ^ ℓ - (d + 1)) (rwA B ℓ + (d + 1)))
      (.seq (SOp.cst rA0 (toWord (rwA B ℓ))).ir (.seq (fwdNIR N ℓ (tbA' B ℓ)) (.seq (sIR (cmpPre ℓ B))
      (.seq (.loopK bC2 bN2 (toWord (2 ^ ℓ)) cmpBody) (sIR [.op .add bQ bQ cOne]))))))) := rfl

theorem ok_lnPre (ℓ B colB str : ℕ) : ∀ o ∈ lnPre ℓ B colB str, o.Ok := by
  simp +decide [lnPre, SOp.Ok, Trk, regs, bU, bT, bQ, ySr, yStr, yDs]

theorem ok_cmpPre (ℓ B : ℕ) : ∀ o ∈ cmpPre ℓ B, o.Ok := by
  simp +decide [cmpPre, SOp.Ok, Trk, regs, bP, bBase, bQ, bF, bR, bN2]

theorem ok_incQ : ∀ o ∈ [SOp.op .add bQ bQ cOne], o.Ok := by
  simp +decide [SOp.Ok, Trk, regs, bQ, cOne]

/-- **One lane `q`** of the builder: flags advance from `q` to `q + 1` lanes; sources, table, the word's base and
row stride kept; `q` incremented. -/
theorem laneB_sem (I : Array Word) (s : St) (hM : Inv s.M) {N ℓ B colB str d tS r q : ℕ} (M₀ : Mem)
    (hN : N ≤ 64) (hℓN : ℓ ≤ N) (hB : regs ≤ B) (hE : fdEnd B ℓ < 2 ^ 64) (hsz : fdEnd B ℓ ≤ s.M.size)
    (hNN : N * N ≤ 8 * 2 ^ ℓ) (hd : d + 1 ≤ 2 ^ ℓ)
    (hW : ∀ j < 2 ^ ℓ, OutB B ℓ (tbBase M₀ tS r + q + tbOcc M₀ tS r * j) ∧
      tbBase M₀ tS r + q + tbOcc M₀ tS r * j < 2 ^ 64)
    (hC : ∀ x < d + 1, OutB B ℓ (colB + str * q + x)) (hC2 : colB + str * q + (d + 1) < 2 ^ 64)
    (hQ : rd s.M bQ = toWord q) (hBa : rd s.M bBase = toWord (tbBase M₀ tS r))
    (hO : rd s.M bOcc = toWord (tbOcc M₀ tS r))
    (hS : SrcEq M₀ B ℓ s.M) (hT : TabOk N B ℓ s.M) (hF : FlagInv M₀ N ℓ B colB str d tS r q s.M) :
    let s' := semXIR I (laneB N ℓ B colB str d) s
    Inv s'.M ∧ rd s'.M bQ = toWord (q + 1) ∧ rd s'.M bBase = rd s.M bBase ∧
      rd s'.M bOcc = rd s.M bOcc ∧ SrcEq M₀ B ℓ s'.M ∧ TabOk N B ℓ s'.M ∧
      FlagInv M₀ N ℓ B colB str d tS r (q + 1) s'.M := by
  intro s'
  have hs := hM.1
  have eS : sA B = B + 4096 := rfl
  have eF : flA B ℓ = B + 4096 + 2 ^ ℓ := rfl
  have eR : rwA B ℓ = B + 4096 + 2 ^ ℓ + 2 ^ ℓ := rfl
  have eT : tbA' B ℓ = B + 4096 + 2 ^ ℓ + 2 * 2 ^ ℓ := rfl
  have eE : fdEnd B ℓ = B + 4096 + 11 * 2 ^ ℓ := rfl
  have hL : 2 ^ ℓ < 2 ^ 64 := by omega
  simp only [regs] at hB hs
  have ec : q * str + colB = colB + str * q := by ring
  -- 1. the lane's prologue
  obtain ⟨p0, p1, p2, p3⟩ := lnPre_run (ℓ := ℓ) (B := B) (colB := colB) (str := str) (rd s.M) (rd s.M) hQ
  obtain ⟨a1, a2, a3, -⟩ := sIR_sem I (rd s.M) (lnPre ℓ B colB str) s (rd s.M) hM (ok_lnPre ℓ B colB str)
    (fun _ _ ↦ rfl) (fun _ _ ↦ rfl) p0
  have r1 : ∀ x, 190 ≤ x → x < 256 → x ≠ bU → x ≠ bT → rd (semXIR I (sIR (lnPre ℓ B colB str)) s).M x =
      rd s.M x := fun x h1 h2 h3 h4 ↦ by
    rw [a1 x (trkB (by omega) h2), sRun_frame _ _ _ _ (by
      simp only [lnPre, SOp.dst, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq,
        ySr, yStr, yDs]; omega)]
  have y1 : rd (semXIR I (sIR (lnPre ℓ B colB str)) s).M ySr = toWord (colB + str * q) := by
    rw [a1 _ (trkB (by decide) (by decide))]; exact p1.trans (congrArg toWord ec)
  have y2 := (a1 _ (trkB (by decide) (by decide))).trans p2
  have y3 := (a1 _ (trkB (by decide) (by decide))).trans p3
  have z1 := size_sIR I (lnPre ℓ B colB str) s
  simp only [s', laneB_eq, semXIR_seq]
  generalize semXIR I (sIR (lnPre ℓ B colB str)) s = s1 at a1 a2 a3 r1 y1 y2 y3 z1
  -- 2. the column's `d + 1` coefficients to the row
  have hcR : ∀ i < d + 1, regs ≤ colB + str * q + 1 * i ∧
      (colB + str * q + 1 * i < rwA B ℓ ∨ rwA B ℓ + (d + 1) ≤ colB + str * q + 1 * i) := fun i hi ↦ by
    obtain ⟨h1, h2⟩ := hC i hi
    simp only [regs] at h1 ⊢
    omega
  obtain ⟨b1, b2, b3⟩ := mcpLoop_sem I s1 a3 (n := d + 1) (src := colB + str * q) (str := 1) (dst := rwA B ℓ)
    (by omega) (by omega) (by simp only [regs]; omega) (by omega) (by omega) (fun i hi ↦ (hcR i hi).2)
    (fun i hi ↦ (hcR i hi).1) y1 y3 y2
  have z2 := size_sem I (mcpLoop (d + 1)) s1
  generalize semXIR I (mcpLoop (d + 1)) s1 = s2 at b1 b2 b3 z2
  -- 3. the zero pad
  obtain ⟨c1, c2, c3⟩ := zeroIR_sem I s2 b3 (n := 2 ^ ℓ - (d + 1)) (dst := rwA B ℓ + (d + 1)) (by omega)
    (by simp only [regs]; omega) (by omega) (by omega)
  have k3 : ∀ x, 187 ≤ x → x < 256 → rd (semXIR I (zeroIR (2 ^ ℓ - (d + 1)) (rwA B ℓ + (d + 1))) s2).M x =
      rd s2.M x := fun x h1 h2 ↦
    keepHi I (wf_zeroIR ..) (allBelow_mono (by decide) (allBelow_zeroIR ..)) s2 b3 h1 h2
  have z3 := size_sem I (zeroIR (2 ^ ℓ - (d + 1)) (rwA B ℓ + (d + 1))) s2
  generalize semXIR I (zeroIR (2 ^ ℓ - (d + 1)) (rwA B ℓ + (d + 1))) s2 = s3 at c1 c2 c3 k3 z3
  -- 4. the row pointer
  obtain ⟨d1, d2, d3, -⟩ := sOp_sem I s3 c3 (.cst rA0 (toWord (rwA B ℓ))) (by simp +decide [SOp.Ok, rA0, regs])
    (rd s3.M) (rd s3.M) (fun _ _ ↦ rfl) (fun _ _ ↦ rfl) trivial
  have z4 := size_sem I (SOp.cst rA0 (toWord (rwA B ℓ))).ir s3
  generalize semXIR I (SOp.cst rA0 (toWord (rwA B ℓ))).ir s3 = s4 at d1 d2 d3 z4
  have k4 : ∀ x, 190 ≤ x → x < 256 → rd s4.M x = rd s3.M x := fun x h1 h2 ↦ by
    rw [d1 x (trkB (by omega) h2)]
    simp only [SOp.step]
    rw [Function.update_apply, if_neg (by simp only [rA0]; omega)]
  have hA0 : rd s4.M rA0 = toWord (rwA B ℓ) := by
    rw [d1 _ (trkB (by decide) (by decide))]
    simp only [SOp.step, Function.update_self]
  -- the heap of `s4` outside the row is `s`'s
  have h4 : ∀ x, regs ≤ x → (x < rwA B ℓ ∨ rwA B ℓ + 2 ^ ℓ ≤ x) → rd s4.M x = rd s.M x := fun x hx hx' ↦ by
    simp only [regs] at hx
    rw [d2 x (by simp only [regs]; omega), c2 x (by simp only [regs]; omega) (by omega),
      b2 x (keepC_of (by omega)) (by omega), a2 x (by simp only [regs]; omega)]
  have hY : ∀ i < 2 ^ ℓ, rdK s4.M (rwA B ℓ + i) =
      (fun x ↦ if x < d + 1 then rdK M₀ (colB + str * q + x) else 0) i := fun i hi ↦ by
    dsimp only
    by_cases hid : i < d + 1
    · rw [if_pos hid]
      obtain ⟨o1, o2⟩ := hC i hid
      simp only [rdK]
      rw [d2 _ (by simp only [regs]; omega), c2 _ (by simp only [regs]; omega) (by omega), b1 i hid,
        a2 _ (by simp only [regs] at o1 ⊢; omega), one_mul, hS _ o1 o2]
    · rw [if_neg hid]
      have e : rwA B ℓ + i = rwA B ℓ + (d + 1) + (i - (d + 1)) := by omega
      simp only [rdK]
      rw [d2 _ (by simp only [regs]; omega), e, c1 _ (by omega)]
      rfl
  -- 5. the encoding
  have hTab4 : ∀ v < N, ∀ i < N, rdK s4.M (tbA' B ℓ + N * v + i) = (wRow ptK N v).getD i 0 := fun v hv i hi ↦ by
    have := hT v hv i hi
    simp only [rdK] at this ⊢
    rw [h4 _ (by simp only [regs]; omega) (by omega), this]
  obtain ⟨f1, f2, f3⟩ := fwdNIR_sem I s4 d3 hN (A := rwA B ℓ) (tb := tbA' B ℓ)
    (Y := fun x ↦ if x < d + 1 then rdK M₀ (colB + str * q + x) else 0) hℓN (by simp only [regs]; omega)
    (by omega) (by omega) (by simp only [regs]; omega) (by have := Nat.mul_le_mul hN hN; omega) (Or.inr (by omega))
    hA0 hTab4 hY
  have k5 : ∀ x, 187 ≤ x → x < 256 → rd (semXIR I (fwdNIR N ℓ (tbA' B ℓ)) s4).M x = rd s4.M x := fun x h1 h2 ↦
    keepHi I (wf_fwdNIR ..) (allBelow_fwdNIR ..) s4 d3 h1 h2
  have z5 := size_sem I (fwdNIR N ℓ (tbA' B ℓ)) s4
  generalize semXIR I (fwdNIR N ℓ (tbA' B ℓ)) s4 = s5 at f1 f2 f3 k5 z5
  -- the lane registers of `s5`
  have g5 : ∀ x, 190 ≤ x → x < 256 → x ≠ bU → x ≠ bT → rd s5.M x = rd s.M x := fun x h1 h2 h3 h4' ↦ by
    rw [k5 x (by omega) h2, k4 x h1 h2, k3 x (by omega) h2, b2 x (keepC_of (by omega)) (Or.inl (by omega)),
      r1 x h1 h2 h3 h4']
  have q5 : rd s5.M bQ = toWord q := (g5 _ (by decide) (by decide) (by decide) (by decide)).trans hQ
  have ba5 : rd s5.M bBase = toWord (tbBase M₀ tS r) :=
    (g5 _ (by decide) (by decide) (by decide) (by decide)).trans hBa
  have oc5 : rd s5.M bOcc = toWord (tbOcc M₀ tS r) :=
    (g5 _ (by decide) (by decide) (by decide) (by decide)).trans hO
  -- 6. the comparison's prologue
  obtain ⟨e0, e1, e2, e3, e4⟩ := cmpPre_run (ℓ := ℓ) (B := B) (rd s5.M) (rd s5.M) q5 ba5
  obtain ⟨m1, m2, m3, -⟩ := sIR_sem I (rd s5.M) (cmpPre ℓ B) s5 (rd s5.M) f3 (ok_cmpPre ℓ B) (fun _ _ ↦ rfl)
    (fun _ _ ↦ rfl) e0
  have z6 := size_sIR I (cmpPre ℓ B) s5
  have r6 : ∀ x, x = bQ ∨ x = bBase ∨ x = bOcc → rd (semXIR I (sIR (cmpPre ℓ B)) s5).M x = rd s5.M x :=
    fun x hx ↦ by
      rw [m1 x (by rcases hx with rfl | rfl | rfl <;> exact trkB (by decide) (by decide)), sRun_frame _ _ _ _ (by
        rcases hx with rfl | rfl | rfl <;> simp +decide [cmpPre, SOp.dst, bP, bF, bR, bN2, bQ, bBase, bOcc])]
  have hP6 := (m1 _ (trkB (by decide) (by decide))).trans e1
  have hF6 := (m1 _ (trkB (by decide) (by decide))).trans e2
  have hR6 := (m1 _ (trkB (by decide) (by decide))).trans e3
  have hN6 := (m1 _ (trkB (by decide) (by decide))).trans e4
  generalize semXIR I (sIR (cmpPre ℓ B)) s5 = s6 at m1 m2 m3 z6 r6 hP6 hF6 hR6 hN6
  -- 7. the comparison loop
  obtain ⟨g1, -, g3, g4, g5', g6, g7⟩ := cmpLoop_sem I s6 m3 (ℓ := ℓ) (B := B) (P0 := tbBase M₀ tS r + q)
    (occ := tbOcc M₀ tS r) (by simp only [regs]; omega) hE (by omega) hP6 ((r6 _ (by simp)).trans oc5) hR6 hF6
    hN6 (fun j hj ↦ by
      obtain ⟨⟨o1, o2⟩, o3⟩ := hW j hj
      simp only [regs] at o1 ⊢
      exact ⟨o1, o3, by omega⟩)
  generalize semXIR I (.loopK bC2 bN2 (toWord (2 ^ ℓ)) cmpBody) s6 = s7 at g1 g3 g4 g5' g6 g7
  -- 8. `q + 1`
  have hQ7 : rd s7.M bQ = toWord q := by rw [g5', r6 _ (by simp), q5]
  obtain ⟨n1, n2, n3, -⟩ := sIR_sem I (rd s7.M) [.op .add bQ bQ cOne] s7 (rd s7.M) g1 ok_incQ (fun _ _ ↦ rfl)
    (fun _ _ ↦ rfl) (by simp [sLd, SOp.LdOk])
  -- the heap of `s6` outside the row and the flags is `s`'s
  have h6 : ∀ x, regs ≤ x → (x < rwA B ℓ ∨ rwA B ℓ + 2 ^ ℓ ≤ x) → rd s6.M x = rd s.M x := fun x hx hx' ↦ by
    rw [m2 x hx, f2 x hx (by omega), h4 x hx (by omega)]
  have h7 : ∀ x, regs ≤ x → (x < flA B ℓ ∨ rwA B ℓ + 2 ^ ℓ ≤ x) →
      rd (semXIR I (sIR [.op .add bQ bQ cOne]) s7).M x = rd s.M x := fun x hx hx' ↦ by
    rw [n2 x hx, g4 x hx (by omega), h6 x hx (by omega)]
  refine ⟨n3, ?_, ?_, ?_, fun x hx hx' ↦ ?_, fun v hv i hi ↦ ?_, fun j hj ↦ ?_⟩
  · rw [n1 _ (trkB (by decide) (by decide))]
    simp only [↓reduceIte, Nat.reduceEqDiff, sRun, SOp.step, Function.update_apply, bQ, cOne]
    rw [show (194 : ℕ) = bQ from rfl, hQ7, show rd s7.M 0 = 1 from g1.2 0 (by decide)]
    exact add_one_toWord q
  · rw [n1 _ (trkB (by decide) (by decide)), sRun_frame _ _ _ _ (by simp +decide [SOp.dst, bQ, bBase]),
      g6, r6 _ (by simp), g5 _ (by decide) (by decide) (by decide) (by decide)]
  · rw [n1 _ (trkB (by decide) (by decide)), sRun_frame _ _ _ _ (by simp +decide [SOp.dst, bQ, bOcc]),
      g7, r6 _ (by simp), g5 _ (by decide) (by decide) (by decide) (by decide)]
  · rw [h7 x hx (by omega), hS x hx hx']
  · have := hT v hv i hi
    simp only [rdK] at this ⊢
    rw [h7 _ (by simp only [regs]; omega) (by have := Nat.mul_le_mul hN hN; omega), this]
  · obtain ⟨⟨o1, o2⟩, o3⟩ := hW j hj
    have e7 : rd (semXIR I (sIR [.op .add bQ bQ cOne]) s7).M (flA B ℓ + j) = rd s7.M (flA B ℓ + j) :=
      n2 _ (by simp only [regs]; omega)
    rw [e7, g3 j hj, h6 _ (by simp only [regs]; omega) (by omega), h6 _ o1 (by omega), m2 _ (by
      simp only [regs]; omega)]
    refine (flag_step (hF j hj) (f1 j hj) ?_).trans forall_lt_succ'
    simp only [rdK]
    rw [hS _ o1 o2]

end Lvm6.X
