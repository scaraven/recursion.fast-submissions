-- lvm6 X8a (X7b §3 items 1–2): toward `sbIR` meeting `SbOkW` with `S = sbSpec`: the
-- listing loop writes the first `d + 3` zero flags (`scanIR_sem`), the lane loop runs `occ ≤ K` lanes
-- (`loopK_runLe`, `laneB_sem`). New.
import Lvm6XDescSbL

/-!
# The builder meets `SbOkW`

* **`take_filter_succ`**: the first `k` of a filtered range, one position further.
* **`scanIR_sem`**: from flags `flag[j] = 0 ↔ G j`, the listing loop writes `((range 2^ℓ).filter G).take (d + 3)`
  at `sA B` and no other heap word.
* **`PreB`**: the round register holds `r` and the heap outside the scratch `[sA B, fdEnd B ℓ)` is `M₀`'s; the
  pieces of `sbIR_okW` (`sbPro_run`, `sbSpec_eq`, the `of_heap` transfers); **`sbSpec_eq_agreeS`**. X8a's assembled
  `sbIR_okW` (prologue, table, flags, lane loop, listing) hit a `whnf` heartbeat timeout and is not in this module.
-/

set_option autoImplicit false

namespace Lvm6.X

open RecursionFast Lvm.X Lvm.Nb Lvm6.FD Finset

attribute [local irreducible] entryK storeM

/-! ## The listing -/

theorem take_filter_succ (g : ℕ → Bool) (k j : ℕ) :
    ((List.range (j + 1)).filter g).take k =
      if g j = true ∧ (((List.range j).filter g).take k).length < k then
        ((List.range j).filter g).take k ++ [j] else ((List.range j).filter g).take k := by
  rw [List.range_succ, List.filter_append, List.take_append]
  by_cases hg : g j = true
  · simp only [List.filter_cons, hg, ↓reduceIte, List.filter_nil, List.length_take, true_and]
    split_ifs with h
    · have e : k - ((List.range j).filter g).length = (k - ((List.range j).filter g).length - 1) + 1 := by omega
      rw [e, List.take_succ_cons, List.take_nil]
    · have e : k - ((List.range j).filter g).length = 0 := by omega
      rw [e, List.take_zero, List.append_nil]
  · simp [List.filter_cons, hg]

/-- The listing's prologue. -/
def scPre (ℓ B d : ℕ) : List SOp := [.cst bF (toWord (flA B ℓ)), .cst bJ (toWord 0), .cst bCnt (toWord 0),
  .cst bS (toWord (sA B)), .cst bDm (toWord (d + 3)), .cst bZ0 (toWord 0), .cst bN2 (toWord (2 ^ ℓ))]
/-- The test. -/
def scA : List SOp := [.ld bf bF, .op .eq bz bf bZ0, .op .ltu bl bCnt bDm, .op .and bz bz bl]
/-- The count step. -/
def scInc : List SOp := [.op .add bS bS cOne, .op .add bCnt bCnt cOne]
/-- The position step. -/
def scB : List SOp := [.op .add bF bF cOne, .op .add bJ bJ cOne]

theorem scanIR_eq (ℓ B d : ℕ) : scanIR ℓ B d = .seq (sIR (scPre ℓ B d)) (.loopK bC2 bN2 (toWord (2 ^ ℓ))
    (.seq (sIR scA) (.seq (.ite bz (.seq (.store bS bJ) (sIR scInc)) (.blk [])) (sIR scB)))) := rfl

theorem ok_scPre (ℓ B d : ℕ) : ∀ o ∈ scPre ℓ B d, o.Ok := by
  simp +decide [scPre, SOp.Ok, Trk, regs, bF, bJ, bCnt, bS, bDm, bZ0, bN2]
theorem ok_scA : ∀ o ∈ scA, o.Ok := by simp +decide [scA, SOp.Ok, Trk, regs, bf, bF, bz, bZ0, bl, bCnt, bDm]
theorem ok_scInc : ∀ o ∈ scInc, o.Ok := by simp +decide [scInc, SOp.Ok, Trk, regs, bS, bCnt, cOne]
theorem ok_scB : ∀ o ∈ scB, o.Ok := by simp +decide [scB, SOp.Ok, Trk, regs, bF, bJ, cOne]

theorem scPre_run (H f : ℕ → Word) (ℓ B d : ℕ) :
    sLd H (scPre ℓ B d) f ∧ sRun H (scPre ℓ B d) f bF = toWord (flA B ℓ) ∧ sRun H (scPre ℓ B d) f bJ = toWord 0 ∧
      sRun H (scPre ℓ B d) f bCnt = toWord 0 ∧ sRun H (scPre ℓ B d) f bS = toWord (sA B) ∧
      sRun H (scPre ℓ B d) f bDm = toWord (d + 3) ∧ sRun H (scPre ℓ B d) f bZ0 = toWord 0 ∧
      sRun H (scPre ℓ B d) f bN2 = toWord (2 ^ ℓ) := by
  refine ⟨by simp [scPre, sLd, SOp.LdOk], ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    simp only [↓reduceIte, Nat.reduceEqDiff, scPre, sRun, SOp.step, Function.update_apply, bF, bJ, bCnt, bS, bDm,
      bZ0, bN2]

/-- The test word: `(flag = 0) ∧ (cnt < d + 3)`. -/
theorem and01 (p q : Prop) [Decidable p] [Decidable q] :
    XOp.and.eval (if p then (1 : Word) else 0) (if q then 1 else 0) = 0 ↔ ¬ (p ∧ q) := by
  by_cases hp : p <;> by_cases hq : q <;> simp [hp, hq, XOp.eval] <;> decide

theorem scA_run (H f : ℕ → Word) {F c dm : ℕ} (hF : f bF = toWord F) (hZ : f bZ0 = toWord 0)
    (hC : f bCnt = toWord c) (hD : f bDm = toWord dm) (hF2 : F < 2 ^ 64) (hFr : regs ≤ F) (hc : c < 2 ^ 64)
    (hdm : dm < 2 ^ 64) :
    sLd H scA f ∧ (sRun H scA f bz = 0 ↔ ¬ (H F = 0 ∧ c < dm)) := by
  replace hF : f 197 = toWord F := hF
  replace hZ : f 207 = toWord 0 := hZ
  replace hC : f 205 = toWord c := hC
  replace hD : f 206 = toWord dm := hD
  have t0 : (toWord F).toNat = F := toNat_toWord hF2
  simp only [regs] at hFr
  refine ⟨?_, ?_⟩
  · simp only [↓reduceIte, Nat.reduceEqDiff, sLd, scA, SOp.LdOk, SOp.step, Function.update_apply, bf, bF, bz,
      bZ0, bl, bCnt, bDm, hF, t0, regs]
    try simp
    try omega
  · simp only [↓reduceIte, Nat.reduceEqDiff, sRun, scA, SOp.step, Function.update_apply, bf, bF, bz, bZ0, bl,
      bCnt, bDm, hF, hZ, hC, hD, t0]
    rw [show XOp.eq.eval (H F) (toWord 0) = if H F = 0 then 1 else 0 from rfl,
      show XOp.ltu.eval (toWord c) (toWord dm) = if c < dm then 1 else 0 by
        simp only [XOp.eval, toWord_lt_toWord hc hdm]]
    exact and01 _ _

theorem scInc_run (H f : ℕ → Word) {S c : ℕ} (hS : f bS = toWord S) (hC : f bCnt = toWord c) (h1 : f cOne = 1) :
    sLd H scInc f ∧ sRun H scInc f bS = toWord (S + 1) ∧ sRun H scInc f bCnt = toWord (c + 1) := by
  replace hS : f 203 = toWord S := hS
  replace hC : f 205 = toWord c := hC
  replace h1 : f 0 = 1 := h1
  refine ⟨by simp [sLd, scInc, SOp.LdOk], ?_, ?_⟩ <;>
    simp only [↓reduceIte, Nat.reduceEqDiff, sRun, scInc, SOp.step, Function.update_apply, bS, bCnt, cOne, hS, hC,
      h1, add_one_toWord]

theorem scB_run (H f : ℕ → Word) {F j : ℕ} (hF : f bF = toWord F) (hJ : f bJ = toWord j) (h1 : f cOne = 1) :
    sLd H scB f ∧ sRun H scB f bF = toWord (F + 1) ∧ sRun H scB f bJ = toWord (j + 1) := by
  replace hF : f 197 = toWord F := hF
  replace hJ : f 204 = toWord j := hJ
  replace h1 : f 0 = 1 := h1
  refine ⟨by simp [sLd, scB, SOp.LdOk], ?_, ?_⟩ <;>
    simp only [↓reduceIte, Nat.reduceEqDiff, sRun, scB, SOp.step, Function.update_apply, bF, bJ, cOne, hF, hJ,
      h1, add_one_toWord]

theorem getD_append_one (L : List ℕ) (j i : ℕ) (hi : i < L.length + 1) :
    (L ++ [j]).getD i 0 = if i < L.length then L.getD i 0 else j := by
  split_ifs with h
  · simp [List.getD_eq_getElem?_getD, List.getElem?_append_left h]
  · have e : i = L.length := by omega
    subst e
    simp [List.getD_eq_getElem?_getD]

/-- **The listing**: from flags `flag[j] = 0 ↔ G j`, it writes the first `d + 3` positions with `G` at `sA B`. -/
theorem scanIR_sem (I : Array Word) (s : St) (hM : Inv s.M) {ℓ B d : ℕ} (g : ℕ → Bool) (hB : regs ≤ B)
    (hE : fdEnd B ℓ < 2 ^ 64) (hsz : fdEnd B ℓ ≤ s.M.size) (hd : d + 3 ≤ 2 ^ ℓ)
    (hG : ∀ j < 2 ^ ℓ, rd s.M (flA B ℓ + j) = 0 ↔ g j = true) :
    let s' := semXIR I (scanIR ℓ B d) s
    let S := ((List.range (2 ^ ℓ)).filter g).take (d + 3)
    Inv s'.M ∧ (∀ i < S.length, rd s'.M (sA B + i) = toWord (S.getD i 0)) ∧
      ∀ x, regs ≤ x → (x < sA B ∨ sA B + (d + 3) ≤ x) → rd s'.M x = rd s.M x := by
  intro s' S
  have hs := hM.1
  have eS : sA B = B + 4096 := rfl
  have eF : flA B ℓ = B + 4096 + 2 ^ ℓ := rfl
  have eE : fdEnd B ℓ = B + 4096 + 11 * 2 ^ ℓ := rfl
  have hL : 2 ^ ℓ < 2 ^ 64 := by omega
  simp only [regs] at hB hs
  obtain ⟨p0, p1, p2, p3, p4, p5, p6, p7⟩ := scPre_run (rd s.M) (rd s.M) ℓ B d
  obtain ⟨a1, a2, a3, -⟩ := sIR_sem I (rd s.M) (scPre ℓ B d) s (rd s.M) hM (ok_scPre ℓ B d) (fun _ _ ↦ rfl)
    (fun _ _ ↦ rfl) p0
  have z1 := size_sIR I (scPre ℓ B d) s
  simp only [s', scanIR_eq, semXIR_seq]
  generalize semXIR I (sIR (scPre ℓ B d)) s = s1 at a1 a2 a3 z1
  let L : ℕ → List ℕ := fun j ↦ ((List.range j).filter g).take (d + 3)
  have hLl : ∀ j, (L j).length ≤ d + 3 := fun j ↦ by simp only [L, List.length_take]; omega
  let Pinv : ℕ → St → Prop := fun j t ↦ Inv t.M ∧ t.M.size = s.M.size ∧
    rd t.M bF = toWord (flA B ℓ + j) ∧ rd t.M bJ = toWord j ∧ rd t.M bCnt = toWord (L j).length ∧
    rd t.M bS = toWord (sA B + (L j).length) ∧ rd t.M bDm = toWord (d + 3) ∧ rd t.M bZ0 = toWord 0 ∧
    (∀ i < (L j).length, rd t.M (sA B + i) = toWord ((L j).getD i 0)) ∧
    (∀ x, regs ≤ x → (x < sA B ∨ sA B + (d + 3) ≤ x) → rd t.M x = rd s.M x)
  have hE0 : ∀ i, i ≠ bC2 → i ≠ cTmp → rd (entryK bC2 bN2 (toWord (2 ^ ℓ)) s1.M) i = rd s1.M i :=
    fun i h1 h2 ↦ entryK_frame _ (Ne.symm h1) (Ne.symm h2)
  have hL0 : L 0 = [] := by simp [L]
  have h0 : Pinv 0 ⟨entryK bC2 bN2 (toWord (2 ^ ℓ)) s1.M, s1.o⟩ := by
    refine ⟨inv_entryK a3 (by decide), by simp only [size_entryK, z1], ?_, ?_, ?_, ?_, ?_, ?_, ?_,
      fun x hx _ ↦ ?_⟩ <;> dsimp only
    · rw [hE0 _ (by decide) (by decide), a1 _ (trkB (by decide) (by decide)), p1, Nat.add_zero]
    · rw [hE0 _ (by decide) (by decide), a1 _ (trkB (by decide) (by decide)), p2]
    · rw [hE0 _ (by decide) (by decide), a1 _ (trkB (by decide) (by decide)), p3, hL0, List.length_nil]
    · rw [hE0 _ (by decide) (by decide), a1 _ (trkB (by decide) (by decide)), p4, hL0, List.length_nil, Nat.add_zero]
    · rw [hE0 _ (by decide) (by decide), a1 _ (trkB (by decide) (by decide)), p5]
    · rw [hE0 _ (by decide) (by decide), a1 _ (trkB (by decide) (by decide)), p6]
    · rw [hL0]; intro i hi; exact absurd hi (Nat.not_lt_zero _)
    · simp only [regs] at hx
      rw [hE0 _ (by simp only [bC2]; omega) (by simp only [cTmp]; omega), a2 x (by simp only [regs]; omega)]
  have hstep : ∀ j t, j < 2 ^ ℓ → Pinv j t → Pinv (j + 1) (decS bC2 (semXIR I
      (.seq (sIR scA) (.seq (.ite bz (.seq (.store bS bJ) (sIR scInc)) (.blk [])) (sIR scB))) t)) := by
    rintro j t hj ⟨i1, i2, i3, i4, i5, i6, i7, i8, i9, i10⟩
    have ht := i1.1
    have hc := hLl j
    obtain ⟨q0, q1⟩ := scA_run (rd t.M) (rd t.M) (F := flA B ℓ + j) (c := (L j).length) (dm := d + 3) i3 i8 i5
      i7 (by omega) (by simp only [regs]; omega) (by omega) (by omega)
    rw [semXIR_seq]
    obtain ⟨a1', a2', a3', -⟩ := sIR_sem I (rd t.M) scA t (rd t.M) i1 ok_scA (fun _ _ ↦ rfl) (fun _ _ ↦ rfl) q0
    have z1' := size_sIR I scA t
    have rz := a1' bz (trkB (by decide) (by decide))
    have nA : ∀ r, Trk r → r ≠ bf → r ≠ bz → r ≠ bl → rd (semXIR I (sIR scA) t).M r = rd t.M r :=
      fun r hr h1 h2 h3 ↦ by rw [a1' r hr, sRun_frame _ _ _ _ (by simp [scA, SOp.dst]; omega)]
    -- the flag of `j` is `t`'s, which is `s`'s
    have hfl : rd t.M (flA B ℓ + j) = rd s.M (flA B ℓ + j) := i10 _ (by simp only [regs]; omega) (by omega)
    generalize semXIR I (sIR scA) t = t1 at a1' a2' a3' z1' rz nA
    rw [semXIR_seq, semXIR_ite]
    have hLs := take_filter_succ g (d + 3) j
    have eL : L (j + 1) = ((List.range (j + 1)).filter g).take (d + 3) := rfl
    have eLj : L j = ((List.range j).filter g).take (d + 3) := rfl
    rw [← eL, ← eLj] at hLs
    -- after the branch: `t2`, with the count, the list and the heap
    obtain ⟨t2, ht2, hM2, z2, r2, c2, s2, l2, f2⟩ : ∃ t2, (if rd t1.M bz = 0 then semXIR I (.blk []) t1 else
        semXIR I (.seq (.store bS bJ) (sIR scInc)) t1) = t2 ∧ Inv t2.M ∧ t2.M.size = s.M.size ∧
        (∀ r, Trk r → r ≠ bS → r ≠ bCnt → rd t2.M r = rd t1.M r) ∧
        rd t2.M bCnt = toWord (L (j + 1)).length ∧ rd t2.M bS = toWord (sA B + (L (j + 1)).length) ∧
        (∀ i < (L (j + 1)).length, rd t2.M (sA B + i) = toWord ((L (j + 1)).getD i 0)) ∧
        (∀ x, regs ≤ x → (x < sA B ∨ sA B + (d + 3) ≤ x) → rd t2.M x = rd s.M x) := by
      refine ⟨_, rfl, ?_⟩
      have hgj : rd s.M (flA B ℓ + j) = 0 ↔ g j = true := hG j hj
      by_cases hz : rd t1.M bz = 0
      · rw [if_pos hz]
        have hn : ¬ (g j = true ∧ (L j).length < d + 3) := by
          rw [rz, q1, hfl] at hz; rwa [← hgj]
        rw [if_neg hn] at hLs
        refine ⟨a3', by rw [show semXIR I (.blk []) t1 = t1 from rfl, z1', i2], fun r _ _ _ ↦ rfl, ?_, ?_,
          fun i hi ↦ ?_, fun x hx hx' ↦ ?_⟩ <;> rw [show semXIR I (.blk []) t1 = t1 from rfl]
        · rw [hLs, nA _ (trkB (by decide) (by decide)) (by decide) (by decide) (by decide), i5]
        · rw [hLs, nA _ (trkB (by decide) (by decide)) (by decide) (by decide) (by decide), i6]
        · rw [hLs] at hi ⊢; rw [a2' _ (by simp only [regs]; omega), i9 i hi]
        · rw [a2' x hx, i10 x hx hx']
      · rw [if_neg hz]
        have hy : g j = true ∧ (L j).length < d + 3 := by
          rw [rz, q1, hfl] at hz; push_neg at hz; rwa [← hgj]
        rw [if_pos hy] at hLs
        have hlen : (L (j + 1)).length = (L j).length + 1 := by rw [hLs]; simp
        have hy2 := hy.2
        rw [semXIR_seq]
        obtain ⟨w1, w2, w3⟩ := store_sem I t1 a3' (p := bS) (v := bJ) (x := sA B + (L j).length) (by decide)
          (by decide) ((nA _ (trkB (by decide) (by decide)) (by decide) (by decide) (by decide)).trans i6)
          (by simp only [regs]; omega) (by omega) (by rw [z1', i2]; omega)
        have zw := size_sem I (.store bS bJ) t1
        generalize semXIR I (.store bS bJ) t1 = tw at w1 w2 w3 zw
        have rw' : ∀ r, Trk r → rd tw.M r = rd t1.M r := fun r hr ↦ by
          have := hr.1
          simp only [regs] at this
          exact w2 r (by omega) (by rcases hr.2 with h | h <;> simp only [cTmp] <;> omega)
        obtain ⟨u0, u1, u2⟩ := scInc_run (rd tw.M) (rd tw.M) (S := sA B + (L j).length) (c := (L j).length)
          ((rw' _ (trkB (by decide) (by decide))).trans ((nA _ (trkB (by decide) (by decide)) (by decide)
            (by decide) (by decide)).trans i6))
          ((rw' _ (trkB (by decide) (by decide))).trans ((nA _ (trkB (by decide) (by decide)) (by decide)
            (by decide) (by decide)).trans i5)) (w3.2 0 (by decide))
        obtain ⟨v1, v2, v3, -⟩ := sIR_sem I (rd tw.M) scInc tw (rd tw.M) w3 ok_scInc (fun _ _ ↦ rfl)
          (fun _ _ ↦ rfl) u0
        refine ⟨v3, by rw [size_sIR, zw, z1', i2], fun r hr h1 h2 ↦ ?_, ?_, ?_, fun i hi ↦ ?_,
          fun x hx hx' ↦ ?_⟩
        · rw [v1 r hr, sRun_frame _ _ _ _ (by simp [scInc, SOp.dst]; omega), rw' r hr]
        · rw [v1 _ (trkB (by decide) (by decide)), u2, hlen]
        · rw [v1 _ (trkB (by decide) (by decide)), u1, hlen, Nat.add_assoc]
        · rw [v2 _ (by simp only [regs]; omega)]
          rw [hlen] at hi
          rw [hLs, getD_append_one (L j) j i (by omega)]
          split_ifs with h
          · rw [w2 _ (by omega) (by simp only [cTmp]; omega), a2' _ (by simp only [regs]; omega), i9 i h]
          · have e : i = (L j).length := by omega
            subst e
            rw [w1, nA _ (trkB (by decide) (by decide)) (by decide) (by decide) (by decide), i4]
        · rw [v2 x hx, w2 x (by omega) (by simp only [regs] at hx; simp only [cTmp]; omega), a2' x hx,
            i10 x hx hx']
    rw [ht2]
    obtain ⟨b0, b1, b2⟩ := scB_run (rd t2.M) (rd t2.M) (F := flA B ℓ + j) (j := j)
      ((r2 _ (trkB (by decide) (by decide)) (by decide) (by decide)).trans
        ((nA _ (trkB (by decide) (by decide)) (by decide) (by decide) (by decide)).trans i3))
      ((r2 _ (trkB (by decide) (by decide)) (by decide) (by decide)).trans
        ((nA _ (trkB (by decide) (by decide)) (by decide) (by decide) (by decide)).trans i4)) (hM2.2 0 (by decide))
    obtain ⟨e1, e2, e3, -⟩ := sIR_sem I (rd t2.M) scB t2 (rd t2.M) hM2 ok_scB (fun _ _ ↦ rfl) (fun _ _ ↦ rfl) b0
    have z3 := size_sIR I scB t2
    generalize semXIR I (sIR scB) t2 = t3 at e1 e2 e3 z3
    have hd : ∀ x, x ≠ bC2 → rd (decS bC2 t3).M x = rd t3.M x := fun x hx ↦ rd_decS (Ne.symm hx) _
    have nB : ∀ r, Trk r → r ≠ bF → r ≠ bJ → rd t3.M r = rd t2.M r := fun r hr h1 h2 ↦ by
      rw [e1 r hr, sRun_frame _ _ _ _ (by simp [scB, SOp.dst]; omega)]
    refine ⟨inv_decS e3 (by decide), by rw [size_decS, z3, z2], ?_, ?_, ?_, ?_, ?_, ?_, fun i hi ↦ ?_,
      fun x hx hx' ↦ ?_⟩
    · rw [hd _ (by decide), e1 _ (trkB (by decide) (by decide)), b1, Nat.add_assoc]
    · rw [hd _ (by decide), e1 _ (trkB (by decide) (by decide)), b2]
    · rw [hd _ (by decide), nB _ (trkB (by decide) (by decide)) (by decide) (by decide), c2]
    · rw [hd _ (by decide), nB _ (trkB (by decide) (by decide)) (by decide) (by decide), s2]
    · rw [hd _ (by decide), nB _ (trkB (by decide) (by decide)) (by decide) (by decide),
        r2 _ (trkB (by decide) (by decide)) (by decide) (by decide),
        nA _ (trkB (by decide) (by decide)) (by decide) (by decide) (by decide), i7]
    · rw [hd _ (by decide), nB _ (trkB (by decide) (by decide)) (by decide) (by decide),
        r2 _ (trkB (by decide) (by decide)) (by decide) (by decide),
        nA _ (trkB (by decide) (by decide)) (by decide) (by decide) (by decide), i8]
    · have := hLl (j + 1)
      rw [hd _ (by simp only [bC2]; omega), e2 _ (by simp only [regs]; omega), l2 i hi]
    · simp only [regs] at hx
      rw [hd _ (by simp only [bC2]; omega), e2 _ (by simp only [regs]; omega), f2 x (by simp only [regs]; omega) hx']
  have hfin := loopK_run I _ Pinv s1 a3 (c := bC2) (n := bN2) (K := 2 ^ ℓ) (by decide) (by decide) (by decide)
    ((a1 _ (trkB (by decide) (by decide))).trans p7) hL h0 hstep
  obtain ⟨f1, -, -, -, -, -, -, -, f9, f10⟩ := hfin
  exact ⟨f1, f9, f10⟩

/-! ## The builder -/

/-- **The builder's precondition**: the round register holds `r`, the heap outside the scratch is `M₀`'s. -/
def PreB (M₀ : Mem) (B ℓ r : ℕ) (s : St) : Prop := rd s.M xR = toWord r ∧ SrcEq M₀ B ℓ s.M

theorem ok_sbPro (tS : ℕ) : ∀ o ∈ sbPro tS, o.Ok := by
  simp +decide [sbPro, SOp.Ok, Trk, regs, bT, bU, bBase, bOcc, bQ, xR, cOne]

theorem sbPro_run (H f : ℕ → Word) {tS r : ℕ} (hR : f xR = toWord r) (h1 : f cOne = 1)
    (hT : r + r + tS + 1 < 2 ^ 64) (hTr : regs ≤ r + r + tS) :
    sLd H (sbPro tS) f ∧ sRun H (sbPro tS) f bBase = H (r + r + tS) ∧
      sRun H (sbPro tS) f bOcc = H (r + r + tS + 1) ∧ sRun H (sbPro tS) f bQ = toWord 0 := by
  replace hR : f 248 = toWord r := hR
  replace h1 : f 0 = 1 := h1
  simp only [regs] at hTr
  have t0 : (toWord (r + r + tS)).toNat = r + r + tS := toNat_toWord (by omega)
  have t1 : (toWord (r + r + tS + 1)).toNat = r + r + tS + 1 := toNat_toWord hT
  refine ⟨?_, ?_, ?_, ?_⟩
  · simp only [↓reduceIte, Nat.reduceEqDiff, sLd, sbPro, SOp.LdOk, SOp.step, Function.update_apply, bT, bU, bBase,
      bOcc, bQ, xR, cOne, hR, h1, add_toWord, add_one_toWord, t0, t1, regs]
    try simp
    try omega
  all_goals simp only [↓reduceIte, Nat.reduceEqDiff, sRun, sbPro, SOp.step, Function.update_apply, bT, bU, bBase,
    bOcc, bQ, xR, cOne, hR, h1, add_toWord, add_one_toWord, t0, t1]

theorem SrcEq.of_heap {M₀ M M' : Mem} {B ℓ : ℕ} (h : SrcEq M₀ B ℓ M) (hh : ∀ x, regs ≤ x → rd M' x = rd M x) :
    SrcEq M₀ B ℓ M' := fun x hx hx' ↦ (hh x hx).trans (h x hx hx')

theorem TabOk.of_heap {N B ℓ : ℕ} {M M' : Mem} (h : TabOk N B ℓ M) (hB : regs ≤ B)
    (hh : ∀ x, regs ≤ x → rd M' x = rd M x) : TabOk N B ℓ M' := fun v hv i hi ↦ by
  have := h v hv i hi
  simp only [rdK] at this ⊢
  rw [hh _ (le_trans hB (by simp only [tbA', yA]; omega)), this]

theorem FlagInv.of_heap {M₀ M M' : Mem} {N ℓ B colB str d tS r q : ℕ} (h : FlagInv M₀ N ℓ B colB str d tS r q M)
    (hB : regs ≤ B) (hh : ∀ x, regs ≤ x → rd M' x = rd M x) : FlagInv M₀ N ℓ B colB str d tS r q M' :=
  fun j hj ↦ by rw [hh _ (le_trans hB (by simp only [flA, yA]; omega))]; exact h j hj

theorem hasOut_wtabNIR' (N tb : ℕ) : hasOut (wtabNIR N tb) = false := by
  simp [wtabNIR, row0NIR, row0Body, rowNIR, rowNBody, Lvm.X.mulK, Lvm.X.invK, hasOut]

theorem hasOut_fwdNIR' (N ℓ tb : ℕ) : hasOut (fwdNIR N ℓ tb) = false := by
  simp [fwdNIR, fStepN, flevelNIR, fpairNBody, farithIR, alphaNIR, alphaBody, Lvm.X.addK, Lvm.X.mulK, hasOut]

open Classical in
/-- `sbSpec` is the listing of the flags' predicate. -/
theorem sbSpec_eq (M₀ : Mem) (N ℓ colB str d tS r : ℕ) :
    sbSpec M₀ N ℓ colB str d tS r =
      ((List.range (2 ^ ℓ)).filter fun j ↦ decide (GoodB M₀ N ℓ colB str d tS r j)).take (d + 3) := by
  unfold sbSpec
  exact congrArg (List.take (d + 3)) (List.filter_congr fun j _ ↦ decide_eq_decide.2 Iff.rfl)

open Classical in
/-- **The bridge to X6b's extractor**: `sbSpec` is `agreeS ℓ (d + 1) good` for any `good` that agrees with `GoodB`
below `2^ℓ` (for the descent, `goodAt d Tc W` once the columns hold `Tc` and the table names `W`). -/
theorem sbSpec_eq_agreeS (M : Mem) (N ℓ colB str d tS r : ℕ) {good : ℕ → Prop}
    (hg : ∀ j < 2 ^ ℓ, GoodB M N ℓ colB str d tS r j ↔ good j) :
    sbSpec M N ℓ colB str d tS r = agreeS ℓ (d + 1) good := by
  classical
  rw [sbSpec_eq, agreeS]
  congr 1
  exact List.filter_congr fun j hj ↦ decide_eq_decide.2 (hg j (List.mem_range.1 hj))

end Lvm6.X
