-- lvm6 X7a (F-X6b-4): the semantics of the descent's loops (`Lvm6XDescProg`): the lanes of a round (`lanesX_sem`),
-- a round (`roundL_sem`) and a group of rounds (`groupX_sem`), each loop by an invariant per iteration, with X6b's
-- `LoadOkB` per lane and `SbOk` per round, read at the lane and round registers. New. X8a: the builder obligation is
-- X7b's `SbOkW` (the builder may use the FD1 workspace `[sA B + |S|, fdEnd B ℓ)` as scratch, F-X7b-1).
import Lvm6XDescBuild

/-!
# The loops on the machine

* **The parts in a loop**: one loader `ld` serves every lane and one builder `sb` every round of a group; they read
  the round and lane from `rRd`, `rLn`. Their obligations are X6b's specifications at those register values:
  `LoadOkB I (rRd, rLn := r, q ; ld) ℓ B M₀ (ys r q)` (`sem_setRQ`: on a state holding `r`, `q` this is `ld`'s run) and
  `SbOkW I sb B ℓ (S r) (Q r ∧ rRd = r)` (X8a; was `SbOk`), and they write no register from `rRd` on (`AllBelow rRd`).
* **`cpyX_sem`**: the copy addressed by `rDs`, then `rDs += rSt`, `rLn += 1`.
* **`lanesX_sem`**: the lane loop's invariant after `j` lanes: `rLn = j`, `rDs = colB + str·j`, lanes `q < j` decoded
  at `colB + str·q` (`fd1 N ℓ S (ys q)`), `LamOk`, `rRd`, and the heap below `B`, in `[fdEnd, colB)` and from
  `colB + str·j` kept. **`roundL_sem`**: the builder, `Λ`, the lanes: `RoundPost` and `rRd + 1`.
* **`groupX_sem`**: for a heap predicate `Q j` per round (`HeapPred`) carried by every round
  (`Q j s → RoundPost … (Ss j) (ys j) s s' → Q (j + 1) s'`), the rounds' loop ends in `Q nr`; `Inv`, the output, the
  heap below `B` kept, `rRd = r0 + nr`.
-/

set_option autoImplicit false

namespace Lvm6.X

open RecursionFast Lvm.X Lvm.Nb Lvm6.FD Finset

theorem ne_of_regs {x c : ℕ} (hx : regs ≤ x) (hc : c < regs) : x ≠ c := (lt_of_lt_of_le hc hx).ne'

/-- **The register-indexed part**: on a state holding `r` in `rRd` and `q` in `rLn`, setting them is no step. -/
theorem sem_setRQ (I : Array Word) (ld : XIR) (s : St) {r q : ℕ} (hr : rd s.M rRd = toWord r)
    (hq : rd s.M rLn = toWord q) :
    semXIR I (.seq (.blk [.const rRd (toWord r), .const rLn (toWord q)]) ld) s = semXIR I ld s := by
  have e : (⟨runPrims [.const rRd (toWord r), .const rLn (toWord q)] s.M, s.o⟩ : St) = s := by
    obtain ⟨M, o⟩ := s
    simp only at hr hq
    simp only [runPrims, List.foldl, Prim.run]
    rw [← hr, set_rd_self, ← hq, set_rd_self]
  rw [semXIR_seq, sem_blk', e]

/-- Registers from `rRd` on survive a part that does not name them. -/
theorem rd_low (I : Array Word) {P : XIR} (hw : WF P) (hl : AllBelow rRd P) (s : St) (hM : Inv s.M) {x : ℕ}
    (h1 : rRd ≤ x) (h2 : x < regs) : rd (semXIR I P s).M x = rd s.M x :=
  frame I P s hw hM x h2 (nw_of_allBelow h1 hl)

/-! ## The copy -/

/-- **The copy addressed by `rDs`**: `2^ℓ` words from `outA B ℓ` to `d`, then `rDs := d + k`, `rLn := j + 1`. -/
theorem cpyX_sem (I : Array Word) (s : St) (hM : Inv s.M) {ℓ B d k j : ℕ} (hB : regs ≤ B)
    (hd : outA B ℓ + 2 ^ ℓ ≤ d) (h64 : d + k < 2 ^ 64) (hk : 2 ^ ℓ ≤ k) (hsz : d + 2 ^ ℓ ≤ s.M.size)
    (hD : rd s.M rDs = toWord d) (hK : rd s.M rSt = toWord k) (hQ : rd s.M rLn = toWord j) :
    (∀ x < 2 ^ ℓ, rd (semXIR I (cpyX ℓ B) s).M (d + x) = rd s.M (outA B ℓ + x)) ∧
    (∀ x, regs ≤ x → (x < d ∨ d + 2 ^ ℓ ≤ x) → rd (semXIR I (cpyX ℓ B) s).M x = rd s.M x) ∧
    Inv (semXIR I (cpyX ℓ B) s).M ∧ (semXIR I (cpyX ℓ B) s).o = s.o ∧
    rd (semXIR I (cpyX ℓ B) s).M rDs = toWord (d + k) ∧ rd (semXIR I (cpyX ℓ B) s).M rLn = toWord (j + 1) ∧
    ∀ r, rRd ≤ r → r < regs → r ≠ rDs → r ≠ rLn → rd (semXIR I (cpyX ℓ B) s).M r = rd s.M r := by
  have hs := hM.1
  have eO : outA B ℓ = B + 4096 + 3 * 2 ^ ℓ := rfl
  simp only [regs] at hs hB
  rw [cpyX, semXIR_seq]
  have w0 : WF (.blk [.const ySr (toWord (outA B ℓ)), .const yStr 1, .op .or yDs rDs rDs]) := by
    simp +decide [WF, Prim.dst, ySr, yStr, yDs]
  have hM0 := inv_sem I w0 hM
  have z0 := size_sem I (.blk [.const ySr (toWord (outA B ℓ)), .const yStr 1, .op .or yDs rDs rDs]) s
  have r0 : rd (semXIR I (.blk [.const ySr (toWord (outA B ℓ)), .const yStr 1, .op .or yDs rDs rDs]) s).M ySr =
        toWord (outA B ℓ) ∧
      rd (semXIR I (.blk [.const ySr (toWord (outA B ℓ)), .const yStr 1, .op .or yDs rDs rDs]) s).M yDs =
        toWord d ∧
      rd (semXIR I (.blk [.const ySr (toWord (outA B ℓ)), .const yStr 1, .op .or yDs rDs rDs]) s).M yStr =
        toWord 1 := by
    rw [sem_blk']; simp only [runPrims, List.foldl, Prim.run]
    refine ⟨?_, ?_, ?_⟩ <;>
    simp (disch := first | decide | (simp only [size_set, ySr, yStr, yDs]; omega)) only [rd_set_self, rd_set_ne,
      or_self_eval, hD] <;> rfl
  have k0 : ∀ r, r ≠ ySr → r ≠ yStr → r ≠ yDs →
      rd (semXIR I (.blk [.const ySr (toWord (outA B ℓ)), .const yStr 1, .op .or yDs rDs rDs]) s).M r =
        rd s.M r := fun r h1 h2 h3 ↦ by
    refine rd_blk_of_not_dst I _ s ?_
    simp only [List.mem_cons, List.mem_nil_iff, or_false]
    rintro p (rfl | rfl | rfl) <;> simp only [Prim.dst] <;> exact Ne.symm (by assumption)
  have o0 : (semXIR I (.blk [.const ySr (toWord (outA B ℓ)), .const yStr 1, .op .or yDs rDs rDs]) s).o = s.o := rfl
  generalize semXIR I (.blk [.const ySr (toWord (outA B ℓ)), .const yStr 1, .op .or yDs rDs rDs]) s = s0
    at hM0 z0 r0 k0 o0
  rw [semXIR_seq]
  have hp : 2 ^ ℓ < 2 ^ 64 := by omega
  obtain ⟨a1, a2, a3⟩ := mcpLoop_sem I s0 hM0 (n := 2 ^ ℓ) (src := outA B ℓ) (str := 1) (dst := d) hp
    (by omega) (by simp only [regs]; omega) (by omega) (by omega) (fun i hi ↦ Or.inl (by omega))
    (fun i _ ↦ by simp only [regs]; omega) r0.1 r0.2.1 r0.2.2
  have a4 := sem_o I (mcpLoop (2 ^ ℓ)) s0 rfl
  have z1 := size_sem I (mcpLoop (2 ^ ℓ)) s0
  have kr : ∀ r, r < regs → KeepC r → rd (semXIR I (mcpLoop (2 ^ ℓ)) s0).M r = rd s0.M r := fun r hr hk ↦
    a2 r hk (Or.inl (by simp only [regs] at hr; omega))
  generalize semXIR I (mcpLoop (2 ^ ℓ)) s0 = s1 at a1 a2 a3 a4 z1 kr
  have kc : ∀ r, rRd ≤ r → r < regs → KeepC r := fun r h1 h2 ↦ by
    simp only [KeepC, rRd, regs, yV, ySr, yDs, yC, yN, cTmp] at h1 h2 ⊢
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> omega
  have q1 : ∀ r, rRd ≤ r → r < regs → rd s1.M r = rd s.M r := fun r h1 h2 ↦ by
    rw [kr r h2 (kc r h1 h2), k0 r (by simp only [rRd, ySr] at h1 ⊢; omega) (by simp only [rRd, yStr] at h1 ⊢; omega)
      (by simp only [rRd, yDs] at h1 ⊢; omega)]
  have h1 : rd s1.M cOne = 1 := a3.2 0 (by decide)
  have ws : WF (.blk [.op .add rDs rDs rSt, .op .add rLn rLn cOne]) := by simp +decide [WF]
  refine ⟨fun x hx ↦ ?_, fun x hx hx' ↦ ?_, inv_sem I ws a3, a4.trans o0, ?_, ?_, fun r h1 h2 h3 h4 ↦ ?_⟩
  · rw [rd_blk_of_not_dst I _ s1 (by simp [Prim.dst, rDs, rLn]; omega), a1 x hx, Nat.one_mul,
      k0 _ (by simp only [ySr]; omega) (by simp only [yStr]; omega) (by simp only [yDs]; omega)]
  · rw [rd_blk_of_not_dst I _ s1 (by simp [Prim.dst, rDs, rLn]; simp only [regs] at hx; omega),
      a2 x (keepC_of_regs hx) hx', k0 _ (by simp only [ySr, regs] at hx ⊢; omega) (by simp only [yStr, regs] at hx ⊢; omega)
        (by simp only [yDs, regs] at hx ⊢; omega)]
  · rw [sem_blk']; simp only [runPrims, List.foldl, Prim.run]
    simp (disch := first | decide | (simp only [size_set, rDs, rLn]; omega)) only [rd_set_self, rd_set_ne]
    rw [q1 rDs (by decide) (by decide), q1 rSt (by decide) (by decide), hD, hK, add_toWord]
  · rw [sem_blk']; simp only [runPrims, List.foldl, Prim.run]
    simp (disch := first | decide | (simp only [size_set, rDs, rLn]; omega)) only [rd_set_self, rd_set_ne]
    rw [h1, q1 rLn (by decide) (by decide), hQ, add_one_toWord]
  · rw [rd_blk_of_not_dst I _ s1 (by simp [Prim.dst]; exact ⟨Ne.symm h3, Ne.symm h4⟩), q1 r h1 h2]

/-! ## The lanes of a round -/

/-- **The lanes of a round on the machine**, a loop over the lanes: lane `q`'s decoded word is at `colB + str·q`. -/
theorem lanesX_sem (I : Array Word) {N ℓ B colB str n r : ℕ} {S : List ℕ} (ld : XIR) (M₀ : Mem)
    (ys : ℕ → ℕ → BF64) (hN : ℓ + 1 ≤ N) (hN64 : N ≤ 64) (hB : regs ≤ B) (hm : S.length ≤ 2 ^ ℓ)
    (hSn : ∀ j ∈ S, j < 2 ^ ℓ) (hcol : fdEnd B ℓ ≤ colB) (hstr : 2 ^ ℓ ≤ str) (h64 : colB + str * n < 2 ^ 64)
    (hw : WF ld) (hl : AllBelow rRd ld)
    (hld : ∀ q < n, LoadOkB I (.seq (.blk [.const rRd (toWord r), .const rLn (toWord q)]) ld) ℓ B M₀ (ys q))
    (s : St) (hM : Inv s.M) (hL : LamOk N ℓ B S s.M) (h0 : ∀ x, regs ≤ x → x < B → rd s.M x = rd M₀ x)
    (hsz : colB + str * n ≤ s.M.size) (hR : rd s.M rRd = toWord r) (hQ : rd s.M rLn = toWord 0)
    (hD : rd s.M rDs = toWord colB) (hK : rd s.M rSt = toWord str) (hn : rd s.M nLn = toWord n) :
    (∀ q < n, ∀ x < 2 ^ ℓ, rdK (semXIR I (lanesX N ℓ S.length B ld n) s).M (colB + str * q + x) =
        fd1 N ℓ S (ys q) x) ∧
      Inv (semXIR I (lanesX N ℓ S.length B ld n) s).M ∧ (semXIR I (lanesX N ℓ S.length B ld n) s).o = s.o ∧
      (semXIR I (lanesX N ℓ S.length B ld n) s).M.size = s.M.size ∧
      LamOk N ℓ B S (semXIR I (lanesX N ℓ S.length B ld n) s).M ∧
      rd (semXIR I (lanesX N ℓ S.length B ld n) s).M rRd = toWord r ∧
      ∀ x, regs ≤ x → (x < B ∨ (fdEnd B ℓ ≤ x ∧ x < colB) ∨ colB + str * n ≤ x) →
        rd (semXIR I (lanesX N ℓ S.length B ld n) s).M x = rd s.M x := by
  have hB' : 256 ≤ B := hB
  have eE : fdEnd B ℓ = B + 4096 + 11 * 2 ^ ℓ := rfl
  have eY : yA B ℓ = B + 4096 + 2 ^ ℓ := rfl
  have eG : gA B ℓ = B + 4096 + 2 * 2 ^ ℓ := rfl
  have eO : outA B ℓ = B + 4096 + 3 * 2 ^ ℓ := rfl
  have eT : tA B ℓ = B + 4096 + 4 * 2 ^ ℓ := rfl
  have hp1 : 1 ≤ 2 ^ ℓ := Nat.one_le_two_pow
  have hnn : n ≤ str * n := Nat.le_mul_of_pos_left n (by omega)
  have hn64 : n < 2 ^ 64 := by omega
  let P : ℕ → St → Prop := fun j s' ↦ Inv s'.M ∧ s'.M.size = s.M.size ∧ s'.o = s.o ∧ LamOk N ℓ B S s'.M ∧
    rd s'.M rRd = toWord r ∧ rd s'.M rLn = toWord j ∧ rd s'.M rDs = toWord (colB + str * j) ∧
    rd s'.M rSt = toWord str ∧
    (∀ q < j, ∀ x < 2 ^ ℓ, rdK s'.M (colB + str * q + x) = fd1 N ℓ S (ys q) x) ∧
    ∀ x, regs ≤ x → (x < B ∨ (fdEnd B ℓ ≤ x ∧ x < colB) ∨ colB + str * j ≤ x) → rd s'.M x = rd s.M x
  have hE : ∀ x, x ≠ cLn → x ≠ cTmp → rd (entryK cLn nLn (toWord n) s.M) x = rd s.M x :=
    fun x h1 h2 ↦ entryK_frame _ (Ne.symm h1) (Ne.symm h2)
  have hEr : ∀ x, regs ≤ x → rd (entryK cLn nLn (toWord n) s.M) x = rd s.M x := fun x hx ↦
    hE x (ne_of_regs hx (by decide)) (ne_of_regs hx (by decide))
  have hP0 : P 0 ⟨entryK cLn nLn (toWord n) s.M, s.o⟩ := by
    refine ⟨inv_entryK hM (by decide), size_entryK .., rfl,
      lamOk_of_frame' hN64 hL (fun x hx _ _ ↦ hEr x hx) hB hm, ?_, ?_, ?_, ?_,
      fun q hq ↦ absurd hq (Nat.not_lt_zero _), fun x hx _ ↦ hEr x hx⟩ <;> dsimp only
    · rw [hE rRd (by decide) (by decide), hR]
    · rw [hE rLn (by decide) (by decide), hQ]
    · rw [hE rDs (by decide) (by decide), hD, Nat.mul_zero, Nat.add_zero]
    · rw [hE rSt (by decide) (by decide), hK]
  have hstep : ∀ j s', j < n → P j s' → P (j + 1) (decS cLn (semXIR I (laneX N ℓ S.length B ld) s')) := by
    rintro j s' hj ⟨i1, i2, i3, i4, i5, i6, i7, i8, i9, i10⟩
    have hsj : colB + str * j + str ≤ colB + str * n := by
      have := Nat.mul_le_mul_left str (show j + 1 ≤ n by omega); rw [Nat.mul_succ] at this; omega
    have h0' : ∀ x, regs ≤ x → x < B → rd s'.M x = rd M₀ x := fun x hx hxB ↦ by
      rw [i10 x hx (Or.inl hxB), h0 x hx hxB]
    simp only [laneX, semXIR_seq]
    -- the loader
    obtain ⟨a1, a2, a3, a4⟩ := hld j hj s' i1 (by omega) h0'
    rw [sem_setRQ I ld s' i5 i6] at a1 a2 a3 a4
    have r1 : ∀ x, rRd ≤ x → x < regs → rd (semXIR I ld s').M x = rd s'.M x := fun x h1 h2 ↦
      rd_low I hw hl s' i1 h1 h2
    have z1 := size_sem I ld s'
    have L1 : LamOk N ℓ B S (semXIR I ld s').M := lamOk_of_frame' hN64 i4
      (fun x hx _ hx' ↦ a4 x hx (by omega)) hB hm
    generalize semXIR I ld s' = s1 at a1 a2 a3 a4 r1 z1 L1
    -- the lane
    obtain ⟨b1, b2, b3, b4⟩ := laneIR_sem I s1 a2 (y := ys j) hN hN64 hB (by omega) (by omega) hm hSn L1 a1
    have r2 : ∀ x, rRd ≤ x → x < regs → rd (semXIR I (laneIR N ℓ S.length B) s1).M x = rd s1.M x :=
      fun x h1 h2 ↦ frame I _ s1 (wf_laneIR ..) a2 x h2 (nw_laneIR _ _ _ _ (by simp only [rRd] at h1; omega))
    have z2 := size_sem I (laneIR N ℓ S.length B) s1
    generalize semXIR I (laneIR N ℓ S.length B) s1 = s2 at b1 b2 b3 b4 r2 z2
    -- the copy
    obtain ⟨c1, c2, c3, c4, c5, c6, c7⟩ := cpyX_sem I s2 b2 (ℓ := ℓ) (B := B) (d := colB + str * j) (k := str)
      (j := j) hB (by omega) (by omega) hstr (by omega)
      (by rw [r2 rDs (by decide) (by decide), r1 rDs (by decide) (by decide), i7])
      (by rw [r2 rSt (by decide) (by decide), r1 rSt (by decide) (by decide), i8])
      (by rw [r2 rLn (by decide) (by decide), r1 rLn (by decide) (by decide), i6])
    have z3 := size_sem I (cpyX ℓ B) s2
    generalize semXIR I (cpyX ℓ B) s2 = s3 at c1 c2 c3 c4 c5 c6 c7 z3
    have dS : ∀ x, x ≠ cLn → rd (decS cLn s3).M x = rd s3.M x := fun x hx ↦ rd_decS (Ne.symm hx) _
    have e1 : str * (j + 1) = str * j + str := Nat.mul_succ str j
    refine ⟨inv_decS c3 (by decide), by rw [size_decS]; omega, c4.trans (b3.trans (a3.trans i3)),
      lamOk_of_frame' hN64 L1 (fun x hx hxE hx' ↦ by
        rw [dS x (ne_of_regs hx (by decide)), c2 x hx (Or.inl (by omega)), b4 x hx (by omega)]) hB hm,
      ?_, ?_, ?_, ?_, fun q hq x hx ↦ ?_, fun x hx hx' ↦ ?_⟩
    · rw [dS rRd (by decide), c7 rRd (by decide) (by decide) (by decide) (by decide),
        r2 rRd (by decide) (by decide), r1 rRd (by decide) (by decide), i5]
    · rw [dS rLn (by decide), c6]
    · rw [dS rDs (by decide), c5, e1, Nat.add_assoc]
    · rw [dS rSt (by decide), c7 rSt (by decide) (by decide) (by decide) (by decide),
        r2 rSt (by decide) (by decide), r1 rSt (by decide) (by decide), i8]
    · by_cases hqj : q = j
      · subst hqj
        rw [← b1 x hx]
        exact rdK_eq ((dS _ (ne_of_regs (by simp only [regs]; omega) (by decide))).trans (c1 x hx))
      · have hq' : q < j := by omega
        have hlt : colB + str * q + x < colB + str * j := by
          have := Nat.mul_le_mul_left str (show q + 1 ≤ j by omega); rw [Nat.mul_succ] at this; omega
        rw [← i9 q hq' x hx]
        refine rdK_eq ?_
        have hx0 : regs ≤ colB + str * q + x := by simp only [regs]; omega
        rw [dS _ (ne_of_regs hx0 (by decide)), c2 _ hx0 (Or.inl hlt), b4 _ hx0 (by omega), a4 _ hx0 (by omega)]
    · rw [e1] at hx'
      rw [dS x (ne_of_regs hx (by decide)), c2 x hx (by omega), b4 x hx (by omega), a4 x hx (by omega),
        i10 x hx (by omega)]
  have hfin := loopK_run I (laneX N ℓ S.length B ld) P s hM (by decide : 4 < cLn) (by decide : cLn < regs)
    (by decide : nLn ≠ cLn) hn hn64 hP0 hstep
  obtain ⟨f1, f2, f3, f4, f5, -, -, -, f9, f10⟩ := hfin
  exact ⟨f9, f1, f3, f2, f4, f5, f10⟩

/-! ## A round -/

/-- What a round leaves: the lanes decoded against `S`, `Inv`, the output, the heap below `B`, in `[fdEnd, colB)`
and from `colB + str·n` kept. -/
def RoundPost (N ℓ B colB str n : ℕ) (S : List ℕ) (ys : ℕ → ℕ → BF64) (s s' : St) : Prop :=
  Inv s'.M ∧ s'.M.size = s.M.size ∧ s'.o = s.o ∧
    (∀ q < n, ∀ x < 2 ^ ℓ, rdK s'.M (colB + str * q + x) = fd1 N ℓ S (ys q) x) ∧
    ∀ x, regs ≤ x → (x < B ∨ (fdEnd B ℓ ≤ x ∧ x < colB) ∨ colB + str * n ≤ x) → rd s'.M x = rd s.M x

/-- **A round on the machine**: the builder writes `S`, `Λ` is built, the lane loop decodes every lane; the round
index moves on. -/
theorem roundL_sem (I : Array Word) {N ℓ B colB str r : ℕ} (g : GroupX) {S : List ℕ} {Pre : St → Prop}
    (M₀ : Mem) (ys : ℕ → ℕ → BF64) (hN : ℓ + 1 ≤ N) (hN64 : N ≤ 64) (hB : regs ≤ B) (hm : S.length ≤ 2 ^ ℓ)
    (hSn : ∀ j ∈ S, j < 2 ^ ℓ) (hcol : fdEnd B ℓ ≤ colB) (hstr : 2 ^ ℓ ≤ str) (h64 : colB + str * g.n < 2 ^ 64)
    (hmS : S.length = g.m) (hsw : WF g.sb) (hsl : AllBelow rRd g.sb) (hw : WF g.ld) (hl : AllBelow rRd g.ld)
    (hsb : SbOkW I g.sb B ℓ S Pre)
    (hld : ∀ q < g.n, LoadOkB I (.seq (.blk [.const rRd (toWord r), .const rLn (toWord q)]) g.ld) ℓ B M₀ (ys q))
    (s : St) (hM : Inv s.M) (hP : Pre s) (h0 : ∀ x, regs ≤ x → x < B → rd s.M x = rd M₀ x)
    (hsz : colB + str * g.n ≤ s.M.size) (hR : rd s.M rRd = toWord r) :
    RoundPost N ℓ B colB str g.n S ys s (semXIR I (roundL N ℓ B colB str g) s) ∧
      rd (semXIR I (roundL N ℓ B colB str g) s).M rRd = toWord (r + 1) := by
  have hB' : 256 ≤ B := hB
  have eE : fdEnd B ℓ = B + 4096 + 11 * 2 ^ ℓ := rfl
  have eS : sA B = B + 4096 := rfl
  have eT : tA B ℓ = B + 4096 + 4 * 2 ^ ℓ := rfl
  have hp1 : 1 ≤ 2 ^ ℓ := Nat.one_le_two_pow
  have hnn : g.n ≤ str * g.n := Nat.le_mul_of_pos_left g.n (by omega)
  rw [roundL, ← hmS, semXIR_seq]
  -- the builder
  obtain ⟨a1, a2, a3, a4⟩ := hsb s hP hM (by omega)
  have z1 := size_sem I g.sb s
  have r1 : ∀ x, rRd ≤ x → x < regs → rd (semXIR I g.sb s).M x = rd s.M x := fun x h1 h2 ↦
    rd_low I hsw hsl s hM h1 h2
  have h01 : ∀ x, regs ≤ x → x < B → rd (semXIR I g.sb s).M x = rd M₀ x := fun x hx hxB ↦ by
    rw [a4 x hx (Or.inl (by omega)), h0 x hx hxB]
  generalize semXIR I g.sb s = s1 at a1 a2 a3 a4 z1 r1 h01
  rw [semXIR_seq]
  -- `Λ`
  obtain ⟨b1, b2, b3, b4⟩ := lamIR_sem I s1 a2 hN hN64 hB (by omega) (by omega) hm hSn a1
  have z2 := size_sem I (lamIR N ℓ S.length B) s1
  have r2 : ∀ x, rRd ≤ x → x < regs → rd (semXIR I (lamIR N ℓ S.length B) s1).M x = rd s1.M x :=
    fun x h1 h2 ↦ frame I _ s1 (wf_lamIR ..) a2 x h2 (nw_lamIR _ _ _ _ (by simp only [rRd] at h1; omega))
  have h02 : ∀ x, regs ≤ x → x < B → rd (semXIR I (lamIR N ℓ S.length B) s1).M x = rd M₀ x := fun x hx hxB ↦ by
    rw [b4 x hx (Or.inl hxB), h01 x hx hxB]
  generalize semXIR I (lamIR N ℓ S.length B) s1 = s2 at b1 b2 b3 b4 z2 r2 h02
  rw [semXIR_seq]
  -- the lane registers
  have hs2 : 256 ≤ s2.M.size := by have := b2.1; simpa only [regs] using this
  have w3 : WF (.blk [.const rLn 0, .const rDs (toWord colB), .const rSt (toWord str), .const nLn (toWord g.n)]) :=
    by simp +decide [WF, Prim.dst, rLn, rDs, rSt, nLn]
  have hM3 := inv_sem I w3 b2
  have z3 := size_sem I (.blk [.const rLn 0, .const rDs (toWord colB), .const rSt (toWord str),
    .const nLn (toWord g.n)]) s2
  have v3 : rd (semXIR I (.blk [.const rLn 0, .const rDs (toWord colB), .const rSt (toWord str),
        .const nLn (toWord g.n)]) s2).M rLn = toWord 0 ∧
      rd (semXIR I (.blk [.const rLn 0, .const rDs (toWord colB), .const rSt (toWord str),
        .const nLn (toWord g.n)]) s2).M rDs = toWord colB ∧
      rd (semXIR I (.blk [.const rLn 0, .const rDs (toWord colB), .const rSt (toWord str),
        .const nLn (toWord g.n)]) s2).M rSt = toWord str ∧
      rd (semXIR I (.blk [.const rLn 0, .const rDs (toWord colB), .const rSt (toWord str),
        .const nLn (toWord g.n)]) s2).M nLn = toWord g.n := by
    rw [sem_blk']; simp only [runPrims, List.foldl, Prim.run]
    refine ⟨?_, ?_, ?_, ?_⟩ <;>
    simp (disch := first | decide | (simp only [size_set, rLn, rDs, rSt, nLn]; omega)) only [rd_set_self,
      rd_set_ne] <;> rfl
  have k3 : ∀ x, (x = rRd ∨ regs ≤ x) → rd (semXIR I (.blk [.const rLn 0, .const rDs (toWord colB),
      .const rSt (toWord str), .const nLn (toWord g.n)]) s2).M x = rd s2.M x := fun x hx ↦ by
    refine rd_blk_of_not_dst I _ s2 ?_
    simp only [List.mem_cons, List.mem_nil_iff, or_false]
    rintro p (rfl | rfl | rfl | rfl) <;> simp only [Prim.dst] <;> rcases hx with rfl | hx <;>
      first | decide | (simp only [regs, rLn, rDs, rSt, nLn] at hx ⊢; omega)
  have o3 : (semXIR I (.blk [.const rLn 0, .const rDs (toWord colB), .const rSt (toWord str),
    .const nLn (toWord g.n)]) s2).o = s2.o := rfl
  generalize semXIR I (.blk [.const rLn 0, .const rDs (toWord colB), .const rSt (toWord str),
    .const nLn (toWord g.n)]) s2 = s3 at hM3 z3 v3 k3 o3
  have L3 : LamOk N ℓ B S s3.M := lamOk_of_frame' hN64 b1 (fun x hx _ _ ↦ k3 x (Or.inr hx)) hB hm
  rw [semXIR_seq]
  -- the lanes
  obtain ⟨c1, c2, c3, c4, -, c6, c7⟩ := lanesX_sem I g.ld M₀ ys hN hN64 hB hm hSn hcol hstr h64 hw hl hld s3 hM3
    L3 (fun x hx hxB ↦ by rw [k3 x (Or.inr hx), h02 x hx hxB]) (by omega)
    (by rw [k3 rRd (Or.inl rfl), r2 rRd le_rfl (by decide), r1 rRd le_rfl (by decide), hR]) v3.1 v3.2.1 v3.2.2.1
    v3.2.2.2
  generalize semXIR I (lanesX N ℓ S.length B g.ld g.n) s3 = s4 at c1 c2 c3 c4 c6 c7
  -- the round index
  have h1 : rd s4.M cOne = 1 := c2.2 0 (by decide)
  have kb : ∀ x, regs ≤ x → rd (semXIR I (.blk [.op .add rRd rRd cOne]) s4).M x = rd s4.M x := fun x hx ↦
    rd_blk_of_not_dst I _ s4 (by simp only [List.mem_singleton, forall_eq, Prim.dst]; exact
      (ne_of_regs hx (by decide)).symm)
  refine ⟨⟨inv_sem I (P := .blk [.op .add rRd rRd cOne]) (by simp +decide [WF, Prim.dst, rRd]) c2,
    by rw [size_sem]; omega, c3.trans (o3.trans (b3.trans a3)), fun q hq x hx ↦ ?_, fun x hx hx' ↦ ?_⟩, ?_⟩
  · rw [← c1 q hq x hx]
    exact rdK_eq (kb _ (by simp only [regs]; omega))
  · rw [kb x hx, c7 x hx hx', k3 x (Or.inr hx), b4 x hx (by omega), a4 x hx (by omega)]
  · rw [sem_blk']; simp only [runPrims, List.foldl, Prim.run]
    rw [rd_set_self (by simp only [rRd]; omega), h1, c6, add_one_toWord]

/-! ## A group of rounds -/

/-- A predicate of the heap (and the output): registers do not matter. -/
def HeapPred (Q : St → Prop) : Prop :=
  ∀ s s' : St, s'.M.size = s.M.size → s'.o = s.o → (∀ x, regs ≤ x → rd s'.M x = rd s.M x) → Q s → Q s'

/-- **A group of rounds on the machine**, a loop over the rounds: round `j` (index `r0 + j`) runs the builder of
`Ss j` and the lanes `ys j`; an invariant `Q` that every round carries holds after the group. -/
theorem groupX_sem (I : Array Word) {N ℓ B colB str r0 : ℕ} (g : GroupX) (M₀ : Mem) (Ss : ℕ → List ℕ)
    (ys : ℕ → ℕ → ℕ → BF64) (Q : ℕ → St → Prop) (hN : ℓ + 1 ≤ N) (hN64 : N ≤ 64) (hB : regs ≤ B)
    (hcol : fdEnd B ℓ ≤ colB) (hstr : 2 ^ ℓ ≤ str) (h64 : colB + str * g.n < 2 ^ 64) (hr64 : r0 + g.nr < 2 ^ 64)
    (hmS : ∀ j < g.nr, (Ss j).length = g.m) (hm : g.m ≤ 2 ^ ℓ) (hSn : ∀ j < g.nr, ∀ x ∈ Ss j, x < 2 ^ ℓ)
    (hsw : WF g.sb) (hsl : AllBelow rRd g.sb) (hw : WF g.ld) (hl : AllBelow rRd g.ld) (hQ : ∀ j, HeapPred (Q j))
    (hsb : ∀ j < g.nr, SbOkW I g.sb B ℓ (Ss j) (fun s ↦ Q j s ∧ rd s.M rRd = toWord (r0 + j)))
    (hld : ∀ j < g.nr, ∀ q < g.n,
      LoadOkB I (.seq (.blk [.const rRd (toWord (r0 + j)), .const rLn (toWord q)]) g.ld) ℓ B M₀ (ys j q))
    (hstep : ∀ j < g.nr, ∀ s s', Q j s → RoundPost N ℓ B colB str g.n (Ss j) (ys j) s s' → Q (j + 1) s')
    (s : St) (hM : Inv s.M) (hQ0 : Q 0 s) (hR : rd s.M rRd = toWord r0)
    (h0 : ∀ x, regs ≤ x → x < B → rd s.M x = rd M₀ x) (hsz : colB + str * g.n ≤ s.M.size) :
    Q g.nr (semXIR I (groupX N ℓ B colB str g) s) ∧ Inv (semXIR I (groupX N ℓ B colB str g) s).M ∧
      (semXIR I (groupX N ℓ B colB str g) s).o = s.o ∧
      (semXIR I (groupX N ℓ B colB str g) s).M.size = s.M.size ∧
      rd (semXIR I (groupX N ℓ B colB str g) s).M rRd = toWord (r0 + g.nr) ∧
      ∀ x, regs ≤ x → x < B → rd (semXIR I (groupX N ℓ B colB str g) s).M x = rd M₀ x := by
  have hs := hM.1
  simp only [regs] at hs
  rw [groupX, semXIR_seq]
  have w0 : WF (.blk [.const nRd (toWord g.nr)]) := by simp +decide [WF, Prim.dst, nRd]
  have hM0 := inv_sem I w0 hM
  have z0 := size_sem I (.blk [.const nRd (toWord g.nr)]) s
  have v0 : rd (semXIR I (.blk [.const nRd (toWord g.nr)]) s).M nRd = toWord g.nr := by
    rw [sem_blk']; simp only [runPrims, List.foldl, Prim.run]
    rw [rd_set_self (by simp only [nRd]; omega)]
  have k0 : ∀ x, x ≠ nRd → rd (semXIR I (.blk [.const nRd (toWord g.nr)]) s).M x = rd s.M x := fun x hx ↦
    rd_blk_of_not_dst I _ s (by simp only [List.mem_singleton, forall_eq, Prim.dst]; exact Ne.symm hx)
  have Q0 : Q 0 (semXIR I (.blk [.const nRd (toWord g.nr)]) s) :=
    hQ 0 s _ z0 rfl (fun x hx ↦ k0 x (ne_of_regs hx (by decide))) hQ0
  have o0 : (semXIR I (.blk [.const nRd (toWord g.nr)]) s).o = s.o := rfl
  generalize semXIR I (.blk [.const nRd (toWord g.nr)]) s = s0 at hM0 z0 v0 k0 Q0 o0
  let P : ℕ → St → Prop := fun j s' ↦ Q j s' ∧ Inv s'.M ∧ s'.o = s.o ∧ s'.M.size = s.M.size ∧
    rd s'.M rRd = toWord (r0 + j) ∧ ∀ x, regs ≤ x → x < B → rd s'.M x = rd M₀ x
  have hE : ∀ x, x ≠ cRd → x ≠ cTmp → rd (entryK cRd nRd (toWord g.nr) s0.M) x = rd s0.M x :=
    fun x h1 h2 ↦ entryK_frame _ (Ne.symm h1) (Ne.symm h2)
  have hEr : ∀ x, regs ≤ x → rd (entryK cRd nRd (toWord g.nr) s0.M) x = rd s0.M x := fun x hx ↦
    hE x (ne_of_regs hx (by decide)) (ne_of_regs hx (by decide))
  have hP0 : P 0 ⟨entryK cRd nRd (toWord g.nr) s0.M, s0.o⟩ := by
    refine ⟨hQ 0 s0 _ (size_entryK ..) rfl hEr Q0, inv_entryK hM0 (by decide), o0, (size_entryK ..).trans z0,
      ?_, fun x hx hxB ↦ ?_⟩ <;> dsimp only
    · rw [hE rRd (by decide) (by decide), k0 rRd (by decide), hR, Nat.add_zero]
    · rw [hEr x hx, k0 x (ne_of_regs hx (by decide)), h0 x hx hxB]
  have hstep' : ∀ j s', j < g.nr → P j s' →
      P (j + 1) (decS cRd (semXIR I (roundL N ℓ B colB str g) s')) := by
    rintro j s' hj ⟨i1, i2, i3, i4, i5, i6⟩
    obtain ⟨⟨p1, p2, p3, p4, p5⟩, p6⟩ := roundL_sem I g (S := Ss j)
      (Pre := fun s ↦ Q j s ∧ rd s.M rRd = toWord (r0 + j)) M₀ (ys j) hN hN64 hB (by rw [hmS j hj]; exact hm)
      (hSn j hj) hcol hstr h64 (hmS j hj) hsw hsl hw hl (hsb j hj) (hld j hj) s' i2 ⟨i1, i5⟩ i6
      (by omega) i5
    have q1 := hstep j hj s' _ i1 ⟨p1, p2, p3, p4, p5⟩
    generalize semXIR I (roundL N ℓ B colB str g) s' = s'' at p1 p2 p3 p4 p5 p6 q1
    have dS : ∀ x, x ≠ cRd → rd (decS cRd s'').M x = rd s''.M x := fun x hx ↦ rd_decS (Ne.symm hx) _
    refine ⟨hQ (j + 1) s'' _ (size_decS ..) rfl (fun x hx ↦ dS x (ne_of_regs hx (by decide))) q1,
      inv_decS p1 (by decide), p3.trans i3, by rw [size_decS]; omega, ?_, fun x hx hxB ↦ ?_⟩
    · rw [dS rRd (by decide), p6, Nat.add_assoc]
    · rw [dS x (ne_of_regs hx (by decide)), p5 x hx (Or.inl hxB), i6 x hx hxB]
  have hfin := loopK_run I (roundL N ℓ B colB str g) P s0 hM0 (by decide : 4 < cRd) (by decide : cRd < regs)
    (by decide : nRd ≠ cRd) v0 (by omega) hP0 hstep'
  exact hfin

end Lvm6.X
