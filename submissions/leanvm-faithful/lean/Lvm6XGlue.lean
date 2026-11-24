-- lvm6 EXG (DP6 §2 item 2, the program): the level glue. A mid level's descent starts from the coefficients of
-- `cand hi U` (`Lvm6XGlueRep.candC`): `glueIR` scatters the previous (next-in-the-ladder) level's decoded columns
-- into the interleaved order (`scpIR`, one copy per source column) and copies the high part `hi`; the final level
-- starts from `fpolyE κ ℓ s`, whose coefficients are `s` (`startIR`). Semantics, exact cost, size; the glue is the
-- first part of the level's transition (`trM`, `tr0M`, `trF`), within `trCap` and `trSz`. New.
import Lvm6XGlueCp
import Lvm6XGlueRep
import Lvm6XDescLv

/-!
# The level glue

* **`lanesG κ' ℓ' colB' str' colB str k`**: source column `p < k` (lane `p / 2`, coordinate `p % 2`), its `2^κ'`
  low coefficients to `colB + str·(p % 2) + p / 2 + 2^ℓ'·y` (`scpIR`). **`pairG n src colB str`**: `n` `E2` scalars
  at `src + 2k` to the coordinate rows `colB + k`, `colB + str + k` (two `mcpIR`).
* **`glueIR`** `= lanesG … (2·2^ℓ') ; pairG ℓ hA (colB + 2^κ) str` (`κ = ℓ' + κ'`); **`startIR`** `= pairG (2^κ + ℓ)`.
* **`glueIR_cols`**: from the decoded columns of `Tc` (as `goodB_iff_goodAt` reads them) and `hi` at `hA`, the
  start columns hold `candC κ Tc hi` (both coordinates, `x < 2^κ + ℓ`); the heap outside `[colB, colB + 2 str)` is
  kept. **`startIR_cols`**: the start columns hold `s`.
* Costs (exact): `cost_glueIR = 35 + 26 ℓ + 2·2^ℓ'·(17 + 13·2^κ')`, `cost_startIR = 33 + 26 (2^κ + ℓ)`; sizes
  `sizeIR_glueIR = 63 + 62·2^ℓ'`, `sizeIR_startIR = 61`.
* **`trM`/`tr0M`/`trF`**: glue then X9's transition (`trIR`; level 0 `tr0IR`; the final level `startIR ; trIR`);
  `PartOk … trCap` (`trM_part`, `tr0M_part`, `trF_part`) and `≤ trSz` statements.
-/

set_option autoImplicit false

namespace Lvm6.X

open RecursionFast Lvm.X Lvm.Nb Lvm6.FD Finset Lvm6.Whir LeanVM.Parameters LeanVM.Protocol.Whir

/-! ## The programs -/

/-- Source columns `p < k` scattered into the interleaved start columns. -/
def lanesG (κ' ℓ' colB' str' colB str : ℕ) : ℕ → XIR
  | 0 => .blk []
  | p + 1 => .seq (lanesG κ' ℓ' colB' str' colB str p)
      (scpIR (2 ^ κ') (colB' + str' * p) (2 ^ ℓ') (colB + str * (p % 2) + p / 2))

/-- `n` `E2` scalars at `src + 2k` into the coordinate rows `colB + k` and `colB + str + k`. -/
def pairG (n src colB str : ℕ) : XIR := .seq (mcpIR n src 2 colB) (mcpIR n (src + 1) 2 (colB + str))

/-- **The glue of a mid level**: the previous level's `2·2^ℓ'` decoded columns (from `colB'`, stride `str'`),
interleaved, then the high part `hi` (`ℓ` scalars at `hA`) above `2^κ`, `κ = ℓ' + κ'`. -/
def glueIR (κ' ℓ' ℓ colB' str' hA colB str : ℕ) : XIR :=
  .seq (lanesG κ' ℓ' colB' str' colB str (2 * 2 ^ ℓ')) (pairG ℓ hA (colB + 2 ^ (ℓ' + κ')) str)

/-- **The final level's start**: the `2^κ + ℓ` scalars `s` at `sA`. -/
def startIR (κ ℓ sA colB str : ℕ) : XIR := pairG (2 ^ κ + ℓ) sA colB str

/-! ## Structure, cost, size -/

theorem partOk_seq {P Q : XIR} {a b : ℕ} (hP : PartOk P a) (hQ : PartOk Q b) : PartOk (.seq P Q) (a + b + 1) :=
  ⟨⟨hP.wf, hQ.wf⟩, ⟨hP.noLoopT, hQ.noLoopT⟩, fun t ↦ by simp only [outs, hP.outs, hQ.outs, Nat.add_zero],
    fun t ↦ by have := hP.cost t; have := hQ.cost t; simp only [cost]; omega⟩

theorem lanesG_part (κ' ℓ' colB' str' colB str : ℕ) (hn : 2 ^ κ' < 2 ^ 64) :
    ∀ k, PartOk (lanesG κ' ℓ' colB' str' colB str k) (1 + k * (17 + 13 * 2 ^ κ')) ∧
      ∀ t, cost (lanesG κ' ℓ' colB' str' colB str k) t = 1 + k * (17 + 13 * 2 ^ κ')
  | 0 => ⟨⟨by simp [lanesG, WF], by simp [lanesG, NoLoopT], fun _ ↦ by simp [lanesG, outs],
      fun _ ↦ by simp [lanesG, cost, blkSteps]⟩, fun _ ↦ by simp [lanesG, cost, blkSteps]⟩
  | k + 1 => by
    obtain ⟨ih, ihc⟩ := lanesG_part κ' ℓ' colB' str' colB str hn k
    have hc : ∀ t, cost (lanesG κ' ℓ' colB' str' colB str (k + 1)) t = 1 + (k + 1) * (17 + 13 * 2 ^ κ') := by
      intro t
      simp only [lanesG, cost, ihc t, cost_scpIR _ _ _ _ t hn]
      ring
    exact ⟨⟨⟨ih.wf, wf_scpIR ..⟩, ⟨ih.noLoopT, noLoopT_scpIR ..⟩,
      fun t ↦ by simp only [lanesG, outs, ih.outs, outs_scpIR, Nat.add_zero], fun t ↦ (hc t).le⟩, hc⟩

theorem pairG_cost (n src colB str t : ℕ) (hn : n < 2 ^ 64) : cost (pairG n src colB str) t = 33 + 26 * n := by
  simp only [pairG, cost, cost_mcpIR _ _ _ _ t hn]
  ring

theorem pairG_part (n src colB str : ℕ) (hn : n < 2 ^ 64) : PartOk (pairG n src colB str) (33 + 26 * n) :=
  ⟨⟨wf_mcpIR .., wf_mcpIR ..⟩, ⟨noLoopT_mcpIR .., noLoopT_mcpIR ..⟩,
    fun t ↦ by simp only [pairG, outs, outs_mcpIR, Nat.add_zero], fun t ↦ (pairG_cost n src colB str t hn).le⟩

/-- **The glue's exact cost.** -/
theorem cost_glueIR (κ' ℓ' ℓ colB' str' hA colB str t : ℕ) (hn : 2 ^ κ' < 2 ^ 64) (hℓ : ℓ < 2 ^ 64) :
    cost (glueIR κ' ℓ' ℓ colB' str' hA colB str) t = 35 + 26 * ℓ + 2 * 2 ^ ℓ' * (17 + 13 * 2 ^ κ') := by
  simp only [glueIR, cost, (lanesG_part κ' ℓ' colB' str' colB str hn _).2 t, pairG_cost _ _ _ _ t hℓ]
  ring

theorem glueIR_part (κ' ℓ' ℓ colB' str' hA colB str : ℕ) (hn : 2 ^ κ' < 2 ^ 64) (hℓ : ℓ < 2 ^ 64) :
    PartOk (glueIR κ' ℓ' ℓ colB' str' hA colB str) (35 + 26 * ℓ + 2 * 2 ^ ℓ' * (17 + 13 * 2 ^ κ')) := by
  have h := partOk_seq ((lanesG_part κ' ℓ' colB' str' colB str hn (2 * 2 ^ ℓ')).1)
    (pairG_part ℓ hA (colB + 2 ^ (ℓ' + κ')) str hℓ)
  refine ⟨h.wf, h.noLoopT, h.outs, fun t ↦ (cost_glueIR κ' ℓ' ℓ colB' str' hA colB str t hn hℓ).le⟩

/-- **The final start's exact cost.** -/
theorem cost_startIR (κ ℓ sA colB str t : ℕ) (hn : 2 ^ κ + ℓ < 2 ^ 64) :
    cost (startIR κ ℓ sA colB str) t = 33 + 26 * (2 ^ κ + ℓ) := pairG_cost _ _ _ _ t hn

theorem sizeIR_lanesG (κ' ℓ' colB' str' colB str : ℕ) :
    ∀ k, sizeIR (lanesG κ' ℓ' colB' str' colB str k) = 1 + 31 * k
  | 0 => by simp [lanesG, sizeIR, blkSteps]
  | k + 1 => by
    simp only [lanesG, sizeIR, sizeIR_lanesG κ' ℓ' colB' str' colB str k, sizeIR_scpIR]
    ring

theorem sizeIR_pairG (n src colB str : ℕ) : sizeIR (pairG n src colB str) = 61 := rfl

theorem sizeIR_glueIR (κ' ℓ' ℓ colB' str' hA colB str : ℕ) :
    sizeIR (glueIR κ' ℓ' ℓ colB' str' hA colB str) = 63 + 62 * 2 ^ ℓ' := by
  simp only [glueIR, sizeIR, sizeIR_lanesG, sizeIR_pairG]
  ring

theorem sizeIR_startIR (κ ℓ sA colB str : ℕ) : sizeIR (startIR κ ℓ sA colB str) = 61 := rfl

/-! ## Semantics -/

theorem hasOut_scpIR (n src str dst : ℕ) : hasOut (scpIR n src str dst) = false := rfl

/-- Two interleaved target cells of distinct source columns differ. -/
theorem cellG_ne {S n str p p' y y' : ℕ} (hp : p < 2 * S) (hp' : p' < 2 * S) (hy : y < n) (hy' : y' < n)
    (hstr : S * n ≤ str) (hne : p ≠ p') :
    str * (p % 2) + p / 2 + S * y ≠ str * (p' % 2) + p' / 2 + S * y' := by
  intro h
  have b1 : S * y + S ≤ S * n := by
    have := Nat.mul_le_mul_left S (show y + 1 ≤ n by omega); rwa [Nat.mul_succ] at this
  have b2 : S * y' + S ≤ S * n := by
    have := Nat.mul_le_mul_left S (show y' + 1 ≤ n by omega); rwa [Nat.mul_succ] at this
  rcases Nat.mod_two_eq_zero_or_one p with h1 | h1 <;> rcases Nat.mod_two_eq_zero_or_one p' with h2 | h2 <;>
    rw [h1, h2] at h <;> simp only [Nat.mul_zero, Nat.mul_one, Nat.zero_add] at h
  · have e := congrArg (· % S) h
    simp only [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt (show p / 2 < S by omega),
      Nat.mod_eq_of_lt (show p' / 2 < S by omega)] at e
    omega
  · omega
  · omega
  · have e := congrArg (· % S) (show p / 2 + S * y = p' / 2 + S * y' by omega)
    simp only [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt (show p / 2 < S by omega),
      Nat.mod_eq_of_lt (show p' / 2 < S by omega)] at e
    omega

/-- A target cell lies in the start columns' two rows. -/
theorem cellG_lt {S n str p y : ℕ} (hp : p < 2 * S) (hy : y < n) (hstr : S * n ≤ str) :
    str * (p % 2) + p / 2 + S * y < 2 * str := by
  have b1 : S * y + S ≤ S * n := by
    have := Nat.mul_le_mul_left S (show y + 1 ≤ n by omega); rwa [Nat.mul_succ] at this
  rcases Nat.mod_two_eq_zero_or_one p with h1 | h1 <;> rw [h1] <;> omega

/-- A source cell lies in the source columns. -/
theorem srcG_lt {str' p y n P : ℕ} (hp : p < P) (hy : y < n) (hn : n ≤ str') : str' * p + y < str' * P := by
  have := Nat.mul_le_mul_left str' (show p + 1 ≤ P by omega); rw [Nat.mul_succ] at this; omega

/-- **The scattered lanes**: source column `p < k` is at `colB + str·(p % 2) + p / 2 + S·y`, `y < 2^κ'`; the heap
outside the two target rows is kept. -/
theorem lanesG_sem (I : Array Word) {κ' ℓ' colB' str' colB str : ℕ}
    (hC : regs ≤ colB) (hC' : regs ≤ colB') (hstr : 2 ^ ℓ' * 2 ^ κ' ≤ str) (hstr' : 2 ^ κ' ≤ str')
    (h64 : colB + 3 * str < 2 ^ 64) (h64' : colB' + str' * (2 * 2 ^ ℓ') < 2 ^ 64)
    (hdis : colB + 2 * str ≤ colB' ∨ colB' + str' * (2 * 2 ^ ℓ') ≤ colB) :
    ∀ k ≤ 2 * 2 ^ ℓ', ∀ s : St, Inv s.M → colB + 2 * str ≤ s.M.size →
      let s' := semXIR I (lanesG κ' ℓ' colB' str' colB str k) s
      (∀ p < k, ∀ y < 2 ^ κ', rd s'.M (colB + str * (p % 2) + p / 2 + 2 ^ ℓ' * y) = rd s.M (colB' + str' * p + y)) ∧
      (∀ x, regs ≤ x → (∀ p < k, ∀ y < 2 ^ κ', x ≠ colB + str * (p % 2) + p / 2 + 2 ^ ℓ' * y) →
        rd s'.M x = rd s.M x) ∧ Inv s'.M ∧ s'.o = s.o
  | 0, _, s, hM, _ => by
    have e : semXIR I (lanesG κ' ℓ' colB' str' colB str 0) s = s := by simp [lanesG, semXIR, runPrims]
    exact ⟨fun _ h ↦ absurd h (Nat.not_lt_zero _), fun _ _ _ ↦ by rw [e], by rw [e]; exact hM, by rw [e]⟩
  | k + 1, hk, s, hM, hsz => by
    obtain ⟨a1, a2, a3, a4⟩ := lanesG_sem I hC hC' hstr hstr' h64 h64' hdis k (by omega) s hM hsz
    have z1 := size_sem I (lanesG κ' ℓ' colB' str' colB str k) s
    intro s'
    simp only [s', lanesG, semXIR_seq]
    generalize semXIR I (lanesG κ' ℓ' colB' str' colB str k) s = s1 at a1 a2 a3 a4 z1
    have hS : 0 < 2 ^ ℓ' := Nat.two_pow_pos ℓ'
    have hsl := srcG_lt (p := k) (P := 2 * 2 ^ ℓ') (y := 2 ^ κ' - 1) (by omega)
      (by have := Nat.two_pow_pos κ'; omega) hstr'
    have hκ0 := Nat.two_pow_pos κ'
    have hSn : 2 ^ ℓ' ≤ 2 ^ ℓ' * 2 ^ κ' := Nat.le_mul_of_pos_right _ hκ0
    have htg : ∀ y < 2 ^ κ', str * (k % 2) + k / 2 + 2 ^ ℓ' * y < 2 * str := fun y hy ↦
      cellG_lt (by omega) hy hstr
    obtain ⟨b1, b2, b3⟩ := scpIR_sem I s1 a3 (n := 2 ^ κ') (src := colB' + str' * k) (str := 2 ^ ℓ')
      (dst := colB + str * (k % 2) + k / 2) hS (by omega) (by omega) (by omega) (by omega)
      (by
        have h1 : 2 ^ ℓ' * 2 ^ κ' ≤ str := hstr
        rcases Nat.mod_two_eq_zero_or_one k with h2 | h2 <;> rw [h2] <;> omega)
      (fun i hi ↦ by have := htg i hi; rw [z1]; omega)
      (fun i hi i' hi' ↦ by
        have h1 := srcG_lt (p := k) (P := 2 * 2 ^ ℓ') (y := i) (by omega) hi hstr'
        have h2 := htg i' hi'
        omega)
    have c4 := sem_o I (scpIR (2 ^ κ') (colB' + str' * k) (2 ^ ℓ') (colB + str * (k % 2) + k / 2)) s1
      (hasOut_scpIR _ _ _ _)
    refine ⟨fun p hp y hy ↦ ?_, fun x hx hx' ↦ ?_, b3, c4.trans a4⟩
    · rcases Nat.lt_succ_iff_lt_or_eq.1 hp with hp | rfl
      · rw [b2 _ (by simp only [regs] at hC ⊢; omega) (fun i hi ↦ by
          have := cellG_ne (S := 2 ^ ℓ') (str := str) (p := p) (p' := k) (y := y) (y' := i) (by omega) (by omega)
            hy hi hstr (by omega)
          omega), a1 p hp y hy]
      · rw [show colB + str * (p % 2) + p / 2 + 2 ^ ℓ' * y = colB + str * (p % 2) + p / 2 + 2 ^ ℓ' * y from rfl,
          b1 y hy]
        have h1 := srcG_lt (p := p) (P := 2 * 2 ^ ℓ') (y := y) (by omega) hy hstr'
        exact a2 _ (by simp only [regs] at hC' ⊢; omega) fun p' _ y' hy' ↦ by
          have := htg y' hy'; have := cellG_lt (S := 2 ^ ℓ') (p := p') (by omega) hy' hstr; omega
    · rw [b2 x hx (fun i hi ↦ hx' k (by omega) i hi), a2 x hx fun p hp y hy ↦ hx' p (by omega) y hy]

/-- **The pairs**: `n` scalars at `src + 2k` into the rows `colB + k`, `colB + str + k`. -/
theorem pairG_sem (I : Array Word) (s : St) (hM : Inv s.M) {n src colB str : ℕ} (hC : regs ≤ colB)
    (hsrc : regs ≤ src) (hn : n ≤ str) (h64 : colB + str + n < 2 ^ 64) (h64s : src + 2 * n + 1 < 2 ^ 64)
    (hsz : colB + str + n ≤ s.M.size) (hdis : colB + str + n ≤ src ∨ src + 2 * n + 1 ≤ colB) :
    let s' := semXIR I (pairG n src colB str) s
    (∀ k < n, rd s'.M (colB + k) = rd s.M (src + 2 * k) ∧ rd s'.M (colB + str + k) = rd s.M (src + 1 + 2 * k)) ∧
      (∀ x, regs ≤ x → (x < colB ∨ colB + n ≤ x) → (x < colB + str ∨ colB + str + n ≤ x) → rd s'.M x = rd s.M x) ∧
      Inv s'.M ∧ s'.o = s.o := by
  intro s'
  simp only [regs] at hC hsrc
  simp only [s', pairG, semXIR_seq]
  obtain ⟨a1, a2, a3⟩ := mcpIR_sem I s hM (n := n) (src := src) (str := 2) (dst := colB) (by omega) (by omega)
    (by norm_num) (by simp only [regs]; omega) (by omega) (by omega) (fun i hi ↦ by omega)
    (fun i hi ↦ by simp only [regs]; omega)
  have z1 := size_sem I (mcpIR n src 2 colB) s
  have o1 := sem_o I (mcpIR n src 2 colB) s (hasOut_mcpIR _ _ _ _)
  generalize semXIR I (mcpIR n src 2 colB) s = s1 at a1 a2 a3 z1 o1
  obtain ⟨b1, b2, b3⟩ := mcpIR_sem I s1 a3 (n := n) (src := src + 1) (str := 2) (dst := colB + str) (by omega)
    (by omega) (by norm_num) (by simp only [regs]; omega) (by omega) (by omega) (fun i hi ↦ by omega)
    (fun i hi ↦ by simp only [regs]; omega)
  have o2 := sem_o I (mcpIR n (src + 1) 2 (colB + str)) s1 (hasOut_mcpIR _ _ _ _)
  refine ⟨fun k hk ↦ ⟨?_, ?_⟩, fun x hx h1 h2 ↦ ?_, b3, o2.trans o1⟩
  · rw [b2 _ (by simp only [regs]; omega) (by omega), a1 k hk]
  · rw [b1 k hk, a2 _ (by simp only [regs]; omega) (by omega)]
  · rw [b2 x hx h2, a2 x hx h1]

theorem bitsToNat_fin0 (u : Fin 0 → Bool) : bitsToNat u = 0 := by simp [bitsToNat]

theorem coord_rdE2 (M : Mem) (a : ℕ) (i : Fin 2) : basisE2.coord i (rdE2 M a) = rdK M (a + i) := by
  match i with
  | 0 => show basisE2.coord 0 (rdE2 M a) = rdK M (a + 0); rw [coord0_E2]; rfl
  | 1 => show basisE2.coord 1 (rdE2 M a) = rdK M (a + 1); rw [coord1_E2]; rfl

/-- **The glue on the machine**: from the previous level's decoded columns (lane `u`, coordinate `i` at
`colB' + str'·(2⟨u⟩ + i)`, as `goodB_iff_goodAt` reads them) and the high part at `hA`, the start columns hold
`candC κ Tc hi`; the heap outside `[colB, colB + 2 str)` is kept. -/
theorem glueIR_cols (I : Array Word) (s : St) (hM : Inv s.M) {κ' ℓ' ℓ colB' str' hA colB str : ℕ}
    (hC : regs ≤ colB) (hC' : regs ≤ colB') (hA0 : regs ≤ hA) (hstr : 2 ^ (ℓ' + κ') + ℓ ≤ str)
    (hstr' : 2 ^ κ' ≤ str') (h64 : colB + 3 * str < 2 ^ 64) (h64' : colB' + str' * (2 * 2 ^ ℓ') < 2 ^ 64)
    (h64A : hA + 2 * ℓ + 1 < 2 ^ 64) (hsz : colB + 2 * str ≤ s.M.size)
    (hdis : colB + 2 * str ≤ colB' ∨ colB' + str' * (2 * 2 ^ ℓ') ≤ colB)
    (hdisA : colB + 2 * str ≤ hA ∨ hA + 2 * ℓ + 1 ≤ colB)
    {Tc : CT E2 ℓ'} {hi : List E2}
    (hsrc : ∀ (u : Fin ℓ' → Bool) (i : Fin 2), ∀ y < 2 ^ κ',
      rdK s.M (colB' + str' * (2 * bitsToNat u + i) + y) = basisE2.coord i (Tc u y))
    (hhi : ∀ k < ℓ, rdE2 s.M (hA + 2 * k) = hi.getD k 0) :
    let s' := semXIR I (glueIR κ' ℓ' ℓ colB' str' hA colB str) s
    (∀ (u : Fin 0 → Bool) (i : Fin 2), ∀ x < 2 ^ (ℓ' + κ') + ℓ,
      rdK s'.M (colB + str * (2 * bitsToNat u + i) + x) = basisE2.coord i (candC (ℓ' + κ') Tc hi u x)) ∧
      (∀ x, regs ≤ x → (x < colB ∨ colB + 2 * str ≤ x) → rd s'.M x = rd s.M x) ∧ Inv s'.M ∧ s'.o = s.o := by
  intro s'
  have hSn : 2 ^ (ℓ' + κ') = 2 ^ ℓ' * 2 ^ κ' := pow_add 2 ℓ' κ'
  obtain ⟨a1, a2, a3, a4⟩ := lanesG_sem I hC hC' (by omega) hstr' h64 h64' hdis (2 * 2 ^ ℓ') le_rfl s hM hsz
  have z1 := size_sem I (lanesG κ' ℓ' colB' str' colB str (2 * 2 ^ ℓ')) s
  have a2' : ∀ x, regs ≤ x → (x < colB ∨ colB + 2 * str ≤ x) →
      rd (semXIR I (lanesG κ' ℓ' colB' str' colB str (2 * 2 ^ ℓ')) s).M x = rd s.M x := fun x hx hx' ↦
    a2 x hx fun p hp y hy ↦ by have := cellG_lt (S := 2 ^ ℓ') hp hy (str := str) (by omega); omega
  simp only [s', glueIR, semXIR_seq]
  generalize semXIR I (lanesG κ' ℓ' colB' str' colB str (2 * 2 ^ ℓ')) s = s1 at a1 a2 a2' a3 a4 z1
  obtain ⟨b1, b2, b3, b4⟩ := pairG_sem I s1 a3 (n := ℓ) (src := hA) (colB := colB + 2 ^ (ℓ' + κ')) (str := str)
    (by simp only [regs] at hC ⊢; omega) hA0 (by omega) (by omega) (by omega) (by rw [z1]; omega) (by omega)
  refine ⟨fun u i x hx ↦ ?_, fun x hx hx' ↦ ?_, b3, b4.trans a4⟩
  · rw [bitsToNat_fin0, Nat.mul_zero, Nat.zero_add]
    have hi2 : (i : ℕ) < 2 := i.isLt
    by_cases hxk : x < 2 ^ (ℓ' + κ')
    · -- an interleaved coefficient
      have hcand : candC (ℓ' + κ') Tc hi u x = Tc (laneOf ℓ' x) (x / 2 ^ ℓ') := by simp only [candC, hxk, ↓reduceIte]
      have hy : x / 2 ^ ℓ' < 2 ^ κ' := (Nat.div_lt_iff_lt_mul (Nat.two_pow_pos ℓ')).2 (by rw [Nat.mul_comm]; omega)
      have hL : x % 2 ^ ℓ' < 2 ^ ℓ' := Nat.mod_lt _ (Nat.two_pow_pos ℓ')
      have hdm := Nat.mod_add_div x (2 ^ ℓ')
      have hp := a1 (2 * (x % 2 ^ ℓ') + i) (by omega) (x / 2 ^ ℓ') hy
      have e1 : (2 * (x % 2 ^ ℓ') + (i : ℕ)) % 2 = i := by omega
      have e2 : (2 * (x % 2 ^ ℓ') + (i : ℕ)) / 2 = x % 2 ^ ℓ' := by omega
      rw [e1, e2] at hp
      have hcell : colB + str * (i : ℕ) + x = colB + str * (i : ℕ) + x % 2 ^ ℓ' + 2 ^ ℓ' * (x / 2 ^ ℓ') := by omega
      have hstrx : str * (i : ℕ) + x < 2 * str := by
        rcases (show (i : ℕ) = 0 ∨ (i : ℕ) = 1 by omega) with h | h <;> rw [h] <;> omega
      rw [hcand, ← hsrc (laneOf ℓ' x) i _ hy, bitsToNat_laneOf, rdK, rdK, b2 _ (by simp only [regs] at hC ⊢; omega)
        (by rcases (show (i : ℕ) = 0 ∨ (i : ℕ) = 1 by omega) with h | h <;> rw [h] <;> omega)
        (by rcases (show (i : ℕ) = 0 ∨ (i : ℕ) = 1 by omega) with h | h <;> rw [h] <;> omega), hcell, hp]
    · -- the high part
      have hcand : candC (ℓ' + κ') Tc hi u x = hi.getD (x - 2 ^ (ℓ' + κ')) 0 := by
        simp only [candC, hxk, ↓reduceIte]
      have hk : x - 2 ^ (ℓ' + κ') < ℓ := by omega
      obtain ⟨c1, c2⟩ := b1 (x - 2 ^ (ℓ' + κ')) hk
      rw [hcand, ← hhi _ hk, coord_rdE2]
      rcases (show (i : ℕ) = 0 ∨ (i : ℕ) = 1 by omega) with h | h
      · rw [h, Nat.mul_zero, Nat.add_zero, Nat.add_zero]
        rw [rdK, rdK, show colB + x = colB + 2 ^ (ℓ' + κ') + (x - 2 ^ (ℓ' + κ')) by omega, c1]
        exact congrArg wK (a2' _ (by simp only [regs] at hA0 ⊢; omega) (by omega))
      · rw [h, Nat.mul_one]
        rw [rdK, rdK, show colB + str + x = colB + 2 ^ (ℓ' + κ') + str + (x - 2 ^ (ℓ' + κ')) by omega, c2,
          show hA + 1 + 2 * (x - 2 ^ (ℓ' + κ')) = hA + 2 * (x - 2 ^ (ℓ' + κ')) + 1 by omega]
        exact congrArg wK (a2' _ (by simp only [regs] at hA0 ⊢; omega) (by omega))
  · rw [b2 x hx (by omega) (by omega), a2' x hx hx']

/-- **The final start on the machine**: the start columns hold `s` (`2^κ + ℓ` scalars at `sA`). -/
theorem startIR_cols (I : Array Word) (st : St) (hM : Inv st.M) {κ ℓ sA colB str : ℕ} (hC : regs ≤ colB)
    (hsA : regs ≤ sA) (hstr : 2 ^ κ + ℓ ≤ str) (h64 : colB + 3 * str < 2 ^ 64)
    (h64A : sA + 2 * (2 ^ κ + ℓ) + 1 < 2 ^ 64) (hsz : colB + 2 * str ≤ st.M.size)
    (hdisA : colB + 2 * str ≤ sA ∨ sA + 2 * (2 ^ κ + ℓ) + 1 ≤ colB) {s : List E2}
    (hs : ∀ k < 2 ^ κ + ℓ, rdE2 st.M (sA + 2 * k) = s.getD k 0) :
    let st' := semXIR I (startIR κ ℓ sA colB str) st
    (∀ (u : Fin 0 → Bool) (i : Fin 2), ∀ x < 2 ^ κ + ℓ,
      rdK st'.M (colB + str * (2 * bitsToNat u + i) + x) = basisE2.coord i (s.getD x 0)) ∧
      (∀ x, regs ≤ x → (x < colB ∨ colB + 2 * str ≤ x) → rd st'.M x = rd st.M x) ∧ Inv st'.M ∧ st'.o = st.o := by
  intro st'
  obtain ⟨b1, b2, b3, b4⟩ := pairG_sem I st hM (n := 2 ^ κ + ℓ) (src := sA) (colB := colB) (str := str) hC hsA
    hstr (by omega) (by omega) (by omega) (by omega)
  refine ⟨fun u i x hx ↦ ?_, fun x hx hx' ↦ b2 x hx (by omega) (by omega), b3, b4⟩
  rw [bitsToNat_fin0, Nat.mul_zero, Nat.zero_add, ← hs x hx, coord_rdE2]
  obtain ⟨c1, c2⟩ := b1 x hx
  have hi2 : (i : ℕ) < 2 := i.isLt
  rcases (show (i : ℕ) = 0 ∨ (i : ℕ) = 1 by omega) with h | h
  · rw [h, Nat.mul_zero, Nat.add_zero, Nat.add_zero, rdK, rdK]
    exact congrArg wK c1
  · rw [h, Nat.mul_one, rdK, rdK, show sA + 2 * x + 1 = sA + 1 + 2 * x by omega]
    exact congrArg wK c2

/-! ## The transitions with the glue -/

/-- X9's transition within `2^37` (`h + (m + j) ≤ 27`, `j ≤ 6`). -/
theorem trIR_part37 (h m j : ℕ) (bf ch : ℕ → ℕ) (tb tS : ℕ) (hc : h + (m + j) ≤ 27) (hj : j ≤ 6) :
    PartOk (trIR h m j bf ch tb tS) (2 ^ 37) := by
  obtain ⟨w, n, o, -⟩ := trIR_part h m j bf ch tb tS hc hj
  refine ⟨w, n, o, fun t ↦ ?_⟩
  have c1 := cost_foldsIR_le h t m j bf ch (by omega)
  have c2 := (part_tabsIR j m tb tS bf t j).2.2.2
  have hp : 2 ^ (h + (m + j)) ≤ 2 ^ 27 := Nat.pow_le_pow_right (by norm_num) hc
  have := Nat.mul_le_mul hj (show 43 + 152 * 2 ^ (h + (m + j)) ≤ 43 + 152 * 2 ^ 27 by omega)
  simp only [trIR, cost]
  have e : (2 : ℕ) ^ 37 = 137438953472 := by norm_num
  have e' : (2 : ℕ) ^ 27 = 134217728 := by norm_num
  rw [e]; rw [e'] at this
  omega

/-- Level 0's transition within `2^37`. -/
theorem tr0IR_part37 (h base : ℕ) (bf ch : ℕ → ℕ) (tb tS : ℕ) (hh : h ≤ 21) :
    PartOk (tr0IR h base bf ch tb tS) (2 ^ 37) := by
  obtain ⟨w, n, o, -⟩ := tr0IR_part h base bf ch tb tS hh
  refine ⟨w, n, o, fun t ↦ ?_⟩
  have hp : 2 ^ h ≤ 2 ^ 21 := Nat.pow_le_pow_right (by norm_num) hh
  have hp' : 2 ^ (h + (0 + 6)) ≤ 2 ^ 27 := Nat.pow_le_pow_right (by norm_num) (by omega)
  have e1 := cost_expIR h base (bf 0) t (by
    have : (128 : ℕ) * 2 ^ 21 < 2 ^ 64 := by norm_num
    omega)
  have c1 := cost_foldsIR_le h t 0 6 bf ch (by omega)
  have c2 := (part_tabsIR 6 0 tb tS bf t 6).2.2.2
  simp only [tr0IR, trIR, cost]
  have e : (2 : ℕ) ^ 37 = 137438953472 := by norm_num
  have e' : (2 : ℕ) ^ 27 = 134217728 := by norm_num
  have e'' : (2 : ℕ) ^ 21 = 2097152 := by norm_num
  rw [e]; rw [e'] at hp'; rw [e''] at hp
  omega

/-- **A mid level's transition** (levels 1–3): the glue, then X9's `trIR`. -/
def trM (κ' ℓ' ℓ colB' str' hA colB str h : ℕ) (bf ch : ℕ → ℕ) (tb tS : ℕ) : XIR :=
  .seq (glueIR κ' ℓ' ℓ colB' str' hA colB str) (trIR h 0 ℓ bf ch tb tS)

/-- **Level 0's transition**: the glue, then `tr0IR`. -/
def tr0M (κ' ℓ' colB' str' hA colB str h base : ℕ) (bf ch : ℕ → ℕ) (tb tS : ℕ) : XIR :=
  .seq (glueIR κ' ℓ' 6 colB' str' hA colB str) (tr0IR h base bf ch tb tS)

/-- **The final level's transition**: the start `s`, then `trIR`. -/
def trF (κ ℓ sA colB str h : ℕ) (bf ch : ℕ → ℕ) (tb tS : ℕ) : XIR :=
  .seq (startIR κ ℓ sA colB str) (trIR h 0 ℓ bf ch tb tS)

theorem trM_part (κ' ℓ' ℓ colB' str' hA colB str h : ℕ) (bf ch : ℕ → ℕ) (tb tS : ℕ) (hκ : κ' ≤ 20)
    (hℓ' : ℓ' ≤ 6) (hℓ : ℓ ≤ 6) (hc : h + ℓ ≤ 27) : PartOk (trM κ' ℓ' ℓ colB' str' hA colB str h bf ch tb tS) trCap := by
  have hn : 2 ^ κ' ≤ 2 ^ 20 := Nat.pow_le_pow_right (by norm_num) hκ
  have hS : 2 ^ ℓ' ≤ 2 ^ 6 := Nat.pow_le_pow_right (by norm_num) hℓ'
  have h1 := partOk_seq (glueIR_part κ' ℓ' ℓ colB' str' hA colB str (by omega) (by omega))
    (trIR_part37 h 0 ℓ bf ch tb tS (by omega) hℓ)
  refine ⟨h1.wf, h1.noLoopT, h1.outs, fun t ↦ (h1.cost t).trans ?_⟩
  have := Nat.mul_le_mul (Nat.mul_le_mul_left 2 hS) (show 17 + 13 * 2 ^ κ' ≤ 17 + 13 * 2 ^ 20 by omega)
  simp only [trCap]
  norm_num at this ⊢
  omega

theorem tr0M_part (κ' ℓ' colB' str' hA colB str h base : ℕ) (bf ch : ℕ → ℕ) (tb tS : ℕ) (hκ : κ' ≤ 20)
    (hℓ' : ℓ' ≤ 6) (hh : h ≤ 21) : PartOk (tr0M κ' ℓ' colB' str' hA colB str h base bf ch tb tS) trCap := by
  have hn : 2 ^ κ' ≤ 2 ^ 20 := Nat.pow_le_pow_right (by norm_num) hκ
  have hS : 2 ^ ℓ' ≤ 2 ^ 6 := Nat.pow_le_pow_right (by norm_num) hℓ'
  have h1 := partOk_seq (glueIR_part κ' ℓ' 6 colB' str' hA colB str (by omega) (by norm_num))
    (tr0IR_part37 h base bf ch tb tS hh)
  refine ⟨h1.wf, h1.noLoopT, h1.outs, fun t ↦ (h1.cost t).trans ?_⟩
  have := Nat.mul_le_mul (Nat.mul_le_mul_left 2 hS) (show 17 + 13 * 2 ^ κ' ≤ 17 + 13 * 2 ^ 20 by omega)
  simp only [trCap]
  norm_num at this ⊢
  omega

theorem trF_part (κ ℓ sA colB str h : ℕ) (bf ch : ℕ → ℕ) (tb tS : ℕ) (hκ : κ ≤ 20) (hℓ : ℓ ≤ 6)
    (hc : h + ℓ ≤ 27) : PartOk (trF κ ℓ sA colB str h bf ch tb tS) trCap := by
  have hn : 2 ^ κ ≤ 2 ^ 20 := Nat.pow_le_pow_right (by norm_num) hκ
  have h1 := partOk_seq (pairG_part (2 ^ κ + ℓ) sA colB str (by omega))
    (trIR_part37 h 0 ℓ bf ch tb tS (by omega) hℓ)
  refine ⟨h1.wf, h1.noLoopT, h1.outs, fun t ↦ (h1.cost t).trans ?_⟩
  simp only [trCap]
  norm_num at hn ⊢
  omega

theorem sizeIR_trM_le (κ' ℓ' ℓ colB' str' hA colB str h : ℕ) (bf ch : ℕ → ℕ) (tb tS : ℕ) (hℓ' : ℓ' ≤ 6)
    (hℓ : ℓ ≤ 6) : sizeIR (trM κ' ℓ' ℓ colB' str' hA colB str h bf ch tb tS) ≤ trSz := by
  have hS : 2 ^ ℓ' ≤ 2 ^ 6 := Nat.pow_le_pow_right (by norm_num) hℓ'
  simp only [trM, sizeIR, sizeIR_glueIR, trIR, sizeIR_foldsIR, sizeIR_tabsIR, trSz]
  norm_num at hS ⊢
  omega

theorem sizeIR_tr0M_le (κ' ℓ' colB' str' hA colB str h base : ℕ) (bf ch : ℕ → ℕ) (tb tS : ℕ) (hℓ' : ℓ' ≤ 6) :
    sizeIR (tr0M κ' ℓ' colB' str' hA colB str h base bf ch tb tS) ≤ trSz := by
  have hS : 2 ^ ℓ' ≤ 2 ^ 6 := Nat.pow_le_pow_right (by norm_num) hℓ'
  simp only [tr0M, tr0IR, sizeIR, sizeIR_glueIR, sizeIR_expIR, trIR, sizeIR_foldsIR, sizeIR_tabsIR, trSz]
  norm_num at hS ⊢
  omega

theorem sizeIR_trF_le (κ ℓ sA colB str h : ℕ) (bf ch : ℕ → ℕ) (tb tS : ℕ) (hℓ : ℓ ≤ 6) :
    sizeIR (trF κ ℓ sA colB str h bf ch tb tS) ≤ trSz := by
  simp only [trF, sizeIR, sizeIR_startIR, trIR, sizeIR_foldsIR, sizeIR_tabsIR, trSz]
  norm_num
  omega

end Lvm6.X
