-- lvm6 EXF phase 2 (F-EXG-2): the fill block's generic parts. The copy program `cpsIR` (one word a copy, from the heap
-- or from the tape), its semantics, cost and size; the run lemmas of W1's pieces (reads, rounds, the tail's high parts)
-- that say which event of a returning run each value is. New.
import Lvm6XFront6
import Lvm6WhirFollow

/-!
# Word copies and the opening's runs

* **`cp1IR (b, src, dst)`**: `M[dst] := M[src]` (`b`) or tape word `src`; **`cpsIR tab`** the copies in order.
  **`cpsIR_sem`**: for copies whose destinations are distinct and lie in `[lo, hi)`, above every heap source,
  `M'[dst] = cpV I M e` for each copy, every other cell `≥ regs` kept, `Inv`, no output, same size.
* **`readF_run`**, **`readFs_run`**, **`roundP_run`**, **`roundsP_run`**, **`tailP_hi`**: the values of W1's returning
  runs are `e2OfE` of their events at fixed indices (round `k`'s `α`, `β`: events `7k + 5`, `7k + 6`; a tail's high
  part `k`: event `k`).
-/

set_option autoImplicit false

namespace Lvm6.X

open RecursionFast Lvm Lvm.X Lvm.FS Lvm6.Whir
open LeanVM.Protocol.Compile (Ev VerifierProgram)
open LeanVM.Parameters (E E2 e2OfE)

/-! ## The copies -/

/-- One copy: `M[dst] :=` `M[src]` if `b`, else tape word `src`. -/
def cp1IR (e : Bool × ℕ × ℕ) : XIR :=
  .seq (.blk [.const rAd4 (toWord e.2.1)]) (.seq (if e.1 then .load rKd rAd4 else .input rKd rAd4)
    (.seq (.blk [.const rAd4 (toWord e.2.2)]) (.store rAd4 rKd)))

/-- The copies in order. -/
def cpsIR : List (Bool × ℕ × ℕ) → XIR
  | [] => .blk []
  | e :: es => .seq (cp1IR e) (cpsIR es)

/-- The value a copy writes. -/
def cpV (I : Array Word) (M : Mem) (e : Bool × ℕ × ℕ) : Word := if e.1 then rd M e.2.1 else I.getD e.2.1 0

/-- A copy's static facts: the destination in `[lo, hi)`, the heap source in `[regs, lo)`. -/
def cpOK (lo hi : ℕ) (e : Bool × ℕ × ℕ) : Bool :=
  decide (regs ≤ lo) && decide (lo ≤ e.2.2) && decide (e.2.2 < hi) && decide (hi ≤ 2 ^ 64) &&
    decide (e.2.1 < 2 ^ 64) && (!e.1 || (decide (regs ≤ e.2.1) && decide (e.2.1 < lo)))

theorem wf_cp1IR (e : Bool × ℕ × ℕ) : WF (cp1IR e) := by
  rcases e with ⟨b, src, dst⟩
  cases b <;> simp +decide [cp1IR, WF, Prim.dst, rAd4, rKd, cTmp]

theorem wf_cpsIR : ∀ tab, WF (cpsIR tab)
  | [] => by simp [cpsIR, WF]
  | e :: es => ⟨wf_cp1IR e, wf_cpsIR es⟩

theorem noLoopT_cpsIR : ∀ tab, NoLoopT (cpsIR tab)
  | [] => trivial
  | e :: es => ⟨by rcases e with ⟨b, _, _⟩; cases b <;> simp [cp1IR, NoLoopT], noLoopT_cpsIR es⟩

theorem hasOut_cpsIR : ∀ tab, hasOut (cpsIR tab) = false
  | [] => rfl
  | e :: es => by
    rcases e with ⟨b, _, _⟩
    cases b <;> simp [cpsIR, cp1IR, hasOut, hasOut_cpsIR es]

theorem outs_cpsIR (t : ℕ) : ∀ tab, outs (cpsIR tab) t = 0
  | [] => rfl
  | e :: es => by
    rcases e with ⟨b, _, _⟩
    cases b <;> simp [cpsIR, cp1IR, outs, outs_cpsIR t es]

theorem cost_cp1IR (e : Bool × ℕ × ℕ) (t : ℕ) : cost (cp1IR e) t = cost (cp1IR (false, 0, 0)) 0 := by
  rcases e with ⟨b, _, _⟩; cases b <;> rfl

theorem sizeIR_cp1IR (e : Bool × ℕ × ℕ) : sizeIR (cp1IR e) = sizeIR (cp1IR (false, 0, 0)) := by
  rcases e with ⟨b, _, _⟩; cases b <;> rfl

theorem cp1_consts : cost (cp1IR (false, 0, 0)) 0 ≤ 20 ∧ sizeIR (cp1IR (false, 0, 0)) ≤ 20 ∧
    cost (XIR.blk []) 0 ≤ 4 ∧ sizeIR (XIR.blk []) ≤ 4 := by
  decide

/-- **The copies' cost**: at most `21` steps a copy, plus `4`. -/
theorem cost_cpsIR (t : ℕ) : ∀ tab, cost (cpsIR tab) t ≤ 21 * tab.length + 4
  | [] => cp1_consts.2.2.1
  | e :: es => by
    have h1 := cost_cpsIR t es
    have h2 := cp1_consts.1
    simp only [cpsIR, cost, cost_cp1IR, List.length_cons]
    omega

/-- **The copies' size**: at most `21` statements a copy, plus `4`. -/
theorem sizeIR_cpsIR : ∀ tab, sizeIR (cpsIR tab) ≤ 21 * tab.length + 4
  | [] => cp1_consts.2.2.2
  | e :: es => by
    have h1 := sizeIR_cpsIR es
    have h2 := cp1_consts.2.1
    simp only [cpsIR, sizeIR, sizeIR_cp1IR, List.length_cons]
    omega

/-- **One copy**: the destination gets `cpV`, every other cell `≥ regs` is kept. -/
theorem cp1IR_sem (I : Array Word) (s : St) (hM : Inv s.M) (e : Bool × ℕ × ℕ) (hd : regs ≤ e.2.2)
    (hds : e.2.2 < s.M.size) (hd64 : e.2.2 < 2 ^ 64) (hs64 : e.2.1 < 2 ^ 64) (hsr : e.1 = true → regs ≤ e.2.1) :
    (∀ y, regs ≤ y → rd (semXIR I (cp1IR e) s).M y = if y = e.2.2 then cpV I s.M e else rd s.M y) ∧
    Inv (semXIR I (cp1IR e) s).M ∧ (semXIR I (cp1IR e) s).o = s.o ∧
    (semXIR I (cp1IR e) s).M.size = s.M.size := by
  refine ⟨fun y hy => ?_, inv_sem I (wf_cp1IR e) hM, sem_o I _ s (by rcases e with ⟨b, _, _⟩; cases b <;> rfl),
    size_sem ..⟩
  have hs := hM.1
  rcases e with ⟨b, src, dst⟩
  simp only at hd hds hd64 hs64 hsr ⊢
  rw [cp1IR, semXIR_seq, semXIR_seq, semXIR_seq]
  have w1 : WF (XIR.blk [.const rAd4 (toWord src)]) := by simp +decide [WF, Prim.dst, rAd4]
  have hM1 := inv_sem I w1 hM
  have z1 := size_sem I (XIR.blk [.const rAd4 (toWord src)]) s
  have a1 : rd (semXIR I (XIR.blk [.const rAd4 (toWord src)]) s).M rAd4 = toWord src := by
    simp only [semXIR, runPrims, List.foldl, Prim.run]
    rw [rd_set_self (by simp only [regs, rAd4] at hs ⊢; omega)]
  have f1 : ∀ i, i ≠ rAd4 → rd (semXIR I (XIR.blk [.const rAd4 (toWord src)]) s).M i = rd s.M i := fun i hi =>
    rd_runPrims_of_not_writes (by simp only [List.mem_cons, List.mem_nil_iff, or_false]; rintro q rfl; exact hi.symm) _
  generalize semXIR I (XIR.blk [.const rAd4 (toWord src)]) s = s1 at hM1 z1 a1 f1
  have w2 : WF (if b = true then XIR.load rKd rAd4 else XIR.input rKd rAd4) := by
    cases b <;> simp +decide [WF, rKd]
  have hM2 := inv_sem I w2 hM1
  have z2 := size_sem I (if b = true then XIR.load rKd rAd4 else XIR.input rKd rAd4) s1
  have a2 : rd (semXIR I (if b = true then XIR.load rKd rAd4 else XIR.input rKd rAd4) s1).M rKd =
      cpV I s.M (b, src, dst) := by
    have hk : rKd < s1.M.size := by rw [z1]; simp only [regs, rKd] at hs ⊢; omega
    cases b
    · simp only [Bool.false_eq_true, ↓reduceIte, semXIR, cpV]
      rw [rd_set_self hk, a1, toNat_toWord hs64]
    · simp only [↓reduceIte, semXIR, cpV]
      rw [rd_set_self hk, a1, toNat_toWord hs64, f1 _ (by have := hsr rfl; simp only [regs, rAd4] at this ⊢; omega)]
  have f2 : ∀ i, i ≠ rKd →
      rd (semXIR I (if b = true then XIR.load rKd rAd4 else XIR.input rKd rAd4) s1).M i = rd s1.M i := by
    intro i hi
    cases b
    · simp only [Bool.false_eq_true, ↓reduceIte, semXIR]; rw [rd_set_ne (Ne.symm hi)]
    · simp only [↓reduceIte, semXIR]; rw [rd_set_ne (Ne.symm hi)]
  generalize semXIR I (if b = true then XIR.load rKd rAd4 else XIR.input rKd rAd4) s1 = s2 at hM2 z2 a2 f2
  have w3 : WF (XIR.blk [.const rAd4 (toWord dst)]) := by simp +decide [WF, Prim.dst, rAd4]
  have hM3 := inv_sem I w3 hM2
  have z3 := size_sem I (XIR.blk [.const rAd4 (toWord dst)]) s2
  have a3 : rd (semXIR I (XIR.blk [.const rAd4 (toWord dst)]) s2).M rAd4 = toWord dst := by
    simp only [semXIR, runPrims, List.foldl, Prim.run]
    rw [rd_set_self (by rw [z2, z1]; simp only [regs, rAd4] at hs ⊢; omega)]
  have f3 : ∀ i, i ≠ rAd4 → rd (semXIR I (XIR.blk [.const rAd4 (toWord dst)]) s2).M i = rd s2.M i := fun i hi =>
    rd_runPrims_of_not_writes (by simp only [List.mem_cons, List.mem_nil_iff, or_false]; rintro q rfl; exact hi.symm) _
  generalize semXIR I (XIR.blk [.const rAd4 (toWord dst)]) s2 = s3 at hM3 z3 a3 f3
  have hst : semXIR I (XIR.store rAd4 rKd) s3 = ⟨storeM s3.M rAd4 rKd, s3.o⟩ := rfl
  rw [hst]
  have hyT : y ≠ cTmp := by simp only [regs, cTmp] at hy ⊢; omega
  rw [rd_storeM hM3 a3 hd hd64 (by rw [z3, z2, z1]; exact hds) (by decide) (by decide) hyT]
  have hyA : y ≠ rAd4 := by simp only [regs, rAd4] at hy ⊢; omega
  have hyK : y ≠ rKd := by simp only [regs, rKd] at hy ⊢; omega
  split_ifs with hyd
  · rw [f3 _ (by decide), a2]
  · rw [f3 _ hyA, f2 _ hyK, f1 _ hyA]

/-- **The copies**: distinct destinations in `[lo, hi)` above every heap source. -/
theorem cpsIR_sem (I : Array Word) (lo hi : ℕ) :
    ∀ (tab : List (Bool × ℕ × ℕ)) (s : St), Inv s.M → hi ≤ s.M.size → tab.all (cpOK lo hi) = true →
      (tab.map fun e => e.2.2).Nodup →
      (∀ e ∈ tab, rd (semXIR I (cpsIR tab) s).M e.2.2 = cpV I s.M e) ∧
      (∀ y, regs ≤ y → y ∉ tab.map (fun e => e.2.2) → rd (semXIR I (cpsIR tab) s).M y = rd s.M y) ∧
      Inv (semXIR I (cpsIR tab) s).M ∧ (semXIR I (cpsIR tab) s).o = s.o ∧
      (semXIR I (cpsIR tab) s).M.size = s.M.size
  | [], s, hM, _, _, _ =>
    ⟨fun e he => absurd he (by simp), fun y _ _ => by simp [cpsIR, semXIR, runPrims], by
      simpa [cpsIR, semXIR, runPrims] using hM, by simp [cpsIR, semXIR], by simp [cpsIR, semXIR, runPrims]⟩
  | e :: es, s, hM, hhi, hok, hnd => by
    simp only [List.all_cons, Bool.and_eq_true] at hok
    obtain ⟨he, hes⟩ := hok
    have he' := he
    simp only [cpOK, Bool.and_eq_true, decide_eq_true_eq, Bool.or_eq_true, Bool.not_eq_true'] at he'
    obtain ⟨⟨⟨⟨⟨hlo, hld⟩, hdh⟩, hh64⟩, hs64⟩, hsrc⟩ := he'
    simp only [List.map_cons, List.nodup_cons] at hnd
    obtain ⟨hnin, hnd⟩ := hnd
    obtain ⟨c1, c2, c3, c4⟩ := cp1IR_sem I s hM e (by omega) (by omega) (by omega) hs64
      (fun hb => (hsrc.resolve_left (by rw [hb]; decide)).1)
    rw [cpsIR, semXIR_seq]
    obtain ⟨r1, r2, r3, r4, r5⟩ := cpsIR_sem I lo hi es _ c2 (by rw [c4]; exact hhi) hes hnd
    refine ⟨fun e' he' => ?_, fun y hy hy' => ?_, r3, by rw [r4, c3], by rw [r5, c4]⟩
    · rcases List.mem_cons.mp he' with rfl | he'
      · rw [r2 _ (by omega) hnin, c1 _ (by omega), if_pos rfl]
      · rw [r1 e' he']
        have hok' := List.all_eq_true.1 hes e' he'
        simp only [cpOK, Bool.and_eq_true, decide_eq_true_eq, Bool.or_eq_true, Bool.not_eq_true'] at hok'
        unfold cpV
        split_ifs with hb
        · have h2 := hok'.2.resolve_left (by rw [hb]; decide)
          rw [c1 _ h2.1, if_neg (by omega)]
        · rfl
    · simp only [List.map_cons, List.mem_cons, not_or] at hy'
      rw [r2 y hy hy'.2, c1 y hy, if_neg hy'.1]

/-! ## The opening's runs, value by event -/

theorem readF_run {l : List Ev} {y : E2} (h : (readF chalE2).after l = some (.ret y)) :
    ∃ x, l = [Ev.read x] ∧ y = e2OfE x := by
  rcases l with _ | ⟨e, es⟩
  · simp [readF, VerifierProgram.after, VerifierProgram.readScalar, VerifierProgram.bind] at h
  · cases e <;> simp [readF, VerifierProgram.after, VerifierProgram.readScalar, VerifierProgram.bind] at h
    rename_i x
    obtain ⟨rfl, h2⟩ := after_ret_eq h
    refine ⟨x, rfl, ?_⟩
    have h3 : VerifierProgram.ret (chalE2.rd x) = VerifierProgram.ret y := h2.symm
    exact (VerifierProgram.ret.inj h3).symm

theorem readFs_run : ∀ (n : ℕ) {l : List Ev} {ys : List E2}, (readFs chalE2 n).after l = some (.ret ys) →
    l.length = n ∧ ∀ k < n, ∃ x, l[k]? = some (Ev.read x) ∧ ys.getD k 0 = e2OfE x
  | 0, l, ys, h => by
    obtain ⟨rfl, -⟩ := after_ret_eq h
    exact ⟨rfl, fun k hk => absurd hk (by omega)⟩
  | n + 1, l, ys, h => by
    obtain ⟨y, l₁, l₂, rfl, h1, h2⟩ := after_bind_ret h
    obtain ⟨x, rfl, rfl⟩ := readF_run h1
    obtain ⟨ys', l₃, l₄, rfl, h3, h4⟩ := after_bind_ret h2
    obtain ⟨rfl, h5⟩ := after_ret_eq h4
    have h6 : ys = e2OfE x :: ys' := VerifierProgram.ret.inj h5
    subst h6
    obtain ⟨hl, hv⟩ := readFs_run n h3
    refine ⟨by simp [hl], fun k hk => ?_⟩
    cases k with
    | zero => exact ⟨x, by simp, rfl⟩
    | succ k =>
      obtain ⟨x', h7, h8⟩ := hv k (by omega)
      exact ⟨x', by simpa using h7, by simpa using h8⟩

theorem roundP_run {g : ℕ} {l : List Ev} {r : Rnd E2} (h : (roundP chalE2 g).after l = some (.ret r)) :
    ∃ c c' : E, l[5]? = some (Ev.sample c) ∧ l[6]? = some (Ev.sample c') ∧ r.α = e2OfE c ∧ r.β = e2OfE c' := by
  obtain ⟨_, l₁, r₁, rfl, h1, hA⟩ := after_bind_ret h
  obtain ⟨_, rfl, -⟩ := readF_run h1
  obtain ⟨_, l₂, r₂, rfl, h2, hB⟩ := after_bind_ret hA
  obtain ⟨_, rfl, -⟩ := readF_run h2
  obtain ⟨_, l₃, r₃, rfl, h3, hC⟩ := after_bind_ret hB
  obtain ⟨_, rfl, -⟩ := readF_run h3
  obtain ⟨_, l₄, r₄, rfl, h4, hD⟩ := after_bind_ret hC
  obtain ⟨_, rfl, -⟩ := readF_run h4
  obtain ⟨v, l₅, r₅, rfl, h5, hE⟩ := after_bind_ret hD
  obtain ⟨x, c, cs, rfl, hlen, rfl⟩ := grp6_run h5
  obtain ⟨rfl, h6⟩ := after_ret_eq hE
  match cs, hlen with
  | [c'], _ =>
    have h7 := (VerifierProgram.ret.inj h6).symm
    subst h7
    exact ⟨c, c', by simp, by simp, rfl, rfl⟩

theorem roundsP_run {g : ℕ} : ∀ (j : ℕ) {l : List Ev} {rs : List (Rnd E2)},
    (roundsP chalE2 g j).after l = some (.ret rs) →
    rs.length = j ∧ ∀ k < j, ∃ c c' : E, l[7 * k + 5]? = some (Ev.sample c) ∧ l[7 * k + 6]? = some (Ev.sample c') ∧
      (rs.getD k default).α = e2OfE c ∧ (rs.getD k default).β = e2OfE c'
  | 0, l, rs, h => by
    obtain ⟨rfl, h2⟩ := after_ret_eq h
    have h3 : rs = [] := VerifierProgram.ret.inj h2
    exact ⟨by simp [h3], fun k hk => absurd hk (by omega)⟩
  | j + 1, l, rs, h => by
    obtain ⟨r, l₁, l₂, rfl, h1, hA⟩ := after_bind_ret h
    obtain ⟨rs', l₃, l₄, rfl, h3, h4⟩ := after_bind_ret hA
    obtain ⟨rfl, h5⟩ := after_ret_eq h4
    have h6 : rs = r :: rs' := VerifierProgram.ret.inj h5
    subst h6
    have hl1 : l₁.length = 7 := after_length _ (follows_roundP g) h1
    obtain ⟨hl, hv⟩ := roundsP_run j h3
    refine ⟨by simp [hl], fun k hk => ?_⟩
    cases k with
    | zero =>
      obtain ⟨c, c', a1, a2, a3, a4⟩ := roundP_run h1
      exact ⟨c, c', by rw [List.getElem?_append_left (by omega)]; exact a1,
        by rw [List.getElem?_append_left (by omega)]; exact a2, a3, a4⟩
    | succ k =>
      obtain ⟨c, c', a1, a2, a3, a4⟩ := hv k (by omega)
      refine ⟨c, c', ?_, ?_, by simpa using a3, by simpa using a4⟩
      · rw [List.getElem?_append_right (by omega), hl1, show 7 * (k + 1) + 5 - 7 = 7 * k + 5 by omega,
          List.append_nil]
        exact a1
      · rw [List.getElem?_append_right (by omega), hl1, show 7 * (k + 1) + 6 - 7 = 7 * k + 6 by omega,
          List.append_nil]
        exact a2

/-- **A tail's high parts** are its first `nh` reads. -/
theorem tailP_hi {n n' m' : ℕ} (L : TailIface E2 n n' m') (ht wd i gO gQ : ℕ) (vals)
    {l : List Ev} {o : TailOut E2 L.ko L.t n} (h : (tailP L chalE2 ht wd i gO gQ vals).after l = some (.ret o)) :
    ∀ k < L.nh, ∃ x, l[k]? = some (Ev.read x) ∧ o.hi.getD k 0 = e2OfE x := by
  obtain ⟨hi, l₁, l₂, rfl, h1, hA⟩ := after_bind_ret h
  obtain ⟨hl, hv⟩ := readFs_run L.nh h1
  have ho : o.hi = hi := by
    obtain ⟨_, _, l₃, rfl, -, hB⟩ := after_bind_ret hA
    obtain ⟨_, _, l₄, rfl, -, hC⟩ := after_bind_ret hB
    obtain ⟨_, _, l₅, rfl, -, hD⟩ := after_bind_ret hC
    obtain ⟨_, _, l₆, rfl, -, hE⟩ := after_bind_ret hD
    obtain ⟨_, _, l₇, rfl, -, hF⟩ := after_bind_ret hE
    obtain ⟨_, _, l₈, rfl, -, hG⟩ := after_bind_ret hF
    obtain ⟨-, hH⟩ := after_ret_eq hG
    rw [VerifierProgram.ret.inj hH]
  intro k hk
  obtain ⟨x, h1, h2⟩ := hv k hk
  exact ⟨x, by rw [List.getElem?_append_left (by omega)]; exact h1, by rw [ho]; exact h2⟩

end Lvm6.X
