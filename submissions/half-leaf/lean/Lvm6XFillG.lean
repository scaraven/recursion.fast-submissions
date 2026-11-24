-- lvm6 X1 (PORT17): the fill block's generic parts, moved here unchanged from `Lvm6XFill` (the copy program
-- `cpsIR`, its semantics, cost and size) and `Lvm6XFill18` (`cpOf`, the `drop` lookups, `length_srcsOp`, the linear
-- `Nodup` check `sortedLt`), so that a shape's fill instance needs neither `Lvm6XFront6` nor `P18`; and the request
-- geometry over any shape (`FillGeo`, `reqsOf`, `fillTabOf`, `srcOKAt`, the opening's operations `openOpsOf`).
import Lvm6XFront6Run
import Lvm6WhirFollow
import LvmXDecCost

/-!
# The fill block's generic parts

* **`cp1IR (b, src, dst)`**: `M[dst] :=` `M[src]` (`b`) or tape word `src`; **`cpsIR tab`** the copies in order.
  **`cpsIR_sem`**: for copies whose destinations are distinct and lie in `[lo, hi)`, above every heap source,
  `M'[dst] = cpV I M e` for each copy, every other cell `≥ regs` kept, `Inv`, no output, same size.
  `cost_cpsIR`, `sizeIR_cpsIR`: at most `21·|tab| + 4`. (From `Lvm6XFill`, unchanged.)
* **`cpOf`**, **`getD_eq_getD_drop`**, **`flatMap_getD_drop`**, **`all_getD_drop`**, **`length_srcsOp`**,
  **`sortedLt`**, **`nodup_of_sortedLt`**. (From `Lvm6XFill18`, unchanged.)
* **`FillGeo`** (`rnd i` rounds at level `i`, `tl i` events in tail `i`, `nFin` final scalars, `N` the opening's first
  event), **`FillGeo.base i`**: level `i`'s first event in the opening. **`reqsOf fg ch hi s`**: `Lvm6XFill18.reqs`'s
  requests at any geometry: round `k` of level `i` draws `α`, `β` at events `N + base i + 7k + 5, + 6` into `ch i k`,
  `ch i k + 2`; tail `i`'s high part `k` is event `N + base i + 7 rnd i + k` into `hi i + 2k`; final scalar `k` is
  event `N + base 4 + 7 rnd 4 + k` into `s + 2k`. **`fillTabOf srcs fg ch hi s`**: two word copies a request.
  **`srcOKAt pz n`**: `Lvm6XFill18.reqOK`'s body with the proof size `pz` (`Lvm6XFill18.reqOK_eq`:
  `srcOKAt xg17.pz (nCh6 P17)`).
* **`openOpsOf rnd tails nFin kqF nSum`**: the opening's operations, level by level (`Lvm6WhirFollow.opsD`'s form);
  **`fillTabOf_drop`**: a table whose requests all lie past event `N₀` reads the sources' `drop N₀` only.
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

/-- The two word copies of a request from its event's source. -/
def cpOf : Src → ℕ → List (Bool × ℕ × ℕ)
  | .smp p, dst => [(true, ansB + 4 * p, dst), (true, ansB + 4 * p + 1, dst + 1)]
  | .rd off _, dst => [(false, 5 + off / 8, dst), (false, 5 + off / 8 + 1, dst + 1)]
  | _, _ => []


/-- `getD` past a prefix is `getD` of the `drop`. -/
theorem getD_eq_getD_drop {α : Type*} (l : List α) (d : α) {n i : ℕ} (h : n ≤ i) :
    l.getD i d = (l.drop n).getD (i - n) d := by
  rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, List.getElem?_drop, Nat.add_sub_cancel' h]

/-- `flatMap` of lookups past a prefix reads the `drop`. -/
theorem flatMap_getD_drop {α β : Type*} (l : List α) (d : α) (n : ℕ) (f : α → ℕ → List β) :
    ∀ rs : List (ℕ × ℕ), rs.all (fun r => decide (n ≤ r.1)) = true →
      rs.flatMap (fun r => f (l.getD r.1 d) r.2) = rs.flatMap (fun r => f ((l.drop n).getD (r.1 - n) d) r.2)
  | [], _ => rfl
  | r :: rs, h => by
    simp only [List.all_cons, Bool.and_eq_true, decide_eq_true_eq] at h
    rw [List.flatMap_cons, List.flatMap_cons, getD_eq_getD_drop l d h.1, flatMap_getD_drop l d n f rs h.2]

/-- `all` of lookups past a prefix reads the `drop`. -/
theorem all_getD_drop {α : Type*} (l : List α) (d : α) (n : ℕ) (g : α → Bool) :
    ∀ rs : List (ℕ × ℕ), rs.all (fun r => decide (n ≤ r.1)) = true →
      rs.all (fun r => g (l.getD r.1 d)) = rs.all (fun r => g ((l.drop n).getD (r.1 - n) d))
  | [], _ => rfl
  | r :: rs, h => by
    simp only [List.all_cons, Bool.and_eq_true, decide_eq_true_eq] at h
    rw [List.all_cons, List.all_cons, getD_eq_getD_drop l d h.1, all_getD_drop l d n g rs h.2]

/-- **One source per operation.** -/
theorem length_srcsOp (cO oc : ℕ → ℕ → ℕ) (t : ℕ → ℕ) :
    ∀ (cs : List (ℕ × ℕ × ℕ)) (ws : List ℕ) (o P : ℕ) (os : List Op),
      (srcsOp cO oc t cs ws o P os).length = os.length
  | _, _, _, _, [] => rfl
  | cs, ws, o, P, .rd :: os => by
    rw [srcsOp, List.length_cons, List.length_cons, length_srcsOp cO oc t _ _ _ _ os]
  | cs, ws, o, P, .smp :: os => by
    rw [srcsOp, List.length_cons, List.length_cons, length_srcsOp cO oc t _ _ _ _ os]
  | cs, ws, o, P, .cap ht w :: os => by
    rw [srcsOp, List.length_cons, List.length_cons, length_srcsOp cO oc t _ _ _ _ os]
  | cs, ws, o, P, .opn i :: os => by
    rw [srcsOp, List.length_cons, List.length_cons, length_srcsOp cO oc t _ _ _ _ os]

/-- Strictly increasing (a linear check for `Nodup`). -/
def sortedLt : List ℕ → Bool
  | a :: b :: l => decide (a < b) && sortedLt (b :: l)
  | _ => true

theorem sortedLt_tail {a : ℕ} {l : List ℕ} (h : sortedLt (a :: l) = true) : sortedLt l = true := by
  match l, h with
  | [], _ => rfl
  | b :: l, h =>
    simp only [sortedLt, Bool.and_eq_true] at h
    exact h.2

theorem lt_of_sortedLt : ∀ {a : ℕ} {l : List ℕ}, sortedLt (a :: l) = true → ∀ x ∈ l, a < x
  | _, [], _, _, hx => absurd hx List.not_mem_nil
  | a, b :: l, h, x, hx => by
    have h' := h
    simp only [sortedLt, Bool.and_eq_true, decide_eq_true_eq] at h'
    rcases List.mem_cons.1 hx with rfl | hx
    · exact h'.1
    · exact h'.1.trans (lt_of_sortedLt (sortedLt_tail h) x hx)

theorem nodup_of_sortedLt : ∀ {l : List ℕ}, sortedLt l = true → l.Nodup
  | [], _ => List.nodup_nil
  | a :: _, h => List.nodup_cons.2 ⟨fun ha ↦ lt_irrefl a (lt_of_sortedLt h a ha), nodup_of_sortedLt (sortedLt_tail h)⟩

/-! ## The request geometry -/

/-- **The fill's request geometry** at a shape. -/
structure FillGeo where
  /-- Level `i`'s fold rounds. -/
  rnd : ℕ → ℕ
  /-- Tail `i`'s events. -/
  tl : ℕ → ℕ
  /-- The final polynomial's scalars. -/
  nFin : ℕ
  /-- The opening's first event in the history. -/
  N : ℕ

/-- Level `i`'s first event in the opening's log. -/
def FillGeo.base (fg : FillGeo) : ℕ → ℕ
  | 0 => 0
  | i + 1 => fg.base i + 7 * fg.rnd i + fg.tl i

/-- **The requests** `(event index, cell)`, the cells `ch i k` (challenge pairs), `hi i` (high parts), `s` (final
scalars). -/
def reqsOf (fg : FillGeo) (ch : ℕ → ℕ → ℕ) (hi : ℕ → ℕ) (s : ℕ) : List (ℕ × ℕ) :=
  ((List.range 5).flatMap fun i ↦ (List.range (fg.rnd i)).flatMap fun k ↦
    [(fg.N + fg.base i + 7 * k + 5, ch i k), (fg.N + fg.base i + 7 * k + 6, ch i k + 2)]) ++
  ((List.range 4).flatMap fun i ↦ (List.range (fg.rnd i)).map fun k ↦
    (fg.N + fg.base i + 7 * fg.rnd i + k, hi i + 2 * k)) ++
  ((List.range fg.nFin).map fun k ↦ (fg.N + fg.base 4 + 7 * fg.rnd 4 + k, s + 2 * k))

/-- **The copies** of the requests from the sources `srcs`. -/
def fillTabOf (srcs : List Src) (fg : FillGeo) (ch : ℕ → ℕ → ℕ) (hi : ℕ → ℕ) (s : ℕ) : List (Bool × ℕ × ℕ) :=
  (reqsOf fg ch hi s).flatMap fun r ↦ cpOf (srcs.getD r.1 default) r.2

/-- A request's check from its source: a draw inside the chain of `n` targets, or a word-aligned 16-byte read inside
a proof of `pz` bytes. -/
def srcOKAt (pz n : ℕ) : Src → Bool
  | .smp p => decide (p < n)
  | .rd off w => decide (w = 16) && decide (off % 8 = 0) && decide (off + 16 ≤ pz)
  | _ => false

/-- **A table whose requests lie past event `N₀`** reads only the sources from `N₀` on. -/
theorem fillTabOf_drop (srcs : List Src) (fg : FillGeo) (ch : ℕ → ℕ → ℕ) (hi : ℕ → ℕ) (s N₀ : ℕ)
    (h : (reqsOf fg ch hi s).all (fun r => decide (N₀ ≤ r.1)) = true) :
    fillTabOf srcs fg ch hi s =
      (reqsOf fg ch hi s).flatMap fun r ↦ cpOf ((srcs.drop N₀).getD (r.1 - N₀) default) r.2 :=
  flatMap_getD_drop srcs default N₀ cpOf _ h

/-- **The opening's operations**: per level `rnd i` rounds, then the tail `tails i` (levels 0–3); at the last level
its rounds, `nFin` final scalars, the position group (`kqF + 1` draws), the openings and `nSum` tail sumcheck rounds. -/
def openOpsOf (rnd : ℕ → ℕ) (tails : ℕ → List Op) (nFin kqF nSum : ℕ) : List Op :=
  (List.replicate (rnd 0) roundOps).flatten ++ (tails 0 ++
  ((List.replicate (rnd 1) roundOps).flatten ++ (tails 1 ++
  ((List.replicate (rnd 2) roundOps).flatten ++ (tails 2 ++
  ((List.replicate (rnd 3) roundOps).flatten ++ (tails 3 ++
  ((List.replicate (rnd 4) roundOps).flatten ++ (List.replicate nFin .rd ++
    ((.rd :: List.replicate (kqF + 1) .smp) ++ ([.opn 4] ++ sumOps nSum)))))))))))

end Lvm6.X
