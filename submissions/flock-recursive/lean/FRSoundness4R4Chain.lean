-- New for `flock-recursive` (BLUEPRINT revision 4.1, §6.2, A.4; stage R4).
import FRSoundness4R4Ref

/-!
# `gen4`'s Fiat–Shamir queries: the chain of `fsMsgs4`

3.x's `fsQ_gen` (`FRVIRChain`) for `gen4 S p fin`: on a trace a run consumes completely, the
entries at the Fiat–Shamir items of `itemsOf S` form the chain of the messages `fsMsgs4 S`
(absolute `(offset, length)` pairs in `S`'s format): entry `q` asks `qOf inp q (fsMsgs4 S)[q]` of
entry `q − 1`'s answer (**`fsQ_gen4`**).

* `phaseMsgs4 S n sh`, `fsMsgs4 S`: a phase's messages, all phases' (3.x's `phaseMsgs`/`fsMsgs`
  with `S`'s offsets).
* **`refPhase4_chain`**: one phase consumes one entry per item; its FS entries are the chain of its
  messages from the state register, and the next context's state register holds the last answer.
  A query phase consumes only column and node entries (`exec_ext`, `items_genPhase4`).
* `refPhases4_chain`, `skeleton4_chain` compose; the table facts are `shOK4` (squeezes nonempty)
  over `phasesOf S`.
-/

namespace FR.Snd.R4
open RecursionFast Rev4

/-! ## The messages -/

/-- **A phase's Fiat–Shamir messages** (`S`'s absolute offsets). -/
def phaseMsgs4 (S : Seq) (n : ℕ) : Sh → List (Option (ℕ × ℕ))
  | .seed => [some (0, 48)]
  | .absorb f len => [some (fieldOffOf S f + phaseOffOf S n f, len)]
  | .squeezes k _ => List.replicate k none
  | .uni f => [some (fieldOffOf S f + phaseOffOf S n f, uniBytes), none]
  | .rounds f k _ inK => roundMsgs 0 (fieldOffOf S f + phaseOffOf S n f) (roundBytes inK) 0 k
  | .queries _ => []

/-- The messages of the phases from number `n`. -/
def msgsFrom4 (S : Seq) : List (String × Sh) → ℕ → List (Option (ℕ × ℕ))
  | [], _ => []
  | ph :: ps, n => phaseMsgs4 S n ph.2 ++ msgsFrom4 S ps (n + 1)

/-- **The Fiat–Shamir messages of `S`**, in item order. -/
def fsMsgs4 (S : Seq) : List (Option (ℕ × ℕ)) := msgsFrom4 S (phasesOf S) 0

/-- A shape the chain lemma covers: a nonempty run of squeezes. -/
def shOK4 : Sh → Bool
  | .squeezes k _ => decide (0 < k)
  | _ => true

def isSeed4 : Sh → Bool
  | .seed => true
  | _ => false

theorem itemsL_allFS {s : Sh} (lv : ℕ → Level) (h : ∀ i, s ≠ .queries i) :
    ∀ it ∈ s.itemsL lv, it.isFS = true := by
  intro it hit
  cases s with
  | queries i => exact absurd rfl (h i)
  | rounds =>
    simp only [Sh.itemsL, List.mem_flatten, List.mem_replicate] at hit
    obtain ⟨l, ⟨-, rfl⟩, hit⟩ := hit
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hit
    rcases hit with rfl | rfl <;> rfl
  | squeezes => rcases List.mem_replicate.1 hit with ⟨-, rfl⟩; rfl
  | uni =>
    simp only [Sh.itemsL, List.mem_cons, List.not_mem_nil, or_false] at hit
    rcases hit with rfl | rfl <;> rfl
  | seed | absorb =>
    simp only [Sh.itemsL, List.mem_cons, List.not_mem_nil, or_false] at hit
    subst hit; rfl

theorem pureRun_base {impl : OpImpl} {κ : Kind} {inp : Input} {os : List Op} {r : Array Val}
    {base : List Val} {y : List Val × Bool} (h : pureRun impl κ inp os r base = some y) :
    ∃ M, y.1 = base ++ M := by
  have := pureRun_rebase impl κ inp os r base []
  rw [List.append_nil] at this
  rw [this] at h
  obtain ⟨z, -, rfl⟩ := Option.map_eq_some_iff.1 h
  exact ⟨z.1, rfl⟩

theorem fieldOffA_zero : fieldOffA.getD 0 0 = 0 := by rw [fieldOffA_getD (by decide)]; rfl

/-! ## One phase -/

section Chain
variable (impl : OpImpl) (κ : Kind) (inp : Input) (S : Seq) (p : KindP)

/-- **One phase's Fiat–Shamir entries** are the chain of its messages from the state register,
and the next context's state register holds the last answer. -/
theorem refPhase4_chain {n : ℕ} {ph : String × Sh} {c : GCtx} {r : Array Val} {tr : Trace}
    {x : List Val × Bool × Trace} (hx : refPhase4 impl κ inp S p n ph c r tr = some x)
    (hb : c.next = r.size) (hok : shOK4 ph.2 = true) {q0 : ℕ}
    (hq : isSeed4 ph.2 = true ↔ q0 = 0) (hst : isSeed4 ph.2 = true ∨ c.st < r.size) :
    ∃ seg, tr = seg ++ x.2.2 ∧ seg.length = (ph.2.itemsL S.lv).length ∧
      ChainOK inp (fsOf seg (ph.2.itemsL S.lv)) (phaseMsgs4 S n ph.2) q0 (rd r c.st).toD ∧
      (rd (r ++ x.1.toArray) (genPhase4 S p n ph c).2.st).toD =
        FR.lastAns (fsOf seg (ph.2.itemsL S.lv)) (rd r c.st).toD := by
  obtain ⟨name, sh⟩ := ph
  obtain ⟨b, st, u, pa, fr, pt, outs⟩ := c
  simp only at hb hok hq hst ⊢; subst hb
  cases sh with
  | seed =>
    simp only [isSeed4, true_iff] at hq; subst hq
    simp only [refPhase4] at hx
    rcases tr with _ | ⟨⟨q, a⟩, tr⟩
    · cases hx
    simp only at hx
    split_ifs at hx with hq
    obtain ⟨y, hy, rfl⟩ := Option.map_eq_some_iff.1 hx
    obtain ⟨M, hM⟩ := pureRun_base hy
    refine ⟨[(q, a)], rfl, rfl, ?_, ?_⟩
    · rw [fsOf_all (itemsL_allFS (s := .seed) S.lv (by simp)) rfl]
      simp only [phaseMsgs4, ChainOK, qOf, ite_true, and_true, hq, FR.msgAt, absOff_zero]
    · rw [fsOf_all (itemsL_allFS (s := .seed) S.lv (by simp)) rfl]
      simp only [genPhase4, hM]
      rw [rd_app _ _ 1]; rfl
  | absorb f len =>
    simp only [isSeed4, false_iff, Bool.false_eq_true, false_or] at hq hst
    simp only [refPhase4] at hx
    obtain ⟨⟨a, tr'⟩, hans, hx⟩ := Option.bind_eq_some_iff.1 hx
    obtain ⟨y, hy, rfl⟩ := Option.map_eq_some_iff.1 hx
    obtain ⟨M, hM⟩ := pureRun_base hy
    rcases tr with _ | ⟨⟨q, a'⟩, tr⟩
    · cases hans
    simp only [ans1] at hans
    split_ifs at hans with hqq
    cases hans
    refine ⟨[(q, a)], rfl, rfl, ?_, ?_⟩
    · rw [fsOf_all (itemsL_allFS (s := .absorb f len) S.lv (by simp)) rfl]
      simp only [phaseMsgs4, ChainOK, qOf, if_neg hq, and_true, hqq, FR.msgAt, absOff_zero]
    · rw [fsOf_all (itemsL_allFS (s := .absorb f len) S.lv (by simp)) rfl]
      simp only [genPhase4, hM]
      split_ifs <;> (rw [rd_app _ _ 1]; rfl)
  | squeezes k ch =>
    simp only [isSeed4, false_iff, Bool.false_eq_true, false_or] at hq hst
    simp only [shOK4, decide_eq_true_eq] at hok
    simp only [refPhase4] at hx
    obtain ⟨y, hy, rfl⟩ := Option.map_eq_some_iff.1 hx
    obtain ⟨seg, h1, h2, h3, h4⟩ := sqzT_chain inp hy q0
    have hk : y.1.length = k := by rw [← h4, List.length_map, h2]
    have hne : y.1 ≠ [] := by
      rw [← h4]; intro h; rw [List.map_eq_nil_iff] at h; subst h; simp at h2; omega
    have hfs := fsOf_all (seg := seg) (itemsL_allFS (s := .squeezes k ch) S.lv (by simp))
      (by simp [Sh.itemsL, h2])
    refine ⟨seg, ?_, by simp [Sh.itemsL, h2], ?_, ?_⟩
    · cases ch <;> exact h1
    · rw [hfs]; exact h3
    · rw [hfs, lastAns_map h4]
      cases ch <;> simp only [genPhase4]
      · rw [show r.size + 3 * k - 3 = r.size + (3 * y.1.length - 3) by omega, rd_app,
          getD_last_coords hne]; exact getLastD_ne hne _ _
      · rw [show r.size + k - 1 = r.size + (y.1.length - 1) by omega, rd_app, getD_last_map hne]
        exact getLastD_ne hne _ _
      · rw [show r.size + k - 1 = r.size + (y.1.length - 1) by omega, rd_app,
          ← List.append_nil (y.1.map Val.d), getD_last_map hne]; exact getLastD_ne hne _ _
  | uni f =>
    simp only [isSeed4, false_iff, Bool.false_eq_true, false_or] at hq hst
    simp only [refPhase4] at hx
    rcases tr with _ | ⟨⟨q₁, a₁⟩, _ | ⟨⟨q₂, a₂⟩, tr⟩⟩
    · cases hx
    · cases hx
    simp only at hx
    split_ifs at hx with hqq hnd <;> cases hx <;>
    · refine ⟨[(q₁, a₁), (q₂, a₂)], rfl, rfl, ?_, ?_⟩
      · rw [fsOf_all (itemsL_allFS (s := .uni f) S.lv (by simp)) rfl]
        simp only [phaseMsgs4, ChainOK, qOf, if_neg hq, and_true, hqq.1, hqq.2, FR.msgAt, absOff_zero]
      · rw [fsOf_all (itemsL_allFS (s := .uni f) S.lv (by simp)) rfl]
        simp only [genPhase4, hnd, ite_true, ite_false, Bool.false_eq_true]
        first
          | (rw [rd_app _ _ 2]; simp [uniVals, FR.lastAns, Val.toD])
          | (rw [rd_app _ _ 3]; simp [uniVals, FR.lastAns, Val.toD])
  | rounds f k deg inK =>
    simp only [isSeed4, false_iff, Bool.false_eq_true, false_or] at hq hst
    simp only [refPhase4] at hx
    obtain ⟨y, hy, rfl⟩ := Option.map_eq_some_iff.1 hx
    obtain ⟨seg, h1, h2, h3, h4⟩ := roundsT_chain inp hy hq
    have hfs := fsOf_all (seg := seg) (itemsL_allFS (s := .rounds f k deg inK) S.lv (by simp))
      (by simp [Sh.itemsL, h2, Nat.mul_comm])
    refine ⟨seg, h1, by simp [Sh.itemsL, h2, Nat.mul_comm], ?_, ?_⟩
    · rw [hfs, phaseMsgs4, ← fieldOffA_zero]; exact h3
    · rw [hfs, h4]
      have hiv := initVals_length inp (initClaim name) 0 (fieldOffOf S f + phaseOffOf S n f) inK
      generalize initVals inp (initClaim name) 0 (fieldOffOf S f + phaseOffOf S n f) inK = iv at hiv ⊢
      simp only [genPhase4]
      generalize initClaim name = ic at hiv ⊢
      cases ic <;> cases inK <;>
        simp only [initOps, Init.width, ite_true, ite_false, Bool.false_eq_true] at hiv ⊢ <;>
        (split_ifs with hk0
         · rw [rd_append_left hst]
         · rw [show ∀ w m : ℕ, r.size + m + w * k - w + 2 = r.size + (m + (w * k - w + 2)) from
              fun w m => by have := Nat.le_mul_of_pos_right w (Nat.pos_of_ne_zero hk0); omega,
            rd_app, ← hiv, getD_app])
  | queries i =>
    simp only [isSeed4, false_iff, Bool.false_eq_true, false_or] at hq hst
    simp only [refPhase4] at hx
    obtain ⟨⟨s, tr'⟩, hy, rfl⟩ := Option.map_eq_some_iff.1 hx
    obtain ⟨L, hL, -, seg, h1, h2⟩ := exec_ext impl κ inp _ r true tr s tr' hy
    rw [items_genPhase4] at h2
    have hfs : fsOf seg ((Sh.queries i).itemsL S.lv) = [] := fsOf_none fun it hit => by
      simp only [Sh.itemsL, List.mem_flatten, List.mem_replicate] at hit
      obtain ⟨l, ⟨-, rfl⟩, hit⟩ := hit
      simp only [posItemsL, List.mem_cons, List.mem_map] at hit
      rcases hit with rfl | ⟨_, -, rfl⟩ <;> rfl
    refine ⟨seg, h1, h2, ?_, ?_⟩
    · rw [hfs]; simp [phaseMsgs4, ChainOK]
    · rw [hfs]; simp only [genPhase4]; rw [rd_append_left hst]; rfl

/-- **A run of non-seed phases**: its Fiat–Shamir entries are the chain of `msgsFrom4`. -/
theorem refPhases4_chain : ∀ (ps : List (String × Sh)) (n : ℕ) (c : GCtx) (r : Array Val) (tr : Trace)
    (y : List Val × List Bool × Trace) (q0 : ℕ), refPhases4 impl κ inp S p ps n c r tr = some y →
    c.next = r.size → CtxOk c r → q0 ≠ 0 →
    ps.all (fun ph => shOK4 ph.2 && !isSeed4 ph.2) = true →
    ∃ seg, tr = seg ++ y.2.2 ∧ seg.length = (ps.flatMap fun ph => ph.2.itemsL S.lv).length ∧
      ChainOK inp (fsOf seg (ps.flatMap fun ph => ph.2.itemsL S.lv)) (msgsFrom4 S ps n) q0 (rd r c.st).toD
  | [], n, c, r, tr, y, q0, h, _, _, _, _ => by
    simp [refPhases4] at h; subst h; exact ⟨[], by simp, rfl, by simp [fsOf, msgsFrom4, ChainOK]⟩
  | ph :: ps, n, c, r, tr, y, q0, h, hb, hc, hq, ha => by
    simp only [List.all_cons, Bool.and_eq_true, Bool.not_eq_true'] at ha
    obtain ⟨⟨hok, hns⟩, ha⟩ := ha
    simp only [refPhases4, Option.bind_eq_some_iff, Option.map_eq_some_iff] at h
    obtain ⟨x, hx, y', hy', rfl⟩ := h
    obtain ⟨s₁, h1, h2, h3, h4⟩ := refPhase4_chain impl κ inp S p hx hb hok (q0 := q0)
      (by simp [hns, hq]) (.inr hc.1)
    obtain ⟨hn, hc', -⟩ := genPhase4_ctx impl κ inp S p n ph c r tr x hb (.inr hc) hx
    have hl := ChainOK_length inp h3
    obtain ⟨s₂, h5, h6, h7⟩ := refPhases4_chain ps (n + 1) _ _ _ y'
      (q0 + (fsOf s₁ (ph.2.itemsL S.lv)).length) hy' hn hc' (by omega) ha
    refine ⟨s₁ ++ s₂, by rw [h1, h5, List.append_assoc], by simp [h2, h6], ?_⟩
    rw [List.flatMap_cons, fsOf_append h2, msgsFrom4, ChainOK_append inp hl]
    exact ⟨h3, by rw [← h4]; exact h7⟩

/-- The initial context. -/
def ctx0 : GCtx := ⟨0, 0, 0, [], [], 0, #[]⟩

/-- **The skeleton of `gen4 S p`**: its Fiat–Shamir entries are the chain of `fsMsgs4 S` from
position `0`, for every `S` whose phases after the seed have nonempty squeezes (`seq4`: `shOK_seq4`). -/
theorem skeleton4_chain (hS : ((phasesOf S).drop 1).all (fun ph => shOK4 ph.2 && !isSeed4 ph.2) = true)
    {tr : Trace} {y : List Val × List Bool × Trace}
    (h : refPhases4 impl κ inp S p (phasesOf S) 0 ctx0 #[] tr = some y) :
    ∃ seg, tr = seg ++ y.2.2 ∧ seg.length = (itemsOf S).length ∧
      ChainOK inp (fsOf seg (itemsOf S)) (fsMsgs4 S) 0 (rd #[] 0).toD := by
  obtain ⟨ps, hps⟩ : ∃ ps, phasesOf S = ("seed", .seed) :: ps := ⟨_, rfl⟩
  rw [fsMsgs4, itemsOf]
  rw [hps] at h hS ⊢
  simp only [List.drop_succ_cons, List.drop_zero] at hS
  simp only [refPhases4, Option.bind_eq_some_iff, Option.map_eq_some_iff] at h
  obtain ⟨x, hx, y', hy', rfl⟩ := h
  obtain ⟨s₁, h1, h2, h3, h4⟩ := refPhase4_chain impl κ inp S p hx rfl rfl (q0 := 0)
    (by simp [isSeed4]) (.inl rfl)
  obtain ⟨hn, hc', -⟩ := genPhase4_ctx impl κ inp S p 0 _ ctx0 #[] tr x rfl
    (.inl ⟨rfl, by simp [CtxOk, ctx0]⟩) hx
  have hl := ChainOK_length inp h3
  have hs1 : (fsOf s₁ (Sh.itemsL S.lv .seed)).length = 1 := by rw [hl]; rfl
  obtain ⟨s₂, h5, h6, h7⟩ := refPhases4_chain impl κ inp S p ps 1 _ _ _ y' 1 hy' hn hc' (by omega) hS
  refine ⟨s₁ ++ s₂, by rw [h1, h5, List.append_assoc], by simp [h2, h6], ?_⟩
  rw [List.flatMap_cons, fsOf_append h2, msgsFrom4, ChainOK_append inp hl]
  refine ⟨h3, ?_⟩
  rw [hs1, Nat.zero_add, show rd #[] 0 = rd #[] ctx0.st from rfl, ← h4]; exact h7

/-- **The query link at revision 4.1** (3.x's `fsQ_gen`): on a trace that a run of `gen4 S p fin`
consumes completely, the Fiat–Shamir entries are `|fsMsgs4 S|`, and entry `q` asks the query of
message `q` from entry `q − 1`'s answer. -/
theorem fsQ_gen4 (hS : ((phasesOf S).drop 1).all (fun ph => shOK4 ph.2 && !isSeed4 ph.2) = true)
    (fin : FinOps) {es : Trace} {b : Bool} (h : semIR impl (gen4 S p fin) inp es = some b) :
    (fsOf es (itemsOf S)).length = (fsMsgs4 S).length ∧ ∀ q < (fsMsgs4 S).length,
      ((fsOf es (itemsOf S)).getD q default).1 =
        qOf inp q ((fsMsgs4 S).getD q none) ((fsOf es (itemsOf S)).getD (q - 1) default).2 := by
  unfold semIR at h
  split at h
  · next s hs =>
    rw [show (gen4 S p fin).ops = (skeleton4 S p).1 ++
        (fin (skeleton4 S p).2.outs (skeleton4 S p).2.next ++ [.accept]) by simp [gen4],
      St.init, exec_skeleton4] at hs
    obtain ⟨y, hy, -⟩ := Option.bind_eq_some_iff.1 hs
    obtain ⟨seg, h1, h2, h3⟩ := skeleton4_chain _ _ inp S p hS hy
    rw [h1, fsOf_prefix h2]
    have hl := ChainOK_length inp h3
    refine ⟨hl, fun q hq => ?_⟩
    rw [ChainOK_getD inp h3 q (by omega), Nat.zero_add]
    rcases q with _ | q
    · -- Not `fsMsgs4 S = some (0, 48) :: _ := ⟨_, rfl⟩`: the kernel took 34 s on that (R4b).
      obtain ⟨ps, hps⟩ : ∃ ps, phasesOf S = ("seed", .seed) :: ps := ⟨_, rfl⟩
      simp only [fsMsgs4, hps, msgsFrom4, phaseMsgs4, List.cons_append, List.nil_append,
        List.getD_cons_zero, qOf, ite_true]
    · rfl
  · cases h

/-- **`seq4`'s table fact**: every squeeze run after the seed is nonempty. -/
theorem shOK_seq4 : ((phasesOf seq4).drop 1).all (fun ph => shOK4 ph.2 && !isSeed4 ph.2) = true := by
  rw [seq4_eq]; decide +kernel

end Chain

end FR.Snd.R4
