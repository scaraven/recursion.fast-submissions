-- G6: this module also holds the former modules `FRSoundness4R4Chain`, `FRSoundness4R4Run`, `FRSoundness4R4At`, `FRSoundness4R4Outs` (one section each, in import order).
import FRSoundness4R4Ref
import FRSoundness4Pos
import FRSoundness4P4aSeg
import FRXChainFlock
import FRXSeed
import FRNodeCircuit4

section G6_FRSoundness4R4Chain

-- New for `flock-recursive` (BLUEPRINT revision 4.1, §6.2, A.4; stage R4).

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

end G6_FRSoundness4R4Chain

section G6_FRSoundness4R4Run

-- New for `flock-recursive` (BLUEPRINT revision 4.1, §5.4, A.9, A.10; stage R4).
-- RET-2: import re-pointed at Core: `FRSoundnessFrRun` → `FRSoundnessCoreAcc`.

/-!
# An accepted `gen4` run: its chain (`runLog_chain4`) and its register files (`accept_chain4`)

* **The message table of `seq4`** (certificates): 486 messages (`fsMsgs4_len`), whose item kinds are
  `fsItems4` (`fsMsgs4_items`) and which fit in a proof of `piSizeOf seq4` bytes (`fsMsgs4_fit`).
* **`matches_fsQ4`**: the 486 Fiat–Shamir entries of an accepted run match `fsItems4` (`G.Matches`
  at `fsSeq4`) and are linked; **`runLog_chain4`**: an accepted run on a log without bad events
  has a chain `j` (`G.IsChain L j`) whose entries are the run's Fiat–Shamir entries.
* **`relocFin R fin`**: a `Finals` with every field's ops relocated to `R`'s format; its ops are
  `fin`'s relocated (`relocFin_ops`). Revision 4.4.1: `finOps4 P` is the relocated fields, then the
  cap check as one more field (`capF`, `finOps4_eq`: `opsOfFields finRS (rest ++ [capF])`).
* **`accept_chain4`** (3.x's `accept_chain`): on an accepted run of `gen4 S p (opsOfFields rs fs)`,
  every phase passes, the skeleton's registers are `R₀`, `finRS` runs from `R₀` to `L₀`, and field
  `k` of the rest runs from `Rs k`, with `Rs 0 = R₀ ++ L₀` and `Rs (k + 1) = Rs k ++ L_k`.
-/

namespace FR.Snd.R4
open RecursionFast Rev4

/-! ## `seq4`'s message table -/

theorem fsMsgs4_len : (fsMsgs4 seq4).length = 486 := by
  rw [fsMsgs4, seq4_eq]; decide +kernel

/-- **The item kinds of `seq4`'s messages are `fsItems4`** (a linear certificate: `X.msgItem` reads
only whether the position is `0`). -/
theorem fsMsgs4_items : .seed :: (fsMsgs4 seq4).tail.map (X.msgItem 1) = fsItems4 := by
  rw [fsMsgs4, fsItems4, seq4_eq]; decide +kernel

theorem fsMsgs4_fit :
    (fsMsgs4 seq4).all (fun m => m.all fun ol => decide (ol.1 + ol.2 ≤ piSizeOf seq4)) = true := by
  rw [fsMsgs4, seq4_eq]; decide +kernel

/-- Message `0` is the seed's (for every `S`; proved without evaluating the table). -/
theorem fsMsgs4_head (S : Seq) : ∃ ms, fsMsgs4 S = some (0, 48) :: ms := by
  obtain ⟨ps, hps⟩ : ∃ ps, phasesOf S = ("seed", .seed) :: ps := ⟨_, rfl⟩
  exact ⟨_, by rw [fsMsgs4, hps, msgsFrom4]; rfl⟩

theorem msgItem_succ (q : ℕ) (m : Option (ℕ × ℕ)) : X.msgItem (q + 1) m = X.msgItem 1 m := by
  cases m <;> rfl

theorem fsItems4_getElem {q : ℕ} (hq : q < fsItems4.length) :
    fsItems4[q] = X.msgItem q ((fsMsgs4 seq4).getD q none) := by
  obtain ⟨ms, hms⟩ := fsMsgs4_head seq4
  have hl : fsItems4.length = ms.length + 1 := by rw [← fsMsgs4_items, hms]; simp
  simp only [← fsMsgs4_items, hms, List.tail_cons]
  rcases q with _ | q
  · rfl
  · rw [List.getElem_cons_succ, List.getElem_map, List.getD_cons_succ,
      List.getD_eq_getElem _ _ (by omega), msgItem_succ q]

theorem fit_getD {q o len : ℕ} (h : (fsMsgs4 seq4).getD q none = some (o, len)) :
    o + len ≤ piSizeOf seq4 := by
  have hq : q < (fsMsgs4 seq4).length := by
    by_contra hq; rw [List.getD_eq_default _ _ (by omega)] at h; cases h
  have hm := List.all_eq_true.mp fsMsgs4_fit _ (List.getElem_mem hq)
  rw [List.getD_eq_getElem _ _ hq] at h
  rw [h] at hm
  simpa using hm

/-- **The query of position `q` passes position `q`'s item check** on a proof of `piSizeOf seq4`
bytes. -/
theorem fsCheck_qOf (inp : Input) (hπ : inp.π.size = piSizeOf seq4) {q : ℕ} (hq : q < 486)
    (st : Digest) :
    fsCheck (fsItems4[q]'(by rw [fsItems4_length]; exact hq)) (qOf inp q ((fsMsgs4 seq4).getD q none) st) =
      true := by
  rw [fsItems4_getElem]
  rcases hm : (fsMsgs4 seq4).getD q none with _ | ⟨o, len⟩
  · rcases q with _ | q
    · obtain ⟨ms, hms⟩ := fsMsgs4_head seq4; rw [hms] at hm; cases hm
    · exact fsCheck_squeezeQ st
  · have hs := size_extract_of_le (π := inp.π) (o := o) (len := len) (by rw [hπ]; exact fit_getD hm)
    rcases q with _ | q
    · obtain ⟨ms, hms⟩ := fsMsgs4_head seq4
      rw [hms, List.getD_cons_zero, Option.some.injEq, Prod.mk.injEq] at hm
      obtain ⟨rfl, rfl⟩ := hm
      exact fsCheck_seedQ inp.vk inp.c _ hs
    · simp only [qOf, X.msgItem, Nat.add_one_ne_zero, ite_false]
      have := fsCheck_absorbQ st (inp.π.extract o (o + len))
      rwa [hs] at this

theorem stateIn_qOf (inp : Input) {q : ℕ} (hq : q ≠ 0) (m : Option (ℕ × ℕ)) (st : Digest) :
    stateIn (qOf inp q m st) = some st := by
  unfold qOf
  split
  · rw [if_neg hq]; exact stateIn_absorbQ st _
  · exact stateIn_squeezeQ st

/-- **The run's Fiat–Shamir entries match `fsItems4`**, and are linked. -/
theorem matches_fsQ4 (inp : Input) (hπ : inp.π.size = piSizeOf seq4) {es : Log} (hl : es.length = 486)
    (hq : ∀ q < 486, (es.getD q default).1 = qOf inp q ((fsMsgs4 seq4).getD q none) (es.getD (q - 1) default).2) :
    G.Matches es ∧ (∀ h : 0 < es.length, stateIn (es[0]'h).1 = none) ∧
      ∀ n (h : n + 1 < es.length), stateIn (es[n + 1]'h).1 = some (es[n]'(by omega)).2 := by
  have hq' : ∀ q (h : q < es.length), (es[q]'h).1 =
      qOf inp q ((fsMsgs4 seq4).getD q none) (es.getD (q - 1) default).2 :=
    fun q h => by rw [← hq q (by omega), List.getD_eq_getElem _ _ h]
  have hck : ∀ q (h : q < es.length), fsCheck (fsItems4[q]'(by rw [fsItems4_length]; omega))
      (es[q]'h).1 = true := fun q h => by rw [hq' q h]; exact fsCheck_qOf inp hπ (by omega) _
  have hlink : ∀ n (h : n + 1 < es.length), stateIn (es[n + 1]'h).1 = some (es[n]'(by omega)).2 :=
    fun n h => by
      rw [hq' _ h, stateIn_qOf inp (by omega), Nat.add_sub_cancel, List.getD_eq_getElem _ _ (by omega)]
  have h0 : ∀ h : 0 < es.length, fsCheck .seed (es[0]'h).1 = true := fun h => by
    have := hck 0 h
    rwa [fsItems4_getElem, X.msgItem] at this
  refine ⟨⟨?_, ⟨by rw [fs_eq4, hl, fsItems4_length], fun i hi => ⟨hlink i hi, hck (i + 1) hi⟩⟩⟩,
    fun h => stateIn_of_seed (h0 h), hlink⟩
  rcases es with _ | ⟨e, es⟩
  · simp at hl
  · simp only [List.head?_cons, Option.map_some]
    exact congrArg some (h0 (by simp))

/-- **`runLog_chain4`**: an accepted run of `gen4 seq4 p fin` on a log without bad events has a chain
`j` whose entries are the run's 486 Fiat–Shamir entries. -/
theorem runLog_chain4 (impl : OpImpl) (p : KindP) (fin : FinOps) {inp : Input} {L : Log}
    (hb : ¬ Bad L) (hπ : inp.π.size = piSizeOf seq4)
    (hrun : (runIR impl (gen4 seq4 p fin) inp).runLog L = some true) :
    ∃ tr : Trace, semIR impl (gen4 seq4 p fin) inp tr = some true ∧
      (∀ e ∈ tr, e ∈ L) ∧ ∃ j, G.IsChain L j ∧ entriesOf L (pathOf L j) = fsOf tr (itemsOf seq4) ∧
        (entriesOf L (pathOf L j)).length = 486 := by
  obtain ⟨tr, h1, h2⟩ := runLog_trace _ hrun
  rw [runSeq_runIR] at h1
  obtain ⟨hl, hq⟩ := fsQ_gen4 impl inp seq4 p shOK_seq4 fin h1
  rw [fsMsgs4_len] at hl hq
  obtain ⟨hm, h0, hs⟩ := matches_fsQ4 inp hπ hl hq
  have hin : ∀ e ∈ fsOf tr (itemsOf seq4), e ∈ L := fun e he => h2 e (mem_fsOf he)
  obtain ⟨j, hj, -, hp⟩ := path_of_links hb hin h0 hs 485 (by omega)
  rw [show 485 + 1 = (fsOf tr (itemsOf seq4)).length by omega, List.take_length] at hp
  exact ⟨tr, h1, h2, j, ⟨hj, hp ▸ hm⟩, hp, by rw [hp, hl]⟩

/-! ## The finals, relocated -/

/-- A field with its ops relocated to `R`'s format. -/
def relocF (R : Seq) (f : FinField) : FinField := fun fi b => ((f fi b).1.map (reloc R), (f fi b).2)

/-- **The finals with every field relocated.** -/
def relocFin (R : Seq) (fin : Finals) : Finals :=
  ⟨relocF R fin.finRS, relocF R fin.finZ, relocF R fin.finLc, relocF R fin.finSh, relocF R fin.finLr,
    relocF R fin.finE, relocF R fin.finB', fun i => relocF R (fin.finP i), relocF R fin.finPf⟩

theorem relocFin_rest (R : Seq) (fin : Finals) : (relocFin R fin).rest = fin.rest.map (relocF R) := by
  simp [relocFin, Finals.rest, List.map_append, Function.comp_def]

theorem runFields_reloc (R : Seq) (outs : Array (List Reg)) (zh : List Reg) :
    ∀ (fs : List FinField) (b : ℕ) (ex : Array (List Reg)),
      runFields outs zh (fs.map (relocF R)) b ex = (runFields outs zh fs b ex).map (reloc R)
  | [], _, _ => rfl
  | f :: fs, b, ex => by
    simp only [List.map_cons, runFields, relocF, opsOut_reloc, List.map_append]
    rw [runFields_reloc R outs zh fs]

/-- **The relocated finals' ops are the finals' ops relocated.** -/
theorem relocFin_ops (R : Seq) (fin : Finals) (outs : Array (List Reg)) (b : ℕ) :
    (relocFin R fin).ops outs b = (fin.ops outs b).map (reloc R) := by
  rw [finals_ops_eq, finals_ops_eq, relocFin_rest, List.map_append]
  have h1 := runFields_reloc R outs [] [fin.finRS] b #[]
  simp only [List.map_cons, List.map_nil] at h1
  have e : (relocFin R fin).finRS = relocF R fin.finRS := rfl
  rw [e, h1]
  simp only [relocF, opsOut_reloc]
  rw [runFields_reloc]

/-- **The cap check as a final field** (revision 4.4.1): `capChkOps`, relocated; it reads the skeleton's
outs only (not `zhat`, not the exports) and exports nothing. -/
def capF (R : Seq) : FinField := fun fi b => ((capChkOps R fi.outs b).map (reloc R), [])

/-- **The finals' ops from `finRS` and a list of fields** (`Finals.ops`'s fold, `finals_ops_eq`). -/
def opsOfFields (rs : FinField) (fs : List FinField) : FinOps := fun outs b =>
  runFields outs [] [rs] b #[] ++
    runFields outs (rs ⟨outs, [], #[]⟩ b).2 fs (b + opsOut (rs ⟨outs, [], #[]⟩ b).1) #[(rs ⟨outs, [], #[]⟩ b).2]

theorem finals_ops_fields (fin : Finals) : fin.ops = opsOfFields fin.finRS fin.rest :=
  funext fun outs => funext fun b => finals_ops_eq fin outs b

/-- A field that reads only the outs, appended to the fold. -/
theorem runFields_snoc (outs : Array (List Reg)) (zh : List Reg) (g : FinField)
    (hg : ∀ (zh zh' : List Reg) (ex ex' : Array (List Reg)) b, g ⟨outs, zh, ex⟩ b = g ⟨outs, zh', ex'⟩ b) :
    ∀ (fs : List FinField) (b : ℕ) (ex : Array (List Reg)), runFields outs zh (fs ++ [g]) b ex =
      runFields outs zh fs b ex ++ (g ⟨outs, zh, ex⟩ (b + opsOut (runFields outs zh fs b ex))).1
  | [], b, ex => by simp [runFields, opsOut]
  | f :: fs, b, ex => by
    simp only [List.cons_append, runFields, List.append_assoc]
    rw [runFields_snoc outs zh g hg fs, opsOut_append, hg zh zh _ ex, Nat.add_assoc]

/-- **Appending a field that reads only the outs** to relocated finals. -/
theorem opsOfFields_snoc (R : Seq) (fin : Finals) (g : FinField)
    (hg : ∀ outs (zh zh' : List Reg) (ex ex' : Array (List Reg)) b, g ⟨outs, zh, ex⟩ b = g ⟨outs, zh', ex'⟩ b)
    (outs : Array (List Reg)) (b : ℕ) :
    opsOfFields (relocFin R fin).finRS ((relocFin R fin).rest ++ [g]) outs b =
      (fin.ops outs b).map (reloc R) ++ (g ⟨outs, [], #[]⟩ (b + opsOut (fin.ops outs b))).1 := by
  have e1 := relocFin_ops R fin outs b
  have e2 := congrArg opsOut e1
  rw [finals_ops_eq] at e1 e2
  rw [opsOut_reloc, opsOut_append] at e2
  unfold opsOfFields
  rw [runFields_snoc outs _ g (hg outs), ← List.append_assoc, e1, hg outs _ [] _ #[], ← e2, Nat.add_assoc]
  congr 4
  simp [runFields, opsOut]

/-- **`finOps4 P`** (revision 4.4.1): the relocated finals' fields, then the cap check (`capF`). -/
theorem finOps4_eq (P : FinP) : finOps4 P =
    opsOfFields (relocFin P.S (finalsOf P)).finRS ((relocFin P.S (finalsOf P)).rest ++ [capF P.S]) := by
  funext outs b
  rw [opsOfFields_snoc P.S (finalsOf P) (capF P.S) (fun _ _ _ _ _ _ => rfl), finOps4_def]
  show List.map _ (_ ++ _) = _
  rw [List.map_append]
  rfl

theorem noAsk_relocFin (R : Seq) {fin : Finals}
    (hna : ∀ f ∈ fin.finRS :: fin.rest, ∀ fi b, (f fi b).1.filterMap Op.item? = []) :
    ∀ f ∈ (relocFin R fin).finRS :: (relocFin R fin).rest, ∀ fi b, (f fi b).1.filterMap Op.item? = [] := by
  intro f hf fi b
  rw [relocFin_rest] at hf
  obtain ⟨g, hg, rfl⟩ : ∃ g ∈ fin.finRS :: fin.rest, f = relocF R g := by
    rcases List.mem_cons.1 hf with rfl | hf
    · exact ⟨_, List.mem_cons_self .., rfl⟩
    · obtain ⟨g, hg, rfl⟩ := List.mem_map.1 hf
      exact ⟨g, List.mem_cons_of_mem _ hg, rfl⟩
  simp only [relocF, List.filterMap_map, Function.comp_def, item_reloc]
  exact hna g hg fi b

theorem noAsk_capF (R : Seq) : ∀ fi b, ((capF R) fi b).1.filterMap Op.item? = [] := by
  intro fi b
  simp only [capF, List.filterMap_map, Function.comp_def, item_reloc]
  exact noAsk_capChkOps R fi.outs b

theorem noAsk_finOps4 (P : FinP) :
    ∀ f ∈ (relocFin P.S (finalsOf P)).finRS :: ((relocFin P.S (finalsOf P)).rest ++ [capF P.S]),
      ∀ fi b, (f fi b).1.filterMap Op.item? = [] := by
  intro f hf
  have h := noAsk_relocFin P.S (noAsk_finalsOf P)
  rcases List.mem_cons.1 hf with rfl | hf
  · exact h _ (List.mem_cons_self ..)
  rcases List.mem_append.1 hf with hf | hf
  · exact h _ (List.mem_cons_of_mem _ hf)
  · rw [List.mem_singleton.1 hf]; exact noAsk_capF P.S

/-! ## `accept_chain4` -/

section Accept
variable (impl : OpImpl) (S : Seq) (p : KindP) (inp : Input)

/-- **An accepted `gen4` run, with its register files** (3.x's `accept_chain`): the skeleton's
registers `R₀ = #[] ++ y.1`; `finRS` runs from `R₀` to `L₀`; field `k` of the rest runs from
`Rs k`, `Rs 0 = R₀ ++ L₀`, `Rs (k + 1) = Rs k ++ L_k`. -/
theorem accept_chain4 (rs : FinField) (fs : List FinField) {tr : Trace}
    (hna : ∀ f ∈ rs :: fs, ∀ fi b, (f fi b).1.filterMap Op.item? = [])
    (h : semIR impl (gen4 S p (opsOfFields rs fs)) inp tr = some true) :
    ∃ y, refPhases4 impl p.tix inp S p (phasesOf S) 0 ctx0 #[] tr = some y ∧ (∀ b ∈ y.2.1, b = true) ∧
      (skeleton4 S p).2.next = (#[] ++ y.1.toArray).size ∧
      ∃ L₀, pureRun impl p.tix inp (rs ⟨(skeleton4 S p).2.outs, [], #[]⟩ (skeleton4 S p).2.next).1
          (#[] ++ y.1.toArray) [] = some (L₀, true) ∧
        ∃ Rs : ℕ → Array Val, Rs 0 = (#[] ++ y.1.toArray) ++ L₀.toArray ∧
          ∀ k (hk : k < fs.length), ∃ L, pureRun impl p.tix inp ((fs[k]'hk)
            ⟨(skeleton4 S p).2.outs, (rs ⟨(skeleton4 S p).2.outs, [], #[]⟩ (skeleton4 S p).2.next).2,
              exAt (skeleton4 S p).2.outs
                (rs ⟨(skeleton4 S p).2.outs, [], #[]⟩ (skeleton4 S p).2.next).2 fs
                ((skeleton4 S p).2.next +
                  opsOut (rs ⟨(skeleton4 S p).2.outs, [], #[]⟩ (skeleton4 S p).2.next).1)
                #[(rs ⟨(skeleton4 S p).2.outs, [], #[]⟩ (skeleton4 S p).2.next).2] k⟩
              (Rs k).size).1 (Rs k) [] = some (L, true) ∧ Rs (k + 1) = Rs k ++ L.toArray := by
  unfold semIR at h
  split at h
  · next s hs =>
    simp only [Option.some.injEq] at h
    rw [show (gen4 S p (opsOfFields rs fs)).ops = (skeleton4 S p).1 ++
        ((opsOfFields rs fs) (skeleton4 S p).2.outs (skeleton4 S p).2.next ++ [.accept]) by simp [gen4],
      show (gen4 S p (opsOfFields rs fs)).kindOn inp = p.tix from rfl, St.init, exec_skeleton4] at hs
    obtain ⟨y, hy, hs'⟩ := Option.bind_eq_some_iff.1 hs
    have hn := skeleton4_next impl p.tix inp S p hy
    rw [hn] at hs'
    simp only [opsOfFields] at hs'
    simp only [List.append_assoc] at hs'
    obtain ⟨hok, -⟩ := fields_ok impl p.tix inp (skeleton4 S p).2.outs [] [rs] _ #[] _ _ _ s []
      (fun f hf => hna f (by simp_all)) hs' h
    obtain ⟨L, hL, -, h2⟩ := field_flag impl p.tix inp
      (hna _ (List.mem_cons_self ..) _ _) (by simpa only [runFields, List.append_nil] using hs') h
    have hsz : ((#[] ++ y.1.toArray) ++ L.toArray).size = (#[] ++ y.1.toArray).size +
        opsOut (rs ⟨(skeleton4 S p).2.outs, [], #[]⟩ (#[] ++ y.1.toArray).size).1 := by
      have hl := pureRun_len impl p.tix inp _ _ [] L true hL
      simp [hl]
    rw [← hsz] at h2
    obtain ⟨Rs, h0, hrest⟩ := fields_chain impl p.tix inp (skeleton4 S p).2.outs _ fs _ _ true _ _
      s [] (fun f hf => hna f (List.mem_cons_of_mem _ hf)) h2 h
    refine ⟨y, hy, by simpa using hok, hn, L, by rw [hn]; exact hL, Rs, h0, fun k hk => ?_⟩
    obtain ⟨Lk, hp, he⟩ := hrest k hk
    rw [hsz] at hp
    rw [hn]
    exact ⟨Lk, hp, he⟩
  · cases h

end Accept

end FR.Snd.R4

end G6_FRSoundness4R4Run

section G6_FRSoundness4R4At

-- New for `flock-recursive` (BLUEPRINT revision 4.1, A.4, A.9; stage R4).

/-!
# Phase `k` of an accepted `gen4` skeleton (`phase_at4`, `SkRun4`)

3.x's `refPhases_at`/`phase_at`/`skeleton_outs` (`FRSoundnessAccSeg`) for `refPhases4`:

* **`refPhases4_at`**: a run of phases cut at phase `k`: the trace splits as `A ++ trk` (`A` one
  entry per earlier item), phase `k` runs `refPhase4` on `trk` from the generator's context
  `cAt4 S p k` and the earlier registers `M`; its values extend into the run's registers; its flag
  is one of the run's flags.
* **`phase_at4`** (`seq4`): the Fiat–Shamir entries from `phStart4 k` on are `trk`'s
  (`phStart4_eq_sum`, from `fsStarts4`'s fold).
* **`skeleton4_outs`**: the skeleton's `outs[k]` is phase `k`'s out list.
* **`SkRun4`**: the facts of an accepted run the views use (the reference run, every flag, the
  486 Fiat–Shamir entries and their queries); **`skRun4_of_accept`**.
-/

namespace FR.Snd.R4
open RecursionFast Rev4

variable (impl : OpImpl) (κ : Kind) (inp : Input) (S : Seq) (p : KindP)

/-- The items of a list of phases. -/
abbrev psItems4 (S : Seq) (ps : List (String × Sh)) : List Item := ps.flatMap fun ph => ph.2.itemsL S.lv

theorem genPhases4_take_succ (ph : String × Sh) (ps : List (String × Sh)) (n k : ℕ) (c : GCtx) :
    (genPhases4 S p ((ph :: ps).take (k + 1)) n c).2 =
      (genPhases4 S p (ps.take k) (n + 1) (genPhase4 S p n ph c).2).2 := rfl

/-- **Phase `k` of a run of phases.** -/
theorem refPhases4_at : ∀ (ps : List (String × Sh)) (n : ℕ) (c : GCtx) (r : Array Val) (tr : Trace)
    (y : List Val × List Bool × Trace), refPhases4 impl κ inp S p ps n c r tr = some y →
    c.next = r.size → StartOk4 ps c r → ps.all (fun ph => shOK4 ph.2) = true →
    ∀ k (hk : k < ps.length), ∃ (A trk : Trace) (M : List Val) (x : List Val × Bool × Trace),
      tr = A ++ trk ∧ A.length = (psItems4 S (ps.take k)).length ∧
      refPhase4 impl κ inp S p (n + k) ps[k] (genPhases4 S p (ps.take k) n c).2 (r ++ M.toArray) trk =
        some x ∧
      (genPhases4 S p (ps.take k) n c).2.next = (r ++ M.toArray).size ∧
      ((ps[k].2 = .seed ∧ CtxOk (genPhases4 S p (ps.take k) n c).2 #[default]) ∨
        CtxOk (genPhases4 S p (ps.take k) n c).2 (r ++ M.toArray)) ∧
      ExtA (r ++ (M ++ x.1).toArray) (r ++ y.1.toArray) ∧ x.2.1 ∈ y.2.1
  | [], _, _, _, _, _, _, _, _, _, k, hk => absurd hk (by simp)
  | ph :: ps, n, c, r, tr, y, h, hb, hs, ha, k, hk => by
    have hwf : (ph.2 = .seed ∧ CtxOk c #[default]) ∨ CtxOk c r := by
      rcases hs with h | ⟨q, qs, he, hq, h0⟩
      · exact .inr h
      · cases he; exact .inl ⟨hq, h0⟩
    simp only [List.all_cons, Bool.and_eq_true] at ha
    simp only [refPhases4, Option.bind_eq_some_iff, Option.map_eq_some_iff] at h
    obtain ⟨x, hx, y', hy', rfl⟩ := h
    rcases k with _ | k
    · refine ⟨[], tr, [], x, rfl, rfl, by simpa [genPhases4] using hx, by simpa [genPhases4] using hb,
        by simpa [genPhases4] using hwf, ?_, by simp⟩
      have := ExtA.app (r ++ x.1.toArray) y'.1
      simpa [app_app] using this
    · obtain ⟨h1, h2, -⟩ := genPhase4_ctx impl κ inp S p n ph c r tr x hb hwf hx
      obtain ⟨seg, hseg, hlen, -⟩ := refPhase4_chain impl κ inp S p hx hb ha.1
        (q0 := if isSeed4 ph.2 then 0 else 1) (by split <;> simp_all)
        (by rcases hwf with ⟨h, -⟩ | h
            · left; simp [h, isSeed4]
            · right; exact h.1)
      obtain ⟨A, trk, M, x', e1, e2, e3, e4, e5, e6, e7⟩ :=
        refPhases4_at ps (n + 1) _ _ _ y' hy' h1 (.inl h2) ha.2 k (by simpa using hk)
      refine ⟨seg ++ A, trk, x.1 ++ M, x', ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
      · rw [hseg, e1, List.append_assoc]
      · simp [psItems4, hlen, e2]
      · rw [genPhases4_take_succ, show n + (k + 1) = n + 1 + k by omega, ← app_app]
        simpa using e3
      · rw [genPhases4_take_succ, e4, ← app_app]
      · rw [genPhases4_take_succ, ← app_app]; simpa using e5
      · rw [← app_app, ← app_app]
        simpa [app_app, List.append_assoc] using e6
      · exact List.mem_cons_of_mem _ e7

/-- The context before phase `k` of `phasesOf S`. -/
def cAt4 (k : ℕ) : GCtx := (genPhases4 S p ((phasesOf S).take k) 0 ctx0).2

theorem psItems4_filter_length (ps : List (String × Sh)) :
    ((psItems4 S ps).filter Item.isFS).length =
      (ps.map fun ph => ((ph.2.itemsL S.lv).filter Item.isFS).length).sum := by
  induction ps with
  | nil => rfl
  | cons ph ps ih => simp [psItems4, List.filter_append, ih] at *

theorem fsStarts4_foldl (ps : List (String × Sh)) (a : ℕ) (acc : List ℕ) :
    (ps.foldl (fun (acc : ℕ × List ℕ) ph =>
      (acc.1 + ((ph.2.itemsL seq4.lv).filter Item.isFS).length, acc.2 ++ [acc.1])) (a, acc)).2 =
      acc ++ (List.range ps.length).map fun n =>
        a + ((ps.take n).map fun ph => ((ph.2.itemsL seq4.lv).filter Item.isFS).length).sum := by
  induction ps generalizing a acc with
  | nil => simp
  | cons ph ps ih =>
    rw [List.foldl_cons, ih, List.length_cons, List.range_succ_eq_map, List.map_cons,
      List.map_map]
    simp only [List.take_zero, List.map_nil, List.sum_nil, Nat.add_zero, List.append_assoc,
      List.singleton_append, Function.comp_def, List.take_succ_cons, List.map_cons, List.sum_cons,
      Nat.add_assoc]

/-- **`phStart4 k`** is the number of Fiat–Shamir items before phase `k`. -/
theorem phStart4_eq_sum {k : ℕ} (hk : k < (phasesOf seq4).length) :
    phStart4 k = (((phasesOf seq4).take k).map fun ph =>
      ((ph.2.itemsL seq4.lv).filter Item.isFS).length).sum := by
  rw [phStart4, fsStarts4, fsStarts4_foldl, List.nil_append, List.getD_eq_getElem _ _ (by simpa)]
  simp

theorem shOK_all_seq4 : (phasesOf seq4).all (fun ph => shOK4 ph.2) = true := by
  rw [seq4_eq]; decide +kernel

/-- **Phase `k` of the accepted skeleton of `gen4 seq4 p`**, with the run's Fiat–Shamir entries
from `phStart4 k` on. -/
theorem phase_at4 {tr : Trace} {y : List Val × List Bool × Trace}
    (h : refPhases4 impl κ inp seq4 p (phasesOf seq4) 0 ctx0 #[] tr = some y) {k : ℕ}
    (hk : k < (phasesOf seq4).length) :
    ∃ (trk : Trace) (M : List Val) (x : List Val × Bool × Trace),
      refPhase4 impl κ inp seq4 p k (phasesOf seq4)[k] (cAt4 seq4 p k) (#[] ++ M.toArray) trk = some x ∧
      (cAt4 seq4 p k).next = M.length ∧
      (((phasesOf seq4)[k].2 = .seed ∧ CtxOk (cAt4 seq4 p k) #[default]) ∨
        CtxOk (cAt4 seq4 p k) (#[] ++ M.toArray)) ∧
      ExtA (#[] ++ (M ++ x.1).toArray) (#[] ++ y.1.toArray) ∧ x.2.1 ∈ y.2.1 ∧
      (fsOf tr (itemsOf seq4)).drop (phStart4 k) = fsOf trk (psItems4 seq4 ((phasesOf seq4).drop k)) ∧
      ∃ A, tr = A ++ trk := by
  obtain ⟨A, trk, M, x, e1, e2, e3, e4, e5, e6, e7⟩ :=
    refPhases4_at impl κ inp seq4 p _ 0 ctx0 #[] tr y h rfl (startOk4 seq4) shOK_all_seq4 k hk
  refine ⟨trk, M, x, by simpa [cAt4] using e3, by simpa [cAt4] using e4, e5, e6, e7, ?_, A, e1⟩
  have hit : itemsOf seq4 = psItems4 seq4 ((phasesOf seq4).take k) ++
      psItems4 seq4 ((phasesOf seq4).drop k) := by
    rw [psItems4, psItems4, ← List.flatMap_append, List.take_append_drop]; rfl
  rw [e1, hit, fsOf_append e2, List.drop_left' ?_]
  rw [fsOf_length e2, psItems4_filter_length, phStart4_eq_sum hk]

/-- `genPhase4` pushes one list on `outs`. -/
theorem genPhase4_outs (n : ℕ) (ph : String × Sh) (c : GCtx) :
    (genPhase4 S p n ph c).2.outs = c.outs.push ((genPhase4 S p n ph c).2.outs.back?.getD []) := by
  obtain ⟨name, sh⟩ := ph
  cases sh with
  | absorb f len => simp only [genPhase4]; split_ifs <;> simp
  | squeezes k ch => cases ch <;> simp [genPhase4]
  | uni f => simp only [genPhase4]; split_ifs <;> simp
  | rounds f k deg inK => cases inK <;> simp [genPhase4]
  | _ => simp [genPhase4]

theorem genPhases4_prefix : ∀ (ps : List (String × Sh)) (n : ℕ) (c : GCtx) (m : ℕ), m < c.outs.size →
    (genPhases4 S p ps n c).2.outs.getD m [] = c.outs.getD m []
  | [], _, _, _, _ => rfl
  | ph :: ps, n, c, m, hm => by
    simp only [genPhases4]
    rw [genPhases4_prefix ps (n + 1) _ m (by rw [genPhase4_outs]; simp; omega), genPhase4_outs]
    simp [Array.getD_eq_getD_getElem?, Array.getElem?_push, show m ≠ c.outs.size by omega]

theorem genPhases4_outs : ∀ (ps : List (String × Sh)) (n : ℕ) (c : GCtx),
    (genPhases4 S p ps n c).2.outs.size = c.outs.size + ps.length ∧
      ∀ k (hk : k < ps.length), (genPhases4 S p ps n c).2.outs.getD (c.outs.size + k) [] =
        (genPhase4 S p (n + k) ps[k] (genPhases4 S p (ps.take k) n c).2).2.outs.back?.getD []
  | [], _, c => ⟨by simp [genPhases4], fun k hk => absurd hk (by simp)⟩
  | ph :: ps, n, c => by
    have ho := genPhase4_outs S p n ph c
    obtain ⟨ih1, ih2⟩ := genPhases4_outs ps (n + 1) (genPhase4 S p n ph c).2
    rw [ho, Array.size_push] at ih1 ih2
    refine ⟨by simp only [genPhases4, ih1, List.length_cons]; omega, fun k hk => ?_⟩
    rcases k with _ | k
    · simp only [genPhases4, List.getElem_cons_zero, List.take_zero, Nat.add_zero]
      have hpre := genPhases4_prefix S p ps (n + 1) (genPhase4 S p n ph c).2 c.outs.size
        (by rw [ho]; simp)
      rw [hpre, ho]; simp
    · have := ih2 k (by simpa using hk)
      simp only [genPhases4] at this ⊢
      rw [show c.outs.size + (k + 1) = c.outs.size + 1 + k by omega, this,
        show n + 1 + k = n + (k + 1) by omega]
      rfl

/-- **The skeleton's `outs[k]`** is phase `k`'s out list. -/
theorem skeleton4_outs {k : ℕ} (hk : k < (phasesOf S).length) :
    (skeleton4 S p).2.outs.getD k [] =
      (genPhase4 S p k (phasesOf S)[k] (cAt4 S p k)).2.outs.back?.getD [] := by
  have := (genPhases4_outs S p (phasesOf S) 0 ctx0).2 k hk
  simpa [skeleton4, ctx0, cAt4] using this

/-! ## The accepted run's facts -/

/-- **The facts of an accepted `gen4 seq4 p` run** the views use. -/
structure SkRun4 (impl : OpImpl) (p : KindP) (inp : Input) (tr : Trace)
    (y : List Val × List Bool × Trace) : Prop where
  ref : refPhases4 impl p.tix inp seq4 p (phasesOf seq4) 0 ctx0 #[] tr = some y
  flags : ∀ b ∈ y.2.1, b = true
  len : (fsOf tr (itemsOf seq4)).length = 486
  hq : ∀ q < 486, ((fsOf tr (itemsOf seq4)).getD q default).1 =
    qOf inp q ((fsMsgs4 seq4).getD q none) ((fsOf tr (itemsOf seq4)).getD (q - 1) default).2

/-- **An accepted run of `gen4 seq4 p fin.ops`** (fields asking nothing) is a `SkRun4`. -/
theorem skRun4_of_accept (fin : Finals) {tr : Trace}
    (hna : ∀ f ∈ fin.finRS :: fin.rest, ∀ fi b, (f fi b).1.filterMap Op.item? = [])
    (h : semIR impl (gen4 seq4 p fin.ops) inp tr = some true) :
    ∃ y, SkRun4 impl p inp tr y := by
  rw [finals_ops_fields] at h
  obtain ⟨y, hy, hf, -⟩ := accept_chain4 impl seq4 p inp fin.finRS fin.rest hna h
  obtain ⟨hl, hq⟩ := fsQ_gen4 impl inp seq4 p shOK_seq4 _ h
  rw [fsMsgs4_len] at hl hq
  exact ⟨y, ⟨hy, hf, hl, hq⟩⟩

/-! ## Controls -/

/-- Control (positive): before phase 0 the context is `ctx0`; after the seed the next free
register is `4` (`seedOps4`'s registers), not `0` (negative). -/
theorem cAt4_ctl : cAt4 S p 0 = ctx0 ∧ (cAt4 S p 1).next = 4 ∧ (cAt4 S p 1).next ≠ 0 := by
  have : cAt4 S p 1 = (genPhase4 S p 0 ("seed", .seed) ctx0).2 := rfl
  refine ⟨rfl, ?_, ?_⟩ <;> rw [this] <;> simp [genPhase4, ctx0, seedOps4, opsOut, Op.outs]

end FR.Snd.R4

end G6_FRSoundness4R4At

section G6_FRSoundness4R4Outs

-- New for `flock-recursive` (BLUEPRINT revision 4.1, A.4; stage R4c).

/-!
# The outs of earlier phases come before `next` (`gen4`)

3.x's `genPhase_out_lt`/`skeleton_out_lt` (`FRSoundnessAccLvl`) for `genPhase4`:

* **`genPhase4_out_lt`**: a phase's out registers are below the next free register (a rounds
  phase's first claim may be the context's `uni` register, hence the hypothesis);
* **`cAt4_succ`**, **`cAt4_next_mono`**: the generator's contexts phase by phase;
* **`cAt4_outs_lt`**: on an accepted run, every register of an earlier phase's outs is below the
  context's `next` (`OutsLt`); so **`segPt_lt`**: the segment's `segPtRegs` precede Z2 (`uni_view4`'s
  `hpt`), and **`skeleton4_out_lt`**: every register the skeleton exports is one of its registers.
-/

namespace FR.Snd.R4
open RecursionFast Rev4

variable (S : Seq) (p : KindP)

theorem opsOut_absorbOps (f o len st b : ℕ) : opsOut (absorbOps f o len st b) = 2 := rfl
theorem opsOut_flatMap (g : ℕ → List Op) (w : ℕ) (hg : ∀ k, opsOut (g k) = w) :
    ∀ l : List ℕ, opsOut (l.flatMap g) = w * l.length
  | [] => rfl
  | a :: l => by rw [List.flatMap_cons, opsOut_append, hg, opsOut_flatMap g w hg l]; simp; ring

theorem opsOut_lastOps (o b : ℕ) : opsOut (lastOps o b) = 94 := by
  simp only [lastOps, opsOut_append]
  rw [opsOut_flatMap _ 2 (fun _ => rfl), opsOut_flatMap _ 3 (fun _ => rfl)]; rfl
theorem opsOut_seedOps4 (b : ℕ) : opsOut (seedOps4 p b) = 4 := rfl

theorem opsOut_nil : opsOut [] = 0 := rfl

theorem opsOut_cons (op : Op) (l : List Op) : opsOut (op :: l) = op.outs + opsOut l := by
  simp [opsOut]

theorem opsOut_sqzCoordOps : ∀ k st b, opsOut (sqzCoordOps k st b) = 3 * k
  | 0, _, _ => rfl
  | k + 1, st, b => by
    rw [sqzCoordOps, opsOut_append, opsOut_sqzCoordOps k]; show 3 + 3 * k = _; ring

theorem opsOut_sqzOps : ∀ k st b, opsOut (sqzOps k st b) = k
  | 0, _, _ => rfl
  | k + 1, st, b => by rw [sqzOps, opsOut_cons, opsOut_sqzOps k]; simp [Op.outs]; ring

theorem opsOut_uniOps (f o st pt b : ℕ) : opsOut (uniOps f o st pt b) = 136 := by
  simp only [uniOps, opsOut_append]
  have : opsOut (uniElems f o) = 127 := by simp [uniElems, opsOut, Function.comp_def, Op.outs]
  rw [this]; rfl

theorem opsOut_roundOpsF (f o deg : ℕ) (real : KC Bool) (st claim b : ℕ) :
    opsOut (roundOpsF f o deg real st claim b) = roundW deg := by
  unfold roundOpsF roundW
  split_ifs <;> simp only [opsOut_append, opsOut_cons, Op.outs, opsOut_nil]

theorem opsOut_roundOpsK (f o : ℕ) (real : KC Bool) (st claim b : ℕ) :
    opsOut (roundOpsK f o real st claim b) = 13 := by
  simp only [roundOpsK, opsOut, List.map_cons, List.map_nil, Op.outs, List.sum_cons, List.sum_nil,
    Nat.reduceAdd]

theorem opsOut_roundsOps (f o deg : ℕ) (inK : Bool) (real : KC ℕ) :
    ∀ n j st claim b, opsOut (roundsOps f o deg inK real n j st claim b) =
      (if inK then 13 else roundW deg) * n
  | 0, _, _, _, _ => by simp [roundsOps, opsOut]
  | n + 1, j, st, claim, b => by
    simp only [roundsOps, opsOut_append, opsOut_roundsOps f o deg inK real n]
    cases inK <;> simp only [Bool.false_eq_true, ite_false, ite_true, opsOut_roundOpsF,
      opsOut_roundOpsK] <;> ring

theorem opsOut_merkleOps4 (sib i : ℕ) (j : Reg) : ∀ n h cur so b, opsOut (merkleOps4 sib i j n h cur so b) = 6 * n
  | 0, _, _, _, _ => rfl
  | n + 1, h, cur, so, b => by
    rw [merkleOps4, opsOut_append, opsOut_merkleOps4 sib i j n]; simp [opsOut, Op.outs]; try ring

theorem opsOut_posOps4 (k : KindP) (i co so capO : ℕ) (ans : List Reg) (w : Reg) (q b : ℕ) :
    opsOut (posOps4 S k i co so capO ans w q b) = posW4 S i := by
  simp only [posOps4, opsOut_append, opsOut_merkleOps4]; simp [opsOut, Op.outs, posW4]; try ring

/-- **A phase's out registers are below the next free register.** -/
theorem genPhase4_out_lt (n : ℕ) (ph : String × Sh) (c : GCtx) (hu : ph.2 = .seed ∨ c.uni < c.next) :
    ∀ x ∈ (genPhase4 S p n ph c).2.outs.back?.getD [], x < (genPhase4 S p n ph c).2.next := by
  obtain ⟨name, sh⟩ := ph
  simp only [Reg]
  cases sh with
  | seed => simp only [genPhase4, opsOut_seedOps4]; simp
  | absorb f len =>
    simp only [genPhase4]
    split_ifs <;>
    simp only [Array.back?_push, Option.getD_some, List.mem_cons, List.mem_singleton, lastOuts,
      List.mem_map, List.mem_range, opsOut_append, opsOut_absorbOps, opsOut_lastOps,
      List.not_mem_nil, or_false] <;>
    (try rintro x (rfl | rfl | ⟨k, hk, rfl⟩)) <;> (try rintro x rfl) <;> omega
  | squeezes k ch =>
    cases ch with
    | coords =>
      simp only [genPhase4, Array.back?_push, Option.getD_some, List.mem_cons, List.mem_map,
        List.mem_range, opsOut_append, opsOut_sqzCoordOps]
      rintro x (rfl | ⟨y, hy, rfl⟩)
      · simp [opsOut, Op.outs]
      · simp only [opsOut, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Op.outs]; omega
    | one =>
      simp only [genPhase4, Array.back?_push, Option.getD_some, List.mem_singleton, opsOut_append,
        opsOut_sqzOps]
      rintro x rfl; simp [opsOut, Op.outs]
    | pos i =>
      simp only [genPhase4, Array.back?_push, Option.getD_some, List.mem_map, List.mem_range,
        opsOut_sqzOps]
      rintro x ⟨y, hy, rfl⟩; omega
  | uni f =>
    simp only [genPhase4]
    split_ifs <;>
    simp only [Array.back?_push, Option.getD_some, List.mem_cons, List.mem_singleton,
      List.not_mem_nil, or_false, opsOut_cons, opsOut_uniOps] <;>
    rintro x (rfl | rfl | rfl) <;> simp [Op.outs]
  | rounds f k deg inK =>
    have hu' : c.uni < c.next := by simpa using hu
    have hR : 4 ≤ roundW deg := by unfold roundW; split <;> omega
    have key : ∀ w, 4 ≤ w → ∀ (cl b' : ℕ), cl < b' → ∀ x ∈ cl ::
        ((List.range k).map (fun j => b' + w * j + 3) ++ [if k = 0 then cl else b' + w * k - 1]),
        x < b' + w * k := by
      intro w hw cl b' hcl x hx
      simp only [List.mem_cons, List.mem_append, List.mem_map, List.mem_range, List.not_mem_nil,
        or_false] at hx
      rcases hx with rfl | ⟨j, hj, rfl⟩ | rfl
      · rcases Nat.eq_zero_or_pos k with rfl | hk <;> nlinarith
      · nlinarith
      · split <;> omega
    rcases hi : initClaim name with _ | _ | _ <;> cases inK <;>
    simp only [genPhase4, hi, initOps, Init.width, Array.back?_push, Option.getD_some, opsOut_append,
      opsOut_roundsOps, Bool.false_eq_true, ite_true, ite_false, ↓reduceIte] <;>
    intro x hx
    · have := key _ hR c.uni (c.next + 0) (by omega) x hx; simp only [opsOut] at *; omega
    · have := key 13 (by omega) c.uni (c.next + 0) (by omega) x hx; simp only [opsOut] at *; omega
    · have := key _ hR c.next (c.next + 1) (by omega) x hx
      simp only [opsOut_cons, opsOut_nil, Op.outs, Nat.reduceAdd] at this ⊢
      omega
    · have := key 13 (by omega) c.next (c.next + 1) (by omega) x hx
      simp only [opsOut_cons, opsOut_nil, Op.outs, Nat.reduceAdd] at this ⊢
      omega
    · have := key _ hR (c.next + 2) (c.next + 3) (by omega) x hx
      simp only [opsOut_cons, opsOut_nil, Op.outs, Nat.reduceAdd] at this ⊢
      omega
    · have := key 13 (by omega) (c.next + 2) (c.next + 3) (by omega) x hx
      simp only [opsOut_cons, opsOut_nil, Op.outs, Nat.reduceAdd] at this ⊢
      omega
  | queries i =>
    simp only [genPhase4, Array.back?_push, Option.getD_some, List.mem_map, List.mem_range,
      opsOut_cons, opsOut_flatMap _ _ (fun q => opsOut_posOps4 S _ _ _ _ _ _ _ _ _)]
    have : 4 ≤ posW4 S i := by unfold posW4; omega
    rintro x ⟨q, hq, rfl⟩
    rw [opsOut_append, opsOut_flatMap _ (posW4 S i) (fun q => opsOut_posOps4 S _ _ _ _ _ _ _ _ _),
      List.length_range]
    have h2 : opsOut [Op.packK c.foldR, Op.eqTableK c.next] = 2 := rfl
    rw [h2]
    nlinarith

/-! ## The generator's contexts -/

theorem genPhases4_split : ∀ (A B : List (String × Sh)) (n : ℕ) (c : GCtx),
    (genPhases4 S p (A ++ B) n c).2 = (genPhases4 S p B (n + A.length) (genPhases4 S p A n c).2).2
  | [], B, n, c => by simp [genPhases4]
  | ph :: A, B, n, c => by
    simp only [List.cons_append, genPhases4]
    rw [genPhases4_split A B (n + 1)]
    simp only [List.length_cons, Nat.add_assoc, Nat.add_comm 1]

theorem cAt4_succ {k : ℕ} (hk : k < (phasesOf S).length) :
    cAt4 S p (k + 1) = (genPhase4 S p k (phasesOf S)[k] (cAt4 S p k)).2 := by
  rw [cAt4, List.take_succ, List.getElem?_eq_getElem hk, Option.toList_some, genPhases4_split,
    List.length_take, min_eq_left hk.le, Nat.zero_add]
  rfl

theorem cAt4_next_succ {k : ℕ} (hk : k < (phasesOf S).length) :
    (cAt4 S p k).next ≤ (cAt4 S p (k + 1)).next := by
  rw [cAt4_succ S p hk, (genPhase4_next S p k _ _).1]; omega

theorem cAt4_next_mono {m : ℕ} : ∀ {k : ℕ}, m ≤ k → k ≤ (phasesOf S).length →
    (cAt4 S p m).next ≤ (cAt4 S p k).next
  | 0, h, _ => by rw [Nat.le_zero.1 h]
  | k + 1, h, hk => by
    rcases Nat.lt_or_ge m (k + 1) with hm | hm
    · exact (cAt4_next_mono (by omega) (by omega)).trans (cAt4_next_succ S p (by omega))
    · rw [show m = k + 1 by omega]

theorem cAt4_size (k : ℕ) : (cAt4 S p k).outs.size = min k (phasesOf S).length := by
  have := (genPhases4_outs S p ((phasesOf S).take k) 0 ctx0).1
  simpa [cAt4, ctx0] using this

theorem skeleton4_eq_cAt4 : (skeleton4 S p).2 = cAt4 S p (phasesOf S).length := by
  rw [cAt4, List.take_length]; rfl

/-- **An earlier phase's outs in a context are the skeleton's.** -/
theorem cAt4_outs {m n : ℕ} (hmn : m < n) (hn : n ≤ (phasesOf S).length) :
    (cAt4 S p n).outs.getD m [] = (skeleton4 S p).2.outs.getD m [] := by
  have e : (skeleton4 S p).2 = (genPhases4 S p ((phasesOf S).drop n) (0 + n) (cAt4 S p n)).2 := by
    have := genPhases4_split S p ((phasesOf S).take n) ((phasesOf S).drop n) 0 ctx0
    rw [List.take_append_drop, List.length_take, min_eq_left hn] at this
    exact this
  rw [e, genPhases4_prefix S p _ _ _ m (by rw [cAt4_size, min_eq_left hn]; exact hmn)]

/-! ## Outs before `next` -/

/-- Every register of the context's outs is below its `next`. -/
def OutsLt (c : GCtx) : Prop := ∀ m, ∀ x ∈ c.outs.getD m [], x < c.next

theorem genPhase4_outsLt (n : ℕ) (ph : String × Sh) (c : GCtx) (hc : OutsLt c)
    (hu : ph.2 = .seed ∨ c.uni < c.next) : OutsLt (genPhase4 S p n ph c).2 := by
  intro m x hx
  have hlt := genPhase4_out_lt S p n ph c hu
  have hnx := (genPhase4_next S p n ph c).1
  rw [genPhase4_outs] at hx
  simp only [Array.getD_eq_getD_getElem?, Array.getElem?_push] at hx
  split_ifs at hx
  · exact hlt x (by simpa using hx)
  · have := hc m x (by simpa [Array.getD_eq_getD_getElem?] using hx)
    exact lt_of_lt_of_le this (by rw [hnx]; exact Nat.le_add_right _ _)

/-- **On an accepted run, every context's outs precede its `next`.** -/
theorem cAt4_outsLt {impl : OpImpl} {κ : Kind} {inp : Input} {tr : Trace}
    {y : List Val × List Bool × Trace}
    (h : refPhases4 impl κ inp seq4 p (phasesOf seq4) 0 ctx0 #[] tr = some y) :
    ∀ k ≤ (phasesOf seq4).length, OutsLt (cAt4 seq4 p k)
  | 0, _ => fun m x hx => by simp [cAt4, genPhases4, ctx0, Array.getD_eq_getD_getElem?] at hx
  | k + 1, hk => by
    rw [cAt4_succ seq4 p (by omega)]
    obtain ⟨trk, M, x', hx', hb, hwf, -⟩ := phase_at4 impl κ inp p h (k := k) (by omega)
    refine genPhase4_outsLt seq4 p k _ _ (cAt4_outsLt h k (by omega)) ?_
    rcases hwf with ⟨h', -⟩ | h'
    · exact .inl h'
    · right; have := h'.2.1; simpa [hb] using this

/-- **The segment's `targetS` operand's registers precede Z2** (`uni_view4`'s `hpt`). -/
theorem segPt_lt {impl : OpImpl} {κ : Kind} {inp : Input} {tr : Trace}
    {y : List Val × List Bool × Trace}
    (h : refPhases4 impl κ inp seq4 p (phasesOf seq4) 0 ctx0 #[] tr = some y) {n : ℕ}
    (h3 : 3 < n) (hn : n ≤ (phasesOf seq4).length) :
    ∀ x ∈ segPtRegs seq4 p (cAt4 seq4 p n).outs, x < (cAt4 seq4 p n).next := by
  have hO := cAt4_outsLt p h n hn
  have hpos : 0 < (cAt4 seq4 p n).next :=
    lt_of_lt_of_le (by rw [(cAt4_ctl seq4 p).2.1]; omega) (cAt4_next_mono seq4 p (m := 1) (by omega) hn)
  intro x hx
  simp only [segPtRegs, List.mem_append, List.mem_replicate] at hx
  rcases hx with (hx | ⟨-, rfl⟩) | hx
  · exact hO 3 x (List.mem_of_mem_drop (List.mem_of_mem_take hx))
  · rw [List.getD_eq_getElem?_getD]
    rcases hq : ((cAt4 seq4 p n).outs.getD 1 [])[1]? with _ | z
    · exact hpos
    · exact hO 1 z (List.mem_of_getElem? hq)
  · exact hO 1 x (List.mem_of_mem_drop hx)

/-- **Every register the skeleton exports is one of its registers.** -/
theorem skeleton4_out_lt {impl : OpImpl} {κ : Kind} {inp : Input} {tr : Trace}
    {y : List Val × List Bool × Trace}
    (h : refPhases4 impl κ inp seq4 p (phasesOf seq4) 0 ctx0 #[] tr = some y) :
    ∀ m, ∀ x ∈ (skeleton4 seq4 p).2.outs.getD m [], x < (#[] ++ y.1.toArray).size := by
  intro m x hx
  rw [← skeleton4_next impl κ inp seq4 p h]
  rw [skeleton4_eq_cAt4] at hx ⊢
  exact cAt4_outsLt p h _ le_rfl m x hx

end FR.Snd.R4

end G6_FRSoundness4R4Outs

section G6_FRSoundness4R4Kind

-- New for `flock-recursive` (BLUEPRINT revision 4.1, B-11; stage R4c).

/-!
# The program's kind is the chain's (`kindOfC`)

On an accepted run of `gen4 seq4 p`, the seed checks `hdr`'s first 16 bytes against the kind's
constant `[p.byte, m, 0, …]` (`seedOps4`), so **π's byte 0 is `p.byte`** (`seed_byte4`); the chain's
first entry is the seed query `"FRSEED0" ‖ vk ‖ c ‖ hdr` (`SkRun4.hq`, `fsMsgs4_head`), whose byte 71
is π's byte 0; so **`kindOfC es` is the program's kind** (`kindOfC_seg4`, `kindOfC_node4`), and the
front's dimensions are the program's (`mC6_seg4`, …).
-/

namespace FR.Snd.R4
open RecursionFast Rev4

section Kind
variable {impl : OpImpl} {p : KindP} {inp : Input} {tr : Trace} {y : List Val × List Bool × Trace}

theorem byteAt_bytesOf_cons (b : UInt8) (l : List UInt8) : byteAt (bytesOf (b :: l)) 0 = b := by
  unfold byteAt bytesOf
  rw [dif_pos (by show 0 < (b :: l).toArray.size; simp)]
  rfl

/-- **The seed's check**: π's byte 0 is the kind's byte. -/
theorem seed_byte4 (h : SkRun4 impl p inp tr y) : byteAt inp.π 0 = p.byte := by
  obtain ⟨trk, M, x, hx, hb, -, -, hfl, -⟩ := phase_at4 impl p.tix inp p h.ref (k := 0) (by decide)
  have hM : M = [] := by
    have : (cAt4 seq4 p 0).next = 0 := rfl
    rw [this] at hb; exact List.eq_nil_of_length_eq_zero hb.symm
  subst hM
  have hph : (phasesOf seq4)[0] = ("seed", .seed) := rfl
  have hfx := h.flags _ hfl
  rw [hph] at hx
  simp only [refPhase4] at hx
  rcases trk with _ | ⟨⟨q, a⟩, trk⟩
  · cases hx
  · simp only at hx
    split_ifs at hx
    simp only [seedTail4, seedOps4, List.drop_succ_cons, List.drop_zero, pureRun, evalOp, absOff_zero,
      rd, Option.map_some] at hx
    rcases hx' : x with ⟨xv, xb, xt⟩
    rw [hx'] at hx hfx
    simp only [Option.some.injEq, Prod.mk.injEq] at hx
    obtain ⟨-, rfl, -⟩ := hx
    generalize hcst : bytesOf ([p.byte, p.d.m.toUInt8] ++ List.replicate 46 0) = cst at hfx
    have he : F.ofBytes (bytesAt inp.π 0 16) = F.ofBytes (bytesAt cst 0 16) := by
      revert hfx; simp [allK, Val.eqv]
    have hv := congrArg (fun v => v[0]) (Circ.ofBytes_inj he)
    simp only [bytesAt, Vector.getElem_ofFn, Nat.add_zero] at hv
    rw [hv, ← hcst, List.cons_append]
    exact byteAt_bytesOf_cons _ _

theorem kindOfC_byte4 (h : SkRun4 impl p inp tr y) (hp : p.byte ≠ 0) :
    (entAt (fsOf tr (itemsOf seq4)) 0).1.data[71]? = some p.byte := by
  have h0 := h.hq 0 (by decide)
  obtain ⟨ms, hms⟩ := fsMsgs4_head seq4
  rw [hms] at h0
  simp only [List.getD_cons_zero, qOf, ite_true] at h0
  have hb := seed_byte4 h
  rw [entAt, h0, ← Array.getElem?_toList, X.seedQ_data']
  rw [List.getElem?_append_right (by simp [tagSeed]), List.getElem?_append_right (by simp [tagSeed]),
    List.getElem?_append_right (by simp [tagSeed])]
  simp only [tagSeed, List.length_cons, List.length_nil, Vector.length_toList]
  rw [show 71 - 7 - 32 - 32 = 0 from rfl, toList_extract]
  simp only [List.drop_zero, Nat.sub_zero, Nat.zero_add]
  rw [List.getElem?_take_of_lt (by norm_num), Array.getElem?_toList]
  unfold byteAt at hb
  split_ifs at hb with hs
  · rw [Array.getElem?_eq_getElem hs]; exact congrArg some hb
  · exact absurd hb.symm hp

/-- **A segment program's chain is the segment kind's.** -/
theorem kindOfC_seg4 {σ : SegKind} (h : SkRun4 impl (.ofSeg σ) inp tr y) :
    kindOfC (fsOf tr (itemsOf seq4)) = .seg σ := by
  have hb := kindOfC_byte4 h (by cases σ <;> decide)
  unfold kindOfC
  rw [hb, Option.bind_some, show (KindP.ofSeg σ).byte = (CKind.seg σ).byte from rfl, CKind.ofByte?_byte]
  rfl

/-- **A node program's chain is the node kind's.** -/
theorem kindOfC_node4 {ν : NodeKind} (h : SkRun4 impl (.ofNode ν) inp tr y) :
    kindOfC (fsOf tr (itemsOf seq4)) = .node ν := by
  have hb := kindOfC_byte4 h (by cases ν <;> decide)
  unfold kindOfC
  rw [hb, Option.bind_some, show (KindP.ofNode ν).byte = (CKind.node ν).byte from rfl, CKind.ofByte?_byte]
  rfl

end Kind

/-! ## The front's dimensions are the program's -/

/-- Z3's real rounds `m − 6`, S2's `nb + 10`, the block bits `m − 14`, per kind. -/
theorem dims_seg4 (σ : SegKind) : (KindP.ofSeg σ).d.seq.z3 = (CKind.seg σ).m - 6 ∧
    (KindP.ofSeg σ).d.seq.s2 = (CKind.seg σ).m - 14 + 10 ∧ (KindP.ofSeg σ).d.m = (CKind.seg σ).m := by
  cases σ <;> decide

theorem dims_node4 (ν : NodeKind) : (KindP.ofNode ν).d.seq.z3 = (CKind.node ν).m - 6 ∧
    (KindP.ofNode ν).d.seq.s2 = (CKind.node ν).m - 14 + 10 ∧ (KindP.ofNode ν).d.m = (CKind.node ν).m ∧
    (KindP.ofNode ν).d.seq.lr = P4b.lrR ν ∧ (KindP.ofNode ν).d.seq.e2 = P4b.e2R ν ∧
    (KindP.ofNode ν).d.seq.e4 = P4b.ncR ν := by
  cases ν <;> decide

end FR.Snd.R4

end G6_FRSoundness4R4Kind
