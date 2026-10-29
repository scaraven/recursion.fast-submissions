-- New for `flock-recursive` (BLUEPRINT §6.2, §10 stage-review changes 16; stage S-0).
-- RET-3: the declarations revision 4 reads moved to `FRVIRSpecCore`.
import FRVIRFinals
import FRXChainFlock
import FRVIRSpecCore

/-!
# The query link: `gen`'s Fiat–Shamir queries are the extractor's `fsQ`

On any trace a run of `gen fin mode` consumes completely (`semIR … = some b`), the trace's
Fiat–Shamir entries (the entries at the FS items of `items`) form the chain of
`FR.X.fsQ vk c π`: entry `p` asks `fsQ vk c π p a_{p−1}`, where `a_{p−1}` is entry `p − 1`'s answer
(**`fsQ_gen`**). S-G2 composes it with `runLog` (S-H2-RESULT Part 13 Q2).

* `ChainOK es ms p st`: entry `i` of `es` asks the query of message `ms[i]` at position `p + i`,
  from state `st` for `i = 0` and from the previous answer after that.
* `fsOf seg its`: the entries of `seg` at the FS items of `its`.
* Per phase (`refPhase_chain`): a phase consumes one entry per item. Its FS entries are the chain
  of `FR.X.phaseMsgs n` from the state register `c.st`, and the next context's state register
  holds the last answer.
* `refPhases_chain` composes the phases. The table facts used are `phases_shapeOK` (squeezes
  nonempty, fields in range) and `phases_seed` (only phase 0 is the seed); both are checked by
  `decide` on the phase table, never on `gen`.
-/

namespace FR

open RecursionFast FR.X

variable (inp : Input)

/-! ## The chain relation -/

/-! ## The table facts -/

/-- A shape the chain lemma covers: a field in range, a nonempty run of squeezes. -/
def shapeOK : Shape → Bool
  | .absorb f _ | .uni f | .rounds f .. => decide (f ≤ nFields)
  | .squeezes k _ => decide (0 < k)
  | _ => true

def isSeed : Shape → Bool
  | .seed => true
  | _ => false

theorem phases_shapeOK : phases.all (fun p => shapeOK p.shape) = true := by decide +kernel

theorem phases_seed : (phases.take 1).map (fun p => isSeed p.shape) = [true] ∧
    (phases.drop 1).all (fun p => !isSeed p.shape) = true := by decide +kernel

/-- The messages of the phases from number `n` (`fsMsgs` for `phases` from `0`). -/
def msgsFrom : List Phase → ℕ → List (Option (ℕ × ℕ))
  | [], _ => []
  | p :: ps, n => phaseMsgs n p.shape ++ msgsFrom ps (n + 1)

theorem msgsFrom_eq (ps : List Phase) (n : ℕ) :
    ((List.range' n ps.length).zip ps).flatMap (fun np => phaseMsgs np.1 np.2.shape) =
      msgsFrom ps n := by
  induction ps generalizing n with
  | nil => rfl
  | cons p ps ih => simp [List.range'_succ, msgsFrom, ih]

theorem fsMsgs_eq : fsMsgs = msgsFrom phases 0 := by
  rw [fsMsgs, List.range_eq_range', msgsFrom_eq]

/-! ## The trace functions, one by one -/

variable (κ : Kind)

/-- A position consumes `1 + sib` entries. -/
theorem stepsT_len {i j n h so : ℕ} {cur : Digest} {tr : Trace}
    {x : List Val × Bool × Digest × Trace} (hx : stepsT κ inp i j n h so cur tr = some x) :
    ∃ seg, tr = seg ++ x.2.2.2 ∧ seg.length = n := by
  induction n generalizing h so cur tr x with
  | zero => simp [stepsT] at hx; subst hx; exact ⟨[], by simp, rfl⟩
  | succ n ih =>
    simp only [stepsT, Option.bind_eq_some_iff, Option.map_eq_some_iff] at hx
    obtain ⟨y, hy, z, hz, rfl⟩ := hx
    rcases tr with _ | ⟨e, tr⟩
    · cases hy
    have hy2 : y.2.2.2 = tr := by
      simp only [stepT] at hy; split_ifs at hy <;> cases hy <;> rfl
    obtain ⟨seg, h1, h2⟩ := ih hz
    exact ⟨e :: seg, by simp [← hy2, h1], by simp [h2]⟩

theorem posAllT_len {i co so t p : ℕ} {ad : ℕ → Digest} {w : Array K} {tr : Trace}
    {x : List Val × Bool × Trace} (hx : posAllT κ inp i co so ad w t p tr = some x) :
    ∃ seg, tr = seg ++ x.2.2 ∧ seg.length = t * (posItems i).length := by
  induction t generalizing p tr x with
  | zero => simp [posAllT] at hx; subst hx; exact ⟨[], by simp, by simp⟩
  | succ t ih =>
    simp only [posAllT, Option.bind_eq_some_iff, Option.map_eq_some_iff] at hx
    obtain ⟨y, hy, z, hz, rfl⟩ := hx
    rcases tr with _ | ⟨e, tr⟩
    · cases hy
    simp only [posT] at hy
    split_ifs at hy
    obtain ⟨u, hu, rfl⟩ := Option.map_eq_some_iff.1 hy
    obtain ⟨s₁, h1, h2⟩ := stepsT_len inp κ hu
    obtain ⟨s₂, h3, h4⟩ := ih hz
    simp only at h3
    refine ⟨e :: s₁ ++ s₂, by simp [h1, h3], ?_⟩
    simp [h2, h4, posItems, Nat.succ_mul]; omega

/-! ## One phase -/

theorem items_allFS {s : Shape} (h : ∀ i, s ≠ .queries i) : ∀ it ∈ s.items, it.isFS = true := by
  intro it hit
  cases s with
  | queries i => exact absurd rfl (h i)
  | rounds =>
    simp only [Shape.items, List.mem_flatten, List.mem_replicate] at hit
    obtain ⟨l, ⟨-, rfl⟩, hit⟩ := hit
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hit
    rcases hit with rfl | rfl <;> rfl
  | squeezes => rcases List.mem_replicate.1 hit with ⟨-, rfl⟩; rfl
  | uni =>
    simp only [Shape.items, List.mem_cons, List.not_mem_nil, or_false] at hit
    rcases hit with rfl | rfl <;> rfl
  | seed | absorb =>
    simp only [Shape.items, List.mem_cons, List.not_mem_nil, or_false] at hit
    subst hit; rfl

variable (impl : OpImpl)

/-- **One phase's Fiat–Shamir entries** are the chain of its messages from the state register,
and the next context's state register holds the last answer. -/
theorem refPhase_chain {n : ℕ} {p : Phase} {c : GCtx} {r : Array Val} {tr : Trace}
    {x : List Val × Bool × Trace} (hx : refPhase impl κ inp n p c r tr = some x)
    (hb : c.next = r.size) (hok : shapeOK p.shape = true) {q0 : ℕ}
    (hq : isSeed p.shape = true ↔ q0 = 0) (hst : isSeed p.shape = true ∨ c.st < r.size) :
    ∃ seg, tr = seg ++ x.2.2 ∧ seg.length = p.shape.items.length ∧
      ChainOK inp (fsOf seg p.shape.items) (phaseMsgs n p.shape) q0 (rd r c.st).toD ∧
      (rd (r ++ x.1.toArray) (genPhase n p c).2.st).toD =
        lastAns (fsOf seg p.shape.items) (rd r c.st).toD := by
  obtain ⟨name, sh⟩ := p
  obtain ⟨b, st, u, pa, fr, pt, outs⟩ := c
  simp only at hb hok hq hst ⊢; subst hb
  cases sh with
  | seed =>
    simp only [isSeed, true_iff] at hq; subst hq
    simp only [refPhase] at hx
    rcases tr with _ | ⟨⟨q, a⟩, tr⟩
    · cases hx
    simp only [seedT] at hx
    split_ifs at hx with hq
    cases hx
    refine ⟨[(q, a)], rfl, rfl, ?_, ?_⟩
    · rw [fsOf_all (items_allFS (by simp)) rfl]
      simp only [phaseMsgs, ChainOK, qOf, ite_true, and_true, hq]
      rw [absOff, fieldOffA_getD (by decide)]; rfl
    · rw [fsOf_all (items_allFS (by simp)) rfl]
      simp only [genPhase]
      rw [rd_app _ _ 1]; rfl
  | absorb f len =>
    simp only [isSeed, false_iff, Bool.false_eq_true, false_or] at hq hst
    simp only [shapeOK, decide_eq_true_eq] at hok
    simp only [refPhase] at hx
    obtain ⟨⟨a, tr'⟩, hans, rfl⟩ := Option.map_eq_some_iff.1 hx
    rcases tr with _ | ⟨⟨q, a'⟩, tr⟩
    · cases hans
    simp only [ans1] at hans
    split_ifs at hans with hqq
    cases hans
    refine ⟨[(q, a)], ?_, rfl, ?_, ?_⟩
    · split_ifs <;> rfl
    · rw [fsOf_all (items_allFS (by simp)) rfl]
      simp only [phaseMsgs, ChainOK, qOf, if_neg hq, and_true, hqq]
      rw [msgAt, absOff, fieldOffA_getD hok]
    · rw [fsOf_all (items_allFS (by simp)) rfl]
      simp only [genPhase]
      split_ifs <;> (rw [rd_app _ _ 1]; rfl)
  | squeezes k ch =>
    simp only [isSeed, false_iff, Bool.false_eq_true, false_or] at hq hst
    simp only [shapeOK, decide_eq_true_eq] at hok
    simp only [refPhase] at hx
    obtain ⟨y, hy, rfl⟩ := Option.map_eq_some_iff.1 hx
    obtain ⟨seg, h1, h2, h3, h4⟩ := sqzT_chain inp hy q0
    have hne : y.1 ≠ [] := by
      rw [← h4]; intro h; rw [List.map_eq_nil_iff] at h; subst h; simp at h2; omega
    have hk : y.1.length = k := by rw [← h4, List.length_map, h2]
    have hfs := fsOf_all (seg := seg) (items_allFS (s := .squeezes k ch) (by simp))
      (by simp [Shape.items, h2])
    refine ⟨seg, ?_, by simp [Shape.items, h2], ?_, ?_⟩
    · cases ch <;> exact h1
    · rw [hfs]; exact h3
    · rw [hfs, lastAns_map h4]
      cases ch <;> simp only [genPhase]
      · rw [show r.size + 3 * k - 3 = r.size + (3 * y.1.length - 3) by omega, rd_app,
          getD_last_coords hne]; exact getLastD_ne hne _ _
      · rw [show r.size + k - 1 = r.size + (y.1.length - 1) by omega, rd_app, getD_last_map hne]
        exact getLastD_ne hne _ _
      · rw [show r.size + k - 1 = r.size + (y.1.length - 1) by omega, rd_app,
          ← List.append_nil (y.1.map Val.d), getD_last_map hne]; exact getLastD_ne hne _ _
  | uni f =>
    simp only [isSeed, false_iff, Bool.false_eq_true, false_or] at hq hst
    simp only [shapeOK, decide_eq_true_eq] at hok
    simp only [refPhase] at hx
    rcases tr with _ | ⟨⟨q₁, a₁⟩, _ | ⟨⟨q₂, a₂⟩, tr⟩⟩
    · cases hx
    · cases hx
    simp only at hx
    split_ifs at hx with hqq
    cases hx
    refine ⟨[(q₁, a₁), (q₂, a₂)], rfl, rfl, ?_, ?_⟩
    · rw [fsOf_all (items_allFS (by simp)) rfl]
      simp only [phaseMsgs, ChainOK, qOf, if_neg hq, and_true, hqq.1, hqq.2]
      rw [msgAt, absOff, fieldOffA_getD hok]
    · rw [fsOf_all (items_allFS (by simp)) rfl]
      simp only [genPhase]
      rw [rd_app _ _ 2]; simp [uniVals, lastAns, Val.toD]
  | rounds f k deg inK real =>
    simp only [isSeed, false_iff, Bool.false_eq_true, false_or] at hq hst
    simp only [shapeOK, decide_eq_true_eq] at hok
    simp only [refPhase] at hx
    obtain ⟨y, hy, rfl⟩ := Option.map_eq_some_iff.1 hx
    obtain ⟨seg, h1, h2, h3, h4⟩ := roundsT_chain inp hy hq
    have hfs := fsOf_all (seg := seg) (items_allFS (s := .rounds f k deg inK real) (by simp))
      (by simp [Shape.items, h2, Nat.mul_comm])
    refine ⟨seg, h1, by simp [Shape.items, h2, Nat.mul_comm], ?_, ?_⟩
    · rw [hfs, phaseMsgs, ← fieldOffA_getD hok]
      simpa [roundMsgs, List.range_eq_range', Nat.add_assoc] using h3
    · rw [hfs, h4]
      have hiv := initVals_length inp (initClaim name) f (phaseOff n f) inK
      generalize initVals inp (initClaim name) f (phaseOff n f) inK = iv at hiv ⊢
      simp only [genPhase]
      generalize initClaim name = ic at hiv ⊢
      cases ic <;> cases inK <;>
        simp only [initOps, Init.width, ite_true, ite_false, Bool.false_eq_true] at hiv ⊢ <;>
        (split_ifs with hk0
         · rw [rd_append_left hst]
         · rw [show ∀ w m : ℕ, r.size + m + w * k - w + 2 = r.size + (m + (w * k - w + 2)) from
              fun w m => by have := Nat.le_mul_of_pos_right w (Nat.pos_of_ne_zero hk0); omega,
            rd_app, ← hiv, getD_app])
  | queries i =>
    simp only [isSeed, false_iff, Bool.false_eq_true, false_or] at hq hst
    simp only [refPhase] at hx
    obtain ⟨y, hy, rfl⟩ := Option.map_eq_some_iff.1 hx
    obtain ⟨seg, h1, h2⟩ := posAllT_len inp κ hy
    have hfs : fsOf seg (Shape.queries i).items = [] := fsOf_none fun it hit => by
      simp only [Shape.items, List.mem_flatten, List.mem_replicate] at hit
      obtain ⟨l, ⟨-, rfl⟩, hit⟩ := hit
      simp only [posItems, List.mem_cons, List.mem_map] at hit
      rcases hit with rfl | ⟨_, -, rfl⟩ <;> rfl
    refine ⟨seg, h1, by simp [Shape.items, h2], ?_, ?_⟩
    · rw [hfs]; simp [phaseMsgs, ChainOK]
    · rw [hfs]; simp only [genPhase]; rw [rd_append_left hst]; rfl

/-! ## The phases, the skeleton, `gen` -/

/-- **A run of non-seed phases**: its Fiat–Shamir entries are the chain of `msgsFrom`. -/
theorem refPhases_chain : ∀ (ps : List Phase) (n : ℕ) (c : GCtx) (r : Array Val) (tr : Trace)
    (y : List Val × List Bool × Trace) (q0 : ℕ), refPhases impl κ inp ps n c r tr = some y →
    c.next = r.size → CtxOk c r → q0 ≠ 0 →
    ps.all (fun p => shapeOK p.shape && !isSeed p.shape) = true →
    ∃ seg, tr = seg ++ y.2.2 ∧ seg.length = (ps.flatMap fun p => p.shape.items).length ∧
      ChainOK inp (fsOf seg (ps.flatMap fun p => p.shape.items)) (msgsFrom ps n) q0 (rd r c.st).toD
  | [], n, c, r, tr, y, q0, h, _, _, _, _ => by
    simp [refPhases] at h; subst h; exact ⟨[], by simp, rfl, by simp [fsOf, msgsFrom, ChainOK]⟩
  | p :: ps, n, c, r, tr, y, q0, h, hb, hc, hq, ha => by
    simp only [List.all_cons, Bool.and_eq_true, Bool.not_eq_true'] at ha
    obtain ⟨⟨hok, hns⟩, ha⟩ := ha
    simp only [refPhases, Option.bind_eq_some_iff, Option.map_eq_some_iff] at h
    obtain ⟨x, hx, y', hy', rfl⟩ := h
    obtain ⟨s₁, h1, h2, h3, h4⟩ := refPhase_chain inp κ impl hx hb hok (q0 := q0)
      (by simp [hns, hq]) (.inr hc.1)
    obtain ⟨hn, hc', -⟩ := genPhase_ctx impl κ inp n p c r tr x hb (.inr hc) hx
    have hl := ChainOK_length inp h3
    obtain ⟨s₂, h5, h6, h7⟩ := refPhases_chain ps (n + 1) _ _ _ y' (q0 + (fsOf s₁ p.shape.items).length)
      hy' hn hc' (by omega) ha
    refine ⟨s₁ ++ s₂, by rw [h1, h5, List.append_assoc], by simp [h2, h6], ?_⟩
    rw [List.flatMap_cons, fsOf_append h2, msgsFrom, ChainOK_append inp hl]
    exact ⟨h3, by rw [← h4]; exact h7⟩

/-- **The skeleton**: its Fiat–Shamir entries are the chain of `fsMsgs` from position `0`. -/
theorem skeleton_chain {tr : Trace} {y : List Val × List Bool × Trace}
    (h : refPhases impl κ inp phases 0 ctx₀ #[] tr = some y) :
    ∃ seg, tr = seg ++ y.2.2 ∧ seg.length = items.length ∧
      ChainOK inp (fsOf seg items) fsMsgs 0 (rd #[] 0).toD := by
  obtain ⟨h0, hrest⟩ := phases_seed
  have hall := phases_shapeOK
  rw [fsMsgs_eq, items]
  generalize phases = ps at h h0 hrest hall
  rcases ps with _ | ⟨p, ps⟩
  · simp at h0
  simp only [List.take_succ_cons, List.take_zero, List.map_cons, List.map_nil, List.cons.injEq,
    and_true] at h0
  simp only [List.drop_succ_cons, List.drop_zero] at hrest
  simp only [List.all_cons, Bool.and_eq_true] at hall
  have hseed : p.shape = .seed := by revert h0; cases p.shape <;> simp [isSeed]
  simp only [refPhases, Option.bind_eq_some_iff, Option.map_eq_some_iff] at h
  obtain ⟨x, hx, y', hy', rfl⟩ := h
  obtain ⟨s₁, h1, h2, h3, h4⟩ := refPhase_chain inp κ impl hx rfl hall.1 (q0 := 0)
    (by simp [h0]) (.inl h0)
  obtain ⟨hn, hc', -⟩ := genPhase_ctx impl κ inp 0 p ctx₀ #[] tr x rfl
    (.inl ⟨hseed, by simp [CtxOk, ctx₀]⟩) hx
  have hl := ChainOK_length inp h3
  have hs1 : (fsOf s₁ p.shape.items).length = 1 := by
    rw [hl, hseed]; rfl
  obtain ⟨s₂, h5, h6, h7⟩ := refPhases_chain inp κ impl ps 1 _ _ _ y' 1 hy' hn hc' (by omega)
    (by simpa [List.all_eq_true, hall.2] using fun q hq => ⟨List.all_eq_true.1 hall.2 q hq,
      by simpa using List.all_eq_true.1 hrest q hq⟩)
  refine ⟨s₁ ++ s₂, by rw [h1, h5, List.append_assoc], by simp [h2, h6], ?_⟩
  rw [List.flatMap_cons, fsOf_append h2, msgsFrom, ChainOK_append inp hl]
  refine ⟨h3, ?_⟩
  rw [hs1, Nat.zero_add, show rd #[] 0 = rd #[] ctx₀.st from rfl, ← h4]; exact h7

/-- **The query link** (stage-review changes 16; S-H2-RESULT Part 13 Q2): on a trace that a run of
`gen fin mode` consumes completely, the Fiat–Shamir entries (the entries at `items`' FS items) are
468 (revision 3.13), and entry `p` asks `fsQ vk c π p` of entry `p − 1`'s answer. -/
theorem fsQ_gen (fin : Finals) (mode : Mode) {es : Trace} {b : Bool}
    (h : semIR impl (gen fin mode) inp es = some b) :
    (fsOf es items).length = 468 ∧ ∀ p < 468, ((fsOf es items).getD p default).1 =
      fsQ inp.vk inp.c inp.π p ((fsOf es items).getD (p - 1) default).2 := by
  unfold semIR at h
  split at h
  · next s hs =>
    rw [show (gen fin mode).ops = skeleton.1 ++ (fin.ops skeleton.2.outs skeleton.2.next ++ [.accept])
      by simp [gen, genWith], St.init, exec_skeleton] at hs
    obtain ⟨y, hy, -⟩ := Option.bind_eq_some_iff.1 hs
    obtain ⟨seg, h1, h2, h3⟩ := skeleton_chain inp _ impl hy
    rw [h1, fsOf_prefix h2]
    have hl := ChainOK_length inp h3
    rw [fsMsgs_length] at hl
    refine ⟨hl, fun p hp => ?_⟩
    rw [ChainOK_getD inp h3 p (by omega), Nat.zero_add]
    unfold fsQ qOf
    rcases p with _ | p
    · rw [fsMsgs_ctl.1]; rfl
    · rfl
  · cases h

end FR
