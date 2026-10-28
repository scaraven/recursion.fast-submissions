-- New for `flock-recursive` (BLUEPRINT §6.2, §10 stage-review changes 16; stage S-0).
import FRVIRFinals
import FRXChainFlock

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

/-- The query of message `m` at Fiat–Shamir position `p` from state `st` (`fsQ`'s body). -/
def qOf (p : ℕ) (m : Option (ℕ × ℕ)) (st : Digest) : ByteArray :=
  match m with
  | some (o, len) => if p = 0 then seedQ inp.vk inp.c (inp.π.extract o (o + len))
      else absorbQ st (inp.π.extract o (o + len))
  | none => squeezeQ st

/-- **`ChainOK es ms p st`**: the entries ask the chain of the messages `ms` from position `p`. -/
def ChainOK : Trace → List (Option (ℕ × ℕ)) → ℕ → Digest → Prop
  | [], [], _, _ => True
  | (q, a) :: es, m :: ms, p, st => q = qOf inp p m st ∧ ChainOK es ms (p + 1) a
  | _, _, _, _ => False

/-- The last answer of `es` (`d` if empty). -/
def lastAns (es : Trace) (d : Digest) : Digest := (es.getLast?.map (·.2)).getD d

/-- The entries of `seg` at the Fiat–Shamir items of `its`. -/
def fsOf (seg : Trace) (its : List Item) : Trace := ((seg.zip its).filter (·.2.isFS)).map (·.1)

theorem ChainOK_length {es : Trace} {ms : List (Option (ℕ × ℕ))} {p : ℕ} {st : Digest}
    (h : ChainOK inp es ms p st) : es.length = ms.length := by
  induction es generalizing ms p st with
  | nil => cases ms <;> simp_all [ChainOK]
  | cons e es ih =>
    obtain ⟨q, a⟩ := e
    cases ms with
    | nil => simp [ChainOK] at h
    | cons m ms => simp only [ChainOK] at h; simp [ih h.2]

theorem lastAns_append (a b : Trace) (d : Digest) :
    lastAns (a ++ b) d = lastAns b (lastAns a d) := by
  cases b using List.reverseRecOn <;> simp [lastAns, List.getLast?_append]

theorem lastAns_cons (q : ByteArray) (a : Digest) (es : Trace) (d : Digest) :
    lastAns ((q, a) :: es) d = lastAns es a := by
  rw [show (q, a) :: es = [(q, a)] ++ es from rfl, lastAns_append]; rfl

theorem ChainOK_append {a b : Trace} {ma mb : List (Option (ℕ × ℕ))} {p : ℕ} {st : Digest}
    (hl : a.length = ma.length) :
    ChainOK inp (a ++ b) (ma ++ mb) p st ↔
      ChainOK inp a ma p st ∧ ChainOK inp b mb (p + a.length) (lastAns a st) := by
  induction a generalizing ma p st with
  | nil => cases ma <;> simp_all [ChainOK, lastAns]
  | cons e a ih =>
    obtain ⟨q, x⟩ := e
    cases ma with
    | nil => simp at hl
    | cons m ma =>
      simp only [List.cons_append, ChainOK, List.length_cons, lastAns_cons]
      rw [ih (by simpa using hl), show p + (a.length + 1) = p + 1 + a.length by omega, and_assoc]

theorem fsOf_append {s₁ s₂ : Trace} {i₁ i₂ : List Item} (h : s₁.length = i₁.length) :
    fsOf (s₁ ++ s₂) (i₁ ++ i₂) = fsOf s₁ i₁ ++ fsOf s₂ i₂ := by
  simp [fsOf, List.zip_append h]

theorem fsOf_all {seg : Trace} {its : List Item} (h : ∀ it ∈ its, it.isFS = true)
    (hl : seg.length = its.length) : fsOf seg its = seg := by
  induction seg generalizing its with
  | nil => simp [fsOf]
  | cons e seg ih =>
    cases its with
    | nil => simp at hl
    | cons it its =>
      have h1 := h it (List.mem_cons_self ..)
      have := ih (fun x hx => h x (List.mem_cons_of_mem _ hx)) (by simpa using hl)
      simp only [fsOf, List.zip_cons_cons, List.filter_cons, h1, ite_true, List.map_cons] at this ⊢
      rw [this]

theorem fsOf_none {seg : Trace} {its : List Item} (h : ∀ it ∈ its, it.isFS = false) :
    fsOf seg its = [] := by
  simp only [fsOf, List.map_eq_nil_iff, List.filter_eq_nil_iff]
  intro x hx; simp [h _ (List.of_mem_zip hx).2]

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

theorem fieldOffA_getD {f : ℕ} (hf : f ≤ nFields) : fieldOffA.getD f 0 = fieldOff f := by
  simp [fieldOffA, Array.getD_eq_getD_getElem?, List.getElem?_range (by omega : f < nFields + 1)]

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

theorem sqzT_chain {k : ℕ} {d : Digest} {tr : Trace} {y : List Digest × Trace}
    (hy : sqzT k d tr = some y) (p : ℕ) :
    ∃ seg, tr = seg ++ y.2 ∧ seg.length = k ∧ ChainOK inp seg (List.replicate k none) p d ∧
      seg.map (·.2) = y.1 := by
  induction k generalizing d tr y p with
  | zero => simp [sqzT] at hy; subst hy; exact ⟨[], by simp, rfl, by simp [ChainOK], rfl⟩
  | succ k ih =>
    rcases tr with _ | ⟨⟨q, a⟩, tr⟩
    · simp [sqzT, ans1] at hy
    simp only [sqzT, ans1, Option.bind_eq_some_iff, Option.map_eq_some_iff] at hy
    obtain ⟨z, hz, w, hw, rfl⟩ := hy
    split_ifs at hz with hq
    cases hz
    obtain ⟨seg, h1, h2, h3, h4⟩ := ih hw (p + 1)
    refine ⟨(q, a) :: seg, by simpa using h1, by simp [h2], ?_, by simp [h4]⟩
    exact ⟨by simp [qOf, hq], h3⟩

theorem lastAns_map {seg : Trace} {as : List Digest} (h : seg.map (·.2) = as) (d : Digest) :
    lastAns seg d = as.getLastD d := by
  subst h; simp [lastAns, List.getLastD_eq_getLast?, List.getLast?_map]

/-- One round's two messages from round `j` (the absorbed range at `A + o + j·rb`). -/
def roundMsgs (A o rb j k : ℕ) : List (Option (ℕ × ℕ)) :=
  (List.range' j k).flatMap fun j => [some (A + o + j * rb, rb), none]

theorem roundsT_chain {f o deg real k j : ℕ} {inK : Bool} {d : Digest} {cl : Val} {tr : Trace}
    {x : List Val × Bool × Trace} (hx : roundsT inp f o deg inK real k j d cl tr = some x)
    {p : ℕ} (hp : p ≠ 0) :
    ∃ seg, tr = seg ++ x.2.2 ∧ seg.length = 2 * k ∧
      ChainOK inp seg (roundMsgs (fieldOffA.getD f 0) o (roundBytes inK) j k) p d ∧
      lastAns seg d = if k = 0 then d else
        (x.1.getD ((if inK then 13 else roundW deg) * k - (if inK then 13 else roundW deg) + 2)
          default).toD := by
  induction k generalizing j d cl tr x p with
  | zero =>
    simp [roundsT] at hx; subst hx
    exact ⟨[], by simp, rfl, by simp [ChainOK, roundMsgs], by simp [lastAns]⟩
  | succ k ih =>
    rcases tr with _ | ⟨⟨q₁, a₁⟩, _ | ⟨⟨q₂, a₂⟩, tr⟩⟩
    · cases hx
    · cases hx
    simp only [roundsT] at hx
    by_cases hq : q₁ = absorbQ d (msgAt inp f (o + j * roundBytes inK) (roundBytes inK)) ∧
      q₂ = squeezeQ a₁
    swap; · rw [if_neg hq] at hx; cases hx
    rw [if_pos hq] at hx
    obtain ⟨y, hy, rfl⟩ := Option.map_eq_some_iff.1 hx
    obtain ⟨seg, h1, h2, h3, h4⟩ := ih hy (p := p + 2) (by omega)
    have hv := roundV_spec inp f (o + j * roundBytes inK) deg inK (decide (j < real)) a₁ a₂ cl
    simp only [roundV] at hv
    have hW3 : 3 ≤ (if inK = true then 13 else roundW deg) := by unfold roundW; split_ifs <;> omega
    generalize hW : (if inK = true then 13 else roundW deg) = W at hv h4 hW3 ⊢
    generalize hV : (if inK = true then roundKVals inp f (o + j * roundBytes inK) (decide (j < real)) a₁ a₂ cl
      else if deg = 3 then round3V inp f (o + j * roundBytes inK) (decide (j < real)) a₁ a₂ cl
      else round2Vals inp f (o + j * roundBytes inK) (decide (j < real)) a₁ a₂ cl) = V at hv ⊢
    obtain ⟨hvl, hv2, -⟩ := hv
    refine ⟨(q₁, a₁) :: (q₂, a₂) :: seg, by simp [h1], by simp [h2]; omega, ?_, ?_⟩
    · simp only [roundMsgs, List.range'_succ, List.flatMap_cons, List.cons_append, List.nil_append,
        ChainOK, qOf, if_neg hp]
      refine ⟨?_, hq.2, ?_⟩
      · rw [hq.1, msgAt]; simp [absOff, Nat.add_assoc]
      · simpa [roundMsgs, show p + 1 + 1 = p + 2 by omega] using h3
    · rw [lastAns_cons, lastAns_cons, h4, if_neg (Nat.succ_ne_zero k)]
      rcases Nat.eq_zero_or_pos k with rfl | hk
      · rw [if_pos rfl, show W * (0 + 1) - W + 2 = 2 by omega, List.getD_eq_getElem?_getD,
          List.getElem?_append_left (by omega), ← List.getD_eq_getElem?_getD, hv2]; rfl
      · have hW1 : W ≤ W * k := Nat.le_mul_of_pos_right _ hk
        have key : ∀ (A B : List Val) (m : ℕ), (A ++ B).getD (A.length + m) default = B.getD m default :=
          fun A B m => by simp [List.getD_eq_getElem?_getD, List.getElem?_append_right]
        dsimp only
        rw [if_neg (by omega),
          show W * (k + 1) - W + 2 = V.length + (W * k - W + 2) by rw [hvl, Nat.mul_succ]; omega, key]

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

theorem getD_app (A B : List Val) (m : ℕ) : (A ++ B).getD (A.length + m) default = B.getD m default := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_append_right]

theorem getD_last_coords {as : List Digest} (h : as ≠ []) (L : List Val) :
    (as.flatMap coordVals ++ L).getD (3 * as.length - 3) default = .d (as.getLastD zeroD) := by
  obtain ⟨ini, a, rfl⟩ := List.eq_nil_or_concat as |>.resolve_left h
  have := getD_app (ini.flatMap coordVals) (coordVals a ++ L) 0
  rw [coordVals_length] at this
  simpa [List.flatMap_append, List.append_assoc, Nat.mul_succ, coordVals] using this

theorem getD_last_map {as : List Digest} (h : as ≠ []) (L : List Val) :
    (as.map Val.d ++ L).getD (as.length - 1) default = .d (as.getLastD zeroD) := by
  obtain ⟨ini, a, rfl⟩ := List.eq_nil_or_concat as |>.resolve_left h
  have := getD_app (ini.map Val.d) (Val.d a :: L) 0
  simpa [List.append_assoc] using this

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

theorem getLastD_ne {as : List Digest} (h : as ≠ []) (d d' : Digest) : as.getLastD d = as.getLastD d' := by
  obtain ⟨ini, a, rfl⟩ := List.eq_nil_or_concat as |>.resolve_left h
  simp

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

theorem fsOf_prefix {seg rest : Trace} {its : List Item} (h : seg.length = its.length) :
    fsOf (seg ++ rest) its = fsOf seg its := by
  have := fsOf_append (s₂ := rest) (i₂ := []) h
  simpa [fsOf] using this

theorem ChainOK_getD : ∀ {es : Trace} {ms : List (Option (ℕ × ℕ))} {p : ℕ} {st : Digest},
    ChainOK inp es ms p st → ∀ i < es.length,
      (es.getD i default).1 = qOf inp (p + i) (ms.getD i none)
        (if i = 0 then st else (es.getD (i - 1) default).2)
  | [], _, _, _, _, i, hi => by simp at hi
  | (q, a) :: es, [], _, _, h, _, _ => by simp [ChainOK] at h
  | (q, a) :: es, m :: ms, p, st, h, i, hi => by
    simp only [ChainOK] at h
    rcases i with _ | i
    · simpa using h.1
    · have := ChainOK_getD h.2 i (by simpa using hi)
      rw [show p + (i + 1) = p + 1 + i by omega]
      simp only [List.getD_cons_succ, this, Nat.add_sub_cancel]
      rcases i with _ | i <;> simp

/-- **The query link** (stage-review changes 16; S-H2-RESULT Part 13 Q2): on a trace that a run of
`gen fin mode` consumes completely, the Fiat–Shamir entries (the entries at `items`' FS items) are
497, and entry `p` asks `fsQ vk c π p` of entry `p − 1`'s answer. -/
theorem fsQ_gen (fin : Finals) (mode : Mode) {es : Trace} {b : Bool}
    (h : semIR impl (gen fin mode) inp es = some b) :
    (fsOf es items).length = 497 ∧ ∀ p < 497, ((fsOf es items).getD p default).1 =
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
