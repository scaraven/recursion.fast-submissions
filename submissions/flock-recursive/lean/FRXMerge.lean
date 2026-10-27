-- New for `flock-recursive` (BLUEPRINT §6.5 `index_spec`; stage S-H2, track L-ext).
import FRXSortSpec

/-!
# The merge pass, as a pure state machine

`mstep` is one step of `stepIR` on abstract state (`MS`: the heads `i`, `j`, the run ends `iE`,
`jE`, the output index `k`, the destination as a function, and a ghost block start `lo`).
`Good` is the invariant; **`pass_ok`**: `n` steps from the empty state, on a source whose runs of
width `w` are strictly sorted and which is injective on `[0, n)`, leave a destination whose
blocks of width `2w` are strictly sorted and draw their values from the same source block.
No permutation is tracked (S-H2-RESULT, Part 3, steps 3–4).
-/

namespace FR.X

open RecursionFast

/-- A strict order, total on distinct words (`keyLt`'s properties, `keyLt_order`). -/
structure SOrd (lt : Word → Word → Bool) : Prop where
  irrefl : ∀ a, lt a a = false
  trans : ∀ a b c, lt a b = true → lt b c = true → lt a c = true
  total : ∀ a b, a ≠ b → lt a b = true ∨ lt b a = true

/-- The abstract state of a merge pass. -/
structure MS where
  lo : ℕ
  i : ℕ
  iE : ℕ
  j : ℕ
  jE : ℕ
  k : ℕ
  dst : ℕ → Word

/-- `f` with `v` at `k`. -/
def upd (f : ℕ → Word) (k : ℕ) (v : Word) : ℕ → Word := fun a => if a = k then v else f a

/-- A new block when both runs are used up (`blockIR`). -/
def bstart (n w : ℕ) (s : MS) : MS :=
  if s.i = s.iE ∧ s.j = s.jE then
    { s with lo := s.k, i := s.k, iE := min (s.k + w) n, j := min (s.k + w) n,
             jE := min (s.k + w + w) n }
  else s

/-- The left head goes next. -/
def takeL (lt : Word → Word → Bool) (src : ℕ → Word) (s : MS) : Bool :=
  decide (s.i < s.iE) && (!decide (s.j < s.jE) || lt (src s.i) (src s.j))

/-- **One step** (`stepIR`). -/
def mstep (lt : Word → Word → Bool) (src : ℕ → Word) (n w : ℕ) (s : MS) : MS :=
  let s := bstart n w s
  if takeL lt src s then { s with dst := upd s.dst s.k (src s.i), i := s.i + 1, k := s.k + 1 }
  else { s with dst := upd s.dst s.k (src s.j), j := s.j + 1, k := s.k + 1 }

/-- The invariant. -/
structure Good (lt : Word → Word → Bool) (src : ℕ → Word) (n w : ℕ) (s : MS) : Prop where
  ord : s.lo ≤ s.i ∧ s.i ≤ s.iE ∧ s.iE ≤ s.j ∧ s.j ≤ s.jE ∧ s.jE ≤ n
  ends : s.iE ≤ s.lo + w ∧ s.jE ≤ s.lo + 2 * w ∧ (s.j < s.jE → s.iE = s.lo + w) ∧
    (s.jE = min (s.lo + 2 * w) n ∨ s.jE = s.lo)
  algn : 2 * w ∣ s.lo
  kk : s.k + s.iE = s.i + s.j
  srt : ∀ a b, s.lo ≤ a → a < b → b < s.k → lt (s.dst a) (s.dst b) = true
  mem : ∀ a, s.lo ≤ a → a < s.k → ∃ c, s.lo ≤ c ∧ c < s.jE ∧ s.dst a = src c
  heads : ∀ a, s.lo ≤ a → a < s.k → (s.i < s.iE → lt (s.dst a) (src s.i) = true) ∧
    (s.j < s.jE → lt (s.dst a) (src s.j) = true)
  dmem : ∀ a, a < s.lo → ∃ c, c < s.lo ∧ c / (2 * w) = a / (2 * w) ∧ s.dst a = src c
  dsrt : ∀ a b, a < b → b < s.lo → a / (2 * w) = b / (2 * w) → lt (s.dst a) (s.dst b) = true

theorem div_eq_of_block {w m a : ℕ} (h1 : w * m ≤ a) (h2 : a < w * m + w) : a / w = m :=
  Nat.div_eq_of_lt_le (by rw [Nat.mul_comm]; exact h1) (by rw [Nat.succ_mul, Nat.mul_comm]; exact h2)

theorem good_init (lt : Word → Word → Bool) (src : ℕ → Word) (n w : ℕ) (d : ℕ → Word) :
    Good lt src n w ⟨0, 0, 0, 0, 0, 0, d⟩ where
  ord := by simp
  ends := by simp
  algn := dvd_zero _
  kk := rfl
  srt := fun _ _ _ _ h => absurd h (by dsimp only; omega)
  mem := fun _ _ h => absurd h (by dsimp only; omega)
  heads := fun _ _ h => absurd h (by dsimp only; omega)
  dmem := fun _ h => absurd h (by dsimp only; omega)
  dsrt := fun _ _ _ h => absurd h (by dsimp only; omega)

/-- **`bstart` keeps the invariant**, and afterwards a head is available. -/
theorem good_bstart {lt : Word → Word → Bool} {src : ℕ → Word} {n w : ℕ} (hw : 0 < w)
    {s : MS} (hg : Good lt src n w s) (hk : s.k < n) :
    Good lt src n w (bstart n w s) ∧ ((bstart n w s).i < (bstart n w s).iE ∨
      (bstart n w s).j < (bstart n w s).jE) ∧ (bstart n w s).k = s.k ∧
      (bstart n w s).dst = s.dst := by
  unfold bstart
  split
  · next h =>
    obtain ⟨hi, hj⟩ := h
    obtain ⟨o1, o2, o3, o4, o5⟩ := hg.ord
    obtain ⟨e1, e2, e3, e4⟩ := hg.ends
    have hkj : s.k = s.jE := by have := hg.kk; omega
    obtain ⟨m, hm⟩ := hg.algn
    -- the closed block ends aligned: `jE = lo + 2w` or the block is empty
    have hal : 2 * w ∣ s.k := by
      rw [hkj]
      rcases e4 with e4 | e4
      · exact ⟨m + 1, by rw [e4, Nat.min_eq_left (by omega), hm]; ring⟩
      · exact ⟨m, by rw [e4, hm]⟩
    have hblk : ∀ a, s.lo ≤ a → a < s.jE → a / (2 * w) = m := fun a h1 h2 =>
      div_eq_of_block (by omega) (by omega)
    refine ⟨⟨by simp; omega, ⟨by simp, by simp; omega, fun h => by simp at h ⊢; omega,
      Or.inl (by simp; omega)⟩, hal, by simp,
      fun a b ha hab hb => absurd hb (by simp at ha ⊢; omega),
      fun a ha hak => absurd hak (by simp at ha ⊢; omega),
      fun a ha hak => absurd hak (by simp at ha ⊢; omega), fun a ha => ?_,
      fun a b hab hb hd => ?_⟩, by simp; omega, rfl, rfl⟩
    · simp only at ha ⊢
      by_cases hlo : a < s.lo
      · obtain ⟨c, hc, hcd, hce⟩ := hg.dmem a hlo
        exact ⟨c, by omega, hcd, hce⟩
      · obtain ⟨c, hc1, hc2, hce⟩ := hg.mem a (by omega) (by omega)
        exact ⟨c, by omega, by rw [hblk c hc1 hc2, hblk a (by omega) (by omega)], hce⟩
    · simp only at hb hd ⊢
      by_cases hb' : b < s.lo
      · exact hg.dsrt a b hab hb' hd
      · by_cases ha' : s.lo ≤ a
        · exact hg.srt a b ha' hab (by omega)
        · exfalso
          have h1 : a / (2 * w) < m := by
            rw [Nat.div_lt_iff_lt_mul (by omega)]; rw [hm] at ha'; linarith
          have h2 : b / (2 * w) = m := hblk b (by omega) (by omega)
          omega
  · next h =>
    refine ⟨hg, ?_, rfl, rfl⟩
    have := hg.ord
    omega

/-- **One step keeps the invariant** and advances `k`. -/
theorem good_mstep {lt : Word → Word → Bool} {src : ℕ → Word} {n w : ℕ} (ho : SOrd lt)
    (hw : 0 < w)
    (hsrt : ∀ a b, a < b → b < n → a / w = b / w → lt (src a) (src b) = true)
    (hinj : ∀ a b, a < n → b < n → src a = src b → a = b)
    {s : MS} (hg : Good lt src n w s) (hk : s.k < n) :
    Good lt src n w (mstep lt src n w s) ∧ (mstep lt src n w s).k = s.k + 1 := by
  obtain ⟨hg', hav, hkk, -⟩ := good_bstart hw hg hk
  unfold mstep
  generalize bstart n w s = t at hg' hav hkk
  rw [← hkk] at hk ⊢
  obtain ⟨o1, o2, o3, o4, o5⟩ := hg'.ord
  obtain ⟨e1, e2, e3, e4⟩ := hg'.ends
  obtain ⟨m, hm⟩ := hg'.algn
  -- the runs: `[lo, iE)` is run `2m`, `[iE, jE)` is run `2m + 1`
  have e2m : w * (2 * m) = 2 * w * m := by ring
  have e2m1 : w * (2 * m + 1) = 2 * w * m + w := by ring
  have runL : ∀ a, t.lo ≤ a → a < t.iE → a / w = 2 * m := fun a h1 h2 =>
    div_eq_of_block (by rw [e2m]; omega) (by rw [e2m]; omega)
  have runR : ∀ a, t.j < t.jE → t.iE ≤ a → a < t.jE → a / w = 2 * m + 1 := fun a hj h1 h2 => by
    have := e3 hj
    exact div_eq_of_block (by rw [e2m1]; omega) (by rw [e2m1]; omega)
  dsimp only
  by_cases hL : takeL lt src t = true
  · rw [if_pos hL]
    simp only [takeL, Bool.and_eq_true, decide_eq_true_eq, Bool.or_eq_true, Bool.not_eq_true',
      decide_eq_false_iff_not, not_lt] at hL
    obtain ⟨hiL, hc⟩ := hL
    refine ⟨⟨by simp; omega, ⟨by simp; omega, by simp; omega, fun h => by simp at h; exact e3 h,
      by simp; exact e4⟩,
      ⟨m, hm⟩, by simp; have := hg'.kk; omega, ?_, ?_, ?_, ?_, ?_⟩, rfl⟩ <;> simp only [upd]
    · intro a b ha hab hb
      rw [if_neg (by omega)]
      by_cases hbk : b = t.k
      · rw [if_pos hbk]; exact (hg'.heads a ha (by omega)).1 hiL
      · rw [if_neg hbk]; exact hg'.srt a b ha hab (by omega)
    · intro a ha hak
      by_cases hak' : a = t.k
      · rw [if_pos hak']; exact ⟨t.i, by omega, by omega, rfl⟩
      · rw [if_neg hak']; exact hg'.mem a ha (by omega)
    · intro a ha hak
      have hiR : ∀ h : t.j < t.jE, lt (src t.i) (src t.j) = true := fun h => by
        rcases hc with hc | hc
        · omega
        · exact hc
      by_cases hak' : a = t.k
      · rw [if_pos hak']
        exact ⟨fun h => hsrt _ _ (by omega) (by omega) (by rw [runL _ (by omega) (by omega),
          runL _ (by omega) h]), hiR⟩
      · rw [if_neg hak']
        have hh := hg'.heads a ha (by omega)
        exact ⟨fun h => ho.trans _ _ _ (hh.1 hiL) (hsrt _ _ (by omega) (by omega)
          (by rw [runL _ (by omega) (by omega), runL _ (by omega) h])), hh.2⟩
    · intro a ha
      have := hg'.kk
      rw [if_neg (by omega)]; exact hg'.dmem a ha
    · intro a b hab hb hd
      have := hg'.kk
      rw [if_neg (by omega), if_neg (by omega)]; exact hg'.dsrt a b hab hb hd
  · rw [if_neg hL]
    simp only [takeL, Bool.and_eq_true, decide_eq_true_eq, Bool.or_eq_true, Bool.not_eq_true',
      decide_eq_false_iff_not, not_lt, not_and, not_or] at hL
    -- the right head is available, and below the left head when that one is
    have hjR : t.j < t.jE := by
      by_contra h
      rcases hav with h' | h'
      · exact (hL h').1 (by omega)
      · exact h h'
    have hji : t.i < t.iE → lt (src t.j) (src t.i) = true := fun h => by
      have hne : src t.i ≠ src t.j := fun he => by
        have := hinj _ _ (by omega) (by omega) he; omega
      rcases ho.total _ _ hne with h1 | h1
      · exact absurd h1 (by have := (hL h).2; simpa using this)
      · exact h1
    refine ⟨⟨by simp; omega, ⟨by simp; omega, by simp; omega, fun h => by
      simp at h; exact e3 (by omega), by simp; exact e4⟩, ⟨m, hm⟩, by simp; have := hg'.kk; omega, ?_, ?_, ?_, ?_,
      ?_⟩, rfl⟩ <;> simp only [upd]
    · intro a b ha hab hb
      rw [if_neg (by omega)]
      by_cases hbk : b = t.k
      · rw [if_pos hbk]; exact (hg'.heads a ha (by omega)).2 hjR
      · rw [if_neg hbk]; exact hg'.srt a b ha hab (by omega)
    · intro a ha hak
      by_cases hak' : a = t.k
      · rw [if_pos hak']; exact ⟨t.j, by omega, by omega, rfl⟩
      · rw [if_neg hak']; exact hg'.mem a ha (by omega)
    · intro a ha hak
      by_cases hak' : a = t.k
      · rw [if_pos hak']
        exact ⟨hji, fun h => hsrt _ _ (by omega) (by omega) (by rw [runR _ hjR (by omega) (by omega),
          runR _ hjR (by omega) h])⟩
      · rw [if_neg hak']
        have hh := hg'.heads a ha (by omega)
        exact ⟨hh.1, fun h => ho.trans _ _ _ (hh.2 hjR) (hsrt _ _ (by omega) (by omega)
          (by rw [runR _ hjR (by omega) (by omega), runR _ hjR (by omega) h]))⟩
    · intro a ha
      have := hg'.kk
      rw [if_neg (by omega)]; exact hg'.dmem a ha
    · intro a b hab hb hd
      have := hg'.kk
      rw [if_neg (by omega), if_neg (by omega)]; exact hg'.dsrt a b hab hb hd

/-! ## One pass -/

/-- `m` steps. -/
def mrun (lt : Word → Word → Bool) (src : ℕ → Word) (n w : ℕ) : ℕ → MS → MS
  | 0, s => s
  | m + 1, s => mrun lt src n w m (mstep lt src n w s)

/-- **The pass**: `n` steps from the empty state. -/
def passF (lt : Word → Word → Bool) (src : ℕ → Word) (n w : ℕ) (d : ℕ → Word) : ℕ → Word :=
  (mrun lt src n w n ⟨0, 0, 0, 0, 0, 0, d⟩).dst

theorem good_mrun {lt : Word → Word → Bool} {src : ℕ → Word} {n w : ℕ} (ho : SOrd lt)
    (hw : 0 < w) (hsrt : ∀ a b, a < b → b < n → a / w = b / w → lt (src a) (src b) = true)
    (hinj : ∀ a b, a < n → b < n → src a = src b → a = b) :
    ∀ m (s : MS), Good lt src n w s → s.k + m ≤ n →
      Good lt src n w (mrun lt src n w m s) ∧ (mrun lt src n w m s).k = s.k + m
  | 0, s, hg, _ => ⟨hg, rfl⟩
  | m + 1, s, hg, hm => by
    obtain ⟨h1, h2⟩ := good_mstep ho hw hsrt hinj hg (by omega)
    obtain ⟨h3, h4⟩ := good_mrun ho hw hsrt hinj m _ h1 (by omega)
    exact ⟨h3, by simp only [mrun]; rw [h4, h2]; omega⟩

/-- What a pass delivers. -/
structure PassOut (lt : Word → Word → Bool) (src d : ℕ → Word) (n w : ℕ) : Prop where
  mem : ∀ a < n, ∃ c < n, c / (2 * w) = a / (2 * w) ∧ d a = src c
  srt : ∀ a b, a < b → b < n → a / (2 * w) = b / (2 * w) → lt (d a) (d b) = true

/-- **`pass_ok`**: a pass on a source with strictly sorted runs of width `w`, injective on
`[0, n)`, gives strictly sorted blocks of width `2w` drawn from the same source blocks. -/
theorem pass_ok {lt : Word → Word → Bool} {src : ℕ → Word} {n w : ℕ} (ho : SOrd lt)
    (hw : 0 < w) (hsrt : ∀ a b, a < b → b < n → a / w = b / w → lt (src a) (src b) = true)
    (hinj : ∀ a b, a < n → b < n → src a = src b → a = b) (d : ℕ → Word) :
    PassOut lt src (passF lt src n w d) n w := by
  obtain ⟨hg, hk⟩ := good_mrun ho hw hsrt hinj n _ (good_init lt src n w d) (by simp)
  simp only [Nat.zero_add] at hk
  unfold passF
  generalize mrun lt src n w n ⟨0, 0, 0, 0, 0, 0, d⟩ = s at hg hk
  obtain ⟨o1, o2, o3, o4, o5⟩ := hg.ord
  obtain ⟨e1, e2, -, -⟩ := hg.ends
  obtain ⟨m, hm⟩ := hg.algn
  have hkk := hg.kk
  have hblk : ∀ a, s.lo ≤ a → a < s.jE → a / (2 * w) = m := fun a h1 h2 =>
    div_eq_of_block (by omega) (by omega)
  have hlt : ∀ a, a < s.lo → a / (2 * w) < m := fun a ha => by
    rw [Nat.div_lt_iff_lt_mul (by omega)]; rw [hm] at ha; linarith
  refine ⟨fun a ha => ?_, fun a b hab hb hd => ?_⟩
  · by_cases hlo : a < s.lo
    · obtain ⟨c, hc, hcd, hce⟩ := hg.dmem a hlo
      exact ⟨c, by omega, hcd, hce⟩
    · obtain ⟨c, hc1, hc2, hce⟩ := hg.mem a (by omega) (by omega)
      exact ⟨c, by omega, by rw [hblk c hc1 hc2, hblk a (by omega) (by omega)], hce⟩
  · by_cases hb' : b < s.lo
    · exact hg.dsrt a b hab hb' hd
    · by_cases ha' : s.lo ≤ a
      · exact hg.srt a b ha' hab (by omega)
      · exfalso
        have := hlt a (by omega)
        have := hblk b (by omega) (by omega)
        omega

/-- A pass's output is injective on `[0, n)`. -/
theorem PassOut.inj {lt : Word → Word → Bool} {src d : ℕ → Word} {n w : ℕ} (ho : SOrd lt)
    (hp : PassOut lt src d n w) (hinj : ∀ a b, a < n → b < n → src a = src b → a = b) :
    ∀ a b, a < n → b < n → d a = d b → a = b := by
  intro a b ha hb he
  by_contra hne
  have key : ∀ a b, a < b → b < n → d a = d b → False := fun a b hab hb he => by
    by_cases hd : a / (2 * w) = b / (2 * w)
    · have := hp.srt a b hab hb hd
      rw [he, ho.irrefl] at this; cases this
    · obtain ⟨c, hc, hcb, hca⟩ := hp.mem a (by omega)
      obtain ⟨c', hc', hcb', hca'⟩ := hp.mem b hb
      have := hinj c c' hc hc' (by rw [← hca, ← hca', he])
      subst this
      exact hd (hcb.symm.trans hcb')
  rcases Nat.lt_or_gt_of_ne hne with h | h
  · exact key a b h hb he
  · exact key b a h ha he.symm

/-- The runs of the next width `min(2w, n)` are sorted. -/
theorem PassOut.runs {lt : Word → Word → Bool} {src d : ℕ → Word} {n w : ℕ}
    (hp : PassOut lt src d n w) :
    ∀ a b, a < b → b < n → a / min (2 * w) n = b / min (2 * w) n → lt (d a) (d b) = true := by
  intro a b hab hb hd
  refine hp.srt a b hab hb ?_
  by_cases h : 2 * w ≤ n
  · rwa [Nat.min_eq_left h] at hd
  · rw [Nat.div_eq_of_lt (by omega), Nat.div_eq_of_lt (by omega)]

/-! ## 64 passes -/

/-- The run widths: `1`, then `min(2w, n)`. -/
def wseq (n : ℕ) : ℕ → ℕ
  | 0 => 1
  | p + 1 => min (2 * wseq n p) n

theorem wseq_eq {n : ℕ} (hn : 0 < n) : ∀ p, wseq n p = min (2 ^ p) n
  | 0 => by simp [wseq]; omega
  | p + 1 => by
    rw [wseq, wseq_eq hn p, pow_succ]
    rcases Nat.le_total (2 ^ p) n with h | h
    · rw [Nat.min_eq_left h]; omega
    · rw [Nat.min_eq_right h]; omega

/-- **The sort's correctness, pure form**: if each array is a pass of the previous one at width
`wseq n p`, starting from an array `X 0` injective on `[0, n)`, then after 64 passes the array is
strictly sorted on `[0, n)` and holds exactly the values of `X 0` there. -/
theorem passes_ok {lt : Word → Word → Bool} (ho : SOrd lt) {n : ℕ} (hn : n < 2 ^ 63)
    (X : ℕ → ℕ → Word) (ds : ℕ → ℕ → Word)
    (hX : ∀ p, ∀ a < n, X (p + 1) a = passF lt (X p) n (wseq n p) (ds p) a)
    (hinj : ∀ a b, a < n → b < n → X 0 a = X 0 b → a = b) :
    (∀ a b, a < b → b < n → lt (X 64 a) (X 64 b) = true) ∧
    (∀ a < n, ∃ c < n, X 64 a = X 0 c) ∧ (∀ c < n, ∃ a < n, X 64 a = X 0 c) := by
  rcases Nat.eq_zero_or_pos n with rfl | hn0
  · exact ⟨fun _ _ _ h => absurd h (by omega), fun _ h => absurd h (by omega),
      fun _ h => absurd h (by omega)⟩
  -- the invariant after `p` passes
  have inv : ∀ p, (∀ a b, a < n → b < n → X p a = X p b → a = b) ∧
      (∀ a b, a < b → b < n → a / wseq n p = b / wseq n p → lt (X p a) (X p b) = true) ∧
      (∀ a < n, ∃ c < n, X p a = X 0 c) := by
    intro p
    induction p with
    | zero =>
      refine ⟨hinj, fun a b hab _ hd => ?_, fun a ha => ⟨a, ha, rfl⟩⟩
      simp only [wseq, Nat.div_one] at hd; omega
    | succ p ih =>
      obtain ⟨i1, i2, i3⟩ := ih
      have hw : 0 < wseq n p := by rw [wseq_eq hn0]; have := Nat.one_le_two_pow (n := p); omega
      have hp := pass_ok ho hw i2 i1 (ds p)
      have hp' : PassOut lt (X p) (X (p + 1)) n (wseq n p) :=
        ⟨fun a ha => by rw [hX p a ha]; exact hp.mem a ha, fun a b hab hb hd => by
          rw [hX p a (by omega), hX p b hb]; exact hp.srt a b hab hb hd⟩
      refine ⟨hp'.inj ho i1, hp'.runs, fun a ha => ?_⟩
      obtain ⟨c, hc, -, hce⟩ := hp'.mem a ha
      obtain ⟨c', hc', hce'⟩ := i3 c hc
      exact ⟨c', hc', hce.trans hce'⟩
  obtain ⟨i1, i2, i3⟩ := inv 64
  have hw64 : wseq n 64 = n := by rw [wseq_eq hn0]; exact Nat.min_eq_right (by omega)
  refine ⟨fun a b hab hb => i2 a b hab hb (by
    rw [hw64, Nat.div_eq_of_lt (by omega), Nat.div_eq_of_lt hb]), i3, fun c hc => ?_⟩
  -- completeness: `n` distinct values among the `n` values of `X 0`
  classical
  have hsub : (Finset.range n).image (X 64) ⊆ (Finset.range n).image (X 0) := by
    intro v hv
    simp only [Finset.mem_image, Finset.mem_range] at hv ⊢
    obtain ⟨a, ha, rfl⟩ := hv
    obtain ⟨c, hc, he⟩ := i3 a ha
    exact ⟨c, hc, he.symm⟩
  have hcard : ((Finset.range n).image (X 0)).card ≤ ((Finset.range n).image (X 64)).card := by
    rw [Finset.card_image_of_injOn (fun a ha b hb he => i1 a b (by simpa using ha)
      (by simpa using hb) he)]
    exact (Finset.card_image_le).trans (by simp)
  have heq := Finset.eq_of_subset_of_card_le hsub hcard
  have : X 0 c ∈ (Finset.range n).image (X 64) := by
    rw [heq]; exact Finset.mem_image_of_mem _ (by simpa using hc)
  simp only [Finset.mem_image, Finset.mem_range] at this
  exact this

/-! ## `keyLt` is a strict total order -/

theorem lexW_irrefl : ∀ l : List Word, lexW l l = false
  | [] => rfl
  | a :: l => by simp [lexW, lexW_irrefl l]

theorem lexW_trans : ∀ l₁ l₂ l₃ : List Word, lexW l₁ l₂ = true → lexW l₂ l₃ = true →
    lexW l₁ l₃ = true
  | a :: l₁, b :: l₂, c :: l₃, h1, h2 => by
    simp only [lexW, Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq] at h1 h2 ⊢
    rcases h1 with h1 | ⟨rfl, h1⟩ <;> rcases h2 with h2 | ⟨rfl, h2⟩
    · left; rw [BitVec.lt_def] at *; omega
    · exact .inl h1
    · exact .inl h2
    · exact .inr ⟨rfl, lexW_trans l₁ l₂ l₃ h1 h2⟩
  | [], _, _, h, _ => by simp [lexW] at h
  | _ :: _, [], _, h, _ => by simp [lexW] at h
  | _ :: _, _ :: _, [], _, h => by simp [lexW] at h

theorem lexW_total : ∀ l₁ l₂ : List Word, l₁.length = l₂.length → l₁ ≠ l₂ →
    lexW l₁ l₂ = true ∨ lexW l₂ l₁ = true
  | [], [], _, h => absurd rfl h
  | a :: l₁, b :: l₂, hl, h => by
    simp only [lexW, Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq]
    by_cases hab : a = b
    · subst hab
      rcases lexW_total l₁ l₂ (by simpa using hl) (fun e => h (by rw [e])) with h' | h'
      · exact .inl (.inr ⟨rfl, h'⟩)
      · exact .inr (.inr ⟨rfl, h'⟩)
    · have hne : a.toNat ≠ b.toNat := fun e => hab (BitVec.eq_of_toNat_eq e)
      rcases Nat.lt_or_gt_of_ne hne with h' | h'
      · exact .inl (.inl (BitVec.lt_def.mpr h'))
      · exact .inr (.inl (BitVec.lt_def.mpr h'))
  | [], _ :: _, hl, _ => by simp at hl
  | _ :: _, [], hl, _ => by simp at hl

/-- **`keyLt I` is a strict total order** (the position is the key's last word). -/
theorem keyLt_order (I : Array Word) : SOrd (keyLt I) where
  irrefl := fun a => lexW_irrefl _
  trans := fun a b c => lexW_trans _ _ _
  total := fun a b hab => lexW_total _ _ (by simp [keyW]) (fun e => hab (by
    simp only [keyW, List.cons.injEq] at e; exact e.2.2.2.2.1))

end FR.X
