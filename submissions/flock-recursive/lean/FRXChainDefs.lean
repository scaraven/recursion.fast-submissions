-- New for `flock-recursive` (BLUEPRINT §6.2, §10 changes 14: the fold challenges; stage S-H2,
-- track L-ext).
import FRXReadDefs

/-!
# The Fiat–Shamir chain replayed off the log: the pure half

The folds of §6.2 step 4 need P1.i's challenges, the answers of the verifier's Fiat–Shamir chain.
`runLog` answers each query by the **first** entry of the log with exactly that query
(`OProg.runLog`, `List.find?`), and the chain's query at position `p` is built from the answer at
`p − 1` (A.2: `"FRABS000" ‖ st ‖ msg`, `"FRSQZ000" ‖ st`). So the chain's answers are

* `fmAns T st₀ L p`: the first-match chain, for any target family `T p st` (the query at position
  `p` when the previous answer is `st`; `T 0` is the seed).

The extractor does not sort the log by query (a merge sort whose key is a whole query costs a
query's length per comparison, over the linear fuel). It **scans the log once, in order**, with the
next target in hand (`scanC`): an entry whose query is the target records its answer and moves to
the next target.

* **`scanC_fm`**: on a log with no state hit (`FRLog.StateHit`, a conjunct of `Bad`), the scan's
  answers are the first-match chain's, at every position below the target count. A query that
  carries the state `a_{p−1}` cannot come before the entry that answered `a_{p−1}`: that would be
  a state hit. So the first entry with the target of `p` lies after the one found for `p − 1`.
-/

namespace FR.X

open RecursionFast FR.Snd

/-! ## The first-match chain and the forward scan -/

/-- **The first-match chain**: the answer at position `p` when every query is answered by the
first entry of `L` with that query (`runLog`'s reading), the query at `p` being `T p st` with `st`
the answer at `p − 1` (`st₀` for the seed). `none` from the first query `L` does not answer. -/
def fmAns (T : ℕ → Digest → ByteArray) (st₀ : Digest) (L : Log) : ℕ → Option Digest
  | 0 => (L.find? fun e => e.1 = T 0 st₀).map Prod.snd
  | p + 1 => (fmAns T st₀ L p).bind fun st => (L.find? fun e => e.1 = T (p + 1) st).map Prod.snd

/-- The scan's state: the next target's index, the current state, the answers found. -/
abbrev SS := ℕ × Digest × List Digest

/-- **One entry of the scan**: an entry whose query is the next target (of the first `N`) records
its answer, which becomes the state. -/
def scanStep (T : ℕ → Digest → ByteArray) (N : ℕ) (x : SS) (e : ByteArray × Digest) : SS :=
  if x.1 < N ∧ e.1 = T x.1 x.2.1 then (x.1 + 1, e.2, x.2.2 ++ [e.2]) else x

/-- **The forward scan** of the log for the first `N` targets. -/
def scanC (T : ℕ → Digest → ByteArray) (N : ℕ) (st₀ : Digest) (L : Log) : SS :=
  L.foldl (scanStep T N) (0, st₀, [])

theorem scanC_snoc (T : ℕ → Digest → ByteArray) (N : ℕ) (st₀ : Digest) (L : Log)
    (e : ByteArray × Digest) : scanC T N st₀ (L ++ [e]) = scanStep T N (scanC T N st₀ L) e := by
  simp [scanC, List.foldl_append]

/-- The state before position `p`. -/
def fmPrev (T : ℕ → Digest → ByteArray) (st₀ : Digest) (L : Log) : ℕ → Option Digest
  | 0 => some st₀
  | p + 1 => fmAns T st₀ L p

theorem fmAns_eq (T : ℕ → Digest → ByteArray) (st₀ : Digest) (L : Log) (p : ℕ) :
    fmAns T st₀ L p =
      (fmPrev T st₀ L p).bind fun st => (L.find? fun e => e.1 = T p st).map Prod.snd := by
  cases p <;> rfl

/-- An answer of a prefix stays an answer. -/
theorem fmAns_snoc_some (T : ℕ → Digest → ByteArray) (st₀ : Digest) (L : Log)
    (e : ByteArray × Digest) : ∀ p a, fmAns T st₀ L p = some a → fmAns T st₀ (L ++ [e]) p = some a
  | 0, a, h => by
    simp only [fmAns, Option.map_eq_some_iff] at h ⊢
    obtain ⟨y, hy, rfl⟩ := h
    exact ⟨y, by rw [List.find?_append, hy, Option.some_or], rfl⟩
  | p + 1, a, h => by
    simp only [fmAns, Option.bind_eq_some_iff, Option.map_eq_some_iff] at h ⊢
    obtain ⟨st, hst, y, hy, rfl⟩ := h
    exact ⟨st, fmAns_snoc_some T st₀ L e p st hst, y,
      by rw [List.find?_append, hy, Option.some_or], rfl⟩

/-- A broken chain stays broken. -/
theorem fmAns_none_le (T : ℕ → Digest → ByteArray) (st₀ : Digest) (L : Log) {p : ℕ}
    (h : fmAns T st₀ L p = none) : ∀ q, p ≤ q → fmAns T st₀ L q = none := by
  intro q hq
  induction q, hq using Nat.le_induction with
  | base => exact h
  | succ q _ ih => simp only [fmAns, ih, Option.bind_none]

theorem stateHit_of_snoc {L : Log} {e : ByteArray × Digest} (h : StateHit L) :
    StateHit (L ++ [e]) := by
  obtain ⟨i, j, hij, hj, hs⟩ := h
  refine ⟨i, j, hij, by simp; omega, ?_⟩
  rw [List.getElem_append_left (by omega), List.getElem_append_left hj]
  exact hs

/-- **No query carrying the last answer as its state**, on a log with no state hit. -/
theorem find?_state_none {L : Log} {e : ByteArray × Digest} (hS : ¬ StateHit (L ++ [e]))
    {q : ByteArray} (hq : stateIn q = some e.2) :
    (L ++ [e]).find? (fun y => y.1 = q) = none := by
  rw [List.find?_eq_none]
  intro y hy hyq
  obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hy
  simp only [decide_eq_true_eq] at hyq
  refine hS ⟨i, L.length, by simp at hi; omega, by simp, ?_⟩
  rw [hyq, hq, List.getElem_concat_length rfl]

/-- The scan's invariant: as many answers as targets passed, the state is the last answer, and
the answers are the first-match chain's. -/
def ScanInv (T : ℕ → Digest → ByteArray) (N : ℕ) (st₀ : Digest) (L : Log) (x : SS) : Prop :=
  x.2.2.length = x.1 ∧ x.1 ≤ N ∧ fmPrev T st₀ L x.1 = some x.2.1 ∧
    ∀ p < N, x.2.2[p]? = fmAns T st₀ L p

theorem scanInv_nil (T : ℕ → Digest → ByteArray) (N : ℕ) (st₀ : Digest) :
    ScanInv T N st₀ [] (0, st₀, []) := by
  refine ⟨rfl, Nat.zero_le _, rfl, fun p _ => ?_⟩
  rw [fmAns_none_le T st₀ [] (p := 0) (by simp [fmAns]) p (Nat.zero_le _)]
  rfl

theorem scanInv_snoc {T : ℕ → Digest → ByteArray} {N : ℕ} {st₀ : Digest} {L : Log}
    {e : ByteArray × Digest} (hT : ∀ p st, 0 < p → stateIn (T p st) = some st)
    (hS : ¬ StateHit (L ++ [e])) {x : SS} (hI : ScanInv T N st₀ L x) :
    ScanInv T N st₀ (L ++ [e]) (scanStep T N x e) := by
  obtain ⟨n, st, acc⟩ := x
  obtain ⟨hlen, hnN, hprev, hacc⟩ := hI
  simp only at hlen hnN hprev hacc
  -- the old answers
  have hold : ∀ p < n, fmAns T st₀ (L ++ [e]) p = acc[p]? := fun p hp => by
    obtain ⟨a, ha⟩ : ∃ a, acc[p]? = some a := ⟨acc[p], List.getElem?_eq_getElem (by omega)⟩
    rw [ha]
    exact fmAns_snoc_some T st₀ L e p a (by rw [← hacc p (by omega), ha])
  have hprev' : fmPrev T st₀ (L ++ [e]) n = some st := by
    cases n with
    | zero => exact hprev
    | succ n =>
      simp only [fmPrev] at hprev ⊢
      exact fmAns_snoc_some T st₀ L e n st hprev
  -- the target `n` is not answered by `L`
  have hnone : n < N → L.find? (fun y => y.1 = T n st) = none := fun hn => by
    have h := hacc n hn
    rw [List.getElem?_eq_none (by omega), fmAns_eq, hprev, Option.bind_some] at h
    exact Option.map_eq_none_iff.mp h.symm
  have hnew : n < N → fmAns T st₀ (L ++ [e]) n =
      if e.1 = T n st then some e.2 else none := fun hn => by
    rw [fmAns_eq, hprev', Option.bind_some, List.find?_append, hnone hn, Option.none_or]
    by_cases he : e.1 = T n st <;> simp [he]
  unfold scanStep
  simp only
  by_cases hm : n < N ∧ e.1 = T n st
  · rw [if_pos hm]
    refine ⟨by simp [hlen], hm.1, ?_, fun p hp => ?_⟩
    · simp only [fmPrev]
      rw [hnew hm.1, if_pos hm.2]
    · have hn1 : fmAns T st₀ (L ++ [e]) (n + 1) = none := by
        rw [fmAns_eq]
        simp only [fmPrev]
        rw [hnew hm.1, if_pos hm.2, Option.bind_some, find?_state_none hS (hT _ _ (by omega)),
          Option.map_none]
      rcases Nat.lt_trichotomy p n with h | rfl | h
      · rw [hold p h, List.getElem?_append_left (by omega)]
      · rw [hnew hm.1, if_pos hm.2, List.getElem?_append_right (by omega), hlen, Nat.sub_self]
        rfl
      · rw [fmAns_none_le T st₀ _ hn1 p (by omega), List.getElem?_eq_none (by simp; omega)]
  · rw [if_neg hm]
    refine ⟨hlen, hnN, hprev', fun p hp => ?_⟩
    rcases Nat.lt_or_ge p n with h | h
    · rw [hold p h]
    · have hn0 : fmAns T st₀ (L ++ [e]) n = none := by
        have hn : n < N := by omega
        rw [hnew hn, if_neg fun he => hm ⟨hn, he⟩]
      rw [fmAns_none_le T st₀ _ hn0 p h, List.getElem?_eq_none (by simp only at hlen ⊢; omega)]

/-- **`scanC_fm`**: on a log with no state hit, the forward scan's answers are the first-match
chain's at every position below `N`, when every query after the seed carries its state
(`stateIn (T p st) = some st`). -/
theorem scanC_fm {T : ℕ → Digest → ByteArray} {N : ℕ} {st₀ : Digest} {L : Log}
    (hT : ∀ p st, 0 < p → stateIn (T p st) = some st) (hS : ¬ StateHit L) :
    ScanInv T N st₀ L (scanC T N st₀ L) := by
  induction L using List.reverseRecOn with
  | nil => exact scanInv_nil T N st₀
  | append_singleton L e ih =>
    rw [scanC_snoc]
    exact scanInv_snoc hT hS (ih fun h => hS (stateHit_of_snoc h))

theorem scanC_answers {T : ℕ → Digest → ByteArray} {N : ℕ} {st₀ : Digest} {L : Log}
    (hT : ∀ p st, 0 < p → stateIn (T p st) = some st) (hS : ¬ StateHit L) {p : ℕ} (hp : p < N) :
    (scanC T N st₀ L).2.2[p]? = fmAns T st₀ L p :=
  (scanC_fm hT hS).2.2.2 p hp


/-! ## Controls -/

section Controls

/-- A toy target family: the seed `q₀ = [7]`, then squeezes of the previous answer. -/
def toyT (p : ℕ) (st : Digest) : ByteArray :=
  if p = 0 then bytesOf [7] else squeezeQ st

/-- Two answers. -/
def toyD (b : UInt8) : Digest := Vector.replicate 32 b

/-- Control (positive): on an in-order log the scan and the first-match chain agree. -/
theorem scan_toy :
    (scanC toyT 2 (toyD 0) [(bytesOf [7], toyD 1), (squeezeQ (toyD 1), toyD 2)]).2.2 =
      [toyD 1, toyD 2] ∧
    fmAns toyT (toyD 0) [(bytesOf [7], toyD 1), (squeezeQ (toyD 1), toyD 2)] 1 = some (toyD 2) := by
  decide +kernel

/-- Control (negative): with a state hit (the squeeze of `d₁` logged before `d₁` is an answer),
the first-match chain answers position 1 but the forward scan does not: `scanC_fm` needs
`¬ StateHit`. -/
theorem scan_toy_hit :
    (scanC toyT 2 (toyD 0) [(squeezeQ (toyD 1), toyD 2), (bytesOf [7], toyD 1)]).2.2 = [toyD 1] ∧
    fmAns toyT (toyD 0) [(squeezeQ (toyD 1), toyD 2), (bytesOf [7], toyD 1)] 1 = some (toyD 2) := by
  decide +kernel

theorem toy_stateHit : StateHit [(squeezeQ (toyD 1), toyD 2), (bytesOf [7], toyD 1)] :=
  ⟨0, 1, by norm_num, by simp, by simp [stateIn_squeezeQ]⟩

/-- Control (negative): the first-match chain stops at the first unanswered query. -/
theorem fm_toy_none : fmAns toyT (toyD 0) [(squeezeQ (toyD 1), toyD 2)] 0 = none ∧
    fmAns toyT (toyD 0) [(squeezeQ (toyD 1), toyD 2)] 1 = none := by
  decide +kernel

end Controls

end FR.X
