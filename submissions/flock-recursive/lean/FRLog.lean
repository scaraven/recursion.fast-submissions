-- New for `flock-recursive` (BLUEPRINT §5.1, §7; stage S-G). The forest, `extCount_split` and
-- the chain lemmas follow `submissions/spartan-srom/lean/SpartanSromSoundnessLog.lean` and
-- `SpartanSromTranscript.lean` (this repository, `v4/flock-recursive` at `cf2f7b3`), re-stated for
-- Flock's queries (A.2) and its Fiat–Shamir item sequence (A.4).
import FRTranscriptDefs
import RecursionFast.Library.Security

/-!
# The log of the knowledge state: bad events, the transcript forest, chains (BLUEPRINT §5.1)

* **`Bad L`** (§5.1, S-D-M1): a collision (two queries, one answer), a **window hit** (an answer
  equal to a 32-byte window at offset `7 + 16k` or `8 + 16k` of a query of at most `queryCap`
  bytes asked before it or by the same entry), a **state hit** (an answer equal to the state field
  of an absorb or squeeze asked before it or by the same entry) or a repeated query.
* **`bad_step_le`** (the H row): on a log without bad events, at most
  `|L|·(2^17 + 2) + 2^17 + 1` of the `2^256` answers to a fresh query make the log bad;
  `bad_step_frac` bounds this by `2^96·(2^17 + 2) + 2^17 + 1` below `logCap`.
* **The forest** (`predIdx`, `back`, `pathOf`): an absorb or squeeze query's predecessor is the
  entry that answered its state. `back_append_old`, `back_new`: a fresh non-bad entry changes no
  old path and is a leaf.
* **The frontier**: an entry whose squeeze has not been asked. **`extCount_split`**: the
  martingale step of a multi-answer phase.
* **Chains**: `Matches es` (the entries start at a seed and follow the Fiat–Shamir items of A.4,
  state-linked; the column and Merkle-node queries are not on the chain), `IsChain`, `chains`,
  `chains_append`, `isChain_new` and its converses.
-/

namespace FR.Snd
open RecursionFast FR.Merkle

/-! ## The state field of a query -/

/-- The state of an absorb (`"FRABS000" ‖ st ‖ msg`) or squeeze (`"FRSQZ000" ‖ st`) query. -/
def stateIn (q : ByteArray) : Option Digest :=
  if (q.data.toList.take 8 = tagAbs ∧ 40 ≤ q.size) ∨ (q.data.toList.take 8 = tagSqz ∧ q.size = 40)
  then some (bytesAt q 8 32) else none

theorem squeezeQ_data (st : Digest) : (squeezeQ st).data.toList = tagSqz ++ st.toList := by
  simp [squeezeQ, bytesOf]

theorem squeezeQ_size (st : Digest) : (squeezeQ st).size = 40 := by
  rw [ByteArray.size, ← Array.length_toList, squeezeQ_data]; simp [tagSqz]

theorem bytesAt_eq_of_data {q : ByteArray} {t : List UInt8} (ht : t.length = 8) {st : Digest}
    {rest : List UInt8} (h : q.data.toList = t ++ st.toList ++ rest) : bytesAt q 8 32 = st := by
  ext k hk
  rw [getElem_bytesAt _ _ _ _ hk, h, List.append_assoc,
    List.getD_append_right _ _ _ _ (by omega), ht, Nat.add_sub_cancel_left,
    List.getD_append _ _ _ _ (by simpa using hk)]
  simp [List.getD_eq_getElem?_getD, hk]

theorem stateIn_squeezeQ (st : Digest) : stateIn (squeezeQ st) = some st := by
  have h : (squeezeQ st).data.toList = tagSqz ++ st.toList ++ [] := by rw [squeezeQ_data]; simp
  have hc : (squeezeQ st).data.toList.take 8 = tagSqz := by rw [squeezeQ_data]; simp [tagSqz]
  simp only [stateIn, hc, squeezeQ_size, and_true, or_true, ↓reduceIte, bytesAt_eq_of_data rfl h]

theorem stateIn_absorbQ (st : Digest) (msg : ByteArray) : stateIn (absorbQ st msg) = some st := by
  have hc : (absorbQ st msg).data.toList.take 8 = tagAbs := by rw [absorbQ_data]; simp [tagAbs]
  have hs : 40 ≤ (absorbQ st msg).size := by rw [absorbQ_size]; omega
  simp only [stateIn, hc, hs, and_self, true_or, ↓reduceIte,
    bytesAt_eq_of_data rfl (absorbQ_data st msg)]

/-! ## Bad events -/

/-- The windows of a query of at most `queryCap` bytes: offsets `7 + 16k` (the seed's) and
`8 + 16k` (every other query's); none for a longer query, which no verifier asks. -/
def wins (q : ByteArray) : List Digest :=
  if q.size ≤ queryCap then windowsFrom 7 q ++ windows q else []

/-- *Window hit*: an answer equal to a window of a query asked before it or by the same entry. -/
def WinHit (L : Log) : Prop :=
  ∃ i j : ℕ, ∃ (hij : i ≤ j) (hj : j < L.length), L[j].2 ∈ wins (L[i]'(by omega)).1

/-- *State hit*: an answer equal to the state field of a query asked before it or by the same
entry. -/
def StateHit (L : Log) : Prop :=
  ∃ i j : ℕ, ∃ (hij : i ≤ j) (hj : j < L.length), stateIn (L[i]'(by omega)).1 = some L[j].2

/-- *Repeated query*: two entries with the same query. -/
def Repeated (L : Log) : Prop := ¬ (L.map Prod.fst).Nodup

/-- **The bad events of a log** (§5.1): collision, window hit, state hit, repeat. -/
def Bad (L : Log) : Prop := Collision L ∨ WinHit L ∨ StateHit L ∨ Repeated L

/-! ## The H row: the bad answers of a fresh query -/

theorem length_windowsFrom_le (o : ℕ) (q : ByteArray) : (windowsFrom o q).length ≤ q.size / 16 :=
  (List.length_filterMap_le _ _).trans (by simp only [List.length_range]; omega)

theorem length_wins_le (q : ByteArray) : (wins q).length ≤ 2 ^ 17 := by
  unfold wins
  split_ifs with h
  · rw [List.length_append]
    have h1 := length_windowsFrom_le 7 q
    have h2 := length_windowsFrom_le 8 q
    unfold windows
    unfold queryCap at h
    omega
  · simp

set_option linter.constructorNameAsVariable false in
open Classical in
/-- **`bad_step_le`** (the H row): on a log without bad events, at most `|L|·(2^17 + 2) + 2^17 + 1`
answers to a fresh query make the log bad. -/
theorem bad_step_le {L : Log} {q : ByteArray} (hb : ¬ Bad L) (hq : q ∉ L.map Prod.fst) :
    (Finset.univ.filter fun a : Digest => Bad (L ++ [(q, a)])).card ≤
      L.length * (2 ^ 17 + 2) + (2 ^ 17 + 1) := by
  set A := (L.map Prod.snd).toFinset
  set B := L.toFinset.biUnion fun e => (wins e.1).toFinset
  set B' := (wins q).toFinset
  set C := L.toFinset.biUnion fun e => (stateIn e.1).toFinset
  set D := (stateIn q).toFinset
  have hA : A.card ≤ L.length := (List.toFinset_card_le _).trans (by simp)
  have hB : B.card ≤ L.length * 2 ^ 17 :=
    (Finset.card_biUnion_le_card_mul _ _ _ fun e _ =>
      (List.toFinset_card_le _).trans (length_wins_le _)).trans
      (Nat.mul_le_mul_right _ (List.toFinset_card_le L))
  have hB' : B'.card ≤ 2 ^ 17 := (List.toFinset_card_le _).trans (length_wins_le _)
  have hC : C.card ≤ L.length * 1 := by
    refine (Finset.card_biUnion_le_card_mul _ _ _ fun e _ => ?_).trans
      (Nat.mul_le_mul_right _ (List.toFinset_card_le L))
    rw [Option.card_toFinset]; cases stateIn e.1 <;> simp
  have hD : D.card ≤ 1 := by rw [Option.card_toFinset]; cases stateIn q <;> simp
  have hsub : (Finset.univ.filter fun a : Digest => Bad (L ++ [(q, a)])) ⊆
      A ∪ B ∪ B' ∪ C ∪ D := by
    intro a ha
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at ha
    simp only [Finset.mem_union]
    have hlen : (L ++ [(q, a)]).length = L.length + 1 := by simp
    rcases ha with ⟨e₁, h₁, e₂, h₂, hne, ht⟩ | ⟨i, j, hij, hj, hm⟩ | ⟨i, j, hij, hj, hs⟩ | hr
    · simp only [List.mem_append, List.mem_singleton] at h₁ h₂
      rcases h₁ with h₁ | rfl <;> rcases h₂ with h₂ | rfl
      · exact absurd (Or.inl ⟨e₁, h₁, e₂, h₂, hne, ht⟩) hb
      · left; left; left; left
        simp only [A, List.mem_toFinset, List.mem_map]; exact ⟨e₁, h₁, ht⟩
      · left; left; left; left
        simp only [A, List.mem_toFinset, List.mem_map]; exact ⟨e₂, h₂, ht.symm⟩
      · exact absurd rfl hne
    · rw [hlen] at hj
      by_cases hjL : j < L.length
      · refine absurd (Or.inr (Or.inl ⟨i, j, hij, hjL, ?_⟩)) hb
        rwa [List.getElem_append_left hjL, List.getElem_append_left (by omega)] at hm
      · have hj' : j = L.length := by omega
        subst hj'
        rw [List.getElem_concat_length rfl] at hm
        by_cases hiL : i < L.length
        · rw [List.getElem_append_left hiL] at hm
          left; left; left; right
          exact Finset.mem_biUnion.mpr ⟨L[i], List.mem_toFinset.mpr (List.getElem_mem hiL),
            List.mem_toFinset.mpr hm⟩
        · have hi' : i = L.length := by omega
          subst hi'
          rw [List.getElem_concat_length rfl] at hm
          left; left; right
          exact List.mem_toFinset.mpr hm
    · rw [hlen] at hj
      by_cases hjL : j < L.length
      · refine absurd (Or.inr (Or.inr (Or.inl ⟨i, j, hij, hjL, ?_⟩))) hb
        rwa [List.getElem_append_left hjL, List.getElem_append_left (by omega)] at hs
      · have hj' : j = L.length := by omega
        subst hj'
        rw [List.getElem_concat_length rfl] at hs
        by_cases hiL : i < L.length
        · rw [List.getElem_append_left hiL] at hs
          left; right
          refine Finset.mem_biUnion.mpr ⟨L[i], List.mem_toFinset.mpr (List.getElem_mem hiL), ?_⟩
          simp [hs]
        · have hi' : i = L.length := by omega
          subst hi'
          rw [List.getElem_concat_length rfl] at hs
          right
          simp [D, hs]
    · exfalso
      apply hr
      have hn : (L.map Prod.fst).Nodup := by
        by_contra h; exact hb (Or.inr (Or.inr (Or.inr h)))
      rw [List.map_append, List.nodup_append]
      refine ⟨hn, by simp, ?_⟩
      intro x hx y hy hxy
      simp only [List.map_cons, List.map_nil, List.mem_singleton] at hy
      subst hy; subst hxy
      exact hq hx
  calc (Finset.univ.filter fun a : Digest => Bad (L ++ [(q, a)])).card
      ≤ (A ∪ B ∪ B' ∪ C ∪ D).card := Finset.card_le_card hsub
    _ ≤ A.card + B.card + B'.card + C.card + D.card := by
      refine (Finset.card_union_le _ _).trans (Nat.add_le_add_right ?_ _)
      refine (Finset.card_union_le _ _).trans (Nat.add_le_add_right ?_ _)
      exact (Finset.card_union_le _ _).trans (Nat.add_le_add_right (Finset.card_union_le _ _) _)
    _ ≤ L.length * (2 ^ 17 + 2) + (2 ^ 17 + 1) := by nlinarith

/-- The H row's count below `logCap`. -/
def badCount : ℕ := 2 ^ 96 * (2 ^ 17 + 2) + (2 ^ 17 + 1)

open Classical in
/-- **`bad_step_frac`**: below `logCap = 2^96` entries, at most `badCount` answers are bad. -/
theorem bad_step_frac {L : Log} {q : ByteArray} (hb : ¬ Bad L) (hq : q ∉ L.map Prod.fst)
    (hl : L.length < logCap) :
    (Finset.univ.filter fun a : Digest => Bad (L ++ [(q, a)])).card ≤ badCount :=
  (bad_step_le hb hq).trans (by unfold logCap at hl; unfold badCount; nlinarith)

/-! ## The transcript forest -/

/-- The index of the first entry of `L` whose answer is `st`. -/
def ansIdx (L : Log) (st : Digest) : Option ℕ := L.findIdx? fun e => decide (e.2 = st)

/-- The index of the entry whose answer is the state of entry `j`. -/
def predIdx (L : Log) (j : ℕ) : Option ℕ := L[j]?.bind fun e => (stateIn e.1).bind (ansIdx L)

/-- The path of indices that ends at `j` and follows `predIdx` down through earlier entries, with
fuel `f`. -/
def back (L : Log) : ℕ → ℕ → List ℕ
  | 0, _ => []
  | f + 1, j =>
    match predIdx L j with
    | some i => if i < j then back L f i ++ [j] else [j]
    | none => [j]

/-- The forest path ending at entry `j`. -/
def pathOf (L : Log) (j : ℕ) : List ℕ := back L (j + 1) j

theorem back_fuel_aux (L : Log) :
    ∀ n f g j, j < n → j < f → j < g → back L f j = back L g j := by
  intro n
  induction n with
  | zero => intro f g j h; omega
  | succ n ih =>
    intro f g j hn hf hg
    obtain ⟨f, rfl⟩ : ∃ f', f = f' + 1 := ⟨f - 1, by omega⟩
    obtain ⟨g, rfl⟩ : ∃ g', g = g' + 1 := ⟨g - 1, by omega⟩
    simp only [back]
    cases predIdx L j with
    | none => rfl
    | some i =>
      simp only
      split_ifs with h
      · rw [ih f g i (by omega) (by omega) (by omega)]
      · rfl

theorem back_fuel (L : Log) (f j : ℕ) (h : j < f) : back L f j = back L (j + 1) j :=
  back_fuel_aux L (j + 1) f (j + 1) j (by omega) h (by omega)

theorem ansIdx_lt {L : Log} {st : Digest} {i : ℕ} (h : ansIdx L st = some i) :
    ∃ hi : i < L.length, L[i].2 = st := by
  obtain ⟨hi, hp, -⟩ := List.findIdx?_eq_some_iff_getElem.mp h
  exact ⟨hi, by simpa using hp⟩

/-- Under `¬ Bad`, the entry answering the state of entry `j` is unique and earlier. -/
theorem pred_unique_lt {L : Log} (hb : ¬ Bad L) {j : ℕ} (hj : j < L.length) {st : Digest}
    (hst : stateIn L[j].1 = some st) :
    (∀ i i' (hi : i < L.length) (hi' : i' < L.length), L[i].2 = st → L[i'].2 = st → i = i') ∧
      ∀ i (hi : i < L.length), L[i].2 = st → i < j := by
  refine ⟨fun i i' hi hi' h h' => ?_, fun i hi h => ?_⟩
  · have hq : L[i].1 = L[i'].1 := by
      by_contra hne
      exact hb (Or.inl ⟨L[i], List.getElem_mem hi, L[i'], List.getElem_mem hi', hne,
        by rw [h, h']⟩)
    have hn : (L.map Prod.fst).Nodup := by
      by_contra hr; exact hb (Or.inr (Or.inr (Or.inr hr)))
    exact (List.Nodup.getElem_inj_iff hn (i := i) (j := i') (hi := by simpa using hi)
      (hj := by simpa using hi')).mp (by simpa using hq)
  · by_contra hji
    exact hb (Or.inr (Or.inr (Or.inl ⟨j, i, by omega, hi, by rw [hst, h]⟩)))

/-- Under `¬ Bad`, the answer index of an entry's state is earlier than the entry. -/
theorem predIdx_lt {L : Log} (hb : ¬ Bad L) {j i : ℕ} (h : predIdx L j = some i) : i < j := by
  simp only [predIdx, Option.bind_eq_some_iff] at h
  obtain ⟨e, he, st, hst, hi⟩ := h
  obtain ⟨hj, rfl⟩ := List.getElem?_eq_some_iff.mp he
  obtain ⟨hiL, hia⟩ := ansIdx_lt hi
  exact (pred_unique_lt hb hj hst).2 i hiL hia

/-- An old entry keeps its predecessor when a non-bad entry is appended. -/
theorem predIdx_append_old {L : Log} {x : ByteArray × Digest} (hb : ¬ Bad (L ++ [x])) {j : ℕ}
    (hj : j < L.length) : predIdx (L ++ [x]) j = predIdx L j := by
  simp only [predIdx, List.getElem?_append_left hj]
  cases hLj : L[j]? with
  | none => rfl
  | some e =>
    simp only [Option.bind_some]
    cases hst : stateIn e.1 with
    | none => rfl
    | some st =>
      simp only [Option.bind_some, ansIdx, List.findIdx?_append]
      cases hf : L.findIdx? (fun e => decide (e.2 = st)) with
      | some i => rfl
      | none =>
        simp only [Option.none_or]
        cases hx : [x].findIdx? (fun e => decide (e.2 = st)) with
        | none => rfl
        | some k =>
          exfalso
          obtain ⟨hk, hkp, -⟩ := List.findIdx?_eq_some_iff_getElem.mp hx
          have hk0 : k = 0 := by simpa using hk
          subst hk0
          have hxst : x.2 = st := by simpa using hkp
          obtain ⟨hjL, rfl⟩ := List.getElem?_eq_some_iff.mp hLj
          apply hb
          refine Or.inr (Or.inr (Or.inl ⟨j, L.length, by omega, by simp, ?_⟩))
          rw [List.getElem_append_left hjL, List.getElem_concat_length rfl, hst, hxst]

/-- **Old paths** (`back_append_old`): appending a non-bad entry changes no path that ends at an
old entry. -/
theorem back_append_old {L : Log} {x : ByteArray × Digest} (hb : ¬ Bad (L ++ [x])) :
    ∀ f j, j < L.length → back (L ++ [x]) f j = back L f j := by
  intro f
  induction f with
  | zero => intro j _; rfl
  | succ f ih =>
    intro j hj
    simp only [back, predIdx_append_old hb hj]
    cases predIdx L j with
    | none => rfl
    | some i =>
      simp only
      split_ifs with h
      · rw [ih i (by omega)]
      · rfl

/-- The new entry's predecessor is read off `L`, under no bad event. -/
theorem predIdx_new {L : Log} {q : ByteArray} {a : Digest} (hb : ¬ Bad (L ++ [(q, a)])) :
    predIdx (L ++ [(q, a)]) L.length = (stateIn q).bind (ansIdx L) := by
  simp only [predIdx, List.getElem?_concat_length, Option.bind_some]
  cases hst : stateIn q with
  | none => rfl
  | some st =>
    simp only [Option.bind_some, ansIdx, List.findIdx?_append]
    cases hf : L.findIdx? (fun e => decide (e.2 = st)) with
    | some i => rfl
    | none =>
      simp only [Option.none_or]
      cases hx : [(q, a)].findIdx? (fun e => decide (e.2 = st)) with
      | none => rfl
      | some k =>
        exfalso
        obtain ⟨hk, hkp, -⟩ := List.findIdx?_eq_some_iff_getElem.mp hx
        have hk0 : k = 0 := by simpa using hk
        subst hk0
        have hast : a = st := by simpa using hkp
        apply hb
        refine Or.inr (Or.inr (Or.inl ⟨L.length, L.length, le_rfl, by simp, ?_⟩))
        rw [List.getElem_concat_length rfl, hst, hast]

/-- **The new entry is a leaf** (`back_new`): under no bad event, its path is its predecessor's
path in `L` followed by it, or the new entry alone. -/
theorem back_new {L : Log} {q : ByteArray} {a : Digest} (hb : ¬ Bad (L ++ [(q, a)])) :
    pathOf (L ++ [(q, a)]) L.length =
      match (stateIn q).bind (ansIdx L) with
      | some i => pathOf L i ++ [L.length]
      | none => [L.length] := by
  simp only [pathOf]
  rw [back.eq_2, predIdx_new hb]
  cases hp : (stateIn q).bind (ansIdx L) with
  | none => rfl
  | some i =>
    simp only
    have hi : i < L.length := by
      have := predIdx_new hb
      rw [hp] at this
      exact predIdx_lt hb this
    simp only [hi, ↓reduceIte]
    rw [back_append_old hb _ _ hi, back_fuel L L.length i hi]

theorem pathOf_append_old {L : Log} {x : ByteArray × Digest} (hb : ¬ Bad (L ++ [x])) {j : ℕ}
    (hj : j < L.length) : pathOf (L ++ [x]) j = pathOf L j :=
  back_append_old hb _ _ hj

/-! ## The frontier -/

/-- An entry is on the frontier of `L` when the squeeze of its answer is not asked in `L`. -/
def OnFrontier (L : Log) (e : ByteArray × Digest) : Prop :=
  e ∈ L ∧ squeezeQ e.2 ∉ L.map Prod.fst

/-- A fresh entry removes from the frontier only the entries whose squeeze it is. -/
theorem frontier_append {L : Log} {q : ByteArray} {a : Digest} {e : ByteArray × Digest}
    (he : e ∈ L) : OnFrontier (L ++ [(q, a)]) e ↔ OnFrontier L e ∧ q ≠ squeezeQ e.2 := by
  simp only [OnFrontier, List.mem_append, List.mem_singleton, he, true_or, true_and,
    List.map_append, List.map_cons, List.map_nil, not_or]
  constructor
  · rintro ⟨h1, h2⟩; exact ⟨h1, fun h => h2 h.symm⟩
  · rintro ⟨h1, h2⟩; exact ⟨h1, fun h => h2 h.symm⟩

/-! ## The martingale split of a phase's count -/

open Classical in
/-- The number of completions of the answers `pre` by `k` more answers that satisfy `P`. -/
noncomputable def extCount (P : List Digest → Prop) (pre : List Digest) (k : ℕ) : ℕ :=
  (Finset.univ.filter fun rest : Fin k → Digest => P (pre ++ List.ofFn rest)).card

open Classical in
/-- **`extCount_split`**: the completions of `pre` by `k + 1` answers are the sum over the next
answer `a` of the completions of `pre ++ [a]` by `k`. -/
theorem extCount_split (P : List Digest → Prop) (pre : List Digest) (k : ℕ) :
    ∑ a : Digest, extCount P (pre ++ [a]) k = extCount P pre (k + 1) := by
  simp only [extCount]
  rw [Finset.card_equiv (Fin.consEquiv fun _ : Fin (k + 1) => Digest).symm
    (t := Finset.univ.filter fun x : Digest × (Fin k → Digest) =>
      P (pre ++ [x.1] ++ List.ofFn x.2))]
  · rw [Finset.card_filter, Fintype.sum_prod_type]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [Finset.card_filter]
  · intro f
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    rw [List.ofFn_succ, List.append_assoc, List.singleton_append]
    rfl

/-! ## Chains

A chain is an entry whose forest path, read as entries, starts at a seed and follows the
Fiat–Shamir items of A.4 (`fsItems`: the seed, the absorbs with their lengths, the squeezes),
state-linked. The column and Merkle-node queries are not on chains: their answers are charged by
`Bad` only. -/

/-- The tag and length check of a Fiat–Shamir item on a query (`Item.qlen`'s sizes). -/
def fsCheck : Item → ByteArray → Bool
  | .seed, q => q.data.toList.take 7 == tagSeed && q.size == Item.seed.qlen
  | .absorb len, q => q.data.toList.take 8 == tagAbs && q.size == 40 + len
  | .squeeze, q => q.data.toList.take 8 == tagSqz && q.size == 40
  | _, _ => false

/-- **The Fiat–Shamir items** (A.4): the item sequence without the column and node queries. -/
def fsItems : List Item := items.filter Item.isFS

/-- The entries of `L` at the indices `is`. -/
def entriesOf (L : Log) (is : List ℕ) : Log := is.map fun i => L[i]!

/-- **The entries follow the Fiat–Shamir items**: a seed first, at most `|fsItems|` entries, each
later entry with the previous answer as its state and the tag and length of its item. -/
def Matches (es : Log) : Prop :=
  (es.head?.map fun e => fsCheck .seed e.1) = some true ∧ ∃ hl : es.length ≤ fsItems.length,
    ∀ i (hi : i + 1 < es.length), stateIn es[i + 1].1 = some es[i].2 ∧
      fsCheck (fsItems[i + 1]'(by omega)) es[i + 1].1 = true

/-- **A chain of `L`**: an entry index whose forest path, read as entries, `Matches`. -/
def IsChain (L : Log) (j : ℕ) : Prop := j < L.length ∧ Matches (entriesOf L (pathOf L j))

noncomputable instance (L : Log) : DecidablePred (IsChain L) := Classical.decPred _

/-- The indices of `L` that are chains. -/
noncomputable def chains (L : Log) : List ℕ :=
  (List.range L.length).filter fun j => decide (IsChain L j)

/-! ### Path facts -/

theorem mem_back_le (L : Log) : ∀ f j, ∀ x ∈ back L f j, x ≤ j := by
  intro f
  induction f with
  | zero => intro j x hx; simp [back] at hx
  | succ f ih =>
    intro j x hx
    simp only [back] at hx
    cases hp : predIdx L j with
    | none => rw [hp] at hx; simp at hx; omega
    | some i =>
      rw [hp] at hx
      simp only at hx
      split_ifs at hx with h
      · rcases List.mem_append.mp hx with hx | hx
        · exact (ih i x hx).trans h.le
        · simp at hx; omega
      · simp at hx; omega

theorem mem_pathOf_le {L : Log} {j x : ℕ} (hx : x ∈ pathOf L j) : x ≤ j :=
  mem_back_le L _ _ _ hx

theorem back_ne_nil (L : Log) (f j : ℕ) : back L (f + 1) j ≠ [] := by
  simp only [back]
  cases predIdx L j with
  | none => simp
  | some i => simp only; split_ifs <;> simp

theorem pathOf_ne_nil (L : Log) (j : ℕ) : pathOf L j ≠ [] := back_ne_nil L j j

theorem back_getLast? (L : Log) (f j : ℕ) : (back L (f + 1) j).getLast? = some j := by
  simp only [back]
  cases predIdx L j with
  | none => simp
  | some i => simp only; split_ifs <;> simp

theorem pathOf_getLast? (L : Log) (j : ℕ) : (pathOf L j).getLast? = some j := back_getLast? L j j

theorem length_entriesOf (L : Log) (is : List ℕ) : (entriesOf L is).length = is.length := by
  simp [entriesOf]

theorem entriesOf_getLast? (L : Log) (j : ℕ) :
    (entriesOf L (pathOf L j)).getLast? = some L[j]! := by
  rw [entriesOf, List.getLast?_map, pathOf_getLast?]
  rfl

theorem entriesOf_append {L : Log} {x : ByteArray × Digest} {is : List ℕ}
    (h : ∀ i ∈ is, i < L.length) : entriesOf (L ++ [x]) is = entriesOf L is := by
  unfold entriesOf
  apply List.map_congr_left
  intro i hi
  have hi' := h i hi
  rw [getElem!_pos (L ++ [x]) i (by simp; omega), getElem!_pos L i hi',
    List.getElem_append_left hi']

theorem entriesOf_getElem (L : Log) (is : List ℕ) (k : ℕ) (hk : k < (entriesOf L is).length) :
    (entriesOf L is)[k] = L[is[k]'(by simpa [entriesOf] using hk)]! := by
  simp [entriesOf]

/-! ### Chains of an extended log -/

theorem matches_ne_nil {es : Log} (h : Matches es) : es ≠ [] := by
  rintro rfl; simp [Matches] at h

/-- `Matches` of a longer list gives `Matches` of its nonempty prefix. -/
theorem matches_of_append {es : Log} {x : ByteArray × Digest} (hne : es ≠ [])
    (h : Matches (es ++ [x])) : Matches es := by
  obtain ⟨h0, hl, hm⟩ := h
  refine ⟨?_, by simp at hl; omega, fun i hi => ?_⟩
  · rwa [List.head?_append_of_ne_nil _ hne] at h0
  · have := hm i (by simp; omega)
    simp only [List.getElem_append_left hi, List.getElem_append_left (show i < es.length by omega)]
      at this
    exact this

/-- **`chains_append`**: appending a non-bad entry keeps every old chain (with its path) and adds
at most the new entry. -/
theorem chains_append {L : Log} {e : ByteArray × Digest} (hb : ¬ Bad (L ++ [e])) :
    chains (L ++ [e]) = chains L ++ (if IsChain (L ++ [e]) L.length then [L.length] else []) := by
  classical
  unfold chains
  rw [List.length_append, List.length_singleton, List.range_succ, List.filter_append]
  congr 1
  · apply List.filter_congr
    intro j hj
    rw [List.mem_range] at hj
    apply decide_eq_decide.mpr
    unfold IsChain
    rw [List.length_append, List.length_singleton, pathOf_append_old hb hj,
      entriesOf_append fun i hi => (mem_pathOf_le hi).trans_lt hj]
    constructor
    · rintro ⟨-, h⟩; exact ⟨hj, h⟩
    · rintro ⟨-, h⟩; exact ⟨by omega, h⟩
  · by_cases h : IsChain (L ++ [e]) L.length <;> simp [h]

theorem chains_nodup (L : Log) : (chains L).Nodup := (List.nodup_range).filter _

theorem mem_chains {L : Log} {j : ℕ} : j ∈ chains L ↔ IsChain L j := by
  unfold chains
  simp only [List.mem_filter, List.mem_range, decide_eq_true_eq]
  exact ⟨fun h => h.2, fun h => ⟨h.1, h⟩⟩

/-- The entries of an old chain are unchanged by appending a non-bad entry. -/
theorem entriesOf_pathOf_append {L : Log} {x : ByteArray × Digest} (hb : ¬ Bad (L ++ [x]))
    {j : ℕ} (hj : j < L.length) :
    entriesOf (L ++ [x]) (pathOf (L ++ [x]) j) = entriesOf L (pathOf L j) := by
  rw [pathOf_append_old hb hj, entriesOf_append fun i hi => (mem_pathOf_le hi).trans_lt hj]

/-- The new entry's chain entries, when it extends entry `i`. -/
theorem entriesOf_new {L : Log} {q : ByteArray} {a : Digest} (hb : ¬ Bad (L ++ [(q, a)])) {i : ℕ}
    (hp : (stateIn q).bind (ansIdx L) = some i) :
    entriesOf (L ++ [(q, a)]) (pathOf (L ++ [(q, a)]) L.length) =
      entriesOf L (pathOf L i) ++ [(q, a)] := by
  have hpath := back_new hb
  rw [hp] at hpath
  have hi : i < L.length := by
    have := predIdx_new hb
    rw [hp] at this
    exact predIdx_lt hb this
  rw [hpath]
  unfold entriesOf
  rw [List.map_append]
  congr 1
  · exact entriesOf_append fun x hx => (mem_pathOf_le hx).trans_lt hi
  · simp

/-- **The new chain**: if the appended entry ends a chain, it is a seed with no predecessor, or it
extends a chain `i` of `L` (its predecessor), whose entries it follows. -/
theorem isChain_new {L : Log} {q : ByteArray} {a : Digest} (hb : ¬ Bad (L ++ [(q, a)]))
    (hc : IsChain (L ++ [(q, a)]) L.length) :
    ((stateIn q).bind (ansIdx L) = none ∧ fsCheck .seed q = true) ∨
      ∃ i, (stateIn q).bind (ansIdx L) = some i ∧ IsChain L i ∧
        entriesOf (L ++ [(q, a)]) (pathOf (L ++ [(q, a)]) L.length) =
          entriesOf L (pathOf L i) ++ [(q, a)] := by
  have hpath := back_new hb
  cases hp : (stateIn q).bind (ansIdx L) with
  | none =>
    rw [hp] at hpath
    left
    refine ⟨rfl, ?_⟩
    have h0 := hc.2.1
    rw [hpath] at h0
    simpa [entriesOf] using h0
  | some i =>
    have hi : i < L.length := by
      have := predIdx_new hb
      rw [hp] at this
      exact predIdx_lt hb this
    have hes := entriesOf_new hb hp
    right
    refine ⟨i, rfl, ⟨hi, ?_⟩, hes⟩
    have := hc.2
    rw [hes] at this
    exact matches_of_append (by simpa [entriesOf] using pathOf_ne_nil L i) this

/-- `Matches` extends by an entry linked to the last answer and matching the next item. -/
theorem matches_append {es : Log} {x : ByteArray × Digest} (h : Matches es)
    (hl' : es.length < fsItems.length) (hy : ∃ y, es.getLast? = some y ∧ stateIn x.1 = some y.2)
    (hmatch : fsCheck (fsItems[es.length]'hl') x.1 = true) : Matches (es ++ [x]) := by
  obtain ⟨h0, hl, hm⟩ := h
  obtain ⟨y, hy, hst⟩ := hy
  have hne : es ≠ [] := by rintro rfl; simp at h0
  refine ⟨?_, by simp; omega, fun i hi => ?_⟩
  · rwa [List.head?_append_of_ne_nil _ hne]
  · simp only [List.length_append, List.length_singleton] at hi
    by_cases hlt : i + 1 < es.length
    · have := hm i hlt
      rwa [List.getElem_append_left hlt, List.getElem_append_left (show i < es.length by omega)]
    · have hie : i + 1 = es.length := by omega
      have hy' : es[i]'(by omega) = y := by
        rw [List.getLast?_eq_getElem?] at hy
        have : es.length - 1 = i := by omega
        rw [this, List.getElem?_eq_getElem (by omega)] at hy
        exact Option.some.inj hy
      rw [List.getElem_append_left (show i < es.length by omega), hy',
        List.getElem_concat_length hie]
      refine ⟨hst, ?_⟩
      have : fsItems[i + 1]'(by omega) = fsItems[es.length]'hl' := by congr 1
      rw [this]; exact hmatch

/-- A seed query has no state field. -/
theorem stateIn_of_seed {q : ByteArray} (h : fsCheck .seed q = true) : stateIn q = none := by
  simp only [fsCheck, Bool.and_eq_true, beq_iff_eq] at h
  have h7 : ∀ t : List UInt8, q.data.toList.take 8 = t → t.take 7 = tagSeed := by
    intro t ht; rw [← ht, List.take_take]; exact h.1
  unfold stateIn
  rw [ite_eq_right_iff]
  rintro (⟨ht, -⟩ | ⟨ht, -⟩) <;> exact absurd (h7 _ ht) (by decide)

theorem one_le_fsItems : 1 ≤ fsItems.length := by
  unfold fsItems
  rw [Nat.one_le_iff_ne_zero, Ne, List.length_eq_zero_iff, List.filter_eq_nil_iff]
  intro hall
  exact absurd (hall Item.seed (List.mem_of_mem_head? qlen_mod.1)) (by decide)

/-- **The new chain, converse** (seed case): a fresh seed is a chain. -/
theorem isChain_new_of_seed {L : Log} {q : ByteArray} {a : Digest} (hb : ¬ Bad (L ++ [(q, a)]))
    (hs : fsCheck .seed q = true) : IsChain (L ++ [(q, a)]) L.length := by
  refine ⟨by simp, ?_⟩
  have hpath := back_new hb
  rw [stateIn_of_seed hs] at hpath
  simp only [Option.bind_none] at hpath
  rw [hpath]
  refine ⟨by simp [entriesOf, hs], ?_, fun i hi => ?_⟩
  · simp only [entriesOf, List.map_cons, List.map_nil, List.length_singleton]
    exact one_le_fsItems
  · simp [entriesOf] at hi

/-- **The new chain, converse** (extension case): an entry whose predecessor ends a chain `i` and
which matches the next item is a chain. -/
theorem isChain_new_of_extend {L : Log} {q : ByteArray} {a : Digest}
    (hb : ¬ Bad (L ++ [(q, a)])) {i : ℕ} (hp : (stateIn q).bind (ansIdx L) = some i)
    (hc : IsChain L i) (hl : (entriesOf L (pathOf L i)).length < fsItems.length)
    (hnext : fsCheck (fsItems[(entriesOf L (pathOf L i)).length]'hl) q = true) :
    IsChain (L ++ [(q, a)]) L.length := by
  have hi : i < L.length := hc.1
  refine ⟨by simp, ?_⟩
  rw [entriesOf_new hb hp]
  refine matches_append hc.2 hl ⟨L[i], ?_, ?_⟩ hnext
  · unfold entriesOf
    rw [List.getLast?_map, pathOf_getLast?]
    simp [List.getElem?_eq_getElem hi]
  · simp only [Option.bind_eq_some_iff] at hp
    obtain ⟨st, hst, hidx⟩ := hp
    obtain ⟨hi2, hans⟩ := ansIdx_lt hidx
    rw [hst, hans]

/-! ## Log facts used by the potential -/

/-- Under `¬ Bad`, distinct entries have distinct answers. -/
theorem ans_inj {L : Log} (hb : ¬ Bad L) {i j : ℕ} (hi : i < L.length) (hj : j < L.length)
    (h : L[i].2 = L[j].2) : i = j := by
  have hq : L[i].1 = L[j].1 := by
    by_contra hne
    exact hb (Or.inl ⟨L[i], List.getElem_mem hi, L[j], List.getElem_mem hj, hne, by rw [h]⟩)
  have hn : (L.map Prod.fst).Nodup := by
    by_contra hr; exact hb (Or.inr (Or.inr (Or.inr hr)))
  exact (List.Nodup.getElem_inj_iff hn (i := i) (j := j) (hi := by simpa using hi)
    (hj := by simpa using hj)).mp (by simpa using hq)

/-- Under `¬ Bad`, the answer index of an entry's own answer is the entry. -/
theorem ansIdx_self {L : Log} (hb : ¬ Bad L) {j : ℕ} (hj : j < L.length) :
    ansIdx L L[j].2 = some j := by
  unfold ansIdx
  rw [List.findIdx?_eq_some_iff_getElem]
  refine ⟨hj, by simp, fun k hk => ?_⟩
  simp only [decide_eq_true_eq]
  intro h
  exact absurd (ans_inj hb (hk.trans hj) hj h) (Nat.ne_of_lt hk)

/-- The squeeze of an old answer has that entry as its predecessor. -/
theorem istar_of_squeeze {L : Log} (hb : ¬ Bad L) {j : ℕ} (hj : j < L.length) {q : ByteArray}
    (hq : q = squeezeQ L[j]!.2) : (stateIn q).bind (ansIdx L) = some j := by
  rw [hq, stateIn_squeezeQ, Option.bind_some, getElem!_pos L j hj, ansIdx_self hb hj]

theorem lt_of_ansIdx {L : Log} {q : ByteArray} {i : ℕ} (h : (stateIn q).bind (ansIdx L) = some i) :
    i < L.length ∧ stateIn q = some L[i]!.2 := by
  rw [Option.bind_eq_some_iff] at h
  obtain ⟨st, hst, hi⟩ := h
  obtain ⟨hiL, hia⟩ := ansIdx_lt hi
  exact ⟨hiL, by rw [hst, getElem!_pos L i hiL, hia]⟩

/-! ## Challenge fibers (A.2): an answer is two uniform F coordinates, or one uniform K element -/

theorem getElem_digestBytes (a : Digest) (o n k : ℕ) (hk : k < n) (ho : o + k < 32) :
    (digestBytes a o n)[k] = a[o + k] := by
  simp [digestBytes, Vector.getElem_ofFn, ho]

/-- **The two F coordinates of an answer** (`chF a 0`, `chF a 1`) are a bijection. -/
noncomputable def chFEquiv : Digest ≃ F × F where
  toFun a := (chF a 0, chF a 1)
  invFun p := F.toBytes p.1 ++ F.toBytes p.2
  left_inv a := by
    simp only [chF, F.toBytes_ofBytes]
    ext i hi
    rw [Vector.getElem_append]
    split_ifs with h
    · rw [getElem_digestBytes a (16 * 0) 16 i h (by omega)]; simp
    · rw [getElem_digestBytes a (16 * 1) 16 (i - 16) (by omega) (by omega)]
      congr 2; omega
  right_inv p := by
    obtain ⟨x, y⟩ := p
    have h0 : digestBytes (F.toBytes x ++ F.toBytes y) (16 * 0) 16 = F.toBytes x := by
      ext i hi
      rw [getElem_digestBytes _ (16 * 0) 16 i hi (by omega), Vector.getElem_append]
      simp [hi]
    have h1 : digestBytes (F.toBytes x ++ F.toBytes y) (16 * 1) 16 = F.toBytes y := by
      ext i hi
      rw [getElem_digestBytes _ (16 * 1) 16 i hi (by omega), Vector.getElem_append]
      simp [show ¬ 16 * 1 + i < 16 by omega]
    simp only [chF, h0, h1, F.ofBytes_toBytes]

theorem chFEquiv_apply (a : Digest) : chFEquiv a = (chF a 0, chF a 1) := rfl

/-- **The K challenge of an answer** is a bijection. -/
noncomputable def chKEquiv : Digest ≃ K where
  toFun := chK
  invFun := K.toBytes
  left_inv a := K.toBytes_ofBytes a
  right_inv x := K.ofBytes_toBytes x

/-- **`card_chF2_fiber`**: the answers whose two F coordinates satisfy `P` number as many as the
pairs that satisfy `P`. -/
theorem card_chF2_fiber (P : F × F → Prop) [DecidablePred P] :
    (Finset.univ.filter fun a : Digest => P (chF a 0, chF a 1)).card =
      (Finset.univ.filter P).card :=
  Finset.card_equiv chFEquiv fun a => by
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, chFEquiv_apply]

/-- **`card_chF_fiber`**: the answers whose first F coordinate lies in `S` number `|S|·2^128`. -/
theorem card_chF_fiber (S : Finset F) :
    (Finset.univ.filter fun a : Digest => chF a 0 ∈ S).card = S.card * 2 ^ 128 := by
  refine (card_chF2_fiber (fun p => p.1 ∈ S)).trans ?_
  have : (Finset.univ.filter fun p : F × F => p.1 ∈ S) = S ×ˢ Finset.univ := by ext; simp
  rw [this, Finset.card_product, Finset.card_univ, F.card_F]

/-- **`card_chK_fiber`**: the answers whose K challenge lies in `S` number `|S|`. -/
theorem card_chK_fiber (S : Finset K) :
    (Finset.univ.filter fun a : Digest => chK a ∈ S).card = S.card :=
  Finset.card_equiv chKEquiv (t := S) fun a => by
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]; rfl

/-! ## Controls -/

/-- The empty log is not bad. -/
theorem not_bad_nil : ¬ Bad [] := by
  rintro (⟨e, he, -⟩ | ⟨i, j, -, hj, -⟩ | ⟨i, j, -, hj, -⟩ | hr)
  · simp at he
  · simp at hj
  · simp at hj
  · exact hr List.nodup_nil

/-- A squeeze answered by its own state is a state hit, hence bad (the self case `i = j`). -/
theorem bad_self_state (st : Digest) : Bad [(squeezeQ st, st)] :=
  Or.inr (Or.inr (Or.inl ⟨0, 0, le_rfl, by simp, by simp [stateIn_squeezeQ]⟩))

/-- Two different queries with one answer are bad (a collision). -/
theorem bad_collision (st a : Digest) (h : st ≠ a) :
    Bad [(squeezeQ st, a), (squeezeQ a, a)] := by
  refine Or.inl ⟨_, List.mem_cons_self .., _, List.mem_cons_of_mem _ (List.mem_cons_self ..), ?_,
    rfl⟩
  intro he
  have := congrArg stateIn he
  simp only [stateIn_squeezeQ, Option.some.injEq] at this
  exact h this

/-- A seed query with a 48-byte header, alone, is a chain's entries. -/
theorem matches_seed (vk c : Digest) (hdr : ByteArray) (hh : hdr.size = 48) (a : Digest) :
    Matches [(seedQ vk c hdr, a)] := by
  have hd : (seedQ vk c hdr).data.toList = tagSeed ++ (vk.toList ++ c.toList ++ hdr.data.toList) := by
    simp [seedQ, bytesOf, ByteArray.data_append]
  have hs : (seedQ vk c hdr).size = Item.seed.qlen := by
    rw [ByteArray.size, ← Array.length_toList, hd]
    simp only [List.length_append, Vector.length_toList, Array.length_toList]
    rw [show hdr.data.size = 48 from hh]; rfl
  refine ⟨?_, by simpa using one_le_fsItems, fun i hi => by simp at hi⟩
  simp only [List.head?_cons, Option.map_some, fsCheck, hs, beq_self_eq_true, Bool.and_true, hd,
    List.take_left' (show tagSeed.length = 7 from rfl)]

/-- A squeeze alone is not a chain's entries (a chain starts at a seed). -/
theorem not_matches_squeeze (st a : Digest) : ¬ Matches [(squeezeQ st, a)] := by
  rintro ⟨h0, -⟩
  have h7 : ((squeezeQ st).data.toList.take 7) = tagSqz.take 7 := by
    rw [squeezeQ_data, List.take_append_of_le_length (by decide)]
  simp only [List.head?_cons, Option.map_some, Option.some.injEq, fsCheck, Bool.and_eq_true,
    beq_iff_eq, h7] at h0
  exact absurd h0.1 (by decide)

end FR.Snd
