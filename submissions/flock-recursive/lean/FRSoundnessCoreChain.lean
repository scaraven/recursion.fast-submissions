-- New for `flock-recursive` (BLUEPRINT §10 changes 27 (B) step 3; stage RET-2): the declarations of
-- the 3.x soundness modules that the revision 4.1 certificate reads, moved here verbatim (same
-- names, statements and proofs) from `FRSoundnessDefs` (14), `FRSoundnessFrChain` (25). Content:
-- the potential's item-list part (`Defs`: `fsStarts`, `fsRanges`, `pRound`, …) and the generic
-- chain `G.*` (`FsSeq`, `Matches`, `IsChain`, `EscG`, `muG`, `chains`). The 3.x modules import this
-- one.
import FRSoundnessCoreDefs

/-! ## From `FRSoundnessDefs` (14 declarations) -/

section

namespace FR.Snd

open RecursionFast FR.Merkle

open scoped NNReal

section Potential

variable (D : Log → Log → Prop) (φ : Log → Log → ℝ≥0)

open Classical in
/-- The charge of chain `j` in `L`: its `φ` if its last entry is on the frontier, else `0`. -/
noncomputable def termG (L : Log) (j : ℕ) : ℝ≥0 :=
  if OnFrontier L L[j]! then φ (L₀ L j) (entriesOf L (pathOf L j)) else 0

/-- A function supported on one index sums, over a duplicate-free list, to its value there. -/
theorem sum_map_single {l : List ℕ} (hl : l.Nodup) (f : ℕ → ℝ≥0) (i : ℕ)
    (hf : ∀ j ∈ l, j ≠ i → f j = 0) : (l.map f).sum = if i ∈ l then f i else 0 := by
  classical
  rw [← List.sum_toFinset f hl]
  split_ifs with hi
  · exact Finset.sum_eq_single i (fun j hj hji => hf j (List.mem_toFinset.mp hj) hji)
      (fun h => absurd (List.mem_toFinset.mpr hi) h)
  · exact Finset.sum_eq_zero fun j hj => hf j (List.mem_toFinset.mp hj)
      (fun h => hi (h ▸ List.mem_toFinset.mp hj))

theorem sum_map_zero {l : List ℕ} (f : ℕ → ℝ≥0) (hf : ∀ j ∈ l, f j = 0) : (l.map f).sum = 0 := by
  rw [List.map_congr_left hf]; simp

variable {D φ}

section Step

variable {L : Log} {q : ByteArray} {a : Digest}

theorem L₀_append {x : ByteArray × Digest} {j : ℕ} (hj : j < L.length) :
    L₀ (L ++ [x]) j = L₀ L j := by
  unfold L₀; rw [List.take_append_of_le_length hj.le]

theorem L₀_new : L₀ (L ++ [(q, a)]) L.length = L := by simp [L₀]

/-- An old chain's charge after appending a fresh non-bad entry, plus the charge it loses when the
query is its squeeze, is its charge before. -/
theorem termG_append (hq : q ∉ L.map Prod.fst) (hb : ¬ Bad (L ++ [(q, a)])) {j : ℕ}
    (hj : j < L.length) :
    termG φ (L ++ [(q, a)]) j +
        (if q = squeezeQ L[j]!.2 then φ (L₀ L j) (entriesOf L (pathOf L j)) else 0) =
      termG φ L j := by
  classical
  have hget : (L ++ [(q, a)])[j]! = L[j]! := by
    rw [getElem!_pos (L ++ [(q, a)]) j (by simp; omega), getElem!_pos L j hj,
      List.getElem_append_left hj]
  have hmem : L[j]! ∈ L := by rw [getElem!_pos L j hj]; exact List.getElem_mem hj
  unfold termG
  rw [hget, L₀_append hj, entriesOf_pathOf_append hb hj]
  have hfr := frontier_append (q := q) (a := a) hmem
  generalize L[j]! = e at hmem hfr ⊢
  by_cases hs : q = squeezeQ e.2
  · have hf : OnFrontier L e := ⟨hmem, hs ▸ hq⟩
    rw [ite_eq_right (fun h => (hfr.mp h).2 hs), ite_eq_left hs, ite_eq_left hf, zero_add]
  · rw [ite_eq_right hs, add_zero]
    by_cases hf : OnFrontier L e
    · rw [ite_eq_left (hfr.mpr ⟨hf, hs⟩), ite_eq_left hf]
    · rw [ite_eq_right (fun h => hf (hfr.mp h).1), ite_eq_right hf]

end Step

open Classical in
/-- `Bad` of a log with an entry appended, as a sum of indicators, is at most the H row's count. -/
theorem card_bad_le {L : Log} {q : ByteArray} (hb : ¬ Bad L) (hq : q ∉ L.map Prod.fst)
    (hl : L.length < logCap) :
    (∑ a : Digest, (if Bad (L ++ [(q, a)]) then 1 else 0 : ℝ≥0)) ≤ (badCount : ℝ≥0) := by
  rw [Finset.sum_boole]
  exact_mod_cast bad_step_frac hb hq hl

end Potential

section Ext

variable (D : Log → Log → Prop)

theorem condCount_split (L₀ es₀ : Log) {r : ℕ} {pre : List Digest} (h : pre.length < r) :
    ∑ a : Digest, condCount D L₀ es₀ r (pre ++ [a]) = 2 ^ 256 * condCount D L₀ es₀ r pre := by
  classical
  unfold condCount
  obtain ⟨k, hk⟩ : ∃ k, r - pre.length = k + 1 := ⟨r - pre.length - 1, by omega⟩
  have hk' : ∀ a : Digest, r - (pre ++ [a]).length = k := fun a => by simp; omega
  simp only [hk', hk]
  simp only [div_eq_mul_inv, ← Finset.sum_mul]
  rw [← Nat.cast_sum, extCount_split, show 256 * (k + 1) = 256 * k + 256 by ring, pow_add, mul_inv]
  have h2 : (2 : ℝ≥0) ^ 256 ≠ 0 := by positivity
  have h3 : (2 : ℝ≥0) ^ (256 * k) ≠ 0 := by positivity
  field_simp

open Classical in
theorem condCount_last (L₀ es₀ : Log) {r : ℕ} {pre : List Digest} (h : pre.length = r) :
    condCount D L₀ es₀ r pre = if EscAtG D L₀ (ext es₀ pre) then 1 else 0 := by
  classical
  unfold condCount
  rw [h, Nat.sub_self, mul_zero, pow_zero, div_one, extCount, Finset.card_filter,
    Finset.univ_unique, Finset.sum_singleton]
  simp only [List.ofFn_zero, List.append_nil]
  split_ifs <;> simp

end Ext

section Local

theorem lastAns_of_getLast? {es : Log} {e : ByteArray × Digest} (h : es.getLast? = some e) :
    lastAns es = e.2 := by
  simp [lastAns, h]

/-- A 40-byte query is its first 8 bytes and its 32-byte state. -/
theorem split40 (q : ByteArray) (hs : q.size = 40) :
    q.data.toList = q.data.toList.take 8 ++ (bytesAt q 8 32).toList := by
  have hl : q.data.toList.length = 40 := by rw [Array.length_toList]; exact hs
  have ht : (q.data.toList.take 8).length = 8 := by rw [List.length_take, hl]; rfl
  refine List.ext_getElem (by rw [List.length_append, ht, hl]; simp) fun k h₁ h₂ => ?_
  by_cases k8 : k < 8
  · rw [List.getElem_append_left (by rw [ht]; omega), List.getElem_take]
  · rw [List.getElem_append_right (by rw [ht]; omega), Vector.getElem_toList, getElem_bytesAt,
      List.getD_eq_getElem _ _ (by omega)]
    congr 1; rw [ht]; omega

/-- A query of the squeeze item with state `st` is `squeezeQ st`. -/
theorem eq_squeezeQ {q : ByteArray} {st : Digest} (hm : fsCheck .squeeze q = true)
    (hs : stateIn q = some st) : q = squeezeQ st := by
  simp only [fsCheck, Bool.and_eq_true, beq_iff_eq] at hm
  obtain ⟨ht, hsz⟩ := hm
  simp only [stateIn, ht, hsz, and_true, or_true, ↓reduceIte, Option.some.injEq] at hs
  apply Merkle.byteArray_ext_toList
  rw [squeezeQ_data, split40 q hsz, ht, hs]

theorem fsCheck_absorb_or {it : Item} {q : ByteArray} (h : fsCheck it q = true) :
    it = .seed ∨ it = .squeeze ∨ ∃ len, it = .absorb len := by
  cases it <;> simp_all [fsCheck]

variable (D : Log → Log → Prop) (rnd : ℕ → Option (ℕ × ℕ))

theorem pRoundG_seed (L : Log) (e : ByteArray × Digest) (h0 : rnd 0 = none) :
    pRoundG D rnd L [e] = 0 := by
  simp [pRoundG, h0]

variable {D rnd}

end Local

end FR.Snd

end

/-! ## From `FRSoundnessFrChain` (25 declarations) -/

section

namespace FR.Snd.G

open RecursionFast FR.Merkle

open scoped NNReal

/-- **A Fiat–Shamir item list** for the chains (3.x: `fsItems`; revision 4.1: `seq4`'s). -/
class FsSeq where
  fs : List Item
  one_le : 1 ≤ fs.length

variable [FsSeq]

/-- **The entries follow the Fiat–Shamir items**: a seed first, at most `|FsSeq.fs|` entries, each
later entry with the previous answer as its state and the tag and length of its item. -/
def Matches (es : Log) : Prop :=
  (es.head?.map fun e => fsCheck .seed e.1) = some true ∧ ∃ hl : es.length ≤ FsSeq.fs.length,
    ∀ i (hi : i + 1 < es.length), stateIn es[i + 1].1 = some es[i].2 ∧
      fsCheck (FsSeq.fs[i + 1]'(by omega)) es[i + 1].1 = true

/-- **A chain of `L`**: an entry index whose forest path, read as entries, `Matches`. -/
def IsChain (L : Log) (j : ℕ) : Prop := j < L.length ∧ Matches (entriesOf L (pathOf L j))

noncomputable instance (L : Log) : DecidablePred (IsChain L) := Classical.decPred _

/-- The indices of `L` that are chains. -/
noncomputable def chains (L : Log) : List ℕ :=
  (List.range L.length).filter fun j => decide (IsChain L j)

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

/-- `Matches` extends by an entry linked to the last answer and matching the next item. -/
theorem matches_append {es : Log} {x : ByteArray × Digest} (h : Matches es)
    (hl' : es.length < FsSeq.fs.length) (hy : ∃ y, es.getLast? = some y ∧ stateIn x.1 = some y.2)
    (hmatch : fsCheck (FsSeq.fs[es.length]'hl') x.1 = true) : Matches (es ++ [x]) := by
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
      have : FsSeq.fs[i + 1]'(by omega) = FsSeq.fs[es.length]'hl' := by congr 1
      rw [this]; exact hmatch

section Potential

variable (D : Log → Log → Prop) (φ : Log → Log → ℝ≥0)

/-- **`Esc`**: some chain of `L` escapes at its last entry. -/
def EscG (L : Log) : Prop := ∃ j ∈ chains L, EscAtG D (L₀ L j) (entriesOf L (pathOf L j))

/-- The sum of the frontier charges over the chains of `L`. -/
noncomputable def sumG (L : Log) : ℝ≥0 := ((chains L).map (termG φ L)).sum

open Classical in
/-- **The potential** (§5.1): `1` on a bad or escaped log, else the frontier charges. -/
noncomputable def muG (L : Log) : ℝ≥0 := if Bad L ∨ EscG D L then 1 else sumG φ L

theorem muG_empty : muG D φ [] = 0 := by
  have hc : chains ([] : Log) = [] := rfl
  have he : ¬ EscG D [] := by rintro ⟨j, hj, -⟩; simp [hc] at hj
  have hb := not_bad_nil
  rw [muG, ite_eq_right (by tauto), sumG, hc]
  rfl

theorem muG_lt_one {L : Log} (h : muG D φ L < 1) : ¬ Bad L ∧ ¬ EscG D L := by
  by_contra hc
  rw [muG, ite_eq_left (by tauto)] at h
  exact lt_irrefl _ h

variable {D φ}

section Step

variable {L : Log} {q : ByteArray} {a : Digest}

/-- The sum over the chains of an extended (non-bad) log: the old chains, then the new entry. -/
theorem sumG_append (hb : ¬ Bad (L ++ [(q, a)])) :
    sumG φ (L ++ [(q, a)]) = ((chains L).map (termG φ (L ++ [(q, a)]))).sum +
      (if IsChain (L ++ [(q, a)]) L.length then termG φ (L ++ [(q, a)]) L.length else 0) := by
  rw [sumG, chains_append hb, List.map_append, List.sum_append]
  split_ifs <;> simp

/-- An escape after appending a non-bad entry is at the new entry. -/
theorem escG_append (hb : ¬ Bad (L ++ [(q, a)])) (he : ¬ EscG D L)
    (h : EscG D (L ++ [(q, a)])) :
    IsChain (L ++ [(q, a)]) L.length ∧
      EscAtG D L (entriesOf (L ++ [(q, a)]) (pathOf (L ++ [(q, a)]) L.length)) := by
  obtain ⟨j, hj, hesc⟩ := h
  rw [chains_append hb, List.mem_append] at hj
  rcases hj with hj | hj
  · have hjL : j < L.length := (mem_chains.mp hj).1
    rw [L₀_append hjL, entriesOf_pathOf_append hb hjL] at hesc
    exact absurd ⟨j, hj, hesc⟩ he
  · split_ifs at hj with hc
    · simp only [List.mem_singleton] at hj
      subst hj
      rw [L₀_new] at hesc
      exact ⟨hc, hesc⟩
    · simp at hj

/-- The new entry of a seed chain is charged nothing and cannot escape. -/
theorem new_seed (hseed : ∀ L₀ e, Matches [e] → φ L₀ [e] = 0) (hb : ¬ Bad (L ++ [(q, a)]))
    (hn : (stateIn q).bind (ansIdx L) = none) (hc : IsChain (L ++ [(q, a)]) L.length) :
    termG φ (L ++ [(q, a)]) L.length = 0 ∧
      ¬ EscAtG D L (entriesOf (L ++ [(q, a)]) (pathOf (L ++ [(q, a)]) L.length)) := by
  classical
  have hpath := back_new hb
  rw [hn] at hpath
  have hes : entriesOf (L ++ [(q, a)]) (pathOf (L ++ [(q, a)]) L.length) = [(q, a)] := by
    rw [hpath]; simp [entriesOf]
  have hm := hc.2
  rw [hes] at hm
  refine ⟨?_, ?_⟩
  · unfold termG; rw [hes, hseed _ _ hm]; simp
  · rw [hes]; rintro ⟨h2, -⟩; simp at h2

end Step

open Classical in
/-- **`muG_step`**: the contract's `step` law for the potential `muG D φ`, with error the H row's
`badCount / 2^256` plus `δ`, from the local inequality `hloc` on one chain `i` of a non-bad log and
one fresh query whose state is `i`'s answer, and `hseed`. -/
theorem muG_step (δ : ℝ≥0)
    (hseed : ∀ L₀ e, Matches [e] → φ L₀ [e] = 0)
    (hloc : ∀ (L : Log) (i : ℕ) (q : ByteArray), ¬ Bad L → IsChain L i →
      q ∉ L.map Prod.fst → stateIn q = some L[i]!.2 →
      ∑ a : Digest, (if Matches (entriesOf L (pathOf L i) ++ [(q, a)]) then
          (if EscAtG D L (entriesOf L (pathOf L i) ++ [(q, a)]) then 1 else 0) +
            φ L (entriesOf L (pathOf L i) ++ [(q, a)]) else 0) ≤
        2 ^ 256 * ((if q = squeezeQ L[i]!.2 then φ (L₀ L i) (entriesOf L (pathOf L i)) else 0) +
          δ))
    {L : Log} {q : ByteArray} (hl : L.length < logCap) (hμ : muG D φ L < 1)
    (hq : q ∉ L.map Prod.fst) :
    ∑ a : Digest, muG D φ (L ++ [(q, a)]) ≤
      (muG D φ L + ((badCount : ℝ≥0) / 2 ^ 256 + δ)) * 2 ^ 256 := by
  obtain ⟨hbL, heL⟩ := muG_lt_one D φ hμ
  have hX : muG D φ L = sumG φ L := by rw [muG, ite_eq_right (by tauto)]
  set X := sumG φ L with hXdef
  set B : ℝ≥0 := (badCount : ℝ≥0)
  obtain ⟨c, nt, hcX, hpt, hnt⟩ : ∃ (c : ℝ≥0) (nt : Digest → ℝ≥0), c ≤ X ∧
      (∀ a, ¬ Bad (L ++ [(q, a)]) → muG D φ (L ++ [(q, a)]) + c ≤ X + nt a) ∧
      ∑ a, nt a ≤ 2 ^ 256 * (c + δ) := by
    have hold : ∀ (c : ℝ≥0), (((chains L).map fun j =>
        if q = squeezeQ L[j]!.2 then φ (L₀ L j) (entriesOf L (pathOf L j)) else 0).sum = c) →
        ∀ a, ¬ Bad (L ++ [(q, a)]) →
          ((chains L).map (termG φ (L ++ [(q, a)]))).sum + c = X := by
      intro c hc a hb
      rw [← hc, ← List.sum_map_add, hXdef, sumG]
      congr 1
      apply List.map_congr_left
      intro j hj
      exact termG_append hq hb (mem_chains.mp hj).1
    cases hi : (stateIn q).bind (ansIdx L) with
    | none =>
      refine ⟨0, fun _ => 0, zero_le, fun a hb => ?_, by simp⟩
      have hc0 := sum_map_zero (l := chains L) (fun j =>
          if q = squeezeQ L[j]!.2 then φ (L₀ L j) (entriesOf L (pathOf L j)) else 0)
        (fun j hj => by
          have hjL := (mem_chains.mp hj).1
          rw [ite_eq_right]
          intro hs
          rw [istar_of_squeeze hbL hjL hs] at hi
          cases hi)
      have hsum := hold 0 hc0 a hb
      have hesc : ¬ EscG D (L ++ [(q, a)]) := fun h => by
        obtain ⟨hc, hesc⟩ := escG_append hb heL h
        exact (new_seed hseed hb hi hc).2 hesc
      rw [muG, ite_eq_right (by tauto), sumG_append hb, add_zero, add_zero]
      split_ifs with hc
      · rw [(new_seed (D := D) hseed hb hi hc).1, add_zero, ← hsum, add_zero]
      · rw [add_zero, ← hsum, add_zero]
    | some i =>
      obtain ⟨hiL, hst⟩ := lt_of_ansIdx hi
      set es := entriesOf L (pathOf L i) with hes
      let c : ℝ≥0 := if IsChain L i ∧ q = squeezeQ L[i]!.2 then φ (L₀ L i) es else 0
      let nt : Digest → ℝ≥0 := fun a => if Matches (es ++ [(q, a)]) then
          (if EscAtG D L (es ++ [(q, a)]) then 1 else 0) + φ L (es ++ [(q, a)]) else 0
      have hc : ((chains L).map fun j =>
          if q = squeezeQ L[j]!.2 then φ (L₀ L j) (entriesOf L (pathOf L j)) else 0).sum = c := by
        rw [sum_map_single (chains_nodup L) _ i]
        · by_cases h1 : IsChain L i
          · rw [ite_eq_left (mem_chains.mpr h1)]; simp only [c, h1, true_and]; rfl
          · rw [ite_eq_right (fun h => h1 (mem_chains.mp h))]; simp only [c, h1, false_and]; rfl
        · intro j hj hji
          have hjL := (mem_chains.mp hj).1
          rw [ite_eq_right]
          intro hs
          rw [istar_of_squeeze hbL hjL hs] at hi
          exact hji (Option.some.inj hi)
      refine ⟨c, nt, ?_, fun a hb => ?_, ?_⟩
      · simp only [c]
        split_ifs with hh
        · obtain ⟨hci, hs⟩ := hh
          have hmem : L[i]! ∈ L := by rw [getElem!_pos L i hiL]; exact List.getElem_mem hiL
          have hterm : termG φ L i = φ (L₀ L i) es := by
            unfold termG; rw [ite_eq_left ⟨hmem, hs ▸ hq⟩]
          rw [← hterm, hXdef, sumG]
          exact List.single_le_sum (fun _ _ => zero_le) _
            (List.mem_map_of_mem (mem_chains.mpr hci))
        · exact zero_le
      · have hsum := hold c hc a hb
        have hesn := entriesOf_new hb hi
        have hnew : (if EscG D (L ++ [(q, a)]) then 1 else 0) +
            (if IsChain (L ++ [(q, a)]) L.length then termG φ (L ++ [(q, a)]) L.length else 0) ≤
            nt a := by
          by_cases hc' : IsChain (L ++ [(q, a)]) L.length
          · have hm : Matches (es ++ [(q, a)]) := by have := hc'.2; rwa [hesn] at this
            simp only [nt, ite_eq_left hm, ite_eq_left hc']
            gcongr
            · split_ifs with h1 h2 h2
              · exact le_rfl
              · obtain ⟨-, h3⟩ := escG_append hb heL h1
                rw [hesn] at h3
                exact absurd h3 h2
              · exact zero_le
              · exact le_rfl
            · unfold termG
              rw [L₀_new, hesn]
              split_ifs
              · exact le_rfl
              · exact zero_le
          · have : ¬ EscG D (L ++ [(q, a)]) := fun h => hc' (escG_append hb heL h).1
            simp [this, hc']
        calc muG D φ (L ++ [(q, a)]) + c
            ≤ ((if EscG D (L ++ [(q, a)]) then 1 else 0) + sumG φ (L ++ [(q, a)])) + c := by
              gcongr
              rw [muG]
              split_ifs with h1 h2
              · exact le_add_right le_rfl
              · tauto
              · tauto
              · exact le_add_self
          _ = ((chains L).map (termG φ (L ++ [(q, a)]))).sum + c +
                ((if EscG D (L ++ [(q, a)]) then 1 else 0) +
                  (if IsChain (L ++ [(q, a)]) L.length then termG φ (L ++ [(q, a)]) L.length
                    else 0)) := by rw [sumG_append hb]; ring
          _ ≤ X + nt a := by rw [hsum]; gcongr
      · by_cases hci : IsChain L i
        · have hloc' := hloc L i q hbL hci hq hst
          have hcc : c = if q = squeezeQ L[i]!.2 then φ (L₀ L i) es else 0 := by
            simp only [c, hci, true_and]
          rw [hcc]
          exact hloc'
        · have : ∀ a, nt a = 0 := fun a => by
            simp only [nt]
            rw [ite_eq_right]
            intro hm
            exact hci ⟨hiL, matches_of_append (by
              rw [← List.length_pos_iff, length_entriesOf, List.length_pos_iff]
              exact pathOf_ne_nil L i) hm⟩
          simp [this]
  have hpt' : ∀ a, muG D φ (L ++ [(q, a)]) ≤
      (if Bad (L ++ [(q, a)]) then 1 else 0) + ((X - c) + nt a) := by
    intro a
    by_cases hb : Bad (L ++ [(q, a)])
    · rw [muG, ite_eq_left (Or.inl hb), ite_eq_left hb]; exact le_self_add
    · rw [ite_eq_right hb, zero_add]
      have h := hpt a hb
      have : (X - c) + c = X := tsub_add_cancel_of_le hcX
      rw [← this, add_assoc, add_comm c, ← add_assoc] at h
      exact le_of_add_le_add_right h
  calc ∑ a : Digest, muG D φ (L ++ [(q, a)])
      ≤ ∑ a : Digest, ((if Bad (L ++ [(q, a)]) then 1 else 0) + ((X - c) + nt a)) :=
        Finset.sum_le_sum fun a _ => hpt' a
    _ = (∑ a : Digest, (if Bad (L ++ [(q, a)]) then 1 else 0 : ℝ≥0)) + 2 ^ 256 * (X - c) +
          ∑ a, nt a := by
        rw [Finset.sum_add_distrib, Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ,
          fintype_card_digest, nsmul_eq_mul]
        push_cast
        ring
    _ ≤ B + 2 ^ 256 * (X - c) + 2 ^ 256 * (c + δ) := by
        gcongr
        exact card_bad_le hbL hq hl
    _ = (muG D φ L + (B / 2 ^ 256 + δ)) * 2 ^ 256 := by
        rw [hX, add_mul, add_mul, div_mul_cancel₀ _ (by positivity)]
        have : (X - c) + c = X := tsub_add_cancel_of_le hcX
        calc B + 2 ^ 256 * (X - c) + 2 ^ 256 * (c + δ)
            = B + 2 ^ 256 * ((X - c) + c) + 2 ^ 256 * δ := by ring
          _ = X * 2 ^ 256 + (B + δ * 2 ^ 256) := by rw [this]; ring

end Potential

section Local

/-- **`Matches` extends exactly by the next item, linked to the last answer.** -/
theorem matches_append_iff {es : Log} (hm : Matches es) (x : ByteArray × Digest) :
    Matches (es ++ [x]) ↔ ∃ hl : es.length < FsSeq.fs.length,
      stateIn x.1 = some (lastAns es) ∧ fsCheck (FsSeq.fs[es.length]'hl) x.1 = true := by
  have hne := matches_ne_nil hm
  have hpos : 0 < es.length := List.length_pos_iff.mpr hne
  have hla : lastAns es = es[es.length - 1].2 := by
    simp [lastAns, List.getLast?_eq_getElem?,
      List.getElem?_eq_getElem (show es.length - 1 < es.length by omega)]
  constructor
  · rintro ⟨-, hl, H⟩
    have hl' : es.length < FsSeq.fs.length := by simp at hl; omega
    obtain ⟨h1, h2⟩ := H (es.length - 1) (by simp; omega)
    have hx : (es ++ [x])[es.length - 1 + 1]'(by simp; omega) = x := by
      simp [show es.length - 1 + 1 = es.length by omega]
    have hy : (es ++ [x])[es.length - 1]'(by
        simp only [List.length_append, List.length_singleton]; omega) =
        es[es.length - 1] :=
      List.getElem_append_left _
    have hf : FsSeq.fs[es.length - 1 + 1]'(by omega) = FsSeq.fs[es.length]'hl' := by
      congr 1; omega
    rw [hx, hy] at h1; rw [hx, hf] at h2
    exact ⟨hl', by rw [hla]; exact h1, h2⟩
  · rintro ⟨hl, hs, hc⟩
    refine matches_append hm hl ⟨es[es.length - 1], ?_, by rw [hs, hla]⟩ hc
    rw [List.getLast?_eq_getElem?, List.getElem?_eq_getElem]

/-- On the squeeze positions after `s0`, a matching chain is the formal extension of its first
`s0 + 1` entries by its later answers. -/
theorem ext_take {es : Log} (hm : Matches es) {s0 : ℕ} (hs : s0 < es.length)
    (hsq : ∀ p, s0 < p → p < es.length → FsSeq.fs[p]? = some .squeeze) :
    es = ext (es.take (s0 + 1)) ((es.drop (s0 + 1)).map Prod.snd) := by
  obtain ⟨-, hl, H⟩ := hm
  suffices Hk : ∀ k, s0 + 1 + k ≤ es.length →
      es.take (s0 + 1 + k) = ext (es.take (s0 + 1)) (((es.take (s0 + 1 + k)).drop (s0 + 1)).map
        Prod.snd) by
    have := Hk (es.length - (s0 + 1)) (by omega)
    rwa [show s0 + 1 + (es.length - (s0 + 1)) = es.length by omega, List.take_length] at this
  intro k
  induction k with
  | zero => intro _; simp [ext]
  | succ k ih =>
    intro hk
    have hn : s0 + 1 + k < es.length := by omega
    rw [show s0 + 1 + (k + 1) = s0 + 1 + k + 1 by omega, List.take_add_one,
      List.getElem?_eq_getElem hn, Option.toList_some, List.drop_append_of_le_length
        (by simp; omega), List.map_append, List.map_cons, List.map_nil, ext_append, ← ih (by omega)]
    simp only [ext1]
    congr 1
    obtain ⟨hst, hck⟩ := H (s0 + k) (by omega)
    have hsqk := hsq (s0 + k + 1) (by omega) (by omega)
    rw [List.getElem?_eq_getElem (by omega), Option.some.injEq] at hsqk
    rw [hsqk] at hck
    have hla : lastAns (es.take (s0 + 1 + k)) = es[s0 + k].2 := by
      rw [lastAns, List.getLast?_eq_getElem?, List.length_take,
        show min (s0 + 1 + k) es.length - 1 = s0 + k by omega, List.getElem?_take_of_lt
          (by omega), List.getElem?_eq_getElem (by omega)]
      rfl
    rw [hla, ← eq_squeezeQ hck hst]
    have heq : es[s0 + k + 1]'(by omega) = es[s0 + 1 + k] := by congr 1; omega
    rw [heq]

/-- **The multi-squeeze phases**: `rnd p = some (s0, r)` places position `p` among the `r` squeezes
after the entry `s0`, and every position of the phase is a squeeze of the same phase. -/
def RndOK (rnd : ℕ → Option (ℕ × ℕ)) : Prop :=
  ∀ p s0 r, rnd p = some (s0, r) → s0 < p ∧ p ≤ s0 + r ∧
    ∀ p', s0 < p' → p' ≤ s0 + r → FsSeq.fs[p']? = some .squeeze ∧ rnd p' = some (s0, r)

variable (D : Log → Log → Prop) (rnd : ℕ → Option (ℕ × ℕ))

variable {D rnd}

open Classical in
/-- **`hloc_of`**: `muG_step`'s local inequality for the charge `pRoundG D rnd`, from
* `habs`: an absorb never undooms;
* `hmid`: a middle answer of a multi-squeeze phase neither dooms nor undooms;
* `hsingle`: a single squeeze escapes on at most `N ≤ 2^256 δ` answers;
* `hround`: a multi-squeeze phase's escape count from its entry is at most `δ`;
* `hstab`: on a non-bad log, `D` reads the same off the log before a chain's last entry and off the
  whole log, on the formal extensions inside a multi-squeeze phase (`StabExt`). -/
theorem hloc_of (hrnd : RndOK rnd) (δ : ℝ≥0) (N : ℕ) (hN : (N : ℝ≥0) ≤ 2 ^ 256 * δ)
    (habs : ∀ L es x len, Matches (es ++ [x]) → FsSeq.fs[es.length]? = some (.absorb len) →
      D L es → D L (es ++ [x]))
    (hmid : ∀ L es x s0 r, Matches (es ++ [x]) → rnd es.length = some (s0, r) →
      es.length < s0 + r → (D L (es ++ [x]) ↔ D L es))
    (hsingle : ∀ L es, Matches es → FsSeq.fs[es.length]? = some .squeeze → rnd es.length = none →
      (Finset.univ.filter fun a => D L es ∧ ¬ D L (ext1 es a)).card ≤ N)
    (hround : ∀ L es₀ s0 r, Matches es₀ → es₀.length = s0 + 1 →
      rnd (s0 + 1) = some (s0, r) → condCount D L es₀ r [] ≤ δ)
    (hstab : ∀ L i, ¬ Bad L → IsChain L i → ∀ X, StabExt rnd (entriesOf L (pathOf L i)) X →
      (D (L.take i) X ↔ D L X))
    (L : Log) (i : ℕ) (q : ByteArray) (hb : ¬ Bad L) (hci : IsChain L i)
    (hst : stateIn q = some L[i]!.2) :
    ∑ a : Digest, (if Matches (entriesOf L (pathOf L i) ++ [(q, a)]) then
        (if EscAtG D L (entriesOf L (pathOf L i) ++ [(q, a)]) then 1 else 0) +
          pRoundG D rnd L (entriesOf L (pathOf L i) ++ [(q, a)]) else 0) ≤
      2 ^ 256 * ((if q = squeezeQ L[i]!.2 then
        pRoundG D rnd (L₀ L i) (entriesOf L (pathOf L i)) else 0) + δ) := by
  have hstab' := hstab L i hb hci
  generalize hes : entriesOf L (pathOf L i) = es at hstab' ⊢
  have hm : Matches es := hes ▸ hci.2
  have hla : lastAns es = L[i]!.2 := lastAns_of_getLast? (hes ▸ entriesOf_getLast? L i)
  have hne := matches_ne_nil hm
  have hp1 : 1 ≤ es.length := List.length_pos_iff.mpr hne
  have hlen : ∀ x : ByteArray × Digest, (es ++ [x]).length - 1 = es.length := fun x => by simp
  by_cases hex : ∃ hl : es.length < FsSeq.fs.length, fsCheck (FsSeq.fs[es.length]'hl) q = true
  swap
  · have : ∀ a, ¬ Matches (es ++ [(q, a)]) := fun a h => by
      obtain ⟨hl, -, hc⟩ := (matches_append_iff hm _).mp h; exact hex ⟨hl, hc⟩
    simp only [this, ite_false, Finset.sum_const_zero]; exact zero_le
  obtain ⟨hl, hc⟩ := hex
  have hM : ∀ a, Matches (es ++ [(q, a)]) := fun a =>
    (matches_append_iff hm _).mpr ⟨hl, by rw [hla]; exact hst, hc⟩
  simp only [hM, ite_true]
  have hit : FsSeq.fs[es.length]? = some (FsSeq.fs[es.length]'hl) := List.getElem?_eq_getElem hl
  have hpr0 : ∀ L₁ x, rnd es.length = none → pRoundG D rnd L₁ (es ++ [x]) = 0 := by
    intro L₁ x hr; unfold pRoundG; rw [hlen, hr]
  rcases fsCheck_absorb_or hc with h | h | ⟨len, h⟩
  · rw [h] at hc; rw [stateIn_of_seed hc] at hst; cases hst
  · -- a squeeze
    rw [h] at hc hit
    have hq : q = squeezeQ L[i]!.2 := eq_squeezeQ hc hst
    subst hq
    rw [ite_eq_left rfl]
    have hext1 : ∀ a, es ++ [(squeezeQ L[i]!.2, a)] = ext1 es a := fun a => by rw [ext1, hla]
    cases hr : rnd es.length with
    | none =>
      calc ∑ a, ((if EscAtG D L (es ++ [(squeezeQ L[i]!.2, a)]) then 1 else 0) +
              pRoundG D rnd L (es ++ [(squeezeQ L[i]!.2, a)]))
          ≤ ∑ a, (if D L es ∧ ¬ D L (ext1 es a) then 1 else 0 : ℝ≥0) := by
            refine Finset.sum_le_sum fun a _ => ?_
            rw [hpr0 _ _ hr, add_zero]
            split_ifs with h1 h2 h2
            · exact le_rfl
            · exfalso; obtain ⟨-, hd, hnd⟩ := h1
              rw [List.dropLast_concat, hext1] at *
              exact h2 ⟨hd, hnd⟩
            · exact zero_le
            · exact le_rfl
        _ = ((Finset.univ.filter fun a => D L es ∧ ¬ D L (ext1 es a)).card : ℝ≥0) := by
            rw [Finset.sum_boole]
        _ ≤ N := by exact_mod_cast hsingle L es hm hit hr
        _ ≤ 2 ^ 256 * δ := hN
        _ ≤ 2 ^ 256 * (pRoundG D rnd (L₀ L i) es + δ) := by gcongr; exact le_add_self
    | some sr =>
      obtain ⟨s0, r⟩ := sr
      obtain ⟨hs0, hpr, hspec⟩ := hrnd _ _ _ hr
      have hes' : es = ext (es.take (s0 + 1)) ((es.drop (s0 + 1)).map Prod.snd) :=
        ext_take hm (by omega) (fun p h1 h2 => (hspec p h1 (by omega)).1)
      have hes0len : (es.take (s0 + 1)).length = s0 + 1 := by simp; omega
      have hnew : ∀ a, es ++ [(squeezeQ L[i]!.2, a)] =
          ext (es.take (s0 + 1)) ((es.drop (s0 + 1)).map Prod.snd ++ [a]) := by
        intro a; rw [ext_append, ← hes', hext1]
      have hterm : ∀ a, (if EscAtG D L (es ++ [(squeezeQ L[i]!.2, a)]) then 1 else 0) +
          pRoundG D rnd L (es ++ [(squeezeQ L[i]!.2, a)]) =
          condCount D L (es.take (s0 + 1)) r ((es.drop (s0 + 1)).map Prod.snd ++ [a]) := by
        intro a
        have hpRnew : pRoundG D rnd L (es ++ [(squeezeQ L[i]!.2, a)]) =
            if es.length - s0 < r then
              condCount D L (es.take (s0 + 1)) r ((es.drop (s0 + 1)).map Prod.snd ++ [a])
            else 0 := by
          unfold pRoundG
          rw [hlen, hr]
          simp only
          rw [List.take_append_of_le_length (by omega),
            List.drop_append_of_le_length (by omega), List.map_append]
          rfl
        by_cases hmidp : es.length < s0 + r
        · rw [ite_eq_right, zero_add, hpRnew, ite_eq_left (by omega)]
          rintro ⟨-, hd, hnd⟩
          rw [List.dropLast_concat] at hd
          exact hnd ((hmid L es _ s0 r (hM _) hr hmidp).mpr hd)
        · rw [hpRnew, ite_eq_right (show ¬ (es.length - s0 < r) by omega), add_zero,
            condCount_last D _ _ (by simp; omega), hnew]
      rw [Finset.sum_congr rfl (fun a _ => hterm a), condCount_split D _ _ (by simp; omega)]
      gcongr
      by_cases hfirst : es.length = s0 + 1
      · have htk : es.take (s0 + 1) = es := List.take_of_length_le (by omega)
        have hpre : (es.drop (s0 + 1)).map Prod.snd = [] := by
          rw [List.drop_of_length_le (by omega)]; rfl
        rw [hpre]
        refine le_trans ?_ le_add_self
        refine hround L _ s0 r (by rw [htk]; exact hm) hes0len ?_
        exact (hspec (s0 + 1) (by omega) (by omega)).2
      · -- the charge before the new answer, read off the charging log (`hstab`)
        have hcc : condCount D L (es.take (s0 + 1)) r ((es.drop (s0 + 1)).map Prod.snd) =
            condCount D (L₀ L i) (es.take (s0 + 1)) r ((es.drop (s0 + 1)).map Prod.snd) := by
          have hX : ∀ as', as'.length ≤ r →
              (D L (ext (es.take (s0 + 1)) as') ↔ D (L₀ L i) (ext (es.take (s0 + 1)) as')) :=
            fun as' h => (hstab' _ ⟨s0, r, as', (hspec (s0 + 1) (by omega) (by omega)).2,
              by omega, h, rfl⟩).symm
          have hpl : ((es.drop (s0 + 1)).map Prod.snd).length = es.length - (s0 + 1) := by simp
          unfold condCount extCount
          congr 3
          refine Finset.filter_congr fun v _ => ?_
          set as := (es.drop (s0 + 1)).map Prod.snd ++ List.ofFn v with has
          have hal : as.length = r := by
            rw [has, List.length_append, List.length_ofFn, hpl]; omega
          have hne : as ≠ [] := by
            intro h; rw [h] at hal; simp at hal; omega
          simp only [EscAtG]
          rw [ext_dropLast _ hne, hX _ hal.le, hX _ (by simp; omega)]
        have hp : pRoundG D rnd (L₀ L i) es =
            condCount D (L₀ L i) (es.take (s0 + 1)) r ((es.drop (s0 + 1)).map Prod.snd) := by
          unfold pRoundG
          rw [(hspec (es.length - 1) (by omega) (by omega)).2]
          simp only
          rw [ite_eq_left (by omega)]
        rw [hcc, hp]; exact le_self_add
  · -- an absorb: no escape, no charge
    rw [h] at hit
    have hr : rnd es.length = none := by
      cases hr : rnd es.length with
      | none => rfl
      | some sr =>
        obtain ⟨h1, h2, hs⟩ := hrnd _ _ _ hr
        rw [(hs _ h1 h2).1] at hit; cases hit
    have hz : ∀ a, (if EscAtG D L (es ++ [(q, a)]) then 1 else 0) +
        pRoundG D rnd L (es ++ [(q, a)]) = (0 : ℝ≥0) := by
      intro a
      rw [hpr0 _ _ hr, add_zero, ite_eq_right]
      rintro ⟨-, hd, hnd⟩
      rw [List.dropLast_concat] at hd
      exact hnd (habs L es _ len (hM a) hit hd)
    simp only [hz, Finset.sum_const_zero]; exact zero_le

open Classical in
/-- **`muG_step_of`**: the contract's `step` law for `muG D (pRoundG D rnd)` from the per-position
facts of `hloc_of` (`rnd 0 = none`: the seed is in no phase). -/
theorem muG_step_of (hrnd : RndOK rnd) (h0 : rnd 0 = none) (δ : ℝ≥0) (N : ℕ)
    (hN : (N : ℝ≥0) ≤ 2 ^ 256 * δ)
    (habs : ∀ L es x len, Matches (es ++ [x]) → FsSeq.fs[es.length]? = some (.absorb len) →
      D L es → D L (es ++ [x]))
    (hmid : ∀ L es x s0 r, Matches (es ++ [x]) → rnd es.length = some (s0, r) →
      es.length < s0 + r → (D L (es ++ [x]) ↔ D L es))
    (hsingle : ∀ L es, Matches es → FsSeq.fs[es.length]? = some .squeeze → rnd es.length = none →
      (Finset.univ.filter fun a => D L es ∧ ¬ D L (ext1 es a)).card ≤ N)
    (hround : ∀ L es₀ s0 r, Matches es₀ → es₀.length = s0 + 1 →
      rnd (s0 + 1) = some (s0, r) → condCount D L es₀ r [] ≤ δ)
    (hstab : ∀ L i, ¬ Bad L → IsChain L i → ∀ X, StabExt rnd (entriesOf L (pathOf L i)) X →
      (D (L.take i) X ↔ D L X))
    {L : Log} {q : ByteArray} (hl : L.length < logCap) (hμ : muG D (pRoundG D rnd) L < 1)
    (hq : q ∉ L.map Prod.fst) :
    ∑ a : Digest, muG D (pRoundG D rnd) (L ++ [(q, a)]) ≤
      (muG D (pRoundG D rnd) L + ((badCount : ℝ≥0) / 2 ^ 256 + δ)) * 2 ^ 256 :=
  muG_step δ (fun L₀ e _ => pRoundG_seed D rnd L₀ e h0)
    (fun L i q hb hci _ hst => hloc_of hrnd δ N hN habs hmid hsingle hround hstab L i q hb hci hst)
    hl hμ hq

end Local

end FR.Snd.G

end
