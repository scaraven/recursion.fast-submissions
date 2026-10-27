-- New for `flock-recursive` (BLUEPRINT §5.1, §7; stage S-G). Part A follows
-- `submissions/spartan-srom/lean/SpartanSromSoundnessDefs.lean` and `SpartanSromSoundnessKSBase.lean`
-- Part A (this repository, `v4/flock-recursive` at `cf2f7b3`), with one change: a chain's charge
-- reads the log strictly before its **last** entry (`L₀ L j = L.take j`), not before its cut.
import FRLog

/-!
# The potential over chains and its `step` law (BLUEPRINT §5.1)

For a doom predicate `D L₀ es` and a per-chain charge `φ L₀ es` (functions of a log `L₀` and a
chain's entries `es`), the potential of §5.1 is

`μ L := if Bad L ∨ Esc L then 1 else Σ_{j ∈ chains L} [OnFrontier L L[j]] φ (L₀ L j) (es j)`

with `EscAt L₀ es := 2 ≤ |es| ∧ D L₀ es.dropLast ∧ ¬ D L₀ es`.

**`L₀ L j` is the log strictly before chain `j`'s last entry.** spartan-srom's prefix (the log
before the chain's commitment absorb) does not serve Flock: the commitments of levels `1 … 4` are
absorbed in the middle of the chain (phase `C` of level `i`), so their Merkle trees are read off a
later log. Old chains keep `L₀` when an entry is appended (`L₀_append`), and the new entry's chain
reads the whole old log (`L₀_new`). A row lemma compares `φ L (es ++ [x])` with `φ (L.take i) es`;
for a charge that reads trees only under caps absorbed in `es`, the two logs read the same trees
when `L` has no bad event (`FRMerkle.colL_prefix`): that is each row's obligation, not this
module's.

**`muG_step`** proves the contract's `step` law for `muG D φ` from one local inequality `hloc` on
one chain `i` of a non-bad log and one fresh query whose state is `i`'s answer, plus `hseed` (a
seed is charged nothing). The error is the H row's `badCount / 2^256` plus the rows' `δ`.
-/

namespace FR.Snd
open RecursionFast FR.Merkle
open scoped NNReal

/-! ## Part A: the potential over chains (generic) -/

/-- The log strictly before entry `j` (the prefix a chain ending at `j` is charged on). -/
def L₀ (L : Log) (j : ℕ) : Log := L.take j

section Potential

variable (D : Log → Log → Prop) (φ : Log → Log → ℝ≥0)

/-- **`EscAt`**: the chain `es` (of at least two entries) was doomed before its last entry and is
not after it, both on the log `L₀`. -/
def EscAtG (L₀ es : Log) : Prop := 2 ≤ es.length ∧ D L₀ es.dropLast ∧ ¬ D L₀ es

/-- **`Esc`**: some chain of `L` escapes at its last entry. -/
def EscG (L : Log) : Prop := ∃ j ∈ chains L, EscAtG D (L₀ L j) (entriesOf L (pathOf L j))

open Classical in
/-- The charge of chain `j` in `L`: its `φ` if its last entry is on the frontier, else `0`. -/
noncomputable def termG (L : Log) (j : ℕ) : ℝ≥0 :=
  if OnFrontier L L[j]! then φ (L₀ L j) (entriesOf L (pathOf L j)) else 0

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

/-- Control: a bad log has potential `1` (the self-answered squeeze of `bad_self_state`). -/
theorem muG_bad_self (st : Digest) : muG D φ [(squeezeQ st, st)] = 1 := by
  rw [muG, ite_eq_left (Or.inl (bad_self_state st))]

theorem muG_lt_one {L : Log} (h : muG D φ L < 1) : ¬ Bad L ∧ ¬ EscG D L := by
  by_contra hc
  rw [muG, ite_eq_left (by tauto)] at h
  exact lt_irrefl _ h

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

/-- **The H row** (§5.2): the bad fraction of a fresh answer is at most `2^-142`. -/
theorem badCount_frac_le : (badCount : ℝ≥0) / 2 ^ 256 ≤ (2 : ℝ≥0)⁻¹ ^ 142 := by
  rw [div_le_iff₀ (by positivity), inv_pow, ← div_eq_inv_mul,
    le_div_iff₀ (by positivity), badCount]
  norm_num

open Classical in
/-- `Bad` of a log with an entry appended, as a sum of indicators, is at most the H row's count. -/
theorem card_bad_le {L : Log} {q : ByteArray} (hb : ¬ Bad L) (hq : q ∉ L.map Prod.fst)
    (hl : L.length < logCap) :
    (∑ a : Digest, (if Bad (L ++ [(q, a)]) then 1 else 0 : ℝ≥0)) ≤ (badCount : ℝ≥0) := by
  rw [Finset.sum_boole]
  exact_mod_cast bad_step_frac hb hq hl

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

/-! ## Part B: the conditional count of a multi-answer phase

A phase of `r` squeezes (Z1, S1, Lr1, RS1, E1, P2, P3) is charged, after its first `i < r`
answers, the conditional probability of its escape over the missing answers (`condCount`); by
`extCount_split` the charges form a martingale (`condCount_split`), and after the last answer the
charge is the escape indicator (`condCount_last`). -/

section Ext

/-- The answer of the last entry (`default` for the empty list). -/
def lastAns (es : Log) : Digest := (es.getLast?.map Prod.snd).getD default

/-- The chain extended by the squeeze of its last answer, answered `a`. -/
def ext1 (es : Log) (a : Digest) : Log := es ++ [(squeezeQ (lastAns es), a)]

/-- The formal extension of `es` by the answers `as`, each a squeeze of the previous answer. -/
def ext (es : Log) (as : List Digest) : Log := as.foldl ext1 es

variable (D : Log → Log → Prop)

open Classical in
/-- **`condCount`**: the conditional count of the escape `EscAt (ext es₀ ·)` of a phase of `r`
answers entered at `es₀`, given its first answers `pre`, as a fraction of `2^256` per missing
answer. -/
noncomputable def condCount (L₀ es₀ : Log) (r : ℕ) (pre : List Digest) : ℝ≥0 :=
  (extCount (fun as => EscAtG D L₀ (ext es₀ as)) pre (r - pre.length) : ℝ≥0) /
    2 ^ (256 * (r - pre.length))

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

end FR.Snd
