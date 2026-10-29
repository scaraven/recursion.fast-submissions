-- New for `flock-recursive` (BLUEPRINT §5.1; stage S-G13, route C1). A copy of `FRLog`'s chain part
-- and of `FRSoundnessDefs`' Parts A–C over an item list `FsSeq.fs` (3.x: `fsItems`), so that the
-- potential and its `step` law serve revision 4.1's sequence `seq4`. Proof text unchanged.
-- RET-2: the declarations revision 4.1 reads moved to `FRSoundnessCoreChain`.
import FRSoundnessDefs
import FRSoundnessCoreChain

/-!
# Chains and the potential over an arbitrary Fiat–Shamir item list (`FsSeq`)

`FRLog.Matches` and everything built on it (`IsChain`, `chains`, `muG`, `muG_step_of`, `hloc_of`)
read the global 3.x list `fsItems`. Revision 4.1 has one other list, `seq4`'s 482 items, for its
six SNARK programs. This module restates the chain part of `FRLog` and Parts A–C of
`FRSoundnessDefs` in namespace `FR.Snd.G` over a class `FsSeq` (the item list and `1 ≤ |fs|`),
with the same names and the same proofs; only `fsItems` reads `FsSeq.fs`. The parts that do not
read the item list (`Bad`, the forest `pathOf`, `entriesOf`, `OnFrontier`, `extCount`, `L₀`) are
`FR.Snd`'s and are used as they are.

**3.x is the instance `fs := fsItems`** (`fs3`): `matches_fs3`, `isChain_fs3`, `chains_fs3` and
`muG_fs3` are `rfl`.
-/

namespace FR.Snd.G
open RecursionFast FR.Merkle
open scoped NNReal

variable [FsSeq]

/-! ### Path facts -/

/-! ### Chains of an extended log -/

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
    exact FsSeq.one_le
  · simp [entriesOf] at hi

/-- **The new chain, converse** (extension case): an entry whose predecessor ends a chain `i` and
which matches the next item is a chain. -/
theorem isChain_new_of_extend {L : Log} {q : ByteArray} {a : Digest}
    (hb : ¬ Bad (L ++ [(q, a)])) {i : ℕ} (hp : (stateIn q).bind (ansIdx L) = some i)
    (hc : IsChain L i) (hl : (entriesOf L (pathOf L i)).length < FsSeq.fs.length)
    (hnext : fsCheck (FsSeq.fs[(entriesOf L (pathOf L i)).length]'hl) q = true) :
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

/-! ## Part A: the potential over chains (generic) -/

section Potential

variable (D : Log → Log → Prop) (φ : Log → Log → ℝ≥0)

/-- Control: a bad log has potential `1` (the self-answered squeeze of `bad_self_state`). -/
theorem muG_bad_self (st : Digest) : muG D φ [(squeezeQ st, st)] = 1 := by
  rw [muG, ite_eq_left (Or.inl (bad_self_state st))]

variable {D φ}

section Step

variable {L : Log} {q : ByteArray} {a : Digest}

end Step

end Potential

/-! ## Part B: the conditional count of a multi-answer phase

A phase of `r` squeezes (Z1, S1, Lr1, RS1, E1, P2, P3) is charged, after its first `i < r`
answers, the conditional probability of its escape over the missing answers (`condCount`); by
`extCount_split` the charges form a martingale (`condCount_split`), and after the last answer the
charge is the escape indicator (`condCount_last`). -/

section Ext

variable (D : Log → Log → Prop)

end Ext

/-! ## Part C: the local inequality from per-position facts (`hloc_of`)

The charge `pRoundG D rnd`: inside a multi-squeeze phase (`rnd p = some (s0, r)`: the `r` answers
`s0 + 1 … s0 + r` after the entry `s0`), after `1 ≤ k < r` answers, the conditional count of the
phase's escape; `0` elsewhere. `hloc_of` proves `muG_step`'s `hloc` for it from four per-position
facts and the stability `hstab` of `D` under the charging log (deviation 1 of part 1). -/

section Local

variable (D : Log → Log → Prop) (rnd : ℕ → Option (ℕ × ℕ))

variable {D rnd}

end Local

/-! ## 3.x is an instance -/

/-- 3.x's item list. -/
abbrev fs3 : FsSeq := ⟨fsItems, one_le_fsItems⟩

omit [FsSeq] in
theorem matches_fs3 (es : Log) : @Matches fs3 es ↔ Snd.Matches es := Iff.rfl
omit [FsSeq] in
theorem isChain_fs3 (L : Log) (j : ℕ) : @IsChain fs3 L j ↔ Snd.IsChain L j := Iff.rfl
omit [FsSeq] in
theorem chains_fs3 (L : Log) : @chains fs3 L = Snd.chains L := rfl
omit [FsSeq] in
theorem muG_fs3 (D : Log → Log → Prop) (φ : Log → Log → ℝ≥0) (L : Log) :
    @muG fs3 D φ L = Snd.muG D φ L := rfl

end FR.Snd.G
