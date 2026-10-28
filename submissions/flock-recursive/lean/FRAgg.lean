-- New for `flock-recursive` (BLUEPRINT revision 4.0, B-11; §10 changes 25 (b); stage S-0′).
import FRSegment
import RecursionFast.Library.Oracle

/-!
# The aggregate leaf `A` and its verifier `V_A` (B-11)

A step's new chain is proved by `k ≤ 4` segment SNARKs assembled into **one signed proof**
`(π_A, tr_A, σ_A)`; it has no SNARK of its own.

* **Format.** `π_A = hdrA ‖ π₁ ‖ … ‖ π_k`, `hdrA = 'A' ‖ k ‖ 0^6 ‖ enc64 n ‖ e` (48 bytes), every
  `πᵢ` a segment proof of `segSize` bytes (`piSizeOf seq4 = 798,192`); `tr_A = tr₁ ‖ … ‖ tr_k`, one
  trace signed once. A segment's queries are its `seq4` item sequence (8,905 items), so the split of
  `tr_A` is fixed; `V_A` does not need it (`VA_sound` recovers it).
* **`V_A`** (`VAwith segSize Vseg`): parse (`|π| = 48 + k · segSize`, byte 0 `'A'`, `hdrA`'s bytes
  2–7 zero: R-4-m5, so `π_A` is canonical given its segments, `n` and `e`); check
  `c = leafStmt e n`, `1 ≤ k ≤ 4`, every
  `1 ≤ nᵢ ≤ cap κᵢ`, `Σ nᵢ = n`, `e_k = e`, and the chaining `s_{i+1} = e_i` (every segment's
  start is its `hdr.pub`, S-0′ I-2); then run the segment verifiers in sequence on the one trace
  (`seqAll`, `OProg.bind`), segment `i` against its statement `cᵢ = leafStmt eᵢ nᵢ` (`segC`).
  `Vseg κ vk cᵢ πᵢ` is the segment program of kind `κ`, a parameter here (its IR program with the
  variable last block is S-C/S-E12′'s; S-0′ RESULT).
* **`VA_sound`**: an accepting run splits the trace into the segments' traces, each accepted, and
  the checks hold. **`VA_extract`**: with the segments' soundness (`SegSound`: an accepted segment
  proves its chain; for the real programs the per-segment `leaf_sound` through S-G's potential),
  an accepting run yields the leaf witness: `aggWit π = some (s, n)` with `n ≤ chainCap` and
  `c = leafStmt (chainEnd s n) n` (`s` segment 1's start). **`VA_complete`**: the honest assembly is
  accepted. **`VA_k_range`**, **`VA_pad`**: an accepting run has `1 ≤ k ≤ 4` and `hdrA`'s bytes
  2–7 zero. **`VA_queries_le`**: `V_A` asks at most `4 ×` a segment program's queries (`k ≤ 4` is
  checked before any query).
* Controls: `ctrlA_pos` (two segments, accepted); rejected: `ctrlA_bad_sum` (a wrong `n`),
  `ctrlA_bad_start` (segment 2 not starting at segment 1's end), `ctrlA_bad_end` (`e_k ≠ e`),
  `ctrlA_bad_pad` (a nonzero byte 2), `ctrlA_k0`/`ctrlA_k5` (`k ∉ [1, 4]`), `ctrlA_cap_kind` (an
  `L31` segment of `2^17 + 1` steps, within `L32`'s cap); `VA_reject_stmt` (the wrong statement).
-/

namespace FR
namespace Rev4
open RecursionFast

/-! ## Running programs in sequence on one trace -/

/-- Run the programs in order, stopping at the first that rejects. -/
def seqAll : List (OProg Bool) → OProg Bool
  | [] => .ret true
  | p :: ps => p.bind fun b => if b then seqAll ps else .ret false

/-- **`runSeq` of a bind** splits the trace. -/
theorem runSeq_bind_some {α β : Type} (p : OProg α) (f : α → OProg β) (tr : Trace) (b : β)
    (h : (p.bind f).runSeq tr = some b) :
    ∃ tr₁ tr₂ a, tr = tr₁ ++ tr₂ ∧ p.runSeq tr₁ = some a ∧ (f a).runSeq tr₂ = some b := by
  induction p generalizing tr with
  | ret a => exact ⟨[], tr, a, rfl, rfl, h⟩
  | query q k ih =>
    rcases tr with _ | ⟨⟨q', a'⟩, tr⟩
    · cases h
    · simp only [OProg.bind, OProg.runSeq] at h
      split at h
      · next hq =>
        obtain ⟨t₁, t₂, a, rfl, h₁, h₂⟩ := ih a' tr h
        exact ⟨(q', a') :: t₁, t₂, a, rfl, by simp [OProg.runSeq, hq, h₁], h₂⟩
      · cases h

/-- The converse: runs on consecutive traces compose. -/
theorem runSeq_bind_of {α β : Type} (p : OProg α) (f : α → OProg β) (tr₁ tr₂ : Trace) (a : α)
    (b : β) (h₁ : p.runSeq tr₁ = some a) (h₂ : (f a).runSeq tr₂ = some b) :
    (p.bind f).runSeq (tr₁ ++ tr₂) = some b := by
  induction p generalizing tr₁ with
  | ret a' =>
    rcases tr₁ with _ | ⟨e, tr₁⟩
    · simp only [OProg.runSeq, Option.some.injEq] at h₁; subst h₁; exact h₂
    · cases h₁
  | query q k ih =>
    rcases tr₁ with _ | ⟨⟨q', a'⟩, tr₁⟩
    · cases h₁
    · simp only [OProg.runSeq] at h₁
      split at h₁
      · next hq => subst hq; simp only [List.cons_append, OProg.bind, OProg.runSeq, ite_true]; exact ih a' tr₁ h₁
      · cases h₁

/-- **An accepting `seqAll` run** is the concatenation of accepting runs, one per program. -/
theorem runSeq_seqAll {ps : List (OProg Bool)} {tr : Trace} (h : (seqAll ps).runSeq tr = some true) :
    ∃ trs : List Trace, tr = trs.flatten ∧ List.Forall₂ (fun p t => p.runSeq t = some true) ps trs := by
  induction ps generalizing tr with
  | nil =>
    rcases tr with _ | ⟨e, tr⟩
    · exact ⟨[], rfl, .nil⟩
    · cases h
  | cons p ps ih =>
    obtain ⟨t₁, t₂, a, rfl, h₁, h₂⟩ := runSeq_bind_some _ _ _ _ h
    cases a
    · rcases t₂ with _ | ⟨e, t₂⟩ <;> simp [OProg.runSeq] at h₂
    · obtain ⟨trs, rfl, hf⟩ := ih h₂
      exact ⟨t₁ :: trs, rfl, .cons h₁ hf⟩

theorem seqAll_of_forall₂ {ps : List (OProg Bool)} {trs : List Trace}
    (h : List.Forall₂ (fun p t => p.runSeq t = some true) ps trs) :
    (seqAll ps).runSeq trs.flatten = some true := by
  induction h with
  | nil => rfl
  | cons h₁ _ ih => exact runSeq_bind_of _ _ _ _ true true h₁ (by simpa using ih)

/-! ## Format and checks -/

/-- `hdrA = 'A' ‖ k ‖ 0^6 ‖ enc64 n ‖ e`. -/
def aggHdr (k n : ℕ) (e : Digest) : List UInt8 :=
  [aggByte, k.toUInt8] ++ List.replicate 6 0 ++ enc64 n ++ e.toList

/-- The `k` segment proofs of `π_A`, each `segSize` bytes after the 48-byte header. -/
def aggSegs (segSize k : ℕ) (π : Proof) : List Proof :=
  (List.range k).map fun i => π.extract (48 + i * segSize) (48 + (i + 1) * segSize)

/-- The chaining: every segment after the first starts at its predecessor's end. -/
def chainOk : List SegView → Bool
  | a :: b :: l => decide (b.start = a.h) && chainOk (b :: l)
  | _ => true

/-- **`V_A`'s checks** on the views: the statement, `1 ≤ k ≤ 4`, the lengths in range, the total,
the last end, the chaining. -/
def aggChecks (c : Digest) (n : ℕ) (e : Digest) (vs : List SegView) : Bool :=
  decide (c = leafStmtF e n) && decide (1 ≤ vs.length ∧ vs.length ≤ 4) &&
    vs.all (fun v => decide (1 ≤ v.n ∧ v.n ≤ v.kind.cap)) && decide ((vs.map SegView.n).sum = n) &&
    decide ((vs.getLast?.map SegView.h) = some e) && chainOk vs

/-- The segment programs of the views, in order. -/
def segProgs (Vseg : SegKind → Digest → Digest → Proof → OProg Bool) (vk : Digest)
    (segs : List Proof) (vs : List SegView) : List (OProg Bool) :=
  (segs.zip vs).map fun pv => Vseg pv.2.kind vk (segC pv.2) pv.1

/-- **`V_A`** with segment proofs of `segSize` bytes and segment verifiers `Vseg`. The parse checks
the size, the kind byte and `hdrA`'s zero bytes 2–7 (R-4-m5). -/
def VAwith (segSize : ℕ) (Vseg : SegKind → Digest → Digest → Proof → OProg Bool)
    (vk c : Digest) (π : Proof) : OProg Bool :=
  let k := (byteAt π 1).toNat
  if π.size = 48 + k * segSize ∧ byteAt π 0 = aggByte ∧ bytesAt π 2 6 = Vector.replicate 6 0 then
    let segs := aggSegs segSize k π
    match segs.mapM segView with
    | some vs =>
      if aggChecks c (rdLE64 π 8) (bytesAt π 16 32) vs then seqAll (segProgs Vseg vk segs vs)
      else .ret false
    | none => .ret false
  else .ret false

/-- **The leaf witness `V_A` certifies**: segment 1's start and `hdrA`'s `n`. -/
def aggWit (segSize : ℕ) (π : Proof) : Option (Digest × ℕ) :=
  ((aggSegs segSize (byteAt π 1).toNat π).head?.bind segView).map fun v => (v.start, rdLE64 π 8)

/-! ## Soundness -/

/-- **`V_A`'s soundness reduction**: an accepting run on `tr` has views `vs` of its segments
meeting `aggChecks`, and `tr` is the concatenation of accepting runs of the segment programs. -/
theorem VA_sound {segSize : ℕ} {Vseg : SegKind → Digest → Digest → Proof → OProg Bool}
    {vk c : Digest} {π : Proof} {tr : Trace} (h : (VAwith segSize Vseg vk c π).runSeq tr = some true) :
    ∃ vs trs, (aggSegs segSize (byteAt π 1).toNat π).mapM segView = some vs ∧
      aggChecks c (rdLE64 π 8) (bytesAt π 16 32) vs = true ∧ tr = trs.flatten ∧
      List.Forall₂ (fun p t => p.runSeq t = some true)
        (segProgs Vseg vk (aggSegs segSize (byteAt π 1).toNat π) vs) trs := by
  simp only [VAwith] at h
  split at h
  · split at h
    · next vs hvs =>
      split at h
      · next hc => obtain ⟨trs, rfl, hf⟩ := runSeq_seqAll h; exact ⟨vs, trs, hvs, hc, rfl, hf⟩
      · rcases tr with _ | ⟨e, tr⟩ <;> simp [OProg.runSeq] at h
    · rcases tr with _ | ⟨e, tr⟩ <;> simp [OProg.runSeq] at h
  · rcases tr with _ | ⟨e, tr⟩ <;> simp [OProg.runSeq] at h

/-- **The segments' soundness** (the interface `V_A` reduces to): an accepted segment proof proves
its chain. For the real segment programs this is `seg_sound` through the per-kind soundness of
S-G (with its error, in the potential); here it is the hypothesis of `VA_extract`. -/
def SegSound (Vseg : SegKind → Digest → Digest → Proof → OProg Bool) (vk : Digest) : Prop :=
  ∀ π v t, segView π = some v → v.n ≤ v.kind.cap →
    (Vseg v.kind vk (segC v) π).runSeq t = some true → chainEnd v.start v.n = v.h

/-- **Segment soundness on the good traces** (`Good`: S-G's non-doomed runs, whose complement the
potential bounds): an accepted run on a good trace proves the segment's chain. `SegSound` is
`Good = ⊤`; for a real SNARK it holds only on good traces (an arbitrary trace may answer the
Fiat–Shamir queries at will), so `VA_extract_on` is the form the real programs use. -/
def SegSoundOn (Vseg : SegKind → Digest → Digest → Proof → OProg Bool) (vk : Digest)
    (Good : Trace → Prop) : Prop :=
  ∀ π v t, segView π = some v → v.n ≤ v.kind.cap → Good t →
    (Vseg v.kind vk (segC v) π).runSeq t = some true → chainEnd v.start v.n = v.h

/-- **Per-segment knowledge soundness on the good traces** (the SNARK's half, per kind: S-G's
potential): an accepted run on a good trace comes with a table meeting the segment circuit. -/
def SegKSOn (Vseg : SegKind → Digest → Digest → Proof → OProg Bool) (vk : Digest)
    (Good : Trace → Prop) : Prop :=
  ∀ π v t, segView π = some v → v.n ≤ v.kind.cap → Good t →
    (Vseg v.kind vk (segC v) π).runSeq t = some true →
      ∃ z : ℕ → Block.Pos → F, SegHolds v.kind v.stmt z

/-- **`SegSoundOn` from the circuit's `leaf_sound`** (`seg_sound`): the chain half of a segment's
soundness is proved; what remains is the SNARK's extraction (`SegKSOn`). -/
theorem segSoundOn_of_KS {Vseg : SegKind → Digest → Digest → Proof → OProg Bool} {vk : Digest}
    {Good : Trace → Prop} (h : SegKSOn Vseg vk Good) : SegSoundOn Vseg vk Good :=
  fun π v t hv hn hg hacc => by
    obtain ⟨z, hz⟩ := h π v t hv hn hg hacc
    exact seg_sound hz

private theorem mapM_forall₂ {l : List Proof} {vs : List SegView} (h : l.mapM segView = some vs) :
    List.Forall₂ (fun p v => segView p = some v) l vs := by
  induction l generalizing vs with
  | nil => simp at h; subst h; exact .nil
  | cons p l ih =>
    simp only [List.mapM_cons, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def,
      Option.some.injEq] at h
    obtain ⟨v, hv, vs', hvs', rfl⟩ := h
    exact .cons hv (ih hvs')

private theorem chainOk_tail : ∀ (a : SegView) (l : List SegView),
    chainOk (a :: l) = true → ChainedTail a.stmt (l.map SegView.stmt)
  | _, [], _ => trivial
  | a, b :: l, h => by
    simp only [chainOk, Bool.and_eq_true, decide_eq_true_eq] at h
    exact ⟨h.1, chainOk_tail b l h.2⟩

private theorem compose_views (a : SegView) (l : List SegView) (hc : chainOk (a :: l) = true)
    (hs : ∀ v ∈ a :: l, chainEnd v.start v.n = v.h) :
    chainEnd a.start ((a :: l).map SegView.n).sum = ((a :: l).getLast (List.cons_ne_nil _ _)).h := by
  have h := segs_compose a.stmt (l.map SegView.stmt) (chainOk_tail a l hc)
    (by
      intro st hst
      simp only [List.mem_cons, List.mem_map] at hst
      rcases hst with rfl | ⟨v, hv, rfl⟩
      · exact hs a (by simp)
      · exact hs v (List.mem_cons_of_mem _ hv))
  have ht : totalN (a.stmt :: l.map SegView.stmt) = ((a :: l).map SegView.n).sum := by
    simp [totalN, SegView.stmt, Function.comp_def]
  rw [ht] at h; refine h.trans ?_
  cases l using List.reverseRecOn with
  | nil => rfl
  | append_singleton l x _ => simp [SegView.stmt]

/-- **An accepting run has `1 ≤ k ≤ 4`** (the views are the `k` segments, `aggChecks` bounds them). -/
theorem VA_k_range {segSize : ℕ} {Vseg : SegKind → Digest → Digest → Proof → OProg Bool}
    {vk c : Digest} {π : Proof} {tr : Trace} (h : (VAwith segSize Vseg vk c π).runSeq tr = some true) :
    1 ≤ (byteAt π 1).toNat ∧ (byteAt π 1).toNat ≤ 4 := by
  obtain ⟨vs, -, hvs, hc, -⟩ := VA_sound h
  have hl := (mapM_forall₂ hvs).length_eq
  simp only [aggSegs, List.length_map, List.length_range] at hl
  simp only [aggChecks, Bool.and_eq_true, decide_eq_true_eq] at hc
  rw [hl]; exact hc.1.1.1.1.2

/-- **An accepting run has `hdrA`'s bytes 2–7 zero** (R-4-m5). -/
theorem VA_pad {segSize : ℕ} {Vseg : SegKind → Digest → Digest → Proof → OProg Bool}
    {vk c : Digest} {π : Proof} {tr : Trace} (h : (VAwith segSize Vseg vk c π).runSeq tr = some true) :
    bytesAt π 2 6 = Vector.replicate 6 0 := by
  simp only [VAwith] at h
  split at h
  · next hh => exact hh.2.2
  · rcases tr with _ | ⟨e, tr⟩ <;> simp [OProg.runSeq] at h

/-- **`V_A` extracts the leaf witness**: with sound segments, an accepting run yields
`aggWit π = some (s, n)`, `n ≤ chainCap` and `c = leafStmt (chainEnd s n) n`. -/
theorem VA_extract {segSize : ℕ} {Vseg : SegKind → Digest → Digest → Proof → OProg Bool}
    {vk c : Digest} {π : Proof} {tr : Trace} (hS : SegSound Vseg vk)
    (h : (VAwith segSize Vseg vk c π).runSeq tr = some true) :
    ∃ s n, aggWit segSize π = some (s, n) ∧ n ≤ chainCap ∧ c = leafStmt (chainEnd s n) n := by
  obtain ⟨vs, trs, hvs, hc, -, hf⟩ := VA_sound h
  set segs := aggSegs segSize (byteAt π 1).toNat π
  have h2 := mapM_forall₂ hvs
  simp only [aggChecks, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true] at hc
  obtain ⟨⟨⟨⟨⟨hst, hk⟩, hr⟩, hsum⟩, hlast⟩, hch⟩ := hc
  -- every segment proves its chain
  have hseg : ∀ v ∈ vs, chainEnd v.start v.n = v.h := by
    intro v hv
    obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hv
    have hl := h2.length_eq
    have hpi : segView segs[i] = some vs[i] := (List.forall₂_iff_get.1 h2).2 i (by omega) hi
    have hf' := (List.forall₂_iff_get.1 hf).2 i (by simp [segProgs]; omega) (by
      have := hf.length_eq; simp [segProgs] at this; omega)
    simp only [segProgs, List.get_eq_getElem, List.getElem_map, List.getElem_zip] at hf'
    exact hS _ _ _ hpi (hr _ hv).2 hf'
  obtain ⟨a, l, rfl⟩ : ∃ a l, vs = a :: l := by
    cases vs with
    | nil => simp at hk
    | cons a l => exact ⟨a, l, rfl⟩
  have hcomp := compose_views a l hch hseg
  have hlast' : ((a :: l).getLast (List.cons_ne_nil _ _)).h = bytesAt π 16 32 := by
    rw [List.getLast?_eq_some_getLast (List.cons_ne_nil _ _)] at hlast; simpa using hlast
  have hhead : segs.head?.bind segView = some a := by
    obtain ⟨p, ps, hp, -, hl⟩ := List.forall₂_cons_right_iff.1 h2
    rw [hl]; exact hp
  refine ⟨a.start, rdLE64 π 8, ?_, ?_, ?_⟩
  · show (segs.head?.bind segView).map (fun v => (v.start, rdLE64 π 8)) = _
    rw [hhead]; rfl
  · rw [← hsum]
    have hle : ∀ v ∈ a :: l, v.n ≤ 2 ^ 18 := fun v hv => (hr v hv).2.trans (by cases v.kind <;> decide)
    have hb := List.sum_le_length_nsmul ((a :: l).map SegView.n) (2 ^ 18) (by
      intro x hx; obtain ⟨v, hv, rfl⟩ := List.mem_map.1 hx; exact hle v hv)
    rw [List.length_map, smul_eq_mul] at hb
    calc ((a :: l).map SegView.n).sum ≤ (a :: l).length * 2 ^ 18 := hb
      _ ≤ 4 * 2 ^ 18 := Nat.mul_le_mul_right _ hk.2
      _ = chainCap := rfl
  · rw [hst, leafStmtF_eq, ← hsum, hcomp, hlast']

/-- **`V_A`'s extraction on the good traces** (`VA_extract` with `SegSoundOn`): `Good` must hold of
every piece of every split of `tr` (e.g. a per-query predicate). -/
theorem VA_extract_on {segSize : ℕ} {Vseg : SegKind → Digest → Digest → Proof → OProg Bool}
    {vk c : Digest} {π : Proof} {tr : Trace} {Good : Trace → Prop} (hS : SegSoundOn Vseg vk Good)
    (hG : ∀ trs : List Trace, tr = trs.flatten → ∀ t ∈ trs, Good t)
    (h : (VAwith segSize Vseg vk c π).runSeq tr = some true) :
    ∃ s n, aggWit segSize π = some (s, n) ∧ n ≤ chainCap ∧ c = leafStmt (chainEnd s n) n := by
  obtain ⟨vs, trs, hvs, hc, htr, hf⟩ := VA_sound h
  set segs := aggSegs segSize (byteAt π 1).toNat π
  have h2 := mapM_forall₂ hvs
  simp only [aggChecks, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true] at hc
  obtain ⟨⟨⟨⟨⟨hst, hk⟩, hr⟩, hsum⟩, hlast⟩, hch⟩ := hc
  -- every segment proves its chain
  have hseg : ∀ v ∈ vs, chainEnd v.start v.n = v.h := by
    intro v hv
    obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hv
    have hl := h2.length_eq
    have hpi : segView segs[i] = some vs[i] := (List.forall₂_iff_get.1 h2).2 i (by omega) hi
    have hf' := (List.forall₂_iff_get.1 hf).2 i (by simp [segProgs]; omega) (by
      have := hf.length_eq; simp [segProgs] at this; omega)
    simp only [segProgs, List.get_eq_getElem, List.getElem_map, List.getElem_zip] at hf'
    have hlt : i < trs.length := by have := hf.length_eq; simp [segProgs] at this; omega
    exact hS _ _ _ hpi (hr _ hv).2 (hG trs htr _ (List.getElem_mem hlt)) hf'
  obtain ⟨a, l, rfl⟩ : ∃ a l, vs = a :: l := by
    cases vs with
    | nil => simp at hk
    | cons a l => exact ⟨a, l, rfl⟩
  have hcomp := compose_views a l hch hseg
  have hlast' : ((a :: l).getLast (List.cons_ne_nil _ _)).h = bytesAt π 16 32 := by
    rw [List.getLast?_eq_some_getLast (List.cons_ne_nil _ _)] at hlast; simpa using hlast
  have hhead : segs.head?.bind segView = some a := by
    obtain ⟨p, ps, hp, -, hl⟩ := List.forall₂_cons_right_iff.1 h2
    rw [hl]; exact hp
  refine ⟨a.start, rdLE64 π 8, ?_, ?_, ?_⟩
  · show (segs.head?.bind segView).map (fun v => (v.start, rdLE64 π 8)) = _
    rw [hhead]; rfl
  · rw [← hsum]
    have hle : ∀ v ∈ a :: l, v.n ≤ 2 ^ 18 := fun v hv => (hr v hv).2.trans (by cases v.kind <;> decide)
    have hb := List.sum_le_length_nsmul ((a :: l).map SegView.n) (2 ^ 18) (by
      intro x hx; obtain ⟨v, hv, rfl⟩ := List.mem_map.1 hx; exact hle v hv)
    rw [List.length_map, smul_eq_mul] at hb
    calc ((a :: l).map SegView.n).sum ≤ (a :: l).length * 2 ^ 18 := hb
      _ ≤ 4 * 2 ^ 18 := Nat.mul_le_mul_right _ hk.2
      _ = chainCap := rfl
  · rw [hst, leafStmtF_eq, ← hsum, hcomp, hlast']

/-! ## Completeness -/

/-- **The honest assembly is accepted**: views meeting the checks and accepting segment runs give
an accepting `V_A` run on the concatenated trace. -/
theorem VA_complete {segSize : ℕ} {Vseg : SegKind → Digest → Digest → Proof → OProg Bool}
    {vk c : Digest} {π : Proof} {vs : List SegView} {trs : List Trace}
    (hsz : π.size = 48 + (byteAt π 1).toNat * segSize) (h0 : byteAt π 0 = aggByte)
    (hpad : bytesAt π 2 6 = Vector.replicate 6 0)
    (hvs : (aggSegs segSize (byteAt π 1).toNat π).mapM segView = some vs)
    (hc : aggChecks c (rdLE64 π 8) (bytesAt π 16 32) vs = true)
    (hf : List.Forall₂ (fun p t => p.runSeq t = some true)
      (segProgs Vseg vk (aggSegs segSize (byteAt π 1).toNat π) vs) trs) :
    (VAwith segSize Vseg vk c π).runSeq trs.flatten = some true := by
  simp only [VAwith, hsz, h0, hpad, and_self, ite_true, hvs, hc]
  exact seqAll_of_forall₂ hf

/-! ## Queries (`KS`'s first conjunct) -/

/-- `seqAll` asks at most the sum of its programs' queries. -/
theorem seqAll_queries_le (H : ByteArray → Digest) {q : ℕ} : ∀ {ps : List (OProg Bool)},
    (∀ p ∈ ps, (p.queries H).length ≤ q) → ((seqAll ps).queries H).length ≤ ps.length * q
  | [], _ => Nat.zero_le _
  | p :: ps, h => by
    have h₁ := h p (by simp)
    have h₂ := seqAll_queries_le H (ps := ps) fun p hp => h p (List.mem_cons_of_mem _ hp)
    rw [seqAll, OProg.queries_bind, List.length_append, List.length_cons, Nat.succ_mul]
    generalize OProg.run H p = b
    cases b
    · simp only [Bool.false_eq_true, ite_false, OProg.queries, List.length_nil]; omega
    · simp only [ite_true]; omega

/-- **`V_A`'s queries**: at most `4 ×` a bound `qS` on every segment program's (`k ≤ 4` is
checked before any query). -/
theorem VA_queries_le {segSize qS : ℕ} {Vseg : SegKind → Digest → Digest → Proof → OProg Bool}
    (H : ByteArray → Digest) (hS : ∀ κ vk c π, ((Vseg κ vk c π).queries H).length ≤ qS)
    (vk c : Digest) (π : Proof) : ((VAwith segSize Vseg vk c π).queries H).length ≤ 4 * qS := by
  simp only [VAwith]
  split
  · split
    · next vs _ =>
      split
      · next hc =>
        have hk : vs.length ≤ 4 := by
          simp only [aggChecks, Bool.and_eq_true, decide_eq_true_eq] at hc; exact hc.1.1.1.1.2.2
        refine (seqAll_queries_le H (q := qS) fun p hp => ?_).trans ?_
        · obtain ⟨pv, -, rfl⟩ := List.mem_map.1 hp; exact hS _ _ _ _
        · simp only [segProgs, List.length_map, List.length_zip]
          exact Nat.mul_le_mul_right _ ((min_le_right _ _).trans hk)
      · exact Nat.zero_le _
    · exact Nat.zero_le _
  · exact Nat.zero_le _

/-! ## Rejection lemmas (used by the controls) -/

/-- The checks other than the statement: `1 ≤ k ≤ 4`, the lengths in range, the total, the last
end, the chaining. -/
def aggRest (n : ℕ) (e : Digest) (vs : List SegView) : Bool :=
  decide (1 ≤ vs.length ∧ vs.length ≤ 4) && vs.all (fun v => decide (1 ≤ v.n ∧ v.n ≤ v.kind.cap)) &&
    decide ((vs.map SegView.n).sum = n) && decide ((vs.getLast?.map SegView.h) = some e) && chainOk vs

theorem aggChecks_eq (c : Digest) (n : ℕ) (e : Digest) (vs : List SegView) :
    aggChecks c n e vs = (decide (c = leafStmtF e n) && aggRest n e vs) := by
  simp only [aggChecks, aggRest, Bool.and_assoc]

/-- **`V_A` rejects** when the segments' views fail `aggRest`. -/
theorem VA_reject_rest {segSize : ℕ} {Vseg : SegKind → Digest → Digest → Proof → OProg Bool}
    {vk c : Digest} {π : Proof} {vs : List SegView}
    (hvs : (aggSegs segSize (byteAt π 1).toNat π).mapM segView = some vs)
    (hr : aggRest (rdLE64 π 8) (bytesAt π 16 32) vs = false) (tr : Trace) :
    (VAwith segSize Vseg vk c π).runSeq tr ≠ some true := fun h => by
  obtain ⟨vs', -, hvs', hc, -⟩ := VA_sound h
  rw [hvs, Option.some.injEq] at hvs'; subst hvs'
  rw [aggChecks_eq, hr, Bool.and_false] at hc; cases hc

/-- **`V_A` rejects the wrong statement**: `c ≠ leafStmt e n`. -/
theorem VA_reject_stmt {segSize : ℕ} {Vseg : SegKind → Digest → Digest → Proof → OProg Bool}
    {vk c : Digest} {π : Proof} (hc : c ≠ leafStmt (bytesAt π 16 32) (rdLE64 π 8)) (tr : Trace) :
    (VAwith segSize Vseg vk c π).runSeq tr ≠ some true := fun h => by
  obtain ⟨vs', -, -, hc', -⟩ := VA_sound h
  rw [aggChecks_eq, leafStmtF_eq] at hc'
  simp only [Bool.and_eq_true, decide_eq_true_eq] at hc'; exact hc hc'.1

/-! ## Controls (segment proofs of 96 bytes; trivial segment programs) -/

/-- A 96-byte segment proof of kind `L31`: `hdr` (start `s`) and the first 48 bytes of `stmt`
(end `h`, length `n`): what `segView` reads. -/
def ctrlSeg (s h : Digest) (n : ℕ) : List UInt8 := segHdr .L31 s ++ (stmtLeafBytes n h).take 48

/-- The control's digests: `dC i` is the constant digest `i`. -/
def dC (i : UInt8) : Digest := Vector.replicate 32 i

/-- `π_A` of two segments `s₁ → d1` (1 step) and `s₂ → d2` (`n₂` steps), total `n`, end `d2`. -/
def ctrlA (n n₂ : ℕ) (s₂ : Digest) : Proof :=
  ⟨(aggHdr 2 n (dC 2) ++ ctrlSeg (dC 0) (dC 1) 1 ++ ctrlSeg s₂ (dC 2) n₂).toArray⟩

/-- The control's views. -/
def ctrlViews (n₂ : ℕ) (s₂ : Digest) : List SegView := [⟨.L31, dC 0, dC 1, 1⟩, ⟨.L31, s₂, dC 2, n₂⟩]

private theorem take_drop_flat {S : ℕ} : ∀ (segs : List (List UInt8)) (pre : List UInt8) (i : ℕ),
    (∀ s ∈ segs, s.length = S) → (hi : i < segs.length) →
      ((pre ++ segs.flatten).drop (pre.length + i * S)).take S = segs[i]
  | s :: ss, pre, 0, hs, _ => by
    simp [← hs s (by simp)]
  | s :: ss, pre, i + 1, hs, hi => by
    have := take_drop_flat ss (pre ++ s) i (fun t ht => hs t (by simp [ht])) (by simpa using hi)
    rw [List.length_append, hs s (by simp), List.append_assoc] at this
    simpa [List.flatten_cons, Nat.add_one_mul, Nat.add_assoc, Nat.add_comm S] using this

/-- `aggSegs` of a header of 48 bytes followed by segments of `S` bytes: the segments. -/
theorem aggSegs_flat {S k : ℕ} (hdr : List UInt8) (segs : List (List UInt8)) (hh : hdr.length = 48)
    (hs : ∀ s ∈ segs, s.length = S) (hk : segs.length = k) :
    aggSegs S k ⟨(hdr ++ segs.flatten).toArray⟩ = segs.map fun s => (⟨s.toArray⟩ : ByteArray) := by
  subst hk
  refine List.ext_getElem (by simp [aggSegs]) fun i h₁ _ => ?_
  simp only [aggSegs, List.getElem_map, List.getElem_range]
  ext1
  simp only [ByteArray.data_extract, List.extract_toArray, List.extract_eq_take_drop]
  have h : 48 + (i + 1) * S - (48 + i * S) = S := by rw [Nat.add_one_mul]; omega
  rw [h, ← hh, take_drop_flat segs hdr i hs (by simpa [aggSegs] using h₁)]

/-- The views of `ctrlA n n₂ s₂` are those of its two segments. -/
theorem ctrlA_mapM (n n₂ : ℕ) (s₂ : Digest) (hk : (byteAt (ctrlA n n₂ s₂) 1).toNat = 2) :
    (aggSegs 96 (byteAt (ctrlA n n₂ s₂) 1).toNat (ctrlA n n₂ s₂)).mapM segView =
      [segView ⟨(ctrlSeg (dC 0) (dC 1) 1).toArray⟩, segView ⟨(ctrlSeg s₂ (dC 2) n₂).toArray⟩].mapM id := by
  rw [hk, show ctrlA n n₂ s₂ = ⟨(aggHdr 2 n (dC 2) ++
      [ctrlSeg (dC 0) (dC 1) 1, ctrlSeg s₂ (dC 2) n₂].flatten).toArray⟩ by simp [ctrlA],
    aggSegs_flat (k := 2) (aggHdr 2 n (dC 2)) [ctrlSeg (dC 0) (dC 1) 1, ctrlSeg s₂ (dC 2) n₂]
      (by simp [aggHdr, enc64]) (by simp [ctrlSeg, segHdr, stmtLeafBytes, enc64]) rfl]
  rfl

/-- Every segment program accepts with no query. -/
def VsegTrue : SegKind → Digest → Digest → Proof → OProg Bool := fun _ _ _ _ => .ret true

theorem forall₂_true (vk : Digest) (segs : List Proof) (vs : List SegView) :
    List.Forall₂ (fun p t => p.runSeq t = some true) (segProgs VsegTrue vk segs vs)
      (List.replicate (segs.zip vs).length []) := by
  rw [segProgs]
  induction segs.zip vs with
  | nil => exact .nil
  | cons _ _ ih => exact .cons rfl ih

/-- Positive: the two chained segments (`d0 → d1 → d2`, `1 + 2` steps) are accepted against
`leafStmt d2 3`, with the empty trace. -/
theorem ctrlA_pos : (VAwith 96 VsegTrue (dC 9) (leafStmtF (dC 2) 3) (ctrlA 3 2 (dC 1))).runSeq [] =
    some true := by
  have hv : (aggSegs 96 (byteAt (ctrlA 3 2 (dC 1)) 1).toNat (ctrlA 3 2 (dC 1))).mapM segView =
      some (ctrlViews 2 (dC 1)) := by rw [ctrlA_mapM _ _ _ (by decide +kernel)]; decide +kernel
  have he : bytesAt (ctrlA 3 2 (dC 1)) 16 32 = dC 2 := by decide +kernel
  have hn : rdLE64 (ctrlA 3 2 (dC 1)) 8 = 3 := by decide +kernel
  have hc : aggChecks (leafStmtF (dC 2) 3) (rdLE64 (ctrlA 3 2 (dC 1)) 8)
      (bytesAt (ctrlA 3 2 (dC 1)) 16 32) (ctrlViews 2 (dC 1)) = true := by
    simp only [aggChecks_eq, he, hn, decide_true, Bool.true_and]; decide +kernel
  have h := VA_complete (vk := dC 9) (by decide +kernel) (by decide +kernel) (by decide +kernel) hv hc
    (forall₂_true _ _ _)
  simpa using h

/-- Negative: a wrong total (`hdrA`'s `n = 4`, the segments' `1 + 2`). -/
theorem ctrlA_bad_sum : (VAwith 96 VsegTrue (dC 9) (leafStmtF (dC 2) 4) (ctrlA 4 2 (dC 1))).runSeq [] ≠
    some true :=
  VA_reject_rest (vs := ctrlViews 2 (dC 1)) 
    (by rw [ctrlA_mapM _ _ _ (by decide +kernel)]; decide +kernel) (by decide +kernel) _

/-- Negative: a segment length out of its kind's range fails the checks (so `V_A` rejects,
`VA_reject_rest`). -/
theorem aggRest_bad_n {n : ℕ} {e : Digest} {vs : List SegView} {v : SegView} (hv : v ∈ vs)
    (hn : v.n = 0 ∨ v.kind.cap < v.n) : aggRest n e vs = false := by
  simp only [aggRest, Bool.and_eq_false_iff, List.all_eq_false]
  left; left; left; right
  exact ⟨v, hv, by rcases hn with h | h <;> simp [h]⟩

/-- Negative: segment 2 does not start at segment 1's end (its public start `s₂ = e₁` fails). -/
theorem ctrlA_bad_start : (VAwith 96 VsegTrue (dC 9) (leafStmtF (dC 2) 3) (ctrlA 3 2 (dC 7))).runSeq [] ≠
    some true :=
  VA_reject_rest (vs := ctrlViews 2 (dC 7)) 
    (by rw [ctrlA_mapM _ _ _ (by decide +kernel)]; decide +kernel) (by decide +kernel) _

/-- `π_A`'s header `hdr` followed by the two segments of `ctrlA 3 2 (dC 1)`. -/
def ctrlAx (hdr : List UInt8) : Proof :=
  ⟨(hdr ++ ctrlSeg (dC 0) (dC 1) 1 ++ ctrlSeg (dC 1) (dC 2) 2).toArray⟩

/-- Negative (R-4-m5): `ctrlA_pos`'s bytes with `hdrA`'s byte 2 set to `1` are rejected. -/
theorem ctrlA_bad_pad : (VAwith 96 VsegTrue (dC 9) (leafStmtF (dC 2) 3)
    (ctrlAx ([aggByte, 2, 1] ++ List.replicate 5 0 ++ enc64 3 ++ (dC 2).toList))).runSeq [] ≠ some true :=
  fun h => absurd (VA_pad h) (by decide +kernel)

/-- Negative: `e_k ≠ e` (`hdrA`'s `e = d3`, the last segment ends at `d2`): `aggRest` fails, so
`V_A` rejects (`VA_reject_rest`); with `e = d2` it holds (`ctrlA_pos`). -/
theorem ctrlA_bad_end : aggRest 3 (dC 3) (ctrlViews 2 (dC 1)) = false ∧
    aggRest 3 (dC 2) (ctrlViews 2 (dC 1)) = true := by
  decide +kernel

/-- Five chained one-step `L31` views `d0 → d1 → … → d5`. -/
def ctrlViews5 : List SegView := (List.range 5).map fun i => ⟨.L31, dC i.toUInt8, dC (i + 1).toUInt8, 1⟩

/-- Negative (`k ∉ [1, 4]`): `k = 0` (a bare 48-byte `hdrA`) is rejected; `k = 5` fails `aggRest` on
five otherwise valid chained views, whose first four pass. -/
theorem ctrlA_k0 : (VAwith 96 VsegTrue (dC 9) (leafStmtF (dC 0) 0)
    ⟨(aggHdr 0 0 (dC 0)).toArray⟩).runSeq [] ≠ some true :=
  fun h => absurd (VA_k_range h).1 (by decide +kernel)

theorem ctrlA_k5 : aggRest 5 (dC 5) ctrlViews5 = false ∧ aggRest 4 (dC 4) (ctrlViews5.take 4) = true := by
  decide +kernel

/-- Negative (the cap is per kind): an `L31` segment of `2^17 + 1` steps fails `aggRest`; the same
view of kind `L32` passes. -/
theorem ctrlA_cap_kind :
    aggRest (2 ^ 17 + 2) (dC 2) [⟨.L31, dC 0, dC 1, 1⟩, ⟨.L31, dC 1, dC 2, 2 ^ 17 + 1⟩] = false ∧
      aggRest (2 ^ 17 + 2) (dC 2) [⟨.L31, dC 0, dC 1, 1⟩, ⟨.L32, dC 1, dC 2, 2 ^ 17 + 1⟩] = true := by
  decide +kernel

end Rev4
end FR
