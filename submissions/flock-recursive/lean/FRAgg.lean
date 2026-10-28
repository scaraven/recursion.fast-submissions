-- New for `flock-recursive` (BLUEPRINT revision 4.0, B-11; §10 changes 25 (b); stage S-0′).
import FRSegment

/-!
# The aggregate leaf `A` and its verifier `V_A` (B-11)

A step's new chain is proved by `k ≤ 4` segment SNARKs assembled into **one signed proof**
`(π_A, tr_A, σ_A)`; it has no SNARK of its own.

* **Format.** `π_A = hdrA ‖ π₁ ‖ … ‖ π_k`, `hdrA = 'A' ‖ k ‖ 0^6 ‖ enc64 n ‖ e` (48 bytes), every
  `πᵢ` a segment proof of `segSize` bytes (`piSizeOf seq4 = 798,192`); `tr_A = tr₁ ‖ … ‖ tr_k`, one
  trace signed once. A segment's queries are its 3.x item sequence (8,905 items), so the split of
  `tr_A` is fixed; `V_A` does not need it (`VA_sound` recovers it).
* **`V_A`** (`VAwith segSize Vseg`): parse; check `c = leafStmt e n`, `1 ≤ k ≤ 4`, every
  `1 ≤ nᵢ ≤ cap κᵢ`, `Σ nᵢ = n`, `e_k = e`, and the chaining `s_{i+1} = e_i` (the public starts of
  segments `i ≥ 2`, B-12); then run the segment verifiers in sequence on the one trace
  (`seqAll`, `OProg.bind`), segment `i` against its statement `cᵢ = leafStmt eᵢ nᵢ` (`segC`).
  `Vseg κ vk cᵢ πᵢ` is the segment program of kind `κ`, a parameter here (its IR program with the
  variable last block is S-C/S-E12′'s; S-0′ RESULT).
* **`VA_sound`**: an accepting run splits the trace into the segments' traces, each accepted, and
  the checks hold. **`VA_extract`**: with the segments' soundness (`SegSound`: an accepted segment
  proves its chain; for the real programs the per-segment `leaf_sound` through S-G's potential),
  an accepting run yields the leaf witness: `aggWit π = some (s, n)` with `n ≤ chainCap` and
  `c = leafStmt (chainEnd s n) n` (`s` segment 1's start). **`VA_complete`**: the honest assembly is
  accepted.
* Controls: `ctrlA_pos` (two one-step segments, accepted), `ctrlA_bad_sum` (a wrong `n`),
  `ctrlA_bad_start` (segment 2 not starting at segment 1's end), `ctrlA_bad_stmt` (the wrong
  statement), all rejected.
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

/-- **`V_A`** with segment proofs of `segSize` bytes and segment verifiers `Vseg`. -/
def VAwith (segSize : ℕ) (Vseg : SegKind → Digest → Digest → Proof → OProg Bool)
    (vk c : Digest) (π : Proof) : OProg Bool :=
  let k := (byteAt π 1).toNat
  if π.size = 48 + k * segSize ∧ byteAt π 0 = aggByte then
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
      ∃ (b : Bool) (z : ℕ → Block.Pos → F), SegHolds v.kind (v.stmt b) z

/-- **`SegSoundOn` from the circuit's `leaf_sound`** (`seg_sound`): the chain half of a segment's
soundness is proved; what remains is the SNARK's extraction (`SegKSOn`). -/
theorem segSoundOn_of_KS {Vseg : SegKind → Digest → Digest → Proof → OProg Bool} {vk : Digest}
    {Good : Trace → Prop} (h : SegKSOn Vseg vk Good) : SegSoundOn Vseg vk Good :=
  fun π v t hv hn hg hacc => by
    obtain ⟨b, z, hz⟩ := h π v t hv hn hg hacc
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

private theorem chainOk_tail : ∀ (a : SegView) (l : List SegView) (p : Bool),
    chainOk (a :: l) = true → ChainedTail (a.stmt p) (l.map (SegView.stmt · true))
  | _, [], _, _ => trivial
  | a, b :: l, _, h => by
    simp only [chainOk, Bool.and_eq_true, decide_eq_true_eq] at h
    exact ⟨h.1, rfl, chainOk_tail b l true h.2⟩

private theorem compose_views (a : SegView) (l : List SegView) (hc : chainOk (a :: l) = true)
    (hs : ∀ v ∈ a :: l, chainEnd v.start v.n = v.h) :
    chainEnd a.start ((a :: l).map SegView.n).sum = ((a :: l).getLast (List.cons_ne_nil _ _)).h := by
  have h := segs_compose (a.stmt false) (l.map (SegView.stmt · true)) (chainOk_tail a l false hc)
    (by
      intro st hst
      simp only [List.mem_cons, List.mem_map] at hst
      rcases hst with rfl | ⟨v, hv, rfl⟩
      · exact hs a (by simp)
      · exact hs v (List.mem_cons_of_mem _ hv))
  have ht : totalN (a.stmt false :: l.map (SegView.stmt · true)) = ((a :: l).map SegView.n).sum := by
    simp [totalN, SegView.stmt, Function.comp_def]
  rw [ht] at h; refine h.trans ?_
  cases l using List.reverseRecOn with
  | nil => rfl
  | append_singleton l x _ => simp [SegView.stmt]

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
    (hvs : (aggSegs segSize (byteAt π 1).toNat π).mapM segView = some vs)
    (hc : aggChecks c (rdLE64 π 8) (bytesAt π 16 32) vs = true)
    (hf : List.Forall₂ (fun p t => p.runSeq t = some true)
      (segProgs Vseg vk (aggSegs segSize (byteAt π 1).toNat π) vs) trs) :
    (VAwith segSize Vseg vk c π).runSeq trs.flatten = some true := by
  simp only [VAwith, hsz, h0, and_self, ite_true, hvs, hc]
  exact seqAll_of_forall₂ hf

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
      some (ctrlViews 2 (dC 1)) := by decide +kernel
  have he : bytesAt (ctrlA 3 2 (dC 1)) 16 32 = dC 2 := by decide +kernel
  have hn : rdLE64 (ctrlA 3 2 (dC 1)) 8 = 3 := by decide +kernel
  have hc : aggChecks (leafStmtF (dC 2) 3) (rdLE64 (ctrlA 3 2 (dC 1)) 8)
      (bytesAt (ctrlA 3 2 (dC 1)) 16 32) (ctrlViews 2 (dC 1)) = true := by
    simp only [aggChecks_eq, he, hn, decide_true, Bool.true_and]; decide +kernel
  have h := VA_complete (vk := dC 9) (by decide +kernel) (by decide +kernel) hv hc (forall₂_true _ _ _)
  simpa using h

/-- Negative: a wrong total (`hdrA`'s `n = 4`, the segments' `1 + 2`). -/
theorem ctrlA_bad_sum : (VAwith 96 VsegTrue (dC 9) (leafStmtF (dC 2) 4) (ctrlA 4 2 (dC 1))).runSeq [] ≠
    some true :=
  VA_reject_rest (vs := ctrlViews 2 (dC 1)) (by decide +kernel) (by decide +kernel) _

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
  VA_reject_rest (vs := ctrlViews 2 (dC 7)) (by decide +kernel) (by decide +kernel) _

end Rev4
end FR
