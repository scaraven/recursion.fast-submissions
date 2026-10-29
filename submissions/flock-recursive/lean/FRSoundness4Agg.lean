-- New for `flock-recursive` (BLUEPRINT revision 4.1, B-11, B-12; stage S-G12′; adopted from the R-4
-- review's probe `logs/R-4/build/src/R4Probe.lean`, ruling R-4-M1/M2). INT-10 (R4i's F1): the
-- size hypothesis `π.size = piSizeOf seq4` of `SegSoundLog`, supplied by `V_A`'s size check.
import FRVerifier4
import FRSoundness4R4Link

/-!
# The aggregate leaf's soundness in `FinalLaw`'s form (`runLog` on a good log)

`FinalLaw` reads the verifier by lookup in **one** log (`OProg.runLog`), and only on good logs
(potential below `1`). So the segment programs' soundness is stated in that form, not on traces
(R-4-M1): `SegSound` (every trace) is false for every Fiat–Shamir verifier (`not_segSound_lucky`),
and S-F4's on-trace `SegSoundOn` asks for a good event on every piece of every split of the trace,
which a potential on logs does not give. Every segment statement carries `1 ≤ n` (R-4-M2: at
`n = 0` the segment's `lastOps` wraps to `cap − 1`); `V_A` checks it, so it is discharged there.
Likewise every segment statement carries `π.size = piSizeOf seq4` (INT-10, R4i's F1: the segment
program reads no size, and its run facts need `π` to hold every absorbed message); `V_A`'s size check
`π.size = 48 + k · segSize` gives it for each segment (`piSize_aggSegs`).

* **`runLog_bind`**, **`runLog_seqAll`**: under `runLog` every program of `seqAll` reads the same
  log, so an accepting `seqAll` has every program accepting (no split of a trace).
* **`VA_sound_log`**: an accepting `V_A` on a log has its size check, its views, its checks and
  every segment program accepting on that log.
* **`SegSoundLog Vseg vk Good`**: on a good log, an accepted segment proof of `piSizeOf seq4` bytes
  with `1 ≤ n ≤ cap` proves its chain.
* **`VA_extract_log`**, **`VA_rel_log`**, **`V4_agg_extract_log`**: with `SegSoundLog`, an accepting
  `V_A` (or `V4`'s `A` branch) on a good log yields `Rel`'s leaf clause: `aggWit π = some (s, n)`,
  `n ≤ chainCap`, `c = leafStmt (chainEnd s n) n`. No factor `k` enters any error.

Controls: `segSoundLog_lucky` (positive: a toy verifier whose acceptance rests on one oracle
answer meets `SegSoundLog` on the logs with no zero answer), `not_segSound_lucky` (negative: the
same verifier fails `SegSound`, so the log form is strictly weaker and is the satisfiable one),
`not_segSoundLog_true` (negative: an accept-all verifier fails `SegSoundLog`), and for the size
hypothesis `segSoundLog_off`/`not_segSoundLog0_off`/`VA_off_reject` (negative: a verifier accepting
exactly the proofs of another size meets `SegSoundLog`, fails the size-free form `SegSoundLog0`, and
never lets `V_A` accept, so the size-free form asks for runs `V_A` never makes).
-/

namespace FR
namespace Rev4
open RecursionFast

/-! ## `runLog` through `bind` and `seqAll` -/

theorem runLog_bind {α β : Type} (p : OProg α) (f : α → OProg β) (L : Log) :
    (p.bind f).runLog L = (p.runLog L).bind fun a => (f a).runLog L := by
  induction p with
  | ret a => rfl
  | query q k ih =>
    simp only [OProg.bind, OProg.runLog]
    cases L.find? (fun e => e.1 = q) with
    | none => rfl
    | some e => simp [ih]

/-- **Every program of an accepting `seqAll` accepts on the same log.** -/
theorem runLog_seqAll {ps : List (OProg Bool)} {L : Log} (h : (seqAll ps).runLog L = some true) :
    ∀ p ∈ ps, p.runLog L = some true := by
  induction ps with
  | nil => simp
  | cons p ps ih =>
    simp only [seqAll, runLog_bind] at h
    cases hp : p.runLog L with
    | none => simp [hp] at h
    | some b =>
      rw [hp] at h
      cases b with
      | false => simp [OProg.runLog] at h
      | true =>
        simp only [Option.bind_some, ite_true] at h
        intro p' hp'
        rcases List.mem_cons.1 hp' with rfl | hp'
        · exact hp
        · exact ih h p' hp'

/-! ## `V_A` on a log -/

/-- **`V_A` under `runLog`**: an accepting run on the log `L` has views meeting the checks, and
every segment program accepts on `L`. -/
theorem VA_sound_log {segSize : ℕ} {Vseg : SegProgs} {vk c : Digest} {π : Proof} {L : Log}
    (h : (VAwith segSize Vseg vk c π).runLog L = some true) :
    π.size = 48 + (byteAt π 1).toNat * segSize ∧
    ∃ vs, (aggSegs segSize (byteAt π 1).toNat π).mapM segView = some vs ∧
      aggChecks c (rdLE64 π 8) (bytesAt π 16 32) vs = true ∧
      ∀ p ∈ segProgs Vseg vk (aggSegs segSize (byteAt π 1).toNat π) vs, p.runLog L = some true := by
  simp only [VAwith] at h
  split at h
  · next hsz =>
    split at h
    · next vs hvs =>
      split at h
      · next hc => exact ⟨hsz.1, vs, hvs, hc, runLog_seqAll h⟩
      · simp [OProg.runLog] at h
    · simp [OProg.runLog] at h
  · simp [OProg.runLog] at h

/-- **Segment soundness in `KS`'s form** (R-4-M1, M2; INT-10): on a good log (for the real
programs: within `logCap` with potential below `1`), an accepted segment proof of `piSizeOf seq4`
bytes and length `1 ≤ n ≤ cap` proves its chain. `V_A` asserts the size and the bounds before it
runs any segment program (`VAwith`'s size check, `piSize_aggSegs`; `aggChecks`). -/
def SegSoundLog (Vseg : SegProgs) (vk : Digest) (Good : Log → Prop) : Prop :=
  ∀ L π v, Good L → segView π = some v → π.size = piSizeOf seq4 → 1 ≤ v.n → v.n ≤ v.kind.cap →
    (Vseg v.kind vk (segC v) π).runLog L = some true → chainEnd v.start v.n = v.h

theorem mapM_segView_forall₂ {l : List Proof} {vs : List SegView} (h : l.mapM segView = some vs) :
    List.Forall₂ (fun p v => segView p = some v) l vs := by
  induction l generalizing vs with
  | nil => simp at h; subst h; exact .nil
  | cons p l ih =>
    simp only [List.mapM_cons, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def,
      Option.some.injEq] at h
    obtain ⟨v, hv, vs', hvs', rfl⟩ := h
    exact .cons hv (ih hvs')

/-- **Chained views compose** (`chainOk`: `s_{i+1} = e_i`; `chainEnd_add`), stated on the views'
fields alone. -/
theorem compose_viewsL : ∀ (a : SegView) (l : List SegView), chainOk (a :: l) = true →
    (∀ v ∈ a :: l, chainEnd v.start v.n = v.h) →
    chainEnd a.start ((a :: l).map SegView.n).sum = ((a :: l).getLast (List.cons_ne_nil _ _)).h
  | a, [], _, hs => by simpa using hs a (by simp)
  | a, b :: l, hc, hs => by
    simp only [chainOk, Bool.and_eq_true, decide_eq_true_eq] at hc
    have ih := compose_viewsL b l hc.2 fun v hv => hs v (List.mem_cons_of_mem _ hv)
    rw [List.map_cons, List.sum_cons, chainEnd_add, hs a (by simp), ← hc.1, ih,
      List.getLast_cons (List.cons_ne_nil _ _)]

/-- **`V_A` extracts the leaf witness on a good log** (the `FinalLaw` shape): with `SegSoundLog`
(which uses `V_A`'s size check and its `1 ≤ nᵢ ≤ cap` check), an accepting `runLog` of `V_A` at
`seq4`'s segment size yields `Rel`'s leaf clause. -/
theorem VA_extract_log {Vseg : SegProgs} {vk c : Digest} {π : Proof} {L : Log}
    {Good : Log → Prop} (hS : SegSoundLog Vseg vk Good) (hG : Good L)
    (h : (VAwith (piSizeOf seq4) Vseg vk c π).runLog L = some true) :
    ∃ s n, aggWit (piSizeOf seq4) π = some (s, n) ∧ n ≤ chainCap ∧
      c = leafStmt (chainEnd s n) n := by
  obtain ⟨hsz, vs, hvs, hc, hf⟩ := VA_sound_log h
  have hsz' := Snd.R4.piSize_aggSegs hsz
  set segs := aggSegs (piSizeOf seq4) (byteAt π 1).toNat π
  have h2 := mapM_segView_forall₂ hvs
  simp only [aggChecks, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true] at hc
  obtain ⟨⟨⟨⟨⟨hst, hk⟩, hr⟩, hsum⟩, hlast⟩, hch⟩ := hc
  have hseg : ∀ v ∈ vs, chainEnd v.start v.n = v.h := by
    intro v hv
    clear_value segs
    obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hv
    have hl := h2.length_eq
    have hpi : segView segs[i] = some vs[i] := (List.forall₂_iff_get.1 h2).2 i (by omega) hi
    have hmem : Vseg vs[i].kind vk (segC vs[i]) segs[i] ∈ segProgs Vseg vk segs vs := by
      unfold segProgs
      refine List.mem_map.2 ⟨(segs[i], vs[i]), ?_, rfl⟩
      have e : (segs.zip vs)[i]'(by simp; omega) = (segs[i], vs[i]) := by simp
      rw [← e]; exact List.getElem_mem _
    exact hS L _ _ hG hpi (hsz' _ (List.getElem_mem _)) (hr _ hv).1 (hr _ hv).2 (hf _ hmem)
  obtain ⟨a, l, rfl⟩ : ∃ a l, vs = a :: l := by
    cases vs with
    | nil => simp at hk
    | cons a l => exact ⟨a, l, rfl⟩
  have hcomp := compose_viewsL a l hch hseg
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

/-- The conclusion is exactly `Rel`'s leaf clause (for every acceptance predicate). -/
theorem VA_rel_log {Vseg : SegProgs} {vk c : Digest} {π : Proof} {L : Log}
    {Good : Log → Prop} (hS : SegSoundLog Vseg vk Good) (hG : Good L)
    (h : (VAwith (piSizeOf seq4) Vseg vk c π).runLog L = some true) (acc : Digest → Signed → Bool) :
    ∃ s n, aggWit (piSizeOf seq4) π = some (s, n) ∧ Rel acc c (.leaf s n) :=
  let ⟨s, n, hw, hn, hc⟩ := VA_extract_log hS hG h; ⟨s, n, hw, hn, hc⟩

/-- **`V4`'s `A` branch in `FinalLaw`'s shape** (`runLog` on a good log). -/
theorem V4_agg_extract_log {Vseg : SegProgs} {Vnode : NodeProgs} {vk c : Digest} {π : Proof}
    {L : Log} {Good : Log → Prop} (hk : kindOf4 π = .agg) (hS : SegSoundLog Vseg vk Good)
    (hG : Good L) (h : (V4with Vseg Vnode vk c π).runLog L = some true) :
    ∃ s n, aggWit (piSizeOf seq4) π = some (s, n) ∧ n ≤ chainCap ∧ c = leafStmt (chainEnd s n) n := by
  rw [V4_agg Vseg Vnode vk c π hk] at h; exact VA_extract_log hS hG h

/-! ## Controls -/

/-- A toy segment verifier whose decision rests on one oracle answer: it asks the proof's bytes and
accepts iff the answer is the zero digest (probability `2^-256` per proof under a random oracle). -/
def VsegLucky : SegProgs := fun _ _ _ π => .query π fun a => .ret (decide (a = dC 0))

/-- A 96-byte `L31` segment proof claiming the one-step chain `0 → 0` (false: `chainEnd 0 1 ≠ 0`). -/
def badSeg : Proof := ⟨(ctrlSeg (dC 0) (dC 0) 1).toArray⟩

theorem badSeg_view : segView badSeg = some ⟨.L31, dC 0, dC 0, 1⟩ := by decide +kernel

/-- (−) **`SegSound` (every trace) is false for `VsegLucky`**: the trace answers the one query with
`0` (R-4-M1). -/
theorem not_segSound_lucky (vk : Digest) : ¬ SegSound VsegLucky vk := by
  intro hS
  have h := hS badSeg _ [(badSeg, dC 0)] badSeg_view (by decide)
    (by simp [VsegLucky, OProg.runSeq])
  exact (Leaf.zero_table_control (R := ZMod 2)).2.2.2.1 h

/-- (+) **The same verifier meets `SegSoundLog`** on the logs with no zero answer (the complement
has probability at most the number of queries times `2^-256`). -/
theorem segSoundLog_lucky (vk : Digest) :
    SegSoundLog VsegLucky vk (fun L => ∀ e ∈ L, e.2 ≠ dC 0) := by
  intro L π v hG _ _ _ _ h
  simp only [VsegLucky, OProg.runLog] at h
  cases hf : L.find? (fun e => e.1 = π) with
  | none => simp [hf] at h
  | some e =>
    simp [hf] at h
    exact absurd h (hG e (List.mem_of_find?_eq_some hf))

/-- `π` zero-padded (or cut) to `n` bytes. -/
def padTo (π : Proof) (n : ℕ) : Proof := ⟨Array.ofFn fun i : Fin n => byteAt π i⟩

theorem padTo_size (π : Proof) (n : ℕ) : (padTo π n).size = n :=
  Array.size_ofFn (f := fun i : Fin n => byteAt π i)

/-- Zero padding reads the same bytes (`byteAt` reads `0` past the end). -/
theorem byteAt_padTo {π : Proof} {n : ℕ} (h : π.size ≤ n) : byteAt (padTo π n) = byteAt π := by
  funext k
  by_cases hk : k < n
  · have h1 : k < (padTo π n).size := by rw [padTo_size]; exact hk
    rw [byteAt, dif_pos h1]
    show (Array.ofFn fun i : Fin n => byteAt π i)[k]'(by rw [Array.size_ofFn]; exact hk) = byteAt π k
    simp
  · have h1 : ¬ k < (padTo π n).size := by rw [padTo_size]; exact hk
    have h2 : ¬ k < π.size := by omega
    simp only [byteAt, h1, h2, dite_false]

/-- `badSeg` padded to a segment proof's size (`piSizeOf seq4`), with the same view. -/
def badSegP : Proof := padTo badSeg (piSizeOf seq4)

theorem badSegP_view : segView badSegP = some ⟨.L31, dC 0, dC 0, 1⟩ := by
  have h : byteAt badSegP = byteAt badSeg :=
    byteAt_padTo (by rw [piSizeOf_seq4]; decide)
  rw [← badSeg_view]; simp only [segView, bytesAt, rdLE64, h]

/-- (−) **`SegSoundLog` is not vacuous**: a verifier accepting every proof fails it on every
log, at the one-step `L31` view `0 → 0` of a proof of `piSizeOf seq4` bytes (`1 ≤ n` holds there). -/
theorem not_segSoundLog_true (vk : Digest) (Good : Log → Prop) (L : Log) (hG : Good L) :
    ¬ SegSoundLog (fun _ _ _ _ => .ret true) vk Good := fun h =>
  (Leaf.zero_table_control (R := ZMod 2)).2.2.2.1
    (h L badSegP _ hG badSegP_view (padTo_size _ _) (by decide) (by decide) rfl)

/-! ### The size hypothesis (INT-10) -/

/-- **`SegSoundLog` without the size hypothesis** (its form before INT-10), for the control only. -/
def SegSoundLog0 (Vseg : SegProgs) (vk : Digest) (Good : Log → Prop) : Prop :=
  ∀ L π v, Good L → segView π = some v → 1 ≤ v.n → v.n ≤ v.kind.cap →
    (Vseg v.kind vk (segC v) π).runLog L = some true → chainEnd v.start v.n = v.h

/-- A segment verifier accepting exactly the proofs that are not of `piSizeOf seq4` bytes. -/
def VsegOff : SegProgs := fun _ _ _ π => .ret (decide (π.size ≠ piSizeOf seq4))

/-- (+) **`VsegOff` meets `SegSoundLog`** on every log: it accepts no proof of the right size. -/
theorem segSoundLog_off (vk : Digest) (Good : Log → Prop) : SegSoundLog VsegOff vk Good := by
  intro L π v _ _ hπ _ _ h
  simp [VsegOff, OProg.runLog, hπ] at h

/-- (−) **`VsegOff` fails the size-free `SegSoundLog0`** on every good log: it accepts the
96-byte `badSeg`, whose chain `0 → 0` is false. -/
theorem not_segSoundLog0_off (vk : Digest) (Good : Log → Prop) (L : Log) (hG : Good L) :
    ¬ SegSoundLog0 VsegOff vk Good := fun h =>
  (Leaf.zero_table_control (R := ZMod 2)).2.2.2.1
    (h L badSeg _ hG badSeg_view (by decide) (by decide)
      (by simp [VsegOff, OProg.runLog, piSizeOf_seq4]; decide))

/-- (−) **`V_A` never runs `VsegOff`'s accepted proofs**: with `VsegOff`, `V_A` at `seq4`'s segment
size accepts on no log. So `SegSoundLog0` asks for runs `V_A` never makes, and `SegSoundLog` (with
the size hypothesis) is what `V_A` needs. -/
theorem VA_off_reject (vk c : Digest) (π : Proof) (L : Log) :
    (VAwith (piSizeOf seq4) VsegOff vk c π).runLog L ≠ some true := by
  intro h
  obtain ⟨hsz, vs, hvs, hc, hf⟩ := VA_sound_log h
  set segs := aggSegs (piSizeOf seq4) (byteAt π 1).toNat π
  have hl := (mapM_segView_forall₂ hvs).length_eq
  simp only [aggChecks, Bool.and_eq_true, decide_eq_true_eq] at hc
  obtain ⟨⟨⟨⟨⟨-, hk⟩, -⟩, -⟩, -⟩, -⟩ := hc
  have hi : 0 < segs.length := by omega
  have hmem : VsegOff (vs[0]'(by omega)).kind vk (segC (vs[0]'(by omega))) segs[0] ∈
      segProgs VsegOff vk segs vs := by
    unfold segProgs
    refine List.mem_map.2 ⟨(segs[0], vs[0]'(by omega)), ?_, rfl⟩
    have e : (segs.zip vs)[0]'(by simp; omega) = (segs[0], vs[0]'(by omega)) := by simp
    rw [← e]; exact List.getElem_mem _
  have hp := Snd.R4.piSize_aggSegs hsz _ (List.getElem_mem hi)
  have := hf _ hmem
  simp [VsegOff, OProg.runLog, hp] at this

end Rev4
end FR
