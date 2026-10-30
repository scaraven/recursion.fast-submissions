-- G6: this module also holds the former modules `FRSoundness4R4Link` (one section each, in import order).
import FRVerifierC4

section G6_FRSoundness4R4Link

-- New for `flock-recursive` (BLUEPRINT revision 4.1, A.9 `finSh`; stage R4b, for P4c's F2).

/-!
# A segment's `finSh` has no link weight

`gShCore` runs `linkWAll`/`linkOps` for every kind. On the segment program the kind index is
`(KindP.ofSeg σ).tix = .L32`, not a node, so the concrete implementation (`implSeg (implC …)`) and
its specification (`specSeg (specC …)`) both answer `0^8` (`linkWAll_segC`, `linkWAll_segS`; any
implementation meeting the specification does, `linkWAll_seg_of_meets`). Then:

* **`linkSum_zero`**: `relSh`'s link term `linkSum 0^8 κ_s n acc pow` is `acc`;
* **`run_linkOps_zero`** (the program): with `0^8` in `linkWAll`'s register `b + 25`, `linkOps ks b`
  passes and its accumulator register `b + 57` holds register `b + 22`'s value: the 32 link ops add
  nothing to `finSh` (ii)'s weight. So P4c's `wSumSeg` (no link term) is the program's value.
-/

namespace FR.Snd.R4
open RecursionFast Rev4

/-- The link families' sum over `0^8` is the accumulator. -/
theorem linkSum_zero (ks : F) : ∀ (n : ℕ) (acc pow : F),
    linkSum (Array.replicate nLinkFam 0) ks n acc pow = acc
  | 0, _, _ => rfl
  | n + 1, acc, pow => by
    rw [linkSum, linkSum_zero ks n, Array.getD_eq_getD_getElem?, Array.getElem?_replicate]
    split_ifs <;> simp

/-- The segment's concrete `linkWAll` is `0^8`. -/
theorem linkWAll_segC (fin : Finals) (lRows : List Circ.Row) (κs₀ : F) (σ : SegKind) (tt rr : Array F) :
    (implSeg (Impl.implC fin lRows κs₀)).linkWAll (KindP.ofSeg σ).tix tt rr =
      Array.replicate nLinkFam 0 := rfl

/-- The segment's specified `linkWAll` is `0^8`. -/
theorem linkWAll_segS (fin : Finals) (lRows : List Circ.Row) (κs₀ : F) (σ : SegKind) (tt rr : Array F) :
    (specSeg (Impl.specC fin lRows κs₀)).linkWAll (KindP.ofSeg σ).tix tt rr =
      Array.replicate nLinkFam 0 := rfl

/-- Any implementation meeting the segment's specification answers `0^8`. -/
theorem linkWAll_seg_of_meets {impl : OpImpl} {fin : Finals} {lRows : List Circ.Row} {κs₀ : F}
    (h : impl.Meets (specSeg (Impl.specC fin lRows κs₀))) (σ : SegKind) (tt rr : Array F) :
    impl.linkWAll (KindP.ofSeg σ).tix tt rr = Array.replicate nLinkFam 0 := by
  rw [h.2.2.2.2.2.2.2.2.2.2.2.2.2.1]; rfl

/-! ## The program: `linkOps` over `0^8` -/

section Run
variable (impl : OpImpl) (κ : Kind) (inp : Input)

/-- Family `f`'s four ops (`linkOps`' body). -/
def linkFam (ks b f : ℕ) : List Op :=
  [.getF (b + 25) f, .mulF (b + (26 + 4 * f)) (b + (27 + 4 * f)),
   .addF (if f = 0 then b + 22 else b + (25 + 4 * f)) (b + (28 + 4 * f)),
   .mulF (b + (26 + 4 * f)) ks]

theorem linkOps_eq (ks b : ℕ) : linkOps ks b = (List.range' 0 8).flatMap (linkFam ks b) := by
  rw [linkOps, List.range_eq_range']; rfl

theorem rd_appL (X : Array Val) (L vs : List Val) {i : ℕ} (hi : i < X.size + L.length) :
    rd (X ++ (L ++ vs).toArray) i = rd (X ++ L.toArray) i := by
  rw [← app_app, rd_app_left _ _ (by simpa using hi)]

theorem rd_appR (X : Array Val) (L vs : List Val) (j : ℕ) :
    rd (X ++ (L ++ vs).toArray) (X.size + L.length + j) = vs.getD j default := by
  rw [← app_app, show X.size + L.length = (X ++ L.toArray).size by simp, rd_app]

/-- One pure op that yields one value and passes. -/
theorem pureRun_step {op : Op} {ops : List Op} {X : Array Val} {L : List Val} {v : Val}
    (h : evalOp impl κ inp (X ++ L.toArray) op = .vals [v] true) :
    pureRun impl κ inp (op :: ops) X L = pureRun impl κ inp ops X (L ++ [v]) := by
  simp only [pureRun, h, Bool.true_and]
  cases pureRun impl κ inp ops X (L ++ [v]) <;> rfl

/-- One family over `0^8`: it appends `0, 0, acc, pow·κ_s`. -/
theorem pureRun_linkFam (X : Array Val) (L : List Val) (ks b f : ℕ) (rest : List Op) {k p a : F}
    (hsz : X.size + L.length = b + 27 + 4 * f) (hk : ks < b + 27 + 4 * f)
    (hW : rd (X ++ L.toArray) (b + 25) = .af (Array.replicate nLinkFam 0))
    (hks : rd (X ++ L.toArray) ks = .f k) (hp : rd (X ++ L.toArray) (b + (26 + 4 * f)) = .f p)
    (ha : rd (X ++ L.toArray) (if f = 0 then b + 22 else b + (25 + 4 * f)) = .f a) :
    pureRun impl κ inp (linkFam ks b f ++ rest) X L =
      pureRun impl κ inp rest X (L ++ [.f 0, .f 0, .f a, .f (p * k)]) := by
  have hA : (if f = 0 then b + 22 else b + (25 + 4 * f)) < b + 27 + 4 * f := by split_ifs <;> omega
  have g0 : (Array.replicate nLinkFam (0 : F)).getD f 0 = 0 := by
    rw [Array.getD_eq_getD_getElem?, Array.getElem?_replicate]; split_ifs <;> rfl
  have e1 : rd (X ++ (L ++ [Val.f 0]).toArray) (b + (27 + 4 * f)) = .f 0 := by
    rw [show b + (27 + 4 * f) = X.size + L.length + 0 by omega, rd_appR]; rfl
  have e2 : rd (X ++ (L ++ [Val.f 0, Val.f 0]).toArray) (b + (28 + 4 * f)) = .f 0 := by
    rw [show b + (28 + 4 * f) = X.size + L.length + 1 by omega, rd_appR]; rfl
  simp only [linkFam, List.cons_append, List.nil_append]
  rw [pureRun_step impl κ inp (v := .f 0) (by simp only [evalOp, hW, Val.toAF, g0]),
    pureRun_step impl κ inp (v := .f 0) (by
      simp only [evalOp, rd_appL X L _ (show b + (26 + 4 * f) < X.size + L.length by omega), hp, e1,
        Val.toF, mul_zero]),
    pureRun_step impl κ inp (v := .f a) (by
      rw [List.append_assoc, List.singleton_append]
      simp only [evalOp, rd_appL X L _ (show (if f = 0 then b + 22 else b + (25 + 4 * f)) <
          X.size + L.length by omega), ha, e2, Val.toF,
        add_zero]),
    pureRun_step impl κ inp (v := .f (p * k)) (by
      rw [List.append_assoc, List.append_assoc, List.singleton_append, List.singleton_append]
      simp only [evalOp, rd_appL X L _ (show b + (26 + 4 * f) < X.size + L.length by omega), hp,
        rd_appL X L _ (show ks < X.size + L.length by omega), hks, Val.toF])]
  simp only [List.append_assoc, List.cons_append, List.nil_append]

theorem pureRun_linkFams (X : Array Val) (ks b : ℕ) (rest : List Op) : ∀ (m f : ℕ) (L : List Val) (k p a : F),
    X.size + L.length = b + 27 + 4 * f → ks < b + 27 →
    rd (X ++ L.toArray) (b + 25) = .af (Array.replicate nLinkFam 0) →
    rd (X ++ L.toArray) ks = .f k → rd (X ++ L.toArray) (b + (26 + 4 * f)) = .f p →
    rd (X ++ L.toArray) (if f = 0 then b + 22 else b + (25 + 4 * f)) = .f a →
    ∃ M, pureRun impl κ inp ((List.range' f m).flatMap (linkFam ks b) ++ rest) X L =
        pureRun impl κ inp rest X (L ++ M) ∧ M.length = 4 * m ∧ (0 < m → M.getD (4 * m - 2) default = .f a)
  | 0, _, L, _, _, _, _, _, _, _, _, _ => ⟨[], by simp, rfl, fun h => absurd h (by omega)⟩
  | m + 1, f, L, k, p, a, hsz, hk, hW, hks, hp, ha => by
    rw [List.range'_succ, List.flatMap_cons, List.append_assoc,
      pureRun_linkFam impl κ inp X L ks b f _ hsz (by omega) hW hks hp ha]
    set V : List Val := [.f 0, .f 0, .f a, .f (p * k)]
    have hl : (L ++ V).length = L.length + 4 := by simp [V]
    obtain ⟨M, h1, h2, h3⟩ := pureRun_linkFams X ks b rest m (f + 1) (L ++ V) k (p * k) a (by omega) hk
      (by rw [rd_appL X L _ (by omega)]; exact hW) (by rw [rd_appL X L _ (by omega)]; exact hks)
      (by rw [show b + (26 + 4 * (f + 1)) = X.size + L.length + 3 by omega, rd_appR]; rfl)
      (by rw [if_neg (by omega), show b + (25 + 4 * (f + 1)) = X.size + L.length + 2 by omega,
          rd_appR]; rfl)
    refine ⟨V ++ M, by rw [h1, List.append_assoc], by simp [V, h2]; ring, fun _ => ?_⟩
    rcases Nat.eq_zero_or_pos m with rfl | hm
    · rfl
    · rw [List.getD_append_right _ _ _ _ (by simp [V]; omega)]
      rw [show 4 * (m + 1) - 2 - V.length = 4 * m - 2 by simp [V]; omega]
      exact h3 hm

/-- **`linkOps` over `0^8`** (a segment's `finSh`): it passes, appends 32 registers, and its
accumulator `b + 57` holds register `b + 22`'s value. -/
theorem run_linkOps_zero (X : Array Val) (L : List Val) (ks b : ℕ) {k p a : F}
    (hsz : X.size + L.length = b + 27) (hk : ks < b + 27)
    (hW : rd (X ++ L.toArray) (b + 25) = .af (Array.replicate nLinkFam 0))
    (hks : rd (X ++ L.toArray) ks = .f k) (hp : rd (X ++ L.toArray) (b + 26) = .f p)
    (ha : rd (X ++ L.toArray) (b + 22) = .f a) :
    ∃ M, pureRun impl κ inp (linkOps ks b) X L = some (L ++ M, true) ∧ M.length = 32 ∧
      rd (X ++ (L ++ M).toArray) (b + 57) = .f a := by
  obtain ⟨M, h1, h2, h3⟩ := pureRun_linkFams impl κ inp X ks b [] 8 0 L k p a hsz hk hW hks hp ha
  rw [List.append_nil] at h1
  refine ⟨M, by rw [linkOps_eq, h1]; rfl, h2, ?_⟩
  rw [show b + 57 = X.size + L.length + 30 by omega, rd_appR]
  exact h3 (by norm_num)

/-! ## Controls -/

/-- Control (−): a nonzero family weight does move the accumulator (`W₀ = 1`, `pow = 1`). -/
theorem linkSum_ctl : linkSum #[(1 : F)] 0 nLinkFam 0 1 = 1 := by simp [linkSum, nLinkFam]

/-- Control (+): a node's concrete `linkWAll` is the node's link weights, not `0^8`. -/
theorem linkWAll_nodeC (fin : Finals) (lRows : List Circ.Row) (κs₀ : F) (ν : NodeKind) (tt rr : Array F) :
    (Impl.implC fin lRows κs₀).linkWAll (KindP.ofNode ν).tix tt rr =
      NodeI.linkWAllI (tt.extract 0 16) (tt.extract 16 26) (rr.extract 0 16) (rr.extract 16 26) := rfl

end Run

/-! ## The proof size the program layer assumes (`runLog_chain4`'s `hπ`) -/

/-- **A node's proof has `seq4`'s size**: `kindOf4` accepts a node byte only at `piSizeOf seq4`. -/
theorem piSize_node4 {π : Proof} {ν : NodeKind} (h : kindOf4 π = .node ν) : π.size = piSizeOf seq4 := by
  unfold kindOf4 at h; dsimp only at h
  split_ifs at h <;> first | assumption | (split at h <;> simp_all)

/-- **Each segment of an aggregate has `segSize` bytes** when the aggregate passes `V_A`'s size
check (`π.size = 48 + k · segSize`). -/
theorem piSize_aggSegs {segSize k : ℕ} {π : Proof} (h : π.size = 48 + k * segSize) :
    ∀ s ∈ aggSegs segSize k π, s.size = segSize := by
  intro s hs
  obtain ⟨i, hi, rfl⟩ := List.mem_map.1 hs
  rw [List.mem_range] at hi
  have : 48 + (i + 1) * segSize ≤ π.size := by rw [h]; nlinarith
  simp only [ByteArray.size_extract]
  rw [Nat.min_eq_left this]; rw [Nat.add_mul]; omega


end FR.Snd.R4

end G6_FRSoundness4R4Link

section G6_FRSoundness4Agg

-- New for `flock-recursive` (BLUEPRINT revision 4.1, B-11, B-12; stage S-G12′; adopted from the R-4
-- review's probe `logs/R-4/build/src/R4Probe.lean`, ruling R-4-M1/M2). INT-10 (R4i's F1): the
-- size hypothesis `π.size = piSizeOf seq4` of `SegSoundLog`, supplied by `V_A`'s size check.

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
      · next hc => exact ⟨hsz.1, vs, hvs, hc, fun p hp => runLog_seqAll h p (mem_intersperse_of_mem hp)⟩
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

end G6_FRSoundness4Agg
