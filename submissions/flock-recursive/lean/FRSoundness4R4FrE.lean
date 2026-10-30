-- G6: this module also holds the former modules `FRSoundness4R4Acc`, `FRSoundness4R4Ex`, `FRSoundness4R4Fld`, `FRSoundness4R4View`, `FRSoundness4R4Rnd`, `FRSoundness4RsvStack` (one section each, in import order).
import FRSoundness4R4FinSh
import FRSoundness4R4Kind
import FRSoundness4P4aSeg
import FRSoundness4P4bE
import FRSoundness4P4aNames
import FRSoundness4Agg

section G6_FRSoundness4R4Acc

-- New for `flock-recursive` (BLUEPRINT revision 4.1, A.9; stage R4c).
/-!
# The finals' fields on an accepted run of `gen4 seq4 p (finOps4 P)`

**`fields_of_accept4`**: an accepted run is a `SkRun4`, and every field of `finalsOf P` after
`finRS` runs (relocated) from a register file extending the skeleton's, with flag `true`.
**`relLr4_of_accept`** (template for the others): then `finLr`'s relation holds there
(`flag_gFinLr`, `pureRun_det`), its registers being skeleton registers (`skeleton4_out_lt`).
-/

namespace FR.Snd.R4
open RecursionFast Rev4

variable {impl : OpImpl} {p : KindP} {inp : Input}

theorem rest_finalsOf_length (P : FinP) : (finalsOf P).rest.length = 12 := by
  simp [Finals.rest, nLevels]

/-- **The fields of an accepted run.** -/
theorem fields_of_accept4 (P : FinP) {tr : Trace}
    (h : semIR impl (gen4 seq4 p (finOps4 P)) inp tr = some true) :
    ∃ y, SkRun4 impl p inp tr y ∧ ∃ (zh : List Reg) (Rs : ℕ → Array Val),
      (∀ k ≤ 12, ExtA (#[] ++ y.1.toArray) (Rs k)) ∧
      ∀ k (hk : k < 12), ∃ (ex : Array (List Reg)) (L : List Val),
        pureRun impl p.tix inp ((((finalsOf P).rest[k]'(by rw [rest_finalsOf_length]; exact hk))
          ⟨(skeleton4 seq4 p).2.outs, zh, ex⟩ (Rs k).size).1.map (reloc P.S)) (Rs k) [] = some (L, true) := by
  rw [finOps4_eq] at h
  obtain ⟨y, hy, hf, -, L₀, -, Rs, h0, hrest⟩ := accept_chain4 impl seq4 p inp _ _ (noAsk_finOps4 P) h
  obtain ⟨hl, hq⟩ := fsQ_gen4 impl inp seq4 p shOK_seq4 _ h
  rw [fsMsgs4_len] at hl hq
  have hlen : ((relocFin P.S (finalsOf P)).rest ++ [capF P.S]).length = 13 := by
    rw [List.length_append, relocFin_rest, List.length_map, rest_finalsOf_length]; rfl
  refine ⟨y, ⟨hy, hf, hl, hq⟩,
    ((finalsOf P).finRS ⟨(skeleton4 seq4 p).2.outs, [], #[]⟩ (skeleton4 seq4 p).2.next).2, Rs, ?_,
    fun k hk => ?_⟩
  · intro k hk
    induction k with
    | zero => rw [h0]; exact ExtA.app _ _
    | succ k ih =>
      obtain ⟨L, -, he⟩ := hrest k (by rw [hlen]; omega)
      rw [he]; exact (ih (by omega)).trans (ExtA.app _ _)
  · obtain ⟨L, hL, -⟩ := hrest k (by rw [hlen]; omega)
    have e : ((relocFin P.S (finalsOf P)).rest ++ [capF P.S])[k]'(by rw [hlen]; omega) =
        relocF P.S ((finalsOf P).rest[k]'(by rw [rest_finalsOf_length]; exact hk)) := by
      rw [List.getElem_append_left (by rw [relocFin_rest, List.length_map, rest_finalsOf_length]; exact hk)]
      simp only [relocFin_rest, List.getElem_map]
    rw [e] at hL
    exact ⟨_, L, hL⟩

/-- The skeleton's registers are positive in number. -/
theorem skel_pos4 {tr : Trace} {y : List Val × List Bool × Trace} (h : SkRun4 impl p inp tr y) :
    0 < (#[] ++ y.1.toArray).size := by
  rw [← skeleton4_next impl p.tix inp seq4 p h.ref]
  rw [skeleton4_eq_cAt4]
  exact lt_of_lt_of_le (by rw [(cAt4_ctl seq4 p).2.1]; omega)
    (cAt4_next_mono seq4 p (m := 1) (by decide) le_rfl)

/-- Every register named by a phase is a skeleton register. -/
theorem outsOf_lt4 {tr : Trace} {y : List Val × List Bool × Trace} (h : SkRun4 impl p inp tr y)
    (zh : List Reg) (ex : Array (List Reg)) (name : String) :
    ∀ x ∈ outsOf ⟨(skeleton4 seq4 p).2.outs, zh, ex⟩ name, x < (#[] ++ y.1.toArray).size := by
  intro x hx; simp only [outsOf] at hx; exact skeleton4_out_lt p h.ref _ x hx

/-- `finLr`'s registers are named registers (stated for an abstract `fi`: instantiating it at the
skeleton must not make the unifier evaluate `skeleton4`). -/
theorem hin_Lr {fi : FinIn} {n : ℕ} (hsk : ∀ name, ∀ x ∈ outsOf fi name, x < n) (hn : 0 < n) (P : FinP) :
    ∀ x ∈ (coordsR fi "Lr1").take P.lrR ++ chals fi "Lr2" P.lrR ++
      [(outsOf fi "Lr3").headD 0, claimN fi "Lr2"], x < n := by
  intro x hx
  simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hx
  rcases hx with (hx | hx) | rfl | rfl
  · exact hsk "Lr1" x (List.mem_of_mem_drop (List.mem_of_mem_take hx))
  · exact hsk "Lr2" x (List.mem_of_mem_drop (List.mem_of_mem_take hx))
  · exact headD_lt (hsk "Lr3") hn
  · exact getLastD_lt (hsk "Lr2") hn

/-- **`finLr`'s relation on an accepted run.** -/
theorem relLr4_of_accept (P : FinP) {tr : Trace}
    (h : semIR impl (gen4 seq4 p (finOps4 P)) inp tr = some true) :
    ∃ y, SkRun4 impl p inp tr y ∧ ∃ (fi : FinIn) (R : Array Val),
      fi.outs = (skeleton4 seq4 p).2.outs ∧ ExtA (#[] ++ y.1.toArray) R ∧
      relLr4 p.tix inp fi R P = true := by
  obtain ⟨y, hS, zh, Rs, hext, hf⟩ := fields_of_accept4 P h
  obtain ⟨ex, L, hL⟩ := hf 3 (by decide)
  have e : (finalsOf P).rest[3]'(by rw [rest_finalsOf_length]; decide) = gFinLr P := by
    simp only [Finals.rest, finalsOf, List.cons_append, List.getElem_cons_succ, List.getElem_cons_zero]
  rw [e] at hL
  have hE := hext 3 (by decide)
  have hpos := skel_pos4 hS
  have hsk : ∀ name, ∀ x ∈ outsOf ⟨(skeleton4 seq4 p).2.outs, zh, ex⟩ name, x < (Rs 3).size :=
    fun name x hx => Nat.lt_of_lt_of_le (outsOf_lt4 (p := p) hS zh ex name x hx) hE.1
  obtain ⟨L', hL', -⟩ := flag_gFinLr impl p.tix inp ⟨(skeleton4 seq4 p).2.outs, zh, ex⟩ (Rs 3) P
    (hin_Lr hsk (lt_of_lt_of_le hpos hE.1) P)
  exact ⟨y, hS, ⟨(skeleton4 seq4 p).2.outs, zh, ex⟩, Rs 3, rfl, hE, pureRun_det hL hL'⟩

end FR.Snd.R4

end G6_FRSoundness4R4Acc

section G6_FRSoundness4R4Ex

-- New for `flock-recursive` (BLUEPRINT revision 4.1, A.9; stage R4d).

/-!
# The finals' exports on an accepted run (`exAt`'s bookkeeping)

`Finals.ops` passes field `k` the exports `exAt … k` of the fields before it, computed at the
fold's own bases `baseAt … k`. **`exAt_succ`**: field `k`'s exports are pushed at base
`baseAt … k`. **`fields_ex4`**: on an accepted run of `gen4 seq4 p (finOps4 P)` the register file
`Rs k` that field `k` runs from has size `baseAt … k`, so `Ex (k + 1)` is `Ex k` with field `k`'s
exports at `(Rs k).size` pushed: `lrEx` of `finE` names `finLr`'s exports (`lrEx_eq4`).
-/

namespace FR.Snd.R4
open RecursionFast Rev4

section ExAt
variable (outs : Array (List Reg)) (zh : List Reg)

/-- **The base the fold gives field `k`** (as `exAt`, the exports). -/
def baseAt : List FinField → ℕ → Array (List Reg) → ℕ → ℕ
  | [], b, _, _ => b
  | _ :: _, b, _, 0 => b
  | f :: fs, b, ex, k + 1 =>
    baseAt fs (b + opsOut (f ⟨outs, zh, ex⟩ b).1) (ex.push (f ⟨outs, zh, ex⟩ b).2) k

theorem exAt_zero (fs : List FinField) (b : ℕ) (ex : Array (List Reg)) :
    exAt outs zh fs b ex 0 = ex ∧ baseAt outs zh fs b ex 0 = b := by
  cases fs <;> exact ⟨rfl, rfl⟩

/-- **One step of the fold**: field `k`'s exports, at base `baseAt … k`, are pushed. -/
theorem exAt_succ : ∀ (fs : List FinField) (b : ℕ) (ex : Array (List Reg)) (k : ℕ) (hk : k < fs.length),
    exAt outs zh fs b ex (k + 1) = (exAt outs zh fs b ex k).push
        ((fs[k]'hk) ⟨outs, zh, exAt outs zh fs b ex k⟩ (baseAt outs zh fs b ex k)).2 ∧
      baseAt outs zh fs b ex (k + 1) = baseAt outs zh fs b ex k +
        opsOut ((fs[k]'hk) ⟨outs, zh, exAt outs zh fs b ex k⟩ (baseAt outs zh fs b ex k)).1
  | [], _, _, _, hk => absurd hk (by simp)
  | f :: fs, b, ex, 0, _ => by cases fs <;> exact ⟨rfl, rfl⟩
  | f :: fs, b, ex, k + 1, hk => by
    simp only [exAt, baseAt, List.getElem_cons_succ]
    exact exAt_succ fs _ _ k (by simpa using hk)

end ExAt

/-! ## `finRS`'s exports are its registers (revision 4.1's `gFinRS`) -/

/-- `gFinRS` appends `7 + 4·(1 + 128·8) + 10` registers. -/
theorem opsOut_gFinRS (P : FinP) (fi : FinIn) (b : ℕ) : opsOut (gFinRS P fi b).1 = 4117 := by
  simp only [gFinRS, opsOut_append]
  rw [opsOut_claimOps, opsOut_claimOps, opsOut_claimOps, opsOut_claimOps]
  · simp [opsOut, gRsTail, Op.outs, elemW]
  all_goals intro; rfl

/-- **`gFinRS`'s exports are among its registers.** -/
theorem gFinRS_ex_lt (P : FinP) (fi : FinIn) (b : ℕ) :
    ∀ x ∈ (gFinRS P fi b).2, x < b + opsOut (gFinRS P fi b).1 := by
  rw [opsOut_gFinRS]
  simp only [Reg]
  intro x hx
  simp only [gFinRS, elemW, List.mem_append, List.mem_map, List.mem_range, List.mem_cons,
    List.not_mem_nil, or_false, Nat.reduceMul, Nat.reduceAdd] at hx
  rcases hx with ⟨j, hj, rfl⟩ | rfl
  · have : j * 1025 ≤ 3 * 1025 := Nat.mul_le_mul_right _ (by omega)
    omega
  · omega

variable {impl : OpImpl} {p : KindP} {inp : Input}

/-- **The fields of an accepted run, with their exports**: field `k` of `finalsOf P` runs
(relocated) from `Rs k` with exports `Ex k` (`k + 1` of them) at base `(Rs k).size`, flag `true`;
`Rs (k + 1)` appends its output and `Ex (k + 1)` pushes its exports. -/
theorem fields_ex4 (P : FinP) {tr : Trace}
    (h : semIR impl (gen4 seq4 p (finOps4 P)) inp tr = some true) :
    ∃ y, SkRun4 impl p inp tr y ∧ ∃ (zh : List Reg) (Rs : ℕ → Array Val) (Ex : ℕ → Array (List Reg)),
      (∀ k ≤ 12, ExtA (#[] ++ y.1.toArray) (Rs k)) ∧ (∀ x ∈ zh, x < (Rs 0).size) ∧
      ∀ k (hk : k < 12), (Ex k).size = k + 1 ∧ ∃ L : List Val,
        pureRun impl p.tix inp ((((finalsOf P).rest[k]'(by rw [rest_finalsOf_length]; exact hk))
          ⟨(skeleton4 seq4 p).2.outs, zh, Ex k⟩ (Rs k).size).1.map (reloc P.S)) (Rs k) [] = some (L, true) ∧
        Rs (k + 1) = Rs k ++ L.toArray ∧
        Ex (k + 1) = (Ex k).push (((finalsOf P).rest[k]'(by rw [rest_finalsOf_length]; exact hk))
          ⟨(skeleton4 seq4 p).2.outs, zh, Ex k⟩ (Rs k).size).2 := by
  rw [finOps4_eq] at h
  obtain ⟨y, hy, hf, hnx, L₀, h0L, Rs, h0, hrest⟩ := accept_chain4 impl seq4 p inp _ _ (noAsk_finOps4 P) h
  obtain ⟨hl, hq⟩ := fsQ_gen4 impl inp seq4 p shOK_seq4 _ h
  rw [fsMsgs4_len] at hl hq
  set fs := (relocFin P.S (finalsOf P)).rest ++ [capF P.S] with hfs
  have hlen : fs.length = 13 := by
    rw [hfs, List.length_append, relocFin_rest, List.length_map, rest_finalsOf_length]; rfl
  have hget : ∀ k (hk : k < 12), fs[k]'(by rw [hlen]; omega) =
      relocF P.S ((finalsOf P).rest[k]'(by rw [rest_finalsOf_length]; exact hk)) := by
    intro k hk
    simp only [hfs]
    rw [List.getElem_append_left (by rw [relocFin_rest, List.length_map, rest_finalsOf_length]; exact hk)]
    simp only [relocFin_rest, List.getElem_map]
  set fin := relocFin P.S (finalsOf P)
  set outs := (skeleton4 seq4 p).2.outs
  set zh := (fin.finRS ⟨outs, [], #[]⟩ (skeleton4 seq4 p).2.next).2
  set B0 := (skeleton4 seq4 p).2.next + opsOut (fin.finRS ⟨outs, [], #[]⟩ (skeleton4 seq4 p).2.next).1
  -- the files' sizes are the fold's bases
  have hsz : ∀ k ≤ 12, (Rs k).size = baseAt outs zh fs B0 #[zh] k := by
    intro k hk
    induction k with
    | zero =>
      rw [(exAt_zero outs zh _ _ _).2, h0]
      have := pureRun_len impl p.tix inp _ _ [] L₀ true h0L
      simp only [Array.size_append, List.size_toArray, this, List.length_nil, Nat.zero_add, B0, hnx]
    | succ k ih =>
      obtain ⟨L, hL, he⟩ := hrest k (by rw [hlen]; omega)
      have hl' := pureRun_len impl p.tix inp _ _ [] L true hL
      have e1 : (Rs (k + 1)).size = (Rs k).size + L.length := by rw [he]; simp
      rw [e1, hl', List.length_nil, Nat.zero_add,
        (exAt_succ outs zh fs B0 #[zh] k (by rw [hlen]; omega)).2, ← ih (by omega)]
  have hzh : ∀ x ∈ zh, x < (Rs 0).size := by
    rw [hsz 0 (by omega), (exAt_zero outs zh _ _ _).2]
    intro x hx
    have := gFinRS_ex_lt P ⟨outs, [], #[]⟩ (skeleton4 seq4 p).2.next x hx
    simpa only [B0, fin, relocFin, relocF, opsOut_reloc, finalsOf] using this
  have hexs : ∀ k ≤ 12, (exAt outs zh fs B0 #[zh] k).size = k + 1 := by
    intro k hk
    induction k with
    | zero => rw [(exAt_zero outs zh _ _ _).1]; rfl
    | succ k ih =>
      rw [(exAt_succ outs zh fs B0 #[zh] k (by rw [hlen]; omega)).1, Array.size_push, ih (by omega)]
  refine ⟨y, ⟨hy, hf, hl, hq⟩, zh, Rs, fun k => exAt outs zh fs B0 #[zh] k, ?_, hzh,
    fun k hk => ⟨hexs k (by omega), ?_⟩⟩
  · intro k hk
    induction k with
    | zero => rw [h0]; exact ExtA.app _ _
    | succ k ih =>
      obtain ⟨L, -, he⟩ := hrest k (by rw [hlen]; omega)
      rw [he]; exact (ih (by omega)).trans (ExtA.app _ _)
  · obtain ⟨L, hL, he⟩ := hrest k (by rw [hlen]; omega)
    have e := hget k hk
    have hs := exAt_succ outs zh fs B0 #[zh] k (by rw [hlen]; omega)
    rw [e] at hL hs
    rw [← hsz k (by omega)] at hs
    exact ⟨L, hL, he, hs.1⟩

/-- **`finE`'s `lrEx` are `finLr`'s exports**: with the fold's exports `Ex 3` before `finLr`
(four of them), `Ex 4`'s entry `exLr` is `finLr`'s output list. -/
theorem lrEx_eq4 {Ex3 : Array (List Reg)} (hs : Ex3.size = 4) (e : List Reg) (fi : FinIn)
    (hfi : fi.ex = Ex3.push e) (j : ℕ) : lrEx fi j = e.getD j 0 := by
  rw [lrEx, hfi, exLr, Array.getD_eq_getD_getElem?, Array.getElem?_push, hs, if_pos rfl, Option.getD_some]

end FR.Snd.R4

end G6_FRSoundness4R4Ex

section G6_FRSoundness4R4Fld

-- New for `flock-recursive` (BLUEPRINT revision 4.1, A.9 the finals; stage R4e).

/-!
# One accepted run, every field: `Fields4`

`fields_ex4` gives each field's run, but its `zhat` registers and register files are existential:
two calls cannot be joined. **`Fields4`** packages one choice of them, together with `finRS`'s run
(its exports are the `zhat` registers, its file `Rs 0`'s prefix), so the checks of several fields
(`finRS`'s `α_j` with `finZ`'s, `finLc`'s, `finSh`'s, `finE`'s bindings) can be read on the same
registers. **`fields4_of_accept`**: an accepted run has one. **`field_run4`**: field `k`'s
relocated run from `Rs k`, flag `true`. Revision 4.4.1: `cap`, the batched cap check's run from
`Rs 12` (after every field), flag `true`.
-/

namespace FR.Snd.R4
open RecursionFast Rev4

/-- **An accepted run's fields**: the skeleton's run `y`, `finRS`'s run from the skeleton's file
(exports `zh`, file `Rs 0`), and field `k` of the rest from `Rs k` with exports `Ex k`. -/
structure Fields4 (impl : OpImpl) (p : KindP) (inp : Input) (tr : Trace) (P : FinP)
    (y : List Val × List Bool × Trace) (zh : List Reg) (Rs : ℕ → Array Val)
    (Ex : ℕ → Array (List Reg)) : Prop where
  sk : SkRun4 impl p inp tr y
  ext : ∀ k ≤ 12, ExtA (#[] ++ y.1.toArray) (Rs k)
  zlt : ∀ x ∈ zh, x < (Rs 0).size
  zh_eq : zh = ((finalsOf P).finRS ⟨(skeleton4 seq4 p).2.outs, [], #[]⟩ (#[] ++ y.1.toArray).size).2
  rs : ∃ L₀ : List Val, pureRun impl p.tix inp
      (((finalsOf P).finRS ⟨(skeleton4 seq4 p).2.outs, [], #[]⟩ (#[] ++ y.1.toArray).size).1.map
        (reloc P.S)) (#[] ++ y.1.toArray) [] = some (L₀, true) ∧
    Rs 0 = (#[] ++ y.1.toArray) ++ L₀.toArray
  fld : ∀ k (hk : k < 12), (Ex k).size = k + 1 ∧ ∃ L : List Val,
    pureRun impl p.tix inp ((((finalsOf P).rest[k]'(by rw [rest_finalsOf_length]; exact hk))
      ⟨(skeleton4 seq4 p).2.outs, zh, Ex k⟩ (Rs k).size).1.map (reloc P.S)) (Rs k) [] = some (L, true) ∧
    Rs (k + 1) = Rs k ++ L.toArray ∧
    Ex (k + 1) = (Ex k).push (((finalsOf P).rest[k]'(by rw [rest_finalsOf_length]; exact hk))
      ⟨(skeleton4 seq4 p).2.outs, zh, Ex k⟩ (Rs k).size).2
  /-- The batched cap check (revision 4.4.1) runs from `Rs 12`, flag `true`. -/
  cap : ∃ L : List Val, pureRun impl p.tix inp
    ((capChkOps P.S (skeleton4 seq4 p).2.outs (Rs 12).size).map (reloc P.S)) (Rs 12) [] = some (L, true)

variable {impl : OpImpl} {p : KindP} {inp : Input}

/-- **An accepted run has its fields** (`fields_ex4` with `finRS`'s run kept). -/
theorem fields4_of_accept (P : FinP) {tr : Trace}
    (h : semIR impl (gen4 seq4 p (finOps4 P)) inp tr = some true) :
    ∃ y zh Rs Ex, Fields4 impl p inp tr P y zh Rs Ex := by
  rw [finOps4_eq] at h
  obtain ⟨y, hy, hf, hnx, L₀, h0L, Rs, h0, hrest⟩ := accept_chain4 impl seq4 p inp _ _ (noAsk_finOps4 P) h
  obtain ⟨hl, hq⟩ := fsQ_gen4 impl inp seq4 p shOK_seq4 _ h
  rw [fsMsgs4_len] at hl hq
  set fs := (relocFin P.S (finalsOf P)).rest ++ [capF P.S] with hfs
  have hlen : fs.length = 13 := by
    rw [hfs, List.length_append, relocFin_rest, List.length_map, rest_finalsOf_length]; rfl
  have hget : ∀ k (hk : k < 12), fs[k]'(by rw [hlen]; omega) =
      relocF P.S ((finalsOf P).rest[k]'(by rw [rest_finalsOf_length]; exact hk)) := by
    intro k hk
    simp only [hfs]
    rw [List.getElem_append_left (by rw [relocFin_rest, List.length_map, rest_finalsOf_length]; exact hk)]
    simp only [relocFin_rest, List.getElem_map]
  have hcap : fs[12]'(by rw [hlen]; omega) = capF P.S := by
    simp only [hfs]
    rw [List.getElem_append_right (by rw [relocFin_rest, List.length_map, rest_finalsOf_length])]
    simp [relocFin_rest, rest_finalsOf_length]
  set fin := relocFin P.S (finalsOf P)
  set outs := (skeleton4 seq4 p).2.outs
  set zh := (fin.finRS ⟨outs, [], #[]⟩ (skeleton4 seq4 p).2.next).2
  set B0 := (skeleton4 seq4 p).2.next + opsOut (fin.finRS ⟨outs, [], #[]⟩ (skeleton4 seq4 p).2.next).1
  have hsz : ∀ k ≤ 12, (Rs k).size = baseAt outs zh fs B0 #[zh] k := by
    intro k hk
    induction k with
    | zero =>
      rw [(exAt_zero outs zh _ _ _).2, h0]
      have := pureRun_len impl p.tix inp _ _ [] L₀ true h0L
      simp only [Array.size_append, List.size_toArray, this, List.length_nil, Nat.zero_add, B0, hnx]
    | succ k ih =>
      obtain ⟨L, hL, he⟩ := hrest k (by rw [hlen]; omega)
      have hl' := pureRun_len impl p.tix inp _ _ [] L true hL
      have e1 : (Rs (k + 1)).size = (Rs k).size + L.length := by rw [he]; simp
      rw [e1, hl', List.length_nil, Nat.zero_add,
        (exAt_succ outs zh fs B0 #[zh] k (by rw [hlen]; omega)).2, ← ih (by omega)]
  have hzh : ∀ x ∈ zh, x < (Rs 0).size := by
    rw [hsz 0 (by omega), (exAt_zero outs zh _ _ _).2]
    intro x hx
    have := gFinRS_ex_lt P ⟨outs, [], #[]⟩ (skeleton4 seq4 p).2.next x hx
    simpa only [B0, fin, relocFin, relocF, opsOut_reloc, finalsOf] using this
  have hexs : ∀ k ≤ 12, (exAt outs zh fs B0 #[zh] k).size = k + 1 := by
    intro k hk
    induction k with
    | zero => rw [(exAt_zero outs zh _ _ _).1]; rfl
    | succ k ih =>
      rw [(exAt_succ outs zh fs B0 #[zh] k (by rw [hlen]; omega)).1, Array.size_push, ih (by omega)]
  refine ⟨y, zh, Rs, fun k => exAt outs zh fs B0 #[zh] k, ⟨⟨hy, hf, hl, hq⟩, ?_, hzh,
    by rw [← hnx]; rfl, ⟨L₀, by rw [← hnx]; exact h0L, h0⟩, fun k hk => ⟨hexs k (by omega), ?_⟩, ?_⟩⟩
  · intro k hk
    induction k with
    | zero => rw [h0]; exact ExtA.app _ _
    | succ k ih =>
      obtain ⟨L, -, he⟩ := hrest k (by rw [hlen]; omega)
      rw [he]; exact (ih (by omega)).trans (ExtA.app _ _)
  · obtain ⟨L, hL, he⟩ := hrest k (by rw [hlen]; omega)
    have e := hget k hk
    have hs := exAt_succ outs zh fs B0 #[zh] k (by rw [hlen]; omega)
    rw [e] at hL hs
    rw [← hsz k (by omega)] at hs
    exact ⟨L, hL, he, hs.1⟩
  · obtain ⟨L, hL, -⟩ := hrest 12 (by rw [hlen]; omega)
    rw [hcap] at hL
    exact ⟨L, hL⟩

section F
variable {tr : Trace} {P : FinP} {y : List Val × List Bool × Trace} {zh : List Reg}
  {Rs : ℕ → Array Val} {Ex : ℕ → Array (List Reg)} (hF : Fields4 impl p inp tr P y zh Rs Ex)
include hF

/-- The files extend each other. -/
theorem Fields4.chain {j k : ℕ} (hjk : j ≤ k) (hk : k ≤ 12) : ExtA (Rs j) (Rs k) := by
  have hch : ∀ k < 12, ExtA (Rs k) (Rs (k + 1)) := fun k hk => by
    obtain ⟨-, L, -, he, -⟩ := hF.fld k hk; rw [he]; exact ExtA.app _ _
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hjk
  induction d with
  | zero => exact ⟨le_rfl, fun _ _ => rfl⟩
  | succ d ih => exact (ih (by omega) (by omega)).trans (hch _ (by omega))

/-- The `zhat` registers lie in every file. -/
theorem Fields4.zlt' {k : ℕ} (hk : k ≤ 12) : ∀ x ∈ zh, x < (Rs k).size :=
  fun x hx => Nat.lt_of_lt_of_le (hF.zlt x hx) (hF.chain (Nat.zero_le k) hk).1

/-- A named register of field `k`'s input lies in its file. -/
theorem Fields4.sk_lt {k : ℕ} (hk : k ≤ 12) (ex : Array (List Reg)) :
    ∀ name, ∀ x ∈ outsOf ⟨(skeleton4 seq4 p).2.outs, zh, ex⟩ name, x < (Rs k).size :=
  fun name x hx => Nat.lt_of_lt_of_le (outsOf_lt4 (p := p) hF.sk zh ex name x hx) (hF.ext k hk).1

theorem Fields4.pos {k : ℕ} (hk : k ≤ 12) : 0 < (Rs k).size :=
  lt_of_lt_of_le (skel_pos4 hF.sk) (hF.ext k hk).1

end F

end FR.Snd.R4

end G6_FRSoundness4R4Fld

section G6_FRSoundness4R4View

-- New for `flock-recursive` (BLUEPRINT revision 4.1, A.9, A.10; stage R4).

/-!
# Register views of an accepted `gen4` run: squeezes (coordinates, one challenge)

On an accepted run (`SkRun4`), a squeeze phase `n` of `phasesOf seq4` leaves its challenges in the
skeleton's registers, read off the run's Fiat–Shamir entries from `phStart4 n`:

* **`sqz_entries4`**: the phase's answers are the entries' answers (`ansAt`) from `phStart4 n`;
* **`coords_view4`** (`.squeezes k .coords`): `outs[n] = (b + 3k) :: (b + 3⌊x/2⌋ + 1 + x mod 2)_x`,
  register `b + 3⌊x/2⌋ + 1 + x mod 2` holding `chF (ansAt es (phStart4 n + ⌊x/2⌋)) (x mod 2)`;
* **`one_view4`** (`.squeezes 1 .one`): the one out register holds `fAt es (phStart4 n) 0`.
-/

namespace FR.Snd.R4
open RecursionFast Rev4

variable {impl : OpImpl} {p : KindP} {inp : Input}

theorem rd_phase4 {M X : List Val} {R : Array Val} (hext : ExtA (#[] ++ (M ++ X).toArray) R)
    {m : ℕ} (hm : m < X.length) : rd R (M.length + m) = X.getD m default := by
  have hlt : M.length + m < (#[] ++ (M ++ X).toArray).size := by simp; omega
  rw [hext.2 _ hlt, show (#[] : Array Val) ++ (M ++ X).toArray = (#[] ++ M.toArray) ++ X.toArray
    by simp, show M.length = (#[] ++ M.toArray).size by simp, rd_app]

/-- A squeeze phase's answers are the chain's entries from `phStart4 n`. -/
theorem sqz_entries4 {tr trk : Trace} {n k : ℕ} (hn : n < (phasesOf seq4).length) {ch : ChalK}
    (hsh : (phasesOf seq4)[n].2 = .squeezes k ch) (hk : 0 < k) {d : Digest}
    {xs : List Digest × Trace} (hsq : sqzT k d trk = some xs)
    (hdrop : (fsOf tr (itemsOf seq4)).drop (phStart4 n) = fsOf trk (psItems4 seq4 ((phasesOf seq4).drop n))) :
    xs.1.length = k ∧ ∀ l < k, xs.1.getD l zeroD = ansAt (fsOf tr (itemsOf seq4)) (phStart4 n + l) := by
  obtain ⟨seg, hseg, hsl, -, hmap⟩ := sqzT_chain ⟨zeroD, zeroD, ByteArray.empty⟩ hsq 0
  have hit : (phasesOf seq4)[n].2.itemsL seq4.lv = List.replicate k .squeeze := by rw [hsh]; rfl
  rw [List.drop_eq_getElem_cons hn, psItems4, List.flatMap_cons, hit] at hdrop
  obtain ⟨-, hent⟩ := seg_entries hdrop hseg (by simpa using hsl) (replicate_sq_fs k) (by simpa using hk)
  rw [List.length_replicate] at hent
  refine ⟨by rw [← hmap, List.length_map, hsl], fun l hl => ?_⟩
  rw [← hmap, List.getD_eq_getElem _ _ (by simp [hsl, hl]), List.getElem_map, ansAt, entAt,
    ← hent l hl, hseg, List.getD_eq_getElem _ _ (by simp [hsl]; omega),
    List.getElem_append_left (by omega)]

/-- **A coordinates phase on the skeleton's registers.** -/
theorem coords_view4 {tr : Trace} {y : List Val × List Bool × Trace} (h : SkRun4 impl p inp tr y)
    {n : ℕ} (hn : n < (phasesOf seq4).length) {k : ℕ}
    (hsh : (phasesOf seq4)[n].2 = .squeezes k .coords) (hk : 0 < k) :
    ∃ b, (skeleton4 seq4 p).2.outs.getD n [] = (b + 3 * k) ::
        (List.range (2 * k)).map (fun x => b + 3 * (x / 2) + 1 + x % 2) ∧
      b + 3 * k + 1 ≤ (#[] ++ y.1.toArray).size ∧
      ∀ x < 2 * k, rd (#[] ++ y.1.toArray) (b + 3 * (x / 2) + 1 + x % 2) =
        .f (chF (ansAt (fsOf tr (itemsOf seq4)) (phStart4 n + x / 2)) (x % 2)) := by
  obtain ⟨trk, M, x, hx, hb, -, hext, -, hdrop, -⟩ := phase_at4 impl p.tix inp p h.ref hn
  generalize hph : (phasesOf seq4)[n] = ph at hx hsh
  obtain ⟨name, sh⟩ := ph
  simp only at hsh; subst hsh
  simp only [refPhase4] at hx
  obtain ⟨xs, hxs, rfl⟩ := Option.map_eq_some_iff.1 hx
  obtain ⟨hl, hans⟩ := sqz_entries4 hn (by rw [hph]) hk hxs hdrop
  dsimp only at hext
  have hsz := hext.1
  simp only [Array.size_append, List.size_toArray, List.length_append, coordVals_length, hl,
    List.length_singleton, List.size_toArray] at hsz
  refine ⟨M.length, ?_, by simp only [Array.size_append, List.size_toArray] at hsz ⊢; omega,
    fun v hv => ?_⟩
  · rw [skeleton4_outs seq4 p hn, hph]; simp [genPhase4, hb]
  · have h3 : 3 * (v / 2) + (1 + v % 2) < (xs.1.flatMap coordVals).length := by
      rw [coordVals_length, hl]; omega
    rw [show M.length + 3 * (v / 2) + 1 + v % 2 = M.length + (3 * (v / 2) + (1 + v % 2)) by ring,
      rd_phase4 hext (by simp only [List.length_append]; omega),
      List.getD_append _ _ _ _ h3, flatMap_coord_getD _ _ _ (by omega) (by omega), hans _ (by omega)]
    rcases Nat.mod_two_eq_zero_or_one v with h0 | h1
    · rw [h0]; rfl
    · rw [h1]; rfl

/-- **A one-challenge squeeze on the skeleton's registers** (`L1`, `L3β`, `Lr3`, `E3`, `B′`): its
one out register holds `fAt es (phStart4 n) 0`. -/
theorem one_view4 {tr : Trace} {y : List Val × List Bool × Trace} (h : SkRun4 impl p inp tr y)
    {n : ℕ} (hn : n < (phasesOf seq4).length) (hsh : (phasesOf seq4)[n].2 = .squeezes 1 .one) :
    ∃ b, (skeleton4 seq4 p).2.outs.getD n [] = [b] ∧ b < (#[] ++ y.1.toArray).size ∧
      rd (#[] ++ y.1.toArray) b = .f (fAt (fsOf tr (itemsOf seq4)) (phStart4 n) 0) := by
  obtain ⟨trk, M, x, hx, hb, -, hext, -, hdrop, -⟩ := phase_at4 impl p.tix inp p h.ref hn
  generalize hph : (phasesOf seq4)[n] = ph at hx hsh
  obtain ⟨name, sh⟩ := ph
  simp only at hsh; subst hsh
  simp only [refPhase4] at hx
  obtain ⟨xs, hxs, rfl⟩ := Option.map_eq_some_iff.1 hx
  obtain ⟨hl, hans⟩ := sqz_entries4 hn (by rw [hph]) (by norm_num) hxs hdrop
  dsimp only at hext
  have hsz := hext.1
  simp only [Array.size_append, List.size_toArray, List.length_append, List.length_map, hl,
    List.length_singleton] at hsz
  refine ⟨M.length + 1, ?_, by dsimp only [Reg]; simp at hsz ⊢; omega, ?_⟩
  · rw [skeleton4_outs seq4 p hn, hph]; simp [genPhase4, hb]
  · rw [rd_phase4 hext (by simp [hl]), List.getD_append_right _ _ _ _ (by simp [hl]),
      List.length_map, hl, Nat.sub_self, List.getD_cons_zero, fAt]
    obtain ⟨a, ha⟩ : ∃ a, xs.1 = [a] := List.length_eq_one_iff.1 hl
    have h0 := hans 0 (by norm_num)
    rw [ha, Nat.add_zero, List.getD_cons_zero] at h0
    rw [ha, List.headD_cons, h0]

end FR.Snd.R4

end G6_FRSoundness4R4View

section G6_FRSoundness4R4Rnd

-- New for `flock-recursive` (BLUEPRINT revision 4.1, A.4, A.9; stage R4b).
-- RET-2: import re-pointed at Core: `FRSoundnessFrRndV` → `FRSoundnessCoreAcc`.

/-!
# The F rounds of an accepted `gen4` run, on the log (real round counts, every init)

A rounds phase `n` of `phasesOf seq4` (`.rounds f k deg false`, `deg ∈ {2, 3}`) runs `k` slots of
which the first `realRounds p name k` are real; a dummy round keeps the claim. On the log the
phase's entries sit at `P = phStart4 n` (`rounds_at4`), and the program's registers are the log's
running claims (no message table is needed: a round's query is `absorbQ d msg`, so the log's
`msgAt` *is* the program's message, `msgAt_of_q`):

* **`rounds3_log`** (degree 3): the claim after the run is `clR P c₀ … (min real (j + n))`;
* **`rounds2_log`** (degree 2): the claim after the run is `clR2 P … (min real (j + n))`, and every
  real round's check `Chk2 P …` holds (the program's `c₁ + c₂ = claim` assert);
* **`roundsF3_view4`**, **`roundsF2_view4`**: on the skeleton's registers. `outs[n]` is
  `cl :: rs ++ [last]` (`genPhase4_roundsF`), `cl` holds the initial claim (`.free`: round 0's
  `c₁ + c₂`; `.zero`: `0`; `.uni`: Z2's register, a hypothesis), `rs[j]` round `j`'s challenge
  `rch P es j`, `last` the claim after the real rounds.
-/

namespace FR.Snd.R4
open RecursionFast Rev4 FR.Impl

/-! ## The log's messages are the program's -/

theorem getLastD_append' (l l' : List α) (a : α) : (l ++ l').getLastD a = l'.getLastD (l.getLastD a) := by
  simp only [List.getLastD_eq_getLast?, List.getLast?_append]
  cases l'.getLast? <;> rfl

/-- A logged absorb's message is the absorbed bytes. -/
theorem msgAt_of_q {es : Log} {p : ℕ} {d : Digest} {m : ByteArray}
    (h : (es.getD p default).1 = absorbQ d m) : Snd.msgAt es p = m := by
  unfold Snd.msgAt entAt; rw [h]; exact extract40_absorbQ _ _

theorem readF_piMsg (inp : Input) (o off : ℕ) {len : ℕ} (h : off + 16 ≤ len) :
    readF (FR.msgAt inp 0 o len) off = elemAt inp 0 (o + off) := by
  simp only [readF, FR.msgAt, elemAt, absOff_zero]
  rw [bytesAt_extract_of_le16 _ h]

/-! ## Dummy rounds keep the claim -/

theorem getLastD_of_ne {l : List α} (h : l ≠ []) (a b : α) : l.getLastD a = l.getLastD b := by
  rw [List.getLastD_eq_getLast?, List.getLastD_eq_getLast?, List.getLast?_eq_getLast h]; rfl

theorem roundsT_dummy (inp : Input) (o deg real : ℕ) :
    ∀ (n j : ℕ) (d : Digest) (cv : Val) (tr : Trace) (x : List Val × Bool × Trace),
      roundsT inp 0 o deg false real n j d cv tr = some x → real ≤ j → x.1.getLastD cv = cv
  | 0, _, _, _, _, x, h, _ => by
    simp only [roundsT, Option.some.injEq] at h; subst h; rfl
  | n + 1, j, d, cv, (q₁, a₁) :: (q₂, a₂) :: tr, x, h, hj => by
    simp only [roundsT, Bool.false_eq_true, ite_false] at h
    have hre : decide (j < real) = false := decide_eq_false (by omega)
    split_ifs at h with hq hd <;>
    · obtain ⟨x', hx', rfl⟩ := Option.map_eq_some_iff.mp h
      have ih := roundsT_dummy inp o deg real n (j + 1) a₂ _ tr x' hx' (by omega)
      rw [getLastD_append']
      simp only [hre, round3V, round2Vals, Bool.false_eq_true, ite_false, List.getLastD_eq_getLast?,
        List.getLast?_cons_cons, List.getLast?_singleton, Option.getD_some] at ih ⊢
      exact ih
  | _ + 1, _, _, _, [], _, h, _ => by simp [roundsT] at h
  | _ + 1, _, _, _, [_], _, h, _ => by simp [roundsT] at h

/-! ## Real rounds on the log -/

/-- A round's two entries on the log: its message is π's, its challenge the answer's. -/
theorem round_entries {inp : Input} {o P j : ℕ} {es : Log} {q₁ q₂ : ByteArray} {a₁ a₂ d : Digest}
    {tr : Trace} (hq : q₁ = absorbQ d (FR.msgAt inp 0 (o + j * roundBytes false) (roundBytes false)))
    (he : ∀ m < 2, ((q₁, a₁) :: (q₂, a₂) :: tr).getD m default = es.getD (P + 2 * j + m) default) :
    (∀ off, off + 16 ≤ 48 → readF (Snd.msgAt es (P + 2 * j)) off = elemAt inp 0 (o + j * 48 + off)) ∧
      ansAt es (P + 2 * j + 1) = a₂ := by
  have e0 := he 0 (by norm_num); have e1 := he 1 (by norm_num)
  simp only [List.getD_cons_zero, List.getD_cons_succ, Nat.add_zero] at e0 e1
  refine ⟨fun off hoff => ?_, by rw [ansAt, entAt, ← e1]⟩
  rw [msgAt_of_q (p := P + 2 * j) (by rw [← e0]; exact hq)]
  exact readF_piMsg inp _ off hoff

theorem shift_entries {es : Log} {P j n : ℕ} {e₁ e₂ : ByteArray × Digest} {tr : Trace}
    (he : ∀ m < 2 * (n + 1), (e₁ :: e₂ :: tr).getD m default = es.getD (P + 2 * j + m) default) :
    ∀ m < 2 * n, tr.getD m default = es.getD (P + 2 * (j + 1) + m) default := fun m hm => by
  have := he (m + 2) (by omega)
  rw [List.getD_cons_succ, List.getD_cons_succ] at this
  rw [this]; congr 1; ring

/-- **Degree-3 F rounds on the log**: from claim `clR P c₀ … j` at round `j ≤ real`, the claim
after `n` rounds is `clR P c₀ … (min real (j + n))` (dummies keep it). -/
theorem rounds3_log (inp : Input) (o real P : ℕ) (es : Log) (c0 : Log → Log → F) (L : Log) :
    ∀ (n j : ℕ) (d : Digest) (cv : Val) (tr : Trace) (x : List Val × Bool × Trace),
      roundsT inp 0 o 3 false real n j d cv tr = some x →
      (∀ m < 2 * n, tr.getD m default = es.getD (P + 2 * j + m) default) →
      j ≤ real → cv = .f (clR P c0 L es j) →
      x.1.getLastD cv = .f (clR P c0 L es (min real (j + n)))
  | 0, j, _, cv, _, x, h, _, hj, hc => by
    simp only [roundsT, Option.some.injEq] at h; subst h
    rw [Nat.add_zero, Nat.min_eq_right hj]; exact hc
  | n + 1, j, d, cv, (q₁, a₁) :: (q₂, a₂) :: tr, x, h, he, hj, hc => by
    simp only [roundsT, Bool.false_eq_true, ite_false, ite_true] at h
    split_ifs at h with hq
    obtain ⟨x', hx', rfl⟩ := Option.map_eq_some_iff.mp h
    obtain ⟨hm, ha⟩ := round_entries hq.1 (fun m hm => he m (by omega))
    have hne : round3V inp 0 (o + j * roundBytes false) (decide (j < real)) a₁ a₂ cv ≠ [] := by
      simp [round3V]
    rw [getLastD_append', getLastD_of_ne hne cv default]
    rcases Nat.lt_or_ge j real with hjr | hjr
    · have hg : (round3V inp 0 (o + j * roundBytes false) (decide (j < real)) a₁ a₂ cv).getLastD
          default = .f (clR P c0 L es (j + 1)) := by
        simp only [round3V, decide_eq_true hjr, ite_true, List.getLastD_eq_getLast?,
          List.getLast?_cons_cons, List.getLast?_singleton, Option.getD_some, clR, g3At, rch, fAt, ha,
          peval_four, hc, Val.toF, roundBytes, Bool.false_eq_true, ite_false]
        rw [hm 0 (by norm_num), hm 16 (by norm_num), hm 32 (by norm_num), Nat.add_zero]; rfl
      rw [hg, rounds3_log inp o real P es c0 L n (j + 1) a₂ _ tr x' (hg ▸ hx') (shift_entries he)
        (by omega) rfl, show j + 1 + n = j + (n + 1) by omega]
    · have hjr' : j = real := by omega
      have hk : (round3V inp 0 (o + j * roundBytes false) (decide (j < real)) a₁ a₂ cv).getLastD
          default = cv := by
        simp [round3V, show ¬ j < real by omega]
      rw [hk, roundsT_dummy inp o 3 real n (j + 1) a₂ cv tr x' (hk ▸ hx') (by omega), hc, hjr',
        Nat.min_eq_left (by omega)]
  | _ + 1, _, _, _, [], _, h, _, _, _ => by simp [roundsT] at h
  | _ + 1, _, _, _, [_], _, h, _, _, _ => by simp [roundsT] at h

/-- **Degree-2 F rounds on the log**: from claim `clR2 P … j` at round `j ≤ real`, the claim
after `n` rounds is `clR2 P … (min real (j + n))`; on a passing run every real round's check holds. -/
theorem rounds2_log (inp : Input) (o real P : ℕ) (es : Log) (c0 : Log → Log → F) (L : Log) :
    ∀ (n j : ℕ) (d : Digest) (cv : Val) (tr : Trace) (x : List Val × Bool × Trace),
      roundsT inp 0 o 2 false real n j d cv tr = some x →
      (∀ m < 2 * n, tr.getD m default = es.getD (P + 2 * j + m) default) →
      j ≤ real → cv = .f (clR2 P 16 readF (fun d => chF d 0) c0 L es j) →
      x.1.getLastD cv = .f (clR2 P 16 readF (fun d => chF d 0) c0 L es (min real (j + n))) ∧
        (x.2.1 = true → ∀ l < n, j + l < real → Chk2 P 16 readF (fun d => chF d 0) c0 L es (j + l))
  | 0, j, _, cv, _, x, h, _, hj, hc => by
    simp only [roundsT, Option.some.injEq] at h; subst h
    exact ⟨by rw [Nat.add_zero, Nat.min_eq_right hj]; exact hc, fun _ l hl => absurd hl (by omega)⟩
  | n + 1, j, d, cv, (q₁, a₁) :: (q₂, a₂) :: tr, x, h, he, hj, hc => by
    simp only [roundsT, Bool.false_eq_true, ite_false, show (2 = 3) = False by decide] at h
    split_ifs at h with hq
    obtain ⟨x', hx', rfl⟩ := Option.map_eq_some_iff.mp h
    obtain ⟨hm, ha⟩ := round_entries hq.1 (fun m hm => he m (by omega))
    have hne : round2Vals inp 0 (o + j * roundBytes false) (decide (j < real)) a₁ a₂ cv ≠ [] := by
      simp [round2Vals]
    rcases Nat.lt_or_ge j real with hjr | hjr
    · have hg : (round2Vals inp 0 (o + j * roundBytes false) (decide (j < real)) a₁ a₂ cv).getLastD
          default = .f (clR2 P 16 readF (fun d => chF d 0) c0 L es (j + 1)) := by
        simp only [round2Vals, decide_eq_true hjr, ite_true, List.getLastD_eq_getLast?,
          List.getLast?_cons_cons, List.getLast?_singleton, Option.getD_some, clR2, g2At, rch2, ha,
          peval_three, g2, roundBytes, Bool.false_eq_true, ite_false]
        rw [hm 0 (by norm_num), hm 16 (by norm_num), show 2 * 16 = 32 by norm_num,
          hm 32 (by norm_num), Nat.add_zero]
        exact congrArg Val.f (by ring)
      obtain ⟨ih1, ih2⟩ := rounds2_log inp o real P es c0 L n (j + 1) a₂ _ tr x' (hg ▸ hx')
        (shift_entries he) (by omega) rfl
      refine ⟨?_, fun hx l hl hjl => ?_⟩
      · rw [getLastD_append', getLastD_of_ne hne cv default, hg, ih1,
          show j + 1 + n = j + (n + 1) by omega]
      · simp only [decide_eq_true hjr, Bool.not_true, Bool.false_or, Bool.true_or, Bool.and_true,
          Bool.and_eq_true] at hx
        rcases l with _ | l
        · have h0 := hx.1
          simp only [roundBytes, Bool.false_eq_true, ite_false, hc, eqv_f] at h0
          rw [Nat.add_zero, Chk2, g2At, charTwo_peval01F, hm 16 (by norm_num),
            show 2 * 16 = 32 by norm_num, hm 32 (by norm_num)]
          exact h0
        · rw [show j + (l + 1) = j + 1 + l by omega]
          exact ih2 hx.2 l (by omega) (by omega)
    · have hjr' : j = real := by omega
      have hk : (round2Vals inp 0 (o + j * roundBytes false) (decide (j < real)) a₁ a₂ cv).getLastD
          default = cv := by
        simp [round2Vals, show ¬ j < real by omega]
      refine ⟨?_, fun _ l _ hjl => absurd hjl (by omega)⟩
      rw [getLastD_append', getLastD_of_ne hne cv default, hk,
        roundsT_dummy inp o 2 real n (j + 1) a₂ cv tr x' (hk ▸ hx') (by omega), hc, hjr',
        Nat.min_eq_left (by omega)]
  | _ + 1, _, _, _, [], _, h, _, _, _ => by simp [roundsT] at h
  | _ + 1, _, _, _, [_], _, h, _, _, _ => by simp [roundsT] at h

/-! ## A rounds phase of the accepted skeleton -/

theorem rounds_itemsL_length (lv : ℕ → Level) (f k deg : ℕ) (inK : Bool) :
    ((Sh.rounds f k deg inK).itemsL lv).length = 2 * k := by
  simp [Sh.itemsL, Nat.mul_comm]

/-- The claim register's value a rounds phase starts from (`refPhase4`'s `cl`). -/
def clVal (inp : Input) (init : Init) (o : ℕ) (r : Array Val) (u : Reg) : Val :=
  match init with
  | .uni => rd r u
  | _ => (initVals inp init 0 o false).getLastD default

variable {impl : OpImpl} {p : KindP} {inp : Input}

/-- **A rounds phase of an accepted run** (`.rounds f k deg false`): before it the registers are
`#[] ++ M`; its `k` slots run `roundsT` with `realRounds p name k` real rounds from the claim
`clVal …`; its values `initVals ++ xr.1` extend into the run's registers; its `2k` entries are the
log's from `phStart4 n`. -/
theorem rounds_at4 {tr : Trace} {y : List Val × List Bool × Trace} (h : SkRun4 impl p inp tr y)
    {n : ℕ} (hn : n < (phasesOf seq4).length) {f k deg : ℕ}
    (hsh : (phasesOf seq4)[n].2 = .rounds f k deg false) :
    ∃ (M : List Val) (xr : List Val × Bool × Trace) (trk : Trace),
      (cAt4 seq4 p n).next = M.length ∧ CtxOk (cAt4 seq4 p n) (#[] ++ M.toArray) ∧
      roundsT inp 0 (fieldOffOf seq4 f + phaseOffOf seq4 n f) deg false
        (realRounds p (phasesOf seq4)[n].1 k) k 0 (rd (#[] ++ M.toArray) (cAt4 seq4 p n).st).toD
        (clVal inp (initClaim (phasesOf seq4)[n].1) (fieldOffOf seq4 f + phaseOffOf seq4 n f)
          (#[] ++ M.toArray) (cAt4 seq4 p n).uni) trk = some xr ∧
      ExtA (#[] ++ (M ++ (initVals inp (initClaim (phasesOf seq4)[n].1) 0
        (fieldOffOf seq4 f + phaseOffOf seq4 n f) false ++ xr.1)).toArray) (#[] ++ y.1.toArray) ∧
      xr.2.1 = true ∧
      ∀ m < 2 * k, trk.getD m default = (fsOf tr (itemsOf seq4)).getD (phStart4 n + m) default := by
  obtain ⟨trk, M, x, hx, hb, hwf, hext, hflag, hdrop, -⟩ := phase_at4 impl p.tix inp p h.ref hn
  have hok : CtxOk (cAt4 seq4 p n) (#[] ++ M.toArray) := by
    rcases hwf with ⟨h', -⟩ | h'
    · rw [hsh] at h'; cases h'
    · exact h'
  obtain ⟨seg, hseg, hsl, -⟩ := refPhase4_chain impl p.tix inp seq4 p hx (by simpa using hb)
    (by rw [hsh]; rfl) (q0 := 1) (by simp [hsh, isSeed4]) (.inr hok.1)
  generalize hph : (phasesOf seq4)[n] = ph at hx hsh hsl
  obtain ⟨name, sh⟩ := ph
  simp only at hsh; subst hsh
  simp only [refPhase4] at hx
  obtain ⟨xr, hxr, rfl⟩ := Option.map_eq_some_iff.1 hx
  refine ⟨M, xr, trk, hb, hok, ?_, hext, h.flags _ hflag, fun m hm => ?_⟩
  · convert hxr using 2; simp only [clVal]; generalize initClaim name = ic; cases ic <;> rfl
  · have hit : (phasesOf seq4)[n].2.itemsL seq4.lv = (Sh.rounds f k deg false).itemsL seq4.lv := by
      rw [hph]
    rw [List.drop_eq_getElem_cons hn, psItems4, List.flatMap_cons, hit] at hdrop
    rw [rounds_itemsL_length] at hsl
    obtain ⟨-, hent⟩ := seg_entries hdrop hseg (by rw [hsl, rounds_itemsL_length])
      (itemsL_allFS _ (by simp)) (by rw [rounds_itemsL_length]; omega)
    exact hent m (by rw [rounds_itemsL_length]; exact hm)

theorem lt_reg {a b : ℕ} (h : a < b) : (a : Reg) < b := h

/-- The register of a rounds phase's first claim (`initOps`' second component). -/
def clReg (init : Init) (u b : Reg) : Reg :=
  match init with
  | .uni => u
  | .zero => b
  | .free => b + 2

/-- **A rounds phase's out list** (`genPhase4`): the first claim, the `k` challenges, the last claim. -/
theorem genPhase4_rounds (S : Seq) (p : KindP) (n : ℕ) (name : String) (f k deg : ℕ) (c : GCtx) :
    (genPhase4 S p n (name, .rounds f k deg false) c).2.outs.back?.getD [] =
      clReg (initClaim name) c.uni c.next ::
        (List.range k).map (fun j => c.next + (initClaim name).width + roundW deg * j + 3) ++
        [if k = 0 then clReg (initClaim name) c.uni c.next
          else c.next + (initClaim name).width + roundW deg * k - 1] := by
  simp only [genPhase4]
  generalize initClaim name = ic
  cases ic <;> simp [initOps, Init.width, clReg]

/-- **A rounds phase on the skeleton's registers** (any degree, any init): `outs[n]` is
`cl :: rs ++ [last]`; `cl` holds `clVal` (the claim the rounds start from), `rs[j]` round `j`'s
challenge `rch P es j`; the rounds' run `xr` passes, reads the log from `P`, and `last` holds its
last claim. -/
theorem rounds_core4 {tr : Trace} {y : List Val × List Bool × Trace} (h : SkRun4 impl p inp tr y)
    {n : ℕ} (hn : n < (phasesOf seq4).length) {f k deg : ℕ}
    (hsh : (phasesOf seq4)[n].2 = .rounds f k deg false) :
    ∃ b : ℕ, (skeleton4 seq4 p).2.outs.getD n [] =
        clReg (initClaim (phasesOf seq4)[n].1) (cAt4 seq4 p n).uni b ::
          (List.range k).map (fun j => b + (initClaim (phasesOf seq4)[n].1).width + roundW deg * j + 3) ++
          [if k = 0 then clReg (initClaim (phasesOf seq4)[n].1) (cAt4 seq4 p n).uni b
            else b + (initClaim (phasesOf seq4)[n].1).width + roundW deg * k - 1] ∧
      b + (initClaim (phasesOf seq4)[n].1).width + roundW deg * k ≤ (#[] ++ y.1.toArray).size ∧
      clReg (initClaim (phasesOf seq4)[n].1) (cAt4 seq4 p n).uni b < (#[] ++ y.1.toArray).size ∧
      rd (#[] ++ y.1.toArray) (clReg (initClaim (phasesOf seq4)[n].1) (cAt4 seq4 p n).uni b) =
        clVal inp (initClaim (phasesOf seq4)[n].1) (fieldOffOf seq4 f + phaseOffOf seq4 n f)
          (#[] ++ y.1.toArray) (cAt4 seq4 p n).uni ∧
      (∀ j < k, rd (#[] ++ y.1.toArray) (b + (initClaim (phasesOf seq4)[n].1).width + roundW deg * j + 3) =
        .f (rch (phStart4 n) (fsOf tr (itemsOf seq4)) j)) ∧
      ∃ (xr : List Val × Bool × Trace) (d : Digest) (trk : Trace),
        roundsT inp 0 (fieldOffOf seq4 f + phaseOffOf seq4 n f) deg false
          (realRounds p (phasesOf seq4)[n].1 k) k 0 d
          (clVal inp (initClaim (phasesOf seq4)[n].1) (fieldOffOf seq4 f + phaseOffOf seq4 n f)
            (#[] ++ y.1.toArray) (cAt4 seq4 p n).uni) trk = some xr ∧ xr.2.1 = true ∧
        (∀ m < 2 * k, trk.getD m default = (fsOf tr (itemsOf seq4)).getD (phStart4 n + 2 * 0 + m) default) ∧
        (0 < k → rd (#[] ++ y.1.toArray) (b + (initClaim (phasesOf seq4)[n].1).width + roundW deg * k - 1) =
          xr.1.getLastD (clVal inp (initClaim (phasesOf seq4)[n].1)
            (fieldOffOf seq4 f + phaseOffOf seq4 n f) (#[] ++ y.1.toArray) (cAt4 seq4 p n).uni)) := by
  obtain ⟨M, xr, trk, hb, hok, hxr, hext, hfl, hent⟩ := rounds_at4 h hn hsh
  have hout := skeleton4_outs seq4 p hn
  generalize hph : (phasesOf seq4)[n] = ph at hsh hxr hext hout ⊢
  obtain ⟨name, sh⟩ := ph
  simp only at hsh; subst hsh
  simp only at hxr hext ⊢
  rw [genPhase4_rounds, hb] at hout
  have huM : (cAt4 seq4 p n).uni < M.length := by simpa using hok.2.1
  generalize fieldOffOf seq4 f + phaseOffOf seq4 n f = o at hxr hext ⊢
  generalize hR0 : #[] ++ y.1.toArray = R0 at hext ⊢
  obtain ⟨u, hu'⟩ : ∃ u : ℕ, (cAt4 seq4 p n).uni = u := ⟨_, rfl⟩
  rw [hu'] at hxr hout huM ⊢
  replace huM : u < M.length := huM
  obtain ⟨hv1, hv2⟩ := roundsT_chalF inp 0 o deg _ k 0 _ _ trk xr hxr
  have hiv := initValsF_length (inp := inp) (initClaim name) 0 o
  have hsz := size_le_of_ext hext
  simp only [List.length_append, hiv, hv1] at hsz
  have hrd : ∀ m < (initClaim name).width + roundW deg * k,
      rd R0 (M.length + m) = (initVals inp (initClaim name) 0 o false ++ xr.1).getD m default :=
    fun m hm => rd_phase4 hext (by simp [hiv, hv1]; omega)
  have hu : rd (#[] ++ M.toArray) u = rd R0 u := by
    have hlt : u < (#[] ++ (M ++ (initVals inp (initClaim name) 0 o false ++ xr.1)).toArray).size := by
      simp only [Array.size_append, List.size_toArray, List.length_append, Array.size_empty, List.length_nil]; omega
    rw [hext.2 _ hlt, show (#[] : Array Val) ++ (M ++ (initVals inp (initClaim name) 0 o false ++
      xr.1)).toArray = (#[] ++ M.toArray) ++ (initVals inp (initClaim name) 0 o false ++ xr.1).toArray
      by simp, rd_app_left (#[] ++ M.toArray) _ (by simpa using huM)]
  have hcv : clVal inp (initClaim name) o (#[] ++ M.toArray) u = clVal inp (initClaim name) o R0 u := by
    simp only [clVal]; generalize initClaim name = ic; cases ic
    exacts [hu, rfl, rfl]
  rw [hcv] at hxr
  have hw : 4 ≤ roundW deg := by unfold roundW; split <;> omega
  refine ⟨M.length, hout, by omega, ?_, ?_, fun j hj => ?_, xr, _, trk, hxr, hfl,
    fun m hm => by simpa using hent m hm, fun hk => ?_⟩
  · simp only [clReg]; generalize hic : initClaim name = ic at hsz ⊢
    cases ic <;> simp only [Init.width] at hsz ⊢ <;> dsimp only [Reg] <;> omega
  · simp only [clReg, clVal]
    generalize hic : initClaim name = ic at hrd hiv
    cases ic
    · rfl
    · rw [show M.length = M.length + 0 from rfl, hrd 0 (by simp [Init.width] <;> omega)]; rfl
    · rw [hrd 2 (by simp [Init.width] <;> omega)]; rfl
  · have hlt : roundW deg * j + 3 < xr.1.length := by
      rw [hv1]
      have : roundW deg * j + roundW deg ≤ roundW deg * k := by
        rw [← Nat.mul_succ]; exact Nat.mul_le_mul_left _ hj
      omega
    rw [show M.length + (initClaim name).width + roundW deg * j + 3 =
        M.length + ((initClaim name).width + (roundW deg * j + 3)) by ring,
      hrd _ (by omega), List.getD_append_right _ _ _ _ (by omega), hiv, Nat.add_sub_cancel_left,
      hv2 j hj, sqAns, hent _ (by omega)]
    rfl
  · have hne : xr.1 ≠ [] := by
      intro he; rw [he] at hv1; simp at hv1; have := Nat.mul_pos (by omega : 0 < roundW deg) hk; omega
    rw [show M.length + (initClaim name).width + roundW deg * k - 1 =
        M.length + ((initClaim name).width + (roundW deg * k - 1)) by
          have := Nat.mul_pos (by omega : 0 < roundW deg) hk; omega,
      hrd _ (by have := Nat.mul_pos (by omega : 0 < roundW deg) hk; omega),
      List.getD_append_right _ _ _ _ (by omega), hiv, Nat.add_sub_cancel_left,
      getLastD_of_ne hne _ default, List.getLastD_eq_getLast?, List.getLast?_eq_getElem?,
      List.getD_eq_getElem?_getD, hv1]

/-- The first round's message on the log (any degree). -/
theorem roundsT_first (inp : Input) (o deg real P : ℕ) (es : Log) {n j : ℕ} {d : Digest} {cv : Val}
    {tr : Trace} {x : List Val × Bool × Trace} (h : roundsT inp 0 o deg false real (n + 1) j d cv tr = some x)
    (he : ∀ m < 2 * (n + 1), tr.getD m default = es.getD (P + 2 * j + m) default) :
    ∀ off, off + 16 ≤ 48 → readF (Snd.msgAt es (P + 2 * j)) off = elemAt inp 0 (o + j * 48 + off) := by
  rcases tr with _ | ⟨⟨q₁, a₁⟩, _ | ⟨⟨q₂, a₂⟩, tr⟩⟩
  · simp [roundsT] at h
  · simp [roundsT] at h
  simp only [roundsT] at h
  split_ifs at h with hq <;> exact (round_entries hq.1 (fun m hm => he m (by omega))).1

/-- **A degree-3 F rounds phase on the skeleton's registers** (Z3, Lr2, E2): with `cl = outs[n]`'s
head holding `c`, its `j`-th challenge register holds `rch P es j`, and its last register the claim
after the real rounds, `clR P c … (min real k)`. -/
theorem roundsF3_view4 {tr : Trace} {y : List Val × List Bool × Trace} (h : SkRun4 impl p inp tr y)
    {n : ℕ} (hn : n < (phasesOf seq4).length) {f k : ℕ}
    (hsh : (phasesOf seq4)[n].2 = .rounds f k 3 false) (L : Log) :
    ((skeleton4 seq4 p).2.outs.getD n []).headD 0 < (#[] ++ y.1.toArray).size ∧
      rd (#[] ++ y.1.toArray) (((skeleton4 seq4 p).2.outs.getD n []).headD 0) =
        clVal inp (initClaim (phasesOf seq4)[n].1) (fieldOffOf seq4 f + phaseOffOf seq4 n f)
          (#[] ++ y.1.toArray) (cAt4 seq4 p n).uni ∧
      (∀ j < k, ((skeleton4 seq4 p).2.outs.getD n []).getD (j + 1) 0 < (#[] ++ y.1.toArray).size ∧
        rd (#[] ++ y.1.toArray) (((skeleton4 seq4 p).2.outs.getD n []).getD (j + 1) 0) =
          .f (rch (phStart4 n) (fsOf tr (itemsOf seq4)) j)) ∧
      ((skeleton4 seq4 p).2.outs.getD n []).getLastD 0 < (#[] ++ y.1.toArray).size ∧
      ∀ c : F, rd (#[] ++ y.1.toArray) (((skeleton4 seq4 p).2.outs.getD n []).headD 0) = .f c →
        rd (#[] ++ y.1.toArray) (((skeleton4 seq4 p).2.outs.getD n []).getLastD 0) =
          .f (clR (phStart4 n) (fun _ _ => c) L (fsOf tr (itemsOf seq4))
            (min (realRounds p (phasesOf seq4)[n].1 k) k)) := by
  obtain ⟨b, hout, hsz, hcl, hcv, hch, xr, d, trk, hxr, -, hent, hlast⟩ := rounds_core4 h hn hsh
  rw [hout]
  have hw : roundW 3 = 16 := rfl
  rw [hw] at hsz hch
  refine ⟨hcl, hcv, fun j hj => ?_, ?_, fun c hc => ?_⟩
  · rw [List.cons_append, List.getD_cons_succ, List.getD_append _ _ _ _ (by simpa using hj),
      List.getD_eq_getElem _ _ (by simpa using hj), List.getElem_map, List.getElem_range]
    exact ⟨lt_reg (by rw [hw]; omega), hch j hj⟩
  · rw [List.cons_append, List.getLastD_cons, List.getLastD_eq_getLast?, List.getLast?_append,
      List.getLast?_singleton]
    split_ifs with hk
    · simpa using hcl
    · simp only [Option.some_or, Option.getD_some, hw]; exact lt_reg (by omega)
  · simp only [List.cons_append, List.headD_cons] at hc
    rw [hcv] at hc
    rw [List.cons_append, List.getLastD_cons, List.getLastD_eq_getLast?, List.getLast?_append,
      List.getLast?_singleton]
    split_ifs with hk
    · subst hk; simp only [Option.some_or, Option.getD_some, Nat.min_zero]
      rw [hcv, hc]; rfl
    · simp only [Option.some_or, Option.getD_some]
      rw [hlast (by omega), rounds3_log inp _ _ (phStart4 n) _ (fun _ _ => c) L k 0 d _ trk xr hxr hent
        (Nat.zero_le _) hc, Nat.zero_add]

/-- **A degree-2 F rounds phase on the skeleton's registers** (L2, S2, E4): as `roundsF3_view4`,
with the claims `clR2`; and every real round's check `Chk2 P …` holds from the head's claim `c`. -/
theorem roundsF2_view4 {tr : Trace} {y : List Val × List Bool × Trace} (h : SkRun4 impl p inp tr y)
    {n : ℕ} (hn : n < (phasesOf seq4).length) {f k : ℕ}
    (hsh : (phasesOf seq4)[n].2 = .rounds f k 2 false) (L : Log) :
    ((skeleton4 seq4 p).2.outs.getD n []).headD 0 < (#[] ++ y.1.toArray).size ∧
      rd (#[] ++ y.1.toArray) (((skeleton4 seq4 p).2.outs.getD n []).headD 0) =
        clVal inp (initClaim (phasesOf seq4)[n].1) (fieldOffOf seq4 f + phaseOffOf seq4 n f)
          (#[] ++ y.1.toArray) (cAt4 seq4 p n).uni ∧
      (∀ j < k, ((skeleton4 seq4 p).2.outs.getD n []).getD (j + 1) 0 < (#[] ++ y.1.toArray).size ∧
        rd (#[] ++ y.1.toArray) (((skeleton4 seq4 p).2.outs.getD n []).getD (j + 1) 0) =
          .f (rch (phStart4 n) (fsOf tr (itemsOf seq4)) j)) ∧
      ((skeleton4 seq4 p).2.outs.getD n []).getLastD 0 < (#[] ++ y.1.toArray).size ∧
      ∀ c : F, rd (#[] ++ y.1.toArray) (((skeleton4 seq4 p).2.outs.getD n []).headD 0) = .f c →
        rd (#[] ++ y.1.toArray) (((skeleton4 seq4 p).2.outs.getD n []).getLastD 0) =
          .f (clR2 (phStart4 n) 16 readF (fun d => chF d 0) (fun _ _ => c) L (fsOf tr (itemsOf seq4))
            (min (realRounds p (phasesOf seq4)[n].1 k) k)) ∧
        ∀ l < min (realRounds p (phasesOf seq4)[n].1 k) k,
          Chk2 (phStart4 n) 16 readF (fun d => chF d 0) (fun _ _ => c) L (fsOf tr (itemsOf seq4)) l := by
  obtain ⟨b, hout, hsz, hcl, hcv, hch, xr, d, trk, hxr, hfl, hent, hlast⟩ := rounds_core4 h hn hsh
  rw [hout]
  have hw : roundW 2 = 13 := rfl
  rw [hw] at hsz hch
  refine ⟨hcl, hcv, fun j hj => ?_, ?_, fun c hc => ?_⟩
  · rw [List.cons_append, List.getD_cons_succ, List.getD_append _ _ _ _ (by simpa using hj),
      List.getD_eq_getElem _ _ (by simpa using hj), List.getElem_map, List.getElem_range]
    exact ⟨lt_reg (by rw [hw]; omega), hch j hj⟩
  · rw [List.cons_append, List.getLastD_cons, List.getLastD_eq_getLast?, List.getLast?_append,
      List.getLast?_singleton]
    split_ifs with hk
    · simpa using hcl
    · simp only [Option.some_or, Option.getD_some, hw]; exact lt_reg (by omega)
  · simp only [List.cons_append, List.headD_cons] at hc
    rw [hcv] at hc
    obtain ⟨h1, h2⟩ := rounds2_log inp _ _ (phStart4 n) _ (fun _ _ => c) L k 0 d _ trk xr hxr hent
      (Nat.zero_le _) hc
    refine ⟨?_, fun l hl => by
      simpa using h2 hfl l (by omega) (by simp only [Nat.zero_add]; omega)⟩
    rw [List.cons_append, List.getLastD_cons, List.getLastD_eq_getLast?, List.getLast?_append,
      List.getLast?_singleton]
    split_ifs with hk
    · subst hk; simp only [Option.some_or, Option.getD_some, Nat.min_zero]
      rw [hcv, hc]; rfl
    · simp only [Option.some_or, Option.getD_some]
      rw [hlast (by omega), h1, Nat.zero_add]

/-! ## Z2's univariate round -/

/-- **The univariate phase (Z2) on the skeleton's registers.** With `s = 0` for a node and `1` for a
segment, `outs[n] = [b + s + 3, b + s + 133, b + s + 134]`: register `b + s + 3` holds `λ`
(`fAt es (P + 1) 0`), `b + s + 133`/`b + s + 134` the two values of `lagrangeS` on the 127
coefficients (the log's message at `P`, `uniEs_log`) at `λ` with the target `targetS κ pe`. A node's
`pe` is the `pt` register's array; a segment's is the packed operand in register `b`, the
`segPtRegs` registers (`hpt`: when they precede the phase). -/
theorem uni_view4 {tr : Trace} {y : List Val × List Bool × Trace} (h : SkRun4 impl p inp tr y)
    {n : ℕ} (hn : n < (phasesOf seq4).length) {f : ℕ} (hsh : (phasesOf seq4)[n].2 = .uni f) :
    ∃ (b : ℕ) (pe : Array F),
      let s := if p.d.node then 0 else 1
      let es := fsOf tr (itemsOf seq4)
      let o := fieldOffOf seq4 f + phaseOffOf seq4 n f
      (skeleton4 seq4 p).2.outs.getD n [] = [b + s + 3, b + s + 133, b + s + 134] ∧
      b + s + 136 ≤ (#[] ++ y.1.toArray).size ∧
      rd (#[] ++ y.1.toArray) (b + s + 3) = .f (fAt es (phStart4 n + 1) 0) ∧
      rd (#[] ++ y.1.toArray) (b + s + 133) =
        .f (impl.lagrangeS (uniEs inp 0 o).toArray (fAt es (phStart4 n + 1) 0) (impl.targetS p.tix pe)).1 ∧
      rd (#[] ++ y.1.toArray) (b + s + 134) =
        .f (impl.lagrangeS (uniEs inp 0 o).toArray (fAt es (phStart4 n + 1) 0) (impl.targetS p.tix pe)).2 ∧
      (∀ i < 127, readF (Snd.msgAt es (phStart4 n)) (16 * i) = elemAt inp 0 (o + 16 * i)) ∧
      (p.d.node = true → pe = (rd (#[] ++ y.1.toArray) (cAt4 seq4 p n).pt).toAF) ∧
      (p.d.node = false → rd (#[] ++ y.1.toArray) b = .af pe ∧
        ((∀ x ∈ segPtRegs seq4 p (cAt4 seq4 p n).outs, x < (cAt4 seq4 p n).next) →
          pe = ((segPtRegs seq4 p (cAt4 seq4 p n).outs).map fun x => (rd (#[] ++ y.1.toArray) x).toF).toArray)) := by
  obtain ⟨trk, M, x, hx, hb, hwf, hext, -, hdrop, -⟩ := phase_at4 impl p.tix inp p h.ref hn
  have hok : CtxOk (cAt4 seq4 p n) (#[] ++ M.toArray) := by
    rcases hwf with ⟨h', -⟩ | h'
    · rw [hsh] at h'; cases h'
    · exact h'
  obtain ⟨seg, hseg, hsl, -⟩ := refPhase4_chain impl p.tix inp seq4 p hx (by simpa using hb)
    (by rw [hsh]; rfl) (q0 := 1) (by simp [hsh, isSeed4]) (.inr hok.1)
  have hout := skeleton4_outs seq4 p hn
  have hit : (phasesOf seq4)[n].2.itemsL seq4.lv = [.absorb uniBytes, .squeeze] := by rw [hsh]; rfl
  rw [List.drop_eq_getElem_cons hn, psItems4, List.flatMap_cons, hit] at hdrop
  rw [hit] at hsl
  obtain ⟨-, hent⟩ := seg_entries hdrop hseg hsl (by simp [Item.isFS]) (by simp)
  simp only [List.length_cons, List.length_nil] at hent
  generalize hph : (phasesOf seq4)[n] = ph at hx hsh hout
  obtain ⟨name, sh⟩ := ph
  simp only at hsh; subst hsh
  have hrM : ∀ z < M.length, rd (#[] ++ y.1.toArray) z = rd (#[] ++ M.toArray) z := fun z hz => by
    have hlt : z < (#[] ++ (M ++ x.1).toArray).size := by simp; omega
    rw [hext.2 _ hlt, show (#[] : Array Val) ++ (M ++ x.1).toArray = (#[] ++ M.toArray) ++ x.1.toArray
      by simp, rd_app_left (#[] ++ M.toArray) _ (by simpa using hz)]
  simp only [refPhase4] at hx
  rcases trk with _ | ⟨⟨q₁, a₁⟩, _ | ⟨⟨q₂, a₂⟩, trk⟩⟩
  · cases hx
  · cases hx
  simp only at hx
  split_ifs at hx with hq hnd <;> cases hx
  all_goals
    have e0 := hent 0 (by norm_num); have e1 := hent 1 (by norm_num)
    simp only [List.getD_cons_zero, List.getD_cons_succ, Nat.add_zero] at e0 e1
    have hlam : fAt (fsOf tr (itemsOf seq4)) (phStart4 n + 1) 0 = chF a₂ 0 := by
      rw [fAt, ansAt, entAt, ← e1]
    have hmsg : ∀ i < 127, readF (Snd.msgAt (fsOf tr (itemsOf seq4)) (phStart4 n)) (16 * i) =
        elemAt inp 0 (fieldOffOf seq4 f + phaseOffOf seq4 n f + 16 * i) := fun i hi => by
      rw [msgAt_of_q (p := phStart4 n) (by rw [← e0]; exact hq.1)]
      exact readF_piMsg inp _ _ (by simp only [uniBytes]; omega)
    have hsz := size_le_of_ext hext
    simp only [uniVals, List.length_append, List.length_cons, List.length_map, List.length_range,
      List.length_nil, uniEs] at hsz
  · -- a node
    refine ⟨M.length, (rd (#[] ++ M.toArray) (cAt4 seq4 p n).pt).toAF, ?_⟩
    dsimp only; rw [if_pos hnd]; simp only [Nat.add_zero]
    refine ⟨by rw [hout]; simp [genPhase4, hnd, hb], by omega, ?_, ?_, ?_, hmsg,
      fun _ => by rw [hrM _ (by simpa using hok.2.2.2.2)], fun h => by rw [hnd] at h; cases h⟩
    · rw [rd_phase4 hext (by simp [uniVals, uniEs]), hlam]; rfl
    · rw [rd_phase4 hext (by simp [uniVals, uniEs]), hlam]; rfl
    · rw [rd_phase4 hext (by simp [uniVals, uniEs]), hlam]; rfl
  · -- a segment
    refine ⟨M.length, ((segPtRegs seq4 p (cAt4 seq4 p n).outs).map fun z =>
      (rd (#[] ++ M.toArray) z).toF).toArray, ?_⟩
    dsimp only; rw [if_neg hnd]
    refine ⟨by rw [hout]; simp [genPhase4, hnd, hb], by omega, ?_, ?_, ?_, hmsg,
      fun h => absurd h hnd, fun _ => ⟨?_, fun hpt => ?_⟩⟩
    · rw [show M.length + 1 + 3 = M.length + 4 by ring, rd_phase4 hext (by simp [uniVals, uniEs]), hlam]; rfl
    · rw [show M.length + 1 + 133 = M.length + 134 by ring, rd_phase4 hext (by simp [uniVals, uniEs]),
        hlam]; rfl
    · rw [show M.length + 1 + 134 = M.length + 135 by ring, rd_phase4 hext (by simp [uniVals, uniEs]),
        hlam]; rfl
    · rw [show M.length = M.length + 0 from rfl, rd_phase4 hext (by simp)]; rfl
    · exact congrArg List.toArray (List.map_congr_left fun z hz => by
        rw [hrM z (by rw [← hb]; exact hpt z hz)])

/-! ## The front's rounds phases by name -/

/-- **The front's univariate and rounds phases of `seq4`** (index, name, shape), and the phase
numbers 3.x's `phaseIx` gives their names, which the finals read through `outsOf`. -/
theorem phases4_rounds (S : Seq) :
    (phasesOf S)[4]? = some ("Z2", Sh.uni fZ2) ∧ (phasesOf S)[5]? = some ("Z3", Sh.rounds fZ3 S.z3 3 false) ∧
    (phasesOf S)[8]? = some ("L2", Sh.rounds fL2 14 2 false) ∧
    (phasesOf S)[12]? = some ("S2", Sh.rounds fS2 S.s2 2 false) ∧
    (phasesOf S)[14]? = some ("Lr2", Sh.rounds fLr S.lr 3 false) ∧
    (phasesOf S)[18]? = some ("E2", Sh.rounds fE S.e2 3 false) ∧
    (phasesOf S)[21]? = some ("E4", Sh.rounds fE S.e4 2 false) :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

theorem phaseIx4_rounds : phaseIx "Z2" = 4 ∧ phaseIx "Z3" = 5 ∧ phaseIx "L2" = 8 ∧ phaseIx "S2" = 12 ∧
    phaseIx "Lr2" = 14 ∧ phaseIx "E2" = 18 ∧ phaseIx "E4" = 21 := by
  obtain ⟨-, h4, h5, -, h8, -, -, h12, -, h14, -, -, h18, -, h21, -, -⟩ := phaseIx_vals
  exact ⟨h4, h5, h8, h12, h14, h18, h21⟩

/-- The real round counts by name: the kind's (`Z3`, `S2`, `Lr2`, `E2`, `E4`); L2's are its 14. -/
theorem realRounds_vals (p : KindP) (k : ℕ) : realRounds p "Z3" k = p.d.seq.z3 ∧
    realRounds p "S2" k = p.d.seq.s2 ∧ realRounds p "Lr2" k = p.d.seq.lr ∧ realRounds p "E2" k = p.d.seq.e2 ∧
    realRounds p "E4" k = p.d.seq.e4 ∧ realRounds p "L2" k = k := ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- The rounds phases' first claims: Z3's is Z2's register, Lr2's and E2's are `0`, the rest free. -/
theorem initClaim_vals : initClaim "Z3" = .uni ∧ initClaim "Lr2" = .zero ∧ initClaim "E2" = .zero ∧
    initClaim "L2" = .free ∧ initClaim "S2" = .free ∧ initClaim "E4" = .free := ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- **The finals' names read the skeleton's phases** (`outsOf`, `claim0`, `claimN`, `chals`). -/
theorem outsOf_skel {fi : FinIn} (hfi : fi.outs = (skeleton4 seq4 p).2.outs) (name : String) :
    outsOf fi name = (skeleton4 seq4 p).2.outs.getD (phaseIx name) [] ∧
      claim0 fi name = ((skeleton4 seq4 p).2.outs.getD (phaseIx name) []).headD 0 ∧
      claimN fi name = ((skeleton4 seq4 p).2.outs.getD (phaseIx name) []).getLastD 0 :=
  ⟨by rw [outsOf, hfi], by rw [claim0, outsOf, hfi], by rw [claimN, outsOf, hfi]⟩

theorem chals_getD {fi : FinIn} (name : String) {k j : ℕ} (hj : j < k) :
    (chals fi name k).getD j 0 = (outsOf fi name).getD (j + 1) 0 := by
  rw [chals, List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, List.getElem?_take_of_lt hj,
    List.getElem?_drop, Nat.add_comm]

/-! ## Controls -/

/-- Control (+/−): a free claim sits at `b + 2`, a zero claim at `b`, Z3's at Z2's register. -/
theorem clReg_ctl : clReg .free 7 10 = 12 ∧ clReg .zero 7 10 = 10 ∧ clReg .uni 7 10 = 7 ∧
    clReg .uni 7 10 ≠ 12 := by decide

/-- Control (+/−): a zero claim is `0` whatever the registers; Z3's reads its register. -/
theorem clVal_ctl (inp : Input) (o u : ℕ) (r : Array Val) :
    clVal inp .zero o r u = .f 0 ∧ clVal inp .uni o r u = rd r u ∧
      clVal inp .free o r u = .f (elemAt inp 0 (o + 16) + elemAt inp 0 (o + 32)) := ⟨rfl, rfl, rfl⟩

/-- Control (−): no rounds, no claim change, and a run of `0` rounds needs no entries. -/
theorem roundsT_zero_ctl (inp : Input) (o deg real : ℕ) (d : Digest) (cv : Val) :
    roundsT inp 0 o deg false real 0 0 d cv [] = some ([], true, []) := rfl

end FR.Snd.R4

end G6_FRSoundness4R4Rnd

section G6_FRSoundness4RsvStack

-- New for `flock-recursive` (revision 4.4.2, the reserve in RSV2's stacked form; track RSV-S2a): the
-- algebra of `finE` (iv″)'s one stacked `evalM`: the coefficients `s^P` split into the own kind's
-- `f̂·κ_E^m` and the child's `w·s`, the mixed point is `x̂ = r_E2 ‖ p_x[e2R, 23)`.

/-!
# The stacked call of `finE` (iv″) in the log's terms

`V(P)`'s row point is `r_E2[<22] ‖ x̂₂₂ ‖ s^P` (32 entries) and its column point `r′[<24] ‖ ŷ₂₄`;
`s^P_i = [i/3 = κ_P.ix]·f̂·κ_E^{i%3} + w·s_i`. **`mStack_sP`**: the stacked extension at those
entries is `f̂·(M̃_A + κ_E M̃_B + κ_E² M̃_C)_{κ_P}(r_E2, r′) + w·Σ_i s_i M̃_i(x̂, ŷ)`, the form of
`P4b.RejFinE4`.
-/

namespace FR.Snd.P4b
open RecursionFast Rev4

theorem arr_getD {α : Type} (l : List α) (j : ℕ) (d : α) : l.toArray.getD j d = l.getD j d := by
  simp [Array.getD_eq_getD_getElem?, List.getD_eq_getElem?_getD]

theorem e2R_ge (ν : NodeKind) : 22 ≤ e2R ν ∧ e2R ν ≤ 23 ∧ 24 ≤ ncR ν ∧ ncR ν ≤ 25 := by
  cases ν <;> decide

/-- `mStack` reads `s` below 9, `p` below 23 and `q` below 25. -/
theorem mStack_congr' (srcE : NodeKind → ESrc) {s s' p p' q q' : ℕ → F}
    (hs : ∀ i < 9, s i = s' i) (hp : ∀ j < 23, p j = p' j) (hq : ∀ j < 25, q j = q' j) :
    mStack srcE s p q = mStack srcE s' p' q' := by
  have hlp : ∀ κ : NodeKind, Rsv.lowA (e2R κ) p = Rsv.lowA (e2R κ) p' :=
    fun κ => funext fun j => hp j (lt_of_lt_of_le j.isLt (dims_le' κ).2.1)
  have hlq : ∀ κ : NodeKind, Rsv.lowA (ncR κ) q = Rsv.lowA (ncR κ) q' :=
    fun κ => funext fun j => hq j (lt_of_lt_of_le j.isLt (dims_le' κ).2.2.1)
  simp only [mStack, NodeKind.all, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    hlp, hlq, NodeKind.ix]
  rw [hs 0 (by norm_num), hs 1 (by norm_num), hs 2 (by norm_num), hs 3 (by norm_num), hs 4 (by norm_num),
    hs 5 (by norm_num), hs 6 (by norm_num), hs 7 (by norm_num), hs 8 (by norm_num)]

/-- `mStack` is linear in its coefficients. -/
theorem mStack_lin (srcE : NodeKind → ESrc) (a b : ℕ → F) (w : F) (p q : ℕ → F) :
    mStack srcE (fun i => a i + w * b i) p q = mStack srcE a p q + w * mStack srcE b p q := by
  simp only [mStack, NodeKind.all, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil]
  ring

/-- The own kind's coefficients `[i/3 = ν.ix]·f̂·κ_E^{i%3}` select `ν`'s three matrices. -/
theorem mStack_own (srcE : NodeKind → ESrc) (ν : NodeKind) (fz kE : F) (p q : ℕ → F) :
    mStack srcE (fun i => (if ν.ix = i / 3 then 1 else 0) * [fz, fz * kE, fz * (kE * kE)].getD (i % 3) 0) p q =
      fz * (Eval.matMLE (srcE ν).ea (Rsv.lowA (e2R ν) p) (Rsv.lowA (ncR ν) q) +
        kE * Eval.matMLE (srcE ν).eb (Rsv.lowA (e2R ν) p) (Rsv.lowA (ncR ν) q) +
        kE ^ 2 * Eval.matMLE (srcE ν).ec (Rsv.lowA (e2R ν) p) (Rsv.lowA (ncR ν) q)) := by
  cases ν <;>
  simp only [mStack, NodeKind.all, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, NodeKind.ix,
    Nat.reduceMul, Nat.reduceAdd, Nat.reduceDiv, Nat.reduceMod, List.getD_cons_zero, List.getD_cons_succ,
    ↓reduceIte, Nat.zero_ne_one, Nat.one_ne_zero, OfNat.ofNat_ne_zero, OfNat.ofNat_ne_one,
    OfNat.zero_ne_ofNat, OfNat.one_ne_ofNat, zero_mul, one_mul, add_zero, zero_add] <;> ring

/-- A mixed entry: below `e` the list `r` (of length `e`), at and above it `hi`. -/
theorem mixed_entry {r : List F} {e : ℕ} (hr : r.length = e) (hi : ℕ → F) {n j : ℕ} (hj : j < n)
    (hen : e ≤ n) (d : F) :
    (r ++ ((List.range n).map hi).drop e).getD j d = Rsv.hiPt (ptOf e r) hi j := by
  by_cases h : j < e
  · rw [Rsv.hiPt_lt _ _ h, List.getD_append _ _ _ _ (by omega)]
    simp only [ptOf]
    rw [List.getD_eq_getElem _ _ (by omega), List.getD_eq_getElem _ _ (by omega)]
  · rw [Rsv.hiPt_ge _ _ h, List.getD_append_right _ _ _ _ (by omega), hr, List.getD_eq_getElem?_getD,
      List.getElem?_drop, List.getElem?_map, List.getElem?_range (by omega)]
    simp only [Option.map_some, Option.getD_some]; congr 1; omega

/-- **The stacked call of `finE` (iv″)** at `V`'s entries (RSV2 §2.2). -/
theorem mStack_sP (srcE : NodeKind → ESrc) (ν : NodeKind) (r2 r4 : List F) (h2 : r2.length = e2R ν)
    (h4 : r4.length = ncR ν) (px py s : ℕ → F) (fz kE w d1 d2 : F) :
    mStack srcE
      (fun i => ((r2.take 22 ++ [(r2 ++ ((List.range 23).map px).drop (e2R ν)).getD 22 d1] ++
        (List.range 9).map fun i => (if ν.ix = i / 3 then 1 else 0) *
          [fz, fz * kE, fz * (kE * kE)].getD (i % 3) 0 + w * s i).toArray).getD (23 + i) 0)
      (fun j => ((r2.take 22 ++ [(r2 ++ ((List.range 23).map px).drop (e2R ν)).getD 22 d1] ++
        (List.range 9).map fun i => (if ν.ix = i / 3 then 1 else 0) *
          [fz, fz * kE, fz * (kE * kE)].getD (i % 3) 0 + w * s i).toArray).getD j 0)
      (fun j => ((r4.take 24 ++ [(r4 ++ ((List.range 25).map py).drop (ncR ν)).getD 24 d2]).toArray).getD j 0) =
    fz * (Eval.matMLE (srcE ν).ea (ptOf (e2R ν) r2) (ptOf (ncR ν) r4) +
        kE * Eval.matMLE (srcE ν).eb (ptOf (e2R ν) r2) (ptOf (ncR ν) r4) +
        kE ^ 2 * Eval.matMLE (srcE ν).ec (ptOf (e2R ν) r2) (ptOf (ncR ν) r4)) +
      w * mStack srcE s (Rsv.hiPt (ptOf (e2R ν) r2) px) (Rsv.hiPt (ptOf (ncR ν) r4) py) := by
  obtain ⟨g2, l2, g4, l4⟩ := e2R_ge ν
  have hl22 : (r2.take 22 ++ [(r2 ++ ((List.range 23).map px).drop (e2R ν)).getD 22 d1]).length = 23 := by
    simp [h2]; omega
  rw [mStack_congr' srcE (s' := fun i => (if ν.ix = i / 3 then 1 else 0) *
      [fz, fz * kE, fz * (kE * kE)].getD (i % 3) 0 + w * s i)
    (p' := Rsv.hiPt (ptOf (e2R ν) r2) px) (q' := Rsv.hiPt (ptOf (ncR ν) r4) py)]
  · rw [mStack_lin, mStack_own]
    have e1 : Rsv.lowA (e2R ν) (Rsv.hiPt (ptOf (e2R ν) r2) px) = ptOf (e2R ν) r2 :=
      funext fun j => Rsv.hiPt_lt _ _ j.isLt
    have e2 : Rsv.lowA (ncR ν) (Rsv.hiPt (ptOf (ncR ν) r4) py) = ptOf (ncR ν) r4 :=
      funext fun j => Rsv.hiPt_lt _ _ j.isLt
    rw [e1, e2]
  · intro i hi
    rw [arr_getD, List.getD_append_right _ _ _ _ (by omega), hl22, Nat.add_sub_cancel_left,
      R4.getD_mapRange _ _ hi]
  · intro j hj
    rw [arr_getD, List.getD_append _ _ _ _ (by omega)]
    by_cases hj22 : j < 22
    · rw [List.getD_append _ _ _ _ (by simp; omega), R4.getD_take' _ _ hj22]
      rw [← mixed_entry h2 px hj l2 0, List.getD_append _ _ _ _ (by omega)]
    · obtain rfl : j = 22 := by omega
      rw [List.getD_append_right _ _ _ _ (by simp <;> omega)]
      simp only [List.length_take, h2, Nat.min_eq_left g2, Nat.sub_self, List.getD_cons_zero]
      exact mixed_entry h2 px (by norm_num) l2 d1
  · intro j hj
    rw [arr_getD]
    by_cases hj24 : j < 24
    · rw [List.getD_append _ _ _ _ (by simp; omega), R4.getD_take' _ _ hj24]
      rw [← mixed_entry h4 py hj l4 0, List.getD_append _ _ _ _ (by omega)]
    · obtain rfl : j = 24 := by omega
      rw [List.getD_append_right _ _ _ _ (by simp <;> omega)]
      simp only [List.length_take, h4, Nat.min_eq_left g4, Nat.sub_self, List.getD_cons_zero]
      exact mixed_entry h4 py (by norm_num) l4 d2

end FR.Snd.P4b

end G6_FRSoundness4RsvStack

section G6_FRSoundness4R4FrE

-- New for `flock-recursive` (BLUEPRINT revision 4.1, A.9–A.10; stage R4d).

/-!
# The front's Lr and E checks on an accepted run (P4b's `RejEndLr4`, `RejEndE4`, …)

Generic views by name, for a `fi` whose `outs` are the skeleton's and a file `R` extending the
skeleton's registers: **`coordsR_view4`** (a coordinates phase's registers hold the log's
coordinates), **`chals_view4`** (a rounds phase's challenge registers hold `rchs`),
**`claimN3z_view4`** (a degree-3 rounds phase from claim `0`: its last register holds `clR … 0`),
**`msg_abs4`** (an absorbed message's reads are π's, through the program's query table). Then each
check: `relLr4`/`relE4` (the flags at `FinP`) read through the views is the log's equation.
-/

namespace FR.Snd.R4
open RecursionFast Rev4

variable {impl : OpImpl} {p : KindP} {inp : Input}

theorem ph4 {n : ℕ} {x : String × Sh} (h : (phasesOf seq4)[n]? = some x) :
    ∃ hn : n < (phasesOf seq4).length, (phasesOf seq4)[n] = x := List.getElem?_eq_some_iff.1 h

theorem val_eqv_f4 {a : F} {v : Val} (h : (Val.f a).eqv v = true) : v = .f a := by
  cases v <;> simp_all [Val.eqv]

/-- **The absorbs' messages read by the front** (one table certificate): Lr end (213, 1,008 bytes
with the reserve's child claim, RSV2 §2.1), E end (273, 112 bytes), E4 end (325), RS0 (326). -/
theorem fsMsgs4_ends : (fsMsgs4 seq4).getD 213 none = some (fieldOffOf seq4 fLrEnd, 1008) ∧
    (fsMsgs4 seq4).getD 273 none = some (fieldOffOf seq4 fEEnd, 112) ∧
    (fsMsgs4 seq4).getD 325 none = some (fieldOffOf seq4 fE + gOE4end seq4, 32) ∧
    (fsMsgs4 seq4).getD 326 none = some (fieldOffOf seq4 fRS0, 4 * 128 * 16) := by
  rw [fsMsgs4, gOE4end, seq4_eq]; decide +kernel

section V
variable {tr : Trace} {y : List Val × List Bool × Trace} (h : SkRun4 impl p inp tr y)

include h in
/-- **An absorbed message's reads are π's** (`SkRun4.hq` at a message of the program's table). -/
theorem msg_abs4 {q o len : ℕ} (hq : q < 482) (hq0 : q ≠ 0)
    (hm : (fsMsgs4 seq4).getD q none = some (o, len)) {off : ℕ} (hoff : off + 16 ≤ len) :
    readF (Snd.msgAt (fsOf tr (itemsOf seq4)) q) off = F.ofBytes (bytesAt inp.π (o + off) 16) := by
  have e := h.hq q (by omega)
  rw [hm] at e
  simp only [qOf, hq0, if_false] at e
  rw [msgAt_of_q e, readF, bytesAt_extract_of_le16 _ hoff]

include h in
/-- **The child claim's values on the log are π's** (Lrend's message at 213, bytes `48 + 16 j`). -/
theorem child_vals4 {j : ℕ} (hj : j < 60) :
    readF (Snd.msgAt (fsOf tr (itemsOf seq4)) 213) (48 + 16 * j) = pe4 seq4 inp fLrEnd (48 + 16 * j) := by
  rw [msg_abs4 h (by norm_num) (by norm_num) fsMsgs4_ends.1 (by omega)]; rfl

include h in
theorem mStL_eq4 : P4b.mStL (fsOf tr (itemsOf seq4)) = pe4 seq4 inp fEEnd 48 := by
  rw [P4b.mStL, msg_abs4 h (by norm_num) (by norm_num) fsMsgs4_ends.2.1 (by norm_num)]; rfl

include h in
theorem xL_eq4 : P4b.xL (fsOf tr (itemsOf seq4)) = pe4 seq4 inp fLrEnd rsvX := by
  rw [P4b.xL, msg_abs4 h (by norm_num) (by norm_num) fsMsgs4_ends.1 (by norm_num)]; rfl

include h in
theorem pxL_eq4 {j : ℕ} (hj : j < 23) : P4b.pxL (fsOf tr (itemsOf seq4)) j = pe4 seq4 inp fLrEnd (rsvRx + 16 * j) := by
  rw [P4b.pxL, child_vals4 h (by omega)]; rfl

include h in
theorem pyL_eq4 {j : ℕ} (hj : j < 25) : P4b.pyL (fsOf tr (itemsOf seq4)) j = pe4 seq4 inp fLrEnd (rsvRy + 16 * j) := by
  rw [P4b.pyL, show 416 + 16 * j = 48 + 16 * (23 + j) by omega, child_vals4 h (by omega)]
  simp only [rsvRy]; congr 1; omega

include h in
theorem sL_eq4 {i : ℕ} (hi : i < 9) : P4b.sL (fsOf tr (itemsOf seq4)) i = pe4 seq4 inp fLrEnd (rsvS + 16 * i) := by
  rw [P4b.sL, show 816 + 16 * i = 48 + 16 * (48 + i) by omega, child_vals4 h (by omega)]
  simp only [rsvS]; congr 1; omega

variable {fi : FinIn} (hfi : fi.outs = (skeleton4 seq4 p).2.outs)
  {R : Array Val} (hR : ExtA (#[] ++ y.1.toArray) R)
include h hfi hR

/-- **A coordinates phase by name**: the first `a ≤ 2k` registers after its head hold the log's
coordinates `fAt es (P + j/2) (j % 2)`. -/
theorem coordsR_view4 {name : String} {n k : ℕ} (hn : n < (phasesOf seq4).length)
    (hsh : (phasesOf seq4)[n].2 = .squeezes k .coords) (hk : 0 < k) (hix : phaseIx name = n)
    {a : ℕ} (ha : a ≤ 2 * k) :
    ((coordsR fi name).take a).map (fv R) =
      (List.range a).map (fun j => fAt (fsOf tr (itemsOf seq4)) (phStart4 n + j / 2) (j % 2)) := by
  obtain ⟨b, hout, hsz, hv⟩ := coords_view4 h hn hsh hk
  rw [coordsR, (outsOf_skel hfi name).1, hix, hout, List.drop_one, List.tail_cons]
  apply List.ext_getElem (by simp; omega)
  intro j h1 h2
  simp only [List.length_map, List.length_range] at h2
  simp only [List.getElem_map, List.getElem_take, List.getElem_range]
  have hlt : b + 3 * (j / 2) + 1 + j % 2 < (#[] ++ y.1.toArray).size := by omega
  show (rd R _).toF = _
  rw [hR.rd hlt, hv j (by omega)]; rfl

/-- **A rounds phase's challenges by name**: its first `a ≤ k` challenge registers hold
`rchs P es a`. -/
theorem chals_view4 {name : String} {n f k deg : ℕ} (hn : n < (phasesOf seq4).length)
    (hsh : (phasesOf seq4)[n].2 = .rounds f k deg false) (hix : phaseIx name = n) {a : ℕ} (ha : a ≤ k) :
    (chals fi name a).map (fv R) = rchs (phStart4 n) (fsOf tr (itemsOf seq4)) a := by
  obtain ⟨b, hout, hsz, -, -, hch, -⟩ := rounds_core4 h hn hsh
  rw [chals, (outsOf_skel hfi name).1, hix, hout, List.cons_append, List.drop_one, List.tail_cons,
    List.take_append_of_le_length (by simp; omega)]
  apply List.ext_getElem (by simp [rchs]; omega)
  intro j h1 h2
  simp only [rchs, List.length_map, List.length_range] at h2
  simp only [List.getElem_map, List.getElem_take, List.getElem_range, rchs]
  have hw : 4 ≤ roundW deg := by unfold roundW; split <;> omega
  have hm : roundW deg * j + roundW deg ≤ roundW deg * k := by
    rw [← Nat.mul_succ]; exact Nat.mul_le_mul_left _ (by omega)
  have hlt : b + (initClaim (phasesOf seq4)[n].1).width + roundW deg * j + 3 <
      (#[] ++ y.1.toArray).size := by omega
  show (rd R _).toF = _
  rw [hR.rd hlt, hch j (by omega)]; rfl

/-- **A degree-3 rounds phase from claim `0`, by name** (Lr2, E2): its last register holds the
claim after the real rounds. -/
theorem claimN3z_view4 {name : String} {n f k : ℕ} (hn : n < (phasesOf seq4).length)
    (hsh : (phasesOf seq4)[n].2 = .rounds f k 3 false) (hix : phaseIx name = n)
    (hnm : (phasesOf seq4)[n].1 = name) (hz : initClaim name = .zero) (L : Log) :
    claimN fi name < (#[] ++ y.1.toArray).size ∧
      rd R (claimN fi name) =
        .f (clR (phStart4 n) (fun _ _ => 0) L (fsOf tr (itemsOf seq4)) (min (realRounds p name k) k)) := by
  obtain ⟨-, hcv, -, hlt, hlast⟩ := roundsF3_view4 h hn hsh L
  rw [hnm, hz] at hcv
  rw [hnm] at hlast
  rw [(outsOf_skel hfi name).2.2, hix]
  exact ⟨hlt, by rw [hR.rd hlt]; exact hlast 0 hcv⟩

/-- **A one-challenge squeeze by name** (`Lr3`, `E3`, …): its register holds `fAt es P 0`. -/
theorem one_name_view4 {name : String} {n : ℕ} (hn : n < (phasesOf seq4).length)
    (hsh : (phasesOf seq4)[n].2 = .squeezes 1 .one) (hix : phaseIx name = n) :
    (outsOf fi name).headD 0 < (#[] ++ y.1.toArray).size ∧
      fv R ((outsOf fi name).headD 0) = fAt (fsOf tr (itemsOf seq4)) (phStart4 n) 0 := by
  obtain ⟨b, hout, hlt, hv⟩ := one_view4 h hn hsh
  rw [(outsOf_skel hfi name).1, hix, hout, List.headD_cons]
  refine ⟨hlt, ?_⟩
  show (rd R b).toF = _
  rw [hR.rd hlt, hv]; rfl

end V

/-! ## The kind of an accepted run's chain -/

theorem kindOfC_acc_node {ν : NodeKind} {P : FinP} {tr : Trace}
    (h : semIR impl (gen4 seq4 (.ofNode ν) (finOps4 P)) inp tr = some true) :
    kindOfC (fsOf tr (itemsOf seq4)) = .node ν := by
  obtain ⟨y, hS, -⟩ := fields_of_accept4 P h
  exact kindOfC_node4 hS

theorem kindOfC_acc_seg {σ : SegKind} {P : FinP} {tr : Trace}
    (h : semIR impl (gen4 seq4 (.ofSeg σ) (finOps4 P)) inp tr = some true) :
    kindOfC (fsOf tr (itemsOf seq4)) = .seg σ := by
  obtain ⟨y, hS, -⟩ := fields_of_accept4 P h
  exact kindOfC_seg4 hS

/-! ## Lr's end check (`finLr` (ii)) -/

/-- Lr's end message: its three values are the relocated reads of `fLrEnd`. -/
theorem vEnd_lr4 {tr : Trace} {y : List Val × List Bool × Trace} (h : SkRun4 impl p inp tr y) :
    vEnd 17 179 (fsOf tr (itemsOf seq4)) 0 = pe4 seq4 inp fLrEnd 0 ∧
    vEnd 17 179 (fsOf tr (itemsOf seq4)) 1 = pe4 seq4 inp fLrEnd 16 ∧
    vEnd 17 179 (fsOf tr (itemsOf seq4)) 2 = pe4 seq4 inp fLrEnd 32 := by
  have hm := fsMsgs4_ends.1
  refine ⟨?_, ?_, ?_⟩ <;> rw [vEnd, show 179 + 2 * 17 = 213 from rfl,
    msg_abs4 h (by norm_num) (by norm_num) hm (by norm_num)] <;> rfl

/-- **Lr's end equation on an accepted node run** (`finLr` (ii) through the views). -/
theorem lr_end4 {ν : NodeKind} {cells : List ℕ} {tr : Trace}
    (h : semIR impl (gen4 seq4 (.ofNode ν) (finOps4 (nodeFinP ν cells))) inp tr = some true) (L : Log) :
    clR 179 (fun _ _ => 0) L (fsOf tr (itemsOf seq4)) (P4b.lrR ν) =
      eq (ptOf (P4b.lrR ν) (tauS (P4b.lrR ν) 169 (fsOf tr (itemsOf seq4))))
          (ptOf (P4b.lrR ν) (rxs (P4b.lrR ν) 179 (fsOf tr (itemsOf seq4)))) *
        (vEnd 17 179 (fsOf tr (itemsOf seq4)) 0 * vEnd 17 179 (fsOf tr (itemsOf seq4)) 1 +
          vEnd 17 179 (fsOf tr (itemsOf seq4)) 2) := by
  obtain ⟨y, hS, fi, R, hfi, hE, hrel⟩ := relLr4_of_accept (nodeFinP ν cells) h
  have hnode : (nodeFinP ν cells).kv.node (KindP.ofNode ν).tix = true := rfl
  have hlr : (nodeFinP ν cells).lrR = P4b.lrR ν := rfl
  have hS4 : (nodeFinP ν cells).S = seq4 := rfl
  simp only [relLr4, hnode, ite_true, hlr, hS4] at hrel
  have hc := val_eqv_f4 hrel
  obtain ⟨hn14, e14⟩ := ph4 (n := 14) (x := ("Lr2", Sh.rounds fLr seq4.lr 3 false)) rfl
  obtain ⟨hn13, e13⟩ := ph4 (n := 13) (x := ("Lr1", Sh.squeezes 9 .coords)) (by rw [seq4_eq]; rfl)
  have hle := P4b.dims_le ν
  obtain ⟨-, hcl⟩ := claimN3z_view4 hS hfi hE hn14 (by rw [e14]) phaseIx4_rounds.2.2.2.2.1
    (by rw [e14]) rfl L
  rw [hc, (realRounds_vals _ _).2.2.1, (dims_node4 ν).2.2.2.1, Nat.min_eq_left hle.1,
    show phStart4 14 = 179 by rw [phStart4, fsStarts4_eq]; rfl] at hcl
  have hco := coordsR_view4 hS hfi hE hn13 (by rw [e13]) (by norm_num) phaseIx_vals.2.2.2.2.2.2.2.2.1
    (a := P4b.lrR ν) (by cases ν <;> decide)
  have hch := chals_view4 hS hfi hE hn14 (by rw [e14]) phaseIx4_rounds.2.2.2.2.1 hle.1
  rw [hco, hch, show phStart4 13 = 170 by rw [phStart4, fsStarts4_eq]; rfl,
    show phStart4 14 = 179 by rw [phStart4, fsStarts4_eq]; rfl, FR.Impl.eqPoint_eq] at hcl
  obtain ⟨v0, v1, v2⟩ := vEnd_lr4 hS
  rw [v0, v1, v2, ← Val.f.inj hcl]
  have hl : ∀ l : List F, l.toArray.size = l.length := fun _ => rfl
  rw [hl, List.length_map, List.length_range, FR.Impl.ptA_toArray, FR.Impl.ptA_toArray]
  rfl

/-- **`RejEndLr4` never holds on an accepted node run.** -/
theorem not_rejEndLr4_node {ν : NodeKind} {cells : List ℕ} {tr : Trace}
    (h : semIR impl (gen4 seq4 (.ofNode ν) (finOps4 (nodeFinP ν cells))) inp tr = some true) (L : Log) :
    ¬ P4b.RejEndLr4 L (fsOf tr (itemsOf seq4)) := by
  rw [P4b.RejEndLr4, P4b.onNode_iff (kindOfC_acc_node h)]
  exact fun ⟨_, hne⟩ => hne (lr_end4 h L)

/-- **… nor on an accepted segment run** (the gate). -/
theorem not_rejEndLr4_seg {σ : SegKind} {P : FinP} {tr : Trace}
    (h : semIR impl (gen4 seq4 (.ofSeg σ) (finOps4 P)) inp tr = some true) (L : Log) :
    ¬ P4b.RejEndLr4 L (fsOf tr (itemsOf seq4)) :=
  P4b.not_onNode_seg (kindOfC_acc_seg h)

/-! ## `finE` on an accepted run, with `finLr`'s exports -/

/-- `finE`'s registers are named, output or `zhat` registers (abstract `fi`). -/
theorem hin_E {fi : FinIn} {n : ℕ} (hsk : ∀ name, ∀ x ∈ outsOf fi name, x < n) (hn : 0 < n)
    (P : FinP) (hz : ∀ x ∈ fi.zhat, x < n) (h0 : lrEx fi 0 < n) (h1 : lrEx fi 1 < n) :
    ∀ x ∈ (coordsR fi "E1").take P.e2R ++ chals fi "E2" P.e2R ++ chals fi "E4" P.e4R ++
      [(outsOf fi "E3").headD 0, claimN fi "E2", claim0 fi "E4", claimN fi "E4",
       fi.zhat.getD 3 0, (outsOf fi "Lr3").headD 0, lrEx fi 0, lrEx fi 1,
       (coordsR fi "E1").getD 23 0, 0], x < n := by
  intro x hx
  simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hx
  rcases hx with ((hx | hx) | hx) | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact hsk "E1" x (List.mem_of_mem_drop (List.mem_of_mem_take hx))
  · exact hsk "E2" x (List.mem_of_mem_drop (List.mem_of_mem_take hx))
  · exact hsk "E4" x (List.mem_of_mem_drop (List.mem_of_mem_take hx))
  · exact headD_lt (hsk "E3") hn
  · exact getLastD_lt (hsk "E2") hn
  · exact headD_lt (hsk "E4") hn
  · exact getLastD_lt (hsk "E4") hn
  · exact getD_lt hn hz 3
  · exact headD_lt (hsk "Lr3") hn
  · exact h0
  · exact h1
  · exact getD_lt hn (fun x hx => hsk "E1" x (List.mem_of_mem_drop hx)) 23
  · exact hn

theorem rest_gFinLr (P : FinP) :
    (finalsOf P).rest[3]'(by rw [rest_finalsOf_length]; decide) = gFinLr P := by
  simp only [Finals.rest, finalsOf, List.cons_append, List.getElem_cons_succ, List.getElem_cons_zero]
theorem rest_gFinE (P : FinP) :
    (finalsOf P).rest[4]'(by rw [rest_finalsOf_length]; decide) = gFinE P := by
  simp only [Finals.rest, finalsOf, List.cons_append, List.getElem_cons_succ, List.getElem_cons_zero]

theorem opsOut_gFinLr (P : FinP) (fi : FinIn) (b : ℕ) :
    opsOut ((gFinLr P fi b).1.map (reloc P.S)) = 14 := by
  rw [opsOut_reloc]; cases hc : P.ck <;> simp [gFinLr, opsOut, Op.outs, hc]

theorem opsOut_gFinE (P : FinP) (fi : FinIn) (b : ℕ) :
    opsOut ((gFinE P fi b).1.map (reloc P.S)) = if P.rsvOps then 168 else 38 := by
  rw [opsOut_reloc]
  cases hr : P.rsvOps
  · cases hc : P.ck <;> simp [gFinE, gFinE0, opsOut, Op.outs, hc, hr]
  · simp only [gFinE, hr, Bool.cond_true, rsvEOps_split, opsOut_append, if_true]
    have hs : opsOut (rsvSOps (b + 38 + 72 + ·) (fun m => [fi.zhat.getD 3 0, b + 38 + 70, b + 38 + 71].getD m 0)
        (b + 38 + 69) (b + 38 + 75) (b + 38 + 48 + ·) (b + 38 + 76)) = 36 := by
      simp [rsvSOps, opsOut, Op.outs, List.map_append, List.sum_append, Function.comp_def]
    rw [hs]
    cases hc : P.ck <;> simp [gFinE0, rsvBC, rsvTl, opsOut, Op.outs, hc, Function.comp_def]

/-- `finE`'s exports after `r′` (`finB′`'s reads) are registers of the file after `finE`. -/
theorem gFinE_ex_lt (P : FinP) (fi : FinIn) {R R' : Array Val} {L : List Val} (hR' : R' = R ++ L.toArray)
    (hl : L.length = opsOut ((gFinE P fi R.size).1.map (reloc P.S))) :
    ∀ x ∈ (gFinE P fi R.size).2.drop 1, x < R'.size := by
  intro x hx
  rw [opsOut_gFinE] at hl
  have hsz : R'.size = R.size + L.length := by rw [hR']; simp
  rw [hsz, hl]
  cases hr : P.rsvOps
  · simp [gFinE, hr] at hx
  · simp only [gFinE, hr, Bool.cond_true, List.drop_succ_cons, List.drop_zero, List.mem_map,
      List.mem_range] at hx
    obtain ⟨i, hi, rfl⟩ := hx
    unfold rsvN at hi
    have : R.size + 38 + i < R.size + 168 := by omega
    simpa using this

/-- **`finE`'s relation on an accepted run**, with `lrEx`'s values: `v_L` (`vLv4` on `finLr`'s
file `R3`) and Lr2's challenges. -/
theorem relE4_of_accept (P : FinP) {tr : Trace}
    (h : semIR impl (gen4 seq4 p (finOps4 P)) inp tr = some true) :
    ∃ y, SkRun4 impl p inp tr y ∧ ∃ (fi : FinIn) (R3 R : Array Val),
      fi.outs = (skeleton4 seq4 p).2.outs ∧ ExtA (#[] ++ y.1.toArray) R3 ∧ ExtA R3 R ∧
      (∀ x ∈ fi.zhat, x < R.size) ∧
      relE4 impl p.tix inp fi R P = true ∧ fv R (lrEx fi 0) = vLv4 inp fi R3 P ∧
      (rd R (lrEx fi 1)).toAF = ((chals fi "Lr2" P.lrR).map (fv R3)).toArray := by
  obtain ⟨y, hS, zh, Rs, Ex, hext, hzh, hf⟩ := fields_ex4 P h
  obtain ⟨hs3, L3, hL3, he3, hx3⟩ := hf 3 (by decide)
  obtain ⟨-, L4, hL4, -, -⟩ := hf 4 (by decide)
  have hch : ∀ k < 12, ExtA (Rs k) (Rs (k + 1)) := fun k hk => by
    obtain ⟨-, L, -, he, -⟩ := hf k hk; rw [he]; exact ExtA.app _ _
  rw [rest_gFinLr] at hL3 hx3
  rw [rest_gFinE] at hL4
  have hpos := skel_pos4 hS
  have hE3 := hext 3 (by decide)
  have hE4 := hext 4 (by decide)
  have h34 : ExtA (Rs 3) (Rs 4) := hch 3 (by decide)
  have h04 : ExtA (Rs 0) (Rs 4) := chain_ext hch (by decide) (by decide)
  have hsk3 : ∀ name, ∀ x ∈ outsOf ⟨(skeleton4 seq4 p).2.outs, zh, Ex 3⟩ name, x < (Rs 3).size :=
    fun name x hx => Nat.lt_of_lt_of_le (outsOf_lt4 (p := p) hS zh (Ex 3) name x hx) hE3.1
  obtain ⟨L', hL', hv0, hv1⟩ := flag_gFinLr impl p.tix inp ⟨(skeleton4 seq4 p).2.outs, zh, Ex 3⟩ (Rs 3) P
    (hin_Lr hsk3 (lt_of_lt_of_le hpos hE3.1) P)
  obtain ⟨rfl, -⟩ := Prod.mk.inj (Option.some.inj (hL3.symm.trans hL'))
  rw [← he3] at hv0 hv1
  have hl3 := pureRun_len impl p.tix inp _ _ [] _ _ hL3
  rw [opsOut_gFinLr, List.length_nil, Nat.zero_add] at hl3
  have hsz4 : (Rs 4).size = (Rs 3).size + 14 := by rw [he3]; simp [hl3]
  set fi : FinIn := ⟨(skeleton4 seq4 p).2.outs, zh, Ex 4⟩
  have hlr : ∀ j, lrEx fi j = (gFinLr P ⟨(skeleton4 seq4 p).2.outs, zh, Ex 3⟩ (Rs 3).size).2.getD j 0 :=
    lrEx_eq4 hs3 _ fi hx3
  have hsk4 : ∀ name, ∀ x ∈ outsOf fi name, x < (Rs 4).size :=
    fun name x hx => Nat.lt_of_lt_of_le (outsOf_lt4 (p := p) hS zh (Ex 4) name x hx) hE4.1
  have hz4 : ∀ x ∈ fi.zhat, x < (Rs 4).size := fun x hx => Nat.lt_of_lt_of_le (hzh x hx) h04.1
  obtain ⟨LE, hLE, -⟩ := flag_gFinE impl p.tix inp fi (Rs 4) P
    (hin_E hsk4 (lt_of_lt_of_le hpos hE4.1) P hz4
      (by rw [hlr]; show (Rs 3).size + 13 < _; omega) (by rw [hlr]; show (Rs 3).size + 4 < _; omega))
  exact ⟨y, hS, fi, Rs 3, Rs 4, rfl, hE3, h34, hz4, pureRun_det hL4 hLE,
    by rw [hlr]; exact hv0, by rw [hlr]; exact hv1⟩

/-! ## E's end check (`finE` (ii)) and E4's rounds -/

theorem vEnd_e4 {tr : Trace} {y : List Val × List Bool × Trace} (h : SkRun4 impl p inp tr y) :
    vEnd 23 227 (fsOf tr (itemsOf seq4)) 0 = pe4 seq4 inp fEEnd 0 ∧
    vEnd 23 227 (fsOf tr (itemsOf seq4)) 1 = pe4 seq4 inp fEEnd 16 ∧
    vEnd 23 227 (fsOf tr (itemsOf seq4)) 2 = pe4 seq4 inp fEEnd 32 := by
  have hm := fsMsgs4_ends.2.1
  refine ⟨?_, ?_, ?_⟩ <;> rw [vEnd, show 227 + 2 * 23 = 273 from rfl,
    msg_abs4 h (by norm_num) (by norm_num) hm (by norm_num)] <;> rfl

/-- **E's end equation on an accepted node run** (`finE` (ii″) through the views; RSV2 §2.2: the
child term `η·eq(p_x, r)·(m̂* − X)`, `+` in `V`, equal in characteristic 2). -/
theorem e_end4 {ν : NodeKind} {cells : List ℕ} {tr : Trace}
    (h : semIR impl (gen4 seq4 (.ofNode ν) (finOps4 (nodeFinP ν cells))) inp tr = some true) (L : Log) :
    clR 227 (fun _ _ => 0) L (fsOf tr (itemsOf seq4)) (P4b.e2R ν) =
      eq (ptOf (P4b.e2R ν) (tauS (P4b.e2R ν) 214 (fsOf tr (itemsOf seq4))))
          (ptOf (P4b.e2R ν) (rxs (P4b.e2R ν) 227 (fsOf tr (itemsOf seq4)))) *
        (vEnd 23 227 (fsOf tr (itemsOf seq4)) 0 * vEnd 23 227 (fsOf tr (itemsOf seq4)) 1 +
          vEnd 23 227 (fsOf tr (itemsOf seq4)) 2) +
      P4b.etaL (fsOf tr (itemsOf seq4)) *
        eq (Rsv.lowA (P4b.e2R ν) (P4b.pxL (fsOf tr (itemsOf seq4))))
          (ptOf (P4b.e2R ν) (rxs (P4b.e2R ν) 227 (fsOf tr (itemsOf seq4)))) *
        (P4b.mStL (fsOf tr (itemsOf seq4)) - P4b.xL (fsOf tr (itemsOf seq4))) := by
  obtain ⟨y, hS, fi, R3, R, hfi, hE3, h3R, -, hrel, -, -⟩ := relE4_of_accept (nodeFinP ν cells) h
  have hE := hE3.trans h3R
  have hnode : (nodeFinP ν cells).kv.node (KindP.ofNode ν).tix = true := rfl
  have hro : (nodeFinP ν cells).rsvOps = true := rfl
  have he2 : (nodeFinP ν cells).e2R = P4b.e2R ν := rfl
  have hS4 : (nodeFinP ν cells).S = seq4 := rfl
  simp only [relE4, hro, hnode, ite_true, he2, hS4, rsvPx4, Bool.not_true, Bool.false_or,
    Bool.and_eq_true] at hrel
  obtain ⟨-, -, -, -, -, -, h2, -, -⟩ := hrel
  have hc := val_eqv_f4 h2
  obtain ⟨hn18, e18⟩ := ph4 (n := 18) (x := ("E2", Sh.rounds fE seq4.e2 3 false)) rfl
  obtain ⟨hn17, e17⟩ := ph4 (n := 17) (x := ("E1", Sh.squeezes 12 .coords)) (by rw [seq4_eq]; rfl)
  have hle := P4b.dims_le ν
  have hle' := P4b.dims_le' ν
  obtain ⟨-, hcl⟩ := claimN3z_view4 hS hfi hE hn18 (by rw [e18]) phaseIx4_rounds.2.2.2.2.2.1
    (by rw [e18]) rfl L
  rw [hc, (realRounds_vals _ _).2.2.2.1, (dims_node4 ν).2.2.2.2.1, Nat.min_eq_left hle.2.1,
    show phStart4 18 = 227 by rw [phStart4, fsStarts4_eq]; rfl] at hcl
  have hco := coordsR_view4 hS hfi hE hn17 (by rw [e17]) (by norm_num)
    phaseIx_vals.2.2.2.2.2.2.2.2.2.2.2.1 (a := P4b.e2R ν) (by cases ν <;> decide)
  have hco24 := coordsR_view4 hS hfi hE hn17 (by rw [e17]) (by norm_num)
    phaseIx_vals.2.2.2.2.2.2.2.2.2.2.2.1 (a := 24) (by norm_num)
  have heta : fv R ((coordsR fi "E1").getD 23 0) = P4b.etaL (fsOf tr (itemsOf seq4)) := by
    rw [show fv R ((coordsR fi "E1").getD 23 0) = ((coordsR fi "E1").map (fv R)).getD 23 (fv R 0) by
      rw [List.getD_map], ← getD_take' _ _ (show 23 < 24 by norm_num), ← List.map_take, hco24,
      getD_mapRange _ _ (by norm_num), P4b.etaL, coordAt,
      show phStart4 17 = 215 by rw [phStart4, fsStarts4_eq]; rfl]
  have hch := chals_view4 hS hfi hE hn18 (by rw [e18]) phaseIx4_rounds.2.2.2.2.2.1 hle.2.1
  rw [hco, hch, heta, show phStart4 17 = 215 by rw [phStart4, fsStarts4_eq]; rfl,
    show phStart4 18 = 227 by rw [phStart4, fsStarts4_eq]; rfl, FR.Impl.eqPoint_eq,
    FR.Impl.eqPoint_eq] at hcl
  obtain ⟨v0, v1, v2⟩ := vEnd_e4 hS
  rw [v0, v1, v2, ← Val.f.inj hcl, mStL_eq4 hS, xL_eq4 hS, CharTwo.sub_eq_add]
  have hl : ∀ l : List F, l.toArray.size = l.length := fun _ => rfl
  rw [hl, hl, List.length_map, List.length_range, List.length_take, List.length_map, List.length_range,
    Nat.min_eq_left hle'.2.1, FR.Impl.ptA_toArray, FR.Impl.ptA_toArray, FR.Impl.ptA_toArray]
  have hpx : ptOf (P4b.e2R ν) (((List.range 23).map fun j => pe4 seq4 inp fLrEnd (rsvRx + 16 * j)).take
      (P4b.e2R ν)) = Rsv.lowA (P4b.e2R ν) (P4b.pxL (fsOf tr (itemsOf seq4))) := by
    funext j
    have hj : (j : ℕ) < 23 := lt_of_lt_of_le j.isLt hle'.2.1
    simp only [ptOf, Rsv.lowA]
    rw [getD_take' _ _ j.isLt, getD_mapRange _ _ hj, pxL_eq4 hS hj]
  rw [hpx, show tauS (P4b.e2R ν) 214 (fsOf tr (itemsOf seq4)) = (List.range (P4b.e2R ν)).map
      (fun j => fAt (fsOf tr (itemsOf seq4)) (215 + j / 2) (j % 2)) from rfl,
    show rxs (P4b.e2R ν) 227 (fsOf tr (itemsOf seq4)) = rchs 227 (fsOf tr (itemsOf seq4)) (P4b.e2R ν) from rfl]
  ring

/-- **The child claim's two zero outputs on an accepted node run** (`finE`'s asserts
`X₃[1] = X₃[2] = 0`, read at Lrend's message, 213). -/
theorem rsvZero4 {ν : NodeKind} {cells : List ℕ} {tr : Trace}
    (h : semIR impl (gen4 seq4 (.ofNode ν) (finOps4 (nodeFinP ν cells))) inp tr = some true) :
    readF (msgAt (fsOf tr (itemsOf seq4)) 213) (48 + 16 * 58) = 0 ∧
      readF (msgAt (fsOf tr (itemsOf seq4)) 213) (48 + 16 * 59) = 0 := by
  obtain ⟨y, hS, fi, R3, R, hfi, hE3, h3R, -, hrel, -, -⟩ := relE4_of_accept (nodeFinP ν cells) h
  have hro : (nodeFinP ν cells).rsvOps = true := rfl
  have hS4 : (nodeFinP ν cells).S = seq4 := rfl
  simp only [relE4, hro, ite_true, hS4, Bool.and_eq_true, decide_eq_true_eq] at hrel
  obtain ⟨-, -, -, -, h58, h59, -⟩ := hrel
  rw [child_vals4 hS (by norm_num), child_vals4 hS (by norm_num)]
  exact ⟨h58, h59⟩

theorem not_rejEndE4_node {ν : NodeKind} {cells : List ℕ} {tr : Trace}
    (h : semIR impl (gen4 seq4 (.ofNode ν) (finOps4 (nodeFinP ν cells))) inp tr = some true) (L : Log) :
    ¬ P4b.RejEndE4 L (fsOf tr (itemsOf seq4)) := by
  rw [P4b.RejEndE4, P4b.onNode_iff (kindOfC_acc_node h)]
  exact fun ⟨_, hne⟩ => hne (e_end4 h L)

theorem not_rejEndE4_seg {σ : SegKind} {P : FinP} {tr : Trace}
    (h : semIR impl (gen4 seq4 (.ofSeg σ) (finOps4 P)) inp tr = some true) (L : Log) :
    ¬ P4b.RejEndE4 L (fsOf tr (itemsOf seq4)) :=
  P4b.not_onNode_seg (kindOfC_acc_seg h)

/-- A round check reads its initial claim only at round `0`, and there only its value. -/
theorem chk2F_c0 {c0 c0' : Log → Log → F} {L es : Log} (hc : c0 L es = c0' L es) (b l : ℕ) :
    Chk2 b 16 readF (fun d => chF d 0) c0 L es l ↔ Chk2 b 16 readF (fun d => chF d 0) c0' L es l := by
  cases l <;> simp only [Chk2, clR2, hc]

/-- **E4's round checks on an accepted node run** hold from `c4E4` (`finE` (iii) gives the first
claim, `lrEx` gives `v_L`). -/
theorem e_in4 {ν : NodeKind} {cells : List ℕ} {tr : Trace}
    (h : semIR impl (gen4 seq4 (.ofNode ν) (finOps4 (nodeFinP ν cells))) inp tr = some true) (L : Log) :
    ∀ l < P4b.ncR ν, Chk2 275 16 readF (fun d => chF d 0) P4b.c4E4 L (fsOf tr (itemsOf seq4)) l := by
  obtain ⟨y, hS, fi, R3, R, hfi, hE3, h3R, -, hrel, hv0, -⟩ := relE4_of_accept (nodeFinP ν cells) h
  have hE := hE3.trans h3R
  have hnode : (nodeFinP ν cells).kv.node (KindP.ofNode ν).tix = true := rfl
  have hS4 : (nodeFinP ν cells).S = seq4 := rfl
  have hro : (nodeFinP ν cells).rsvOps = true := rfl
  simp only [relE4, hro, hnode, ite_true, hS4, Bool.not_true, Bool.false_or, Bool.and_eq_true] at hrel
  obtain ⟨-, -, -, -, -, -, -, h3, -⟩ := hrel
  have hc := val_eqv_f4 h3
  rw [hv0] at hc
  obtain ⟨hn21, e21⟩ := ph4 (n := 21) (x := ("E4", Sh.rounds fE seq4.e4 2 false)) rfl
  obtain ⟨hn20, e20⟩ := ph4 (n := 20) (x := ("E3", Sh.squeezes 1 .one)) rfl
  obtain ⟨hn16, e16⟩ := ph4 (n := 16) (x := ("Lr3", Sh.squeezes 1 .one)) rfl
  obtain ⟨-, hkE⟩ := one_name_view4 hS hfi hE hn20 (by rw [e20]) phaseIx_vals.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  obtain ⟨-, hkL⟩ := one_name_view4 hS hfi hE3 hn16 (by rw [e16]) phaseIx_vals.2.2.2.2.2.2.2.2.2.2.1
  have hle := P4b.dims_le ν
  obtain ⟨hcl, -, -, -, hlast⟩ := roundsF2_view4 hS hn21 (by rw [e21]) L
  rw [(outsOf_skel hfi "E4").2.1, phaseIx4_rounds.2.2.2.2.2.2] at hc
  rw [← hE.rd hcl, hc] at hlast
  obtain ⟨-, hchk⟩ := hlast _ rfl
  rw [e21, (realRounds_vals _ _).2.2.2.2.1, (dims_node4 ν).2.2.2.2.2, Nat.min_eq_left hle.2.2,
    show phStart4 21 = 275 by rw [phStart4, fsStarts4_eq]; rfl] at hchk
  intro l hl
  refine (chk2F_c0 ?_ 275 l).1 (hchk l hl)
  obtain ⟨v0, v1, v2⟩ := vEnd_e4 hS
  obtain ⟨w0, w1, w2⟩ := vEnd_lr4 hS
  rw [show phStart4 20 = 274 by rw [phStart4, fsStarts4_eq]; rfl] at hkE
  rw [show phStart4 16 = 214 by rw [phStart4, fsStarts4_eq]; rfl] at hkL
  simp only [vLv4, hS4, hkE, hkL, P4b.c4E4, c4, kapB, v0, v1, v2, w0, w1, w2, mStL_eq4 hS]
  ring

theorem not_rejInE4_node {ν : NodeKind} {cells : List ℕ} {tr : Trace}
    (h : semIR impl (gen4 seq4 (.ofNode ν) (finOps4 (nodeFinP ν cells))) inp tr = some true) (L : Log) :
    ¬ P4b.RejInE4 L (fsOf tr (itemsOf seq4)) := by
  rw [P4b.RejInE4, P4b.onNode_iff (kindOfC_acc_node h)]
  exact fun ⟨l, hl, _, hne⟩ => hne (e_in4 h L l hl)

theorem not_rejInE4_seg {σ : SegKind} {P : FinP} {tr : Trace}
    (h : semIR impl (gen4 seq4 (.ofSeg σ) (finOps4 P)) inp tr = some true) (L : Log) :
    ¬ P4b.RejInE4 L (fsOf tr (itemsOf seq4)) :=
  P4b.not_onNode_seg (kindOfC_acc_seg h)

/-! ## `finE` (iv): E4's last claim (node matrix facts are parameters) -/

theorem clR2_c0_succ {c0 c0' : Log → Log → F} (b : ℕ) (L es : Log) (n : ℕ) :
    clR2 b 16 readF (fun d => chF d 0) c0 L es (n + 1) = clR2 b 16 readF (fun d => chF d 0) c0' L es (n + 1) :=
  rfl

/-- **`finE` (iv″) on an accepted node run** (RSV2 §2.2): E4's last claim is
`W(r′)·α_E + κ_E⁴·eq(p_y, r′)·Σ_i s_i M̃_i(x̂, ŷ)`, for `evalM`/`evalL` meeting the matrix MLEs (`hM`:
the stacked call at a 32-entry row point, `implN4F_hMX`'s content in `mStack`'s form; `hL`: the node's
L rows). -/
theorem e_fin4 (srcE srcL : NodeKind → P4b.ESrc) {ν : NodeKind} {cells : List ℕ} {tr : Trace}
    (hM : ∀ τ σ : Array F, τ.size = 32 → impl.evalM τ σ =
      (P4b.mStack srcE (fun i => τ.getD (23 + i) 0) (fun j => τ.getD j 0) (fun j => σ.getD j 0), 0, 0))
    (hL : ∀ rL r4 : Array F, rL.size = P4b.lrR ν → r4.size = P4b.ncR ν → impl.evalL rL r4 =
      (Eval.matMLE (srcL ν).ea (FR.Impl.ptA (P4b.lrR ν) rL) (FR.Impl.ptA (P4b.ncR ν) r4),
       Eval.matMLE (srcL ν).eb (FR.Impl.ptA (P4b.lrR ν) rL) (FR.Impl.ptA (P4b.ncR ν) r4),
       Eval.matMLE (srcL ν).ec (FR.Impl.ptA (P4b.lrR ν) rL) (FR.Impl.ptA (P4b.ncR ν) r4)))
    (h : semIR impl (gen4 seq4 (.ofNode ν) (finOps4 (nodeFinP ν cells))) inp tr = some true) (L : Log) :
    clR2 275 16 readF (fun d => chF d 0) P4b.c4E4 L (fsOf tr (itemsOf seq4)) (P4b.ncR ν) =
      mle (P4b.wEb4 srcE srcL ν (fsOf tr (itemsOf seq4))) (ptOf (P4b.ncR ν) (P4b.rPt4 ν (fsOf tr (itemsOf seq4)))) *
        readF (msgAt (fsOf tr (itemsOf seq4)) 325) 0 +
      kapB 23 227 (fsOf tr (itemsOf seq4)) ^ 4 *
        eq (Rsv.lowA (P4b.ncR ν) (P4b.pyL (fsOf tr (itemsOf seq4))))
          (ptOf (P4b.ncR ν) (P4b.rPt4 ν (fsOf tr (itemsOf seq4)))) *
        P4b.mStack srcE (P4b.sL (fsOf tr (itemsOf seq4))) (P4b.xHat ν (fsOf tr (itemsOf seq4)))
          (Rsv.hiPt (ptOf (P4b.ncR ν) (P4b.rPt4 ν (fsOf tr (itemsOf seq4)))) (P4b.pyL (fsOf tr (itemsOf seq4)))) := by
  obtain ⟨y, hS, fi, R3, R, hfi, hE3, h3R, -, hrel, -, hv1⟩ := relE4_of_accept (nodeFinP ν cells) h
  have hE := hE3.trans h3R
  have hnode : (nodeFinP ν cells).kv.node (KindP.ofNode ν).tix = true := rfl
  have hS4 : (nodeFinP ν cells).S = seq4 := rfl
  have he2 : (nodeFinP ν cells).e2R = P4b.e2R ν := rfl
  have he4 : (nodeFinP ν cells).e4R = P4b.ncR ν := rfl
  have hlr : (nodeFinP ν cells).lrR = P4b.lrR ν := rfl
  have hro : (nodeFinP ν cells).rsvOps = true := rfl
  have hkix : (nodeFinP ν cells).kix = ν.ix := rfl
  simp only [relE4, hro, hnode, ite_true, hS4, he2, he4, hkix, rsvPx4, rsvPy4, Bool.not_true, Bool.false_or,
    Bool.and_eq_true] at hrel
  rw [hlr] at hv1
  obtain ⟨⟨h4, -⟩, -, -, -, -, -, -, h2, h3⟩ := hrel
  have hc0 := val_eqv_f4 h2
  have hc := val_eqv_f4 h3
  have hz := val_eqv_f4 h4
  obtain ⟨hn21, e21⟩ := ph4 (n := 21) (x := ("E4", Sh.rounds fE seq4.e4 2 false)) rfl
  obtain ⟨hn20, e20⟩ := ph4 (n := 20) (x := ("E3", Sh.squeezes 1 .one)) rfl
  obtain ⟨hn16, e16⟩ := ph4 (n := 16) (x := ("Lr3", Sh.squeezes 1 .one)) rfl
  obtain ⟨hn18, e18⟩ := ph4 (n := 18) (x := ("E2", Sh.rounds fE seq4.e2 3 false)) rfl
  obtain ⟨hn14, e14⟩ := ph4 (n := 14) (x := ("Lr2", Sh.rounds fLr seq4.lr 3 false)) rfl
  have hle := P4b.dims_le ν
  obtain ⟨-, hkE⟩ := one_name_view4 hS hfi hE hn20 (by rw [e20]) phaseIx_vals.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  obtain ⟨-, hkL⟩ := one_name_view4 hS hfi hE hn16 (by rw [e16]) phaseIx_vals.2.2.2.2.2.2.2.2.2.2.1
  have hc2 := chals_view4 hS hfi hE hn18 (by rw [e18]) phaseIx4_rounds.2.2.2.2.2.1 hle.2.1
  have hc4 := chals_view4 hS hfi hE hn21 (by rw [e21]) phaseIx4_rounds.2.2.2.2.2.2 hle.2.2
  have hcL := chals_view4 hS hfi hE3 hn14 (by rw [e14]) phaseIx4_rounds.2.2.2.2.1 hle.1
  -- E4's last claim register holds the rounds' last claim
  obtain ⟨hcl, -, -, hlt, hlast⟩ := roundsF2_view4 hS hn21 (by rw [e21]) L
  rw [(outsOf_skel hfi "E4").2.1, phaseIx4_rounds.2.2.2.2.2.2] at hc0
  rw [(outsOf_skel hfi "E4").2.2, phaseIx4_rounds.2.2.2.2.2.2] at hc
  rw [← hE.rd hcl, hc0] at hlast
  obtain ⟨hN, -⟩ := hlast _ rfl
  rw [← hE.rd hlt, hc, e21, (realRounds_vals _ _).2.2.2.2.1, (dims_node4 ν).2.2.2.2.2,
    Nat.min_eq_left hle.2.2, show phStart4 21 = 275 by rw [phStart4, fsStarts4_eq]; rfl] at hN
  have hpos : P4b.ncR ν ≠ 0 := by cases ν <;> decide
  obtain ⟨n, hn⟩ : ∃ n, P4b.ncR ν = n + 1 := ⟨P4b.ncR ν - 1, by omega⟩
  rw [hn, clR2_c0_succ (c0' := P4b.c4E4), ← hn] at hN
  rw [← Val.f.inj hN]
  -- the right-hand side through `mle_wEb4`
  have hrP : P4b.rPt4 ν (fsOf tr (itemsOf seq4)) = rchs 275 (fsOf tr (itemsOf seq4)) (P4b.ncR ν) := rfl
  have hα : readF (msgAt (fsOf tr (itemsOf seq4)) 325) 0 = (rd R (fi.zhat.getD 3 0)).toF := by
    rw [hz, msg_abs4 hS (by norm_num) (by norm_num) fsMsgs4_ends.2.2.1 (by norm_num), Nat.add_zero]; rfl
  rw [P4b.mle_wEb4, hα, hrP]
  have hl : ∀ l : List F, l.toArray.size = l.length := fun _ => rfl
  rw [hc2, hc4, show phStart4 18 = 227 by rw [phStart4, fsStarts4_eq]; rfl,
    show phStart4 21 = 275 by rw [phStart4, fsStarts4_eq]; rfl] at *
  obtain ⟨g2, l2, g4, l4⟩ := P4b.e2R_ge ν
  have hτ : ((rchs 227 (fsOf tr (itemsOf seq4)) (P4b.e2R ν)).take 22 ++
      [(rchs 227 (fsOf tr (itemsOf seq4)) (P4b.e2R ν) ++ ((List.range 23).map fun j =>
        pe4 seq4 inp fLrEnd (rsvRx + 16 * j)).drop (P4b.e2R ν)).getD 22 (fv R 0)] ++
      (List.range 9).map fun i => (if ν.ix = i / 3 then 1 else 0) *
        [fv R (fi.zhat.getD 3 0), fv R (fi.zhat.getD 3 0) * fv R ((outsOf fi "E3").headD 0),
          fv R (fi.zhat.getD 3 0) * (fv R ((outsOf fi "E3").headD 0) * fv R ((outsOf fi "E3").headD 0))].getD
          (i % 3) 0 +
        fv R ((outsOf fi "E3").headD 0) * fv R ((outsOf fi "E3").headD 0) *
          (fv R ((outsOf fi "E3").headD 0) * fv R ((outsOf fi "E3").headD 0)) *
          eqPoint (((List.range 25).map fun j => pe4 seq4 inp fLrEnd (rsvRy + 16 * j)).take (P4b.ncR ν)).toArray
            (rchs 275 (fsOf tr (itemsOf seq4)) (P4b.ncR ν)).toArray * (rsvS4 inp (nodeFinP ν cells)).getD i 0).toArray.size
      = 32 := by
    simp [rchs]; omega
  rw [hv1, hcL, show phStart4 14 = 179 by rw [phStart4, fsStarts4_eq]; rfl, hM _ _ hτ,
    hL _ _ (by rw [hl]; simp [rxs, rchs]) (by rw [hl]; simp [rchs]),
    P4b.mStack_sP srcE ν _ _ (by simp [rchs]) (by simp [rchs])]
  simp only [FR.Impl.ptA_toArray]
  have hk1 : kapB 23 227 (fsOf tr (itemsOf seq4)) = fv R ((outsOf fi "E3").headD 0) := by
    rw [hkE, show phStart4 20 = 274 by rw [phStart4, fsStarts4_eq]; rfl]; rfl
  have hk2 : kapB 17 179 (fsOf tr (itemsOf seq4)) = fv R ((outsOf fi "Lr3").headD 0) := by
    rw [hkL, show phStart4 16 = 214 by rw [phStart4, fsStarts4_eq]; rfl]; rfl
  have hst : P4b.mStack srcE (fun i => (rsvS4 inp (nodeFinP ν cells)).getD i 0)
      (Rsv.hiPt (ptOf (P4b.e2R ν) (rchs 227 (fsOf tr (itemsOf seq4)) (P4b.e2R ν)))
        fun j => pe4 seq4 inp fLrEnd (rsvRx + 16 * j))
      (Rsv.hiPt (ptOf (P4b.ncR ν) (rchs 275 (fsOf tr (itemsOf seq4)) (P4b.ncR ν)))
        fun j => pe4 seq4 inp fLrEnd (rsvRy + 16 * j)) =
      P4b.mStack srcE (P4b.sL (fsOf tr (itemsOf seq4))) (P4b.xHat ν (fsOf tr (itemsOf seq4)))
        (Rsv.hiPt (ptOf (P4b.ncR ν) (rchs 275 (fsOf tr (itemsOf seq4)) (P4b.ncR ν)))
          (P4b.pyL (fsOf tr (itemsOf seq4)))) := by
    refine P4b.mStack_congr' srcE (fun i hi => ?_) (fun j hj => ?_) (fun j hj => ?_)
    · rw [rsvS4, getD_mapRange _ _ hi, sL_eq4 hS hi]; rfl
    · simp only [P4b.xHat, Rsv.hiPt]; split_ifs
      · rfl
      · rw [pxL_eq4 hS hj]
    · simp only [Rsv.hiPt]; split_ifs
      · rfl
      · rw [pyL_eq4 hS hj]
  have hw : eqPoint (((List.range 25).map fun j => pe4 seq4 inp fLrEnd (rsvRy + 16 * j)).take (P4b.ncR ν)).toArray
      (rchs 275 (fsOf tr (itemsOf seq4)) (P4b.ncR ν)).toArray =
      eq (Rsv.lowA (P4b.ncR ν) (P4b.pyL (fsOf tr (itemsOf seq4))))
        (ptOf (P4b.ncR ν) (rchs 275 (fsOf tr (itemsOf seq4)) (P4b.ncR ν))) := by
    rw [FR.Impl.eqPoint_eq, hl, List.length_take, List.length_map, List.length_range, Nat.min_eq_left l4,
      FR.Impl.ptA_toArray, FR.Impl.ptA_toArray]
    have hpy : ptOf (P4b.ncR ν) (((List.range 25).map fun j => pe4 seq4 inp fLrEnd (rsvRy + 16 * j)).take
        (P4b.ncR ν)) = Rsv.lowA (P4b.ncR ν) (P4b.pyL (fsOf tr (itemsOf seq4))) := by
      funext j
      have hj : (j : ℕ) < 25 := lt_of_lt_of_le j.isLt l4
      simp only [ptOf, Rsv.lowA]
      rw [getD_take' _ _ j.isLt, getD_mapRange _ _ hj, pyL_eq4 hS hj]
    rw [hpy]
  rw [hst, hw, hk1, hk2, rxs, rxs]
  ring

/-- **`RejFinE4` never holds on an accepted node run** (for `evalM`/`evalL` at the spec). -/
theorem not_rejFinE4_node (srcE srcL : NodeKind → P4b.ESrc) {ν : NodeKind} {cells : List ℕ} {tr : Trace}
    (hM : ∀ τ σ : Array F, τ.size = 32 → impl.evalM τ σ =
      (P4b.mStack srcE (fun i => τ.getD (23 + i) 0) (fun j => τ.getD j 0) (fun j => σ.getD j 0), 0, 0))
    (hL : ∀ rL r4 : Array F, rL.size = P4b.lrR ν → r4.size = P4b.ncR ν → impl.evalL rL r4 =
      (Eval.matMLE (srcL ν).ea (FR.Impl.ptA (P4b.lrR ν) rL) (FR.Impl.ptA (P4b.ncR ν) r4),
       Eval.matMLE (srcL ν).eb (FR.Impl.ptA (P4b.lrR ν) rL) (FR.Impl.ptA (P4b.ncR ν) r4),
       Eval.matMLE (srcL ν).ec (FR.Impl.ptA (P4b.lrR ν) rL) (FR.Impl.ptA (P4b.ncR ν) r4)))
    (h : semIR impl (gen4 seq4 (.ofNode ν) (finOps4 (nodeFinP ν cells))) inp tr = some true) (L : Log) :
    ¬ P4b.RejFinE4 srcE srcL L (fsOf tr (itemsOf seq4)) := by
  rw [P4b.RejFinE4, P4b.onNode_iff (kindOfC_acc_node h)]
  exact fun ⟨_, hne⟩ => hne (e_fin4 srcE srcL hM hL h L)

theorem not_rejFinE4_seg (srcE srcL : NodeKind → P4b.ESrc) {σ : SegKind} {P : FinP} {tr : Trace}
    (h : semIR impl (gen4 seq4 (.ofSeg σ) (finOps4 P)) inp tr = some true) (L : Log) :
    ¬ P4b.RejFinE4 srcE srcL L (fsOf tr (itemsOf seq4)) :=
  P4b.not_onNode_seg (kindOfC_acc_seg h)

/-! ## `finLc` on an accepted run; L2's round checks (`RejL2`) -/

/-- **The front's earlier absorbs** (one table certificate): Zend (67), L3 (97). -/
theorem fsMsgs4_front : (fsMsgs4 seq4).getD 67 none = some (fieldOffOf seq4 fZend, 32) ∧
    (fsMsgs4 seq4).getD 97 none = some (fieldOffOf seq4 fL2 + phaseOffOf seq4 9 fL2, 128) := by
  rw [fsMsgs4, seq4_eq]; decide +kernel

theorem rest_gFinLc (P : FinP) :
    (finalsOf P).rest[1]'(by rw [rest_finalsOf_length]; decide) = gFinLc P := by
  simp only [Finals.rest, finalsOf, List.cons_append, List.getElem_cons_succ, List.getElem_cons_zero]

/-- `finLc`'s registers are named or `zhat` registers (abstract `fi`). -/
theorem hin_Lc {fi : FinIn} {n : ℕ} (hsk : ∀ name, ∀ x ∈ outsOf fi name, x < n) (hn : 0 < n)
    (P : FinP) (hz : ∀ x ∈ fi.zhat, x < n) :
    ∀ x ∈ (chals fi "Z3" P.S.z3).take 8 ++ chals fi "L2" 14 ++
      [(outsOf fi "L1").headD 0, (outsOf fi "L3β").headD 0, (outsOf fi "Z2").headD 0,
       claim0 fi "L2", claimN fi "L2", fi.zhat.getD 1 0], x < n := by
  intro x hx
  simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hx
  rcases hx with (hx | hx) | rfl | rfl | rfl | rfl | rfl | rfl
  · exact hsk "Z3" x (List.mem_of_mem_drop (List.mem_of_mem_take (List.mem_of_mem_take hx)))
  · exact hsk "L2" x (List.mem_of_mem_drop (List.mem_of_mem_take hx))
  · exact headD_lt (hsk "L1") hn
  · exact headD_lt (hsk "L3β") hn
  · exact headD_lt (hsk "Z2") hn
  · exact headD_lt (hsk "L2") hn
  · exact getLastD_lt (hsk "L2") hn
  · exact getD_lt hn hz 1

/-- **`finLc`'s relation on an accepted run.** -/
theorem relLc4_of_accept (P : FinP) {tr : Trace}
    (h : semIR impl (gen4 seq4 p (finOps4 P)) inp tr = some true) :
    ∃ y, SkRun4 impl p inp tr y ∧ ∃ (fi : FinIn) (R : Array Val),
      fi.outs = (skeleton4 seq4 p).2.outs ∧ ExtA (#[] ++ y.1.toArray) R ∧ (∀ x ∈ fi.zhat, x < R.size) ∧
      relLc4 impl p.tix inp fi R P = true := by
  obtain ⟨y, hS, zh, Rs, Ex, hext, hzh, hf⟩ := fields_ex4 P h
  obtain ⟨-, L1, hL1, -, -⟩ := hf 1 (by decide)
  obtain ⟨-, L0, -, he0, -⟩ := hf 0 (by decide)
  rw [rest_gFinLc] at hL1
  have hpos := skel_pos4 hS
  have hE1 := hext 1 (by decide)
  have h01 : ExtA (Rs 0) (Rs 1) := by rw [he0]; exact ExtA.app _ _
  have hsk : ∀ name, ∀ x ∈ outsOf ⟨(skeleton4 seq4 p).2.outs, zh, Ex 1⟩ name, x < (Rs 1).size :=
    fun name x hx => Nat.lt_of_lt_of_le (outsOf_lt4 (p := p) hS zh (Ex 1) name x hx) hE1.1
  have hz : ∀ x ∈ zh, x < (Rs 1).size := fun x hx => Nat.lt_of_lt_of_le (hzh x hx) h01.1
  obtain ⟨L', hL'⟩ := flag_gFinLc impl p.tix inp ⟨(skeleton4 seq4 p).2.outs, zh, Ex 1⟩ (Rs 1) P
    (hin_Lc hsk (lt_of_lt_of_le hpos hE1.1) P hz)
  exact ⟨y, hS, ⟨(skeleton4 seq4 p).2.outs, zh, Ex 1⟩, Rs 1, rfl, hE1, hz, pureRun_det hL1 hL'⟩

/-- **L2's round checks on an accepted run** (any kind): `finLc` (i) gives L2's first claim
`â + α b̂` (Zend's message at 67, L1's `α`). -/
theorem l2_chk4 (P : FinP) (hP : P.S = seq4) {tr : Trace}
    (h : semIR impl (gen4 seq4 p (finOps4 P)) inp tr = some true) (L : Log) :
    ∀ l < 14, Chk2 69 16 readF (fun d => chF d 0) (fun _ es => c0L es) L (fsOf tr (itemsOf seq4)) l := by
  obtain ⟨y, hS, fi, R, hfi, hE, -, hrel⟩ := relLc4_of_accept P h
  simp only [relLc4, Bool.and_eq_true] at hrel
  have hc0 := val_eqv_f4 hrel.1.1
  obtain ⟨hn8, e8⟩ := ph4 (n := 8) (x := ("L2", Sh.rounds fL2 14 2 false)) rfl
  obtain ⟨hn7, e7⟩ := ph4 (n := 7) (x := ("L1", Sh.squeezes 1 .one)) rfl
  obtain ⟨-, hα⟩ := one_name_view4 hS hfi hE hn7 (by rw [e7]) phaseIx_vals.2.2.2.1
  obtain ⟨hcl, -, -, -, hlast⟩ := roundsF2_view4 hS hn8 (by rw [e8]) L
  rw [(outsOf_skel hfi "L2").2.1, phaseIx4_rounds.2.2.1] at hc0
  rw [← hE.rd hcl, hc0] at hlast
  obtain ⟨-, hchk⟩ := hlast _ rfl
  rw [e8, (realRounds_vals _ _).2.2.2.2.2, Nat.min_self,
    show phStart4 8 = 69 by rw [phStart4, fsStarts4_eq]; rfl] at hchk
  intro l hl
  refine (chk2F_c0 ?_ 69 l).1 (hchk l hl)
  have hm := fsMsgs4_front.1
  rw [hα, show phStart4 7 = 68 by rw [phStart4, fsStarts4_eq]; rfl, c0L, alL, vZ, vZ,
    msg_abs4 hS (by norm_num) (by norm_num) hm (by norm_num),
    msg_abs4 hS (by norm_num) (by norm_num) hm (by norm_num), hP]
  rfl

/-- **`RejL2` never holds on an accepted run** (either kind). -/
theorem not_rejL2_4 (P : FinP) (hP : P.S = seq4) {tr : Trace}
    (h : semIR impl (gen4 seq4 p (finOps4 P)) inp tr = some true) (L : Log) :
    ¬ P4a.RejL2 L (fsOf tr (itemsOf seq4)) :=
  fun ⟨l, hl, _, hne⟩ => hne (l2_chk4 P hP h L l hl)

/-! ## `relSh4`'s link term on a segment -/

/-- **A segment's `relSh4` link term is its accumulator** (R4c's D7): for an implementation meeting
the segment's specification, `linkWAll` is `0^8` (`linkWAll_seg_of_meets`), so `linkSum` adds
nothing (`linkSum_zero`): `w_in = (sh + κ_s e₀)·s_in`. -/
theorem linkSum_seg4 {fin : Finals} {lRows : List Circ.Row} {κs₀ : F}
    (hm : impl.Meets (specSeg (Impl.specC fin lRows κs₀))) (σ : SegKind) (tt rr : Array F)
    (ks acc pow : F) :
    linkSum (impl.linkWAll (KindP.ofSeg σ).tix tt rr) ks nLinkFam acc pow = acc := by
  rw [linkWAll_seg_of_meets hm σ, linkSum_zero]

end FR.Snd.R4

end G6_FRSoundness4R4FrE
