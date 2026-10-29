-- New for `flock-recursive` (BLUEPRINT revision 4.1, A.9; stage R4c).
import FRSoundness4R4FinCtrl

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
