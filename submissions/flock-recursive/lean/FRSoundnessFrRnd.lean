-- New for `flock-recursive` (BLUEPRINT §3, A.4, A.9; stage S-G10).
-- RET-2: the declarations revision 4.1 reads moved to `FRSoundnessCoreAcc`.
import FRSoundnessFrRun
import FRSoundness4P4aSeg

/-!
# The front's F rounds on the skeleton's registers

The front's sumcheck phases (Z3, L2, S2, Lr2, E2, E4) run over F. **`chalsF_view`**: on an
accepted skeleton (`SkRun`), round `j`'s challenge register (`chals fi name K`'s `j`-th) holds
`rch (phStart n) es j`, the chain's F challenge at the round's squeeze (`roundsT_chalF`: register
`3` of each round's `roundW deg` registers is `chF a₂ 0`).
-/

namespace FR.Snd
open RecursionFast Finset FR.Impl

variable {impl : OpImpl} {κ : Kind} {inp : Input}

/-- An F rounds phase, unfolded. -/
theorem refPhase_roundsF {n : ℕ} {p : Phase} {c : GCtx} {r : Array Val} {tr : Trace}
    {x : List Val × Bool × Trace} {f K deg : ℕ} {real : KC ℕ}
    (hsh : p.shape = .rounds f K deg false real) (hx : refPhase impl κ inp n p c r tr = some x) :
    ∃ cl xr, roundsT inp f (phaseOff n f) deg false (real κ) K 0 (rd r c.st).toD cl tr = some xr ∧
      x = (initVals inp (initClaim p.name) f (phaseOff n f) false ++ xr.1, xr.2.1, xr.2.2) := by
  obtain ⟨name, sh⟩ := p
  simp only at hsh; subst hsh
  simp only [refPhase] at hx
  obtain ⟨xr, h1, rfl⟩ := Option.map_eq_some_iff.1 hx
  exact ⟨_, xr, h1, rfl⟩

/-- An F rounds phase's out list. -/
theorem genPhase_roundsF {n : ℕ} {p : Phase} (c : GCtx) {f K deg : ℕ} {real : KC ℕ}
    (hsh : p.shape = .rounds f K deg false real) :
    ∃ cl last, (genPhase n p c).2.outs.back?.getD [] = cl ::
        (List.range K).map (fun j => c.next + (initClaim p.name).width + roundW deg * j + 3) ++
          [last] := by
  obtain ⟨name, sh⟩ := p
  simp only at hsh; subst hsh
  simp only [genPhase]
  rcases initClaim name with _ | _ | _ <;>
  exact ⟨_, _, by simp [initOps, Init.width, Nat.add_assoc]; exact ⟨rfl, rfl⟩⟩

/-- **The challenge registers of an F rounds phase, by name**: `chals fi name K`'s `j`-th register
is a skeleton register holding `rch (phStart n) es j`. -/
theorem chalsF_view {tr : Trace} {y : List Val × List Bool × Trace} (h : SkRun impl κ inp tr y)
    {n : ℕ} (hn : n < phases.length) {f K deg : ℕ} {real : KC ℕ}
    (hsh : phases[n].shape = .rounds f K deg false real) (hf : f ≤ nFields) (hn0 : 0 < n)
    {fi : FinIn} (hfi : fi.outs = skeleton.2.outs) {name : String} (hix : phaseIx name = n)
    {R : Array Val} (hR : ExtA (#[] ++ y.1.toArray) R) {j : ℕ} (hj : j < K) :
    (chals fi name K).getD j 0 < (#[] ++ y.1.toArray).size ∧
      rd R ((chals fi name K).getD j 0) = .f (rch (phStart n) (fsOf tr items) j) := by
  obtain ⟨trk, M, x, hx, hb, hwf, hext, -, hdrop, -⟩ := phase_at impl κ inp h.ref hn
  have hst : (cAt n).st < (#[] ++ M.toArray).size := by
    rcases hwf with ⟨h', -⟩ | h'
    · rw [hsh] at h'; cases h'
    · exact h'.1
  obtain ⟨seg, hseg, hsl, -⟩ := refPhase_chain inp κ impl hx (by simpa using hb)
    (by rw [hsh]; exact decide_eq_true hf) (q0 := 1) (by simp [hsh, isSeed]) (.inr hst)
  obtain ⟨cl, xr, hxr, rfl⟩ := refPhase_roundsF hsh hx
  dsimp only at hext
  obtain ⟨hv1, hv2⟩ := roundsT_chalF inp f (phaseOff n f) deg (real κ) K 0 _ _ trk xr hxr
  obtain ⟨-, hent⟩ := phase_entries hn hdrop hseg hsl
    (by rw [hsh]; exact rounds_items_fs _ _ _ _ _) (by rw [hsh, rounds_items_length]; omega)
  rw [hsh, rounds_items_length] at hent
  obtain ⟨cl', last, hout⟩ := genPhase_roundsF (n := n) (cAt n) hsh
  have hiv := initValsF_length (inp := inp) (initClaim phases[n].name) f (phaseOff n f)
  set w0 := (initClaim phases[n].name).width
  have hc : (chals fi name K).getD j 0 = M.length + w0 + roundW deg * j + 3 := by
    rw [chals, outsOf, hfi, hix, skeleton_outs hn, hout, hb, List.cons_append, List.drop_one,
      List.tail_cons, List.take_left' (by simp), List.getD_eq_getElem _ _ (by simpa using hj),
      List.getElem_map, List.getElem_range]
  have hw : 4 ≤ roundW deg := by unfold roundW; split <;> omega
  have hlt : roundW deg * j + 3 < xr.1.length := by
    rw [hv1]
    have : roundW deg * j + roundW deg ≤ roundW deg * K := by
      rw [← Nat.mul_succ]; exact Nat.mul_le_mul_left _ hj
    omega
  have hm : w0 + (roundW deg * j + 3) < (initVals inp (initClaim phases[n].name) f
      (phaseOff n f) false ++ xr.1).length := by rw [List.length_append, hiv]; omega
  rw [hc]
  have hsz := size_le_of_ext hext
  refine ⟨(by omega : M.length + w0 + roundW deg * j + 3 < (#[] ++ y.1.toArray).size), ?_⟩
  rw [show M.length + w0 + roundW deg * j + 3 = M.length + (w0 + (roundW deg * j + 3)) by ring]
  have hlt' : M.length + (w0 + (roundW deg * j + 3)) < (#[] ++ y.1.toArray).size := by
    omega
  rw [hR.rd hlt', rd_phase hext hm, List.getD_append_right _ _ _ _ (by omega), hiv,
    Nat.add_sub_cancel_left, hv2 j hj, sqAns, hent _ (by omega)]
  rfl

end FR.Snd
