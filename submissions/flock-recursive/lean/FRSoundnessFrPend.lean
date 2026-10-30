-- New for `flock-recursive` (BLUEPRINT A.10 E4 end → RS0, A.9 finals' bindings; stage S-G6).
-- RET-2: the declarations revision 4.1 reads moved to `FRSoundnessCoreRows`.
import FRSoundnessFrE
import FRSoundnessCoreFront

/-!
# The RS claims' bindings, and E4 end's claim as RS claim 4

* **`okRS oZ oSh`**: the four bindings RS0's `RejRS`/`PendBad` take (`FRSoundnessFrRS0`): Z's
  (`oZ`; since INT-4 `finZ` asserts `P^z*(λ) = α_Z` (`relZ`), and the concrete binding is
  `FRSoundnessFrZ.oZ`), Lc's `v = v_β` (`finLc` (iii): `v_β = Σ_{i<8} β^i v_i` with L3's values
  and L3β's `β`; under revision 3.16's ruling on R-V-M1/M2 for a node), Sh's (`oSh`; the concrete
  binding is `FRSoundnessFrS.oSh`, `finSh` (ii)), E's `v = E4 end's value` (`okE`, `finE` (v)).
  `okRS` keeps Z's and Sh's as parameters so that this module stays below theirs.
  **`okRS_reads`**.
* **`trueL_three`**: on a node, RS claim 4's true value is `ẑ(r′)` at E4's point (`pack_unpack`,
  `eqPts_eq`). **`pendE_pendBad`**: E's pending doom is RS0's `PendBad` at claim 4.
-/

namespace FR.Snd
open RecursionFast FR.Merkle Finset

set_option linter.constructorNameAsVariable false

/-! ## The bindings -/

/-- **The RS claims' bindings**: Z's and Sh's are parameters; Lc's is `v_β`; E's is E4 end's value. -/
def okRS (oZ oSh : Kind → Log → F → Prop) (κ : Kind) (es : Log) (j : ℕ) (v : F) : Prop :=
  match j with
  | 0 => oZ κ es v
  | 1 => v = vBetaL es
  | 2 => oSh κ es v
  | _ => okE es v

theorem okRS_reads {oZ oSh : Kind → Log → F → Prop}
    (hZ : ∀ κ es es', Agree es es' 312 → oZ κ es = oZ κ es')
    (hSh : ∀ κ es es', Agree es es' 312 → oSh κ es = oSh κ es') : OkReads (okRS oZ oSh) := by
  intro κ es es' h
  have hv : vBetaL es = vBetaL es' := by
    simp only [vBetaL, fAt_congr h (show 98 < 312 by norm_num),
      msgAt_congr h (show 97 < 312 by norm_num)]
  have he : okE es = okE es' := by
    funext v; simp only [okE, msgAt_congr h (show 311 < 312 by norm_num)]
  funext j v
  rcases j with _ | _ | _ | j
  · simp only [okRS, hZ κ es es' h]
  · simp only [okRS, hv]
  · simp only [okRS, hSh κ es es' h]
  · simp only [okRS, he]

/-! ## E4 end's claim is RS claim 4 -/

theorem ePtL_eq (es : Log) : ePtL es = rE4 es := by
  unfold ePtL rE4 rchs2; exact List.map_congr_left fun _ _ => rfl

theorem rsPtsL_three {κ : Kind} (hn : κ.isNode = true) (es : Log) :
    (rsPtsL κ es).getD 3 [] = ePtL es := by
  simp [rsPtsL, hn]

/-- **RS claim 4's true value is `ẑ(r′)`** (a node; `pack_unpack`, `eqPts_eq`). -/
theorem trueL_three {L es : Log} (hn : (kindOf es).isNode = true) :
    trueL (kindOf es) L es 3 = mle (zC 23 L es) (ptOf 23 (rE4 es)) := by
  generalize hκ : kindOf es = κ at hn ⊢
  have hlen : (rsPtsL κ es).length = 4 := by rw [rsPtsL_length, if_pos hn]
  have hP : nrP 0 κ = 23 := by
    rw [nrP_zero]; cases κ <;> simp_all [Kind.isNode] <;> rfl
  have hlr : (rE4 es).length = 23 := by simp [rE4, rchs2]
  have h3 : ((3 : Fin 4) : ℕ) = 3 := rfl
  have hg : ∀ u : Fin (2 ^ nrP 0 κ), gL κ es 3 u = eqPts (rE4 es) (bitsL 23 u) := by
    intro u
    rw [gL, h3, if_pos (by rw [hlen]; norm_num), if_neg (show (3 : ℕ) ≠ 1 by norm_num), mul_one,
      rsPtsL_three hn, ePtL_eq, hlr]
  have hzC : zC 23 L es = fun y : Fin (2 ^ 23) => fF κ L es y := by
    funext y; simp [zC, hκ]
  have hb : ∀ i : Fin 128, bb i = bitBasis i := fun i => by
    simp only [bb, Nat.mod_eq_of_lt i.isLt]
  -- the left side, as a sum over the cube's indices
  have hl : trueL κ L es 3 =
      ∑ u ∈ range (2 ^ nrP 0 κ), eqPts (rE4 es) (bitsL 23 u) * fF κ L es u := by
    unfold trueL
    rw [← Fin.sum_univ_eq_sum_range (fun u => eqPts (rE4 es) (bitsL 23 u) * fF κ L es u)]
    simp only [hg, h3, cwL_three, hb, Algebra.algebraMap_self, RingHom.id_apply, mul_sum]
    rw [sum_comm]
    refine sum_congr rfl fun u _ => ?_
    rw [← pack_unpack (fF κ L es u), mul_sum]
    refine sum_congr rfl fun i _ => ?_
    simp only [rsQ]; ring
  -- the right side
  have hr : mle (zC 23 L es) (ptOf 23 (rE4 es)) =
      ∑ u ∈ range (2 ^ 23), eqPts (rE4 es) (bitsL 23 u) * fF κ L es u := by
    rw [mle, hzC, ← Fin.sum_univ_eq_sum_range (fun u => eqPts (rE4 es) (bitsL 23 u) * fF κ L es u)]
    refine sum_congr rfl fun u _ => ?_
    rw [eqPts_eq _ _ hlr (by simp [bitsL]), ptOf_bitsL u.val 23 u.isLt]
  rw [hl, hr, hP]

variable {rows : List Circ.Row}

/-- **E's pending doom is RS0's `PendBad` at claim 4.** -/
theorem pendE_pendBad {oZ oSh : Kind → Log → F → Prop} {L es : Log} (h : PendE L es) :
    PendBad (okRS oZ oSh) L es := by
  obtain ⟨hn, -, hne⟩ := h
  have hn' : (kindOf es).isNode = true := hn
  refine ⟨3, by rw [rsPtsL_length, if_pos hn']; decide, ?_⟩
  show ¬ okE es (trueL (kindOf es) L es 3)
  rw [trueL_three hn']; exact hne

/-! ## Controls -/

/-- Control (positive): Lc's binding accepts exactly `v_β`. -/
theorem okRS_one (oZ oSh : Kind → Log → F → Prop) (κ : Kind) (es : Log) :
    okRS oZ oSh κ es 1 (vBetaL es) := rfl

/-- Control (negative): Lc's binding refuses any other value. -/
theorem not_okRS_one {oZ oSh : Kind → Log → F → Prop} {κ : Kind} {es : Log} {v : F}
    (h : v ≠ vBetaL es) : ¬ okRS oZ oSh κ es 1 v := h

/-- Control: a zero L3 message gives `v_β = 0`. -/
theorem vBetaL_zero {es : Log} (h : ∀ i < 8, readF (msgAt es 97) (16 * i) = 0) : vBetaL es = 0 :=
  sum_eq_zero fun i hi => by rw [h i (mem_range.mp hi), mul_zero]

end FR.Snd
