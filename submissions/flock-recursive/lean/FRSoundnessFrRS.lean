-- New for `flock-recursive` (BLUEPRINT A.10 RS0/RS1, §5.2 row RS1; stage S-G5).
-- RET-2: the declarations revision 4.1 reads moved to `FRSoundnessCoreRows`.
import FRSoundnessFrB
import FRSoundnessCoreFront

/-!
# RS1: the ring-switching batch (`hfin` at RS1's range `(312, 4)`)

* **`gL`, `sL`**: the four claims' weights `g_j(u) = eq(p_j, u)` on level 0's cube (claim 2 times
  the node's kind factor `kfT`, revision 3.16) and their RS0 slices (a leaf's fourth claim is `0`).
* **`DRS0`** (RS0's doom at its absorb): the level-0 word is far, a public cell is false, or some
  slice is false (`¬ truthRS0`).
* **`vRSL_eq`**: `v_RS = Σ_j κ^j T_j` (`rsT`); **`fipL_eq`**: `⟨W_rs, f⁽⁰⁾⟩ = Σ_j κ^j rsTruth_j`
  (`pack_unpack`).
* **`hfin_RS1`**: from `DRS0`, the escape to `¬ DRS1` puts `(r″, κ)` in `rs1_joint`'s set of at
  most `(7 + 3)·|F|^7` (§5.2's `10/2^128`).
-/

namespace FR.Snd
open RecursionFast Finset

set_option linter.constructorNameAsVariable false

/-! ## The claims' weights and slices -/

/-- Claim `j`'s weight on level 0's cube: `eq(p_j, cube u)`, times the kind factor
`kfT κ es (u / 2^7)` for claim 2 (`j = 1`; revision 3.16), `0` for a leaf's fourth claim. -/
noncomputable def gL (κ : Kind) (es : Log) (j : Fin 4) (u : Fin (2 ^ nrP 0 κ)) : F :=
  if j.val < (rsPtsL κ es).length then
    eqPts ((rsPtsL κ es).getD j []) (bitsL ((rsPtsL κ es).getD j []).length u) *
      (if j.val = 1 then kfT κ es (u.val / 2 ^ 7) else 1) else 0

/-- Claim `j`'s RS0 slices (`0` for a leaf's fourth claim). -/
def sL (κ : Kind) (es : Log) (j : Fin 4) (i : Fin 128) : F :=
  if j.val < (rsPtsL κ es).length then sliceL es j i else 0

/-- **RS0's doom** at its absorb: far, a public cell false, or a slice false. -/
def DRS0 (L es : Log) : Prop :=
  farL (kindOf es) L es 0 ∨ ¬ PubOK (kindOf es) L es ∨
    ¬ truthRS0 (kindOf es) L es (gL (kindOf es) es) (sL (kindOf es) es)

/-- RS1's `r″` as a point. -/
def fsL (es : Log) : Fin 7 → F := fun i => rsCoL es i

theorem ofFn_fsL (es : Log) : List.ofFn (fsL es) = rsRL es := by
  simp [fsL, rsRL, List.range_succ]

theorem rsPtsL_length (κ : Kind) (es : Log) :
    (rsPtsL κ es).length = if κ.isNode then 4 else 3 := by
  cases κ <;> rfl

/-! ## `v_RS` and its truth as batches -/

theorem rsTvL_eq (es : Log) (j : ℕ) :
    rsTvL es j = ∑ i : Fin 128, bitBasis i * Phi (rsRL es) (sliceL es j i) := by
  rw [rsTvL, ← Fin.sum_univ_eq_sum_range (fun k => bb k * Phi (rsRL es) (sliceL es j k))]
  refine sum_congr rfl fun i _ => ?_
  simp only [bb, Nat.mod_eq_of_lt i.isLt]

/-- **`v_RS = Σ_j κ^j T_j`** (`rsV`'s Horner form; a leaf's `T₃` is `0`). -/
theorem vRSL_eq (κ : Kind) (es : Log) :
    vRSL κ es = ∑ j : Fin 4, rsKL es ^ j.val * rsT (sL κ es) (fsL es) j := by
  have hT : ∀ j : Fin 4, rsT (sL κ es) (fsL es) j =
      if j.val < (rsPtsL κ es).length then rsTvL es j else 0 := by
    intro j
    simp only [rsT, sL, ofFn_fsL, Algebra.algebraMap_self, RingHom.id_apply, rsTvL_eq]
    split_ifs <;> simp [Phi_zero']
  simp only [hT, Fin.sum_univ_four, vRSL, rsPtsL_length]
  cases κ <;> simp [Kind.isNode] <;> ring

/-- The RS weight is the claims' `Φ`-batch of `gL`. -/
theorem wrsL_eq (κ : Kind) (es : Log) (u : Fin (2 ^ nrP 0 κ)) :
    wrsL κ es u = ∑ j : Fin 4, rsKL es ^ j.val * Phi (rsRL es) (gL κ es j u) := by
  simp only [Fin.sum_univ_four, gL, rsPtsL_length]
  cases κ <;>
    simp [wrsL, rsPtsL, Kind.isNode, List.zipIdx_cons, Phi_zero'] <;> ring

/-- **`⟨W_rs, f⁽⁰⁾⟩` is the batch of the switched claims' truths** (`pack_unpack`). -/
theorem fipL_eq (κ : Kind) (L es : Log) :
    fipL κ L es = ∑ j : Fin 4, rsKL es ^ j.val *
      rsTruth (rsQ κ L es (nrP 0 κ)) (gL κ es) (fsL es) j := by
  have hq : ∀ u : Fin (2 ^ nrP 0 κ),
      (∑ i, rsQ κ L es (nrP 0 κ) i u * bitBasis i) = fF κ L es u := fun u => pack_unpack _
  simp only [rsTruth, Algebra.algebraMap_self, RingHom.id_apply, hq, ofFn_fsL, mul_sum]
  rw [sum_comm, fipL, ← Fin.sum_univ_eq_sum_range (fun y => wrsL κ es y * fF κ L es y)]
  refine sum_congr rfl fun u _ => ?_
  rw [wrsL_eq, sum_mul]
  exact sum_congr rfl fun j _ => by ring

/-! ## `hfin` at RS1 -/

theorem gL_congr {es es' : Log} (h : Agree es es' 311) (κ : Kind) : gL κ es = gL κ es' := by
  funext j u; simp only [gL, rsPtsL_congr h κ, kfT_congr (h.mono (by norm_num)) κ]

theorem sL_congr {es es' : Log} (h : Agree es es' 313) (κ : Kind) : sL κ es = sL κ es' := by
  funext j i
  rw [sL, sL, rsPtsL_congr (h.mono (by norm_num)) κ, sliceL, sliceL,
    msgAt_congr h (show 312 < 313 by norm_num)]

open Classical in
/-- **`hfin` at RS1** (`hfin_rs1`, `rs1_of_not_truthRS0`): with RS0's doom `DRS0` before the range
and `DRS1` at its end, the escape probability is at most `10/2^128 ≤ deltaR`. -/
theorem hfin_RS1 {Dk : ℕ → Log → Log → Prop} (hmem : (312, 4) ∈ fsRanges)
    (hprev : Dk (phOf 312) = DRS0) (hfin : Dk (phOf 313) = msD (Dk (phOf 312)) DRS1 312 4)
    (L es₀ : Log) (hl : es₀.length = 313) : condCount (DPos (Dp Dk)) L es₀ 4 [] ≤ deltaR := by
  refine hfin_rs1 hmem hfin (c := 10) (by norm_num)
    (fun L es => if farL (kindOf es) L es 0 ∨ ¬ PubOK (kindOf es) L es then ∅ else
      univ.filter fun p : (Fin 7 → F) × F =>
        ∑ j, p.2 ^ j.val * rsT (sL (kindOf es) es) p.1 j =
          ∑ j, p.2 ^ j.val * rsTruth (rsQ (kindOf es) L es (nrP 0 (kindOf es)))
            (gL (kindOf es) es) p.1 j) (fun L es hd => ?_) (fun L es as hl' has hd hnf => ?_)
    L es₀ hl
  · rw [hprev] at hd
    split_ifs with hb
    · simp
    · have ht : ¬ truthRS0 (kindOf es) L es (gL (kindOf es) es) (sL (kindOf es) es) := by
        rcases hd with h | h | h
        · exact absurd (.inl h) hb
        · exact absurd (.inr h) hb
        · exact h
      exact rs1_of_not_truthRS0 (J' := 3) ht
  · -- the escape: `v_RS` true at the end
    generalize hX : ext es as = X at hnf ⊢
    have hS : Same L X L es 313 := by
      obtain ⟨ys, hys⟩ := ext_eq_append es as
      rw [← hX, hys, show (313 : ℕ) = es.length by omega]
      exact same_append L es ys
    have hag : Agree X es 313 := hS.1
    have hk : kindOf X = kindOf es := hS.kind (by norm_num)
    have hfar : farL (kindOf es) L X 0 ↔ farL (kindOf es) L es 0 :=
      farL_same hS (i := 0) (by norm_num) _ (by rw [capPos_zero]; norm_num)
    have hfF : fF (kindOf es) L X = fF (kindOf es) L es := by
      funext y
      simp only [fF, fTab_same hS (i := 0) (by norm_num) _ (by rw [capPos_zero]; norm_num)]
    have hpub : PubOK (kindOf es) L X ↔ PubOK (kindOf es) L es := by
      simp only [PubOK, hfF, vkL, stL, hag 0 (by norm_num), msgAt_congr hag (show 1 < 313 by
        norm_num)]
    simp only [DRS1, not_or, not_not, hk] at hnf
    obtain ⟨hnf1, hnf2, hnf3⟩ := hnf
    have hb : ¬ (farL (kindOf es) L es 0 ∨ ¬ PubOK (kindOf es) L es) := by
      rw [← hfar, ← hpub]; exact fun h => h.elim hnf1 fun h' => h' hnf3
    simp only [hb, ↓reduceIte, mem_filter, mem_univ, true_and]
    have h1 := vRSL_eq (kindOf es) X
    have h2 := fipL_eq (kindOf es) L X
    have hq : rsQ (kindOf es) L X (nrP 0 (kindOf es)) =
        rsQ (kindOf es) L es (nrP 0 (kindOf es)) := by
      funext i u; simp only [rsQ, hfF]
    rw [sL_congr hag] at h1
    rw [hq, gL_congr (hag.mono (by norm_num))] at h2
    exact h1.symm.trans (hnf2.trans h2)

/-! ## Controls -/

/-- Control (positive): with the true slices, RS0's slice part is not doomed. -/
theorem truthRS0_gL_true (κ : Kind) (L es : Log) :
    truthRS0 κ L es (gL κ es) fun j i => ∑ u, gL κ es j u * algebraMap F F (rsQ κ L es _ i u) :=
  truthRS0_true κ L es _

/-- Control (negative): a leaf's fourth claim carries no weight. -/
theorem gL_leaf_three (es : Log) (u : Fin (2 ^ nrP 0 .P30)) : gL .P30 es 3 u = 0 := by
  simp [gL, rsPtsL_length, Kind.isNode]

end FR.Snd
