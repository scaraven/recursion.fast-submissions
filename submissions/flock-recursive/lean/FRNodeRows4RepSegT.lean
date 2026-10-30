-- New for `flock-recursive` (SEG-R §4.2–4.3, stage SEG-R1b): prototype 1's `targetS` and `shiftTarget` replays.
import FRNodeRows4RepSegK
import FRVIRTplSegT
import FRNodeRows4RepRsK

/-!
# The segment program's `targetS` and `shiftTarget` replays (`KOpD`s on `rtKD`)

* **`kTSS`** (`targetS r`, `r : AF 37`): canonical inputs = the 37 entries of `r` (`tssLay`), no forced
  positions; template `Tpl.tsSegT` (55 gates, 18 forcing rows `L_l · L_l = L_l`). **`kTSS_ok`**: `KOkD` at
  every index, no hypothesis (`implSeg`'s `targetS` at a leaf kind is `targetSSegI`).
* **`kSTS`** (`shiftTarget τ θ bnd κs`, types `[af 18, af 10, af 22, f]`): canonical inputs = the 51
  encoding entries (`stsLay`); template `Tpl.stSegT` (789 gates, 512 bit locals, 516 forcing rows).
  **`kSTS_ok`**: `KOkD` at every index, given that the base's `shiftTarget` is `shiftTargetI` (`SegBase`).
* Operand types other than these get the rejecting row (`kdRows`' `inOk` check).

SEG-R2: the definitions (`kTSS`, `kSTS`) moved verbatim to `FRNodeRows4SegD` (below `FRNodeRows4`, so that the
fold names them); the theorems stay here.
-/

namespace FR
namespace N4s
open RecursionFast Rev4 Circ Tpl

/-! ## `targetS` -/


theorem tssIn_eq {ts : List Ty} (h : tssIn ts = true) : ts = [.af 37] := by
  unfold tssIn at h; split at h
  · rfl
  · exact absurd h Bool.false_ne_true

/-- **`targetS`'s replay obligation holds at every index** (no hypothesis). -/
theorem kTSS_ok {impl₀ : OpImpl} {base : NodeKind → OpImpl} (ι : Kind) : KOkD (implP impl₀ base 1 ι) ι kTSS := by
  intro op hc
  cases op
  all_goals first | exact absurd hc Bool.false_ne_true | skip
  rename_i r
  refine ⟨fun _ _ _ h => Res.noConfusion h, fun inp regs vs ok ts hev hin hty => ?_⟩
  simp only [evalOp, Res.vals.injEq] at hev
  obtain ⟨rfl, -⟩ := hev
  obtain rfl := tssIn_eq hin
  simp only [kTSS, tsArgs, List.map_cons, List.map_nil, List.cons.injEq, and_true] at hty
  obtain ⟨a, ha, hs⟩ := val_af hty
  have hv : (implP impl₀ base 1 ι).targetS ι (rd regs r).toAF = Rev4.targetSSegI a := by
    simp only [implP, one_ne_zero, ite_false, OpImpl.fixK, implSeg, ha, Val.toAF]
    rfl
  rw [hv]
  refine ⟨by simp [tyOf, Rev4.targetSSegI, Impl.targetSLeafI, kTSS], fun cst _ e h1 hinp _ => ?_⟩
  have hx : (kTSS.args (.targetS r) ι).flatMap (fun a => encV (rd regs a)) = a.toList := by
    simp [kTSS, tsArgs, ha, encV]
  rw [hx] at hinp
  refine GM.ok_mono (ok_tsSegT h1 cst a fun p hp => ?_) fun o ho hr => ?_
  · rw [hinp p hp]; simp [kTSS, tssLay, hp, arr_getD]
  · rw [ho hr]; simp [encV]

/-! ## `shiftTarget` -/


theorem stsIn_eq {ts : List Ty} (h : stsIn ts = true) : ts = [.af 18, .af 10, .af 22, .f] := by
  unfold stsIn at h; split at h
  · rfl
  · exact absurd h Bool.false_ne_true

/-- **`shiftTarget`'s replay obligation holds at every index** (the base's `shiftTarget` is
`shiftTargetI`). -/
theorem kSTS_ok {impl₀ : OpImpl} {base : NodeKind → OpImpl} (hS : impl₀.shiftTarget = Impl.shiftTargetI)
    (ι : Kind) : KOkD (implP impl₀ base 1 ι) ι kSTS := by
  intro op hc
  cases op
  all_goals first | exact absurd hc Bool.false_ne_true | skip
  rename_i t h bd ks
  refine ⟨fun _ _ _ h => Res.noConfusion h, fun inp regs vs ok ts hev hin hty => ?_⟩
  simp only [evalOp, Res.vals.injEq] at hev
  obtain ⟨rfl, -⟩ := hev
  obtain rfl := stsIn_eq hin
  simp only [kSTS, stArgs, List.map_cons, List.map_nil, List.cons.injEq, and_true] at hty
  obtain ⟨τ, hτ, hτs⟩ := val_af hty.1
  obtain ⟨θ, hθ, hθs⟩ := val_af hty.2.1
  obtain ⟨bn, hbn, hbs⟩ := val_af hty.2.2.1
  obtain ⟨κ, hκ⟩ := val_f hty.2.2.2
  have hv : (implP impl₀ base 1 ι).shiftTarget (rd regs ks).toF (rd regs t).toAF (rd regs h).toAF
      (rd regs bd).toAF = Impl.shiftTargetI κ τ θ bn := by
    rw [hτ, hθ, hbn, hκ]
    show impl₀.shiftTarget _ _ _ _ = _
    rw [hS]; rfl
  rw [hv]
  refine ⟨rfl, fun cst _ e h1 hinp _ => ?_⟩
  have hx : (kSTS.args (.shiftTarget t h bd ks) ι).flatMap (fun a => encV (rd regs a)) =
      τ.toList ++ θ.toList ++ bn.toList ++ [κ] := by
    simp [kSTS, stArgs, hτ, hθ, hbn, hκ, encV]
  rw [hx] at hinp
  have hi : ∀ p < 51, e.inp p = (τ.toList ++ θ.toList ++ bn.toList ++ [κ]).getD p 0 := fun p hp => by
    rw [hinp p hp]; simp [kSTS, stsLay, hp]
  have lτ : τ.toList.length = 18 := by simp [hτs]
  have lθ : θ.toList.length = 10 := by simp [hθs]
  have lb : bn.toList.length = 22 := by simp [hbs]
  refine GM.ok_mono (ok_stSegT h1 cst κ τ θ bn (fun l hl => ?_) (fun l hl => ?_) (fun l hl => ?_) ?_)
    fun o ho hr => ?_
  · rw [hi l (by omega), List.append_assoc, List.append_assoc, getD_append_left (by omega), arr_getD]
  · rw [hi _ (by omega), List.append_assoc, List.append_assoc, show 18 + l = τ.toList.length + l by omega,
      getD_append_right, getD_append_left (by omega), arr_getD]
  · rw [hi _ (by omega), List.append_assoc, show 28 + l = (τ.toList ++ θ.toList).length + l by simp [lτ, lθ],
      getD_append_right, getD_append_left (by omega), arr_getD]
  · rw [hi _ (by omega), show 50 = (τ.toList ++ θ.toList ++ bn.toList).length + 0 by simp [lτ, lθ, lb],
      getD_append_right]
    rfl
  · rw [ho hr]; simp [encV]

/-! ## Controls -/

/-- (+) `targetS` is covered; (−) nothing else is (`shiftTarget`). -/
theorem kTSS_cov : kTSS.cov (.targetS 3) = true ∧ kTSS.cov (.shiftTarget 0 1 2 3) = false := by decide

/-- (+) `shiftTarget` is covered; (−) nothing else is (`targetS`). -/
theorem kSTS_cov : kSTS.cov (.shiftTarget 0 1 2 3) = true ∧ kSTS.cov (.targetS 3) = false := by decide

/-- (+) The segment's `targetS` operand `AF 37` is served; (−) not another width (a node's `r`), nor two
operands. -/
theorem tssIn_ctl : tssIn [.af 37] = true ∧ tssIn [.af 36] = false ∧ tssIn [.af 37, .af 37] = false := by
  decide

/-- (+) The segment's `shiftTarget` operands are served; (−) not a `bnd` of another width (a node's),
nor `τ` of 16 coordinates, nor a `K` `κs`. -/
theorem stsIn_ctl : stsIn [.af 18, .af 10, .af 22, .f] = true ∧ stsIn [.af 18, .af 10, .af 4, .f] = false ∧
    stsIn [.af 16, .af 10, .af 22, .f] = false ∧ stsIn [.af 18, .af 10, .af 22, .k] = false := by decide

/-- (+) The canonical inputs read the whole encoding; (−) nothing past it. -/
theorem lay_ctl : tssLay [] 36 = some 36 ∧ tssLay [] 37 = none ∧ stsLay [] 50 = some 50 ∧ stsLay [] 51 = none := by
  decide

/-- (−) **A non-Boolean `L` entry fails its forcing row** (`targetS`'s range factor reads `L`'s bits). -/
theorem tsRow_neg {e : Env} {x : F} (hx : e.inp 19 = x) (h0 : x ≠ 0) (h1 : x ≠ 1) :
    ¬ RowT.Holds e ⟨I 19, I 19, I 19⟩ := fun h => by
  simp only [RowT.Holds, ev_I, hx] at h
  rcases bool_of_row h with h' | h'
  · exact h0 h'
  · exact h1 h'

/-- (−) **A flipped digest bit fails the pack row**: two Boolean bit vectors packing to the same half
agree everywhere (`shiftTarget`'s decomposition is unique). -/
theorem pack_neg {v v' : ℕ → F} {h : F} (hb : ∀ q < 128, v q = 0 ∨ v q = 1) (hb' : ∀ q < 128, v' q = 0 ∨ v' q = 1)
    (hp : ∑ q ∈ Finset.range 128, W4.E q * v q = h) {j : ℕ} (hj : j < 128) (hne : v' j ≠ v j) :
    ∑ q ∈ Finset.range 128, W4.E q * v' q ≠ h := fun hp' =>
  hne (by rw [bits_of_pack hb' hp' ⟨j, hj⟩, bits_of_pack hb hp ⟨j, hj⟩])

end N4s
end FR
