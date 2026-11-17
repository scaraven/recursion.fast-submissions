-- New for lvm2 (CR-V, roll 7 SH2-Z; CR-DES §1.5): V_S's native small shape. The `FE` side of
-- `LvmShape` (its definitions, moved here unchanged so that V_S can run them; `zStarF` computed from
-- Keccak-f directly) and V_S's new steps: the shape bit, the wire phase that also returns the ring
-- coefficients, the tail values per claim kind, the small `C_main` opening.
import LvmDecideTape
import LvmKeccakSpec

/-!
# V_S's small shape (native)

* **The `FE` side of `LvmShape`'s interface** (definitions unchanged, moved below V_S): `regions`,
  `relocF`, `onStackZF`, `meets`, `onStackZB`, `InStack`, `tailDF`, `tailPtF`, `ringTailF`,
  `onStackZsF`. `zStarF l` is lane `l` of `Keccak-f(0)` (computed once, `zStarsF`); `LvmShape` proves
  it is `FE.ofK (ofBF64 (zStar l))`.
* **`smallP p pub`**: `P20`'s record and `n ≤ 2^18` (the header's `n`, bound by the seed query).
* **`ringSwitchC`**, **`dWireC`**: `ringSwitch` and `dWire` that also return the Frobenius
  coefficients (`ringSwitch_eqC`, `dWire_eqC`: the old steps are their first components).
* **`tapeTails`**: the tail values of the tape's claims in closed form (`tailDF`, `ringTailN`, `0`);
  **`dClaimsZ`**: `dClaims` with a tail value per claim (`0` for every claim off `D`);
  **`dOpenZ`**: `C_main`'s claims through `onStackZsF (smallP p pub)`.
-/

set_option autoImplicit false

namespace Lvm.Shape

open Lvm DM

/-! ## The `FE` side of `LvmShape` -/

/-- The small logical table's variables. -/
abbrev sLog : ℕ := CMain.nu20s

/-- The relocated regions `(k, ob, os)`: `2^k` words at big word `ob`, small logical word `os` (both
`2^k`-aligned); they cover the small logical table. lvm2 roll 8 (B1, physical ν = 23, logical ν = 22): `D_l`'s live
rows and the three `2^20` blocks above `D` (`TypedV.regionsN 23`). -/
def regions : List (ℕ × ℕ × ℕ) :=
  ((List.range 4).map fun l ↦ (18, l * 2 ^ 20, l * 2 ^ 18)) ++
    ((List.range (2 ^ (CMain.nu20 - 21) - 1)).map fun j ↦ (20, (4 + j) * 2 ^ 20, (1 + j) * 2 ^ 20))

/-- The 25 lanes of `Keccak-f(0)` over `FE` (a closed term: computed once). -/
def zStarsF : Array FE :=
  (LeanVM.Semantics.keccakF1600 (Vector.replicate 25 0)).toArray.map fun w ↦ FE.ofK ⟨w⟩

/-- `z*_l` over `FE`: lane `l` of `Keccak-f(0)`. -/
def zStarF (l : ℕ) : FE := zStarsF.getD l 0

/-- `relocE` over `FE`. -/
def relocF (x : List FE) (r : ℕ × ℕ × ℕ) : List FE :=
  (x.tail ++ List.replicate sLog 0).take r.1 ++ Lvm.selectorPoint (r.2.1 >>> r.1) (CMain.nu20 - r.1)

/-- **`onStackZ` over `FE`** on a native big-stack claim, its tail value `t` given. -/
def onStackZF (c : Lvm.StackClaim) (t : FE) : Lvm.StackClaim :=
  (fun x ↦ (1 - x.headD 0) * (regions.map fun r ↦
      (⟨r.1, r.2.2⟩ : Lvm.Placement).eqAbove x.tail * c.1 (relocF x r)).sum,
    c.2 - t)

/-- A block meets a region (their word ranges intersect). -/
def meets (b : Lvm.Placement) (r : ℕ × ℕ × ℕ) : Bool :=
  decide (b.index < r.2.1 + 2 ^ r.1 ∧ r.2.1 < b.index + 2 ^ b.variableCount)

/-- **V_S's small claim of a block claim**: `onStackZF` over the regions the block meets only. -/
def onStackZB (c : Lvm.BlockClaim) (t : FE) : Lvm.StackClaim :=
  (fun x ↦ (1 - x.headD 0) * ((regions.filter (meets c.block)).map fun r ↦
      (⟨r.1, r.2.2⟩ : Lvm.Placement).eqAbove x.tail * c.onStack.1 (relocF x r)).sum,
    c.value - t)

/-- An aligned block inside `C_main`'s `2^ν` words. -/
def InStack (b : Lvm.Placement) : Prop :=
  b.variableCount ≤ CMain.nu20 ∧ b.index % 2 ^ b.variableCount = 0 ∧ b.index < 2 ^ CMain.nu20

/-- A `D` point claim's tail at `r ‖ sel(l)` (`r` the 20 row coordinates). -/
def tailDF (r : List FE) (l : ℕ) : FE := (1 - (1 - r.getD 18 0) * (1 - r.getD 19 0)) * zStarF l

/-- The tail of one Frobenius term at the point `ρ` (`ν` coordinates: 20 rows, 2 lanes, `ν − 22` block bits; one
at B1's ν = 23). -/
def tailPtF (ρ : List FE) : FE :=
  (1 - (1 - ρ.getD 18 0) * (1 - ρ.getD 19 0)) *
    ((List.range 4).map fun l ↦ Lvm.eqEval ((ρ.drop 20).take 2) (Lvm.selectorPoint l 2) * zStarF l).sum *
    Lvm.eqEval (ρ.drop 22) (Lvm.selectorPoint 0 (CMain.nu20 - 22))

/-- The tape's ring claim's tail: `Σ_k c_k · tailPtF (pt^(2^k))`. -/
def ringTailF (pt cs : List FE) : FE := (cs.zipIdx.map fun e ↦ e.1 * tailPtF (pt.map (· ^ 2 ^ e.2))).sum

/-- V_S's `C_main` claims on its shape's stack: each with its tail value (closed form). -/
def onStackZsF (s : Bool) (cs : List (Lvm.BlockClaim × FE)) : List Lvm.StackClaim :=
  if s then cs.map fun e ↦ onStackZB e.1 e.2 else cs.map (·.1.onStack)

/-! ## V_S's new steps -/

/-- **The shape bit** (CR-DES §1.3): `P20`'s record and `n ≤ 2^18`. -/
def smallP (p : Params) (pub : Pub) : Bool :=
  p.logN == 20 && p.nuMain == CMain.nu20 && decide (pub.n ≤ 2 ^ CMain.smallLogN20)

/-- `ringSwitch` returning the target and the Frobenius coefficients (no closure). -/
def ringSwitchC (s : List FE) : DM (FE × List FE) := do
  let challenges ← samples ringStages
  pure (polyEval (s.map (phiMap · challenges)) gen, ringCoefficients challenges)

/-- `ringSwitch` is `ringSwitchC` with the weight closure. -/
theorem ringSwitch_eqC (point s : List FE) :
    ringSwitch point s =
      ringSwitchC s >>= fun rc ↦ pure (rc.1, fun rPrime ↦ ringWeight point rPrime rc.2) := by
  simp only [ringSwitch, ringSwitchC, bind_assoc, pure_bind]

/-- The ring switch's point of the wire phase (`σ ‖ τ ‖ sel(dSel)`). -/
def wirePt (p : Params) (wo : WireOut) : List FE := wo.sc.1 ++ wo.sl.1 ++ selectorPoint (dSel p) (dSelBits p)

/-- **The wire phase with the ring coefficients** (`dWire`, read for read). -/
def dWireC (p : Params) (pub : Pub) (claim : KeccakClaim) : DM (WireOut × List FE) := do
  let sc ← sumcheck (wireTargetF pub.s pub.n claim) 3 (List.replicate p.logN none)
  let g ← readEs 1
  require (sc.2 == msEvalF claim.point claim.mu sc.1 0 (pub.n - 1) * g.getD 0 0)
  let sl ← sumcheck (g.getD 0 0) 3 [none, none]
  let sv ← readEs kBits
  require (sl.2 == dot (slotWF claim.weights.toArray sl.1) sv)
  let rc ← ringSwitchC sv
  pure (⟨sc, g, sl, sv, (rc.1, fun rPrime ↦ ringWeight (sc.1 ++ sl.1 ++ selectorPoint (dSel p) (dSelBits p))
    rPrime rc.2)⟩, rc.2)

/-- `dWire` is `dWireC`'s first component. -/
theorem dWire_eqC (p : Params) (pub : Pub) (claim : KeccakClaim) :
    dWire p pub claim = dWireC p pub claim >>= fun x ↦ pure x.1 := by
  simp only [dWire, dWireC, ringSwitch_eqC, bind_assoc, pure_bind]

/-- The ring's tail by repeated squaring of the six coordinates `tailPtF` reads (`ringTailN_eq`:
`ringTailF`). -/
def ringTailN (pt cs : List FE) : FE :=
  (cs.foldl (fun (acc : FE × List FE) c ↦
    (acc.1 + c * tailPtF (List.replicate 18 0 ++ acc.2), acc.2.map FE.sq)) (0, pt.drop 18)).1

/-- **The tails of the tape's claims** (`tapeClaims`' order): `tailDF r l` for the four `D` point
claims, the ring claim's `ringTailN`, `0` for the boundary claims. -/
def tapeTails (p : Params) (t : TapeRes) (wo : WireOut) (cs : List FE) (pub : Pub) : List FE :=
  ((List.range dLanes).map fun l ↦ tailDF t.r l) ++ [ringTailN (wirePt p wo) cs] ++ pub.h.map fun _ ↦ 0

/-- Claims with tail `0`. -/
def zeroTails (l : List (Com × BlockClaim)) : List (Com × BlockClaim × FE) := l.map fun e ↦ (e.1, e.2, 0)

/-- **`dClaims` with a tail value per claim.** -/
def dClaimsZ (m : M3) (p : Params) (pub : Pub) (busClaims : List (Com × BlockClaim))
    (evals : List (List FE × List FE))
    (tp : TapeRes) (wo : WireOut) (cs : List FE)
    (rk vks : List FE) (ksClaims : List BlockClaim)
    (kLinkClaims : List (Com × BlockClaim)) : List (Com × BlockClaim × FE) :=
  zeroTails (busClaims ++ m.tableClaims pub evals) ++
    (((tapeClaims p tp wo pub).zip (tapeTails p tp wo cs pub)).map (fun e ↦ (Com.main, e.1, e.2)) ++
      zeroTails (ksClaims.map (.main, ·))) ++
    zeroTails (m.ksOutputClaims rk vks ++ kLinkClaims)

/-- **The openings in both shapes** (phases 8–9): `C_rec`'s as before; `C_main`'s claims through
`onStackZsF s`. -/
def dOpenZ (p : Params) (s : Bool) (claims : List (Com × BlockClaim × FE)) : DM Unit := do
  verifyStackedOpening p.recLevels p.nuRec ((claims.filter (·.1 == .crec)).map (·.2.1.onStack)) false
    p.grind p.recOod
  verifyStackedOpening p.mainLevels p.nuMain (onStackZsF s ((claims.filter (·.1 == .main)).map (·.2)))
    false p.grind p.mainOod

theorem map_zeroTails (l : List (Com × BlockClaim)) :
    (zeroTails l).map (fun e ↦ (e.1, e.2.1)) = l := by
  induction l with
  | nil => rfl
  | cons a l ih => simp only [zeroTails, List.map_cons, List.map_map] at ih ⊢; rw [ih]

theorem length_tapeTails (p : Params) (tp : TapeRes) (wo : WireOut) (cs : List FE) (pub : Pub) :
    (tapeTails p tp wo cs pub).length = (tapeClaims p tp wo pub).length := by
  simp [tapeTails, tapeClaims]

/-- **Without the tails, `dClaimsZ` is V_S's claim list** (`decideProg`'s before roll 7). -/
theorem dClaimsZ_fst (m : M3) (p : Params) (pub : Pub) (busClaims : List (Com × BlockClaim))
    (evals : List (List FE × List FE)) (tp : TapeRes) (wo : WireOut) (cs rk vks : List FE)
    (ksClaims : List BlockClaim) (kl : List (Com × BlockClaim)) :
    (dClaimsZ m p pub busClaims evals tp wo cs rk vks ksClaims kl).map (fun e ↦ (e.1, e.2.1)) =
      busClaims ++ m.tableClaims pub evals ++ (tapeClaims p tp wo pub ++ ksClaims).map (.main, ·) ++
        m.ksOutputClaims rk vks ++ kl := by
  have hz : List.map (fun e ↦ (e.1, e.2.1)) (List.map
      (fun e ↦ ((Com.main, e.1, e.2) : Com × BlockClaim × FE))
        ((tapeClaims p tp wo pub).zip (tapeTails p tp wo cs pub))) =
      (tapeClaims p tp wo pub).map (.main, ·) := by
    have h := List.map_fst_zip (l₁ := tapeClaims p tp wo pub) (l₂ := tapeTails p tp wo cs pub)
      (Nat.le_of_eq (length_tapeTails _ _ _ _ _).symm)
    calc _ = List.map (fun x ↦ (Com.main, x))
          (List.map Prod.fst ((tapeClaims p tp wo pub).zip (tapeTails p tp wo cs pub))) := by
            rw [List.map_map, List.map_map]; rfl
      _ = _ := by rw [h]
  unfold dClaimsZ
  simp only [List.map_append, map_zeroTails, hz, List.append_assoc]

/-- Filtering by the commitment commutes with forgetting the tails. -/
theorem filter_fst (l : List (Com × BlockClaim × FE)) (com : Com) :
    (l.filter (·.1 == com)).map (fun e ↦ (e.1, e.2.1)) =
      (l.map (fun e ↦ (e.1, e.2.1))).filter (·.1 == com) := by
  induction l with
  | nil => rfl
  | cons a l ih =>
    by_cases h : (a.1 == com) = true
    · simp [h, ih]
    · simp [h, ih]

/-- **The big shape's openings are V_S's before roll 7** (`C_main`'s claims on the stack as they are). -/
theorem dOpenZ_false (p : Params) (claims : List (Com × BlockClaim × FE)) :
    dOpenZ p false claims = (do
      let on (com : Com) := ((claims.map (fun e ↦ (e.1, e.2.1))).filter (·.1 == com)).map (·.2.onStack)
      verifyStackedOpening p.recLevels p.nuRec (on .crec) false p.grind p.recOod
      verifyStackedOpening p.mainLevels p.nuMain (on .main) false p.grind p.mainOod) := by
  simp only [dOpenZ, onStackZsF, Bool.false_eq_true, ite_false, ← filter_fst, List.map_map]
  rfl

end Lvm.Shape
