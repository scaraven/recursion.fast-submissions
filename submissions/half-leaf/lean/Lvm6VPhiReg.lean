-- New for lvm6 (WP-PHIV): the typed phase's region claims (`com`, `ks`, `σ`) in factored form. A region claim's
-- weight is `Σ_{y in the regions} eq(r, y)·eq(X, w(y))`, a plain sum over `2^19` (`com`), `2^18` (`ks`) or `2^11`
-- (`σ`) words per evaluation. When the map `w` is a shift on each region (`regAffB`, a start-up check) and the
-- region and its image are aligned, the sum is `eq(r_hi)·eq(X_hi)·Σ_{i<2^l} eq(r_lo, i)·eq(X_lo, i)`, the last
-- factor in closed form (`wPre`): about `3l` products.
import Lvm6VPhiR3

/-!
# Factored region claims

* `regTermF`, `regSumF`: a region's weight in factored form (the plain sum when the alignment fails).
* `regAffB Ti s w`: on every region of source `s`, `w (base + i) = w base + i` (start-up, untimed).
* **`regSumF_eq`**: under `regAffB`, `regSumF = regSumW … (eq(r, y)·eq(X, w y))` at every point `X`.
* `regClaimFF`, `typedClaimsFX`, `fTypedProgEX`, `fTypedPhase6X`; **`tw_typedPhase6X`**: the typed phase's twin with the
  factored claims, under the three checks and any evaluator with `PhiOk`.
-/

set_option autoImplicit false

namespace Lvm6.V

open RecursionFast LeanVM.Parameters Lvm.FS Lvm.Replay Lvm Lvm.E2V Lvm.Typed Lvm.Loop
open LeanVM.Protocol.Compile hiding Proof Bytes Word

open Lvm6.Ty (TInst6 TyInst6 typedPhase6 regSumW)

/-- A region's weight `Σ_{i<2^l} eq(r, base + i)·eq(X, wb + i)`: factored when the region and its image are
aligned and the points long enough, else the plain sum (`w` the map). -/
def regTermF (r X : List FE2) (w : ℕ → ℕ) (reg : YReg) : FE2 :=
  let l := reg.log
  let wb := w reg.base
  if l ≤ r.length ∧ l ≤ X.length ∧ reg.base % 2 ^ l = 0 ∧ wb % 2 ^ l = 0 then
    eqAtF (r.drop l) (reg.base / 2 ^ l) * eqAtF (X.drop l) (wb / 2 ^ l) * (wPre (r.take l) (X.take l) (2 ^ l)).1
  else ((List.range (2 ^ l)).map fun i => eqAtF r (reg.base + i) * eqAtF X (w (reg.base + i))).sum

/-- **The factored region weight** of source `s`. -/
def regSumF (Ti : TInst6) (s : YSrc) (w : ℕ → ℕ) (r X : List FE2) : FE2 :=
  (Ti.lay.yregs.map fun reg => if (reg.src == s) = true then regTermF r X w reg else 0).sum

/-- **The start-up check**: `w` is a shift on every region of source `s`. -/
def regAffB (Ti : TInst6) (s : YSrc) (w : ℕ → ℕ) : Bool :=
  Ti.lay.yregs.all fun reg => reg.src != s || (List.range (2 ^ reg.log)).all fun i => w (reg.base + i) == w reg.base + i

theorem regTermF_eq (r X : List FE2) (w : ℕ → ℕ) (reg : YReg)
    (hw : ∀ i < 2 ^ reg.log, w (reg.base + i) = w reg.base + i) :
    regTermF r X w reg = ((List.range (2 ^ reg.log)).map fun i => eqAtF r (reg.base + i) * eqAtF X (w (reg.base + i))).sum := by
  unfold regTermF
  simp only
  split
  · rename_i h
    obtain ⟨hr, hX, hb, hwb⟩ := h
    obtain ⟨q, hq⟩ : 2 ^ reg.log ∣ reg.base := Nat.dvd_of_mod_eq_zero hb
    obtain ⟨q', hq'⟩ : 2 ^ reg.log ∣ w reg.base := Nat.dvd_of_mod_eq_zero hwb
    have hl1 : (r.take reg.log).length = reg.log := by simp [hr]
    have hl2 : (X.take reg.log).length = reg.log := by simp [hX]
    rw [wPre_eq _ _ _ (by rw [hl1, hl2]) (by rw [hl1])]
    simp only
    rw [← List.sum_map_mul_left]
    refine congrArg List.sum (List.map_congr_left fun i hi => ?_)
    have hi' : i < 2 ^ reg.log := List.mem_range.mp hi
    rw [hw i hi', hq', hq, show 2 ^ reg.log * q + i = i + 2 ^ reg.log * q by ring,
      show 2 ^ reg.log * q' + i = i + 2 ^ reg.log * q' by ring, eq_split r _ _ _ hr hi', eq_split X _ _ _ hX hi',
      Nat.mul_div_cancel_left _ (by positivity), Nat.mul_div_cancel_left _ (by positivity)]
    ring
  · rfl

theorem regSumF_eq (Ti : TInst6) (s : YSrc) (w : ℕ → ℕ) (h : regAffB Ti s w = true) (r X : List FE2) :
    regSumF Ti s w r X = regSumW Ti (fun s' => s' == s) fun y => eqAtF r y * eqAtF X (w y) := by
  unfold regSumF regSumW
  simp only [regAffB, List.all_eq_true, Bool.or_eq_true, bne_iff_ne, ne_eq, List.mem_range, beq_iff_eq] at h
  refine congrArg List.sum (List.map_congr_left fun reg hreg => ?_)
  split
  · rename_i hs
    have hs' : reg.src = s := by simpa using hs
    rcases h reg hreg with h1 | h1
    · exact absurd hs' h1
    · exact regTermF_eq r X w reg h1
  · rfl

/-- A region claim with the factored weight. -/
def regClaimFF (Ti : TInst6) (s : YSrc) (w : ℕ → ℕ) (r : List FE2) (v : FE2) : FClaim :=
  ⟨fun X => regSumF Ti s w r X, v⟩

theorem regClaimFF_eq (Ti : TInst6) (s : YSrc) (w : ℕ → ℕ) (h : regAffB Ti s w = true) (r : List FE2) (v : FE2) :
    regClaimFF Ti s w r v = regClaimF Ti s w r v := by
  unfold regClaimFF regClaimF
  congr 1
  funext X
  exact regSumF_eq Ti s w h r X

/-- The three region checks of an instance. -/
def regsOkB (Ti : TInst6) : Bool :=
  regAffB Ti .com Ti.comW && regAffB Ti .ks Ti.ksW && regAffB Ti .sigma Ti.sigmaW

/-- The typed claims with the factored region claims. -/
def typedClaimsFX (Ti : TInst6) (ry rv rr : List FE2) (vR : FE2) (cl : List FClaim) : List FClaim × List FClaim :=
  ([pointRecF rr vR, regClaimFF Ti .sigma Ti.sigmaW ry (rv.getD 2 0)],
    [regClaimFF Ti .com Ti.comW ry (rv.getD 0 0), regClaimFF Ti .ks Ti.ksW ry (rv.getD 3 0)] ++ cl)

theorem typedClaimsFX_eq (Ti : TInst6) (h : regsOkB Ti = true) : typedClaimsFX Ti = typedClaimsF Ti := by
  simp only [regsOkB, Bool.and_eq_true] at h
  obtain ⟨⟨hc, hk⟩, hs⟩ := h
  funext ry rv rr vR cl
  simp only [typedClaimsFX, typedClaimsF, regClaimFF_eq Ti _ _ hc, regClaimFF_eq Ti _ _ hk, regClaimFF_eq Ti _ _ hs]

/-- `fTypedProgE` with the factored claims. -/
def fTypedProgEX (Ti : TInst6) (L : Lvm.M3.Lay) (pw : ℕ → FK) (tab : List FE2 → FE2) (accP : List FE2)
    (accY : FE2) : VF (List FClaim × List FClaim) :=
  VF.bind fZero fun z => VF.bind (fWire Ti pw z.2) fun w => VF.bind (fRelay Ti w.1 (w.2.2.getD 1 0)) fun r =>
  VF.bind (fAcc tab accY accP (z.1 ++ w.1) w.2.1) fun _ =>
  VF.bind (fMiniBus6 L Ti.mbT Lvm6.Mb.miniDepth) fun cl => VF.pure (typedClaimsFX Ti w.1 w.2.2 r.1 r.2 cl)

/-- **The fast typed phase with the factored region claims.** -/
def fTypedPhase6X (sh : Lvm6.Shape) (i : TyInst6) (tab : List FE2 → FE2) : VF (List FClaim) :=
  if sh.M = Lvm6.Ty.L6.nuMain then
    VF.bind (fTypedProgEX i.Ti Lvm6.Ty.L6 i.pw tab (i.acc.1.map FE2.ofE2) (FE2.ofE2 i.acc.2)) fun out =>
      VF.pure (out.1.map recClaimF ++ out.2)
  else fun _ _ => none

theorem fTypedPhase6X_eq (sh : Lvm6.Shape) (i : TyInst6) (h : regsOkB i.Ti = true) (tab : List FE2 → FE2) :
    fTypedPhase6X sh i tab = fTypedPhase6 sh i tab := by
  unfold fTypedPhase6X fTypedPhase6 fTypedProgEX fTypedProgE
  rw [typedClaimsFX_eq i.Ti h]

/-- **The typed phase's twin with the factored region claims**, any evaluator with `PhiOk`. -/
theorem tw_typedPhase6X (sh : Lvm6.Shape) (i : TyInst6) (hlay : Lvm6.QD.TyLayOk i.Ti) (h : regsOkB i.Ti = true)
    {tab : List FE2 → FE2} (htab : PhiOk tab i.Ti.Q i.Ti.lay) :
    TwinF (List.map FClaim.dec) (typedPhase6 sh i) (fTypedPhase6X sh i tab) := by
  rw [fTypedPhase6X_eq sh i h]
  exact tw_typedPhase6 sh i hlay htab

end Lvm6.V
