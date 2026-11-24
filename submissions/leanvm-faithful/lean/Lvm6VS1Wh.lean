-- New for lvm6 (VS1): the opening's normalised vanishing table `nwF` without list indexing (`nwFH = nwF`), and the
-- fast opening over it (`fWhir18H = fWhir18`).
import Lvm6VTwO2

/-!
# VS1: the opening's vanishing table without list indexing

`nwF a` builds `[Ŵ_0(a), …, Ŵ_19(a)]` by `List.ofFn` with two `List.getD i` per entry (a walk of `i` cells each).
The opening calls it once per query position of every level (`glueF`'s `colLF` and `valAtF`'s `highEvalF`). `nwFH`
zips the two lists instead.

* **`nwFH`**, **`nwFH_eq : nwFH = nwF`**;
* `colGo` (`colGo_eq`: `colLF` without the nested closures and `List.getD`);
* `valAtFH`, `valsMidFH`, `glueFH`, `fMidH` (the level twins over `nwFH` and `colGo`, each equal to its original);
* **`fWhir18H`**, **`fWhir18H_eq : fWhir18H = fWhir18`**.
-/

set_option autoImplicit false

namespace Lvm6.V

open RecursionFast LeanVM.Parameters Lvm.FS Lvm.Replay Lvm Lvm.E2V

/-- **`nwF` by a zip**: `W_i(a) · W_i(e_i)⁻¹` for `i < 20`. -/
def nwFH (a : FK) : List FK := List.zipWith (· * ·) (vanL rootsN a) invRootsN

theorem nwFH_eq : nwFH = nwF := by
  funext a
  have hl : rootsN.length = 20 := (rootsUpTo_spec 20).1
  have hv : (vanL rootsN a).length = 21 := by rw [vanL_length, hl]
  have hi : invRootsN.length = 20 := by rw [invRootsN, List.length_map, hl]
  apply List.ext_getElem
  · simp only [nwFH, nwF, List.length_zipWith, hv, hi, List.length_ofFn]
    rfl
  · intro i h1 h2
    simp only [nwFH, List.length_zipWith, hv, hi] at h1
    simp only [nwFH, nwF, List.getElem_zipWith, List.getElem_ofFn, List.getD_eq_getElem?_getD,
      List.getElem?_eq_getElem (show i < (vanL rootsN a).length by omega),
      List.getElem?_eq_getElem (show i < invRootsN.length by omega), Option.getD_some]

/-- `valAtF` over `nwFH`. -/
def valAtFH (κ ℓ : ℕ) (rs : List RndF) (hi : List FE2) (p : ℕ) (lane : ℕ → FE2) : FE2 :=
  let a := kOfNat p
  foldRowF (FE2.ofK a) ℓ rs lane 0 - highEvalF κ ℓ hi (nwFH a)

theorem valAtFH_eq : valAtFH = valAtF := by
  funext κ ℓ rs hi p lane
  simp only [valAtFH, valAtF, nwFH_eq]

/-- `valsMidF` over `valAtFH`. -/
def valsMidFH (z : Bool) (κ ℓ h c t : ℕ) (rs : List RndF) (π : ByteArray) (hi qv : List FE2) (r : RowsF) :
    List FE2 :=
  List.ofFn fun k : Fin t => valAtFH κ ℓ rs hi (posNF h c qv k) (laneF z π r r.os[(k : ℕ)]?)

theorem valsMidFH_eq : valsMidFH = valsMidF := by
  funext z κ ℓ h c t rs π hi qv r
  simp only [valsMidFH, valsMidF, valAtFH_eq]

/-- `colLF κ W y` walking `W` and `y` together: `prodLF` reaches factor `i` through `i` nested closures and reads
`W.getD i` from the head, both quadratic in `κ`. -/
def colGo : ℕ → List FK → List FE2 → FE2
  | 0, _, _ => 1
  | n + 1, W, y => ((1 - y.headD 0) + FE2.mulK (y.headD 0) (W.headD 0)) * colGo n W.tail y.tail

theorem colGo_eq : ∀ (n : ℕ) (W : List FK) (y : List FE2), colGo n W y = colLF n W y
  | 0, _, _ => rfl
  | n + 1, W, y => by
    rw [colGo, colGo_eq n W.tail y.tail]
    unfold colLF
    rw [prodLF]
    congr 1
    · cases W <;> rfl
    · congr 1
      funext i X
      cases W <;> rfl

/-- `glueF` over `nwFH` and `colGo`. -/
def glueFH (ko t : ℕ) (φ : List FE2 → FE2) (zv : List FE2) (lam : FE2) (pk : ℕ → ℕ) (y : List FE2) : FE2 :=
  φ y + lam * eqLF (ko + 1) zv y + (psum lam (fun k => colGo (ko + 1) (nwFH (kOfNat (pk k))) y) t).1

theorem glueFH_eq : glueFH = glueF := by
  funext ko t φ zv lam pk y
  simp only [glueFH, glueF, nwFH_eq, colGo_eq]

/-- `fMid` over `valsMidFH` and `glueFH`. -/
def fMidH (i ko ℓ h h' kq t c gQ : ℕ) (z : Bool) (frest : (List FE2 → FE2) → FE2 → VF Bool)
    (φ : List FE2 → FE2) (σ : FE2) : VF Bool :=
  VF.bind (fRounds 10 ℓ) fun rs =>
  VF.bind (fTail ℓ h' 32 i 18 ko gQ kq (posListF h c t) (valsMidFH z (ko + 1) ℓ h c t rs)) fun o =>
  frest (glueFH ko t (fun y => φ (alphasF ℓ rs ++ y)) o.zv (o.qv.getD (kq + 1) 0) (posNF h c o.qv))
    (gluedCF (foldsCF ℓ rs σ) o.y (o.qv.getD (kq + 1) 0) t o.c)

theorem fMidH_eq : fMidH = fMid := by
  funext i ko ℓ h h' kq t c gQ z frest φ σ
  simp only [fMidH, fMid, valsMidFH_eq, glueFH_eq]

/-- **`fWhir18` over `fMidH`.** -/
def fWhir18H (f : List FE2 → FE2) (v : FE2) : VF Bool :=
  fMidH 0 18 6 21 20 18 110 6 19 true
    (fMidH 1 14 4 20 19 7 45 6 17 false
      (fMidH 2 10 4 19 18 4 28 6 18 false (fMidH 3 6 4 18 17 2 21 7 17 false fFin18)))
    (fun y => f ((padF25 y).drop 6 ++ (padF25 y).take 6)) v

theorem fWhir18H_eq : fWhir18H = fWhir18 := by
  funext f v
  simp only [fWhir18H, fWhir18, fMidH_eq]

end Lvm6.V
