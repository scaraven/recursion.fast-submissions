-- New for lvm6 (WP W1). The deployed opening of FORMAT6 v2.2.1 §6.6 at `P18` as a ladder of the
-- `Lvm6WhirLadder` calculus: four levels with a next one (`midE`: `tailE2`, F1's group rule
-- `chalE2`, the lanes `valsE`/`wordE`, the glue `wGlueE`, the admitted weights `wokE`) and the
-- final level (`finE2`, `fvE`, the tail sumcheck `chkE`), with PARAM's numbers (`Lvm6Params`); its
-- hypotheses `LadOK` are proved (`lad18_ok`), so the opening rejects from the descent invariant at
-- level 0's start agreement (`whirSpec18`).
import Lvm6WhirWok
import Lvm6WhirNum2
import Lvm6WhirLanes

/-!
# The deployed opening at `P18` (W1)

* `midE`, `finE`: a deployed level's data; `midOK_E`, `finOK_E`: its hypotheses from PARAM's numbers.
* `lad18`: levels `(κ, R, k) = (19,2,6), (15,5,4), (11,8,4), (7,11,4), (3,14,4)`, positions
  `2^21 … 2^17`, `t = 110, 45, 28, 21, 18` openings from `19, 8, 5, 3, 3` draws, grinds fold 10, OOD
  18, query `19, 17, 18, 17, 13`, tail 2. **`lad18_ok`**: `LadOK chalE2 εI lad18 (Aend₀ − 6)`.
* `w₀ cl`: the batched claim's weight (lane bits first, as `Φ(y) = cl(y[6..] ++ y[..6])`);
  `whirP18 cl`; **`whirSpec18`**: from the descent invariant at `1,053,294`, rejection at `εI`.
-/

namespace Lvm6.Whir

open LeanVM.Parameters LeanVM.Protocol.Compile LeanVM.Protocol.Whir.Sound LeanVM.Protocol.Whir
  LeanVM.Protocol.Whir.AffineCombiner
open scoped ENNReal

/-- PARAM's per-group escape cap. -/
noncomputable abbrev εW : ℝ≥0∞ := 7 * (2 : ℝ≥0∞)⁻¹ ^ 131

/-! ## A deployed level and its hypotheses -/

/-- **A deployed level with a next one.** -/
noncomputable def midE (i ko ℓ h κ' ℓ' h' kq t c gQ A' : ℕ) (z : Bool) (hκ : 0 + ℓ' + κ' = ko + 1)
    (hko : ko + 1 < 64) (hℓ : 1 ≤ ℓ) (hℓ' : ℓ ≤ 64) (hh : h ≤ 64) (hh' : h' ≤ 64) (hc : 0 < c)
    (hch : c * h ≤ 128) (ht : t ≤ (kq + 1) * c) : MidLv E2 WtE (2 ^ h) ℓ (2 ^ h') ℓ' where
  L := tailE2 ko ℓ h κ' ℓ' h' kq t c hκ hko hℓ hℓ' hh hh' hc hch ht
  g := 10
  gO := 18
  gQ := gQ
  ht := h'
  wd := 32
  i := i
  t₀ := 1
  par := parP i
  A' := A'
  vals := valsE z h ℓ (ko + 1) hh
  wGlue := wGlueE κ' ℓ' ko t h
  word := wordE z i (0 + ℓ) h
  WOK := wokE (ko + 1) ℓ

/-- **The final level.** -/
noncomputable def finE (κ ℓ h kq t c gq : ℕ) (hκ : κ < 64) (hℓ : 1 ≤ ℓ) (hℓ' : ℓ ≤ 64)
    (hh : h ≤ 64) (hc : 0 < c) (hch : c * h ≤ 128) (ht : t ≤ (kq + 1) * c) :
    FinLv E2 WtE (2 ^ h) ℓ where
  Fv := finE2 κ ℓ h kq t c hκ hℓ hℓ' hh hc hch ht
  g := 10
  gq := gq
  i := 4
  t₀ := 1
  par := parP 4
  fv := fvE false h ℓ hh
  chk := chkE 2 κ
  word := wordE false 4 (0 + ℓ) h
  WOK := wokE κ ℓ

theorem εW_lt_one : εW < 1 := εI_lt_one

/-- **A deployed level's hypotheses** from PARAM's numbers. -/
theorem midOK_E (i ko ℓ h κ' ℓ' h' kq t c gQ A' : ℕ) (z : Bool) (hκ : 0 + ℓ' + κ' = ko + 1)
    (hko : ko + 1 < 64) (hℓ : 1 ≤ ℓ) (hℓ' : ℓ ≤ 64) (hh : h ≤ 64) (hh' : h' ≤ 64) (hc : 0 < c)
    (hch : c * h ≤ 128) (ht : t ≤ (kq + 1) * c) (hi5 : i < 5) (hgQ : gQ ≤ 64)
    (hN : roundN (lvP i).1 (lvP i).2.1 = 2 ^ h)
    (hD : roundD (lvP i).1 (lvP i).2.2.1 = 2 ^ (ko + 1) - 1 + ℓ) (hk : (lvP i).2.2.1 = ℓ)
    (hgap : 2 ^ h' * (2 ^ κ' - 1 + ℓ') < A' * A')
    (hadm : Lvm6.Params.admits ((jl (2 ^ h') A' (2 ^ κ' - 1 + ℓ')).choose 2 * (ko + 1)) 18 = true)
    (hq : 8 * ((lvP i).2.2.2.1 - 1) ^ t * 2 ^ 128 +
      8 * (t + 1) * jl (2 ^ h') A' (2 ^ κ' - 1 + ℓ') * (2 ^ h) ^ t ≤ 7 * 2 ^ gQ * (2 ^ h) ^ t) :
    MidOK chalE2 εW (midE i ko ℓ h κ' ℓ' h' kq t c gQ A' z hκ hko hℓ hℓ' hh hh' hc hch ht)
      ((lvP i).2.2.2.1 - ℓ) (i + 1) (domE h' hh') (2 ^ κ' - 1 + ℓ') (wokE κ' ℓ') := by
  obtain ⟨h1, h2, h3, h4, h5, h6⟩ := levelRounds_ok (F := E2) card_E2 hi5
  rw [hN, hD, hk] at h1
  rw [hk] at h2 h3 h4 h5 h6
  have hA : aOut (fun s ↦ (parP i s).A) ((lvP i).2.2.2.1 - ℓ) 1 ℓ = (lvP i).2.2.2.1 := h6
  have heQ := eQry_tailE2_le (hκ := hκ) (hko := hko) (hℓ := hℓ) (hℓ' := hℓ') (hh := hh)
    (hh' := hh') (hc := hc) (hch := hch) (ht := ht) gQ (jl (2 ^ h') A' (2 ^ κ' - 1 + ℓ'))
    (lvP i).2.2.2.1 hq
  have heO := eOod_tailE2_le (hκ := hκ) (hko := hko) (hℓ := hℓ) (hℓ' := hℓ') (hh := hh)
    (hh' := hh') (hc := hc) (hch := hch) (ht := ht) 18 (jl (2 ^ h') A' (2 ^ κ' - 1 + ℓ')) hadm
  exact {
    hg := by show 10 ≤ 64; norm_num
    hgO := by show 18 ≤ 64; norm_num
    hgQ := hgQ
    hpar := h1
    he := h2
    heT := h3
    hchain := h4
    ha := h5
    hstab := fun cs c hl ↦ wordE_append z i (0 + ℓ) h cs c hl
    hread := fun rs h₀ _ ps rows hans hi ↦ hread_valsE z i h ℓ (ko + 1) hh rs h₀ ps rows hans hi
    hgap := hgap
    heO := heO.trans_lt εW_lt_one
    heOT := heO
    heQ := by dsimp only [midE]; rw [hA]; exact heQ.trans_lt εW_lt_one
    heQT := by dsimp only [midE]; rw [hA]; exact heQ
    hi' := rfl
    hdom' := rfl
    hd' := rfl
    hWH := fun w hw rs hi ↦ hWH_E hko.le w hw rs hi
    hglue := fun w hw rs o ↦ hglue_E hκ w hw rs o
    den_wGlue := fun w hw rs o ↦ den_wGlueE ko ℓ h κ' ℓ' h' kq t c hκ hko hℓ hℓ' hh hh' hc hch ht
      (wFolds WtE ℓ rs w) (by rw [wFolds_fst]; exact hw.1) o }

/-- **The final level's hypotheses** from PARAM's numbers. -/
theorem finOK_E (κ ℓ h kq t c gq : ℕ) (hκ : κ < 64) (hℓ : 1 ≤ ℓ) (hℓ' : ℓ ≤ 64) (hh : h ≤ 64)
    (hc : 0 < c) (hch : c * h ≤ 128) (ht : t ≤ (kq + 1) * c) (hgq : gq ≤ 64)
    (hN : roundN (lvP 4).1 (lvP 4).2.1 = 2 ^ h)
    (hD : roundD (lvP 4).1 (lvP 4).2.2.1 = 2 ^ κ - 1 + ℓ) (hk : (lvP 4).2.2.1 = ℓ)
    (hq : 8 * ((lvP 4).2.2.2.1 - 1) ^ t * 2 ^ 128 + 8 * (t + 1) * 0 * (2 ^ h) ^ t ≤
      7 * 2 ^ gq * (2 ^ h) ^ t) :
    FinOK chalE2 εW (finE κ ℓ h kq t c gq hκ hℓ hℓ' hh hc hch ht) ((lvP 4).2.2.2.1 - ℓ) := by
  obtain ⟨h1, h2, h3, h4, h5, h6⟩ := levelRounds_ok (F := E2) card_E2 (i := 4) (by norm_num)
  rw [hN, hD, hk] at h1
  rw [hk] at h2 h3 h4 h5 h6
  have hA : aOut (fun s ↦ (parP 4 s).A) ((lvP 4).2.2.2.1 - ℓ) 1 ℓ = (lvP 4).2.2.2.1 := h6
  have heF := eFin_finE2_le (hκ := hκ) (hℓ := hℓ) (hℓ' := hℓ') (hh := hh) (hc := hc) (hch := hch)
    (ht := ht) gq (lvP 4).2.2.2.1 hq
  exact {
    hg := by show 10 ≤ 64; norm_num
    hgq := hgq
    hpar := h1
    he := h2
    heT := h3
    hchain := h4
    ha := h5
    hread := fun h₀ _ rs ps rows hans ↦ hread_fvE false 4 h ℓ hh rs h₀ ps rows hans
    hchk := fun w σ hw rs s ↦ hchk_E (le_of_lt hκ) (by norm_num) (eSum_le_εI.trans_lt εW_lt_one)
      eSum_le_εI w hw σ rs s
    heF := by dsimp only [finE]; rw [hA]; exact heF.trans_lt εW_lt_one
    heFT := by dsimp only [finE]; rw [hA]; exact heF }

/-! ## The ladder at `P18` -/

/-- Level 4 (final). -/
noncomputable def fin18 : FinLv E2 WtE (2 ^ 17) 4 :=
  finE 3 4 17 2 18 7 13 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num)

/-- Level 3. -/
noncomputable def mid3 : MidLv E2 WtE (2 ^ 18) 4 (2 ^ 17) 4 :=
  midE 3 6 4 18 3 4 17 2 21 7 17 (1548 - 4) false (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

/-- Level 2. -/
noncomputable def mid2 : MidLv E2 WtE (2 ^ 19) 4 (2 ^ 18) 4 :=
  midE 2 10 4 19 7 4 18 4 28 6 18 (6525 - 4) false (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

/-- Level 1. -/
noncomputable def mid1 : MidLv E2 WtE (2 ^ 20) 4 (2 ^ 19) 4 :=
  midE 1 14 4 20 11 4 19 7 45 6 17 (34227 - 4) false (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

/-- Level 0. -/
noncomputable def mid0 : MidLv E2 WtE (2 ^ 21) 6 (2 ^ 20) 4 :=
  midE 0 18 6 21 15 4 20 18 110 6 19 (188173 - 4) true (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

/-- **The ladder of `P18`.** -/
noncomputable def lad18 : Lad E2 WtE (2 ^ 21) 6 :=
  .mid mid0 (.mid mid1 (.mid mid2 (.mid mid3 (.fin fin18))))

/-- **The ladder's hypotheses hold at `P18`** (PARAM's row, `Lvm6Params`), from level 0's start
agreement `Aend₀ − 6 = 1,053,294`. -/
theorem lad18_ok : LadOK chalE2 εW lad18 (1053300 - 6) := by
  refine ⟨midOK_E 0 18 6 21 15 4 20 18 110 6 19 (188173 - 4) true _ _ _ _ _ _ _ _ _ (by norm_num)
    (by norm_num) (by decide) (by decide) (by decide) (by decide) (by decide +kernel)
    (by decide +kernel), ?_⟩
  refine ⟨midOK_E 1 14 4 20 11 4 19 7 45 6 17 (34227 - 4) false _ _ _ _ _ _ _ _ _ (by norm_num)
    (by norm_num) (by decide) (by decide) (by decide) (by decide) (by decide +kernel)
    (by decide +kernel), ?_⟩
  refine ⟨midOK_E 2 10 4 19 7 4 18 4 28 6 18 (6525 - 4) false _ _ _ _ _ _ _ _ _ (by norm_num)
    (by norm_num) (by decide) (by decide) (by decide) (by decide) (by decide +kernel)
    (by decide +kernel), ?_⟩
  refine ⟨midOK_E 3 6 4 18 3 4 17 2 21 7 17 (1548 - 4) false _ _ _ _ _ _ _ _ _ (by norm_num)
    (by norm_num) (by decide) (by decide) (by decide) (by decide) (by decide +kernel)
    (by decide +kernel), ?_⟩
  exact finOK_E 3 4 17 2 18 7 13 _ _ _ _ _ _ _ (by norm_num) (by decide) (by decide) (by decide)
    (by decide +kernel)

/-! ## The opening -/

/-- The first 25 entries of a list, padded with zeros. -/
def pad25 (y : List E2) : List E2 := List.ofFn fun i : Fin 25 ↦ y.getD i 0

/-- **The batched claim's weight** at level 0: `Φ(y) = cl(y[6..25) ++ y[..6))` (the lane bits are the
stack index's top six bits, FORMAT6 §6.5 placement), read on the first 25 entries. -/
noncomputable def w₀ (cl : (List E2 → E2) × E2) : WtE.Wt (0 + 6) :=
  (19, fun y ↦ cl.1 ((pad25 y).drop 6 ++ (pad25 y).take 6))

/-- **The deployed opening program** of a batched claim (FORMAT6 §6.6 at `P18`). -/
noncomputable def whirP18 (cl : (List E2 → E2) × E2) : VerifierProgram Bool :=
  ladP chalE2 lad18 (w₀ cl) cl.2

/-- **The deployed opening rejects from the descent invariant** at level 0's start agreement, for a
claim whose weight is affine in each of its 25 variables (in the rotated order of `w₀`). -/
noncomputable def whirSpec18 (cl : (List E2 → E2) × E2)
    (hma : MA 25 (w₀ cl).2) :
    Spec (whirP18 cl) (fun h ↦ (commits h).length = 1 ∧
      TViol (domE 21 (by norm_num)) (wordE true 0 (0 + 6) 21 (commits h)) (WtE.den (w₀ cl)) cl.2
        (1053300 - 6) (2 ^ 19 - 1 + 6) (fun _ ↦ True)) (fun b _ ↦ b = false) εW 0 0 :=
  ladSpec lad18 (1053300 - 6) lad18_ok (w₀ cl) cl.2 ⟨rfl, hma⟩

end Lvm6.Whir
