-- New for lvm6 (WP W1). The deployed opening of FORMAT6 §6.6 as a ladder of the `Lvm6WhirLadder`
-- calculus: four levels with a next one (`midEOf`: `tailE2`, F1's group rule `chalE2`, the lanes
-- `valsE`/`wordE`, the glue `wGlueE`, the admitted weights `wokE`) and the final level (`finE2`, `fvE`,
-- the tail sumcheck `chkE`), with PARAM's numbers; its hypotheses `LadOK` are proved, so the opening
-- rejects from the descent invariant at level 0's start agreement (`whirSpecD`).
-- PORT17 W1: the ladder is generic over the shape (`midRow`, `finRow`, `ladAt`, `ladAt_ok`); the
-- deployed ladder is `ladAt P17` (`M = 24`), `P18`'s (`ladP18`, `ladP18_ok`) is a corollary (in `Lvm6P18Park` since INT11).
import Lvm6WhirWok
import Lvm6WhirNum2
import Lvm6WhirLanes
import Lvm6FormatP17

/-!
# The deployed opening (W1)

* `midEOf pl`, `finEOf pl`: a level's data at PARAM's list `pl`; `midOK_EOf`, `finOK_EOf`: its
  hypotheses from PARAM's numbers. `midE`, `finE`: at the deployed list (`Lvm6.Params17.levels`).
* **The rows from the shape**: `midRow sh pl i` (`midE`'s arguments: `ko + 1 = sh.nu (i + 1)`, folds,
  heights, `⌊128/ht⌋` positions a draw and `⌈t/per⌉` draws from `sh.lev`, the query grind, the next
  start agreement `Aend' − ℓ'`), `finRow sh i`; `MidRow.Ok`, `FinRow.Ok`, `RowsOK sh pl`: their side
  conditions and PARAM's numbers, decidable.
* **`ladAt sh pl hr`**: the five-level ladder of a shape; **`ladAt_ok`**: `LadOK chalE2 εI (ladAt …)
  (Aend₀ − ℓ₀)` for a checked PARAM list.
* `ladD = ladAt P17 Params17.levels`: levels `(κ, R, k) = (18,2,6), (14,5,4), (10,8,4), (6,11,4),
  (2,14,4)`, positions `2^20 … 2^16`, `t = 110, 45, 28, 21, 18` openings from `19, 8, 4, 3, 3` draws
  (`6, 6, 7, 7, 8` positions each), grinds fold 10, OOD 18, query `19, 17, 18, 17, 18`, tail 2.
  **`ladD_ok`**: `LadOK chalE2 εI ladD (Aend₀ − 6)`; `midRow_P17`, `finRow_P17`: the rows, written out.
* `P18`: `ladP18`, `ladP18_ok`, `midRow_P18` (the rows of the pre-port `ladD`).
* `w₀ cl`: the batched claim's weight (lane bits first, as `Φ(y) = cl(y[6..] ++ y[..6])`);
  `whirP cl`; **`whirSpecD`**: from the descent invariant at `526,650`, rejection at `εI`.
-/

namespace Lvm6.Whir

open LeanVM.Parameters LeanVM.Protocol.Compile LeanVM.Protocol.Whir.Sound LeanVM.Protocol.Whir
  LeanVM.Protocol.Whir.AffineCombiner
open scoped ENNReal

/-- PARAM's per-group escape cap. -/
noncomputable abbrev εW : ℝ≥0∞ := 7 * (2 : ℝ≥0∞)⁻¹ ^ 131

/-! ## A deployed level and its hypotheses -/

/-- **A deployed level with a next one** (PARAM's list `pl`). -/
noncomputable def midEOf (pl : PLv) (i ko ℓ h κ' ℓ' h' kq t c gQ A' : ℕ) (z : Bool) (hκ : 0 + ℓ' + κ' = ko + 1)
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
  par := parOf pl i
  A' := A'
  vals := valsE z h ℓ (ko + 1) hh
  wGlue := wGlueE κ' ℓ' ko t h
  word := wordE z i (0 + ℓ) h
  WOK := wokE (ko + 1) ℓ

/-- **The final level** (PARAM's list `pl`). -/
noncomputable def finEOf (pl : PLv) (κ ℓ h kq t c gq : ℕ) (hκ : κ < 64) (hℓ : 1 ≤ ℓ) (hℓ' : ℓ ≤ 64)
    (hh : h ≤ 64) (hc : 0 < c) (hch : c * h ≤ 128) (ht : t ≤ (kq + 1) * c) :
    FinLv E2 WtE (2 ^ h) ℓ where
  Fv := finE2 κ ℓ h kq t c hκ hℓ hℓ' hh hc hch ht
  g := 10
  gq := gq
  i := 4
  t₀ := 1
  par := parOf pl 4
  fv := fvE false h ℓ hh
  chk := chkE 2 κ
  word := wordE false 4 (0 + ℓ) h
  WOK := wokE κ ℓ

theorem εW_lt_one : εW < 1 := εI_lt_one

/-- **A deployed level's hypotheses** from PARAM's numbers. -/
theorem midOK_EOf {pl : PLv} (hpl : roundsCheckOf pl = true) (i ko ℓ h κ' ℓ' h' kq t c gQ A' : ℕ)
    (z : Bool) (hκ : 0 + ℓ' + κ' = ko + 1)
    (hko : ko + 1 < 64) (hℓ : 1 ≤ ℓ) (hℓ' : ℓ ≤ 64) (hh : h ≤ 64) (hh' : h' ≤ 64) (hc : 0 < c)
    (hch : c * h ≤ 128) (ht : t ≤ (kq + 1) * c) (hi5 : i < pl.length) (hgQ : gQ ≤ 64)
    (hN : roundN (lvOf pl i).1 (lvOf pl i).2.1 = 2 ^ h)
    (hD : roundD (lvOf pl i).1 (lvOf pl i).2.2.1 = 2 ^ (ko + 1) - 1 + ℓ) (hk : (lvOf pl i).2.2.1 = ℓ)
    (hgap : 2 ^ h' * (2 ^ κ' - 1 + ℓ') < A' * A')
    (hadm : Lvm6.Params.admits ((jl (2 ^ h') A' (2 ^ κ' - 1 + ℓ')).choose 2 * (ko + 1)) 18 = true)
    (hq : 8 * ((lvOf pl i).2.2.2.1 - 1) ^ t * 2 ^ 128 +
      8 * (t + 1) * jl (2 ^ h') A' (2 ^ κ' - 1 + ℓ') * (2 ^ h) ^ t ≤ 7 * 2 ^ gQ * (2 ^ h) ^ t) :
    MidOK chalE2 εW (midEOf pl i ko ℓ h κ' ℓ' h' kq t c gQ A' z hκ hko hℓ hℓ' hh hh' hc hch ht)
      ((lvOf pl i).2.2.2.1 - ℓ) (i + 1) (domE h' hh') (2 ^ κ' - 1 + ℓ') (wokE κ' ℓ') := by
  obtain ⟨h1, h2, h3, h4, h5, h6⟩ := levelRounds_okOf (F := E2) card_E2 hpl hi5
  rw [hN, hD, hk] at h1
  rw [hk] at h2 h3 h4 h5 h6
  have hA : aOut (fun s ↦ (parOf pl i s).A) ((lvOf pl i).2.2.2.1 - ℓ) 1 ℓ = (lvOf pl i).2.2.2.1 := h6
  have heQ := eQry_tailE2_le (hκ := hκ) (hko := hko) (hℓ := hℓ) (hℓ' := hℓ') (hh := hh)
    (hh' := hh') (hc := hc) (hch := hch) (ht := ht) gQ (jl (2 ^ h') A' (2 ^ κ' - 1 + ℓ'))
    (lvOf pl i).2.2.2.1 hq
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
    heQ := by dsimp only [midEOf]; rw [hA]; exact heQ.trans_lt εW_lt_one
    heQT := by dsimp only [midEOf]; rw [hA]; exact heQ
    hi' := rfl
    hdom' := rfl
    hd' := rfl
    hWH := fun w hw rs hi ↦ hWH_E hko.le w hw rs hi
    hglue := fun w hw rs o ↦ hglue_E hκ w hw rs o
    den_wGlue := fun w hw rs o ↦ den_wGlueE ko ℓ h κ' ℓ' h' kq t c hκ hko hℓ hℓ' hh hh' hc hch ht
      (wFolds WtE ℓ rs w) (by rw [wFolds_fst]; exact hw.1) o }

/-- **The final level's hypotheses** from PARAM's numbers. -/
theorem finOK_EOf {pl : PLv} (hpl : roundsCheckOf pl = true) (κ ℓ h kq t c gq : ℕ) (hκ : κ < 64)
    (hℓ : 1 ≤ ℓ) (hℓ' : ℓ ≤ 64) (hh : h ≤ 64)
    (hc : 0 < c) (hch : c * h ≤ 128) (ht : t ≤ (kq + 1) * c) (h4 : 4 < pl.length) (hgq : gq ≤ 64)
    (hN : roundN (lvOf pl 4).1 (lvOf pl 4).2.1 = 2 ^ h)
    (hD : roundD (lvOf pl 4).1 (lvOf pl 4).2.2.1 = 2 ^ κ - 1 + ℓ) (hk : (lvOf pl 4).2.2.1 = ℓ)
    (hq : 8 * ((lvOf pl 4).2.2.2.1 - 1) ^ t * 2 ^ 128 + 8 * (t + 1) * 0 * (2 ^ h) ^ t ≤
      7 * 2 ^ gq * (2 ^ h) ^ t) :
    FinOK chalE2 εW (finEOf pl κ ℓ h kq t c gq hκ hℓ hℓ' hh hc hch ht) ((lvOf pl 4).2.2.2.1 - ℓ) := by
  obtain ⟨h1, h2, h3, h4, h5, h6⟩ := levelRounds_okOf (F := E2) card_E2 hpl h4
  rw [hN, hD, hk] at h1
  rw [hk] at h2 h3 h4 h5 h6
  have hA : aOut (fun s ↦ (parOf pl 4 s).A) ((lvOf pl 4).2.2.2.1 - ℓ) 1 ℓ = (lvOf pl 4).2.2.2.1 := h6
  have heF := eFin_finE2_le (hκ := hκ) (hℓ := hℓ) (hℓ' := hℓ') (hh := hh) (hc := hc) (hch := hch)
    (ht := ht) gq (lvOf pl 4).2.2.2.1 hq
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
    heF := by dsimp only [finEOf]; rw [hA]; exact heF.trans_lt εW_lt_one
    heFT := by dsimp only [finEOf]; rw [hA]; exact heF }

/-- **A deployed level with a next one** at the deployed list (`Lvm6.Params17.levels`). -/
noncomputable abbrev midE (i ko ℓ h κ' ℓ' h' kq t c gQ A' : ℕ) (z : Bool) (hκ : 0 + ℓ' + κ' = ko + 1)
    (hko : ko + 1 < 64) (hℓ : 1 ≤ ℓ) (hℓ' : ℓ ≤ 64) (hh : h ≤ 64) (hh' : h' ≤ 64) (hc : 0 < c)
    (hch : c * h ≤ 128) (ht : t ≤ (kq + 1) * c) : MidLv E2 WtE (2 ^ h) ℓ (2 ^ h') ℓ' :=
  midEOf Lvm6.Params17.levels i ko ℓ h κ' ℓ' h' kq t c gQ A' z hκ hko hℓ hℓ' hh hh' hc hch ht

/-- **The final level** at the deployed list. -/
noncomputable abbrev finE (κ ℓ h kq t c gq : ℕ) (hκ : κ < 64) (hℓ : 1 ≤ ℓ) (hℓ' : ℓ ≤ 64)
    (hh : h ≤ 64) (hc : 0 < c) (hch : c * h ≤ 128) (ht : t ≤ (kq + 1) * c) :
    FinLv E2 WtE (2 ^ h) ℓ :=
  finEOf Lvm6.Params17.levels κ ℓ h kq t c gq hκ hℓ hℓ' hh hc hch ht

/-! ## The rows, from the shape -/

/-- **A level with a next one, as a row** (`midEOf`'s numbers): commitment index `i`, message
variables `ko + 1`, folds `ℓ`, `2^h` positions; the next level's message variables `κ'`, folds `ℓ'`,
`2^h'` positions; `kq + 1` position draws of `c` positions each, `t` openings, the query grind `gQ`,
the next level's start agreement `A'`. -/
structure MidRow where
  i : ℕ
  ko : ℕ
  ℓ : ℕ
  h : ℕ
  κ' : ℕ
  ℓ' : ℕ
  h' : ℕ
  kq : ℕ
  t : ℕ
  c : ℕ
  gQ : ℕ
  A' : ℕ
deriving DecidableEq, Repr

/-- **The final level, as a row** (`finEOf`'s numbers). -/
structure FinRow where
  κ : ℕ
  ℓ : ℕ
  h : ℕ
  kq : ℕ
  t : ℕ
  c : ℕ
  gq : ℕ
deriving DecidableEq, Repr

/-- The message variables of level `i`, less one: `sh.nu (i + 1) − 1` (level `i`'s variables after
its folds). -/
def koOf (sh : Shape) (i : ℕ) : ℕ := sh.nu (i + 1) - 1

/-- **Level `i`'s row**, read from the shape (`sh.lvl`, `sh.lev`'s `per`/`draws`, `sh.nu`) and the next
level's final agreement in PARAM's list `pl`. -/
def midRow (sh : Shape) (pl : PLv) (i : ℕ) : MidRow where
  i := i
  ko := koOf sh i
  ℓ := (sh.lvl i).fold
  h := (sh.lvl i).ht
  -- `= sh.nu (i + 2)` (`hκ` checks it is positive); written as the next row's `ko + 1`, so that
  -- `ladAt`'s next degree matches by definition.
  κ' := koOf sh (i + 1) + 1
  ℓ' := (sh.lvl (i + 1)).fold
  h' := (sh.lvl (i + 1)).ht
  kq := (sh.lev i).draws - 1
  t := (sh.lvl i).nOpen
  c := (sh.lev i).per
  gQ := (sh.lvl i).gQuery
  A' := (lvOf pl (i + 1)).2.2.2.1 - (sh.lvl (i + 1)).fold

/-- **The final level `i`'s row**, read from the shape. -/
def finRow (sh : Shape) (i : ℕ) : FinRow where
  κ := koOf sh i + 1
  ℓ := (sh.lvl i).fold
  h := (sh.lvl i).ht
  kq := (sh.lev i).draws - 1
  t := (sh.lvl i).nOpen
  c := (sh.lev i).per
  gq := (sh.lvl i).gQuery

/-- **A row's conditions**: `midEOf`'s side conditions and `midOK_EOf`'s numbers at PARAM's list. -/
structure MidRow.Ok (pl : PLv) (r : MidRow) : Prop where
  hκ : 0 + r.ℓ' + r.κ' = r.ko + 1
  hko : r.ko + 1 < 64
  hℓ : 1 ≤ r.ℓ
  hℓ' : r.ℓ ≤ 64
  hh : r.h ≤ 64
  hh' : r.h' ≤ 64
  hc : 0 < r.c
  hch : r.c * r.h ≤ 128
  ht : r.t ≤ (r.kq + 1) * r.c
  hi : r.i < pl.length
  hgQ : r.gQ ≤ 64
  hN : roundN (lvOf pl r.i).1 (lvOf pl r.i).2.1 = 2 ^ r.h
  hD : roundD (lvOf pl r.i).1 (lvOf pl r.i).2.2.1 = 2 ^ (r.ko + 1) - 1 + r.ℓ
  hk : (lvOf pl r.i).2.2.1 = r.ℓ
  hgap : 2 ^ r.h' * (2 ^ r.κ' - 1 + r.ℓ') < r.A' * r.A'
  hadm : Lvm6.Params.admits ((jl (2 ^ r.h') r.A' (2 ^ r.κ' - 1 + r.ℓ')).choose 2 * (r.ko + 1)) 18 = true
  hq : 8 * ((lvOf pl r.i).2.2.2.1 - 1) ^ r.t * 2 ^ 128 +
    8 * (r.t + 1) * jl (2 ^ r.h') r.A' (2 ^ r.κ' - 1 + r.ℓ') * (2 ^ r.h) ^ r.t ≤
      7 * 2 ^ r.gQ * (2 ^ r.h) ^ r.t

instance (pl : PLv) (r : MidRow) : Decidable (r.Ok pl) :=
  decidable_of_iff (0 + r.ℓ' + r.κ' = r.ko + 1 ∧ r.ko + 1 < 64 ∧ 1 ≤ r.ℓ ∧ r.ℓ ≤ 64 ∧ r.h ≤ 64 ∧
      r.h' ≤ 64 ∧ 0 < r.c ∧ r.c * r.h ≤ 128 ∧ r.t ≤ (r.kq + 1) * r.c ∧ r.i < pl.length ∧ r.gQ ≤ 64 ∧
      roundN (lvOf pl r.i).1 (lvOf pl r.i).2.1 = 2 ^ r.h ∧
      roundD (lvOf pl r.i).1 (lvOf pl r.i).2.2.1 = 2 ^ (r.ko + 1) - 1 + r.ℓ ∧
      (lvOf pl r.i).2.2.1 = r.ℓ ∧ 2 ^ r.h' * (2 ^ r.κ' - 1 + r.ℓ') < r.A' * r.A' ∧
      Lvm6.Params.admits ((jl (2 ^ r.h') r.A' (2 ^ r.κ' - 1 + r.ℓ')).choose 2 * (r.ko + 1)) 18 = true ∧
      8 * ((lvOf pl r.i).2.2.2.1 - 1) ^ r.t * 2 ^ 128 +
        8 * (r.t + 1) * jl (2 ^ r.h') r.A' (2 ^ r.κ' - 1 + r.ℓ') * (2 ^ r.h) ^ r.t ≤
          7 * 2 ^ r.gQ * (2 ^ r.h) ^ r.t)
    ⟨fun ⟨a, b, c, d, e, f, g, h, i, j, k, l, m, n, o, p, q⟩ ↦ ⟨a, b, c, d, e, f, g, h, i, j, k, l, m, n, o, p, q⟩,
      fun ⟨a, b, c, d, e, f, g, h, i, j, k, l, m, n, o, p, q⟩ ↦ ⟨a, b, c, d, e, f, g, h, i, j, k, l, m, n, o, p, q⟩⟩

/-- **The final row's conditions** (level `4` of PARAM's list). -/
structure FinRow.Ok (pl : PLv) (r : FinRow) : Prop where
  hκ : r.κ < 64
  hℓ : 1 ≤ r.ℓ
  hℓ' : r.ℓ ≤ 64
  hh : r.h ≤ 64
  hc : 0 < r.c
  hch : r.c * r.h ≤ 128
  ht : r.t ≤ (r.kq + 1) * r.c
  h4 : 4 < pl.length
  hgq : r.gq ≤ 64
  hN : roundN (lvOf pl 4).1 (lvOf pl 4).2.1 = 2 ^ r.h
  hD : roundD (lvOf pl 4).1 (lvOf pl 4).2.2.1 = 2 ^ r.κ - 1 + r.ℓ
  hk : (lvOf pl 4).2.2.1 = r.ℓ
  hq : 8 * ((lvOf pl 4).2.2.2.1 - 1) ^ r.t * 2 ^ 128 + 8 * (r.t + 1) * 0 * (2 ^ r.h) ^ r.t ≤
    7 * 2 ^ r.gq * (2 ^ r.h) ^ r.t

instance (pl : PLv) (r : FinRow) : Decidable (r.Ok pl) :=
  decidable_of_iff (r.κ < 64 ∧ 1 ≤ r.ℓ ∧ r.ℓ ≤ 64 ∧ r.h ≤ 64 ∧ 0 < r.c ∧ r.c * r.h ≤ 128 ∧
      r.t ≤ (r.kq + 1) * r.c ∧ 4 < pl.length ∧ r.gq ≤ 64 ∧
      roundN (lvOf pl 4).1 (lvOf pl 4).2.1 = 2 ^ r.h ∧
      roundD (lvOf pl 4).1 (lvOf pl 4).2.2.1 = 2 ^ r.κ - 1 + r.ℓ ∧ (lvOf pl 4).2.2.1 = r.ℓ ∧
      8 * ((lvOf pl 4).2.2.2.1 - 1) ^ r.t * 2 ^ 128 + 8 * (r.t + 1) * 0 * (2 ^ r.h) ^ r.t ≤
        7 * 2 ^ r.gq * (2 ^ r.h) ^ r.t)
    ⟨fun ⟨a, b, c, d, e, f, g, h, i, j, k, l, m⟩ ↦ ⟨a, b, c, d, e, f, g, h, i, j, k, l, m⟩,
      fun ⟨a, b, c, d, e, f, g, h, i, j, k, l, m⟩ ↦ ⟨a, b, c, d, e, f, g, h, i, j, k, l, m⟩⟩

/-- **A five-level shape's rows hold** at PARAM's list: the shape has five levels, their fold and OOD
grinds are the program's (`midEOf`'s `g := 10`, `gO := 18`), and the five rows pass. -/
structure RowsOK (sh : Shape) (pl : PLv) : Prop where
  hlen : sh.levels.length = 5
  hgr : ∀ l ∈ sh.levels, l.gFold = 10 ∧ l.gOod = 18
  h0 : (midRow sh pl 0).Ok pl
  h1 : (midRow sh pl 1).Ok pl
  h2 : (midRow sh pl 2).Ok pl
  h3 : (midRow sh pl 3).Ok pl
  hf : (finRow sh 4).Ok pl

/-! ## The ladder of a shape -/

/-- **Level `i` of a shape** (`midEOf` at its row; lane values at level 0). -/
noncomputable def midAt (sh : Shape) (pl : PLv) (i : ℕ) (hr : (midRow sh pl i).Ok pl) :
    MidLv E2 WtE (2 ^ (midRow sh pl i).h) (midRow sh pl i).ℓ (2 ^ (midRow sh pl i).h')
      (midRow sh pl i).ℓ' :=
  midEOf pl (midRow sh pl i).i (midRow sh pl i).ko (midRow sh pl i).ℓ (midRow sh pl i).h
    (midRow sh pl i).κ' (midRow sh pl i).ℓ' (midRow sh pl i).h' (midRow sh pl i).kq (midRow sh pl i).t
    (midRow sh pl i).c (midRow sh pl i).gQ (midRow sh pl i).A' (i == 0) hr.hκ hr.hko hr.hℓ hr.hℓ'
    hr.hh hr.hh' hr.hc hr.hch hr.ht

/-- **The final level of a shape** (level `4`). -/
noncomputable def finAt (sh : Shape) (pl : PLv) (hr : (finRow sh 4).Ok pl) :
    FinLv E2 WtE (2 ^ (finRow sh 4).h) (finRow sh 4).ℓ :=
  finEOf pl (finRow sh 4).κ (finRow sh 4).ℓ (finRow sh 4).h (finRow sh 4).kq (finRow sh 4).t
    (finRow sh 4).c (finRow sh 4).gq hr.hκ hr.hℓ hr.hℓ' hr.hh hr.hc hr.hch hr.ht

/-- **The ladder of a five-level shape.** -/
noncomputable def ladAt (sh : Shape) (pl : PLv) (hr : RowsOK sh pl) :
    Lad E2 WtE (2 ^ (sh.lvl 0).ht) (sh.lvl 0).fold :=
  .mid (midAt sh pl 0 hr.h0) (.mid (midAt sh pl 1 hr.h1) (.mid (midAt sh pl 2 hr.h2)
    (.mid (midAt sh pl 3 hr.h3) (.fin (finAt sh pl hr.hf)))))

theorem midOK_At {sh : Shape} {pl : PLv} (hpl : roundsCheckOf pl = true) (i : ℕ)
    (hr : (midRow sh pl i).Ok pl) :
    MidOK chalE2 εW (midAt sh pl i hr) ((lvOf pl i).2.2.2.1 - (midRow sh pl i).ℓ) (i + 1)
      (domE (midRow sh pl i).h' hr.hh') (2 ^ (midRow sh pl i).κ' - 1 + (midRow sh pl i).ℓ')
      (wokE (midRow sh pl i).κ' (midRow sh pl i).ℓ') :=
  midOK_EOf hpl (midRow sh pl i).i (midRow sh pl i).ko (midRow sh pl i).ℓ (midRow sh pl i).h
    (midRow sh pl i).κ' (midRow sh pl i).ℓ' (midRow sh pl i).h' (midRow sh pl i).kq (midRow sh pl i).t
    (midRow sh pl i).c (midRow sh pl i).gQ (midRow sh pl i).A' (i == 0) hr.hκ hr.hko hr.hℓ hr.hℓ'
    hr.hh hr.hh' hr.hc hr.hch hr.ht hr.hi hr.hgQ hr.hN hr.hD hr.hk hr.hgap hr.hadm hr.hq

theorem finOK_At {sh : Shape} {pl : PLv} (hpl : roundsCheckOf pl = true) (hr : (finRow sh 4).Ok pl) :
    FinOK chalE2 εW (finAt sh pl hr) ((lvOf pl 4).2.2.2.1 - (finRow sh 4).ℓ) :=
  finOK_EOf hpl (finRow sh 4).κ (finRow sh 4).ℓ (finRow sh 4).h (finRow sh 4).kq (finRow sh 4).t
    (finRow sh 4).c (finRow sh 4).gq hr.hκ hr.hℓ hr.hℓ' hr.hh hr.hc hr.hch hr.ht hr.h4 hr.hgq hr.hN hr.hD
    hr.hk hr.hq

/-- **The ladder's hypotheses hold for a five-level shape** whose rows hold at a checked PARAM list,
from level 0's start agreement `Aend₀ − ℓ₀`. -/
theorem ladAt_ok {sh : Shape} {pl : PLv} (hpl : roundsCheckOf pl = true) (hr : RowsOK sh pl) :
    LadOK chalE2 εW (ladAt sh pl hr) ((lvOf pl 0).2.2.2.1 - (sh.lvl 0).fold) :=
  ⟨midOK_At hpl 0 hr.h0, midOK_At hpl 1 hr.h1, midOK_At hpl 2 hr.h2, midOK_At hpl 3 hr.h3,
    finOK_At hpl hr.hf⟩

/-! ## The deployed ladder (`P17`, `M = 24`) -/

/-- **The rows of `P17`**, written out (P17-freeze §5 W1, in `midE i ko ℓ h κ' ℓ' h' kq t c gQ A'` and
`finE κ ℓ h kq t c gq` order). -/
theorem midRow_P17 : (List.range 4).map (midRow P17 Lvm6.Params17.levels) =
    [⟨0, 17, 6, 20, 14, 4, 19, 18, 110, 6, 19, 94049 - 4⟩, ⟨1, 13, 4, 19, 10, 4, 18, 7, 45, 6, 17, 17103 - 4⟩,
      ⟨2, 9, 4, 18, 6, 4, 17, 3, 28, 7, 18, 3282 - 4⟩, ⟨3, 5, 4, 17, 2, 4, 16, 2, 21, 7, 17, 933 - 4⟩] := by
  decide +kernel

theorem finRow_P17 : finRow P17 4 = ⟨2, 4, 16, 2, 18, 8, 18⟩ := by decide +kernel

theorem rowsOK_P17 : RowsOK P17 Lvm6.Params17.levels :=
  ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel,
    by decide +kernel, by decide +kernel⟩

/-- Level 4 (final). -/
noncomputable def finD : FinLv E2 WtE (2 ^ 16) 4 := finAt P17 Lvm6.Params17.levels rowsOK_P17.hf

/-- Level 3. -/
noncomputable def mid3 : MidLv E2 WtE (2 ^ 17) 4 (2 ^ 16) 4 := midAt P17 Lvm6.Params17.levels 3 rowsOK_P17.h3

/-- Level 2. -/
noncomputable def mid2 : MidLv E2 WtE (2 ^ 18) 4 (2 ^ 17) 4 := midAt P17 Lvm6.Params17.levels 2 rowsOK_P17.h2

/-- Level 1. -/
noncomputable def mid1 : MidLv E2 WtE (2 ^ 19) 4 (2 ^ 18) 4 := midAt P17 Lvm6.Params17.levels 1 rowsOK_P17.h1

/-- Level 0. -/
noncomputable def mid0 : MidLv E2 WtE (2 ^ 20) 6 (2 ^ 19) 4 := midAt P17 Lvm6.Params17.levels 0 rowsOK_P17.h0

/-- **The deployed ladder** (`P17`; the name is `P18`'s until the port's rename). -/
noncomputable def ladD : Lad E2 WtE (2 ^ 20) 6 :=
  .mid mid0 (.mid mid1 (.mid mid2 (.mid mid3 (.fin finD))))

theorem ladD_eq_ladAt : ladD = ladAt P17 Lvm6.Params17.levels rowsOK_P17 := rfl

/-- **The ladder's hypotheses hold at `P17`** (PARAM's row, `Lvm6.Params17`), from level 0's start
agreement `Aend₀ − 6 = 526,650`. -/
theorem ladD_ok : LadOK chalE2 εW ladD (526656 - 6) :=
  ladAt_ok roundsCheck_ok rowsOK_P17

/-! ### The deployed ladder's level 0, as consumers read it -/

theorem ladD_i : ladD.i = 0 := rfl

theorem ladD_dom : ladD.dom = domE 20 (by norm_num) := rfl

theorem ladD_d : ladD.d = 2 ^ 18 - 1 + 6 := rfl

theorem ladD_word : ladD.word = wordE true 0 (0 + 6) 20 := rfl

/-- The deployed levels as literal `midE`/`finE` applications (the rows of `midRow_P17`, `finRow_P17`). -/
theorem mid0_eq : mid0 = midE 0 17 6 20 14 4 19 18 110 6 19 (94049 - 4) true (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) := rfl

theorem mid1_eq : mid1 = midE 1 13 4 19 10 4 18 7 45 6 17 (17103 - 4) false (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) := rfl

theorem mid2_eq : mid2 = midE 2 9 4 18 6 4 17 3 28 7 18 (3282 - 4) false (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) := rfl

theorem mid3_eq : mid3 = midE 3 5 4 17 2 4 16 2 21 7 17 (933 - 4) false (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) := rfl

theorem finD_eq : finD = finE 2 4 16 2 18 8 18 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) := rfl

/-! ## `P18` (before the port): a corollary of the same theorem -/

/-! ## The opening -/

/-- The first 24 entries of a list, padded with zeros (`M = 24`; the name is `P18`'s until the port's
rename). -/
def padD (y : List E2) : List E2 := List.ofFn fun i : Fin 24 ↦ y.getD i 0

/-- **The batched claim's weight** at level 0: `Φ(y) = cl(y[6..24) ++ y[..6))` (the lane bits are the
stack index's top six bits, FORMAT6 §6.5 placement), read on the first 24 entries. -/
noncomputable def w₀ (cl : (List E2 → E2) × E2) : WtE.Wt (0 + 6) :=
  (18, fun y ↦ cl.1 ((padD y).drop 6 ++ (padD y).take 6))

/-- **The deployed opening program** of a batched claim (FORMAT6 §6.6 at `P17`). -/
noncomputable def whirP (cl : (List E2 → E2) × E2) : VerifierProgram Bool :=
  ladP chalE2 ladD (w₀ cl) cl.2

/-- **The deployed opening rejects from the descent invariant** at level 0's start agreement, for a
claim whose weight is affine in each of its 24 variables (in the rotated order of `w₀`). -/
noncomputable def whirSpecD (cl : (List E2 → E2) × E2)
    (hma : MA 24 (w₀ cl).2) :
    Spec (whirP cl) (fun h ↦ (commits h).length = 1 ∧
      TViol (domE 20 (by norm_num)) (wordE true 0 (0 + 6) 20 (commits h)) (WtE.den (w₀ cl)) cl.2
        (526656 - 6) (2 ^ 18 - 1 + 6) (fun _ ↦ True)) (fun b _ ↦ b = false) εW 0 0 :=
  ladSpec ladD (526656 - 6) ladD_ok (w₀ cl) cl.2 ⟨rfl, hma⟩

end Lvm6.Whir
