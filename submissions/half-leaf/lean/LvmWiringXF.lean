-- New for lvm2 E2-FT (E2F-C): the fast twins of statement 13's cache (`cacheWX`) and its check (`PhiCacheX.okB`) on
-- roll 11's array caches (`K.FLF`: the layout's words and slots, the writer counts), as roll 11's `cacheT20` /
-- `termsChecked`: the entries of the twin `e2` rows read through `FLF`, not through `Lay`'s list scans.
import LvmWiringX
import LvmQTypedGuard
import LvmWiringKF

/-!
# The coordinate-split cache, fast

* **`K.FLF.rowEntsX`**: `FLF.rowEnts` with the `e2` twin rows' entries (`instEntsX`'s, through the caches).
* **`srcEntsXF G s`**: coordinate `s`'s entries (`srcEntsX`'s filter and retag) on `FLF`.
* **`srcEntsXF_eq`**: on a checked layout they are `srcEntsX` (the same entries, so the same check).
* **`deriveTermsXF`**, **`cacheWXF`** (`K.compileTF`), **`PhiCache.okBXF`**, **`PhiCacheX.okBF`**: the cache and the
  check computed on `srcEntsXF`; **`cacheWXF_eq`**, **`okBF_eq`**: equal to `cacheWX`, `PhiCacheX.okB` on a checked
  layout, so `PhiQCX_eq` (statement 13) applies to the fast cache under the fast check (**`PhiQCX_eqF`**).
-/

set_option autoImplicit false

namespace Lvm.Typed

open Lvm.Loop LeanVM.Parameters

namespace K.FL

variable (F : FL)

/-- **`FL.rowEnts` with the `e2` twin rows** (the proof's intermediate: `FLF.rowEntsX` with the writer counts read
from the blocks). -/
def rowEntsX (b t jf : ℕ) : List Ent :=
  let Bq := F.qb.getD b default
  let row := (F.tpls.getD b #[]).getD t default
  let j := unflat Bq.dims jf
  let x := match (F.crA.getD b #[]).getD t none with
    | some r => F.slotR b r jf
    | none => 0
  let arg (k : ℕ) (w : FE) : List (ℕ × FE) :=
    let a := row.args.getD k default
    F.cellEnts a.ty (a.at j) w
  let ck := F.stK.getD b 0 + Bq.tw .K * jf + (F.rkK.getD b #[]).getD t 0
  let ce := F.stE.getD b 0 + Bq.tw .E * jf + (F.rkE.getD b #[]).getD t 0
  let res : List (ℕ × FE) := F.cellEnts row.ty (match row.ty with | .K => ck | .E => ce) 1
  let res1 : List (ℕ × FE) := F.cellEnts .K (ck + 1) 1
  match row.op with
  | .e2 .mul false =>
      tagE 0 x (arg 0 1) ++ tagE 4 x (arg 1 1) ++ tagE 1 x (arg 2 1) ++ tagE 5 x (arg 3 1) ++
      tagE 2 x (arg 4 1) ++ tagE 6 x (arg 5 1) ++ tagE 3 x res ++ tagE 7 x res1
  | .e2 (.lin k k₀ k₁) false =>
      tagE 2 x (arg 0 1 ++ arg 2 (FE.ofK k) ++ [(F.lay.one, FE.ofK k₀)]) ++
      tagE 6 x (arg 1 1 ++ arg 3 (FE.ofK k) ++ [(F.lay.one, FE.ofK k₁)]) ++
      tagE 3 x res ++ tagE 7 x res1
  | .e2 _ true => []
  | _ => F.rowEnts b t jf

end K.FL

namespace K.FLF

variable (G : FLF)

/-- **`FLF.rowEnts` with the `e2` twin rows** (`instEntsX` on the caches): a twin's first row carries both
coordinates' entries at its slot, the second none; every other row is `rowEnts`'s. -/
def rowEntsX (b t jf : ℕ) : List Ent :=
  let F := G.F
  let Bq := F.qb.getD b default
  let row := (F.tpls.getD b #[]).getD t default
  let j := unflat Bq.dims jf
  let x := match (F.crA.getD b #[]).getD t none with
    | some r => F.slotR b r jf
    | none => 0
  let arg (k : ℕ) (w : FE) : List (ℕ × FE) :=
    let a := row.args.getD k default
    F.cellEntsF a.ty (a.at j) w
  let ck := F.stK.getD b 0 + G.twK.getD b 0 * jf + (F.rkK.getD b #[]).getD t 0
  let ce := F.stE.getD b 0 + G.twE.getD b 0 * jf + (F.rkE.getD b #[]).getD t 0
  let res : List (ℕ × FE) := F.cellEntsF row.ty (match row.ty with | .K => ck | .E => ce) 1
  let res1 : List (ℕ × FE) := F.cellEntsF .K (ck + 1) 1
  match row.op with
  | .e2 .mul false =>
      tagE 0 x (arg 0 1) ++ tagE 4 x (arg 1 1) ++ tagE 1 x (arg 2 1) ++ tagE 5 x (arg 3 1) ++
      tagE 2 x (arg 4 1) ++ tagE 6 x (arg 5 1) ++ tagE 3 x res ++ tagE 7 x res1
  | .e2 (.lin k k₀ k₁) false =>
      tagE 2 x (arg 0 1 ++ arg 2 (FE.ofK k) ++ [(F.lay.one, FE.ofK k₀)]) ++
      tagE 6 x (arg 1 1 ++ arg 3 (FE.ofK k) ++ [(F.lay.one, FE.ofK k₁)]) ++
      tagE 3 x res ++ tagE 7 x res1
  | .e2 _ true => []
  | _ => G.rowEnts b t jf

end K.FLF

/-- **Coordinate `s`'s entries on the caches** (`srcEntsX`'s filter and retag on `FLF.rowEntsX`). -/
def srcEntsXF (G : K.FLF) (s : Bool) : TSrc → ℕ → List Ent
  | .row b t, jf => ((G.rowEntsX b t jf).filter fun e ↦ (e.o / 4 == 1) == s).map fun e ↦ { e with o := e.o % 4 }
  | .aux k r, j => if s then [] else G.auxEnts k r j

/-- **The terms of coordinate `s`** on the caches (`deriveTermsX`'s order and counts). -/
def deriveTermsXF (Q : Program) (lay : Lay) (s : Bool) : Array CTerm :=
  let E := srcEntsXF (K.FLF.ofLay Q lay) s
  let ents : TSrc → ℕ → Array Ent := fun src jf ↦ (E src jf).toArray
  ((rowsOf Q lay).map fun src ↦ K.rowTermsG ents src (srcL Q lay src) (E src 0).length
    (match src with
      | .row b _ => K.fields (Q.blk b).dims
      | .aux k _ => [(0, (lay.aux.getD k default).l)])).foldl (· ++ ·) #[]

/-- **The coordinate-split cache on the caches** (`K.compileTF`). -/
def cacheWXF (Q : Program) (lay : Lay) : PhiCacheX :=
  let t0 := deriveTermsXF Q lay false
  let t1 := deriveTermsXF Q lay true
  ⟨⟨t0.toList, K.compileTF t0⟩, ⟨t1.toList, K.compileTF t1⟩⟩

/-- **The class check of one coordinate on the caches** (`PhiCache.okBX`'s, the entries on `FLF`, the check on
arrays). -/
def PhiCache.okBXF (Q : Program) (lay : Lay) (s : Bool) (c : PhiCache) : Bool :=
  let E := srcEntsXF (K.FLF.ofLay Q lay) s
  c.terms.map (fun t ↦ (t.src, t.idx)) ==
      (rowsOf Q lay).flatMap (fun src ↦ (List.range (E src 0).length).map (src, ·)) &&
    c.terms.all (fun t ↦ t.l == srcL Q lay t.src && K.termWFB t) &&
    K.checkTermsGA (fun src jf ↦ (E src jf).toArray) CTerm.atF c.terms.toArray

/-- **The class check of the coordinate-split cache on the caches.** -/
def PhiCacheX.okBF (Q : Program) (lay : Lay) (c : PhiCacheX) : Bool :=
  c.c0.okBXF Q lay false && c.c1.okBXF Q lay true

/-! ## The fast twins are the definitions -/

/-- `FLF.rowEntsX` is `FL.rowEntsX` (the writer counts from the arrays, the cell words from one owner search). -/
theorem flf_rowEntsX (Q : Program) (lay : Lay) (b t jf : ℕ) :
    (K.FLF.ofLay Q lay).rowEntsX b t jf = (K.FL.ofLay Q lay).rowEntsX b t jf := by
  have hK : (K.FLF.ofLay Q lay).twK.getD b 0 = ((K.FL.ofLay Q lay).qb.getD b default).tw .K :=
    K.sw_getD_map _ _ (K.sw_tw_default .K) b
  have hE : (K.FLF.ofLay Q lay).twE.getD b 0 = ((K.FL.ofLay Q lay).qb.getD b default).tw .E :=
    K.sw_getD_map _ _ (K.sw_tw_default .E) b
  unfold K.FLF.rowEntsX K.FL.rowEntsX
  rw [hK, hE, K.flf_rowEnts]
  simp only [K.cellEntsF_eq]
  rfl

/-- **The cached entries of a template row are its instance's** (`instEntsX`; `rowEnts_eq`'s row case with the
twin rows): on a checked layout. -/
theorem fl_rowEntsX (Q : Program) (lay : Lay) (hlay : lay.Ok Q) (b t jf : ℕ) :
    (K.FL.ofLay Q lay).rowEntsX b t jf = instEntsX Q lay (Q.inst b jf t) := by
  unfold K.FL.rowEntsX K.FL.rowEnts instEntsX instEnts Lay.slot
  simp only [K.fl_qb_getD, K.fl_tpls_getD, K.fl_crA_getD, K.fl_cellEnts_app Q lay hlay, K.fl_lay, K.fl_Q,
    Program.inst, Lay.argEnts, Lay.resEnts]
  have hsl : ∀ r, (lay.blocks.getD b default).cr.getD t none = some r →
      (K.FL.ofLay Q lay).slotR b r jf = lay.slotR b r jf := by
    intro r hr
    refine K.fl_slotR Q lay b r jf ?_
    by_contra hb
    rw [K.fl_getD_ge lay.blocks b default (by omega)] at hr
    cases hr
  have hbd : ((Q.blk b).tpl.getD t default).op ≠ .assert0 → b < Q.blocks.length ∧ t < (Q.blk b).tpl.length := by
    intro h
    by_contra hc
    apply h
    by_cases ht : t < (Q.blk b).tpl.length
    · have hb : ¬ b < Q.blocks.length := fun hb ↦ hc ⟨hb, ht⟩
      have : Q.blk b = default := K.fl_getD_ge Q.blocks b default (by omega)
      rw [this] at ht; cases ht
    · rw [K.fl_getD_ge _ t default (by omega)]; rfl
  have hck : ((Q.blk b).tpl.getD t default).op ≠ .assert0 →
      (K.FL.ofLay Q lay).stK.getD b 0 + (Q.blk b).tw Ty.K * jf + ((K.FL.ofLay Q lay).rkK.getD b #[]).getD t 0 =
        Q.start .K b + (Q.blk b).tw .K * jf + (Q.blk b).rank .K t := by
    intro h
    obtain ⟨hb, ht⟩ := hbd h
    rw [K.fl_stK Q lay b hb.le, K.fl_rkK Q lay b t hb ht.le]
  have hce : ((Q.blk b).tpl.getD t default).op ≠ .assert0 →
      (K.FL.ofLay Q lay).stE.getD b 0 + (Q.blk b).tw Ty.E * jf + ((K.FL.ofLay Q lay).rkE.getD b #[]).getD t 0 =
        Q.start .E b + (Q.blk b).tw .E * jf + (Q.blk b).rank .E t := by
    intro h
    obtain ⟨hb, ht⟩ := hbd h
    rw [K.fl_stE Q lay b hb.le, K.fl_rkE Q lay b t hb ht.le]
  clear hbd
  generalize hc : (lay.blocks.getD b default).cr.getD t none = c at hsl
  generalize (Q.blk b).tpl.getD t default = row at hck hce
  obtain ⟨op, ty, args⟩ := row
  rcases c with _ | r <;>
  rcases op with _ | _ | _ | _ | _ | _ | ⟨_ | _, _ | _⟩ <;> cases ty <;>
    simp only [Inst.clock, ne_eq, reduceCtorEq, not_false_eq_true, hck, hce, hsl]

/-- **The cached entries are the entries** (coordinate-split): on a checked layout. -/
theorem srcEntsXF_eq (Q : Program) (lay : Lay) (hlay : lay.Ok Q) (s : Bool) :
    srcEntsXF (K.FLF.ofLay Q lay) s = srcEntsX Q lay s := by
  funext src jf
  cases src with
  | row b t =>
    simp only [srcEntsXF, srcEntsX]
    rw [flf_rowEntsX, fl_rowEntsX Q lay hlay]
  | aux k r =>
    simp only [srcEntsXF, srcEntsX]
    have h := rowEnts_eq Q lay hlay (.aux k r) jf
    rw [← K.flf_srcEnts] at h
    simp only [K.FLF.srcEnts, srcEnts] at h
    rw [h]

theorem deriveTermsXF_eq (Q : Program) (lay : Lay) (hlay : lay.Ok Q) (s : Bool) :
    deriveTermsXF Q lay s = deriveTermsX Q lay s := by
  unfold deriveTermsXF deriveTermsX
  rw [srcEntsXF_eq Q lay hlay s]
  rfl

/-- **The fast cache is `cacheWX`** on a checked layout. -/
theorem cacheWXF_eq (Q : Program) (lay : Lay) (hlay : lay.Ok Q) : cacheWXF Q lay = cacheWX Q lay := by
  unfold cacheWXF cacheWX
  rw [deriveTermsXF_eq Q lay hlay false, deriveTermsXF_eq Q lay hlay true, K.compileTF_eq]

theorem okBXF_eq (Q : Program) (lay : Lay) (hlay : lay.Ok Q) (s : Bool) (c : PhiCache) :
    c.okBXF Q lay s = c.okBX Q lay s := by
  unfold PhiCache.okBXF PhiCache.okBX termKeysX
  rw [srcEntsXF_eq Q lay hlay s, K.cterm_atF, K.checkTermsG_eqA]

/-- **The fast check is `PhiCacheX.okB`** on a checked layout. -/
theorem okBF_eq (Q : Program) (lay : Lay) (hlay : lay.Ok Q) (c : PhiCacheX) : c.okBF Q lay = c.okB Q lay := by
  unfold PhiCacheX.okBF PhiCacheX.okB
  rw [okBXF_eq Q lay hlay false, okBXF_eq Q lay hlay true]

/-- **Statement 13 on the fast cache and check.** -/
theorem PhiQCX_eqF (Q : Program) (lay : Lay) (hlay : lay.Ok Q) (hc : (cacheWXF Q lay).okBF Q lay = true)
    (pt : List FE) (hpt : pt.length = phiVarsX) : PhiQCX (cacheWXF Q lay) pt = PhiQFX Q lay pt := by
  rw [cacheWXF_eq Q lay hlay] at hc ⊢
  rw [okBF_eq Q lay hlay] at hc
  exact PhiQCX_eq Q lay hlay hc pt hpt

end Lvm.Typed
