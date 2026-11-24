-- New for lvm6 (PHIV8): `PT.eval8`, the class evaluator of `Φ_Q` with its hot sums of products unreduced
-- (`Lvm6VPhiU`): one finish per sum instead of three reversals and two reductions per product. Downstream of
-- `Lvm6VPhiPT`; every twin has an `_eq` (or `fin_`) lemma to PHIV7's form, and
-- **`PT.eval8_eq : P.eval8 pt = P.eval pt`**.
import Lvm6VPhiPT
import Lvm6VPhiU

/-!
# `PT.eval8`

* Buckets: `bkGoU` (a bucket's groups, `Σ key·Σ members` unreduced), `bkSumU`, **`bkSumU_eq`** (`= bkSum`);
  `flatSumK8`, `rsumK8`, `CTpl.val8` with their `_eq` lemmas to PHIV7's `flatSumK`, `rsumK`, `CTpl.val2`.
* Gathers: `GK.colU` (a column, a single line without the inner loop), **`GK.valW8`** (columns, groups and rows
  unreduced), **`GK.valW8_eq`** (`= GK.valW`).
* Kernels: `kSumSt`, `kerMargLo`, `kerMargHi` (word sums), **`kerMargLo_kerF`**, **`kerMargHi_kerF`** (a kernel's
  marginal is the kernel of the other coordinates); `kTabG`, `gKa`, `gKb`, `gSf` with `_eq` lemmas (the prefix and
  segment tables off the shared kernels, no products).
* Strided runs: `SRunF.initS8`, `SRunF.valGS8` (`= valGS`): no `toSRun`, `mulE`, the atoms unreduced.
* Singles: `flushSumU` (**`flushSumU_eq`**, any order), `sglSumK8` (`= sglSumK`).
* Wiring: `PT.kval8`, `PT.evalW8` (`= PT.evalW7` given the shared kernels), **`PT.eval8`**, **`PT.eval8_eq`**.
-/

set_option autoImplicit false

namespace Lvm6.V

open LeanVM.Parameters Lvm Lvm.E2V Lvm.Typed Lvm.Loop

/-! ## Buckets -/

/-- **A bucket's groups from `g` on**, `Σ key·Σ members` unreduced in six words (PHIV7's `bkGo` reduces three `FK`
products a group). -/
@[specialize] def bkGoU (b : FBk) (KV MV : Array FE2) (KK MK : Array ℕ) (fk fm : ℕ → FE2) (g : ℕ)
    (l0 l1 lm h0 h1 hm : UInt64) : U6 :=
  if g < b.gk.size then
    let sm := memGo MV MK fm b.mm (b.off.getD (g + 1) 0) (b.off.getD g 0) 0 0
    let u := m2U (rd KV KK fk (b.gk.getD g 0)) sm
    bkGoU b KV MV KK MK fk fm (g + 1) (l0 ^^^ u.l0) (l1 ^^^ u.l1) (lm ^^^ u.lm) (h0 ^^^ u.h0) (h1 ^^^ u.h1)
      (hm ^^^ u.hm)
  else ⟨l0, l1, lm, h0, h1, hm⟩
termination_by b.gk.size - g

theorem fin_bkGoU (b : FBk) (KV MV : Array FE2) (KK MK : Array ℕ) (fk fm : ℕ → FE2) :
    ∀ (d g : ℕ) (l0 l1 lm h0 h1 hm : UInt64), b.gk.size - g = d →
      (bkGoU b KV MV KK MK fk fm g l0 l1 lm h0 h1 hm).fin = (U6.mk l0 l1 lm h0 h1 hm).fin +
        ((List.range' g (b.gk.size - g)).map fun g' =>
          rd KV KK fk (b.gk.getD g' 0) * ((b.mem g').map fun j => rd MV MK fm (b.mm.getD j 0)).sum).sum
  | 0, g, l0, l1, lm, h0, h1, hm, hd => by
    rw [bkGoU, if_neg (by omega), hd]; simp
  | d + 1, g, l0, l1, lm, h0, h1, hm, hd => by
    rw [bkGoU, if_pos (by omega)]
    dsimp only
    have hs := memGo_eq MV MK fm b.mm (b.off.getD (g + 1) 0) _ (b.off.getD g 0) 0 0 rfl
    rw [show (⟨0, 0⟩ : FE2) = 0 from rfl, zero_add] at hs
    generalize hu : m2U (rd KV KK fk (b.gk.getD g 0)) (memGo MV MK fm b.mm (b.off.getD (g + 1) 0) (b.off.getD g 0) 0 0)
      = u
    rw [fin_bkGoU b KV MV KK MK fk fm d (g + 1) _ _ _ _ _ _ (by omega),
      show U6.mk (l0 ^^^ u.l0) (l1 ^^^ u.l1) (lm ^^^ u.lm) (h0 ^^^ u.h0) (h1 ^^^ u.h1) (hm ^^^ u.hm) =
        (U6.mk l0 l1 lm h0 h1 hm).add u from rfl, fin_add, ← hu, fin_m2U_eq, hs,
      show b.gk.size - g = (b.gk.size - (g + 1)) + 1 by omega, List.range'_succ, List.map_cons, List.sum_cons]
    simp only [FBk.mem, add_assoc]

/-- A bucket's sum, keys and members by `byRow`, unreduced. -/
@[specialize] def bkSumU (b : FBk) (SK WK : Array ℕ) (SV WV : Array FE2) (fs fw : ℕ → FE2) : FE2 :=
  if b.byRow then (bkGoU b SV WV SK WK fs fw 0 0 0 0 0 0 0).fin else (bkGoU b WV SV WK SK fw fs 0 0 0 0 0 0 0).fin

theorem bkSumU_eq (b : FBk) (SK WK : Array ℕ) (SV WV : Array FE2) (fs fw : ℕ → FE2) :
    bkSumU b SK WK SV WV fs fw = bkSum b SK WK SV WV fs fw := by
  unfold bkSumU bkSum
  split <;> rw [fin_bkGoU _ _ _ _ _ _ _ _ 0 _ _ _ _ _ _ rfl, bkGo_zero, show U6.mk 0 0 0 0 0 0 = U6.zero from rfl,
    fin_zero, zero_add, List.range_eq_range', Nat.sub_zero]

/-! ## Singles -/

/-- **The grouped fold, unreduced**: the run's inner sum `Σ g t` and the outer sum `Σ F r (inner)` in six words
each; at a change of group the inner sum is finished once and `F` applied. -/
@[specialize] def flushGoU {α : Type} (es : Array α) (same : α → α → Bool) (g : α → U6) (F : α → FE2 → U6)
    (i : ℕ) (r : α) (a0 a1 am b0 b1 bm c0 c1 cm d0 d1 dm : UInt64) : U6 :=
  if h : i < es.size then
    let t := es[i]
    let u := g t
    if same r t then
      flushGoU es same g F (i + 1) r (a0 ^^^ u.l0) (a1 ^^^ u.l1) (am ^^^ u.lm) (b0 ^^^ u.h0) (b1 ^^^ u.h1)
        (bm ^^^ u.hm) c0 c1 cm d0 d1 dm
    else
      let w := F r (U6.mk a0 a1 am b0 b1 bm).fin
      flushGoU es same g F (i + 1) t u.l0 u.l1 u.lm u.h0 u.h1 u.hm (c0 ^^^ w.l0) (c1 ^^^ w.l1) (cm ^^^ w.lm)
        (d0 ^^^ w.h0) (d1 ^^^ w.h1) (dm ^^^ w.hm)
  else (U6.mk c0 c1 cm d0 d1 dm).add (F r (U6.mk a0 a1 am b0 b1 bm).fin)
termination_by es.size - i

/-- **`Σ_t F t (g t)`, grouped and unreduced.** -/
@[specialize] def flushSumU {α : Type} (es : Array α) (same : α → α → Bool) (g : α → U6) (F : α → FE2 → U6) :
    FE2 :=
  if h : 0 < es.size then
    let u := g es[0]
    (flushGoU es same g F 1 es[0] u.l0 u.l1 u.lm u.h0 u.h1 u.hm 0 0 0 0 0 0).fin
  else 0

section GroupedU

variable {α : Type} (es : Array α) (same : α → α → Bool) (g : α → U6) (F : α → FE2 → U6)
  (hadd : ∀ r x y, (F r (x + y)).fin = (F r x).fin + (F r y).fin)
  (hsame : ∀ r t, same r t = true → ∀ v, (F r v).fin = (F t v).fin)

include hadd hsame in
theorem fin_flushGoU : ∀ (d i : ℕ) (r : α) (a0 a1 am b0 b1 bm c0 c1 cm d0 d1 dm : UInt64), es.size - i = d →
    (flushGoU es same g F i r a0 a1 am b0 b1 bm c0 c1 cm d0 d1 dm).fin =
      (U6.mk c0 c1 cm d0 d1 dm).fin + (F r (U6.mk a0 a1 am b0 b1 bm).fin).fin +
        ((es.toList.drop i).map fun t => (F t (g t).fin).fin).sum
  | 0, i, r, a0, a1, am, b0, b1, bm, c0, c1, cm, d0, d1, dm, hd => by
    rw [flushGoU, dif_neg (by omega), List.drop_eq_nil_of_le (by simp; omega), fin_add]
    simp
  | d + 1, i, r, a0, a1, am, b0, b1, bm, c0, c1, cm, d0, d1, dm, hd => by
    have hi : i < es.size := by omega
    rw [flushGoU, dif_pos hi, List.drop_eq_getElem_cons (by simpa using hi)]
    simp only [Array.getElem_toList, List.map_cons, List.sum_cons]
    split
    · rename_i hs
      rw [fin_flushGoU d (i + 1) _ _ _ _ _ _ _ _ _ _ _ _ _ (by omega),
        show U6.mk (a0 ^^^ (g es[i]).l0) (a1 ^^^ (g es[i]).l1) (am ^^^ (g es[i]).lm) (b0 ^^^ (g es[i]).h0)
          (b1 ^^^ (g es[i]).h1) (bm ^^^ (g es[i]).hm) = (U6.mk a0 a1 am b0 b1 bm).add (g es[i]) from rfl,
        fin_add, hadd, hsame r es[i] hs ((g es[i]).fin)]
      abel
    · rw [fin_flushGoU d (i + 1) _ _ _ _ _ _ _ _ _ _ _ _ _ (by omega),
        show U6.mk (c0 ^^^ (F r (U6.mk a0 a1 am b0 b1 bm).fin).l0) (c1 ^^^ (F r (U6.mk a0 a1 am b0 b1 bm).fin).l1)
          (cm ^^^ (F r (U6.mk a0 a1 am b0 b1 bm).fin).lm) (d0 ^^^ (F r (U6.mk a0 a1 am b0 b1 bm).fin).h0)
          (d1 ^^^ (F r (U6.mk a0 a1 am b0 b1 bm).fin).h1) (dm ^^^ (F r (U6.mk a0 a1 am b0 b1 bm).fin).hm) =
          (U6.mk c0 c1 cm d0 d1 dm).add (F r (U6.mk a0 a1 am b0 b1 bm).fin) from rfl, fin_add]
      abel

include hadd hsame in
/-- **The unreduced grouped fold is the plain sum**, whatever the order of `es`. -/
theorem flushSumU_eq : flushSumU es same g F = (es.toList.map fun t => (F t (g t).fin).fin).sum := by
  unfold flushSumU
  split
  · rename_i h
    have hc := List.drop_eq_getElem_cons (l := es.toList) (i := 0) (by simpa using h)
    rw [List.drop_zero] at hc
    dsimp only
    rw [fin_flushGoU es same g F hadd hsame _ 1 _ _ _ _ _ _ _ _ _ _ _ _ _ rfl,
      show U6.mk 0 0 0 0 0 0 = U6.zero from rfl, fin_zero, zero_add]
    conv_rhs => rw [hc]
    simp [Array.getElem_toList]
  · rename_i h
    have h0 : es.toList = [] := List.eq_nil_of_length_eq_zero (by rw [Array.length_toList]; omega)
    simp [h0]

end GroupedU

/-- PHIV8: **the singles grouped and unreduced**: per single `fs(x)·(c·lw(y))` unreduced (one product at `c = 1`),
per group `fa(o)·(hw(key)·Σ)` with the last product unreduced. -/
@[specialize] def sglSumK8 (sg : Array CSgl) (fa fs : ℕ → FE2) (key : ℕ → ℕ) (hw lw : ℕ → FE2) : FE2 :=
  flushSumU sg (fun r t => r.o == t.o && key r.y == key t.y)
    (fun t => m2U (fs t.x) (if isOne t.c then lw t.y else mulE t.c (lw t.y)))
    (fun r v => m2U (fa r.o) (mulE (hw (key r.y)) v))

theorem sglSumK8_eq (sg : Array CSgl) (fa fs : ℕ → FE2) (key : ℕ → ℕ) (hw lw : ℕ → FE2) :
    sglSumK8 sg fa fs key hw lw = sglSumK sg fa fs key hw lw := by
  unfold sglSumK8 sglSumK
  have hsame : ∀ (r t : CSgl), (r.o == t.o && key r.y == key t.y) = true → ∀ v : FE2,
      mulE (fa r.o) (mulE (hw (key r.y)) v) = mulE (fa t.o) (mulE (hw (key t.y)) v) := by
    intro r t hs v
    simp only [Bool.and_eq_true, beq_iff_eq] at hs
    rw [hs.1, hs.2]
  have hU := flushSumU_eq sg (fun r t => r.o == t.o && key r.y == key t.y)
    (fun t => m2U (fs t.x) (if isOne t.c then lw t.y else mulE t.c (lw t.y)))
    (fun r v => m2U (fa r.o) (mulE (hw (key r.y)) v))
    (fun r x y => by simp only [fin_m2U_eq, mulE_eq]; ring)
    (fun r t hs v => by rw [fin_m2U_eq, fin_m2U_eq, ← mulE_eq, ← mulE_eq, hsame r t hs v])
  have h7 := flushSum_eq sg (fun r t => r.o == t.o && key r.y == key t.y)
    (fun t => cmulO t.c (mulE (fs t.x) (lw t.y))) (fun r v => mulE (fa r.o) (mulE (hw (key r.y)) v))
    (fun r x y => by simp only [mulE_eq]; ring) hsame
  rw [hU, h7]
  refine congrArg List.sum (List.map_congr_left fun t _ => ?_)
  rw [fin_m2U_eq, fin_m2U_eq, cmulO_eq]
  simp only [mulE_eq]
  split
  · rename_i h
    rw [isOne_eq _ h, one_mul]
  · ring

/-- PHIV8: `flatSumK` with the buckets and singles unreduced. -/
@[specialize] def flatSumK8 (ft : FCov) (fa : ℕ → FE2) (T : FE2) (fs fcv fov : ℕ → FE2) (SV CV OV : Array FE2)
    (key : ℕ → ℕ) (hw lw : ℕ → FE2) : FE2 :=
  (List.range 8).foldl (fun s β =>
    if (ft.bk.getD β default).gk.size = 0 then s else
    s + mulE (fa (β / 2)) (if β % 2 == 1 then mulE T (bkSumU (ft.bk.getD β default) ft.slots ft.als SV CV fs fcv)
      else bkSumU (ft.bk.getD β default) ft.slots ft.ods SV OV fs fov)) 0 +
    sglSumK8 ft.sgl fa fs key hw lw

theorem flatSumK8_eq (ft : FCov) (fa : ℕ → FE2) (T : FE2) (fs fcv fov : ℕ → FE2) (SV CV OV : Array FE2)
    (key : ℕ → ℕ) (hw lw : ℕ → FE2) :
    flatSumK8 ft fa T fs fcv fov SV CV OV key hw lw = flatSumK ft fa T fs fcv fov SV CV OV key hw lw := by
  unfold flatSumK8 flatSumK
  refine congrArg₂ (· + ·) ?_ (sglSumK8_eq _ _ _ _ _ _)
  refine congrArg (fun f => List.foldl f 0 (List.range 8)) (funext fun s => funext fun β => ?_)
  split
  · rfl
  · simp only [bkSumU_eq, mulE_eq]
    split <;> simp

/-- PHIV8: `rsumK` with `flatSumK8`. -/
@[specialize] def rsumK8 (rc : RCov) (fa : ℕ → FE2) (T : FE2) (fs fcv fov fw : ℕ → FE2) (ms bs : List FE2)
    (key : ℕ → ℕ) (hw lw : ℕ → FE2) : FE2 :=
  let needS := rc.fc.bk.any fun b => !b.byRow && decide (0 < b.gk.size)
  let needC := rc.fc.bk.any fun b => b.byRow
  let fl := flatSumK8 rc.fc fa T fs fcv fov (if needS = true then rc.fc.slots.map fs else #[])
    (if needC = true then rc.fc.als.map fcv else #[]) (if needC = true then rc.fc.ods.map fov else #[]) key hw lw
  if rc.wr.size = 0 then fl
  else
    let hz := hzip ms bs
    fl + rc.wr.foldl (fun s r => s + runSumH hz fa T fs fcv fw ms bs r) 0

theorem rsumK8_eq (rc : RCov) (fa : ℕ → FE2) (T : FE2) (fs fcv fov fw : ℕ → FE2) (ms bs : List FE2)
    (key : ℕ → ℕ) (hw lw : ℕ → FE2) :
    rsumK8 rc fa T fs fcv fov fw ms bs key hw lw = rsumK rc fa T fs fcv fov fw ms bs key hw lw := by
  unfold rsumK8 rsumK
  simp only [flatSumK8_eq]

/-- PHIV8: `CTpl.val2` with `rsumK8`. -/
@[specialize] def CTpl.val8 (k : CTpl) (fa : ℕ → FE2) (m b : List FE2) (ka kb : Array (Array FE2 × ℕ))
    (fcvR fwR hwR lwR : ℕ → FE2) : FE2 :=
  let T := twT b
  let bt := b.take k.bb
  let b0 := b.headD 0
  let xt := ka.getD k.a (#[], 0)
  let yt := kb.getD k.bb (#[], 0)
  let xlo : ℕ → FE2 := fun i => klF xt.1 xt.2 (m.take k.a) i
  let ytl : ℕ → FE2 := fun c => klF yt.1 yt.2 bt.tail c
  let ylo : ℕ → FE2 := fun w => mulE (if w % 2 = 1 then b0 else 1 + b0) (ytl (w / 2))
  let yod : ℕ → FE2 := fun c => ylo (2 * c + 1) + KT.mX (ylo (2 * c + 2))
  let hw0 : ℕ → FE2 := fun q => if q = 1 then b0 else 1 + b0
  let lw0 : ℕ → FE2 := fun w => ytl (w / 2)
  clsCombF2 k.n ((m.drop k.a).take k.L) ((b.drop k.bb).take k.L) (k.XH m) (k.YH b)
    (rsumK8 k.t0 fa T xlo ytl yod ylo (m.take k.a) bt.tail (· % 2) hw0 lw0)
    (rsumK8 k.t1 fa T xlo ytl yod ylo (m.take k.a) bt.tail (· % 2) hw0 lw0)
    (rsumK8 k.t2 fa T xlo fcvR (fun c => fwR (2 * c + 1) + KT.mX (fwR (2 * c + 2))) fwR (m.take k.a) b.tail (· / 2048)
      hwR lwR)

theorem CTpl.val8_eq (k : CTpl) (fa : ℕ → FE2) (m b : List FE2) (ka kb : Array (Array FE2 × ℕ))
    (fcvR fwR hwR lwR : ℕ → FE2) : k.val8 fa m b ka kb fcvR fwR hwR lwR = k.val2 fa m b ka kb fcvR fwR hwR lwR := by
  unfold CTpl.val8 CTpl.val2
  simp only [rsumK8_eq]

/-! ## Gathers -/

theorem goSum_zero (f : ℕ → FE2) (a b : ℕ) : goSum f a b 0 = ((List.range' a (b - a)).map f).sum := by
  rw [goSum_eq f b _ a 0 rfl, zero_add]

/-- A gather line, `coef t·xlo(lj[t])` unreduced: `cmulK`'s cheap shapes (`1`, `X`, a base-field coefficient)
reduced as before, a general coefficient unreduced. -/
@[inline] def GK.lineU (g : GK) (xlo : ℕ → FE2) (t : ℕ) : U6 :=
  let k := g.lk.getD t 0
  let x := xlo (g.lj.getD t 0)
  if k = 0 then U6.ofE x
  else
    let c := rdE g.cv (k - 1)
    if c.im.val = 0 ∨ (c.re.val = 0 ∧ c.im.val = 1) then U6.ofE (cmulK c x) else m2U c x

theorem GK.lineU_fin (g : GK) (xlo : ℕ → FE2) (t : ℕ) : (g.lineU xlo t).fin = g.cmul t (xlo (g.lj.getD t 0)) := by
  unfold GK.lineU
  rw [GK.cmul_eq, GK.coef]
  dsimp only
  split
  · rw [fin_ofE, one_mul]
  · split
    · rw [fin_ofE, cmulK_eq]
    · rw [fin_m2U_eq]

/-- **A gather column**, `ylo(cw[c])·Σ_t coef t·xlo(lj[t])` unreduced; a single line without the inner loop, the
lines of a longer column unreduced. -/
@[inline] def GK.colU (g : GK) (xlo ylo : ℕ → FE2) (c : ℕ) : U6 :=
  let s := g.co.getD c 0
  let e := g.co.getD (c + 1) 0
  let y := ylo (g.cw.getD c 0)
  m2U y (if s + 1 = e then g.cmul s (xlo (g.lj.getD s 0)) else sumU (g.lineU xlo) s e)

theorem GK.colU_fin (g : GK) (xlo ylo : ℕ → FE2) (c : ℕ) :
    (g.colU xlo ylo c).fin =
      ylo (g.cw.getD c 0) *
        goSum (fun t => g.cmul t (xlo (g.lj.getD t 0))) (g.co.getD c 0) (g.co.getD (c + 1) 0) 0 := by
  unfold GK.colU
  dsimp only
  rw [fin_m2U_eq]
  congr 1
  split
  · rename_i h
    rw [← h, goSum_zero, Nat.add_sub_cancel_left, List.range'_one, List.map_singleton, List.sum_singleton]
  · rw [sumU_eq, goSum_zero]
    simp only [GK.lineU_fin]

/-- **The gather kind's value, unreduced**: per row `fa(o)·xhi(x₀/2^l)·Σ_h yhi(gh[h])·Σ_c (column)`, each sum
finished once. -/
@[specialize] def GK.valW8 (g : GK) (fa xlo xhi ylo yhi : ℕ → FE2) : FE2 :=
  sumArrU g.rows fun r => m2U (mulE (fa r.2.1) (xhi (r.1 / 2 ^ g.l)))
    (sumU (fun h => m2U (yhi (g.gh.getD h 0)) (sumU (g.colU xlo ylo) (g.go.getD h 0) (g.go.getD (h + 1) 0)))
      r.2.2.1 r.2.2.2)

theorem GK.valW8_eq (g : GK) (fa xlo xhi ylo yhi : ℕ → FE2) :
    g.valW8 fa xlo xhi ylo yhi = g.valW fa xlo xhi ylo yhi := by
  unfold GK.valW8 GK.valW
  rw [sumArrU_eq, ← Array.foldl_toList, foldl_add_eq, zero_add]
  refine congrArg List.sum (List.map_congr_left fun r _ => ?_)
  simp only [fin_m2U_eq, sumU_eq, goSum_zero, GK.colU_fin, mulE_eq]

/-! ## Strided runs -/

/-- PHIV8: `SRunF.initS` on `mulE` (not the out-of-line `FE2.mul`), `2^hb·xr` once, each group's atoms unreduced. -/
def SRunF.initS8 (F : SRunF) (fa fx : ℕ → FE2) (m : List FE2) : Array (ℕ × FE2) :=
  let L := kerF (m.take F.p)
  let xo := 2 ^ F.hb * F.xr
  let W := F.tpl.map fun t => mulE t.1 (mulE (fa t.2.1) (fx (t.2.2 + xo)))
  F.grp.map fun g => (g.1, sumArrU g.2 fun ek => m2U (W.getD ek.1 0) (L.getD ek.2 0))

theorem SRunF.initS8_eq (F : SRunF) (fa fx : ℕ → FE2) (m : List FE2) : F.initS8 fa fx m = F.initS fa fx m := by
  unfold SRunF.initS8 SRunF.initS
  dsimp only
  simp only [mulE_eq]
  refine Array.map_congr_left fun g _ => ?_
  rw [sumArrU_eq, ← Array.foldl_toList, foldl_add_eq, zero_add]
  simp only [fin_m2U_eq]

theorem SRunF.xs_eq (F : SRunF) : F.toSRun.xs = (Array.range F.n).map (F.p + ·) := rfl

/-- PHIV8: `SRunF.valGS` without building `toSRun` (only its `xs` is read) and with `initS8`. -/
@[specialize] def SRunF.valGS8 (F : SRunF) (fa fx lo hi : ℕ → FE2) (M : ℕ) (m b : List FE2) : FE2 :=
  hgGo lo hi M (runAuto2B ⟨#[], m.toArray, b.toArray⟩ ((Array.range F.n).map (F.p + ·)) F.R
    (F.initS8 fa fx m)).toList 0 0 0

theorem SRunF.valGS8_eq (F : SRunF) (fa fx lo hi : ℕ → FE2) (M : ℕ) (m b : List FE2) :
    F.valGS8 fa fx lo hi M m b = F.valGS fa fx lo hi M m b := by
  unfold SRunF.valGS8 SRunF.valGS
  rw [SRunF.initS8_eq, SRunF.xs_eq]

/-- `sufT` with `2^(11 - K)` given. -/
theorem sufTs_eq (p : List FE2) (st : Array (Array FE2 × ℕ)) (hi : Array FE2 × ℕ) (K v : ℕ) :
    sufTs p st hi K (2 ^ (11 - K)) v = sufT p st hi K v := rfl

/-! ## Kernels by marginals

A kernel's marginal over its low (high) coordinates is the kernel of the other coordinates, since `eq` sums to `1`
over a cube (`sum_eqAtF`). The tables of the segments `m[K, 11)`, `m[K, 20)` (`K > 11`), `b[K, …)` and of the prefixes
`m[0, k)`, `b[1, k)` are therefore sums of the shared kernels `K11`, `MH`, `B11`, `BH`, `B12` (word `xor`s), not
`2^(len+1)` products each. -/

/-- `⟨r, i⟩ + Σ_{j<c} T[s + d·j]`, on the words. -/
def kSumSt (T : Array FE2) (s d : ℕ) : ℕ → UInt64 → UInt64 → FE2
  | 0, r, i => ⟨⟨r⟩, ⟨i⟩⟩
  | c + 1, r, i =>
    let v := T.getD (s + d * c) 0
    kSumSt T s d c (r ^^^ v.re.val) (i ^^^ v.im.val)

theorem kSumSt_eq (T : Array FE2) (s d : ℕ) : ∀ (c : ℕ) (r i : UInt64),
    kSumSt T s d c r i = ⟨⟨r⟩, ⟨i⟩⟩ + ∑ j ∈ Finset.range c, T.getD (s + d * j) 0
  | 0, r, i => by simp [kSumSt]
  | c + 1, r, i => by
    rw [kSumSt, kSumSt_eq T s d c, Finset.sum_range_succ,
      show (⟨⟨r ^^^ (T.getD (s + d * c) 0).re.val⟩, ⟨i ^^^ (T.getD (s + d * c) 0).im.val⟩⟩ : FE2) =
        ⟨⟨r⟩, ⟨i⟩⟩ + T.getD (s + d * c) 0 from rfl]
    abel

/-- The marginal over the low `k` coordinates: `n` entries, entry `j` the sum of the block `[j·2^k, (j+1)·2^k)`. -/
def kerMargLo (T : Array FE2) (k n : ℕ) : Array FE2 :=
  let p := 2 ^ k
  (Array.range n).map fun j => kSumSt T (j * p) 1 p 0 0

/-- The marginal over the high coordinates: `n` entries, entry `i` the sum of `T[i + n·j]`, `j < c`. -/
def kerMargHi (T : Array FE2) (n c : ℕ) : Array FE2 := (Array.range n).map fun i => kSumSt T i n c 0 0

theorem size_foldl_kerStep : ∀ (ρ : List FE2) (a0 : Array FE2),
    (ρ.foldl kerStep a0).size = a0.size * 2 ^ ρ.length
  | [], a0 => by simp
  | r :: ρ, a0 => by
    rw [List.foldl_cons, size_foldl_kerStep ρ, kerStep_eq, Array.size_append, Array.size_map, Array.size_map,
      List.length_cons, pow_succ]
    ring

theorem kerF_size (ρ : List FE2) : (kerF ρ).size = 2 ^ ρ.length := by
  rw [kerF, size_foldl_kerStep]
  simp

theorem kerF_getElem (ρ : List FE2) (i : ℕ) (h : i < (kerF ρ).size) : (kerF ρ)[i] = eqAtF ρ i := by
  rw [← kerF_getD ρ i (by rwa [kerF_size] at h)]
  simp [Array.getD, h]

theorem fe2_zero_mk : (⟨⟨0⟩, ⟨0⟩⟩ : FE2) = 0 := rfl

/-- **The low marginal of a kernel** is the kernel of the high coordinates. -/
theorem kerMargLo_kerF (ρ1 ρ2 : List FE2) : kerMargLo (kerF (ρ1 ++ ρ2)) ρ1.length (2 ^ ρ2.length) = kerF ρ2 := by
  apply Array.ext
  · simp [kerMargLo, kerF_size]
  · intro j h1 h2
    have hj : j < 2 ^ ρ2.length := by simpa [kerMargLo] using h1
    simp only [kerMargLo, Array.getElem_map, Array.getElem_range]
    rw [kSumSt_eq, fe2_zero_mk, zero_add, kerF_getElem]
    have hterm : ∀ i ∈ Finset.range (2 ^ ρ1.length),
        (kerF (ρ1 ++ ρ2)).getD (j * 2 ^ ρ1.length + 1 * i) 0 = eqAtF ρ1 i * eqAtF ρ2 j := by
      intro i hi
      have hi' : i < 2 ^ ρ1.length := Finset.mem_range.mp hi
      have hb : j * 2 ^ ρ1.length + 1 * i < 2 ^ (ρ1 ++ ρ2).length := by
        rw [List.length_append, pow_add]
        calc j * 2 ^ ρ1.length + 1 * i < j * 2 ^ ρ1.length + 2 ^ ρ1.length := by omega
          _ = 2 ^ ρ1.length * (j + 1) := by ring
          _ ≤ 2 ^ ρ1.length * 2 ^ ρ2.length := Nat.mul_le_mul_left _ hj
      rw [kerF_getD _ _ hb, eqAtF_append, eqAtF_mod ρ1,
        show (j * 2 ^ ρ1.length + 1 * i) % 2 ^ ρ1.length = i by
          rw [one_mul, Nat.mul_comm, Nat.mul_add_mod, Nat.mod_eq_of_lt hi'],
        show (j * 2 ^ ρ1.length + 1 * i) / 2 ^ ρ1.length = j by
          rw [one_mul, Nat.mul_comm, Nat.mul_add_div (by positivity), Nat.div_eq_of_lt hi', add_zero]]
    rw [Finset.sum_congr rfl hterm, ← Finset.sum_mul, Lvm6.sum_eqAtF, one_mul]

/-- **The high marginal of a kernel** is the kernel of the low coordinates. -/
theorem kerMargHi_kerF (ρ1 ρ2 : List FE2) : kerMargHi (kerF (ρ1 ++ ρ2)) (2 ^ ρ1.length) (2 ^ ρ2.length) = kerF ρ1 := by
  apply Array.ext
  · simp [kerMargHi, kerF_size]
  · intro i h1 h2
    have hi : i < 2 ^ ρ1.length := by simpa [kerMargHi] using h1
    simp only [kerMargHi, Array.getElem_map, Array.getElem_range]
    rw [kSumSt_eq, fe2_zero_mk, zero_add, kerF_getElem]
    have hterm : ∀ j ∈ Finset.range (2 ^ ρ2.length),
        (kerF (ρ1 ++ ρ2)).getD (i + 2 ^ ρ1.length * j) 0 = eqAtF ρ1 i * eqAtF ρ2 j := by
      intro j hj
      have hj' : j < 2 ^ ρ2.length := Finset.mem_range.mp hj
      have hb : i + 2 ^ ρ1.length * j < 2 ^ (ρ1 ++ ρ2).length := by
        rw [List.length_append, pow_add]
        calc i + 2 ^ ρ1.length * j < 2 ^ ρ1.length + 2 ^ ρ1.length * j := by omega
          _ = 2 ^ ρ1.length * (j + 1) := by ring
          _ ≤ 2 ^ ρ1.length * 2 ^ ρ2.length := Nat.mul_le_mul_left _ hj'
      rw [kerF_getD _ _ hb, eqAtF_append, eqAtF_mod ρ1,
        show (i + 2 ^ ρ1.length * j) % 2 ^ ρ1.length = i by rw [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hi],
        show (i + 2 ^ ρ1.length * j) / 2 ^ ρ1.length = j by
          rw [Nat.add_mul_div_left _ _ (by positivity), Nat.div_eq_of_lt hi, zero_add]]
    rw [Finset.sum_congr rfl hterm, ← Finset.mul_sum, Lvm6.sum_eqAtF, mul_one]

/-- A table of kernels by index `k < 22` (`segTab f` is the instance `g := kerF ∘ f`, and `kerTabS2`, `kbTabS` are
instances too, each equal after unfolding). -/
def kTabG (len : ℕ → ℕ) (g : ℕ → Array FE2) (ks : List ℕ) : Array (Array FE2 × ℕ) :=
  ((List.range 22).map fun k => if k ∈ ks then (g k, 2 ^ len k) else (#[], 0)).toArray

theorem kTabG_congr (len : ℕ → ℕ) (g g' : ℕ → Array FE2) (ks : List ℕ) (h : ∀ k, g k = g' k) :
    kTabG len g ks = kTabG len g' ks := by
  rw [show g = g' from funext h]

/-- The prefix kernels `m[0, k)`: `K11` at `11`, one step past it at `12`, its high marginal below `11`. -/
def gKa (ρ : List FE2) (K11 : Array FE2) (k : ℕ) : Array FE2 :=
  if k = 11 then K11 else if k = 12 ∧ 12 ≤ ρ.length then kerStep K11 (ρ.getD 11 0)
  else if k < 11 ∧ 11 ≤ ρ.length then kerMargHi K11 (2 ^ k) (2 ^ (11 - k)) else kerF (ρ.take k)

theorem gKa_eq (ρ : List FE2) (K11 : Array FE2) (hK : K11 = kerF (ρ.take 11)) (k : ℕ) :
    gKa ρ K11 k = if k = 11 then K11 else if k = 12 ∧ 12 ≤ ρ.length then kerStep K11 (ρ.getD 11 0)
      else kerF (ρ.take k) := by
  unfold gKa
  split
  · rfl
  · split
    · rfl
    · split
      · rename_i h
        have h1 : (ρ.take k).length = k := by simp; omega
        have h2 : ((ρ.take 11).drop k).length = 11 - k := by simp; omega
        have hs : ρ.take 11 = ρ.take k ++ (ρ.take 11).drop k := by
          conv_lhs => rw [← List.take_append_drop k (ρ.take 11)]
          rw [List.take_take, Nat.min_eq_left (by omega)]
        have hm := kerMargHi_kerF (ρ.take k) ((ρ.take 11).drop k)
        rw [h1, h2, ← hs] at hm
        rw [hK, hm]
      · rfl

/-- The twin-word prefix kernels `b[1, k)`: `B12` at `12`, its high marginal for `1 ≤ k < 12`. -/
def gKb (b : List FE2) (B12 : Array FE2) (k : ℕ) : Array FE2 :=
  if k = 12 then B12 else if 1 ≤ k ∧ k < 12 ∧ 12 ≤ b.length then kerMargHi B12 (2 ^ (k - 1)) (2 ^ (12 - k))
  else kerF (b.take k).tail

theorem gKb_eq (b : List FE2) (B12 : Array FE2) (hB : B12 = kerF (b.take 12).tail) (k : ℕ) :
    gKb b B12 k = if k = 12 then B12 else kerF (b.take k).tail := by
  unfold gKb
  split
  · rfl
  · split
    · rename_i h
      have ht : ∀ j, (b.take j).tail = (b.drop 1).take (j - 1) := fun j => by
        cases b with
        | nil => simp
        | cons x xs => cases j <;> simp
      have h1 : ((b.drop 1).take (k - 1)).length = k - 1 := by simp; omega
      have h2 : (((b.drop 1).take 11).drop (k - 1)).length = 12 - k := by simp; omega
      have hs : (b.drop 1).take 11 = (b.drop 1).take (k - 1) ++ ((b.drop 1).take 11).drop (k - 1) := by
        conv_lhs => rw [← List.take_append_drop (k - 1) ((b.drop 1).take 11)]
        rw [List.take_take, Nat.min_eq_left (by omega)]
      have hm := kerMargHi_kerF ((b.drop 1).take (k - 1)) (((b.drop 1).take 11).drop (k - 1))
      rw [h1, h2, ← hs] at hm
      rw [hB, ht, ht, show 12 - 1 = 11 from rfl, hm]
    · rfl

/-- The suffix-segment kernels `sfSeg p K`: low marginals of `P11 = eq(p[0, 11))` (`K ≤ 11`) or of
`PH = eq(p[11, …))` (`K > 11`). -/
def gSf (p : List FE2) (P11 PH : Array FE2) (K : ℕ) : Array FE2 :=
  if K ≤ 11 ∧ 11 ≤ p.length then kerMargLo P11 K (2 ^ (11 - K))
  else if 11 < K ∧ K ≤ p.length then kerMargLo PH (K - 11) (2 ^ (p.length - K)) else kerF (sfSeg p K)

theorem gSf_eq (p : List FE2) (P11 PH : Array FE2) (h11 : P11 = kerF (p.take 11)) (hH : PH = kerF (p.drop 11))
    (K : ℕ) : gSf p P11 PH K = kerF (sfSeg p K) := by
  unfold gSf
  split
  · rename_i h
    have h1 : (p.take K).length = K := by simp; omega
    have h2 : ((p.drop K).take (11 - K)).length = 11 - K := by simp; omega
    have hs : p.take 11 = p.take K ++ (p.drop K).take (11 - K) := by
      rw [← List.take_add, Nat.add_sub_cancel' h.1]
    have hm := kerMargLo_kerF (p.take K) ((p.drop K).take (11 - K))
    rw [h1, h2, ← hs] at hm
    rw [h11, hm, sfSeg, if_pos h.1]
  · split
    · rename_i _ h
      have h1 : ((p.drop 11).take (K - 11)).length = K - 11 := by simp; omega
      have h2 : (p.drop K).length = p.length - K := by simp
      have hs : p.drop 11 = (p.drop 11).take (K - 11) ++ p.drop K := by
        conv_lhs => rw [← List.take_append_drop (K - 11) (p.drop 11)]
        rw [List.drop_drop, Nat.add_sub_cancel' (by omega)]
      have hm := kerMargLo_kerF ((p.drop 11).take (K - 11)) (p.drop K)
      rw [h1, h2, ← hs] at hm
      rw [hH, hm, sfSeg, if_neg (by omega)]
    · rfl

/-! ## The evaluator -/

/-- PHIV8: `PT.kval7` with the gathers unreduced and the strided runs by `valGS8`. -/
@[specialize] def PT.kval8 (P : PT) (fa : ℕ → FE2) (m b : List FE2) (fw : ℕ → FE2)
    (ka kb mt sm sb : Array (Array FE2 × ℕ)) (B11 MH BH : Array FE2) : FE2 :=
  let MHp := kpair (m.drop 11) MH
  let BHp := kpair (b.drop 11) BH
  P.ak.foldl (fun s k => s + k.valK2 fa m b fw ka kb mt sm sb B11 MHp BHp) 0 +
    P.str.foldl (fun s F =>
      let K := F.p + F.n
      let sK := 2 ^ (11 - K)
      s + F.valGS8 fa (sufTs m sm MHp K sK) (sufL b sb F.n) (sufH b sb BHp F.n) (sufM F.n) m b) 0 +
    P.gk.foldl (fun s g =>
      let xt := ka.getD g.l (#[], 0)
      s + g.valW8 fa (fun i => klG xt i fun _ => eqAtF (m.take g.l) i) (sufT m sm MHp g.l) (fun w => B11.getD w 0)
        (fun v => klG BHp v fun _ => eqAtF (b.drop 11) v)) 0 +
    P.bk.foldl (fun s k => s + k.valW fa m b) 0

theorem PT.kval8_eq (P : PT) (fa : ℕ → FE2) (m b : List FE2) (fw : ℕ → FE2)
    (ka kb mt sm sb : Array (Array FE2 × ℕ)) (B11 MH BH : Array FE2) :
    P.kval8 fa m b fw ka kb mt sm sb B11 MH BH = P.kval7 fa m b fw ka kb mt sm sb B11 MH BH := by
  unfold PT.kval8 PT.kval7
  simp only [GK.valW8_eq, SRunF.valGS8_eq, sufTs_eq]
  rfl

/-- PHIV8: `PT.evalW7` with the unreduced twins and the kernel tables by marginals (`gKa`, `gKb`, `gSf`). -/
@[specialize] def PT.evalW8 (P : PT) (m b : List FE2) (fa fs fcv fw : ℕ → FE2) (K11 B12 B11 MH BH : Array FE2) :
    FE2 :=
  let ka := kTabG (fun k => (m.take k).length) (gKa m K11) (P.cls.toList.map CTpl.a ++
    (P.ak.toList.filterMap fun k => if k.a ≤ 11 then some k.a else none) ++ P.gk.toList.map GK.l)
  let kb := kTabG (fun k => (b.take k).tail.length) (gKb b B12)
    (P.cls.toList.map CTpl.bb ++ P.ak.toList.flatMap fun k => k.ds.toList.filter (· ≤ 12))
  let mt := segTab (midSeg b) (P.ak.toList.flatMap fun k => k.ds.toList.filter (12 < ·))
  let sm := kTabG (fun k => (sfSeg m k).length) (gSf m K11 MH) ((P.ak.toList.map fun k => k.a + k.L) ++
    P.gk.toList.map GK.l ++ P.str.toList.map fun F => F.p + F.n)
  let sb := kTabG (fun k => (sfSeg b k).length) (gSf b B11 BH)
    (P.ak.toList.flatMap (fun k => k.ds.toList.map (· + k.L)) ++ P.str.toList.map SRunF.n)
  P.cls.foldl (fun s k => s + k.val8 fa m b ka kb fcv fw (hwB b BH) (lwB B11)) 0 +
    P.kval8 fa m b fw ka kb mt sm sb B11 MH BH +
    rsumK8 P.rest fa (twT b) fs fcv (fun c => fw (2 * c + 1) + KT.mX (fw (2 * c + 2))) fw m b.tail (· / 2048)
      (hwB b BH) (lwB B11) +
    P.rk.valW fa fs fw fcv (twT b)

theorem PT.evalW8_eq (P : PT) (m b : List FE2) (fa fs fcv fw : ℕ → FE2) (K11 B12 B11 MH BH : Array FE2)
    (hK : K11 = kerF (m.take 11)) (hB : B12 = kerF (b.take 12).tail) (hB11 : B11 = kerF (b.take 11))
    (hMH : MH = kerF (m.drop 11)) (hBH : BH = kerF (b.drop 11)) :
    P.evalW8 m b fa fs fcv fw K11 B12 B11 MH BH = P.evalW7 m b fa fs fcv fw K11 B12 B11 MH BH := by
  unfold PT.evalW8 PT.evalW7
  rw [kTabG_congr _ _ _ _ (gKa_eq m K11 hK), kTabG_congr _ _ _ _ (gKb_eq b B12 hB),
    kTabG_congr _ _ _ _ (gSf_eq m K11 MH hK hMH), kTabG_congr _ _ _ _ (gSf_eq b B11 BH hB11 hBH)]
  simp only [CTpl.val8_eq, PT.kval8_eq, rsumK8_eq]
  rfl

/-- **PHIV8: the class evaluator of `Φ_Q` with its sums unreduced** (`PT.eval7` with the PHIV8 twins). -/
def PT.eval8 (P : PT) (pt : List FE2) : FE2 :=
  if pt.length = 43 then
    let a := pt.take 2
    let m := (pt.drop 2).take 20
    let b := pt.drop 22
    let at4 := ((List.range 4).map fun o => eqAtF a o).toArray
    let sm := mkSEqF m
    let st := mkSEqF b.tail
    let sb := mkSEqF b
    P.evalW8 m b (fun o => if h : o < at4.size then at4[o] else eqAtF a o) (fun x => sm.atI m x)
      (fun c => st.atI b.tail c) (fun y => sb.atI b y) sm.lo st.lo sb.lo sm.hi sb.hi
  else ((P.ents.map toIdx).map fun e => e.1 * eqAtF pt e.2).sum

/-- **`PT.eval8 = PT.eval`**, for every table and every point. -/
theorem PT.eval8_eq (P : PT) (pt : List FE2) : P.eval8 pt = P.eval pt := by
  rw [← PT.eval7_eq]
  unfold PT.eval8 PT.eval7
  split
  · dsimp only
    refine PT.evalW8_eq _ _ _ _ _ _ _ _ _ _ _ _ rfl ?_ rfl rfl rfl
    show kerF ((pt.drop 22).tail.take 11) = kerF ((pt.drop 22).take 12).tail
    cases pt.drop 22 <;> simp
  · rfl

end Lvm6.V
