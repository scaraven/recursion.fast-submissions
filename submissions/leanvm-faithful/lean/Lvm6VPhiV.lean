-- New for lvm6 (WP-PHIV): the flat cover-form `Φ_Q`. TWT's `phiCov` (PHI-decision R1) on flat arrays: per bucket
-- the group keys, the member offsets and the members as arrays of indices, the products inlined on the words, the
-- group sums accumulated in three words (`X·Σ p₁` once per bucket), no allocation in the group loop. The flat
-- table reads back as a `Cov` (`FCov.toCov`), and the evaluator is `phiCov` of it (`phiFlat_eq`), so TWT's start-up
-- check (`covCheck`) on the decoded table gives `PhiOk`.
import Lvm6VTwT
import LvmE2VRingA
import Lvm6VMulB

/-!
# The flat cover-form `Φ_Q`

* `mulI`, `mulE`: `FK` and `FE2` products with the carry-less product inlined (`mulI_eq`: definitional; `mulE` is
  MUL's `m2B`, `mulE_eq` by `m2B_eq`).
* `FBk`, `FCov`: a bucket as flat index arrays (`byRow`: keys are slots, members cells; else the converse);
  `FCov.toCov` the `Cov` it stands for (the keys' values read off the key tables).
* `memRe`, `memIm`, `bkGo`, `bkSum`: a bucket's `Σ_g key_g·Σ_{members} val` (`bkSum_eq`).
* **`phiFlat`**, **`phiFlat_eq`**: `phiFlat ft pt = phiCov ft.toCov pt` for every flat table; **`phiOk_flat`**,
  **`tw_typedPhase6_flat`** under `covCheck ft.toCov (entsE …)`.
* `FCov.ofCov` (a hint): TWT's `mkCov` flattened.
-/

set_option autoImplicit false

namespace Lvm6.V

open LeanVM.Parameters Lvm Lvm.E2V Lvm.Typed Lvm.Loop

/-! ## Inlined products -/

/-- `FK.mul` inlined. -/
@[inline] def mulI (a b : FK) : FK :=
  let p := FK.clmul64 a.val b.val
  ⟨FK.reduce p.lo p.hi⟩

theorem mulI_eq (a b : FK) : mulI a b = a * b := rfl

/-- `FE2.mul` inlined: season 1's `m2` (three carry-less products, two reductions, `x·p₁` by a shift) on `bmul64`
low words and bit-reversed high words (`m2B`, 96 integer multiplies instead of 144). -/
@[inline] def mulE (a b : FE2) : FE2 := m2B a b

theorem mulE_eq (a b : FE2) : mulE a b = a * b := (m2B_eq a b).trans (Lvm.Typed.KT.m2_eq a b)

/-- `SEq.at` with the inlined product. -/
@[inline] def SEq.atI (s : SEq FE2) (ρ : List FE2) (i : ℕ) : FE2 :=
  if s.ok && decide (i < s.bound) then mulE (s.lo.getD (i % 2048) 0) (s.hi.getD (i / 2048) 0) else eqAtF ρ i

theorem SEq.atI_eq (s : SEq FE2) (ρ : List FE2) (i : ℕ) : s.atI ρ i = s.at ρ i := by
  unfold SEq.atI SEq.at
  rw [mulE_eq]

/-! ## The flat table -/

/-- **A flat bucket**: group `g` has key index `gk[g]` and members `mm[off[g] .. off[g+1])`. -/
structure FBk where
  byRow : Bool
  gk : Array ℕ
  off : Array ℕ
  mm : Array ℕ
  deriving Inhabited

/-- **The flat cover table**: TWT's `Cov` with flat buckets. -/
structure FCov where
  slots : Array ℕ
  als : Array ℕ
  ods : Array ℕ
  bk : Array FBk
  sgl : Array CSgl

/-- Group `g`'s member positions. -/
def FBk.mem (b : FBk) (g : ℕ) : List ℕ := List.range' (b.off.getD g 0) (b.off.getD (g + 1) 0 - b.off.getD g 0)

/-- The groups of a bucket as `CGrp`s, keys valued in `kk`, members in `mm`. -/
def FBk.grps (b : FBk) (kk mm : Array ℕ) : Array CGrp :=
  ((List.range b.gk.size).map fun g =>
    (⟨b.gk.getD g 0, kk.getD (b.gk.getD g 0) 0,
      ((b.mem g).map fun j => (⟨b.mm.getD j 0, mm.getD (b.mm.getD j 0) 0⟩ : CMem)).toArray⟩ : CGrp)).toArray

/-- The cell table of bucket `β`. -/
def FCov.cells (ft : FCov) (β : ℕ) : Array ℕ := if β % 2 == 1 then ft.als else ft.ods

/-- **The `Cov` a flat table stands for.** -/
def FCov.toCov (ft : FCov) : Cov :=
  ⟨ft.slots, ft.als, ft.ods,
    ((List.range 8).map fun β =>
      if (ft.bk.getD β default).byRow then (ft.bk.getD β default).grps ft.slots (ft.cells β) else #[]).toArray,
    ((List.range 8).map fun β =>
      if (ft.bk.getD β default).byRow then #[] else (ft.bk.getD β default).grps (ft.cells β) ft.slots).toArray,
    ft.sgl⟩

/-! ## The bucket loop -/

/-- A table value by index (`f` of the key past the table). -/
@[inline] def rd (vals : Array FE2) (keys : Array ℕ) (f : ℕ → FE2) (k : ℕ) : FE2 :=
  if h : k < vals.size then vals[k] else f (keys.getD k 0)

theorem rd_map (keys : Array ℕ) (f : ℕ → FE2) (k : ℕ) : rd (keys.map f) keys f k = f (keys.getD k 0) := by
  unfold rd
  split
  · rename_i h
    rw [Array.getElem_map]
    have h' : k < keys.size := by simpa using h
    simp [Array.getD, h']
  · rfl

/-- `Σ re` of the members `mk[j .. e)`. -/
@[specialize] def memRe (MV : Array FE2) (MK : Array ℕ) (fm : ℕ → FE2) (mk : Array ℕ) (e j : ℕ) (acc : FK) : FK :=
  if j < e then memRe MV MK fm mk e (j + 1) (acc + (rd MV MK fm (mk.getD j 0)).re) else acc
termination_by e - j

/-- `Σ im` of the members `mk[j .. e)`. -/
@[specialize] def memIm (MV : Array FE2) (MK : Array ℕ) (fm : ℕ → FE2) (mk : Array ℕ) (e j : ℕ) (acc : FK) : FK :=
  if j < e then memIm MV MK fm mk e (j + 1) (acc + (rd MV MK fm (mk.getD j 0)).im) else acc
termination_by e - j

/-- `Σ` of the members `mk[j .. e)` in one pass (both words). -/
@[specialize] def memGo (MV : Array FE2) (MK : Array ℕ) (fm : ℕ → FE2) (mk : Array ℕ) (e j : ℕ) (re im : FK) : FE2 :=
  if j < e then
    let v := rd MV MK fm (mk.getD j 0)
    memGo MV MK fm mk e (j + 1) (re + v.re) (im + v.im)
  else ⟨re, im⟩
termination_by e - j

/-- The accumulator `R + (I + x·T)·X`. -/
def accE (R I T : FK) : FE2 := ⟨R, I + FK.x * T⟩

/-- **A bucket's groups from `g` on**, the sum in three words. -/
@[specialize] def bkGo (b : FBk) (KV MV : Array FE2) (KK MK : Array ℕ) (fk fm : ℕ → FE2) (g : ℕ) (R I T : FK) : FE2 :=
  if g < b.gk.size then
    let s := b.off.getD g 0
    let e := b.off.getD (g + 1) 0
    let sm := memGo MV MK fm b.mm e s 0 0
    let sr := sm.re
    let si := sm.im
    let k := rd KV KK fk (b.gk.getD g 0)
    let p0 := mulI k.re sr
    let p1 := mulI k.im si
    let m := mulI (k.re + k.im) (sr + si)
    bkGo b KV MV KK MK fk fm (g + 1) (R + (p0 + p1)) (I + (m + p0 + p1)) (T + p1)
  else accE R I T
termination_by b.gk.size - g

/-- A bucket's sum, keys and members by `byRow`. -/
@[specialize] def bkSum (b : FBk) (SK WK : Array ℕ) (SV WV : Array FE2) (fs fw : ℕ → FE2) : FE2 :=
  if b.byRow then bkGo b SV WV SK WK fs fw 0 0 0 0 else bkGo b WV SV WK SK fw fs 0 0 0 0

section Loops

variable (MV : Array FE2) (MK : Array ℕ) (fm : ℕ → FE2) (mk : Array ℕ)

theorem memRe_eq (e : ℕ) : ∀ (d j : ℕ) (acc : FK), e - j = d →
    memRe MV MK fm mk e j acc = acc + ((List.range' j (e - j)).map fun j' => (rd MV MK fm (mk.getD j' 0)).re).sum
  | 0, j, acc, hd => by
    rw [memRe, if_neg (by omega), hd]; simp
  | d + 1, j, acc, hd => by
    rw [memRe, if_pos (by omega), memRe_eq e d (j + 1) _ (by omega),
      show e - j = (e - (j + 1)) + 1 by omega, List.range'_succ, List.map_cons, List.sum_cons, add_assoc]

theorem memIm_eq (e : ℕ) : ∀ (d j : ℕ) (acc : FK), e - j = d →
    memIm MV MK fm mk e j acc = acc + ((List.range' j (e - j)).map fun j' => (rd MV MK fm (mk.getD j' 0)).im).sum
  | 0, j, acc, hd => by
    rw [memIm, if_neg (by omega), hd]; simp
  | d + 1, j, acc, hd => by
    rw [memIm, if_pos (by omega), memIm_eq e d (j + 1) _ (by omega),
      show e - j = (e - (j + 1)) + 1 by omega, List.range'_succ, List.map_cons, List.sum_cons, add_assoc]

theorem fe2_sum_re {α : Type} (l : List α) (f : α → FE2) : ((l.map f).sum).re = (l.map fun x => (f x).re).sum := by
  induction l with
  | nil => rfl
  | cons x l ih => rw [List.map_cons, List.sum_cons, List.map_cons, List.sum_cons, ← ih]; rfl

theorem fe2_sum_im {α : Type} (l : List α) (f : α → FE2) : ((l.map f).sum).im = (l.map fun x => (f x).im).sum := by
  induction l with
  | nil => rfl
  | cons x l ih => rw [List.map_cons, List.sum_cons, List.map_cons, List.sum_cons, ← ih]; rfl

theorem memGo_eq (e : ℕ) : ∀ (d j : ℕ) (re im : FK), e - j = d →
    memGo MV MK fm mk e j re im = (⟨re, im⟩ : FE2) +
      ((List.range' j (e - j)).map fun j' => rd MV MK fm (mk.getD j' 0)).sum
  | 0, j, re, im, hd => by
    rw [memGo, if_neg (by omega), hd]; simp
  | d + 1, j, re, im, hd => by
    rw [memGo, if_pos (by omega), memGo_eq e d (j + 1) _ _ (by omega),
      show e - j = (e - (j + 1)) + 1 by omega, List.range'_succ, List.map_cons, List.sum_cons, ← add_assoc]
    rfl

/-- The members' sum. -/
theorem mem_pair (e s : ℕ) :
    (⟨memRe MV MK fm mk e s 0, memIm MV MK fm mk e s 0⟩ : FE2) =
      ((List.range' s (e - s)).map fun j => rd MV MK fm (mk.getD j 0)).sum := by
  rw [memRe_eq MV MK fm mk e _ s 0 rfl, memIm_eq MV MK fm mk e _ s 0 rfl, zero_add, zero_add, ← fe2_sum_re,
    ← fe2_sum_im]

end Loops

theorem fe2_mul_def (a b : FE2) : a * b =
    ⟨a.re * b.re + a.im * b.im, (a.re + a.im) * (b.re + b.im) + a.re * b.re + a.im * b.im + FK.x * (a.im * b.im)⟩ :=
  rfl

theorem fe2_add_def (a b : FE2) : a + b = ⟨a.re + b.re, a.im + b.im⟩ := rfl

theorem accE_step (R I T : FK) (k s : FE2) :
    accE (R + (mulI k.re s.re + mulI k.im s.im))
        (I + (mulI (k.re + k.im) (s.re + s.im) + mulI k.re s.re + mulI k.im s.im)) (T + mulI k.im s.im) =
      accE R I T + k * s := by
  show (⟨R + (k.re * s.re + k.im * s.im),
      I + ((k.re + k.im) * (s.re + s.im) + k.re * s.re + k.im * s.im) + FK.x * (T + k.im * s.im)⟩ : FE2) =
    ⟨R + (k.re * s.re + k.im * s.im),
      (I + FK.x * T) + ((k.re + k.im) * (s.re + s.im) + k.re * s.re + k.im * s.im + FK.x * (k.im * s.im))⟩
  congr 1
  ring

theorem accE_zero : accE 0 0 0 = 0 := by
  show (⟨0, 0 + FK.x * 0⟩ : FE2) = ⟨0, 0⟩
  rw [mul_zero, add_zero]

theorem bkGo_eq (b : FBk) (KV MV : Array FE2) (KK MK : Array ℕ) (fk fm : ℕ → FE2) :
    ∀ (d g : ℕ) (R I T : FK), b.gk.size - g = d →
      bkGo b KV MV KK MK fk fm g R I T = accE R I T + ((List.range' g (b.gk.size - g)).map fun g' =>
        rd KV KK fk (b.gk.getD g' 0) * ((b.mem g').map fun j => rd MV MK fm (b.mm.getD j 0)).sum).sum
  | 0, g, R, I, T, hd => by
    rw [bkGo, if_neg (by omega), hd]; simp
  | d + 1, g, R, I, T, hd => by
    rw [bkGo, if_pos (by omega)]
    simp only
    have hs := memGo_eq MV MK fm b.mm (b.off.getD (g + 1) 0) _ (b.off.getD g 0) 0 0 rfl
    rw [show (⟨0, 0⟩ : FE2) = 0 from rfl, zero_add] at hs
    set sm := memGo MV MK fm b.mm (b.off.getD (g + 1) 0) (b.off.getD g 0) 0 0
    have := accE_step R I T (rd KV KK fk (b.gk.getD g 0)) sm
    rw [bkGo_eq b KV MV KK MK fk fm d (g + 1) _ _ _ (by omega), this, show b.gk.size - g = (b.gk.size - (g + 1)) + 1 by omega,
      List.range'_succ, List.map_cons, List.sum_cons, hs]
    simp only [FBk.mem, add_assoc]

/-- **A bucket's sum**: `Σ_g key_g·Σ_{members} val`. -/
theorem bkGo_zero (b : FBk) (KV MV : Array FE2) (KK MK : Array ℕ) (fk fm : ℕ → FE2) :
    bkGo b KV MV KK MK fk fm 0 0 0 0 = ((List.range b.gk.size).map fun g =>
      rd KV KK fk (b.gk.getD g 0) * ((b.mem g).map fun j => rd MV MK fm (b.mm.getD j 0)).sum).sum := by
  rw [bkGo_eq b KV MV KK MK fk fm _ 0 0 0 0 rfl, List.range_eq_range', Nat.sub_zero, accE_zero, zero_add]

/-! ## The evaluation -/

/-- The sum over the buckets and the singles (as `covSum`, the buckets flat). -/
def flatSum (ft : FCov) (a : List FE2) (T : FE2) (fsv fcv fov fy : ℕ → FE2) (SV CV OV : Array FE2) : FE2 :=
  (List.range 8).foldl (fun s β =>
    let al := β % 2 == 1
    let b := ft.bk.getD β default
    let S := if al then bkSum b ft.slots ft.als SV CV fsv fcv else bkSum b ft.slots ft.ods SV OV fsv fov
    s + eqAtF a (β / 2) * ((if al then T else 1) * S)) 0 +
    ft.sgl.foldl (fun s e => s + e.c * (eqAtF a e.o * (fsv e.x * fy e.y))) 0

/-- The three tables of a point (`slots`, aligned cells, odd cells). -/
def flatTabs (ft : FCov) (mid bt b : List FE2) : Array FE2 × Array FE2 × Array FE2 :=
  let sm := mkSEq mid
  let st := mkSEq bt
  let sb := mkSEq b
  (ft.slots.map fun x => sm.atI mid x, ft.als.map fun c => st.atI bt c,
    ft.ods.map fun c => sb.atI b (2 * c + 1) + xF * sb.atI b (2 * c + 2))

/-- **The flat cover-form `Φ_Q`** (`phiCov` of the decoded table at a point not of 43 coordinates). -/
def phiFlat (ft : FCov) (pt : List FE2) : FE2 :=
  if pt.length = 43 then
    let a := pt.take 2
    let mid := (pt.drop 2).take 20
    let b := pt.drop 22
    let bt := b.tail
    let b0 := b.headD 0
    let sm := mkSEq mid
    let st := mkSEq bt
    let sb := mkSEq b
    let tabs := flatTabs ft mid bt b
    flatSum ft a ((1 + b0) + xF * b0) (fun x => sm.at mid x) (fun c => st.at bt c)
      (fun c => sb.at b (2 * c + 1) + xF * sb.at b (2 * c + 2)) (fun y => sb.at b y) tabs.1 tabs.2.1 tabs.2.2
  else phiCov ft.toCov pt

/-! ## Correctness -/

theorem getD_mapRange {α : Type} (n : ℕ) (f : ℕ → α) (d : α) (β : ℕ) (hβ : β < n) :
    ((List.range n).map f).toArray.getD β d = f β := by
  simp [Array.getD, hβ]

theorem foldl_congr_mem {α β : Type} (f g : α → β → α) (l : List β) (h : ∀ x ∈ l, ∀ s, f s x = g s x) :
    ∀ a, l.foldl f a = l.foldl g a := by
  induction l with
  | nil => intro a; rfl
  | cons x l ih =>
    intro a
    rw [List.foldl_cons, List.foldl_cons, h x (by simp) a]
    exact ih (fun y hy s => h y (by simp [hy]) s) _

/-- A bucket's groups summed as `grpSum` sums them. -/
theorem grps_sum (b : FBk) (kk mm : Array ℕ) (fk fm : ℕ → FE2) :
    ((b.grps kk mm).toList.map fun g => fk g.v * (g.mem.toList.map fun m => fm m.v).sum).sum =
      ((List.range b.gk.size).map fun g =>
        rd (kk.map fk) kk fk (b.gk.getD g 0) * ((b.mem g).map fun j => rd (mm.map fm) mm fm (b.mm.getD j 0)).sum).sum := by
  simp only [FBk.grps, List.toList_toArray, List.map_map, Function.comp_def, rd_map]

theorem covSum_toCov (ft : FCov) (a : List FE2) (T : FE2) (fsv fcv fov fy : ℕ → FE2) :
    covSum ft.toCov a T fsv fcv fov fy (ft.slots.map fsv) (ft.als.map fcv) (ft.ods.map fov) =
      flatSum ft a T fsv fcv fov fy (ft.slots.map fsv) (ft.als.map fcv) (ft.ods.map fov) := by
  unfold covSum flatSum
  refine congrArg₂ (· + ·) ?_ rfl
  refine foldl_congr_mem _ _ _ (fun β hβ s => ?_) 0
  have hβ8 : β < 8 := List.mem_range.mp hβ
  have key : ∀ (kk mm : Array ℕ) (fk fm : ℕ → FE2) (rows cols : Array CGrp),
      grpSum kk (kk.map fk) fk mm (mm.map fm) fm rows cols =
        (rows.toList.map fun g => fk g.v * (g.mem.toList.map fun m => fm m.v).sum).sum +
          (cols.toList.map fun g => fm g.v * (g.mem.toList.map fun m => fk m.v).sum).sum := by
    intro kk mm fk fm rows cols
    simp only [grpSum, memT_eq, lk_eq, arr_foldl_sum]
  rcases Bool.eq_false_or_eq_true (β % 2 == 1) with hal | hal <;>
    by_cases hb : (ft.bk.getD β default).byRow <;>
    simp only [FCov.toCov, getD_mapRange 8 _ _ β hβ8, FCov.cells, hal, hb, if_true, if_false, Bool.false_eq_true,
      bkSum, key, bkGo_zero, ← grps_sum] <;> simp

/-- **The flat evaluator is `phiCov` of its decoded table.** -/
theorem phiFlat_eq (ft : FCov) (pt : List FE2) : phiFlat ft pt = phiCov ft.toCov pt := by
  unfold phiFlat phiCov
  split
  · unfold covEval
    simp only [flatTabs, SEq.atI_eq]
    rw [← covSum_toCov]
    rfl
  · rfl

/-- **The flat `Φ_Q` computes `Φ_Q`** once TWT's start-up check passed on the decoded table. -/
theorem phiOk_flat {Q : Program} {lay : Lay} {ft : FCov} (h : covCheck ft.toCov (Lvm6.Ty.entsE Q lay) = true) :
    PhiOk (phiFlat ft) Q lay := fun pt => by rw [phiFlat_eq]; exact phiCov_ents _ _ h pt

/-- **The typed phase with the flat `Φ_Q`.** -/
theorem tw_typedPhase6_flat (sh : Lvm6.Shape) (i : Lvm6.Ty.TyInst6) (hlay : Lvm6.QD.TyLayOk i.Ti) {ft : FCov}
    (h : covCheck ft.toCov (Lvm6.Ty.entsE i.Ti.Q i.Ti.lay) = true) :
    TwinF (List.map FClaim.dec) (Lvm6.Ty.typedPhase6 sh i) (fTypedPhase6 sh i (phiFlat ft)) :=
  tw_typedPhase6 sh i hlay (phiOk_flat h)

/-! ## The flat table of a cover (a hint) -/

/-- A bucket's groups flattened. -/
def flatGrps (byRow : Bool) (gs : Array CGrp) : FBk :=
  let r := gs.foldl (fun (st : Array ℕ × Array ℕ × Array ℕ) g =>
    (st.1.push g.k, st.2.1.push st.2.2.size, g.mem.foldl (fun mk m => mk.push m.k) st.2.2)) (#[], #[], #[])
  ⟨byRow, r.1, r.2.1.push r.2.2.size, r.2.2⟩

/-- **The flat table of a cover** (not proved: the check on `toCov` decides). -/
def FCov.ofCov (c : Cov) : FCov :=
  ⟨c.slots, c.als, c.ods,
    ((List.range 8).map fun β =>
      let rows := c.rowsB.getD β #[]
      if rows.size = 0 then flatGrps false (c.colsB.getD β #[]) else flatGrps true rows).toArray, c.sgl⟩

end Lvm6.V
