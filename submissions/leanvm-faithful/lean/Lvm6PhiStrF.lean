-- New for lvm6 (WP STR): the factored form of a strided run. Atoms share their template entry's weight
-- `c·eq(κ, o)·eq(m_hi, row)` (rows off one small kernel) and their low slot bits off one kernel, so an atom costs
-- one product; the finals read `eq(b[n…], ·)` off two kernels shared by every run with the same `n`.
import Lvm6PhiStr
import Lvm6VPhiR3

/-!
# Factored strided runs

* **`SRunF`**: template entries `(c, o, r)` at slots `xh r = (xr·2^hb + r)·2^(p+n)`; atoms `(e, k)` (`k < 2^p`)
  grouped by initial word. `toSRun` is the plain run (`SRun`), `ents` its expansion.
* **`SRunF.valT`**: low kernel `eq(m[0,p), ·)`, row kernel `eq(m[p+n, p+n+hb), ·)`, one `eqAtF` for `xr`, three
  products per template entry, one per atom, the automaton, the finals through `fy`. **`SRunF.valT_eq`**.
* **`SRunF.valG`** (PHIV4): the finals grouped by their high word bits (`hgGo`, `hgGo_eq`), **`SRunF.valG_eq`**;
  **`SRunF.valGS`**: the row weights off a shared table (`initS`, **`SRunF.initS_eq`**, **`SRunF.valGS_eq`**).
* `autoStepP2B`, `runAuto2B` (MUL): `KT.autoStepP2`, `KT.runAuto2` on `m2B` (`runAuto2B_eq`); `valGS` runs them
  (`valT` and `valG` are statements' forms only).
* **`yTab`**, **`yTab_eq`**: `eq(b[n…], z)` as a low kernel over `b[n, 11)` times the high kernel over `b[11, 21)`.
-/

set_option autoImplicit false

namespace Lvm6.V

open Lvm Lvm.E2V Lvm.Typed.K Lvm.Typed.KT

/-- **A factored strided run.** -/
structure SRunF where
  p : ℕ
  n : ℕ
  R : ℕ
  hb : ℕ
  xr : ℕ
  tpl : Array (FE2 × ℕ × ℕ)
  grp : Array (ℕ × Array (ℕ × ℕ))
  deriving Inhabited

/-- The slot of template row `r` at iteration `0`, `k = 0`. -/
def SRunF.xh (F : SRunF) (r : ℕ) : ℕ := (F.xr * 2 ^ F.hb + r) * 2 ^ (F.p + F.n)

/-- An atom as the plain run's atom. -/
def SRunF.atom (F : SRunF) (ek : ℕ × ℕ) : FE2 × ℕ × ℕ :=
  let t := F.tpl.getD ek.1 default
  (t.1, t.2.1, F.xh t.2.2 + ek.2)

/-- **The plain run.** -/
def SRunF.toSRun (F : SRunF) : SRun := ⟨F.p, F.n, F.R, F.grp.map fun g => (g.1, g.2.map F.atom)⟩

/-- **Its entries.** -/
def SRunF.ents (F : SRunF) : List (FE2 × ℕ × ℕ × ℕ) := F.toSRun.ents

/-- **Its check.** -/
def SRunF.okB (F : SRunF) : Bool :=
  F.toSRun.okB && decide (F.p + F.n + F.hb ≤ 20) && F.tpl.toList.all (fun t => decide (t.2.2 < 2 ^ F.hb)) &&
    F.grp.toList.all fun g => g.2.toList.all fun ek => decide (ek.1 < F.tpl.size) && decide (ek.2 < 2 ^ F.p)

/-- The initial states, factored. -/
def SRunF.initT (F : SRunF) (fa : ℕ → FE2) (m : List FE2) : Array (ℕ × FE2) :=
  let L := kerF (m.take F.p)
  let mh := m.drop (F.p + F.n)
  let K := kerF (mh.take F.hb)
  let H := eqAtF (mh.drop F.hb) F.xr
  let W := F.tpl.map fun t => t.1 * (fa t.2.1 * (K.getD t.2.2 0 * H))
  F.grp.map fun g => (g.1, g.2.foldl (fun s ek => s + W.getD ek.1 0 * L.getD ek.2 0) 0)

/-- **The factored value** (`fy` the finals' weights `eq(b[n…], ·)`). -/
def SRunF.valT (F : SRunF) (fa fy : ℕ → FE2) (m b : List FE2) : FE2 :=
  (runAuto2 ⟨#[], m.toArray, b.toArray⟩ F.toSRun.xs F.R (F.initT fa m)).foldl (fun s cv => s + cv.2 * fy cv.1) 0

/-- PHIV4: `s + hi(h)·g + Σ v·lo(c % M)·hi(c / M)` over the list, one `hi` product per run of equal `c / M`
(`g` the open run's sum). -/
@[specialize] def hgGo (lo hi : ℕ → FE2) (M : ℕ) : List (ℕ × FE2) → ℕ → FE2 → FE2 → FE2
  | [], h, g, s => s + mulE (hi h) g
  | cv :: l, h, g, s =>
    if cv.1 / M = h then hgGo lo hi M l h (g + mulE cv.2 (lo (cv.1 % M))) s
    else hgGo lo hi M l (cv.1 / M) (mulE cv.2 (lo (cv.1 % M))) (s + mulE (hi h) g)

theorem hgGo_eq (lo hi : ℕ → FE2) (M : ℕ) : ∀ (l : List (ℕ × FE2)) (h : ℕ) (g s : FE2),
    hgGo lo hi M l h g s = s + hi h * g + (l.map fun cv => cv.2 * (lo (cv.1 % M) * hi (cv.1 / M))).sum
  | [], h, g, s => by simp [hgGo, mulE_eq]
  | cv :: l, h, g, s => by
    rw [hgGo]
    split
    · rename_i hc
      rw [hgGo_eq lo hi M l h, List.map_cons, List.sum_cons, mulE_eq, hc]
      ring
    · rw [hgGo_eq lo hi M l, List.map_cons, List.sum_cons, mulE_eq, mulE_eq]
      ring

/-- **The factored value, finals grouped** by `z / M` (`fy z = lo(z % M)·hi(z / M)`): one product a final, one a
group (`valT`: two a final). -/
@[specialize] def SRunF.valG (F : SRunF) (fa lo hi : ℕ → FE2) (M : ℕ) (m b : List FE2) : FE2 :=
  hgGo lo hi M (runAuto2 ⟨#[], m.toArray, b.toArray⟩ F.toSRun.xs F.R (F.initT fa m)).toList 0 0 0

theorem SRunF.valG_eq (F : SRunF) (fa lo hi fy : ℕ → FE2) (M : ℕ) (m b : List FE2)
    (hy : ∀ z, fy z = lo (z % M) * hi (z / M)) : F.valG fa lo hi M m b = F.valT fa fy m b := by
  unfold SRunF.valG SRunF.valT
  rw [hgGo_eq, ← Array.foldl_toList, foldl_sumF]
  simp [hy]

theorem kerF_getD (ρ : List FE2) (i : ℕ) (h : i < 2 ^ ρ.length) : (kerF ρ).getD i 0 = eqAtF ρ i := by
  rw [kerF_eq, eqKernelAF_getD]; simp [h]

theorem SRunF.initT_eq (F : SRunF) (hok : F.okB = true) (fa : ℕ → FE2) (m : List FE2) (hm : m.length = 20) :
    F.initT fa m = F.toSRun.init fa (eqAtF (m.take F.p)) (eqAtF (m.drop (F.p + F.n))) := by
  simp only [SRunF.okB, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true] at hok
  obtain ⟨⟨⟨-, hl⟩, htr⟩, hat⟩ := hok
  apply Array.ext'
  simp only [SRunF.initT, SRun.init, SRunF.toSRun, Array.toList_map, List.map_map]
  refine List.map_congr_left fun g hg => ?_
  simp only [Function.comp_apply, Prod.mk.injEq, true_and]
  rw [← Array.foldl_toList, ← Array.foldl_toList, Array.toList_map, foldl_sumF, foldl_sumF, List.map_map]
  congr 1
  refine congrArg List.sum (List.map_congr_left fun ek hek => ?_)
  obtain ⟨he, hk⟩ := hat g hg ek hek
  have hte : F.tpl.getD ek.1 default = F.tpl[ek.1] := by
    simp [Array.getD_eq_getD_getElem?, Array.getElem?_eq_getElem he]
  have hr : (F.tpl[ek.1]).2.2 < 2 ^ F.hb := htr _ (Array.getElem_mem_toList he)
  have hW : (F.tpl.map fun t => t.1 * (fa t.2.1 * ((kerF ((m.drop (F.p + F.n)).take F.hb)).getD t.2.2 0 *
      eqAtF ((m.drop (F.p + F.n)).drop F.hb) F.xr))).getD ek.1 0 =
      F.tpl[ek.1].1 * (fa F.tpl[ek.1].2.1 * ((kerF ((m.drop (F.p + F.n)).take F.hb)).getD F.tpl[ek.1].2.2 0 *
      eqAtF ((m.drop (F.p + F.n)).drop F.hb) F.xr)) := by
    simp [Array.getD_eq_getD_getElem?, Array.getElem?_map, Array.getElem?_eq_getElem he]
  have hlp : (m.take F.p).length = F.p := by simp; omega
  have hlh : ((m.drop (F.p + F.n)).take F.hb).length = F.hb := by simp; omega
  have h1 : (F.xh F.tpl[ek.1].2.2 + ek.2) % 2 ^ F.p = ek.2 := by
    unfold SRunF.xh
    rw [pow_add, show (F.xr * 2 ^ F.hb + F.tpl[ek.1].2.2) * (2 ^ F.p * 2 ^ F.n) =
      ((F.xr * 2 ^ F.hb + F.tpl[ek.1].2.2) * 2 ^ F.n) * 2 ^ F.p by ring, Nat.mul_add_mod_of_lt hk]
  have h2 : (F.xh F.tpl[ek.1].2.2 + ek.2) / 2 ^ (F.p + F.n) = F.xr * 2 ^ F.hb + F.tpl[ek.1].2.2 := by
    unfold SRunF.xh
    have : ek.2 < 2 ^ (F.p + F.n) := lt_of_lt_of_le hk (Nat.pow_le_pow_right (by norm_num) (by omega))
    rw [mul_comm, Nat.mul_add_div (by positivity), Nat.div_eq_of_lt this, Nat.add_zero]
  simp only [Function.comp_apply, SRunF.atom, hte, hW, kerF_getD _ _ (by rw [hlp]; exact hk), kerF_getD _ _ (by rw [hlh]; exact hr),
    h1, h2]
  rw [show F.xr * 2 ^ F.hb + F.tpl[ek.1].2.2 = F.tpl[ek.1].2.2 + 2 ^ F.hb * F.xr by ring,
    eq_split _ F.hb _ _ (by simp; omega) hr]
  ring

/-- **The factored run is the sum of its entries.** -/
theorem SRunF.valT_eq (F : SRunF) (hok : F.okB = true) (fa fy : ℕ → FE2) (m b : List FE2) (hm : m.length = 20)
    (hb : b.length = 21) (hy : ∀ z, fy z = eqAtF (b.drop F.n) z) :
    F.valT fa fy m b = (F.ents.map fun e => e.1 * (fa e.2.1 * (eqAtF m e.2.2.1 * eqAtF b e.2.2.2))).sum := by
  obtain rfl : fy = eqAtF (b.drop F.n) := funext hy
  have h0 := hok
  simp only [SRunF.okB, Bool.and_eq_true] at h0
  rw [SRunF.ents, ← SRun.valW_eq F.toSRun fa m b h0.1.1.1 hm hb]
  unfold SRunF.valT SRun.valW
  rw [F.initT_eq hok fa m hm]
  rfl

/-- PHIV4: the initial states with the row weight `eq(m.drop (p + n), r + 2^hb·xr)` read off a shared table (`fx`),
not a per-run kernel of `m[p+n, p+n+hb)` and an `eqAtF` of the rest. -/
def SRunF.initS (F : SRunF) (fa fx : ℕ → FE2) (m : List FE2) : Array (ℕ × FE2) :=
  let L := kerF (m.take F.p)
  let W := F.tpl.map fun t => t.1 * (fa t.2.1 * fx (t.2.2 + 2 ^ F.hb * F.xr))
  F.grp.map fun g => (g.1, g.2.foldl (fun s ek => s + W.getD ek.1 0 * L.getD ek.2 0) 0)

theorem SRunF.initS_eq (F : SRunF) (hok : F.okB = true) (fa fx : ℕ → FE2) (m : List FE2) (hm : m.length = 20)
    (hfx : ∀ z, fx z = eqAtF (m.drop (F.p + F.n)) z) : F.initS fa fx m = F.initT fa m := by
  simp only [SRunF.okB, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true] at hok
  obtain ⟨⟨⟨-, hl⟩, htr⟩, -⟩ := hok
  have hW : (F.tpl.map fun t => t.1 * (fa t.2.1 * fx (t.2.2 + 2 ^ F.hb * F.xr))) =
      F.tpl.map fun t => t.1 * (fa t.2.1 * ((kerF ((m.drop (F.p + F.n)).take F.hb)).getD t.2.2 0 *
        eqAtF ((m.drop (F.p + F.n)).drop F.hb) F.xr)) := by
    apply Array.map_congr_left
    intro t ht
    have hr : t.2.2 < 2 ^ F.hb := htr t (Array.mem_toList_iff.mpr ht)
    have hlh : ((m.drop (F.p + F.n)).take F.hb).length = F.hb := by simp; omega
    rw [hfx, eq_split _ F.hb _ _ (by simp; omega) hr, kerF_getD _ _ (by rw [hlh]; exact hr)]
  unfold SRunF.initS SRunF.initT
  simp only [hW]

/-! ## The automaton on `m2B` (MUL)

`KT.autoStepP2` and `KT.runAuto2` with `m2B` for `KT.m2` (`runAuto2B_eq`). -/

/-- `KT.autoStepP2` on `m2B`. -/
def autoStepP2B (R : ℕ) (rxk ryk : FE2) (cs : Array ℕ) (vs : Array FE2) : Array ℕ × Array FE2 := Id.run do
  let p := m2B rxk ryk
  let e00 := a2 (a2 (a2 1 rxk) ryk) p
  let e01 := a2 ryk p
  let e10 := a2 rxk p
  let e11 := p
  let n := cs.size
  let half (sh : ℕ) : Array ℕ × Array FE2 × Array ℕ := Id.run do
    let mut ts : Array ℕ := Array.mkEmpty n
    let mut xs : Array FE2 := Array.mkEmpty n
    let mut ks : Array ℕ := Array.mkEmpty n
    let mut i := 0
    while i < n do
      let c := cs.getD i 0
      let v := vs.getD i 0
      let d := c + sh
      if d % 2 == 0 then
        if i + 1 < n && cs.getD (i + 1) 0 == c + 1 then
          let v' := vs.getD (i + 1) 0
          ts := ts.push (d / 2); xs := xs.push (a2 v (m2B ryk (a2 v v'))); ks := ks.push 2
          i := i + 2
        else
          ts := ts.push (d / 2); xs := xs.push v; ks := ks.push 0
          i := i + 1
      else
        ts := ts.push (d / 2); xs := xs.push v; ks := ks.push 1
        i := i + 1
    return (ts, xs, ks)
  let (ta, va, ka) := half 0
  let (tb, vb, kb) := half R
  let wy (val : FE2) (k : ℕ) : FE2 := if k == 2 then val else if k == 0 then a2 val (m2B ryk val) else m2B ryk val
  let mut oc : Array ℕ := Array.mkEmpty (ta.size + tb.size)
  let mut ov : Array FE2 := Array.mkEmpty (ta.size + tb.size)
  let mut i := 0
  let mut j := 0
  while i < ta.size || j < tb.size do
    let a := ta.getD i 0
    let b := tb.getD j 0
    if j ≥ tb.size || (i < ta.size && a < b) then
      let x := va.getD i 0
      let k := ka.getD i 0
      oc := oc.push a; ov := ov.push (if k == 2 then a2 x (m2B rxk x) else m2B x (if k == 0 then e00 else e01))
      i := i + 1
    else if i ≥ ta.size || b < a then
      let x := vb.getD j 0
      let k := kb.getD j 0
      oc := oc.push b; ov := ov.push (if k == 2 then m2B rxk x else m2B x (if k == 0 then e10 else e11))
      j := j + 1
    else
      let x := va.getD i 0
      let y := vb.getD j 0
      let k := ka.getD i 0
      let k' := kb.getD j 0
      oc := oc.push a
      if k != 2 && k' != 2 then
        ov := ov.push (a2 (m2B x (if k == 0 then e00 else e01)) (m2B y (if k' == 0 then e10 else e11)))
      else
        let A := wy x k
        let B := wy y k'
        ov := ov.push (a2 A (m2B rxk (a2 A B)))
      i := i + 1
      j := j + 1
  return (oc, ov)

/-- `KT.runAuto2` on `m2B`. -/
def runAuto2B (P : Pt2) (xs : Array ℕ) (R : ℕ) (st : Array (ℕ × FE2)) : Array (ℕ × FE2) := Id.run do
  let mut cs := st.map (·.1)
  let mut vs := st.map (·.2)
  for k in [0:xs.size] do
    let r := autoStepP2B R (P.rx.getD (xs.getD k 0) 0) (P.ry.getD k 0) cs vs
    cs := r.1
    vs := r.2
  return (Array.range cs.size).map fun i ↦ (cs.getD i 0, vs.getD i 0)

theorem autoStepP2B_eq (R : ℕ) (rxk ryk : FE2) (cs : Array ℕ) (vs : Array FE2) :
    autoStepP2B R rxk ryk cs vs = autoStepP2 R rxk ryk cs vs := by
  unfold autoStepP2B autoStepP2; simp only [m2B_fun]

theorem runAuto2B_eq (P : Pt2) (xs : Array ℕ) (R : ℕ) (st : Array (ℕ × FE2)) :
    runAuto2B P xs R st = runAuto2 P xs R st := by
  unfold runAuto2B runAuto2; simp only [autoStepP2B_eq]

/-- **The grouped value off a shared row table** (`initS`). -/
@[specialize] def SRunF.valGS (F : SRunF) (fa fx lo hi : ℕ → FE2) (M : ℕ) (m b : List FE2) : FE2 :=
  hgGo lo hi M (runAuto2B ⟨#[], m.toArray, b.toArray⟩ F.toSRun.xs F.R (F.initS fa fx m)).toList 0 0 0

theorem SRunF.valGS_eq (F : SRunF) (hok : F.okB = true) (fa fx lo hi : ℕ → FE2) (M : ℕ) (m b : List FE2)
    (hm : m.length = 20) (hfx : ∀ z, fx z = eqAtF (m.drop (F.p + F.n)) z) :
    F.valGS fa fx lo hi M m b = F.valG fa lo hi M m b := by
  unfold SRunF.valGS SRunF.valG
  rw [runAuto2B_eq, F.initS_eq hok fa fx m hm hfx]

/-! ## The finals' weights -/

/-- **`eq(b[n…], ·)` off kernels**: `lo` over `b[n, 11)` (built per `n`), `hi` over `b[11, 21)` (shared). -/
def yTab (lo hi : Array FE2) (b : List FE2) (n z : ℕ) : FE2 :=
  lo.getD (z % 2 ^ (11 - n)) 0 * klF hi (2 ^ 10) (b.drop 11) (z / 2 ^ (11 - n))

theorem yTab_eq (b : List FE2) (hb : b.length = 21) (n : ℕ) (hn : n ≤ 11) (z : ℕ) :
    yTab (kerF ((b.drop n).take (11 - n))) (kerF (b.drop 11)) b n z = eqAtF (b.drop n) z := by
  have hl : ((b.drop n).take (11 - n)).length = 11 - n := by simp; omega
  have hd : (b.drop n).drop (11 - n) = b.drop 11 := by rw [List.drop_drop]; congr 1; omega
  unfold yTab
  rw [kerF_getD _ _ (by rw [hl]; exact Nat.mod_lt _ (by positivity)),
    klF_eq _ _ _ (Or.inl ⟨kerF_eq _, by simp [hb]⟩)]
  conv_rhs => rw [← List.take_append_drop (11 - n) (b.drop n), eqAtF_append, hl, hd,
    eqAtF_mod ((b.drop n).take (11 - n)), hl]

/-! ## A loop's factored run (a hint; `ptsCheck` checks the expansion) -/

/-- **The factored run of a loop's strided reads** `(c, o, r, w)`: slots `xb + r·2^(a+n) + k₁ + 2^a·k₂`, words
`w + R₁·k₁ + R·k₂`, rows below `2^hb`, `xb` aligned to `2^(a+n+hb)`. -/
def strLoopF (xb a n hb R₁ R : ℕ) (reads : List (FE2 × ℕ × ℕ × ℕ)) : SRunF :=
  let atoms := reads.zipIdx.flatMap fun (rd, e) => (List.range (2 ^ a)).map fun k => (rd.2.2.2 + R₁ * k, e, k)
  let srt := atoms.mergeSort fun u v => decide (u.1 ≤ v.1)
  let grp := srt.foldr (fun u (acc : List (ℕ × List (ℕ × ℕ))) =>
    match acc with
    | (s, l) :: rest => if s = u.1 then (s, u.2 :: l) :: rest else (u.1, [u.2]) :: acc
    | [] => [(u.1, [u.2])]) []
  ⟨a, n, R, hb, xb / 2 ^ (a + n + hb), (reads.map fun rd => (rd.1, rd.2.1, rd.2.2.1)).toArray,
    (grp.map fun g => (g.1, g.2.toArray)).toArray⟩

end Lvm6.V
