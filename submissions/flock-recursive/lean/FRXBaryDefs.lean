-- New for `flock-recursive` (BLUEPRINT §6.2 step 4; S-H2 Part 11 §4 step 4; stage S-H2, track
-- L-ext).
import FRXBflyDefs

/-!
# The barycentric interpolation: the pure form and the program

`interpF pt J y s` (`FRRSEval`) is the Lagrange interpolation of `y` on the points `pt J` at
`pt s`. The machine computes it in barycentric form (S-H2 Part 11 §4 step 4):

* off `J`: `interpF pt J y s = ℓ(s) · Σ_{i ∈ J} y i · w_i · (pt s − pt i)⁻¹`, with
  `ℓ(s) = Π_{m ∈ J} (pt s − pt m)` and `w_i = (Π_{m ∈ J∖i} (pt i − pt m))⁻¹` (`interpF_bary`);
* on `J`: `interpF pt J y s = y s` (`interpF_self`).

The machine tells the two apart by `ℓ(s) = 0` (`pt` injective). Over `F`, with `J` the list
`Jl = J₀ … J_{k−1}` (the agreement scan's), the machine's value is `baryVal` and
**`baryVal_eq`** proves it is `interpF D Jl.toFinset y s` for `s < 2^20`.

The program (`baryIR`) works coordinate-wise over `F`: a column holds `C` elements of `F` (level
0: 64; levels 1–4: the 16 `F`-coordinates of 8 `K` elements), element `c` of position `j` at
`cb + cs·j + 2c`. Its phases:

1. `djIR`: `DJ[t] := D(J_t)` (`alphaIR` on the basis table's row 0);
2. `wIR`: `W[t] := (Π_{m ≠ t} (DJ[t] + DJ[m]))⁻¹`;
3. per target `s < k` (`sBody`): `D(s)`; `E[t] := W[t] · (D(s) + DJ[t])⁻¹` and
   `ℓ := Π_t (D(s) + DJ[t])`; per coordinate `c`: `acc := Σ_t y_c(J_t) E[t]` (registers only),
   then `out[c][s] := (ℓ = 0 ? y_c(s) : ℓ · acc)` at `ob + 2(c·k + s)`.
-/

namespace FR.X

open RecursionFast FR Finset

/-! ## The pure form -/

section Pure

variable {L : Type*} [Field L] {M : Type*} [Field M] [Algebra L M]

/-- **On `J`, the interpolation returns the value.** -/
theorem interpF_self {pt : ℕ → L} {J : Finset ℕ} (hJ : Set.InjOn pt J) (y : ℕ → M) {s : ℕ}
    (hs : s ∈ J) : interpF pt J y s = y s := by
  unfold interpF
  rw [Finset.sum_eq_single s]
  · rw [Finset.prod_eq_one, mul_one]
    intro m hm
    obtain ⟨hne, hmJ⟩ := Finset.mem_erase.1 hm
    have : algebraMap L M (pt s) - algebraMap L M (pt m) ≠ 0 := by
      rw [sub_ne_zero]
      exact fun h => hne (hJ hmJ hs ((algebraMap L M).injective h).symm)
    exact div_self this
  · intro i hi hne
    rw [Finset.prod_eq_zero (i := s) (Finset.mem_erase.2 ⟨Ne.symm hne, hs⟩) (by simp), mul_zero]
  · intro h; exact absurd hs h

/-- **Off `J`, the interpolation is barycentric**: `ℓ(s) · Σ_i y i · w_i (pt s − pt i)⁻¹`. -/
theorem interpF_bary {pt : ℕ → L} {J : Finset ℕ} {s : ℕ} (hs : ∀ m ∈ J, pt s ≠ pt m)
    (y : ℕ → M) :
    interpF pt J y s = algebraMap L M (∏ m ∈ J, (pt s - pt m)) *
      ∑ i ∈ J, y i * algebraMap L M ((∏ m ∈ J.erase i, (pt i - pt m))⁻¹ * (pt s - pt i)⁻¹) := by
  unfold interpF
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun i hi => ?_
  have hsi : pt s - pt i ≠ 0 := sub_ne_zero.2 (hs i hi)
  have hl : ∏ m ∈ J, (pt s - pt m) = (pt s - pt i) * ∏ m ∈ J.erase i, (pt s - pt m) :=
    (Finset.mul_prod_erase J (fun m => pt s - pt m) hi).symm
  have e : ∏ m ∈ J.erase i, (algebraMap L M (pt s) - algebraMap L M (pt m)) /
      (algebraMap L M (pt i) - algebraMap L M (pt m)) =
      algebraMap L M (∏ m ∈ J.erase i, (pt s - pt m) / (pt i - pt m)) := by
    rw [map_prod]; simp [map_sub, map_div₀]
  rw [e, Finset.prod_div_distrib, hl]
  rw [mul_left_comm, ← map_mul]
  congr 2
  field_simp

end Pure

/-! ## The machine's value over `F`, against `interpF` -/

/-- `D(J_t)` for the list `Jl`. -/
def dj (Jl : List ℕ) (t : ℕ) : F := D (Jl.getD t 0)

/-- **The weight** `W[t] = (Π_{m < k, m ≠ t} (DJ[t] + DJ[m]))⁻¹`, as the machine's product
(`m = t` contributes `1`). -/
def wgt (Jl : List ℕ) (k t : ℕ) : F :=
  (∏ m ∈ range k, if m = t then 1 else dj Jl t + dj Jl m)⁻¹

/-- `ℓ(s) = Π_{t < k} (D s + DJ[t])`. -/
def ellS (Jl : List ℕ) (k s : ℕ) : F := ∏ t ∈ range k, (D s + dj Jl t)

/-- `E[t] = W[t] · (D s + DJ[t])⁻¹`. -/
def eAt (Jl : List ℕ) (k s t : ℕ) : F := wgt Jl k t * (D s + dj Jl t)⁻¹

/-- **The machine's value** at target `s` for the values `y`: `y s` when `ℓ(s) = 0`, else
`ℓ(s) · Σ_t y(J_t) E[t]`. -/
def baryVal (Jl : List ℕ) (k s : ℕ) (y : ℕ → F) : F :=
  if ellS Jl k s = 0 then y s else ellS Jl k s * ∑ t ∈ range k, y (Jl.getD t 0) * eAt Jl k s t

theorem sub_eq_add_F (a b : F) : a - b = a + b := rfl

theorem toFinset_eq_image (Jl : List ℕ) :
    Jl.toFinset = (range Jl.length).image (fun t => Jl.getD t 0) := by
  ext x
  simp only [List.mem_toFinset, Finset.mem_image, Finset.mem_range, List.mem_iff_getElem]
  constructor
  · rintro ⟨t, ht, rfl⟩; exact ⟨t, ht, by rw [List.getD_eq_getElem]⟩
  · rintro ⟨t, ht, rfl⟩; exact ⟨t, ht, by rw [List.getD_eq_getElem]⟩

theorem getD_injOn {Jl : List ℕ} (hnd : Jl.Nodup) :
    Set.InjOn (fun t => Jl.getD t 0) (range Jl.length : Set ℕ) := fun a ha b hb h => by
  simp only [coe_range, Set.mem_Iio] at ha hb
  simp only [List.getD_eq_getElem _ _ ha, List.getD_eq_getElem _ _ hb] at h
  exact (hnd.getElem_inj_iff).1 h

theorem prod_toFinset {Jl : List ℕ} (hnd : Jl.Nodup) (f : ℕ → F) :
    ∏ m ∈ Jl.toFinset, f m = ∏ t ∈ range Jl.length, f (Jl.getD t 0) := by
  rw [toFinset_eq_image, Finset.prod_image (getD_injOn hnd)]

theorem sum_toFinset {Jl : List ℕ} (hnd : Jl.Nodup) (f : ℕ → F) :
    ∑ m ∈ Jl.toFinset, f m = ∑ t ∈ range Jl.length, f (Jl.getD t 0) := by
  rw [toFinset_eq_image, Finset.sum_image (getD_injOn hnd)]

theorem prod_erase_ite {J : Finset ℕ} {i : ℕ} (hi : i ∈ J) (f : ℕ → F) :
    ∏ m ∈ J.erase i, f m = ∏ m ∈ J, if m = i then 1 else f m := by
  rw [← Finset.mul_prod_erase J _ hi, if_pos rfl, one_mul]
  exact Finset.prod_congr rfl fun m hm => by rw [if_neg (Finset.mem_erase.1 hm).1]

/-- **The machine's value is the interpolation** (`J ⊆ [0, 2^20)` listed without repeats,
`s < 2^20`). -/
theorem baryVal_eq {Jl : List ℕ} (hnd : Jl.Nodup) (hJ : ∀ j ∈ Jl, j < nMax) {s : ℕ}
    (hs : s < nMax) (y : ℕ → F) :
    baryVal Jl Jl.length s y = interpF D Jl.toFinset y s := by
  have hinj : Set.InjOn D (Jl.toFinset : Set ℕ) := fun a ha b hb h =>
    D_injOn_nMax (Set.mem_Iio.2 (hJ a (List.mem_toFinset.1 ha)))
      (Set.mem_Iio.2 (hJ b (List.mem_toFinset.1 hb))) h
  have hget : ∀ t < Jl.length, Jl.getD t 0 ∈ Jl := fun t ht => by
    rw [List.getD_eq_getElem _ _ ht]; exact List.getElem_mem ht
  by_cases hsJ : s ∈ Jl
  · obtain ⟨t, ht, hts⟩ := List.mem_iff_getElem.1 hsJ
    have h0 : ellS Jl Jl.length s = 0 := by
      refine Finset.prod_eq_zero (i := t) (Finset.mem_range.2 ht) ?_
      rw [dj, List.getD_eq_getElem _ _ ht, hts, ← sub_eq_add_F, sub_self]
    rw [baryVal, if_pos h0, interpF_self hinj y (List.mem_toFinset.2 hsJ)]
  · have hne : ∀ m ∈ Jl.toFinset, D s ≠ D m := fun m hm h => hsJ (by
      have := D_injOn_nMax (Set.mem_Iio.2 hs) (Set.mem_Iio.2 (hJ m (List.mem_toFinset.1 hm))) h
      rw [this]; exact List.mem_toFinset.1 hm)
    have h0 : ellS Jl Jl.length s ≠ 0 := by
      refine Finset.prod_ne_zero_iff.2 fun t ht => ?_
      rw [dj, ← sub_eq_add_F, sub_ne_zero]
      exact hne _ (List.mem_toFinset.2 (hget t (Finset.mem_range.1 ht)))
    rw [baryVal, if_neg h0, interpF_bary hne, Algebra.algebraMap_self]
    simp only [RingHom.id_apply]
    rw [prod_toFinset hnd, sum_toFinset hnd]
    refine congrArg₂ _ rfl (Finset.sum_congr rfl fun t ht => ?_)
    have ht' := Finset.mem_range.1 ht
    rw [eAt, wgt,
      prod_erase_ite (List.mem_toFinset.2 (hget t ht')), prod_toFinset hnd]
    congr 3
    refine Finset.prod_congr rfl fun m hm => ?_
    have hm' := Finset.mem_range.1 hm
    by_cases hmt : m = t
    · rw [if_pos hmt, if_pos (by rw [hmt])]
    · rw [if_neg hmt, if_neg (fun h => hmt ((hnd.getElem_inj_iff).1 (by
        rwa [List.getD_eq_getElem _ _ hm', List.getD_eq_getElem _ _ ht'] at h))), dj, dj]
      rfl

/-! ## Registers (`216 …`) -/

/-- `D(s)` or `DJ[t]`. -/ def fDs : ℕ := 216
/-- `ℓ`. -/ def fLp : ℕ := 218
/-- `D(s) + DJ[t]`. -/ def fDd : ℕ := 220
/-- Its inverse. -/ def fIv : ℕ := 222
/-- `E[t]`. -/ def fEt : ℕ := 224
/-- A product. -/ def fPr : ℕ := 226
/-- A column value. -/ def fY : ℕ := 228
/-- The accumulator. -/ def fAc : ℕ := 230
/-- A loaded element. -/ def fX : ℕ := 232
/-- `t` (or `m`'s partner). -/ def bT : ℕ := 236
/-- `m`. -/ def bM : ℕ := 237
/-- `s`. -/ def bS : ℕ := 238
/-- `c`. -/ def bCi : ℕ := 239
/-- An address. -/ def bA : ℕ := 240
/-- Its successor. -/ def bA1 : ℕ := 241
/-- A column address. -/ def bJ : ℕ := 242
/-- Constant scratch. -/ def bK : ℕ := 243
/-- A flag. -/ def bZ : ℕ := 244
/-- The outer loop's counter. -/ def bC1 : ℕ := 245
/-- Its count. -/ def bN1 : ℕ := 246
/-- The middle loop's counter. -/ def bC2 : ℕ := 247
/-- Its count. -/ def bN2 : ℕ := 248
/-- The inner loop's counter. -/ def bC3 : ℕ := 249
/-- Its count. -/ def bN3 : ℕ := 250
/-- `2c`. -/ def bCo : ℕ := 251

/-! ## The program -/

/-- `d := b + m · M[i]`. -/
def addrPs (d i b m : ℕ) : List Prim :=
  [.const bK (toWord m), .op .mul d i bK, .const bK (toWord b), .op .add d d bK]

/-- **`DJ[t] := D(J_t)`** for the current `t` (`J_t` at `jb + t`, `DJ[t]` at `djb + 2t`). -/
def djBody (jb djb tb : ℕ) : XIR :=
  .seq (.blk (addrPs bA bT jb 1)) (.seq (.load rBs bA) (.seq (.blk [.const rTr (toWord tb)])
    (.seq alphaIR (.seq (.blk (addrPs bA bT djb 2)) (.seq (stF bA bA1 fAl)
      (.blk [.op .add bT bT cOne]))))))

/-- The table `DJ`. -/
def djIR (k jb djb tb : ℕ) : XIR :=
  .seq (.blk [.const bT 0, .const bN1 (toWord k)]) (.loopK bC1 bN1 (toWord k) (djBody jb djb tb))

/-- One factor of `W[t]`'s product: `fPr *= DJ[t] + DJ[m]` unless `m = t`. -/
def wInner (djb : ℕ) : XIR :=
  .seq (.blk (addrPs bA bM djb 2)) (.seq (ldF fX bA bA1) (.seq (addF fDd fDs fX)
    (.seq (.blk [.op .eq bZ bM bT]) (.seq (.ite bZ (.blk []) (mulF fPr fPr fDd))
      (.blk [.op .add bM bM cOne])))))

/-- **`W[t] := (Π_{m ≠ t} (DJ[t] + DJ[m]))⁻¹`** at `wb + 2t`. -/
def wtBody (k djb wb : ℕ) : XIR :=
  .seq (.blk (addrPs bA bT djb 2)) (.seq (ldF fDs bA bA1)
    (.seq (.blk [.const fPr 1, .const (fPr + 1) 0, .const bM 0, .const bN2 (toWord k)])
      (.seq (.loopK bC2 bN2 (toWord k) (wInner djb)) (.seq (invF fIv fPr)
        (.seq (.blk (addrPs bA bT wb 2)) (.seq (stF bA bA1 fIv) (.blk [.op .add bT bT cOne])))))))

/-- The table `W`. -/
def wtIR (k djb wb : ℕ) : XIR :=
  .seq (.blk [.const bT 0, .const bN1 (toWord k)]) (.loopK bC1 bN1 (toWord k) (wtBody k djb wb))

/-- **`E[t] := W[t] · (D(s) + DJ[t])⁻¹`** at `eb + 2t`, and `ℓ *= D(s) + DJ[t]`. -/
def eBody (djb wb eb : ℕ) : XIR :=
  .seq (.blk (addrPs bA bT djb 2)) (.seq (ldF fX bA bA1) (.seq (addF fDd fDs fX)
    (.seq (mulF fLp fLp fDd) (.seq (invF fIv fDd) (.seq (.blk (addrPs bA bT wb 2))
      (.seq (ldF fX bA bA1) (.seq (mulF fEt fX fIv) (.seq (.blk (addrPs bA bT eb 2))
        (.seq (stF bA bA1 fEt) (.blk [.op .add bT bT cOne]))))))))))

/-- **`acc += y_c(J_t) · E[t]`** (`y_c(j)` at `cb + cs·j + 2c`, `2c` in `bCo`). -/
def aBody (jb eb cb cs : ℕ) : XIR :=
  .seq (.blk (addrPs bA bT jb 1)) (.seq (.load bJ bA)
    (.seq (.blk (addrPs bJ bJ cb cs ++ [.op .add bJ bJ bCo])) (.seq (ldF fY bJ bA1)
      (.seq (.blk (addrPs bA bT eb 2)) (.seq (ldF fX bA bA1) (.seq (mulF fPr fY fX)
        (.seq (addF fAc fAc fPr) (.blk [.op .add bT bT cOne]))))))))

/-- `fAc := y_c(s)`. -/
def yIR (cb cs : ℕ) : XIR :=
  .seq (.blk (addrPs bA bS cb cs ++ [.op .add bA bA bCo])) (ldF fAc bA bA1)

/-- **One coordinate `c`**: `acc := Σ_t y_c(J_t) E[t]`, then `out[c][s] := (ℓ = 0 ? y_c(s) :
ℓ · acc)` at `ob + 2k·c + 2s`. -/
def cBody (k jb eb cb cs ob : ℕ) : XIR :=
  .seq (.blk [.const fAc 0, .const (fAc + 1) 0, .const bT 0, .const bN3 (toWord k)])
    (.seq (.loopK bC3 bN3 (toWord k) (aBody jb eb cb cs))
      (.seq (.ite bZ (yIR cb cs) (mulF fAc fLp fAc))
        (.seq (.blk (addrPs bA bCi ob (2 * k) ++ [.op .add bA bA bS, .op .add bA bA bS]))
          (.seq (stF bA bA1 fAc) (.blk [.op .add bCi bCi cOne, .const bK 2,
            .op .add bCo bCo bK])))))

/-- **One target `s`**: `D(s)`, the `E` row and `ℓ`, the flag `[ℓ = 0]`, the `C` coordinates. -/
def sBody (k C jb djb wb eb cb cs ob tb : ℕ) : XIR :=
  .seq (.seq (.blk [.op .or rBs bS bS, .const rTr (toWord tb)]) alphaIR)
    (.seq (.blk [.op .or fDs fAl fAl, .op .or (fDs + 1) (fAl + 1) (fAl + 1), .const fLp 1,
        .const (fLp + 1) 0, .const bT 0, .const bN2 (toWord k)])
      (.seq (.loopK bC2 bN2 (toWord k) (eBody djb wb eb))
        (.seq (.blk [.op .or bZ fLp (fLp + 1), .const bK 0, .op .eq bZ bZ bK, .const bCi 0,
            .const bCo 0, .const bN2 (toWord C)])
          (.seq (.loopK bC2 bN2 (toWord C) (cBody k jb eb cb cs ob))
            (.blk [.op .add bS bS cOne])))))

/-- **The interpolation**: `out[c][s] = interpF D J y_c s` for `s < k`, `c < C`. -/
def baryIR (k C jb djb wb eb cb cs ob tb : ℕ) : XIR :=
  .seq (djIR k jb djb tb) (.seq (wtIR k djb wb)
    (.seq (.blk [.const bS 0, .const bN1 (toWord k)])
      (.loopK bC1 bN1 (toWord k) (sBody k C jb djb wb eb cb cs ob tb))))

/-! ## Well formed, cost, size -/

theorem bnw_mulF {d a b i : ℕ} (h1 : i ≠ d) (h2 : i ≠ d + 1) (h3 : 15 ≤ i) :
    Writes (mulF d a b) i ↔ False := ⟨nw_mulF h3 h1 h2, False.elim⟩

theorem bnw_addF {d a b i : ℕ} (h1 : i ≠ d) (h2 : i ≠ d + 1) : Writes (addF d a b) i ↔ False :=
  ⟨fun ⟨p, hp, he⟩ => by have := addFC_dst d a b p hp; omega, False.elim⟩

theorem bnw_invF {d a i : ℕ} (h1 : i ≠ d) (h2 : i ≠ d + 1) (h3 : 19 ≤ i) :
    Writes (invF d a) i ↔ False := ⟨nw_invF h3 h1 h2, False.elim⟩

theorem wfF_mul {d a b : ℕ} (h : 4 ≤ d) : WF (mulF d a b) ↔ True := iff_true_intro (wf_mulF d a b h)
theorem wfF_add {d a b : ℕ} (h : 4 ≤ d) : WF (addF d a b) ↔ True := iff_true_intro (wf_addF d a b h)
theorem wfF_inv {d a : ℕ} (h : 4 ≤ d) : WF (invF d a) ↔ True := iff_true_intro (wf_invF d a h)

theorem wf_baryIR (k C jb djb wb eb cb cs ob tb : ℕ) :
    WF (baryIR k C jb djb wb eb cb cs ob tb) := by
  simp [baryIR, djIR, djBody, wtIR, wtBody, wInner, sBody, eBody, cBody, aBody, yIR, addrPs,
    alphaIR, alphaBody, ldF, stF, WF, Writes, Prim.dst, bnw_mulF, bnw_addF, bnw_invF, wfF_mul, wfF_add, wfF_inv,
    fDs, fLp, fDd, fIv, fEt, fPr, fY, fAc, fX, bT, bM, bS, bCi, bA, bA1, bJ, bK, bZ, bC1, bN1, bC2,
    bN2, bC3, bN3, bCo, rBs, rTr, rTa, rTa1, rBit, uI, uT1, fG, fAl, rC2, rN2, cTmp, regs]

theorem noLoopT_baryIR (k C jb djb wb eb cb cs ob tb : ℕ) :
    NoLoopT (baryIR k C jb djb wb eb cb cs ob tb) := by
  simp [baryIR, djIR, djBody, wtIR, wtBody, wInner, sBody, eBody, cBody, aBody, yIR, alphaIR,
    alphaBody, ldF, stF, mulF, addF, invF, NoLoopT]

theorem outs_baryIR (k C jb djb wb eb cb cs ob tb t : ℕ) :
    outs (baryIR k C jb djb wb eb cb cs ob tb) t = 0 := by
  simp [baryIR, djIR, djBody, wtIR, wtBody, wInner, sBody, eBody, cBody, aBody, yIR, alphaIR,
    alphaBody, ldF, stF, mulF, addF, invF, outs]

/-- **The interpolation's cost** (`k, C < 2^64`). -/
theorem cost_baryIR (k C jb djb wb eb cb cs ob tb t : ℕ) (hk : k < 2 ^ 64) (hC : C < 2 ^ 64) :
    cost (baryIR k C jb djb wb eb cb cs ob tb) t =
      38 + k * 2487 + k * C * 108 + k ^ 2 * 1363 + k ^ 2 * C * 106 := by
  have e1 : (toWord k).toNat = k := toNat_toWord hk
  have e2 : (toWord C).toNat = C := toNat_toWord hC
  simp only [baryIR, djIR, djBody, wtIR, wtBody, wInner, sBody, eBody, cBody, aBody, yIR, addrPs,
    ldF, stF, cost, cost_mulF, cost_addF, cost_invF, cost_alphaIR, blkSteps, List.length_cons,
    List.length_nil, List.length_append, e1, e2]
  norm_num
  ring_nf

end FR.X
