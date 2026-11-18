-- adapted from rf-k/submissions/flock-recursive/lean/FRXLag.lean@8bff272b (section G6_FRXBaryTop:
-- `sBody_sem`, `BaryLay`, `cell_ne`, `sValM`, `sLoop_sem`, `baryIR_sem`, `baryIR_interp`) for lvm
-- (WP-13b): FR's two-word `F` re-targeted to `K = BF64`; FR's `alphaIR` call for `D(s)` is replaced
-- by the target index word itself (`ptK s`), FR's `djIR` table by the list `J` (`ptK J_t`).
import LvmXDec
import LvmXLoop

-- (GOLF2: 12 declarations that `certified` does not use moved verbatim to `LvmXInterp4Off`, outside its import closure.)

-- ===== merged from `LvmXInterp` (GOLF module merge: `LvmXInterp.lean` is now a stub importing `LvmXInterp4`) =====
section
-- adapted from rf-k/submissions/flock-recursive/lean/FRXBaryDefs.lean@8bff272b (section
-- G6_FRXBaryDefs) for lvm (WP-13b): FR's two-word field `F` re-targeted to lvm's one-word
-- `K = BF64`; namespace `FR.X` → `Lvm.X`; FR's `djIR`/`alphaIR` phases dropped (`ptK j` is the word `j`).

/-!
# The barycentric interpolation over `K`: the pure form and the program

`interpF ptK J y s` (`LvmXEnc`) is the Lagrange interpolation of `y` on the points `ptK J` at
`ptK s`. The machine computes it in barycentric form (FR's `FRXBaryDefs`):

* off `J`: `interpF ptK J y s = ℓ(s) · Σ_{i ∈ J} y i · w_i · (ptK s − ptK i)⁻¹`, with
  `ℓ(s) = Π_{m ∈ J} (ptK s − ptK m)` and `w_i = (Π_{m ∈ J∖i} (ptK i − ptK m))⁻¹`
  (`interpF_bary`);
* on `J`: `interpF ptK J y s = y s` (`interpF_self`).

The machine tells the two apart by `ℓ(s) = 0` (`ptK` is injective below `2^15`). With `J` the list
`Jl = J₀ … J_{k−1}`, the machine's value is `baryValK` and **`baryValK_eq`** proves it is
`interpF ptK Jl.toFinset y s` for `s < 2^15`.

## The port from FR

FR's `F = GF(2^128)` takes two words; lvm's `K` element is one word (`rdK`), so FR's `ldF`/`stF`
are `.load`/`.store`, `addF` is one `xor`, `mulF`/`invF` are `mulK`/`invK`, and every table has
stride 1. The domain point of position `j` is the word `j` itself (`ptK j = wK (toWord j)`), so
FR's table `DJ` (`djIR`, the `alphaIR` call on the basis table) and the `alphaIR` call computing
`D(s)` in `sBody` disappear: `J_t` is read from `jb + t` as the `K` element, and the target index
word `s` is `ptK s`. FR's registers `216 …` are kept (each `F` pair's first word).

## The program (`baryIR k C jb wb eb cb cs ob`)

A coordinate `c < C` of position `j` is the `K` element at `cb + cs·j + c`. Phases:

1. `wtIR`: `W[t] := (Π_{m ≠ t} (J_t + J_m))⁻¹` at `wb + t`;
2. per target `s < k` (`sBody`): `E[t] := W[t] · (ptK s + J_t)⁻¹` at `eb + t` and
   `ℓ := Π_t (ptK s + J_t)`; per coordinate `c`: `acc := Σ_t y_c(J_t) E[t]` (registers only),
   then `out[c][s] := (ℓ = 0 ? y_c(s) : ℓ · acc)` at `ob + k·c + s`.

`cost_baryIR`: `25 + 1106 k + 49 k C + 1118 k² + 44 k² C` (FR: `38 + 2487 k + 108 k C +
1363 k² + 106 k² C`); at lvm's `k = 2^13`, `C = 64`: `264 041 021 465 ≈ 2^37.94`
(`cost_baryIR_lvm`).
-/

namespace Lvm.X

open RecursionFast Finset Lvm.Nb

/-! ## The machine's value over `K`, against `interpF` -/

/-- The domain point `ptK J_t` of the list `Jl`. -/
def djK (Jl : List ℕ) (t : ℕ) : BF64 := ptK (Jl.getD t 0)

/-- **The weight** `W[t] = (Π_{m < k, m ≠ t} (J_t + J_m))⁻¹`, as the machine's product
(`m = t` contributes `1`). -/
def wgtK (Jl : List ℕ) (k t : ℕ) : BF64 :=
  (∏ m ∈ range k, if m = t then 1 else djK Jl t + djK Jl m)⁻¹

/-- `ℓ(s) = Π_{t < k} (ptK s + J_t)`. -/
def ellK (Jl : List ℕ) (k s : ℕ) : BF64 := ∏ t ∈ range k, (ptK s + djK Jl t)

/-- `E[t] = W[t] · (ptK s + J_t)⁻¹`. -/
def eAtK (Jl : List ℕ) (k s t : ℕ) : BF64 := wgtK Jl k t * (ptK s + djK Jl t)⁻¹

/-- **The machine's value** at target `s` for the values `y`: `y s` when `ℓ(s) = 0`, else
`ℓ(s) · Σ_t y(J_t) E[t]`. -/
def baryValK (Jl : List ℕ) (k s : ℕ) (y : ℕ → BF64) : BF64 :=
  if ellK Jl k s = 0 then y s else ellK Jl k s * ∑ t ∈ range k, y (Jl.getD t 0) * eAtK Jl k s t

theorem toFinset_eq_imageB (Jl : List ℕ) :
    Jl.toFinset = (range Jl.length).image (fun t => Jl.getD t 0) := by
  ext x
  simp only [List.mem_toFinset, Finset.mem_image, Finset.mem_range, List.mem_iff_getElem]
  constructor
  · rintro ⟨t, ht, rfl⟩; exact ⟨t, ht, by rw [List.getD_eq_getElem]⟩
  · rintro ⟨t, ht, rfl⟩; exact ⟨t, ht, by rw [List.getD_eq_getElem]⟩

theorem getD_injOnB {Jl : List ℕ} (hnd : Jl.Nodup) :
    Set.InjOn (fun t => Jl.getD t 0) (range Jl.length : Set ℕ) := fun a ha b hb h => by
  simp only [coe_range, Set.mem_Iio] at ha hb
  simp only [List.getD_eq_getElem _ _ ha, List.getD_eq_getElem _ _ hb] at h
  exact (hnd.getElem_inj_iff).1 h

theorem prod_toFinsetB {Jl : List ℕ} (hnd : Jl.Nodup) (f : ℕ → BF64) :
    ∏ m ∈ Jl.toFinset, f m = ∏ t ∈ range Jl.length, f (Jl.getD t 0) := by
  rw [toFinset_eq_imageB, Finset.prod_image (getD_injOnB hnd)]

theorem sum_toFinsetB {Jl : List ℕ} (hnd : Jl.Nodup) (f : ℕ → BF64) :
    ∑ m ∈ Jl.toFinset, f m = ∑ t ∈ range Jl.length, f (Jl.getD t 0) := by
  rw [toFinset_eq_imageB, Finset.sum_image (getD_injOnB hnd)]

theorem prod_erase_iteB {J : Finset ℕ} {i : ℕ} (hi : i ∈ J) (f : ℕ → BF64) :
    ∏ m ∈ J.erase i, f m = ∏ m ∈ J, if m = i then 1 else f m := by
  rw [← Finset.mul_prod_erase J _ hi, if_pos rfl, one_mul]
  exact Finset.prod_congr rfl fun m hm => by rw [if_neg (Finset.mem_erase.1 hm).1]

/-! ## Registers (`216 …`, FR's numbers) -/

/-- `ptK s` or `J_t`. -/ def fDs : ℕ := 216
/-- `ℓ`. -/ def fLp : ℕ := 218
/-- `ptK s + J_t`. -/ def fDd : ℕ := 220
/-- Its inverse. -/ def fIv : ℕ := 222
/-- `E[t]`. -/ def fEt : ℕ := 224
/-- A product. -/ def fPr : ℕ := 226
/-- A column value. -/ def fY : ℕ := 228
/-- The accumulator. -/ def fAc : ℕ := 230
/-- A loaded element. -/ def fX : ℕ := 232
/-- `t`. -/ def bT : ℕ := 236
/-- `m`. -/ def bM : ℕ := 237
/-- `s`. -/ def bS : ℕ := 238
/-- `c`. -/ def bCi : ℕ := 239
/-- An address. -/ def bA : ℕ := 240
/-- A column address. -/ def bJ : ℕ := 242
/-- Constant scratch. -/ def bK : ℕ := 243
/-- A flag. -/ def bZ : ℕ := 244
/-- The outer loop's counter. -/ def bC1 : ℕ := 245
/-- Its count. -/ def bN1 : ℕ := 246
/-- The middle loop's counter. -/ def bC2 : ℕ := 247
/-- Its count. -/ def bN2 : ℕ := 248
/-- The inner loop's counter. -/ def bC3 : ℕ := 249
/-- Its count. -/ def bN3 : ℕ := 250

/-! ## The program -/

/-- `d := b + m · M[i]`. -/
def addrPs (d i b m : ℕ) : List Prim :=
  [.const bK (toWord m), .op .mul d i bK, .const bK (toWord b), .op .add d d bK]

/-- `d := b + M[i]` (stride 1). -/
def addr1Ps (d i b : ℕ) : List Prim := [.const bK (toWord b), .op .add d i bK]

/-- One factor of `W[t]`'s product: `fPr *= J_t + J_m` unless `m = t`. -/
def wInner (jb : ℕ) : XIR :=
  .seq (.blk (addr1Ps bA bM jb)) (.seq (.load fX bA)
    (.seq (.blk [.op .xor fDd fDs fX, .op .eq bZ bM bT])
      (.seq (.ite bZ (.blk []) (mulK fPr fPr fDd)) (.blk [.op .add bM bM cOne]))))

/-- **`W[t] := (Π_{m ≠ t} (J_t + J_m))⁻¹`** at `wb + t`. -/
def wtBody (k jb wb : ℕ) : XIR :=
  .seq (.blk (addr1Ps bA bT jb)) (.seq (.load fDs bA)
    (.seq (.blk [.const fPr 1, .const bM 0, .const bN2 (toWord k)])
      (.seq (.loopK bC2 bN2 (toWord k) (wInner jb)) (.seq (invK fIv fPr)
        (.seq (.blk (addr1Ps bA bT wb)) (.seq (.store bA fIv) (.blk [.op .add bT bT cOne])))))))

/-- The table `W`. -/
def wtIR (k jb wb : ℕ) : XIR :=
  .seq (.blk [.const bT 0, .const bN1 (toWord k)]) (.loopK bC1 bN1 (toWord k) (wtBody k jb wb))

/-- **`E[t] := W[t] · (ptK s + J_t)⁻¹`** at `eb + t`, and `ℓ *= ptK s + J_t`. -/
def eBody (jb wb eb : ℕ) : XIR :=
  .seq (.blk (addr1Ps bA bT jb)) (.seq (.load fX bA) (.seq (.blk [.op .xor fDd fDs fX])
    (.seq (mulK fLp fLp fDd) (.seq (invK fIv fDd) (.seq (.blk (addr1Ps bA bT wb))
      (.seq (.load fX bA) (.seq (mulK fEt fX fIv) (.seq (.blk (addr1Ps bA bT eb))
        (.seq (.store bA fEt) (.blk [.op .add bT bT cOne]))))))))))

/-- **`acc += y_c(J_t) · E[t]`** (`y_c(j)` at `cb + cs·j + c`, `c` in `bCi`). -/
def aBody (jb eb cb cs : ℕ) : XIR :=
  .seq (.blk (addr1Ps bA bT jb)) (.seq (.load bJ bA)
    (.seq (.blk (addrPs bJ bJ cb cs ++ [.op .add bJ bJ bCi])) (.seq (.load fY bJ)
      (.seq (.blk (addr1Ps bA bT eb)) (.seq (.load fX bA) (.seq (mulK fPr fY fX)
        (.blk [.op .xor fAc fAc fPr, .op .add bT bT cOne])))))))

/-- `fAc := y_c(s)`. -/
def yIR (cb cs : ℕ) : XIR :=
  .seq (.blk (addrPs bA bS cb cs ++ [.op .add bA bA bCi])) (.load fAc bA)

/-- **One coordinate `c`**: `acc := Σ_t y_c(J_t) E[t]`, then `out[c][s] := (ℓ = 0 ? y_c(s) :
ℓ · acc)` at `ob + k·c + s`. -/
def cBody (k jb eb cb cs ob : ℕ) : XIR :=
  .seq (.blk [.const fAc 0, .const bT 0, .const bN3 (toWord k)])
    (.seq (.loopK bC3 bN3 (toWord k) (aBody jb eb cb cs))
      (.seq (.ite bZ (yIR cb cs) (mulK fAc fLp fAc))
        (.seq (.blk (addrPs bA bCi ob k ++ [.op .add bA bA bS]))
          (.seq (.store bA fAc) (.blk [.op .add bCi bCi cOne])))))

/-- **One target `s`**: `ptK s`, the `E` row and `ℓ`, the flag `[ℓ = 0]`, the `C` coordinates. -/
def sBody (k C jb wb eb cb cs ob : ℕ) : XIR :=
  .seq (.blk [.op .or fDs bS bS, .const fLp 1, .const bT 0, .const bN2 (toWord k)])
    (.seq (.loopK bC2 bN2 (toWord k) (eBody jb wb eb))
      (.seq (.blk [.const bK 0, .op .eq bZ fLp bK, .const bCi 0, .const bN2 (toWord C)])
        (.seq (.loopK bC2 bN2 (toWord C) (cBody k jb eb cb cs ob))
          (.blk [.op .add bS bS cOne]))))

/-- **The interpolation**: `out[c][s] = interpF ptK J y_c s` for `s < k`, `c < C`. -/
def baryIR (k C jb wb eb cb cs ob : ℕ) : XIR :=
  .seq (wtIR k jb wb) (.seq (.blk [.const bS 0, .const bN1 (toWord k)])
    (.loopK bC1 bN1 (toWord k) (sBody k C jb wb eb cb cs ob)))

/-! ## Well formed, no `loopT`, no output, cost -/

theorem bnw_mulK {d a b i : ℕ} (h1 : i ≠ d) (h3 : 9 ≤ i) : Writes (mulK d a b) i ↔ False :=
  ⟨fun ⟨p, hp, he⟩ => by have := mulKC_dst d a b p hp; omega, False.elim⟩

theorem bnw_invK {d a i : ℕ} (h1 : i ≠ d) (h3 : 12 ≤ i) : Writes (invK d a) i ↔ False :=
  ⟨fun ⟨p, hp, he⟩ => by have := invKC_dst d a p hp; omega, False.elim⟩

theorem wfK_mul {d a b : ℕ} (h : 4 ≤ d) : WF (mulK d a b) ↔ True := iff_true_intro (wf_mulK d a b h)
theorem wfK_inv {d a : ℕ} (h : 4 ≤ d) : WF (invK d a) ↔ True := iff_true_intro (wf_invK d a h)

theorem wf_baryIR (k C jb wb eb cb cs ob : ℕ) : WF (baryIR k C jb wb eb cb cs ob) := by
  simp [baryIR, wtIR, wtBody, wInner, sBody, eBody, cBody, aBody, yIR, addrPs, addr1Ps, WF,
    Writes, Prim.dst, bnw_mulK, bnw_invK, wfK_mul, wfK_inv, fDs, fLp, fDd, fIv, fEt, fPr, fY,
    fAc, fX, bT, bM, bS, bCi, bA, bJ, bK, bZ, bC1, bN1, bC2, bN2, bC3, bN3, cTmp, regs]

theorem noLoopT_baryIR (k C jb wb eb cb cs ob : ℕ) : NoLoopT (baryIR k C jb wb eb cb cs ob) := by
  simp [baryIR, wtIR, wtBody, wInner, sBody, eBody, cBody, aBody, yIR, mulK, invK, NoLoopT]

theorem outs_baryIR (k C jb wb eb cb cs ob t : ℕ) : outs (baryIR k C jb wb eb cb cs ob) t = 0 := by
  simp [baryIR, wtIR, wtBody, wInner, sBody, eBody, cBody, aBody, yIR, mulK, invK, outs]

/-- **The interpolation's cost** (`k, C < 2^64`). -/
theorem cost_baryIR (k C jb wb eb cb cs ob t : ℕ) (hk : k < 2 ^ 64) (hC : C < 2 ^ 64) :
    cost (baryIR k C jb wb eb cb cs ob) t =
      25 + 1106 * k + 49 * k * C + 1118 * k ^ 2 + 44 * k ^ 2 * C := by
  have e1 : (toWord k).toNat = k := toNat_toWord hk
  have e2 : (toWord C).toNat = C := toNat_toWord hC
  simp only [baryIR, wtIR, wtBody, wInner, sBody, eBody, cBody, aBody, yIR, addrPs, addr1Ps,
    cost, cost_mulK, cost_invK, blkSteps, List.length_cons, List.length_nil, List.length_append,
    e1, e2]
  norm_num
  ring

/-- **The cost at lvm's sizes** (`k = 2^13`, `C = 64`): `≈ 2^37.94`. -/
theorem cost_baryIR_lvm (jb wb eb cb cs ob t : ℕ) :
    cost (baryIR (2 ^ 13) 64 jb wb eb cb cs ob) t = 264041021465 := by
  rw [cost_baryIR _ _ _ _ _ _ _ _ _ (by norm_num) (by norm_num)]
  norm_num

end Lvm.X
end
-- ===== end of `LvmXInterp` =====

-- ===== merged from `LvmXInterp2` (GOLF module merge: `LvmXInterp2.lean` is now a stub importing `LvmXInterp4`) =====
section
-- adapted from rf-k/submissions/flock-recursive/lean/FRXBary.lean@8bff272b (helpers, `wInner_sem` …
-- `wtIR_sem`, `eBody_sem`, `eLoop_sem`) for lvm (WP-13b): FR's two-word `F` re-targeted to `K = BF64`;
-- FR's `djIR` (the table `D(J_t)`) is dropped: `J_t`'s word is its domain point (`ptK`).

/-!
# The barycentric interpolation on the machine (1): the table `W` and one target's `E` row

Bottom-up: the address blocks, the increment, `wInner_sem` (one factor of a weight),
**`wtIR_sem`** (`W[t] = (Π_{m ≠ t} (G t + G m))⁻¹` at `wb + t`, `G m` the element at `jb + m`),
`eBody_sem` and **`eLoop_sem`** (`E[t] = W[t] (ds + G t)⁻¹` at `eb + t`, `ℓ = Π_t (ds + G t)`).
-/

namespace Lvm.X

open RecursionFast Finset

attribute [local irreducible] entryK storeM

/-! ## Helpers -/

theorem rdK_congrB {M M' : Mem} {a a' : ℕ} (h : rd M a = rd M' a') : rdK M a = rdK M' a' := by
  rw [rdK, rdK, h]

theorem wK_eq_zero (w : Word) : wK w = 0 ↔ w = 0 := by
  constructor
  · intro h; exact congrArg BF64.toBitVec h
  · rintro rfl; rfl

theorem sem_blk_append (I : Array Word) (ps qs : List Prim) (s : St) :
    semXIR I (.blk (ps ++ qs)) s = semXIR I (.blk qs) (semXIR I (.blk ps) s) := by
  simp only [semXIR, runPrims_append]

/-- **The address block** `d := b + m · M[i]`. -/
theorem addr_sem (I : Array Word) (s : St) (hM : Inv s.M) {d i b m x : ℕ} (hd : d < regs)
    (hd4 : 4 ≤ d) (hdK : d ≠ bK) (hi : i ≠ bK) (hx : rd s.M i = toWord x) :
    rd (semXIR I (.blk (addrPs d i b m)) s).M d = toWord (b + m * x) ∧
    (∀ j, j ≠ d → j ≠ bK → rd (semXIR I (.blk (addrPs d i b m)) s).M j = rd s.M j) ∧
    Inv (semXIR I (.blk (addrPs d i b m)) s).M := by
  have hs := hM.1
  have hK : bK < s.M.size := by simp only [regs] at hs; simp only [bK]; (clear * - hs; omega)
  have hd' : d < s.M.size := by simp only [regs] at hs hd; (clear * - hd hd4 hs; omega)
  rw [sem_blk]
  refine ⟨?_, fun j h1 h2 => rd_runPrims_of_not_writes (by
    simp only [addrPs, List.mem_cons, List.mem_nil_iff, or_false]
    rintro p (rfl | rfl | rfl | rfl) <;> simp only [Prim.dst] <;> (clear * - h2 h1; omega)) _,
    inv_runPrims (by
      simp only [addrPs, List.mem_cons, List.mem_nil_iff, or_false]
      rintro p (rfl | rfl | rfl | rfl) <;> simp only [Prim.dst, bK] <;> omega) hM⟩
  simp only [addrPs, runPrims, List.foldl, Prim.run]
  simp (disch := first | exact hdK | exact hdK.symm | exact hi.symm | exact hK | exact hd' |
    (simp only [size_set]; first | exact hd' | exact hK)) only [rd_set_self, rd_set_ne, hx]
  rw [mul_toWord, add_toWord, Nat.add_comm, Nat.mul_comm]

/-- **The address block** `d := b + M[i]` (stride 1). -/
theorem addr1_sem (I : Array Word) (s : St) (hM : Inv s.M) {d i b x : ℕ} (hd : d < regs)
    (hd4 : 4 ≤ d) (_hdK : d ≠ bK) (hi : i ≠ bK) (hx : rd s.M i = toWord x) :
    rd (semXIR I (.blk (addr1Ps d i b)) s).M d = toWord (b + x) ∧
    (∀ j, j ≠ d → j ≠ bK → rd (semXIR I (.blk (addr1Ps d i b)) s).M j = rd s.M j) ∧
    Inv (semXIR I (.blk (addr1Ps d i b)) s).M := by
  have hs := hM.1
  have hK : bK < s.M.size := by simp only [regs] at hs; simp only [bK]; (clear * - hs; omega)
  have hd' : d < s.M.size := by simp only [regs] at hs hd; (clear * - hd hd4 hs; omega)
  rw [sem_blk]
  refine ⟨?_, fun j h1 h2 => rd_runPrims_of_not_writes (by
    simp only [addr1Ps, List.mem_cons, List.mem_nil_iff, or_false]
    rintro p (rfl | rfl) <;> simp only [Prim.dst] <;> (clear * - h2 h1; omega)) _,
    inv_runPrims (by
      simp only [addr1Ps, List.mem_cons, List.mem_nil_iff, or_false]
      rintro p (rfl | rfl) <;> simp only [Prim.dst, bK] <;> omega) hM⟩
  simp only [addr1Ps, runPrims, List.foldl, Prim.run]
  simp (disch := first | exact hi.symm | exact hK | exact hd' |
    (simp only [size_set]; first | exact hd' | exact hK)) only [rd_set_self, rd_set_ne, hx]
  rw [add_toWord, Nat.add_comm]

/-- `r += 1`. -/
theorem bInc_sem (I : Array Word) (s : St) (hM : Inv s.M) {r x : ℕ} (hr : r < regs)
    (hr4 : 4 ≤ r) (hx : rd s.M r = toWord x) :
    rd (semXIR I (.blk [.op .add r r cOne]) s).M r = toWord (x + 1) ∧
    (∀ i, i ≠ r → rd (semXIR I (.blk [.op .add r r cOne]) s).M i = rd s.M i) ∧
    Inv (semXIR I (.blk [.op .add r r cOne]) s).M := by
  have hs := hM.1
  have h1 : rd s.M cOne = 1 := hM.2 0 (by decide)
  rw [sem_blk]
  refine ⟨?_, fun i hi => rd_runPrims_of_not_writes (by simp [Prim.dst]; exact Ne.symm hi) _,
    inv_runPrims (by simp [Prim.dst]; exact hr4) hM⟩
  simp only [runPrims, List.foldl, Prim.run]
  rw [rd_set_self (by simp only [regs] at hs hr; (clear * - hr hr4 hs; omega)), hx, h1, add_one_toWord]

/-- `d += M[r]`. -/
theorem bAdd_sem (I : Array Word) (s : St) (hM : Inv s.M) {d r x y : ℕ} (hd : d < regs)
    (hd4 : 4 ≤ d) (hx : rd s.M d = toWord x) (hy : rd s.M r = toWord y) :
    rd (semXIR I (.blk [.op .add d d r]) s).M d = toWord (x + y) ∧
    (∀ j, j ≠ d → rd (semXIR I (.blk [.op .add d d r]) s).M j = rd s.M j) ∧
    Inv (semXIR I (.blk [.op .add d d r]) s).M := by
  have hs := hM.1
  rw [sem_blk]
  refine ⟨?_, fun j hj => rd_runPrims_of_not_writes (by simp [Prim.dst]; exact Ne.symm hj) _,
    inv_runPrims (by simp [Prim.dst]; exact hd4) hM⟩
  simp only [runPrims, List.foldl, Prim.run]
  rw [rd_set_self (by simp only [regs] at hs hd; (clear * - hd hd4 hs; omega)), hx, hy, add_toWord]

theorem frK_mul {I : Array Word} {s : St} {d a b r : ℕ} (h0 : 9 ≤ r) (h1 : r ≠ d) :
    rd (semXIR I (mulK d a b) s).M r = rd s.M r := by
  rw [mulK, sem_blk]; exact mulKC_frame _ _ _ (.inr h0) h1 _

theorem frK_inv {I : Array Word} {s : St} {d a r : ℕ} (h0 : 12 ≤ r) (h1 : r ≠ d) :
    rd (semXIR I (invK d a) s).M r = rd s.M r := by
  rw [invK, sem_blk]; exact invKC_frame _ _ (.inr h0) h1 _

theorem lo_mulK {d a b : ℕ} (h : d < regs) : Lo (mulK d a b) := fun p hp => by
  have := mulKC_dst d a b p hp; simp only [regs] at h ⊢; (clear * - h this; omega)

/-! ## The table `W` -/

theorem lo_wInner (jb : ℕ) : Lo (wInner jb) := by
  simp [wInner, addr1Ps, Lo, Prim.dst, bA, bK, fX, fDd, bZ, bM, fPr, regs]
  exact lo_mulK (by decide)

/-- **One factor** of `W[t]`: `fPr *= (m = t ? 1 : J_t + J_m)`. -/
theorem wInner_sem (I : Array Word) (s : St) (hM : Inv s.M) {jb m t : ℕ} {dt : BF64}
    (hjb : regs ≤ jb) (hm : m < 2 ^ 64) (ht : t < 2 ^ 64) (hjb2 : jb + m < 2 ^ 64)
    (hBm : rd s.M bM = toWord m) (hBt : rd s.M bT = toWord t) (hDs : rdK s.M fDs = dt) :
    rdK (semXIR I (wInner jb) s).M fPr =
      rdK s.M fPr * (if m = t then 1 else dt + rdK s.M (jb + m)) ∧
    rd (semXIR I (wInner jb) s).M bM = toWord (m + 1) ∧
    rd (semXIR I (wInner jb) s).M bT = toWord t ∧ rdK (semXIR I (wInner jb) s).M fDs = dt ∧
    Inv (semXIR I (wInner jb) s).M := by
  simp only [regs] at hjb
  rw [wInner]
  simp only [semXIR_seq]
  -- `bA := jb + m`
  obtain ⟨a1, f1, hM1⟩ := addr1_sem I s hM (d := bA) (i := bM) (b := jb) (by decide) (by decide)
    (by decide) (by decide) hBm
  generalize semXIR I (.blk (addr1Ps bA bM jb)) s = s1 at a1 f1 hM1
  -- `fX := J_m`
  obtain ⟨l2, f2, hM2⟩ := load_sem I s1 hM1 (d := fX) (p := bA) (x := jb + m) (by decide)
    (by decide) a1 hjb2
  rw [f1 _ (by simp only [bA]; (clear * - hjb hm; omega)) (by simp only [bK]; (clear * - hjb hm; omega))] at l2
  generalize semXIR I (.load fX bA) s1 = s2 at l2 f2 hM2
  have g2 : ∀ r, r ≠ fX → r ≠ bA → r ≠ bK → rd s2.M r = rd s.M r := fun r a b c =>
    (f2 r a).trans (f1 r b c)
  -- `fDd := fDs + fX`, `bZ := [m = t]`
  have hs2 := hM2.1
  have v3 : rdK (semXIR I (.blk [.op .xor fDd fDs fX, .op .eq bZ bM bT]) s2).M fDd =
        dt + rdK s.M (jb + m) ∧
      rd (semXIR I (.blk [.op .xor fDd fDs fX, .op .eq bZ bM bT]) s2).M bZ =
        bW (decide (m = t)) := by
    rw [sem_blk]
    simp only [runPrims, List.foldl, Prim.run]
    refine ⟨?_, ?_⟩
    · rw [rdK]
      simp (disch := first | decide |
        ((try simp only [size_set]); exact lt_of_lt_of_le (by decide) hs2))
        only [rd_set_self, rd_set_ne]
      rw [eval_xor, wK_xor, g2 fDs (by decide) (by decide) (by decide), l2]
      show rdK s.M fDs + rdK s.M (jb + m) = dt + rdK s.M (jb + m)
      rw [hDs]
    · simp (disch := first | decide |
        ((try simp only [size_set]); exact lt_of_lt_of_le (by decide) hs2))
        only [rd_set_self, rd_set_ne]
      rw [g2 bM (by decide) (by decide) (by decide), g2 bT (by decide) (by decide) (by decide),
        hBm, hBt, eqW_toWord hm ht]
  have f3 : ∀ r, r ≠ fDd → r ≠ bZ →
      rd (semXIR I (.blk [.op .xor fDd fDs fX, .op .eq bZ bM bT]) s2).M r = rd s2.M r :=
    fun r a b => rd_runPrims_of_not_writes (by
      simp only [List.mem_cons, List.mem_nil_iff, or_false]
      rintro p (rfl | rfl) <;> simp only [Prim.dst] <;> (clear * - a b; omega)) _
  have hM3 := inv_sem I (P := .blk [.op .xor fDd fDs fX, .op .eq bZ bM bT]) (s := s2)
    (by simp [WF, Prim.dst, fDd, bZ]) hM2
  generalize semXIR I (.blk [.op .xor fDd fDs fX, .op .eq bZ bM bT]) s2 = s3 at v3 f3 hM3
  -- the conditional product
  have ePr : rdK s3.M fPr = rdK s.M fPr :=
    rdK_congrB ((f3 _ (by decide) (by decide)).trans (g2 _ (by decide) (by decide) (by decide)))
  have p4 : rdK (semXIR I (.ite bZ (.blk []) (mulK fPr fPr fDd)) s3).M fPr =
      rdK s.M fPr * (if m = t then 1 else dt + rdK s.M (jb + m)) := by
    rw [semXIR_ite, v3.2]
    by_cases hmt : m = t
    · rw [decide_eq_true hmt, if_neg bW_ne_zero, if_pos hmt, mul_one]; exact ePr
    · rw [decide_eq_false hmt, bW_false, if_pos rfl, if_neg hmt,
        mulK_sem hM3 (by decide) (by decide) (by decide) (by decide), ePr, v3.1]
  have f4 : ∀ r, 9 ≤ r → r ≠ fPr →
      rd (semXIR I (.ite bZ (.blk []) (mulK fPr fPr fDd)) s3).M r = rd s3.M r := fun r h0 h1 => by
    rw [semXIR_ite]
    split_ifs
    · exact frK_mul h0 h1
    · rfl
  have hM4 := inv_sem I (P := .ite bZ (.blk []) (mulK fPr fPr fDd)) (s := s3)
    ⟨by simp [WF], wf_mulK _ _ _ (by decide)⟩ hM3
  generalize semXIR I (.ite bZ (.blk []) (mulK fPr fPr fDd)) s3 = s4 at p4 f4 hM4
  have G4 : ∀ r, 9 ≤ r → r ≠ fPr → r ≠ fDd → r ≠ bZ → r ≠ fX → r ≠ bA → r ≠ bK →
      rd s4.M r = rd s.M r := fun r h0 a b c d e f =>
    (f4 r h0 a).trans ((f3 r b c).trans (g2 r d e f))
  -- `m += 1`
  obtain ⟨i5, f5, hM5⟩ := bInc_sem I s4 hM4 (r := bM) (x := m) (by decide) (by decide)
    ((G4 _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide)).trans hBm)
  refine ⟨?_, i5, ?_, ?_, hM5⟩
  · rw [rdK_congrB (f5 fPr (by decide)), p4]
  · rw [f5 _ (by decide), G4 _ (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide), hBt]
  · rw [rdK_congrB ((f5 fDs (by decide)).trans (G4 _ (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide))), hDs]

/-- **One entry of `W`**: `W[t] := (Π_{m < k} (m = t ? 1 : G t + G m))⁻¹`, `G m` the element at
`jb + m`. -/
theorem wtBody_sem (I : Array Word) (s : St) (hM : Inv s.M) {k jb wb t : ℕ} {G : ℕ → BF64}
    (hk : k < 2 ^ 64) (ht : t < k) (hjb : regs ≤ jb) (hwb : regs ≤ wb)
    (hjb2 : jb + k < 2 ^ 64) (hwb2 : wb + k < 2 ^ 64) (hsz : wb + k ≤ s.M.size)
    (hG : ∀ m < k, rdK s.M (jb + m) = G m) (hBt : rd s.M bT = toWord t) :
    rdK (semXIR I (wtBody k jb wb) s).M (wb + t) =
      (∏ m ∈ range k, if m = t then 1 else G t + G m)⁻¹ ∧
    rd (semXIR I (wtBody k jb wb) s).M bT = toWord (t + 1) ∧
    (∀ y, regs ≤ y → y ≠ wb + t → rd (semXIR I (wtBody k jb wb) s).M y = rd s.M y) ∧
    Inv (semXIR I (wtBody k jb wb) s).M := by
  have hs := hM.1
  simp only [regs] at hs hjb hwb
  rw [wtBody]
  simp only [semXIR_seq]
  -- `fDs := J_t`
  obtain ⟨a1, f1, hM1⟩ := addr1_sem I s hM (d := bA) (i := bT) (b := jb) (by decide) (by decide)
    (by decide) (by decide) hBt
  have z1 := size_sem I (.blk (addr1Ps bA bT jb)) s
  generalize semXIR I (.blk (addr1Ps bA bT jb)) s = s1 at a1 f1 hM1 z1
  obtain ⟨l2, f2, hM2⟩ := load_sem I s1 hM1 (d := fDs) (p := bA) (x := jb + t) (by decide)
    (by decide) a1 (by (clear * - ht hjb2; omega))
  have z2 := size_sem I (.load fDs bA) s1
  have gt : rdK (semXIR I (.load fDs bA) s1).M fDs = G t := by
    rw [rdK_congrB (l2.trans (f1 _ (by simp only [bA]; (clear * - hjb; omega)) (by simp only [bK]; (clear * - hjb; omega)))),
      hG t ht]
  generalize semXIR I (.load fDs bA) s1 = s2 at l2 f2 hM2 z2 gt
  have g2 : ∀ r, r ≠ fDs → r ≠ bA → r ≠ bK → rd s2.M r = rd s.M r := fun r a b c =>
    (f2 r a).trans (f1 r b c)
  -- the product's constants
  have hs2 := hM2.1
  have q3 : rdK (semXIR I (.blk [.const fPr 1, .const bM 0, .const bN2 (toWord k)]) s2).M fPr = 1 ∧
      rd (semXIR I (.blk [.const fPr 1, .const bM 0, .const bN2 (toWord k)]) s2).M bM =
        toWord 0 ∧
      rd (semXIR I (.blk [.const fPr 1, .const bM 0, .const bN2 (toWord k)]) s2).M bN2 =
        toWord k := by
    rw [sem_blk]
    simp only [runPrims, List.foldl, Prim.run, rdK]
    refine ⟨?_, ?_, ?_⟩ <;>
    simp (disch := first | decide |
      ((try simp only [size_set]); exact lt_of_lt_of_le (by decide) hs2))
      only [rd_set_self, rd_set_ne] <;> rfl
  have f3 : ∀ r, r ≠ fPr → r ≠ bM → r ≠ bN2 →
      rd (semXIR I (.blk [.const fPr 1, .const bM 0, .const bN2 (toWord k)]) s2).M r =
        rd s2.M r := fun r a b c => rd_runPrims_of_not_writes (by
      simp only [List.mem_cons, List.mem_nil_iff, or_false]
      rintro p (rfl | rfl | rfl) <;> simp only [Prim.dst] <;> (clear * - a b c; omega)) _
  have hM3 := inv_sem I (P := .blk [.const fPr 1, .const bM 0, .const bN2 (toWord k)]) (s := s2)
    (by simp [WF, Prim.dst, fPr, bM, bN2]) hM2
  have z3 := size_sem I (.blk [.const fPr 1, .const bM 0, .const bN2 (toWord k)]) s2
  generalize semXIR I (.blk [.const fPr 1, .const bM 0, .const bN2 (toWord k)]) s2 = s3
    at q3 f3 hM3 z3
  have g3 : ∀ r, r ≠ fPr → r ≠ bM → r ≠ bN2 → r ≠ fDs → r ≠ bA → r ≠ bK →
      rd s3.M r = rd s.M r := fun r a b c d e f => (f3 r a b c).trans (g2 r d e f)
  let Q : ℕ → St → Prop := fun j st => Inv st.M ∧ st.M.size = s.M.size ∧
    rdK st.M fPr = (∏ m ∈ range j, if m = t then 1 else G t + G m) ∧ rd st.M bM = toWord j ∧
    rd st.M bT = toWord t ∧ rdK st.M fDs = G t ∧ ∀ y, regs ≤ y → rd st.M y = rd s.M y
  have hQ := loopK_run I (c := bC2) (n := bN2) (K := k) (wInner jb) Q s3 hM3
    (by decide) (by decide) (by decide) q3.2.2 hk ?_ ?_
  rotate_left
  · have ef : ∀ i, i ≠ bC2 → i ≠ cTmp → rd (entryK bC2 bN2 (toWord k) s3.M) i = rd s3.M i :=
      fun i a b => entryK_frame _ (Ne.symm a) (Ne.symm b)
    refine ⟨inv_entryK hM3 (by decide), by rw [size_entryK, z3, z2, z1], ?_, ?_, ?_, ?_,
      fun y hy => ?_⟩
    · rw [rdK_congrB (ef _ (by decide) (by decide)), q3.1, prod_range_zero]
    · rw [ef _ (by decide) (by decide), q3.2.1]
    · rw [ef _ (by decide) (by decide), g3 _ (by decide) (by decide) (by decide) (by decide)
        (by decide) (by decide), hBt]
    · rw [rdK_congrB ((ef _ (by decide) (by decide)).trans
        (f3 _ (by decide) (by decide) (by decide))), gt]
    · simp only [regs] at hy
      rw [ef _ (by simp only [bC2]; (clear * - hy; omega)) (by simp only [cTmp]; (clear * - hy; omega)),
        g3 _ (by simp only [fPr]; (clear * - hy; omega)) (by simp only [bM]; (clear * - hy; omega)) (by simp only [bN2]; (clear * - hy; omega))
          (by simp only [fDs]; (clear * - hy; omega)) (by simp only [bA]; (clear * - hy; omega)) (by simp only [bK]; (clear * - hy; omega))]
  · rintro j st hj ⟨hM', hz, hP, hm, hb, hd, hH⟩
    obtain ⟨w1, w2, w3, w4, hM''⟩ := wInner_sem I st hM' (jb := jb) (m := j) (t := t) (dt := G t)
      (by simp only [regs]; omega) (by (clear * - hjb hjb2 hj; omega)) (by (clear * - ht hjb hjb2; omega)) (by (clear * - hjb2 hj; omega)) hm hb hd
    have hrs : ∀ y, regs ≤ y → rd (semXIR I (wInner jb) st).M y = rd st.M y :=
      fun y hy => hframe I _ st (lo_wInner jb) y hy
    refine ⟨inv_decS hM'' (by decide), by rw [size_decS, size_sem, hz], ?_, ?_, ?_, ?_,
      fun y hy => ?_⟩
    · rw [rdK_congrB (rd_decS (by decide) _), w1, hP, prod_range_succ,
        rdK_congrB (hH (jb + j) (by simp only [regs]; (clear * - hjb; omega))), hG j hj]
    · rw [rd_decS (by decide), w2]
    · rw [rd_decS (by decide), w3]
    · rw [rdK_congrB (rd_decS (by decide) _), w4]
    · rw [rd_decS (by simp only [bC2, regs] at hy ⊢; (clear * - hy; omega)), hrs y hy, hH y hy]
  obtain ⟨Q1, Qz, Q2, -, Q4, -, Q6⟩ := hQ
  generalize semXIR I (.loopK bC2 bN2 (toWord k) (wInner jb)) s3 = s4 at Q1 Qz Q2 Q4 Q6
  -- the inverse
  have v5 := invK_sem (I := I) (s := s4) Q1 (d := fIv) (a := fPr) (by decide) (by decide)
  rw [Q2] at v5
  have hM5 := inv_sem I (wf_invK fIv fPr (by decide)) Q1
  have z5 := size_sem I (invK fIv fPr) s4
  have k5 : ∀ r, 12 ≤ r → r ≠ fIv → rd (semXIR I (invK fIv fPr) s4).M r = rd s4.M r :=
    fun r h0 h1 => frK_inv h0 h1
  generalize semXIR I (invK fIv fPr) s4 = s5 at v5 hM5 k5 z5
  -- `bA := wb + t`
  have t5 : rd s5.M bT = toWord t := (k5 _ (by decide) (by decide)).trans Q4
  obtain ⟨a6, f6, hM6⟩ := addr1_sem I s5 hM5 (d := bA) (i := bT) (b := wb) (by decide)
    (by decide) (by decide) (by decide) t5
  have z6 := size_sem I (.blk (addr1Ps bA bT wb)) s5
  have v6 : rdK (semXIR I (.blk (addr1Ps bA bT wb)) s5).M fIv =
      (∏ m ∈ range k, if m = t then 1 else G t + G m)⁻¹ := by
    rw [rdK_congrB (f6 _ (by decide) (by decide)), v5]
  generalize semXIR I (.blk (addr1Ps bA bT wb)) s5 = s6 at a6 f6 hM6 z6 v6
  -- `W[t] := fIv`
  have hz : wb + t < s6.M.size := by rw [z6, z5, Qz]; (clear * - ht hsz z1 z2 z3 Qz z5 z6; omega)
  obtain ⟨g1, g2', hM7⟩ := store_sem I s6 hM6 (p := bA) (v := fIv) (x := wb + t) (by decide)
    (by decide) a6 (by simp only [regs]; (clear * - hwb; omega)) (by (clear * - ht hwb2; omega)) hz
  have t7 : rd (semXIR I (.store bA fIv) s6).M bT = toWord t := by
    rw [g2' _ (by simp only [bT]; (clear * - hwb; omega)) (by decide), f6 _ (by decide) (by decide), t5]
  generalize semXIR I (.store bA fIv) s6 = s7 at g1 g2' hM7 t7
  obtain ⟨i8, f8, hM8⟩ := bInc_sem I s7 hM7 (r := bT) (x := t) (by decide) (by decide) t7
  refine ⟨?_, i8, fun y hy h1' => ?_, hM8⟩
  · rw [rdK_congrB ((f8 (wb + t) (by simp only [bT]; (clear * - hwb; omega))).trans g1), v6]
  · simp only [regs] at hy
    rw [f8 _ (by simp only [bT]; (clear * - hy; omega)), g2' y h1' (by simp only [cTmp]; (clear * - hy; omega)),
      f6 _ (by simp only [bA]; (clear * - hy; omega)) (by simp only [bK]; (clear * - hy; omega)),
      k5 _ (by (clear * - hy; omega)) (by simp only [fIv]; (clear * - hy; omega)), Q6 y (by simp only [regs]; omega)]

/-- **The table `W`**: `W[t] = (Π_{m<k} (m = t ? 1 : G t + G m))⁻¹` at `wb + t`, `G m` the
element at `jb + m`; nothing else on the heap changes. -/
theorem wtIR_sem (I : Array Word) (s : St) (hM : Inv s.M) {k jb wb : ℕ} {G : ℕ → BF64}
    (hk : k < 2 ^ 64) (hjb : regs ≤ jb) (hwb : regs ≤ wb) (hjb2 : jb + k < 2 ^ 64)
    (hwb2 : wb + k < 2 ^ 64) (hsz : wb + k ≤ s.M.size)
    (hdW : jb + k ≤ wb ∨ wb + k ≤ jb) (hG : ∀ m < k, rdK s.M (jb + m) = G m) :
    (∀ t < k, rdK (semXIR I (wtIR k jb wb) s).M (wb + t) =
      (∏ m ∈ range k, if m = t then 1 else G t + G m)⁻¹) ∧
    (∀ y, regs ≤ y → (y < wb ∨ wb + k ≤ y) →
      rd (semXIR I (wtIR k jb wb) s).M y = rd s.M y) ∧
    Inv (semXIR I (wtIR k jb wb) s).M := by
  have hs := hM.1
  rw [wtIR, semXIR_seq]
  have p1 : rd (semXIR I (.blk [.const bT 0, .const bN1 (toWord k)]) s).M bT = toWord 0 ∧
      rd (semXIR I (.blk [.const bT 0, .const bN1 (toWord k)]) s).M bN1 = toWord k := by
    rw [sem_blk]
    simp only [runPrims, List.foldl, Prim.run]
    refine ⟨?_, ?_⟩ <;>
    simp (disch := first | decide |
      ((try simp only [size_set]); exact lt_of_lt_of_le (by decide) hs))
      only [rd_set_self, rd_set_ne] <;> rfl
  have p3 : ∀ i, i ≠ bT → i ≠ bN1 →
      rd (semXIR I (.blk [.const bT 0, .const bN1 (toWord k)]) s).M i = rd s.M i :=
    fun i h1 h2 => rd_runPrims_of_not_writes (by
      simp only [List.mem_cons, List.mem_nil_iff, or_false]
      rintro p (rfl | rfl) <;> simp only [Prim.dst] <;> (clear * - h1 h2; omega)) _
  have hM1 := inv_sem I (P := .blk [.const bT 0, .const bN1 (toWord k)]) (s := s)
    (by simp [WF, Prim.dst, bT, bN1]) hM
  have z1 := size_sem I (.blk [.const bT 0, .const bN1 (toWord k)]) s
  generalize semXIR I (.blk [.const bT 0, .const bN1 (toWord k)]) s = s1 at p1 p3 hM1 z1
  let P : ℕ → St → Prop := fun j st => Inv st.M ∧ st.M.size = s.M.size ∧ rd st.M bT = toWord j ∧
    (∀ t < j, rdK st.M (wb + t) = (∏ m ∈ range k, if m = t then 1 else G t + G m)⁻¹) ∧
    (∀ y, regs ≤ y → (y < wb ∨ wb + j ≤ y) → rd st.M y = rd s.M y)
  have hfin := loopK_run I (c := bC1) (n := bN1) (K := k) (wtBody k jb wb) P s1 hM1
    (by decide) (by decide) (by decide) p1.2 hk ?_ ?_
  · exact ⟨hfin.2.2.2.1, fun y hy hy2 => hfin.2.2.2.2 y hy hy2, hfin.1⟩
  · refine ⟨inv_entryK hM1 (by decide), by rw [size_entryK, z1], ?_,
      fun t ht => absurd ht (Nat.not_lt_zero _), fun y hy _ => ?_⟩
    · rw [entryK_frame _ (by decide) (by decide), p1.1]
    · simp only [regs] at hy
      rw [entryK_frame _ (by simp only [bC1]; (clear * - hy; omega)) (by simp only [cTmp]; (clear * - hy; omega)),
        p3 _ (by simp only [bT]; (clear * - hy; omega)) (by simp only [bN1]; (clear * - hy; omega))]
  · rintro j st hj ⟨hM', hz, hT', hW, hH⟩
    have hG' : ∀ m < k, rdK st.M (jb + m) = G m := fun m hm => by
      rw [rdK_congrB (hH (jb + m) (by simp only [regs] at hjb ⊢; (clear * - hjb; omega)) (by (clear * - hdW hj hm; omega))), hG m hm]
    obtain ⟨b1, b2, b3, hM2⟩ := wtBody_sem I st hM' hk hj hjb hwb hjb2 hwb2 (by (clear * - hsz z1 hz; omega)) hG' hT'
    refine ⟨inv_decS hM2 (by decide), by rw [size_decS, size_sem, hz], ?_, fun t ht => ?_,
      fun y hy hy2 => ?_⟩
    · rw [rd_decS (by decide), b2]
    · rw [rdK_congrB (rd_decS (by simp only [bC1, regs] at hwb ⊢; (clear * - hwb; omega)) _)]
      rcases Nat.lt_succ_iff_lt_or_eq.1 ht with ht | rfl
      · rw [rdK_congrB (b3 _ (by simp only [regs] at hwb ⊢; (clear * - hwb; omega)) (by (clear * - ht; omega))), hW t ht]
      · exact b1
    · rw [rd_decS (by simp only [bC1, regs] at hy ⊢; (clear * - hy; omega)), b3 y hy (by (clear * - hy2; omega)),
        hH y hy (by (clear * - hy2; omega))]

/-! ## One target's `E` row -/

theorem wf_eBody (jb wb eb : ℕ) : WF (eBody jb wb eb) := by
  simp [eBody, addr1Ps, WF, Prim.dst, wfK_mul, wfK_inv, bA, bK, fX, fDd, fLp, fIv, fEt, bT, cTmp]

/-- **One entry of the `E` row**: `E[t] := W[t] · (ds + J_t)⁻¹`, `ℓ *= ds + J_t`. -/
theorem eBody_sem (I : Array Word) (s : St) (hM : Inv s.M) {jb wb eb t : ℕ} {ds lp g w : BF64}
    (hjb : regs ≤ jb) (hwb : regs ≤ wb) (heb : regs ≤ eb) (hjb2 : jb + t < 2 ^ 64)
    (hwb2 : wb + t < 2 ^ 64) (heb2 : eb + t < 2 ^ 64)
    (hsz : eb + t < s.M.size) (hBt : rd s.M bT = toWord t) (hDs : rdK s.M fDs = ds)
    (hLp : rdK s.M fLp = lp) (hG : rdK s.M (jb + t) = g) (hW : rdK s.M (wb + t) = w) :
    rdK (semXIR I (eBody jb wb eb) s).M (eb + t) = w * (ds + g)⁻¹ ∧
    rdK (semXIR I (eBody jb wb eb) s).M fLp = lp * (ds + g) ∧
    rd (semXIR I (eBody jb wb eb) s).M bT = toWord (t + 1) ∧
    rdK (semXIR I (eBody jb wb eb) s).M fDs = ds ∧
    (∀ y, regs ≤ y → y ≠ eb + t → rd (semXIR I (eBody jb wb eb) s).M y = rd s.M y) ∧
    Inv (semXIR I (eBody jb wb eb) s).M := by
  have hs := hM.1
  simp only [regs] at hs hjb hwb heb
  rw [eBody]
  simp only [semXIR_seq]
  -- `fX := J_t`
  obtain ⟨a1, f1, hM1⟩ := addr1_sem I s hM (d := bA) (i := bT) (b := jb) (by decide) (by decide)
    (by decide) (by decide) hBt
  have z1 := size_sem I (.blk (addr1Ps bA bT jb)) s
  generalize semXIR I (.blk (addr1Ps bA bT jb)) s = s1 at a1 f1 hM1 z1
  obtain ⟨l2, f2, hM2⟩ := load_sem I s1 hM1 (d := fX) (p := bA) (x := jb + t) (by decide)
    (by decide) a1 hjb2
  rw [f1 _ (by simp only [bA]; (clear * - hjb; omega)) (by simp only [bK]; (clear * - hjb; omega))] at l2
  have z2 := size_sem I (.load fX bA) s1
  generalize semXIR I (.load fX bA) s1 = s2 at l2 f2 hM2 z2
  have g2 : ∀ r, r ≠ fX → r ≠ bA → r ≠ bK → rd s2.M r = rd s.M r := fun r a b c =>
    (f2 r a).trans (f1 r b c)
  -- `fDd := ds + J_t`
  have hs2 := hM2.1
  have d3 : rdK (semXIR I (.blk [.op .xor fDd fDs fX]) s2).M fDd = ds + g := by
    rw [sem_blk, rdK, rd_xor_run (lt_of_lt_of_le (by decide) hs2), wK_xor,
      g2 fDs (by decide) (by decide) (by decide), l2]
    show rdK s.M fDs + rdK s.M (jb + t) = ds + g
    rw [hDs, hG]
  have f3 : ∀ r, r ≠ fDd → rd (semXIR I (.blk [.op .xor fDd fDs fX]) s2).M r = rd s2.M r :=
    fun r h => xorC_frame _ _ _ h _
  have hM3 : Inv (semXIR I (.blk [.op .xor fDd fDs fX]) s2).M := xorC_inv _ _ _ (by decide) hM2
  have z3 := size_sem I (.blk [.op .xor fDd fDs fX]) s2
  generalize semXIR I (.blk [.op .xor fDd fDs fX]) s2 = s3 at d3 f3 hM3 z3
  -- `ℓ *= fDd`
  have m4 := mulK_sem (I := I) (s := s3) hM3 (d := fLp) (a := fLp) (b := fDd) (by decide)
    (by decide) (by decide) (by decide)
  rw [d3, rdK_congrB ((f3 _ (by decide)).trans (g2 _ (by decide) (by decide) (by decide))),
    hLp] at m4
  have hM4 := inv_sem I (wf_mulK fLp fLp fDd (by decide)) hM3
  have z4 := size_sem I (mulK fLp fLp fDd) s3
  have f4 : ∀ r, 9 ≤ r → r ≠ fLp → rd (semXIR I (mulK fLp fLp fDd) s3).M r = rd s3.M r :=
    fun r h0 h1 => frK_mul h0 h1
  have dd4 : rdK (semXIR I (mulK fLp fLp fDd) s3).M fDd = ds + g := by
    rw [rdK_congrB (f4 _ (by decide) (by decide)), d3]
  generalize semXIR I (mulK fLp fLp fDd) s3 = s4 at m4 hM4 z4 f4 dd4
  -- `fIv := fDd⁻¹`
  have v5 := invK_sem (I := I) (s := s4) hM4 (d := fIv) (a := fDd) (by decide) (by decide)
  rw [dd4] at v5
  have hM5 := inv_sem I (wf_invK fIv fDd (by decide)) hM4
  have z5 := size_sem I (invK fIv fDd) s4
  have f5 : ∀ r, 12 ≤ r → r ≠ fIv → rd (semXIR I (invK fIv fDd) s4).M r = rd s4.M r :=
    fun r h0 h1 => frK_inv h0 h1
  generalize semXIR I (invK fIv fDd) s4 = s5 at v5 hM5 z5 f5
  -- the registers so far, against `s`
  have K5 : ∀ r, 12 ≤ r → r ≠ fIv → r ≠ fLp → r ≠ fDd → r ≠ fX → r ≠ bA → r ≠ bK →
      rd s5.M r = rd s.M r := fun r h0 a b c d e f =>
    (f5 r h0 a).trans ((f4 r (by (clear * - h0; omega)) b).trans ((f3 r c).trans (g2 r d e f)))
  have Lp5 : rdK s5.M fLp = lp * (ds + g) := by
    rw [rdK_congrB (f5 _ (by decide) (by decide)), m4]
  have t5 : rd s5.M bT = toWord t := (K5 _ (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide)).trans hBt
  have hH5 : ∀ y, 256 ≤ y → rd s5.M y = rd s.M y := fun y hy =>
    K5 y (by (clear * - hy; omega)) (by simp only [fIv]; (clear * - hy; omega)) (by simp only [fLp]; (clear * - hy; omega))
      (by simp only [fDd]; (clear * - hy; omega)) (by simp only [fX]; (clear * - hy; omega)) (by simp only [bA]; (clear * - hy; omega))
      (by simp only [bK]; (clear * - hy; omega))
  -- `fX := W[t]`
  obtain ⟨a6, f6, hM6⟩ := addr1_sem I s5 hM5 (d := bA) (i := bT) (b := wb) (by decide)
    (by decide) (by decide) (by decide) t5
  have z6 := size_sem I (.blk (addr1Ps bA bT wb)) s5
  generalize semXIR I (.blk (addr1Ps bA bT wb)) s5 = s6 at a6 f6 hM6 z6
  obtain ⟨l7, f7, hM7⟩ := load_sem I s6 hM6 (d := fX) (p := bA) (x := wb + t) (by decide)
    (by decide) a6 hwb2
  have w7 : rdK (semXIR I (.load fX bA) s6).M fX = w := by
    rw [rdK_congrB (l7.trans ((f6 _ (by simp only [bA]; (clear * - hwb; omega)) (by simp only [bK]; (clear * - hwb; omega))).trans
      (hH5 _ (by (clear * - hjb hwb hjb2; omega))))), hW]
  have z7 := size_sem I (.load fX bA) s6
  generalize semXIR I (.load fX bA) s6 = s7 at l7 f7 hM7 z7 w7
  have k7 : ∀ r, r ≠ fX → r ≠ bA → r ≠ bK → rd s7.M r = rd s5.M r := fun r a b c =>
    (f7 r a).trans (f6 r b c)
  -- `fEt := W[t] · fIv`
  have m8 := mulK_sem (I := I) (s := s7) hM7 (d := fEt) (a := fX) (b := fIv) (by decide)
    (by decide) (by decide) (by decide)
  rw [w7, rdK_congrB (k7 _ (by decide) (by decide) (by decide)), v5] at m8
  have hM8 := inv_sem I (wf_mulK fEt fX fIv (by decide)) hM7
  have z8 := size_sem I (mulK fEt fX fIv) s7
  have k8 : ∀ r, 9 ≤ r → r ≠ fEt → r ≠ fX → r ≠ bA → r ≠ bK →
      rd (semXIR I (mulK fEt fX fIv) s7).M r = rd s5.M r := fun r h0 a b c d =>
    (frK_mul h0 a).trans (k7 r b c d)
  generalize semXIR I (mulK fEt fX fIv) s7 = s8 at m8 hM8 z8 k8
  -- `E[t] := fEt`
  have t8 : rd s8.M bT = toWord t := (k8 _ (by decide) (by decide) (by decide) (by decide)
    (by decide)).trans t5
  obtain ⟨a9, f9, hM9⟩ := addr1_sem I s8 hM8 (d := bA) (i := bT) (b := eb) (by decide)
    (by decide) (by decide) (by decide) t8
  have z9 := size_sem I (.blk (addr1Ps bA bT eb)) s8
  have E9 : rdK (semXIR I (.blk (addr1Ps bA bT eb)) s8).M fEt = w * (ds + g)⁻¹ := by
    rw [rdK_congrB (f9 _ (by decide) (by decide)), m8]
  generalize semXIR I (.blk (addr1Ps bA bT eb)) s8 = s9 at a9 f9 hM9 z9 E9
  have hz : eb + t < s9.M.size := by rw [z9, z8, z7, z6, z5, z4, z3, z2, z1]; exact hsz
  obtain ⟨g1, g2', hM10⟩ := store_sem I s9 hM9 (p := bA) (v := fEt) (x := eb + t) (by decide)
    (by decide) a9 (by simp only [regs]; (clear * - hjb heb hjb2; omega)) heb2 hz
  have K10 : ∀ r, r < 256 → r ≠ cTmp → r ≠ bA → r ≠ bK →
      rd (semXIR I (.store bA fEt) s9).M r = rd s8.M r := fun r hr a b c => by
    rw [g2' r (by (clear * - hjb heb hjb2 hr; omega)) a, f9 r b c]
  generalize semXIR I (.store bA fEt) s9 = s10 at g1 g2' hM10 K10
  have t10 : rd s10.M bT = toWord t := (K10 _ (by decide) (by decide) (by decide)
    (by decide)).trans t8
  obtain ⟨i11, f11, hM11⟩ := bInc_sem I s10 hM10 (r := bT) (x := t) (by decide) (by decide) t10
  have back : ∀ r, 12 ≤ r → r < 256 → r ≠ bT → r ≠ cTmp → r ≠ bA → r ≠ bK → r ≠ fEt →
      r ≠ fX → rd (semXIR I (.blk [.op .add bT bT cOne]) s10).M r = rd s5.M r :=
    fun r h0 hr a b c d e f => (f11 r a).trans ((K10 r hr b c d).trans (k8 r (by (clear * - h0 hr; omega)) e f c d))
  refine ⟨?_, ?_, i11, ?_, fun y hy h1' => ?_, hM11⟩
  · rw [rdK_congrB ((f11 (eb + t) (by simp only [bT]; (clear * - heb; omega))).trans g1), E9]
  · rw [rdK_congrB (back _ (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide)), Lp5]
  · rw [rdK_congrB ((back _ (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide)).trans (K5 _ (by decide) (by decide) (by decide)
        (by decide) (by decide) (by decide) (by decide))), hDs]
  · simp only [regs] at hy
    rw [f11 _ (by simp only [bT]; (clear * - hy; omega)), g2' y h1' (by simp only [cTmp]; (clear * - hy; omega)),
      f9 _ (by simp only [bA]; (clear * - hy; omega)) (by simp only [bK]; (clear * - hy; omega)),
      k8 _ (by (clear * - hy; omega)) (by simp only [fEt]; (clear * - hy; omega)) (by simp only [fX]; (clear * - hy; omega))
        (by simp only [bA]; (clear * - hy; omega)) (by simp only [bK]; (clear * - hy; omega)), hH5 y hy]

/-- **The `E` row**: `E[t] = W[t] (ds + J_t)⁻¹` for `t < k`, `ℓ = Π_t (ds + J_t)`. -/
theorem eLoop_sem (I : Array Word) (s : St) (hM : Inv s.M) {k jb wb eb : ℕ} {ds : BF64}
    (hk : k < 2 ^ 64) (hjb : regs ≤ jb) (hwb : regs ≤ wb) (heb : regs ≤ eb)
    (hjb2 : jb + k < 2 ^ 64) (hwb2 : wb + k < 2 ^ 64) (heb2 : eb + k < 2 ^ 64)
    (hsz : eb + k ≤ s.M.size) (hjE : jb + k ≤ eb ∨ eb + k ≤ jb)
    (hwE : wb + k ≤ eb ∨ eb + k ≤ wb)
    (hN : rd s.M bN2 = toWord k) (hBt : rd s.M bT = toWord 0) (hDs : rdK s.M fDs = ds)
    (hLp : rdK s.M fLp = 1) :
    (∀ t < k, rdK (semXIR I (.loopK bC2 bN2 (toWord k) (eBody jb wb eb)) s).M (eb + t) =
      rdK s.M (wb + t) * (ds + rdK s.M (jb + t))⁻¹) ∧
    rdK (semXIR I (.loopK bC2 bN2 (toWord k) (eBody jb wb eb)) s).M fLp =
      ∏ t ∈ range k, (ds + rdK s.M (jb + t)) ∧
    (∀ y, regs ≤ y → (y < eb ∨ eb + k ≤ y) →
      rd (semXIR I (.loopK bC2 bN2 (toWord k) (eBody jb wb eb)) s).M y = rd s.M y) ∧
    (∀ r, r < regs → r ≠ bC2 → r ≠ cTmp → ¬ Writes (eBody jb wb eb) r →
      rd (semXIR I (.loopK bC2 bN2 (toWord k) (eBody jb wb eb)) s).M r = rd s.M r) ∧
    Inv (semXIR I (.loopK bC2 bN2 (toWord k) (eBody jb wb eb)) s).M := by
  let Q : ℕ → St → Prop := fun j st => Inv st.M ∧ st.M.size = s.M.size ∧ rd st.M bT = toWord j ∧
    rdK st.M fDs = ds ∧ rdK st.M fLp = ∏ t ∈ range j, (ds + rdK s.M (jb + t)) ∧
    (∀ t < j, rdK st.M (eb + t) = rdK s.M (wb + t) * (ds + rdK s.M (jb + t))⁻¹) ∧
    (∀ y, regs ≤ y → (y < eb ∨ eb + j ≤ y) → rd st.M y = rd s.M y) ∧
    (∀ r, r < regs → r ≠ bC2 → r ≠ cTmp → ¬ Writes (eBody jb wb eb) r → rd st.M r = rd s.M r)
  have ef : ∀ i, i ≠ bC2 → i ≠ cTmp → rd (entryK bC2 bN2 (toWord k) s.M) i = rd s.M i :=
    fun i a b => entryK_frame _ (Ne.symm a) (Ne.symm b)
  have h := loopK_run I (c := bC2) (n := bN2) (K := k) (eBody jb wb eb) Q s hM (by decide)
    (by decide) (by decide) hN hk ⟨inv_entryK hM (by decide), size_entryK .., by
        rw [ef _ (by decide) (by decide), hBt],
      by rw [rdK_congrB (ef _ (by decide) (by decide)), hDs],
      by rw [rdK_congrB (ef _ (by decide) (by decide)), hLp, prod_range_zero],
      fun t ht => absurd ht (Nat.not_lt_zero _),
      fun y hy _ => ef y (by simp only [regs, bC2] at hy ⊢; (clear * - hy; omega))
        (by simp only [regs, cTmp] at hy ⊢; (clear * - hy; omega)),
      fun r _ h1 h2 _ => ef r h1 h2⟩ ?_
  · exact ⟨h.2.2.2.2.2.1, h.2.2.2.2.1, fun y hy hy2 => h.2.2.2.2.2.2.1 y hy hy2,
      h.2.2.2.2.2.2.2, h.1⟩
  · rintro j st hj ⟨hM', hz, hT', hD, hL, hE, hH, hR⟩
    simp only [regs] at hjb hwb heb
    have hG : rdK st.M (jb + j) = rdK s.M (jb + j) :=
      rdK_congrB (hH _ (by simp only [regs]; (clear * - hjb; omega)) (by (clear * - hjE hwE hj; omega)))
    have hW : rdK st.M (wb + j) = rdK s.M (wb + j) :=
      rdK_congrB (hH _ (by simp only [regs]; (clear * - hwb; omega)) (by (clear * - hwE hj; omega)))
    obtain ⟨b1, b2, b3, b4, b5, hM2⟩ := eBody_sem I st hM' (t := j) (by simp only [regs]; omega)
      (by simp only [regs]; omega) (by simp only [regs]; omega) (by (clear * - hjb2 hj; omega)) (by (clear * - hwb2 hj; omega)) (by (clear * - heb2 hj; omega))
      (by (clear * - hsz hj hz; omega)) hT' hD hL hG hW
    refine ⟨inv_decS hM2 (by decide), by rw [size_decS, size_sem, hz],
      by rw [rd_decS (by decide), b3],
      by rw [rdK_congrB (rd_decS (by decide) _), b4],
      by rw [rdK_congrB (rd_decS (by decide) _), b2, prod_range_succ], fun t ht => ?_,
      fun y hy hy2 => ?_, fun r hr h1 h2 h3 => ?_⟩
    · rw [rdK_congrB (rd_decS (by simp only [bC2]; (clear * - heb; omega)) _)]
      rcases Nat.lt_succ_iff_lt_or_eq.1 ht with ht | rfl
      · rw [rdK_congrB (b5 _ (by simp only [regs]; (clear * - heb; omega)) (by (clear * - ht; omega))), hE t ht]
      · exact b1
    · rw [rd_decS (by simp only [bC2, regs] at hy ⊢; (clear * - hy; omega)), b5 y hy (by (clear * - hy2; omega)),
        hH y hy (by (clear * - hy2; omega))]
    · rw [rd_decS (Ne.symm h1), frame I _ st (wf_eBody jb wb eb) hM' r hr h3, hR r hr h1 h2 h3]

end Lvm.X
end
-- ===== end of `LvmXInterp2` =====

-- ===== merged from `LvmXInterp3` (GOLF module merge: `LvmXInterp3.lean` is now a stub importing `LvmXInterp4`) =====
section
-- adapted from rf-k/submissions/flock-recursive/lean/FRXBary.lean@8bff272b (`aBody_sem`, `aLoop_sem`,
-- `cBody_sem`, `cLoop_sem`) for lvm (WP-13b): FR's two-word `F` re-targeted to `K = BF64`; a
-- coordinate's offset is `c` (FR: `2c` in `bCo`), the output cell `ob + k·c + s` (FR: `ob + 2kc + 2s`).

/-!
# The barycentric interpolation on the machine (2): one coordinate, the coordinate loop

`aLoop_sem`: `acc = Σ_{t<k} y_c(J_t) E[t]`; `cBody_sem`: `out[c][s] := (ℓ = 0 ? y_c(s) : ℓ · acc)`;
**`cLoop_sem`**: every coordinate `c < C` of one target `s`.
-/

namespace Lvm.X

open RecursionFast Finset

attribute [local irreducible] entryK storeM

/-! ## Arithmetic of the cells -/

theorem lt_mulB {k c j : ℕ} (h : c < j) : k * c + k ≤ k * j := by
  have := Nat.mul_le_mul_left k (show c + 1 ≤ j by omega)
  rw [Nat.mul_add, Nat.mul_one] at this; omega

/-- Output cell `(c, s)` lies in the output rows. -/
theorem out_ltB {k c C s : ℕ} (hc : c < C) (hs : s < k) : k * c + s < k * C := by
  have := lt_mulB (k := k) hc; (clear * - hs this; omega)

/-- Distinct targets have distinct output cells. -/
theorem cellB_ne {k c c' s s' : ℕ} (hs : s < k) (hs' : s' < k) (hne : s ≠ s') :
    k * c + s ≠ k * c' + s' := by
  intro h
  have h3 : c = c' := by
    have := congrArg (· / k) h
    rwa [Nat.mul_add_div (by (clear * - hs h; omega)), Nat.mul_add_div (by (clear * - hs h; omega)), Nat.div_eq_of_lt hs,
      Nat.div_eq_of_lt hs', add_zero, add_zero] at this
  subst h3; (clear * - hne h; omega)

/-! ## One coordinate's accumulation -/

theorem lo_aBody (jb eb cb cs : ℕ) : Lo (aBody jb eb cb cs) := by
  simp [aBody, Lo, addrPs, addr1Ps, Prim.dst, regs, bK, bA, bJ, bT, fY, fX, fAc, bCi, fPr]
  exact lo_mulK (by decide)

theorem wf_aBody (jb eb cb cs : ℕ) : WF (aBody jb eb cb cs) := by
  simp [aBody, addrPs, addr1Ps, WF, Prim.dst, wfK_mul, bA, bK, bJ, fY, fX, fPr, fAc, bT, bCi]

/-- **One term of `acc`**: `acc += y(J_t) · E[t]`, `y(j)` at `cb + cs·j + c`. -/
theorem aBody_sem (I : Array Word) (s : St) (hM : Inv s.M) {jb eb cb cs t c x : ℕ} {acc : BF64}
    (hjb : regs ≤ jb) (heb : regs ≤ eb) (hcb : regs ≤ cb) (hjb2 : jb + t < 2 ^ 64)
    (heb2 : eb + t < 2 ^ 64) (hcb2 : cb + cs * x + c < 2 ^ 64)
    (hBt : rd s.M bT = toWord t) (hCi : rd s.M bCi = toWord c) (hAc : rdK s.M fAc = acc)
    (hJ : rd s.M (jb + t) = toWord x) :
    rdK (semXIR I (aBody jb eb cb cs) s).M fAc =
      acc + rdK s.M (cb + cs * x + c) * rdK s.M (eb + t) ∧
    rd (semXIR I (aBody jb eb cb cs) s).M bT = toWord (t + 1) ∧
    Inv (semXIR I (aBody jb eb cb cs) s).M := by
  simp only [regs] at hjb heb hcb
  rw [aBody]
  simp only [semXIR_seq, sem_blk_append]
  -- `bA := jb + t`, `bJ := J_t`
  obtain ⟨a1, f1, hM1⟩ := addr1_sem I s hM (d := bA) (i := bT) (b := jb) (by decide) (by decide)
    (by decide) (by decide) hBt
  generalize semXIR I (.blk (addr1Ps bA bT jb)) s = s1 at a1 f1 hM1
  obtain ⟨l2, f2, hM2⟩ := load_sem I s1 hM1 (d := bJ) (p := bA) (x := jb + t) (by decide)
    (by decide) a1 hjb2
  rw [f1 _ (by simp only [bA]; (clear * - hjb; omega)) (by simp only [bK]; (clear * - hjb; omega)), hJ] at l2
  generalize semXIR I (.load bJ bA) s1 = s2 at l2 f2 hM2
  have k2 : ∀ r, r ≠ bJ → r ≠ bA → r ≠ bK → rd s2.M r = rd s.M r := fun r a b c =>
    (f2 r a).trans (f1 r b c)
  -- `bJ := cb + cs·x`, `bJ += c`
  obtain ⟨c3, f3, hM3⟩ := addr_sem I s2 hM2 (d := bJ) (i := bJ) (b := cb) (m := cs) (x := x)
    (by decide) (by decide) (by decide) (by decide) l2
  generalize semXIR I (.blk (addrPs bJ bJ cb cs)) s2 = s3 at c3 f3 hM3
  obtain ⟨c4, f4, hM4⟩ := bAdd_sem I s3 hM3 (d := bJ) (r := bCi) (x := cb + cs * x) (y := c)
    (by decide) (by decide) c3
    ((f3 _ (by decide) (by decide)).trans ((k2 _ (by decide) (by decide) (by decide)).trans hCi))
  generalize semXIR I (.blk [.op .add bJ bJ bCi]) s3 = s4 at c4 f4 hM4
  have k4 : ∀ r, r ≠ bJ → r ≠ bA → r ≠ bK → rd s4.M r = rd s.M r := fun r a b c =>
    (f4 r a).trans ((f3 r a c).trans (k2 r a b c))
  -- `fY := y(J_t)`
  obtain ⟨l5, f5, hM5⟩ := load_sem I s4 hM4 (d := fY) (p := bJ) (x := cb + cs * x + c)
    (by decide) (by decide) c4 hcb2
  have hy : rdK (semXIR I (.load fY bJ) s4).M fY = rdK s.M (cb + cs * x + c) :=
    rdK_congrB (l5.trans (k4 _ (by simp only [bJ]; (clear * - hcb; omega)) (by simp only [bA]; (clear * - hcb; omega))
      (by simp only [bK]; (clear * - hcb; omega))))
  generalize semXIR I (.load fY bJ) s4 = s5 at l5 f5 hM5 hy
  have k5 : ∀ r, r ≠ fY → r ≠ bJ → r ≠ bA → r ≠ bK → rd s5.M r = rd s.M r := fun r a b c d =>
    (f5 r a).trans (k4 r b c d)
  -- `fX := E[t]`
  obtain ⟨a6, f6, hM6⟩ := addr1_sem I s5 hM5 (d := bA) (i := bT) (b := eb) (by decide)
    (by decide) (by decide) (by decide)
    ((k5 _ (by decide) (by decide) (by decide) (by decide)).trans hBt)
  generalize semXIR I (.blk (addr1Ps bA bT eb)) s5 = s6 at a6 f6 hM6
  obtain ⟨l7, f7, hM7⟩ := load_sem I s6 hM6 (d := fX) (p := bA) (x := eb + t) (by decide)
    (by decide) a6 heb2
  have he : rdK (semXIR I (.load fX bA) s6).M fX = rdK s.M (eb + t) :=
    rdK_congrB (l7.trans ((f6 _ (by simp only [bA]; (clear * - heb; omega)) (by simp only [bK]; (clear * - heb; omega))).trans
      (k5 _ (by simp only [fY]; (clear * - heb; omega)) (by simp only [bJ]; (clear * - heb; omega)) (by simp only [bA]; (clear * - heb; omega))
        (by simp only [bK]; (clear * - heb; omega)))))
  generalize semXIR I (.load fX bA) s6 = s7 at l7 f7 hM7 he
  have k7 : ∀ r, r ≠ fX → r ≠ bA → r ≠ bK → rd s7.M r = rd s5.M r := fun r a b c =>
    (f7 r a).trans (f6 r b c)
  -- `fPr := y · E`
  have m8 := mulK_sem (I := I) (s := s7) hM7 (d := fPr) (a := fY) (b := fX) (by decide)
    (by decide) (by decide) (by decide)
  rw [rdK_congrB (k7 fY (by decide) (by decide) (by decide)), hy, he] at m8
  have hM8 := inv_sem I (wf_mulK fPr fY fX (by decide)) hM7
  have k8 : ∀ r, 9 ≤ r → r ≠ fPr → r ≠ fX → r ≠ bA → r ≠ bK →
      rd (semXIR I (mulK fPr fY fX) s7).M r = rd s5.M r := fun r h0 a b c d =>
    (frK_mul h0 a).trans (k7 r b c d)
  generalize semXIR I (mulK fPr fY fX) s7 = s8 at m8 hM8 k8
  -- `fAc += fPr`, `t += 1`
  have hs8 := hM8.1
  have h1 : rd s8.M cOne = 1 := hM8.2 0 (by decide)
  have ac8 : rd s8.M fAc = rd s.M fAc := (k8 fAc (by decide) (by decide) (by decide) (by decide)
    (by decide)).trans (k5 _ (by decide) (by decide) (by decide) (by decide))
  have t8 : rd s8.M bT = toWord t := (k8 bT (by decide) (by decide) (by decide) (by decide)
    (by decide)).trans ((k5 _ (by decide) (by decide) (by decide) (by decide)).trans hBt)
  refine ⟨?_, ?_, inv_sem I (P := .blk [.op .xor fAc fAc fPr, .op .add bT bT cOne])
    (by simp [WF, Prim.dst, fAc, bT]) hM8⟩
  · rw [sem_blk]
    simp only [runPrims, List.foldl, Prim.run]
    rw [rdK]
    simp (disch := first | decide |
      ((try simp only [size_set]); exact lt_of_lt_of_le (by decide) hs8))
      only [rd_set_self, rd_set_ne]
    rw [eval_xor, wK_xor, ac8]
    show rdK s.M fAc + rdK s8.M fPr = _
    rw [hAc, m8]
  · rw [sem_blk]
    simp only [runPrims, List.foldl, Prim.run]
    simp (disch := first | decide |
      ((try simp only [size_set]); exact lt_of_lt_of_le (by decide) hs8))
      only [rd_set_self, rd_set_ne]
    rw [t8, h1, add_one_toWord]

/-- **The accumulation loop**: `acc = Σ_{t<k} y(J_t) · E[t]`. -/
theorem aLoop_sem (I : Array Word) (s : St) (hM : Inv s.M) {k jb eb cb cs c : ℕ} {x : ℕ → ℕ}
    (hk : k < 2 ^ 64) (hjb : regs ≤ jb) (heb : regs ≤ eb) (hcb : regs ≤ cb)
    (hjb2 : jb + k < 2 ^ 64) (heb2 : eb + k < 2 ^ 64)
    (hcb2 : ∀ t < k, cb + cs * x t + c < 2 ^ 64)
    (hN : rd s.M bN3 = toWord k) (hBt : rd s.M bT = toWord 0) (hCi : rd s.M bCi = toWord c)
    (hAc : rdK s.M fAc = 0) (hJ : ∀ t < k, rd s.M (jb + t) = toWord (x t)) :
    rdK (semXIR I (.loopK bC3 bN3 (toWord k) (aBody jb eb cb cs)) s).M fAc =
      ∑ t ∈ range k, rdK s.M (cb + cs * x t + c) * rdK s.M (eb + t) ∧
    Inv (semXIR I (.loopK bC3 bN3 (toWord k) (aBody jb eb cb cs)) s).M ∧
    (∀ y, regs ≤ y → rd (semXIR I (.loopK bC3 bN3 (toWord k) (aBody jb eb cb cs)) s).M y =
      rd s.M y) ∧
    (∀ r, r < regs → r ≠ bC3 → r ≠ cTmp → ¬ Writes (aBody jb eb cb cs) r →
      rd (semXIR I (.loopK bC3 bN3 (toWord k) (aBody jb eb cb cs)) s).M r = rd s.M r) := by
  let Q : ℕ → St → Prop := fun j st => Inv st.M ∧
    rdK st.M fAc = ∑ t ∈ range j, rdK s.M (cb + cs * x t + c) * rdK s.M (eb + t) ∧
    rd st.M bT = toWord j ∧ (∀ y, regs ≤ y → rd st.M y = rd s.M y) ∧
    (∀ r, r < regs → r ≠ bC3 → r ≠ cTmp → ¬ Writes (aBody jb eb cb cs) r → rd st.M r = rd s.M r)
  have ef : ∀ i, i ≠ bC3 → i ≠ cTmp → rd (entryK bC3 bN3 (toWord k) s.M) i = rd s.M i :=
    fun i a b => entryK_frame _ (Ne.symm a) (Ne.symm b)
  refine (loopK_run I (c := bC3) (n := bN3) (K := k) (aBody jb eb cb cs) Q s hM (by decide)
    (by decide) (by decide) hN hk ⟨inv_entryK hM (by decide), ?_, ?_, fun y hy => ?_,
      fun r _ h1 h2 _ => ef r h1 h2⟩ ?_) |> fun h => ⟨h.2.1, h.1, h.2.2.2.1, h.2.2.2.2⟩
  · rw [rdK_congrB (ef _ (by decide) (by decide)), hAc, sum_range_zero]
  · rw [ef _ (by decide) (by decide), hBt]
  · simp only [regs] at hy
    exact ef y (by simp only [bC3]; (clear * - hy; omega)) (by simp only [cTmp]; (clear * - hy; omega))
  · rintro j st hj ⟨hM', hA, hT', hH, hR⟩
    have hJ' : rd st.M (jb + j) = toWord (x j) := by
      rw [hH _ (by simp only [regs] at hjb ⊢; (clear * - hjb; omega)), hJ j hj]
    have hCi' : rd st.M bCi = toWord c := by
      rw [hR _ (by decide) (by decide) (by decide) (by
        simp [aBody, addrPs, addr1Ps, Writes, Prim.dst, bnw_mulK, bCi, fPr, fAc, bA, bK, bJ, fY,
          fX, bT]), hCi]
    obtain ⟨b1, b2, hM2⟩ := aBody_sem I st hM' (t := j) (c := c) (x := x j) hjb heb hcb (by (clear * - hjb2 hj; omega))
      (by (clear * - heb2 hj; omega)) (hcb2 j hj) hT' hCi' hA hJ'
    have hH2 : ∀ y, regs ≤ y → rd (semXIR I (aBody jb eb cb cs) st).M y = rd st.M y :=
      fun y hy => hframe I _ st (lo_aBody jb eb cb cs) y hy
    refine ⟨inv_decS hM2 (by decide), ?_, by rw [rd_decS (by decide), b2], fun y hy => ?_,
      fun r hr h1 h2 h3 => ?_⟩
    · rw [rdK_congrB (rd_decS (by decide) _), b1, sum_range_succ,
        rdK_congrB (hH (cb + cs * x j + c) (by simp only [regs] at hcb ⊢; (clear * - hcb; omega))),
        rdK_congrB (hH (eb + j) (by simp only [regs] at heb ⊢; (clear * - heb; omega)))]
    · rw [rd_decS (by simp only [bC3, regs] at hy ⊢; (clear * - hy; omega)), hH2 y hy, hH y hy]
    · rw [rd_decS (Ne.symm h1), frame I _ st (wf_aBody jb eb cb cs) hM' r hr h3,
        hR r hr h1 h2 h3]

/-! ## One coordinate -/

/-- **One coordinate `c`**: `out[c][s] := (ℓ = 0 ? y_c(s) : ℓ · Σ_t y_c(J_t) E[t])` at
`ob + k·c + s`; `c += 1`. -/
theorem cBody_sem (I : Array Word) (s : St) (hM : Inv s.M)
    {k jb eb cb cs ob c s0 : ℕ} {x : ℕ → ℕ} {lp : BF64}
    (hk : k < 2 ^ 64) (hjb : regs ≤ jb) (heb : regs ≤ eb) (hcb : regs ≤ cb) (hob : regs ≤ ob)
    (hjb2 : jb + k < 2 ^ 64) (heb2 : eb + k < 2 ^ 64)
    (hcb2 : ∀ t < k, cb + cs * x t + c < 2 ^ 64) (hcs2 : cb + cs * s0 + c < 2 ^ 64)
    (hob2 : ob + k * c + s0 < 2 ^ 64) (hsz : ob + k * c + s0 < s.M.size)
    (hCi : rd s.M bCi = toWord c) (hS : rd s.M bS = toWord s0)
    (hLp : rdK s.M fLp = lp) (hZ : rd s.M bZ = bW (decide (lp = 0)))
    (hJ : ∀ t < k, rd s.M (jb + t) = toWord (x t)) :
    rdK (semXIR I (cBody k jb eb cb cs ob) s).M (ob + k * c + s0) =
      (if lp = 0 then rdK s.M (cb + cs * s0 + c) else
        lp * ∑ t ∈ range k, rdK s.M (cb + cs * x t + c) * rdK s.M (eb + t)) ∧
    rd (semXIR I (cBody k jb eb cb cs ob) s).M bCi = toWord (c + 1) ∧
    (∀ y, regs ≤ y → y ≠ ob + k * c + s0 →
      rd (semXIR I (cBody k jb eb cb cs ob) s).M y = rd s.M y) ∧
    Inv (semXIR I (cBody k jb eb cb cs ob) s).M := by
  have hs := hM.1
  simp only [regs] at hs hjb heb hcb hob
  rw [cBody]
  simp only [semXIR_seq, sem_blk_append]
  -- `acc := 0`, `t := 0`, `bN3 := k`
  have q1 : rdK (semXIR I (.blk [.const fAc 0, .const bT 0, .const bN3 (toWord k)]) s).M fAc = 0 ∧
      rd (semXIR I (.blk [.const fAc 0, .const bT 0, .const bN3 (toWord k)]) s).M bT =
        toWord 0 ∧
      rd (semXIR I (.blk [.const fAc 0, .const bT 0, .const bN3 (toWord k)]) s).M bN3 =
        toWord k := by
    rw [sem_blk]
    simp only [runPrims, List.foldl, Prim.run, rdK]
    refine ⟨?_, ?_, ?_⟩ <;>
    simp (disch := first | decide |
      ((try simp only [size_set]); exact lt_of_lt_of_le (by decide) hs))
      only [rd_set_self, rd_set_ne] <;> rfl
  have f1 : ∀ i, i ≠ fAc → i ≠ bT → i ≠ bN3 →
      rd (semXIR I (.blk [.const fAc 0, .const bT 0, .const bN3 (toWord k)]) s).M i = rd s.M i :=
    fun i a b c => rd_runPrims_of_not_writes (by
      simp only [List.mem_cons, List.mem_nil_iff, or_false]
      rintro p (rfl | rfl | rfl) <;> simp only [Prim.dst] <;> (clear * - a b c; omega)) _
  have hM1 := inv_sem I (P := .blk [.const fAc 0, .const bT 0, .const bN3 (toWord k)]) (s := s)
    (by simp [WF, Prim.dst, fAc, bT, bN3]) hM
  have z1 := size_sem I (.blk [.const fAc 0, .const bT 0, .const bN3 (toWord k)]) s
  generalize semXIR I (.blk [.const fAc 0, .const bT 0, .const bN3 (toWord k)]) s = s1
    at q1 f1 hM1 z1
  have hH1 : ∀ y, 256 ≤ y → rd s1.M y = rd s.M y := fun y hy =>
    f1 y (by simp only [fAc]; (clear * - hy; omega)) (by simp only [bT]; (clear * - hy; omega)) (by simp only [bN3]; (clear * - hy; omega))
  -- the accumulation
  obtain ⟨A1, hM2, A3, A4⟩ := aLoop_sem I s1 hM1 (k := k) (jb := jb) (eb := eb) (cb := cb)
    (cs := cs) (c := c) (x := x) hk (by simp only [regs]; omega) (by simp only [regs]; omega)
    (by simp only [regs]; omega) hjb2 heb2 hcb2 q1.2.2 q1.2.1
    ((f1 _ (by decide) (by decide) (by decide)).trans hCi) q1.1
    (fun t ht => by rw [hH1 _ (by (clear * - hjb; omega)), hJ t ht])
  have nw : ∀ r, r ∈ [bZ, bS, bCi, fLp] → ¬ Writes (aBody jb eb cb cs) r := by
    simp [aBody, addrPs, addr1Ps, Writes, Prim.dst, bnw_mulK, bZ, bS, bCi, fLp, fPr, fAc, bA, bK,
      bJ, fY, fX, bT]
  have R2 : ∀ r, r ∈ [bZ, bS, bCi, fLp] →
      rd (semXIR I (.loopK bC3 bN3 (toWord k) (aBody jb eb cb cs)) s1).M r = rd s.M r :=
    fun r hr => by
      have : r < regs ∧ r ≠ bC3 ∧ r ≠ cTmp ∧ r ≠ fAc ∧ r ≠ bT ∧ r ≠ bN3 := by
        simp only [List.mem_cons, List.mem_nil_iff, or_false] at hr
        rcases hr with rfl | rfl | rfl | rfl <;> decide
      obtain ⟨a, b, c', d, e, f⟩ := this
      rw [A4 r a b c' (nw r hr), f1 r d e f]
  replace A1 : rdK (semXIR I (.loopK bC3 bN3 (toWord k) (aBody jb eb cb cs)) s1).M fAc =
      ∑ t ∈ range k, rdK s.M (cb + cs * x t + c) * rdK s.M (eb + t) := by
    rw [A1]
    exact Finset.sum_congr rfl fun t _ => by
      rw [rdK_congrB (hH1 (cb + cs * x t + c) (by (clear * - hcb hcs2; omega))), rdK_congrB (hH1 (eb + t) (by (clear * - heb; omega)))]
  have z2 := size_sem I (.loopK bC3 bN3 (toWord k) (aBody jb eb cb cs)) s1
  generalize semXIR I (.loopK bC3 bN3 (toWord k) (aBody jb eb cb cs)) s1 = s2
    at A1 hM2 A3 A4 R2 z2
  have H2 : ∀ y, regs ≤ y → rd s2.M y = rd s.M y := fun y hy =>
    (A3 y hy).trans (hH1 y (by simp only [regs] at hy; omega))
  -- the value: `y_c(s)` or `ℓ · acc`
  have st3 : rdK (semXIR I (.ite bZ (yIR cb cs) (mulK fAc fLp fAc)) s2).M fAc =
        (if lp = 0 then rdK s.M (cb + cs * s0 + c) else
          lp * ∑ t ∈ range k, rdK s.M (cb + cs * x t + c) * rdK s.M (eb + t)) ∧
      (∀ r, r ∈ [bS, bCi] →
        rd (semXIR I (.ite bZ (yIR cb cs) (mulK fAc fLp fAc)) s2).M r = rd s.M r) ∧
      (∀ y, regs ≤ y → rd (semXIR I (.ite bZ (yIR cb cs) (mulK fAc fLp fAc)) s2).M y =
        rd s.M y) ∧
      Inv (semXIR I (.ite bZ (yIR cb cs) (mulK fAc fLp fAc)) s2).M := by
    have wy : WF (yIR cb cs) := by simp [yIR, addrPs, WF, Prim.dst, bA, bK, fAc]
    have ly : Lo (yIR cb cs) := by simp [yIR, addrPs, Lo, Prim.dst, bA, bK, fAc, regs]
    have nwy : ∀ r, r ∈ [bS, bCi] → ¬ Writes (yIR cb cs) r := by
      simp [yIR, addrPs, Writes, Prim.dst, bA, bK, fAc, bS, bCi]
    have nwm : ∀ r, r ∈ [bS, bCi] → ¬ Writes (mulK fAc fLp fAc) r := by
      simp [bnw_mulK, fAc, bS, bCi]
    have mem3 : ∀ r, r ∈ [bS, bCi] → r < regs ∧ r ∈ [bZ, bS, bCi, fLp] := by
      simp [bS, bCi, regs]
    rw [semXIR_ite, R2 bZ (by simp), hZ]
    by_cases hl : lp = 0
    · rw [decide_eq_true hl, if_neg bW_ne_zero, if_pos hl]
      refine ⟨?_, fun r hr => ?_, fun y hy => (hframe I _ s2 ly y hy).trans (H2 y hy),
        inv_sem I wy hM2⟩
      · rw [yIR, semXIR_seq, sem_blk_append]
        obtain ⟨c1, f1', hMa⟩ := addr_sem I s2 hM2 (d := bA) (i := bS) (b := cb) (m := cs)
          (x := s0) (by decide) (by decide) (by decide) (by decide) ((R2 bS (by simp)).trans hS)
        obtain ⟨c2, f2', hMb⟩ := bAdd_sem I _ hMa (d := bA) (r := bCi) (x := cb + cs * s0)
          (y := c) (by decide) (by decide) c1
          ((f1' _ (by decide) (by decide)).trans ((R2 bCi (by simp)).trans hCi))
        obtain ⟨l1, -, -⟩ := load_sem I _ hMb (d := fAc) (p := bA) (x := cb + cs * s0 + c)
          (by decide) (by decide) c2 hcs2
        rw [rdK_congrB (l1.trans ((f2' _ (by simp only [bA]; (clear * - hcb; omega))).trans
          ((f1' _ (by simp only [bA]; (clear * - hcb; omega)) (by simp only [bK]; (clear * - hcb; omega))).trans
            (H2 _ (by simp only [regs]; (clear * - hcb; omega))))))]
      · rw [frame I _ s2 wy hM2 r (mem3 r hr).1 (nwy r hr), R2 r (mem3 r hr).2]
    · rw [decide_eq_false hl, bW_false, if_pos rfl, if_neg hl]
      refine ⟨?_, fun r hr => ?_, fun y hy => (hframe I _ s2 (lo_mulK (by decide)) y hy).trans
        (H2 y hy), inv_sem I (wf_mulK _ _ _ (by decide)) hM2⟩
      · rw [mulK_sem hM2 (by decide) (by decide) (by decide) (by decide), A1,
          rdK_congrB (R2 fLp (by simp)), hLp]
      · rw [frame I _ s2 (wf_mulK _ _ _ (by decide)) hM2 r (mem3 r hr).1 (nwm r hr),
          R2 r (mem3 r hr).2]
  obtain ⟨v3, r3, h3, hM3⟩ := st3
  have z3 := size_sem I (.ite bZ (yIR cb cs) (mulK fAc fLp fAc)) s2
  generalize semXIR I (.ite bZ (yIR cb cs) (mulK fAc fLp fAc)) s2 = s3 at v3 r3 h3 hM3 z3
  -- the address `ob + k·c + s`
  obtain ⟨o1, g1, hM4⟩ := addr_sem I s3 hM3 (d := bA) (i := bCi) (b := ob) (m := k) (x := c)
    (by decide) (by decide) (by decide) (by decide) ((r3 bCi (by simp)).trans hCi)
  have z4 := size_sem I (.blk (addrPs bA bCi ob k)) s3
  generalize semXIR I (.blk (addrPs bA bCi ob k)) s3 = s4 at o1 g1 hM4 z4
  obtain ⟨o2, g2, hM5⟩ := bAdd_sem I s4 hM4 (d := bA) (r := bS) (x := ob + k * c) (y := s0)
    (by decide) (by decide) o1 ((g1 _ (by decide) (by decide)).trans ((r3 bS (by simp)).trans hS))
  have z5 := size_sem I (.blk [.op .add bA bA bS]) s4
  generalize semXIR I (.blk [.op .add bA bA bS]) s4 = s5 at o2 g2 hM5 z5
  -- the store
  have hz : ob + k * c + s0 < s5.M.size := by rw [z5, z4, z3, z2, z1]; exact hsz
  obtain ⟨w1, w2, hM6⟩ := store_sem I s5 hM5 (p := bA) (v := fAc) (x := ob + k * c + s0)
    (by decide) (by decide) o2 (by simp only [regs]; (clear * - hob; omega)) hob2 hz
  have K6 : ∀ r, r < 256 → r ≠ cTmp → r ≠ bA → r ≠ bK →
      rd (semXIR I (.store bA fAc) s5).M r = rd s3.M r := fun r hr a b c' => by
    rw [w2 r (by (clear * - hob hr; omega)) a, g2 r b, g1 r b c']
  generalize semXIR I (.store bA fAc) s5 = s6 at w1 w2 hM6 K6
  -- `c += 1`
  obtain ⟨i7, f7, hM7⟩ := bInc_sem I s6 hM6 (r := bCi) (x := c) (by decide) (by decide)
    ((K6 _ (by decide) (by decide) (by decide) (by decide)).trans ((r3 bCi (by simp)).trans hCi))
  refine ⟨?_, i7, fun y hy hy1 => ?_, hM7⟩
  · rw [rdK_congrB ((f7 (ob + k * c + s0) (by simp only [bCi]; (clear * - hob; omega))).trans w1),
      rdK_congrB ((g2 fAc (by decide)).trans (g1 fAc (by decide) (by decide))), v3]
  · simp only [regs] at hy
    rw [f7 _ (by simp only [bCi]; (clear * - hy; omega)), w2 y hy1 (by simp only [cTmp]; (clear * - hy; omega)),
      g2 _ (by simp only [bA]; (clear * - hy; omega)), g1 _ (by simp only [bA]; (clear * - hy; omega)) (by simp only [bK]; (clear * - hy; omega)),
      h3 y (by simp only [regs]; omega)]

/-! ## The coordinates of one target -/

theorem wf_cBody (k jb eb cb cs ob : ℕ) : WF (cBody k jb eb cb cs ob) := by
  simp [cBody, aBody, yIR, addrPs, addr1Ps, WF, Writes, Prim.dst, wfK_mul, bnw_mulK, bA, bK, bJ,
    fY, fX, fPr, fAc, fLp, bT, bN3, bC3, bCi, bS, cTmp, regs]

/-- **The coordinates of one target**: `out[c][s] = (ℓ = 0 ? y_c(s) : ℓ Σ_t y_c(J_t) E[t])` for
`c < C`. -/
theorem cLoop_sem (I : Array Word) (s : St) (hM : Inv s.M)
    {k C jb eb cb cs ob s0 : ℕ} {x : ℕ → ℕ} {lp : BF64}
    (hk : k < 2 ^ 64) (hC : C < 2 ^ 64) (hjb : regs ≤ jb) (heb : regs ≤ eb) (hcb : regs ≤ cb)
    (hob : regs ≤ ob) (hjb2 : jb + k < 2 ^ 64) (heb2 : eb + k < 2 ^ 64)
    (hcb2 : ∀ t < k, ∀ c < C, cb + cs * x t + c < 2 ^ 64)
    (hcs2 : ∀ c < C, cb + cs * s0 + c < 2 ^ 64) (hs0 : s0 < k)
    (hob2 : ob + k * C < 2 ^ 64) (hsz : ob + k * C ≤ s.M.size)
    (hOJ : ob + k * C ≤ jb ∨ jb + k ≤ ob) (hOE : ob + k * C ≤ eb ∨ eb + k ≤ ob)
    (hOY : ∀ c < C, ∀ j, j ∈ (List.range k).map x ∨ j = s0 →
      ob + k * C ≤ cb + cs * j + c ∨ cb + cs * j + c < ob)
    (hN : rd s.M bN2 = toWord C) (hCi : rd s.M bCi = toWord 0)
    (hS : rd s.M bS = toWord s0) (hLp : rdK s.M fLp = lp) (hZ : rd s.M bZ = bW (decide (lp = 0)))
    (hJ : ∀ t < k, rd s.M (jb + t) = toWord (x t)) :
    (∀ c < C, rdK (semXIR I (.loopK bC2 bN2 (toWord C) (cBody k jb eb cb cs ob)) s).M
        (ob + k * c + s0) =
      (if lp = 0 then rdK s.M (cb + cs * s0 + c) else
        lp * ∑ t ∈ range k, rdK s.M (cb + cs * x t + c) * rdK s.M (eb + t))) ∧
    (∀ y, regs ≤ y → (∀ c < C, y ≠ ob + k * c + s0) →
      rd (semXIR I (.loopK bC2 bN2 (toWord C) (cBody k jb eb cb cs ob)) s).M y = rd s.M y) ∧
    (∀ r, r < regs → r ≠ bC2 → r ≠ cTmp → ¬ Writes (cBody k jb eb cb cs ob) r →
      rd (semXIR I (.loopK bC2 bN2 (toWord C) (cBody k jb eb cb cs ob)) s).M r = rd s.M r) ∧
    Inv (semXIR I (.loopK bC2 bN2 (toWord C) (cBody k jb eb cb cs ob)) s).M := by
  simp only [regs] at hjb heb hcb hob
  let V : ℕ → BF64 := fun c => if lp = 0 then rdK s.M (cb + cs * s0 + c) else
    lp * ∑ t ∈ range k, rdK s.M (cb + cs * x t + c) * rdK s.M (eb + t)
  let Q : ℕ → St → Prop := fun j st => Inv st.M ∧ st.M.size = s.M.size ∧ rd st.M bCi = toWord j ∧
    (∀ c < j, rdK st.M (ob + k * c + s0) = V c) ∧
    (∀ y, regs ≤ y → (∀ c < j, y ≠ ob + k * c + s0) → rd st.M y = rd s.M y) ∧
    (∀ r, r < regs → r ≠ bC2 → r ≠ cTmp → ¬ Writes (cBody k jb eb cb cs ob) r → rd st.M r = rd s.M r)
  have ef : ∀ i, i ≠ bC2 → i ≠ cTmp → rd (entryK bC2 bN2 (toWord C) s.M) i = rd s.M i :=
    fun i a b => entryK_frame _ (Ne.symm a) (Ne.symm b)
  have h := loopK_run I (c := bC2) (n := bN2) (K := C) (cBody k jb eb cb cs ob) Q s hM (by decide)
    (by decide) (by decide) hN hC ⟨inv_entryK hM (by decide), size_entryK .., by
        rw [ef _ (by decide) (by decide), hCi],
      fun c hc => absurd hc (Nat.not_lt_zero _),
      fun y hy _ => ef y (by simp only [regs, bC2] at hy ⊢; (clear * - hy; omega))
        (by simp only [regs, cTmp] at hy ⊢; (clear * - hy; omega)),
      fun r _ h1 h2 _ => ef r h1 h2⟩ ?_
  · exact ⟨h.2.2.2.1, h.2.2.2.2.1, h.2.2.2.2.2, h.1⟩
  · rintro j st hj ⟨hM', hz, hCi', hV, hH, hR⟩
    have nwc : ∀ r, r ∈ [bS, fLp, bZ] → ¬ Writes (cBody k jb eb cb cs ob) r := by
      simp [cBody, aBody, yIR, addrPs, addr1Ps, Writes, Prim.dst, bnw_mulK, bA, bK, bJ, fY, fX,
        fPr, fAc, bT, bN3, bC3, bCi, cTmp, bS, fLp, bZ]
    have R : ∀ r, r ∈ [bS, fLp, bZ] → rd st.M r = rd s.M r := fun r hr => by
      have : r < regs ∧ r ≠ bC2 ∧ r ≠ cTmp := by
        simp only [List.mem_cons, List.mem_nil_iff, or_false] at hr
        rcases hr with rfl | rfl | rfl <;> decide
      exact hR r this.1 this.2.1 this.2.2 (nwc r hr)
    have hHy : ∀ y, regs ≤ y → (y < ob ∨ ob + k * C ≤ y) → rd st.M y = rd s.M y :=
      fun y hy hy2 => hH y hy fun c hc => by
        have := out_ltB (k := k) (show c < C by (clear * - hj hc; omega)) hs0
        (clear * - hy2 this; omega)
    have hk2 := out_ltB (k := k) hj hs0
    obtain ⟨b1, b2, b3, hM2⟩ := cBody_sem I st hM' (c := j) (s0 := s0) (x := x) (lp := lp) hk
      (by simp only [regs]; omega) (by simp only [regs]; omega) (by simp only [regs]; omega)
      (by simp only [regs]; omega) hjb2 heb2 (fun t ht => hcb2 t ht j hj) (hcs2 j hj) (by (clear * - hob2 hk2; omega))
      (by rw [hz]; (clear * - hsz hz hk2; omega)) hCi' ((R bS (by simp)).trans hS)
      (by rw [rdK_congrB (R fLp (by simp)), hLp]) ((R bZ (by simp)).trans hZ)
      (fun t ht => by
        rw [hHy _ (by simp only [regs]; (clear * - hjb; omega)) (by rcases hOJ with h | h <;> (clear * - h ht; omega)), hJ t ht])
    refine ⟨inv_decS hM2 (by decide), by rw [size_decS, size_sem, hz],
      by rw [rd_decS (by decide), b2], fun c hc => ?_,
      fun y hy hy2 => ?_, fun r hr h1 h2 h3 => ?_⟩
    · rw [rdK_congrB (rd_decS (by simp only [bC2]; (clear * - hob hob2; omega)) _)]
      rcases Nat.lt_succ_iff_lt_or_eq.1 hc with hc | rfl
      · have hlt := lt_mulB (k := k) hc
        rw [rdK_congrB (b3 _ (by simp only [regs]; (clear * - hob; omega)) (by (clear * - hs0 hlt; omega))), hV c hc]
      · rw [b1]
        have hy' : ∀ j', j' ∈ (List.range k).map x ∨ j' = s0 →
            rdK st.M (cb + cs * j' + c) = rdK s.M (cb + cs * j' + c) := fun j' hj' =>
          rdK_congrB (hHy _ (by simp only [regs]; (clear * - hC hcb hj; omega))
            (by rcases hOY c hj j' hj' with h | h <;> (clear * - h; omega)))
        simp only [V]
        split_ifs
        · exact hy' s0 (.inr rfl)
        · refine congrArg (lp * ·) (Finset.sum_congr rfl fun t ht => ?_)
          have ht' := Finset.mem_range.1 ht
          rw [hy' (x t) (.inl (List.mem_map.2 ⟨t, List.mem_range.2 ht', rfl⟩)),
            rdK_congrB (hHy _ (by simp only [regs]; (clear * - heb; omega)) (by rcases hOE with h | h <;> (clear * - h ht'; omega)))]
    · rw [rd_decS (by simp only [bC2, regs] at hy ⊢; (clear * - hy; omega)), b3 y hy (hy2 j (by (clear * -; omega))),
        hH y hy fun c hc => hy2 c (by (clear * - hc; omega))]
    · rw [rd_decS (Ne.symm h1), frame I _ st (wf_cBody k jb eb cb cs ob) hM' r hr h3,
        hR r hr h1 h2 h3]

end Lvm.X
end
-- ===== end of `LvmXInterp3` =====

/-!
# The barycentric interpolation on the machine (3): one target, the target loop, `baryIR_sem`

* `sBody_sem`: one target `s₀`: `out[c][s₀] = (ℓ = 0 ? y_c(s₀) : ℓ Σ_t y_c(J_t) E[t])`;
* `sLoop_sem`: every target `s < k`;
* **`baryIR_sem`**: the whole program, `out[c][s] = baryValK Jl k s y_c`, hence (`baryValK_eq`)
  **`baryIR_interp`**: `out[c][s] = interpF ptK Jl.toFinset y_c s`; `baryIR_lvm` at lvm's sizes
  (`k = 2^13`, `C = cs = 64`).
-/

namespace Lvm.X

open RecursionFast Finset Lvm.Nb

attribute [local irreducible] entryK storeM runPrims

/-! ## One target -/

/-- **One target `s₀`**: the `C` output cells of `s₀`, `bS := s₀ + 1`; the heap outside the `E`
row and those cells is kept. -/
theorem sBody_sem (I : Array Word) (s : St) (hM : Inv s.M)
    {k C jb wb eb cb cs ob s0 : ℕ} {x : ℕ → ℕ}
    (hk : k < 2 ^ 64) (hC : C < 2 ^ 64) (hs0 : s0 < k)
    (hjb : regs ≤ jb) (hwb : regs ≤ wb) (heb : regs ≤ eb) (hcb : regs ≤ cb) (hob : regs ≤ ob)
    (hjb2 : jb + k < 2 ^ 64) (hwb2 : wb + k < 2 ^ 64) (heb2 : eb + k < 2 ^ 64)
    (hcb2 : ∀ t < k, ∀ c < C, cb + cs * x t + c < 2 ^ 64)
    (hcs2 : ∀ c < C, cb + cs * s0 + c < 2 ^ 64)
    (hob2 : ob + k * C < 2 ^ 64) (hsz : ob + k * C ≤ s.M.size) (hszE : eb + k ≤ s.M.size)
    (hjE : jb + k ≤ eb ∨ eb + k ≤ jb) (hwE : wb + k ≤ eb ∨ eb + k ≤ wb)
    (hOJ : ob + k * C ≤ jb ∨ jb + k ≤ ob) (hOE : ob + k * C ≤ eb ∨ eb + k ≤ ob)
    (hOY : ∀ c < C, ∀ j, j ∈ (List.range k).map x ∨ j = s0 →
      (ob + k * C ≤ cb + cs * j + c ∨ cb + cs * j + c < ob) ∧
      (eb + k ≤ cb + cs * j + c ∨ cb + cs * j + c < eb))
    (hS : rd s.M bS = toWord s0) (hJ : ∀ t < k, rd s.M (jb + t) = toWord (x t)) :
    (∀ c < C, rdK (semXIR I (sBody k C jb wb eb cb cs ob) s).M (ob + k * c + s0) =
      (if ∏ t ∈ range k, (ptK s0 + rdK s.M (jb + t)) = 0 then rdK s.M (cb + cs * s0 + c)
       else (∏ t ∈ range k, (ptK s0 + rdK s.M (jb + t))) *
        ∑ t ∈ range k, rdK s.M (cb + cs * x t + c) *
          (rdK s.M (wb + t) * (ptK s0 + rdK s.M (jb + t))⁻¹))) ∧
    rd (semXIR I (sBody k C jb wb eb cb cs ob) s).M bS = toWord (s0 + 1) ∧
    (∀ y, regs ≤ y → (y < eb ∨ eb + k ≤ y) → (∀ c < C, y ≠ ob + k * c + s0) →
      rd (semXIR I (sBody k C jb wb eb cb cs ob) s).M y = rd s.M y) ∧
    Inv (semXIR I (sBody k C jb wb eb cb cs ob) s).M := by
  have hs := hM.1
  rw [sBody]
  simp only [semXIR_seq]
  -- `fDs := ptK s₀`, `ℓ := 1`, `t := 0`, `bN2 := k`
  have r0 : rd (semXIR I (.blk [.op .or fDs bS bS, .const fLp 1, .const bT 0,
        .const bN2 (toWord k)]) s).M fDs = toWord s0 ∧
      rdK (semXIR I (.blk [.op .or fDs bS bS, .const fLp 1, .const bT 0,
        .const bN2 (toWord k)]) s).M fLp = 1 ∧
      rd (semXIR I (.blk [.op .or fDs bS bS, .const fLp 1, .const bT 0,
        .const bN2 (toWord k)]) s).M bT = toWord 0 ∧
      rd (semXIR I (.blk [.op .or fDs bS bS, .const fLp 1, .const bT 0,
        .const bN2 (toWord k)]) s).M bN2 = toWord k ∧
      rd (semXIR I (.blk [.op .or fDs bS bS, .const fLp 1, .const bT 0,
        .const bN2 (toWord k)]) s).M bS = toWord s0 := by
    rw [sem_blk]
    simp only [runPrims, List.foldl, Prim.run, rdK]
    refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;>
    simp (disch := first | decide |
      ((try simp only [size_set]); exact lt_of_lt_of_le (by decide) hs))
      only [rd_set_self, rd_set_ne, hS, or_self_eval] <;> rfl
  have H0 := hframe I (.blk [.op .or fDs bS bS, .const fLp 1, .const bT 0,
    .const bN2 (toWord k)]) s (by simp [Lo, Prim.dst, regs, fDs, fLp, bT, bN2])
  have hM0 := inv_sem I (P := .blk [.op .or fDs bS bS, .const fLp 1, .const bT 0,
    .const bN2 (toWord k)]) (s := s) (by simp [WF, Prim.dst, fDs, fLp, bT, bN2]) hM
  have z0 := size_sem I (.blk [.op .or fDs bS bS, .const fLp 1, .const bT 0,
    .const bN2 (toWord k)]) s
  generalize semXIR I (.blk [.op .or fDs bS bS, .const fLp 1, .const bT 0,
    .const bN2 (toWord k)]) s = q0 at r0 H0 hM0 z0
  -- the `E` row and `ℓ`
  obtain ⟨e1, e2, e3, e4, hM1⟩ := eLoop_sem I q0 hM0 (k := k) (jb := jb) (wb := wb) (eb := eb)
    (ds := ptK s0) hk hjb hwb heb hjb2 hwb2 heb2 (by rw [z0]; exact hszE) hjE hwE r0.2.2.2.1
    r0.2.2.1 (rdK_toWord r0.1) r0.2.1
  have nw_e : ¬ Writes (eBody jb wb eb) bS := by
    simp [eBody, addr1Ps, Writes, Prim.dst, bnw_mulK, bnw_invK, bA, bK, fX, fDd, fLp, fIv, fEt,
      bT, bS, cTmp]
  have r1 : rd (semXIR I (.loopK bC2 bN2 (toWord k) (eBody jb wb eb)) q0).M bS = toWord s0 :=
    (e4 bS (by decide) (by decide) (by decide) nw_e).trans r0.2.2.2.2
  have z1 := size_sem I (.loopK bC2 bN2 (toWord k) (eBody jb wb eb)) q0
  generalize semXIR I (.loopK bC2 bN2 (toWord k) (eBody jb wb eb)) q0 = q1 at e1 e2 e3 e4 hM1 z1 r1
  have hjt : ∀ t < k, rdK q0.M (jb + t) = rdK s.M (jb + t) := fun t _ =>
    rdK_congrB (H0 (jb + t) (by simp only [regs] at hjb ⊢; (clear * - hjb; omega)))
  have hL1 : rdK q1.M fLp = ∏ t ∈ range k, (ptK s0 + rdK s.M (jb + t)) := by
    rw [e2]
    exact Finset.prod_congr rfl fun t ht => by rw [hjt t (Finset.mem_range.1 ht)]
  -- the flag, `c := 0`, `bN2 := C`
  have hs1 := hM1.1
  have r2 : rd (semXIR I (.blk [.const bK 0, .op .eq bZ fLp bK, .const bCi 0,
        .const bN2 (toWord C)]) q1).M bN2 = toWord C ∧
      rd (semXIR I (.blk [.const bK 0, .op .eq bZ fLp bK, .const bCi 0,
        .const bN2 (toWord C)]) q1).M bCi = toWord 0 ∧
      rd (semXIR I (.blk [.const bK 0, .op .eq bZ fLp bK, .const bCi 0,
        .const bN2 (toWord C)]) q1).M bS = toWord s0 ∧
      rd (semXIR I (.blk [.const bK 0, .op .eq bZ fLp bK, .const bCi 0,
        .const bN2 (toWord C)]) q1).M fLp = rd q1.M fLp := by
    rw [sem_blk]
    simp only [runPrims, List.foldl, Prim.run]
    refine ⟨?_, ?_, ?_, ?_⟩ <;>
    simp (disch := first | decide |
      ((try simp only [size_set]); exact lt_of_lt_of_le (by decide) hs1))
      only [rd_set_self, rd_set_ne, r1] <;> rfl
  have r2z : rd (semXIR I (.blk [.const bK 0, .op .eq bZ fLp bK, .const bCi 0,
      .const bN2 (toWord C)]) q1).M bZ = bW (decide (rdK q1.M fLp = 0)) := by
    rw [sem_blk]
    simp only [runPrims, List.foldl, Prim.run]
    simp (disch := first | decide |
      ((try simp only [size_set]); exact lt_of_lt_of_le (by decide) hs1))
      only [rd_set_self, rd_set_ne]
    rw [eq_bW]
    congr 1
    exact decide_eq_decide.mpr (wK_eq_zero _).symm
  have H2 := hframe I (.blk [.const bK 0, .op .eq bZ fLp bK, .const bCi 0,
    .const bN2 (toWord C)]) q1 (by simp [Lo, Prim.dst, regs, bK, bZ, bCi, bN2])
  have hM2 := inv_sem I (P := .blk [.const bK 0, .op .eq bZ fLp bK, .const bCi 0,
    .const bN2 (toWord C)]) (s := q1) (by simp [WF, Prim.dst, bK, bZ, bCi, bN2]) hM1
  have z2 := size_sem I (.blk [.const bK 0, .op .eq bZ fLp bK, .const bCi 0,
    .const bN2 (toWord C)]) q1
  generalize semXIR I (.blk [.const bK 0, .op .eq bZ fLp bK, .const bCi 0,
    .const bN2 (toWord C)]) q1 = q2 at r2 r2z H2 hM2 z2
  -- the heap of `q2` is `s`'s off the `E` row
  have Hq2 : ∀ y, regs ≤ y → (y < eb ∨ eb + k ≤ y) → rd q2.M y = rd s.M y := fun y hy hy2 =>
    (H2 y hy).trans ((e3 y hy hy2).trans (H0 y hy))
  have hE2 : ∀ t < k, rdK q2.M (eb + t) =
      rdK s.M (wb + t) * (ptK s0 + rdK s.M (jb + t))⁻¹ := fun t ht => by
    rw [rdK_congrB (H2 (eb + t) (by simp only [regs] at heb ⊢; (clear * - heb; omega))), e1 t ht,
      rdK_congrB (H0 (wb + t) (by simp only [regs] at hwb ⊢; (clear * - hwb; omega))), hjt t ht]
  -- the coordinates
  obtain ⟨c1, c2, c3, hM3⟩ := cLoop_sem I q2 hM2 (k := k) (C := C) (jb := jb) (eb := eb) (cb := cb)
    (cs := cs) (ob := ob) (s0 := s0) (x := x) (lp := rdK q1.M fLp) hk hC hjb heb hcb hob hjb2
    heb2 hcb2 hcs2 hs0 hob2 (by rw [z2, z1, z0]; exact hsz) hOJ hOE
    (fun c hc j hj => (hOY c hc j hj).1) r2.1 r2.2.1 r2.2.2.1 (rdK_congrB r2.2.2.2) r2z
    (fun t ht => by
      rw [Hq2 _ (by simp only [regs] at hjb ⊢; (clear * - hjb; omega)) (by rcases hjE with h | h <;> (clear * - ht h; omega)),
        hJ t ht])
  have nw_c : ¬ Writes (cBody k jb eb cb cs ob) bS := by
    simp [cBody, aBody, yIR, addrPs, addr1Ps, Writes, Prim.dst, bnw_mulK, bA, bK, bJ, fY, fX, fPr,
      fAc, bT, bN3, bC3, bCi, cTmp, bS]
  have r3 : rd (semXIR I (.loopK bC2 bN2 (toWord C) (cBody k jb eb cb cs ob)) q2).M bS =
      toWord s0 :=
    (c3 bS (by decide) (by decide) (by decide) nw_c).trans r2.2.2.1
  generalize semXIR I (.loopK bC2 bN2 (toWord C) (cBody k jb eb cb cs ob)) q2 = q3
    at c1 c2 c3 hM3 r3
  -- `s₀ += 1`
  obtain ⟨i1, i2, hM4⟩ := bInc_sem I q3 hM3 (r := bS) (x := s0) (by decide) (by decide) r3
  refine ⟨fun c hc => ?_, i1, fun y hy hy2 hy3 => ?_, hM4⟩
  · rw [rdK_congrB (i2 (ob + k * c + s0) (by simp only [regs] at hob; simp only [bS]; (clear * - hob; omega))),
      c1 c hc, hL1]
    have hy' : ∀ j, j ∈ (List.range k).map x ∨ j = s0 →
        rdK q2.M (cb + cs * j + c) = rdK s.M (cb + cs * j + c) := fun j hj =>
      rdK_congrB (Hq2 _ (by simp only [regs] at hcb ⊢; (clear * - hC hcb hc; omega))
        (by rcases (hOY c hc j hj).2 with h | h <;> (clear * - h; omega)))
    split_ifs
    · exact hy' s0 (.inr rfl)
    · refine congrArg (_ * ·) (Finset.sum_congr rfl fun t ht => ?_)
      have ht' := Finset.mem_range.1 ht
      rw [hy' (x t) (.inl (List.mem_map.2 ⟨t, List.mem_range.2 ht', rfl⟩)), hE2 t ht']
  · rw [i2 y (by simp only [regs] at hy; simp only [bS]; (clear * - hy; omega)), c2 y hy hy3, Hq2 y hy hy2]

/-! ## The layout and the target loop -/

/-! ## The whole program -/

end Lvm.X
