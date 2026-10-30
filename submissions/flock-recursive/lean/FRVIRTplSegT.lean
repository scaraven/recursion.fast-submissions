-- G6: this module also holds the former modules `FRVIRTplSegR` (one section each, in import order).
import FRNodeRows4RepCFRs
import FRVIRTplTab
import FRSegTarget4
import FRNodeRows4Ext

section G6_FRVIRTplSegR

-- New for `flock-recursive` (SEG-R §4.4, stage SEG-R1): the segment program's `rsWeight` replay template.

/-!
# The segment's `rsWeight` template (three `F`-point claims, `β = 1`)

At prototype 1 every `rsWeight` claim point is an `F`-point and `β` is unread (`act` false at every
kind), so its value is `Σ_j κ^j Σ_{k<128} c_k(r″) Π_l (1 + a_{j,l}^{2^k} + ρ_l)` (SEG-R §4.4,
SEG-R0 §1.1; the kind factor of claim 2 collapses at `β = 1`). **`rsSegT cst`** computes it over
133 canonical inputs, one instance at 25 coordinates (a narrower kind's missing coordinates are `0`:
the factor `1 + 0 + 0` is `1`):

| inputs | |
|---|---|
| `0 … 6` | `r″` |
| `7` | `κ` |
| `8 + 2l`, `9 + 2l` (`l < 25`) | `ρ_l` (`f₀`, `f₁`) |
| `58 + 25 j + l` | claim `j`'s coordinate `l` (its `f₀`; the wrapper forces `f₁ = 0`) |

Gates: `phiG` (247), a squaring chain in `F` per non-constant claim coordinate (127 each; a
constant hinted by the wrapper is folded), per claim and stage the product of the 25 factors (24
`mulK`) times `c_k` (`smulK`), and `κ²`, `κ S₁`, `κ² S₂`. **`ok_rsSegT`**: the outputs are
`rsSegV` of the inputs' values.
-/

namespace FR
namespace Tpl
open Circ

variable {e : Env}

/-- Canonical input `p`: its hinted constant, else its wire. -/
def inC (cst : List (Option F)) (p : ℕ) : LinT :=
  match cst.getD p none with
  | some c => C c
  | none => I p

theorem inC_ev (h1 : e.one = 1) {cst : List (Option F)} (hc : ∀ p c, cst.getD p none = some c → e.inp p = c)
    (p : ℕ) : (inC cst p).ev e = e.inp p := by
  unfold inC
  split
  · rename_i c h; rw [ev_C, h1, mul_one, hc p c h]
  · exact ev_I e p

/-- **A claim coordinate's squaring chain** (`x^(2^k)`, `k < 128`), folded for a constant. -/
def chainC (cst : List (Option F)) (p : ℕ) : GM (List LinT) :=
  match cst.getD p none with
  | some c => GM.ret ((List.range 128).map fun k => C (sqIter k c))
  | none => sqChainF 127 (I p)

theorem ok_chainC (h1 : e.one = 1) {cst : List (Option F)} (hc : ∀ p c, cst.getD p none = some c → e.inp p = c)
    (p : ℕ) : GM.Ok e (chainC cst p) fun ys => ys.map (LinT.ev e) = (List.range 128).map fun k => sqIter k (e.inp p) := by
  unfold chainC
  split
  · rename_i c h
    exact GM.ok_ret (by simp [ev_C, h1, hc p c h])
  · exact GM.ok_mono (ok_sqChainF 127 (I p)) fun ys h => by simpa using h

/-- The factor `1 + a + ρ` (characteristic two: `eq(a, ρ)`), `a` an `F` form. -/
def rsFac (a : LinT) (ρ : KF) : KF := (C 1 ++ a ++ ρ.1, ρ.2)

theorem evK_rsFac (h1 : e.one = 1) (a : LinT) (ρ : KF) :
    evK e (rsFac a ρ) = 1 + K.ofF (a.ev e) + evK e ρ := by
  apply K_ext'
  · rw [K_add_f₀, K_add_f₀]; simp only [evK, rsFac, ev_append, ev_C, h1, mul_one]; rfl
  · rw [K_add_f₁, K_add_f₁]; simp only [evK, rsFac]; show _ = 0 + 0 + _; rw [zero_add, zero_add]

/-- **One claim's stage sum** `Σ_{k<128} c_k Π_{l<25} (1 + a_l^{2^k} + ρ_l)` (the chains `chs`). -/
def rsStage (cs : List LinT) (chs : List (List LinT)) (ρ : List KF) : GM KF :=
  GM.foldL (fun acc k => (prodK ((List.range 25).map fun l => rsFac ((chs.getD l []).getD k []) (ρ.getD l zeroK))).bind
    fun w => (smulK (cs.getD k []) w).map (addK acc)) zeroK (List.range 128)

/-- The `ρ` inputs as `K` pairs. -/
def rhoIn (cst : List (Option F)) : List KF := (List.range 25).map fun l => (inC cst (8 + 2 * l), inC cst (9 + 2 * l))

/-- **The template.** -/
def rsSegT (cst : List (Option F)) : GM (List LinT × List RowT) :=
  (phiG ((List.range 7).map (inC cst))).bind fun c =>
  (GM.mapL (fun j => GM.mapL (fun l => chainC cst (58 + 25 * j + l)) (List.range 25)) (List.range 3)).bind fun ch =>
  (GM.mapL (fun j => rsStage c (ch.getD j []) (rhoIn cst)) (List.range 3)).bind fun S =>
  (mulF (inC cst 7) (inC cst 7)).bind fun κ2 =>
  (smulK (inC cst 7) (S.getD 1 zeroK)).bind fun t1 =>
  (smulK κ2 (S.getD 2 zeroK)).map fun t2 =>
  ([(addK (addK (S.getD 0 zeroK) t1) t2).1, (addK (addK (S.getD 0 zeroK) t1) t2).2], [])

/-! ## The value -/

/-- **The value**: `r″`'s 7 values, `κ`, `ρ` (25), the claims' coordinates `a j l`. -/
noncomputable def rsSegV (rv : List F) (κ : F) (ρ : List K) (a : ℕ → ℕ → F) : K :=
  ∑ j ∈ Finset.range 3, K.ofF κ ^ j * ∑ k ∈ Finset.range 128,
    K.ofF ((phiTable rv).toList.getD k 0) *
      ((List.range 25).map fun l => 1 + K.ofF (sqIter k (a j l)) + ρ.getD l 0).prod

theorem rsSegV_eq3 (rv : List F) (κ : F) (ρ : List K) (a : ℕ → ℕ → F) :
    rsSegV rv κ ρ a = (∑ k ∈ Finset.range 128, K.ofF ((phiTable rv).toList.getD k 0) *
        ((List.range 25).map fun l => 1 + K.ofF (sqIter k (a 0 l)) + ρ.getD l 0).prod) +
      K.ofF κ * (∑ k ∈ Finset.range 128, K.ofF ((phiTable rv).toList.getD k 0) *
        ((List.range 25).map fun l => 1 + K.ofF (sqIter k (a 1 l)) + ρ.getD l 0).prod) +
      K.ofF (κ * κ) * (∑ k ∈ Finset.range 128, K.ofF ((phiTable rv).toList.getD k 0) *
        ((List.range 25).map fun l => 1 + K.ofF (sqIter k (a 2 l)) + ρ.getD l 0).prod) := by
  have hm : K.ofF (κ * κ) = K.ofF κ * K.ofF κ := map_mul K.ofFRingHom κ κ
  unfold rsSegV
  rw [Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_one, hm]
  simp only [pow_zero, one_mul, pow_one, pow_two]

theorem foldl_add_range {M : Type*} [AddCommMonoid M] (g : ℕ → M) :
    ∀ n (c : M), (List.range n).foldl (fun acc k => acc + g k) c = c + ∑ k ∈ Finset.range n, g k
  | 0, c => by simp
  | n + 1, c => by
    rw [List.range_succ, List.foldl_append, foldl_add_range g n c, Finset.sum_range_succ]
    simp [add_assoc]

theorem ok_rsStage (h1 : e.one = 1) (cs : List LinT) (chs : List (List LinT)) (ρ : List KF)
    (cv : ℕ → F) (hcv : ∀ k < 128, (cs.getD k []).ev e = cv k) (av : ℕ → ℕ → F)
    (hav : ∀ l < 25, ∀ k < 128, ((chs.getD l []).getD k []).ev e = av l k) (ρv : List K)
    (hρ : ∀ l < 25, evK e (ρ.getD l zeroK) = ρv.getD l 0) :
    GM.Ok e (rsStage cs chs ρ) fun s => evK e s = ∑ k ∈ Finset.range 128,
      K.ofF (cv k) * ((List.range 25).map fun l => 1 + K.ofF (av l k) + ρv.getD l 0).prod := by
  unfold rsStage
  have := GM.ok_foldL (e := e) (f := fun acc k => (prodK ((List.range 25).map fun l =>
      rsFac ((chs.getD l []).getD k []) (ρ.getD l zeroK))).bind fun w => (smulK (cs.getD k []) w).map (addK acc))
    (E := evK e) (g := fun acc k => acc + K.ofF (cv k) *
      ((List.range 25).map fun l => 1 + K.ofF (av l k) + ρv.getD l 0).prod) (List.range 128) zeroK
    fun b k hk => GM.ok_bind (ok_prodK h1 _) fun w hw => GM.ok_map (ok_smulK _ w) fun t ht => by
      have hk' := List.mem_range.1 hk
      rw [evK_addK, ht, hw, hcv k hk', List.map_map]
      congr 2
      refine congrArg List.prod (List.map_congr_left fun l hl => ?_)
      have hl' := List.mem_range.1 hl
      simp only [Function.comp_apply, evK_rsFac h1, hav l hl' k hk', hρ l hl']
  refine GM.ok_mono this fun s hs => ?_
  rw [hs, foldl_add_range, evK_zeroK, zero_add]

theorem getD_mapL_len {α β : Type} (f : α → GM β) (l : List α) (k : ℕ) : ((GM.mapL f l) k).2.length = l.length := by
  induction l generalizing k with
  | nil => rfl
  | cons a l ih => simp [GM.mapL, GM.bind, GM.map, ih]

theorem getD_map' {α β : Type} (f : α → β) (l : List α) (n : ℕ) (d : α) :
    (l.map f).getD n (f d) = f (l.getD n d) := by
  simp only [List.getD_eq_getElem?_getD, List.getElem?_map]; cases l[n]? <;> rfl

theorem getD_range_map {α : Type} (g : ℕ → α) {n i : ℕ} (hi : i < n) (d : α) :
    ((List.range n).map g).getD i d = g i := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range hi]

/-- **The template computes `rsSegV`** of its inputs' values (the hinted constants agreeing). -/
theorem ok_rsSegT (h1 : e.one = 1) {cst : List (Option F)} (hc : ∀ p c, cst.getD p none = some c → e.inp p = c) :
    GM.Ok e (rsSegT cst) fun o => o.1.map (LinT.ev e) = encK (rsSegV ((List.range 7).map e.inp) (e.inp 7)
      ((List.range 25).map fun l => (⟨e.inp (8 + 2 * l), e.inp (9 + 2 * l)⟩ : K))
      fun j l => e.inp (58 + 25 * j + l)) := by
  have hin := inC_ev h1 hc
  unfold rsSegT
  refine GM.ok_bind (ok_phiG h1 _) fun c hcv => ?_
  refine GM.ok_bind (GM.ok_mapL (E := fun xs : List (List LinT) => xs.map (List.map (LinT.ev e)))
    (v := fun j => (List.range 25).map fun l => (List.range 128).map fun k => sqIter k (e.inp (58 + 25 * j + l)))
    (List.range 3) fun j _ => GM.ok_mapL (List.range 25) fun l _ => ok_chainC h1 hc _) fun ch hch => ?_
  have hr7 : (List.range 7).map (LinT.ev e ∘ inC cst) = (List.range 7).map e.inp :=
    List.map_congr_left fun p _ => hin p
  have hcv' : ∀ k < 128, (c.getD k []).ev e = (phiTable ((List.range 7).map e.inp)).toList.getD k 0 := by
    intro k _
    rw [← getD_map' (LinT.ev e) _ _ [], ev_nil, hcv, List.map_map, hr7]
  have hch' : ∀ j < 3, ∀ l < 25, ∀ k < 128, (((ch.getD j []).getD l []).getD k []).ev e =
      sqIter k (e.inp (58 + 25 * j + l)) := by
    intro j hj l hl k hk
    have e1 : (((ch.getD j []).getD l []).getD k []).ev e =
        (((ch.map (List.map (List.map (LinT.ev e)))).getD j []).getD l []).getD k 0 := by
      rw [← getD_map' (LinT.ev e) _ _ [], ev_nil, ← getD_map' (List.map (LinT.ev e)) _ _ [], List.map_nil,
        ← getD_map' (List.map (List.map (LinT.ev e))) _ _ [], List.map_nil]
    rw [e1, hch, getD_range_map _ hj, getD_range_map _ hl, getD_range_map _ hk]
  refine GM.ok_bind (GM.ok_mapL (E := evK e) (v := fun j => ∑ k ∈ Finset.range 128,
      K.ofF ((phiTable ((List.range 7).map e.inp)).toList.getD k 0) *
        ((List.range 25).map fun l => 1 + K.ofF (sqIter k (e.inp (58 + 25 * j + l))) +
          ((List.range 25).map fun l => (⟨e.inp (8 + 2 * l), e.inp (9 + 2 * l)⟩ : K)).getD l 0).prod)
    (List.range 3) fun j hj => ok_rsStage h1 _ _ _ _ hcv' _ (fun l hl k hk => hch' j (List.mem_range.1 hj) l hl k hk) _
      fun l hl => by
        rw [rhoIn, getD_range_map _ hl, getD_range_map _ hl]
        exact K_ext' (by simp [evK, hin]) (by simp [evK, hin])) fun S hS => ?_
  have hS' : ∀ j < 3, evK e (S.getD j zeroK) = ∑ k ∈ Finset.range 128,
      K.ofF ((phiTable ((List.range 7).map e.inp)).toList.getD k 0) *
        ((List.range 25).map fun l => 1 + K.ofF (sqIter k (e.inp (58 + 25 * j + l))) +
          ((List.range 25).map fun l => (⟨e.inp (8 + 2 * l), e.inp (9 + 2 * l)⟩ : K)).getD l 0).prod := by
    intro j hj
    rw [← getD_map' (evK e) _ _ zeroK, hS, getD_range_map _ hj]
  refine GM.ok_bind (ok_mulF _ _) fun κ2 hκ2 => GM.ok_bind (ok_smulK _ _) fun t1 ht1 =>
    GM.ok_map (ok_smulK _ _) fun t2 ht2 => ?_
  have hv : evK e (addK (addK (S.getD 0 zeroK) t1) t2) = rsSegV ((List.range 7).map e.inp) (e.inp 7)
      ((List.range 25).map fun l => (⟨e.inp (8 + 2 * l), e.inp (9 + 2 * l)⟩ : K))
      (fun j l => e.inp (58 + 25 * j + l)) := by
    rw [evK_addK, evK_addK, ht1, ht2, hκ2, hS' 0 (by norm_num), hS' 1 (by norm_num), hS' 2 (by norm_num), hin,
      rsSegV_eq3]
  rw [← hv]; rfl

end Tpl
end FR

end G6_FRVIRTplSegR

section G6_FRVIRTplSegT

-- New for `flock-recursive` (SEG-R §4.2–4.3, stage SEG-R1b): the segment program's `targetS` and
-- `shiftTarget` replay templates.

/-!
# The segment's `targetS` and `shiftTarget` templates

**`tsSegT`** (`targetS`, `targetSSegI r` for `r : AF 37`: `r₀`, the block coordinates `1 … 18`, `L`'s
bits `19 … 36`). `targetSLeafI r` reads `r` only through `r₀` and is affine in it (`leaf_affine`),
so the outputs are `α_σ R + β_σ (r₀ R)` with the constants `α = targetSLeafI [0]`,
`β = targetSLeafI [1] − α`. In characteristic two `eq(b, x) = 1 + b + x`, so on Boolean bits the
range factor `Σ_{t ≤ L} eq(r_blk, t)` is `P + Q`, `P = Π_l (1 + b_l + x_l)` (`t = L`) and
`Q = Σ_l b_l (1 + x_l) Π_{j>l} (1 + b_j + x_j)` (`t < L`, first differing bit `l`): `rangeG`, 3 gates a
coordinate, then one gate `r₀ R`. Forcing rows `b_l · b_l = b_l` (18). **`ok_tsSegT`**.

**`stSegT`** (`shiftTarget`, `shiftTargetI κs τ θ bnd` for `τ : AF 18`, `θ : AF 10`, `bnd : AF 22`,
`κs`): the two digests' 256 bits each as `pad` locals with forcing rows `bit · bit = bit` and
`one · Σ_b E_b bit_b = half` (`W4.bitF_sumO`: the bits are the halves' bits, `bits_dig`); the eq
table over `θ₀ … θ₇` (255 gates); the digest sums `Σ_σ bit_σ E[σ]` (512 gates; `σ < 256` clears
bits 8 and 9, so `eq(θ, σ) = E₈[σ] (1 − θ₈)(1 − θ₉)`, `eqAtR_ten`); `eq(τ, L) = Π_l (1 + τ_l + L_l)`
(18 gates); `(1 − θ₈)(1 − θ₉)` and the final three gates. **`ok_stSegT`**.
-/

namespace FR
namespace Tpl
open Circ Impl Finset

variable {e : Env}

/-! ## Characteristic two, Booleans -/

theorem one_add_eq (x : F) : 1 + x = 1 - x := by rw [sub_eq_add_neg, CharTwo.neg_eq]

theorem bool_of_row {x : F} (h : x * x = x) : x = 0 ∨ x = 1 := by
  have h' : x * (x - 1) = 0 := by rw [mul_sub, h, mul_one, sub_self]
  rcases mul_eq_zero.1 h' with h0 | h0
  · exact .inl h0
  · exact .inr (sub_eq_zero.1 h0)

/-! ## `targetS`: the leaf part is affine in `r₀` -/

theorem zLo_eq (r : Array F) : zLo r = zLo #[r.getD 0 0] := by
  funext l; unfold zLo; split_ifs <;> simp

theorem leafI_eq (r : Array F) : targetSLeafI r = targetSLeafI #[r.getD 0 0] := by
  unfold targetSLeafI; rw [zLo_eq r]

/-- An `eq` table entry over `zLo [x]`: a constant times the last coordinate's factor. -/
theorem eqZ_getD (x : F) {hi : ℕ} (hh : hi < 256) :
    (eqTable (List.ofFn (zLo #[x]))).getD hi 0 =
      (∏ l : Fin 7, if hi.testBit l then pinnedRho l else 1 - pinnedRho l) *
        (if hi.testBit 7 then x else 1 - x) := by
  rw [eqTable_ofFn_getD _ (show hi < 2 ^ 8 by norm_num [hh]), eqAtR, Fin.prod_univ_castSucc]
  refine congrArg₂ (· * ·) (Finset.prod_congr rfl fun l _ => ?_) ?_
  · simp only [zLo, Fin.coe_castSucc, l.isLt, dite_true]
  · simp [zLo]

theorem affine_getD (x : F) {hi : ℕ} (hh : hi < 256) :
    (eqTable (List.ofFn (zLo #[x]))).getD hi 0 = (eqTable (List.ofFn (zLo #[0]))).getD hi 0 +
      x * ((eqTable (List.ofFn (zLo #[1]))).getD hi 0 - (eqTable (List.ofFn (zLo #[0]))).getD hi 0) := by
  rw [eqZ_getD x hh, eqZ_getD 0 hh, eqZ_getD 1 hh]
  split_ifs <;> ring

/-- **`targetSLeafI` is affine in `r₀`.** -/
theorem leaf_affine (r : Array F) (σ : ℕ) :
    (targetSLeafI r).getD σ 0 = (targetSLeafI #[0]).getD σ 0 +
      r.getD 0 0 * ((targetSLeafI #[1]).getD σ 0 - (targetSLeafI #[0]).getD σ 0) := by
  rw [leafI_eq r]
  generalize r.getD 0 0 = x
  by_cases hσ : σ < 64
  · have hg : ∀ y : F, (targetSLeafI #[y]).getD σ 0 =
        ∑ hi ∈ range 256, chainTab.getD (σ + 64 * hi) 0 * (eqTable (List.ofFn (zLo #[y]))).getD hi 0 :=
      fun y => by simp only [targetSLeafI, Array.getD_eq_getD_getElem?, Array.getElem?_ofFn, hσ, dite_true,
        Option.getD_some, sumTo_eq]
    rw [hg, hg, hg, ← Finset.sum_sub_distrib, Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun hi hm => ?_
    rw [affine_getD x (Finset.mem_range.1 hm)]
    ring
  · simp [targetSLeafI, Array.getD_eq_getD_getElem?, hσ]

/-! ## `targetS`: the range factor -/

/-- **The range factor's recursion** over coordinate pairs `(b_l, x_l)`, the low one first: `(P, Q)`
with `P = Π_l (1 + b_l + x_l)`, `Q = Σ_l b_l (1 + x_l) Π_{j>l} (1 + b_j + x_j)` (3 gates a pair). -/
def rangeG : List (LinT × LinT) → GM (LinT × LinT)
  | [] => GM.ret (C 1, [])
  | p :: r => (rangeG r).bind fun pq =>
      (mulF (C 1 ++ p.1 ++ p.2) pq.1).bind fun P =>
      (mulF p.1 (C 1 ++ p.2)).bind fun q =>
      (mulF q pq.1).map fun t => (P, pq.2 ++ t)

/-- A bit list's number (the first entry the low bit; an entry is set iff it is `1`). -/
def rgVal : List F → ℕ
  | [] => 0
  | b :: r => (if b = 1 then 1 else 0) + 2 * rgVal r

theorem rgVal_lt : ∀ l : List F, rgVal l < 2 ^ l.length
  | [] => by simp [rgVal]
  | b :: r => by
    have := rgVal_lt r
    simp only [rgVal, List.length_cons, pow_succ]
    split_ifs <;> omega

/-- The `eq` factors at the points `xs` (`n` coordinates; `prefixP`'s form). -/
def rgEqF (xs : List F) (n : ℕ) : Fin n → Bool → F := fun l b => if b then xs.getD l 0 else 1 - xs.getD l 0

theorem rgEqF_succ (x : F) (xs : List F) (n : ℕ) :
    (fun l : Fin n => rgEqF (x :: xs) (n + 1) l.succ) = rgEqF xs n := by
  funext l b; simp [rgEqF]

/-- **One coordinate of the range recursion** (the low bit `b`, Boolean): `prodAt`'s and `prefixP`'s
low-bit steps. -/
theorem range_step (x b : F) (xs : List F) (n c : ℕ) (hc : c < 2 ^ n) (hb : b = 0 ∨ b = 1) :
    (1 + b + x) * prodAt (rgEqF xs n) c = prodAt (rgEqF (x :: xs) (n + 1)) ((if b = 1 then 1 else 0) + 2 * c) ∧
    prefixP n (rgEqF xs n) c + b * (1 + x) * prodAt (rgEqF xs n) c =
      prefixP (n + 1) (rgEqF (x :: xs) (n + 1)) ((if b = 1 then 1 else 0) + 2 * c) := by
  have hs : ∀ l : Fin n, rgEqF (x :: xs) (n + 1) l.succ = rgEqF xs n l := fun l => congrFun (rgEqF_succ x xs n) l
  have hP : prodAt (rgEqF xs n) c = ∏ l : Fin n, rgEqF xs n l (c.testBit l) := by
    unfold prodAt; rw [if_pos hc]
  rcases hb with rfl | rfl
  · have h01 : ¬ (0 : F) = 1 := zero_ne_one
    simp only [h01, ite_false, zero_add]
    refine ⟨?_, ?_⟩
    · rw [hP]
      unfold prodAt
      rw [if_pos (by rw [pow_succ]; omega), Fin.prod_univ_succ]
      congr 1
      · simp [rgEqF, Nat.testBit_zero, one_add_eq]
      · refine Finset.prod_congr rfl fun l _ => ?_
        rw [hs l, Fin.val_succ, Nat.testBit_succ, show 2 * c / 2 = c by omega]
    · rw [zero_mul, zero_mul, add_zero]
      conv_rhs => rw [prefixP]
      rw [show 2 * c / 2 = c by omega, if_neg (by omega), add_zero,
        show (fun l : Fin n => rgEqF (x :: xs) (n + 1) l.succ) = rgEqF xs n from rgEqF_succ x xs n]
      simp [rgEqF]
  · simp only [ite_true]
    refine ⟨?_, ?_⟩
    · rw [hP]
      unfold prodAt
      rw [if_pos (by rw [pow_succ]; omega), Fin.prod_univ_succ]
      congr 1
      · simp [rgEqF, Nat.testBit_zero, show (1 + 2 * c) % 2 = 1 by omega, CharTwo.add_self_eq_zero]
      · refine Finset.prod_congr rfl fun l _ => ?_
        rw [hs l, Fin.val_succ, Nat.testBit_succ, show (1 + 2 * c) / 2 = c by omega]
    · conv_rhs => rw [prefixP]
      rw [show (1 + 2 * c) / 2 = c by omega, if_pos (by omega),
        show (fun l : Fin n => rgEqF (x :: xs) (n + 1) l.succ) = rgEqF xs n from rgEqF_succ x xs n]
      simp only [rgEqF, Fin.val_zero, List.getD_cons_zero, Bool.false_eq_true, ite_false, ite_true, sub_add_cancel,
        one_mul, one_add_eq]

theorem ok_rangeG (h1 : e.one = 1) : ∀ (bx : List (LinT × LinT)), (∀ p ∈ bx, p.1.ev e = 0 ∨ p.1.ev e = 1) →
    GM.Ok e (rangeG bx) fun pq =>
      pq.1.ev e = prodAt (rgEqF (bx.map fun p => p.2.ev e) bx.length) (rgVal (bx.map fun p => p.1.ev e)) ∧
      pq.2.ev e = prefixP bx.length (rgEqF (bx.map fun p => p.2.ev e) bx.length) (rgVal (bx.map fun p => p.1.ev e))
  | [], _ => GM.ok_ret ⟨by simp [prodAt, rgVal, h1], by simp [prefixP, rgVal]⟩
  | p :: r, hb => by
    have hb0 := hb p (List.mem_cons_self ..)
    refine GM.ok_bind (ok_rangeG h1 r fun q hq => hb q (List.mem_cons_of_mem _ hq)) fun pq ⟨hP, hQ⟩ => ?_
    refine GM.ok_bind (ok_mulF _ _) fun P hP' => GM.ok_bind (ok_mulF _ _) fun q hq =>
      GM.ok_map (ok_mulF _ _) fun t ht => ?_
    have hc := rgVal_lt (r.map fun p => p.1.ev e)
    rw [List.length_map] at hc
    obtain ⟨g1, g2⟩ := range_step (p.2.ev e) (p.1.ev e) (r.map fun p => p.2.ev e) r.length _ hc hb0
    simp only [ev_append, ev_C, h1, mul_one] at hP' hq ht
    simp only [List.map_cons, List.length_cons, rgVal, ev_append]
    refine ⟨?_, ?_⟩
    · rw [hP', hP, g1]
    · rw [ht, hq, hP, hQ, ← g2]

/-- The bit number of entries `o … o + n − 1`. -/
theorem sum_bits_rgVal (a : ℕ → F) : ∀ n o : ℕ,
    ∑ l ∈ range n, (if a (o + l) = 1 then 2 ^ l else 0) = rgVal ((List.range n).map fun l => a (o + l))
  | 0, _ => by simp [rgVal]
  | n + 1, o => by
    rw [Finset.sum_range_succ', List.range_succ_eq_map, List.map_cons, List.map_map, rgVal]
    have ih := sum_bits_rgVal a n (o + 1)
    have hf : (fun l => a (o + l)) ∘ Nat.succ = fun l => a (o + 1 + l) := funext fun l => by
      simp only [Function.comp_apply]; congr 1; omega
    rw [hf, ← ih, add_zero, add_comm]
    congr 1
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun l _ => ?_
    rw [show o + (l + 1) = o + 1 + l by omega]
    split_ifs <;> ring

/-- **`prefixP` one further**: the prefix through `c` is the prefix below `c` plus `c`'s term. -/
theorem prefixP_succ (n : ℕ) (E : Fin n → Bool → F) (c : ℕ) : prefixP n E (c + 1) = prefixP n E c + prodAt E c := by
  rw [prefixP_eq, prefixP_eq, prodAt]
  rw [show (∑ x : Fin (2 ^ n), if x.val < c + 1 then ∏ l : Fin n, E l (x.val.testBit l) else 0) =
      ∑ x : Fin (2 ^ n), ((if x.val < c then ∏ l : Fin n, E l (x.val.testBit l) else 0) +
        (if x.val = c then ∏ l : Fin n, E l (x.val.testBit l) else 0)) from
      Finset.sum_congr rfl fun x _ => by split_ifs <;> first | omega | simp, Finset.sum_add_distrib]
  congr 1
  split_ifs with hc
  · rw [Finset.sum_eq_single (⟨c, hc⟩ : Fin (2 ^ n)) (fun b _ hb => if_neg fun h => hb (Fin.ext h)) (by simp)]
    simp
  · exact Finset.sum_eq_zero fun x _ => if_neg fun (h : x.val = c) => hc (h ▸ x.isLt)

/-! ## `targetS`: the template -/

/-- `targetS`'s coordinate pairs `(L_l, r_blk,l)`: inputs `19 + l`, `1 + l`. -/
def tsBX : List (LinT × LinT) := (List.range 18).map fun l => (I (19 + l), I (1 + l))

/-- The leaf target at `r₀ = 0`, and at `r₀ = 1` (constants of the template). -/
def tsA0 : Array F := targetSLeafI #[0]
def tsA1 : Array F := targetSLeafI #[1]

/-- **The segment's `targetS` template** (the hints are not read). -/
def tsSegT (_ : List (Option F)) : GM (List LinT × List RowT) :=
  (rangeG tsBX).bind fun pq =>
  (mulF (I 0) (pq.1 ++ pq.2)).map fun rR =>
  ((List.range 64).map fun σ => sc (tsA0.getD σ 0) (pq.1 ++ pq.2) ++ sc (tsA1.getD σ 0 - tsA0.getD σ 0) rR,
   (List.range 18).map fun l => ⟨I (19 + l), I (19 + l), I (19 + l)⟩)

/-- **The `targetS` template computes `targetSSegI`** of the inputs (`r`'s entries below 37), its
forcing rows holding. -/
theorem ok_tsSegT (h1 : e.one = 1) (cst : List (Option F)) (r : Array F) (hr : ∀ p < 37, e.inp p = r.getD p 0) :
    GM.Ok e (tsSegT cst) fun o => (∀ q ∈ o.2, q.Holds e) → o.1.map (LinT.ev e) = (Rev4.targetSSegI r).toList := by
  unfold tsSegT
  have hl : tsBX.length = 18 := by simp [tsBX]
  have hbit : ∀ p ∈ tsBX, p.1.ev e = 0 ∨ p.1.ev e = 1 → True := fun _ _ _ => trivial
  refine GM.ok_bind (P := fun pq => (∀ p ∈ tsBX, p.1.ev e = 0 ∨ p.1.ev e = 1) →
      pq.1.ev e = prodAt (rgEqF (tsBX.map fun p => p.2.ev e) tsBX.length) (rgVal (tsBX.map fun p => p.1.ev e)) ∧
      pq.2.ev e = prefixP tsBX.length (rgEqF (tsBX.map fun p => p.2.ev e) tsBX.length) (rgVal (tsBX.map fun p => p.1.ev e)))
    (fun k hk hb => ok_rangeG h1 tsBX hb k hk) fun pq hpq => GM.ok_map (ok_mulF _ _) fun rR hrR hrows => ?_
  clear hbit
  -- the bits
  have hB : ∀ l < 18, e.inp (19 + l) = 0 ∨ e.inp (19 + l) = 1 := fun l hl' => by
    have := hrows ⟨I (19 + l), I (19 + l), I (19 + l)⟩ (List.mem_map.2 ⟨l, List.mem_range.2 hl', rfl⟩)
    simp only [RowT.Holds, ev_I] at this
    exact bool_of_row this
  have hb : ∀ p ∈ tsBX, p.1.ev e = 0 ∨ p.1.ev e = 1 := fun p hp => by
    obtain ⟨l, hl', rfl⟩ := List.mem_map.1 hp
    simpa using hB l (List.mem_range.1 hl')
  obtain ⟨hP, hQ⟩ := hpq hb
  rw [hl] at hP hQ
  -- the range factor
  have hx : rgEqF (tsBX.map fun p => p.2.ev e) 18 = fun l b => if b then Rev4.blkOf r l else 1 - Rev4.blkOf r l := by
    funext l b
    simp only [rgEqF, Rev4.blkOf, tsBX, List.map_map]
    rw [getD_range_map _ l.isLt, Function.comp_apply, ev_I, hr _ (by omega)]
  have hc : rgVal (tsBX.map fun p => p.1.ev e) = Rev4.lastAt r 19 := by
    rw [Rev4.lastAt, sum_bits_rgVal (fun p => r.getD p 0) 18 19]
    simp only [tsBX, List.map_map]
    refine congrArg rgVal (List.map_congr_left fun l hl' => ?_)
    simp only [Function.comp_apply, ev_I]
    exact hr _ (by have := List.mem_range.1 hl'; omega)
  have hR : (pq.1 ++ pq.2).ev e = Rev4.segRangeI r := by
    rw [ev_append, hP, hQ, hx, hc, Rev4.segRangeI, prefixP_succ, add_comm]
  -- the outputs
  have h0 : e.inp 0 = r.getD 0 0 := hr 0 (by norm_num)
  have hsz : (targetSLeafI r).size = 64 := by simp [targetSLeafI]
  refine List.ext_getElem (by simp [Rev4.targetSSegI, hsz]) fun σ h₁ h₂ => ?_
  have hσ : σ < 64 := by simpa using h₁
  have hg : (targetSLeafI r)[σ]'(by rw [hsz]; exact hσ) = (targetSLeafI r).getD σ 0 := by
    simp [Array.getD_eq_getD_getElem?, hsz, hσ]
  simp only [List.getElem_map, List.getElem_range, ev_append, ev_sc, hrR, hR, ev_I, h0, Rev4.targetSSegI,
    Array.getElem_toList, Array.getElem_map, hg, leaf_affine r σ, tsA0, tsA1]
  ring


/-! ## `shiftTarget`: the digest bits -/

/-- `n` free locals from `k` (a `pad`: no gate equation, no row); its result is `k`. -/
def bitsG (n : ℕ) : GM ℕ := fun k => ([.pad 0 n], k)

/-- The pack `Σ_{b<128} E_b · L (o + b)`. -/
def packL (o : ℕ) : LinT := (List.range 128).flatMap fun b => sc (W4.E b) (L (o + b))

/-- **A digest's 256 bit locals** from `kb`: `bit · bit = bit`, and the two packs are the halves `h0`,
`h1`. -/
def digRows (kb : ℕ) (h0 h1 : LinT) : List RowT :=
  (List.range 256).map (fun i => ⟨L (kb + i), L (kb + i), L (kb + i)⟩) ++
    [⟨C 1, packL kb, h0⟩, ⟨C 1, packL (kb + 128), h1⟩]

theorem packL_ev (o : ℕ) : (packL o).ev e = ∑ b ∈ range 128, W4.E b * e.loc (o + b) := by
  rw [packL, ev_flatMap, ← sumTo_list, sumTo_eq]
  simp only [ev_sc, ev_L]

/-- **Packed Boolean values are the element's bits** (`W4.bitF_sumO`). -/
theorem bits_of_pack {v : ℕ → F} {h : F} (hb : ∀ q < 128, v q = 0 ∨ v q = 1)
    (hp : ∑ q ∈ range 128, W4.E q * v q = h) (j : Fin 128) : v j = if bitF h j then 1 else 0 := by
  have := W4.bitF_sumO (v := v) (d := 0) (n := 128) (by norm_num) hb j
  simp only [add_zero, Nat.sub_zero, zero_le, true_and, zero_add, hp] at this
  rw [this]
  rcases hb j j.isLt with h' | h'
  · simp [h']
  · simp [h', j.isLt]

/-- **The bits of a digest** given as its two halves' packs (`Impl.digBit`'s order). -/
theorem bits_dig {v : ℕ → F} {h0 h1 : F} (hb : ∀ q < 256, v q = 0 ∨ v q = 1)
    (hp0 : ∑ q ∈ range 128, W4.E q * v q = h0) (hp1 : ∑ q ∈ range 128, W4.E q * v (128 + q) = h1) :
    ∀ σ < 256, v σ = if digBit h0 h1 σ then 1 else 0 := by
  intro σ hσ
  unfold digBit
  by_cases hs : σ < 128
  · rw [dif_pos hs]; exact bits_of_pack (fun q hq => hb q (by omega)) hp0 ⟨σ, hs⟩
  · rw [dif_neg hs]
    have := bits_of_pack (v := fun q => v (128 + q)) (fun q hq => hb _ (by omega)) hp1
      ⟨(σ - 128) % 128, Nat.mod_lt _ (by norm_num)⟩
    simp only at this
    rw [show 128 + (σ - 128) % 128 = σ by omega] at this
    exact this

/-- **The bit rows give the digest's bits.** -/
theorem ok_digRows (h1 : e.one = 1) {kb : ℕ} {h0 h1' : LinT} (h : ∀ q ∈ digRows kb h0 h1', q.Holds e) :
    ∀ σ < 256, e.loc (kb + σ) = if digBit (h0.ev e) (h1'.ev e) σ then 1 else 0 := by
  have hb : ∀ q < 256, e.loc (kb + q) = 0 ∨ e.loc (kb + q) = 1 := fun q hq => by
    have := h ⟨L (kb + q), L (kb + q), L (kb + q)⟩
      (List.mem_append_left _ (List.mem_map.2 ⟨q, List.mem_range.2 hq, rfl⟩))
    simp only [RowT.Holds, ev_L] at this
    exact bool_of_row this
  have r0 := h ⟨C 1, packL kb, h0⟩ (List.mem_append_right _ (List.mem_cons_self ..))
  have r1 := h ⟨C 1, packL (kb + 128), h1'⟩
    (List.mem_append_right _ (List.mem_cons_of_mem _ (List.mem_cons_self ..)))
  simp only [RowT.Holds, ev_C, h1, mul_one, one_mul, packL_ev] at r0 r1
  refine bits_dig (v := fun q => e.loc (kb + q)) hb r0 ?_
  rw [← r1]
  exact Finset.sum_congr rfl fun q _ => by rw [Nat.add_assoc]

/-! ## `shiftTarget`: the template -/

theorem foldl_mul_rangeC {M : Type*} [CommMonoid M] (g : ℕ → M) :
    ∀ n (c : M), (List.range n).foldl (fun acc k => acc * g k) c = c * ∏ k ∈ range n, g k
  | 0, c => by simp
  | n + 1, c => by
    rw [List.range_succ, List.foldl_append, foldl_mul_rangeC g n c, Finset.prod_range_succ]
    simp [mul_assoc]

/-- `a · b + c` (one gate). -/
def mulAddF (a b c : LinT) : GM LinT := GM.gate (.mulAdd a b c) L

theorem ok_mulAddF (a b c : LinT) : GM.Ok e (mulAddF a b c) fun o => o.ev e = a.ev e * b.ev e + c.ev e :=
  fun k h => by
    have := (Eqns.cons.1 h).1
    simpa [mulAddF, GM.gate, Gate.Eqn] using this

/-- `eq(t, b)` in characteristic two is linear. -/
theorem eq_lin (t b : F) : t * b + (1 - t) * (1 - b) = 1 + t + b := by
  linear_combination (t * b - t - b) * (CharTwo.two_eq_zero (R := F))

/-- **`eq(θ, σ)` over 10 coordinates at `σ < 256`**: bits 8 and 9 are clear. -/
theorem eqAtR_ten (θ : Array F) {σ : ℕ} (hσ : σ < 256) :
    eqAtR (ptA 10 θ) σ = eqAtR (fun l : Fin 8 => θ.getD l 0) σ * ((1 - θ.getD 8 0) * (1 - θ.getD 9 0)) := by
  have h8 : σ.testBit 8 = false := Nat.testBit_lt_two_pow (by norm_num; omega)
  have h9 : σ.testBit 9 = false := Nat.testBit_lt_two_pow (by norm_num; omega)
  unfold eqAtR
  rw [Fin.prod_univ_castSucc, Fin.prod_univ_castSucc]
  simp [ptA, h8, h9, mul_assoc]

/-- **The segment's `shiftTarget` template** (the hints are not read): inputs `τ` `0 … 17`, `θ`
`18 … 27`, `bnd` `28 … 49`, `κs` `50`. -/
def stSegT (_ : List (Option F)) : GM (List LinT × List RowT) :=
  (bitsG 256).bind fun kh =>
  (bitsG 256).bind fun ks =>
  GM.bind (eqTblG (List.ofFn fun l : Fin 8 => I (18 + l))) fun E =>
  (GM.mapL (fun σ => mulF (L (kh + σ)) (E.getD σ [])) (List.range 256)).bind fun dh =>
  (GM.mapL (fun σ => mulF (L (ks + σ)) (E.getD σ [])) (List.range 256)).bind fun ds =>
  (GM.foldL (fun acc l => mulF acc (C 1 ++ I l ++ I (32 + l))) (C 1) (List.range 18)).bind fun eL =>
  (mulF (C 1 ++ sc (-1) (I 26)) (C 1 ++ sc (-1) (I 27))).bind fun f89 =>
  (mulF eL dh.flatten).bind fun m1 =>
  (mulAddF (I 50) ds.flatten m1).bind fun m2 =>
  (mulF f89 m2).map fun out => ([out], digRows kh (I 30) (I 31) ++ digRows ks (I 28) (I 29))

/-- A digest's sum `Σ_σ bit_σ E[σ]` is `digestMle` up to the factor `(1 − θ₈)(1 − θ₉)`. -/
theorem digest_eq (θ : Array F) (v : ℕ → F) (h0 h1 : F) (hv : ∀ σ < 256, v σ = if digBit h0 h1 σ then 1 else 0) :
    digestMle (eqTable (List.ofFn (ptA 10 θ))) h0 h1 =
      (∑ σ ∈ range 256, v σ * eqAtR (fun l : Fin 8 => θ.getD l 0) σ) * ((1 - θ.getD 8 0) * (1 - θ.getD 9 0)) := by
  unfold digestMle
  rw [sumTo_eq, Finset.sum_mul]
  refine Finset.sum_congr rfl fun σ hσ => ?_
  have hσ' := Finset.mem_range.1 hσ
  rw [eqTable_ofFn_getD _ (lt_of_lt_of_le hσ' (by norm_num)), eqAtR_ten θ hσ', hv σ hσ']
  split_ifs <;> ring

/-- **The `shiftTarget` template computes `shiftTargetI`** of the inputs, its forcing rows holding. -/
theorem ok_stSegT (h1 : e.one = 1) (cst : List (Option F)) (κs : F) (τ θ bnd : Array F)
    (hτ : ∀ l < 18, e.inp l = τ.getD l 0) (hθ : ∀ l < 10, e.inp (18 + l) = θ.getD l 0)
    (hb : ∀ l < 22, e.inp (28 + l) = bnd.getD l 0) (hκ : e.inp 50 = κs) :
    GM.Ok e (stSegT cst) fun o => (∀ q ∈ o.2, q.Holds e) → o.1.map (LinT.ev e) = [shiftTargetI κs τ θ bnd] := by
  unfold stSegT
  refine GM.ok_bind (P := fun _ => True) (fun _ _ => trivial) fun kh _ => ?_
  refine GM.ok_bind (P := fun _ => True) (fun _ _ => trivial) fun ks _ => ?_
  refine GM.ok_bind (g := eqTblG (List.ofFn fun l : Fin 8 => I (18 + l)))
    (P := fun E => E.map (LinT.ev e) = (eqTable ((List.ofFn fun l : Fin 8 => I (18 + l)).map (LinT.ev e))).toList)
    (fun k hk => eqTblG_ev h1 _ k hk) fun E hE => ?_
  have hEσ : ∀ σ < 256, (E.getD σ []).ev e = eqAtR (fun l : Fin 8 => θ.getD l 0) σ := fun σ hσ => by
    rw [getD_map_ev, hE, arr_getD, List.map_ofFn, eqTable_ofFn_getD _ (lt_of_lt_of_le hσ (by norm_num))]
    congr 1; funext l
    simp only [Function.comp_apply, ev_I]
    exact hθ l (by omega)
  refine GM.ok_bind (GM.ok_mapL (E := LinT.ev e)
    (v := fun σ => e.loc (kh + σ) * eqAtR (fun l : Fin 8 => θ.getD l 0) σ) (List.range 256)
    fun σ hσ => GM.ok_mono (ok_mulF _ _) fun o ho => by rw [ho, ev_L, hEσ σ (List.mem_range.1 hσ)])
    fun dh hdh => ?_
  refine GM.ok_bind (GM.ok_mapL (E := LinT.ev e)
    (v := fun σ => e.loc (ks + σ) * eqAtR (fun l : Fin 8 => θ.getD l 0) σ) (List.range 256)
    fun σ hσ => GM.ok_mono (ok_mulF _ _) fun o ho => by rw [ho, ev_L, hEσ σ (List.mem_range.1 hσ)])
    fun ds hds => ?_
  refine GM.ok_bind (GM.ok_foldL (E := LinT.ev e) (g := fun acc l => acc * (1 + e.inp l + e.inp (32 + l)))
    (List.range 18) (C 1) fun b a _ => GM.ok_mono (ok_mulF _ _) fun o ho => by
      rw [ho]; simp only [ev_append, ev_C, ev_I, h1, mul_one]) fun eL heL => ?_
  refine GM.ok_bind (ok_mulF _ _) fun f89 hf89 => GM.ok_bind (ok_mulF _ _) fun m1 hm1 =>
    GM.ok_bind (ok_mulAddF _ _ _) fun m2 hm2 => GM.ok_map (ok_mulF _ _) fun out hout hrows => ?_
  -- the bits
  have hbh := ok_digRows h1 (fun q hq => hrows q (List.mem_append_left _ hq))
  have hbs := ok_digRows h1 (fun q hq => hrows q (List.mem_append_right _ hq))
  simp only [ev_I] at hbh hbs
  have hb0 := hb 0 (by norm_num); have hb1 := hb 1 (by norm_num)
  have hb2 := hb 2 (by norm_num); have hb3 := hb 3 (by norm_num)
  simp only [add_zero, show 28 + 1 = 29 from rfl, show 28 + 2 = 30 from rfl, show 28 + 3 = 31 from rfl] at hb0 hb1 hb2 hb3
  rw [hb2, hb3] at hbh
  rw [hb0, hb1] at hbs
  -- the value
  simp only [List.map_cons, List.map_nil, List.cons.injEq, and_true]
  rw [hout, hm2, hm1, hf89, heL, ev_flatten, ev_flatten, hdh, hds, ← sumTo_list, ← sumTo_list, sumTo_eq, sumTo_eq,
    foldl_mul_rangeC, ev_I, hκ]
  unfold shiftTargetI
  simp only []
  rw [digest_eq θ _ _ _ hbh, digest_eq θ _ _ _ hbs, prodTo_eq]
  have hL : ∏ k ∈ range 18, (1 + e.inp k + e.inp (32 + k)) =
      ∏ l ∈ range 18, (τ.getD l 0 * bnd.getD (4 + l) 0 + (1 - τ.getD l 0) * (1 - bnd.getD (4 + l) 0)) :=
    Finset.prod_congr rfl fun l hl => by
      have hl' := Finset.mem_range.1 hl
      have h4 := hb (4 + l) (by omega)
      rw [show 28 + (4 + l) = 32 + l by omega] at h4
      rw [eq_lin, hτ l hl', h4]
  have h8 := hθ 8 (by norm_num); have h9 := hθ 9 (by norm_num)
  simp only [show 18 + 8 = 26 from rfl, show 18 + 9 = 27 from rfl] at h8 h9
  simp only [ev_append, ev_sc, ev_C, ev_I, h1, mul_one, one_mul, hL, h8, h9]
  ring

end Tpl
end FR

end G6_FRVIRTplSegT
