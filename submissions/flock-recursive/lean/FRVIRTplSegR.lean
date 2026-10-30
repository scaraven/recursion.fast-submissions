-- New for `flock-recursive` (SEG-R §4.4, stage SEG-R1): the segment program's `rsWeight` replay template.
import FRVIRTplChain

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
