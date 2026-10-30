-- G6: this module also holds the former modules `FRVIRTplRep`, `FRVIRTplMaskN`, `FRVIRTplKMux`, `FRVIRTplExt` (one section each, in import order).
import FRVIRTplLag
import FRVIRTplTab
import FRVIRTplSeg
import FRVIRCompileSound
import FRVIRTplWalk
import FRVerifierImplOps
import Mathlib.Data.Nat.Size

section G6_FRVIRTplRep

-- New for `flock-recursive` (BLUEPRINT A.11, §10 changes 17; stage S-E6, track L-circ).

/-!
# Replay templates for the ops still imported (S-E6): `tensorW`, `rowW`

BLUEPRINT A.11's table. Each template mirrors `implC`'s implementation gate for gate, so its
correctness is an identity of pure functions (`tplX_ok`, the shape of S-E3's templates).

* **`tensorW j r`** (`Impl.tensorWI`): `Π_{v<n} (1 − r_v + r_v·Ŵ_v(D[j]))`. `Ŵ_v(D[j]) =
  Σ_{i<20} bit_i(j) · Ŵ_v(D[2^i])` (`Impl.wAtT`) is a **linear form** in `j`'s bits (an auxiliary
  import, `AuxK.bits 20`), so a factor costs two `K × F` gates and the product `n` Karatsuba
  products: `5n` rows.
* **`rowW λ r′_hi`** (`Impl.rowWI`): the 64 Lagrange weights `L_c(λ)` (`lagG`) and the table
  `eq(r′_hi, ·)` over 8 coordinates (`eqTblG`), then the `2^14` products `L_{k mod 64}·E_{⌊k/64⌋}`.
-/

namespace FR
namespace Tpl
open Circ

variable {e : Env}

/-! ## `tensorW` -/

/-- `Ŵ_v(D[j])` as a form over `j`'s bits (inputs `boff + i`, `i < 20`). -/
def twW (boff v : ℕ) : LinT :=
  sumLT logNMax fun i => sc ((Impl.wTab.getD v #[]).getD i 0) (I (boff + i))

/-- The factor `1 − r_v + r_v·ŵ_v` of `n` coordinates (two gates, locals `k`, `k + 1`). -/
def twFac (n v k : ℕ) : List Gate × (LinT × LinT) :=
  ([.mul (I (2 * v)) (twW (2 * n) v), .mul (I (2 * v + 1)) (twW (2 * n) v)],
   (C 1 ++ I (2 * v) ++ L k, I (2 * v + 1) ++ L (k + 1)))

/-- The product of the first `m` factors (`prodTo`'s fold, from `1`). -/
def twChain (n : ℕ) : ℕ → List Gate × (LinT × LinT)
  | 0 => ([], (C 1, []))
  | m + 1 =>
    let p := twChain n m
    let q := mulKG p.2 (twFac n m (nlocs p.1)).2 (nlocs p.1 + 2)
    (p.1 ++ (twFac n m (nlocs p.1)).1 ++ q.1, q.2)

/-- **`tensorW`** for `r : AK n` (inputs `0 … 2n−1`) and `j`'s 20 bits (inputs `2n … 2n+19`). -/
def tplTensorW (n : ℕ) : Tpl := ⟨(twChain n n).1, [(twChain n n).2.1, (twChain n n).2.2]⟩

theorem twChain_nlocs (n : ℕ) : ∀ m, nlocs (twChain n m).1 = 5 * m
  | 0 => rfl
  | m + 1 => by
    simp only [twChain, nlocs_appendL, twChain_nlocs n m, mulKG_nlocs]
    simp [twFac, nlocs, Gate.nloc]; ring

theorem twW_ev {n v : ℕ} {j : ℕ} (hv : v < logNMax)
    (hb : ∀ i < logNMax, e.inp (2 * n + i) = if j.testBit i then 1 else 0) :
    (twW (2 * n) v).ev e = Impl.wAtT v j := by
  rw [twW, ev_sumLT, Impl.wAtT, if_pos hv, FR.sumTo_eq]
  refine Finset.sum_congr rfl fun i hi => ?_
  rw [ev_sc, ev_I, hb i (Finset.mem_range.1 hi)]
  split_ifs <;> simp

theorem twChain_ev (h1 : e.one = 1) {n : ℕ} {r : Array K} {j : ℕ} (hn : n ≤ logNMax)
    (hr : ∀ v < n, e.inp (2 * v) = (r.getD v 0).f₀ ∧ e.inp (2 * v + 1) = (r.getD v 0).f₁)
    (hb : ∀ i < logNMax, e.inp (2 * n + i) = if j.testBit i then 1 else 0) :
    ∀ m ≤ n, Eqns e (twChain n m).1 0 →
      evK e (twChain n m).2 =
        Impl.prodTo m fun v => 1 - r.getD v 0 + r.getD v 0 * algebraMap F K (Impl.wAtT v j)
  | 0, _, _ => by
    apply K_ext' <;> simp [twChain, evK, h1, Impl.prodTo] <;> rfl
  | m + 1, hm, h => by
    simp only [twChain, Eqns.append, twChain_nlocs, zero_add] at h
    obtain ⟨⟨hp, hf⟩, hq⟩ := h
    have hk : 5 * m + nlocs (twFac n m (5 * m)).1 = 5 * m + 2 := by simp [twFac, nlocs, Gate.nloc]
    rw [nlocs_appendL, twChain_nlocs, hk] at hq
    have ih := twChain_ev h1 hn hr hb m (by omega) hp
    simp only [twChain, twChain_nlocs]
    rw [mulKG_ev _ _ _ hq, ih, Impl.prodTo_eq, Impl.prodTo_eq, Finset.prod_range_succ]
    congr 1
    simp only [twFac, Eqns.cons, Gate.Eqn, Gate.nloc, Eqns.nil, and_true] at hf
    obtain ⟨f0, f1⟩ := hf
    obtain ⟨r0, r1⟩ := hr m (by omega)
    have hw := twW_ev (n := n) (v := m) (by omega) hb
    apply K_ext'
    · simp only [evK, twFac, ev_append, ev_C, ev_I, ev_L, h1, f0, r0, hw, K_add_f₀,
        K_one_sub_f₀, K_mul_f₀, K.algebraMap_eq_ofF, K.ofF]
      ring
    · simp only [evK, twFac, ev_append, ev_I, ev_L, f1, r1, hw, K_add_f₁, K_one_sub_f₁,
        K_mul_f₁, K.algebraMap_eq_ofF, K.ofF, r0]
      linear_combination -(r.getD m 0).f₀ * Impl.wAtT m j * (CharTwo.two_eq_zero (R := F))

/-- **`tensorW`'s template gives `Impl.tensorWI`.** -/
theorem tplTensorW_ok (h1 : e.one = 1) {r : Array K} {j : ℕ} (hn : r.size ≤ logNMax)
    (hi : InpIs e (r.toList.flatMap encK ++
      (List.range logNMax).map fun i => if j.testBit i then 1 else 0))
    (h : Eqns e (tplTensorW r.size).gates 0) :
    (tplTensorW r.size).outs.map (LinT.ev e) = encV (.k (Impl.tensorWI j r)) := by
  have hlen : (r.toList.flatMap encK).length = 2 * r.size := by
    rw [length_flatMap_encK, Array.length_toList]
  have hr : ∀ v < r.size, e.inp (2 * v) = (r.getD v 0).f₀ ∧
      e.inp (2 * v + 1) = (r.getD v 0).f₁ := fun v hv => by
    rw [hi, hi, getD_append_left (by omega), getD_append_left (by omega)]
    exact ⟨by simpa using (encK_getD r.toList v).1, by simpa using (encK_getD r.toList v).2⟩
  have hb : ∀ i < logNMax, e.inp (2 * r.size + i) = if j.testBit i then 1 else 0 := fun i hi' => by
    rw [hi, ← hlen, getD_append_right, List.getD_eq_getElem _ _ (by simpa using hi'),
      List.getElem_map, List.getElem_range]
  have := twChain_ev h1 hn hr hb r.size le_rfl h
  simp only [tplTensorW, List.map_cons, List.map_nil, encV, encK, Impl.tensorWI]
  rw [← this]; rfl

theorem tplTensorW_nlocs (n : ℕ) : nlocs (tplTensorW n).gates = 5 * n := twChain_nlocs n n

/-! ## `rowW` -/

/-- `rowW`'s template for `N` products: the products `L_{k mod 64} · E_{⌊k/64⌋}` first (locals and
rows `0 … N − 1`, so that product `k` is row `k` and local `k`), then the 64 weights `L_c(λ)`
(`lagG`, locals from `N`) and the table `eq(r′_hi, ·)` over 8 coordinates (`eqTblG`). -/
def rowWG (N : ℕ) : Tpl :=
  ⟨mulsG N (fun k => (lagG Impl.xT 64 Impl.denS (I 0) N).2.getD (k % 64) [])
      (fun k => (eqTblG ((List.range 8).map fun l => I (l + 1))
        (N + nlocs (lagG Impl.xT 64 Impl.denS (I 0) N).1)).2.getD (k / 64) []) ++
      (lagG Impl.xT 64 Impl.denS (I 0) N).1 ++
      (eqTblG ((List.range 8).map fun l => I (l + 1)) (N + nlocs (lagG Impl.xT 64 Impl.denS (I 0) N).1)).1,
    (List.range N).map fun k => L k⟩

/-- `rowWG` with the weights and the table built once (`rowWG` rebuilds them per product; S-E13:
plan time). -/
def rowWGF (N : ℕ) : Tpl :=
  let g := lagG Impl.xT 64 Impl.denS (I 0) N
  let t := eqTblG ((List.range 8).map fun l => I (l + 1)) (N + nlocs g.1)
  ⟨mulsG N (fun k => g.2.getD (k % 64) []) (fun k => t.2.getD (k / 64) []) ++ g.1 ++ t.1,
    (List.range N).map fun k => L k⟩

theorem rowWGF_eq (N : ℕ) : rowWGF N = rowWG N := rfl

/-- **`rowW`** (inputs `λ`, then `r′_hi`'s coordinates): `rowWG` at `2^14` products. -/
def tplRowW : Tpl := rowWGF (2 ^ 14)

theorem rowWI_size (l : F) (r : Array F) : (Impl.rowWI l r).size = 2 ^ 14 := Array.size_ofFn ..

theorem rowWG_ev (h1 : e.one = 1) (N : ℕ) {l : F} {rhi : Array F} (hi : InpIs e (l :: rhi.toList))
    (h : Eqns e (rowWG N).gates 0) {k : ℕ} (hk : k < N) :
    e.loc k = (Impl.lagW Impl.xT 64 Impl.denS l).getD (k % 64) 0 *
      (eqTable (List.ofFn (Impl.ptA 8 rhi))).getD (k / 64) 0 := by
  unfold rowWG at h
  rw [Eqns.append, Eqns.append, nlocs_appendL, mulsG_nlocs, zero_add, zero_add] at h
  obtain ⟨⟨hm, hg⟩, ht⟩ := h
  have hl : (I 0).ev e = l := by rw [ev_I, hi]; rfl
  have hw := fun j (hj : j < 64) => lagG_ev h1 _ _ _ _ _ hg hj
  rw [hl] at hw
  have hE := eqTblG_ev h1 _ _ ht
  have hcs : ((List.range 8).map fun l => I (l + 1)).map (LinT.ev e) =
      List.ofFn (Impl.ptA 8 rhi) := by
    refine List.ext_getElem (by simp) fun j h₁ h₂ => ?_
    simp only [List.map_map, Function.comp_apply, List.getElem_map, List.getElem_range, ev_I,
      List.getElem_ofFn, Impl.ptA, hi, List.getD_cons_succ, Array.getD_eq_getD_getElem?,
      List.getD_eq_getElem?_getD, Array.getElem?_toList]
    rw [hi]; simp [List.getD_eq_getElem?_getD]
  rw [← zero_add k, mulsG_eqns hm k hk, zero_add, hw _ (Nat.mod_lt _ (by norm_num)), getD_map_ev,
    hE, hcs]
  simp only [Array.getD_eq_getD_getElem?, List.getD_eq_getElem?_getD, Array.getElem?_toList]

/-- **`rowW`'s template gives `Impl.rowWI`.** -/
theorem tplRowW_ok (h1 : e.one = 1) {l : F} {rhi : Array F} (hi : InpIs e (l :: rhi.toList))
    (h : Eqns e tplRowW.gates 0) :
    tplRowW.outs.map (LinT.ev e) = encV (.af (Impl.rowWI l rhi)) := by
  rw [tplRowW, rowWGF_eq]; simp only [rowWG, encV]
  refine List.ext_getElem (by simp [rowWI_size]) fun k h₁ h₂ => ?_
  have hk : k < 2 ^ 14 := by simpa using h₁
  simp only [List.getElem_map, List.getElem_range, Array.getElem_toList, Impl.rowWI,
    Array.getElem_ofFn, ev_L]
  exact rowWG_ev h1 _ hi h hk

end Tpl
end FR

end G6_FRVIRTplRep

section G6_FRVIRTplMaskN

-- New for `flock-recursive` (BLUEPRINT revision 4.1, B-13, A.9 `finSh`, A.11; stage S-E12e, track
-- L-circ).

/-!
# The replay template of a node's `shiftMask` (revision 4.1, the `chainLk4` mask), kind-muxed

A node of kind `ν` runs `NI4.shiftMask4I ν τ r` (`FRVerifierImplNode4`): with `n = nb(ν)`
coordinates, `c = chLen₀ + chLen₁ − 1` and `a = chLen₀ − 1`, the triple

  `(Σ_{y<c} eq(τ,y) eq(r,y) − eq(τ,a) eq(r,a),  Σ_{y<c} eq(τ,y) eq(r,y+1) − eq(τ,a) eq(r,a+1),
    eq(r,0) + eq(r,chLen₀))`,

the prefix sums by `prefixP` and `shP` (the low bit first). That module is downstream of this one,
so the value is a copy over the constants `q = (nb, chLen₀, chLen₁)`: **`maskNV q`**
(`FRVIRTpl4Bridge.maskNV_eq`: `maskNV (maskQ ν) = shiftMask4I ν`).

The node prototype is one program for the group `{N4, N2, N8}` (the selector index `ι` stands for
`nodeGrp ι`), so the template is **kind-muxed**: it computes every kind's triple (`blkG`, one
sub-circuit per entry of `ks`, each mirroring `maskNV` gate for gate at its constants: `prefixG`
for `prefixP`, `shG` for `shP`, `eqAtG` for the `eq`s at constant indices), and the outputs are
`Σ_j sel_j · out_j` (the selector forms are the instance's last inputs). The products
`t_l = τ_l r_l` are shared. **`tplMaskN_ok`**: with the selectors one-hot at `j₀`, the outputs are
`maskNV ks[j₀]`.
-/

namespace FR
namespace Tpl
open Circ Finset

variable {e : Env}

/-! ## The value (a copy of `NI4.shiftMask4I` over its constants) -/

/-- `m_l(b, b′) = eq(τ_l, b)·eq(r_l, b′)` (`NI4.mF`). -/
def mFV {n : ℕ} (τ r : Fin n → F) (l : Fin n) (b b' : Bool) : F :=
  (if b then τ l else 1 - τ l) * (if b' then r l else 1 - r l)

/-- The successor's prefix sum by the low bit (`NI4.shP`). -/
def shPV : (n : ℕ) → (Fin n → Bool → Bool → F) → ℕ → F
  | 0, _, _ => 0
  | n + 1, m, c => m 0 false true * prefixP n (fun l b => m l.succ b b) ((c + 1) / 2) +
      m 0 true false * shPV n (fun l => m l.succ) (c / 2)

/-- **A node's `shiftMask` at the constants `q = (nb, chLen₀, chLen₁)`** (`NI4.shiftMask4I`). -/
def maskNV (q : ℕ × ℕ × ℕ) (τ r : Array F) : F × F × F :=
  let n := q.1
  let τ' := Impl.ptA n τ; let r' := Impl.ptA n r
  let L0 := q.2.1
  let c := L0 + q.2.2 - 1
  let ea := Impl.eqAtR τ' (L0 - 1)
  (prefixP n (fun l b => mFV τ' r' l b b) c - ea * Impl.eqAtR r' (L0 - 1),
   shPV n (mFV τ' r') c - ea * Impl.eqAtR r' L0,
   Impl.eqAtR r' 0 + Impl.eqAtR r' L0)

/-! ## The prefix sums, gate for gate -/

/-- `prodAt e c` over factor forms `e l b` (`n` products; `0` if `c ≥ 2^n`). -/
def prodAtG (n : ℕ) (e : ℕ → Bool → LinT) (c k : ℕ) : List Gate × LinT :=
  if c < 2 ^ n then prodG (C 1) ((List.range n).map fun l => e l (c.testBit l)) k else ([], [])

theorem prodAtG_ev (h1 : e.one = 1) (n : ℕ) (f : ℕ → Bool → LinT) (c k : ℕ)
    (h : Eqns e (prodAtG n f c k).1 k) :
    (prodAtG n f c k).2.ev e = prodAt (fun (l : Fin n) b => (f l b).ev e) c := by
  unfold prodAtG prodAt at *
  split_ifs at h ⊢ with hc
  · rw [prodG_ev _ _ _ h, ev_C, h1, one_mul, one_mul, List.map_map, prod_range_list (M := F),
      ← Fin.prod_univ_eq_prod_range]
    rfl
  · rfl

/-- **`prefixP` over factor forms**, gate for gate (`(e₀ + e₁)·rec`, and on an odd `c`
`e₀(0)·prodAt`). -/
def prefixG : ℕ → (ℕ → Bool → LinT) → ℕ → ℕ → List Gate × LinT
  | 0, _, c, _ => ([], if 0 < c then C 1 else [])
  | n + 1, f, c, k =>
    let r := prefixG n (fun l => f (l + 1)) (c / 2) k
    let k1 := k + nlocs r.1
    if c % 2 = 1 then
      let p := prodAtG n (fun l => f (l + 1)) (c / 2) (k1 + 1)
      let k2 := k1 + 1 + nlocs p.1
      (r.1 ++ (.mul (f 0 false ++ f 0 true) r.2 :: (p.1 ++ [.mul (f 0 false) p.2])), L k1 ++ L k2)
    else (r.1 ++ [.mul (f 0 false ++ f 0 true) r.2], L k1)

theorem prefixG_ev (h1 : e.one = 1) : ∀ (n : ℕ) (f : ℕ → Bool → LinT) (c k : ℕ),
    Eqns e (prefixG n f c k).1 k →
    (prefixG n f c k).2.ev e = prefixP n (fun (l : Fin n) b => (f l b).ev e) c
  | 0, f, c, k, _ => by
    simp only [prefixG, prefixP]; split_ifs <;> simp [h1]
  | n + 1, f, c, k, h => by
    simp only [prefixG] at h ⊢
    rw [prefixP]
    split_ifs at h ⊢ with hc
    · simp only [Eqns.append, Eqns.cons, Gate.nloc, Gate.Eqn, Eqns.nil, and_true] at h
      obtain ⟨hr, hm, hp, hl⟩ := h
      rw [ev_append, ev_L, ev_L, hm, hl, prefixG_ev h1 n _ _ _ hr, prodAtG_ev h1 n _ _ _ hp, ev_append]
      rfl
    · simp only [Eqns.append, Eqns.cons, Gate.nloc, Gate.Eqn, Eqns.nil, and_true] at h
      obtain ⟨hr, hm⟩ := h
      rw [ev_L, hm, prefixG_ev h1 n _ _ _ hr, ev_append, add_zero]
      rfl

/-- **`shP` over factor forms**, gate for gate. -/
def shG : ℕ → (ℕ → Bool → Bool → LinT) → ℕ → ℕ → List Gate × LinT
  | 0, _, _, _ => ([], [])
  | n + 1, m, c, k =>
    let p := prefixG n (fun l b => m (l + 1) b b) ((c + 1) / 2) k
    let k1 := k + nlocs p.1
    let s := shG n (fun l => m (l + 1)) (c / 2) (k1 + 1)
    let k2 := k1 + 1 + nlocs s.1
    (p.1 ++ (.mul (m 0 false true) p.2 :: (s.1 ++ [.mul (m 0 true false) s.2])), L k1 ++ L k2)

theorem shG_ev (h1 : e.one = 1) : ∀ (n : ℕ) (m : ℕ → Bool → Bool → LinT) (c k : ℕ),
    Eqns e (shG n m c k).1 k →
    (shG n m c k).2.ev e = shPV n (fun (l : Fin n) b b' => (m l b b').ev e) c
  | 0, m, c, k, _ => rfl
  | n + 1, m, c, k, h => by
    simp only [shG, Eqns.append, Eqns.cons, Gate.nloc, Gate.Eqn, Eqns.nil, and_true] at h
    obtain ⟨hp, hm, hs, hl⟩ := h
    simp only [shG]
    rw [ev_append, ev_L, ev_L, hm, hl, prefixG_ev h1 n _ _ _ hp, shG_ev h1 n _ _ _ hs, shPV]
    rfl

/-! ## One kind's sub-circuit -/

/-- `t_l = τ_l r_l`: the shared product's local (`[]` past `τ`'s `n`, where `τ_l = 0`). -/
def tF (n l : ℕ) : LinT := if l < n then L l else []

/-- `m_l(b, b′)` from `τ_l`, `r_l` and `t_l` (linear). -/
def mgN (n m l : ℕ) : Bool → Bool → LinT
  | true, true => tF n l
  | false, false => C 1 ++ sc (-1) (cT n l) ++ sc (-1) (cR n m l) ++ tF n l
  | true, false => cT n l ++ sc (-1) (tF n l)
  | false, true => cR n m l ++ sc (-1) (tF n l)

/-- **One kind's triple** at the constants `q`, its locals from `k` (the products `t_l` at locals
`0 … n − 1`). -/
def blkG (n m : ℕ) (q : ℕ × ℕ × ℕ) (k : ℕ) : List Gate × (LinT × LinT × LinT) :=
  let nb := q.1; let L0 := q.2.1; let c := L0 + q.2.2 - 1
  let P := prefixG nb (fun l b => mgN n m l b b) c k
  let k1 := k + nlocs P.1
  let S := shG nb (mgN n m) c k1
  let k2 := k1 + nlocs S.1
  let A := eqAtG nb (cT n) (L0 - 1) k2
  let k3 := k2 + nlocs A.1
  let B := eqAtG nb (cR n m) (L0 - 1) k3
  let k4 := k3 + nlocs B.1
  let Cl := eqAtG nb (cR n m) L0 k4
  let k5 := k4 + nlocs Cl.1
  let D := eqAtG nb (cR n m) 0 k5
  let k6 := k5 + nlocs D.1
  (P.1 ++ (S.1 ++ (A.1 ++ (B.1 ++ (Cl.1 ++ (D.1 ++ [.mul A.2 B.2, .mul A.2 Cl.2]))))),
   (P.2 ++ sc (-1) (L k6), S.2 ++ sc (-1) (L (k6 + 1)), D.2 ++ Cl.2))

/-- The kinds' sub-circuits in order. -/
def blksG (n m : ℕ) : List (ℕ × ℕ × ℕ) → ℕ → List Gate × List (LinT × LinT × LinT)
  | [], _ => ([], [])
  | q :: qs, k => let b := blkG n m q k; let r := blksG n m qs (k + nlocs b.1); (b.1 ++ r.1, b.2 :: r.2)

/-- A triple's values. -/
def ev3 (e : Env) (o : LinT × LinT × LinT) : F × F × F := (o.1.ev e, o.2.1.ev e, o.2.2.ev e)

/-- Output `i` of the triple (`0`, `1`, `2`). -/
def pr3 (i : ℕ) (o : LinT × LinT × LinT) : LinT := if i = 0 then o.1 else if i = 1 then o.2.1 else o.2.2

/-- **The node's `shiftMask`** for `τ : AF n`, `r : AF m` and the kinds `ks` (inputs `τ`, `r`, then
one selector per kind): the shared products, the kinds' sub-circuits, and per output `i` the
products `sel_j · out_{j,i}`; output `i` is their sum. -/
def tplMaskN (n m : ℕ) (ks : List (ℕ × ℕ × ℕ)) : Tpl :=
  let Bk := blksG n m ks n
  let k1 := n + nlocs Bk.1
  let J := ks.length
  let mux := fun i : ℕ => mulsG J (fun j => I (n + m + j)) (fun j => pr3 i (Bk.2.getD j ([], [], [])))
  let out := fun i : ℕ => (List.range J).flatMap fun j => L (k1 + i * J + j)
  ⟨mulsG n (cT n) (cR n m) ++ (Bk.1 ++ (mux 0 ++ (mux 1 ++ mux 2))), [out 0, out 1, out 2]⟩

/-! ## Correctness -/

section Proof
variable {τ r : Array F} {sv : List F} (hi : InpIs e (τ.toList ++ r.toList ++ sv))
include hi

theorem cT_evN (l : ℕ) : (cT τ.size l).ev e = τ.getD l 0 := by
  by_cases h : l < τ.size
  · simp only [cT, h, ite_true]
    rw [ev_I, hi, List.append_assoc, getD_append_left (by simpa using h), arr_getD]
  · simp only [cT, h, ite_false, ev_nil]
    rw [Array.getD_eq_getD_getElem?, Array.getElem?_eq_none (by omega)]; rfl

theorem cR_evN (l : ℕ) : (cR τ.size r.size l).ev e = r.getD l 0 := by
  by_cases h : l < r.size
  · simp only [cR, h, ite_true]
    rw [ev_I, hi, List.append_assoc, ← Array.length_toList, getD_append_right,
      getD_append_left (by simpa using h), arr_getD]
  · simp only [cR, h, ite_false, ev_nil]
    rw [Array.getD_eq_getD_getElem?, Array.getElem?_eq_none (by omega)]; rfl

theorem sel_evN (j : ℕ) : (I (τ.size + r.size + j)).ev e = sv.getD j 0 := by
  rw [ev_I, hi, ← Array.length_toList, ← Array.length_toList, ← List.length_append, getD_append_right]

variable (ht : ∀ l, (tF τ.size l).ev e = τ.getD l 0 * r.getD l 0)
include ht

theorem mgN_ev (h1 : e.one = 1) (l : ℕ) (b b' : Bool) : (mgN τ.size r.size l b b').ev e =
    (if b then τ.getD l 0 else 1 - τ.getD l 0) * (if b' then r.getD l 0 else 1 - r.getD l 0) := by
  cases b <;> cases b' <;> simp only [mgN, ev_append, ev_sc, ev_C, cT_evN hi, cR_evN hi, ht] <;>
    simp [h1] <;> ring

set_option maxHeartbeats 1000000 in
/-- **One kind's sub-circuit computes `maskNV q`.** -/
theorem blkG_ev (h1 : e.one = 1) (q : ℕ × ℕ × ℕ) (k : ℕ) (h : Eqns e (blkG τ.size r.size q k).1 k) :
    ev3 e (blkG τ.size r.size q k).2 = maskNV q τ r := by
  simp only [blkG, Eqns.append, Eqns.cons, Gate.nloc, Gate.Eqn, Eqns.nil, and_true] at h
  obtain ⟨hP, hS, hA, hB, hC, hD, hm1, hm2⟩ := h
  have vP := prefixG_ev h1 _ _ _ _ hP
  have vS := shG_ev h1 _ _ _ _ hS
  have vA := eqAtG_ev h1 _ _ _ _ hA
  have vB := eqAtG_ev h1 _ _ _ _ hB
  have vC := eqAtG_ev h1 _ _ _ _ hC
  have vD := eqAtG_ev h1 _ _ _ _ hD
  simp only [mgN_ev hi ht h1, cT_evN hi, cR_evN hi] at vP vS vA vB vC vD
  simp only [blkG, ev3, maskNV, ev_append, ev_sc, ev_L, hm1, hm2, vP, vS, vA, vB, vC, vD]
  refine Prod.ext ?_ (Prod.ext ?_ rfl) <;> dsimp only <;> rw [sub_eq_add_neg] <;> ring_nf <;> rfl

theorem blksG_ev (h1 : e.one = 1) : ∀ (ks : List (ℕ × ℕ × ℕ)) (k : ℕ),
    Eqns e (blksG τ.size r.size ks k).1 k →
    (blksG τ.size r.size ks k).2.map (ev3 e) = ks.map fun q => maskNV q τ r
  | [], _, _ => rfl
  | q :: qs, k, h => by
    simp only [blksG, Eqns.append] at h
    simp only [blksG, List.map_cons, blkG_ev hi ht h1 q k h.1, blksG_ev h1 qs _ h.2]

end Proof

theorem sum_range_list {M : Type*} [AddCommMonoid M] (f : ℕ → M) :
    ∀ n, ((List.range n).map f).sum = ∑ i ∈ range n, f i
  | 0 => rfl
  | n + 1 => by rw [List.range_succ, List.map_append, List.sum_append, sum_range_list f n,
      sum_range_succ]; simp

section Mux
variable {τ r : Array F} {sv : List F} (hi : InpIs e (τ.toList ++ r.toList ++ sv))
include hi

set_option maxHeartbeats 1000000 in
/-- **The node template computes `maskNV ks[j₀]`** when the selector inputs are one-hot at `j₀`. -/
theorem tplMaskN_ok (h1 : e.one = 1) {ks : List (ℕ × ℕ × ℕ)} {j0 : ℕ} (hj : j0 < ks.length)
    (hs : ∀ j, sv.getD j 0 = if j = j0 then 1 else 0)
    (h : Eqns e (tplMaskN τ.size r.size ks).gates 0) :
    (tplMaskN τ.size r.size ks).outs.map (LinT.ev e) =
      encV (.f (maskNV (ks.getD j0 (0, 0, 0)) τ r).1) ++ encV (.f (maskNV (ks.getD j0 (0, 0, 0)) τ r).2.1) ++
        encV (.f (maskNV (ks.getD j0 (0, 0, 0)) τ r).2.2) := by
  simp only [tplMaskN, Eqns.append, mulsG_nlocs] at h
  obtain ⟨h0, hb, hm0, hm1, hm2⟩ := h
  -- the shared products
  have e0 := mulsG_eqns h0
  have ht : ∀ l, (tF τ.size l).ev e = τ.getD l 0 * r.getD l 0 := fun l => by
    by_cases hl : l < τ.size
    · simp only [tF, hl, if_true]
      rw [ev_L, ← zero_add l, e0 l hl, zero_add, cT_evN hi, cR_evN hi]
    · simp only [tF, hl, if_false]
      rw [ev_nil, Array.getD_eq_getD_getElem?, Array.getElem?_eq_none (by omega)]; simp
  simp only [zero_add] at hb hm0 hm1 hm2
  -- the kinds
  have vb := blksG_ev hi ht h1 ks _ hb
  set Bk := blksG τ.size r.size ks τ.size with hBk
  have hlen : Bk.2.length = ks.length := by simpa using congrArg List.length vb
  have hv : ev3 e (Bk.2.getD j0 ([], [], [])) = maskNV (ks.getD j0 (0, 0, 0)) τ r := by
    rw [List.getD_eq_getElem _ _ (hlen ▸ hj), List.getD_eq_getElem _ _ hj]
    have := List.getElem_of_eq vb (by rw [List.length_map]; exact hlen ▸ hj)
    simpa only [List.getElem_map] using this
  -- the mux: output `i` is `Σ_j sel_j · out_{j,i}` = `out_{j₀,i}`
  have mux : ∀ i K, Eqns e (mulsG ks.length (fun j => I (τ.size + r.size + j))
      (fun j => pr3 i (Bk.2.getD j ([], [], [])))) K →
      LinT.ev e ((List.range ks.length).flatMap fun j => L (K + j)) = (pr3 i (Bk.2.getD j0 ([], [], []))).ev e := by
    intro i K hK
    have em := mulsG_eqns hK
    rw [ev_flatMap, sum_range_list (M := F)]
    rw [Finset.sum_congr rfl fun j hjr => by rw [ev_L, em j (Finset.mem_range.1 hjr), sel_evN hi, hs j]]
    rw [Finset.sum_eq_single j0 (fun j _ hne => by rw [if_neg hne, zero_mul])
      (fun hn => absurd (Finset.mem_range.2 hj) hn), if_pos rfl, one_mul]
  simp only [List.map_cons, List.map_nil, encV, List.cons_append, List.nil_append]
  rw [← hv]
  refine List.cons_eq_cons.2 ⟨?_, List.cons_eq_cons.2 ⟨?_, List.cons_eq_cons.2 ⟨?_, rfl⟩⟩⟩
  · have := mux 0 _ hm0
    rw [show τ.size + nlocs Bk.1 = τ.size + nlocs Bk.1 + 0 * ks.length by ring] at this
    exact this
  · have := mux 1 _ hm1
    rw [show τ.size + nlocs Bk.1 + ks.length = τ.size + nlocs Bk.1 + 1 * ks.length by ring] at this
    exact this
  · have := mux 2 _ hm2
    rw [show τ.size + nlocs Bk.1 + ks.length + ks.length = τ.size + nlocs Bk.1 + 2 * ks.length by ring]
      at this
    exact this

end Mux

/-! ## Controls -/

/-- (+) Three outputs. -/
theorem tplMaskN_outs (n m : ℕ) (ks : List (ℕ × ℕ × ℕ)) : (tplMaskN n m ks).outs.length = 3 := rfl

/-- (+) `prefixP`'s mirror at `n = 2`, `c = 3` over the constant factors `e l b = [b]`: one
`x < 3` of the four has both bits set, so the value is `0` (not `1`, the count of `x = 3`). -/
theorem prefixP_ctl : prefixP 2 (fun (_ : Fin 2) (b : Bool) => (if b then 1 else 0 : F)) 3 = 0 ∧
    prefixP 2 (fun (_ : Fin 2) (b : Bool) => (if b then 1 else 0 : F)) 4 = 1 := by
  simp [prefixP, prodAt]

end Tpl
end FR

end G6_FRVIRTplMaskN

section G6_FRVIRTplKMux

-- New for `flock-recursive` (BLUEPRINT revision 4.3, route (A); stage S-E12f, track L-circ:
-- INT-9's finding F1).

/-!
# Kind-muxed templates: `tensorW` and `eqPt` on operands whose length depends on the kind

INT-8's group-uniform programs select some points by the kind (a `keep` chain over the kinds'
`packK`, a `packFK` of the kinds' lists), with a **length that depends on the kind**. `tensorW`
and `eqPt` on such a point have one template per kind here, muxed by the selectors (as
`tplMaskN`):

* **`kmuxT σ so nout ts`**: the sub-templates `ts`, sub-template `j` with its inputs substituted
  by `σ j` (`subW`: it reads its kind's operand block and the shared inputs) and its locals after
  the previous ones; then per output `c` the products `sel_j · out_{j,c}` (`sel_j` the input
  `so + j`), and output `c` is their sum. **`kmuxT_ok`**: with the selectors one-hot at `j₀`,
  the outputs are sub-template `j₀`'s at the wires it sees (`pullE`), and its gate equations hold
  there (`eqns_sub`).
* **`tplTensorWK ns`** (inputs: per kind a point `r_j : AK ns_j`, then `j`'s 20 bits, then the
  selectors) and **`tplEqPtK ps`** (inputs: per kind `a_j : AF`, `b_j : AF`, then the selectors),
  with **`tplTensorWK_ok`** and **`tplEqPtK_ok`**: the kind's `Impl.tensorWI`/`eqPoint`.
-/

namespace FR
namespace Tpl
open Circ Finset

variable {e : Env}

/-! ## Substitution -/

/-- A form with input `i` replaced by the form `σ i` and local `k` moved to `k0 + k`. -/
def subW (σ : ℕ → LinT) (k0 : ℕ) (l : LinT) : LinT :=
  l.flatMap fun t => match t.1 with
    | .one => [(.one, t.2)]
    | .inp i => sc t.2 (σ i)
    | .loc k => [(.loc (k0 + k), t.2)]

/-- A gate with its forms substituted (`subW`). -/
def Gate.sub (σ : ℕ → LinT) (k0 : ℕ) : Gate → Gate
  | .mul a b => .mul (subW σ k0 a) (subW σ k0 b)
  | .inv a => .inv (subW σ k0 a)
  | .mulAdd a b c => .mulAdd (subW σ k0 a) (subW σ k0 b) (subW σ k0 c)
  | .pad r l => .pad r l

/-- The wires a substituted template sees. -/
def pullE (e : Env) (σ : ℕ → LinT) (k0 : ℕ) : Env := ⟨e.one, fun i => (σ i).ev e, fun k => e.loc (k0 + k)⟩

theorem subW_cons (σ : ℕ → LinT) (k0 : ℕ) (t : Wire × F) (l : LinT) :
    subW σ k0 (t :: l) = subW σ k0 [t] ++ subW σ k0 l := by
  simp only [subW, List.flatMap_cons, List.flatMap_nil, List.append_nil]

theorem subW_one_ev (σ : ℕ → LinT) (k0 : ℕ) (t : Wire × F) :
    (subW σ k0 [t]).ev e = t.2 * t.1.ev (pullE e σ k0) := by
  obtain ⟨wr, c⟩ := t
  cases wr with
  | one => rw [subW, List.flatMap_cons, List.flatMap_nil, List.append_nil, ev_cons, ev_nil, add_zero]; rfl
  | inp i => rw [subW, List.flatMap_cons, List.flatMap_nil, List.append_nil, ev_sc]; rfl
  | loc k => rw [subW, List.flatMap_cons, List.flatMap_nil, List.append_nil, ev_cons, ev_nil, add_zero]; rfl

theorem subW_ev (σ : ℕ → LinT) (k0 : ℕ) (l : LinT) : (subW σ k0 l).ev e = l.ev (pullE e σ k0) := by
  induction l with
  | nil => rw [subW, List.flatMap_nil, ev_nil, ev_nil]
  | cons t l ih => rw [subW_cons, ev_append, subW_one_ev, ih, ev_cons]

theorem nloc_sub (σ : ℕ → LinT) (k0 : ℕ) (g : Gate) : (g.sub σ k0).nloc = g.nloc := by
  cases g <;> rfl

theorem nlocs_sub (σ : ℕ → LinT) (k0 : ℕ) : ∀ gs : List Gate, nlocs (gs.map (Gate.sub σ k0)) = nlocs gs
  | [] => rfl
  | g :: gs => by
    rw [List.map_cons, ← List.singleton_append, nlocs_append, nlocs_sub σ k0 gs,
      ← List.singleton_append (l := gs), nlocs_append]
    simp [nlocs, nloc_sub]

theorem eqn_sub (σ : ℕ → LinT) (k0 k : ℕ) (g : Gate) :
    (g.sub σ k0).Eqn e (k0 + k) ↔ g.Eqn (pullE e σ k0) k := by
  cases g <;> simp [Gate.sub, Gate.Eqn, subW_ev, pullE]

/-- **A substituted gate list's equations are the original's at the wires it sees.** -/
theorem eqns_sub (σ : ℕ → LinT) (k0 : ℕ) :
    ∀ (gs : List Gate) (k : ℕ), Eqns e (gs.map (Gate.sub σ k0)) (k0 + k) ↔ Eqns (pullE e σ k0) gs k
  | [], _ => by simp
  | g :: gs, k => by
    rw [List.map_cons, Eqns.cons, Eqns.cons, nloc_sub, eqn_sub, Nat.add_assoc, eqns_sub σ k0 gs]

/-! ## The kind mux -/

/-- The sub-templates `ts` (sub-template `j` substituted by `σ j`), their locals one after the
other from `k`: their gates and their outputs. -/
def subsG (σ : ℕ → ℕ → LinT) : List Tpl → ℕ → ℕ → List Gate × List (List LinT)
  | [], _, _ => ([], [])
  | T :: ts, j, k =>
    let r := subsG σ ts (j + 1) (k + nlocs T.gates)
    (T.gates.map (Gate.sub (σ j) k) ++ r.1, T.outs.map (subW (σ j) k) :: r.2)

theorem subsG_at (σ : ℕ → ℕ → LinT) : ∀ (ts : List Tpl) (j k : ℕ), Eqns e (subsG σ ts j k).1 k →
    ∀ i (hi : i < ts.length), ∃ k', Eqns (pullE e (σ (j + i)) k') ts[i].gates 0 ∧
      (subsG σ ts j k).2.getD i [] = ts[i].outs.map (subW (σ (j + i)) k')
  | [], _, _, _, i, hi => absurd hi (by simp)
  | T :: ts, j, k, h, i, hi => by
    simp only [subsG, Eqns.append, nlocs_sub] at h
    rcases i with _ | i
    · exact ⟨k, (eqns_sub (σ j) k T.gates 0).1 (by simpa using h.1), by simp [subsG]⟩
    · obtain ⟨k', h1, h2⟩ := subsG_at σ ts (j + 1) _ h.2 i (by simpa using hi)
      rw [show j + 1 + i = j + (i + 1) by omega] at h1 h2
      exact ⟨k', h1, by simpa [subsG] using h2⟩

/-- **The kind mux** of the sub-templates `ts`: `σ j i` is what sub-template `j` reads as its
input `i`; `so + j` is selector `j`; `nout` outputs, output `c` = `Σ_j sel_j · out_{j,c}`. -/
def kmuxT (σ : ℕ → ℕ → LinT) (so nout : ℕ) (ts : List Tpl) : Tpl :=
  let B := subsG σ ts 0 0
  ⟨B.1 ++ (List.range nout).flatMap fun c =>
      mulsG ts.length (fun j => I (so + j)) fun j => (B.2.getD j []).getD c [],
   (List.range nout).map fun c => (List.range ts.length).flatMap fun j => L (nlocs B.1 + c * ts.length + j)⟩

theorem nlocs_range_flatMap {J : ℕ} (g : ℕ → List Gate) (hg : ∀ c, nlocs (g c) = J) :
    ∀ n, nlocs ((List.range n).flatMap g) = n * J
  | 0 => by simp [nlocs]
  | n + 1 => by
    rw [List.range_succ, List.flatMap_append, nlocs_append, nlocs_range_flatMap g hg n]
    simp [hg]; ring

theorem eqns_range_flatMap {J : ℕ} (g : ℕ → List Gate) (hg : ∀ c, nlocs (g c) = J) :
    ∀ (n k : ℕ), Eqns e ((List.range n).flatMap g) k → ∀ c < n, Eqns e (g c) (k + c * J)
  | 0, _, _, c, hc => absurd hc (by omega)
  | n + 1, k, h, c, hc => by
    rw [List.range_succ, List.flatMap_append, Eqns.append] at h
    rcases Nat.lt_succ_iff_lt_or_eq.1 hc with hc | rfl
    · exact eqns_range_flatMap g hg n k h.1 c hc
    · simpa [nlocs_range_flatMap g hg] using h.2

/-- **The kind mux computes sub-template `j₀`** when the selectors are one-hot at `j₀`: its gate
equations hold at the wires it sees, and the outputs are its outputs there. -/
theorem kmuxT_ok {σ : ℕ → ℕ → LinT} {so nout : ℕ} {ts : List Tpl} {j0 : ℕ}
    (hj : j0 < ts.length) (hout : ts[j0].outs.length = nout)
    (hs : ∀ j < ts.length, e.inp (so + j) = if j = j0 then 1 else 0)
    (h : Eqns e (kmuxT σ so nout ts).gates 0) :
    ∃ k', Eqns (pullE e (σ j0) k') ts[j0].gates 0 ∧
      (kmuxT σ so nout ts).outs.map (LinT.ev e) = ts[j0].outs.map (LinT.ev (pullE e (σ j0) k')) := by
  simp only [kmuxT, Eqns.append, zero_add] at h
  obtain ⟨hB, hM⟩ := h
  obtain ⟨k', hE, hO⟩ := subsG_at σ ts 0 0 hB j0 hj
  rw [zero_add] at hE hO
  refine ⟨k', hE, ?_⟩
  apply List.ext_getElem (by simp [kmuxT, hout])
  intro c hc1 hc2
  have hc : c < nout := by simpa [kmuxT] using hc1
  have em := mulsG_eqns (eqns_range_flatMap _ (fun c => mulsG_nlocs _ _ _) nout _ hM c hc)
  simp only [kmuxT, List.getElem_map, List.getElem_range]
  rw [ev_flatMap, sum_range_list (M := F)]
  rw [Finset.sum_congr rfl fun j hjr => by rw [ev_L, em j (Finset.mem_range.1 hjr), ev_I, hs j (Finset.mem_range.1 hjr)]]
  rw [Finset.sum_eq_single j0 (fun j _ hne => by rw [if_neg hne, zero_mul])
    (fun hn => absurd (Finset.mem_range.2 hj) hn), if_pos rfl, one_mul, hO,
    List.getD_eq_getElem _ _ (by simp; omega), List.getElem_map, subW_ev]

/-! ## Blocks of inputs -/

/-- Element `i` of block `j₀` of a concatenation of blocks. -/
theorem flatten_getD {vb : List (List F)} {j0 i : ℕ} (hj : j0 < vb.length) (hi : i < vb[j0].length) :
    vb.flatten.getD (((vb.take j0).map List.length).sum + i) 0 = vb[j0].getD i 0 := by
  have hv : vb = vb.take j0 ++ vb[j0] :: vb.drop (j0 + 1) := by
    rw [← List.drop_eq_getElem_cons hj, List.take_append_drop]
  have hlen : ((vb.take j0).map List.length).sum = (vb.take j0).flatten.length := by
    rw [List.length_flatten]
  rw [hlen]
  conv_lhs => arg 1; rw [hv]
  rw [List.flatten_append, List.flatten_cons, getD_append_right, getD_append_left hi]

theorem flatten_le {vb : List (List F)} {j0 : ℕ} (hj : j0 < vb.length) :
    ((vb.take j0).map List.length).sum + vb[j0].length ≤ vb.flatten.length := by
  have hv : vb = vb.take j0 ++ vb[j0] :: vb.drop (j0 + 1) := by
    rw [← List.drop_eq_getElem_cons hj, List.take_append_drop]
  conv_rhs => rw [hv]
  simp only [List.flatten_append, List.flatten_cons, List.length_append, List.length_flatten]
  omega

theorem sum_take_map {ns : List ℕ} {vb : List (List F)} (c : ℕ) (hw : vb.map List.length = ns.map (c * ·))
    (j : ℕ) : ((vb.take j).map List.length).sum = c * (ns.take j).sum := by
  rw [List.map_take, hw, ← List.map_take, List.sum_map_mul_left, List.map_id']

theorem getElem_len {ns : List ℕ} {vb : List (List F)} {c : ℕ} (hw : vb.map List.length = ns.map (c * ·))
    {j : ℕ} (hj : j < vb.length) (hj' : j < ns.length) : vb[j].length = c * ns[j] := by
  have := congrArg (·[j]?) hw
  simpa [List.getElem?_map, List.getElem?_eq_getElem hj, List.getElem?_eq_getElem hj'] using this

/-! ## `tensorW` on a kind-muxed point -/

/-- What `tensorW`'s sub-template `j` reads: its kind's point (block `j`: `2·ns_j` inputs from
`2·Σ_{l<j} ns_l`), then `j`'s 20 bits (after every block); `0` past them. -/
def twSig (ns : List ℕ) (j i : ℕ) : LinT :=
  if i < 2 * ns.getD j 0 then I (2 * (ns.take j).sum + i)
  else if i < 2 * ns.getD j 0 + logNMax then I (2 * ns.sum + (i - 2 * ns.getD j 0)) else []

/-- **`tensorW` on a kind-muxed point** (inputs: per selector index `j` the point `r_j : AK ns_j`,
then `j`'s 20 bits, then one selector per kind). -/
def tplTensorWK (ns : List ℕ) : Tpl := kmuxT (twSig ns) (2 * ns.sum + logNMax) 2 (ns.map tplTensorW)

/-- The bits of `j` (as `tensorW`'s auxiliary import). -/
def bitsF (j : ℕ) : List F := (List.range logNMax).map fun i => if j.testBit i then 1 else 0

/-- A one-hot list (the selectors' values). -/
def oneHot (J j0 : ℕ) : List F := (List.range J).map fun j => if j = j0 then 1 else 0

/-- **`tplTensorWK` gives the selected kind's `Impl.tensorWI`.** `vb`: the kinds' point values (block
`j` of `2·ns_j` values), the selected one `r`'s encoding. -/
theorem tplTensorWK_ok (h1 : e.one = 1) {ns : List ℕ} {vb : List (List F)} {j0 jj : ℕ} {r : Array K}
    (hw : vb.map List.length = ns.map (2 * ·)) (hj : j0 < ns.length)
    (hr : vb[j0]? = some (r.toList.flatMap encK)) (hn : r.size ≤ logNMax)
    (hi : InpIs e (vb.flatten ++ bitsF jj ++ oneHot ns.length j0))
    (h : Eqns e (tplTensorWK ns).gates 0) :
    (tplTensorWK ns).outs.map (LinT.ev e) = encV (.k (Impl.tensorWI jj r)) := by
  have hl : vb.length = ns.length := by simpa using congrArg List.length hw
  have hjv : j0 < vb.length := hl ▸ hj
  have hv : vb[j0] = r.toList.flatMap encK := by simpa [List.getElem?_eq_getElem hjv] using hr
  have hsz : r.size = ns[j0] := by
    have := getElem_len hw hjv hj; rw [hv, length_flatMap_encK, Array.length_toList] at this; omega
  have hflat : vb.flatten.length = 2 * ns.sum := by
    rw [List.length_flatten, hw, List.sum_map_mul_left, List.map_id']
  obtain ⟨k', hE, hO⟩ := kmuxT_ok (σ := twSig ns) (so := 2 * ns.sum + logNMax) (nout := 2)
    (ts := ns.map tplTensorW) (j0 := j0) (by simpa using hj) (by rw [List.getElem_map]; rfl)
    (fun j hjl => by
      rw [hi, List.append_assoc, show 2 * ns.sum + logNMax + j = (vb.flatten ++ bitsF jj).length + j by
        simp [hflat, bitsF], ← List.append_assoc, getD_append_right]
      simp only [oneHot, List.length_map] at hjl ⊢
      rw [List.getD_eq_getElem _ _ (by simpa using hjl)]; simp) h
  simp only [List.getElem_map] at hE hO
  rw [← hsz] at hE hO
  unfold tplTensorWK; rw [hO]
  refine tplTensorW_ok (e := pullE e (twSig ns j0) k') h1 hn (fun i => ?_) hE
  have hn0 : ns.getD j0 0 = r.size := by rw [List.getD_eq_getElem _ _ hj, hsz]
  have hlen : (r.toList.flatMap encK).length = 2 * r.size := by
    rw [length_flatMap_encK, Array.length_toList]
  simp only [pullE, twSig, hn0]
  split_ifs with h2 h3
  · have hle := flatten_le hjv
    rw [hv, hlen] at hle
    rw [ev_I, hi, List.append_assoc, ← sum_take_map 2 hw, getD_append_left (by omega),
      flatten_getD hjv (by rw [hv, hlen]; exact h2), hv, getD_append_left (by rw [hlen]; exact h2)]
  · have hb : i - 2 * r.size < logNMax := by omega
    rw [ev_I, hi, List.append_assoc, ← hflat, getD_append_right,
      getD_append_left (by simpa [bitsF] using hb)]
    conv_rhs => rw [show i = (r.toList.flatMap encK).length + (i - 2 * r.size) by rw [hlen]; omega,
      getD_append_right]
    rfl
  · rw [ev_nil, List.getD_eq_getElem?_getD, List.getElem?_eq_none (by
      simp only [List.length_append, hlen, List.length_map, List.length_range]; omega)]; rfl

/-! ## `eqPt` on kind-muxed points -/

/-- A kind's block width for `eqPt` (its two points). -/
def epW (q : ℕ × ℕ) : ℕ := q.1 + q.2

/-- A kind's `eqPt` sub-template. -/
def epT (q : ℕ × ℕ) : Tpl := tplEqPt q.1 q.2

/-- What `eqPt`'s sub-template `j` reads: its kind's two points (block `j`, `ps_j.1 + ps_j.2`
inputs); `0` past them. -/
def epSig (ps : List (ℕ × ℕ)) (j i : ℕ) : LinT :=
  if i < (ps.getD j (0, 0)).1 + (ps.getD j (0, 0)).2 then I (((ps.map epW).take j).sum + i)
  else []

/-- **`eqPt` on kind-muxed points** (inputs: per selector index `j` the points `a_j : AF ps_j.1`
and `b_j : AF ps_j.2`, then one selector per kind). -/
def tplEqPtK (ps : List (ℕ × ℕ)) : Tpl :=
  kmuxT (epSig ps) (ps.map epW).sum 1 (ps.map epT)

/-- **`tplEqPtK` gives the selected kind's `eqPoint`.** `vb`: the kinds' point values (block `j`
of `ps_j.1 + ps_j.2` values), the selected one `a ++ b`. -/
theorem tplEqPtK_ok (h1 : e.one = 1) {ps : List (ℕ × ℕ)} {vb : List (List F)} {j0 : ℕ} {a b : Array F}
    (hw : vb.map List.length = ps.map epW) (hj : j0 < ps.length)
    (hp : ps[j0]? = some (a.size, b.size)) (hr : vb[j0]? = some (a.toList ++ b.toList))
    (hi : InpIs e (vb.flatten ++ oneHot ps.length j0))
    (h : Eqns e (tplEqPtK ps).gates 0) :
    (tplEqPtK ps).outs.map (LinT.ev e) = encV (.f (eqPoint a b)) := by
  have hl : vb.length = ps.length := by simpa using congrArg List.length hw
  have hjv : j0 < vb.length := hl ▸ hj
  have hv : vb[j0] = a.toList ++ b.toList := by simpa [List.getElem?_eq_getElem hjv] using hr
  have hpj : ps[j0] = (a.size, b.size) := by simpa [List.getElem?_eq_getElem hj] using hp
  have hflat : vb.flatten.length = (ps.map epW).sum := by
    rw [List.length_flatten, hw]
  obtain ⟨k', hE, hO⟩ := kmuxT_ok (σ := epSig ps) (so := (ps.map epW).sum) (nout := 1)
    (ts := ps.map epT) (j0 := j0) (by simpa using hj) (by rw [List.getElem_map]; rfl)
    (fun j hjl => by
      rw [hi, ← hflat, getD_append_right]
      simp only [oneHot, List.length_map] at hjl ⊢
      rw [List.getD_eq_getElem _ _ (by simpa using hjl)]; simp) h
  simp only [List.getElem_map, hpj, epT] at hE hO
  unfold tplEqPtK; rw [hO]
  refine tplEqPt_ok (e := pullE e (epSig ps j0) k') h1 (fun i => ?_) hE
  have hn0 : ps.getD j0 (0, 0) = (a.size, b.size) := by rw [List.getD_eq_getElem _ _ hj, hpj]
  have hlen : (a.toList ++ b.toList).length = a.size + b.size := by simp
  simp only [pullE, epSig, hn0]
  split_ifs with h2
  · have hoff : ((vb.take j0).map List.length).sum = ((ps.map epW).take j0).sum := by
      rw [List.map_take, hw]
    have hle := flatten_le hjv
    rw [hv, hlen] at hle
    rw [ev_I, hi, ← hoff, getD_append_left (by omega), flatten_getD hjv (by rw [hv, hlen]; exact h2), hv]
  · rw [ev_nil, List.getD_eq_getElem?_getD, List.getElem?_eq_none (by simp; omega)]; rfl

/-! ## Controls -/

/-- (+) Three kinds' sub-templates: `5·Σ n` locals, plus `2·3` mux products. -/
theorem tplTensorWK_nlocs (a b c : ℕ) :
    nlocs (tplTensorWK [a, b, c]).gates = 5 * (a + b + c) + 2 * 3 := by
  simp only [tplTensorWK, kmuxT, nlocs_append, nlocs_range_flatMap _ (fun _ => mulsG_nlocs _ _ _),
    subsG, nlocs_sub, tplTensorW_nlocs, List.map_cons, List.map_nil, List.length_cons, List.length_nil]
  simp [nlocs]; ring

/-- (+) Two outputs (a `K`); (−) `eqPt`'s mux has one. -/
theorem tplKMux_outs (ns : List ℕ) (ps : List (ℕ × ℕ)) :
    (tplTensorWK ns).outs.length = 2 ∧ (tplEqPtK ps).outs.length = 1 := ⟨by simp [tplTensorWK, kmuxT],
  by simp [tplEqPtK, kmuxT]⟩

end Tpl
end FR

end G6_FRVIRTplKMux

section G6_FRVIRTplExt

-- New for `flock-recursive` (BLUEPRINT A.11, §4.3, stage S-E3; track L-circ).

/-!
# `compileT`: the compiler with the replay templates, and `compileT_sound`

BLUEPRINT A.11. `tplExt` routes each structured op whose operands have the template's types to its
template (`tplOf`): the op's result slots are the template's output forms at the instance's cells
(`outSlots`), and the instance (key, input forms) is recorded; its rows are `Tpl.instRows`.
**`tplExt_ok`**: the extension is sound for every `impl` whose fields are `implC`'s on the
templated ops (`ImplT`): an instance's rows give the gate equations (`inst_eqns`), which give the
op's value (`tplX_ok`). So **`compileT_sound`** (`compileX_sound` at `tplExt`) has as import
hypotheses only the ops left without a template, plus the auxiliary imports (trace cells, L bits).

**The layout** (A.11's alignment): a first pass (`cb = 0`) counts each key's instances; the groups
are then laid out after the skeleton's cells and rows, each instance region `2^b` cells and `2^a`
rows (`Tpl.cbits`, `Tpl.rbits`), aligned (`mkLay`). Soundness does not depend on the layout
(overlapping regions only constrain more); the counts and the evaluator use it.
-/

namespace FR
namespace Circ
open Tpl RecursionFast

/-! ## The template table -/

/-- The node's walk template (`rowW′`, `colW` of `2^14` entries), computed once. -/
def tplWalk14 : Tpl := tplWalkG (2 ^ 14) (2 ^ 14)

/-- `walkAB`'s template at operand sizes `n`, `m` (the node's from the closed term). -/
def tplWalkOf (n m : ℕ) : Tpl := if n = 2 ^ 14 ∧ m = 2 ^ 14 then tplWalk14 else tplWalkG n m

theorem tplWalkOf_eq (n m : ℕ) : tplWalkOf n m = tplWalkG n m := by
  unfold tplWalkOf; split_ifs with h
  · obtain ⟨rfl, rfl⟩ := h; rfl
  · rfl

/-- **The templates** by key (A.11's table; keys without a template yet have none). -/
def tplOf : TKey → Tpl
  | .eqPt n m => tplEqPt n m
  | .shiftEq n m => tplShiftEq n m
  | .phiRS n => tplPhiRS n
  | .zero => tplZero
  | .targetS n => tplTargetS n
  | .slotW s n m => tplSlotW s n m
  | .maskRows n m => tplMaskRows n m
  | .eqZ => tplEqZ
  | .lagrangeS n m => tplLagrangeS n m
  | .eqTableK v => tplEqTableK v
  | .dotKF n => tplDotKF n
  | .tensorW n => tplTensorW n
  | .rowW _ => tplRowW
  | .shiftMask n m => tplShiftMaskF n m
  | .walkAB n m => tplWalkOf n m
  | .shiftSeg n m => tplShiftSeg n m
  | .maskN n m ks => tplMaskN n m ks
  | .tensorWK ns => tplTensorWK ns
  | .eqPtK ps => tplEqPtK ps
  | _ => ⟨[], []⟩

/-! ## The walk template's rows and sizes, computed once (S-E11: plan time) -/

/-- A template's cell bits from its rows, given once (`Tpl.cbits` reads them twice). -/
def cbitsOf (T : Tpl) (rows : List RowT) : ℕ :=
  Nat.size (max ((rows.map fun r => max r.a.maxLoc (max r.b.maxLoc r.c.maxLoc)).foldl max 0)
    (nlocs T.gates - 1))

theorem cbitsOf_rows (T : Tpl) : cbitsOf T T.rows = T.cbits := rfl

def tplWalk14Rows : List RowT := tplWalk14.rows
-- (S-E13: the row and cell bits from the rows above, not from rows built again)
def tplWalk14RB : ℕ := Nat.size (tplWalk14Rows.length - 1)
def tplWalk14CB : ℕ := cbitsOf tplWalk14 tplWalk14Rows
def tplWalk14NL : ℕ := nlocs tplWalk14.gates

/-- The node's walk key. -/
def isWalk14 : TKey → Bool
  | .walkAB n m => n == 2 ^ 14 && m == 2 ^ 14
  | _ => false

/-- A key's template rows (the walk's from the closed term). -/
def tRows (k : TKey) : List RowT := if isWalk14 k then tplWalk14Rows else (tplOf k).rows
/-- A key's row bits. -/
def tRbits (k : TKey) : ℕ := if isWalk14 k then tplWalk14RB else (tplOf k).rbits
/-- A key's cell bits. -/
def tCbits (k : TKey) : ℕ := if isWalk14 k then tplWalk14CB else (tplOf k).cbits
/-- A key's locals. -/
def tNlocs (k : TKey) : ℕ := if isWalk14 k then tplWalk14NL else nlocs (tplOf k).gates

theorem tplOf_walk14 {k : TKey} (h : isWalk14 k = true) : tplOf k = tplWalk14 := by
  cases k <;> simp [isWalk14] at h
  obtain ⟨rfl, rfl⟩ := h
  show tplWalkOf _ _ = _
  unfold tplWalkOf
  rw [if_pos ⟨rfl, rfl⟩]

theorem tRows_eq (k : TKey) : tRows k = (tplOf k).rows := by
  unfold tRows; split_ifs with h
  · rw [tplOf_walk14 h]; rfl
  · rfl

theorem tRbits_eq (k : TKey) : tRbits k = (tplOf k).rbits := by
  unfold tRbits; split_ifs with h
  · rw [tplOf_walk14 h, tplWalk14RB, tplWalk14Rows, Tpl.rbits]
  · rfl

/-- **A layout**: per key, the group's row base (relative to the slot), cell base and cell field
(`cW`, `cG`: the instances' cell windows). -/
abbrev TLay := List (TKey × ℕ × ℕ × ℕ)

/-- A layout entry's cell field `f` is `b` (one instance per `2^b`-cell window) or, for a **packed**
key (B2″), `w + 64·g` with `2 ≤ g`: `g` instances per `2^w`-cell window, at the stride `cS f =
2^w / g`. The window's bits. -/
def cW (f : ℕ) : ℕ := f % 64
/-- The instances per window (`1` if not packed). -/
def cG (f : ℕ) : ℕ := max 1 (f / 64)
/-- The member stride of a packed window. -/
def cS (f : ℕ) : ℕ := 2 ^ cW f / cG f

/-- The base of the `2^cW`-cell window holding instance `i` of key `k`. -/
def TLay.gb (L : TLay) (k : TKey) (i : ℕ) : ℕ :=
  match L.find? (·.1 == k) with
  | some (_, _, c, f) => c + i / cG f * 2 ^ cW f
  | none => 0

/-- Instance `i`'s offset in its window (`0` if the key is not packed). -/
def TLay.mo (L : TLay) (k : TKey) (i : ℕ) : ℕ :=
  match L.find? (·.1 == k) with
  | some (_, _, _, f) => i % cG f * cS f
  | none => 0

/-- The cell base of instance `i` of key `k` (`c + i·2^b` for an unpacked entry `(k, r, c, b)`). -/
def TLay.cb (L : TLay) (k : TKey) (i : ℕ) : ℕ := L.gb k i + L.mo k i

/-- (+) An unpacked entry places instance `i` at `c + i·2^b`; (−) a packed one (`g = 3` per `2^8`,
stride 85) does not: instance 4 is window 1's member 1. -/
theorem TLay.cb_ctl : TLay.cb [(.zero, 0, 100, 4)] .zero 3 = 148 ∧
    TLay.cb [(.zero, 0, 0, 8 + 64 * 3)] .zero 4 = 256 + 85 := by decide

/-- The context of a layout. -/
def TLay.ctx (L : TLay) : TCtx := ⟨tplOf, L.cb⟩

/-! ## The extension -/

/-- A slot's components. -/
def comps : Slot → List Lin
  | some (_, ls) => ls
  | none => []

/-- The output slots of an instance: the types `tys`, the template's outputs split by length. -/
def outSlots (one : Lin) (ins : List Lin) (cb : ℕ) : List Ty → List LinT → List Slot
  | [], _ => []
  | t :: ts, os =>
    some (t, (os.take t.len).map (instLin one ins cb)) :: outSlots one ins cb ts (os.drop t.len)

/-- A template instance's contribution: no rows of its own (they are the instance's). -/
def tplOut (tc : TCtx) (P : Params) (cs : CS) (k : TKey) (ins : List Lin) (tys : List Ty) : Out :=
  { slots := outSlots P.one ins (tc.cb k (cs.tcount k)) tys (tc.tpl k).outs, tin := some (k, ins) }

/-- **`tplExt`**: the templated ops, at their operands' types. -/
def tplExt (tc : TCtx) : Ext := fun P cs op =>
  match op with
  | .eqPt a b =>
    match cs.slot a, cs.slot b with
    | some (.af n, la), some (.af m, lb) => some (tplOut tc P cs (.eqPt n m) (la ++ lb) [.f])
    | _, _ => none
  | .shiftEq a b =>
    match cs.slot a, cs.slot b with
    | some (.af n, la), some (.af m, lb) => some (tplOut tc P cs (.shiftEq n m) (la ++ lb) [.f])
    | _, _ => none
  | .phiRS r a =>
    match cs.slot r, cs.slot a with
    | some (.af n, lr), some (.f, la) => some (tplOut tc P cs (.phiRS n) (lr ++ la) [.f])
    | _, _ => none
  | .kindFoldWeight .. => some (tplOut tc P cs .zero [] [.f])
  -- `linkWAll` (revision 3.14): an import until `tplLinkWAll` (S-E)
  | .shiftMask t r =>
    match cs.slot t, cs.slot r with
    | some (.af n, lt), some (.af m, lr) =>
      some (tplOut tc P cs (.shiftMask n m) (lt ++ lr) [.f, .f, .f])
    | _, _ => none
  -- `targetS` is the node's at a node kind (S-CN's `targetSNodeI`) and the leaf's otherwise, so
  -- the leaf template no longer serves every kind: an import until `tplTargetSNode` (S-E6)
  -- the walk as the node's own XOR DAG (revision 3.15)
  | .walkAB r c =>
    match cs.slot r, cs.slot c with
    | some (.af n, lr), some (.af m, lc) => some (tplOut tc P cs (.walkAB n m) (lr ++ lc) [.f, .f])
    | _, _ => none
  | .slotW sm t r =>
    match cs.slot t, cs.slot r with
    | some (.af n, lt), some (.af m, lr) => some (tplOut tc P cs (.slotW sm n m) (lt ++ lr) [.f])
    | _, _ => none
  | .maskRows kw rw =>
    match cs.slot kw, cs.slot rw with
    | some (.af n, lk), some (.af m, lr) => some (tplOut tc P cs (.maskRows n m) (lk ++ lr) [.af m])
    | _, _ => none
  | .eqZ l r =>
    match cs.slot l, cs.slot r with
    | some (.f, ll), some (.f, lr) => some (tplOut tc P cs .eqZ (ll ++ lr) [.af 128])
    | _, _ => none
  | .lagrangeS v l pe =>
    match cs.slot v, cs.slot l, cs.slot pe with
    | some (.af n, lv), some (.f, ll), some (.af m, lp) =>
      some (tplOut tc P cs (.lagrangeS n m) (lv ++ ll ++ lp) [.f, .f])
    | _, _, _ => none
  | .eqTableK r =>
    match cs.slot r with
    | some (.ak n, lr) => some (tplOut tc P cs (.eqTableK n) lr [.ak (2 ^ n)])
    | _ => none
  | .dotKF w col =>
    match cs.slot w with
    | some (.ak n, lw) =>
      -- the column's `n` F elements: auxiliary import cells (trace cells), in the instance's own
      -- cell region after the template's `2n` locals (S-E5: local to the instance)
      let cb := tc.cb (.dotKF n) (cs.tcount (.dotKF n))
      let cells := (List.range n).map fun b => Lin.cell (cb + 2 * n + b)
      some { tplOut tc P cs (.dotKF n) (lw ++ cells) [.k] with aux := [(cells, col, .felems n)] }
    | _ => none
  | .rowW lam rhi =>
    match cs.slot lam, cs.slot rhi with
    | some (.f, ll), some (.af n, lr) => some (tplOut tc P cs (.rowW n) (ll ++ lr) [.af (2 ^ 14)])
    | _, _ => none
  | .tensorW j r =>
    match cs.slot r with
    | some (.ak n, lr) =>
      if n ≤ logNMax then
        -- `j`'s 20 bits: auxiliary import cells (L bits) after the template's `5n` locals (S-E6)
        let cb := tc.cb (.tensorW n) (cs.tcount (.tensorW n))
        let cells := (List.range logNMax).map fun i => Lin.cell (cb + 5 * n + i)
        some { tplOut tc P cs (.tensorW n) (lr ++ cells) [.k] with aux := [(cells, j, .bits logNMax)] }
      else none
    | _ => none
  | _ => none

/-! ## Soundness -/

/-- **The implementation the templates mirror** (`implC`'s fields on the templated ops). -/
structure ImplT (impl : OpImpl) : Prop where
  shiftEq : impl.shiftEq = Impl.shiftEqI
  phiRS : impl.phiRS = Impl.phiRSI
  kfw : ∀ a b c, impl.kindFoldWeight a b c = 0
  eqZ : impl.eqZ = Impl.eqZI
  lagrangeS : impl.lagrangeS = Impl.lagrangeSI
  slotW : ∀ κ, impl.slotW κ = Impl.slotWI
  tensorW : impl.tensorW = Impl.tensorWI
  rowW : impl.rowW = Impl.rowWI
  shiftMask : impl.shiftMask = NodeI.shiftMaskI
  walkAB : impl.walkAB = Eval.walkImpl

theorem outSlots_length (one : Lin) (ins : List Lin) (cb : ℕ) :
    ∀ (tys : List Ty) (os : List LinT), (outSlots one ins cb tys os).length = tys.length
  | [], _ => rfl
  | _ :: ts, os => by simp [outSlots, outSlots_length one ins cb ts]

theorem inpIs_of {w : Asg} {one : Lin} {cb : ℕ} {ins : List Lin} {xs : List F}
    (h : ins.map (Lin.ev w) = xs) : InpIs (envOf w one ins cb) xs := fun i => getD_ev h i

/-- One output: the template's outputs are the value's encoding. -/
theorem outSlots_one {w : Asg} {one : Lin} {ins : List Lin} {cb : ℕ} {t : Ty} {os : List LinT}
    {v : Val} (hv : tyOf v = some t) (ho : os.map (LinT.ev (envOf w one ins cb)) = encV v) :
    List.Forall₂ (RepS w) (outSlots one ins cb [t] os) [v] := by
  have hl : os.length = t.len := by rw [← encV_length hv, ← ho, List.length_map]
  simp only [outSlots, List.forall₂_cons, List.Forall₂.nil, and_true, RepS, hv, true_and,
    List.take_of_length_le hl.le, List.map_map]
  rw [← ho]; exact List.map_congr_left fun l _ => by simp only [Function.comp_apply, instLin_ev]

/-- Two outputs. -/
theorem outSlots_two {w : Asg} {one : Lin} {ins : List Lin} {cb : ℕ} {t₁ t₂ : Ty} {os : List LinT}
    {v₁ v₂ : Val} (hv₁ : tyOf v₁ = some t₁) (hv₂ : tyOf v₂ = some t₂)
    (ho : os.map (LinT.ev (envOf w one ins cb)) = encV v₁ ++ encV v₂) :
    List.Forall₂ (RepS w) (outSlots one ins cb [t₁, t₂] os) [v₁, v₂] := by
  have hl := congrArg List.length ho
  rw [List.length_map, List.length_append, encV_length hv₁, encV_length hv₂] at hl
  have h1 : (os.take t₁.len).map (LinT.ev (envOf w one ins cb)) = encV v₁ := by
    rw [List.map_take, ho, List.take_left' (encV_length hv₁)]
  have h2 : (os.drop t₁.len).map (LinT.ev (envOf w one ins cb)) = encV v₂ := by
    rw [List.map_drop, ho, List.drop_left' (encV_length hv₁)]
  have := outSlots_one (one := one) (ins := ins) (cb := cb) hv₂ h2
  simp only [outSlots] at this ⊢
  refine List.Forall₂.cons ⟨hv₁, ?_⟩ this
  rw [← h1, List.map_map]; exact List.map_congr_left fun l _ => by simp only [Function.comp_apply, instLin_ev]

/-- Three outputs. -/
theorem outSlots_three {w : Asg} {one : Lin} {ins : List Lin} {cb : ℕ} {t₁ t₂ t₃ : Ty}
    {os : List LinT} {v₁ v₂ v₃ : Val} (hv₁ : tyOf v₁ = some t₁) (hv₂ : tyOf v₂ = some t₂)
    (hv₃ : tyOf v₃ = some t₃)
    (ho : os.map (LinT.ev (envOf w one ins cb)) = encV v₁ ++ encV v₂ ++ encV v₃) :
    List.Forall₂ (RepS w) (outSlots one ins cb [t₁, t₂, t₃] os) [v₁, v₂, v₃] := by
  have h1 : (os.take t₁.len).map (LinT.ev (envOf w one ins cb)) = encV v₁ := by
    rw [List.map_take, ho, List.append_assoc, List.take_left' (encV_length hv₁)]
  have h2 : (os.drop t₁.len).map (LinT.ev (envOf w one ins cb)) = encV v₂ ++ encV v₃ := by
    rw [List.map_drop, ho, List.append_assoc, List.drop_left' (encV_length hv₁)]
  have := outSlots_two (one := one) (ins := ins) (cb := cb) hv₂ hv₃ h2
  simp only [outSlots] at this ⊢
  refine List.Forall₂.cons ⟨hv₁, ?_⟩ this
  rw [← h1, List.map_map]; exact List.map_congr_left fun l _ => by simp only [Function.comp_apply, instLin_ev]

theorem eqStepL_length (l : List K) : ∀ t : List K, (l.foldl eqStepL t).length = t.length * 2 ^ l.length := by
  induction l with
  | nil => simp
  | cons x l ih => intro t; simp [ih, eqStepL, pow_succ]; ring

theorem eqTab_size (r : Array K) : (eqTab r).size = 2 ^ r.size := by
  rw [← Array.length_toList, eqTab_toList, eqStepL_length]; simp

/-- An `AK` operand. -/
theorem rep_ak {w : Asg} {n : ℕ} {ls : List Lin} {v : Val} (h : RepS w (some (.ak n, ls)) v) :
    ∃ x : Array K, v = .ak x ∧ x.size = n ∧ ls.map (Lin.ev w) = x.toList.flatMap encK := by
  obtain ⟨h1, h2⟩ := h
  rcases v with _ | _ | _ | _ | _ | _ | _ | x | _ <;> simp [tyOf] at h1
  exact ⟨x, rfl, h1, h2⟩

/-- An `AF` operand: its value is an array of that size, its forms evaluate to the elements. -/
theorem rep_af {w : Asg} {n : ℕ} {ls : List Lin} {v : Val} (h : RepS w (some (.af n, ls)) v) :
    ∃ x : Array F, v = .af x ∧ x.size = n ∧ ls.map (Lin.ev w) = x.toList := by
  obtain ⟨h1, h2⟩ := h
  rcases v with _ | _ | _ | _ | _ | _ | x | _ | _ <;> simp [tyOf] at h1
  exact ⟨x, rfl, h1, h2⟩

theorem rep_f {w : Asg} {ls : List Lin} {v : Val} (h : RepS w (some (.f, ls)) v) :
    ∃ x : F, v = .f x ∧ ls.map (Lin.ev w) = [x] := by
  obtain ⟨h1, h2⟩ := h
  rcases v with x | _ | _ | _ | _ | _ | _ | _ | _ <;> simp [tyOf] at h1
  exact ⟨x, rfl, h2⟩

/-- The slot of a register (from the invariant). -/
theorem rep_slot {w : Asg} {cs : CS} {regs : Array Val} (hI : ∀ i, RepS w (cs.slot i) (rd regs i))
    {a : ℕ} {s : Slot} (h : cs.slot a = s) : RepS w s (rd regs a) := h ▸ hI a

/-- The instance's gate equations from its rows. -/
theorem tin_eqns {tc : TCtx} {P : Params} {cs : CS} {w : Asg} (hone : P.one.ev w = 1) {k : TKey}
    {ins : List Lin} {tys : List Ty}
    (h : ∀ t ∈ (tplOut tc P cs k ins tys).tin, ∀ r ∈ instRows tc P.one (t.1, cs.tcount t.1, t.2),
      r.Holds w) :
    Eqns (envOf w P.one ins (tc.cb k (cs.tcount k))) (tc.tpl k).gates 0 :=
  inst_eqns hone ins _ (tc.tpl k) fun r hr =>
    h (k, ins) rfl _ (List.mem_map.2 ⟨r, hr, rfl⟩)

/-- **`tplExt` is sound** (A.11's `tplX_sound` for every templated op). -/
theorem tplExt_ok {impl : OpImpl} (hT : ImplT impl) (L : TLay) : ExtOk impl L.ctx (tplExt L.ctx) := by
  intro P cs op o hX
  cases op <;> simp only [tplExt] at hX
  case eqPt a b =>
    split at hX <;> simp only [Option.some.injEq, reduceCtorEq] at hX; subst hX
    rename_i n la m lb ha hb
    refine ⟨rfl, fun κ inp w regs hP hI => ⟨fun q => by simp [evalOp], fun _ ht _ vs ok he => ?_⟩⟩
    simp only [evalOp, Res.vals.injEq] at he; obtain ⟨rfl, rfl⟩ := he
    refine ⟨fun _ => ?_, fun _ => rfl⟩
    obtain ⟨x, hx, rfl, hxl⟩ := rep_af (rep_slot hI ha)
    obtain ⟨y, hy, rfl, hyl⟩ := rep_af (rep_slot hI hb)
    rw [hx, hy]
    exact outSlots_one rfl (tplEqPt_ok hP.1 (inpIs_of (by simp [hxl, hyl])) (tin_eqns hP.1 ht))
  case shiftEq a b =>
    split at hX <;> simp only [Option.some.injEq, reduceCtorEq] at hX; subst hX
    rename_i n la m lb ha hb
    refine ⟨rfl, fun κ inp w regs hP hI => ⟨fun q => by simp [evalOp], fun _ ht _ vs ok he => ?_⟩⟩
    simp only [evalOp, Res.vals.injEq] at he; obtain ⟨rfl, rfl⟩ := he
    refine ⟨fun _ => ?_, fun _ => rfl⟩
    obtain ⟨x, hx, rfl, hxl⟩ := rep_af (rep_slot hI ha)
    obtain ⟨y, hy, rfl, hyl⟩ := rep_af (rep_slot hI hb)
    rw [hx, hy, hT.shiftEq]
    exact outSlots_one rfl (tplShiftEq_ok hP.1 (inpIs_of (by simp [hxl, hyl])) (tin_eqns hP.1 ht))
  case phiRS r a =>
    split at hX <;> simp only [Option.some.injEq, reduceCtorEq] at hX; subst hX
    rename_i n lr la hr ha
    refine ⟨rfl, fun κ inp w regs hP hI => ⟨fun q => by simp [evalOp], fun _ ht _ vs ok he => ?_⟩⟩
    simp only [evalOp, Res.vals.injEq] at he; obtain ⟨rfl, rfl⟩ := he
    refine ⟨fun _ => ?_, fun _ => rfl⟩
    obtain ⟨x, hx, rfl, hxl⟩ := rep_af (rep_slot hI hr)
    obtain ⟨y, hy, hyl⟩ := rep_f (rep_slot hI ha)
    rw [hx, hy, hT.phiRS]
    exact outSlots_one rfl (tplPhiRS_ok (inpIs_of (by simp [hxl, hyl, Val.toF])) (tin_eqns hP.1 ht))
  case slotW sm t r =>
    split at hX <;> simp only [Option.some.injEq, reduceCtorEq] at hX; subst hX
    rename_i n lt m lr ht' hr
    refine ⟨rfl, fun κ inp w regs hP hI => ⟨fun q => by simp [evalOp], fun _ ht _ vs ok he => ?_⟩⟩
    simp only [evalOp, Res.vals.injEq] at he; obtain ⟨rfl, rfl⟩ := he
    refine ⟨fun _ => ?_, fun _ => rfl⟩
    obtain ⟨x, hx, rfl, hxl⟩ := rep_af (rep_slot hI ht')
    obtain ⟨y, hy, rfl, hyl⟩ := rep_af (rep_slot hI hr)
    rw [hx, hy, hT.slotW]
    exact outSlots_one rfl (tplSlotW_ok hP.1 sm (inpIs_of (by simp [hxl, hyl])) (tin_eqns hP.1 ht))
  case maskRows kw rw =>
    split at hX <;> simp only [Option.some.injEq, reduceCtorEq] at hX; subst hX
    rename_i n lk m lr hk hr
    refine ⟨rfl, fun κ inp w regs hP hI => ⟨fun q => by simp [evalOp], fun _ ht _ vs ok he => ?_⟩⟩
    simp only [evalOp, Res.vals.injEq] at he; obtain ⟨rfl, rfl⟩ := he
    refine ⟨fun _ => ?_, fun _ => rfl⟩
    obtain ⟨x, hx, rfl, hxl⟩ := rep_af (rep_slot hI hk)
    obtain ⟨y, hy, rfl, hyl⟩ := rep_af (rep_slot hI hr)
    rw [hx, hy]
    exact outSlots_one (by simp [tyOf, maskRows, Val.toAF])
      (tplMaskRows_ok (inpIs_of (by simp [hxl, hyl])) (tin_eqns hP.1 ht))
  case eqZ l r =>
    split at hX <;> simp only [Option.some.injEq, reduceCtorEq] at hX; subst hX
    rename_i ll lr hl hr
    refine ⟨rfl, fun κ inp w regs hP hI => ⟨fun q => by simp [evalOp], fun _ ht _ vs ok he => ?_⟩⟩
    simp only [evalOp, Res.vals.injEq] at he; obtain ⟨rfl, rfl⟩ := he
    refine ⟨fun _ => ?_, fun _ => rfl⟩
    obtain ⟨x, hx, hxl⟩ := rep_f (rep_slot hI hl)
    obtain ⟨y, hy, hyl⟩ := rep_f (rep_slot hI hr)
    rw [hx, hy, hT.eqZ]
    exact outSlots_one (by simp [tyOf, eqZI_size])
      (tplEqZ_ok hP.1 (inpIs_of (by simp [hxl, hyl, Val.toF])) (tin_eqns hP.1 ht))
  case lagrangeS v l pe =>
    split at hX <;> simp only [Option.some.injEq, reduceCtorEq] at hX; subst hX
    rename_i n lv ll m lp hv hl hp
    refine ⟨rfl, fun κ inp w regs hP hI => ⟨fun q => by simp [evalOp], fun _ ht _ vs ok he => ?_⟩⟩
    simp only [evalOp, Res.vals.injEq] at he; obtain ⟨rfl, rfl⟩ := he
    refine ⟨fun _ => ?_, fun _ => rfl⟩
    obtain ⟨x, hx, rfl, hxl⟩ := rep_af (rep_slot hI hv)
    obtain ⟨y, hy, hyl⟩ := rep_f (rep_slot hI hl)
    obtain ⟨z, hz, rfl, hzl⟩ := rep_af (rep_slot hI hp)
    rw [hx, hy, hz, hT.lagrangeS]
    exact outSlots_two rfl rfl (tplLagrangeS_ok hP.1
      (inpIs_of (by simp [hxl, hyl, hzl, Val.toF, Val.toAF])) (tin_eqns hP.1 ht))
  case eqTableK r =>
    split at hX <;> simp only [Option.some.injEq, reduceCtorEq] at hX; subst hX
    rename_i n lr hr
    refine ⟨rfl, fun κ inp w regs hP hI => ⟨fun q => by simp [evalOp], fun _ ht _ vs ok he => ?_⟩⟩
    simp only [evalOp, Res.vals.injEq] at he; obtain ⟨rfl, rfl⟩ := he
    refine ⟨fun _ => ?_, fun _ => rfl⟩
    obtain ⟨x, hx, rfl, hxl⟩ := rep_ak (rep_slot hI hr)
    rw [hx]
    exact outSlots_one (by simp [tyOf, Val.toAK, eqTab_size])
      (tplEqTableK_ok hP.1 (inpIs_of hxl) (tin_eqns hP.1 ht))
  case dotKF w col =>
    split at hX <;> simp only [Option.some.injEq, reduceCtorEq] at hX; subst hX
    rename_i n lw hw
    refine ⟨rfl, fun κ inp ww regs hP hI => ⟨fun q => by simp [evalOp], fun _ ht hx vs ok he => ?_⟩⟩
    simp only [evalOp, Res.vals.injEq] at he; obtain ⟨rfl, rfl⟩ := he
    refine ⟨fun _ => ?_, fun _ => rfl⟩
    obtain ⟨x, hx', rfl, hxl⟩ := rep_ak (rep_slot hI hw)
    have hc := hx _ (List.mem_singleton_self _)
    simp only [Tpl.AuxK.val] at hc
    rw [hx', dotKFF_eq]
    exact outSlots_one rfl (tplDotKF_ok rfl (inpIs_of (by rw [List.map_append, hxl, hc]; rfl))
      (tin_eqns (tc := L.ctx) (k := .dotKF x.size) (tys := [.k]) hP.1 ht))
  case rowW lam rhi =>
    split at hX <;> simp only [Option.some.injEq, reduceCtorEq] at hX; subst hX
    rename_i ll n lr hl hr
    refine ⟨rfl, fun κ inp w regs hP hI => ⟨fun q => by simp [evalOp], fun _ ht _ vs ok he => ?_⟩⟩
    simp only [evalOp, Res.vals.injEq] at he; obtain ⟨rfl, rfl⟩ := he
    refine ⟨fun _ => ?_, fun _ => rfl⟩
    obtain ⟨x, hx, hxl⟩ := rep_f (rep_slot hI hl)
    obtain ⟨y, hy, rfl, hyl⟩ := rep_af (rep_slot hI hr)
    rw [hx, hy, hT.rowW]
    exact outSlots_one (by simp [tyOf, rowWI_size])
      (tplRowW_ok hP.1 (inpIs_of (by simp [hxl, hyl, Val.toF, Val.toAF])) (tin_eqns hP.1 ht))
  case shiftMask t r =>
    split at hX <;> simp only [Option.some.injEq, reduceCtorEq] at hX; subst hX
    rename_i n lt m lr ht' hr
    refine ⟨rfl, fun κ inp w regs hP hI => ⟨fun q => by simp [evalOp], fun _ ht _ vs ok he => ?_⟩⟩
    simp only [evalOp, Res.vals.injEq] at he; obtain ⟨rfl, rfl⟩ := he
    refine ⟨fun _ => ?_, fun _ => rfl⟩
    obtain ⟨x, hx, rfl, hxl⟩ := rep_af (rep_slot hI ht')
    obtain ⟨y, hy, rfl, hyl⟩ := rep_af (rep_slot hI hr)
    rw [hx, hy, hT.shiftMask]
    exact outSlots_three rfl rfl rfl
      (tplShiftMask_ok (inpIs_of (by simp [hxl, hyl])) hP.1 (tin_eqns hP.1 ht))
  case walkAB r c =>
    split at hX <;> simp only [Option.some.injEq, reduceCtorEq] at hX; subst hX
    rename_i n lr m lc hr hc
    refine ⟨rfl, fun κ inp w regs hP hI => ⟨fun q => by simp [evalOp], fun _ ht _ vs ok he => ?_⟩⟩
    simp only [evalOp, Res.vals.injEq] at he; obtain ⟨rfl, rfl⟩ := he
    refine ⟨fun _ => ?_, fun _ => rfl⟩
    obtain ⟨x, hx, rfl, hxl⟩ := rep_af (rep_slot hI hr)
    obtain ⟨y, hy, rfl, hyl⟩ := rep_af (rep_slot hI hc)
    rw [hx, hy, hT.walkAB]
    have he := tin_eqns hP.1 ht
    have hg : (L.ctx.tpl (.walkAB x.size y.size)) = tplWalkG x.size y.size := by
      simp only [TLay.ctx, tplOf, tplWalkOf_eq]
    rw [hg] at he
    have ho := tplWalkAB_ok (inpIs_of (by simp [hxl, hyl])) he
    rw [← hg] at ho
    exact outSlots_two rfl rfl ho
  case tensorW j r =>
    split at hX
    · rename_i n lr hr
      split_ifs at hX with hn
      · simp only [Option.some.injEq] at hX; subst hX
        refine ⟨rfl, fun κ inp ww regs hP hI => ⟨fun q => by simp [evalOp], fun _ ht hx vs ok he => ?_⟩⟩
        simp only [evalOp, Res.vals.injEq] at he; obtain ⟨rfl, rfl⟩ := he
        refine ⟨fun _ => ?_, fun _ => rfl⟩
        obtain ⟨x, hx', rfl, hxl⟩ := rep_ak (rep_slot hI hr)
        have hc := hx _ (List.mem_singleton_self _)
        simp only [Tpl.AuxK.val] at hc
        rw [hx', hT.tensorW]
        exact outSlots_one rfl (tplTensorW_ok hP.1 hn
          (inpIs_of (by rw [List.map_append, hxl, hc]))
          (tin_eqns (tc := L.ctx) (k := .tensorW x.size) (tys := [.k]) hP.1 ht))
    · simp at hX
  all_goals first
    | (simp at hX; done)
    | skip
  case kindFoldWeight r b ρ =>
    obtain rfl := Option.some.inj hX
    refine ⟨rfl, fun κ inp w regs hP hI => ⟨fun q => by simp [evalOp], fun _ _ _ vs ok he => ?_⟩⟩
    simp only [evalOp, Res.vals.injEq] at he; obtain ⟨rfl, rfl⟩ := he
    rw [hT.kfw]
    exact ⟨fun _ => outSlots_one rfl tplZero_ok, fun _ => rfl⟩

/-! ## `compileT` and `compileT_sound` -/

/-- **`compileT`**: `compile` with the templates at layout `L`. -/
def compileT (L : TLay) (P : Params) (base : ℕ) (ops : List Op) : CS :=
  compileX (tplExt L.ctx) P base ops

/-- **`compileT_sound`** (A.11): with `ImplT`, the template instances' rows and the auxiliary
imports, the import hypotheses left are those of the ops without a template (and the trace / L /
public imports of the skeleton): the run accepts and every tracked register is represented. -/
theorem compileT_sound {impl : OpImpl} {κ : Kind} {inp : Input} {ops : List Op} {tr tr' : Trace}
    {s : St} {w : Asg} {P : Params} (hT : ImplT impl) (L : TLay) (base : ℕ) (hP : SelOk w P κ)
    (he : exec impl κ inp ops St.init tr = some (s, tr'))
    (hr : ∀ r ∈ (compileT L P base ops).rows, r.Holds w)
    (ht : ∀ r ∈ (compileT L P base ops).tplRows L.ctx P.one, r.Holds w)
    (hx : ∀ a ∈ (compileT L P base ops).aux,
      a.1.1.map (Lin.ev w) = a.1.2.2.val (rd (s.regs.extract 0 a.2) a.1.2.1))
    (hi : ∀ i ∈ (compileT L P base ops).imp,
      RepS w ((compileT L P base ops).slot i) (rd s.regs i))
    (hf : ∀ p ∈ (compileT L P base ops).fors, flagOf impl κ inp (s.regs.extract 0 p.2) p.1 = true) :
    s.ok = true ∧ ∀ i, RepS w ((compileT L P base ops).slot i) (rd s.regs i) :=
  compileX_sound (tplExt_ok hT L) base hP he hr ht hx hi hf

/-! ## The layout -/

/-- The keys in order of first appearance, with their instance counts. -/
def keyCounts (tins : List (TKey × ℕ × List Lin)) : List (TKey × ℕ) :=
  tins.reverse.foldl (fun acc t => if acc.any (·.1 == t.1) then
    acc.map fun p => if p.1 == t.1 then (p.1, p.2 + 1) else p else acc ++ [(t.1, 1)]) []

/-- `tplTensorWK ns`'s locals (`5·Σ ns` for the kinds' sub-templates, `2·|ns|` mux products;
`tplTensorWK_nlocs`): `j`'s 20 bits are read into the cells after them. -/
def twkLocs (ns : List ℕ) : ℕ := 5 * ns.sum + 2 * ns.length

/-- A key's cell region bits: its template's locals and, for `dotKF`, the column cells after them. -/
def cregion (k : TKey) : ℕ :=
  match k with
  | .dotKF n => max (tplOf k).cbits (Nat.size (3 * n + 1))
  | .tensorW n => max (tplOf k).cbits (Nat.size (5 * n + logNMax))
  | .tensorWK ns => max (tplOf k).cbits (Nat.size (twkLocs ns + logNMax))
  | _ => tCbits k

/-- The cells after a template's locals that its extension writes (auxiliary import cells:
`dotKF`'s column, `tensorW`'s and `tensorWK`'s bits; `cregion`'s operands). -/
def auxEnd : TKey → ℕ
  | .dotKF n => 3 * n + 1
  | .tensorW n => 5 * n + logNMax
  | .tensorWK ns => twkLocs ns + logNMax
  | _ => 0

/-- The largest local template rows read. -/
def rowsMaxLoc (rows : List RowT) : ℕ :=
  (rows.map fun r => max r.a.maxLoc (max r.b.maxLoc r.c.maxLoc)).foldl max 0

/-- **The cells an instance uses**, from its template's rows and locals: every local a row reads,
every local the template writes, its auxiliary cells. -/
def usedN (k : TKey) (rows : List RowT) (nl : ℕ) : ℕ := max (rowsMaxLoc rows + 1) (max nl (auxEnd k))

/-- A key's used cells. -/
def cUsed (k : TKey) : ℕ := usedN k (tRows k) (tNlocs k)

/-- The keys packed (B2″, PK-M3: the eight keys whose window padding frees the arenas' cells). -/
def pkKey : TKey → Bool
  | .dotKF n => n == 64 || n == 16
  | .phiRS n => n == 7
  | .tensorW n => n == 7
  | .tensorWK _ => true
  | _ => false

/-- The most instances a packed window holds (B2″): each member is a key of its own, whose
preparation (`kprep3`, ≈ 2.7 µs a template row per evaluation) every evaluation pays; at 16 the
eight keys' members cost ≈ +35 ms of `kp` (`logs/B2pp/plan4t-1.log`). -/
def packMax : ℕ := 4

/-- **The packing policy** (B2″, B2′'s option (b′); performance only, soundness does not depend
on the layout): for `u` used cells in a `2^cr` window, the window bits `w ∈ (cr, cr + 4]`, `w ≤ 13`,
holding `g = 2^w / u` instances (`2 ≤ g ≤ packMax`) at the fewest cells an instance (`2^w / g`), if
fewer than `2^cr`; ties take the smaller `w`. The stride `2^w / g` is at least `u`. -/
def packN (cr u : ℕ) : Option (ℕ × ℕ) :=
  (List.range 4).foldl (fun (best : Option (ℕ × ℕ)) d =>
    let w := cr + 1 + d
    let g := 2 ^ w / max u 1
    if w ≤ 13 ∧ 2 ≤ g ∧ g ≤ packMax ∧ 2 ^ w / g < 2 ^ cr then
      match best with
      | some (w', g') => if 2 ^ w * g' < 2 ^ w' * g then some (w, g) else best
      | none => some (w, g)
    else best) none

/-- A key's packing from its cell region and used cells. -/
def packOfN (k : TKey) (cr u : ℕ) : Option (ℕ × ℕ) := if pkKey k then packN cr u else none

/-- **A key's packing** `(w, g)`. -/
def packOf (k : TKey) : Option (ℕ × ℕ) := packOfN k (cregion k) (cUsed k)

/-- (+) `phiRS 7`'s 134 cells take three per `2^9` (170 each, from 256), a 306-cell `tensorWK`
three per `2^10`; (−) `dotKF 64`'s 193 gain nothing within `packMax` (two per `2^9`), nor 251
cells in `2^8`, nor 16 in `2^4`. -/
theorem packN_ctl : packN 8 134 = some (9, 3) ∧ packN 8 193 = none ∧
    packN 9 306 = some (10, 3) ∧ packN 8 251 = none ∧ packN 4 16 = none := by decide

/-- The walk's blocks (`G` gadgets at a `2^gBits` stride): its rows and cells are aligned to the
block, and the next group's cells start after its last local (S-E10). -/
def isWalk : TKey → Bool
  | .walkAB .. => true
  | _ => false

/-- The rows a split must save per instance (B0: below it, the extra piece costs `evalM` more than
the rows are worth; `tensorW 7`'s 64 → 36 saves 28 and is not split). -/
def splitMin : ℕ := 32

/-- **The split policy** (B0, generalising S-E11's `phiRS` split, changes 22 (b)): a template of
`nr` rows with `2^(r−1) < nr ≤ 2^r` whose rows past the head `2^a` (`a = r − 1`) fit `2^b` rows with
`b < a` is laid out as a head block and a tail block, so that an instance takes `2^a + 2^b` rows of
the layout instead of its aligned stride `2^r`, if that saves at least `splitMin` rows an instance
(a split instance is one more piece for the evaluator, ≈ 1.5–2 µs of `evalM`: B0's `piececost`).
Templates of at most 16 rows, and of more than `2^12` rows (evaluated in 64-row chunks), are not
split. The policy reads only the template's row count: it is generic in the program (performance
only; soundness does not depend on the layout). -/
def splitN (nr : ℕ) : Option (ℕ × ℕ) :=
  let r := Nat.size (nr - 1)
  if 4 < r ∧ r ≤ 12 then
    let b := Nat.size (nr - 2 ^ (r - 1) - 1)
    if b < r - 1 ∧ 2 ^ (r - 1) + 2 ^ b + splitMin ≤ 2 ^ r then some (r - 1, b) else none
  else none

/-- A key's split from its row count `nr` (the walk is laid out in blocks, never split). -/
def splitOfN (k : TKey) (nr : ℕ) : Option (ℕ × ℕ) := if isWalk k then none else splitN nr

/-- **A split template**: `splitN` of its row count (`phiRS 7`: 134 = 128 + 6 rows, (7, 3);
`tensorWK [19, 18, 19]`: 286 = 256 + 30, (8, 5)). -/
def splitOf (k : TKey) : Option (ℕ × ℕ) := splitOfN k (tRows k).length

/-- **The row of a split instance**: groups of `g = 2^(a−b)` instances; a group's `g` tails first
(`g · 2^b = 2^a` rows), then its `g` heads (`(g + 1)·2^a` rows a group); instance `i`'s row `j`.
The tails come first so that a last group of `m < g` instances takes `(m + 1)·2^a` rows
(`splitEnd`): a key with one instance takes `2^(a+1)`, its unsplit stride. -/
def splitRow (a b i j : ℕ) : ℕ :=
  let g := 2 ^ (a - b)
  i / g * ((g + 1) * 2 ^ a) + if j < 2 ^ a then 2 ^ a + i % g * 2 ^ a + j else i % g * 2 ^ b + (j - 2 ^ a)

/-- The rows a split key's `n` instances take: the full groups, then the last group's tail block and
heads. -/
def splitEnd (a b n : ℕ) : ℕ :=
  let g := 2 ^ (a - b)
  n / g * ((g + 1) * 2 ^ a) + if n % g = 0 then 0 else (n % g + 1) * 2 ^ a

/-- (+) The policy splits `phiRS 7`'s 134 rows as (7, 3), a 72-row template as (6, 3) and the
`tensorWK` rows 286 and 151 as (8, 5) and (7, 5); instance 0's tail is the group's first row, its
head follows the group's 16 tails; instance 16 starts the next group of `17 · 128` rows; 512
instances take `32 · 17 · 128` rows. -/
theorem splitRow_phi : splitN 134 = some (7, 3) ∧ splitN 72 = some (6, 3) ∧ splitN 286 = some (8, 5) ∧
    splitN 151 = some (7, 5) ∧ splitRow 7 3 0 128 = 0 ∧ splitRow 7 3 0 0 = 128 ∧
    splitRow 7 3 15 133 = 125 ∧ splitRow 7 3 16 0 = 2304 ∧ splitEnd 7 3 512 = 69632 := by
  refine ⟨by decide, by decide, by decide, by decide, ?_, ?_, ?_, ?_, ?_⟩ <;> norm_num [splitRow, splitEnd]

/-- (−) Rows that fill their stride, whose tail does not fit half the head (`241 = 128 + 113`), or
whose split saves fewer than `splitMin` rows (`tensorW 7`'s 35: 28) are not split, nor a template
of more than `2^12` rows, nor the walk. -/
theorem splitOf_walk (n m : ℕ) : splitOf (.walkAB n m) = none ∧ splitN 128 = none ∧ splitN 241 = none ∧
    splitN 35 = none ∧ splitN 16 = none ∧ splitN 4200 = none := by
  refine ⟨rfl, by decide, by decide, by decide, by decide, by decide⟩

/-- **The layout** from the counts: groups after the skeleton's rows `r0` and cells `c0`, each
aligned to its instance size. -/
def mkLay (r0 c0 : ℕ) : List (TKey × ℕ) → TLay
  | [] => []
  | (k, n) :: ks =>
    -- the template's rows once (S-E11: plan time); `Nat.size (nr − 1)` is `Tpl.rbits`
    let nr := (tRows k).length; let rbk := Nat.size (nr - 1); let cr := cregion k
    -- a template of more than `2^12` rows is evaluated in 64-row chunks (`FRVIRTplPlan.tinPP`),
    -- so its rows need only 64-row alignment (S-E6); the walk's in `2^gBits` blocks (S-E10)
    let rb := alignUp r0 (match splitOfN k nr with
      | some (a, _) => a
      | none => if isWalk k then gBits else if 12 < rbk then 6 else rbk)
    let cb := alignUp c0 (if isWalk k then gBits else cr)
    -- the next group starts after the last instance's rows, not its whole aligned region (S-E6);
    -- a split template's instances take `(g + 1)·2^a` rows per group of `g` (S-E11, `splitEnd`)
    let re := match splitOfN k nr with
      | some (a, b) => rb + splitEnd a b n
      | none => rb + (n - 1) * 2 ^ rbk + nr
    (k, rb, cb, cr) :: mkLay re
      (if isWalk k then cb + (n - 1) * 2 ^ cr + tNlocs k else cb + n * 2 ^ cr) ks

/-- **The two-pass compile**: count with the zero layout, lay the groups out, compile again. -/
def layOf (P : Params) (base : ℕ) (ops : List Op) : TLay :=
  let cs := compileT [] P base ops
  mkLay cs.nrows cs.next (keyCounts cs.tins)

end Circ
end FR

end G6_FRVIRTplExt

section G6_FRVIRTplEval

-- New for `flock-recursive` (BLUEPRINT A.11, §4.4, stage S-E3; track L-circ).

/-!
# The templated matrix MLEs (`evalM`, `evalMK`, `evalL`) and `tpl_mle`

BLUEPRINT §4.4, A.11. Region M's rows are indexed: slot `σ`'s skeleton row `j` at `σ·2^20 + j`, and
instance `inst` of template `X` at `σ·2^20 + rowBase_X + inst·2^a + j`, its local `k` at cell
`cellBase_X + inst·2^b + k` (`slotIRows`). The MLE of a matrix `Σ_{x,y} eq(τ,x) eq(σ,y) M[x][y]`
is the sparse sum over its entries (`FRVIREval.sparse_eq`); here the sparse sum over an instance's
entries is put in **closed form** (`tpl_mle`):

  `eq(τ_hi, ⌊rowBase/2^a⌋ + inst) · ( eq(σ_hi, ⌊cellBase/2^b⌋ + inst) · LOC + ONE · E(one)
     + Σ_{(i,u) ∈ IT} u · E(ins_i) )`

where `LOC = Σ_{(j, loc k, c)} eq(τ_lo, j) c eq(σ_lo, k)`, `ONE`, `IT` are computed **once per
template** (A.11's local class), and `E(ℓ) = Σ_{(cell, c) ∈ ℓ} c eq(σ, cell)` reads the instance's
input forms (the shared and irregular classes). The skeleton's rows stay sparse. Everything is
over a commutative ring `R` with the coefficients mapped by `ι : F →+* R`: `R = F` is `evalM`,
`R = K` (`τ` mapped) is `evalMK`.
-/

namespace FR
namespace TEval
open Circ Tpl Finset

variable {R : Type*} [CommRing R] (ι : F →+* R)

/-! ## `eq` at an index -/

/-- `eq(t, x)` over the first `n` coordinates of `t`. -/
def eqN (n : ℕ) (t : ℕ → R) (x : ℕ) : R := ∏ l ∈ range n, if x.testBit l then t l else 1 - t l

/-- `eq(t, x)` on the cube, `0` off it (the sparse sum's guard). -/
def gN (n : ℕ) (t : ℕ → R) (x : ℕ) : R := if x < 2 ^ n then eqN n t x else 0

/-- **The split**: `eq(t, H·2^A + j) = eq(t_lo, j) · eq(t_hi, H)`. -/
theorem eqN_split {A n : ℕ} (hA : A ≤ n) (t : ℕ → R) (H : ℕ) {j : ℕ} (hj : j < 2 ^ A) :
    eqN n t (2 ^ A * H + j) = eqN A t j * eqN (n - A) (fun l => t (A + l)) H := by
  unfold eqN
  rw [show n = A + (n - A) by omega, Finset.prod_range_add, show A + (n - A) - A = n - A by omega]
  congr 1
  · refine Finset.prod_congr rfl fun l hl => ?_
    simp only [Nat.testBit_two_pow_mul_add _ hj, Finset.mem_range.1 hl, if_true]
  · refine Finset.prod_congr rfl fun l _ => ?_
    simp only [Nat.testBit_two_pow_mul_add _ hj, show ¬ A + l < A by omega, if_false,
      Nat.add_sub_cancel_left]

theorem gN_split {A n : ℕ} (hA : A ≤ n) (t : ℕ → R) (H : ℕ) {j : ℕ} (hj : j < 2 ^ A) :
    gN n t (2 ^ A * H + j) = eqN A t j * gN (n - A) (fun l => t (A + l)) H := by
  unfold gN
  have : 2 ^ A * H + j < 2 ^ n ↔ H < 2 ^ (n - A) := by
    rw [show 2 ^ n = 2 ^ A * 2 ^ (n - A) by rw [← pow_add]; congr 1; omega]
    constructor
    · intro h; by_contra h'; push_neg at h'
      have := Nat.mul_le_mul_left (2 ^ A) h'; omega
    · intro h; have := Nat.mul_le_mul_left (2 ^ A) (Nat.succ_le_of_lt h); rw [Nat.mul_succ] at this; omega
  by_cases h : H < 2 ^ (n - A)
  · rw [if_pos (this.2 h), if_pos h, eqN_split hA t H hj]
  · rw [if_neg (fun h' => h (this.1 h')), if_neg h, mul_zero]

/-! ## Matrices, forms, rows -/

/-- The three matrices. -/
inductive Mat where
  | a | b | c

def Mat.r : Mat → Row → Lin
  | .a, r => r.a | .b, r => r.b | .c, r => r.c

def Mat.t : Mat → RowT → LinT
  | .a, r => r.a | .b, r => r.b | .c, r => r.c

theorem Mat.r_inst (s : Mat) (one : Lin) (ins : List Lin) (cb : ℕ) (r : RowT) :
    s.r (instRow one ins cb r) = instLin one ins cb (s.t r) := by cases s <;> rfl

/-- `Σ_{(cell, c)} ι c · eq(σ, cell)`. -/
def linE (m : ℕ) (σ : ℕ → R) (l : Lin) : R := (l.map fun t => ι t.2 * gN m σ t.1).sum

/-- **The sparse value of indexed rows** (the specification's sparse sum, `rowsVal_eq`). -/
def rowsVal (s : Mat) (n m : ℕ) (τ σ : ℕ → R) (rows : List (ℕ × Row)) : R :=
  (rows.map fun p => gN n τ p.1 * linE ι m σ (s.r p.2)).sum

/-- An instantiated form's value: wire by wire. -/
def wireE (m : ℕ) (σ : ℕ → R) (one : Lin) (ins : List Lin) (cb : ℕ) : Wire → R
  | .one => linE ι m σ one
  | .inp i => linE ι m σ (ins.getD i [])
  | .loc k => gN m σ (cb + k)

theorem linE_smul (m : ℕ) (σ : ℕ → R) (c : F) (l : Lin) :
    linE ι m σ (l.smul c) = ι c * linE ι m σ l := by
  simp only [linE, Lin.smul, List.map_map, Function.comp_def, map_mul, mul_assoc, List.sum_map_mul_left]

theorem linE_instLin (m : ℕ) (σ : ℕ → R) (one : Lin) (ins : List Lin) (cb : ℕ) (l : LinT) :
    linE ι m σ (instLin one ins cb l) = (l.map fun t => ι t.2 * wireE ι m σ one ins cb t.1).sum := by
  induction l with
  | nil => rfl
  | cons t l ih =>
    obtain ⟨w, c⟩ := t
    have e : instLin one ins cb ((w, c) :: l) = (match w with
      | .one => one.smul c | .inp i => (ins.getD i []).smul c | .loc k => [(cb + k, c)]) ++
        instLin one ins cb l := rfl
    rw [e, linE, List.map_append, List.sum_append, ← linE, ← linE, ih, List.map_cons, List.sum_cons]
    congr 1
    cases w with
    | one => exact linE_smul ι m σ c one
    | inp i => exact linE_smul ι m σ c _
    | loc k => simp [linE, wireE]

/-! ## One instance in closed form (`tpl_mle`) -/

/-- The template's terms with the row factor: `(wire, eq(τ_lo, j) · ι c)`. -/
@[specialize]
def ttOf (s : Mat) (T : Tpl) (eτ : ℕ → R) : List (Wire × R) :=
  T.rows.zipIdx.flatMap fun p => (s.t p.1).map fun t => (t.1, eτ p.2 * ι t.2)

/-- The local part `LOC`. -/
@[specialize]
def locSum (eσ : ℕ → R) (tt : List (Wire × R)) : R :=
  (tt.map fun p => match p.1 with | .loc k => p.2 * eσ k | _ => 0).sum
/-- The `one` part. -/
@[specialize]
def oneSum (tt : List (Wire × R)) : R := (tt.map fun p => match p.1 with | .one => p.2 | _ => 0).sum
/-- The input terms. -/
@[specialize]
def inpList (tt : List (Wire × R)) : List (ℕ × R) :=
  tt.filterMap fun p => match p.1 with | .inp i => some (i, p.2) | _ => none

/-- **The closed form of one instance**: `Hτ · (Hσ · LOC + ONE · E(one) + Σ_IT u · E(ins_i))`. -/
def instClosed (m : ℕ) (σ : ℕ → R) (one : Lin) (ins : List Lin) (Hτ Hσ loc onew : R)
    (it : List (ℕ × R)) : R :=
  Hτ * (Hσ * loc + onew * linE ι m σ one + (it.map fun p => p.2 * linE ι m σ (ins.getD p.1 [])).sum)

theorem partition (m : ℕ) (σ : ℕ → R) (one : Lin) (ins : List Lin) (cb : ℕ) (eσ : ℕ → R) (Hσ : R)
    (tt : List (Wire × R)) (hloc : ∀ p ∈ tt, ∀ k, p.1 = .loc k → gN m σ (cb + k) = eσ k * Hσ) :
    (tt.map fun p => p.2 * wireE ι m σ one ins cb p.1).sum =
      Hσ * locSum eσ tt + oneSum tt * linE ι m σ one +
        ((inpList tt).map fun p => p.2 * linE ι m σ (ins.getD p.1 [])).sum := by
  induction tt with
  | nil => simp [locSum, oneSum, inpList]
  | cons p tt ih =>
    rw [List.map_cons, List.sum_cons, ih fun q hq => hloc q (List.mem_cons_of_mem _ hq)]
    obtain ⟨w, u⟩ := p
    cases w with
    | one => simp [locSum, oneSum, inpList, wireE]; ring
    | inp i => simp [locSum, oneSum, inpList, wireE]; ring
    | loc k =>
      have := hloc _ (List.mem_cons_self ..) k rfl
      simp only [wireE] at this ⊢
      simp [locSum, oneSum, inpList, this]; ring

/-- A template row index is below `2^rbits`. -/
theorem lt_rbits (T : Tpl) {j : ℕ} (hj : j < T.rows.length) : j < 2 ^ T.rbits := by
  unfold Tpl.rbits
  exact lt_of_le_of_lt (show j ≤ T.rows.length - 1 by omega) (Nat.lt_size_self _)

theorem le_foldl_max (l : List ℕ) (a : ℕ) : a ≤ l.foldl max a := by
  induction l generalizing a with
  | nil => exact le_rfl
  | cons x l ih => exact le_trans (le_max_left _ _) (ih _)

theorem mem_le_foldl_max {l : List ℕ} {x : ℕ} (hx : x ∈ l) (a : ℕ) : x ≤ l.foldl max a := by
  induction l generalizing a with
  | nil => simp at hx
  | cons y l ih =>
    rcases List.mem_cons.1 hx with rfl | h
    · exact le_trans (le_max_right _ _) (le_foldl_max _ _)
    · exact ih h _

theorem mlStep_ge (a : ℕ) (t : Wire × F) : a ≤ mlStep a t := by
  obtain ⟨w, c⟩ := t; cases w <;> simp [mlStep]

theorem foldl_ml_ge (l : LinT) (a : ℕ) : a ≤ l.foldl mlStep a := by
  induction l generalizing a with
  | nil => exact le_rfl
  | cons t l ih => exact le_trans (mlStep_ge a t) (ih _)

theorem maxLoc_ge {l : LinT} {k : ℕ} {c : F} (h : (Wire.loc k, c) ∈ l) : k ≤ l.maxLoc := by
  unfold LinT.maxLoc
  suffices ∀ a, k ≤ l.foldl mlStep a from this 0
  induction l with
  | nil => simp at h
  | cons t l ih =>
    intro a
    rcases List.mem_cons.1 h with rfl | h'
    · exact le_trans (by simp [mlStep]) (foldl_ml_ge l _)
    · exact ih h' _

/-- A referenced local is below `2^cbits`. -/
theorem lt_cbits (T : Tpl) (s : Mat) {r : RowT} (hr : r ∈ T.rows) {k : ℕ} {c : F}
    (h : (Wire.loc k, c) ∈ s.t r) : k < 2 ^ T.cbits := by
  unfold Tpl.cbits
  refine lt_of_le_of_lt (le_trans ?_ (le_max_left _ _)) (Nat.lt_size_self _)
  have hk : k ≤ max r.a.maxLoc (max r.b.maxLoc r.c.maxLoc) := by
    cases s <;> simp only [Mat.t] at h <;> have := maxLoc_ge h <;> omega
  unfold Tpl.maxLoc
  exact le_trans hk (mem_le_foldl_max (l := T.rows.map fun r => max r.a.maxLoc
    (max r.b.maxLoc r.c.maxLoc)) (List.mem_map.2 ⟨r, hr, rfl⟩) 0)

theorem zipIdx_mem {α : Type*} {l : List α} {p : α × ℕ} (h : p ∈ l.zipIdx) :
    p.1 ∈ l ∧ p.2 < l.length := by
  obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.1 h
  simp only [List.getElem_zipIdx, List.length_zipIdx] at hi ⊢
  exact ⟨List.getElem_mem _, by simpa using hi⟩

/-- The rows of instance `(inst, ins)` of `T` at row base `X` (a multiple of `2^rbits`). -/
def instIRows (T : Tpl) (one : Lin) (ins : List Lin) (X cb : ℕ) : List (ℕ × Row) :=
  T.rows.zipIdx.map fun p => (X + p.2, instRow one ins cb p.1)

theorem sum_flatMap_map {α β : Type*} (l : List α) (f : α → List β) (g : β → R) :
    ((l.flatMap f).map g).sum = (l.map fun a => ((f a).map g).sum).sum := by
  induction l with
  | nil => rfl
  | cons a l ih => simp [List.flatMap_cons, ih]

/-- **`tpl_mle`**: an instance's sparse value is its closed form, when its row base is
`2^A · Xh` and its cell base `2^B · Ch` (A.11's alignment), `A = rbits`, `B = cbits`. -/
theorem tpl_mle (s : Mat) {n m : ℕ} (τ σ : ℕ → R) (T : Tpl) (one : Lin) (ins : List Lin)
    (Xh Ch : ℕ) (hA : T.rbits ≤ n) (hB : T.cbits ≤ m) (eτ eσ : ℕ → R)
    (heτ : ∀ j < T.rows.length, eτ j = eqN T.rbits τ j)
    (heσ : ∀ k < 2 ^ T.cbits, eσ k = eqN T.cbits σ k) :
    rowsVal ι s n m τ σ (instIRows T one ins (2 ^ T.rbits * Xh) (2 ^ T.cbits * Ch)) =
      instClosed ι m σ one ins (gN (n - T.rbits) (fun l => τ (T.rbits + l)) Xh)
        (gN (m - T.cbits) (fun l => σ (T.cbits + l)) Ch) (locSum eσ (ttOf ι s T eτ))
        (oneSum (ttOf ι s T eτ)) (inpList (ttOf ι s T eτ)) := by
  set Hτ := gN (n - T.rbits) (fun l => τ (T.rbits + l)) Xh
  set Hσ := gN (m - T.cbits) (fun l => σ (T.cbits + l)) Ch
  set cb := 2 ^ T.cbits * Ch
  have hloc : ∀ p ∈ ttOf ι s T eτ, ∀ k, p.1 = .loc k → gN m σ (cb + k) = eσ k * Hσ := by
    intro p hp k hk
    simp only [ttOf, List.mem_flatMap, List.mem_map] at hp
    obtain ⟨q, hq, ⟨w, c⟩, hwc, rfl⟩ := hp
    simp only at hk; subst hk
    have hk' := lt_cbits T s (zipIdx_mem hq).1 hwc
    rw [gN_split hB _ _ hk', heσ k hk']
  have hrow : ∀ p ∈ T.rows.zipIdx,
      gN n τ (2 ^ T.rbits * Xh + p.2) * linE ι m σ (s.r (instRow one ins cb p.1)) =
      Hτ * ((s.t p.1).map fun t => eτ p.2 * ι t.2 * wireE ι m σ one ins cb t.1).sum := by
    intro p hp
    have hj := (zipIdx_mem hp).2
    rw [gN_split hA _ _ (lt_rbits T hj), Mat.r_inst, linE_instLin, ← heτ _ hj, mul_comm (eτ _),
      mul_assoc, ← List.sum_map_mul_left]
    simp only [mul_assoc]; rfl
  unfold instClosed
  rw [← partition ι m σ one ins cb eσ Hσ _ hloc, rowsVal, instIRows, List.map_map, ttOf,
    sum_flatMap_map]
  simp only [Function.comp_def]
  rw [List.map_congr_left hrow, List.sum_map_mul_left]
  simp only [List.map_map, Function.comp_def]

/-! ## The slot: skeleton rows, then the instances -/

/-- A key's row base in a layout. -/
def _root_.FR.Circ.TLay.rb (L : TLay) (k : TKey) : ℕ :=
  match L.find? (·.1 == k) with
  | some (_, r, _, _) => r
  | none => 0

/-- Instance `t`'s indexed rows in a slot at row offset `off`. -/
def tinIRows (L : TLay) (one : Lin) (off : ℕ) (t : TKey × ℕ × List Lin) : List (ℕ × Row) :=
  let ia := t.2.2.toArray
  let cb := L.cb t.1 t.2.1
  match splitOf t.1 with
  | some (a, b) => (tRows t.1).zipIdx.map fun p =>
      (off + L.rb t.1 + splitRow a b t.2.1 p.2, instRowA one ia cb p.1)
  | none =>
    let X := off + L.rb t.1 + t.2.1 * 2 ^ tRbits t.1
    (tRows t.1).zipIdx.map fun p => (X + p.2, instRowA one ia cb p.1)

theorem tinIRows_none (L : TLay) (one : Lin) (off : ℕ) (t : TKey × ℕ × List Lin)
    (h : splitOf t.1 = none) :
    tinIRows L one off t =
      instIRows (tplOf t.1) one t.2.2 (off + L.rb t.1 + t.2.1 * 2 ^ (tplOf t.1).rbits) (L.cb t.1 t.2.1) := by
  unfold tinIRows; rw [h]; simp only [instIRows, tRows_eq, tRbits_eq, instRowA_eq]

/-- **A slot's indexed rows**: skeleton row `j` at `off + j`, then every instance's. -/
def slotIRows (L : TLay) (one : Lin) (off : ℕ) (cs : CS) : List (ℕ × Row) :=
  cs.rowList.zipIdx.map (fun p => (off + p.2, p.1)) ++ cs.tins.flatMap (tinIRows L one off)

theorem rowsVal_append (s : Mat) (n m : ℕ) (τ σ : ℕ → R) (a b : List (ℕ × Row)) :
    rowsVal ι s n m τ σ (a ++ b) = rowsVal ι s n m τ σ a + rowsVal ι s n m τ σ b := by
  simp [rowsVal]

theorem rowsVal_flatMap {α : Type*} (s : Mat) (n m : ℕ) (τ σ : ℕ → R) (l : List α)
    (f : α → List (ℕ × Row)) :
    rowsVal ι s n m τ σ (l.flatMap f) = (l.map fun a => rowsVal ι s n m τ σ (f a)).sum := by
  simp only [rowsVal, sum_flatMap_map]

/-! ## The implementation -/

/-- `eq(t, x)` over `n` coordinates by a list product (`eqNL_eq`). -/
@[specialize]
def eqNL (n : ℕ) (t : ℕ → R) (x : ℕ) : R :=
  ((List.range n).map fun l => if x.testBit l then t l else 1 - t l).prod

theorem eqNL_eq (n : ℕ) (t : ℕ → R) (x : ℕ) : eqNL n t x = eqN n t x := by
  unfold eqNL eqN
  induction n with
  | zero => rfl
  | succ n ih => rw [List.range_succ, List.map_append, List.prod_append, ih, Finset.prod_range_succ]; simp

/-- `gN` by `eqNL`. -/
@[specialize]
def gNL (n : ℕ) (t : ℕ → R) (x : ℕ) : R := if x < 2 ^ n then eqNL n t x else 0

/-- The table `eq(t_lo, ·)` over the first `A` coordinates. -/
@[specialize]
def loTab (A : ℕ) (t : ℕ → R) : Array R := eqTable ((List.range A).map t)

theorem loTab_getD (A : ℕ) (t : ℕ → R) {j : ℕ} (hj : j < 2 ^ A) :
    (loTab A t).getD j 0 = eqN A t j := by
  have h := Impl.eqTable_getD ((List.range A).map t) (i := j) (by simpa using hj)
  rw [loTab, h, Impl.eqAtR, eqN, List.length_map, List.length_range, ← Fin.prod_univ_eq_prod_range]
  refine Finset.prod_congr rfl fun l _ => ?_
  simp [ptOf, List.getD_eq_getElem?_getD]

/-- **`eq(σ, ·)` by two tables** (`s` low coordinates, `m − s` high): one product per cell. -/
@[specialize]
def splitAt (lo hi : Array R) (p x : ℕ) : R := lo.getD (x % p) 0 * hi.getD (x / p) 0

/-- The two tables are built once (a closure over them). -/
@[specialize]
def splitE (m s : ℕ) (t : ℕ → R) : ℕ → R :=
  splitAt (loTab s t) (loTab (m - s) fun l => t (s + l)) (2 ^ s)

theorem splitE_eq {m s : ℕ} (hs : s ≤ m) (t : ℕ → R) : splitE m s t = gN m t := by
  funext x
  have hx : x = 2 ^ s * (x / 2 ^ s) + x % 2 ^ s := (Nat.div_add_mod x _).symm
  have hlt : x % 2 ^ s < 2 ^ s := Nat.mod_lt _ (by positivity)
  simp only [splitE, splitAt]
  rw [loTab_getD s t hlt]
  conv_rhs => rw [hx, gN_split hs _ _ hlt]
  congr 1
  unfold gN
  split_ifs with h
  · rw [loTab_getD _ _ h]
  · rw [Array.getD_eq_getD_getElem?, Array.getElem?_eq_none]; · rfl
    simp [loTab, eqTable_size]; omega

/-- `Σ_{x ∈ l} f x` by a fold (no intermediate list). -/
@[specialize]
def sumL {α : Type*} (f : α → R) (l : List α) : R := l.foldl (fun a x => a + f x) 0

theorem sumL_eq {α : Type*} (f : α → R) (l : List α) : sumL f l = (l.map f).sum := by
  unfold sumL
  suffices ∀ a, l.foldl (fun a x => a + f x) a = a + (l.map f).sum by simpa using this 0
  induction l with
  | nil => simp
  | cons x l ih => intro a; simp [ih, add_assoc]

/-- `ι c · g x`, with no product when `c = 1`. -/
@[specialize]
def cmul (c : F) (g : R) : R := if c == 1 then g else ι c * g

theorem cmul_eq (c : F) (g : R) : cmul ι c g = ι c * g := by
  unfold cmul; split_ifs with h
  · rw [beq_iff_eq.1 h, map_one, one_mul]
  · rfl

/-- `linE` with an eq function. -/
@[specialize]
def linEI (g : ℕ → R) (l : Lin) : R := sumL (fun t => cmul ι t.2 (g t.1)) l

/-- The sparse value with eq functions (the skeleton's evaluation). -/
@[specialize]
def rowsValI (s : Mat) (gt gs : ℕ → R) (rows : List (ℕ × Row)) : R :=
  sumL (fun p => gt p.1 * linEI ι gs (s.r p.2)) rows

/-- **One key's precomputation** (once per evaluation, A.11's `O(|tpl|)`). -/
structure Prep (R : Type*) where
  A : ℕ
  B : ℕ
  loc : R
  one : R
  it : List (ℕ × R)

/-- `a[j]` (`0` past the end), as a function of `j` closing over the table. -/
@[specialize]
def getD0 (a : Array R) (j : ℕ) : R := a.getD j 0

@[specialize]
def prepT (s : Mat) (τ σ : ℕ → R) (T : Tpl) : Prep R :=
  let tt := ttOf ι s T (getD0 (loTab T.rbits τ))
  ⟨T.rbits, T.cbits, locSum (getD0 (loTab T.cbits σ)) tt, oneSum tt, inpList tt⟩

/-- A key's precomputation (`prepT` of its template). -/
@[specialize]
def prepOf (s : Mat) (τ σ : ℕ → R) (k : TKey) : Prep R := prepT ι s τ σ (tplOf k)

/-- An instance's value: the closed form when aligned, else its rows' sparse value. -/
@[specialize]
def instVal (s : Mat) (n m : ℕ) (τ σ : ℕ → R) (gt gs : ℕ → R) (L : TLay) (one : Lin) (off : ℕ)
    (p : Prep R) (t : TKey × ℕ × List Lin) : R :=
  let A := p.A; let B := p.B
  let X := off + L.rb t.1 + t.2.1 * 2 ^ A
  let cb := L.cb t.1 t.2.1
  if splitOf t.1 = none ∧ A ≤ n ∧ B ≤ m ∧ X % 2 ^ A = 0 ∧ cb % 2 ^ B = 0 then
    gNL (n - A) (fun l => τ (A + l)) (X / 2 ^ A) *
      (gNL (m - B) (fun l => σ (B + l)) (cb / 2 ^ B) * p.loc + p.one * linEI ι gs one +
        sumL (fun q => q.2 * linEI ι gs (t.2.2.getD q.1 [])) p.it)
  else rowsValI ι s gt gs (tinIRows L one off t)

/-- The cache of `prepOf` over the keys present. -/
@[specialize]
def prepCache (s : Mat) (τ σ : ℕ → R) (ks : List TKey) : List (TKey × Prep R) :=
  ks.map fun k => (k, prepOf ι s τ σ k)

@[specialize]
def prepFind (s : Mat) (τ σ : ℕ → R) (c : List (TKey × Prep R)) (k : TKey) : Prep R :=
  match c.find? (·.1 == k) with
  | some p => p.2
  | none => prepOf ι s τ σ k

theorem prepFind_eq (s : Mat) (τ σ : ℕ → R) (ks : List TKey) (k : TKey) :
    prepFind ι s τ σ (prepCache ι s τ σ ks) k = prepOf ι s τ σ k := by
  unfold prepFind
  split
  · rename_i p hp
    have h1 := List.find?_some hp
    obtain ⟨k', -, rfl⟩ := List.mem_map.1 (List.mem_of_find?_eq_some hp)
    simp only [beq_iff_eq] at h1; rw [h1]
  · rfl

/-- **A slot's matrix value** (templated): the skeleton sparse, every instance in closed form. -/
@[specialize]
def slotVal (s : Mat) (n m : ℕ) (τ σ : ℕ → R) (gt gs : ℕ → R) (L : TLay) (one : Lin) (off : ℕ)
    (cs : CS) : R :=
  let c := prepCache ι s τ σ ((keyCounts cs.tins).map (·.1))
  rowsValI ι s gt gs (cs.rowList.zipIdx.map fun p => (off + p.2, p.1)) +
    sumL (fun t => instVal ι s n m τ σ gt gs L one off (prepFind ι s τ σ c t.1) t) cs.tins

theorem linEI_eq (m : ℕ) (σ : ℕ → R) : linEI ι (gN m σ) = linE ι m σ := by
  funext l; simp only [linEI, linE, cmul_eq, sumL_eq]

theorem rowsValI_eq (s : Mat) (n m : ℕ) (τ σ : ℕ → R) (rows : List (ℕ × Row)) :
    rowsValI ι s (gN n τ) (gN m σ) rows = rowsVal ι s n m τ σ rows := by
  simp only [rowsValI, rowsVal, linEI_eq, sumL_eq]

theorem heτ (k : TKey) {τ : ℕ → R} : ∀ j < (tplOf k).rows.length,
    getD0 (loTab (tplOf k).rbits τ) j = eqN (tplOf k).rbits τ j := by
  intro j hj; unfold getD0; exact loTab_getD (tplOf k).rbits τ (lt_rbits _ hj)

theorem heσ (k : TKey) {σ : ℕ → R} : ∀ j < 2 ^ (tplOf k).cbits,
    getD0 (loTab (tplOf k).cbits σ) j = eqN (tplOf k).cbits σ j := by
  intro j hj; unfold getD0; exact loTab_getD (tplOf k).cbits σ hj

theorem gNL_eq (n : ℕ) (t : ℕ → R) : gNL n t = gN n t := by
  funext x; simp [gNL, gN, eqNL_eq]

/-- **`slotVal_eq`**: the templated value is the sparse value of the slot's indexed rows. -/
theorem slotVal_eq (s : Mat) (n m : ℕ) (τ σ : ℕ → R) (L : TLay) (one : Lin) (off : ℕ) (cs : CS) :
    slotVal ι s n m τ σ (gN n τ) (gN m σ) L one off cs = rowsVal ι s n m τ σ (slotIRows L one off cs) := by
  unfold slotVal slotIRows
  rw [rowsVal_append, rowsVal_flatMap, rowsValI_eq]
  simp only [sumL_eq]
  congr 2
  refine List.map_congr_left fun t _ => ?_
  rw [prepFind_eq]
  unfold instVal
  simp only []
  split_ifs with h
  · simp only [prepOf, prepT] at h ⊢
    obtain ⟨hs, hA, hB, hX, hc⟩ := h
    obtain ⟨Xh, hXh⟩ := Nat.dvd_of_mod_eq_zero hX
    obtain ⟨Ch, hCh⟩ := Nat.dvd_of_mod_eq_zero hc
    rw [tinIRows_none _ _ _ _ hs, hXh, hCh, Nat.mul_div_cancel_left _ (Nat.two_pow_pos _),
      Nat.mul_div_cancel_left _ (Nat.two_pow_pos _),
      tpl_mle ι s τ σ (tplOf t.1) one t.2.2 _ _ hA hB (getD0 (loTab (tplOf t.1).rbits τ))
        (getD0 (loTab (tplOf t.1).cbits σ)) (heτ t.1) (heσ t.1)]
    simp only [instClosed, gNL_eq, linEI_eq, sumL_eq]
  · exact rowsValI_eq ι s n m τ σ _

/-! ## Bridges to the sparse sums of `FRVIREval` (F) and `FRVerifierImpl` (K) -/

/-- The entries of indexed rows `(row, cell, coefficient)`. -/
def entriesI (s : Mat) (rows : List (ℕ × Row)) : Eval.Entries :=
  rows.flatMap fun p => (s.r p.2).map fun t => (p.1, t.1, t.2)

theorem eqAt_eqN (n : ℕ) (a : Array F) (x : ℕ) :
    Eval.eqAt (Eval.ptOf n a) x = eqN n (fun l => a.getD l 0) x := by
  rw [Eval.eqAt, eqN, ← Fin.prod_univ_eq_prod_range]; rfl

theorem rowsVal_sparse {R : Type*} [CommRing R] (ι : F →+* R) (s : Mat) (a b : ℕ) (τ σ : ℕ → R)
    (rows : List (ℕ × Row)) :
    rowsVal ι s a b τ σ rows = ((entriesI s rows).map fun e =>
      if e.1 < 2 ^ a ∧ e.2.1 < 2 ^ b then ι e.2.2 * eqN a τ e.1 * eqN b σ e.2.1 else 0).sum := by
  rw [entriesI, sum_flatMap_map, rowsVal]
  refine congrArg List.sum (List.map_congr_left fun p _ => ?_)
  rw [linE, ← List.sum_map_mul_left, List.map_map]
  refine congrArg List.sum (List.map_congr_left fun t _ => ?_)
  simp only [Function.comp_apply, gN]
  by_cases h1 : p.1 < 2 ^ a <;> by_cases h2 : t.1 < 2 ^ b <;> simp [h1, h2] <;> ring

/-- **F**: the templated value is `FRVIREval.sparseEval` of the indexed rows' entries. -/
theorem rowsVal_F (s : Mat) (a b : ℕ) (τ σ : Array F) (rows : List (ℕ × Row)) :
    rowsVal (RingHom.id F) s a b (fun l => τ.getD l 0) (fun l => σ.getD l 0) rows =
      Eval.sparseEval (entriesI s rows) (Eval.ptOf a τ) (Eval.ptOf b σ) := by
  rw [rowsVal_sparse, Eval.sparseEval]
  refine congrArg List.sum (List.map_congr_left fun e _ => ?_)
  simp only [eqAt_eqN, RingHom.id_apply]

theorem eqN_map {R : Type*} [CommRing R] (ι : F →+* R) (n : ℕ) (t : ℕ → F) (x : ℕ) :
    eqN n (fun l => ι (t l)) x = ι (eqN n t x) := by
  simp only [eqN, map_prod, apply_ite, map_sub, map_one]

/-- **K**: the templated value is S-F2's sparse sum over `K` (`sparseEvalK`'s body). -/
theorem rowsVal_K (s : Mat) (a b : ℕ) (τ : Array F) (σ : Array K) (rows : List (ℕ × Row)) :
    rowsVal K.ofFRingHom s a b (fun l => K.ofF (τ.getD l 0)) (fun l => σ.getD l 0) rows =
      ((entriesI s rows).map fun e => if e.1 < 2 ^ a ∧ e.2.1 < 2 ^ b then
        K.ofF (e.2.2 * Eval.eqAt (Eval.ptOf a τ) e.1) *
          Impl.eqAtR (fun l : Fin b => σ.getD l 0) e.2.1 else 0).sum := by
  rw [rowsVal_sparse]
  refine congrArg List.sum (List.map_congr_left fun e _ => ?_)
  have h1 := eqN_map K.ofFRingHom a (fun l => τ.getD l 0) e.1
  have h2 : Impl.eqAtR (fun l : Fin b => σ.getD l 0) e.2.1 = eqN b (fun l => σ.getD l 0) e.2.1 := by
    rw [Impl.eqAtR, eqN, ← Fin.prod_univ_eq_prod_range]
  have h1' : eqN a (fun l => K.ofF (τ.getD l 0)) e.1 = K.ofF (eqN a (fun l => τ.getD l 0) e.1) := h1
  have hm : ∀ x y : F, K.ofF (x * y) = K.ofF x * K.ofF y := fun x y => map_mul K.ofFRingHom x y
  split_ifs
  · rw [eqAt_eqN, h2, h1', hm]; rfl
  · rfl

end TEval
end FR

end G6_FRVIRTplEval
