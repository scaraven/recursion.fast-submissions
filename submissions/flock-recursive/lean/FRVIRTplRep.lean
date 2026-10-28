-- New for `flock-recursive` (BLUEPRINT A.11, §10 changes 17; stage S-E6, track L-circ).
import FRVIRTplLag
import FRVIRTplTab

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
