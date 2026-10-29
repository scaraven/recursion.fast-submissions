-- New for `flock-recursive` (BLUEPRINT revision 4.1, B-13, A.9 `finSh`, A.11; stage S-E12e, track
-- L-circ).
import FRVIRTplSeg

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
