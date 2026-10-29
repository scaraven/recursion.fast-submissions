-- New for `flock-recursive` (BLUEPRINT revision 4.3, route (A); stage S-E12f, track L-circ:
-- INT-9's finding F1).
import FRVIRTplRep
import FRVIRTplMaskN

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
