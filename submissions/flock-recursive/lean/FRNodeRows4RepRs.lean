-- New for `flock-recursive` (R-OPS §5.2, stage R3: `rsWeight`'s replay at the previous-node slot).
import FRVIRTplChain
import FRNodeRows4RepRsV

/-!
# The replay template of a node's `rsWeight` (`rsWeightF4 ν`, the kind factor included)

One node kind's sub-template, built with the chain library (`FRVIRTplChain`) and computing
`RsR.rsRef` (= `rsWeightF4 ν` by `RsR.rsWeightF4_ref`) for **any** claim points in `K`:

* `phiG`: the 128 coefficients `c_k(r″)` (`phiTable`'s tree, `F`);
* per claim, per coordinate, a `K` squaring chain of 127 steps (`sqChainK`: the stage points);
* per block of the kind skeleton, once: `W₀` and `G` (`prodK` over the fixed bits; the exponent sum
  from `β`'s powers `powF`), then `W₀`'s squaring chain (`blockG`);
* per claim and stage: claim 2 (`j = 1`) the product `eq(q_hi, ρ_hi)` and the kind factor (per level
  `Σ W₀^(2^k)·G`, Horner over the levels: `kindG`); the other claims `eq(q, ρ)` (`prodK`); each
  times `c_k` (`smulK`);
* `Σ_j κ^j v_j`.

**`ok_rsG`**: under the gate equations, the output is `rsRef ν r ps κ β ρ` at the inputs' values.
-/

namespace FR
namespace Tpl
open Circ GM Rev4 RsR Impl

variable {e : Env}

/-! ## Pieces -/

/-- `1 + a + b` (one factor of `eqPtsC`; linear). -/
def addE (a b : KF) : KF := addK (addK oneK a) b

theorem evK_addE (h1 : e.one = 1) (a b : KF) : evK e (addE a b) = 1 + evK e a + evK e b := by
  rw [addE, evK_addK, evK_addK, evK_oneK h1]

/-- A fixed bit's factor as a pair of forms. -/
def selK (x : ℕ → KF) (b : ℕ × Bool) : KF := if b.2 then x b.1 else oneSubK (x b.1)

theorem evK_selK (h1 : e.one = 1) {x : ℕ → KF} {v : ℕ → K} (hx : ∀ l, evK e (x l) = v l) (b : ℕ × Bool) :
    evK e (selK x b) = selV v b := by
  unfold selK selV; split_ifs <;> simp [hx, evK_oneSubK h1]

/-- `Σ_{i ∈ es} β^i` from the powers' forms. -/
def expSum (βp : List LinT) (es : List ℕ) : LinT := es.flatMap fun i => βp.getD i []

theorem ev_getD_pow {βp : List LinT} {β : F} {E : ℕ}
    (hβ : βp.map (LinT.ev e) = (List.range (E + 1)).map (β ^ ·)) {i : ℕ} (hi : i ≤ E) :
    (βp.getD i []).ev e = β ^ i := by
  have hl : βp.length = E + 1 := by simpa using congrArg List.length hβ
  rw [List.getD_eq_getElem _ _ (by omega)]
  have := congrArg (fun l => l[i]?) hβ
  simp only [List.getElem?_map, List.getElem?_range (show i < E + 1 by omega)] at this
  rw [List.getElem?_eq_getElem (by omega)] at this
  simpa using this

theorem ev_expSum {βp : List LinT} {β : F} {E : ℕ}
    (hβ : βp.map (LinT.ev e) = (List.range (E + 1)).map (β ^ ·)) {es : List ℕ} (hes : ∀ i ∈ es, i ≤ E) :
    (expSum βp es).ev e = (es.map (β ^ ·)).sum := by
  induction es with
  | nil => rfl
  | cons i es ih =>
    rw [expSum, List.flatMap_cons, ev_append, ← expSum, ih fun j hj => hes j (List.mem_cons_of_mem _ hj),
      ev_getD_pow hβ (hes i (List.mem_cons_self ..)), List.map_cons, List.sum_cons]

theorem evK_getD (l : List KF) (k : ℕ) : evK e (l.getD k zeroK) = (l.map (evK e)).getD k 0 := by
  rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, List.getElem?_map]
  cases l[k]? <;> rfl

/-- The largest exponent of a skeleton. -/
def maxE (sk : List (List (List (ℕ × Bool) × List ℕ))) : ℕ :=
  ((sk.flatten).flatMap (·.2)).foldr max 0

theorem le_foldr_max : ∀ {l : List ℕ} {i : ℕ}, i ∈ l → i ≤ l.foldr max 0
  | _ :: _, _, .head _ => le_max_left _ _
  | _ :: _, _, .tail _ h => le_trans (le_foldr_max h) (le_max_right _ _)

theorem le_maxE {sk : List (List (List (ℕ × Bool) × List ℕ))} {g : List (List (ℕ × Bool) × List ℕ)}
    (hg : g ∈ sk) {p : List (ℕ × Bool) × List ℕ} (hp : p ∈ g) {i : ℕ} (hi : i ∈ p.2) : i ≤ maxE sk :=
  le_foldr_max (List.mem_flatMap.2 ⟨p, List.mem_flatten.2 ⟨g, hg, hp⟩, hi⟩)

/-! ## A block of the kind skeleton (once) -/

/-- **A block, once**: `W₀ = (Σ β^i)·Π q_b`, `G = Π ρ_b`, and `W₀`'s squaring chain (128 values). -/
def blockG (βp : List LinT) (qa ρa : ℕ → KF) (p : List (ℕ × Bool) × List ℕ) : GM (List KF × KF) :=
  (prodK (ofFK (expSum βp p.2) :: p.1.map (selK qa))).bind fun w0 =>
  (prodK (p.1.map (selK ρa))).bind fun g =>
  (sqChainK 127 w0).map fun ws => (ws, g)

/-- A block's values: `W₀`'s 128 Frobenius images, and `G`. -/
def blockV (β : F) (q ρ : ℕ → K) (p : List (ℕ × Bool) × List ℕ) : List K × K :=
  ((List.range 128).map fun i => sqIter i (w0V β q p), gV ρ p)

/-- The value of a built block. -/
def blockE (e : Env) (wg : List KF × KF) : List K × K := (wg.1.map (evK e), evK e wg.2)

theorem ok_blockG (h1 : e.one = 1) {βp : List LinT} {β : F} {E : ℕ}
    (hβ : βp.map (LinT.ev e) = (List.range (E + 1)).map (β ^ ·)) {qa ρa : ℕ → KF} {q ρ : ℕ → K}
    (hq : ∀ l, evK e (qa l) = q l) (hρ : ∀ l, evK e (ρa l) = ρ l) (p : List (ℕ × Bool) × List ℕ)
    (hp : ∀ i ∈ p.2, i ≤ E) : Ok e (blockG βp qa ρa p) fun wg => blockE e wg = blockV β q ρ p :=
  ok_bind (ok_prodK h1 _) fun w0 hw0 => ok_bind (ok_prodK h1 _) fun g hg =>
    ok_map (ok_sqChainK 127 w0) fun ws hws => (by
      have hw : evK e w0 = w0V β q p := by
        rw [hw0, List.map_cons, List.prod_cons, evK_ofFK, ev_expSum hβ hp, List.map_map, w0V]
        exact congrArg _ (congrArg _ (List.map_congr_left fun b _ => evK_selK h1 hq b))
      have hg' : evK e g = gV ρ p := by
        rw [hg, List.map_map, gV]
        exact congrArg _ (List.map_congr_left fun b _ => evK_selK h1 hρ b)
      simp only [blockE, blockV, hws, hw, hg'])

/-! ## Claim 2's kind factor at one stage -/

/-- One level at stage `k`: `Σ_p W₀(p)^(2^k)·G(p)`. -/
def levelG (k : ℕ) (lvl : List (List KF × KF)) : GM KF :=
  (mapL (fun wg : List KF × KF => mulK (wg.1.getD k zeroK) wg.2) lvl).map sumK

theorem ok_levelG {k : ℕ} (hk : k < 128) {β : F} {q ρ : ℕ → K} {lvl : List (List KF × KF)}
    {g : List (List (ℕ × Bool) × List ℕ)} (hl : lvl.map (blockE e) = g.map (blockV β q ρ)) :
    Ok e (levelG k lvl) fun y => evK e y = (g.map fun p => sqIter k (w0V β q p) * gV ρ p).sum :=
  ok_map (ok_mapL (E := evK e) (v := fun wg => (blockE e wg).1.getD k 0 * (blockE e wg).2) lvl
    fun wg _ => ok_mono (ok_mulK _ _) fun o ho => by rw [ho, evK_getD]; rfl) fun ms hms => (by
    rw [evK_sumK, hms]
    have := congrArg (List.map fun x : List K × K => x.1.getD k 0 * x.2) hl
    simp only [List.map_map] at this
    rw [show (fun wg : List KF × KF => (blockE e wg).1.getD k 0 * (blockE e wg).2) =
      (fun x : List K × K => x.1.getD k 0 * x.2) ∘ blockE e from rfl, this]
    refine congrArg _ (List.map_congr_left fun p _ => ?_)
    simp only [Function.comp_apply, blockV]
    rw [List.getD_eq_getElem _ _ (by simpa using hk)]
    simp)

/-- **Claim 2's block factor at stage `k`**: the levels, then Horner with `s_l = 1 + q_l + ρ_l`. -/
def kindG (bl : List (List (List KF × KF))) (qk ρa : ℕ → KF) (k : ℕ) : GM KF :=
  (mapL (levelG k) bl).bind fun ys => hornerKG (fun l => addE (qk l) (ρa l)) 0 ys

theorem ok_kindG (h1 : e.one = 1) {k : ℕ} (hk : k < 128) {β : F} {q ρ : ℕ → K} {qk ρa : ℕ → KF}
    (hqk : ∀ l, evK e (qk l) = sqIter k (q l)) (hρ : ∀ l, evK e (ρa l) = ρ l)
    {bl : List (List (List KF × KF))} {sk : List (List (List (ℕ × Bool) × List ℕ))}
    (hbl : bl.map (List.map (blockE e)) = sk.map (List.map (blockV β q ρ))) :
    Ok e (kindG bl qk ρa k) fun y => evK e y = kindV sk β q ρ k := by
  have hlen : bl.length = sk.length := by simpa using congrArg List.length hbl
  refine ok_bind (P := fun ys => ys.map (evK e) =
      sk.map fun g => (g.map fun p => sqIter k (w0V β q p) * gV ρ p).sum) ?_ fun ys hys =>
    ok_mono (ok_hornerKG _ 0 ys) fun y hy => by
      rw [hy, hys, kindV]
      congr 1
      funext l
      rw [evK_addE h1, hqk, hρ]
  -- the levels, pairwise
  have key : ∀ (bl : List (List (List KF × KF))) (sk : List (List (List (ℕ × Bool) × List ℕ))),
      bl.map (List.map (blockE e)) = sk.map (List.map (blockV β q ρ)) →
      Ok e (mapL (levelG k) bl) fun ys => ys.map (evK e) =
        sk.map fun g => (g.map fun p => sqIter k (w0V β q p) * gV ρ p).sum := by
    intro bl
    induction bl with
    | nil => intro sk h; cases sk with
      | nil => exact ok_ret rfl
      | cons _ _ => simp at h
    | cons lv bl ih => intro sk h; cases sk with
      | nil => simp at h
      | cons g sk =>
        simp only [List.map_cons, List.cons.injEq] at h
        exact ok_bind (ok_levelG hk h.1) fun y hy => ok_map (ih sk h.2) fun ys hys => by
          simp [hy, hys]
  exact key bl sk hbl

/-! ## One claim -/

/-- The stage-`k` point from the coordinates' chains. -/
def stagePt (chs : List (List KF)) (k : ℕ) : List KF := chs.map (·.getD k zeroK)

theorem stagePt_ev {k : ℕ} (hk : k < 128) {chs : List (List KF)} {p : List K}
    (h : chs.map (List.map (evK e)) = p.map fun x => (List.range 128).map fun i => sqIter i x) :
    (stagePt chs k).map (evK e) = p.map (sqIter k) := by
  have := congrArg (List.map fun l : List K => l.getD k 0) h
  simp only [List.map_map] at this
  rw [stagePt, List.map_map]
  refine (List.map_congr_left fun ch _ => ?_).trans (this.trans (List.map_congr_left fun x _ => ?_))
  · simp only [Function.comp_apply, evK_getD]
  · simp only [Function.comp_apply]
    rw [List.getD_eq_getElem _ _ (by simpa using hk)]
    simp

theorem map_zipWith_addE (h1 : e.one = 1) (a b : List KF) :
    (List.zipWith addE a b).map (evK e) = List.zipWith (fun x y => 1 + x + y) (a.map (evK e)) (b.map (evK e)) := by
  induction a generalizing b with
  | nil => rfl
  | cons x a ih => cases b with
    | nil => rfl
    | cons y b => simp only [List.zipWith_cons_cons, List.map_cons, ih, evK_addE h1]

theorem ok_eqPtsC (h1 : e.one = 1) (a b : List KF) :
    Ok e (prodK (List.zipWith addE a b)) fun o => evK e o = eqPtsC (a.map (evK e)) (b.map (evK e)) :=
  ok_mono (ok_prodK h1 _) fun o ho => by rw [ho, map_zipWith_addE h1]; rfl

/-- Claim `j`'s stage-`k` term (claim 2: `eq(q_hi, ρ_hi)` times the kind factor). -/
def termG (ρI : List KF) (bl : List (List (List KF × KF))) (chs : List (List KF)) (j k : ℕ) : GM KF :=
  if j = 1 then
    (prodK (List.zipWith addE ((stagePt chs k).take 7) (ρI.take 7))).bind fun hi =>
    (kindG bl (fun l => ((stagePt chs k).drop 7).getD l zeroK) (fun l => (ρI.drop 7).getD l zeroK) k).bind
      fun kf => mulK hi kf
  else prodK (List.zipWith addE (stagePt chs k) ρI)

theorem take_drop_getD (l : List KF) (l' : ℕ) :
    evK e ((l.drop 7).getD l' zeroK) = ((l.map (evK e)).drop 7).getD l' 0 := by
  rw [evK_getD, List.map_drop]

theorem ok_termG (h1 : e.one = 1) (ν : NodeKind) {k : ℕ} (hk : k < 128) {β : F} {ρI : List KF} {ρ : List K}
    (hρ : ρI.map (evK e) = ρ) {bl : List (List (List KF × KF))} {chs : List (List KF)} {p : List K} {j : ℕ}
    (hch : chs.map (List.map (evK e)) = p.map fun x => (List.range 128).map fun i => sqIter i x)
    (hbl : j = 1 → bl.map (List.map (blockE e)) = (skelAt ν (ρ.length - 7)).map
      (List.map (blockV β (fun l => (p.drop 7).getD l 0) (fun l => (ρ.drop 7).getD l 0)))) :
    Ok e (termG ρI bl chs j k) fun o => evK e o = termV ν β ρ p j k := by
  have hst := stagePt_ev hk hch
  unfold termG termV
  split_ifs with hj
  · refine ok_bind (ok_eqPtsC h1 _ _) fun hi hhi => ok_bind (ok_kindG h1 hk (q := fun l => (p.drop 7).getD l 0)
      (ρ := fun l => (ρ.drop 7).getD l 0) (fun l => ?_) (fun l => ?_) (hbl hj)) fun kf hkf =>
      ok_mono (ok_mulK hi kf) fun o ho => by
        rw [ho, hhi, hkf, List.map_take, List.map_take, hst, hρ]
    · rw [take_drop_getD, hst, ← List.map_drop, List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD,
        List.getElem?_map]
      cases (p.drop 7)[l]? <;> simp [sqIter_zeroK]
    · rw [take_drop_getD, hρ]
  · exact ok_mono (ok_eqPtsC h1 _ _) fun o ho => by rw [ho, hst, hρ]

/-- **One claim**: its coordinates' squaring chains, then `Σ_k c_k · term_k`. -/
def claimG (ρI : List KF) (bl : List (List (List KF × KF))) (cT : List LinT) (pj : List KF × ℕ) : GM KF :=
  (mapL (sqChainK 127) pj.1).bind fun chs =>
  (mapL (fun k => (termG ρI bl chs pj.2 k).bind fun t => smulK (cT.getD k []) t) (List.range 128)).map sumK

/-- A claim's value. -/
def claimV (ν : NodeKind) (c : List F) (β : F) (ρ p : List K) (j : ℕ) : K :=
  ((List.range 128).map fun k => K.ofF (c.getD k 0) * termV ν β ρ p j k).sum

theorem ok_claimG (h1 : e.one = 1) (ν : NodeKind) {β : F} {ρI : List KF} {ρ : List K}
    (hρ : ρI.map (evK e) = ρ) {bl : List (List (List KF × KF))} {cT : List LinT} {c : List F}
    (hc : cT.map (LinT.ev e) = c) (a : List KF) (j : ℕ)
    (hbl : j = 1 → bl.map (List.map (blockE e)) = (skelAt ν (ρ.length - 7)).map
      (List.map (blockV β (fun l => ((a.map (evK e)).drop 7).getD l 0) (fun l => (ρ.drop 7).getD l 0)))) :
    Ok e (claimG ρI bl cT (a, j)) fun o => evK e o = claimV ν c β ρ (a.map (evK e)) j :=
  ok_bind (ok_mapL (E := List.map (evK e)) (v := fun x => (List.range 128).map fun i => sqIter i (evK e x)) a
    fun x _ => ok_sqChainK 127 x) fun chs hch =>
  ok_map (ok_mapL (E := evK e) (v := fun k => K.ofF (c.getD k 0) * termV ν β ρ (a.map (evK e)) j k) _
    fun k hk => ok_bind (ok_termG h1 ν (List.mem_range.1 hk) hρ (by rw [hch, List.map_map]; rfl) hbl)
      fun t ht => ok_mono (ok_smulK _ t) fun o ho => by rw [ho, ht, ev_getD_lag, hc]) fun ts hts =>
  (by rw [evK_sumK, hts, claimV])

/-! ## The template -/

theorem getD_map_nil {α β : Type} (f : List α → List β) (hf : f [] = []) (l : List (List α)) (j : ℕ) :
    (l.map f).getD j [] = f (l.getD j []) := by
  rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, List.getElem?_map]
  cases l[j]? <;> simp [hf]

/-- **The node kind `ν`'s `rsWeight` template** over input forms: `r″` (`F`), the claims (`K`
coordinates), `κ`, `β` (`F`), `ρ` (`K`). -/
def rsG (ν : NodeKind) (rI : List LinT) (pI : List (List KF)) (κI βI : LinT) (ρI : List KF) : GM KF :=
  (phiG rI).bind fun cT =>
  (powF (maxE (skelAt ν (ρI.length - 7))) βI).bind fun βp =>
  (mapL (mapL (blockG βp (fun l => ((pI.getD 1 []).drop 7).getD l zeroK) (fun l => (ρI.drop 7).getD l zeroK)))
    (skelAt ν (ρI.length - 7))).bind fun bl =>
  (powF pI.length κI).bind fun κp =>
  (mapL (fun aj : List KF × ℕ => (claimG ρI bl cT aj).bind fun v => smulK (κp.getD aj.2 []) v) pI.zipIdx).map
    sumK

/-- **`rsG` computes `rsRef`** at the inputs' values. -/
theorem ok_rsG (h1 : e.one = 1) (ν : NodeKind) {rI : List LinT} {pI : List (List KF)} {κI βI : LinT}
    {ρI : List KF} {r : List F} {ps : List (List K)} {κ β : F} {ρ : List K}
    (hr : rI.map (LinT.ev e) = r) (hp : pI.map (List.map (evK e)) = ps) (hκ : κI.ev e = κ)
    (hβ : βI.ev e = β) (hρ : ρI.map (evK e) = ρ) :
    Ok e (rsG ν rI pI κI βI ρI) fun o => evK e o = rsRef ν r ps κ β ρ := by
  have hlρ : ρI.length = ρ.length := by rw [← hρ, List.length_map]
  have hq0 : ∀ l, evK e (((pI.getD 1 []).drop 7).getD l zeroK) = ((ps.getD 1 []).drop 7).getD l 0 := fun l => by
    rw [take_drop_getD, ← hp, getD_map_nil _ rfl]
  refine ok_bind (ok_phiG h1 rI) fun cT hcT => ok_bind (ok_powF h1 _ βI) fun βp hβp =>
    ok_bind (P := fun bl => bl.map (List.map (blockE e)) = (skelAt ν (ρI.length - 7)).map
        (List.map (blockV β (fun l => ((ps.getD 1 []).drop 7).getD l 0) (fun l => (ρ.drop 7).getD l 0))))
      (ok_mapL _ fun g hg => ok_mapL _ fun p hp' => ok_blockG h1 (hβ ▸ hβp) hq0
        (fun l => by rw [take_drop_getD, hρ]) p fun i hi => le_maxE hg hp' hi) fun bl hbl =>
    ok_bind (ok_powF h1 pI.length κI) fun κp hκp =>
    ok_map (ok_mapL (E := evK e) (v := fun aj : List KF × ℕ =>
        K.ofF (κ ^ aj.2) * claimV ν (phiTable r).toList β ρ (aj.1.map (evK e)) aj.2) pI.zipIdx
      fun aj haj => ?_) fun vs hvs => ?_
  · obtain ⟨a, j⟩ := aj
    obtain ⟨-, hjl, ha⟩ := List.mem_zipIdx haj
    simp only [zero_add, Nat.sub_zero] at hjl ha
    refine ok_bind (ok_claimG h1 ν hρ (c := (phiTable r).toList) (by rw [hcT, hr]) a j fun hj => ?_)
      fun v hv => ok_mono (ok_smulK _ v) fun o ho => by
        rw [ho, hv, ev_getD_pow hκp (by omega), hκ]
    subst hj
    rw [hbl, hlρ, ← hp, getD_map_nil _ rfl, List.getD_eq_getElem _ _ hjl, ha]
  · rw [evK_sumK, hvs, rsRef, ← hp, List.zipIdx_map, List.map_map]
    rfl

end Tpl
end FR
