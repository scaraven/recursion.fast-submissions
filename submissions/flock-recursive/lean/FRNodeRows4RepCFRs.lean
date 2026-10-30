-- New for `flock-recursive` (track CF): `rsWeight`'s replay template as repeated patterns.
import FRNodeRows4RepRs
import FRVIRTplCF

/-!
# `rsWeight`'s replay template, laid out as repeated patterns

R3's `rsG` computes `rsRef` gate by gate; 93 % of its rows are 128-step squaring chains and the
128 Frobenius stages. **`rsGS`** computes the same value (`ok_rsGS`) with those parts as repeated
patterns (`FRVIRTplCF.Rep`), whose rows' MLE the plan evaluates in closed form:

* the blocks once (`W₀`, `G`; irregular), then **one chain per block** (`chainS`: the pattern is a
  127-step `K` squaring chain, its seed a placeholder);
* **one chain per claim coordinate** (`chainS`);
* **stage group A** (`patA`, 128 instances): per claim `j ≠ 1`, `c_k · eq(p_j^(2^k), ρ)`; for claim 1
  the `eq` of its first seven coordinates;
* **stage group B** (`patB`, 128 instances): claim 1's kind factor at stage `k` (`kindG`), times A's
  prefix, times `c_k`;
* per claim, `κ^j · Σ_k` (irregular).

A pattern reads its inputs through placeholders: input `0` is `c_k`, slot `v` (inputs `1 + 2v`,
`2 + 2v`) a `K` value (`kv v`), each a constant or one form per stage (`Src`).
-/

namespace FR
namespace Tpl
open Circ GM Rev4 RsR Impl

variable {e : Env}

/-! ## Flat `K` lists -/

/-- `K` pairs, flat. -/
def flatK (l : List KF) : List LinT := l.flatMap fun x => [x.1, x.2]

/-- `K` values, flat. -/
def flatV (l : List K) : List F := l.flatMap fun x => [x.f₀, x.f₁]

/-- The `i`-th `K` pair of a flat list. -/
def kfAt (l : List LinT) (i : ℕ) : KF := (l.getD (2 * i) [], l.getD (2 * i + 1) [])

theorem flatK_ev (l : List KF) : (flatK l).map (LinT.ev e) = flatV (l.map (evK e)) := by
  induction l with
  | nil => rfl
  | cons x l ih =>
    simp only [flatK, flatV, List.flatMap_cons, List.map_append, List.map_cons, List.map_nil] at ih ⊢
    rw [ih]; rfl

theorem flatV_getD : ∀ (vs : List K) (i : ℕ) (hi : i < vs.length),
    (flatV vs).getD (2 * i) 0 = (vs[i]'hi).f₀ ∧ (flatV vs).getD (2 * i + 1) 0 = (vs[i]'hi).f₁
  | [], _, hi => absurd hi (by simp)
  | v :: vs, 0, _ => by simp [flatV]
  | v :: vs, i + 1, hi => by
    have := flatV_getD vs i (by simpa using hi)
    simp only [flatV, List.flatMap_cons] at this ⊢
    rw [show 2 * (i + 1) = 2 * i + 2 by ring, show 2 * i + 2 + 1 = (2 * i + 1) + 2 by ring]
    simpa [List.getD_eq_getElem?_getD] using this

theorem evK_kfAt {l : List LinT} {vs : List K} (h : l.map (LinT.ev e) = flatV vs) {i : ℕ} (hi : i < vs.length) :
    evK e (kfAt l i) = vs[i] := by
  have := flatV_getD vs i hi
  rw [← h] at this
  apply K_ext'
  · show (l.getD (2 * i) []).ev e = _; rw [ev_getD_lag]; exact this.1
  · show (l.getD (2 * i + 1) []).ev e = _; rw [ev_getD_lag]; exact this.2

/-! ## Shapes -/

/-- `l` cut into the lengths of `L`'s lists. -/
def unflat {α β : Type} : List (List α) → List β → List (List β)
  | [], _ => []
  | g :: gs, l => l.take g.length :: unflat gs (l.drop g.length)

theorem unflat_map {α β γ : Type} (f : β → γ) : ∀ (L : List (List α)) (l : List β),
    unflat L (l.map f) = (unflat L l).map (List.map f)
  | [], _ => rfl
  | g :: gs, l => by
    simp only [unflat, List.map_cons, List.map_take]; rw [← List.map_drop, unflat_map f gs]

theorem unflat_flatten {α β : Type} : ∀ (L : List (List α)) (M : List (List β)),
    M.map List.length = L.map List.length → unflat L M.flatten = M
  | [], [], _ => rfl
  | [], _ :: _, h => by simp at h
  | _ :: _, [], h => by simp at h
  | g :: gs, x :: xs, h => by
    simp only [List.map_cons, List.cons.injEq] at h
    simp only [unflat, List.flatten_cons, ← h.1, List.take_left', List.drop_left', unflat_flatten gs xs h.2]

theorem range_map_getElem {α β : Type} (l : List α) (f : α → β) (g : ℕ → β)
    (h : ∀ i (hi : i < l.length), g i = f l[i]) : (List.range l.length).map g = l.map f :=
  List.ext_getElem (by simp) fun i h1 h2 => by simp [h i (by simpa using h1)]

/-! ## Placeholders: `c_k` and `K` slots -/

/-- Slot `v`'s `K` input. -/
def kv (v : ℕ) : KF := (I (1 + 2 * v), I (2 + 2 * v))

/-- A slot's source: one pair for every instance, or one per instance. -/
inductive Src where
  | cst (x : KF)
  | var (a : Array KF)

def Src.at : Src → ℕ → KF
  | .cst x, _ => x
  | .var a, s => a.getD s zeroK

def Src.ph : Src → List Ph
  | .cst x => [.cst x.1, .cst x.2]
  | .var a => [.var (a.map (·.1)), .var (a.map (·.2))]

/-- The placeholders: `c_k` (input `0`), then the slots. -/
def phOf (c : Array LinT) (sl : List Src) : Array Ph := (Ph.var c :: sl.flatMap Src.ph).toArray

theorem getD_pairs {α : Type} (d : α) (g : Src → List α) (hg : ∀ x, (g x).length = 2) :
    ∀ (sl : List Src) (v : ℕ) (hv : v < sl.length),
      (sl.flatMap g).getD (2 * v) d = (g sl[v]).getD 0 d ∧ (sl.flatMap g).getD (2 * v + 1) d = (g sl[v]).getD 1 d
  | [], _, hv => absurd hv (by simp)
  | x :: sl, 0, _ => by
    have := hg x
    match h : g x, this with
    | [a, b], _ => simp [h]
  | x :: sl, v + 1, hv => by
    have ih := getD_pairs d g hg sl v (by simpa using hv)
    have hx := hg x
    simp only [List.flatMap_cons, List.getElem_cons_succ]
    rw [show 2 * (v + 1) = (2 * v) + (g x).length by rw [hx]; ring,
      show 2 * v + (g x).length + 1 = (2 * v + 1) + (g x).length by ring]
    simp only [List.getD_eq_getElem?_getD, List.getElem?_append_right (Nat.le_add_left _ _),
      Nat.add_sub_cancel] at ih ⊢
    exact ih

theorem Src.at_ph (x : Src) (s : ℕ) :
    ((x.ph.getD 0 (.cst [])).at s, (x.ph.getD 1 (.cst [])).at s) = x.at s := by
  cases x with
  | cst y => rfl
  | var a =>
    simp only [Src.ph, Src.at, List.getD_cons_zero, List.getD_cons_succ, Ph.at]
    simp only [Array.getD_eq_getD_getElem?, Array.getElem?_map]
    cases a[s]? <;> rfl

/-- **A pattern's inputs at instance `s`**: `c_k` and the slots' values. -/
theorem phOf_inp {n p : ℕ} {g : List Gate} {c : Array LinT} {sl : List Src} {e' : Env} {s : ℕ}
    (h : ∀ i, e'.inp i = (Rep.σ ⟨n, p, g, phOf c sl⟩ s i).ev e) :
    (I 0).ev e' = (c.getD s []).ev e ∧ ∀ v (hv : v < sl.length), evK e' (kv v) = evK e (sl[v].at s) := by
  refine ⟨by rw [ev_I, h]; rfl, fun v hv => ?_⟩
  have hp := getD_pairs (Ph.cst []) Src.ph (fun x => by cases x <;> rfl) sl v hv
  have e0 : (phOf c sl).getD (1 + 2 * v) (.cst []) = (sl.flatMap Src.ph).getD (2 * v) (.cst []) := by
    simp [phOf, Array.getD_eq_getD_getElem?, List.getD_eq_getElem?_getD, Nat.add_comm 1]
  have e1 : (phOf c sl).getD (2 + 2 * v) (.cst []) = (sl.flatMap Src.ph).getD (2 * v + 1) (.cst []) := by
    simp [phOf, Array.getD_eq_getD_getElem?, List.getD_eq_getElem?_getD, show 2 + 2 * v = (2 * v + 1) + 1 by ring]
  have := Src.at_ph sl[v] s
  rw [← hp.1, ← hp.2, ← e0, ← e1] at this
  apply K_ext'
  · show (I (1 + 2 * v)).ev e' = _; rw [ev_I, h, ← this]; rfl
  · show (I (2 + 2 * v)).ev e' = _; rw [ev_I, h, ← this]; rfl

/-! ## Repeated patterns at their own stride -/

/-- The stride of a pattern: the least `p` with `2^p` above its rows and locals. -/
def pOf (g : GM (List LinT)) : ℕ := Nat.clog 2 (max (nrows (g 0).1) (nlocs (g 0).1))

theorem fit_pOf (n : ℕ) (g : GM (List LinT)) (ph : Array Ph) : Rep.Fit ⟨n, pOf g, (g 0).1, ph⟩ := by
  have := Nat.le_pow_clog (by norm_num : 1 < 2) (max (nrows (g 0).1) (nlocs (g 0).1))
  exact ⟨le_trans (le_max_left _ _) this, le_trans (le_max_right _ _) this⟩

/-- `n` instances of `g` at its stride. -/
def repA (n : ℕ) (g : GM (List LinT)) (ph : Array Ph) : SM (ℕ → List LinT) := SM.rep n (pOf g) g ph

theorem ok_repA {n : ℕ} {g : GM (List LinT)} {ph : Array Ph} (V : ℕ → List F)
    (hpat : ∀ s < n, ∀ e' : Env, e'.one = e.one → (∀ i, e'.inp i = (Rep.σ ⟨n, pOf g, (g 0).1, ph⟩ s i).ev e) →
      Eqns e' (g 0).1 0 → (g 0).2.map (LinT.ev e') = V s) :
    SM.Ok e (repA n g ph) fun res => ∀ s < n, (res s).map (LinT.ev e) = V s :=
  SM.ok_rep (fit_pOf n g ph) V hpat

/-! ## Chains -/

/-- The 127-step squaring chain of the `K` seed on inputs `0`, `1`, flat (`x^(2^i)`, `i ≤ 127`). -/
def chainP : GM (List LinT) := (sqChainK 127 (I 0, I 1)).map flatK

/-- **One chain per seed.** -/
def chainS (seeds : List KF) : SM (ℕ → List LinT) :=
  repA seeds.length chainP #[.var (seeds.map (·.1)).toArray, .var (seeds.map (·.2)).toArray]

theorem ok_chainS (seeds : List KF) :
    SM.Ok e (chainS seeds) fun res => ∀ b < seeds.length,
      (res b).map (LinT.ev e) = flatV ((List.range 128).map fun i => sqIter i (evK e (seeds.getD b zeroK))) := by
  refine ok_repA _ fun s hs e' _ hinp hE => ?_
  have h := ok_sqChainK (e := e') 127 (I 0, I 1) 0 hE
  have hseed : evK e' (I 0, I 1) = evK e (seeds.getD s zeroK) := by
    rw [List.getD_eq_getElem _ _ hs]
    apply K_ext'
    · show (I 0).ev e' = _; rw [ev_I, hinp]
      simp [Rep.σ, Ph.at, Array.getD_eq_getD_getElem?, hs, evK]
    · show (I 1).ev e' = _; rw [ev_I, hinp]
      simp [Rep.σ, Ph.at, Array.getD_eq_getD_getElem?, hs, evK]
  show (flatK _).map (LinT.ev e') = _
  rw [flatK_ev, h, hseed]

/-- A chain's stage-`k` value. -/
theorem evK_chain {l : List LinT} {x : K} (h : l.map (LinT.ev e) = flatV ((List.range 128).map fun i => sqIter i x))
    {k : ℕ} (hk : k < 128) : evK e (kfAt l k) = sqIter k x := by
  rw [evK_kfAt h (by simpa using hk)]; simp

/-! ## The blocks once -/

/-- A block's `W₀` and `G` (irregular: the fixed bits differ per block). -/
def blockOG (βp : List LinT) (qa ρa : ℕ → KF) (p : List (ℕ × Bool) × List ℕ) : GM (KF × KF) :=
  (prodK (ofFK (expSum βp p.2) :: p.1.map (selK qa))).bind fun w0 =>
  (prodK (p.1.map (selK ρa))).map fun g => (w0, g)

theorem ok_blockOG (h1 : e.one = 1) {βp : List LinT} {β : F} {E : ℕ}
    (hβ : βp.map (LinT.ev e) = (List.range (E + 1)).map (β ^ ·)) {qa ρa : ℕ → KF} {q ρ : ℕ → K}
    (hq : ∀ l, evK e (qa l) = q l) (hρ : ∀ l, evK e (ρa l) = ρ l) (p : List (ℕ × Bool) × List ℕ)
    (hp : ∀ i ∈ p.2, i ≤ E) : Ok e (blockOG βp qa ρa p) fun wg => (evK e wg.1, evK e wg.2) = (w0V β q p, gV ρ p) :=
  ok_bind (ok_prodK h1 _) fun w0 hw0 => ok_map (ok_prodK h1 _) fun g hg => (by
    have hw : evK e w0 = w0V β q p := by
      rw [hw0, List.map_cons, List.prod_cons, evK_ofFK, ev_expSum hβ hp, List.map_map, w0V]
      exact congrArg _ (congrArg _ (List.map_congr_left fun b _ => evK_selK h1 hq b))
    have hg' : evK e g = gV ρ p := by
      rw [hg, List.map_map, gV]
      exact congrArg _ (List.map_congr_left fun b _ => evK_selK h1 hρ b)
    simp only [hw, hg'])

/-! ## The kind factor at a stage (values per stage) -/

theorem ok_levelGS {k0 k : ℕ} {β : F} {q ρ : ℕ → K} {lvl : List (List KF × KF)}
    {g : List (List (ℕ × Bool) × List ℕ)}
    (hl : lvl.map (fun wg => (evK e (wg.1.getD k0 zeroK), evK e wg.2)) = g.map fun p => (sqIter k (w0V β q p), gV ρ p)) :
    Ok e (levelG k0 lvl) fun y => evK e y = (g.map fun p => sqIter k (w0V β q p) * gV ρ p).sum := by
  unfold levelG
  refine ok_map (ok_mapL (f := fun wg : List KF × KF => mulK (wg.1.getD k0 zeroK) wg.2) (E := evK e)
    (v := fun wg => evK e (wg.1.getD k0 zeroK) * evK e wg.2) lvl fun wg _ => ok_mulK _ _) fun ms hms => ?_
  rw [evK_sumK, hms]
  have := congrArg (fun l => (List.map (fun x : K × K => x.1 * x.2) l).sum) hl
  simp only [List.map_map] at this
  exact this

theorem ok_kindGS (h1 : e.one = 1) {k0 k : ℕ} {β : F} {q ρ : ℕ → K} {qk ρa : ℕ → KF}
    (hqk : ∀ l, evK e (qk l) = sqIter k (q l)) (hρ : ∀ l, evK e (ρa l) = ρ l)
    {bl : List (List (List KF × KF))} {sk : List (List (List (ℕ × Bool) × List ℕ))}
    (hbl : bl.map (List.map fun wg => (evK e (wg.1.getD k0 zeroK), evK e wg.2)) =
      sk.map (List.map fun p => (sqIter k (w0V β q p), gV ρ p))) :
    Ok e (kindG bl qk ρa k0) fun y => evK e y = kindV sk β q ρ k := by
  refine ok_bind (P := fun ys => ys.map (evK e) =
      sk.map fun g => (g.map fun p => sqIter k (w0V β q p) * gV ρ p).sum) ?_ fun ys hys =>
    ok_mono (ok_hornerKG _ 0 ys) fun y hy => by
      rw [hy, hys, kindV]
      congr 1
      funext l
      rw [evK_addE h1, hqk, hρ]
  have key : ∀ (bl : List (List (List KF × KF))) (sk : List (List (List (ℕ × Bool) × List ℕ))),
      bl.map (List.map fun wg => (evK e (wg.1.getD k0 zeroK), evK e wg.2)) =
        sk.map (List.map fun p => (sqIter k (w0V β q p), gV ρ p)) →
      Ok e (mapL (levelG k0) bl) fun ys => ys.map (evK e) =
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
        exact ok_bind (ok_levelGS h.1) fun y hy => ok_map (ih sk h.2) fun ys hys => by
          simp [hy, hys]
  exact key bl sk hbl


/-! ## Index lemmas -/

theorem getD_pairR {α : Type} (x y : ℕ → α) (d : α) : ∀ (n b : ℕ), b < n →
    ((List.range n).flatMap fun b => [x b, y b]).getD (2 * b) d = x b ∧
      ((List.range n).flatMap fun b => [x b, y b]).getD (2 * b + 1) d = y b
  | 0, _, h => absurd h (Nat.not_lt_zero _)
  | n + 1, b, h => by
    have hl : ((List.range n).flatMap fun b => [x b, y b]).length = 2 * n := by
      simp [List.length_flatMap]; ring
    rw [List.range_succ, List.flatMap_append, List.flatMap_singleton]
    rcases Nat.lt_succ_iff_lt_or_eq.1 h with h | rfl
    · rw [List.getD_append _ _ _ _ (by omega), List.getD_append _ _ _ _ (by omega)]
      exact getD_pairR x y d n b h
    · rw [List.getD_append_right _ _ _ _ (by omega), List.getD_append_right _ _ _ _ (by omega), hl]
      simp

theorem phOf_inpD {n p : ℕ} {g : List Gate} {c : Array LinT} {sl : List Src} {e' : Env} {s : ℕ}
    (h : ∀ i, e'.inp i = (Rep.σ ⟨n, p, g, phOf c sl⟩ s i).ev e) :
    (I 0).ev e' = (c.getD s []).ev e ∧ ∀ v < sl.length, evK e' (kv v) = evK e ((sl.getD v (.cst zeroK)).at s) := by
  refine ⟨(phOf_inp h).1, fun v hv => ?_⟩
  rw [(phOf_inp h).2 v hv, List.getD_eq_getElem _ _ hv]

/-! ## The stage groups -/

/-- **Stage group A's pattern** (`m = |ρ|`; the claims' shapes `pI`): per claim `j`, `c_k · eq` of its
stage coordinates with `ρ` (`j ≠ 1`), or `eq` of the first seven (`j = 1`: the kind factor's prefix).
Slots: `ρ` (`0 … m−1`), then the claims' stage coordinates, flat. -/
def patA (m : ℕ) (pI : List (List KF)) : GM (List LinT) :=
  (mapL (fun cj : List KF × ℕ => if cj.2 = 1 then
      prodK (List.zipWith addE (cj.1.take 7) (((List.range m).map kv).take 7))
    else (prodK (List.zipWith addE cj.1 ((List.range m).map kv))).bind (smulK (I 0)))
    (unflat pI ((List.range pI.flatten.length).map fun i => kv (m + i))).zipIdx).map flatK

/-- Group A's values: per claim. -/
def vA (ρ : List K) (c : F) (Q : List (List K)) : List K :=
  Q.zipIdx.map fun qj => if qj.2 = 1 then eqPtsC (qj.1.take 7) (ρ.take 7) else K.ofF c * eqPtsC qj.1 ρ

theorem unflat_vals {α : Type} {L : List (List α)} {Q : List (List K)} (hQ : Q.map List.length = L.map List.length)
    (f : ℕ → KF) (hq : ∀ i < L.flatten.length, evK e (f i) = Q.flatten.getD i 0) :
    (unflat L ((List.range L.flatten.length).map f)).map (List.map (evK e)) = Q := by
  have hn : L.flatten.length = Q.flatten.length := by simp [List.length_flatten, hQ]
  rw [← unflat_map, List.map_map, hn]
  rw [range_map_getElem Q.flatten id (evK e ∘ f) fun i hi => by
    simp only [Function.comp_apply, id]; rw [hq i (by omega), List.getD_eq_getElem _ _ hi]]
  rw [List.map_id]; exact unflat_flatten L Q hQ

theorem ok_patA (h1 : e.one = 1) {m : ℕ} {pI : List (List KF)} {ρ : List K} {c : F} {Q : List (List K)}
    (hρ : ((List.range m).map kv).map (evK e) = ρ) (hc : (I 0).ev e = c)
    (hQ : Q.map List.length = pI.map List.length)
    (hq : ∀ i < pI.flatten.length, evK e (kv (m + i)) = Q.flatten.getD i 0) :
    Ok e (patA m pI) fun r => r.map (LinT.ev e) = flatV (vA ρ c Q) := by
  have hcs := unflat_vals hQ (fun i => kv (m + i)) hq
  unfold patA
  refine ok_map (ok_mapL (E := evK e) (v := fun cj : List KF × ℕ => if cj.2 = 1 then
      eqPtsC ((cj.1.map (evK e)).take 7) (ρ.take 7) else K.ofF c * eqPtsC (cj.1.map (evK e)) ρ) _
    fun cj _ => ?_) fun ys hys => ?_
  · by_cases hj : cj.2 = 1
    · simp only [hj, if_true]
      exact ok_mono (ok_eqPtsC h1 _ _) fun o ho => by rw [ho, List.map_take, List.map_take, hρ]
    · simp only [hj, if_false]
      exact ok_bind (ok_eqPtsC h1 _ _) fun x hx => ok_mono (ok_smulK (I 0) x) fun o ho => by
        rw [ho, hx, hc, hρ]
  · rw [flatK_ev, hys, vA, ← hcs, List.zipIdx_map, List.map_map]
    rfl

/-- **Stage group B's pattern** (skeleton `sk`, `m = |ρ|`, `n1` claim 1's length): claim 1's kind factor
at the stage, times A's prefix, times `c_k`. Slots: per block `W₀^(2^k)` and `G` (`2b`, `2b+1`), `ρ`
(from `2nB`), claim 1's stage coordinates (from `2nB + m`), the prefix (`2nB + m + n1`). -/
def patB (sk : List (List (List (ℕ × Bool) × List ℕ))) (m n1 : ℕ) : GM (List LinT) :=
  ((kindG (unflat sk ((List.range sk.flatten.length).map fun b => ([kv (2 * b)], kv (2 * b + 1))))
      (fun l => (((List.range n1).map fun l => kv (2 * sk.flatten.length + m + l)).drop 7).getD l zeroK)
      (fun l => (((List.range m).map fun l => kv (2 * sk.flatten.length + l)).drop 7).getD l zeroK) 0).bind
    fun kf => (mulK (kv (2 * sk.flatten.length + m + n1)) kf).bind fun v => smulK (I 0) v).map
    fun x => [x.1, x.2]

theorem ok_patB (h1 : e.one = 1) {sk : List (List (List (ℕ × Bool) × List ℕ))} {m n1 k : ℕ} {β : F}
    {q ρ : ℕ → K} {qq ρl : List K} {H : K} {c : F}
    (hb : ∀ b < sk.flatten.length, evK e (kv (2 * b)) = sqIter k (w0V β q (sk.flatten.getD b ([], []))) ∧
      evK e (kv (2 * b + 1)) = gV ρ (sk.flatten.getD b ([], [])))
    (hq : ((List.range n1).map fun l => kv (2 * sk.flatten.length + m + l)).map (evK e) = qq)
    (hqq : ∀ l, (qq.drop 7).getD l 0 = sqIter k (q l))
    (hρl : ((List.range m).map fun l => kv (2 * sk.flatten.length + l)).map (evK e) = ρl)
    (hρ : ∀ l, (ρl.drop 7).getD l 0 = ρ l)
    (hH : evK e (kv (2 * sk.flatten.length + m + n1)) = H) (hc : (I 0).ev e = c) :
    Ok e (patB sk m n1) fun r => r.map (LinT.ev e) = flatV [K.ofF c * (H * kindV sk β q ρ k)] := by
  unfold patB
  have hbl : (unflat sk ((List.range sk.flatten.length).map fun b => ([kv (2 * b)], kv (2 * b + 1)))).map
      (List.map fun wg => (evK e (wg.1.getD 0 zeroK), evK e wg.2)) =
      sk.map (List.map fun p => (sqIter k (w0V β q p), gV ρ p)) := by
    rw [← unflat_map, List.map_map]
    rw [range_map_getElem sk.flatten (fun p => (sqIter k (w0V β q p), gV ρ p)) _ fun b hb' => by
      simp only [Function.comp_apply, List.getD_cons_zero]
      rw [(hb b hb').1, (hb b hb').2, List.getD_eq_getElem _ _ hb']]
    rw [List.map_flatten]
    exact unflat_flatten sk _ (by simp)
  refine ok_map (P := fun x => evK e x = K.ofF c * (H * kindV sk β q ρ k))
    (ok_bind (ok_kindGS (k0 := 0) h1 (q := q) (ρ := ρ) (fun l => ?_) (fun l => ?_) hbl) fun kf hkf =>
      ok_bind (ok_mulK _ kf) fun v hv => ok_mono (ok_smulK (I 0) v) fun o ho => ?_) fun x hx => ?_
  · rw [evK_getD, List.map_drop, hq, hqq]
  · rw [evK_getD, List.map_drop, hρl, hρ]
  · rw [ho, hv, hkf, hH, hc]
  · simp only [List.map_cons, List.map_nil, flatV, List.flatMap_cons, List.flatMap_nil, List.append_nil]
    rw [← hx]; rfl


/-! ## The template -/

/-- Chain `i`'s stage values (a slot source). -/
def srcCh (res : ℕ → List LinT) (i : ℕ) : Src := .var ((List.range 128).map fun k => kfAt (res i) k).toArray

/-- A stage group's `j`-th result per stage (a slot source). -/
def srcSt (res : ℕ → List LinT) (j : ℕ) : Src := .var ((List.range 128).map fun k => kfAt (res k) j).toArray

theorem rarr_getD {α : Type} (f : ℕ → α) (d : α) {s : ℕ} (hs : s < 128) :
    ((List.range 128).map f).toArray.getD s d = f s := by
  simp [Array.getD_eq_getD_getElem?, hs]

/-- **The node kind `ν`'s `rsWeight` template as segments** (inputs as `rsG`'s). -/
def rsGS (ν : NodeKind) (rI : List LinT) (pI : List (List KF)) (κI βI : LinT) (ρI : List KF) : SM KF :=
  (SM.lift (phiG rI)).bind fun cT =>
  (SM.lift (powF (maxE (skelAt ν (ρI.length - 7))) βI)).bind fun βp =>
  (SM.lift (mapL (blockOG βp (fun l => ((pI.getD 1 []).drop 7).getD l zeroK) (fun l => (ρI.drop 7).getD l zeroK))
    (skelAt ν (ρI.length - 7)).flatten)).bind fun bo =>
  (chainS (bo.map (·.1))).bind fun wch =>
  (SM.lift (powF pI.length κI)).bind fun κp =>
  (chainS pI.flatten).bind fun cch =>
  (repA 128 (patA ρI.length pI) (phOf ((List.range 128).map fun k => cT.getD k []).toArray
    (ρI.map Src.cst ++ (List.range pI.flatten.length).map (srcCh cch)))).bind fun ra =>
  (repA 128 (patB (skelAt ν (ρI.length - 7)) ρI.length (pI.getD 1 []).length)
    (phOf ((List.range 128).map fun k => cT.getD k []).toArray
      (((List.range (skelAt ν (ρI.length - 7)).flatten.length).flatMap fun b =>
        [srcCh wch b, Src.cst (bo.getD b (zeroK, zeroK)).2]) ++ (ρI.map Src.cst ++
        ((List.range (pI.getD 1 []).length).map (fun l => srcCh cch ((pI.getD 0 []).length + l)) ++
        [srcSt ra 1]))))).bind fun rb =>
  (SM.lift (mapL (fun j => smulK (κp.getD j []) (sumK ((List.range 128).map fun k =>
      if j = 1 then kfAt (rb k) 0 else kfAt (ra k) j))) (List.range pI.length))).map sumK

theorem getD_appR {α : Type} (P M : List α) (d : α) (x : ℕ) : (P ++ M).getD (P.length + x) d = M.getD x d := by
  rw [List.getD_append_right _ _ _ _ (by omega), Nat.add_sub_cancel_left]

theorem flatten_getD_one {α : Type} (L : List (List α)) (d : α) {l : ℕ} (hl : l < (L.getD 1 []).length) :
    L.flatten.getD ((L.getD 0 []).length + l) d = (L.getD 1 []).getD l d := by
  match L, hl with
  | a :: b :: L, hl =>
    simp only [List.getD_cons_zero, List.getD_cons_succ] at hl ⊢
    rw [List.flatten_cons, List.flatten_cons, List.getD_append_right _ _ _ _ (by omega), Nat.add_sub_cancel_left,
      List.getD_append _ _ _ _ hl]

/-- **`rsGS` computes `rsRef`** at the inputs' values. -/
theorem ok_rsGS (h1 : e.one = 1) (ν : NodeKind) {rI : List LinT} {pI : List (List KF)} {κI βI : LinT}
    {ρI : List KF} {r : List F} {ps : List (List K)} {κ β : F} {ρ : List K}
    (hr : rI.map (LinT.ev e) = r) (hp : pI.map (List.map (evK e)) = ps) (hκ : κI.ev e = κ)
    (hβ : βI.ev e = β) (hρ : ρI.map (evK e) = ρ) :
    SM.Ok e (rsGS ν rI pI κI βI ρI) fun o => evK e o = rsRef ν r ps κ β ρ := by
  have hlρ : ρI.length = ρ.length := by rw [← hρ, List.length_map]
  have hq0 : ∀ l, evK e (((pI.getD 1 []).drop 7).getD l zeroK) = ((ps.getD 1 []).drop 7).getD l 0 := fun l => by
    rw [take_drop_getD, ← hp, getD_map_nil _ rfl]
  have hρ0 : ∀ l, evK e ((ρI.drop 7).getD l zeroK) = (ρ.drop 7).getD l 0 := fun l => by
    rw [take_drop_getD, hρ]
  have hpf : pI.flatten.map (evK e) = ps.flatten := by rw [List.map_flatten, hp]
  have hpl : pI.length = ps.length := by rw [← hp, List.length_map]
  -- the values used below
  have hsq : ∀ s (x : List K) l, ((x.map (sqIter s)).drop 7).getD l 0 = sqIter s ((x.drop 7).getD l 0) := by
    intro s x l
    rw [← List.map_drop, List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, List.getElem?_map]
    cases (x.drop 7)[l]? <;> simp [sqIter_zeroK]
  set sk := skelAt ν (ρI.length - 7) with hsk
  simp only [rsGS]
  refine SM.ok_bind (SM.ok_lift (ok_phiG h1 rI)) fun cT hcT => ?_
  refine SM.ok_bind (SM.ok_lift (ok_powF h1 _ βI)) fun βp hβp => ?_
  refine SM.ok_bind (P := fun bo => bo.map (fun wg => (evK e wg.1, evK e wg.2)) = sk.flatten.map fun p =>
      (w0V β (fun l => ((ps.getD 1 []).drop 7).getD l 0) p, gV (fun l => (ρ.drop 7).getD l 0) p))
    (SM.ok_lift (ok_mapL _ fun p hp' => ok_blockOG h1 (hβ ▸ hβp) hq0 hρ0 p fun i hi => by
      obtain ⟨g, hg, hpg⟩ := List.mem_flatten.1 hp'
      exact le_maxE hg hpg hi)) fun bo hbo => ?_
  have hbl : bo.length = sk.flatten.length := by
    have := congrArg List.length hbo; rwa [List.length_map, List.length_map] at this
  have hbo' : ∀ b < sk.flatten.length, evK e (bo.getD b (zeroK, zeroK)).1 =
      w0V β (fun l => ((ps.getD 1 []).drop 7).getD l 0) (sk.flatten.getD b ([], [])) ∧
      evK e (bo.getD b (zeroK, zeroK)).2 = gV (fun l => (ρ.drop 7).getD l 0) (sk.flatten.getD b ([], [])) := by
    intro b hb
    have := congrArg (fun l => l[b]?) hbo
    simp only [List.getElem?_map, List.getElem?_eq_getElem (show b < bo.length by omega),
      List.getElem?_eq_getElem hb, Option.map_some, Option.some.injEq, Prod.mk.injEq] at this
    rw [List.getD_eq_getElem _ _ (by omega), List.getD_eq_getElem _ _ hb]
    exact this
  refine SM.ok_bind (ok_chainS _) fun wch hwch => ?_
  refine SM.ok_bind (SM.ok_lift (ok_powF h1 pI.length κI)) fun κp hκp => ?_
  refine SM.ok_bind (ok_chainS _) fun cch hcch => ?_
  -- the stage values
  have hch : ∀ i < pI.flatten.length, ∀ s < 128, evK e (kfAt (cch i) s) = sqIter s (ps.flatten.getD i 0) := by
    intro i hi s hs
    rw [evK_chain (hcch i hi) hs, ← hpf, List.getD_eq_getElem _ _ hi,
      List.getD_eq_getElem _ _ (by rw [List.length_map]; exact hi), List.getElem_map]
  set c : ℕ → F := fun s => (phiTable r).toList.getD s 0 with hc
  have hcs : ∀ s < 128, (((List.range 128).map fun k => cT.getD k []).toArray.getD s []).ev e = c s := by
    intro s hs
    rw [rarr_getD _ _ hs, ev_getD_lag, hcT, hr]
  have hsrc : ∀ (res : ℕ → List LinT) i s, s < 128 → (srcCh res i).at s = kfAt (res i) s := fun res i s hs => by
    simp only [srcCh, Src.at]; exact rarr_getD _ _ hs
  have hsrcS : ∀ (res : ℕ → List LinT) j s, s < 128 → (srcSt res j).at s = kfAt (res s) j := fun res j s hs => by
    simp only [srcSt, Src.at]; exact rarr_getD _ _ hs
  -- stage group A
  refine SM.ok_bind (ok_repA (fun s => flatV (vA ρ (c s) (ps.map (List.map (sqIter s)))))
    fun s hs e' hone hinp hE => ?_) fun ra hra => ?_
  · obtain ⟨hc0, hsl⟩ := phOf_inpD hinp
    have hlen : (ρI.map Src.cst ++ (List.range pI.flatten.length).map (srcCh cch)).length =
        ρI.length + pI.flatten.length := by simp
    refine ok_patA (e := e') (by rw [hone, h1]) (ρ := ρ) (c := c s) (Q := ps.map (List.map (sqIter s))) ?_
      (by rw [hc0, hcs s hs]) (by rw [← hp]; simp [Function.comp_def]) ?_ 0 hE
    · refine List.ext_getElem (by simp [hlρ]) fun v h1' h2' => ?_
      have hv : v < ρI.length := by simpa using h1'
      rw [List.getElem_map, List.getElem_map, List.getElem_range, hsl v (by rw [hlen]; omega),
        List.getD_append _ _ _ _ (by simpa using hv), List.getD_eq_getElem _ _ (by simpa using hv), List.getElem_map]
      simp only [Src.at]; subst hρ; simp
    · intro i hi
      have hi' : i < ps.flatten.length := by rw [← hpf, List.length_map]; exact hi
      rw [hsl (ρI.length + i) (by rw [hlen]; omega),
        show ρI.length + i = (ρI.map Src.cst).length + i by rw [List.length_map], getD_appR,
        List.getD_eq_getElem _ _ (by simpa using hi), List.getElem_map, List.getElem_range, hsrc _ _ _ hs,
        hch i hi s hs, ← List.map_flatten, List.getD_eq_getElem _ _ hi',
        List.getD_eq_getElem _ _ (by rw [List.length_map]; exact hi'), List.getElem_map]
  -- stage group B
  refine SM.ok_bind (ok_repA (fun s => flatV [K.ofF (c s) * (evK e (kfAt (ra s) 1) *
      kindV sk β (fun l => ((ps.getD 1 []).drop 7).getD l 0) (fun l => (ρ.drop 7).getD l 0) s)])
    fun s hs e' hone hinp hE => ?_) fun rb hrb => ?_
  · obtain ⟨hc0, hsl⟩ := phOf_inpD hinp
    set nB := sk.flatten.length with hnB
    set n1 := (pI.getD 1 []).length with hn1d
    set P := (List.range nB).flatMap fun b => [srcCh wch b, Src.cst (bo.getD b (zeroK, zeroK)).2] with hP
    set Cs := (List.range n1).map (fun l => srcCh cch ((pI.getD 0 []).length + l)) with hCs
    have hlP : P.length = 2 * nB := by simp [hP, List.length_flatMap]; ring
    have hn1 : n1 = (ps.getD 1 []).length := by rw [hn1d, ← hp, getD_map_nil _ rfl, List.length_map]
    have hlen : (P ++ (ρI.map Src.cst ++ (Cs ++ [srcSt ra 1]))).length = 2 * nB + (ρI.length + (n1 + 1)) := by
      simp [hlP, hCs]
    have hsl' : ∀ x < ρI.length + (n1 + 1), evK e' (kv (2 * nB + x)) =
        evK e (((ρI.map Src.cst ++ (Cs ++ [srcSt ra 1])).getD x (.cst zeroK)).at s) := fun x hx => by
      rw [hsl _ (by rw [hlen]; omega), ← hlP, getD_appR]
    refine ok_patB (e := e') (by rw [hone, h1]) (k := s) (β := β) (q := fun l => ((ps.getD 1 []).drop 7).getD l 0)
      (ρ := fun l => (ρ.drop 7).getD l 0) (qq := (ps.getD 1 []).map (sqIter s)) (ρl := ρ)
      (H := evK e (kfAt (ra s) 1)) (c := c s) (fun b hb => ?_) ?_ (fun l => hsq s _ l) ?_ (fun l => rfl) ?_
      (by rw [hc0, hcs s hs]) 0 hE
    · rw [← hnB] at hb
      have hp2 := getD_pairR (fun b => srcCh wch b) (fun b => Src.cst (bo.getD b (zeroK, zeroK)).2) (Src.cst zeroK) nB b hb
      have hw := hwch b (by rw [List.length_map]; omega)
      have hb0 : (bo.map (·.1)).getD b zeroK = (bo.getD b (zeroK, zeroK)).1 := by
        rw [List.getD_eq_getElem _ _ (by rw [List.length_map]; omega), List.getD_eq_getElem _ _ (by omega),
          List.getElem_map]
      constructor
      · rw [hsl (2 * b) (by rw [hlen]; omega), List.getD_append _ _ _ _ (by rw [hlP]; omega), hp2.1,
          hsrc _ _ _ hs, evK_chain hw hs, hb0, (hbo' b hb).1]
      · rw [hsl (2 * b + 1) (by rw [hlen]; omega), List.getD_append _ _ _ _ (by rw [hlP]; omega), hp2.2]
        exact (hbo' b hb).2
    · refine List.ext_getElem (by simp [hn1]) fun l h1' h2' => ?_
      have hl : l < n1 := by simpa using h1'
      have h2 : 2 ≤ pI.length := by
        by_contra hc'; push_neg at hc'
        have : n1 = 0 := by rw [hn1d, List.getD_eq_default _ _ (by omega)]; rfl
        omega
      have hlt : (pI.getD 0 []).length + l < pI.flatten.length := by
        match pI, h2 with
        | a :: b :: L, _ =>
          simp only [List.getD_cons_zero, List.getD_cons_succ, hn1d] at hl ⊢
          simp only [List.flatten_cons, List.length_append]; omega
      rw [List.getElem_map, List.getElem_map, List.getElem_range, show 2 * nB + ρI.length + l = 2 * nB + (ρI.length + l) by ring,
        hsl' _ (by omega), show ρI.length + l = (ρI.map Src.cst).length + l by rw [List.length_map], getD_appR,
        List.getD_append _ _ _ _ (by simpa [hCs] using hl), List.getD_eq_getElem _ _ (by simpa [hCs] using hl)]
      simp only [hCs, List.getElem_map, List.getElem_range]
      rw [hsrc _ _ _ hs, hch _ hlt s hs]
      congr 1
      have := flatten_getD_one ps 0 (l := l) (by rw [← hn1]; exact hl)
      rw [show (pI.getD 0 []).length = (ps.getD 0 []).length by rw [← hp, getD_map_nil _ rfl, List.length_map],
        this, List.getD_eq_getElem _ _ (by rw [← hn1]; exact hl)]
    · refine List.ext_getElem (by simp [hlρ]) fun v h1' h2' => ?_
      have hv : v < ρI.length := by simpa using h1'
      rw [List.getElem_map, List.getElem_map, List.getElem_range, hsl' v (by omega),
        List.getD_append _ _ _ _ (by simpa using hv), List.getD_eq_getElem _ _ (by simpa using hv), List.getElem_map]
      simp only [Src.at]; subst hρ; simp
    · rw [show 2 * nB + ρI.length + n1 = 2 * nB + (ρI.length + n1) by ring, hsl' _ (by omega),
        show ρI.length + n1 = (ρI.map Src.cst).length + n1 by rw [List.length_map], getD_appR,
        show n1 = Cs.length by simp [hCs], List.getD_append_right _ _ _ _ (le_refl _), Nat.sub_self]
      simp only [List.getD_cons_zero]
      rw [hsrcS _ _ _ hs]
  -- the claims
  refine SM.ok_map (SM.ok_lift (ok_mapL (E := evK e)
    (v := fun j => K.ofF (κ ^ j) * claimV ν (phiTable r).toList β ρ (ps.getD j []) j) (List.range pI.length)
    fun j hj => ok_mono (ok_smulK _ _) fun o ho => ?_)) fun vs hvs => ?_
  · have hj0 := List.mem_range.1 hj
    have hj' : j < ps.length := by rw [← hpl]; exact hj0
    rw [ho, ev_getD_pow hκp (by omega), hκ, evK_sumK, List.map_map, claimV]
    refine congrArg _ (congrArg List.sum (List.map_congr_left fun k hk => ?_))
    have hk' := List.mem_range.1 hk
    have hA := hra k hk'
    have hlA : (vA ρ (c k) (ps.map (List.map (sqIter k)))).length = ps.length := by simp [vA]
    simp only [Function.comp_apply]
    by_cases h1j : j = 1
    · subst h1j
      rw [if_pos rfl, evK_kfAt (hrb k hk') (by simp), List.getElem_singleton, evK_kfAt hA (by rw [hlA]; exact hj')]
      simp only [vA, List.getElem_map, List.getElem_zipIdx, if_true, termV, hlρ, sk]
      rw [List.getD_eq_getElem _ _ hj']
    · rw [if_neg h1j, evK_kfAt hA (by rw [hlA]; exact hj')]
      simp only [vA, List.getElem_map, List.getElem_zipIdx, termV, h1j, if_false, zero_add]
      rw [List.getD_eq_getElem _ _ hj']
  · rw [evK_sumK, hvs, rsRef]
    refine congrArg List.sum (List.ext_getElem (by simp [hpl]) fun j h1' h2' => ?_)
    simp only [List.getElem_map, List.getElem_range, List.getElem_zipIdx, zero_add, claimV]
    rw [List.getD_eq_getElem _ _ (by simpa [hpl] using h1')]

end Tpl
end FR
