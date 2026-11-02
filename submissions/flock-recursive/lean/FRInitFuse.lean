-- G6: this module also holds the former modules `FRNodeRows4RepFD`, `FRVIRTplCFE`, `FRNodeRows4RepCFP` (one section each, in import order).
import FRNodeRows4
import FRNodeRows4RepCFRs
import FRNodeRows4AskB

section G6_FRNodeRows4RepFD

-- New for `flock-recursive` (track REPF; C1b-RESULT §5.2): the replay rows at process start, in the
-- ask rows' memoized pass, and their split into the frame and local parts the plan evaluates.

/-!
# The replay rows from the memoized trail (the fold lemma)

* **`trailMR`**: ASK-P's memoized trail (`trailMS`: the template memo of `compMSX`) carrying a second
  accumulator, the replay template's rows. One pass gives a prototype's ask rows and its replay rows,
  without C1's second (un-memoized) compile.
* **`trailMR_eq`**: its two accumulators are `trailRows` and `repRowsX` (reversed onto them). Hence
  **`repRowsP_trail`** (`repRowsP rt π` is the second component from a fresh state): the fold lemma
  the plan's rows need. It holds for every `RT`; no locality or SSA property of the templates is used.
* **`repLocF`/`repLocL`**: a replay row list in local coordinates (row `k`, cells below `2^20`): the
  frame part (cells `< repB`) and the local part (cells `≥ repB`, moved down by `repB`). The plan
  evaluates them once per call and combines them per kind (`FRNodeRows4Plan.repV0_eq`).
-/

namespace FR
namespace Rev4
open RecursionFast Circ TEval Tpl

/-- **The memoized trail with the replay rows** (`trailMS` plus a second accumulator). -/
def trailMR (X : TCtx → Ext) (L : TLay) (P : Params) (G : TG) (rt : RT) :
    List (TKey × Tpl) → CS → Option Op → ℕ → List Op → List Row → List Row → List Row × List Row
  | _, _, _, _, [], acc, acr => (acc, acr)
  | M, cs, pre, k, op :: ops, acc, acr =>
    let c := cs.align (alignOf op ops)
    let acc := (if op.item?.isSome || G.cov op then G.rows P c pre op k else []).reverseAux acc
    let M := memoAdd M ((X ⟨fun _ => ⟨[], []⟩, L.cb⟩ P c op).bind (·.tin))
    let o := stepOut (X ⟨tlook M, L.cb⟩) P c op
    let acr := (if rt.cov op then rt.rows P c op o.slots else []).reverseAux acr
    trailMR X L P G rt (memoAdd M o.tin) (c.add op o) (some op) (if op.item?.isSome then k + 1 else k) ops acc acr

/-- **`trailMR` is `trailRows` and `repRowsX`** (each reversed onto its accumulator), for a memo of
`tplOf`'s templates. -/
theorem trailMR_eq (X : TCtx → Ext) (L : TLay) (P : Params) (G : TG) (rt : RT) :
    ∀ (ops : List Op) (M : List (TKey × Tpl)) (cs : CS) (pre : Option Op) (k : ℕ) (acc acr : List Row),
      MOk M → trailMR X L P G rt M cs pre k ops acc acr =
        ((trailRows (X L.ctx) P G cs pre k ops).reverse ++ acc, (repRowsX (X L.ctx) P rt cs ops).reverse ++ acr)
  | [], _, _, _, _, _, _, _ => rfl
  | op :: ops, M, cs, pre, k, acc, acr, h => by
    have hc : ∀ x, (⟨tlook (memoAdd M x), L.cb⟩ : TCtx) = L.ctx := fun x => by
      rw [tlook_eq (memoAdd_ok h x)]; rfl
    simp only [trailMR, trailRows, repRowsX, hc]
    rw [trailMR_eq X L P G rt ops _ _ _ _ _ _ (memoAdd_ok (memoAdd_ok h _) _), List.reverseAux_eq,
      List.reverseAux_eq, List.reverse_append, List.reverse_append, List.append_assoc, List.append_assoc]

/-- **A prototype's ask rows and replay rows in one memoized pass** (the plan's). -/
def arRepOf (π : ℕ) : List Row × List Row :=
  let r := trailMR (N4s.XofC π) (protoLay π) (protoP π) (askTG π) (N4s.rtC1d π) []
    (CS.init (baseR π)) none 0 (protoProg π).ops [] []
  (r.1.reverse, r.2.reverse)

/-- **The fold lemma**: the pass gives `askRowsT π` and `repRowsP (rtC1d π) π`. -/
theorem arRepOf_eq (π : ℕ) : arRepOf π = (askRowsT π, N4s.repRowsP (N4s.rtC1d π) π) := by
  unfold arRepOf
  rw [trailMR_eq _ _ _ _ _ _ _ _ _ _ _ _ (by simp [MOk])]
  simp only [List.append_nil, List.reverse_reverse]
  rfl

/-- **`repRowsP` from the memoized trail** (for every replay template). -/
theorem repRowsP_trail (rt : RT) (π : ℕ) :
    N4s.repRowsP rt π = ((trailMR (N4s.XofC π) (protoLay π) (protoP π) TG.none rt []
      (CS.init (baseR π)) none 0 (protoProg π).ops [] []).2).reverse := by
  rw [trailMR_eq _ _ _ _ _ _ _ _ _ _ _ _ (by simp [MOk])]
  simp only [List.append_nil, List.reverse_reverse]
  rfl

/-! ## Local coordinates -/

/-- A form's frame part (cells below `repB`). -/
def linFr (l : Lin) : Lin := l.filter fun t => decide (t.1 < N4s.repB)

/-- A form's local part (cells at or above `repB`), moved down by `repB`. -/
def linLoc (l : Lin) : Lin := (l.filter fun t => !decide (t.1 < N4s.repB)).map fun t => (t.1 - N4s.repB, t.2)

def rowFr (r : Row) : Row := ⟨linFr r.a, linFr r.b, linFr r.c⟩
def rowLoc (r : Row) : Row := ⟨linLoc r.a, linLoc r.b, linLoc r.c⟩

/-- **The replay rows' frame part** at rows `k` (local coordinates). -/
def repLocF (rows : List Row) : List (ℕ × Row) := rows.zipIdx.map fun p => (p.2, rowFr p.1)

/-- **The replay rows' local part** at rows `k`, cells `c − repB`. -/
def repLocL (rows : List Row) : List (ℕ × Row) := rows.zipIdx.map fun p => (p.2, rowLoc p.1)

theorem r_rowFr (s : TEval.Mat) (r : Row) : s.r (rowFr r) = linFr (s.r r) := by cases s <;> rfl
theorem r_rowLoc (s : TEval.Mat) (r : Row) : s.r (rowLoc r) = linLoc (s.r r) := by cases s <;> rfl

/-- (+) A frame cell goes to the frame part, a local to the local part moved down; (−) neither part keeps
the other's term. -/
theorem linFr_ctl : linFr [(5, 2), (N4s.repB + 7, 3)] = [(5, 2)] ∧
    linLoc [(5, 2), (N4s.repB + 7, 3)] = [(7, 3)] := by
  simp only [linFr, linLoc, N4s.repB]; decide

end Rev4
end FR

end G6_FRNodeRows4RepFD

section G6_FRVIRTplCFE

-- New for `flock-recursive` (track CF): segments prepared once, evaluated per call.

/-!
# Segments prepared for evaluation

`sgVal` rebuilds a segment's rows at every call. **`prepS`** builds them once (an irregular
segment's rows, a repeated pattern's pattern rows); **`psVal`** evaluates the prepared segments with
the row weights `gt` (split tables: one product per row); **`psVal_eq`**: it is `sgVal`.
-/

namespace FR
namespace Tpl
open Circ TEval

/-- `tm` with the row weights `gt` (a fold). -/
def tmG (s : Mat) (gt : ℕ → F) (e : Env) (X : ℕ) (rows : List RowT) : F :=
  (rows.foldl (fun (p : F × ℕ) r => (p.1 + gt p.2 * (s.t r).ev e, p.2 + 1)) (0, X)).1

theorem tmG_go (s : Mat) (gt : ℕ → F) (t : ℕ → F) (e : Env) (hgt : ∀ x, gt x = gN 20 t x) :
    ∀ (rows : List RowT) (a : F) (X : ℕ),
      rows.foldl (fun (p : F × ℕ) r => (p.1 + gt p.2 * (s.t r).ev e, p.2 + 1)) (a, X) = (a + tm s t e X rows, X + rows.length)
  | [], a, X => by simp [tm]
  | r :: rows, a, X => by
    rw [List.foldl_cons, tmG_go s gt t e hgt rows, tm, hgt, List.length_cons]
    ext <;> simp only <;> ring

theorem tmG_eq (s : Mat) (gt t : ℕ → F) (e : Env) (hgt : ∀ x, gt x = gN 20 t x) (X : ℕ) (rows : List RowT) :
    tmG s gt e X rows = tm s t e X rows := by
  rw [tmG, tmG_go s gt t e hgt]; simp

/-- A prepared segment: its rows (at row `X`), or a fitting repeated pattern and its pattern's rows. -/
inductive PS where
  | rows (X : ℕ) (rs : List RowT)
  | rep (X K : ℕ) (R : Rep) (pr : List RowT)

/-- **The segments, prepared** (rows from `X`, locals from `K`). -/
def prepS : ℕ → ℕ → List SG → List PS
  | _, _, [] => []
  | X, K, .irr gs :: l => .rows X (rowsAt gs K) :: prepS (X + nrows gs) (K + nlocs gs) l
  | X, K, .rep R :: l =>
    (if R.p ≤ 20 ∧ R.Fit then .rep X K R (rowsAt R.pat 0) else .rows X (rowsAt (R.gates K) K)) ::
      prepS (X + R.n * nrows R.padP) (K + R.n * nlocs R.padP) l

/-- **The prepared segments' value**, rows from `X0` on. -/
def psVal (s : Mat) (gt t u : ℕ → F) (e : Env) (lam : F) (cl X0 : ℕ) : List PS → F
  | [] => 0
  | .rows X rs :: l => tmG s gt e (X0 + X) rs + psVal s gt t u e lam cl X0 l
  | .rep X K R pr :: l => R.pass s (R.ctx t u e cl (X0 + X) K) t u e lam cl (X0 + X) K 0 pr +
      psVal s gt t u e lam cl X0 l

theorem psVal_eq (s : Mat) (gt t u : ℕ → F) (e : Env) (lam : F) (cl X0 : ℕ) (hgt : ∀ x, gt x = gN 20 t x)
    (he : ∀ x, e.loc x = lam * gN 20 u (cl + x)) :
    ∀ (X K : ℕ) (l : List SG), psVal s gt t u e lam cl X0 (prepS X K l) = sgVal s t u e lam cl (X0 + X) K l
  | _, _, [] => rfl
  | X, K, .irr gs :: l => by
    rw [prepS, psVal, sgVal, tmG_eq s gt t e hgt, psVal_eq s gt t u e lam cl X0 hgt he _ _ l, Nat.add_assoc]
  | X, K, .rep R :: l => by
    have ih := psVal_eq s gt t u e lam cl X0 hgt he (X + R.n * nrows R.padP) (K + R.n * nlocs R.padP) l
    rw [← Nat.add_assoc] at ih
    rw [prepS, sgVal]
    split_ifs with h
    · rw [psVal, ih]
    · rw [psVal, ih, tmG_eq s gt t e hgt]

/-- A segment list's rows. -/
def sgNr (l : List SG) : ℕ := (l.map fun g => match g with | .irr gs => nrows gs | .rep R => R.n * nrows R.padP).sum

theorem nrows_sgGates : ∀ (l : List SG) (K : ℕ), nrows (sgGates l K) = sgNr l
  | [], _ => rfl
  | .irr gs :: l, K => by rw [sgGates, nrows_append, nrows_sgGates l]; simp [sgNr, SG.gates]
  | .rep R :: l, K => by
    rw [sgGates, nrows_append, nrows_sgGates l]; simp [sgNr, SG.gates, Rep.gates, R.nrows_gatesN]


/-! ## Bounds on the locals a segment list's rows read -/

/-- Every local of the form is below `M`. -/
def locLt (M : ℕ) (l : LinT) : Bool := l.all fun t => match t.1 with | .loc k => decide (k < M) | _ => true

def rowLocLt (M : ℕ) (r : RowT) : Bool := locLt M r.a && locLt M r.b && locLt M r.c

def Ph.locLt (M : ℕ) : Ph → Bool
  | .cst f => Tpl.locLt M f
  | .var fs => fs.toList.all (Tpl.locLt M)

/-- The prepared segments' check: their rows' locals below `M`. -/
def psLocOk (M : ℕ) : List PS → Bool
  | [] => true
  | .rows _ rs :: l => rs.all (rowLocLt M) && psLocOk M l
  | .rep _ K R pr :: l => pr.all (rowLocLt (2 ^ R.p)) && R.ph.toList.all (Ph.locLt M) &&
      decide (K + R.n * 2 ^ R.p ≤ M) && psLocOk M l

theorem locLt_iff {M : ℕ} {l : LinT} : locLt M l = true ↔ ∀ k c, (Wire.loc k, c) ∈ l → k < M := by
  unfold locLt
  rw [List.all_eq_true]
  constructor
  · intro h k c hm; simpa using h _ hm
  · rintro h ⟨w, c⟩ hm
    cases w with
    | loc k => simpa using h _ _ hm
    | _ => rfl

theorem locLt_subW {M m k0 : ℕ} {σ : ℕ → LinT} {l : LinT} (hl : locLt m l = true) (hσ : ∀ i, locLt M (σ i) = true)
    (hk : k0 + m ≤ M) : locLt M (subW σ k0 l) = true := by
  rw [locLt_iff] at hl ⊢
  intro k c hm
  obtain ⟨⟨w, d⟩, hw, hm⟩ := List.mem_flatMap.1 hm
  cases w with
  | one => simp at hm
  | inp i =>
    obtain ⟨⟨w', d'⟩, hw', he⟩ := List.mem_map.1 hm
    simp only [Prod.mk.injEq] at he
    rw [he.1] at hw'
    exact locLt_iff.1 (hσ i) _ _ hw'
  | loc k' =>
    simp only [List.mem_singleton, Prod.mk.injEq, Wire.loc.injEq] at hm
    have := hl k' d hw; omega

theorem rowLocLt_sub {M m k0 : ℕ} {σ : ℕ → LinT} {r : RowT} (hr : rowLocLt m r = true)
    (hσ : ∀ i, locLt M (σ i) = true) (hk : k0 + m ≤ M) : rowLocLt M (r.sub σ k0) = true := by
  simp only [rowLocLt, Bool.and_eq_true] at hr ⊢
  exact ⟨⟨locLt_subW hr.1.1 hσ hk, locLt_subW hr.1.2 hσ hk⟩, locLt_subW hr.2 hσ hk⟩

theorem rowLocLt_mono {m M : ℕ} (h : m ≤ M) {r : RowT} (hr : rowLocLt m r = true) : rowLocLt M r = true := by
  have hm : ∀ {l : LinT}, locLt m l = true → locLt M l = true := fun hl =>
    locLt_iff.2 fun k c hk => lt_of_lt_of_le (locLt_iff.1 hl k c hk) h
  simp only [rowLocLt, Bool.and_eq_true] at hr ⊢
  exact ⟨⟨hm hr.1.1, hm hr.1.2⟩, hm hr.2⟩

theorem empty_rowLocLt (M : ℕ) : rowLocLt M ⟨[], [], []⟩ = true := rfl

/-- **The check bounds the locals of the segments' rows.** -/
theorem psLocOk_rows (M : ℕ) : ∀ (X K : ℕ) (l : List SG), psLocOk M (prepS X K l) = true →
    ∀ r ∈ rowsAt (sgGates l K) K, rowLocLt M r = true
  | _, _, [], _, r, hr => by simp [sgGates] at hr
  | X, K, .irr gs :: l, h, r, hr => by
    simp only [prepS, psLocOk, Bool.and_eq_true, List.all_eq_true] at h
    rw [sgGates, rowsAt_append, List.mem_append] at hr
    rcases hr with hr | hr
    · exact h.1 r hr
    · rw [SG.nlocs_gates] at hr; exact psLocOk_rows M _ _ l h.2 r hr
  | X, K, .rep R :: l, h, r, hr => by
    simp only [prepS] at h
    rw [sgGates, rowsAt_append, List.mem_append] at hr
    split_ifs at h with hf
    · simp only [psLocOk, Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq] at h
      rcases hr with hr | hr
      · simp only [SG.gates, Rep.gates] at hr
        rw [R.rowsAt_gatesN hf.2 K] at hr
        obtain ⟨s, hs, hr⟩ := List.mem_flatMap.1 hr
        obtain ⟨r0, hr0, rfl⟩ := List.mem_map.1 hr
        rw [Rep.padP, rowsAt_append, List.mem_append] at hr0
        have hs' := List.mem_range.1 hs
        have hk : K + s * 2 ^ R.p + 2 ^ R.p ≤ M := by
          have h2 := Nat.mul_le_mul_right (2 ^ R.p) (Nat.succ_le_of_lt hs')
          rw [Nat.succ_mul] at h2
          have := h.1.2; linarith
        have hσ : ∀ i, locLt M (R.σ s i) = true := fun i => by
          unfold Rep.σ
          have hph : (R.ph.getD i (.cst [])).locLt M = true := by
            rw [Array.getD_eq_getD_getElem?]
            cases hi : R.ph[i]? with
            | none => rfl
            | some x => exact h.1.1.2 x (List.mem_of_getElem? (by rw [Array.getElem?_toList]; exact hi))
          revert hph
          cases R.ph.getD i (.cst []) with
          | cst f => exact id
          | var fs =>
            intro hph
            simp only [Ph.locLt, List.all_eq_true] at hph
            simp only [Ph.at, Array.getD_eq_getD_getElem?]
            cases hj : fs[s]? with
            | none => rfl
            | some f => exact hph f (List.mem_of_getElem? (by rw [Array.getElem?_toList]; exact hj))
        rcases hr0 with hr0 | hr0
        · exact rowLocLt_sub (h.1.1.1 r0 hr0) hσ hk
        · simp [rowsAt_cons, Gate.rows] at hr0
          rw [hr0.2]; exact empty_rowLocLt M
      · rw [SG.nlocs_gates] at hr; exact psLocOk_rows M _ _ l h.2 r hr
    · simp only [psLocOk, Bool.and_eq_true, List.all_eq_true] at h
      rcases hr with hr | hr
      · exact h.1 r hr
      · rw [SG.nlocs_gates] at hr; exact psLocOk_rows M _ _ l h.2 r hr

end Tpl
end FR

end G6_FRVIRTplCFE

section G6_FRNodeRows4RepCFP

-- New for `flock-recursive` (track CF): the replay rows' value with `rsWeight`'s block in closed form.

/-!
# The replay rows' local values, blocks and closed forms

REPF evaluates prototype 0's replay rows (`repRowsP (rtC1c 0) 0`, ≈ 846 k rows) sparse in local
coordinates (`repLocF`: the frame part, `repLocL`: the local part). Here:

* **`rm s t w X rows`**: rows `X, X+1, …` at the row point `t`, the cells at `w`. `repLocF`'s value is
  `rm` at `wF` (`eq(u, ·)` below `repB`), `repLocL`'s at `wL` (`eq(u, · − repB)` above)
  (`rowsVal_locF`, `rowsVal_locL`).
* **`rm_inst`**: instantiated template rows are the template rows at `envOf w one ins cb`.
* **`tm_subsG`**: the kind mux's sub-templates, each at its substituted wires (`pullE`).
* **`KPrep`/`kopV`**: an `rsWeight` op's rows (`kRows kRS`), prepared once (the three kinds'
  segments, the mux rows, the copy rows) and evaluated per call: **`kopV_eq`**.
-/

namespace FR
namespace N4s
open RecursionFast Rev4 Circ Tpl

-- moved here from `FRNodeRows4RepK` (CF2: the plan imports this module, not `FRNodeRows4RepK`)
theorem gatesAtGo_eq : ∀ (gs : List Gate) (k : ℕ) (acc : List (ℕ × Gate)),
    gatesAtGo gs k acc = (gatesAt gs k).reverse ++ acc
  | [], _, _ => rfl
  | g :: gs, k, acc => by
    rw [gatesAtGo, gatesAtGo_eq gs, gatesAt, List.reverse_cons, List.append_assoc]; rfl

theorem rowsTR_eq (T : Tpl) : rowsTR T = T.rows := by
  rw [rowsTR, gatesAtGo_eq, List.append_nil, List.reverse_reverse]; rfl

end N4s

namespace Rev4
open RecursionFast Circ TEval Tpl

/-! ## Rows at cell weights -/

/-- Rows `X, X+1, …`' value (matrix `s`) at the row point `t` (20 coordinates), cells weighted by `w`. -/
def rm (s : Mat) (t : ℕ → F) (w : Asg) : ℕ → List Row → F
  | _, [] => 0
  | X, r :: rs => gN 20 t X * (s.r r).ev w + rm s t w (X + 1) rs

theorem rm_append (s : Mat) (t : ℕ → F) (w : Asg) :
    ∀ (X : ℕ) (a b : List Row), rm s t w X (a ++ b) = rm s t w X a + rm s t w (X + a.length) b
  | _, [], _ => by simp [rm]
  | X, r :: a, b => by
    rw [List.cons_append, rm, rm, rm_append s t w (X + 1) a b, List.length_cons]
    rw [show X + 1 + a.length = X + (a.length + 1) by omega]; ring

/-- The frame part's cell weights: `eq(u, c)` below `repB`. -/
def wF (u : ℕ → F) : Asg := fun c => if c < N4s.repB then gN 20 u c else 0

/-- The local part's cell weights: `eq(u, c − repB)` from `repB`. -/
def wL (u : ℕ → F) : Asg := fun c => if c < N4s.repB then 0 else gN 20 u (c - N4s.repB)

theorem linE_filt (u : ℕ → F) (B : ℕ) : ∀ l : Lin,
    linE (RingHom.id F) 20 u (l.filter fun t => decide (t.1 < B)) = l.ev (fun c => if c < B then gN 20 u c else 0)
  | [] => by simp [linE, Lin.ev]
  | q :: l => by
    have ih := linE_filt u B l
    simp only [linE, Lin.ev, RingHom.id_apply] at ih ⊢
    by_cases h : q.1 < B
    · rw [List.filter_cons_of_pos (by simpa using h)]
      simp only [List.map_cons, List.sum_cons, ih, if_pos h]
    · rw [List.filter_cons_of_neg (by simpa using h), ih]
      simp only [List.map_cons, List.sum_cons, if_neg h, mul_zero, zero_add]

theorem linE_filtL (u : ℕ → F) (B : ℕ) : ∀ l : Lin,
    linE (RingHom.id F) 20 u ((l.filter fun t => !decide (t.1 < B)).map fun t => (t.1 - B, t.2)) =
      l.ev (fun c => if c < B then 0 else gN 20 u (c - B))
  | [] => by simp [linE, Lin.ev]
  | q :: l => by
    have ih := linE_filtL u B l
    simp only [linE, Lin.ev, RingHom.id_apply, List.map_map] at ih ⊢
    by_cases h : q.1 < B
    · rw [List.filter_cons_of_neg (by simpa using h), ih]
      simp only [List.map_cons, List.sum_cons, if_pos h, mul_zero, zero_add]
    · rw [List.filter_cons_of_pos (by simpa using h)]
      simp only [List.map_cons, List.sum_cons, Function.comp_apply, ih, if_neg h]

theorem linE_linFr (u : ℕ → F) (l : Lin) : linE (RingHom.id F) 20 u (linFr l) = l.ev (wF u) :=
  linE_filt u N4s.repB l

theorem linE_linLoc (u : ℕ → F) (l : Lin) : linE (RingHom.id F) 20 u (linLoc l) = l.ev (wL u) :=
  linE_filtL u N4s.repB l

theorem Mat.r_rowFr (s : Mat) (r : Row) : s.r (rowFr r) = linFr (s.r r) := by cases s <;> rfl
theorem Mat.r_rowLoc (s : Mat) (r : Row) : s.r (rowLoc r) = linLoc (s.r r) := by cases s <;> rfl

theorem rowsVal_locF (s : Mat) (t u : ℕ → F) :
    ∀ (X : ℕ) (R : List Row), rowsVal (RingHom.id F) s 20 20 t u ((R.zipIdx X).map fun p => (p.2, rowFr p.1)) =
      rm s t (wF u) X R
  | _, [] => rfl
  | X, r :: R => by
    rw [List.zipIdx_cons, List.map_cons, rm, ← rowsVal_locF s t u (X + 1) R]
    simp only [rowsVal, List.map_cons, List.sum_cons, Mat.r_rowFr, linE_linFr]

theorem rowsVal_locL (s : Mat) (t u : ℕ → F) :
    ∀ (X : ℕ) (R : List Row), rowsVal (RingHom.id F) s 20 20 t u ((R.zipIdx X).map fun p => (p.2, rowLoc p.1)) =
      rm s t (wL u) X R
  | _, [] => rfl
  | X, r :: R => by
    rw [List.zipIdx_cons, List.map_cons, rm, ← rowsVal_locL s t u (X + 1) R]
    simp only [rowsVal, List.map_cons, List.sum_cons, Mat.r_rowLoc, linE_linLoc]

/-- **Instantiated template rows** are the template rows at the pulled-back wires. -/
theorem rm_inst (s : Mat) (t : ℕ → F) (w : Asg) (one : Lin) (ins : List Lin) (cb : ℕ) :
    ∀ (X : ℕ) (rows : List RowT), rm s t w X (rows.map (instRow one ins cb)) = tm s t (envOf w one ins cb) X rows
  | _, [] => rfl
  | X, r :: rs => by
    rw [List.map_cons, rm, tm, Mat.r_inst, instLin_ev, rm_inst s t w one ins cb (X + 1) rs]

/-! ## The kind mux's sub-templates -/

/-- The sub-templates' rows' value, each at its wires. -/
def subsTm (s : Mat) (t : ℕ → F) (e : Env) (σ : ℕ → ℕ → LinT) : List Tpl → ℕ → ℕ → ℕ → F
  | [], _, _, _ => 0
  | T :: ts, j, k, X => tm s t (pullE e (σ j) k) X (rowsAt T.gates 0) +
      subsTm s t e σ ts (j + 1) (k + nlocs T.gates) (X + nrows T.gates)

theorem tm_subsG (s : Mat) (t : ℕ → F) (e : Env) (σ : ℕ → ℕ → LinT) :
    ∀ (ts : List Tpl) (j k X : ℕ), tm s t e X (rowsAt (subsG σ ts j k).1 k) = subsTm s t e σ ts j k X
  | [], _, _, _ => rfl
  | T :: ts, j, k, X => by
    simp only [subsG]
    have hs := rowsAt_sub (σ j) k T.gates 0
    rw [Nat.add_zero] at hs
    rw [rowsAt_append, hs, tm_append, tm_sub, nlocs_subL, List.length_map, rowsAt_length,
      tm_subsG s t e σ ts (j + 1) (k + nlocs T.gates) (X + nrows T.gates), subsTm]

theorem nlocs_subsG (σ : ℕ → ℕ → LinT) : ∀ (ts : List Tpl) (j k : ℕ),
    nlocs (subsG σ ts j k).1 = (ts.map fun T => nlocs T.gates).sum
  | [], _, _ => rfl
  | T :: ts, j, k => by
    simp only [subsG, nlocs_app, nlocs_subL, nlocs_subsG σ ts, List.map_cons, List.sum_cons]

theorem nrows_subsG (σ : ℕ → ℕ → LinT) : ∀ (ts : List Tpl) (j k : ℕ),
    nrows (subsG σ ts j k).1 = (ts.map fun T => nrows T.gates).sum
  | [], _, _ => rfl
  | T :: ts, j, k => by
    simp only [subsG, nrows_append, nrows_sub, nrows_subsG σ ts, List.map_cons, List.sum_cons]


/-! ## `rsWeight`'s block -/

/-- `rsWeight`'s sub-template as segments and outputs (`rsT_segs`). -/
def rsSegs (ν : NodeKind) (ts : List Ty) : List SG × List LinT :=
  match N4s.rsShape ts with
  | some (m, ns) =>
    let g := rsGS ν ((List.range 7).map I) (N4s.cIn (9 + 2 * m) ns) (I 7) (I 8) (N4s.kIn 9 m) 0
    (g.1, [g.2.1, g.2.2])
  | none => ([], [[], []])

theorem rsT_segs (ν : NodeKind) (ts : List Ty) : N4s.rsT ν ts = ⟨sgGates (rsSegs ν ts).1 0, (rsSegs ν ts).2⟩ := by
  cases hs : N4s.rsShape ts <;> simp only [N4s.rsT, rsSegs, hs] <;> rfl

/-- The substituted outputs of sub-templates given as (locals, outputs). -/
def subsO (σ : ℕ → ℕ → LinT) : List (ℕ × List LinT) → ℕ → ℕ → List (List LinT)
  | [], _, _ => []
  | (n, os) :: ts, j, k => os.map (Tpl.subW (σ j) k) :: subsO σ ts (j + 1) (k + n)

theorem subsG_two (σ : ℕ → ℕ → LinT) : ∀ (ts : List Tpl) (j k : ℕ),
    (subsG σ ts j k).2 = subsO σ (ts.map fun T => (nlocs T.gates, T.outs)) j k
  | [], _, _ => rfl
  | T :: ts, j, k => by simp only [subsG, List.map_cons, subsO, subsG_two σ ts]

/-- The mux gates of `kmuxT` from the substituted outputs. -/
def muxG (so nout n : ℕ) (O : List (List LinT)) : List Gate :=
  (List.range nout).flatMap fun c => mulsG n (fun j => I (so + j)) fun j => (O.getD j []).getD c []

/-- `rm` with the row weights `gt` (a fold). -/
def rmG (s : Mat) (gt : ℕ → F) (w : Asg) (X : ℕ) (rows : List Row) : F :=
  (rows.foldl (fun (p : F × ℕ) r => (p.1 + gt p.2 * (s.r r).ev w, p.2 + 1)) (0, X)).1

theorem rmG_go (s : Mat) (gt t : ℕ → F) (w : Asg) (hgt : ∀ x, gt x = gN 20 t x) :
    ∀ (rows : List Row) (a : F) (X : ℕ),
      rows.foldl (fun (p : F × ℕ) r => (p.1 + gt p.2 * (s.r r).ev w, p.2 + 1)) (a, X) = (a + rm s t w X rows, X + rows.length)
  | [], a, X => by simp [rm]
  | r :: rows, a, X => by
    rw [List.foldl_cons, rmG_go s gt t w hgt rows, rm, hgt, List.length_cons]
    ext <;> simp only <;> ring

theorem rmG_eq (s : Mat) (gt t : ℕ → F) (w : Asg) (hgt : ∀ x, gt x = gN 20 t x) (X : ℕ) (rows : List Row) :
    rmG s gt w X rows = rm s t w X rows := by
  rw [rmG, rmG_go s gt t w hgt]; simp

/-- **An `rsWeight` op's rows, prepared**: the three kinds' prepared segments (with their locals and
rows), the mux rows, the copy rows; or the rows themselves if the op's checks fail. -/
structure KP where
  ok : Bool
  alt : List Row
  one : Lin
  ins : List Lin
  ws : List ℕ
  subs : List (List PS × ℕ × ℕ)
  mux : List RowT
  copy : List Row

/-- The three kinds' segments of the op's blocks. -/
def rsTs (bs : List (List Ty × List Lin)) : List (List SG × List LinT) :=
  [rsSegs .N4 (bs.getD 0 ([], [])).1, rsSegs .N2 (bs.getD 1 ([], [])).1, rsSegs .N8 (bs.getD 2 ([], [])).1]

/-- **The prepared `rsWeight` op** (`kRows kRS repB cbRS`'s ingredients). -/
def kpOf (P : Params) (cs : CS) (op : Op) (outs : List Slot) : KP :=
  match N4s.kBlocks N4s.kRS cs op with
  | some bs =>
    if N4s.outsOk N4s.kRS.tys outs && bs.all (fun b => N4s.kRS.inOk b.1) &&
        (N4s.kIns P bs ++ N4s.outF outs).all (linLt N4s.repB) then
      let ws := bs.map fun b => b.2.length
      let Ts := rsTs bs
      let N := (Ts.map fun T => sgNl T.1).sum
      let O := subsO (N4s.kSig ws) (Ts.map fun T => (sgNl T.1, T.2)) 0 0
      ⟨true, [], P.one, N4s.kIns P bs, ws, Ts.map (fun T => (prepS 0 0 T.1, sgNl T.1, sgNr T.1)),
        rowsAt (muxG ws.sum 2 3 O) N,
        N4s.copyRows P outs (((List.range 2).map fun c => (List.range 3).flatMap fun j => L (N + c * 3 + j)).map
          (instLin P.one (N4s.kIns P bs) N4s.cbRS))⟩
    else ⟨false, [N4s.rejRow P], [], [], [], [], [], []⟩
  | none => ⟨false, [N4s.rejRow P], [], [], [], [], [], []⟩

/-- The sub-templates' value (prepared), each at its wires. -/
def subsV (s : Mat) (gt t u : ℕ → F) (e : Env) (lam : F) (σ : ℕ → ℕ → LinT) :
    List (List PS × ℕ × ℕ) → ℕ → ℕ → ℕ → F
  | [], _, _, _ => 0
  | (ps, nl, nr) :: l, j, k, X => psVal s gt t u (pullE e (σ j) k) lam (2 ^ 16 + k) X ps +
      subsV s gt t u e lam σ l (j + 1) (k + nl) (X + nr)

/-- **The prepared `rsWeight` op's rows' value** (matrix `s`, rows from `X`, cells at `w`; the
template's locals at `lam · eq(u, 2^16 + ·)`). -/
def kopV (s : Mat) (gt gu t u : ℕ → F) (w : Asg) (lam : F) (X : ℕ) (kp : KP) : F :=
  if kp.ok then
    let vin := (kp.ins.map (Lin.ev w)).toArray
    let e : Env := ⟨kp.one.ev w, fun i => vin.getD i 0, fun x => lam * gu (2 ^ 16 + x)⟩
    let R := (kp.subs.map fun p => p.2.2).sum
    subsV s gt t u e lam (N4s.kSig kp.ws) kp.subs 0 0 X + tmG s gt e (X + R) kp.mux +
      rmG s gt w (X + R + kp.mux.length) kp.copy
  else rmG s gt w X kp.alt


theorem subsV_eq (s : Mat) (gt t u : ℕ → F) (e : Env) (lam : F) (σ : ℕ → ℕ → LinT)
    (hgt : ∀ x, gt x = gN 20 t x) (he : ∀ x, e.loc x = lam * gN 20 u (2 ^ 16 + x)) :
    ∀ (Ts : List (List SG × List LinT)) (j k X : ℕ),
      subsV s gt t u e lam σ (Ts.map fun T => (prepS 0 0 T.1, sgNl T.1, sgNr T.1)) j k X =
        subsTm s t e σ (Ts.map fun T => (⟨sgGates T.1 0, T.2⟩ : Tpl)) j k X
  | [], _, _, _ => rfl
  | T :: Ts, j, k, X => by
    simp only [List.map_cons, subsV, subsTm, nlocs_sgGates, nrows_sgGates]
    rw [subsV_eq s gt t u e lam σ hgt he Ts]
    congr 1
    rw [psVal_eq s gt t u _ lam _ X hgt (fun x => by simp only [pullE]; rw [he]; ring_nf), Nat.add_zero,
      sgVal_eq s t u _ lam _ (fun x => by simp only [pullE]; rw [he]; ring_nf)]

theorem envOf_eq (w : Asg) (one : Lin) (ins : List Lin) (lam : F) (gu u : ℕ → F) (hgu : ∀ x, gu x = gN 20 u x)
    (hw : ∀ x, w (N4s.cbRS + x) = lam * gN 20 u (2 ^ 16 + x)) :
    envOf w one ins N4s.cbRS = ⟨one.ev w, fun i => (ins.map (Lin.ev w)).toArray.getD i 0, fun x => lam * gu (2 ^ 16 + x)⟩ := by
  simp only [envOf, Env.mk.injEq, true_and]
  constructor
  · funext i
    rw [Array.getD_eq_getD_getElem?, List.getElem?_toArray, List.getElem?_map, List.getD_eq_getElem?_getD]
    cases ins[i]? <;> rfl
  · funext x; rw [hw, hgu]

/-- **The prepared `rsWeight` op's value is its rows' value.** -/
theorem kopV_eq (s : Mat) (gt gu t u : ℕ → F) (w : Asg) (lam : F) (hgt : ∀ x, gt x = gN 20 t x)
    (hgu : ∀ x, gu x = gN 20 u x) (hw : ∀ x, w (N4s.cbRS + x) = lam * gN 20 u (2 ^ 16 + x))
    (P : Params) (cs : CS) (op : Op) (outs : List Slot) (X : ℕ) :
    kopV s gt gu t u w lam X (kpOf P cs op outs) = rm s t w X (N4s.kRows N4s.kRS N4s.repB N4s.cbRS P cs op outs) := by
  unfold kpOf N4s.kRows
  cases hbs : N4s.kBlocks N4s.kRS cs op with
  | none => simp [kopV, rmG_eq s gt t w hgt]
  | some bs =>
    simp only []
    by_cases hc : (N4s.outsOk N4s.kRS.tys outs && bs.all (fun b => N4s.kRS.inOk b.1) &&
        (N4s.kIns P bs ++ N4s.outF outs).all (linLt N4s.repB)) = true
    · rw [if_pos hc, if_pos hc]
      simp only [kopV]
      rw [N4s.rowsTR_eq, rm_append, rm_inst, rmG_eq s gt t w hgt, tmG_eq s gt t _ hgt]
      have hT : N4s.kTpl N4s.kRS op bs = kmuxT (N4s.kSig (bs.map fun b => b.2.length)) (bs.map fun b => b.2.length).sum 2
          ((rsTs bs).map fun T => (⟨sgGates T.1 0, T.2⟩ : Tpl)) := by
        simp only [N4s.kTpl, rsTs, List.map_cons, List.map_nil, ← rsT_segs]; rfl
      rw [envOf_eq w P.one _ lam gu u hgu hw, hT]
      simp only [kmuxT, tpl_rows_eq, rowsAt_append, tm_append, tm_subsG]
      rw [← subsV_eq s gt t u _ lam _ hgt (fun x => by simp only; rw [hgu])]
      simp only [nlocs_subsG, nrows_subsG, subsG_two, List.map_map, Function.comp_def, nlocs_sgGates,
        nrows_sgGates, rowsAt_length, List.length_map, nrows_append, Nat.zero_add, List.length_range]
      simp only [ite_true, muxG, rsTs, List.length_cons, List.length_nil, List.map_cons, List.map_nil,
        List.length_append, rowsAt_length, nrows_subsG, nrows_sgGates, Nat.add_assoc,
        show (0 + 1 + 1 + 1 : ℕ) = 3 from rfl]
    · rw [if_neg hc, if_neg hc]; simp [kopV, rmG_eq s gt t w hgt]


/-! ## Prototype 0's replay blocks -/

/-- A replay block: rows, or an `rsWeight` op (its rows `kRows kRS`, not built). -/
inductive RBlk where
  | sp (l : List Row)
  | rs (P : Params) (cs : CS) (op : Op) (outs : List Slot)

def RBlk.rows : RBlk → List Row
  | .sp l => l
  | .rs P cs op outs => N4s.kRows N4s.kRS N4s.repB N4s.cbRS P cs op outs

/-- Prototype 0's block of a covered op: `rsWeight` lazily, the others' rows. -/
def blk0 (P : Params) (cs : CS) (op : Op) (outs : List Slot) : RBlk :=
  if N4s.rtN0.cov op then .sp (N4s.rtN0.rows P cs op outs)
  else if N4s.kRS.cov op then .rs P cs op outs
  else .sp ((N4s.rtC1c 0).rows P cs op outs)

theorem blk0_rows (P : Params) (cs : CS) (op : Op) (outs : List Slot) :
    (blk0 P cs op outs).rows = (N4s.rtC1c 0).rows P cs op outs := by
  unfold blk0
  split_ifs with h0 h1
  · simp [RBlk.rows, N4s.rtC1c, N4s.rtN0c, N4s.rtN0R, Circ.RT.orElse, h0]
  · simp [RBlk.rows, N4s.rtC1c, N4s.rtN0c, N4s.rtN0R, Circ.RT.orElse, h0, h1, N4s.rtRs, N4s.rtK]
  · rfl

/-- The replay blocks along the compile's trail (as `repRowsX`). -/
def repBlkX (X : Ext) (P : Params) (rt : RT) (bk : Params → CS → Op → List Slot → RBlk) : CS → List Op → List RBlk
  | _, [] => []
  | cs, op :: ops =>
    let c := cs.align (alignOf op ops)
    (if rt.cov op then [bk P c op (stepOut X P c op).slots] else []) ++
      repBlkX X P rt bk (c.add op (stepOut X P c op)) ops

theorem repBlkX_rows (X : Ext) (P : Params) (rt : RT) (bk : Params → CS → Op → List Slot → RBlk)
    (hbk : ∀ P c op o, (bk P c op o).rows = rt.rows P c op o) :
    ∀ (cs : CS) (ops : List Op), (repBlkX X P rt bk cs ops).flatMap RBlk.rows = repRowsX X P rt cs ops
  | _, [] => rfl
  | cs, op :: ops => by
    simp only [repBlkX, repRowsX, List.flatMap_append, repBlkX_rows X P rt bk hbk]
    split_ifs <;> simp [hbk]

/-- **The memoized trail with the replay blocks** (`trailMR` with blocks). -/
def trailMB (X : TCtx → Ext) (L : TLay) (P : Params) (G : TG) (rt : RT) (bk : Params → CS → Op → List Slot → RBlk) :
    List (TKey × Tpl) → CS → Option Op → ℕ → List Op → List Row → List RBlk → List Row × List RBlk
  | _, _, _, _, [], acc, acr => (acc, acr)
  | M, cs, pre, k, op :: ops, acc, acr =>
    let c := cs.align (alignOf op ops)
    let acc := (if op.item?.isSome || G.cov op then G.rows P c pre op k else []).reverseAux acc
    let M := memoAdd M ((X ⟨fun _ => ⟨[], []⟩, L.cb⟩ P c op).bind (·.tin))
    let o := stepOut (X ⟨tlook M, L.cb⟩) P c op
    let acr := if rt.cov op then bk P c op o.slots :: acr else acr
    trailMB X L P G rt bk (memoAdd M o.tin) (c.add op o) (some op) (if op.item?.isSome then k + 1 else k) ops acc acr

theorem trailMB_eq (X : TCtx → Ext) (L : TLay) (P : Params) (G : TG) (rt : RT) (bk : Params → CS → Op → List Slot → RBlk) :
    ∀ (ops : List Op) (M : List (TKey × Tpl)) (cs : CS) (pre : Option Op) (k : ℕ) (acc : List Row) (acr : List RBlk),
      MOk M → trailMB X L P G rt bk M cs pre k ops acc acr =
        ((trailRows (X L.ctx) P G cs pre k ops).reverse ++ acc, (repBlkX (X L.ctx) P rt bk cs ops).reverse ++ acr)
  | [], _, _, _, _, _, _, _ => rfl
  | op :: ops, M, cs, pre, k, acc, acr, h => by
    have hc : ∀ x, (⟨tlook (memoAdd M x), L.cb⟩ : TCtx) = L.ctx := fun x => by
      rw [tlook_eq (memoAdd_ok h x)]; rfl
    simp only [trailMB, trailRows, repBlkX, hc]
    rw [trailMB_eq X L P G rt bk ops _ _ _ _ _ _ (memoAdd_ok (memoAdd_ok h _) _), List.reverseAux_eq,
      List.reverse_append, List.reverse_append, List.append_assoc, List.append_assoc]
    split_ifs <;> simp

/-- **Prototype 0's ask rows and replay blocks in one memoized pass.** -/
def arBlk0 : List Row × List RBlk :=
  let r := trailMB (N4s.XofC 0) (protoLay 0) (protoP 0) (askTG 0) (N4s.rtC1c 0) blk0 []
    (CS.init (baseR 0)) none 0 (protoProg 0).ops [] []
  (r.1.reverse, r.2.reverse)

theorem arBlk0_eq : arBlk0.1 = askRowsT 0 ∧ arBlk0.2.flatMap RBlk.rows = N4s.repRowsP (N4s.rtC1c 0) 0 := by
  unfold arBlk0
  rw [trailMB_eq _ _ _ _ _ _ _ _ _ _ _ _ _ (by simp [MOk])]
  simp only [List.append_nil, List.reverse_reverse]
  exact ⟨rfl, repBlkX_rows _ _ _ _ blk0_rows _ _⟩

end Rev4
end FR

end G6_FRNodeRows4RepCFP

section G6_FRInitFuse

-- New for `flock-recursive` (track INIT: the badge's start-up). The plan compile and the template
-- generators' trail in one pass.

/-!
# One pass for the compile and the trail (`compMSXA`)

The node plan walks each prototype's ops twice at process start: `compMSX` (the compile with the
template memo, `planData4`) and `trailMS` (the ask-template generators' rows, `arOf`). Both evolve the
same compile state and memo op by op. **`compMSXA`** does both in one walk, and **`compMSXA_eq`** says
it is the pair `(compMSX …, trailMS …)`, for every extension, generator and starting state.
-/

namespace FR
namespace Rev4
open RecursionFast Circ TEval Tpl

/-- **`compMSX` and `trailMS` in one pass** (`compMSXA_eq`): the compile's state, segments and memo,
and the generator `G`'s rows (reversed onto `racc`, `pre` the previous op, `k` the items so far). -/
def compMSXA (X : TCtx → Ext) (L : TLay) (P : Params) (G : TG) : List (TKey × Tpl) → CS → List Op →
    Option (ℕ × ℕ × ℕ) → List Seg → Option Op → ℕ → List Row →
    (CS × List Seg × List (TKey × Tpl)) × List Row
  | M, cs, [], _, acc, _, _, racc => ((cs, acc, M), racc)
  | M, cs, op :: ops, cur, acc, pre, k, racc =>
    let a := alignOf op ops
    let acc := match a, cur with
      | some _, some (r0, c0, b) => cutBlock r0 cs.nrows c0 b acc
      | _, _ => acc
    let cs' := cs.align a
    let cur := match a with
      | some (_, b) => some (cs'.nrows, cs'.next, b)
      | none => cur
    let acc := match op with
      | .eqTable r =>
        if (cs'.slot r).isSome && decide (8 ≤ (asAF (cs'.slot r)).length) then
          (tensorSegs P cs' (asAF (cs'.slot r))).reverse ++ acc
        else acc
      | _ => acc
    let racc := (if op.item?.isSome || G.cov op then G.rows P cs' pre op k else []).reverseAux racc
    let M := memoAdd M ((X ⟨fun _ => ⟨[], []⟩, L.cb⟩ P cs' op).bind (·.tin))
    let o := stepOut (X ⟨tlook M, L.cb⟩) P cs' op
    let M := memoAdd M o.tin
    let cs2 := cs'.add op o
    let k' := if op.item?.isSome then k + 1 else k
    match op, cur with
    | .assertEq .., some (r0, c0, b) =>
      compMSXA X L P G M cs2 ops none (cutBlock r0 cs2.nrows c0 b acc) (some op) k' racc
    | _, _ => compMSXA X L P G M cs2 ops cur acc (some op) k' racc

/-- **The one pass is the two passes.** -/
theorem compMSXA_eq (X : TCtx → Ext) (L : TLay) (P : Params) (G : TG) :
    ∀ (ops : List Op) (M : List (TKey × Tpl)) (cs : CS) (cur : Option (ℕ × ℕ × ℕ)) (acc : List Seg)
      (pre : Option Op) (k : ℕ) (racc : List Row),
      compMSXA X L P G M cs ops cur acc pre k racc =
        (compMSX X L P M cs ops cur acc, trailMS X L P G M cs pre k ops racc)
  | [], _, _, _, _, _, _, _ => rfl
  | op :: ops, M, cs, cur, acc, pre, k, racc => by
    cases op with
    | assertEq a b act =>
      simp only [compMSXA, compMSX, trailMS]
      rcases ha : alignOf (Op.assertEq a b act) ops with _ | ⟨x, w⟩ <;> simp only [ha] <;>
        rcases cur with _ | ⟨r0, c0, w'⟩ <;> dsimp only <;> rw [compMSXA_eq X L P G ops]
    | _ => simp only [compMSXA, compMSX, trailMS]; rw [compMSXA_eq X L P G ops]; rfl

/-- (+) The pass at no ops is the starting state and accumulator. -/
theorem compMSXA_nil (X : TCtx → Ext) (L : TLay) (P : Params) (G : TG) (M : List (TKey × Tpl)) (cs : CS)
    (racc : List Row) : compMSXA X L P G M cs [] none [] none 0 racc = ((cs, [], M), racc) := rfl

/-! ## The compile and the trail with replay blocks (CF2, INIT's proposal 2 for `trailMB`) -/

/-- **`compMSX` and `trailMB` in one pass** (`compMSXB_eq`): the compile's state, segments and memo,
the generator `G`'s rows and the replay template `rt`'s blocks (`bk`), each reversed onto its
accumulator. -/
def compMSXB (X : TCtx → Ext) (L : TLay) (P : Params) (G : TG) (rt : RT) (bk : Params → CS → Op → List Slot → RBlk) :
    List (TKey × Tpl) → CS → List Op → Option (ℕ × ℕ × ℕ) → List Seg → Option Op → ℕ → List Row → List RBlk →
    (CS × List Seg × List (TKey × Tpl)) × List Row × List RBlk
  | M, cs, [], _, acc, _, _, racc, bacc => ((cs, acc, M), racc, bacc)
  | M, cs, op :: ops, cur, acc, pre, k, racc, bacc =>
    let a := alignOf op ops
    let acc := match a, cur with
      | some _, some (r0, c0, b) => cutBlock r0 cs.nrows c0 b acc
      | _, _ => acc
    let cs' := cs.align a
    let cur := match a with
      | some (_, b) => some (cs'.nrows, cs'.next, b)
      | none => cur
    let acc := match op with
      | .eqTable r =>
        if (cs'.slot r).isSome && decide (8 ≤ (asAF (cs'.slot r)).length) then
          (tensorSegs P cs' (asAF (cs'.slot r))).reverse ++ acc
        else acc
      | _ => acc
    let racc := (if op.item?.isSome || G.cov op then G.rows P cs' pre op k else []).reverseAux racc
    let M := memoAdd M ((X ⟨fun _ => ⟨[], []⟩, L.cb⟩ P cs' op).bind (·.tin))
    let o := stepOut (X ⟨tlook M, L.cb⟩) P cs' op
    let bacc := if rt.cov op then bk P cs' op o.slots :: bacc else bacc
    let M := memoAdd M o.tin
    let cs2 := cs'.add op o
    let k' := if op.item?.isSome then k + 1 else k
    match op, cur with
    | .assertEq .., some (r0, c0, b) =>
      compMSXB X L P G rt bk M cs2 ops none (cutBlock r0 cs2.nrows c0 b acc) (some op) k' racc bacc
    | _, _ => compMSXB X L P G rt bk M cs2 ops cur acc (some op) k' racc bacc

/-- **The one pass is the two passes.** -/
theorem compMSXB_eq (X : TCtx → Ext) (L : TLay) (P : Params) (G : TG) (rt : RT) (bk : Params → CS → Op → List Slot → RBlk) :
    ∀ (ops : List Op) (M : List (TKey × Tpl)) (cs : CS) (cur : Option (ℕ × ℕ × ℕ)) (acc : List Seg)
      (pre : Option Op) (k : ℕ) (racc : List Row) (bacc : List RBlk),
      compMSXB X L P G rt bk M cs ops cur acc pre k racc bacc =
        (compMSX X L P M cs ops cur acc, trailMB X L P G rt bk M cs pre k ops racc bacc)
  | [], _, _, _, _, _, _, _, _ => rfl
  | op :: ops, M, cs, cur, acc, pre, k, racc, bacc => by
    cases op with
    | assertEq a b act =>
      simp only [compMSXB, compMSX, trailMB]
      rcases ha : alignOf (Op.assertEq a b act) ops with _ | ⟨x, w⟩ <;> simp only [ha] <;>
        rcases cur with _ | ⟨r0, c0, w'⟩ <;> dsimp only <;> rw [compMSXB_eq X L P G rt bk ops]
    | _ => simp only [compMSXB, compMSX, trailMB]; rw [compMSXB_eq X L P G rt bk ops]; rfl

end Rev4
end FR

end G6_FRInitFuse
