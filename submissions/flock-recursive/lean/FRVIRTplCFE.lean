-- New for `flock-recursive` (track CF): segments prepared once, evaluated per call.
import FRVIRTplCF

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
