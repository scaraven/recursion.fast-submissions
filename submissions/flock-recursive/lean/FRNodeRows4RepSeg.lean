-- New for `flock-recursive` (SEG-R §4, stage SEG-R1): prototype 1's replay templates.
import FRNodeRows4RepSegK
import FRVIRTplSegR
import FRNodeRows4RepLT
import FRSubmission4V

/-!
# The segment program's replay ops (prototype 1)

* **`kRSS`** (`rsWeight`): covers an `rsWeight` whose `act` is false at every index (so `β` is unread,
  `β = 1`) with three claims at every index; serves the operand types `[af 7, f, f, ak m ×4]`,
  `23 ≤ m ≤ 25`; forces the claims' `f₁` to zero (`F`-points); one `Tpl.rsSegT` instance.
  **`rsWeightF_seg`**: at those operands `Impl.rsWeightF r ps κ 1 ρ` is `Tpl.rsSegV` (the kind factor of
  claim 2 collapses at `β = 1`, `kwSL_one`; the narrower kinds' coordinates padded with `0`).
  **`kRSS_ok`**: `KOkD` at every index, given that the base's `rsWeight` is `rsWeightF` (`SegBase`).
* Operands of any other shape get the rejecting row (`kdRows`); an `rsWeight` with some `act` true or
  another claim count is not covered (it stays an import: no segment program has one, SEG-R0 §6).
-/

namespace FR
namespace N4s
open RecursionFast Rev4 Circ Tpl

/-- **The base ops a segment slot replays** (the certificate's `implB`: `rfl`). -/
def SegBase (impl₀ : OpImpl) : Prop := impl₀.rsWeight = Impl.rsWeightF ∧ impl₀.shiftTarget = Impl.shiftTargetI

/-! ## `rsWeight`'s value at `β = 1` and `F`-point claims -/

theorem ofF_f₀ {x : K} (h : x.f₁ = 0) : K.ofF x.f₀ = x := K_ext' rfl (by rw [h]; rfl)

theorem sqIter_zeroK (k : ℕ) : sqIter k (0 : K) = 0 := by
  rw [sqIter_eq, zero_pow (by positivity)]

theorem sqIter_oneK (k : ℕ) : sqIter k (1 : K) = 1 := by
  rw [sqIter_eq, one_pow]

/-- **`eq` on two lists of length `m ≤ n`, padded to `n` coordinates** (characteristic two). -/
theorem eqPts_pad : ∀ (q ρ : List K) (n : ℕ), q.length = ρ.length → q.length ≤ n →
    eqPts q ρ = ((List.range n).map fun l => 1 + q.getD l 0 + ρ.getD l 0).prod
  | [], [], n, _, _ => by rw [eqPts]; simp
  | x :: q, y :: ρ, n + 1, hl, hn => by
    have hc : x * y + (1 - x) * (1 - y) = 1 + x + y := by
      have := Impl.eqPtsC_eq [x] [y]; simpa [Impl.eqPtsC, eqPts] using this.symm
    rw [eqPts_cons, eqPts_pad q ρ n (by simpa using hl) (by simp at hn; omega), List.range_succ_eq_map,
      List.map_cons, List.prod_cons, List.map_map, hc]
    simp [Function.comp_def]
  | [], _ :: _, _, hl, _ => by simp at hl
  | _ :: _, [], _, hl, _ => by simp at hl
  | _ :: _, _ :: _, 0, _, hn => by simp at hn

/-- One claim's `eq` at stage `k`, as the template's product. -/
theorem eqPts_stage (a ρ : Array K) (m : ℕ) (ha : a.size = m) (hρ : ρ.size = m) (hm : m ≤ 25)
    (hf : ∀ x ∈ a.toList, x.f₁ = 0) (k : ℕ) :
    eqPts (a.toList.map (sqIter k)) ρ.toList =
      ((List.range 25).map fun l => 1 + K.ofF (sqIter k (a.toList.getD l 0).f₀) + ρ.toList.getD l 0).prod := by
  rw [eqPts_pad _ _ 25 (by simp [ha, hρ]) (by simp [ha, hm])]
  refine congrArg List.prod (List.map_congr_left fun l _ => ?_)
  rw [← Impl.sqIter_ofF, ← sqIter_zeroK k, getD_map', sqIter_zeroK]
  congr 3
  rw [List.getD_eq_getElem?_getD]
  rcases h : a.toList[l]? with _ | x
  · rfl
  · exact (ofF_f₀ (hf x (List.mem_of_getElem? h))).symm

theorem phiTable_getD (r : Array F) (k : ℕ) : (phiTable r.toList).getD k 0 = (phiTable r.toList).toList.getD k 0 := by
  rw [Array.getD_eq_getD_getElem?, List.getD_eq_getElem?_getD, Array.getElem?_toList]

/-- **`rsWeight` at prototype 1** (`β = 1`, three `F`-point claims of `m` coordinates, `23 ≤ m ≤ 25`)
**is the template's value.** -/
theorem rsWeightF_seg (r : Array F) (hr : r.size = 7) (a₀ a₁ a₂ ρ : Array K) (m : ℕ) (hm : 23 ≤ m)
    (hm' : m ≤ 25) (h₀ : a₀.size = m) (h₁ : a₁.size = m) (h₂ : a₂.size = m) (hρ : ρ.size = m)
    (hf₀ : ∀ x ∈ a₀.toList, x.f₁ = 0) (hf₁ : ∀ x ∈ a₁.toList, x.f₁ = 0) (hf₂ : ∀ x ∈ a₂.toList, x.f₁ = 0)
    (κ : F) :
    Impl.rsWeightF r [a₀, a₁, a₂] κ 1 ρ = rsSegV r.toList κ ((List.range 25).map fun l => ρ.toList.getD l 0)
      (fun j l => (([a₀, a₁, a₂].getD j #[]).toList.getD l 0).f₀) := by
  rw [Impl.rsWeightF_eq, Impl.rsWeight_meets _ _ _ _ _ hr (by omega), rsSegV_eq3]
  have hρ' : ∀ l < 25, ((List.range 25).map fun l => ρ.toList.getD l 0).getD l 0 = ρ.toList.getD l 0 :=
    fun l hl => getD_range_map _ hl 0
  have hst : ∀ (a : Array K), a.size = m → (∀ x ∈ a.toList, x.f₁ = 0) → ∀ k,
      ((List.range 25).map fun l => 1 + K.ofF (sqIter k (a.toList.getD l 0).f₀) +
        ((List.range 25).map fun l => ρ.toList.getD l 0).getD l 0).prod = eqPts (a.toList.map (sqIter k)) ρ.toList :=
    fun a ha hf k => by
      rw [eqPts_stage a ρ m ha hρ hm' hf k]
      exact congrArg List.prod (List.map_congr_left fun l hl => by rw [hρ' l (List.mem_range.1 hl)])
  have hkw : ∀ k, Impl.kwSL (sqIter k (K.ofF 1)) (a₁.toList.map (sqIter k)) ρ.toList = eqPts (a₁.toList.map (sqIter k)) ρ.toList :=
    fun k => by
      have h1K : K.ofF 1 = 1 := map_one K.ofFRingHom
      rw [h1K, sqIter_oneK]
      exact Snd.kwSL_one _ _ (by simp [h₁, hρ]) (by simp [hρ, hm])
  have hzi : [a₀, a₁, a₂].zipIdx = [(a₀, 0), (a₁, 1), (a₂, 2)] := rfl
  simp only [Impl.rsWeightS, hzi, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    add_zero, pow_zero, one_mul, pow_one, zero_ne_one, ite_false, ite_true,
    show (2 : ℕ) ≠ 1 by norm_num, hkw]
  simp only [List.getD_cons_zero, List.getD_cons_succ, phiTable_getD, hst a₀ h₀ hf₀, hst a₁ h₁ hf₁,
    hst a₂ h₂ hf₂, pow_two]
  rw [show K.ofF (κ * κ) = K.ofF κ * K.ofF κ from map_mul K.ofFRingHom κ κ]
  ring

theorem rsSegV_congr (rv rv' : List F) (κ κ' : F) (ρ ρ' : List K) (a a' : ℕ → ℕ → F) (hr : rv = rv')
    (hκ : κ = κ') (hρ : ρ = ρ') (ha : ∀ j < 3, ∀ l < 25, a j l = a' j l) : rsSegV rv κ ρ a = rsSegV rv' κ' ρ' a' := by
  subst hr hκ hρ
  unfold rsSegV
  refine Finset.sum_congr rfl fun j hj => congrArg _ (Finset.sum_congr rfl fun k _ => congrArg _
    (congrArg List.prod (List.map_congr_left fun l hl => ?_)))
  rw [ha j (Finset.mem_range.1 hj) l (List.mem_range.1 hl)]

/-! ## `rsWeight`'s `KOpD` -/

/-- An `rsWeight` with `act` false and three claims at every index. -/
def isRSS : Op → Bool
  | .rsWeight _ ps _ _ act _ => kinds.all (fun ι => !act ι) && kinds.all fun ι => (ps ι).length == 3
  | _ => false

/-- The operand types the template serves: `[af 7, f, f, ak m ×4]`, `23 ≤ m ≤ 25`. -/
def rssIn : List Ty → Bool
  | [.af 7, .f, .f, .ak m, .ak m₁, .ak m₂, .ak m₃] =>
    decide (23 ≤ m) && decide (m ≤ 25) && m₁ == m && m₂ == m && m₃ == m
  | _ => false

/-- `ρ`'s width. -/
def rssM : List Ty → ℕ
  | _ :: _ :: _ :: .ak m :: _ => m
  | _ => 0

/-- Canonical input `p`'s encoding position (`r″`, `κ`; `ρ`; the claims' `f₀`). -/
def rssLay (ts : List Ty) (p : ℕ) : Option ℕ :=
  if p < 8 then some p
  else if p < 58 then (if (p - 8) / 2 < rssM ts then some (p + 1) else none)
  else if p < 133 then
    (if (p - 58) % 25 < rssM ts then
      some (9 + 2 * rssM ts + 2 * rssM ts * ((p - 58) / 25) + 2 * ((p - 58) % 25)) else none)
  else none

/-- The claims' `f₁` positions (forced to `0`: `F`-points). -/
def rssZf (ts : List Ty) : List ℕ :=
  (List.range 3).flatMap fun j => (List.range (rssM ts)).map fun l => 10 + 2 * rssM ts + 2 * rssM ts * j + 2 * l

/-- **The segment's `rsWeight` replay.** -/
def kRSS : KOpD := ⟨isRSS, rsArgs, rssIn, 133, rssLay, rssZf, rsSegT, [.k]⟩

theorem rssIn_eq {ts : List Ty} (h : rssIn ts = true) :
    ∃ m, ts = [.af 7, .f, .f, .ak m, .ak m, .ak m, .ak m] ∧ 23 ≤ m ∧ m ≤ 25 := by
  unfold rssIn at h
  split at h
  · simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at h
    obtain ⟨⟨⟨⟨h1, h2⟩, rfl⟩, rfl⟩, rfl⟩ := h
    exact ⟨_, rfl, h1, h2⟩
  · simp at h

theorem implP1_rsWeight {impl₀ : OpImpl} {base : NodeKind → OpImpl} (ι : Kind) :
    (implP impl₀ base 1 ι).rsWeight = impl₀.rsWeight := rfl

theorem flatMap_encV_k (v : K) : [Val.k v].flatMap encV = encK v := by simp [encV]

/-- The encoding's entry at `pre.length + i`. -/
theorem getD_at {pre mid post : List F} {i n : ℕ} (hn : pre.length = n) (hi : i < mid.length) :
    (pre ++ mid ++ post).getD (n + i) 0 = mid.getD i 0 := by
  subst hn; exact getD_mid pre mid post hi

/-- **`rsWeight`'s replay obligation holds at every index** (the base's `rsWeight` is `rsWeightF`). -/
theorem kRSS_ok {impl₀ : OpImpl} {base : NodeKind → OpImpl} (hR : impl₀.rsWeight = Impl.rsWeightF)
    (ι : Kind) : KOkD (implP impl₀ base 1 ι) ι kRSS := by
  intro op hc
  cases op
  all_goals first | exact absurd hc Bool.false_ne_true | skip
  rename_i r ps κ' β act ρ
  simp only [kRSS, isRSS, Bool.and_eq_true, List.all_eq_true, Bool.not_eq_true', beq_iff_eq] at hc
  have hact : act ι = false := hc.1 ι (by cases ι <;> simp [kinds])
  have hps : (ps ι).length = 3 := hc.2 ι (by cases ι <;> simp [kinds])
  refine ⟨fun _ _ _ h => Res.noConfusion h, fun inp regs vs ok ts hev hin hty => ?_⟩
  simp only [evalOp, Res.vals.injEq, hact, Bool.false_eq_true, ite_false] at hev
  obtain ⟨rfl, -⟩ := hev
  refine ⟨rfl, fun cst hz e h1 hinp hcst => ?_⟩
  obtain ⟨m, rfl, hm1, hm2⟩ := rssIn_eq hin
  obtain ⟨p0, p1, p2, hp⟩ : ∃ p0 p1 p2, ps ι = [p0, p1, p2] := by
    rcases h : ps ι with _ | ⟨p0, _ | ⟨p1, _ | ⟨p2, _ | ⟨_, _⟩⟩⟩⟩ <;> rw [h] at hps <;> simp at hps
    exact ⟨p0, p1, p2, rfl⟩
  simp only [kRSS, rsArgs, hp, List.map_cons, List.map_nil, List.cons_append, List.nil_append,
    List.cons.injEq] at hty
  obtain ⟨hr, hκ, hβ, hρ, h0, h1', h2, -⟩ := hty
  obtain ⟨ra, hra, hrs⟩ := val_af hr
  obtain ⟨κv, hκv⟩ := val_f hκ
  obtain ⟨βv, hβv⟩ := val_f hβ
  obtain ⟨ρa, hρa, hρs⟩ := val_ak hρ
  obtain ⟨a0, ha0, ha0s⟩ := val_ak h0
  obtain ⟨a1, ha1, ha1s⟩ := val_ak h1'
  obtain ⟨a2, ha2, ha2s⟩ := val_ak h2
  have hx : (kRSS.args (.rsWeight r ps κ' β act ρ) ι).flatMap (fun a => encV (rd regs a)) =
      ra.toList ++ [κv, βv] ++ ρa.toList.flatMap encK ++
        (a0.toList.flatMap encK ++ (a1.toList.flatMap encK ++ a2.toList.flatMap encK)) := by
    simp only [kRSS, rsArgs, hp, List.cons_append, List.nil_append, List.flatMap_cons, List.flatMap_nil,
      List.append_nil, hra, hκv, hβv, hρa, ha0, ha1, ha2, encV]
    simp
  rw [hx] at hz hinp
  have hlr : ra.toList.length = 7 := by simp [hrs]
  have hlρ : (ρa.toList.flatMap encK).length = 2 * m := by rw [length_flatMap_encK]; simp [hρs]
  have hla : ∀ a : Array K, a.size = m → (a.toList.flatMap encK).length = 2 * m := fun a ha => by
    rw [length_flatMap_encK]; simp [ha]
  have hM : rssM [.af 7, .f, .f, .ak m, .ak m, .ak m, .ak m] = m := rfl
  obtain ⟨xs, hxs⟩ : ∃ xs, xs = ra.toList ++ [κv, βv] ++ ρa.toList.flatMap encK ++
    (a0.toList.flatMap encK ++ (a1.toList.flatMap encK ++ a2.toList.flatMap encK)) := ⟨_, rfl⟩
  rw [← hxs] at hz hinp
  have hinp' : ∀ p < 133, e.inp p = ((rssLay [.af 7, .f, .f, .ak m, .ak m, .ak m, .ak m] p).map fun q =>
      xs.getD q 0).getD 0 := hinp
  have hz' : ∀ q ∈ rssZf [.af 7, .f, .f, .ak m, .ak m, .ak m, .ak m], xs.getD q 0 = 0 := hz
  have hL : ∀ a : Array K, (a.toList.flatMap encK).length = 2 * a.size := fun a => by
    rw [length_flatMap_encK, Array.length_toList]
  -- the encoding's entries
  have hpre : (ra.toList ++ [κv, βv] ++ ρa.toList.flatMap encK).length = 9 + 2 * m := by
    simp only [List.length_append, hL, Array.length_toList, hrs, hρs, List.length_cons, List.length_nil] <;> omega
  have hcl : ∀ j < 3, ∀ q < 2 * m, xs.getD (9 + 2 * m + 2 * m * j + q) 0 =
      (([a0, a1, a2].getD j #[]).toList.flatMap encK).getD q 0 := by
    intro j hj q hq
    interval_cases j
    · rw [hxs, ← List.append_assoc, show 9 + 2 * m + 2 * m * 0 + q = 9 + 2 * m + q by ring,
        getD_at hpre (by rw [hL, ha0s]; omega)]; rfl
    · rw [hxs, ← List.append_assoc, ← List.append_assoc,
        show 9 + 2 * m + 2 * m * 1 + q = (9 + 2 * m + 2 * m) + q by ring,
        getD_at (by rw [List.length_append, hpre, hL, ha0s]) (by rw [hL, ha1s]; omega)]; rfl
    · rw [hxs, ← List.append_assoc, ← List.append_assoc, ← List.append_nil (a2.toList.flatMap encK),
        ← List.append_assoc, show 9 + 2 * m + 2 * m * 2 + q = (9 + 2 * m + 2 * m + 2 * m) + q by ring,
        getD_at (by rw [List.length_append, List.length_append, hpre, hL, hL, ha0s, ha1s]) (by rw [hL, ha2s]; omega)]; rfl
  have hρx : ∀ q < 2 * m, xs.getD (9 + q) 0 = (ρa.toList.flatMap encK).getD q 0 := fun q hq => by
    rw [hxs, show ra.toList ++ [κv, βv] ++ ρa.toList.flatMap encK ++
        (a0.toList.flatMap encK ++ (a1.toList.flatMap encK ++ a2.toList.flatMap encK)) =
        (ra.toList ++ [κv, βv]) ++ ρa.toList.flatMap encK ++
        (a0.toList.flatMap encK ++ (a1.toList.flatMap encK ++ a2.toList.flatMap encK)) from rfl,
      getD_at (by simp [hrs]) (by rw [hL, hρs]; omega)]
  have hrx : ∀ q < 7, xs.getD q 0 = ra.toList.getD q 0 := fun q hq => by
    rw [hxs, List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, List.append_assoc, List.append_assoc,
      List.getElem?_append_left (by simp [hrs]; omega)]
  have hκx : xs.getD 7 0 = κv := by
    rw [hxs, List.getD_eq_getElem?_getD, List.append_assoc, List.append_assoc,
      List.getElem?_append_right (by simp [hrs])]
    simp [hrs]
  -- the claims' coordinates are `F`-points
  have hfz : ∀ j < 3, ∀ x ∈ ([a0, a1, a2].getD j #[]).toList, x.f₁ = 0 := by
    intro j hj x hx'
    obtain ⟨l, hl, hxl⟩ := List.getElem_of_mem hx'
    have hsz : ([a0, a1, a2].getD j #[]).size = m := by interval_cases j <;> assumption
    have hl' : l < m := by rw [Array.length_toList, hsz] at hl; exact hl
    have hq := hz' (10 + 2 * m + 2 * m * j + 2 * l) (List.mem_flatMap.2 ⟨j, List.mem_range.2 hj,
      List.mem_map.2 ⟨l, List.mem_range.2 (by rw [hM]; exact hl'), by rw [hM]⟩⟩)
    rw [show 10 + 2 * m + 2 * m * j + 2 * l = 9 + 2 * m + 2 * m * j + (2 * l + 1) by ring,
      hcl j hj _ (by omega), (encK_getD _ l).2, List.getD_eq_getElem _ _ hl, hxl] at hq
    exact hq
  -- the canonical inputs' values
  have hin7 : ∀ p < 7, e.inp p = ra.toList.getD p 0 := fun p hp => by
    rw [hinp' p (by omega)]
    simp only [rssLay, if_pos (show p < 8 by omega), Option.map_some, Option.getD_some]
    exact hrx p hp
  have hinκ : e.inp 7 = κv := by
    rw [hinp' 7 (by norm_num)]
    simp only [rssLay, if_pos (show 7 < 8 by norm_num), Option.map_some, Option.getD_some]
    exact hκx
  have hinρ : ∀ l < 25, (⟨e.inp (8 + 2 * l), e.inp (9 + 2 * l)⟩ : K) = ρa.toList.getD l 0 := fun l hl => by
    rw [hinp' _ (by omega), hinp' _ (by omega)]
    simp only [rssLay, hM, show ¬ 8 + 2 * l < 8 by omega, show ¬ 9 + 2 * l < 8 by omega,
      show 8 + 2 * l < 58 by omega, show 9 + 2 * l < 58 by omega, ite_false, ite_true,
      show (8 + 2 * l - 8) / 2 = l by omega, show (9 + 2 * l - 8) / 2 = l by omega]
    by_cases hlm : l < m
    · simp only [hlm, ite_true, Option.map_some, Option.getD_some, show 8 + 2 * l + 1 = 9 + 2 * l by ring,
        show 9 + 2 * l + 1 = 9 + (2 * l + 1) by ring]
      rw [hρx _ (by omega), hρx _ (by omega), (encK_getD _ l).1, (encK_getD _ l).2]
    · simp only [hlm, ite_false, Option.map_none, Option.getD_none]
      rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by simp [hρs]; omega)]; rfl
  have hina : ∀ j < 3, ∀ l < 25, e.inp (58 + 25 * j + l) = (([a0, a1, a2].getD j #[]).toList.getD l 0).f₀ := by
    intro j hj l hl
    have hsz : ([a0, a1, a2].getD j #[]).size = m := by interval_cases j <;> assumption
    rw [hinp' _ (by omega)]
    simp only [rssLay, hM, show ¬ 58 + 25 * j + l < 8 by omega, show ¬ 58 + 25 * j + l < 58 by omega,
      show 58 + 25 * j + l < 133 by omega, ite_false, ite_true, show (58 + 25 * j + l - 58) % 25 = l by omega,
      show (58 + 25 * j + l - 58) / 25 = j by omega]
    by_cases hlm : l < m
    · simp only [hlm, ite_true, Option.map_some, Option.getD_some]
      rw [show 9 + 2 * m + 2 * m * j + 2 * l = 9 + 2 * m + 2 * m * j + 2 * l from rfl, hcl j hj _ (by omega),
        (encK_getD _ l).1]
    · simp only [hlm, ite_false, Option.map_none, Option.getD_none]
      rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by rw [Array.length_toList, hsz]; omega)]; rfl
  -- the value
  have hT : kRSS.T cst = rsSegT cst := rfl
  rw [hT]
  refine GM.ok_mono (g := rsSegT cst) (ok_rsSegT h1 hcst) fun o ho _ => ?_
  rw [ho]
  rw [hp, flatMap_encV_k, implP1_rsWeight, hR]
  simp only [List.map_cons, List.map_nil]
  rw [hra, hκv, hρa, ha0, ha1, ha2, show (Val.af ra).toAF = ra from rfl, show (Val.f κv).toF = κv from rfl,
    show (Val.ak ρa).toAK = ρa from rfl, show (Val.ak a0).toAK = a0 from rfl, show (Val.ak a1).toAK = a1 from rfl,
    show (Val.ak a2).toAK = a2 from rfl]
  rw [rsWeightF_seg ra hrs a0 a1 a2 ρa m hm1 hm2 ha0s ha1s ha2s hρs (hfz 0 (by norm_num)) (hfz 1 (by norm_num))
    (hfz 2 (by norm_num)) κv]
  refine congrArg encK ?_
  refine rsSegV_congr _ _ _ _ _ _ _ _ ?_ hinκ ?_ ?_
  · refine List.ext_getElem (by simp [hrs]) fun p h1p h2p => ?_
    simp only [List.getElem_map, List.getElem_range]
    rw [hin7 p (by simpa using h1p), List.getD_eq_getElem _ _ h2p]
  · exact List.map_congr_left fun l hl => hinρ l (List.mem_range.1 hl)
  · exact fun j hj l hl => hina j hj l hl

/-! ## Prototype 1's templates -/

/-- `rsWeight`'s locals (the mux's 207, then the template's 36,923; below `repB + 2^16`). -/
def cbRSS : ℕ := repB + 2 ^ 12

/-- **Prototype 1's replay templates** (SEG-R1): `linkWAll` (S-E14), `evalM`/`evalL` (zero), `rsWeight`. -/
def rtSeg1 : RT := (rtLinkSegW repB).orElse ((rtEvZ repB).orElse (rtKD kRSS repB cbRSS))

/-- **The replay templates per prototype** (`rtC1c` with prototype 1's `rtSeg1`). -/
def rtC1d (π : ℕ) : RT := if π = 0 then rtN0c else if π = 1 then rtSeg1 else RT.none

theorem rtC1d_ok {impl₀ : OpImpl} {base : NodeKind → OpImpl} (hZ : LinkZero impl₀) (hB : STBase base)
    (hS : SegBase impl₀) {π : ℕ} (hπ : π ≤ 1) (ι : Kind) :
    RTOkW (implP impl₀ base π ι) (Xof π) (rtC1d π) ι repB := by
  by_cases h : π = 0
  · subst h
    have h0 := rtC1c_ok hZ hB (π := 0) (by norm_num) ι
    simpa only [rtC1c, rtC1d, ite_true] using h0
  · obtain rfl : π = 1 := by omega
    simp only [rtC1d, one_ne_zero, ite_false, ite_true, rtSeg1]
    exact RT.orElse_okW (rtLinkSegW_ok base hZ repB ι)
      (RT.orElse_okW (rtEvZ_okW impl₀ base repB ι) (rtKD_okW repB cbRSS (kRSS_ok hS.1 ι)))

/-- **`RepOkW` for `rtC1d`.** -/
theorem repOkW_rtC1d {impl₀ : OpImpl} {base : NodeKind → OpImpl} (hZ : LinkZero impl₀) (hB : STBase base)
    (hS : SegBase impl₀) : RepOkW rtC1d impl₀ base := fun _ hπ ι => rtC1d_ok hZ hB hS hπ ι

/-- The certificate's base ops are a `SegBase`. -/
theorem segBase_implB : SegBase Sub4.implB := ⟨rfl, rfl⟩

/-- **`rtC1d` is sound at the certificate's ops.** -/
theorem repOkW_rtC1dB : RepOkW rtC1d Sub4.implB (fun _ => Sub4.implB) :=
  repOkW_rtC1d (fun _ _ => rfl) (fun _ => rfl) segBase_implB

/-! ## Controls -/

/-- (+) The segment's `rsWeight` shape is covered: `act` false, three claims. -/
theorem isRSS_pos : isRSS (.rsWeight 0 (fun _ => [1, 2, 3]) 4 5 (fun _ => false) 6) = true := by decide

/-- (−) … not with `act` true at some index (`β` would be read). -/
theorem isRSS_neg_act : isRSS (.rsWeight 0 (fun _ => [1, 2, 3]) 4 5 (fun ι => ι == .P30) 6) = false := by decide

/-- (−) … nor with two claims. -/
theorem isRSS_neg_claims : isRSS (.rsWeight 0 (fun _ => [1, 2]) 4 5 (fun _ => false) 6) = false := by decide

/-- (+) The three segment widths are served. -/
theorem rssIn_pos : ∀ m ∈ [23, 24, 25], rssIn [.af 7, .f, .f, .ak m, .ak m, .ak m, .ak m] = true := by decide

/-- (−) … not 26 (the template has 25 coordinates), not 22 (`kwS_one` needs 16 block coordinates). -/
theorem rssIn_neg : rssIn [.af 7, .f, .f, .ak 26, .ak 26, .ak 26, .ak 26] = false ∧
    rssIn [.af 7, .f, .f, .ak 22, .ak 22, .ak 22, .ak 22] = false := by decide

/-- (−) … nor claims of another width than `ρ`, nor another `r″`. -/
theorem rssIn_neg' : rssIn [.af 7, .f, .f, .ak 25, .ak 24, .ak 25, .ak 25] = false ∧
    rssIn [.af 8, .f, .f, .ak 25, .ak 25, .ak 25, .ak 25] = false := by decide

/-- (+) The forced positions at `m = 23` are the claims' `f₁` (encoding offset `9 + 2·23` for the
claims, then `f₁` at odd offsets). -/
theorem rssZf_pos : rssZf [.af 7, .f, .f, .ak 23, .ak 23, .ak 23, .ak 23] =
    (List.range 3).flatMap fun j => (List.range 23).map fun l => 56 + 46 * j + 2 * l := by
  simp only [rssZf, rssM]

end N4s
end FR
