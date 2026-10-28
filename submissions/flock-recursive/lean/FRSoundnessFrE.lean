-- New for `flock-recursive` (BLUEPRINT A.10 rows E1–E4 end, §5.2; stage S-G6).
import FRSoundnessFrRS0

/-!
# E: the Rows unit at the M rows, with E4's batched inner rounds (positions 209 … 311)

E is a row Spartan over the M rows (`rows`, 21 row bits, 23 cell bits, nodes only): the
zerocheck point after 209 (E1, 11 squeezes), 21 outer rounds from 221 (E2), the end absorb at
263 (`â_M ‖ b̂_M ‖ ĉ_M`), `κ_E` at 264 (E3), 23 inner rounds from 265 (E4), E4 end at 311. The
outer half is `FRSoundnessRows`' unit as is (`s0 = 209`, `b2 = 221`, `a = 21`, `nc = 23`,
`lrOn`; the precondition `209 + 1 + 11 = 221`). The inner half is new: since revision 3.13 E4
batches Lr's claim too (`finE` (iii)), so

* **`c4E`** `= â_M + κ_E b̂_M + κ_E² ĉ_M + κ_E³ v_L` with Lr's `v_L = â_L + κ_L b̂_L + κ_L² ĉ_L`
  (`c4 15 178`), and **`wE4`** `= W_M(κ_E) + κ_E³ W_L(κ_L)` on the 2^23 cells (`wInn`, the first
  table of `innerTables`); **`T4E`** `= [wE4, z]`, **`trueSum_T4E`** (the batched true values).
* **`BatBadE`** (E3's doom), **`D4E`** (E4's rounds, `D2`), **`RejInE`** (their checks).
* **`single_batchE`** (E3's `hsingle`): from a wrong M triple (`EndBad`) or a false Lr claim
  (Lr's `BatBad`, pending since Lr3), at most `3·2^128` answers `κ_E` make `c4E` true
  (`batch_count` at degree 3: four claims).
* **`habs_innerE`**, **`single_innerE`**, **`inner_appendE`**, **`rejInE_ok`**, **`D4E_reads`**.
* **E4 end** (311): **`RejE4`** is `finE` (iv)–(v) on the log (the last claim is
  `W(r′)·α_E` with `α_E` E4 end's value); **`habs_E4end`**: `D4E` before the absorb gives
  `RejE4`, or E's pending claim false (**`PendE`**: E4 end's value is not `ẑ(r′)`).
-/

namespace FR.Snd
open RecursionFast FR.Merkle Finset

set_option linter.constructorNameAsVariable false

/-! ## Positions -/

/-- **E's positions** (A.4, revision 3.13): the zerocheck after 209 (11 squeezes, phase 17), the
outer rounds from 221 (phase 18), the end absorb at 263 (19), `κ_E` at 264 (20), the inner rounds
from 265 (21), E4 end at 311 (22), RS0 at 312 (23). -/
theorem e_unit_pos :
    (209, 11) ∈ fsRanges ∧ phOf 209 = 16 ∧ phOf 210 = 17 ∧ phOf 220 = 17 ∧ phOf 221 = 18 ∧
    phOf 262 = 18 ∧ phOf 263 = 19 ∧ phOf 264 = 20 ∧ phOf 265 = 21 ∧ phOf 310 = 21 ∧
    phOf 311 = 22 ∧ phOf 312 = 23 := by
  refine ⟨by rw [fsRanges_eq]; simp, ?_⟩
  have hph : ∀ q, phOf q = (fsStarts.filter (· ≤ q)).length - 1 := fun _ => rfl
  simp only [hph, fsStarts_eq]
  exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

/-! ## The outer half: `FRSoundnessRows`' unit at E's positions -/

section Outer
variable (rows : List Circ.Row)

open Classical in
/-- **E1's charge** (A.10 E1: `21/2^128 ≤ deltaR`). -/
theorem e_zc_hfin {Dk : ℕ → Log → Log → Prop} {Bg : Log → Log → Prop} (hBg : Reads 210 Bg)
    (hprev : Dk (phOf 209) = fun L es => Bg L es ∨ RowsBad rows 21 23 lrOn L es)
    (hfin : Dk (phOf 210) =
      msD (Dk (phOf 209)) (fun L es => Bg L es ∨ ZCw rows 21 23 lrOn 209 L es) 209 11)
    (L es₀ : Log) (hl : es₀.length = 210) : condCount (DPos (Dp Dk)) L es₀ 11 [] ≤ deltaR :=
  zc_hfin e_unit_pos.1 hBg (by norm_num) (by norm_num) (by norm_num) hprev hfin L es₀ hl

/-- Into E2 (`habs` at 221). -/
theorem e_habs_outer {L es : Log} (x : ByteArray × Digest) (hl : es.length = 221)
    (hz : ZCw rows 21 23 lrOn 209 L es) :
    D3 221 (fun _ _ => 0) (nr3 21 lrOn) outerExpr (T3 rows 21 23 lrOn 209) L (es ++ [x]) :=
  habs_outer (by norm_num) (by norm_num) x hl hz

open Classical in
/-- E2's squeezes (`3·2^128`). -/
theorem e_single_outer (L es : Log) :
    (univ.filter fun d => D3 221 (fun _ _ => 0) (nr3 21 lrOn) outerExpr (T3 rows 21 23 lrOn 209) L es ∧
      ¬ D3 221 (fun _ _ => 0) (nr3 21 lrOn) outerExpr (T3 rows 21 23 lrOn 209) L (ext1 es d)).card ≤
      3 * 2 ^ 128 :=
  single_outer (by norm_num) (by norm_num) L es

/-- At E's end absorb (263). -/
theorem e_habs_end {L es : Log} (x : ByteArray × Digest) (hl : es.length = 263)
    (hd : D3 221 (fun _ _ => 0) (nr3 21 lrOn) outerExpr (T3 rows 21 23 lrOn 209) L es) :
    RejEnd 21 lrOn 209 221 L (es ++ [x]) ∨ EndBad rows 21 23 lrOn 221 L (es ++ [x]) :=
  habs_end (by norm_num) (by norm_num) x hl hd

theorem e_rejEnd_ok (hpe : fsItems[263]? ≠ some .squeeze) : RejOK (RejEnd 21 lrOn 209 221) :=
  rejEnd_ok (by norm_num) (by norm_num) hpe

end Outer

/-! ## Lr (positions 169 … 209): the same unit at `lRows` (assembly only) -/

/-- Into Lr2 (`habs` at 178; precondition `169 + 1 + 8 = 178`). -/
theorem lr_habs_outer {L es : Log} (x : ByteArray × Digest) (hl : es.length = 178)
    (hz : ZCw Layout.lRows 15 23 lrOn 169 L es) :
    D3 178 (fun _ _ => 0) (nr3 15 lrOn) outerExpr (T3 Layout.lRows 15 23 lrOn 169) L (es ++ [x]) :=
  habs_outer (by norm_num) (by norm_num) x hl hz

open Classical in
/-- Lr2's squeezes (`3·2^128`). -/
theorem lr_single_outer (L es : Log) :
    (univ.filter fun d =>
      D3 178 (fun _ _ => 0) (nr3 15 lrOn) outerExpr (T3 Layout.lRows 15 23 lrOn 169) L es ∧
      ¬ D3 178 (fun _ _ => 0) (nr3 15 lrOn) outerExpr (T3 Layout.lRows 15 23 lrOn 169) L
        (ext1 es d)).card ≤ 3 * 2 ^ 128 :=
  single_outer (by norm_num) (by norm_num) L es

/-- At Lr's end absorb (208). -/
theorem lr_habs_end {L es : Log} (x : ByteArray × Digest) (hl : es.length = 208)
    (hd : D3 178 (fun _ _ => 0) (nr3 15 lrOn) outerExpr (T3 Layout.lRows 15 23 lrOn 169) L es) :
    RejEnd 15 lrOn 169 178 L (es ++ [x]) ∨ EndBad Layout.lRows 15 23 lrOn 178 L (es ++ [x]) :=
  habs_end (by norm_num) (by norm_num) x hl hd

/-! ## The inner half: E4 with Lr's claim batched in -/

/-- Counting under an implication, the decidability instances taken from the context (so that
two classical `filter`s with different instance terms compare without unfolding them). -/
theorem card_filter_imp {P Q : Digest → Prop} {iP : DecidablePred P} {iQ : DecidablePred Q}
    (h : ∀ d, P d → Q d) : (@filter _ P iP univ).card ≤ (@filter _ Q iQ univ).card := by
  refine card_le_card fun a ha => ?_
  simp only [mem_filter, mem_univ, true_and] at ha ⊢; exact h a ha

/-- A row Spartan's inner weight at `(r_x, ρ)` (`innerTables`' first table). -/
noncomputable def wInn {a nc : ℕ} (A B C : Fin (2 ^ a) → Fin (2 ^ nc) → F) (rx : Fin a → F) (ρ : F)
    (y : Fin (2 ^ nc)) : F :=
  matMle A rx (cube y) + ρ * matMle B rx (cube y) + ρ ^ 2 * matMle C rx (cube y)

section Inner
variable (rows : List Circ.Row)

/-- **E4's weight**: M's batched by `κ_E`, plus `κ_E³` times Lr's batched by `κ_L`. -/
noncomputable def wE4 (es : Log) (y : Fin (2 ^ 23)) : F :=
  wInn (mA rows 21 23) (mB rows 21 23) (mC rows 21 23) (ptOf 21 (rxs 21 221 es)) (kapB 21 221 es) y +
    kapB 21 221 es ^ 3 * wInn (mA Layout.lRows 15 23) (mB Layout.lRows 15 23) (mC Layout.lRows 15 23)
      (ptOf 15 (rxs 15 178 es)) (kapB 15 178 es) y

/-- **E4's initial claim** (`finE` (iii)): `â_M + κ_E b̂_M + κ_E² ĉ_M + κ_E³ v_L`. -/
def c4E (L es : Log) : F := c4 21 221 L es + kapB 21 221 es ^ 3 * c4 15 178 L es

/-- E4's tables `[wE4, z]` (none off the nodes). -/
noncomputable def T4E (L es : Log) : Array (Array F) :=
  if lrOn (kindOf es) then #[Array.ofFn (wE4 rows es), Array.ofFn (zC 23 L es)] else #[]

/-- **E3's doom**: the batched claim is false after `κ_E`. -/
noncomputable def BatBadE (L es : Log) : Prop :=
  lrOn (kindOf es) = true ∧ 264 < es.length ∧ c4E L es ≠ trueSum innerExpr (T4E rows L es) 23

/-- E4's rounds as a `D2` (F, degree 2, from 265). -/
abbrev D2E : Log → Log → Prop :=
  D2 265 16 readF (fun d => chF d 0) c4E (nr4 23 lrOn) innerExpr (T4E rows)

/-- **E4's doom**: on a node, the rounds' claim is false (a leaf runs E4's rounds as dummies). -/
def D4E (L es : Log) : Prop := lrOn (kindOf es) = true ∧ D2E rows L es

/-- **E4's round checks** fail. -/
def RejInE (L es : Log) : Prop :=
  ∃ l < nr4 23 lrOn (kindOf es), 265 + 2 * l < es.length ∧
    ¬ Chk2 265 16 readF (fun d => chF d 0) c4E L es l

/-- The binding of E's RS claim (`finE` (v)): its value is E4 end's message. -/
def okE (es : Log) (v : F) : Prop := v = readF (msgAt es 311) 0

/-- E4 end's point `r′` (E4's 23 challenges). -/
def rE4 (es : Log) : List F := rchs2 265 (fun d => chF d 0) es 23

/-- **`finE` (iv) fails** (from 312): E4's last claim is not `W(r′)·α_E`, `α_E` E4 end's value. -/
noncomputable def RejE4 (L es : Log) : Prop :=
  312 ≤ es.length ∧ lrOn (kindOf es) = true ∧
    clR2 265 16 readF (fun d => chF d 0) c4E L es 23 ≠
      mle (wE4 rows es) (ptOf 23 (rE4 es)) * readF (msgAt es 311) 0

/-- **E's pending claim is false** (after E4 end): its value is not `ẑ(r′)`. -/
noncomputable def PendE (L es : Log) : Prop :=
  lrOn (kindOf es) = true ∧ 311 < es.length ∧
    ¬ okE es (mle (zC 23 L es) (ptOf 23 (rE4 es)))

variable {rows}

theorem wE_congr {es es' : Log} (h : Agree es es' 265) : wE4 rows es = wE4 rows es' := by
  funext y
  simp only [wE4, rxs_agree (a := 21) (b2 := 221) h (by norm_num),
    rxs_agree (a := 15) (b2 := 178) h (by norm_num), kapB_agree (a := 21) (b2 := 221) h le_rfl,
    kapB_agree (a := 15) (b2 := 178) h (by norm_num)]

theorem c4E_agree {L L' es es' : Log} {p : ℕ} (h : Agree es es' p) (hp : 265 ≤ p) :
    c4E L es = c4E L' es' := by
  simp only [c4E, c4_agree (a := 21) (b2 := 221) (L := L) (L' := L') h hp,
    c4_agree (a := 15) (b2 := 178) (L := L) (L' := L') h (by omega),
    kapB_agree (a := 21) (b2 := 221) h (by omega)]

theorem T4E_same {L es L' es' : Log} {p : ℕ} (h : Same L es L' es' p) (hp : 265 ≤ p) :
    T4E rows L es = T4E rows L' es' := by
  simp only [T4E, h.kind (by omega), zC_same h (by omega), wE_congr (h.1.mono hp)]

theorem T4E_local : TruthLocal2 265 c4E (T4E rows) := fun L es es' h =>
  ⟨T4E_same (same_of_agree L h) le_rfl, c4E_agree h le_rfl⟩

theorem T4E_size (L es : Log) : ∀ t ∈ T4E rows L es, t.size = 2 ^ nr4 23 lrOn (kindOf es) := by
  unfold T4E nr4
  split_ifs with h
  · simp
  · simp

/-- **The batched true value** (`inner_trueSum` twice). -/
theorem trueSum_T4E {L es : Log} (h : lrOn (kindOf es) = true) :
    trueSum innerExpr (T4E rows L es) 23 =
      trueSum innerExpr (T4 rows 21 23 lrOn 221 L es) 23 +
        kapB 21 221 es ^ 3 * trueSum innerExpr (T4 Layout.lRows 15 23 lrOn 178 L es) 23 := by
  simp only [T4E, T4, h, ite_true, innerTables, prod_trueSum, wE4, wInn, mul_sum,
    ← sum_add_distrib]
  exact sum_congr rfl fun _ _ => by ring

theorem batBadE_reads : Reads 265 (BatBadE rows) := fun L es L' es' h1 h2 h => by
  have hk := h.kind (by omega)
  simp only [BatBadE, hk, T4E_same h le_rfl, c4E_agree (L := L) (L' := L') h.1 le_rfl]
  exact and_congr_right fun _ => ⟨fun h' => ⟨by omega, h'.2⟩, fun h' => ⟨by omega, h'.2⟩⟩

/-- **Four claims batched by one challenge** (`batch_count` at degree 3, over abstract values so
that no concrete claim is ever unfolded by the kernel). -/
theorem batch_count4 (P : Digest → Prop) [DecidablePred P] {v0 v1 v2 v3 t0 t1 t2 t3 : F}
    (hvt : v0 ≠ t0 ∨ v1 ≠ t1 ∨ v2 ≠ t2 ∨ v3 ≠ t3)
    (h : ∀ a, P a → v0 + chF a 0 * v1 + chF a 0 ^ 2 * v2 + chF a 0 ^ 3 * v3 =
      t0 + chF a 0 * t1 + chF a 0 ^ 2 * t2 + chF a 0 ^ 3 * t3) :
    (univ.filter P).card ≤ 3 * 2 ^ 128 := by
  refine batch_count (k := 3) P ![v0, v1, v2, v3] ![t0, t1, t2, t3] ?_ fun a ha => ?_
  · intro he
    rcases hvt with h0 | h0 | h0 | h0
    · exact h0 (by simpa using congrFun he 0)
    · exact h0 (by simpa using congrFun he 1)
    · exact h0 (by simpa using congrFun he 2)
    · exact h0 (by simpa using congrFun he 3)
  · have := h a ha
    simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.val_zero, Fin.val_succ,
      Matrix.cons_val_zero, Matrix.cons_val_succ, pow_zero, one_mul, add_zero]
    linear_combination this

open Classical in
/-- **E3's count** (`hsingle` at 264, A.10 E3): from a wrong M triple or a false Lr claim, at
most `3·2^128` answers `κ_E` make E4's initial claim true (four claims, degree 3). -/
theorem single_batchE (L es : Log) (hl : es.length = 264) :
    (univ.filter fun d => (EndBad rows 21 23 lrOn 221 L es ∨
        BatBad Layout.lRows 15 23 lrOn 178 L es) ∧ ¬ BatBadE rows L (ext1 es d)).card ≤
      3 * 2 ^ 128 := by
  have hS : ∀ d, Same L (ext1 es d) L es 264 := fun d => hl ▸ same_ext1 L es d
  have hk : ∀ d, kindOf (ext1 es d) = kindOf es := fun d => (hS d).kind (by norm_num)
  by_cases hon : lrOn (kindOf es) = true
  swap
  · rw [filter_false_of_mem fun d _ hd => hd.1.elim (fun h => hon h.1) fun h => hon h.1,
      card_empty]
    exact Nat.zero_le _
  by_cases hD : EndBad rows 21 23 lrOn 221 L es ∨ BatBad Layout.lRows 15 23 lrOn 178 L es
  swap
  · rw [filter_false_of_mem fun d _ hd => hD hd.1, card_empty]
    exact Nat.zero_le _
  refine batch_count4 _ (v0 := vEnd 21 221 es 0) (v1 := vEnd 21 221 es 1)
    (v2 := vEnd 21 221 es 2) (v3 := c4 15 178 L es) (t0 := (triT rows 21 23 221 L es).1)
    (t1 := (triT rows 21 23 221 L es).2.1) (t2 := (triT rows 21 23 221 L es).2.2)
    (t3 := trueSum innerExpr (T4 Layout.lRows 15 23 lrOn 178 L es) 23) ?_ fun d hd => ?_
  · by_contra hc
    simp only [not_or, not_not] at hc
    exact hD.elim (fun h => h.2.2 (Prod.ext hc.1 (Prod.ext hc.2.1 hc.2.2.1)))
      fun h => h.2.2 hc.2.2.2
  have hag : Agree (ext1 es d) es 264 := (hS d).1
  have hκ : kapB 21 221 (ext1 es d) = chF d 0 := by
    simp only [kapB, fAt, ansAt, show 221 + 2 * 21 + 1 = es.length by omega]
    exact congrArg (chF · 0) (entAt_ext1 es d)
  have heq : c4E L (ext1 es d) = trueSum innerExpr (T4E rows L (ext1 es d)) 23 := by
    by_contra hne
    exact hd.2 ⟨by rw [hk]; exact hon, by simp [ext1]; omega, hne⟩
  rw [trueSum_T4E (by rw [hk]; exact hon)] at heq
  have hT4 : T4 rows 21 23 lrOn 221 L (ext1 es d) = innerTables (ptOf 21 (rxs 21 221 es)) (chF d 0)
      (mA rows 21 23) (mB rows 21 23) (mC rows 21 23) (zC 23 L es) := by
    simp only [T4, hk, hon, ite_true, hκ, rxs_agree (a := 21) (b2 := 221) hag (by norm_num),
      zC_same (hS d) (by norm_num)]
  have hT4L : T4 Layout.lRows 15 23 lrOn 178 L (ext1 es d) = T4 Layout.lRows 15 23 lrOn 178 L es :=
    T4_same (hS d) (by norm_num) (by norm_num)
  have hcL : c4 15 178 L (ext1 es d) = c4 15 178 L es :=
    c4_agree (a := 15) (b2 := 178) hag (by norm_num)
  have hcM : c4 21 221 L (ext1 es d) = vEnd 21 221 es 0 + chF d 0 * vEnd 21 221 es 1 +
      chF d 0 ^ 2 * vEnd 21 221 es 2 := by
    simp only [c4, hκ, vEnd_agree (a := 21) (b2 := 221) hag (by norm_num)]
  rw [hT4, hT4L, inner_trueSum, hκ, c4E, hcL, hκ, hcM] at heq
  simp only [triT]
  exact heq

/-- **Into E4** (`habs` at 265): a false batched claim is E4's doom. -/
theorem habs_innerE {L es : Log} (x : ByteArray × Digest) (hl : es.length = 265)
    (hb : BatBadE rows L es) : D4E rows L (es ++ [x]) := by
  have hS := same_append L es [x]
  have hk : kindOf (es ++ [x]) = kindOf es := hS.kind (by omega)
  refine ⟨by rw [hk]; exact hb.1, by simp; omega, ?_⟩
  have ha0 : ans3 265 (nr4 23 lrOn) (es ++ [x]) = 0 := by
    simp only [ans3, List.length_append, List.length_singleton, hl]; simp
  rw [ha0]
  simp only [Wrong2, clR2, rchs2, List.range_zero, List.map_nil, bindAll, Nat.sub_zero]
  rw [T4E_same (hl ▸ hS) le_rfl, hk, c4E_agree (L := L) (L' := L) (hl ▸ hS).1 le_rfl]
  simp only [nr4, hb.1, ite_true]
  exact hb.2.2

theorem D4E_esc {L es : Log} (d : Digest) (hd : D4E rows L es ∧ ¬ D4E rows L (ext1 es d)) :
    D2E rows L es ∧ ¬ D2E rows L (ext1 es d) := by
  obtain ⟨⟨hon, h2⟩, hn⟩ := hd
  have hk : kindOf (ext1 es d) = kindOf es := (same_ext1 L es d).kind (by have := h2.1; omega)
  exact ⟨h2, fun h => hn ⟨hk ▸ hon, h⟩⟩

open Classical in
/-- **An E4 round's squeeze** (`D2_single`, `2·2^128`). -/
theorem single_innerE (L es : Log)
    (hchk : ∀ j, es.length = 265 + 2 * j + 1 → j < nr4 23 lrOn (kindOf es) →
      Chk2 265 16 readF (fun d => chF d 0) c4E L es j) :
    (univ.filter fun d => D4E rows L es ∧ ¬ D4E rows L (ext1 es d)).card ≤ 2 * 2 ^ 128 :=
  (card_filter_imp (D4E_esc (rows := rows) (L := L) (es := es))).trans
    (D2_single (by omega) T4E_local innerExpr_deg card_chF_fiber T4E_size L es hchk)

/-- An E4 round's absorb keeps the doom. -/
theorem inner_appendE {L es : Log} (x : ByteArray × Digest) (hlen : 265 < es.length)
    (hc : (es.length - 265) % 2 = 0 ∨ nr4 23 lrOn (kindOf es) ≤ (es.length - 265) / 2) :
    D4E rows L (es ++ [x]) ↔ D4E rows L es := by
  unfold D4E
  rw [(same_append L es [x]).kind (by omega)]
  exact and_congr_right fun _ => D2_append_iff (by omega) T4E_local x hlen hc

theorem chk_of_not_rejInE {L es : Log} (hr : ¬ RejInE L es) (j : ℕ)
    (hj : es.length = 265 + 2 * j + 1) (hjn : j < nr4 23 lrOn (kindOf es)) :
    Chk2 265 16 readF (fun d => chF d 0) c4E L es j := by
  by_contra hc; exact hr ⟨j, hjn, by omega, hc⟩

theorem D4E_same {L L' X : Log} {p : ℕ} (h : Same L X L' X p) (hp : 265 ≤ p) :
    D4E rows L X ↔ D4E rows L' X :=
  and_congr_right fun _ => D2_congrL (T4E_same h hp) rfl

/-- **Once every E4 round is answered, E4's doom reads before 312.** -/
theorem D4E_reads : Reads 312 (D4E rows) := fun L es L' es' h1 h2 h => by
  have hk := h.kind (by omega)
  have hans : ∀ Y : Log, 311 ≤ Y.length → ans3 265 (nr4 23 lrOn) Y = nr4 23 lrOn (kindOf Y) :=
    fun Y hY => by unfold ans3 nr4; split_ifs <;> (simp; try omega)
  unfold D4E D2E D2 Wrong2
  rw [hans es (by omega), hans es' (by omega), hk, T4E_same h (by omega),
    clR2_same (L' := L') (es' := es') (c4E_agree h.1 (by omega))
      (h.1.mono (by unfold nr4; split_ifs <;> omega)),
    rchs2_congr (h.1.mono (by unfold nr4; split_ifs <;> omega))]
  exact and_congr_right fun _ => and_congr_left fun _ => ⟨fun _ => by omega, fun _ => by omega⟩

theorem chkE_same {L L' es es' : Log} {p : ℕ} (h : Same L es L' es' p) {j : ℕ}
    (hj : 265 + 2 * j < p) :
    Chk2 265 16 readF (fun d => chF d 0) c4E L es j ↔
      Chk2 265 16 readF (fun d => chF d 0) c4E L' es' j := by
  have hg : g2At 265 16 readF es j = g2At 265 16 readF es' j := by
    simp only [g2At, msgAt, h.1 (265 + 2 * j) hj]
  have hc := clR2_same (b := 265) (wd := 16) (rd := readF) (ch := fun d => chF d 0)
    (c4E_agree (L := L) (L' := L') (h.1.mono (by omega)) (le_refl 265)) (l := j)
    (h.1.mono (by omega))
  simp only [Chk2, hg, hc]

theorem rejInE_mono {L es : Log} (x : ByteArray × Digest) (h : RejInE L es) :
    RejInE L (es ++ [x]) := by
  obtain ⟨j, hj, hlt, hc⟩ := h
  have hS := same_append L es [x]
  refine ⟨j, by rw [hS.kind (by omega)]; exact hj, by simp; omega, fun h' => hc ?_⟩
  exact (chkE_same hS (by omega)).mp h'

/-- **`RejOK` for E4's round checks**, given that their messages are absorbs. -/
theorem rejInE_ok (habs4 : ∀ j < 23, fsItems[265 + 2 * j]? ≠ some .squeeze) : RejOK RejInE where
  mono L es x := rejInE_mono x
  sq L es x hit := by
    refine ⟨fun ⟨j, hj, hlt, hc⟩ => ?_, rejInE_mono x⟩
    simp only [List.length_append, List.length_singleton] at hlt
    have hS := same_append L es [x]
    rw [hS.kind (by omega)] at hj
    by_cases he : 265 + 2 * j = es.length
    · exact absurd (he ▸ hit) (habs4 j (lt_of_lt_of_le hj (nr4_le _)))
    exact ⟨j, hj, by omega, fun h' => hc ((chkE_same hS (by omega)).mpr h')⟩
  stab L i hb hci X hX := by
    have hS := same_stabX hb hci hX
    by_cases h0 : X.length = 0
    · constructor <;> rintro ⟨j, -, hlt, -⟩ <;> omega
    unfold RejInE
    rw [hS.kind (by omega)]
    exact exists_congr fun j => and_congr_right fun _ => and_congr_right fun _ =>
      not_congr (chkE_same hS (by omega))

/-! ## E4 end (311) -/

theorem innerExpr_eval2 {R : Type*} [CommRing R] (v : ℕ → R) : innerExpr.eval v = v 0 * v 1 := rfl

theorem arrGetD_pair0 {α : Type*} (a b d : α) : (#[a, b] : Array α).getD 0 d = a := rfl

theorem arrGetD_pair1 {α : Type*} (a b d : α) : (#[a, b] : Array α).getD 1 d = b := rfl

theorem rE4_def (es : Log) : rchs2 265 (fun d => chF d 0) es 23 = rE4 es := rfl

theorem rE4_agree {es es' : Log} {p : ℕ} (h : Agree es es' p) (hp : 311 ≤ p) :
    rE4 es = rE4 es' := rchs2_congr (h.mono (by omega))

/-- **`habs` at E4 end** (A.10 E4 end, `finE` (iv)–(v)): with every E4 round answered and doomed,
after E4 end's absorb either `finE` (iv) fails on the log, or E's pending claim is false. -/
theorem habs_E4end {L es : Log} (x : ByteArray × Digest) (hl : es.length = 311)
    (hd : D4E rows L es) : RejE4 rows L (es ++ [x]) ∨ PendE L (es ++ [x]) := by
  have hS : Same L (es ++ [x]) L es 311 := hl ▸ same_append L es [x]
  have hk : kindOf (es ++ [x]) = kindOf es := hS.kind (by norm_num)
  obtain ⟨hon, -, hw⟩ := hd
  have ha : ans3 265 (nr4 23 lrOn) es = 23 := by
    simp only [ans3, nr4, hon, ite_true, hl]; simp
  rw [ha] at hw
  unfold Wrong2 at hw
  simp only [nr4, hon, ite_true, Nat.sub_self] at hw
  have hfin : trueSum innerExpr (bindAll (T4E rows L es) (rchs2 265 (fun d => chF d 0) es 23)) 0 =
      mle (wE4 rows es) (ptOf 23 (rE4 es)) * mle (zC 23 L es) (ptOf 23 (rE4 es)) := by
    simp only [T4E, hon, ite_true]
    rw [trueSum_bindAll' _ _ _ (by simp [rchs2]) (prod_sizes _ _), innerExpr_eval2, arrGetD_pair0,
      arrGetD_pair1, tbl_ofFn, tbl_ofFn, rE4_def]
  rw [hfin] at hw
  have hag : Agree (es ++ [x]) es 311 := hS.1
  have hc : clR2 265 16 readF (fun d => chF d 0) c4E L (es ++ [x]) 23 =
      clR2 265 16 readF (fun d => chF d 0) c4E L es 23 :=
    clR2_same (c4E_agree hag (by norm_num)) (hag.mono (by norm_num))
  by_cases hrej : RejE4 rows L (es ++ [x])
  · exact .inl hrej
  right
  refine ⟨by rw [hk]; exact hon, by simp; omega, fun hok => ?_⟩
  have hchk : clR2 265 16 readF (fun d => chF d 0) c4E L (es ++ [x]) 23 =
      mle (wE4 rows (es ++ [x])) (ptOf 23 (rE4 (es ++ [x]))) * readF (msgAt (es ++ [x]) 311) 0 := by
    by_contra hne; exact hrej ⟨by simp; omega, by rw [hk]; exact hon, hne⟩
  rw [hc, wE_congr (hag.mono (by norm_num)), rE4_agree hag le_rfl, ← hok, rE4_agree hag le_rfl,
    zC_same hS (by norm_num)] at hchk
  exact hw hchk

/-! ## Controls -/

/-- Control (positive): off the nodes E3 is never doomed. -/
theorem not_batBadE_leaf {L es : Log} (h : kindOf es = .P30) : ¬ BatBadE rows L es := by
  rintro ⟨hon, -⟩; rw [h] at hon; exact absurd hon (by decide)

/-- Control (negative, non-vacuous): on a node, a batched claim differing from the true value
after `κ_E` is E3's doom. -/
theorem batBadE_of_ne {L es : Log} (hn : (kindOf es).isNode = true) (hl : 264 < es.length)
    (h : c4E L es ≠ trueSum innerExpr (T4E rows L es) 23) : BatBadE rows L es := ⟨hn, hl, h⟩

/-- Control: E4's initial claim with a zero Lr claim is the Rows unit's three-claim batch. -/
theorem c4E_of_lr_zero {L es : Log} (h : c4 15 178 L es = 0) : c4E L es = c4 21 221 L es := by
  simp [c4E, h]

/-- Control (negative): with E4 end's value equal to `ẑ(r′)`, E's claim is not pending. -/
theorem not_pendE {L es : Log} (h : readF (msgAt es 311) 0 = mle (zC 23 L es) (ptOf 23 (rE4 es))) :
    ¬ PendE L es := fun ⟨_, _, hn⟩ => hn h.symm

end Inner

end FR.Snd
