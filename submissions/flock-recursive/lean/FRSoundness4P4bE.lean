-- New for `flock-recursive` (BLUEPRINT revision 4.1, A.10 rows Lr1–Lr3, E1–E4 end, §5.2; stage
-- P4b): Lr and E at `seq4`'s positions, per node kind, with E4's batched inner rounds. The 3.x
-- template is `FRSoundnessFrE` (and `FRSoundnessRows`' Lr instances).
import FRNodeCircuit4

/-!
# Lr and E at revision 4.1 (P4b)

Positions (`p4b_pos`, against `fsStarts4_eq`/`fsRanges4_eq`): Lr1 after 169 (9 squeezes), Lr2 from
179 (17 slots), Lrend 213, Lr3 (`κ_L`) 214, E1 after 214 (12 squeezes), E2 from 227 (23 slots),
Eend 273, E3 (`κ_E`) 274, E4 from 275 (25 slots), E4 end 325, RS0 326. The absorbs the checks read
are not squeezes (`p4b_abs`).

Every doom is gated by `OnNode` (`FRSoundness4P4bNames`): at node kind `κ` the unit runs with
`lrR κ` Lr row bits, `e2R κ` M row bits, `ncR κ` cell bits; the slots stay `seq4`'s. The obligations
come in the form 3.x's `FRSoundnessFrE` gives them, lifted through the gate (**`onNode_card`**):

* **Lr**: `lr4_zc_count` (Lr1's charge `≤ lrR κ/2^128`), `lr4_habs_outer`, `lr4_single_outer`,
  `lr4_outer_append`, `lr4_habs_end` (at 213: `RejEndLr4` or `EndBadLr4`), `lr4_single_batch` (at
  214), `rejEndLr4_log`.
* **E, outer half**: the same at 214/227/273 (`e4_*`), `rejEndE4_log`.
* **E4, batched with Lr** (`finE` (iii)): `trueSum_TEb4` (the batched true value),
  **`e4_single_batchE`** (E3: from a wrong M triple or a false Lr claim, `≤ 3·2^128` answers
  `κ_E`), `e4_habs_innerE` (into E4), `e4_single_innerE` (`≤ 2·2^128` from `¬ RejInE4`),
  `e4_inner_appendE`, `D4E4_reads`, `rejInE4_log`.
* **E4 end** (325, `finE` (iv)–(v)): **`e4_habs_end4`**: E4's doom before the absorb gives
  `RejFinE4` or `PendE4` after it; `rejFinE4_log`.
-/

namespace FR.Snd.P4b
open RecursionFast FR.Merkle FR.Rev4 Finset
open scoped NNReal

set_option linter.constructorNameAsVariable false

/-! ## Positions -/

/-- **P4b's positions** at `seq4` (`fsStarts4_eq`, `fsRanges4_eq`). -/
theorem p4b_pos : (169, 9) ∈ fsRanges4 ∧ (214, 12) ∈ fsRanges4 ∧ (326, 4) ∈ fsRanges4 ∧
    phStart4 13 = 170 ∧ phStart4 14 = 179 ∧ phStart4 15 = 213 ∧ phStart4 16 = 214 ∧
    phStart4 17 = 215 ∧ phStart4 18 = 227 ∧ phStart4 19 = 273 ∧ phStart4 20 = 274 ∧
    phStart4 21 = 275 ∧ phStart4 22 = 325 ∧ phStart4 23 = 326 ∧ phStart4 24 = 327 ∧
    phStart4 25 = 331 ∧ phStart4 26 = 332 := by
  have h4 : ∀ k, phStart4 k = fsStarts4.getD k 0 := fun _ => rfl
  simp only [fsRanges4_eq, h4, fsStarts4_eq]
  decide

/-- The absorbs the checks read (Lrend, Eend, E4's rounds, E4 end, RS0) are not squeezes. -/
def absOK4 : Bool :=
  ([213, 273, 325, 326] ++ (List.range 25).map (fun j => 275 + 2 * j)).all fun p =>
    fsItems4[p]? != some Item.squeeze

theorem absOK4_eq : absOK4 = true := by
  rw [absOK4, fsItems4, seq4_eq]; decide +kernel

theorem p4b_abs : fsItems4[213]? ≠ some .squeeze ∧ fsItems4[273]? ≠ some .squeeze ∧
    fsItems4[325]? ≠ some .squeeze ∧ fsItems4[326]? ≠ some .squeeze ∧
    ∀ j < 25, fsItems4[275 + 2 * j]? ≠ some .squeeze := by
  have h := absOK4_eq
  simp only [absOK4, List.all_eq_true, List.mem_append, List.mem_cons, List.mem_map,
    List.mem_range, bne_iff_ne, ne_eq] at h
  exact ⟨h _ (.inl (.inl rfl)), h _ (.inl (.inr (.inl rfl))), h _ (.inl (.inr (.inr (.inl rfl)))),
    h _ (.inl (.inr (.inr (.inr (.inl rfl))))), fun j hj => h _ (.inr ⟨j, hj, rfl⟩)⟩

/-- The real counts fit the slots. -/
theorem dims_le' (κ : NodeKind) : lrR κ ≤ 17 ∧ e2R κ ≤ 23 ∧ ncR κ ≤ 25 ∧ 1 ≤ ncR κ := by
  cases κ <;> decide

/-! ## The gate -/

theorem kindOfC_append {es : Log} (xs : Log) (h : 1 ≤ es.length) :
    kindOfC (es ++ xs) = kindOfC es := kindOfC_congr (agree_append es xs h)

theorem kindOfC_ext1 {es : Log} (d : Digest) (h : 1 ≤ es.length) :
    kindOfC (ext1 es d) = kindOfC es := kindOfC_append _ h

theorem onNode_or {P Q : NodeKind → Log → Log → Prop} {L es : Log} :
    (OnNode P L es ∨ OnNode Q L es) ↔ OnNode (fun κ L es => P κ L es ∨ Q κ L es) L es := by
  constructor
  · rintro (⟨κ, hk, h⟩ | ⟨κ, hk, h⟩)
    · exact ⟨κ, hk, .inl h⟩
    · exact ⟨κ, hk, .inr h⟩
  · rintro ⟨κ, hk, h | h⟩
    · exact .inl ⟨κ, hk, h⟩
    · exact .inr ⟨κ, hk, h⟩

/-- A doom preserved kind by kind is preserved through the gate (`es` nonempty). -/
theorem onNode_imp {P Q : NodeKind → Log → Log → Prop} {L L' es es' : Log}
    (hk : kindOfC es' = kindOfC es) (h : ∀ κ, kindOfC es = .node κ → P κ L es → Q κ L' es')
    (hp : OnNode P L es) : OnNode Q L' es' := by
  obtain ⟨κ, hκ, hP⟩ := hp
  exact ⟨κ, hk.trans hκ, h κ hκ hP⟩

theorem onNode_congr {P Q : NodeKind → Log → Log → Prop} {L L' es es' : Log}
    (hk : kindOfC es' = kindOfC es) (h : ∀ κ, kindOfC es = .node κ → (P κ L es ↔ Q κ L' es')) :
    OnNode P L es ↔ OnNode Q L' es' :=
  ⟨onNode_imp hk fun κ hκ => (h κ hκ).1,
    onNode_imp hk.symm fun κ hκ => (h κ (hk.symm.trans hκ)).2⟩

open Classical in
/-- **Counting through the gate**: an escape of a gated doom is an escape at the chain's kind. -/
theorem onNode_card {P Q : NodeKind → Log → Log → Prop} {N : ℕ} (L es : Log) (h1 : 1 ≤ es.length)
    (h : ∀ κ, kindOfC es = .node κ →
      (univ.filter fun d => P κ L es ∧ ¬ Q κ L (ext1 es d)).card ≤ N) :
    (univ.filter fun d => OnNode P L es ∧ ¬ OnNode Q L (ext1 es d)).card ≤ N := by
  rcases hk : kindOfC es with σ | κ
  · rw [filter_false_of_mem fun d _ hd => not_onNode_seg hk hd.1]; simp
  · refine (card_filter_imp fun d ⟨hP, hnQ⟩ => ⟨(onNode_iff hk).1 hP, fun hq => hnQ ?_⟩).trans
      (h κ hk)
    exact (onNode_iff ((kindOfC_ext1 d h1).trans hk)).2 hq

theorem readsS_onNode {R : FSrc} {p : ℕ} {P : NodeKind → Log → Log → Prop} (hp : 1 ≤ p)
    (h : ∀ κ, ReadsS R p (P κ)) : ReadsS R p (OnNode P) := fun L es L' es' h1 h2 hS =>
  onNode_congr (kindOfC_congr ((R.agree hS).mono hp)).symm fun κ _ => h κ L es L' es' h1 h2 hS

/-- A gated check whose every kind's check is log-only and monotone. -/
theorem rejLog4_onNode {P : NodeKind → Log → Log → Prop} (h : ∀ κ, RejLog4 (P κ))
    (hlen : ∀ κ L es, P κ L es → 1 ≤ es.length) : RejLog4 (OnNode P) where
  mono L es x hp := onNode_imp (kindOfC_append [x] (by obtain ⟨κ, -, h'⟩ := hp; exact hlen κ L es h'))
    (fun κ _ => (h κ).mono L es x) hp
  sq L es x hit := by
    by_cases h0 : es.length = 0
    · constructor
      · rintro ⟨κ, -, hp⟩
        have := (h κ).sq L es x hit
        have h1 := hlen κ L es (this.mp hp); omega
      · rintro ⟨κ, -, hp⟩; have := hlen κ L es hp; omega
    exact onNode_congr (kindOfC_append [x] (by omega)).symm fun κ _ => (h κ).sq L es x hit
  log L L' es := onNode_congr rfl fun κ _ => (h κ).log L L' es

/-! ## Lr -/

section Lr
variable (R : FSrc) (srcL : NodeKind → ESrc)

theorem lr_hs (κ : NodeKind) : 169 + 1 + (lrR κ + 1) / 2 ≤ 179 := by
  have := (dims_le' κ).1; omega

open Classical in
/-- **Lr1's charge** (A.10 Lr1): at the chain's node kind `κ`, from `RowsBadLr4` at Lr1's entry,
any phase doom whose escapes clear `ZCwLr4` costs `≤ lrR κ/2^128`. -/
theorem lr4_zc_count {D : Log → Log → Prop} {L es₀ : Log} {κ : NodeKind}
    (hk : kindOfC es₀ = .node κ) (hl : es₀.length = 170) (hd : RowsBadLr4 R srcL L es₀)
    (hesc : ∀ as : List Digest, as.length = 9 → EscAtG D L (ext es₀ as) →
      ¬ ZCwLr4 R srcL L (ext es₀ as)) :
    condCount D L es₀ 9 [] ≤ (lrR κ : ℝ≥0) / 2 ^ 128 := by
  refine zcG_count R (srcL κ) (lrR κ) (ncR κ) 169 hl (by norm_num)
    (by have := (dims_le' κ).1; omega) ((onNode_iff hk).1 hd) fun as has he hz => hesc as has he ?_
  obtain ⟨ys, hy⟩ := ext_eq_append es₀ as
  exact ⟨κ, by rw [hy, kindOfC_append ys (by omega), hk], hz⟩

theorem lr4_habs_outer {L es : Log} (x : ByteArray × Digest) (hl : es.length = 179)
    (hz : ZCwLr4 R srcL L es) : D3Lr4 R srcL L (es ++ [x]) :=
  onNode_imp (kindOfC_append [x] (by omega)) (fun κ _ h =>
    habsG_outer R (srcL κ) (lrR κ) (ncR κ) 169 179 (lr_hs κ) (by norm_num) x hl h) hz

open Classical in
theorem lr4_single_outer (L es : Log) :
    (univ.filter fun d => D3Lr4 R srcL L es ∧ ¬ D3Lr4 R srcL L (ext1 es d)).card ≤ 3 * 2 ^ 128 := by
  by_cases h1 : 1 ≤ es.length
  · exact onNode_card L es h1 fun κ _ =>
      singleG_outer R (srcL κ) (lrR κ) (ncR κ) 169 179 (lr_hs κ) (by norm_num) L es
  · rw [filter_false_of_mem fun d _ hd => by obtain ⟨κ, -, h, -⟩ := hd.1; omega]; simp

theorem lr4_outer_append {L es : Log} (x : ByteArray × Digest) (hlen : 179 < es.length)
    (hc : (es.length - 179) % 2 = 0 ∨ 17 ≤ (es.length - 179) / 2) :
    D3Lr4 R srcL L (es ++ [x]) ↔ D3Lr4 R srcL L es :=
  onNode_congr (kindOfC_append [x] (by omega)).symm fun κ _ =>
    outerG_append R (srcL κ) (lrR κ) (ncR κ) 169 179 (lr_hs κ) (by norm_num) x hlen
      (hc.imp_right fun h => le_trans (dims_le' κ).1 h)

/-- **At Lrend** (213): Lr2's doom gives `RejEndLr4` or a wrong triple. -/
theorem lr4_habs_end {L es : Log} (x : ByteArray × Digest) (hl : es.length = 213)
    (hd : D3Lr4 R srcL L es) : RejEndLr4 (L) (es ++ [x]) ∨ EndBadLr4 R srcL L (es ++ [x]) := by
  obtain ⟨κ, hk, h⟩ := hd
  have hk' : kindOfC (es ++ [x]) = .node κ := (kindOfC_append [x] (by omega)).trans hk
  rcases habsG_end R (srcL κ) (lrR κ) (ncR κ) 169 179 17 (lr_hs κ) (by norm_num)
    (dims_le' κ).1 x hl h with h | h
  · exact .inl ⟨κ, hk', h⟩
  · exact .inr ⟨κ, hk', h⟩

open Classical in
/-- **At Lr3** (214, `κ_L`): `≤ 2·2^128` answers clear a wrong triple. -/
theorem lr4_single_batch (L es : Log) (hl : es.length = 214) :
    (univ.filter fun d => EndBadLr4 R srcL L es ∧ ¬ BatBadLr4 R srcL L (ext1 es d)).card ≤
      2 * 2 ^ 128 :=
  onNode_card L es (by omega) fun κ _ =>
    singleG_batch R (srcL κ) (lrR κ) (ncR κ) 179 17 (by norm_num) (dims_le' κ).1 L es hl

end Lr

theorem rejEndLr4_log : RejLog4 RejEndLr4 :=
  rejLog4_onNode (fun κ => rejEndG_log (lr_hs κ) (dims_le' κ).1 p4b_abs.1)
    fun _ _ _ h => by have := h.1; omega

/-! ## The child claim on the log (RSV2 §2.6) -/

section Child
variable (srcE : NodeKind → ESrc)

theorem child_agree {es es' : Log} {p : ℕ} (h : Agree es es' p) (hp : 214 ≤ p) :
    pxL es = pxL es' ∧ pyL es = pyL es' ∧ sL es = sL es' ∧ xL es = xL es' := by
  have h2 : msgAt es 213 = msgAt es' 213 := msgAt_congr h (by omega)
  exact ⟨funext fun _ => by simp only [pxL, h2], funext fun _ => by simp only [pyL, h2],
    funext fun _ => by simp only [sL, h2], by simp only [xL, h2]⟩

theorem etaL_agree {es es' : Log} {p : ℕ} (h : Agree es es' p) (hp : 227 ≤ p) : etaL es = etaL es' := by
  simp only [etaL, coordAt, fAt, ansAt, h (214 + 1 + 23 / 2) (by omega)]

theorem dChild_agree {es es' : Log} {p : ℕ} (h : Agree es es' p) (hp : 214 ≤ p) :
    dChild srcE es = dChild srcE es' := by
  obtain ⟨h1, h2, h3, h4⟩ := child_agree h hp
  simp only [dChild, h1, h2, h3, h4]

theorem xHat_agree {κ : NodeKind} {es es' : Log} {p : ℕ} (h : Agree es es' p) (hp : 273 ≤ p) :
    xHat κ es = xHat κ es' := by
  simp only [xHat, rxs_agree (a := e2R κ) (b2 := 227) h (by have := (dims_le' κ).2.1; omega),
    (child_agree h (by omega)).1]

theorem truthChild_iff (es : Log) : truthChild4 srcE es ↔ dChild srcE es = 0 := by
  rw [truthChild4, dChild, sub_eq_zero, eq_comm]

/-- **The stacked extension in its row point** (`matMLE_hiRow` per kind and matrix). -/
theorem mle_mStack_row (s : ℕ → F) (p q : ℕ → F) {n : ℕ} (r : Fin n → F) :
    mle (fun x : Fin (2 ^ n) => mStack srcE s (Rsv.hiPt (cube x) p) q) r = mStack srcE s (Rsv.hiPt r p) q := by
  simp only [mStack, NodeKind.all, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero]
  simp only [Rsv.mle_add', mle_smul, Rsv.matMLE_hiRow]

/-- **… and in its column point.** -/
theorem mle_mStack_col (s : ℕ → F) (p q : ℕ → F) {n : ℕ} (r : Fin n → F) :
    mle (fun y : Fin (2 ^ n) => mStack srcE s p (Rsv.hiPt (cube y) q)) r = mStack srcE s p (Rsv.hiPt r q) := by
  simp only [mStack, NodeKind.all, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero]
  simp only [Rsv.mle_add', mle_smul, Rsv.matMLE_hiCol]

end Child

/-! ## E, the outer half -/

section EOuter
variable (R : FSrc) (srcE : NodeKind → ESrc)

theorem e_hs (κ : NodeKind) : 214 + 1 + (e2R κ + 1) / 2 ≤ 227 := by
  have := (dims_le' κ).2.1; omega

/-- E1's table at the entry: the residual on `e2R κ` coordinates, plus `D` times coordinate 23. -/
noncomputable def zcE4 (κ : NodeKind) (L es : Log) : Fin (2 ^ 24) → F :=
  Rsv.zcT (⟨23, by norm_num⟩ : Fin 24)
    (residual (entMat (srcE κ).ea (e2R κ) (ncR κ)) (entMat (srcE κ).eb (e2R κ) (ncR κ))
      (entMat (srcE κ).ec (e2R κ) (ncR κ)) (zCG R (ncR κ) L es)) (dChild srcE es)

open Classical in
/-- **E1's charge** (A.10 E1, RSV2 §2.6): from a false M row or a false child claim at the entry,
`≤ 24/2^128` (`ml_round_le` over E1's 24 coordinates `τ ‖ η`; for `N2`, coordinate 22 is unread:
the table is constant in it). -/
theorem e4_zc_count {D : Log → Log → Prop} {L es₀ : Log} {κ : NodeKind}
    (hk : kindOfC es₀ = .node κ) (hl : es₀.length = 215)
    (hd : nE4 R srcE L es₀ ∨ ChildBad4 srcE L es₀)
    (hesc : ∀ as : List Digest, as.length = 12 → EscAtG D L (ext es₀ as) →
      ¬ ZCwE4 R srcE L (ext es₀ as)) :
    condCount D L es₀ 12 [] ≤ (24 : ℝ≥0) / 2 ^ 128 := by
  have ha : e2R κ ≤ 23 := (dims_le' κ).2.1
  have ht : (Array.ofFn (zcE4 R srcE κ L es₀)).size = 2 ^ 24 := Array.size_ofFn
  refine ml_round_le hl (by norm_num) ht ?_ fun as has he => ?_
  · rw [tbl_ofFn]
    refine Rsv.zcT_ne _ ha ?_
    rcases hd with h | h
    · left
      have := zc_start ((onNode_iff hk).1 h)
      rwa [tbl_ofFn] at this
    · right
      obtain ⟨-, hc⟩ := (onNode_iff hk).1 h
      rwa [truthChild_iff] at hc
  · have hnf := hesc as has he
    obtain ⟨ys, hy⟩ := ext_eq_append es₀ as
    have hk' : kindOfC (ext es₀ as) = .node κ := by rw [hy, kindOfC_append ys (by omega), hk]
    have hag : Agree (ext es₀ as) es₀ 215 := by rw [hy]; exact hl ▸ agree_append es₀ ys le_rfl
    have hz : zCG R (ncR κ) L (ext es₀ as) = zCG R (ncR κ) L es₀ :=
      zCG_same R (ncR κ) (R.ofAgree L hag) (by omega)
    have hD : dChild srcE (ext es₀ as) = dChild srcE es₀ := dChild_agree srcE hag (by omega)
    have hlen : 24 ≤ (List.ofFn fun j : Fin (12 * 2) => coordAt (ext es₀ as) 214 j).length := by
      simp only [List.length_ofFn]; omega
    rw [mlDoom_full _ ht _ hlen, tbl_ofFn, zcE4, Rsv.mle_zcT]
    intro hm
    apply hnf
    refine ⟨κ, hk', ?_⟩
    dsimp only
    rw [hz, hD]
    rw [take_ofFn_coord (ext es₀ as) (show 24 ≤ 12 * 2 by norm_num)] at hm
    have h1 : Rsv.lowA (e2R κ) (Rsv.hiPt (ptOf 24 (tauS 24 214 (ext es₀ as))) 0) =
        ptOf (e2R κ) (tauS (e2R κ) 214 (ext es₀ as)) := by
      funext j
      have hj : (j : ℕ) < 24 := by omega
      simp [Rsv.lowA, Rsv.hiPt, hj, ptOf, tauS, List.getD_eq_getElem?_getD]
    have h2 : ptOf 24 (tauS 24 214 (ext es₀ as)) ⟨23, by norm_num⟩ = etaL (ext es₀ as) := by
      simp [ptOf, etaL, tauS, List.getD_eq_getElem?_getD]
    rw [h1, h2] at hm
    rw [mul_comm] at hm
    exact hm

theorem T3E4_same (κ : NodeKind) {L es L' es' : Log} {p : ℕ} (h : R.Sm L es L' es' p) (hp : 227 ≤ p) :
    T3E4 R srcE κ L es = T3E4 R srcE κ L' es' := by
  have hA := R.agree h
  obtain ⟨h1, h2, h3, h4⟩ := child_agree hA (by omega)
  simp only [T3E4, zCG_same R (ncR κ) h (by omega), tauS_agree (a := e2R κ) (s0 := 214) hA
    ((e_hs κ).trans hp), h1, h2, h3, h4, etaL_agree hA hp]

theorem T3E4_local (κ : NodeKind) : TruthLocal 227 (fun _ _ => 0) (T3E4 R srcE κ) := fun L _ _ h =>
  ⟨T3E4_same R srcE κ (R.ofAgree L h) le_rfl, rfl⟩

theorem T3E4_size (κ : NodeKind) (L es : Log) :
    ∀ t ∈ T3E4 R srcE κ L es, t.size = 2 ^ (fun _ : Kind => e2R κ) (kindOf es) := by
  simp [T3E4, eqTable_size, tauS]

theorem outerExprR_deg : outerExprR.deg = 3 := rfl
theorem innerExprR_deg : innerExprR.deg = 2 := rfl

theorem T3E4_get (κ : NodeKind) (L es : Log) :
    (T3E4 R srcE κ L es).getD 0 #[] = eqTable (tauS (e2R κ) 214 es) ∧
    (T3E4 R srcE κ L es).getD 1 #[] = Array.ofFn (matVec (entMat (srcE κ).ea (e2R κ) (ncR κ)) (zCG R (ncR κ) L es)) ∧
    (T3E4 R srcE κ L es).getD 2 #[] = Array.ofFn (matVec (entMat (srcE κ).eb (e2R κ) (ncR κ)) (zCG R (ncR κ) L es)) ∧
    (T3E4 R srcE κ L es).getD 3 #[] = Array.ofFn (matVec (entMat (srcE κ).ec (e2R κ) (ncR κ)) (zCG R (ncR κ) L es)) ∧
    (T3E4 R srcE κ L es).getD 4 #[] = Array.ofFn (fun x : Fin (2 ^ e2R κ) =>
      etaL es * eq (Rsv.lowA (e2R κ) (pxL es)) (cube x)) ∧
    (T3E4 R srcE κ L es).getD 5 #[] = Array.ofFn (fun x : Fin (2 ^ e2R κ) =>
      mStack srcE (sL es) (Rsv.hiPt (cube x) (pxL es)) (pyL es) - xL es) :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- The child table's extension at a point is `mStack` there minus `X`. -/
theorem mle_yTab (es : Log) {n : ℕ} (r : Fin n → F) :
    mle (fun x : Fin (2 ^ n) => mStack srcE (sL es) (Rsv.hiPt (cube x) (pxL es)) (pyL es) - xL es) r =
      mStack srcE (sL es) (Rsv.hiPt r (pxL es)) (pyL es) - xL es := by
  rw [Rsv.mle_sub', mle_mStack_row, Rsv.mle_const]

/-- **E2's true sum** is E1's polynomial at `(τ, η)`: `F̃(τ) + η·D`. -/
theorem trueSum_T3E4 (κ : NodeKind) (L es : Log) :
    trueSum outerExprR (T3E4 R srcE κ L es) (e2R κ) =
      mle (residual (entMat (srcE κ).ea (e2R κ) (ncR κ)) (entMat (srcE κ).eb (e2R κ) (ncR κ))
        (entMat (srcE κ).ec (e2R κ) (ncR κ)) (zCG R (ncR κ) L es)) (ptOf (e2R κ) (tauS (e2R κ) 214 es)) +
      etaL es * dChild srcE es := by
  obtain ⟨g0, g1, g2, g3, g4, g5⟩ := T3E4_get R srcE κ L es
  set A := entMat (srcE κ).ea (e2R κ) (ncR κ)
  set B := entMat (srcE κ).eb (e2R κ) (ncR κ)
  set C := entMat (srcE κ).ec (e2R κ) (ncR κ)
  set z := zCG R (ncR κ) L es
  set τ := tauS (e2R κ) 214 es
  have o0 : (outerTables τ A B C z).getD 0 #[] = eqTable τ := rfl
  have o1 : (outerTables τ A B C z).getD 1 #[] = Array.ofFn (matVec A z) := rfl
  have o2 : (outerTables τ A B C z).getD 2 #[] = Array.ofFn (matVec B z) := rfl
  have o3 : (outerTables τ A B C z).getD 3 #[] = Array.ofFn (matVec C z) := rfl
  have h0 := outer_trueSum τ (by simp [τ, tauS]) A B C z
  unfold trueSum at h0 ⊢
  simp only [outerExpr, outerExprR, Expr.eval] at h0 ⊢
  rewrite [o0, o1, o2, o3] at h0
  rewrite [g0, g1, g2, g3, g4, g5, sum_add_distrib, h0, tbl_ofFn, tbl_ofFn]
  have hm := mle_yTab srcE es (Rsv.lowA (e2R κ) (pxL es))
  rw [Rsv.hiPt_self] at hm
  have hY : ∑ u : Fin (2 ^ e2R κ), etaL es * eq (Rsv.lowA (e2R κ) (pxL es)) (cube u) *
      (mStack srcE (sL es) (Rsv.hiPt (cube u) (pxL es)) (pyL es) - xL es) = etaL es * dChild srcE es := by
    rw [show dChild srcE es = mStack srcE (sL es) (pxL es) (pyL es) - xL es from rfl, ← hm, mle, mul_sum]
    exact sum_congr rfl fun u _ => by ring
  rewrite [hY]
  rfl

/-- **Into E2's rounds** (`habs` at 227): E1's doom is a false outer claim `0`. -/
theorem e4_habs_outer {L es : Log} (x : ByteArray × Digest) (hl : es.length = 227)
    (hz : ZCwE4 R srcE L es) : D3E4 R srcE L (es ++ [x]) := by
  refine onNode_imp (kindOfC_append [x] (by omega)) (fun κ _ h => ?_) hz
  refine ⟨by simp; omega, ?_⟩
  have ha0 : ans3 227 (fun _ => e2R κ) (es ++ [x]) = 0 := by
    simp only [ans3, List.length_append, List.length_singleton, hl]
    rw [show 227 + 1 - 227 = 1 by omega]; simp
  rw [ha0]
  simp only [Wrong3, clR, rchs, List.range_zero, List.map_nil, bindAll, Nat.sub_zero]
  rw [T3E4_same R srcE κ (R.ofAgree L (agree_append es [x] le_rfl)) (by omega), trueSum_T3E4]
  exact fun h0 => h h0.symm

open Classical in
theorem e4_single_outer (L es : Log) :
    (univ.filter fun d => D3E4 R srcE L es ∧ ¬ D3E4 R srcE L (ext1 es d)).card ≤ 3 * 2 ^ 128 := by
  by_cases h1 : 1 ≤ es.length
  · exact onNode_card L es h1 fun κ _ =>
      D3_single (by omega) (T3E4_local R srcE κ) outerExprR_deg (T3E4_size R srcE κ) L es
  · rw [filter_false_of_mem fun d _ hd => by obtain ⟨κ, -, h, -⟩ := hd.1; omega]; simp

theorem e4_outer_append {L es : Log} (x : ByteArray × Digest) (hlen : 227 < es.length)
    (hc : (es.length - 227) % 2 = 0 ∨ 23 ≤ (es.length - 227) / 2) :
    D3E4 R srcE L (es ++ [x]) ↔ D3E4 R srcE L es :=
  onNode_congr (kindOfC_append [x] (by omega)).symm fun κ _ =>
    D3_append_iff (by omega) (T3E4_local R srcE κ) x hlen
      (hc.imp_right fun h => le_trans (dims_le' κ).2.1 h)

/-- E2's final true value: the outer part at `r_E2`, plus `η·eq(p_x, r_E2)·(m̂*_true − X)`. -/
theorem final_T3E4 (κ : NodeKind) (L es : Log) :
    trueSum outerExprR (bindAll (T3E4 R srcE κ L es) (rchs 227 es (e2R κ))) 0 =
      eq (ptOf (e2R κ) (tauS (e2R κ) 214 es)) (ptOf (e2R κ) (rxs (e2R κ) 227 es)) *
        ((triTG R (srcE κ) (e2R κ) (ncR κ) 227 L es).1 * (triTG R (srcE κ) (e2R κ) (ncR κ) 227 L es).2.1 +
          (triTG R (srcE κ) (e2R κ) (ncR κ) 227 L es).2.2) +
      etaL es * eq (Rsv.lowA (e2R κ) (pxL es)) (ptOf (e2R κ) (rxs (e2R κ) 227 es)) *
        (mHatT srcE κ es - xL es) := by
  obtain ⟨g0, g1, g2, g3, g4, g5⟩ := T3E4_get R srcE κ L es
  rw [trueSum_bindAll' _ _ _ (by simp [rchs]) (fun t ht => T3E4_size R srcE κ L es t ht)]
  simp only [outerExprR, Expr.eval]
  rw [g0, g1, g2, g3, g4, g5, tbl_ofFn, tbl_ofFn, tbl_ofFn, tbl_ofFn, tbl_ofFn,
    tbl_eqTable' _ (by simp [tauS]), mle_smul, mle_eqPt, mle_eqPt, mle_yTab]
  simp only [triTG, mHatT, xHat, rxs]

/-- **At Eend** (273): a doomed outer claim gives the end check's failure or a wrong quadruple. -/
theorem e4_habs_end {L es : Log} (x : ByteArray × Digest) (hl : es.length = 273)
    (hd : D3E4 R srcE L es) : RejEndE4 L (es ++ [x]) ∨ EndBadE4 R srcE L (es ++ [x]) := by
  obtain ⟨κ, hk, -, hw⟩ := hd
  have hk' : kindOfC (es ++ [x]) = .node κ := (kindOfC_append [x] (by omega)).trans hk
  have hdm := dims_le' κ
  have ha : ans3 227 (fun _ => e2R κ) es = e2R κ := by simp only [ans3, hl]; omega
  rw [ha] at hw
  unfold Wrong3 at hw
  rw [Nat.sub_self, final_T3E4] at hw
  have hag := agree_append es [x] (le_of_eq hl.symm)
  have hc : clR 227 (fun _ _ => 0) L (es ++ [x]) (e2R κ) = clR 227 (fun _ _ => 0) L es (e2R κ) :=
    clR_congr (b := 227) (c0 := fun _ _ => (0 : F)) (L := L) (es := es ++ [x]) (es' := es) rfl
      (l := e2R κ) (hag.mono (by omega))
  have hτ := tauS_agree (a := e2R κ) (s0 := 214) hag (by omega)
  have hr := rxs_agree (a := e2R κ) (b2 := 227) hag (by omega)
  have heta := etaL_agree hag (by omega)
  obtain ⟨hpx, -, -, hX⟩ := child_agree hag (by omega)
  by_cases hrej : RejEndE4 L (es ++ [x])
  · exact .inl hrej
  right
  refine ⟨κ, hk', by simp; omega, ?_⟩
  have hchk : clR 227 (fun _ _ => 0) L (es ++ [x]) (e2R κ) =
      eq (ptOf (e2R κ) (tauS (e2R κ) 214 (es ++ [x]))) (ptOf (e2R κ) (rxs (e2R κ) 227 (es ++ [x]))) *
        (vEnd 23 227 (es ++ [x]) 0 * vEnd 23 227 (es ++ [x]) 1 + vEnd 23 227 (es ++ [x]) 2) +
      etaL (es ++ [x]) * eq (Rsv.lowA (e2R κ) (pxL (es ++ [x]))) (ptOf (e2R κ) (rxs (e2R κ) 227 (es ++ [x]))) *
        (mStL (es ++ [x]) - xL (es ++ [x])) := by
    by_contra hne; exact hrej ⟨κ, hk', by simp; omega, hne⟩
  rw [triTG_same R (srcE κ) (e2R κ) (ncR κ) 227 (R.ofAgree L hag) (by omega) (by omega),
    show mHatT srcE κ (es ++ [x]) = mHatT srcE κ es by
      simp only [mHatT, xHat_agree hag (by omega), (child_agree hag (by omega)).2.1,
        (child_agree hag (by omega)).2.2.1]]
  rw [hc, hτ, hr, heta, hpx, hX] at hchk
  by_contra hne
  simp only [not_or, not_not] at hne
  obtain ⟨h1, h2⟩ := hne
  apply hw
  rw [hchk, ← h2, ← h1]

/-- E1's doom reads the log before 227 (and `f⁽⁰⁾`). -/
theorem zcwE4_reads (κ : NodeKind) : ReadsS R 227 fun L es =>
    mle (residual (entMat (srcE κ).ea (e2R κ) (ncR κ)) (entMat (srcE κ).eb (e2R κ) (ncR κ))
        (entMat (srcE κ).ec (e2R κ) (ncR κ)) (zCG R (ncR κ) L es)) (ptOf (e2R κ) (tauS (e2R κ) 214 es)) +
      etaL es * dChild srcE es ≠ 0 := fun L es L' es' _ _ h => by
  dsimp only
  rw [zCG_same R (ncR κ) h (by norm_num), tauS_agree (R.agree h) (e_hs κ), etaL_agree (R.agree h) le_rfl,
    dChild_agree srcE (R.agree h) (by norm_num)]

/-- A wrong quadruple reads the log before 274. -/
theorem endBadE4_reads (κ : NodeKind) : ReadsS R 274 fun L es =>
    273 < es.length ∧ ((vEnd 23 227 es 0, vEnd 23 227 es 1, vEnd 23 227 es 2) ≠
      triTG R (srcE κ) (e2R κ) (ncR κ) 227 L es ∨ mStL es ≠ mHatT srcE κ es) := fun L es L' es' h1 h2 h => by
  have hA := R.agree h
  have hdm := dims_le' κ
  dsimp only
  rw [triTG_same R (srcE κ) (e2R κ) (ncR κ) 227 h (by norm_num) (by omega),
    vEnd_agree (a := 23) (b2 := 227) hA le_rfl 0, vEnd_agree (a := 23) (b2 := 227) hA le_rfl 1,
    vEnd_agree (a := 23) (b2 := 227) hA le_rfl 2,
    show mStL es = mStL es' by simp only [mStL, msgAt_congr hA (show 273 < 274 by norm_num)],
    show mHatT srcE κ es = mHatT srcE κ es' by
      simp only [mHatT, xHat_agree hA (by norm_num), (child_agree hA (by norm_num)).2.1,
        (child_agree hA (by norm_num)).2.2.1]]
  exact and_congr_left fun _ => ⟨fun _ => by omega, fun _ => by omega⟩

/-- E2's doom reads the same off two logs whose words agree. -/
theorem D3E4_same (κ : NodeKind) {L L' X : Log} {p : ℕ} (h : R.Sm L X L' X p) (hp : 227 ≤ p) :
    D3 227 (fun _ _ => 0) (fun _ => e2R κ) outerExprR (T3E4 R srcE κ) L X ↔
      D3 227 (fun _ _ => 0) (fun _ => e2R κ) outerExprR (T3E4 R srcE κ) L' X :=
  (D3_log_congr (b := 227) (c0 := fun _ _ => (0 : F)) (nr := fun _ => e2R κ) (e := outerExprR)
    (T3E4_same R srcE κ h hp).symm rfl).symm

end EOuter

theorem rejEndE4_agree {κ : NodeKind} {L es L' es' : Log} (h : Agree es es' 274) (hl : 274 ≤ es.length)
    (hl' : 274 ≤ es'.length) :
    (273 < es.length ∧ clR 227 (fun _ _ => 0) L es (e2R κ) ≠
      eq (ptOf (e2R κ) (tauS (e2R κ) 214 es)) (ptOf (e2R κ) (rxs (e2R κ) 227 es)) *
        (vEnd 23 227 es 0 * vEnd 23 227 es 1 + vEnd 23 227 es 2) +
      etaL es * eq (Rsv.lowA (e2R κ) (pxL es)) (ptOf (e2R κ) (rxs (e2R κ) 227 es)) * (mStL es - xL es)) ↔
    (273 < es'.length ∧ clR 227 (fun _ _ => 0) L' es' (e2R κ) ≠
      eq (ptOf (e2R κ) (tauS (e2R κ) 214 es')) (ptOf (e2R κ) (rxs (e2R κ) 227 es')) *
        (vEnd 23 227 es' 0 * vEnd 23 227 es' 1 + vEnd 23 227 es' 2) +
      etaL es' * eq (Rsv.lowA (e2R κ) (pxL es')) (ptOf (e2R κ) (rxs (e2R κ) 227 es')) *
        (mStL es' - xL es')) := by
  have hdm := dims_le' κ
  have hc : clR 227 (fun _ _ => (0 : F)) L es (e2R κ) = clR 227 (fun _ _ => 0) L' es' (e2R κ) :=
    (clR_log_congr (b := 227) (c0 := fun _ _ => (0 : F)) (L := L') (L' := L) rfl (e2R κ)).trans
      (clR_congr (b := 227) (c0 := fun _ _ => (0 : F)) (L := L') (es := es) (es' := es') rfl
        (l := e2R κ) (h.mono (by omega)))
  obtain ⟨hpx, -, -, hX⟩ := child_agree h (by omega)
  rw [hc, tauS_agree (a := e2R κ) (s0 := 214) h (by omega), rxs_agree (a := e2R κ) (b2 := 227) h (by omega),
    vEnd_agree (a := 23) (b2 := 227) h le_rfl 0, vEnd_agree (a := 23) (b2 := 227) h le_rfl 1,
    vEnd_agree (a := 23) (b2 := 227) h le_rfl 2, etaL_agree h (by omega), hpx, hX,
    show mStL es = mStL es' by simp only [mStL, msgAt_congr h (show 273 < 274 by norm_num)]]
  exact and_congr_left fun _ => ⟨fun _ => by omega, fun _ => by omega⟩

theorem rejEndE4_log : RejLog4 RejEndE4 :=
  rejLog4_onNode (fun κ => rejLog4_of (q := 274) (by norm_num) (fun _ _ h => by have := h.1; omega)
    (fun L es L' es' h1 h2 h => rejEndE4_agree h h1 h2) (by simpa using p4b_abs.2.1))
    fun _ _ _ h => by have := h.1; omega

/-! ## E4, batched with Lr and the child claim -/

section Inner
variable (R : FSrc) (srcE srcL : NodeKind → ESrc) (κ : NodeKind)

theorem wEb4_agree {es es' : Log} (h : Agree es es' 275) : wEb4 srcE srcL κ es = wEb4 srcE srcL κ es' := by
  have hd := dims_le' κ
  funext y
  simp only [wEb4, rxs_agree (a := e2R κ) (b2 := 227) h (by omega),
    rxs_agree (a := lrR κ) (b2 := 179) h (by omega), kapB_agree (a := 23) (b2 := 227) h le_rfl,
    kapB_agree (a := 17) (b2 := 179) h (by norm_num)]

theorem cTab4_agree {es es' : Log} {p : ℕ} (h : Agree es es' p) (hp : 273 ≤ p) :
    cTab4 srcE κ es = cTab4 srcE κ es' := by
  obtain ⟨-, h2, h3, -⟩ := child_agree h (by omega)
  funext y; simp only [cTab4, xHat_agree h hp, h2, h3]

theorem c4E4_agree {L L' es es' : Log} {p : ℕ} (h : Agree es es' p) (hp : 275 ≤ p) :
    c4E4 L es = c4E4 L' es' := by
  simp only [c4E4, c4_agree (a := 23) (b2 := 227) (L := L) (L' := L') h hp,
    c4_agree (a := 17) (b2 := 179) (L := L) (L' := L') h (by omega),
    kapB_agree (a := 23) (b2 := 227) h (by omega), mStL, msgAt_congr h (show 273 < p by omega)]

theorem TEb4_same {L es L' es' : Log} {p : ℕ} (h : R.Sm L es L' es' p) (hp : 275 ≤ p) :
    TEb4 R srcE srcL κ L es = TEb4 R srcE srcL κ L' es' := by
  have hA := R.agree h
  simp only [TEb4, zCG_same R _ h (by omega), wEb4_agree srcE srcL κ (hA.mono hp),
    cTab4_agree srcE κ hA (by omega), kapB_agree (a := 23) (b2 := 227) hA (by omega),
    (child_agree hA (by omega)).2.1]

theorem TEb4_local : TruthLocal2 275 c4E4 (TEb4 R srcE srcL κ) := fun L _ _ h =>
  ⟨TEb4_same R srcE srcL κ (R.ofAgree L h) le_rfl, c4E4_agree h le_rfl⟩

theorem TEb4_size (L es : Log) :
    ∀ t ∈ TEb4 R srcE srcL κ L es, t.size = 2 ^ (fun _ : Kind => ncR κ) (kindOf es) := by
  simp [TEb4]

/-- **The child table's sum** is `m̂*`'s true value: `Σ_y κ_E⁴ eq(p_y, y)·C(y) = κ_E⁴·M̃*(x̂, p_y)`. -/
theorem sum_cTab4 (es : Log) :
    ∑ y : Fin (2 ^ ncR κ), kapB 23 227 es ^ 4 * eq (Rsv.lowA (ncR κ) (pyL es)) (cube y) * cTab4 srcE κ es y =
      kapB 23 227 es ^ 4 * mHatT srcE κ es := by
  have hm := mle_mStack_col srcE (sL es) (xHat κ es) (pyL es) (Rsv.lowA (ncR κ) (pyL es))
  rw [Rsv.hiPt_self] at hm
  rw [mHatT, ← hm, mle, mul_sum]
  exact sum_congr rfl fun y _ => by simp only [cTab4]; ring

theorem TEb4_get (L es : Log) :
    (TEb4 R srcE srcL κ L es).getD 0 #[] = Array.ofFn (wEb4 srcE srcL κ es) ∧
    (TEb4 R srcE srcL κ L es).getD 1 #[] = Array.ofFn (zCG R (ncR κ) L es) ∧
    (TEb4 R srcE srcL κ L es).getD 2 #[] = Array.ofFn (fun y : Fin (2 ^ ncR κ) =>
      kapB 23 227 es ^ 4 * eq (Rsv.lowA (ncR κ) (pyL es)) (cube y)) ∧
    (TEb4 R srcE srcL κ L es).getD 3 #[] = Array.ofFn (cTab4 srcE κ es) :=
  ⟨rfl, rfl, rfl, rfl⟩

/-- **The batched true value** (`inner_trueSum` twice, and the child table). -/
theorem trueSum_TEb4 (L es : Log) :
    trueSum innerExprR (TEb4 R srcE srcL κ L es) (ncR κ) =
      trueSum innerExpr (T4G R (srcE κ) (e2R κ) (ncR κ) 227 23 L es) (ncR κ) +
        kapB 23 227 es ^ 3 *
          trueSum innerExpr (T4G R (srcL κ) (lrR κ) (ncR κ) 179 17 L es) (ncR κ) +
        kapB 23 227 es ^ 4 * mHatT srcE κ es := by
  obtain ⟨g0, g1, g2, g3⟩ := TEb4_get R srcE srcL κ L es
  rw [← sum_cTab4]
  simp only [T4G, innerTables, prod_trueSum]
  unfold trueSum
  simp only [innerExprR, Expr.eval]
  rw [g0, g1, g2, g3, tbl_ofFn, tbl_ofFn, tbl_ofFn, tbl_ofFn, mul_sum, ← sum_add_distrib,
    ← sum_add_distrib]
  exact sum_congr rfl fun _ _ => by simp only [wEb4, wInn]; ring

end Inner

section InnerG
variable (R : FSrc) (srcE srcL : NodeKind → ESrc)

/-- **Five claims batched by one challenge** (`batch_count` at degree 4). -/
theorem batch_count5 (P : Digest → Prop) [DecidablePred P] {v0 v1 v2 v3 v4 t0 t1 t2 t3 t4 : F}
    (hvt : v0 ≠ t0 ∨ v1 ≠ t1 ∨ v2 ≠ t2 ∨ v3 ≠ t3 ∨ v4 ≠ t4)
    (h : ∀ a, P a → v0 + chF a 0 * v1 + chF a 0 ^ 2 * v2 + chF a 0 ^ 3 * v3 + chF a 0 ^ 4 * v4 =
      t0 + chF a 0 * t1 + chF a 0 ^ 2 * t2 + chF a 0 ^ 3 * t3 + chF a 0 ^ 4 * t4) :
    (univ.filter P).card ≤ 4 * 2 ^ 128 := by
  refine batch_count (k := 4) P ![v0, v1, v2, v3, v4] ![t0, t1, t2, t3, t4] ?_ fun a ha => ?_
  · intro he
    rcases hvt with h0 | h0 | h0 | h0 | h0
    · exact h0 (by simpa using congrFun he 0)
    · exact h0 (by simpa using congrFun he 1)
    · exact h0 (by simpa using congrFun he 2)
    · exact h0 (by simpa using congrFun he 3)
    · exact h0 (by simpa using congrFun he 4)
  · have := h a ha
    simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.val_zero, Fin.val_succ,
      Matrix.cons_val_zero, Matrix.cons_val_succ, pow_zero, one_mul, add_zero]
    linear_combination this

open Classical in
/-- **E3's count at a kind** (`hsingle` at 274): from a wrong M triple, a wrong `m̂*` or a false Lr
claim, at most `4·2^128` answers `κ_E` make E4's batched claim true (five claims, degree 4). -/
theorem single_batchE_at (κ : NodeKind) (L es : Log) (hl : es.length = 274) :
    (univ.filter fun d => ((273 < es.length ∧ ((vEnd 23 227 es 0, vEnd 23 227 es 1, vEnd 23 227 es 2) ≠
        triTG R (srcE κ) (e2R κ) (ncR κ) 227 L es ∨ mStL es ≠ mHatT srcE κ es)) ∨
        BatBadG R (srcL κ) (lrR κ) (ncR κ) 179 17 L es) ∧
      ¬ (274 < (ext1 es d).length ∧
        c4E4 L (ext1 es d) ≠ trueSum innerExprR (TEb4 R srcE srcL κ L (ext1 es d)) (ncR κ))).card ≤
      4 * 2 ^ 128 := by
  have hd := dims_le' κ
  by_cases hD : (273 < es.length ∧ ((vEnd 23 227 es 0, vEnd 23 227 es 1, vEnd 23 227 es 2) ≠
        triTG R (srcE κ) (e2R κ) (ncR κ) 227 L es ∨ mStL es ≠ mHatT srcE κ es)) ∨
      BatBadG R (srcL κ) (lrR κ) (ncR κ) 179 17 L es
  swap
  · rw [filter_false_of_mem fun d _ h => hD h.1, card_empty]; exact Nat.zero_le _
  refine batch_count5 _ (v0 := vEnd 23 227 es 0) (v1 := vEnd 23 227 es 1)
    (v2 := vEnd 23 227 es 2) (v3 := c4 17 179 L es) (v4 := mStL es)
    (t0 := (triTG R (srcE κ) (e2R κ) (ncR κ) 227 L es).1)
    (t1 := (triTG R (srcE κ) (e2R κ) (ncR κ) 227 L es).2.1)
    (t2 := (triTG R (srcE κ) (e2R κ) (ncR κ) 227 L es).2.2)
    (t3 := trueSum innerExpr (T4G R (srcL κ) (lrR κ) (ncR κ) 179 17 L es) (ncR κ))
    (t4 := mHatT srcE κ es) ?_ fun d hd' => ?_
  · by_contra hc
    simp only [not_or, not_not] at hc
    rcases hD with ⟨-, h | h⟩ | h
    · exact h (Prod.ext hc.1 (Prod.ext hc.2.1 hc.2.2.1))
    · exact h hc.2.2.2.2
    · exact h.2 hc.2.2.2.1
  have hag : Agree (ext1 es d) es 274 := hl ▸ agree_append es _ le_rfl
  have hκ : kapB 23 227 (ext1 es d) = chF d 0 := by
    simp only [kapB, fAt, ansAt, show 227 + 2 * 23 + 1 = es.length by omega]
    exact congrArg (chF · 0) (entAt_ext1 es d)
  have heq : c4E4 L (ext1 es d) = trueSum innerExprR (TEb4 R srcE srcL κ L (ext1 es d)) (ncR κ) := by
    by_contra hne
    exact hd'.2 ⟨by simp [ext1]; omega, hne⟩
  rw [trueSum_TEb4] at heq
  have hS := R.ofAgree L hag
  have hT4 : T4G R (srcE κ) (e2R κ) (ncR κ) 227 23 L (ext1 es d) =
      innerTables (ptOf (e2R κ) (rxs (e2R κ) 227 es)) (chF d 0) (entMat (srcE κ).ea (e2R κ) (ncR κ))
        (entMat (srcE κ).eb (e2R κ) (ncR κ)) (entMat (srcE κ).ec (e2R κ) (ncR κ))
        (zCG R (ncR κ) L es) := by
    simp only [T4G, hκ, rxs_agree (a := e2R κ) (b2 := 227) hag (by omega),
      zCG_same R (ncR κ) hS (by norm_num)]
  have hT4L : T4G R (srcL κ) (lrR κ) (ncR κ) 179 17 L (ext1 es d) =
      T4G R (srcL κ) (lrR κ) (ncR κ) 179 17 L es :=
    T4G_same R (srcL κ) (lrR κ) (ncR κ) 179 17 hS (by norm_num) hd.1 (by norm_num)
  have hcL : c4 17 179 L (ext1 es d) = c4 17 179 L es :=
    c4_agree (a := 17) (b2 := 179) hag (by norm_num)
  have hcM : c4 23 227 L (ext1 es d) = vEnd 23 227 es 0 + chF d 0 * vEnd 23 227 es 1 +
      chF d 0 ^ 2 * vEnd 23 227 es 2 := by
    simp only [c4, hκ, vEnd_agree (a := 23) (b2 := 227) hag (by norm_num)]
  have hmS : mStL (ext1 es d) = mStL es := by simp only [mStL, msgAt_congr hag (show 273 < 274 by norm_num)]
  have hmT : mHatT srcE κ (ext1 es d) = mHatT srcE κ es := by
    simp only [mHatT, xHat_agree hag (by norm_num), (child_agree hag (by norm_num)).2.1,
      (child_agree hag (by norm_num)).2.2.1]
  rw [hT4, hT4L, inner_trueSum, hκ, c4E4, hcL, hκ, hcM, hmS, hmT] at heq
  simp only [triTG]
  exact heq

open Classical in
/-- **E3's count** (`hsingle` at 274, A.10 E3, RSV2 §2.6: `≤ 4·2^128`, within RSV2's `8/2^128` row),
through the gate. -/
theorem e4_single_batchE (L es : Log) (hl : es.length = 274) :
    (univ.filter fun d => (EndBadE4 R srcE L es ∨ BatBadLr4 R srcL L es) ∧
      ¬ BatBadE4 R srcE srcL L (ext1 es d)).card ≤ 4 * 2 ^ 128 := by
  have h := onNode_card (N := 4 * 2 ^ 128)
    (P := fun κ L es => (273 < es.length ∧ ((vEnd 23 227 es 0, vEnd 23 227 es 1, vEnd 23 227 es 2) ≠
        triTG R (srcE κ) (e2R κ) (ncR κ) 227 L es ∨ mStL es ≠ mHatT srcE κ es)) ∨
      BatBadG R (srcL κ) (lrR κ) (ncR κ) 179 17 L es)
    (Q := fun κ L es => 274 < es.length ∧
      c4E4 L es ≠ trueSum innerExprR (TEb4 R srcE srcL κ L es) (ncR κ))
    L es (by omega) fun κ _ =>
      le_trans (card_filter_imp fun d hd => hd) (single_batchE_at R srcE srcL κ L es hl)
  refine le_trans (card_filter_imp fun d hd => ⟨onNode_or.1 hd.1, hd.2⟩) h

/-- **Into E4** (`habs` at 275): a false batched claim is E4's doom. -/
theorem e4_habs_innerE {L es : Log} (x : ByteArray × Digest) (hl : es.length = 275)
    (hb : BatBadE4 R srcE srcL L es) : D4E4 R srcE srcL L (es ++ [x]) := by
  refine onNode_imp (kindOfC_append [x] (by omega)) (fun κ _ hb => ?_) hb
  have hS := R.ofAgree L (agree_append es [x] (le_of_eq hl.symm))
  refine ⟨by simp; omega, ?_⟩
  have ha0 : ans3 275 (fun _ => ncR κ) (es ++ [x]) = 0 := by
    simp only [ans3, List.length_append, List.length_singleton, hl]; simp
  rw [ha0]
  simp only [Wrong2, clR2, rchs2, List.range_zero, List.map_nil, bindAll, Nat.sub_zero]
  rw [TEb4_same R srcE srcL κ hS le_rfl, c4E4_agree (L := L) (L' := L) (R.agree hS) le_rfl]
  exact hb.2

theorem chk_of_not_rejInE4 {L es : Log} {κ : NodeKind} (hk : kindOfC es = .node κ)
    (hr : ¬ RejInE4 L es) (j : ℕ) (hj : es.length = 275 + 2 * j + 1) (hjn : j < ncR κ) :
    Chk2 275 16 readF (fun d => chF d 0) c4E4 L es j := by
  by_contra hc; exact hr ⟨κ, hk, j, hjn, by omega, hc⟩

open Classical in
/-- **An E4 round's squeeze** (`D2_single`, `2·2^128`), from `¬ RejInE4`. -/
theorem e4_single_innerE (L es : Log) (hr : ¬ RejInE4 L es) :
    (univ.filter fun d => D4E4 R srcE srcL L es ∧ ¬ D4E4 R srcE srcL L (ext1 es d)).card ≤
      2 * 2 ^ 128 := by
  by_cases h1 : 1 ≤ es.length
  · exact onNode_card L es h1 fun κ hk =>
      D2_single (by omega) (TEb4_local R srcE srcL κ) innerExprR_deg card_chF_fiber
        (TEb4_size R srcE srcL κ) L es fun j hj hjn => chk_of_not_rejInE4 hk hr j hj hjn
  · rw [filter_false_of_mem fun d _ hd => by obtain ⟨κ, -, h, -⟩ := hd.1; omega]; simp

/-- An E4 round's absorb (or a dummy slot's items) keeps E4's doom. -/
theorem e4_inner_appendE {L es : Log} (x : ByteArray × Digest) (hlen : 275 < es.length)
    (hc : (es.length - 275) % 2 = 0 ∨ 25 ≤ (es.length - 275) / 2) :
    D4E4 R srcE srcL L (es ++ [x]) ↔ D4E4 R srcE srcL L es :=
  onNode_congr (kindOfC_append [x] (by omega)).symm fun κ _ =>
    D2_append_iff (by omega) (TEb4_local R srcE srcL κ) x hlen
      (hc.imp_right fun h => le_trans (dims_le' κ).2.2.1 h)

/-- **Once every E4 round is answered, E4's doom reads before 326.** -/
theorem D4E4_reads : ReadsS R 326 (D4E4 R srcE srcL) := by
  refine readsS_onNode (by norm_num) fun κ L es L' es' h1 h2 h => ?_
  have hd := dims_le' κ
  have hans : ∀ Y : Log, 325 ≤ Y.length → ans3 275 (fun _ => ncR κ) Y = ncR κ := fun Y hY => by
    unfold ans3; simp; omega
  unfold D2Eb4 D2 Wrong2
  rw [hans es (by omega), hans es' (by omega), TEb4_same R srcE srcL κ h (by omega),
    clR2_same (L' := L') (es' := es') (c4E4_agree (R.agree h) (by omega))
      ((R.agree h).mono (by omega)),
    rchs2_congr ((R.agree h).mono (by omega))]
  exact and_congr_left fun _ => ⟨fun _ => by omega, fun _ => by omega⟩

end InnerG

theorem chkE4_agree {L L' es es' : Log} {p : ℕ} (h : Agree es es' p) {j : ℕ} (hj : 275 + 2 * j < p) :
    Chk2 275 16 readF (fun d => chF d 0) c4E4 L es j ↔
      Chk2 275 16 readF (fun d => chF d 0) c4E4 L' es' j := by
  have hg : g2At 275 16 readF es j = g2At 275 16 readF es' j := by
    simp only [g2At, msgAt, h (275 + 2 * j) hj]
  have hc := clR2_same (b := 275) (wd := 16) (rd := readF) (ch := fun d => chF d 0)
    (c4E4_agree (L := L) (L' := L') (h.mono (by omega)) (le_refl 275)) (l := j) (h.mono (by omega))
  simp only [Chk2, hg, hc]

/-- **E4's round checks are a revision 4.1 check** (their messages are absorbs). -/
theorem rejInE4_log : RejLog4 RejInE4 := by
  refine rejLog4_onNode (fun κ => ?_) fun _ _ _ ⟨_, _, h, _⟩ => by omega
  have hd := dims_le' κ
  exact {
    mono := fun L es x ⟨j, hj, hlt, hc⟩ =>
      ⟨j, hj, by simp; omega, fun h' =>
        hc ((chkE4_agree (agree_append es [x] le_rfl) (by omega)).mp h')⟩
    sq := fun L es x hit => by
      refine ⟨fun ⟨j, hj, hlt, hc⟩ => ?_, fun ⟨j, hj, hlt, hc⟩ =>
        ⟨j, hj, by simp; omega, fun h' =>
          hc ((chkE4_agree (agree_append es [x] le_rfl) (by omega)).mp h')⟩⟩
      simp only [List.length_append, List.length_singleton] at hlt
      by_cases he : 275 + 2 * j = es.length
      · exact absurd (he ▸ hit) (p4b_abs.2.2.2.2 j (by omega))
      exact ⟨j, hj, by omega, fun h' =>
        hc ((chkE4_agree (agree_append es [x] le_rfl) (by omega)).mpr h')⟩
    log := fun L L' es => exists_congr fun j => and_congr_right fun _ => and_congr_right fun hj =>
      not_congr (chkE4_agree (fun _ _ => rfl) hj) }

/-! ## E4's weight at `r′` is the verifier's `evalM`/`evalL` values -/

theorem mle_add_mul {ℓ : ℕ} (f g : Fin (2 ^ ℓ) → F) (c : F) (r : Fin ℓ → F) :
    mle (fun y => f y + c * g y) r = mle f r + c * mle g r := by
  simp only [mle, mul_add, sum_add_distrib, mul_sum]
  congr 1; exact sum_congr rfl fun _ _ => by ring

/-- **E4's weight at a point** (`finE` (iv)'s `W(r′)`): the M rows' three matrix MLEs (`evalM`,
`Eval.matMLE` of the entries) at `(r_x, r′)` batched by `κ_E`, plus `κ_E³` times the L rows'
(`evalL`) at `(r_Lr, r′)` batched by `κ_L`. -/
theorem mle_wEb4 (srcE srcL : NodeKind → ESrc) (κ : NodeKind) (es : Log) (r : Fin (ncR κ) → F) :
    mle (wEb4 srcE srcL κ es) r =
      (Eval.matMLE (srcE κ).ea (ptOf (e2R κ) (rxs (e2R κ) 227 es)) r +
        kapB 23 227 es * Eval.matMLE (srcE κ).eb (ptOf (e2R κ) (rxs (e2R κ) 227 es)) r +
        kapB 23 227 es ^ 2 * Eval.matMLE (srcE κ).ec (ptOf (e2R κ) (rxs (e2R κ) 227 es)) r) +
      kapB 23 227 es ^ 3 *
        (Eval.matMLE (srcL κ).ea (ptOf (lrR κ) (rxs (lrR κ) 179 es)) r +
          kapB 17 179 es * Eval.matMLE (srcL κ).eb (ptOf (lrR κ) (rxs (lrR κ) 179 es)) r +
          kapB 17 179 es ^ 2 * Eval.matMLE (srcL κ).ec (ptOf (lrR κ) (rxs (lrR κ) 179 es)) r) := by
  show mle (fun y => _ + _ * _) r = _
  rw [mle_add_mul, mle_wInn, mle_wInn]
  rfl

/-! ## E4 end (325) -/

theorem rPt4_agree {κ : NodeKind} {es es' : Log} {p : ℕ} (h : Agree es es' p) (hp : 325 ≤ p) :
    rPt4 κ es = rPt4 κ es' := rchs2_congr (h.mono (by have := (dims_le' κ).2.2.1; omega))

/-- E4's final true value: `W(r′)·ẑ(r′) + κ_E⁴·eq(p_y, r′)·M̃*(x̂, ŷ)`. -/
theorem final_TEb4 (R : FSrc) (srcE srcL : NodeKind → ESrc) (κ : NodeKind) (L es : Log) :
    trueSum innerExprR (bindAll (TEb4 R srcE srcL κ L es) (rchs2 275 (fun d => chF d 0) es (ncR κ))) 0 =
      mle (wEb4 srcE srcL κ es) (ptOf (ncR κ) (rPt4 κ es)) *
        mle (zCG R (ncR κ) L es) (ptOf (ncR κ) (rPt4 κ es)) +
      kapB 23 227 es ^ 4 * eq (Rsv.lowA (ncR κ) (pyL es)) (ptOf (ncR κ) (rPt4 κ es)) *
        mStack srcE (sL es) (xHat κ es) (Rsv.hiPt (ptOf (ncR κ) (rPt4 κ es)) (pyL es)) := by
  obtain ⟨g0, g1, g2, g3⟩ := TEb4_get R srcE srcL κ L es
  rw [trueSum_bindAll' _ _ _ (by simp [rchs2]) (fun t ht => TEb4_size R srcE srcL κ L es t ht)]
  simp only [innerExprR, Expr.eval]
  rw [g0, g1, g2, g3, tbl_ofFn, tbl_ofFn, tbl_ofFn, tbl_ofFn, mle_smul, mle_eqPt]
  have hc : mle (cTab4 srcE κ es) (ptOf (ncR κ) (rchs2 275 (fun d => chF d 0) es (ncR κ))) =
      mStack srcE (sL es) (xHat κ es) (Rsv.hiPt (ptOf (ncR κ) (rPt4 κ es)) (pyL es)) :=
    mle_mStack_col srcE (sL es) (xHat κ es) (pyL es) _
  rw [hc]
  simp only [rPt4]

/-- **`habs` at E4 end** (A.10 E4 end, `finE` (iv″)–(v)): with every E4 round answered and doomed,
after E4 end's absorb either `finE` (iv″) fails on the log, or E's pending claim is false. -/
theorem e4_habs_end4 (R : FSrc) (srcE srcL : NodeKind → ESrc) {L es : Log}
    (x : ByteArray × Digest) (hl : es.length = 325) (hd : D4E4 R srcE srcL L es) :
    RejFinE4 srcE srcL L (es ++ [x]) ∨ PendE4 R L (es ++ [x]) := by
  obtain ⟨κ, hk, -, hw⟩ := hd
  have hdm := dims_le' κ
  have hk' : kindOfC (es ++ [x]) = .node κ := (kindOfC_append [x] (by omega)).trans hk
  have ha : ans3 275 (fun _ => ncR κ) es = ncR κ := by
    simp only [ans3, hl]; omega
  rw [ha] at hw
  unfold Wrong2 at hw
  simp only [Nat.sub_self] at hw
  rw [final_TEb4] at hw
  have hag : Agree (es ++ [x]) es 325 := hl ▸ agree_append es [x] le_rfl
  have hc : clR2 275 16 readF (fun d => chF d 0) c4E4 L (es ++ [x]) (ncR κ) =
      clR2 275 16 readF (fun d => chF d 0) c4E4 L es (ncR κ) :=
    clR2_same (c4E4_agree hag (by norm_num)) (hag.mono (by omega))
  by_cases hrej : RejFinE4 srcE srcL L (es ++ [x])
  · exact .inl hrej
  right
  refine ⟨κ, hk', by simp; omega, fun hok => ?_⟩
  have hchk : clR2 275 16 readF (fun d => chF d 0) c4E4 L (es ++ [x]) (ncR κ) =
      mle (wEb4 srcE srcL κ (es ++ [x])) (ptOf (ncR κ) (rPt4 κ (es ++ [x]))) *
        readF (msgAt (es ++ [x]) 325) 0 +
      kapB 23 227 (es ++ [x]) ^ 4 * eq (Rsv.lowA (ncR κ) (pyL (es ++ [x]))) (ptOf (ncR κ) (rPt4 κ (es ++ [x]))) *
        mStack srcE (sL (es ++ [x])) (xHat κ (es ++ [x]))
          (Rsv.hiPt (ptOf (ncR κ) (rPt4 κ (es ++ [x]))) (pyL (es ++ [x]))) := by
    by_contra hne; exact hrej ⟨κ, hk', by simp; omega, hne⟩
  obtain ⟨-, hpy, hs, -⟩ := child_agree hag (by norm_num)
  rw [hc, wEb4_agree srcE srcL κ (hag.mono (by norm_num)), rPt4_agree hag le_rfl, ← hok,
    rPt4_agree hag le_rfl, zCG_same R (ncR κ) (R.ofAgree L hag) (by norm_num),
    kapB_agree (a := 23) (b2 := 227) hag (by norm_num), hpy, hs, xHat_agree hag (by norm_num)] at hchk
  exact hw hchk

/-- **`finE` (iv″) is a revision 4.1 check.** -/
theorem rejFinE4_log (srcE srcL : NodeKind → ESrc) : RejLog4 (RejFinE4 srcE srcL) := by
  refine rejLog4_onNode (fun κ => rejLog4_of (q := 326) (by norm_num) (fun _ _ h => h.1)
    (fun L es L' es' h1 h2 h => ?_) (by simpa using p4b_abs.2.2.1)) fun _ _ _ h => by
      have := h.1; omega
  have hdm := dims_le' κ
  obtain ⟨-, hpy, hs, -⟩ := child_agree h (by norm_num)
  rw [clR2_same (L' := L') (es' := es') (c4E4_agree h (by norm_num)) (h.mono (by omega)),
    wEb4_agree srcE srcL κ (h.mono (by norm_num)), rPt4_agree h (by norm_num),
    msgAt_congr h (show 325 < 326 by norm_num), kapB_agree (a := 23) (b2 := 227) h (by norm_num),
    hpy, hs, xHat_agree h (by norm_num)]
  exact and_congr_left fun _ => ⟨fun _ => h2, fun _ => h1⟩

/-! ## Controls -/

/-- (+) On a segment's chain, E3 is never doomed (a segment runs no E). -/
theorem not_batBadE4_seg {R : FSrc} {srcE srcL : NodeKind → ESrc} {L es : Log} {σ : SegKind}
    (h : kindOfC es = .seg σ) : ¬ BatBadE4 R srcE srcL L es := not_onNode_seg h

/-- (−) On a node, a batched claim differing from the true value after `κ_E` is E3's doom. -/
theorem batBadE4_of_ne {R : FSrc} {srcE srcL : NodeKind → ESrc} {L es : Log} {κ : NodeKind}
    (hk : kindOfC es = .node κ) (hl : 274 < es.length)
    (h : c4E4 L es ≠ trueSum innerExprR (TEb4 R srcE srcL κ L es) (ncR κ)) :
    BatBadE4 R srcE srcL L es := ⟨κ, hk, hl, h⟩

/-- (−) With E4 end's value equal to `ẑ(r′)`, E's claim is not pending. -/
theorem not_pendE4 {R : FSrc} {L es : Log} {κ : NodeKind} (hk : kindOfC es = .node κ)
    (h : readF (msgAt es 325) 0 = mle (zCG R (ncR κ) L es) (ptOf (ncR κ) (rPt4 κ es))) :
    ¬ PendE4 R L es := by
  rintro ⟨ν, hν, -, hn⟩; rw [hk] at hν; cases hν; exact hn h.symm

/-- (+) `N2`'s E4 point has 24 coordinates: the 25th slot is a dummy (`rPt4_length`). -/
theorem rPt4_N2 (es : Log) : (rPt4 .N2 es).length = 24 := rPt4_length _ _

end FR.Snd.P4b
