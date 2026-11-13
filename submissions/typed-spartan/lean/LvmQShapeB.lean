-- New for lvm2 (CR-Q, roll 7 SH2-Z; CR-DES §1.5 circuit side): the batched basis of `C_main`'s opening in
-- both shapes. The regular claims' terms come in pairs (the big key, the moved key, one leaf); the trie is cut
-- at depth 20: the subtries below are built once per top pair, the top four levels twice (big and moved keys)
-- and muxed. Adapted from HAR-WH's `basisG`/`claimTerms` (`LvmQAsmArith2WhirBasis`).
import LvmQShapeC

/-!
# The basis in both shapes

* **`ZT`**: a term pair: scale, leaf, big top key `pb`, moved top key `ps` (`ν − 20` bits each, `ν = CMain.nu20`;
  three at B1's ν = 23), the common rest.
  `ptPair`, `rgPair`, `partsPairs`, `regPairs`: the pairs of a regular claim (one leaf, two keys);
  `ptPair_spec` … `regPairs_spec`: the big keys give the claim's weight, the moved keys `smallW`.
* **`zTerms`**: the pairs of the regular claims and the plain terms of the muxed ones (`oneClaim`).
* **`lowsG`**: the subtries below depth 20, one per top pair (`keysOf`); `sum_groups`: regrouping.
* **`basisZ`**: the two tops (big and moved keys over the shared subtries, plus the muxed claims' terms) and
  their mux. `basisZ_spec`: `mux(s, Σ s^i W_i(X), Σ s^i W^σ_i(X))`.
-/

set_option autoImplicit false

namespace Lvm.QShape

open Lvm Lvm.Loop Lvm.Loop.Build Lvm.Loop.QRing Lvm.Har Lvm.Shape

variable {c : Ctx} {M : Mem}

/-! ## Keys -/

/-- The top `ν − 20` bits of a key (coordinates `ν − 1` … 20; 22 … 20 at B1's ν = 23). -/
def topK (bit : ℕ → Bool) : List Bool := keyOf bit CMain.nu20 20

theorem keyOf_app (bit : ℕ → Bool) {k m : ℕ} (hk : k ≤ m) :
    ∀ n, m ≤ n → keyOf bit n k = keyOf bit n m ++ keyOf bit m k
  | 0, h => by
    obtain rfl : m = 0 := by omega
    obtain rfl : k = 0 := by omega
    rfl
  | n + 1, h => by
    by_cases e : m = n + 1
    · subst e
      rw [show keyOf bit (n + 1) (n + 1) = [] by rw [keyOf.eq_2]; simp, List.nil_append]
    · rw [keyOf.eq_2, if_neg (by omega), keyOf.eq_2, if_neg (by omega), keyOf_app bit hk n (by omega),
        List.cons_append]

theorem keyOf_length (bit : ℕ → Bool) (k : ℕ) : ∀ n, (keyOf bit n k).length = n - k
  | 0 => by simp [keyOf]
  | n + 1 => by
    rw [keyOf.eq_2]
    split_ifs with h
    · simp; omega
    · rw [List.length_cons, keyOf_length bit k n]; omega

theorem topK_length (bit : ℕ → Bool) : (topK bit).length = CMain.nu20 - 20 := keyOf_length bit 20 _

theorem keyOf_top (bit : ℕ → Bool) {k : ℕ} (hk : k ≤ 20) : keyOf bit CMain.nu20 k = topK bit ++ keyOf bit 20 k :=
  keyOf_app bit hk CMain.nu20 (by decide)

theorem keyOf_congr (b b' : ℕ → Bool) (k : ℕ) : ∀ n, (∀ i, k ≤ i → i < n → b i = b' i) →
    keyOf b n k = keyOf b' n k
  | 0, _ => rfl
  | n + 1, h => by
    rw [keyOf.eq_2, keyOf.eq_2]
    split_ifs with hn
    · rfl
    · rw [h n (by omega) (by omega), keyOf_congr b b' k n fun i h1 h2 ↦ h i h1 (by omega)]

theorem shr_sub (a i : ℕ) (hi : i < 20) (h : 3 * 2 ^ 20 ≤ a) : (a - 3 * 2 ^ 20) / 2 ^ i % 2 = a / 2 ^ i % 2 := by
  have hk : 3 * 2 ^ 20 = 2 ^ i * (3 * 2 ^ (20 - i)) := by
    rw [mul_left_comm, ← pow_add, Nat.add_sub_cancel' (by omega)]
  have ha : a = (a - 3 * 2 ^ 20) + 2 ^ i * (3 * 2 ^ (20 - i)) := by rw [← hk]; omega
  have he : 3 * 2 ^ (20 - i) % 2 = 0 := by
    rw [Nat.mul_mod, Nat.two_pow_mod_two_eq_zero.mpr (by omega)]
  conv_rhs => rw [ha]
  rw [Nat.add_mul_div_left _ _ (by positivity), Nat.add_mod, he, add_zero, Nat.mod_mod]

theorem selbit_shift_lo (blk : Placement) (hr : RegP blk) {i : ℕ} (h1 : blk.variableCount ≤ i) (h2 : i < 20) :
    selbit (shiftP blk) i = selbit blk i := by
  rw [selbit_eq _ (by rw [shiftP_vc]; exact h1), selbit_eq _ h1, shiftP_index, shr_div, shr_div,
    shr_sub _ _ h2 (by have := hr.2.2.1; omega)]

theorem bitP_shift_lo (z o : Cell) (blk : Placement) (zl : List Cell) (hr : RegP blk) {i : ℕ} (h2 : i < 20) :
    bitP z o CMain.nu20 (shiftP blk) zl i = bitP z o CMain.nu20 blk zl i := by
  unfold bitP
  rw [shiftP_vc]
  split_ifs with h1 h3
  · rfl
  · exact selbit_shift_lo blk hr h3 h2
  · rfl

/-! ## Term pairs -/

/-- A term pair: scale, leaf, the big and the moved top keys, the common rest of the key. -/
structure ZT where
  sc : Cell
  lf : Cell
  pb : List Bool
  ps : List Bool
  rest : List Bool

/-- The big term. -/
def ZT.big (t : ZT) : TC := ⟨t.sc, t.pb ++ t.rest, t.lf⟩
/-- The moved term. -/
def ZT.sml (t : ZT) : TC := ⟨t.sc, t.ps ++ t.rest, t.lf⟩
/-- The term below depth 20. -/
def ZT.low (t : ZT) : TC := ⟨t.sc, t.rest, t.lf⟩

/-- The pair of a point part on a regular block (`nu = ν`). -/
def ptPair (xb : ℕ) (z o sc : Cell) (blk : Placement) (zl : List Cell) (memo : Memo) : BM (Memo × ZT) := do
  let r ← chainG xb z o zl (ncPre z o zl) memo
  pure (r.1, ⟨sc, r.2, topK (bitP z o CMain.nu20 blk zl), topK (bitP z o CMain.nu20 (shiftP blk) zl),
    keyOf (bitP z o CMain.nu20 blk zl) 20 (ncPre z o zl)⟩)

theorem e0f_nu (xb : ℕ) : e0f M CMain.nu20 xb CMain.nu20 = 1 := by simp [e0f]

theorem ptPair_spec {xb : ℕ} {z o : Cell} (hz : z.val M = 0) (ho : o.val M = 1) {sc : Cell} {blk : Placement}
    {zl : List Cell} {memo : Memo} (hm : MemoOk M (fun i ↦ M.e (xb + i)) memo) (hzl : zl.length = blk.variableCount)
    (hr : RegP blk) :
    Hs c M (ptPair xb z o sc blk zl memo) (fun r ↦ MemoOk M (fun i ↦ M.e (xb + i)) r.1 ∧
      tval M (fun i ↦ M.e (xb + i)) CMain.nu20 r.2.big = sc.val M * partW M CMain.nu20 xb CMain.nu20 blk zl ∧
      tval M (fun i ↦ M.e (xb + i)) CMain.nu20 r.2.sml =
        sc.val M * partW M CMain.nu20 xb CMain.nu20 (shiftP blk) zl ∧
      r.2.pb.length = CMain.nu20 - 20 ∧ r.2.ps.length = CMain.nu20 - 20) := by
  have hnu : CMain.nu20 = 23 := rfl
  have hk : ncPre z o zl ≤ 20 := (ncPre_le z o zl).trans (hzl ▸ hr.1)
  refine hs_bind (chainG_spec hz ho _ memo (ncPre_le z o zl) hm) fun r ⟨hm', hv⟩ ↦
    hs_pure ⟨hm', ?_, ?_, topK_length _, topK_length _⟩
  · simp only [ZT.big]
    rw [← keyOf_top _ hk, tval, kprod_keyOf, hv, mul_assoc,
      partW_eq hz ho hzl (by have := hr.1; omega) le_rfl, e0f_nu, one_mul]
  · simp only [ZT.sml]
    rw [keyOf_congr (bitP z o CMain.nu20 blk zl) (bitP z o CMain.nu20 (shiftP blk) zl) _ 20
        (fun i _ hi ↦ (bitP_shift_lo z o blk zl hr hi).symm),
      ← keyOf_top _ hk, tval, kprod_keyOf, hv, mul_assoc,
      partW_eq hz ho (by rw [shiftP_vc]; exact hzl) (by rw [shiftP_vc]; have := hr.1; omega) le_rfl, e0f_nu,
      one_mul]

/-- The pair of a ring claim on a regular block. -/
def rgPair (xb : ℕ) (z sc : Cell) (blk : Placement) (pt cs : List Cell) : BM ZT := do
  let lf ← ringLeaf blk.variableCount pt cs xb z.n
  pure ⟨sc, lf, topK (selbit blk), topK (selbit (shiftP blk)), keyOf (selbit blk) 20 blk.variableCount⟩

theorem rgPair_spec {xb : ℕ} {z : Cell} (hz : z.val M = 0) (hzE : z.ty = .E) {sc : Cell} {blk : Placement}
    {pt cs : List Cell} (hr : RegP blk) (hpt : pt.length = blk.variableCount) (hcs : cs.length = 64)
    (hbs : sz (binDec 64 blk.variableCount 0) = blk.variableCount) :
    Hs c M (rgPair xb z sc blk pt cs) (fun t ↦
      tval M (fun i ↦ M.e (xb + i)) CMain.nu20 t.big = sc.val M * (blk.eqAbove (xsOf M CMain.nu20 xb) *
        ringWeight (vs M pt) ((xsOf M CMain.nu20 xb).take blk.variableCount) (vs M cs)) ∧
      tval M (fun i ↦ M.e (xb + i)) CMain.nu20 t.sml = sc.val M * ((shiftP blk).eqAbove (xsOf M CMain.nu20 xb) *
        ringWeight (vs M pt) ((xsOf M CMain.nu20 xb).take blk.variableCount) (vs M cs)) ∧
      t.pb.length = CMain.nu20 - 20 ∧ t.ps.length = CMain.nu20 - 20) := by
  have hnu : CMain.nu20 = 23 := rfl
  have hv := hr.1
  refine hs_bind (ringLeaf_spec (zval_e hz hzE) hpt hcs hbs ((xsOf M CMain.nu20 xb).take blk.variableCount)
    (by rw [List.length_take, xs_length]; omega)
    (fun n hn ↦ by rw [getD_take' _ _ hn, xs_getD (by omega)])) fun lf hlf ↦
      hs_pure ⟨?_, ?_, topK_length _, topK_length _⟩
  · simp only [ZT.big]
    rw [← keyOf_top _ hv, tval, kprod_keyOf, hlf, eqAbove_prod blk _ (fun i ↦ M.e (xb + i))
      (by rw [xs_length]; omega) (fun i hi ↦ xs_getD (by rwa [xs_length] at hi)), xs_length]
    ring
  · simp only [ZT.sml]
    rw [keyOf_congr (selbit blk) (selbit (shiftP blk)) _ 20 (fun i h1 h2 ↦ (selbit_shift_lo blk hr h1 h2).symm),
      ← keyOf_top _ hv, tval, kprod_keyOf, hlf, eqAbove_prod (shiftP blk) _ (fun i ↦ M.e (xb + i))
      (by rw [xs_length, shiftP_vc]; omega) (fun i hi ↦ xs_getD (by rwa [xs_length] at hi)), xs_length, shiftP_vc]
    ring

/-- The pairs of a sum's parts (scale `sc · c_j`). -/
def partsPairs (xb : ℕ) (z o sc : Cell) : List (Cell × Placement × List Cell) → Memo → BM (Memo × List ZT)
  | [], memo => pure (memo, [])
  | x :: ps, memo => do
    let sc' ← mulAdd .E sc x.1 z
    let r ← ptPair xb z o sc' x.2.1 x.2.2 memo
    let r' ← partsPairs xb z o sc ps r.1
    pure (r'.1, r.2 :: r'.2)

theorem partsPairs_spec {xb : ℕ} {z o : Cell} (hz : z.val M = 0) (ho : o.val M = 1) {sc : Cell} :
    ∀ (ps : List (Cell × Placement × List Cell)) (memo : Memo),
      (ps.all fun x ↦ decide (x.2.1.variableCount ≤ CMain.nu20) && decide (x.2.2.length = x.2.1.variableCount)) =
        true →
      (∀ x ∈ ps, RegP x.2.1) → MemoOk M (fun i ↦ M.e (xb + i)) memo →
      Hs c M (partsPairs xb z o sc ps memo) (fun r ↦ MemoOk M (fun i ↦ M.e (xb + i)) r.1 ∧
        (r.2.map fun t ↦ tval M (fun i ↦ M.e (xb + i)) CMain.nu20 t.big).sum =
          sc.val M * (ps.map fun x ↦ x.1.val M * partW M CMain.nu20 xb CMain.nu20 x.2.1 x.2.2).sum ∧
        (r.2.map fun t ↦ tval M (fun i ↦ M.e (xb + i)) CMain.nu20 t.sml).sum =
          sc.val M * (ps.map fun x ↦ x.1.val M * partW M CMain.nu20 xb CMain.nu20 (shiftP x.2.1) x.2.2).sum ∧
        ∀ t ∈ r.2, t.pb.length = CMain.nu20 - 20 ∧ t.ps.length = CMain.nu20 - 20)
  | [], memo, _, _, hm => hs_pure ⟨hm, by simp, by simp, by simp⟩
  | x :: ps, memo, hwf, hr, hm => by
    simp only [List.all_cons, Bool.and_eq_true, decide_eq_true_eq] at hwf
    obtain ⟨⟨-, h2⟩, hrest⟩ := hwf
    unfold partsPairs
    refine hs_bind (hs_mulAdd _ _ _ _) fun sc' hsc ↦ hs_bind (ptPair_spec hz ho hm h2 (hr x List.mem_cons_self))
      fun r ⟨hm', hb, hs, hl1, hl2⟩ ↦ hs_bind (partsPairs_spec hz ho ps r.1 hrest
        (fun y hy ↦ hr y (List.mem_cons_of_mem _ hy)) hm') fun r' ⟨hm'', hb', hs', hl'⟩ ↦
      hs_pure ⟨hm'', ?_, ?_, ?_⟩
    · rw [List.map_cons, List.sum_cons, hb, hb', hsc, hz, List.map_cons, List.sum_cons]; ring
    · rw [List.map_cons, List.sum_cons, hs, hs', hsc, hz, List.map_cons, List.sum_cons]; ring
    · intro t ht
      rcases List.mem_cons.mp ht with rfl | ht
      · exact ⟨hl1, hl2⟩
      · exact hl' t ht

/-- The pairs of a regular claim (scale cell `sc`). -/
def regPairs (xb : ℕ) (z o sc : Cell) (cc : CClaim) (memo : Memo) : BM (Memo × List ZT) :=
  match cc.cw with
  | .point blk zl => do
    let r ← ptPair xb z o sc blk zl memo
    pure (r.1, [r.2])
  | .ring blk pt cs => do
    let t ← rgPair xb z sc blk pt cs
    pure (memo, [t])
  | .sum _ parts => partsPairs xb z o sc parts memo

theorem take_nu (xb : ℕ) : (xsOf M CMain.nu20 xb).take CMain.nu20 = xsOf M CMain.nu20 xb :=
  List.take_of_length_le (by rw [xs_length])

theorem eqAbove_nu (y : List FE) (hy : y.length = CMain.nu20) : (⟨CMain.nu20, 0⟩ : Placement).eqAbove y = 1 := by
  simp [Placement.eqAbove, hy, selectorPoint, eqEval]

theorem regPairs_spec {xb : ℕ} {z o : Cell} (hz : z.val M = 0) (ho : o.val M = 1) (hzE : z.ty = .E) {sc : Cell}
    {cc : CClaim} {memo : Memo} (hwf : WF1 CMain.nu20 cc = true) (hr : RegC cc)
    (hm : MemoOk M (fun i ↦ M.e (xb + i)) memo) :
    Hs c M (regPairs xb z o sc cc memo) (fun r ↦ MemoOk M (fun i ↦ M.e (xb + i)) r.1 ∧
      (r.2.map fun t ↦ tval M (fun i ↦ M.e (xb + i)) CMain.nu20 t.big).sum =
        sc.val M * (cc.val M).2.onStack.1 (xsOf M CMain.nu20 xb) ∧
      (r.2.map fun t ↦ tval M (fun i ↦ M.e (xb + i)) CMain.nu20 t.sml).sum =
        sc.val M * smallW M cc (xsOf M CMain.nu20 xb) ∧
      ∀ t ∈ r.2, t.pb.length = CMain.nu20 - 20 ∧ t.ps.length = CMain.nu20 - 20) := by
  rcases cc with ⟨com, cw, v⟩
  cases cw with
  | point blk zl =>
    simp only [WF1, Bool.and_eq_true, decide_eq_true_eq] at hwf
    simp only [RegC] at hr
    unfold regPairs
    refine hs_bind (ptPair_spec hz ho hm hwf.2 hr) fun r ⟨hm', hb, hs, hl1, hl2⟩ ↦ hs_pure ⟨hm', ?_, ?_, ?_⟩
    · rw [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero, hb, partW, take_nu]; rfl
    · rw [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero, hs, partW, take_nu]; rfl
    · intro t ht; rcases List.mem_singleton.mp ht with rfl; exact ⟨hl1, hl2⟩
  | ring blk pt cs =>
    simp only [WF1, Bool.and_eq_true, decide_eq_true_eq] at hwf
    obtain ⟨⟨⟨-, h2⟩, h3⟩, h4⟩ := hwf
    simp only [RegC] at hr
    unfold regPairs
    refine hs_bind (rgPair_spec hz hzE hr h2 h3 h4) fun t ⟨hb, hs, hl1, hl2⟩ ↦ hs_pure ⟨hm, ?_, ?_, ?_⟩
    · rw [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero, hb]; rfl
    · rw [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero, hs]; rfl
    · intro t' ht; rcases List.mem_singleton.mp ht with rfl; exact ⟨hl1, hl2⟩
  | sum nu parts =>
    simp only [WF1, Bool.and_eq_true, decide_eq_true_eq] at hwf
    simp only [RegC] at hr
    obtain ⟨rfl, hp⟩ := hr
    show Hs c M (partsPairs xb z o sc parts memo) _
    refine hs_mono (partsPairs_spec hz ho parts memo hwf.2 hp hm) fun r ⟨hm', hb, hs, hl⟩ ↦ ⟨hm', ?_, ?_, hl⟩
    · rw [hb]
      show _ = sc.val M * (sumClaim CMain.nu20 (parts.map fun e ↦ (e.1.val M, e.2.1, vs M e.2.2)) (v.val M)).onStack.1
        (xsOf M CMain.nu20 xb)
      rw [sumClaim_onStack _ _ _ (xs_length CMain.nu20 xb), List.map_map]
      refine congrArg (sc.val M * ·) (congrArg List.sum (List.map_congr_left fun x _ ↦ ?_))
      simp only [Function.comp_apply, partW, take_nu, partB, BlockClaim.point, BlockClaim.onStack]
    · rw [hs]
      show _ = sc.val M * (sumClaim CMain.nu20 (parts.map fun e ↦ (e.1.val M, shiftP e.2.1, vs M e.2.2)) 0).onStack.1
        (xsOf M CMain.nu20 xb)
      rw [sumClaim_onStack _ _ _ (xs_length CMain.nu20 xb), List.map_map]
      refine congrArg (sc.val M * ·) (congrArg List.sum (List.map_congr_left fun x _ ↦ ?_))
      simp only [Function.comp_apply, partW, take_nu, partB, BlockClaim.point, BlockClaim.onStack]

theorem hs_and {α : Type} {m : BM α} {P Q : α → Prop} (hP : Hs c M m P) (hQ : Hs c M m Q) :
    Hs c M m (fun a ↦ P a ∧ Q a) := fun p h ↦ ⟨hP p h, hQ p h⟩

/-! ## The claims' terms -/

/-- The term pairs of the regular claims and the terms of the muxed ones (scale cells `sp + i`). -/
def zTerms (xb : ℕ) (z o : Cell) (sp : ℕ) : ℕ → List (CClaim × Bool) → Memo → BM (Memo × List ZT × List TC)
  | _, [], memo => pure (memo, [], [])
  | i, e :: cl, memo =>
    if e.2 then do
      let r ← regPairs xb z o (ec (sp + i)) e.1 memo
      let r' ← zTerms xb z o sp (i + 1) cl r.1
      pure (r'.1, r.2 ++ r'.2.1, r'.2.2)
    else do
      let r ← oneClaim CMain.nu20 xb z o (ec (sp + i)) e.1 memo
      let r' ← zTerms xb z o sp (i + 1) cl r.1
      pure (r'.1, r'.2.1, r.2 ++ r'.2.2)

/-- The big weight of a claim at `xs`. -/
def wBig (M : Mem) (xs : List FE) (e : CClaim × Bool) : FE := (e.1.val M).2.onStack.1 xs

/-- The small weight of a claim at `xs` (regular: moved blocks; muxed: its own form). -/
def wSml (M : Mem) (xs : List FE) (e : CClaim × Bool) : FE :=
  if e.2 then smallW M e.1 xs else (e.1.val M).2.onStack.1 xs

theorem zTerms_spec {xb : ℕ} {z o : Cell} (hz : z.val M = 0) (ho : o.val M = 1) (hzE : z.ty = .E) {sp N : ℕ}
    {s : FE} (hs : ∀ j < N, M.e (sp + j) = s ^ j) :
    ∀ (cl : List (CClaim × Bool)) (i : ℕ) (memo : Memo),
      (∀ e ∈ cl, WF1 CMain.nu20 e.1 = true ∧ (e.2 = true → RegC e.1)) →
      MemoOk M (fun i ↦ M.e (xb + i)) memo → i + cl.length ≤ N →
      Hs c M (zTerms xb z o sp i cl memo) (fun r ↦ MemoOk M (fun i ↦ M.e (xb + i)) r.1 ∧
        (r.2.1.map fun t ↦ tval M (fun i ↦ M.e (xb + i)) CMain.nu20 t.big).sum +
          (r.2.2.map (tval M (fun i ↦ M.e (xb + i)) CMain.nu20)).sum =
            bsum s i (cl.map (wBig M (xsOf M CMain.nu20 xb))) ∧
        (r.2.1.map fun t ↦ tval M (fun i ↦ M.e (xb + i)) CMain.nu20 t.sml).sum +
          (r.2.2.map (tval M (fun i ↦ M.e (xb + i)) CMain.nu20)).sum =
            bsum s i (cl.map (wSml M (xsOf M CMain.nu20 xb))) ∧
        ∀ t ∈ r.2.1, t.pb.length = CMain.nu20 - 20 ∧ t.ps.length = CMain.nu20 - 20)
  | [], _, memo, _, hm, _ => hs_pure ⟨hm, by simp [bsum], by simp [bsum], by simp⟩
  | e :: cl, i, memo, hw, hm, hN => by
    simp only [List.length_cons] at hN
    obtain ⟨hwf, hreg⟩ := hw e List.mem_cons_self
    have hw' : ∀ e' ∈ cl, WF1 CMain.nu20 e'.1 = true ∧ (e'.2 = true → RegC e'.1) :=
      fun e' he' ↦ hw e' (List.mem_cons_of_mem _ he')
    have hsi : (ec (sp + i)).val M = s ^ i := by rw [Cell.val_E, hs i (by omega)]
    unfold zTerms
    by_cases he : e.2 = true
    · rw [if_pos he]
      refine hs_bind (regPairs_spec hz ho hzE hwf (hreg he) hm) fun r ⟨hm', hb, hsm, hl⟩ ↦
        hs_bind (zTerms_spec hz ho hzE hs cl (i + 1) r.1 hw' hm' (by omega)) fun r' ⟨hm'', hb', hs', hl'⟩ ↦
          hs_pure ⟨hm'', ?_, ?_, ?_⟩
      · rw [List.map_append, List.sum_append, add_assoc, hb', hb, hsi, List.map_cons, bsum]; rfl
      · rw [List.map_append, List.sum_append, add_assoc, hs', hsm, hsi, List.map_cons, bsum, wSml, if_pos he]
      · intro t ht
        rcases List.mem_append.mp ht with ht | ht
        · exact hl t ht
        · exact hl' t ht
    · rw [if_neg he]
      refine hs_bind (oneClaim_spec hz ho hzE hwf hm) fun r ⟨hm', hv⟩ ↦
        hs_bind (zTerms_spec hz ho hzE hs cl (i + 1) r.1 hw' hm' (by omega)) fun r' ⟨hm'', hb', hs', hl'⟩ ↦
          hs_pure ⟨hm'', ?_, ?_, hl'⟩
      · dsimp only
        rw [List.map_append, List.sum_append, List.map_cons, bsum, ← hb', wBig, ← hsi, ← hv]
        ring
      · dsimp only
        rw [List.map_append, List.sum_append, List.map_cons, bsum, ← hs', wSml, if_neg he, ← hsi, ← hv]
        ring

/-! ## The cut at depth 20 -/

/-- A pair's two top keys. -/
abbrev ZK : Type := List Bool × List Bool

/-- The top keys of a pair. -/
def zkey (t : ZT) : ZK := (t.pb, t.ps)

/-- The distinct top-key pairs. -/
def keysOf (ts : List ZT) : List ZK := (ts.map zkey).dedup

/-- The terms below depth 20 of the pairs with top keys `k`. -/
def grp (ts : List ZT) (k : ZK) : List TC := (ts.filter fun t ↦ zkey t == k).map ZT.low

/-- **The subtries below depth 20**, one per top-key pair. -/
def lowsG (xb : ℕ) (z : Cell) (ts : List ZT) : List ZK → BM (List (ZK × Cell))
  | [] => pure []
  | k :: ks => do
    let v ← trieG xb z 20 (grp ts k)
    let r ← lowsG xb z ts ks
    pure ((k, v) :: r)

theorem lowsG_spec {xb : ℕ} {z : Cell} (hz : z.val M = 0) (ts : List ZT) (F : ZK → FE) :
    ∀ ks : List ZK, Hs c M (lowsG xb z ts ks) (fun r ↦ (r.map fun e ↦ F e.1 * e.2.val M).sum =
      (ks.map fun k ↦ F k * ((grp ts k).map (tval M (fun i ↦ M.e (xb + i)) 20)).sum).sum)
  | [] => hs_pure (by simp)
  | k :: ks => by
    unfold lowsG
    exact hs_bind (trieG_spec hz 20 _) fun v hv ↦ hs_bind (lowsG_spec hz ts F ks) fun r hr ↦
      hs_pure (by rw [List.map_cons, List.sum_cons, hr, hv, List.map_cons, List.sum_cons])

theorem sum_ite_mem {K : Type} [DecidableEq K] (a : FE) (k₀ : K) :
    ∀ L : List K, L.Nodup → k₀ ∈ L → (L.map fun k ↦ if k₀ = k then a else 0).sum = a
  | [], _, h => absurd h (by simp)
  | k :: L, hn, h => by
    rw [List.nodup_cons] at hn
    rw [List.map_cons, List.sum_cons]
    by_cases e : k₀ = k
    · subst e
      rw [if_pos rfl, List.map_congr_left (g := fun _ ↦ (0 : FE)) fun k' hk' ↦ if_neg fun (h : k₀ = k') ↦ hn.1 (h ▸ hk')]
      simp
    · rw [if_neg e, zero_add, sum_ite_mem a k₀ L hn.2 ((List.mem_cons.mp h).resolve_left e)]

/-- **Regrouping by top keys.** -/
theorem sum_groups (f : ZT → FE) (ts : List ZT) : ∀ L : List ZK, L.Nodup → (∀ t ∈ ts, zkey t ∈ L) →
    (ts.map f).sum = (L.map fun k ↦ ((ts.filter fun t ↦ zkey t == k).map f).sum).sum := by
  induction ts with
  | nil => intro L _ _; simp
  | cons t ts ih =>
    intro L hn hm
    rw [List.map_cons, List.sum_cons, ih L hn fun t' ht' ↦ hm t' (List.mem_cons_of_mem _ ht')]
    have e2 : ∀ k, (((t :: ts).filter fun t ↦ zkey t == k).map f).sum =
        (if zkey t = k then f t else 0) + ((ts.filter fun t ↦ zkey t == k).map f).sum := fun k ↦ by
      by_cases h : zkey t = k <;> simp [List.filter_cons, h]
    rw [List.map_congr_left (fun k _ ↦ e2 k), List.sum_map_add,
      sum_ite_mem (f t) (zkey t) L hn (hm t List.mem_cons_self)]

theorem kprod_app (X : ℕ → FE) (m : ℕ) (r : List Bool) :
    ∀ p : List Bool, kprod X (m + p.length) (p ++ r) = kprod X (m + p.length) p * kprod X m r
  | [] => by simp [kprod]
  | b :: p => by
    have ih := kprod_app X m r p
    show fb b (X (m + p.length)) * kprod X (m + p.length) (p ++ r) =
      fb b (X (m + p.length)) * kprod X (m + p.length) p * kprod X m r
    rw [ih]; ring

theorem kprod_split (X : ℕ → FE) (p r : List Bool) (hp : p.length = CMain.nu20 - 20) :
    kprod X CMain.nu20 (p ++ r) = kprod X CMain.nu20 p * kprod X 20 r := by
  have e : CMain.nu20 = 20 + p.length := by rw [hp]; rfl
  rw [e]; exact kprod_app X 20 r p

/-- **A top over the subtries**: the top keys `sel` (`ν − 20` bits, a function `selk` of the key pair) over the
shared rests give the terms with those keys. -/
theorem top_val (X : ℕ → FE) (ts : List ZT) (sel : ZT → List Bool) (selk : ZK → List Bool)
    (hl : ∀ t ∈ ts, (sel t).length = CMain.nu20 - 20) (hk : ∀ t, sel t = selk (zkey t)) :
    ((keysOf ts).map fun k ↦ kprod X CMain.nu20 (selk k) * ((grp ts k).map (tval M X 20)).sum).sum =
      (ts.map fun t ↦ tval M X CMain.nu20 ⟨t.sc, sel t ++ t.rest, t.lf⟩).sum := by
  have e1 : (ts.map fun t ↦ tval M X CMain.nu20 ⟨t.sc, sel t ++ t.rest, t.lf⟩) =
      ts.map fun t ↦ kprod X CMain.nu20 (sel t) * tval M X 20 t.low := List.map_congr_left fun t ht ↦ by
    simp only [tval, ZT.low, kprod_split X _ _ (hl t ht)]; ring
  rw [e1, sum_groups _ ts (keysOf ts) (List.nodup_dedup _) fun t ht ↦ by
    rw [keysOf, List.mem_dedup]; exact List.mem_map_of_mem ht]
  refine congrArg List.sum (List.map_congr_left fun k _ ↦ ?_)
  rw [grp, List.map_map, ← List.sum_map_mul_left]
  refine congrArg List.sum (List.map_congr_left fun t ht ↦ ?_)
  have hz : zkey t = k := by simpa using (List.mem_filter.mp ht).2
  simp only [Function.comp_apply, hk t, hz]

/-! ## The basis -/

/-- **The batched weight in both shapes** at the point in the `E` cells `xb + i` (`x^σ`'s copies): the term pairs
and the muxed claims' terms (`zTerms`), the subtries below depth 20 (`lowsG`), the two tops, their mux. -/
def basisZ (cl : List (CClaim × Bool)) (sp xb : ℕ) (z o s : Cell) : BM Cell := do
  let r ← zTerms xb z o sp 0 cl []
  let lows ← lowsG xb z r.2.1 (keysOf r.2.1)
  let tb ← trieG xb z CMain.nu20 (lows.map (fun e ↦ (⟨o, e.1.1, e.2⟩ : TC)) ++ r.2.2)
  let ts ← trieG xb z CMain.nu20 (lows.map (fun e ↦ (⟨o, e.1.2, e.2⟩ : TC)) ++ r.2.2)
  muxG s tb ts

theorem basisZ_spec {cl : List (CClaim × Bool)} {sp xb : ℕ} {z o s : Cell} (hz : z.val M = 0) (ho : o.val M = 1)
    (hzE : z.ty = .E) (hw : ∀ e ∈ cl, WF1 CMain.nu20 e.1 = true ∧ (e.2 = true → RegC e.1)) (σ : FE)
    (hs : ∀ j < cl.length, M.e (sp + j) = σ ^ j) :
    Hs c M (basisZ cl sp xb z o s) (fun r ↦ r.val M = mux (s.val M)
      (bsum σ 0 (cl.map (wBig M (xsOf M CMain.nu20 xb)))) (bsum σ 0 (cl.map (wSml M (xsOf M CMain.nu20 xb))))) := by
  unfold basisZ
  refine hs_bind (zTerms_spec (N := cl.length) hz ho hzE hs cl 0 [] hw (fun _ h ↦ by simp at h) (by omega))
    fun r ⟨_, hb, hsm, hl⟩ ↦ ?_
  set X : ℕ → FE := fun i ↦ M.e (xb + i)
  refine hs_bind (hs_and (lowsG_spec hz r.2.1 (fun k ↦ kprod X CMain.nu20 k.1) _)
    (lowsG_spec hz r.2.1 (fun k ↦ kprod X CMain.nu20 k.2) _)) fun lows ⟨hl1, hl2⟩ ↦
    hs_bind (trieG_spec hz CMain.nu20 _) fun tb htb ↦ hs_bind (trieG_spec hz CMain.nu20 _) fun ts hts ↦
      hs_mono (muxG_spec _ _ _) fun w hw ↦ ?_
  have t1 : ((lows.map fun e ↦ (⟨o, e.1.1, e.2⟩ : TC)).map (tval M X CMain.nu20)).sum =
      (r.2.1.map fun t ↦ tval M X CMain.nu20 t.big).sum := by
    rw [List.map_map]
    have : (lows.map ((tval M X CMain.nu20) ∘ fun e ↦ (⟨o, e.1.1, e.2⟩ : TC))) =
        lows.map fun e ↦ kprod X CMain.nu20 e.1.1 * e.2.val M :=
      List.map_congr_left fun e _ ↦ by simp only [Function.comp_apply, tval, ho, one_mul]
    rw [this, hl1, top_val X r.2.1 ZT.pb Prod.fst (fun t ht ↦ (hl t ht).1) fun _ ↦ rfl]
    rfl
  have t2 : ((lows.map fun e ↦ (⟨o, e.1.2, e.2⟩ : TC)).map (tval M X CMain.nu20)).sum =
      (r.2.1.map fun t ↦ tval M X CMain.nu20 t.sml).sum := by
    rw [List.map_map]
    have : (lows.map ((tval M X CMain.nu20) ∘ fun e ↦ (⟨o, e.1.2, e.2⟩ : TC))) =
        lows.map fun e ↦ kprod X CMain.nu20 e.1.2 * e.2.val M :=
      List.map_congr_left fun e _ ↦ by simp only [Function.comp_apply, tval, ho, one_mul]
    rw [this, hl2, top_val X r.2.1 ZT.ps Prod.snd (fun t ht ↦ (hl t ht).2) fun _ ↦ rfl]
    rfl
  rw [hw, htb, hts, List.map_append, List.sum_append, List.map_append, List.sum_append, t1, t2, hb, hsm]

/-! ## The shape cell, the muxed point, the claims -/

/-- **The child's shape cell** `σ' = (1 + d₁₈)(1 + d₁₉)` from `n' − 1`'s bits (the borrow chain's cells). -/
def sigmaG (mb : List Cell) (zc : Cell) : BM Cell := do
  let a ← onePlusG (mb.getD 18 default)
  let b ← onePlusG (mb.getD 19 default)
  mulAdd .E a b zc

theorem sigmaG_spec {mb : List Cell} {zc : Cell} (hz : zc.val M = 0) :
    Hs c M (sigmaG mb zc) (fun r ↦ r.val M = (1 + (mb.getD 18 default).val M) * (1 + (mb.getD 19 default).val M)) :=
  hs_bind (onePlusG_spec _) fun a ha ↦ hs_bind (onePlusG_spec _) fun b hb ↦
    hs_mono (hs_mulAdd _ _ _ _) fun r hr ↦ by rw [hr, ha, hb, hz, add_zero]

theorem muxG_ty (s a b : Cell) (p : Ptr) : (muxG s a b p).1.ty = .E := rfl

/-- **The muxed terminal point** `x^σ_i = mux(σ, x_i, x_{(i+1) mod ν})` (the point in `E` cells `xb + i`). -/
def muxPtG (s : Cell) (xb : ℕ) : List ℕ → BM (List Cell)
  | [] => pure []
  | i :: is => do
    let m ← muxG s (ec (xb + i)) (ec (xb + (i + 1) % CMain.nu20))
    let r ← muxPtG s xb is
    pure (m :: r)

theorem muxPtG_spec (s : Cell) (xb : ℕ) : ∀ is : List ℕ, Hs c M (muxPtG s xb is) (fun r ↦ r.length = is.length ∧
    (∀ x ∈ r, x.ty = .E) ∧ ∀ j < is.length, (r.getD j default).val M =
      mux (s.val M) (M.e (xb + is.getD j 0)) (M.e (xb + (is.getD j 0 + 1) % CMain.nu20)))
  | [] => hs_pure ⟨rfl, by simp, by simp⟩
  | i :: is => by
    unfold muxPtG
    refine hs_bind (hs_and (muxG_spec _ _ _) (show Hs c M (muxG s (ec (xb + i)) (ec (xb + (i + 1) % CMain.nu20)))
        (fun r ↦ r.ty = .E) from fun p _ ↦ muxG_ty _ _ _ p))
      fun m ⟨hm, hmE⟩ ↦ hs_bind (muxPtG_spec s xb is) fun r ⟨hl, hE, hv⟩ ↦ hs_pure ⟨by simp [hl], ?_, ?_⟩
    · intro x hx
      rcases List.mem_cons.mp hx with rfl | hx
      · exact hmE
      · exact hE x hx
    · intro j hj
      rcases j with _ | j
      · simpa using hm
      · simpa using hv j (by simpa using hj)

/-- The claims in both shapes, related one by one (`ZRel`). -/
theorem zClaimsG_spec {s z o : Cell} (hz : z.val M = 0) (ho : o.val M = 1) :
    ∀ cl : List CClaim, (∀ cc ∈ cl, ZWF z cc = true) →
      Hs c M (zClaimsG s z o cl) (fun r ↦ List.Forall₂ (ZRel M s) cl r)
  | [], _ => hs_pure List.Forall₂.nil
  | cc :: cl, h => by
    unfold zClaimsG
    exact hs_bind (zClaimG_spec hz ho cc (h cc List.mem_cons_self)) fun r hr ↦
      hs_bind (zClaimsG_spec hz ho cl fun c' hc' ↦ h c' (List.mem_cons_of_mem _ hc')) fun rs hrs ↦
        hs_pure (List.Forall₂.cons hr hrs)

end Lvm.QShape
