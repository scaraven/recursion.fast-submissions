-- New for lvm2 MP-B cap pruning (CAP-X4, 2026-11-17): the extractor's π tail words are the packed bytes of the
-- specification's π tail `tailB` (proof-help of `EXB_node`).
import LvmS2GBExtPlanW
import LvmQLinkBridge
import LvmXSOutW

/-!
# The π tail: the extractor's words against `tailB`

* `tailWs R ls`: the words `tailIR` outputs after `bmIR` from a memory `R` (per level, per uncovered node `x`
  ascending, the 4 words of its half);
* **`tailB_B20`**: with the stream's lanes at `sgB` (`R (sgB + u) = W u`), `tailB P20B (readTraceLS stB20 W)` is the
  bytes of `tailWs R tlvB20`.
-/

set_option autoImplicit false

namespace Lvm.XB

open RecursionFast Lvm Lvm.X Lvm.XS Lvm.Replay

/-- **The tail words** read from the memory `R` (`tailIR` after `bmIR`). -/
def tailWs (R : ℕ → Word) (ls : List TLv) : List Word :=
  ls.flatMap fun l => (List.range (2 ^ l.m)).flatMap fun x =>
    if covW R l x then [] else (List.range 4).map fun k => R (l.heap.getD (x / 2) 0 + 4 * (x % 2) + k)

/-- The uncovered nodes of the levels. -/
def uncW (R : ℕ → Word) (ls : List TLv) : ℕ :=
  (ls.map fun l => ((List.range (2 ^ l.m)).filter fun x => !covW R l x).length).sum

theorem length_tailWs (R : ℕ → Word) (ls : List TLv) : (tailWs R ls).length = 4 * uncW R ls := by
  induction ls with
  | nil => rfl
  | cons l ls ih =>
    simp only [tailWs, uncW, List.flatMap_cons, List.length_append, List.map_cons, List.sum_cons] at ih ⊢
    rw [ih, Nat.mul_add]
    congr 1
    generalize List.range (2 ^ l.m) = xs
    induction xs with
    | nil => rfl
    | cons x xs ih' =>
      simp only [List.flatMap_cons, List.length_append, List.filter_cons]
      split_ifs with h <;> simp_all <;> omega

theorem uncW_le (R : ℕ → Word) : ∀ (ls : List TLv) (b : ℕ), uncW R ls + b ≤ bmEnd b ls
  | [], b => by simp [uncW, bmEnd]
  | l :: ls, b => by
    have ih := uncW_le R ls (b + 2 ^ l.m)
    have hf : ((List.range (2 ^ l.m)).filter fun x => !covW R l x).length ≤ 2 ^ l.m :=
      (List.length_filter_le _ _).trans (by simp)
    simp only [uncW, bmEnd, List.map_cons, List.sum_cons] at ih ⊢
    omega

theorem cntZ_eq (R : ℕ → Word) : ∀ (n b : ℕ), cntZ R b n = ((List.range' b n).filter fun a => R a == 0).length
  | 0, _ => rfl
  | n + 1, b => by
    rw [cntZ, cntZ_eq R n (b + 1), List.range'_succ, List.filter_cons]
    by_cases h : R b = 0#64
    · simp [h, Nat.add_comm]
    · simp [h]

/-- **The count of a bitmap**: the cells `1` at the covered nodes, `0` elsewhere. -/
theorem cntZ_bitmap (R R0 : ℕ → Word) (l : TLv)
    (h : ∀ x < 2 ^ l.m, R (l.bm + x) = if covW R0 l x then 1 else 0) :
    cntZ R l.bm (2 ^ l.m) = ((List.range (2 ^ l.m)).filter fun x => !covW R0 l x).length := by
  rw [cntZ_eq, List.range'_eq_map_range, List.filter_map, List.length_map]
  congr 1
  exact List.filter_congr fun x hx => by
    simp only [Function.comp_apply]
    rw [h x (List.mem_range.1 hx)]
    cases covW R0 l x <;> decide

/-! ## Bits of an answer -/

theorem wordsBytes_flatMap {α : Type} (L : List α) (g : α → List Word) :
    wordsBytes (L.flatMap g) = L.flatMap fun a => wordsBytes (g a) := by
  unfold wordsBytes; rw [List.flatMap_assoc]

theorem answerBits_digW {ws : List Word} (h : ws.length = 4) :
    answerBits (digW ws) = (ws.getD 0 0).toNat + 2 ^ 64 * (ws.getD 1 0).toNat + 2 ^ 128 * (ws.getD 2 0).toNat := by
  have ha := digW_toList h
  simp only [answerBits]
  rw [show (0 : ℕ) = 8 * 0 from rfl, Lvm.QLink.u64At_digest h ha (by norm_num), show (8 : ℕ) = 8 * 1 from rfl,
    Lvm.QLink.u64At_digest h ha (by norm_num), show (16 : ℕ) = 8 * 2 from rfl,
    Lvm.QLink.u64At_digest h ha (by norm_num)]

/-- **An `m`-bit field of three words** at bit `s` is `fldW` of the words holding it. -/
theorem shr_three (f : ℕ → Word) (s m : ℕ) (hm : m ≤ 64) (hs : s + m ≤ 192) :
    (((f 0).toNat + 2 ^ 64 * (f 1).toNat + 2 ^ 128 * (f 2).toNat) >>> s) % 2 ^ m =
      fldW (f (s / 64)) (f (s / 64 + 1)) (s % 64) m := by
  apply Nat.eq_of_testBit_eq; intro t
  rw [fldW, Nat.testBit_mod_two_pow, Nat.testBit_mod_two_pow, Nat.testBit_shiftRight, Nat.testBit_shiftRight,
    Lvm.QLink.testBit_three _ _ _ (f 0).isLt (f 1).isLt,
    show (f (s / 64)).toNat + 2 ^ 64 * (f (s / 64 + 1)).toNat = 2 ^ 64 * (f (s / 64 + 1)).toNat + (f (s / 64)).toNat
      by ring, Nat.testBit_two_pow_mul_add _ (f (s / 64)).isLt]
  by_cases ht : t < m
  · simp only [ht, decide_true, Bool.true_and]
    have hq : s / 64 = 0 ∨ s / 64 = 1 ∨ s / 64 = 2 := by omega
    rcases hq with hq | hq | hq
    · rw [hq, show s % 64 = s by omega]
      by_cases h1 : s + t < 64
      · rw [if_pos h1, if_pos h1]
      · rw [if_neg h1, if_neg h1, if_pos (by omega)]
    · rw [hq]
      by_cases h1 : s % 64 + t < 64
      · rw [if_pos h1, if_neg (by omega), if_pos (by omega), show s + t - 64 = s % 64 + t by omega]
      · rw [if_neg h1, if_neg (by omega), if_neg (by omega), show s + t - 128 = s % 64 + t - 64 by omega]
    · rw [hq, if_pos (show s % 64 + t < 64 by omega), if_neg (by omega), if_neg (by omega),
        show s + t - 128 = s % 64 + t by omega]
  · simp [ht]

/-! ## The trace's entries -/

theorem getD_readTraceLS (st : XStage) (W : ℕ → Word) {e : ℕ} (h1 : 1 ≤ e) (h2 : e ≤ (entLS st).length) :
    (readTraceLS st W).getD e dflt = entAt W (laneE st e).1 (laneE st e).2 := by
  obtain ⟨e', rfl⟩ : ∃ e', e = e' + 1 := ⟨e - 1, by omega⟩
  have h : e' < (entLS st).length := by omega
  simp only [readTraceLS, laneE, Nat.add_sub_cancel, List.getD_cons_succ]
  rw [List.getD_eq_getElem _ _ (by simpa using h), List.getElem_map, List.getD_eq_getElem _ _ h]

theorem getD_wsAt (W : ℕ → Word) (b : ℕ) {n k : ℕ} (hk : k < n) : (wsAt W b n).getD k 0 = W (b + k) := by
  rw [wsAt, List.getD_eq_getElem _ _ (by simpa using hk), List.getElem_map, List.getElem_range]

/-- **A field of a trace entry's answer** is `fldW` of the stream's lanes holding it. -/
theorem field_readTraceLS (st : XStage) (W : ℕ → Word) {e : ℕ} (h1 : 1 ≤ e) (h2 : e ≤ (entLS st).length)
    (s m : ℕ) (hm : m ≤ 64) (hs : s + m ≤ 192) :
    (answerBits (aOf (readTraceLS st W) e) >>> s) % 2 ^ m =
      fldW (W ((laneE st e).1 + 1 + (laneE st e).2 / 8 + s / 64))
        (W ((laneE st e).1 + 1 + (laneE st e).2 / 8 + (s / 64 + 1))) (s % 64) m := by
  rw [aOf, getD_readTraceLS st W h1 h2, entAt]
  dsimp only
  rw [answerBits_digW (length_wsAt _ _ _), getD_wsAt _ _ (by norm_num), getD_wsAt _ _ (by norm_num),
    getD_wsAt _ _ (by norm_num)]
  exact shr_three (fun k => W ((laneE st e).1 + 1 + (laneE st e).2 / 8 + k)) s m hm hs

theorem bl_bArr (l : List UInt8) : bl (bArr l) = l := by simp [bl, bArr]

theorem halfB_readTraceLS (st : XStage) (W : ℕ → Word) {e : ℕ} (h1 : 1 ≤ e) (h2 : e ≤ (entLS st).length)
    (h64 : (laneE st e).2 = 64) {b : ℕ} (hb : b < 2) :
    halfB (readTraceLS st W) e b = wordsBytes ((List.range 4).map fun k => W ((laneE st e).1 + 1 + 4 * b + k)) := by
  have e8 : wsAt W ((laneE st e).1 + 1) 8 = wsAt W ((laneE st e).1 + 1) 4 ++ wsAt W ((laneE st e).1 + 1 + 4) 4 :=
    wsAt_add W _ 4 4
  rw [halfB, qOf, getD_readTraceLS st W h1 h2, entAt, h64, show 64 / 8 = 8 from rfl, bl_bArr, e8, wordsBytes_append]
  have hl : (wordsBytes (wsAt W ((laneE st e).1 + 1) 4)).length = 32 := by rw [wordsBytes_length, length_wsAt]
  rcases (by omega : b = 0 ∨ b = 1) with rfl | rfl
  · rw [if_pos rfl, List.take_left' hl]; simp [wsAt]
  · rw [if_neg (by decide), List.drop_left' hl]; simp [wsAt, Nat.add_assoc]

/-! ## The plan's lengths and the entry lanes -/

theorem planS_lens (st : XStage) (hP : (planItems st.p w0 st.items).2.ok = true) :
    (planS st).map PE.len = 7 :: lensLS st := by
  rw [show planS st = ⟨.q0, 7⟩ :: ⟨.fs 0, seedLenP st.p⟩ :: (planItems st.p w0 st.items).1 from rfl,
    List.map_cons, List.map_cons, plan_lens _ _ _ hP, lensLS,
    show blocksS st = .one .seed (seedLenP st.p) :: itemBlks st.p st.items 0 from rfl, List.flatMap_cons]
  rfl

theorem planLens_B20 : (plan P20B).map PE.len = 7 :: lensLS stB20 := planS_lens stB20 outOK_stB20.planOk

theorem length_entLS_B20 : (entLS stB20).length + 1 = (plan P20B).length := by
  have h := congrArg List.length planLens_B20
  rw [List.length_map, List.length_cons] at h
  have hw := congrArg List.length (walk_snd 6 (lensLS stB20))
  rw [List.length_map] at hw
  rw [h, entLS, hw]

/-- `getD` through `map` with the image default (no bound, no `getElem` proof). -/
private theorem getD_mapD {α β : Type} (f : α → β) (l : List α) (d : α) (n : ℕ) :
    (l.map f).getD n (f d) = f (l.getD n d) := by
  simp

/- The proof stays in `getD` form: a `getElem` bound proof on `plan P20B` makes the kernel evaluate the plan
(~22 M hb). -/
theorem laneE_len {e : ℕ} (h1 : 1 ≤ e) (h2 : e < (plan P20B).length) :
    (laneE stB20 e).2 = ((plan P20B).getD e default).len := by
  obtain ⟨e', rfl⟩ : ∃ e', e = e' + 1 := ⟨e - 1, by omega⟩
  rw [← getD_mapD PE.len, planLens_B20, laneE, Nat.add_sub_cancel, ← getD_mapD Prod.snd, entLS, walk_snd]
  rfl

theorem laneE_bound {e : ℕ} (h1 : 1 ≤ e) (h2 : e ≤ (entLS stB20).length) :
    (laneE stB20 e).1 + 5 + (laneE stB20 e).2 / 8 ≤ nCp := by
  have hmem : laneE stB20 e ∈ entLS stB20 := by
    rw [laneE, List.getD_eq_getElem _ _ (by omega)]; exact List.getElem_mem _
  have := (walk_lt 6 (lensLS stB20) _ hmem).2
  have h3 : lanesOf (lensLS stB20) = ((blocksS stB20).map Blk.lanes).sum := lanesOf_flatMapB _
  have hL := outOK_stB20.lanes
  omega

/-! ## One level -/

/-- A level's memory words are the copied stream's. -/
def LvOK (l : TLv) : Prop :=
  1 ≤ l.m ∧ l.m ≤ 64 ∧ (∀ p ∈ l.pos, sgB ≤ p.1 ∧ p.1 + 1 < sgB + nCp ∧ p.2 < 64) ∧
    l.heap.length = 2 ^ (l.m - 1) ∧ ∀ q ∈ l.heap, sgB ≤ q ∧ q + 8 ≤ sgB + nCp

theorem two_pow_pred {m : ℕ} (h : 1 ≤ m) : 2 ^ m = 2 * 2 ^ (m - 1) := by
  rw [← Nat.pow_succ']; congr 1; omega

/-- The facts at an opening's first heap entry. -/
theorem tlvEnt_facts {pe h t path i0 m k : ℕ} {cap : Option (ℕ × ℕ × ℕ)} {len i : ℕ}
    (hk : k + 1 = 2 ^ m) (hok : tlvEntOK (plan P20B) 4134 i ⟨.heap pe h t path i0 m k cap, len⟩ = true) :
    1 ≤ m ∧ m ≤ 64 ∧ path + m = h ∧
    (∀ j < t, 1 ≤ pe + j / 8 ∧ pe + j / 8 ≤ (entLS stB20).length ∧ j % 8 * h + path + m ≤ 192) ∧
    ∀ y < 2 ^ (m - 1), 1 ≤ i + 2 ^ (m - 1) - 1 - y ∧ i + 2 ^ (m - 1) - 1 - y ≤ (entLS stB20).length ∧
      (laneE stB20 (i + 2 ^ (m - 1) - 1 - y)).2 = 64 := by
  have hP := tlvFacts_B20.1
  have hE := length_entLS_B20
  simp only [tlvEntOK, if_pos hk, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true, List.mem_range,
    beq_iff_eq] at hok
  obtain ⟨⟨⟨⟨⟨⟨hm1, hm64⟩, hph⟩, hi1⟩, hpos⟩, hiN⟩, htake⟩ := hok
  refine ⟨hm1, hm64, hph, fun j hj => ⟨(hpos j hj).1.1, by have := (hpos j hj).1.2; omega, (hpos j hj).2⟩,
    fun y hy => ⟨by omega, by omega, ?_⟩⟩
  rw [laneE_len (by omega) (by omega)]
  have hy' : 2 ^ (m - 1) - 1 - y < (((plan P20B).drop i).take (2 ^ (m - 1))).length := by
    simp only [List.length_take, List.length_drop]; omega
  have := htake _ (List.getElem_mem hy')
  rw [List.getElem_take, List.getElem_drop] at this
  rw [show i + 2 ^ (m - 1) - 1 - y = i + (2 ^ (m - 1) - 1 - y) by omega, List.getD_eq_getElem _ _ (by omega)]
  exact this

/-- **A level's layout** from the plan's conditions. -/
theorem lvOK_tlvAt {bm i : ℕ} {e : PE} {l : TLv} (h : tlvAt stB20 bm i e = some l)
    (hok : tlvEntOK (plan P20B) 4134 i e = true) : LvOK l ∧ l.bm = bm := by
  rcases e with ⟨k, len⟩
  cases k with
  | heap pe h t path i0 m k cap =>
    by_cases hk : k + 1 = 2 ^ m
    · simp only [tlvAt, if_pos hk, Option.some.injEq] at h
      subst h
      obtain ⟨hm1, hm64, hph, hpos, hheap⟩ := tlvEnt_facts hk hok
      refine ⟨⟨hm1, hm64, fun p hp => ?_, by simp, fun q hq => ?_⟩, rfl⟩
      · obtain ⟨j, hj, rfl⟩ := List.mem_map.1 hp
        have hj' := List.mem_range.1 hj
        obtain ⟨h1, h2, h3⟩ := hpos j hj'
        have := laneE_bound h1 h2
        refine ⟨by omega, ?_, Nat.mod_lt _ (by norm_num)⟩
        have : (j % 8 * h + path) / 64 ≤ 2 := by omega
        omega
      · obtain ⟨y, hy, rfl⟩ := List.mem_map.1 hq
        have hy' := List.mem_range.1 hy
        obtain ⟨h1, h2, h3⟩ := hheap y hy'
        have := laneE_bound h1 h2
        rw [h3] at this
        exact ⟨by omega, by omega⟩
    · simp [tlvAt, if_neg hk] at h
  | q0 => simp [tlvAt] at h
  | fs _ => simp [tlvAt] at h
  | leaf => simp [tlvAt] at h
  | node _ _ _ _ _ => simp [tlvAt] at h

/-- **An opening's first heap entry's tail bytes** are the bytes of its level's tail words. -/
theorem tailEntB_eq (W R : ℕ → Word) (hR : ∀ u < nCp, R (sgB + u) = W u) (bm i : ℕ) (e : PE)
    (hok : tlvEntOK (plan P20B) 4134 i e = true) :
    tailEntB (readTraceLS stB20 W) i e =
      match tlvAt stB20 bm i e with
      | some l => wordsBytes (tailWs R [l])
      | none => [] := by
  rcases e with ⟨k, len⟩
  cases k with
  | heap pe h t path i0 m k cap =>
    by_cases hk : k + 1 = 2 ^ m
    · obtain ⟨hm1, hm64, hph, hpos, hheap⟩ := tlvEnt_facts hk hok
      simp only [tlvAt, tailEntB, if_pos hk]
      rw [tailWs, List.flatMap_singleton, wordsBytes_flatMap]
      refine List.flatMap_congr fun x hx => ?_
      have hx' := List.mem_range.1 hx
      -- the cover
      have hcov : coveredB (readTraceLS stB20 W) pe h t path x =
          covW R ⟨m, bm, (List.range t).map (fun j =>
            (sgB + (laneE stB20 (pe + j / 8)).1 + 1 + (laneE stB20 (pe + j / 8)).2 / 8 + (j % 8 * h + path) / 64,
              (j % 8 * h + path) % 64)),
            (List.range (2 ^ (m - 1))).map fun y => sgB + (laneE stB20 (i + 2 ^ (m - 1) - 1 - y)).1 + 1⟩ x := by
        rw [coveredB, covW, List.any_map]
        refine any_congr' fun j hj => ?_
        have hj' := List.mem_range.1 hj
        obtain ⟨h1, h2, h3⟩ := hpos j hj'
        have hb := laneE_bound h1 h2
        simp only [Function.comp_apply]
        rw [Lvm.QLink.posVal_shift _ _ _ _ _ (by omega), show h - path = m by omega,
          field_readTraceLS stB20 W h1 h2 _ _ hm64 (by omega)]
        have hq : (j % 8 * h + path) / 64 ≤ 2 := by omega
        generalize laneE stB20 (pe + j / 8) = U at hb ⊢
        generalize j % 8 * h + path = s at hq ⊢
        rw [show sgB + U.1 + 1 + U.2 / 8 + s / 64 + 1 = sgB + (U.1 + 1 + U.2 / 8 + (s / 64 + 1)) by omega,
          show sgB + U.1 + 1 + U.2 / 8 + s / 64 = sgB + (U.1 + 1 + U.2 / 8 + s / 64) by omega,
          hR _ (by omega), hR _ (by omega), Bool.eq_iff_iff]
        simp only [beq_iff_eq]
        exact eq_comm
      rw [hcov]
      split_ifs with hc
      · rfl
      · have hy : x / 2 < 2 ^ (m - 1) := by have := two_pow_pred hm1; omega
        obtain ⟨e1, e2, e3⟩ := hheap (x / 2) hy
        have hb := laneE_bound e1 e2
        rw [e3] at hb
        rw [halfB_readTraceLS stB20 W e1 e2 e3 (Nat.mod_lt _ (by norm_num))]
        congr 1
        refine List.map_congr_left fun k hk => ?_
        have hk' := List.mem_range.1 hk
        rw [List.getD_eq_getElem _ _ (by simpa using hy), List.getElem_map, List.getElem_range]
        generalize laneE stB20 (i + 2 ^ (m - 1) - 1 - x / 2) = U at hb ⊢
        have hx2 := Nat.mod_lt x (show 2 > 0 by norm_num)
        rw [show sgB + U.1 + 1 + 4 * (x % 2) + k = sgB + (U.1 + 1 + 4 * (x % 2) + k) by omega, hR _ (by omega)]
    · simp only [tlvAt, tailEntB, if_neg hk]
  | q0 => rfl
  | fs _ => rfl
  | leaf => rfl
  | node _ _ _ _ _ => rfl

/-! ## The levels -/

/-- **The tail over a run of plan entries.** -/
theorem tailB_gen (W R : ℕ → Word) (hR : ∀ u < nCp, R (sgB + u) = W u) :
    ∀ (ps : List (ℕ × PE)) (bm : ℕ), (∀ q ∈ ps, tlvEntOK (plan P20B) 4134 q.1 q.2 = true) →
    ps.flatMap (fun q => tailEntB (readTraceLS stB20 W) q.1 q.2) = wordsBytes (tailWs R (tlvsFrom stB20 bm ps))
  | [], _, _ => rfl
  | (i, e) :: ps, bm, hok => by
    have h0 := tailEntB_eq W R hR bm i e (hok (i, e) List.mem_cons_self)
    rw [List.flatMap_cons]
    simp only [tlvsFrom]
    revert h0
    cases tlvAt stB20 bm i e with
    | none =>
      intro h0
      dsimp only at h0 ⊢
      rw [h0, List.nil_append]
      exact tailB_gen W R hR ps bm fun q hq => hok q (List.mem_cons_of_mem _ hq)
    | some l =>
      intro h0
      dsimp only at h0 ⊢
      rw [h0, tailB_gen W R hR ps (bm + 2 ^ l.m) (fun q hq => hok q (List.mem_cons_of_mem _ hq)),
        ← wordsBytes_append]
      congr 1
      simp only [tailWs, List.flatMap_cons, List.flatMap_nil, List.append_nil]

/-- The levels' layout over a run of plan entries. -/
theorem lvOK_tlvsFrom : ∀ (ps : List (ℕ × PE)) (bm : ℕ), (∀ q ∈ ps, tlvEntOK (plan P20B) 4134 q.1 q.2 = true) →
    (∀ l ∈ tlvsFrom stB20 bm ps, LvOK l) ∧ BmChain bm (tlvsFrom stB20 bm ps) ∧
    bmEnd bm (tlvsFrom stB20 bm ps) ≤ bm + (ps.map fun q => bmOf q.2).sum
  | [], bm, _ => ⟨fun _ h => by simp [tlvsFrom] at h, trivial, by simp [tlvsFrom, bmEnd]⟩
  | (i, e) :: ps, bm, hok => by
    have h0 := hok (i, e) List.mem_cons_self
    simp only [tlvsFrom, List.map_cons, List.sum_cons]
    have hb : bmOf e = match tlvAt stB20 bm i e with | some l => 2 ^ l.m | none => 0 := by
      rcases e with ⟨k, len⟩
      cases k with
      | heap pe h t path i0 m k cap =>
        by_cases hk : k + 1 = 2 ^ m
        · simp [bmOf, tlvAt, if_pos hk]
        · simp [bmOf, tlvAt, if_neg hk]
      | q0 => rfl
      | fs _ => rfl
      | leaf => rfl
      | node _ _ _ _ _ => rfl
    revert hb
    cases hT : tlvAt stB20 bm i e with
    | none =>
      intro hb
      dsimp only at hb ⊢
      obtain ⟨ih1, ih2, ih3⟩ := lvOK_tlvsFrom ps bm fun q hq => hok q (List.mem_cons_of_mem _ hq)
      exact ⟨ih1, ih2, by omega⟩
    | some l =>
      intro hb
      dsimp only at hb ⊢
      obtain ⟨hl, hlb⟩ := lvOK_tlvAt hT h0
      obtain ⟨ih1, ih2, ih3⟩ := lvOK_tlvsFrom ps (bm + 2 ^ l.m) fun q hq => hok q (List.mem_cons_of_mem _ hq)
      refine ⟨fun l' hl' => ?_, ⟨hlb, ih2⟩, ?_⟩
      · rcases List.mem_cons.1 hl' with rfl | hl'
        · exact hl
        · exact ih1 l' hl'
      · show bmEnd (bm + 2 ^ l.m) _ ≤ _
        generalize 2 ^ l.m = P at ih3 hb ⊢
        omega

theorem tlvLay_gen (ps : List (ℕ × PE)) (h : ∀ q ∈ ps, tlvEntOK (plan P20B) 4134 q.1 q.2 = true)
    (h4 : (ps.map fun q => bmOf q.2).sum ≤ 512) :
    (∀ l ∈ tlvsFrom stB20 wB2M ps, LvOK l) ∧ BmChain wB2M (tlvsFrom stB20 wB2M ps) ∧
      bmEnd wB2M (tlvsFrom stB20 wB2M ps) ≤ wB2M + 512 := by
  obtain ⟨h1, h2, h3⟩ := lvOK_tlvsFrom ps wB2M h
  exact ⟨h1, h2, by omega⟩

/-- **S2GB's tail data's layout.** -/
theorem tlvLay_B20 : (∀ l ∈ tlvB20, LvOK l) ∧ BmChain wB2M tlvB20 ∧ bmEnd wB2M tlvB20 ≤ wB2M + 512 := by
  have h := tlvLay_gen _ tlvFacts_B20.2.1 tlvFacts_B20.2.2
  rw [tlvB20]
  exact h

theorem tailB_eq_idx (p : Params) (tr : Trace) :
    tailB p tr = ((List.range (plan p).length).map fun i => (i, (plan p).getD i default)).flatMap
      fun q => tailEntB tr q.1 q.2 := by
  rw [tailB, List.flatMap_map]

/-- **S2GB's π tail is the tail words' bytes.** -/
theorem tailB_B20 (W R : ℕ → Word) (hR : ∀ u < nCp, R (sgB + u) = W u) :
    tailB P20B (readTraceLS stB20 W) = wordsBytes (tailWs R tlvB20) := by
  have h := tailB_gen W R hR _ wB2M tlvFacts_B20.2.1
  rw [tailB_eq_idx, tlvB20]
  generalize ((List.range (plan P20B).length).map (fun i => (i, (plan P20B).getD i default))) = ps at h ⊢
  exact h

end Lvm.XB
