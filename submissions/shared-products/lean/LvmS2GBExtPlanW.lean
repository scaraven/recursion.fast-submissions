-- New for lvm2 MP-B cap pruning (CAP-X6, 2026-11-17): S2GB's plan facts (`tlvFacts_B20`, the heap levels' sums) by
-- one walk over the plan (one kernel evaluation of the plan, no re-walks).
import LvmS2GBExtNodeTlv

/-!
# S2GB's plan facts by one walk

* `tlvW`: one pass over a plan, carrying the entry index, the number of upcoming entries that must have 64-byte
  queries, and the sums of `bmOf`, `tlvTW` and `tlvCW`;
* `tlvW_facts`: for any list, an accepting walk gives the length, `tlvChkL` and the three sums;
* **`tlvFacts_B20`**: at S2GB's plan (4,134 entries), and the levels' bitmaps take at most 512 words;
* `planW_B20`: the plan's heap levels at `P20B` (512 layer nodes, 250 paths, 3 levels).
-/

set_option autoImplicit false

namespace Lvm.XB

open RecursionFast Lvm Lvm.X Lvm.XS Lvm.Replay

/-- A plan entry's paths at an opening's first heap entry. -/
def tlvTW (e : PE) : ℕ :=
  match e.k with
  | .heap _ _ t _ _ m k _ => if k + 1 = 2 ^ m then t else 0
  | _ => 0

/-- A plan entry's levels (one at an opening's first heap entry). -/
def tlvCW (e : PE) : ℕ :=
  match e.k with
  | .heap _ _ _ _ _ m k _ => if k + 1 = 2 ^ m then 1 else 0
  | _ => 0

/-- `tlvEntOK`'s conditions at an opening's first heap entry, but the 64-byte window. -/
def tlvLoc (nP i pe h t path m : ℕ) : Bool :=
  decide (1 ≤ m) && decide (m ≤ 64) && decide (path + m = h) && decide (1 ≤ i) &&
    (List.range t).all (fun j => decide (1 ≤ pe + j / 8) && decide (pe + j / 8 < nP) &&
      decide (j % 8 * h + path + m ≤ 192)) &&
    decide (i + 2 ^ (m - 1) ≤ nP)

/-- One walk over the entries from index `i`: `n` upcoming entries must have 64-byte queries; `sM`, `sT`, `sC` are
the sums so far; at the end the index is `nP` and the sums are `fM`, `fT`, `fC`. -/
def tlvW (nP fM fT fC : ℕ) : ℕ → ℕ → ℕ → ℕ → ℕ → List PE → Bool
  | i, _, sM, sT, sC, [] => i == nP && sM == fM && sT == fT && sC == fC
  | i, n, sM, sT, sC, e :: Q =>
    match e.k with
    | .heap pe h t path _ m k _ =>
      if k + 1 = 2 ^ m then
        tlvLoc nP i pe h t path m && e.len == 64 &&
          tlvW nP fM fT fC (i + 1) (max n (2 ^ (m - 1)) - 1) (sM + 2 ^ m) (sT + t) (sC + 1) Q
      else (n == 0 || e.len == 64) && tlvW nP fM fT fC (i + 1) (n - 1) sM sT sC Q
    | _ => (n == 0 || e.len == 64) && tlvW nP fM fT fC (i + 1) (n - 1) sM sT sC Q

theorem all64_take_mono {L : List PE} {a b : ℕ} (hab : a ≤ b)
    (h : (L.take b).all (fun e => e.len == 64) = true) : (L.take a).all (fun e => e.len == 64) = true := by
  rw [List.all_eq_true] at h ⊢
  intro x hx
  apply h x
  have e : L.take a = (L.take b).take a := by rw [List.take_take, Nat.min_eq_left hab]
  rw [e] at hx
  exact List.mem_of_mem_take hx

theorem all64_take_cons {e : PE} {Q : List PE} {n : ℕ} (he : e.len = 64)
    (h : (Q.take (n - 1)).all (fun e => e.len == 64) = true) : ((e :: Q).take n).all (fun e => e.len == 64) = true := by
  cases n with
  | zero => rfl
  | succ n => simpa [List.take_succ_cons, he] using h

theorem tlvEntOK_open (P : List PE) (nP i pe h t path i0 m k : ℕ) (cap : Option (ℕ × ℕ × ℕ)) (len : ℕ)
    (hk : k + 1 = 2 ^ m) : tlvEntOK P nP i ⟨.heap pe h t path i0 m k cap, len⟩ =
      (tlvLoc nP i pe h t path m && ((P.drop i).take (2 ^ (m - 1))).all (fun e' => e'.len == 64)) := by
  simp only [tlvEntOK, tlvLoc, hk, ite_true]

/-- **The walk's invariant** over the suffix `Q = P.drop i`. -/
theorem tlvW_sound (P : List PE) (nP fM fT fC : ℕ) : ∀ (Q : List PE) (i n sM sT sC : ℕ), P.drop i = Q →
    tlvW nP fM fT fC i n sM sT sC Q = true →
    i + Q.length = nP ∧ tlvChkL P nP i Q = true ∧ (Q.take n).all (fun e => e.len == 64) = true ∧
      sM + (Q.map bmOf).sum = fM ∧ sT + (Q.map tlvTW).sum = fT ∧ sC + (Q.map tlvCW).sum = fC
  | [], i, n, sM, sT, sC, _, hw => by
    simp only [tlvW, Bool.and_eq_true, beq_iff_eq] at hw
    obtain ⟨⟨⟨h1, h2⟩, h3⟩, h4⟩ := hw
    simp [tlvChkL, h1, h2, h3, h4]
  | ⟨kk, len⟩ :: Q, i, n, sM, sT, sC, hd, hw => by
    have hd' : P.drop (i + 1) = Q := by
      rw [← List.drop_drop, hd]; rfl
    cases kk
    case heap pe h t path i0 m k cap =>
      by_cases hk : k + 1 = 2 ^ m
      · simp only [tlvW, hk, ite_true, Bool.and_eq_true, beq_iff_eq] at hw
        obtain ⟨⟨hl, hlen⟩, hr⟩ := hw
        obtain ⟨e1, e2, e3, e4, e5, e6⟩ := tlvW_sound P nP fM fT fC Q _ _ _ _ _ hd' hr
        have hm : 1 ≤ m := by
          simp only [tlvLoc, Bool.and_eq_true, decide_eq_true_eq] at hl
          exact hl.1.1.1.1.1
        have hp : 1 ≤ 2 ^ (m - 1) := Nat.one_le_two_pow
        refine ⟨by simp only [List.length_cons]; omega, ?_, ?_, ?_, ?_, ?_⟩
        · simp only [tlvChkL, Bool.and_eq_true]
          refine ⟨?_, e2⟩
          rw [tlvEntOK_open P nP i pe h t path i0 m k cap len hk, hl, Bool.true_and, hd]
          exact all64_take_cons hlen (all64_take_mono (by omega) e3)
        · exact all64_take_cons hlen (all64_take_mono (by omega) e3)
        · simp only [List.map_cons, List.sum_cons, bmOf, hk, ite_true]; omega
        · simp only [List.map_cons, List.sum_cons, tlvTW, hk, ite_true]; omega
        · simp only [List.map_cons, List.sum_cons, tlvCW, hk, ite_true]; omega
      · simp only [tlvW, hk, ite_false, Bool.and_eq_true] at hw
        obtain ⟨hn, hr⟩ := hw
        obtain ⟨e1, e2, e3, e4, e5, e6⟩ := tlvW_sound P nP fM fT fC Q _ _ _ _ _ hd' hr
        refine ⟨by simp only [List.length_cons]; omega, ?_, ?_, ?_, ?_, ?_⟩
        · simp only [tlvChkL, Bool.and_eq_true]
          exact ⟨by simp only [tlvEntOK, hk, ite_false], e2⟩
        · cases n with
          | zero => rfl
          | succ n =>
            simp only [Bool.or_eq_true, beq_iff_eq, Nat.add_one_ne_zero, false_or] at hn
            exact all64_take_cons hn e3
        · simp only [List.map_cons, List.sum_cons, bmOf, hk, ite_false]; omega
        · simp only [List.map_cons, List.sum_cons, tlvTW, hk, ite_false]; omega
        · simp only [List.map_cons, List.sum_cons, tlvCW, hk, ite_false]; omega
    all_goals
      simp only [tlvW, Bool.and_eq_true] at hw
      obtain ⟨hn, hr⟩ := hw
      obtain ⟨e1, e2, e3, e4, e5, e6⟩ := tlvW_sound P nP fM fT fC Q _ _ _ _ _ hd' hr
      refine ⟨by simp only [List.length_cons]; omega, ?_, ?_, ?_, ?_, ?_⟩
      · simp only [tlvChkL, Bool.and_eq_true]
        exact ⟨by simp only [tlvEntOK], e2⟩
      · cases n with
        | zero => rfl
        | succ n =>
          simp only [Bool.or_eq_true, beq_iff_eq, Nat.add_one_ne_zero, false_or] at hn
          exact all64_take_cons hn e3
      · simp only [List.map_cons, List.sum_cons, bmOf]; omega
      · simp only [List.map_cons, List.sum_cons, tlvTW]; omega
      · simp only [List.map_cons, List.sum_cons, tlvCW]; omega

/-- An accepting walk from the start: the plan's length, `tlvChkL`, and the three sums. -/
theorem tlvW_facts (P : List PE) (nP fM fT fC : ℕ) (h : tlvW nP fM fT fC 0 0 0 0 0 P = true) :
    P.length = nP ∧ tlvChkL P nP 0 P = true ∧ (P.map bmOf).sum = fM ∧ (P.map tlvTW).sum = fT ∧
      (P.map tlvCW).sum = fC := by
  obtain ⟨h1, h2, -, h4, h5, h6⟩ := tlvW_sound P nP fM fT fC P 0 0 0 0 0 List.drop_zero h
  exact ⟨by simpa using h1, h2, by simpa using h4, by simpa using h5, by simpa using h6⟩

/-- S2GB's plan walk accepts (one kernel evaluation of the plan). -/
theorem tlvWalk_B20 : tlvW 4134 512 250 3 0 0 0 0 0 (plan P20B) = true := by
  decide +kernel

/-- **The plan's heap levels at `P20B`**: 512 layer nodes, 250 paths, 3 levels (and the plan facts). -/
theorem planW_B20 : (plan P20B).length = 4134 ∧ tlvChkL (plan P20B) 4134 0 (plan P20B) = true ∧
    ((plan P20B).map bmOf).sum = 512 ∧ ((plan P20B).map tlvTW).sum = 250 ∧ ((plan P20B).map tlvCW).sum = 3 :=
  tlvW_facts (plan P20B) 4134 512 250 3 tlvWalk_B20

/-- **S2GB's plan meets the tail data's conditions** (one kernel evaluation, linear in the plan). -/
theorem tlvFactsL_B20 : (plan P20B).length = 4134 ∧ tlvChkL (plan P20B) 4134 0 (plan P20B) = true ∧
    ((plan P20B).map bmOf).sum ≤ 512 :=
  ⟨planW_B20.1, planW_B20.2.1, Nat.le_of_eq planW_B20.2.2.1⟩

/-- **S2GB's plan meets the tail data's conditions.** -/
theorem tlvFacts_B20 : (plan P20B).length = 4134 ∧
    (∀ q ∈ (List.range (plan P20B).length).map (fun i => (i, (plan P20B).getD i default)),
      tlvEntOK (plan P20B) 4134 q.1 q.2 = true) ∧
    (((List.range (plan P20B).length).map (fun i => (i, (plan P20B).getD i default))).map
      fun q => bmOf q.2).sum ≤ 512 := by
  obtain ⟨h0, h1, h2⟩ := tlvFactsL_B20
  have e : (List.range (plan P20B).length).map (fun i => (i, (plan P20B).getD i default)) = idxL 0 (plan P20B) := by
    rw [← idxL_eq]; simp only [Nat.zero_add]
  rw [e]
  refine ⟨h0, fun q hq => tlvChkL_mem _ _ 0 _ h1 q hq, ?_⟩
  rw [show (fun q : ℕ × PE => bmOf q.2) = bmOf ∘ Prod.snd from rfl, ← List.map_map, idxL_snd]
  exact h2

end Lvm.XB
