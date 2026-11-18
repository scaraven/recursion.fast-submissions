-- New for lvm2 S2GT (GT-C4): the values of blob GT's typed `E2` gadgets (`LvmE2QTypedT`), for the replays of
-- `LvmE2QTypedPhaseT`: `eqDot2`/`eqDot2K` (`Lvm.QAcc.eqDot_spec` at `E2`), Horner, `virtGT = virtD`,
-- `relayKernGT = relayKernD` (roll 11's `LvmQTypedHarR` on the `C2` gadgets, the native steps by `LvmE2TVKernP`).
import LvmE2QHarGen
import LvmE2TVKernF
import LvmE2VDecG

/-!
# The typed `E2` gadgets' values

* `eq_blocks`: `Σ_h eq(hi, h)·Σ_l eq(lo, l)·E(h·2^|lo| + l) = Σ_k eq(lo ‖ hi, k)·E(k)` (the two half tables);
* **`hs_eqDot2`**, **`hs_eqDot2K`**: `eqDot2`/`eqDot2K` are `Σ_k eq(r, k)·e_k` (`E2` entries / `K` cells);
* `hs_horner2`, **`hs_powSum2`**: `Σ_k γ^k·d_k`;
* `pubG_hdrLanesT`: S2GT's child `PUB` lanes are the stream's from lane `11`, the key's from `vk`.
-/

set_option autoImplicit false

namespace Lvm.E2Q

open Lvm Lvm.Loop Lvm.Loop.Build Lvm.Har Lvm.Q2 Lvm.QTyped Lvm.QShape
open Finset (range)

/-! ## Sums by blocks -/

theorem sum_blocks2 (f : Nat → FE2) (B : Nat) : ∀ n : Nat,
    ∑ k ∈ range (n * B), f k = ∑ h ∈ range n, ∑ l ∈ range B, f (h * B + l)
  | 0 => by simp
  | n + 1 => by rw [Nat.succ_mul, Finset.sum_range_add, sum_blocks2 f B n, Finset.sum_range_succ]

theorem blocks_len (len B : Nat) (hB : 0 < B) : len ≤ (len + B - 1) / B * B := by
  have h1 := Nat.div_add_mod (len + B - 1) B
  have h2 := Nat.mod_lt (len + B - 1) hB
  rw [mul_comm]; (clear * - hB h1 h2; omega)

theorem blocks_lt {len B H : Nat} (hB : 0 < B) (hn : len ≤ B * H) {h : Nat} (hh : h < (len + B - 1) / B) : h < H := by
  have h1 : (h + 1) * B ≤ len + B - 1 := (Nat.le_div_iff_mul_le hB).mp (by (clear * - hh; omega))
  have h2 : h * B < H * B := by rw [Nat.succ_mul] at h1; rw [Nat.mul_comm H B]; (clear * - hn hB h1; omega)
  exact Nat.lt_of_mul_lt_mul_right h2

/-- **The two half tables**: `Σ_h eq(hi, h)·Σ_l eq(lo, l)·E(h·2^|lo| + l)` over the blocks is `Σ_k eq(lo ‖ hi, k)·E(k)`
(`E` zero from `len`). -/
theorem eq_blocks (E : Nat → FE2) (lo hi : List FE2) (len : Nat) (hE : ∀ k, len ≤ k → E k = 0) :
    ∑ h ∈ range ((len + 2 ^ lo.length - 1) / 2 ^ lo.length), E2V.eqAtF hi h *
      ∑ l ∈ range (2 ^ lo.length), E2V.eqAtF lo l * E (h * 2 ^ lo.length + l) =
    ∑ k ∈ range len, E2V.eqAtF (lo ++ hi) k * E k := by
  have hB0 : 0 < 2 ^ lo.length := by positivity
  obtain ⟨m, hm⟩ : ∃ m, (len + 2 ^ lo.length - 1) / 2 ^ lo.length * 2 ^ lo.length = len + m :=
    ⟨_, (Nat.add_sub_cancel' (blocks_len len _ hB0)).symm⟩
  have e : ∑ k ∈ range len, E2V.eqAtF (lo ++ hi) k * E k =
      ∑ k ∈ range ((len + 2 ^ lo.length - 1) / 2 ^ lo.length * 2 ^ lo.length), E2V.eqAtF (lo ++ hi) k * E k := by
    rw [hm, Finset.sum_range_add, Finset.sum_eq_zero (s := range m) fun j _ => by rw [hE _ (by omega), mul_zero],
      add_zero]
  rw [e, sum_blocks2]
  refine Finset.sum_congr rfl fun h _ => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun l hl => ?_
  rw [Finset.mem_range] at hl
  rw [Lvm.eqAtF_append, show (h * 2 ^ lo.length + l) % 2 ^ lo.length = l by
      rw [Nat.mul_comm, Nat.mul_add_mod, Nat.mod_eq_of_lt hl],
    show (h * 2 ^ lo.length + l) / 2 ^ lo.length = h by
      rw [Nat.mul_comm, Nat.mul_add_div hB0, Nat.div_eq_of_lt hl, Nat.add_zero]]
  ring

/-! ## `eqDot2`, `eqDot2K` -/

section
variable {c : Ctx} {M : Mem}

theorem fe2_mul_ofK (e : FE2) (k : FK) : e * FE2.ofK k = ⟨e.re * k, e.im * k⟩ :=
  FE2.toE2_injective (by
    rw [FE2.fe2_mul_eq, FE2.toE2_ofK, show (⟨e.re * k, e.im * k⟩ : FE2) = FE2.mulK e k from rfl, FE2.toE2_mulK])

/-- `acc + e·x` (`g2MacK`, `K` operands). -/
theorem hs_g2MacK {acc e : C2} {x : Cell} (hacc : KC2 acc) (he : KC2 e) (hx : x.ty = .K) :
    Hs c M (g2MacK acc e x) (fun r => KC2 r ∧ r.val M = acc.val M + e.val M * FE2.ofK (x.val M).c₀) := by
  unfold g2MacK
  refine hs_bind (hs_and (hs_mulAdd .K _ _ _) (Q := fun x : Cell => x.ty = .K) fun _ _ => rfl) fun r ⟨hr, hrK⟩ =>
    hs_bind (hs_and (hs_mulAdd .K _ _ _) (Q := fun x : Cell => x.ty = .K) fun _ _ => rfl) fun i ⟨hi, hiK⟩ =>
      hs_pure ⟨⟨hrK, hiK⟩, ?_⟩
  rw [fe2_mul_ofK]
  show (⟨(r.val M).c₀, (i.val M).c₀⟩ : FE2) = ⟨(acc.re.val M).c₀ + (e.re.val M).c₀ * (x.val M).c₀,
    (acc.im.val M).c₀ + (e.im.val M).c₀ * (x.val M).c₀⟩
  rw [hr, hi, ← kcell_val he.1, ← kcell_val he.2, ← kcell_val hx, ← kcell_val hacc.1, ← kcell_val hacc.2,
    ← ofK_mul, ← ofK_add, ← ofK_mul, ← ofK_add, add_comm, add_comm (_ * _)]
  rfl

theorem hs_g2DotK : ∀ (acc : C2) (l : List (C2 × Cell)), KC2 acc → (∀ e ∈ l, KC2 e.1 ∧ e.2.ty = .K) →
    Hs c M (g2DotK acc l) (fun r => r.val M = acc.val M + (l.map fun e => e.1.val M * FE2.ofK (e.2.val M).c₀).sum)
  | acc, [], _, _ => hs_pure (by simp)
  | acc, (e, x) :: l, hacc, hl => by
    rw [g2DotK]
    have h0 := hl (e, x) List.mem_cons_self
    refine hs_bind (hs_g2MacK hacc h0.1 h0.2) fun a ⟨haK, ha⟩ =>
      hs_mono (hs_g2DotK a l haK fun e' he' => hl e' (List.mem_cons_of_mem _ he')) fun r hr => ?_
    rw [hr, ha, List.map_cons, List.sum_cons, add_assoc]

/-- The entries of a block (`filterMap` over the optional entries), summed. -/
theorem sum_filterMap_opt {β : Type} (w : Nat → C2) (o : Nat → Option β) (V : C2 × β → FE2) : ∀ B : Nat,
    (((List.range B).filterMap fun l => (o l).map fun e => (w l, e)).map V).sum =
      ∑ l ∈ range B, ((o l).map fun e => V (w l, e)).getD 0
  | 0 => by simp
  | B + 1 => by
    rw [List.range_succ, List.filterMap_append, List.map_append, List.sum_append, sum_filterMap_opt w o V B,
      Finset.sum_range_succ]
    cases h : o B <;> simp [h]

theorem eqTab_kernel {o2 : C2} (ho : o2.val M = 1) {pt t : List C2}
    (ht : t.map (C2.val M) = (pt.map (C2.val M)).foldl eqStep2 ([o2].map (C2.val M))) :
    t.map (C2.val M) = E2V.eqKernelF (pt.map (C2.val M)) := by
  rw [ht, List.map_cons, List.map_nil, ho, eqKernelF_eq]

theorem eqTab_len {o2 : C2} (ho : o2.val M = 1) {pt t : List C2}
    (ht : t.map (C2.val M) = (pt.map (C2.val M)).foldl eqStep2 ([o2].map (C2.val M))) : t.length = 2 ^ pt.length := by
  rw [← List.length_map (f := C2.val M), eqTab_kernel ho ht, E2V.eqKernelF_length, List.length_map]

/-- The `eq` table from `[o2]` is `eqKernelF`, entry for entry. -/
theorem eqTab_getD {o2 : C2} (ho : o2.val M = 1) {pt t : List C2}
    (ht : t.map (C2.val M) = (pt.map (C2.val M)).foldl eqStep2 ([o2].map (C2.val M))) {l : Nat}
    (hl : l < 2 ^ pt.length) : (t.getD l default).val M = E2V.eqAtF (pt.map (C2.val M)) l := by
  rw [c2_getD t (by rw [eqTab_len ho ht]; exact hl), eqTab_kernel ho ht, E2V.eqKernelF_getD, List.length_map,
    if_pos hl]

/-- **`Σ_k eq(r, k)·e_k` at `E2`** (`eqDot2`, the point split at `la`; `Lvm.QAcc.eqDot_spec`'s twin). -/
theorem hs_eqDot2 {z2 o2 : C2} (hz : z2.val M = 0) (ho : o2.val M = 1) (r : List C2) (la : Nat)
    (hla : la ≤ r.length) (es : List C2) (hn : es.length ≤ 2 ^ r.length) :
    Hs c M (eqDot2 z2 o2 r la es) (fun y => y.val M =
      ∑ k ∈ range es.length, E2V.eqAtF (r.map (C2.val M)) k * (es.map (C2.val M)).getD k 0) := by
  unfold eqDot2
  have hlo : (r.take la).length = la := List.length_take_of_le hla
  have hhi : (r.drop la).length = r.length - la := List.length_drop
  refine hs_bind (hs_g2EqTab hz [o2] (r.take la)) fun eL heL =>
    hs_bind (hs_g2EqTab hz [o2] (r.drop la)) fun eH heH => ?_
  dsimp only
  refine hs_bind (hs_mapB _ (fun h => ∑ l ∈ range (2 ^ la), E2V.eqAtF ((r.take la).map (C2.val M)) l *
      (es.map (C2.val M)).getD (h * 2 ^ la + l) 0)
    (fun h => hs_mono (hs_g2Dot z2 _) fun a ha => ?_) _) fun accs haccs => hs_mono (hs_g2Dot z2 _) fun y hy => ?_
  · rw [ha, hz, zero_add, sum_filterMap_opt]
    refine Finset.sum_congr rfl fun l hl => ?_
    rw [Finset.mem_range] at hl
    rw [show (es.map (C2.val M)).getD (h * 2 ^ la + l) 0 = (es[h * 2 ^ la + l]?.map (C2.val M)).getD 0 by
      rw [List.getD_eq_getElem?_getD, List.getElem?_map]]
    cases es[h * 2 ^ la + l]? with
    | none => simp
    | some e => simp only [Option.map_some, Option.getD_some]; rw [eqTab_getD ho heL (by rw [hlo]; exact hl)]
  · have hB0 : 0 < 2 ^ la := by positivity
    have hal : accs.length = (es.length + 2 ^ la - 1) / 2 ^ la := by
      rw [← List.length_map (f := C2.val M), haccs, List.length_map, List.length_range]
    rw [hy, hz, zero_add, List.map_map, Lvm.E2T.kf_list_sum_range]
    have key := eq_blocks (fun k => (es.map (C2.val M)).getD k 0) ((r.take la).map (C2.val M))
      ((r.drop la).map (C2.val M)) es.length (fun k hk => List.getD_eq_default _ _ (by simpa using hk))
    rw [List.length_map, hlo, ← List.map_append, List.take_append_drop] at key
    rw [← key]
    refine Finset.sum_congr rfl fun h hh => ?_
    rw [Finset.mem_range] at hh
    have hH : h < 2 ^ (r.drop la).length := by
      refine blocks_lt hB0 ?_ hh
      rw [hhi, ← pow_add, Nat.add_sub_cancel' hla]; exact hn
    simp only [Function.comp_apply]
    rw [eqTab_getD ho heH hH, c2_getD accs (by rw [hal]; exact hh), haccs,
      List.getD_eq_getElem _ _ (by simpa using hh), List.getElem_map, List.getElem_range]

/-- **`Σ_k eq(r, k)·x_k` for `K` cells** (`eqDot2K`, the point split at `la`). -/
theorem hs_eqDot2K {z2 o2 : C2} (hz : z2.val M = 0) (ho : o2.val M = 1) (hz2K : KC2 z2) (ho2K : KC2 o2)
    (r : List C2) (la : Nat) (hla : la ≤ r.length) (xs : List Cell) (hxK : ∀ x ∈ xs, x.ty = .K)
    (hn : xs.length ≤ 2 ^ r.length) :
    Hs c M (eqDot2K z2 o2 r la xs) (fun y => y.val M =
      ∑ k ∈ range xs.length, E2V.eqAtF (r.map (C2.val M)) k * FE2.ofK ((xs.getD k default).val M).c₀) := by
  unfold eqDot2K
  have hlo : (r.take la).length = la := List.length_take_of_le hla
  have hhi : (r.drop la).length = r.length - la := List.length_drop
  refine hs_bind (hs_and (hs_g2EqTab hz [o2] (r.take la)) (hs_g2EqTab_K z2 [o2] _ (by simpa using ho2K)))
    fun eL ⟨heL, heLK⟩ => hs_bind (hs_g2EqTab hz [o2] (r.drop la)) fun eH heH => ?_
  dsimp only
  have hELK : ∀ l, KC2 (eL.getD l default) ∨ eL.getD l default = default := fun l => by
    rw [List.getD_eq_getElem?_getD]
    cases h : eL[l]? with
    | none => exact Or.inr rfl
    | some e => exact Or.inl (heLK e (List.mem_of_getElem? h))
  refine hs_bind (hs_mapB _ (fun h => ∑ l ∈ range (2 ^ la), E2V.eqAtF ((r.take la).map (C2.val M)) l *
      FE2.ofK ((xs.getD (h * 2 ^ la + l) default).val M).c₀ * (if h * 2 ^ la + l < xs.length then 1 else 0))
    (fun h => hs_mono (hs_g2DotK z2 _ hz2K fun e he => ?_) fun a ha => ?_) _) fun accs haccs =>
      hs_mono (hs_g2Dot z2 _) fun y hy => ?_
  · obtain ⟨l, hl, hle⟩ := List.mem_filterMap.mp he
    rw [List.mem_range] at hl
    rcases hx : xs[h * 2 ^ la + l]? with _ | x
    · simp [hx] at hle
    · simp only [hx, Option.map_some, Option.some.injEq] at hle
      subst hle
      refine ⟨?_, hxK x (List.mem_of_getElem? hx)⟩
      rcases hELK l with h1 | h1
      · exact h1
      · have hlt : l < eL.length := by rw [eqTab_len ho heL, hlo]; exact hl
        exact heLK _ (List.getD_eq_getElem _ _ hlt ▸ List.getElem_mem hlt)
  · rw [ha, hz, zero_add, sum_filterMap_opt]
    refine Finset.sum_congr rfl fun l hl => ?_
    rw [Finset.mem_range] at hl
    rcases hx : xs[h * 2 ^ la + l]? with _ | x
    · have : ¬ h * 2 ^ la + l < xs.length := fun h' => by simp [List.getElem?_eq_getElem h'] at hx
      simp [this]
    · have h' : h * 2 ^ la + l < xs.length := (List.getElem?_eq_some_iff.mp hx).1
      simp only [Option.map_some, Option.getD_some, if_pos h', mul_one]
      rw [eqTab_getD ho heL (by rw [hlo]; exact hl), List.getD_eq_getElem?_getD, hx, Option.getD_some]
  · have hB0 : 0 < 2 ^ la := by positivity
    have hal : accs.length = (xs.length + 2 ^ la - 1) / 2 ^ la := by
      rw [← List.length_map (f := C2.val M), haccs, List.length_map, List.length_range]
    rw [hy, hz, zero_add, List.map_map, Lvm.E2T.kf_list_sum_range]
    have key := eq_blocks (fun k => FE2.ofK ((xs.getD k default).val M).c₀ * if k < xs.length then 1 else 0)
      ((r.take la).map (C2.val M)) ((r.drop la).map (C2.val M)) xs.length
      (fun k hk => by rw [if_neg (by omega), mul_zero])
    rw [List.length_map, hlo, ← List.map_append, List.take_append_drop] at key
    have e2 : ∑ k ∈ range xs.length, E2V.eqAtF (r.map (C2.val M)) k * FE2.ofK ((xs.getD k default).val M).c₀ =
        ∑ k ∈ range xs.length, E2V.eqAtF (r.map (C2.val M)) k *
          (FE2.ofK ((xs.getD k default).val M).c₀ * if k < xs.length then 1 else 0) :=
      Finset.sum_congr rfl fun k hk => by rw [if_pos (Finset.mem_range.mp hk), mul_one]
    rw [e2, ← key]
    refine Finset.sum_congr rfl fun h hh => ?_
    rw [Finset.mem_range] at hh
    have hH : h < 2 ^ (r.drop la).length := by
      refine blocks_lt hB0 ?_ hh
      rw [hhi, ← pow_add, Nat.add_sub_cancel' hla]; exact hn
    simp only [Function.comp_apply]
    rw [eqTab_getD ho heH hH, c2_getD accs (by rw [hal]; exact hh), haccs,
      List.getD_eq_getElem _ _ (by simpa using hh), List.getElem_map, List.getElem_range]
    refine congrArg _ (Finset.sum_congr rfl fun l _ => by ring)

/-! ## Horner -/

theorem hs_horner2 (γ : C2) : ∀ (xs : List C2) (acc : C2),
    Hs c M (horner2 γ xs acc) (fun r => r.val M = (xs.map (C2.val M)).foldl (fun a x => γ.val M * a + x) (acc.val M))
  | [], _ => hs_pure rfl
  | x :: xs, acc => by
    rw [horner2]
    exact hs_bind (hs_g2Mul γ acc x) fun a ha => hs_mono (hs_horner2 γ xs a) fun r hr => by
      rw [hr, ha, List.map_cons, List.foldl_cons]

theorem foldl_rev_horner (γ : FE2) : ∀ ds : List FE2,
    ds.reverse.foldl (fun a x => γ * a + x) 0 = ((List.range ds.length).map fun k => γ ^ k * ds.getD k 0).sum
  | [] => by simp
  | d :: ds => by
    rw [List.reverse_cons, List.foldl_append, foldl_rev_horner γ ds, List.foldl_cons, List.foldl_nil,
      List.length_cons, List.range_succ_eq_map, List.map_cons, List.sum_cons, List.map_map, ← List.sum_map_mul_left]
    simp only [Function.comp_def, List.getD_cons_succ, List.getD_cons_zero, pow_zero, one_mul, pow_succ]
    rw [add_comm]
    exact congrArg₂ _ rfl (congrArg List.sum (List.map_congr_left fun k _ => by ring))

/-- **`Σ_k γ^k·d_k`** (`powSum2`, Horner from the top). -/
theorem hs_powSum2 {z2 : C2} (hz : z2.val M = 0) (γ : C2) (ds : List C2) :
    Hs c M (powSum2 z2 γ ds) (fun r => r.val M =
      ((List.range ds.length).map fun k => γ.val M ^ k * (ds.map (C2.val M)).getD k 0).sum) :=
  hs_mono (hs_horner2 γ ds.reverse z2) fun r hr => by
    rw [hr, hz, List.map_reverse, foldl_rev_horner, List.length_map]

end

/-! ## S2GT's child `PUB` lanes -/

open Lvm.QAcc in
theorem range_splitT (F : Nat → FK) (n : Nat) :
    (List.range (615 + n)).map F = [F 0] ++ ((List.range 4).map fun i => F (1 + i)) ++
      ((List.range 4).map fun i => F (5 + i)) ++ ((List.range 4).map fun i => F (9 + i)) ++ [F 13] ++
      ((List.range 4).map fun i => F (14 + i)) ++ ((List.range 597).map fun i => F (18 + i)) ++
      ((List.range n).map fun i => F (615 + i)) := by
  rw [show 615 + n = 1 + 4 + 4 + 4 + 1 + 4 + 597 + n by omega]
  simp only [map_range_add, List.map_map, Function.comp_def, List.append_assoc]
  simp only [List.range_one, List.map_cons, List.map_nil, Nat.add_zero, Nat.zero_add, List.cons_append,
    List.nil_append, Nat.add_assoc, Nat.reduceAdd]

open Lvm.QAcc in
/-- **S2GT's child `PUB` lanes** (`pubG`'s `hdrLanesT`, 707 lanes): the stream's lanes from `11`, except the key lanes
`1 … 4` (`pubOfA_hdrLanesS` at `acc_in`'s two-lane scalars). -/
theorem pubG_hdrLanesT (vk c : Vector UInt8 32) (sig : ByteArray) :
    (Lvm.E2T.pubG vk c sig).hdrLanesT = (List.range (615 + 2 * (Lvm.VEq.accVT + 1))).map (hdrLaneS vk sig) := by
  have pos (i : Nat) (h : ¬ (1 ≤ i ∧ i < 5)) : hdrLaneS vk sig i = kAt sig (8 * (11 + i)) := by
    simp only [hdrLaneS, h, ite_false]
  have e0 : (⟨(Lvm.E2T.pubG vk c sig).b.toUInt64⟩ : FK) = hdrLaneS vk sig 0 := by
    rw [pos 0 (by omega)]
    simp only [Lvm.E2T.pubG, pubOfW, pubOf, kAt, Nat.toUInt64, UInt64.ofNat_toNat]; rfl
  have e1 : (Lvm.E2T.pubG vk c sig).vk = (List.range 4).map fun i => hdrLaneS vk sig (1 + i) := by
    show digestLanes vk = _
    conv_lhs => rw [list_eq_range_getD (digestLanes vk)]
    rw [show (digestLanes vk).length = 4 by simp [digestLanes]]
    apply List.map_congr_left; intro i hi
    simp only [List.mem_range] at hi
    simp [hdrLaneS, show 1 ≤ 1 + i ∧ 1 + i < 5 by omega]
  have seg (o k n : Nat) (ho : 5 ≤ k) (hk : headerAt o = 8 * (11 + k)) :
      ((List.range n).map fun i => kAt sig (headerAt o + 8 * i)) =
        (List.range n).map fun i => hdrLaneS vk sig (k + i) := by
    apply List.map_congr_left; intro i _
    rw [pos _ (by omega), hk, show 8 * (11 + k) + 8 * i = 8 * (11 + (k + i)) by ring]
  have e4 : (⟨(Lvm.E2T.pubG vk c sig).n.toUInt64⟩ : FK) = hdrLaneS vk sig 13 := by
    rw [pos 13 (by omega)]
    simp only [Lvm.E2T.pubG, pubOfW, pubOf, kAt, Nat.toUInt64, UInt64.ofNat_toNat]; rfl
  have e7 : ((Lvm.E2T.pubG vk c sig).accIn.pt ++ [(Lvm.E2T.pubG vk c sig).accIn.y]).flatMap FE.lanes2 =
      (List.range (2 * (Lvm.VEq.accVT + 1))).map fun i => hdrLaneS vk sig (615 + i) := by
    have : (Lvm.E2T.pubG vk c sig).accIn.pt ++ [(Lvm.E2T.pubG vk c sig).accIn.y] =
        (List.range (Lvm.VEq.accVT + 1)).map fun j => fe16At sig (8 * 626 + 8 * 2 * j) := by
      simp only [Lvm.E2T.pubG, pubOfW]
      rw [List.range_succ, List.map_append, List.map_singleton]
      refine congrArg₂ (· ++ ·) (List.map_congr_left fun j _ => congrArg (fe16At sig) ?_)
        (congrArg (fun o => [fe16At sig o]) ?_) <;> simp only [headerAt, offAcc, sigBytes] <;> omega
    rw [this, flatMap_lanes2 sig (8 * 626) (Lvm.VEq.accVT + 1)]
    apply List.map_congr_left; intro i _
    rw [pos _ (by omega), show 8 * 626 + 8 * i = 8 * (11 + (615 + i)) by ring]
  have e2 : (Lvm.E2T.pubG vk c sig).cL = (List.range 4).map fun i => hdrLaneS vk sig (5 + i) :=
    seg 48 5 4 (by omega) rfl
  have e3 : (Lvm.E2T.pubG vk c sig).s = (List.range 4).map fun i => hdrLaneS vk sig (9 + i) :=
    seg 80 9 4 (by omega) rfl
  have e5 : (Lvm.E2T.pubG vk c sig).h = (List.range 4).map fun i => hdrLaneS vk sig (14 + i) :=
    seg 120 14 4 (by omega) rfl
  have e6 : (Lvm.E2T.pubG vk c sig).sigLeaf = (List.range 597).map fun i => hdrLaneS vk sig (18 + i) := by
    simp only [Lvm.E2T.pubG, pubOfW, pubOf]
    rw [show sigBytes / 8 = 597 from rfl]
    exact seg 152 18 597 (by omega) rfl
  rw [range_splitT]
  simp only [Pub.hdrLanesT, Pub.hdrLanesW, List.append_assoc]
  rw [e0, e1, e2, e3, e4, e5, e6, e7]


/-! ## `virtGT = virtD` -/

theorem sum_map_ite_filter {ι : Type} (p : ι → Prop) [DecidablePred p] (q : ι → Bool) (hpq : ∀ x, p x ↔ q x = true)
    (A : ι → FE2) : ∀ l : List ι, (l.map fun x => if p x then A x else 0).sum = ((l.filter q).map A).sum
  | [] => rfl
  | x :: l => by
    by_cases h : p x
    · simp [h, (hpq x).mp h, sum_map_ite_filter p q hpq A l]
    · have h' : q x = false := by simpa [hpq x] using h
      simp [h, h', sum_map_ite_filter p q hpq A l]

/-- **`virtD` on V_S's regions** (`TdOk`): the `PUB` region's term and the word `1`'s selector (`z_virtEF_td` at
`E2`). -/
theorem virtD_td {Td : TData} {N : Lvm.E2T.TNatT} (htd : TdOk Td N.toN) (pub : Pub) (ry : List FE2)
    (hry : 10 ≤ ry.length) :
    Lvm.E2T.virtD N pub ry = Lvm.E2T.hiWG ry 10 Td.pub * ∑ i ∈ range (2 ^ 10),
      FE2.ofK (pub.hdrLanesT.toArray.getD i 0) * E2V.eqAtF (ry.take 10) i + Lvm.E2T.hiWG ry 0 Td.one := by
  have hP : N.regs.filter (·.src == .pub) = [⟨Td.pub, 10, .pub, 0⟩] := htd.pub
  have hO : (N.regs.filter (·.src == .one)).map (fun g => (g.base, g.log)) = [(Td.one, 0)] := htd.one
  unfold Lvm.E2T.virtD
  rw [Lvm.E2T.kf_virtG _ _ _ fun g hg hs => ?_, List.sum_map_add,
    sum_map_ite_filter (fun g : TypedV.NReg => g.src = .pub) (·.src == .pub) (fun _ => beq_iff_eq.symm),
    sum_map_ite_filter (fun g : TypedV.NReg => g.src = .one) (·.src == .one) (fun _ => beq_iff_eq.symm), hP,
    show ∀ l : List TypedV.NReg, l.map (fun g => Lvm.E2T.hiWG ry g.log g.base) =
      (l.map fun g => (g.base, g.log)).map fun x => Lvm.E2T.hiWG ry x.2 x.1 from fun l => by rw [List.map_map]; rfl, hO]
  · simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero, Nat.zero_add]
    rfl
  · have : g ∈ N.regs.filter (·.src == .pub) := List.mem_filter.mpr ⟨hg, by simp [hs]⟩
    rw [hP, List.mem_singleton] at this
    rw [this]; exact hry

section
variable {c : Ctx} {M : Mem}

theorem pubLaneC_K (hd vkc i : Nat) : (Lvm.QAcc.pubLaneC hd vkc i).ty = .K := by
  unfold Lvm.QAcc.pubLaneC; split <;> rfl

/-- **`virtGT`'s value is V_S's `virtD`** at `r_y` on the child's `PUB` at S2GT (`pubG`: the stream's header lanes,
the current proof's `vk` cells at `pb + 1`), on regions that are V_S's. -/
theorem hs_virtGT (vk cL : Vector UInt8 32) {sig : ByteArray} {T : Nat} (hS : Lvm.Q1.Streamed M sig T)
    {z2 o2 : C2} (hz : z2.val M = 0) (ho : o2.val M = 1) (hz2K : KC2 z2) (ho2K : KC2 o2) {Td : TData}
    {N : Lvm.E2T.TNatT} (htd : TdOk Td N.toN) {pb n : Nat} (hn : n = 615 + 2 * (Lvm.VEq.accVT + 1))
    (hvk : ∀ i < 4, M.k (pb + 1 + i) = (digestLanes vk).getD i 0) (hH : 11 + n ≤ T) (ry : List C2)
    (hry : 10 ≤ ry.length) :
    Hs c M (virtGT z2 o2 Td pb n ry) (fun w => w.val M =
      Lvm.E2T.virtD N (Lvm.E2T.pubG vk cL sig) (ry.map (C2.val M))) := by
  unfold virtGT regSel2
  simp only [htd.qlt]
  have hlen : (ry.take 10).length = 10 := List.length_take_of_le hry
  have hn' : n = 707 := by rw [hn]; rfl
  refine hs_bind (hs_eqConst2 hz ho ho2K _ _) fun sP ⟨_, hsP⟩ =>
    hs_bind (hs_eqDot2K hz ho hz2K ho2K (ry.take 10) 5 (by rw [hlen]; omega) _
      (fun x hx => by obtain ⟨i, -, rfl⟩ := List.mem_map.mp hx; exact pubLaneC_K _ _ _)
      (by rw [List.length_map, List.length_range, hlen, hn']; omega)) fun vP hvP =>
    hs_bind (hs_g2Mul sP vP z2) fun w hw => hs_bind (hs_eqConst2 hz ho ho2K ry Td.one) fun e1 ⟨_, he1⟩ =>
    hs_mono (hs_g2Add w e1) fun w' hw' => ?_
  rw [hw', hw, hz, add_zero, hsP, hvP, he1, virtD_td htd _ _ (by simpa using hry), pubG_hdrLanesT]
  simp only [Lvm.E2T.hiWG, List.map_drop, Nat.shiftRight_zero, List.drop_zero, List.map_take]
  refine congrArg₂ (· + ·) (congrArg₂ (· * ·) rfl ?_) rfl
  rw [List.length_map, List.length_range]
  rw [← hn]
  obtain ⟨m, hm⟩ : ∃ m, 2 ^ 10 = n + m := ⟨2 ^ 10 - n, by rw [hn']; norm_num⟩
  rw [hm, Finset.sum_range_add, Finset.sum_eq_zero (s := range m) fun j _ => by
    rw [Lvm.list_toArray_getD, List.getD_eq_default _ _ (by rw [List.length_map, List.length_range]; omega),
      show FE2.ofK 0 = 0 from rfl, zero_mul], add_zero]
  refine Finset.sum_congr rfl fun i hi => ?_
  rw [Finset.mem_range] at hi
  rw [mul_comm, Lvm.list_toArray_getD, List.getD_eq_getElem _ _ (by simpa using hi), List.getElem_map,
    List.getElem_range, List.getD_eq_getElem _ _ (by simpa using hi), List.getElem_map, List.getElem_range]
  refine congrArg₂ (· * ·) (congrArg FE2.ofK ?_) rfl
  unfold Lvm.QAcc.pubLaneC Lvm.QAcc.hdrLaneS
  split_ifs with h
  · rw [Cell.val_K, show pb + 1 + (i - 1) = pb + 1 + (i - 1) from rfl, hvk _ (by omega)]; rfl
  · rw [Cell.val_K, hS _ (by omega)]; rfl

end

/-! ## The relayout's kernel at `E2` (`relayKernGT = relayKernD`) -/

/-- A weight's value (`none`: `0`). -/
def ov2 (M : Mem) : Option C2 → FE2
  | none => 0
  | some x => x.val M

/-- `divStep2`'s transitions. -/
def d2_cg (z2 ρi nρ : C2) : Option C2 → BM (List (Nat × Nat × C2))
  | none => pure [(0, 0, nρ), (1, 0, ρi)]
  | some r => do
    let nr ← g2One r
    let c00 ← g2Mul nρ nr z2
    let c10 ← g2Mul ρi nr z2
    let c01 ← g2Mul nρ r z2
    let c11 ← g2Mul ρi r z2
    pure [(0, 0, c00), (1, 0, c10), (0, 1, c01), (1, 1, c11)]

/-- The incoming transitions of the new remainder `r'`. -/
def d2_ins (c : List (Nat × Nat × C2)) (W : List (Option C2)) (r' : Nat) : List (C2 × C2) :=
  (List.range 17).flatMap fun rem => match W.getD rem none with
    | none => []
    | some w => c.filterMap fun x =>
      let v := 2 * rem + x.1
      let qb := if 17 ≤ v then 1 else 0
      if qb = x.2.1 ∧ v - 17 * qb = r' then some (w, x.2.2) else none

/-- A weight, `none` for no incoming transition. -/
def d2_opt (z2 : C2) : List (C2 × C2) → BM (Option C2)
  | [] => pure none
  | l => g2Dot z2 l >>= fun s => pure (some s)

theorem divStep2_eq (z2 ρi : C2) (ri : Option C2) (W : List (Option C2)) :
    divStep2 z2 ρi ri W = (g2One ρi >>= fun nρ => d2_cg z2 ρi nρ ri >>= fun c =>
      mapB (fun r' => d2_opt z2 (d2_ins c W r')) (List.range 17)) := by
  cases ri <;> rfl

section
variable {c : Ctx} {M : Mem}

theorem hs_d2_opt {z2 : C2} (hz : z2.val M = 0) (l : List (C2 × C2)) :
    Hs c M (d2_opt z2 l) (fun o => ov2 M o = (l.map fun e => e.1.val M * e.2.val M).sum) := by
  cases l with
  | nil => exact hs_pure rfl
  | cons e l => exact hs_bind (hs_g2Dot z2 _) fun s hs => hs_pure (by rw [ov2, hs, hz, zero_add])

theorem hs_mapB_ov {α : Type} (f : α → BM (Option C2)) (g : α → FE2) (hf : ∀ a, Hs c M (f a) (fun o => ov2 M o = g a)) :
    ∀ l : List α, Hs c M (mapB f l) (fun os => os.map (ov2 M) = l.map g)
  | [] => hs_pure rfl
  | a :: l => hs_bind (hf a) fun r hr => hs_bind (hs_mapB_ov f g hf l) fun rs hrs =>
    hs_pure (by rw [List.map_cons, List.map_cons, hr, hrs])

/-- The transitions' values: `Σ_x g(b, q)·x = Σ_{b, q} g(b, q)·fac(b, q)` (`kg_fac` at bit `k`). -/
theorem hs_d2_cg {z2 : C2} (hz : z2.val M = 0) (ρi nρ : C2) (hnρ : nρ.val M = 1 + ρi.val M) (ρv rlo : List FE2)
    (k : Nat) (hρ : ρv.toArray.getD k 0 = ρi.val M) :
    ∀ ri : Option C2, (∀ r, ri = some r → k < 14 ∧ rlo.toArray.getD k 0 = r.val M) → (ri = none → 14 ≤ k) →
    Hs c M (d2_cg z2 ρi nρ ri) (fun cs => ∀ g : Nat → Nat → FE2,
      (cs.map fun x => g x.1 x.2.1 * x.2.2.val M).sum =
        g 0 0 * Lvm.E2T.kg_fac ρv rlo k false false + g 1 0 * Lvm.E2T.kg_fac ρv rlo k true false +
          g 0 1 * Lvm.E2T.kg_fac ρv rlo k false true + g 1 1 * Lvm.E2T.kg_fac ρv rlo k true true)
  | none, _, hn => hs_pure fun g => by
    have hk : ¬ k < 14 := by have := hn rfl; omega
    simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Lvm.E2T.kg_fac, Lvm.E2T.eq1G,
      TypedV.recRowBits, hk, ite_false, ite_true, hρ, hnρ, Bool.false_eq_true]
    ring
  | some r, hr, _ => by
    obtain ⟨hk, hra⟩ := hr r rfl
    unfold d2_cg
    refine hs_bind (hs_g2One r) fun nr hnr => hs_bind (hs_g2Mul _ _ _) fun c00 h00 =>
      hs_bind (hs_g2Mul _ _ _) fun c10 h10 => hs_bind (hs_g2Mul _ _ _) fun c01 h01 =>
      hs_bind (hs_g2Mul _ _ _) fun c11 h11 => hs_pure fun g => ?_
    simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Lvm.E2T.kg_fac, Lvm.E2T.eq1G,
      TypedV.recRowBits, hk, ite_false, ite_true, hρ, hra, Bool.false_eq_true]
    rw [h00, h01, h10, h11, hnr, hnρ, hz]
    ring

theorem sum_filterMap_ite2 {α : Type} (P : α → Prop) [DecidablePred P] (h : α → C2 × C2) (G : C2 × C2 → FE2) :
    ∀ l : List α, ((l.filterMap fun x => if P x then some (h x) else none).map G).sum =
      (l.map fun x => if P x then G (h x) else 0).sum
  | [] => rfl
  | x :: l => by
    rw [List.filterMap_cons]
    by_cases hx : P x
    · simp only [hx, ite_true, List.map_cons, List.sum_cons, sum_filterMap_ite2 P h G l]
    · simp only [hx, ite_false, List.map_cons, List.sum_cons, sum_filterMap_ite2 P h G l, zero_add]

theorem sum_flatMap2 {α β : Type} (f : α → List β) (G : β → FE2) : ∀ l : List α,
    ((l.flatMap f).map G).sum = (l.map fun a => ((f a).map G).sum).sum
  | [] => rfl
  | a :: l => by
    rw [List.flatMap_cons, List.map_append, List.sum_append, sum_flatMap2 f G l, List.map_cons, List.sum_cons]

theorem d2_ins_sum (c' : List (Nat × Nat × C2)) (W : List (Option C2)) (r' : Nat) :
    ((d2_ins c' W r').map fun ab => ab.1.val M * ab.2.val M).sum =
      ((List.range 17).map fun rem => ov2 M (W.getD rem none) *
        (c'.map fun x => (if (if 17 ≤ 2 * rem + x.1 then 1 else 0) = x.2.1 ∧
          2 * rem + x.1 - 17 * (if 17 ≤ 2 * rem + x.1 then 1 else 0) = r' then 1 else 0) * x.2.2.val M).sum).sum := by
  rw [d2_ins, sum_flatMap2]
  refine congrArg List.sum (List.map_congr_left fun rem _ => ?_)
  cases hw : W.getD rem none with
  | none => simp [ov2]
  | some w =>
    simp only [ov2]
    refine (sum_filterMap_ite2 _ _ _ c').trans ?_
    rw [← List.sum_map_mul_left]
    refine congrArg List.sum (List.map_congr_left fun x _ => ?_)
    split_ifs <;> simp

/-- The automaton's state against the circuit's weights. -/
def DRel2 (M : Mem) (V : Array FE2) (W : List (Option C2)) : Prop :=
  W.length = 17 ∧ ∀ j < 17, V.getD j 0 = ov2 M (W.getD j none)

theorem divStep2_rel {z2 : C2} (hz : z2.val M = 0) {ρi : C2} {ri : Option C2} {k : Nat} (ρv rlo : List FE2)
    (hρ : ρv.toArray.getD k 0 = ρi.val M) (hri : ∀ r, ri = some r → k < 14 ∧ rlo.toArray.getD k 0 = r.val M)
    (hn : ri = none → 14 ≤ k) {V : Array FE2} {W : List (Option C2)} (hVW : DRel2 M V W) :
    Hs c M (divStep2 z2 ρi ri W) (fun W' => DRel2 M (Lvm.E2T.kg_dstep (Lvm.E2T.kg_fac ρv rlo k) V) W') := by
  rw [divStep2_eq]
  refine hs_bind (hs_g2One ρi) fun nρ hnρ => hs_bind (hs_d2_cg hz ρi nρ hnρ ρv rlo k hρ ri hri hn) fun cc hc =>
    hs_mono (hs_mapB_ov _ (fun r' => ((d2_ins cc W r').map fun ab => ab.1.val M * ab.2.val M).sum)
      (fun r' => hs_d2_opt hz _) _) fun W' hW' => ?_
  have hl : W'.length = 17 := by
    rw [← List.length_map (f := ov2 M), hW', List.length_map, List.length_range]
  refine ⟨hl, fun j hj => ?_⟩
  have hv : ov2 M (W'.getD j none) = ((d2_ins cc W j).map fun ab => ab.1.val M * ab.2.val M).sum := by
    rw [← List.getD_map (f := ov2 M), hW', List.getD_eq_getElem _ _ (by simpa using hj), List.getElem_map, List.getElem_range]
  rw [hv, Lvm.E2T.kg_dstep_getD, d2_ins_sum, Lvm.E2T.kg_list_sum_range]
  refine Finset.sum_congr rfl fun rem hrem => ?_
  have hrem' : rem < 17 := Finset.mem_range.mp hrem
  rw [hc fun b q => if (if 17 ≤ 2 * rem + b then 1 else 0) = q ∧
    2 * rem + b - 17 * (if 17 ≤ 2 * rem + b then 1 else 0) = j then 1 else 0, ← hVW.2 rem hrem']
  simp only [Lvm.E2T.kg_idx, Lvm.E2T.kg_f, Lvm.E2T.kg_t, TypedV.sLanes, recStreamCols]
  by_cases h17 : 17 ≤ 2 * rem <;> by_cases h16 : 17 ≤ 2 * rem + 1 <;>
    simp [h17, h16] <;> split_ifs <;> ring

theorem getD_val2 {z2 : C2} (hz : z2.val M = 0) (l : List C2) (k : Nat) :
    (l.map (C2.val M)).getD k 0 = (l.getD k z2).val M := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_map, List.getD_eq_getElem?_getD]
  cases l[k]? <;> simp [hz]

theorem divRun2_rel {z2 : C2} (hz : z2.val M = 0) (ρ r : List C2) : ∀ n, n ≤ 19 →
    ∀ (V : Array FE2) (W : List (Option C2)), DRel2 M V W →
      Hs c M (divRun2 z2 ρ r n W) (fun W' => DRel2 M ((List.range n).reverse.foldl
        (fun V k => Lvm.E2T.kg_dstep (Lvm.E2T.kg_fac (ρ.map (C2.val M)) ((r.map (C2.val M)).take 14) k) V) V) W')
  | 0, _, V, W, hVW => hs_pure hVW
  | n + 1, hn, V, W, hVW => by
    rw [divRun2, List.range_succ, List.reverse_append, List.reverse_singleton, List.singleton_append,
      List.foldl_cons]
    refine hs_bind (divStep2_rel hz _ _ ?_ (fun r' hr' => ?_) (fun hn' => ?_) hVW) fun W' hW' =>
      divRun2_rel hz ρ r n (by omega) _ _ hW'
    · rw [Lvm.E2T.kg_toArray_getD, getD_val2 hz]
    · by_cases h14 : n < 14
      · rw [if_pos h14, Option.some.injEq] at hr'
        refine ⟨h14, ?_⟩
        rw [← hr', Lvm.E2T.kg_toArray_getD, ← List.map_take, getD_val2 hz, List.getD_eq_getElem?_getD,
          List.getElem?_take, if_pos h14, ← List.getD_eq_getElem?_getD]
      · rw [if_neg h14] at hr'; exact absurd hr' (by simp)
    · by_cases h14 : n < 14
      · rw [if_pos h14] at hn'; exact absurd hn' (by simp)
      · omega

theorem drel2_init {o2 : C2} (ho : o2.val M = 1) :
    DRel2 M Lvm.E2T.kg_init ((List.range 17).map fun i => if i = 0 then some o2 else none) := by
  refine ⟨by simp, fun j hj => ?_⟩
  rw [Lvm.E2T.kg_init_getD]
  rcases j with _ | j
  · simp [ov2, ho]
  · simp [ov2, List.getD_eq_getElem?_getD, hj]

end

/-! ### The comparator's tail (`geKernG` at the stream's end) -/

section Ge
variable {F : Type} [Field F]

/-- A run of `0` bits of `c` (`r_geRun_zero` over a field). -/
theorem ge_run_zero (c : Nat) (ρ r : List F) : ∀ (ks : List Nat) (a b : F),
    (∀ k ∈ ks, c.testBit k = false) → ks.foldl (Lvm.E2T.kg_gt c ρ r) (a, b) =
      (a * (ks.map fun k => Lvm.E2T.eq1G (ρ.getD k 0) false * Lvm.E2T.eq1G (r.getD k 0) false).prod,
        (a + b) * (ks.map fun k => Lvm.E2T.eq1G (ρ.getD k 0) false * Lvm.E2T.eq1G (r.getD k 0) false +
          Lvm.E2T.eq1G (ρ.getD k 0) true * Lvm.E2T.eq1G (r.getD k 0) true).prod -
        a * (ks.map fun k => Lvm.E2T.eq1G (ρ.getD k 0) false * Lvm.E2T.eq1G (r.getD k 0) false).prod)
  | [], a, b, _ => by simp
  | k :: ks, a, b, h => by
    have hk : c.testBit k = false := h k List.mem_cons_self
    rw [List.foldl_cons]
    simp only [Lvm.E2T.kg_gt, hk, Bool.false_eq_true, ite_false, Lvm.E2T.kg_toArray_getD]
    rw [ge_run_zero c ρ r ks _ _ fun k' hk' => h k' (List.mem_cons_of_mem _ hk')]
    simp only [List.map_cons, List.prod_cons, Prod.mk.injEq]
    constructor <;> ring

/-- `t_k(0)`. -/
def tF (ρ r : List F) (k : Nat) : F := Lvm.E2T.eq1G (ρ.getD k 0) false * Lvm.E2T.eq1G (r.getD k 0) false

/-- `t_k(1)`. -/
def tT (ρ r : List F) (k : Nat) : F := Lvm.E2T.eq1G (ρ.getD k 0) true * Lvm.E2T.eq1G (r.getD k 0) true

/-- **`geKernG` at the stream's end** (`c = 17·2^14`), `t_k(b) = eq1(ρ_k, b)·eq1(r_k, b)` (characteristic 2). -/
theorem geKern_tail (h2 : (2 : F) = 0) (ρ r : List F) :
    Lvm.E2T.geKernG 278528 19 ρ r =
      ((List.range 14).map fun k => tF ρ r k + tT ρ r k).prod * tT ρ r 18 *
      (((List.range 4).map fun i => tF ρ r (14 + i) + tT ρ r (14 + i)).prod +
       ((List.range 4).map fun i => tF ρ r (14 + i)).prod) := by
  unfold tF tT
  have e : (List.range 19).reverse = [18, 17, 16, 15, 14] ++ (List.range 14).reverse := by decide
  have hz : ∀ k ∈ (List.range 14).reverse, Nat.testBit 278528 k = false := by decide
  rw [Lvm.E2T.kg_geKern_unfold, e, List.foldl_append]
  simp only [List.foldl_cons, List.foldl_nil, Lvm.E2T.kg_gt, Lvm.E2T.kg_toArray_getD,
    show Nat.testBit 278528 18 = true by decide, show Nat.testBit 278528 17 = false by decide,
    show Nat.testBit 278528 16 = false by decide, show Nat.testBit 278528 15 = false by decide,
    show Nat.testBit 278528 14 = true by decide, ite_true, ite_false, Bool.false_eq_true]
  rw [ge_run_zero _ _ _ _ _ _ hz, List.map_reverse, List.prod_reverse, List.map_reverse, List.prod_reverse]
  simp only [show List.range 4 = [0, 1, 2, 3] from rfl, List.map_cons, List.map_nil, List.prod_cons, List.prod_nil,
    Nat.reduceAdd]
  generalize ((List.range 14).map fun k => Lvm.E2T.eq1G (ρ.getD k 0) false * Lvm.E2T.eq1G (r.getD k 0) false).prod = P0
  generalize ((List.range 14).map fun k => Lvm.E2T.eq1G (ρ.getD k 0) false * Lvm.E2T.eq1G (r.getD k 0) false +
    Lvm.E2T.eq1G (ρ.getD k 0) true * Lvm.E2T.eq1G (r.getD k 0) true).prod = PF
  linear_combination (-(Lvm.E2T.eq1G (ρ.getD 18 0) true * Lvm.E2T.eq1G (r.getD 18 0) true) * PF *
    (Lvm.E2T.eq1G (ρ.getD 14 0) false * Lvm.E2T.eq1G (r.getD 14 0) false *
      (Lvm.E2T.eq1G (ρ.getD 15 0) false * Lvm.E2T.eq1G (r.getD 15 0) false) *
      (Lvm.E2T.eq1G (ρ.getD 16 0) false * Lvm.E2T.eq1G (r.getD 16 0) false) *
      (Lvm.E2T.eq1G (ρ.getD 17 0) false * Lvm.E2T.eq1G (r.getD 17 0) false))) * h2

end Ge


section
variable {c : Ctx} {M : Mem}

theorem fe2_two : (2 : FE2) = 0 := by rw [← one_add_one_eq_two]; exact fe2_add_self 1

theorem hs_mapB_len {α β : Type} (f : α → BM β) : ∀ l : List α, Hs c M (mapB f l) (fun rs => rs.length = l.length)
  | [] => hs_pure rfl
  | a :: l => hs_bind (hs_true _) fun _ _ => hs_bind (hs_mapB_len f l) fun rs hrs =>
    hs_pure (by rw [List.length_cons, List.length_cons, hrs])

theorem map_val_dt (ts : List (C2 × C2 × C2)) (f : C2 × C2 × C2 → C2) (g : Nat → FE2) (a n : Nat)
    (hl : a + n ≤ ts.length) (hv : ∀ i, a ≤ i → i < a + n → (f (ts.getD i default)).val M = g i) :
    (((ts.drop a).take n).map f).map (C2.val M) = (List.range n).map fun i => g (a + i) := by
  apply List.ext_getElem
  · simp; omega
  · intro i h1 h2
    simp only [List.length_map, List.length_range] at h2
    simp only [List.getElem_map, List.getElem_take, List.getElem_drop, List.getElem_range]
    rw [← hv (a + i) (by omega) (by omega), List.getD_eq_getElem _ _ (by omega)]

/-- **`tailG2`'s value**: `geKernG` at the stream's end (`r_tailG_val` at `E2`). -/
theorem hs_tailG2 {z2 o2 : C2} (hz : z2.val M = 0) (ho : o2.val M = 1) (ρ r : List C2) :
    Hs c M (tailG2 z2 o2 ρ r) (fun b => b.val M = Lvm.E2T.geKernG 278528 19 (ρ.map (C2.val M)) (r.map (C2.val M))) := by
  rw [geKern_tail fe2_two]
  unfold tailG2
  dsimp only
  refine hs_bind (hs_and (hs_mapB_len _ _) (hs_mapB_getD _ (fun i (t : C2 × C2 × C2) =>
      t.1.val M = tF (ρ.map (C2.val M)) (r.map (C2.val M)) i ∧ t.2.1.val M = tT (ρ.map (C2.val M)) (r.map (C2.val M)) i ∧
        t.2.2.val M = tF (ρ.map (C2.val M)) (r.map (C2.val M)) i + tT (ρ.map (C2.val M)) (r.map (C2.val M)) i)
      (fun i => ?_) _)) fun ts ⟨hlen, hts⟩ => ?_
  · refine hs_bind (hs_g2One _) fun na hna => hs_bind (hs_g2One _) fun nb hnb => hs_bind (hs_g2Mul _ _ _) fun d0 h0 =>
      hs_bind (hs_g2Mul _ _ _) fun d1 h1 => hs_bind (hs_g2Add _ _) fun t ht => hs_pure ?_
    have e0 : d0.val M = tF (ρ.map (C2.val M)) (r.map (C2.val M)) i := by
      rw [h0, hna, hnb, hz, add_zero, tF, getD_val2 hz, getD_val2 hz]; rfl
    have e1 : d1.val M = tT (ρ.map (C2.val M)) (r.map (C2.val M)) i := by
      rw [h1, hz, add_zero, tT, getD_val2 hz, getD_val2 hz]; rfl
    exact ⟨e0, e1, by rw [ht, e0, e1]⟩
  · rw [List.length_range] at hlen
    have hv : ∀ i < 19, (ts.getD i default).1.val M = tF (ρ.map (C2.val M)) (r.map (C2.val M)) i ∧
        (ts.getD i default).2.1.val M = tT (ρ.map (C2.val M)) (r.map (C2.val M)) i ∧
        (ts.getD i default).2.2.val M = tF (ρ.map (C2.val M)) (r.map (C2.val M)) i +
          tT (ρ.map (C2.val M)) (r.map (C2.val M)) i := fun i hi => by
      have := hts i (by simpa using hi); rwa [List.getElem_range] at this
    have p1 := map_val_dt ts (·.2.2) _ 0 14 (by omega) fun i _ hi => (hv i (by omega)).2.2
    have p2 := map_val_dt ts (·.2.2) _ 14 4 (by omega) fun i _ hi => (hv i (by omega)).2.2
    have p3 := map_val_dt ts (·.1) _ 14 4 (by omega) fun i _ hi => (hv i (by omega)).1
    rw [List.drop_zero] at p1
    simp only [Nat.zero_add] at p1
    have h18 : (ts.getD 18 (z2, z2, z2)).2.1.val M = tT (ρ.map (C2.val M)) (r.map (C2.val M)) 18 := by
      rw [List.getD_eq_getElem _ _ (by omega), ← List.getD_eq_getElem _ default (by omega)]; exact (hv 18 (by omega)).2.1
    refine hs_bind (hs_g2Prod hz o2 _) fun pT hpT => hs_bind (hs_g2Prod hz o2 _) fun pM hpM =>
      hs_bind (hs_g2Prod hz o2 _) fun pZ hpZ => hs_bind (hs_g2Add pM pZ) fun df hdf =>
      hs_bind (hs_g2Mul _ _ z2) fun hh hhh => hs_mono (hs_g2Mul hh df z2) fun b hb => ?_
    rw [hb, hhh, hdf, hpT, hpM, hpZ, ho, hz, p1, p2, p3, h18]
    ring

theorem pt5_vals {z2 : C2} (hz : z2.val M = 0) (r : List C2) (hr : r.length = 19) :
    ((List.range 5).map fun i => r.getD (14 + i) z2).map (C2.val M) = (r.map (C2.val M)).drop 14 := by
  apply List.ext_getElem (by simp [hr])
  intro i h1 h2
  simp only [List.length_map, List.length_range] at h1
  rw [List.getElem_map, List.getElem_map, List.getElem_range, List.getElem_drop, List.getElem_map,
    List.getD_eq_getElem _ _ (by omega)]

/-- **The relayout's kernel in the circuit is V_S's** (`relayKernD`, on regions that are V_S's; `relayKernG_spec`
at `E2`). -/
theorem hs_relayKernGT {z2 o2 : C2} (hz : z2.val M = 0) (ho : o2.val M = 1) (ho2K : KC2 o2) {Td : TData}
    {N : Lvm.E2T.TNatT} (htd : TdOk Td N.toN) (ry r : List C2) (hr : r.length = 19) :
    Hs c M (relayKernGT z2 o2 Td ry r) (fun k => k.val M =
      Lvm.E2T.relayKernD N (ry.map (C2.val M)) (r.map (C2.val M))) := by
  unfold relayKernGT regSel2
  dsimp only
  refine hs_bind (hs_eqConst2 hz ho ho2K _ _) fun sel ⟨_, hsel⟩ =>
    hs_bind (divRun2_rel hz (ry.take 19) r 19 le_rfl _ _ (drel2_init ho)) fun W hW =>
    hs_bind (hs_eqDot2 hz ho _ 2 (by simp) _ (by simp [hW.1])) fun a ha =>
    hs_bind (hs_tailG2 hz ho _ _) fun b hb => hs_bind (hs_g2Add a b) fun s hs => hs_mono (hs_g2Mul sel s z2) fun k hk => ?_
  have hrl : (r.map (C2.val M)).length = 19 := by simp [hr]
  have hdk : Lvm.E2T.divKernG 0 19 ((ry.map (C2.val M)).take 19) ((r.map (C2.val M)).take 14) ((r.map (C2.val M)).drop 14) =
      ∑ rem ∈ range 17, ((List.range 19).reverse.foldl (fun V k => Lvm.E2T.kg_dstep
        (Lvm.E2T.kg_fac ((ry.map (C2.val M)).take 19) ((r.map (C2.val M)).take 14) k) V) Lvm.E2T.kg_init).getD rem 0 *
        E2V.eqAtF ((r.map (C2.val M)).drop 14) rem := by
    have hd := Lvm.E2T.kg_divKern_unfold ((ry.map (C2.val M)).take 19) ((r.map (C2.val M)).take 14) ((r.map (C2.val M)).drop 14)
    rw [Lvm.E2T.kg_foldl_range, zero_add] at hd
    exact hd
  rw [hk, hs, hz, add_zero, hsel, ha, hb, pt5_vals hz r hr]
  unfold Lvm.E2T.relayKernD Lvm.E2T.relayKernG
  rw [show N.toN.regsOf .sflat = [⟨Td.sflat, 19, .sflat, 0⟩] from htd.sflat]
  simp only [List.foldl_cons, List.foldl_nil, zero_add]
  rw [if_neg (by decide), List.drop_of_length_le (by omega : (r.map (C2.val M)).length ≤ 19),
    List.take_of_length_le (by omega : (r.map (C2.val M)).length ≤ 19),
    show TypedV.sPos - min TypedV.sPos 0 = 278528 from rfl, show TypedV.recRowBits = 14 from rfl, hdk]
  simp only [Lvm.E2T.hiWG, List.map_drop, List.map_take, E2V.eqAtF_nil, one_mul, Nat.zero_shiftRight]
  refine congrArg₂ (· * ·) rfl (congrArg₂ (· + ·) ?_ rfl)
  rw [List.length_map, hW.1]
  rw [List.map_take] at hW
  refine Finset.sum_congr rfl fun k hk => ?_
  rw [Finset.mem_range] at hk
  rw [mul_comm, hW.2 k hk, List.getD_eq_getElem _ _ (by simpa [hW.1] using hk), List.getElem_map, List.getElem_map,
    ← List.getD_eq_getElem _ none (by rw [hW.1]; exact hk)]
  cases W.getD k none <;> simp [ov2, hz]

end
end Lvm.E2Q
