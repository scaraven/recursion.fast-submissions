-- New for `flock-recursive` (stage P4a pass 4 (P4d)): controls for `FRSoundness4P4aZ`/`L`/`T`/`DF`.
import FRSoundness4P4aT
import FRSoundness4P4aDF

/-!
# Controls for pass 4

* `ZLM4.EtLocal`: P4a's `zlm4` meets it (`zlm4_etLocal`, +); a target reading the log's length
  does not (`not_etLocal_len`, −).
* `WitBits`: T4's `zW` meets it (`witBits_zW`, +); a constant non-bit witness does not
  (`not_witBits`, −).
* `rejOK_at4`: Z's check is one (`rejZ_ok4`, +); a check from an absorb position's squeeze
  successor is refused (`not_rejOK_at_sq`, −: position 3 is Z1's squeeze).
* `RejF4a`: no check fails before Zend's absorb (`not_rejF4a_short`, −); S2's failed round check is
  one (`rejF4a_of_rejS2`, +).
* `L3BadN`/`PendLcN`: never on a segment (`not_l3BadN_seg`, `not_pendLcN_seg`, −); on a node, a
  wrong masked value is L3's doom (`l3BadN_of`, +).
* `DF4a`: the background dooms every non-`msD` phase 2 … 12 (`DF4a_of_bgA`, +); phases 0, 1 and
  13 on are `False` (`not_DF4a_out`, −).
* `frontCls4a`: Zend's absorb (67) is no squeeze class and Z3's first squeeze (16) no absorb class
  (`frontCls4a_neg`, −); both are classified by their items (`frontCls4a_pos`, +).
* `SameStab4`: a predicate of `L` itself is not stable (`not_ss_log4`, −); `False` is (+).
* `WitOf`: T4's witness is the unpacked `fF` (`witOf_of`, +, for any source with `fz = fF`).
-/

namespace FR.Snd.P4a
open RecursionFast FR.Merkle Finset FR.Impl

/-! ## `EtLocal`, `WitBits` -/

/-- Control (negative): a target reading the log's length does not read before 2. -/
theorem not_etLocal_len :
    ¬ ZLM4.EtLocal ⟨0, 0, 0, fun _ es _ _ => if es.length ≤ 2 then 0 else 1⟩ := fun h => by
  have hA : Agree (List.replicate 2 default ++ [default]) (List.replicate 2 default) 2 :=
    agree_append _ _ (by simp)
  have := congrFun (congrFun (h (.seg .L32) _ _ hA) 0) 0
  simp at this

open Classical in
theorem exists_not_bit : ∃ x : F, ¬ IsBitF x := by
  by_contra h
  push Not at h
  have hs : (univ : Finset F) ⊆ {0, 1} := fun x _ => by
    rcases h x with hx | hx <;> simp [hx]
  have h1 := card_le_card hs
  rw [card_univ, F.card_F] at h1
  have h2 := h1.trans (card_insert_le _ _)
  simp at h2

/-- Control (negative): a constant non-bit witness is not bit-valued. -/
theorem not_witBits : ∃ zw : Wit, ¬ WitBits zw := by
  obtain ⟨x, hx⟩ := exists_not_bit
  exact ⟨fun _ _ _ _ => x, fun h => hx (h (.seg .L32) [] [] 0)⟩

/-- Control (positive): any source whose `fz` is `fF` at the log's kind has T4's `zW` as its
unpacked witness. -/
theorem witOf_of {R : P4b.FSrc} (h : ∀ L es, R.fz L es = T4.fF (kindOfC es) L es) :
    WitOf R T4.zW := fun L es b => by simp only [T4.zW, h]

/-! ## Checks -/

/-- Control (negative): `rejOK_at4` needs a non-squeeze: a check from Z1's first squeeze's
successor on is not a `T4.RejOK` (it changes at the squeeze). -/
theorem not_rejOK_at_sq : ¬ T4.RejOK fun (_ : Log) (es : Log) => 3 + 1 ≤ es.length := fun h => by
  have hsq : fsItems4[3]? = some .squeeze := by
    have := T4.sq_of_fsRnd (p := 3) (s0 := 2) (r := 10) (by
      rw [fsRnd4, fsRanges4_eq]; decide)
    exact this
  have := (h.sq [] (List.replicate 3 default) default (by simpa using hsq)).mp (by simp)
  simp at this

theorem not_rejF4a_short {M : ZLM4} {L es : Log} (hl : es.length < 68) : ¬ RejF4a M L es := by
  rintro (h | ⟨l, -, hl', -⟩ | h | h | ⟨l, -, hl', -⟩)
  · exact absurd h.1 (by omega)
  · omega
  · exact absurd h.1 (by omega)
  · exact absurd h.1 (by omega)
  · omega

theorem rejF4a_of_rejS2 {M : ZLM4} {L es : Log} (h : RejS2 L es) : RejF4a M L es :=
  Or.inr (Or.inr (Or.inr (Or.inr h)))

/-! ## The node's L dooms -/

theorem not_l3BadN_seg {M : ZLM4} {zw : Wit} {L es : Log} (hn : (kindOfC es).isNode = false) :
    ¬ L3BadN M zw L es := fun h => by rw [h.2.1] at hn; exact Bool.noConfusion hn

theorem not_pendLcN_seg {M : ZLM4} {zw : Wit} {L es : Log} (hn : (kindOfC es).isNode = false) :
    ¬ PendLcN M zw L es := fun h => by rw [h.2.1] at hn; exact Bool.noConfusion hn

theorem l3BadN_of {M : ZLM4} {zw : Wit} {L es : Log} (hl : 98 ≤ es.length)
    (hn : (kindOfC es).isNode = true) {j : Fin 9} (hj : vM (kindOfC es) es j ≠ zfL M zw L es j) :
    L3BadN M zw L es := ⟨hl, hn, j, hj⟩

/-! ## `DF4a` -/

/-- Control (positive): the background dooms every non-`msD` phase from 2 to 12. -/
theorem DF4a_of_bgA {P : Front4a} {L es : Log} (h : P.BgA L es) :
    ∀ k, 2 ≤ k → k ≤ 12 → k ≠ 3 → k ≠ 11 → DF4a P k L es := by
  intro k h1 h2 h3 h11
  interval_cases k <;> simp_all [DF4a, D2F4, D10F4, bgZ4, bg5_4, bg10_4]

/-- Control (negative): phases 0, 1 and those past S2 are not P4a's. -/
theorem not_DF4a_out {P : Front4a} {L es : Log} {k : ℕ} (hk : k < 2 ∨ 13 ≤ k) :
    ¬ DF4a P k L es := by
  rcases hk with hk | hk
  · interval_cases k <;> simp [DF4a]
  · obtain ⟨j, rfl⟩ : ∃ j, k = j + 13 := ⟨k - 13, by omega⟩
    simp [DF4a]

/-- Control (negative): the classification separates the items. -/
theorem frontCls4a_neg : frontCls4a 67 .squeeze = false ∧ frontCls4a 16 (.absorb 48) = false := by
  unfold frontCls4a rndCls4a absPts4a sqPts4a rndPh4a fsRnd4
  rw [fsRanges4_eq]; decide +kernel

/-- Control (positive): Z3's first squeeze and Zend's absorb are classified. -/
theorem frontCls4a_pos : frontCls4a 16 .squeeze = true ∧ frontCls4a 67 (.absorb 48) = true := by
  unfold frontCls4a rndCls4a absPts4a sqPts4a rndPh4a fsRnd4
  rw [fsRanges4_eq]; decide +kernel

/-! ## `SameStab4` -/

/-- Control (negative): a predicate of the charging log itself is not stable. -/
theorem not_ss_log4 : ¬ SameStab4 0 fun L _ => L = [] := fun h => by
  have := (h [] [(ByteArray.empty, 0)] [] (Nat.zero_le _)
    ⟨fun _ h => absurd h (Nat.not_lt_zero _), fun _ _ _ h => absurd h (Nat.not_lt_zero _)⟩).mp rfl
  simp at this

theorem ss_false4_ctrl : SameStab4 3 fun _ _ => False := ss_false4 3

end FR.Snd.P4a
