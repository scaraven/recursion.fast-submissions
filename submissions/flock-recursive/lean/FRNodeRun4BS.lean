-- New for `flock-recursive` (IMPC2 §7 step 3; track IMPC2b): the decomposition rows give `StmtBits`; the
-- rows at the seed's ask are among the template's.
import FRNodeRun4BR

/-!
# The decomposition rows' facts

`bitTGB` emits the decomposition rows (`globRows`) once, at the seed's ask (`k = 0`):

* **`seed_rows`**: the program's first ask is the seed's; its template rows are among `askRowsX`'s
  (`first_ask`), so `globRows` holds wherever the template's rows do;
* **`stmtBits_of_glob`**: the statement element rows (`stElRow`) with `PfCells` and Boolean bit cells
  give `StmtBits`: each statement element is its tag part plus `Σ e_j·cell`, so its bits are the cells'
  (`bit_bitsLin`) and the bits no cell takes are zero.
-/

namespace FR
namespace N4s
open RecursionFast Rev4 Circ TEval W4 Tpl

/-! ## The rows at the first ask -/

/-- **The first ask's template rows are among `askRowsX`'s** (its ask index is `0`). -/
theorem first_ask (X : Ext) (P : Params) (A : AT) : ∀ (ops : List Op) (cs : CS) (pre : Option Op) {it : Item},
    (ops.filterMap Op.item?).head? = some it →
    ∃ c pre' op, op.item? = some it ∧ ∀ r ∈ A.rows P c pre' op 0, r ∈ askRowsX X P A cs pre 0 ops
  | [], _, _, _, h => by simp at h
  | op :: ops, cs, pre, it, h => by
    rw [askRowsX_cons]
    cases hi : op.item? with
    | some it' =>
      simp only [List.filterMap_cons, hi, List.head?_cons, Option.some.injEq] at h
      subst h
      exact ⟨_, pre, op, hi, fun r hr => List.mem_append_left _ (by rw [if_pos (by simp [hi])]; exact hr)⟩
    | none =>
      simp only [List.filterMap_cons, hi] at h
      obtain ⟨c, pre', op', ho, hr⟩ := first_ask X P A ops _ (some op) h
      refine ⟨c, pre', op', ho, fun r hr0 => List.mem_append_right _ ?_⟩
      convert hr r hr0 using 2
      simp

/-- **`globRows` hold** wherever prototype `π`'s template rows do, when the template has `bitTGB`'s rows. -/
theorem seed_rows {A : AT} {π : ℕ} {T : BTab} {Xa : Ext} {w : Asg}
    (hrA : ∀ c pre op k, ∀ r ∈ bitRowsB T Xa π (protoP π) c pre op k, r ∈ A.rows (protoP π) c pre op k)
    (hask : ∀ r ∈ askRowsP A π, r.Holds w) : ∀ r ∈ globRows T (protoP π) π, r.Holds w := by
  obtain ⟨rest, hr, -⟩ := itemsOf_seq4_al
  obtain ⟨c, pre', op, ho, hm⟩ := first_ask (Xof π) (protoP π) A (protoProg π).ops (CS.init (baseR π)) none
    (it := .seed) (by rw [protoProg_items, hr]; rfl)
  cases op <;> simp only [Op.item?, reduceCtorEq, Option.some.injEq] at ho
  intro r hr0
  exact hask r (hm r (hrA _ _ _ _ r (by simp only [bitRowsB, if_true]; exact hr0)))

/-! ## The statement's bits -/

theorem eBitT_get {j : ℕ} (hj : j < 128) : eBitT.getD j 0 = eBit j := by
  unfold eBitT; simp [hj]

theorem bitsLin_eq {L : List (ℕ × ℕ)} (h : ∀ p ∈ L, p.1 < 128) : bitsLin L = L.map fun p => (p.2, eBit p.1) := by
  unfold bitsLin
  exact List.map_congr_left fun p hp => by rw [eBitT_get (h p hp)]

theorem nodup_fst_filterMap {β : Type} : ∀ (l : List ℕ), l.Nodup → ∀ (f : ℕ → Option (ℕ × β)),
    (∀ j y, f j = some y → y.1 = j) → ((l.filterMap f).map Prod.fst).Nodup
  | [], _, _, _ => List.nodup_nil
  | j :: l, hl, f, hf => by
    have ih := nodup_fst_filterMap l (List.nodup_cons.1 hl).2 f hf
    cases h : f j with
    | none => simpa [List.filterMap_cons, h] using ih
    | some y =>
      rw [List.filterMap_cons, h, List.map_cons, List.nodup_cons]
      refine ⟨fun hm => ?_, ih⟩
      obtain ⟨z, hz, hz1⟩ := List.mem_map.1 hm
      obtain ⟨a, ha, hfa⟩ := List.mem_filterMap.1 hz
      have h1 : y.1 = j := hf j y h
      have h2 : z.1 = a := hf a z hfa
      have : a = j := by rw [← h2, hz1, h1]
      exact (List.nodup_cons.1 hl).1 (this ▸ ha)

theorem tagF_bit (t : UInt8) {j : ℕ} (hj : j < 128) : (tagF t).bit j = (decide (j < 8) && t.toNat.testBit j) := by
  simp only [tagF, F.bit]
  split
  · rw [show t.toUInt64.toNat = t.toNat from UInt8.toNat_toUInt64 t]
    by_cases h8 : j < 8
    · simp [h8]
    · simp only [h8, decide_false, Bool.false_and]
      exact Nat.testBit_lt_two_pow (lt_of_lt_of_le t.toNat_lt (Nat.pow_le_pow_right (by norm_num) (by omega)))
  · rw [show ((0 : UInt64)).toNat = 0 from rfl, Nat.zero_testBit]; simp; omega

theorem byte_eq_of_testBit {x y : UInt8} (h : ∀ t < 8, x.toNat.testBit t = y.toNat.testBit t) : x = y := by
  apply UInt8.toNat_inj.1
  apply Nat.eq_of_testBit_eq; intro t
  by_cases ht : t < 8
  · exact h t ht
  · have hp : 2 ^ 8 ≤ 2 ^ t := Nat.pow_le_pow_right (by norm_num) (by omega)
    rw [Nat.testBit_lt_two_pow (lt_of_lt_of_le x.toNat_lt hp), Nat.testBit_lt_two_pow (lt_of_lt_of_le y.toNat_lt hp)]

/-- **`StmtBits` from the statement element rows** (`globRows`), arena₁'s windows (`PfCells`) and the
bit area's Boolean cells. -/
theorem stmtBits_of_glob {T : BTab} {P : Params} {w : Asg} {π : ℕ} {inp : Input} (hone : P.one.ev w = 1)
    (hpc : PfCells w π inp) (hB : ∀ c < arNb, w (bitC π c) = 0 ∨ w (bitC π c) = 1)
    (hg : ∀ r ∈ globRows T P π, r.Holds w) : StmtBits T w π inp.π := by
  unfold globRows at hg
  cases hst : T.st with
  | none =>
    simp only [hst] at hg
    exact absurd (hg _ (List.mem_append_right _ List.mem_cons_self)) (failRT_not hone)
  | some s =>
    simp only [hst] at hg
    have hck : 1 ≤ s.z ∧ s.z ≤ s.L ∧ s.L % 16 = 0 ∧ T.stmtB + 8 * s.z ≤ arNb + 8 := by
      by_contra hn
      rw [if_neg hn] at hg
      exact failRT_not hone (hg _ (List.mem_append_right _ (List.mem_append_left _ List.mem_cons_self)))
    -- the cell bit statement bit `128·kk + j` takes, if any
    let cb : ℕ → Bool := fun b => match T.stCell b with
      | some (some x) => decide (w (bitC π x) = 1)
      | _ => false
    -- element `kk`'s window and its bits
    have hel : ∀ kk < s.L / 16, ∀ j < 128,
        (byteAt inp.π (s.so + 16 * kk + j / 8)).toNat.testBit (j % 8) =
          ((decide (kk = 0) && decide (j < 8) && s.t.toNat.testBit j) ^^ cb (128 * kk + j)) := by
      intro kk hkk j hj
      have hrow := hg (stElRow T P π s kk) (List.mem_append_right _ (List.mem_append_right _
        (List.mem_map.2 ⟨kk, List.mem_range.2 hkk, rfl⟩)))
      unfold stElRow at hrow
      split at hrow
      · rename_i e he
        set L := stCells T π kk with hL
        have hL1 : ∀ p ∈ L, p.1 < 128 ∧ ∃ x, T.stCell (128 * kk + p.1) = some (some x) ∧ p.2 = bitC π x := by
          intro p hp
          obtain ⟨j', hj', hf⟩ := List.mem_filterMap.1 hp
          split at hf
          · rename_i x hx
            cases hf; exact ⟨List.mem_range.1 hj', x, hx, rfl⟩
          · cases hf
        have hLb : ∀ p ∈ L, w p.2 = 0 ∨ w p.2 = 1 := by
          intro p hp
          obtain ⟨-, x, hx, hp2⟩ := hL1 p hp
          rw [hp2]
          refine hB x ?_
          simp only [BTab.stCell, hst] at hx
          split_ifs at hx with h1 h2 <;> cases hx
          omega
        have hnd : (L.map Prod.fst).Nodup := nodup_fst_filterMap _ List.nodup_range _ fun j y hy => by
          split at hy
          · cases hy; rfl
          · cases hy
        simp only [Row.Holds, hone, one_mul, ev_subN, Lin.ev_cell] at hrow
        rw [bitsLin_eq fun p hp => (hL1 p hp).1] at hrow
        have hwin : w (arC π e) = F.ofBytes (bytesAt inp.π (s.so + 16 * kk) 16) := hpc _ _ he
        have hw2 : F.ofBytes (bytesAt inp.π (s.so + 16 * kk) 16) =
            Lin.ev w (if kk = 0 then Lin.smul (tagF s.t) P.one else []) + Lin.ev w (L.map fun p => (p.2, eBit p.1)) := by
          rw [← hwin]; exact sub_eq_iff_eq_add.1 hrow
        have hbyte : (byteAt inp.π (s.so + 16 * kk + j / 8)).toNat.testBit (j % 8) =
            (F.ofBytes (bytesAt inp.π (s.so + 16 * kk) 16)).bit j := by
          rw [F.bit_ofBytes _ hj]; simp only [bytesAt, Vector.getElem_ofFn]
        rw [hbyte, hw2, F.bit_add, bit_bitsLin w L hLb (fun p hp => (hL1 p hp).1) hnd j hj]
        have hex : decide (∃ p ∈ L, p.1 = j ∧ w p.2 = 1) = cb (128 * kk + j) := by
          simp only [cb]
          split
          · rename_i x hx
            refine decide_eq_decide.2 ⟨?_, fun hw => ⟨(j, bitC π x), List.mem_filterMap.2 ⟨j, List.mem_range.2 hj,
              by rw [hx]⟩, rfl, hw⟩⟩
            rintro ⟨p, hp, rfl, hw⟩
            obtain ⟨-, x', hx', hp2⟩ := hL1 p hp
            rw [hx] at hx'; cases hx'; rwa [hp2] at hw
          · rename_i hx
            simp only [decide_eq_false_iff_not]
            rintro ⟨p, hp, rfl, -⟩
            obtain ⟨-, x', hx', -⟩ := hL1 p hp
            exact hx x' hx'
        rw [hex]
        congr 1
        split_ifs with hk0
        · subst hk0; simp only [Lin.ev_smul, hone, mul_one, tagF_bit _ hj]; simp
        · simp [F.bit_zero, hk0]
      · exact absurd hrow (failRT_not hone)
    have hcb0 : ∀ b, b < 8 → cb b = false := by
      intro b hb
      simp only [cb, BTab.stCell, hst]
      rw [if_neg (by omega), if_neg (by omega)]
    refine ⟨fun s' hs' => ?_, fun b x hx => ?_⟩
    · cases hs'.symm.trans hst
      apply byte_eq_of_testBit
      intro t ht
      have := hel 0 (by omega) t (by omega)
      rw [show s.so + 16 * 0 + t / 8 = s.so by omega, show t % 8 = t by omega,
        show 128 * 0 + t = t by omega, hcb0 t ht] at this
      rw [this]
      simp [ht]
    · have hx' := hx
      simp only [BTab.stCell, hst] at hx'
      have hb : b < 8 * s.L ∧ 8 ≤ b := by
        split_ifs at hx' with h1 h2 <;> first | omega | simp at hx'
      have hkk : b / 128 < s.L / 16 := by omega
      have := hel (b / 128) hkk (b % 128) (Nat.mod_lt _ (by norm_num))
      rw [show 128 * (b / 128) + b % 128 = b by omega] at this
      have hst8 : stBit T inp.π b = (byteAt inp.π (s.so + 16 * (b / 128) + b % 128 / 8)).toNat.testBit (b % 128 % 8) := by
        simp only [stBit, hst]
        rw [show s.so + b / 8 = s.so + 16 * (b / 128) + b % 128 / 8 by omega, show b % 8 = b % 128 % 8 by omega]
      have htag : (decide (b / 128 = 0) && decide (b % 128 < 8) && s.t.toNat.testBit (b % 128)) = false := by
        by_cases h0 : b / 128 = 0
        · simp [h0, show ¬ b % 128 < 8 by omega]
        · simp [h0]
      rw [htag, Bool.false_xor] at this
      rw [hst8, this]
      cases x with
      | none => simp only [SrcV, cb, hx]
      | some c =>
        simp only [SrcV, cb, hx]
        have hc : c < arNb := by
          split_ifs at hx' with h1 h2 <;> first | (simp only [Option.some.injEq] at hx'; omega) | simp at hx'
        first
          | done
          | (rcases hB c hc with h0 | h0 <;> simp [h0, Circ.bitF])

/-! ## The answers' bits -/

/-- A kind using an answer gets every one of its 256 bits a cell. -/
theorem ansCell_some {T : BTab} {ι : Kind} {k j x : ℕ} (h : T.ansCell ι k j = some x) {j' : ℕ} (hj' : j' < 256) :
    (T.ansCell ι k j').isSome = true := by
  unfold BTab.ansCell at h ⊢
  split at h
  · rename_i i q g hk
    dsimp only at h ⊢
    split_ifs at h with h1 h2 <;> (rw [if_pos ⟨h1.1, hj'⟩]; split <;> rfl)
  · cases h

theorem ansCell_lt {T : BTab} {ι : Kind} {k j x : ℕ} (h : T.ansCell ι k j = some x) :
    j < 256 ∧ ∃ i q g, T.ans.getD k none = some (i, q, g) := by
  unfold BTab.ansCell at h
  split at h
  · rename_i i q g hk
    dsimp only at h
    split_ifs at h with h1 h2 <;> exact ⟨h1.2, i, q, g, hk⟩
  · cases h

/-- **Each kind's map has a class representative** (`ansRows`' `cls`) whose class contains it. -/
theorem cls_ex {α : Type} [DecidableEq α] (ok : Kind → Bool) (m : Kind → α) (ι : Kind) (h : ok ι = true) :
    ∃ ι' ∈ kinds.filter (fun ι' => ok ι' && !(kinds.any fun κ => decide (kix κ < kix ι') && ok κ &&
        decide (m κ = m ι'))), m ι' = m ι ∧ (kinds.filter fun κ => ok κ && decide (m κ = m ι')).contains ι = true := by
  cases ι
  · exact ⟨.L32, by simp [kinds, kix, h], rfl, by simp [kinds, h]⟩
  · by_cases hL : ok .L32 = true ∧ m .L32 = m .P30
    · exact ⟨.L32, by simp [kinds, kix, hL.1], hL.2, by simp [kinds, h, hL.2]⟩
    · refine ⟨.P30, ?_, rfl, by simp [kinds, h]⟩
      simp only [kinds, kix, List.filter_cons, List.any_cons, List.any_nil, h]
      split_ifs <;> simp_all
  · by_cases hL : ok .L32 = true ∧ m .L32 = m .N30
    · exact ⟨.L32, by simp [kinds, kix, hL.1], hL.2, by simp [kinds, h, hL.2]⟩
    · by_cases hP : ok .P30 = true ∧ m .P30 = m .N30
      · refine ⟨.P30, ?_, hP.2, by simp [kinds, h, hP.2]⟩
        have : ¬ (ok .L32 = true ∧ m .L32 = m .P30) := fun h' => hL ⟨h'.1, h'.2.trans hP.2⟩
        simp only [kinds, kix, List.filter_cons, List.any_cons, List.any_nil]
        split_ifs <;> simp_all
      · refine ⟨.N30, ?_, rfl, by simp [kinds, h]⟩
        simp only [kinds, kix, List.filter_cons, List.any_cons, List.any_nil]
        split_ifs <;> simp_all

theorem nodup_zipIdx_filterMap (g : ℕ → ℕ) : ∀ (l : List (Option ℕ)) (n : ℕ),
    (((l.zipIdx n).filterMap fun p => p.1.map fun x => (p.2, g x)).map Prod.fst).Nodup ∧
      ∀ q ∈ ((l.zipIdx n).filterMap fun p => p.1.map fun x => (p.2, g x)).map Prod.fst, n ≤ q
  | [], _ => by simp
  | a :: l, n => by
    obtain ⟨ih1, ih2⟩ := nodup_zipIdx_filterMap g l (n + 1)
    rw [List.zipIdx_cons]
    cases a with
    | none =>
      simp only [List.filterMap_cons, Option.map_none]
      exact ⟨ih1, fun q hq => by have := ih2 q hq; omega⟩
    | some x =>
      simp only [List.filterMap_cons, Option.map_some, List.map_cons, List.nodup_cons, List.mem_cons]
      refine ⟨⟨fun hm => by have := ih2 n hm; omega, ih1⟩, fun q hq => ?_⟩
      rcases hq with rfl | hq
      · exact le_refl _
      · have := ih2 q hq; omega

/-- **One answer half's decomposition rows** (`ansRows`, half `c` on arena₁'s element `el`): a cell the
selected kind's map gives for bit `128c + j` is bit `j` of the element. -/
theorem ans_half {T : BTab} {P : Params} {w : Asg} {π k el c : ℕ} {ι : Kind} (hP : SelOk w P ι)
    (hB : ∀ c < arNb, w (bitC π c) = 0 ∨ w (bitC π c) = 1) (hR : ∀ r ∈ ansRows T P π k el c, r.Holds w)
    {j : ℕ} (hj : j < 128) {x : ℕ} (hx : T.ansCell ι k (128 * c + j) = some x) :
    w (bitC π x) = if (w (arC π el)).bit j then 1 else 0 := by
  unfold ansRows at hR
  simp only [kt_eq] at hR
  set m : Kind → List (Option ℕ) := fun ι => (List.range 128).map fun j => T.ansCell ι k (128 * c + j) with hm
  have hbound : (kinds.all fun ι => (m ι).all fun x => x.all (· < arNb)) = true := by
    by_contra hn
    rw [if_neg hn] at hR
    exact failRT_not hP.1 (hR _ (List.mem_append_left _ List.mem_cons_self))
  rw [if_pos hbound, List.nil_append] at hR
  have hok : ((m ι).all Option.isSome) = true := by
    rw [List.all_eq_true]; intro y hy
    simp only [hm] at hy
    obtain ⟨j', hj', rfl⟩ := List.mem_map.1 hy
    exact ansCell_some hx (by have := (ansCell_lt hx).1; have := List.mem_range.1 hj'; omega)
  obtain ⟨ι', hι', hmι, hcon⟩ := cls_ex (fun ι => (m ι).all Option.isSome) m ι hok
  have hrow := hR _ (List.mem_map.2 ⟨ι', hι', rfl⟩)
  try dsimp only at hrow
  have hlin : ∀ a : Lin, (a.ev w = 1) →
      (⟨a, subN (Lin.cell (arC π el)) (bitsLin (((m ι').zipIdx).filterMap fun p => p.1.map fun x => (p.2, bitC π x))), []⟩ : Row).Holds w →
      w (arC π el) = Lin.ev w (bitsLin (((m ι').zipIdx).filterMap fun p => p.1.map fun x => (p.2, bitC π x))) := by
    intro a ha hh
    simp only [Row.Holds, ha, one_mul, ev_subN, Lin.ev_cell, Lin.ev_nil] at hh
    exact sub_eq_zero.1 hh
  have heq : w (arC π el) = Lin.ev w (bitsLin (((m ι').zipIdx).filterMap fun p => p.1.map fun x => (p.2, bitC π x))) := by
    split_ifs at hrow
    · exact hlin _ hP.1 hrow
    · simp only [hm] at hcon
      exact hlin _ (by simp only [gateS_ev hP, hcon]; rfl) hrow
  rw [hmι] at heq
  set L := ((m ι).zipIdx).filterMap fun p => p.1.map fun x => (p.2, bitC π x) with hL
  have hmemL : ∀ p ∈ L, p.1 < 128 ∧ ∃ y, T.ansCell ι k (128 * c + p.1) = some y ∧ p.2 = bitC π y := by
    intro p hp
    obtain ⟨q, hq, hf⟩ := List.mem_filterMap.1 hp
    obtain ⟨y, hy, rfl⟩ := Option.map_eq_some_iff.1 hf
    obtain ⟨i, hi, he⟩ := List.mem_iff_getElem.1 hq
    simp only [List.length_zipIdx, hm, List.length_map, List.length_range] at hi
    have hq1 : q.1 = (m ι)[i]'(by simp [hm]; omega) := by rw [← he]; simp
    have hq2 : q.2 = i := by rw [← he]; simp
    refine ⟨by rw [hq2]; exact hi, y, ?_, rfl⟩
    rw [← hy, hq1, hq2]; simp [hm]
  have hLb : ∀ p ∈ L, w p.2 = 0 ∨ w p.2 = 1 := by
    intro p hp
    obtain ⟨-, y, hy, hp2⟩ := hmemL p hp
    rw [hp2]
    refine hB y ?_
    have := List.all_eq_true.1 hbound ι (by cases ι <;> simp [kinds])
    have := List.all_eq_true.1 this (some y) (by
      rw [← hy]; simp only [hm]; exact List.mem_map.2 ⟨_, List.mem_range.2 (hmemL p hp).1, rfl⟩)
    simpa using this
  have hnd := (nodup_zipIdx_filterMap (bitC π) (m ι) 0).1
  rw [bitsLin_eq fun p hp => (hmemL p hp).1] at heq
  have hjx : (j, bitC π x) ∈ L := by
    refine List.mem_filterMap.2 ⟨((m ι)[j]'(by simp [hm, hj]), j), ?_, ?_⟩
    · rw [List.mem_iff_getElem?]; exact ⟨j, by simp [List.getElem?_zipIdx, hm, hj]⟩
    · simp [hm, hx]
  exact decomp_cell w L hLb (fun p hp => (hmemL p hp).1) hnd heq hjx

theorem ans_fold_mem : ∀ (l : List ((ℕ × ℕ × ℕ) × ℕ)) (acc : Array (Option (ℕ × ℕ × ℕ))) (k : ℕ) (v : ℕ × ℕ × ℕ),
    (l.foldl (fun a p => a.set! p.1.1 (some (p.1.2.1, p.1.2.2, p.2))) acc).getD k none = some v →
    acc.getD k none = some v ∨ ∃ p ∈ l, p.1.1 = k
  | [], _, _, _, h => Or.inl h
  | p :: l, acc, k, v, h => by
    rw [List.foldl_cons] at h
    rcases ans_fold_mem l _ k v h with h1 | ⟨q, hq, hqk⟩
    · by_cases hk : p.1.1 = k
      · exact Or.inr ⟨p, List.mem_cons_self, hk⟩
      · left
        simp only [Array.getD_eq_getD_getElem?, Array.set!_eq_setIfInBounds, Array.getElem?_setIfInBounds_ne hk] at h1
        simpa [Array.getD_eq_getD_getElem?] using h1
    · exact Or.inr ⟨q, List.mem_cons_of_mem _ hq, hqk⟩

/-- **A table's answer places are `ansList`'s** (`mkTab`). -/
theorem mkTab_ans {ops : List Op} {G : Grp} {k : ℕ} {v : ℕ × ℕ × ℕ} (h : (mkTab ops G).ans.getD k none = some v) :
    ∃ a ∈ ansList, a.1 = k := by
  simp only [mkTab] at h
  rcases ans_fold_mem _ _ k v h with h1 | ⟨p, hp, hpk⟩
  · rw [Array.getD_eq_getD_getElem?, Array.getElem?_replicate] at h1
    split at h1 <;> simp at h1
  · have := List.mem_map_of_mem (f := Prod.fst) hp
    rw [List.zipIdx_map_fst] at this
    exact ⟨p.1, this, hpk⟩

/-- **`PosBits` from the answer decomposition rows** (`globRows`), arena₁'s answer halves (`hA`) and the
bit area's Boolean cells. -/
theorem posBits_of_glob {T : BTab} {P : Params} {w : Asg} {π : ℕ} {ι : Kind} {tr : Trace} (hP : SelOk w P ι)
    (hans : ∀ k v, T.ans.getD k none = some v → ∃ a ∈ ansList, a.1 = k)
    (hB : ∀ c < arNb, w (bitC π c) = 0 ∨ w (bitC π c) = 1) (hg : ∀ r ∈ globRows T P π, r.Holds w)
    (hA : ∀ k it e, itemsT[k]? = some it → tr[k]? = some e →
      w (arC π (aElT k it)) = dlo e.2 ∧ w (arC π (aElT k it + 1)) = dhi e.2) :
    PosBits T w π ι tr := by
  intro k j x e hx he
  obtain ⟨hj, i, q, g, hk⟩ := ansCell_lt hx
  obtain ⟨a, ha, rfl⟩ := hans _ _ hk
  have hga : ∀ r ∈ (match itemsT[a.1]? with
      | some it => ansRows T P π a.1 (aElT a.1 it) 0 ++ ansRows T P π a.1 (aElT a.1 it + 1) 1
      | none => [failRT P]), r.Holds w := fun r hr =>
    hg r (List.mem_append_left _ (List.mem_flatMap.2 ⟨a, ha, hr⟩))
  split at hga
  · rename_i it hit
    obtain ⟨hlo, hhi⟩ := hA _ _ _ hit he
    by_cases hc : j < 128
    · have := ans_half hP hB (fun r hr => hga r (List.mem_append_left _ hr)) hc (c := 0) (by simpa using hx)
      rw [this, hlo, bit_dlo _ hc]; rfl
    · have := ans_half hP hB (fun r hr => hga r (List.mem_append_right _ hr)) (j := j - 128) (by omega) (c := 1)
        (by rw [show 128 * 1 + (j - 128) = j by omega]; exact hx)
      rw [this, hhi, bit_dhi _ (by omega), show 128 + (j - 128) = j by omega]; rfl
  · exact absurd (hga _ List.mem_cons_self) (failRT_not hP.1)

end N4s
end FR
