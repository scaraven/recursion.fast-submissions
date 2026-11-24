import LvmQSig

-- ===== merged from `LvmQSigChain` (GOLF module merge: `LvmQSigChain.lean` is now a stub importing `LvmQSigPre`) =====
section

/-!
# `Q_sig`: what the loop templates compute

New for lvm (WP-12). Per template of `LvmQSig`, in every memory where its rows hold:
* `chain_spec`: a WOTS chain's step inputs and end are the mux of `[d < s]` (FR `wots_chain_sound`'s
  `hsel`/`hend` hypotheses);
* `csf_spec`: the checksum factor is `x^{3 − d}`; `pt_spec`: a product-tree level; `t_spec`: a
  doubling level of `T`;
* `path_spec`: the path mux orders `(cur, sib)` by the index bit.
-/

set_option autoImplicit false

namespace Lvm.QSig

open Lvm Lvm.Loop Lvm.Loop.Build

/-- The value of row `t`'s cell at iteration `jf` of a loop. -/
abbrev cv (M : Mem) (o : LoopOut) (t jf : Nat) : FK := M.k (o.cell t jf).n

/-- A Boolean `K` value as a number. -/
def bnat (b : FK) : Nat := if b = 1 then 1 else 0

theorem FK.one_add_one : (1 : FK) + 1 = 0 := FK.add_self 1

theorem mux_eq {s a b : FK} (hs : s = 0 ∨ s = 1) :
    s * (a + b) + b = if s = 1 then a else b := by
  rcases hs with rfl | rfl
  · simp [show ¬ ((0 : FK) = 1) from by decide]
  · simp only [one_mul, if_true]; rw [add_assoc, FK.add_self, add_zero]

section chain

variable {c : Ctx} {M : Mem} {dims : List Nat} {p : Ptr} {d0 d1 Z O : Opd}
  {ots o1 o2 o3 : Nat → Opd}

/-- **One WOTS chain**: with Boolean digit bits `b₀, b₁` (`d = b₀ + 2 b₁`), lane `l`'s step-2 input
is `out₁` if `d < 1`, its step-3 input `out₂` if `d < 2`, its end `out₃` if `d < 3`, else the signed
value `ots`. -/
theorem chain_spec
    (h : SegsHold c M p (loop dims (chainTpl d0 d1 Z O ots o1 o2 o3) p).2)
    {jf : Nat} (hjf : jf < 2 ^ dims.sum)
    (hK : ∀ x ∈ [d0, d1, Z, O], OpdK (loop dims (chainTpl d0 d1 Z O ots o1 o2 o3) p).1 x)
    (hKl : ∀ l < 4, ∀ x ∈ [ots l, o1 l, o2 l, o3 l],
      OpdK (loop dims (chainTpl d0 d1 Z O ots o1 o2 o3) p).1 x)
    (hZ : ov M (loop dims (chainTpl d0 d1 Z O ots o1 o2 o3) p).1 jf Z = 0)
    (hO : ov M (loop dims (chainTpl d0 d1 Z O ots o1 o2 o3) p).1 jf O = 1)
    {b0 b1 : FK} (hv0 : ov M (loop dims (chainTpl d0 d1 Z O ots o1 o2 o3) p).1 jf d0 = b0)
    (hv1 : ov M (loop dims (chainTpl d0 d1 Z O ots o1 o2 o3) p).1 jf d1 = b1)
    (hb0 : b0 = 0 ∨ b0 = 1) (hb1 : b1 = 0 ∨ b1 = 1) {l : Nat} (hl : l < 4) :
    cv M (loop dims (chainTpl d0 d1 Z O ots o1 o2 o3) p).1 (8 + l) jf =
        (if bnat b0 + 2 * bnat b1 < 1 then ov M (loop dims (chainTpl d0 d1 Z O ots o1 o2 o3) p).1 jf (o1 l)
          else ov M (loop dims (chainTpl d0 d1 Z O ots o1 o2 o3) p).1 jf (ots l)) ∧
      cv M (loop dims (chainTpl d0 d1 Z O ots o1 o2 o3) p).1 (16 + l) jf =
        (if bnat b0 + 2 * bnat b1 < 2 then ov M (loop dims (chainTpl d0 d1 Z O ots o1 o2 o3) p).1 jf (o2 l)
          else ov M (loop dims (chainTpl d0 d1 Z O ots o1 o2 o3) p).1 jf (ots l)) ∧
      cv M (loop dims (chainTpl d0 d1 Z O ots o1 o2 o3) p).1 (24 + l) jf =
        (if bnat b0 + 2 * bnat b1 < 3 then ov M (loop dims (chainTpl d0 d1 Z O ots o1 o2 o3) p).1 jf (o3 l)
          else ov M (loop dims (chainTpl d0 d1 Z O ots o1 o2 o3) p).1 jf (ots l)) := by
  set o := (loop dims (chainTpl d0 d1 Z O ots o1 o2 o3) p).1 with ho
  have hlen : (chainTpl d0 d1 Z O ots o1 o2 o3).length = 28 := by simp [chainTpl]
  have hcur : ∀ t < 28, OpdK o (.cur t) := fun t ht => by
    show ((chainTpl d0 d1 Z O ots o1 o2 o3).getD t default).ty = .K
    have hm : (chainTpl d0 d1 Z O ots o1 o2 o3).map LRow.ty = List.replicate 28 .K := rfl
    rw [← List.getD_map (f := LRow.ty), hm]
    rw [List.getD_eq_getElem _ _ (by rw [List.length_replicate]; exact ht), List.getElem_replicate]
  have ovc : ∀ t < 28, ov M o jf (.cur t) = cv M o t jf := fun t ht =>
    ov_cur M o hjf t (hcur t ht)
  have hd0 := hK d0 (by simp); have hd1 := hK d1 (by simp)
  have hZK := hK Z (by simp); have hOK := hK O (by simp)
  obtain ⟨hots, ho1, ho2, ho3⟩ : OpdK o (ots l) ∧ OpdK o (o1 l) ∧ OpdK o (o2 l) ∧ OpdK o (o3 l) :=
    ⟨hKl l hl _ (by simp), hKl l hl _ (by simp), hKl l hl _ (by simp), hKl l hl _ (by simp)⟩
  have r0 := loopK_lin h hjf (t := 0) (by (clear * - hlen; omega)) rfl hd0 hd0
  have r1 := loopK_lin h hjf (t := 1) (by (clear * - hlen; omega)) rfl hd1 hd1
  have r2 := loopK_mad h hjf (t := 2) (by (clear * - hlen; omega)) rfl (hcur 0 (by (clear * -; omega))) (hcur 1 (by (clear * -; omega))) hZK
  have r3 := loopK_mad h hjf (t := 3) (by (clear * - hlen; omega)) rfl hd0 hd1 hOK
  have g4 : (chainTpl d0 d1 Z O ots o1 o2 o3).getD (4 + l) default = lr 1 0 (o1 l) (ots l) := by
    interval_cases l <;> rfl
  have g8 : (chainTpl d0 d1 Z O ots o1 o2 o3).getD (8 + l) default = mr (.cur 2) (.cur (4 + l)) (ots l) := by
    interval_cases l <;> rfl
  have g12 : (chainTpl d0 d1 Z O ots o1 o2 o3).getD (12 + l) default = lr 1 0 (o2 l) (ots l) := by
    interval_cases l <;> rfl
  have g16 : (chainTpl d0 d1 Z O ots o1 o2 o3).getD (16 + l) default =
      mr (.cur 1) (.cur (12 + l)) (ots l) := by
    interval_cases l <;> rfl
  have g20 : (chainTpl d0 d1 Z O ots o1 o2 o3).getD (20 + l) default = lr 1 0 (o3 l) (ots l) := by
    interval_cases l <;> rfl
  have g24 : (chainTpl d0 d1 Z O ots o1 o2 o3).getD (24 + l) default =
      mr (.cur 3) (.cur (20 + l)) (ots l) := by
    interval_cases l <;> rfl
  have r4 := loopK_lin h hjf (by (clear * - hl hlen; omega)) g4 ho1 hots
  have r8 := loopK_mad h hjf (by (clear * - hl hlen; omega)) g8 (hcur 2 (by (clear * -; omega))) (hcur _ (by (clear * - hl; omega))) hots
  have r12 := loopK_lin h hjf (by (clear * - hl hlen; omega)) g12 ho2 hots
  have r16 := loopK_mad h hjf (by (clear * - hl hlen; omega)) g16 (hcur 1 (by (clear * -; omega))) (hcur _ (by (clear * - hl; omega))) hots
  have r20 := loopK_lin h hjf (by (clear * - hl hlen; omega)) g20 ho3 hots
  have r24 := loopK_mad h hjf (by (clear * - hl hlen; omega)) g24 (hcur 3 (by (clear * -; omega))) (hcur _ (by (clear * - hl; omega))) hots
  simp only [← ho] at r0 r1 r2 r3 r4 r8 r12 r16 r20 r24
  simp only [one_mul, zero_mul, add_zero] at r0 r1 r4 r12 r20
  have e2 := ovc 2 (by (clear * -; omega)); have e1 := ovc 1 (by (clear * -; omega)); have e3 := ovc 3 (by (clear * -; omega))
  have e0 := ovc 0 (by (clear * -; omega)); have e4 := ovc (4 + l) (by (clear * - hl; omega))
  have e12 := ovc (12 + l) (by (clear * - hl; omega)); have e20 := ovc (20 + l) (by (clear * - hl; omega))
  simp only [cv] at e0 e1 e2 e3 e4 e12 e20 ⊢
  rw [e0, e1, hZ, add_zero] at r2
  rw [hO] at r3
  rw [e2, e4, r2, r0, r1, r4] at r8
  rw [e1, e12, r1, r12] at r16
  rw [e3, e20, r3, r20] at r24
  rw [r8, r16, r24]
  rw [hv0, hv1] at *
  have h10 : ¬ ((1 : FK) = 0) := by decide
  have h01 : ¬ ((0 : FK) = 1) := by decide
  rcases hb0 with rfl | rfl <;> rcases hb1 with rfl | rfl <;>
    simp [bnat, h01, FK.one_add_one, add_assoc, FK.add_self]

end chain

end Lvm.QSig
end
-- ===== end of `LvmQSigChain` =====

/-!
# `Q_sig`: constants and the table `T[i] = i << 8`

New for lvm (WP-12). `gPre_spec`: in every memory where `gPre`'s rows hold, `Z = 0`, `O = 1` and
the cells `Tbase + i` hold `i << 8` (`i < 128`), the byte `i` a chain step's lane 1 carries.
-/

set_option autoImplicit false

namespace Lvm.QSig

open Lvm Lvm.Loop Lvm.Loop.Build

/-- The doubling levels' values: level `d + 1` at index `q` is level `d` at `q / 2` plus bit
`q mod 2` at `x^{14 − d}`. -/
def tv : Nat → Nat → FK
  | 0, _ => 0
  | d + 1, q => tv d (q / 2) + (if q % 2 = 1 then w64 ((1 : UInt64) <<< (14 - d : Nat).toUInt64) else 0)

/-- `tv` on the words as natural numbers (GOLF3: the kernel computes `ℕ`'s operations natively). -/
private def tvN : Nat → Nat → Nat
  | 0, _ => 0
  | d + 1, q => tvN d (q / 2) ^^^ (if q % 2 = 1 then ((1 : UInt64) <<< (14 - d : Nat).toUInt64).toNat else 0)

private theorem tv_toNat : ∀ d q : Nat, (tv d q).val.toNat = tvN d q
  | 0, _ => rfl
  | d + 1, q => by
    rw [tv, tvN, FK.add_toNat, tv_toNat d]
    split_ifs <;> rfl

theorem tv_seven : ∀ q < 128, tv 7 q = w64 (q.toUInt64 <<< (8 : Nat).toUInt64) := by
  have h : ∀ q < 128, tvN 7 q = (q.toUInt64 <<< (8 : Nat).toUInt64).toNat := by decide +kernel
  intro q hq
  rw [FK.eq_iff_toNat, tv_toNat]
  exact h q hq

theorem cell_lin1 (o : LoopOut) (t jf : Nat) (ht : t < o.tpl.length)
    (hw : ∀ r ∈ o.tpl, r.op ≠ .assert0 ∧ r.ty = .K) :
    (o.cell t jf).n = o.p.k + t + o.tpl.length * jf := by
  have hall : ∀ r ∈ o.tpl, LRow.w .K r = 1 := fun r hr => by
    obtain ⟨h1, h2⟩ := hw r hr
    obtain ⟨op, ty, args⟩ := r
    simp only at h1 h2; subst h2
    cases op <;> simp_all [LRow.w, Row.w, Row.writes]
  have hK : (o.tpl.getD t default).ty = .K := by
    rw [List.getD_eq_getElem _ _ ht]; exact (hw _ (List.getElem_mem ht)).2
  have hrank : lrank .K o.tpl t = t := by
    unfold lrank
    rw [List.map_congr_left (l := o.tpl.take t) (g := fun _ => 1)
      (fun r hr => hall r (List.mem_of_mem_take hr))]
    simp; (clear * - ht; omega)
  have htw : ltw .K o.tpl = o.tpl.length := by
    unfold ltw
    rw [List.map_congr_left (g := fun _ => 1) hall]
    simp
  simp only [LoopOut.cell, hK, Ptr.at, hrank, htw]

/-- **One doubling level.** -/
theorem tlev_spec {c : Ctx} {M : Mem} {d : Nat} {src : Opd} {Zn : Nat} {p : Ptr}
    (h : SegsHold c M p (loop [d] (tTpl d src Zn) p).2) (hs : OpdK (loop [d] (tTpl d src Zn) p).1 src)
    (hZ : M.k Zn = 0) {q : Nat} (hq : q < 2 ^ (d + 1)) :
    M.k (p.k + q) = ov M (loop [d] (tTpl d src Zn) p).1 (q / 2) src +
      (if q % 2 = 1 then w64 ((1 : UInt64) <<< (14 - d : Nat).toUInt64) else 0) := by
  have hy : q / 2 < 2 ^ ([d].sum) := by simp; rw [pow_succ] at hq; (clear * - hq; omega)
  have hZK : OpdK (loop [d] (tTpl d src Zn) p).1 (oA Zn) := rfl
  have hc : ∀ t < 2, ((loop [d] (tTpl d src Zn) p).1.cell t (q / 2)).n = p.k + t + 2 * (q / 2) :=
    fun t ht => cell_lin1 _ t _ (by simpa [loop_apply, tTpl] using ht)
      (fun r hr => by simp [loop_apply, tTpl] at hr; rcases hr with rfl | rfl <;> simp)
  rcases Nat.mod_two_eq_zero_or_one q with h0 | h1
  · have r := loopK_lin h hy (t := 0) (by simp [tTpl]) rfl hs hZK
    rw [hc 0 (by (clear * -; omega)), ov_oA, hZ] at r
    rw [show p.k + q = p.k + 0 + 2 * (q / 2) by (clear * - h0; omega), r, h0]; simp
  · have r := loopK_lin h hy (t := 1) (by simp [tTpl]) rfl hs hZK
    rw [hc 1 (by (clear * -; omega)), ov_oA, hZ] at r
    rw [show p.k + q = p.k + 1 + 2 * (q / 2) by (clear * - h1; omega), r, h1]; simp

end Lvm.QSig

namespace Lvm.QSig
open Lvm Lvm.Loop Lvm.Loop.Build

theorem const_K_spec {c : Ctx} {M : Mem} {p : Ptr} {k' : FK} {a : Nat}
    (h : SegsHold c M p (const .K k' (kc a) p).2) : M.k (const .K k' (kc a) p).1.n = k' := by
  have := linK_spec h
  simp only [const, lin, rowRes, Ptr.at] at this ⊢
  rw [this, one_mul, FK.add_self, zero_add]

/-- **Sequencing, hold only**: a postcondition of `m >>= f` from `m`'s rows and `f`'s at any pointer. -/
theorem seqH {α β : Type} {c : Ctx} {M : Mem} {m : BM α} {f : α → BM β} {p : Ptr} {Q : β → Prop}
    (h : SegsHold c M p ((m >>= f) p).2)
    (k : SegsHold c M p (m p).2 → ∀ p', SegsHold c M p' (f (m p).1 p').2 → Q (f (m p).1 p').1) :
    Q ((m >>= f) p).1 := by
  rw [hold_bind] at h
  rw [bind_apply]
  exact k h.1 _ h.2

/-- **Sequencing**: rows and assertions. -/
theorem seqHA {α β : Type} {c : Ctx} {M : Mem} {m : BM α} {f : α → BM β} {p : Ptr} {Q : β → Prop}
    (h : SegsHold c M p ((m >>= f) p).2) (hA : SegsAssert M p ((m >>= f) p).2)
    (k : SegsHold c M p (m p).2 → SegsAssert M p (m p).2 → ∀ p', SegsHold c M p' (f (m p).1 p').2 →
      SegsAssert M p' (f (m p).1 p').2 → Q (f (m p).1 p').1) :
    Q ((m >>= f) p).1 := by
  rw [hold_bind] at h
  rw [assert_bind] at hA
  rw [bind_apply]
  exact k h.1 hA.1 _ h.2 hA.2

/-- A doubling level read from the previous level's cells. -/
theorem tlev_next {c : Ctx} {M : Mem} {d : Nat} {b Zn : Nat} {p : Ptr}
    (h : SegsHold c M p (loop [d + 1] (tTpl (d + 1) (oS b 1) Zn) p).2) (hZ : M.k Zn = 0)
    (hprev : ∀ q < 2 ^ (d + 1), M.k (b + q) = tv (d + 1) q) :
    ∀ q < 2 ^ (d + 2), M.k (p.k + q) = tv (d + 2) q := by
  intro q hq
  rw [tlev_spec h rfl hZ hq, ov_oS _ _ rfl (by rw [pow_succ] at hq; (clear * - hq; omega)), Nat.one_mul,
    hprev _ (by rw [pow_succ] at hq; (clear * - hq; omega))]
  rfl

/-- What `gPre` gives. -/
def PreOk (M : Mem) (r : Cell × Cell × List LoopOut) : Prop :=
  r.1.ty = .K ∧ r.2.1.ty = .K ∧ M.k r.1.n = 0 ∧ M.k r.2.1.n = 1 ∧
    ∀ i < 128, M.k (Tbase r + i) = w64 (i.toUInt64 <<< (8 : Nat).toUInt64)

theorem gPre_spec {c : Ctx} {M : Mem} {p : Ptr} {I : SigIn} (h : SegsHold c M p (gPre I p).2) :
    PreOk M (gPre I p).1 := by
  unfold gPre at h ⊢
  refine seqH (Q := PreOk M) h fun hZ p1 h => ?_
  have eZ := const_K_spec hZ
  have tZ : (const .K 0 (kc I.flag) p).1.ty = .K := rfl
  generalize const .K 0 (kc I.flag) p = rZ at eZ tZ h ⊢
  refine seqH (Q := PreOk M) h fun hO p2 h => ?_
  have eO := const_K_spec hO
  have tO : (const .K 1 (kc I.flag) p1).1.ty = .K := rfl
  generalize const .K 1 (kc I.flag) p1 = rO at eO tO h ⊢
  refine seqH (Q := PreOk M) h fun h0 p3 h => ?_
  have e0 : ∀ q < 2 ^ 1, M.k (p2.k + q) = tv 1 q := fun q hq => by
    rw [tlev_spec h0 rfl eZ hq, ov_oA, eZ]; rfl
  replace e0 : ∀ q < 2 ^ 1, M.k ((loop [0] (tTpl 0 (oA rZ.1.n) rZ.1.n) p2).1.p.k + q) = tv 1 q := e0
  generalize loop [0] (tTpl 0 (oA rZ.1.n) rZ.1.n) p2 = r0 at e0 h ⊢
  refine seqH (Q := PreOk M) h fun h1 p4 h => ?_
  have e1 := tlev_next (d := 0) h1 eZ e0
  replace e1 : ∀ q < 2 ^ 2, M.k ((loop [1] (tTpl 1 (oS r0.1.p.k 1) rZ.1.n) p3).1.p.k + q) = tv 2 q := e1
  generalize loop [1] (tTpl 1 (oS r0.1.p.k 1) rZ.1.n) p3 = r1 at e1 h ⊢
  refine seqH (Q := PreOk M) h fun h2 p5 h => ?_
  have e2 := tlev_next (d := 1) h2 eZ e1
  replace e2 : ∀ q < 2 ^ 3, M.k ((loop [2] (tTpl 2 (oS r1.1.p.k 1) rZ.1.n) p4).1.p.k + q) = tv 3 q := e2
  generalize loop [2] (tTpl 2 (oS r1.1.p.k 1) rZ.1.n) p4 = r2 at e2 h ⊢
  refine seqH (Q := PreOk M) h fun h3 p6 h => ?_
  have e3 := tlev_next (d := 2) h3 eZ e2
  replace e3 : ∀ q < 2 ^ 4, M.k ((loop [3] (tTpl 3 (oS r2.1.p.k 1) rZ.1.n) p5).1.p.k + q) = tv 4 q := e3
  generalize loop [3] (tTpl 3 (oS r2.1.p.k 1) rZ.1.n) p5 = r3 at e3 h ⊢
  refine seqH (Q := PreOk M) h fun h4 p7 h => ?_
  have e4 := tlev_next (d := 3) h4 eZ e3
  replace e4 : ∀ q < 2 ^ 5, M.k ((loop [4] (tTpl 4 (oS r3.1.p.k 1) rZ.1.n) p6).1.p.k + q) = tv 5 q := e4
  generalize loop [4] (tTpl 4 (oS r3.1.p.k 1) rZ.1.n) p6 = r4 at e4 h ⊢
  refine seqH (Q := PreOk M) h fun h5 p8 h => ?_
  have e5 := tlev_next (d := 4) h5 eZ e4
  replace e5 : ∀ q < 2 ^ 6, M.k ((loop [5] (tTpl 5 (oS r4.1.p.k 1) rZ.1.n) p7).1.p.k + q) = tv 6 q := e5
  generalize loop [5] (tTpl 5 (oS r4.1.p.k 1) rZ.1.n) p7 = r5 at e5 h ⊢
  refine seqH (Q := PreOk M) h fun h6 p9 _ => ?_
  have e6 := tlev_next (d := 5) h6 eZ e5
  replace e6 : ∀ q < 2 ^ 7, M.k ((loop [6] (tTpl 6 (oS r5.1.p.k 1) rZ.1.n) p8).1.p.k + q) = tv 7 q := e6
  generalize loop [6] (tTpl 6 (oS r5.1.p.k 1) rZ.1.n) p8 = r6 at e6 ⊢
  refine ⟨tZ, tO, eZ, eO, fun i hi => ?_⟩
  show M.k (r6.1.p.k + i) = _
  rw [e6 i hi, tv_seven i hi]

end Lvm.QSig
