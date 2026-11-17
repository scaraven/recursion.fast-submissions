/- `LvmQAccSoundOff` (GOLF2 off-path move, group 36 of 48): declarations that the certificate `certified`
   does not use, moved here verbatim (same names, same namespaces and context) from LvmQAccParts, LvmQAcc, LvmQAccSound,
   so that `Solution`'s import closure need not elaborate them. Import this module where they are needed;
   the name -> module map is GOLF2's moved.tsv. -/
import LvmQAccParts
import LvmQAcc
import LvmQAccSound
import LvmM3MidCertOff

-- ===== from `LvmQAccParts` =====

section
section
set_option autoImplicit false
namespace Lvm.QAcc
open Lvm Lvm.Loop Lvm.Loop.Build Lvm.QSig Lvm.Q1
variable {c : Ctx} {M : Mem}

theorem ldE_cell (q : Nat) (p : Ptr) : (ldE q p).1 = ec p.e := rfl

theorem ldE_val {q : Nat} {p : Ptr} (h : SegsHold c M p (ldE q p).2) :
    (ldE q p).1.val M = FE.ofK (M.k q) + FE.y * FE.ofK (M.k (q + 1)) + FE.y * FE.y * FE.ofK (M.k (q + 2)) :=
  loadE_spec h

/-- **A loaded stream scalar is `F`'s scalar** at byte `8q`. -/
theorem ldE_feAt {sig : ByteArray} {T q : Nat} {p : Ptr} (hS : Streamed M sig T) (hq : q + 2 < T)
    (h : SegsHold c M p (ldE q p).2) : (ldE q p).1.val M = feAt sig (8 * q) := by
  rw [ldE_val h]; exact load_feAt hS hq

end Lvm.QAcc
end
end

section
section
set_option autoImplicit false
namespace Lvm.QAcc
open Lvm Lvm.Loop Lvm.Loop.Build Lvm.QSig Lvm.Q1
variable {c : Ctx} {M : Mem}

theorem ldEs_length : ∀ (qs : List Nat) (p : Ptr), (ldEs qs p).1.length = qs.length
  | [], _ => rfl
  | q :: qs, p => by
    simp only [ldEs, List.map_cons, seqAll_cons_apply, List.length_cons] at *
    rw [show (seqAll (qs.map ldE) _).1.length = qs.length from ldEs_length qs _]

theorem ldEs_spec {sig : ByteArray} {T : Nat} (hS : Streamed M sig T) :
    ∀ (qs : List Nat) (p : Ptr), (∀ q ∈ qs, q + 2 < T) → SegsHold c M p (ldEs qs p).2 →
      ∀ i < qs.length, ((ldEs qs p).1.getD i default).ty = .E ∧
        ((ldEs qs p).1.getD i default).val M = feAt sig (8 * qs.getD i 0)
  | [], _, _, _, i, hi => absurd hi (by simp)
  | q :: qs, p, hq, h, i, hi => by
    simp only [ldEs, List.map_cons, seqAll_cons_apply] at h ⊢
    rw [segsHold_append, segsHold_append] at h
    cases i with
    | zero =>
      simp only [List.getD_cons_zero]
      exact ⟨rfl, ldE_feAt hS (hq q (by simp)) h.1⟩
    | succ i =>
      simp only [List.getD_cons_succ]
      exact ldEs_spec hS qs _ (fun q' h' => hq q' (by simp [h'])) h.2.1 i (by simpa using hi)

theorem ldEs_cells : ∀ (qs : List Nat) (p : Ptr) (i : Nat), i < qs.length →
    (ldEs qs p).1.getD i default = ec (p.e + i)
  | [], _, i, hi => absurd hi (by simp)
  | q :: qs, p, i, hi => by
    simp only [ldEs, List.map_cons, seqAll_cons_apply]
    cases i with
    | zero => simp [ldE_cell]
    | succ i =>
      simp only [List.getD_cons_succ]
      rw [show (seqAll (qs.map ldE) _).1.getD i default = _ from ldEs_cells qs _ i (by simpa using hi)]
      simp [ldE, loadE, rowRes, Ptr.adv, segsW, Seg.w, Row.w, Row.writes, Ptr.at]
      omega

end Lvm.QAcc
end
end

section
section
set_option autoImplicit false
namespace Lvm.QAcc
open Lvm Lvm.Loop Lvm.Loop.Build Lvm.QSig Lvm.Q1
variable {c : Ctx} {M : Mem}

theorem ldEsB_spec {sig : ByteArray} {T : Nat} (hS : Streamed M sig T) {qs : List Nat} {p : Ptr}
    (hq : ∀ q ∈ qs, q + 2 < T) (h : SegsHold c M p (ldEsB qs p).2) :
    ∀ i < qs.length, M.e ((ldEsB qs p).1 + i) = feAt sig (8 * qs.getD i 0) := by
  simp only [ldEsB, bind_apply, getPtr, pure_apply, List.nil_append, List.append_nil, Ptr.adv_nil] at h ⊢
  intro i hi
  have := (ldEs_spec hS qs p hq h i hi).2
  rwa [ldEs_cells qs p i hi] at this

/-- `ldEsB` on any `K` cells: the scalar of three consecutive cells. -/
theorem ldEsB_val {qs : List Nat} {p : Ptr} (h : SegsHold c M p (ldEsB qs p).2) :
    ∀ i < qs.length, M.e ((ldEsB qs p).1 + i) =
      ⟨M.k (qs.getD i 0), M.k (qs.getD i 0 + 1), M.k (qs.getD i 0 + 2)⟩ := by
  have key : ∀ (qs : List Nat) (p : Ptr), SegsHold c M p (ldEs qs p).2 → ∀ i < qs.length,
      ((ldEs qs p).1.getD i default).val M =
        ⟨M.k (qs.getD i 0), M.k (qs.getD i 0 + 1), M.k (qs.getD i 0 + 2)⟩ := by
    intro qs
    induction qs with
    | nil => intro p _ i hi; exact absurd hi (by simp)
    | cons q qs ih =>
      intro p h i hi
      simp only [ldEs, List.map_cons, seqAll_cons_apply] at h ⊢
      rw [segsHold_append, segsHold_append] at h
      cases i with
      | zero => simp only [List.getD_cons_zero]; rw [ldE_val h.1, FE_mk_eq]
      | succ i => simpa [ldEs] using ih _ h.2.1 i (by simpa using hi)
  simp only [ldEsB, bind_apply, getPtr, pure_apply, List.nil_append, List.append_nil, Ptr.adv_nil] at h ⊢
  intro i hi
  have := key qs p h i hi
  rwa [ldEs_cells qs p i hi] at this

/-- **`Σ_{i<n} x_i · y_i`**, `x_i` at the `E` cells `xb + xs·i`, `y_i` at the `K` cells `yb + ys·i`
(QA2's `dotG` with a `K` operand: a `2^a`-term running `muladd`, one difference row stopping at
`n`). -/
def dotGK (a n xb xs yb ys : Nat) : BM Cell := do
  let p ← getPtr
  let s ← loop [a] [⟨.muladd, .E, [.abs ⟨.E, xb, [xs]⟩, .abs ⟨.K, yb, [ys]⟩, .prev 0]⟩]
  add (s.cell 0 (n - 1)) (ec (p.e - 1))

theorem dotGK_spec {p : Ptr} {a n xb xs yb ys : Nat} (h : SegsHold c M p (dotGK a n xb xs yb ys p).2)
    (hp : 1 ≤ p.e) (hn : 1 ≤ n) (hna : n ≤ 2 ^ a) :
    (dotGK a n xb xs yb ys p).1.val M =
      ∑ i ∈ Finset.range n, M.e (xb + xs * i) * FE.ofK (M.k (yb + ys * i)) := by
  simp only [dotGK, bind_apply, getPtr, pure_apply, List.nil_append, Ptr.adv_nil] at h ⊢
  rw [segsHold_append] at h
  have hs := lin_spec h.2
  simp only [add] at hs ⊢
  rw [hs]
  have hstep : ∀ x < 2 ^ a, M.e (p.e + 1 * x) =
      M.e (xb + xs * x) * FE.ofK (M.k (yb + ys * x)) + M.e (p.e - 1 + 1 * x) := by
    intro x hx
    have hjf : x < 2 ^ [a].sum := by simpa using hx
    have hu : unflat [a] x = [x] := by simp [unflat, Nat.mod_eq_of_lt hx]
    have r := loop_rel h.1 (jf := x) (t := 0) hjf (by simp)
    simp only [LRel, List.getD_cons_zero, List.getD_cons_succ, LoopOut.arg, loop_apply,
      LoopOut.cell_val, Opd.val_abs] at r
    rw [Opd.val_prev M _ hjf] at r
    simp [lrank, ltw, LRow.w, Row.w, Row.writes, Ptr.at, Addr.at, Loop.dot, hu, Mem.rd_E, Mem.rd_K] at r
    simp only [Nat.one_mul]
    rw [r]
  have hpre := prefix_cells M.e p.e 1 (2 ^ a) hp _ hstep
  have hl := hpre n hna
  simp only [Nat.one_mul] at hl
  have hc : (LoopOut.cell ⟨p, [a], [⟨.muladd, .E, [.abs ⟨.E, xb, [xs]⟩, .abs ⟨.K, yb, [ys]⟩,
      .prev 0]⟩]⟩ 0 (n - 1)).val M = M.e (p.e - 1 + n) := by
    simp [LoopOut.cell_val, lrank, ltw, LRow.w, Row.w, Row.writes, Ptr.at, Mem.rd_E]
    congr 1; omega
  simp only [loop_apply] at hc ⊢
  rw [hc, hl, ofK_one, ofK_zero, one_mul, add_zero, Cell.val_E, add_right_comm,
    CharTwo.add_self_eq_zero, zero_add]

end Lvm.QAcc
end
end

section
section
set_option autoImplicit false
namespace Lvm.QAcc
open Lvm Lvm.Loop Lvm.Loop.Build Lvm.QSig Lvm.Q1
variable {c : Ctx} {M : Mem}

theorem consts_spec {x : Nat} {p : Ptr} (h : SegsHold c M p (consts x p).2) :
    (consts x p).1.1 = ec p.e ∧ (consts x p).1.2 = ec (p.e + 1) ∧
      M.e p.e = 0 ∧ M.e (p.e + 1) = 1 := by
  simp only [consts, bind_apply, pure_apply, List.append_nil] at h ⊢
  rw [segsHold_append] at h
  have h1 := lin_spec h.1
  have h2 := lin_spec h.2
  have hp : (p.adv (const .E 0 (kc x) p).2).e = p.e + 1 := by
    simp [const, lin, rowRes, Ptr.adv, segsW, Seg.w, Row.w, Row.writes]
  refine ⟨rfl, by simp [const, lin, rowRes, Ptr.at, Ptr.adv, segsW, Seg.w, Row.w, Row.writes], ?_, ?_⟩
  · have : (const .E 0 (kc x) p).1.val M = M.e p.e := rfl
    rw [← this]; simp only [const] at h1 ⊢; rw [h1, ofK_one, one_mul, CharTwo.add_self_eq_zero, ofK_zero,
      add_zero]
  · have : (const .E 1 (kc x) (p.adv (const .E 0 (kc x) p).2)).1.val M = M.e (p.e + 1) := by
      simp [const, lin, rowRes, Ptr.at, Cell.val, Mem.rd_E, Ptr.adv, segsW, Seg.w, Row.w, Row.writes]
    rw [← this]; simp only [const] at h2 ⊢; rw [h2, ofK_one, one_mul, CharTwo.add_self_eq_zero, zero_add]

end Lvm.QAcc
end
end

section
section
set_option autoImplicit false
namespace Lvm.QAcc
open Lvm Lvm.Loop Lvm.Loop.Build Lvm.QSig Lvm.Q1
variable {c : Ctx} {M : Mem}

theorem macChain_spec : ∀ (l : List (Cell × Cell)) (acc : Cell) (p : Ptr),
    SegsHold c M p (macChain l acc p).2 →
      (macChain l acc p).1.val M = acc.val M + (l.map fun ab => ab.1.val M * ab.2.val M).sum
  | [], acc, p, _ => by simp [macChain, pure_apply]
  | ab :: l, acc, p, h => by
    simp only [macChain, bind_apply] at h ⊢
    rw [segsHold_append] at h
    rw [macChain_spec l _ _ h.2, mulAdd_spec h.1, List.map_cons, List.sum_cons]
    ring

end Lvm.QAcc
end
end

section
section
set_option autoImplicit false
namespace Lvm.QAcc
open Lvm Lvm.Loop Lvm.Loop.Build Lvm.QSig Lvm.Q1
variable {c : Ctx} {M : Mem}

theorem horner_spec (t z : Cell) (hz : z.val M = 0) : ∀ (cs : List Cell) (p : Ptr),
    SegsHold c M p (horner cs t z p).2 →
      (horner cs t z p).1.val M = polyEval (cs.map (Cell.val M)) (t.val M)
  | [], p, _ => by simp [horner, pure_apply, polyEval, hz]
  | c₀ :: cs, p, h => by
    simp only [horner, bind_apply] at h ⊢
    rw [segsHold_append] at h
    rw [mulAdd_spec h.2, horner_spec t z hz cs p h.1]
    simp [polyEval]

end Lvm.QAcc
end
end

section
section
set_option autoImplicit false
namespace Lvm.QAcc
open Lvm Lvm.Loop Lvm.Loop.Build Lvm.QSig Lvm.Q1
variable {c : Ctx} {M : Mem}

theorem linePt_spec {a b t : Cell} {p : Ptr} (h : SegsHold c M p (linePt a b t p).2) :
    (linePt a b t p).1.val M = a.val M + t.val M * (a.val M + b.val M) := by
  simp only [linePt, bind_apply] at h ⊢
  rw [segsHold_append] at h
  rw [mulAdd_spec h.2, add, lin_spec h.1, ofK_one, ofK_zero, one_mul, add_zero]
  ring

end Lvm.QAcc
end
end

section
section
set_option autoImplicit false
namespace Lvm.QAcc
open Lvm Lvm.Loop Lvm.Loop.Build Lvm.QSig Lvm.Q1
variable {c : Ctx} {M : Mem}

theorem linePts_spec (t : Cell) : ∀ (ab : List (Cell × Cell)) (p : Ptr),
    SegsHold c M p (linePts ab t p).2 → (linePts ab t p).1.length = ab.length ∧
      ∀ i < ab.length, ((linePts ab t p).1.getD i default).val M =
        (ab.getD i default).1.val M + t.val M * ((ab.getD i default).1.val M + (ab.getD i default).2.val M)
  | [], _, _ => ⟨rfl, fun i hi => absurd hi (by simp)⟩
  | x :: ab, p, h => by
    simp only [linePts, List.map_cons, seqAll_cons_apply] at h ⊢
    rw [segsHold_append, segsHold_append] at h
    obtain ⟨ih1, ih2⟩ := linePts_spec t ab _ h.2.1
    refine ⟨by simpa [linePts] using ih1, fun i hi => ?_⟩
    cases i with
    | zero => simpa using linePt_spec h.1
    | succ i => simpa [linePts] using ih2 i (by simpa using hi)

end Lvm.QAcc
end
end

section
section
set_option autoImplicit false
namespace Lvm.QAcc
open Lvm Lvm.Loop Lvm.Loop.Build Lvm.QSig Lvm.Q1
variable {c : Ctx} {M : Mem}

theorem assertEqs_spec {g : Cell} (hg : g.val M = 1) : ∀ (ab : List (Cell × Cell)) (p : Ptr),
    Ok c M (assertEqs ab g) p → ∀ x ∈ ab, x.1.val M = x.2.val M
  | [], _, _, x, hx => absurd hx (by simp)
  | y :: ab, p, h, x, hx => by
    obtain ⟨h1, h2⟩ := h
    simp only [assertEqs, List.map_cons, seqAll_cons_apply] at h1 h2
    rw [segsHold_append, segsHold_append] at h1
    rw [segsAssert_append, segsAssert_append] at h2
    rcases List.mem_cons.mp hx with rfl | hx
    · exact assertEqE_spec ⟨h1.1, h2.1⟩ hg
    · exact assertEqs_spec hg ab _ ⟨h1.2.1, h2.2.1⟩ x hx

end Lvm.QAcc
end
end

section
set_option autoImplicit false
namespace Lvm.QAcc
open Lvm Lvm.Loop Lvm.Loop.Build Lvm.QSig Lvm.Q1
variable {c : Ctx} {M : Mem}

theorem seqAll_vals {α : Type} [Inhabited α] (f : Nat → BM α) (V : α → FE) (val : Nat → FE)
    (hf : ∀ k q, SegsHold c M q (f k q).2 → V (f k q).1 = val k) :
    ∀ (ks : List Nat) (p : Ptr), SegsHold c M p (seqAll (ks.map f) p).2 →
      ∀ i < ks.length, V ((seqAll (ks.map f) p).1.getD i default) = val (ks.getD i 0)
  | [], _, _, i, hi => absurd hi (by simp)
  | k :: ks, p, h, i, hi => by
    simp only [List.map_cons, seqAll_cons_apply] at h ⊢
    rw [segsHold_append, segsHold_append] at h
    cases i with
    | zero => exact hf k p h.1
    | succ i => simpa using seqAll_vals f V val hf ks _ h.2.1 i (by simpa using hi)

theorem forN_vals {α : Type} [Inhabited α] {n : Nat} {f : Nat → BM α} (V : α → FE) (val : Nat → FE)
    (hf : ∀ k q, SegsHold c M q (f k q).2 → V (f k q).1 = val k) {p : Ptr}
    (h : SegsHold c M p (forN n f p).2) : ∀ i < n, V ((forN n f p).1.getD i default) = val i := by
  intro i hi
  have := seqAll_vals f V val hf (List.range n) p h i (by simpa using hi)
  simpa [forN, List.getD_eq_getElem?_getD, hi] using this

theorem sum_map_range (f : Nat → FE) : ∀ n, ((List.range n).map f).sum = ∑ k ∈ Finset.range n, f k
  | 0 => by simp
  | n + 1 => by rw [List.range_succ, List.map_append, List.sum_append, sum_map_range f n,
      Finset.sum_range_succ]; simp

end Lvm.QAcc
end

section
set_option autoImplicit false
namespace Lvm.QAcc
open Lvm Lvm.Loop Lvm.Loop.Build Lvm.QSig Lvm.Q1
variable {c : Ctx} {M : Mem}

theorem sum_blocks (f : Nat → FE) (B : Nat) : ∀ n : Nat,
    ∑ k ∈ Finset.range (n * B), f k = ∑ h ∈ Finset.range n, ∑ l ∈ Finset.range B, f (h * B + l)
  | 0 => by simp
  | n + 1 => by
    rw [Nat.succ_mul, Finset.sum_range_add, sum_blocks f B n, Finset.sum_range_succ]

theorem eqW_split (v : Nat → FE) (la dk : Nat) (hla : la ≤ dk) (x : Nat) :
    eqW ((List.range dk).map v) x =
      eqW ((List.range la).map v) (x % 2 ^ la) *
        eqW ((List.range (dk - la)).map fun i => v (la + i)) (x / 2 ^ la) := by
  have e : (List.range dk).map v = (List.range la).map v ++ (List.range (dk - la)).map fun i => v (la + i) := by
    obtain ⟨m, rfl⟩ : ∃ m, dk = la + m := ⟨dk - la, by omega⟩
    rw [List.range_add, List.map_append, List.map_map, Nat.add_sub_cancel_left]; rfl
  rw [e, eqW_append, List.length_map, List.length_range]

theorem eqDot_spec {al : Nat → Cell} {la dk : Nat} {z one : Cell} {xs : List Cell} {p : Ptr}
    (hal : ∀ i, (al i).ty = .E) (hla : la ≤ dk) (hn : xs.length ≤ 2 ^ dk)
    (hz : z.val M = 0) (hone : M.e one.n = 1) (h : SegsHold c M p (eqDot al la dk z one xs p).2) :
    (eqDot al la dk z one xs p).1.val M =
      ∑ k ∈ Finset.range xs.length,
        eqW ((List.range dk).map fun i => (al i).val M) k * (xs.getD k z).val M := by
  simp only [eqDot, bind_apply] at h ⊢
  rw [segsHold_append, segsHold_append, segsHold_append] at h
  obtain ⟨h1, h2, h3, h4⟩ := h
  have eL := eqTab_spec al z one false la h1 hz hal hone
  have eH := eqTab_spec (fun i => al (la + i)) z one false (dk - la) h2 hz (fun i => hal _) hone
  simp only [eqCoord, Bool.false_eq_true, ite_false] at eL eH
  have hB0 : 0 < 2 ^ la := by positivity
  have hacc := forN_vals (n := (xs.length + 2 ^ la - 1) / 2 ^ la) (Cell.val M)
    (fun h => ∑ l ∈ Finset.range (2 ^ la), M.e ((eqTab al z one false la p).1 + l) *
      (xs.getD (h * 2 ^ la + l) z).val M)
    (fun k q hk => by rw [macChain_spec _ _ _ hk, hz, zero_add, List.map_map, sum_map_range]; rfl) h3
  rw [macChain_spec _ _ _ h4, hz, zero_add, List.map_map, sum_map_range]
  have hE : 2 ^ dk = 2 ^ la * 2 ^ (dk - la) := by rw [← pow_add, Nat.add_sub_cancel' hla]
  have hblk : ∀ hh < (xs.length + 2 ^ la - 1) / 2 ^ la, hh < 2 ^ (dk - la) := by
    intro hh hh'
    have h1 : (hh + 1) * 2 ^ la ≤ xs.length + 2 ^ la - 1 := (Nat.le_div_iff_mul_le hB0).mp (by (clear * - hh'; omega))
    have h2 : 2 ^ la * hh < 2 ^ la * 2 ^ (dk - la) := by
      rw [Nat.succ_mul] at h1; rw [← hE, mul_comm]; (clear * - hn hB0 hE h1; omega)
    exact Nat.lt_of_mul_lt_mul_left h2
  have hlen : xs.length ≤ (xs.length + 2 ^ la - 1) / 2 ^ la * 2 ^ la := by
    have h1 := Nat.div_add_mod (xs.length + 2 ^ la - 1) (2 ^ la)
    have h2 := Nat.mod_lt (xs.length + 2 ^ la - 1) hB0
    rw [mul_comm]; (clear * - hB0 h1; omega)
  refine (Finset.sum_congr rfl (g := fun hh => ∑ l ∈ Finset.range (2 ^ la),
    eqW ((List.range dk).map fun i => (al i).val M) (hh * 2 ^ la + l) * (xs.getD (hh * 2 ^ la + l) z).val M)
    fun hh hh' => ?_).trans ?_
  · rw [Finset.mem_range] at hh'
    simp only [Function.comp_apply, Cell.val_E]
    rw [hacc hh hh', Finset.mul_sum]
    refine Finset.sum_congr rfl fun l hl => ?_
    rw [Finset.mem_range] at hl
    rw [eqW_split _ la dk hla, eL l hl, eH hh (hblk hh hh'),
      show (hh * 2 ^ la + l) % 2 ^ la = l by rw [Nat.mul_comm, Nat.mul_add_mod, Nat.mod_eq_of_lt hl],
      show (hh * 2 ^ la + l) / 2 ^ la = hh by
        rw [Nat.mul_comm, Nat.mul_add_div hB0, Nat.div_eq_of_lt hl, Nat.add_zero]]
    ring
  · rw [← sum_blocks (fun k => eqW ((List.range dk).map fun i => (al i).val M) k * (xs.getD k z).val M)]
    obtain ⟨m, hm⟩ : ∃ m, (xs.length + 2 ^ la - 1) / 2 ^ la * 2 ^ la = xs.length + m :=
      ⟨_, (Nat.add_sub_cancel' hlen).symm⟩
    rw [hm, Finset.sum_range_add]
    have h0 : ∑ j ∈ Finset.range m, eqW ((List.range dk).map fun i => (al i).val M) (xs.length + j) *
        (xs.getD (xs.length + j) z).val M = 0 := by
      apply Finset.sum_eq_zero; intro j _
      rw [List.getD_eq_default _ _ (by (clear * -; omega)), hz, mul_zero]
    rw [h0, add_zero]

end Lvm.QAcc
end

section
set_option autoImplicit false
namespace Lvm.QAcc
open Lvm Lvm.Loop Lvm.Loop.Build Lvm.QSig Lvm.Q1
variable {c : Ctx} {M : Mem}

theorem qyown_spec {kb la dk : Nat} {z one : Cell}
    {fx : List Cell} {p : Ptr} (hla : la ≤ dk) (hn : fx.length ≤ 2 ^ dk)
    (hz : z.val M = 0) (hone : M.e one.n = 1)
    (h : SegsHold c M p (qyown kb la dk z one fx p).2) :
    (qyown kb la dk z one fx p).1.val M =
      ∑ k ∈ Finset.range fx.length,
        eqW ((List.range dk).map fun i => M.e (kb + i)) k * (fx.getD k z).val M :=
  eqDot_spec (fun _ => rfl) hla hn hz hone h

/-- The child's `PUB` lane `i` in the circuit: the key from the cells `vkc …`, else stream lane `hd + i`. -/
def pubLane (M : Mem) (hd vkc i : Nat) : FK := if 1 ≤ i ∧ i < 5 then M.k (vkc + (i - 1)) else M.k (hd + i)

end Lvm.QAcc
end

section
set_option autoImplicit false
namespace Lvm.QAcc
open Lvm Lvm.Loop Lvm.Loop.Build Lvm.QSig Lvm.Q1
variable {c : Ctx} {M : Mem}

theorem qpub_spec {al : Nat → Cell} {z one : Cell} {τp hd vkc nL : Nat} {p : Ptr} (hz : z.val M = 0)
    (hal : ∀ i, (al i).ty = .E) (hone : M.e one.n = 1) (hn : nL ≤ 2 ^ τp)
    (h : SegsHold c M p (qpub al z one τp hd vkc nL p).2) :
    (qpub al z one τp hd vkc nL p).1.val M =
      ∑ i ∈ Finset.range nL, eqW ((List.range τp).map fun i => (al i).val M) i *
        FE.ofK (pubLane M hd vkc i) := by
  rw [qpub, eqDot_spec hal (by (clear * -; omega)) (by simpa using hn) hz hone h, List.length_map, List.length_range]
  refine Finset.sum_congr rfl fun i hi => ?_
  rw [Finset.mem_range] at hi
  rw [List.getD_eq_getElem _ _ (by simpa using hi), List.getElem_map, List.getElem_range]
  congr 1
  simp only [pubLaneC, pubLane]
  split_ifs <;> rfl

end Lvm.QAcc
end

-- ===== from `LvmQAcc` =====

section
section
set_option autoImplicit false
namespace Lvm.QAcc
open Lvm Lvm.Loop Lvm.Loop.Build Lvm.QSig Lvm.Q1 DM

theorem flatMap_feAt (sig : ByteArray) (b : Nat) : ∀ n : Nat,
    ((List.range n).map fun j => feAt sig (8 * (b + 3 * j))).flatMap FE.lanes =
      (List.range (3 * n)).map fun x => kAt sig (8 * (b + x))
  | 0 => rfl
  | n + 1 => by
    rw [List.range_succ, List.map_append, List.flatMap_append, flatMap_feAt sig b n,
      show 3 * (n + 1) = 3 * n + 1 + 1 + 1 by ring, List.range_succ, List.range_succ, List.range_succ]
    simp only [List.map_cons, List.map_nil, List.flatMap_cons, List.flatMap_nil, List.append_nil,
      List.map_append, List.append_assoc, feAt, FE.lanes, List.cons_append, List.nil_append]
    rw [show 8 * (b + 3 * n) + 8 = 8 * (b + (3 * n + 1)) by ring,
      show 8 * (b + 3 * n) + 16 = 8 * (b + (3 * n + 1 + 1)) by ring, show 8 * (b + 3 * n) = 8 * (b + 3 * n) from rfl]

end Lvm.QAcc
end
end

section
section
set_option autoImplicit false
namespace Lvm.QAcc
open Lvm Lvm.Loop Lvm.Loop.Build Lvm.QSig Lvm.Q1 DM

theorem range_split (F : Nat → FK) :
    (List.range pubLanes).map F = [F 0] ++ ((List.range 4).map fun i => F (1 + i)) ++
      ((List.range 4).map fun i => F (5 + i)) ++ ((List.range 4).map fun i => F (9 + i)) ++ [F 13] ++
      ((List.range 4).map fun i => F (14 + i)) ++ ((List.range 597).map fun i => F (18 + i)) ++
      ((List.range 132).map fun i => F (615 + i)) := by
  rw [show pubLanes = 1 + 4 + 4 + 4 + 1 + 4 + 597 + 132 from rfl]
  simp only [map_range_add, List.map_map, Function.comp_def, List.append_assoc]
  simp only [List.range_one, List.map_cons, List.map_nil, Nat.add_zero, Nat.zero_add, List.cons_append,
    List.nil_append, Nat.add_assoc, Nat.reduceAdd]

/-- **The child's `PUB` lanes** are its stream's lanes from `11`, the key from `V`'s argument. -/
theorem pubOf_hdrLanes (vk c : Vector UInt8 32) (sig : ByteArray) :
    (pubOf vk c sig).hdrLanes = (List.range pubLanes).map (hdrLaneS vk sig) := by
  have pos (i : Nat) (h : ¬ (1 ≤ i ∧ i < 5)) : hdrLaneS vk sig i = kAt sig (8 * (11 + i)) := by
    simp only [hdrLaneS, h, ite_false]
  have e0 : (⟨(pubOf vk c sig).b.toUInt64⟩ : FK) = hdrLaneS vk sig 0 := by
    rw [pos 0 (by (clear * -; omega))]
    simp only [pubOf, kAt, Nat.toUInt64, UInt64.ofNat_toNat]; rfl
  have e1 : (pubOf vk c sig).vk = (List.range 4).map fun i => hdrLaneS vk sig (1 + i) := by
    show digestLanes vk = _
    conv_lhs => rw [list_eq_range_getD (digestLanes vk)]
    rw [show (digestLanes vk).length = 4 by simp [digestLanes]]
    apply List.map_congr_left; intro i hi
    simp only [List.mem_range] at hi
    simp [hdrLaneS, show 1 ≤ 1 + i ∧ 1 + i < 5 by (clear * - hi; omega)]
  have seg (o k n : Nat) (ho : 5 ≤ k) (hk : headerAt o = 8 * (11 + k)) :
      ((List.range n).map fun i => kAt sig (headerAt o + 8 * i)) =
        (List.range n).map fun i => hdrLaneS vk sig (k + i) := by
    apply List.map_congr_left; intro i _
    rw [pos _ (by (clear * - ho; omega)), hk, show 8 * (11 + k) + 8 * i = 8 * (11 + (k + i)) by ring]
  have e2 : (pubOf vk c sig).cL = (List.range 4).map fun i => hdrLaneS vk sig (5 + i) :=
    seg 48 5 4 (by (clear * -; omega)) rfl
  have e3 : (pubOf vk c sig).s = (List.range 4).map fun i => hdrLaneS vk sig (9 + i) :=
    seg 80 9 4 (by (clear * -; omega)) rfl
  have e4 : (⟨(pubOf vk c sig).n.toUInt64⟩ : FK) = hdrLaneS vk sig 13 := by
    rw [pos 13 (by (clear * -; omega))]
    simp only [pubOf, kAt, Nat.toUInt64, UInt64.ofNat_toNat]; rfl
  have e5 : (pubOf vk c sig).h = (List.range 4).map fun i => hdrLaneS vk sig (14 + i) :=
    seg 120 14 4 (by (clear * -; omega)) rfl
  have e6 : (pubOf vk c sig).sigLeaf = (List.range 597).map fun i => hdrLaneS vk sig (18 + i) := by
    simp only [pubOf]
    rw [show sigBytes / 8 = 597 from rfl]
    exact seg 152 18 597 (by (clear * -; omega)) rfl
  have hpos : ∀ i, headerAt (offAcc + eBytes * i) = 8 * (626 + 3 * i) := by
    intro i; simp only [headerAt, offAcc, eBytes, sigBytes]; (clear * -; omega)
  have e7 : ((pubOf vk c sig).accIn.pt ++ [(pubOf vk c sig).accIn.y]).flatMap FE.lanes =
      (List.range 132).map fun i => hdrLaneS vk sig (615 + i) := by
    have : (pubOf vk c sig).accIn.pt ++ [(pubOf vk c sig).accIn.y] =
        (List.range 44).map fun j => feAt sig (8 * (626 + 3 * j)) := by
      simp only [pubOf, hpos]
      rw [show (44 : Nat) = accVars + 1 from rfl, List.range_succ, List.map_append, List.map_singleton]
    rw [this, flatMap_feAt sig 626 44]
    apply List.map_congr_left; intro i _
    rw [pos _ (by (clear * -; omega)), show 11 + (615 + i) = 626 + i by (clear * -; omega)]
  rw [range_split]
  simp only [Pub.hdrLanes, List.append_assoc]
  rw [e0, e1, e2, e3, e4, e5, e6, e7]

/-- **The child's `PUB` evaluation on streamed cells**: with the stream's lanes `< T` and the key
cells `vkc …` holding `digestLanes vk`, `pubEval` of the child's lanes at a point of `τp` coordinates
is `qpub`'s sum. -/
theorem pubEval_child {M : Mem} {sig : ByteArray} {T : Nat} (hS : Streamed M sig T)
    (hT : 11 + pubLanes ≤ T) {vk : Vector UInt8 32} (c : Vector UInt8 32) {vkc : Nat}
    (hvk : ∀ i < 4, M.k (vkc + i) = (digestLanes vk).getD i 0) (pt : List FE)
    (hn : pubLanes ≤ 2 ^ pt.length) :
    M3.pubEval (pubOf vk c sig).hdrLanes pt =
      ∑ i ∈ Finset.range pubLanes, eqW pt i * FE.ofK (pubLane M 11 vkc i) := by
  rw [M3.pubEval_eq, mle_eq_sum, pubOf_hdrLanes]
  obtain ⟨m, hm⟩ : ∃ m, 2 ^ pt.length = pubLanes + m := ⟨_, (Nat.add_sub_cancel' hn).symm⟩
  rw [hm, Finset.sum_range_add]
  have h0 : ∑ x ∈ Finset.range m, eqW pt (pubLanes + x) *
      FE.ofK (M3.pubCell ((List.range pubLanes).map (hdrLaneS vk sig)) (pubLanes + x)) = 0 := by
    apply Finset.sum_eq_zero; intro x _
    simp [M3.pubCell, List.getD_eq_getElem?_getD, ofK_zero]
  rw [h0, add_zero]
  apply Finset.sum_congr rfl; intro i hi
  rw [Finset.mem_range] at hi
  refine congrArg (fun x => eqW pt i * FE.ofK x) ?_
  simp only [M3.pubCell, List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range hi,
    Option.map_some, Option.getD_some, hdrLaneS, pubLane]
  split_ifs with h
  · rw [hvk _ (by (clear * - h; omega)), List.getD_eq_getElem?_getD]
  · rw [hS _ (by (clear * - hT hm hi; omega))]

/-- Phase 3b's positions from its start `P` (`dk` batching challenges). -/
def phH (P dk : Nat) : Nat := P + 72 * dk
def phZ (P dk : Nat) : Nat := phH P dk + 24 * (accVars + 1) + 72

/-- **Phase 3b from position `P`** (`accFold`, BLUEPRINT §12.4): `κ`, `h`, `t`, the zero scalar read at
fixed offsets; the four checks on `ok`; the folded claim. -/
theorem accFold_run (P : Params) (m : M3) (pub : Pub) (evals : List (List FE × List FE))
    (sig : ByteArray) (s : RS) (hdk : 1 ≤ P.accLog) :
    accFold P m pub evals sig s =
      let v := feAt sig
      let kap := samplesAt v (s.ent + s.msg) P.accLog
      let h := scalarsAt v (phH (s.ent + s.msg) P.accLog + 40) (accVars + 1)
      let t := v (phH (s.ent + s.msg) P.accLog + 24 * (accVars + 1) + 40)
      (⟨accLine pub.accIn.pt (tablePoint evals ++ kap) t, polyEval h t⟩,
        ⟨phZ (s.ent + s.msg) P.accLog, 24,
          (v (phZ (s.ent + s.msg) P.accLog + 40) == 0) &&
            ((sumE h == dot (eqKernel kap) (m.fixSent pub evals)) &&
              ((h.headD 0 == pub.accIn.y) && (m.pubCheck pub evals && s.ok)))⟩) := by
  unfold accFold
  rw [bind_run, require_run, bind_run, samples_run sig _ _ hdk, bind_run, readEs_run, bind_run,
    sampleE_run, bind_run, readE_run, bind_run, require_run, bind_run, require_run, bind_run,
    require_run, pure_run]
  simp only [samplesAt, phH, phZ]
  rw [show s.ent + s.msg + 72 * P.accLog + 40 + (0 + 24 * (accVars + 1)) =
      s.ent + s.msg + 72 * P.accLog + 24 * (accVars + 1) + 40 by (clear * -; omega),
    show s.ent + s.msg + 72 * P.accLog + 0 + 40 = s.ent + s.msg + 72 * P.accLog + 40 by (clear * -; omega),
    show s.ent + s.msg + 72 * P.accLog + 72 + (0 + 24 * (accVars + 1)) =
      s.ent + s.msg + 72 * P.accLog + 24 * (accVars + 1) + 72 by (clear * -; omega), Nat.add_zero, Nat.zero_add]

end Lvm.QAcc
end
end

section
set_option autoImplicit false
namespace Lvm.QAcc
open Lvm Lvm.Loop Lvm.Loop.Build Lvm.QSig Lvm.Q1

/-- The current proof's `acc_in` from its `PUB` cells (three lanes per scalar). -/
def accC (M : Mem) (pb : Nat) : Acc :=
  ⟨(List.range accVars).map fun i => ⟨M.k (pb + 615 + 3 * i), M.k (pb + 615 + 3 * i + 1), M.k (pb + 615 + 3 * i + 2)⟩,
    ⟨M.k (pb + 615 + 3 * accVars), M.k (pb + 615 + 3 * accVars + 1), M.k (pb + 615 + 3 * accVars + 2)⟩⟩

/-- **What Q_acc's rows and assertions give** (gate on), on the stream view `v = feAt Σ`. -/
structure AccFacts (A : AccIn) (M : Mem) (sig : ByteArray) : Prop where
  /-- (4) The child's `PUB` evaluation is its lanes' extension at `PUB`'s point. -/
  pub : A.pv.val M = ∑ i ∈ Finset.range pubLanes,
    eqW ((List.range A.τp).map fun i => (A.pp i).val M) i * FE.ofK (pubLane M 11 (A.pb + 1) i)
  /-- (2) `h'₀ = acc_in'.y`. -/
  h0 : feAt sig (8 * A.hL 0) = feAt sig (8 * accLane accVars)
  /-- (2) `Σ_j h'_j = y' = Σ_k eq(κ', k)·fx_k`. -/
  sum : ((List.range (accVars + 1)).map fun j => feAt sig (8 * A.hL j)).sum =
    ∑ k ∈ Finset.range A.fx.length,
      eqW ((List.range A.dk).map fun i => feAt sig (8 * A.kap i)) k * (A.fx.getD k default).val M
  /-- (3) The line point is the current `acc_in.pt`. -/
  line : ∀ i < accVars, feAt sig (8 * accLane i) + feAt sig (8 * A.tL) *
      (feAt sig (8 * accLane i) + ((A.rc.map (Cell.val M) ++
        (List.range A.dk).map fun j => feAt sig (8 * A.kap j)).getD i 0)) = (accC M A.pb).pt.getD i 0
  /-- (3) `h'(t')` is the current `acc_in.y`. -/
  y : polyEval ((List.range (accVars + 1)).map fun j => feAt sig (8 * A.hL j)) (feAt sig (8 * A.tL)) =
    (accC M A.pb).y
  /-- The zero scalar. -/
  zero : feAt sig (8 * A.zL) = 0

end Lvm.QAcc
end

-- ===== from `LvmQAccSound` =====

section
section
set_option autoImplicit false
namespace Lvm.QAcc
open Lvm Lvm.Loop Lvm.Loop.Build Lvm.QSig Lvm.Q1

theorem okBind {c : Ctx} {M : Mem} {α β : Type} {m : BM α} {f : α → BM β} {p : Ptr}
    (h : Ok c M (m >>= f) p) : Ok c M m p ∧ Ok c M (f (m p).1) (p.adv (m p).2) := by
  obtain ⟨h1, h2⟩ := h
  rw [hold_bind] at h1; rw [assert_bind] at h2
  exact ⟨⟨h1.1, h2.1⟩, ⟨h1.2, h2.2⟩⟩

theorem okBindE {c : Ctx} {M : Mem} {α β : Type} {m : BM α} {f : α → BM β} {p : Ptr}
    (h : Ok c M (m >>= f) p) : ∃ x q, (m p).1 = x ∧ p.adv (m p).2 = q ∧ Ok c M m p ∧ Ok c M (f x) q :=
  ⟨_, _, rfl, rfl, okBind h⟩

end Lvm.QAcc
end
end

section
section
set_option autoImplicit false
namespace Lvm.QAcc
open Lvm Lvm.Loop Lvm.Loop.Build Lvm.QSig Lvm.Q1

theorem sum_map_range' (f : Nat → FE) (n : Nat) :
    ((List.range n).map f).sum = ∑ k ∈ Finset.range n, f k := sum_map_range f n

attribute [local irreducible] horner macChain linePts in
set_option maxHeartbeats 1000000 in
/-- **Q_acc's facts**: where its rows and assertions hold with the gate on (`M.k pb = 1`) and the
child's stream bound (`Streamed`, lanes below `T`), the six equations of `AccFacts`. -/
theorem qacc_facts {c : Ctx} {M : Mem} {sig : ByteArray} {T : Nat} {A : AccIn} {p : Ptr}
    (hS : Streamed M sig T) (hT : A.zL + 2 < T) (hH : 11 + pubLanes ≤ T) (hg : M.k A.pb = 1)
    (hpp : ∀ i, (A.pp i).ty = .E) (hτp : pubLanes ≤ 2 ^ A.τp) (hla : A.la ≤ A.dk)
    (hnf : A.fx.length ≤ 2 ^ A.dk) (hRD : A.rc.length + A.dk = accVars)
    (h : Ok c M (qacc A) p) : AccFacts A M sig := by
  have hD : accVars = 43 := rfl
  have hPL : pubLanes = 747 := rfl
  have hgv : (kc A.pb).val M = 1 := kc_val_one hg
  unfold qacc at h
  -- constants
  obtain ⟨zo, p1, evo1, epo1, o1, h⟩ := okBindE h
  obtain ⟨hz1, hz2, hz0, hone⟩ := consts_spec o1.1
  have hp1 : 1 ≤ (p.adv (consts A.pb p).2).e := by
    have := adv_e_le p (consts A.pb p).2
    have : (p.adv (consts A.pb p).2).e = p.e + 2 := by
      simp [consts, const, lin, rowRes, Ptr.adv, segsW, Seg.w, Row.w, Row.writes, bind_apply, pure_apply]
    omega
  have hzv : (consts A.pb p).1.1.val M = 0 := by rw [hz1]; exact hz0
  have hzE : (consts A.pb p).1.1.ty = .E := by rw [hz1]
  have hov : M.e (consts A.pb p).1.2.n = 1 := by rw [hz2]; exact hone
  have hov' : (consts A.pb p).1.2.val M = 1 := by rw [hz2]; exact hone
  -- κ'
  rw [evo1] at hzv hzE hov hov'
  rw [epo1] at hp1
  obtain ⟨kb, p2, evo2, epo2, o2, h⟩ := okBindE h
  have hk := ldEsB_spec hS (qs := (List.range A.dk).map A.kap)
    (by intro q hq; simp only [List.mem_map, List.mem_range] at hq; obtain ⟨i, hi, rfl⟩ := hq
        simp only [AccIn.kap, AccIn.zL, AccIn.z0, AccIn.h0] at hT ⊢; omega) o2.1
  have hp2 := le_trans hp1 (adv_e_le p1 (ldEsB ((List.range A.dk).map A.kap) p1).2)
  -- (4) PUB
  rw [evo2] at hk
  rw [epo2] at hp2
  obtain ⟨sP, p3, evo3, epo3, o3, h⟩ := okBindE h
  have hsP := qpub_spec hzv hpp hov hτp o3.1
  rw [evo3] at hsP
  obtain ⟨_vo4, p4, evo4, epo4, o4, h⟩ := okBindE h
  have e4 := assertEqE_spec o4 hgv
  -- (1) y'
  obtain ⟨y, p5, evo5, epo5, o5, h⟩ := okBindE h
  have hy := qyown_spec hla hnf hzv hov o5.1
  -- h', acc_in'
  rw [evo5] at hy
  obtain ⟨hb, p6, evo6, epo6, o6, h⟩ := okBindE h
  have hh := ldEsB_spec hS (qs := (List.range (accVars + 1)).map A.hL)
    (by intro q hq; simp only [List.mem_map, List.mem_range] at hq; obtain ⟨i, hi, rfl⟩ := hq
        simp only [AccIn.hL, AccIn.zL, AccIn.z0, AccIn.h0] at hT ⊢; omega) o6.1
  rw [evo6] at hh
  obtain ⟨ab, p7, evo7, epo7, o7, h⟩ := okBindE h
  have ha := ldEsB_spec hS (qs := (List.range (accVars + 1)).map accLane)
    (by intro q hq; simp only [List.mem_map, List.mem_range] at hq; obtain ⟨i, hi, rfl⟩ := hq
        simp only [accLane]; omega) o7.1
  rw [evo7] at ha
  obtain ⟨_vo8, p8, evo8, epo8, o8, h⟩ := okBindE h
  have e8 := assertEqE_spec o8 hgv
  obtain ⟨sh, p9, evo9, epo9, o9, h⟩ := okBindE h
  have hsh := macChain_spec _ _ _ o9.1
  rw [evo9] at hsh
  obtain ⟨_vo10, p10, evo10, epo10, o10, h⟩ := okBindE h
  have e10 := assertEqE_spec o10 hgv
  -- t', h'(t'), the line
  obtain ⟨t, p11, evo11, epo11, o11, h⟩ := okBindE h
  have ht := ldE_feAt hS (q := A.tL) (by simp only [AccIn.tL, AccIn.zL, AccIn.z0] at hT ⊢; omega) o11.1
  rw [evo11] at ht
  obtain ⟨hv, p12, evo12, epo12, o12, h⟩ := okBindE h
  have hhv := horner_spec (c := c) (M := M) t zo.1 hzv ((List.range (accVars + 1)).map fun j => ec (hb + j)) p11 o12.1
  rw [evo12] at hhv
  obtain ⟨pts, p13, evo13, epo13, o13, h⟩ := okBindE h
  have hpt := linePts_spec (c := c) (M := M) t ((List.range accVars).map fun i => (ec (ab + i), A.bC kb i)) p12 o13.1
  -- the current acc_in
  rw [evo13] at hpt
  obtain ⟨pc, p14, evo14, epo14, o14, h⟩ := okBindE h
  have hpc := ldEsB_val (c := c) (M := M) (qs := (List.range (accVars + 1)).map fun j => A.pb + 615 + 3 * j) (p := p13) o14.1
  rw [evo14] at hpc
  obtain ⟨_vo15, p15, evo15, epo15, o15, h⟩ := okBindE h
  have e15 := assertEqs_spec (c := c) (M := M) hgv ((List.range accVars).map fun i => (pts.getD i default, ec (pc + i))) p14 o15
  obtain ⟨_vo16, p16, evo16, epo16, o16, h⟩ := okBindE h
  have e16 := assertEqE_spec o16 hgv
  obtain ⟨zz, _qo17, evo17, epo17, o17, h⟩ := okBindE h
  have hz := ldE_feAt hS (q := A.zL) (by omega) o17.1
  rw [evo17] at hz
  have e17 := assert0_spec h.2
  rw [hgv, one_mul] at e17
  -- the facts
  have hkv : (List.range A.dk).map (fun i => M.e (kb + i)) =
      (List.range A.dk).map fun i => feAt sig (8 * A.kap i) := by
    apply List.map_congr_left; intro i hi; rw [List.mem_range] at hi
    rw [hk i (by simpa using hi)]; simp [List.getD_eq_getElem?_getD, hi]
  have hhv' : ∀ j < accVars + 1, M.e (hb + j) = feAt sig (8 * A.hL j) := by
    intro j hj; rw [hh j (by simpa using hj)]; simp [List.getD_eq_getElem?_getD, hj]
  have hav : ∀ j < accVars + 1, M.e (ab + j) = feAt sig (8 * accLane j) := by
    intro j hj; rw [ha j (by simpa using hj)]; simp [List.getD_eq_getElem?_getD, hj]
  have hHl : (List.range (accVars + 1)).map (fun j => feAt sig (8 * A.hL j)) =
      ((List.range (accVars + 1)).map fun j => ec (hb + j)).map (Cell.val M) := by
    rw [List.map_map]; apply List.map_congr_left; intro j hj; rw [List.mem_range] at hj
    simp [hhv' j hj]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [e4, hsP]
  · rw [← hhv' 0 (by omega), ← hav accVars (by omega)]; exact e8
  · have hsum : sh.val M = ∑ j ∈ Finset.range (accVars + 1), feAt sig (8 * A.hL j) := by
      rw [hsh, hzv, zero_add, List.map_map, sum_map_range']
      apply Finset.sum_congr rfl; intro j hj; rw [Finset.mem_range] at hj
      simp [hov', hhv' j hj]
    have hyv : y.val M = ∑ k ∈ Finset.range A.fx.length,
        eqW ((List.range A.dk).map fun i => feAt sig (8 * A.kap i)) k * (A.fx.getD k default).val M := by
      rw [hy, ← hkv]
      apply Finset.sum_congr rfl; intro k hk'
      rw [Finset.mem_range] at hk'
      rw [List.getD_eq_getElem _ _ hk', List.getD_eq_getElem _ _ hk']
    rw [sum_map_range', ← hsum, e10, hyv]
  · intro i hi
    have hpi := hpt.2 i (by simpa using hi)
    rw [List.getD_eq_getElem ((List.range accVars).map fun i => (ec (ab + i), A.bC kb i)) _ (by simpa using hi),
      List.getElem_map, List.getElem_range] at hpi
    have hq := e15 ((pts.getD i default, ec (pc + i))) (List.mem_map.mpr ⟨i, List.mem_range.mpr hi, rfl⟩)
    simp only at hq
    have hpci : M.e (pc + i) = ⟨M.k (A.pb + 615 + 3 * i), M.k (A.pb + 615 + 3 * i + 1),
        M.k (A.pb + 615 + 3 * i + 2)⟩ := by
      rw [hpc i (by simp; omega)]
      simp [List.getD_eq_getElem?_getD, List.getElem?_range (by omega : i < accVars + 1)]
    have hb : (A.bC kb i).val M = (A.rc.map (Cell.val M) ++
        (List.range A.dk).map fun j => feAt sig (8 * A.kap j)).getD i 0 := by
      simp only [AccIn.bC]
      by_cases hir : i < A.rc.length
      · have hir' : i < (A.rc.map (Cell.val M)).length := by simpa using hir
        simp only [List.getD_eq_getElem?_getD, List.getElem?_append_left hir, List.getElem?_append_left hir',
          List.getElem?_map, List.getElem?_eq_getElem hir, Option.map_some, Option.getD_some]
      · have hik : i - A.rc.length < A.dk := by omega
        rw [List.getD_eq_getElem?_getD, List.getElem?_append_right (by omega),
          List.getD_eq_getElem?_getD, List.getElem?_append_right (by simp; omega)]
        simp only [List.length_map, List.getElem?_map, List.getElem?_range hik, Option.map_some,
          Option.getD_some]
        rw [Cell.val_E, hk (i - A.rc.length) (by simpa using hik)]
        simp [List.getD_eq_getElem?_getD, List.getElem?_range hik]
    rw [hq, Cell.val_E, hpci, Cell.val_E, hav i (by omega), ht, hb] at hpi
    rw [← hpi]
    simp [accC, List.getD_eq_getElem?_getD, List.getElem?_range hi]
  · rw [hHl, ← ht, ← hhv, e16, Cell.val_E, hpc accVars (by simp)]
    simp [accC, List.getD_eq_getElem?_getD]
  · rw [← hz]; exact e17

end Lvm.QAcc
end
end

section
set_option autoImplicit false
namespace Lvm.QAcc
open Lvm Lvm.Loop Lvm.Loop.Build Lvm.QSig Lvm.Q1 DM
variable {M : Mem}

theorem dot_le : ∀ (l r : List FE), r.length ≤ l.length →
    Lvm.dot l r = ∑ i ∈ Finset.range r.length, l.getD i 0 * r.getD i 0
  | _, [], _ => by simp [Lvm.dot]
  | [], _ :: _, h => by simp at h
  | x :: l, y :: r, h => by
    have ih := dot_le l r (by simpa using h)
    simp only [Lvm.dot, foldl_add_id, zero_add] at ih ⊢
    simp only [List.zipWith_cons_cons, List.sum_cons, List.length_cons, Finset.sum_range_succ',
      List.getD_cons_succ, List.getD_cons_zero]
    rw [ih]; ring

theorem dot_eqKernel (κ r : List FE) (h : r.length ≤ 2 ^ κ.length) :
    Lvm.dot (eqKernel κ) r = ∑ k ∈ Finset.range r.length, eqW κ k * r.getD k 0 := by
  rw [dot_le _ _ (by rw [eqKernel_length]; exact h)]
  apply Finset.sum_congr rfl; intro k hk; rw [Finset.mem_range] at hk
  rw [List.getD_eq_getElem?_getD, eqKernel_get? κ k (by omega)]; rfl

end Lvm.QAcc
end

section
set_option autoImplicit false
namespace Lvm.QAcc
open Lvm Lvm.Loop Lvm.Loop.Build Lvm.QSig Lvm.Q1 DM
variable {M : Mem}

set_option maxHeartbeats 1000000 in
/-- **Q_acc replays phase 3b** (HAR's `Replays c M Σ (accFold P m pub evals) (qacc A) p (8 L)
(8 z0 + 24) (fun a _ => a = accC M pb)`, unfolded; `pub = pubOf vk c Σ` is the child's). -/
theorem qacc_sound {c : Ctx} {sig : ByteArray} {T : Nat} {A : AccIn} {p : Ptr}
    (P : Params) (m : M3) (vk cc : Vector UInt8 32) (evals : List (List FE × List FE))
    (hS : Streamed M sig T) (hT : A.zL + 2 < T) (hH : 11 + pubLanes ≤ T) (hg : M.k A.pb = 1)
    (hpp : ∀ i, (A.pp i).ty = .E) (hτp : pubLanes ≤ 2 ^ A.τp) (hla : A.la ≤ A.dk)
    (hnf : A.fx.length ≤ 2 ^ A.dk) (hRD : A.rc.length + A.dk = accVars)
    (hdk : P.accLog = A.dk) (hdk1 : 1 ≤ A.dk)
    (hvk : ∀ i < 4, M.k (A.pb + 1 + i) = (digestLanes vk).getD i 0) (hppl : A.ppt.length = A.τp)
    (hfs : m.fixSent (pubOf vk cc sig) evals = A.fx.map (Cell.val M))
    (hpc : m.pubCheck (pubOf vk cc sig) evals =
      (A.pv.val M == M3.pubEval (pubOf vk cc sig).hdrLanes (A.ppt.map (Cell.val M))))
    (htp : tablePoint evals = A.rc.map (Cell.val M)) :
    Ok c M (qacc A) p → ∀ s : RS, s.ent + s.msg = 8 * A.L → s.ok = true →
      (accFold P m (pubOf vk cc sig) evals sig s).2.ok = true ∧
      (accFold P m (pubOf vk cc sig) evals sig s).2.ent +
        (accFold P m (pubOf vk cc sig) evals sig s).2.msg = 8 * A.z0 + 24 ∧
      (accFold P m (pubOf vk cc sig) evals sig s).1 = accC M A.pb := by
  intro h s hs hok
  have F := qacc_facts hS hT hH hg hpp hτp hla hnf hRD h
  have hD : accVars = 43 := rfl
  rw [accFold_run P m _ evals sig s (by omega)]
  simp only [hs, hdk, phH, phZ]
  -- positions as lanes
  have pk : ∀ i, 8 * A.L + 40 + 72 * i = 8 * A.kap i := by intro i; simp only [AccIn.kap]; ring
  have phv : ∀ j, 8 * A.L + 72 * A.dk + 40 + 24 * j = 8 * A.hL j := by
    intro j; simp only [AccIn.hL, AccIn.h0]; ring
  have ptv : 8 * A.L + 72 * A.dk + 24 * (accVars + 1) + 40 = 8 * A.tL := by
    simp only [AccIn.tL, AccIn.h0]; ring
  have pzv : 8 * A.L + 72 * A.dk + 24 * (accVars + 1) + 72 + 40 = 8 * A.zL := by
    simp only [AccIn.zL, AccIn.z0, AccIn.h0]; ring
  have hkap : samplesAt (feAt sig) (8 * A.L) A.dk =
      (List.range A.dk).map fun i => feAt sig (8 * A.kap i) := by
    simp only [samplesAt]; apply List.map_congr_left; intro i _; rw [pk]
  have hhs : scalarsAt (feAt sig) (8 * A.L + 72 * A.dk + 40) (accVars + 1) =
      (List.range (accVars + 1)).map fun j => feAt sig (8 * A.hL j) := by
    simp only [scalarsAt]; apply List.map_congr_left; intro j _; rw [phv]
  have hacc : ∀ i, headerAt (offAcc + eBytes * i) = 8 * accLane i := by
    intro i; simp only [headerAt, offAcc, eBytes, sigBytes, accLane]; omega
  have hy : (pubOf vk cc sig).accIn.y = feAt sig (8 * accLane accVars) := by
    show feAt sig (headerAt (offAcc + eBytes * accVars)) = _; rw [hacc]
  have hpt : (pubOf vk cc sig).accIn.pt = (List.range accVars).map fun i => feAt sig (8 * accLane i) := by
    show (List.range accVars).map (fun i => feAt sig (headerAt (offAcc + eBytes * i))) = _
    simp only [hacc]
  rw [hkap, hhs, ptv, pzv, hfs, hpc, htp]
  refine ⟨?_, by simp only [AccIn.z0, AccIn.h0]; ring, ?_⟩
  · -- the four checks
    have c2 : sumE ((List.range (accVars + 1)).map fun j => feAt sig (8 * A.hL j)) =
        Lvm.dot (eqKernel ((List.range A.dk).map fun i => feAt sig (8 * A.kap i))) (A.fx.map (Cell.val M)) := by
      rw [sumE_eq, F.sum, dot_eqKernel _ _ (by simp only [List.length_map, List.length_range]; exact hnf)]
      simp only [List.length_map]
      refine Finset.sum_congr rfl fun k hk => ?_
      rw [Finset.mem_range] at hk
      simp only [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_eq_getElem hk,
        Option.map_some, Option.getD_some]
    have c3 : ((List.range (accVars + 1)).map fun j => feAt sig (8 * A.hL j)).headD 0 =
        (pubOf vk cc sig).accIn.y := by
      rw [hy, ← F.h0, List.range_succ_eq_map, List.map_cons, List.headD_cons]
    have c4 : A.pv.val M = M3.pubEval (pubOf vk cc sig).hdrLanes (A.ppt.map (Cell.val M)) := by
      rw [F.pub, pubEval_child hS hH cc (vkc := A.pb + 1) (fun i hi => by rw [hvk i hi]) _ (by
        simpa [hppl] using hτp)]
      have : A.ppt.map (Cell.val M) = (List.range A.τp).map fun i => (A.pp i).val M := by
        apply List.ext_getElem (by simp [hppl])
        intro i h1 h2
        simp [AccIn.pp, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by simpa using h1)]
      rw [this]
    rw [c2, c3, c4, F.zero]
    simp [hok, QB.FE.beq_iff]
  · -- the folded claim
    show _ = Acc.mk (accC M A.pb).pt (accC M A.pb).y
    refine congrArg₂ Acc.mk ?_ F.y
    rw [hpt]
    apply List.ext_getElem
    · simp [accLine, accC, List.length_zipWith, hRD]
    intro i h1 h2
    have hi : i < accVars := by simpa [accC] using h2
    have := F.line i hi
    rw [List.getD_eq_getElem _ _ h2] at this
    rw [← this]
    simp only [accLine, List.getElem_zipWith, List.getElem_map, List.getElem_range]
    congr 2
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by simp [List.length_append, hRD]; omega),
      Option.getD_some]

/-- **Q_acc in HAR's `Replays` form** (phase 3b from `8 L` to phase 4's start `8 z0 + 24`; the value is
the current proof's `acc_in`, `accC M pb`). -/
theorem qacc_replays {c : Ctx} {sig : ByteArray} {T : Nat} {A : AccIn} {p : Ptr}
    (P : Params) (m : M3) (vk cc : Vector UInt8 32) (evals : List (List FE × List FE))
    (hS : Streamed M sig T) (hT : A.zL + 2 < T) (hH : 11 + pubLanes ≤ T) (hg : M.k A.pb = 1)
    (hpp : ∀ i, (A.pp i).ty = .E) (hτp : pubLanes ≤ 2 ^ A.τp) (hla : A.la ≤ A.dk)
    (hnf : A.fx.length ≤ 2 ^ A.dk) (hRD : A.rc.length + A.dk = accVars)
    (hdk : P.accLog = A.dk) (hdk1 : 1 ≤ A.dk)
    (hvk : ∀ i < 4, M.k (A.pb + 1 + i) = (digestLanes vk).getD i 0) (hppl : A.ppt.length = A.τp)
    (hfs : m.fixSent (pubOf vk cc sig) evals = A.fx.map (Cell.val M))
    (hpc : m.pubCheck (pubOf vk cc sig) evals =
      (A.pv.val M == M3.pubEval (pubOf vk cc sig).hdrLanes (A.ppt.map (Cell.val M))))
    (htp : tablePoint evals = A.rc.map (Cell.val M)) :
    Har.Replays c M sig (accFold P m (pubOf vk cc sig) evals) (qacc A) p (8 * A.L) (8 * A.z0 + 24)
      (fun a _ => a = accC M A.pb) := fun h s hs hok =>
  qacc_sound P m vk cc evals hS hT hH hg hpp hτp hla hnf hRD hdk hdk1 hvk hppl hfs hpc htp h s hs hok

/-- The values of the table gadget's cells (`tabPh`'s result shape). -/
def evV (M : Mem) (evc : List (List Cell × List Cell)) : List (List FE × List FE) :=
  evc.map fun e => (e.1.map (Cell.val M), e.2.map (Cell.val M))

end Lvm.QAcc
end

section
set_option autoImplicit false
namespace Lvm.QAcc
open Lvm Lvm.Loop Lvm.Loop.Build Lvm.QSig Lvm.Q1 DM
variable {M : Mem}

theorem tablePoint_evV (evc : List (List Cell × List Cell)) :
    tablePoint (evV M evc) = (tablePointC evc).map (Cell.val M) := by
  have key : ∀ (l : List (List Cell × List Cell)) (r : List Cell),
      (evV M l).foldl (fun r e => if r.length < e.1.length then e.1 else r) (r.map (Cell.val M)) =
        (l.foldl (fun r e => if r.length < e.1.length then e.1 else r) r).map (Cell.val M) := by
    intro l
    induction l with
    | nil => intro r; rfl
    | cons e l ih =>
      intro r
      simp only [evV, List.map_cons, List.foldl_cons, List.length_map] at ih ⊢
      split_ifs with h
      · exact ih e.1
      · exact ih r
  exact key evc []

/-- `fixCols`' evaluation cells (`zc` a cell holding `0`, for columns past a table's end). -/
def fixCellsR (tabs : List M3.Tab) (pubTab : Nat) (evc : List (List Cell × List Cell)) (zc : Cell) :
    List Cell :=
  (M3.fixColsR tabs pubTab).map fun c => (evc.getD c.tab default).2.getD c.col zc

theorem getD_evV (evc : List (List Cell × List Cell)) (j : Nat) :
    (evV M evc).getD j default = ((evc.getD j default).1.map (Cell.val M), (evc.getD j default).2.map (Cell.val M)) := by
  simp only [evV, List.getD_eq_getElem?_getD, List.getElem?_map]
  cases evc[j]? <;> rfl

theorem getD_vals (l : List Cell) (zc : Cell) (hz : zc.val M = 0) (i : Nat) :
    (l.map (Cell.val M)).getD i 0 = (l.getD i zc).val M := by
  simp only [List.getD_eq_getElem?_getD, List.getElem?_map]
  cases l[i]? <;> simp [hz]

theorem fixSentR_evV (tabs : List M3.Tab) (pubTab : Nat) (evc : List (List Cell × List Cell)) {zc : Cell}
    (hz : zc.val M = 0) :
    M3.fixSentR tabs pubTab (evV M evc) = (fixCellsR tabs pubTab evc zc).map (Cell.val M) := by
  simp only [M3.fixSentR, fixCellsR, List.map_map]
  apply List.map_congr_left; intro x _
  simp only [Function.comp_apply, getD_evV, getD_vals _ zc hz]

theorem pubCheckR_evV (pubTab : Nat) (pub : Pub) (evc : List (List Cell × List Cell)) {zc : Cell}
    (hz : zc.val M = 0) :
    M3.pubCheckR pubTab pub (evV M evc) = (((evc.getD pubTab default).2.getD 0 zc).val M ==
      M3.pubEval pub.hdrLanes ((evc.getD pubTab default).1.map (Cell.val M))) := by
  simp only [M3.pubCheckR, M3.pubCheckRW, getD_evV, getD_vals _ zc hz]

end Lvm.QAcc
end
