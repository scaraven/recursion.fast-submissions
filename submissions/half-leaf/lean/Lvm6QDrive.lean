-- New for lvm6 (WP CA). The replay argument of season 1's `LvmReplay.drive_replayP`, re-done for the
-- plan-driven program `drive6` (no schedule walk inside the program: the plan is data).
import Lvm6QPlan
import LvmReplayBase

/-!
# A linked trace replays the plan-driven program (CA-1)

**`replay6`**: if every link of the plan points backwards (`refsOK`, decided per `Shape`) and the
trace meets its plan (`LinkOk6`, what `Q_link` asserts), then `drive6` on the proof the trace
carries (`reassemble6`) asks exactly the trace's queries, in order, and returns `F tr`:
`runSeq tr (drive6 P c (reassemble6 P tr) F) = some (F tr)`.

The proof walks the plan with the cursor at the length of the contributions so far (`bodyTo`); at
each entry the query `mkQ` builds is the trace's (`mkQ_eq`), and the cap check after it
holds (`postOK_eq`).
-/

set_option autoImplicit false

namespace Lvm6.Q

open RecursionFast Lvm Lvm.Replay

/-! ## Prefixes of a trace -/

theorem getD_take_lt (tr : Trace) {k j : ℕ} (h : j < k) (d : ByteArray × Digest) :
    (tr.take k).getD j d = tr.getD j d := by
  simp only [List.getD_eq_getElem?_getD, List.getElem?_take, if_pos h]

theorem aOf_take (tr : Trace) {k j : ℕ} (h : j < k) : aOf (tr.take k) j = aOf tr j := by
  simp only [aOf, getD_take_lt tr h]

theorem qOf_take (tr : Trace) {k j : ℕ} (h : j < k) : qOf (tr.take k) j = qOf tr j := by
  simp only [qOf, getD_take_lt tr h]

theorem posOf_take (tr : Trace) {k pd : ℕ} (h : pd < k) (sh hh : ℕ) :
    posOf (tr.take k) pd sh hh = posOf tr pd sh hh := by
  simp only [posOf, aOf_take tr h]

theorem take_succ_eq (tr : Trace) {k : ℕ} (hk : k < tr.length) :
    tr.take (k + 1) = tr.take k ++ [(qOf tr k, aOf tr k)] := by
  rw [List.take_succ, List.getElem?_eq_getElem hk]
  simp only [Option.toList_some, qOf, aOf, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hk,
    Option.getD_some]

theorem drop_eq_cons (tr : Trace) {k : ℕ} (hk : k < tr.length) :
    tr.drop k = (qOf tr k, aOf tr k) :: tr.drop (k + 1) := by
  rw [List.drop_eq_getElem_cons hk]
  simp only [qOf, aOf, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hk, Option.getD_some]

/-! ## The body as a growing prefix -/

theorem bodyTo_succ (tr : Trace) (P : List PE6) (k : ℕ) :
    bodyTo tr P (k + 1) = bodyTo tr P k ++ contrib6 tr k (P.getD k default) := by
  simp only [bodyTo, List.range_succ, List.flatMap_append, List.flatMap_cons, List.flatMap_nil,
    List.append_nil]

theorem bodyTo_prefix (tr : Trace) (P : List PE6) (k : ℕ) :
    ∀ m, ∃ R, bodyTo tr P (k + m) = bodyTo tr P k ++ R
  | 0 => ⟨[], by simp⟩
  | m + 1 => by
    obtain ⟨R, hR⟩ := bodyTo_prefix tr P k m
    exact ⟨R ++ contrib6 tr (k + m) (P.getD (k + m) default), by
      rw [← Nat.add_assoc, bodyTo_succ, hR, List.append_assoc]⟩

/-- At entry `k < n`, the rest of the body starts with entry `k`'s contribution. -/
theorem body_at (tr : Trace) (P : List PE6) {k : ℕ} (hk : k < P.length) :
    ∃ R, (bl (reassemble6 P tr)).drop (bodyTo tr P k).length = contrib6 tr k (P.getD k default) ++ R := by
  obtain ⟨R, hR⟩ := bodyTo_prefix tr P (k + 1) (P.length - (k + 1))
  rw [show k + 1 + (P.length - (k + 1)) = P.length by omega, bodyTo_succ] at hR
  refine ⟨R, ?_⟩
  rw [reassemble6, bl_mk, hR, List.append_assoc, List.drop_left]

/-! ## Byte facts -/

theorem bl_size (b : ByteArray) : (bl b).length = b.size := (size_bl b).symm

theorem take_drop_eq (l : List UInt8) (n : ℕ) : l.take n ++ l.drop n = l := List.take_append_drop n l

theorem ba_of_bl {a b : ByteArray} (h : bl a = bl b) : a = b := ba_ext h

/-- The bytes `[a, a + n)` of `π`, inside the body read at `a` (season 1's `bl_extract_body`). -/
theorem bl_extract_body {π : ByteArray} {a : ℕ} {c rest : List UInt8} (h : (bl π).drop a = c ++ rest)
    {n : ℕ} (hn : c.length = n) : bl (π.extract a (a + n)) = c := by
  rw [bl_extract, h, Nat.add_sub_cancel_left, List.take_left' hn]

/-! ## Each entry's query is the trace's -/

section
variable {P : List PE6} {c : Digest} {tr : Trace}

theorem mkQ_eq (hR : refsOK P = true) (hL : LinkOk6 P c tr) {k : ℕ} (hk : k < P.length) :
    mkQ c (reassemble6 P tr) (bodyTo tr P k).length (tr.take k) k (P.getD k default) =
      (qOf tr k, (bodyTo tr P (k + 1)).length) := by
  have hkt : k < tr.length := hL.1 ▸ hk
  have hG := hL.2 k hkt
  have hr : refsOK1 k (P.getD k default) = true := refsOK_get hR hk
  obtain ⟨R, hB⟩ := body_at tr P hk
  rw [bodyTo_succ, List.length_append]
  generalize P.getD k default = e at hG hr hB
  obtain ⟨hsz, hG⟩ := hG
  have hsz' : (bl (qOf tr k)).length = e.len := by rw [bl_size, hsz]
  rcases e with ⟨ek, len⟩
  cases ek with
  | q0 =>
    simp only [refsOK1, Bool.and_eq_true, beq_iff_eq] at hr
    simp only [mkQ, contrib6, List.length_nil, Nat.add_zero, Prod.mk.injEq, and_true]
    exact ba_of_bl (by rw [hG]; rfl)
  | seed =>
    simp only [refsOK1, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at hr
    simp only [contrib6] at hB ⊢
    have hl : ((bl (qOf tr k)).drop 64).length = len - 64 := by rw [List.length_drop, hsz']
    simp only [mkQ, hl, Prod.mk.injEq, and_true]
    apply ba_of_bl
    rw [bl_append, bl_append, bl_digestBytes, bl_digestBytes,
      bl_extract_body hB hl, aOf_take tr (by omega), ← hG, take_drop_eq]
  | fs st g =>
    simp only [refsOK1, Bool.and_eq_true, decide_eq_true_eq] at hr
    simp only [contrib6] at hB ⊢
    have hl : ((bl (qOf tr k)).drop 32).length = len - 32 := by rw [List.length_drop, hsz']
    simp only [mkQ, hl, Prod.mk.injEq, and_true]
    apply ba_of_bl
    rw [bl_append, bl_digestBytes, bl_extract_body hB hl, aOf_take tr hr.1, ← hG, take_drop_eq]
  | leaf =>
    simp only [contrib6] at hB ⊢
    simp only [mkQ, hsz', Prod.mk.injEq, and_true]
    exact ba_of_bl (bl_extract_body hB hsz')
  | node pd sh h lvl cap =>
    simp only [refsOK1, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at hr
    obtain ⟨⟨⟨⟨hpd, hk1⟩, hlen⟩, -⟩, -⟩ := hr
    subst hlen
    have hcl : (contrib6 tr k ⟨.node pd sh h lvl cap, 64⟩).length = 32 := by
      simp only [contrib6]; split <;> simp [hsz']
    simp only [mkQ, hcl, Prod.mk.injEq, and_true]
    rw [posOf_take tr hpd, aOf_take tr (by omega)]
    apply ba_of_bl
    have hsib := bl_extract_body hB hcl
    obtain ⟨hlink, -⟩ := hG
    have ht : ((bl (qOf tr k)).take 32).length = 32 := by rw [List.length_take, hsz']; rfl
    split
    · next hb =>
      rw [if_pos hb] at hlink
      rw [bl_append, bl_digestBytes, hsib]
      simp only [contrib6]
      rw [if_pos hlink, ← hlink, take_drop_eq]
    · next hb =>
      rw [if_neg hb] at hlink
      rw [bl_append, bl_digestBytes, hsib, ← hlink]
      simp only [contrib6]
      split
      · next he =>
        have e2 : (bl (qOf tr k)).take 32 = (bl (qOf tr k)).drop 32 := he.trans hlink.symm
        rw [show (bl (qOf tr k)).drop 32 ++ (bl (qOf tr k)).drop 32 =
          (bl (qOf tr k)).take 32 ++ (bl (qOf tr k)).drop 32 by rw [e2], take_drop_eq]
      · exact take_drop_eq _ _

theorem postOK_eq (hR : refsOK P = true) (hL : LinkOk6 P c tr) {k : ℕ} (hk : k < P.length) :
    postOK (tr.take k ++ [(qOf tr k, aOf tr k)]) k (P.getD k default) = true := by
  have hkt : k < tr.length := hL.1 ▸ hk
  have hG := hL.2 k hkt
  have hr : refsOK1 k (P.getD k default) = true := refsOK_get hR hk
  rw [← take_succ_eq tr hkt]
  generalize P.getD k default = e at hG hr
  obtain ⟨-, hG⟩ := hG
  rcases e with ⟨ek, len⟩
  cases ek with
  | fs st g => rfl
  | node pd sh h lvl cap =>
    cases cap with
    | none => rfl
    | some cp =>
      obtain ⟨ce, co, path⟩ := cp
      simp only [refsOK1, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at hr
      simp only [postOK]
      rw [aOf_take tr (Nat.lt_succ_self k), qOf_take tr (by omega), posOf_take tr (by omega), hG.2]
      exact beq_self_eq_true _
  | q0 => rfl
  | seed => rfl
  | leaf => rfl

/-- The replay, from entry `k` on. -/
theorem replay_from (hR : refsOK P = true) (hL : LinkOk6 P c tr) (F : Trace → Bool) :
    ∀ m k, k + m = P.length →
      OProg.runSeq (tr.drop k) (drv c (reassemble6 P tr) F (P.drop k) k (bodyTo tr P k).length (tr.take k)) =
        some (F tr)
  | 0, k, hkm => by
    have hk : k = P.length := by omega
    subst hk
    rw [List.drop_eq_nil_of_le (by rw [hL.1]), List.drop_eq_nil_of_le (le_refl _),
      List.take_of_length_le (by rw [hL.1])]
    simp only [drv, OProg.runSeq, reassemble6, ByteArray.size, List.size_toArray, beq_self_eq_true,
      Bool.true_and]
  | m + 1, k, hkm => by
    have hk : k < P.length := by omega
    have hkt : k < tr.length := hL.1 ▸ hk
    rw [List.drop_eq_getElem_cons hk, drop_eq_cons tr hkt]
    have hgd : P[k] = P.getD k default := by
      rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hk, Option.getD_some]
    rw [hgd]
    simp only [drv, OProg.runSeq, mkQ_eq hR hL hk, if_true, postOK_eq hR hL hk]
    rw [← take_succ_eq tr hkt]
    exact replay_from hR hL F m (k + 1) (by omega)

/-- **A linked trace replays the plan-driven program** (CA-1). -/
theorem replay6 (hR : refsOK P = true) (hL : LinkOk6 P c tr) (F : Trace → Bool) :
    OProg.runSeq tr (drive6 P c (reassemble6 P tr) F) = some (F tr) := by
  have := replay_from hR hL F P.length 0 (by omega)
  simpa [drive6, bodyTo] using this

end

end Lvm6.Q
