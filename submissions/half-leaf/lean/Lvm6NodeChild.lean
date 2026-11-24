-- New for lvm6 (WP NODE). The child side of `node6`: CA3's two open items (the reassembled proof's header
-- check and magic), the child accepted by `VSasm` from `ChildOk`, and `node6V` from the child and `σ_leaf`.
import Lvm6NodeStmt
import Lvm6VHdr
import Lvm6QLinkP17

/-!
# The child accepted, and `node6V` from the child

* **`hdrOk_of_childHdr6 : Stmt.hdrOk_of_childHdr6`**, **`isS_of_childHdr6 : Stmt.isS_of_childHdr6`** (CA3): the
  reassembled proof of a linked trace of `planOf P17` starts with the seed's `HDR` (`bl_reassemble`: entry 0
  carries nothing, entry 1 its `HDR`, 824 bytes), so `V_S`'s header check reads `ChildHdr6`'s bytes.
* **`accV_of_childOk`**: `ChildOk Φ vk c tr σ` gives `accV (VSasm Φ P17) vk c ⟨reassemble6 P6 tr, tr, σ⟩` (CA's
  `accV_of_link` with the static facts at `P17`: `simOK_P17`, `planOf_P17`, `cdConsts_P17`).
* **`node6V_of_child`**: if in node mode the tree relation and `rest` give `ChildOk` of the stack's child for
  `(x.vk, x.c')` and `σ_leaf` signing `traceDigest []` under `x.vk`, then `Stmt.node6V (VSasm Φ) rest`.
-/

set_option autoImplicit false

namespace Lvm6.Node

open RecursionFast Lvm.T Lvm6.Q Lvm.Replay
open RecursionFast.WitnessSending (encode)

/-! ## Bytes -/

theorem u64At_le8 (x : ByteArray) (o : ℕ) : Lvm.u64At x o = le8 (bl x) o := by
  show (Lvm.laneAt x o).toNat = _
  rw [Lvm.VEq.toNat_laneAt]
  simp only [le8, Fin.sum_univ_eight, List.range_succ, List.range_zero, List.nil_append, List.map_cons,
    List.map_nil, List.sum_cons, List.sum_nil, List.map_append, List.sum_append, get!_bl]
  norm_num

theorem digestAt_dig32 (x : ByteArray) (o : ℕ) : Lvm.digestAt x o = dig32 (bl x) o := by
  apply Vector.ext
  intro i hi
  simp only [Lvm.digestAt, dig32, Vector.getElem_ofFn, get!_bl]

/-! ## The reassembled proof starts with `HDR` -/

theorem P6_eq : P6 = Lvm6.planP17 := Lvm6.planOf_P17_eq

theorem P6_get0 : P6.getD 0 default = ⟨.q0, 7⟩ := by
  rw [P6_eq]
  rfl

theorem P6_get1 : P6.getD 1 default = ⟨.fs 0 0, seedLen P17⟩ := by
  rw [P6_eq, seedLen_P17.1]
  rfl

theorem P6_two : 2 ≤ P6.length := cdConsts_P17.2.2.2.2.1

theorem hdrLen_P17 : hdrLen P17 = 824 := cdConsts_P17.2.1

theorem seed_size {c : Digest} {tr : Trace} (hL : LinkOk6 P6 c tr) : (qOf tr 1).size = 856 := by
  have h := (hL.2 1 (by rw [hL.1]; exact P6_two)).1
  rw [h]
  exact cdConsts_P17.2.2.2.1

theorem hdrOf6_length {c : Digest} {tr : Trace} (hL : LinkOk6 P6 c tr) : (hdrOf6 tr).length = 824 := by
  rw [hdrOf6, List.length_drop, Lvm6.Q.bl_size, seed_size hL]

theorem bodyTo_succ (tr : Trace) (P : List PE6) (k : ℕ) :
    bodyTo tr P (k + 1) = bodyTo tr P k ++ contrib6 tr k (P.getD k default) := by
  simp [bodyTo, List.range_succ]

theorem bodyTo_P6_two (tr : Trace) : bodyTo tr P6 2 = hdrOf6 tr := by
  rw [bodyTo_succ, bodyTo_succ, P6_get0, P6_get1]
  simp [bodyTo, contrib6, hdrOf6]

theorem bodyTo_P6_from (tr : Trace) : ∀ j, ∃ rest, bodyTo tr P6 (j + 2) = hdrOf6 tr ++ rest
  | 0 => ⟨[], by rw [bodyTo_P6_two, List.append_nil]⟩
  | j + 1 => by
    obtain ⟨r, hr⟩ := bodyTo_P6_from tr j
    exact ⟨r ++ _, by rw [show j + 1 + 2 = (j + 2) + 1 by omega, bodyTo_succ, hr, List.append_assoc]⟩

/-- **The reassembled proof is `HDR ‖ BODY`**: its bytes start with the seed's `HDR`. -/
theorem bl_reassemble (tr : Trace) : ∃ rest, bl (reassemble6 P6 tr) = hdrOf6 tr ++ rest := by
  rw [reassemble6, bl_mk]
  have h := bodyTo_P6_from tr (P6.length - 2)
  rwa [show P6.length - 2 + 2 = P6.length by have := P6_two; omega] at h

theorem extract_hdr {c : Digest} {tr : Trace} (hL : LinkOk6 P6 c tr) :
    bl ((reassemble6 P6 tr).extract 0 (hdrLen P17)) = hdrOf6 tr := by
  obtain ⟨rest, h⟩ := bl_reassemble tr
  rw [show hdrLen P17 = 0 + (hdrOf6 tr).length by rw [hdrOf6_length hL, hdrLen_P17]]
  exact Lvm6.Q.bl_extract_body (by rw [List.drop_zero, h]) rfl

theorem magic_getD {H : List UInt8} (hm : H.take 8 = magic6) {i : ℕ} (hi : i < 8) :
    H.getD i 0 = magic6.getD i 0 := by
  rw [← hm, List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, List.getElem?_take, if_pos hi]

/-- **CA3 open item 1.** -/
theorem hdrOk_of_childHdr6 : Stmt.hdrOk_of_childHdr6 := by
  intro vk c tr hL hH
  have hbl := extract_hdr hL
  simp only [ChildHdr6] at hH
  obtain ⟨hm, hb, hn, hz, hv, hc⟩ := hH
  generalize (reassemble6 P6 tr).extract 0 (hdrLen P17) = x at hbl ⊢
  have hlog : (2 : ℕ) ^ P17.logN = 2 ^ 17 := rfl
  have e1 : ((List.range 8).all fun i => x.get! i == V.magic6.getD i 0) = true := by
    refine List.all_eq_true.mpr fun i hi => ?_
    have hi8 := List.mem_range.mp hi
    rw [get!_bl, hbl, beq_iff_eq, magic_getD hm hi8]
    rfl
  have e2 : decide (Lvm.digestAt x 88 = vk) = true := by
    rw [digestAt_dig32, hbl]; exact decide_eq_true hv
  have e3 : (Lvm.u64At x 8 == 0 || Lvm.u64At x 8 == 1) = true := by
    rw [u64At_le8, hbl]; rcases hb with h | h <;> simp [h]
  have e4 : (Lvm.u64At x 16 == 2 ^ P17.logN) = true := by
    rw [u64At_le8, hbl, hn, hlog]; exact beq_self_eq_true _
  have e5 : (Lvm.u64At x 8 != 0 || decide (Lvm.digestAt x 56 = Lvm.zeroDigest)) = true := by
    rw [u64At_le8, digestAt_dig32, hbl]
    by_cases h0 : le8 (hdrOf6 tr) 8 = 0
    · simp [h0, hz h0]
    · simp [h0]
  have e6 : decide (c = V.stmtWith leafStmtF nodeStmtF x) = true := by
    rw [V.stmtWith, u64At_le8, u64At_le8, digestAt_dig32, digestAt_dig32, hbl, leafStmtF_eq, nodeStmtF_eq]
    exact decide_eq_true hc
  simp only [V.hdrOkWith, e1, e2, e3, e4, e5, e6, Bool.and_self]

theorem data_getD (π : ByteArray) : π.data.getD 0 0 = (bl π).getD 0 0 := by
  first
    | simp [bl, List.getD_eq_getElem?_getD, Array.getD_eq_getD_getElem?]
    | simp [bl, Array.getD, List.getD_eq_getElem?_getD]

/-- **CA3 open item 2.** -/
theorem isS_of_childHdr6 : Stmt.isS_of_childHdr6 := by
  intro vk c tr hL hH
  obtain ⟨rest, h⟩ := bl_reassemble tr
  have h0 : (bl (reassemble6 P6 tr)).getD 0 0 = 0x53 := by
    rw [h, List.getD_eq_getElem?_getD, List.getElem?_append_left (by rw [hdrOf6_length hL]; omega),
      ← List.getD_eq_getElem?_getD, magic_getD hH.1 (by omega)]
    rfl
  unfold isS
  rw [data_getD, h0]
  rfl

/-! ## The child accepted -/

theorem contrib6_length (tr : Trace) (i : ℕ) (e : PE6) : (contrib6 tr i e).length ≤ (qOf tr i).size := by
  have hb : (bl (qOf tr i)).length = (qOf tr i).size := by rw [bl, Array.length_toList]; rfl
  unfold contrib6
  split
  · simp
  · simp [hb]
  · simp [hb]
  · simp [hb]
  · split_ifs <;> simp [hb]

theorem qOf_size_le {c : Digest} {tr : Trace} (hL : LinkOk6 P6 c tr) (hcap : ∀ e ∈ P6, e.len ≤ queryCap)
    (i : ℕ) : (qOf tr i).size ≤ queryCap := by
  by_cases hi : i < tr.length
  · have hq : qOf tr i = tr[i].1 := by
      simp only [qOf, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi, Option.getD_some]
    rw [hq]
    exact size_of_link hL hcap _ (List.getElem_mem hi)
  · rw [qOf, List.getD_eq_getElem?_getD, List.getElem?_eq_none (show tr.length ≤ i by omega)]
    exact Nat.zero_le _

theorem size_mk (l : List UInt8) : (⟨l.toArray⟩ : ByteArray).size = l.length := by
  simp [ByteArray.size]

theorem sum_const_range (n c : ℕ) : ((List.range n).map fun _ => c).sum = n * c := by
  simp

theorem reassemble6_size {c : Digest} {tr : Trace} (hL : LinkOk6 P6 c tr) (hcap : ∀ e ∈ P6, e.len ≤ queryCap)
    (hn : P6.length ≤ 16384) : (reassemble6 P6 tr).size < 2 ^ 64 := by
  have hs : (reassemble6 P6 tr).size = (bodyTo tr P6 P6.length).length := size_mk _
  have hle : (bodyTo tr P6 P6.length).length ≤ P6.length * queryCap := by
    rw [bodyTo, List.length_flatMap]
    calc ((List.range P6.length).map fun i => (contrib6 tr i (P6.getD i default)).length).sum
        ≤ ((List.range P6.length).map fun _ => queryCap).sum :=
          List.sum_le_sum fun i _ => (contrib6_length tr i _).trans (qOf_size_le hL hcap i)
      _ = P6.length * queryCap := sum_const_range _ _
  rw [hs]
  calc _ ≤ P6.length * queryCap := hle
    _ ≤ 16384 * queryCap := Nat.mul_le_mul_right _ hn
    _ < 2 ^ 64 := by simp [queryCap]

theorem P6_len_le : P6.length ≤ 16384 := by
  rw [planOf_P17.2.2.1, qS_P17]
  decide

theorem P6_cap : ∀ e ∈ P6, e.len ≤ queryCap := by
  intro e he
  exact of_decide_eq_true (List.all_eq_true.mp planOf_P17.2.2.2.2 e he)

/-- `accV` of an `'S'` proof reads `VS` at the key only. -/
theorem accV_S {VS VS' : SProg} {vk c : Digest} {p : Signed} (hS : isS p.π = true)
    (h : VS vk c p.π = VS' vk c p.π) : accV VS vk c p = accV VS' vk c p := by
  simp only [accV]
  rw [V_S VS vk c p.π hS, V_S VS' vk c p.π hS, h]

/-- **The child is accepted** by `VSasm Φ P17`. -/
theorem accV_of_childOk {Φ : Phases} {vk c : Digest} {tr : Trace} {σ : Sig} (h : ChildOk Φ vk c tr σ) :
    accV (VSasm Φ P17) vk c ⟨reassemble6 P6 tr, tr, σ⟩ = true := by
  have hS := isS_of_childHdr6 vk c tr h.link h.hdr
  rw [accV_S (VS' := V.VS6 (Lvm6.toV P17) (F6 Φ P17 vk)) (p := ⟨reassemble6 P6 tr, tr, σ⟩) hS
    (by unfold VSasm; rfl)]
  exact accV_of_link P17 simOK_P17 planOf_P17.2.1 hS h.link (hdrOk_of_childHdr6 vk c tr h.link h.hdr) h.pow
    h.dec (P6_len_le.trans (by decide)) P6_cap (reassemble6_size h.link P6_cap P6_len_le) h.sig

/-! ## `node6V` from the child -/

/-- The child a stack carries: the reassembled proof of the decoded trace `trOf q`, with `σ'`. -/
def childOf6 (trOf : Stack → Trace) (σOf : Stack → Sig) (q : Stack) : Signed :=
  ⟨reassemble6 P6 (trOf q), trOf q, σOf q⟩

/-- **`node6V` from the child and `σ_leaf`**. -/
theorem node6V_of_child (Φ : Phases) (rest : Hdr → Stack → Prop) (trOf : Stack → Trace)
    (σOf σlOf : Stack → Sig)
    (h : ∀ x q, x.b = 1 → TreeOk q x.h → rest x q →
      ChildOk Φ x.vk x.c' (trOf q) (σOf q) ∧ SigOk x.vk (traceDigest []) (σlOf q) = true) :
    Stmt.node6V (VSasm Φ) rest (childOf6 trOf σOf) σlOf := by
  intro vk c x q hwf hok hvk hg
  rcases hwf.b_le with hb | hb
  · exact node6_leaf (VSasm Φ P17) vk rest _ _ hwf hok hb hg
  obtain ⟨hch, hsl⟩ := h x q hb hg.1 hg.2
  subst hvk
  have hc : c = stmtOf x := of_decide_eq_true hok
  have hb0 : x.b ≠ 0 := by rw [hb]; decide
  rw [witOf6, if_neg hb0]
  have hR : Rel (accV (VSasm Φ P17) x.vk) (leafStmt x.h x.n.toNat) (.leaf (blocksOf q)) := by
    refine ⟨by simp [length_blocksOfAt, leafCap], ?_⟩
    rw [length_blocksOfAt, treeOk_sound hg.1, hwf.n_eq]
    rfl
  refine ⟨?_, accV_of_childOk hch, ?_⟩
  · rw [hc, stmtOf, if_neg hb0, leafStmtF_eq, nodeStmtF_eq]
  · simp only [accV, accWith, Bool.and_eq_true, decide_eq_true_eq, SigOkF_eq, traceDigestF_eq]
    refine ⟨⟨⟨⟨?_, by simp⟩, by simp⟩, hsl⟩, ?_⟩
    · rw [WitnessSending.size_encode_leaf, length_blocksOfAt]
      norm_num
    · rw [V_encode _ hR]
      rfl

end Lvm6.Node
