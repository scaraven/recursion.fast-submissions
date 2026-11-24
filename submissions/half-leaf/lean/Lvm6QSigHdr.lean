-- New for lvm6 (WP CA). From `qsig6_sound`'s cell facts to the trace-level `ChildHdr6` on the stream's
-- decoded trace (season 1's `hdrBridgeS`, re-done on `decode6` instead of the reassembled proof).
import Lvm6QSig

/-!
# The child's header, from cells to the trace (CA-3)

**`childHdr6_of_cells`**: if the stream cells from `sb` hold the stream words, the header copy's facts
hold (`hdrCopy6_spec`) and season 1's `ChildOkS` holds on the copy, then the decoded trace's `HDR`
passes `ChildHdr6` for the statement in the cells `I.cL`.
-/

set_option autoImplicit false

namespace Lvm6.Q

open RecursionFast Lvm Lvm.Loop Lvm.Replay Lvm.QLink Lvm.QSig Lvm.Wots

/-- Entry 0 (`q₀`) takes the stream's bytes 1–47. -/
theorem slen1 {P : List PE6} (h0 : (P.getD 0 default).len = 7) (hP : 2 ≤ P.length) :
    slenS ((P.map PE6.len).take 1) = 47 := by
  cases P with
  | nil => simp at hP
  | cons e es => simp only [List.getD_cons_zero] at h0; simp [slenS, h0]

theorem lens1 {P : List PE6} (hP : 2 ≤ P.length) : (P.map PE6.len).getD 1 0 = (P.getD 1 default).len := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_map, List.getD_eq_getElem?_getD,
    List.getElem?_eq_getElem (by omega)]
  simp

theorem seed_entry {P : List PE6} {ws : List Word} (h0 : (P.getD 0 default).len = 7) (hP : 2 ≤ P.length) :
    (decode6 P ws).getD 1 dflt = entryAt (wordsBytes ws) 48 (P.getD 1 default).len := by
  rw [decode6, readEntries_getD _ _ _ _ (by simp; omega), slen1 h0 hP, lens1 hP]

/-- Byte `j` of the seed's `HDR` is stream byte `88 + j` (the seed's query starts at byte 56; FORMAT6
v2.5: `HDR` follows `a₀`). -/
theorem hdr_getD {P : List PE6} {ws : List Word} (h0 : (P.getD 0 default).len = 7) (hP : 2 ≤ P.length)
    {j : ℕ} (hj : 32 + j < (P.getD 1 default).len) :
    (hdrOf6 (decode6 P ws)).getD j 0 = (wordsBytes ws).getD (88 + j) 0 := by
  rw [hdrOf6, qOf, seed_entry h0 hP, entryAt, bl_mk, List.getD_eq_getElem?_getD, List.getElem?_drop,
    List.getElem?_take, if_pos hj, List.getElem?_drop, ← List.getD_eq_getElem?_getD]
  congr 1
  omega

/-- Eight bytes of a word, read back little-endian. -/
theorem le8_word (x : ℕ) (hx : x < 2 ^ 64) :
    ((List.range 8).map fun t => (x / 256 ^ t % 256).toUInt8.toNat * 2 ^ (8 * t)).sum = x := by
  have e : ∀ y : ℕ, y.toUInt8.toNat = y % 256 := fun y => by simp [Nat.toUInt8]
  simp only [List.range_succ, List.range_zero, List.nil_append, List.map_cons, List.map_nil,
    List.sum_cons, List.sum_nil, List.map_append, List.sum_append, e]
  norm_num
  omega

theorem lw_lt64 (ws : List Word) (j : ℕ) : lw ws j < 2 ^ 64 := (ws.getD j 0).isLt

/-- `HDR` word `k` read little-endian is stream word `hdrW k`. -/
theorem le8_hdr {P : List PE6} {ws : List Word} (h0 : (P.getD 0 default).len = 7) (hP : 2 ≤ P.length)
    {k : ℕ} (hk : 32 + 8 * k + 8 ≤ (P.getD 1 default).len) :
    le8 (hdrOf6 (decode6 P ws)) (8 * k) = lw ws (hdrW k) := by
  unfold le8
  rw [← le8_word (lw ws (hdrW k)) (lw_lt64 _ _)]
  congr 1
  apply List.map_congr_left
  intro t ht
  have ht8 := List.mem_range.mp ht
  rw [hdr_getD h0 hP (by omega), show 88 + (8 * k + t) = 8 * hdrW k + t by simp [hdrW, seedW]; omega,
    byte_of_lane ws _ _ ht8]

/-- `HDR` bytes `8k … 8k + 31` as a digest are the four stream words from `hdrW k`, as `digAt` reads
them from cells holding the words. -/
theorem dig32_hdr {P : List PE6} {ws : List Word} (h0 : (P.getD 0 default).len = 7) (hP : 2 ≤ P.length)
    {k : ℕ} (hk : 32 + 8 * k + 32 ≤ (P.getD 1 default).len) {v : ℕ → FK} {a : ℕ}
    (hv : ∀ l < 4, v (a + l) = laneK ws (hdrW k + l)) :
    dig32 (hdrOf6 (decode6 P ws)) (8 * k) = digAt v a := by
  apply Vector.ext
  intro x hx
  simp only [dig32, Vector.getElem_ofFn, digAt]
  rw [digOfW_get _ hx, hdr_getD h0 hP (by omega),
    show 88 + (8 * k + x) = 8 * (hdrW k + x / 8) + x % 8 by simp [hdrW, seedW]; omega,
    byte_of_lane ws _ _ (Nat.mod_lt _ (by norm_num)), hv _ (by omega), byteW_toNat _ (Nat.mod_lt _ (by norm_num)),
    laneK_val]
  exact toUInt8_mod _

/-- **The child's header passes `V_S`'s checks** (CA-3, trace level), from `qsig6_sound`'s cell facts. -/
theorem childHdr6_of_cells {P : List PE6} {ws : List Word} {M : Mem} {I : SigIn} {sb : ℕ}
    (h0 : (P.getD 0 default).len = 7) (hP : 2 ≤ P.length) (h1 : 152 ≤ (P.getD 1 default).len)
    (hB : 56 + (P.getD 1 default).len ≤ (wordsBytes ws).length)
    (hs : ∀ j < 27, M.k (sb + j) = laneK ws j)
    (hcp : ∀ pr ∈ hdrPairs6 I.hd sb, M.k pr.1 = M.k pr.2) (hmg : M.k (sb + hdrW 0) = magicK)
    (hnk : M.k (I.hd + 13) = nStarK) (hch : ChildOkS I M.k) :
    ChildHdr6 (digAt M.k I.vk) (digAt M.k I.cL) (decode6 P ws) := by
  have cp : ∀ a b, (a, b) ∈ hdrPairs6 I.hd sb → M.k a = M.k b := fun a b h => hcp (a, b) h
  have m0 : (I.hd, sb + hdrW 1) ∈ hdrPairs6 I.hd sb :=
    List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _
      (List.mem_singleton_self _))))
  have m13 : (I.hd + 13, sb + hdrW 2) ∈ hdrPairs6 I.hd sb :=
    List.mem_append_left _ (List.mem_append_right _ (List.mem_singleton_self _))
  have mc : ∀ l < 4, (I.hd + 5 + l, sb + hdrW 7 + l) ∈ hdrPairs6 I.hd sb := fun l hl =>
    List.mem_append_left _ (List.mem_append_left _ (List.mem_append_right _
      (List.mem_map.mpr ⟨l, List.mem_range.mpr hl, rfl⟩)))
  have mv : ∀ l < 4, (I.hd + 1 + l, sb + hdrW 11 + l) ∈ hdrPairs6 I.hd sb := fun l hl =>
    List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_right _
      (List.mem_map.mpr ⟨l, List.mem_range.mpr hl, rfl⟩))))
  have mh : ∀ l < 4, (I.hd + 14 + l, sb + hdrW 3 + l) ∈ hdrPairs6 I.hd sb := fun l hl =>
    List.mem_append_right _ (List.mem_map.mpr ⟨l, List.mem_range.mpr hl, rfl⟩)
  have hb : (M.k I.hd).val.toNat = le8 (hdrOf6 (decode6 P ws)) 8 := by
    rw [cp _ _ m0, hs _ (by simp [hdrW, seedW]), laneK_val,
      show (8 : ℕ) = 8 * 1 from rfl, le8_hdr h0 hP (by omega)]
  have hn : (M.k (I.hd + 13)).val.toNat = le8 (hdrOf6 (decode6 P ws)) 16 := by
    rw [cp _ _ m13, hs _ (by simp [hdrW, seedW]), laneK_val,
      show (16 : ℕ) = 8 * 2 from rfl, le8_hdr h0 hP (by omega)]
  have hh : digAt M.k (I.hd + 14) = dig32 (hdrOf6 (decode6 P ws)) 24 := by
    rw [show (24 : ℕ) = 8 * 3 from rfl]
    refine (dig32_hdr h0 hP (by omega) fun l hl => ?_).symm
    rw [cp _ _ (mh l hl), Nat.add_assoc, hs _ (by simp [hdrW, seedW]; omega)]
  have hc : digAt M.k (I.hd + 5) = dig32 (hdrOf6 (decode6 P ws)) 56 := by
    rw [show (56 : ℕ) = 8 * 7 from rfl]
    refine (dig32_hdr h0 hP (by omega) fun l hl => ?_).symm
    rw [cp _ _ (mc l hl), Nat.add_assoc, hs _ (by simp [hdrW, seedW]; omega)]
  have hv : digAt M.k (I.hd + 1) = dig32 (hdrOf6 (decode6 P ws)) 88 := by
    rw [show (88 : ℕ) = 8 * 11 from rfl]
    refine (dig32_hdr h0 hP (by omega) fun l hl => ?_).symm
    rw [cp _ _ (mv l hl), Nat.add_assoc, hs _ (by simp [hdrW, seedW]; omega)]
  obtain ⟨hb01, hvk, -, -, hz, hst⟩ := hch
  have hnv : (M.k (I.hd + 13)).val.toNat = 2 ^ 17 := by rw [hnk]; rfl
  have hlen : 8 ≤ (hdrOf6 (decode6 P ws)).length := by
    rw [hdrOf6, qOf, seed_entry h0 hP]
    simp only [entryAt, bl_mk, List.length_drop, List.length_take]
    omega
  have hmag : (hdrOf6 (decode6 P ws)).take 8 = magic6 := by
    have e1 : (hdrOf6 (decode6 P ws)).take 8 = (List.range 8).map fun t => (hdrOf6 (decode6 P ws)).getD t 0 := by
      apply List.ext_getElem (by simp; omega)
      intro i hi1 hi2
      simp only [List.getElem_take, List.getElem_map, List.getElem_range, List.getD_eq_getElem?_getD,
        List.getElem?_eq_getElem (show i < (hdrOf6 (decode6 P ws)).length by simp at hi1; omega),
        Option.getD_some]
    have e2 : lw ws (hdrW 0) = 0x010000366D766C53 := by
      rw [← laneK_val, ← hs _ (by simp [hdrW, seedW]), hmg]; rfl
    rw [e1]
    have e3 : ((List.range 8).map fun t => (hdrOf6 (decode6 P ws)).getD t 0) =
        (List.range 8).map fun t => ((0x010000366D766C53 : ℕ) / 256 ^ t % 256).toUInt8 := by
      apply List.map_congr_left
      intro t ht
      have ht8 := List.mem_range.mp ht
      rw [hdr_getD h0 hP (by omega), show 88 + t = 8 * hdrW 0 + t by simp [hdrW, seedW],
        byte_of_lane ws _ _ ht8, e2]
    rw [e3]; decide
  refine ⟨hmag, ?_, ?_, ?_, ?_, ?_⟩
  · rw [← hb]; exact hb01
  · rw [← hn, hnv]
  · intro h0'
    rw [← hc]; exact hz (by rw [hb]; exact h0')
  · rw [← hv, hvk]
  · rw [hst, hb, hn, hh, hc]

end Lvm6.Q
