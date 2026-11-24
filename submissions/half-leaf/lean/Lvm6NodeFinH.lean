-- New for lvm6 (WP NODE5a). The root claims' values (tree claims 11–14): the child header's root lanes, at the
-- header `F6` replays, are the stream cells `hdrLaneC (3 + m)` (`RootLanes`), from `LinkOk6` and the stream cells.
import Lvm6NodeFinC
import Lvm6NodeTailHH

/-!
# The root lanes (WP NODE5a)

**`rootLanes_hdr`**: `RootLanes M (hdrOf6 πW).h` from `LinkOk6` and the stream cells (`QIn6.stream`), as N4-tail's
`tyIn_hdr` reads the header's words: lane `l < 103` of `HDR` is the cell `sbC + hdrW l` (`le8_hdr`); the root `h`
is `HDR`'s bytes 24–55 (`hdrView`), its lane `m` the word of bytes `24 + 8m …` (`byteOf_dLane`, `byteOf_le8`).
-/

set_option autoImplicit false

namespace Lvm6.Node.Hdr

open RecursionFast LeanVM.Parameters Lvm Lvm.Loop Lvm6.Q

/-- **The root lanes are the stream's header cells.** -/
theorem rootLanes_hdr {M : Mem} {ws : List Word} {c : Digest} (hL : LinkOk6 P6 c (decode6 P6 ws))
    (hs : ∀ j < 2 ^ Dep.lay6.m, M.k (Dep.lay6.sb + j) = QLink.laneK ws j) :
    Fin.RootLanes M (Lvm6.Node.hdrOf6 (reassemble6 P6 (decode6 P6 ws))).h := by
  set H := Lvm6.Q.hdrOf6 (decode6 P6 ws) with hH
  have hlen : H.length = 824 := hdrOf6_length hL
  have hx : Lvm6.Node.hdrOf6 (reassemble6 P6 (decode6 P6 ws)) = hdrView P17 H := by
    obtain ⟨rest, hr⟩ := bl_reassemble (decode6 P6 ws)
    show hdrView P17 ((Lvm.Replay.bl (reassemble6 P6 (decode6 P6 ws))).take (V.hdrLen (toV P17))) = _
    rw [hr, show V.hdrLen (toV P17) = H.length by rw [hlen]; rfl, List.take_left]
  have hcell : ∀ l, l < 103 → M.k (Dep.sbC + Dep.hdrW l) = QSig.w64 (le8 H (8 * l)).toUInt64 := by
    intro l hl
    have hk : 32 + 8 * l + 8 ≤ (P6.getD 1 default).len := by
      rw [P6_get1]
      simp only [seedLen, hdrLen, cdConsts_P17.1]
      omega
    have hj : Dep.hdrW l < 2 ^ Dep.lay6.m := by
      simp only [Dep.hdrW, Dep.lay6]
      omega
    rw [show Dep.sbC + Dep.hdrW l = Dep.lay6.sb + Dep.hdrW l from rfl, hs _ hj, laneK_w64, hdrW_eq,
      le8_hdr (P := P6) (ws := ws) (by rw [P6_get0]) P6_two hk]
  intro m hm
  rw [hx, Dep.hdrLaneC_eq]
  show K.ofLane (dLane (rdD H 24) m) = FK.toBF64 (M.k (Dep.sbC + Dep.hdrW (3 + m)))
  rw [hcell (3 + m) (by omega)]
  show K.ofLane (dLane (rdD H 24) m) = K.ofLane (K.lane (FK.toBF64 (QSig.w64 (le8 H (8 * (3 + m))).toUInt64)))
  rw [lane_toBF64]
  congr 1
  refine word_ext fun k hk ↦ ?_
  rw [byteOf_dLane _ _ hk, byteOf_le8 _ _ hk]
  have h32 : 8 * m + k < 32 := by omega
  simp only [rdD, Lvm.FS.dg, Vector.toArray_ofFn, Array.getD_eq_getD_getElem?, Array.getElem?_ofFn, h32,
    dite_true, Option.getD_some, getD_drop']
  congr 1
  omega

end Lvm6.Node.Hdr
