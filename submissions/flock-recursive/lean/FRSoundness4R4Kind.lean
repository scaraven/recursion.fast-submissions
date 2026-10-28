-- New for `flock-recursive` (BLUEPRINT revision 4.1, B-11; stage R4c).
import FRSoundness4R4Outs
import FRXSeed
import FRSoundness4P4bNames

/-!
# The program's kind is the chain's (`kindOfC`)

On an accepted run of `gen4 seq4 p`, the seed checks `hdr`'s first 16 bytes against the kind's
constant `[p.byte, m, 0, …]` (`seedOps4`), so **π's byte 0 is `p.byte`** (`seed_byte4`); the chain's
first entry is the seed query `"FRSEED0" ‖ vk ‖ c ‖ hdr` (`SkRun4.hq`, `fsMsgs4_head`), whose byte 71
is π's byte 0; so **`kindOfC es` is the program's kind** (`kindOfC_seg4`, `kindOfC_node4`), and the
front's dimensions are the program's (`mC6_seg4`, …).
-/

namespace FR.Snd.R4
open RecursionFast Rev4

section Kind
variable {impl : OpImpl} {p : KindP} {inp : Input} {tr : Trace} {y : List Val × List Bool × Trace}

theorem byteAt_bytesOf_cons (b : UInt8) (l : List UInt8) : byteAt (bytesOf (b :: l)) 0 = b := by
  unfold byteAt bytesOf
  rw [dif_pos (by show 0 < (b :: l).toArray.size; simp)]
  rfl

/-- **The seed's check**: π's byte 0 is the kind's byte. -/
theorem seed_byte4 (h : SkRun4 impl p inp tr y) : byteAt inp.π 0 = p.byte := by
  obtain ⟨trk, M, x, hx, hb, -, -, hfl, -⟩ := phase_at4 impl p.tix inp p h.ref (k := 0) (by decide)
  have hM : M = [] := by
    have : (cAt4 seq4 p 0).next = 0 := rfl
    rw [this] at hb; exact List.eq_nil_of_length_eq_zero hb.symm
  subst hM
  have hph : (phasesOf seq4)[0] = ("seed", .seed) := rfl
  have hfx := h.flags _ hfl
  rw [hph] at hx
  simp only [refPhase4] at hx
  rcases trk with _ | ⟨⟨q, a⟩, trk⟩
  · cases hx
  · simp only at hx
    split_ifs at hx
    simp only [seedTail4, seedOps4, List.drop_succ_cons, List.drop_zero, pureRun, evalOp, absOff_zero,
      rd, Option.map_some] at hx
    rcases hx' : x with ⟨xv, xb, xt⟩
    rw [hx'] at hx hfx
    simp only [Option.some.injEq, Prod.mk.injEq] at hx
    obtain ⟨-, rfl, -⟩ := hx
    generalize hcst : bytesOf ([p.byte, p.d.m.toUInt8] ++ List.replicate 46 0) = cst at hfx
    have he : F.ofBytes (bytesAt inp.π 0 16) = F.ofBytes (bytesAt cst 0 16) := by
      revert hfx; simp [allK, Val.eqv]
    have hv := congrArg (fun v => v[0]) (Circ.ofBytes_inj he)
    simp only [bytesAt, Vector.getElem_ofFn, Nat.add_zero] at hv
    rw [hv, ← hcst, List.cons_append]
    exact byteAt_bytesOf_cons _ _

theorem kindOfC_byte4 (h : SkRun4 impl p inp tr y) (hp : p.byte ≠ 0) :
    (entAt (fsOf tr (itemsOf seq4)) 0).1.data[71]? = some p.byte := by
  have h0 := h.hq 0 (by decide)
  obtain ⟨ms, hms⟩ := fsMsgs4_head seq4
  rw [hms] at h0
  simp only [List.getD_cons_zero, qOf, ite_true] at h0
  have hb := seed_byte4 h
  rw [entAt, h0, ← Array.getElem?_toList, X.seedQ_data']
  rw [List.getElem?_append_right (by simp [tagSeed]), List.getElem?_append_right (by simp [tagSeed]),
    List.getElem?_append_right (by simp [tagSeed])]
  simp only [tagSeed, List.length_cons, List.length_nil, Vector.length_toList]
  rw [show 71 - 7 - 32 - 32 = 0 from rfl, toList_extract]
  simp only [List.drop_zero, Nat.sub_zero, Nat.zero_add]
  rw [List.getElem?_take_of_lt (by norm_num), Array.getElem?_toList]
  unfold byteAt at hb
  split_ifs at hb with hs
  · rw [Array.getElem?_eq_getElem hs]; exact congrArg some hb
  · exact absurd hb.symm hp

/-- **A segment program's chain is the segment kind's.** -/
theorem kindOfC_seg4 {σ : SegKind} (h : SkRun4 impl (.ofSeg σ) inp tr y) :
    kindOfC (fsOf tr (itemsOf seq4)) = .seg σ := by
  have hb := kindOfC_byte4 h (by cases σ <;> decide)
  unfold kindOfC
  rw [hb, Option.bind_some, show (KindP.ofSeg σ).byte = (CKind.seg σ).byte from rfl, CKind.ofByte?_byte]
  rfl

/-- **A node program's chain is the node kind's.** -/
theorem kindOfC_node4 {ν : NodeKind} (h : SkRun4 impl (.ofNode ν) inp tr y) :
    kindOfC (fsOf tr (itemsOf seq4)) = .node ν := by
  have hb := kindOfC_byte4 h (by cases ν <;> decide)
  unfold kindOfC
  rw [hb, Option.bind_some, show (KindP.ofNode ν).byte = (CKind.node ν).byte from rfl, CKind.ofByte?_byte]
  rfl

end Kind

/-! ## The front's dimensions are the program's -/

/-- Z3's real rounds `m − 6`, S2's `nb + 10`, the block bits `m − 14`, per kind. -/
theorem dims_seg4 (σ : SegKind) : (KindP.ofSeg σ).d.seq.z3 = (CKind.seg σ).m - 6 ∧
    (KindP.ofSeg σ).d.seq.s2 = (CKind.seg σ).m - 14 + 10 ∧ (KindP.ofSeg σ).d.m = (CKind.seg σ).m := by
  cases σ <;> decide

theorem dims_node4 (ν : NodeKind) : (KindP.ofNode ν).d.seq.z3 = (CKind.node ν).m - 6 ∧
    (KindP.ofNode ν).d.seq.s2 = (CKind.node ν).m - 14 + 10 ∧ (KindP.ofNode ν).d.m = (CKind.node ν).m ∧
    (KindP.ofNode ν).d.seq.lr = P4b.lrR ν ∧ (KindP.ofNode ν).d.seq.e2 = P4b.e2R ν ∧
    (KindP.ofNode ν).d.seq.e4 = P4b.ncR ν := by
  cases ν <;> decide

end FR.Snd.R4
