/- `LvmSubmissionSOff` (GOLF2 off-path move, group 20 of 48): declarations that the certificate `certified`
   does not use, moved here verbatim (same names, same namespaces and context) from LvmReplay, LvmXSpec, LvmSubmissionS,
   so that `Solution`'s import closure need not elaborate them. Import this module where they are needed;
   the name -> module map is GOLF2's moved.tsv. -/
import LvmReplay
import LvmXSpec
import LvmSubmissionS
import LvmXTopOff
import LvmChainTablePad
import LvmJBMutual
import LvmMlListLemmas
import LvmSpecRulesCert

-- ===== from `LvmReplay` =====

section
section
set_option autoImplicit false
namespace Lvm.Replay
open RecursionFast Lvm

theorem stepFS_iter_i (w : WS) : ∀ n, (WS.stepFS^[n] w).i = w.i + n
  | 0 => rfl
  | n + 1 => by rw [Function.iterate_succ_apply, stepFS_iter_i w.stepFS n]; simp [WS.stepFS, WS.settle]; omega

end Lvm.Replay
end
end

section
set_option autoImplicit false
namespace Lvm.Replay
open RecursionFast Lvm

/-- `drive_replayP` at a record with `accVars` header variables. -/
theorem drive_replay (p : Params) (_hA : p.accV = accVars) (hP : PlanOk p) (tr : Trace) (hL : LinkOk p tr)
    (F : ByteArray → Bool) :
    (drive p (reassemble p tr) F).runSeq tr = some (F (traceBytesB tr)) :=
  drive_replayP p hP tr hL F

/-- **Replay** (BLUEPRINT §4.6, generic over the schedule): on a trace of the schedule whose
reassembled proof passes `V_S`'s native header checks, `V_S` asks exactly the trace and returns its
decision `F vk c Σ` on the trace's stream. -/
theorem VS_replay (p : Params) (hA : p.accV = accVars) (m : M3) (vk c : Digest) (hP : PlanOk p) (tr : Trace) (hL : LinkOk p tr)
    (hparse : parseOk p vk c (reassemble p tr) = true) :
    (VS p m vk c (reassemble p tr)).runSeq tr = some (decideF p m vk c (traceBytesB tr)) := by
  simp only [VS, hparse, ite_true]
  exact drive_replay p hA hP tr hL _

end Lvm.Replay
end

section
set_option autoImplicit false
namespace Lvm.Replay
open RecursionFast Lvm

/-- `P8` with its WHIR levels written out. -/
def P8L : Params := { P8 with
  mainLevels := [⟨0, 6, 17, 1, 18, 4, 14, 33, 416⟩, ⟨1, 4, 13, 2, 15, 4, 11, 17, 384⟩,
    ⟨2, 4, 9, 3, 12, 4, 8, 11, 384⟩]
  recLevels := [] }

end Lvm.Replay
end

section
set_option autoImplicit false
namespace Lvm.Replay
open RecursionFast Lvm

theorem P8_eq : P8 = P8L := by
  have h1 : P8.mainLevels = P8L.mainLevels := by decide +kernel
  have h2 : P8.recLevels = P8L.recLevels := by decide +kernel
  show P8 = { P8 with mainLevels := P8L.mainLevels, recLevels := P8L.recLevels }
  rw [← h1, ← h2]

end Lvm.Replay
end

section
set_option autoImplicit false
namespace Lvm.Replay
open RecursionFast Lvm

set_option maxRecDepth 200000 in
theorem planOk_P8 : PlanOk P8 := by rw [P8_eq]; decide +kernel

/-- The plan has `qS` entries (5,464 at `P20`; WP-0's frozen count). -/
theorem plan_P20 : (plan P20).length = 3895 := by
  have h := planItems_i P20 w0 (schedule P20)
  have h2 : (planItems P20 w0 (schedule P20)).2.i = 3895 := planSt_P20.2
  have hw : w0.i = 2 := rfl
  rw [plan_length, planAll]
  omega

set_option maxRecDepth 200000 in
theorem plan_P8 : (plan P8).length = 1836 := by rw [P8_eq]; decide +kernel

theorem VS20_replay (tabs : Pub → List M3.Tab) (vk c : Digest) (tr : Trace) (hL : LinkOk P20 tr)
    (hparse : parseOk P20 vk c (reassemble P20 tr) = true) :
    (VSL P20 tabs vk c (reassemble P20 tr)).runSeq tr = some (decideF P20 (M3.real P20 tabs) vk c (traceBytesB tr)) :=
  VS_replay P20 rfl (M3.real P20 tabs) vk c planOk_P20 tr hL hparse

theorem VS8_replay (tabs : Pub → List M3.Tab) (vk c : Digest) (tr : Trace) (hL : LinkOk P8 tr)
    (hparse : parseOk P8 vk c (reassemble P8 tr) = true) :
    (VSL P8 tabs vk c (reassemble P8 tr)).runSeq tr = some (decideF P8 (M3.real P8 tabs) vk c (traceBytesB tr)) :=
  VS_replay P8 rfl (M3.real P8 tabs) vk c planOk_P8 tr hL hparse

end Lvm.Replay
end

-- ===== from `LvmXSpec` =====

section
namespace Lvm.X
open RecursionFast Lvm

/-- `f₂`'s coefficient `v` from π (`E` scalars of 3 words at π word `f2Off / 8`; lvm2 S4: `C_rec`'s
final after its level 1). -/
def f2E (π : Proof) (v : ℕ) : BF64.Ext3 :=
  mkE (wK (pw π (f2Off pX / 8 + 3 * v))) (wK (pw π (f2Off pX / 8 + 3 * v + 1)))
    (wK (pw π (f2Off pX / 8 + 3 * v + 2)))

/-- `C_rec`'s (level 0's) cap from π: 128 digests at π word `capRecOff / 8`. -/
def capRec (π : Proof) : List Digest :=
  (List.range 128).map fun e => hdD π (capRecOff pX / 8 + 4 * e)

/-- `C_rec`'s level-1 cap from π: 128 digests at π word `capRec1Off / 8`. -/
def capRec1 (π : Proof) : List Digest :=
  (List.range 128).map fun e => hdD π (capRec1Off pX / 8 + 4 * e)

/-- The decoded message's words. -/
def wOut (out : List BF64) (i : ℕ) : Word := BF64.toBitVec (out.getD i 0)

end Lvm.X
end

section
namespace Lvm.X
open RecursionFast Lvm

/-- **The SNARK branch's run**: on an `S` proof of `piSize` bytes the program's denotation is the
SNARK branch's output from the parse's state. -/
theorem den_S (c : Digest) (π : Proof) (L : Log) (hs : π.size = piSize pX)
    (h0 : π.data[0]? = some 0x53) :
    ∃ s1 : St, Inv s1.M ∧ s1.M.size = memX + mpwX * (extractorInput c π L).length ∧ s1.o = #[] ∧
      den memX mpwX (extIRWith (piSize pX) decX) (extractorInput c π L) =
        (semXIR (extractorInput c π L).toArray decX s1).o.toList := by
  set I := (extractorInput c π L).toArray with hI
  have hreg : regs ≤ memX := by simp only [regs, memX]; norm_num
  have h0' : Inv (initSt (memX + mpwX * (extractorInput c π L).length)).M :=
    inv_initSt (Nat.le_add_right_of_le hreg)
  refine ⟨semXIR I (parseIR (piSize pX)) (initSt (memX + mpwX * (extractorInput c π L).length)),
    inv_sem I (wf_extIRWith (pz := piSize pX) wf_decX).1 h0', by rw [size_sem, initSt_M, size_runPrims,
      Array.size_replicate], by rw [parse_o, initSt_o], ?_⟩
  have hk : rd (semXIR I (parseIR (piSize pX)) (initSt (memX + mpwX * (extractorInput c π L).length))).M
      rIsK ≠ 0 := by
    rw [parse_isK _ I _ h0']
    have hb := tape_byte0 c π L h0
    have e : I.getD 5 0 &&& 0xFF = kindS := by
      apply BitVec.eq_of_toNat_eq
      rw [lowByte, hI, getD_toArray, hb]; rfl
    rw [if_pos e]; decide
  have hz : rd (semXIR I (parseIR (piSize pX)) (initSt (memX + mpwX * (extractorInput c π L).length))).M
      rIsSz ≠ 0 := by
    rw [parse_regs _ I _ h0', hI, getD_toArray, tape_getD4, hs]
    rw [if_pos (by rfl)]; decide
  rw [den, extIRWith, semXIR_seq, semXIR_ite, if_neg hk, semXIR_ite, if_neg hz]

theorem pw_lt (π : Proof) (j : ℕ) : (pw π j).toNat < 2 ^ 64 := (pw π j).isLt

end Lvm.X
end

section
namespace Lvm.X
open RecursionFast Lvm

/-- **`EX` on an `S` proof with `b = 0`**, on every log: the leaf witness of its header. -/
theorem EX_leaf (A : Digest → Digest → Signed → Bool) (c : Digest) (π : Proof) (L : Log)
    (hs : π.size = piSize pX) (h0 : π.data[0]? = some 0x53) (hb : pw π 1 = 0) :
    EX A c π L = some (leafW π) := by
  by_cases hD : InDomE c π L
  · rw [EX, if_pos hD, EdX, Eden]
    obtain ⟨s1, hM1, -, ho1, hden⟩ := den_S c π L hs h0
    rw [hden]
    set I := (extractorInput c π L).toArray with hI
    obtain ⟨b1, -, hM2, -, bo⟩ := readAt_val I s1 hM1 (d := rBb) (pos := 6) (by decide) (by decide)
      (by decide) (by norm_num)
    rw [decX, semXIR_seq]
    generalize semXIR I (readAt rBb 6) s1 = s2 at b1 hM2 bo
    have h6 : I.getD 6 0 = 0 := by rw [show (6 : ℕ) = 5 + 1 from rfl, tape_pw c π L hs (by norm_num), hb]
    rw [semXIR_ite, if_pos (by rw [b1, h6]), leafIR, semXIR_seq]
    obtain ⟨e1, -⟩ := emitIR_sem I s2 hM2 (toWord 0)
    have hM3 := inv_sem I (wf_emitIR (toWord 0)) hM2
    generalize semXIR I (emitIR (toWord 0)) s2 = s3 at e1 hM3
    obtain ⟨t1, -⟩ := tcpIR_sem I s3 hM3 (a := 15) (n := 5) (by norm_num)
    rw [t1, e1, bo, ho1]
    have t2 := wsAt_tape c π L hs (a := 10) (n := 5) (by norm_num)
    simp only [show (5 + 10 : ℕ) = 15 from rfl] at t2
    rw [t2]
    have hw : witWords (leafW π) = toWord 0 :: wsAt (pw π) 10 5 := by
      simp only [leafW, witWords, hdD, packBytes_digW (length_wsAt _ _ _), toWord_toNat',
        show (5 : ℕ) = 4 + 1 from rfl, wsAt_add]
      simp [wsAt]
    rw [Array.toList_empty, List.nil_append, List.singleton_append, ← hw]
    exact decodeWit_witWords _ (pw π 14).isLt
  · rw [EX, if_neg hD, EoutX, if_pos h0, if_pos hs, if_pos hb]

/-- **`EX` on an `S` node proof outside the domain**: the search under the key the proof carries. -/
theorem EX_node_out (A : Digest → Digest → Signed → Bool) (c : Digest) (π : Proof) (L : Log)
    (hD : ¬ InDomE c π L) (hs : π.size = piSize pX) (h0 : π.data[0]? = some 0x53) (hb : pw π 1 ≠ 0) :
    EX A c π L = search A (hdD π 2) c := by
  rw [EX, if_neg hD, EoutX, if_pos h0, if_pos hs, if_neg hb]

end Lvm.X
end

section
namespace Lvm.X
open RecursionFast Lvm

theorem hasOut_chainL : hasOut chainL = false := by
  simp only [chainL, chainIR, hasOut_seq, hasOut_storesIR, cntIR, cntBody, readAt, sdL, startPs, wordIR,
    lenIR, qryIR, ansIR, ansPs, setSPs, lastIR, recIR, recPre, st4IR, stNext, nextIR, nextPre]
  simp only [hasOut, Bool.or_false]

theorem hasOut_idx : hasOut (idxIR4 memX pLX) = false := by
  simp [idxIR4, walkIR4, walkPre4, walkBody, sortIR4, sortPre4, passIR4, passPre4, stepIR, blockIR,
    cmpIR, cmpWord, aposIR, readAt, hasOut]

theorem wf_chainL : WF chainL :=
  wf_chainIR (posL (piSize pX)) (nChain pX) chTabL wf_sdL (nw_sdL _ (by decide) (by decide) (by decide))

end Lvm.X
end

section
namespace Lvm.X
open RecursionFast Lvm

theorem alphaPos_eq (j : ℕ) : alphaPos pX j = 1244 + j := by
  rw [alphaPos, layout_P20.1]

end Lvm.X
end

section
namespace Lvm.X
open RecursionFast Lvm

/-- **The `α` copies**: `α_j`'s answer words 0–2 at `aB + 3j`. -/
theorem acpIR_sem (I : Array Word) (s : St) (hM : Inv s.M) (hsz : 2 ^ 25 ≤ s.M.size) :
    (∀ j < 6, ∀ m < 3, rd (semXIR I acpIR s).M (aBX + 3 * j + m) = rd s.M (ansB + 4 * alphaPos pX j + m)) ∧
    (∀ r, regs ≤ r → (r < aBX ∨ aBX + 18 ≤ r) → rd (semXIR I acpIR s).M r = rd s.M r) ∧
    Inv (semXIR I acpIR s).M ∧ (semXIR I acpIR s).M.size = s.M.size ∧ (semXIR I acpIR s).o = s.o := by
  have hA : ∀ j, ansB + 4 * alphaPos pX j = 16793600 + 4 * (1244 + j) := fun j => by
    rw [alphaPos_eq, ansB_eq]
  simp only [acpIR, hA]
  simp only [aBX]
  obtain ⟨p1, q1, i1, z1, o1⟩ := mcp3 I s hM hsz (src := 16793600 + 4 * (1244 + 0)) (dst := 2 ^ 19)
    (by simp only [regs]; norm_num) (by norm_num) (by norm_num) (by norm_num)
  rw [semXIR_seq]
  generalize semXIR I (mcpIR 3 (16793600 + 4 * (1244 + 0)) 1 (2 ^ 19)) s = s1 at p1 q1 i1 z1 o1
  obtain ⟨p2, q2, i2, z2, o2⟩ := mcp3 I s1 i1 (by (clear * - hsz z1; omega)) (src := 16793600 + 4 * (1244 + 1))
    (dst := 2 ^ 19 + 3) (by simp only [regs]; norm_num) (by norm_num) (by norm_num) (by norm_num)
  rw [semXIR_seq]
  generalize semXIR I (mcpIR 3 (16793600 + 4 * (1244 + 1)) 1 (2 ^ 19 + 3)) s1 = s2 at p2 q2 i2 z2 o2
  obtain ⟨p3, q3, i3, z3, o3⟩ := mcp3 I s2 i2 (by (clear * - hsz z1 z2; omega)) (src := 16793600 + 4 * (1244 + 2))
    (dst := 2 ^ 19 + 6) (by simp only [regs]; norm_num) (by norm_num) (by norm_num) (by norm_num)
  rw [semXIR_seq]
  generalize semXIR I (mcpIR 3 (16793600 + 4 * (1244 + 2)) 1 (2 ^ 19 + 6)) s2 = s3 at p3 q3 i3 z3 o3
  obtain ⟨p4, q4, i4, z4, o4⟩ := mcp3 I s3 i3 (by (clear * - hsz z1 z2 z3; omega)) (src := 16793600 + 4 * (1244 + 3))
    (dst := 2 ^ 19 + 9) (by simp only [regs]; norm_num) (by norm_num) (by norm_num) (by norm_num)
  rw [semXIR_seq]
  generalize semXIR I (mcpIR 3 (16793600 + 4 * (1244 + 3)) 1 (2 ^ 19 + 9)) s3 = s4 at p4 q4 i4 z4 o4
  obtain ⟨p5, q5, i5, z5, o5⟩ := mcp3 I s4 i4 (by (clear * - hsz z1 z2 z3 z4; omega)) (src := 16793600 + 4 * (1244 + 4))
    (dst := 2 ^ 19 + 12) (by simp only [regs]; norm_num) (by norm_num) (by norm_num) (by norm_num)
  rw [semXIR_seq]
  generalize semXIR I (mcpIR 3 (16793600 + 4 * (1244 + 4)) 1 (2 ^ 19 + 12)) s4 = s5 at p5 q5 i5 z5 o5
  obtain ⟨p6, q6, i6, z6, o6⟩ := mcp3 I s5 i5 (by (clear * - hsz z1 z2 z3 z4 z5; omega)) (src := 16793600 + 4 * (1244 + 5))
    (dst := 2 ^ 19 + 15) (by simp only [regs]; norm_num) (by norm_num) (by norm_num) (by norm_num)
  generalize semXIR I (mcpIR 3 (16793600 + 4 * (1244 + 5)) 1 (2 ^ 19 + 15)) s5 = s6 at p6 q6 i6 z6 o6
  have hR : ∀ r, regs ≤ r → (r < 2 ^ 19 ∨ 2 ^ 19 + 18 ≤ r) → rd s6.M r = rd s.M r := fun r hr h => by
    rw [q6 r hr (by (clear * - h; omega)), q5 r hr (by (clear * - h; omega)), q4 r hr (by (clear * - h; omega)), q3 r hr (by (clear * - h; omega)), q2 r hr (by (clear * - h; omega)),
      q1 r hr (by (clear * - h; omega))]
  have hsrc : ∀ j < 6, ∀ m < 3, regs ≤ 16793600 + 4 * (1244 + j) + m ∧
      (16793600 + 4 * (1244 + j) + m < 2 ^ 19 ∨ 2 ^ 19 + 18 ≤ 16793600 + 4 * (1244 + j) + m) :=
    fun j _ m _ => ⟨by simp only [regs]; (clear hA hM hR hsz i1 i2 i3 i4 i5 i6 o1 o2 o3 o4 o5 o6 p1 p2 p3 p4 p5 p6 q1 q2 q3 q4 q5 q6 z1 z2 z3 z4 z5 z6; omega), .inr (by (clear hA hM hR hsz i1 i2 i3 i4 i5 i6 o1 o2 o3 o4 o5 o6 p1 p2 p3 p4 p5 p6 q1 q2 q3 q4 q5 q6 z1 z2 z3 z4 z5 z6; omega))⟩
  refine ⟨fun j hj m hm => ?_, hR, i6, by rw [z6, z5, z4, z3, z2, z1], by rw [o6, o5, o4, o3, o2, o1]⟩
  have hr : regs ≤ 2 ^ 19 + 3 * j + m := by simp only [regs]; (clear * - hj hm; omega)
  interval_cases j
  · rw [q6 _ hr (by (clear * - hm; omega)), q5 _ hr (by (clear * - hm; omega)), q4 _ hr (by (clear * - hm; omega)), q3 _ hr (by (clear * - hm; omega)),
      q2 _ hr (by (clear * - hm; omega)), show 2 ^ 19 + 3 * 0 + m = 2 ^ 19 + m by (clear * -; omega), p1 m hm]
  · rw [q6 _ hr (by (clear * - hm; omega)), q5 _ hr (by (clear * - hm; omega)), q4 _ hr (by (clear * - hm; omega)), q3 _ hr (by (clear * - hm; omega)),
      show 2 ^ 19 + 3 * 1 + m = 2 ^ 19 + 3 + m by (clear * -; omega), p2 m hm, q1 _ (hsrc 1 (by norm_num) m hm).1
        (by (clear * - hm; omega))]
  · rw [q6 _ hr (by (clear * - hm; omega)), q5 _ hr (by (clear * - hm; omega)), q4 _ hr (by (clear * - hm; omega)),
      show 2 ^ 19 + 3 * 2 + m = 2 ^ 19 + 6 + m by (clear * -; omega), p3 m hm,
      q2 _ (hsrc 2 (by norm_num) m hm).1 (by (clear * - hm; omega)), q1 _ (hsrc 2 (by norm_num) m hm).1 (by (clear * - hm; omega))]
  · rw [q6 _ hr (by (clear * - hm; omega)), q5 _ hr (by (clear * - hm; omega)), show 2 ^ 19 + 3 * 3 + m = 2 ^ 19 + 9 + m by (clear * -; omega),
      p4 m hm, q3 _ (hsrc 3 (by norm_num) m hm).1 (by (clear * - hm; omega)), q2 _ (hsrc 3 (by norm_num) m hm).1 (by (clear * - hm; omega)),
      q1 _ (hsrc 3 (by norm_num) m hm).1 (by (clear * - hm; omega))]
  · rw [q6 _ hr (by (clear * - hm; omega)), show 2 ^ 19 + 3 * 4 + m = 2 ^ 19 + 12 + m by (clear * -; omega), p5 m hm,
      q4 _ (hsrc 4 (by norm_num) m hm).1 (by (clear * - hm; omega)), q3 _ (hsrc 4 (by norm_num) m hm).1 (by (clear * - hm; omega)),
      q2 _ (hsrc 4 (by norm_num) m hm).1 (by (clear * - hm; omega)), q1 _ (hsrc 4 (by norm_num) m hm).1 (by (clear * - hm; omega))]
  · rw [show 2 ^ 19 + 3 * 5 + m = 2 ^ 19 + 15 + m by (clear * -; omega), p6 m hm,
      q5 _ (hsrc 5 (by norm_num) m hm).1 (by (clear * - hm; omega)), q4 _ (hsrc 5 (by norm_num) m hm).1 (by (clear * - hm; omega)),
      q3 _ (hsrc 5 (by norm_num) m hm).1 (by (clear * - hm; omega)), q2 _ (hsrc 5 (by norm_num) m hm).1 (by (clear * - hm; omega)),
      q1 _ (hsrc 5 (by norm_num) m hm).1 (by (clear * - hm; omega))]

/-- **After the decoder**: with the flag set and the message `w` at `mB`, the node output. -/
theorem okXIR_sem (c : Digest) (π : Proof) (L : Log) (hs : π.size = piSize pX) (s8 : St)
    (hM8 : Inv s8.M) (hsz : sgB + nCp ≤ s8.M.size) (hf : rd s8.M (okB dBX) = 1) (w : ℕ → Word)
    (hw : ∀ i < 2 ^ 19, rd s8.M (mB dBX + i) = w i) :
    (semXIR (extractorInput c π L).toArray okXIR s8).o.toList = s8.o.toList ++ outWords π w := by
  have hs8 := hM8.1
  simp only [regs] at hs8
  rw [okXIR, semXIR_seq]
  have e1 := blk_const_val (extractorInput c π L).toArray s8 hM8 (d := eA) (by decide) (toWord (okB dBX))
  have g1 : ∀ y, y ≠ eA → rd (semXIR (extractorInput c π L).toArray (.blk [.const eA (toWord (okB dBX))]) s8).M y =
      rd s8.M y := fun y hy => blk_const_ne _ s8 _ hy
  have hM9 := inv_sem (extractorInput c π L).toArray (P := .blk [.const eA (toWord (okB dBX))])
    (by simp +decide [WF, Prim.dst, eA]) hM8
  have z9 := size_sem (extractorInput c π L).toArray (.blk [.const eA (toWord (okB dBX))]) s8
  have o9 : (semXIR (extractorInput c π L).toArray (.blk [.const eA (toWord (okB dBX))]) s8).o = s8.o := rfl
  generalize semXIR (extractorInput c π L).toArray (.blk [.const eA (toWord (okB dBX))]) s8 = s9 at e1 g1 hM9 z9 o9
  have hok64 : okB dBX < 2 ^ 64 := by simp only [okB, dBX]; norm_num
  have hs9 := hM9.1
  simp only [regs] at hs9
  have eL : semXIR (extractorInput c π L).toArray (.load eW eA) s9 =
      ⟨s9.M.setIfInBounds eW (rd s9.M (rd s9.M eA).toNat), s9.o⟩ := rfl
  have l1 : rd (semXIR (extractorInput c π L).toArray (.load eW eA) s9).M eW = rd s9.M (okB dBX) := by
    rw [eL]; show rd (s9.M.setIfInBounds eW _) eW = _
    rw [rd_set_self (by simp only [eW]; (clear * - hs8 z9; omega)), e1, toNat_toWord hok64]
  have l2 : ∀ i, i ≠ eW → rd (semXIR (extractorInput c π L).toArray (.load eW eA) s9).M i = rd s9.M i :=
    fun i hi => by rw [eL]; exact rd_set_ne (Ne.symm hi)
  have hM10 := inv_sem (extractorInput c π L).toArray (P := .load eW eA) (show 4 ≤ eW by decide) hM9
  have z10 := size_sem (extractorInput c π L).toArray (.load eW eA) s9
  have o10 : (semXIR (extractorInput c π L).toArray (.load eW eA) s9).o = s9.o := rfl
  rw [semXIR_seq]
  generalize semXIR (extractorInput c π L).toArray (.load eW eA) s9 = s10 at l1 l2 hM10 z10 o10
  have hflag : rd s10.M eW ≠ 0 := by
    rw [l1, g1 _ (by simp only [okB, dBX, eA]; (clear * -; omega)), hf]; decide
  rw [semXIR_ite, if_neg hflag]
  have hw10 : ∀ i < 2 ^ 19, rd s10.M (mB dBX + i) = w i := fun i hi => by
    rw [l2 _ (by simp only [mB, dBX, eW]; (clear * - hi; omega)), g1 _ (by simp only [mB, dBX, eA]; (clear * - hi; omega)), hw i hi]
  have hsz10 : sgB + nCp ≤ s10.M.size := by rw [z10, z9]; exact hsz
  rw [outIR_sem c π L hs s10 hM10 (mB := mB dBX) (by simp only [regs, mB, dBX]; norm_num)
    (by simp only [mB, dBX, sgB]; norm_num) hsz10 w hw10, o10, o9]

end Lvm.X
end

section
namespace Lvm.X
open RecursionFast Lvm

theorem alpha1Pos_eq (j : ℕ) : alpha1Pos pX j = 1247 + j := by
  have h := layout_P20.2.2.2.2.2.2.2.1
  simp only [alpha1Pos] at h ⊢
  omega

/-- **After the level-1 decoder**: with its flag set, `C_rec`'s level-0 word, `α₀` and `f₁` in v1's
decoder layout, and the level-0 decoder returning `out`, the node output. -/
theorem ok1XIR_sem (c : Digest) (π : Proof) (L : Log) (hs : π.size = piSize pX) (s : St)
    (hM : Inv s.M) (hsz : 2 ^ 25 ≤ s.M.size) (hf : rd s.M (ok1B d1BX) = 1)
    (wd : ℕ → ℕ → BF64) (α f₁ : ℕ → BF64.Ext3)
    (hW : ∀ q < 2 ^ 15, ∀ t < 64, rdK s.M (wBX + 64 * q + t) = wd q t)
    (hA : ∀ i < 6, rdE s.M (aBX + 3 * i) = α i) (hF : ∀ v < 2 ^ 13, rdE s.M (fBX + 3 * v) = f₁ v)
    (out : List BF64) (hdec : decodeRec wd α f₁ = some out) :
    (semXIR (extractorInput c π L).toArray ok1XIR s).o.toList = s.o.toList ++ outWords π (wOut out) := by
  set I := (extractorInput c π L).toArray
  have hs0 := hM.1
  simp only [regs] at hs0
  rw [ok1XIR, semXIR_seq]
  have e1 := blk_const_val I s hM (d := eA) (by decide) (toWord (ok1B d1BX))
  have g1 : ∀ y, y ≠ eA → rd (semXIR I (.blk [.const eA (toWord (ok1B d1BX))]) s).M y = rd s.M y :=
    fun y hy => blk_const_ne _ s _ hy
  have hM9 := inv_sem I (P := .blk [.const eA (toWord (ok1B d1BX))]) (by simp +decide [WF, Prim.dst, eA]) hM
  have z9 := size_sem I (.blk [.const eA (toWord (ok1B d1BX))]) s
  have o9 : (semXIR I (.blk [.const eA (toWord (ok1B d1BX))]) s).o = s.o := rfl
  generalize semXIR I (.blk [.const eA (toWord (ok1B d1BX))]) s = s9 at e1 g1 hM9 z9 o9
  have hok64 : ok1B d1BX < 2 ^ 64 := by simp only [ok1B, d1BX]; norm_num
  have hs9 := hM9.1
  simp only [regs] at hs9
  have eL : semXIR I (.load eW eA) s9 = ⟨s9.M.setIfInBounds eW (rd s9.M (rd s9.M eA).toNat), s9.o⟩ := rfl
  have l1 : rd (semXIR I (.load eW eA) s9).M eW = rd s9.M (ok1B d1BX) := by
    rw [eL]; show rd (s9.M.setIfInBounds eW _) eW = _
    rw [rd_set_self (by simp only [eW]; (clear * - hsz z9; omega)), e1, toNat_toWord hok64]
  have l2 : ∀ i, i ≠ eW → rd (semXIR I (.load eW eA) s9).M i = rd s9.M i :=
    fun i hi => by rw [eL]; exact rd_set_ne (Ne.symm hi)
  have hM10 := inv_sem I (P := .load eW eA) (show 4 ≤ eW by decide) hM9
  have z10 := size_sem I (.load eW eA) s9
  have o10 : (semXIR I (.load eW eA) s9).o = s9.o := rfl
  rw [semXIR_seq]
  generalize semXIR I (.load eW eA) s9 = s10 at l1 l2 hM10 z10 o10
  have hflag : rd s10.M eW ≠ 0 := by
    rw [l1, g1 _ (by simp only [ok1B, d1BX, eA]; (clear * -; omega)), hf]; decide
  rw [semXIR_ite, if_neg hflag, semXIR_seq]
  have hfr : ∀ y, regs ≤ y → rd s10.M y = rd s.M y := fun y hy => by
    simp only [regs] at hy
    rw [l2 _ (by simp only [eW]; (clear * - hy; omega)), g1 _ (by simp only [eA]; (clear * - hy; omega))]
  have hsz10 : 2 ^ 25 ≤ s10.M.size := by rw [z10, z9]; exact hsz
  have hW' : ∀ q < 2 ^ 15, ∀ t < 64, rdK s10.M (wBX + 64 * q + t) = wd q t := fun q hq t ht => by
    simp only [rdK]; rw [hfr _ (by simp only [regs, wBX]; (clear * - hq ht; omega))]; exact hW q hq t ht
  have hA' : ∀ i < 6, rdE s10.M (aBX + 3 * i) = α i := fun i hi => by
    rw [← hA i hi, rdE_eq, rdE_eq, hfr _ (by simp only [regs, aBX]; (clear * - hi; omega)),
      hfr _ (by simp only [regs, aBX]; (clear * - hi; omega)), hfr _ (by simp only [regs, aBX]; (clear * - hi; omega))]
  have hF' : ∀ v < 2 ^ 13, rdE s10.M (fBX + 3 * v) = f₁ v := fun v hv => by
    rw [← hF v hv, rdE_eq, rdE_eq, hfr _ (by simp only [regs, fBX]; (clear * - hv; omega)),
      hfr _ (by simp only [regs, fBX]; (clear * - hv; omega)), hfr _ (by simp only [regs, fBX]; (clear * - hv; omega))]
  obtain ⟨d1, d2, d3, hM8⟩ := decIR_sem I s10 hM10
    (show DecLay dBX wBX aBX fBX s10.M.size from decLay_example _ hsz10) wd α f₁ hW' hA' hF'
  have z8 := size_sem I (decIR dBX wBX aBX fBX) s10
  have o8 := decIR_o I s10 dBX wBX aBX fBX
  have hok : 2 ^ 13 ≤ (agreeL wd α f₁).length := by
    by_contra hn
    rw [decodeRec, if_neg hn] at hdec
    cases hdec
  rw [decide_eq_true hok] at d1
  have hmsg := d2 out hdec
  generalize semXIR I (decIR dBX wBX aBX fBX) s10 = s8 at d1 hmsg d3 hM8 z8 o8
  have hsz8 : sgB + nCp ≤ s8.M.size := by
    rw [z8]; simp only [sgB, nCp]; (clear * - hsz z9 z10 z8; omega)
  have hw : ∀ i < 2 ^ 19, rd s8.M (mB dBX + i) = wOut out i := fun i hi => by
    rw [← rdK_toBitVec, hmsg i hi]; rfl
  rw [okXIR_sem c π L hs s8 hM8 hsz8 d1 (wOut out) hw, o8, o10, o9]

end Lvm.X
end

-- ===== from `LvmSubmissionS` =====

section
section
set_option autoImplicit false
namespace Lvm.ASM

/-- **`schemeS`'s cap levels are the schedule's** (review fact): for every level of both
commitments at P20, `capOfS` of its height is its cap exponent. -/
theorem capOfS_P20 :
    ((P20.levels .main).all fun L ↦ capOfS L.height 0 == L.cap) = true ∧
      ((P20.levels .crec).all fun L ↦ capOfS L.height 0 == L.cap) = true := by
  decide +kernel

/-- **`schemeS`'s leaves are the schedule's rows** (Z2): for every level of both commitments at P20
(rows of `2^ℓ` words at the root, `3·2^ℓ` later), the row the proof carries is `8 · occOfS` of its
shape's words, all of them but at the roots. -/
theorem occOfS_P20 :
    ((P20.levels .main).all fun L ↦ let w := if L.level = 0 then 2 ^ L.fold else 3 * 2 ^ L.fold
      L.row == 8 * min (occOfS L.height w) w && (L.level == 0 || occOfS L.height w == w)) = true ∧
      ((P20.levels .crec).all fun L ↦ let w := if L.level = 0 then 2 ^ L.fold else 3 * 2 ^ L.fold
        L.row == 8 * min (occOfS L.height w) w && (L.level == 0 || occOfS L.height w == w)) = true := by
  decide +kernel

end Lvm.ASM
end
end
