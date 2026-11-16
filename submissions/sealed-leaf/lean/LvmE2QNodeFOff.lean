/- `LvmE2QNodeFOff` (GOLF2 off-path move, group 31 of 48): declarations that the certificate `certified`
   does not use, moved here verbatim (same names, same namespaces and context) from LvmQLinkSound, LvmQLinkMain, LvmQTypedHarR, LvmQTypedHarS, LvmE2QHarFacts, LvmE2QTypedPhase, LvmE2QHarF, LvmE2QNodeF,
   so that `Solution`'s import closure need not elaborate them. Import this module where they are needed;
   the name -> module map is GOLF2's moved.tsv. -/
import LvmQLinkSound
import LvmQLinkMain
import LvmQTypedHarR
import LvmQTypedHarS
import LvmE2QHarFacts
import LvmE2QTypedPhase
import LvmE2QHarF
import LvmE2QNodeF
import LvmE2QHarFrontOff
import LvmE2QHarPosOff
import LvmE2QInstOff
import LvmE2QNodeChkGOff
import LvmE2VWidthsFOff
import LvmFinPosOff
import LvmM3MidCertOff
import LvmQAccSoundOff
import LvmQAsmArith2BusOff
import LvmQAsmArith2Off
import LvmQEqKeccakTapeOff
import LvmQTypedHarCOff
import LvmQTypedHarZOff
import LvmSubmissionSOff
import LvmVerifierSTOff
import LvmChainTablePad
import LvmJBMutual
import LvmMlListLemmas
import LvmQAsmHar47
import LvmQAsmHarP47
import LvmQShapeC
import LvmQShapeH
import LvmQTypedHarZ
import LvmSpecRulesCert
import LvmTensorSwitch
import LvmVEqTape
import LvmVerifierF
import LvmVerifierST

-- ===== from `LvmQLinkSound` =====

section
section
set_option autoImplicit false
namespace Lvm.Loop.Build
open Lvm.Loop

/-- Run `f s a` for every chunk `(s, a)`. -/
def splitRun (cs : List (Nat × Nat)) (f : Nat → Nat → BM Unit) : BM Unit := do
  let _ ← seqAll (cs.map fun c => f c.1 c.2)
  pure ()

theorem seqAll_hold {c : Ctx} {M : Mem} {α : Type} :
    ∀ (ms : List (BM α)) (p : Ptr), SegsHold c M p (seqAll ms p).2 →
      ∀ m ∈ ms, ∃ q, SegsHold c M q (m q).2
  | [], _, _, _, h => by simp at h
  | m :: ms, p, h, m', hm => by
    simp only [seqAll] at h
    rw [hold_bind] at h
    rcases List.mem_cons.mp hm with rfl | hm
    · exact ⟨p, h.1⟩
    · rw [hold_bind] at h
      exact seqAll_hold ms _ h.2.1 m' hm

/-- An equality check `A = k·B + k'` on affine `K` operands. -/
structure Chk where
  /-- The checked operand. -/
  A : Addr
  /-- The other operand. -/
  B : Addr
  /-- The factor. -/
  k : FK
  /-- The constant. -/
  k' : FK

/-- The rows of checks `c₀, c₀ + 1, …`: per check a `lin` and an `assert0` of it. -/
def chkRows (gate : Cell) : Nat → List Chk → List LRow
  | _, [] => []
  | c, ch :: rest => ⟨.lin ch.k ch.k', .K, [.abs ch.A, .abs ch.B]⟩ ::
      ⟨.assert0, .K, [.cur (2 * c), gate.opd]⟩ :: chkRows gate (c + 1) rest

/-- **A check loop**: the checks at every loop index of `dims`. -/
def checkLoop (dims : List Nat) (gate : Cell) (chks : List Chk) : BM Unit := do
  let _ ← loop dims (chkRows gate 0 chks)
  pure ()

theorem chkRows_getD (gate : Cell) : ∀ (chks : List Chk) (c₀ i : Nat), i < chks.length →
    (chkRows gate c₀ chks).getD (2 * i) default =
        ⟨.lin (chks.getD i ⟨default, default, 0, 0⟩).k (chks.getD i ⟨default, default, 0, 0⟩).k', .K,
          [.abs (chks.getD i ⟨default, default, 0, 0⟩).A, .abs (chks.getD i ⟨default, default, 0, 0⟩).B]⟩ ∧
      (chkRows gate c₀ chks).getD (2 * i + 1) default = ⟨.assert0, .K, [.cur (2 * (c₀ + i)), gate.opd]⟩
  | [], _, _, h => absurd h (by simp)
  | ch :: rest, c₀, 0, _ => by simp [chkRows]
  | ch :: rest, c₀, i + 1, h => by
    have ih := chkRows_getD gate rest (c₀ + 1) i (by simpa using h)
    rw [show 2 * (i + 1) = 2 * i + 1 + 1 by ring, show 2 * i + 1 + 1 + 1 = 2 * i + 1 + 1 + 1 from rfl,
      show 2 * (c₀ + (i + 1)) = 2 * (c₀ + 1 + i) by ring]
    simp only [chkRows, List.getD_cons_succ]
    exact ih

theorem chkRows_length (gate : Cell) : ∀ (chks : List Chk) (c₀ : Nat), (chkRows gate c₀ chks).length = 2 * chks.length
  | [], _ => rfl
  | _ :: rest, c₀ => by simp [chkRows, chkRows_length gate rest]; ring

/-- **A check loop's checks hold** at every loop index when the gate is `1`. -/
theorem checkLoop_spec {c : Ctx} {M : Mem} {p : Ptr} {dims : List Nat} {gate : Cell} {chks : List Chk}
    (h : SegsHold c M p (checkLoop dims gate chks p).2) (hA : SegsAssert M p (checkLoop dims gate chks p).2)
    (hK : ∀ ch ∈ chks, ch.A.ty = .K ∧ ch.B.ty = .K) (hg : gate.ty = .K) (hg1 : M.k gate.n = 1) :
    ∀ jf < 2 ^ dims.sum, ∀ ch ∈ chks,
      M.k (ch.A.at (unflat dims jf)) = ch.k * M.k (ch.B.at (unflat dims jf)) + ch.k' := by
  intro jf hjf ch hch
  obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hch
  simp only [checkLoop, hold_bind, assert_bind] at h hA
  have hr := chkRows_getD gate chks 0 i hi
  have hgd : chks.getD i ⟨default, default, 0, 0⟩ = chks[i] := by
    simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi]
  rw [hgd] at hr
  have hl := lrel_lin hr.1 (loop_rel h.1 hjf (by rw [chkRows_length]; (clear * - hi; omega)))
  have ha := lassert_of hr.2 (loop_assert hA.1 hjf (by rw [chkRows_length]; (clear * - hi; omega)))
  simp only [List.getD_cons_zero, List.getD_cons_succ, Nat.zero_add] at hl ha
  rw [Cell.val_opd, Opd.val_cur _ _ hjf, hl] at ha
  obtain ⟨hAK, hBK⟩ := hK _ hch
  obtain ⟨gn, rfl⟩ : ∃ n, gate = kc n := ⟨gate.n, by cases gate; simp_all [kc]⟩
  generalize chks[i] = ch at *
  obtain ⟨⟨τA, bA, sA⟩, ⟨τB, bB, sB⟩, k, k'⟩ := ch
  simp only at hAK hBK
  subst hAK hBK
  simp only [Opd.val_absK, Cell.val_K, hg1, ofK_one, one_mul, loop_apply] at ha
  rw [← ofK_mul, ← ofK_add, ← ofK_add, ← ofK_zero] at ha
  have := ofK_inj ha
  simp only [Addr.at]
  have e := congrArg (· + (k * M.k (bB + dot sB (unflat dims jf)) + k')) this
  simp only [zero_add] at e
  rw [← e]
  generalize M.k (bA + dot sA (unflat dims jf)) = A
  generalize k * M.k (bB + dot sB (unflat dims jf)) = X
  have : A + X + k' + (X + k') = A + ((X + X) + (k' + k')) := by ring
  rw [this, FK.add_self, FK.add_self, add_zero, add_zero]

end Lvm.Loop.Build
end
end

section
set_option autoImplicit false
namespace Lvm.QLink
open RecursionFast Lvm Lvm.Replay Lvm.Loop Lvm.Loop.Build

theorem kOf_inj {v w : Nat} (hv : v < 2 ^ 64) (hw : w < 2 ^ 64) (h : kOf v = kOf w) : v = w := by
  rw [← kOf_toNat hv, ← kOf_toNat hw, h]

end Lvm.QLink
end

section
set_option autoImplicit false
namespace Lvm.QLink
open RecursionFast Lvm Lvm.Replay Lvm.Loop Lvm.Loop.Build

/-- `b·2^d + a = b·2^d ⊕ a` for `a < 2^d` (as `LvmXEnc.mul_two_pow_add_eq_xor`). -/
theorem mul_two_pow_add_xor {b d a : Nat} (ha : a < 2 ^ d) : b * 2 ^ d + a = b * 2 ^ d ^^^ a := by
  apply Nat.eq_of_testBit_eq
  intro i
  rw [Nat.mul_comm, Nat.testBit_two_pow_mul_add _ ha, Nat.testBit_xor, Nat.testBit_two_pow_mul]
  by_cases h : i < d
  · simp [h, show ¬ (d ≤ i) by (clear * - h; omega)]
  · rw [if_neg h, Nat.testBit_lt_two_pow (ha.trans_le (Nat.pow_le_pow_right (by norm_num) (by (clear * - h; omega))))]
    simp [show d ≤ i by (clear * - h; omega)]

/-- **Two disjoint fields add to the position** (`K` addition is `xor`). -/
theorem kOf_add_fields {a b d : Nat} (ha : a < 2 ^ d) (h64 : b * 2 ^ d + a < 2 ^ 64) :
    kOf a + kOf (b * 2 ^ d) = kOf (b * 2 ^ d + a) := by
  have hb : b * 2 ^ d < 2 ^ 64 := by (clear * - h64; omega)
  have ha' : a < 2 ^ 64 := by (clear * - h64 hb; omega)
  show FK.add _ _ = _
  simp only [FK.add, kOf]
  congr 1
  apply UInt64.toNat_inj.mp
  rw [UInt64.toNat_xor, Nat.toUInt64_eq, Nat.toUInt64_eq, Nat.toUInt64_eq, UInt64.toNat_ofNat',
    UInt64.toNat_ofNat', UInt64.toNat_ofNat', Nat.mod_eq_of_lt (by simpa using ha'),
    Nat.mod_eq_of_lt (by simpa using hb), Nat.mod_eq_of_lt (by simpa using h64), mul_two_pow_add_xor ha,
    Nat.xor_comm]

end Lvm.QLink
end

-- ===== from `LvmQLinkMain` =====

section
set_option autoImplicit false
namespace Lvm.QLink
open RecursionFast Lvm Lvm.Replay Lvm.Loop Lvm.Loop.Build
section
variable {p : Params} {lay : Layout} {ws : List Word} {c : Ctx} {M : Mem}

/-- **Replay** (BLUEPRINT §4.6), from Q_link's rows and assertions: `V_S` on the proof that the
stream's trace reassembles asks exactly that trace and answers `F` on `Σ`; `Σ`'s padding is pinned. -/
theorem qlink_replay (hAv : p.accV = accVars) (m : M3) (vk cd : Digest) (hP : PlanOk p) (hS : StreamOk p) (hQ : QOk p lay)
    (hin : QIn p lay ws M) (hws : 2 ^ lay.m ≤ ws.length)
    {N : Nat} (hinj : GInj N) (hN : c.cells .K ≤ N) (hNs : lay.sb + 2 ^ lay.m ≤ N) {pt : Ptr}
    (h : SegsHold c M pt (qlink p lay pt).2) (hA : SegsAssert M pt (qlink p lay pt).2)
    (hparse : parseOk p vk cd (reassemble p (decode p ws)) = true) :
    (VS p m vk cd (reassemble p (decode p ws))).runSeq (decode p ws) = some (decideF p m vk cd (sigma p ws)) ∧
      LinkOk p (decode p ws) ∧ PadOkB (wordsBytes ws) (hashedLen p) := by
  obtain ⟨hL, hpad⟩ := qlink_sound hS hQ hin hws hinj hN hNs h hA
  refine ⟨?_, linkOk_of_laneLink hS hL, hpad⟩
  rw [VS_replay p hAv m vk cd hP _ (linkOk_of_laneLink hS hL) hparse, traceBytesB_decode hS hL]

/-- **Replay from the interpreter** (BLUEPRINT §4.6's `interp Q_link Σ = true → …`): Q_link alone as a
LoopIR program on `nK` input cells. -/
theorem qlink_interp_replay (hAv : p.accV = accVars) (m : M3) (vk cd : Digest) (hP : PlanOk p) (hS : StreamOk p) (hQ : QOk p lay)
    (nK : Nat) (hseg : segsOk ⟨nK, 0⟩ (qlink p lay ⟨nK, 0⟩).2 = true) (inK : Array FK) (hsz : inK.size = nK)
    (hinj : GInj (max ((toProgram nK 0 (qlink p lay)).cells .K) ((toProgram nK 0 (qlink p lay)).cells .E)))
    (hNs : lay.sb + 2 ^ lay.m ≤ (toProgram nK 0 (qlink p lay)).cells .K)
    (hinb : ((toProgram nK 0 (qlink p lay)).interp inK #[]).inb = true)
    (hok : ((toProgram nK 0 (qlink p lay)).interp inK #[]).ok = true)
    (hin : QIn p lay ws ((toProgram nK 0 (qlink p lay)).interpMem inK #[])) (hws : 2 ^ lay.m ≤ ws.length)
    (hparse : parseOk p vk cd (reassemble p (decode p ws)) = true) :
    (VS p m vk cd (reassemble p (decode p ws))).runSeq (decode p ws) = some (decideF p m vk cd (sigma p ws)) ∧
      LinkOk p (decode p ws) ∧ PadOkB (wordsBytes ws) (hashedLen p) := by
  obtain ⟨hH, hOk, -⟩ := toProgram_interp nK 0 (qlink p lay) (toProgram_wf _ _ _ hseg) inK #[] ⟨hsz, rfl⟩
    hinj hinb
  have hc := ctxOf_cells (toProgram nK 0 (qlink p lay))
  exact qlink_replay hAv m vk cd hP hS hQ hin hws hinj (by rw [hc]; exact le_max_left _ _)
    (le_trans hNs (le_max_left _ _)) hH (hOk.mp hok) hparse

end
end Lvm.QLink
end

section
set_option autoImplicit false
namespace Lvm.QLink
open RecursionFast Lvm Lvm.Replay Lvm.Loop Lvm.Loop.Build

theorem u64_byte (x : UInt64) (b : Nat) (hb : b < 8) :
    (x >>> (8 * b).toUInt64).toUInt8 = (x.toNat / 256 ^ b % 256).toUInt8 := by
  apply UInt8.toNat_inj.mp
  have h1 : ((8 * b).toUInt64).toNat % 64 = 8 * b := by
    rw [Nat.toUInt64_eq, UInt64.toNat_ofNat']; omega
  rw [UInt64.toNat_toUInt8, UInt64.toNat_shiftRight, h1, Nat.shiftRight_eq_div_pow,
    show (256 : Nat) ^ b = 2 ^ (8 * b) by rw [Nat.pow_mul]]
  simp [Nat.toUInt8]

end Lvm.QLink
end

section
set_option autoImplicit false
namespace Lvm.QLink
open RecursionFast Lvm Lvm.Replay Lvm.Loop Lvm.Loop.Build
section
variable {ws : List Word} {msg : ℕ → ℕ → LeanVM.Parameters.K}

/-- A `KS` message byte is the stream's byte, when `KS`'s message lanes hold the stream
(`msg i l` = lane `17 i + l`, rows `i < B`). -/
theorem msgBytes_eq {B : Nat} (hmsg : ∀ i < B, ∀ l < 17, (LeanVM.Parameters.K.lane (msg i l)).toNat = lw ws (17 * i + l))
    {n : Nat} (hn : n < 136 * B) : KG.msgBytes msg (n / 136) (n % 136) = (wordsBytes ws).getD n 0 := by
  have hn : n = 8 * (n / 8) + n % 8 := by omega
  conv_rhs => rw [hn]
  rw [byte_of_lane ws _ _ (Nat.mod_lt _ (by decide)), KG.msgBytes, show n % 136 % 8 = n % 8 by omega,
    u64_byte _ _ (Nat.mod_lt _ (by decide)), hmsg _ (by omega) _ (by omega), show 17 * (n / 136) + n % 136 / 8 = n / 8 by omega]

/-- **The bytes `KS`'s first rows absorb are the stream's.** -/
theorem streamOf_KS (L : Nat)
    (hmsg : ∀ i < nBlk L, ∀ l < 17, (LeanVM.Parameters.K.lane (msg i l)).toNat = lw ws (17 * i + l))
    (hL : L ≤ 8 * ws.length) : KSponge.streamOf (KG.msgBytes msg) L = (wordsBytes ws).take L := by
  apply List.ext_getElem
  · rw [KSponge.streamOf_length, List.length_take, wordsBytes_length]; omega
  · intro n h1 h2
    rw [KSponge.streamOf_length] at h1
    have e := KSponge.streamOf_getD (KG.msgBytes msg) L h1
    rw [List.getD_eq_getElem _ _ (by rw [KSponge.streamOf_length]; exact h1)] at e
    rw [e, List.getElem_take, ← List.getD_eq_getElem _ 0 (by rw [List.length_take] at h2; omega)]
    exact msgBytes_eq hmsg (by simp only [nBlk]; omega)

/-- **WP-8's `PadOk`** for the `KS` rows that hold the stream, from Q_link's `PadOkB`. -/
theorem padOk_KS (L : Nat)
    (hmsg : ∀ i < nBlk L, ∀ l < 17, (LeanVM.Parameters.K.lane (msg i l)).toNat = lw ws (17 * i + l))
    (h : PadOkB (wordsBytes ws) L) : KSponge.PadOk (KG.msgBytes msg) L := by
  intro q h1 h2
  exact (msgBytes_eq hmsg h2).trans (h q h1 h2)

/-- **WP-8's stream hypothesis**: the `KS` rows that hold the stream absorb `tagTrace ‖ traceBytes`
of the trace the stream encodes. -/
theorem streamOf_KS_trace {p : Params} (hS : StreamOk p) (hL : LaneLink p ws)
    (hmsg : ∀ i < nBlk (hashedLen p), ∀ l < 17,
      (LeanVM.Parameters.K.lane (msg i l)).toNat = lw ws (17 * i + l)) :
    KSponge.streamOf (KG.msgBytes msg) (hashedLen p) = tagTrace :: traceBytes (decode p ws) := by
  rw [streamOf_KS _ hmsg hL.size, stream_of_laneLink hS hL]

end
end Lvm.QLink
end

section
set_option autoImplicit false
namespace Lvm.QLink
open RecursionFast Lvm Lvm.Replay Lvm.Loop Lvm.Loop.Build

/-- Q_link's standalone layout: the stream at cells `0 …` (the `17 · 2^rec` stream lanes, or the
`readd` region's `2^m` if larger: `P8`), then the QLT table, the gate cell, the position bits, the positions' BITS fields (low, then high). -/
def layOf (p : Params) (aQ K m pa : Nat) : Layout :=
  let qt := max (17 * 2 ^ p.recRowsLog) (2 ^ m)
  let fg := qt + 3 * 2 ^ aQ
  ⟨0, fg, qt, fg + 1, m, K, aQ, fg + 1 + ((opens p).map fun o => padT o.L.t * o.L.height).sum, pa⟩

/-- The input cells of the standalone layout. -/
def nInKOf (lay : Layout) : Nat := lay.fl + 2 * 2 ^ lay.pa

/-- At `P20`: 2^11 QLT iterations (1,415 entries), step array 2^8, `readd` region 2^18 lanes (the stream's
105,472 lanes need 2^17), 2^10 position cells (719 positions). -/
def lay20 : Layout := layOf P20 11 8 18 10

/-- At `P8`: 2^10 QLT iterations (914 entries), step array 2^5, `readd` region 2^17 lanes (the
stream's 46,178 lanes pass 2^16; as `LvmQAsmLay.cfg8`), 2^8 position cells (156 positions). -/
def lay8 : Layout := layOf P8 11 5 17 8

/-- KS13 (lvm2 roll 8, B1): at `P20` the `KS` table has half as many rows as `C_rec` (roll 7's KS14: as many). -/
theorem ksLog_P20 : P20.ksLog + 1 = P20.recRowsLog := by decide

theorem ksLog_P8 : P8.ksLog = P8.recRowsLog := by decide

end Lvm.QLink
end

-- ===== from `LvmQTypedHarR` =====

section
set_option autoImplicit false
namespace Lvm.Har
open Lvm Lvm.Loop Lvm.Loop.Build Lvm.QTyped Lvm.Q1 DM
open Lvm.TypedV (TNat)
open Lvm.TypedV (eq1)

/-- `divKern`'s step (its local `step`). -/
def r_dStep (p0 log : Nat) (ρa ra : Array FE) (V : Array FE) (k : Nat) : Array FE :=
  let free := decide (k < log)
  let bits : List Bool := if free then [false, true] else [p0.testBit k]
  let fac (b q : Bool) : FE :=
    (if free then eq1 (ρa.getD k 0) b else 1) *
      (if k < TypedV.recRowBits then eq1 (ra.getD k 0) q else if q then 0 else 1)
  let f00 := fac false false
  let f01 := fac false true
  let f10 := fac true false
  let f11 := fac true true
  (List.range TypedV.sLanes).foldl (fun W rem =>
    let v := V.getD rem 0
    bits.foldl (fun W b =>
      let t := 2 * rem + (if b then 1 else 0)
      let q := decide (TypedV.sLanes ≤ t)
      let f := if b then (if q then f11 else f10) else (if q then f01 else f00)
      W.modify (if q then t - TypedV.sLanes else t) (· + v * f)) W) (Array.replicate TypedV.sLanes 0)

theorem r_divKern_eq (p0 log : Nat) (ρ rlo rhi : List FE) :
    TypedV.divKern p0 log ρ rlo rhi = (List.range 17).foldl (fun acc rem => acc +
      ((List.range 19).reverse.foldl (r_dStep p0 log ρ.toArray rlo.toArray)
        ((Array.replicate 17 (0 : FE)).set! 0 1)).getD rem 0 * eqAtF rhi rem) 0 := rfl

/-- `geKern`'s step. -/
def r_geStep (c : Nat) (t : Nat → Bool → FE) (st : FE × FE) (k : Nat) : FE × FE :=
  let full := t k false + t k true
  if c.testBit k then (st.1 * t k true, st.2 * full) else (st.1 * t k false, st.2 * full + st.1 * t k true)

theorem r_geKern_eq (c log : Nat) (ρ r : List FE) :
    TypedV.geKern c log ρ r = ((List.range log).reverse.foldl
      (r_geStep c fun k b => eq1 (ρ.toArray.getD k 0) b * eq1 (r.toArray.getD k 0) b) (1, 0)).1 +
      ((List.range log).reverse.foldl
      (r_geStep c fun k b => eq1 (ρ.toArray.getD k 0) b * eq1 (r.toArray.getD k 0) b) (1, 0)).2 := rfl

theorem r_sLanes_eq : TypedV.sLanes = 17 := rfl
theorem r_recRowBits_eq : TypedV.recRowBits = 14 := rfl

theorem r_getD_modify_add (A : Array FE) (i j : Nat) (d : FE) (hj : j < A.size) :
    (A.modify i (· + d)).getD j 0 = A.getD j 0 + if i = j then d else 0 := by
  simp only [Array.getD_eq_getD_getElem?, Array.getElem?_modify, Array.getElem?_eq_getElem hj]
  split_ifs <;> simp

theorem r_foldl_getD {α : Type} (F : Array FE → α → Array FE) (D : α → Nat → FE)
    (hF : ∀ A x, (F A x).size = A.size ∧ ∀ j < A.size, (F A x).getD j 0 = A.getD j 0 + D x j) :
    ∀ (l : List α) (A : Array FE), (l.foldl F A).size = A.size ∧
      ∀ j < A.size, (l.foldl F A).getD j 0 = A.getD j 0 + (l.map fun x => D x j).sum
  | [], A => ⟨rfl, fun j _ => by simp⟩
  | x :: l, A => by
    obtain ⟨h1, h2⟩ := hF A x
    obtain ⟨ih1, ih2⟩ := r_foldl_getD F D hF l (F A x)
    refine ⟨by rw [List.foldl_cons, ih1, h1], fun j hj => ?_⟩
    rw [List.foldl_cons, ih2 j (by rw [h1]; exact hj), h2 j hj, List.map_cons, List.sum_cons, add_assoc]

/-- The quotient bit of `2 rem + b`. -/
def r_qN (rem : Nat) (b : Bool) : Bool := decide (17 ≤ 2 * rem + (if b then 1 else 0))

/-- The new remainder. -/
def r_idxN (rem : Nat) (b : Bool) : Nat :=
  if r_qN rem b then 2 * rem + (if b then 1 else 0) - 17 else 2 * rem + (if b then 1 else 0)

/-- The transition's factor. -/
def r_facN (ρa ra : Array FE) (k : Nat) (b q : Bool) : FE :=
  eq1 (ρa.getD k 0) b * (if k < 14 then eq1 (ra.getD k 0) q else if q then 0 else 1)

theorem r_dStep_getD (ρa ra V : Array FE) {k : Nat} (hk : k < 19) {j : Nat} (hj : j < 17) :
    (r_dStep 0 19 ρa ra V k).getD j 0 = ((List.range 17).map fun rem =>
      (if r_idxN rem false = j then V.getD rem 0 * r_facN ρa ra k false (r_qN rem false) else 0) +
      (if r_idxN rem true = j then V.getD rem 0 * r_facN ρa ra k true (r_qN rem true) else 0)).sum := by
  unfold r_dStep
  have hk' : decide (k < 19) = true := decide_eq_true hk
  simp only [hk', ite_true, r_sLanes_eq, r_recRowBits_eq]
  rw [(r_foldl_getD _ (fun rem j =>
      (if r_idxN rem false = j then V.getD rem 0 * r_facN ρa ra k false (r_qN rem false) else 0) +
      (if r_idxN rem true = j then V.getD rem 0 * r_facN ρa ra k true (r_qN rem true) else 0)) ?_ _ _).2 j
      (by simp [hj])]
  · simp [Array.getD]
  · intro A rem
    simp only [List.foldl_cons, List.foldl_nil]
    refine ⟨by simp, fun j hj => ?_⟩
    rw [r_getD_modify_add _ _ _ _ (by simpa using hj), r_getD_modify_add _ _ _ _ hj, add_assoc]
    simp only [r_idxN, r_qN, r_facN]
    by_cases h17 : 17 ≤ 2 * rem <;> by_cases h16 : 17 ≤ 2 * rem + 1 <;>
      simp [h17, h16]

def r_divCG (z ρi nρ : Cell) : Option Cell → BM (List (Nat × Nat × Cell))
  | none => pure [(0, 0, nρ), (1, 0, ρi)]
  | some r => do
    let nr ← neg1 r
    let c00 ← mulAdd .E nρ nr z
    let c10 ← mulAdd .E ρi nr z
    let c01 ← mulAdd .E nρ r z
    let c11 ← mulAdd .E ρi r z
    pure [(0, 0, c00), (1, 0, c10), (0, 1, c01), (1, 1, c11)]

/-- The incoming transitions of the new remainder `r'`. -/
def r_divIns (c : List (Nat × Nat × Cell)) (W : List (Option Cell)) (r' : Nat) : List (Cell × Cell) :=
  (List.range 17).flatMap fun rem => match W.getD rem none with
    | none => []
    | some w => c.filterMap fun x =>
      let v := 2 * rem + x.1
      let qb := if 17 ≤ v then 1 else 0
      if qb = x.2.1 ∧ v - 17 * qb = r' then some (w, x.2.2) else none

/-- A weight cell, `none` for no incoming transition. -/
def r_optMac (z : Cell) : List (Cell × Cell) → BM (Option Cell)
  | [] => pure none
  | l => do
    let s ← Lvm.QAcc.macChain l z
    pure (some s)

theorem r_divStep_eq (z ρi : Cell) (ri : Option Cell) (W : List (Option Cell)) :
    divStep z ρi ri W = (do
      let nρ ← neg1 ρi
      let c ← r_divCG z ρi nρ ri
      seqAll ((List.range 17).map fun r' => r_optMac z (r_divIns c W r'))) := by
  cases ri <;> rfl

end Lvm.Har
end

section
set_option autoImplicit false
namespace Lvm.Har
open Lvm Lvm.Loop Lvm.Loop.Build Lvm.QTyped Lvm.Q1 DM
open Lvm.TypedV (TNat)
open Lvm.TypedV (eq1)
section
variable {c : Ctx} {M : Mem}

theorem r_neg1_val {x : Cell} {p : Ptr} (h : SegsHold c M p (neg1 x p).2) :
    (neg1 x p).1.val M = x.val M + 1 := by
  simp only [neg1, addK] at h ⊢
  rw [lin_spec h, ofK_zero, ofK_one, zero_mul, add_zero]

theorem r_eqConstG_val {z o : Cell} (hz : z.val M = 0) (ho : o.val M = 1) :
    ∀ (rs : List Cell) (b : Nat) (p : Ptr), SegsHold c M p (eqConstG z o rs b p).2 →
      (eqConstG z o rs b p).1.val M = eqAtF (vs M rs) b
  | [], b, p, _ => by simp only [eqConstG, pure_apply, vs, List.map_nil, eqAtF, ho]
  | r :: rs, b, p, h => by
    simp only [eqConstG, bind_apply] at h ⊢
    rw [segsHold_append] at h
    have ih := r_eqConstG_val hz ho rs (b / 2) p h.1
    simp only [vs, List.map_cons, eqAtF] at ih ⊢
    by_cases hb : b % 2 = 1
    · rw [ite_eq_left hb] at h ⊢
      rw [ite_eq_left hb, mulAdd_spec h.2, ih, hz, add_zero, mul_comm]
    · rw [ite_eq_right hb] at h ⊢
      simp only [bind_apply] at h ⊢
      rw [segsHold_append] at h
      rw [ite_eq_right hb, mulAdd_spec h.2.2, r_neg1_val h.2.1, ih, hz, add_zero, mul_comm, add_comm (r.val M)]

end
end Lvm.Har
end

section
set_option autoImplicit false
namespace Lvm.Har
open Lvm Lvm.Loop Lvm.Loop.Build Lvm.QTyped Lvm.Q1 DM
open Lvm.TypedV (TNat)
open Lvm.TypedV (eq1)

/-- A weight cell's value (`none`: `0`). -/
def r_oval (M : Mem) : Option Cell → FE
  | none => 0
  | some x => x.val M

/-- The automaton's state against the circuit's weights. -/
def r_DRel (M : Mem) (V : Array FE) (W : List (Option Cell)) : Prop :=
  W.length = 17 ∧ ∀ j < 17, V.getD j 0 = r_oval M (W.getD j none)

theorem r_seqAll_length {α : Type} : ∀ (ms : List (BM α)) (p : Ptr), (seqAll ms p).1.length = ms.length
  | [], _ => rfl
  | m :: ms, p => by rw [Lvm.QSig.seqAll_cons_apply, List.length_cons, List.length_cons, r_seqAll_length ms]

end Lvm.Har
end

section
set_option autoImplicit false
namespace Lvm.Har
open Lvm Lvm.Loop Lvm.Loop.Build Lvm.QTyped Lvm.Q1 DM
open Lvm.TypedV (TNat)
open Lvm.TypedV (eq1)
section
variable {c : Ctx} {M : Mem}

theorem r_optMac_val {z : Cell} (hz : z.val M = 0) : ∀ (l : List (Cell × Cell)) (q : Ptr),
    SegsHold c M q (r_optMac z l q).2 → r_oval M (r_optMac z l q).1 = (l.map fun ab => ab.1.val M * ab.2.val M).sum
  | [], _, _ => by simp [r_optMac, pure_apply, r_oval]
  | ab :: l, q, h => by
    simp only [r_optMac, bind_apply] at h ⊢
    rw [segsHold_append] at h
    rw [pure_apply]
    simp only [r_oval]
    rw [Lvm.QAcc.macChain_spec _ _ _ h.1, hz, zero_add]

theorem r_divCG_spec {z : Cell} (hz : z.val M = 0) {ρi nρ : Cell} (hnρ : nρ.val M = ρi.val M + 1) {k : Nat}
    {ρa ra : Array FE} (hρ : ρa.getD k 0 = ρi.val M) :
    ∀ (ri : Option Cell), (∀ r, ri = some r → k < 14 ∧ ra.getD k 0 = r.val M) → (ri = none → 14 ≤ k) →
    ∀ (p : Ptr), SegsHold c M p (r_divCG z ρi nρ ri p).2 → ∀ g : Nat → Nat → FE,
      ((r_divCG z ρi nρ ri p).1.map fun x => g x.1 x.2.1 * x.2.2.val M).sum =
        g 0 0 * r_facN ρa ra k false false + g 1 0 * r_facN ρa ra k true false +
          g 0 1 * r_facN ρa ra k false true + g 1 1 * r_facN ρa ra k true true
  | none, _, hn, p, _, g => by
    have hk : ¬ k < 14 := by have := hn rfl; (clear * - this; omega)
    simp only [r_divCG, pure_apply, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, r_facN, eq1,
      hk, ite_false, ite_true, hρ, hnρ, Bool.false_eq_true]
    ring
  | some r, hr, _, p, h, g => by
    obtain ⟨hk, hra⟩ := hr r rfl
    simp only [r_divCG, bind_apply, pure_apply, List.append_nil] at h ⊢
    rw [segsHold_append, segsHold_append, segsHold_append, segsHold_append] at h
    obtain ⟨h1, h2, h3, h4, h5⟩ := h
    simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, r_facN, eq1, hk, ite_false,
      ite_true, hρ, hra, Bool.false_eq_true]
    rw [mulAdd_spec h2, mulAdd_spec h3, mulAdd_spec h4, mulAdd_spec h5, r_neg1_val h1, hnρ, hz]
    ring

theorem r_sum_filterMap_ite {α : Type} (P : α → Prop) [DecidablePred P] (h : α → Cell × Cell)
    (G : Cell × Cell → FE) : ∀ l : List α,
    ((l.filterMap fun x => if P x then some (h x) else none).map G).sum =
      (l.map fun x => if P x then G (h x) else 0).sum
  | [] => rfl
  | x :: l => by
    rw [List.filterMap_cons]
    by_cases hx : P x
    · simp only [hx, ite_true, List.map_cons, List.sum_cons, r_sum_filterMap_ite P h G l]
    · simp only [hx, ite_false, List.map_cons, List.sum_cons, r_sum_filterMap_ite P h G l, zero_add]

theorem r_sum_flatMap {α β : Type} (f : α → List β) (G : β → FE) : ∀ l : List α,
    ((l.flatMap f).map G).sum = (l.map fun a => ((f a).map G).sum).sum
  | [] => rfl
  | a :: l => by
    rw [List.flatMap_cons, List.map_append, List.sum_append, r_sum_flatMap f G l, List.map_cons, List.sum_cons]

theorem r_divIns_sum (c' : List (Nat × Nat × Cell)) (W : List (Option Cell)) (r' : Nat) :
    ((r_divIns c' W r').map fun ab => ab.1.val M * ab.2.val M).sum =
      ((List.range 17).map fun rem => r_oval M (W.getD rem none) *
        (c'.map fun x => (if (if 17 ≤ 2 * rem + x.1 then 1 else 0) = x.2.1 ∧
          2 * rem + x.1 - 17 * (if 17 ≤ 2 * rem + x.1 then 1 else 0) = r' then 1 else 0) * x.2.2.val M).sum).sum := by
  rw [r_divIns, r_sum_flatMap]
  refine congrArg List.sum (List.map_congr_left fun rem _ => ?_)
  cases hw : W.getD rem none with
  | none => simp [r_oval]
  | some w =>
    simp only [r_oval]
    refine (r_sum_filterMap_ite _ _ _ c').trans ?_
    rw [← List.sum_map_mul_left]
    refine congrArg List.sum (List.map_congr_left fun x _ => ?_)
    split_ifs <;> simp

theorem r_divStep_rel {z : Cell} (hz : z.val M = 0) {ρi : Cell} {ri : Option Cell} {k : Nat} (hk : k < 19)
    {ρa ra : Array FE} (hρ : ρa.getD k 0 = ρi.val M)
    (hri : ∀ r, ri = some r → k < 14 ∧ ra.getD k 0 = r.val M) (hn : ri = none → 14 ≤ k)
    {V : Array FE} {W : List (Option Cell)} (hVW : r_DRel M V W) {p : Ptr}
    (h : SegsHold c M p (divStep z ρi ri W p).2) : r_DRel M (r_dStep 0 19 ρa ra V k) (divStep z ρi ri W p).1 := by
  rw [r_divStep_eq] at h ⊢
  simp only [bind_apply] at h ⊢
  rw [segsHold_append, segsHold_append] at h
  obtain ⟨h1, h2, h3⟩ := h
  have hc := r_divCG_spec hz (r_neg1_val h1) hρ ri hri hn _ h2
  generalize (r_divCG z ρi (neg1 ρi p).1 ri (p.adv (neg1 ρi p).2)).1 = cc at hc h3 ⊢
  refine ⟨by rw [r_seqAll_length, List.length_map, List.length_range], fun j hj => ?_⟩
  have hv := Lvm.QAcc.seqAll_vals (fun r' => r_optMac z (r_divIns cc W r')) (r_oval M)
    (fun r' => ((r_divIns cc W r').map fun ab => ab.1.val M * ab.2.val M).sum)
    (fun k q hq => r_optMac_val hz _ q hq) (List.range 17) _ h3 j (by simpa using hj)
  rw [List.getD_eq_getElem (List.range 17) 0 (by simpa using hj), List.getElem_range] at hv
  rw [show (none : Option Cell) = default from rfl, hv, r_dStep_getD ρa ra V hk hj, r_divIns_sum]
  refine congrArg List.sum (List.map_congr_left fun rem hrem => ?_)
  have hrem' : rem < 17 := List.mem_range.mp hrem
  have hc' := hc fun b q => if (if 17 ≤ 2 * rem + b then 1 else 0) = q ∧
    2 * rem + b - 17 * (if 17 ≤ 2 * rem + b then 1 else 0) = j then 1 else 0
  rw [hc', ← hVW.2 rem hrem']
  by_cases h17 : 17 ≤ 2 * rem <;> by_cases h16 : 17 ≤ 2 * rem + 1 <;>
    simp [r_idxN, r_qN, h17, h16] <;> split_ifs <;> ring

theorem r_divRun_rel {z o : Cell} (hz : z.val M = 0) (ρ r : List Cell) {ρa ra : Array FE}
    (hρa : ∀ k < 19, ρa.getD k 0 = (ρ.getD k z).val M) (hra : ∀ k < 14, ra.getD k 0 = (r.getD k z).val M) :
    ∀ n, n ≤ 19 → ∀ (V : Array FE) (W : List (Option Cell)) (p : Ptr), r_DRel M V W →
      SegsHold c M p (divRun z o ρ r n W p).2 →
        r_DRel M ((List.range n).reverse.foldl (r_dStep 0 19 ρa ra) V) (divRun z o ρ r n W p).1
  | 0, _, V, W, p, hVW, _ => by simpa [divRun, pure_apply] using hVW
  | n + 1, hn, V, W, p, hVW, h => by
    simp only [divRun, bind_apply] at h ⊢
    rw [segsHold_append] at h
    rw [List.range_succ, List.reverse_append, List.reverse_singleton, List.singleton_append, List.foldl_cons]
    refine r_divRun_rel hz ρ r hρa hra n (by (clear * - hn; omega)) _ _ _ (r_divStep_rel hz (by (clear * - hn; omega)) (hρa n (by (clear * - hn; omega)))
      (fun r' hr' => ?_) (fun hn' => ?_) hVW h.1) h.2
    · by_cases h14 : n < 14
      · rw [ite_eq_left h14, Option.some.injEq] at hr'
        exact ⟨h14, hr' ▸ hra n h14⟩
      · rw [ite_eq_right h14] at hr'; exact absurd hr' (by simp)
    · by_cases h14 : n < 14
      · rw [ite_eq_left h14] at hn'; exact absurd hn' (by simp)
      · (clear * - hn h14; omega)

end
end Lvm.Har
end

section
set_option autoImplicit false
namespace Lvm.Har
open Lvm Lvm.Loop Lvm.Loop.Build Lvm.QTyped Lvm.Q1 DM
open Lvm.TypedV (TNat)
open Lvm.TypedV (eq1)

/-- A run of `0` bits of `c`. -/
theorem r_geRun_zero (c : Nat) (t : Nat → Bool → FE) : ∀ (ks : List Nat) (a b : FE),
    (∀ k ∈ ks, c.testBit k = false) → ks.foldl (r_geStep c t) (a, b) =
      (a * (ks.map fun k => t k false).prod,
        (a + b) * (ks.map fun k => t k false + t k true).prod - a * (ks.map fun k => t k false).prod)
  | [], a, b, _ => by simp
  | k :: ks, a, b, h => by
    have hk : c.testBit k = false := h k List.mem_cons_self
    rw [List.foldl_cons]
    simp only [r_geStep, hk, Bool.false_eq_true, ite_false]
    rw [r_geRun_zero c t ks _ _ fun k' hk' => h k' (List.mem_cons_of_mem _ hk')]
    simp only [List.map_cons, List.prod_cons, Prod.mk.injEq]
    constructor <;> ring

/-- **`geKern` at the stream's end** (`c = 17·2^14 = 2^18 + 2^14`): `Π_{k<14} t_k · t₁₈(1) ·
(Π_{14≤k<18} t_k + Π_{14≤k<18} t_k(0))`, `t_k = t_k(0) + t_k(1)` (characteristic 2). -/
theorem r_geKern_tail (t : Nat → Bool → FE) :
    ((List.range 19).reverse.foldl (r_geStep 278528 t) (1, 0)).1 +
      ((List.range 19).reverse.foldl (r_geStep 278528 t) (1, 0)).2 =
    ((List.range 14).map fun k => t k false + t k true).prod * t 18 true *
      ((t 14 false + t 14 true) * (t 15 false + t 15 true) * (t 16 false + t 16 true) *
        (t 17 false + t 17 true) + t 14 false * t 15 false * t 16 false * t 17 false) := by
  have e : (List.range 19).reverse = [18, 17, 16, 15, 14] ++ (List.range 14).reverse := by decide
  have hz : ∀ k ∈ (List.range 14).reverse, Nat.testBit 278528 k = false := by decide
  rw [e, List.foldl_append]
  simp only [List.foldl_cons, List.foldl_nil, r_geStep,
    show Nat.testBit 278528 18 = true by decide, show Nat.testBit 278528 17 = false by decide,
    show Nat.testBit 278528 16 = false by decide, show Nat.testBit 278528 15 = false by decide,
    show Nat.testBit 278528 14 = true by decide, ite_true, ite_false, Bool.false_eq_true]
  rw [r_geRun_zero _ _ _ _ _ hz, List.map_reverse, List.prod_reverse, List.map_reverse, List.prod_reverse]
  generalize ((List.range 14).map fun k => t k false).prod = P0
  generalize ((List.range 14).map fun k => t k false + t k true).prod = PF
  have h2 : (2 : FE) = 0 := CharTwo.two_eq_zero
  linear_combination (-(t 18 true) * PF * (t 14 false * t 15 false * t 16 false * t 17 false)) * h2

end Lvm.Har
end

section
set_option autoImplicit false
namespace Lvm.Har
open Lvm Lvm.Loop Lvm.Loop.Build Lvm.QTyped Lvm.Q1 DM
open Lvm.TypedV (TNat)
open Lvm.TypedV (eq1)
section
variable {c : Ctx} {M : Mem}

theorem r_add_val {a b : Cell} {p : Ptr} (h : SegsHold c M p (add a b p).2) :
    (add a b p).1.val M = a.val M + b.val M := by
  have := lin_spec h
  rw [ofK_one, one_mul, ofK_zero, add_zero] at this
  exact this

theorem r_prodG_val {z : Cell} (hz : z.val M = 0) : ∀ (l : List Cell) (acc : Cell) (p : Ptr),
    SegsHold c M p ((l.foldlM (fun acc x => mulAdd .E acc x z) acc : BM Cell) p).2 →
      ((l.foldlM (fun acc x => mulAdd .E acc x z) acc : BM Cell) p).1.val M =
        acc.val M * (l.map (Cell.val M)).prod
  | [], acc, p, _ => by simp [pure_apply]
  | x :: l, acc, p, h => by
    rw [List.foldlM_cons, hold_bind] at h
    rw [List.foldlM_cons, bind_apply, r_prodG_val hz l _ _ h.2, mulAdd_spec h.1, hz, add_zero,
      List.map_cons, List.prod_cons, mul_assoc]

theorem r_getD_vs {z : Cell} (hz : z.val M = 0) (l : List Cell) (k : Nat) :
    (vs M l).toArray.getD k 0 = (l.getD k z).val M := by
  rw [Array.getD_eq_getD_getElem?, List.getElem?_toArray, vs, List.getElem?_map, List.getD_eq_getElem?_getD]
  cases l[k]? <;> simp [hz]

theorem r_map_dt {α : Type} [Inhabited α] (ts : List α) (f : α → FE) (g : Nat → FE) (n m : Nat)
    (hl : n + m ≤ ts.length) (hv : ∀ i, n ≤ i → i < n + m → f (ts.getD i default) = g i) :
    ((ts.drop n).take m).map f = (List.range m).map fun i => g (n + i) := by
  apply List.ext_getElem
  · simp; (clear * - hl; omega)
  · intro i h1 h2
    simp only [List.length_map, List.length_range] at h2
    simp only [List.getElem_map, List.getElem_take, List.getElem_drop, List.getElem_range]
    rw [← hv (n + i) (by (clear * -; omega)) (by (clear * - h2; omega)), List.getD_eq_getElem _ _ (by (clear * - hl h2; omega))]

theorem r_forN_length {α : Type} (n : Nat) (f : Nat → BM α) (p : Ptr) : (forN n f p).1.length = n := by
  rw [forN, r_seqAll_length, List.length_map, List.length_range]

theorem r_tail_facts {z : Cell} {t : Nat → Bool → FE} (ts : List (Cell × Cell × Cell))
    (hlen : ts.length = 19)
    (v0 : ∀ i < 19, (ts.getD i default).1.val M = t i false)
    (v1 : ∀ i < 19, (ts.getD i default).2.1.val M = t i true)
    (v2 : ∀ i < 19, (ts.getD i default).2.2.val M = t i false + t i true) :
    (((ts.take 14).map (fun x => x.2.2)).map (Cell.val M)).prod =
        ((List.range 14).map fun k => t k false + t k true).prod ∧
      ((((ts.drop 14).take 4).map (fun x => x.2.2)).map (Cell.val M)).prod =
        (t 14 false + t 14 true) * (t 15 false + t 15 true) * (t 16 false + t 16 true) *
          (t 17 false + t 17 true) ∧
      ((((ts.drop 14).take 4).map (fun x => x.1)).map (Cell.val M)).prod =
        t 14 false * t 15 false * t 16 false * t 17 false ∧
      (ts.getD 18 (z, z, z)).2.1.val M = t 18 true := by
  have h4 : List.range 4 = [0, 1, 2, 3] := rfl
  refine ⟨?_, ?_, ?_, ?_⟩
  · have := r_map_dt ts (fun x => x.2.2.val M) (fun i => t i false + t i true) 0 14 (by (clear * - hlen; omega))
      (fun i _ hi => v2 i (by (clear h4 hlen v0 v1 v2; omega)))
    rw [List.drop_zero] at this
    rw [List.map_map, show (Cell.val M ∘ fun x : Cell × Cell × Cell => x.2.2) = (fun x => x.2.2.val M) from rfl,
      this]
    simp only [Nat.zero_add]
  · rw [List.map_map, show (Cell.val M ∘ fun x : Cell × Cell × Cell => x.2.2) = (fun x => x.2.2.val M) from rfl,
      r_map_dt ts (fun x => x.2.2.val M) (fun i => t i false + t i true) 14 4 (by (clear * - hlen; omega))
        (fun i _ hi => v2 i (by (clear h4 hlen v0 v1 v2; omega))), h4]
    simp only [List.map_cons, List.map_nil, List.prod_cons, List.prod_nil]
    ring
  · rw [List.map_map, show (Cell.val M ∘ fun x : Cell × Cell × Cell => x.1) = (fun x => x.1.val M) from rfl,
      r_map_dt ts (fun x => x.1.val M) (fun i => t i false) 14 4 (by (clear * - hlen; omega))
        (fun i _ hi => v0 i (by (clear h4 hlen v0 v1 v2; omega))), h4]
    simp only [List.map_cons, List.map_nil, List.prod_cons, List.prod_nil]
    ring
  · have := v1 18 (by (clear * -; omega))
    rw [List.getD_eq_getElem _ _ (by (clear * - hlen; omega))] at this ⊢
    exact this

/-- `tailG`'s per-coordinate step. -/
def r_tStep (z : Cell) (ρ r : List Cell) (i : Nat) : BM (Cell × Cell × Cell) := do
  let a := ρ.getD i z
  let b := r.getD i z
  let na ← neg1 a
  let nb ← neg1 b
  let d0 ← mulAdd .E na nb z
  let d1 ← mulAdd .E a b z
  let t ← add d0 d1
  pure (d0, d1, t)

/-- `tailG` after its steps. -/
def r_tRest (z o : Cell) (ts : List (Cell × Cell × Cell)) : BM Cell := do
  let lo ← Lvm.QAcc.macChain [] o
  let prodG (l : List Cell) : BM Cell := l.foldlM (fun acc x => mulAdd .E acc x z) lo
  let pT ← prodG ((ts.take 14).map (·.2.2))
  let pM ← prodG (((ts.drop 14).take 4).map (·.2.2))
  let pZ ← prodG (((ts.drop 14).take 4).map (·.1))
  let df ← add pM pZ
  let h ← mulAdd .E pT (ts.getD 18 (z, z, z)).2.1 z
  mulAdd .E h df z

theorem r_bind_fst {α β : Type} (m : BM α) (f : α → BM β) (p : Ptr) :
    ((m >>= f) p).1 = (f (m p).1 (p.adv (m p).2)).1 := rfl

theorem r_tailG_eq (z o : Cell) (ρ r : List Cell) :
    Lvm.QTyped.tailG z o ρ r = forN 19 (r_tStep z ρ r) >>= r_tRest z o := rfl

theorem r_tStep_val {z : Cell} (hz : z.val M = 0) (ρ r : List Cell) (t : Nat → Bool → FE)
    (ht : ∀ k b, t k b = eq1 ((ρ.getD k z).val M) b * eq1 ((r.getD k z).val M) b) (k : Nat) (q : Ptr)
    (hq : SegsHold c M q (r_tStep z ρ r k q).2) :
    (r_tStep z ρ r k q).1.1.val M = t k false ∧ (r_tStep z ρ r k q).1.2.1.val M = t k true ∧
      (r_tStep z ρ r k q).1.2.2.val M = t k false + t k true := by
  simp only [r_tStep, bind_apply, pure_apply, segsHold_append] at hq ⊢
  have e0 : (mulAdd .E (neg1 (ρ.getD k z) q).1 (neg1 (r.getD k z) (q.adv (neg1 (ρ.getD k z) q).2)).1 z
      ((q.adv (neg1 (ρ.getD k z) q).2).adv (neg1 (r.getD k z) (q.adv (neg1 (ρ.getD k z) q).2)).2)).1.val M =
      t k false := by
    rw [mulAdd_spec hq.2.2.1, r_neg1_val hq.1, r_neg1_val hq.2.1, hz, add_zero, ht]
    simp only [eq1, Bool.false_eq_true, ite_false]; ring
  have e1 : ∀ q', SegsHold c M q' (mulAdd .E (ρ.getD k z) (r.getD k z) z q').2 →
      (mulAdd .E (ρ.getD k z) (r.getD k z) z q').1.val M = t k true := by
    intro q' h'
    rw [mulAdd_spec h', hz, add_zero, ht]
    simp only [eq1, ite_true]
  refine ⟨e0, e1 _ hq.2.2.2.1, ?_⟩
  rw [r_add_val hq.2.2.2.2.1, e0, e1 _ hq.2.2.2.1]

theorem r_tRest_val {z o : Cell} (hz : z.val M = 0) (ho : o.val M = 1) {t : Nat → Bool → FE}
    (ts : List (Cell × Cell × Cell)) (hlen : ts.length = 19)
    (v0 : ∀ i < 19, (ts.getD i default).1.val M = t i false)
    (v1 : ∀ i < 19, (ts.getD i default).2.1.val M = t i true)
    (v2 : ∀ i < 19, (ts.getD i default).2.2.val M = t i false + t i true)
    (p : Ptr) (h : SegsHold c M p (r_tRest z o ts p).2) :
    (r_tRest z o ts p).1.val M =
      ((List.range 14).map fun k => t k false + t k true).prod * t 18 true *
        ((t 14 false + t 14 true) * (t 15 false + t 15 true) * (t 16 false + t 16 true) *
          (t 17 false + t 17 true) + t 14 false * t 15 false * t 16 false * t 17 false) := by
  simp only [r_tRest, bind_apply] at h ⊢
  simp only [segsHold_append] at h
  obtain ⟨h2, h3, h4, h5, h6, h7, h8⟩ := h
  obtain ⟨e1, e2, e3, e4⟩ := r_tail_facts ts hlen v0 v1 v2
  rw [mulAdd_spec h8, mulAdd_spec h7, r_add_val h6, r_prodG_val hz _ _ _ h3, r_prodG_val hz _ _ _ h4,
    r_prodG_val hz _ _ _ h5, Lvm.QAcc.macChain_spec _ _ _ h2, e1, e2, e3, e4, hz, ho]
  simp only [List.map_nil, List.sum_nil, add_zero, one_mul]

theorem r_tailG_val {z o : Cell} (hz : z.val M = 0) (ho : o.val M = 1) (ρ r : List Cell)
    (t : Nat → Bool → FE) (ht : ∀ k b, t k b = eq1 ((ρ.getD k z).val M) b * eq1 ((r.getD k z).val M) b)
    (p : Ptr) (h : SegsHold c M p (Lvm.QTyped.tailG z o ρ r p).2) :
    (Lvm.QTyped.tailG z o ρ r p).1.val M =
      ((List.range 14).map fun k => t k false + t k true).prod * t 18 true *
        ((t 14 false + t 14 true) * (t 15 false + t 15 true) * (t 16 false + t 16 true) *
          (t 17 false + t 17 true) + t 14 false * t 15 false * t 16 false * t 17 false) := by
  rw [r_tailG_eq, hold_bind] at h
  rw [r_tailG_eq, r_bind_fst]
  have hf := r_tStep_val (c := c) hz ρ r t ht
  have v0 := Lvm.QAcc.forN_vals (c := c) (M := M) (n := 19) (f := r_tStep z ρ r) (p := p)
    (fun x : Cell × Cell × Cell => x.1.val M) (fun i => t i false) (fun k q hq => (hf k q hq).1) h.1
  have v1 := Lvm.QAcc.forN_vals (c := c) (M := M) (n := 19) (f := r_tStep z ρ r) (p := p)
    (fun x : Cell × Cell × Cell => x.2.1.val M) (fun i => t i true) (fun k q hq => (hf k q hq).2.1) h.1
  have v2 := Lvm.QAcc.forN_vals (c := c) (M := M) (n := 19) (f := r_tStep z ρ r) (p := p)
    (fun x : Cell × Cell × Cell => x.2.2.val M) (fun i => t i false + t i true)
    (fun k q hq => (hf k q hq).2.2) h.1
  have hl := r_forN_length 19 (r_tStep z ρ r) p
  obtain ⟨-, h⟩ := h
  generalize p.adv (forN 19 (r_tStep z ρ r) p).2 = p' at h ⊢
  generalize (forN 19 (r_tStep z ρ r) p).1 = ts at h hl v0 v1 v2 ⊢
  exact r_tRest_val hz ho ts hl v0 v1 v2 p' h

end
end Lvm.Har
end

section
set_option autoImplicit false
namespace Lvm.Har
open Lvm Lvm.Loop Lvm.Loop.Build Lvm.QTyped Lvm.Q1 DM
open Lvm.TypedV (TNat)
open Lvm.TypedV (eq1)
section
variable {c : Ctx} {M : Mem}

theorem r_eqAtF_eqW : ∀ (r : List FE) (w : Nat), eqAtF r w = Loop.eqW r w
  | [], _ => rfl
  | a :: r, w => by
    rw [eqAtF, Loop.eqW, r_eqAtF_eqW r (w / 2), sub_eq_add_neg, CharTwo.neg_eq]

theorem r_foldl_add (f : Nat → FE) : ∀ (l : List Nat) (a : FE),
    l.foldl (fun acc x => acc + f x) a = a + (l.map f).sum
  | [], a => by simp
  | x :: l, a => by rw [List.foldl_cons, r_foldl_add f l, List.map_cons, List.sum_cons, add_assoc]

theorem r_oval_getD {z : Cell} (hz : z.val M = 0) (w : Option Cell) : (w.getD z).val M = r_oval M w := by
  cases w <;> simp [r_oval, hz]

theorem r_drel_init {o : Cell} (ho : o.val M = 1) :
    r_DRel M ((Array.replicate 17 (0 : FE)).set! 0 1) ((List.range 17).map fun i => if i = 0 then some o else none) := by
  refine ⟨by simp, fun j hj => ?_⟩
  rcases j with _ | j
  · simp [r_oval, ho]
  · simp [r_oval, hj]

end
end Lvm.Har
end

section
set_option autoImplicit false
namespace Lvm.Har
open Lvm Lvm.Loop Lvm.Loop.Build Lvm.QTyped Lvm.Q1 DM
open Lvm.TypedV (TNat)
open Lvm.TypedV (eq1)

theorem r_scSpec_len (v : Nat → FE) (count : Nat) : ∀ (p : Nat) (claim : FE) (eqs : List (Option FE)),
    (Q1.scSpec v count p claim eqs).1.length = eqs.length
  | _, _, [] => rfl
  | p, claim, e :: es => by simp only [Q1.scSpec, List.length_cons, r_scSpec_len v count _ _ es]

theorem r_getPtr_apply (p : Ptr) : getPtr p = (p, []) := rfl

end Lvm.Har
end

section
set_option autoImplicit false
namespace Lvm.Har
open Lvm Lvm.Loop Lvm.Loop.Build Lvm.QTyped Lvm.Q1 DM
open Lvm.TypedV (TNat)
open Lvm.TypedV (eq1)
section
variable {c : Ctx} {M : Mem} {sig : ByteArray} {T : Nat}

/-- **The relayout's kernel in the circuit is V_S's** (`relayKernF`), on regions that are V_S's. -/
theorem relayKernG_spec {z o : Cell} (hz : z.val M = 0) (ho : o.val M = 1) (hzE : z.ty = .E) (hoE : o.ty = .E)
    {Td : TData} {N : TNat} (htd : TdOk Td N) (ry r : List Cell) (hry : ry.length = 21) (hr : r.length = 19)
    (hryE : ∀ x ∈ ry, x.ty = .E) (hrE : ∀ x ∈ r, x.ty = .E) (q : Ptr)
    (h : SegsHold c M q (relayKernG z o Td ry r q).2) :
    (relayKernG z o Td ry r q).1.val M = TypedV.relayKernF N (vs M ry) (vs M r) := by
  have hone : M.e o.n = 1 := by rw [← ho]; rcases o with ⟨τ, n⟩; simp at hoE; subst hoE; rfl
  have hal : ∀ i, (r.getD (14 + i) z).ty = .E := fun i => by
    rw [List.getD_eq_getElem?_getD]
    cases hx : r[14 + i]? with
    | none => exact hzE
    | some y => exact hrE y (List.mem_of_getElem? hx)
  have hvt : ∀ (l : List Cell) (n : Nat), (vs M l).take n = vs M (l.take n) := fun l n => by
    simp [vs, List.map_take]
  have hρa : ∀ k < 19, ((vs M ry).take 19).toArray.getD k 0 = ((ry.take 19).getD k z).val M := fun k _ => by
    rw [hvt, r_getD_vs hz]
  have hra : ∀ k < 14, ((vs M r).take 14).toArray.getD k 0 = (r.getD k z).val M := fun k hk => by
    rw [hvt, r_getD_vs hz, List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, List.getElem?_take,
      ite_eq_left hk]
  simp only [relayKernG, regSelG, hold_bind] at h
  simp only [relayKernG, regSelG, r_bind_fst]
  obtain ⟨h1, h2, h3, h4, h5, h6⟩ := h
  have hW := r_divRun_rel hz (ry.take 19) r hρa hra 19 le_rfl _ _ _ (r_drel_init ho) h2
  generalize (divRun z o (ry.take 19) r 19 _ _).1 = W at hW h3 h4 h5 h6 ⊢
  have hWl : W.length = 17 := hW.1
  have htt : ∀ k b, (fun k b => eq1 (((vs M ry).take 19).toArray.getD k 0) b * eq1 ((vs M r).toArray.getD k 0) b) k b =
      eq1 (((ry.take 19).getD k z).val M) b * eq1 ((r.getD k z).val M) b := fun k b => by
    simp only; rw [hvt, r_getD_vs hz, r_getD_vs hz]
  rw [mulAdd_spec h6, r_add_val h5, r_eqConstG_val hz ho _ _ _ h1,
    Lvm.QAcc.eqDot_spec hal (by norm_num) (by rw [List.length_map, hWl]; norm_num) hz hone h3,
    r_tailG_val hz ho _ _ _ htt _ h4, hz, add_zero]
  simp only [TypedV.relayKernF, htd.sflat, List.foldl_cons, List.foldl_nil, zero_add]
  have hrd : List.drop 19 (vs M r) = [] := List.drop_eq_nil_of_le (by simp [vs, hr])
  have hrt : List.take 19 (vs M r) = vs M r := List.take_of_length_le (by simp [vs, hr])
  have hd5 : (List.range 5).map (fun i => (r.getD (14 + i) z).val M) = (vs M r).drop 14 := by
    apply List.ext_getElem
    · simp [vs, hr]
    · intro i h1 h2
      simp only [List.length_map, List.length_range] at h1
      simp only [List.getElem_map, List.getElem_range, List.getElem_drop, vs]
      rw [List.getD_eq_getElem _ _ (by (clear * - hr h1; omega))]
  rw [ite_eq_right (by decide), hrd, hrt, show TypedV.sPos - min TypedV.sPos 0 = 278528 from rfl, r_geKern_eq,
    r_geKern_tail, r_recRowBits_eq, show eqAtF [] (0 >>> 19) = 1 from rfl, one_mul]
  congr 1
  · simp [TypedV.hiW, vs, List.map_drop]
  · congr 1
    rw [r_divKern_eq, r_foldl_add, zero_add, Lvm.QAcc.sum_map_range, List.length_map, hWl]
    refine Finset.sum_congr rfl fun k hk => ?_
    rw [Finset.mem_range] at hk
    -- by `getElem?` (the `getD`/`getElem` round trip left the kernel evaluating `divRun`)
    have hgw : (List.map (fun w : Option Cell => w.getD z) W).getD k z = (W.getD k none).getD z := by
      rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, List.getElem?_map]; cases W[k]? <;> rfl
    rw [hd5, ← r_eqAtF_eqW, hgw, r_oval_getD hz, ← hW.2 k hk, mul_comm]

/-- **The relayout replayed**: wherever `relayG`'s rows hold and assert (gate on), `dRelayT` at `r_y` from `v_S`
from any state at `rRP P` with `ok` keeps `ok`, ends at `aP P`; `r` and `v_R` are the output's cells' values. -/
theorem relayG_replays (hS : Streamed M sig T) {z o g : Cell} (hz : z.val M = 0) (ho : o.val M = 1)
    (hzE : z.ty = .E) (hoE : o.ty = .E) (hg : g.val M = 1) (hgK : g.ty = .K) {Td : TData} {N : TNat}
    (htd : TdOk Td N) {P : Nat} (hP : P % 8 = 0) (hT : aP P + 40 ≤ 8 * T) (ry : List Cell) (hry : ry.length = 21)
    (hryE : ∀ x ∈ ry, x.ty = .E) (vS : Cell) (ptr : Ptr) (hp : 1 ≤ ptr.e) :
    Replays c M sig (TypedV.dRelayT N (vs M ry) (vS.val M)) (relayG z o g Td P ry vS) ptr (rRP P) (aP P)
      fun v t => v.1 = vs M t.1 ∧ v.2 = t.2.val M ∧ t.1.length = 19 ∧ (∀ x ∈ t.1, x.ty = .E) := by
  intro hok s hs hsok
  have hR8 : rRP P % 8 = 0 := by simp only [rRP, wVP, wRP, wGP, zAbcP, zRP, tX, tY]; (clear * - hP; omega)
  have hA : aP P = rRP P + 2304 := by simp only [aP, rVP, tR]
  have hV : rVP P = rRP P + 2280 := by simp only [rVP, tR]
  have hs' : s.ent + s.msg = rRP P := hs
  unfold relayG at hok ⊢
  obtain ⟨-, hok⟩ := okb hok
  simp only [r_getPtr_apply, Ptr.adv_nil] at hok
  obtain ⟨hF, hok⟩ := okb hok
  obtain ⟨hVl, hok⟩ := okb hok
  obtain ⟨hK, hok⟩ := okb hok
  obtain ⟨hM, hok⟩ := okb hok
  obtain ⟨hAs, -⟩ := okb hok
  simp only [r_bind_fst, r_getPtr_apply, Ptr.adv_nil, pure_apply]
  have hsc := QB.scRunP3_eq (binParts tR) (rRP P / 8) vS ptr hF.1 sig ⟨8 * (rRP P / 8), 0, true⟩ rfl rfl
    (fun j _ h2 => by rw [nRounds_binParts] at h2; exact hS j (by simp only [tR] at h2; (clear hAs hF hK hM hP hS hV hVl hg hgK ho hoE hok hp hry hryE hs hs' hsok htd hz hzE; omega)))
  rw [nRounds_binParts, Q1.sumcheck_run sig 3 (by decide)] at hsc
  simp only [show 8 * (rRP P / 8) + 0 = rRP P by (clear * - hR8; omega)] at hsc
  have hvR := Lvm.QAcc.ldE_feAt hS (q := (rVP P + 40) / 8) (by (clear * - hT hR8 hA hV; omega)) hVl.1
  have hrr : ∀ x ∈ (List.range tR).map (fun i => ec (ptr.e + 3 + 6 * i)), x.ty = .E := by
    intro x hx; simp only [List.mem_map] at hx; obtain ⟨i, _, rfl⟩ := hx; rfl
  have hk := relayKernG_spec hz ho hzE hoE htd ry _ hry (by simp) hryE hrr _ hK.1
  have hpr := mulAdd_spec hM.1
  have heq := Lvm.QAcc.assertEqE_spec hAs hg
  rw [hpr, hk, hvR, hz, add_zero, hsc.1] at heq
  rw [show feAt sig (8 * ((rVP P + 40) / 8)) = feAt sig (rRP P + 2280 + 40 + 0) from congrArg _ (by (clear * - hR8 hV; omega))]
    at heq hvR
  unfold TypedV.dRelayT
  simp only [Q1.bind_run, Q1.sumcheck_run sig 3 (by decide : 2 ≤ 3), Q1.readE_run, require_run', Q1.pure_run]
  have hst : Q1.scState 3 s (List.replicate TypedV.relayRoundsN none) = ⟨rRP P + 2280, 0, s.ok⟩ := by
    rw [← hs']; rfl
  rw [hst, hs']
  have hl := r_scSpec_len (feAt sig) 3 (rRP P) (vS.val M) (List.replicate tR none)
  rw [List.length_replicate] at hl
  have hch := hsc.2
  generalize Q1.scSpec (feAt sig) 3 (rRP P) (vS.val M) (List.replicate tR none) = SC at heq hl hch ⊢
  have hrv : SC.1 = vs M ((List.range tR).map fun i => ec (ptr.e + 3 + 6 * i)) := by
    apply List.ext_getElem
    · simp [vs, hl]
    · intro i h1 h2
      rw [← List.getD_eq_getElem _ 0 h1, ← hch i (by (clear * - hl h1; omega))]
      simp only [vs, List.getElem_map, List.getElem_range, Cell.val_E]
      congr 1; (clear * -; omega)
  dsimp only
  refine ⟨?_, ?_, hrv, hvR.symm, by simp, hrr⟩
  · rw [hsok, heq, hrv]; simp
  · simp only [pos]; (clear * - hR8 hA; omega)

end
end Lvm.Har
end

-- ===== from `LvmQTypedHarS` =====

section
section
set_option autoImplicit false
namespace Lvm.Q1
open Lvm Lvm.Loop Lvm.Loop.Build

theorem spongeBlocks_P8 : spongeBlocks P8 = 2262 := by
  rw [spongeBlocks, sizes_P8.2.2.2.2.2.2.2.1]

end Lvm.Q1
end
end

section
section
set_option autoImplicit false
namespace Lvm.Q1
open Lvm Lvm.Loop Lvm.Loop.Build

theorem getD_map_shape (ins : List Ins) (k : Nat) :
    (ins.map Ins.shape).getD k default = (ins.getD k default).shape := by
  simp only [List.getD_eq_getElem?_getD, List.getElem?_map]
  cases ins[k]? <;> rfl

theorem locOk_shape (ins : List Ins) (k : Nat) (i : Ins) :
    i.shape.locOk (ins.map Ins.shape) k = i.locOk ins k := by
  simp only [Ins.locOk, Ins.shape, List.all_map, getD_map_shape, List.length_map]
  congr 1
  congr 1
  funext s
  cases s <;> rfl

/-- **`SLok` of a template is that of its shape.** -/
theorem SLok_shape (ins : List Ins) : SLok (ins.map Ins.shape) = SLok ins := by
  simp only [SLok, List.length_map, getD_map_shape, locOk_shape]

/-- Two operand lists with the same shape. -/
def SameShape (xs ys : List Src) : Prop := xs.map Src.shape = ys.map Src.shape

theorem shape_loc (k : Nat) : (Src.loc k).shape = .loc k := rfl

theorem map_cellSrc_shape (l : List Cell) : (l.map cellSrc).map Src.shape = List.replicate l.length (.ext default) := by
  induction l with
  | nil => rfl
  | cons c l ih => simp only [List.map_cons, List.length_cons, List.replicate_succ, ih]; rfl

theorem shape_mulI (a b d : Src) : (mulI a b d).shape = mulI a.shape b.shape d.shape := rfl
theorem shape_linI (k k' : FK) (a b : Src) : (linI k k' a b).shape = linI k k' a.shape b.shape := rfl
theorem shape_addI (a b : Src) : (addI a b).shape = addI a.shape b.shape := rfl
theorem shape_shape (s : Src) : s.shape.shape = s.shape := by cases s <;> rfl

theorem dotIns_shape : ∀ (n : Nat) (s : Src) (ps : List (Src × Src)),
    (dotIns n s ps).map Ins.shape = (dotIns n s.shape (ps.map fun ab => (ab.1.shape, ab.2.shape))).map Ins.shape
  | _, _, [] => rfl
  | n, s, (a, b) :: ps => by
    simp only [dotIns, List.map_cons, shape_mulI, shape_shape, dotIns_shape (n + 1) (.loc n) ps]
    rfl

theorem mulChainIns_shape (z : Src) : ∀ (n : Nat) (s : Src) (cs : List Src),
    (mulChainIns z n s cs).map Ins.shape = (mulChainIns z n s.shape (cs.map Src.shape)).map Ins.shape
  | _, _, [] => rfl
  | n, s, c :: cs => by
    simp only [mulChainIns, List.map_cons, shape_mulI, shape_shape, mulChainIns_shape z (n + 1) (.loc n) cs]
    rfl

theorem shiftRecE_shape (n : Nat) : ∀ (xs ys : List Src) (E0 : Src),
    (shiftRecE n (xs.map Src.shape) (ys.map Src.shape) E0.shape).shape = (shiftRecE n xs ys E0).shape
  | _ :: _, _ :: _, _ => by simp [shiftRecE]
  | [], _, _ => by simp [shiftRecE, shape_shape]
  | _ :: _, [], _ => by simp [shiftRecE, shape_shape]

theorem shiftRecS_shape (n : Nat) : ∀ (xs ys : List Src) (S0 : Src),
    (shiftRecS n (xs.map Src.shape) (ys.map Src.shape) S0.shape).shape = (shiftRecS n xs ys S0).shape
  | _ :: _, _ :: _, _ => by simp [shiftRecS]
  | [], _, _ => by simp [shiftRecS, shape_shape]
  | _ :: _, [], _ => by simp [shiftRecS, shape_shape]

theorem shiftRecIns_shape (z : Src) (n : Nat) : ∀ (xs ys : List Src) (E0 S0 : Src),
    (shiftRecIns z n xs ys E0 S0).map Ins.shape =
      (shiftRecIns z.shape n (xs.map Src.shape) (ys.map Src.shape) E0.shape S0.shape).map Ins.shape
  | x0 :: x, y0 :: y, E0, S0 => by
    simp only [List.map_cons, shiftRecIns, List.map_append, shiftRecIns_shape z n x y E0 S0, List.length_map]
    congr 1
    simp only [shiftLevel, List.map_cons, List.map_nil, shape_mulI, shape_linI, shape_shape, shape_loc,
      shiftRecE_shape, shiftRecS_shape]
  | [], _, _, _ => rfl
  | _ :: _, [], _, _ => rfl

theorem preRecOut_shape (n : Nat) : ∀ (xs ys : List Src) (base : Src × Src × Src),
    preRecOut n (xs.map Src.shape) (ys.map Src.shape) (base.1.shape, base.2.1.shape, base.2.2.shape) =
      ((preRecOut n xs ys base).1.shape, (preRecOut n xs ys base).2.1.shape, (preRecOut n xs ys base).2.2.shape)
  | _ :: _, _ :: _, _ => by simp [preRecOut, shape_loc]
  | [], _, _ => rfl
  | _ :: _, [], _ => rfl

theorem preRecIns_shape (z : Src) (n : Nat) : ∀ (xs ys : List Src) (H : Nat) (base : Src × Src × Src),
    (preRecIns z n xs ys H base).map Ins.shape =
      (preRecIns z.shape n (xs.map Src.shape) (ys.map Src.shape) H
        (base.1.shape, base.2.1.shape, base.2.2.shape)).map Ins.shape
  | x0 :: x, y0 :: y, H, base => by
    simp only [List.map_cons, preRecIns, List.map_append, preRecIns_shape z n x y (H / 2) base, List.length_map,
      preRecOut_shape]
    congr 1
    simp only [preLevel, List.map_cons, List.map_nil, shape_mulI, shape_linI, shape_addI, shape_shape, shape_loc]
    split <;> simp [shape_mulI, shape_shape, shape_loc]
  | [], _, _, _ => rfl
  | _ :: _, [], _, _ => rfl

theorem eqLevelIns_shape (z : Src) (n : Nat) (olds : List Src) (r : Src) :
    (eqLevelIns z n olds r).map Ins.shape = (eqLevelIns z.shape n (olds.map Src.shape) r.shape).map Ins.shape := by
  simp only [eqLevelIns, List.map_cons, shape_linI, shape_shape, List.length_map, List.map_map]
  congr 1
  apply List.map_congr_left
  intro i hi
  have hi' := List.mem_range.mp hi
  simp only [Function.comp_def]
  split
  · rename_i h; simp only [shape_mulI, shape_shape, shape_loc]
    rw [List.getD_eq_getElem _ _ h, List.getD_eq_getElem _ _ (by simpa using h), List.getElem_map, shape_shape]
  · rename_i h; simp only [shape_mulI, shape_shape]
    rw [List.getD_eq_getElem _ _ (by omega), List.getD_eq_getElem _ _ (by simp; omega), List.getElem_map, shape_shape]

theorem eqLevelOut_shape (n m : Nat) : (eqLevelOut n m).map Src.shape = eqLevelOut n m := by
  unfold eqLevelOut; rw [List.map_map]; rfl

theorem eqTabGo_shape (z : Src) : ∀ (rs : List Src) (n : Nat) (olds : List Src),
    (eqTabGo z n olds rs).map Ins.shape = (eqTabGo z.shape n (olds.map Src.shape) (rs.map Src.shape)).map Ins.shape
  | [], _, _ => rfl
  | r :: rs, n, olds => by
    simp only [eqTabGo, List.map_cons, List.map_append, List.length_map]
    rw [eqLevelIns_shape, eqTabGo_shape z rs, eqLevelOut_shape]

theorem shape_cellSrc (c : Cell) : (cellSrc c).shape = .ext default := rfl

theorem shape_ins_mk (op : Op) (ty : Ty) (args : List Src) :
    (⟨op, ty, args⟩ : Ins).shape = ⟨op, ty, args.map Src.shape⟩ := rfl

theorem shape_getD_mapCellSrc {α : Type} (f : α → Cell) (l : List α) (i : Nat) :
    ((l.map fun x => cellSrc (f x)).getD i default).shape = .ext default := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_map]
  cases l[i]? <;> rfl

theorem eqTabOut_len : ∀ (n : Nat) (olds rs rs' : List Src), rs.length = rs'.length →
    eqTabOut n olds rs = eqTabOut n olds rs'
  | _, _, [], [], _ => rfl
  | n, olds, _ :: rs, _ :: rs', h => by
    simp only [eqTabOut]; exact eqTabOut_len _ _ rs rs' (by simpa using h)
  | _, _, [], _ :: _, h => by simp at h
  | _, _, _ :: _, [], h => by simp at h

theorem eMus_any (c₀ c₁ : Cell) : eMus [c₀, c₁] = eMus [default, default] := by
  funext m; unfold eMus
  rw [eqTabOut_len 66 [.loc 65] ([c₀, c₁].map cellSrc) ([default, default].map cellSrc) (by simp)]

theorem shape_getD_cellSrc (l : List Cell) (i : Nat) : ((l.map cellSrc).getD i default).shape = .ext default := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_map]
  cases l[i]? <;> rfl

theorem loadsAt_shape (q s N : Nat) : (loadsAt q s N).map Ins.shape = (loadsAt 0 0 N).map Ins.shape := by
  simp only [loadsAt, List.map_map]; rfl

/-- A placeholder loop output (only its shape matters to `SLok`). -/
def defOut : LoopOut := ⟨⟨0, 0⟩, [], []⟩

end Lvm.Q1
end
end

section
section
set_option autoImplicit false
namespace Lvm.Fin
open Lvm Lvm.Loop Lvm.Loop.Build Lvm.Q1

/-- The positions of a template's assertions. -/
def assertPos (ins : List Ins) : List ℕ :=
  (ins.zipIdx.filter fun x => !(x.1.op != .assert0)).map Prod.snd

/-- **`SLok` in one pass**: the reads of earlier results look the assertions up in `assertPos`. -/
def SLokF (ins : List Ins) : Bool :=
  ins.zipIdx.all fun x => (match x.1.op with
    | .muladd | .lin .. | .loadE | .assert0 | .e2 .. => true
    | _ => false) &&
    x.1.args.all fun s => match s with
      | .loc k' => decide (k' < x.2) && !((assertPos ins).contains k')
      | .prev k' => decide (k' < ins.length) && !((assertPos ins).contains k')
      | .ext _ => true

/-- A row is no assertion iff its position is not in `assertPos`. -/
theorem bne_assert {ins : List Ins} {k : ℕ} (hk : k < ins.length) :
    ((ins.getD k default).op != .assert0) = !((assertPos ins).contains k) := by
  rw [List.getD_eq_getElem _ _ hk]
  cases hc : (assertPos ins).contains k
  · have hn : ¬ k ∈ assertPos ins := by simpa using hc
    simp only [Bool.not_false]
    by_contra hb
    apply hn
    simp only [assertPos, List.mem_map, List.mem_filter]
    exact ⟨(ins[k], k), ⟨List.mem_zipIdx_iff_getElem?.mpr (by simp [hk]), by simpa using hb⟩, rfl⟩
  · have hm : k ∈ assertPos ins := by simpa using hc
    simp only [assertPos, List.mem_map, List.mem_filter] at hm
    obtain ⟨⟨i, k'⟩, ⟨hz, hb⟩, rfl⟩ := hm
    have := List.mem_zipIdx_iff_getElem?.mp hz
    simp only [List.getElem?_eq_getElem hk, Option.some.injEq] at this
    rw [← this] at hb
    simpa using hb

/-- **`SLokF` decides `SLok`** (one direction suffices). -/
theorem SLok_of_F {ins : List Ins} (h : SLokF ins = true) : SLok ins = true := by
  unfold SLok
  rw [List.all_eq_true]
  intro k hk
  rw [List.mem_range] at hk
  unfold SLokF at h
  rw [List.all_eq_true] at h
  have hx := h (ins[k], k) (List.mem_zipIdx_iff_getElem?.mpr (by simp [hk]))
  rw [List.getD_eq_getElem _ _ hk]
  unfold Ins.locOk
  simp only [Bool.and_eq_true, List.all_eq_true] at hx ⊢
  refine ⟨hx.1, fun s hs => ?_⟩
  have hs' := hx.2 s hs
  cases s with
  | loc k' =>
    simp only [Bool.and_eq_true, decide_eq_true_eq] at hs' ⊢
    refine ⟨hs'.1, ?_⟩
    rw [bne_assert (by omega)]
    exact hs'.2
  | prev k' =>
    simp only [Bool.and_eq_true, decide_eq_true_eq] at hs' ⊢
    refine ⟨hs'.1, ?_⟩
    rw [bne_assert hs'.1]
    exact hs'.2
  | ext a => rfl

end Lvm.Fin
end
end

section
section
set_option autoImplicit false
namespace Lvm.Har
open Lvm Lvm.Loop Lvm.Loop.Build Lvm.QTyped Lvm.Q1 DM
section helpers
open Lvm.QAcc Lvm.QSig

attribute [local irreducible] Lvm.QAcc.horner Lvm.QAcc.macChain Lvm.QAcc.linePts in
set_option maxHeartbeats 1000000 in
/-- **`qaccT`'s facts** (gate on, the child's stream bound): the five equations of A23 on `feAt Σ`. -/
theorem qaccT_facts {c : Ctx} {M : Mem} {sig : ByteArray} {T : Nat} {L pb : Nat} {p : Ptr}
    (hS : Streamed M sig T) (hT : L + 166 < T) (hH : 11 + pubLanes ≤ T) (hg : M.k pb = 1)
    (rx ry v : List Cell) (hrx : rx.length = 20) (hry : ry.length = 21) (hv : v.length = 4)
    (h : Lvm.QSig.Ok c M (qaccT L pb rx ry v) p) :
    let K := (List.range 2).map fun i => feAt sig (8 * (L + 5 + 9 * i))
    let H := (List.range 44).map fun j => feAt sig (8 * (L + 18 + 5 + 3 * j))
    let t := feAt sig (8 * (L + 18 + 3 * 44 + 5))
    H.headD 0 = feAt sig (8 * accLane 43) ∧ sumE H = Lvm.dot (eqKernel K) (vs M v) ∧
      accLine ((List.range 43).map fun i => feAt sig (8 * accLane i)) (K ++ vs M (rx ++ ry)) t =
        (accC M pb).pt ∧
      polyEval H t = (accC M pb).y ∧ feAt sig (8 * (L + 18 + 3 * 44 + 9 + 5)) = 0 := by
  have hD : tVars = 43 := rfl
  have hA : accVars = 43 := rfl
  have hPL : pubLanes = 747 := rfl
  have hgv : (kc pb).val M = 1 := kc_val_one hg
  unfold qaccT at h
  obtain ⟨zo, p1, evo1, epo1, o1, h⟩ := okBindE h
  obtain ⟨hz1, hz2, hz0, hone⟩ := consts_spec o1.1
  have hzv : (consts pb p).1.1.val M = 0 := by rw [hz1]; exact hz0
  have hov : M.e (consts pb p).1.2.n = 1 := by rw [hz2]; exact hone
  have hov' : (consts pb p).1.2.val M = 1 := by rw [hz2]; exact hone
  rw [evo1] at hzv hov hov'
  -- κ
  obtain ⟨kb, p2, evo2, epo2, o2, h⟩ := okBindE h
  have hk := ldEsB_spec hS (qs := (List.range 2).map fun i => L + 5 + 9 * i)
    (by intro q hq; simp only [List.mem_map, List.mem_range] at hq; obtain ⟨i, hi, rfl⟩ := hq; (clear * - hT hi; omega)) o2.1
  rw [evo2] at hk
  -- y'
  obtain ⟨y, p5, evo5, epo5, o5, h⟩ := okBindE h
  have hy := qyown_spec (by (clear * -; omega) : 1 ≤ 2) (by rw [hv]; decide) hzv hov o5.1
  rw [evo5] at hy
  -- h', acc_in'
  obtain ⟨hb, p6, evo6, epo6, o6, h⟩ := okBindE h
  have hh := ldEsB_spec hS (qs := (List.range (tVars + 1)).map fun j => L + 18 + 5 + 3 * j)
    (by intro q hq; simp only [List.mem_map, List.mem_range] at hq; obtain ⟨i, hi, rfl⟩ := hq; (clear * - hT hD hi; omega)) o6.1
  rw [evo6] at hh
  obtain ⟨ab, p7, evo7, epo7, o7, h⟩ := okBindE h
  have ha := ldEsB_spec hS (qs := (List.range (tVars + 1)).map accLane)
    (by intro q hq; simp only [List.mem_map, List.mem_range] at hq; obtain ⟨i, hi, rfl⟩ := hq
        simp only [accLane]; (clear * - hH hD hPL hi; omega)) o7.1
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
  have ht := ldE_feAt hS (q := L + 18 + 3 * (tVars + 1) + 5) (by (clear * - hT hD; omega)) o11.1
  rw [evo11] at ht
  obtain ⟨hv', p12, evo12, epo12, o12, h⟩ := okBindE h
  have hhv := horner_spec (c := c) (M := M) t zo.1 hzv ((List.range (tVars + 1)).map fun j => ec (hb + j)) p11 o12.1
  rw [evo12] at hhv
  obtain ⟨pts, p13, evo13, epo13, o13, h⟩ := okBindE h
  have hpt := linePts_spec (c := c) (M := M) t ((List.range tVars).map fun i =>
    (ec (ab + i), (((List.range 2).map (fun j => ec (kb + j)) ++ rx ++ ry).getD i (ec 0)))) p12 o13.1
  rw [evo13] at hpt
  -- the current acc_in
  obtain ⟨pc, p14, evo14, epo14, o14, h⟩ := okBindE h
  have hpc := ldEsB_val (c := c) (M := M) (qs := (List.range (tVars + 1)).map fun j => pb + 615 + 3 * j) (p := p13) o14.1
  rw [evo14] at hpc
  obtain ⟨_vo15, p15, evo15, epo15, o15, h⟩ := okBindE h
  have e15 := assertEqs_spec (c := c) (M := M) hgv ((List.range tVars).map fun i => (pts.getD i default, ec (pc + i))) p14 o15
  obtain ⟨_vo16, p16, evo16, epo16, o16, h⟩ := okBindE h
  have e16 := assertEqE_spec o16 hgv
  obtain ⟨zz, _qo17, evo17, epo17, o17, h⟩ := okBindE h
  have hz := ldE_feAt hS (q := L + 18 + 3 * (tVars + 1) + 9 + 5) (by omega) o17.1
  rw [evo17] at hz
  have e17 := assert0_spec h.2
  rw [hgv, one_mul] at e17
  have h44 : tVars + 1 = 44 := rfl
  rw [h44] at hh ha hpc ht hz hhv
  rw [hD] at e8 hpt e15 e16
  have hkv : ∀ i < 2, M.e (kb + i) = feAt sig (8 * (L + 5 + 9 * i)) := by
    intro i hi; rw [hk i (by simpa using hi)]; simp [List.getD_eq_getElem?_getD, List.getElem?_range hi]
  have hhv' : ∀ j < 44, M.e (hb + j) = feAt sig (8 * (L + 18 + 5 + 3 * j)) := by
    intro j hj; rw [hh j (by simpa using hj)]; simp [List.getD_eq_getElem?_getD, List.getElem?_range hj]
  have hav : ∀ j < 44, M.e (ab + j) = feAt sig (8 * accLane j) := by
    intro j hj; rw [ha j (by simpa using hj)]; simp [List.getD_eq_getElem?_getD, List.getElem?_range hj]
  have hHl : (List.range 44).map (fun j => feAt sig (8 * (L + 18 + 5 + 3 * j))) =
      ((List.range 44).map fun j => ec (hb + j)).map (Cell.val M) := by
    rw [List.map_map]; apply List.map_congr_left; intro j hj; rw [List.mem_range] at hj
    simp [hhv' j hj]
  have hKv : (List.range 2).map (fun i => M.e (kb + i)) = (List.range 2).map fun i => feAt sig (8 * (L + 5 + 9 * i)) := by
    apply List.map_congr_left; intro i hi; rw [List.mem_range] at hi; exact hkv i hi
  dsimp only
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · rw [List.range_succ_eq_map, List.map_cons, List.headD_cons]
    have := hhv' 0 (by (clear * -; omega))
    rw [Nat.add_zero] at this
    rw [← this, ← hav 43 (by (clear * -; omega))]; exact e8
  · have hsum : sh.val M = ((List.range 44).map fun j => feAt sig (8 * (L + 18 + 5 + 3 * j))).sum := by
      rw [hsh, hzv, zero_add, List.map_map, hHl, List.map_map]
      congr 1; apply List.map_congr_left; intro j _
      simp [hov']
    rw [sumE_eq, ← hsum, e10, hy, dot_eqKernel _ _ (by simp [vs, hv]), hKv]
    simp only [vs, List.length_map]
    refine Finset.sum_congr rfl fun k hk => ?_
    rw [Finset.mem_range] at hk
    rw [List.getD_eq_getElem _ _ hk, List.getD_eq_getElem _ _ (by simpa using hk), List.getElem_map]
  · have hbc : ((List.range 2).map (fun j => ec (kb + j)) ++ rx ++ ry).map (Cell.val M) =
        (List.range 2).map (fun i => feAt sig (8 * (L + 5 + 9 * i))) ++ vs M (rx ++ ry) := by
      rw [← hKv, List.append_assoc, List.map_append, List.map_map]; rfl
    have hbl : ((List.range 2).map (fun j => ec (kb + j)) ++ rx ++ ry).length = 43 := by
      simp [hrx, hry]
    rw [← hbc, ← ht]
    apply List.ext_getElem
    · simp [accLine, accC, List.length_zipWith, hrx, hry, hA]
    intro i h1 h2
    have hi : i < 43 := by simpa [accC, hA] using h2
    have hpi := hpt.2 i (by simpa using hi)
    rw [List.getD_eq_getElem ((List.range 43).map fun i =>
        (ec (ab + i), ((List.range 2).map (fun j => ec (kb + j)) ++ rx ++ ry).getD i (ec 0))) _ (by simpa using hi),
      List.getElem_map, List.getElem_range,
      List.getD_eq_getElem ((List.range 2).map (fun j => ec (kb + j)) ++ rx ++ ry) _ (by rw [hbl]; exact hi)] at hpi
    have hq := e15 ((pts.getD i default, ec (pc + i))) (List.mem_map.mpr ⟨i, List.mem_range.mpr hi, rfl⟩)
    have hpci : M.e (pc + i) = ⟨M.k (pb + 615 + 3 * i), M.k (pb + 615 + 3 * i + 1),
        M.k (pb + 615 + 3 * i + 2)⟩ := by
      rw [hpc i (by simp; (clear * - hi; omega))]
      simp [List.getD_eq_getElem?_getD, List.getElem?_range (by (clear * - hi; omega) : i < 44)]
    simp only [Cell.val_E] at hq hpi
    rw [hq, hpci, hav i (by (clear * - hi; omega))] at hpi
    simp only [accLine, List.getElem_zipWith, List.getElem_map, List.getElem_range, accC]
    exact hpi.symm
  · rw [hHl, ← ht, ← hhv, e16, Cell.val_E, hpc 43 (by simp)]
    simp [accC, List.getD_eq_getElem?_getD, hA]
  · exact hz.symm.trans e17

/-- **`dAccT` from position `Q = ent + msg`**: `κ`, `h`, `t`, the zero scalar at fixed offsets. -/
theorem dAccT_run (pub : Pub) (rxy w : List FE) (sig : ByteArray) (s : RS) :
    TypedV.dAccT pub rxy w sig s =
      let K := (List.range 2).map fun i => feAt sig (s.ent + s.msg + 40 + 72 * i)
      let H := (List.range 44).map fun j => feAt sig (s.ent + s.msg + 184 + 24 * j)
      let t := feAt sig (s.ent + s.msg + 1240)
      (⟨accLine pub.accIn.pt (K ++ rxy) t, polyEval H t⟩,
        ⟨s.ent + s.msg + 1272, 24, (feAt sig (s.ent + s.msg + 1312) == 0) &&
          ((sumE H == Lvm.dot (eqKernel K) w) && ((H.headD 0 == pub.accIn.y) && s.ok))⟩) := by
  unfold TypedV.dAccT
  rw [Lvm.Q1.bind_run, Lvm.Q1.samples_run sig 2 _ (by norm_num), Lvm.Q1.bind_run, Lvm.Q1.readEs_run,
    Lvm.Q1.bind_run, Lvm.Q1.sampleE_run, Lvm.Q1.bind_run, Lvm.Q1.readE_run, Lvm.Q1.bind_run, require_run_lk,
    Lvm.Q1.bind_run, require_run_lk, Lvm.Q1.bind_run, require_run_lk, Lvm.Q1.pure_run]
  dsimp only [scalarsAt]
  rfl

/-- The child's `acc_in` (`pubOf`'s header) at the stream lanes `accLane`. -/
theorem pubOf_accIn (vk cL : Vector UInt8 32) (sig : ByteArray) :
    (pubOf vk cL sig).accIn.y = feAt sig (8 * accLane 43) ∧
      (pubOf vk cL sig).accIn.pt = (List.range 43).map fun i => feAt sig (8 * accLane i) := by
  have hacc : ∀ i, headerAt (offAcc + eBytes * i) = 8 * accLane i := by
    intro i; simp only [headerAt, offAcc, eBytes, sigBytes, accLane]; omega
  refine ⟨?_, ?_⟩
  · show feAt sig (headerAt (offAcc + eBytes * 43)) = _; rw [hacc]
  · show (List.range 43).map (fun i => feAt sig (headerAt (offAcc + eBytes * i))) = _
    simp only [hacc]

end helpers
end Lvm.Har
end
end

section
section
set_option autoImplicit false
namespace Lvm.Har
open Lvm Lvm.Loop Lvm.Loop.Build Lvm.QTyped Lvm.Q1 DM
section
variable {c : Ctx} {M : Mem} {sig : ByteArray} {T : Nat}

/-- **A23 at `Φ_Q` replayed** (soundness direction). -/
theorem qaccT_replays (vk cL : Vector UInt8 32) (hS : Streamed M sig T) (hH : 11 + pubLanes ≤ T) {pb : Nat}
    (hg : M.k pb = 1) {P : Nat} (hP : P % 8 = 0) (hT : mbP P + 40 ≤ 8 * T) (rx ry v : List Cell)
    (hrx : rx.length = 20) (hry : ry.length = 21) (hv : v.length = 4) (hE : ∀ x ∈ rx ++ ry ++ v, x.ty = .E)
    (ptr : Ptr) :
    Replays c M sig (TypedV.dAccT (pubOf vk cL sig) (vs M (rx ++ ry)) (vs M v)) (qaccT (aP P / 8) pb rx ry v) ptr
      (aP P) (mbP P) fun a _ => a = Lvm.QAcc.accC M pb := by
  intro h s hs hok
  have hD : tVars = 43 := rfl
  have h8 : 8 * (aP P / 8) = aP P := by
    have : aP P % 8 = 0 := by simp only [aP, rVP, rRP, wVP, wRP, wGP, zAbcP, zRP]; (clear * - hP; omega)
    (clear * - this; omega)
  have hmb : mbP P = aP P + 1296 := by unfold mbP; rw [hD]
  obtain ⟨F1, F2, F3, F4, F5⟩ := qaccT_facts hS (by (clear * - hT h8 hmb; omega)) hH hg rx ry v hrx hry hv h
  obtain ⟨hy, hpt⟩ := pubOf_accIn vk cL sig
  have hQ : s.ent + s.msg = 8 * (aP P / 8) := by rw [h8]; exact hs
  rw [dAccT_run]
  dsimp only
  rw [hQ]
  -- the reader's positions as the gadget's lanes
  have eK : (List.range 2).map (fun i => feAt sig (8 * (aP P / 8) + 40 + 72 * i)) =
      (List.range 2).map fun i => feAt sig (8 * (aP P / 8 + 5 + 9 * i)) :=
    List.map_congr_left fun i _ => congrArg _ (by (clear * -; omega))
  have eH : (List.range 44).map (fun j => feAt sig (8 * (aP P / 8) + 184 + 24 * j)) =
      (List.range 44).map fun j => feAt sig (8 * (aP P / 8 + 18 + 5 + 3 * j)) :=
    List.map_congr_left fun j _ => congrArg _ (by (clear * -; omega))
  have et : feAt sig (8 * (aP P / 8) + 1240) = feAt sig (8 * (aP P / 8 + 18 + 3 * 44 + 5)) :=
    congrArg _ (by (clear * -; omega))
  have ez : feAt sig (8 * (aP P / 8) + 1312) = feAt sig (8 * (aP P / 8 + 18 + 3 * 44 + 9 + 5)) :=
    congrArg _ (by (clear * -; omega))
  rw [eK, eH, et, ez]
  refine ⟨?_, ?_, ?_⟩
  · rw [F5, F1, hy, F2]
    simp [hok]
  · show 8 * (aP P / 8) + 1272 + 24 = mbP P
    (clear * - h8 hmb; omega)
  · rw [hpt, F3, F4]

end
end Lvm.Har
end
end

section
section
set_option autoImplicit false
namespace Lvm.Har
open Lvm Lvm.Loop Lvm.Loop.Build Lvm.QTyped Lvm.Q1 Lvm.M3 DM
open Lvm.TypedV (TNat)

theorem typedPos_le (Td : TData) (P : Nat) :
    wGP P ≤ rRP P ∧ rRP P ≤ aP P ∧ aP P ≤ mbP P ∧ mbP P ≤ typedEnd Td P := by
  have h1 : mbP P ≤ busEndD Td.mbD (mbP P) := by
    unfold busEndD
    have := le_layersEnd (gkrSteps Td.mbD) 0 (busP1 (mbP P) + 48)
    simp only [busP1] at this ⊢
    omega
  have h2 : busEndD Td.mbD (mbP P) ≤ typedEnd Td P := by
    unfold typedEnd tabEnd; (clear * -; omega)
  refine ⟨?_, ?_, ?_, le_trans h1 h2⟩ <;> simp only [wGP, rRP, aP, mbP, wRP, wVP, rVP] <;> (clear * -; omega)

theorem typedPos_mod {P : Nat} (hP : P % 8 = 0) :
    wGP P % 8 = 0 ∧ rRP P % 8 = 0 ∧ aP P % 8 = 0 ∧ mbP P % 8 = 0 := by
  simp only [wGP, rRP, aP, mbP, wRP, wVP, rVP, zAbcP, zRP, tX, tY, tR, tVars]
  omega

private theorem bind_runG {α β : Type} (m : DM α) (f : α → DM β) (sig : ByteArray) (s : RS) :
    (m >>= f) sig s = f (m sig s).1 sig (m sig s).2 := (bind_run' m f sig s).trans rfl
private theorem pure_runG {α : Type} (a : α) (sig : ByteArray) (s : RS) : (pure a : DM α) sig s = (a, s) :=
  (pure_run' a sig s).trans rfl

end Lvm.Har
end
end

section
section
set_option autoImplicit false
namespace Lvm.Har
open Lvm Lvm.Loop Lvm.Loop.Build Lvm.QTyped Lvm.Q1 Lvm.M3 DM
open Lvm.TypedV (TNat)
section
variable {c : Ctx} {M : Mem} {sig : ByteArray} {T : Nat}

set_option maxHeartbeats 1000000 in
/-- **The typed core gadget replays `dTypedT`** (soundness direction). -/
theorem typedG_replaysG (vk cL : Vector UInt8 32) (hS : Streamed M sig T) (hH : 11 + pubLanes ≤ T) {pb : Nat}
    (hg : M.k pb = 1) (hvk : ∀ i < 4, M.k (pb + 1 + i) = (digestLanes vk).getD i 0) {z o : Cell}
    (hzE : z.ty = .E) (hoE : o.ty = .E) (hz : z.val M = 0) (ho : o.val M = 1) (p : Params)
    (hl : p.leafdecReads = 1) {Td : TData} {N : TNat} (htd : TdOk Td N) (hsc : sumcheckTabs N.mbT = N.mbT)
    (hS' : Td.mbS = N.mbT.map Tab.shape) (hR : Td.mbR = p.tableRounds) (hD : Td.mbD = p.busDepth)
    (hfix : FixListed N.mbT Td.mbFix) {P : Nat} (hP : P % 8 = 0) (hT : typedEnd Td P + 40 ≤ 8 * T) (q : Ptr)
    (hq : 1 ≤ q.e) :
    Replays c M sig (TypedV.dTypedT p N (N.m3 p) (pubOf vk cL sig)) (typedG Td pb P z o) q P (typedEnd Td P)
      fun v t => v.1 = Lvm.QAcc.accC M pb ∧
        v.2.1 = TypedV.typedClaimsN N p (vs M t.ry) (vs M t.rv) (vs M t.rr) (t.vR.val M) ∧
        v.2.2 = t.tab.map fun e => (vs M e.1, vs M e.2) := by
  intro hok s hs hsok
  have hgv : (kc pb).val M = 1 := Lvm.QAcc.kc_val_one hg
  obtain ⟨l1, l2, l3, l4⟩ := typedPos_le Td P
  obtain ⟨m1, m2, m3, m4⟩ := typedPos_mod hP
  simp only [typedG] at hok
  simp only [typedG, bind_apply, pure_apply, TypedV.dTypedT, bind_runG, pure_runG]
  rw [show N.m3 p = M3.real p (fun _ => N.mbT) from rfl]
  -- the zerocheck
  obtain ⟨hZ, hok⟩ := okb hok
  generalize hzr : (zeroG z (kc pb) P q).1 = zr at hok ⊢
  generalize hq1 : q.adv (zeroG z (kc pb) P q).2 = q1 at hok ⊢
  have hq1e : 1 ≤ q1.e := le_trans hq (by rw [← hq1]; exact adv_e_le _ _)
  have RZ := zeroG_replays (c := c) hS hz hzE hgv rfl hP (by (clear * - hT l1 l2 l3 l4 m1 m2 m3 m4; omega)) q hq hZ s hs hsok
  rw [hzr] at RZ
  generalize TypedV.dZeroT sig s = Zv at RZ ⊢
  obtain ⟨zv, s1⟩ := Zv
  obtain ⟨z1, z2, z3, z4, z5, z6, z7, z8⟩ := RZ
  simp only at z1 z2 z3 z4 z5 z6 ⊢
  have ez : zv.2 = ((zr.2.getD 0 z).val M, (zr.2.getD 1 z).val M, (zr.2.getD 2 z).val M) := by
    rw [← z4, ← z5, ← z6]
  rw [ez]
  -- the wiring
  obtain ⟨hW, hok⟩ := okb hok
  generalize hw : (wireG z o (kc pb) Td pb P zr.2 q1).1 = w at hok ⊢
  generalize hq2 : q1.adv (wireG z o (kc pb) Td pb P zr.2 q1).2 = q2 at hok ⊢
  have hq2e : 1 ≤ q2.e := le_trans hq1e (by rw [← hq2]; exact adv_e_le _ _)
  have RW := wireG_replays (c := c) vk cL hS hH hz ho hzE hoE hgv rfl htd hvk hP (by (clear * - hT l2 l3 l4 m2 m3 m4; omega)) zr.2 q1 hq1e hW s1 z2 z1
  rw [hw] at RW
  generalize TypedV.dWiringT N (pubOf vk cL sig) ((zr.2.getD 0 z).val M, (zr.2.getD 1 z).val M,
    (zr.2.getD 2 z).val M) sig s1 = Wv at RW ⊢
  obtain ⟨wv, s2⟩ := Wv
  obtain ⟨w1, w2, w3, w4, w5, w6, w7, w8, w9, w10, w11⟩ := RW
  simp only at w1 w2 w3 w4 w5 ⊢
  have evS : wv.2.2.getD 1 0 = (w.2.2.getD 1 z).val M := by
    rw [w5]; exact Lvm.QAcc.getD_vals _ _ hz 1
  rw [evS, w3]
  -- the relayout
  obtain ⟨hRl, hok⟩ := okb hok
  generalize hr : (relayG z o (kc pb) Td P w.1 (w.2.2.getD 1 z) q2).1 = r at hok ⊢
  generalize hq3 : q2.adv (relayG z o (kc pb) Td P w.1 (w.2.2.getD 1 z) q2).2 = q3 at hok ⊢
  have hq3e : 1 ≤ q3.e := le_trans hq2e (by rw [← hq3]; exact adv_e_le _ _)
  have RR := relayG_replays (c := c) hS hz ho hzE hoE hgv rfl htd hP (by (clear * - hT l3 l4 m3 m4; omega)) w.1 w6 w7 (w.2.2.getD 1 z) q2
    hq2e hRl s2 w2 w1
  rw [hr] at RR
  generalize TypedV.dRelayT N (vs M w.1) ((w.2.2.getD 1 z).val M) sig s2 = Rv at RR ⊢
  obtain ⟨rv, s3⟩ := Rv
  obtain ⟨r1, r2, r3, r4, r5, r6⟩ := RR
  simp only at r1 r2 r3 r4 ⊢
  have exy : zv.1 ++ vs M w.1 = vs M (zr.1 ++ w.1) := by rw [z3]; simp [vs]
  rw [exy, w4]
  -- A23 at `Φ_Q`
  obtain ⟨hA, hok⟩ := okb hok
  generalize hq4 : q3.adv (qaccT (aP P / 8) pb zr.1 w.1 w.2.1 q3).2 = q4 at hok ⊢
  have hq4e : 1 ≤ q4.e := le_trans hq3e (by rw [← hq4]; exact adv_e_le _ _)
  have hE : ∀ x ∈ zr.1 ++ w.1 ++ w.2.1, x.ty = .E := by
    intro x hx
    simp only [List.mem_append] at hx
    rcases hx with (hx | hx) | hx
    · exact z8 x hx
    · exact w7 x hx
    · exact w9 x hx
  have RA := qaccT_replays (c := c) vk cL hS hH hg hP (by (clear * - hT l4 m4; omega)) zr.1 w.1 w.2.1 z7 w6 w8 hE q3 hA s3 r2 r1
  generalize TypedV.dAccT (pubOf vk cL sig) (vs M (zr.1 ++ w.1)) (vs M w.2.1) sig s3 = Av at RA ⊢
  obtain ⟨av, s4⟩ := Av
  obtain ⟨a1, a2, a3⟩ := RA
  simp only at a1 a2 a3 ⊢
  -- the mini-bus
  obtain ⟨hM, -⟩ := okb hok
  have RM := miniG_replays (c := c) hS hz ho hzE hoE hgv rfl p hl Td N.mbT hsc hS' hR hD hfix
    (pubOf vk cL sig) m4 (by unfold typedEnd at hT; omega) q4 hq4e hM s4 a2 a1
  generalize TypedV.dMiniT p (M3.real p fun _ => N.mbT) N.mbT (pubOf vk cL sig) sig s4 = Mv at RM ⊢
  obtain ⟨mv, s5⟩ := Mv
  obtain ⟨b1, b2, b3⟩ := RM
  refine ⟨b1, b2, a3, ?_, b3⟩
  rw [w5, r3, r4]

end
end Lvm.Har
end
end

section
section
set_option autoImplicit false
namespace Lvm.Har
open Lvm DM

/-- **`decideProgT` by phases.** -/
def decideProgTH (p : Params) (N : TypedV.TNat) (vk c : Vector UInt8 32) : DM Acc := do
  let sig ← read
  let pub := pubOf vk c sig
  skip (nodeBytes * 2 ^ (p.level ⟨.main, 0⟩).cap)
  let (acc, tcl, evals) ← TypedV.dTypedT p N (N.m3 p) pub
  let tp ← tapePh p
  let wo ← wirePhC p pub tp.claim
  let (rk, vks, kko, kring) ← ksPh p
  let (okK, kLinkClaims) ← ksLinkPh p (N.m3 p) rk pub
  require okK
  TypedV.dOpenT p (TypedV.smallT p pub) (tcl ++ Shape.dClaimsZ (N.m3 p) p pub [] evals tp wo.1 wo.2 rk vks
    (keccakClaims (N.m3 p).ksBlock kko kring) kLinkClaims)
  pure acc

set_option maxHeartbeats 4000000 in
theorem decideProgT_eq (p : Params) (N : TypedV.TNat) (vk c : Vector UInt8 32) :
    TypedV.decideProgT p N vk c = decideProgTH p N vk c := by
  funext sig s
  simp only [TypedV.decideProgT, decideProgTH, tapePh, wirePhC, ksPh, ksLinkPh, bind_assoc, pure_bind]

private theorem bind_runT {α β : Type} (m : DM α) (f : α → DM β) (sig : ByteArray) (s : RS) :
    (m >>= f) sig s = f (m sig s).1 sig (m sig s).2 := (bind_run' m f sig s).trans rfl
private theorem pure_runT {α : Type} (a : α) (sig : ByteArray) (s : RS) : (pure a : DM α) sig s = (a, s) :=
  (pure_run' a sig s).trans rfl
private theorem require_runT (c : Bool) (sig : ByteArray) (s : RS) :
    require c sig s = ((), { s with ok := c && s.ok }) := (require_run' c sig s).trans rfl
private theorem skip_runT (n : Nat) (sig : ByteArray) (s : RS) :
    skip n sig s = ((), { s with msg := s.msg + n }) := (skip_run' n sig s).trans rfl
private theorem read_runT (sig : ByteArray) (s : RS) : (read : DM ByteArray) sig s = (sig, s) :=
  (read_run' sig s).trans rfl

/-- **`decideCoreT` and `accOutOfT` from the phases** (generic in the parameters and the instance). -/
theorem core_of_phasesT (p : Params) (N : TypedV.TNat) (vk c : Vector UInt8 32) (sig : ByteArray)
    {Pb P4 P5 P6 P7 P8 : Nat} {acc : Acc} {tcl : List (Com × BlockClaim × FE)}
    {evals : List (List FE × List FE)} {tp : TapeRes} {wo : WireOut × List FE} {rk vks : List FE}
    {kko : KeccakOut} {kring : FE × (List FE → FE)} {okK : Bool} {kLinkClaims : List (Com × BlockClaim)}
    (h0 : RS.start.ent + nodeBytes * 2 ^ (p.level ⟨.main, 0⟩).cap = Pb)
    (htyped : PhaseAt (TypedV.dTypedT p N (N.m3 p) (pubOf vk c sig)) sig Pb P4 (acc, tcl, evals))
    (htape : PhaseAt (tapePh p) sig P4 P5 tp)
    (hwire : PhaseAt (wirePhC p (pubOf vk c sig) tp.claim) sig P5 P6 wo)
    (hks : PhaseAt (ksPh p) sig P6 P7 (rk, vks, kko, kring))
    (hksl : PhaseAt (ksLinkPh p (N.m3 p) rk (pubOf vk c sig)) sig P7 P8 (okK, kLinkClaims)) (hokK : okK = true)
    (hopen : ∀ s : RS, pos s = P8 → s.ok = true →
      let o := TypedV.dOpenT p (TypedV.smallT p (pubOf vk c sig))
        (tcl ++ Shape.dClaimsZ (N.m3 p) p (pubOf vk c sig) [] evals tp wo.1 wo.2 rk vks
          (keccakClaims (N.m3 p).ksBlock kko kring) kLinkClaims) sig s
      o.2.ok = true ∧ o.2.ent = sig.size ∧ o.2.msg = 0) :
    TypedV.decideCoreT p N vk c sig = true ∧ TypedV.accOutOfT p N vk c sig = acc := by
  obtain ⟨s1, hs1⟩ : ∃ s1 : RS, s1 = ⟨RS.start.ent, nodeBytes * 2 ^ (p.level ⟨.main, 0⟩).cap, true⟩ :=
    ⟨_, rfl⟩
  have e1 : pos s1 = Pb := by rw [← h0, hs1]; rfl
  obtain ⟨b1, b2, b3⟩ := htyped s1 e1 (by rw [hs1])
  generalize hB : TypedV.dTypedT p N (N.m3 p) (pubOf vk c sig) sig s1 = B at b1 b2 b3
  obtain ⟨bv, s2⟩ := B
  simp only at b1 b2 b3
  rw [b1] at hB
  obtain ⟨c1, c2, c3⟩ := htape s2 b3 b2
  generalize hC : tapePh p sig s2 = CC at c1 c2 c3
  obtain ⟨cv, s5⟩ := CC
  simp only at c1 c2 c3
  rw [c1] at hC
  obtain ⟨l1, l2, l3⟩ := hwire s5 c3 c2
  generalize hL : wirePhC p (pubOf vk c sig) tp.claim sig s5 = LL at l1 l2 l3
  obtain ⟨lv, s6⟩ := LL
  simp only at l1 l2 l3
  rw [l1] at hL
  obtain ⟨k1, k2, k3⟩ := hks s6 l3 l2
  generalize hK : ksPh p sig s6 = KK at k1 k2 k3
  obtain ⟨kv, s7⟩ := KK
  simp only at k1 k2 k3
  rw [k1] at hK
  obtain ⟨m1, m2, m3⟩ := hksl s7 k3 k2
  generalize hM : ksLinkPh p (N.m3 p) rk (pubOf vk c sig) sig s7 = MM at m1 m2 m3
  obtain ⟨mv, s8⟩ := MM
  simp only at m1 m2 m3
  rw [m1] at hM
  obtain ⟨s8', hs8'⟩ : ∃ s8' : RS, s8' = { s8 with ok := okK && s8.ok } := ⟨_, rfl⟩
  have e8 : pos s8' = P8 := by rw [hs8']; exact m3
  have o8 : s8'.ok = true := by rw [hs8']; simp [hokK, m2]
  obtain ⟨o1, o2', o3⟩ := hopen s8' e8 o8
  generalize hO : TypedV.dOpenT p (TypedV.smallT p (pubOf vk c sig))
    (tcl ++ Shape.dClaimsZ (N.m3 p) p (pubOf vk c sig) [] evals tp wo.1 wo.2 rk vks
      (keccakClaims (N.m3 p).ksBlock kko kring) kLinkClaims) sig s8' = OO at o1 o2' o3
  obtain ⟨ov, s9⟩ := OO
  simp only at o1 o2' o3
  have run : decideProgTH p N vk c sig RS.start = (acc, s9) := by
    unfold decideProgTH
    simp only [bind_runT, read_runT, skip_runT, pure_runT, require_runT]
    have hs1' : ({ RS.start with msg := RS.start.msg + nodeBytes * 2 ^ (p.level ⟨.main, 0⟩).cap } : RS) = s1 := by
      simp [hs1, RS.start]
    rw [hs1', hB]
    simp only
    rw [hC]
    simp only
    rw [hL]
    simp only
    rw [hK]
    simp only
    rw [hM]
    simp only
    rw [← hs8', hO]
  have hrun : (TypedV.decideProgT p N vk c).runOn sig = (acc, s9) := by
    rw [decideProgT_eq, DM.runOn, StateT.run]; exact run
  -- `decideCoreT`, `accOutOfT` by `delta` on the bare constants: unfolding them applied (`unfold`) left the kernel a
  -- check whose `match`/projection on the run it reduced by running `decideProgT` symbolically
  have eC : @TypedV.decideCoreT = @TypedV.decideCoreT := rfl
  conv at eC => rhs; delta TypedV.decideCoreT
  have eA : @TypedV.accOutOfT = @TypedV.accOutOfT := rfl
  conv at eA => rhs; delta TypedV.accOutOfT
  rw [eC, eA]
  beta_reduce
  rw [hrun]
  simp only [o1, o2', o3, Bool.true_and, beq_self_eq_true, and_self]

end Lvm.Har
end
end

section
set_option autoImplicit false
namespace Lvm.Har
open RecursionFast Lvm Lvm.Loop Lvm.Loop.Build Lvm.Q1 Lvm.QAsm Lvm.QTyped Lvm.Typed Lvm.NS Lvm.T Lvm.ASM Lvm.QLink
  Lvm.Replay DM
open Lvm.M3 (lay26)
open Lvm.VEq (pubX)
open LeanVM.Protocol (Column)

/-- **The typed HAR's numbers at `P20`** (one kernel decision): phases 4–7's positions (roll 7's `P47Pos`), the
lane bounds, the sizes, the typed phases' and the openings' positions (`T` the stream's lanes). -/
def HarNumT (T P4 P5 P6 P7 P8 : Nat) : Prop :=
  (P4 + 40 = 8 * aLane P20 0 ∧ P4 + 72 * P20.logN + 40 = 8 * aLane P20 1 ∧
    8 * aLane P20 2 - 40 = P4 + 72 * P20.logN + 600 ∧
    Lvm.Q1.tapeEnd (P20.logN - 5) (aLane P20 2) = aLane P20 3 ∧ 8 * aLane P20 3 - 40 = P5 ∧
    8 * Lvm.Q1.wireEnd (P20.logN - 5) (aLane P20 3) - 40 = P6 ∧ P6 + 40 = 8 * aLane P20 4 ∧
    kV P20.ksLog P6 + 40 = 8 * aLane P20 5 ∧ kG P20.ksLog P6 = 8 * aLane P20 6 - 40 ∧
    8 * gkrEnd (P20.ksLog - 4) (aLane P20 6) - 40 + 72 * ringStages = P7 ∧ P7 + 40 = 8 * aLane P20 7 ∧
    ksP2 P20 P7 + 96 = P8) ∧
  5 ≤ P20.logN ∧ 4 ≤ P20.ksLog ∧ 5 ≤ aLane P20 2 ∧ 5 ≤ aLane P20 3 ∧ 5 ≤ aLane P20 6 ∧
  Lvm.Q1.wireEnd (P20.logN - 5) (aLane P20 3) + 2 ≤ T ∧ gkrEnd (P20.ksLog - 4) (aLane P20 6) + 48 ≤ T ∧
  aLane P20 0 + 9 * P20.logN + 2 < T ∧ aLane P20 1 + 3 * 25 + 2 < T ∧
  aLane P20 4 + 9 * P20.ksLog + 2 < T ∧ aLane P20 5 + 3 * 25 + 2 < T ∧
  P20.logN ≤ 2 ^ Lvm.QAsm.clog2 P20.logN ∧ P20.ksLog ≤ 2 ^ Lvm.QAsm.clog2 P20.ksLog ∧
  ksQV P20.ksLog (aLane P20 7) + 3 * 4 + 3 ≤ T ∧
  aLane P20 7 + 9 * (P20.ksLog + laneBits) + 15 * P20.ksLog + 12 ≤ T ∧
  1 ≤ spongeBlocks P20 ∧ spongeBlocks P20 ≤ 2 ^ P20.ksLog ∧ ksSplit P20 + 431 ≤ 2 ^ P20.ksLog ∧
  29 ≤ T ∧ P20.logN ≤ 64 ∧ 11 + pubLanes ≤ T ∧ P4 + 40 ≤ 8 * T ∧ P8 = 8 * openU P20 ∧
  P20.mainLevels.length ≤ (opens P20).length ∧
  P20.leafdecReads = 1 ∧ P20.nuRec = 19 ∧ P20.nuMain = 23 ∧ P20.logN = 20 ∧ typedPos P20 % 8 = 0 ∧
  busEndD P20.busDepth (mbP (typedPos P20)) + 72 + 144 * P20.tableRounds = phaseByte P20 .tape ∧
  RS.start.ent + nodeBytes * 2 ^ (P20.level ⟨.main, 0⟩).cap = typedPos P20

/-- `D`'s block and selector at `P20` (`tapeTails_eq`'s `hD`, `hds`). -/
theorem hDzT : Lvm.dBlock P20 = ⟨22, 0⟩ ∧ dSel P20 = 0 := ⟨by decide +kernel, by decide +kernel⟩

theorem phases47S_eqT (C : QCfg) : phases47S C = phases47 C := by
  rw [phases47S_eq]; unfold VF.phases47F phases47; rw [VF.tapeGadgetF_eq, VF.gkrGadgetF_eq]

/-- **What `harChkB` gives** (L-W's guard field `SF20.har`): the regions, and the B program's claim parts at Q_arith's
pointer are well formed in both shapes. -/
theorem harChk_sound {C : QCfg} {T : TData} {N : TypedV.TNat} (h : harChkB C T N = true) :
    TdOk T N ∧ claimsOkB C (qarithBParts C T (phases47 C (p2C C)).1 ((p2C C).adv (phases47 C (p2C C)).2)).1 = true := by
  simp only [harChkB, phases47S_eqT, Bool.and_eq_true] at h
  exact ⟨tdOk_of h.2, h.1⟩

theorem vk_cellsT {M : Mem} {x : List UInt8} {pb : ℕ} {vk : RecursionFast.Digest}
    (hpub : ∀ j < pubLanes, M.k (pb + j) = Lvm.NS.hdrLane x j) (hvk : (hdrOf x).vk = vk) :
    ∀ i < 4, M.k (pb + 1 + i) = (digestLanes vk).getD i 0 := by
  intro i hi
  have hj : 1 + i < pubLanes := by rw [pubLanes_eq]; omega
  have e1 : M.k (pb + 1 + i) = (Lvm.NS.hdrLanes x).getD (1 + i) 0 := by
    rw [Nat.add_assoc, hpub _ hj, Lvm.NS.hdrLanes, List.getD_eq_getElem?_getD, List.getElem?_map,
      List.getElem?_range hj, Option.map_some, Option.getD_some]
  have hv : (pubX x).vk = digestLanes vk := by rw [← hvk]; rfl
  have hl : i < (digestLanes vk).length := by simp only [digestLanes, List.length_map, List.length_range]; omega
  rw [e1, Lvm.NS.hdrLanes_eq_pubX, Pub.hdrLanes, hv]
  simp only [List.append_assoc, List.singleton_append]
  rw [Nat.add_comm, List.getD_append _ _ _ _ (by rw [List.length_cons]; omega), List.getD_cons_succ]

/-- Accumulators equal coordinate-wise (`LvmAccNodeLen.acc_eq_of`'s text; that module imports the bus refinement). -/
theorem acc_eq_ofT {a b : Acc} (ha : a.pt.length = accVars) (hb : b.pt.length = accVars)
    (hpt : ∀ i < accVars, a.pt.getD i 0 = b.pt.getD i 0) (hy : a.y = b.y) : a = b := by
  obtain ⟨pa, ya⟩ := a
  obtain ⟨pb, yb⟩ := b
  simp only at ha hb hpt hy
  subst hy
  congr
  refine List.ext_getElem (by rw [ha, hb]) fun i h1 h2 ↦ ?_
  have := hpt i (by omega)
  rwa [List.getD_eq_getElem _ _ h1, List.getD_eq_getElem _ _ h2] at this

theorem accC_eqT {M : Mem} {x : List UInt8} {pb : ℕ}
    (hpub : ∀ j < pubLanes, M.k (pb + j) = Lvm.NS.hdrLane x j) : Lvm.QAcc.accC M pb = (pubX x).accIn := by
  have hP : ∀ j a, j < pubLanes → a = pb + j → M.k a = Lvm.NS.hdrLane x j := fun j a hj ha => ha ▸ hpub j hj
  have hL : pubLanes = 747 := pubLanes_eq
  have hA : accVars = 43 := rfl
  refine acc_eq_ofT (by simp only [Lvm.QAcc.accC, List.length_map, List.length_range])
    (by rw [pubX]; simp [pubOf]) (fun i hi => ?_) ?_
  · rw [accIn_pt_lanes x hi]
    simp only [Lvm.QAcc.accC, List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range hi,
      Option.map_some, Option.getD_some]
    rw [hP (615 + 3 * i) _ (by omega) (by omega), hP (616 + 3 * i) _ (by omega) (by omega),
      hP (617 + 3 * i) _ (by omega) (by omega)]
  · rw [accIn_y_lanes x]
    simp only [Lvm.QAcc.accC]
    rw [hP (615 + 3 * accVars) _ (by omega) (by omega), hP (616 + 3 * accVars) _ (by omega) (by omega),
      hP (617 + 3 * accVars) _ (by omega) (by omega)]

end Lvm.Har
end

section
set_option autoImplicit false
namespace Lvm.Har
open RecursionFast Lvm Lvm.Loop Lvm.Loop.Build Lvm.Q1 Lvm.QAsm Lvm.QTyped Lvm.Typed Lvm.NS Lvm.T Lvm.ASM Lvm.QLink
  Lvm.Replay DM
open Lvm.M3 (lay26)
open Lvm.VEq (pubX)
open LeanVM.Protocol (Column)

/-- The child's trace bytes `Σ'` of a `C_rec` candidate. -/
abbrev sigC (qr : Column 19) : ByteArray := traceBytesB (decode P20 (wsC qr))

/-- **The memory facts of the `BITS` rows the HAR reads** (roll 7's `BVFacts` fields on the B program's memory
`memT`; L-D proves them from the typed `BITS` rows `bitsAux`): `s'`'s bits, `n'`'s bits and range, the positions of
both openings, the proof-of-work fields. -/
structure BVT (vk : RecursionFast.Digest) (x : List UInt8) (qm : Column CMain.nu20) (qr : Column 19) : Prop where
  sb : Lvm.Q1.SBitsS (memT x qm qr).k (sigIn cfg20).hd (bsB cfg20)
  nb : NBits (memT x qm qr).k ((sigIn cfg20).bn + 2) P20.logN
  n1 : 1 ≤ (pubOf vk (hdrOf x).cL (sigC qr)).n
  nN : (pubOf vk (hdrOf x).cL (sigC qr)).n ≤ 2 ^ P20.logN
  -- R11-E (M′, `S2GM`): the child has no `C_rec` opening, so B1's `posr` field (its positions) is gone and `posm`
  -- starts at `openU P20 + 15` (was `stackEndL … recLevels (openU P20 + 15) + 15`)
  posm : PosOk (cfgMain P20 (posBase cfg20) (pwBase cfg20)) (memT x qm qr) (sigC qr) 0 P20.mainLevels (openU P20 + 15)
  pw : ∀ k < (Lvm.QLink.opens P20).length, ((memT x qm qr).k (pwB cfg20 + k)).val.toNat < 2 ^ (64 - P20.grind)

end Lvm.Har
end

section
set_option autoImplicit false
namespace Lvm.Har
open RecursionFast Lvm Lvm.Loop Lvm.Loop.Build Lvm.Q1 Lvm.QAsm Lvm.QTyped Lvm.Typed Lvm.NS Lvm.T Lvm.ASM Lvm.QLink
  Lvm.Replay DM
open Lvm.M3 (lay26)
open Lvm.VEq (pubX)
open LeanVM.Protocol (Column)

theorem NT20_mbT : NT20.mbT = mbTOf cfg20 frz20 := by rw [NT20_eq]; simp only [tnatOf]
theorem tdata20_mbS : tdata20.mbS = (mbTOf cfg20 frz20).map M3.Tab.shape := by rw [tdata20_eq]; exact (tdataOf_mb _ _).1
theorem tdata20_mbR : tdata20.mbR = ((mbTOf cfg20 frz20).map (·.τ)).foldl max 0 := by
  rw [tdata20_eq]; exact (tdataOf_mb _ _).2.1
theorem tdata20_mbD : tdata20.mbD = log2Ceil (M3.pushLeavesR (mbTOf cfg20 frz20)) := by
  rw [tdata20_eq]; exact (tdataOf_mb _ _).2.2.1
theorem tdata20_mbFix : tdata20.mbFix = mbFixOf cfg20 := by rw [tdata20_eq]; exact (tdataOf_mb _ _).2.2.2


/-- **The opening at ν = 23, generic in the parameters** (the proof of part 4; M′ `S2GM`: `C_main`'s alone, roll 7's
`open_at` on `dOpenT`): from `openG`'s rows (gate on) on claims all on `C_main`, `dOpenT p (smallT p pub)` on the
cells' claims, from phase 8's start with `ok`, keeps `ok`, reads `Σ'` to its end and leaves no message pending. -/
theorem openT_atG (p : Params) (hnu : p.nuMain = 23) {c : Ctx} {M : Mem} {sig : ByteArray} {T : Nat}
    (hS : Streamed M sig T) (hg : M.k (pbB cfg20) = 1)
    (hlm : LayOk (cfgMain p (posBase cfg20) (pwBase cfg20)) T = true)
    (hop : p.mainLevels.length ≤ (Lvm.QLink.opens p).length)
    (hposm : PosOk (cfgMain p (posBase cfg20) (pwBase cfg20)) M sig 0 p.mainLevels (openU p + 15))
    (hend : 8 * stackEndL p.grind p.mainOod p.mainLevels (openU p + 15) = sig.size)
    (hpw : ∀ x < (Lvm.QLink.opens p).length, p.grind ≠ 0 → (M.k (pwB cfg20 + x)).val.toNat < 2 ^ (64 - p.grind))
    (cs : List CClaim) (hall : cs.all (·.com == .main) = true)
    (hwm : ClaimsWF p.nuMain (onCom cs .main) = true) {z one : Cell} (hzE : z.ty = .E) (hoE : one.ty = .E)
    (hz : z.val M = 0) (ho : one.val M = 1) {q : Ptr} (hq : 1 ≤ q.e) (pub : Pub) (mb : List Cell)
    (hσ : (1 + (mb.getD 18 default).val M) * (1 + (mb.getD 19 default).val M) =
      if decide (pub.n ≤ 2 ^ CMain.smallLogN20) then 1 else 0)
    (hzw : ∀ cc ∈ onCom cs .main, Lvm.QShape.ZWF z cc = true)
    (h : Lvm.QSig.Ok c M (openG (cfgMain p (posBase cfg20) (pwBase cfg20))
      (p.logN == 20 && p.nuMain == CMain.nu20) cs mb z one (kc (pbB cfg20))) q) :
    ∀ s : RS, pos s = 8 * openU p → s.ok = true →
      (TypedV.dOpenT p (TypedV.smallT p pub) (claimsT M cs) sig s).2.ok = true ∧
      (TypedV.dOpenT p (TypedV.smallT p pub) (claimsT M cs) sig s).2.ent = sig.size ∧
      (TypedV.dOpenT p (TypedV.smallT p pub) (claimsT M cs) sig s).2.msg = 0 := by
  intro s hs hok
  have hall' : (claimsT M cs).all (·.1 == .main) = true := by rw [claimsT, List.all_map]; exact hall
  have hrq : ({ s with ok := true && s.ok } : RS) = s := by cases s; rfl
  have e : TypedV.dOpenT p (TypedV.smallT p pub) (claimsT M cs) sig s =
      verifyStackedOpening p.mainLevels p.nuMain (Shape.onStackZsF (Shape.smallP p pub)
        ((onCom cs .main).map fun cc => ((cc.val M).2, Lvm.QShape.tailC M cc))) false p.grind p.mainOod sig s := by
    have h1 : TypedV.smallT p pub = Shape.smallP p pub := by simp only [TypedV.smallT, Shape.smallP, hnu]
    unfold TypedV.dOpenT Shape.onStackZsF
    rw [dm_bind, require_runW, hall', hrq, claimsT_main, h1, hnu, TypedV.onStackZBN_23]
  rw [e]
  simp only [openG] at h
  have hzp : (p.logN == 20 && p.nuMain == CMain.nu20) = true → p.logN = 20 ∧ p.nuMain = CMain.nu20 :=
    fun hz' => by simpa using hz'
  have hpwm : PwOk (cfgMain p (posBase cfg20) (pwBase cfg20)) M 0 (cfgMain p (posBase cfg20) (pwBase cfg20)).levels :=
    fun i hi hg0 => hpw (0 + i) (by simp only [cfgMain] at hi; omega) hg0
  have hs' : pos s = 8 * (cfgMain p (posBase cfg20) (pwBase cfg20)).U := hs
  have hend' : 8 * stackEndL (cfgMain p (posBase cfg20) (pwBase cfg20)).g (cfgMain p (posBase cfg20) (pwBase cfg20)).ood
      (cfgMain p (posBase cfg20) (pwBase cfg20)).levels ((cfgMain p (posBase cfg20) (pwBase cfg20)).U + 15) =
      sig.size := hend
  by_cases hz' : (p.logN == 20 && p.nuMain == CMain.nu20) = true
  · rw [if_pos hz'] at h
    have hsm : Shape.smallP p pub = decide (pub.n ≤ 2 ^ CMain.smallLogN20) := by
      obtain ⟨e1, e2⟩ := hzp hz'
      simp [Shape.smallP, e1, e2]
    rw [hsm]
    have hνZ : (cfgMain p (posBase cfg20) (pwBase cfg20)).nu = CMain.nu20 := (hzp hz').2
    have hwm' : ClaimsWF CMain.nu20 (onCom cs .main) = true := by rw [← (hzp hz').2]; exact hwm
    obtain ⟨o2, p2, m2⟩ := stackZ_run _ _ mb z one _ _ hσ hνZ hwm' hzw hS hlm hz ho hzE hoE (gate_val cfg20 hg) rfl
      hposm hpwm hq h s hs'
    simp only [cfgMain] at o2 p2 m2 hend'
    refine ⟨o2.trans hok, ?_, m2⟩
    simp only [pos] at p2
    omega
  · rw [if_neg hz'] at h
    have hsm : Shape.smallP p pub = false := by
      have : (p.logN == 20 && p.nuMain == CMain.nu20) = false := by simpa using hz'
      simp only [Shape.smallP]
      rw [this, Bool.false_and]
    rw [hsm]
    simp only [Shape.onStackZsF, Bool.false_eq_true, if_false, List.map_map]
    rw [show ((fun x : BlockClaim × FE => x.1.onStack) ∘
      fun cc : CClaim => ((CClaim.val M cc).2, Lvm.QShape.tailC M cc)) = fun cc => (cc.val M).2.onStack from rfl]
    obtain ⟨o2, p2, m2⟩ := stack_run _ _ z one _ hS (by simp only [StackOk, hlm, Bool.true_and]; exact hwm) hz ho
      hzE hoE (gate_val cfg20 hg) rfl
      hposm hpwm hq h s hs'
    simp only [cfgMain] at o2 p2 m2 hend'
    refine ⟨o2.trans hok, ?_, m2⟩
    simp only [pos] at p2
    omega

/-- **Part 4: the opening at ν = 23, both shapes** (R11-E, M′: restated on the one-commitment `openG`; B1's
`hlr`, `hposr`, `hwr` (`C_rec`'s layout, positions and claims) are gone, `C_main`'s opening starts at `openU P20`;
R11-N: `hall`, every claim on `C_main`, which `dOpenT` requires) (roll 7's `open_at` on `dOpenT`): from `openG`'s
rows (gate on), `dOpenT P20 (smallT P20 pub)` on the cells' claims, from phase 8's start with `ok`, keeps `ok`, reads
`Σ'` to its end and leaves no message pending. -/
theorem openT_at {c : Ctx} {M : Mem} {sig : ByteArray} {T : Nat} (hS : Streamed M sig T)
    (hg : M.k (pbB cfg20) = 1)
    (hlm : LayOk (cfgMain P20 (posBase cfg20) (pwBase cfg20)) T = true)
    (hop : P20.mainLevels.length ≤ (Lvm.QLink.opens P20).length)
    (hposm : PosOk (cfgMain P20 (posBase cfg20) (pwBase cfg20)) M sig 0 P20.mainLevels (openU P20 + 15))
    (hend : 8 * stackEndL P20.grind P20.mainOod P20.mainLevels (openU P20 + 15) = sig.size)
    (hpw : ∀ x < (Lvm.QLink.opens P20).length, P20.grind ≠ 0 → (M.k (pwB cfg20 + x)).val.toNat < 2 ^ (64 - P20.grind))
    (cs : List CClaim) (hall : cs.all (·.com == .main) = true)
    (hwm : ClaimsWF P20.nuMain (onCom cs .main) = true) {z one : Cell} (hzE : z.ty = .E) (hoE : one.ty = .E)
    (hz : z.val M = 0) (ho : one.val M = 1) {q : Ptr} (hq : 1 ≤ q.e) (pub : Pub) (mb : List Cell)
    (hσ : (1 + (mb.getD 18 default).val M) * (1 + (mb.getD 19 default).val M) =
      if decide (pub.n ≤ 2 ^ CMain.smallLogN20) then 1 else 0)
    (hzw : ∀ cc ∈ onCom cs .main, Lvm.QShape.ZWF z cc = true)
    (h : Lvm.QSig.Ok c M (openG (cfgMain P20 (posBase cfg20) (pwBase cfg20))
      (P20.logN == 20 && P20.nuMain == CMain.nu20) cs mb z one (kc (pbB cfg20))) q) :
    ∀ s : RS, pos s = 8 * openU P20 → s.ok = true →
      (TypedV.dOpenT P20 (TypedV.smallT P20 pub) (claimsT M cs) sig s).2.ok = true ∧
      (TypedV.dOpenT P20 (TypedV.smallT P20 pub) (claimsT M cs) sig s).2.ent = sig.size ∧
      (TypedV.dOpenT P20 (TypedV.smallT P20 pub) (claimsT M cs) sig s).2.msg = 0 :=
  openT_atG P20 rfl hS hg hlm hop hposm hend hpw cs hall hwm hzE hoE hz ho hq pub mb hσ hzw h

/-- **What phases 4–7's output cells are** (generic in the configuration and the pointer: roll 7's `claims_at`
steps; at the instance a `simp` on `phases47 cfg20 (p2C cfg20)` is slow): the tape's 25 values, `KS`'s 25 lanes,
`logN` point cells, and `KS`'s GKR slices are the stream's. -/
theorem p47_out_facts (C : QCfg) {c : Ctx} {M : Mem} {sig : ByteArray} {T : Nat} {p2 : Ptr} {o : P47Out}
    (h47 : Lvm.QSig.Ok c M (phases47 C) p2) (ho47 : (phases47 C p2).1 = o) (hS : Streamed M sig T)
    (hlayk : layOk (C.p.ksLog - 4) = true) (hqk : 5 ≤ aLane C.p 6) (hT : gkrEnd (C.p.ksLog - 4) (aLane C.p 6) ≤ T) :
    o.v.length = 25 ∧ o.vk.length = 25 ∧ o.r.length = C.p.logN ∧
      (o.kko.vals M).slices = slAt sig (gkrEnd (C.p.ksLog - 4) (aLane C.p 6) - 192) := by
  have hO : (phases47 C p2).1 = o := ho47
  simp only [phases47, bind_apply, pure_apply] at hO
  have ekko := congrArg P47Out.kko hO
  have ev : o.v.length = 25 := by rw [← hO]; simp only [List.length_map, List.length_range]
  have evk : o.vk.length = 25 := by rw [← hO]; simp only [List.length_map, List.length_range]
  have erl : o.r.length = C.p.logN := by rw [← hO]; simp only [List.length_map, List.length_range]
  dsimp only at ekko
  clear hO
  obtain ⟨hh, -⟩ := h47
  simp only [phases47] at hh
  rw [hold_bind] at hh; obtain ⟨-, hh⟩ := hh
  rw [hold_bind] at hh; obtain ⟨-, hh⟩ := hh
  rw [hold_bind] at hh; obtain ⟨-, hh⟩ := hh
  rw [hold_bind] at hh; obtain ⟨-, hh⟩ := hh
  rw [hold_bind] at hh; obtain ⟨-, hh⟩ := hh
  rw [hold_bind] at hh; obtain ⟨-, hh⟩ := hh
  rw [hold_bind] at hh; obtain ⟨-, hh⟩ := hh
  rw [hold_bind] at hh; obtain ⟨-, hh⟩ := hh
  rw [hold_bind] at hh; obtain ⟨-, hh⟩ := hh
  rw [hold_bind] at hh; obtain ⟨hhGk, -⟩ := hh
  have sK := gkrGadget_slices hlayk hqk hS hT hhGk
  rw [ekko] at sK
  exact ⟨ev, evk, erl, sK⟩

/-- **`claimsOkB`'s parts** (by rewriting a generic tuple: a `simp` on the instance's claim list is slow; M′: every
claim on `C_main`). -/
theorem claimsOkB_parts {C : QCfg} {z : Cell} {a b c d e f : List CClaim}
    (h : claimsOkB C (z, a, b, c, d, e, f) = true) :
    (a ++ b ++ (c ++ d) ++ e ++ f).all (·.com == .main) = true ∧
      ClaimsWF C.p.nuMain (onCom (a ++ b ++ (c ++ d) ++ e ++ f) .main) = true ∧
      (∀ cc ∈ onCom (a ++ b ++ (c ++ d) ++ e ++ f) .main, Lvm.QShape.ZWF z cc = true) ∧
      a.all noDRB = true ∧ b.all noDRB = true ∧ (d ++ e ++ f).all noDRB = true := by
  simp only [claimsOkB, csB, Bool.and_eq_true] at h
  obtain ⟨⟨⟨h1, h2⟩, h3⟩, h4⟩ := h
  simp only [List.all_append, Bool.and_eq_true] at h4
  obtain ⟨⟨⟨⟨h0, h5⟩, h6⟩, h7⟩, h8⟩ := h4
  exact ⟨h1, h2, List.all_eq_true.mp h3, h0, h5, by simp only [List.all_append, h6, h7, h8, Bool.and_self]⟩

/-- `M3.real`'s table claims on a native instance's tables. -/
theorem m3_tableClaimsT (N : TypedV.TNat) (p : Params) (pub : Pub) (ev : List (List FE × List FE)) :
    (N.m3 p).tableClaims pub ev = M3.tableClaimsR (M3.sumcheckTabs N.mbT) ev := rfl

/-- `M3.real`'s `KS` block on a native instance. -/
theorem m3_ksBlockT (N : TypedV.TNat) (p : Params) : (N.m3 p).ksBlock = ⟨p.ksLog + slotLog, (layout0 p).ks⟩ := rfl

/-- Q_arith's pointer (a rewrite: a definitional check would run Q_link's and Q_sig's builders). -/
theorem p2_eqT : p2 (lay cfg20) (sigIn cfg20) (nK cfg20) 0 = p2C cfg20 := by
  unfold p2 p2P p1P p0 p2C p1C
  rw [show cfg20.p = P20 from rfl]

end Lvm.Har
end

-- ===== from `LvmE2QHarFacts` =====

section
set_option autoImplicit false
namespace Lvm.E2Q
open RecursionFast Lvm Lvm.T Lvm.Loop Lvm.Loop.Build Lvm.QLink Lvm.QAsm Lvm.NS Lvm.Typed Lvm.QTyped
open Lvm.VEq (pubXF)
open LeanVM.Protocol (Column)

/-- **The child's trace bytes `Σ'`** of a `C_rec` candidate at S2GF. -/
abbrev sigCF (qr : Column 19) : ByteArray := traceBytesB (decode P20F (wsC qr))

/-- `|Σ'| = hashedLen P20F` on a linked stream. -/
theorem sigCF_size {qr : Column 19} (hL : LaneLink P20F (wsC qr)) : (sigCF qr).size = hashedLen P20F := by
  rw [sigCF, traceBytesB_decode streamOk_P20F hL, Lvm.Har.sigma_sizeT hL.size]

/-- **The node memory streams `Σ'`** (`streamed_child` at `cfgF20`, `T = streamLanes P20F = 73,001`). -/
theorem streamedF {M : Mem} {qr : Column 19}
    (hst : ∀ j < 2 ^ (lay cfgF20).m, M.k ((lay cfgF20).sb + j) = laneK (wsC qr) j) (hL : LaneLink P20F (wsC qr)) :
    Lvm.Q1.Streamed M (sigCF qr) (streamLanes P20F) := by
  have hh : hashedLen P20F = 584008 := spongeBlocks_P20F.2
  have hw : (wsC qr).length = 17 * 2 ^ 14 := by rw [wsC, wsOf, List.length_map, List.length_range]
  have h := Lvm.Har.streamed_child cfgF20 streamOk_P20F hL hst (T := streamLanes P20F)
    (by rw [streamLanes, hh]; decide) (by rw [show cfgF20.p = P20F from rfl, streamLanes]; omega)
    (by rw [streamLanes, hh, hw]; norm_num)
  rwa [show cfgF20.p = P20F from rfl] at h

/-- **`acc_in` read off its `PUB` cells** at `n` coordinates (three lanes per scalar from `pb + 615`). -/
def accCA (n : ℕ) (M : Mem) (pb : ℕ) : Acc :=
  ⟨(List.range n).map fun i => ⟨M.k (pb + 615 + 3 * i), M.k (pb + 615 + 3 * i + 1), M.k (pb + 615 + 3 * i + 2)⟩,
    ⟨M.k (pb + 615 + 3 * n), M.k (pb + 615 + 3 * n + 1), M.k (pb + 615 + 3 * n + 2)⟩⟩

theorem accCA_accVars (M : Mem) (pb : ℕ) : accCA accVars M pb = Lvm.QAcc.accC M pb := rfl

/-- `PUB` cell `pb + 615 + 3i + t` is the header's word at stream byte `headerAt (offAcc + 24 i) + 8 t`. -/
theorem pub_acc_lane {M : Mem} {x : List UInt8} {pb : ℕ}
    (hpub : ∀ j < pubLanesX accVF, M.k (pb + j) = hdrLane x j) {i t : ℕ} (hi : i ≤ accVF) (ht : t < 3) :
    M.k (pb + 615 + 3 * i + t) = kAt (Lvm.VEq.sigOfX x) (headerAt (offAcc + eBytes * i) + 8 * t) := by
  have hj : 615 + 3 * i + t < pubLanesX accVF := by
    unfold pubLanesX; rw [show accVF = 44 from rfl] at hi ⊢; omega
  rw [show pb + 615 + 3 * i + t = pb + (615 + 3 * i + t) by omega, hpub _ hj, hdrLane_eq_kAt]
  congr 1
  simp only [headerAt, offAcc, eBytes, sigBytes]
  omega

/-- **`acc_in` from `PUB` at S2GF** is the statement's (`accVF = 44` coordinates, `pubLanesX 44 = 750` lanes). -/
theorem accCA_pubXF {M : Mem} {x : List UInt8} {pb : ℕ}
    (hpub : ∀ j < pubLanesX accVF, M.k (pb + j) = hdrLane x j) : accCA accVF M pb = (pubXF x).accIn := by
  have e : (pubXF x).accIn = ⟨(List.range accVF).map fun i =>
      feAt (Lvm.VEq.sigOfX x) (headerAt (offAcc + eBytes * i)),
      feAt (Lvm.VEq.sigOfX x) (headerAt (offAcc + eBytes * accVF))⟩ := rfl
  rw [e]
  unfold accCA
  congr 1
  · refine List.map_congr_left fun i hi => ?_
    have hi' : i ≤ accVF := Nat.le_of_lt (List.mem_range.mp hi)
    have h0 := pub_acc_lane hpub hi' (t := 0) (by omega)
    have h1 := pub_acc_lane hpub hi' (t := 1) (by omega)
    have h2 := pub_acc_lane hpub hi' (t := 2) (by omega)
    rw [Nat.add_zero, Nat.mul_zero, Nat.add_zero] at h0
    rw [h0, h1, h2]
    rfl
  · have h0 := pub_acc_lane hpub (le_refl accVF) (t := 0) (by omega)
    have h1 := pub_acc_lane hpub (le_refl accVF) (t := 1) (by omega)
    have h2 := pub_acc_lane hpub (le_refl accVF) (t := 2) (by omega)
    rw [Nat.add_zero, Nat.mul_zero, Nat.add_zero] at h0
    rw [h0, h1, h2]
    rfl

end Lvm.E2Q
end

section
set_option autoImplicit false
namespace Lvm.E2Q
open RecursionFast Lvm Lvm.T Lvm.Loop Lvm.Loop.Build Lvm.QLink Lvm.QAsm Lvm.NS Lvm.Typed Lvm.QTyped
open Lvm.VEq (pubXF)
open LeanVM.Protocol (Column)

/-- **V's proof-of-work checks at S2GF** on a good pair's memory (`powOk_of_blks` at `cfgF20`, the pair's words). -/
theorem powOkF {F : TFrz} {Q : Program} {tl : Typed.Lay} {N : TypedV.TNat} (S : NodeGF F Q tl N)
    (H : THypX (N.inst Q tl)) {x : List UInt8} {qm : Column CMain.nu20} {qr : Column 19}
    (hG : E2V.GoodTF (N.inst Q tl) H x qm qr) {pw : List (ℕ × ℕ)} {d : Array (Ty × ℕ × ℕ)}
    (hl : tl = (mkLayD Q (specQF cfgF20 Q pw) d).1) {sig : ByteArray} {T : ℕ}
    (hS : Lvm.Q1.Streamed (memF (N.inst Q tl) x qm qr) sig T) {L : List (ℕ × ℕ)} (hL : ∀ a ∈ L, a ∈ pw)
    (hpw : ∀ a ∈ L, a.1 + 2 < T ∧ a.2 ≤ 64) : Lvm.Q1.PowOkV (feAt sig) L :=
  powOk_of_blks cfgF20 hl S.st.hlay (one_zTX H pubXF) hG.1.1.1.1 hS hL hpw

/-- `PUB`'s first `pubLanes` cells from S2GF's input map (`pubLanesX 44 = 750 ≥ 747`; roll 11's `PUB` glue,
`Lvm.Har.vk_cellsT`, reads them). -/
theorem pub747F {M : Mem} {vk : RecursionFast.Digest} {x : List UInt8} {qm : Column CMain.nu20} {qr : Column 19}
    (hin : InMapMB (spongeBlocks P20F) (pubLanesX accVF) (lay cfgF20) (sigIn cfgF20) M vk x qm qr) :
    ∀ j < pubLanes, M.k ((sigIn cfgF20).flag + j) = hdrLane x j :=
  fun j hj ↦ hin.pub j (lt_of_lt_of_le hj (by decide))

end Lvm.E2Q
end

-- ===== from `LvmE2QTypedPhase` =====

section
set_option autoImplicit false
namespace Lvm.E2Q
open Lvm Lvm.Loop Lvm.Loop.Build Lvm.QTyped Lvm.Q1 DM Lvm.Har
open Lvm.TypedV (TNat)
section Pub
open Lvm.QAcc

theorem range_splitA (F : Nat → FK) (accV : Nat) :
    (List.range (pubLanesX accV)).map F = [F 0] ++ ((List.range 4).map fun i => F (1 + i)) ++
      ((List.range 4).map fun i => F (5 + i)) ++ ((List.range 4).map fun i => F (9 + i)) ++ [F 13] ++
      ((List.range 4).map fun i => F (14 + i)) ++ ((List.range 597).map fun i => F (18 + i)) ++
      ((List.range (3 * (accV + 1))).map fun i => F (615 + i)) := by
  rw [show pubLanesX accV = 1 + 4 + 4 + 4 + 1 + 4 + 597 + 3 * (accV + 1) by unfold pubLanesX; omega]
  simp only [map_range_add, List.map_map, Function.comp_def, List.append_assoc]
  simp only [List.range_one, List.map_cons, List.map_nil, Nat.add_zero, Nat.zero_add, List.cons_append,
    List.nil_append, Nat.add_assoc, Nat.reduceAdd]

/-- **The child's `PUB` lanes at `accV` variables** are its stream's lanes from `11` (`pubOf_hdrLanes` with
`acc_in` of `accV + 1` scalars), except the key lanes `1 … 4`. -/
theorem pubOfA_hdrLanesS (accV : Nat) (vk c : Vector UInt8 32) (sig : ByteArray) :
    (Lvm.pubOfA accV vk c sig).hdrLanes = (List.range (pubLanesX accV)).map (hdrLaneS vk sig) := by
  have pos (i : Nat) (h : ¬ (1 ≤ i ∧ i < 5)) : hdrLaneS vk sig i = kAt sig (8 * (11 + i)) := by
    simp only [hdrLaneS, h, ite_false]
  have e0 : (⟨(Lvm.pubOfA accV vk c sig).b.toUInt64⟩ : FK) = hdrLaneS vk sig 0 := by
    rw [pos 0 (by omega)]
    simp only [Lvm.pubOfA, pubOf, kAt, Nat.toUInt64, UInt64.ofNat_toNat]; rfl
  have e1 : (Lvm.pubOfA accV vk c sig).vk = (List.range 4).map fun i => hdrLaneS vk sig (1 + i) := by
    show digestLanes vk = _
    conv_lhs => rw [list_eq_range_getD (digestLanes vk)]
    rw [show (digestLanes vk).length = 4 by simp [digestLanes]]
    apply List.map_congr_left; intro i hi
    simp only [List.mem_range] at hi
    simp [hdrLaneS, show 1 ≤ 1 + i ∧ 1 + i < 5 by omega]
  have seg (o k n : Nat) (ho : 5 ≤ k) (hk : headerAt o = 8 * (11 + k)) :
      ((List.range n).map fun i => kAt sig (headerAt o + 8 * i)) =
        (List.range n).map fun i => hdrLaneS vk sig (k + i) := by
    apply List.map_congr_left; intro i _
    rw [pos _ (by omega), hk, show 8 * (11 + k) + 8 * i = 8 * (11 + (k + i)) by ring]
  have e2 : (Lvm.pubOfA accV vk c sig).cL = (List.range 4).map fun i => hdrLaneS vk sig (5 + i) :=
    seg 48 5 4 (by omega) rfl
  have e3 : (Lvm.pubOfA accV vk c sig).s = (List.range 4).map fun i => hdrLaneS vk sig (9 + i) :=
    seg 80 9 4 (by omega) rfl
  have e4 : (⟨(Lvm.pubOfA accV vk c sig).n.toUInt64⟩ : FK) = hdrLaneS vk sig 13 := by
    rw [pos 13 (by omega)]
    simp only [Lvm.pubOfA, pubOf, kAt, Nat.toUInt64, UInt64.ofNat_toNat]; rfl
  have e5 : (Lvm.pubOfA accV vk c sig).h = (List.range 4).map fun i => hdrLaneS vk sig (14 + i) :=
    seg 120 14 4 (by omega) rfl
  have e6 : (Lvm.pubOfA accV vk c sig).sigLeaf = (List.range 597).map fun i => hdrLaneS vk sig (18 + i) := by
    simp only [Lvm.pubOfA, pubOf]
    rw [show sigBytes / 8 = 597 from rfl]
    exact seg 152 18 597 (by omega) rfl
  have hpos : ∀ i, headerAt (offAcc + eBytes * i) = 8 * (626 + 3 * i) := by
    intro i; simp only [headerAt, offAcc, eBytes, sigBytes]; omega
  have e7 : ((Lvm.pubOfA accV vk c sig).accIn.pt ++ [(Lvm.pubOfA accV vk c sig).accIn.y]).flatMap FE.lanes =
      (List.range (3 * (accV + 1))).map fun i => hdrLaneS vk sig (615 + i) := by
    have : (Lvm.pubOfA accV vk c sig).accIn.pt ++ [(Lvm.pubOfA accV vk c sig).accIn.y] =
        (List.range (accV + 1)).map fun j => feAt sig (8 * (626 + 3 * j)) := by
      simp only [Lvm.pubOfA, hpos]
      rw [List.range_succ, List.map_append, List.map_singleton]
    rw [this, flatMap_feAt sig 626 (accV + 1)]
    apply List.map_congr_left; intro i _
    rw [pos _ (by omega), show 11 + (615 + i) = 626 + i by omega]
  rw [range_splitA]
  simp only [Pub.hdrLanes, List.append_assoc]
  rw [e0, e1, e2, e3, e4, e5, e6, e7]

end Pub
end Lvm.E2Q
end

section
set_option autoImplicit false
namespace Lvm.E2Q
open Lvm Lvm.Loop Lvm.Loop.Build Lvm.QTyped Lvm.Q1 DM Lvm.Har
open Lvm.TypedV (TNat)
section
variable {c : Ctx} {M : Mem} {sig : ByteArray} {T : Nat}

theorem wGPX_eq (P : Nat) : wGPX P = P + 4056 := by simp only [wGPX, zAbcPX, zRPX, tX]

/-- **The coordinate-split zerocheck replayed** (soundness direction): wherever `zeroGX`'s rows hold and assert
(gate on), `dZeroX` from any state at position `P` with `ok` keeps `ok`, ends at `wGPX P`; `r_x` is the output's
first list's values, the six values the second's. -/
theorem zeroGX_replays (hS : Streamed M sig T) {z g : Cell} (hz : z.val M = 0)
    (hg : g.val M = 1) {P : Nat} (hP : P % 8 = 0) (hT : wGPX P + 40 ≤ 8 * T) (ptr : Ptr) :
    Replays c M sig TypedV.dZeroX (zeroGX z g P) ptr P (wGPX P) fun v t =>
      v.1 = vs M t.1 ∧ v.2 = vs M t.2 ∧ t.1.length = 20 ∧ (∀ x ∈ t.1, x.ty = .E) ∧ t.2.length = 6 ∧
        (∀ x ∈ t.2, x.ty = .E) := by
  rw [wGPX_eq] at hT ⊢
  refine z_replays_of ?_
  unfold zeroGX
  refine z_soundAt_bind (z_soundAt_of (ldEsP_sound hS ((P + 40) / 8) 9 tX fun i hi => by simp only [tX] at hi; omega) _)
    fun tb htb => ?_
  refine z_soundAt_bind (z_ldE_at hS (a := (P + 72 * tX + 40) / 8) (by simp only [tX]; omega) _) fun om hom => ?_
  refine z_soundAt_getPtr ?_
  refine z_soundAt_bind (z_scQ3_at hS tX _ tb.1 z _ ((List.range tX).map fun i => feAt sig (P + 40 + 72 * i))
    (by simp) (fun i hi => by rw [htb.2 i hi, QB.getD_map_range _ _ hi]; congr 1; omega)
    (by simp only [zRPX, tX]; omega)) fun fin hfin => ?_
  refine z_soundAt_bind (z_soundAt_of (z_ldEs_soundE hS ((zAbcPX P + 40) / 8) 3 6 fun i hi => by
    simp only [zAbcPX, zRPX, tX]; omega) _) fun v hv => ?_
  refine z_soundAt_bind (z_soundAt_of (soundG_aspec (QB.aspec_mulAdd .E _ _ _)) _) fun t0 ht0 => ?_
  refine z_soundAt_bind (z_soundAt_of (soundG_aspec (QB.aspec_mulAdd .E _ _ _)) _) fun r0 hr0 => ?_
  refine z_soundAt_bind (z_soundAt_of (soundG_aspec (QB.aspec_mulAdd .E _ _ _)) _) fun p11 hp11 => ?_
  refine z_soundAt_bind (z_soundAt_of (soundG_aspec (QB.aspec_lin _ _ _ _ _)) _) fun t1 ht1 => ?_
  refine z_soundAt_bind (z_soundAt_of (soundG_aspec (QB.aspec_mulAdd .E _ _ _)) _) fun t2 ht2 => ?_
  refine z_soundAt_bind (z_soundAt_of (soundG_aspec (QB.aspec_mulAdd .E _ _ _)) _) fun r1 hr1 => ?_
  refine z_soundAt_bind (z_soundAt_of (soundG_aspec (QB.aspec_mulAdd .E _ _ _)) _) fun t ht => ?_
  refine z_soundAt_bind (z_soundAt_of (soundG_aspec (QB.aspec_assertEq _ _ _)) _) fun _ hA => ?_
  refine z_soundAt_pure ?_
  intro s hs hok
  simp only [pos] at hs
  simp only [TypedV.dZeroX, Q1.bind_run, Q1.samples_run sig _ s (by decide : 1 ≤ Lvm.Typed.xVars), Q1.sampleE_run,
    Q1.pure_run, Q1.readEs_run, Lvm.Har.require_run, hs, hok]
  have homv : om.val M = feAt sig (P + 72 * tX + 40) := by rw [hom]; congr 1; simp only [tX]; omega
  rw [hz] at hfin
  obtain ⟨h1, h2⟩ := hfin ⟨P + 72 * (tX + 1), 0, true⟩ rfl (by simp only [zRPX]; omega)
  have hst := congrArg Prod.snd (QB.sumcheck_run 3 (by decide) sig
    ((List.map (fun i => feAt sig (P + 40 + 72 * i)) (List.range tX)).map some) 0 ⟨P + 72 * (tX + 1), 0, true⟩ rfl)
  have hlen := sumcheck_len 0 3 (by decide)
    ((List.map (fun i => feAt sig (P + 40 + 72 * i)) (List.range tX)).map some) sig ⟨P + 72 * (tX + 1), 0, true⟩ rfl
  have hent : P + 72 * Lvm.Typed.xVars + 72 + 0 = P + 72 * (tX + 1) := by simp only [tX, Lvm.Typed.xVars]
  have hans : P + 72 * Lvm.Typed.xVars + 40 + 0 = P + 72 * tX + 40 := by simp only [tX, Lvm.Typed.xVars]
  simp only [hent, hans] at *
  generalize sumcheck 0 3 _ sig _ = R at h1 h2 hst hlen ⊢
  rw [hst]
  have hab : scalarsAt (feAt sig) (P + 72 * (tX + 1) + QB.entB (3 - 1) * tX + 0 + 40) 6 = vs M v := by
    rw [hv.1, scalarsAt]
    refine List.map_congr_left fun i _ => congrArg _ ?_
    simp only [zAbcPX, zRPX, tX, QB.entB]; omega
  simp only [List.length_map, List.length_range] at hst hlen ⊢
  rw [hab]
  simp only [z_getD_vs v z, hz] at ht0 hr0 hp11 ht1 ht2 hr1
  have hfa := (QB.gate_eq_iff hg _ _).mp hA.2
  refine ⟨?_, ?_, ?_, rfl, ?_, ?_, ?_, hv.2⟩
  · rw [Bool.and_true, QB.FE.beq_iff, ← h1, hfa, ht.1, hr1.1, ht2.1, ht1.1, hp11.1, hr0.1, ht0.1, homv, ofK_zero]
    ring
  · simp only [pos, QB.entB, tX]
  · apply List.ext_getElem (by simp [vs, hlen])
    intro i h1' h2'
    simp only [vs, List.map_map, List.getElem_map, List.getElem_range, Function.comp_apply, Cell.val_E]
    rw [h2 i (by simpa [hlen] using h1'), List.getD_eq_getElem _ _ h1']
  · simp
  · intro x hx
    simp only [List.mem_map, List.mem_range] at hx
    obtain ⟨i, _, rfl⟩ := hx
    rfl
  · simpa [vs] using congrArg List.length hv.1

end
end Lvm.E2Q
end

section
set_option autoImplicit false
namespace Lvm.E2Q
open Lvm Lvm.Loop Lvm.Loop.Build Lvm.QTyped Lvm.Q1 DM Lvm.Har
open Lvm.TypedV (TNat)
section PubEval
open Lvm.QAcc Lvm.QSig

/-- `pubEval` of the child's `PUB` lanes at `accV` (`pubEval_child` at `pubLanesX accV` lanes). -/
theorem pubEval_childA (accV : Nat) {M : Mem} {sig : ByteArray} {T : Nat} (hS : Streamed M sig T)
    (hT : 11 + pubLanesX accV ≤ T) {vk : Vector UInt8 32} (c : Vector UInt8 32) {vkc : Nat}
    (hvk : ∀ i < 4, M.k (vkc + i) = (digestLanes vk).getD i 0) (pt : List FE)
    (hn : pubLanesX accV ≤ 2 ^ pt.length) :
    M3.pubEval (Lvm.pubOfA accV vk c sig).hdrLanes pt =
      ∑ i ∈ Finset.range (pubLanesX accV), eqW pt i * FE.ofK (pubLane M 11 vkc i) := by
  rw [M3.pubEval_eq, mle_eq_sum, pubOfA_hdrLanesS]
  obtain ⟨m, hm⟩ : ∃ m, 2 ^ pt.length = pubLanesX accV + m := ⟨_, (Nat.add_sub_cancel' hn).symm⟩
  rw [hm, Finset.sum_range_add]
  have h0 : ∑ x ∈ Finset.range m, eqW pt (pubLanesX accV + x) *
      FE.ofK (M3.pubCell ((List.range (pubLanesX accV)).map (hdrLaneS vk sig)) (pubLanesX accV + x)) = 0 := by
    apply Finset.sum_eq_zero; intro x _
    simp [M3.pubCell, List.getD_eq_getElem?_getD, ofK_zero]
  rw [h0, add_zero]
  apply Finset.sum_congr rfl; intro i hi
  rw [Finset.mem_range] at hi
  refine congrArg (fun x => eqW pt i * FE.ofK x) ?_
  simp only [M3.pubCell, List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range hi,
    Option.map_some, Option.getD_some, hdrLaneS, pubLane]
  split_ifs with h
  · rw [hvk _ (by omega), List.getD_eq_getElem?_getD]
  · rw [hS _ (by omega)]

/-- The child's `acc_in` at `accV` coordinates at the stream lanes `accLane`. -/
theorem pubOfA_accIn (accV : Nat) (vk cL : Vector UInt8 32) (sig : ByteArray) :
    (Lvm.pubOfA accV vk cL sig).accIn.y = feAt sig (8 * accLane accV) ∧
      (Lvm.pubOfA accV vk cL sig).accIn.pt = (List.range accV).map fun i => feAt sig (8 * accLane i) := by
  have hacc : ∀ i, headerAt (offAcc + eBytes * i) = 8 * accLane i := by
    intro i; simp only [headerAt, offAcc, eBytes, sigBytes, accLane]; omega
  refine ⟨?_, ?_⟩
  · show feAt sig (headerAt (offAcc + eBytes * accV)) = _; rw [hacc]
  · show (List.range accV).map (fun i => feAt sig (headerAt (offAcc + eBytes * i))) = _
    simp only [hacc]

end PubEval
end Lvm.E2Q
end

section
set_option autoImplicit false
namespace Lvm.E2Q
open Lvm Lvm.Loop Lvm.Loop.Build Lvm.QTyped Lvm.Q1 DM Lvm.Har
open Lvm.TypedV (TNat)
section
variable {c : Ctx} {M : Mem} {sig : ByteArray} {T : Nat}

/-- **`virtGX`'s value is V_S's `virtEF`** at `r_y` on the child's `PUB` at `acc_in` of `accV` coordinates
(`virtG_spec` at `pubLanesX accV` lanes). -/
theorem virtGX_spec (accV : Nat) (vk cL : Vector UInt8 32) (hS : Streamed M sig T)
    (hH : 11 + pubLanesX accV ≤ T) (hA : pubLanesX accV ≤ 2 ^ 10) {z o : Cell}
    (hz : z.val M = 0) (ho : o.val M = 1) (hzE : z.ty = .E) (hoE : o.ty = .E) {Td : TData} {N : TNat}
    (htd : TdOk Td N) {pb : Nat} (hvk : ∀ i < 4, M.k (pb + 1 + i) = (digestLanes vk).getD i 0) (ry : List Cell)
    (hry : ry.length = 21) (hryE : ∀ x ∈ ry, x.ty = .E) (q : Ptr)
    (h : SegsHold c M q (virtGX z o Td pb (pubLanesX accV) ry q).2) :
    (virtGX z o Td pb (pubLanesX accV) ry q).1.val M =
      TypedV.virtEF N (Lvm.pubOfA accV vk cL sig) (vs M ry) := by
  have hone : M.e o.n = 1 := by rw [← ho]; rcases o with ⟨τ, n⟩; simp only at hoE; subst hoE; rfl
  have hal : ∀ i, (ry.getD i z).ty = .E := fun i => by
    rw [List.getD_eq_getElem?_getD]
    cases h : ry[i]? with
    | none => exact hzE
    | some y => exact hryE y (List.mem_of_getElem? h)
  have hvl : (vs M ry).length = 21 := by simp [vs, hry]
  have hpt : (List.range 10).map (fun i => (ry.getD i z).val M) = (vs M ry).take 10 := by
    apply List.ext_getElem (by simp [hvl])
    intro i h1 h2
    simp only [List.length_map, List.length_range] at h1
    rw [List.getElem_map, List.getElem_range, List.getElem_take, z_getD_vs, List.getD_eq_getElem _ _ (by omega)]
  have hqp : ∀ p : Ptr, z_HoldAt c M (Lvm.QAcc.qpub (fun i => ry.getD i z) z o 10 11 (pb + 1) (pubLanesX accV)) p
      fun v => v.val M = M3.pubEval (Lvm.pubOfA accV vk cL sig).hdrLanes ((vs M ry).take 10) := fun p h => by
    refine (Lvm.QAcc.qpub_spec hz hal hone hA h).trans ?_
    rw [hpt, pubEval_childA accV hS hH cL hvk _ (by rw [List.length_take, hvl]; exact hA)]
  have key : z_HoldAt c M (virtGX z o Td pb (pubLanesX accV) ry) q fun w => w.val M =
      TypedV.hiW (vs M ry) 10 Td.pub * M3.pubEval (Lvm.pubOfA accV vk cL sig).hdrLanes ((vs M ry).take 10) +
        TypedV.hiW (vs M ry) 0 Td.one := by
    simp only [virtGX, regSelG, htd.qlt, Lvm.Loop.Build.add]
    refine z_holdAt_bind (z_eqConstG_hold hz ho _ _ _) fun sP hsP => ?_
    refine z_holdAt_bind (hqp _) fun vP hvP => ?_
    refine z_holdAt_bind (z_holdAt_mulAdd .E sP vP z _) fun w hw => ?_
    refine z_holdAt_bind (z_eqConstG_hold hz ho ry Td.one _) fun e1 he1 => ?_
    refine z_holdAt_bind (z_holdAt_lin _ 1 0 w e1 _) fun w' hw' => z_holdAt_pure ?_
    rw [hw', ofK_one, ofK_zero, one_mul, add_zero, hw, hz, add_zero, hsP, hvP, he1]
    simp only [TypedV.hiW, vs, List.map_drop, List.drop_zero, Nat.shiftRight_zero]
  rw [key h, z_virtEF_td htd, z_mleK_pub _ _ (by omega)]

theorem z_virtGX_at (accV : Nat) (vk cL : Vector UInt8 32) (hS : Streamed M sig T)
    (hH : 11 + pubLanesX accV ≤ T) (hA : pubLanesX accV ≤ 2 ^ 10) {z o : Cell}
    (hz : z.val M = 0) (ho : o.val M = 1) (hzE : z.ty = .E) (hoE : o.ty = .E) {Td : TData} {N : TNat}
    (htd : TdOk Td N) {pb : Nat} (hvk : ∀ i < 4, M.k (pb + 1 + i) = (digestLanes vk).getD i 0) (ry : List Cell)
    (hry : ry.length = 21) (hryE : ∀ x ∈ ry, x.ty = .E) (q : Ptr) :
    z_SoundAt c M (virtGX z o Td pb (pubLanesX accV) ry) q fun w =>
      w.val M = TypedV.virtEF N (Lvm.pubOfA accV vk cL sig) (vs M ry) :=
  fun h _ => virtGX_spec accV vk cL hS hH hA hz ho hzE hoE htd hvk ry hry hryE q h

/-- Horner's rule in the circuit (`hornerG`). -/
theorem hornerG_sound (γ : Cell) : ∀ (xs : List Cell) (acc : Cell),
    SoundG c M (hornerG γ xs acc) fun r => r.val M = xs.foldl (fun a x => γ.val M * a + x.val M) (acc.val M)
  | [], _ => soundG_pure rfl
  | x :: xs, acc => by
    rw [hornerG]
    exact soundG_bind (soundG_aspec (QB.aspec_mulAdd .E γ acc x)) fun a ha =>
      soundG_mono (hornerG_sound γ xs a) fun r hr => by rw [hr, ha.1]; rfl

/-- **`batch6G`'s value**: `Σ_{k<6} γ^k v_k` (V_S's initial claim of the wiring). -/
theorem batch6G_sound {z γ : Cell} {v : List Cell} (hv : v.length = 6) :
    SoundG c M (batch6G z γ v) fun c0 =>
      c0.val M = ((List.range 6).map fun k => γ.val M ^ k * (vs M v).getD k 0).sum := by
  match v, hv with
  | [a0, a1, a2, a3, a4, a5], _ =>
    rw [batch6G]
    simp only [List.take_succ_cons, List.take_zero, List.reverse_cons, List.reverse_nil, List.nil_append,
      List.cons_append, List.drop_succ_cons, List.drop_zero, List.getD_cons_succ, List.getD_cons_zero]
    refine soundG_mono (hornerG_sound γ [a4, a3, a2, a1, a0] a5) fun r hr => ?_
    rw [hr]
    simp [vs, List.range_succ]
    ring

/-- **The wiring over the six values replayed** (soundness direction): wherever `wireGX`'s rows hold and assert
(gate on), `dWiringX` on the zerocheck's six values from any state at `wGPX P` with `ok` keeps `ok`, ends at
`rRPX P`; `r_y`, the eight matrix values and the four region values are the output's cells' values. -/
theorem wireGX_replays (accV : Nat) (vk cL : Vector UInt8 32) (hS : Streamed M sig T)
    (hH : 11 + pubLanesX accV ≤ T) (hA : pubLanesX accV ≤ 2 ^ 10) {z o g : Cell}
    (hz : z.val M = 0) (ho : o.val M = 1) (hzE : z.ty = .E) (hoE : o.ty = .E) (hg : g.val M = 1)
    {Td : TData} {N : TNat} (htd : TdOk Td N) {pb : Nat}
    (hvk : ∀ i < 4, M.k (pb + 1 + i) = (digestLanes vk).getD i 0) {P : Nat} (hP : P % 8 = 0)
    (hT : rRPX P + 40 ≤ 8 * T) (v : List Cell) (hv : v.length = 6) (ptr : Ptr) :
    Replays c M sig (TypedV.dWiringX N (Lvm.pubOfA accV vk cL sig) (vs M v))
      (wireGX z o g Td pb P (pubLanesX accV) v) ptr (wGPX P) (rRPX P) fun r t =>
        r.1 = vs M t.1 ∧ r.2.1 = vs M t.2.1 ∧ r.2.2 = vs M t.2.2 ∧ t.1.length = 21 ∧ (∀ x ∈ t.1, x.ty = .E) ∧
          t.2.1.length = 8 ∧ (∀ x ∈ t.2.1, x.ty = .E) ∧ t.2.2.length = 4 ∧ (∀ x ∈ t.2.2, x.ty = .E) := by
  have hW : wGPX P = P + 4056 := wGPX_eq P
  have hR : rRPX P = P + 6936 := by simp only [rRPX, wVPX, wRPX, wGPX, zAbcPX, zRPX, tX, tY]
  have hV : wVPX P = P + 6648 := by simp only [wVPX, wRPX, wGPX, zAbcPX, zRPX, tX, tY]
  have hRP : wRPX P = P + 4128 := by simp only [wRPX, wGPX, zAbcPX, zRPX, tX]
  rw [hR] at hT
  rw [hW, hR]
  refine z_replays_of ?_
  unfold wireGX
  rw [hW, hV, hRP]
  refine z_soundAt_bind (z_ldE_at hS (a := (P + 4056 + 40) / 8) (by omega) _) fun γ hγ => ?_
  refine z_soundAt_bind (z_soundAt_of (batch6G_sound hv) _) fun c0 hc0 => ?_
  refine z_soundAt_getPtr ?_
  refine z_soundAt_bind (z_scP3_at hS tY ((P + 4128) / 8) c0 _ (by simp only [tY]; omega)) fun fin hfin => ?_
  refine z_soundAt_bind (z_soundAt_of (z_ldEs_soundE hS ((P + 6648 + 40) / 8) 3 8 fun i hi => by omega) _)
    fun vC hvC => ?_
  refine z_soundAt_bind (z_soundAt_of (z_ldEs_soundE hS ((P + 6648 + 40) / 8 + 24) 3 4 fun i hi => by omega) _)
    fun rC hrC => ?_
  refine z_soundAt_bind (z_soundAt_of (soundG_aspec (QB.aspec_lin _ 1 0 _ _)) _) fun d1 hd1 => ?_
  refine z_soundAt_bind (z_soundAt_of (soundG_aspec (QB.aspec_lin _ 1 0 _ _)) _) fun d0 hd0 => ?_
  refine z_soundAt_bind (z_soundAt_of (soundG_aspec (QB.aspec_mulAdd .E _ _ _)) _) fun m4 hm4 => ?_
  refine z_soundAt_bind (z_soundAt_of (soundG_aspec (QB.aspec_mulAdd .E _ _ _)) _) fun m3 hm3 => ?_
  refine z_soundAt_bind (z_soundAt_of (soundG_aspec (QB.aspec_mulAdd .E _ _ _)) _) fun m2 hm2 => ?_
  refine z_soundAt_bind (z_soundAt_of (soundG_aspec (QB.aspec_mulAdd .E _ _ _)) _) fun m1 hm1 => ?_
  refine z_soundAt_bind (z_soundAt_of (soundG_aspec (QB.aspec_mulAdd .E _ _ _)) _) fun m0 hm0 => ?_
  refine z_soundAt_bind (z_virtGX_at accV vk cL hS hH hA hz ho hzE hoE htd hvk _ (by simp) (by
    intro x hx
    simp only [List.mem_map, List.mem_range] at hx
    obtain ⟨i, _, rfl⟩ := hx
    rfl) _) fun ve hve => ?_
  refine z_soundAt_bind (z_soundAt_of (sumG_sound hz _) _) fun sC hsC => ?_
  refine z_soundAt_bind (z_soundAt_of (soundG_aspec (QB.aspec_mulAdd .E _ _ _)) _) fun pr hpr => ?_
  refine z_soundAt_bind (z_soundAt_of (soundG_aspec (QB.aspec_assertEq _ _ _)) _) fun _ hA' => ?_
  refine z_soundAt_pure ?_
  intro s hs hok
  simp only [pos] at hs
  simp only [TypedV.dWiringX, Q1.bind_run, Q1.sampleE_run, Q1.pure_run, Q1.readEs_run, Lvm.Har.require_run, hok]
  have e1 : s.ent + 40 + s.msg = P + 4056 + 40 := by omega
  have e2 : s.ent + 72 + s.msg = P + 4128 := by omega
  rw [e1, e2]
  have hγ' : γ.val M = feAt sig (P + 4056 + 40) := by rw [hγ]; congr 1; omega
  have hcl : c0.val M = ((List.range 6).map fun k => feAt sig (P + 4056 + 40) ^ k * (vs M v).getD k 0).sum := by
    rw [hc0, hγ']
  rw [hcl] at hfin
  obtain ⟨h1, h2⟩ := hfin ⟨P + 4128, 0, true⟩ rfl (by dsimp only; omega)
  have hst := congrArg Prod.snd (QB.sumcheck_run 3 (by decide) sig (List.replicate tY none) (c0.val M)
    ⟨P + 4128, 0, true⟩ rfl)
  have hlen := sumcheck_len (c0.val M) 3 (by decide) (List.replicate tY none) sig ⟨P + 4128, 0, true⟩ rfl
  rw [hcl] at hlen hst
  generalize sumcheck _ 3 _ sig _ = R at h1 h2 hst hlen ⊢
  simp only [List.length_replicate] at hst hlen
  rw [hst]
  rw [← h2] at hve
  have hv8 : ∀ s' : RS, s' = ⟨P + 4128 + QB.entB (3 - 1) * tY, 0, true⟩ →
      scalarsAt (feAt sig) (s'.ent + s'.msg + 40) 8 = vs M vC := by
    rintro s' rfl
    rw [hvC.1, scalarsAt]
    refine List.map_congr_left fun i _ => congrArg _ ?_
    simp only [QB.entB, tY]; omega
  have hr4 : ∀ s' : RS, s' = ⟨P + 4128 + QB.entB (3 - 1) * tY, 0, true⟩ →
      scalarsAt (feAt sig) (s'.ent + (s'.msg + 24 * 8) + 40) 4 = vs M rC := by
    rintro s' rfl
    rw [hrC.1, scalarsAt]
    refine List.map_congr_left fun i _ => congrArg _ ?_
    simp only [QB.entB, tY]; omega
  rw [hv8 _ rfl, hr4 _ rfl]
  dsimp only
  simp only [z_getD_vs vC z, hz] at hd1 hd0 hm4 hm3 hm2 hm1 hm0
  have hsC' : sC.val M = sumE (vs M rC) + ve.val M := by
    rw [hsC, show vs M (rC ++ [ve]) = vs M rC ++ [ve.val M] by simp [vs], sumE_append, sumE_cons, sumE_nil,
      add_zero]
  refine ⟨?_, ?_, h2, rfl, rfl, by simp, ?_, ?_, hvC.2, ?_, hrC.2⟩
  · rw [Bool.and_true, QB.FE.beq_iff, ← h1, (QB.gate_eq_iff hg _ _).mp hA'.2, hpr.1, hz, add_zero, hsC', hve,
      hm0.1, hm1.1, hm2.1, hm3.1, hm4.1, hd1.1, hd0.1, hγ', ofK_one, ofK_zero, one_mul, add_zero, add_zero,
      TypedV.wGXF]
    ring
  · simp only [pos, QB.entB, tY]
  · intro x hx
    simp only [List.mem_map, List.mem_range] at hx
    obtain ⟨i, _, rfl⟩ := hx
    rfl
  · simpa [vs] using congrArg List.length hvC.1
  · simpa [vs] using congrArg List.length hrC.1

end
end Lvm.E2Q
end

section
set_option autoImplicit false
namespace Lvm.E2Q
open Lvm Lvm.Loop Lvm.Loop.Build Lvm.QTyped Lvm.Q1 DM Lvm.Har
open Lvm.TypedV (TNat)
section
variable {c : Ctx} {M : Mem} {sig : ByteArray} {T : Nat}
section helpers
open Lvm.QAcc Lvm.QSig

attribute [local irreducible] Lvm.QAcc.horner Lvm.QAcc.macChain Lvm.QAcc.linePts in
set_option maxHeartbeats 1000000 in
/-- **`qaccTX`'s facts** (gate on, the child's stream bound): the five equations of A23 on `feAt Σ` (`qaccT_facts`
at `κ` of 3 samples, `h` of 45 scalars, the current `acc_in` at 44 coordinates). -/
theorem qaccTX_facts {L pb : Nat} {p : Ptr} (hS : Streamed M sig T) (hT : L + 178 < T)
    (hH : 11 + pubLanesX accVF ≤ T) (hg : M.k pb = 1)
    (rx ry v : List Cell) (hrx : rx.length = 20) (hry : ry.length = 21) (hv : v.length = 8)
    (h : Lvm.QSig.Ok c M (qaccTX L pb rx ry v) p) :
    let K := (List.range 3).map fun i => feAt sig (8 * (L + 5 + 9 * i))
    let H := (List.range 45).map fun j => feAt sig (8 * (L + 27 + 5 + 3 * j))
    let t := feAt sig (8 * (L + 27 + 3 * 45 + 5))
    H.headD 0 = feAt sig (8 * accLane 44) ∧ sumE H = Lvm.dot (eqKernel K) (vs M v) ∧
      accLine ((List.range 44).map fun i => feAt sig (8 * accLane i)) (K ++ vs M (rx ++ ry)) t =
        (accCA accVF M pb).pt ∧
      polyEval H t = (accCA accVF M pb).y ∧ feAt sig (8 * (L + 27 + 3 * 45 + 9 + 5)) = 0 := by
  have hD : tVarsX = 44 := rfl
  have hPL : pubLanesX accVF = 750 := rfl
  have hgv : (kc pb).val M = 1 := kc_val_one hg
  unfold qaccTX at h
  obtain ⟨zo, p1, evo1, epo1, o1, h⟩ := okBindE h
  obtain ⟨hz1, hz2, hz0, hone⟩ := consts_spec o1.1
  have hzv : (consts pb p).1.1.val M = 0 := by rw [hz1]; exact hz0
  have hov : M.e (consts pb p).1.2.n = 1 := by rw [hz2]; exact hone
  have hov' : (consts pb p).1.2.val M = 1 := by rw [hz2]; exact hone
  rw [evo1] at hzv hov hov'
  -- κ
  obtain ⟨kb, p2, evo2, epo2, o2, h⟩ := okBindE h
  have hk := ldEsB_spec hS (qs := (List.range 3).map fun i => L + 5 + 9 * i)
    (by intro q hq; simp only [List.mem_map, List.mem_range] at hq; obtain ⟨i, hi, rfl⟩ := hq; omega) o2.1
  rw [evo2] at hk
  -- y'
  obtain ⟨y, p5, evo5, epo5, o5, h⟩ := okBindE h
  have hy := qyown_spec (by omega : 1 ≤ 3) (by rw [hv]; decide) hzv hov o5.1
  rw [evo5] at hy
  -- h', acc_in'
  obtain ⟨hb, p6, evo6, epo6, o6, h⟩ := okBindE h
  have hh := ldEsB_spec hS (qs := (List.range (tVarsX + 1)).map fun j => L + 27 + 5 + 3 * j)
    (by intro q hq; simp only [List.mem_map, List.mem_range] at hq; obtain ⟨i, hi, rfl⟩ := hq; omega) o6.1
  rw [evo6] at hh
  obtain ⟨ab, p7, evo7, epo7, o7, h⟩ := okBindE h
  have ha := ldEsB_spec hS (qs := (List.range (tVarsX + 1)).map accLane)
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
  have ht := ldE_feAt hS (q := L + 27 + 3 * (tVarsX + 1) + 5) (by omega) o11.1
  rw [evo11] at ht
  obtain ⟨hv', p12, evo12, epo12, o12, h⟩ := okBindE h
  have hhv := horner_spec (c := c) (M := M) t zo.1 hzv ((List.range (tVarsX + 1)).map fun j => ec (hb + j)) p11
    o12.1
  rw [evo12] at hhv
  obtain ⟨pts, p13, evo13, epo13, o13, h⟩ := okBindE h
  have hpt := linePts_spec (c := c) (M := M) t ((List.range tVarsX).map fun i =>
    (ec (ab + i), (((List.range 3).map (fun j => ec (kb + j)) ++ rx ++ ry).getD i (ec 0)))) p12 o13.1
  rw [evo13] at hpt
  -- the current acc_in
  obtain ⟨pc, p14, evo14, epo14, o14, h⟩ := okBindE h
  have hpc := ldEsB_val (c := c) (M := M) (qs := (List.range (tVarsX + 1)).map fun j => pb + 615 + 3 * j)
    (p := p13) o14.1
  rw [evo14] at hpc
  obtain ⟨_vo15, p15, evo15, epo15, o15, h⟩ := okBindE h
  have e15 := assertEqs_spec (c := c) (M := M) hgv
    ((List.range tVarsX).map fun i => (pts.getD i default, ec (pc + i))) p14 o15
  obtain ⟨_vo16, p16, evo16, epo16, o16, h⟩ := okBindE h
  have e16 := assertEqE_spec o16 hgv
  obtain ⟨zz, _qo17, evo17, epo17, o17, h⟩ := okBindE h
  have hz := ldE_feAt hS (q := L + 27 + 3 * (tVarsX + 1) + 9 + 5) (by omega) o17.1
  rw [evo17] at hz
  have e17 := assert0_spec h.2
  rw [hgv, one_mul] at e17
  have h45 : tVarsX + 1 = 45 := rfl
  rw [h45] at hh ha hpc ht hz hhv
  rw [hD] at e8 hpt e15 e16
  have hkv : ∀ i < 3, M.e (kb + i) = feAt sig (8 * (L + 5 + 9 * i)) := by
    intro i hi; rw [hk i (by simpa using hi)]; simp [List.getD_eq_getElem?_getD, List.getElem?_range hi]
  have hhv' : ∀ j < 45, M.e (hb + j) = feAt sig (8 * (L + 27 + 5 + 3 * j)) := by
    intro j hj; rw [hh j (by simpa using hj)]; simp [List.getD_eq_getElem?_getD, List.getElem?_range hj]
  have hav : ∀ j < 45, M.e (ab + j) = feAt sig (8 * accLane j) := by
    intro j hj; rw [ha j (by simpa using hj)]; simp [List.getD_eq_getElem?_getD, List.getElem?_range hj]
  have hHl : (List.range 45).map (fun j => feAt sig (8 * (L + 27 + 5 + 3 * j))) =
      ((List.range 45).map fun j => ec (hb + j)).map (Cell.val M) := by
    rw [List.map_map]; apply List.map_congr_left; intro j hj; rw [List.mem_range] at hj
    simp [hhv' j hj]
  have hKv : (List.range 3).map (fun i => M.e (kb + i)) =
      (List.range 3).map fun i => feAt sig (8 * (L + 5 + 9 * i)) := by
    apply List.map_congr_left; intro i hi; rw [List.mem_range] at hi; exact hkv i hi
  dsimp only
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · rw [List.range_succ_eq_map, List.map_cons, List.headD_cons]
    have := hhv' 0 (by omega)
    rw [Nat.add_zero] at this
    rw [← this, ← hav 44 (by omega)]; exact e8
  · have hsum : sh.val M = ((List.range 45).map fun j => feAt sig (8 * (L + 27 + 5 + 3 * j))).sum := by
      rw [hsh, hzv, zero_add, List.map_map, hHl, List.map_map]
      congr 1; apply List.map_congr_left; intro j _
      simp [hov']
    rw [Lvm.Har.sumE_eq, ← hsum, e10, hy, dot_eqKernel _ _ (by simp [vs, hv]), hKv]
    simp only [vs, List.length_map]
    refine Finset.sum_congr rfl fun k hk => ?_
    rw [Finset.mem_range] at hk
    rw [List.getD_eq_getElem _ _ hk, List.getD_eq_getElem _ _ (by simpa using hk), List.getElem_map]
  · have hbc : ((List.range 3).map (fun j => ec (kb + j)) ++ rx ++ ry).map (Cell.val M) =
        (List.range 3).map (fun i => feAt sig (8 * (L + 5 + 9 * i))) ++ vs M (rx ++ ry) := by
      rw [← hKv, List.append_assoc, List.map_append, List.map_map]; rfl
    have hbl : ((List.range 3).map (fun j => ec (kb + j)) ++ rx ++ ry).length = 44 := by
      simp [hrx, hry]
    rw [← hbc, ← ht]
    apply List.ext_getElem
    · simp [accLine, accCA, List.length_zipWith, hrx, hry, accVF]
    intro i h1 h2
    have hi : i < 44 := by simpa [accCA, accVF] using h2
    have hpi := hpt.2 i (by simpa using hi)
    rw [List.getD_eq_getElem ((List.range 44).map fun i =>
        (ec (ab + i), ((List.range 3).map (fun j => ec (kb + j)) ++ rx ++ ry).getD i (ec 0))) _ (by simpa using hi),
      List.getElem_map, List.getElem_range,
      List.getD_eq_getElem ((List.range 3).map (fun j => ec (kb + j)) ++ rx ++ ry) _ (by rw [hbl]; exact hi)] at hpi
    have hq := e15 ((pts.getD i default, ec (pc + i))) (List.mem_map.mpr ⟨i, List.mem_range.mpr hi, rfl⟩)
    have hpci : M.e (pc + i) = ⟨M.k (pb + 615 + 3 * i), M.k (pb + 615 + 3 * i + 1),
        M.k (pb + 615 + 3 * i + 2)⟩ := by
      rw [hpc i (by simp; omega)]
      simp [List.getD_eq_getElem?_getD, List.getElem?_range (by omega : i < 45)]
    simp only [Cell.val_E] at hq hpi
    rw [hq, hpci, hav i (by omega)] at hpi
    simp only [accLine, List.getElem_zipWith, List.getElem_map, List.getElem_range, accCA]
    exact hpi.symm
  · rw [hHl, ← ht, ← hhv, e16, Cell.val_E, hpc 44 (by simp)]
    simp [accCA, List.getD_eq_getElem?_getD, accVF]
  · exact hz.symm.trans e17

/-- **`dAccX` from position `Q = ent + msg`**: `κ` (3), `h` (45), `t`, the zero scalar at fixed offsets. -/
theorem dAccX_run (pub : Pub) (rxy w : List FE) (sig : ByteArray) (s : RS) :
    TypedV.dAccX pub rxy w sig s =
      let K := (List.range 3).map fun i => feAt sig (s.ent + s.msg + 40 + 72 * i)
      let H := (List.range 45).map fun j => feAt sig (s.ent + s.msg + 256 + 24 * j)
      let t := feAt sig (s.ent + s.msg + 1336)
      (⟨accLine pub.accIn.pt (K ++ rxy) t, polyEval H t⟩,
        ⟨s.ent + s.msg + 1368, 24, (feAt sig (s.ent + s.msg + 1408) == 0) &&
          ((sumE H == Lvm.dot (eqKernel K) w) && ((H.headD 0 == pub.accIn.y) && s.ok))⟩) := by
  unfold TypedV.dAccX
  rw [Lvm.Q1.bind_run, Lvm.Q1.samples_run sig 3 _ (by norm_num), Lvm.Q1.bind_run, Lvm.Q1.readEs_run,
    Lvm.Q1.bind_run, Lvm.Q1.sampleE_run, Lvm.Q1.bind_run, Lvm.Q1.readE_run, Lvm.Q1.bind_run, require_run_lk,
    Lvm.Q1.bind_run, require_run_lk, Lvm.Q1.bind_run, require_run_lk, Lvm.Q1.pure_run]
  dsimp only [scalarsAt]
  rfl

end helpers
end
end Lvm.E2Q
end

section
set_option autoImplicit false
namespace Lvm.E2Q
open Lvm Lvm.Loop Lvm.Loop.Build Lvm.QTyped Lvm.Q1 DM Lvm.Har
open Lvm.TypedV (TNat)
section
variable {c : Ctx} {M : Mem} {sig : ByteArray} {T : Nat}

/-- **A23 at `Φ_Q` in 44 variables replayed** (soundness direction): `dAccX` on the child's `PUB` at
`acc_in` of 44 coordinates folds to the current proof's `acc_in` (`accCA accVF M pb`). -/
theorem qaccTX_replays (vk cL : Vector UInt8 32) (hS : Streamed M sig T) (hH : 11 + pubLanesX accVF ≤ T)
    {pb : Nat} (hg : M.k pb = 1) {P : Nat} (hP : P % 8 = 0) (hT : mbPX P + 40 ≤ 8 * T) (rx ry v : List Cell)
    (hrx : rx.length = 20) (hry : ry.length = 21) (hv : v.length = 8) (ptr : Ptr) :
    Replays c M sig (TypedV.dAccX (Lvm.pubOfA accVF vk cL sig) (vs M (rx ++ ry)) (vs M v))
      (qaccTX (aPX P / 8) pb rx ry v) ptr (aPX P) (mbPX P) fun a _ => a = accCA accVF M pb := by
  intro h s hs hok
  have hD : tVarsX = 44 := rfl
  have h8 : 8 * (aPX P / 8) = aPX P := by
    have : aPX P % 8 = 0 := by simp only [aPX, rVPX, rRPX, wVPX, wRPX, wGPX, zAbcPX, zRPX, tX, tY, tR]; omega
    omega
  have hmb : mbPX P = aPX P + 1392 := by simp only [mbPX]; omega
  obtain ⟨F1, F2, F3, F4, F5⟩ := qaccTX_facts hS (by omega) hH hg rx ry v hrx hry hv h
  obtain ⟨hy, hpt⟩ := pubOfA_accIn accVF vk cL sig
  have hQ : s.ent + s.msg = 8 * (aPX P / 8) := by rw [h8]; exact hs
  rw [dAccX_run]
  dsimp only
  rw [hQ]
  have eK : (List.range 3).map (fun i => feAt sig (8 * (aPX P / 8) + 40 + 72 * i)) =
      (List.range 3).map fun i => feAt sig (8 * (aPX P / 8 + 5 + 9 * i)) :=
    List.map_congr_left fun i _ => congrArg _ (by omega)
  have eH : (List.range 45).map (fun j => feAt sig (8 * (aPX P / 8) + 256 + 24 * j)) =
      (List.range 45).map fun j => feAt sig (8 * (aPX P / 8 + 27 + 5 + 3 * j)) :=
    List.map_congr_left fun j _ => congrArg _ (by omega)
  have et : feAt sig (8 * (aPX P / 8) + 1336) = feAt sig (8 * (aPX P / 8 + 27 + 3 * 45 + 5)) :=
    congrArg _ (by omega)
  have ez : feAt sig (8 * (aPX P / 8) + 1408) = feAt sig (8 * (aPX P / 8 + 27 + 3 * 45 + 9 + 5)) :=
    congrArg _ (by omega)
  rw [eK, eH, et, ez]
  refine ⟨?_, ?_, ?_⟩
  · rw [F5, F1, hy, F2]
    simp [hok, accVF]
  · show 8 * (aPX P / 8) + 1368 + 24 = mbPX P
    omega
  · rw [hpt, show accVF = 44 from rfl, F3, F4]
    rfl

theorem typedPosX_le (Td : TData) (P : Nat) :
    wGPX P ≤ rRPX P ∧ rRPX P ≤ aPX P ∧ aPX P ≤ mbPX P ∧ mbPX P ≤ typedEndX Td P := by
  have h1 : mbPX P ≤ busEndD Td.mbD (mbPX P) := by
    unfold busEndD
    have := le_layersEnd (gkrSteps Td.mbD) 0 (busP1 (mbPX P) + 48)
    simp only [busP1] at this ⊢
    omega
  have h2 : busEndD Td.mbD (mbPX P) ≤ typedEndX Td P := by
    unfold typedEndX tabEnd; omega
  refine ⟨?_, ?_, ?_, le_trans h1 h2⟩ <;> simp only [wGPX, rRPX, aPX, mbPX, wRPX, wVPX, rVPX] <;> omega

set_option maxHeartbeats 1000000 in
/-- **The typed core gadget at S2GF replays `dTypedX`** (soundness direction), on the child's `PUB` at
`acc_in` of 44 coordinates. -/
theorem typedGX_replays (vk cL : Vector UInt8 32) (hS : Streamed M sig T) (hH : 11 + pubLanesX accVF ≤ T)
    {pb : Nat} (hg : M.k pb = 1) (hvk : ∀ i < 4, M.k (pb + 1 + i) = (digestLanes vk).getD i 0) {z o : Cell}
    (hzE : z.ty = .E) (hoE : o.ty = .E) (hz : z.val M = 0) (ho : o.val M = 1) (p : Params)
    (hl : p.leafdecReads = 1) {Td : TData} {N : TNat} (htd : TdOk Td N) (hsc : Lvm.M3.sumcheckTabs N.mbT = N.mbT)
    (hS' : Td.mbS = N.mbT.map Lvm.M3.Tab.shape) (hR : Td.mbR = p.tableRounds) (hD : Td.mbD = p.busDepth)
    (hfix : FixListed N.mbT Td.mbFix) {P : Nat} (hP : P % 8 = 0) (hT : typedEndX Td P + 40 ≤ 8 * T) (q : Ptr)
    (hq : 1 ≤ q.e) :
    Replays c M sig (TypedV.dTypedX p N (N.m3 p) (Lvm.pubOfA accVF vk cL sig)) (typedGX Td pb P accVF z o) q P
      (typedEndX Td P) fun v t => v.1 = accCA accVF M pb ∧
        v.2.1 = TypedV.typedClaimsN N p (vs M t.ry) (vs M t.rv) (vs M t.rr) (t.vR.val M) ∧
        v.2.2 = t.tab.map fun e => (vs M e.1, vs M e.2) := by
  intro hok s hs hsok
  have hgv : (kc pb).val M = 1 := Lvm.QAcc.kc_val_one hg
  have hA : pubLanesX accVF ≤ 2 ^ 10 := by decide
  obtain ⟨l1, l2, l3, l4⟩ := typedPosX_le Td P
  have m1 : wGPX P % 8 = 0 := by simp only [wGPX, zAbcPX, zRPX, tX]; omega
  have m4 : mbPX P % 8 = 0 := by
    simp only [mbPX, aPX, rVPX, rRPX, wVPX, wRPX, wGPX, zAbcPX, zRPX, tVarsX, tX, tY, tR]; omega
  have eR : rRP (rRPX P - rRP 0) = rRPX P := by
    simp only [rRP, wVP, wRP, wGP, zAbcP, zRP, rRPX, wVPX, wRPX, wGPX, zAbcPX, zRPX, tX, tY]; omega
  have eA : aP (rRPX P - rRP 0) = aPX P := by
    simp only [aP, rVP, rRP, wVP, wRP, wGP, zAbcP, zRP, aPX, rVPX, rRPX, wVPX, wRPX, wGPX, zAbcPX, zRPX, tX, tY,
      tR]; omega
  have m2 : (rRPX P - rRP 0) % 8 = 0 := by
    simp only [rRP, wVP, wRP, wGP, zAbcP, zRP, rRPX, wVPX, wRPX, wGPX, zAbcPX, zRPX, tX, tY]; omega
  simp only [typedGX] at hok
  simp only [typedGX, bind_apply, pure_apply, TypedV.dTypedX, bind_run', pure_run']
  rw [show N.m3 p = M3.real p (fun _ => N.mbT) from rfl]
  -- the zerocheck
  obtain ⟨hZ, hok⟩ := okb hok
  generalize hzr : (zeroGX z (kc pb) P q).1 = zr at hok ⊢
  generalize hq1 : q.adv (zeroGX z (kc pb) P q).2 = q1 at hok ⊢
  have hq1e : 1 ≤ q1.e := le_trans hq (by rw [← hq1]; exact Lvm.QAcc.adv_e_le _ _)
  have RZ := zeroGX_replays (c := c) hS hz hgv hP (by omega) q hZ s hs hsok
  rw [hzr] at RZ
  generalize TypedV.dZeroX sig s = Zv at RZ ⊢
  obtain ⟨zv, s1⟩ := Zv
  obtain ⟨z1, z2, ⟨z3, z4, z5, z6, z7, z8⟩⟩ := RZ
  simp only at z1 z2 z3 z4 ⊢
  rw [z4]
  -- the wiring
  obtain ⟨hW, hok⟩ := okb hok
  generalize hw : (wireGX z o (kc pb) Td pb P (pubLanesX accVF) zr.2 q1).1 = w at hok ⊢
  generalize hq2 : q1.adv (wireGX z o (kc pb) Td pb P (pubLanesX accVF) zr.2 q1).2 = q2 at hok ⊢
  have hq2e : 1 ≤ q2.e := le_trans hq1e (by rw [← hq2]; exact Lvm.QAcc.adv_e_le _ _)
  have RW := wireGX_replays (c := c) accVF vk cL hS hH hA hz ho hzE hoE hgv htd hvk hP (by omega) zr.2 z7 q1 hW
    s1 z2 z1
  rw [hw] at RW
  generalize TypedV.dWiringX N (Lvm.pubOfA accVF vk cL sig) (vs M zr.2) sig s1 = Wv at RW ⊢
  obtain ⟨wv, s2⟩ := Wv
  obtain ⟨w1, w2, w3, w4, w5, w6, w7, w8, w9, w10, w11⟩ := RW
  simp only at w1 w2 w3 w4 w5 ⊢
  have evS : wv.2.2.getD 1 0 = (w.2.2.getD 1 z).val M := by
    rw [w5]; exact Lvm.QAcc.getD_vals _ _ hz 1
  rw [evS, w3]
  -- the relayout
  obtain ⟨hRl, hok⟩ := okb hok
  generalize hr : (relayG z o (kc pb) Td (rRPX P - rRP 0) w.1 (w.2.2.getD 1 z) q2).1 = r at hok ⊢
  generalize hq3 : q2.adv (relayG z o (kc pb) Td (rRPX P - rRP 0) w.1 (w.2.2.getD 1 z) q2).2 = q3 at hok ⊢
  have hq3e : 1 ≤ q3.e := le_trans hq2e (by rw [← hq3]; exact Lvm.QAcc.adv_e_le _ _)
  have RR := relayG_replays (c := c) hS hz ho hzE hoE hgv rfl htd m2 (by rw [eA]; omega) w.1 w6 w7
    (w.2.2.getD 1 z) q2 hq2e hRl s2 (by rw [eR]; exact w2) w1
  rw [hr, eA] at RR
  generalize TypedV.dRelayT N (vs M w.1) ((w.2.2.getD 1 z).val M) sig s2 = Rv at RR ⊢
  obtain ⟨rv, s3⟩ := Rv
  obtain ⟨r1, r2, r3, r4, r5, r6⟩ := RR
  simp only at r1 r2 r3 r4 ⊢
  have exy : zv.1 ++ vs M w.1 = vs M (zr.1 ++ w.1) := by rw [z3]; simp [vs]
  rw [exy, w4]
  -- A23 at `Φ_Q`
  obtain ⟨hA23, hok⟩ := okb hok
  generalize hq4 : q3.adv (qaccTX (aPX P / 8) pb zr.1 w.1 w.2.1 q3).2 = q4 at hok ⊢
  have hq4e : 1 ≤ q4.e := le_trans hq3e (by rw [← hq4]; exact Lvm.QAcc.adv_e_le _ _)
  have RA := qaccTX_replays (c := c) vk cL hS hH hg hP (by omega) zr.1 w.1 w.2.1 z5 w6 w8 q3 hA23 s3 r2 r1
  generalize TypedV.dAccX (Lvm.pubOfA accVF vk cL sig) (vs M (zr.1 ++ w.1)) (vs M w.2.1) sig s3 = Av at RA ⊢
  obtain ⟨av, s4⟩ := Av
  obtain ⟨a1, a2, a3⟩ := RA
  simp only at a1 a2 a3 ⊢
  -- the mini-bus
  obtain ⟨hM, -⟩ := okb hok
  have RM := miniG_replays (c := c) hS hz ho hzE hoE hgv rfl p hl Td N.mbT hsc hS' hR hD hfix
    (Lvm.pubOfA accVF vk cL sig) m4 (by unfold typedEndX at hT; omega) q4 hq4e hM s4 a2 a1
  generalize TypedV.dMiniT p (M3.real p fun _ => N.mbT) N.mbT (Lvm.pubOfA accVF vk cL sig) sig s4 = Mv at RM ⊢
  obtain ⟨mv, s5⟩ := Mv
  obtain ⟨b1, b2, b3⟩ := RM
  refine ⟨b1, b2, a3, ?_, b3⟩
  rw [w5, r3, r4]

/-- **The typed phases at S2GF in `PhaseAt` form** (`core_of_phasesF`'s `htyped`): from `P` to `typedEndX Td P`,
the accumulator the current proof's `acc_in` cells, the claims and evaluations the gadget's cells'. -/
theorem typed_phaseX (vk cL : Vector UInt8 32) (hS : Streamed M sig T) (hH : 11 + pubLanesX accVF ≤ T)
    {pb : Nat} (hg : M.k pb = 1) (hvk : ∀ i < 4, M.k (pb + 1 + i) = (digestLanes vk).getD i 0) {z o : Cell}
    (hzE : z.ty = .E) (hoE : o.ty = .E) (hz : z.val M = 0) (ho : o.val M = 1) (p : Params)
    (hl : p.leafdecReads = 1) {Td : TData} {N : TNat} (htd : TdOk Td N) (hsc : Lvm.M3.sumcheckTabs N.mbT = N.mbT)
    (hS' : Td.mbS = N.mbT.map Lvm.M3.Tab.shape) (hR : Td.mbR = p.tableRounds) (hD : Td.mbD = p.busDepth)
    (hfix : FixListed N.mbT Td.mbFix) {P : Nat} (hP : P % 8 = 0) (hT : typedEndX Td P + 40 ≤ 8 * T) (q : Ptr)
    (hq : 1 ≤ q.e) (hok : Lvm.QSig.Ok c M (typedGX Td pb P accVF z o) q) :
    PhaseAt (TypedV.dTypedX p N (N.m3 p) (Lvm.pubOfA accVF vk cL sig)) sig P (typedEndX Td P)
      (accCA accVF M pb, TypedV.typedClaimsN N p (vs M (typedGX Td pb P accVF z o q).1.ry)
        (vs M (typedGX Td pb P accVF z o q).1.rv) (vs M (typedGX Td pb P accVF z o q).1.rr)
        ((typedGX Td pb P accVF z o q).1.vR.val M),
        (typedGX Td pb P accVF z o q).1.tab.map fun e => (vs M e.1, vs M e.2)) :=
  phaseAt_of (typedGX_replays vk cL hS hH hg hvk hzE hoE hz ho p hl htd hsc hS' hR hD hfix hP hT q hq) hok
    fun a ⟨h1, h2, h3⟩ => Prod.ext h1 (Prod.ext h2 h3)

end
end Lvm.E2Q
end

-- ===== from `LvmE2QHarF` =====

section
set_option autoImplicit false
namespace Lvm.E2Q
open RecursionFast Lvm Lvm.T Lvm.ASM Lvm.Replay Lvm.Loop Lvm.Loop.Build Lvm.QLink Lvm.QSig Lvm.QAsm Lvm.NS
open Lvm.Typed LeanVM.Protocol

/-- The facts `harChkBF20` decides. -/
theorem harChkF20_sound (h : harChkBF20 = true) :
    Lvm.Har.TdOk tdataF20 NTF20 ∧ typedPosF P20F % 8 = 0 ∧
      typedEndX tdataF20 (typedPosF P20F) = posOf P20F (phaseItem0 P20F .tape) ∧
      typedEndX tdataF20 (typedPosF P20F) + 40 ≤ 8 * streamLanes P20F ∧
      posOf P20F (phaseItem0 P20F .openMain) + 48 ≤ 8 * streamLanes P20F ∧
      (∀ a ∈ powFront P20F, a.1 + 2 < streamLanes P20F ∧ a.2 ≤ 64) ∧
      posOf P20F (phaseItem0 P20F .openMain) = 8 * (phaseLane P20F .openMain 0 - 5) ∧
      Lvm.Har.LayOk (cfgMainF P20F (fun _ => 0) (fun _ => 0)) (streamLanes P20F) = true ∧
      8 * Lvm.Har.stackEndL P20F.grind P20F.mainOod P20F.mainLevels (phaseLane P20F .openMain 0 - 5 + 15) =
        hashedLen P20F ∧
      P20F.mainLevels.length ≤ (Lvm.QLink.opens P20F).length ∧ 1 ≤ 64 - P20F.grind ∧
      Lvm.Fin.PosLanes P20F P20F.grind P20F.mainOod P20F.mainLevels (phaseLane P20F .openMain 0 - 5 + 15) 0 ∧
      typedRegB tdataF20 (layout0 P20F).s = true := by
  simp only [harChkBF20, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq, List.all_eq_true] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩, h7⟩, h8⟩, h9⟩, h10⟩, h11⟩, h12⟩, h13⟩ := h
  exact ⟨Lvm.Har.tdOk_of h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13⟩

end Lvm.E2Q
end

section
set_option autoImplicit false
namespace Lvm.E2Q
open RecursionFast Lvm Lvm.T Lvm.ASM Lvm.Replay Lvm.Loop Lvm.Loop.Build Lvm.QLink Lvm.QSig Lvm.QAsm Lvm.NS
open Lvm.Typed LeanVM.Protocol

/-- **Q_arith of the S2GF node program**: the root pin, the `E2` front, `qarithF`. -/
def qaF20 : BM Unit := do
  let pin ← pinF cfgF20.p
  let o ← frontF cfgF20
  qarithF cfgF20 tdataF20 pin o

/-- The S2GF node program is a node program with Q_arith `qaF20`. -/
theorem QF20_qa : QF20 = toProgram (nK cfgF20) 0 (qprogP P20F (lay cfgF20) (sigIn cfgF20) qaF20) :=
  QF20_eq

/-- **`Φ_Q` holds at the statement's `acc_in`** for V_S's fast evaluator at S2GF (`NTF20.phi = PhiQCX cacheF20`):
statement 13 (`PhiQCX_eq`, its cache check decided in the guard) and the good pair's `AccOkTX`. -/
theorem phiF20_acc (S : NodeGF frzF20 QF20 layF20 NTF20) (H : THypX TiF20) {x : List UInt8}
    {qm : Column CMain.nu20} {qr : Column 19} (hG : E2V.GoodTF TiF20 H x qm qr) :
    NTF20.phi (Lvm.VEq.pubXF x).accIn.pt = (Lvm.VEq.pubXF x).accIn.y := by
  have hacc : AccOkTX TiF20 (Lvm.VEq.pubXF x) := hG.1.2
  have e : NTF20.phi (Lvm.VEq.pubXF x).accIn.pt = PhiQFX QF20 layF20 (Lvm.VEq.pubXF x).accIn.pt := by
    show PhiQCX cacheF20 _ = _
    rw [cacheF20_eq S.st.hlay]
    exact PhiQCX_eq QF20 layF20 S.st.hlay S.st.cache _ (H.acc x)
  rw [e]
  apply FE.toExt3_injective
  rw [← hacc]
  show _ = FE.toExt3 (PhiQFX QF20 layF20 (((Lvm.VEq.pubXF x).accIn.pt.map FE.toExt3).map FE.ofExt3))
  rw [List.map_map]
  congr 2

/-- The circuit's static data at S2GF is `tdataOf` (roll 11's `tdata20_eq`). -/
theorem tdataF20_of : tdataF20 = Lvm.QTyped.tdataOf cfgF20 frzF20 := rfl

/-- **The mini-bus record at S2GF** (roll 11's `mini20`): the tables are all sumcheck tables, the circuit's tables,
rounds, depth and fixed list are the record's. -/
theorem miniF20 (S : NodeGF frzF20 QF20 layF20 NTF20) : Lvm.M3.sumcheckTabs NTF20.mbT = NTF20.mbT ∧
    tdataF20.mbS = NTF20.mbT.map Lvm.M3.Tab.shape ∧ tdataF20.mbR = P20F.tableRounds ∧
    tdataF20.mbD = P20F.busDepth ∧ Lvm.Har.FixListed NTF20.mbT tdataF20.mbFix := by
  have hsc : Lvm.M3.sumcheckTabs (Lvm.QTyped.mbTOf cfgF20 frzF20) = Lvm.QTyped.mbTOf cfgF20 frzF20 :=
    Lvm.Har.mbT_sumcheck cfgF20 _ _ _
  have hm := S.st.mini
  have hN : NTF20.mbT = Lvm.QTyped.mbTOf cfgF20 frzF20 := rfl
  rw [hN, show cfgF20.p = P20F from rfl] at hm
  simp only [TypedV.fitsMiniB, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at hm
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨-, hD⟩, -⟩, -⟩, hR⟩, -⟩, -⟩, -⟩, -⟩ := hm
  rw [hsc] at hR
  obtain ⟨t1, t2, t3, t4⟩ := Lvm.Har.tdataOf_mb cfgF20 frzF20
  rw [tdataF20_of, hN, t1, t2, t3, t4, hR, hD]
  exact ⟨hsc, rfl, rfl, rfl, Lvm.Har.mbT_fix cfgF20 _ _ _⟩

end Lvm.E2Q
end

section
set_option autoImplicit false
namespace Lvm.E2Q
open RecursionFast Lvm Lvm.T Lvm.ASM Lvm.Replay Lvm.Loop Lvm.Loop.Build Lvm.QLink Lvm.QSig Lvm.QAsm Lvm.NS
open Lvm.Typed LeanVM.Protocol

/-- The small shape at `P20F` (generic in `pub`: a closed `pub` would make the kernel evaluate its `n`). -/
theorem smallT_P20F (pub : Pub) : TypedV.smallT P20F pub = decide (pub.n ≤ 2 ^ 18) := rfl

end Lvm.E2Q
end

section
set_option autoImplicit false
namespace Lvm.E2Q
open RecursionFast Lvm Lvm.T Lvm.ASM Lvm.Replay Lvm.Loop Lvm.Loop.Build Lvm.QLink Lvm.QSig Lvm.QAsm Lvm.NS
open Lvm.Typed LeanVM.Protocol

end Lvm.E2Q
end

section
set_option autoImplicit false
namespace Lvm.E2Q
open RecursionFast Lvm Lvm.T Lvm.ASM Lvm.Replay Lvm.Loop Lvm.Loop.Build Lvm.QLink Lvm.QSig Lvm.QAsm Lvm.NS
open Lvm.Typed LeanVM.Protocol

/-- **The typed claims stand for V's** (generic in the memory: the kernel never unfolds the instance's), from
`typedClaimsC_val`'s two lists and `typedClaimsC_ok`. -/
theorem typed_relF {M : Mem} {zc : Cell} {b : Bool} {N : TypedV.TNat} {pub : Pub} {t : Lvm.QTyped.TypedC}
    {tc : List Lvm.Har.CClaim × List Lvm.Har.CClaim} {z : Cell} (hz : z.val M = 0) {st : List Lvm.M3.Tab}
    {ev : List (List FE × List FE)} (hX : (N.m3 P20F).tableClaims pub ev = Lvm.M3.tableClaimsR st ev)
    (T1 : tc.1.map (Lvm.Har.CClaim.val M) =
      (.main, BlockClaim.point ⟨19, (layout0 P20F).s⟩ (Lvm.Har.vs M t.rr) (t.vR.val M)) ::
        (.main, ⟨⟨P20F.nuMain, 0⟩, TypedV.affW N .sigma (Lvm.Har.vs M t.ry), (t.rv.getD 2 z).val M⟩) ::
          (Lvm.M3.tableClaimsR st ev).filter (·.1 == .crec))
    (T2 : tc.2.map (Lvm.Har.CClaim.val M) =
      (.main, ⟨⟨P20F.nuMain, 0⟩, TypedV.affW N .com (Lvm.Har.vs M t.ry), (t.rv.getD 0 z).val M⟩) ::
        (.main, ⟨⟨P20F.nuMain, 0⟩, TypedV.affW N .ks (Lvm.Har.vs M t.ry), (t.rv.getD 3 z).val M⟩) ::
          (Lvm.M3.tableClaimsR st ev).filter (·.1 == .main))
    (hl2 : tc.1.length = 2) (hcok : ∀ cc ∈ tc.1 ++ tc.2, cOkB zc cc = true) :
    List.Forall₂ (Lvm.Q2.FRelZ M zc b) ((tc.1 ++ tc.2).map .e3)
      (TypedV.typedClaimsN N P20F (Lvm.Har.vs M t.ry) (Lvm.Har.vs M t.rv) (Lvm.Har.vs M t.rr) (t.vR.val M) ++
        Shape.zeroTails ((N.m3 P20F).tableClaims pub ev)) := by
  have hcr : (Lvm.M3.tableClaimsR st ev).filter (·.1 == .crec) = [] := by
    have := congrArg List.length T1
    rw [List.length_map, hl2] at this
    simp only [List.length_cons] at this
    exact List.eq_nil_of_length_eq_zero (by omega)
  have hmain : ∀ e ∈ Lvm.M3.tableClaimsR st ev, e.1 = .main := fun e he => by
    have := List.filter_eq_nil_iff.mp hcr e he
    revert this
    cases e.1 <;> simp
  have hmn : (Lvm.M3.tableClaimsR st ev).filter (·.1 == .main) = Lvm.M3.tableClaimsR st ev :=
    List.filter_eq_self.mpr fun e he => by simp [hmain e he]
  rw [hX]
  refine e3s_rel ?_ ?_ hcok
  · rw [List.map_append, T1, T2, hcr, hmn]
    simp only [TypedV.typedClaimsN, Shape.zeroTails, List.map_append, List.map_cons, List.map_map, List.nil_append,
      List.cons_append, Function.comp_def, List.map_id']
    rw [show P20F.nuRec = 19 from rfl, ← Lvm.QAcc.getD_vals t.rv z hz 2, ← Lvm.QAcc.getD_vals t.rv z hz 0,
      ← Lvm.QAcc.getD_vals t.rv z hz 3]
    rfl
  · intro e he
    simp only [TypedV.typedClaimsN, Shape.zeroTails, List.mem_append, List.mem_cons, List.mem_map,
      List.not_mem_nil, or_false] at he
    rcases he with (rfl | rfl | rfl | rfl) | ⟨e', he', rfl⟩
    · exact ⟨rfl, rfl⟩
    · exact ⟨rfl, rfl⟩
    · exact ⟨rfl, rfl⟩
    · exact ⟨rfl, rfl⟩
    · exact ⟨hmain e' he', rfl⟩

/-- **Q_arith at S2GF is V_S's decision** (`harithT20`'s twin; `nodeSoundFG`'s `harith` at the S2GF instance). -/
theorem harithF20 (S : NodeGF frzF20 QF20 layF20 NTF20) (hhar : harChkBF20 = true) (H : THypX TiF20)
    (vk : RecursionFast.Digest) :
    ∀ c x qm qr, okS vk c x = true → (hdrOf x).b = 1 →
      E2V.GoodTF TiF20 H x qm qr ∧ SBlk qm qr →
      InMapMB (spongeBlocks P20F) (pubLanesX accVF) (lay cfgF20) (sigIn cfgF20) (memF TiF20 x qm qr) vk x qm qr →
      LaneLink P20F (wsC qr) → LinkOk P20F (decode P20F (wsC qr)) →
      Ok (ctxOf TiF20.Q) (memF TiF20 x qm qr) qaF20 (p2P (lay cfgF20) (sigIn cfgF20) (nK cfgF20) 0 P20F) →
      E2V.decideFFX P20F NTF20 vk (hdrOf x).cL (traceBytesB (decode P20F (wsC qr))) = true := by
  intro c x qm qr hok hb hG hin hLL hlink hrun
  -- the program's three parts after Q_sig: the pin, the front, `qarithF`
  have hrun' : Lvm.QSig.Ok (ctxOf TiF20.Q) (memF TiF20 x qm qr)
      (pinF cfgF20.p >>= fun pin ↦ frontF cfgF20 >>= fun o ↦ qarithF cfgF20 tdataF20 pin o)
      (p2P (lay cfgF20) (sigIn cfgF20) (nK cfgF20) 0 P20F) := hrun
  obtain ⟨hPin, hR⟩ := Lvm.Har.okb hrun'
  -- (pointers and outputs as opaque variables: `generalize` would substitute the builders' runs back into the proof
  -- term, and the kernel then evaluates them when it compares cells)
  obtain ⟨q1, hq1⟩ : ∃ q1, (p2P (lay cfgF20) (sigIn cfgF20) (nK cfgF20) 0 P20F).adv
      (pinF cfgF20.p (p2P (lay cfgF20) (sigIn cfgF20) (nK cfgF20) 0 P20F)).2 = q1 := ⟨_, rfl⟩
  obtain ⟨pin, hpinE⟩ : ∃ pin, (pinF cfgF20.p (p2P (lay cfgF20) (sigIn cfgF20) (nK cfgF20) 0 P20F)).1 = pin :=
    ⟨_, rfl⟩
  rw [hq1, hpinE] at hR
  obtain ⟨hFr, hQa⟩ := Lvm.Har.okb hR
  obtain ⟨o, hfr⟩ : ∃ o, (frontF cfgF20 q1).1 = o := ⟨_, rfl⟩
  obtain ⟨q2, hq2⟩ : ∃ q2, q1.adv (frontF cfgF20 q1).2 = q2 := ⟨_, rfl⟩
  rw [hfr, hq2] at hQa
  -- the static facts, the stream, the gate, `vk`
  obtain ⟨htd, hP8, hTE, hTT, hTO, hPW, hOU, hLY, hSE, hML, hGR, hPL, hTR⟩ := harChkF20_sound hhar
  have hle : typedPosF P20F ≤ typedEndX tdataF20 (typedPosF P20F) := by
    obtain ⟨a1, -, -, -⟩ := typedPosX_le tdataF20 (typedPosF P20F)
    have : typedPosF P20F ≤ wGPX (typedPosF P20F) := by simp only [wGPX, zAbcPX, zRPX]; omega
    have := (typedPosX_le tdataF20 (typedPosF P20F)).2.2.2
    have := (typedPosX_le tdataF20 (typedPosF P20F)).2.2.1
    have := (typedPosX_le tdataF20 (typedPosF P20F)).2.1
    omega
  have hS : Lvm.Q1.Streamed (memF TiF20 x qm qr) (sigCF qr) (streamLanes P20F) := streamedF hin.stream hLL
  have hTl : streamLanes P20F = 73001 := by rw [streamLanes, spongeBlocks_P20F.2]
  have hg : (memF TiF20 x qm qr).k (pbB cfgF20) = 1 := hin.flag
  have hvk := Lvm.Har.vk_cellsT (pub747F hin) (okS_vk hok)
  -- `qarithF`: the constants
  unfold qarithF at hQa
  obtain ⟨hZ, hR⟩ := Lvm.Har.okb hQa
  -- (the cells' equalities are stated without the memory: a kernel check of `Cell.val` at `memF TiF20` must not
  -- unfold the memory)
  have ez : (const .E 0 (kc 0) q2).1 = ec q2.e := rfl
  have hzv := (Lvm.Har.constE_val hZ.1).trans ofK_zero
  rw [ez] at hzv
  rw [ez, Lvm.Loop.QRing.constE_adv] at hR
  obtain ⟨hO, hR⟩ := Lvm.Har.okb hR
  have eo : (const .E 1 (kc 0) ⟨q2.k, q2.e + 1⟩).1 = ec (q2.e + 1) := rfl
  have hov := (Lvm.Har.constE_val hO.1).trans ofK_one
  rw [eo] at hov
  rw [eo, Lvm.Loop.QRing.constE_adv] at hR
  obtain ⟨hZK, hR⟩ := Lvm.Har.okb hR
  rw [show (const .K 0 (kc 0) ⟨q2.k, q2.e + 1 + 1⟩).1 = kc q2.k from rfl, Lvm.Har.constK_adv] at hR
  obtain ⟨hOK, hR⟩ := Lvm.Har.okb hR
  rw [show (const .K 1 (kc 0) ⟨q2.k + 1, q2.e + 1 + 1⟩).1 = kc (q2.k + 1) from rfl, Lvm.Har.constK_adv] at hR
  -- the typed phases (`typed_phaseX`), their claims, the shape cell (outputs and pointers opaque)
  obtain ⟨t, q3, ht, hq3e, hTy, hR⟩ := ok_bindV hR
  obtain ⟨tc, q4, htc, hq4e, hTC, hR⟩ := ok_bindV hR
  obtain ⟨ka, q5, hka, hq5e, hKA, hR⟩ := ok_bindV hR
  obtain ⟨kb, q6, hkb, hq6e, hKB, hR⟩ := ok_bindV hR
  obtain ⟨sK, q7, hsKe, hq7e, hSK, hOpen⟩ := ok_bindV hR
  obtain ⟨hsc, hSs, hRr, hDd, hfix⟩ := miniF20 S
  have htyped := typed_phaseX (c := ctxOf TiF20.Q) vk (hdrOf x).cL hS (by rw [hTl]; decide) hg hvk
    (z := ec q2.e) (o := ec (q2.e + 1)) rfl rfl hzv hov P20F rfl htd hsc hSs hRr hDd hfix hP8 hTT _
    (by simp) hTy
  rw [show cfgF20.p = P20F from rfl, show P20F.accV = accVF from rfl] at ht
  rw [hTE, accCA_pubXF (pb := pbB cfgF20) hin.pub, ht] at htyped
  -- the pin (`pin_phase`)
  have hnu : P20F.nuMain = 23 := rfl
  have hpb := pinHPF
  have hpe := pinEndF
  have hqa := pinQaF
  rw [hnu] at hpe hqa
  have epin : pinF cfgF20.p = Lvm.Q2.pinG 23 (phaseLane P20F .commit 1) (phaseLane P20F .commit (23 + 1)) := rfl
  rw [epin] at hPin hpinE
  obtain ⟨hpin, hpinV⟩ := Lvm.Q2.pin_phase hS (nu := 23) (by norm_num) hpb.symm hqa
    (by rw [hTl] at hTT ⊢; omega) (by rw [hqa]; rw [hTl] at hTT ⊢; omega) hPin.1
  rw [hpe] at hpin
  rw [hpinE] at hpinV
  obtain ⟨zP, aP, hzP, hzL⟩ := pinG_fst 23 (phaseLane P20F .commit 1) (phaseLane P20F .commit (23 + 1))
    (p2P (lay cfgF20) (sigIn cfgF20) (nK cfgF20) 0 P20F)
  rw [hpinE] at hzP
  have hpinB : (Lvm.pinD 23 (sigCF qr) ⟨posOf P20F 1, 0, true⟩).1 =
      BlockClaim.point ⟨23, 0⟩ (Lvm.Har.vs (memF TiF20 x qm qr) zP) (aP.val (memF TiF20 x qm qr)) := by
    rw [hzP, cclaim_point] at hpinV
    exact (Prod.mk.inj hpinV).2.symm
  rw [hpinB] at hpin
  -- the front's inputs (E2F-C6's `LvmE2QHarIn`) and its phases
  have hT29 : 29 ≤ streamLanes P20F := by rw [hTl]; norm_num
  obtain ⟨hrw, hrk⟩ := rowWordsF S H hG.1
  have hch := childOkF S H hok hb hG
  have hsb := sBits_onC (outsOnF S H hG.1)
  obtain ⟨hnb, hn, hsbv⟩ := frontIns hS hT29 (hbitsF S H hG.1) hch hsb accVF vk (hdrOf x).cL rfl rfl
  have hpow := powOkF S H hG.1 (pw := powF20) rfl hS (fun a ha => ha) hPW
  have hh : (pubOfA accVF vk (hdrOf x).cL (sigCF qr)).h = (List.range 4).map fun l => (memF TiF20 x qm qr).k (Lvm.Har.hLane l) :=
    Lvm.Har.pub_h hS hT29 vk (hdrOf x).cL
  have hsmE : TypedV.smallT P20F (pubOfA accVF vk (hdrOf x).cL (sigCF qr)) =
      decide ((pubOfA accVF vk (hdrOf x).cL (sigCF qr)).n ≤ 2 ^ 18) := smallT_P20F _
  obtain ⟨tp, co, lo, htape, hcall, hlink, hfrel, hmbv⟩ := front_phasesF hS hTO hg hpow hrw hrk
    (pubOfA accVF vk (hdrOf x).cL (sigCF qr)) hnb hn hsbv hh (ec q2.e)
    (TypedV.smallT P20F (pubOfA accVF vk (hdrOf x).cL (sigCF qr)))
    (fun h => by rw [hsmE] at h; exact of_decide_eq_true h) hFr
  rw [hfr] at hfrel hmbv
  -- the shape: `σ` from `n' − 1`'s bits 18, 19, the `K` cell `sK` (`(1 + b₁₈)(1 + b₁₉)`)
  have hσ := Lvm.Har.sigma_val o.mb _ hmbv hn.1 hn.2
  rw [← hsmE] at hσ
  have hzkv : (kc q2.k).val (memF TiF20 x qm qr) = 0 := by
    have e := const_val hZK.1
    rw [show (const .K 0 (kc 0) ⟨q2.k, q2.e + 1 + 1⟩).1 = kc q2.k from rfl, ofK_zero] at e
    exact e
  have hokv : (kc (q2.k + 1)).val (memF TiF20 x qm qr) = 1 := by
    have e := const_val hOK.1
    rw [show (const .K 1 (kc 0) ⟨q2.k + 1, q2.e + 1 + 1⟩).1 = kc (q2.k + 1) from rfl, ofK_one] at e
    exact e
  have hsK : sK.val (memF TiF20 x qm qr) =
      if TypedV.smallT P20F (pubOfA accVF vk (hdrOf x).cL (sigCF qr)) then 1 else 0 := by
    rw [← hsKe, mulAdd_spec hSK.1, ← hka, ← hkb, Lvm.Har.addK_val hKA.1, Lvm.Har.addK_val hKB.1, hzkv, ofK_one, add_zero, ← hσ]
    ring
  -- the opening's context, the pin as `FRel`
  have hF : Lvm.Q2.FCtxOk (memF TiF20 x qm qr)
      ⟨ec q2.e, ec (q2.e + 1), kc q2.k, ⟨kc q2.k, kc q2.k⟩, ⟨kc (q2.k + 1), kc q2.k⟩, false⟩ := by
    refine ⟨hzv, hov, hzkv, rfl, rfl, ?_, ⟨rfl, rfl⟩, ?_⟩
    · show (⟨((kc (q2.k + 1)).val (memF TiF20 x qm qr)).c₀, ((kc q2.k).val (memF TiF20 x qm qr)).c₀⟩ : FE2) = 1
      rw [hokv, hzkv]; rfl
    · show (⟨((kc q2.k).val (memF TiF20 x qm qr)).c₀, ((kc q2.k).val (memF TiF20 x qm qr)).c₀⟩ : FE2) = 0
      rw [hzkv]; rfl
  have hpsp := Lvm.Q2.pinG_spec (c := ctxOf TiF20.Q) hS (nu := 23) (qz := phaseLane P20F .commit 1)
    (qa := phaseLane P20F .commit (23 + 1)) (by rw [hTl] at hTT ⊢; omega) (by rw [hqa]; rw [hTl] at hTT ⊢; omega) _
    hPin.1
  rw [hpinE, hzP, cclaim_point] at hpsp
  have hzl : zP.length = 23 := by
    rw [hzL]; simp
  have hpt : pin.cw = .point ⟨CMain.nu20, 0⟩ (Lvm.Q2.pinPt pin) := by rw [hzP]; rfl
  have hpinR : Lvm.Q2.FRel (memF TiF20 x qm qr) CMain.nu20 (.e3 pin)
      (BlockClaim.point ⟨23, 0⟩ (Lvm.Har.vs (memF TiF20 x qm qr) zP) (aP.val (memF TiF20 x qm qr))) := by
    refine ⟨?_, ?_⟩
    · rw [hzP]; simp [Lvm.Har.WF1, hzl]
    · rw [hzP, cclaim_point]
  -- the claims: the typed phases', then the front's
  have htrel : List.Forall₂ (Lvm.Q2.FRelZ (memF TiF20 x qm qr) (ec q2.e)
      (TypedV.smallT P20F (pubOfA accVF vk (hdrOf x).cL (sigCF qr)))) ((tc.1 ++ tc.2).map .e3)
      (TypedV.typedClaimsN NTF20 P20F (Lvm.Har.vs (memF TiF20 x qm qr) t.ry) (Lvm.Har.vs (memF TiF20 x qm qr) t.rv)
        (Lvm.Har.vs (memF TiF20 x qm qr) t.rr) (t.vR.val (memF TiF20 x qm qr)) ++
       Shape.zeroTails ((NTF20.m3 P20F).tableClaims (pubOfA accVF vk (hdrOf x).cL (sigCF qr))
         (t.tab.map fun e => (Lvm.Har.vs (memF TiF20 x qm qr) e.1, Lvm.Har.vs (memF TiF20 x qm qr) e.2)))) := by
    have hsh := typedGX_shape (c := ctxOf TiF20.Q) (M := memF TiF20 x qm qr) _ _ _ _ _ _ _ hTy.1
    rw [show cfgF20.p = P20F from rfl, show P20F.accV = accVF from rfl, ht] at hsh
    obtain ⟨hry, hrr, htabl⟩ := hsh
    rw [show cfgF20.p = P20F from rfl] at htc hTC
    have hok := typedClaimsC_ok (c := ctxOf TiF20.Q) (M := memF TiF20 x qm qr) (zc := ec q2.e) (nu := P20F.nuMain)
      rfl hTR hry hrr htabl _ hTC.1
    rw [htc] at hok
    obtain ⟨hl2, hcok⟩ := hok
    obtain ⟨T1, T2, -⟩ := Lvm.Har.typedClaimsC_val hzv hov htd P20F.nuMain (layout0 P20F).s t NTF20.mbT hSs _ hTC.1
    rw [htc] at T1 T2
    exact typed_relF hzv (by rw [Lvm.Har.m3_tableClaimsT, hsc]) T1 T2 hl2 hcok
  have hrel := List.rel_append htrel hfrel
  beta_reduce at hrel
  -- the opening's static inputs
  have hopenU : posOf P20F (phaseItem0 P20F .openMain) =
      8 * (cfgMainF P20F (Lvm.Har.posBase cfgF20) (Lvm.Har.pwBase cfgF20)).U := by
    rw [cfgMainF_U]; exact hOU
  have hlayO : Lvm.Har.LayOk (cfgMainF P20F (Lvm.Har.posBase cfgF20) (Lvm.Har.pwBase cfgF20)) (streamLanes P20F) = true := by
    rw [layOkF_pb P20F _ _ (fun _ => 0) (fun _ => 0)]; exact hLY
  have hposO : Lvm.Har.PosOk (cfgMainF P20F (Lvm.Har.posBase cfgF20) (Lvm.Har.pwBase cfgF20)) (memF TiF20 x qm qr) (sigCF qr) 0
      (cfgMainF P20F (Lvm.Har.posBase cfgF20) (Lvm.Har.pwBase cfgF20)).levels ((cfgMainF P20F (Lvm.Har.posBase cfgF20) (Lvm.Har.pwBase cfgF20)).U + 15) := by
    have hPL' : Lvm.Fin.PosLanes P20F (cfgMainF P20F (Lvm.Har.posBase cfgF20) (Lvm.Har.pwBase cfgF20)).g
        (cfgMainF P20F (Lvm.Har.posBase cfgF20) (Lvm.Har.pwBase cfgF20)).ood
        (cfgMainF P20F (Lvm.Har.posBase cfgF20) (Lvm.Har.pwBase cfgF20)).levels
        ((cfgMainF P20F (Lvm.Har.posBase cfgF20) (Lvm.Har.pwBase cfgF20)).U + 15) 0 := by
      rw [cfgMainF_g, cfgMainF_ood, cfgMainF_levels, cfgMainF_U]; exact hPL
    exact posOk_ofG P20F cfgF20 rfl _ 0 (fun i => by rw [Nat.zero_add, cfgMainF_pb]) hPL' streamOk_P20F hLL hQF20
      (posCellsF S H hok hb hG)
  have hpwO : Lvm.Har.PwOk (cfgMainF P20F (Lvm.Har.posBase cfgF20) (Lvm.Har.pwBase cfgF20)) (memF TiF20 x qm qr) 0
      (cfgMainF P20F (Lvm.Har.posBase cfgF20) (Lvm.Har.pwBase cfgF20)).levels := by
    intro i hi _
    rw [cfgMainF_levels] at hi
    rw [cfgMainF_pw, cfgMainF_g, Nat.zero_add]
    have e := pw_onC (outsOnF S H hG.1) hGR i (lt_of_lt_of_le hi hML)
    exact e
  have hendO : 8 * Lvm.Har.stackEndL (cfgMainF P20F (Lvm.Har.posBase cfgF20) (Lvm.Har.pwBase cfgF20)).g
      (cfgMainF P20F (Lvm.Har.posBase cfgF20) (Lvm.Har.pwBase cfgF20)).ood (cfgMainF P20F (Lvm.Har.posBase cfgF20) (Lvm.Har.pwBase cfgF20)).levels
      ((cfgMainF P20F (Lvm.Har.posBase cfgF20) (Lvm.Har.pwBase cfgF20)).U + 15) = (sigCF qr).size := by
    rw [sigCF_size hLL, stackEnd_cfgMainF]; exact hSE
  have hq7 : 1 ≤ q7.e := by
    have h3 : 1 ≤ q3.e := le_trans (by simp) hq3e
    omega
  rw [show cfgF20.p = P20F from rfl] at hOpen
  -- `core_of_phasesF`, the opening by `open_phase`
  refine Lvm.Har.decideFFX_of (acc := (Lvm.VEq.pubXF x).accIn) P20F NTF20 vk (hdrOf x).cL _ ?_
    (phiF20_acc S H hG.1)
  refine Lvm.Har.core_of_phasesF P20F _ NTF20.m3 vk (hdrOf x).cL (sigCF qr) (RS.startH (headerBytesP P20F)) rfl hbF
    hpin htyped htape hcall hlink ?_
  intro s hs hsok
  rw [show P20F.accV = accVF from rfl]
  have key := Lvm.Q2.open_phase P20F (cfgMainF P20F (Lvm.Har.posBase cfgF20) (Lvm.Har.pwBase cfgF20)) rfl rfl rfl rfl rfl hF pin hpt _ _
    hpinR _ _ _ hrel o.mb hσ sK (kc (pbB cfgF20)) hsK hS hlayO (by rw [Cell.val_K, hg, ofK_one]) rfl hposO hpwO hendO
    hq7 hOpen s (hs.trans hopenU) hsok
  rw [hnu] at key
  exact key

end Lvm.E2Q
end

-- ===== from `LvmE2QNodeF` =====

section
set_option autoImplicit false
namespace Lvm.E2Q
open RecursionFast Lvm Lvm.ASM Lvm.Typed

/-- **The S2GF guard's facts.** -/
abbrev SFF20 : Prop := NodeGF frzF20 QF20 layF20 NTF20 ∧ harChkBF20 = true ∧ Lvm.T.oneOkB layF20 = true

/-- **The guard's facts** from `staticOkBF20 = true`. -/
theorem sfF20 (h : staticOkBF20 = true) : SFF20 := by
  simp only [staticOkBF20, Bool.and_eq_true] at h
  exact ⟨nodeGF_of QF20_eq rfl rfl rfl h.1.1.1.1 h.1.1.1.2 h.1.1.2, h.1.2, h.2⟩

/-- **Statement 16 (`nodeF20`)**: `NodeSound` of the S2GF circuit for `VSFX NTF20`, on stream-block pairs of the
S2GF good relation, with the left child read at `P20F` (roll 11's `nodeT20` shape). -/
theorem nodeF20 (S : SFF20) (H : THypX TiF20) (vk : RecursionFast.Digest) :
    NodeSound (Lvm.E2V.VSFX NTF20) vk (fun x qm qr ↦ Lvm.E2V.GoodTF TiF20 H x qm qr ∧ Lvm.NS.SBlk qm qr)
      (Lvm.NS.childSP P20F) :=
  nodeSoundFG (F := frzF20) (Q := QF20) (tl := layF20) (N := NTF20) S.1 H vk NTF20 qaF20 QF20_qa
    (harithF20 S.1 S.2.1 H vk)

end Lvm.E2Q
end
