-- New for lvm2 E2-FT (E2F-C): the S2GF node program's Q_arith is V_S's decision (`harithF20`, roll 11's
-- `harithT20` at S2GF): from Q_arith's segments on a good pair's memory, `decideFFX P20F NTF20` accepts the child's
-- stream, composed by `core_of_phasesF` from the gadgets' phase lemmas (pin, typed, tape + wire, `KS`, `KS` link,
-- the opening) and `decideFFX_of`; the typed claims stand for V's (`typedClaimsC_ok`, `e3s_rel`).
import LvmE2QInst
import LvmE2QNodeG
import LvmE2QHarTop
import LvmE2QHarPos
import LvmQTypedHarB
import LvmE2QTypedPhase
import LvmQTypedHarS
import LvmE2QHarFront
import LvmE2QHarIn
import LvmE2QHarPosOk

/-!
# Q_arith at S2GF (`harithF20`)

* **`qaF20`**: Q_arith of the S2GF node program (the root pin, the `E2` front, `qarithF`), so that
  `QF20 = toProgram (nK cfgF20) 0 (qprogP P20F (lay cfgF20) (sigIn cfgF20) qaF20)` (`QF20_qa`).
* **`harithF20`**: on a stream-block pair of the S2GF good relation whose memory carries the input map, with Q_link's
  `LaneLink`/`LinkOk`, Q_arith's segments ⇒ `decideFFX P20F NTF20 vk c_L Σ = true` (`nodeSoundFG`'s `harith`).
-/

set_option autoImplicit false

namespace Lvm.E2Q

open RecursionFast Lvm Lvm.T Lvm.ASM Lvm.Replay Lvm.Loop Lvm.Loop.Build Lvm.QLink Lvm.QSig Lvm.QAsm Lvm.NS
open Lvm.Typed LeanVM.Protocol

instance posLanesDec (p : Params) (g : ℕ) (ood : Bool) (Ls : List Level) (V k0 : ℕ) :
    Decidable (Lvm.Fin.PosLanes p g ood Ls V k0) := by
  unfold Lvm.Fin.PosLanes; infer_instance

/-- **The typed claims' static data at S2GF**, decided in the guard: the relayout's block, the regions (`σ′`,
committed, `KS` aliases) and the mini-bus's committed columns are regular blocks, the regions at most `2^21` words,
the tables at most `mbR` and `ν` rounds, no `C_rec` column. -/
def typedRegB (T : Lvm.QTyped.TData) (sOff : ℕ) : Bool :=
  decide (Lvm.QShape.RegP ⟨19, sOff⟩) &&
    (T.sig ++ T.com ++ T.ks).all (fun R => decide (R.log ≤ 21) && decide (Lvm.QShape.RegP ⟨R.log, R.off⟩)) &&
    T.mbS.all fun s => decide (s.τ ≤ T.mbR) && decide (s.τ ≤ CMain.nu20) &&
      s.cols.all fun c => match c with
        | some (rec, off) => !rec && decide (Lvm.QShape.RegP ⟨s.τ, off⟩)
        | none => true

theorem typedRegB_sound {T : Lvm.QTyped.TData} {sOff : ℕ} (h : typedRegB T sOff = true) :
    Lvm.QShape.RegP ⟨19, sOff⟩ ∧ (∀ R ∈ T.sig ++ T.com ++ T.ks, R.log ≤ 21 ∧ Lvm.QShape.RegP ⟨R.log, R.off⟩) ∧
      ∀ s ∈ T.mbS, s.τ ≤ T.mbR ∧ s.τ ≤ CMain.nu20 ∧
        ∀ c ∈ s.cols, ∀ rec off, c = some (rec, off) → rec = false ∧ Lvm.QShape.RegP ⟨s.τ, off⟩ := by
  simp only [typedRegB, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true] at h
  obtain ⟨⟨h1, h2⟩, h3⟩ := h
  refine ⟨h1, h2, fun s hs => ⟨(h3 s hs).1.1, (h3 s hs).1.2, fun c hc rec off e => ?_⟩⟩
  have := (h3 s hs).2 c hc
  rw [e] at this
  simpa using this

/-- **The HAR's static checks at S2GF** (roll 11's `harChkB`: the regions and the phases' positions in `Σ`), decided
by the S2GF guard (`staticOkBF20`, natively): the circuit's typed regions are V_S's (`tdMatchB`), the typed phases
start on a lane boundary, end where the tape phase starts, and inside the stream; the opening starts inside the stream
(the front's lane bounds); every proof-of-work answer of the front is streamed with `g ≤ 64` (`powOkF`'s `hpw`).
(The opening's claim shapes follow with `open_phase`.) -/
def harChkBF20 : Bool :=
  Lvm.QTyped.tdMatchB tdataF20 NTF20 && typedPosF P20F % 8 == 0 &&
    typedEndX tdataF20 (typedPosF P20F) == posOf P20F (phaseItem0 P20F .tape) &&
    decide (typedEndX tdataF20 (typedPosF P20F) + 40 ≤ 8 * streamLanes P20F) &&
    decide (posOf P20F (phaseItem0 P20F .openMain) + 48 ≤ 8 * streamLanes P20F) &&
    (powFront P20F).all (fun a => decide (a.1 + 2 < streamLanes P20F) && decide (a.2 ≤ 64)) &&
    posOf P20F (phaseItem0 P20F .openMain) == 8 * (phaseLane P20F .openMain 0 - 5) &&
    Lvm.Har.LayOk (cfgMainF P20F (fun _ => 0) (fun _ => 0)) (streamLanes P20F) &&
    8 * Lvm.Har.stackEndL P20F.grind P20F.mainOod P20F.mainLevels (phaseLane P20F .openMain 0 - 5 + 15) ==
      hashedLen P20F &&
    decide (P20F.mainLevels.length ≤ (Lvm.QLink.opens P20F).length) && decide (1 ≤ 64 - P20F.grind) &&
    decide (Lvm.Fin.PosLanes P20F P20F.grind P20F.mainOod P20F.mainLevels (phaseLane P20F .openMain 0 - 5 + 15) 0) &&
    typedRegB tdataF20 (layout0 P20F).s

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

theorem cfgMainF_U (p : Params) (pb pw : Nat → Nat) : (cfgMainF p pb pw).U = phaseLane p .openMain 0 - 5 := rfl

theorem stackEnd_cfgMainF (p : Params) (pb pw : Nat → Nat) :
    Lvm.Har.stackEndL (cfgMainF p pb pw).g (cfgMainF p pb pw).ood (cfgMainF p pb pw).levels ((cfgMainF p pb pw).U + 15) =
      Lvm.Har.stackEndL p.grind p.mainOod p.mainLevels (phaseLane p .openMain 0 - 5 + 15) := rfl

theorem cfgMainF_levels (p : Params) (pb pw : Nat → Nat) : (cfgMainF p pb pw).levels = p.mainLevels := rfl
theorem cfgMainF_g (p : Params) (pb pw : Nat → Nat) : (cfgMainF p pb pw).g = p.grind := rfl
theorem cfgMainF_pw (p : Params) (pb pw : Nat → Nat) : (cfgMainF p pb pw).pw = pw := rfl
theorem cfgMainF_pb (p : Params) (pb pw : Nat → Nat) (i : Nat) : (cfgMainF p pb pw).pb i = pb i := rfl
theorem cfgMainF_ood (p : Params) (pb pw : Nat → Nat) : (cfgMainF p pb pw).ood = p.mainOod := rfl

/-- `LayOk` of `C_main`'s opening does not read the position and PoW bases. -/
theorem layOkF_pb (p : Params) (pb pw pb' pw' : Nat → Nat) (T : Nat) :
    Lvm.Har.LayOk (cfgMainF p pb pw) T = Lvm.Har.LayOk (cfgMainF p pb' pw') T :=
  Lvm.Har.layOk_pb _ _ _ pb pb' _ _ _ _ pw pw' T

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

/-- A bind's output and next pointer as opaque variables (`generalize` would substitute the builder's run back into
the proof term, and the kernel then evaluates it). -/
theorem ok_bindV {c : Ctx} {M : Mem} {α β : Type} {m : BM α} {f : α → BM β} {p : Ptr}
    (h : Lvm.QSig.Ok c M (m >>= f) p) :
    ∃ a q, (m p).1 = a ∧ p.e ≤ q.e ∧ Lvm.QSig.Ok c M m p ∧ Lvm.QSig.Ok c M (f a) q := by
  obtain ⟨h1, h2⟩ := Lvm.Har.okb h
  exact ⟨_, _, rfl, Lvm.Har.adv_e_le _ _, h1, h2⟩

theorem cclaim_point (M : Mem) (blk : Placement) (z : List Cell) (a : Cell) :
    Lvm.Har.CClaim.val M ⟨.main, .point blk z, a⟩ = (.main, BlockClaim.point blk (Lvm.Har.vs M z) (a.val M)) := rfl

/-- The small shape at `P20F` (generic in `pub`: a closed `pub` would make the kernel evaluate its `n`). -/
theorem smallT_P20F (pub : Pub) : TypedV.smallT P20F pub = decide (pub.n ≤ 2 ^ 18) := rfl

theorem mapB_len {α β : Type} (f : α → BM β) : ∀ (l : List α) (p : Ptr), (Lvm.Q2.mapB f l p).1.length = l.length
  | [], _ => rfl
  | a :: l, p => by
    simp only [Lvm.Q2.mapB, bind_apply, pure_apply, List.length_cons]
    rw [mapB_len f l]

/-- The pin gadget's claim is a point claim on `⟨ν, 0⟩` (generic: no builder run). -/
theorem pinG_fst (nu qz qa : Nat) (p : Ptr) :
    ∃ z a, (Lvm.Q2.pinG nu qz qa p).1 = ⟨.main, .point ⟨nu, 0⟩ z, a⟩ ∧ z.length = (List.range nu).length :=
  ⟨_, _, rfl, mapB_len _ _ _⟩

/-! ## The typed phases' claims (`htrel`) -/

/-- A claim off `D` and the ring by its form (its tail `0` in both shapes). -/
def tailFreeB (cc : Lvm.Har.CClaim) : Bool :=
  match cc.cw with
  | .point blk _ => blk != ⟨22, 0⟩
  | .ring blk _ _ => blk != ⟨CMain.nu20, 0⟩
  | .sum _ _ => true

/-- **A claim the opening takes as it is**: well formed at `ν = 23`, regular in the small shape, tail-free. -/
def cOkB (zc : Cell) (cc : Lvm.Har.CClaim) : Bool :=
  Lvm.Har.WF1 CMain.nu20 cc && Lvm.QShape.ZWF zc cc && tailFreeB cc

theorem tailC_free {M : Mem} {cc : Lvm.Har.CClaim} (h : tailFreeB cc = true) : Lvm.QShape.tailC M cc = 0 := by
  unfold tailFreeB at h
  unfold Lvm.QShape.tailC
  rcases hcw : cc.cw with ⟨blk, zl⟩ | ⟨blk, pt, cs⟩ | ⟨nu, parts⟩ <;> rw [hcw] at h <;> simp_all

/-- **Claims of `C_main` taken as they are** stand for V's claims with tail `0` (`FRelZ`, both shapes). -/
theorem e3s_rel {M : Mem} {zc : Cell} {b : Bool} : ∀ {cs : List Lvm.Har.CClaim} {cls : List (Com × BlockClaim × FE)},
    cs.map (Lvm.Har.CClaim.val M) = cls.map (fun e => (e.1, e.2.1)) → (∀ e ∈ cls, e.1 = .main ∧ e.2.2 = 0) →
    (∀ cc ∈ cs, cOkB zc cc = true) → List.Forall₂ (Lvm.Q2.FRelZ M zc b) (cs.map .e3) cls
  | [], [], _, _, _ => .nil
  | cc :: cs, e :: cls, h, he, hc => by
    simp only [List.map_cons, List.cons.injEq] at h
    have hc0 := hc cc (List.mem_cons_self ..)
    simp only [cOkB, Bool.and_eq_true] at hc0
    obtain ⟨⟨hw, hz⟩, ht⟩ := hc0
    obtain ⟨hm, h0⟩ := he e (List.mem_cons_self ..)
    exact .cons ⟨⟨hm, hw, (congrArg Prod.snd h.1).symm⟩, hz, fun _ => by rw [h0, tailC_free ht]⟩
      (e3s_rel h.2 (fun e' he' => he e' (List.mem_cons_of_mem _ he'))
        (fun c' hc' => hc c' (List.mem_cons_of_mem _ hc')))
  | [], _ :: _, h, _, _ => by simp at h
  | _ :: _, [], h, _, _ => by simp at h

theorem hs_bind_true {c : Ctx} {M : Mem} {α β : Type} {m : BM α} {f : α → BM β} {Q : β → Prop}
    (h : ∀ a, Lvm.Har.Hs c M (f a) Q) : Lvm.Har.Hs c M (m >>= f) Q :=
  Lvm.Har.hs_bind (hs_true m) fun a _ => h a

theorem hs_seqAll_snd {c : Ctx} {M : Mem} {α β γ : Type} {f : α → BM (β × γ)} (g : α → γ)
    (hf : ∀ a, Lvm.Har.Hs c M (f a) (fun x => x.2 = g a)) :
    ∀ l : List α, Lvm.Har.Hs c M (seqAll (l.map f)) (fun ps => ps.map (·.2) = l.map g)
  | [] => Lvm.Har.hs_pure rfl
  | a :: l => Lvm.Har.hs_bind (hf a) fun x hx => Lvm.Har.hs_bind (hs_seqAll_snd g hf l) fun xs hxs =>
      Lvm.Har.hs_pure (by rw [List.map_cons, List.map_cons, hx, hxs])

/-- A region claim's form: a sum over the regions' blocks at `r_y`'s low coordinates. -/
theorem regClaimG_shape {c : Ctx} {M : Mem} (z o : Cell) (com : Com) (nu : ℕ) (rs : List Lvm.QTyped.TReg)
    (ry : List Cell) (v : Cell) :
    Lvm.Har.Hs c M (Lvm.QTyped.regClaimG z o com nu rs ry v) (fun cc => ∃ parts : List (Cell × Placement × List Cell),
      cc = ⟨com, .sum nu parts, v⟩ ∧
        parts.map (·.2) = rs.map fun R => ((⟨R.log, R.off⟩ : Placement), ry.take R.log)) := by
  unfold Lvm.QTyped.regClaimG
  refine Lvm.Har.hs_bind (hs_seqAll_snd (fun R => ((⟨R.log, R.off⟩ : Placement), ry.take R.log))
    (fun R => hs_bind_true fun _ => Lvm.Har.hs_pure rfl) rs) fun parts hp => Lvm.Har.hs_pure ⟨parts, rfl, hp⟩

theorem regClaim_ok {zc : Cell} {com : Com} {rs : List Lvm.QTyped.TReg} {ry : List Cell} {v : Cell}
    {parts : List (Cell × Placement × List Cell)} (hry : ry.length = 21)
    (hrs : ∀ R ∈ rs, R.log ≤ 21 ∧ Lvm.QShape.RegP ⟨R.log, R.off⟩)
    (hp : parts.map (·.2) = rs.map fun R => ((⟨R.log, R.off⟩ : Placement), ry.take R.log)) :
    cOkB zc ⟨com, .sum CMain.nu20 parts, v⟩ = true := by
  have key : ∀ x ∈ parts, ∃ R ∈ rs, x.2 = ((⟨R.log, R.off⟩ : Placement), ry.take R.log) := fun x hx => by
    have : x.2 ∈ parts.map (·.2) := List.mem_map_of_mem hx
    rw [hp] at this
    obtain ⟨R, hR, e⟩ := List.mem_map.mp this
    exact ⟨R, hR, e.symm⟩
  simp only [cOkB, tailFreeB, Lvm.Har.WF1, Lvm.QShape.ZWF, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true,
    and_true]
  refine ⟨⟨le_refl _, fun x hx => ?_⟩, trivial, fun x hx => ?_⟩
  · obtain ⟨R, hR, e⟩ := key x hx
    rw [e]
    have := (hrs R hR).1
    simp only [List.length_take, hry]
    exact ⟨by show R.log ≤ CMain.nu20; simp only [CMain.nu20]; omega, by show min R.log 21 = R.log; omega⟩
  · obtain ⟨R, hR, e⟩ := key x hx
    rw [e]; exact (hrs R hR).2

theorem zip_map_take {α β γ : Type} (pts : List γ) (τ : α → ℕ) : ∀ (S : List α) (E : List β),
    ∀ x ∈ S.zip ((S.zip E).map fun y => (pts.take (τ y.1), y.2)), x.2.1.length = min pts.length (τ x.1)
  | [], _ => by simp
  | _ :: _, [] => by simp
  | a :: S, e :: E => by
    intro x hx
    simp only [List.zip_cons_cons, List.map_cons, List.mem_cons] at hx
    rcases hx with rfl | hx
    · simp [Nat.min_comm]
    · exact zip_map_take pts τ S E x hx

/-- The mini-bus's table points have `min R τ` coordinates. -/
theorem tabG_pts {c : Ctx} {M : Mem} (S : List Lvm.Har.TShape) (R P : ℕ) (z o g : Cell) (bc : Lvm.Har.BusC) :
    Lvm.Har.Hs c M (Lvm.Har.tabG S R P z o g bc) (fun out => ∀ x ∈ S.zip out, x.2.1.length = min R x.1.τ) := by
  unfold Lvm.Har.tabG
  iterate 20 refine hs_bind_true fun _ => ?_
  refine Lvm.Har.hs_bind (hs_true _) fun r _ => ?_
  iterate 4 refine hs_bind_true fun _ => ?_
  refine Lvm.Har.hs_pure fun x hx => ?_
  have := zip_map_take (((List.range R).map (Lvm.Har.chC r.2)).reverse) (·.τ) S _ x hx
  simpa using this

theorem wireGX_ry {c : Ctx} {M : Mem} (z o g : Cell) (T : Lvm.QTyped.TData) (pb P n : ℕ) (v : List Cell) :
    Lvm.Har.Hs c M (wireGX z o g T pb P n v) (fun w => w.1.length = 21) := by
  unfold wireGX
  iterate 17 refine hs_bind_true fun _ => ?_
  exact Lvm.Har.hs_pure (by simp)

theorem relayG_rr {c : Ctx} {M : Mem} (z o g : Cell) (T : Lvm.QTyped.TData) (P : ℕ) (ry : List Cell) (vS : Cell) :
    Lvm.Har.Hs c M (Lvm.QTyped.relayG z o g T P ry vS) (fun r => r.1.length = 19) := by
  unfold Lvm.QTyped.relayG
  iterate 6 refine hs_bind_true fun _ => ?_
  exact Lvm.Har.hs_pure (by simp)

/-- **The typed gadget's points**: `r_y` (21), `r''` (19), the tables' (`min mbR τ`). -/
theorem typedGX_shape {c : Ctx} {M : Mem} (T : Lvm.QTyped.TData) (pb P accV : ℕ) (z o : Cell) :
    Lvm.Har.Hs c M (typedGX T pb P accV z o) (fun t => t.ry.length = 21 ∧ t.rr.length = 19 ∧
      ∀ x ∈ T.mbS.zip t.tab, x.2.1.length = min T.mbR x.1.τ) := by
  unfold typedGX
  refine hs_bind_true fun zr => Lvm.Har.hs_bind (wireGX_ry _ _ _ _ _ _ _ _) fun w hw => ?_
  refine Lvm.Har.hs_bind (relayG_rr _ _ _ _ _ _ _) fun r hr => hs_bind_true fun _ => ?_
  unfold Lvm.QTyped.miniG
  refine Lvm.Har.hs_bind (Lvm.Har.hs_bind (hs_true _) fun bus _ => Lvm.Har.hs_bind (tabG_pts _ _ _ _ _ _ _)
    fun tab ht => hs_bind_true fun _ => Lvm.Har.hs_pure (show ∀ x ∈ T.mbS.zip (bus, tab).2, _ from ht))
    fun mb hmb => Lvm.Har.hs_pure ⟨hw, hr, hmb⟩

/-- **The typed claims are taken as they are**: two in the first list (no `C_rec` table claim), every claim
`cOkB`. -/
theorem typedClaimsC_ok {c : Ctx} {M : Mem} {z o zc : Cell} {T : Lvm.QTyped.TData} {sOff : ℕ}
    {t : Lvm.QTyped.TypedC} {nu : ℕ} (hnu : nu = CMain.nu20) (hreg : typedRegB T sOff = true)
    (hry : t.ry.length = 21) (hrr : t.rr.length = 19) (hl : ∀ x ∈ T.mbS.zip t.tab, x.2.1.length = min T.mbR x.1.τ) :
    Lvm.Har.Hs c M (Lvm.QTyped.typedClaimsC z o T nu sOff t)
      (fun tc => tc.1.length = 2 ∧ ∀ cc ∈ tc.1 ++ tc.2, cOkB zc cc = true) := by
  subst hnu
  obtain ⟨h19, hR, hS⟩ := typedRegB_sound hreg
  have htab : ∀ cc ∈ Lvm.Har.tabClaims T.mbS t.tab z, cOkB zc cc = true ∧ cc.com = .main := by
    intro cc hcc
    unfold Lvm.Har.tabClaims at hcc
    obtain ⟨x, hx, hcc⟩ := List.mem_flatMap.mp hcc
    obtain ⟨ci, hci, hcc⟩ := List.mem_filterMap.mp hcc
    have hs := hS x.1 (List.of_mem_zip hx).1
    have hcm : ci.1 ∈ x.1.cols := List.mem_of_getElem? (List.mem_zipIdx_iff_getElem?.mp hci)
    rcases hc : ci.1 with _ | ⟨rec, off⟩
    · rw [hc] at hcc; exact absurd hcc (by simp)
    · rw [hc] at hcc hcm
      obtain ⟨hrec, hreg'⟩ := hs.2.2 _ hcm rec off rfl
      subst hrec
      simp only [Option.some.injEq] at hcc
      subst hcc
      have hlen := hl x hx
      have hne : (⟨x.1.τ, off⟩ : Placement) ≠ ⟨22, 0⟩ := fun e => by
        have := hreg'.2.2.1; rw [show off = 0 from congrArg Placement.index e] at this; simp at this
      refine ⟨?_, rfl⟩
      simp only [cOkB, tailFreeB, Lvm.Har.WF1, Lvm.QShape.ZWF, Bool.and_eq_true, decide_eq_true_eq, hne,
        ↓reduceIte, bne_iff_ne, ne_eq, not_false_eq_true, and_true]
      refine ⟨⟨hs.2.1, ?_⟩, hreg'⟩
      rw [hlen]; exact Nat.min_eq_right hs.1
  unfold Lvm.QTyped.typedClaimsC
  refine Lvm.Har.hs_bind (regClaimG_shape _ _ _ _ _ _ _) fun cS ⟨pS, eS, hpS⟩ => ?_
  refine Lvm.Har.hs_bind (regClaimG_shape _ _ _ _ _ _ _) fun cC ⟨pC, eC, hpC⟩ => ?_
  refine Lvm.Har.hs_bind (regClaimG_shape _ _ _ _ _ _ _) fun cK ⟨pK, eK, hpK⟩ => Lvm.Har.hs_pure ?_
  have hnil : (Lvm.Har.tabClaims T.mbS t.tab z).filter (·.com == .crec) = [] :=
    List.filter_eq_nil_iff.mpr fun cc hcc => by simp [(htab cc hcc).2]
  refine ⟨by simp [hnil], fun cc hcc => ?_⟩
  rw [hnil] at hcc
  have h19' : (⟨Lvm.QTyped.tR, sOff⟩ : Placement) ≠ ⟨22, 0⟩ := by simp
  rcases List.mem_append.mp hcc with h | h
  · rcases List.mem_cons.mp h with rfl | h
    · simp only [cOkB, tailFreeB, Lvm.Har.WF1, Lvm.QShape.ZWF, Bool.and_eq_true, decide_eq_true_eq, hrr, h19',
        ↓reduceIte, bne_iff_ne, ne_eq, not_false_eq_true, and_true]
      exact ⟨by decide, h19⟩
    · rcases List.mem_cons.mp h with rfl | h
      · rw [eS]; exact regClaim_ok hry (fun R hR' => hR R (by simp [hR'])) hpS
      · simp at h
  · rcases List.mem_cons.mp h with rfl | h
    · rw [eC]; exact regClaim_ok hry (fun R hR' => hR R (by simp [hR'])) hpC
    · rcases List.mem_cons.mp h with rfl | h
      · rw [eK]; exact regClaim_ok hry (fun R hR' => hR R (by simp [hR'])) hpK
      · exact (htab cc (List.mem_filter.mp h).1).1

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
  obtain ⟨hnb, hn, hsbv⟩ := frontIns hS hT29 (hbitsF S H hG.1) hch hsb accVF vk (hdrOf x).cL
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
