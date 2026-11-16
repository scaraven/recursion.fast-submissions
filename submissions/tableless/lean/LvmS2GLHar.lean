-- New for lvm2 MB-LIN (MBL-C3, 2026-11-16): the S2GL circuit's helper lemmas for `harithL20` and `nodeL20`
-- (MBL-STMT 7e, 7f): the front's phases over the config and the wire's `cont` intervals (`front_phasesUG`, ported
-- from ACW-C's RF-2 onto GOLF3's `front_phasesU`; V's `tapeUDGc`), the typed phases without the table phase
-- (`typed_phaseTL`), the opening with the three linear claims, and V_S's S2GL decision from its phases.
import LvmE2QFrontU
import LvmE2LDec
import LvmS2GLPlan
import LvmE2QInstL
import LvmE2QTypedLSem
import LvmE2QNodeU

/-!
# The S2GL circuit's phases (`harithL20`'s helpers)

* **`front_phasesUG`**: `front_phasesU` at any config `C` with `C.p = p`, `P20U`'s front facts (`FrontPF p`) and the
  wire's `cont` intervals `ivs` (V's `tapeUDGc ivs`).
-/

set_option autoImplicit false

namespace Lvm.E2Q

open Lvm Lvm.Loop Lvm.Loop.Build Lvm.Har Lvm.QSig Lvm.QAsm Lvm.Typed Lvm.QTyped


/-! ## Positions at `P20L` -/

set_option maxRecDepth 100000 in
/-- The first items of `P20L`'s phases (proof help: one walk of the literal `phasesL20`). -/
private theorem phaseItem0_P20L : phaseItem0 P20L .commit = 0 ∧ phaseItem0 P20L .bus = 25 ∧
    phaseItem0 P20L .tape = 357 ∧ phaseItem0 P20L .wire = 2595 ∧ phaseItem0 P20L .openMain = 2716 := by
  simp only [phaseItem0, phases_P20L_lit]; decide +kernel

/-- The phases' suffixes at `P20L` from one another (proof help: `.wire` and `.openMain` from `.tape`'s suffix). -/
private theorem drop_chainL (l : List Nat) :
    l.drop 2716 = ((l.drop 357).drop 2238).drop 121 ∧ l.drop 2595 = (l.drop 357).drop 2238 := by
  constructor <;> simp only [List.drop_drop]

set_option maxRecDepth 200000 in
/-- **`P20L`'s positions** (`posU20`'s twin; one kernel evaluation of the schedule's lanes). -/
theorem posL20 : startByte P20L + nodeBytes * 2 ^ (P20L.level ⟨.main, 0⟩).cap = posOf P20L 1 ∧
    posOf P20L 1 + 40 = 8 * phaseLane P20L .commit 1 ∧
    phaseLane P20L .commit (P20L.nuMain + 1) = phaseLane P20L .commit 1 + 9 * P20L.nuMain ∧
    posOf P20L 1 + 72 * P20L.nuMain + 24 = typedPosF P20L ∧ busLanesB P20L = true ∧
    ((∀ i < 20, 8 * phaseLane P20L .tape (2 + 2 * i) = posOf P20L (phaseItem0 P20L .tape) + 120 + 80 * i) ∧
      8 * phaseLane P20L .tape 41 = posOf P20L (phaseItem0 P20L .tape) + 1712 ∧
      8 * phaseLane P20L .tape 43 = posOf P20L (phaseItem0 P20L .tape) + 2520 ∧
      8 * phaseLane P20L .tape 45 = posOf P20L (phaseItem0 P20L .tape) + 2600 ∧
      posOf P20L (phaseItem0 P20L .wire) = 8 * Lvm.Q1.tapeEnd2 16 (phaseLane P20L .tape 45) - 40 ∧
      8 * phaseLane P20L .wire 0 = posOf P20L (phaseItem0 P20L .wire) + 40 ∧
      posOf P20L (phaseItem0 P20L .openMain) = posOf P20L (phaseItem0 P20L .wire) + 8216 ∧
      posOf P20L (phaseItem0 P20L .tape) % 8 = 0) := by
  simp only [posOf_drop, phaseLane_drop, typedPosF, busLanesB, busL_drop, phaseItem0_P20L.1, phaseItem0_P20L.2.1,
    phaseItem0_P20L.2.2.1, phaseItem0_P20L.2.2.2.1, phaseItem0_P20L.2.2.2.2]
  rw [itemLanes, schedule_P20L_lit, P20L_eqL, (drop_chainL _).1, (drop_chainL _).2, itemLanesAux_eq_R]
  simp only [← dropLN_eq, ← getDLN_eq, iZR, iWR, iRR, getDLN_add]
  decide +kernel

theorem hbL : Lvm.Har.pos (RS.startH (headerBytesP P20L)) + nodeBytes * 2 ^ (P20L.level ⟨.main, 0⟩).cap =
    posOf P20L 1 := by
  rw [pos_startH]; exact posL20.1

theorem pinHPL : posOf P20L 1 + 40 = 8 * phaseLane P20L .commit 1 := posL20.2.1

theorem pinQaL : phaseLane P20L .commit (P20L.nuMain + 1) = phaseLane P20L .commit 1 + 9 * P20L.nuMain :=
  posL20.2.2.1

theorem pinEndL : posOf P20L 1 + 72 * P20L.nuMain + 24 = typedPosF P20L := posL20.2.2.2.1

theorem busLanesB_P20L : busLanesB P20L = true := posL20.2.2.2.2.1


/-! ## The typed phases at S2GL (no table phase) -/

section TypedL

open Lvm.Q1 Lvm.Q2 DM Lvm.E2V

theorem mbPT_leL (Td : TData) (p : Params) : mbPT p ≤ typedEndL Td p := by
  unfold typedEndL busEndD
  have := le_layersEnd (gkrSteps Td.mbD) 0 (busP1 (mbPT p) + 48)
  simp only [busP1] at this ⊢
  omega

/-- **`dMiniL` as roll 7's phase 2** (`busPh`), then the bus check. -/
theorem dMiniL_eq (p : Params) (m : M3) (pub : Pub) :
    Lvm.E2L.dMiniL p m pub = (do
      let (alphas, beta, countRoot, point, values, leafdec) ← busPh p
      let bus := m.busFinal ⟨alphas, beta, countRoot, point, values, leafdec, pub⟩
      require bus.ok
      pure (point, bus)) := by
  funext sig s
  simp only [Lvm.E2L.dMiniL, busPh, bind_assoc, pure_bind]

variable {c : Ctx} {M : Mem} {sig : ByteArray} {T : Nat}

set_option maxHeartbeats 1000000 in
/-- **The typed phases in `PhaseAt` form at the circuit parameters `pc`** (S2GT-STMT 10c at `pc = P20T`;
`core_of_phasesG`'s `htyped`): where `typedGT`'s rows hold and assert (gate on) on the lanes of `pc`'s phase `bus`
(from `P`), V_S's `dTypedT`
runs from `P` to `typedEndT`, folds to the current proof's `PUB` accumulator, and its claims and evaluations are the
gadget's cells'. -/
theorem typed_phaseTL (pc : Params) (hacc : pc.accV = P20T.accV) (vk cL : Vector UInt8 32) (hS : Streamed M sig T) {pb : Nat} (hg : M.k pb = 1)
    (hvk : ∀ i < 4, M.k (pb + 1 + i) = (digestLanes vk).getD i 0) {z o zk ok : Cell} (hzE : z.ty = .E)
    (hoE : o.ty = .E) (hz : z.val M = 0) (ho : o.val M = 1) (hzK : zk.ty = .K) (hoK : ok.ty = .K)
    (hzk : zk.val M = 0) (hok1 : ok.val M = 1) {Td : TData} {N : Lvm.E2T.TNatT} (htd : TdOk Td N.toN)
    (p : Params) (hl : p.leafdecReads = 1) (hD : Td.mbD = p.busDepth) (m : M3) {P : Nat} (hL : BusLanesT (busL pc) P)
    (hpow : PowOkV (feAt sig) (typedChalsT pc)) (hT : typedEndL Td pc + 40 ≤ 8 * T)
    (hH : 11 + pubLanesTC pc ≤ T) (q : Ptr) (hq : 1 ≤ q.e)
    (hok : Lvm.QSig.Ok c M (typedGL Td pc pb (pubLanesTC pc) z o zk ok) q)
    (hm : ∀ i : BusIn, (m.busFinal i).ok = (i.values.length == 3 && i.leafdec == [0])) {α : Type}
    (mk : List FE2 → List FE2 → List FE2 → FE2 → α) :
    PhaseAt (Lvm.E2L.dTypedLG p N m (Lvm.E2T.pubG vk cL sig) mk) sig P (typedEndL Td pc)
      (accCT M pb, mk ((typedGL Td pc pb (pubLanesTC pc) z o zk ok q).1.1.ry.map (C2.val M)) ((typedGL Td pc pb (pubLanesTC pc) z o zk ok q).1.1.rv.map (C2.val M)) ((typedGL Td pc pb (pubLanesTC pc) z o zk ok q).1.1.rr.map (C2.val M)) ((typedGL Td pc pb (pubLanesTC pc) z o zk ok q).1.1.vR.val M),
        vs M (typedGL Td pc pb (pubLanesTC pc) z o zk ok q).1.1.bus.pt,
        m.busFinal ⟨vs M (typedGL Td pc pb (pubLanesTC pc) z o zk ok q).1.1.bus.al, (typedGL Td pc pb (pubLanesTC pc) z o zk ok q).1.1.bus.be.val M, (typedGL Td pc pb (pubLanesTC pc) z o zk ok q).1.1.bus.cnt.val M, vs M (typedGL Td pc pb (pubLanesTC pc) z o zk ok q).1.1.bus.pt, vs M (typedGL Td pc pb (pubLanesTC pc) z o zk ok q).1.1.bus.vals, [0],
          Lvm.E2T.pubG vk cL sig⟩) := by
  have hpl : pubLanesTC pc = pubLanesTC P20T := by unfold pubLanesTC; rw [hacc]
  rw [hpl] at hok hH ⊢
  intro s hs hsok
  have hgv : (kc pb).val M = 1 := Lvm.QAcc.kc_val_one hg
  have kz : ∀ x : Cell, x.ty = .K → x.val M = 0 → (x.val M).c₀ = 0 := fun x _ h => by rw [h]; rfl
  have hz2 : (⟨zk, zk⟩ : C2).val M = 0 := by
    show (⟨(zk.val M).c₀, (zk.val M).c₀⟩ : FE2) = 0; rw [hzk]; rfl
  have ho2 : (⟨ok, zk⟩ : C2).val M = 1 := by
    show (⟨(ok.val M).c₀, (zk.val M).c₀⟩ : FE2) = 1; rw [hok1, hzk]; rfl
  have hz2K : KC2 ⟨zk, zk⟩ := ⟨hzK, hzK⟩
  have ho2K : KC2 ⟨ok, zk⟩ := ⟨hoK, hzK⟩
  obtain ⟨pτ, pω, pZ, pγ, pW, pR, pκ, pt⟩ := powT_facts hL hpow
  have hP8 := hL.al
  -- through `mbPT`'s equation (GOLF2-K1: the kernel's defeq `mbPT P20T =?= 8 * busL P20T iMB - 40` evaluated
  -- `busL P20T`, 5.4 M heartbeats; the omegas below clear the facts they do not use)
  have hmb : mbPT pc = P + 10120 := (mbPT.eq_1 pc).trans hL.mb
  have hE := mbPT_leL Td pc
  -- the circuit's parts, at their pointers
  unfold typedGL at hok ⊢
  dsimp only at hok ⊢
  simp only [bind_apply, pure_apply] at ⊢
  obtain ⟨hZ, hok⟩ := okb hok
  obtain ⟨zr, hzr⟩ : ∃ x, (zeroGT ⟨zk, zk⟩ (kc pb) (busL pc) q).1 = x := ⟨_, rfl⟩
  obtain ⟨q1, hq1⟩ : ∃ x, q.adv (zeroGT ⟨zk, zk⟩ (kc pb) (busL pc) q).2 = x := ⟨_, rfl⟩
  have RZ := zeroGT_run (c := c) hS hz2 hgv (P := P) (qz := (P + 1792) / 8) hL.tau hL.om
    (by clear * - hP8; omega) (fun k hk => by have := hL.zr k hk; clear * - this hP8; omega) hL.zv
    (by clear * - hT hE hmb; omega) pτ pω pZ q hZ.1 hZ.2
  rw [hzr] at RZ hok
  rw [hq1] at hok
  simp only [hzr, hq1]
  obtain ⟨hW, hok⟩ := okb hok
  obtain ⟨w, hw⟩ : ∃ x, (wireGT ⟨zk, zk⟩ ⟨ok, zk⟩ (kc pb) Td pb (pubLanesTC P20T) (busL pc) zr.2 q1).1 = x :=
    ⟨_, rfl⟩
  obtain ⟨q2, hq2⟩ : ∃ x, q1.adv (wireGT ⟨zk, zk⟩ ⟨ok, zk⟩ (kc pb) Td pb (pubLanesTC P20T) (busL pc) zr.2 q1).2 = x :=
    ⟨_, rfl⟩
  have hs1 : rpos s = P := hs
  obtain ⟨z1, z2', z3, z4, z5⟩ := RZ s hs1 hsok
  have RW := wireGT_run (c := c) vk cL hS hz2 ho2 hz2K ho2K hgv htd hvk (P := P + 4136) (qw := (P + 4256) / 8)
    (by rw [hL.gam]) (by clear * - hP8; omega) (fun k hk => by have := hL.wr k hk; clear * - this hP8; omega)
    (by rw [hL.wv]) (by rw [hL.wv4])
    (by clear * - hT hE hmb; omega) hH (by rw [show P + 4136 + 48 = P + 4184 from rfl]; exact pγ)
    (by rw [show P + 4136 + 80 = P + 4216 from rfl]; exact pW) zr.2 (by rw [z5]; simp [ld2s]) q1 hW.1 hW.2
  rw [hw] at RW hok
  rw [hq2] at hok
  simp only [hw, hq2]
  obtain ⟨hRl, hok⟩ := okb hok
  obtain ⟨r, hr⟩ : ∃ x, (relayGT ⟨zk, zk⟩ ⟨ok, zk⟩ (kc pb) Td (busL pc) w.1 (w.2.2.getD 1 ⟨zk, zk⟩) q2).1 = x :=
    ⟨_, rfl⟩
  obtain ⟨q3, hq3⟩ : ∃ x, q2.adv (relayGT ⟨zk, zk⟩ ⟨ok, zk⟩ (kc pb) Td (busL pc) w.1
      (w.2.2.getD 1 ⟨zk, zk⟩) q2).2 = x := ⟨_, rfl⟩
  -- V's run
  unfold Lvm.E2L.dTypedLG
  rw [dbind_run]
  obtain ⟨Z, hZr⟩ : ∃ x, Lvm.E2T.dZeroT sig s = x := ⟨_, rfl⟩
  rw [hZr] at z1 z2' z3
  rw [hZr, dbind_run, Prod.fst, z1]
  obtain ⟨W1, W2, W3, W4, W5, W6, W7⟩ := RW Z.2 z3 z2'
  have RR := relayGT_run (c := c) hS hz2 ho2 hz2K ho2K hgv htd (N := N) (P := P + 6824) (qr := (P + 6864) / 8)
    (by clear * - hP8; omega) (fun k hk => by have := hL.rr k hk; clear * - this hP8; omega) (by rw [hL.rv])
    (by clear * - hT hE hmb; omega)
    (by rw [show P + 6824 = P + 6824 by rfl]; exact pR) w.1 W4 W5 (w.2.2.getD 1 ⟨zk, zk⟩) q2 hRl.1 hRl.2
  rw [hr] at RR hok
  rw [hq3] at hok
  simp only [hr, hq3]
  obtain ⟨hA, hok⟩ := okb hok
  obtain ⟨q4, hq4⟩ : ∃ x, q3.adv (qaccGT ⟨zk, zk⟩ ⟨ok, zk⟩ pb (busL pc) zr.1 w.1 w.2.1 q3).2 = x := ⟨_, rfl⟩
  have RA := qaccGT_run (c := c) vk cL hS hz2 ho2 hz2K ho2K hg (P := P + 8968)
    (fun j hj => by rw [hL.kap j hj]) (by rw [hL.h]) (by rw [hL.t]) (by rw [hL.z])
    (by clear * - hT hE hmb; omega) hH pκ
    (by rw [show P + 8968 + 1104 = P + 10072 from rfl]; exact pt) zr.1 w.1 w.2.1 z4 W4
    (by rw [W6]; simp [ld2s]) q3 hA.1 hA.2
  rw [hq4] at hok
  simp only [hq4]
  have e1 : q.e ≤ q1.e := hq1 ▸ Lvm.Har.adv_e_le _ _
  have e2 : q1.e ≤ q2.e := hq2 ▸ Lvm.Har.adv_e_le _ _
  have e3 : q2.e ≤ q3.e := hq3 ▸ Lvm.Har.adv_e_le _ _
  have e4 : q3.e ≤ q4.e := hq4 ▸ Lvm.Har.adv_e_le _ _
  -- the wiring's run
  obtain ⟨Wr, hWr⟩ : ∃ x, Lvm.E2T.dWiringT N (Lvm.E2T.pubG vk cL sig) (zr.2.map (C2.val M)) sig Z.2 = x := ⟨_, rfl⟩
  rw [hWr] at W1 W2 W3
  rw [hWr, W1]
  dsimp only
  have egd : (w.2.2.map (C2.val M)).getD 1 0 = (w.2.2.getD 1 ⟨zk, zk⟩).val M := by rw [← hz2, List.getD_map]
  rw [egd, dbind_run]
  -- the relayout's run
  obtain ⟨Rr, hRr⟩ : ∃ x, Lvm.E2T.dRelayT2 N (w.1.map (C2.val M)) ((w.2.2.getD 1 ⟨zk, zk⟩).val M) sig Wr.2 = x :=
    ⟨_, rfl⟩
  obtain ⟨R1, R2, R3, R4, R5, R6⟩ := RR Wr.2 (by clear * - W3; omega) W2
  rw [hRr] at R1 R2 R3
  rw [hRr, dbind_run, R1]
  dsimp only
  rw [← List.map_append]
  -- A23's run
  obtain ⟨Ar, hAr⟩ : ∃ x, Lvm.E2T.dAccT (Lvm.E2T.pubG vk cL sig) ((zr.1 ++ w.1).map (C2.val M))
      (w.2.1.map (C2.val M)) sig Rr.2 = x := ⟨_, rfl⟩
  obtain ⟨A1, A2, A3⟩ := RA Rr.2 (by clear * - R3; omega) R2
  rw [hAr] at A1 A2 A3
  rw [hAr, dbind_run, A1]
  -- the mini-bus's GKR (no table phase)
  obtain ⟨hB, -⟩ := okb hok
  have e1 : busGD Td.mbD z o (kc pb) (mbPT pc) = busG p z o (kc pb) (mbPT pc) := by rw [hD]; rfl
  have eE : typedEndL Td pc = busEnd p (mbPT pc) := by unfold typedEndL; rw [hD]; rfl
  rw [e1] at hB ⊢
  rw [eE] at hT ⊢
  obtain ⟨b1, b2, b3⟩ := busG_replays (c := c) hS hz ho hgv p hl (P := mbPT pc) (by clear * - hmb hP8; omega)
    (by clear * - hT; omega) q4 hB Ar.2
    (by show Ar.2.ent + Ar.2.msg = _; simp only [rpos] at A3; clear * - A3 hmb; omega) A2
  obtain ⟨hbv, h3⟩ := busR_eq b3
  rw [dMiniL_eq, dbind_run]
  generalize busPh p sig Ar.2 = BB at b1 b2 hbv ⊢
  obtain ⟨bv, s1⟩ := BB
  simp only at b1 b2 hbv
  subst hbv
  have hok2 : (m.busFinal ⟨vs M (busG p z o (kc pb) (mbPT pc) q4).1.al, (busG p z o (kc pb) (mbPT pc) q4).1.be.val M,
      (busG p z o (kc pb) (mbPT pc) q4).1.cnt.val M, vs M (busG p z o (kc pb) (mbPT pc) q4).1.pt,
      vs M (busG p z o (kc pb) (mbPT pc) q4).1.vals, [0], Lvm.E2T.pubG vk cL sig⟩).ok = true := by
    rw [hm]; show ((vs M (busG p z o (kc pb) (mbPT pc) q4).1.vals).length == 3 && [(0 : FE)] == [0]) = true
    rw [h3]; decide
  simp only [busV, bind_run', require_run', pure_run', hok2, b1]
  exact ⟨trivial, rfl, b2⟩

end TypedL


/-! ## The three linear claims: shape, relation, the opening -/

section ClaimsL

open Lvm.Q2 Lvm.QShape

theorem stepG_len (z o g : Cell) (st Q : Nat) (vals : List Cell) (d : PD) (ptr : Ptr) :
    ((stepG z o g st Q vals d) ptr).1.2.len = st + d.len := by
  simp only [stepG, bind_apply, pure_apply, PD.len]

theorem layersG_len (z o g : Cell) : ∀ (sts : List Nat) (Q : Nat) (vals : List Cell) (d : PD) (ptr : Ptr),
    ((layersG z o g sts Q vals d) ptr).1.2.len = sts.sum + d.len
  | [], _, _, _, _ => by simp only [layersG, pure_apply, List.sum_nil, Nat.zero_add]
  | st :: sts, Q, vals, d, ptr => by
    simp only [layersG, bind_apply, layersG_len z o g sts, stepG_len, List.sum_cons]
    omega

theorem gkrSteps_sum : ∀ n : Nat, (gkrSteps n).sum = n
  | 0 => rfl
  | 1 => rfl
  | n + 2 => by
    unfold gkrSteps
    split
    · rw [List.sum_cons, gkrSteps_sum (n + 1)]; omega
    · rw [List.sum_cons, gkrSteps_sum n]; omega

/-- **The bus phase's point has `busDepth` cells.** -/
theorem busG_pt_len (p : Params) (z o g : Cell) (P : Nat) (ptr : Ptr) :
    ((busG p z o g P) ptr).1.pt.length = p.busDepth := by
  simp only [busG, bind_apply, pure_apply, PD.cells, List.length_map, List.length_range]
  rw [layersG_len, gkrSteps_sum]
  rfl

theorem comOff_mem {t : TShape} {c off : Nat} (h : comOff t c = some off) : some (false, off) ∈ t.cols := by
  unfold comOff at h
  split at h
  · rename_i off' heq
    obtain rfl := Option.some.inj h
    rw [List.getD_eq_getElem?_getD] at heq
    rcases hcc : t.cols[c]? with _ | y
    · rw [hcc] at heq; simp at heq
    · rw [hcc, Option.getD_some] at heq; subst heq; exact List.mem_of_getElem? hcc
  · simp at h

/-- The parts of `mbLinG`'s claim of side `s` (for the shape lemma). -/
theorem mem_partsPlanL {S : List TShape} {s : Nat} {x : Nat × Nat × CKey} (h : x ∈ partsPlan S s) :
    ∃ off, S.getD x.1 shape0 ∈ S ∧ some (false, off) ∈ (S.getD x.1 shape0).cols ∧
      comOff (S.getD x.1 shape0) x.2.1 = some off := by
  unfold partsPlan at h
  obtain ⟨⟨t, j⟩, htj, h⟩ := List.mem_flatMap.mp h
  obtain ⟨c, -, h⟩ := List.mem_filterMap.mp h
  have hj : S[j]? = some t := (List.mem_zipIdx_iff_getElem?.mp htj)
  have hS : S.getD j shape0 = t := by rw [List.getD_eq_getElem?_getD, hj]; rfl
  rcases hc : comOff t c with _ | off
  · simp only [hc] at h; exact absurd h (by simp)
  · simp only [hc] at h
    split at h
    · exact absurd h (by simp)
    · simp only [Option.some.injEq] at h
      subst h
      exact ⟨off, by rw [hS]; exact List.mem_of_getElem? hj, by rw [hS]; exact comOff_mem hc, by rw [hS]; exact hc⟩

variable {c : Ctx} {M : Mem}

/-- **`mbLinG`'s claims are taken as they are** (`cOkB`, on `C_main`): the parts' blocks are regular committed columns
of the mini-bus's shapes (`typedRegB`), the points `ζ.take τ`. -/
theorem mbLinG_ok {zc z o : Cell} {T : TData} {bc : BusC} {sOff : Nat} (hreg : typedRegB T sOff = true)
    (hpt : T.mbR ≤ bc.pt.length) :
    Hs c M (mbLinG z o T bc) (fun cs => ∀ cc ∈ cs, cOkB zc cc = true ∧ cc.com = .main) := by
  obtain ⟨-, -, hS⟩ := typedRegB_sound hreg
  have key : ∀ (cs : List Cell) (s : Nat), ∀ e ∈ (partsPlan T.mbS s).map (fun x =>
      (atC z cs ((keysPlan T.mbS).idxOf x.2.2),
        (⟨(T.mbS.getD x.1 shape0).τ, (comOff (T.mbS.getD x.1 shape0) x.2.1).getD 0⟩ : Placement),
        bc.pt.take (T.mbS.getD x.1 shape0).τ)),
      e.2.1.variableCount ≤ CMain.nu20 ∧ e.2.2.length = e.2.1.variableCount ∧ RegP e.2.1 := by
    intro cs s e he
    obtain ⟨x, hx, rfl⟩ := List.mem_map.mp he
    obtain ⟨off, hmem, hcol, hco⟩ := mem_partsPlanL hx
    obtain ⟨h1, h2, h3⟩ := hS _ hmem
    obtain ⟨-, hR⟩ := h3 _ hcol false off rfl
    simp only [hco, Option.getD_some, List.length_take]
    exact ⟨h2, Nat.min_eq_left (le_trans h1 hpt), hR⟩
  have hc : ∀ (cs : List Cell) (s : Nat) (v : Cell), cOkB zc ⟨.main, .sum CMain.nu20 ((partsPlan T.mbS s).map
      fun x => (atC z cs ((keysPlan T.mbS).idxOf x.2.2),
        (⟨(T.mbS.getD x.1 shape0).τ, (comOff (T.mbS.getD x.1 shape0) x.2.1).getD 0⟩ : Placement),
        bc.pt.take (T.mbS.getD x.1 shape0).τ)), v⟩ = true := by
    intro cs s v
    have k := key cs s
    simp only [cOkB, tailFreeB, Lvm.Har.WF1, Lvm.QShape.ZWF, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true,
      le_refl, true_and, and_true]
    exact ⟨fun e he => ⟨(k e he).1, (k e he).2.1⟩, fun e he => (k e he).2.2⟩
  unfold mbLinG
  dsimp only
  repeat (first | refine hs_bind_true fun _ => ?_)
  refine hs_pure ?_
  intro cc hcc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hcc
  rcases hcc with rfl | rfl | rfl <;> exact ⟨hc _ _ _, rfl⟩

/-- **V_S's three claims at the bus's outputs are `mbClaimsN`'s** (tails `0`). -/
theorem linClaims_eq (nu : Nat) (tabs : List Lvm.M3.Tab) (i : BusIn) :
    Lvm.E2L.linClaims nu i.point ((List.range 3).map (Lvm.M3.mbColsN tabs (Lvm.M3.busFinalR tabs i)))
      ((List.range 3).map (Lvm.M3.mbValueN tabs (Lvm.M3.busFinalR tabs i) i.point)) =
    (Lvm.M3.mbClaimsN nu tabs i).map fun b => (Com.main, b, (0 : FE)) := by
  simp only [Lvm.E2L.linClaims, Lvm.M3.mbClaimsN, Lvm.M3.mbPartsN_cols, Lvm.E2L.partsOf]
  rfl

/-- **The gadget's three claims stand for V_S's** (`FRelZ`, both shapes). -/
theorem lin_rel {zc : Cell} {b : Bool} {cs : List CClaim} {tabs : List Lvm.M3.Tab} {i : BusIn}
    (hcs : cs.map (CClaim.val M) = (Lvm.M3.mbClaimsN CMain.nu20 tabs i).map fun b => (Com.main, b))
    (hok : ∀ cc ∈ cs, cOkB zc cc = true) :
    List.Forall₂ (FRelZ M zc b) (cs.map FClaim.e3)
      (Lvm.E2L.linClaims CMain.nu20 i.point ((List.range 3).map (Lvm.M3.mbColsN tabs (Lvm.M3.busFinalR tabs i)))
        ((List.range 3).map (Lvm.M3.mbValueN tabs (Lvm.M3.busFinalR tabs i) i.point))) := by
  rw [linClaims_eq]
  refine e3s_rel ?_ ?_ hok
  · rw [hcs, List.map_map]; rfl
  · intro e he
    obtain ⟨b', -, rfl⟩ := List.mem_map.mp he
    exact ⟨rfl, rfl⟩

end ClaimsL

/-! ## V's merged tape by phases, any `cont` intervals -/

section WirePhL

open Lvm.Q2 DM

set_option maxHeartbeats 1000000 in
/-- **V's S2GU wire by phases** (`wireUDGc cv rowSwitchDR`, `cont`'s intervals `cv`, `w = 20`, from `P`, first
message lane `q`): the wire sumcheck, `g_D, g_Y, g_M`, the final check (`hfin`), the slot reductions of `D` (2 rounds,
from `P + 2288`), `Y` (5, from `+ 1752`) and `M` (5, from `+ 2088`) with their checks. -/
theorem wireUDGc_phase {sig : ByteArray} {q P : ℕ} (cv : List (ℕ × ℕ)) (p : Params) (hw : p.logN = 20)
    (hk : p.ksLog = 13) (s : List FK)
    (n : ℕ) (claim : E2V.KClaim FE2) (hq : 8 * q = P + 40)
    (hpw : ∀ k < 20, powOKR E2V.gC2 (feAt sig (P + 80 + 112 * k)) = true)
    (hpD : ∀ k < 2, powOKR E2V.gC2 (feAt sig (P + 2288 + 80 + 112 * k)) = true)
    (hpY : ∀ k < 5, powOKR E2V.gC2 (feAt sig (P + 4040 + 80 + 112 * k)) = true)
    (hpM : ∀ k < 5, powOKR E2V.gC2 (feAt sig (P + 6128 + 80 + 112 * k)) = true)
    (hfin : scFold2 (fun k => fe2At sig (8 * k)) 20 q (wireTargetDF (sBitsD s) n claim) =
      E2V.msEvalF claim.point claim.mu (scPts sig P 20) 0 (n - 1) * fe2At sig (P + 2280) +
        Lvm.E2U.eTailF 13 20 (scPts sig P 20) *
          (Lvm.E2U.kksF cv claim.point claim.mu ((scPts sig P 20).take 13) (2 ^ 20) *
              fe2At sig (P + 2296) +
            E2V.ikEvalP claim.point claim.mu ((scPts sig P 20).take 13) (2 ^ 20) * fe2At sig (P + 2312)))
    (hD : scFold2 (fun k => fe2At sig (8 * k)) 2 ((P + 2288 + 40) / 8) (fe2At sig (P + 2280)) =
      E2V.sumF ((List.range 64).map fun z => E2V.slotWF 2 (dWA claim.weights.toArray) (scPts sig (P + 2288) 2) z *
        (readsE2 sig (P + 2288 + 112 * 2) 64).getD z 0))
    (hY : scFold2 (fun k => fe2At sig (8 * k)) 5 ((P + 4040 + 40) / 8) (fe2At sig (P + 2296)) =
      E2V.sumF ((List.range 64).map fun z => E2V.slotWF 5 (Lvm.E2V.yWG claim.weights) (scPts sig (P + 4040) 5) z *
        (readsE2 sig (P + 4040 + 112 * 5) 64).getD z 0))
    (hM : scFold2 (fun k => fe2At sig (8 * k)) 5 ((P + 6128 + 40) / 8) (fe2At sig (P + 2312)) =
      E2V.sumF ((List.range 64).map fun z => E2V.slotWF 5 (Lvm.E2V.mWG claim.weights) (scPts sig (P + 6128) 5) z *
        (readsE2 sig (P + 6128 + 112 * 5) 64).getD z 0)) :
    PhaseAt (Lvm.E2L.wireUDGc cv rowSwitchDR p s n claim) sig P (P + 8216)
      ⟨(scPts sig P 20, scFold2 (fun k => fe2At sig (8 * k)) 20 q (wireTargetDF (sBitsD s) n claim)),
        readsE2 sig (P + 2240) 3,
        ((scPts sig (P + 2288) 2, scFold2 (fun k => fe2At sig (8 * k)) 2 ((P + 2288 + 40) / 8) (fe2At sig (P + 2280))),
          readsE2 sig (P + 2288 + 112 * 2) 64,
          (rowSwitchDR (scPts sig P 20 ++ scPts sig (P + 2288) 2 ++ Lvm.E2V.selPtF (dSel p) (dSelBits p))
            (readsE2 sig (P + 2288 + 112 * 2) 64) sig ⟨P + 2288 + 112 * 2 + 1024, 0, true⟩).1),
        ((scPts sig (P + 4040) 5, scFold2 (fun k => fe2At sig (8 * k)) 5 ((P + 4040 + 40) / 8) (fe2At sig (P + 2296))),
          readsE2 sig (P + 4040 + 112 * 5) 64,
          (rowSwitchDR ((scPts sig P 20).take 13 ++ scPts sig (P + 4040) 5 ++
              Lvm.E2V.selPtF ((layout0 p).ks / 2 ^ (p.ksLog + 5)) (p.nuMain - (p.ksLog + 5)))
            (readsE2 sig (P + 4040 + 112 * 5) 64) sig ⟨P + 4040 + 112 * 5 + 1024, 0, true⟩).1),
        ((scPts sig (P + 6128) 5, scFold2 (fun k => fe2At sig (8 * k)) 5 ((P + 6128 + 40) / 8) (fe2At sig (P + 2312))),
          readsE2 sig (P + 6128 + 112 * 5) 64,
          (rowSwitchDR ((scPts sig P 20).take 13 ++ [0] ++ scPts sig (P + 6128) 5 ++
              Lvm.E2V.selPtF ((layout0 p).s / 2 ^ p.nuRec) (p.nuMain - p.nuRec))
            (readsE2 sig (P + 6128 + 112 * 5) 64) sig ⟨P + 6128 + 112 * 5 + 1024, 0, true⟩).1)⟩ := by
  unfold Lvm.E2L.wireUDGc
  rw [hw, hk]
  simp only [Lvm.E2U.slotBitsU]
  refine phaseAt_bind (sumcheckD_phase hq hpw) (phaseAt_bind readE2s_phase (phaseAt_bind
    (phaseAt_require ?_) ?_))
  · have g0 : (readsE2 sig (P + 112 * 20) 3).getD 0 0 = fe2At sig (P + 2280) := by
      simp [readsE2, List.getD_eq_getElem?_getD]
    have g1 : (readsE2 sig (P + 112 * 20) 3).getD 1 0 = fe2At sig (P + 2296) := by
      simp [readsE2, List.getD_eq_getElem?_getD]
    have g2 : (readsE2 sig (P + 112 * 20) 3).getD 2 0 = fe2At sig (P + 2312) := by
      simp [readsE2, List.getD_eq_getElem?_getD]
    dsimp only
    rw [beq_iff_eq, g0, g1, g2]
    exact hfin
  · have hP8 : P % 8 = 0 := by omega
    have e1 : P + 112 * 20 + 16 * 3 = P + 2288 := by ring
    have hr : readsE2 sig (P + 112 * 20) 3 = readsE2 sig (P + 2240) 3 := by rw [show 112 * 20 = 2240 by rfl]
    dsimp only
    rw [e1, hr]
    have g0 : (readsE2 sig (P + 2240) 3).getD 0 0 = fe2At sig (P + 2280) := by
      simp [readsE2, List.getD_eq_getElem?_getD]
    have g1 : (readsE2 sig (P + 2240) 3).getD 1 0 = fe2At sig (P + 2296) := by
      simp [readsE2, List.getD_eq_getElem?_getD]
    have g2 : (readsE2 sig (P + 2240) 3).getD 2 0 = fe2At sig (P + 2312) := by
      simp [readsE2, List.getD_eq_getElem?_getD]
    rw [g0, g1, g2]
    refine phaseAt_bind (slotDFG_phase (q := (P + 2288 + 40) / 8) (by omega) hpD hD) ?_
    rw [show P + 2288 + 112 * 2 + 1024 + 504 = P + 4040 by ring, Lvm.E2U.slotDFW_yWG]
    refine phaseAt_bind (slotDFG_phase (q := (P + 4040 + 40) / 8) (by omega) hpY hY) ?_
    rw [show P + 4040 + 112 * 5 + 1024 + 504 = P + 6128 by ring, Lvm.E2U.slotDFW_mWG,
      show Lvm.E2U.slotBitsU = 5 from rfl]
    refine phaseAt_bind (slotDFG_phase (q := (P + 6128 + 40) / 8) (by omega) hpM hM) ?_
    rw [show P + 6128 + 112 * 5 + 1024 + 504 = P + 8216 by ring]
    exact phaseAt_pure

set_option maxHeartbeats 1000000 in
/-- **V's merged tape by phases** (`tapeUDGc cv rowSwitchDR`, `w = 20`, from `P`): the separator, `r_{<20}` (answers
`8 q₀ = P + 120`), the 50 scalars, `r₂₀` (answer at `P + 2520`), the GKR on T1's values (`htg`, from `P + 2552`),
`n`'s range, the wire (`hwire`). -/
theorem tapeUDGc_phase {sig : ByteArray} {q0 P P5 P6 : ℕ} (cv : List (ℕ × ℕ)) (p : Params) (hw : p.logN = 20)
    (hk : p.ksLog = 13)
    (s : List FK) (n : ℕ) {claim : E2V.KClaim FE2} {wo : Lvm.E2U.WireU RowZ} (hq0 : 8 * q0 = P + 120)
    (hpowR : Lvm.Q1.PowOkV (feAt sig) (chalsG q0 E2V.gC1 20))
    (hpow20 : powOKR E2V.gC1 (feAt sig (P + 2520)) = true)
    (htg : PhaseAt (tapeGkrDF 21 (sampsG sig (P + 72) 20 ++ [fe2At sig (P + 2520)])
      (Lvm.E2U.t1ValsF 20 13 (sampsG sig (P + 72) 20 ++ [fe2At sig (P + 2520)]) (readsE2 sig (P + 1672) 50)))
      sig (P + 2552) P5 claim)
    (hn : 1 ≤ n ∧ n ≤ 2 ^ 20) (hwire : PhaseAt (Lvm.E2L.wireUDGc cv rowSwitchDR p s n claim) sig P5 P6 wo) :
    PhaseAt (Lvm.E2L.tapeUDGc cv rowSwitchDR p s n) sig P P6
      ⟨sampsG sig (P + 72) 20, fe2At sig (P + 2520), readsE2 sig (P + 1672) 50, claim, wo⟩ := by
  unfold Lvm.E2L.tapeUDGc
  rw [hw, hk]
  refine phaseAt_bind sepE2_phase (phaseAt_bind (samplesG_phase (by omega) hpowR) (phaseAt_bind readE2s_phase ?_))
  rw [show P + 72 + 80 * 20 + 16 * (2 * 25) = P + 2472 by ring,
    show P + 72 + 80 * 20 = P + 1672 by ring]
  refine phaseAt_bind (sampleG_phase (by rw [show P + 2472 + 48 = P + 2520 by ring]; exact hpow20)) ?_
  rw [show P + 2472 + 48 = P + 2520 by ring, show P + 2472 + 80 = P + 2552 by ring]
  exact phaseAt_bind htg (phaseAt_bind (phaseAt_require (decide_eq_true hn)) (phaseAt_bind hwire phaseAt_pure))


end WirePhL

/-- The lanes of `CHwire` at `p` (`wlU`'s at `P20U`). -/
abbrev wlUG (p : Params) : Lvm.Q2.WireLanesU := Lvm.Q2.wireLanesU p.logN (phaseLane p .wire 0)

section FrontUG

open Lvm.Q2 Lvm.QShape

variable {M : Mem}

/-- **The facts about `p` the front's phases use** (`P20U`'s and `P20A`'s): the table sizes, `C_main`'s words and
`layout0`, the sponge blocks below the key table, the tape's and the wire's positions (`posU20`'s last conjunct). -/
structure FrontPF (p : Params) : Prop where
  logN : p.logN = 20
  ksLog : p.ksLog = 13
  nuMain : p.nuMain = CMain.nu20
  recRowsLog : p.recRowsLog = 14
  lay : layout0 p = layout0 P20U
  sb : spongeBlocks p - 1 < 2 ^ 13
  pos : (∀ i < 20, 8 * phaseLane p .tape (2 + 2 * i) = posOf p (phaseItem0 p .tape) + 120 + 80 * i) ∧
    8 * phaseLane p .tape 41 = posOf p (phaseItem0 p .tape) + 1712 ∧
    8 * phaseLane p .tape 43 = posOf p (phaseItem0 p .tape) + 2520 ∧
    8 * phaseLane p .tape 45 = posOf p (phaseItem0 p .tape) + 2600 ∧
    posOf p (phaseItem0 p .wire) = 8 * Lvm.Q1.tapeEnd2 16 (phaseLane p .tape 45) - 40 ∧
    8 * phaseLane p .wire 0 = posOf p (phaseItem0 p .wire) + 40 ∧
    posOf p (phaseItem0 p .openMain) = posOf p (phaseItem0 p .wire) + 8216 ∧
    posOf p (phaseItem0 p .tape) % 8 = 0

theorem FrontPF.ksSplit_eq {p : Params} (hf : FrontPF p) : ksSplit p = 7680 := by
  unfold ksSplit ksXLog; rw [hf.ksLog, hf.recRowsLog]; rfl

theorem FrontPF.dSel_eq {p : Params} (hf : FrontPF p) : dSel p = dSel P20U := by
  unfold dSel; rw [hf.lay, hf.logN]; rfl

theorem FrontPF.dSelBits_eq {p : Params} (hf : FrontPF p) : dSelBits p = dSelBits P20U := by
  unfold dSelBits; rw [hf.nuMain, hf.logN]; rfl

theorem FrontPF.frontCsU_eq {p : Params} (hf : FrontPF p) : frontCsU p = frontCsU P20U := by
  have h1 : p.ksLog = P20U.ksLog := hf.ksLog
  have h2 : p.recRowsLog = P20U.recRowsLog := hf.recRowsLog
  have h3 : p.logN = P20U.logN := hf.logN
  funext F r a b wo rD nuD rY nuY rM nuM mbE
  simp only [frontCsU, dBlock, hf.dSel_eq, hf.dSelBits_eq, hf.lay, h1, h2, h3]

theorem FrontPF.frontItemsU_eq {p : Params} (hf : FrontPF p) (pub : Pub) (tp : Lvm.E2U.TapeU RowZ) :
    Lvm.E2U.frontItemsU rowAccR p pub tp = Lvm.E2U.frontItemsU rowAccR P20U pub tp := by
  have h1 : p.ksLog = P20U.ksLog := hf.ksLog
  have h2 : p.recRowsLog = P20U.recRowsLog := hf.recRowsLog
  have h3 : p.logN = P20U.logN := hf.logN
  have h4 : p.nuMain = P20U.nuMain := hf.nuMain
  simp only [Lvm.E2U.frontItemsU, dBlock, hf.dSel_eq, hf.dSelBits_eq, hf.lay, Params.nuRec, h1, h2, h3, h4]

/-- **`front_claimsU` at any `p` with `P20U`'s front facts** (`FrontPF`): the claims and V's items are `P20U`'s. -/
theorem front_claimsUG {p : Params} (hf : FrontPF p) {zc : Cell} {b : Bool} {pub : Pub} {F : FCtx} {r a bb : List C2}
    {wo : WireOutU} {rD rY rM : RowOut} {nuD nuY nuM : RowNu} {mbE : List Cell} {tp : Lvm.E2U.TapeU RowZ}
    {eqD eqY eqM : List FE}
    (hz2 : F.z2.val M = 0) (ho2 : F.o2.val M = 1) (hz2K : KC2 F.z2) (ho2K : KC2 F.o2) (hzE : M.e F.z.n = 0)
    (hoE : M.e F.o.n = 1)
    (hr : ∀ x ∈ r, KC2 x) (hrl : r.length = 20) (ha : ∀ l < 4, KC2 (a.getD l default))
    (hb : ∀ l < 25, KC2 (bb.getD l default))
    (htr : tp.r = r.map (C2.val M)) (hta : ∀ l < 4, tp.ab.getD l 0 = (a.getD l default).val M)
    (htb : ∀ l < 25, tp.ab.getD (25 + l) 0 = (bb.getD l default).val M)
    (hsgK : ∀ x ∈ wo.sigma, KC2 x) (hsgl : wo.sigma.length = 20) (hdK : ∀ x ∈ wo.tauD, KC2 x)
    (hdl : wo.tauD.length = 2) (hyK : ∀ x ∈ wo.tauY, KC2 x) (hyl : wo.tauY.length = 5)
    (hmK : ∀ x ∈ wo.tauM, KC2 x) (hml : wo.tauM.length = 5)
    (hsc : tp.wo.sc.1 = wo.sigma.map (C2.val M)) (htd : tp.wo.d.1.1 = wo.tauD.map (C2.val M))
    (hRD : tp.wo.d.2.2.1 = ⟨rD.target.val M, (wo.sigma.map (C2.val M) ++ wo.tauD.map (C2.val M) ++
      E2V.selPtF (dSel p) (dSelBits p)).map tColsW, eqD.toArray, eqD⟩) (hnuD : RowNuOk M nuD eqD)
    {sY sM : List FE2}
    (hRY : tp.wo.y.2.2.1 = ⟨rY.target.val M, ((wo.sigma.map (C2.val M)).take 13 ++ wo.tauY.map (C2.val M) ++ sY).map
      tColsW, eqY.toArray, eqY⟩) (hnuY : RowNuOk M nuY eqY)
    (hRM : tp.wo.m.2.2.1 = ⟨rM.target.val M, ((wo.sigma.map (C2.val M)).take 13 ++ [0] ++ wo.tauM.map (C2.val M) ++
      sM).map tColsW, eqM.toArray, eqM⟩) (hnuM : RowNuOk M nuM eqM)
    (hmbE : vs M mbE = selectorPoint (pub.n - 1) 20) (hh : pub.h = (List.range 4).map fun l => M.k (hLane l))
    (hsm : b = true → pub.n ≤ 2 ^ 18) (hn : 1 ≤ pub.n) :
    List.Forall₂ (FRelZ M zc b) (frontCsU p F r a bb wo rD nuD rY nuY rM nuM mbE)
      ((Lvm.E2U.frontItemsU rowAccR p pub tp).flatMap FItem.flat) := by
  rw [hf.frontCsU_eq, hf.frontItemsU_eq, hf.dSel_eq, hf.dSelBits_eq] at *
  exact front_claimsU hz2 ho2 hz2K ho2K hzE hoE hr hrl ha hb htr hta htb hsgK hsgl hdK hdl hyK hyl hmK hml hsc htd hRD
    hnuD hRY hnuY hRM hnuM hmbE hh hsm hn

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 100000 in
/-- **`front_phasesUG`** (25b over the config): the front's phases at `p = C.p` with `P20U`'s front facts (`FrontPF`)
and `cont`'s intervals `ivs` (`[(1, B − 1), (K + 400, K + 430)]`, `B` the sponge blocks, `K = ksSplit p`): from the
front's rows and assertions (gate on), the proof-of-work answers (`powFrontU`), the three row switches' words (the
`rowAux` blocks on `tBu`), `n'`'s bits and range and the bits of `s'`, V_S's merged tape with the wire runs from the
tape's first item to the opening's, the front's claims stand for `frontItemsU`'s, and `mb` is `n' − 1`'s selector. -/
theorem front_phasesUG (C : QCfg) {p : Params} (hp : C.p = p) (hf : FrontPF p) (ivs : List (ℕ × ℕ))
    (hivs : [(1, spongeBlocks p - 1), (ksSplit p + 399 + 1, ksSplit p + 399 + 31)] = ivs) {c : Ctx} {M : Mem}
    {sig : ByteArray} {q : Ptr}
    (hS : Lvm.Q1.Streamed M sig (streamLanes p))
    (hTo : posOf p (phaseItem0 p .openMain) + 48 ≤ 8 * streamLanes p)
    (hg : M.k (pbB C) = 1) (hpow : Lvm.Q1.PowOkV (feAt sig) (powFrontU p))
    (hrD : ∀ j < 128, M.k (tBu C 0 + j) = rowWordD (Lvm.Q2.slicesOf M (wlUG p).slicesD) j)
    (hrY : ∀ j < 128, M.k (tBu C 1 + j) = rowWordD (Lvm.Q2.slicesOf M (wlUG p).slicesY) j)
    (hrM : ∀ j < 128, M.k (tBu C 2 + j) = rowWordD (Lvm.Q2.slicesOf M (wlUG p).slicesM) j)
    (pub : Pub) (hnb : ∀ j < 20, (kc ((sigIn C).bn + 2 + j)).val M = bitE pub.n j)
    (hn : 1 ≤ pub.n ∧ pub.n ≤ 2 ^ 20) (hsb : ∀ i < 256, M.k (bsB C + i) = if sBitsD pub.s i then 1 else 0)
    (hh : pub.h = (List.range 4).map fun l => M.k (hLane l)) (zc : Cell) (b : Bool)
    (hsm : b = true → pub.n ≤ 2 ^ 18) (h : Lvm.QSig.Ok c M (frontU C) q) :
    ∃ tp : Lvm.E2U.TapeU Lvm.RowZ,
      Lvm.Har.PhaseAt (Lvm.E2L.tapeUDGc ivs Lvm.rowSwitchDR p pub.s pub.n) sig
        (posOf p (phaseItem0 p .tape)) (posOf p (phaseItem0 p .openMain)) tp ∧
      List.Forall₂ (Lvm.Q2.FRelZ M zc b) (frontU C q).1.cs
        ((Lvm.E2U.frontItemsU Lvm.rowAccR p pub tp).flatMap Lvm.FItem.flat) ∧
      vs M (frontU C q).1.mb = selectorPoint (pub.n - 1) 20 := by
  obtain ⟨hn1, hn2⟩ := hn
  obtain ⟨T, hTl⟩ : ∃ T, streamLanes p = T := ⟨_, rfl⟩
  rw [hTl] at hS hTo
  -- GOLF3-U: no `streamLanes p` fact left: every later `omega` listed it as an atom and the kernel evaluated the
  -- tally while checking each certificate (0.2–0.5 M heartbeats per `omega`)
  clear hTl
  have hgv : (kc (pbB C)).val M = 1 := by rw [Cell.val_K, hg, ofK_one]
  -- the positions
  obtain ⟨pR, pOut, p20, pQs, pW, pQw, pOp, -⟩ := hf.pos
  simp only [phaseLane] at pR pOut p20 pQs pW pQw
  simp only [wlUG, phaseLane, hf.logN] at hrD hrY hrM
  -- the proof of work, by phase
  simp only [powFrontU, getD_toArray, hf.logN, Nat.reduceMul, Nat.reduceAdd, Nat.reduceSub] at hpow
  obtain ⟨hp3, hpW⟩ := powOkV_append hpow
  obtain ⟨hp2, hpT⟩ := powOkV_append hp3
  obtain ⟨hpR, hp20⟩ := powOkV_append hp2
  clear hpow hp3 hp2
  -- the front's gadgets
  obtain ⟨fo, hfo⟩ : ∃ fo, (frontU C q).1 = fo := ⟨_, rfl⟩
  rw [hfo]
  simp only [frontU, hp, getD_toArray, Lvm.Q1.tapeGadgetE2F_eq, hf.logN, Nat.reduceMul, Nat.reduceAdd,
    Nat.reduceSub] at h hfo
  obtain ⟨q1, hZ, h1, E⟩ := ok_bindE h
  clear h
  rw [E] at hfo
  rw [show (const .E 0 (kc 0) q).1 = ec q.e from rfl] at h1 hfo
  obtain ⟨q2, hO, h2, E⟩ := ok_bindE h1
  clear h1
  rw [E] at hfo
  rw [show (const .E 1 (kc 0) q1).1 = ec q1.e from rfl] at h2 hfo
  obtain ⟨q3, hZK, h3, E⟩ := ok_bindE h2
  clear h2
  rw [E] at hfo
  rw [show (const .K 0 (kc 0) q2).1 = kc q2.k from rfl] at h3 hfo
  obtain ⟨q4, hOK, h4, E⟩ := ok_bindE h3
  clear h3
  rw [E] at hfo
  rw [show (const .K 1 (kc 0) q3).1 = kc q3.k from rfl] at h4 hfo
  have hz : M.e q.e = 0 := (const_val hZ.1).trans ofK_zero
  have ho : M.e q1.e = 1 := (const_val hO.1).trans ofK_one
  have hzk : (kc q2.k).val M = 0 := (const_val hZK.1).trans ofK_zero
  have hok : M.k q3.k = 1 := congrArg FE.c₀ ((const_val hOK.1).trans ofK_one.symm)
  clear hZ hO hZK hOK
  obtain ⟨q5, hV, h5, E⟩ := ok_bindE h4
  clear h4
  rw [E] at hfo
  obtain ⟨q6, hT, h6, E⟩ := ok_bindE h5
  clear h5
  rw [E] at hfo
  obtain ⟨q7, hB, h7, E⟩ := ok_bindE h6
  clear h6
  rw [E] at hfo
  obtain ⟨q8, hW, h8, E⟩ := ok_bindE h7
  clear h7
  rw [E] at hfo
  obtain ⟨q9, hRD, h9, E⟩ := ok_bindE h8
  clear h8
  rw [E] at hfo
  obtain ⟨q10, hND, h10, E⟩ := ok_bindE h9
  clear h9
  rw [E] at hfo
  obtain ⟨q11, hRY, h11, E⟩ := ok_bindE h10
  clear h10
  rw [E] at hfo
  obtain ⟨q12, hNY, h12, E⟩ := ok_bindE h11
  clear h11
  rw [E] at hfo
  obtain ⟨q13, hRM, h13, E⟩ := ok_bindE h12
  clear h12
  rw [E] at hfo
  obtain ⟨q14, hNM, h14, E⟩ := ok_bindE h13
  clear h13
  rw [E] at hfo
  obtain ⟨q15, hME, -, E⟩ := ok_bindE h14
  clear h14
  rw [E] at hfo
  clear E
  -- names
  -- GOLF3-U: `generalize`, not `set`: as `let` values the positions were closed atoms of every later `omega`, which
  -- the kernel evaluated (the lanes' walk) while checking the certificates
  have hq0' : 8 * laneOf p (phaseItem0 p .tape + 2) = posOf p (phaseItem0 p .tape) + 120 := by
    have := pR 0 (by norm_num); simpa using this
  generalize posOf p (phaseItem0 p .tape) = Pt at *
  generalize posOf p (phaseItem0 p .wire) = Pw at *
  generalize posOf p (phaseItem0 p .openMain) = Pop at *
  generalize laneOf p (phaseItem0 p .tape + 45) = qs at *
  generalize laneOf p (phaseItem0 p .wire + 0) = qw at *
  generalize laneOf p (phaseItem0 p .tape + 41) = tOut at *
  generalize laneOf p (phaseItem0 p .tape + 43) = r43 at *
  generalize laneOf p (phaseItem0 p .tape + 2) = q0 at *
  have hri : ∀ i < 20, laneOf p (phaseItem0 p .tape + (2 + 2 * i)) = q0 + 10 * i := fun i hi => by
    have := pR i hi; omega
  have htE : qs + 49 ≤ Lvm.Q1.tapeEnd2 16 qs := by unfold Lvm.Q1.tapeEnd2 Lvm.Q1.tapeQ2; omega
  have hqwE : qw = Lvm.Q1.tapeEnd2 16 qs := by omega
  have hTw : qw + 1027 < T := by omega
  -- GOLF3-U: the tape's end as a variable too (as a closed `omega` atom the kernel evaluated `lay02 16`); the link kept
  -- as a `HEq`, which `omega` does not read
  generalize hE : Lvm.Q1.tapeEnd2 16 qs = E at *
  have hEh : HEq (Lvm.Q1.tapeEnd2 16 qs) E := heq_of_eq hE
  clear hE
  -- T1's values and the tape GKR
  set F : FCtx := ⟨ec q.e, ec q1.e, kc q2.k, ⟨kc q2.k, kc q2.k⟩, ⟨kc q3.k, kc q2.k⟩, false⟩ with hF
  set r : List C2 := (List.range 20).map fun i => Lvm.Q1.laneC2 (laneOf p (phaseItem0 p .tape + (2 + 2 * i)))
    with hr
  set r20 := Lvm.Q1.laneC2 r43 with hr20
  set a : List C2 := (List.range 25).map fun l => Lvm.Q1.laneC2 (tOut + 2 * l) with ha
  set bb : List C2 := (List.range 25).map fun l => Lvm.Q1.laneC2 (tOut + 50 + 2 * l) with hbb
  have hz2v : F.z2.val M = 0 := by
    show (⟨((kc q2.k).val M).c₀, ((kc q2.k).val M).c₀⟩ : FE2) = 0
    rw [hzk]; rfl
  have ho2v : F.o2.val M = 1 := by
    show (⟨((kc q3.k).val M).c₀, ((kc q2.k).val M).c₀⟩ : FE2) = 1
    rw [Cell.val_K, hok, ofK_one, hzk]; rfl
  have hrl : r.length = 20 := by simp [hr]
  have hrv : r.map (C2.val M) = sampsG sig (Pt + 72) 20 := by
    rw [hr, List.map_map]
    unfold sampsG
    refine List.map_congr_left fun i hi => ?_
    have hi' := List.mem_range.mp hi
    simp only [Function.comp_apply]
    rw [hri i hi', Lvm.Q1.laneC2_val hS (by omega)]
    exact congrArg _ (by omega)
  have hr20v : r20.val M = fe2At sig (Pt + 2520) := by rw [hr20, Lvm.Q1.laneC2_val hS (by omega), p20]
  have hav : (List.range 25).map (fun l => (a.getD l default).val M) = readsE2 sig (Pt + 1672) 25 := by
    unfold readsE2
    refine List.map_congr_left fun l hl => ?_
    have hl' := List.mem_range.mp hl
    rw [ha, getD_map_range _ hl', Lvm.Q1.laneC2_val hS (by omega)]
    exact congrArg _ (by omega)
  have hbv : (List.range 25).map (fun l => (bb.getD l default).val M) = readsE2 sig (Pt + 1672 + 16 * 25) 25 := by
    unfold readsE2
    refine List.map_congr_left fun l hl => ?_
    have hl' := List.mem_range.mp hl
    rw [hbb, getD_map_range _ hl', Lvm.Q1.laneC2_val hS (by omega)]
    exact congrArg _ (by omega)
  have habv : ((List.range 25).map fun l => (a.getD l default).val M) ++
      (List.range 25).map (fun l => (bb.getD l default).val M) = readsE2 sig (Pt + 1672) 50 := by
    rw [hav, hbv, show 50 = 25 + 25 from rfl, readsE2_add]
  have hV1 := hs_tOneU F hz2v ho2v r hrl r20 a bb q4 hV.1
  have hinst : (List.range (16 + 5)).map (fun i => ((r ++ [r20]).getD i default).val M) =
      sampsG sig (Pt + 72) 20 ++ [fe2At sig (Pt + 2520)] := by
    rw [show 16 + 5 = (r ++ [r20]).length by simp [hrl], map_range_getD, List.map_append, hrv, List.map_singleton,
      hr20v]
  have hout : (List.range 25).map (fun l => ((tOneU F r r20 a bb q4).1.getD l default).val M) =
      Lvm.E2U.t1ValsF 20 13 (sampsG sig (Pt + 72) 20 ++ [fe2At sig (Pt + 2520)]) (readsE2 sig (Pt + 1672) 50) := by
    rw [List.map_congr_left fun l hl => hV1 l (List.mem_range.mp hl), hrv, hr20v, habv]
    conv_rhs => unfold Lvm.E2U.t1ValsF
    exact List.map_congr_left fun l hl => by
      unfold Lvm.E2U.t1ValsF; exact getD_map_range0 _ (List.mem_range.mp hl)
  have TG := tapeGkr_phaseU hS (P := Pt) (qs := qs) pQs (by rw [eq_of_heq hEh]; omega) hT.1 hT.2 hgv hpT hinst hout
  obtain ⟨TG1, hR⟩ := TG
  set claimV := (tapeGkrD 21 (sampsG sig (Pt + 72) 20 ++ [fe2At sig (Pt + 2520)]) (Lvm.E2U.t1ValsF 20 13
    (sampsG sig (Pt + 72) 20 ++ [fe2At sig (Pt + 2520)]) (readsE2 sig (Pt + 1672) 50)) sig ⟨Pt + 2552, 0, true⟩).1
    with hclaimV
  set cv := (Lvm.Q1.tapeGadgetE2 16 qs (fun i => (r ++ [r20]).getD i default)
    (fun l => ((tOneU F r r20 a bb q4).1).getD l default) (kc (pbB C)) q5).1.cv with hcv
  -- `n' − 1`'s bits
  have hmbv := borrowK_vs (N := pub.n) (show M.k (kc q3.k).n = 1 from hok) (fun j hj => hnb j hj) hn1 hB.1
  have hmb := kC2_bits (m := 20) hzk hmbv
  -- the wire gadget
  have hsbl : (sbCells C).length = 256 := by simp [sbCells]
  have hBs : spongeBlocks p - 1 < 2 ^ 13 := hf.sb
  have hKs : ksSplit p + 399 + 31 < 2 ^ 13 := by rw [hf.ksSplit_eq]; norm_num
  obtain ⟨wo, hwo, WS⟩ := hsA_out (wireGU_sound qw cv _ (sbCells C) (spongeBlocks p) (ksSplit p + 399)
    (kc q2.k) (kc (pbB C)) (pub.n - 1) hzk hgv hsbl hmb (by omega) hBs hKs) hW
  rw [wireLanesU_20] at WS
  dsimp only at WS
  obtain ⟨hs1, hd1, hy1, hm1, hfinW, hDW, hYW, hMW⟩ := WS
  have hpt : cvRho M 16 cv = claimV.point := hR.point
  have hmu : cvMu M cv = claimV.mu := hR.mu
  have hω : ∀ j < 1600, claimV.weights.getD j 0 = omegaF M 16 cv j := fun j hj => Lvm.Q1.rep2_lt_posF hR hj
  have htgt : targetF M 16 cv (((sbCells C).map fun b => kC2 b (kc q2.k)).map (C2.val M)) (pub.n - 1) =
      wireTargetDF (sBitsD pub.s) pub.n claimV := by
    rw [wireTargetDF_eq]
    exact targetF_eq 16 cv claimV pub.s pub.n _ hR.value.symm hmu.symm hpt.symm hω (sb_vals hzk pub.s hsb)
  have hσ : wo.sigma.map (C2.val M) = scPts sig Pw 20 := by rw [hs1]; exact sc2_vals hS pQw (by omega)
  have hτD : wo.tauD.map (C2.val M) = scPts sig (Pw + 2288) 2 := by rw [hd1]; exact sc2_vals hS (by omega) (by omega)
  have hτY : wo.tauY.map (C2.val M) = scPts sig (Pw + 4040) 5 := by rw [hy1]; exact sc2_vals hS (by omega) (by omega)
  have hτM : wo.tauM.map (C2.val M) = scPts sig (Pw + 6128) 5 := by rw [hm1]; exact sc2_vals hS (by omega) (by omega)
  have hg0 : (ld2 (qw + 280)).val M = fe2At sig (Pw + 2280) := by rw [ld2_val hS (by omega)]; exact congrArg _ (by omega)
  have hg1 : (ld2 (qw + 280 + 2)).val M = fe2At sig (Pw + 2296) := by
    rw [ld2_val hS (by omega)]; exact congrArg _ (by omega)
  have hg2 : (ld2 (qw + 280 + 4)).val M = fe2At sig (Pw + 2312) := by
    rw [ld2_val hS (by omega)]; exact congrArg _ (by omega)
  have hcont : [(1, spongeBlocks p - 1), (ksSplit p + 399 + 1, ksSplit p + 399 + 31)] = ivs := hivs
  have hfin : scFold2 (fun k => fe2At sig (8 * k)) 20 qw (wireTargetDF (sBitsD pub.s) pub.n claimV) =
      E2V.msEvalF claimV.point claimV.mu (scPts sig Pw 20) 0 (pub.n - 1) * fe2At sig (Pw + 2280) +
        Lvm.E2U.eTailF 13 20 (scPts sig Pw 20) *
          (Lvm.E2U.kksF ivs claimV.point claimV.mu ((scPts sig Pw 20).take 13) (2 ^ 20) *
              fe2At sig (Pw + 2296) +
            E2V.ikEvalP claimV.point claimV.mu ((scPts sig Pw 20).take 13) (2 ^ 20) * fe2At sig (Pw + 2312)) := by
    rw [← htgt, ← scFold2_ld2 hS (by omega), hfinW, hpt, hmu, hσ, hg0, hg1, hg2, hcont]
  have hD : scFold2 (fun k => fe2At sig (8 * k)) 2 ((Pw + 2288 + 40) / 8) (fe2At sig (Pw + 2280)) =
      E2V.sumF ((List.range 64).map fun z => E2V.slotWF 2 (dWA claimV.weights.toArray) (scPts sig (Pw + 2288) 2) z *
        (readsE2 sig (Pw + 2288 + 112 * 2) 64).getD z 0) := by
    rw [show (Pw + 2288 + 40) / 8 = qw + 286 by omega, ← hg0, ← scFold2_ld2 hS (by omega), hDW, E2V.sumF_eq_sum,
      dWA_eq]
    refine congrArg List.sum (List.map_congr_left fun zz hzz => ?_)
    have hzz' := List.mem_range.mp hzz
    rw [hτD, slotW_eq _ _ (by simp [scPts]) _ hω zz hzz', readsE2_getD _ _ _ hzz', ld2_val hS (by omega)]
    exact congrArg _ (congrArg _ (by omega))
  have hY : scFold2 (fun k => fe2At sig (8 * k)) 5 ((Pw + 4040 + 40) / 8) (fe2At sig (Pw + 2296)) =
      E2V.sumF ((List.range 64).map fun z => E2V.slotWF 5 (Lvm.E2V.yWG claimV.weights) (scPts sig (Pw + 4040) 5) z *
        (readsE2 sig (Pw + 4040 + 112 * 5) 64).getD z 0) := by
    rw [show (Pw + 4040 + 40) / 8 = qw + 505 by omega, ← hg1, ← scFold2_ld2 hS (by omega), hYW, E2V.sumF_eq_sum]
    refine congrArg List.sum (List.map_congr_left fun zz hzz => ?_)
    have hzz' := List.mem_range.mp hzz
    rw [hτY, slotWF_yWG hω _ hzz', readsE2_getD _ _ _ hzz', ld2_val hS (by omega)]
    exact congrArg _ (congrArg _ (by omega))
  have hM : scFold2 (fun k => fe2At sig (8 * k)) 5 ((Pw + 6128 + 40) / 8) (fe2At sig (Pw + 2312)) =
      E2V.sumF ((List.range 64).map fun z => E2V.slotWF 5 (Lvm.E2V.mWG claimV.weights) (scPts sig (Pw + 6128) 5) z *
        (readsE2 sig (Pw + 6128 + 112 * 5) 64).getD z 0) := by
    rw [show (Pw + 6128 + 40) / 8 = qw + 766 by omega, ← hg2, ← scFold2_ld2 hS (by omega), hMW, E2V.sumF_eq_sum]
    refine congrArg List.sum (List.map_congr_left fun zz hzz => ?_)
    have hzz' := List.mem_range.mp hzz
    rw [hτM, slotWF_mWG hω _ hzz', readsE2_getD _ _ _ hzz', ld2_val hS (by omega)]
    exact congrArg _ (congrArg _ (by omega))
  obtain ⟨hpw, hpD, hpY, hpM⟩ := powW_of pQw hpW
  have WP := wireUDGc_phase (P := Pw) (q := qw) ivs p hf.logN hf.ksLog pub.s pub.n claimV pQw hpw hpD hpY hpM hfin hD
    hY hM
  have TG1' : Lvm.Har.PhaseAt (tapeGkrDF 21 (sampsG sig (Pt + 72) 20 ++ [fe2At sig (Pt + 2520)])
      (Lvm.E2U.t1ValsF 20 13 (sampsG sig (Pt + 72) 20 ++ [fe2At sig (Pt + 2520)]) (readsE2 sig (Pt + 1672) 50)))
      sig (Pt + 2552) Pw claimV := by rw [pW, ← eq_of_heq hEh]; exact TG1
  have hp20' : DM.powOKR E2V.gC1 (feAt sig (Pt + 2520)) = true := by
    have := hp20 _ List.mem_cons_self; rwa [p20] at this
  have TP := tapeUDGc_phase (P := Pt) (q0 := q0) ivs p hf.logN hf.ksLog pub.s pub.n hq0' hpR hp20' TG1' ⟨hn1, hn2⟩ WP
  rw [pOp]
  refine ⟨_, TP, ?_, ?_⟩
  · rw [← hfo]
    subst hwo
    simp only [wireLanesU_20] at hrD hrY hrM
    have hsD := slicesOf_reads hS (a := qw + 314) (P := Pw + 2288 + 112 * 2) (by omega) (by omega)
    have hsY := slicesOf_reads hS (a := qw + 575) (P := Pw + 4040 + 112 * 5) (by omega) (by omega)
    have hsM := slicesOf_reads hS (a := qw + 836) (P := Pw + 6128 + 112 * 5) (by omega) (by omega)
    rw [hsD] at hrD
    rw [hsY] at hrY
    rw [hsM] at hrM
    have hTD : (wireLanesU 20 qw).ringD + 9 * 6 + 2 < T := by simp only [wireLanesU_20]; omega
    have hTY : (wireLanesU 20 qw).ringY + 9 * 6 + 2 < T := by simp only [wireLanesU_20]; omega
    have hTM : (wireLanesU 20 qw).ringM + 9 * 6 + 2 < T := by simp only [wireLanesU_20]; omega
    refine front_claimsUG hf (zc := zc) (b := b) (pub := pub) (F := F) (r := r) (a := a) (bb := bb)
      (sY := E2V.selPtF ((layout0 p).ks / 2 ^ (p.ksLog + 5)) (p.nuMain - (p.ksLog + 5)))
      (sM := E2V.selPtF ((layout0 p).s / 2 ^ p.nuRec) (p.nuMain - p.nuRec))
      (eqD := (rowG (wireLanesU 20 qw).ringD (tBu C 0) (ec q.e).n (ec q1.e).n q8).1.eqR.map (Cell.val M))
      (eqY := (rowG (wireLanesU 20 qw).ringY (tBu C 1) (ec q.e).n (ec q1.e).n q10).1.eqR.map (Cell.val M))
      (eqM := (rowG (wireLanesU 20 qw).ringM (tBu C 2) (ec q.e).n (ec q1.e).n q12).1.eqR.map (Cell.val M))
      hz2v ho2v ⟨rfl, rfl⟩ ⟨rfl, rfl⟩ hz ho ?_ hrl ?_ ?_ hrv.symm ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ hσ.symm hτD.symm ?_
      ?_ ?_ ?_ ?_ ?_ ?_ hh hsm hn1
    · intro x hx
      rw [hr] at hx
      obtain ⟨i, -, rfl⟩ := List.mem_map.mp hx
      exact ⟨rfl, rfl⟩
    · intro l hl; rw [ha, getD_map_range _ (by omega)]; exact ⟨rfl, rfl⟩
    · intro l hl; rw [hbb, getD_map_range _ hl]; exact ⟨rfl, rfl⟩
    · intro l hl
      show (readsE2 sig (Pt + 1672) 50).getD l 0 = _
      rw [← habv, List.getD_append _ _ _ _ (by simp; omega), getD_map_range0 _ (by omega)]
    · intro l hl
      show (readsE2 sig (Pt + 1672) 50).getD (25 + l) 0 = _
      rw [← habv, List.getD_append_right _ _ _ _ (by simp), List.length_map, List.length_range,
        Nat.add_sub_cancel_left, getD_map_range0 _ hl]
    · rw [hs1]; exact ld2_K _
    · rw [hs1]; simp [sc2Ans]
    · rw [hd1]; exact ld2_K _
    · rw [hd1]; simp [sc2Ans]
    · rw [hy1]; exact ld2_K _
    · rw [hy1]; simp [sc2Ans]
    · rw [hm1]; exact ld2_K _
    · rw [hm1]; simp [sc2Ans]
    · show ((rowSwitchDR _ _ sig ⟨Pw + 2288 + 112 * 2 + 1024, 0, true⟩).1).1 = _
      rw [row_data hS hz ho hTD hRD.1 (by simp only [wireLanesU_20]; omega) _ _ hrD, hσ, hτD]
    · exact rowNuOk_of hS hz ho hTD hRD.1 hND.1
    · show ((rowSwitchDR _ _ sig ⟨Pw + 4040 + 112 * 5 + 1024, 0, true⟩).1).1 = _
      rw [row_data hS hz ho hTY hRY.1 (by simp only [wireLanesU_20]; omega) _ _ hrY, hσ, hτY]
    · exact rowNuOk_of hS hz ho hTY hRY.1 hNY.1
    · show ((rowSwitchDR _ _ sig ⟨Pw + 6128 + 112 * 5 + 1024, 0, true⟩).1).1 = _
      rw [row_data hS hz ho hTM hRM.1 (by simp only [wireLanesU_20]; omega) _ _ hrM, hσ, hτM]
    · exact rowNuOk_of hS hz ho hTM hRM.1 hNM.1
    · exact (mapB_add_vs (by rw [Cell.val_E, hz]) _ _ hME.1).trans (by rw [hmbv, selectorPoint_bits])
  · rw [← hfo]
    exact hmbv.trans (selectorPoint_bits _ _).symm

theorem frontPF_P20L : FrontPF P20L :=
  ⟨rfl, rfl, rfl, rfl, rfl, by rw [sizes_P20L.1.2.2.2.2.1]; norm_num, posL20.2.2.2.2.2⟩

/-- The wire's `cont` intervals at S2GL are V_S's (`contIvOf 3843`). -/
theorem ivsL20 : [(1, spongeBlocks P20L - 1), (ksSplit P20L + 399 + 1, ksSplit P20L + 399 + 31)] =
    Lvm.E2L.contIvOf 3843 := by
  rw [sizes_P20L.1.2.2.2.2.1, frontPF_P20L.ksSplit_eq]; rfl

end FrontUG

end Lvm.E2Q

/-! ## V_S's S2GL decision from its phases -/

namespace Lvm.Har

open Lvm DM Lvm.E2T Lvm.E2U

theorem linClaims_main (nu : Nat) (ζ : List FE) (css : List (List (FE × Nat × Nat))) (vs : List FE) :
    ∀ e ∈ Lvm.E2L.linClaims nu ζ css vs, e.1 = .main := by
  intro e he
  obtain ⟨_, -, rfl⟩ := List.mem_map.mp he
  rfl

/-- **`dOpenFFL` is `dOpenF`** on the typed items' claims, the three claims, the front's claims. -/
theorem dOpenFFL_eq (p : Params) (s : Bool) (pin : BlockClaim) (ti : List FItem) (ζ : List FE)
    (css : List (List (FE × Nat × Nat))) (vs : List FE) (items : List FItem) :
    Lvm.E2L.dOpenFFL p s pin ti ζ css vs items =
      dOpenF p s pin (ti.flatMap FItem.flat ++ Lvm.E2L.linClaims p.nuMain ζ css vs ++ items.flatMap FItem.flat) := by
  have hm := linClaims_main p.nuMain ζ css vs
  have hall : (Lvm.E2L.linClaims p.nuMain ζ css vs).all (·.1 == .main) = true :=
    List.all_eq_true.mpr fun e he => by rw [hm e he]; rfl
  have hfl : (Lvm.E2L.linClaims p.nuMain ζ css vs).filter (·.1 == .main) = Lvm.E2L.linClaims p.nuMain ζ css vs :=
    List.filter_eq_self.mpr fun e he => by rw [hm e he]; rfl
  unfold Lvm.E2L.dOpenFFL dOpenF
  rw [verifyStackedOpeningG_eq]
  simp only [List.flatMap_cons, List.flatMap_append, groups_flat, List.all_append, hall, Bool.and_true,
    List.filter_append, hfl, List.map_append]
  cases s <;> simp only [SGroup.one, Lvm.E2L.linGroup, toStk, List.map_map, Function.comp_def, Bool.false_eq_true,
    ↓reduceIte, List.singleton_append, List.append_assoc]

private theorem bind_runL {α β : Type} (m : DM α) (f : α → DM β) (sig : ByteArray) (s : RS) :
    (m >>= f) sig s = f (m sig s).1 sig (m sig s).2 := (bind_run' m f sig s).trans rfl
private theorem pure_runL {α : Type} (a : α) (sig : ByteArray) (s : RS) : (pure a : DM α) sig s = (a, s) :=
  (pure_run' a sig s).trans rfl
private theorem skip_runL (n : Nat) (sig : ByteArray) (s : RS) :
    skip n sig s = ((), { s with msg := s.msg + n }) := (skip_run' n sig s).trans rfl
private theorem read_runL (sig : ByteArray) (s : RS) : (read : DM ByteArray) sig s = (sig, s) :=
  (read_run' sig s).trans rfl
private theorem stRunL {α : Type} (x : StateM RS α) (s : RS) : x.run s = x s := (rfl : x.run s = x s).trans rfl

/-- **`decideProgLG` from its phases** (`core_of_phasesU`'s twin: the typed phases at S2GL end at the bus's point and
decomposition; the opening is `dOpenF` on the typed claims, the three claims and the front's). -/
theorem core_of_phasesL (p pT : Params) (B : Nat) (N : TNatT) (vk c : Vector UInt8 32) (sig : ByteArray)
    {Pb P1 P2 P3 : Nat} {pin : BlockClaim} {acc : Acc} {ti : List FItem} {ζ : List FE} {bus : BusOut}
    {tp : TapeU RowZ}
    (hb : pos (RS.startH (headerBytesP p)) + nodeBytes * 2 ^ (p.level ⟨.main, 0⟩).cap = Pb)
    (hpin : PhaseAt (pinD p.nuMain) sig Pb P1 pin)
    (htyped : PhaseAt (Lvm.E2L.dTypedLG pT N (m3G N p) (pubG vk c sig) (typedItemsND N p)) sig P1 P2
      (acc, ti, ζ, bus))
    (htape : PhaseAt (Lvm.E2L.tapeUDGc (Lvm.E2L.contIvOf B) rowSwitchDR p (pubG vk c sig).s (pubG vk c sig).n) sig
      P2 P3 tp)
    (hopen : ∀ s : RS, pos s = P3 → s.ok = true →
      let o := dOpenF p (TypedV.smallT p (pubG vk c sig)) pin
        (ti.flatMap FItem.flat ++ Lvm.E2L.linClaims p.nuMain ζ
            ((List.range 3).map (M3.mbColsN (M3.sumcheckTabs N.mbT) bus))
            ((List.range 3).map (M3.mbValueN (M3.sumcheckTabs N.mbT) bus ζ)) ++
          (frontItemsU rowAccR p (pubG vk c sig) tp).flatMap FItem.flat) sig s
      o.2.ok = true ∧ o.2.ent = sig.size ∧ o.2.msg = 0) :
    ∃ s₉ : RS, Lvm.E2L.decideProgLG p pT B N vk c sig (RS.startH (headerBytesP p)) = (acc, s₉) ∧ s₉.ok = true ∧
      s₉.ent = sig.size ∧ s₉.msg = 0 := by
  obtain ⟨s₀, hs₀⟩ : ∃ s₀ : RS, RS.startH (headerBytesP p) = s₀ := ⟨_, rfl⟩
  have h₀ : s₀.ok = true := by rw [← hs₀]; rfl
  rw [hs₀] at hb ⊢
  obtain ⟨s1, hs1⟩ : ∃ s1 : RS, s1 = { s₀ with msg := s₀.msg + nodeBytes * 2 ^ (p.level ⟨.main, 0⟩).cap } :=
    ⟨_, rfl⟩
  have e1 : pos s1 = Pb := by rw [← hb, hs1]; simp only [pos]; omega
  obtain ⟨a1, a2, a3⟩ := hpin s1 e1 (by rw [hs1]; exact h₀)
  generalize hA : pinD p.nuMain sig s1 = AA at a1 a2 a3
  obtain ⟨av, s2⟩ := AA
  simp only at a1 a2 a3
  rw [a1] at hA
  obtain ⟨b1, b2, b3⟩ := htyped s2 a3 a2
  generalize hB : Lvm.E2L.dTypedLG pT N (m3G N p) (pubG vk c sig) (typedItemsND N p) sig s2 = BB at b1 b2 b3
  obtain ⟨bv, s3⟩ := BB
  simp only at b1 b2 b3
  rw [b1] at hB
  obtain ⟨c1, c2, c3⟩ := htape s3 b3 b2
  generalize hC : Lvm.E2L.tapeUDGc (Lvm.E2L.contIvOf B) rowSwitchDR p (pubG vk c sig).s (pubG vk c sig).n sig s3 = CC
    at c1 c2 c3
  obtain ⟨cv, s4⟩ := CC
  simp only at c1 c2 c3
  rw [c1] at hC
  obtain ⟨o1, o2, o3⟩ := hopen s4 c3 c2
  rw [← dOpenFFL_eq] at o1 o2 o3
  generalize hO : Lvm.E2L.dOpenFFL p (TypedV.smallT p (pubG vk c sig)) pin ti ζ
    ((List.range 3).map (M3.mbColsN (M3.sumcheckTabs N.mbT) bus))
    ((List.range 3).map (M3.mbValueN (M3.sumcheckTabs N.mbT) bus ζ))
    (frontItemsU rowAccR p (pubG vk c sig) tp) sig s4 = OO at o1 o2 o3
  obtain ⟨ov, s5⟩ := OO
  simp only at o1 o2 o3
  refine ⟨s5, ?_, o1, o2, o3⟩
  unfold Lvm.E2L.decideProgLG
  simp only [bind_runL, read_runL, skip_runL, pure_runL]
  rw [← hs1, hA]
  simp only
  rw [hB]
  simp only
  rw [hC]
  simp only
  rw [Lvm.M3.mbValsF_eq, hO]

/-- **`decideFLG` accepts** when its run ends accepting with the accumulator `acc` and `Φ_Q` at `E2` holds at it. -/
theorem decideFLG_of (p pT : Params) (B : Nat) (N : TNatT) (vk c : Vector UInt8 32) (sig : ByteArray) {acc : Acc}
    (hrun : ∃ s₉ : RS, Lvm.E2L.decideProgLG p pT B N vk c sig (RS.startH (headerBytesP p)) = (acc, s₉) ∧
      s₉.ok = true ∧ s₉.ent = sig.size ∧ s₉.msg = 0)
    (hphi : N.phiT (acc.pt.map Lvm.e2OfFE) = Lvm.e2OfFE acc.y) :
    Lvm.E2L.decideFLG p pT B N vk c sig = true := by
  obtain ⟨s₉, h1, h2, h3, h4⟩ := hrun
  have eD : @Lvm.E2L.decideFLG = @Lvm.E2L.decideFLG := rfl
  conv at eD => rhs; delta Lvm.E2L.decideFLG
  rw [eD]
  beta_reduce
  rw [DM.runOnH, stRunL, h1]
  simp only [h2, h3, h4, hphi, beq_self_eq_true, Bool.and_self]

end Lvm.Har

/-! ## The node's pair facts and `NodeSound` over the configuration (ACW-C's RF-2 port onto GOLF3's `LvmE2QNodeU`)

S2GU's `inMapTGLU`, `readdTGLU`, section `PairU` and `nodeSoundCU` at a configuration `C` on S2GU's `C_main` layout
(`CfgU C`) and a child of `b + 1` sponge blocks (`GkB b`); S2GU's lemmas stay as they are. -/

namespace Lvm.E2Q

open RecursionFast Lvm Lvm.T Lvm.ASM Lvm.Replay Lvm.Loop Lvm.Loop.Build Lvm.QLink Lvm.QSig Lvm.M3 Lvm.QAsm Lvm.NS
open Lvm.QTyped Lvm.Typed Lvm.TypedV Lvm.BitsTab Lvm.SigBits LeanVM.Protocol

/-- **A configuration on S2GU's `C_main` layout**: `layout0`, `C_rec`'s and `KS`'s row logs, the stage's layout
branch and the columns' sizes as `P20U`'s, `C_rec`'s rows as `cfg20`'s. -/
structure CfgU (C : QCfg) : Prop where
  lay0 : layout0 C.p = layout0 P20U
  rr : C.p.recRowsLog = 14
  ksl : C.p.ksLog = 13
  stg : C.p.stage = 3
  rl : C.rl = 14
  nm : C.p.nuMain = 23
  nr : C.p.nuRec = 19

theorem CfgU.sCol_eq {C : QCfg} (hC : CfgU C) (l : ℕ) : sCol C.p l = sCol P20U l := by
  rw [sCol, sCol, hC.lay0, hC.rr]; rfl

theorem CfgU.xCol_eq {C : QCfg} (hC : CfgU C) (l : ℕ) : xCol C.p l = xCol P20U l := by
  rw [xCol, xCol, hC.lay0, hC.rr]; rfl

theorem CfgU.ksYCol_eq {C : QCfg} (hC : CfgU C) (l : ℕ) : ksYCol C.p l = ksYCol P20U l := by
  rw [ksYCol, if_pos hC.stg, hC.lay0, hC.ksl, ksYCol_P20U, layout0_P20U]

theorem CfgU.ksSplit_eq {C : QCfg} (hC : CfgU C) : ksSplit C.p = ksSplit P20U := by
  rw [ksSplit, ksSplit, ksXLog, ksXLog, hC.ksl, hC.rr]; rfl

theorem CfgU.s_eq {C : QCfg} (hC : CfgU C) : (layout0 C.p).s = CMain.sOffU20 := by rw [hC.lay0, layout0_P20U]

/-- **The input map's bundles from the check** at a configuration `C` on S2GU's layout (`inMap_of_okGLU` over
`C`). -/
theorem inMap_of_okGLB (C : QCfg) (hC : CfgU C) (B nPub : ℕ) (N : TNat) (pl : Lvm.Pub → List FK) (Q : Program)
    (tl : Typed.Lay) (hlay : tl.Ok Q) (pub : Lvm.Pub) (qm : Column CMain.nu20) (qr : Column 19)
    (hS : SBlkS CMain.sOffU20 qm qr) (hok : N.okB 23 19 = true) (hl : N.layOk tl = true)
    (hσ : SigInSL CMain.sOffU20 N) (h : inMapBGL B nPub C Q tl N = true) :
    let M := memOf tl ((N.instL pl Q tl).zOf lay26 pub qm qr)
    CellsAt M.k lay26 qm qr 17 14 (Lvm.QAsm.lay C).sb true (fun l ↦ l * 2 ^ 14) ∧
      CellsAt M.k lay26 qm qr 1 10 (sigIn C).sg true (fun _ ↦ 17 * 2 ^ 14) ∧
      CellsAt M.k lay26 qm qr 17 9 (sigIn C).xs false (fun l ↦ xCol P20U l) ∧
      CellsAt M.k lay26 qm qr 4 9 (sigIn C).ys false (fun l ↦ ksYCol P20U l + ksSplit P20U) ∧
      CellsAt M.k lay26 qm qr 4 0 (sigIn C).md false (fun l ↦ ksYCol P20U l + (B - 1)) ∧
      ∀ j < nPub, M.k ((sigIn C).flag + j) = (pl pub).getD j 0 := by
  intro M
  have hs : (layout0 C.p).s = CMain.sOffU20 := hC.s_eq
  simp only [inMapBGL, Bool.and_eq_true] at h
  obtain ⟨⟨⟨⟨⟨hSt, hG⟩, hX⟩, hY⟩, hMd⟩, hP⟩ := h
  rw [hs] at hSt hG hX hY hMd hP
  have f1 : ∀ j < 17 * 2 ^ 14, j % 17 * 2 ^ 14 + j / 17 < 2 ^ 19 := fun j hj ↦ by omega
  have f2 : ∀ j < 1 * 2 ^ 10, 17 * 2 ^ 14 + j / 1 < 2 ^ 19 := fun j hj ↦ by omega
  refine ⟨bundleS_of_okLS sOffU20_mod sOffU20_fit N pl Q tl hlay _ qm qr hS hok hl hσ f1
      (fun l r ↦ by rw [hC.sCol_eq, sCol_P20U, Nat.add_assoc]) hSt,
    bundleS_of_okLS sOffU20_mod sOffU20_fit N pl Q tl hlay _ qm qr hS hok hl hσ f2
      (fun l r ↦ by rw [hC.sCol_eq, sCol_P20U, Nat.add_assoc]) hG,
    bundle_of_okLS sOffU20_mod sOffU20_fit N pl Q tl hlay _ qm qr hS hok hl hσ
      (fun l r ↦ by simp only [hC.xCol_eq]) hX,
    bundle_of_okLS sOffU20_mod sOffU20_fit N pl Q tl hlay _ qm qr hS hok hl hσ
      (fun l r ↦ by simp only [hC.ksYCol_eq, hC.ksSplit_eq]) hY,
    bundle_of_okLS sOffU20_mod sOffU20_fit N pl Q tl hlay _ qm qr hS hok hl hσ
      (fun l r ↦ by simp only [hC.ksYCol_eq]) hMd,
    fun j hj ↦ ?_⟩
  exact cell_of_okLS sOffU20_mod sOffU20_fit N pl Q tl hlay pub qm qr hS hok hl hσ
    (List.all_eq_true.mp hP j (List.mem_range.mpr hj))

/-- **The input map on a pair's memory** at a configuration `C` on S2GU's layout (`inMapTGLU` over `C`). -/
theorem inMapTGLB (C : QCfg) (hC : CfgU C) (B nPub : ℕ) (N : TNat) (pl : Lvm.Pub → List FK) (Q : Program)
    (tl : Typed.Lay) (pb : List UInt8 → Lvm.Pub) (hlay : tl.Ok Q) (hreg : N.okB 23 19 = true) (hl : N.layOk tl = true)
    (hσ : SigInSL CMain.sOffU20 N) (hin : inMapBGL B nPub C Q tl N = true) (hB : B ≤ 2 ^ 13)
    (hm : 2 ^ (lay C).m ≤ 17 * 2 ^ 14) (hn : 615 ≤ nPub)
    (hpub : ∀ x, ∀ j < nPub, (pl (pb x)).getD j 0 = hdrLane x j)
    {vk c : RecursionFast.Digest} {x : List UInt8} (qm : Column CMain.nu20) (qr : Column 19)
    (hSB : SBlkS CMain.sOffU20 qm qr) (hok : okS vk c x = true) (hb1 : (hdrOf x).b = 1) :
    InMapMBU B nPub (lay C) (sigIn C) (memOf tl ((N.instL pl Q tl).zOf lay26 (pb x) qm qr)) vk x qm qr := by
  obtain ⟨hS, hG, hX, hY, hMd, hP⟩ := inMap_of_okGLB C hC B nPub N pl Q tl hlay (pb x) qm qr hSB hreg hl hσ hin
  have hP' : ∀ j < nPub, (memOf tl ((N.instL pl Q tl).zOf lay26 (pb x) qm qr)).k ((sigIn C).flag + j) =
      hdrLane x j := fun j hj ↦ (hP j hj).trans (hpub x j hj)
  have hPC : PubCells (memOf tl ((N.instL pl Q tl).zOf lay26 (pb x) qm qr)).k x (sigIn C).flag :=
    fun j hj ↦ hP' j (lt_of_lt_of_le hj hn)
  have hy := ys_vU hY rfl rfl rfl
  exact ⟨fun j hj ↦ stream_v hS (lt_of_lt_of_le hj hm), flag_v hPC hb1, xs_vU hX, hy.1, hy.2.1, hy.2.2.1,
    hy.2.2.2, (vk_v hPC).trans (okS_vk hok), cL_v hPC, sl_v hPC, md_vU hB hMd, sg_v hG, hd_v hS rfl, hP'⟩

/-- **`ReaddOk` on a stream-block pair's memory** at a configuration `C` on S2GU's layout (`readdTGLU` over `C`). -/
theorem readdTGLB (C : QCfg) (hC : CfgU C) (F : TFrz) (Q : Program) (tl : Typed.Lay) (N : TNat)
    (pl : Lvm.Pub → List FK) (pub : Lvm.Pub) (B nPub : ℕ) (hlay : tl.Ok Q) (hreg : N.okB 23 19 = true)
    (hl : N.layOk tl = true)
    (hσ : SigInSL CMain.sOffU20 N) (hchk : nodeChkBGL B nPub C F Q tl N = true) (hc : nK C ≤ Q.cells .K)
    {qm : Column CMain.nu20} {qr : Column 19} (hτ : ∀ t ∈ mbTOf C F, t.τ ≤ lay26.μ)
    (hLay : LayOk lay26 (mbTOf C F)) (hM : M3Holds (inst lay26 (mbTOf C F) hτ) () (stackOf lay26 qm qr))
    (hSB : SBlkS CMain.sOffU20 qm qr) (hlin : NonReaddHolds Q (memOf tl ((N.instL pl Q tl).zOf lay26 pub qm qr))) :
    ReaddOk Q (memOf tl ((N.instL pl Q tl).zOf lay26 pub qm qr)) := by
  have hs : (layout0 C.p).s = CMain.sOffU20 := hC.s_eq
  have hnK : 17 * 2 ^ 14 ≤ nK C := by
    unfold nK obB qtB pbB mdB ysB xsB sgB nStream
    rw [hC.rl]; generalize 2 ^ C.aQT = u; generalize 2 ^ C.bo = w; omega
  simp only [nodeChkBGL, Bool.and_eq_true] at hchk
  obtain ⟨⟨hin, hrd⟩, hsd⟩ := hchk
  rw [hs] at hrd
  simp only [mbSeedsOkB, Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq] at hsd
  obtain ⟨hblk, hlen⟩ := hsd
  have hS := (inMap_of_okGLB C hC B nPub N pl Q tl hlay pub qm qr hSB hreg hl hσ hin).1
  refine readdOk_of_chkLS sOffU20_mod sOffU20_fit C F Q tl N pl hlay pub qm qr hSB hreg hl hσ hrd ?_ ?_ hlin
  · intro τ wa wv hp y hy
    obtain ⟨k, hk⟩ := List.mem_iff_getElem?.mp hp
    exact mbRead_seeded C F lay26 hτ qm qr hLay hM hlen hk hy
  · intro lq hlq x' hx'
    obtain ⟨hl17, hq⟩ := hblk lq hlq
    rw [hC.rl] at hq
    have hx'16 : x' < 16 := hx'
    have hj : 17 * (lq.2 + x') + lq.1 < 17 * 2 ^ 14 := by omega
    have e : (Lvm.QAsm.lay C).sb + 17 * lq.2 + lq.1 + 17 * x' =
        (Lvm.QAsm.lay C).sb + (17 * (lq.2 + x') + lq.1) := by ring
    have h16 : (2 : ℕ) ^ 14 = 16384 := by norm_num
    refine ⟨?_, ?_⟩
    · have hsb : (Lvm.QAsm.lay C).sb = 0 := rfl
      rw [e, hsb]
      (clear * - hj hnK hc; omega)
    · have h1 := hS (17 * (lq.2 + x') + lq.1) hj
      beta_reduce at h1
      have e2 : (17 * (lq.2 + x') + lq.1) % 17 * 2 ^ 14 + (17 * (lq.2 + x') + lq.1) / 17 =
          lq.1 * 2 ^ C.rl + lq.2 + x' := by
        rw [hC.rl, h16]; omega
      have hs' : Lvm.sCol C.p lq.1 + lq.2 + x' = CMain.sOffU20 + (lq.1 * 2 ^ C.rl + lq.2 + x') := by
        rw [hC.sCol_eq, sCol_P20U, hC.rl]
        omega
      rw [e, h1, e2, hs', comCell_SS sOffU20_fit hSB (by rw [hC.rl, h16]; omega)]

section PairB

variable {C : QCfg} {B nPub : ℕ} {F : TFrz} {Q : Program} {tl : Typed.Lay} {N : TNat}
  (S : NodeGCL C B nPub F Q tl N) (pl : Lvm.Pub → List FK) (pb : List UInt8 → Lvm.Pub)
  {x : List UInt8} {qm : Column CMain.nu20} {qr : Column 19}
include S

theorem regsCB (hC : CfgU C) : N.okB 23 19 = true := by
  have h := S.st.regs
  rwa [hC.nm, hC.nr] at h

theorem sigCB (hC : CfgU C) : SigInSL CMain.sOffU20 N := by
  have h := S.sig
  rwa [hC.s_eq] at h

theorem hqltCB (Ti : TInst) (hTi : Ti.lay = tl) :
    ∀ y < (qltData C.p (lay C)).length,
      (memTX Ti pb x qm qr).k ((lay C).qt + y) = (qltData C.p (lay C)).getD y 0 := by
  subst hTi
  exact hqltG C _ S.st.cst _

theorem hlinCB (hone : (N.instL pl Q tl).src? tl.one = some .one)
    (hW : WiringRelX Q tl (zTX (N.instL pl Q tl) pb x qm qr)) :
    NonReaddHolds Q (memTX (N.instL pl Q tl) pb x qm qr) :=
  nonReadd_of_wiringX Q tl _ S.st.wf S.st.twins S.st.hlay (zOf_one (N.instL pl Q tl) hone lay26 (pb x) qm qr) hW

theorem readdCB (hC : CfgU C) (hone : (N.instL pl Q tl).src? tl.one = some .one)
    (hW : WiringRelX Q tl (zTX (N.instL pl Q tl) pb x qm qr)) (hτ : ∀ t ∈ N.mbT, t.τ ≤ lay26.μ)
    (hL : LayOk lay26 N.mbT) (hM : M3Holds (inst lay26 N.mbT hτ) () (stackOf lay26 qm qr))
    (hSB : SBlkS CMain.sOffU20 qm qr) :
    ReaddOk Q (memTX (N.instL pl Q tl) pb x qm qr) := by
  have hτ' : ∀ t ∈ mbTOf C F, t.τ ≤ lay26.μ := fun t ht ↦ hτ t (by rw [S.mb]; exact ht)
  have hL' : LayOk lay26 (mbTOf C F) := by rwa [S.mb] at hL
  exact readdTGLB C hC F Q tl N pl (pb x) B nPub S.st.hlay (regsCB S hC) S.st.hlayOk (sigCB S hC) S.chk S.cells hτ'
    hL' (m3Holds_eq S.mb hM) hSB (hlinCB S pl pb hone hW)

theorem hholdsCB (hC : CfgU C) (hone : (N.instL pl Q tl).src? tl.one = some .one)
    (hW : WiringRelX Q tl (zTX (N.instL pl Q tl) pb x qm qr)) (hτ : ∀ t ∈ N.mbT, t.τ ≤ lay26.μ)
    (hL : LayOk lay26 N.mbT) (hM : M3Holds (inst lay26 N.mbT hτ) () (stackOf lay26 qm qr))
    (hSB : SBlkS CMain.sOffU20 qm qr) :
    (N.instL pl Q tl).Q.Holds (memTX (N.instL pl Q tl) pb x qm qr) ∧
      (N.instL pl Q tl).Q.Asserts (memTX (N.instL pl Q tl) pb x qm qr) :=
  holds_memTX S.st.wf S.st.twins S.st.hlay hone hW (readdCB S pl pb hC hone hW hτ hL hM hSB)

theorem hmapCB (hC : CfgU C) (St : NodeStC C) (hB : B ≤ 2 ^ 13) (hn : 615 ≤ nPub)
    (hpub : ∀ x, ∀ j < nPub, (pl (pb x)).getD j 0 = hdrLane x j)
    {vk c : RecursionFast.Digest} (hok : okS vk c x = true) (hb : (hdrOf x).b = 1)
    (hSB : SBlkS CMain.sOffU20 qm qr) :
    InMapMBU B nPub (lay C) (sigIn C) (memTX (N.instL pl Q tl) pb x qm qr) vk x qm qr := by
  have hchk := S.chk
  simp only [nodeChkBGL, Bool.and_eq_true] at hchk
  exact inMapTGLB C hC _ _ N pl Q tl pb S.st.hlay (regsCB S hC) S.st.hlayOk (sigCB S hC) hchk.1.1 hB St.wsl hn hpub
    qm qr hSB hok hb

theorem outsOnCB (hone : (N.instL pl Q tl).src? tl.one = some .one)
    (hW : WiringRelX Q tl (zTX (N.instL pl Q tl) pb x qm qr)) :
    OutsOnC C (memTX (N.instL pl Q tl) pb x qm qr).k := by
  obtain ⟨bw, haux⟩ := S.aux
  exact outsOnC_of C tl _ bw haux fun hk hj hr ↦
    auxRow_of_wiringX Q tl _ S.st.hlay (zOf_one (N.instL pl Q tl) hone lay26 (pb x) qm qr) hW hk hj hr

theorem hposCB (hC : CfgU C) (St : NodeStC C) (hB : B ≤ 2 ^ 13) (hn : 615 ≤ nPub)
    (hpub : ∀ x, ∀ j < nPub, (pl (pb x)).getD j 0 = hdrLane x j) (hone : (N.instL pl Q tl).src? tl.one = some .one)
    (hW : WiringRelX Q tl (zTX (N.instL pl Q tl) pb x qm qr)) {vk c : RecursionFast.Digest}
    (hok : okS vk c x = true) (hb : (hdrOf x).b = 1) (hSB : SBlkS CMain.sOffU20 qm qr) :
    ∀ k < (opens C.p).length, ∀ j < ((opens C.p).getD k default).L.t,
      ∀ z < ((opens C.p).getD k default).L.height,
      (memTX (N.instL pl Q tl) pb x qm qr).k
          (bitBase C.p (lay C) k + ((opens C.p).getD k default).L.height * j + z) =
        if ansBit C.p (wsC qr) (((opens C.p).getD k default).pe + j / 8)
          (j % 8 * ((opens C.p).getD k default).L.height + z) then 1 else 0 :=
  hposTC (C := C) St.stream St.qok
    (outsOnCB S pl pb hone hW) (hmapCB S pl pb hC St hB hn hpub hok hb hSB).stream

theorem hbitsCB (St : NodeStC C) (hone : (N.instL pl Q tl).src? tl.one = some .one)
    (hW : WiringRelX Q tl (zTX (N.instL pl Q tl) pb x qm qr)) :
    SigBits (sigIn C) (qsig (sigIn C) (p1P (lay C) (nK C) 0 C.p)).1
      (memTX (N.instL pl Q tl) pb x qm qr).k :=
  have hln : C.ln = 20 := St.ln
  sigBits_ofC C (outsOnCB S pl pb hone hW) ⟨by omega, by omega⟩

end PairB

/-- **`NodeSound` from the parts** at a configuration `C` with the statics `St` and a child of `b + 1` sponge blocks
(`nodeSoundCU` over `C` and `b`: the Keccak half `GkB b`). -/
theorem nodeSoundCB (C : QCfg) (b : ℕ) (VS : SProg)
    (D : RecursionFast.Digest → RecursionFast.Digest → ByteArray → Bool)
    (hVS : ∀ vk c π, VS vk c π = if parseOk C.p vk c π then drive C.p π (D vk c) else .ret false)
    (St : NodeStC C) (hbB : spongeBlocks C.p = b + 1) (nPub : ℕ) (pb : List UInt8 → Lvm.Pub)
    (vk : RecursionFast.Digest) (Ti : TInst) (qa : BM Unit) (G : GoodRel)
    (hQ : Ti.Q = toProgram (nK C) 0 (qprogP C.p (lay C) (sigIn C) qa))
    (hinj : GInj (max (Ti.Q.cells .K) (Ti.Q.cells .E)))
    (hGK : ∀ c x qm qr, okS vk c x = true → G x qm qr →
      Lvm.E2U.GkB b x (qm, qr) ∧ BndS x qm ∧ Lvm.E2U.SBlkU qm qr)
    (hholds : ∀ c x qm qr, okS vk c x = true → (hdrOf x).b = 1 → G x qm qr →
      Ti.Q.Holds (memTX Ti pb x qm qr) ∧ Ti.Q.Asserts (memTX Ti pb x qm qr))
    (hmap : ∀ c x qm qr, okS vk c x = true → (hdrOf x).b = 1 → G x qm qr →
      InMapMBU (spongeBlocks C.p) nPub (lay C) (sigIn C) (memTX Ti pb x qm qr) vk x qm qr)
    (hqlt : ∀ c x qm qr, okS vk c x = true → (hdrOf x).b = 1 → G x qm qr →
      ∀ y < (qltData C.p (lay C)).length,
        (memTX Ti pb x qm qr).k ((lay C).qt + y) = (qltData C.p (lay C)).getD y 0)
    (hpos : ∀ c x qm qr, okS vk c x = true → (hdrOf x).b = 1 → G x qm qr →
      ∀ k < (opens C.p).length, ∀ j < ((opens C.p).getD k default).L.t,
        ∀ z < ((opens C.p).getD k default).L.height,
        (memTX Ti pb x qm qr).k (bitBase C.p (lay C) k + ((opens C.p).getD k default).L.height * j + z) =
          if ansBit C.p (wsC qr) (((opens C.p).getD k default).pe + j / 8)
            (j % 8 * ((opens C.p).getD k default).L.height + z) then 1 else 0)
    (hbits : ∀ c x qm qr, okS vk c x = true → (hdrOf x).b = 1 → G x qm qr →
      SigBits (sigIn C) (qsig (sigIn C) (p1P (lay C) (nK C) 0 C.p)).1 (memTX Ti pb x qm qr).k)
    (harith : ∀ c x qm qr, okS vk c x = true → (hdrOf x).b = 1 → G x qm qr →
      InMapMBU (spongeBlocks C.p) nPub (lay C) (sigIn C) (memTX Ti pb x qm qr) vk x qm qr →
      LaneLink C.p (wsC qr) → LinkOk C.p (decode C.p (wsC qr)) →
      Ok (ctxOf Ti.Q) (memTX Ti pb x qm qr) qa (p2P (lay C) (sigIn C) (nK C) 0 C.p) →
      D vk (hdrOf x).cL (traceBytesB (decode C.p (wsC qr))) = true) :
    NodeSound VS vk G (childSP C.p) := by
  refine nodeSound_of (fun c x qm qr hok hG ↦ ?_) fun c x qm qr hok hb hG ↦ ?_
  · obtain ⟨hK, hBn, -⟩ := hGK c x qm qr hok hG
    exact Lvm.KG.chain_of_tape (okS_n hok).1 (okS_n hok).2 ⟨hK.1, hBn (okS_n hok).2⟩
  have hK := hGK c x qm qr hok hG
  obtain ⟨hH, hA⟩ := hholds c x qm qr hok hb hG
  have hinj' := hinj
  rw [hQ] at hH hA hinj'
  have P := parts_of_holdsP hH hA
  have mp := hmap c x qm qr hok hb hG
  have hwsl : 2 ^ (lay C).m ≤ (wsC qr).length := by
    rw [wsC, wsOf, List.length_map, List.length_range]; exact St.wsl
  have hqin : QIn C.p (lay C) (wsC qr) (memTX Ti pb x qm qr) :=
    ⟨mp.flag, mp.stream, hqlt c x qm qr hok hb hG, hpos c x qm qr hok hb hG⟩
  have hN : (ctxOf (toProgram (nK C) 0 (qprogP C.p (lay C) (sigIn C) qa))).cells .K ≤
      max ((toProgram (nK C) 0 (qprogP C.p (lay C) (sigIn C) qa)).cells .K)
        ((toProgram (nK C) 0 (qprogP C.p (lay C) (sigIn C) qa)).cells .E) := by
    rw [NS.ctxOf_cells]; exact le_max_left _ _
  have hNs : (lay C).sb + 2 ^ (lay C).m ≤
      max ((toProgram (nK C) 0 (qprogP C.p (lay C) (sigIn C) qa)).cells .K)
        ((toProgram (nK C) 0 (qprogP C.p (lay C) (sigIn C) qa)).cells .E) :=
    le_trans St.ns (le_trans (nK_le_cells _ _ _) (le_max_left _ _))
  obtain ⟨hLL, hpad⟩ := qlink_sound St.stream St.qok hqin hwsl hinj' hN hNs P.1.1 P.1.2
  have hlink := linkOk_of_laneLink St.stream hLL
  have hks := Lvm.E2U.sigKSin_of_GkB (by have := St.blk; omega) hK.1 mp.xs mp.ys mp.yc mp.yls mp.yns
  obtain ⟨hsig, hchild⟩ := qsig_sound_in (by rw [St.ln]; omega) P.2.1 mp.flag hks
    (hbits c x qm qr hok hb hG) fun a b ha hb h => FK.FKx_pow_inj (by omega) (by omega) h
  have hmd := (digAt_of_cells mp.md).trans
    (Lvm.E2U.traceDigest_of_GkB St.stream hbB St.nblk St.blk hK.1 hK.2.2 hLL hpad)
  have har := harith c x qm qr hok hb hG mp hLL hlink (by rw [hQ]; exact P.2.2)
  exact accV_childC C.p VS D hVS St.plan qr hlink har hsig hchild St.ln mp.vk mp.cL mp.sl hmd mp.sg mp.hd
    (okS_sig hok hb)

/-! ## `typedGL`'s shape (the typed claims' inputs and the three claims' bus) -/

section ShapeL

open Lvm.Har Lvm.Q2

variable {c : Ctx} {M : Mem}

/-- **`typedGL`'s outputs** (`typedGT_shape`'s twin): the relay's and wire's cells are `K` pairs, no table outputs, and
the mini-bus's claims satisfy whatever `mbLinG` guarantees on a bus whose `α` and point cells are `E` cells, `busBits`
and `busDepth` of them. -/
theorem typedGL_shape (Td : TData) (p : Params) (pb n : Nat) (z o zk ok : Cell) (hD : Td.mbD = p.busDepth)
    (Φ : BusC → List CClaim → Prop)
    (hΦ : ∀ bc : BusC, bc.al.length = busBits → (∀ x ∈ bc.al, x.ty = .E) → (∀ x ∈ bc.pt, x.ty = .E) →
      bc.pt.length = p.busDepth → SoundG c M (mbLinG z o Td bc) (Φ bc)) :
    SoundG c M (typedGL Td p pb n z o zk ok) (fun t => ((t.1.ry.length = tY ∧ ∀ x ∈ t.1.ry, KC2 x) ∧
      (t.1.rr.length = tR ∧ ∀ x ∈ t.1.rr, KC2 x) ∧ KC2 t.1.vR ∧ (∀ x ∈ t.1.rv, KC2 x)) ∧ t.1.tab = [] ∧
      Φ t.1.bus t.2) := by
  have hsg : ∀ {α : Type} {m : BM α} {P : α → Prop}, Hs c M m P → SoundG c M m P := fun h q hH _ => h q hH
  unfold typedGL
  dsimp only
  refine soundG_bind (Φ := fun _ => True) (fun _ _ _ => trivial) fun zr _ => ?_
  refine soundG_bind (hsg (hs_wireGT_fst _ _ _ _ _ _ _ _)) fun w ⟨hw1, hw2⟩ => ?_
  refine soundG_bind (hsg (hs_relayGT_fst _ _ _ _ _ _ _)) fun r ⟨hr1, hr2⟩ => ?_
  refine soundG_bind (Φ := fun _ => True) (fun _ _ _ => trivial) fun _ _ => ?_
  refine soundG_bind (Φ := fun bc : BusC => bc.al.length = busBits ∧ (∀ x ∈ bc.al, x.ty = .E) ∧
    (∀ x ∈ bc.pt, x.ty = .E) ∧ bc.pt.length = p.busDepth) ?_ fun bc ⟨h1, h2, h3, h4⟩ => ?_
  · intro q _ _
    have e1 : busGD Td.mbD z o (kc pb) (mbPT p) = busG p z o (kc pb) (mbPT p) := by rw [hD]; rfl
    rw [e1]
    obtain ⟨ha, d, hd⟩ := busG_fst p z o (kc pb) (mbPT p) q
    refine ⟨by rw [ha, List.length_map, List.length_range], fun x hx => ?_, fun x hx => ?_,
      busG_pt_len p z o (kc pb) (mbPT p) q⟩
    · rw [ha] at hx
      obtain ⟨_, -, rfl⟩ := List.mem_map.mp hx
      rfl
    · rw [hd] at hx
      obtain ⟨_, -, rfl⟩ := List.mem_map.mp hx
      rfl
  refine soundG_bind (hΦ bc h1 h2 h3 h4) fun cs hcs => soundG_pure ⟨⟨⟨by rw [hw1]; simp, by
    rw [hw1]; exact kc2_range _ _ _⟩, ⟨by rw [hr1]; simp, by rw [hr1]; exact kc2_range _ _ _⟩,
    by rw [hr2]; exact kc2_ld2 _, ?_⟩, rfl, hcs⟩
  show ∀ x ∈ w.2.2, KC2 x
  rw [hw2]
  intro x hx
  obtain ⟨j, -, rfl⟩ := List.mem_map.mp hx
  exact kc2_ld2 _

end ShapeL

/-! ### At S2GL (`cfgL20`) -/

/-- `QOk` reads a layout's `sb`, `m`, `K`, `aQ` and `pa` only. -/
theorem qOk_congr {p : Params} {L L' : Layout} (hsb : L'.sb = L.sb) (hm : L'.m = L.m) (hK : L'.K = L.K)
    (haQ : L'.aQ = L.aQ) (hpa : L'.pa = L.pa) (h : QOk p L) : QOk p L' := by
  have hq : qltEntries p L' = qltEntries p L := by simp only [qltEntries, hsb]
  exact ⟨by rw [hq, haQ]; exact h.qlen, by rw [hq, hsb, hm]; exact h.qbound, by rw [hm]; exact h.hT,
    by simp only [hK, hm]; exact h.opens, by rw [hpa]; exact h.pos⟩

theorem cfgU_L20 : CfgU cfgL20 := ⟨rfl, rfl, rfl, by decide, rfl, rfl, rfl⟩

/-- **Q_link's static checks at S2GL** (`qOkF_P20L`; `lay cfgL20` is `lay cfgU20`). -/
theorem hQL20 : QOk P20L (lay cfgL20) :=
  qOk_congr (by decide) (by decide) (by decide) (by decide) (by decide)
    (qOk_of streamOk_P20L ((qOkF_eq _ _).symm.trans qOkF_P20L))

/-- S2GL's plan facts. -/
theorem planC_P20L : PlanC P20L :=
  planC_ofR passR_P20L planSt_P20L.1 (by decide) sizes_P20L.1.1 (by norm_num) sizes_P20L.1.2.2.1
    (by norm_num) (by norm_num) rfl

/-- **S2GL's node statics.** -/
theorem nodeStL20 : NodeStC cfgL20 :=
  ⟨streamOk_P20L, hQL20, by decide,
    by rw [show cfgL20.p = P20L from rfl, sizes_P20L.1.2.2.2.2.1]; norm_num,
    by rw [show cfgL20.p = P20L from rfl, sizes_P20L.1.2.2.2.2.1, sizes_P20L.1.2.2.1]; rfl, rfl,
    by decide, by decide, planC_P20L⟩

end Lvm.E2Q
