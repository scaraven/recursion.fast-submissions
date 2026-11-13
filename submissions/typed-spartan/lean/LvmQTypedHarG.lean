-- New for lvm2 (roll 8 = B1, L-H): the typed core gadget `typedG` replays V_S's typed phases `dTypedT` (the
-- composition of the zerocheck's, the wiring's, the relayout's, A23's and the mini-bus's replays), generic in the
-- parameters, the static data and the instance.
import LvmQTypedHarZ
import LvmQTypedHarR
import LvmQTypedHarA
import LvmQTypedHarM

/-!
# `typedG` replays `dTypedT`

**`typedG_replaysG`**: on regions that are V_S's (`TdOk`) and mini-bus tables whose shapes, rounds, depth and fixed
columns are the circuit's, wherever `typedG Td pb P z o`'s rows hold and assert (gate on), `dTypedT p N (N.m3 p)` on
the child's `PUB` from any state at `P` with `ok` keeps `ok`, ends at `typedEnd Td P`; its accumulator is the current
proof's `acc_in` (`accC M pb`), its claims are `typedClaimsN` of the output cells, its evaluations the table cells'.
-/

set_option autoImplicit false

namespace Lvm.Har

open Lvm Lvm.Loop Lvm.Loop.Build Lvm.QTyped Lvm.Q1 Lvm.M3 DM
open Lvm.TypedV (TNat)

/-! ## The positions -/

theorem typedPos_le (Td : TData) (P : Nat) :
    wGP P ≤ rRP P ∧ rRP P ≤ aP P ∧ aP P ≤ mbP P ∧ mbP P ≤ typedEnd Td P := by
  have h1 : mbP P ≤ busEndD Td.mbD (mbP P) := by
    unfold busEndD
    have := le_layersEnd (gkrSteps Td.mbD) 0 (busP1 (mbP P) + 48)
    simp only [busP1] at this ⊢
    omega
  have h2 : busEndD Td.mbD (mbP P) ≤ typedEnd Td P := by
    unfold typedEnd tabEnd; omega
  refine ⟨?_, ?_, ?_, le_trans h1 h2⟩ <;> simp only [wGP, rRP, aP, mbP, wRP, wVP, rVP] <;> omega

theorem typedPos_mod {P : Nat} (hP : P % 8 = 0) :
    wGP P % 8 = 0 ∧ rRP P % 8 = 0 ∧ aP P % 8 = 0 ∧ mbP P % 8 = 0 := by
  simp only [wGP, rRP, aP, mbP, wRP, wVP, rVP, zAbcP, zRP, tX, tY, tR, tVars]
  omega

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
  simp only [typedG, bind_apply, pure_apply, TypedV.dTypedT, bind_run', pure_run']
  rw [show N.m3 p = M3.real p (fun _ => N.mbT) from rfl]
  -- the zerocheck
  obtain ⟨hZ, hok⟩ := okb hok
  generalize hzr : (zeroG z (kc pb) P q).1 = zr at hok ⊢
  generalize hq1 : q.adv (zeroG z (kc pb) P q).2 = q1 at hok ⊢
  have hq1e : 1 ≤ q1.e := le_trans hq (by rw [← hq1]; exact adv_e_le _ _)
  have RZ := zeroG_replays (c := c) hS hz hzE hgv rfl hP (by omega) q hq hZ s hs hsok
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
  have RW := wireG_replays (c := c) vk cL hS hH hz ho hzE hoE hgv rfl htd hvk hP (by omega) zr.2 q1 hq1e hW s1 z2 z1
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
  have RR := relayG_replays (c := c) hS hz ho hzE hoE hgv rfl htd hP (by omega) w.1 w6 w7 (w.2.2.getD 1 z) q2
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
  have RA := qaccT_replays (c := c) vk cL hS hH hg hP (by omega) zr.1 w.1 w.2.1 z7 w6 w8 hE q3 hA s3 r2 r1
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
