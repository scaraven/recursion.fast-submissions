-- New for lvm2 (CR-Q, roll 7 SH2-Z): glue between Q_arith's cells and `V_S`'s roll-7 phases: the ring
-- coefficients `dWireC` also returns are the wire gadget's coefficient cells (`dWireC_snd`, from T-W's
-- `wire_spec` reading and `wire_core`), and the tails' closed forms agree (`tailD`/`tailDF`, `tailR`/`ringTailN`).
import LvmQWireSound
import LvmQAsmHarTop
import LvmQShapeB
import LvmShapeVT

set_option autoImplicit false

namespace Lvm.Q1

open Lvm DM Lvm.VEq Lvm.VEq.Wr Lvm.Loop Lvm.Loop.Build Lvm.Har

/-- `ringSwitchC` on a view. -/
theorem ringSwitchC_runW (sig : ByteArray) (sv : List FE) (st : RS) :
    Lvm.Shape.ringSwitchC sv sig st =
      ((polyEval (sv.map (phiMap · (sampAt (feAt sig) (st.ent + st.msg) ringStages))) gen,
        ringCoefficients (sampAt (feAt sig) (st.ent + st.msg) ringStages)),
        ⟨st.ent + st.msg + 72 * ringStages, 0, st.ok⟩) := by
  rw [show Lvm.Shape.ringSwitchC sv = (samples ringStages >>= fun challenges =>
    pure (polyEval (sv.map (phiMap · challenges)) gen, ringCoefficients challenges)) from rfl,
    bind_run, show ringStages = 5 + 1 from rfl, gk_samples_run sig 5 st _ rfl, pure_run]

/-- **`dWireC`'s coefficients** are read at the wire's challenge lanes. -/
theorem dWireC_snd {P qw : Nat} (hq : 5 ≤ qw) (pp : Params) (hlog : pp.logN = P + 5) (pub : Pub)
    (claim : KeccakClaim) (sig : ByteArray) (s : RS) (hs : s.ent + s.msg = 8 * qw - 40) :
    (Lvm.Shape.dWireC pp pub claim sig s).1.2 = ringCoefficients (chsAt sig (qw + 15 * (P + 5) + 225)) := by
  have hst1 : scState 3 s (List.replicate (P + 5) none) = ⟨8 * qw - 40 + (P + 5) * roundLen 3, 0, s.ok⟩ := by
    rw [show P + 5 = (P + 4) + 1 from rfl, List.replicate_succ]
    show (⟨s.ent + s.msg + _, 0, s.ok⟩ : RS) = _
    rw [hs, List.length_cons, List.length_replicate]
  have hrl : roundLen 3 = 120 := rfl
  unfold Lvm.Shape.dWireC
  rw [hlog, bind_run, sumcheck_run sig 3 (by norm_num), hs, hst1, bind_run, readEs_run, bind_run, require_run,
    bind_run, sumcheck_run sig 3 (by norm_num), bind_run, readEs_run, bind_run, require_run, bind_run,
    ringSwitchC_runW, pure_run]
  simp only [scState, List.length_cons, List.length_nil, hrl]
  have hp1 : 8 * qw - 40 + (P + 5) * 120 + (0 + 24 * 1) = 8 * (qw + 15 * (P + 5) + 3) - 40 := by omega
  have hpr : 8 * (qw + 15 * (P + 5) + 3) - 40 + (0 + 1 + 1) * 120 + (0 + 24 * kBits) =
      8 * (qw + 15 * (P + 5) + 225) - 40 := by simp only [kBits]; omega
  rw [hp1, hpr, sampAt_chs sig (by omega)]

end Lvm.Q1

namespace Lvm.Har

open Lvm DM

/-- `wirePh` is `wirePhC`'s first component. -/
theorem wirePh_runC (pp : Params) (pub : Pub) (claim : KeccakClaim) (sig : ByteArray) (s : RS) :
    wirePh pp pub claim sig s = ((wirePhC pp pub claim sig s).1.1, (wirePhC pp pub claim sig s).2) := by
  have br : ∀ {α β : Type} (m : DM α) (f : α → DM β) (sig : ByteArray) (s : RS),
      (m >>= f) sig s = f (m sig s).1 sig (m sig s).2 := fun _ _ _ _ => rfl
  have pr : ∀ {α : Type} (a : α) (sig : ByteArray) (s : RS), (pure a : DM α) sig s = (a, s) := fun _ _ _ => rfl
  unfold wirePh wirePhC
  rw [Lvm.Shape.dWire_eqC, br, br, br, pr]

/-- **The wire phase with its coefficients** (`wirePhC`) from `wirePh`'s phase fact: the coefficients are read
at the wire's challenge lanes. -/
theorem wireC_phase {pp : Params} {pub : Pub} {claim : KeccakClaim} {sig : ByteArray} {P5 P6 : Nat} {wo : WireOut}
    {P qw : Nat} (hW : PhaseAt (wirePh pp pub claim) sig P5 P6 wo) (hq : 5 ≤ qw) (hlog : pp.logN = P + 5)
    (hn1 : 1 ≤ pub.n) (hnN : pub.n ≤ 2 ^ pp.logN) (hP5 : 8 * qw - 40 = P5) :
    PhaseAt (wirePhC pp pub claim) sig P5 P6 (wo, ringCoefficients (chsAt sig (qw + 15 * (P + 5) + 225))) := by
  intro s hs hok
  have hw := hW s hs hok
  rw [wirePh_runC] at hw
  have br : ∀ {α β : Type} (m : DM α) (f : α → DM β) (sig : ByteArray) (s : RS),
      (m >>= f) sig s = f (m sig s).1 sig (m sig s).2 := fun _ _ _ _ => rfl
  have hc : (wirePhC pp pub claim sig s).1.2 = ringCoefficients (chsAt sig (qw + 15 * (P + 5) + 225)) := by
    unfold wirePhC
    rw [br, Lvm.Q1.dRange_run pp pub sig s hn1 hnN]
    dsimp only
    exact Lvm.Q1.dWireC_snd hq pp hlog pub claim sig s (by simp only [pos] at hs; omega)
  generalize wirePhC pp pub claim sig s = X at hw hc ⊢
  obtain ⟨⟨a, b⟩, st⟩ := X
  obtain ⟨h1, h2, h3⟩ := hw
  exact ⟨by rw [show a = wo from h1, show b = _ from hc], h2, h3⟩

end Lvm.Har

namespace Lvm.QShape

open Lvm Lvm.Shape Lvm.Har

theorem zF_sel (l : ℕ) (hl : l < 4) :
    zF ((selectorPoint l 2).getD 0 0) ((selectorPoint l 2).getD 1 0) = zStarF l := by
  have h4 : (4 : FE) = 0 := by
    rw [show (4 : FE) = 2 * 2 by norm_num, CharTwo.two_eq_zero, zero_mul]
  rw [zF_eq]
  interval_cases l <;>
    simp [selectorPoint, List.range_succ, Har.eOfNat_zero, Har.eOfNat_one, CharTwo.add_self_eq_zero] <;> ring_nf <;>
      simp [CharTwo.two_eq_zero, h4]

/-- **`D`'s point claims**: the cells' tail is `V_S`'s `tailDF`. -/
theorem tailD_pt (r : List FE) (hr : r.length = 20) (l : ℕ) (hl : l < 4) :
    tailD (r ++ selectorPoint l 2) = tailDF r l := by
  have g : ∀ i < 20, (r ++ selectorPoint l 2).getD i 0 = r.getD i 0 := fun i hi ↦ getD_append_lo (by omega)
  have g2 : ∀ j < 2, (r ++ selectorPoint l 2).getD (20 + j) 0 = (selectorPoint l 2).getD j 0 := fun j _ ↦ by
    rw [show 20 + j = r.length + j by omega, getD_append_hi]
  rw [tailD, kappaD, g 18 (by norm_num), g 19 (by norm_num), show 20 = 20 + 0 from rfl, g2 0 (by norm_num),
    show 21 = 20 + 1 from rfl, g2 1 (by norm_num), zF_sel l hl, tailDF, CharTwo.sub_eq_add, CharTwo.sub_eq_add,
    CharTwo.sub_eq_add]

/-- **`D`'s boundary claims** (`m < 2^18`): no tail. -/
theorem tailD_bnd (m : ℕ) (hm : m < 2 ^ 18) (l : ℕ) :
    tailD (selectorPoint m 20 ++ selectorPoint l 2) = 0 := by
  have g : ∀ i < 20, (selectorPoint m 20 ++ selectorPoint l 2).getD i 0 = eOfNat ((m >>> i) % 2) := fun i hi ↦ by
    rw [getD_append_lo (by rw [selectorPoint_length']; omega), selectorPoint_getD' hi]
  rw [tailD, kappaD, g 18 (by norm_num), g 19 (by norm_num), Nat.shiftRight_eq_div_pow, Nat.shiftRight_eq_div_pow,
    show m / 2 ^ 18 % 2 = 0 by omega, show m / 2 ^ 19 % 2 = 0 by omega]
  simp [Har.eOfNat_zero, CharTwo.add_self_eq_zero]

/-- **The tape's ring claim** (`pt` zero above `D`: its `ν − 22` block bits): the cells' tail is `V_S`'s
`ringTailN`. -/
theorem tailR_eq (pt cs : List FE) (hpt : pt.length = CMain.nu20)
    (h0 : pt.drop 22 = List.replicate (CMain.nu20 - 22) 0) :
    tailR pt cs = ringTailN pt cs := by
  rw [ringTailN_eq', ringTailF_sum, tailR]
  refine Finset.sum_congr rfl fun k _ ↦ ?_
  congr 1
  have hpow : ∀ i, (0 : FE) ^ 2 ^ i = 0 := fun i ↦ zero_pow (by positivity)
  have hl : (pt.map (· ^ 2 ^ k)).length = CMain.nu20 := by rw [List.length_map, hpt]
  have hd : (pt.map (· ^ 2 ^ k)).drop 22 = List.replicate (CMain.nu20 - 22) 0 := by
    rw [← List.map_drop, h0, List.map_replicate, hpow]
  have g : ∀ i < CMain.nu20, (pt.map (· ^ 2 ^ k)).getD i 0 = (pt.getD i 0) ^ 2 ^ k := fun i hi ↦ by
    simp [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_eq_getElem (show i < pt.length by omega)]
  rw [tailPtF, hd, kappaD, g 18 (by decide), g 19 (by decide), ← g 20 (by decide), ← g 21 (by decide)]
  have e2 : ((pt.map (· ^ 2 ^ k)).drop 20).take 2 = [(pt.map (· ^ 2 ^ k)).getD 20 0, (pt.map (· ^ 2 ^ k)).getD 21 0] := by
    have hl2 : (((pt.map (· ^ 2 ^ k)).drop 20).take 2).length = 2 := by
      simp only [List.length_take, List.length_drop, hl]; decide
    refine List.ext_getElem (by rw [hl2]; rfl) fun i h1 h2 ↦ ?_
    have hi : i < 2 := by simpa using h2
    interval_cases i <;> simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (show 21 < (pt.map (· ^ 2 ^ k)).length by
      rw [hl]; decide), List.getElem?_eq_getElem (show 20 < (pt.map (· ^ 2 ^ k)).length by rw [hl]; decide)]
  rw [e2, show CMain.nu20 - 22 = 1 from rfl, ← selectorPoint_zero]
  simp [zF, selectorPoint, List.range_succ, eqEval, Har.eOfNat_zero, CharTwo.sub_eq_add]

end Lvm.QShape
