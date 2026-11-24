-- New for lvm6 (WP CB). The middle-state opening of a Keccak batch in the node circuit (FORMAT6 §6.2
-- row 9, §6.3): 6 plain rounds over the slot bits, `c_out`, and the check `midWt·c_out = final`,
-- with its HAR (gated assertion).
import Lvm6QKHead

/-!
# The middle-state opening (generator and HAR)

* **`midProg base rseg rlane cst`**: row 9 of `kHead6` (`base = 8` for the tree, `25` for the
  sponge): `sumcheckE2 gC2 cst 3` over 6 slot bits, `E(1)` = `c_out`, `require (midWt …·c_out =
  final)`.
* **`treeMidG base q cst seg lanes gate`**: the gadget. `sc2 6` from lane `q`, `c_out` at `q + 84`,
  the `eq` table of the slot point (126 products), `Σ_{ℓ<25} eq(ϱ, base+ℓ)·eq(r_lane, ℓ)` from the
  head's lane table (25), then `(1 + r_seg)·Σ·c_out + final` asserted zero under the gate.
* **`treeMid_har`**: with the lane table representing `eqKernelF r_lane`, the gadget re-executes
  `midProg` (its check included) and hands on the slot point and `c_out`.
-/

set_option autoImplicit false

namespace Lvm6.QK

open LeanVM.Parameters LeanVM.Protocol.Compile LeanVM.Protocol.Verifier
open Lvm Lvm.Loop Lvm.Loop.Build Lvm.Q2 Lvm.Har Lvm.E2V Lvm6.K Lvm6.KPack
open Lvm6 (Item rep rnd)
open Finset

variable {c : Ctx} {M : Mem}

/-- **Row 9**: the middle-state opening and its check. -/
def midProg (base : ℕ) (rseg : E2) (rlane : List E2) (cst : E2) : VerifierProgram (List E2 × E2) :=
  sumcheckE2 gC2 cst 3 (List.replicate 6 none) >>= fun om ↦ e2Read >>= fun cout ↦
  VerifierProgram.require (midWt base rseg rlane om.1 * cout = om.2) >>= fun _ ↦ pure (om.1, cout)

/-- Its items. -/
def midItems : List Item := rep 6 (rnd 2 2) ++ [.E 1]

theorem layEnd_rep6 (q : ℕ) : layEnd (rep 6 (rnd 2 2)) q = q + 84 := by
  simp only [rep, rnd, List.replicate, List.flatten, List.append_eq, List.cons_append,
    List.nil_append, List.append_nil, layEnd]

/-- **The middle-state opening gadget.** -/
def treeMidG (base q : ℕ) (cst seg : C2) (lanes : List C2) (gate : Cell) : BM (List C2 × C2) :=
  sc2 6 q cst >>= fun om ↦
  let cout := ld2 (q + 84)
  g2Zero cout >>= fun z ↦ g2One z >>= fun one ↦ g2EqTab z [one] om.1 >>= fun tab ↦
  g2Dot z ((List.range 25).map fun l ↦ (tab.getD (base + l) default, lanes.getD l default)) >>= fun s ↦
  g2One seg >>= fun seg1 ↦ g2Mul seg1 s z >>= fun w ↦ g2Mul w cout om.2 >>= fun e ↦
  g2Assert e gate >>= fun _ ↦ pure (om.1, cout)

theorem hs_and {α : Type} {m : BM α} {P Q : α → Prop} (hP : Hs c M m P) (hQ : Hs c M m Q) :
    Hs c M m fun a ↦ P a ∧ Q a := fun p h ↦ ⟨hP p h, hQ p h⟩

theorem lsum_range' (f : ℕ → E2) (n : ℕ) : ((List.range n).map f).sum = ∑ i ∈ range n, f i := by
  induction n with
  | zero => simp
  | succ n ih => rw [List.range_succ, List.map_append, List.sum_append, ih, sum_range_succ]; simp

theorem ev2_getD {l : List C2} {L : List E2} (h : l.map (ev2 M) = L) {i : ℕ} (hi : i < L.length) :
    ev2 M (l.getD i default) = L.getD i 0 := by
  have hl : i < l.length := by rw [← h, List.length_map] at hi; exact hi
  rw [← h, List.getD_eq_getElem _ _ hl, List.getD_eq_getElem _ _ (by simpa using hl),
    List.getElem_map]

/-- **The middle-state gadget re-executes row 9**, its check included. -/
theorem treeMid_har (base q : ℕ) (hb : base + 25 ≤ 64) (cst seg : C2) (lanes : List C2)
    (rlane : List E2) (hrl : rlane.length = 5) (hlan : lanes.map (ev2 M) = eqKernelF rlane)
    (gate : Cell) (hg : gate.val M = 1) :
    HsA c M (treeMidG base q cst seg lanes gate) fun o ↦
      Runs M (layItems midItems q) (midProg base (ev2 M seg) rlane (ev2 M cst))
        (fun r ↦ r.1 = o.1.map (ev2 M) ∧ r.2 = ev2 M o.2) := by
  unfold treeMidG
  refine hsA_bind (hsA_of_hs (hs_and (sc2_runs (c := c) 2 (by norm_num) 6 q cst) (hs_sc2 6 q cst)))
    fun om hh ↦ ?_
  obtain ⟨hom, homs, -⟩ := hh
  refine hsA_bind (hsA_of_hs (hs_g2Zero _)) fun z hz ↦ hsA_bind (hsA_of_hs (hs_g2One z)) fun one hone ↦
    hsA_bind (hsA_of_hs (hs_g2EqTab hz [one] om.1)) fun tab htab ↦
    hsA_bind (hsA_of_hs (hs_g2Dot _ _)) fun s hs ↦ hsA_bind (hsA_of_hs (hs_g2One seg)) fun seg1 hseg1 ↦
    hsA_bind (hsA_of_hs (hs_g2Mul _ _ _)) fun w hw ↦ hsA_bind (hsA_of_hs (hs_g2Mul _ _ _)) fun e he ↦
    hsA_bind (hsA_g2Assert e gate hg) fun _ hE ↦ hsA_pure ?_
  rw [hz, add_zero] at hone
  have htab' := eqTab_ev2 hone _ htab
  -- the check: `w·c_out = final`
  have hchk : ev2 M w * ev2 M (ld2 (q + 84)) = ev2 M om.2 := by
    have h0 : w.val M * (ld2 (q + 84)).val M = om.2.val M := by
      rw [he] at hE
      linear_combination hE - om.2.val M * CharTwo.two_eq_zero (R := FE2)
    simp only [ev2, ← FE2.fe2_mul_eq, h0]
  have hw' : ev2 M w = (1 + ev2 M seg) * ∑ l ∈ range 25,
      ev2 M (tab.getD (base + l) default) * ev2 M (lanes.getD l default) := by
    rw [ev2_mul hw, show ev2 M z = 0 by simp [ev2, hz], add_zero]
    have h1 : ev2 M seg1 = 1 + ev2 M seg := by simp [ev2, hseg1, FE2.toE2_add, FE2.toE2_one]
    have h2 : ev2 M s = ∑ l ∈ range 25,
        ev2 M (tab.getD (base + l) default) * ev2 M (lanes.getD l default) := by
      rw [ev2, hs, hz, zero_add, ev2_sum, List.map_map, List.map_map, ← lsum_range']
      congr 1
      exact List.map_congr_left fun l _ ↦ by simp [ev2, FE2.fe2_mul_eq]
    rw [h1, h2]
  intro hpw evs hev
  rw [show layItems midItems q = layItems (rep 6 (rnd 2 2)) q ++ (layItems [.E 1] (q + 84) ++ []) by
    rw [midItems, layItems_append, layEnd_rep6, List.append_nil]] at hpw hev
  refine runs_bind (hom) (fun omv homv ↦ runs_bind (runs_e2Read' M (q + 84)) fun cout hcout ↦
    runs_bind' (l₁ := []) (l₂ := []) rfl (runs_require ?_) fun _ _ ↦ runs_pure ⟨homv.1, hcout⟩)
    hpw evs hev
  rw [homv.1, homv.2, hcout, ← hchk, hw', midWt]
  have hlen : (om.1.map (ev2 M)).length = 6 := by
    rw [homs, List.map_map, List.length_map, sc2Ans_length]
  have hsum : ∑ l ∈ range 25, eqAtF (om.1.map (ev2 M)) (base + l) * eqAtF rlane l =
      ∑ l ∈ range 25, ev2 M (tab.getD (base + l) default) * ev2 M (lanes.getD l default) := by
    refine sum_congr rfl fun l hl ↦ ?_
    have hl' : l < 25 := mem_range.mp hl
    rw [ev2_getD htab' (by rw [eqKernelF_length, hlen]; norm_num; omega),
      ev2_getD hlan (by rw [eqKernelF_length, hrl]; norm_num; omega),
      eqKernelF_getD, eqKernelF_getD, if_pos (by rw [hlen]; norm_num; omega),
      if_pos (by rw [hrl]; norm_num; omega)]
  rw [hsum]

end Lvm6.QK
