-- New for lvm6 (WP CD). The child's `S_flat` relayout in the node circuit (`relay6`, CD-3): with
-- CD's `STREAM` layout (identity on slot 33, stride 1) the kernel factors into a selector and one
-- `eq` product, so the circuit needs no carry automaton (season 1's `relayKernG`).
import Lvm6QDTy
import Lvm6TySpecP
import LvmE2VKS
import LvmE2VWireAlg

/-!
# The relayout (generator and HAR)

* **`relayKern_eq`**: for an instance with `Ti.Ok` and `StreamRegs6 Ti` (one `S_flat` region of
  `2^19` words at `bs`, `sflatW (bs + p) = p`), `relayKernE Ti r_y r = eq(r_y^{≥19}, bs / 2^19) ·
  Π_{i<19} (1 + r_{y,i} + r_i)`.
* **`relay6 Ti ry vS a gate`**: CB's `sc2` (19 plain rounds from `v_S`), `v_R` at `a + 266`, the
  selector (`g2Sel`, 2 coordinates), the product (`g2EqEval`), the gated check
  `final = kern·v_R`. **`relay6_har : RelayHarStmt relay6`**.
-/

set_option autoImplicit false

namespace Lvm6.QD

open LeanVM.Parameters LeanVM.Protocol LeanVM.Protocol.Compile LeanVM.Protocol.Verifier
open Lvm Lvm.Loop Lvm.Loop.Build Lvm.Q2 Lvm.Har Lvm.E2V Lvm.Typed Finset
open Lvm6 (Item rep rnd)
open Lvm6.QK
open Lvm6.Ty (TInst6 relayProgE relayKernE regSumW regSumT relayRounds gWire)

/-! ## Region sums over a filtered list -/

theorem regSumW_filter {α : Type} [AddCommMonoid α] (Ti : TInst6) (S : YSrc → Bool) (f : ℕ → α) :
    regSumW Ti S f = ((Ti.lay.yregs.filter fun r ↦ S r.src).map fun reg ↦
      ((List.range (2 ^ reg.log)).map fun i ↦ f (reg.base + i)).sum).sum := by
  unfold regSumW
  induction Ti.lay.yregs with
  | nil => rfl
  | cons r l ih =>
    by_cases h : S r.src = true
    · simp [List.filter_cons, h, ih]
    · simp [List.filter_cons, h, ih]

theorem yregsSorted_aligned : ∀ (l : List YReg), yregsSorted l = true → ∀ r ∈ l, r.base % 2 ^ r.log = 0
  | [], _, r, hr => by simp at hr
  | [x], h, r, hr => by
    simp only [yregsSorted, decide_eq_true_eq] at h
    simp only [List.mem_singleton] at hr
    exact hr ▸ h.1
  | x :: y :: l, h, r, hr => by
    simp only [yregsSorted, Bool.and_eq_true, decide_eq_true_eq] at h
    rcases List.mem_cons.mp hr with rfl | hr
    · exact h.1.1
    · exact yregsSorted_aligned (y :: l) h.2 r hr

theorem ok_aligned {Ti : TInst6} (hok : Ti.Ok) : ∀ r ∈ Ti.lay.yregs, r.base % 2 ^ r.log = 0 := by
  have h := hok.1
  simp only [Lay.Ok, Lay.okB, Bool.and_eq_true] at h
  exact yregsSorted_aligned _ (by tauto)

theorem find?_of_filter {α : Type} (p : α → Bool) : ∀ (l : List α) (x : α) (t : List α),
    l.filter p = x :: t → l.find? p = some x
  | [], _, _, h => by simp at h
  | y :: l, x, t, h => by
    by_cases hy : p y = true
    · simp only [List.filter_cons, hy, if_true, List.cons.injEq] at h
      obtain ⟨rfl, -⟩ := h
      simp [List.find?_cons, hy]
    · simp only [List.filter_cons, hy] at h
      simp only [List.find?_cons, hy]
      exact find?_of_filter p l x t (by simpa using h)

/-- The base of the (first) `S_flat` region. -/
def sflatBase (Ti : TInst6) : ℕ := ((Ti.lay.yregs.find? fun r ↦ r.src == .sflat).map (·.base)).getD 0

/-! ## The kernel factors -/

/-- **The relayout kernel under CD's layout.** -/
theorem relayKern_eq {Ti : TInst6} (hok : Ti.Ok) (hS : StreamRegs6 Ti) (ry r : List E2)
    (hry : ry.length = yVars) (hr : r.length = relayRounds) :
    relayKernE Ti ry r =
      E2V.eqAtF (ry.drop relayRounds) (sflatBase Ti / 2 ^ relayRounds) * eqEvalF (ry.take relayRounds) r := by
  obtain ⟨bs, bg, hf, -, hw, -⟩ := hS
  have hbase : sflatBase Ti = bs := by
    rw [sflatBase, find?_of_filter _ _ _ _ hf]; rfl
  have hmem : (⟨bs, relayRounds, .sflat⟩ : YReg) ∈ Ti.lay.yregs := by
    have : (⟨bs, relayRounds, .sflat⟩ : YReg) ∈ Ti.lay.yregs.filter (fun r ↦ r.src == .sflat) := by
      rw [hf]; exact List.mem_singleton_self _
    exact (List.mem_filter.mp this).1
  have hal : bs % 2 ^ relayRounds = 0 := ok_aligned hok _ hmem
  have htl : (ry.take relayRounds).length = relayRounds := by simp [hry, relayRounds, yVars]
  unfold relayKernE regSumT
  rw [regSumW_filter, hf, hbase]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero]
  rw [lsum_range]
  have key : ∀ i ∈ range (2 ^ relayRounds), E2V.eqAtF ry (bs + i) * E2V.eqAtF r (Ti.sflatW (bs + i)) =
      E2V.eqAtF (ry.drop relayRounds) (bs / 2 ^ relayRounds) * (E2V.eqAtF (ry.take relayRounds) i * E2V.eqAtF r i) := by
    intro i hi
    have hi' : i < 2 ^ relayRounds := Finset.mem_range.mp hi
    rw [hw i hi']
    conv_lhs => rw [← List.take_append_drop relayRounds ry]
    rw [eqAtF_append, htl, eqAtF_mod (ry.take relayRounds), htl]
    have h1 : (bs + i) % 2 ^ relayRounds = i := by
      rw [Nat.add_mod, hal, zero_add, Nat.mod_mod, Nat.mod_eq_of_lt hi']
    have h2 : (bs + i) / 2 ^ relayRounds = bs / 2 ^ relayRounds := by
      obtain ⟨k, hk⟩ := Nat.dvd_of_mod_eq_zero hal
      rw [hk, Nat.mul_add_div (by positivity), Nat.div_eq_of_lt hi', add_zero, Nat.mul_div_cancel_left _ (by positivity)]
    rw [h1, h2]; ring
  rw [Finset.sum_congr rfl key, ← Finset.mul_sum]
  rw [← sum_eqAtF_mul_eqAtF (ry.take relayRounds) r (by rw [htl, hr]), htl]

/-! ## Gadgets -/

/-- `eq(pt, w)` for a constant `w`: per coordinate `r` or `1 + r`. -/
def g2Sel (z o : C2) : List C2 → ℕ → BM C2
  | [], _ => pure o
  | r :: rs, w => g2Sel z o rs (w / 2) >>= fun acc ↦
      if w % 2 = 1 then g2Mul acc r z else g2One r >>= fun r1 ↦ g2Mul acc r1 z

theorem hs_g2Sel {c : Ctx} {M : Mem} {z o : C2} (hz : z.val M = 0) (ho : o.val M = 1) :
    ∀ (rs : List C2) (w : ℕ), Hs c M (g2Sel z o rs w) (fun s ↦ ev2 M s = E2V.eqAtF (rs.map (ev2 M)) w)
  | [], w => hs_pure (by simp [ev2, ho])
  | r :: rs, w => by
    refine hs_bind (hs_g2Sel hz ho rs (w / 2)) fun acc hacc ↦ ?_
    by_cases hw : w % 2 = 1
    · simp only [hw, if_true]
      exact hs_mono (hs_g2Mul _ _ _) fun s hs ↦ by
        rw [ev2_mul hs, hacc, ev2_of_zero hz, List.map_cons, E2V.eqAtF]; simp [hw, mul_comm]
    · simp only [hw, if_false]
      exact hs_bind (hs_g2One r) fun r1 hr1 ↦ hs_mono (hs_g2Mul _ _ _) fun s hs ↦ by
        rw [ev2_mul hs, hacc, ev2_of_zero hz, List.map_cons, E2V.eqAtF]
        simp only [hw, if_false, add_zero]
        rw [mul_comm]; congr 1; simp [ev2, hr1]

theorem toE2_eqEvalF : ∀ (x y : List FE2), x.length = y.length →
    FE2.toE2 (eqEvalF x y) = eqEvalF (x.map FE2.toE2) (y.map FE2.toE2)
  | [], [], _ => by simp [eqEvalF]
  | a :: x, b :: y, h => by
    rw [List.map_cons, List.map_cons, eqEvalF_cons, eqEvalF_cons, FE2.fe2_mul_eq,
      toE2_eqEvalF x y (by simpa using h)]
    simp
  | [], _ :: _, h => by simp at h
  | _ :: _, [], h => by simp at h

/-- **The relayout gadget.** -/
def relay6 (Ti : TInst6) (ry : List C2) (vS : C2) (a : ℕ) (gate : Cell) : BM RelayOutC :=
  sc2 relayRounds a vS >>= fun rf ↦ g2Zero (ld2 a) >>= fun z ↦ g2Const 1 (ld2 a) >>= fun o ↦
    g2Sel z o (ry.drop relayRounds) (sflatBase Ti / 2 ^ relayRounds) >>= fun sel ↦
      g2EqEval z sel (ry.take relayRounds) rf.1 >>= fun k ↦
        g2Mul k (ld2 (a + 14 * relayRounds)) z >>= fun m ↦ g2Add rf.2 m >>= fun d ↦
          g2Assert d gate >>= fun _ ↦ pure ⟨rf.1, ld2 (a + 14 * relayRounds)⟩

theorem hs_and {c : Ctx} {M : Mem} {α : Type} {m : BM α} {P Q : α → Prop} (h1 : Hs c M m P)
    (h2 : Hs c M m Q) : Hs c M m fun o ↦ P o ∧ Q o := fun p hp ↦ ⟨h1 p hp, h2 p hp⟩

/-- **CD-3**: `relay6` re-executes the relayout. -/
theorem relay6_har : RelayHarStmt relay6 := by
  intro Ti hok hlay ry hry vS a gate c M hg
  refine hsA_bind (hsA_of_hs (hs_and (sc2_runs (c := c) gWire (by norm_num) relayRounds a vS)
    (hs_sc2 relayRounds a vS))) fun rf hrf2 ↦ ?_
  obtain ⟨hrf, hlen, -⟩ := hrf2
  have hrl : rf.1.length = relayRounds := by rw [hlen]; simp [sc2Ans]
  refine hsA_bind (hsA_of_hs (hs_g2Zero _)) fun z hz ↦ ?_
  refine hsA_bind (hsA_of_hs (hs_g2Const 1 _)) fun o ho ↦ ?_
  refine hsA_bind (hsA_of_hs (hs_g2Sel hz ho _ _)) fun sel hsel ↦ ?_
  have htl : (ry.take relayRounds).length = rf.1.length := by rw [hrl]; simp [hry, relayRounds, yVars]
  refine hsA_bind (hsA_of_hs (hs_g2EqEval hz sel _ _ htl)) fun k hk ↦ ?_
  refine hsA_bind (hsA_of_hs (hs_g2Mul _ _ _)) fun m hm ↦ ?_
  refine hsA_bind (hsA_of_hs (hs_g2Add _ _)) fun d hd ↦ ?_
  refine hsA_bind (hsA_g2Assert d gate hg) fun _ h0 ↦ hsA_pure ?_
  show Runs M (layItems relayItems a) _ _
  have hfin : ev2 M rf.2 = relayKernE Ti (ry.map (ev2 M)) (rf.1.map (ev2 M)) *
      ev2 M (ld2 (a + 14 * relayRounds)) := by
    rw [ev2_eq_of_add (hd.symm.trans h0), ev2_mul hm, ev2_of_zero hz, add_zero,
      relayKern_eq hok hlay.1 _ _ (by simp [hry]) (by simp [hrl]), ← List.map_drop, ← List.map_take, ← hsel]
    congr 1
    simp only [ev2, hk, FE2.fe2_mul_eq]
    rw [toE2_eqEvalF _ _ (by simpa using htl), List.map_map, List.map_map]; rfl
  have hl : layItems relayItems a = layItems (rep relayRounds (rnd 2 gWire)) a ++
      layItems [.E 1] (a + 14 * relayRounds) := by
    rw [relayItems, layItems_append, layEnd_repR2]
  unfold relayProgE
  refine runs_bind' hl hrf fun res hres ↦ ?_
  refine runs_bind' (l₂ := []) rfl (runs_e2Read M _) fun vR hvR ↦ ?_
  refine runs_bind' (l₁ := []) (l₂ := []) rfl (runs_require ?_) fun _ _ ↦ runs_pure ⟨hres.1, by rw [hvR]; rfl⟩
  rw [hres.1, hres.2, hvR, hfin]; rfl

end Lvm6.QD
