-- New for lvm6 K1: T2 `treeSpec` — the tree batch (`FORMAT6.md` §6.2 rows 1–10) in the doom calculus,
-- assembled from the front (`Lvm6KFront`), the head (`headSpec`) and the input end (`treeEndSpec`).
import Lvm6KFront
import Lvm6KEnd
import Lvm6KBridge

/-!
# `treeSpec`

**`treeSpec (κ) (h5 : 5 ≤ κ) (h29 : κ ≤ 29) : TreeSpecStmt κ`.** The bound `κ ≤ 29` is the wiring point's
group: `ρ ∈ E^(κ−1)` at grind 5 fits `εS` iff `8·(κ−1) ≤ 7·2^5` (`P18` has `κ = 19`).

Steps (`κ = P + 4`, `N = P + 3`): `δ` (moves); `ρ` (`gPointSpec`, alive `AliveR`, from `TreeOkG ∧ R` by
`treeOkG_of_aliveR`); `D^b` (moves); `u` (`doomE2SampleSpec`, `aliveU_escape`); `o₄ … o₂₄` (moves);
`headSpec` at slots `8 + ℓ` on the inputs `Itree`; `treeEndSpec`; the claims `treeCols` from `WireOk`,
`RootOk` (`stepMle_boolpt`) and the middle word claim.
-/

set_option autoImplicit false

namespace Lvm6.K

open LeanVM.Parameters LeanVM.Semantics LeanVM.Protocol.Compile LeanVM.Protocol.Verifier
open LeanVM.Protocol.EndToEnd.Front
open LeanVM.Protocol.KeccakGkr (Shape statesOfS laneWord segStateS roundsFrom)
open Lvm.E2V Lvm6.KPack
open Lvm.ASM (εS)
open RecursionFast
open Finset
open scoped ENNReal

variable {β : Type} {C : List Ev → Set β} [Finite β]

/-- `n + 1` `K` words keep doom; lead `0`. -/
noncomputable def kReadsSpec (hst : Stable C) (A : β → Prop) {T : ℝ≥0∞} (hT : T ≤ εS) :
    (n : ℕ) → Spec (kReads (n + 1)) (Doomed C A) (fun xs h ↦ xs.length = n + 1 ∧ Doomed C A h) εS 0 T
  | 0 => (doomRead hst A hT).bind' fun x ↦
      (Spec.ret (Post := fun xs h ↦ xs = [] ∧ Doomed C A h) []).mono
        (fun _ hd ↦ ⟨rfl, hd⟩) (fun _ _ h ↦ h) le_rfl le_rfl le_rfl |>.bind' fun xs ↦
          (Spec.ret (x.limb 0 :: xs)).mono (fun _ h ↦ ⟨by simp [h.1], h.2⟩) (fun _ _ h ↦ h) le_rfl
            le_rfl le_rfl
  | n + 1 => (doomRead (T := 0) hst A zero_le).bind' fun x ↦
      ((kReadsSpec hst A hT n).mono (fun _ h ↦ h) (fun _ _ h ↦ h) le_rfl zero_le le_rfl).bind'
        fun xs ↦ (Spec.ret (x.limb 0 :: xs)).mono (fun _ h ↦ ⟨by simp [h.1], h.2⟩)
          (fun _ _ h ↦ h) le_rfl le_rfl le_rfl

/-- The wiring point's group fits `εS` for `κ ≤ 29`. -/
theorem grp_rho {c : ℕ} (hc : c ≤ 28) : grpEps 1 c 5 ≤ epsS := by
  unfold grpEps epsS
  have : (c : ℚ) ≤ 28 := by exact_mod_cast hc
  calc (1 : ℚ) * c / 2 ^ (128 + 5) ≤ 1 * 28 / 2 ^ (128 + 5) := by gcongr
    _ ≤ 7 / 2 ^ 131 := by norm_num

/-- `treeProg (P + 4)` with the arithmetic done. -/
def treeProgFlat (P : ℕ) : VerifierProgram TreeOut :=
  kReads (3 + 1) >>= fun δ ↦
  gPoint gRho (P + 2) >>= fun ρ ↦
  e2Reads (7 + 1) >>= fun dd ↦
  e2Sample gU >>= fun u ↦
  e2Reads (20 + 1) >>= fun o' ↦
  kHead6 P 8 (u :: ρ) (oLow u dd ++ o') >>= fun hd ↦
  treeEnd6 P hd.claim >>= fun en ↦
  pure ⟨δ, ρ, dd, u, oLow u dd ++ o', hd, en⟩

theorem treeProg_flat (P : ℕ) : treeProg (P + 4) = treeProgFlat P := rfl

theorem outW_segState {κ : ℕ} (Q : Stack) (x l : ℕ) :
    laneWord (segStateS Shape.v1 (Itree κ Q) 1 12 x) l = outW κ Q x l := by
  simp [segStateS, Itree, outW, Shape.v1]
  rfl

theorem oLow_append_getD (u : E2) (dd o' : List E2) {m : ℕ} (hm : m < 4) :
    (oLow u dd ++ o').getD m 0 = (oLow u dd).getD m 0 := by
  rw [List.getD_append _ _ _ _ (by simp [oLow, hm])]

theorem treeCols_inv {P : ℕ} {Q : Stack} {h : Digest} {out : TreeOut}
    (hc : ∀ c ∈ treeCols (P + 4) h out, ColTrue (P + 4 + 6) Q c) :
    WireOk (P + 3 + 1) Q out.δ out.ρ out.dd ∧ RootOk (P + 3 + 1) Q h ∧
      stepMleK (P + 4 + 6) ((out.u :: out.ρ) ++ out.hd.ϱm) Q = out.hd.cout := by
  have hL : ∀ m < 4, stepMleK (P + 4 + 6) (out.ρ ++ [0] ++ bitsF m 6) Q =
      out.dd.getD m 0 + eqAtF out.ρ 0 * kF (out.δ.getD m 0) := fun m hm ↦
    (hc (out.ρ ++ [0] ++ bitsF m 6, out.dd.getD m 0 + eqAtF out.ρ 0 * kF (out.δ.getD m 0))
      (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _
        (List.mem_map.2 ⟨m, List.mem_range.2 hm, rfl⟩))))).2
  have hR : ∀ m < 4, stepMleK (P + 4 + 6) (out.ρ ++ [0] ++ bitsF (4 + m) 6) Q = out.dd.getD (4 + m) 0 :=
    fun m hm ↦ (hc (out.ρ ++ [0] ++ bitsF (4 + m) 6, out.dd.getD (4 + m) 0)
      (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_right _
        (List.mem_map.2 ⟨m, List.mem_range.2 hm, rfl⟩))))).2
  have hB : ∀ m < 4, stepMleK (P + 4 + 6) (bitsF 0 (P + 4) ++ bitsF (4 + m) 6) Q =
      kF (K.ofLane (dLane h m)) := fun m hm ↦
    (hc (bitsF 0 (P + 4) ++ bitsF (4 + m) 6, kF (K.ofLane (dLane h m)))
      (List.mem_append_left _ (List.mem_append_right _
        (List.mem_map.2 ⟨m, List.mem_range.2 hm, rfl⟩)))).2
  have hM : stepMleK (P + 4 + 6) ((out.u :: out.ρ) ++ out.hd.ϱm) Q = out.hd.cout :=
    (hc ((out.u :: out.ρ) ++ out.hd.ϱm, out.hd.cout)
      (List.mem_append_right _ (List.mem_singleton_self _))).2
  refine ⟨⟨hL, hR⟩, fun m hm ↦ ?_, hM⟩
  have := hB m hm
  rw [stepMle_boolpt Q (Nat.two_pow_pos _) (by omega), zero_add] at this
  exact kF_inj this

open Classical in
/-- **T2 at `2^(P+4)` rows.** -/
noncomputable def treeSpecW (hst : Stable C) (hcard : ∀ hh, (C hh).ncard ≤ 1) (stk : β → Stack)
    (h : Digest) (R : β → Prop) {T : ℝ≥0∞} (hT : T ≤ εS) (P : ℕ) (hP : 1 ≤ P) (h28 : P + 3 ≤ 28) :
    Spec (treeProg (P + 4)) (Doomed C (fun q ↦ TreeOkG (P + 4) (stk q) h ∧ R q))
      (fun out hist ↦ TreeShape (P + 4) out ∧
        Doomed C (fun q ↦ TreeClaims (P + 4) (stk q) h out ∧ R q) hist) εS 0 T :=
  Spec.congr (treeProg_flat P).symm <|
  ((kReadsSpec (T := 0) hst (fun q ↦ TreeOkG (P + 4) (stk q) h ∧ R q) zero_le 3).mono
    (fun _ h' ↦ h') (fun _ _ h' ↦ h') le_rfl le_rfl le_rfl).bind' fun δ ↦
  if hδ : δ.length = 3 + 1 then
  ((gPointSpec (T := 0) hst hcard (g := gRho) (by norm_num) (P + 2)
      (AliveR (P + 3 + 1) stk h R δ) (errG 0 1)
      (fun acc q hq ↦ aliveR_escape (N := P + 3) stk h R δ acc q hq)
      εS_lt_one (grp_le (grp_rho h28))).mono
    (fun _ hd ↦ Doomed.mono hd.2 fun q ha ↦ treeOkG_of_aliveR ha)
    (fun _ _ h' ↦ h') le_rfl le_rfl le_rfl).bind' fun ρ ↦
  if hρ : ρ.length = P + 3 then
  ((e2ReadsSpec (T := 0) hst (fun q ↦ AliveR (P + 3 + 1) stk h R δ ρ q) zero_le 7).mono
    (fun _ hd ↦ hd.2) (fun _ _ h' ↦ h') le_rfl le_rfl le_rfl).bind' fun dd ↦
  if hdd : dd.length = 7 + 1 then
  ((doomE2SampleSpec (T := 0) hst hcard (g := gU) (fun q ↦ AliveR (P + 3 + 1) stk h R δ ρ q)
      (fun u q ↦ AliveU (P + 3 + 1) stk h R δ ρ dd u q) (errG gU 1)
      (fun q hq ↦ aliveU_escape (N := P + 3) (by norm_num) stk h R δ hρ dd q hq) errG_c1).mono
    (fun _ hd ↦ hd.2) (fun _ _ h' ↦ h') le_rfl le_rfl le_rfl).bind' fun u ↦
  ((e2ReadsSpec (T := 0) hst (fun q ↦ AliveU (P + 3 + 1) stk h R δ ρ dd u q) zero_le 20).mono
    (fun _ h' ↦ h') (fun _ _ h' ↦ h') le_rfl le_rfl le_rfl).bind' fun o' ↦
  if ho' : o'.length = 20 + 1 then
  let R' : β → Prop := fun q ↦ WireOk (P + 3 + 1) (stk q) δ ρ dd ∧ RootOk (P + 3 + 1) (stk q) h ∧ R q
  ((headSpec (T := 0) hst hcard R' (fun q ↦ Itree (P + 4) (stk q)) stk P 8 (by norm_num)
      (fun q x l hl ↦ laneWord_Itree_one _ _ _ hl) (inst := u :: ρ) (output := oLow u dd ++ o')
      (by simp [hρ]) (by simp [oLow, ho']) zero_le).mono
    (fun _ hd ↦ Doomed.mono hd.2 fun q ⟨hout, hmid, hW, hroot, hR⟩ ↦
      ⟨hW, hroot, fun m hm ↦ by
        have := hout m (by omega)
        rw [oLow_append_getD u dd o' hm] at this
        simpa only [outW_segState] using this, hmid, hR⟩)
    (fun _ _ h' ↦ h') le_rfl le_rfl le_rfl).bind' fun hd ↦
  if hhd : hd.sl.length = 6 ∧ ClaimShapeF P hd.claim ∧ hd.ϱm.length = 6 then
  ((treeEndSpec hst hcard
      (fun q ↦ stepMleK (P + 4 + 6) ((u :: ρ) ++ hd.ϱm) (stk q) = hd.cout ∧ R' q)
      stk P hP hd.claim hhd.2.1 hT).mono
    (fun _ hd' ↦ Doomed.mono hd'.2.2.2 fun q ⟨hct, hmw, hR'⟩ ↦ ⟨hct, hmw, hR'⟩)
    (fun _ _ h' ↦ h') le_rfl le_rfl le_rfl).bind' fun en ↦
  (Spec.ret (Post := fun out hist ↦ TreeShape (P + 4) out ∧
      Doomed C (fun q ↦ TreeClaims (P + 4) (stk q) h out ∧ R q) hist)
    (⟨δ, ρ, dd, u, oLow u dd ++ o', hd, en⟩ : TreeOut)).mono
    (fun _ hd' ↦ ⟨⟨hδ, by simp [hρ], hdd, by simp [oLow, ho'], hhd.1, hhd.2.1, hhd.2.2, hd'.1,
        hd'.2.1, hd'.2.2.1⟩,
      Doomed.mono hd'.2.2.2 fun q ⟨⟨hcols, hsl⟩, hR⟩ ↦ by
        obtain ⟨hW, hroot, hmw⟩ := treeCols_inv (out := ⟨δ, ρ, dd, u, oLow u dd ++ o', hd, en⟩) hcols
        exact ⟨hsl, hmw, hW, hroot, hR⟩⟩)
    (fun _ _ h' ↦ h') le_rfl le_rfl le_rfl
  else Spec.dead.mono (fun _ hd' ↦ hhd ⟨hd'.1, hd'.2.1, hd'.2.2.1⟩) (fun _ _ h' ↦ h') le_rfl le_rfl le_rfl
  else Spec.dead.mono (fun _ hd' ↦ ho' hd'.1) (fun _ _ h' ↦ h') le_rfl le_rfl le_rfl
  else Spec.dead.mono (fun _ hd' ↦ hdd hd'.1) (fun _ _ h' ↦ h') le_rfl le_rfl le_rfl
  else Spec.dead.mono (fun _ hd' ↦ hρ hd'.1) (fun _ _ h' ↦ h') le_rfl le_rfl le_rfl
  else Spec.dead.mono (fun _ hd' ↦ hδ hd'.1) (fun _ _ h' ↦ h') le_rfl le_rfl le_rfl

/-- **T2, `treeSpec`**: the tree batch for `5 ≤ κ ≤ 29` (`P18`: `κ = 19`). -/
theorem treeSpec (κ : ℕ) (h5 : 5 ≤ κ) (h29 : κ ≤ 29) : TreeSpecStmt κ := by
  intro β _ C hst hcard stk h R T hT
  obtain ⟨P, rfl⟩ : ∃ P, κ = P + 4 := ⟨κ - 4, by omega⟩
  exact ⟨treeSpecW hst hcard stk h R hT P (by omega) (by omega)⟩

/-! ## In WP S's form (`Stmt.treeSpec`) -/

/-- The tree phase in WP S's form for the shapes `treeSpec` covers (`M = logN + 7`,
`4 ≤ logN ≤ 28`; `P18`: `logN = 18`). Versioned addition to `treeProgS` (whose bridge assumes
`treeSpec` at every `κ`; the wiring group fits `εS` only for `κ ≤ 29`). -/
def treeProgS29 (sh : Lvm6.Shape) (x : Lvm6.Hdr) : VerifierProgram Lvm6.TreeOut :=
  if sh.M = sh.logN + 7 ∧ 4 ≤ sh.logN ∧ sh.logN ≤ 28 then
    treeProg (sh.logN + 1) >>= fun out ↦ pure (toS (sh.logN + 1) x.h out)
  else VerifierProgram.fail

/-- **T2 in WP S's form**: `Stmt.treeSpec treeProgS29`. -/
theorem treeSpecS : Stmt.treeSpec treeProgS29 := by
  intro sh x
  by_cases hs : sh.M = sh.logN + 7 ∧ 4 ≤ sh.logN ∧ sh.logN ≤ 28
  · simp only [treeProgS29, if_pos hs]
    have hμ : sh.M = sh.logN + 1 + 6 := by omega
    refine doomSpec_of fun {β} _ C hst hcard stk R ↦ ?_
    obtain ⟨S⟩ := treeSpec (sh.logN + 1) (by omega) (by omega) C hst hcard stk x.h R 0 zero_le
    refine ⟨(S.mono (fun _ hd ↦ Doomed.mono hd fun q ⟨hq, hR⟩ ↦
      ⟨treeOkG_treeOkAt sh.logN (stk q) x.h hq, hR⟩) (fun _ _ h ↦ h) le_rfl le_rfl le_rfl).bind'
        fun out ↦ (Spec.ret (Post := fun o hist ↦
          Doomed C (fun q ↦ o.Holds sh.M (stk q) ∧ R q) hist) (toS (sh.logN + 1) x.h out)).mono
      (fun _ hd ↦ Doomed.mono hd.2 fun q ⟨hh, hR⟩ ↦
        ⟨treeClaims_of_holds (by omega) hd.1 x.h (stk q) (hμ ▸ hh), hR⟩)
      (fun _ _ h ↦ h) le_rfl le_rfl le_rfl⟩
  · simp only [treeProgS29, if_neg hs]
    intro C R G _ _
    exact ⟨Spec.fail⟩

end Lvm6.K
