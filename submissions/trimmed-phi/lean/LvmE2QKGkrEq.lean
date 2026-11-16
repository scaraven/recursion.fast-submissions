-- New for lvm2 E2F (E2F-QH4): the `KS` GKR at `E2` (phase KS): `V`'s `verifyKeccakD (P + 4)` (`LvmDecideE2`) replayed by
-- `gkrGadgetE2` (`LvmE2QKGkr`), the `E2` counterpart of `LvmQEqKeccakGkr`'s `gkr_spec`.
import LvmE2QKTapeEq

/-!
# The `KS` GKR at `E2`

* **`V` side.** `vkSpec2 v va P inst output p`: `V`'s `verifyKeccakD (P + 4)` from the segment challenge's entry `p`
  (the challenges, the committed scalar, the 12 layers as `chain2`, the two openings' sumchecks, the word, the instance
  sumcheck, the slices, the two final checks); **`verifyKeccakD_run`**: the result, the position after, the flag
  `vkOk2 ∧` the flag before (`keccakOpenD_run`, `vkTail_run'`).
* **Circuit blocks.** `preTB2_spec`/`rep_firstK2` (the first claim), `fin1TB2_spec` (slice copies, the `eq` tables, the
  committed check), `rot2_spec` (the rotated sums), `fin2TB2_spec` (the input check), `q2Mle_spec`.
-/

set_option autoImplicit false

namespace Lvm.Q1

open Lvm Lvm.Loop Lvm.Loop.Build Lvm.E2V DM

/-! ## `V`'s `verifyKeccakD` on a view -/

theorem keccakOpenD_run (sig : ByteArray) (ls : Nat) (claim : KClaim FE2) (first count : Nat) (value : FE2) (s : RS) :
    keccakOpenD ls claim first count value sig s =
      (((scSpec2 (fe2At sig) (feAt sig) gC2 3 (s.ent + s.msg) value 6).1,
        foldRowsF (scSpec2 (fe2At sig) (feAt sig) gC2 3 (s.ent + s.msg) value 6).1 (slotWeightsF ls claim first count),
        (scSpec2 (fe2At sig) (feAt sig) gC2 3 (s.ent + s.msg) value 6).2.1),
        ⟨s.ent + s.msg + 6 * 112, 0, (scSpec2 (fe2At sig) (feAt sig) gC2 3 (s.ent + s.msg) value 6).2.2 && s.ok⟩) := by
  show (sumcheckD gC2 value 3 (List.replicate LeanVM.Protocol.Verifier.qkeccakSlotBits none) >>= fun sv =>
    pure (sv.1, foldRowsF sv.1 (slotWeightsF ls claim first count), sv.2)) sig s = _
  rw [qkeccakSlotBits_eqF, rdE_bind_run, sumcheckD_runS' sig gC2 3 (by (clear * -; omega)) 5 value s, rdE_pure_run]
  -- not a closing `rfl`: the kernel decided `scSpec2 … (5 + 1) = scSpec2 … 6` by unfolding the sumcheck (47 M hb)
  rw [show (5 + 1 : Nat) = 6 from rfl, show roundLen2 3 = 112 from rfl]

theorem readE2_run' (sig : ByteArray) (s : RS) :
    readE2 sig s = (fe2At sig (s.ent + s.msg + 40), ⟨s.ent, s.msg + 16, s.ok⟩) := by
  rw [readE2_run, show s.ent + 40 + s.msg = s.ent + s.msg + 40 by (clear * -; omega)]

/-- What `V`'s `verifyKeccakD` reads, as positions from `p`. -/
structure VkOut2 where
  /-- The result (the committed outputs' word claim, the slice point, the slices). -/
  res : List (List FE2 × FE2) × List FE2 × List FE2
  /-- The two final checks. -/
  ok1 : Bool
  ok2 : Bool
  /-- The proof-of-work flags of the openings' and the instance sumcheck's rounds. -/
  pwO : Bool

/-- **`V`'s `verifyKeccakD (P + 4)` on a view** from `p` (the segment challenge's entry). -/
def vkSpec2 (v : Nat → FE2) (va : Nat → FE) (P : Nat) (inst output : List FE2) (p : Nat) : VkOut2 :=
  let seg := sampsG va p 1
  let lanes := sampsG va (p + 80) 5
  let committed := v (p + 520)
  let first := firstClaimSF LeanVM.Protocol.KeccakGkr.Shape.v1 inst seg lanes output committed
  let L := 2440 + 112 * (P + 1)
  let claim := chain2 v va (fun k => iotaSF LeanVM.Protocol.KeccakGkr.Shape.v1 (P + 4) (0 + k)) first (p + 496) L 12
  let p1 := p + 496 + 12 * L
  let sc1 := scSpec2 v va gC2 3 p1 committed 6
  let word := v (p1 + 712)
  let lv := scSpec2 v va gC2 3 (p1 + 688) claim.value 4
  let sc3 := scSpec2 v va gC2 3 (p1 + 1136) lv.2.1 6
  let slices := scalars2 v (p1 + 1848) 64
  ⟨([(inst.take 4 ++ inst.drop 4 ++ sc1.1, word)], lv.1 ++ claim.point.take (P + 4 - 4) ++ sc3.1, slices),
    (foldRowsF sc1.1 (slotWeightsF (P + 4) first 1 1)).headD 0 * word == sc1.2.1,
    multilinearEvalF claim.mu lv.1 * dotF (foldRowsF sc3.1 (slotWeightsF (P + 4) claim 0 2)) slices == sc3.2.1,
    sc1.2.2 && lv.2.2 && sc3.2.2⟩

theorem sampsG_length (va : Nat → FE) : ∀ (n p : Nat), (sampsG va p n).length = n
  | 0, _ => rfl
  | n + 1, p => by rw [sampsG, List.length_cons, sampsG_length va n]

theorem firstClaimSF_v1_point_length {P : Nat} {inst seg lanes out : List FE2} (com : FE2) (hinst : inst.length = P + 4)
    (hseg : seg.length = 1) :
    (firstClaimSF LeanVM.Protocol.KeccakGkr.Shape.v1 inst seg lanes out com).point.length = P + 1 := by
  show (inst.drop 4 ++ seg).length = P + 1
  rw [List.length_append, List.length_drop, hinst, hseg]; (clear * -; omega)

theorem verifyKeccakD_eq (ls : Nat) (inst output : List FE2) :
    verifyKeccakD ls inst output =
      (samplesG gC1 (0 + 1) >>= fun segment => samplesG gC1 (4 + 1) >>= fun lanePoint => readE2 >>= fun committed =>
        keccakLayersD LeanVM.Protocol.KeccakGkr.Shape.v1 ls (List.range' 0 (11 + 1))
          (firstClaimSF LeanVM.Protocol.KeccakGkr.Shape.v1 inst segment lanePoint output committed) >>= fun claim =>
        keccakOpenD ls (firstClaimSF LeanVM.Protocol.KeccakGkr.Shape.v1 inst segment lanePoint output committed) 1
            (2 - 1) committed >>= fun o => readE2 >>= fun word => require (o.2.1.headD 0 * word == o.2.2) >>= fun _ =>
        sumcheckD gC2 claim.value 3 (List.replicate 4 none) >>= fun lv =>
        keccakOpenD ls claim 0 2 lv.2 >>= fun o' => readE2s kBits >>= fun slices =>
        require (multilinearEvalF claim.mu lv.1 * dotF o'.2.1 slices == o'.2.2) >>= fun _ =>
        pure ([(inst.take 4 ++ inst.drop 4 ++ o.1, word)], lv.1 ++ claim.point.take (ls - 4) ++ o'.1, slices)) := by
  unfold verifyKeccakD
  rw [show LeanVM.Protocol.Verifier.keccakSegmentBits = 0 + 1 by decide,
    show LeanVM.Protocol.Verifier.keccakLaneBits = 4 + 1 from rfl,
    show LeanVM.Protocol.Verifier.keccakSegments = 2 by decide, show LeanVM.Protocol.Verifier.keccakDepth = 11 + 1 from rfl,
    List.range_eq_range']
  simp only [Nat.one_lt_two, ite_true, pure_bind]

/-- **The tail on a view** from `p = ent + msg`: committed open at `p`, word at `p + 712`, instance sumcheck at
`p + 688`, input open at `p + 1136`, slices at `p + 1848`. -/
theorem vkTail_run' (sig : ByteArray) (ls : Nat) (inst : List FE2) (first : KClaim FE2) (com : FE2) (claim : KClaim FE2)
    (s : RS) :
    (keccakOpenD ls first 1 (2 - 1) com >>= fun o => readE2 >>= fun word =>
      require (o.2.1.headD 0 * word == o.2.2) >>= fun _ =>
      sumcheckD gC2 claim.value 3 (List.replicate 4 none) >>= fun lv =>
      keccakOpenD ls claim 0 2 lv.2 >>= fun o' => readE2s kBits >>= fun slices =>
      require (multilinearEvalF claim.mu lv.1 * dotF o'.2.1 slices == o'.2.2) >>= fun _ =>
      (pure ([(inst.take 4 ++ inst.drop 4 ++ o.1, word)], lv.1 ++ claim.point.take (ls - 4) ++ o'.1, slices) :
        DM (List (List FE2 × FE2) × List FE2 × List FE2))) sig s =
      (([(inst.take 4 ++ inst.drop 4 ++ (scSpec2 (fe2At sig) (feAt sig) gC2 3 (s.ent + s.msg) com 6).1,
          fe2At sig (s.ent + s.msg + 712))],
        (scSpec2 (fe2At sig) (feAt sig) gC2 3 (s.ent + s.msg + 688) claim.value 4).1 ++ claim.point.take (ls - 4) ++
          (scSpec2 (fe2At sig) (feAt sig) gC2 3 (s.ent + s.msg + 1136)
            (scSpec2 (fe2At sig) (feAt sig) gC2 3 (s.ent + s.msg + 688) claim.value 4).2.1 6).1,
        scalars2 (fe2At sig) (s.ent + s.msg + 1848) 64),
       ⟨s.ent + s.msg + 1808, 1024,
        (multilinearEvalF claim.mu (scSpec2 (fe2At sig) (feAt sig) gC2 3 (s.ent + s.msg + 688) claim.value 4).1 *
            dotF (foldRowsF (scSpec2 (fe2At sig) (feAt sig) gC2 3 (s.ent + s.msg + 1136)
              (scSpec2 (fe2At sig) (feAt sig) gC2 3 (s.ent + s.msg + 688) claim.value 4).2.1 6).1
              (slotWeightsF ls claim 0 2)) (scalars2 (fe2At sig) (s.ent + s.msg + 1848) 64) ==
          (scSpec2 (fe2At sig) (feAt sig) gC2 3 (s.ent + s.msg + 1136)
            (scSpec2 (fe2At sig) (feAt sig) gC2 3 (s.ent + s.msg + 688) claim.value 4).2.1 6).2.1) &&
        ((scSpec2 (fe2At sig) (feAt sig) gC2 3 (s.ent + s.msg + 1136)
            (scSpec2 (fe2At sig) (feAt sig) gC2 3 (s.ent + s.msg + 688) claim.value 4).2.1 6).2.2 &&
        ((scSpec2 (fe2At sig) (feAt sig) gC2 3 (s.ent + s.msg + 688) claim.value 4).2.2 &&
        (((foldRowsF (scSpec2 (fe2At sig) (feAt sig) gC2 3 (s.ent + s.msg) com 6).1 (slotWeightsF ls first 1 1)).headD 0 *
            fe2At sig (s.ent + s.msg + 712) == (scSpec2 (fe2At sig) (feAt sig) gC2 3 (s.ent + s.msg) com 6).2.1) &&
        ((scSpec2 (fe2At sig) (feAt sig) gC2 3 (s.ent + s.msg) com 6).2.2 && s.ok))))⟩) := by
  obtain ⟨e, m, o⟩ := s
  simp only []
  generalize hp : e + m = p
  rw [show List.replicate 4 (none : Option FE2) = List.replicate (3 + 1) none from rfl,
    show (2 - 1 : Nat) = 1 from rfl, show kBits = 64 from rfl]
  simp only [rdE_bind_run, keccakOpenD_run, readE2_run', rdE_require_run, sumcheckD_runS' sig gC2 3 (by (clear * -; omega)),
    readE2s_run, rdE_pure_run, hp]
  have q1 : p + 6 * 112 + 0 + 40 = p + 712 := by (clear * -; omega)
  have q2 : p + 6 * 112 + (0 + 16) = p + 688 := by (clear * -; omega)
  have q3 : p + 688 + (3 + 1) * roundLen2 3 + 0 = p + 1136 := by unfold roundLen2; (clear * -; omega)
  have q4 : p + 1136 + 6 * 112 + 0 + 40 = p + 1848 := by (clear * -; omega)
  have q5 : p + 1136 + 6 * 112 = p + 1808 := by (clear * -; omega)
  have q6 : (0 + 16 * 64 : Nat) = 1024 := by (clear * -; omega)
  have q7 : (3 + 1 : Nat) = 4 := rfl
  simp only [q1, q2, q3, q4, q5, q6, q7]

/-- The part of `verifyKeccakD` after the layers. -/
def vkTail (ls : Nat) (inst : List FE2) (first : KClaim FE2) (com : FE2) (claim : KClaim FE2) :
    DM (List (List FE2 × FE2) × List FE2 × List FE2) :=
  keccakOpenD ls first 1 (2 - 1) com >>= fun o => readE2 >>= fun word =>
    require (o.2.1.headD 0 * word == o.2.2) >>= fun _ =>
    sumcheckD gC2 claim.value 3 (List.replicate 4 none) >>= fun lv =>
    keccakOpenD ls claim 0 2 lv.2 >>= fun o' => readE2s kBits >>= fun slices =>
    require (multilinearEvalF claim.mu lv.1 * dotF o'.2.1 slices == o'.2.2) >>= fun _ =>
    pure ([(inst.take 4 ++ inst.drop 4 ++ o.1, word)], lv.1 ++ claim.point.take (ls - 4) ++ o'.1, slices)

theorem verifyKeccakD_eq2 (ls : Nat) (inst output : List FE2) :
    verifyKeccakD ls inst output =
      (samplesG gC1 (0 + 1) >>= fun segment => samplesG gC1 (4 + 1) >>= fun lanePoint => readE2 >>= fun committed =>
        keccakLayersD LeanVM.Protocol.KeccakGkr.Shape.v1 ls (List.range' 0 (11 + 1))
          (firstClaimSF LeanVM.Protocol.KeccakGkr.Shape.v1 inst segment lanePoint output committed) >>= fun claim =>
        vkTail ls inst (firstClaimSF LeanVM.Protocol.KeccakGkr.Shape.v1 inst segment lanePoint output committed)
          committed claim) := by
  rw [verifyKeccakD_eq]; rfl

theorem bool_vk (c1 c2 s1 lv s3 X ln sg o : Bool) :
    (c2 && (s3 && (lv && (c1 && (s1 && (X && (ln && (sg && o)))))))) =
      ((c1 && c2 && (s1 && lv && s3) && X && ln && sg) && o) := by
  cases c1 <;> cases c2 <;> cases s1 <;> cases lv <;> cases s3 <;> cases X <;> cases ln <;> cases sg <;> cases o <;> rfl

/-- All of `V`'s checks in `verifyKeccakD (P + 4)` from `p`: the two final checks, the openings' and the instance
sumcheck's proof-of-work flags, the 12 layers' checks, the lane and segment challenges' proof-of-work flags. -/
def vkOk2 (v : Nat → FE2) (va : Nat → FE) (P : Nat) (inst output : List FE2) (p : Nat) : Bool :=
  (vkSpec2 v va P inst output p).ok1 && (vkSpec2 v va P inst output p).ok2 && (vkSpec2 v va P inst output p).pwO &&
    chainOk2 v va (fun k => iotaSF LeanVM.Protocol.KeccakGkr.Shape.v1 (P + 4) (0 + k))
      (firstClaimSF LeanVM.Protocol.KeccakGkr.Shape.v1 inst (sampsG va p 1) (sampsG va (p + 80) 5) output (v (p + 520)))
      (p + 496) (2440 + 112 * (P + 1)) 12 &&
    powsG va gC1 (p + 80) 5 && powsG va gC1 p 1

/-- **`V`'s `verifyKeccakD (P + 4)` on a view** from the segment challenge's entry `p = ent + msg`: the result, the
position after, the flag (`vkOk2 ∧` the flag before). -/
theorem verifyKeccakD_run (sig : ByteArray) (P : Nat) (inst output : List FE2) (hinst : inst.length = P + 4)
    (s : RS) :
    (verifyKeccakD (P + 4) inst output sig s).1 = (vkSpec2 (fe2At sig) (feAt sig) P inst output (s.ent + s.msg)).res ∧
    (verifyKeccakD (P + 4) inst output sig s).2.ent + (verifyKeccakD (P + 4) inst output sig s).2.msg =
      s.ent + s.msg + 496 + 12 * (2440 + 112 * (P + 1)) + 2832 ∧
    (verifyKeccakD (P + 4) inst output sig s).2.ok =
      (vkOk2 (fe2At sig) (feAt sig) P inst output (s.ent + s.msg) && s.ok) := by
  obtain ⟨e, m, o⟩ := s
  simp only []
  generalize hp : e + m = p
  rw [verifyKeccakD_eq2]
  simp only [rdE_bind_run, samplesG_run, readE2_run', hp]
  have hfl : (firstClaimSF LeanVM.Protocol.KeccakGkr.Shape.v1 inst (sampsG (feAt sig) p (0 + 1))
      (sampsG (feAt sig) (p + 80 * (0 + 1) + 0) (4 + 1)) output
        (fe2At sig (p + 80 * (0 + 1) + 0 + 80 * (4 + 1) + 0 + 40))).point.length = P + 1 :=
    firstClaimSF_v1_point_length _ hinst (sampsG_length _ _ _)
  simp only [keccakLayersD_run sig _ (P + 4) P 11 0 _ _ hfl]
  -- `rw`, not `simp`, for the tail (simp's projection reductions left the kernel a costly defeq: 1.6 M hb)
  rw [vkTail, vkTail_run']
  have n1 : (0 + 1 : Nat) = 1 := rfl
  have n5 : (4 + 1 : Nat) = 5 := rfl
  have n12 : (11 + 1 : Nat) = 12 := rfl
  have n16 : (0 + 16 : Nat) = 16 := rfl
  have hP4 : P + 4 - 4 = P := by (clear * -; omega)
  have a1 : p + 80 * 1 + 0 = p + 80 := by (clear * -; omega)
  have a2 : p + 80 + 80 * 5 + 0 + 40 = p + 520 := by (clear * -; omega)
  have a3 : p + 80 + 80 * 5 + 16 = p + 496 := by (clear * -; omega)
  have a4 : p + 496 + 12 * (2440 + 112 * (P + 1)) + 0 = p + 496 + 12 * (2440 + 112 * (P + 1)) := Nat.add_zero _
  simp only [n1, n5, n12, n16, hP4, a1, a2, a3, a4, vkOk2, vkSpec2, true_and]
  exact bool_vk _ _ _ _ _ _ _ _ _

/-! ## `KS`'s first claim at `E2` -/

/-- **`KS`'s first claim** is represented by its carried values (`carVT2` with the segment last in the point). -/
theorem rep_firstK2 (P : Nat) {instV lp out fl : List FE2} (s0 com : FE2) (hinst : instV.length = P + 4)
    (hlp : lp.length = 5) (hout : out.length = 25)
    (hfl : ∀ i < 7, fl.getD i 0 = (eqKernelF lp).getD 0 0 * gx ^ iotaPos i) :
    Rep2 P (fun j => (carVT2 (s0 * ((List.range 25).map fun l => (eqKernelF lp).getD l 0 * out.getD l 0).sum + com)
        (eqKernelF (instV.take 4)) (instV.drop 4 ++ [s0]) (eqKernelF lp) fl).getD j 0)
      (firstClaimSF LeanVM.Protocol.KeccakGkr.Shape.v1 instV [s0] lp out com) true := by
  have hL : (eqKernelF lp).length = 32 := by rw [eqKernelF_length, hlp]; rfl
  have hmu : (eqKernelF (instV.take 4)).length = 16 := by
    rw [eqKernelF_length, List.length_take, hinst]; rfl
  have hiP1 : (instV.drop 4 ++ [s0]).length = P + 1 := by
    rw [List.length_append, List.length_drop, hinst, List.length_singleton]; (clear * -; omega)
  have hla : 25 ≤ (eqKernelF lp).length := by (clear * - hL; omega)
  have hB : ∀ l < 25, (repB2 P fun j => (carVT2 (s0 * ((List.range 25).map fun l => (eqKernelF lp).getD l 0 *
      out.getD l 0).sum + com) (eqKernelF (instV.take 4)) (instV.drop 4 ++ [s0]) (eqKernelF lp) fl).getD j 0).getD l 0 =
      (eqKernelF lp).getD l 0 := by
    intro l hl
    simp only [repB2, List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range hl, Option.map_some,
      Option.getD_some]
    rw [← List.getD_eq_getElem?_getD, carVT2_B hmu hiP1 hla hl, List.getD_eq_getElem?_getD]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · show (carVT2 _ _ _ _ _).getD 0 0 = com + (eqKernelF [s0]).getD (2 - 1) 0 * dotF ((eqKernelF lp).take 25) out
    rw [carVT2_v0, show (eqKernelF [s0]).getD (2 - 1) 0 = 1 * s0 from rfl, one_mul,
      dotF_eq _ _ (by rw [List.length_take, hL, hout]; rfl), List.length_take, hL,
      show min 25 32 = 25 from rfl, ← sumF_eq_sum, sumF_map_range, add_comm com]
    congr 2
    refine Finset.sum_congr rfl fun l hl => ?_
    have hl' := Finset.mem_range.mp hl
    simp [List.getD_eq_getElem?_getD, List.getElem?_take, hl']
  · show (List.range 16).map (fun i => (carVT2 _ _ _ _ _).getD (1 + i) 0) = eqKernelF (instV.take 4)
    apply List.ext_getElem (by simp [hmu])
    intro i h1 h2
    rw [List.getElem_map, List.getElem_range, carVT2_mu hmu (by simpa using h1), List.getD_eq_getElem _ _ h2]
  · show (carVT2 _ _ _ _ _).getD 17 0 = sumF (eqKernelF (instV.take 4))
    rw [carVT2_kappa hmu, sumF_eqKernelF]
  · show (List.range (P + 1)).map (fun i => (carVT2 _ _ _ _ _).getD (18 + i) 0) = instV.drop 4 ++ [s0]
    apply List.ext_getElem (by simp [hiP1])
    intro i h1 h2
    rw [List.getElem_map, List.getElem_range, carVT2_pt hmu hiP1 (by simpa using h1), List.getD_eq_getElem _ _ h2]
  · rw [if_pos rfl]
    unfold firstClaimSF
    dsimp only
    rw [firstWeightsF_eq]
    exact firstWG_congr fun i hi => (hB i hi).symm
  · intro i hi
    rw [if_pos rfl, hB 0 (by decide), carVT2_fl hmu hiP1 hla, hfl i hi]

/-- `KS`'s lane challenges, answer `k` at lane `qs + 10(k + 1)`. -/
def lanePtK2 (u : Nat → FE2) (qs : Nat) : List FE2 := (List.range 5).map fun k => u (qs + 10 * (k + 1))

theorem fx2_q2Mul (a b d : S2) (n : Nat) : Fx2 (q2Mul a b d n).1 := fx2_emit2 _ _ _

/-- **`KS`'s first-claim block** at `E2`: the segment, the committed scalar, the lanes, the carried values. -/
theorem preTB2_spec {xv : Src → FE} {V : Nat → FE} {P qs : Nat} {inst out : Nat → S2} {b : Src}
    {u : Nat → FE2} (hu : ∀ m ≤ qs + 59, lv2 xv [] m = u m) (hinst : ∀ i, Fx2 (inst i)) {n : Nat}
    (h : THold2 xv V n (preTB2 P qs inst out b n).2) :
    (preTB2 P qs inst out b n).1.seg = lane2 qs [] ∧ (preTB2 P qs inst out b n).1.com = lane2 (qs + 59) [] ∧
    vals2 xv V (preTB2 P qs inst out b n).1.lanes = eqKernelF (lanePtK2 u qs) ∧
    (∀ x ∈ (preTB2 P qs inst out b n).1.lanes, Fx2 x) ∧
    (preTB2 P qs inst out b n).1.carried.length = 57 + P ∧ (∀ x ∈ (preTB2 P qs inst out b n).1.carried, Fx2 x) ∧
    vals2 xv V (preTB2 P qs inst out b n).1.carried =
      carVT2 (u qs * ((List.range 25).map fun l =>
          (eqKernelF (lanePtK2 u qs)).getD l 0 * ((List.range 25).map fun l => (out l).valF xv V).getD l 0).sum +
          u (qs + 59))
        (eqKernelF ((List.range 4).map fun i => (inst i).valF xv V))
        (((List.range P).map fun i => (inst (4 + i)).valF xv V) ++ [u qs]) (eqKernelF (lanePtK2 u qs))
        ((List.range 7).map fun i => (eqKernelF (lanePtK2 u qs)).getD 0 0 * gx ^ iotaPos i) := by
  have hseg : (lane2 qs []).valF xv V = u qs := by rw [lane2_valF, hu _ (by (clear * -; omega))]
  have hcom : (lane2 (qs + 59) []).valF xv V = u (qs + 59) := by rw [lane2_valF, hu _ le_rfl]
  have fseg : Fx2 (lane2 qs []) := ⟨Or.inr ⟨_, _, rfl⟩, Or.inr ⟨_, _, rfl⟩⟩
  unfold preTB2 at h ⊢
  -- zero, one
  obtain ⟨h1, h, e⟩ := tb_peel2 _ _ h; rw [e]; clear e
  obtain ⟨-, ez, eo⟩ := q2Base_spec h1
  obtain ⟨fz, fo⟩ := fx2_q2Base b n
  generalize (q2Base b n).1 = base at h ez eo fz fo ⊢
  generalize n + (q2Base b n).2.length = n1 at h ⊢
  -- the lanes
  obtain ⟨h2, h, e⟩ := tb_peel2 _ _ h; rw [e]; clear e
  have el := eqTab_one2 ez eo _ n1 h2
  have elp : vals2 xv V ((List.range 5).map fun k => lane2 (qs + 10 * (k + 1)) []) = lanePtK2 u qs := by
    simp only [vals2, List.map_map, lanePtK2]
    refine List.map_congr_left fun k hk => ?_
    simp only [Function.comp_apply]
    rw [lane2_valF, hu _ (by have := List.mem_range.mp hk; (clear * - this; omega))]
  rw [elp] at el
  have fl := fx2_q2EqTab base.2.1 ((List.range 5).map fun k => lane2 (qs + 10 * (k + 1)) []) [base.2.2] n1
    (by simpa using fo)
  generalize (q2EqTab base.2.1 [base.2.2] ((List.range 5).map fun k => lane2 (qs + 10 * (k + 1)) []) n1).1 = lanes
    at h el fl ⊢
  generalize n1 + (q2EqTab base.2.1 [base.2.2] ((List.range 5).map fun k => lane2 (qs + 10 * (k + 1)) []) n1).2.length
    = n2 at h ⊢
  have hll : lanes.length = 32 := by
    have := congrArg List.length el; rw [vals2, List.length_map, eqKernelF_length] at this; simpa [lanePtK2] using this
  -- the value
  obtain ⟨h3, h, e⟩ := tb_peel2 _ _ h; rw [e]; clear e
  have ed := q2Dot_spec _ _ _ h3
  generalize (q2Dot base.2.1 ((List.range 25).map fun l => (lanes.getD l default, out l)) n2).1 = dt at h ed ⊢
  generalize n2 + (q2Dot base.2.1 ((List.range 25).map fun l => (lanes.getD l default, out l)) n2).2.length = n3
    at h ⊢
  obtain ⟨h4, h, e⟩ := tb_peel2 _ _ h; rw [e]; clear e
  have ev := q2Mul_spec h4
  have fv := fx2_q2Mul (lane2 qs []) dt (lane2 (qs + 59) []) n3
  generalize (q2Mul (lane2 qs []) dt (lane2 (qs + 59) []) n3).1 = v0 at h ev fv ⊢
  generalize n3 + (q2Mul (lane2 qs []) dt (lane2 (qs + 59) []) n3).2.length = n4 at h ⊢
  -- `μ`
  obtain ⟨h5, h, e⟩ := tb_peel2 _ _ h; rw [e]; clear e
  have em := eqTab_one2 ez eo ((List.range 4).map inst) n4 h5
  have fm := fx2_q2EqTab base.2.1 ((List.range 4).map inst) [base.2.2] n4 (by simpa using fo)
  generalize (q2EqTab base.2.1 [base.2.2] ((List.range 4).map inst) n4).1 = mu at h em fm ⊢
  generalize n4 + (q2EqTab base.2.1 [base.2.2] ((List.range 4).map inst) n4).2.length = n5 at h ⊢
  -- the flips
  obtain ⟨h6, -, e⟩ := tb_peel2 _ _ h; rw [e]; clear e
  have ef : vals2 xv V (mapT2 (fun i => q2Scale (FK.x ^ iotaPos i) (lanes.getD 0 default)) (List.range 7) n5).1 =
      (List.range 7).map fun i => (eqKernelF (lanePtK2 u qs)).getD 0 0 * gx ^ iotaPos i :=
    forall₂_map_eq2 (mapT2_spec (P := fun i x => S2.valF xv V x = (eqKernelF (lanePtK2 u qs)).getD 0 0 * gx ^ iotaPos i)
      (fun i m hm => by rw [q2Scale_spec hm, getD_valF2 _ (by (clear * - hll; omega)), el, mul_comm, fe2_ofK_pow]; rfl) _ _ h6)
  have ffl : ∀ x ∈ (mapT2 (fun i => q2Scale (FK.x ^ iotaPos i) (lanes.getD 0 default)) (List.range 7) n5).1, Fx2 x :=
    fx2_mapT2 (fun _ _ => fx2_emit2 _ _ _) _ _
  have hfl : (mapT2 (fun i => q2Scale (FK.x ^ iotaPos i) (lanes.getD 0 default)) (List.range 7) n5).1.length = 7 := by
    rw [mapT2_length]; rfl
  generalize (mapT2 (fun i => q2Scale (FK.x ^ iotaPos i) (lanes.getD 0 default)) (List.range 7) n5).1 = fls
    at ef ffl hfl ⊢
  rw [tb_pure]
  have hmu : mu.length = 16 := by
    have := congrArg List.length em; rw [vals2, List.length_map, eqKernelF_length] at this; simpa using this
  refine ⟨rfl, rfl, el, fl, ?_, ?_, ?_⟩
  · simp [hmu, hll, hfl]; (clear * -; omega)
  · intro x hx
    simp only [List.mem_append, List.mem_singleton, List.mem_map, List.mem_range] at hx
    rcases hx with (((((((rfl | hx) | rfl) | ⟨i, -, rfl⟩) | rfl) | hx) | hx) | hx)
    · exact fv
    · exact fm x hx
    · exact fo
    · exact hinst _
    · exact fseg
    · exact fl x (List.mem_of_mem_take hx)
    · rw [List.eq_of_mem_replicate hx]; exact fz
    · exact ffl x hx
  · simp only [vals2, List.map_append, List.map_cons, List.map_nil, List.map_take, List.map_replicate] at em el ef ⊢
    rw [em, el, ef, ev, ed, eo, ez, zero_add, hseg, hcom]
    simp only [carVT2, List.map_map, Function.comp_def, List.append_assoc]
    have hs : (List.map (fun x => S2.valF xv V (lanes.getD x default) * S2.valF xv V (out x)) (List.range 25)).sum =
        (List.map (fun l => (eqKernelF (lanePtK2 u qs)).getD l 0 *
          (List.map (fun l => S2.valF xv V (out l)) (List.range 25)).getD l 0) (List.range 25)).sum := by
      refine congrArg List.sum (List.map_congr_left fun l hl => ?_)
      have hl' := List.mem_range.mp hl
      rw [getD_valF2 _ (by (clear * - hll hl'; omega)), vals2, el]
      simp [List.getD_eq_getElem?_getD, hl']
    rw [hs]

/-! ## `multilinearEval` at `E2` -/

theorem q2FoldPairs_spec {xv : Src → FE} {V : Nat → FE} {z r1 r : S2} (hz : z.valF xv V = 0)
    (h1 : r1.valF xv V = 1 + r.valF xv V) : ∀ (l : List S2) (n : Nat), THold2 xv V n (q2FoldPairs z r1 r l n).2 →
      vals2 xv V (q2FoldPairs z r1 r l n).1 = foldPairsF (r.valF xv V) (vals2 xv V l)
  | a :: b :: rest, n, h => by
    simp only [q2FoldPairs] at h ⊢
    obtain ⟨g1, h, e⟩ := tb_peel2 _ _ h; rw [e]; clear e
    obtain ⟨g2, h, e⟩ := tb_peel2 _ _ h; rw [e]; clear e
    obtain ⟨g3, -, e⟩ := tb_peel2 _ _ h; rw [e]; clear e
    rw [tb_pure]
    simp only [vals2, List.map_cons, foldPairsF] at g3 ⊢
    rw [q2Mul_spec g2, q2Mul_spec g1, hz, add_zero, h1, ← vals2, q2FoldPairs_spec hz h1 rest _ g3]
  | [], _, _ => rfl
  | [_], _, _ => rfl

theorem q2Mle_spec {xv : Src → FE} {V : Nat → FE} {z : S2} (hz : z.valF xv V = 0) :
    ∀ (pt cur : List S2) (n : Nat), THold2 xv V n (q2Mle z cur pt n).2 →
      (q2Mle z cur pt n).1.valF xv V = multilinearEvalF (vals2 xv V cur) (vals2 xv V pt)
  | [], cur, n, _ => by
    simp only [q2Mle, tb_pure, multilinearEvalF, vals2, List.map_nil, List.foldl_nil]
    cases cur <;> simp [hz]
  | r :: rs, cur, n, h => by
    simp only [q2Mle] at h ⊢
    obtain ⟨g1, h, e⟩ := tb_peel2 _ _ h; rw [e]; clear e
    obtain ⟨g2, h, e⟩ := tb_peel2 _ _ h; rw [e]; clear e
    rw [q2Mle_spec hz rs _ _ h, q2FoldPairs_spec hz (q2One_spec g1) cur _ g2]
    simp only [multilinearEvalF, vals2, List.map_cons, List.foldl_cons]

theorem noA_q2FoldPairs (z r1 r : S2) : ∀ l : List S2, NoA (q2FoldPairs z r1 r l)
  | _ :: _ :: rest => noA_bind (noA_q2Mul _ _ _) fun _ => noA_bind (noA_q2Mul _ _ _) fun _ =>
      noA_bind (noA_q2FoldPairs z r1 r rest) fun _ => noA_pure _
  | [] => noA_pure _
  | [_] => noA_pure _

theorem noA_q2Mle (z : S2) : ∀ (cur pt : List S2), NoA (q2Mle z cur pt)
  | _, [] => noA_pure _
  | _, _ :: rs => noA_bind (noA_q2One _) fun _ => noA_bind (noA_q2FoldPairs _ _ _ _) fun _ => noA_q2Mle z _ rs

/-! ## The first opening block at `E2` -/

theorem mapT2_kLin_snd (g : Nat → Src) : ∀ (l : List Nat) (n : Nat),
    (mapT2 (fun t => kLin 0 0 (g t) (g t)) l n).2 = l.map fun t => (⟨.lin 0 0, .K, [g t, g t]⟩ : Ins)
  | [], _ => rfl
  | a :: as, n => by
    simp only [mapT2, tb_bind, tb_pure, List.append_nil, List.map_cons]
    rw [mapT2_kLin_snd g as]
    rfl

theorem gk_add_eq_zero2 (x y : FE2) (h : x + y = 0) : x = y := (fe2_add_eq_zero x y).mp h

/-- **The first opening block** at `E2`: the slice copies, the zero, the two `eq` tables, the committed check. -/
theorem fin1TB2_spec {xv : Src → FE} {V : Nat → FE} {qO : Nat} {b : Src} {slot1 slot3 aF : List S2}
    {seg val1 : S2} {lanes : List S2} (hlanes : 25 ≤ lanes.length) (hs1 : slot1.length = 6) {n : Nat}
    (h : THold2 xv V n (fin1TB2 qO b slot1 slot3 aF seg val1 lanes n).2) :
    (∀ t < 256, V (n + t) = xv (.ext ⟨.K, qO + 226 + 2 * (t / 2 % 64) + t % 2, []⟩)) ∧
    (fin1TB2 qO b slot1 slot3 aF seg val1 lanes n).1.z.valF xv V = 0 ∧ Fx2 (fin1TB2 qO b slot1 slot3 aF seg val1 lanes n).1.z ∧
    (fin1TB2 qO b slot1 slot3 aF seg val1 lanes n).1.word = lane2 (qO + 84) [] ∧
    vals2 xv V (fin1TB2 qO b slot1 slot3 aF seg val1 lanes n).1.e3 = eqKernelF (vals2 xv V slot3) ∧
    (∀ x ∈ (fin1TB2 qO b slot1 slot3 aF seg val1 lanes n).1.e3, Fx2 x) ∧
    vals2 xv V (fin1TB2 qO b slot1 slot3 aF seg val1 lanes n).1.ea = eqKernelF (vals2 xv V aF) ∧
    (∀ x ∈ (fin1TB2 qO b slot1 slot3 aF seg val1 lanes n).1.ea, Fx2 x) ∧
    (b.valF xv V = 1 → (TAssert xv V (fin1TB2 qO b slot1 slot3 aF seg val1 lanes n).2 ↔
      ((List.range 25).map fun l => (eqKernelF (vals2 xv V slot1)).getD (25 + l) 0 *
        (vals2 xv V lanes).getD l 0).sum * (1 + seg.valF xv V) * (lane2 (qO + 84) []).valF xv V + val1.valF xv V = 0)) := by
  unfold fin1TB2 at h ⊢
  -- the slice copies
  obtain ⟨h1, h, e⟩ := tb_peel2 _ _ h; rw [e, tassert_bind]; clear e
  have hcp : ∀ t < 256, V (n + t) = xv (.ext ⟨.K, qO + 226 + 2 * (t / 2 % 64) + t % 2, []⟩) := by
    intro t ht
    rw [mapT2_kLin_snd] at h1
    have := h1 t (by simpa using ht) (by
      simp only [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range ht, Option.map_some,
        Option.getD_some]
      exact Or.inl (Or.inr (Or.inl ⟨0, 0, rfl⟩)))
    rw [this]
    simp only [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range ht, Option.map_some,
      Option.getD_some, Ins.evalF2, Ins.evalF, List.getD_cons_zero, List.getD_cons_succ]
    rw [show FE.ofK 0 = 0 from rfl, zero_mul, add_zero, add_zero]
    rfl
  have hA1 : TAssert xv V (mapT2 (fun t => kLin 0 0 (.ext ⟨.K, qO + 226 + 2 * (t / 2 % 64) + t % 2, []⟩)
      (.ext ⟨.K, qO + 226 + 2 * (t / 2 % 64) + t % 2, []⟩)) (List.range 256) n).2 :=
    noA_mapT2 (fun _ => noA_kLin _ _ _ _) _ xv V n
  generalize n + (mapT2 (fun t => kLin 0 0 (.ext ⟨.K, qO + 226 + 2 * (t / 2 % 64) + t % 2, []⟩)
      (.ext ⟨.K, qO + 226 + 2 * (t / 2 % 64) + t % 2, []⟩)) (List.range 256) n).2.length = n1 at h ⊢
  -- zero, one
  obtain ⟨h2, h, e⟩ := tb_peel2 _ _ h; rw [e, tassert_bind]; clear e
  obtain ⟨-, ez, eo⟩ := q2Base_spec h2
  obtain ⟨fz, fo⟩ := fx2_q2Base b n1
  have hA2 := noA_q2Base b xv V n1
  generalize (q2Base b n1).1 = base at h ez eo fz fo ⊢
  generalize n1 + (q2Base b n1).2.length = n2 at h ⊢
  -- the committed check
  obtain ⟨h3, h, e⟩ := tb_peel2 _ _ h; rw [e, tassert_bind]; clear e
  have e1 := eqTab_one2 ez eo slot1 n2 h3
  have hA3 := noA_q2EqTab base.2.1 [base.2.2] slot1 xv V n2
  generalize (q2EqTab base.2.1 [base.2.2] slot1 n2).1 = t1 at h e1 ⊢
  generalize n2 + (q2EqTab base.2.1 [base.2.2] slot1 n2).2.length = n3 at h ⊢
  have ht1 : t1.length = 64 := by
    have := congrArg List.length e1; rw [vals2, List.length_map, eqKernelF_length, vals2, List.length_map, hs1] at this
    simpa using this
  obtain ⟨h4, h, e⟩ := tb_peel2 _ _ h; rw [e, tassert_bind]; clear e
  have ewc := q2Dot_spec _ _ _ h4
  have hA4 := noA_q2Dot base.2.1 ((List.range 25).map fun l => (t1.getD (25 + l) default, lanes.getD l default)) xv V n3
  generalize (q2Dot base.2.1 ((List.range 25).map fun l => (t1.getD (25 + l) default, lanes.getD l default)) n3).1 = wc
    at h ewc ⊢
  generalize n3 + (q2Dot base.2.1 ((List.range 25).map fun l => (t1.getD (25 + l) default, lanes.getD l default)) n3).2.length
    = n4 at h ⊢
  obtain ⟨h5, h, e⟩ := tb_peel2 _ _ h; rw [e, tassert_bind]; clear e
  have ef := q2One_spec h5
  have hA5 := noA_q2One seg xv V n4
  generalize (q2One seg n4).1 = f at h ef ⊢; generalize n4 + (q2One seg n4).2.length = n5 at h ⊢
  obtain ⟨h6, h, e⟩ := tb_peel2 _ _ h; rw [e, tassert_bind]; clear e
  have eww := q2Mul_spec h6
  have hA6 := noA_q2Mul wc f base.2.1 xv V n5
  generalize (q2Mul wc f base.2.1 n5).1 = w at h eww ⊢; generalize n5 + (q2Mul wc f base.2.1 n5).2.length = n6 at h ⊢
  obtain ⟨h7, h, e⟩ := tb_peel2 _ _ h; rw [e, tassert_bind]; clear e
  have et := q2Mul_spec h7
  have etz : (q2Mul w (lane2 (qO + 84) []) val1 n6).1.valF xv V = 0 ↔
      ((q2Mul w (lane2 (qO + 84) []) val1 n6).1.1.valF xv V = 0 ∧
        (q2Mul w (lane2 (qO + 84) []) val1 n6).1.2.valF xv V = 0) := emit2_zero_iff h7
  have hA7 := noA_q2Mul w (lane2 (qO + 84) []) val1 xv V n6
  generalize ht : (q2Mul w (lane2 (qO + 84) []) val1 n6).1 = t at h et etz ⊢
  generalize n6 + (q2Mul w (lane2 (qO + 84) []) val1 n6).2.length = n7 at h ⊢
  obtain ⟨-, h, e⟩ := tb_peel2 _ _ h; rw [e, tassert_bind, tassert_q2Assert]; clear e
  generalize n7 + (q2Assert t b n7).2.length = n8 at h ⊢
  -- the two tables
  obtain ⟨h9, h, e⟩ := tb_peel2 _ _ h; rw [e, tassert_bind]; clear e
  have e3 := eqTab_one2 ez eo slot3 n8 h9
  have f3 := fx2_q2EqTab base.2.1 slot3 [base.2.2] n8 (by simpa using fo)
  have hA9 := noA_q2EqTab base.2.1 [base.2.2] slot3 xv V n8
  generalize (q2EqTab base.2.1 [base.2.2] slot3 n8).1 = t3 at h e3 f3 ⊢
  generalize n8 + (q2EqTab base.2.1 [base.2.2] slot3 n8).2.length = n9 at h ⊢
  obtain ⟨h10, -, e⟩ := tb_peel2 _ _ h; rw [e, tassert_bind]; clear e
  have ea := eqTab_one2 ez eo aF n9 h10
  have fa := fx2_q2EqTab base.2.1 aF [base.2.2] n9 (by simpa using fo)
  have hA10 := noA_q2EqTab base.2.1 [base.2.2] aF xv V n9
  generalize (q2EqTab base.2.1 [base.2.2] aF n9).1 = ta at ea fa ⊢
  rw [tb_pure]
  refine ⟨hcp, ez, fz, rfl, e3, f3, ea, fa, fun hb => ?_⟩
  rw [hb, one_mul, one_mul]
  have hval : t.valF xv V = ((List.range 25).map fun l => (eqKernelF (vals2 xv V slot1)).getD (25 + l) 0 *
      (vals2 xv V lanes).getD l 0).sum * (1 + seg.valF xv V) * (lane2 (qO + 84) []).valF xv V + val1.valF xv V := by
    rw [et, eww, ef, ewc, ez, add_zero, zero_add, List.map_map]
    congr 3
    refine congrArg List.sum (List.map_congr_left fun l hl => ?_)
    have hl' := List.mem_range.mp hl
    simp only [Function.comp_apply]
    rw [getD_valF2 _ (by (clear * - ht1 hl'; omega)), getD_valF2 _ (by (clear * - hlanes hl'; omega)), e1]
  rw [← hval]
  constructor
  · rintro ⟨-, -, -, -, -, -, -, ⟨ht1', ht2'⟩, -, -, -⟩
    exact etz.mpr ⟨ht1', ht2'⟩
  · intro hz
    obtain ⟨z1, z2⟩ := etz.mp hz
    exact ⟨hA1, hA2, hA3, hA4, hA5, hA6, hA7, ⟨z1, z2⟩, hA9, hA10, fun k hk => by simp [tb_pure] at hk⟩

/-! ## The rotated sums at `E2` -/

theorem flatMap2_length (g : Nat → List Ins) (hg : ∀ w, (g w).length = 2) :
    ∀ n, ((List.range n).flatMap g).length = 2 * n
  | 0 => rfl
  | n + 1 => by rw [List.range_succ, List.flatMap_append, List.length_append, flatMap2_length g hg n]; simp [hg]; ring

theorem flatMap2_getD (g : Nat → List Ins) (hg : ∀ w, (g w).length = 2) :
    ∀ (n w j : Nat), w < n → j < 2 → ((List.range n).flatMap g).getD (2 * w + j) default = (g w).getD j default
  | 0, _, _, h, _ => absurd h (Nat.not_lt_zero _)
  | n + 1, w, j, hw, hj => by
    have hlen := flatMap2_length g hg n
    rw [List.range_succ, List.flatMap_append]
    rcases Nat.lt_or_ge w n with h | h
    · rw [List.getD_append _ _ _ _ (by rw [hlen]; omega), flatMap2_getD g hg n w j h hj]
    · obtain rfl : w = n := by omega
      rw [List.getD_append_right _ _ _ _ (by rw [hlen]; omega), hlen, show 2 * w + j - 2 * w = j by omega]
      simp

theorem rotIns2_getD (ea : List S2) (sb : Nat) (z : S2) {w j : Nat} (hw : w < 64) (hj : j < 2) :
    (rotIns2 ea sb z).getD (2 * w + j) default =
      (mul2I (ea.getD w default) (.ext ⟨.K, sb + 2 * w, [2]⟩, .ext ⟨.K, sb + 2 * w + 1, [2]⟩)
        (if w = 0 then z else locS2 (2 * (w - 1)))).getD j default :=
  flatMap2_getD _ (fun _ => rfl) 64 w j hw hj

theorem rotIns2_length (ea : List S2) (sb : Nat) (z : S2) : (rotIns2 ea sb z).length = 128 := by
  simp [rotIns2, mul2I, e2I]

/-- A twin pair inside a held list. -/
theorem thold2_pair {xv : Src → FE} {V : Nat → FE} {n : Nat} {δ : List Ins} (h : THold2 xv V n δ) {k : Nat} {f : E2Fn}
    {xs : List S2} (hk : δ.getD k default = ⟨.e2 f false, .K, s2Args xs⟩)
    (hk1 : δ.getD (k + 1) default = ⟨.e2 f true, .K, s2Args xs⟩) (hlen : k + 1 < δ.length) :
    (⟨(V (n + k)).c₀, (V (n + k + 1)).c₀⟩ : FE2) = f.val fun o => ((s2Args xs).getD o default |>.valF xv V).c₀ := by
  have h0 := h k (by (clear * - hlen; omega)) (Or.inr ⟨f, false, by rw [hk]⟩)
  have h1 := h (k + 1) hlen (Or.inr ⟨f, true, by rw [hk1]⟩)
  rw [hk] at h0
  rw [hk1] at h1
  simp only [Ins.evalF2] at h0 h1
  apply FE2.ext_coord
  · show (V (n + k)).c₀ = _; rw [h0]; rfl
  · show (V (n + k + 1)).c₀ = _; rw [Nat.add_assoc, h1]; rfl

/-- **The rotation block** at `E2`: iteration `i`'s last pair is `Σ_w A(w)·slice(sb + 2w + 2i)`. -/
theorem rot2_spec {c : Ctx} {M : Mem} {p : Ptr} {ea : List S2} {sb : Nat} {z : S2}
    (h : SegsHold c M p (loop [6] (tplOf (rotIns2 ea sb z)) p).2) {A : Nat → FE2}
    (hA : ∀ w < 64, ∀ jf < 64, (ea.getD w default).valF (iterXv M (loop [6] (tplOf (rotIns2 ea sb z)) p).1 jf)
      (iterF M (loop [6] (tplOf (rotIns2 ea sb z)) p).1 jf) = A w)
    (hz : ∀ jf < 64, z.valF (iterXv M (loop [6] (tplOf (rotIns2 ea sb z)) p).1 jf)
      (iterF M (loop [6] (tplOf (rotIns2 ea sb z)) p).1 jf) = 0) {i : Nat} (hi : i < 64) :
    (⟨(iterF M (loop [6] (tplOf (rotIns2 ea sb z)) p).1 i 126).c₀,
      (iterF M (loop [6] (tplOf (rotIns2 ea sb z)) p).1 i 127).c₀⟩ : FE2) =
      ((List.range 64).map fun w => A w * ⟨M.k (sb + 2 * w + 2 * i), M.k (sb + 2 * w + 1 + 2 * i)⟩).sum := by
  have hH := thold2_of_loop h (jf := i) (by simpa using hi)
  have hx : ∀ b, (Src.ext ⟨.K, b, [2]⟩).valF (iterXv M (loop [6] (tplOf (rotIns2 ea sb z)) p).1 i)
      (iterF M (loop [6] (tplOf (rotIns2 ea sb z)) p).1 i) = FE.ofK (M.k (b + 2 * i)) :=
    fun b => iterXv_ext1 M _ rfl (by simpa using hi) _ _ _
  have key : ∀ w < 64, (⟨(iterF M (loop [6] (tplOf (rotIns2 ea sb z)) p).1 i (2 * w)).c₀,
      (iterF M (loop [6] (tplOf (rotIns2 ea sb z)) p).1 i (2 * w + 1)).c₀⟩ : FE2) =
      ((List.range (w + 1)).map fun w' => A w' * ⟨M.k (sb + 2 * w' + 2 * i), M.k (sb + 2 * w' + 1 + 2 * i)⟩).sum := by
    intro w
    induction w with
    | zero =>
      intro _
      have := thold2_pair hH (k := 0) (f := .mul)
        (xs := [ea.getD 0 default, (.ext ⟨.K, sb + 2 * 0, [2]⟩, .ext ⟨.K, sb + 2 * 0 + 1, [2]⟩), z])
        (by rw [show 0 = 2 * 0 + 0 from rfl, rotIns2_getD _ _ _ (by (clear * -; omega)) (by (clear * -; omega))]; simp [mul2I, e2I])
        (by rw [show 0 + 1 = 2 * 0 + 1 from rfl, rotIns2_getD _ _ _ (by (clear * -; omega)) (by (clear * -; omega))]; simp [mul2I, e2I])
        (by rw [rotIns2_length]; (clear * -; omega))
      rw [Nat.zero_add] at this
      rw [Nat.mul_zero, Nat.zero_add, this]
      show (ea.getD 0 default).valF _ _ * (⟨(Src.valF _ _ (.ext ⟨.K, sb + 2 * 0, [2]⟩)).c₀,
        (Src.valF _ _ (.ext ⟨.K, sb + 2 * 0 + 1, [2]⟩)).c₀⟩ : FE2) + z.valF _ _ = _
      rw [hA 0 (by (clear * -; omega)) i hi, hz i hi, hx, hx, fe_ofK_c0, fe_ofK_c0, add_zero]
      simp
    | succ w ih =>
      intro hw
      have := thold2_pair hH (k := 2 * (w + 1)) (f := .mul)
        (xs := [ea.getD (w + 1) default, (.ext ⟨.K, sb + 2 * (w + 1), [2]⟩, .ext ⟨.K, sb + 2 * (w + 1) + 1, [2]⟩),
          locS2 (2 * w)])
        (by rw [show 2 * (w + 1) = 2 * (w + 1) + 0 from rfl, rotIns2_getD _ _ _ hw (by (clear * -; omega))]; simp [mul2I, e2I])
        (by rw [rotIns2_getD _ _ _ hw (by (clear * -; omega))]; simp [mul2I, e2I])
        (by rw [rotIns2_length]; (clear * - hw; omega))
      rw [Nat.zero_add] at this
      rw [this]
      show (ea.getD (w + 1) default).valF _ _ * (⟨(Src.valF _ _ (.ext ⟨.K, sb + 2 * (w + 1), [2]⟩)).c₀,
        (Src.valF _ _ (.ext ⟨.K, sb + 2 * (w + 1) + 1, [2]⟩)).c₀⟩ : FE2) +
          (⟨(iterF M (loop [6] (tplOf (rotIns2 ea sb z)) p).1 i (2 * w)).c₀,
            (iterF M (loop [6] (tplOf (rotIns2 ea sb z)) p).1 i (2 * w + 1)).c₀⟩ : FE2) = _
      rw [hA (w + 1) hw i hi, hx, hx, fe_ofK_c0, fe_ofK_c0, ih (by (clear * - hw; omega)), List.range_succ (n := w + 1), List.map_append,
        List.sum_append]
      simp [add_comm]
  exact key 63 (by (clear * -; omega))

/-! ## The input check block at `E2` -/

theorem fin2_lane2 {xv : Src → FE} {V : Nat → FE} {z : S2} (hz : z.valF xv V = 0) {B : List S2} (hB : 25 ≤ B.length)
    (R : Nat → S2) {e3 : List S2} {x x1 : S2} (hx1 : x1.valF xv V = 1 + x.valF xv V) {l : Nat} (hl : l < 25)
    (m : Nat) (h : THold2 xv V m ((q2LaneForm z B R l >>= fun lf => q2Mul (e3.getD l default) x1 z >>= fun u =>
      q2Mul (e3.getD (25 + l) default) x u >>= fun u' => q2Mul u' lf z) m).2) :
    ((q2LaneForm z B R l >>= fun lf => q2Mul (e3.getD l default) x1 z >>= fun u =>
      q2Mul (e3.getD (25 + l) default) x u >>= fun u' => q2Mul u' lf z) m).1.valF xv V =
      ((e3.getD (25 + l) default).valF xv V * x.valF xv V + (e3.getD l default).valF xv V * (1 + x.valF xv V)) *
        laneFormF (vals2 xv V B) (fun s => (R s).valF xv V) l := by
  obtain ⟨g1, h, e⟩ := tb_peel2 _ _ h; rw [e]; clear e
  have el := q2LaneForm_spec hz hB R hl m g1
  obtain ⟨g2, h, e⟩ := tb_peel2 _ _ h; rw [e]; clear e
  obtain ⟨g3, h, e⟩ := tb_peel2 _ _ h; rw [e]; clear e
  rw [q2Mul_spec h, q2Mul_spec g3, q2Mul_spec g2, el, hz, add_zero, add_zero, hx1]

/-- **The input check block** at `E2`: with the gate `1`, its assertion is `V`'s input check. -/
theorem fin2TB2_spec {xv : Src → FE} {V : Nat → FE} {b : Src} {z : S2} {B : List S2} {R : Nat → S2} {e3 : List S2}
    {x : S2} {mu low : List S2} {val3 : S2} (hz : z.valF xv V = 0) (hB : 25 ≤ B.length) (he3 : 50 ≤ e3.length)
    {n : Nat} (h : THold2 xv V n (fin2TB2 b z B R e3 x mu low val3 n).2) (hb : b.valF xv V = 1) :
    TAssert xv V (fin2TB2 b z B R e3 x mu low val3 n).2 ↔
      multilinearEvalF (vals2 xv V mu) (vals2 xv V low) *
        ((List.range 25).map fun l => ((vals2 xv V e3).getD (25 + l) 0 * x.valF xv V +
          (vals2 xv V e3).getD l 0 * (1 + x.valF xv V)) * laneFormF (vals2 xv V B) (fun s => (R s).valF xv V) l).sum +
        val3.valF xv V = 0 := by
  unfold fin2TB2 at h ⊢
  obtain ⟨h1, h, e⟩ := tb_peel2 _ _ h; rw [tassert_bind]; clear e
  have ex := q2One_spec h1
  have hA1 := noA_q2One x xv V n
  generalize (q2One x n).1 = x1 at h ex ⊢; generalize n + (q2One x n).2.length = n1 at h ⊢
  obtain ⟨h2, h, e⟩ := tb_peel2 _ _ h; rw [tassert_bind]; clear e
  have et := q2SumMap_spec hz (F := fun l => ((vals2 xv V e3).getD (25 + l) 0 * x.valF xv V +
      (vals2 xv V e3).getD l 0 * (1 + x.valF xv V)) * laneFormF (vals2 xv V B) (fun s => (R s).valF xv V) l)
    (fun l hl m hm => by
      rw [fin2_lane2 hz hB R ex hl m hm, getD_valF2 _ (by (clear * - he3 hl; omega)), getD_valF2 _ (by (clear * - he3 hl; omega))]) n1 h2
  have hA2 := noA_q2SumMap z 25 (f := fun l => q2LaneForm z B R l >>= fun lf => q2Mul (e3.getD l default) x1 z >>= fun u =>
    q2Mul (e3.getD (25 + l) default) x u >>= fun u' => q2Mul u' lf z)
    (fun _ => noA_bind (noA_q2LaneForm _ _ _ _) fun _ => noA_bind (noA_q2Mul _ _ _) fun _ =>
      noA_bind (noA_q2Mul _ _ _) fun _ => noA_q2Mul _ _ _) xv V n1
  generalize (q2SumMap z 25 _ n1).1 = tot at h et ⊢
  generalize n1 + (q2SumMap z 25 _ n1).2.length = n2 at h ⊢
  obtain ⟨h3, h, e⟩ := tb_peel2 _ _ h; rw [tassert_bind]; clear e
  have em := q2Mle_spec hz low mu n2 h3
  have hA3 := noA_q2Mle z mu low xv V n2
  generalize (q2Mle z mu low n2).1 = mle at h em ⊢; generalize n2 + (q2Mle z mu low n2).2.length = n3 at h ⊢
  obtain ⟨h4, -, e⟩ := tb_peel2 _ _ h; rw [tassert_bind, tassert_q2Assert, hb, one_mul, one_mul]; clear e
  have etz : (q2Mul mle tot val3 n3).1.valF xv V = 0 ↔
      ((q2Mul mle tot val3 n3).1.1.valF xv V = 0 ∧ (q2Mul mle tot val3 n3).1.2.valF xv V = 0) := emit2_zero_iff h4
  rw [q2Mul_spec h4, em, et] at etz
  rw [← etz]
  exact ⟨fun ⟨_, _, _, _, hz'⟩ => hz', fun hz' => ⟨hA1, hA2, hA3, noA_q2Mul _ _ _ xv V n3, hz'⟩⟩

/-! ## The `KS` gadget against `V` (WRITTEN DURING THE PAUSE, NOT YET BUILT: blocks through the rotation were
elaborated in scratch before the pause; `gkr_core2`'s tail, `vkSpec2_pwO`, `gkr_spec2`, `gkr_phase2`, `gnoA_rotIns2` are
unbuilt) -/

/-! ## The `KS` gadget's blocks -/

theorem noA_scTpl2 (d q : Nat) (xv : Src → FE) (V : Nat → FE) : TAssert xv V (scTpl2 d q) := by
  unfold scTpl2 scRound2
  exact noA_bind (noA_q2Sum _ _) (fun _ => noA_q2Horner _ _ _) xv V 0

/-- A sumcheck gadget at `E2` asserts nothing. -/
theorem sc2_asserts (M : Mem) (p : Ptr) (D d q : Nat) (claim : C2) : SegsAssert M p (scGadget2 D d q claim p).2 := by
  rw [scGadget2, loopP_apply, segsAssert_append]
  refine ⟨prologueSegs_assert M _ p 0 _, ?_⟩
  have := (segsAssert_loop_iff (M := M) (dims := [D]) (ins := scTpl2 d q)
    (p := p.adv (prologueSegs (fun t => if t = scLen2 d - 1 then claim.im else claim.re) 0 (tplOf (scTpl2 d q))))).mpr
    (fun jf _ => noA_scTpl2 d q _ _)
  simpa [loop_apply] using this

/-- **The sumcheck gadget's lists**: its `R` challenge cells and its last claim cell are `V`'s. -/
theorem sc2_lists {c : Ctx} {M : Mem} {p : Ptr} {D q R : Nat} {claim : C2} {sig : ByteArray} {T : Nat} (g : Nat)
    (hR : R ≤ 2 ^ D) (hR1 : 1 ≤ R) (hq : 5 ≤ q) (hS : Streamed M sig T) (hT : q + 14 * R + 7 ≤ T)
    (h : SegsHold c M p (scGadget2 D 2 q claim p).2) :
    (List.range R).map (fun i => (scChal2 2 q i).val M) =
        (scSpec2 (fe2At sig) (feAt sig) g 3 (8 * q - 40) (claim.val M) R).1 ∧
    (scClaim2 (scGadget2 D 2 q claim p).1 2 (R - 1)).val M =
        (scSpec2 (fe2At sig) (feAt sig) g 3 (8 * q - 40) (claim.val M) R).2.1 := by
  have hs := sc2_spec (R := R) g hR hq hS hT h
  refine ⟨?_, ?_⟩
  · apply List.ext_getElem (by rw [List.length_map, List.length_range, scSpec2_length])
    intro i h1 h2
    rw [List.getElem_map, List.getElem_range, (hs i (by simpa using h1)).1,
      List.getD_eq_getElem _ _ h2]
  · have := (hs (R - 1) (by (clear * - hR1; omega))).2
    rw [show R - 1 + 1 = R by (clear * - hR1; omega)] at this
    exact this

theorem drop_last2 {l : List FE2} {P : Nat} (h : l.length = P + 1) : l.drop P = [l.getD P 0] := by
  apply List.ext_getElem (by simp [h])
  intro i h1 h2
  simp only [List.length_singleton, Nat.lt_one_iff] at h2
  subst h2
  rw [List.getD_eq_getElem _ _ (by (clear * - h; omega))]
  simp

/-- `KS`'s `ι` term at `E2`: two segments, the point's last coordinate selects. -/
theorem iotaSF_v1 {P k : Nat} {C : KClaim FE2} (hC : C.point.length = P + 1) :
    iotaSF LeanVM.Protocol.KeccakGkr.Shape.v1 (P + 4) k C =
      (1 + C.point.getD P 0) * iotaFG (keccakRC.getD (gkrDepth * 1 - k - 1) 0) C.weights +
        C.point.getD P 0 * iotaFG (keccakRC.getD (gkrDepth * 2 - k - 1) 0) C.weights := by
  have hd : C.point.drop (P + 4 - 4) = [C.point.getD P 0] := by
    rw [show P + 4 - 4 = P by (clear * -; omega)]; exact drop_last2 hC
  unfold iotaSF
  rw [hd]
  show sumF [(eqKernelF [C.point.getD P 0]).getD 0 0 * _, (eqKernelF [C.point.getD P 0]).getD 1 0 * _] = _
  rw [sumF_eq_sum, List.sum_cons, List.sum_singleton,
    show (eqKernelF [C.point.getD P 0]).getD 0 0 = 1 * (1 + C.point.getD P 0) from rfl,
    show (eqKernelF [C.point.getD P 0]).getD 1 0 = 1 * C.point.getD P 0 from rfl, one_mul, one_mul]
  rfl

theorem noA_preTB2 (P qs : Nat) (inst out : Nat → S2) (b : Src) : NoA (preTB2 P qs inst out b) :=
  noA_bind (noA_q2Base _) fun _ => noA_bind (noA_q2EqTab _ _ _) fun _ => noA_bind (noA_q2Dot _ _) fun _ =>
    noA_bind (noA_q2Mul _ _ _) fun _ => noA_bind (noA_q2EqTab _ _ _) fun _ =>
      noA_bind (noA_mapT2 (fun _ => noA_q2Scale _ _) _) fun _ => noA_pure _

theorem rot_reindex2 (A S : Nat → FE2) {s : Nat} (hs : s < 64) :
    ((List.range 64).map fun w => A w * S ((w + (64 - s) % 64) % 64)).sum =
      sumF ((List.range 64).map fun z => S z * A ((z + s) % 64)) := by
  rw [sumF_map_range, ← sumF_eq_sum, sumF_map_range]
  symm
  refine Finset.sum_nbij' (fun z => (z + s) % 64) (fun w => (w + (64 - s) % 64) % 64) ?_ ?_ ?_ ?_ ?_
  · intro a _; simp only [Finset.mem_range]; (clear * -; omega)
  · intro a _; simp only [Finset.mem_range]; (clear * -; omega)
  · intro a ha; simp only [Finset.mem_range] at ha; (clear * - hs ha; omega)
  · intro a ha; simp only [Finset.mem_range] at ha; (clear * - hs ha; omega)
  · intro a ha
    simp only [Finset.mem_range] at ha
    rw [show ((a + s) % 64 + (64 - s) % 64) % 64 = a by (clear * - hs ha; omega), mul_comm]

theorem sum2_lanes2 (e : Nat → FE2) (x : FE2) (lf : Nat → FE2) :
    sumF ((List.range 2).map fun s => sumF ((List.range 25).map fun l => e (25 * s + l) * (eqKernelF [x]).getD s 0 * lf l)) =
      ((List.range 25).map fun l => (e (25 + l) * x + e l * (1 + x)) * lf l).sum := by
  rw [sumF_map_range, ← sumF_eq_sum, sumF_map_range, Finset.sum_range_succ, Finset.sum_range_one, sumF_map_range,
    sumF_map_range, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun l _ => ?_
  rw [show (eqKernelF [x]).getD 0 0 = 1 * (1 + x) from rfl, show (eqKernelF [x]).getD 1 0 = 1 * x from rfl]
  simp only [Nat.mul_zero, Nat.zero_add, Nat.mul_one]
  ring

theorem headD_getD2 (l : List FE2) : l.headD 0 = l.getD 0 0 := by cases l <;> rfl

theorem laneC2_s2_valF {M : Mem} {sig : ByteArray} {T : Nat} (hS : Streamed M sig T) (o : LoopOut) (jf a : Nat)
    (V : Nat → FE) (ha : a + 1 < T) : (laneC2 a).s2.valF (iterXv M o jf) V = fe2At sig (8 * a) := by
  rw [s2_valF_s2, laneC2_val hS ha]


theorem fin1TB2_snd (qO : Nat) (b : Src) (slot1 slot3 aF : List S2) (seg val1 : S2) (lanes : List S2) :
    ∃ B, (fin1TB2 qO b slot1 slot3 aF seg val1 lanes 0).2 =
      ((List.range 256).map fun t => (⟨.lin 0 0, .K, [.ext ⟨.K, qO + 226 + 2 * (t / 2 % 64) + t % 2, []⟩,
        .ext ⟨.K, qO + 226 + 2 * (t / 2 % 64) + t % 2, []⟩]⟩ : Ins)) ++ B := by
  unfold fin1TB2
  rw [tb_bind, mapT2_kLin_snd]
  exact ⟨_, rfl⟩

/-- The first opening block's slice copies are its first `256` `K` cells. -/
theorem fin1_cells (M : Mem) (p : Ptr) (qO : Nat) (b : Src) (slot1 slot3 aF : List S2) (seg val1 : S2)
    (lanes : List S2) {t : Nat} (ht : t < 256) :
    iterF M ⟨p, [], tplOf (fin1TB2 qO b slot1 slot3 aF seg val1 lanes 0).2⟩ 0 t = FE.ofK (M.k (p.k + t)) := by
  obtain ⟨B, hsnd⟩ := fin1TB2_snd qO b slot1 slot3 aF seg val1 lanes
  generalize (fin1TB2 qO b slot1 slot3 aF seg val1 lanes 0).2 = δ at hsnd ⊢
  generalize hA : ((List.range 256).map fun t => (⟨.lin 0 0, .K, [.ext ⟨.K, qO + 226 + 2 * (t / 2 % 64) + t % 2, []⟩,
    .ext ⟨.K, qO + 226 + 2 * (t / 2 % 64) + t % 2, []⟩]⟩ : Ins)) = A at hsnd
  have hAl : A.length = 256 := by rw [← hA]; simp
  have hw : ∀ i ∈ A, Row.w .K ⟨i.op, i.ty, []⟩ = 1 := by
    intro i hi; rw [← hA] at hi; simp only [List.mem_map] at hi; obtain ⟨a, -, rfl⟩ := hi; rfl
  have hlr : lrank .K (tplOf δ) t = t := by
    rw [hsnd, lrank_append_le _ _ _ (by (clear * - ht hAl; omega)), lrank_ones hw (by (clear * - ht hAl; omega))]
  have hty : ((tplOf δ).getD t default).ty = .K := by
    have hk' : t < δ.length := by rw [hsnd, List.length_append]; (clear * - ht hAl; omega)
    rw [tplOf_getD _ hk']
    show (δ.getD t default).ty = _
    rw [hsnd, List.getD_append _ _ _ _ (by (clear * - ht hAl; omega)), ← hA]
    simp [List.getD_eq_getElem?_getD, ht]
  show Cell.val M (LoopOut.cell ⟨p, [], tplOf δ⟩ t 0) = _
  simp only [LoopOut.cell, hty, hlr, Cell.val, Ptr.at, Nat.mul_zero, Nat.add_zero]
  rfl

theorem fe_ofK_inj {a b : FK} (h : FE.ofK a = FE.ofK b) : a = b := congrArg FE.c₀ h

/-- The `KS` constants block read as `layers2_spec`'s constants. -/
theorem ks_cst {M : Mem} {pk : Nat} {β : FE}
    (hc : ∀ t < 256, FE.ofK (M.k (pk + t)) =
      if t % 16 = 15 then (if t / 16 < 12 then β else 0) else FE.ofK (cstK (t / 16) (t % 16)))
    {jf : Nat} (hjf : jf < 12) :
    (∀ i < 7, FE.ofK (M.k (pk + (16 * jf + i))) = rcBit (keccakRC.getD (gkrDepth * 1 - jf - 1) 0) i ∧
      FE.ofK (M.k (pk + (16 * jf + (7 + i)))) = rcBit (keccakRC.getD (gkrDepth * 2 - jf - 1) 0) i) ∧
    FE.ofK (M.k (pk + (16 * jf + 14))) = (if (true && jf == 0) = true then 1 else 0) := by
  refine ⟨fun i hi => ⟨?_, ?_⟩, ?_⟩
  · rw [hc _ (by (clear * - hjf hi; omega)), if_neg (by (clear * - hi; omega)), show (16 * jf + i) / 16 = jf by (clear * - hi; omega),
      show (16 * jf + i) % 16 = i by (clear * - hi; omega), ← ofK_rcK]
    simp only [cstK, if_neg (show ¬ 12 ≤ jf by (clear * - hjf; omega)), if_pos hi]
  · rw [hc _ (by (clear * - hjf hi; omega)), if_neg (by (clear * - hi; omega)), show (16 * jf + (7 + i)) / 16 = jf by (clear * - hi; omega),
      show (16 * jf + (7 + i)) % 16 = 7 + i by (clear * - hi; omega), ← ofK_rcK]
    simp only [cstK, if_neg (show ¬ 12 ≤ jf by (clear * - hjf; omega)), if_neg (show ¬ 7 + i < 7 by (clear * -; omega)),
      if_pos (show 7 + i < 14 by (clear * - hi; omega)), show 7 + i - 7 = i by (clear * -; omega)]
  · rw [hc _ (by (clear * - hjf; omega)), if_neg (by (clear * -; omega)), show (16 * jf + 14) / 16 = jf by (clear * -; omega),
      show (16 * jf + 14) % 16 = 14 by (clear * -; omega), Bool.true_and]
    simp only [cstK, if_neg (show ¬ 12 ≤ jf by (clear * - hjf; omega)), if_neg (show ¬ 14 < 7 by (clear * -; omega)),
      if_neg (show ¬ 14 < 14 by (clear * -; omega))]
    rcases Nat.eq_zero_or_pos jf with h0 | h0
    · rw [h0]; rfl
    · rw [if_neg (by (clear * - h0; omega)), if_neg (by rw [beq_iff_eq]; (clear * - h0; omega))]; rfl

/-- The gadget's first-claim block's lanes for `V`'s view (`sampsG` from the segment's entry `8 qs − 48`). -/
theorem lanes_eq_sampsG (sig : ByteArray) {qs : Nat} (hq : 6 ≤ qs) :
    sampsG (feAt sig) (8 * qs - 48 + 80) 5 = lanePtK2 (fun m => fe2At sig (8 * m)) qs := by
  rw [sampsG_eq, lanePtK2]
  refine List.map_congr_left fun k _ => ?_
  rw [e2OfFE_feAt, show 8 * qs - 48 + 80 + 48 + 80 * k = 8 * (qs + 10 * (k + 1)) by (clear * - hq; omega)]

theorem seg_eq_sampsG (sig : ByteArray) {qs : Nat} (hq : 6 ≤ qs) :
    sampsG (feAt sig) (8 * qs - 48) 1 = [fe2At sig (8 * qs)] := by
  rw [sampsG_eq]
  simp only [List.range_one, List.map_cons, List.map_nil, Nat.mul_zero, Nat.add_zero]
  rw [e2OfFE_feAt, show 8 * qs - 48 + 48 = 8 * qs by (clear * - hq; omega)]

/-- The rotation block asserts nothing. -/
theorem gnoA_rotIns2 (ea : List S2) (sb : Nat) (z : S2) : GNoA (rotIns2 ea sb z) := by
  intro k hk
  rw [rotIns2_length] at hk
  rw [show k = 2 * (k / 2) + k % 2 by (clear * -; omega), rotIns2_getD _ _ _ (by (clear * - hk; omega)) (Nat.mod_lt _ (by (clear * -; omega)))]
  rcases Nat.mod_two_eq_zero_or_one k with h | h <;> simp [h, mul2I, e2I]

set_option maxRecDepth 20000 in
/-- **The `KS` gadget at `E2`** (`V`'s `verifyKeccakD (P + 4)` read as `vkSpec2` from the segment challenge's entry
`8 qs − 48`): its outputs are `V`'s result, and with the gate `1` its assertions hold iff `V`'s two final checks and
every layer's two checks do. -/
theorem gkr_core2 {c : Ctx} {M : Mem} {p : Ptr} {P qs : Nat} {inst out : Nat → C2} {b : Cell}
    {sig : ByteArray} {T : Nat} (hP : layOk2 P = true) (hq : 6 ≤ qs) (hS : Streamed M sig T)
    (hT : gkrEnd2 P qs ≤ T) (h : SegsHold c M p (gkrGadgetE2 P qs inst out b p).2) :
    ([((gkrGadgetE2 P qs inst out b p).1.wordPoint.map (C2.val M), (gkrGadgetE2 P qs inst out b p).1.word.val M)],
      (gkrGadgetE2 P qs inst out b p).1.slicePoint.map (C2.val M),
      (gkrGadgetE2 P qs inst out b p).1.slices.map (C2.val M)) =
      (vkSpec2 (fe2At sig) (feAt sig) P ((List.range (P + 4)).map fun i => (inst i).val M)
        ((List.range 25).map fun l => (out l).val M) (8 * qs - 48)).res ∧
    (b.val M = 1 → (SegsAssert M p (gkrGadgetE2 P qs inst out b p).2 ↔
      (vkSpec2 (fe2At sig) (feAt sig) P ((List.range (P + 4)).map fun i => (inst i).val M)
        ((List.range 25).map fun l => (out l).val M) (8 * qs - 48)).ok1 = true ∧
      (vkSpec2 (fe2At sig) (feAt sig) P ((List.range (P + 4)).map fun i => (inst i).val M)
        ((List.range 25).map fun l => (out l).val M) (8 * qs - 48)).ok2 = true ∧
      ∀ k < 12,
        (lay2At (fe2At sig) (feAt sig) (fun k => iotaSF LeanVM.Protocol.KeccakGkr.Shape.v1 (P + 4) (0 + k))
          (firstClaimSF LeanVM.Protocol.KeccakGkr.Shape.v1 ((List.range (P + 4)).map fun i => (inst i).val M)
            (sampsG (feAt sig) (8 * qs - 48) 1) (sampsG (feAt sig) (8 * qs - 48 + 80) 5)
            ((List.range 25).map fun l => (out l).val M) (fe2At sig (8 * qs - 48 + 520)))
          (8 * qs - 48 + 496) (2440 + 112 * (P + 1)) k).ok1 = true ∧
        (lay2At (fe2At sig) (feAt sig) (fun k => iotaSF LeanVM.Protocol.KeccakGkr.Shape.v1 (P + 4) (0 + k))
          (firstClaimSF LeanVM.Protocol.KeccakGkr.Shape.v1 ((List.range (P + 4)).map fun i => (inst i).val M)
            (sampsG (feAt sig) (8 * qs - 48) 1) (sampsG (feAt sig) (8 * qs - 48 + 80) 5)
            ((List.range 25).map fun l => (out l).val M) (fe2At sig (8 * qs - 48 + 520)))
          (8 * qs - 48 + 496) (2440 + 112 * (P + 1)) k).ok2 = true)) := by
  generalize hinstV : ((List.range (P + 4)).map fun i => (inst i).val M) = instV
  generalize houtV : ((List.range 25).map fun l => (out l).val M) = outV
  have hinstL : instV.length = P + 4 := by rw [← hinstV]; simp
  have hstr : (lay02 P).str2 = 305 + 14 * (P + 1) := rfl
  have hqO : gkrQO2 P qs = qs + 61 + 12 * (lay02 P).str2 := rfl
  have hTq : gkrQO2 P qs + 354 ≤ T := hT
  rw [seg_eq_sampsG sig hq, lanes_eq_sampsG sig hq, show 8 * qs - 48 + 520 = 8 * (qs + 59) by (clear * - hq; omega),
    show 8 * qs - 48 + 496 = 8 * (qs + 61) - 40 by (clear * - hq; omega),
    show 2440 + 112 * (P + 1) = 8 * (lay02 P).str2 by rw [hstr]; ring]
  rw [gkrGadgetE2, VF.loopF_eq] at h ⊢
  simp only [hold_bind, assert_bind, gk_bind_fst_eq, gk_pure_apply_eq, gk_getPtr_eq, Ptr.adv_nil] at h ⊢
  obtain ⟨-, hK, hPre, hCp, hLay, hS1, hS2, hS3, hF1, hRot, hF2, -⟩ := h
  -- the constants
  have hc := fun t (ht : t < 256) => cst_spec hK (t := t) ht
  have hAK : SegsAssert M p (loop [] (tplOf (cstIns (gkS b))) p).2 :=
    segsAssert_loop_iff.mpr fun _ _ => tassert_noA (gnoA_map _ _ fun t => by
      obtain ⟨k, k', hk⟩ := cstI_op (gkS b) t; rw [hk]; exact Lvm.Loop.Op.noConfusion)
  generalize p.adv (loop [] (tplOf (cstIns (gkS b))) p).2 = p1 at hPre hCp hLay hS1 hS2 hS3 hF1 hRot hF2 ⊢
  -- the first claim
  have hpre0 := thold2_of_loop hPre (jf := 0) (by simp)
  rw [gk_loop_fst] at hpre0
  obtain ⟨es, ec, el, fl, lc, fcar, ecar⟩ := preTB2_spec (u := fun m => fe2At sig (8 * m))
    (fun m hm => lv2_fix hS _ 0 m (by (clear * - hqO hTq hm; omega))) (fun i => fx2_s2 (inst i)) hpre0
  have hAPre := (segsAssert_loop_iff (M := M) (dims := []) (p := p1)).mpr fun _ _ =>
    noA_preTB2 P qs (fun i => (inst i).s2) (fun l => (out l).s2) (gkS b) _ _ 0
  simp only [s2_valF_s2, hinstV, houtV] at ecar
  set preT := preTB2 P qs (fun i => (inst i).s2) (fun l => (out l).s2) (gkS b) 0 with hpreT
  simp only [gk_loop_fst] at hCp hLay hS1 hS2 hS3 hF1 hRot hF2 ⊢
  generalize p1.adv (loop [] (tplOf preT.2) p1).2 = p2 at hCp hLay hS1 hS2 hS3 hF1 hRot hF2 ⊢
  -- the copies
  have hcopy : ∀ j < 57 + P, (⟨M.k (p2.k + 2 * j), M.k (p2.k + 2 * j + 1)⟩ : FE2) =
      (vals2 (iterXv M ⟨p1, [], tplOf preT.2⟩ 0) (iterF M ⟨p1, [], tplOf preT.2⟩ 0) preT.1.carried).getD j 0 :=
    fun j hj => cp2_spec hCp fcar (by rw [lc]; exact hj)
  set cpL := cpIns2 (preT.1.carried.map (S2.gkOut ⟨p1, [], tplOf preT.2⟩)) with hcpL
  have hp3 : (p2.adv (loop [] (tplOf cpL) p2).2).k = p2.k + 2 * (57 + P) := by
    rw [gk_adv_loop, ltw_ones (cpIns2_w _)]
    simp [cpL, cpIns2_length, lc]
  have hACp : SegsAssert M p2 (loop [] (tplOf cpL) p2).2 :=
    segsAssert_loop_iff.mpr fun _ _ => noA_cpIns2 _ _ _
  generalize p2.adv (loop [] (tplOf cpL) p2).2 = p3 at hp3 hLay hS1 hS2 hS3 hF1 hRot hF2 ⊢
  -- the first claim, carried
  have hlp : (lanePtK2 (fun m => fe2At sig (8 * m)) qs).length = 5 := by simp [lanePtK2]
  have houtL : outV.length = 25 := by rw [← houtV]; simp
  have hfl : ∀ i < 7, ((List.range 7).map fun i =>
      (eqKernelF (lanePtK2 (fun m => fe2At sig (8 * m)) qs)).getD 0 0 * gx ^ iotaPos i).getD i 0 =
      (eqKernelF (lanePtK2 (fun m => fe2At sig (8 * m)) qs)).getD 0 0 * gx ^ iotaPos i := by
    intro i hi; simp [List.getD_eq_getElem?_getD, hi]
  have hr := rep_firstK2 P (fe2At sig (8 * qs)) (fe2At sig (8 * (qs + 59))) hinstL hlp houtL hfl
  have htake : instV.take 4 = (List.range 4).map fun i => (inst i).val M := by
    rw [← hinstV, take_range_map2 _ (by (clear * -; omega))]
  have hdrop : instV.drop 4 = (List.range P).map fun i => (inst (4 + i)).val M := by
    rw [← hinstV, drop_range_map2, show P + 4 - 4 = P by (clear * -; omega)]
  rw [htake, hdrop] at hr
  set C0 := firstClaimSF LeanVM.Protocol.KeccakGkr.Shape.v1 instV [fe2At sig (8 * qs)]
    (lanePtK2 (fun m => fe2At sig (8 * m)) qs) outV (fe2At sig (8 * (qs + 59))) with hC0
  have h0 : Rep2 P (layCv2 M ⟨p3, [4], layTpl2 P (qs + 61) p.k⟩ (57 + P) (cbOf2 P) 0) C0 true :=
    rep2_congr hr fun j hj => by
      show _ = (⟨M.k (p3.k - 2 * (57 + P) + 2 * j), M.k (p3.k - 2 * (57 + P) + 2 * j + 1)⟩ : FE2)
      rw [hp3, show p2.k + 2 * (57 + P) - 2 * (57 + P) + 2 * j = p2.k + 2 * j by (clear * -; omega), hcopy j hj, ecar]
  -- the layers
  obtain ⟨hrep, hlayA⟩ := layers2_spec (d := 4) (N := 12) (first0 := true) (β := b.val M) (C0 := C0)
    (io := fun k => iotaSF LeanVM.Protocol.KeccakGkr.Shape.v1 (P + 4) (0 + k))
    (rc0 := fun k => keccakRC.getD (gkrDepth * 1 - k - 1) 0) (rc1 := fun k => keccakRC.getD (gkrDepth * 2 - k - 1) 0)
    hP hLay hS (by rw [hqO] at hTq; (clear * - hTq; omega)) (by (clear * -; omega)) (by norm_num) (by norm_num)
    (fun k hk => ⟨rc_mem (by simp only [gkrDepth]; (clear * -; omega)), rc_mem (by simp only [gkrDepth]; (clear * -; omega))⟩)
    (fun k hk C hC => by rw [Nat.zero_add]; exact iotaSF_v1 hC)
    (fun jf hjf => ks_cst hc hjf)
    (fun jf hjf => by
      rw [hc _ (by (clear * - hjf; omega)), if_pos (by (clear * -; omega)), show (16 * jf + 15) / 16 = jf by (clear * -; omega)])
    (by (clear * - hp3; omega)) h0
  simp only [gk_loop_fst] at hrep
  generalize p3.adv (loop [4] (layTpl2 P (qs + 61) p.k) p3).2 = p4 at hS1 hS2 hS3 hF1 hRot hF2 ⊢
  -- the committed open's sumcheck
  have hcl1 : (preT.1.com.gkCell ⟨p1, [], tplOf preT.2⟩).val M = fe2At sig (8 * (qs + 59)) := by
    rw [ec]; exact laneC2_val (a := qs + 59) hS (by rw [hqO] at hTq; (clear * - hTq; omega))
  have hqO5 : 5 ≤ gkrQO2 P qs := by rw [hqO]; (clear * -; omega)
  obtain ⟨hc1, hv1⟩ := sc2_lists (D := 3) (R := 6) gC2 (by norm_num) (by norm_num) hqO5 hS (by (clear * - hTq; omega)) hS1
  rw [hcl1] at hc1 hv1
  generalize p4.adv (scGadget2 3 2 (gkrQO2 P qs) (preT.1.com.gkCell ⟨p1, [], tplOf preT.2⟩) p4).2 = p5
    at hS2 hS3 hF1 hRot hF2 ⊢
  generalize (scGadget2 3 2 (gkrQO2 P qs) (preT.1.com.gkCell ⟨p1, [], tplOf preT.2⟩) p4).1 = sc1
    at hc1 hv1 hS2 hS3 hF1 hRot hF2 ⊢
  -- the instance sumcheck
  have hcl2 : (lastC2 P ⟨p3, [4], layTpl2 P (qs + 61) p.k⟩ 0).val M =
      (chain2 (fe2At sig) (feAt sig) (fun k => iotaSF LeanVM.Protocol.KeccakGkr.Shape.v1 (P + 4) (0 + k)) C0
        (8 * (qs + 61) - 40) (8 * (lay02 P).str2) 12).value := hrep.value
  obtain ⟨hc2, hv2⟩ := sc2_lists (D := 2) (R := 4) gC2 (by norm_num) (by norm_num) (by (clear * -; omega)) hS (by (clear * - hTq; omega)) hS2
  rw [hcl2] at hc2 hv2
  generalize p5.adv (scGadget2 2 2 (gkrQO2 P qs + 86) (lastC2 P ⟨p3, [4], layTpl2 P (qs + 61) p.k⟩ 0) p5).2 = p6
    at hS3 hF1 hRot hF2 ⊢
  generalize (scGadget2 2 2 (gkrQO2 P qs + 86) (lastC2 P ⟨p3, [4], layTpl2 P (qs + 61) p.k⟩ 0) p5).1 = sc2
    at hc2 hv2 hS3 hF1 hRot hF2 ⊢
  -- the input open's sumcheck
  obtain ⟨hc3, hv3⟩ := sc2_lists (D := 3) (R := 6) gC2 (by norm_num) (by norm_num) (by (clear * -; omega)) hS (by (clear * - hTq; omega)) hS3
  rw [show 4 - 1 = 3 from rfl] at hv2
  rw [hv2] at hc3 hv3
  generalize p6.adv (scGadget2 3 2 (gkrQO2 P qs + 142) (scClaim2 sc2 2 3) p6).2 = p7 at hF1 hRot hF2 ⊢
  generalize (scGadget2 3 2 (gkrQO2 P qs + 142) (scClaim2 sc2 2 3) p6).1 = sc3 at hc3 hv3 hF1 hRot hF2 ⊢
  -- the first opening block
  have hrep' := hrep
  rw [show 12 - 1 = 11 from rfl] at hrep'
  set lay : LoopOut := ⟨p3, [4], layTpl2 P (qs + 61) p.k⟩ with hlay
  set cv : Nat → FE2 := fun j => (lay.cell2 (cbOf2 P + 2 * j) 11).val M with hcv
  have hlc : ∀ j, (lastC2 P lay j).val M = cv j := fun j => rfl
  set G := fin1TB2 (gkrQO2 P qs) (gkS b) (List.map C2.s2 ((List.range 6).map fun i => scChal2 2 (gkrQO2 P qs) i))
    (List.map C2.s2 ((List.range 6).map fun i => scChal2 2 (gkrQO2 P qs + 142) i))
    ((List.range 6).map fun i => (lastC2 P lay (44 + P + i)).s2)
    (preT.1.seg.gkOut ⟨p1, [], tplOf preT.2⟩) (scClaim2 sc1 2 5).s2
    (preT.1.lanes.map (S2.gkOut ⟨p1, [], tplOf preT.2⟩)) 0 with hG
  have hll : preT.1.lanes.length = 32 := by
    have := congrArg List.length el; simp only [vals2, List.length_map, eqKernelF_length, lanePtK2, List.length_range] at this
    simpa using this
  have hf10 := thold2_of_loop hF1 (jf := 0) (by simp)
  rw [gk_loop_fst] at hf10
  obtain ⟨hcp, ez, fz, hwd, e3, f3, ea, fa, hA1⟩ := fin1TB2_spec (by simp [hll]) (by simp) hf10
  have hslc : ∀ t < 256, M.k (p7.k + t) = kAt sig (8 * (gkrQO2 P qs + 226 + 2 * (t / 2 % 64) + t % 2)) := by
    intro t ht
    have h1 := hcp t ht
    rw [Nat.zero_add, fin1_cells M p7 _ _ _ _ _ _ _ _ ht, gk_iterXv_fix] at h1
    rw [fe_ofK_inj h1, hS _ (by rw [hqO] at hTq ⊢; (clear * - hTq; omega))]
  generalize p7.adv (loop [] (tplOf G.2) p7).2 = p8 at hRot hF2 ⊢
  -- the carried values of the final claim
  have hcvA : vals2 (iterXv M ⟨p7, [], tplOf G.2⟩ 0) (iterF M ⟨p7, [], tplOf G.2⟩ 0)
      ((List.range 6).map fun i => (lastC2 P lay (44 + P + i)).s2) = repA2 P cv := by
    simp only [vals2, List.map_map, repA2]
    refine List.map_congr_left fun i _ => ?_
    rw [Function.comp_apply, s2_valF_s2]
    rfl
  -- the slices as `V` reads them
  set slV : List FE2 := (List.range 64).map fun k => fe2At sig (8 * (gkrQO2 P qs + 226 + 2 * k)) with hslV
  have hslP : ∀ w < 64, ∀ i < 64, (⟨M.k (p7.k + 2 * w + 2 * i), M.k (p7.k + 2 * w + 1 + 2 * i)⟩ : FE2) =
      slV.getD ((w + i) % 64) 0 := by
    intro w hw i hi
    rw [show p7.k + 2 * w + 2 * i = p7.k + (2 * (w + i)) by ring,
      show p7.k + 2 * w + 1 + 2 * i = p7.k + (2 * (w + i) + 1) by ring, hslc _ (by (clear * - hw hi; omega)), hslc _ (by (clear * - hw hi; omega)),
      hslV, List.getD_eq_getElem _ _ (by simp; (clear * -; omega)), List.getElem_map, List.getElem_range,
      show 2 * (w + i) / 2 % 64 = (w + i) % 64 by (clear * -; omega), show 2 * (w + i) % 2 = 0 by (clear * -; omega),
      show (2 * (w + i) + 1) / 2 % 64 = (w + i) % 64 by (clear * -; omega), show (2 * (w + i) + 1) % 2 = 1 by (clear * -; omega)]
    show (⟨kAt sig _, kAt sig _⟩ : FE2) = ⟨kAt sig _, kAt sig _⟩
    rw [Nat.add_zero, show 8 * (gkrQO2 P qs + 226 + 2 * ((w + i) % 64) + 1) =
      8 * (gkrQO2 P qs + 226 + 2 * ((w + i) % 64)) + 8 by ring]
  -- the rotation block
  set rotT := tplOf (rotIns2 (G.1.ea.map (S2.gkOut ⟨p7, [], tplOf G.2⟩)) p7.k (G.1.z.gkOut ⟨p7, [], tplOf G.2⟩))
    with hrotT
  have hea64 : G.1.ea.length = 64 := by
    have := congrArg List.length ea
    simp only [vals2, List.length_map, eqKernelF_length, List.length_range] at this
    rw [hG]; simpa [List.map_map] using this
  have hrot : ∀ i < 64, (⟨(iterF M ⟨p8, [6], rotT⟩ i 126).c₀, (iterF M ⟨p8, [6], rotT⟩ i 127).c₀⟩ : FE2) =
      ((List.range 64).map fun w => eqAtG (repA2 P cv) w * slV.getD ((w + i) % 64) 0).sum := by
    intro i hi
    have := rot2_spec hRot (A := fun w => eqAtG (repA2 P cv) w)
      (fun w hw jf _ => by
        rw [getD_map_default (S2.gkOut _) rfl, gkOut2_val M _ _ jf _ (fa _ (by
          rw [List.getD_eq_getElem _ _ (by (clear * - hea64 hw; omega))]; exact List.getElem_mem _)), getD_valF2 _ (by (clear * - hea64 hw; omega)), ea, hcvA]
        rfl)
      (fun jf _ => by rw [gkOut2_val M _ _ jf _ fz, ez]) hi
    rw [gk_loop_fst] at this
    rw [this]
    refine congrArg List.sum (List.map_congr_left fun w hw => ?_)
    rw [hslP w (List.mem_range.mp hw) i hi]
  have hR : ∀ s < 64, ((⟨p8, [6], rotT⟩ : LoopOut).cell2 126 ((64 - s) % 64)).val M =
      rotSumG (fun z => slV.getD z 0) (eqAtG (repA2 P cv)) s := by
    intro s hs
    show (⟨(iterF M ⟨p8, [6], rotT⟩ ((64 - s) % 64) 126).c₀, (iterF M ⟨p8, [6], rotT⟩ ((64 - s) % 64) 127).c₀⟩ : FE2) = _
    rw [hrot _ (Nat.mod_lt _ (by (clear * -; omega))), rot_reindex2 (eqAtG (repA2 P cv)) (fun z => slV.getD z 0) hs]
    rfl
  generalize p8.adv (loop [6] rotT p8).2 = p9 at hF2 ⊢
  -- `V`'s run in the gadget's coordinates
  rw [show (6 : Nat) - 1 = 5 from rfl] at hv1 hv3
  have hp1 : 8 * qs - 48 + 496 + 12 * (2440 + 112 * (P + 1)) = 8 * gkrQO2 P qs - 40 := by rw [hqO, hstr]; (clear * - hq; omega)
  set chainC := chain2 (fe2At sig) (feAt sig) (fun k => iotaSF LeanVM.Protocol.KeccakGkr.Shape.v1 (P + 4) (0 + k)) C0
    (8 * (qs + 61) - 40) (8 * (lay02 P).str2) 12 with hchainC
  set S1 := scSpec2 (fe2At sig) (feAt sig) gC2 3 (8 * gkrQO2 P qs - 40) (fe2At sig (8 * (qs + 59))) 6 with hS1d
  set LV := scSpec2 (fe2At sig) (feAt sig) gC2 3 (8 * (gkrQO2 P qs + 86) - 40) chainC.value 4 with hLVd
  set S3 := scSpec2 (fe2At sig) (feAt sig) gC2 3 (8 * (gkrQO2 P qs + 142) - 40) LV.2.1 6 with hS3d
  have hVr : vkSpec2 (fe2At sig) (feAt sig) P instV outV (8 * qs - 48) =
      ⟨([(instV.take 4 ++ instV.drop 4 ++ S1.1, fe2At sig (8 * (gkrQO2 P qs + 84)))],
        LV.1 ++ chainC.point.take (P + 4 - 4) ++ S3.1, scalars2 (fe2At sig) (8 * (gkrQO2 P qs + 226)) 64),
        (foldRowsF S1.1 (slotWeightsF (P + 4) C0 1 1)).headD 0 * fe2At sig (8 * (gkrQO2 P qs + 84)) == S1.2.1,
        multilinearEvalF chainC.mu LV.1 *
          dotF (foldRowsF S3.1 (slotWeightsF (P + 4) chainC 0 2)) (scalars2 (fe2At sig) (8 * (gkrQO2 P qs + 226)) 64) ==
          S3.2.1,
        S1.2.2 && LV.2.2 && S3.2.2⟩ := by
    simp only [vkSpec2]
    rw [hp1, seg_eq_sampsG sig hq, lanes_eq_sampsG sig hq, show 8 * qs - 48 + 520 = 8 * (qs + 59) by (clear * - hqO hp1; omega),
      show 8 * qs - 48 + 496 = 8 * (qs + 61) - 40 by (clear * - hqO hp1; omega),
      show 2440 + 112 * (P + 1) = 8 * (lay02 P).str2 by rw [hstr]; ring,
      show 8 * gkrQO2 P qs - 40 + 712 = 8 * (gkrQO2 P qs + 84) by (clear * - hp1; omega),
      show 8 * gkrQO2 P qs - 40 + 688 = 8 * (gkrQO2 P qs + 86) - 40 by (clear * - hp1; omega),
      show 8 * gkrQO2 P qs - 40 + 1136 = 8 * (gkrQO2 P qs + 142) - 40 by (clear * - hp1; omega),
      show 8 * gkrQO2 P qs - 40 + 1848 = 8 * (gkrQO2 P qs + 226) by (clear * - hp1; omega)]
  have hslices : scalars2 (fe2At sig) (8 * (gkrQO2 P qs + 226)) 64 = slV := by
    simp only [scalars2, hslV]
    refine List.map_congr_left fun k _ => ?_
    rw [show 8 * (gkrQO2 P qs + 226) + 16 * k = 8 * (gkrQO2 P qs + 226 + 2 * k) by ring]
  have hdrop3 : chainC.point.drop (P + 4 - 4) = [cv (18 + P)] := by
    rw [← hrep'.point, show P + 4 - 4 = P by (clear * -; omega), drop_range_map2, show P + 1 - P = 1 by (clear * -; omega)]
    rfl
  refine ⟨?_, fun hb => ?_⟩
  · -- the outputs
    rw [hVr]
    simp only [Prod.mk.injEq, List.cons.injEq, and_true, List.map_append, List.map_map, Function.comp_def]
    refine ⟨⟨?_, ?_⟩, ?_, ?_⟩
    · rw [List.take_append_drop, hinstV, hc1]
    · exact laneC2_val hS (by (clear * - hTq; omega))
    · rw [hc2, hc3, ← hrep'.point, show P + 4 - 4 = P by (clear * -; omega), take_range_map2 _ (by (clear * -; omega) : P ≤ P + 1)]
      simp only [hlc]
    · rw [hslices, hslV]
      refine List.map_congr_left fun k hk => ?_
      rw [laneC2_val hS (by have := List.mem_range.mp hk; (clear * - hTq this; omega))]
  · -- the assertions
    have e0 : ∀ (q : Ptr) (ins : List Ins), (∀ jf < 2 ^ ([] : List Nat).sum,
        TAssert (iterXv M (loop [] (tplOf ins) q).1 jf) (iterF M (loop [] (tplOf ins) q).1 jf) ins) ↔
        TAssert (iterXv M ⟨q, [], tplOf ins⟩ 0) (iterF M ⟨q, [], tplOf ins⟩ 0) ins :=
      fun _ _ => ⟨fun h => h 0 (by simp), fun h jf hjf => by rw [show jf = 0 by simpa using hjf]; exact h⟩
    -- the first opening block: `V`'s committed check
    have hs1V : vals2 (iterXv M ⟨p7, [], tplOf G.2⟩ 0) (iterF M ⟨p7, [], tplOf G.2⟩ 0)
        (List.map C2.s2 ((List.range 6).map fun i => scChal2 2 (gkrQO2 P qs) i)) = S1.1 := by
      simp only [vals2, List.map_map, Function.comp_def, s2_valF_s2]; exact hc1
    have hlV : vals2 (iterXv M ⟨p7, [], tplOf G.2⟩ 0) (iterF M ⟨p7, [], tplOf G.2⟩ 0)
        (preT.1.lanes.map (S2.gkOut ⟨p1, [], tplOf preT.2⟩)) = eqKernelF (lanePtK2 (fun m => fe2At sig (8 * m)) qs) := by
      rw [← el]; simp only [vals2, List.map_map]
      exact List.map_congr_left fun x hx => gkOut2_val M _ _ 0 _ (fl x hx)
    have hsgV : (preT.1.seg.gkOut ⟨p1, [], tplOf preT.2⟩).valF (iterXv M ⟨p7, [], tplOf G.2⟩ 0)
        (iterF M ⟨p7, [], tplOf G.2⟩ 0) = fe2At sig (8 * qs) := by
      rw [es]; show lv2 _ [] qs = _; exact lv2_fix hS _ 0 qs (by (clear * - hTq hp1; omega))
    have hwdV : (lane2 (gkrQO2 P qs + 84) []).valF (iterXv M ⟨p7, [], tplOf G.2⟩ 0) (iterF M ⟨p7, [], tplOf G.2⟩ 0) =
        fe2At sig (8 * (gkrQO2 P qs + 84)) := lv2_fix hS _ 0 _ (by (clear * - hTq; omega))
    have hv1V : (scClaim2 sc1 2 5).s2.valF (iterXv M ⟨p7, [], tplOf G.2⟩ 0) (iterF M ⟨p7, [], tplOf G.2⟩ 0) = S1.2.1 := by
      rw [s2_valF_s2]; exact hv1
    have hw1 : C0.weights = firstWG gx (eqKernelF (lanePtK2 (fun m => fe2At sig (8 * m)) qs)) :=
      firstWeightsF_eq _
    have hdrop1 : C0.point.drop (P + 4 - 4) = [fe2At sig (8 * qs)] := by
      show (instV.drop 4 ++ [fe2At sig (8 * qs)]).drop (P + 4 - 4) = _
      rw [show P + 4 - 4 = P by (clear * -; omega)]
      exact List.drop_left' (by rw [List.length_drop, hinstL]; (clear * -; omega))
    have hAf1 : SegsAssert M p7 (loop [] (tplOf G.2) p7).2 ↔
        ((foldRowsF S1.1 (slotWeightsF (P + 4) C0 1 1)).headD 0 * fe2At sig (8 * (gkrQO2 P qs + 84)) == S1.2.1) =
          true := by
      have key : ((List.range 25).map fun l => (eqKernelF S1.1).getD (25 + l) 0 *
          (eqKernelF (lanePtK2 (fun m => fe2At sig (8 * m)) qs)).getD l 0).sum * (1 + fe2At sig (8 * qs)) =
          sumF ((List.range 25).map fun l => eqAtG S1.1 (25 + l) * (eqKernelF [fe2At sig (8 * qs)]).getD 0 0 *
            (eqKernelF (lanePtK2 (fun m => fe2At sig (8 * m)) qs)).getD l 0) := by
        rw [sumF_map_range, ← sumF_eq_sum, sumF_map_range, Finset.sum_mul]
        refine Finset.sum_congr rfl fun l _ => ?_
        rw [show (eqKernelF [fe2At sig (8 * qs)]).getD 0 0 = 1 * (1 + fe2At sig (8 * qs)) from rfl, eqAtG]
        ring
      rw [segsAssert_loop_iff, e0, hA1 (by rw [gkS_valF]; exact hb), hs1V, hlV, hsgV, hwdV, hv1V, fe2_beq_iff,
        fe2_add_eq_zero, headD_getD2,
        open_committed_firstG gx (P + 4) C0 _ hw1 (by rw [hS1d]; exact scSpec2_length _ _ _ _ _ _ _), hdrop1, key]
    -- the input check block: `V`'s input check
    have hf20 := thold2_of_loop hF2 (jf := 0) (by simp)
    rw [gk_loop_fst] at hf20
    have he3L : G.1.e3.length = 64 := by
      have := congrArg List.length e3
      simp only [vals2, List.length_map, eqKernelF_length, List.length_range, Nat.reducePow] at this
      exact this
    have hzV : ∀ (o : LoopOut) (V : Nat → FE), (G.1.z.gkOut ⟨p7, [], tplOf G.2⟩).valF (iterXv M o 0) V = 0 :=
      fun o V => by rw [gkOut2_val M _ _ 0 _ fz, ez]
    have hmuV : ∀ (o : LoopOut) (V : Nat → FE),
        vals2 (iterXv M o 0) V ((List.range 16).map fun i => (lastC2 P lay (1 + i)).s2) = chainC.mu := by
      intro o V; rw [← hrep'.mu]; simp only [vals2, List.map_map, Function.comp_def, s2_valF_s2, hlc]
    have hlowV : ∀ (o : LoopOut) (V : Nat → FE),
        vals2 (iterXv M o 0) V (((List.range 4).map fun i => scChal2 2 (gkrQO2 P qs + 86) i).map C2.s2) = LV.1 := by
      intro o V; simp only [vals2, List.map_map, Function.comp_def, s2_valF_s2]; exact hc2
    have he3V : ∀ (o : LoopOut) (V : Nat → FE),
        vals2 (iterXv M o 0) V (G.1.e3.map (S2.gkOut ⟨p7, [], tplOf G.2⟩)) = eqKernelF S3.1 := by
      intro o V
      have h3 : vals2 (iterXv M ⟨p7, [], tplOf G.2⟩ 0) (iterF M ⟨p7, [], tplOf G.2⟩ 0)
          (List.map C2.s2 ((List.range 6).map fun i => scChal2 2 (gkrQO2 P qs + 142) i)) = S3.1 := by
        simp only [vals2, List.map_map, Function.comp_def, s2_valF_s2]; exact hc3
      rw [← h3, ← e3]; simp only [vals2, List.map_map]
      exact List.map_congr_left fun x hx => gkOut2_val M _ _ 0 _ (f3 x hx)
    have hxV : ∀ (o : LoopOut) (V : Nat → FE), (lastC2 P lay (18 + P)).s2.valF (iterXv M o 0) V = cv (18 + P) :=
      fun o V => by rw [s2_valF_s2, hlc]
    have hBV : ∀ (o : LoopOut) (V : Nat → FE),
        vals2 (iterXv M o 0) V ((List.range 25).map fun l => (lastC2 P lay (19 + P + l)).s2) = repB2 P cv := by
      intro o V; simp only [vals2, List.map_map, Function.comp_def, s2_valF_s2, hlc, repB2]
    have hv3V : ∀ (o : LoopOut) (V : Nat → FE), (scClaim2 sc3 2 5).s2.valF (iterXv M o 0) V = S3.2.1 :=
      fun o V => by rw [s2_valF_s2]; exact hv3
    have hRV : ∀ (o : LoopOut) (V : Nat → FE), ∀ s < 64,
        ((⟨p8, [6], rotT⟩ : LoopOut).cell2 126 ((64 - s) % 64)).s2.valF (iterXv M o 0) V =
          rotSumG (fun z => slV.getD z 0) (eqAtG (repA2 P cv)) s :=
      fun o V s hs => by rw [s2_valF_s2]; exact hR s hs
    have hw3 : chainC.weights = linearTransposeF (prodWG (eqAtG (repA2 P cv)) (repB2 P cv)) := by
      rw [hrep'.weights, if_neg Bool.false_ne_true]
    have hdot : dotF (foldRowsF S3.1 (slotWeightsF (P + 4) chainC 0 2)) (scalars2 (fe2At sig) (8 * (gkrQO2 P qs + 226)) 64) =
        ((List.range 25).map fun l => (eqAtG S3.1 (25 + l) * cv (18 + P) + eqAtG S3.1 l * (1 + cv (18 + P))) *
          laneFormF (repB2 P cv) (rotSumG (fun z => slV.getD z 0) (eqAtG (repA2 P cv))) l).sum := by
      rw [hslices, open_input_ltG (P + 4) chainC _ _ hw3 (by rw [hS3d]; exact scSpec2_length _ _ _ _ _ _ _)
        (by simp [hslV]), hdrop3, sum2_lanes2]
    have hAf2 : SegsAssert M p9 (loop [] (tplOf (fin2TB2 (gkS b) (G.1.z.gkOut ⟨p7, [], tplOf G.2⟩)
          ((List.range 25).map fun l => (lastC2 P lay (19 + P + l)).s2)
          (fun s => ((⟨p8, [6], rotT⟩ : LoopOut).cell2 126 ((64 - s) % 64)).s2)
          (G.1.e3.map (S2.gkOut ⟨p7, [], tplOf G.2⟩)) (lastC2 P lay (18 + P)).s2
          ((List.range 16).map fun i => (lastC2 P lay (1 + i)).s2)
          (((List.range 4).map fun i => scChal2 2 (gkrQO2 P qs + 86) i).map C2.s2) (scClaim2 sc3 2 5).s2 0).2) p9).2 ↔
        (multilinearEvalF chainC.mu LV.1 *
          dotF (foldRowsF S3.1 (slotWeightsF (P + 4) chainC 0 2)) (scalars2 (fe2At sig) (8 * (gkrQO2 P qs + 226)) 64) ==
          S3.2.1) = true := by
      rw [segsAssert_loop_iff, e0, fin2TB2_spec (hzV _ _) (by simp) (by simp [he3L]) hf20 (by rw [gkS_valF]; exact hb),
        hmuV, hlowV, he3V, hxV, hBV, hv3V, fe2_beq_iff, fe2_add_eq_zero, hdot]
      simp only [laneFormF_congr (repB2 P cv) (hRV _ _), eqAtG]
    have hArot : SegsAssert M p8 (loop [6] rotT p8).2 :=
      segsAssert_loop_iff.mpr fun _ _ => tassert_noA (gnoA_rotIns2 _ _ _)
    rw [hVr]
    dsimp only
    constructor
    · rintro ⟨-, -, -, -, hL, -, -, -, h1, -, h2, -⟩
      exact ⟨hAf1.mp h1, hAf2.mp h2, (hlayA hb).mp hL⟩
    · rintro ⟨h1, h2, hL⟩
      exact ⟨trivial, hAK, hAPre, hACp, (hlayA hb).mpr hL, sc2_asserts _ _ _ _ _ _, sc2_asserts _ _ _ _ _ _,
        sc2_asserts _ _ _ _ _ _, hAf1.mpr h1, hArot, hAf2.mpr h2, trivial⟩

/-- The proof-of-work flag of `V`'s three opening sumchecks, per round. -/
theorem vkSpec2_pwO (v : Nat → FE2) (va : Nat → FE) (P : Nat) (inst output : List FE2) (p : Nat) :
    (vkSpec2 v va P inst output p).pwO = true ↔
      ((∀ i < 6, powOKR gC2 (va (ansAt2 (p + 496 + 12 * (2440 + 112 * (P + 1)) + i * roundLen2 3) 3)) = true) ∧
        ∀ i < 4, powOKR gC2 (va (ansAt2 (p + 496 + 12 * (2440 + 112 * (P + 1)) + 688 + i * roundLen2 3) 3)) = true) ∧
      ∀ i < 6, powOKR gC2 (va (ansAt2 (p + 496 + 12 * (2440 + 112 * (P + 1)) + 1136 + i * roundLen2 3) 3)) = true := by
  show ((scSpec2 v va gC2 3 _ _ 6).2.2 && (scSpec2 v va gC2 3 _ _ 4).2.2 && (scSpec2 v va gC2 3 _ _ 6).2.2) = true ↔ _
  rw [Bool.and_eq_true, Bool.and_eq_true, scSpec2_pw, scSpec2_pw, scSpec2_pw]

/-- **`V`'s `KS` GKR, replayed by the `KS` gadget** (`verifyKeccakD (P + 4)` from the segment challenge's entry
`8 qs − 48`): the gadget's output cells are `V`'s result, `V`'s position after is the gadget's last lane (`gkrEnd2`),
and with the gate `1` `V`'s flag after holds iff the flag before does, every ground answer of `KS` passes its proof
of work (`gkrChals2`), and every assertion of the gadget holds. -/
theorem gkr_spec2 {c : Ctx} {M : Mem} {p : Ptr} {P qs : Nat} {inst out : Nat → C2} {b : Cell}
    {sig : ByteArray} {T : Nat} (hP : layOk2 P = true) (hq : 6 ≤ qs) (hS : Streamed M sig T)
    (hT : gkrEnd2 P qs ≤ T) (h : SegsHold c M p (gkrGadgetE2 P qs inst out b p).2) (s : RS)
    (hs : s.ent + s.msg = 8 * qs - 48) :
    ([((gkrGadgetE2 P qs inst out b p).1.wordPoint.map (C2.val M), (gkrGadgetE2 P qs inst out b p).1.word.val M)],
      (gkrGadgetE2 P qs inst out b p).1.slicePoint.map (C2.val M),
      (gkrGadgetE2 P qs inst out b p).1.slices.map (C2.val M)) =
      (verifyKeccakD (P + 4) ((List.range (P + 4)).map fun i => (inst i).val M)
        ((List.range 25).map fun l => (out l).val M) sig s).1 ∧
    (verifyKeccakD (P + 4) ((List.range (P + 4)).map fun i => (inst i).val M)
        ((List.range 25).map fun l => (out l).val M) sig s).2.ent +
      (verifyKeccakD (P + 4) ((List.range (P + 4)).map fun i => (inst i).val M)
        ((List.range 25).map fun l => (out l).val M) sig s).2.msg = 8 * gkrEnd2 P qs - 40 ∧
    (b.val M = 1 →
      ((verifyKeccakD (P + 4) ((List.range (P + 4)).map fun i => (inst i).val M)
        ((List.range 25).map fun l => (out l).val M) sig s).2.ok = true ↔
        s.ok = true ∧ PowOkV (feAt sig) (gkrChals2 P qs) ∧ SegsAssert M p (gkrGadgetE2 P qs inst out b p).2)) := by
  obtain ⟨hres, hA⟩ := gkr_core2 hP hq hS hT h
  generalize hinstV : ((List.range (P + 4)).map fun i => (inst i).val M) = instV at hres hA ⊢
  generalize houtV : ((List.range 25).map fun l => (out l).val M) = outV at hres hA ⊢
  have hinstL : instV.length = P + 4 := by rw [← hinstV]; simp
  have hstr : (lay02 P).str2 = 305 + 14 * (P + 1) := rfl
  have hqO : gkrQO2 P qs = qs + 61 + 12 * (lay02 P).str2 := rfl
  obtain ⟨r1, r2, r3⟩ := verifyKeccakD_run sig P instV outV hinstL s
  rw [hs] at r1 r2 r3
  refine ⟨by rw [r1]; exact hres, by rw [r2, gkrEnd2, hqO, hstr]; (clear * - hq; omega), fun hb => ?_⟩
  have hCpt := firstClaimSF_v1_point_length (fe2At sig (8 * qs - 48 + 520)) hinstL (sampsG_length (feAt sig) 1 (8 * qs - 48))
    (lanes := sampsG (feAt sig) (8 * qs - 48 + 80) 5) (out := outV)
  have hSL : PowOkV (feAt sig) ((List.range 6).map fun k => (qs + 10 * k, 1)) ↔
      (∀ k < 5, powOKR gC1 (feAt sig (8 * qs - 48 + 80 + 48 + 80 * k)) = true) ∧
        ∀ k < 1, powOKR gC1 (feAt sig (8 * qs - 48 + 48 + 80 * k)) = true := by
    rw [powOkV_map]
    constructor
    · intro h
      refine ⟨fun k hk => ?_, fun k hk => ?_⟩
      · rw [show 8 * qs - 48 + 80 + 48 + 80 * k = 8 * (qs + 10 * (k + 1)) by (clear * - hq; omega)]; exact h (k + 1) (by (clear * - hk; omega))
      · rw [show 8 * qs - 48 + 48 + 80 * k = 8 * (qs + 10 * k) by (clear * - hq; omega)]; exact h k (by (clear * - hk; omega))
    · rintro ⟨h1, h0⟩ k hk
      rcases k with _ | k
      · have := h0 0 (by (clear * -; omega))
        rw [show 8 * qs - 48 + 48 + 80 * 0 = 8 * (qs + 10 * 0) by (clear * - hq; omega)] at this; exact this
      · have := h1 k (by (clear * - hk; omega))
        rw [show 8 * qs - 48 + 80 + 48 + 80 * k = 8 * (qs + 10 * (k + 1)) by (clear * - hq; omega)] at this; exact this
  have hLP : PowOkV (feAt sig) ((List.range 12).flatMap fun L => layerChals2 P (qs + 61 + L * (lay02 P).str2)) ↔
      ∀ k < 12, (lay2At (fe2At sig) (feAt sig) (fun k => iotaSF LeanVM.Protocol.KeccakGkr.Shape.v1 (P + 4) (0 + k))
        (firstClaimSF LeanVM.Protocol.KeccakGkr.Shape.v1 instV (sampsG (feAt sig) (8 * qs - 48) 1)
          (sampsG (feAt sig) (8 * qs - 48 + 80) 5) outV (fe2At sig (8 * qs - 48 + 520)))
        (8 * qs - 48 + 496) (2440 + 112 * (P + 1)) k).pw = true := by
    rw [powOkV_flatMap]
    refine forall₂_congr fun k _ => ?_
    unfold lay2At
    refine (layer_pw _ _ _ (by rw [chain2_length, hCpt]) ?_).symm
    rw [show k * (2440 + 112 * (P + 1)) = 8 * (k * (lay02 P).str2) by rw [hstr]; ring]
    (clear * - hq; omega)
  have hO : ∀ (o n : Nat), 5 ≤ qs + o →
      (PowOkV (feAt sig) ((List.range n).map fun i => (gkrQO2 P qs + o + 14 * i + 5, 2)) ↔
        ∀ i < n, powOKR gC2 (feAt sig (ansAt2 (8 * qs - 48 + 496 + 12 * (2440 + 112 * (P + 1)) + 8 * o +
          i * roundLen2 3) 3)) = true) := by
    intro o n _
    rw [powOkV_map]
    refine forall₂_congr fun i _ => ?_
    rw [show ansAt2 (8 * qs - 48 + 496 + 12 * (2440 + 112 * (P + 1)) + 8 * o + i * roundLen2 3) 3 =
      8 * (gkrQO2 P qs + o + 14 * i + 5) by simp only [ansAt2, roundLen2]; rw [hqO, hstr]; (clear * - hq; omega)]
  have hO1 := hO 0 6 (by (clear * - hq; omega))
  have hO2 := hO 86 4 (by (clear * -; omega))
  have hO3 := hO 142 6 (by (clear * -; omega))
  simp only [Nat.add_zero, Nat.mul_zero, show 8 * 86 = 688 from rfl, show 8 * 142 = 1136 from rfl] at hO1 hO2 hO3
  rw [r3]
  unfold vkOk2
  simp only [Bool.and_eq_true]
  rw [vkSpec2_pwO, chainOk2_iff, powsG_iff, powsG_iff, hA hb]
  unfold gkrChals2
  rw [powOkV_append, powOkV_append, powOkV_append, powOkV_append, hSL, hLP, hO1, hO2, hO3]
  constructor
  · rintro ⟨⟨⟨⟨⟨⟨hk1, hk2⟩, ⟨hq1, hq2⟩, hq3⟩, hch⟩, hlan⟩, hseg⟩, hok⟩
    exact ⟨hok, ⟨⟨⟨⟨⟨hlan, hseg⟩, fun k hk => (hch k hk).2.2⟩, hq1⟩, hq2⟩, hq3⟩, hk1, hk2,
      fun k hk => ⟨(hch k hk).1, (hch k hk).2.1⟩⟩
  · rintro ⟨hok, ⟨⟨⟨⟨⟨hlan, hseg⟩, hlp⟩, hq1⟩, hq2⟩, hq3⟩, hk1, hk2, hlay⟩
    exact ⟨⟨⟨⟨⟨⟨hk1, hk2⟩, ⟨hq1, hq2⟩, hq3⟩, fun k hk => ⟨(hlay k hk).1, (hlay k hk).2, hlp k hk⟩⟩, hlan⟩, hseg⟩,
      hok⟩

/-- **The `KS` GKR as a `PhaseAt` fact** (roll 11's HAR form): with the gadget's rows and assertions holding, the
gate `1` and every ground answer's proof of work passing, `V`'s `verifyKeccakD (P + 4)` on the cells' values runs
from `8 qs − 48` to `8 gkrEnd2 − 40`, stays ok, and returns the gadget's output cells' values. -/
theorem gkr_phase2 {c : Ctx} {M : Mem} {p : Ptr} {P qs : Nat} {inst out : Nat → C2} {b : Cell}
    {sig : ByteArray} {T : Nat} (hP : layOk2 P = true) (hq : 6 ≤ qs) (hS : Streamed M sig T)
    (hT : gkrEnd2 P qs ≤ T) (hh : SegsHold c M p (gkrGadgetE2 P qs inst out b p).2)
    (ha : SegsAssert M p (gkrGadgetE2 P qs inst out b p).2) (hb : b.val M = 1)
    (hpow : PowOkV (feAt sig) (gkrChals2 P qs)) :
    Lvm.Har.PhaseAt (verifyKeccakD (P + 4) ((List.range (P + 4)).map fun i => (inst i).val M)
        ((List.range 25).map fun l => (out l).val M)) sig (8 * qs - 48) (8 * gkrEnd2 P qs - 40)
      ([((gkrGadgetE2 P qs inst out b p).1.wordPoint.map (C2.val M), (gkrGadgetE2 P qs inst out b p).1.word.val M)],
        (gkrGadgetE2 P qs inst out b p).1.slicePoint.map (C2.val M),
        (gkrGadgetE2 P qs inst out b p).1.slices.map (C2.val M)) :=
  fun s hs hok =>
    ⟨((gkr_spec2 hP hq hS hT hh s hs).1).symm, ((gkr_spec2 hP hq hS hT hh s hs).2.2 hb).mpr ⟨hok, hpow, ha⟩,
      (gkr_spec2 hP hq hS hT hh s hs).2.1⟩

end Lvm.Q1
