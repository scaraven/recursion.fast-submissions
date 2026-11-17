-- New for lvm2 MP-B cap pruning (CAP-C2, 2026-11-17): `F`'s levels on the S2GB stream (`whirLevelsB`, the text of
-- `whirLevels` reading the next level's sent cap `2^capSendBits` and skipping the level's heap entries) and its
-- one-level run lemmas (`whirLevels_step`'s, `whirLevels_final`'s twins on `lvLanes … (some p)`).
import LvmQAsmArith2Whir
import LvmS2GBV
import LvmS2GBInstC

/-!
# `F`'s levels at S2GB

* **`whirLevelsB p`**: `whirLevels` with the next cap of `2^capSendBits` nodes and `heapQ` heap node entries (104 B)
  after each level's openings; `whirLevelsFB_eq`: `whirLevelsFB p = whirLevelsB p` (`inducedWeightK_eq`).
* **`whirLevels_stepB`**, **`whirLevels_finalB`**: one level of `whirLevelsB p` from position `8V`, explicitly, at the
  lanes `lvLanes … (some p)`.
-/

set_option autoImplicit false

namespace Lvm

open DM Lvm.E2V

/-- **`whirLevels` on the S2GB stream** (see the module doc). -/
def whirLevelsB (p : Params) (logN laneFolds : Nat) (evaluateBasis : List FE → FE) (direct : Bool) (g : Nat)
    (ood : Bool) : List Level → WhirState → DM Unit
  | [], _ => require false
  | L :: rest, s => do
    let (s, levelFolds) ← foldRounds L.fold s []
    let messageLog := logN - s.folds.length
    let residual ← match rest with
      | [] => readEs (2 ^ messageLog)
      | N :: _ => do skip (nodeBytes * 2 ^ p.capSendBits N.level N.cap); pure []
    let oodClaims ← match rest with
      | [] => pure []
      | _ :: _ => oodStep ood messageLog
    grindPreR g
    powCheckR g
    let queries ← positionsR L
    let lam ← sampleE
    let queryWeights := powers lam queries.length
    let rowOffs ← openingR L
    skipEntries (p.heapQ L.level L.cap)
    let sig ← read
    let eq := eqKernelA levelFolds
    let folds := rowOffs.map fun o =>
      if L.level = 0 then foldRow0 sig eq o (L.row / 8) else foldRowE sig eq o (2 ^ L.fold)
    let enforced := dot queryWeights folds
    let intro ← sumcheckRoundPoly 3 enforced none
    let s := glue lam s (oodClaims ++ [(intro, fun x => inducedWeight messageLog queries queryWeights x)])
    match rest with
    | [] => do
      if direct then require (directFinal residual L queries folds)
      let (tailFolds, target) ← tailRounds messageLog s.runningQuad
      let point := s.folds ++ tailFolds
      let weight := s.glued.foldl
        (fun weight claim =>
          weight + claim.scalar * claim.weightAt (s.folds.drop claim.foldStart ++ tailFolds))
        (evaluateBasis (point.drop laneFolds ++ point.take laneFolds))
      let terminal := weight * multilinearEval residual tailFolds
      require (terminal == target)
    | _ :: _ => whirLevelsB p logN laneFolds evaluateBasis direct g ood rest s

/-- `whirLevelsFB p` is `whirLevelsB p` (the glued weight `inducedWeightK = inducedWeight`). -/
theorem whirLevelsFB_eq (p : Params) (logN laneFolds : Nat) (evaluateBasis : List FE → FE) (direct : Bool) (g : Nat)
    (ood : Bool) (levels : List Level) (s : WhirState) :
    whirLevelsFB p logN laneFolds evaluateBasis direct g ood levels s =
      whirLevelsB p logN laneFolds evaluateBasis direct g ood levels s := by
  induction levels generalizing s with
  | nil => rfl
  | cons L rest ih =>
    cases rest with
    | nil =>
      rw [whirLevelsFB, whirLevelsB]
      simp only [inducedWeightK_eq]
    | cons N rest' =>
      rw [whirLevelsFB, whirLevelsB]
      simp only [inducedWeightK_eq, ih]

/-- **`verifyWhir` on the S2GB stream** (`whirLevelsB p`). -/
def verifyWhirB (p : Params) (levels : List Level) (logN : Nat) (target : FE) (evaluateBasis : List FE → FE)
    (direct : Bool) (g : Nat) (ood : Bool) : DM Unit := do
  let quad ← sumcheckRoundPoly 3 target none
  whirLevelsB p logN ((levels.head?.map (·.fold)).getD 0) evaluateBasis direct g ood levels ⟨quad, [], []⟩

/-- **`verifyStackedOpening` on the S2GB stream** (`verifyWhirB p`). -/
def verifyStackedOpeningB (p : Params) (levels : List Level) (stackLog : Nat) (claims : List StackClaim)
    (direct : Bool) (g : Nat) (ood : Bool) : DM Unit := do
  let scales := powers (← sampleE) claims.length
  verifyWhirB p levels stackLog (dot scales (claims.map (·.2)))
    (fun point => dot scales (claims.map fun c => c.1 point)) direct g ood

/-- `verifyWhirFB p` is `verifyWhirB p`. -/
theorem verifyWhirFB_eq (p : Params) (levels : List Level) (logN : Nat) (target : FE) (evaluateBasis : List FE → FE)
    (direct : Bool) (g : Nat) (ood : Bool) :
    verifyWhirFB p levels logN target evaluateBasis direct g ood =
      verifyWhirB p levels logN target evaluateBasis direct g ood := by
  unfold verifyWhirFB verifyWhirB
  simp only [whirLevelsFB_eq]

/-- `verifyStackedOpeningGB p` is `verifyStackedOpeningB p` on the groups' flat claims. -/
theorem verifyStackedOpeningGB_eq (p : Params) (levels : List Level) (stackLog : Nat) (gs : List SGroup)
    (direct : Bool) (g : Nat) (ood : Bool) :
    verifyStackedOpeningGB p levels stackLog gs direct g ood =
      verifyStackedOpeningB p levels stackLog (gs.flatMap (·.flat)) direct g ood := by
  unfold verifyStackedOpeningGB verifyStackedOpeningB
  simp only [flatMap_wts, verifyWhirFB_eq]

end Lvm

namespace Lvm.Har

open Lvm Lvm.Loop Lvm.Loop.Build DM

theorem skipEntries_run (n : Nat) (sig : ByteArray) (s : RS) :
    skipEntries n sig s = ((), { s with ent := s.ent + 104 * n }) := rfl

/-! ## One level of `whirLevelsB` -/

theorem whirLevels_stepB (p : Params) (ν lf : Nat) (B : List FE → FE) (g : Nat) (ood : Bool) (L N : Level) (rest : List Level)
    (st : WhirState) (sig : ByteArray) (s : RS) (V : Nat) (hs : pos s = 8 * V) (hrow : L.row % 8 = 0)
    (hκ : L.kappa = ν - (st.folds.length + L.fold)) (hκ1 : 1 ≤ L.kappa) :
    whirLevelsB p ν lf B false g ood (L :: N :: rest) st sig s =
      whirLevelsB p ν lf B false g ood (N :: rest)
        (glue (feAt sig (8 * (lvLanes g ood L (some N) V (some p)).V3 + 40))
          ⟨frQ sig (8 * V) L.fold st.runningQuad, st.folds ++ frC sig (8 * V) L.fold, st.glued⟩
          (oodF sig ood L.kappa (8 * (lvLanes g ood L (some N) V (some p)).Vc) ++
          [([feAt sig (8 * (lvLanes g ood L (some N) V (some p)).V5 + 40),
              Lvm.dot (powers (feAt sig (8 * (lvLanes g ood L (some N) V (some p)).V3 + 40)) L.t)
                ((List.range L.t).map fun j =>
                  if L.level = 0 then foldRow0 sig (eqKernelA (frC sig (8 * V) L.fold))
                    (8 * ((lvLanes g ood L (some N) V (some p)).V4 + 1 + oStr L * j)) (L.row / 8)
                  else foldRowE sig (eqKernelA (frC sig (8 * V) L.fold))
                    (8 * ((lvLanes g ood L (some N) V (some p)).V4 + 1 + oStr L * j)) (2 ^ L.fold)) +
                feAt sig (8 * (lvLanes g ood L (some N) V (some p)).V5 + 64),
              feAt sig (8 * (lvLanes g ood L (some N) V (some p)).V5 + 64)],
            fun x => inducedWeight L.kappa
              (qsAt sig (8 * (lvLanes g ood L (some N) V (some p)).V2) L)
              (powers (feAt sig (8 * (lvLanes g ood L (some N) V (some p)).V3 + 40)) L.t) x)]))
        sig ⟨8 * (lvLanes g ood L (some N) V (some p)).V5, 48, powF sig g (8 * (lvLanes g ood L (some N) V (some p)).Vo) && s.ok⟩ := by
  have hD : 40 + L.row + 104 * L.path = 8 * oStr L := by unfold oStr; (clear * - L ν st s V hrow; omega)
  conv_lhs => rw [whirLevelsB]
  have hfl : ∀ (x : List FE), (st.folds ++ x).length = st.folds.length + x.length := fun x => List.length_append
  have base := fun (h1 : List (List FE × (List FE → FE)) → Prop) => h1
  cases ood <;> rcases Nat.eq_zero_or_pos g with rfl | hg
  all_goals first
    | (have hg0 : g ≠ 0 := Nat.pos_iff_ne_zero.mp hg
       simp only [oodStep_true _ hκ1, oodStep_false, grindPreR_run _ hg0, powCheckR_run _ hg0,
        dm_bind, dm_pure, skip_run, read_run, sampleE_run, srp3_run, foldRounds_fst, foldRounds_pos,
        foldRounds_ok, positionsR_fst, positionsR_pos, positionsR_ok, pos_upd, pos_mk0, pos_mk72, pos_mk24, pos_mk48,
        openingR_mk, skipEntries_run, hs, List.nil_append, hfl, frC_length, qsAt_length, List.map_map, Nat.zero_add, Function.comp_def, ← hκ]
       simp only [lvLanes, oodF, powF, nodeBytes, hg0, Bool.and_true, Bool.true_and, Bool.and_false,
        Option.isSome_some, ↓reduceIte, Bool.false_eq_true, List.nil_append, hD]
       ring_nf)
    | (simp only [oodStep_true _ hκ1, oodStep_false, grindPreR_zero, powCheckR_zero,
        dm_bind, dm_pure, skip_run, read_run, sampleE_run, srp3_run, foldRounds_fst, foldRounds_pos,
        foldRounds_ok, positionsR_fst, positionsR_pos, positionsR_ok, pos_upd, pos_mk0, pos_mk72, pos_mk24, pos_mk48,
        openingR_mk, skipEntries_run, hs, List.nil_append, hfl, frC_length, qsAt_length, List.map_map, Nat.zero_add, Function.comp_def, ← hκ]
       simp only [lvLanes, oodF, powF, nodeBytes, Bool.and_true, Bool.true_and, Bool.and_false,
        Option.isSome_some, ↓reduceIte, Bool.false_eq_true, List.nil_append, hD]
       ring_nf)

/-- The final level of `whirLevelsB` from position `8V` (`whirLevels_final`'s twin). -/
theorem whirLevels_finalB (p : Params) (ν lf : Nat) (B : List FE → FE) (g : Nat) (ood : Bool) (L : Level) (st : WhirState)
    (sig : ByteArray) (s : RS) (V : Nat) (hs : pos s = 8 * V) (hrow : L.row % 8 = 0)
    (hκ : L.kappa = ν - (st.folds.length + L.fold)) (hm : 1 ≤ L.kappa) :
    let ll := lvLanes g ood L none V (some p)
    let lam := feAt sig (8 * ll.V3 + 40)
    let st' := glue lam ⟨frQ sig (8 * V) L.fold st.runningQuad, st.folds ++ frC sig (8 * V) L.fold, st.glued⟩
      [([feAt sig (8 * ll.V5 + 40),
          Lvm.dot (powers lam L.t) ((List.range L.t).map fun j =>
              if L.level = 0 then foldRow0 sig (eqKernelA (frC sig (8 * V) L.fold)) (8 * (ll.V4 + 1 + oStr L * j))
                (L.row / 8)
              else foldRowE sig (eqKernelA (frC sig (8 * V) L.fold)) (8 * (ll.V4 + 1 + oStr L * j)) (2 ^ L.fold)) +
            feAt sig (8 * ll.V5 + 64),
          feAt sig (8 * ll.V5 + 64)],
        fun x => inducedWeight L.kappa (qsAt sig (8 * ll.V2) L) (powers lam L.t) x)]
    let tf := frC sig (8 * ll.V6) L.kappa
    let point := st'.folds ++ tf
    let weight := st'.glued.foldl
      (fun w cl => w + cl.scalar * cl.weightAt (st'.folds.drop cl.foldStart ++ tf))
      (B (point.drop lf ++ point.take lf))
    whirLevelsB p ν lf B false g ood [L] st sig s =
      ((), ⟨8 * ll.V6 + 120 * (L.kappa - 1) + 72, 0,
        (weight * multilinearEval ((List.range (2 ^ L.kappa)).map fun i => feAt sig (8 * ll.V1 + 40 + 24 * i)) tf ==
          tlT sig (8 * ll.V6) L.kappa st'.runningQuad) && (powF sig g (8 * ll.Vo) && s.ok)⟩) := by
  dsimp only
  have hD : 40 + L.row + 104 * L.path = 8 * oStr L := by unfold oStr; (clear * - L ν st s V hrow; omega)
  conv_lhs => rw [whirLevelsB]
  have hfl : ∀ (x : List FE), (st.folds ++ x).length = st.folds.length + x.length := fun x => List.length_append
  rcases Nat.eq_zero_or_pos g with rfl | hg
  all_goals first
    | (have hg0 : g ≠ 0 := Nat.pos_iff_ne_zero.mp hg
       simp only [grindPreR_run _ hg0, powCheckR_run _ hg0, dm_bind, dm_pure, read_run, sampleE_run, srp3_run,
        readEs_run, require_runW, foldRounds_fst, foldRounds_pos, foldRounds_ok, positionsR_fst, positionsR_pos,
        positionsR_ok, pos_upd, pos_mk0, pos_mk24, pos_mk48, openingR_mk, skipEntries_run, hs, List.nil_append, hfl, frC_length,
        qsAt_length, List.map_map, Nat.zero_add, Function.comp_def, ← hκ, tailRounds_run L.kappa hm,
        Bool.false_eq_true, ↓reduceIte, pos_msg]
       simp only [lvLanes, powF, hg0, Bool.and_false, Option.isSome_none, Bool.false_eq_true, ↓reduceIte, hD]
       ring_nf)
    | (simp only [grindPreR_zero, powCheckR_zero, dm_bind, dm_pure, read_run, sampleE_run, srp3_run,
        readEs_run, require_runW, foldRounds_fst, foldRounds_pos, foldRounds_ok, positionsR_fst, positionsR_pos,
        positionsR_ok, pos_upd, pos_mk0, pos_mk24, pos_mk48, openingR_mk, skipEntries_run, hs, List.nil_append, hfl, frC_length,
        qsAt_length, List.map_map, Nat.zero_add, Function.comp_def, ← hκ, tailRounds_run L.kappa hm,
        Bool.false_eq_true, ↓reduceIte, pos_msg]
       simp only [lvLanes, powF, Bool.and_false, Option.isSome_none, Bool.false_eq_true, ↓reduceIte, hD, Bool.true_and]
       ring_nf)
/-! ## One level's prefix on the S2GB stream -/

/-- The heap lanes after a level's openings on the stream `cp` (`lvLanes`' `V5`). -/
def heapLn (cp : Option Params) (L : Level) : Nat :=
  match cp with
  | none => 0
  | some p => 13 * p.heapQ L.level L.cap

/-- `lvLanes_facts` on the stream `cp` (the openings end `heapLn cp L` lanes later). -/
theorem lvLanes_factsB (g : Nat) (ood : Bool) (L : Level) (nxt : Option Level) (V : Nat) (cp : Option Params) :
    (lvLanes g ood L nxt V cp).V1 = V + 15 * L.fold ∧ (lvLanes g ood L nxt V cp).V1 ≤ (lvLanes g ood L nxt V cp).Vc ∧
    (lvLanes g ood L nxt V cp).V2 ≤ (lvLanes g ood L nxt V cp).V3 ∧
    (lvLanes g ood L nxt V cp).V4 = (lvLanes g ood L nxt V cp).V3 + 9 ∧
    (lvLanes g ood L nxt V cp).V5 = (lvLanes g ood L nxt V cp).V4 + oStr L * L.t + heapLn cp L ∧
    (lvLanes g ood L nxt V cp).V6 = (lvLanes g ood L nxt V cp).V5 + 6 ∧
    (lvLanes g ood L nxt V cp).Vc ≤ (lvLanes g ood L nxt V cp).Vo ∧
    (lvLanes g ood L nxt V cp).Vo = (if ood && nxt.isSome then (lvLanes g ood L nxt V cp).Vc + 9 * L.kappa + 9
      else (lvLanes g ood L nxt V cp).Vc) ∧
    (lvLanes g ood L nxt V cp).V2 =
      (if g = 0 then (lvLanes g ood L nxt V cp).Vo else (lvLanes g ood L nxt V cp).Vo + 21) ∧
    (lvLanes g ood L nxt V cp).Vo ≤ (lvLanes g ood L nxt V cp).V2 := by
  cases cp <;> cases nxt <;> cases ood <;> by_cases hg : g = 0 <;> simp [lvLanes, heapLn, hg] <;>
    (clear * -; first | decide | (simp only [Nat.add_comm, Nat.add_left_comm, Nat.add_assoc]; done) | ring1 | omega)

section
variable {c : Ctx} {M : Mem}

/-- **`lvPre_spec` on the stream `cp`** (`lvPreB`; the same proof, `lvLanes_factsB`). -/
theorem lvPreB_spec (C : SCfg) (cp : Option Params) {sig : ByteArray} {T : Nat} (hS : Lvm.Q1.Streamed M sig T) (pc : Nat)
    (zc oc g : Cell) (zk : Nat) (hz : zc.val M = 0) (ho : oc.val M = 1) (hzE : zc.ty = .E)
    (hoE : oc.ty = .E) (hgK : g.ty = .K) (hg : g.val M = 1) (hzk : M.k zk = 0)
    (L : Level) (nxt : Option Level) (i f V : Nat) (q : Cell × Cell × Cell) (p : Ptr) (hp : 1 ≤ p.e)
    (hν : f + L.fold + L.kappa = C.nu) (hw0 : L.level ≠ 0 ∨ (0 < L.fold ∧ L.row / 8 ≤ 2 ^ L.fold))
    (htc : L.t ≤ pw (C.pch i))
    (hch : ∀ k < (C.pch i).length, pw ((C.pch i).take k) < L.t) (hcs : csum (C.cch i) = L.kappa)
    (hT1 : (lvLanes C.g C.ood L nxt V cp).V4 + 1 + oStr L * (L.t - 1) + 3 * 2 ^ L.fold + 2 < T)
    (hT2 : (lvLanes C.g C.ood L nxt V cp).V6 + 8 < T) (hg64 : C.g ≤ 64)
    (hfold : ∀ j < L.fold, M.e (pc + f + j) = feAt sig (8 * V + 120 * j + 40))
    (hpos : ∀ j < L.t, FE.ofK (M.k (C.pb i + j)) =
      eOfNat ((qsAt sig (8 * (lvLanes C.g C.ood L nxt V cp).V2) L).getD j 0))
    (hpw : C.g ≠ 0 → (M.k (C.pw i)).val.toNat < 2 ^ (64 - C.g))
    (h : Lvm.QSig.Ok c M (lvPreB C cp pc zc oc g zk L nxt i f V q) p) :
    qv M (lvPreB C cp pc zc oc g zk L nxt i f V q p).1.1 =
      (if C.ood && nxt.isSome then
        List.zipWith (fun a b => a + 1 * feAt sig (8 * (lvLanes C.g C.ood L nxt V cp).V3 + 40) *
            feAt sig (8 * (lvLanes C.g C.ood L nxt V cp).V3 + 40) * b)
          (List.zipWith (fun a b => a + 1 * feAt sig (8 * (lvLanes C.g C.ood L nxt V cp).V3 + 40) * b)
            (frQ sig (8 * V) L.fold (qv M q))
            ((oodF sig true L.kappa (8 * (lvLanes C.g C.ood L nxt V cp).Vc)).headD ([], fun _ => 0)).1)
      else
        List.zipWith (fun a b => a + 1 * feAt sig (8 * (lvLanes C.g C.ood L nxt V cp).V3 + 40) * b)
          (frQ sig (8 * V) L.fold (qv M q)))
        [feAt sig (8 * (lvLanes C.g C.ood L nxt V cp).V5 + 40),
          Lvm.dot (powers (feAt sig (8 * (lvLanes C.g C.ood L nxt V cp).V3 + 40)) L.t) ((List.range L.t).map fun j =>
            if L.level = 0 then foldRow0 sig (eqKernelA (frC sig (8 * V) L.fold))
              (8 * ((lvLanes C.g C.ood L nxt V cp).V4 + 1 + oStr L * j)) (L.row / 8)
            else foldRowE sig (eqKernelA (frC sig (8 * V) L.fold))
              (8 * ((lvLanes C.g C.ood L nxt V cp).V4 + 1 + oStr L * j)) (2 ^ L.fold)) +
            feAt sig (8 * (lvLanes C.g C.ood L nxt V cp).V5 + 64),
          feAt sig (8 * (lvLanes C.g C.ood L nxt V cp).V5 + 64)] ∧
    (lvPreB C cp pc zc oc g zk L nxt i f V q p).1.2.map (fun x => (x.1.val M, x.2.val M)) =
      (if C.ood && nxt.isSome then
        [(1 * feAt sig (8 * (lvLanes C.g C.ood L nxt V cp).V3 + 40),
            eqEval (oodZ sig (8 * (lvLanes C.g C.ood L nxt V cp).Vc) L.kappa) ((ptv M pc C.nu).drop (f + L.fold))),
          (1 * feAt sig (8 * (lvLanes C.g C.ood L nxt V cp).V3 + 40) * feAt sig (8 * (lvLanes C.g C.ood L nxt V cp).V3 + 40),
            inducedWeight L.kappa (qsAt sig (8 * (lvLanes C.g C.ood L nxt V cp).V2) L)
              (powers (feAt sig (8 * (lvLanes C.g C.ood L nxt V cp).V3 + 40)) L.t) ((ptv M pc C.nu).drop (f + L.fold)))]
      else
        [(1 * feAt sig (8 * (lvLanes C.g C.ood L nxt V cp).V3 + 40),
          inducedWeight L.kappa (qsAt sig (8 * (lvLanes C.g C.ood L nxt V cp).V2) L)
            (powers (feAt sig (8 * (lvLanes C.g C.ood L nxt V cp).V3 + 40)) L.t) ((ptv M pc C.nu).drop (f + L.fold)))]) ∧
    powF sig C.g (8 * (lvLanes C.g C.ood L nxt V cp).Vo) = true := by
  have lf := lvLanes_factsB C.g C.ood L nxt V cp
  obtain ⟨l1, l2, l3, l4, l5, l6, l7, l8, l9, l10⟩ := lf
  simp only [lvPreB] at h ⊢
  generalize (lvLanes C.g C.ood L nxt V cp).V1 = V1 at *
  generalize (lvLanes C.g C.ood L nxt V cp).V2 = V2 at *
  generalize (lvLanes C.g C.ood L nxt V cp).V3 = V3 at *
  generalize (lvLanes C.g C.ood L nxt V cp).V4 = V4 at *
  generalize (lvLanes C.g C.ood L nxt V cp).V5 = V5 at *
  generalize (lvLanes C.g C.ood L nxt V cp).V6 = V6 at *
  generalize (lvLanes C.g C.ood L nxt V cp).Vc = Vc at *
  generalize (lvLanes C.g C.ood L nxt V cp).Vo = Vo at *
  have hpw2 : L.t ≤ 2 ^ Nat.clog 2 (pw (C.pch i)) := le_trans htc (Nat.le_pow_clog (by norm_num) _)
  -- 1. fold rounds
  obtain ⟨h1, h⟩ := okb h
  rw [bind_apply]; dsimp only
  have e1 := roundsG_spec hS L.fold f V q p (by (clear * - l1 l3 hT1 l4 l5 l6 l2 l9 l10 l7 l8; omega)) hfold h1.1
  have hp1 := le_trans hp (adv_e_le p (roundsG pc f V L.fold q p).2)
  generalize (roundsG pc f V L.fold q p).1 = q1 at h e1 ⊢
  generalize p.adv (roundsG pc f V L.fold q p).2 = p1 at h hp1 ⊢
  -- 2. λ
  obtain ⟨h2, h⟩ := okb h
  rw [bind_apply]; dsimp only
  have e2 := ldE_spec hS (by (clear * - hT1 l4 l5 l6; omega)) h2.1
  rw [ldE_out] at e2 h ⊢
  rw [ldEW_adv] at h ⊢
  have e2' : M.e p1.e = feAt sig (8 * V3 + 40) := by
    rw [show 8 * V3 + 40 = 8 * (V3 + 5) by ring]; exact e2
  -- 3. powers of λ
  obtain ⟨h3, h⟩ := okb h
  rw [bind_apply]; dsimp only
  have e3 := pows_spec h3.1 hz ho hoE
  have hlp : ∀ k < L.t, M.e ((pows (Nat.clog 2 (pw (C.pch i))) (ec p1.e) oc zc ⟨p1.k, p1.e + 1⟩).1 + k) =
      feAt sig (8 * V3 + 40) ^ k := fun k hk => by rw [e3 k (by (clear * - hpw2 hk; omega)), Cell.val_E, e2']
  have hp3 : 1 ≤ ((⟨p1.k, p1.e + 1⟩ : Ptr).adv
      (pows (Nat.clog 2 (pw (C.pch i))) (ec p1.e) oc zc ⟨p1.k, p1.e + 1⟩).2).e :=
    le_trans (by simp) (adv_e_le _ _)
  generalize (pows (Nat.clog 2 (pw (C.pch i))) (ec p1.e) oc zc ⟨p1.k, p1.e + 1⟩).1 = lp at h hlp ⊢
  generalize (⟨p1.k, p1.e + 1⟩ : Ptr).adv
    (pows (Nat.clog 2 (pw (C.pch i))) (ec p1.e) oc zc ⟨p1.k, p1.e + 1⟩).2 = p3 at h hp3 ⊢
  -- 4. the fold `eq` table
  obtain ⟨h4, h⟩ := okb h
  rw [bind_apply]; dsimp only
  have hlen := frC_length sig (8 * V) L.fold
  have h4' := h4.1
  rw [← hlen] at h4'
  have e4 := eqTab_eq (fun j => ec (pc + f + j)) zc oc (decide (L.level = 0)) (frC sig (8 * V) L.fold)
    h4' hz (fun _ => rfl) (by rw [← val_E hoE]; exact ho)
    (fun j hj => by rw [Cell.val_E, frC_getD _ _ _ _ (by (clear * - hlen hj; omega)), hfold j (by (clear * - hlen hj; omega))])
  simp only [hlen] at e4
  have hp4 := le_trans hp3 (adv_e_le p3
    (Lvm.Loop.Build.eqTab (fun j => ec (pc + f + j)) zc oc (decide (L.level = 0)) L.fold p3).2)
  have hend := fun (hn : 0 < L.fold) =>
    eqTab_end (fun j => ec (pc + f + j)) zc oc (decide (L.level = 0)) hn p3
  generalize (Lvm.Loop.Build.eqTab (fun j => ec (pc + f + j)) zc oc (decide (L.level = 0)) L.fold p3).1 = er0
    at h e4 hend ⊢
  generalize p3.adv (Lvm.Loop.Build.eqTab (fun j => ec (pc + f + j)) zc oc (decide (L.level = 0)) L.fold p3).2 = p4
    at h hp4 hend ⊢
  rw [ite_bind_eq_bind_ite] at h ⊢
  let win : BM Nat := if L.level = 0 ∧ L.row / 8 < 2 ^ L.fold then do
      let _ ← seqAll ((List.range (2 ^ L.fold - L.row / 8)).map fun _ => lin .E 0 0 zc zc)
      pure (er0 + (2 ^ L.fold - L.row / 8))
    else pure er0
  obtain ⟨hwin, h⟩ := okb h
  rw [bind_apply]; dsimp only
  change Lvm.QSig.Ok c M win p4 at hwin
  have hww : decide (L.level = 0) = true → L.row / 8 ≤ 2 ^ L.fold := by
    intro hl
    have hl' : L.level = 0 := of_decide_eq_true hl
    exact (hw0.resolve_left (by simp [hl'])).2
  have e4w : ∀ k < 2 ^ L.fold, M.e ((win p4).1 + k) =
      if decide (L.level = 0) then
        if k < L.row / 8 then (eqKernelA (frC sig (8 * V) L.fold)).getD (L.row / 8 - 1 - k) 0 else 0
      else (eqKernelA (frC sig (8 * V) L.fold)).getD k 0 := by
    intro k hk
    by_cases hnwin : L.level = 0 ∧ L.row / 8 < 2 ^ L.fold
    · have hpositive := (hw0.resolve_left (by simp [hnwin.1])).1
      have heEnd := hend hpositive
      have hzwin := hwin
      simp only [win, if_pos hnwin] at hzwin
      have hzeros := seqZeros_hold zc hz (2 ^ L.fold - L.row / 8) p4 (okb hzwin).1.1
      simp only [win, if_pos hnwin, bind_apply, pure_apply, hnwin.1, decide_true, ite_true]
      by_cases hkw : k < L.row / 8
      · rw [if_pos hkw]
        have he := e4 (2 ^ L.fold - L.row / 8 + k) (by (clear * - hnwin heEnd hkw; omega))
        simpa only [hnwin.1, decide_true, ite_true,
          show 2 ^ L.fold - 1 - (2 ^ L.fold - L.row / 8 + k) = L.row / 8 - 1 - k by (clear * - hnwin heEnd hkw; omega),
          Nat.add_assoc] using he
      · rw [if_neg hkw, show er0 + (2 ^ L.fold - L.row / 8) + k = p4.e + (k - L.row / 8) by (clear * - hnwin heEnd hkw; omega)]
        exact hzeros (k - L.row / 8) (by (clear * - hk hnwin heEnd hkw; omega))
    · simp only [win, if_neg hnwin, pure_apply]
      by_cases hl : L.level = 0
      · have hw : L.row / 8 = 2 ^ L.fold := by
          have := (hw0.resolve_left (by simp [hl])).2
          (clear * - hnwin hl this; omega)
        simpa [hl, hw, hk] using e4 k hk
      · simpa [hl] using e4 k hk
  have hp4w := le_trans hp4 (adv_e_le p4 (win p4).2)
  generalize (win p4).1 = er at h e4w ⊢
  generalize p4.adv (win p4).2 = p4w at h hp4w ⊢
  -- 5. row folds and the enforced sum
  obtain ⟨h5, h⟩ := okb h
  rw [bind_apply]; dsimp only
  have e5 := foldsG_window_spec hS hz (eqKernelA (frC sig (8 * V) L.fold)) (feAt sig (8 * V3 + 40)) hww e4w hlp
    (fun k hk => by
      have : oStr L * k ≤ oStr L * (L.t - 1) := Nat.mul_le_mul_left _ (by (clear * - hk; omega))
      (clear * - hT1 l5 l6 this; omega))
    (C.pch i) 0 p4w hp4w (by simpa [pw] using htc) (fun k hk => by simpa [pw] using hch k hk) h5.1
  have hp5 := le_trans hp4w (adv_e_le p4w (foldsG (decide (L.level = 0)) L.fold (V4 + 1) (oStr L) er lp
    L.t zc 0 (C.pch i) p4w).2)
  generalize (foldsG (decide (L.level = 0)) L.fold (V4 + 1) (oStr L) er lp L.t zc 0 (C.pch i) p4w).1 = enf
    at h e5 ⊢
  generalize p4w.adv (foldsG (decide (L.level = 0)) L.fold (V4 + 1) (oStr L) er lp L.t zc 0 (C.pch i)
    p4w).2 = p5 at h hp5 ⊢
  -- 6. the intro polynomial
  obtain ⟨h6, h⟩ := okb h
  rw [bind_apply]; dsimp only
  have e6 := rdQ_spec hS (by (clear * - hT2 l6; omega)) h6.1
  have hp6 := le_trans hp5 (adv_e_le p5 (rdQ V5 enf p5).2)
  generalize (rdQ V5 enf p5).1 = it at h e6 ⊢
  generalize p5.adv (rdQ V5 enf p5).2 = p6 at h hp6 ⊢
  -- 7. pointer, 8. roots and inverses
  obtain ⟨-, h⟩ := okb h
  rw [bind_apply]; dsimp only [getPtr] at h ⊢
  rw [Ptr.adv_nil] at h ⊢
  obtain ⟨h8, h⟩ := okb h
  rw [bind_apply]; dsimp only
  have e8 := iwConsts_spec L.kappa hgK h8.1
  have hp8 := le_trans hp6 (adv_e_le p6 (iwConsts L.kappa g p6).2)
  generalize p6.adv (iwConsts L.kappa g p6).2 = p8 at h hp8 ⊢
  -- 9. the column weight
  obtain ⟨h9, h⟩ := okb h
  rw [bind_apply]; dsimp only
  have hptl : ((ptv M pc C.nu).drop (f + L.fold)).length = L.kappa := by
    rw [List.length_drop, ptv_length]; (clear * - hν hcs; omega)
  have e9 := colWG_spec hzE hz hzk L.kappa (qsAt sig (8 * V2) L) (feAt sig (8 * V3 + 40))
    ((ptv M pc C.nu).drop (f + L.fold)) (by rw [hptl, hcs])
    (fun k hk => by rw [ptv_getD _ _ _ _ (by (clear * - hν hcs hptl hk; omega))])
    (fun k hk => by rw [hptl] at hk; exact (e8 k hk).2)
    (fun k hk => by rw [hptl] at hk; exact (e8 k hk).1) hlp hpos (C.pch i) 0 p8
    hp8 (by simpa [pw] using htc) (fun k hk => by simpa [pw] using hch k hk) h9.1
  have eW : (colWG (C.cch i) (pc + (f + L.fold)) (p6.k + L.kappa) p6.k lp (C.pb i) L.t zc zk 0 (C.pch i)
      p8).1.val M = inducedWeight L.kappa (qsAt sig (8 * V2) L) (powers (feAt sig (8 * V3 + 40)) L.t)
        ((ptv M pc C.nu).drop (f + L.fold)) := by
    rw [e9, ← Finset.range_eq_Ico, ← qsAt_length sig (8 * V2) L, inducedWeight_pow]
  have hp9 := le_trans hp8 (adv_e_le p8 (colWG (C.cch i) (pc + (f + L.fold)) (p6.k + L.kappa) p6.k lp
    (C.pb i) L.t zc zk 0 (C.pch i) p8).2)
  generalize (colWG (C.cch i) (pc + (f + L.fold)) (p6.k + L.kappa) p6.k lp (C.pb i) L.t zc zk 0 (C.pch i)
    p8).1 = W at h eW ⊢
  generalize p8.adv (colWG (C.cch i) (pc + (f + L.fold)) (p6.k + L.kappa) p6.k lp (C.pb i) L.t zc zk 0
    (C.pch i) p8).2 = p9 at h hp9 ⊢
  -- 10. the PoW check
  obtain ⟨h10, h⟩ := okb h
  rw [bind_apply]; dsimp only
  have hpow : powF sig C.g (8 * Vo) = true := by
    unfold powF
    split_ifs with hg0
    · rfl
    · obtain ⟨gt, gn⟩ := g
      cases hgK
      have hV2 : V2 = Vo + 21 := by rw [l9]; simp [hg0]
      simp only [powG, hg0, ↓reduceIte] at h10
      have e := assertEqKK_spec h10.1 h10.2 (ofK_inj (hg.trans ofK_one.symm))
      have hl := hS (V2 - 2) (by (clear * - l3 hT1 l4 l5 l6 l9 l8 hV2; omega))
      rw [hl] at e
      apply powOKR_of hg64
      rw [show 8 * Vo + 136 + 16 = 8 * (V2 - 2) by (clear * - l9 l8 hV2; omega), e]
      exact hpw hg0
  have hp10 := le_trans hp9 (adv_e_le p9 (powG C V2 i g p9).2)
  generalize p9.adv (powG C V2 i g p9).2 = p10 at h hp10 ⊢
  -- 11. the OOD items and the glue
  by_cases hod : (C.ood && nxt.isSome) = true
  · simp only [hod, ↓reduceIte] at h ⊢
    have hVo : Vo = Vc + 9 * L.kappa + 9 := by rw [l8]; simp [hod]
    obtain ⟨g1, h⟩ := okb h
    rw [bind_apply]; dsimp only
    obtain ⟨ezb, ez⟩ := preloadG_spec hS (fun v hv => by
      simp only [List.mem_map, List.mem_range] at hv; obtain ⟨j, hj, rfl⟩ := hv; (clear * - hcs l3 hT1 l4 l5 l6 l9 l10 l8 hptl hVo hj; omega)) g1.1
    rw [ezb] at h ⊢
    rw [preloadG_adv] at h ⊢
    obtain ⟨g2, h⟩ := okb h
    rw [bind_apply]; dsimp only
    have ey := ldE_spec hS (by (clear * - hcs l3 hT1 l4 l5 l6 l9 l10 l8 hptl hVo; omega)) g2.1
    rw [ldE_out] at ey h ⊢
    rw [ldEW_adv] at h ⊢
    obtain ⟨g3, h⟩ := okb h
    rw [bind_apply]; dsimp only
    have eio := rdQ_spec hS (by (clear * - hcs l3 hT1 l4 l5 l6 l9 l10 l8 hptl hVo; omega)) g3.1
    rw [rdQ_adv] at h ⊢
    obtain ⟨g4, h⟩ := okb h
    rw [bind_apply]; dsimp only
    have el2 := mulAdd_spec g4.1
    obtain ⟨g5, h⟩ := okb h
    rw [bind_apply]; dsimp only
    have eg1 := glueG_spec g5.1
    obtain ⟨g6, h⟩ := okb h
    rw [bind_apply]; dsimp only
    have eg2 := glueG_spec g6.1
    obtain ⟨g7, -⟩ := okb h
    rw [bind_apply]; dsimp only
    have eo := eqZG_range g7.1 hz ho
    simp only [pure_apply]
    refine ⟨?_, ?_, hpow⟩
    · rw [eg2, eg1, eio, e1, e6, e5, el2, ey, hz, add_zero, Cell.val_E, e2']
      simp only [oodF, ↓reduceIte, List.headD_cons]
      rw [show 8 * (Vc + 9 * L.kappa + 3) + 40 = 8 * Vc + 72 * L.kappa + 24 + 40 by ring,
        show 8 * (Vc + 9 * L.kappa + 3) + 64 = 8 * Vc + 72 * L.kappa + 24 + 64 by ring,
        show 8 * (Vc + 9 * L.kappa + 5) = 8 * Vc + 72 * L.kappa + 40 by ring, dot_map_range,
        Finset.range_eq_Ico]
      simp only [decide_eq_true_eq, mul_one, one_mul, mul_assoc]
    · simp only [List.map_cons, List.map_nil, el2, Cell.val_E, e2', hz, add_zero, eW, eo, one_mul]
      refine List.cons_eq_cons.mpr ⟨?_, rfl⟩
      congr 1
      congr 1
      · simp only [oodZ]
        refine List.map_congr_left fun j hj => ?_
        rw [ez j (by simpa using hj)]
        simp only [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range (List.mem_range.mp hj),
          Option.map_some, Option.getD_some]
        congr 1; ring
      · apply List.ext_getElem (by simp [ptv_length]; (clear * - hν hcs hptl; omega))
        intro k h1 h2
        simp only [List.length_map, List.length_range] at h1
        rw [List.getElem_map, List.getElem_range, ← List.getD_eq_getElem _ 0,
          ptv_getD _ _ _ _ (by (clear * - hν hcs hptl h2; omega))]
  · simp only [hod, Bool.false_eq_true, ↓reduceIte] at h ⊢
    obtain ⟨g5, -⟩ := okb h
    rw [bind_apply]; dsimp only
    have eg1 := glueG_spec g5.1
    simp only [pure_apply]
    refine ⟨?_, ?_, hpow⟩
    · rw [eg1, e1, e6, e5, Cell.val_E, e2', dot_map_range, Finset.range_eq_Ico]
      simp only [decide_eq_true_eq]
    · simp only [List.map_cons, List.map_nil, Cell.val_E, e2', eW, one_mul]



end

section
variable {c : Ctx} {M : Mem}

/-! ## The level induction on the S2GB stream -/

/-- The challenge cells from `pc + f` hold `F`'s challenges of the levels `Ls` from lane `V`. -/
def ChOkB (g : Nat) (ood : Bool) (cp : Option Params) (M : Mem) (sig : ByteArray) (pc f : Nat) (Ls : List Level) (V : Nat) : Prop :=
  ∀ j < (chLanes g ood Ls V cp).length, M.e (pc + f + j) = feAt sig (8 * (chLanes g ood Ls V cp).getD j 0)

/-- The position cells of the levels `Ls` (level `i` first) hold `F`'s positions. -/
def PosOkB (C : SCfg) (cp : Option Params) (M : Mem) (sig : ByteArray) (i : Nat) (Ls : List Level) (V : Nat) : Prop :=
  ∀ i' < Ls.length, ∀ j < (Ls.getD i' default).t, FE.ofK (M.k (C.pb (i + i') + j)) =
    eOfNat ((qsAt sig (8 * (posLanes C.g C.ood Ls V cp).getD i' 0) (Ls.getD i' default)).getD j 0)

theorem chOk_foldB {cp : Option Params} {g : Nat} {ood : Bool} {M : Mem} {sig : ByteArray} {pc f : Nat} {L : Level} {rest : List Level} {V : Nat}
    (h : ChOkB g ood cp M sig pc f (L :: rest) V) : ∀ j < L.fold, M.e (pc + f + j) = feAt sig (8 * V + 120 * j + 40) := by
  intro j hj
  have hl : j < (chLanes g ood (L :: rest) V cp).length := by
    cases rest <;> simp [chLanes] <;> (clear * - hj; omega)
  rw [h j hl]
  have : (chLanes g ood (L :: rest) V cp).getD j 0 = V + 15 * j + 5 := by
    cases rest <;> (simp only [chLanes]; rw [getD_app_left _ _ _ (by simpa using hj), getD_map_range _ _ _ _ hj])
  rw [this]; congr 1; ring

theorem chOk_nextB {cp : Option Params} {g : Nat} {ood : Bool} {M : Mem} {sig : ByteArray} {pc f : Nat} {L N : Level} {rest : List Level} {V : Nat}
    (h : ChOkB g ood cp M sig pc f (L :: N :: rest) V) :
    ChOkB g ood cp M sig pc (f + L.fold) (N :: rest) (lvLanes g ood L (some N) V cp).V6 := by
  intro j hj
  have e := h (L.fold + j) (by simp only [chLanes] at hj ⊢; simp; (clear * - hj; omega))
  simp only [chLanes] at e ⊢
  have hlen : ((List.range L.fold).map (fun j => V + 15 * j + 5)).length = L.fold := by simp
  have ga := getD_app_right ((List.range L.fold).map (fun j => V + 15 * j + 5))
    (chLanes g ood (N :: rest) (lvLanes g ood L (some N) V cp).V6 cp) j
  rw [hlen] at ga
  rw [ga] at e
  rw [show pc + (f + L.fold) + j = pc + f + (L.fold + j) by ring]; exact e

theorem chOk_tailB {cp : Option Params} {g : Nat} {ood : Bool} {M : Mem} {sig : ByteArray} {pc f : Nat} {L : Level} {V : Nat}
    (h : ChOkB g ood cp M sig pc f [L] V) :
    ∀ j < L.kappa, M.e (pc + (f + L.fold) + j) = feAt sig (8 * (lvLanes g ood L none V cp).V6 + 120 * j + 40) := by
  intro j hj
  have e := h (L.fold + j) (by simp [chLanes]; (clear * - hj; omega))
  simp only [chLanes] at e
  have hlen : ((List.range L.fold).map (fun j => V + 15 * j + 5)).length = L.fold := by simp
  have ga := getD_app_right ((List.range L.fold).map (fun j => V + 15 * j + 5))
    ((List.range L.kappa).map (fun j => (lvLanes g ood L none V cp).V6 + 15 * j + 5)) j
  rw [hlen] at ga
  rw [ga, getD_map_range _ _ _ _ hj] at e
  rw [show pc + (f + L.fold) + j = pc + f + (L.fold + j) by ring, e]; congr 1; ring

theorem posOk_headB {cp : Option Params} {C : SCfg} {M : Mem} {sig : ByteArray} {i : Nat} {L : Level} {rest : List Level} {V : Nat}
    (h : PosOkB C cp M sig i (L :: rest) V) : ∀ j < L.t, FE.ofK (M.k (C.pb i + j)) =
      eOfNat ((qsAt sig (8 * (lvLanes C.g C.ood L rest.head? V cp).V2) L).getD j 0) := by
  intro j hj
  have e := h 0 (by simp) j (by simpa using hj)
  cases rest <;> simpa [posLanes] using e

theorem posOk_nextB {cp : Option Params} {C : SCfg} {M : Mem} {sig : ByteArray} {i : Nat} {L N : Level} {rest : List Level} {V : Nat}
    (h : PosOkB C cp M sig i (L :: N :: rest) V) : PosOkB C cp M sig (i + 1) (N :: rest) (lvLanes C.g C.ood L (some N) V cp).V6 := by
  intro i' hi' j hj
  have e := h (i' + 1) (by simp at hi' ⊢; (clear * - hi'; omega)) j (by simpa using hj)
  simp only [posLanes] at e
  rw [show i + 1 + i' = i + (i' + 1) by ring]
  simpa using e

set_option maxHeartbeats 4000000 in
theorem levels_runB (C : SCfg) (pp : Params) {sig : ByteArray} {T : Nat} (hS : Lvm.Q1.Streamed M sig T) (pc : Nat)
    (zc oc g : Cell) (zk : Nat) (bas : Cell) (hz : zc.val M = 0) (ho : oc.val M = 1) (hzE : zc.ty = .E)
    (hoE : oc.ty = .E) (hg : g.val M = 1) (hgK : g.ty = .K) (hzk : M.k zk = 0) (lf : Nat)
    (B : List FE → FE) (hbas : bas.val M = B ((ptv M pc C.nu).drop lf ++ (ptv M pc C.nu).take lf)) :
    ∀ (Ls : List Level) (i f V : Nat) (q : Cell × Cell × Cell) (gl : List (Cell × Cell)) (st : WhirState)
      (p : Ptr), lvOkB C (some pp) T Ls i f V = true → 1 ≤ p.e → qv M q = st.runningQuad →
      st.folds = (ptv M pc C.nu).take f → ChOkB C.g C.ood (some pp) M sig pc f Ls V → PosOkB C (some pp) M sig i Ls V →
      PwOk C M i Ls → GlOk M pc C.nu f st gl → Lvm.QSig.Ok c M (levelsGB C (some pp) pc zc oc g zk bas Ls i f V q gl) p →
      ∀ s : RS, pos s = 8 * V →
        (whirLevelsB pp C.nu lf B false C.g C.ood Ls st sig s).2.ok = s.ok ∧
        pos (whirLevelsB pp C.nu lf B false C.g C.ood Ls st sig s).2 = 8 * stackEndL C.g C.ood Ls V (some pp) ∧
        (whirLevelsB pp C.nu lf B false C.g C.ood Ls st sig s).2.msg = 0 := by
  intro Ls
  induction Ls with
  | nil => intro i f V q gl st p hok; simp [lvOkB] at hok
  | cons L rest ih =>
    intro i f V q gl st p hok hp hq hfo hch hpo hpw hgl h s hs
    have hA := fun (n : Nat) (hn : f + L.fold + n = C.nu) => ptv_take_append (M := M) (pc := pc) (ν := C.nu) (f := f)
      (frC_length sig (8 * V) L.fold) (by (clear * - hn; omega)) (fun j hj => by rw [frC_getD _ _ _ _ hj, chOk_foldB hch j hj])
    cases rest with
    | nil =>
      simp only [lvOkB, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true, List.mem_range,
        and_assoc, List.head?_nil, and_true] at hok
      obtain ⟨hν, hrow, hw0, ht1, htc, hchk, hcs, hT1, hT2, hm, hg64⟩ := hok
      replace hT1 := of_decide_eq_true hT1
      replace hT2 := of_decide_eq_true hT2
      have hfl : st.folds.length = f := by rw [hfo, List.length_take, ptv_length]; (clear * - hν hcs hm; omega)
      obtain ⟨l1, l2, l3, l4, l5, l6, l7, l8, l9, l10⟩ := lvLanes_factsB C.g C.ood L none V (some pp)
      simp only [levelsGB, List.head?_nil] at h
      obtain ⟨hpre, h⟩ := okb h
      have hpo0 := posOk_headB hpo
      have e := lvPreB_spec C (some pp) hS pc zc oc g zk hz ho hzE hoE hgK hg hzk L none i f V q p hp hν hw0 htc
        hchk hcs hT1 (by (clear * - hT2 l6; omega)) hg64 (chOk_foldB hch) hpo0 (pwOk_head hpw) hpre
      generalize (lvPreB C (some pp) pc zc oc g zk L none i f V q p).1 = r at h e
      generalize p.adv (lvPreB C (some pp) pc zc oc g zk L none i f V q p).2 = p' at h
      obtain ⟨eq, el, epw⟩ := e
      simp only [Option.isSome_none, Bool.and_false, Bool.false_eq_true, ↓reduceIte] at eq el
      rw [hq] at eq
      obtain ⟨ht, h⟩ := okb h
      have et := tailG_spec hS L.kappa (f + L.fold) (lvLanes C.g C.ood L none V (some pp)).V6 r.1 p' hm (by (clear * - hT2; omega))
        (fun j hj => chOk_tailB hch j hj) ht.1
      generalize (tailG pc (f + L.fold) (lvLanes C.g C.ood L none V (some pp)).V6 L.kappa r.1 p').1 = tgt at h et
      generalize p'.adv (tailG pc (f + L.fold) (lvLanes C.g C.ood L none V (some pp)).V6 L.kappa r.1 p').2 = p2 at h
      obtain ⟨hmf, h⟩ := okb h
      have hVc : (lvLanes C.g C.ood L none V (some pp)).Vc = (lvLanes C.g C.ood L none V (some pp)).V1 + 3 * 2 ^ L.kappa := by
        simp [lvLanes]
      have hVcV2 : (lvLanes C.g C.ood L none V (some pp)).Vc ≤ (lvLanes C.g C.ood L none V (some pp)).V2 := by
        rw [l9]; split_ifs <;> omega
      have em := mleFold_eq hmf.1 sig
        ((List.range (2 ^ L.kappa)).map fun i => feAt sig (8 * (lvLanes C.g C.ood L none V (some pp)).V1 + 40 + 24 * i))
        (frC sig (8 * (lvLanes C.g C.ood L none V (some pp)).V6) L.kappa) (by simp) (frC_length _ _ _)
        (fun j hj => by rw [Cell.val_E, frC_getD _ _ _ _ hj, chOk_tailB hch j hj])
        (fun v hv k hk => by
          have : 3 * v < 3 * 2 ^ L.kappa := by (clear * - hv; omega)
          rw [hS _ (by (clear * - hT1 l3 l4 l5 l9 hVc hVcV2 hv hk; omega))]; rfl)
        (fun v hv => by rw [getD_map_range _ _ _ _ hv]; congr 1; ring)
      generalize (mleFold L.kappa ((lvLanes C.g C.ood L none V (some pp)).V1 + 5) (fun j => ec (pc + (f + L.fold) + j)) p2).1
        = mle at h em
      generalize p2.adv (mleFold L.kappa ((lvLanes C.g C.ood L none V (some pp)).V1 + 5)
        (fun j => ec (pc + (f + L.fold) + j)) p2).2 = p3 at h
      obtain ⟨hw, h⟩ := okb h
      have ew := wsumG_spec (gl ++ r.2) bas p3 hw.1
      generalize (wsumG bas (gl ++ r.2) p3).1 = w at h ew
      generalize p3.adv (wsumG bas (gl ++ r.2) p3).2 = p4 at h
      have hfin := (terminalCheck_iff h.1 hg).mp h.2
      have hF := whirLevels_finalB pp C.nu lf B C.g C.ood L st sig s V hs hrow (by (clear * - hν hcs hm hfl; omega)) hm
      dsimp only at hF
      rw [hF]
      refine ⟨?_, ?_, rfl⟩
      · rw [epw, Bool.true_and, Bool.and_eq_right_iff_imp]
        intro _
        rw [wh_fe_beq, glue_one]
        dsimp only
        rw [← eq, ← et, ← em, hfo, hA L.kappa (by (clear * - hν; omega))]
        have hB := ptv_take_append (M := M) (pc := pc) (ν := C.nu) (f := f + L.fold)
          (frC_length sig (8 * (lvLanes C.g C.ood L none V (some pp)).V6) L.kappa) (by (clear * - hν; omega))
          (fun j hj => by rw [frC_getD _ _ _ _ hj, chOk_tailB hch j hj])
        rw [List.take_of_length_le (l := ptv M pc C.nu) (i := f + L.fold + L.kappa)
          (by rw [ptv_length]; (clear * - hν; omega))] at hB
        rw [glued_foldl _ _ _ _ _ hB (fun gc hgc => ?_), hB, ← hbas]
        · rw [List.map_append, hgl.1]
          have hnew : ([⟨1 * feAt sig (8 * (lvLanes C.g C.ood L none V (some pp)).V3 + 40),
              ((ptv M pc C.nu).take (f + L.fold)).length, fun x => inducedWeight L.kappa
                (qsAt sig (8 * (lvLanes C.g C.ood L none V (some pp)).V2) L)
                (powers (feAt sig (8 * (lvLanes C.g C.ood L none V (some pp)).V3 + 40)) L.t) x⟩] : List GluedClaim).map
              (fun gc => (gc.scalar, gc.weightAt ((ptv M pc C.nu).drop gc.foldStart))) =
              r.2.map (fun x => (x.1.val M, x.2.val M)) := by
            rw [el]
            simp only [List.map_cons, List.map_nil, List.length_take, ptv_length]
            rw [show min (f + L.fold) C.nu = f + L.fold by (clear * - hν hcs hm; omega)]
          rw [hnew, ← List.map_append, List.foldl_map, ← ew]
          exact hfin
        · rw [List.length_take, ptv_length, show min (f + L.fold) C.nu = f + L.fold by (clear * - hν hcs hm; omega)]
          rcases List.mem_append.mp hgc with h1 | h1
          · exact le_trans (hgl.2 gc h1) (by (clear * - hν hcs hfl; omega))
          · simp only [List.mem_singleton] at h1; subst h1; simp [ptv_length]
      · simp only [pos, stackEndL]
        have : 1 ≤ L.kappa := hm
        (clear * -; first | decide | (simp only [Nat.add_comm, Nat.add_left_comm, Nat.add_assoc]; done) | ring1 | omega)
    | cons N rest' =>
      simp only [lvOkB, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true, List.mem_range,
        and_assoc, List.head?_cons] at hok
      obtain ⟨hν, hrow, hw0, ht1, htc, hchk, hcs, hT1, hT2, hm, hg64, hrest⟩ := hok
      replace hT1 := of_decide_eq_true hT1
      replace hT2 := of_decide_eq_true hT2
      have hfl : st.folds.length = f := by rw [hfo, List.length_take, ptv_length]; (clear * - hν hcs hm; omega)
      obtain ⟨l1, l2, l3, l4, l5, l6, l7, l8, l9, l10⟩ := lvLanes_factsB C.g C.ood L (some N) V (some pp)
      rw [levelsGB] at h
      simp only [List.head?_cons] at h
      obtain ⟨hpre, h⟩ := okb h
      have hpo0 := posOk_headB hpo
      have e := lvPreB_spec C (some pp) hS pc zc oc g zk hz ho hzE hoE hgK hg hzk L (some N) i f V q p hp hν hw0 htc
        hchk hcs hT1 (by (clear * - hT2 l6; omega)) hg64 (chOk_foldB hch) hpo0 (pwOk_head hpw) hpre
      have hpr := le_trans hp (adv_e_le p (lvPreB C (some pp) pc zc oc g zk L (some N) i f V q p).2)
      generalize (lvPreB C (some pp) pc zc oc g zk L (some N) i f V q p).1 = r at h e
      generalize p.adv (lvPreB C (some pp) pc zc oc g zk L (some N) i f V q p).2 = p' at h hpr
      obtain ⟨eq, el, epw⟩ := e
      simp only [Option.isSome_some, Bool.and_true] at eq el
      rw [hq] at eq
      rw [whirLevels_stepB pp C.nu lf B C.g C.ood L N rest' st sig s V hs hrow (by (clear * - hν hcs hm hfl; omega)) hm, epw, Bool.true_and]
      simp only [stackEndL]
      have hfo' : st.folds ++ frC sig (8 * V) L.fold = (ptv M pc C.nu).take (f + L.fold) := by
        rw [hfo]; exact hA L.kappa (by (clear * - hν; omega))
      by_cases hod : C.ood = true
      · rw [if_pos hod] at eq el
        rw [show oodF sig C.ood = oodF sig true by rw [hod]]
        simp only [oodF, ↓reduceIte, List.headD_cons, List.cons_append, List.nil_append, glue_two] at eq ⊢
        exact ih (i + 1) (f + L.fold) (lvLanes C.g C.ood L (some N) V (some pp)).V6 r.1 (gl ++ r.2) _ p' hrest hpr
          (by exact eq) (by exact hfo') (chOk_nextB hch) (posOk_nextB hpo) (pwOk_next hpw)
          (by
            dsimp only [GlOk]
            refine ⟨?_, ?_⟩
            · rw [List.map_append, List.map_append, hgl.1, List.map_append, el]
              simp only [List.map_cons, List.map_nil, List.length_append, frC_length, hfl, List.append_assoc,
                List.singleton_append]
            · intro gc hgc
              simp only [List.mem_append, List.mem_singleton] at hgc
              rcases hgc with (h1 | h1) | h1
              · exact le_trans (hgl.2 gc h1) (by (clear * - hν hcs hfl; omega))
              · subst h1; simp [frC_length, hfl]
              · subst h1; simp [frC_length, hfl])
          h _ (by simp only [pos]; (clear * - l6; omega))
      · rw [if_neg hod] at eq el
        rw [show oodF sig C.ood = oodF sig false by simp only [Bool.not_eq_true] at hod; rw [hod]]
        simp only [oodF, Bool.false_eq_true, ↓reduceIte, List.nil_append, glue_one]
        exact ih (i + 1) (f + L.fold) (lvLanes C.g C.ood L (some N) V (some pp)).V6 r.1 (gl ++ r.2) _ p' hrest hpr
          (by exact eq) (by exact hfo') (chOk_nextB hch) (posOk_nextB hpo) (pwOk_next hpw)
          (by
            dsimp only [GlOk]
            refine ⟨?_, ?_⟩
            · rw [List.map_append, hgl.1, List.map_append, el]
              simp only [List.map_cons, List.map_nil, List.length_append, frC_length, hfl]
            · intro gc hgc
              rcases List.mem_append.mp hgc with h1 | h1
              · exact le_trans (hgl.2 gc h1) (by (clear * - hν hcs hfl; omega))
              · simp only [List.mem_singleton] at h1; subst h1; simp [frC_length, hfl])
          h _ (by simp only [pos]; (clear * - l6; omega))

end

section
variable {c : Ctx} {M : Mem}

set_option maxHeartbeats 1000000 in
/-- **`stackG_run` on the S2GB stream**: `stackGWGB` replays `verifyStackedOpeningB` on any claim list `scs` whose batched
values the target and the basis gadgets give. -/
theorem stackG_runB {β : Type} (C : SCfg) (pp : Params) (n : Nat) (pre : BM β) (tg : β → Nat → BM Cell)
    (bg : β → Nat → Nat → BM Cell) (W : β → Prop) (scs : List StackClaim) (hn : scs.length = n)
    (hpre : Hs c M pre W)
    (htg : ∀ w, W w → ∀ (sp : Nat) (s : FE), (∀ i < n, M.e (sp + i) = s ^ i) →
      Hs c M (tg w sp) (fun t => t.val M = Lvm.dot (powers s n) (scs.map (·.2))))
    (hbg : ∀ w, W w → ∀ (sp xb : Nat) (s : FE), (∀ i < n, M.e (sp + i) = s ^ i) →
      Hs c M (bg w sp xb) (fun b => b.val M =
        Lvm.dot (powers s n) (scs.map fun sc => sc.1 ((List.range C.nu).map fun i => M.e (xb + i)))))
    (zc oc g : Cell) {sig : ByteArray} {T : Nat}
    (hS : Lvm.Q1.Streamed M sig T) (hok : LayOkB C (some pp) T = true) (hz : zc.val M = 0)
    (ho : oc.val M = 1) (hzE : zc.ty = .E) (hoE : oc.ty = .E) (hg : g.val M = 1) (hgK : g.ty = .K)
    (hpos : PosOkB C (some pp) M sig 0 C.levels (C.U + 15)) (hpw : PwOk C M 0 C.levels) {p : Ptr} (hp : 1 ≤ p.e)
    (h : Lvm.QSig.Ok c M (stackGWGB C (some pp) n pre tg bg zc oc g) p) (s : RS) (hs : pos s = 8 * C.U) :
    (verifyStackedOpeningB pp C.levels C.nu scs false C.g C.ood sig s).2.ok = s.ok ∧
    pos (verifyStackedOpeningB pp C.levels C.nu scs false C.g C.ood sig s).2 =
      8 * stackEndL C.g C.ood C.levels (C.U + 15) (some pp) ∧
    (verifyStackedOpeningB pp C.levels C.nu scs false C.g C.ood sig s).2.msg = 0 := by
  simp only [LayOkB, Bool.and_eq_true, List.all_eq_true] at hok
  obtain ⟨⟨⟨hlv, hch⟩, hU⟩, hlf⟩ := hok
  replace hU := of_decide_eq_true hU
  replace hlf := of_decide_eq_true hlf
  simp only [stackGWGB] at h
  -- the shape and the muxed claims
  obtain ⟨h0, h⟩ := okb h
  have hw := hpre p h0.1
  have hp0 := le_trans hp (adv_e_le p (pre p).2)
  generalize (pre p).1 = w at h hw
  generalize p.adv (pre p).2 = p at h hp0
  clear hp
  -- the challenges
  obtain ⟨h1, h⟩ := okb h
  obtain ⟨epc, ech⟩ := preloadG_spec hS (fun v hv => of_decide_eq_true (hch v hv)) h1.1
  rw [epc] at h
  have hp1 := le_trans hp0 (adv_e_le p (preloadG (chLanes C.g C.ood C.levels (C.U + 15) (some pp)) p).2)
  generalize p.adv (preloadG (chLanes C.g C.ood C.levels (C.U + 15) (some pp)) p).2 = p1 at h hp1
  -- the batching challenge and its powers
  obtain ⟨h2, h⟩ := okb h
  have esb := ldE_spec hS (by (clear * - hU; omega)) h2.1
  rw [ldE_out] at esb h
  rw [ldEW_adv] at h
  have esb' : M.e p1.e = feAt sig (8 * C.U + 40) := by
    rw [show 8 * C.U + 40 = 8 * (C.U + 5) by ring]; exact esb
  obtain ⟨h3, h⟩ := okb h
  have e3 := pows_spec h3.1 hz ho hoE
  have hsp : ∀ i < n,
      M.e ((pows (Nat.clog 2 n) (ec p1.e) oc zc ⟨p1.k, p1.e + 1⟩).1 + i) =
        feAt sig (8 * C.U + 40) ^ i := fun i hi => by
    rw [e3 i (le_trans hi.le (Nat.le_pow_clog (by norm_num) _)), Cell.val_E, esb']
  have hp3 : 1 ≤ ((⟨p1.k, p1.e + 1⟩ : Ptr).adv
      (pows (Nat.clog 2 n) (ec p1.e) oc zc ⟨p1.k, p1.e + 1⟩).2).e :=
    le_trans (by show 1 ≤ p1.e + 1; (clear * - hp1; omega)) (adv_e_le _ _)
  generalize (pows (Nat.clog 2 n) (ec p1.e) oc zc ⟨p1.k, p1.e + 1⟩).1 = sp at h hsp
  generalize (⟨p1.k, p1.e + 1⟩ : Ptr).adv
    (pows (Nat.clog 2 n) (ec p1.e) oc zc ⟨p1.k, p1.e + 1⟩).2 = p3 at h hp3
  -- the target
  obtain ⟨h4, h⟩ := okb h
  have et := htg w hw sp _ hsp p3 h4.1
  have hp4 := le_trans hp3 (adv_e_le p3 (tg w sp p3).2)
  generalize (tg w sp p3).1 = tgt at h et
  generalize p3.adv (tg w sp p3).2 = p4 at h hp4
  -- the basis point and the basis
  obtain ⟨h5, h⟩ := okb h
  obtain ⟨exb, ecp⟩ := copiesG_spec (fun x hx => by
    rcases List.mem_append.mp hx with hx | hx
    · obtain ⟨k, -, rfl⟩ := List.mem_map.mp (List.mem_of_mem_drop hx); rfl
    · obtain ⟨k, -, rfl⟩ := List.mem_map.mp (List.mem_of_mem_take hx); rfl) h5.1
  have hxs := xs_eq (M := M) hlf ecp
  rw [exb] at h
  have hp5 : 1 ≤ (p4.adv (copiesG (((List.range C.nu).map fun k => ec (p.e + k)).drop C.lf ++
      ((List.range C.nu).map fun k => ec (p.e + k)).take C.lf) p4).2).e :=
    le_trans hp4 (adv_e_le _ _)
  generalize p4.adv (copiesG (((List.range C.nu).map fun k => ec (p.e + k)).drop C.lf ++
      ((List.range C.nu).map fun k => ec (p.e + k)).take C.lf) p4).2 = p5 at h hp5
  obtain ⟨h6, h⟩ := okb h
  have eb := hbg w hw sp p4.e _ hsp p5 h6.1
  rw [hxs] at eb
  have hp6 := le_trans hp5 (adv_e_le p5 (bg w sp p4.e p5).2)
  generalize (bg w sp p4.e p5).1 = bas at h eb
  generalize p5.adv (bg w sp p4.e p5).2 = p6 at h hp6
  -- the `K` zero cell
  obtain ⟨h7, h⟩ := okb h
  have ez := lin_spec (τ := .K) (k := 1) (k' := 0) (a := g) (b := g) h7.1
  have hzk : M.k p6.k = 0 := by
    rw [show (lin .K 1 0 g g p6).1 = kc p6.k from rfl, Cell.val_K, hg, ofK_one, ofK_zero, one_mul,
      add_zero, CharTwo.add_self_eq_zero] at ez
    exact ofK_inj (ez.trans ofK_zero.symm)
  have hp7 := le_trans hp6 (adv_e_le p6 (const .K 0 g p6).2)
  rw [show (const .K 0 g p6).1 = kc p6.k from rfl] at h
  generalize p6.adv (const .K 0 g p6).2 = p7 at h hp7
  -- `verifyWhir`'s first polynomial
  obtain ⟨h8, h⟩ := okb h
  have eq0 := rdQ_spec hS (by (clear * - hU; omega)) h8.1
  have hp8 := le_trans hp7 (adv_e_le p7 (rdQ (C.U + 9) tgt p7).2)
  generalize (rdQ (C.U + 9) tgt p7).1 = q at h eq0
  generalize p7.adv (rdQ (C.U + 9) tgt p7).2 = p8 at h hp8
  -- `F`
  simp only [verifyStackedOpeningB, verifyWhirB]
  rw [dm_bind, sampleE_run]
  dsimp only
  rw [dm_bind, srp3_run]
  dsimp only
  refine levels_runB C pp hS p.e zc oc g p6.k bas hz ho hzE hoE hg hgK hzk C.lf _ ?_ C.levels 0 0 (C.U + 15)
    q [] _ p8 hlv hp8 ?_ (by simp) (fun j hj => by rw [Nat.add_zero]; exact ech j hj) hpos hpw
    ⟨by simp, by simp⟩ h _ ?_
  · rw [eb, hs, hn]
  · rw [eq0, et, pos_mk0, hs, hn, show 8 * (C.U + 9) = 8 * C.U + 72 by ring]
  · simp only [pos] at hs ⊢; (clear * - hs; omega)


end

end Lvm.Har
