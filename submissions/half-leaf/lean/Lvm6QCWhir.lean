-- New for lvm6 (WP CC). Generators and HARs of the opening family's transcript part: a fold round,
-- a level's fold rounds, the level interface (with position and value gadgets as parameters), one
-- level, and the ring group (CC-1 … CC-5 of `Lvm6QCStmt`).
import Lvm6QCRun

/-!
# The opening's rounds, interface, level and ring group (generator and HAR)

The transcript part of the opening asserts nothing: its values are stream lanes (`ld2`), its
grinds are `PowLayO` (CD's PoW rows), its positions and opened values come from the gadgets the
statements take (`posG`, `valsG`). So the generators place no rows of their own:

* `roundGen g a`: `u₀, w, c₀, c₁` at `a, a + 2, a + 4, a + 6`, `α` at `a + 9`, `β` at `a + 18`;
  **`roundHar : RoundHarStmt roundGen`**. `roundsGen`, **`roundsHar`** (27 lanes a round).
* `tailGen`: the high part from `a`, the OOD point's answers (`ansAt`), `y`, the positions from
  `posG` on the query group's first `kq + 1` answers, `λ` its answer `kq + 1`, the values from
  `valsG` on the opened rows (`openRows`); **`tailHar L : TailHarStmt L (tailGen …)`** via
  `runsO_tailP` (the `RunsO` fact for any cells meeting the gadgets' conclusions).
* `levelGen`, **`levelHar L : LevelHarStmt L (levelGen …)`**: rounds, then the interface at
  `a + 27ℓ`, whose value gadget reads the rounds' cells.
* `ringGen g a`: `f`, `g`, `λ₀` = answers `0–7`, `8–15`, `16` of the group; **`ringHar`**.
-/

set_option autoImplicit false

namespace Lvm6.QC

open LeanVM.Parameters LeanVM.Protocol.Compile LeanVM.Protocol.Verifier
open Lvm Lvm.Loop Lvm.Loop.Build Lvm.Q2 Lvm.Har Lvm.E2V Lvm6.QK
open Lvm6 (Item Level)

theorem runsO_of_eq {β : Type} {M : Mem} {l l' : List OEv} {p : VerifierProgram β} {P : β → Prop}
    (hl : l' = l) (h : RunsO M l p P) : RunsO M l' p P := hl ▸ h

/-- Answers `s … s + m − 1` of a ground group are the lanes `ansAt`. -/
theorem ans_slice {M : Mem} {a k : ℕ} {v : List E}
    (hv : v.map e2OfE = ev2 M (ld2 (a + 1)) :: draws M (a + 10) k) (s m : ℕ) (hsm : s + m ≤ k + 1) :
    ((v.drop s).take m).map e2OfE = (List.range m).map fun j ↦ ev2 M (ansAt a (s + j)) := by
  have hlen : v.length = k + 1 := by
    have := congrArg List.length hv
    simpa [draws] using this
  apply List.ext_getElem
  · simp only [List.length_map, List.length_take, List.length_drop, List.length_range, hlen]
    omega
  · intro j h1 h2
    have hj : s + j < v.length := by
      simp only [List.length_map, List.length_take, List.length_drop, hlen] at h1
      omega
    simp only [List.getElem_map, List.getElem_take, List.getElem_drop, List.getElem_range]
    rw [← ground_ansE hv (j := s + j) (by omega), List.getD_eq_getElem _ _ hj]

/-! ## Fold rounds -/

/-- **A fold round's cells**: the four scalars, `α`, `β`. -/
def roundCells (a : ℕ) : RndC :=
  ⟨ld2 a, ld2 (a + 2), ld2 (a + 4), ld2 (a + 6), ld2 (a + 9), ld2 (a + 18)⟩

/-- **The fold round generator** (no rows). -/
def roundGen (_g a : ℕ) (_gate : Cell) : BM RndC := pure (roundCells a)

theorem runsO_roundP (M : Mem) {g : ℕ} (hg : g ≤ 64) (a : ℕ) :
    RunsO M (layRound g a) (Whir.roundP Whir.chalE2 g) (RndRep M (roundCells a)) := by
  refine runsO_of_eq ?_ (runsO_bind (runsO_readF M a) fun u hu ↦ runsO_bind (runsO_readF M (a + 2))
    fun w hw ↦ runsO_bind (runsO_readF M (a + 4)) fun c0 hc0 ↦ runsO_bind (runsO_readF M (a + 6))
    fun c1 hc1 ↦ runsO_bind (runsO_ground M hg 1 (a + 8)) fun v hv ↦
      runsO_pure (P := RndRep M (roundCells a)) ?_)
  · simp [layRound, layItems, bl, List.range_succ]
  · have h0 := ground_ans hv (j := 0) (by omega)
    have h1 := ground_ans hv (j := 1) le_rfl
    simp only [ansAt] at h0 h1
    refine ⟨hu.symm, hw.symm, hc0.symm, hc1.symm, ?_, ?_⟩
    · exact h0.symm
    · exact h1.symm

/-- **CC-1 proved.** -/
theorem roundHar : RoundHarStmt roundGen := fun g hg a gate c M _ ↦
  hsA_pure (runsO_roundP M hg a)

/-- The cells of `ℓ` rounds from lane `a`, 27 lanes apart. -/
def roundsCells (ℓ a : ℕ) : List RndC := (List.range ℓ).map fun j ↦ roundCells (a + 27 * j)

/-- **`ℓ` fold rounds' generator** (no rows). -/
def roundsGen (_g ℓ a : ℕ) (_gate : Cell) : BM (List RndC) := pure (roundsCells ℓ a)

theorem roundsGen_eq (g ℓ a : ℕ) (gate : Cell) : roundsGen g ℓ a gate = pure (roundsCells ℓ a) := rfl

theorem runsO_roundsP (M : Mem) {g : ℕ} (hg : g ≤ 64) : ∀ (ℓ a : ℕ),
    RunsO M (layRounds g ℓ a) (Whir.roundsP Whir.chalE2 g ℓ) (RndsRep M (roundsCells ℓ a))
  | 0, a => runsO_pure List.Forall₂.nil
  | ℓ + 1, a => by
    have e : roundsCells (ℓ + 1) a = roundCells a :: roundsCells ℓ (a + 27) := by
      simp only [roundsCells, List.range_succ_eq_map, List.map_cons, List.map_map]
      congr 1
      exact List.map_congr_left fun j _ ↦ by simp only [Function.comp_apply, Nat.succ_eq_add_one]; congr 1; ring
    rw [e]
    exact runsO_of_eq (List.append_nil _ ▸ rfl) (runsO_bind (runsO_roundP M hg a) fun r hr ↦
      runsO_bind (runsO_roundsP M hg ℓ (a + 27)) fun rs hrs ↦
        runsO_pure (P := RndsRep M _) (List.Forall₂.cons hr hrs))

/-- **CC-2 proved.** -/
theorem roundsHar : RoundsHarStmt roundsGen := fun g hg ℓ a gate c M _ ↦ by
  rw [roundsGen_eq]
  exact hsA_pure (runsO_roundsP M hg ℓ a)

/-! ## The level interface -/

/-- **The level interface's cells**: the high part from `a`, the OOD point (answers of the group
whose nonce is at `a₂ + 9`), `y`, the positions (`posG` on the query group's first `kq + 1`
answers), `λ` (its answer `kq + 1`), the values (`valsG` on the opened rows). -/
def tailGen {kq : ℕ} (nh ko t : ℕ) (posG : (Fin (kq + 1) → C2) → Cell → BM (List Cell))
    (valsG : List C2 → List Cell → List (List (Option ℕ)) → Cell → BM (List C2))
    (lev : Level) (wdI lvN a : ℕ) (gate : Cell) : BM TailOutC :=
  let a2 := a + 2 * nh + 4 * 2 ^ lvN
  let aq := a2 + 9 + 10 + 9 * ko + 2 * 1
  let hi := (List.range nh).map fun j ↦ ld2 (a + 2 * j)
  posG (fun j ↦ ansAt aq j) gate >>= fun ps ↦
    valsG hi ps (openRows lev wdI (tailOpenAt nh ko kq lvN a - 4) t) gate >>= fun cs ↦
      pure ⟨hi, List.ofFn (fun j : Fin (ko + 1) ↦ ansAt (a2 + 9) j), ld2 (a2 + 9 + 10 + 9 * ko), ps,
        ansAt aq (kq + 1), cs⟩

theorem layTail_eq (nh ko kq t : ℕ) (lev : Level) (wdI ht wd lvN gO gQ a : ℕ) :
    layTail nh ko kq t lev wdI ht wd lvN gO gQ a =
      bl (layItems [.E nh] a) ++ ([.c ht wd] ++ ([.b (.d (a + 2 * nh + 4 * 2 ^ lvN) 0)] ++
        (bl (layItems [.G gO, .D ko] (a + 2 * nh + 4 * 2 ^ lvN + 9)) ++
        (bl (layItems [.E 1] (a + 2 * nh + 4 * 2 ^ lvN + 9 + 10 + 9 * ko)) ++
        (bl (layItems [.G gQ, .D (kq + 1)] (a + 2 * nh + 4 * 2 ^ lvN + 9 + 10 + 9 * ko + 2 * 1)) ++
        ([.o (openRows lev wdI (tailOpenAt nh ko kq lvN a - 4) t)] ++ [])))))) := by
  simp only [layTail, List.append_assoc, List.append_nil, List.cons_append]
  rw [show [Lvm6.V.Item.G gO, Lvm6.V.Item.D ko, Lvm6.V.Item.E 1, Lvm6.V.Item.G gQ, Lvm6.V.Item.D (kq + 1)] =
    [Lvm6.V.Item.G gO, Lvm6.V.Item.D ko] ++ ([Lvm6.V.Item.E 1] ++ [Lvm6.V.Item.G gQ, Lvm6.V.Item.D (kq + 1)]) from rfl,
    layItems_append, layItems_append]
  simp only [bl_append, List.append_assoc, layEnd]

variable {n n' m' : ℕ} (L : Whir.TailIface E2 n n' m')

/-- **The interface runs** for any cells that meet the gadgets' conclusions. -/
theorem runsO_tailP (M : Mem) (vals : List E2 → (Fin L.t → Fin n) → List (List K) → Fin L.t → E2)
    {ht wd i gO gQ : ℕ} (hgO : gO ≤ 64) (hgQ : gQ ≤ 64) (lev : Level) (wdI lvN a : ℕ)
    (ps : List Cell) (cs : List C2)
    (hps : posOf M ps = List.ofFn fun k ↦ (L.pos (fun j ↦ ev2 M
      (ansAt (a + 2 * L.nh + 4 * 2 ^ lvN + 9 + 10 + 9 * L.ko + 2 * 1) j)) k : ℕ))
    (hcs : ∀ p : Fin L.t → Fin n, posOf M ps = List.ofFn (fun k ↦ (p k : ℕ)) →
      cs.map (ev2 M) = List.ofFn (vals (((List.range L.nh).map fun j ↦ ld2 (a + 2 * j)).map (ev2 M)) p
        (rowsOf M (openRows lev wdI (tailOpenAt L.nh L.ko L.kq lvN a - 4) L.t)))) :
    RunsO M (layTail L.nh L.ko L.kq L.t lev wdI ht wd lvN gO gQ a)
      (Whir.tailP L Whir.chalE2 ht wd i gO gQ vals)
      (TailRep M ⟨(List.range L.nh).map fun j ↦ ld2 (a + 2 * j),
        List.ofFn (fun j : Fin (L.ko + 1) ↦ ansAt (a + 2 * L.nh + 4 * 2 ^ lvN + 9) j),
        ld2 (a + 2 * L.nh + 4 * 2 ^ lvN + 9 + 10 + 9 * L.ko), ps,
        ansAt (a + 2 * L.nh + 4 * 2 ^ lvN + 9 + 10 + 9 * L.ko + 2 * 1) (L.kq + 1), cs⟩) := by
  rw [layTail_eq]
  refine runsO_bind (runsO_readFs M L.nh a) fun hi hhi ↦ runsO_bind (runsO_commit M ht wd)
    fun _ _ ↦ runsO_bind (runsO_sep M _) fun _ _ ↦ runsO_bind (runsO_ground M hgO L.ko _)
    fun zv hzv ↦ runsO_bind (runsO_readF M _) fun y hy ↦ runsO_bind (runsO_ground M hgQ (L.kq + 1) _)
    fun qv hqv ↦ runsO_bind (runsO_query M i _ _) fun rows hrows ↦ runsO_pure ?_
  have hq : (fun j : Fin (L.kq + 1) ↦ ev2 M
      (ansAt (a + 2 * L.nh + 4 * 2 ^ lvN + 9 + 10 + 9 * L.ko + 2 * 1) j)) =
      fun k : Fin (L.kq + 1) ↦ qv.getD k 0 := by
    funext j
    exact (ground_ans hqv (j := j) (by omega)).symm
  have hhi' : ((List.range L.nh).map fun j ↦ ld2 (a + 2 * j)).map (ev2 M) = hi := by
    rw [hhi, List.map_map]
    rfl
  refine ⟨hhi', ?_, hy.symm, ?_, (ground_ans hqv le_rfl).symm, ?_⟩
  · rw [List.map_ofFn]
    congr 1
    funext j
    exact (ground_ans hzv (j := j) (by omega)).symm
  · show posOf M ps = List.ofFn fun k ↦ (Whir.qPos L qv k : ℕ)
    rw [hps, hq]
    rfl
  · show cs.map (ev2 M) = List.ofFn (vals hi (Whir.qPos L qv) rows)
    rw [hcs (Whir.qPos L qv) (by rw [hps, hq]; rfl), hhi', hrows]

/-- **CC-3 proved**: the interface generator re-executes `tailP`. -/
theorem tailHar : TailHarStmt L (tailGen L.nh L.ko L.t) := by
  intro vals posG valsG hpos hvals ht wd i gO gQ hgO hgQ lev wdI lvN a gate c M hgate
  exact hsA_bind (hpos c M _ gate hgate) fun ps hps ↦ hsA_bind (hvals c M _ ps _ gate hgate)
    fun cs hcs ↦ hsA_pure (runsO_tailP L M vals hgO hgQ lev wdI lvN a ps cs hps hcs)

/-! ## One level -/

/-- **One level's cells**: `ℓ` rounds from `a`, then the interface at `a + 27ℓ`, whose value
gadget reads the rounds' cells. -/
def levelGen {kq : ℕ} (nh ko t : ℕ) (posG : (Fin (kq + 1) → C2) → Cell → BM (List Cell))
    (valsG : List RndC → List C2 → List Cell → List (List (Option ℕ)) → Cell → BM (List C2))
    (g ℓ : ℕ) (lev : Level) (wdI lvN a : ℕ) (gate : Cell) : BM (List RndC × TailOutC) :=
  roundsGen g ℓ a gate >>= fun rc ↦
    tailGen nh ko t posG (valsG rc) lev wdI lvN (a + 27 * ℓ) gate >>= fun o ↦ pure (rc, o)

/-- **CC-4 proved**: the level generator re-executes `levelP`. -/
theorem levelHar : LevelHarStmt L (levelGen L.nh L.ko L.t) := by
  intro vals posG valsG hpos hvals g ht wd i gO gQ ℓ hg hgO hgQ lev wdI lvN a gate c M hgate
  unfold levelGen
  rw [roundsGen_eq]
  refine hsA_bind (hsA_pure (P := fun rc ↦ rc = roundsCells ℓ a) rfl) fun rc hrc ↦ ?_
  subst hrc
  refine hsA_bind (P := fun o ↦ ∀ rs, RndsRep M (roundsCells ℓ a) rs →
      RunsO M (layTail L.nh L.ko L.kq L.t lev wdI ht wd lvN gO gQ (a + 27 * ℓ))
        (Whir.tailP L Whir.chalE2 ht wd i gO gQ (vals rs)) (TailRep M o)) ?_ fun o ho ↦ hsA_pure ?_
  · dsimp only [tailGen]
    refine hsA_bind (hpos c M _ gate hgate) fun ps hps ↦ hsA_bind (P := fun cs ↦
        ∀ rs, RndsRep M (roundsCells ℓ a) rs → ∀ p : Fin L.t → Fin n,
        posOf M ps = List.ofFn (fun k ↦ (p k : ℕ)) → cs.map (ev2 M) = List.ofFn (vals rs
          (((List.range L.nh).map fun j ↦ ld2 (a + 27 * ℓ + 2 * j)).map (ev2 M)) p
          (rowsOf M (openRows lev wdI (tailOpenAt L.nh L.ko L.kq lvN (a + 27 * ℓ) - 4) L.t))))
      (fun p hh ha rs hrs ↦ hvals c M _ rs hrs _ ps _ gate hgate p hh ha) fun cs hcs ↦
        hsA_pure fun rs hrs ↦ runsO_tailP L M (vals rs) hgO hgQ lev wdI lvN (a + 27 * ℓ) ps cs hps
          (hcs rs hrs)
  · exact runsO_of_eq (by rw [List.append_nil]) (runsO_bind (runsO_roundsP M hg ℓ a) fun rs hrs ↦
      runsO_bind (ho rs hrs) fun o' ho' ↦ runsO_pure (P := LevelRep M (roundsCells ℓ a, o)) ⟨hrs, ho'⟩)

/-! ## The ring group -/

/-- **The ring group's cells**: answers `0–7` (`f`), `8–15` (`g`), `16` (`λ₀`). -/
def ringCells (a : ℕ) : RingC :=
  ⟨(List.range 8).map (ansAt a), (List.range 8).map fun j ↦ ansAt a (8 + j), ansAt a 16⟩

/-- **The ring group generator** (no rows). -/
def ringGen (_g a : ℕ) (_gate : Cell) : BM RingC :=
  pure (ringCells a)

theorem runsO_readScalar (M : Mem) (a : ℕ) :
    RunsO M [.b (.k a)] VerifierProgram.readScalar fun _ ↦ True := fun _ evs he ↦ by
  cases he with
  | cons hx hr =>
    cases hr
    rename_i ev
    cases ev with
    | read x => exact ⟨x, rfl, trivial⟩
    | _ => exact absurd hx (by simp [OEvM, EvM])

theorem runsO_ringProg (M : Mem) {g : ℕ} (hg : g ≤ 64) (a : ℕ) :
    RunsO M (layRing g a) (Ring.ringProg g) (RingRep M (ringCells a)) := by
  intro hpw
  have e : layRing g a = [.b (.k a)] ++ (([.b (.d (a + 1) g)] ++
      (bl ((List.range 16).map fun i ↦ LEv.d (a + 10 + 9 * i) 0) ++ [])) ++ ([] ++ [])) := by
    simp [layRing, layItems, bl]
  have hpow : kToNat (lk M (a + 1 + 2)) < 2 ^ (64 - g) := hpw (a + 1) g (by rw [e]; simp)
  rw [e] at hpw ⊢
  have hS : RunsO M ([.b (.d (a + 1) g)] ++
      (bl ((List.range 16).map fun i ↦ LEv.d (a + 10 + 9 * i) 0) ++ []))
      (VerifierProgram.sampleChallenges 17) (fun cs ↦ cs.map e2OfE =
        ev2 M (ld2 (a + 1)) :: draws M (a + 10) 16 ∧ powOK g (cs.headD 0)) := by
    show RunsO M _ (VerifierProgram.sampleChallenge >>= fun x ↦
      VerifierProgram.sampleChallenges 16 >>= fun xs ↦ pure (x :: xs)) _
    refine runsO_bind (runsO_sample M (a + 1) g) fun x hx ↦ runsO_bind (runsO_samples M 16 (a + 10))
      fun xs hxs ↦ runsO_pure ⟨by rw [List.map_cons, hx.1, hxs], ?_⟩
    rw [List.headD_cons, powOK_iff_lane2 hg, hx.2]
    exact hpow
  unfold Ring.ringProg
  refine runsO_bind (p := VerifierProgram.readScalar) (runsO_readScalar M a) (fun _ _ ↦
    runsO_bind (p := VerifierProgram.sampleChallenges 17) hS fun cs hcs ↦
      runsO_bind (runsO_require hcs.2) fun _ _ ↦ runsO_pure ?_) hpw
  have hf := ans_slice hcs.1 0 8 (by omega)
  have hg' := ans_slice hcs.1 8 8 (by omega)
  simp only [List.drop_zero, Nat.zero_add] at hf
  refine ⟨?_, ?_, ?_⟩
  · show ((List.range 8).map (ansAt a)).map (ev2 M) = (cs.take 8).map e2OfE
    rw [hf, List.map_map]
    rfl
  · show ((List.range 8).map fun j ↦ ansAt a (8 + j)).map (ev2 M) = ((cs.drop 8).take 8).map e2OfE
    rw [hg', List.map_map]
    rfl
  · exact (ground_ansE hcs.1 (j := 16) (by omega)).symm

/-- **CC-5 proved.** -/
theorem ringHar : RingHarStmt ringGen := fun _ hg a _ _ M _ ↦
  hsA_pure (runsO_ringProg M hg a)

end Lvm6.QC
