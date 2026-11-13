-- New for lvm (WP-14a, H0): the phases of `P_S` follow the schedule's items (`Fol`, LvmVEqShape). lvm2 roll 8 (B1,
-- wave L, L-C): the schedule's `bus`/`tables` phases are the typed items (`zeroI` … `miniTabI`); the bus path's
-- `folP_midS`/`midFollows_midS` are gone (dead at the refreeze `S2GB1`), the typed ones are `LvmTypedVEqFol`'s.
import LvmVEqFol
import LvmVEqFit
import LvmVEqRel

/-!
# The phases follow the schedule

The phases' items of `LvmSchedule.phases` by name (`commitI`; the typed `zeroI`, `wiringI`, `relayI`, `accI`,
`miniBusI`, `miniTabI`, `typedI`; `tapeI`, …, `openMainI`; `phases_eq` by `rfl`, `schedule_eq`, `midItems_eq`), and
per program a `FolP` (from every `pp`, the program follows the phase's atoms and keeps `pp`):

* `folP_lvmBusProg`, `folP_tablePhaseClaims`, `folP_accProg`: WP-9b's bus phase, the table phase, A23's phase
  (the typed mini-bus and A23 at `Φ_Q` use them, `LvmTypedVEqFol`);
* `folP_tapeProg` (lvm2 S2: `folP_tapeGkr`, `folP_wireChProg`), `folP_callerProg`, `folP_ksLinkProg`,
  `folP_kgProgS`: the tape caller and WP-8's `KS` programs against `tapeI ++ wireI ++ ksI ++ ksLinkI`;
* `midItems_noPos`: `midItems` has no positions item.
-/

set_option autoImplicit false

namespace Lvm.VEq

open LeanVM.Parameters LeanVM.Protocol LeanVM.Protocol.Compile

/-! ## The phases' items -/

section Items

variable (p : Params)

/-- The commit phase: `C_main`'s root cap (lvm2 roll 11, M′ `S2GM`: one commitment; B1 also sent `C_rec`'s). -/
def commitI : List Item := [.cap (p.level ⟨.main, 0⟩).cap ⟨.main, 0⟩]
/-- The bus phase (roll 7's; the typed mini-bus's grand product has the same items, `miniBusI`). -/
def busI : List Item := List.flatten [smp (busBits + 1), gpI p.busDepth, rd p.leafdecReads]
/-- The tape (lvm2 S2, T1–T2). -/
def tapeI : List Item := List.flatten [smp p.logN, rd lanes, tapeLayersI p.logN]
/-- The wire (lvm2 S2, T3–T4). -/
def wireI : List Item := List.flatten [sumcheckI p.logN 2, rd 1, sumcheckI 2 2, rd kBits, smp ringStages]
/-- `KS`'s Keccak GKR. -/
def ksI : List Item := List.flatten [smp p.ksLog, rd lanes, keccakI p.ksLog, smp ringStages]
/-- The `KS` link. -/
def ksLinkI : List Item := List.flatten [smp (p.ksLog + laneBits), sumcheckI p.ksLog 2, rd 4]
/-- `C_main`'s opening (with the OOD samples when `p.mainOod`, lvm2 JB-VQP). -/
def openMainI : List Item :=
  smp 1 ++ (if p.mainOod then whirIJ else whirI) .main p.mainLevels p.mainFinalLog p.grind

/-! The typed items (lvm2 roll 8, B1, refreeze `S2GB1`: `LvmSchedule.phases` carries `LvmTypedVSched.phasesT`'s items
under the old phase names; `bus`: zerocheck, wiring, relayout, A23 at `Φ_Q`, the mini-bus's grand product;
`tables`: the mini-bus's table phase). -/

/-- The zerocheck: `τ`, 20 equality-mode rounds of 2 scalars, `a*, b*, c*`. -/
def zeroI : List Item := List.flatten [smp 20, sumcheckI 20 2, rd 3]
/-- The wiring: `γ`, 21 rounds of 2 scalars, the 4 matrix values, the 4 region values. -/
def wiringI : List Item := List.flatten [smp 1, sumcheckI 21 2, rd 4, rd 4]
/-- The relayout: 19 rounds of 2 scalars, `v_R`. -/
def relayI : List Item := List.flatten [sumcheckI 19 2, rd 1]
/-- A23 at `Φ_Q`: `κ`, `h` (`accVars + 1 = 44` coefficients), `t`, the zero scalar. -/
def accI : List Item := List.flatten [smp 2, rd (accVars + 1), smp 1, rd 1]
/-- The mini-bus's grand product (`busI`'s items at the record's depth). -/
def miniBusI : List Item := List.flatten [smp (busBits + 1), gpI p.busDepth, rd p.leafdecReads]
/-- The mini-bus's table phase. -/
def miniTabI : List Item := List.flatten [smp 1, sumcheckI p.tableRounds 3, rd p.tableEvals]
/-- **The typed phases' items** (the schedule's `bus` and `tables` phases). -/
def typedI : List Item := zeroI ++ (wiringI ++ (relayI ++ (accI ++ (miniBusI p ++ miniTabI p))))

/-- **The schedule by phase** (lvm2 roll 11, M′ `S2GM`: one root cap, no `openRec` phase; roll 8, B1: the typed
items under `bus` and `tables`; roll 7: `busI`, `tablesI`). -/
theorem phases_eq : phases p = [(.commit, commitI p), (.bus, zeroI ++ (wiringI ++ (relayI ++ (accI ++ miniBusI p)))),
    (.tables, miniTabI p), (.tape, tapeI p), (.wire, wireI p), (.ks, ksI p), (.ksLink, ksLinkI p),
    (.openMain, openMainI p)] := by
  rfl

/-- The schedule, item list by item list. -/
theorem schedule_eq : schedule p = commitI p ++ (typedI p ++ (tapeI p ++ (wireI p ++ (ksI p ++ (ksLinkI p ++
    (openMainI p ++ [])))))) := by
  rw [schedule, phases_eq]
  simp only [typedI, List.flatMap_cons, List.flatMap_nil, List.append_assoc, List.append_nil]
end Items

/-- **The middle phases' items**: the typed phases, then the tape, the wire, `KS`, the `KS` link. -/
theorem midItems_eq : Lvm.ASM.midItems =
    typedI P20 ++ (tapeI P20 ++ (wireI P20 ++ (ksI P20 ++ (ksLinkI P20 ++ [])))) := by
  rw [show Lvm.ASM.midItems = (((phases P20).drop 1).take 6).flatMap (·.2) from rfl, phases_eq]
  simp only [typedI, List.drop_succ_cons, List.drop_zero, List.take_succ_cons, List.take_zero,
    List.flatMap_cons, List.flatMap_nil, List.append_assoc, List.append_nil]

/-! ## The bus phase and the table sumcheck -/

section BusTables

variable {cap : ℕ → ℕ → ℕ} {shp : ℕ → ℕ × ℕ} {idx : Ref → ℕ} (p : Params)

theorem folP_abProg : FolP cap shp idx EndToEnd.Front.abProg (List.replicate (busBits + 1) .sm) fun _ ↦ True := by
  rw [List.replicate_succ']
  exact (folP_sampleChallenges 4).bind fun _ _ ↦ folP_sampleChallenge.bind_ret fun _ _ ↦ trivial

/-- **The bus phase** against `busI`. -/
theorem folP_lvmBusProg (hl : p.leafdecReads = 1) :
    FolP cap shp idx (M3.lvmBusProg p.busDepth) (atomsOf p (busI p)) fun _ ↦ True := by
  simp only [busI, List.flatten_cons, List.flatten_nil, List.append_nil, atomsOf_append, atomsOf_smp,
    atomsOf_rd, hl]
  unfold M3.lvmBusProg
  exact folP_abProg.bind fun _ _ ↦ (folP_verifyGkrGrandProducts p _).bind fun _ _ ↦
    (folP_require _).bind fun _ _ ↦ folP_readScalar.bind_nil fun _ _ ↦
    (folP_require _).bind_nil fun _ _ ↦ FolP.ret trivial

theorem folP_tableTermsClaims (tables : List Verifier.Table) (cp fp point : List E) :
    ∀ (rows : List (Verifier.Table × ℕ × List Verifier.Form × E)) (cursor : ℕ) (final : E)
      (claims : List Verifier.ColumnClaim),
      FolP cap shp idx (Verifier.tableTermsClaims tables cp fp point rows cursor final claims)
        (List.replicate (rows.map fun r ↦ r.1.width).sum .rd) fun _ ↦ True
  | [], _, _, _ => FolP.ret trivial
  | r :: rows, cursor, final, claims => by
    rw [List.map_cons, List.sum_cons, List.replicate_add]
    unfold Verifier.tableTermsClaims
    exact (folP_readScalars _).bind fun _ _ ↦ folP_tableTermsClaims tables cp fp point rows _ _ _

theorem length_tableWeights (heights : List ℕ) (eqp point : List E) :
    (Verifier.tableWeights heights eqp point).length = heights.length := by
  unfold Verifier.tableWeights
  suffices h : ∀ (l : List (E × ℕ)) (acc : List E), acc.length = heights.length →
      (l.foldl (fun weights (x : E × ℕ) ↦
        List.zipWith (fun weight height ↦ weight * if x.2 < height then 1 + eqp.getD x.2 0 + x.1 else x.1)
          weights heights) acc).length = heights.length from h _ _ (by simp)
  intro l
  induction l with
  | nil => intro acc h; exact h
  | cons x l ih => intro acc h; exact ih _ (by simp [h])

theorem folP_tableSumcheckClaims (tables : List Verifier.Table) (heights : List ℕ)
    (busForms : List (List Verifier.Form)) (cp fp eqp : List E) (target : E)
    (hh : tables.length ≤ heights.length) (hb : tables.length ≤ busForms.length) :
    FolP cap shp idx (Verifier.tableSumcheckClaims tables heights busForms cp fp eqp target)
      (atomsOf p (sumcheckI (heights.foldl max 0) 3) ++ List.replicate (tables.map (·.width)).sum .rd)
      fun _ ↦ True := by
  unfold Verifier.tableSumcheckClaims
  refine (folP_sumcheck p rfl (by norm_num) _ _ _ (List.length_replicate ..)).bind fun x _ ↦ ?_
  have hrows : ((List.zip tables (List.zip heights (List.zip busForms
      (Verifier.tableWeights heights eqp x.1.reverse)))).map fun r ↦ r.1.width) = tables.map (·.width) := by
    rw [show (fun r : Verifier.Table × ℕ × List Verifier.Form × E ↦ r.1.width) =
      Verifier.Table.width ∘ Prod.fst from rfl, ← List.map_map, List.map_fst_zip]
    simp [length_tableWeights]; omega
  rw [← List.append_nil (List.replicate _ _), ← hrows]
  exact (folP_tableTermsClaims _ _ _ _ _ _ _ _).bind fun _ _ ↦ (folP_require _).bind_nil fun _ _ ↦
    FolP.ret trivial

theorem folP_tablePhaseClaims (tables : List Verifier.Table) (layout : Verifier.Layout)
    (bus : Verifier.BusResult) (hh : tables.length ≤ layout.tableLogHeights.length)
    (hb : tables.length ≤ bus.forms.length) :
    FolP cap shp idx (Verifier.tablePhaseClaims tables layout bus)
      (.sm :: (atomsOf p (sumcheckI (layout.tableLogHeights.foldl max 0) 3) ++
        List.replicate (tables.map (·.width)).sum .rd)) fun _ ↦ True := by
  unfold Verifier.tablePhaseClaims
  exact folP_sampleChallenge.bind fun _ _ ↦
    (folP_tableSumcheckClaims p _ _ _ _ _ _ _ hh hb).bind_ret fun _ _ ↦ trivial

theorem width_vTables (T : List M3.Tab) : ((M3.vTables T).map (·.width)).sum = (T.map (·.w)).sum := by
  suffices h : ∀ k, ((T.zipIdx k).map fun x ↦ x.1.w) = T.map (·.w) by
    simp [M3.vTables, M3.vTable, Verifier.Table.width, List.map_map, Function.comp_def, h]
  induction T with
  | nil => intro; rfl
  | cons t T ih => intro k; simp [List.zipIdx_cons, ih]

/-- **Phase 3b** (AC-S's `accProg`) against its items. -/
theorem folP_accProg (dk D : ℕ) (ok : Bool) (yIn : E) (a : List E) (yOwn : List E → E)
    (bOf : List E → List E) (Φ : List E → E) :
    FolP cap shp idx (Lvm.Acc.accProg dk D ok yIn a yOwn bOf Φ)
      (atomsOf p (List.flatten [smp dk, rd (D + 1), smp 1, rd 1])) fun _ ↦ True := by
  simp only [List.flatten_cons, List.flatten_nil, List.append_nil, atomsOf_append, atomsOf_smp,
    atomsOf_rd]
  unfold Lvm.Acc.accProg
  exact (folP_sampleChallenges dk).bind fun _ _ ↦ (folP_readScalars (D + 1)).bind fun _ _ ↦
    folP_sampleChallenge.bind fun _ _ ↦ folP_readScalar.bind_nil fun _ _ ↦
      (folP_require _).mono fun _ _ ↦ trivial

end BusTables

/-! ## The Keccak phases (WP-8's `kgSpec` program) -/

section Kg

variable {cap : ℕ → ℕ → ℕ} {shp : ℕ → ℕ × ℕ} {idx : Ref → ℕ} (p : Params)

/-- **The Keccak phase with caller claims** against `smp h, rd lanes, keccakI h, smp ringStages`. -/
theorem folP_callerProg (h : ℕ) :
    FolP cap shp idx (KG.callerProg h) (atomsOf p (List.flatten [smp h, rd lanes, keccakI h, smp ringStages]))
      fun _ ↦ True := by
  simp only [List.flatten_cons, List.flatten_nil, List.append_nil, atomsOf_append, atomsOf_smp, atomsOf_rd]
  unfold KG.callerProg
  exact (folP_sampleChallenges h).bind fun r hr ↦ (folP_readScalars 25).bind fun v _ ↦
    (folP_verifyKeccak p h r v hr).bind fun _ _ ↦ (folP_ringSwitch _ _).bind_ret fun _ _ ↦ trivial

/-- **The `KS` link** against its items. -/
theorem folP_ksLinkProg (hk xl : ℕ) (rows : List ℕ) :
    FolP cap shp idx (KG.ksLinkProg hk xl rows)
      (atomsOf p (List.flatten [smp (hk + laneBits), sumcheckI hk 2, rd 4])) fun _ ↦ True := by
  simp only [List.flatten_cons, List.flatten_nil, List.append_nil, atomsOf_append, atomsOf_smp, atomsOf_rd]
  unfold KG.ksLinkProg
  exact (folP_sampleChallenges _).bind fun _ _ ↦
    (folP_sumcheck p rfl (by norm_num) _ hk _ (List.length_replicate ..)).bind fun _ _ ↦
    (folP_readScalars 4).bind_nil fun _ _ ↦ (folP_require _).bind_nil fun _ _ ↦ FolP.ret trivial

/-- **A generic Keccak layer** (T-G's `verifyKeccakLayerS`) against `keccakLayerI`. -/
theorem folP_verifyKeccakLayerS (sh : KeccakGkr.Shape) (logSteps step : ℕ) (claim : Verifier.KeccakClaim) :
    FolP cap shp idx (KeccakGkr.verifyKeccakLayerS sh logSteps step claim)
      (atomsOf p (keccakLayerI claim.point.length)) fun c ↦ c.point.length = claim.point.length := by
  simp only [keccakLayerI, List.flatten_cons, List.flatten_nil, List.append_nil, atomsOf_append,
    atomsOf_rd, atomsOf_smp]
  unfold KeccakGkr.verifyKeccakLayerS
  exact (folP_readScalars _).bind fun _ _ ↦ (folP_require _).bind fun _ _ ↦
    folP_sampleChallenge.bind fun _ _ ↦ (folP_keccakPackRounds p claim.point _ _).bind fun x hx ↦
    (folP_sumcheck p rfl (by norm_num) _ localBits _ (List.length_replicate ..)).bind fun _ _ ↦
    (folP_readScalars 3).bind fun _ _ ↦ (folP_require _).bind fun _ _ ↦
    folP_sampleChallenge.bind_ret fun _ _ ↦ hx

theorem folP_keccakLayersS (sh : KeccakGkr.Shape) (logSteps : ℕ) :
    ∀ (steps : List ℕ) (claim : Verifier.KeccakClaim),
    FolP cap shp idx (KeccakGkr.keccakLayersS sh logSteps steps claim)
      (List.replicate steps.length (atomsOf p (keccakLayerI claim.point.length))).flatten
      fun c ↦ c.point.length = claim.point.length
  | [], _ => FolP.ret rfl
  | st :: steps, claim => by
    rw [List.length_cons, List.replicate_succ, List.flatten_cons]
    exact (folP_verifyKeccakLayerS p sh logSteps st claim).bind fun c hc ↦ by
      rw [← hc]
      exact folP_keccakLayersS sh logSteps steps c

/-- **The tape's GKR** (T-G's `tapeGkr`) against `tapeLayersI`, the instance point of `logSteps`
coordinates. -/
theorem folP_tapeGkr (logSteps : ℕ) (inst output : List E) (hinst : inst.length = logSteps) :
    FolP cap shp idx (KeccakGkr.tapeGkr logSteps inst output) (atomsOf p (tapeLayersI logSteps))
      fun _ ↦ True := by
  rw [KeccakGkr.tapeGkr_eq]
  simp only [tapeLayersI, atomsOf_append, atomsOf_smp, atomsOf_flatten, List.map_replicate]
  refine (folP_sampleChallenges _).bind fun lp _ ↦ ?_
  have hpt' : (KeccakGkr.tapeFirstClaim inst lp output).point.length = logSteps - packBits := by
    simp only [KeccakGkr.tapeFirstClaim, List.length_drop, hinst]; rfl
  rw [← hpt', show tapeDepth = (List.range 24).length by simp; rfl]
  exact (folP_keccakLayersS p KeccakGkr.Shape.tape logSteps _ _).mono fun _ _ ↦ trivial

/-- **T-W's slot reduction** (two lane bits) against its items. -/
theorem folP_slotProg (sb blk : ℕ) (W : ℕ → ℕ → E) (pt : List E) (v : E) :
    FolP cap shp idx (KG.slotProg 2 sb blk W pt v)
      (atomsOf p (List.flatten [sumcheckI 2 2, rd kBits, smp ringStages])) fun _ ↦ True := by
  simp only [List.flatten_cons, List.flatten_nil, List.append_nil, atomsOf_append, atomsOf_smp, atomsOf_rd]
  unfold KG.slotProg
  exact (folP_sumcheck p rfl (by norm_num) _ 2 _ (List.length_replicate ..)).bind fun _ _ ↦
    (folP_readScalars 64).bind fun _ _ ↦ (folP_require _).bind fun _ _ ↦
    (folP_ringSwitch _ _).bind_ret fun _ _ ↦ trivial

/-- **T-W's wiring phase** against `wireI`'s items. -/
theorem folP_wireChProg (w sb dsel : ℕ) (s : RecursionFast.Digest) (n : ℕ) (claim : Verifier.KeccakClaim) :
    FolP cap shp idx (KG.wireChProg w sb dsel s n claim)
      (atomsOf p (List.flatten [sumcheckI w 2, rd 1, sumcheckI 2 2, rd kBits, smp ringStages]))
      fun _ ↦ True := by
  have e : atomsOf p (List.flatten [sumcheckI w 2, rd 1, sumcheckI 2 2, rd kBits, smp ringStages]) =
      atomsOf p (sumcheckI w 2) ++ (List.replicate 1 .rd ++
        atomsOf p (List.flatten [sumcheckI 2 2, rd kBits, smp ringStages])) := by
    simp only [List.flatten_cons, List.flatten_nil, List.append_nil, atomsOf_append, atomsOf_rd,
      atomsOf_smp, List.append_assoc]
  rw [e]
  unfold KG.wireChProg
  exact (folP_sumcheck p rfl (by norm_num) _ w _ (List.length_replicate ..)).bind fun _ _ ↦
    (folP_readScalars 1).bind fun _ _ ↦ (folP_require _).bind fun _ _ ↦
    (folP_slotProg p _ _ _ _ _).bind_ret fun _ _ ↦ trivial

/-- **The tape caller** (lvm2 S2, `tapeProg`) against the tape's and the wire's items. -/
theorem folP_tapeProg (w sb dsel : ℕ) (s : RecursionFast.Digest) (n : ℕ) :
    FolP cap shp idx (KG.tapeProg w sb dsel s n)
      (atomsOf p (List.flatten [smp w, rd lanes, tapeLayersI w]) ++
        atomsOf p (List.flatten [sumcheckI w 2, rd 1, sumcheckI 2 2, rd kBits, smp ringStages]))
      fun _ ↦ True := by
  have e : atomsOf p (List.flatten [smp w, rd lanes, tapeLayersI w]) ++
        atomsOf p (List.flatten [sumcheckI w 2, rd 1, sumcheckI 2 2, rd kBits, smp ringStages]) =
      List.replicate w .sm ++ (List.replicate 25 .rd ++ (atomsOf p (tapeLayersI w) ++
        atomsOf p (List.flatten [sumcheckI w 2, rd 1, sumcheckI 2 2, rd kBits, smp ringStages]))) := by
    simp only [List.flatten_cons, List.flatten_nil, List.append_nil, atomsOf_append, atomsOf_rd,
      atomsOf_smp, List.append_assoc]; rfl
  rw [e]
  unfold KG.tapeProg
  exact (folP_sampleChallenges w).bind fun r hr ↦ (folP_readScalars 25).bind fun v _ ↦
    (folP_tapeGkr p w r v hr).bind fun _ _ ↦ (folP_require _).bind fun _ _ ↦
    (folP_wireChProg p _ _ _ _ _ _).bind_ret fun _ _ ↦ trivial

/-- **V_S phases 4–7** (`kgProgS`, lvm2 S2) against the tape, the wire, `KS`, the `KS` link at
`P20`. -/
theorem folP_kgProgS (s : RecursionFast.Digest) (n : ℕ) :
    FolP cap shp idx (kgProgS s n) (atomsOf P20 (tapeI P20 ++ (wireI P20 ++ (ksI P20 ++ ksLinkI P20))))
      fun _ ↦ True := by
  have e : atomsOf P20 (tapeI P20 ++ (wireI P20 ++ (ksI P20 ++ ksLinkI P20))) =
      (atomsOf P20 (tapeI P20) ++ atomsOf P20 (wireI P20)) ++
        (atomsOf P20 (ksI P20) ++ atomsOf P20 (ksLinkI P20)) := by
    simp only [atomsOf_append, List.append_assoc]
  rw [e]
  unfold kgProgS
  exact (folP_tapeProg P20 20 1 0 s n).bind fun _ _ ↦
    (FolP.bind (S := fun _ ↦ True) (folP_callerProg P20 (9 + 4)) fun _ _ ↦
      (folP_ksLinkProg P20 (9 + 4) 9 _).bind_ret fun _ _ ↦ trivial).bind_ret fun _ _ ↦ trivial

end Kg

/-! ## The middle phases -/

section Mid

variable {cap : ℕ → ℕ → ℕ} {shp : ℕ → ℕ × ℕ} {idx : Ref → ℕ}

/-- Is the item a positions item. -/
def isPos : Item → Bool
  | .positions _ => true
  | _ => false

theorem midItems_noPosB : Lvm.ASM.midItems.all (fun it ↦ !isPos it) = true := by decide +kernel

theorem midItems_noPos : ∀ it ∈ Lvm.ASM.midItems, ∀ r, it ≠ .positions r := by
  intro it hit r heq
  have := List.all_eq_true.mp midItems_noPosB it hit
  subst heq
  simp [isPos] at this

end Mid

end Lvm.VEq
