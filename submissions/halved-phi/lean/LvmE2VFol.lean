-- New for lvm2 E2-FT (E2F-V2-FOL): S2GF's `P_S` (`PSWithM (midP (midM reloc (midF₂ Ti)))`) follows S2GF's schedule
-- (`Fol`, LvmVEqShape) at `P20F.withF accVF`: the pin, the coordinate-split typed phases, the `E2` front
-- (LvmE2VFolFront), `C_main`'s opening (roll 11's); the static check `stA` and the read widths `rwF20`.
import LvmE2VFolFront
import LvmE2FPin
import LvmMPVEq
import LvmTypedVEqTop

/-!
# S2GF's `P_S` follows the schedule

At `P20F.withF accVF` (S2GF's record: `P20`'s levels, stage `1`, A23 at 44 variables):

* the schedule by phase (`phasesF_eq`, `scheduleF_eq`; the items `pinI`, `zeroIX`, `wiringIX`, `accIX`, `typedIX`,
  `midItemsF`; the front's `tapeIF` … `ksLinkIF` are LvmE2VFolFront's);
* `folP_zeroProgX`, `folP_wireProgX`, `folP_accProgQX`, **`folP_typedProgX`**: the coordinate-split typed phases
  (`ω`, 6 values at `r_x`, 8 matrix values, `κ` of 3, `h` of `accV + 1 = 45`) against `typedIX`;
* `folP_pinProg`, `folP_midP`, `folP_midF₂`, **`folP_midPF`**: the pinned middle phases against `midItemsF`;
  **`fol_PSOfF`**: the whole `P_S` against the whole schedule (roll 11's `fol_PSOfM` pattern, `C_main`'s opening at
  `P20`'s levels);
* **`stA_P20F`**: the static check, one kernel evaluation on the record with literal levels (`PF_eq`);
* `widthsA_atomsOf` (the atoms' read widths are the items'), **`wAt_rwF20`** (`rwF20` reads them), and
  `mem_widthsA_pinF`, `mem_widthsA_typedF`, `mem_widthsA_openF` (those phases read 24-byte scalars only).

A `Fol` at concrete atoms is applied with `@` (the default application elaborator would unfold it).
-/

set_option autoImplicit false

namespace Lvm.VEq

open LeanVM.Parameters LeanVM.Protocol LeanVM.Protocol.Compile
open LeanVM.Protocol.Whir.Sound (cfgMain24G cfgMain23Jq)
open Lvm.E2V

/-! ## The S2GF items -/

section Items

variable (p : Params)

/-- The root OOD pin: `ν` samples, one read. -/
def pinI : List Item := smp p.nuMain ++ rd 1
/-- The coordinate-split zerocheck: `τ` (20), `ω`, 20 equality-mode rounds of 2, the six values at `r_x`. -/
def zeroIX : List Item := List.flatten [smp 20, smp 1, sumcheckI 20 2, rd 6]
/-- The coordinate-split wiring: `γ`, 21 rounds of 2, the 8 matrix and 4 region values. -/
def wiringIX : List Item := List.flatten [smp 1, sumcheckI 21 2, rd 8, rd 4]
/-- A23: `κ` (3), `h` (`accV + 1`), `t`, the zero scalar. -/
def accIX : List Item := List.flatten [smp 3, rd (p.accV + 1), smp 1, rd 1]
/-- **The typed phases' items at S2GF** (the schedule's `bus` and `tables` phases). -/
def typedIX : List Item := zeroIX ++ (wiringIX ++ (relayI ++ (accIX p ++ (miniBusI p ++ miniTabI p))))
/-- **The pinned middle phases' items**: the pin, the typed phases, the tape, the wire, `KS`, the `KS` link. -/
def midItemsF : List Item := pinI p ++ (typedIX p ++ (tapeIF p ++ (wireIF p ++ (ksIF p ++ ksLinkIF p))))

/-- **S2GF's schedule by phase.** -/
theorem phasesF_eq (h : p.stage = 1) : phases p = [(.commit, commitI p ++ pinI p),
    (.bus, zeroIX ++ (wiringIX ++ (relayI ++ (accIX p ++ miniBusI p)))), (.tables, miniTabI p), (.tape, tapeIF p),
    (.wire, wireIF p), (.ks, ksIF p), (.ksLink, ksLinkIF p), (.openMain, openMainI p)] := by
  rw [phases, h]
  rfl

/-- S2GF's schedule: the root, the pinned middle phases, `C_main`'s opening. -/
theorem scheduleF_eq (h : p.stage = 1) : schedule p = commitI p ++ (midItemsF p ++ (openMainI p ++ [])) := by
  rw [schedule, phasesF_eq p h]
  simp only [midItemsF, typedIX, List.flatMap_cons, List.flatMap_nil, List.append_assoc, List.append_nil]

end Items

/-! ## The coordinate-split typed phases -/

section Typed

variable {cap : ℕ → ℕ → ℕ} {shp : ℕ → ℕ × ℕ} {idx : Ref → ℕ} (p : Params)

/-- The coordinate-split zerocheck against `zeroIX`. -/
theorem folP_zeroProgX : FolP cap shp idx Typed.zeroProgX (atomsOf p zeroIX) fun _ ↦ True := by
  simp only [zeroIX, List.flatten_cons, List.flatten_nil, List.append_nil, atomsOf_append, atomsOf_smp,
    atomsOf_rd]
  unfold Typed.zeroProgX
  exact (folP_sampleChallenges Typed.xVars).bind fun τ hτ ↦ folP_sampleChallenge.bind fun _ _ ↦
    (folP_sumcheck p rfl (by norm_num) (τ.map some) Typed.xVars 0 (by rw [List.length_map, hτ])).bind fun _ _ ↦
    (folP_readScalars 6).bind_nil fun _ _ ↦ (folP_require _).bind_ret fun _ _ ↦ trivial

/-- The coordinate-split wiring against `wiringIX`. -/
theorem folP_wireProgX (Ti : Typed.TInst) (pub : Pub) (v : List E) :
    FolP cap shp idx (Typed.wireProgX Ti pub v) (atomsOf p wiringIX) fun _ ↦ True := by
  simp only [wiringIX, List.flatten_cons, List.flatten_nil, List.append_nil, atomsOf_append, atomsOf_smp,
    atomsOf_rd]
  unfold Typed.wireProgX
  exact folP_sampleChallenge.bind fun _ _ ↦
    (folP_sumcheck p rfl (by norm_num) _ Typed.yVars _ (List.length_replicate ..)).bind fun _ _ ↦
    (folP_readScalars 8).bind fun _ _ ↦ (folP_readScalars 4).bind_nil fun _ _ ↦
    (folP_require _).bind_ret fun _ _ ↦ trivial

/-- A23 at `Φ_Q` in `phiVarsX = 44` variables against `accIX` (`accV = 44`). -/
theorem folP_accProgQX (hacc : p.accV = Typed.phiVarsX) (Q : Lvm.Loop.Program) (lay : Typed.Lay) (ok : Bool)
    (yIn : E) (a rxy vs : List E) :
    FolP cap shp idx (Typed.accProgQX Q lay ok yIn a rxy vs) (atomsOf p (accIX p)) fun _ ↦ True := by
  rw [accIX, hacc]
  unfold Typed.accProgQX
  exact folP_accProg p 3 Typed.phiVarsX ok yIn a _ _ _

/-- **The coordinate-split typed phases** against `typedIX p` (`accV = 44`; the record's mini-bus numbers those
of `Ti.mbT`, as `folP_typedProg`). -/
theorem folP_typedProgX (Ti : Typed.TInst) (pub : Pub) (hacc : p.accV = Typed.phiVarsX)
    (hl : p.leafdecReads = 1) (hd : p.busDepth = Typed.miniDepth)
    (hr : p.tableRounds = (Ti.mbT.map (·.τ)).foldl max 0) (he : p.tableEvals = (Ti.mbT.map (·.w)).sum) :
    FolP cap shp idx (Typed.typedProgX Ti pub) (atomsOf p (typedIX p)) fun _ ↦ True := by
  simp only [typedIX, atomsOf_append]
  rw [← atomsOf_append p (miniBusI p)]
  unfold Typed.typedProgX
  exact (folP_zeroProgX p).bind fun _ _ ↦ (folP_wireProgX p Ti pub _).bind fun _ _ ↦
    (folP_relayProg p Ti _ _).bind fun _ _ ↦ (folP_accProgQX p hacc _ _ _ _ _ _ _).bind fun _ _ ↦
    (folP_miniBusProg p Ti hl hd hr he).bind_ret fun _ _ ↦ trivial

end Typed

/-! ## The pinned middle phases -/

section Mid

variable {cap : ℕ → ℕ → ℕ} {shp : ℕ → ℕ × ℕ} {idx : Ref → ℕ}

/-- **The root OOD pin**: `ν = 23` samples, one read. -/
theorem folP_pinProg :
    FolP cap shp idx Lvm.E2F.pinProg (List.replicate CMain.nu20 .sm ++ [.rd]) fun _ ↦ True := by
  unfold Lvm.E2F.pinProg
  exact (folP_sampleChallenges _).bind fun _ _ ↦ folP_readScalar.bind_ret fun _ _ ↦ trivial

/-- `midP` follows the pin's atoms, then what `mid x` follows. -/
theorem folP_midP (mid : List UInt8 → VerifierProgram (List Verifier.StackClaim)) (x : List UInt8)
    (as : List Atom) (h : FolP cap shp idx (mid x) as fun _ ↦ True) :
    FolP cap shp idx (Lvm.E2F.midP mid x) ((List.replicate CMain.nu20 .sm ++ [.rd]) ++ as) fun _ ↦ True := by
  unfold Lvm.E2F.midP
  exact folP_pinProg.bind fun _ _ ↦ h.bind_ret fun _ _ ↦ trivial

/-- **S2GF's middle phases** (`midF₂ Ti`) against the typed and the front items at `P20F.withF accVF`. -/
theorem folP_midF₂ (Ti : Typed.TInst) (hl : (P20F.withF accVF).leafdecReads = 1)
    (hd : (P20F.withF accVF).busDepth = Typed.miniDepth)
    (hr : (P20F.withF accVF).tableRounds = (Ti.mbT.map (·.τ)).foldl max 0)
    (he : (P20F.withF accVF).tableEvals = (Ti.mbT.map (·.w)).sum) (x : List UInt8) :
    FolP cap shp idx (midF₂ Ti x) (atomsOf (P20F.withF accVF) (typedIX (P20F.withF accVF) ++
      (tapeIF (P20F.withF accVF) ++ (wireIF (P20F.withF accVF) ++ (ksIF (P20F.withF accVF) ++
        ksLinkIF (P20F.withF accVF)))))) fun _ ↦ True := by
  rw [atomsOf_append]
  unfold midF₂ midFWith midFWithR
  exact (folP_typedProgX _ Ti _ rfl hl hd hr he).bind fun _ _ ↦
    (folP_kgProgFR _ rfl rfl _ _ _).bind_ret fun _ _ ↦ trivial

theorem atomsOf_pinI : atomsOf (P20F.withF accVF) (pinI (P20F.withF accVF)) =
    List.replicate CMain.nu20 .sm ++ [.rd] := by
  rw [pinI, atomsOf_append, atomsOf_smp, atomsOf_rd]
  rfl

/-- **The pinned middle phases follow `midItemsF`** at `P20F.withF accVF`, for every relocation. -/
theorem folP_midPF (reloc : List UInt8 → VStackClaim → VStackClaim) (Ti : Typed.TInst)
    (hl : (P20F.withF accVF).leafdecReads = 1) (hd : (P20F.withF accVF).busDepth = Typed.miniDepth)
    (hr : (P20F.withF accVF).tableRounds = (Ti.mbT.map (·.τ)).foldl max 0)
    (he : (P20F.withF accVF).tableEvals = (Ti.mbT.map (·.w)).sum) (x : List UInt8) :
    FolP cap shp idx (Lvm.E2F.midP (Lvm.ASM.midM reloc (midF₂ Ti)) x)
      (atomsOf (P20F.withF accVF) (midItemsF (P20F.withF accVF))) fun _ ↦ True := by
  rw [midItemsF, atomsOf_append, atomsOf_pinI]
  exact folP_midP _ x _ (folP_midM reloc _ x _ (folP_midF₂ Ti hl hd hr he x))

end Mid

/-! ## The whole `P_S` -/

theorem level_F : (P20F.withF accVF).level = P20.level := rfl

theorem atomsOf_F (its : List Item) : atomsOf (P20F.withF accVF) its = atomsOf P20 its := by
  unfold atomsOf
  congr 1

theorem openMainI_F : openMainI (P20F.withF accVF) = openMainI P20 := rfl

theorem commitI_F : commitI (P20F.withF accVF) = commitI P20 := by
  unfold commitI
  rw [level_F]

theorem atomsOf_scheduleF : atomsOf (P20F.withF accVF) (schedule (P20F.withF accVF)) =
    [.cap (P20.level ⟨.main, 0⟩).cap ⟨.main, 0⟩] ++
      (atomsOf (P20F.withF accVF) (midItemsF (P20F.withF accVF)) ++ (atomsOf P20 (openMainI P20) ++ [])) := by
  rw [scheduleF_eq _ rfl, atomsOf_append, atomsOf_append, atomsOf_append, openMainI_F, atomsOf_F (openMainI P20),
    commitI_F, atomsOf_F (commitI P20), atomsOf_commitI, atomsOf_nil]

/-- **S2GF's `P_S` follows the schedule** at `P20F.withF accVF`: the root, the pin, the coordinate-split typed
phases, the `E2` front, `C_main`'s opening (`P20`'s levels), from no pending positions. -/
theorem fol_PSOfF (reloc : List UInt8 → VStackClaim → VStackClaim) (Ti : Typed.TInst)
    (hl : (P20F.withF accVF).leafdecReads = 1) (hd : (P20F.withF accVF).busDepth = Typed.miniDepth)
    (hr : (P20F.withF accVF).tableRounds = (Ti.mbT.map (·.τ)).foldl max 0)
    (he : (P20F.withF accVF).tableEvals = (Ti.mbT.map (·.w)).sum) (x : List UInt8) :
    Fol capS shpS idxS (Lvm.ASM.PSWithM (Lvm.E2F.midP (Lvm.ASM.midM reloc (midF₂ Ti))) x)
      (atomsOf (P20F.withF accVF) (schedule (P20F.withF accVF))) [] fun _ _ ↦ True := by
  rw [atomsOf_scheduleF]
  unfold Lvm.ASM.PSWithM
  refine Fol.bindP (folP_commitRootUd cfgMain24G rfl cap_main0 rfl) fun _ _ ↦ ?_
  refine @Fol.bindP capS shpS idxS _ _ (Lvm.E2F.midP (Lvm.ASM.midM reloc (midF₂ Ti)) x) _
    (atomsOf (P20F.withF accVF) (midItemsF (P20F.withF accVF))) (atomsOf P20 (openMainI P20) ++ []) _ [] _
    (folP_midPF reloc Ti hl hd hr he x) fun cl _ ↦ ?_
  exact @Fol.bindQ capS shpS idxS _ _ _ _ (atomsOf P20 (openMainI P20)) [] [] _ _ (@fol_openMain cl [])
    fun _ _ _ ↦ trivial

/-! ## The static check -/

/-- S2GF's record with `P20`'s levels as literals (`LvmReplay.P20_eq`). -/
theorem PF_eq : P20F.withF accVF = { Lvm.Replay.P20L with name := "P20F", stage := 1, accV := accVF } := by
  unfold Params.withF P20F
  rw [Lvm.Replay.P20_eq]

set_option maxRecDepth 200000 in
/-- **The static check at S2GF** (one kernel evaluation over the items, `stA_atomsOf`). -/
theorem stA_P20F :
    stA (P20F.withF accVF) (atomsOf (P20F.withF accVF) (schedule (P20F.withF accVF))) 0 [] [] = true := by
  rw [stA_atomsOf, PF_eq]
  decide +kernel

/-! ## Read widths -/

/-- The read widths of an item (`read m`: `m` × 24 B; `readW m w`: `m` × `w` B). -/
def itemW : Item → List ℕ
  | .read m => List.replicate m 24
  | .readW m w => List.replicate m w
  | _ => []

theorem widthsA_replicate_rdw (w : ℕ) : ∀ m, widthsA (List.replicate m (.rdw w)) = List.replicate m w
  | 0 => rfl
  | m + 1 => by rw [List.replicate_succ, List.replicate_succ, ← widthsA_replicate_rdw w m]; rfl

theorem widthsA_itemAtoms (p : Params) (it : Item) : widthsA (itemAtoms p it) = itemW it := by
  cases it with
  | read m => exact widthsA_replicate_rd m
  | readW m w => exact widthsA_replicate_rdw w m
  | positions r => exact widthsA_posAtoms _ _ _
  | _ => rfl

/-- **The atoms' read widths are the items'.** -/
theorem widthsA_atomsOf (p : Params) : ∀ its : List Item, widthsA (atomsOf p its) = its.flatMap itemW
  | [] => rfl
  | it :: its => by
    rw [atomsOf_cons, widthsA_append, widthsA_itemAtoms, widthsA_atomsOf p its, List.flatMap_cons]

theorem readWidthsF_eq :
    readWidthsF P20F accVF = widthsA (atomsOf (P20F.withF accVF) (schedule (P20F.withF accVF))) := by
  rw [widthsA_atomsOf]
  unfold readWidthsF
  congr 1

theorem wAt_getD (l : List ℕ) (d : ℕ) : WAt (fun i ↦ l.getD i d) 0 l := fun k hk ↦ by
  show l.getD (0 + k) d = l.getD k 0
  rw [Nat.zero_add, List.getD_eq_getElem _ _ hk, List.getD_eq_getElem _ _ hk]

/-- **`rwF20` is the S2GF schedule's read widths** from read `0`. -/
theorem wAt_rwF20 : WAt rwF20 0 (widthsA (atomsOf (P20F.withF accVF) (schedule (P20F.withF accVF)))) := by
  rw [← readWidthsF_eq]
  exact wAt_getD _ _

/-! ### Phases that read 24-byte scalars only -/

theorem noWB_append (a b : List Item) : noWB (a ++ b) = (noWB a && noWB b) := List.all_append

theorem noWB_rd (m : ℕ) : noWB (rd m) = true := by unfold rd; split <;> rfl

theorem noWB_smp : ∀ n, noWB (smp n) = true
  | 0 => rfl
  | n + 1 => noWB_smp n

theorem noWB_flatten_replicate (l : List Item) (hl : noWB l = true) :
    ∀ n, noWB (List.replicate n l).flatten = true
  | 0 => rfl
  | n + 1 => by rw [List.replicate_succ, List.flatten_cons, noWB_append, hl, noWB_flatten_replicate l hl n]; rfl

theorem noWB_sumcheckI (n d : ℕ) : noWB (sumcheckI n d) = true :=
  noWB_flatten_replicate _ (by rw [noWB_append, noWB_rd]; rfl) n

theorem noWB_rdsmp (a b : ℕ) : noWB (rd a ++ smp b) = true := by
  rw [noWB_append, noWB_rd, noWB_smp]; rfl

theorem noWB_gpLayersI : ∀ fuel layer point, noWB (gpLayersI fuel layer point) = true
  | 0, _, _ => rfl
  | fuel + 1, layer, point => by
    rw [gpLayersI]
    split
    · rfl
    · simp only [List.flatten_cons, List.flatten_nil, List.append_nil, noWB_append, noWB_smp, noWB_rd,
        noWB_gpLayersI fuel, noWB_flatten_replicate _ (noWB_rdsmp _ _), Bool.and_self]

theorem noWB_typedIX (p : Params) : noWB (typedIX p) = true := by
  simp only [typedIX, zeroIX, wiringIX, relayI, accIX, miniBusI, miniTabI, gpI, List.flatten_cons,
    List.flatten_nil, List.append_nil, noWB_append, noWB_smp, noWB_rd, noWB_sumcheckI, noWB_gpLayersI,
    Bool.and_self]

/-- The pin reads one 24-byte scalar. -/
theorem mem_widthsA_pinF : ∀ x ∈ widthsA (atomsOf (P20F.withF accVF) (pinI (P20F.withF accVF))), x = 24 :=
  mem_widthsA_atomsOf _ _ (by rw [pinI, noWB_append, noWB_smp, noWB_rd]; rfl)

/-- The coordinate-split typed phases read 24-byte scalars only. -/
theorem mem_widthsA_typedF :
    ∀ x ∈ widthsA (atomsOf (P20F.withF accVF) (typedIX (P20F.withF accVF))), x = 24 :=
  mem_widthsA_atomsOf _ _ (noWB_typedIX _)

/-- `C_main`'s opening reads 24-byte scalars only (it is `P20`'s, which has no `readW`). -/
theorem mem_widthsA_openF :
    ∀ x ∈ widthsA (atomsOf (P20F.withF accVF) (openMainI (P20F.withF accVF))), x = 24 := by
  have h := noWB_P20
  rw [schedule_eq P20 (by decide)] at h
  simp only [noWB_append, Bool.and_eq_true] at h
  rw [openMainI_F]
  exact mem_widthsA_atomsOf _ _ h.2.2.2.2.2.2.1

end Lvm.VEq
