-- New for lvm2 E2-FT (E2F-V2-TOP): the S2GF schedule's read widths in V_S's decision order: the pin's read, the
-- typed phases', the `E2` front's (E2F-V's per-phase width lists `wTape`, `wCaller`, `wKsLink`), the opening's.
import LvmE2VFol
import LvmE2VEqCaller

/-!
# The S2GF read widths, phase by phase

* `wI its := its.flatMap itemW` (the items' read widths, `widthsA_atomsOf`); its value on the `E2` builders:
  `wI_rdE2`, `wI_gsmpN`, `wI_sumcheckE2I`, `wI_keccakLayerE2I`, `wI_tapeLayersE2I`, `wI_keccakE2I`;
* the front: **`widthsA_frontF`** (`tapeIF ++ wireIF ++ ksIF ++ ksLinkIF` reads `wTape 20 ++ wCaller 13 ++ wKsLink 13`);
* **`widthsA_scheduleF`**: the schedule reads `[24]` (the pin), the typed phases', the front's, the opening's.
-/

set_option autoImplicit false

namespace Lvm.VEq

open LeanVM.Parameters LeanVM.Protocol.Compile

/-! ## Widths of item lists -/

theorem flatMap_flatten_replicate {β : Type} (f : Item → List β) (l : List Item) :
    ∀ n, ((List.replicate n l).flatten).flatMap f = (List.replicate n (l.flatMap f)).flatten
  | 0 => rfl
  | n + 1 => by
    rw [List.replicate_succ, List.flatten_cons, List.flatMap_append, flatMap_flatten_replicate f l n,
      List.replicate_succ, List.flatten_cons]

theorem flatten_replicate_single (a : ℕ) : ∀ n, (List.replicate n [a]).flatten = List.replicate n a
  | 0 => rfl
  | n + 1 => by
    rw [List.replicate_succ, List.flatten_cons, flatten_replicate_single a n, List.replicate_succ]; rfl

theorem wI_rdE2 (m : ℕ) : (rdE2 m).flatMap itemW = wReads m := by
  unfold rdE2
  split
  · subst_vars; rfl
  · rw [List.flatMap_cons, List.flatMap_nil, List.append_nil]; rfl

theorem wI_smp : ∀ n, (smp n).flatMap itemW = []
  | 0 => rfl
  | n + 1 => by rw [smp, List.replicate_succ, List.flatMap_cons, ← smp, wI_smp n]; rfl

theorem wI_gsmp : gsmp.flatMap itemW = wSampleG := rfl

theorem wI_gsmpN (n : ℕ) : (gsmpN n).flatMap itemW = List.replicate n 8 := by
  rw [gsmpN, flatMap_flatten_replicate, wI_gsmp, wSampleG, flatten_replicate_single]

theorem wI_sumcheckE2I (r d : ℕ) : (sumcheckE2I r d).flatMap itemW = wSc (d + 1) r := by
  rw [sumcheckE2I, flatMap_flatten_replicate, List.flatMap_append, wI_rdE2, wI_gsmp, wSc, wRoundG,
    Nat.add_sub_cancel]

theorem wI_keccakLayerE2I (pt : ℕ) : (keccakLayerE2I pt).flatMap itemW = wLayer pt := by
  simp only [keccakLayerE2I, List.flatten_cons, List.flatten_nil, List.append_nil, List.flatMap_append, wI_rdE2,
    wI_gsmp, wI_sumcheckE2I, wLayer, wPack, List.append_assoc]
  rfl

theorem wI_tapeLayersE2I (ls : ℕ) :
    (tapeLayersE2I ls).flatMap itemW = List.replicate laneBits 8 ++ wLayers (ls - packBits) tapeDepth := by
  rw [tapeLayersE2I, List.flatMap_append, wI_gsmpN, flatMap_flatten_replicate, wI_keccakLayerE2I, wLayers]

theorem slotLog_eq : slotLog = LeanVM.Protocol.Verifier.qkeccakSlotBits := by decide

theorem wI_keccakE2I (ls : ℕ) :
    (keccakE2I ls).flatMap itemW =
      List.replicate (segmentBits + laneBits) 8 ++ wReads 1 ++ wLayers (ls - packBits + segmentBits) gkrDepth ++
        wOpen ++ wReads 1 ++ wSc 3 packBits ++ wOpen ++ wReads kBits := by
  simp only [keccakE2I, List.flatten_cons, List.flatten_nil, List.append_nil, List.flatMap_append, wI_rdE2,
    wI_gsmpN, wI_sumcheckE2I, flatMap_flatten_replicate, wI_keccakLayerE2I, wLayers, wOpen, slotLog_eq,
    List.append_assoc]

/-! ## The front -/

/-- **The `E2` front's read widths at S2GF** are E2F-V's per-phase width lists. -/
theorem widthsA_frontF :
    widthsA (atomsOf (P20F.withF accVF) (tapeIF (P20F.withF accVF) ++ (wireIF (P20F.withF accVF) ++
      (ksIF (P20F.withF accVF) ++ ksLinkIF (P20F.withF accVF))))) = wTape 20 ++ wCaller 13 ++ wKsLink 13 := by
  rw [widthsA_atomsOf]
  have hN : (P20F.withF accVF).logN = 20 := rfl
  have hK : (P20F.withF accVF).ksLog = 13 := rfl
  simp only [tapeIF, wireIF, ksIF, ksLinkIF, hN, hK, List.flatten_cons, List.flatten_nil, List.append_nil,
    List.flatMap_append, wI_rdE2, wI_gsmpN, wI_sumcheckE2I, wI_tapeLayersE2I, wI_keccakE2I, wI_smp,
    show sepI.flatMap itemW = [] from rfl, wTape, wTapeGkr, wWire, wSlot, wCaller, wVK, wKsLink, List.nil_append,
    List.append_assoc]
  rw [show List.replicate (segmentBits + laneBits) 8 = List.replicate 1 8 ++ List.replicate 5 8 from
    List.replicate_add 1 5 8]
  simp only [List.append_assoc]
  rfl

/-! ## The schedule -/

/-- **The S2GF schedule's read widths** in V_S's decision order: the pin's read, the typed phases', the front's,
the opening's. -/
theorem widthsA_scheduleF :
    widthsA (atomsOf (P20F.withF accVF) (schedule (P20F.withF accVF))) =
      [24] ++ widthsA (atomsOf (P20F.withF accVF) (typedIX (P20F.withF accVF))) ++
        (wTape 20 ++ wCaller 13 ++ wKsLink 13) ++ widthsA (atomsOf P20 (openMainI P20)) := by
  have hp : widthsA (List.replicate CMain.nu20 Atom.sm) = [] := by
    generalize CMain.nu20 = n
    induction n with
    | zero => rfl
    | succ n ih => rw [List.replicate_succ]; exact ih
  rw [atomsOf_scheduleF, midItemsF, atomsOf_append (P20F.withF accVF) (pinI _),
    atomsOf_append (P20F.withF accVF) (typedIX _), atomsOf_pinI]
  simp only [widthsA_append, widthsA_frontF, hp, List.append_nil, List.nil_append, List.append_assoc]
  rfl

end Lvm.VEq
