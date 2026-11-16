-- New for lvm (WP-14a, H3): the per-phase value refinements of V_S's phases 4–7 (`dKg`) against `kgProgS`, and the
-- claim lists they return. lvm2 roll 11 (M′, R11-IR): the bus path's top (`dTop`, `ref_dMid`, `ref_decide`) is gone;
-- the typed top is `LvmTypedVEqTop`.
import LvmVEqTape
import LvmVEqWire
import LvmVEqParse
import LvmVEqKec
import LvmVEqBus
import LvmVEqWhir
import LvmCertS
import LvmAccNodeFold
import LvmShape
import LvmVEqClaims
import LvmVEqSum
import LvmMPVEqReloc

-- ===== merged from `LvmShapeVR` (GOLF module merge: `LvmShapeVR.lean` is now a stub importing `LvmVEqTop`) =====
section
-- New for lvm2 (CR-V, roll 7 SH2-Z; CR-DES §1.5): V_S's small `C_main` claims against `onStackZs`.
-- The wire phase with the ring coefficients (`dWireC`) refines as `dWire` does; at `P20` every
-- `C_main` claim of `dClaimsT` is an aligned block inside the stack and carries its tail value
-- (`tails_main`).

/-!
# V_S's small claims refine `onStackZs`

* **`ref_dWireC`**: `dWireC` refines T-W's wiring program with `WireRel` and `WireRing` (the ring
  claim's weight is `ringWeight` at `wirePt` with the returned coefficients).
* **`dClaimsT_fst`**: without the tails, `dClaimsT` is `dClaims`.
* **Tails per claim kind at `P20`** (each from `LvmShape`'s closed forms, none assumed):
  `table_tails` (`colsFitB`, `colsHiB`: blocks from word `2^22`), `ks_tails` (`KS`'s two claims),
  `ksOut_tails` (`KS`'s 25 output lanes), `ksLink_tails` (the link's four sums, M′: all on `C_main`),
  `tape_tails` (`D`'s point claims `tailDF`, the ring claim `ringTailN`, the boundary claims `0`);
  **`tails_main`**: every `C_main` claim of `dClaimsT` is `InStack` and its tail is `tailValueF`.
* (B1's two-commitment `ref_dOpenZ` is gone at M′ `S2GM`; the M′ opening is `LvmTypedVEqTop.ref_dOpenT`.)
-/

set_option autoImplicit false

namespace Lvm.Shape

open Lvm Lvm.VEq DM LeanVM.Parameters LeanVM.Protocol LeanVM.Protocol.Compile

/-! ## The wire phase with the ring coefficients -/

theorem runD_bind_map {β γ : Type} (d : DM β) (f : β → γ) (sig : ByteArray) (s : RS) :
    runD (d >>= fun x ↦ Pure.pure (f x)) sig s = (f (runD d sig s).1, (runD d sig s).2) := rfl

theorem runD_dWire_fst (p : Params) (pub : Pub) (claim : KeccakClaim) (sig : ByteArray) (s : RS) :
    (runD (dWire p pub claim) sig s).1 = (runD (dWireC p pub claim) sig s).1.1 := by
  rw [dWire_eqC, runD_bind_map (dWireC p pub claim) Prod.fst sig s]

theorem runD_dWire_snd (p : Params) (pub : Pub) (claim : KeccakClaim) (sig : ByteArray) (s : RS) :
    (runD (dWire p pub claim) sig s).2 = (runD (dWireC p pub claim) sig s).2 := by
  rw [dWire_eqC, runD_bind_map (dWireC p pub claim) Prod.fst sig s]

theorem monoD_dWireC (p : Params) (pub : Pub) (claim : KeccakClaim) : MonoD (dWireC p pub claim) := by
  intro sig s h
  apply monoD_dWire p pub claim sig s
  rw [runD_dWire_snd]
  exact h

/-- The ring claim's weight is `ringWeight` at the wire point with the returned coefficients. -/
def WireRing (p : Params) (x : WireOut × List FE) : Prop :=
  x.1.ring.2 = fun rPrime ↦ ringWeight (wirePt p x.1) rPrime x.2

theorem retD_dWireC (p : Params) (pub : Pub) (claim : KeccakClaim) :
    RetD (WireRing p) (dWireC p pub claim) := by
  unfold dWireC
  exact RetD.bind_true fun _ ↦ RetD.bind_true fun _ ↦ RetD.bind_true fun _ ↦ RetD.bind_true fun _ ↦
    RetD.bind_true fun _ ↦ RetD.bind_true fun _ ↦ RetD.bind_true fun _ ↦ RetD.pure rfl

/-- **The wire phase with the ring coefficients refines T-W's wiring program** (`ref_dWire`). -/
theorem ref_dWireC {cap occ : ℕ → ℕ → ℕ} {shp : ℕ → ℕ × ℕ} {sig : ByteArray} (p : Params) (pub : Pub)
    (claim : KeccakClaim) (d : RecursionFast.Digest) (hs : pub.s = digestLanes d) :
    RefAt cap occ shp sig (dWireC p pub claim)
      (Lvm.KG.wireChProg p.logN (dSelBits p) (dSel p) d pub.n (kcE claim))
      (fun x a ↦ WireRel p.logN x.1 a ∧ WireRing p x) := fun s hok ↦ by
  have hok' : (runD (dWire p pub claim) sig s).2.ok = true := by rw [runD_dWire_snd]; exact hok
  have h := ref_dWire (cap := cap) (occ := occ) (shp := shp) (sig := sig) p pub claim d hs s hok'
  rw [runD_dWire_snd, runD_dWire_fst] at h
  obtain ⟨a, h1, h2, h3, h4⟩ := h
  exact ⟨a, h1, h2, h3, h4, retD_dWireC p pub claim sig s⟩

/-! ## The claims without their tails -/

theorem dClaimsT_fst (m : M3) (p : Params) (pub : Pub) (bus : BusOut)
    (evals : List (List FE × List FE)) (tp : TapeRes) (wo : WireOut × List FE)
    (ks : List FE × List FE × KeccakOut × (FE × (List FE → FE))) (kl : List (Com × BlockClaim)) :
    (dClaimsT m p pub bus evals tp wo ks kl).map (fun e ↦ (e.1, e.2.1)) =
      dClaims m p pub bus evals tp wo.1 ks kl := by
  unfold dClaimsT dClaims
  rw [dClaimsZ_fst]

/-! ## Tails per claim kind at `P20` -/

/-- A block from word `2^22`, at most `2^22` words, aligned, inside the stack. -/
def OffOK (b : Placement) : Prop :=
  2 ^ 22 ≤ b.index ∧ b.variableCount ≤ 22 ∧ b.index < 2 ^ CMain.nu20 ∧ b.index % 2 ^ b.variableCount = 0

instance (b : Placement) : Decidable (OffOK b) := by unfold OffOK; infer_instance

instance (b : Placement) : Decidable (InStack b) := by unfold InStack; infer_instance

theorem OffOK.inStack {b : Placement} (h : OffOK b) : InStack b :=
  ⟨by have := h.2.1; unfold CMain.nu20; (clear * - this; omega), h.2.2.2, h.2.2.1⟩

theorem OffOK.tail {c : BlockClaim} (h : OffOK c.block) : tailValueF c.onStack.1 = 0 :=
  tailValueF_off c h.1 h.2.1 h.2.2.1

theorem nuMain_P20 : P20.nuMain = CMain.nu20 := by decide +kernel

theorem logN_P20 : P20.logN = 20 := by decide +kernel

/-- `KS`'s block at `P20`. -/
theorem offOK_ks : OffOK ⟨P20.ksLog + slotLog, (layout0 P20).ks⟩ := by
  rw [layout0_P20]; decide +kernel

/-- `KS`'s `Y` lanes at `P20`. -/
theorem offOK_ksY (l : ℕ) (hl : l < 25) (pt : List FE) : OffOK (ksYPart P20 (layout0 P20) l pt).1 := by
  unfold ksYPart
  split_ifs
  · exact offOK_ks
  · rw [layout0_P20]
    have : ∀ l < 25, ¬ l < 14 → OffOK ⟨P20.ksLog, CMain.ksY2Off20 + (l - 14) * 2 ^ P20.ksLog⟩ := by
      decide +kernel
    exact this l hl (by assumption)

/-- `X`'s message columns at `P20` (KS14: `2^ksXLog` rows from `xOff20`, column `l` at `+ l·2^ksXLog`). -/
theorem offOK_x (l : ℕ) (hl : l < 17) :
    OffOK ⟨ksXLog P20, (layout0 P20).x + l * 2 ^ ksXLog P20⟩ := by
  rw [layout0_P20]
  have : ∀ l < 17, OffOK ⟨ksXLog P20, CMain.xOff20 + l * 2 ^ ksXLog P20⟩ := by decide +kernel
  exact this l hl

/-- **The tables' `C_main` claims** have no tail (`colsFitB`: aligned inside the stack; `colsHiB`: from
word `2^22`, at most `2^22` words). -/
theorem table_tails (T T₀ : List M3.Tab) (hT : ∀ t ∈ T, t ∈ T₀) (evs : List (List FE × List FE))
    (hc : M3.colsFitB P20 T₀ = true) (hh : M3.colsHiB T₀ = true) :
    ∀ e ∈ M3.tableClaimsR T evs, e.1 = .main → OffOK e.2.block := by
  intro e he hm
  unfold M3.tableClaimsR at he
  obtain ⟨⟨t, pt, ev⟩, htz, he⟩ := List.mem_flatMap.mp he
  have ht : t ∈ T₀ := hT t (List.of_mem_zip htz).1
  obtain ⟨⟨c, i⟩, hci, hce⟩ := List.mem_filterMap.mp he
  have hc' : c ∈ t.cols := List.fst_mem_of_mem_zipIdx hci
  unfold M3.colsFitB at hc
  unfold M3.colsHiB at hh
  simp only [Bool.and_eq_true, List.all_eq_true] at hc hh
  have h1 := hc.2 t ht c hc'
  have h2 := hh t ht c hc'
  cases c with
  | fix f ev' => simp at hce
  | com rec off =>
    simp only [Option.some.injEq] at hce
    subst hce
    cases rec with
    | true => simp at hm
    | false =>
      simp only [Bool.false_or, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq, Bool.false_eq_true,
        ite_false] at h1 h2
      refine ⟨h2.1, h2.2, ?_, h1.1⟩
      rw [nuMain_P20] at h1
      have := Nat.one_le_two_pow (n := t.τ)
      simp only [BlockClaim.point]
      (clear * - h1; omega)

/-- **`KS`'s output lanes** have no tail. -/
theorem ksOut_tails (rk v : List FE) : ∀ e ∈ ksOutputClaims0 P20 rk v, OffOK e.2.block := by
  intro e he
  unfold ksOutputClaims0 at he
  obtain ⟨l, hl, rfl⟩ := List.mem_map.mp he
  exact offOK_ksY l (List.mem_range.mp hl) rk

/-- `M`'s columns at `P20` (M′: the stream block's column `l`, `2^ksLog` rows from `S + l·2^recRowsLog`). -/
theorem offOK_m (l : ℕ) (hl : l < 17) :
    OffOK ⟨P20.ksLog, (layout0 P20).s + l * 2 ^ P20.recRowsLog⟩ := by
  rw [layout0_P20]
  have : ∀ l < 17, OffOK ⟨P20.ksLog, CMain.sOff20 + l * 2 ^ P20.recRowsLog⟩ := by decide +kernel
  exact this l hl

/-- `M`'s top rows at `P20` (`2^ksXLog` rows of column `l` from the split). -/
theorem offOK_mx (l : ℕ) (hl : l < 17) :
    OffOK ⟨ksXLog P20, (layout0 P20).s + l * 2 ^ P20.recRowsLog + ksSplit P20⟩ := by
  rw [layout0_P20]
  have : ∀ l < 17, OffOK ⟨ksXLog P20, CMain.sOff20 + l * 2 ^ P20.recRowsLog + ksSplit P20⟩ := by decide +kernel
  exact this l hl

/-- `X`'s columns at `P20` (M′: column `l`'s rows from the split, `X` at `S + ksSplit`, stride `2^recRowsLog`). -/
theorem offOK_xs (l : ℕ) (hl : l < 17) :
    OffOK ⟨ksXLog P20, (layout0 P20).x + l * 2 ^ P20.recRowsLog⟩ := by
  rw [layout0_P20]
  have : ∀ l < 17, OffOK ⟨ksXLog P20, CMain.xOff20 + l * 2 ^ P20.recRowsLog⟩ := by decide +kernel
  exact this l hl

/-- **The `KS` link's claims** (`yC`, `inC`, `mC`, `xC`, sums on `⟨ν, 0⟩`; M′: all on `C_main`) have no tail. -/
theorem ksLink_tails (i : KsLinkIn) :
    ∀ e ∈ (ksLink0 P20 i).2, e.1 = .main → InStack e.2.block ∧ tailValueF e.2.onStack.1 = 0 := by
  have hw : InStack ⟨P20.nuMain, 0⟩ := by rw [nuMain_P20]; decide
  intro e he _
  have hk : P20.ksLog ≤ P20.recRowsLog := by decide +kernel
  simp only [ksLink0, hk, if_true, ksLink14, List.mem_cons, List.mem_nil_iff, or_false] at he
  rcases he with rfl | rfl | rfl | rfl
  · refine ⟨hw, ?_⟩
    simp only [nuMain_P20]
    refine tailValueF_sum _ _ fun q hq ↦ ?_
    obtain ⟨l, hl, rfl⟩ := List.mem_map.mp hq
    have h := offOK_ksY l (List.mem_range.mp hl) (i.shift.1)
    exact ⟨h.1, h.2.1, h.2.2.1⟩
  · refine ⟨hw, ?_⟩
    simp only [nuMain_P20]
    refine tailValueF_sum _ _ fun q hq ↦ ?_
    obtain ⟨l, hl, rfl⟩ := List.mem_map.mp hq
    exact ⟨offOK_ks.1, offOK_ks.2.1, offOK_ks.2.2.1⟩
  · refine ⟨hw, ?_⟩
    simp only [nuMain_P20]
    refine tailValueF_sum _ _ fun q hq ↦ ?_
    rcases List.mem_append.mp hq with hq | hq
    · obtain ⟨l, hl, rfl⟩ := List.mem_map.mp hq
      have h := offOK_m l (List.mem_range.mp hl)
      exact ⟨h.1, h.2.1, h.2.2.1⟩
    · obtain ⟨l, hl, rfl⟩ := List.mem_map.mp hq
      have h := offOK_mx l (List.mem_range.mp hl)
      exact ⟨h.1, h.2.1, h.2.2.1⟩
  · refine ⟨hw, ?_⟩
    simp only [nuMain_P20]
    refine tailValueF_sum _ _ fun q hq ↦ ?_
    obtain ⟨l, hl, rfl⟩ := List.mem_map.mp hq
    have h := offOK_xs l (List.mem_range.mp hl)
    exact ⟨h.1, h.2.1, h.2.2.1⟩

theorem mem_zip_map_self {α β γ : Type} (L : List α) (f : α → β) (g : α → γ) (e : β × γ)
    (h : e ∈ (L.map f).zip (L.map g)) : ∃ a ∈ L, e = (f a, g a) := by
  induction L with
  | nil => simp at h
  | cons a L ih =>
    simp only [List.map_cons, List.zip_cons_cons, List.mem_cons] at h
    rcases h with rfl | h
    · exact ⟨a, by simp, rfl⟩
    · obtain ⟨b, hb, rfl⟩ := ih h
      exact ⟨b, by simp [hb], rfl⟩

theorem mem_zip_map {α β γ δ : Type} (A : List α) (B : List β) (f : α → γ) (g : β → δ) (e : γ × δ)
    (h : e ∈ (A.map f).zip (B.map g)) : ∃ a ∈ A, ∃ b ∈ B, e = (f a, g b) := by
  rw [List.zip_map] at h
  obtain ⟨⟨a, b⟩, hab, rfl⟩ := List.mem_map.mp h
  exact ⟨a, (List.of_mem_zip hab).1, b, (List.of_mem_zip hab).2, rfl⟩

/-- **The tape's claims** carry their tails: `D`'s point claims `tailDF`, the ring claim `ringTailN`,
the boundary claims `0` (`n ≤ 2^18`). -/
theorem tape_tails (tp : TapeRes) (wo : WireOut × List FE) (pub : Pub) (hr : tp.r.length = 20)
    (hsc : wo.1.sc.1.length = 20) (hsl : wo.1.sl.1.length = 2) (hring : WireRing P20 wo)
    (hn : pub.n ≤ 2 ^ 18) (hh : pub.h.length ≤ 4) :
    ∀ e ∈ (tapeClaims P20 tp wo.1 pub).zip (tapeTails P20 tp wo.1 wo.2 pub),
      InStack e.1.block ∧ e.2 = tailValueF e.1.onStack.1 := by
  have hD : InStack (dBlock P20) := by rw [dBlock_P20]; decide
  intro e he
  unfold tapeClaims tapeTails at he
  rw [List.zip_append (by simp), List.zip_append (by simp)] at he
  simp only [List.mem_append] at he
  rcases he with (he | he) | he
  · obtain ⟨l, hl, rfl⟩ := mem_zip_map_self _ _ _ e he
    exact ⟨hD, (tailValueF_pointD tp.r hr l (by simpa [dLanes] using hl) _).symm⟩
  · simp only [List.zip_cons_cons, List.zip_nil_right, List.mem_singleton] at he
    subst he
    refine ⟨show InStack ⟨P20.nuMain, 0⟩ by rw [nuMain_P20]; decide, ?_⟩
    show ringTailN (wirePt P20 wo.1) wo.2 =
      tailValueF (⟨⟨P20.nuMain, 0⟩, wo.1.ring.2, wo.1.ring.1⟩ : BlockClaim).onStack.1
    have hpt : (wirePt P20 wo.1).length = CMain.nu20 := by
      simp only [wirePt, List.length_append, hsc, hsl, selectorPoint, List.length_map, List.length_range]
      decide +kernel
    rw [hring, nuMain_P20, tailValueF_ring _ _ hpt, ringTailN_eq]
  · obtain ⟨⟨w, l⟩, hwl, z, -, rfl⟩ := mem_zip_map _ _ _ _ e he
    have hl : l < 4 := lt_of_lt_of_le (List.mem_zipIdx hwl).2.1 (by simpa using hh)
    refine ⟨hD, ?_⟩
    show (0 : FE) = tailValueF (BlockClaim.point (dBlock P20)
      (selectorPoint (pub.n - 1) P20.logN ++ selectorPoint l 2) (FE.ofK w)).onStack.1
    rw [logN_P20, tailValueF_bnd _ (by (clear * - hn; omega)) l hl]

/-- **Every `C_main` claim of V_S's list at `P20` is an aligned block inside the stack and carries its
tail value** (when `n ≤ 2^18`): the closed forms of `LvmShape`, claim kind by claim kind. -/
theorem tails_main (tabs : Pub → List M3.Tab) (pub : Pub) (hc : M3.colsFitB P20 (tabs pub) = true)
    (hh : M3.colsHiB (tabs pub) = true) (bus : BusOut) (hb : bus.claims = [])
    (evals : List (List FE × List FE)) (tp : TapeRes) (wo : WireOut × List FE)
    (ks : List FE × List FE × KeccakOut × (FE × (List FE → FE))) (kl : List (Com × BlockClaim))
    (hr : tp.r.length = 20) (hsc : wo.1.sc.1.length = 20) (hsl : wo.1.sl.1.length = 2)
    (hring : WireRing P20 wo) (hkl : ∃ i, kl = ((M3.real P20 tabs).ksLink i).2)
    (hn : pub.n ≤ 2 ^ 18) (hh4 : pub.h.length ≤ 4) :
    ∀ e ∈ dClaimsT (M3.real P20 tabs) P20 pub bus evals tp wo ks kl, e.1 = .main →
      InStack e.2.1.block ∧ e.2.2 = tailValueF e.2.1.onStack.1 := by
  have hz : ∀ (l : List (Com × BlockClaim)),
      (∀ e ∈ l, e.1 = .main → InStack e.2.block ∧ tailValueF e.2.onStack.1 = 0) →
      ∀ e ∈ l.map (fun e ↦ ((e.1, e.2, 0) : Com × BlockClaim × FE)), e.1 = .main →
        InStack e.2.1.block ∧ e.2.2 = tailValueF e.2.1.onStack.1 := by
    intro l hl e he hm
    obtain ⟨e', he', rfl⟩ := List.mem_map.mp he
    exact ⟨(hl e' he' hm).1, (hl e' he' hm).2.symm⟩
  have hoff : ∀ (l : List (Com × BlockClaim)), (∀ e ∈ l, e.1 = .main → OffOK e.2.block) →
      ∀ e ∈ l, e.1 = .main → InStack e.2.block ∧ tailValueF e.2.onStack.1 = 0 :=
    fun l hl e he hm ↦ ⟨(hl e he hm).inStack, (hl e he hm).tail⟩
  intro e he hm
  simp only [dClaimsT, dClaimsZ, zeroTails, List.map_append, List.mem_append] at he
  rcases he with ((he | he) | (he | he)) | (he | he)
  · exact hz _ (fun e he _ ↦ by simp [hb] at he) e he hm
  · exact hz _ (hoff _ (table_tails _ (tabs pub) (fun t ht ↦ List.mem_of_mem_filter ht) evals hc hh))
      e he hm
  · obtain ⟨q, hq, rfl⟩ := List.mem_map.mp he
    exact tape_tails tp wo pub hr hsc hsl hring hn hh4 q hq
  · refine hz _ (hoff _ fun e he _ ↦ ?_) e he hm
    obtain ⟨c, hc', rfl⟩ := List.mem_map.mp he
    unfold keccakClaims at hc'
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hc'
    rcases hc' with rfl | rfl <;> exact offOK_ks
  · exact hz _ (hoff _ fun e he _ ↦ ksOut_tails ks.1 ks.2.1 e he) e he hm
  · obtain ⟨i, rfl⟩ := hkl
    exact hz _ (ksLink_tails i) e he hm

/-! ## The openings in both shapes -/

theorem monoD_dOpenZ (p : Params) (s : Bool) (claims : List (Com × BlockClaim × FE)) :
    MonoD (dOpenZ p s claims) :=
  (monoD_verifyStacked _ _ _ _ _ _).bind fun _ ↦ monoD_verifyStacked _ _ _ _ _ _

end Lvm.Shape
end
-- ===== end of `LvmShapeVR` =====

-- ===== merged from `LvmVEqLinkArith` (GOLF module merge: `LvmVEqLinkArith.lean` is now a stub importing `LvmVEqTop`) =====
section
-- New for lvm (WP-14a, H3): V_S's CH/KS link formulas (LvmDecideV0: `shiftEval`, `eqMasked`, `omegaCH`,
-- `padWeight`, `padConst`, the link targets and checks, `contShift`) and its caller-placed ring switch
-- (LvmDecide `ringRaw`) over `E`: WP-8's `shiftEvalE`, `eqMaskedE`, `omegaE`, `padWeightE`, `padConstE`,
-- `chShiftTargetE`, `chSc2TargetE`, `wtE`, `contShiftE` and leanVM's `ringSwitch` (LvmVCore).

/-!
# The link formulas over `E`

`FE.toExt3` of each native link formula is WP-8's `E` formula at the mapped arguments. V_S's
equality kernels are tables (`eqKernel`, `eqKernelA`) where WP-8 uses `eqAt`; they agree below
`2^|p|` (`toExt3_getD_eqKernel`, `toExt3_getD_eqKernelA`, WP-2's `eqKernel_getD`), so the lemmas
take the lengths of the challenge lists (`λ` 3, `ζ` 6, `μ` 2, the `KS` points 13 at KS13, B1; roll 7: 14 at KS14, lvm2 CR-K).

`ringRaw s` (V_S's caller-placed ring switch: target and Frobenius coefficients) refines leanVM's
`ringSwitch pt s` at any point `pt`: same target, weight `ringWeight pt · coeffs` (`ref_ringRaw`).
The lengths of the native `samples`, `readEs`, `sumcheck` values (`length_*`) enter through
`refAt_withD`. Everything here is in `Lvm.VEq.Lk`.
-/

set_option autoImplicit false

namespace Lvm.VEq.Lk

open Lvm Lvm.VEq DM LeanVM.Parameters LeanVM.Protocol LeanVM.Protocol.KeccakGkr Finset
open Lvm.M3 (tE_add tE_mul tE_zero tE_one tE_ofK)

/-! ## Folds and sums -/

theorem toExt3_foldl {β γ : Type} (ψ : β → γ) (f : FE → β → FE) (g : E → γ → E)
    (h : ∀ a b, FE.toExt3 (f a b) = g (FE.toExt3 a) (ψ b)) :
    ∀ (l : List β) (a : FE), FE.toExt3 (l.foldl f a) = (l.map ψ).foldl g (FE.toExt3 a)
  | [], _ => rfl
  | b :: l, a => by
    simp only [List.foldl_cons, List.map_cons]
    rw [toExt3_foldl ψ f g h l, h]

theorem sumE_map_eq_sum (f : ℕ → E) (n : ℕ) :
    Verifier.sumE ((List.range n).map f) = ∑ j ∈ range n, f j := by
  rw [Whir.Complete.sumE_eq, Lvm.KG.list_sum_map_range]

theorem toExt3_sumE_range (f : ℕ → FE) (n : ℕ) :
    FE.toExt3 (Lvm.sumE ((List.range n).map f)) = ∑ j ∈ range n, FE.toExt3 (f j) := by
  rw [toExt3_sumE, List.map_map, sumE_map_eq_sum]; rfl

/-! ## Equality kernels -/

theorem length_eqKernel_FE (p : List FE) : (Lvm.eqKernel p).length = 2 ^ p.length := by
  rw [← List.length_map (f := FE.toExt3), map_eqKernel, eqKernel_length, List.length_map]

theorem size_eqKernelA (p : List FE) : (Lvm.eqKernelA p).size = 2 ^ p.length := by
  rw [← Array.length_toList, eqKernelA_toList, length_eqKernel_FE]

theorem toExt3_getD_eqKernel (p : List FE) {i : ℕ} (hi : i < 2 ^ p.length) :
    FE.toExt3 ((Lvm.eqKernel p).getD i 0) = eqAt (p.map FE.toExt3) i := by
  rw [← getD_map_toExt3, map_eqKernel, eqKernel_getD, List.length_map, ite_eq_left hi]

theorem toExt3_getD_eqKernelA (p : List FE) {i : ℕ} (hi : i < 2 ^ p.length) :
    FE.toExt3 ((Lvm.eqKernelA p).getD i 0) = eqAt (p.map FE.toExt3) i := by
  rw [getD_eqKernelA, toExt3_getD_eqKernel p hi]

/-! ## `shiftEval`, `eqMasked` -/

theorem toExt3_shiftEval (x y : List FE) :
    FE.toExt3 (Lvm.shiftEval x y) = Lvm.KG.shiftEvalE (x.map FE.toExt3) (y.map FE.toExt3) := by
  unfold Lvm.shiftEval Lvm.KG.shiftEvalE
  simp only [toExt3_sumE, toExt3_prodE, List.map_map, Function.comp_def, tE_mul, tE_add, tE_one,
    getD_map_toExt3, List.length_map]

theorem toExt3_eqMasked (x y : List FE) :
    FE.toExt3 (Lvm.eqMasked x y) = Lvm.KG.eqMaskedE (x.map FE.toExt3) (y.map FE.toExt3) := by
  simp only [Lvm.eqMasked, Lvm.KG.eqMaskedE, Lvm.eqOnes, tE_add, tE_mul, toExt3_eqEval, toExt3_prodE]

/-! ## The `CH` link's weights -/

theorem omegaCH_getD (lam zeta : List FE) {m p : ℕ} (hm : m < 2 ^ lam.length)
    (hp : p < 2 ^ zeta.length) :
    FE.toExt3 (((Lvm.omegaCH lam zeta).getD m #[]).getD p 0) =
      Lvm.KG.omegaE (lam.map FE.toExt3) (zeta.map FE.toExt3) m p := by
  have hL : m < (Lvm.eqKernelA lam).size := by rw [size_eqKernelA]; exact hm
  have hZ : p < (Lvm.eqKernelA zeta).size := by rw [size_eqKernelA]; exact hp
  have h : ((Lvm.omegaCH lam zeta).getD m #[]).getD p 0 =
      (Lvm.eqKernelA lam).getD m 0 * (Lvm.eqKernelA zeta).getD p 0 := by
    simp [Lvm.omegaCH, Array.getD, hL, hZ]
  rw [h, tE_mul, toExt3_getD_eqKernelA lam hm, toExt3_getD_eqKernelA zeta hp]
  rfl

theorem toExt3_padWeight (lam zeta : List FE) (hl : lam.length = 3) (hz : zeta.length = 6) {m q : ℕ}
    (hm : m < 4) (hq : q < 64) :
    FE.toExt3 (Lvm.padWeight (Lvm.omegaCH lam zeta) m q) =
      Lvm.KG.padWeightE (lam.map FE.toExt3) (zeta.map FE.toExt3) m q := by
  unfold Lvm.padWeight Lvm.KG.padWeightE
  split_ifs <;> exact omegaCH_getD _ _ (by rw [hl]; norm_num; omega) (by rw [hz]; norm_num; omega)

theorem toExt3_padConst (lam zeta : List FE) (hl : lam.length = 3) (hz : zeta.length = 6) :
    FE.toExt3 (Lvm.padConst (Lvm.omegaCH lam zeta)) =
      Lvm.KG.padConstE (lam.map FE.toExt3) (zeta.map FE.toExt3) := by
  unfold Lvm.padConst Lvm.KG.padConstE
  rw [tE_add, toExt3_sumE, List.map_filterMap,
    omegaCH_getD _ _ (by rw [hl]; norm_num) (by rw [hz]; norm_num)]
  with_reducible congr 1
  rw [← sumE_filterMap_range]
  congr 1
  refine List.filterMap_congr fun p hp ↦ ?_
  have hp' := List.mem_range.1 hp
  split_ifs
  · exact congrArg some
      (omegaCH_getD lam zeta (m := 0) (p := p) (by rw [hl]; norm_num) (by rw [hz]; norm_num; omega))
  · rfl

/-- The `CH` link's challenges at `P20`. -/
theorem chSplit_P20 (chal : List FE) :
    Lvm.chSplit P20 chal = (chal.take 20, (chal.drop 20).take 3, chal.drop 23) := rfl

theorem toExt3_chShiftTarget0 (chal : List FE) (hc : chal.length = 29) :
    FE.toExt3 (Lvm.chShiftTarget0 P20 chal) = Lvm.KG.chShiftTargetE 20 (chal.map FE.toExt3) := by
  simp only [Lvm.chShiftTarget0, chSplit_P20, Lvm.KG.chShiftTargetE, Lvm.KG.chLam, Lvm.KG.chZeta,
    Lvm.KG.chRho, tE_mul, tE_add, tE_one, Lvm.eqOnes, toExt3_prodE, ← List.map_take, ← List.map_drop]
  rw [toExt3_padConst _ _ (by simp [hc]) (by simp [hc])]

theorem toExt3_chSc2Target0 (chal : List FE) (shift : List FE × FE) (inS : List FE)
    (hc : chal.length = 29) (hin : inS.length = 64) :
    FE.toExt3 (Lvm.chSc2Target0 P20 chal shift inS) =
      Lvm.KG.chSc2TargetE 20 (chal.map FE.toExt3) (shift.1.map FE.toExt3, FE.toExt3 shift.2)
        (inS.map FE.toExt3) := by
  simp only [Lvm.chSc2Target0, chSplit_P20, Lvm.KG.chSc2TargetE, Lvm.KG.chZeta, Lvm.KG.chRho,
    tE_mul, tE_add, toExt3_shiftEval, toExt3_dot, map_eqKernel, ← List.map_take, ← List.map_drop,
    Nat.reduceAdd]
  congr 2
  have hz : ((chal.drop 23).map FE.toExt3).length = 6 := by simp [hc]
  rw [dot_eq _ _ (by simp [eqKernel_length, hc, hin])]
  simp only [eqKernel_length, hz]
  refine Finset.sum_congr rfl fun p hp ↦ ?_
  have hp' := Finset.mem_range.1 hp
  rw [eqKernel_getD, hz, ite_eq_left (by norm_num; omega)]

/-- The `CH` link's check. -/
theorem toExt3_chOk (lam zeta mu rho rho' yS : List FE) (hl : lam.length = 3) (hz : zeta.length = 6)
    (hmu : mu.length = 2) :
    FE.toExt3 (Lvm.eqMasked rho rho' * Lvm.sumE ((List.range 64).map fun q =>
        Lvm.sumE ((List.range 4).map fun m =>
          (Lvm.eqKernel mu).getD m 0 * Lvm.padWeight (Lvm.omegaCH lam zeta) m q) * yS.getD q 0)) =
      Lvm.KG.eqMaskedE (rho.map FE.toExt3) (rho'.map FE.toExt3) *
        ∑ q ∈ range 64, Lvm.KG.wtE (lam.map FE.toExt3) (zeta.map FE.toExt3) (mu.map FE.toExt3) q *
          (yS.map FE.toExt3).getD q 0 := by
  rw [tE_mul, toExt3_eqMasked, toExt3_sumE_range]
  congr 1
  refine Finset.sum_congr rfl fun q hq ↦ ?_
  rw [tE_mul, toExt3_sumE_range, getD_map_toExt3]
  congr 1
  refine Finset.sum_congr rfl fun m hm ↦ ?_
  have hm' := Finset.mem_range.1 hm
  rw [tE_mul, toExt3_getD_eqKernel mu (by rw [hmu]; norm_num; omega),
    toExt3_padWeight lam zeta hl hz hm' (Finset.mem_range.1 hq)]

/-! ## The `KS` link -/

/-- `contRows P20` is in `[1, 2^13)` (KS13: the WOTS leaf's rows from the split 7,680; roll 7's KS14: `2^14`,
15,360). -/
theorem contRows_bound : ∀ i ∈ contRows P20, 1 ≤ i ∧ i < 2 ^ 13 := by
  have hs : spongeBlocks P20 = 4447 := sizes_P20.2.2.2.2.2.2.2.2
  intro i hi
  simp only [contRows, List.mem_append, List.mem_map, List.mem_range, hs, ksSplit_P20] at hi
  rcases hi with ⟨j, hj, rfl⟩ | ⟨j, hj, rfl⟩ <;> omega

theorem toExt3_contShift (rho rho' : List FE) (h1 : rho.length = 13) (h2 : rho'.length = 13) :
    FE.toExt3 (Lvm.contShift P20 rho rho') =
      Lvm.KG.contShiftE (contRows P20) (rho.map FE.toExt3) (rho'.map FE.toExt3) := by
  unfold Lvm.contShift Lvm.KG.contShiftE
  have hb0 := contRows_bound
  generalize contRows P20 = rows at hb0 ⊢
  have hf : ∀ (g : ℕ → FE) (l : List ℕ), l.foldl (fun acc i => acc + g i) 0 = Lvm.sumE (l.map g) :=
    fun g l ↦ by rw [Lvm.sumE, List.foldl_map]
  rw [hf, toExt3_sumE, List.map_map, Whir.Complete.sumE_eq]
  congr 1
  refine List.map_congr_left fun i hi ↦ ?_
  have hb := hb0 i hi
  simp only [Function.comp, tE_mul]
  rw [toExt3_getD_eqKernelA _ (by rw [h1]; omega), toExt3_getD_eqKernelA _ (by rw [h2]; omega)]

/-- The `KS` link's check (KS13: `in + M + sel·X`, `sel = Π_{j ≥ 9} ρ'_j`; roll 7's KS14: `ρ` of 14, `j ≥ 10`). -/
theorem toExt3_ksOk (kchal rho' vals : List FE) (hk : kchal.length = 18) (hr : rho'.length = 13) :
    FE.toExt3 (Lvm.contShift P20 (kchal.take 13) rho' * vals.getD 0 0 +
        Lvm.eqEval (kchal.take 13) rho' * (vals.getD 1 0 + vals.getD 2 0 +
          Lvm.prodE (rho'.drop (ksXLog P20)) * vals.getD 3 0)) =
      Lvm.KG.contShiftE (contRows P20) ((kchal.map FE.toExt3).take 13) (rho'.map FE.toExt3) *
          (vals.map FE.toExt3).getD 0 0 +
        Verifier.eqEval ((kchal.map FE.toExt3).take 13) (rho'.map FE.toExt3) *
          ((vals.map FE.toExt3).getD 1 0 + (vals.map FE.toExt3).getD 2 0 +
            Lvm.KG.selX 9 (rho'.map FE.toExt3) * (vals.map FE.toExt3).getD 3 0) := by
  rw [← List.map_take, ← toExt3_contShift _ _ (by simp [hk]) hr, ← toExt3_eqEval, ksXLog_P20, Lvm.KG.selX,
    ← List.map_drop, ← EndToEnd.Complete.prodE_eq, ← toExt3_prodE]
  simp only [tE_add, tE_mul, getD_map_toExt3]

/-! ## Ring switching -/

theorem toExt3_phiMap (v : FE) (ch : List FE) :
    FE.toExt3 (Lvm.phiMap v ch) = Verifier.phiMap (FE.toExt3 v) (ch.map FE.toExt3) := by
  unfold Lvm.phiMap Verifier.phiMap
  rw [toExt3_foldl (Prod.map FE.toExt3 id) _
    (fun value (cs : E × ℕ) ↦ value + cs.1 * value ^ (2 ^ cs.2)) fun a b ↦ ?_]
  · rw [← List.zip_map_left]; rfl
  · obtain ⟨c, s⟩ := b
    simp only [tE_add, tE_mul, toExt3_frob, Prod.map, id]

theorem map_ringCoefficients (ch : List FE) :
    (Lvm.ringCoefficients ch).map FE.toExt3 = Verifier.ringCoefficients (ch.map FE.toExt3) := by
  unfold Lvm.ringCoefficients Verifier.ringCoefficients
  rw [List.map_map, show Lvm.kBits = Verifier.kBits from rfl]
  refine List.map_congr_left fun k _ ↦ ?_
  simp only [Function.comp]
  rw [toExt3_foldl (Prod.map FE.toExt3 id) _
    (fun acc (fs : E × ℕ) ↦ acc * fs.1 ^ (2 ^ (k % fs.2))) fun a b ↦ ?_, tE_one]
  · rw [List.zip_map_left, List.filter_map]; rfl
  · obtain ⟨f, s⟩ := b
    simp only [tE_mul, toExt3_frob, Prod.map, id]

theorem toExt3_ringProduct (l rP : List FE) (c : FE) :
    FE.toExt3 ((List.zip l rP).foldl (fun product (vc : FE × FE) => product * (1 + vc.1 + vc.2)) c) =
      (List.zip (l.map FE.toExt3) (rP.map FE.toExt3)).foldl
        (fun product (vc : E × E) => product * (1 + vc.1 + vc.2)) (FE.toExt3 c) := by
  rw [toExt3_foldl (Prod.map FE.toExt3 FE.toExt3) _
    (fun product (vc : E × E) => product * (1 + vc.1 + vc.2)) fun a b ↦ ?_, List.zip_map]
  simp only [tE_mul, tE_add, tE_one, Prod.map]

theorem toExt3_ringWeight (r rP cs : List FE) :
    FE.toExt3 (Lvm.ringWeight r rP cs) =
      Verifier.ringWeight (r.map FE.toExt3) (rP.map FE.toExt3) (cs.map FE.toExt3) := by
  unfold Lvm.ringWeight Verifier.ringWeight
  suffices h : ∀ (cs : List FE) (acc : FE × List FE),
      (FE.toExt3 (cs.foldl (fun (acc : FE × List FE) c =>
          ((acc.1 + (List.zip acc.2 rP).foldl (fun product (vc : FE × FE) =>
            product * (1 + vc.1 + vc.2)) c), acc.2.map FE.sq)) acc).1,
        (cs.foldl (fun (acc : FE × List FE) c =>
          ((acc.1 + (List.zip acc.2 rP).foldl (fun product (vc : FE × FE) =>
            product * (1 + vc.1 + vc.2)) c), acc.2.map FE.sq)) acc).2.map FE.toExt3) =
      (cs.map FE.toExt3).foldl (fun (acc : E × List E) c =>
          ((acc.1 + (List.zip acc.2 (rP.map FE.toExt3)).foldl (fun product (vc : E × E) =>
            product * (1 + vc.1 + vc.2)) c), acc.2.map (· ^ 2))) (FE.toExt3 acc.1, acc.2.map FE.toExt3) by
    have := congrArg Prod.fst (h cs (0, r))
    simp only [tE_zero] at this
    exact this
  intro cs
  induction cs with
  | nil => intro acc; rfl
  | cons c cs ih =>
    intro acc
    simp only [List.foldl_cons, List.map_cons]
    rw [ih]
    simp only [tE_add, toExt3_ringProduct, List.map_map]
    congr 3
    funext x
    exact toExt3_sq_eq_pow x

/-! ## Native lengths and the ring switch's refinement -/

theorem length_samples : ∀ (n : ℕ) (sig : ByteArray) (s : RS), (runD (DM.samples n) sig s).1.length = n
  | 0, _, _ => rfl
  | n + 1, sig, _ => congrArg (· + 1) (length_samples n sig _)

theorem length_readEs : ∀ (n : ℕ) (sig : ByteArray) (s : RS), (runD (DM.readEs n) sig s).1.length = n
  | 0, _, _ => rfl
  | n + 1, sig, _ => congrArg (· + 1) (length_readEs n sig _)

theorem length_sumcheck (count : ℕ) : ∀ (eqs : List (Option FE)) (claim : FE) (sig : ByteArray) (s : RS),
    (runD (Lvm.sumcheck claim count eqs) sig s).1.1.length = eqs.length
  | [], _, _, _ => rfl
  | _ :: eqs, _, sig, _ => congrArg (· + 1) (length_sumcheck count eqs _ sig _)

section Ref

variable {cap : ℕ → ℕ → ℕ} {occ : ℕ → ℕ → ℕ} {shp : ℕ → ℕ × ℕ} {sig : ByteArray}

/-- A fact about the native step's value. -/
theorem refAt_withD {α β : Type} {d : DM β} {P : LeanVM.Protocol.Compile.VerifierProgram α}
    {R : β → α → Prop} {Q : β → Prop} (h : RefAt cap occ shp sig d P R) (hq : ∀ s, Q (runD d sig s).1) :
    RefAt cap occ shp sig d P fun b a ↦ R b a ∧ Q b := fun s hok ↦ by
  obtain ⟨a, h1, h2, h3, h4⟩ := h s hok
  exact ⟨a, h1, h2, h3, h4, hq s⟩

theorem monoD_ringRaw (s : List FE) : MonoD (Lvm.ringRaw s) :=
  (monoD_samples _).bind fun _ ↦ MonoD.pure _

/-- **V_S's caller-placed ring switch** refines leanVM's `ringSwitch` at any point: the same
target, the weight `ringWeight pt · coeffs` on the coefficients' images. -/
theorem ref_ringRaw (s : List FE) (pt : List E) :
    RefAt cap occ shp sig (Lvm.ringRaw s) (Verifier.ringSwitch pt (s.map FE.toExt3))
      fun r r' ↦ r' = (FE.toExt3 r.1, fun x ↦ Verifier.ringWeight pt x (r.2.map FE.toExt3)) := by
  refine RefAt.bind (fun _ ↦ MonoD.pure _) (ref_samples ringStages) ?_
  rintro ch _ rfl
  refine RefAt.pure ?_
  simp only [toExt3_polyEval, toExt3_gen, List.map_map, map_ringCoefficients, Function.comp_def,
    toExt3_phiMap]

end Ref

end Lvm.VEq.Lk
end
-- ===== end of `LvmVEqLinkArith` =====

-- ===== merged from `LvmVEqLink` (GOLF module merge: `LvmVEqLink.lean` is now a stub importing `LvmVEqTop`) =====
section
-- New for lvm (WP-14a, H3): V_S's phases 5 and 7 (LvmVEqPhases `dChLink`, `dKsLink`, the CH and KS links of
-- `M3.real P20`) refine WP-8's DSL programs (`Lvm.KG.chLinkProg`, `ksLinkProg`) on the stream, their claims
-- related by `CRel` to LvmVEqMid's `chLinkClaimsE`, `ksLinkClaimsE`.

/-!
# The `CH` and `KS` links: V_S refines the verifier language

(lvm2 S2: v1's `CH` link is gone from V_S, so `ref_dChLink` is deleted.) v1's `ref_dChLink`: wherever V_S's phase 5 ends with its checks held, WP-8's `chLinkProg 20 52` read off
the stream returns `lo` at the same cursor with V_S's link claims `CRel`-related to
`chLinkClaimsE lo`; `ref_dKsLink` the same for phase 7, `ksLinkProg 13 9 (contRows P20)` (KS13, lvm2 roll 8, B1;
roll 7: `ksLinkProg 14 10`, KS14) and
`ksLinkClaimsE`. Read for read: the samples and scalars by `ref_samples`/`ref_readEs`, the sumchecks
by H1's `ref_sumcheck` (their claims transported by LvmVEqLinkArith), the caller-placed ring switches
by `ref_ringRaw`, the final `require` by the transported check (`toExt3_chOk`, `toExt3_ksOk`).
`monoD_dChLink`, `monoD_dKsLink` hold for every `p`, `m`.
-/

set_option autoImplicit false

namespace Lvm.VEq

open Lvm DM LeanVM.Parameters LeanVM.Protocol LeanVM.Protocol.KeccakGkr Finset Lk
open Lvm.M3 (tE_add tE_mul tE_zero tE_one tE_ofK FE_eq_of_beq)

/-! ## `MonoD` -/

theorem monoD_dChLink (p : Params) (m : M3) (r v : List FE) (pub : Pub) :
    MonoD (dChLink p m r v pub) :=
  (monoD_samples _).bind fun _ ↦ (monoD_sumcheck _ _ _).bind fun _ ↦ (monoD_readEs _).bind fun _ ↦
    (monoD_ringRaw _).bind fun _ ↦ (monoD_sumcheck _ _ _).bind fun _ ↦ (monoD_readEs _).bind fun _ ↦
      (monoD_ringRaw _).bind fun _ ↦ (monoD_samples _).bind fun _ ↦
        (MonoD.require _).bind fun _ ↦ MonoD.pure _

theorem monoD_dKsLink (p : Params) (m : M3) (rk : List FE) (pub : Pub) : MonoD (dKsLink p m rk pub) :=
  (monoD_samples _).bind fun _ ↦ (monoD_sumcheck _ _ _).bind fun _ ↦ (monoD_readEs _).bind fun _ ↦
    (MonoD.require _).bind fun _ ↦ MonoD.pure _

/-! ## Refinement -/

section Ref

variable {cap : ℕ → ℕ → ℕ} {occ : ℕ → ℕ → ℕ} {shp : ℕ → ℕ × ℕ} {sig : ByteArray}

namespace Lk

theorem forall₂_map_both {α β γ δ : Type} {R : γ → δ → Prop} {f : α → γ} {g : β → δ} {l : List α}
    {l' : List β} (h : List.Forall₂ (fun a b ↦ R (f a) (g b)) l l') :
    List.Forall₂ R (l.map f) (l'.map g) :=
  List.forall₂_map_left_iff.2 (List.forall₂_map_right_iff.2 h)

theorem ref_samplesL (n : ℕ) :
    RefAt cap occ shp sig (DM.samples n) (Compile.VerifierProgram.sampleChallenges n)
      fun xs ys ↦ ys = xs.map FE.toExt3 ∧ xs.length = n :=
  refAt_withD (ref_samples n) (Q := fun xs ↦ xs.length = n) (length_samples n sig)

theorem ref_readEsL (n : ℕ) :
    RefAt cap occ shp sig (DM.readEs n) (Compile.VerifierProgram.readScalars n)
      fun xs ys ↦ ys = xs.map FE.toExt3 ∧ xs.length = n :=
  refAt_withD (ref_readEs n) (Q := fun xs ↦ xs.length = n) (length_readEs n sig)

theorem ref_sumcheckL (count : ℕ) (eqs : List (Option FE)) (claim : FE) :
    RefAt cap occ shp sig (Lvm.sumcheck claim count eqs)
      (Verifier.sumcheck (FE.toExt3 claim) count (eqs.map (Option.map FE.toExt3)))
      fun r r' ↦ r' = (r.1.map FE.toExt3, FE.toExt3 r.2) ∧ r.1.length = eqs.length :=
  refAt_withD (ref_sumcheck count eqs claim) (Q := fun r ↦ r.1.length = eqs.length)
    (length_sumcheck count eqs claim sig)

end Lk

/-- **A native claim against a spec claim, M′** (lvm2 roll 11, `S2GM`): the same claim (`CRel`), or V_S's `C_main`
claim on the stream block `S` against a `C_rec` claim, through the relocation `relocS`. -/
def CRelM (a : Com × Lvm.BlockClaim) (b : Com × BClaim) : Prop :=
  CRel a b ∨ (a.1 = .main ∧ b.1 = .crec ∧ SCRel a.2.onStack (relocS b.2.onStack))

theorem CRel.crelM {a : Com × Lvm.BlockClaim} {b : Com × BClaim} (h : CRel a b) : CRelM a b := Or.inl h

/-- **V_S's phase 7 (the `KS` link) refines WP-8's `ksLinkProg`** (lvm2 CR-K; KS13, lvm2 roll 8, B1: `ksLog = 13`,
`X` on `2^9` rows, V_S's `ksLink14`; roll 7: KS14, `ksLinkProg (10 + 4) 10`). lvm2 roll 11, M′ `S2GM`: V_S's four
claims are on `C_main`; `M`'s (on the stream block `S`) is the spec's `C_rec` claim relocated (`CRelM`; B1: `CRel`). -/
theorem ref_dKsLink (tabs : Pub → List M3.Tab) (rk : List FE) (pub : Pub) :
    Ref20 sig (dKsLink P20 (M3.real P20 tabs) rk pub) (Lvm.KG.ksLinkProg (9 + 4) 9 (contRows P20))
      (fun cl out ↦ List.Forall₂ CRelM cl (ksLinkClaimsE out.1 out.2.1 out.2.2)) := by
  unfold dKsLink Lvm.KG.ksLinkProg
  -- ρ, λ
  refine RefAt.bind (fun _ ↦ (monoD_sumcheck _ _ _).bind fun _ ↦ (monoD_readEs _).bind fun _ ↦
    (MonoD.require _).bind fun _ ↦ MonoD.pure _) (ref_samplesL _) ?_
  rintro kchal _ ⟨rfl, hk⟩
  replace hk : kchal.length = 18 := hk
  -- the shift sumcheck (claim 0)
  have h2 := ref_sumcheckL (cap := capS) (occ := occS) (shp := shpS) (sig := sig) 3 (List.replicate 13 none) 0
  simp only [tE_zero, List.map_replicate, Option.map_none] at h2
  refine RefAt.bind (fun _ ↦ (monoD_readEs _).bind fun _ ↦
    (MonoD.require _).bind fun _ ↦ MonoD.pure _) h2 ?_
  rintro ⟨rho', f⟩ _ ⟨rfl, hr⟩
  replace hr : rho'.length = 13 := hr
  -- the four scalars
  refine RefAt.bind (fun _ ↦ (MonoD.require _).bind fun _ ↦ MonoD.pure _) (ref_readEs _) ?_
  rintro vals _ rfl
  have h14 : P20.ksLog ≤ P20.recRowsLog := by decide
  -- the check and the claims
  refine RefAt.bind (fun _ ↦ MonoD.pure _) (RefAt.require fun hok ↦ ?_) fun _ _ _ ↦ RefAt.pure ?_
  · have h := congrArg FE.toExt3 (FE_eq_of_beq hok)
    dsimp only at h ⊢
    simp only [M3.real, M3.realW, M3.ofParts, Lvm.ksLink0, if_pos h14, Lvm.ksLink14,
      show P20.ksLog = 13 from rfl] at h
    rw [toExt3_ksOk _ _ _ hk hr] at h
    simpa only [Nat.reduceAdd] using h
  · dsimp only
    simp only [M3.real, M3.realW, M3.ofParts, Lvm.ksLink0, if_pos h14, Lvm.ksLink14, ksLinkClaimsE]
    have hom (l : ℕ) : (Verifier.eqKernel ((kchal.map FE.toExt3).drop 13)).getD l 0 =
        FE.toExt3 ((Lvm.eqKernel (kchal.drop P20.ksLog)).getD l 0) := by
      rw [← List.map_drop, ← map_eqKernel, getD_map_toExt3]; rfl
    have hsel : Lvm.KG.selX 9 (rho'.map FE.toExt3) = FE.toExt3 (prodE (rho'.drop (ksXLog P20))) := by
      rw [toExt3_prodE, EndToEnd.Complete.prodE_eq, ksXLog_P20, Lvm.KG.selX, List.map_drop]
    refine .cons (CRel.crelM ⟨rfl, sumClaim_rel _ _ _ ?_ (getD_map_toExt3 _ _)⟩)
      (.cons (CRel.crelM ⟨rfl, sumClaim_rel _ _ _ ?_ (getD_map_toExt3 _ _)⟩)
        (.cons (Or.inr ⟨rfl, rfl, ?_⟩)
          (.cons (CRel.crelM ⟨rfl, sumClaim_rel _ _ _ ?_ (getD_map_toExt3 _ _)⟩) .nil)))
    · rw [List.map_map]
      refine List.map_congr_left fun l _ ↦ ?_
      simp only [Function.comp, partE, hom, (ksYPart_rel l rho').1, (ksYPart_rel l rho').2]
    · rw [List.map_map]
      refine List.map_congr_left fun l _ ↦ ?_
      simp only [Function.comp, partE, hom, List.map_append, map_selectorPoint]
      rfl
    · -- `M` on `S`: V_S's sum on `C_main` is the spec's `C_rec` sum relocated
      rw [← relocS_sum]
      · refine onStack_rel (sumClaim_rel _ _ _ ?_ (getD_map_toExt3 _ _))
        rw [List.map_append, List.map_append, List.map_map, List.map_map, List.map_map, List.map_map]
        congr 1 <;> refine List.map_congr_left fun l _ ↦ ?_
        · simp only [Function.comp, partE, hom, shiftS]
          rfl
        · simp only [Function.comp, partE, hom, hsel, tE_mul, ← List.map_take, ksXLog_P20, shiftS]
          have hs : (layout0 P20).s = CMain.sOff20 := by rw [layout0_P20]
          have hR : P20.recRowsLog = 14 := by decide
          rw [hs, hR, Nat.add_assoc]
          rfl
      · intro q hq
        rcases List.mem_append.mp hq with hq | hq <;> obtain ⟨l, hl, rfl⟩ := List.mem_map.mp hq <;>
          have hl' := List.mem_range.mp hl <;>
          simp only [Nat.shiftRight_eq_div_pow, CMain.sOff20, ksSplit_P20] <;> norm_num <;> (clear * - hl'; omega)
    · rw [List.map_map]
      refine List.map_congr_left fun l _ ↦ ?_
      simp only [Function.comp, partE, hom, ← List.map_take, ksXLog_P20]
      rfl

end Ref

end Lvm.VEq
end
-- ===== end of `LvmVEqLink` =====

/-!
# V_S's phases 4–7 refine `kgProgS`

`dBusTab` (the bus path's phases 2–3b, dead at B1), `dKg` (phases 4–7, grouped as `kgProgS`); against `kgProgS`:
phases 4–5 by `ref_dTapeW` (`ref_dTape`, `ref_dWire`), phase 6 by H2's `ref_dKec`, phase 7 by `ref_dKsLink`
(**`ref_dKg`**, relation `KgRel`); `dClaims_rel`: the claims of the tape, `KS` and its output lanes, claim for claim
(`CRel`); the `KS` link's by `CRelM` (M′: `M` on `S`).
-/

set_option autoImplicit false

namespace Lvm.VEq

open Lvm DM LeanVM.Parameters LeanVM.Protocol LeanVM.Protocol.Compile Lk
open LeanVM.Protocol.Whir.Sound (cfgMain24G)

/-! ## `decideProg` grouped as `P_S` -/

/-- The native result of a Keccak phase (`dKec`). -/
abbrev KecN : Type := List FE × List FE × Lvm.KeccakOut × (FE × (List FE → FE))

/-- Phases 2–3b (A23: the table phase's evaluations, then phase 3b's folded accumulator). -/
def dBusTab (p : Params) (m : M3) (pub : Pub) :
    DM (((List FE × BusOut) × List (List FE × List FE)) × Acc) :=
  (dBus p m pub >>= fun pb ↦ dTab p m pub pb.1 pb.2 >>= fun ev ↦ pure (pb, ev)) >>= fun bt ↦
    accFold p m pub bt.2 >>= fun acc ↦ pure (bt, acc)

/-- Phases 4–7, grouped as `kgProgS` (lvm2 S2: the tape and the wire, then `KS` and its link). -/
def dKg (p : Params) (m : M3) (pub : Pub) :
    DM ((TapeRes × (WireOut × List FE)) × (KecN × List (Com × BlockClaim))) :=
  (dTape p.logN >>= fun tp ↦ dRange p pub >>= fun _ ↦ Shape.dWireC p pub tp.claim >>= fun wo ↦
      pure (tp, wo)) >>= fun tw ↦
    (dKec p.ksLog >>= fun ks ↦ dKsLink p m ks.1 pub >>= fun klc ↦ pure (ks, klc)) >>= fun ksN ↦
      pure (tw, ksN)

/-! ## `MonoD` -/

theorem monoD_dKg (p : Params) (m : M3) (pub : Pub) : MonoD (dKg p m pub) :=
  ((monoD_dTape _).bind fun _ ↦ (MonoD.require _).bind fun _ ↦ (Shape.monoD_dWireC _ _ _).bind fun _ ↦
    MonoD.pure _).bind fun _ ↦
    ((monoD_dKec _).bind fun _ ↦ (monoD_dKsLink _ _ _ _).bind fun _ ↦ MonoD.pure _).bind fun _ ↦
      MonoD.pure _

/-! ## The claims -/

/-- The native tape and wire against the tape caller's output (lvm2 S2; roll 7: `r`'s length and the
ring claim's weight at the returned coefficients). -/
def TapeWRel (tw : TapeRes × (WireOut × List FE)) (o : Lvm.KG.TapeOutE) : Prop :=
  o.1 = tw.1.r.map FE.toExt3 ∧ o.2.1 = tw.1.v.map FE.toExt3 ∧ o.2.2.1 = kcE tw.1.claim ∧
    WireRel 20 tw.2.1 o.2.2.2 ∧ tw.1.r.length = 20 ∧ Shape.WireRing P20 tw.2

/-- The native and the language's outputs of phases 4–7 (`KS` at `9 + 4`: KS13, lvm2 roll 8, B1; roll 7: `10 + 4`; lvm2
roll 11, M′: the `KS` link's claims by `CRelM`, `M` on `S` against the spec's relocated `C_rec` claim). -/
def KgRel (kg : (TapeRes × (WireOut × List FE)) × (KecN × List (Com × BlockClaim))) (kg' : KgOut) : Prop :=
  TapeWRel kg.1 kg'.1 ∧
    (KecRel (9 + 4) kg.2.1 kg'.2.1 ∧
      List.Forall₂ CRelM kg.2.2 (ksLinkClaimsE kg'.2.2.1 kg'.2.2.2.1 kg'.2.2.2.2))

theorem forall₂_main {l : List BlockClaim} {l' : List BClaim} (h : List.Forall₂ BCRel l l') :
    List.Forall₂ CRel (l.map (.main, ·)) (l'.map (.main, ·)) :=
  forall₂_map_both (h.imp fun _ _ h ↦ ⟨rfl, h⟩)

/-- **The claim list of phases 2–6** (all but the `KS` link's, which `KgRel` relates by `CRelM`): V_S's against
`assembleS`'s, claim for claim (lvm2 roll 11, M′: B1's `dClaims_rel` over the whole list, now split at the link). -/
theorem dClaims_rel (tabs : Pub → List M3.Tab) (pub : Pub)
    (kg : (TapeRes × (WireOut × List FE)) × (KecN × List (Com × BlockClaim))) (kg' : KgOut)
    (hk : KgRel kg kg') :
    List.Forall₂ CRel ((tapeClaims P20 kg.1.1 kg.1.2.1 pub ++ keccakClaims (M3.real P20 tabs).ksBlock kg.2.1.2.2.1
        kg.2.1.2.2.2).map (.main, ·) ++ (M3.real P20 tabs).ksOutputClaims kg.2.1.1 kg.2.1.2.1)
      ((tapeClaimsE kg'.1 pub ++ keccakClaimsE ksBlk kg'.2.1).map (.main, ·) ++
        ksOutputClaimsE kg'.2.1.1 kg'.2.1.2.1) := by
  obtain ⟨⟨hr, hv, -, hw, -, -⟩, ⟨hks, -⟩⟩ := hk
  have hk1 := hks.1
  have hk2 := hks.2.1
  refine forall₂_append (forall₂_main
    (forall₂_append (tapeClaims_rel _ _ _ pub hr hv hw.2.2.2.2.1 hw.2.2.2.2.2.1)
      (keccakClaims_rel hks _))) ?_
  rw [hk1, hk2]
  exact ksOutputClaims_rel _ _

/-! ## `s` from the statement -/

theorem get!_hdX_x (x : List UInt8) (t : ℕ) :
    (⟨(List.replicate 8 0 ++ x).toArray⟩ : ByteArray).get! (8 + t) = x.getD t 0 := by
  rw [get!_mk, List.getD_append_right _ _ _ _ (by simp), List.length_replicate,
    Nat.add_sub_cancel_left]

theorem get!_sigOfX_x' (x : List UInt8) (t : ℕ) : (sigOfX x).get! (headerAt 8 + t) = x.getD t 0 := by
  rw [sigOfX, get!_mk, List.getD_append_right _ _ _ _ (by simp), List.length_replicate,
    Nat.add_sub_cancel_left]

/-- **The statement's chain start**: V_S's `s` lanes are the header digest `s`'s (lvm2 S2: the wire
phase's `Pad43(s)`). -/
theorem pubX_s (x : List UInt8) : (pubX x).s = digestLanes (hdX x).s := by
  have e : ∀ i < 4, ∀ j < 8, ((hdX x).s.toArray.getD (8 * i + j) 0) =
      (sigOfX x).get! (headerAt 80 + 8 * i + j) := by
    intro i hi j hj
    rw [Array.getD_eq_getD_getElem?, Vector.getElem?_toArray, Vector.getElem?_eq_getElem (by omega)]
    simp only [hdX, Header.ofProof, digestAt, Vector.getElem_ofFn, Option.getD_some, offS]
    rw [show 80 + (8 * i + j) = 8 + (72 + 8 * i + j) by (clear * -; omega), get!_hdX_x,
      show headerAt 80 + 8 * i + j = headerAt 8 + (72 + 8 * i + j) by simp only [headerAt]; (clear * -; omega),
      get!_sigOfX_x']
  unfold pubX pubOf digestLanes
  refine List.map_congr_left fun i hi ↦ ?_
  have hi' := List.mem_range.mp hi
  have e0 := e i hi' 0 (by (clear * -; omega))
  simp only [Nat.add_zero] at e0
  simp only [show List.range 8 = [0, 1, 2, 3, 4, 5, 6, 7] from rfl, List.foldl_cons, List.foldl_nil,
    e0, e i hi' 1 (by (clear * -; omega)), e i hi' 2 (by (clear * -; omega)), e i hi' 3 (by (clear * -; omega)),
    e i hi' 4 (by (clear * -; omega)), e i hi' 5 (by (clear * -; omega)), e i hi' 6 (by (clear * -; omega)), e i hi' 7 (by (clear * -; omega)), kAt, laneAt,
    UInt64.zero_or, Nat.add_zero, Nat.add_assoc]

/-! ## Refinement -/

section Ref

variable {sig : ByteArray}

theorem dSel_P20 : dSel P20 = 0 := by decide +kernel

/-- `D`'s selector bits at P20: `ν − 22 = 1` (B1, ν = 23; roll 7: `2`). -/
theorem dSelBits_P20 : dSelBits P20 = 1 := by decide +kernel

/-- The tape caller as the tape phase, then the wire phase. -/
theorem tapeProg_eq (w sb dsel : ℕ) (s : RecursionFast.Digest) (n : ℕ) :
    Lvm.KG.tapeProg w sb dsel s n =
      (VerifierProgram.sampleChallenges w >>= fun r ↦ VerifierProgram.readScalars 25 >>= fun v ↦
        KeccakGkr.tapeGkr w r v >>= fun claim ↦ VerifierProgram.ret (r, v, claim)) >>= fun t ↦
      VerifierProgram.require (1 ≤ n ∧ n ≤ 2 ^ w) >>= fun _ ↦
      Lvm.KG.wireChProg w sb dsel s n t.2.2 >>= fun wo ↦ VerifierProgram.ret (t.1, t.2.1, t.2.2, wo) := by
  simp only [Lvm.KG.tapeProg, bind_assoc]
  rfl

/-- **Phases 4–5 refine the tape caller** (lvm2 S2; B1: `D`'s selector bits `dSelBits P20 = 1`, roll 7: `2`). -/
theorem ref_dTapeW (pub : Pub) (d : RecursionFast.Digest) (hs : pub.s = digestLanes d) :
    Ref20 sig (dTape P20.logN >>= fun tp ↦ dRange P20 pub >>= fun _ ↦ Shape.dWireC P20 pub tp.claim >>=
      fun wo ↦ pure (tp, wo))
      (Lvm.KG.tapeProg 20 1 0 d pub.n) TapeWRel := by
  rw [tapeProg_eq]
  refine RefAt.bind (fun _ ↦ (MonoD.require _).bind fun _ ↦ (Shape.monoD_dWireC _ _ _).bind fun _ ↦
    MonoD.pure _) (ref_dTape _) ?_
  rintro tp t ⟨h1, h2, h3, -, h5, -, -⟩
  refine RefAt.bind (fun _ ↦ (Shape.monoD_dWireC _ _ _).bind fun _ ↦ MonoD.pure _)
    (RefAt.require fun hc ↦ of_decide_eq_true hc) ?_
  rintro _ _ _
  have hw := Shape.ref_dWireC (cap := capS) (occ := occS) (shp := shpS) (sig := sig) P20 pub tp.claim d hs
  rw [dSel_P20, dSelBits_P20] at hw
  rw [h5]
  refine RefAt.bind (fun _ ↦ MonoD.pure _) hw ?_
  rintro wo out ⟨hwo, hring⟩
  exact RefAt.pure ⟨h1, h2, rfl, hwo, h3, hring⟩

/-- The `KS` link's claims are `m.ksLink`'s (`dKsLink` returns them unchanged). -/
theorem retD_dKsLink (p : Params) (m : M3) (rk : List FE) (pub : Pub) :
    RetD (fun kl ↦ ∃ i, kl = (m.ksLink i).2) (dKsLink p m rk pub) := by
  unfold dKsLink
  refine RetD.bind_true fun kchal ↦ RetD.bind_true fun kshift ↦ RetD.bind_true fun kvals ↦ ?_
  intro sig s
  rcases h : m.ksLink ⟨kchal, kshift, kvals, rk, pub⟩ with ⟨ok, kl⟩
  exact ⟨⟨kchal, kshift, kvals, rk, pub⟩, by rw [h]; rfl⟩

/-- **Phases 4–7 refine `kgProgS`** (roll 7: the native `KS` link claims are `ksLink`'s; roll 8, B1: KS13, `tapeProg 20 1 0`). -/
theorem ref_dKg (tabs : Pub → List M3.Tab) (pub : Pub) (d : RecursionFast.Digest)
    (hs : pub.s = digestLanes d) :
    Ref20 sig (dKg P20 (M3.real P20 tabs) pub) (kgProgS d pub.n)
      (fun kg kg' ↦ KgRel kg kg' ∧ ∃ i, kg.2.2 = ((M3.real P20 tabs).ksLink i).2) := by
  unfold dKg kgProgS
  refine RefAt.bind (fun _ ↦ ((monoD_dKec _).bind fun _ ↦ (monoD_dKsLink _ _ _ _).bind fun _ ↦
    MonoD.pure _).bind fun _ ↦ MonoD.pure _) (ref_dTapeW pub d hs) ?_
  intro tw tp htw
  refine RefAt.bind (fun _ ↦ MonoD.pure _)
    (R := fun ksN ks ↦ (KecRel (9 + 4) ksN.1 ks.1 ∧
      List.Forall₂ CRelM ksN.2 (ksLinkClaimsE ks.2.1 ks.2.2.1 ks.2.2.2)) ∧
        ∃ i, ksN.2 = ((M3.real P20 tabs).ksLink i).2) ?_ ?_
  · refine RefAt.bind (fun _ ↦ (monoD_dKsLink _ _ _ _).bind fun _ ↦ MonoD.pure _) (ref_dKec _) ?_
    intro ks co hco
    refine RefAt.bind (fun _ ↦ MonoD.pure _)
      ((ref_dKsLink tabs ks.1 pub).retD (retD_dKsLink _ _ _ _)) ?_
    rintro klc lo ⟨hlo, hi⟩
    exact RefAt.pure ⟨⟨hco, hlo⟩, hi⟩
  rintro ksN ks ⟨hks, hi⟩
  exact RefAt.pure ⟨⟨htw, hks⟩, hi⟩

theorem smallP_P20 (x : List UInt8) : Shape.smallP P20 (pubX x) = Shape.small x := by
  unfold Shape.smallP Shape.small
  rw [show (P20.logN == 20 && P20.nuMain == CMain.nu20) = true by decide +kernel, Bool.true_and]

theorem commitRootUd_main : Verifier.commitRootUd cfgMain24G = VerifierProgram.readCommitment 19 64 := rfl

end Ref

end Lvm.VEq
