-- New for lvm2 (CR-V, roll 7 SH2-Z; CR-DES §1.5): V_S's small `C_main` claims against `onStackZs`.
-- The wire phase with the ring coefficients (`dWireC`) refines as `dWire` does; at `P20` every
-- `C_main` claim of `dClaimsT` is an aligned block inside the stack and carries its tail value
-- (`tails_main`); the small opening (`dOpenZ`) refines the two stacked WHIR openings.
import LvmShape
import LvmVEqWire
import LvmVEqClaims
import LvmVEqTape
import LvmVEqWhir

/-!
# V_S's small claims refine `onStackZs`

* **`ref_dWireC`**: `dWireC` refines T-W's wiring program with `WireRel` and `WireRing` (the ring
  claim's weight is `ringWeight` at `wirePt` with the returned coefficients).
* **`dClaimsT_fst`**: without the tails, `dClaimsT` is `dClaims`.
* **Tails per claim kind at `P20`** (each from `LvmShape`'s closed forms, none assumed):
  `table_tails` (`colsFitB`, `colsHiB`: blocks from word `2^22`), `ks_tails` (`KS`'s two claims),
  `ksOut_tails` (`KS`'s 25 output lanes), `ksLink_tails` (the link's three `C_main` sums),
  `tape_tails` (`D`'s point claims `tailDF`, the ring claim `ringTailN`, the boundary claims `0`);
  **`tails_main`**: every `C_main` claim of `dClaimsT` is `InStack` and its tail is `tailValueF`.
* **`ref_dOpenZ`**: the openings in both shapes refine `verifyStackedJ` on `SCRel`-related lists.
-/

set_option autoImplicit false

namespace Lvm.Shape

open Lvm Lvm.VEq DM LeanVM.Parameters LeanVM.Protocol LeanVM.Protocol.Compile
open LeanVM.Protocol.Whir.Sound (cfgRec20Jp cfgMain23Jq)

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
  ⟨by have := h.2.1; unfold CMain.nu20; omega, h.2.2.2, h.2.2.1⟩

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
      omega

/-- **`KS`'s output lanes** have no tail. -/
theorem ksOut_tails (rk v : List FE) : ∀ e ∈ ksOutputClaims0 P20 rk v, OffOK e.2.block := by
  intro e he
  unfold ksOutputClaims0 at he
  obtain ⟨l, hl, rfl⟩ := List.mem_map.mp he
  exact offOK_ksY l (List.mem_range.mp hl) rk

/-- **The `KS` link's `C_main` claims** (`yC`, `inC`, `xC`, sums on `⟨ν, 0⟩`) have no tail. -/
theorem ksLink_tails (i : KsLinkIn) :
    ∀ e ∈ (ksLink0 P20 i).2, e.1 = .main → InStack e.2.block ∧ tailValueF e.2.onStack.1 = 0 := by
  have hw : InStack ⟨P20.nuMain, 0⟩ := by rw [nuMain_P20]; decide
  intro e he hm
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
  · simp at hm
  · refine ⟨hw, ?_⟩
    simp only [nuMain_P20]
    refine tailValueF_sum _ _ fun q hq ↦ ?_
    obtain ⟨l, hl, rfl⟩ := List.mem_map.mp hq
    have h := offOK_x l (List.mem_range.mp hl)
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
    rw [logN_P20, tailValueF_bnd _ (by omega) l hl]

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

/-- **Phases 8–9 at `P20` in both shapes**: V_S's two stacked openings refine `verifyStackedJ cfgRec20Jp`
then `verifyStackedJ (cfgMain23Jq 3)` (B1, ν = 23; roll 7: `cfgMain24J 3`) on `SCRel`-related lists
(`C_main`'s through `onStackZsF s`). -/
theorem ref_dOpenZ {sig : ByteArray} (s : Bool) (claims : List (Com × BlockClaim × FE))
    (cl : List VStackClaim × List VStackClaim)
    (h1 : List.Forall₂ SCRel ((claims.filter (·.1 == .crec)).map (·.2.1.onStack)) cl.1)
    (h2 : List.Forall₂ SCRel (onStackZsF s ((claims.filter (·.1 == .main)).map (·.2))) cl.2) :
    Ref20 sig (dOpenZ P20 s claims)
      (Verifier.verifyStackedJ cfgRec20Jp cl.1 >>= fun _ ↦ Verifier.verifyStackedJ (cfgMain23Jq 3) cl.2)
      (fun _ _ ↦ True) :=
  RefAt.bind (fun _ ↦ monoD_verifyStacked _ _ _ _ _ _)
    (ref_verifyStackedJ _ cfgRec20Jp _ _ _ _ _ h1 recOod_P20 rfl rfl rfl rfl rfl corrRec20)
    fun _ _ _ ↦ ref_verifyStackedJ _ (cfgMain23Jq 3) _ _ _ _ _ h2 mainOod_P20 rfl rfl rfl rfl rfl corrMain24

end Lvm.Shape
