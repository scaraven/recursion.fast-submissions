-- New for lvm2 E2-FT (stage S2GT, E2F-T-H1): V_S's typed phases at S2GT (`LvmE2TV`) refine the specification's
-- (`LvmE2TProg`) on the width-aware stream (E2F-V's `RefAtW`), read for read.
import LvmE2TVKernF
import LvmE2VEqRounds
import LvmTypedVEqTop
import LvmE2TZero

/-!
# The typed phases at S2GT: V_S refines the specification

The typed phase reads `E2` scalars (16 B), nonces (8 B) and, in the mini-bus, `E3` scalars (24 B), so its
refinement is E2F-V's width-aware `RefAtW` (`ivpW rw`):

* **`RefAtWP`**: `RefAtW` under a promise on the native value (`RefAtP`'s twin: A23's `Φ_Q` check is the
  decision's); rules `RefAtW.toP`, `RefAtWP.bind`, `RefAtWP.require_left`, `RefAtWP.pure_require`;
* **the bridge** `RefAt.toW`: a roll-11 refinement (`ivp`, 24-B reads) of a program that follows atoms `as`
  (`FolP`) is a `RefAtW` from read index `i` to `i + nrd(as)` where the widths there are `24` (`ivpW_fol`);
* the phases with their widths: `refW_dZeroT` (`wZeroT`), `refW_dWiringT` (`wWireT`, `virtD_rel`),
  `refW_dRelayT2` (`wRelayT`, `relayKernD_rel`), `refW_dAccT` (`wAccT`, under the promise), the mini-bus
  (roll 11's `ref_dMiniT` through the bridge at `folP_miniBusProg`'s atoms, `nMiniRd` reads of 24 B);
* **`ref_dTypedT`**: the typed phases against `typedProgT (N.inst Q lay) pub` (`TRelTT`: the native claims
  are `typedClaimsND` of values whose images `typedClaimsT` takes), under the promise that the folded claim holds
  natively (`N.phiT` at `E2` on the accumulator's lanes 0–1), on `TRefHypT` (roll 11's `TRefHyp` with
  `N.phiT` the specification's `Φ_Q` at `E2`, 45 coordinates); and `MonoD` of each phase.
-/

set_option autoImplicit false

namespace Lvm.E2T

open Lvm DM LeanVM.Parameters LeanVM.Protocol.Compile
open Lvm.VEq
open Lvm.TypedV (TNat dMiniT fitsMiniB)
open Lvm.Typed (xVars yVars selBitsT phiVarsT relayRounds Lay PhiQFT PhiQT PhiQF)
open Lvm.M3 (Tab sumcheckTabs tableClaimsR claimsOfEvs AllSc lbusTableCheckProg)
open Lvm.FE2 (toE2)

/-! ## `MonoD` -/

theorem monoD_dZeroT : MonoD dZeroT :=
  monoD_sepE2.bind fun _ ↦ (monoD_samplesG _ _).bind fun _ ↦ (monoD_sampleG _).bind fun _ ↦
    (monoD_sumcheckD _ _ _ _).bind fun _ ↦ (monoD_readE2s _).bind fun _ ↦ (MonoD.require _).bind fun _ ↦
      MonoD.pure _

theorem monoD_dWiringT (N : TNatT) (pub : Pub) (v : List FE2) : MonoD (dWiringT N pub v) :=
  (monoD_sampleG _).bind fun _ ↦ (monoD_sumcheckD _ _ _ _).bind fun _ ↦ (monoD_readE2s _).bind fun _ ↦
    (monoD_readE2s _).bind fun _ ↦ (MonoD.require _).bind fun _ ↦ MonoD.pure _

theorem monoD_dRelayT2 (N : TNatT) (ry : List FE2) (vS : FE2) : MonoD (dRelayT2 N ry vS) :=
  (monoD_sumcheckD _ _ _ _).bind fun _ ↦ monoD_readE2.bind fun _ ↦ (MonoD.require _).bind fun _ ↦
    MonoD.pure _

theorem monoD_dAccT (pub : Pub) (rxy vs : List FE2) : MonoD (dAccT pub rxy vs) :=
  (monoD_samplesG _ _).bind fun _ ↦ (monoD_readE2s _).bind fun _ ↦ (monoD_sampleG _).bind fun _ ↦
    monoD_readE2.bind fun _ ↦ (MonoD.require _).bind fun _ ↦ (MonoD.require _).bind fun _ ↦
      (MonoD.require _).bind fun _ ↦ MonoD.pure _

theorem monoD_dTypedT (p : Params) (N : TNatT) (m : M3) (pub : Pub) : MonoD (dTypedT p N m pub) :=
  E2T.monoD_dZeroT.bind fun _ ↦ (E2T.monoD_dWiringT _ _ _).bind fun _ ↦ (E2T.monoD_dRelayT2 _ _ _).bind fun _ ↦
    (E2T.monoD_dAccT _ _ _).bind fun _ ↦ (Lvm.VEq.monoD_dMiniT _ _ _ _).bind fun _ ↦ MonoD.pure _

/-! ## Returned lengths -/

theorem retD_samplesG (g : ℕ) : ∀ n, RetD (fun xs : List FE2 ↦ xs.length = n) (samplesG g n)
  | 0 => RetD.pure rfl
  | n + 1 => RetD.bind_true fun _ ↦ (retD_samplesG g n).bind fun _ h ↦ RetD.pure (by simp [h])

theorem retD_readE2s : ∀ n, RetD (fun xs : List FE2 ↦ xs.length = n) (readE2s n)
  | 0 => RetD.pure rfl
  | n + 1 => RetD.bind_true fun _ ↦ (retD_readE2s n).bind fun _ h ↦ RetD.pure (by simp [h])

/-! ## The promise variant and the bridge -/

section Ref

variable {cap : ℕ → ℕ → ℕ} {occ : ℕ → ℕ → ℕ} {shp : ℕ → ℕ × ℕ} {rw : ℕ → ℕ} {sig : ByteArray}

/-- A width-aware refinement with a fact on the native value. -/
theorem RefAtW.retD {α β : Type} {i j : ℕ} {d : DM β} {P : VerifierProgram α} {R : β → α → Prop}
    {Q : β → Prop} (h : RefAtW cap occ shp rw sig i d P R j) (hq : RetD Q d) :
    RefAtW cap occ shp rw sig i d P (fun b a ↦ R b a ∧ Q b) j := fun s hok ↦ by
  obtain ⟨a, h1, h2, h3, h4, h5⟩ := h s hok
  exact ⟨a, h1, h2, h3, h4, h5, hq sig s⟩

variable (cap occ shp rw) in
/-- **`d` refines `P` on the width-aware stream under the promise `Q` on `d`'s value.** -/
def RefAtWP {α β : Type} (sig : ByteArray) (i : ℕ) (d : DM β) (P : VerifierProgram α) (R : β → α → Prop)
    (Q : β → Prop) (j : ℕ) : Prop :=
  ∀ s, (runD d sig s).2.ok = true → Q (runD d sig s).1 →
    ∃ a, (ivpW cap occ shp rw P sig s i).1 = some a ∧
      (ivpW cap occ shp rw P sig s i).2.1.ent = (runD d sig s).2.ent ∧
      (ivpW cap occ shp rw P sig s i).2.1.msg = (runD d sig s).2.msg ∧
      (ivpW cap occ shp rw P sig s i).2.2 = j ∧ R (runD d sig s).1 a

theorem RefAtW.toP {α β : Type} {i j : ℕ} {d : DM β} {P : VerifierProgram α} {R : β → α → Prop}
    (h : RefAtW cap occ shp rw sig i d P R j) (Q : β → Prop) : RefAtWP cap occ shp rw sig i d P R Q j :=
  fun s hok _ ↦ h s hok

/-- The end index along an equality. -/
theorem RefAtWP.idx {α β : Type} {i j j' : ℕ} {d : DM β} {P : VerifierProgram α} {R : β → α → Prop}
    {Q : β → Prop} (h : RefAtWP cap occ shp rw sig i d P R Q j) (hj : j = j') :
    RefAtWP cap occ shp rw sig i d P R Q j' :=
  hj ▸ h

/-- **Composition under a promise**: the continuation's promise implies the first step's. -/
theorem RefAtWP.bind {α α' β β' : Type} {i j k : ℕ} {d : DM β} {d' : β → DM β'} {P : VerifierProgram α}
    {P' : α → VerifierProgram α'} {R : β → α → Prop} {R' : β' → α' → Prop} {Q : β → Prop} {Q' : β' → Prop}
    (hm : ∀ b, MonoD (d' b)) (h : RefAtWP cap occ shp rw sig i d P R Q j)
    (hQ : ∀ b s, Q' (runD (d' b) sig s).1 → Q b)
    (h' : ∀ b a, R b a → Q b → RefAtWP cap occ shp rw sig j (d' b) (P' a) R' Q' k) :
    RefAtWP cap occ shp rw sig i (d >>= d') (P.bind P') R' Q' k := by
  intro s hok hq
  have hsplit : runD (d >>= d') sig s = runD (d' (runD d sig s).1) sig (runD d sig s).2 := rfl
  rw [hsplit] at hok hq ⊢
  have hq1 := hQ _ _ hq
  obtain ⟨a, ha, he, hmsg, hj, hR⟩ := h s (hm _ sig _ hok) hq1
  obtain ⟨a', ha', he', hm', hk, hR'⟩ := h' _ _ hR hq1 _ hok hq
  refine ⟨a', ?_⟩
  rw [ivpW_bind]
  rcases hP : ivpW cap occ shp rw P sig s i with ⟨_ | a₀, s₂, i₂⟩
  · rw [hP] at ha; exact absurd ha (by simp)
  · rw [hP] at ha he hmsg hj
    simp only [Option.some.injEq] at ha
    subst ha
    simp only at hj
    subst hj
    obtain ⟨c1, c2, c3, c4⟩ := ivpW_congr (cap := cap) (occ := occ) (shp := shp) (rw := rw) (P' a₀) sig i₂
      he hmsg
    exact ⟨c1.trans ha', c2.trans he', c3.trans hm', c4.trans hk, hR'⟩

/-- A native `require` first, under a promise. -/
theorem RefAtWP.require_left {α β : Type} {i j : ℕ} {c : Bool} {d : Unit → DM β} {P : VerifierProgram α}
    {R : β → α → Prop} {Q : β → Prop} (hm : ∀ u, MonoD (d u))
    (h : c = true → RefAtWP cap occ shp rw sig i (d ()) P R Q j) :
    RefAtWP cap occ shp rw sig i (DM.require c >>= d) P R Q j := by
  intro s hok hq
  have e : runD (DM.require c >>= d) sig s = runD (d ()) sig { s with ok := c && s.ok } := rfl
  rw [e] at hok hq ⊢
  have hc : c = true := (Bool.and_eq_true _ _ ▸ hm () sig _ hok).1
  obtain ⟨a, h1, h2, h3, h4, h5⟩ := h hc _ hok hq
  obtain ⟨c1, c2, c3, c4⟩ := ivpW_congr (cap := cap) (occ := occ) (shp := shp) (rw := rw) P sig
    (s := s) (s' := { s with ok := c && s.ok }) i rfl rfl
  exact ⟨a, c1.trans h1, c2.trans h2, c3.trans h3, c4.trans h4, h5⟩

/-- A language `require` justified by the promise, against a native `pure`. -/
theorem RefAtWP.pure_require {β : Type} {i : ℕ} {b : β} {q : Prop} [Decidable q] {Q : β → Prop}
    (hq : Q b → q) :
    RefAtWP cap occ shp rw sig i (Pure.pure b : DM β) (VerifierProgram.require q) (fun _ _ ↦ True) Q i := by
  intro s _ hQ
  have e : VerifierProgram.require q = VerifierProgram.ret () := by
    simp only [VerifierProgram.require, hq hQ, ↓reduceIte]
  rw [e]
  exact ⟨(), rfl, rfl, rfl, rfl, trivial⟩

/-- The reads among atoms: one per `rd` (24 B) and per `rdw` (route A's width-read). -/
def atomReads (as : List Atom) : ℕ :=
  as.countP fun a ↦ match a with
    | .rd => true
    | .rdw _ => true
    | _ => false

theorem atomReads_cons (x : Atom) (as : List Atom) :
    atomReads (x :: as) = atomReads as + (match x with
      | .rd => 1
      | .rdw _ => 1
      | _ => 0) := by
  cases x <;> simp [atomReads]

/-- **`ivpW` is `ivp`** along a program that follows the atoms `as`, where the widths of its `nrd(as)` reads
are `24`; on a returned value it ends at read index `i + nrd(as)`. -/
theorem ivpW_fol {cap' : ℕ → ℕ → ℕ} {shp' : ℕ → ℕ × ℕ} {idx : Ref → ℕ} (sig : ByteArray) :
    ∀ (as : List Atom) {α : Type} (P : VerifierProgram α) (pp : List ℕ) (Qf : α → List ℕ → Prop),
      Fol cap' shp' idx P as pp Qf → ∀ (s : RS) (i : ℕ), (∀ k < atomReads as, rw (i + k) = 24) →
        (ivpW cap occ shp rw P sig s i).1 = (ivp cap occ shp P sig s).1 ∧
        (ivpW cap occ shp rw P sig s i).2.1 = (ivp cap occ shp P sig s).2 ∧
        ((ivp cap occ shp P sig s).1.isSome = true → (ivpW cap occ shp rw P sig s i).2.2 = i + atomReads as)
  | [], α, P, pp, Qf, h, s, i, _ => by
    cases P with
    | ret a => exact ⟨rfl, rfl, fun _ ↦ rfl⟩
    | fail => exact ⟨rfl, rfl, fun h' ↦ absurd h' (by simp [ivp])⟩
    | _ => simp [Fol] at h
  | a :: as, α, P, pp, Qf, h, s, i, hw => by
    cases a with
    | pclr =>
      have h' : Fol cap' shp' idx P as [] Qf := by cases P <;> exact h
      simp only [atomReads_cons, add_zero] at hw ⊢
      exact ivpW_fol sig as P [] Qf h' s i hw
    | rd =>
      cases P with
      | read k =>
        simp only [atomReads_cons] at hw ⊢
        have hw0 : rw i = 24 := by simpa using hw 0 (by (clear * - as; omega))
        have ih := ivpW_fol sig as (k (Lvm.FS.eOfBytes (sbs sig (s.ent + 40 + s.msg) 24))) pp Qf (h _)
          { s with msg := s.msg + 24 } (i + 1) fun k' hk' ↦ by
            have := hw (k' + 1) (by (clear * - k' as rw i hk'; omega))
            rwa [show i + (k' + 1) = i + 1 + k' by (clear * - i k' rw as; omega)] at this
        simp only [ivpW, ivp, hw0]
        refine ⟨ih.1, ih.2.1, fun hs ↦ ?_⟩
        rw [ih.2.2 hs]
        (clear * - i as rw; omega)
      | fail => exact ⟨rfl, rfl, fun h' ↦ absurd h' (by simp [ivp])⟩
      | _ => simp [Fol] at h
    | rdw w =>
      cases P with
      | read k =>
        simp only [atomReads_cons] at hw ⊢
        have hw0 : rw i = 24 := by simpa using hw 0 (by (clear * - as; omega))
        have ih := ivpW_fol sig as (k (Lvm.FS.eOfBytes (sbs sig (s.ent + 40 + s.msg) 24))) pp Qf (h _)
          { s with msg := s.msg + 24 } (i + 1) fun k' hk' ↦ by
            have := hw (k' + 1) (by (clear * - k' as rw i hk'; omega))
            rwa [show i + (k' + 1) = i + 1 + k' by (clear * - i k' rw as; omega)] at this
        simp only [ivpW, ivp, hw0]
        refine ⟨ih.1, ih.2.1, fun hs ↦ ?_⟩
        rw [ih.2.2 hs]
        (clear * - i as rw; omega)
      | fail => exact ⟨rfl, rfl, fun h' ↦ absurd h' (by simp [ivp])⟩
      | _ => simp [Fol] at h
    | sm =>
      simp only [atomReads_cons, add_zero] at hw ⊢
      cases P with
      | sample k =>
        simp only [ivpW, ivp]
        exact ivpW_fol sig as _ pp Qf (h _) _ i hw
      | fail => exact ⟨rfl, rfl, fun h' ↦ absurd h' (by simp [ivp])⟩
      | _ => simp [Fol] at h
    | ps hh n =>
      simp only [atomReads_cons, add_zero] at hw ⊢
      cases P with
      | sample k =>
        simp only [ivpW, ivp]
        exact ivpW_fol sig as _ _ Qf (h _) _ i hw
      | fail => exact ⟨rfl, rfl, fun h' ↦ absurd h' (by simp [ivp])⟩
      | _ => simp [Fol] at h
    | cap c r =>
      simp only [atomReads_cons, add_zero] at hw ⊢
      cases P with
      | commit ht w k =>
        simp only [ivpW, ivp]
        exact ivpW_fol sig as k pp Qf h.2.2 _ i hw
      | fail => exact ⟨rfl, rfl, fun h' ↦ absurd h' (by simp [ivp])⟩
      | _ => simp [Fol] at h
    | op r =>
      simp only [atomReads_cons, add_zero] at hw ⊢
      cases P with
      | query i' ps k =>
        simp only [ivpW, ivp]
        exact ivpW_fol sig as _ pp Qf (h.2.2 _) _ i hw
      | fail => exact ⟨rfl, rfl, fun h' ↦ absurd h' (by simp [ivp])⟩
      | _ => simp [Fol] at h

/-- **The bridge**: roll 11's refinement of a program following the atoms `as`, on 24-B reads, is a width-aware
refinement from `i` to `i + nrd(as)`. -/
theorem RefAt.toW {α β : Type} {d : DM β} {P : VerifierProgram α} {R : β → α → Prop} {as : List Atom}
    {cap' : ℕ → ℕ → ℕ} {shp' : ℕ → ℕ × ℕ} {idx : Ref → ℕ} {Qr : α → Prop}
    (h : RefAt cap occ shp sig d P R) (hf : FolP cap' shp' idx P as Qr) {i : ℕ}
    (hw : WAt rw i (List.replicate (atomReads as) 24)) :
    RefAtW cap occ shp rw sig i d P R (i + atomReads as) := by
  intro s hok
  obtain ⟨a, h1, h2, h3, h4⟩ := h s hok
  obtain ⟨e1, e2, e3⟩ := ivpW_fol (cap := cap) (occ := occ) (shp := shp) (rw := rw) sig as P [] _ (hf.fol [])
    s i fun k hk ↦ by
      have := hw k (by simpa using hk)
      rw [List.getD_eq_getElem?_getD, List.getElem?_replicate] at this
      simpa [hk] using this
  exact ⟨a, e1.trans h1, by rw [e2]; exact h2, by rw [e2]; exact h3, e3 (by rw [h1]; rfl), h4⟩

end Ref

/-! ## Arithmetic over `E2` -/

theorem kv_toE2_getD (l : List FE2) (n : ℕ) : toE2 (l.getD n 0) = (l.map toE2).getD n 0 := by
  rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, List.getElem?_map]
  cases l[n]? <;> rfl

theorem kv_toE2_pow (a : FE2) (k : ℕ) : toE2 (a ^ k) = toE2 a ^ k := by
  rw [← FE2.ringEquivE2_apply, map_pow]; rfl

theorem toE2_zeroFinalD (ω : FE2) (v : List FE2) :
    toE2 (zeroFinalD ω v) = zeroFinalT (toE2 ω) (v.map toE2) := by
  unfold zeroFinalD zeroFinalT
  rw [kf_toE2_sum]
  refine congrArg List.sum (List.map_congr_left fun k _ ↦ ?_)
  rw [kf_toE2_mul, kv_toE2_pow, FE2.toE2_add, mulY3_toE2, kv_toE2_getD]
  simp only [kv_toE2_getD]

theorem toE2_wBatchD (γ : FE2) (v : List FE2) : toE2 (wBatchD γ v) = wBatchT (toE2 γ) (v.map toE2) := by
  unfold wBatchD wBatchT
  rw [kf_toE2_sum]
  refine congrArg List.sum (List.map_congr_left fun k _ ↦ ?_)
  rw [kf_toE2_mul, kv_toE2_pow, kv_toE2_getD]

theorem toE2_wGD (γ : FE2) (vs : List FE2) : toE2 (wGD γ vs) = wGT (toE2 γ) (vs.map toE2) := by
  unfold wGD wGT
  rw [kf_toE2_sum]
  refine congrArg List.sum (List.map_congr_left fun j _ ↦ ?_)
  simp only [FE2.toE2_add, kf_toE2_mul, kv_toE2_pow, kv_toE2_getD]

theorem toE2_hEvalD (t : FE2) : ∀ hs : List FE2, toE2 (hEvalD hs t) = hEvalT (hs.map toE2) (toE2 t)
  | [] => rfl
  | c :: hs => by
    show toE2 (c + t * hEvalD hs t) = toE2 c + toE2 t * hEvalT (hs.map toE2) (toE2 t)
    rw [FE2.toE2_add, kf_toE2_mul, toE2_hEvalD t hs]

theorem toE2_yOwnD (vs κ : List FE2) : toE2 (yOwnD vs κ) = yOwnT (vs.map toE2) (κ.map toE2) := by
  rw [yOwnD, yOwnT, E2V.toE2_dotF, E2V.map_toE2_eqKernelF]

theorem map_toE2_lineD (a b : List FE2) (t : FE2) :
    (lineD a b t).map toE2 = lineT (a.map toE2) (b.map toE2) (toE2 t) :=
  map_zipWith_of (fun x y ↦ by rw [FE2.toE2_add, kf_toE2_mul, FE2.toE2_add]) a b

theorem toE2_e2OfFE' (c : FE) : toE2 (Lvm.e2OfFE c) = e2OfFE c := rfl

theorem kv_map_replicate_none (n : ℕ) :
    (List.replicate n (none : Option FE2)).map (Option.map toE2) = List.replicate n none := by simp

theorem fe2_beq {a b : FE2} (h : (a == b) = true) : a = b := beq_iff_eq.mp h

/-! ## The phases -/

/-- The zerocheck's widths: `τ`'s nonces, `ω`'s, 20 rounds, nine values. -/
def wZeroT : List ℕ := List.replicate xVars 8 ++ (wSampleG ++ (wSc 3 xVars ++ wReads 9))

/-- The wiring's widths: `γ`'s nonce, 21 rounds, twelve and four values. -/
def wWireT : List ℕ := wSampleG ++ (wSc 3 yVars ++ (wReads 12 ++ wReads 4))

/-- The relayout's widths: 19 rounds, `v_R`. -/
def wRelayT : List ℕ := wSc 3 relayRounds ++ wReads 1

/-- A23's widths: `κ`'s nonces, `h`, `t`'s nonce, the zero scalar. -/
def wAccT : List ℕ := List.replicate selBitsT 8 ++ (wReads (phiVarsT + 1) ++ (wSampleG ++ wReads 1))

/-- The mini-bus's reads (24 B each): its atoms' `rd` count at `P20` (`folP_miniBusProg`). -/
def nMiniRd : ℕ := atomReads (atomsOf P20 (miniBusI P20 ++ miniTabI P20))

/-- **The typed phase's widths at S2GT.** -/
def wTypedT : List ℕ := wZeroT ++ (wWireT ++ (wRelayT ++ (wAccT ++ List.replicate nMiniRd 24)))

section Phases

variable {cap : ℕ → ℕ → ℕ} {occ : ℕ → ℕ → ℕ} {shp : ℕ → ℕ × ℕ} {rw : ℕ → ℕ} {sig : ByteArray}

/-- **The zerocheck at `E2`.** -/
theorem refW_dZeroT {i : ℕ} (hw : WAt rw i wZeroT) :
    RefAtW cap occ shp rw sig i dZeroT zeroProgT
      (fun z z' ↦ z' = (z.1.map toE2, z.2.map toE2) ∧ z.1.length = xVars ∧ z.2.length = 9)
      (i + wZeroT.length) := by
  simp only [wZeroT, WAt.append, List.length_replicate, wSampleG, WAt.cons, length_wSc] at hw
  obtain ⟨h1, ⟨h2, -⟩, h3, h4⟩ := hw
  unfold dZeroT zeroProgT
  refine RefAtW.bind (fun _ ↦ (monoD_samplesG _ _).bind fun _ ↦ (monoD_sampleG _).bind fun _ ↦
    (monoD_sumcheckD _ _ _ _).bind fun _ ↦ (monoD_readE2s _).bind fun _ ↦ (MonoD.require _).bind fun _ ↦
      MonoD.pure _) refW_sepE2 fun _ _ _ ↦ ?_
  refine RefAtW.bind (fun _ ↦ (monoD_sampleG _).bind fun _ ↦ (monoD_sumcheckD _ _ _ _).bind fun _ ↦
    (monoD_readE2s _).bind fun _ ↦ (MonoD.require _).bind fun _ ↦ MonoD.pure _)
    (RefAtW.retD (refW_samplesG gTau xVars h1) (retD_samplesG gTau xVars)) ?_
  rintro tau _ ⟨rfl, htau⟩
  refine RefAtW.bind (fun _ ↦ (monoD_sumcheckD _ _ _ _).bind fun _ ↦ (monoD_readE2s _).bind fun _ ↦
    (MonoD.require _).bind fun _ ↦ MonoD.pure _) (refW_sampleG gOmega h2) ?_
  rintro om _ rfl
  have hs := refW_sumcheckD (cap := cap) (occ := occ) (shp := shp) (rw := rw) (sig := sig) gZero 3 (by norm_num)
    (tau.map some) 0 (i := i + xVars + 1) (by rw [List.length_map, htau]; exact h3)
  rw [List.map_map, show (Option.map toE2 ∘ some) = (some ∘ toE2) from rfl, ← List.map_map, FE2.toE2_zero] at hs
  refine RefAtW.bind (fun _ ↦ (monoD_readE2s _).bind fun _ ↦ (MonoD.require _).bind fun _ ↦ MonoD.pure _) hs ?_
  rintro rf rf' ⟨hr1, hr2, hr3⟩
  refine RefAtW.bind (fun _ ↦ (MonoD.require _).bind fun _ ↦ MonoD.pure _)
    (RefAtW.retD (refW_readE2s 9 (WAt.idx_eq h4 (by simp only [List.length_map, htau, length_wSc, List.length_cons, List.length_nil]))) (retD_readE2s 9)) ?_
  rintro v _ ⟨rfl, hv⟩
  refine RefAtW.bind (fun _ ↦ MonoD.pure _) (RefAtW.require fun hc ↦ ?_) ?_
  · rw [hr2, fe2_beq hc, toE2_zeroFinalD]
  · intro _ _ _
    refine (RefAtW.pure ⟨by rw [hr1], by rw [hr3, List.length_map, htau], hv⟩).idx ?_
    simp only [wZeroT, List.length_append, List.length_replicate, wSampleG, List.length_cons, List.length_nil,
      length_wSc, length_wReads, List.length_map, htau]
    (clear * - i rw tau rf v; omega)

/-- **The wiring at `E2`** (`virtD_rel`). -/
theorem refW_dWiringT (N : TNatT) (Q : Lvm.Loop.Program) (lay : Lay) (hok : N.toN.okB P20.nuMain P20.nuRec = true)
    (hlay : N.toN.layOk lay = true) (pub : Pub) (v : List FE2) {i : ℕ} (hw : WAt rw i wWireT) :
    RefAtW cap occ shp rw sig i (dWiringT N pub v) (wireProgT (N.inst Q lay) pub (v.map toE2))
      (fun w w' ↦ w' = (w.1.map toE2, w.2.1.map toE2, w.2.2.map toE2) ∧ w.1.length = yVars ∧
        w.2.1.length = 12 ∧ w.2.2.length = 4) (i + wWireT.length) := by
  simp only [wWireT, WAt.append, wSampleG, WAt.cons, List.length_cons, List.length_nil, length_wSc,
    length_wReads] at hw
  obtain ⟨⟨h1, -⟩, h2, h3, h4⟩ := hw
  unfold dWiringT wireProgT
  refine RefAtW.bind (fun _ ↦ (monoD_sumcheckD _ _ _ _).bind fun _ ↦ (monoD_readE2s _).bind fun _ ↦
    (monoD_readE2s _).bind fun _ ↦ (MonoD.require _).bind fun _ ↦ MonoD.pure _) (refW_sampleG gGamma h1) ?_
  rintro g _ rfl
  have hs := refW_sumcheckD (cap := cap) (occ := occ) (shp := shp) (rw := rw) (sig := sig) gWire 3 (by norm_num)
    (List.replicate yVars none) (wBatchD g v) (i := i + 1) (by rw [List.length_replicate]; exact h2)
  rw [kv_map_replicate_none, toE2_wBatchD] at hs
  refine RefAtW.bind (fun _ ↦ (monoD_readE2s _).bind fun _ ↦ (monoD_readE2s _).bind fun _ ↦
    (MonoD.require _).bind fun _ ↦ MonoD.pure _) hs ?_
  rintro rf rf' ⟨hr1, hr2, hr3⟩
  rw [List.length_replicate] at hr3
  refine RefAtW.bind (fun _ ↦ (monoD_readE2s _).bind fun _ ↦ (MonoD.require _).bind fun _ ↦ MonoD.pure _)
    (RefAtW.retD (refW_readE2s 12 (WAt.idx_eq h3 (by simp only [List.length_replicate, length_wSc]))) (retD_readE2s 12)) ?_
  rintro vs _ ⟨rfl, hvs⟩
  refine RefAtW.bind (fun _ ↦ (MonoD.require _).bind fun _ ↦ MonoD.pure _)
    (RefAtW.retD (refW_readE2s 4 (WAt.idx_eq h4 (by simp only [List.length_replicate, length_wSc]))) (retD_readE2s 4)) ?_
  rintro rv _ ⟨rfl, hrv⟩
  refine RefAtW.bind (fun _ ↦ MonoD.pure _) (RefAtW.require fun hc ↦ ?_) ?_
  · rw [hr2, hr1, fe2_beq hc, kf_toE2_mul, toE2_wGD, FE2.toE2_add, E2V.toE2_sumF,
      virtD_rel N Q lay P20.nuMain P20.nuRec hok hlay pub rf.1 hr3]
  · intro _ _ _
    refine (RefAtW.pure ⟨by rw [hr1], hr3, hvs, hrv⟩).idx ?_
    simp only [wWireT, List.length_append, wSampleG, List.length_cons, List.length_nil, length_wSc,
      length_wReads, List.length_replicate]
    (clear * - i rw rf vs rv; omega)

/-- **The relayout at `E2`** (`relayKernD_rel`). -/
theorem refW_dRelayT2 (N : TNatT) (Q : Lvm.Loop.Program) (lay : Lay)
    (hok : N.toN.okB P20.nuMain P20.nuRec = true) (hlay : N.toN.layOk lay = true) (ry : List FE2)
    (hry : ry.length = yVars) (vS : FE2) {i : ℕ} (hw : WAt rw i wRelayT) :
    RefAtW cap occ shp rw sig i (dRelayT2 N ry vS) (relayProgT (N.inst Q lay) (ry.map toE2) (toE2 vS))
      (fun r r' ↦ r' = (r.1.map toE2, toE2 r.2) ∧ r.1.length = relayRounds) (i + wRelayT.length) := by
  simp only [wRelayT, WAt.append, length_wSc] at hw
  obtain ⟨h1, h2⟩ := hw
  unfold dRelayT2 relayProgT
  have hs := refW_sumcheckD (cap := cap) (occ := occ) (shp := shp) (rw := rw) (sig := sig) gWire 3 (by norm_num)
    (List.replicate relayRounds none) vS (i := i) (by rw [List.length_replicate]; exact h1)
  rw [kv_map_replicate_none] at hs
  refine RefAtW.bind (fun _ ↦ monoD_readE2.bind fun _ ↦ (MonoD.require _).bind fun _ ↦ MonoD.pure _) hs ?_
  rintro rf rf' ⟨hr1, hr2, hr3⟩
  rw [List.length_replicate] at hr3
  have h2' : rw (i + (wSc 3 (List.replicate relayRounds none : List (Option FE2)).length).length) = 16 := by
    have h2'' := WAt.idx_eq h2 (j := i + (wSc 3 (List.replicate relayRounds none : List (Option FE2)).length).length)
      (by simp only [List.length_replicate, length_wSc])
    simpa [wReads] using h2'' 0 (by simp [wReads])
  refine RefAtW.bind (fun _ ↦ (MonoD.require _).bind fun _ ↦ MonoD.pure _) (refW_readE2 h2') ?_
  rintro vR _ rfl
  refine RefAtW.bind (fun _ ↦ MonoD.pure _) (RefAtW.require fun hc ↦ ?_) ?_
  · rw [hr2, hr1, fe2_beq hc, kf_toE2_mul, relayKernD_rel N Q lay P20.nuMain P20.nuRec hok hlay ry rf.1 hry hr3]
  · intro _ _ _
    refine (RefAtW.pure ⟨by rw [hr1], hr3⟩).idx ?_
    simp only [wRelayT, List.length_append, length_wSc, length_wReads, List.length_replicate]
    (clear * - i rw ry rf; omega)

/-- **A23 at `E2`** under the promise that the folded claim holds natively (lanes 0–1 of the accumulator). -/
theorem refW_dAccT (N : TNatT) (Q : Lvm.Loop.Program) (lay : Lay)
    (hphi : ∀ pt : List FE2, pt.length = phiVarsT → N.phiT pt = PhiQFT Q lay pt) (pub : Pub)
    (hacc : pub.accIn.pt.length = phiVarsT) (rxy vs : List FE2) (hrxy : rxy.length = xVars + yVars) {i : ℕ}
    (hw : WAt rw i wAccT) :
    RefAtWP cap occ shp rw sig i (dAccT pub rxy vs)
      (accProgT Q lay true (accYT pub) (accPtT pub) (rxy.map toE2) (vs.map toE2))
      (fun _ _ ↦ True) (fun a ↦ N.phiT (a.pt.map Lvm.e2OfFE) = Lvm.e2OfFE a.y) (i + wAccT.length) := by
  simp only [wAccT, WAt.append, wSampleG, WAt.cons, List.length_replicate, List.length_cons, List.length_nil,
    length_wReads] at hw
  obtain ⟨h1, h2, ⟨h3, -⟩, h4⟩ := hw
  unfold dAccT accProgT
  refine RefAtWP.bind (Q := fun _ ↦ True) (fun _ ↦ (monoD_readE2s _).bind fun _ ↦ (monoD_sampleG _).bind fun _ ↦
      monoD_readE2.bind fun _ ↦ (MonoD.require _).bind fun _ ↦ (MonoD.require _).bind fun _ ↦
        (MonoD.require _).bind fun _ ↦ MonoD.pure _)
    (RefAtW.toP (RefAtW.retD (refW_samplesG gKappa selBitsT h1) (retD_samplesG gKappa selBitsT)) _) (fun _ _ _ ↦ trivial) ?_
  rintro κ _ ⟨rfl, hκ⟩ -
  refine RefAtWP.bind (Q := fun _ ↦ True) (fun _ ↦ (monoD_sampleG _).bind fun _ ↦ monoD_readE2.bind fun _ ↦
      (MonoD.require _).bind fun _ ↦ (MonoD.require _).bind fun _ ↦ (MonoD.require _).bind fun _ ↦
        MonoD.pure _)
    (RefAtW.toP (refW_readE2s (phiVarsT + 1) h2) _) (fun _ _ _ ↦ trivial) ?_
  rintro h _ rfl -
  refine RefAtWP.bind (Q := fun _ ↦ True) (fun _ ↦ monoD_readE2.bind fun _ ↦
      (MonoD.require _).bind fun _ ↦ (MonoD.require _).bind fun _ ↦ (MonoD.require _).bind fun _ ↦
        MonoD.pure _)
    (RefAtW.toP (refW_sampleG gT h3) _) (fun _ _ _ ↦ trivial) ?_
  rintro t _ rfl -
  have h4' : rw (i + selBitsT + (phiVarsT + 1) + 1) = 16 := by simpa [wReads] using h4 0 (by simp [wReads])
  refine RefAtWP.bind (Q := fun _ ↦ True) (fun _ ↦ (MonoD.require _).bind fun _ ↦
      (MonoD.require _).bind fun _ ↦ (MonoD.require _).bind fun _ ↦ MonoD.pure _)
    (RefAtW.toP (refW_readE2 h4') _) (fun _ _ _ ↦ trivial) ?_
  rintro z _ rfl -
  refine RefAtWP.require_left (fun _ ↦ (MonoD.require _).bind fun _ ↦ (MonoD.require _).bind fun _ ↦
    MonoD.pure _) fun h0 ↦ ?_
  refine RefAtWP.require_left (fun _ ↦ (MonoD.require _).bind fun _ ↦ MonoD.pure _) fun h1' ↦ ?_
  refine RefAtWP.require_left (fun _ ↦ MonoD.pure _) fun hz ↦ ?_
  refine RefAtWP.idx (RefAtWP.pure_require fun hA ↦ ?_) ?_
  · refine ⟨rfl, ?_, ?_, ?_, ?_⟩
    · rw [show (0 : E2) = toE2 0 from rfl, ← toE2_hEvalD, fe2_beq h0]; rfl
    · rw [show (1 : E2) = toE2 1 from FE2.toE2_one.symm, ← toE2_hEvalD, fe2_beq h1', toE2_yOwnD]
    · rw [fe2_beq hz]; rfl
    · have hl : (lineD (pub.accIn.pt.map Lvm.e2OfFE) (κ ++ rxy) t).length = phiVarsT := by
        simp only [lineD, List.length_zipWith, List.length_map, List.length_append, hacc, hκ, hrxy]
        rfl
      have hA' : N.phiT (lineD (pub.accIn.pt.map Lvm.e2OfFE) (κ ++ rxy) t) = hEvalD h t := by
        simpa [List.map_map, Function.comp_def, fe2ToFE, Lvm.e2OfFE] using hA
      rw [hphi _ hl] at hA'
      have hpt : accPtT pub = (pub.accIn.pt.map Lvm.e2OfFE).map toE2 := by
        rw [accPtT, List.map_map]; rfl
      rw [hpt, ← List.map_append, ← map_toE2_lineD, PhiQT, List.map_map,
        show (Lvm.Typed.ofE2 ∘ toE2) = id from funext fun _ ↦ rfl, List.map_id, hA', toE2_hEvalD]
  · simp only [wAccT, List.length_append, List.length_replicate, length_wReads, wSampleG, List.length_cons,
      List.length_nil]
    (clear * - i rw pub rxy κ; omega)

end Phases

/-! ## The typed phases -/

/-- **What the S2GT typed refinement needs of the native instance**: roll 11's `TRefHyp` on the regions and
tables, with `N.phiT` the specification's `Φ_Q` at `E2` on `phiVarsT = 45` coordinates. -/
structure TRefHypT (N : TNatT) (Q : Lvm.Loop.Program) (lay : Lay) : Prop where
  /-- The shape check the closed forms rely on. -/
  ok : N.toN.okB P20.nuMain P20.nuRec = true
  /-- The native regions are the layout's. -/
  hlay : N.toN.layOk lay = true
  /-- The record is the mini-bus's. -/
  mini : fitsMiniB P20 N.mbT = true
  /-- Every mini-bus table takes part in the table sumcheck. -/
  sc : AllSc N.mbT
  /-- V_S's `Φ_Q` at `E2` is the specification's at `45` coordinates. -/
  phiT : ∀ pt : List FE2, pt.length = phiVarsT → N.phiT pt = PhiQFT Q lay pt

/-- Roll 11's hypothesis on the record with roll 11's `Φ_Q` (the mini-bus does not read it). -/
theorem TRefHypT.toT {N : TNatT} {Q : Lvm.Loop.Program} {lay : Lay} (H : TRefHypT N Q lay) :
    TRefHyp ⟨N.regs, PhiQF Q lay, N.mbT⟩ Q lay :=
  ⟨H.ok, H.hlay, H.mini, H.sc, fun _ _ ↦ rfl⟩

/-- **The typed phases' native results against the specification's claims** on the layout of the record `p`: the
native claims are `typedClaimsND N p` of values (`r_y` of 21 coordinates, four region values, `r` of 19) whose
images `typedClaimsT` takes, with the mini-bus's claims those of its evaluations. -/
def TRelTTO (p : Params) (N : TNatT) (Q : Lvm.Loop.Program) (lay : Lay)
    (r : Acc × List (Com × BlockClaim × FE) × List (List FE × List FE)) (a : Lvm.ASM.OpenClaims) : Prop :=
  ∃ ry rv rr : List FE2, ∃ vR : FE2, r.2.1 = typedClaimsND N p ry rv rr vR ∧ ry.length = yVars ∧
    rv.length = 4 ∧ rr.length = relayRounds ∧
    a = typedClaimsT (N.inst Q lay) (ry.map toE2) (rv.map toE2) (rr.map toE2) (toE2 vR)
      (claimsOfEvs N.mbT r.2.2) ∧
    EvLen N.mbT r.2.2 ∧ List.Forall₂ CRel (tableClaimsR N.mbT r.2.2) (tableClaimsE N.mbT (claimsOfEvs N.mbT r.2.2))

/-- `TRelTTO` at S2GT's layout (`P20`). -/
def TRelTT (N : TNatT) (Q : Lvm.Loop.Program) (lay : Lay)
    (r : Acc × List (Com × BlockClaim × FE) × List (List FE × List FE)) (a : Lvm.ASM.OpenClaims) : Prop :=
  TRelTTO P20 N Q lay r a

/-- **The typed phases refine `typedProgT`** on the width-aware stream (read index `i` to `i + |wTypedT|`), under
the promise that the folded claim holds natively, their claims formed on the layout of the record `p`. -/
theorem ref_dTypedTO {cap : ℕ → ℕ → ℕ} {occ : ℕ → ℕ → ℕ} {shp : ℕ → ℕ × ℕ} {rw : ℕ → ℕ} {sig : ByteArray}
    (p : Params) (N : TNatT) (Q : Lvm.Loop.Program) (lay : Lay) (H : TRefHypT N Q lay) (pub : Pub)
    (hacc : pub.accIn.pt.length = phiVarsT) {i : ℕ} (hw : WAt rw i wTypedT) :
    RefAtWP cap occ shp rw sig i (dTypedTG P20 N (N.toN.m3 P20) pub (typedClaimsND N p))
      (typedProgT (N.inst Q lay) pub) (TRelTTO p N Q lay) (fun r ↦ N.phiT (r.1.pt.map Lvm.e2OfFE) = Lvm.e2OfFE r.1.y)
      (i + wTypedT.length) := by
  obtain ⟨hl, hr, he, -, -⟩ := H.toT.fits
  simp only [wTypedT, WAt.append] at hw
  obtain ⟨hwz, hww, hwr, hwa, hwm⟩ := hw
  unfold dTypedTG typedProgT
  refine RefAtWP.bind (Q := fun _ ↦ True) (fun _ ↦ (E2T.monoD_dWiringT _ _ _).bind fun _ ↦
    (E2T.monoD_dRelayT2 _ _ _).bind fun _ ↦ (E2T.monoD_dAccT _ _ _).bind fun _ ↦
      (Lvm.VEq.monoD_dMiniT _ _ _ _).bind fun _ ↦ MonoD.pure _) (RefAtW.toP (refW_dZeroT hwz) _)
    (fun _ _ _ ↦ trivial) ?_
  rintro z _ ⟨rfl, hz, -⟩ -
  refine RefAtWP.bind (Q := fun _ ↦ True) (fun _ ↦ (E2T.monoD_dRelayT2 _ _ _).bind fun _ ↦
    (E2T.monoD_dAccT _ _ _).bind fun _ ↦ (Lvm.VEq.monoD_dMiniT _ _ _ _).bind fun _ ↦ MonoD.pure _)
    (RefAtW.toP (refW_dWiringT N Q lay H.ok H.hlay pub z.2 hww) _) (fun _ _ _ ↦ trivial) ?_
  rintro w _ ⟨rfl, hry, -, hrv⟩ -
  have hR := refW_dRelayT2 (cap := cap) (occ := occ) (shp := shp) (rw := rw) (sig := sig) N Q lay H.ok H.hlay w.1
    hry (w.2.2.getD 1 0) hwr
  rw [kv_toE2_getD] at hR
  refine RefAtWP.bind (Q := fun _ ↦ True) (fun _ ↦ (E2T.monoD_dAccT _ _ _).bind fun _ ↦
    (Lvm.VEq.monoD_dMiniT _ _ _ _).bind fun _ ↦ MonoD.pure _) (RefAtW.toP hR _) (fun _ _ _ ↦ trivial) ?_
  rintro r _ ⟨rfl, hrr⟩ -
  have hA := refW_dAccT (cap := cap) (occ := occ) (shp := shp) (rw := rw) (sig := sig) N Q lay H.phiT pub hacc
    (z.1 ++ w.1) w.2.1 (by rw [List.length_append, hz, hry]) hwa
  rw [List.map_append] at hA
  dsimp only
  refine RefAtWP.bind (Q := fun (a : Acc) ↦ N.phiT (a.pt.map Lvm.e2OfFE) = Lvm.e2OfFE a.y)
    (fun _ ↦ (Lvm.VEq.monoD_dMiniT _ _ _ _).bind fun _ ↦ MonoD.pure _) hA
    (fun _ _ h ↦ by rw [runD_bind_pure_fst] at h; exact h) ?_
  intro acc _ _ _
  have hM := ref_dMiniT (cap := cap) (occ := occ) (shp := shp) (sig := sig) P20 N.mbT pub hl busDepth_P20 hr
    H.toT.sc_eq
  have hF := folP_miniBusProg (cap := cap) (shp := shp) (idx := fun _ ↦ 0) P20 (N.inst Q lay) hl
    busDepth_P20 hr he
  have hW := RefAt.toW (rw := rw) hM hF hwm
  refine RefAtWP.bind (Q := fun _ ↦ True) (fun _ ↦ MonoD.pure _) (RefAtW.toP hW _) (fun _ _ _ ↦ trivial) ?_
  rintro evs cl ⟨rfl, hlen, hcl⟩ -
  refine RefAtWP.idx (RefAtW.toP (RefAtW.pure ⟨w.1, w.2.2, r.1, r.2, rfl, hry, hrv, hrr, rfl, hlen, hcl⟩) _) ?_
  simp only [wTypedT, List.length_append, List.length_replicate, nMiniRd]
  (clear * - i N Q lay pub z w r; omega)

/-- **The typed phases at S2GT refine `typedProgT`** (`ref_dTypedTO` at `P20`). -/
theorem ref_dTypedT {cap : ℕ → ℕ → ℕ} {occ : ℕ → ℕ → ℕ} {shp : ℕ → ℕ × ℕ} {rw : ℕ → ℕ} {sig : ByteArray}
    (N : TNatT) (Q : Lvm.Loop.Program) (lay : Lay) (H : TRefHypT N Q lay) (pub : Pub)
    (hacc : pub.accIn.pt.length = phiVarsT) {i : ℕ} (hw : WAt rw i wTypedT) :
    RefAtWP cap occ shp rw sig i (dTypedT P20 N (N.toN.m3 P20) pub) (typedProgT (N.inst Q lay) pub)
      (TRelTT N Q lay) (fun r ↦ N.phiT (r.1.pt.map Lvm.e2OfFE) = Lvm.e2OfFE r.1.y) (i + wTypedT.length) :=
  ref_dTypedTO P20 N Q lay H pub hacc hw

end Lvm.E2T
