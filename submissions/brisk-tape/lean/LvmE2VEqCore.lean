-- New for lvm2 S1 (E2-F, E2F-V): the width-aware hub of V_S ⇒ spec at S2GF: a program of the verifier language
-- read off the stream with reads of per-index widths (`ivpW rw`), the refinement of a native step by such a
-- program (`RefAtW`) and its rules (the twins of `LvmVEqCore`'s `ivp`/`RefAt`), and the primitives of the
-- `E2` front (`readE2`, the nonce, `sampleG`, `sepE2`) against `e2Read`, `e2Sample`, `e2Sep`.
import LvmVEqPrim
import LvmE2VTwins

/-!
# Width-aware reading and refinement

At S2GF the `i`-th read of a run takes `rw i` bytes (`8`: a nonce, `16`: an `E2` scalar, `24`: an `E3`
scalar) and decodes by zero padding to 24 bytes (`Lvm.FS.eOfBytes` reads missing bytes as `0`).

* `ivpW cap occ shp rw P sig s i` (`LvmVEqCore`): `ivp` with a read counter `i`; a read takes `rw i` bytes.
* **`RefAtW … sig i d P R j`**: from every cursor at which the native step `d` ends with every check held,
  `ivpW P` started at read index `i` returns a value related to `d`'s at the same `ent`, `msg`, and ends at
  read index `j`. Rules: `mono`, `bind`, `pure`, `dm_left`, `read_left`, `require`, `idx`.
* **Widths**: `WAt rw i ws` (`LvmVEqCore`).
* **Primitives**: `refW_readE2` (16), `refW_readE2s`, `refW_nonce` (8), `refW_sampleG` (8: the nonce is one
  read whose value is unused), `refW_samplesG`, `refW_sepE2`; values through `FE2.toE2`.
-/

set_option autoImplicit false

namespace Lvm.VEq

open Lvm DM LeanVM.Parameters LeanVM.Protocol.Compile
open Lvm.FE2 (toE2)


/-! ## Refinement with read indices -/

section Ref

variable (cap : ℕ → ℕ → ℕ) (occ : ℕ → ℕ → ℕ) (shp : ℕ → ℕ × ℕ) (rw : ℕ → ℕ)

/-- **The native step `d` refines `P` from read index `i` to read index `j`**: wherever `d` ends with every
check held, `P` read off the stream from read index `i` returns a value related to `d`'s at the same cursor
and ends at read index `j`. -/
def RefAtW {α β : Type} (sig : ByteArray) (i : ℕ) (d : DM β) (P : VerifierProgram α) (R : β → α → Prop)
    (j : ℕ) : Prop :=
  ∀ s, (runD d sig s).2.ok = true →
    ∃ a, (ivpW cap occ shp rw P sig s i).1 = some a ∧
      (ivpW cap occ shp rw P sig s i).2.1.ent = (runD d sig s).2.ent ∧
      (ivpW cap occ shp rw P sig s i).2.1.msg = (runD d sig s).2.msg ∧
      (ivpW cap occ shp rw P sig s i).2.2 = j ∧ R (runD d sig s).1 a

variable {cap occ shp rw} {sig : ByteArray}

theorem RefAtW.mono {α β : Type} {i j : ℕ} {d : DM β} {P : VerifierProgram α} {R R' : β → α → Prop}
    (h : RefAtW cap occ shp rw sig i d P R j) (hR : ∀ b a, R b a → R' b a) :
    RefAtW cap occ shp rw sig i d P R' j :=
  fun s hok ↦ by
    obtain ⟨a, h1, h2, h3, h4, h5⟩ := h s hok
    exact ⟨a, h1, h2, h3, h4, hR _ _ h5⟩

/-- The end index along an equality. -/
theorem RefAtW.idx {α β : Type} {i j j' : ℕ} {d : DM β} {P : VerifierProgram α} {R : β → α → Prop}
    (h : RefAtW cap occ shp rw sig i d P R j) (hj : j = j') : RefAtW cap occ shp rw sig i d P R j' :=
  hj ▸ h

/-- **Composition.** -/
theorem RefAtW.bind {α α' β β' : Type} {i j k : ℕ} {d : DM β} {d' : β → DM β'} {P : VerifierProgram α}
    {P' : α → VerifierProgram α'} {R : β → α → Prop} {R' : β' → α' → Prop}
    (hm : ∀ b, MonoD (d' b)) (h : RefAtW cap occ shp rw sig i d P R j)
    (h' : ∀ b a, R b a → RefAtW cap occ shp rw sig j (d' b) (P' a) R' k) :
    RefAtW cap occ shp rw sig i (d >>= d') (P.bind P') R' k := by
  intro s hok
  have hsplit : runD (d >>= d') sig s = runD (d' (runD d sig s).1) sig (runD d sig s).2 := rfl
  rw [hsplit] at hok ⊢
  obtain ⟨a, ha, he, hmsg, hj, hR⟩ := h s (hm _ sig _ hok)
  obtain ⟨a', ha', he', hm', hk, hR'⟩ := h' _ _ hR _ hok
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

/-- A returned value. -/
theorem RefAtW.pure {α β : Type} {i : ℕ} {b : β} {a : α} {R : β → α → Prop} (h : R b a) :
    RefAtW cap occ shp rw sig i (Pure.pure b : DM β) (VerifierProgram.ret a) R i :=
  fun _ _ ↦ ⟨a, rfl, rfl, rfl, rfl, h⟩

/-- A native step that reads without moving the cursor, then the rest. -/
theorem RefAtW.dm_left {α β β' : Type} {i j : ℕ} {d₀ : DM β'} {b₀ : β'}
    (h₀ : ∀ s, runD d₀ sig s = (b₀, s)) {d : β' → DM β} {P : VerifierProgram α} {R : β → α → Prop}
    (h : RefAtW cap occ shp rw sig i (d b₀) P R j) : RefAtW cap occ shp rw sig i (d₀ >>= d) P R j := by
  intro s hok
  have hsplit : runD (d₀ >>= d) sig s = runD (d b₀) sig s := by
    show runD (d (runD d₀ sig s).1) sig (runD d₀ sig s).2 = _
    rw [h₀]
  rw [hsplit] at hok ⊢
  exact h s hok

/-- **V_S's strict `require` against the language's `require`.** -/
theorem RefAtW.require {i : ℕ} {c : Bool} {q : Prop} [Decidable q] (h : c = true → q) :
    RefAtW cap occ shp rw sig i (DM.require c) (VerifierProgram.require q) (fun _ _ ↦ True) i := by
  intro s hok
  have hc : c = true := by
    simp only [runD, DM.require, modify, modifyGet, MonadStateOf.modifyGet] at hok
    exact (Bool.and_eq_true _ _ ▸ hok).1
  have hq : VerifierProgram.require q = VerifierProgram.ret () := by
    simp only [VerifierProgram.require, h hc, ↓reduceIte]
  rw [hq]
  exact ⟨(), rfl, rfl, rfl, rfl, trivial⟩

/-- A native step followed by a pure map refines the program alone. -/
theorem RefAtW.bind_pure_left {α β β' : Type} {i j : ℕ} {d : DM β} {g : β → β'} {P : VerifierProgram α}
    {R : β → α → Prop} {R' : β' → α → Prop} (h : RefAtW cap occ shp rw sig i d P R j)
    (hR : ∀ b a, R b a → R' (g b) a) :
    RefAtW cap occ shp rw sig i (d >>= fun b ↦ Pure.pure (g b)) P R' j := by
  intro s hok
  obtain ⟨a, h1, h2, h3, h4, h5⟩ := h s hok
  exact ⟨a, h1, h2, h3, h4, hR _ _ h5⟩

/-- Transport along an equality of programs. -/
theorem RefAtW.congr_prog {α β : Type} {i j : ℕ} {d : DM β} {P P' : VerifierProgram α} {R : β → α → Prop}
    (hP : P = P') (h : RefAtW cap occ shp rw sig i d P R j) : RefAtW cap occ shp rw sig i d P' R j :=
  hP ▸ h

/-- Transport along an equality of native steps. -/
theorem RefAtW.congr_dm {α β : Type} {i j : ℕ} {d d' : DM β} {P : VerifierProgram α} {R : β → α → Prop}
    (hd : d = d') (h : RefAtW cap occ shp rw sig i d P R j) : RefAtW cap occ shp rw sig i d' P R j :=
  hd ▸ h

end Ref


/-! ## The `E2` primitives -/

/-- `FE2` scalar bytes: `re` then `im`. -/
theorem toE2_fe2At (sig : ByteArray) (o : ℕ) :
    toE2 (fe2At sig o) = LeanVM.Parameters.e2OfE (Lvm.FS.eOfBytes (sbs sig o 16)) := by
  have hre : FK.toBF64 (kAt sig o) = Lvm.FS.kOfBytes (sbs sig o 16) :=
    toBF64_kAt_of _ _ _ fun i hi ↦ getD_sb sig o 16 i (by omega)
  have him : FK.toBF64 (kAt sig (o + 8)) = Lvm.FS.kOfBytes ((sbs sig o 16).drop 8) :=
    toBF64_kAt_of _ _ _ fun i hi ↦ by
      rw [getD_drop_bytes, show sbs sig o 16 = sb sig o 16 from rfl, getD_sb sig o 16 _ (by omega),
        Nat.add_assoc]
  show (⟨FK.toBF64 (kAt sig o), FK.toBF64 (kAt sig (o + 8))⟩ : E2) = _
  rw [hre, him]
  rfl

/-- An answer's `E2` challenge: lanes 0–1. -/
theorem toE2_e2OfFE (c : FE) : toE2 (e2OfFE c) = LeanVM.Parameters.e2OfE (FE.toExt3 c) := rfl

theorem monoD_readE2 : MonoD readE2 := fun _ _ h ↦ h
theorem monoD_nonceE2 : MonoD nonceE2 := fun _ _ h ↦ h

theorem monoD_readE2s : ∀ n, MonoD (readE2s n)
  | 0 => MonoD.pure _
  | n + 1 => monoD_readE2.bind fun _ ↦ (monoD_readE2s n).bind fun _ ↦ MonoD.pure _

theorem monoD_sampleG (g : ℕ) : MonoD (sampleG g) :=
  monoD_nonceE2.bind fun _ ↦ monoD_sampleE.bind fun _ ↦ (MonoD.require _).bind fun _ ↦ MonoD.pure _

theorem monoD_samplesG (g : ℕ) : ∀ n, MonoD (samplesG g n)
  | 0 => MonoD.pure _
  | n + 1 => (monoD_sampleG g).bind fun _ ↦ (monoD_samplesG g n).bind fun _ ↦ MonoD.pure _

theorem monoD_sepE2 : MonoD sepE2 := monoD_sampleE.bind fun _ ↦ MonoD.pure _

section Prim

variable {cap : ℕ → ℕ → ℕ} {occ : ℕ → ℕ → ℕ} {shp : ℕ → ℕ × ℕ} {rw : ℕ → ℕ} {sig : ByteArray}

/-- **A challenge** (no read). -/
theorem refW_sampleE {i : ℕ} :
    RefAtW cap occ shp rw sig i DM.sampleE VerifierProgram.sampleChallenge
      (fun x y ↦ y = FE.toExt3 x) i :=
  fun s _ ↦ ⟨_, rfl, rfl, rfl, rfl, (toExt3_feAt_chal sig _).symm⟩

/-- **`n` challenges** (no read). -/
theorem refW_samples : ∀ (n : ℕ) {i : ℕ}, RefAtW cap occ shp rw sig i (DM.samples n)
    (VerifierProgram.sampleChallenges n) (fun xs ys ↦ ys = xs.map FE.toExt3) i
  | 0, _ => RefAtW.pure rfl
  | n + 1, _ => by
    refine RefAtW.bind (fun _ ↦ (monoD_samples n).bind fun _ ↦ MonoD.pure _) refW_sampleE ?_
    intro x y hxy
    refine RefAtW.bind (fun _ ↦ MonoD.pure _) (refW_samples n) ?_
    intro xs ys hs
    exact RefAtW.pure (by simp [hxy, hs])

/-- **An `E3` scalar** (24 bytes). -/
theorem refW_readE {i : ℕ} (hw : rw i = 24) :
    RefAtW cap occ shp rw sig i DM.readE VerifierProgram.readScalar (fun x y ↦ y = FE.toExt3 x) (i + 1) := by
  intro s _
  refine ⟨_, rfl, rfl, ?_, rfl, ?_⟩
  · show s.msg + rw i = s.msg + 24
    rw [hw]
  · show _ = FE.toExt3 (feAt sig (s.ent + 40 + s.msg))
    rw [toExt3_feAt, ← hw]
    rfl

/-- **An `E2` scalar** (16 bytes). -/
theorem refW_readE2 {i : ℕ} (hw : rw i = 16) :
    RefAtW cap occ shp rw sig i readE2 E2V.e2Read (fun x y ↦ y = toE2 x) (i + 1) := by
  intro s _
  refine ⟨_, rfl, rfl, ?_, rfl, ?_⟩
  · show s.msg + rw i = s.msg + 16
    rw [hw]
  · show _ = toE2 (fe2At sig (s.ent + 40 + s.msg))
    rw [toE2_fe2At, ← hw]

/-- The widths of `n` `E2` scalars. -/
def wReads (n : ℕ) : List ℕ := List.replicate n 16

/-- **`n` `E2` scalars.** -/
theorem refW_readE2s : ∀ (n : ℕ) {i : ℕ}, WAt rw i (wReads n) →
    RefAtW cap occ shp rw sig i (readE2s n) (E2V.e2Reads n) (fun xs ys ↦ ys = xs.map toE2) (i + n)
  | 0, i, _ => RefAtW.pure rfl
  | n + 1, i, hw => by
    rw [wReads, List.replicate_succ, WAt.cons] at hw
    refine RefAtW.bind (fun _ ↦ (monoD_readE2s n).bind fun _ ↦ MonoD.pure _) (refW_readE2 hw.1) ?_
    intro x y hxy
    refine RefAtW.bind (fun _ ↦ MonoD.pure _) (refW_readE2s n hw.2) ?_
    intro xs ys hs
    exact (RefAtW.pure (by simp [hxy, hs])).idx (by omega)

/-- **The nonce**: one 8-byte read whose value is unused. -/
theorem refW_nonce {i : ℕ} (hw : rw i = 8) :
    RefAtW cap occ shp rw sig i nonceE2 VerifierProgram.readScalar (fun _ _ ↦ True) (i + 1) := by
  intro s _
  refine ⟨_, rfl, rfl, ?_, rfl, trivial⟩
  show s.msg + rw i = s.msg + 8
  rw [hw]

/-- The widths of a ground challenge: its nonce. -/
def wSampleG : List ℕ := [8]

/-- **A ground `E2` challenge**: the nonce, the answer, `powOK`, lanes 0–1. -/
theorem refW_sampleG (g : ℕ) {i : ℕ} (hw : rw i = 8) :
    RefAtW cap occ shp rw sig i (sampleG g) (E2V.e2Sample g) (fun x y ↦ y = toE2 x) (i + 1) := by
  unfold sampleG E2V.e2Sample
  refine RefAtW.bind (fun _ ↦ monoD_sampleE.bind fun _ ↦ (MonoD.require _).bind fun _ ↦ MonoD.pure _)
    (refW_nonce hw) fun _ _ _ ↦ ?_
  refine RefAtW.bind (fun _ ↦ (MonoD.require _).bind fun _ ↦ MonoD.pure _) refW_sampleE ?_
  intro c c' hc
  subst hc
  refine RefAtW.bind (fun _ ↦ MonoD.pure _)
    (RefAtW.require (q := LeanVM.Protocol.Verifier.powOK g (FE.toExt3 c)) fun h ↦ by
      simpa only [DM.powOKR, LeanVM.Protocol.Verifier.powOK, eToNat_toExt3, decide_eq_true_eq]
        using h) fun _ _ _ ↦ RefAtW.pure (toE2_e2OfFE c).symm

/-- **`n` ground challenges.** -/
theorem refW_samplesG (g : ℕ) : ∀ (n : ℕ) {i : ℕ}, WAt rw i (List.replicate n 8) →
    RefAtW cap occ shp rw sig i (samplesG g n) (E2V.e2Samples g n) (fun xs ys ↦ ys = xs.map toE2) (i + n)
  | 0, i, _ => RefAtW.pure rfl
  | n + 1, i, hw => by
    rw [List.replicate_succ, WAt.cons] at hw
    refine RefAtW.bind (fun _ ↦ (monoD_samplesG g n).bind fun _ ↦ MonoD.pure _)
      (refW_sampleG g hw.1) ?_
    intro x y hxy
    refine RefAtW.bind (fun _ ↦ MonoD.pure _) (refW_samplesG g n hw.2) ?_
    intro xs ys hs
    exact (RefAtW.pure (by simp [hxy, hs])).idx (by omega)

/-- **The separator**: one sample, no read. -/
theorem refW_sepE2 {i : ℕ} :
    RefAtW cap occ shp rw sig i sepE2 E2V.e2Sep (fun _ _ ↦ True) i := by
  unfold sepE2 E2V.e2Sep
  exact RefAtW.bind (fun _ ↦ MonoD.pure _) refW_sampleE fun _ _ _ ↦ RefAtW.pure trivial

end Prim

end Lvm.VEq
