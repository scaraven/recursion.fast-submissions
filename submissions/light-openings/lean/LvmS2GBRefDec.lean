-- New for lvm2 MP-B cap pruning (CAP-V, 2026-11-17): the S2GB decision (`decideProgSB`) refines the compiled `P_S`'s
-- program at S2GB (`midGB`, the S2GB WHIR opening) on the S2GB stream (`ivpWB`: sent caps, heap entries), and the
-- schedule's `Fol` at `P20B`. Proof-help statements for `refinesB20` (V's own; not frozen).
import LvmS2GBFill

/-!
# The S2GB decision on the S2GB stream (owner V)

* **`ref_decideGB`**: `ref_decideGSX`'s twin: `decideProgSB P20B pT (contIvSB aSP)` refines
  `PSWithM (midP (midMk 4 relocU20 (midGB _)))` on `ivpWB capOfB occOfU shpS pthB hqB rwB20`, for a typed-phase
  record `pT` with the mini-bus at depth 13.
* **`fol_PSOfB`**: `P_S` at S2GB follows `atomsOf P20B (schedule P20B)` (`fol_PSOfS`'s twin; `Fol` at S2GS's caps
  `capS`: the schedule's cap items carry the level's `cap`, the driver sends `2^capSendBits`).
* **`decideFSB_ok`**, **`pubGB_eq`**: `decideFSG_ok`'s and `pubGS_eq`'s twins; **`parseOkB_parts`**.
* Proof help: `ivpB`/`RefAtB` (the S2GB stream at 24-byte reads; `RefAt.toB` for programs with no commitment and no
  opening, `NoCQ`), `ref_openingRB` (an opening and its heap entries), the WHIR twins (`LevelsCorrB`,
  `ref_whirLevelsJB`, `ref_dOpenFOB` on `dOpenFB`), the lifts (`RefAtB.toPWB`, `RefAtPW.toB`/`toBP` by `ivpWB_of_noOp`),
  the typed phases at depth 13 (`ref_dTypedLOB`, `ref_dTypedLSB`), `claimsL_relB`, `widthsA_scheduleB`, `corrMainB`.
-/

set_option autoImplicit false
namespace Lvm.VEq
open RecursionFast Lvm DM LeanVM.Parameters LeanVM.Protocol LeanVM.Protocol.Compile
open LeanVM.Protocol.Verifier (WhirStateT foldRoundsT tailRoundsT glueT whirLevelsUd verifyWhirUd
  verifyStackedUd UdConfig cidx whirLevelsJ verifyWhirJ verifyStackedJ WhirConfig)
open Lvm.M3 (tE_add tE_mul tE_zero tE_one FE_eq_of_beq)

/-! ## The S2GB stream at 24-byte reads (`ivp`'s twin) -/

section IvpB24

variable (cap : ℕ → ℕ → ℕ) (occ : ℕ → ℕ → ℕ) (shp : ℕ → ℕ × ℕ) (pth hq : ℕ → ℕ)

/-- **A program read off the S2GB stream at 24-byte reads** (`ivpWB` at `rw = 24`; `ivp` with the paths `pth` and
the heap entries `hq` after each opening). -/
def ivpB {α : Type} : VerifierProgram α → ByteArray → RS → Option α × RS
  | .ret a, _, s => (some a, s)
  | .fail, _, s => (none, s)
  | .grind _ _, _, s => (none, s)
  | .read k, sig, s =>
    ivpB (k (Lvm.FS.eOfBytes (sbs sig (s.ent + 40 + s.msg) 24))) sig { s with msg := s.msg + 24 }
  | .sample k, sig, s =>
    ivpB (k (Lvm.FS.chalOf (digestAt sig (s.ent + 40 + s.msg)))) sig
      { s with ent := s.ent + 72 + s.msg, msg := 0 }
  | .commit ht w k, sig, s => ivpB k sig { s with msg := s.msg + 32 * 2 ^ cap ht w }
  | .query i ps k, sig, s =>
    let r := opRows sig (shp i).2 (occ (shp i).1 (shp i).2) (pth i) ps.length s.ent
    ivpB (k r.1) sig { s with ent := r.2 + 104 * hq i }

/-- **`d` refines `P` on the S2GB stream** (`RefAt` with `ivpB`). -/
def RefAtB {α β : Type} (sig : ByteArray) (d : DM β) (P : VerifierProgram α) (R : β → α → Prop) : Prop :=
  ∀ s, (runD d sig s).2.ok = true →
    ∃ a, (ivpB cap occ shp pth hq P sig s).1 = some a ∧
      (ivpB cap occ shp pth hq P sig s).2.ent = (runD d sig s).2.ent ∧
      (ivpB cap occ shp pth hq P sig s).2.msg = (runD d sig s).2.msg ∧ R (runD d sig s).1 a

variable {cap occ shp pth hq}

theorem ivpB_congr {α : Type} (P : VerifierProgram α) (sig : ByteArray) {s s' : RS}
    (he : s.ent = s'.ent) (hm : s.msg = s'.msg) :
    (ivpB cap occ shp pth hq P sig s).1 = (ivpB cap occ shp pth hq P sig s').1 ∧
      (ivpB cap occ shp pth hq P sig s).2.ent = (ivpB cap occ shp pth hq P sig s').2.ent ∧
      (ivpB cap occ shp pth hq P sig s).2.msg = (ivpB cap occ shp pth hq P sig s').2.msg := by
  induction P generalizing s s' with
  | ret a => exact ⟨rfl, he, hm⟩
  | fail => exact ⟨rfl, he, hm⟩
  | grind b k ih => exact ⟨rfl, he, hm⟩
  | read k ih =>
    simp only [ivpB, he, hm]
    exact ih _ rfl rfl
  | sample k ih =>
    simp only [ivpB, he, hm]
    exact ih _ rfl rfl
  | commit ht w k ih =>
    simp only [ivpB]
    exact ih he (by simp [hm])
  | query i ps k ih =>
    simp only [ivpB, he]
    exact ih _ rfl hm

theorem ivpB_bind {α β : Type} (P : VerifierProgram α) (f : α → VerifierProgram β) (sig : ByteArray)
    (s : RS) : ivpB cap occ shp pth hq (P.bind f) sig s =
      match ivpB cap occ shp pth hq P sig s with
      | (some a, s') => ivpB cap occ shp pth hq (f a) sig s'
      | (none, s') => (none, s') := by
  induction P generalizing s with
  | ret a => rfl
  | fail => rfl
  | grind b k ih => rfl
  | read k ih => exact ih _ _
  | sample k ih => exact ih _ _
  | commit ht w k ih => exact ih _
  | query i ps k ih => exact ih _ _

/-- **A program with no commitment and no opening.** -/
def NoCQ {α : Type} : VerifierProgram α → Prop
  | .ret _ => True
  | .fail => True
  | .grind _ _ => True
  | .read k => ∀ y, NoCQ (k y)
  | .sample k => ∀ y, NoCQ (k y)
  | .commit _ _ _ => False
  | .query _ _ _ => False

theorem NoCQ.bind {α β : Type} {P : VerifierProgram α} {f : α → VerifierProgram β} (h : NoCQ P)
    (hf : ∀ a, NoCQ (f a)) : NoCQ (P.bind f) := by
  induction P with
  | ret a => exact hf a
  | fail => trivial
  | grind b k ih => trivial
  | read k ih => exact fun y ↦ ih y (h y)
  | sample k ih => exact fun y ↦ ih y (h y)
  | commit ht w k ih => exact h.elim
  | query i ps k ih => exact h.elim

/-- **With no commitment and no opening, the S2GB stream reads as the stream.** -/
theorem ivpB_noCQ {α : Type} {P : VerifierProgram α} (hP : NoCQ P) (sig : ByteArray) (s : RS) :
    ivpB cap occ shp pth hq P sig s = ivp cap occ shp P sig s := by
  induction P generalizing s with
  | ret a => rfl
  | fail => rfl
  | grind b k ih => rfl
  | read k ih => exact ih _ (hP _) _
  | sample k ih => exact ih _ (hP _) _
  | commit ht w k ih => exact hP.elim
  | query i ps k ih => exact hP.elim

theorem RefAt.toB {α β : Type} {sig : ByteArray} {d : DM β} {P : VerifierProgram α} {R : β → α → Prop}
    (h : RefAt cap occ shp sig d P R) (hP : NoCQ P) : RefAtB cap occ shp pth hq sig d P R := by
  intro s hok
  rw [ivpB_noCQ hP]
  exact h s hok

variable {sig : ByteArray}

theorem RefAtB.mono {α β : Type} {d : DM β} {P : VerifierProgram α} {R R' : β → α → Prop}
    (h : RefAtB cap occ shp pth hq sig d P R) (hR : ∀ b a, R b a → R' b a) :
    RefAtB cap occ shp pth hq sig d P R' :=
  fun s hok ↦ by
    obtain ⟨a, h1, h2, h3, h4⟩ := h s hok
    exact ⟨a, h1, h2, h3, hR _ _ h4⟩

theorem RefAtB.bind {α α' β β' : Type} {d : DM β} {d' : β → DM β'} {P : VerifierProgram α}
    {P' : α → VerifierProgram α'} {R : β → α → Prop} {R' : β' → α' → Prop}
    (hm : ∀ b, MonoD (d' b)) (h : RefAtB cap occ shp pth hq sig d P R)
    (h' : ∀ b a, R b a → RefAtB cap occ shp pth hq sig (d' b) (P' a) R') :
    RefAtB cap occ shp pth hq sig (d >>= d') (P.bind P') R' := by
  intro s hok
  have hsplit : runD (d >>= d') sig s = runD (d' (runD d sig s).1) sig (runD d sig s).2 := rfl
  rw [hsplit] at hok ⊢
  obtain ⟨a, ha, he, hmsg, hR⟩ := h s (hm _ sig _ hok)
  obtain ⟨a', ha', he', hm', hR'⟩ := h' _ _ hR _ hok
  refine ⟨a', ?_⟩
  rw [ivpB_bind]
  rcases hP : ivpB cap occ shp pth hq P sig s with ⟨_ | a₀, s₂⟩
  · rw [hP] at ha; exact absurd ha (by simp)
  · rw [hP] at ha he hmsg
    simp only [Option.some.injEq] at ha
    subst ha
    obtain ⟨c1, c2, c3⟩ := ivpB_congr (cap := cap) (occ := occ) (shp := shp) (pth := pth) (hq := hq)
      (P' a₀) sig he hmsg
    exact ⟨c1.trans ha', c2.trans he', c3.trans hm', hR'⟩

theorem RefAtB.pure {α β : Type} {b : β} {a : α} {R : β → α → Prop} (h : R b a) :
    RefAtB cap occ shp pth hq sig (Pure.pure b : DM β) (VerifierProgram.ret a) R :=
  fun _ _ ↦ ⟨a, rfl, rfl, rfl, h⟩

theorem RefAtB.dm_left {α β β' : Type} {d₀ : DM β'} {b₀ : β'} (h₀ : ∀ s, runD d₀ sig s = (b₀, s))
    {d : β' → DM β} {P : VerifierProgram α} {R : β → α → Prop} (h : RefAtB cap occ shp pth hq sig (d b₀) P R) :
    RefAtB cap occ shp pth hq sig (d₀ >>= d) P R := by
  intro s hok
  have hsplit : runD (d₀ >>= d) sig s = runD (d b₀) sig s := by
    show runD (d (runD d₀ sig s).1) sig (runD d₀ sig s).2 = _
    rw [h₀]
  rw [hsplit] at hok ⊢
  exact h s hok

theorem RefAtB.read_left {α β : Type} {d : ByteArray → DM β} {P : VerifierProgram α}
    {R : β → α → Prop} (h : RefAtB cap occ shp pth hq sig (d sig) P R) :
    RefAtB cap occ shp pth hq sig (MonadReader.read >>= d) P R :=
  RefAtB.dm_left (fun _ ↦ rfl) h

theorem RefAtB.require_false_bind {α β : Type} {k : Unit → DM β} {P : VerifierProgram α}
    {R : β → α → Prop} (hk : ∀ u, MonoD (k u)) : RefAtB cap occ shp pth hq sig (DM.require false >>= k) P R := by
  intro s hok
  have hsplit : runD (DM.require false >>= k) sig s =
      runD (k ()) sig { s with ok := false && s.ok } := rfl
  rw [hsplit] at hok
  exact absurd (hk () sig _ hok) (by simp)

theorem RefAtB.require_false {α : Type} {P : VerifierProgram α} {R : Unit → α → Prop} :
    RefAtB cap occ shp pth hq sig (DM.require false) P R := by
  intro s hok
  have h : (runD (DM.require false) sig s).2.ok = (false && s.ok) := rfl
  rw [h] at hok
  exact absurd hok (by simp)

theorem RefAtB.assoc {α β γ δ : Type} {d : DM γ} {f : γ → DM δ} {k : δ → DM β} {P : VerifierProgram α}
    {R : β → α → Prop} (h : RefAtB cap occ shp pth hq sig (d >>= fun x ↦ f x >>= k) P R) :
    RefAtB cap occ shp pth hq sig ((d >>= f) >>= k) P R := h

/-- **A cap**: its bytes skipped (`ref_skip`'s twin). -/
theorem ref_skipB {ht w n : ℕ} (h : n = 32 * 2 ^ cap ht w) :
    RefAtB cap occ shp pth hq sig (DM.skip n) (VerifierProgram.readCommitment ht w) fun _ _ ↦ True := by
  intro s _
  subst h
  exact ⟨(), rfl, rfl, rfl, trivial⟩

theorem monoD_skipEntries (n : ℕ) : MonoD (Lvm.skipEntries n) := fun _ _ h ↦ h

/-- **An opening and its heap entries**: the rows at V_S's row offsets, the cursor after the `n` heap entries
(`ref_openingR`'s twin). -/
theorem ref_openingRB (L : Level) {i : ℕ} {ps : List ℕ} {wd n : ℕ} (hshp : shp i = (L.height, wd))
    (hrow : L.row = 8 * min (occ L.height wd) wd) (hpath : pth i = L.path) (hhq : hq i = n)
    (hlen : ps.length = L.t) :
    RefAtB cap occ shp pth hq sig (DM.openingR L >>= fun o ↦ Lvm.skipEntries n >>= fun _ ↦ Pure.pure o)
      (VerifierProgram.queryOpenings i ps)
      fun offs rows ↦ rows = offs.map fun o ↦ padAt sig o wd (occ L.height wd) := by
  intro s _
  have hsplit : runD (DM.openingR L >>= fun o ↦ Lvm.skipEntries n >>= fun _ ↦ Pure.pure o) sig s =
      ((runD (DM.openingAux L L.t) sig { s with ok := s.ok && s.msg == 0 }).1,
        { (runD (DM.openingAux L L.t) sig { s with ok := s.ok && s.msg == 0 }).2 with
          ent := (runD (DM.openingAux L L.t) sig { s with ok := s.ok && s.msg == 0 }).2.ent + 104 * n }) := rfl
  obtain ⟨h1, h2, h3⟩ := opRows_openingAux (sig := sig) L wd (occ L.height wd) hrow L.t
    { s with ok := s.ok && s.msg == 0 }
  have hiv : ivpB cap occ shp pth hq (VerifierProgram.queryOpenings i ps) sig s =
      (some (opRows sig wd (occ L.height wd) L.path L.t s.ent).1,
        { s with ent := (opRows sig wd (occ L.height wd) L.path L.t s.ent).2 + 104 * n }) := by
    simp only [VerifierProgram.queryOpenings, ivpB, hshp, hlen, hpath, hhq]
  rw [hsplit, hiv]
  exact ⟨_, rfl, by rw [← h1], h3.symm, h2⟩

end IvpB24


/-! ## Leaves on the S2GB stream (programs with no commitment and no opening) -/

section LeavesB

theorem noCQ_readScalar : NoCQ VerifierProgram.readScalar := fun _ ↦ trivial

theorem noCQ_sampleChallenge : NoCQ VerifierProgram.sampleChallenge := fun _ ↦ trivial

theorem noCQ_readScalars : ∀ n, NoCQ (VerifierProgram.readScalars n)
  | 0 => trivial
  | n + 1 => NoCQ.bind noCQ_readScalar fun _ ↦ NoCQ.bind (noCQ_readScalars n) fun _ ↦ trivial

theorem noCQ_sampleChallenges : ∀ n, NoCQ (VerifierProgram.sampleChallenges n)
  | 0 => trivial
  | n + 1 => NoCQ.bind noCQ_sampleChallenge fun _ ↦ NoCQ.bind (noCQ_sampleChallenges n) fun _ ↦ trivial

theorem noCQ_require (c : Prop) [Decidable c] : NoCQ (VerifierProgram.require c) := by
  unfold VerifierProgram.require
  split <;> trivial

theorem noCQ_rp (count : ℕ) (claim : E) : ∀ e, NoCQ (Verifier.sumcheckRoundPoly count claim e)
  | none => NoCQ.bind noCQ_readScalar fun _ ↦ NoCQ.bind (noCQ_readScalars _) fun _ ↦ trivial
  | some _ => NoCQ.bind (noCQ_readScalars _) fun _ ↦ trivial

theorem noCQ_foldRoundsT : ∀ n s lf, NoCQ (Verifier.foldRoundsT n s lf)
  | 0, _, _ => trivial
  | n + 1, _, _ => NoCQ.bind noCQ_sampleChallenge fun _ ↦ NoCQ.bind (noCQ_rp _ _ _) fun _ ↦
    noCQ_foldRoundsT n _ _

theorem noCQ_tailRoundsT : ∀ n t q, NoCQ (Verifier.tailRoundsT n t q)
  | 0, _, _ => trivial
  | n + 1, _, _ => NoCQ.bind noCQ_sampleChallenge fun _ ↦ by
    dsimp only
    split
    · trivial
    · exact NoCQ.bind (noCQ_rp _ _ _) fun _ ↦ NoCQ.bind (noCQ_tailRoundsT n _ _) fun _ ↦ trivial

theorem noCQ_grindPre (g : ℕ) : NoCQ (Verifier.grindPre g) := by
  unfold Verifier.grindPre
  split
  · trivial
  · exact NoCQ.bind noCQ_sampleChallenge fun _ ↦ NoCQ.bind noCQ_readScalar fun _ ↦ trivial

theorem noCQ_powCheck (g : ℕ) : NoCQ (Verifier.powCheck g) := by
  unfold Verifier.powCheck
  split
  · trivial
  · exact NoCQ.bind noCQ_sampleChallenge fun _ ↦ noCQ_require _

theorem noCQ_samplePositionsAux (per depth : ℕ) :
    ∀ fuel rem, NoCQ (Verifier.samplePositionsAux per depth fuel rem)
  | 0, _ => trivial
  | fuel + 1, rem => by
    unfold Verifier.samplePositionsAux
    split
    · trivial
    · exact NoCQ.bind noCQ_sampleChallenge fun _ ↦
        NoCQ.bind (noCQ_samplePositionsAux per depth fuel _) fun _ ↦ trivial

variable {cap : ℕ → ℕ → ℕ} {occ : ℕ → ℕ → ℕ} {shp : ℕ → ℕ × ℕ} {pth hq : ℕ → ℕ} {sig : ByteArray}

theorem monoD_rpWB (claim : FE) (e : Option FE) : MonoD (Lvm.sumcheckRoundPoly 3 claim e) := by
  cases e
  · exact monoD_readE.bind fun _ ↦ (monoD_readEs _).bind fun _ ↦ MonoD.pure _
  · exact (monoD_readEs _).bind fun _ ↦ MonoD.pure _

theorem ref_rpW0 {claim : FE} {claim' : E} (h : claim' = FE.toExt3 claim) :
    RefAt cap occ shp sig (Lvm.sumcheckRoundPoly 3 claim none) (Verifier.sumcheckRoundPoly 3 claim' none)
      (fun xs ys ↦ ys = xs.map FE.toExt3) := by
  subst h
  refine RefAt.bind (fun _ ↦ (monoD_readEs _).bind fun _ ↦ MonoD.pure _) ref_readE ?_
  rintro x _ rfl
  refine RefAt.bind (fun _ ↦ MonoD.pure _) (ref_readEs _) ?_
  rintro xs _ rfl
  exact RefAt.pure (by simp [toExt3_sumE])

theorem ref_rpWB {claim : FE} {claim' : E} (h : claim' = FE.toExt3 claim) :
    RefAtB cap occ shp pth hq sig (Lvm.sumcheckRoundPoly 3 claim none) (Verifier.sumcheckRoundPoly 3 claim' none)
      (fun xs ys ↦ ys = xs.map FE.toExt3) :=
  (ref_rpW0 h).toB (noCQ_rp _ _ _)

theorem ref_readEB :
    RefAtB cap occ shp pth hq sig DM.readE VerifierProgram.readScalar fun x y ↦ y = FE.toExt3 x :=
  ref_readE.toB noCQ_readScalar

theorem ref_sampleEB :
    RefAtB cap occ shp pth hq sig DM.sampleE VerifierProgram.sampleChallenge fun x y ↦ y = FE.toExt3 x :=
  ref_sampleE.toB noCQ_sampleChallenge

theorem ref_readEsB (n : ℕ) : RefAtB cap occ shp pth hq sig (DM.readEs n) (VerifierProgram.readScalars n)
    fun xs ys ↦ ys = xs.map FE.toExt3 :=
  (ref_readEs n).toB (noCQ_readScalars n)

theorem ref_samplesB (n : ℕ) : RefAtB cap occ shp pth hq sig (DM.samples n) (VerifierProgram.sampleChallenges n)
    fun xs ys ↦ ys = xs.map FE.toExt3 :=
  (ref_samples n).toB (noCQ_sampleChallenges n)

theorem ref_foldRoundsB (n : ℕ) (s : Lvm.WhirState) (t : WhirStateT) (lf : List FE) (lf' : List E)
    (hW : WRel s t) (hl : lf' = lf.map FE.toExt3) :
    RefAtB cap occ shp pth hq sig (Lvm.foldRounds n s lf) (foldRoundsT n t lf')
      (fun r r' ↦ WRel r.1 r'.1 ∧ r'.2 = r.2.map FE.toExt3 ∧ r.1.folds.length = s.folds.length + n ∧
        r.2.length = lf.length + n) :=
  (ref_foldRounds n s t lf lf' hW hl).toB (noCQ_foldRoundsT _ _ _)

theorem ref_tailRoundsB (n : ℕ) (quad : List FE) (tgt : E) (quad' : List E) (hq' : quad' = quad.map FE.toExt3) :
    RefAtB cap occ shp pth hq sig (Lvm.tailRounds n quad) (tailRoundsT n tgt quad')
      (fun r r' ↦ r' = (r.1.map FE.toExt3, FE.toExt3 r.2)) :=
  (ref_tailRounds n quad tgt quad' hq').toB (noCQ_tailRoundsT _ _ _)

theorem ref_positionsWB (L : Level) {h' t' : ℕ} (hh : h' = L.height) (ht : t' = L.t) :
    RefAtB cap occ shp pth hq sig (DM.positionsR L) (Verifier.samplePositions positionsPerAnswer h' t')
      (fun ps ps' ↦ ps' = ps ∧ ps.length = L.t) :=
  (ref_positionsW L hh ht).toB (noCQ_samplePositionsAux _ _ _ _)

theorem ref_grindPreRB (g : ℕ) :
    RefAtB cap occ shp pth hq sig (DM.grindPreR g) (Verifier.grindPre g) fun _ _ ↦ True :=
  (ref_grindPreR g).toB (noCQ_grindPre g)

theorem ref_powCheckRB (g : ℕ) :
    RefAtB cap occ shp pth hq sig (DM.powCheckR g) (Verifier.powCheck g) fun _ _ ↦ True :=
  (ref_powCheckR g).toB (noCQ_powCheck g)

theorem RefAtB.require {c : Bool} {q : Prop} [Decidable q] (h : c = true → q) :
    RefAtB cap occ shp pth hq sig (DM.require c) (VerifierProgram.require q) fun _ _ ↦ True :=
  (RefAt.require h).toB (noCQ_require q)

theorem RefAtB.require_left {α β : Type} {c : Bool} {d : Unit → DM β} {P : VerifierProgram α}
    {R : β → α → Prop} (hm : ∀ u, MonoD (d u))
    (h : c = true → RefAtB cap occ shp pth hq sig (d ()) P R) :
    RefAtB cap occ shp pth hq sig (DM.require c >>= d) P R := by
  intro s hok
  have e : runD (DM.require c >>= d) sig s = runD (d ()) sig { s with ok := c && s.ok } := rfl
  rw [e] at hok ⊢
  have hc : c = true := (Bool.and_eq_true _ _ ▸ hm () sig _ hok).1
  obtain ⟨a, h1, h2, h3, h4⟩ := h hc _ hok
  obtain ⟨c1, c2, c3⟩ := ivpB_congr (cap := cap) (occ := occ) (shp := shp) (pth := pth) (hq := hq) P sig
    (s := s) (s' := { s with ok := c && s.ok }) rfl rfl
  exact ⟨a, c1.trans h1, c2.trans h2, c3.trans h3, h4⟩

/-- An opening and its heap entries, then the rest. -/
theorem RefAtB.bind_open {α α' β' γ : Type} {d : DM γ} {e : DM Unit} {d' : γ → DM β'}
    {P : VerifierProgram α} {P' : α → VerifierProgram α'} {R : γ → α → Prop} {R' : β' → α' → Prop}
    (hm : ∀ b, MonoD (d' b)) (h : RefAtB cap occ shp pth hq sig (d >>= fun o ↦ e >>= fun _ ↦ Pure.pure o) P R)
    (h' : ∀ b a, R b a → RefAtB cap occ shp pth hq sig (d' b) (P' a) R') :
    RefAtB cap occ shp pth hq sig (d >>= fun o ↦ e >>= fun _ ↦ d' o) (P.bind P') R' := by
  have h2 := RefAtB.bind (d := d >>= fun o ↦ e >>= fun _ ↦ Pure.pure o) (d' := d') hm h h'
  exact h2

theorem ref_oodStepB {α β : Type} (k : ℕ) {K : List (List FE × (List FE → FE)) → DM β}
    {P : List E → E → List E → VerifierProgram α} {R : β → α → Prop} (hK : ∀ oc, MonoD (K oc))
    (h : ∀ (z : List FE) (y : FE) (i : List FE), RefAtB cap occ shp pth hq sig (K [(i, fun x ↦ Lvm.eqEval z x)])
      (P (z.map FE.toExt3) (FE.toExt3 y) (i.map FE.toExt3)) R) :
    RefAtB cap occ shp pth hq sig (Lvm.oodStep true k >>= K)
      ((VerifierProgram.sampleChallenges k).bind fun z ↦ VerifierProgram.readScalar.bind fun y ↦
        (Verifier.sumcheckRoundPoly 3 y none).bind fun i ↦ P z y i) R := by
  rw [Lvm.oodStep, if_pos rfl]
  refine RefAtB.assoc ?_
  refine RefAtB.bind (fun _ ↦ (monoD_readE.bind fun _ ↦ (monoD_rpWB _ _).bind fun _ ↦ MonoD.pure _).bind hK)
    (ref_samplesB k) ?_
  rintro z _ rfl
  refine RefAtB.assoc ?_
  refine RefAtB.bind (fun _ ↦ ((monoD_rpWB _ _).bind fun _ ↦ MonoD.pure _).bind hK) ref_readEB ?_
  rintro y _ rfl
  refine RefAtB.assoc ?_
  refine RefAtB.bind (fun _ ↦ (MonoD.pure _).bind hK) (ref_rpWB rfl) ?_
  rintro i _ rfl
  exact RefAtB.dm_left (fun _ ↦ rfl) (h z y i)

end LeavesB

/-! ## The S2GB WHIR levels -/

theorem monoD_whirLevelsFB (p : Params) (logN laneFolds : ℕ) (eb : List FE → FE) (direct : Bool) (g : ℕ)
    (ood : Bool) : ∀ (Ls : List Level) (s : Lvm.WhirState), MonoD (Lvm.whirLevelsFB p logN laneFolds eb direct g ood Ls s)
  | [], _ => MonoD.require _
  | [L], s => by
    rw [Lvm.whirLevelsFB]
    refine (monoD_foldRounds _ _ _).bind fun r ↦ ?_
    obtain ⟨s', lf⟩ := r
    dsimp only
    refine (monoD_readEs _).bind fun _ ↦ (MonoD.pure _).bind fun _ ↦ (monoD_grindPreR _).bind fun _ ↦
      (monoD_powCheckR _).bind
      fun _ ↦ (monoD_positionsR _).bind fun _ ↦ monoD_sampleE.bind fun _ ↦
      (monoD_openingR _).bind fun _ ↦ (monoD_skipEntries _).bind fun _ ↦ MonoD.read.bind fun _ ↦
      (monoD_rpWB _ _).bind fun _ ↦ ?_
    split
    · exact (MonoD.require _).bind fun _ ↦ (monoD_tailRounds _ _).bind fun _ ↦ MonoD.require _
    · exact (monoD_tailRounds _ _).bind fun _ ↦ MonoD.require _
  | L :: N :: Ls, s => by
    rw [Lvm.whirLevelsFB]
    refine (monoD_foldRounds _ _ _).bind fun r ↦ ?_
    obtain ⟨s', lf⟩ := r
    dsimp only
    exact (monoD_skip _).bind fun _ ↦ (MonoD.pure _).bind fun _ ↦ (monoD_oodStep _ _).bind fun _ ↦
      (monoD_grindPreR _).bind fun _ ↦
      (monoD_powCheckR _).bind fun _ ↦ (monoD_positionsR _).bind fun _ ↦
      monoD_sampleE.bind fun _ ↦ (monoD_openingR _).bind fun _ ↦ (monoD_skipEntries _).bind fun _ ↦
      MonoD.read.bind fun _ ↦
      (monoD_rpWB _ _).bind fun _ ↦ monoD_whirLevelsFB p logN laneFolds eb direct g ood (N :: Ls) _

theorem monoD_verifyWhirFB (p : Params) (levels : List Level) (logN : ℕ) (target : FE) (eb : List FE → FE)
    (direct : Bool) (g : ℕ) (ood : Bool) : MonoD (Lvm.verifyWhirFB p levels logN target eb direct g ood) :=
  (monoD_rpWB _ _).bind fun _ ↦ monoD_whirLevelsFB _ _ _ _ _ _ _ _ _

/-- The next level's sent cap at S2GB: V_S skips `nodeBytes · 2^capSendBits` bytes where the language reads the
commitment. -/
def NextOKB (p : Params) (cap : ℕ → ℕ → ℕ) (logN F' : ℕ) : List Level → List Whir.Level → Prop
  | N :: _, W :: _ =>
    nodeBytes * 2 ^ p.capSendBits N.level N.cap = 32 * 2 ^ cap (logN - F' - W.fold + W.logInvRate) (3 * 2 ^ W.fold)
  | _, _ => True

/-- **The levels correspond on the S2GB stream** (`LevelsCorr`'s twin): each level as `LevelOK` at the levels' caps
`capL`, the stream's path `pth` the level's path, its heap entries `hq` the level's `heapQ`, and the next level's
sent cap at the stream's `cap`. -/
def LevelsCorrB (p : Params) (capL cap : ℕ → ℕ → ℕ) (occ : ℕ → ℕ → ℕ) (shp : ℕ → ℕ × ℕ) (pth hq : ℕ → ℕ)
    (logN c₀ n₀ : ℕ) : ℕ → ℕ → List Level → List Whir.Level → Prop
  | _, _, [], [] => True
  | j, F, L :: Ls, W :: Ws => LevelOK capL occ shp logN c₀ n₀ j F L W ∧ pth (cidx c₀ n₀ j) = L.path ∧
      hq (cidx c₀ n₀ j) = p.heapQ L.level L.cap ∧ NextOKB p cap logN (F + L.fold) Ls Ws ∧
      LevelsCorrB p capL cap occ shp pth hq logN c₀ n₀ (j + 1) (F + L.fold) Ls Ws
  | _, _, _, _ => False

section RefB

variable {cap : ℕ → ℕ → ℕ} {occ : ℕ → ℕ → ℕ} {shp : ℕ → ℕ × ℕ} {pth hq : ℕ → ℕ} {sig : ByteArray}
  {capL : ℕ → ℕ → ℕ}

/-- **The final level at S2GB** (`ref_levelFinal`'s twin). -/
theorem ref_levelFinalB (p : Params) (logN laneFolds c₀ n₀ g : ℕ) (ood : Bool) (eb : List FE → FE)
    (eb' : List E → E) (heb : ∀ xs, eb' (xs.map FE.toExt3) = FE.toExt3 (eb xs)) (L : Level) (W : Whir.Level)
    (j F : ℕ) (s : Lvm.WhirState) (t : WhirStateT) (hL : LevelOK capL occ shp logN c₀ n₀ j F L W)
    (hpth : pth (cidx c₀ n₀ j) = L.path) (hhq : hq (cidx c₀ n₀ j) = p.heapQ L.level L.cap) (hW : WRel s t)
    (hF : s.folds.length = F) :
    RefAtB cap occ shp pth hq sig (Lvm.whirLevelsFB p logN laneFolds eb false g ood [L] s)
      (whirLevelsUd logN laneFolds positionsPerAnswer c₀ n₀ g false eb' j [W] t) (fun _ _ ↦ True) := by
  rw [Lvm.whirLevelsFB, whirLevelsUd, ← hL.fold, ← hL.t]
  refine RefAtB.bind ?_ (ref_foldRoundsB L.fold s t [] [] hW rfl) ?_
  rotate_left
  rintro ⟨s1, lf⟩ ⟨t1, lf'⟩ ⟨hW1, rfl, hF1, hlf⟩
  dsimp only at hW1 hF1 hlf ⊢
  simp only [List.length_nil, Nat.zero_add] at hlf
  have hm : t1.folds.length = F + L.fold := by rw [hW1.folds, List.length_map, hF1, hF]
  rw [hm, hF1, hF]
  refine RefAtB.bind ?_ (ref_readEsB _) ?_
  rotate_left
  rintro res _ rfl
  refine RefAtB.dm_left (b₀ := ([] : List (List FE × (List FE → FE)))) (fun _ ↦ rfl) ?_
  refine RefAtB.bind ?_ (ref_grindPreRB g) ?_
  rotate_left
  rintro _ _ -
  refine RefAtB.bind ?_ (ref_powCheckRB g) ?_
  rotate_left
  rintro _ _ -
  refine RefAtB.bind ?_ (ref_positionsWB L hL.height.symm rfl) ?_
  rotate_left
  rintro qs0 qs ⟨rfl, hqs⟩
  refine RefAtB.bind ?_ ref_sampleEB ?_
  rotate_left
  rintro lam _ rfl
  refine RefAtB.bind_open ?_ (ref_openingRB L hL.shp hL.row hpth hhq hqs) ?_
  rotate_left
  rintro offs _ rfl
  refine RefAtB.read_left ?_
  refine RefAtB.bind ?_ (ref_rpWB (toExt3_enforced L j _ hL.level lf hlf hL.row hL.full offs _ _
      (map_powers _ _).symm)) ?_
  rotate_left
  rintro intro _ rfl
  have hW2 : ∀ v, WRel (Lvm.glue lam s1 [(intro, fun x ↦
        Lvm.inducedWeightK (logN - (F + L.fold)) qs (powers lam qs.length) x)])
      (glueT (FE.toExt3 lam) t1 [(v, intro.map FE.toExt3, fun x ↦
        Verifier.inducedWeight (logN - (F + L.fold)) qs (Verifier.powers (FE.toExt3 lam) qs.length) x)]) :=
    fun v ↦ wrel_glue hW1 rfl rfl (fun xs ↦ by rw [Lvm.inducedWeightK_eq, toExt3_inducedWeight, map_powers]) v
  rw [ite_cond_eq_false _ _ (by decide : (false = true) = False),
    ite_cond_eq_false _ _ (by decide : (false = true) = False),
    VerifierProgram.pure_eq, VerifierProgram.ret_bind]
  refine RefAtB.bind ?_ (ref_tailRoundsB _ _ _ _ (hW2 _).quad) ?_
  rotate_left
  rintro ⟨tf, tg⟩ _ rfl
  exact RefAtB.require fun h ↦
    (toExt3_terminal (hW2 _) eb eb' heb laneFolds tf res).trans (congrArg FE.toExt3 (FE_eq_of_beq h))
  all_goals repeat' (first
    | (with_reducible exact MonoD.pure _) | (with_reducible exact MonoD.require _)
    | (with_reducible exact MonoD.read) | (with_reducible exact monoD_readE)
    | (with_reducible exact monoD_sampleE) | (with_reducible exact monoD_skip _)
    | (with_reducible exact monoD_skipEntries _)
    | (with_reducible exact monoD_readEs _) | (with_reducible exact monoD_positionsR _)
    | (with_reducible exact monoD_openingR _) | (with_reducible exact monoD_rpWB _ _)
    | (with_reducible exact monoD_foldRounds _ _ _) | (with_reducible exact monoD_tailRounds _ _)
    | (with_reducible exact monoD_whirLevelsFB _ _ _ _ _ _ _ _ _) | (with_reducible exact monoD_oodStep _ _)
    | (with_reducible exact monoD_samples _)
    | (with_reducible exact monoD_grindPreR _) | (with_reducible exact monoD_powCheckR _)
    | (with_reducible refine MonoD.bind ?_ fun _ ↦ ?_) | (dsimp only) | split | intro _)

/-- **The S2GB level loop with OOD samples** against `whirLevelsJ` (`ref_whirLevelsJ`'s twin). -/
theorem ref_whirLevelsJB (p : Params) (logN laneFolds c₀ n₀ g : ℕ) (eb : List FE → FE) (eb' : List E → E)
    (heb : ∀ xs, eb' (xs.map FE.toExt3) = FE.toExt3 (eb xs)) :
    ∀ (Ls : List Level) (Ws : List Whir.Level) (j F : ℕ) (s : Lvm.WhirState) (t : WhirStateT),
      LevelsCorrB p capL cap occ shp pth hq logN c₀ n₀ j F Ls Ws → WRel s t → s.folds.length = F →
      RefAtB cap occ shp pth hq sig (Lvm.whirLevelsFB p logN laneFolds eb false g true Ls s)
        (whirLevelsJ logN laneFolds positionsPerAnswer c₀ n₀ g false eb' j Ws t) (fun _ _ ↦ True)
  | [], _, _, _, _, _, _, _, _ => by rw [Lvm.whirLevelsFB]; exact RefAtB.require_false
  | _ :: _, [], _, _, _, _, hc, _, _ => False.elim hc
  | [L], [W], j, F, s, t, hc, hW, hF => by
    rw [LeanVM.Protocol.Verifier.whirLevelsJ_one]
    exact ref_levelFinalB p logN laneFolds c₀ n₀ g true eb eb' heb L W j F s t hc.1 hc.2.1 hc.2.2.1 hW hF
  | [_], _ :: _ :: _, _, _, _, _, hc, _, _ => False.elim hc.2.2.2.2
  | _ :: _ :: _, [_], _, _, _, _, hc, _, _ => False.elim hc.2.2.2.2
  | L :: N :: Ls, W :: W' :: Ws, j, F, s, t, hc, hW, hF => by
    obtain ⟨hL, hpth, hhq, hN, hc'⟩ := hc
    have ih := ref_whirLevelsJB p logN laneFolds c₀ n₀ g eb eb' heb (N :: Ls) (W' :: Ws) (j + 1) (F + L.fold)
    rw [Lvm.whirLevelsFB, whirLevelsJ, ← hL.fold, ← hL.t]
    refine RefAtB.bind ?_ (ref_foldRoundsB L.fold s t [] [] hW rfl) ?_
    rotate_left
    rintro ⟨s1, lf⟩ ⟨t1, lf'⟩ ⟨hW1, rfl, hF1, hlf⟩
    dsimp only at hW1 hF1 hlf ⊢
    simp only [List.length_nil, Nat.zero_add] at hlf
    have hm : t1.folds.length = F + L.fold := by rw [hW1.folds, List.length_map, hF1, hF]
    rw [hm, hF1, hF]
    refine RefAtB.bind ?_ (ref_skipB hN) ?_
    rotate_left
    rintro _ _ -
    refine RefAtB.dm_left (b₀ := ([] : List FE)) (fun _ ↦ rfl) ?_
    refine ref_oodStepB _ ?_ fun z y oi ↦ ?_
    rotate_left
    refine RefAtB.bind ?_ (ref_grindPreRB g) ?_
    rotate_left
    rintro _ _ -
    refine RefAtB.bind ?_ (ref_powCheckRB g) ?_
    rotate_left
    rintro _ _ -
    refine RefAtB.bind ?_ (ref_positionsWB L hL.height.symm rfl) ?_
    rotate_left
    rintro qs0 qs ⟨rfl, hqs⟩
    refine RefAtB.bind ?_ ref_sampleEB ?_
    rotate_left
    rintro lam _ rfl
    refine RefAtB.bind_open ?_ (ref_openingRB L hL.shp hL.row hpth hhq hqs) ?_
    rotate_left
    rintro offs _ rfl
    refine RefAtB.read_left ?_
    refine RefAtB.bind ?_ (ref_rpWB (toExt3_enforced L j _ hL.level lf hlf hL.row hL.full offs _ _
      (map_powers _ _).symm)) ?_
    rotate_left
    rintro intro _ rfl
    exact ih _ _ hc' (wrel_glue2 hW1 rfl rfl rfl (fun xs ↦ (toExt3_eqEval z xs).symm)
      (fun xs ↦ by rw [Lvm.inducedWeightK_eq, toExt3_inducedWeight, map_powers]) _ _)
      (hF1.trans (congrArg (· + L.fold) hF))
    all_goals repeat' (first
      | (with_reducible exact MonoD.pure _) | (with_reducible exact MonoD.require _)
      | (with_reducible exact MonoD.read) | (with_reducible exact monoD_readE)
      | (with_reducible exact monoD_sampleE) | (with_reducible exact monoD_skip _)
      | (with_reducible exact monoD_skipEntries _)
      | (with_reducible exact monoD_readEs _) | (with_reducible exact monoD_positionsR _)
      | (with_reducible exact monoD_openingR _) | (with_reducible exact monoD_rpWB _ _)
      | (with_reducible exact monoD_foldRounds _ _ _) | (with_reducible exact monoD_tailRounds _ _)
      | (with_reducible exact monoD_whirLevelsFB _ _ _ _ _ _ _ _ _) | (with_reducible exact monoD_oodStep _ _)
      | (with_reducible exact monoD_samples _)
      | (with_reducible exact monoD_grindPreR _) | (with_reducible exact monoD_powCheckR _)
      | (with_reducible refine MonoD.bind ?_ fun _ ↦ ?_) | (dsimp only) | split | intro _)

/-- **One S2GB WHIR opening with OOD samples** (`ref_verifyWhirJ`'s twin). -/
theorem ref_verifyWhirJB (p : Params) (levels : List Level) (cfg : WhirConfig) (logN g : ℕ) (target : FE)
    (target' : E) (eb : List FE → FE) (eb' : List E → E) (heb : ∀ xs, eb' (xs.map FE.toExt3) = FE.toExt3 (eb xs))
    (ht : target' = FE.toExt3 target) (hood : cfg.ood = true) (hμ : cfg.μ = logN)
    (hper : cfg.per = positionsPerAnswer) (hdir : cfg.direct = false) (hg : cfg.grind = g)
    (hc : LevelsCorrB p capL cap occ shp pth hq logN cfg.c₀ cfg.n₀ 0 0 levels cfg.levels) :
    RefAtB cap occ shp pth hq sig (Lvm.verifyWhirFB p levels logN target eb false g true)
      (verifyWhirJ cfg target' eb') (fun _ _ ↦ True) := by
  obtain ⟨⟨μ, Ws, per, c₀, n₀, direct, grind⟩, ood⟩ := cfg
  dsimp only at hood hμ hper hdir hg hc
  subst hood hμ hper hdir hg
  have hlf : (Ws.head?.map (·.fold)).getD 0 = (levels.head?.map (·.fold)).getD 0 := by
    cases levels <;> cases Ws
    · rfl
    · exact False.elim hc
    · exact False.elim hc
    · simp [hc.1.fold]
  unfold verifyWhirJ
  rw [if_pos rfl]
  dsimp only
  rw [hlf]
  refine RefAtB.bind (fun _ ↦ monoD_whirLevelsFB _ _ _ _ _ _ _ _ _) (ref_rpWB ht) ?_
  rintro q _ rfl
  exact ref_whirLevelsJB _ _ _ _ _ _ eb eb' heb levels Ws 0 0 _ _ hc ⟨rfl, rfl, List.Forall₂.nil⟩ rfl

end RefB

end Lvm.VEq

/-! ## The S2GB opening on a list of claims -/

namespace Lvm.VEq

open RecursionFast Lvm DM LeanVM.Parameters LeanVM.Protocol LeanVM.Protocol.Compile
open Lvm.TypedV Lvm.Typed
open LeanVM.Protocol.Verifier (WhirStateT WhirConfig verifyStackedJ)
open LeanVM.Protocol.Whir.Sound (cfgMain23Jq cfgMain24G)

/-- **`verifyStackedOpening` at S2GB** (the claims batched, then `verifyWhirFB`). -/
def verifyStackedOpeningB (p : Params) (levels : List Level) (stackLog : Nat) (claims : List Lvm.StackClaim)
    (direct : Bool) (g : Nat) (ood : Bool) : DM Unit := do
  let scales := Lvm.powers (← DM.sampleE) claims.length
  Lvm.verifyWhirFB p levels stackLog (Lvm.dot scales (claims.map (·.2)))
    (fun point => Lvm.dot scales (claims.map fun c => c.1 point)) direct g ood

/-- **`dOpenF` at S2GB.** -/
def dOpenFB (p : Params) (s : Bool) (pin : Lvm.BlockClaim) (claims : List (Lvm.Com × Lvm.BlockClaim × FE)) :
    DM Unit := do
  require (claims.all (·.1 == .main))
  let cm := (claims.filter (·.1 == .main)).map (·.2)
  verifyStackedOpeningB p p.mainLevels p.nuMain
    ((pin.weight, pin.value) :: if s then cm.map fun e => onStackZBN p.nuMain e.1 e.2 else cm.map (·.1.onStack))
    false p.grind p.mainOod

theorem verifyStackedOpeningGB_eq (p : Params) (levels : List Level) (stackLog : Nat) (gs : List Lvm.SGroup)
    (direct : Bool) (g : Nat) (ood : Bool) :
    Lvm.verifyStackedOpeningGB p levels stackLog gs direct g ood =
      verifyStackedOpeningB p levels stackLog (gs.flatMap (·.flat)) direct g ood := by
  unfold Lvm.verifyStackedOpeningGB verifyStackedOpeningB
  simp only [Lvm.flatMap_wts]

theorem monoD_verifyStackedB (p : Params) (levels : List Level) (stackLog : ℕ) (claims : List Lvm.StackClaim)
    (direct : Bool) (g : ℕ) (ood : Bool) : MonoD (verifyStackedOpeningB p levels stackLog claims direct g ood) :=
  monoD_sampleE.bind fun _ ↦ monoD_verifyWhirFB _ _ _ _ _ _ _ _

theorem monoD_dOpenFB (p : Params) (s : Bool) (pin : Lvm.BlockClaim) (claims : List (Lvm.Com × Lvm.BlockClaim × FE)) :
    MonoD (dOpenFB p s pin claims) :=
  (MonoD.require _).bind fun _ ↦ monoD_verifyStackedB _ _ _ _ _ _ _

section RefB

variable {cap : ℕ → ℕ → ℕ} {occ : ℕ → ℕ → ℕ} {shp : ℕ → ℕ × ℕ} {pth hq : ℕ → ℕ} {sig : ByteArray}
  {capL : ℕ → ℕ → ℕ}

/-- **A stacked S2GB opening with OOD samples** (`ref_verifyStackedJ`'s twin). -/
theorem ref_verifyStackedJB (p : Params) (levels : List Level) (cfg : WhirConfig) (stackLog g : ℕ) (ood : Bool)
    (claims : List Lvm.StackClaim) (cl : List VStackClaim) (h : List.Forall₂ SCRel claims cl)
    (hood' : ood = true) (hood : cfg.ood = true) (hμ : cfg.μ = stackLog)
    (hper : cfg.per = positionsPerAnswer) (hdir : cfg.direct = false) (hg : cfg.grind = g)
    (hc : LevelsCorrB p capL cap occ shp pth hq stackLog cfg.c₀ cfg.n₀ 0 0 levels cfg.levels) :
    RefAtB cap occ shp pth hq sig (verifyStackedOpeningB p levels stackLog claims false g ood)
      (verifyStackedJ cfg cl) (fun _ _ ↦ True) := by
  subst hood'
  refine RefAtB.bind (fun _ ↦ monoD_verifyWhirFB _ _ _ _ _ _ _ _) ref_sampleEB ?_
  rintro c _ rfl
  have hlen : cl.length = claims.length := h.length_eq.symm
  rw [hlen]
  refine ref_verifyWhirJB p levels cfg stackLog g _ _ _ _ (fun xs ↦ ?_) ?_ hood hμ hper hdir hg hc
  · rw [toExt3_dot, map_powers, List.map_map]
    congr 1
    exact map_eq_of_forall₂W h fun a b hab ↦ hab.2 xs
  · rw [toExt3_dot, map_powers, List.map_map]
    congr 1
    exact map_eq_of_forall₂W h fun a b hab ↦ hab.1

/-- **The opening of a stage at `C_main` on the S2GB stream** (`ref_dOpenFO`'s twin). -/
theorem ref_dOpenFOB (p : Params) (hnu : p.nuMain = CMain.nu20)
    (hg : (cfgMain23Jq 1).grind = p.grind) (hood : p.mainOod = true)
    (hc : LevelsCorrB p capL cap occ shp pth hq 23 0 1 0 0 p.mainLevels (cfgMain23Jq 1).levels)
    (pin : Lvm.BlockClaim) (pc : VStackClaim) (hpc : SCRel (pin.weight, pin.value) pc) (s : Bool)
    (claims : List (Lvm.Com × Lvm.BlockClaim × FE)) (cl : List VStackClaim)
    (h : claims.all (·.1 == .main) = true →
      List.Forall₂ SCRel (Shape.onStackZsF s ((claims.filter (·.1 == .main)).map (·.2))) cl) :
    RefAtB cap occ shp pth hq sig (dOpenFB p s pin claims)
      (verifyStackedJ (cfgMain23Jq 1) (pc :: cl)) (fun _ _ ↦ True) := by
  unfold dOpenFB
  refine RefAtB.require_left (fun _ ↦ monoD_verifyStackedB _ _ _ _ _ _ _) fun hall ↦ ?_
  have h' := h hall
  have e : (if s then ((claims.filter (·.1 == .main)).map (·.2)).map fun e ↦ onStackZBN p.nuMain e.1 e.2
      else ((claims.filter (·.1 == .main)).map (·.2)).map (·.1.onStack)) =
      Shape.onStackZsF s ((claims.filter (·.1 == .main)).map (·.2)) := by
    rw [hnu]; unfold Shape.onStackZsF; rfl
  dsimp only
  rw [e, hnu]
  exact ref_verifyStackedJB p p.mainLevels (cfgMain23Jq 1) 23 _ _ _ _ (.cons hpc h') hood rfl rfl rfl rfl hg hc

end RefB

/-! ## The lift to read widths on the S2GB stream -/

section LiftB

variable {cap : ℕ → ℕ → ℕ} {occ : ℕ → ℕ → ℕ} {shp : ℕ → ℕ × ℕ} {pth hq : ℕ → ℕ} {rw : ℕ → ℕ} {sig : ByteArray}
  {cap' : ℕ → ℕ → ℕ} {shp' : ℕ → ℕ × ℕ} {idx : Ref → ℕ}

/-- **`ivpW_of_fol`'s twin on the S2GB stream.** -/
theorem ivpWB_of_fol {α : Type} : ∀ (as : List Atom) (P : VerifierProgram α) (pp : List ℕ)
    (Qf : α → List ℕ → Prop) (s : RS) (i : ℕ) (a : α),
    Fol cap' shp' idx P as pp Qf → WAt rw i (widthsA as) → (∀ x ∈ widthsA as, x = 24) →
    (ivpB cap occ shp pth hq P sig s).1 = some a →
    ivpWB cap occ shp pth hq rw P sig s i = (some a, (ivpB cap occ shp pth hq P sig s).2, i + (widthsA as).length)
  | [], P, pp, Qf, s, i, a, hF, _, _, hv => by
    cases P with
    | ret b => simp only [ivpB, Option.some.injEq] at hv; subst hv; rfl
    | fail => simp [ivpB] at hv
    | _ => exact hF.elim
  | .rd :: as, P, pp, Qf, s, i, a, hF, hw, h24, hv => by
    cases P with
    | read k =>
      obtain ⟨hw0, hw'⟩ := WAt.cons.mp hw
      have := ivpWB_of_fol as _ pp Qf _ (i + 1) a (hF _) hw' (fun x hx ↦ h24 x (List.mem_cons_of_mem _ hx)) hv
      simp only [ivpWB, ivpB, hw0] at this ⊢
      rw [this]; congr 2; simp only [widthsA, List.length_cons]; omega
    | fail => simp [ivpB] at hv
    | _ => exact hF.elim
  | .rdw w :: as, P, pp, Qf, s, i, a, hF, hw, h24, hv => by
    cases P with
    | read k =>
      obtain ⟨hw0, hw'⟩ := WAt.cons.mp hw
      have hw24 : rw i = 24 := hw0.trans (h24 w List.mem_cons_self)
      have := ivpWB_of_fol as _ pp Qf _ (i + 1) a (hF _) hw' (fun x hx ↦ h24 x (List.mem_cons_of_mem _ hx)) hv
      simp only [ivpWB, ivpB, hw24] at this ⊢
      rw [this]; congr 2; simp only [widthsA, List.length_cons]; omega
    | fail => simp [ivpB] at hv
    | _ => exact hF.elim
  | .sm :: as, P, pp, Qf, s, i, a, hF, hw, h24, hv => by
    cases P with
    | sample k =>
      simp only [ivpWB, ivpB] at hv ⊢
      exact ivpWB_of_fol as _ pp Qf _ i a (hF _) hw h24 hv
    | fail => simp [ivpB] at hv
    | _ => exact hF.elim
  | .ps h n :: as, P, pp, Qf, s, i, a, hF, hw, h24, hv => by
    cases P with
    | sample k =>
      simp only [ivpWB, ivpB] at hv ⊢
      exact ivpWB_of_fol as _ _ Qf _ i a (hF _) hw h24 hv
    | fail => simp [ivpB] at hv
    | _ => exact hF.elim
  | .pclr :: as, P, pp, Qf, s, i, a, hF, hw, h24, hv => by
    rw [fol_pclr] at hF
    exact ivpWB_of_fol as P [] Qf s i a hF hw h24 hv
  | .cap c r :: as, P, pp, Qf, s, i, a, hF, hw, h24, hv => by
    cases P with
    | commit ht w k =>
      simp only [ivpWB, ivpB] at hv ⊢
      exact ivpWB_of_fol as _ pp Qf _ i a hF.2.2 hw h24 hv
    | fail => simp [ivpB] at hv
    | _ => exact hF.elim
  | .op r :: as, P, pp, Qf, s, i, a, hF, hw, h24, hv => by
    cases P with
    | query i' ps k =>
      simp only [ivpWB, ivpB] at hv ⊢
      exact ivpWB_of_fol as _ pp Qf _ i a (hF.2.2 _) hw h24 hv
    | fail => simp [ivpB] at hv
    | _ => exact hF.elim

/-- **A 24-byte S2GB refinement is one with read widths** (`RefAtP.toPW`'s twin). -/
theorem RefAtB.toPWB {α β : Type} {d : DM β} {P : VerifierProgram α} {R : β → α → Prop}
    {as : List Atom} {Qf : α → List ℕ → Prop} {i : ℕ} (h : RefAtB cap occ shp pth hq sig d P R)
    (hF : ∀ pp, Fol cap' shp' idx P as pp Qf) (hw : WAt rw i (widthsA as)) (h24 : ∀ x ∈ widthsA as, x = 24)
    (Q : β → Prop) : RefAtPWB cap occ shp pth hq rw sig i d P R Q (i + (widthsA as).length) := by
  intro s hok _
  obtain ⟨a, h1, h2, h3, h4⟩ := h s hok
  have e := ivpWB_of_fol (cap := cap) (occ := occ) (shp := shp) (pth := pth) (hq := hq) (rw := rw) (sig := sig)
    as P [] Qf s i a (hF []) hw h24 h1
  rw [e]
  exact ⟨a, rfl, h2, h3, rfl, h4⟩

/-- **With no opening, the S2GB stream reads as the stream** (a program that follows atoms with no `op`). -/
theorem ivpWB_of_noOp {α : Type} : ∀ (as : List Atom) (P : VerifierProgram α) (pp : List ℕ)
    (Qf : α → List ℕ → Prop) (s : RS) (i : ℕ),
    Fol cap' shp' idx P as pp Qf → (∀ r, Atom.op r ∉ as) →
    ivpWB cap occ shp pth hq rw P sig s i = ivpW cap occ shp rw P sig s i
  | [], P, pp, Qf, s, i, hF, _ => by
    cases P with
    | ret b => rfl
    | fail => rfl
    | _ => exact hF.elim
  | .rd :: as, P, pp, Qf, s, i, hF, hn => by
    cases P with
    | read k =>
      simp only [ivpWB, ivpW]
      exact ivpWB_of_noOp as _ pp Qf _ _ (hF _) fun r h ↦ hn r (List.mem_cons_of_mem _ h)
    | fail => rfl
    | _ => exact hF.elim
  | .rdw w :: as, P, pp, Qf, s, i, hF, hn => by
    cases P with
    | read k =>
      simp only [ivpWB, ivpW]
      exact ivpWB_of_noOp as _ pp Qf _ _ (hF _) fun r h ↦ hn r (List.mem_cons_of_mem _ h)
    | fail => rfl
    | _ => exact hF.elim
  | .sm :: as, P, pp, Qf, s, i, hF, hn => by
    cases P with
    | sample k =>
      simp only [ivpWB, ivpW]
      exact ivpWB_of_noOp as _ pp Qf _ _ (hF _) fun r h ↦ hn r (List.mem_cons_of_mem _ h)
    | fail => rfl
    | _ => exact hF.elim
  | .ps h n :: as, P, pp, Qf, s, i, hF, hn => by
    cases P with
    | sample k =>
      simp only [ivpWB, ivpW]
      exact ivpWB_of_noOp as _ _ Qf _ _ (hF _) fun r h ↦ hn r (List.mem_cons_of_mem _ h)
    | fail => rfl
    | _ => exact hF.elim
  | .pclr :: as, P, pp, Qf, s, i, hF, hn => by
    rw [fol_pclr] at hF
    exact ivpWB_of_noOp as P [] Qf s i hF fun r h ↦ hn r (List.mem_cons_of_mem _ h)
  | .cap c r :: as, P, pp, Qf, s, i, hF, hn => by
    cases P with
    | commit ht w k =>
      simp only [ivpWB, ivpW]
      exact ivpWB_of_noOp as _ pp Qf _ _ hF.2.2 fun r h ↦ hn r (List.mem_cons_of_mem _ h)
    | fail => rfl
    | _ => exact hF.elim
  | .op r :: as, P, pp, Qf, s, i, hF, hn => absurd List.mem_cons_self (hn r)

/-- **A width-aware refinement of a program with no opening holds on the S2GB stream.** -/
theorem RefAtPW.toB {α β : Type} {i j : ℕ} {d : DM β} {P : VerifierProgram α} {R : β → α → Prop} {Q : β → Prop}
    {as : List Atom} {Qf : α → List ℕ → Prop} (h : RefAtPW cap occ shp rw sig i d P R Q j)
    (hF : Fol cap' shp' idx P as [] Qf) (hn : ∀ r, Atom.op r ∉ as) :
    RefAtPWB cap occ shp pth hq rw sig i d P R Q j := by
  intro s hok hq'
  rw [ivpWB_of_noOp as P [] Qf s i hF hn]
  exact h s hok hq'

end LiftB

end Lvm.VEq

namespace Lvm.VEq
open RecursionFast Lvm DM LeanVM.Parameters LeanVM.Protocol LeanVM.Protocol.Compile
open Lvm.E2U Lvm.E2T Lvm.E2S Lvm.ASM Lvm.E2V
open LeanVM.Protocol.Whir.Sound (cfgMain23Jq cfgMain24G)
/-! ## `P_S` at S2GB follows the schedule -/

section FolB
variable {cap : ℕ → ℕ → ℕ} {shp : ℕ → ℕ × ℕ} {idx : Ref → ℕ} (p : Params)

/-- **The mini-bus at depth `d`** against `miniBusI` (`folP_miniBusLProg` at `p.busDepth = d`). -/
theorem folP_miniBusLProgB (tabs : List Lvm.M3.Tab) (d : ℕ) (hl : p.leafdecReads = 1) (hd : p.busDepth = d) :
    FolP cap shp idx (Lvm.E2L.miniBusLProg tabs d) (atomsOf p (miniBusI p)) fun _ ↦ True := by
  have hb := folP_lvmBusProg (cap := cap) (shp := shp) (idx := idx) p hl
  rw [hd] at hb
  unfold Lvm.E2L.miniBusLProg
  exact hb.bind_ret fun _ _ ↦ trivial

/-- **The typed phases at depth `d`** against `typedIL` (`folP_typedProgL`'s twin). -/
theorem folP_typedProgLB (d : ℕ) (Ti : Typed.TInst) (pub : Pub) (hacc : p.accV = Typed.phiVarsT)
    (hl : p.leafdecReads = 1) (hd : p.busDepth = d) :
    FolP cap shp idx (typedProgLB d Ti pub) (atomsOf p (typedIL p)) fun _ ↦ True := by
  simp only [typedIL, atomsOf_append]
  unfold typedProgLB
  exact (folP_zeroProgT p).bind fun _ _ ↦ (folP_wireProgT p Ti pub _).bind fun _ _ ↦
    (folP_relayProgT p Ti _ _).bind fun _ _ ↦ (folP_accProgT p hacc _ _ _ _ _ _ _).bind fun _ _ ↦
    (folP_miniBusLProgB p Ti.mbT d hl hd).bind_ret fun _ _ ↦ trivial

end FolB

section MidB
variable {cap : ℕ → ℕ → ℕ} {shp : ℕ → ℕ × ℕ} {idx : Ref → ℕ}

/-- **S2GB's middle phases** (`midGB Ti`) against the typed and the front items at `P20B`. -/
theorem folP_midGB (Ti : Typed.TInst) (x : List UInt8) :
    FolP cap shp idx (Lvm.E2S.midGB Ti x) (atomsOf P20B (typedIL P20B ++ (tapeU P20B ++ wireU P20B)))
      fun _ ↦ True := by
  rw [atomsOf_append, atomsOf_append]
  unfold Lvm.E2S.midGB
  exact (folP_typedProgLB _ 13 Ti _ rfl rfl rfl).bind fun _ _ ↦
    (folP_tapeProgL _ _ rfl _ _).bind_ret fun _ _ ↦ trivial

theorem atomsOf_pinIB : atomsOf P20B (pinI P20B) = List.replicate CMain.nu20 .sm ++ [.rd] := by
  rw [pinI, atomsOf_append, atomsOf_smp, atomsOf_rd]
  rfl

/-- **S2GB's pinned middle phases follow `midItemsL`** at `P20B`, for every relocation. -/
theorem folP_midPB (reloc : List UInt8 → VStackClaim → VStackClaim) (Ti : Typed.TInst) (x : List UInt8) :
    FolP cap shp idx (Lvm.E2F.midP (Lvm.ASM.midMk 4 reloc (Lvm.E2S.midGB Ti)) x) (atomsOf P20B (midItemsL P20B))
      fun _ ↦ True := by
  rw [midItemsL, atomsOf_append, atomsOf_pinIB]
  exact folP_midP _ x _ (folP_midMk 4 reloc _ x _ (folP_midGB Ti x))

end MidB

/-- **S2GB's atoms are `P20`'s** (`P20B`'s levels are `P20S`'s). -/
theorem atomsOf_B (its : List Item) : atomsOf P20B its = atomsOf P20 its :=
  atomsOf_congrL P20B P20 (fun r ↦ by
    obtain ⟨c, lv⟩ := r
    cases c
    · exact withRow0_getD P20.mainLevels 46 lv
    · exact ⟨rfl, rfl⟩) its

theorem atomsOf_scheduleB : atomsOf P20B (schedule P20B) =
    [.cap (P20.level ⟨.main, 0⟩).cap ⟨.main, 0⟩] ++
      (atomsOf P20B (midItemsL P20B) ++ (atomsOf P20 (openMainI P20) ++ [])) := by
  rw [scheduleL_eq _ rfl rfl, atomsOf_append, atomsOf_append, atomsOf_append, atomsOf_nil,
    atomsOf_B (openMainI P20B), atomsOf_B (commitI P20B), show openMainI P20B = openMainI P20 from rfl,
    show commitI P20B = commitI P20 from rfl, atomsOf_commitI]

end Lvm.VEq

/-! ## The typed phases with the mini-bus at depth 13 -/

namespace Lvm.E2T

open Lvm DM LeanVM.Parameters LeanVM.Protocol.Compile
open Lvm.VEq
open Lvm.TypedV (TNat fitsMiniB)
open Lvm.Typed (xVars yVars selBitsT phiVarsT relayRounds Lay)
open Lvm.M3 (Tab sumcheckTabs)
open Lvm.FE2 (toE2)
open Lvm.E2L (dMiniL dTypedLG typedClaimsL miniBusLProg)

/-- The mini-bus's reads at S2GB (24 B each): its bus phase's at depth 13 (`miniBusI P20B`). -/
def nMiniRdLB : ℕ := atomReads (atomsOf P20B (miniBusI P20B))

/-- **The typed phase's widths at S2GB** (`wTypedL` with the depth-13 mini-bus). -/
def wTypedLB : List ℕ := wZeroT ++ (wWireT ++ (wRelayT ++ (wAccT ++ List.replicate nMiniRdLB 24)))

section Ref

variable {cap : ℕ → ℕ → ℕ} {occ : ℕ → ℕ → ℕ} {shp : ℕ → ℕ × ℕ} {rw : ℕ → ℕ} {sig : ByteArray}

/-- **The mini-bus at depth `d`** refines `miniBusLProg tabs d` (`ref_dMiniL` at `p.busDepth = d`). -/
theorem ref_dMiniLB (p : Params) (m : M3) (tabs : List Tab) (pub : Pub) (d : ℕ)
    (hm : m.busFinal = (M3.real p fun _ ↦ tabs).busFinal) (hsc : sumcheckTabs tabs = tabs)
    (hl : p.leafdecReads = 1) (hd : p.busDepth = d) :
    RefAt cap occ shp sig (dMiniL p m pub) (miniBusLProg tabs d)
      fun pb cl ↦ ∃ b, BusRel tabs pb b ∧ cl = Lvm.M3.mbClaimsL CMain.nu20 tabs b := by
  have e : dMiniL p m pub = dBus p (M3.real p fun _ ↦ tabs) pub >>= fun r ↦ Pure.pure r := by
    rw [bind_pure]
    unfold dMiniL dBus
    simp only [hm]
  have h := ref_dBus (cap := cap) (occ := occ) (shp := shp) (sig := sig) p (fun _ ↦ tabs) pub hl
  rw [hsc, hd] at h
  rw [e]
  unfold miniBusLProg
  exact RefAt.bind (fun _ ↦ MonoD.pure _) h fun pb b hb ↦ RefAt.pure ⟨b, hb, rfl⟩

/-- Every mini-bus table of an S2GB record is a sumcheck table (`TRefHyp.sc_eq`'s twin). -/
theorem TRefHypTB.sc_eqB {N : TNatT} {Q : Lvm.Loop.Program} {lay : Lay} (H : TRefHypTB N Q lay) :
    sumcheckTabs N.mbT = N.mbT := by
  unfold sumcheckTabs
  rw [List.filter_eq_self]
  intro t ht
  rcases H.sc t ht with h | h <;> simp [h]

/-- **The typed phases at S2GB refine `typedProgLB 13`** (`ref_dTypedLO`'s twin for a record `pT` with the mini-bus at
depth 13). -/
theorem ref_dTypedLOB (p pT : Params) (N : TNatT) (Q : Lvm.Loop.Program) (lay : Lay) (H : TRefHypTB N Q lay) (m : M3)
    (hm : m.busFinal = (M3.real pT fun _ ↦ N.mbT).busFinal) (hl : pT.leafdecReads = 1) (hbus : pT.busDepth = 13)
    (pub : Pub) (hacc : pub.accIn.pt.length = phiVarsT) {i : ℕ} (hw : WAt rw i wTypedLB) :
    RefAtWP cap occ shp rw sig i (dTypedLG pT N m pub (typedClaimsND N p))
      (Lvm.E2S.typedProgLB 13 (N.inst Q lay) pub) (TRelTL p N Q lay)
      (fun r ↦ N.phiT (r.1.pt.map Lvm.e2OfFE) = Lvm.e2OfFE r.1.y) (i + wTypedLB.length) := by
  simp only [wTypedLB, WAt.append] at hw
  obtain ⟨hwz, hww, hwr, hwa, hwm⟩ := hw
  unfold dTypedLG Lvm.E2S.typedProgLB
  refine RefAtWP.bind (Q := fun _ ↦ True) (fun _ ↦ (E2T.monoD_dWiringT _ _ _).bind fun _ ↦
    (E2T.monoD_dRelayT2 _ _ _).bind fun _ ↦ (E2T.monoD_dAccT _ _ _).bind fun _ ↦
      (monoD_dMiniL _ _ _).bind fun _ ↦ MonoD.pure _) (RefAtW.toP (refW_dZeroT hwz) _)
    (fun _ _ _ ↦ trivial) ?_
  rintro z _ ⟨rfl, hz, -⟩ -
  refine RefAtWP.bind (Q := fun _ ↦ True) (fun _ ↦ (E2T.monoD_dRelayT2 _ _ _).bind fun _ ↦
    (E2T.monoD_dAccT _ _ _).bind fun _ ↦ (monoD_dMiniL _ _ _).bind fun _ ↦ MonoD.pure _)
    (RefAtW.toP (refW_dWiringT N Q lay H.ok H.hlay pub z.2 hww) _) (fun _ _ _ ↦ trivial) ?_
  rintro w _ ⟨rfl, hry, -, hrv⟩ -
  have hR := refW_dRelayT2 (cap := cap) (occ := occ) (shp := shp) (rw := rw) (sig := sig) N Q lay H.ok H.hlay w.1
    hry (w.2.2.getD 1 0) hwr
  rw [kv_toE2_getD] at hR
  refine RefAtWP.bind (Q := fun _ ↦ True) (fun _ ↦ (E2T.monoD_dAccT _ _ _).bind fun _ ↦
    (monoD_dMiniL _ _ _).bind fun _ ↦ MonoD.pure _) (RefAtW.toP hR _) (fun _ _ _ ↦ trivial) ?_
  rintro r _ ⟨rfl, hrr⟩ -
  have hA := refW_dAccT (cap := cap) (occ := occ) (shp := shp) (rw := rw) (sig := sig) N Q lay H.phiT pub hacc
    (z.1 ++ w.1) w.2.1 (by rw [List.length_append, hz, hry]) hwa
  rw [List.map_append] at hA
  dsimp only
  refine RefAtWP.bind (Q := fun (a : Acc) ↦ N.phiT (a.pt.map Lvm.e2OfFE) = Lvm.e2OfFE a.y)
    (fun _ ↦ (monoD_dMiniL _ _ _).bind fun _ ↦ MonoD.pure _) hA
    (fun _ _ h ↦ by rw [runD_bind_pure_fst] at h; exact h) ?_
  intro acc _ _ _
  have hM := ref_dMiniLB (cap := cap) (occ := occ) (shp := shp) (sig := sig) pT m N.mbT pub 13 hm H.sc_eqB hl
    hbus
  have hF := folP_miniBusLProgB (cap := cap) (shp := shp) (idx := fun _ ↦ 0) P20B N.mbT 13 rfl rfl
  have hW := RefAt.toW (rw := rw) hM hF hwm
  refine RefAtWP.bind (Q := fun _ ↦ True) (fun _ ↦ MonoD.pure _) (RefAtW.toP hW _) (fun _ _ _ ↦ trivial) ?_
  rintro pb cl ⟨b, hb, rfl⟩ -
  refine RefAtWP.idx (RefAtW.toP (RefAtW.pure ⟨w.1, w.2.2, r.1, r.2, b, rfl, hry, hrv, hrr, hb, rfl⟩) _) ?_
  simp only [wTypedLB, List.length_append, List.length_replicate, nMiniRdLB]
  (clear * - i N Q lay pub z w r; omega)

end Ref

end Lvm.E2T

/-! ## The decision at S2GB -/

namespace Lvm.VEq

open RecursionFast Lvm DM LeanVM.Parameters LeanVM.Protocol LeanVM.Protocol.Compile Finset
open Lvm.FE2 (toE2)
open Lvm.E2U Lvm.E2T Lvm.E2S Lvm.ASM
open Lvm.E2V (selPtF)
open Lvm.E2L (linClaims linGroup dOpenFFL mbSumsN typedClaimsL dTypedLG)
open Lvm.CT (occOfU)
open LeanVM.Protocol.Whir.Sound (cfgMain23Jq cfgMain24G)

section WB

variable {cap : ℕ → ℕ → ℕ} {occ : ℕ → ℕ → ℕ} {shp : ℕ → ℕ × ℕ} {pth hq : ℕ → ℕ} {rw : ℕ → ℕ} {sig : ByteArray}

theorem ivpWB_congr {α : Type} (P : VerifierProgram α) (sig : ByteArray) {s s' : RS} (i : ℕ)
    (he : s.ent = s'.ent) (hm : s.msg = s'.msg) :
    (ivpWB cap occ shp pth hq rw P sig s i).1 = (ivpWB cap occ shp pth hq rw P sig s' i).1 ∧
      (ivpWB cap occ shp pth hq rw P sig s i).2.1.ent = (ivpWB cap occ shp pth hq rw P sig s' i).2.1.ent ∧
      (ivpWB cap occ shp pth hq rw P sig s i).2.1.msg = (ivpWB cap occ shp pth hq rw P sig s' i).2.1.msg ∧
      (ivpWB cap occ shp pth hq rw P sig s i).2.2 = (ivpWB cap occ shp pth hq rw P sig s' i).2.2 := by
  induction P generalizing s s' i with
  | ret a => exact ⟨rfl, he, hm, rfl⟩
  | fail => exact ⟨rfl, he, hm, rfl⟩
  | grind b k ih => exact ⟨rfl, he, hm, rfl⟩
  | read k ih =>
    simp only [ivpWB, he, hm]
    exact ih _ _ rfl rfl
  | sample k ih =>
    simp only [ivpWB, he, hm]
    exact ih _ _ rfl rfl
  | commit ht w k ih =>
    simp only [ivpWB]
    exact ih _ he (by simp [hm])
  | query i' ps k ih =>
    simp only [ivpWB, he]
    exact ih _ _ rfl hm

theorem ivpWB_bind {α β : Type} (P : VerifierProgram α) (f : α → VerifierProgram β) (sig : ByteArray)
    (s : RS) (i : ℕ) : ivpWB cap occ shp pth hq rw (P.bind f) sig s i =
      match ivpWB cap occ shp pth hq rw P sig s i with
      | (some a, s', i') => ivpWB cap occ shp pth hq rw (f a) sig s' i'
      | (none, s', i') => (none, s', i') := by
  induction P generalizing s i with
  | ret a => rfl
  | fail => rfl
  | grind b k ih => rfl
  | read k ih => exact ih _ _ _
  | sample k ih => exact ih _ _ _
  | commit ht w k ih => exact ih _ _
  | query i' ps k ih => exact ih _ _ _

theorem RefAtPWB.bind {α α' β β' : Type} {i j k : ℕ} {d : DM β} {d' : β → DM β'} {P : VerifierProgram α}
    {P' : α → VerifierProgram α'} {R : β → α → Prop} {R' : β' → α' → Prop} {Q : β → Prop}
    {Q' : β' → Prop} (hm : ∀ b, MonoD (d' b)) (h : RefAtPWB cap occ shp pth hq rw sig i d P R Q j)
    (hQ : ∀ b s, Q' (runD (d' b) sig s).1 → Q b)
    (h' : ∀ b a, R b a → Q b → RefAtPWB cap occ shp pth hq rw sig j (d' b) (P' a) R' Q' k) :
    RefAtPWB cap occ shp pth hq rw sig i (d >>= d') (P.bind P') R' Q' k := by
  intro s hok hq'
  have hsplit : runD (d >>= d') sig s = runD (d' (runD d sig s).1) sig (runD d sig s).2 := rfl
  rw [hsplit] at hok hq' ⊢
  have hq1 := hQ _ _ hq'
  obtain ⟨a, ha, he, hmsg, hj, hR⟩ := h s (hm _ sig _ hok) hq1
  obtain ⟨a', ha', he', hm', hk, hR'⟩ := h' _ _ hR hq1 _ hok hq'
  refine ⟨a', ?_⟩
  rw [ivpWB_bind]
  rcases hP : ivpWB cap occ shp pth hq rw P sig s i with ⟨_ | a₀, s₂, i₂⟩
  · rw [hP] at ha; exact absurd ha (by simp)
  · rw [hP] at ha he hmsg hj
    simp only [Option.some.injEq] at ha
    subst ha
    simp only at hj
    subst hj
    obtain ⟨c1, c2, c3, c4⟩ := ivpWB_congr (cap := cap) (occ := occ) (shp := shp) (pth := pth) (hq := hq)
      (rw := rw) (P' a₀) sig i₂ he hmsg
    exact ⟨c1.trans ha', c2.trans he', c3.trans hm', c4.trans hk, hR'⟩

theorem RefAtPWB.read_left {α β : Type} {i j : ℕ} {d : ByteArray → DM β} {P : VerifierProgram α}
    {R : β → α → Prop} {Q : β → Prop} (h : RefAtPWB cap occ shp pth hq rw sig i (d sig) P R Q j) :
    RefAtPWB cap occ shp pth hq rw sig i (MonadReader.read >>= d) P R Q j :=
  fun s hok hq' ↦ h s hok hq'

/-- `C_main`'s sent cap on the S2GB stream. -/
theorem refWB_skip {i ht w n : ℕ} (h : n = 32 * 2 ^ cap ht w) (Q : Unit → Prop) :
    RefAtPWB cap occ shp pth hq rw sig i (DM.skip n) (VerifierProgram.readCommitment ht w) (fun _ _ ↦ True) Q i := by
  intro s _ _
  subst h
  exact ⟨(), rfl, rfl, rfl, rfl, trivial⟩

theorem refWB_pure {α β : Type} {i : ℕ} {b : β} {a : α} {R : β → α → Prop} (h : R b a) (Q : β → Prop) :
    RefAtPWB cap occ shp pth hq rw sig i (Pure.pure b : DM β) (VerifierProgram.ret a) R Q i :=
  fun _ _ _ ↦ ⟨a, rfl, rfl, rfl, rfl, h⟩

end WB

/-! ### Facts at `P20B` -/

/-- The items with no opening. -/
def noOpI (its : List Item) : Bool := its.all fun it ↦ match it with | .opening _ => false | _ => true

theorem not_op_posAtoms (h : ℕ) : ∀ (n rem : ℕ) (r : Ref), Atom.op r ∉ posAtoms h n rem
  | 0, _, _ => List.not_mem_nil
  | n + 1, rem, r => by
    rw [posAtoms]
    exact fun hm ↦ (List.mem_cons.1 hm).elim (fun e ↦ Atom.noConfusion e) (not_op_posAtoms h n _ r)

theorem not_op_atomsOf (p : Params) {its : List Item} (h : noOpI its = true) (r : Ref) :
    Atom.op r ∉ atomsOf p its := by
  intro hm
  obtain ⟨it, hit, hm⟩ := List.mem_flatMap.1 hm
  have h1 := List.all_eq_true.1 h it hit
  cases it with
  | read m => exact absurd (List.eq_of_mem_replicate hm) (fun e ↦ Atom.noConfusion e)
  | readW m w => exact absurd (List.eq_of_mem_replicate hm) (fun e ↦ Atom.noConfusion e)
  | cap c r' => exact absurd (List.mem_singleton.1 hm) (fun e ↦ Atom.noConfusion e)
  | sample => exact absurd (List.mem_singleton.1 hm) (fun e ↦ Atom.noConfusion e)
  | positions r' =>
    exact (List.mem_cons.1 hm).elim (fun e ↦ Atom.noConfusion e) (not_op_posAtoms _ _ _ r)
  | opening r' => exact Bool.false_ne_true h1

set_option maxRecDepth 100000 in
/-- Proof help: S2GB's typed items have no opening. -/
theorem noOp_typedB : noOpI (typedIL P20B) = true := by decide +kernel

theorem noOpI_append (a b : List Item) : noOpI (a ++ b) = (noOpI a && noOpI b) := List.all_append

theorem noOpI_flatten (l : List (List Item)) (h : ∀ x ∈ l, noOpI x = true) : noOpI l.flatten = true := by
  simp only [noOpI, List.all_eq_true, List.mem_flatten] at h ⊢
  rintro x ⟨y, hy, hx⟩
  exact h y hy x hx

theorem noOpI_rep (n : ℕ) (x : List Item) (h : noOpI x = true) : noOpI (List.replicate n x).flatten = true :=
  noOpI_flatten _ fun y hy => (List.eq_of_mem_replicate hy) ▸ h

theorem noOpI_rdE2 (m : ℕ) : noOpI (rdE2 m) = true := by unfold rdE2; split <;> rfl

theorem noOpI_gsmpN (n : ℕ) : noOpI (gsmpN n) = true := noOpI_rep _ _ rfl

theorem noOpI_smp (n : ℕ) : noOpI (smp n) = true := by
  simp only [noOpI, smp, List.all_eq_true]
  intro x hx
  rw [List.eq_of_mem_replicate hx]

theorem noOpI_sumE2 (r d : ℕ) : noOpI (sumcheckE2I r d) = true :=
  noOpI_rep _ _ (by rw [noOpI_append, noOpI_rdE2]; rfl)

theorem noOpI_layer (n : ℕ) : noOpI (keccakLayerE2I n) = true := by
  unfold keccakLayerE2I
  refine noOpI_flatten _ fun x hx => ?_
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    first | exact noOpI_rdE2 _ | exact noOpI_sumE2 _ _ | rfl

/-- The tape and wire items have no opening, at every parameter set (proof help, no evaluation). -/
theorem noOp_tapeG (p : Params) : noOpI (tapeU p ++ wireU p) = true := by
  rw [noOpI_append, tapeU, wireU]
  refine Bool.and_eq_true_iff.2 ⟨noOpI_flatten _ fun x hx => ?_, noOpI_flatten _ fun x hx => ?_⟩
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl
    · rfl
    · exact noOpI_gsmpN _
    · exact noOpI_rdE2 _
    · rfl
    · rw [tapeLayersE2I, noOpI_append, noOpI_gsmpN, noOpI_rep _ _ (noOpI_layer _)]; rfl
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
    have hs : ∀ r, noOpI (slotRedI r) = true := fun r => by
      rw [slotRedI]
      refine noOpI_flatten _ fun y hy => ?_
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hy
      rcases hy with rfl | rfl | rfl
      · exact noOpI_sumE2 _ _
      · exact noOpI_rdE2 _
      · exact noOpI_smp _
    rcases hx with rfl | rfl | rfl | rfl | rfl
    · exact noOpI_sumE2 _ _
    · exact noOpI_rdE2 _
    all_goals exact hs _

/-- Proof help: S2GB's tape items have no opening. -/
theorem noOp_tapeB : noOpI (tapeU P20B ++ wireU P20B) = true := noOp_tapeG P20B

/-- **`C_main`'s levels at S2GB correspond on the S2GB stream** (`corrMainU`'s twin). -/
theorem corrMainB :
    LevelsCorrB P20B capS capOfB occOfU shpS pthB hqB 23 0 1 0 0 P20B.mainLevels (cfgMain23Jq 1).levels := by
  rw [show P20B.mainLevels = P20U.mainLevels from rfl, mainLevels_P20U]
  simp only [LevelsCorrB, NextOKB, cfgMain23Jq]
  decide

theorem skip_P20B : nodeBytes * 2 ^ P20B.capSendBits 0 (P20B.level ⟨.main, 0⟩).cap = 32 * 2 ^ capOfB 19 64 := by
  decide

end Lvm.VEq

namespace Lvm.VEq

open RecursionFast Lvm DM LeanVM.Parameters LeanVM.Protocol LeanVM.Protocol.Compile Finset
open Lvm.FE2 (toE2)
open Lvm.E2U Lvm.E2T Lvm.E2S Lvm.ASM
open Lvm.E2V (selPtF)
open Lvm.E2L (linClaims linGroup dOpenFFL mbSumsN typedClaimsL dTypedLG)
open Lvm.CT (occOfU)
open LeanVM.Protocol.Whir.Sound (cfgMain23Jq cfgMain24G)

/-- **The read widths of V_S's S2GB decision**: the pin's read, the typed phases' (depth 13), the tape's, the
opening's. -/
def wDecLB (asO : List Atom) : List ℕ := [24] ++ wTypedLB ++ wTapeU ++ widthsA asO

/-- **The S2GB schedule's read widths** in V_S's decision order (`widthsA_scheduleS`'s twin). -/
theorem widthsA_scheduleB : widthsA (atomsOf P20B (schedule P20B)) = wDecLB (atomsOf P20 (openMainI P20)) := by
  have hp : widthsA (List.replicate CMain.nu20 Atom.sm) = [] := by
    generalize CMain.nu20 = n
    induction n with
    | zero => rfl
    | succ n ih => rw [List.replicate_succ]; exact ih
  have hT : widthsA (atomsOf P20B (typedIL P20B)) = wTypedLB := by
    have e : typedIL P20B = (zeroIT ++ (wiringIT ++ (relayIT ++ accIT P20B))) ++ miniBusI P20B := by
      simp only [typedIL, List.append_assoc]
    have hm : widthsA (atomsOf P20B (miniBusI P20B)) = List.replicate nMiniRdLB 24 := by
      rw [widthsA_eq_replicate _ (mem_widthsA_atomsOf _ _ (by
        simp only [miniBusI, gpI, List.flatten_cons, List.flatten_nil, List.append_nil, noWB_append, noWB_smp,
          noWB_rd, noWB_gpLayersI, Bool.and_self]))]
      rfl
    rw [e, atomsOf_append, widthsA_append, hm, widthsA_atomsOf]
    simp only [zeroIT, wiringIT, relayIT, accIT, List.flatten_cons, List.flatten_nil, List.append_nil,
      List.flatMap_append, wI_rdE2, wI_gsmpN, wI_gsmp, wI_sumcheckE2I, show sepI.flatMap itemW = [] from rfl,
      wTypedLB, wZeroT, wWireT, wRelayT, wAccT, List.append_assoc, List.nil_append]
    rfl
  have hF : widthsA (atomsOf P20B (tapeU P20B ++ wireU P20B)) = wTapeU := by
    rw [widthsA_atomsOf]
    simp only [tapeU, wireU, slotRedI, show P20B.logN = 20 from rfl, List.flatten_cons, List.flatten_nil,
      List.append_nil, List.flatMap_append, wI_rdE2, wI_gsmpN, wI_gsmp, wI_sumcheckE2I, wI_tapeLayersE2I, wI_smp,
      show sepI.flatMap itemW = [] from rfl, wTapeU, wWireU, wTapeGkr, wSlot, List.nil_append, List.append_assoc]
    rfl
  rw [atomsOf_scheduleB, midItemsL, atomsOf_append P20B (pinI _), atomsOf_append P20B (typedIL _), atomsOf_pinIB]
  simp only [widthsA_append, hp, hT, hF, List.append_nil, List.nil_append, List.append_assoc, wDecLB]
  rfl

/-- **`rwB20` is the S2GB schedule's read widths** from read `0`. -/
theorem wAt_rwB20 : WAt rwB20 0 (widthsA (atomsOf P20B (schedule P20B))) := by
  rw [← readWidthsP_eqAP]
  exact wAt_getD _ _

/-- **The pinned middle phases at S2GB as one chain** (`psS_eq`'s twin). -/
theorem psB_eq (Ti : Typed.TInst) (x : List UInt8) :
    Lvm.ASM.PSWithM (Lvm.E2F.midP (Lvm.ASM.midMk 4 relocU20 (Lvm.E2S.midGB Ti))) x =
      VerifierProgram.readCommitment 19 64 >>= fun _ ↦ Lvm.E2F.pinProg >>= fun za ↦
        Lvm.E2S.typedProgLB 13 Ti (pubXTS x) >>= fun a ↦
          tapeProgL (Lvm.E2S.contIvSB Lvm.E2S.aSP) (hdX x).s (pubX x).n >>= fun k ↦
          LeanVM.Protocol.Verifier.verifyStackedJ (cfgMain23Jq 1) (Lvm.E2F.pinClaim za ::
            Lvm.ASM.ordMk 4 ((assembleU₂ x a k).1.map (relocU20 x)) (assembleU₂ x a k).2) >>= fun _ ↦
              pure true := by
  unfold Lvm.ASM.PSWithM Lvm.E2F.midP Lvm.ASM.midMk Lvm.E2S.midGB
  rw [commitRootUd_mainT]
  simp only [bind_assoc, ret_bindM, pure_bind]

/-- **`dOpenFFLB` is `dOpenFB`** on the typed items' claims, the three claims, the front's (`dOpenFFL_eq`'s twin). -/
theorem dOpenFFLB_eq (p : Params) (s : Bool) (pin : BlockClaim) (ti : List FItem) (ζ : List FE)
    (css : List (List (FE × ℕ × ℕ))) (vs : List FE) (items : List FItem) :
    Lvm.E2L.dOpenFFLB p s pin ti ζ css vs items =
      dOpenFB p s pin (ti.flatMap FItem.flat ++ linClaims p.nuMain ζ css vs ++ items.flatMap FItem.flat) := by
  have hL := linClaims_main p.nuMain ζ css vs
  have hLf : (linClaims p.nuMain ζ css vs).filter (·.1 == .main) = linClaims p.nuMain ζ css vs :=
    List.filter_eq_self.2 fun e he ↦ by simp [hL e he]
  have hLa : (linClaims p.nuMain ζ css vs).all (·.1 == .main) = true :=
    List.all_eq_true.2 fun e he ↦ by simp [hL e he]
  have hall : ((ti ++ items).flatMap FItem.flat).all (·.1 == .main) =
      (ti.flatMap FItem.flat ++ linClaims p.nuMain ζ css vs ++ items.flatMap FItem.flat).all (·.1 == .main) := by
    simp only [List.flatMap_append, List.all_append, hLa, Bool.and_true]
  unfold Lvm.E2L.dOpenFFLB dOpenFB
  rw [hall, verifyStackedOpeningGB_eq, List.flatMap_cons, List.flatMap_append, List.flatMap_cons,
    groups_flat, groups_flat, List.filter_append, List.filter_append, hLf,
    show (linGroup s p.nuMain ζ css vs).flat = (linClaims p.nuMain ζ css vs).map fun c ↦ toStk s p.nuMain c.2 from rfl]
  cases s <;> simp only [SGroup.one, toStk, List.map_map, List.map_append, Function.comp_def, Bool.false_eq_true,
    ↓reduceIte, List.singleton_append, List.append_assoc]

/-- **`dOpenFB` sees its claims only through their stack forms** (`dOpenF_congr`'s twin). -/
theorem dOpenFB_congr (p : Params) (s : Bool) (pin : BlockClaim) {c₁ c₂ : List (Com × BlockClaim × FE)}
    (h : c₁.map (fun e => (e.1, toStk s p.nuMain e.2)) = c₂.map (fun e => (e.1, toStk s p.nuMain e.2))) :
    dOpenFB p s pin c₁ = dOpenFB p s pin c₂ := by
  have hm : c₁.map (·.1) = c₂.map (·.1) := by
    have := congrArg (List.map Prod.fst) h
    simpa only [List.map_map, Function.comp_def] using this
  have hall : ∀ c : List (Com × BlockClaim × FE), c.all (·.1 == .main) = (c.map (·.1)).all (· == .main) :=
    fun c => by rw [List.all_map]; rfl
  have hst : ∀ c : List (Com × BlockClaim × FE),
      (if s then ((c.filter (·.1 == .main)).map (·.2)).map fun e => TypedV.onStackZBN p.nuMain e.1 e.2
        else ((c.filter (·.1 == .main)).map (·.2)).map (·.1.onStack)) =
      ((c.map fun e => (e.1, toStk s p.nuMain e.2)).filter (·.1 == .main)).map (·.2) := fun c => by
    rw [List.filter_map, List.map_map, List.map_map]
    cases s <;> simp only [toStk, Function.comp_def, Bool.false_eq_true, ↓reduceIte, List.map_map]
  unfold dOpenFB
  dsimp only
  rw [hall, hall, hm, hst, hst, h]

theorem monoD_dOpenFFLB (p : Params) (s : Bool) (pin : BlockClaim) (ti : List FItem) (ζ : List FE)
    (css : List (List (FE × ℕ × ℕ))) (vs : List FE) (items : List FItem) :
    MonoD (Lvm.E2L.dOpenFFLB p s pin ti ζ css vs items) := by
  rw [dOpenFFLB_eq]
  exact monoD_dOpenFB _ _ _ _

theorem not_op_pin (r : Ref) : Atom.op r ∉ List.replicate CMain.nu20 Atom.sm ++ [Atom.rd] := by
  simp [List.mem_replicate]

theorem not_op_tapeB (r : Ref) : Atom.op r ∉ atomsOf P20B (tapeU P20B) ++ atomsOf P20B (wireU P20B) := by
  rw [← atomsOf_append]
  exact not_op_atomsOf P20B noOp_tapeB r

theorem layout0_P20B : layout0 P20B = layout0 P20U := by decide

end Lvm.VEq

namespace Lvm.VEq
open Lvm DM LeanVM.Parameters LeanVM.Protocol.Compile Finset
open Lvm.FE2 (toE2)
open Lvm.E2U Lvm.E2T
open Lvm.E2V (selPtF)
open Lvm.E2L (linClaims dOpenFFL mbSumsN typedClaimsL typedProgL midGL bL dTypedLG decideProgLG decideFLG)
open Lvm.CT (occOfU)
open LeanVM.Protocol.Whir.Sound (cfgMain23Jq cfgMain24G)

/-- The S2GB record's column facts (`TRefHyp.fits`'s last two at `P20`'s `ν`s). -/
theorem _root_.Lvm.E2T.TRefHypTB.fitsB {N : TNatT} {Q : Lvm.Loop.Program} {lay : Typed.Lay} (H : TRefHypTB N Q lay) :
    M3.colsFitB P20 N.mbT = true ∧ M3.colsHiB N.mbT = true := by
  have h := H.mini
  unfold Lvm.TypedV.fitsMiniB at h
  simp only [Bool.and_eq_true] at h
  exact ⟨h.1.1.2, h.1.2⟩

/-- **V_S's claim list at S2GL (after the pin) against `ordMk 4` of `assembleU₂`'s relocated pair** (both shapes;
`claimsU_rel`'s twin; `claimsL_rel` for an S2GB record): the typed claims as S2GU's, the three claims (`vrel_mbSums`, tails `0` under `mbLinB`), the
front's (`front_relU`). -/
theorem claimsL_relB (N : TNatT) (Q : Lvm.Loop.Program) (lay : Typed.Lay) (H : TRefHypTB N Q lay)
    (hlin : Lvm.M3.mbLinB N.mbT = true)
    (hσ : ∀ g ∈ N.toN.regs, g.src = .sigma → (layout0 P20U).s ≤ g.dst ∧ g.dst + 2 ^ g.log ≤ (layout0 P20U).s + 2 ^ 19)
    (x : List UInt8) (t : Acc × List (Com × BlockClaim × FE) × List FE × BusOut) (a : Lvm.ASM.OpenClaims)
    (hT : TRelTL P20L N Q lay t a) (tp : TapeVU) (k : TapeOutU) (hk : TapeURelW tp k) (hsh : TapeShapeU tp)
    (hall : (t.2.1 ++ (mbSumsN N.mbT (t.2.2.1, t.2.2.2)).map (fun c ↦ (Com.main, c, (0 : FE))) ++
      frontClaimsUD P20U (pubXT x) tp).all (·.1 == .main) = true) :
    List.Forall₂ SCRel (Shape.onStackZsF (Shape.small x)
        (((t.2.1 ++ (mbSumsN N.mbT (t.2.2.1, t.2.2.2)).map (fun c ↦ (Com.main, c, (0 : FE))) ++
          frontClaimsUD P20U (pubXT x) tp).filter (·.1 == .main)).map (·.2)))
      (Lvm.ASM.ordMk 4 ((assembleU₂ x a k).1.map (relocU20 x)) (assembleU₂ x a k).2) := by
  obtain ⟨ry, rv, rr, vR, b, ht1, hry, -, -, hbus, rfl⟩ := hT
  obtain ⟨hfc, hfh⟩ := H.fitsB
  have hall' : ∀ e ∈ t.2.1 ++ (mbSumsN N.mbT (t.2.2.1, t.2.2.2)).map (fun c ↦ (Com.main, c, (0 : FE))) ++
      frontClaimsUD P20U (pubXT x) tp, e.1 = .main := fun e he ↦ by
    simpa using List.all_eq_true.1 hall e he
  rw [List.filter_eq_self.2 fun e he ↦ by simp [hall' e he]]
  have hok := H.ok
  rw [nuMain_P20] at hok
  have hS : (layout0 P20U).s = CMain.sOffU20 := by rw [layout0_P20U]
  -- the typed claims
  have hrelay := vrel_splitMAt (s := Shape.small x) CMain.sOffU20 [(1, ⟨P20U.nuRec, (layout0 P20U).s⟩, rr)]
    (by simpa using offOK_relayU) vR [(1, ⟨Typed.relayRounds, 0⟩, rr.map toE2)]
    (by simp [E2V.partE, shiftS2At, hS, Lvm.FE2.toE2_one]; rfl)
    (by simp only [List.mem_singleton, forall_eq]; exact relocOKAt_relayU _) (toE2 vR) rfl
  have hsg := vrel_regND (s := Shape.small x) N Q lay P20.nuRec hok H.hlay .sigma (.inr (.inr rfl)) ry hry
    (rv.getD 2 0)
  rw [regClaimT_relocSAt N Q lay 23 P20.nuRec hok H.hlay CMain.sOffU20 (by decide) (hS ▸ hσ)] at hsg
  have hcom := vrel_regND (s := Shape.small x) N Q lay P20.nuRec hok H.hlay .com (.inl rfl) ry hry (rv.getD 0 0)
  have hks := vrel_regND (s := Shape.small x) N Q lay P20.nuRec hok H.hlay .ks (.inr (.inl rfl)) ry hry
    (rv.getD 3 0)
  have hTV : List.Forall₂ (VRel (Shape.small x)) t.2.1
      ((E2V.splitE2 19 ⟨[(1, ⟨Typed.relayRounds, 0⟩, rr.map toE2)], toE2 vR⟩).map
          (fun c ↦ relocSAt CMain.sOffU20 c.onStack) ++
        (regClaimT (N.inst Q lay) .sigma (N.inst Q lay).sigmaW (ry.map toE2) (toE2 (rv.getD 2 0))).map
          (relocSAt CMain.sOffU20) ++
        regClaimT (N.inst Q lay) .com N.toN.off (ry.map toE2) (toE2 (rv.getD 0 0)) ++
        regClaimT (N.inst Q lay) .ks N.toN.off (ry.map toE2) (toE2 (rv.getD 3 0))) := by
    rw [ht1, show typedClaimsND N P20L ry rv rr vR = typedClaimsND N P20U ry rv rr vR from rfl]
    unfold typedClaimsND
    exact Lk.forall₂_append (Lk.forall₂_append (Lk.forall₂_append hrelay hsg) hcom) hks
  -- the three claims
  have hZV := vrel_mbSums (s := Shape.small x) N.mbT hlin hfc hfh (t.2.2.1, t.2.2.2) b hbus
  -- the front
  have hFV := front_relU (s := Shape.small x) x tp k hk hsh (fun hs ↦ of_decide_eq_true hs)
    (by simp [pubX, pubOf])
  have hV := forall₂_onStackZsF (Lk.forall₂_append (Lk.forall₂_append hTV hZV) hFV)
  -- the spec's list in V_S's order
  convert hV using 1
  set G : VStackClaim → VStackClaim := fun w ↦ if Shape.small x then Shape.onStackZ w else w with hG
  have hρ : ∀ l : List VStackClaim, l.map (relocU20 x) = (l.map (relocSAt CMain.sOffU20)).map G := fun l ↦ by
    rw [List.map_map]; rfl
  unfold assembleU₂ typedClaimsL
  dsimp only
  rw [onStackZs_eq_map, hρ, ordMk_of_length 4 _ _ (by simp [E2V.splitE2, regClaimT]), ← List.map_append]
  simp only [List.map_append, List.map_map, List.append_assoc, List.append_nil, Function.comp_def, List.map_nil,
    List.nil_append, E2V.pointE2, E2T.kv_toE2_getD]
  rfl


section Ref
variable {cap : ℕ → ℕ → ℕ} {occ : ℕ → ℕ → ℕ} {shp : ℕ → ℕ × ℕ} {rw : ℕ → ℕ} {sig : ByteArray}

/-- **V_S's typed phases at S2GB** (items on `P20B`'s layout) refine `typedProgLB 13` (`ref_dTypedLS`'s twin). -/
theorem ref_dTypedLSB (N : TNatT) (Q : Lvm.Loop.Program) (lay : Typed.Lay) (H : TRefHypTB N Q lay) (pT : Params)
    (hld : pT.leafdecReads = 1) (hbus : pT.busDepth = 13) (pub : Pub)
    (hacc : pub.accIn.pt.length = Typed.phiVarsT) {i : ℕ} (hw : WAt rw i wTypedLB) :
    RefAtWP cap occ shp rw sig i (dTypedLG pT N (m3G N P20B) pub (typedItemsND N P20B))
      (Lvm.E2S.typedProgLB 13 (N.inst Q lay) pub)
      (fun r a ↦ TRelTL P20B N Q lay (r.1, r.2.1.flatMap FItem.flat, r.2.2) a)
      (fun r ↦ N.phiT (r.1.pt.map Lvm.e2OfFE) = Lvm.e2OfFE r.1.y) (i + wTypedLB.length) := by
  have h := ref_dTypedLOB (cap := cap) (occ := occ) (shp := shp) (rw := rw) (sig := sig) P20B pT N Q lay H
    (m3G N P20B) ((m3G_busFinal N P20B).trans (real_busFinal pT N.mbT).symm) hld hbus pub hacc hw
  rw [dTypedLG_items] at h
  have h' := RefAtWP.of_map h
  exact h'

end Ref
end Lvm.VEq

namespace Lvm.VEq
open RecursionFast Lvm DM LeanVM.Parameters LeanVM.Protocol LeanVM.Protocol.Compile Finset
open Lvm.FE2 (toE2)
open Lvm.E2U Lvm.E2T Lvm.E2S Lvm.ASM
open Lvm.E2V (selPtF)
open Lvm.E2L (linClaims linGroup dOpenFFL mbSumsN typedClaimsL dTypedLG wireUDGc tapeUDGc)
open Lvm.CT (occOfU)
open LeanVM.Protocol.Whir.Sound (cfgMain23Jq cfgMain24G)

theorem monoD_tapeUDGcB (iv : List (ℕ × ℕ)) (s : List FK) (n : ℕ) : MonoD (tapeUDGc iv rowSwitchDR P20B s n) :=
  monoD_tapeUDGcS iv s n

theorem RefAtPW.toBP {cap : ℕ → ℕ → ℕ} {occ : ℕ → ℕ → ℕ} {shp : ℕ → ℕ × ℕ} {pth hq : ℕ → ℕ} {rw : ℕ → ℕ}
    {sig : ByteArray} {cap' : ℕ → ℕ → ℕ} {shp' : ℕ → ℕ × ℕ} {idx : Ref → ℕ}
    {α β : Type} {i j : ℕ} {d : DM β} {P : VerifierProgram α} {R : β → α → Prop} {Q : β → Prop}
    {as : List Atom} {R' : α → Prop} (h : RefAtPW cap occ shp rw sig i d P R Q j)
    (hF : FolP cap' shp' idx P as R') (hn : ∀ r, Atom.op r ∉ as) :
    RefAtPWB cap occ shp pth hq rw sig i d P R Q j :=
  RefAtPW.toB h (hF.run []) hn

end Lvm.VEq

namespace Lvm.VEq

open RecursionFast Lvm DM LeanVM.Parameters LeanVM.Protocol.Compile
open Lvm.E2U Lvm.E2T Lvm.E2S Lvm.ASM
open Lvm.CT (occOfU)
open Lvm.E2V
open LeanVM.Protocol.Whir.Sound (cfgMain23Jq cfgMain24G)

end Lvm.VEq

namespace Lvm.VEq

open RecursionFast Lvm DM LeanVM.Parameters LeanVM.Protocol LeanVM.Protocol.Compile Finset
open Lvm.FE2 (toE2)
open Lvm.E2U Lvm.E2T Lvm.E2S Lvm.ASM
open Lvm.E2V (selPtF)
open Lvm.E2L (linClaims linGroup dOpenFFL mbSumsN typedClaimsL dTypedLG wireUDGc tapeUDGc)
open Lvm.CT (occOfU)
open LeanVM.Protocol.Whir.Sound (cfgMain23Jq cfgMain24G)

/-- **The S2GB decision refines `P_S` at S2GB on the S2GB stream** (`ref_decideGSX`'s twin). -/
theorem ref_decideGB (N : TNatT) (Q : Lvm.Loop.Program) (lay : Typed.Lay) (H : TRefHypTB N Q lay)
    (hlin : Lvm.M3.mbLinB N.mbT = true) (hσ : Lvm.TypedV.SigInSL (layout0 P20B).s N.toN)
    (pT : Params) (hbus : pT.busDepth = 13) (hld : pT.leafdecReads = 1)
    (sig : ByteArray) (vk c : RecursionFast.Digest) (x : List UInt8) (hpub : pubOfWS vk c sig = pubXTS x) :
    RefAtPWB capOfB occOfU shpS pthB hqB rwB20 sig 0 (decideProgSB P20B pT (contIvSB aSP) N vk c)
      (Lvm.ASM.PSWithM (Lvm.E2F.midP (Lvm.ASM.midMk 4 relocU20 (midGB (N.inst Q lay)))) x) (fun _ b ↦ b = true)
      (fun a ↦ N.phiT (a.pt.map Lvm.e2OfFE) = Lvm.e2OfFE a.y) (readWidthsP P20B).length := by
  have hw : WAt rwB20 0 (wDecLB (atomsOf P20 (openMainI P20))) := by
    have h := wAt_rwB20
    rw [widthsA_scheduleB] at h
    exact h
  have hlen : (readWidthsP P20B).length = (wDecLB (atomsOf P20 (openMainI P20))).length := by
    rw [readWidthsP_eqAP, widthsA_scheduleB]
  rw [hlen]
  have hacc : (pubXTS x).accIn.pt.length = Typed.phiVarsT := by
    simp only [pubXTS, pubOfWS, List.length_map, List.length_range]; rfl
  have hs : sBitsD (pubXTS x).s = KG.digestBits (hdX x).s := by
    rw [show (pubXTS x).s = (pubX x).s from rfl, pubX_s, E2V.sBitsD_digestLanes]
  have hσ' : ∀ g ∈ N.toN.regs, g.src = .sigma →
      (layout0 P20U).s ≤ g.dst ∧ g.dst + 2 ^ g.log ≤ (layout0 P20U).s + 2 ^ 19 := by
    have h := hσ
    unfold Lvm.TypedV.SigInSL at h
    rw [layout0_P20B] at h
    exact h
  have hFO : ∀ (cl : List VStackClaim) (pp : List ℕ),
      Fol capS shpS idxS (LeanVM.Protocol.Verifier.verifyStackedJ (cfgMain23Jq 1) cl)
        (atomsOf P20 (openMainI P20)) pp fun _ _ ↦ True := fun cl pp ↦ fol_openMain cl pp
  have h24O : ∀ w ∈ widthsA (atomsOf P20 (openMainI P20)), w = 24 :=
    fun w hw' ↦ mem_widthsA_openF w (by rw [openMainI_F, atomsOf_F]; exact hw')
  rw [wDecLB, WAt.append, WAt.append, WAt.append] at hw
  obtain ⟨⟨⟨hw0, hwT⟩, hwF⟩, hwO⟩ := hw
  replace hwF := WAt.idx_eq hwF (j := 0 + [24].length + wTypedLB.length)
    (by simp only [List.length_append]; omega)
  replace hwO := WAt.idx_eq hwO (j := 0 + [24].length + wTypedLB.length + wTapeU.length)
    (by simp only [List.length_append]; omega)
  have hsc : M3.sumcheckTabs N.mbT = N.mbT := H.sc_eqB
  rw [psB_eq]
  unfold decideProgSB
  refine RefAtPWB.read_left ?_
  dsimp only
  rw [hpub]
  -- the cap
  refine RefAtPWB.bind (Q := fun _ ↦ True) ?_ (refWB_skip skip_P20B _) (fun _ _ _ ↦ trivial) ?_
  rotate_left
  rintro - - - -
  -- the pin
  refine RefAtPWB.bind (Q := fun _ ↦ True) ?_
    (((refW_pinD (WAt.cons.mp hw0).1).toPW _).toBP
      (folP_pinProg (cap := capS) (shp := shpS) (idx := idxS)) not_op_pin)
    (fun _ _ _ ↦ trivial) ?_
  rotate_left
  rintro pin za ⟨z, a, rfl, rfl⟩ -
  -- the typed phases
  have hT0 : RefAtPWB capOfB occOfU shpS pthB hqB rwB20 sig (0 + [24].length)
      (dTypedLG pT N (m3G N P20B) (pubXTS x) (typedItemsND N P20B))
      (Lvm.E2S.typedProgLB 13 (N.inst Q lay) (pubXTS x))
      (fun r a ↦ TRelTL P20B N Q lay (r.1, r.2.1.flatMap FItem.flat, r.2.2) a)
      (fun t ↦ N.phiT (t.1.pt.map Lvm.e2OfFE) = Lvm.e2OfFE t.1.y) (0 + [24].length + wTypedLB.length) := by
    have h' : RefAtPW capOfB occOfU shpS rwB20 sig (0 + [24].length)
        (dTypedLG pT N (m3G N P20B) (pubXTS x) (typedItemsND N P20B))
        (Lvm.E2S.typedProgLB 13 (N.inst Q lay) (pubXTS x))
        (fun r a ↦ TRelTL P20B N Q lay (r.1, r.2.1.flatMap FItem.flat, r.2.2) a)
        (fun t ↦ N.phiT (t.1.pt.map Lvm.e2OfFE) = Lvm.e2OfFE t.1.y) (0 + [24].length + wTypedLB.length) :=
      ref_dTypedLSB N Q lay H pT hld hbus (pubXTS x) hacc hwT
    exact RefAtPW.toBP h'
      (folP_typedProgLB (cap := capS) (shp := shpS) (idx := idxS) P20B 13 (N.inst Q lay) (pubXTS x) rfl rfl
        rfl) (not_op_atomsOf P20B noOp_typedB)
  refine RefAtPWB.bind (Q := fun t ↦ N.phiT (t.1.pt.map Lvm.e2OfFE) = Lvm.e2OfFE t.1.y) ?_ hT0 ?_ ?_
  rotate_left
  · intro b s hs'
    refine promise_of_retDG (fun a ↦ N.phiT (a.pt.map Lvm.e2OfFE) = Lvm.e2OfFE a.y) ?_ hs'
    exact RetD.bind_true fun _ ↦ RetD.bind_true fun _ ↦ RetD.pure rfl
  rintro ⟨acc, ti, ζ, bus⟩ a' hT -
  dsimp only
  -- the tape
  rw [show (pubXTS x).n = (pubX x).n from rfl]
  have eT : tapeUDGc (contIvSB aSP) rowSwitchDR P20B = tapeUDGc (contIvSB aSP) rowSwitchDR P20S := rfl
  rw [eT]
  have hTp1 := refW_tapeUDGcS (cap := capOfB) (occ := occOfU) (shp := shpS) (rw := rwB20) (sig := sig)
    (contIvSB aSP) (pubXTS x).s (hdX x).s hs (pubX x).n hwF
  have hTp2 := hTp1.retD (retD_tapeUDGcS (contIvSB aSP) (pubXTS x).s (pubX x).n)
  have hTp := (hTp2.toPW (fun _ ↦ True)).toBP (pth := pthB) (hq := hqB)
    (folP_tapeProgL (cap := capS) (shp := shpS) (idx := idxS) P20B (contIvSB aSP) rfl _ _)
    not_op_tapeB
  refine RefAtPWB.bind (Q := fun _ ↦ True) ?_ hTp (fun _ _ _ ↦ trivial) ?_
  rotate_left
  rintro tp k ⟨hk, hsh, hcols⟩ -
  -- the opening, on the closures' claims
  have hsh' := hsh
  obtain ⟨-, hl20, -, -, hy5, -, hm5, -⟩ := hsh'
  have hlc : linClaims CMain.nu20 ζ ((List.range 3).map (M3.mbColsN N.mbT bus))
      ((List.range 3).map (M3.mbValueN N.mbT bus ζ)) =
      (mbSumsN N.mbT (ζ, bus)).map fun c ↦ (Com.main, c, (0 : FE)) := Lvm.E2L.linClaims_mb N.mbT (ζ, bus)
  have e : Lvm.E2L.dOpenFFLB P20B (TypedV.smallT P20B (pubXTS x)) (BlockClaim.point ⟨CMain.nu20, 0⟩ z a) ti ζ
      ((List.range 3).map (M3.mbColsN (M3.sumcheckTabs N.mbT) bus))
      (M3.mbValsF (M3.sumcheckTabs N.mbT) bus ζ) (frontItemsU rowAccR P20B (pubXTS x) tp) =
      dOpenFB P20B (Shape.small x) (BlockClaim.point ⟨CMain.nu20, 0⟩ z a) (ti.flatMap FItem.flat ++
        (mbSumsN N.mbT (ζ, bus)).map (fun c ↦ (Com.main, c, (0 : FE))) ++ frontClaimsUD P20U (pubXT x) (mapTU tp)) := by
    rw [M3.mbValsF_eq, dOpenFFLB_eq, hsc]
    show dOpenFB P20B (TypedV.smallT P20U (pubXT x)) _ (ti.flatMap FItem.flat ++
      linClaims CMain.nu20 ζ ((List.range 3).map (M3.mbColsN N.mbT bus))
        ((List.range 3).map (M3.mbValueN N.mbT bus ζ)) ++
      (frontItemsU rowAccR P20U (pubXT x) tp).flatMap FItem.flat) = _
    rw [smallT_P20U, hlc]
    refine dOpenFB_congr _ _ _ ?_
    rw [List.map_append, List.map_append, List.map_append, List.map_append,
      show P20B.nuMain = P20U.nuMain from rfl, frontU_stk _ _ tp hcols hl20 hy5 hm5]
  rw [e]
  have hO := RefAtB.toPWB (ref_dOpenFOB (cap := capOfB) (occ := occOfU) (shp := shpS) (pth := pthB) (hq := hqB)
    (capL := capS) (sig := sig) P20B rfl rfl rfl corrMainB _ _ (screl_pinW z a) (Shape.small x) _ _
    (claimsL_relB N Q lay H hlin hσ' x (acc, ti.flatMap FItem.flat, ζ, bus) a' hT (mapTU tp) k hk hsh))
    (cap' := capS) (shp' := shpS) (idx := idxS) (hFO _) hwO h24O (fun _ ↦ True)
  refine RefAtPWB.bind (Q := fun _ ↦ True) (fun _ ↦ MonoD.pure _) hO (fun _ _ _ ↦ trivial) ?_
  rintro - - - -
  have hj : 0 + [24].length + wTypedLB.length + wTapeU.length + (widthsA (atomsOf P20 (openMainI P20))).length =
      (wDecLB (atomsOf P20 (openMainI P20))).length := by
    -- by `rw`: `simp`'s closing `0 + 1 + … = 1 + …` made the kernel evaluate the widths' lengths (5.2 M hb)
    rw [Nat.zero_add, wDecLB, List.length_append, List.length_append, List.length_append, List.length_singleton]
  rw [hj]
  exact refWB_pure (R := fun (_ : Acc) (b : Bool) ↦ b = true) rfl _
  all_goals repeat' (first
    | (with_reducible exact MonoD.pure _) | (with_reducible exact monoD_skip _)
    | (with_reducible exact monoD_pinD _) | (with_reducible exact monoD_dTypedLG _ _ _ _ _)
    | (with_reducible exact monoD_tapeUDGcS _ _ _) | (with_reducible exact monoD_tapeUDGcB _ _ _) | (with_reducible exact monoD_dOpenFB _ _ _ _)
    | (with_reducible exact monoD_dOpenFFLB _ _ _ _ _ _ _ _)
    | (with_reducible refine MonoD.bind ?_ fun _ ↦ ?_) | (dsimp only) | split | intro _)

end Lvm.VEq

namespace Lvm.VEq


open RecursionFast Lvm DM LeanVM.Parameters LeanVM.Protocol.Compile
open Lvm.E2U Lvm.E2T Lvm.E2S Lvm.ASM
open Lvm.CT (occOfU)
open Lvm.E2V
open LeanVM.Protocol.Whir.Sound (cfgMain23Jq cfgMain24G)

/-- **`P_S` at S2GB follows the S2GB schedule** (`fol_PSOfS`'s twin). -/
theorem fol_PSOfB (reloc : List UInt8 → VStackClaim → VStackClaim) (Ti : Typed.TInst) (x : List UInt8) :
    Fol capS shpS idxS (Lvm.ASM.PSWithM (Lvm.E2F.midP (Lvm.ASM.midMk 4 reloc (midGB Ti))) x)
      (atomsOf P20B (schedule P20B)) [] fun _ _ ↦ True := by
  rw [atomsOf_scheduleB]
  unfold Lvm.ASM.PSWithM
  refine Fol.bindP (folP_commitRootUd cfgMain24G rfl cap_main0 rfl) fun _ _ ↦ ?_
  refine @Fol.bindP capS shpS idxS _ _ (Lvm.E2F.midP (Lvm.ASM.midMk 4 reloc (Lvm.E2S.midGB Ti)) x) _
    (atomsOf P20B (midItemsL P20B)) (atomsOf P20 (openMainI P20) ++ []) _ [] _
    (folP_midPB reloc Ti x) fun cl _ ↦ ?_
  exact @Fol.bindQ capS shpS idxS _ _ _ _ (atomsOf P20 (openMainI P20)) [] [] _ _ (@fol_openMain cl [])
    fun _ _ _ ↦ trivial

/-- `decideFSB` holds: the run's checks held and its folded claim passes `Φ_Q` at `E2` (`decideFSG_ok`'s twin). -/
private theorem stRunLB {α : Type} (x : StateM RS α) (s : RS) : x.run s = x s := (rfl : x.run s = x s).trans rfl

theorem decideFSB_ok {pT : Params} {iv : List (ℕ × ℕ)} {N : TNatT} {vk c : RecursionFast.Digest} {sig : ByteArray}
    (h : decideFSB P20B pT iv N vk c sig = true) :
    (runD (decideProgSB P20B pT iv N vk c) sig (RS.startH (headerBytesP P20B))).2.ok = true ∧
      N.phiT ((runD (decideProgSB P20B pT iv N vk c) sig (RS.startH (headerBytesP P20B))).1.pt.map
        Lvm.e2OfFE) =
        Lvm.e2OfFE (runD (decideProgSB P20B pT iv N vk c) sig (RS.startH (headerBytesP P20B))).1.y := by
  have eD : @decideFSB = @decideFSB := rfl
  conv at eD => rhs; delta decideFSB
  rw [eD] at h
  beta_reduce at h
  rw [DM.runOnH, stRunLB] at h
  rcases hr : runD (decideProgSB P20B pT iv N vk c) sig (RS.startH (headerBytesP P20B)) with ⟨a, s⟩
  rw [show decideProgSB P20B pT iv N vk c sig (RS.startH (headerBytesP P20B)) = (a, s) from hr] at h
  simp only [Bool.and_eq_true] at h
  exact ⟨h.1.1.1, fe2_beq h.2⟩

/-- **`parseOkB`'s parts** (`parseOkS_parts`'s twin: the size check is `piStatic ≤ |π| ≤ piStatic + tailMax`). -/
theorem parseOkB_parts {p : Params} {vk c : RecursionFast.Digest} {π : ByteArray} (h : parseOkB p vk c π = true) :
    piStatic p ≤ π.size ∧ π.size ≤ piStatic p + tailMax p ∧ π.get! 0 = 0x53 ∧ zeroBytes π 1 7 = true ∧
      ((Header.ofProof π).b = 0 ∨ (Header.ofProof π).b = 1) ∧ (Header.ofProof π).vk = vk ∧
      1 ≤ (Header.ofProof π).n ∧ (Header.ofProof π).n ≤ chainCap ∧ c = (Header.ofProof π).stmt := by
  simp only [parseOkB, Bool.and_eq_true, beq_iff_eq, Bool.or_eq_true, decide_eq_true_eq, and_assoc] at h
  obtain ⟨hs1, hs2, h0, hz, hb, hvk, hn1, hn2, -, hif⟩ := h
  refine ⟨hs1, hs2, h0, hz, hb, hvk, hn1, hn2, ?_⟩
  by_cases hb0 : (Header.ofProof π).b = 0
  · simp only [hb0, ↓reduceIte, Bool.and_eq_true, beq_iff_eq] at hif
    exact hif.2
  · simp only [hb0, ↓reduceIte, beq_iff_eq] at hif
    exact hif

/-- **V_S's public values at S2GB are the statement's** (`pubGS_eq`'s twin with `parseOkB`). -/
theorem pubGB_eq {vk c : RecursionFast.Digest} {π : ByteArray} (h : parseOkB P20B vk c π = true) {sig : ByteArray}
    (hsig : ∀ t < headerBytesP P20B - 8, sig.get! (headerAt 8 + t) = π.get! (8 + t)) :
    pubOfWS vk c sig = pubXTS (xOfH (headerBytesP P20B) π) := by
  have h888 : headerBytesP P20B = 888 := by decide
  obtain ⟨-, -, -, -, -, hvk, -, -, hc⟩ := parseOkB_parts h
  obtain ⟨eb, evk, ecL, -, en, eh⟩ := hdrOf_xOfH_fix π (hb := headerBytesP P20B) (by rw [h888]; decide)
  have hst : (hdX (xOfH (headerBytesP P20B) π)).stmt = c := by
    rw [hc]
    show (Lvm.ASM.hdrOf _).stmt = _
    unfold Header.stmt Header.leaf
    rw [eb, ecL, en, eh]
  unfold pubXTS
  rw [hst, show (hdX (xOfH (headerBytesP P20B) π)).vk = vk from evk.trans hvk]
  refine pubOfWS_congr fun o h1 h2 ↦ ?_
  obtain ⟨t, rfl⟩ : ∃ t, o = headerAt 8 + t := ⟨o - headerAt 8, by (clear * - h1; omega)⟩
  have ht : t < headerBytesP P20B - 8 := by rw [h888]; simp only [headerAt] at h2 ⊢; (clear * - h2; omega)
  rw [hsig t ht, get!_sigOfXH π ht]

end Lvm.VEq
