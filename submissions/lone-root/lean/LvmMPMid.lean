-- New for lvm2 roll 11 (M′, R11-I): the layout-independent bridge from the pair-form middle phases (claims on
-- `C_rec` and `C_main`, candidate pairs) to `MidSpecM`/`MidShapeM` (claims on `C_main` only, one root), through an
-- abstract relocation `recOf`/`reloc` whose laws are hypotheses (the lead discharges them from R11-E's layout).
import LvmMPCert
import LvmCertSMid3

/-!
# M′'s middle phases from the pair form

In M′ the `C_rec` column is a function of the `C_main` column, `recOf x q` (the stream region read through the
shape's view), and a `C_rec` claim becomes a `C_main` claim by `reloc x` (as `LvmShape.onStackZ` relocates
big-stack claims onto the small stack). The laws (`RelocLaw`): a relocated claim holding on `q` gives the claim
on `recOf x q`, and relocation keeps multiaffinity, both for multiaffine claims only.

* **`midM reloc mid x`**: `mid x`, then the claims `ordM (cl.1.map (reloc x)) cl.2` (all on `C_main`, in V_S's
  order; a permutation of `cl.2 ++ cl.1.map (reloc x)`);
* **`candM h`**: `C_main`'s root candidates (`OpenPostM`'s set); **`candRelM recOf x h`**: their image under
  `q ↦ (q, recOf x q)`; **`GoodOfM recOf G`**: `G x q (recOf x q)`;
* **`OpenPostRG C Sh`**, **`MidSpecP mid C Sh`**: `OpenPostR`/`MidSpecR` with the candidate set `C x` and the
  shape `Sh` as parameters (`OpenPostR = OpenPostRG candPairs RootShape`, `midSpecR_iff`);
* **`midSpecM_of`**: `MidSpecP mid (candRelM recOf) RootShapeM G εm Lm` and a length bound on `mid`'s returns
  give `MidSpecM (midM reloc mid) (GoodOfM recOf G) εm Lm`; **`midShapeM_of`**: `NoCG` gives `MidShapeM`;
* **`midSpecOfRelG`**: `midSpecOfRel` (`LvmCertSMid3`) generic in the candidate set, the shape (any predicate a
  commitment-free run keeps), `εm`, and with `Kc`, `Qk` depending on `x`.
-/

set_option autoImplicit false

namespace Lvm.ASM

open RecursionFast
open LeanVM.Parameters LeanVM.Protocol LeanVM.Protocol.Compile LeanVM.Protocol.Verifier
open LeanVM.Protocol.Compile.VerifierProgram LeanVM.Protocol.Whir.Sound LeanVM.Protocol.EndToEnd
open LeanVM.Protocol.EndToEnd.Front
open LeanVM.Protocol.EndToEnd.Sound (RetOK)
open Lvm.M3 (NoCG cg_ret)
open scoped ENNReal NNReal

/-! ## The relocation and `midM` -/

/-- **The relocation's laws** (hypotheses; the lead discharges them from the layout): for a multiaffine
`C_rec` claim `c`, `reloc x c` holding on a `C_main` column `q` gives `c` on `recOf x q`, and `reloc x c` is
multiaffine on `C_main`. -/
structure RelocLaw (recOf : List UInt8 → Column CMain.nu20 → Column 19)
    (reloc : List UInt8 → LeanVM.Protocol.Verifier.StackClaim → LeanVM.Protocol.Verifier.StackClaim) :
    Prop where
  holds : ∀ x c q, IsMultiaffine 19 c.1 →
    StackClaim.Holds CMain.nu20 (reloc x c) q → StackClaim.Holds 19 c (recOf x q)
  affine : ∀ x c, IsMultiaffine 19 c.1 → IsMultiaffine CMain.nu20 (reloc x c).1

/-- **V_S's claim order** from the relocated stream claims `r` and `C_main`'s claims `m`: the first two stream
claims (the relayout's point claim, `σ′`'s), `C_main`'s claims but the last, the other stream claims (the `KS`
link's `M`), `C_main`'s last (the `KS` link's `X`). Always a permutation of `m ++ r` (`perm_ordM`). -/
def ordM {α : Type} (r m : List α) : List α := r.take 2 ++ m.dropLast ++ r.drop 2 ++ m.getLast?.toList

theorem perm_ordM {α : Type} (r m : List α) : (ordM r m).Perm (m ++ r) := by
  classical
  have hm : m.dropLast ++ m.getLast?.toList = m := by
    cases m using List.reverseRecOn with
    | nil => rfl
    | append_singleton l a => simp
  conv_rhs => rw [← hm, ← List.take_append_drop 2 r]
  rw [ordM, List.perm_iff_count]
  intro a
  simp only [List.count_append]
  omega

/-- **M′'s middle phases**: the pair-form phases, then every claim on `C_main` (`C_rec`'s relocated), in V_S's
phase order (`ordM`; lvm2 roll 11, R11-IR: the opening `verifyStackedJ` batches its claims with the powers of one
challenge `γ`, so the order is part of what V_S checks and the spec must list the claims as V_S's `dOpenT` does:
the typed phases' `[relay, σ′, com, ks, mini-bus]`, then the tape's, `KS`'s, the output lanes' and the `KS` link's
`[Y, in, M, X]`). Only membership and the count matter to `OpenPostM` (`perm_ordM`). -/
def midM (reloc : List UInt8 → LeanVM.Protocol.Verifier.StackClaim → LeanVM.Protocol.Verifier.StackClaim)
    (mid : List UInt8 → VerifierProgram OpenClaims) (x : List UInt8) :
    VerifierProgram (List LeanVM.Protocol.Verifier.StackClaim) :=
  mid x >>= fun cl ↦ .ret (ordM (cl.1.map (reloc x)) cl.2)

/-- `C_main`'s root candidates (`OpenPostM`'s set). -/
def candM (h : List Ev) : Set (Column CMain.nu20) := Candidates CMain.nu20 2 thrMain (wordOf (commits h) 0)

/-- **The one-root candidate pairs**: `C_main`'s candidates with their `C_rec` column. -/
def candRelM (recOf : List UInt8 → Column CMain.nu20 → Column 19) (x : List UInt8) (h : List Ev) : Set Pair :=
  (fun q ↦ (q, recOf x q)) '' candM h

/-- The good relation on `C_main` alone. -/
def GoodOfM (recOf : List UInt8 → Column CMain.nu20 → Column 19) (G : GoodRel) : GoodRelM :=
  fun x q ↦ G x q (recOf x q)

/-! ## The pair form, generic in the candidate set and the shape -/

/-- **`OpenPostR` at a candidate set `C` and a shape `Sh`**. -/
def OpenPostRG (C : List Ev → Set Pair) (Sh : List Ev → Prop) (Good : GoodRel) (x : List UInt8)
    (cl : OpenClaims) (h : List Ev) : Prop :=
  (∀ p ∈ C h, ¬ Good x p.1 p.2 →
      (∃ c ∈ cl.1, ¬ StackClaim.Holds 19 c p.2) ∨ (∃ c ∈ cl.2, ¬ StackClaim.Holds CMain.nu20 c p.1)) ∧
  Sh h ∧ (∀ c ∈ cl.1, IsMultiaffine 19 c.1) ∧ (∀ c ∈ cl.2, IsMultiaffine CMain.nu20 c.1) ∧
  cl.1.length ≤ 2 ^ 55 ∧ cl.2.length ≤ 2 ^ 40

theorem openPostR_eq : OpenPostR = OpenPostRG candPairs RootShape := rfl

/-- **`MidSpecR` at a candidate set `C x` and a shape `Sh`** (the pair form). -/
def MidSpecP (mid : List UInt8 → VerifierProgram OpenClaims) (C : List UInt8 → List Ev → Set Pair)
    (Sh : List Ev → Prop) (Good : GoodRel) (εm Lm : ℝ≥0∞) : Prop :=
  ∀ x (T : ℝ≥0∞), T ≤ εm → Nonempty (Spec (mid x) Sh (OpenPostRG (C x) Sh Good x) εm Lm T)

theorem midSpecR_iff {mid : List UInt8 → VerifierProgram OpenClaims} {Good : GoodRel} {εm Lm : ℝ≥0∞} :
    MidSpecR mid Good εm Lm ↔ MidSpecP mid (fun _ ↦ candPairs) RootShape Good εm Lm := Iff.rfl

/-! ## The bridge -/

section Bridge

variable {recOf : List UInt8 → Column CMain.nu20 → Column 19}
  {reloc : List UInt8 → LeanVM.Protocol.Verifier.StackClaim → LeanVM.Protocol.Verifier.StackClaim}

/-- **`OpenPostM` from the pair form**: a non-good candidate `q` of `C_main` is the pair `(q, recOf x q)`, which
fails a `C_main` claim or a `C_rec` claim; the latter's relocation fails on `q`. -/
theorem openPostM_of (hρ : RelocLaw recOf reloc) {G : GoodRel} {x : List UInt8} {cl : OpenClaims} {h : List Ev}
    (hp : OpenPostRG (candRelM recOf x) RootShapeM G x cl h) (hl : cl.2.length + cl.1.length ≤ 2 ^ 40) :
    OpenPostM (GoodOfM recOf G) x (ordM (cl.1.map (reloc x)) cl.2) h := by
  have hP := perm_ordM (cl.1.map (reloc x)) cl.2
  obtain ⟨hc, hR, hm1, hm2, -⟩ := hp
  refine ⟨fun q hq hng ↦ ?_, hR, fun c hc' ↦ ?_, by rw [hP.length_eq]; simpa using hl⟩
  · rcases hc (q, recOf x q) ⟨q, hq, rfl⟩ hng with ⟨c, hc1, hn⟩ | ⟨c, hc2, hn⟩
    · exact ⟨reloc x c, hP.mem_iff.mpr (List.mem_append_right _ (List.mem_map_of_mem hc1)),
        fun hh ↦ hn (hρ.holds x c q (hm1 c hc1) hh)⟩
    · exact ⟨c, hP.mem_iff.mpr (List.mem_append_left _ hc2), hn⟩
  · rcases List.mem_append.mp (hP.mem_iff.mp hc') with hc' | hc'
    · exact hm2 c hc'
    · obtain ⟨c', hc1, rfl⟩ := List.mem_map.mp hc'
      exact hρ.affine x c' (hm1 c' hc1)

/-- **`MidSpecM` from the pair form** at the one-root candidate pairs `candRelM recOf`, with at most `2^40`
claims in all. -/
theorem midSpecM_of (hρ : RelocLaw recOf reloc) {mid : List UInt8 → VerifierProgram OpenClaims} {G : GoodRel}
    {εm Lm : ℝ≥0∞} (hP : MidSpecP mid (candRelM recOf) RootShapeM G εm Lm)
    (hlen : ∀ x, RetOK (fun cl : OpenClaims ↦ cl.2.length + cl.1.length ≤ 2 ^ 40) (mid x)) :
    MidSpecM (midM reloc mid) (GoodOfM recOf G) εm Lm := fun x T hT ↦
  (hP x T hT).map fun S ↦
    (Lvm.KG.specWithRet S (hlen x)).bind' fun cl ↦
      (Spec.ret (Post := OpenPostM (GoodOfM recOf G) x) (εmax := εm) (T := T)
          (ordM (cl.1.map (reloc x)) cl.2)).mono
        (fun _ hp ↦ openPostM_of hρ hp.2 hp.1) (fun _ _ h ↦ h) le_rfl le_rfl le_rfl

/-- **`MidShapeM` of `midM`**: the pair-form phases commit nothing and grind nothing. -/
theorem midShapeM_of {mid : List UInt8 → VerifierProgram OpenClaims} (hcg : ∀ x, NoCG (mid x)) :
    MidShapeM (midM reloc mid) where
  noCommit x := (Lvm.M3.NoCG.bind (hcg x) fun _ ↦ cg_ret _).1
  noGrind x := (Lvm.M3.NoCG.bind (hcg x) fun _ ↦ cg_ret _).2

end Bridge

/-! ## `midSpecOfRel`, generic in the candidate set and the shape -/

section Glue

variable {α κ : Type} {busP : List UInt8 → VerifierProgram α} {kgP : List UInt8 → VerifierProgram κ}
  {asm : List UInt8 → α → κ → OpenClaims}
  {Gb Gk : List UInt8 → Pair → Prop} {B : List UInt8 → α → Pair → Prop}
  {Kc : List UInt8 → κ → Pair → Prop} {Qa : List UInt8 → α → Prop} {Qk : List UInt8 → κ → Prop}
  {εm Lb Lk : ℝ≥0∞} {C : List UInt8 → List Ev → Set Pair} {Sh : List Ev → Prop}

/-- `openPostR_of` at a candidate set and a shape. -/
theorem openPostRG_of {Good : GoodRel} {x : List UInt8} {a : α} {k : κ} {h : List Ev}
    (hasm : ∀ p : Pair, (∀ c ∈ (asm x a k).1, StackClaim.Holds 19 c p.2) →
      (∀ c ∈ (asm x a k).2, StackClaim.Holds CMain.nu20 c p.1) → Kc x k p ∧ B x a p)
    (hside : (∀ c ∈ (asm x a k).1, IsMultiaffine 19 c.1) ∧
      (∀ c ∈ (asm x a k).2, IsMultiaffine CMain.nu20 c.1) ∧ (asm x a k).1.length ≤ 2 ^ 55 ∧
      (asm x a k).2.length ≤ 2 ^ 40)
    (hD : Doomed (C x) (fun p ↦ Kc x k p ∧ (B x a p ∧ ¬ Good x p.1 p.2)) h) (hR : Sh h) :
    OpenPostRG (C x) Sh Good x (asm x a k) h := by
  refine ⟨fun p hp hng ↦ ?_, hR, hside⟩
  by_contra hno
  push Not at hno
  have hkb := hasm p hno.1 hno.2
  exact hD p hp ⟨hkb.1, hkb.2, hng⟩

open Classical in
/-- **`midSpecOfRel` at a candidate set `C x` and a shape `Sh`** (any predicate a commitment-free run keeps):
the same two phases and link, into `MidSpecP`. -/
theorem midSpecOfRelG (hSh : ∀ h₀ l, commits l = [] → Sh h₀ → Sh (h₀ ++ l))
    (SB : ∀ x, Spec (busP x)
      (fun h ↦ Sh h ∧ Doomed (C x) (fun p ↦ Gb x p ∧ (Gk x p ∧ ¬ (Gb x p ∧ Gk x p))) h)
      (fun a h ↦ Doomed (C x)
        (fun p ↦ (B x a p ∧ ¬ (Gb x p ∧ Gk x p)) ∧ (Gk x p ∧ ¬ (Gb x p ∧ Gk x p))) h ∧ Sh h)
      εm Lb Lk)
    (hQa : ∀ x, RetOK (Qa x) (busP x))
    (SK : ∀ x a (T : ℝ≥0∞), T ≤ εm → Spec (kgP x)
      (Doomed (C x) (fun p ↦ (Gk x p ∧ ¬ (Gb x p ∧ Gk x p)) ∧ (B x a p ∧ ¬ (Gb x p ∧ Gk x p))))
      (fun k h ↦ Doomed (C x) (fun p ↦ Kc x k p ∧ (B x a p ∧ ¬ (Gb x p ∧ Gk x p))) h) εm Lk T)
    (hQk : ∀ x, RetOK (Qk x) (kgP x)) (hkc : ∀ x, NoCG (kgP x))
    (hasm : ∀ x a k (p : Pair), Qa x a → Qk x k →
      (∀ c ∈ (asm x a k).1, StackClaim.Holds 19 c p.2) →
      (∀ c ∈ (asm x a k).2, StackClaim.Holds CMain.nu20 c p.1) → Kc x k p ∧ B x a p)
    (hside : ∀ x a k, Qa x a → Qk x k → (∀ c ∈ (asm x a k).1, IsMultiaffine 19 c.1) ∧
      (∀ c ∈ (asm x a k).2, IsMultiaffine CMain.nu20 c.1) ∧ (asm x a k).1.length ≤ 2 ^ 55 ∧
      (asm x a k).2.length ≤ 2 ^ 40) :
    MidSpecP (fun x ↦ busP x >>= fun a ↦ kgP x >>= fun k ↦ VerifierProgram.ret (asm x a k)) C Sh
      (fun x qm qr ↦ Gb x (qm, qr) ∧ Gk x (qm, qr)) εm Lb := fun x T hT ↦
  ⟨((Lvm.KG.specWithRet (SB x) (hQa x)).bind' fun a ↦
      if ha : Qa x a then
        ((Lvm.KG.specWithRet ((SK x a T hT).frame Sh fun _ _ hl hr ↦
            hSh _ _ ((hkc x).1.reach_commits hl) hr) (hQk x)).mono
          (fun _ hp ↦ ⟨Doomed.mono hp.2.1 fun _ hq ↦ ⟨hq.2, hq.1⟩, hp.2.2⟩) (fun _ _ h ↦ h) le_rfl
          le_rfl le_rfl).bind' fun k ↦
        if hk : Qk x k then
          (Spec.ret (Post := OpenPostRG (C x) Sh (fun x qm qr ↦ Gb x (qm, qr) ∧ Gk x (qm, qr)) x) (εmax := εm)
              (T := T) (asm x a k)).mono
            (fun _ hp ↦ openPostRG_of (hasm x a k · ha hk) (hside x a k ha hk) hp.2.1 hp.2.2)
            (fun _ _ h ↦ h) le_rfl le_rfl le_rfl
        else Spec.dead.mono (fun _ hd ↦ hk hd.1) (fun _ _ h ↦ h) le_rfl le_rfl le_rfl
      else Spec.dead.mono (fun _ hd ↦ ha hd.1) (fun _ _ h ↦ h) le_rfl le_rfl le_rfl).mono
    (fun _ hp ↦ ⟨hp, fun _ _ hq ↦ hq.2.2 ⟨hq.1, hq.2.1⟩⟩) (fun _ _ h ↦ h) le_rfl le_rfl le_rfl⟩

end Glue

end Lvm.ASM
