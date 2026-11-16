-- New for lvm2 (J2C, J2′ at G0): the interface of the INV certificate (J2C-DES §3). Definitions only; the three
-- WPs J2C-A (front end), J2C-B (openings) and J2C-C (extraction) state and prove against these.
import LvmCertS
import LvmWhirParamsJp
import LvmWhirPrefixJ
import LvmWhirPathR
import LvmWhirFoldsR

/-!
# J2′'s INV certificate: the shared definitions

J2C-DES §0–§1: `C_rec` opens at the Johnson radius (`cfgRec20Jp`), and the certificate has **no doom**: its luck
is "the invariant broke, or the extractor's luck" (`Lvm.FS.kcertOfInv`, `LvmInvCert`). The invariant, by phase:
every **non-good** candidate pair fails a running claim (front end, `OpenPostR`); at the openings either every
non-`GoodRec` member of `C_rec`'s list fails a `C_rec` claim (`StackedPreR`) or every `C_main` candidate fails a
`C_main` claim (`MainPre`); through `C_rec`'s opening JB-L's relativised doom; at the residual `GoodResAt` or the
residual's doom. An accepting run in the invariant has `ExtI`.

* `GoodRec Good x q`: some `C_main` column makes `(qm, q)` good (any column, not only candidates).
* `OpenPostR Good x cl h`: `OpenPost` on the non-good pairs; `C_rec`'s claims at most `2^55` (its batching at
  `L = 304` within `εS`).
* `MidSpecR mid Good εm Lm`: the middle phases from `RootShape` end in `OpenPostR`.
* `RunMid mid x cl h`: `h` is the roots' run then a run of `mid x` returning `cl`.
* `recPrefixProg mid x`: the run up to `C_rec`'s residual; `GoodResAt`: `PostR`'s left disjunct at J2′ for the
  good set `GoodRec`; `ExtI mid Good x h`: a prefix of `h` is such a run, with `GoodResAt` (stable under appends).
* `ExtJ mid Good VS vk`: what extraction (J2C-C) hands the final assembly (`kcertOfInv`'s luck and extraction
  arguments for `schemeS vk (PSWith mid)`).

**Soundness is the case `Good := ⊥`**: `OpenPostR` is then `OpenPost` (without the claim bound's slack) and
`ExtI` is `False`.
-/

set_option autoImplicit false

namespace Lvm.ASM

open RecursionFast Lvm.FS Lvm.T
open LeanVM.Parameters
open LeanVM.Protocol.Compile hiding Proof Bytes
open LeanVM.Protocol.Verifier LeanVM.Protocol.Whir.Sound LeanVM.Protocol.EndToEnd
open scoped NNReal ENNReal

/-- **The good set of `C_rec`**: `q` is the `C_rec` half of a good pair (any `C_main` column). -/
def GoodRec (Good : GoodRel) (x : List UInt8) (q : LeanVM.Protocol.Column 19) : Prop := ∃ qm, Good x qm q

/-- **`OpenPost` on the non-good pairs** (J2C-DES §3): every non-good candidate pair fails a claim on `C_rec`
or on `C_main`; the roots' shape; the claims are multiaffine; at most `2^55` claims on `C_rec` (its batching
`(J − 1)·304/|E| ≤ εS` at the Johnson list bound) and `2^40` on `C_main`. `candPairs` is at `thrRec`. -/
def OpenPostR (Good : GoodRel) (x : List UInt8) (cl : OpenClaims) (h : List Ev) : Prop :=
  (∀ p ∈ candPairs h, ¬ Good x p.1 p.2 →
      (∃ c ∈ cl.1, ¬ LeanVM.Protocol.EndToEnd.StackClaim.Holds 19 c p.2) ∨
        (∃ c ∈ cl.2, ¬ LeanVM.Protocol.EndToEnd.StackClaim.Holds CMain.nu20 c p.1)) ∧
  RootShape h ∧ (∀ c ∈ cl.1, IsMultiaffine 19 c.1) ∧ (∀ c ∈ cl.2, IsMultiaffine CMain.nu20 c.1) ∧
  cl.1.length ≤ 2 ^ 55 ∧ cl.2.length ≤ 2 ^ 40

/-- **Obligation `MidSpecR`** (J2C-A): the middle phases, from the roots' shape alone, end in `OpenPostR`,
every group's escape at most `εm`, lead `Lm`, for every follower's allowance `T ≤ εm`. -/
def MidSpecR (mid : List UInt8 → VerifierProgram OpenClaims) (Good : GoodRel) (εm Lm : ℝ≥0∞) : Prop :=
  ∀ x (T : ℝ≥0∞), T ≤ εm → Nonempty (Spec (mid x) RootShape (OpenPostR Good x) εm Lm T)

/-- **The roots then the middle phases**: `h` is a completed run of the two root commitments followed by a
completed run of `mid x` returning `cl`. -/
def RunMid (mid : List UInt8 → VerifierProgram OpenClaims) (x : List UInt8) (cl : OpenClaims)
    (h : List Ev) : Prop :=
  ∃ hr lm, h = hr ++ lm ∧
    (commitRootUd cfgMain24G >>= fun _ ↦ commitRootUd cfgRec20G).after hr = some (.ret ()) ∧
    (mid x).after lm = some (.ret cl)

/-- **The run up to `C_rec`'s residual**: the roots, the middle phases, `C_rec`'s stacked opening up to the
residual (`stackPrefixJ`); returns the claims, `ρ`, the final level's fold state and the residual. -/
def recPrefixProg (mid : List UInt8 → VerifierProgram OpenClaims) (x : List UInt8) :
    VerifierProgram (OpenClaims × E × ((WhirStateT × List E) × List E)) :=
  (commitRootUd cfgMain24G >>= fun _ ↦ commitRootUd cfgRec20G) >>= fun _ ↦ mid x >>= fun cl ↦
    stackPrefixJ cfgRec20Jp cl.1 >>= fun a ↦ .ret (cl, a)

/-- **The residual is good** (`PostR`'s left disjunct at J2′, `cs := viewC 1 2 (commits h₁)`): the residual's
encoding is in the list of the final folded word, and it is the path of a member of the final good set, for
the good root set `gdRoot (codesRec20Jp 0) (GoodRec Good x)`. -/
def GoodResAt (Good : GoodRel) (x : List UInt8) (a : E × ((WhirStateT × List E) × List E))
    (h₁ : List Ev) : Prop :=
  let cs := viewC 1 2 (commits h₁)
  GoodRes (codesRec20Jp 1) 1
    (gdFinal codesRec20Jp cs a.2.1.1.folds 0 0 cfgRec20Jp.levels
      (gdRoot (codesRec20Jp 0) (GoodRec Good x) cs)) a.2.1 a.2.2 cs

/-- **What an accepting run in the invariant has** (J2C-DES §1): a prefix `h₁` of `h` is a completed run of
`recPrefixProg mid x` whose residual is good. Stable under appending events by construction. -/
def ExtI (mid : List UInt8 → VerifierProgram OpenClaims) (Good : GoodRel) (x : List UInt8)
    (h : List Ev) : Prop :=
  ∃ h₁ cl a, h₁ <+: h ∧ (recPrefixProg mid x).after h₁ = some (.ret (cl, a)) ∧ GoodResAt Good x a h₁

theorem ExtI.append {mid : List UInt8 → VerifierProgram OpenClaims} {Good : GoodRel} {x : List UInt8}
    {h : List Ev} (hE : ExtI mid Good x h) (l : List Ev) : ExtI mid Good x (h ++ l) := by
  obtain ⟨h₁, cl, a, hp, ha, hg⟩ := hE
  exact ⟨h₁, cl, a, hp.trans (List.prefix_append h l), ha, hg⟩

/-- **The extraction's interface** (J2C-C delivers it, the assembly `kcertOfInv` consumes it): the
extractor's luck `BL` (kept by prover moves, absent at the start, each group's escape at most `2^-132`) and
the extraction map, which on an accepting history with `ExtI`, not lucky at the end nor at any boundary,
gives a witness of the relation. -/
structure ExtJ (mid : List UInt8 → VerifierProgram OpenClaims) (Good : GoodRel) (VS : SProg)
    (vk : Digest) : Type where
  /-- The extractor's luck. -/
  BL : List UInt8 → List Ev → Prop
  BL_nil : ∀ x, ¬ BL x []
  BL_read : ∀ {x h k} (y : E), (PSWith mid x).Reachable h → (PSWith mid x).after h = some (.read k) →
    ¬ BL x h → ¬ BL x (h ++ [Ev.read y])
  BL_commit : ∀ {x h ht w k} (word : LeanVM.Protocol.Compile.Word), (PSWith mid x).Reachable h →
    (PSWith mid x).after h = some (.commit ht w k) → WellShaped w word → ¬ BL x h →
    ¬ BL x (h ++ [Ev.commit ht w word])
  BL_group : ∀ {x h p}, (PSWith mid x).Reachable h → Boundary h → (PSWith mid x).after h = some p →
    ((∃ k, p = .sample k) ∨ (∃ i ps k, p = .query i ps k)) → ¬ BL x h →
    esc (fun h' => ¬ BL x h') h p ≤ (((2 : ℝ≥0)⁻¹ ^ 132 : ℝ≥0) : ℝ≥0∞)
  /-- The extraction map. -/
  ext : Digest → List UInt8 → List Ev → Wit
  extract : ∀ {c x h}, okS vk c x = true → (PSWith mid x).Reachable h →
    (PSWith mid x).after h = some (.ret true) → ExtI mid Good x h → ¬ BL x h →
    (∀ h', h' <+: h → Boundary h' → ¬ BL x h') → Rel (accV VS vk) c (ext c x h)

end Lvm.ASM
