-- WP-14 (ASM). New for lvm (BLUEPRINT §7.1–7.2, A15, A16): the `S` branch's scheme for WP-5's
-- compiler, the top-level shape of the IOP verifier `P_S`, the doom root, the witness of an
-- accepted `S` proof, and a generic `KCert` from a whole-program `Spec` (leanVM
-- `Spec.toCertOfLead`, `LV/formal/lean_vm/LeanVM/Protocol/Compile/SpecRules/Cert.lean`, ported as
-- `LvmSpecRulesCert`; the top-level shape follows leanVM `EndToEnd/Sound/Assemble.lean`'s
-- `realSpec`: the commitments' doom, then the phases, then the stacked openings).
import LvmSubmission
import LvmCompileCodec
import LvmSpecRulesCert
import LvmWhirParams
import LvmWhirParams24
import LvmWhirParamsG
import LvmWhirParamsJ
import LvmWhirParamsJp
import LvmWhirParamsJ23
import LvmWhirDoom
import LvmFrontMech

/-!
# The `S` branch's certificate: the scheme, `P_S`, the doom root

**The scheme** `schemeS vk P` (WP-5 `Scheme`, BLUEPRINT §2.1–2.2): the statement is the header from
byte 8 (`hdrLen = 5,976` bytes, absorbed by the seed: `enc = id`); `hdrS π` accepts a proof of
`piSz` bytes starting `'S' 0^7` and splits it into that header and the body; `okS vk c x` is
`V_S`'s native header check (`parseOk`) with the specification hashes, minus what `hdrS` checks;
`q₀ = "lvm/1\0\0"`; `E` scalars, `K` words and challenges by WP-5's codec (`eOfBytes`, `kOfBytes`,
`chalOf`); the cap level is `8` for `C_main`'s root (`2^19` leaves, lvm2 S2) and `7` for every other tree
(`cfgMain24G`/`cfgRec20G`, BLUEPRINT §3.1).

**`P_S`** (`PSWith mid x`, BLUEPRINT §5, WP-11a's `decideProg` order): the roots of `C_main` and
`C_rec` (`commitRootUd`), the middle phases `mid x` (bus, tables, `CH` GKR with its caller claims
and link, `KS` GKR and sponge link; they return the claims on `C_rec` and on `C_main`), then
`C_rec`'s two-level opening (lvm2 S4: it commits `C_rec`'s level-1 oracle) and `C_main`'s
four-level opening (WP-7 `verifyStackedUd`; A16: `C_rec` first), then `true`.

**The doom root** (`CommitDoomS Good x h`): no pair of candidates of the two committed words (the
codewords within the threshold, WHIR `Candidates`; lvm2 J2′: both at the Johnson radius) is a witness of
the M3 instance `Good x` (the arithmetisation: bus, LoopIR tables, `CH`, `KS`, links, boundaries).

**`witOf x child`**: the witness an accepted `S` proof proves (BLUEPRINT §1): `leaf s n` for
`b = 0`; for `b = 1`, the node of the left child `child` and the right `W` leaf
`⟨encode (leaf s n), [], σ_leaf⟩`.

**`kcertOfSpec`**: a `KCert` (WP-5) from a specification of every statement's program from no doom
(`Spec … (fun _ ↦ False) (b = false) εm L 0`, as leanVM's `leanVmSpec`; the doom is created at the
root commitments), no proof of work, a luck predicate and an extraction (`LuckExt`): doom is the
specification's.
-/

set_option autoImplicit false

namespace Lvm.ASM

open RecursionFast Lvm.FS Lvm.T
open LeanVM.Parameters
open LeanVM.Protocol.Compile hiding Proof Bytes
open LeanVM.Protocol.Verifier LeanVM.Protocol.Whir.Sound LeanVM.Protocol.EndToEnd
open RecursionFast.WitnessSending (encode)
open scoped NNReal ENNReal

/-! ## The scheme -/

/-- The header bytes after byte 8 (the seed's statement bytes). -/
def hdrLen : ℕ := Lvm.headerBytes - 8

/-- Bytes 0–7 of an `S` proof: `'S'` and the zero pad. -/
def sPrefix : List UInt8 := [0x53, 0, 0, 0, 0, 0, 0, 0]

/-- **The header parser**: a proof of `piSz` bytes starting `'S' 0^7` is the statement (bytes
`8 … 4927`) and the body. -/
def hdrS (π : Proof) : Option (List UInt8 × List UInt8) :=
  if π.size = piSz ∧ π.data.toList.take 8 = sPrefix then
    some ((π.data.toList.drop 8).take hdrLen, π.data.toList.drop Lvm.headerBytes)
  else none

/-- The header fields of a statement (WP-11a's parser at the same offsets). -/
def hdrOf (x : List UInt8) : Lvm.Header := Lvm.Header.ofProof ⟨(List.replicate 8 0 ++ x).toArray⟩

/-- **The native statement check** (`parseOk` with the specification hashes): `b ∈ {0, 1}`, the
key's copy, `1 ≤ n ≤ 2^20`, the statement equation, and for `b = 1` the leaf signature. -/
def okS (vk c : Digest) (x : List UInt8) : Bool :=
  let hd := hdrOf x
  (hd.b == 0 || hd.b == 1) && hd.vk == vk && decide (1 ≤ hd.n) && decide (hd.n ≤ chainCap) &&
    (if hd.b = 0 then decide (c = leafStmt hd.h hd.n)
     else decide (c = nodeStmt hd.cL (leafStmt hd.h hd.n)) && SigOk vk (traceDigest []) hd.sig)

/-- The cap level of a tree of `2^ht` leaves: `8` for `C_main`'s root, `7` for the others (P20). -/
def capOfS (ht _w : ℕ) : ℕ := if ht = 19 then 8 else 7

/-- The occupied words of a commitment of `2^ht` rows of `w` words (Z2, after #17): `47` for `C_main`'s root
(`2^19` rows of 64 words; lvm2 roll 11, M′ `S2GM`: the stream block's 17 columns at stride `2^14` reach lane 46 of a
big step's 64 lanes of `2^17` words, a small step's end lower, so lanes 47–63 are empty in both shapes; B1 had 46,
roll 7 58), `35` for `C_rec`'s root (B1 only: M′ has no `C_rec`), the whole row for the others (P20; `occOfS_P20`
ties it to the schedule's rows). -/
def occOfS (ht w : ℕ) : ℕ := if ht = 19 ∧ w = 64 then 47 else if ht = 15 ∧ w = 64 then 35 else w

/-- **The `S` branch's scheme** for the program `P` under the key `vk`. -/
def schemeS (vk : Digest) (P : List UInt8 → VerifierProgram Bool) : Scheme where
  Stmt := List UInt8
  P := P
  enc := id
  enc_inj := Function.injective_id
  hdr := hdrS
  ok := okS vk
  capOf := capOfS
  q0 := Lvm.q0Bytes
  q0_short := by decide
  decE := eOfBytes
  decK := kOfBytes
  chal := chalOf
  chal_sum := chalOf_sum
  occ := occOfS

/-! ## `P_S` -/

/-- The claims the middle phases hand the openings: on `C_rec`, on `C_main`. -/
abbrev OpenClaims : Type :=
  List LeanVM.Protocol.Verifier.StackClaim × List LeanVM.Protocol.Verifier.StackClaim

/-- **The IOP verifier `P_S`** with the middle phases `mid` (lvm2 JB-VQP, J1: `C_main`'s opening at
the Johnson radius with OOD samples, `verifyStackedJ (cfgMain23Jq 3)`, `n₀ = 2` commitments before it;
lvm2 J2′ (J2C): `C_rec`'s opening at the Johnson radius with OOD samples, `verifyStackedJ cfgRec20Jp`; the
roots' shapes are unchanged: `cfgMain24G`'s root is `cfgMain23Jq`'s, `cfgRec20G`'s is `cfgRec20Jp`'s). -/
def PSWith (mid : List UInt8 → VerifierProgram OpenClaims) (x : List UInt8) : VerifierProgram Bool := do
  commitRootUd cfgMain24G
  commitRootUd cfgRec20G
  let cl ← mid x
  verifyStackedJ cfgRec20Jp cl.1
  verifyStackedJ (cfgMain23Jq 3) cl.2
  return true

/-! ## The doom root -/

/-- `C_main`'s threshold (level 0; lvm2 JB-VQP J1: the Johnson threshold, `(codesMain23Jq 0).thr`). -/
noncomputable def thrMain : ℕ := (codesMain23Jq 0).thr

/-- `C_rec`'s threshold (level 0; lvm2 J2′ (J2C): the Johnson threshold, `(codesRec20Jp 0).thr`, list
size at most `304`). -/
noncomputable def thrRec : ℕ := (codesRec20Jp 0).thr

/-- `C_rec`'s threshold is the one of J2′'s opening `verifyStackedJ cfgRec20Jp` (`StackedPreR`'s list). -/
theorem thrRec_eq : thrRec = (codesRec20Jp 0).thr := rfl

/-- The M3 witness relation on a candidate pair (`C_main`, `C_rec`) for a statement. -/
abbrev GoodRel : Type := List UInt8 → LeanVM.Protocol.Column CMain.nu20 → LeanVM.Protocol.Column 19 → Prop

/-- The candidate pairs of a history's two first commitments (`C_main` at rate `2^-2`, lvm2 roll 8 B1:
`codeJ17R2` at ν = 23; `C_rec` at rate `2^-2`). -/
def candPairs (h : List Ev) : Set (LeanVM.Protocol.Column CMain.nu20 × LeanVM.Protocol.Column 19) :=
  {p | p.1 ∈ Candidates CMain.nu20 2 thrMain (wordOf (commits h) 0) ∧
    p.2 ∈ Candidates 19 2 thrRec (wordOf (commits h) 1)}

/-- **The doom root**: no candidate pair of the committed words is a witness of the M3 instance. -/
def CommitDoomS (Good : GoodRel) (x : List UInt8) (h : List Ev) : Prop :=
  ∀ p ∈ candPairs h, ¬ Good x p.1 p.2

/-- The doom root is WP-2/WP-8's `Doomed` over the candidate pairs (so the phase specs, generic in
the candidate type `β` and the carried predicate, compose with it). -/
theorem commitDoomS_eq (Good : GoodRel) (x : List UInt8) :
    CommitDoomS Good x = LeanVM.Protocol.EndToEnd.Front.Doomed candPairs (fun p ↦ Good x p.1 p.2) := rfl

/-- The candidate pairs do not change along a run with no commitment (`LeanVM.Protocol.EndToEnd.Front.Stable`, the middle
phases' hypothesis). -/
theorem candPairs_stable : LeanVM.Protocol.EndToEnd.Front.Stable candPairs := by
  intro h₀ l hl
  simp only [candPairs, LeanVM.Protocol.Whir.Sound.commits_append, hl, List.append_nil]

/-- The shape of the two root commitments (heights, widths), and nothing else committed. -/
def RootShape (h : List Ev) : Prop :=
  ∃ Wm Wr, commits h = [(19, 64, Wm), (15, 64, Wr)] ∧ WellShaped 64 Wm ∧ WellShaped 64 Wr

/-- **The middle phases' postcondition** (in doom): every candidate pair fails a claim on `C_rec`
or on `C_main`, and the roots' shape is kept; the returned claims are multiaffine and at most
`2^63` per commitment (the WHIR specs' side conditions, `retInv` facts of the phases). -/
def OpenPost (cl : OpenClaims) (h : List Ev) : Prop :=
  (∀ p ∈ candPairs h, (∃ c ∈ cl.1, ¬ LeanVM.Protocol.EndToEnd.StackClaim.Holds 19 c p.2) ∨
    (∃ c ∈ cl.2, ¬ LeanVM.Protocol.EndToEnd.StackClaim.Holds CMain.nu20 c p.1)) ∧ RootShape h ∧
  (∀ c ∈ cl.1, IsMultiaffine 19 c.1) ∧ (∀ c ∈ cl.2, IsMultiaffine CMain.nu20 c.1) ∧
  cl.1.length ≤ 2 ^ 63 ∧ cl.2.length ≤ 2 ^ 40

/-- **`C_main`'s opening precondition before `C_rec`'s opening** (lvm2, S4): the two roots are
present, `C_main`'s root has level 0's shape, and every candidate of its word violates one of the
claims. `C_rec`'s two-level opening then adds one commitment, after which this is `C_main`'s
`StackedPreUd` (`stackedPreUd_of_mainPre`). -/
def MainPre (cl : List LeanVM.Protocol.Verifier.StackClaim)
    (cs : List (ℕ × ℕ × LeanVM.Protocol.Compile.Word)) : Prop :=
  cs.length = 2 ∧
    (∃ W, cs[0]? = some ((codesMain23Jq 0).κ + (codesMain23Jq 0).R,
      2 ^ LeanVM.Protocol.EndToEnd.laneBits, W) ∧ WellShaped (2 ^ LeanVM.Protocol.EndToEnd.laneBits) W) ∧
    ∀ q ∈ Candidates CMain.nu20 (codesMain23Jq 0).R (codesMain23Jq 0).thr (wordOf cs 0), ∃ c ∈ cl,
      ¬ LeanVM.Protocol.EndToEnd.StackClaim.Holds CMain.nu20 c q

/-- After one more commitment, `MainPre` is `C_main`'s opening precondition. -/
theorem stackedPreUd_of_mainPre {cl : List LeanVM.Protocol.Verifier.StackClaim}
    {cs l : List (ℕ × ℕ × LeanVM.Protocol.Compile.Word)} (h : MainPre cl cs) (hl : l.length = 1) :
    StackedPreUd (cfgMain23Jq 3).toUdConfig (codesMain23Jq 0) cl (cs ++ l) := by
  obtain ⟨hlen, ⟨W, hW, hws⟩, hc⟩ := h
  have h0 : 0 < cs.length := by omega
  have hw : wordOf (cs ++ l) 0 = wordOf cs 0 := by
    simp [wordOf, List.getElem?_append_left h0]
  refine ⟨by decide, by simp [hlen, hl, cfgMain23Jq], ⟨W, ?_, hws⟩, ?_⟩
  · show (cs ++ l)[0]? = _
    rw [List.getElem?_append_left h0]; exact hW
  · show ∀ q ∈ Candidates CMain.nu20 _ _ (wordOf (cs ++ l) 0), _
    rw [hw]; exact hc

/-- Candidates are antitone in the threshold. -/
theorem candidates_anti {μ R A A' : ℕ} {W : LeanVM.Protocol.Compile.Word} (hA : A ≤ A')
    {q : LeanVM.Protocol.Column μ} (hq : q ∈ Candidates μ R A' W) : q ∈ Candidates μ R A W :=
  let ⟨S, hS, hag⟩ := hq; ⟨S, hA.trans hS, hag⟩

/-- J2′'s threshold is below the unique-decoding one (`16,410 ≤ 20,480`): every UD candidate is one. -/
theorem thrRec_le_ud : thrRec ≤ (codesRec20 0).thr := by
  show (codesRec20Jp 0).thr ≤ (codesRec20 0).thr
  decide

/-- **The openings' precondition splits** (no unique decoding needed): if some candidate of
`C_rec` meets all its claims, every candidate of `C_main` fails one of its claims (`MainPre`). -/
theorem openPost_split {cl : OpenClaims} {h : List Ev} (hp : OpenPost cl h) :
    StackedPreUd cfgRec20G (codesRec20 0) cl.1 (commits h) ∨ MainPre cl.2 (commits h) := by
  obtain ⟨hpairs, ⟨Wm, Wr, hc, hWm, hWr⟩, -⟩ := hp
  by_cases hr : ∀ q ∈ Candidates 19 2 thrRec (wordOf (commits h) 1),
      ∃ c ∈ cl.1, ¬ LeanVM.Protocol.EndToEnd.StackClaim.Holds 19 c q
  · left
    exact ⟨by decide, by rw [hc]; rfl, ⟨Wr, by rw [hc]; rfl, hWr⟩,
      fun q hq ↦ hr q (candidates_anti thrRec_le_ud hq)⟩
  · right
    push Not at hr
    obtain ⟨qr, hqr, hall⟩ := hr
    refine ⟨by rw [hc]; rfl, ⟨Wm, by rw [hc]; rfl, hWm⟩, fun qm hqm => ?_⟩
    rcases hpairs (qm, qr) ⟨hqm, hqr⟩ with ⟨c, hc1, hn⟩ | h2
    · exact absurd (hall c hc1) hn
    · exact h2

/-- **Obligation `MidSpec`** (WP-8/9/10/11b phases, composed by WP-14): the middle phases, from the
doom root with the roots' shape, end in `OpenPost`, every group's escape at most `εm`, lead `Lm`,
for every follower's allowance `T ≤ εm`. -/
def MidSpec (mid : List UInt8 → VerifierProgram OpenClaims) (Good : GoodRel) (εm Lm : ℝ≥0∞) : Prop :=
  ∀ x (T : ℝ≥0∞), T ≤ εm →
    Nonempty (Spec (mid x) (fun h ↦ CommitDoomS Good x h ∧ RootShape h) OpenPost εm Lm T)

/-! ## The witness of an accepted `S` proof -/

/-- **The witness** of the statement `x` with left child `child` (BLUEPRINT §1). -/
def witOf (x : List UInt8) (child : Signed) : Wit :=
  let hd := hdrOf x
  if hd.b = 0 then .leaf hd.s hd.n
  else .node hd.cL (leafStmt hd.h hd.n) child ⟨encode (.leaf hd.s hd.n), [], hd.sig⟩

/-- **Obligation `NodeSound`** (the arithmetisation's soundness, BLUEPRINT §7.1 row 4; WP-8 chain
and sponge, WP-9 bus, WP-10 `loopir_sound`, WP-11b replay/`Q_arith_eq`, WP-12 `Q_sig`, assembled by
WP-14): a statement the header check accepts and a good candidate pair give the relation for the
witness whose left child is read from `C_rec`'s candidate (`child`, WP-13a's output map). -/
def NodeSound (VS : SProg) (vk : Digest) (Good : GoodRel) (child : LeanVM.Protocol.Column 19 → Signed) : Prop :=
  ∀ c x qm qr, okS vk c x = true → Good x qm qr → Rel (accV VS vk) c (witOf x (child qr))

/-! ## A knowledge certificate from a whole-program specification -/

/-- Luck and extraction for a scheme, given the doom predicate `D` of every statement's program
(`KCert`'s fields other than the doom certificate). -/
structure LuckExt (S : Scheme) (R : Digest → Wit → Prop) (D : S.Stmt → List Ev → Prop) where
  /-- Luck. -/
  B : S.Stmt → List Ev → Prop
  /-- The luck bound of a group. -/
  εB : ℝ≥0
  εB_lt_one : εB < 1
  B_nil : ∀ x, ¬ B x []
  B_read : ∀ {x h k} (y : E), (S.P x).Reachable h → (S.P x).after h = some (.read k) → ¬ B x h →
    ¬ B x (h ++ [Ev.read y])
  B_commit : ∀ {x h ht w k} (word : LeanVM.Protocol.Compile.Word), (S.P x).Reachable h →
    (S.P x).after h = some (.commit ht w k) → WellShaped w word → ¬ B x h →
    ¬ B x (h ++ [Ev.commit ht w word])
  B_group : ∀ {x h p}, (S.P x).Reachable h → Boundary h → (S.P x).after h = some p →
    ((∃ k, p = .sample k) ∨ (∃ i ps k, p = .query i ps k)) → ¬ B x h →
    esc (fun h' => ¬ B x h') h p ≤ εB
  /-- The extraction map. -/
  ext : Digest → S.Stmt → List Ev → Wit
  /-- Extraction from an accepting history, not lucky, outside doom at every boundary. -/
  extract : ∀ {c x h}, S.ok c x = true → (S.P x).Reachable h →
    (S.P x).after h = some (.ret true) → ¬ B x h → (∀ h', h' <+: h → Boundary h' → ¬ B x h') →
    (∀ h', h' <+: h → Boundary h' → ¬ D x h') → R c (ext c x h)

/-- **A knowledge certificate from a whole-program specification** (leanVM `Spec.toCert`, as
leanVM's `leanVmCert`: the specification starts from no doom, `Pre = False`, and the doom is created
by the root commitments): doom and escape bounds are the specification's; a program with no proof
of work has every escape bound at most `εm`. -/
noncomputable def kcertOfSpec {S : Scheme} {R : Digest → Wit → Prop} {εm : ℝ≥0} {L : ℝ≥0∞}
    (SP : ∀ x, Spec (S.P x) (fun _ ↦ False) (fun b _ ↦ b = false) (εm : ℝ≥0∞) L 0)
    (hstart : ∀ x, (SP x).D [] [] → (SP x).V [] [] ≤ εm) (hε1 : εm < 1)
    (hng : ∀ x h, (S.P x).Reachable h → grindBits h = 0)
    (LE : LuckExt S R fun x ↦ (SP x).D []) : KCert S R where
  cert x := (SP x).toCert
  ε := εm
  cert_ε x h hr _ _ := by
    have := (SP x).toCert_bound (hstart x) h
    rwa [hng x h hr, pow_zero, one_mul] at this
  ε_lt_one := hε1
  B := LE.B
  εB := LE.εB
  εB_lt_one := LE.εB_lt_one
  B_nil := LE.B_nil
  B_read := LE.B_read
  B_commit := LE.B_commit
  B_group := LE.B_group
  ext := LE.ext
  extract := LE.extract

/-- The certificate's doom is the specification's from the empty history. -/
theorem kcertOfSpec_D {S : Scheme} {R : Digest → Wit → Prop} {εm : ℝ≥0} {L : ℝ≥0∞}
    (SP : ∀ x, Spec (S.P x) (fun _ ↦ False) (fun b _ ↦ b = false) (εm : ℝ≥0∞) L 0)
    (hstart : ∀ x, (SP x).D [] [] → (SP x).V [] [] ≤ εm) (hε1 : εm < 1)
    (hng : ∀ x h, (S.P x).Reachable h → grindBits h = 0)
    (LE : LuckExt S R fun x ↦ (SP x).D []) (x : S.Stmt) :
    ((kcertOfSpec SP hstart hε1 hng LE).cert x).D = (SP x).D [] := rfl

/-- The certificate's error budget: groups at `2^-129` and luck at `2^-130` give `εFS ≤ 2^-128`
(WP-5 `εFS_le`). -/
theorem εFS_kcertOfSpec {S : Scheme} {R : Digest → Wit → Prop} {εm : ℝ≥0} {L : ℝ≥0∞}
    (SP : ∀ x, Spec (S.P x) (fun _ ↦ False) (fun b _ ↦ b = false) (εm : ℝ≥0∞) L 0)
    (hstart : ∀ x, (SP x).D [] [] → (SP x).V [] [] ≤ εm) (hε1 : εm < 1)
    (hng : ∀ x h, (S.P x).Reachable h → grindBits h = 0)
    (LE : LuckExt S R fun x ↦ (SP x).D []) (hεm : εm ≤ 7 * (2 : ℝ≥0)⁻¹ ^ 131)
    (hεB : LE.εB ≤ (2 : ℝ≥0)⁻¹ ^ 132) :
    Scheme.εFS (kcertOfSpec SP hstart hε1 hng LE) ≤ (2 : ℝ≥0)⁻¹ ^ 128 :=
  -- lvm2 JB-VQP: the exact budget `7·2^-131 + 2^-132 + 2^-139 ≤ 2^-128`
  Scheme.εFS_le_of _ ((add_le_add (add_le_add hεm hεB) le_rfl).trans (by
    rw [← NNReal.coe_le_coe]; push_cast; norm_num))

/-! ## `SSound` from the scheme -/

/-- **`SSound` from a knowledge certificate of `schemeS`**: `V_S` refines the compiled verifier
(obligation `refines`, WP-14 step 4) and `E` is the specification extractor on accepted proofs over
good logs (obligation `ext_eq`, WP-13a with WP-14). -/
theorem sSound_of (VS : SProg) (E : Digest → Proof → Log → Option Wit) (vk : Digest)
    (P : List UInt8 → VerifierProgram Bool) (K : KCert (schemeS vk P) (Rel (accV VS vk)))
    (hε : Scheme.εFS K ≤ (2 : ℝ≥0)⁻¹ ^ 128)
    (refines : ∀ L c π, isS π = true → (VS vk c π).runLog L = some true →
      ((schemeS vk P).V c π).runLog L = some true)
    (ext_eq : ∀ L c π, isS π = true → L.length ≤ logCap → Lvm.FS.Scheme.μ K L < 1 →
      ((schemeS vk P).V c π).runLog L = some true →
      (∃ w, E c π L = some w ∧ Rel (accV VS vk) c w) ∨ E c π L = (schemeS vk P).Ex K.ext c π L) :
    SSound VS E vk :=
  ⟨schemeS vk P, K, hε, refines, ext_eq⟩

/-! ## Controls -/

/-- (−) The header parser refuses a proof that does not start with `'S' 0^7`. -/
theorem hdrS_ctl : hdrS ⟨#[0x57]⟩ = none := by
  simp [hdrS, piSz, sPrefix]

/-- (+) `P_S` starts with the two root commitments (`C_main`: `2^19` leaves (lvm2 S2) of `64` words; `C_rec`:
`2^15` leaves of `64` words). -/
theorem PSWith_roots (mid : List UInt8 → VerifierProgram OpenClaims) (x : List UInt8) :
    ∃ k, PSWith mid x = .commit 19 64 (.commit 15 64 k) := ⟨_, rfl⟩

end Lvm.ASM
