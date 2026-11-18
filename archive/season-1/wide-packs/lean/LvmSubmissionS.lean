-- WP-14 (ASM). New for lvm: the current submission (V_S at P20, WP-13a's extractor) and its open
-- obligations, in the reduced form of the assembly (lvm2 J2′: `LvmCertSKJ.kcertSJ`, the INV certificate).
import LvmCertSKJ
import LvmCertSGood
import LvmXSpec
import LvmVerifier
import LvmVerifierS
import LvmCertS
import LvmSchedLit

-- (GOLF2: 2 declarations that `certified` does not use moved verbatim to `LvmSubmissionSOff`, outside its import closure.)

-- ===== merged from `LvmCertSQ` (GOLF module merge: `LvmCertSQ.lean` is now a stub importing `LvmSubmissionS`) =====
section
-- WP-14 (ASM). New for lvm (O1): the query bound of `V_S` on every oracle path, by a static count
-- of the schedule (the driver's loops are fixed by the schedule; only rejections stop early).

/-!
# The query bound of `V_S` (O1)

`qcItems p items b`: the queries the driver's items ask at most, `b` bounding the current
positions (`sample` 1; `positions r` its `nPosQ` FS queries, after which at most `t` positions;
`opening r` at most `b · (1 + path)`: a leaf and the path per position). By induction over
`climb`, `openLoop`, `posLoop`, `driveItems`: **`queries_VS_le`**, `|(VS p m vk c π).queries H| ≤
2 + qcItems p (schedule p) 0` for every oracle `H`; at P20 that is at most `16384`
(`qcItems_P20`, one kernel evaluation of the schedule, as `checks_P20`).
-/

set_option autoImplicit false

namespace Lvm

open RecursionFast

/-- **The static query count** of a list of items, with at most `b` current positions. -/
def qcItems (p : Params) : List Item → ℕ → ℕ
  | [], _ => 0
  | .read _ :: rest, b => qcItems p rest b
  | .readW _ _ :: rest, b => qcItems p rest b
  | .cap _ _ :: rest, b => qcItems p rest b
  | .sample :: rest, b => 1 + qcItems p rest b
  | .positions r :: rest, _ => (p.level r).nPosQ + qcItems p rest (p.level r).t
  | .opening r :: rest, b => b * (1 + (p.level r).path) + qcItems p rest b

section Bounds

variable (H : ByteArray → Digest) (π : ByteArray)

theorem q_climb (q : ℕ) : ∀ (j lvl : ℕ) (cur : Digest) (s : DSt) (k : DSt → Digest → OProg Bool)
    (K : ℕ), (∀ s' d, s'.pos = s.pos → ((k s' d).queries H).length ≤ K) →
    ((climb π q j lvl cur s k).queries H).length ≤ j + K
  | 0, _, cur, s, k, K, hk => by
    simp only [climb]; exact (hk s cur rfl).trans (by (clear * - K; omega))
  | j + 1, lvl, cur, s, k, K, hk => by
    simp only [climb, ask, OProg.queries, List.length_cons]
    refine (Nat.add_le_add_right (q_climb q j (lvl + 1) _ _ k K ?_) 1).trans ?_
    · exact fun s' d h ↦ hk s' d h
    · (clear * - j K; omega)

theorem q_openLoop (L : Level) (capOff : ℕ) : ∀ (qs : List ℕ) (s : DSt) (k : DSt → OProg Bool)
    (K : ℕ), (∀ s', s'.pos = s.pos → ((k s').queries H).length ≤ K) →
    ((openLoop π L capOff qs s k).queries H).length ≤ qs.length * (1 + L.path) + K
  | [], s, k, K, hk => by simp only [openLoop]; exact (hk s rfl).trans (by simp)
  | q :: qs, s, k, K, hk => by
    simp only [openLoop, ask, OProg.queries, List.length_cons]
    refine (Nat.add_le_add_right (q_climb H π q L.path 0 _ _ _ (qs.length * (1 + L.path) + K)
      ?_) 1).trans ?_
    · intro s' d h
      split
      · exact q_openLoop L capOff qs s' k K fun s'' h' ↦ hk s'' (h'.trans h)
      · simp [OProg.queries]
    · rw [Nat.add_mul, Nat.one_mul]
      (clear * - L qs K; omega)

theorem q_posLoop (h : ℕ) : ∀ (n rem : ℕ) (s : DSt) (k : DSt → OProg Bool) (K : ℕ),
    (∀ s', s'.pos.length ≤ s.pos.length + rem → ((k s').queries H).length ≤ K) →
    ((posLoop π h n rem s k).queries H).length ≤ n + K
  | 0, rem, s, k, K, hk => by simp only [posLoop]; exact (hk s (by omega)).trans (by omega)
  | n + 1, rem, s, k, K, hk => by
    simp only [posLoop, fsQuery, ask, OProg.queries, List.length_cons]
    refine (Nat.add_le_add_right (q_posLoop h n (rem - min positionsPerAnswer rem) _ k K ?_) 1).trans ?_
    · intro s' hs'
      refine hk s' ?_
      simp only [List.length_append, List.length_map, List.length_range] at hs'
      have := Nat.min_le_right positionsPerAnswer rem
      (clear * - s' s rem hs' this; omega)
    · (clear * - n K; omega)

theorem q_driveItems (p : Params) (k : DSt → OProg Bool) (K : ℕ)
    (hk : ∀ s, ((k s).queries H).length ≤ K) :
    ∀ (items : List Item) (b : ℕ) (s : DSt), s.pos.length ≤ b →
      ((driveItems p π items s k).queries H).length ≤ qcItems p items b + K
  | [], b, s, _ => by simp only [driveItems, qcItems]; exact (hk s).trans (by omega)
  | .read m :: rest, b, s, hs => by
    simp only [driveItems, qcItems]; exact q_driveItems p k K hk rest b _ hs
  | .readW m w :: rest, b, s, hs => by
    simp only [driveItems, qcItems]; exact q_driveItems p k K hk rest b _ hs
  | .cap c r :: rest, b, s, hs => by
    simp only [driveItems, qcItems]; exact q_driveItems p k K hk rest b _ hs
  | .sample :: rest, b, s, hs => by
    simp only [driveItems, qcItems, fsQuery, ask, OProg.queries, List.length_cons]
    refine (Nat.add_le_add_right (q_driveItems p k K hk rest b _ ?_) 1).trans ?_
    · exact hs
    · (clear * - p rest b K s; omega)
  | .positions r :: rest, b, s, _ => by
    simp only [driveItems, qcItems]
    refine (q_posLoop H π (p.level r).height (p.level r).nPosQ (p.level r).t { s with pos := [] }
      _ (qcItems p rest (p.level r).t + K) fun s' hs' ↦
        q_driveItems p k K hk rest (p.level r).t s' (by simpa using hs')).trans ?_
    (clear * - p r rest K b s; omega)
  | .opening r :: rest, b, s, hs => by
    simp only [driveItems, qcItems]
    split
    · simp [OProg.queries]
    · rename_i capOff _
      split
      · refine (q_openLoop H π (p.level r) capOff s.pos s _ (qcItems p rest b + K)
          fun s' hs' ↦ q_driveItems p k K hk rest b _ (by simpa [hs'] using hs)).trans ?_
        have hm := Nat.mul_le_mul_right (1 + (p.level r).path) hs
        (clear * - s p r rest b K hm; omega)
      · simp [OProg.queries]

end Bounds

/-- **The query bound of `V_S`** on every oracle path. -/
theorem queries_VS_le (p : Params) (m : M3) (vk c : Digest) (π : Proof) (H : ByteArray → Digest) :
    ((VS p m vk c π).queries H).length ≤ 2 + qcItems p (schedule p) 0 := by
  unfold VS
  split
  · simp only [drive, OProg.queries, List.length_cons]
    refine (Nat.add_le_add_right (Nat.add_le_add_right (q_driveItems H π p _ 0 (fun s ↦ by
      simp [OProg.queries]) (schedule p) 0 _ (by simp)) 1) 1).trans ?_
    (clear * - p; omega)
  · simp [OProg.queries]

/-- At P20 the static count is within the declared `qV`. -/
theorem qcItems_P20 : 2 + qcItems P20 (schedule P20) 0 ≤ 16384 := by
  rw [schedule, phases_P20_lit]; decide +kernel

/-- **O1**: `V_S` at P20 on any tables asks at most `qV = 16384` queries on every oracle path
(lvm2 S2-CERT: generic in the node program's tables; `VS20`'s is `LvmSubmissionS20.hq_VS20`). -/
theorem hq_VSL (tabs : Pub → List M3.Tab) (H : ByteArray → Digest) (vk c : Digest) (π : Proof) :
    ((VSL P20 tabs vk c π).queries H).length ≤ Lvm.T.qVlvm :=
  (queries_VS_le P20 _ vk c π H).trans qcItems_P20

end Lvm

namespace Lvm.ASM

end Lvm.ASM
end
-- ===== end of `LvmCertSQ` =====

/-!
# The submission and its open obligations

`submissionT tabs := subWith (VSL P20 tabs) (EX (accV (VSL P20 tabs))) extX`: `V_S` at P20 (WP-11a) on
the node program's tables `tabs` (lvm2 S2-CERT: generic; `LvmSubmissionS20`'s `submission` takes
`M3.tabsP20`), WP-13a's extractor program `extX` and its specification `EX` (the search branch
under `accV`).

**Closed** here: O1 the query bound (`hq_VSL`, `LvmCertSQ`), O2 `Computes extX (EX A) fuel`
(`computesX`), O3 the program's size (`extX_caps`),
O4 `EX` on `W` proofs (`EX_W`), O5a the knowledge certificate from its parts (`kcertSJ`), O7, O8, O9,
O11.

**`OpenS VS E`**, the obligations left (statements final; each a field):

| field | obligation | owner |
|---|---|---|
| `mid`, `Good`, `Lm`, `hmid`, `hLm` | O6: the middle phases' specification into `OpenPostR` (`MidSpecR`) | WP-8/9 phases, J2C-A |
| `hsh` | the middle phases commit nothing, grind nowhere, return multiaffine `C_rec` claims | WP-14 (structural) |
| `child`, `hnode` | O10: `NodeSound` | WP-8/9/10/11b/12, WP-14 assembles |
| `refines` | O5b: `V_S` accepting implies the compiled `S.V` accepting | WP-14a |
| `ext_eq` | O5c: on accepted `'S'` proofs over logs of potential below `1`, `E = S.Ex K.ext` or a witness | J2C-INT (`LvmCertSExq.ext_eq_SJ`) |
-/

set_option autoImplicit false

namespace Lvm.T

open RecursionFast Lvm.ASM
open RecursionFast.WitnessSending (encode decode encodeF)
open LeanVM.Protocol.Compile hiding Proof Bytes
open scoped NNReal ENNReal

/-- **The open obligations** of `subWith VS E ext`'s `S` branch. -/
structure OpenS (VS : SProg) (E : Digest → Proof → Log → Option Wit) : Type where
  /-- The middle phases of `P_S`. -/
  mid : List UInt8 → VerifierProgram OpenClaims
  /-- The M3 relation on a candidate pair. -/
  Good : GoodRel
  /-- The middle phases' lead. -/
  Lm : ℝ≥0∞
  /-- O6 (lvm2 J2′): the middle phases from the roots' shape into `OpenPostR` (the non-good pairs). -/
  hmid : MidSpecR mid Good εS Lm
  hLm : Lm ≤ εS
  /-- The middle phases' shape. -/
  hsh : MidShape mid
  /-- The left child read from `C_rec`'s candidate. -/
  child : LeanVM.Protocol.Column 19 → Signed
  /-- O10: the arithmetisation's soundness. -/
  hnode : ∀ vk, NodeSound VS vk Good child
  /-- O5b: `V_S` refines the compiled verifier. -/
  refines : ∀ vk L c π, isS π = true → (VS vk c π).runLog L = some true →
    ((schemeS vk (PSWith mid)).V c π).runLog L = some true
  /-- O5c: the extractor is the specification extractor on good logs (`final_good` gives the
  replayed history's facts there), or returns a witness (WP-14d: FR's search outside the
  extractor's domain, which a log entry of `≥ 2^64` bytes or a tape over `2^64` words reaches). -/
  ext_eq : ∀ vk L c π, isS π = true → L.length ≤ logCap →
    Lvm.FS.Scheme.μ (kcertSJ hmid hLm hsh (extJ hsh (hnode vk))) L < 1 →
    ((schemeS vk (PSWith mid)).V c π).runLog L = some true →
    (∃ w, E c π L = some w ∧ Rel (accV VS vk) c w) ∨
      E c π L = (schemeS vk (PSWith mid)).Ex (kcertSJ hmid hLm hsh (extJ hsh (hnode vk))).ext c π L

/-- **`SSound` from the open obligations.** -/
theorem sSound_of_openS {VS : SProg} {E : Digest → Proof → Log → Option Wit} (o : OpenS VS E)
    (vk : Digest) : SSound VS E vk :=
  sSound_of VS E vk (PSWith o.mid) (kcertSJ o.hmid o.hLm o.hsh (extJ o.hsh (o.hnode vk)))
    (εFS_kcertSJ o.hmid o.hLm o.hsh (extJ o.hsh (o.hnode vk))) (o.refines vk)
    fun L c π hS hl hμ hv ↦ o.ext_eq vk L c π hS hl hμ hv

/-! ## The submission on the node program's tables `tabs`

lvm2 S2-CERT: everything below is generic in the tables `tabs` of `V_S`'s M3 instance (the node
program's), so the certificate does not depend on the program's data; `LvmSubmissionS20` takes
`tabs := M3.tabsP20` (`submission`, `Open`, `certificateR_open`). -/

/-- `V_S` at P20 on the tables `tabs`. -/
abbrev VSt (tabs : Lvm.Pub → List Lvm.M3.Tab) : SProg := Lvm.VSL Lvm.P20 tabs

/-- The extractor specification: WP-13a's `EX` with the search branch under `accV (VSt tabs)`. -/
def EXt (tabs : Lvm.Pub → List Lvm.M3.Tab) : Digest → Proof → Log → Option Wit :=
  Lvm.X.EX (accV (VSt tabs))

/-- **The submission on the tables `tabs`**: `V_S` at P20, WP-13a's extractor. -/
def submissionT (tabs : Lvm.Pub → List Lvm.M3.Tab) : Submission := subWith (VSt tabs) (EXt tabs) Lvm.X.extX

/-- O4: on witness-sending proofs `EX` decodes (WP-13a `EX_W`). -/
theorem EXt_W (tabs : Lvm.Pub → List Lvm.M3.Tab) (c : Digest) (π : Proof) (L : Log)
    (h : isS π = false) : EXt tabs c π L = decode π := by
  refine Lvm.X.EX_W _ c π L fun h0 ↦ ?_
  have : π.data.getD 0 0 = 0x53 := by
    rw [Array.getD_eq_getD_getElem?, h0]; rfl
  simp [isS, this, sByte] at h

/-- **The open obligations of the submission on `tabs`.** -/
abbrev OpenT (tabs : Lvm.Pub → List Lvm.M3.Tab) : Type := OpenS (VSt tabs) (EXt tabs)

/-- **The certificate of the submission on `tabs`** against `claim.json`, from its open
obligations. -/
theorem certificateR_openT (tabs : Lvm.Pub → List Lvm.M3.Tab) (o : OpenT tabs) :
    CertificateR ⟨(1 : ℝ≥0) / 340282366920938463463374607431768211456, (0 : ℝ≥0) / 1, 16384,
      fun t => 70368744177664 + 8192 * t⟩ (submissionT tabs) :=
  certificateR_claim (VSt tabs) (EXt tabs) Lvm.X.extX
    ⟨fun H vk c π _ ↦ Lvm.hq_VSL tabs H vk c π, Lvm.X.computesX _, Lvm.X.extX_caps.2, EXt_W tabs,
      sSound_of_openS o⟩

end Lvm.T
