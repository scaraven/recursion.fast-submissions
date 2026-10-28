-- New for `flock-recursive` (BLUEPRINT B-11 … B-15, §5.1; stage S-G13, items (f)/(g)): the frame
-- of revision 4.1's knowledge soundness. 3.x templates: `FRKState.kstate_of`/`ks_of`,
-- `FRXExt.Eout` (B-15 as built, S-H2n), `FRSoundnessAccRun.acc_W_all`.
import FRSoundness4Agg
import FRSoundness4Qry
import FRXSearch
import FRXSeed
import RecursionFast.Library.PaperTheorem

/-!
# Knowledge soundness of `V4with VsegC VnodeC` from a potential and two per-kind laws

**`E4 A`** is B-15's extractor (S-H2n, ruled 2026-10-28) on revision 4.1's kinds (`kindOf4`): a `W`
proof is decoded; an aggregate `A` gives its leaf witness `(s, n)` from its header and first
segment (`aggWit`); a node SNARK is searched under the key it carries (`search A (vkOf π) c`); a
bare segment or any other proof gives `none`.

**`finalLaw4`**: on a good log, every proof `V4with Vseg Vnode` accepts is extracted by `S.E`, given
* **`ExtOff S.E`**: `S.E` decodes a `W` proof and returns an aggregate's `aggWit` (`E4` meets it,
  `extOff_E4`; so does any extractor that agrees with `E4` off the node branch);
* **`NodeExtLog Vnode vk Good S.E (Rel (S.acc vk))`**: on an accepted node run on a good log, `S.E`
  returns a witness. At `E4` it follows from **`NodeSoundLog`** (the run carries the key `vk` and
  the statement has a witness), through `search_spec_acc` (`nodeExt_E4`);
* **`SegSoundLog Vseg vk Good`** (R-4-M1/M2, `FRSoundness4Agg`): an accepted segment run on a good
  log proves its chain step `chainEnd v.start v.n = v.h`;
* **`NodeSoundLog Vnode vk Good (Rel (S.acc vk))`**: an accepted node run on a good log carries the
  key `vk` and its statement has a witness of the relation.

**`ks4_of`**: with a potential `μ` that meets `KState`'s `empty` and `step` laws at `ε`, and the two
laws at `Good L := L.length ≤ logCap ∧ μ L < 1`, the textbook `KS` for `S.V = VC4 …` at `qV4`
(the query bound is `ks_queriesC4`); **`ks4_E4`** is it at `S.E = E4 S.acc`. `E4`'s node branch is
the search, which is not the certificate's fuel-bounded program: B-15's computable `E` uses the
extractor program's denotation on its domain, and that program's revision 4.1 form is S-H's. Its
correctness on accepted node runs is `NodeExtLog` at that `E`. **What is left for the revision 4.1 theorem is exactly**: the
potential and its `step` law (the doom chain at `seq4`, `FRSoundnessFrChain`/`FRSoundness4Pos`),
`SegSoundLog (VsegC impl₀)` per segment kind, and `NodeSoundLog (VnodeC implN cells)` per node kind.
-/

namespace FR.Rev4
open RecursionFast
open RecursionFast.WitnessSending (decode)
open scoped NNReal

/-- **The revision 4.1 extractor** (B-15 on `kindOf4`). -/
def E4 (A : Digest → Digest → Signed → Bool) (c : Digest) (π : Proof) (_L : Log) : Option Wit :=
  match kindOf4 π with
  | .W => decode π
  | .agg => (aggWit (piSizeOf seq4) π).map fun p => .leaf p.1 p.2
  | .node _ => X.search A (X.vkOf π) c
  | .bad => none

/-- **The node law**: an accepted node run on a good log carries the key `vk`, and its statement has
a witness of `R` (the node relation: two children `acc` accepts, B-13). -/
def NodeSoundLog (Vnode : NodeProgs) (vk : Digest) (Good : Log → Prop) (R : Digest → Wit → Prop) :
    Prop :=
  ∀ κ L c π, Good L → kindOf4 π = .node κ → (Vnode κ vk c π).runLog L = some true →
    X.vkOf π = vk ∧ ∃ w, R c w

/-- **The node law with an extractor `E`**: on an accepted node run on a good log, `E` returns a
witness of `R`. -/
def NodeExtLog (Vnode : NodeProgs) (vk : Digest) (Good : Log → Prop)
    (E : Digest → Proof → Log → Option Wit) (R : Digest → Wit → Prop) : Prop :=
  ∀ κ L c π, Good L → kindOf4 π = .node κ → (Vnode κ vk c π).runLog L = some true →
    ∃ w, E c π L = some w ∧ R c w

/-- What an extractor does off the node branch: decode a `W` proof, return an aggregate's leaf
witness `(s, n)` (`aggWit`). -/
def ExtOff (E : Digest → Proof → Log → Option Wit) : Prop :=
  (∀ c π L, kindOf4 π = .W → E c π L = decode π) ∧
    ∀ c π L s n, kindOf4 π = .agg → aggWit (piSizeOf seq4) π = some (s, n) → E c π L = some (.leaf s n)

theorem runLog_ret {b : Bool} {L : Log} (h : (OProg.ret b : OProg Bool).runLog L = some true) : b = true := by
  simpa [OProg.runLog] using h

/-- **The final law of revision 4.1**, for any extractor that decodes `W`, reads the aggregate's
leaf witness, and extracts on accepted node runs. -/
theorem finalLaw4 (Vseg : SegProgs) (Vnode : NodeProgs) (S : Submission) (vk : Digest)
    (hV : S.V = V4with Vseg Vnode) (hq : S.qV = qV4) (hE : ExtOff S.E) {Good : Log → Prop}
    (hS : SegSoundLog Vseg vk Good) (hN : NodeExtLog Vnode vk Good S.E (Rel (S.acc vk))) :
    ∀ L c π, Good L → (S.V vk c π).runLog L = some true → ∃ w, S.E c π L = some w ∧ Rel (S.acc vk) c w := by
  intro L c π hG h
  rw [hV] at h
  rcases hk : kindOf4 π with _ | _ | _ | κ
  · -- `W`: the decoded witness
    have hr : V4with Vseg Vnode vk c π = .ret true := by
      have h' := h; rw [V4_W Vseg Vnode vk c π hk] at h'; rw [V4_W Vseg Vnode vk c π hk, runLog_ret h']
    obtain ⟨w, hd, -, hw⟩ := V4_W_sound Vseg Vnode vk c π hk hr
    exact ⟨w, by rw [hE.1 c π L hk, hd], by rw [acc_eq4 Vseg Vnode S hV hq]; exact hw⟩
  · rw [V4_bad Vseg Vnode vk c π hk] at h; exact absurd (runLog_ret h) (by decide)
  · obtain ⟨s, n, ha, hn, hc⟩ := V4_agg_extract_log hk hS hG h
    exact ⟨.leaf s n, hE.2 c π L s n hk ha, hn, hc⟩
  · rw [V4_node Vseg Vnode vk c π hk] at h
    exact hN κ L c π hG hk h

/-- `E4` meets `ExtOff`. -/
theorem extOff_E4 (A : Digest → Digest → Signed → Bool) : ExtOff (E4 A) :=
  ⟨fun c π L hk => by rw [E4, hk], fun c π L s n hk ha => by rw [E4, hk, ha]; rfl⟩

/-- **`E4`'s node branch**: the search finds a witness under the run's key. -/
theorem nodeExt_E4 {Vnode : NodeProgs} {S : Submission} {vk : Digest} {Good : Log → Prop}
    (hq : S.qV = qV4) (hN : NodeSoundLog Vnode vk Good (Rel (S.acc vk))) :
    NodeExtLog Vnode vk Good (E4 S.acc) (Rel (S.acc vk)) := fun κ L c π hG hk h => by
  obtain ⟨hvk, hw⟩ := hN κ L c π hG hk h
  obtain ⟨w, hs, hr⟩ := X.search_spec_acc (A := S.acc) (vk := vk)
    (fun _ _ ha => X.sFits_of_acc (by rw [hq]; decide) ha) hw
  exact ⟨w, by rw [E4, hk, hvk]; exact hs, hr⟩

/-- **`KS` for revision 4.1's verifier** from a potential `μ` with the `empty` and `step` laws at
`ε`, `SegSoundLog` and `NodeExtLog` on the logs within `logCap` below potential `1`, for an
extractor meeting `ExtOff`. -/
theorem ks4_of (impl₀ : OpImpl) (implN : NodeKind → OpImpl) (cells : NodeKind → List ℕ)
    (S : Submission) (vk : Digest) (hV : S.V = VC4 impl₀ implN cells) (hq : S.qV = qV4)
    (hE : ExtOff S.E) {ε : ℝ≥0} (μ : Log → ℝ≥0) (h0 : μ [] = 0)
    (hstep : ∀ L q, L.length < logCap → μ L < 1 → q ∉ L.map Prod.fst →
      ∑ a : Digest, μ (L ++ [(q, a)]) ≤ (μ L + ε) * 2 ^ 256)
    (hS : SegSoundLog (VsegC impl₀) vk fun L => L.length ≤ logCap ∧ μ L < 1)
    (hN : NodeExtLog (VnodeC implN cells) vk (fun L => L.length ≤ logCap ∧ μ L < 1) S.E
      (Rel (S.acc vk))) :
    KS (Rel (S.acc vk)) (S.V vk) S.E ε S.qV :=
  KState.ks
    { μ := μ, empty := h0, step := hstep
      final := fun L c π hl hμ h => finalLaw4 (VsegC impl₀) (VnodeC implN cells) S vk hV hq hE hS hN
        L c π ⟨hl, hμ⟩ h }
    (ks_queriesC4 impl₀ implN cells S hV hq vk)

/-- **`ks4_of` at the specification extractor `E4 S.acc`** (`hE : S.E = E4 S.acc`): the node law
needs only the key and a witness (`NodeSoundLog`). -/
theorem ks4_E4 (impl₀ : OpImpl) (implN : NodeKind → OpImpl) (cells : NodeKind → List ℕ)
    (S : Submission) (vk : Digest) (hV : S.V = VC4 impl₀ implN cells) (hq : S.qV = qV4)
    (hE : S.E = E4 S.acc) {ε : ℝ≥0} (μ : Log → ℝ≥0) (h0 : μ [] = 0)
    (hstep : ∀ L q, L.length < logCap → μ L < 1 → q ∉ L.map Prod.fst →
      ∑ a : Digest, μ (L ++ [(q, a)]) ≤ (μ L + ε) * 2 ^ 256)
    (hS : SegSoundLog (VsegC impl₀) vk fun L => L.length ≤ logCap ∧ μ L < 1)
    (hN : NodeSoundLog (VnodeC implN cells) vk (fun L => L.length ≤ logCap ∧ μ L < 1)
      (Rel (S.acc vk))) :
    KS (Rel (S.acc vk)) (S.V vk) S.E ε S.qV :=
  ks4_of impl₀ implN cells S vk hV hq (hE ▸ extOff_E4 S.acc) μ h0 hstep hS (hE ▸ nodeExt_E4 hq hN)

/-! ## Controls -/

/-- (+) `E4` decodes a `W` proof. -/
theorem E4_W (A : Digest → Digest → Signed → Bool) (c : Digest) (w : Wit) (L : Log) :
    E4 A c (WitnessSending.encode w) L = decode (WitnessSending.encode w) := by
  rw [E4, kindOf4_encode]

/-- (−) An extractor that returns nothing fails `ExtOff` (at a `W` proof). -/
theorem not_extOff_none : ¬ ExtOff fun _ _ _ => none := fun h => by
  have := h.1 0 (WitnessSending.encode (.leaf 0 0)) [] (kindOf4_encode _)
  rw [WitnessSending.decode_encode (.leaf 0 0) (show (0 : ℕ) < 2 ^ 64 by norm_num)] at this; cases this

/-- (−) `E4` extracts nothing from a bare segment byte, nor from a node proof of the wrong size. -/
theorem E4_bad (A : Digest → Digest → Signed → Bool) (c : Digest) (L : Log) :
    E4 A c ⟨#[SegKind.L32.byte]⟩ L = none ∧ E4 A c ⟨#[NodeKind.N4.byte]⟩ L = none := by
  constructor <;> rfl

/-- (+) `NodeSoundLog` holds vacuously for a node program that never accepts. -/
theorem nodeSoundLog_false (vk : Digest) (Good : Log → Prop) (R : Digest → Wit → Prop) :
    NodeSoundLog (fun _ _ _ _ => .ret false) vk Good R := fun _ _ _ _ _ _ h => by
  simp [OProg.runLog] at h

/-- (−) `NodeSoundLog` fails for the accept-all node program at a relation with no witness. -/
theorem not_nodeSoundLog_true (vk : Digest) :
    ¬ NodeSoundLog (fun _ _ _ _ => .ret true) vk (fun _ => True) (fun _ _ => False) := fun h => by
  have hex : ∀ n, 1 ≤ n → ∃ π : Proof, byteAt π 0 = NodeKind.N4.byte ∧ π.size = n := by
    intro n hn
    refine ⟨⟨#[NodeKind.N4.byte] ++ Array.replicate (n - 1) 0⟩, ?_, ?_⟩
    · have h0 : 0 < (⟨#[NodeKind.N4.byte] ++ Array.replicate (n - 1) 0⟩ : ByteArray).size := by
        simp [ByteArray.size]
      rw [byteAt, dif_pos h0]
      simp [ByteArray.getElem_eq_getElem_data]
    · simp [ByteArray.size]; omega
  obtain ⟨π, hb, hs⟩ := hex (piSizeOf seq4) (by rw [piSizeOf_seq4]; decide)
  have hk : kindOf4 π = .node .N4 := by
    rw [kindOf4]; simp only [hb, NodeKind.ofByte?_byte, hs]; decide
  exact (h .N4 [] 0 π trivial hk rfl).2.elim fun _ h => h

end FR.Rev4
