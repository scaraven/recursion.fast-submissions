-- G6: this module also holds the former modules `FRSoundness4XFinal`, `FRSoundness4P4fObl`, `FRSoundness4RsvCtrl` (one section each, in import order).
import FRSoundness4XLaws
import FRXDec4F0
import FRSoundnessCoreFront
import FRSoundness4R4W0

section G6_FRSoundness4XFinal

-- New for `flock-recursive` (BLUEPRINT revision 4.1, B-11 … B-15, §5; stage X4, items 4–5): the
-- knowledge soundness of `V4with VsegC VnodeC` with every remaining gap a named hypothesis, and the
-- map onto the contract's `Certificate` (core `6d05d00`).
-- RET-2: import re-pointed at Core: `FRKState` → `FRSoundnessCoreRows`.

/-!
# `ks_rev4`: revision 4.1's knowledge soundness, composed

**`ks_rev4`** is the contract's `KS` for `VC4 impl₀ (implN4F base) cells4` (the segment programs
under `implSeg impl₀`, the node programs under INT-9's `implN4F`), the extractor
`S.E = E4X nd S.acc` (S-H3) and the error `S.ε = εR`. It is S-H3's `ks4_E4X` at T4's potential
`muT` of the composed front (`frontObl_X`, `muT_laws_of_front`), with
* the segment law from `segSound_X`;
* `NodeSoundLog` from S-E12a's `nodeLaws4C'`, its per-run truths from `nodeRun_X`.

**Its hypotheses are exactly the named residuals** (`X4-RESULT.md`, with owners):
* `hHi : FrontHi DFhi`: phases 13 … 25 of the front (P4b's unrun item 2);
* `hRun : RunFacts4 …`: the program layer's run facts (R4's `acceptTail4_of_run` assembled with
  R4h's `pf0`/`enc`/`fin`, the `not_rej*` theorems, and the statement views);
* `hI`, `hRes`: S-E's slot interface `I` at the node rows and its residual `NodeResid4`;
* `D : NodeDec4 nd`, `hL`: S-H4's node decoder and its links on the domain;
* the definitional hypotheses `hV`, `hq`, `hE`, `hε` that fix the submission.

**`certificate_rev4`** builds the contract's `Certificate` from `ks_rev4` (for every key), the
completeness (a named residual), `computes4` (`DecOk4 nd`, S-H4's) and the caps (`epsR_le_errorCap`,
`ext4_caps`).
-/

namespace FR.Snd.X4
open RecursionFast FR.Rev4 FR.X.X4
open scoped NNReal

set_option linter.constructorNameAsVariable false

/-- **The node laws at the concrete node programs**, from the front's residual, the run facts and
S-E's slot interface (`nodeLaws4C'`). -/
theorem nodeSound_X (impl₀ : OpImpl) (implN : NodeKind → OpImpl) (S : Submission) (vk : Digest)
    (hV : S.V = VC4 impl₀ implN N4c.cells4) (hq : S.qV = qV4) {DFhi : ℕ → Log → Log → Prop}
    (hHi : FrontHi DFhi) (hRun : RunFacts4 (VsegC impl₀) (VnodeC implN N4c.cells4) vk)
    (I : N4c.SlotIface4 (VsegC impl₀) (VnodeC implN N4c.cells4)) (rd : N4c.Read4)
    (hI : I.lrows = lRows4 ∧ I.irows = nodeIRows4)
    (hRes : ∀ κ w c₁ c₂, N4c.StmtN4 κ (lRows4 κ) (nodeIRows4 κ) vk c₁ c₂ w →
      N4c.NodeResid4 I rd κ vk c₁ c₂ w) :
    NodeSoundLog (VnodeC implN N4c.cells4) vk (GoodX DFhi) (Rel (S.acc vk)) := by
  obtain ⟨hl, hi⟩ := hI
  refine (N4c.nodeLaws4C' impl₀ implN N4c.cells4 S vk hV hq I rd (fun _ _ _ _ h => h) ?_ ?_).1
  · rw [hl, hi]; exact nodeRun_X hHi hRun
  · rw [hl, hi]; exact hRes

/-- **`KS` for revision 4.1's verifier** at the extractor `E4X nd S.acc` and `S.ε = εR`; every
hypothesis after `hε` is a named residual (`X4-RESULT.md`). -/
theorem ks_rev4 (impl₀ : OpImpl) (base : NodeKind → OpImpl) (S : Submission) (vk : Digest)
    (hV : S.V = VC4 impl₀ (NI4F.implN4F base) N4c.cells4) (hq : S.qV = qV4)
    {nd : X.XIR} (hE : S.E = E4X nd S.acc) (hε : S.ε = epsR)
    {DFhi : ℕ → Log → Log → Prop} (hHi : FrontHi DFhi)
    (hRun : RunFacts4 (VsegC impl₀) (VnodeC (NI4F.implN4F base) N4c.cells4) vk)
    (I : N4c.SlotIface4 (VsegC impl₀) (VnodeC (NI4F.implN4F base) N4c.cells4)) (rd : N4c.Read4)
    (hI : I.lrows = lRows4 ∧ I.irows = nodeIRows4)
    (hRes : ∀ κ w c₁ c₂, N4c.StmtN4 κ (lRows4 κ) (nodeIRows4 κ) vk c₁ c₂ w →
      N4c.NodeResid4 I rd κ vk c₁ c₂ w)
    (D : NodeDec4 nd)
    (hL : ∀ κ L c π, GoodX DFhi L → kindOf4 π = .node κ → X.InDomE c π L →
      (VnodeC (NI4F.implN4F base) N4c.cells4 κ vk c π).runLog L = some true →
      ∃ es, D.Links κ L es π c ∧ Rel (S.acc vk) c (D.readW κ L es)) :
    KS (Rel (S.acc vk)) (S.V vk) S.E S.ε S.qV := by
  have hF := T4.muT_laws_of_front (frontObl_X hHi)
  rw [hε]
  exact ks4_E4X impl₀ (NI4F.implN4F base) N4c.cells4 S vk hV hq D hE _ hF.1 hF.2
    (segSound_X hHi hRun) (nodeSound_X impl₀ _ S vk hV hq hHi hRun I rd hI hRes) hL

/-! ## The contract's `Certificate` -/

/-- **The residuals of `ks_rev4` at one key** (everything but the submission's definition). -/
structure Resid4 (impl₀ : OpImpl) (base : NodeKind → OpImpl) (S : Submission) (nd : X.XIR)
    (D : NodeDec4 nd) (DFhi : ℕ → Log → Log → Prop) (vk : Digest) : Prop where
  run : RunFacts4 (VsegC impl₀) (VnodeC (NI4F.implN4F base) N4c.cells4) vk
  slots : ∃ (I : N4c.SlotIface4 (VsegC impl₀) (VnodeC (NI4F.implN4F base) N4c.cells4))
    (rd : N4c.Read4), (I.lrows = lRows4 ∧ I.irows = nodeIRows4) ∧
      ∀ κ w c₁ c₂, N4c.StmtN4 κ (lRows4 κ) (nodeIRows4 κ) vk c₁ c₂ w →
        N4c.NodeResid4 I rd κ vk c₁ c₂ w
  links : ∀ κ L c π, GoodX DFhi L → kindOf4 π = .node κ → X.InDomE c π L →
    (VnodeC (NI4F.implN4F base) N4c.cells4 κ vk c π).runLog L = some true →
      ∃ es, D.Links κ L es π c ∧ Rel (S.acc vk) c (D.readW κ L es)

/-- **The contract's `Certificate` for the revision 4.1 submission**: `secure` from `ks_rev4`,
`computes` from S-H3's `computes4`, the caps from `epsR_le_errorCap` and `ext4_caps`; the
completeness and `δ`'s cap are named hypotheses. -/
theorem certificate_rev4 (impl₀ : OpImpl) (base : NodeKind → OpImpl) (S : Submission) {nd : X.XIR}
    (hV : S.V = VC4 impl₀ (NI4F.implN4F base) N4c.cells4) (hq : S.qV = qV4)
    (hE : S.E = E4X nd S.acc) (hε : S.ε = epsR) (hext : S.ext = ext4With nd) (hfuel : S.fuel = X.fuel)
    (hnd : DecOk4 nd) (D : NodeDec4 nd) {DFhi : ℕ → Log → Log → Prop} (hHi : FrontHi DFhi)
    (hR : ∀ vk, Resid4 impl₀ base S nd D DFhi vk)
    (hC : ∀ vk, CompleteWithError (Rel (S.acc vk)) (S.P vk) (S.V vk) S.δ)
    (hδ : S.δ ≤ completenessCap) : Certificate S where
  secure vk := by
    obtain ⟨hrun, ⟨I, rd, hI, hRes⟩, hL⟩ := hR vk
    exact ks_rev4 impl₀ base S vk hV hq hE hε hHi hrun I rd hI hRes D hL
  complete := hC
  computes := by rw [hext, hE, hfuel]; exact computes4 hnd S.acc
  cap := by
    obtain ⟨hf, hs⟩ := ext4_caps hnd
    refine ⟨hε ▸ epsR_le_errorCap, hδ, by rw [hq, qV4]; norm_num, fun t => ?_, by rw [hext]; exact hs⟩
    rw [hfuel]; exact hf t

end FR.Snd.X4

end G6_FRSoundness4XFinal

section G6_FRSoundness4P4fObl

-- New for `flock-recursive` (BLUEPRINT revision 4.1, A.10 rows Lr1 … B′ → P1.0, §5.1–§5.2; stage
-- P4f): X4's residual 1, `FrontHi DFhi`, from P4b's phase lemmas and T4's frames. 3.x's
-- `FRSoundnessFrObl` is the template, P4a's `FRSoundness4P4aDF` the form (one `seq4` certificate).

/-!
# `FrontHi DFhi`: the front's obligations at positions 170 … 331

* **`frontClsHi_check`**: one checked classification of the `seq4` positions `170 … 331` (by
  item): every absorb is a boundary of `absPtsHi` or a round absorb of `rndPhHi`, every single
  squeeze one of `sqPtsHi` or a round squeeze; the phases at the boundary points (`ph_checkHi`), the
  rounds phases by `phOf4_eq` from their starts.
* The fields: **`ms_hi`** (Lr1, E1, RS1 are `msD`), **`habs_hi`**, **`handoff_hi`** (B′'s `DB4` is
  T4's `D1 W0X c0X 0` after P1.0's first absorb, with `ipW_eq` and `fTab_F`), **`hsingle_hi`**,
  **`hfin_hi`** (Lr1's and E1's zerocheck charges `lr4_zc_count`/`e4_zc_count`, RS1's
  `rs1_hfin4`, framed by `hfin_frame`), **`hstab_hi`**, **`chain_hi`** (`dfhi_ss`).
* **`frontHi_X : X4.FrontHi DFhi`**; **`frontObl_P4f`**, **`frontChainStab_P4f`** and
  **`ks_rev4F`** (X4's `ks_rev4` without `hHi`).
-/

namespace FR.Snd.P4f
open RecursionFast FR.Merkle FR.Rev4 Finset FR.Impl
open scoped NNReal

set_option linter.constructorNameAsVariable false

/-! ## The classification of positions 170 … 331 -/

/-- The boundary absorbs `(p, phOf4 (p − 1), phOf4 p)` from 170 on. -/
def absPtsHi : List (ℕ × ℕ × ℕ) :=
  [(179, 13, 14), (213, 14, 15), (227, 17, 18), (273, 18, 19), (275, 20, 21), (325, 21, 22),
    (326, 22, 23)]

/-- The single squeezes outside a rounds phase from 170 on. -/
def sqPtsHi : List (ℕ × ℕ × ℕ) := [(214, 15, 16), (274, 19, 20), (331, 24, 25)]

/-- The rounds phases `(b, end, k)` from 170 on: phase `k` runs from `b` to `end`. -/
def rndPhHi : List (ℕ × ℕ × ℕ) := [(179, 213, 14), (227, 273, 18), (275, 325, 21)]

def rndClsHi (par p : ℕ) : Bool :=
  rndPhHi.any fun x => decide (x.1 < p) && decide (p < x.2.1) && (p - x.1) % 2 == par

/-- **A position's class** by its item. -/
def frontClsHi (p : ℕ) : Item → Bool
  | .squeeze => fsRnd4 p != none || sqPtsHi.any (fun x => p == x.1) || rndClsHi 1 p
  | .absorb _ => absPtsHi.any (fun x => p == x.1) || rndClsHi 0 p
  | _ => true

/-- **Checked: every `seq4` position from 170 to 331 has its class.** -/
theorem frontClsHi_check :
    ((fsItems4.take 332).zipIdx).all (fun x => decide (x.2 < 170) || frontClsHi x.2 x.1) = true := by
  unfold frontClsHi rndClsHi absPtsHi sqPtsHi rndPhHi fsRnd4
  rw [fsRanges4_eq, fsItems4, Rev4.seq4_eq]; decide +kernel

/-- **Checked: the phases at the boundary points**, and the rounds phases' starts and ends. -/
theorem ph_checkHi : ((absPtsHi ++ sqPtsHi).all fun x =>
      phOf4 (x.1 - 1) == x.2.1 && phOf4 x.1 == x.2.2) = true ∧
    (rndPhHi.all fun x => phStart4 x.2.2 == x.1 && phStart4 (x.2.2 + 1) == x.2.1) = true := by
  unfold absPtsHi sqPtsHi rndPhHi phOf4 phStart4; rw [fsStarts4_eq]; decide +kernel

theorem frontClsHi_of {p : ℕ} {it : Item} (h1 : 170 ≤ p) (hp : p < 332) (h : fsItems4[p]? = some it) :
    frontClsHi p it = true := by
  have hc := frontClsHi_check
  rw [List.all_eq_true] at hc
  have := hc (it, p) (List.mem_zipIdx_iff_getElem?.mpr (by simp [hp, h]))
  simpa [show ¬ p < 170 by omega] using this

theorem pt_phHi {x : ℕ × ℕ × ℕ} (hx : x ∈ absPtsHi ++ sqPtsHi) :
    phOf4 (x.1 - 1) = x.2.1 ∧ phOf4 x.1 = x.2.2 := by
  have := List.all_eq_true.mp ph_checkHi.1 x hx
  simpa only [Bool.and_eq_true, beq_iff_eq] using this

theorem rnd_phHi {x : ℕ × ℕ × ℕ} (hx : x ∈ rndPhHi) {p : ℕ} (h1 : x.1 < p) (h2 : p < x.2.1) :
    phOf4 (p - 1) = x.2.2 ∧ phOf4 p = x.2.2 := by
  have hs := List.all_eq_true.mp ph_checkHi.2 x hx
  simp only [Bool.and_eq_true, beq_iff_eq] at hs
  have hk : x.2.2 < 51 := by
    simp only [rndPhHi, List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl | rfl <;> norm_num
  exact ⟨P4a.phOf4_eq hk (by omega) (by omega), P4a.phOf4_eq hk (by omega) (by omega)⟩

theorem abs_clsHi {p len : ℕ} (h1 : 170 ≤ p) (hp : p < 332) (h : fsItems4[p]? = some (.absorb len)) :
    (∃ x ∈ absPtsHi, p = x.1 ∧ phOf4 (p - 1) = x.2.1 ∧ phOf4 p = x.2.2) ∨
    ∃ x ∈ rndPhHi, x.1 < p ∧ p < x.2.1 ∧ (p - x.1) % 2 = 0 ∧ phOf4 (p - 1) = x.2.2 ∧
      phOf4 p = x.2.2 := by
  have hc := frontClsHi_of h1 hp h
  simp only [frontClsHi, rndClsHi, Bool.or_eq_true, List.any_eq_true, Bool.and_eq_true,
    beq_iff_eq, decide_eq_true_eq] at hc
  rcases hc with ⟨x, hx, h1⟩ | ⟨x, hx, ⟨h1, h2⟩, h3⟩
  · have := pt_phHi (List.mem_append_left _ hx); subst h1
    exact Or.inl ⟨x, hx, rfl, this⟩
  · exact Or.inr ⟨x, hx, h1, h2, h3, rnd_phHi hx h1 h2⟩

theorem sq_clsHi {p : ℕ} (h1 : 170 ≤ p) (hp : p < 332) (h : fsItems4[p]? = some .squeeze)
    (hr : fsRnd4 p = none) :
    (∃ x ∈ sqPtsHi, p = x.1 ∧ phOf4 (p - 1) = x.2.1 ∧ phOf4 p = x.2.2) ∨
    ∃ x ∈ rndPhHi, x.1 < p ∧ p < x.2.1 ∧ (p - x.1) % 2 = 1 ∧ phOf4 (p - 1) = x.2.2 ∧
      phOf4 p = x.2.2 := by
  have hc := frontClsHi_of h1 hp h
  simp only [frontClsHi, rndClsHi, hr, Bool.or_eq_true, List.any_eq_true, Bool.and_eq_true,
    beq_iff_eq, decide_eq_true_eq, bne_self_eq_false, Bool.false_eq_true, false_or] at hc
  rcases hc with ⟨x, hx, h1⟩ | ⟨x, hx, ⟨h1, h2⟩, h3⟩
  · have := pt_phHi (List.mem_append_right _ hx); subst h1
    exact Or.inl ⟨x, hx, rfl, this⟩
  · exact Or.inr ⟨x, hx, h1, h2, h3, rnd_phHi hx h1 h2⟩

/-- The multi-squeeze phases entered between 170 and 331: Lr1, E1, RS1. -/
theorem fsRanges_hi {s0 r : ℕ} (hmem : (s0, r) ∈ fsRanges4) (h1 : 170 ≤ s0 + 1)
    (h2 : s0 + 1 < 332) : (s0 = 169 ∧ r = 9) ∨ (s0 = 214 ∧ r = 12) ∨ (s0 = 326 ∧ r = 4) := by
  rw [fsRanges4_eq] at hmem
  simp only [List.mem_cons, Prod.mk.injEq, List.not_mem_nil, or_false] at hmem
  rcases hmem with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ |
    ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ |
    ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> simp_all

/-- `phOf4_eq` at known starts. -/
theorem phOf4_at {k p a b : ℕ} (hk : k < 51) (ha : phStart4 k = a) (hb : phStart4 (k + 1) = b)
    (h1 : a ≤ p) (h2 : p < b) : phOf4 p = k :=
  P4a.phOf4_eq hk (by omega) (by omega)

/-- The phases around the multi-squeeze entries (`phOf4_eq` at the starts). -/
theorem ph_msHi : phOf4 169 = 12 ∧ phOf4 170 = 13 ∧ phOf4 214 = 16 ∧ phOf4 215 = 17 ∧
    phOf4 326 = 23 ∧ phOf4 327 = 24 := by
  obtain ⟨h12, h13, h14, -, h16, h17, h18, -, -, -, -, h23, h24, h25, -⟩ := phStart_hi
  exact ⟨phOf4_at (by norm_num) h12 h13 (by norm_num) (by norm_num),
    phOf4_at (by norm_num) h13 h14 (by norm_num) (by norm_num),
    phOf4_at (by norm_num) h16 h17 (by norm_num) (by norm_num),
    phOf4_at (by norm_num) h17 h18 (by norm_num) (by norm_num),
    phOf4_at (by norm_num) h23 h24 (by norm_num) (by norm_num),
    phOf4_at (by norm_num) h24 h25 (by norm_num) (by norm_num)⟩

/-! ## `ms` -/

theorem ms_hi : ∀ s0 r, (s0, r) ∈ fsRanges4 → 170 ≤ s0 + 1 → s0 + 1 < T4.p1Start 0 →
    ∃ fin, X4.DFX DFhi (phOf4 (s0 + 1)) = msD (X4.DFX DFhi (phOf4 s0)) fin s0 r := by
  intro s0 r hmem h1 h2
  rw [X4.p1Start_zero4] at h2
  obtain ⟨p169, p170, p214, p215, p326, p327⟩ := ph_msHi
  rcases fsRanges_hi hmem h1 h2 with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · rw [p170, p169, X4.DFX_hi (by norm_num), X4.DFX_lo (by norm_num)]; exact ⟨_, rfl⟩
  · rw [p215, p214, X4.DFX_hi (by norm_num), X4.DFX_hi (by norm_num)]; exact ⟨_, rfl⟩
  · rw [p327, p326, X4.DFX_hi (by norm_num), X4.DFX_hi (by norm_num)]; exact ⟨_, rfl⟩

/-! ## `habs` -/

/-- **`FrontHi.habs`**: at every absorb from 170 to 331, the doom of the previous position gives a
failed check (`RejF4b`'s end checks, `finE` (iv), RS0's slices) or the next position's doom. -/
theorem habs_hi : ∀ L es x len, G.Matches (es ++ [x]) → fsItems4[es.length]? = some (.absorb len) →
    170 ≤ es.length → es.length < T4.p1Start 0 → ¬ T4.RejC X4.RejFX X4.c0X L es →
      X4.DFX DFhi (phOf4 (es.length - 1)) L es →
        T4.RejC X4.RejFX X4.c0X L (es ++ [x]) ∨ X4.DFX DFhi (phOf4 es.length) L (es ++ [x]) := by
  intro L es x len _ hit h1 hp _ hd
  rw [X4.p1Start_zero4] at hp
  have ap := fun {Q : Log → Log → Prop} {q : ℕ} (h : T4.Reads q Q) (hq : q ≤ es.length) =>
    h.append L es [x] hq
  rcases abs_clsHi h1 hp hit with ⟨⟨q, a, b⟩, hy, he, ha, hb⟩ |
    ⟨⟨q, e, k⟩, hy, hq, he, hpar, ha, hb⟩
  · simp only [absPtsHi, List.mem_cons, Prod.mk.injEq, List.not_mem_nil, or_false] at hy
    dsimp only at he ha hb
    rw [ha] at hd; rw [hb]
    rcases hy with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ |
      ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ <;>
      rw [X4.DFX_hi (by norm_num)] at hd ⊢
    · -- 179: Lr1's end into Lr2
      simp only [DFhi, msD, if_neg (show ¬ es.length ≤ 169 + 9 by omega)] at hd
      right; simp only [DFhi]
      rcases hd with h | h
      · exact .inl ((ap rd_bg12X (by omega)).mpr h)
      · exact .inr (P4b.lr4_habs_outer X4.src4 NI4F.srcL4 x he h)
    · -- 213: Lr end (`finLr` (ii))
      simp only [DFhi] at hd
      rcases hd with h | h
      · right; simp only [DFhi]; exact .inl ((ap rd_bg12X (by omega)).mpr h)
      · rcases P4b.lr4_habs_end X4.src4 NI4F.srcL4 x he h with h' | h'
        · exact .inl (.inl (.inr (.inl h')))
        · right; simp only [DFhi]; exact .inr h'
    · -- 227: E1's end into E2
      simp only [DFhi, msD, if_neg (show ¬ es.length ≤ 214 + 12 by omega)] at hd
      right; simp only [DFhi]
      rcases hd with h | h
      · exact .inl ((ap rd_bg16X (by omega)).mpr h)
      · exact .inr (P4b.e4_habs_outer X4.src4 NI4F.srcE4 x he h)
    · -- 273: E end (`finE` (ii))
      simp only [DFhi] at hd
      rcases hd with h | h
      · right; simp only [DFhi]; exact .inl ((ap rd_bg16X (by omega)).mpr h)
      · rcases P4b.e4_habs_end X4.src4 NI4F.srcE4 x he h with h' | h'
        · exact .inl (.inl (.inr (.inr (.inl h'))))
        · right; simp only [DFhi]; exact .inr h'
    · -- 275: E3 into E4
      simp only [DFhi] at hd
      right; simp only [DFhi]
      rcases hd with h | h
      · exact .inl ((ap rd_bg20X (by omega)).mpr h)
      · exact .inr (P4b.e4_habs_innerE X4.src4 NI4F.srcE4 NI4F.srcL4 x he h)
    · -- 325: E4 end (`finE` (iv)–(v))
      simp only [DFhi] at hd
      rcases hd with h | h
      · right; simp only [DFhi]; exact .inl ((ap rd_bg20X (by omega)).mpr h)
      · rcases P4b.e4_habs_end4 X4.src4 NI4F.srcE4 NI4F.srcL4 x he h with h' | h'
        · exact .inl (.inl (.inr (.inr (.inr (.inr (.inl h'))))))
        · right; simp only [DFhi]; exact .inr h'
    · -- 326: RS0 (the pending claims against the slices)
      rcases P4b.habs_RS0_4 (R := X4.src4) X4.okReads_X rd_far0X rd_PubX x he
        (dPend_X (by omega) hd) with h' | h'
      · exact .inl (.inl (.inr (.inr (.inr (.inr (.inr h'))))))
      · right; simp only [DFhi]; exact P4b.dRS0_4_mono (fun _ _ h => h.1) h'
  · simp only [rndPhHi, List.mem_cons, Prod.mk.injEq, List.not_mem_nil, or_false] at hy
    dsimp only at hq he hpar ha hb
    rw [ha] at hd; rw [hb]; right
    rcases hy with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ <;>
      rw [X4.DFX_hi (by norm_num)] at hd ⊢ <;> simp only [DFhi] at hd ⊢
    · exact hd.imp (ap rd_bg12X (by omega)).mpr
        (P4b.lr4_outer_append X4.src4 NI4F.srcL4 x (by omega) (Or.inl hpar)).mpr
    · exact hd.imp (ap rd_bg16X (by omega)).mpr
        (P4b.e4_outer_append X4.src4 NI4F.srcE4 x (by omega) (Or.inl hpar)).mpr
    · exact hd.imp (ap rd_bg20X (by omega)).mpr
        (P4b.e4_inner_appendE X4.src4 NI4F.srcE4 NI4F.srcL4 x (by omega) (Or.inl hpar)).mpr

/-! ## `hsingle` -/

/-- **P4b's `hrcells`** at `Rev4.rsvCells` (`rsvCells_ctl`): 60 cells on `N2`/`N4`, none on `N8`, inside
level 0. -/
theorem hrcellsX : ∀ ν, (Rev4.rsvCells ν).length = P4b.nRsv (.node ν) ∧
    ∀ c ∈ Rev4.rsvCells ν, c < 2 ^ P4b.ncR ν :=
  fun ν => ⟨by cases ν <;> rfl, fun c hc => (N4c.rsvCells_ctl.2.2.2.1 ν c hc).2.2⟩


open Classical in
/-- **`FrontHi.hsingle`**: at every single squeeze from 170 to 331 at most `239·2^128` answers
escape (Lr3 `2`, E3 `3`, B′ `10`, a round `2` or `3`). -/
theorem hsingle_hi : ∀ L es, G.Matches es → fsItems4[es.length]? = some .squeeze →
    fsRnd4 es.length = none → 170 ≤ es.length → es.length < T4.p1Start 0 →
      ¬ T4.RejC X4.RejFX X4.c0X L es →
        (univ.filter fun a => X4.DFX DFhi (phOf4 (es.length - 1)) L es ∧
          ¬ X4.DFX DFhi (phOf4 es.length) L (ext1 es a)).card ≤ 239 * 2 ^ 128 := by
  intro L es _ hit hrnd h1 hp hr
  rw [X4.p1Start_zero4] at hp
  rcases sq_clsHi h1 hp hit hrnd with ⟨⟨q, a, b⟩, hy, he, ha, hb⟩ |
    ⟨⟨q, e, k⟩, hy, hq, he, hpar, ha, hb⟩
  · simp only [sqPtsHi, List.mem_cons, Prod.mk.injEq, List.not_mem_nil, or_false] at hy
    dsimp only at he ha hb
    rw [ha, hb]
    rcases hy with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ <;>
      rw [X4.DFX_hi (by norm_num), X4.DFX_hi (by norm_num)]
    · -- 214: Lr3's `κ_L`
      refine le_trans (P4a.card_frame2_4 (U := P4b.EndBadLr4 X4.src4 NI4F.srcL4)
        (U' := P4b.BatBadLr4 X4.src4 NI4F.srcL4) rd_bg12X (by omega) (fun h => h) ?_)
        ((P4b.lr4_single_batch X4.src4 NI4F.srcL4 L es he).trans (by norm_num))
      intro a h
      simp only [DFhi, D16X, bg16X, bg12X] at h ⊢
      rcases h with (h | h) | h
      · exact .inl (.inl h)
      · exact .inr (.inl h)
      · exact .inl (.inr h)
    · -- 274: E3's `κ_E`
      have hc := (P4b.e4_single_batchE X4.src4 NI4F.srcE4 NI4F.srcL4 L es he).trans
        (show 4 * 2 ^ 128 ≤ 239 * 2 ^ 128 by norm_num)
      refine le_trans (P4a.card_frame2_4 (Bg := bg20X)
        (U := fun L es => P4b.EndBadE4 X4.src4 NI4F.srcE4 L es ∨ P4b.BatBadLr4 X4.src4 NI4F.srcL4 L es)
        (U' := P4b.BatBadE4 X4.src4 NI4F.srcE4 NI4F.srcL4) rd_bg20X (by omega) ?_ (fun _ h => h))
        (by convert hc using 3)
      intro h
      simp only [DFhi, bg16X] at h
      rcases h with (h | h) | h
      · exact .inl h
      · exact .inr (.inr h)
      · exact .inr (.inl h)
    · -- 331: B′'s `κ′`
      refine le_trans (P4a.card_frame2_4 (U := DRS1X) (U' := DBX) (T4.reads_false 0) (Nat.zero_le _)
        ?_ ?_) ((P4b.single_B4 (R := X4.src4) rd_far0X N4c.hcells4P4b hrcellsX L es he).trans
          (by norm_num))
      · intro h
        simp only [DFhi, msD, if_neg (show ¬ es.length ≤ 326 + 4 by omega)] at h
        exact .inr h
      · intro a h
        simp only [DFhi]
        exact h.elim False.elim id
  · simp only [rndPhHi, List.mem_cons, Prod.mk.injEq, List.not_mem_nil, or_false] at hy
    dsimp only at hq he hpar ha hb
    rw [ha, hb]
    rcases hy with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ <;>
      rw [X4.DFX_hi (by norm_num)]
    · exact le_trans (P4a.card_frame2_4 (U := P4b.D3Lr4 X4.src4 NI4F.srcL4)
        (U' := P4b.D3Lr4 X4.src4 NI4F.srcL4) rd_bg12X (by omega) (fun h => h) (fun _ h => h))
        ((P4b.lr4_single_outer X4.src4 NI4F.srcL4 L es).trans (by norm_num))
    · exact le_trans (P4a.card_frame2_4 (U := P4b.D3E4 X4.src4 NI4F.srcE4)
        (U' := P4b.D3E4 X4.src4 NI4F.srcE4) rd_bg16X (by omega) (fun h => h)
        (fun _ h => h)) ((P4b.e4_single_outer X4.src4 NI4F.srcE4 L es).trans (by norm_num))
    · exact le_trans (P4a.card_frame2_4 (U := P4b.D4E4 X4.src4 NI4F.srcE4 NI4F.srcL4)
        (U' := P4b.D4E4 X4.src4 NI4F.srcE4 NI4F.srcL4) rd_bg20X (by omega) (fun h => h)
        (fun _ h => h)) ((P4b.e4_single_innerE X4.src4 NI4F.srcE4 NI4F.srcL4 L es fun h =>
          hr (.inl (.inr (.inr (.inr (.inl h)))))).trans (by norm_num))

/-! ## `hfin` -/

open Classical in
/-- **A multi-squeeze phase's charge through its frame**: if the entry's doom is a background `Bg`
(read before the phase) or the unit's statement `U`, and the phase's final doom contains `Bg` and
the unit's final `U'`, the charge is the unit's count from `U` against escapes that clear `U'`. -/
theorem hfin_frame {Dk : ℕ → Log → Log → Prop} {s0 r : ℕ} (hmem : (s0, r) ∈ fsRanges4)
    {fin : Log → Log → Prop} (hfin : Dk (phOf4 (s0 + 1)) = msD (Dk (phOf4 s0)) fin s0 r)
    {Bg U U' : Log → Log → Prop} (hBg : T4.Reads (s0 + 1) Bg)
    (hprev : ∀ L es, Dk (phOf4 s0) L es → Bg L es ∨ U L es)
    (hfinI : ∀ L es, Bg L es ∨ U' L es → fin L es) {L es₀ : Log} (hl : es₀.length = s0 + 1)
    (hcnt : U L es₀ → (∀ as : List Digest, as.length = r → EscAtG (DPos (T4.Dp Dk)) L (ext es₀ as) →
      ¬ U' L (ext es₀ as)) → condCount (DPos (T4.Dp Dk)) L es₀ r [] ≤ deltaR) :
    condCount (DPos (T4.Dp Dk)) L es₀ r [] ≤ deltaR := by
  have esc : ∀ as : List Digest, as.length = r → EscAtG (DPos (T4.Dp Dk)) L (ext es₀ as) →
      U L es₀ ∧ ¬ U' L (ext es₀ as) := fun as has he => by
    obtain ⟨hd, hnf⟩ := T4.esc_msD hmem hfin hl as has he
    have hb : ¬ Bg L es₀ := fun hb => hnf (hfinI _ _ (.inl ((hBg.ext L es₀ as (by omega)).mpr hb)))
    exact ⟨(hprev _ _ hd).resolve_left hb, fun hu => hnf (hfinI _ _ (.inr hu))⟩
  by_cases hU : U L es₀
  · exact hcnt hU fun as has he => (esc as has he).2
  · rw [condCount_eq_zero fun as has he => hU (esc as has he).1]; exact zero_le

/-- Phase 12's doom is `bg12X` or Lr's statement (X4's `BgA4` split). -/
theorem df12_split {L es : Log} (h : P4a.DF4a X4.P4X 12 L es) :
    bg12X L es ∨ P4b.RowsBadLr4 X4.src4 NI4F.srcL4 L es := by
  simp only [P4a.DF4a, P4a.bg10_4] at h
  rcases h with ((h | h | h | h) | h | h | h) | h
  · exact .inl (.inl (.inl h))
  · exact .inl (.inl (.inr (.inl h)))
  · exact .inr h
  · exact .inl (.inr h)
  · exact .inl (.inl (.inr (.inr (.inl h))))
  · exact .inl (.inl (.inr (.inr (.inr (.inl h)))))
  · exact .inl (.inl (.inr (.inr (.inr (.inr (.inl h))))))
  · exact .inl (.inl (.inr (.inr (.inr (.inr (.inr h))))))

/-- **`FrontHi.hfin`**: Lr1's charge (`lr4_zc_count`, `≤ lrR κ/2^128`), E1's (`e4_zc_count`,
`≤ 24/2^128`: the M rows or the child claim, RSV2 §2.6), RS1's (`rs1_hfin4`, `≤ 10/2^128`). -/
theorem hfin_hi : ∀ s0 r, (s0, r) ∈ fsRanges4 → 170 ≤ s0 + 1 → s0 + 1 < T4.p1Start 0 → ∀ L es₀,
    G.Matches es₀ → es₀.length = s0 + 1 → ¬ T4.RejC X4.RejFX X4.c0X L es₀ →
      condCount (DPos (T4.Dp (X4.DFX DFhi))) L es₀ r [] ≤ deltaR := by
  intro s0 r hmem h1 h2 L es₀ _ hl _
  rw [X4.p1Start_zero4] at h2
  obtain ⟨p169, p170, p214, p215, p326, p327⟩ := ph_msHi
  rcases fsRanges_hi hmem h1 h2 with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · have hfin : X4.DFX DFhi (phOf4 (169 + 1)) = msD (X4.DFX DFhi (phOf4 169))
        (fun L es => bg12X L es ∨ P4b.ZCwLr4 X4.src4 NI4F.srcL4 L es) 169 9 := by
      rw [p170, p169, X4.DFX_hi (by norm_num), X4.DFX_lo (by norm_num)]; rfl
    refine hfin_frame (U := P4b.RowsBadLr4 X4.src4 NI4F.srcL4) hmem hfin rd_bg12X (fun L es h => ?_) (fun L es h => h) hl
      fun hU hesc => ?_
    · rw [p169, X4.DFX_lo (by norm_num)] at h; exact df12_split h
    · obtain ⟨κ, hk, -⟩ := id hU
      exact (P4b.lr4_zc_count X4.src4 NI4F.srcL4 hk hl hU hesc).trans
        (coord_le_deltaR (by have := (P4b.dims_le' κ).1; omega))
  · have hfin : X4.DFX DFhi (phOf4 (214 + 1)) = msD (X4.DFX DFhi (phOf4 214))
        (fun L es => bg16X L es ∨ P4b.ZCwE4 X4.src4 NI4F.srcE4 L es) 214 12 := by
      rw [p215, p214, X4.DFX_hi (by norm_num), X4.DFX_hi (by norm_num)]; rfl
    refine hfin_frame (U := fun L es => P4b.nE4 X4.src4 NI4F.srcE4 L es ∨ P4b.ChildBad4 NI4F.srcE4 L es)
      hmem hfin rd_bg16X (fun L es h => ?_) (fun L es h => h) hl fun hU hesc => ?_
    · rw [p214, X4.DFX_hi (by norm_num)] at h; exact h
    · obtain ⟨κ, hk, -⟩ : ∃ κ, kindOfC es₀ = .node κ ∧ True := by
        rcases hU with ⟨κ, hk, -⟩ | ⟨κ, hk, -⟩ <;> exact ⟨κ, hk, trivial⟩
      exact (P4b.e4_zc_count X4.src4 NI4F.srcE4 hk hl hU hesc).trans (coord_le_deltaR (by norm_num))
  · have hfin : X4.DFX DFhi (phOf4 (326 + 1)) = msD (X4.DFX DFhi (phOf4 326)) DRS1X 326 4 := by
      rw [p327, p326, X4.DFX_hi (by norm_num), X4.DFX_hi (by norm_num)]; rfl
    refine hfin_frame (Bg := fun _ _ => False) (U := DRS0X) hmem hfin (T4.reads_false _) (fun L es h => ?_)
      (fun L es h => h.elim False.elim id) hl fun hU hesc => ?_
    · rw [p326, X4.DFX_hi (by norm_num)] at h; exact .inr h
    · exact (P4b.rs1_hfin4 (R := X4.src4) rd_far0X (rd_PubRSX.mono (by norm_num)) hl hU hesc).trans
        (coord_le_deltaR (by norm_num))

/-! ## The handoff: B′ → P1.0 -/

theorem nrP0 (κ : CKind) : T4.nrP 0 κ = κ.m - 7 := by
  rcases κ with σ | ν <;> [cases σ; cases ν] <;> decide

/-- `W0X`, `c0X` read only the entries before P1.0 (`frontLocal4`). -/
theorem locX : T4.FrontLocal X4.W0X X4.c0X := fun L es L' es' _ hS hp =>
  P4b.frontLocal4 N4c.kf4 X4.cellsX L L' (hS.1.mono (by rw [← X4.p1Start_zero4]; exact hp))

/-- **`⟨W₀, f⁽⁰⁾⟩` in P1.0's form** on a close level-0 word (3.x's `ip_W0`): T4's `trueSum` of
`lvT W0X 0` is `ι` of B′'s `ipW` (`fTab_F`, `trueSum_tabs`). -/
theorem ip_W0X {L es : Log} (hnf : ¬ T4.farL (kindOfC es) L es 0) :
    trueSum e2 (T4.lvT X4.W0X 0 L es) (T4.nrP 0 (kindOfC es)) =
      algebraMap F K (P4b.ipW (P4b.wrsL4 N4c.kf4 (kindOfC es) es)
        (P4b.cellsC X4.cellsX (kindOfC es)) (P4b.kpL4 es) ((kindOfC es).m - 7) (X4.src4.fz L es)) := by
  rw [T4.lvT, trueSum_tabs, nrP0]
  simp only [T4.lvW, X4.W0X, P4b.W₀L4, T4.fTab_F hnf, ← map_mul, ← map_sum, P4b.ipW]
  rfl

/-- **`FrontHi.handoff`**: B′'s doom (`DB4`) is P1.0's doom `D1 0` after P1.0's first absorb
(3.x's `handoff_B`). -/
theorem handoff_hi : ∀ L es x len, G.Matches (es ++ [x]) → fsItems4[es.length]? = some (.absorb len) →
    es.length = T4.p1Start 0 → ¬ T4.RejC X4.RejFX X4.c0X L es → X4.DFX DFhi 25 L es →
      T4.RejC X4.RejFX X4.c0X L (es ++ [x]) ∨ T4.D1 X4.W0X X4.c0X 0 L (es ++ [x]) := by
  intro L es x len _ _ hl _ hd
  right
  rw [X4.DFX_hi (by norm_num)] at hd
  have hp := X4.p1Start_zero4
  have hS : T4.Same L (es ++ [x]) L es (T4.p1Start 0) := hl ▸ T4.same_append L es [x]
  have hk : kindOfC (es ++ [x]) = kindOfC es := hS.kind (by rw [hp]; norm_num)
  have hfar : T4.farL (kindOfC es) L (es ++ [x]) 0 ↔ T4.farL (kindOfC es) L es 0 :=
    T4.farL_same hS (i := 0) (by norm_num) _ (by rw [P4a.capPos_zero4, hp]; norm_num)
  have h0 : T4.hRnd (es ++ [x]) 0 = 0 := by simp [T4.hRnd, hl]
  unfold T4.D1
  rw [h0, T4.closeP_zero, not_not, hk, hfar]
  rcases hd with hd | ⟨hnf, hd⟩
  · exact .inl hd
  refine .inr ⟨hnf, by simp [hl], ?_⟩
  have ha : T4.ans3 (T4.p1Start 0) (T4.nrP 0) (es ++ [x]) = 0 := by simp [T4.ans3, hl]
  rw [ha]
  simp only [T4.Wrong2, clR2, T4.lvC, rchs2, List.range_zero, List.map_nil, bindAll, Nat.sub_zero, hk]
  rw [(locX L (es ++ [x]) L es _ hS le_rfl).2, T4.lvT_same locX hS (show 0 < 5 by norm_num) le_rfl,
    ip_W0X hnf]
  intro heq
  exact hd ((algebraMap F K).injective heq)

/-! ## `hstab` and `chain` -/

theorem len_stabExt {L : Log} {i : ℕ} {X : Log} (hX : StabExt fsRnd4 (entriesOf L (pathOf L i)) X) :
    1 ≤ X.length := by
  obtain ⟨s0, r, as, -, hs, -, rfl⟩ := hX
  rw [length_ext, List.length_take]; omega

/-- **`FrontHi.hstab`** (`dfhi_ss` on T4's `same_stabX`). -/
theorem hstab_hi : ∀ k, 12 < k → k < 26 → ∀ L i, ¬ Bad L → G.IsChain L i → ∀ X,
    StabExt fsRnd4 (entriesOf L (pathOf L i)) X → phOf4 (X.length - 1) = k →
      (DFhi k (L.take i) X ↔ DFhi k L X) := by
  intro k hk1 hk2 L i hb hci X hX hph
  have hX1 := len_stabExt hX
  obtain ⟨b1, -, -⟩ := T4.phOf_bounds (X.length - 1)
  rw [hph] at b1
  exact dfhi_ss k hk1 (by omega) _ _ X (by omega) (T4.same_stabX hb hci hX)

/-- **`FrontHi.chain`** (`dfhi_ss` on T4's `same_chain`). -/
theorem chain_hi : ∀ L j, ¬ Bad L → G.IsChain L j → ∀ k, 12 < k → k < 26 →
    phOf4 ((entriesOf L (pathOf L j)).length - 1) = k →
      (DFhi k (L.take j) (entriesOf L (pathOf L j)) ↔ DFhi k L (entriesOf L (pathOf L j))) := by
  intro L j hb hci k hk1 hk2 hph
  have h1 : 1 ≤ (entriesOf L (pathOf L j)).length :=
    List.length_pos_iff.mpr (G.matches_ne_nil hci.2)
  obtain ⟨b1, -, -⟩ := T4.phOf_bounds ((entriesOf L (pathOf L j)).length - 1)
  rw [hph] at b1
  exact dfhi_ss k hk1 (by omega) _ _ _ (by omega) (T4.same_chain hb hci)

/-! ## `FrontHi DFhi` -/

/-- **X4's residual 1**: the front's obligations at positions 170 … 331 for the concrete dooms. -/
theorem frontHi_X : X4.FrontHi DFhi where
  ms := ms_hi
  habs := habs_hi
  handoff := handoff_hi
  hsingle := hsingle_hi
  hfin := hfin_hi
  hstab := hstab_hi
  chain := chain_hi

/-- **T4's `FrontObl` at revision 4.1**, unconditionally (X4's `frontObl_X` at `frontHi_X`). -/
theorem frontObl_P4f : T4.FrontObl X4.RejFX (X4.DFX DFhi) X4.W0X X4.c0X := X4.frontObl_X frontHi_X

theorem frontChainStab_P4f : T4.FrontChainStab X4.RejFX (X4.DFX DFhi) :=
  X4.frontChainStab_X frontHi_X

/-! ## `ks_rev4` and `certificate_rev4` without residual 1 -/

section KS
open FR.X.X4

/-- **X4's `ks_rev4` with residual 1 discharged** (`frontHi_X`): `KS` for revision 4.1's verifier at
`E4X nd S.acc` and `εR`. Every hypothesis after `hε` is one of X4's residuals 2 … 6. -/
theorem ks_rev4F (impl₀ : OpImpl) (base : NodeKind → OpImpl) (S : Submission) (vk : Digest)
    (hV : S.V = VC4 impl₀ (NI4F.implN4F base) N4c.cells4) (hq : S.qV = qV4)
    {nd : X.XIR} (hE : S.E = E4X nd S.acc) (hε : S.ε = epsR)
    (hRun : X4.RunFacts4 (VsegC impl₀) (VnodeC (NI4F.implN4F base) N4c.cells4) vk)
    (I : N4c.SlotIface4 (VsegC impl₀) (VnodeC (NI4F.implN4F base) N4c.cells4)) (rd : N4c.Read4)
    (hI : I.lrows = lRows4 ∧ I.irows = nodeIRows4)
    (hRes : ∀ κ w c₁ c₂, N4c.StmtN4 κ (lRows4 κ) (nodeIRows4 κ) vk c₁ c₂ w →
      N4c.NodeResid4 I rd κ vk c₁ c₂ w)
    (D : NodeDec4 nd)
    (hL : ∀ κ L c π, X4.GoodX DFhi L → kindOf4 π = .node κ → X.InDomE c π L →
      (VnodeC (NI4F.implN4F base) N4c.cells4 κ vk c π).runLog L = some true →
      ∃ es, D.Links κ L es π c ∧ Rel (S.acc vk) c (D.readW κ L es)) :
    KS (Rel (S.acc vk)) (S.V vk) S.E S.ε S.qV :=
  X4.ks_rev4 impl₀ base S vk hV hq hE hε frontHi_X hRun I rd hI hRes D hL

/-- **X4's `certificate_rev4` with residual 1 discharged.** -/
theorem certificate_rev4F (impl₀ : OpImpl) (base : NodeKind → OpImpl) (S : Submission) {nd : X.XIR}
    (hV : S.V = VC4 impl₀ (NI4F.implN4F base) N4c.cells4) (hq : S.qV = qV4)
    (hE : S.E = E4X nd S.acc) (hε : S.ε = epsR) (hext : S.ext = ext4With nd) (hfuel : S.fuel = X.fuel)
    (hnd : DecOk4 nd) (D : NodeDec4 nd) (hR : ∀ vk, X4.Resid4 impl₀ base S nd D DFhi vk)
    (hC : ∀ vk, CompleteWithError (Rel (S.acc vk)) (S.P vk) (S.V vk) S.δ)
    (hδ : S.δ ≤ completenessCap) : Certificate S :=
  X4.certificate_rev4 impl₀ base S hV hq hE hε hext hfuel hnd D frontHi_X hR hC hδ

end KS

end FR.Snd.P4f

end G6_FRSoundness4P4fObl

section G6_FRSoundness4RsvCtrl

-- New for `flock-recursive` (revision 4.4.2, the reserve in RSV2's stacked form; RSV2 §5 item 8; track
-- RSV-S2b): the controls of the child claim (`truthChild4`, `ChildBad4`) and of the kind change.

/-!
# Controls of the reserve's child claim

* **`truthChild_pos`** (+): an honest child claim (`X = Σ_i s_i·M̃_i(p)`) on honest M rows is not
  doomed: `ChildBad4` fails, E1's table `zcE4` is zero, so `ZCwE4` fails at every `(τ, η)`.
* **`childBad_neg`** (−): the claim `X + 1` is in `ChildBad4` (`D = −1`); E1's table is nonzero
  (`zcT_ne`), and at the concrete point `τ = 0`, `η = 1` its extension is `−1`; on the log, `ZCwE4`
  holds at every `η ≠ 0`.
* **`kindChange_pos`** (+): the parent's sum over its own row coordinates with the claim's higher
  coordinates fixed is the stacked extension at the claim's point, for an `N2` parent (22
  coordinates; `N4`'s and `N8`'s matrices read 23: the fixed evaluation) and an `N4` parent (23;
  `N2`'s read 22: the constant extension), at any coefficients `s` (full support included); per
  matrix: `N2 ← N4` and `N4 ← N2` (`matMLE_hiRow` both ways).
* **`n8_zero`** (+): the zero claim (`N8`'s `fLrEnd[48, 1008) = 0`) is a true child claim.
-/

namespace FR.Snd.P4b
open RecursionFast FR.Merkle FR.Rev4 Finset

set_option linter.constructorNameAsVariable false

section
variable (R : FSrc) (srcE : NodeKind → ESrc)

/-- The reserve's readers are the claim's values: `p_x` at `0 … 22`, `p_y` at `23 … 47`, `s` at
`48 … 56`, `X` at `57`. -/
theorem child_rsvV (es : Log) :
    (∀ j, pxL es j = rsvV es j) ∧ (∀ j, pyL es j = rsvV es (23 + j)) ∧
      (∀ i, sL es i = rsvV es (48 + i)) ∧ xL es = rsvV es 57 := by
  refine ⟨fun j => rfl, fun j => ?_, fun i => ?_, rfl⟩
  · simp only [pyL, rsvV]; congr 1; ring
  · simp only [sL, rsvV]; congr 1; ring

/-- (+) **An honest child claim on honest M rows is never doomed by E1**: `ChildBad4` fails, E1's
table is `0`, and `ZCwE4` fails whatever `(τ, η)` was drawn. -/
theorem truthChild_pos {κ : NodeKind} {L es : Log} (hk : kindOfC es = .node κ)
    (htc : truthChild4 srcE es)
    (hrows : residual (entMat (srcE κ).ea (e2R κ) (ncR κ)) (entMat (srcE κ).eb (e2R κ) (ncR κ))
      (entMat (srcE κ).ec (e2R κ) (ncR κ)) (zCG R (ncR κ) L es) = 0) :
    ¬ ChildBad4 srcE L es ∧ zcE4 R srcE κ L es = 0 ∧ ¬ ZCwE4 R srcE L es := by
  have hD : dChild srcE es = 0 := (truthChild_iff srcE es).1 htc
  refine ⟨fun ⟨_, _, _, h⟩ => h htc, ?_, fun ⟨κ', hk', h⟩ => ?_⟩
  · funext u
    simp only [zcE4, Rsv.zcT, hrows, hD, zero_mul, add_zero, Pi.zero_apply]
    simp [mle]
  · rw [hk] at hk'
    cases hk'
    apply h
    show _ = _
    rw [hrows, hD, mul_zero, add_zero]
    simp [mle]

/-- (−) **The claim `X + 1` is caught** (RSV2 §5 item 8): it is in `ChildBad4` with defect `−1`; E1's
table is nonzero (`zcT_ne`), and its extension at the concrete point `τ = 0`, `η = 1` (coordinate 23)
is `−1` on honest M rows; on the log, `ZCwE4` holds at every `η ≠ 0`. -/
theorem childBad_neg {κ : NodeKind} {L es : Log} (hk : kindOfC es = .node κ) (hl : 214 ≤ es.length)
    (hX : xL es = mStack srcE (sL es) (pxL es) (pyL es) + 1)
    (hrows : residual (entMat (srcE κ).ea (e2R κ) (ncR κ)) (entMat (srcE κ).eb (e2R κ) (ncR κ))
      (entMat (srcE κ).ec (e2R κ) (ncR κ)) (zCG R (ncR κ) L es) = 0) :
    ChildBad4 srcE L es ∧ dChild srcE es = -1 ∧ zcE4 R srcE κ L es ≠ 0 ∧
      mle (zcE4 R srcE κ L es) (fun j => if j.val = 23 then 1 else 0) = -1 ∧
      (etaL es ≠ 0 → ZCwE4 R srcE L es) := by
  have hD : dChild srcE es = -1 := by rw [dChild, hX]; ring
  have hD0 : dChild srcE es ≠ 0 := by rw [hD]; exact neg_ne_zero.mpr one_ne_zero
  refine ⟨⟨κ, hk, hl, fun h => hD0 ((truthChild_iff srcE es).1 h)⟩, hD,
    Rsv.zcT_ne _ (dims_le' κ).2.1 (.inr hD0), ?_, fun he => ⟨κ, hk, ?_⟩⟩
  · rw [zcE4, Rsv.mle_zcT, hrows, hD]
    simp [mle]
  · show _ ≠ _
    rw [hrows, hD]
    simpa [mle] using he

end

/-! ## The kind change -/

/-- (+) **The kind change goes through** (RSV2 §2.5, the E2 sum at the mixed point): for an `N2` parent
(22 row coordinates) and an `N4` parent (23), at any coefficients `s` (full support included), the
sum over the parent's coordinates with the claim's higher ones fixed is the stacked extension at the
claim's point `p`. -/
theorem kindChange_pos (srcE : NodeKind → ESrc) (s p q : ℕ → F) :
    mle (fun x : Fin (2 ^ 22) => mStack srcE s (Rsv.hiPt (cube x) p) q) (Rsv.lowA 22 p) =
        mStack srcE s p q ∧
      mle (fun x : Fin (2 ^ 23) => mStack srcE s (Rsv.hiPt (cube x) p) q) (Rsv.lowA 23 p) =
        mStack srcE s p q := by
  refine ⟨?_, ?_⟩ <;> rw [mle_mStack_row, Rsv.hiPt_self]

/-- (+) **Per matrix, both directions**: `N2 ← N4` (a 22-coordinate parent, `N4`'s 23-coordinate
matrix: coordinate 22 is the claim's, fixed) and `N4 ← N2` (a 23-coordinate parent, `N2`'s
22-coordinate matrix: constant in coordinate 22). -/
theorem kindChange_mat (E : Eval.Entries) {b : ℕ} (p : ℕ → F) (σ : Fin b → F) :
    mle (fun x : Fin (2 ^ e2R .N2) => Eval.matMLE E (Rsv.lowA (e2R .N4) (Rsv.hiPt (cube x) p)) σ)
        (Rsv.lowA (e2R .N2) p) = Eval.matMLE E (Rsv.lowA (e2R .N4) p) σ ∧
      mle (fun x : Fin (2 ^ e2R .N4) => Eval.matMLE E (Rsv.lowA (e2R .N2) (Rsv.hiPt (cube x) p)) σ)
        (Rsv.lowA (e2R .N4) p) = Eval.matMLE E (Rsv.lowA (e2R .N2) p) σ := by
  refine ⟨?_, ?_⟩ <;> rw [Rsv.matMLE_hiRow, Rsv.hiPt_self]

/-- The two parents' row counts: `N2` sums over 22 coordinates, `N4` over 23 (so `kindChange_mat` is
the fixed evaluation one way and the constant extension the other). -/
theorem e2R_N2_N4 : e2R .N2 = 22 ∧ e2R .N4 = 23 := ⟨rfl, rfl⟩

/-! ## `N8`'s zero claim -/

/-- (+) **The zero claim is true** (`N8` writes `fLrEnd[48, 1008) = 0`): with every claim value `0`,
`X = 0 = Σ_i 0·M̃_i(p)`, so `truthChild4` holds and `ChildBad4` fails. -/
theorem n8_zero (srcE : NodeKind → ESrc) {L es : Log} (h0 : ∀ i < 60, rsvV es i = 0) :
    truthChild4 srcE es ∧ ¬ ChildBad4 srcE L es := by
  obtain ⟨-, -, hs, hx⟩ := child_rsvV es
  have hs0 : ∀ i < 9, sL es i = 0 := fun i hi => by rw [hs]; exact h0 _ (by omega)
  have ht : truthChild4 srcE es := by
    rw [truthChild4, hx, h0 57 (by norm_num)]
    simp only [mStack, NodeKind.all, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil]
    simp [hs0, NodeKind.ix]
  exact ⟨ht, fun ⟨_, _, _, h⟩ => h ht⟩

/-- (−) … and a nonzero `X` on zero coefficients is a false claim. -/
theorem n8_neg (srcE : NodeKind → ESrc) {es : Log} (hs : ∀ i < 9, sL es i = 0) (hx : xL es ≠ 0) :
    ¬ truthChild4 srcE es := by
  rw [truthChild4]
  simp only [mStack, NodeKind.all, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil]
  simpa [hs, NodeKind.ix] using hx

end FR.Snd.P4b

end G6_FRSoundness4RsvCtrl

section G6_FRNodeStmtR4

-- New for `flock-recursive` (revision 4.4.2, the reserve in RSV2's stacked form, §2.4; track RSV-S2b):
-- the node statement with the reserve's child claim (`StmtN4R`), its per-run input from the front
-- (`nodeRunR_X`), and the value form of slot 0's `evalM` discharge (`evalM_childV`).

/-!
# The node statement with the reserve's child claim

A node `P` with a previous node `C` replays `V(C)` in slot 0; `V(C)`'s one stacked `evalM` call has
three output registers, imports of `P`'s circuit (RSV2 §2.4). They are bound by three facts about
`P`'s own log, all of which an accepted run of `V(P)` on a good log gives:

* **`PubCellsR4`**: `f⁽⁰⁾` at `Rev4.rsvCells` is `P`'s child claim `ch = p_x ‖ p_y ‖ s ‖ X₃` (60
  values of Lrend's message; RS0's `Pub`, `PubRX`, refuted on the accepted prefix);
* **`truthChild4`**: `X = Σ_i s_i·M̃_i(p)` (E1's entry doom `D16X` refuted on the prefix);
* **`RsvZero`**: `X₃[1] = X₃[2] = 0` (`V(P)`'s two zero asserts, `RunFacts4.node`).

* **`truthChildV`**, **`StmtN4R`**: the two last facts on the value list `ch`, and `StmtN4 ∧
  PubCellsR4 ∧ truthChildV` (`StmtN4`'s signature is kept; `ch` is a binder). On `N8` the list is
  empty and both hold trivially (`truthChildV_nil`).
* **`nodeRunR_X`**: `nodeRun_X` with the reserve: an accepted node run on a good log meets
  `StmtN4R` at its own child claim.
* **`evalM_childV`**: the value form of the discharge: on a 32-entry row point and a column point
  whose entries are `ch`'s `p_x ‖ s` and `p_y`, the node's `evalM` returns `ch`'s `X₃` (`implN4F_hMX`).
-/

namespace FR.N4c
open RecursionFast Rev4 Circ Finset

/-! ## The child claim on its values -/

/-- The stacked extension at the claim's own values (`p_x = ch[0, 23)`, `p_y = ch[23, 48)`,
`s = ch[48, 57)`). -/
noncomputable def mStackV (srcE : NodeKind → Snd.P4b.ESrc) (ch : List F) : F :=
  Snd.P4b.mStack srcE (fun i => ch.getD (48 + i) 0) (fun j => ch.getD j 0) (fun j => ch.getD (23 + j) 0)

/-- **The child claim is true on its values**: `X = Σ_i s_i·M̃_i(p)` and `X₃[1] = X₃[2] = 0`. -/
def truthChildV (srcE : NodeKind → Snd.P4b.ESrc) (ch : List F) : Prop :=
  ch.getD 57 0 = mStackV srcE ch ∧ ch.getD 58 0 = 0 ∧ ch.getD 59 0 = 0

/-- **`StmtN4` with the reserve** (RSV2 §2.4): the node's truths, its reserve cells holding the child
claim `ch`, and the claim true (INT-9's M-row sources `srcE4`). -/
def StmtN4R (κ : NodeKind) (lr : List Circ.Row) (er : List (ℕ × Circ.Row)) (vk c₁ c₂ : Digest) (w : Asg)
    (ch : List F) : Prop :=
  StmtN4 κ lr er vk c₁ c₂ w ∧ PubCellsR4 κ w ch ∧ truthChildV NI4F.srcE4 ch

/-- (+) The empty claim (`N8`: no reserve cells) is true. -/
theorem truthChildV_nil (srcE : NodeKind → Snd.P4b.ESrc) : truthChildV srcE [] := by
  refine ⟨?_, rfl, rfl⟩
  simp only [mStackV, List.getD_nil, Snd.P4b.mStack, NodeKind.all, List.map_cons, List.map_nil,
    List.sum_cons, List.sum_nil, zero_mul, add_zero]

/-- `mStack` reads `s` below 9, `p` below 23 and `q` below 25. -/
theorem mStack_congr (srcE : NodeKind → Snd.P4b.ESrc) {s s' p p' q q' : ℕ → F}
    (hs : ∀ i < 9, s i = s' i) (hp : ∀ j < 23, p j = p' j) (hq : ∀ j < 25, q j = q' j) :
    Snd.P4b.mStack srcE s p q = Snd.P4b.mStack srcE s' p' q' := by
  have hlp : ∀ κ : NodeKind, Snd.Rsv.lowA (Snd.P4b.e2R κ) p = Snd.Rsv.lowA (Snd.P4b.e2R κ) p' :=
    fun κ => funext fun j => hp j (lt_of_lt_of_le j.isLt (Snd.P4b.dims_le' κ).2.1)
  have hlq : ∀ κ : NodeKind, Snd.Rsv.lowA (Snd.P4b.ncR κ) q = Snd.Rsv.lowA (Snd.P4b.ncR κ) q' :=
    fun κ => funext fun j => hq j (lt_of_lt_of_le j.isLt (Snd.P4b.dims_le' κ).2.2.1)
  simp only [Snd.P4b.mStack, NodeKind.all, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    hlp, hlq, NodeKind.ix]
  rw [hs 0 (by norm_num), hs 1 (by norm_num), hs 2 (by norm_num), hs 3 (by norm_num), hs 4 (by norm_num),
    hs 5 (by norm_num), hs 6 (by norm_num), hs 7 (by norm_num), hs 8 (by norm_num)]

/-- **The log's claim on its values**: a true `truthChild4` and the two zero outputs give
`truthChildV` of the reserve's values (`rsvL`; on `N8` the empty list). -/
theorem truthChildV_rsvL (srcE : NodeKind → Snd.P4b.ESrc) (κ : NodeKind) {es : Log}
    (ht : Snd.P4b.truthChild4 srcE es) (h58 : Snd.P4b.rsvV es 58 = 0) (h59 : Snd.P4b.rsvV es 59 = 0) :
    truthChildV srcE (Snd.P4b.rsvL (.node κ) es) := by
  cases hp : κ.hasPrev
  · have : Snd.P4b.rsvL (.node κ) es = [] := by simp [Snd.P4b.rsvL, Snd.P4b.nRsv, hp]
    rw [this]; exact truthChildV_nil srcE
  · have hg : ∀ i < 60, (Snd.P4b.rsvL (.node κ) es).getD i 0 = Snd.P4b.rsvV es i := fun i hi => by
      rw [List.getD_eq_getElem _ _ (by simp [Snd.P4b.rsvL, Snd.P4b.nRsv, hp, hi])]
      simp [Snd.P4b.rsvL]
    obtain ⟨hx, hy, hs, hX⟩ := Snd.P4b.child_rsvV es
    refine ⟨?_, by rw [hg 58 (by norm_num), h58], by rw [hg 59 (by norm_num), h59]⟩
    rw [hg 57 (by norm_num), ← hX, ht, mStackV]
    exact mStack_congr srcE (fun i hi => by rw [hs, hg _ (by omega)])
      (fun j hj => by rw [hx, hg _ (by omega)]) (fun j hj => by rw [hy, hg _ (by omega)])

/-! ## Slot 0's `evalM`, in values -/

/-- **The value form of slot 0's `evalM` discharge** (RSV2 §2.4, step 3): if the stacked call's row
point (32 entries) holds `ch`'s `p_x ‖ s` and its column point `ch`'s `p_y`, the node's `evalM` returns
`ch`'s `X₃` whenever the claim is true (`implN4F_hMX`, and `mStack`'s reads). -/
theorem evalM_childV (base : NodeKind → OpImpl) (ν : NodeKind) {ch : List F}
    (hT : truthChildV NI4F.srcE4 ch) {τ σ : Array F} (hτ : τ.size = 32)
    (hx : ∀ j < 23, τ.getD j 0 = ch.getD j 0) (hs : ∀ i < 9, τ.getD (23 + i) 0 = ch.getD (48 + i) 0)
    (hy : ∀ j < 25, σ.getD j 0 = ch.getD (23 + j) 0) :
    (NI4F.implN4F base ν).evalM τ σ = (ch.getD 57 0, ch.getD 58 0, ch.getD 59 0) := by
  have hpt : ∀ n (r : Array F), FR.Impl.ptA n r = Snd.Rsv.lowA n (fun j => r.getD j 0) := fun _ _ => rfl
  have key : (NodeKind.all.map fun κ => NI4F.dot3 (NI4F.sOf τ κ.ix)
      (Eval.matMLE (NI4F.srcE4 κ).ea (FR.Impl.ptA (Snd.P4b.e2R κ) τ) (FR.Impl.ptA (Snd.P4b.ncR κ) σ),
       Eval.matMLE (NI4F.srcE4 κ).eb (FR.Impl.ptA (Snd.P4b.e2R κ) τ) (FR.Impl.ptA (Snd.P4b.ncR κ) σ),
       Eval.matMLE (NI4F.srcE4 κ).ec (FR.Impl.ptA (Snd.P4b.e2R κ) τ) (FR.Impl.ptA (Snd.P4b.ncR κ) σ))).sum =
      ch.getD 57 0 := by
    rw [hT.1, mStackV, ← mStack_congr NI4F.srcE4 (s := fun i => τ.getD (23 + i) 0)
      (p := fun j => τ.getD j 0) (q := fun j => σ.getD j 0) hs hx hy]
    simp only [Snd.P4b.mStack, NodeKind.all, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
      NI4F.dot3, NI4F.sOf, NodeKind.ix, hpt]
  rw [NI4F.implN4F_hMX base ν τ σ hτ, key, hT.2.1, hT.2.2]

end FR.N4c

namespace FR.Snd.X4
open RecursionFast FR.Merkle FR.Rev4 Finset

/-! ## The per-run input with the reserve -/

theorem agree_takeN {es : Log} {n : ℕ} (h : n ≤ es.length) : Agree (es.take n) es n := by
  have e := agree_append (es.take n) (es.drop n) (n := n) (by simp; omega)
  rw [List.take_append_drop] at e
  exact fun p hp => (e p hp).symm

/-- The phase of positions 214 (Lr3's squeeze: E1's entry, `D16X`) and 326 (RS0's absorb, `DRS0X`). -/
theorem phOf4_214_326 : phOf4 214 = 16 ∧ phOf4 326 = 23 := by
  obtain ⟨-, -, -, -, h16, h17, -, -, -, -, -, h23, h24, -, -⟩ := P4f.phStart_hi
  exact ⟨P4a.phOf4_eq (by norm_num) (by rw [h16]) (by rw [h17]; norm_num),
    P4a.phOf4_eq (by norm_num) (by rw [h23]) (by rw [h24]; norm_num)⟩

/-- **An accepted chain's prefixes are not doomed at phases 16 and 23** (`tail_of_accept`): the child
claim is true after Lrend, and RS0's `Pub` (the nine public cells and the reserve's) holds. -/
theorem rsv_of_tail {L : Log} {j : ℕ} (hG : GoodX P4f.DFhi L) (hT : T4.AcceptTail RejFX W0X c0X L j)
    {κ : NodeKind} (hk : kindOfC (entriesOf L (pathOf L j)) = .node κ) :
    Snd.P4b.truthChild4 NI4F.srcE4 (entriesOf L (pathOf L j)) ∧
      Snd.P4b.PubOKR4 src4 Rev4.rsvCells L ((entriesOf L (pathOf L j)).take 327) := by
  have hlen : 327 ≤ (entriesOf L (pathOf L j)).length := by
    have := hT.len; rw [T4.capPh_pos.2.2.2] at this; omega
  obtain ⟨hnd, -⟩ := T4.tail_of_accept (frontObl_X P4f.frontHi_X).loc
    (frontChainStab_X P4f.frontHi_X) hG.2 hT
  generalize entriesOf L (pathOf L j) = es at hlen hnd hk ⊢
  obtain ⟨p214, p326⟩ := phOf4_214_326
  have hA : ∀ n, n ≤ es.length → Agree (es.take n) es n := fun n hn => agree_takeN hn
  have hkn : ∀ n, 3 ≤ n → n ≤ es.length → kindOfC (es.take n) = .node κ := fun n h3 hn =>
    (kindOfC_congr ((hA n hn).mono (by omega))).trans hk
  refine ⟨?_, ?_⟩
  · by_contra hc
    apply hnd 214 (by omega)
    refine .inr ?_
    have hl : (es.take (214 + 1)).length - 1 = 214 := by rw [List.length_take]; omega
    unfold DPos T4.Dp
    rw [hl, p214, T4.DkC, if_pos (by norm_num), DFX_hi (by norm_num)]
    refine .inr (.inr ⟨κ, hkn 215 (by norm_num) (by omega), by simp; omega, fun ht => hc ?_⟩)
    obtain ⟨h1, h2, h3, h4⟩ := Snd.P4b.child_agree (hA 215 (by omega)) (by norm_num)
    simpa only [Snd.P4b.truthChild4, h1, h2, h3, h4] using ht
  · by_contra hc
    apply hnd 326 (by omega)
    refine .inr ?_
    have hl : (es.take (326 + 1)).length - 1 = 326 := by rw [List.length_take]; omega
    unfold DPos T4.Dp
    rw [hl, p326, T4.DkC, if_pos (by norm_num), DFX_hi (by norm_num)]
    exact .inr (.inl fun h => hc h.2)

/-- **`nodeRun_X` with the reserve**: an accepted node run on a good log meets `StmtN4R` on `f⁽⁰⁾`,
at the log's child claim `ch = rsvL` (empty on `N8`). -/
theorem nodeRunR_X {Vseg : SegProgs} {Vnode : NodeProgs} {vk : Digest} (hR : RunFacts4 Vseg Vnode vk) :
    ∀ κ L c π, GoodX P4f.DFhi L → kindOf4 π = .node κ → (Vnode κ vk c π).runLog L = some true →
      X.vkOf π = vk ∧ ∃ (w : Circ.Asg) (c₁ c₂ : Digest) (ch : List F), c = nodeStmt c₁ c₂ ∧
        N4c.StmtN4R κ (lRows4 κ) (nodeIRows4 κ) vk c₁ c₂ w ch := by
  intro κ L c π hG hk hrun
  obtain ⟨hb, -, -⟩ := T4.muT_lt_one hG.2
  obtain ⟨j, hT, ⟨hkC, hvk, hvkL, hc⟩, hZ⟩ := hR.node κ L c π hb hk hrun
  obtain ⟨hlen3, hSt⟩ := stmt4_of_tail P4f.frontHi_X hG hT
  have hlen : 327 ≤ (entriesOf L (pathOf L j)).length := by
    have := hT.len; rw [T4.capPh_pos.2.2.2] at this; omega
  obtain ⟨htc, hpub⟩ := rsv_of_tail hG hT hkC
  generalize entriesOf L (pathOf L j) = es at hlen hlen3 hSt htc hpub hkC hvkL hc hZ ⊢
  have hA := agree_take3 hlen3
  have hA' := agree_takeN (es := es) hlen
  have hk3 : kindOfC (es.take 3) = .node κ := (kindOfC_congr (hA.mono (by norm_num))).trans hkC
  rw [P4a.stmt4_node_iff hk3] at hSt
  have hp : pvL (es.take 3) = (vk, stL es 0, stL es 1) := by
    simp only [pvL, vkL, stL, hA 0 (by norm_num), msgAt_congr hA (by norm_num : 1 < 3)]
    rw [← hvkL]; rfl
  rw [hp] at hSt
  have h33 : Agree (es.take 3) (es.take 327) 3 := fun p hp => (hA p hp).trans (hA' p (by omega)).symm
  have hfz : src4.fz L (es.take 3) = src4.fz L (es.take 327) := src4.fz_same (src4.ofAgree L h33) le_rfl
  have hk327 : kindOfC (es.take 327) = .node κ := (kindOfC_congr (hA'.mono (by norm_num))).trans hkC
  refine ⟨hvk, _, _, _, Snd.P4b.rsvL (.node κ) es, hc, hSt, ?_,
    N4c.truthChildV_rsvL _ κ htc hZ.1 hZ.2⟩
  unfold N4c.PubCellsR4
  rw [hfz, hpub κ hk327, Snd.P4b.rsvL_congr hA' (by norm_num)]

/-! ## The node law and `KS` with the reserve -/

section KSR
open FR.X.X4

/-- **The node laws from `StmtN4R`** (`nodeLaws4C'` at `St := ∃ ch, StmtN4R`): the residual `hRes` may
use the reserve's cells and the true child claim (`gap4Imp_of_rsv`'s inputs). -/
theorem nodeSoundR_X (impl₀ : OpImpl) (implN : NodeKind → OpImpl) (S : Submission) (vk : Digest)
    (hV : S.V = VC4 impl₀ implN N4c.cells4) (hq : S.qV = qV4)
    (hRun : RunFacts4 (VsegC impl₀) (VnodeC implN N4c.cells4) vk)
    (I : N4c.SlotIface4 (VsegC impl₀) (VnodeC implN N4c.cells4)) (rd : N4c.Read4)
    (hI : I.lrows = lRows4 ∧ I.irows = nodeIRows4)
    (hRes : ∀ κ w c₁ c₂ ch, N4c.StmtN4R κ (lRows4 κ) (nodeIRows4 κ) vk c₁ c₂ w ch →
      N4c.NodeResid4 I rd κ vk c₁ c₂ w) :
    NodeSoundLog (VnodeC implN N4c.cells4) vk (GoodX P4f.DFhi) (Rel (S.acc vk)) := by
  obtain ⟨hl, hi⟩ := hI
  refine (N4c.nodeLaws4C' impl₀ implN N4c.cells4 S vk hV hq I rd
    (St := fun κ w c₁ c₂ => ∃ ch, N4c.StmtN4R κ (lRows4 κ) (nodeIRows4 κ) vk c₁ c₂ w ch)
    (fun κ w c₁ c₂ ⟨_, h⟩ => by rw [hl, hi]; exact h.1) ?_ fun κ w c₁ c₂ ⟨ch, h⟩ => hRes κ w c₁ c₂ ch h).1
  intro κ L c π hG hk h
  obtain ⟨hvk, w, c₁, c₂, ch, hc, hS⟩ := nodeRunR_X hRun κ L c π hG hk h
  exact ⟨hvk, w, c₁, c₂, hc, ch, hS⟩

/-- **`KS` with the reserve** (`ks_rev4` at the concrete front `P4f.DFhi`, `frontHi_X`): the residual
`hRes` is over `StmtN4R`, which carries the reserve's cells and the true child claim. -/
theorem ks_rev4R (impl₀ : OpImpl) (base : NodeKind → OpImpl) (S : Submission) (vk : Digest)
    (hV : S.V = VC4 impl₀ (NI4F.implN4F base) N4c.cells4) (hq : S.qV = qV4)
    {nd : X.XIR} (hE : S.E = E4X nd S.acc) (hε : S.ε = epsR)
    (hRun : RunFacts4 (VsegC impl₀) (VnodeC (NI4F.implN4F base) N4c.cells4) vk)
    (I : N4c.SlotIface4 (VsegC impl₀) (VnodeC (NI4F.implN4F base) N4c.cells4)) (rd : N4c.Read4)
    (hI : I.lrows = lRows4 ∧ I.irows = nodeIRows4)
    (hRes : ∀ κ w c₁ c₂ ch, N4c.StmtN4R κ (lRows4 κ) (nodeIRows4 κ) vk c₁ c₂ w ch →
      N4c.NodeResid4 I rd κ vk c₁ c₂ w)
    (D : NodeDec4 nd)
    (hL : ∀ κ L c π, GoodX P4f.DFhi L → kindOf4 π = .node κ → X.InDomE c π L →
      (VnodeC (NI4F.implN4F base) N4c.cells4 κ vk c π).runLog L = some true →
      ∃ es, D.Links κ L es π c ∧ Rel (S.acc vk) c (D.readW κ L es)) :
    KS (Rel (S.acc vk)) (S.V vk) S.E S.ε S.qV := by
  have hF := T4.muT_laws_of_front (frontObl_X P4f.frontHi_X)
  rw [hε]
  exact ks4_E4X impl₀ (NI4F.implN4F base) N4c.cells4 S vk hV hq D hE _ hF.1 hF.2
    (segSound_X P4f.frontHi_X hRun) (nodeSoundR_X impl₀ _ S vk hV hq hRun I rd hI hRes) hL

/-- **The residuals of `ks_rev4R` at one key** (`Resid4` at `P4f.DFhi` with `slots` over `StmtN4R`). -/
structure Resid4R (impl₀ : OpImpl) (base : NodeKind → OpImpl) (S : Submission) (nd : X.XIR)
    (D : NodeDec4 nd) (vk : Digest) : Prop where
  run : RunFacts4 (VsegC impl₀) (VnodeC (NI4F.implN4F base) N4c.cells4) vk
  slots : ∃ (I : N4c.SlotIface4 (VsegC impl₀) (VnodeC (NI4F.implN4F base) N4c.cells4))
    (rd : N4c.Read4), (I.lrows = lRows4 ∧ I.irows = nodeIRows4) ∧
      ∀ κ w c₁ c₂ ch, N4c.StmtN4R κ (lRows4 κ) (nodeIRows4 κ) vk c₁ c₂ w ch →
        N4c.NodeResid4 I rd κ vk c₁ c₂ w
  links : ∀ κ L c π, GoodX P4f.DFhi L → kindOf4 π = .node κ → X.InDomE c π L →
    (VnodeC (NI4F.implN4F base) N4c.cells4 κ vk c π).runLog L = some true →
      ∃ es, D.Links κ L es π c ∧ Rel (S.acc vk) c (D.readW κ L es)

/-- `Resid4` at `P4f.DFhi` gives `Resid4R` (`StmtN4R` implies `StmtN4`). -/
theorem resid4R_of {impl₀ : OpImpl} {base : NodeKind → OpImpl} {S : Submission} {nd : X.XIR}
    {D : NodeDec4 nd} {vk : Digest} (h : Resid4 impl₀ base S nd D P4f.DFhi vk) :
    Resid4R impl₀ base S nd D vk :=
  let ⟨I, rd, hI, hRes⟩ := h.slots
  ⟨h.run, ⟨I, rd, hI, fun κ w c₁ c₂ _ hS => hRes κ w c₁ c₂ hS.1⟩, h.links⟩

/-- **The contract's `Certificate` with the reserve** (`certificate_rev4` at `P4f.DFhi`, with
`secure` from `ks_rev4R`: the residual `hRes` is over `StmtN4R`). -/
theorem certificate_rev4R (impl₀ : OpImpl) (base : NodeKind → OpImpl) (S : Submission) {nd : X.XIR}
    (hV : S.V = VC4 impl₀ (NI4F.implN4F base) N4c.cells4) (hq : S.qV = qV4)
    (hE : S.E = E4X nd S.acc) (hε : S.ε = epsR) (hext : S.ext = ext4With nd) (hfuel : S.fuel = X.fuel)
    (hnd : DecOk4 nd) (D : NodeDec4 nd) (hR : ∀ vk, Resid4R impl₀ base S nd D vk)
    (hC : ∀ vk, CompleteWithError (Rel (S.acc vk)) (S.P vk) (S.V vk) S.δ)
    (hδ : S.δ ≤ completenessCap) : Certificate S where
  secure vk := by
    obtain ⟨hrun, ⟨I, rd, hI, hRes⟩, hL⟩ := hR vk
    exact ks_rev4R impl₀ base S vk hV hq hE hε hrun I rd hI hRes D hL
  complete := hC
  computes := by rw [hext, hE, hfuel]; exact computes4 hnd S.acc
  cap := by
    obtain ⟨hf, hs⟩ := ext4_caps hnd
    refine ⟨hε ▸ epsR_le_errorCap, hδ, by rw [hq, qV4]; norm_num, fun t => ?_, by rw [hext]; exact hs⟩
    rw [hfuel]; exact hf t

end KSR

end FR.Snd.X4

end G6_FRNodeStmtR4
