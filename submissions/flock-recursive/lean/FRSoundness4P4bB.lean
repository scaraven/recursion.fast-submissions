-- New for `flock-recursive` (BLUEPRINT revision 4.1, A.9 `finRS`/`finB′`/`finPf`, A.10 RS1, B′ →
-- P1.0, §5.2; stage P4b): RS1 (327 … 330), B′ (331) and the front's `W₀`, `c₀` at `seq4`. The 3.x
-- templates are `FRSoundnessFrW0`, `FRSoundnessFrRS` and `FRSoundnessFrB`.
import FRSoundness4P4bRS

/-!
# RS1, B′ and the front's `W₀`, `c₀` at revision 4.1 (P4b)

* **Readers** at `seq4`: RS1's coordinates `r″`, `κ` after 326 (`rsCoL4`, `rsRL4`, `rsKL4`), B′'s
  `κ′` at 331 (`kpL4`); the RS weight `wrsL4` (claim 2 with the kind factor `kfT4 kf`), `v_RS`
  (`vRSL4`), its truth `⟨W_rs, f⁽⁰⁾⟩` (`fipL4`), `v*` (`vStarL4`: `v_RS + [node] κ′²·pubH(κ′)`;
  `gFinB'` is `finB′`, so `pubH` is 3.x's `pubHL` over the seed's `vk` and the statement's `c₁`,
  `c₂`, positions 0 and 1). **`W₀L4`** (`w0F` with the node kind's public cells `cells ν`, as
  `nodeFinP κ cells`) and **`c₀L4`** (`ι v*`); **`frontLocal4`**: both read before P1.0 (332).
* **The node's public cells hold** (`PubOK4 R cells`): `f⁽⁰⁾` at `cells ν` is `pubL` (3.x's
  `Node.pubVals`). It is the concrete `Pub` of `DPend4`/`DRS0_4`, which keep `Pub` a parameter.
* **RS1**: `DRS1_4` (far, `v_RS` false, a public cell false); **`rs1_hfin4`**: from `DRS0_4` at
  RS1's entry, any phase doom whose escapes clear `DRS1_4` costs `≤ 10/2^128` (`rs1_round_le`,
  `rs1_count4`).
* **B′**: `DB4` (far, or `v* ≠ ⟨W₀, f⁽⁰⁾⟩` in F, `ipW`); **`single_B4`** (`hsingle` at 331,
  `≤ 10·2^128`, `batch_count` at degree 10); `dB4_reads` (before 332). The handoff into P1.0's
  doom (`D1 0`, T4's) is the instantiation's: `ipW_eq` puts `⟨W₀, f⁽⁰⁾⟩` in the form 3.x's
  `ip_W0` gives `trueSum e2 (lvT W₀ 0)` on a close word.
-/

namespace FR.Snd.P4b
open RecursionFast FR.Merkle FR.Rev4 Finset
open scoped NNReal

set_option linter.constructorNameAsVariable false

/-! ## Readers -/

/-- RS1's coordinate `p` (`p < 7`: `r″`; `p = 7`: `κ`), after RS0 (326). -/
def rsCoL4 (es : Log) (p : ℕ) : F := coordAt es 326 p
def rsRL4 (es : Log) : List F := (List.range 7).map (rsCoL4 es)
def rsKL4 (es : Log) : F := rsCoL4 es 7
def fsL4 (es : Log) : Fin 7 → F := fun i => rsCoL4 es i
/-- B′'s challenge `κ′` (331). -/
def kpL4 (es : Log) : F := fAt es 331 0

/-- **The RS weight table** (`rsWeightS`'s): `y ↦ Σ_j κ^j Φ_{r″}(eq(p_j, cube y)·f_j(y))`, `f_1` the
kind factor of `y`'s block. -/
noncomputable def wrsL4 (kf : NodeKind → F → ℕ → F) (κ : CKind) (es : Log) (y : ℕ) : F :=
  ((rsPtsL4 κ es).zipIdx.map fun p =>
    rsKL4 es ^ p.2 * Phi (rsRL4 es) (eqPts p.1 (bitsL p.1.length y) *
      if p.2 = 1 then kfT4 kf κ es (y / 2 ^ 7) else 1)).sum

/-- Claim `j`'s switched claim `T_j = Σ_i bb_i Φ_{r″}(s_{j,i})`. -/
noncomputable def rsTvL4 (es : Log) (j : ℕ) : F :=
  ∑ k ∈ range 128, bb k * Phi (rsRL4 es) (sliceL4 es j k)

/-- **`v_RS`** (`rsV`): `T₀ + κ(T₁ + κ(T₂ + κ·[node]T₃))`. -/
noncomputable def vRSL4 (κ : CKind) (es : Log) : F :=
  rsTvL4 es 0 + rsKL4 es * (rsTvL4 es 1 + rsKL4 es * (rsTvL4 es 2 +
    rsKL4 es * (if κ.isNode then rsTvL4 es 3 else 0)))

/-- **The true `v_RS`**: `⟨W_rs, f⁽⁰⁾⟩` over level 0's `2^(m − 7)` cells. -/
noncomputable def fipL4 (R : FSrc) (kf : NodeKind → F → ℕ → F) (κ : CKind) (L es : Log) : F :=
  ∑ y ∈ range (2 ^ (κ.m - 7)), wrsL4 kf κ es y * R.fz L es y

/-- **The previous node's claim**, value `i` (RSV2 §2.1: `fLrEnd[48, 1008)` of Lrend's message, 213,
is `p_x ‖ p_y ‖ s ‖ X₃`, 60 values of 16 bytes; `pxL`, `pyL`, `sL`, `xL` read the same bytes). -/
def rsvV (es : Log) (i : ℕ) : F := readF (msgAt es 213) (48 + 16 * i)

/-- **The reserve's cell count** of a chain kind (`Rev4.rsvCells`' length): 60 on a node kind with a
previous node (`N2`, `N4`), none on `N8` or a segment. -/
def nRsv : CKind → ℕ
  | .node ν => if ν.hasPrev then 60 else 0
  | .seg _ => 0

/-- **The reserve's values** `v_0 … v_{n−1}` (`finB′`'s exports, RSV2 §2.2). -/
def rsvL (κ : CKind) (es : Log) : List F := (List.range (nRsv κ)).map (rsvV es)

/-- **The reserve's batch** `Σ_i κ′^i·v_i` (`0` without the reserve). -/
noncomputable def rsvHL (κ : CKind) (es : Log) (kp : F) : F :=
  ∑ i ∈ range (nRsv κ), kp ^ i * rsvV es i

/-- **`v*`** (`vStar`, `finB′`; revision 4.4.2, RSV2 §2.2): `v_RS + [node] (κ′²·pubH(κ′) +
κ′^{11}·Σ_i κ′^i v_i)`, the reserve's values at `κ′^{11} … κ′^{70}` (none on `N8`). -/
noncomputable def vStarL4 (κ : CKind) (es : Log) : F :=
  vRSL4 κ es + if κ.isNode then
    kpL4 es * kpL4 es * pubHL es (kpL4 es) + kpL4 es ^ 11 * rsvHL κ es (kpL4 es) else 0

/-- The public cells of the chain's kind (none on a segment). -/
def cellsC (cells : NodeKind → List ℕ) : CKind → List ℕ
  | .node ν => cells ν
  | .seg _ => []

/-- **The front's level-0 weight** (`w0V`'s table), in K. -/
noncomputable def W₀L4 (kf : NodeKind → F → ℕ → F) (cells : NodeKind → List ℕ) (_ : Log) (es : Log)
    (y : ℕ) : K :=
  algebraMap F K (w0F (wrsL4 kf (kindOfC es) es) (cellsC cells (kindOfC es)) (kpL4 es) y)

/-- **The front's initial claim** (`relB`'s `v*`), in K. -/
noncomputable def c₀L4 (_ : Log) (es : Log) : K := algebraMap F K (vStarL4 (kindOfC es) es)

/-- `⟨w0F Wrs cells κ′, f⟩` over `2^n` cells. -/
def ipW (Wrs : ℕ → F) (cells : List ℕ) (kp : F) (n : ℕ) (f : ℕ → F) : F :=
  ∑ y ∈ range (2 ^ n), w0F Wrs cells kp y * f y

/-! ## The dooms -/

/-- **The node's public cells hold**: `f⁽⁰⁾` at the kind's cells is `pubVals vk c₁ c₂`. -/
def PubOK4 (R : FSrc) (cells : NodeKind → List ℕ) (L es : Log) : Prop :=
  ∀ ν, kindOfC es = .node ν → (cells ν).map (R.fz L es) = pubL es

/-- **The reserve's public cells hold** (RSV2 §2.4; revision 4.4.2): `f⁽⁰⁾` at the node kind's
reserve cells `rcells ν` is the node's own child claim `rsvL` (Lrend's message, 213). With the nine
public cells it is RS0's and RS1's `Pub` (`PubOK4 ∧ PubOKR4`); B′ batches both families. -/
def PubOKR4 (R : FSrc) (rcells : NodeKind → List ℕ) (L es : Log) : Prop :=
  ∀ ν, kindOfC es = .node ν → (rcells ν).map (R.fz L es) = rsvL (.node ν) es

/-- **RS1's doom at its last answer**: far, `v_RS` false, or a public cell false. -/
def DRS1_4 (R : FSrc) (kf : NodeKind → F → ℕ → F) (F0 Pub : Log → Log → Prop) (L es : Log) : Prop :=
  F0 L es ∨ vRSL4 (kindOfC es) es ≠ fipL4 R kf (kindOfC es) L es ∨ ¬ Pub L es

/-- **B′'s doom** (P1.0's `D1 0` in F): far, or `v* ≠ ⟨W₀, f⁽⁰⁾⟩`. -/
def DB4 (R : FSrc) (kf : NodeKind → F → ℕ → F) (cells : NodeKind → List ℕ) (F0 : Log → Log → Prop)
    (L es : Log) : Prop :=
  F0 L es ∨ (¬ F0 L es ∧ vStarL4 (kindOfC es) es ≠
    ipW (wrsL4 kf (kindOfC es) es) (cellsC cells (kindOfC es)) (kpL4 es) ((kindOfC es).m - 7)
      (R.fz L es))

/-! ## Locality -/

section Congr
variable {es es' : Log}

theorem rsCoL4_congr (h : Agree es es' 331) {p : ℕ} (hp : p < 8) : rsCoL4 es p = rsCoL4 es' p :=
  fAt_congr h (by omega) _

theorem rsRL4_congr (h : Agree es es' 331) : rsRL4 es = rsRL4 es' :=
  List.map_congr_left fun p hp => rsCoL4_congr h (by simp at hp; omega)

theorem kfT4_congr (kf : NodeKind → F → ℕ → F) (h : Agree es es' 99) (κ : CKind) :
    kfT4 kf κ es = kfT4 kf κ es' := by
  funext t
  cases κ with
  | seg σ => rfl
  | node ν =>
    show kf ν (fAt es 98 0) t = kf ν (fAt es' 98 0) t
    rw [fAt_congr h (show 98 < 99 by norm_num)]

theorem wrsL4_congr (kf : NodeKind → F → ℕ → F) (h : Agree es es' 331) (κ : CKind) :
    wrsL4 kf κ es = wrsL4 kf κ es' := by
  funext y
  simp only [wrsL4, rsPtsL4_congr (h.mono (by norm_num)) κ, rsRL4_congr h, rsKL4,
    rsCoL4_congr h (show 7 < 8 by norm_num), kfT4_congr kf (h.mono (by norm_num)) κ]

theorem vRSL4_congr (h : Agree es es' 331) (κ : CKind) : vRSL4 κ es = vRSL4 κ es' := by
  have hs : ∀ j i, sliceL4 es j i = sliceL4 es' j i := fun j i => by
    simp only [sliceL4, msgAt_congr h (show 326 < 331 by norm_num)]
  have hT : ∀ j, rsTvL4 es j = rsTvL4 es' j := fun j => by simp only [rsTvL4, hs, rsRL4_congr h]
  simp only [vRSL4, hT, rsKL4, rsCoL4_congr h (show 7 < 8 by norm_num)]

theorem rsvV_congr {p : ℕ} (h : Agree es es' p) (hp : 214 ≤ p) : rsvV es = rsvV es' :=
  funext fun _ => by simp only [rsvV, msgAt_congr h (show 213 < p by omega)]

theorem rsvL_congr {p : ℕ} (h : Agree es es' p) (hp : 214 ≤ p) (κ : CKind) : rsvL κ es = rsvL κ es' := by
  simp only [rsvL, rsvV_congr h hp]

theorem rsvHL_congr {p : ℕ} (h : Agree es es' p) (hp : 214 ≤ p) (κ : CKind) (kp : F) :
    rsvHL κ es kp = rsvHL κ es' kp := by
  simp only [rsvHL, rsvV_congr h hp]

theorem vStarL4_congr (h : Agree es es' 332) (κ : CKind) : vStarL4 κ es = vStarL4 κ es' := by
  simp only [vStarL4, vRSL4_congr (h.mono (by norm_num)) κ, pubHL_congr (h.mono (by norm_num)),
    rsvHL_congr h (by norm_num), kpL4, fAt_congr h (show 331 < 332 by norm_num)]

/-- **`FrontObl.loc`'s content**: `W₀L4` and `c₀L4` read only the entries before P1.0 (332). -/
theorem frontLocal4 (kf : NodeKind → F → ℕ → F) (cells : NodeKind → List ℕ) (L L' : Log)
    (h : Agree es es' 332) : W₀L4 kf cells L es = W₀L4 kf cells L' es' ∧ c₀L4 L es = c₀L4 L' es' := by
  have hk : kindOfC es = kindOfC es' := kindOfC_congr (h.mono (by norm_num))
  refine ⟨funext fun y => ?_, ?_⟩
  · simp only [W₀L4, hk, wrsL4_congr kf (h.mono (by norm_num)), kpL4,
      fAt_congr h (show 331 < 332 by norm_num)]
  · simp only [c₀L4, hk, vStarL4_congr h]

end Congr

theorem pubOK4_reads (R : FSrc) (cells : NodeKind → List ℕ) : ReadsS R 3 (PubOK4 R cells) :=
  fun L es L' es' _ _ h => by
    have hA := R.agree h
    simp only [PubOK4, kindOfC_congr (hA.mono (by norm_num)), R.fz_same h le_rfl, pubL, vkL, stL,
      hA 0 (by norm_num), msgAt_congr hA (show 1 < 3 by norm_num)]

theorem pubOKR4_reads (R : FSrc) (rcells : NodeKind → List ℕ) : ReadsS R 214 (PubOKR4 R rcells) :=
  fun L es L' es' _ _ h => by
    have hA := R.agree h
    simp only [PubOKR4, kindOfC_congr (hA.mono (by norm_num)), R.fz_same h (by norm_num),
      rsvL_congr hA le_rfl]

theorem ReadsS.and {R : FSrc} {p : ℕ} {P Q : Log → Log → Prop} (hP : ReadsS R p P) (hQ : ReadsS R p Q) :
    ReadsS R p fun L es => P L es ∧ Q L es :=
  fun L es L' es' h1 h2 hS => and_congr (hP L es L' es' h1 h2 hS) (hQ L es L' es' h1 h2 hS)

theorem dB4_reads {R : FSrc} {kf : NodeKind → F → ℕ → F} {cells : NodeKind → List ℕ}
    {F0 : Log → Log → Prop} (hF : ReadsS R 3 F0) : ReadsS R 332 (DB4 R kf cells F0) :=
  fun L es L' es' h1 h2 h => by
    have hA := R.agree h
    have hk := kindOfC_congr (hA.mono (by norm_num))
    have hf := hF L es L' es' (by omega) (by omega) (R.mono h (by norm_num))
    simp only [DB4, hf, hk, vStarL4_congr hA, wrsL4_congr kf (hA.mono (by norm_num)), kpL4,
      fAt_congr hA (show 331 < 332 by norm_num), R.fz_same h (by norm_num)]

/-- RS0's doom reads before RS1's first squeeze (327); `Pub` may read up to there (revision 4.4.2:
the reserve's cells read Lrend's message, 213). -/
theorem dRS0_4_reads {R : FSrc} {kf : NodeKind → F → ℕ → F} {F0 Pub : Log → Log → Prop}
    (hF : ReadsS R 3 F0) (hP : ReadsS R 327 Pub) : ReadsS R 327 (DRS0_4 R kf F0 Pub) := by
  have hT : ReadsS R 327 fun L es =>
      ¬ truthRS0_4 R L es (gL4 kf (kindOfC es) es) (sL4 (kindOfC es) es) := by
    intro L es L' es' h1 h2 h
    have hA := R.agree h
    beta_reduce
    rw [kindOfC_congr (hA.mono (by norm_num)), gL4_congr kf (hA.mono (by norm_num)), sL4_congr hA]
    unfold truthRS0_4
    rw [rsQ4_same R h (by norm_num)]
  exact (hF.mono (by norm_num)).or (hP.not.or hT)

/-- RS1's doom reads before B′ (331). -/
theorem dRS1_4_reads {R : FSrc} {kf : NodeKind → F → ℕ → F} {F0 Pub : Log → Log → Prop}
    (hF : ReadsS R 3 F0) (hP : ReadsS R 331 Pub) : ReadsS R 331 (DRS1_4 R kf F0 Pub) := by
  have hT : ReadsS R 331 fun L es => vRSL4 (kindOfC es) es ≠ fipL4 R kf (kindOfC es) L es := by
    intro L es L' es' h1 h2 h
    have hA := R.agree h
    beta_reduce
    rw [kindOfC_congr (hA.mono (by norm_num)), vRSL4_congr hA]
    unfold fipL4
    rw [wrsL4_congr kf hA, R.fz_same h (by norm_num)]
  exact (hF.mono (by norm_num)).or (hT.or hP.not)

/-- **RS0's doom is monotone in `Pub`**: a smaller `Pub′` (RS0's with the reserve's cells) is doomed
wherever `Pub` is (E4 end's `DPend4` keeps the nine cells; `habs_RS0_4` then lands in `Pub′`'s). -/
theorem dRS0_4_mono {R : FSrc} {kf : NodeKind → F → ℕ → F} {F0 Pub Pub' : Log → Log → Prop}
    (h : ∀ L es, Pub' L es → Pub L es) {L es : Log} (hd : DRS0_4 R kf F0 Pub L es) :
    DRS0_4 R kf F0 Pub' L es :=
  hd.imp_right (Or.imp_left fun hn hp => hn (h L es hp))

/-! ## `v_RS` and its truth as batches -/

theorem rsTvL4_eq (es : Log) (j : ℕ) :
    rsTvL4 es j = ∑ i : Fin 128, bitBasis i * Phi (rsRL4 es) (sliceL4 es j i) := by
  rw [rsTvL4, ← Fin.sum_univ_eq_sum_range (fun k => bb k * Phi (rsRL4 es) (sliceL4 es j k))]
  refine sum_congr rfl fun i _ => ?_
  simp only [bb, Nat.mod_eq_of_lt i.isLt]

theorem ofFn_fsL4 (es : Log) : List.ofFn (fsL4 es) = rsRL4 es := by
  simp [fsL4, rsRL4, List.range_succ]

/-- **`v_RS = Σ_j κ^j T_j`** (a segment's `T₃` is `0`). -/
theorem vRSL4_eq (κ : CKind) (es : Log) :
    vRSL4 κ es = ∑ j : Fin 4, rsKL4 es ^ j.val * rsT (sL4 κ es) (fsL4 es) j := by
  have hT : ∀ j : Fin 4, rsT (sL4 κ es) (fsL4 es) j =
      if j.val < (rsPtsL4 κ es).length then rsTvL4 es j else 0 := by
    intro j
    simp only [rsT, sL4, ofFn_fsL4, Algebra.algebraMap_self, RingHom.id_apply, rsTvL4_eq]
    split_ifs <;> simp [Phi_zero']
  simp only [hT, Fin.sum_univ_four, vRSL4, rsPtsL4_length]
  cases κ <;> simp [CKind.isNode] <;> ring

/-- The RS weight is the claims' `Φ`-batch of `gL4`. -/
theorem wrsL4_eq (kf : NodeKind → F → ℕ → F) (κ : CKind) (es : Log) (u : Fin (2 ^ (κ.m - 7))) :
    wrsL4 kf κ es u = ∑ j : Fin 4, rsKL4 es ^ j.val * Phi (rsRL4 es) (gL4 kf κ es j u) := by
  simp only [Fin.sum_univ_four, gL4, rsPtsL4_length]
  cases κ <;>
    simp [wrsL4, rsPtsL4, CKind.isNode, List.zipIdx_cons, Phi_zero'] <;> ring

/-- **`⟨W_rs, f⁽⁰⁾⟩` is the batch of the switched claims' truths** (`pack_unpack`). -/
theorem fipL4_eq (R : FSrc) (kf : NodeKind → F → ℕ → F) (κ : CKind) (L es : Log) :
    fipL4 R kf κ L es = ∑ j : Fin 4, rsKL4 es ^ j.val *
      rsTruth (rsQ4 R L es (κ.m - 7)) (gL4 kf κ es) (fsL4 es) j := by
  have hq : ∀ u : Fin (2 ^ (κ.m - 7)),
      (∑ i, rsQ4 R L es (κ.m - 7) i u * bitBasis i) = R.fz L es u := fun u => pack_unpack _
  simp only [rsTruth, Algebra.algebraMap_self, RingHom.id_apply, hq, ofFn_fsL4, mul_sum]
  rw [sum_comm, fipL4, ← Fin.sum_univ_eq_sum_range (fun y => wrsL4 kf κ es y * R.fz L es y)]
  refine sum_congr rfl fun u _ => ?_
  rw [wrsL4_eq, sum_mul]
  exact sum_congr rfl fun j _ => by ring

/-! ## RS1's charge -/

open Classical in
/-- **RS1's charge** (A.10 RS1, `rs1_round_le` at `(326, 4)`, `rs1_count4`): from RS0's doom at
RS1's entry, a phase doom whose escapes clear `DRS1_4` costs at most `10/2^128`. -/
theorem rs1_hfin4 {R : FSrc} {kf : NodeKind → F → ℕ → F} {F0 Pub : Log → Log → Prop}
    (hF : ReadsS R 3 F0) (hP : ReadsS R 327 Pub) {D : Log → Log → Prop} {L es₀ : Log}
    (hl : es₀.length = 327) (hd : DRS0_4 R kf F0 Pub L es₀)
    (hesc : ∀ as : List Digest, as.length = 4 → EscAtG D L (ext es₀ as) →
      ¬ DRS1_4 R kf F0 Pub L (ext es₀ as)) :
    condCount D L es₀ 4 [] ≤ ((10 : ℕ) : ℝ≥0) / 2 ^ 128 := by
  set κ := kindOfC es₀
  refine rs1_round_le hl (if F0 L es₀ ∨ ¬ Pub L es₀ then ∅ else
      univ.filter fun p : (Fin 7 → F) × F =>
        ∑ j, p.2 ^ j.val * rsT (sL4 κ es₀) p.1 j =
          ∑ j, p.2 ^ j.val * rsTruth (rsQ4 R L es₀ (κ.m - 7)) (gL4 kf κ es₀) p.1 j) ?_
    fun as has he => ?_
  · split_ifs with hb
    · simp
    · have ht : ¬ truthRS0_4 R L es₀ (gL4 kf κ es₀) (sL4 κ es₀) := by
        rcases hd with h | h | h
        · exact absurd (.inl h) hb
        · exact absurd (.inr h) hb
        · exact h
      exact (rs1_count4 (J' := 3) ht).trans (by norm_num)
  · have hnf := hesc as has he
    have hlenX : 327 ≤ (ext es₀ as).length := by
      obtain ⟨ys, hys⟩ := ext_eq_append es₀ as; rw [hys]; simp; omega
    generalize hX : ext es₀ as = X at hnf hlenX ⊢
    have hag : Agree X es₀ 327 := by
      obtain ⟨ys, hys⟩ := ext_eq_append es₀ as
      rw [← hX, hys, ← hl]; exact agree_append es₀ ys le_rfl
    have hS : R.Sm L X L es₀ 327 := R.ofAgree L hag
    have hk : kindOfC X = κ := kindOfC_congr (hag.mono (by norm_num))
    have hf := hF L X L es₀ (by omega) (by omega) (R.mono hS (by norm_num))
    have hp := hP L X L es₀ (by omega) (by omega) hS
    simp only [DRS1_4, not_or, not_not, hk] at hnf
    obtain ⟨hnf1, hnf2, hnf3⟩ := hnf
    have hb : ¬ (F0 L es₀ ∨ ¬ Pub L es₀) := fun h =>
      h.elim (fun h' => hnf1 (hf.mpr h')) fun h' => h' (hp.mp hnf3)
    rw [ite_neg' hb]
    simp only [mem_filter, mem_univ, true_and]
    have h1 := vRSL4_eq κ X
    have h2 := fipL4_eq R kf κ L X
    rw [sL4_congr hag] at h1
    rw [rsQ4_same R hS (by norm_num), gL4_congr kf (hag.mono (by norm_num))] at h2
    exact h1.symm.trans (hnf2.trans h2)

/-! ## B′ -/

/-- `⟨W₀, f⟩` is `⟨W_rs, f⟩` plus the cells' batch (`ip_W0`'s computation). -/
theorem ipW_eq (Wrs : ℕ → F) {cells : List ℕ} (kp : F) {n : ℕ} (f : ℕ → F)
    (hc : ∀ c ∈ cells, c < 2 ^ n) :
    ipW Wrs cells kp n f = ∑ y ∈ range (2 ^ n), Wrs y * f y +
      ∑ k ∈ range cells.length, kp ^ (k + 2) * f (cells.getD k 0) := by
  simp only [ipW, w0F, add_mul, sum_add_distrib]
  refine congrArg (_ + ·) ?_
  simp only [sum_mul]
  rw [sum_comm]
  refine sum_congr rfl fun k hk => ?_
  have hck : cells.getD k 0 < 2 ^ n := hc _ (by
    rw [List.getD_eq_getElem _ _ (mem_range.mp hk)]; exact List.getElem_mem _)
  simp only [mul_ite, mul_one, mul_zero, ite_mul, zero_mul]
  rw [sum_ite_eq' (range _), ite_pos' (mem_range.mpr hck)]

/-- The batched terms (revision 4.4.2: `J_f = 69`, powers `κ′⁰ … κ′^{70}`): `v_RS`, `0`, and (a node)
the nine public values and the reserve's (`pub ++ rsv`), or their truths. -/
def bTerms4 (node : Bool) (v0 : F) (pub rsv : List F) (i : Fin 71) : F :=
  if i.val = 0 then v0 else if node ∧ 2 ≤ i.val then (pub ++ rsv).getD (i.val - 2) 0 else 0

theorem bTerms4_sum (node : Bool) (v0 kp : F) (pub rsv : List F) :
    ∑ i, kp ^ i.val * bTerms4 node v0 pub rsv i =
      v0 + if node then ∑ k ∈ range 69, kp ^ (k + 2) * (pub ++ rsv).getD k 0 else 0 := by
  have e := Fin.sum_univ_eq_sum_range (fun j => kp ^ j * if j = 0 then v0 else
    if node ∧ 2 ≤ j then (pub ++ rsv).getD (j - 2) 0 else 0) 71
  beta_reduce at e
  rw [show ∑ i, kp ^ i.val * bTerms4 node v0 pub rsv i = ∑ i : Fin 71, kp ^ i.val * (if i.val = 0 then v0
    else if node ∧ 2 ≤ i.val then (pub ++ rsv).getD (i.val - 2) 0 else 0) from rfl, e,
    Finset.sum_range_succ', Finset.sum_range_succ']
  cases node
  · simp
  · simp [add_comm]
    refine sum_congr rfl fun x _ => ?_
    rw [ite_pos' (by omega), show 1 + (x + 1) = x + 2 by omega, Nat.add_sub_cancel]

/-- A weighted sum over a list's cells is the sum over `N ≥` its length of the values' list padded
by `0` (`ipW_eq`'s second sum in `bTerms4`'s form). -/
theorem sum_cells_pad (l : List ℕ) (f : ℕ → F) (g : ℕ → F) {N : ℕ} (hN : l.length ≤ N) :
    ∑ k ∈ range l.length, g k * f (l.getD k 0) = ∑ k ∈ range N, g k * (l.map f).getD k 0 := by
  rw [← Finset.sum_range_add_sum_Ico _ hN, Finset.sum_eq_zero (s := Ico _ _) fun k hk => by
    rw [List.getD_eq_default _ _ (by simp only [List.length_map]; exact (mem_Ico.1 hk).1), mul_zero],
    add_zero]
  exact sum_congr rfl fun k hk => by rw [listGetD_map_lt (mem_range.1 hk)]

/-- The reserve's batch over 60 powers (`0` past `nRsv`). -/
theorem rsvHL_eq (κ : CKind) (es : Log) (kp : F) :
    rsvHL κ es kp = ∑ i ∈ range 60, kp ^ i * (rsvL κ es).getD i 0 := by
  have h : nRsv κ = 0 ∨ nRsv κ = 60 := by
    rcases κ with σ | ν
    · exact .inl rfl
    · cases ν <;> simp [nRsv, NodeKind.hasPrev]
  have e : ∀ i < 60, i < nRsv κ → (rsvL κ es).getD i 0 = rsvV es i := fun i _ hi => by
    rw [List.getD_eq_getElem _ _ (by simpa [rsvL] using hi)]; simp [rsvL]
  rcases h with h | h
  · simp [rsvHL, rsvL, h]
  · rw [rsvHL, h]
    exact sum_congr rfl fun i hi => by rw [e i (mem_range.1 hi) (h ▸ mem_range.1 hi)]

theorem rsvL_length (κ : CKind) (es : Log) : (rsvL κ es).length = nRsv κ := by simp [rsvL]

/-- **The node's public part of `v*`** in `bTerms4`'s form: `κ′²·pubH(κ′) + κ′^{11}·Σ_i κ′^i v_i =
Σ_{k<69} κ′^{k+2}·(pubL ++ rsvL)_k`. -/
theorem pubPart_eq (κ : CKind) (es : Log) (kp : F) :
    kp * kp * pubHL es kp + kp ^ 11 * rsvHL κ es kp =
      ∑ k ∈ range 69, kp ^ (k + 2) * (pubL es ++ rsvL κ es).getD k 0 := by
  have hpl : (pubL es).length = 9 := (Node.pubCells_length (vkL es) (stL es 0) (stL es 1)).2
  rw [pubHL_eq, rsvHL_eq, mul_sum, mul_sum, Finset.sum_range_add (fun k => kp ^ (k + 2) *
    (pubL es ++ rsvL κ es).getD k 0) 9 60]
  refine congrArg₂ (· + ·) (sum_congr rfl fun k hk => ?_) (sum_congr rfl fun i _ => ?_)
  · rw [List.getD_append _ _ _ _ (by rw [hpl]; exact mem_range.1 hk)]; ring
  · rw [List.getD_append_right _ _ _ _ (by omega), hpl, show 9 + i - 9 = i by omega]; ring

theorem cellsC_lt {cells : NodeKind → List ℕ} (hc : ∀ ν, ∀ c ∈ cells ν, c < 2 ^ ncR ν) (κ : CKind) :
    ∀ c ∈ cellsC cells κ, c < 2 ^ (κ.m - 7) := by
  cases κ with
  | seg σ => simp [cellsC]
  | node ν => exact hc ν

/-- Two lists of the same length agree if their `getD`s do. -/
theorem list_eq_of_getD {l l' : List F} (hl : l.length = l'.length)
    (h : ∀ k < l.length, l.getD k 0 = l'.getD k 0) : l = l' := by
  refine List.ext_getElem hl fun k h1 h2 => ?_
  rw [← List.getD_eq_getElem _ 0 h1, ← List.getD_eq_getElem _ 0 h2]
  exact h k h1

open Classical in
/-- **`hsingle` at B′** (331, revision 4.4.2: `70/2^128`, RSV2 §2.6): from RS1's doom (with the node's
nine public cells and the reserve's cells as `Pub`), at most `70·2^128` answers `κ′` make B′'s doom
(over the cells `cells ν ++ rcells ν`) false. `hcells`: a node kind's public cells are nine cells
inside level 0 (S-E's layout); `hrcells`: its reserve cells are `nRsv` cells inside level 0. -/
theorem single_B4 {R : FSrc} {kf : NodeKind → F → ℕ → F} {cells rcells : NodeKind → List ℕ}
    {F0 : Log → Log → Prop} (hF : ReadsS R 3 F0)
    (hcells : ∀ ν, (cells ν).length = 9 ∧ ∀ c ∈ cells ν, c < 2 ^ ncR ν)
    (hrcells : ∀ ν, (rcells ν).length = nRsv (.node ν) ∧ ∀ c ∈ rcells ν, c < 2 ^ ncR ν) (L es : Log)
    (hl : es.length = 331) :
    (univ.filter fun a => DRS1_4 R kf F0 (fun L es => PubOK4 R cells L es ∧ PubOKR4 R rcells L es) L es ∧
      ¬ DB4 R kf (fun ν => cells ν ++ rcells ν) F0 L (ext1 es a)).card ≤ 70 * 2 ^ 128 := by
  obtain ⟨κ, hκ⟩ : ∃ κ, kindOfC es = κ := ⟨_, rfl⟩
  have hag : ∀ a, Agree (ext1 es a) es 331 := fun a => hl ▸ agree_append es _ le_rfl
  have hS : ∀ a, R.Sm L (ext1 es a) L es 331 := fun a => R.ofAgree L (hag a)
  have hk : ∀ a, kindOfC (ext1 es a) = κ := fun a =>
    (kindOfC_congr ((hag a).mono (by norm_num))).trans hκ
  have hfar : ∀ a, F0 L (ext1 es a) ↔ F0 L es := fun a =>
    hF L _ L es (by simp [ext1]; omega) (by omega) (R.mono (hS a) (by norm_num))
  by_cases hf : F0 L es
  · rw [filter_false_of_mem fun a _ ha => ha.2 (.inl ((hfar a).mpr hf)), card_empty]
    exact Nat.zero_le _
  by_cases hD : DRS1_4 R kf F0 (fun L es => PubOK4 R cells L es ∧ PubOKR4 R rcells L es) L es
  swap
  · rw [filter_false_of_mem fun a _ ha => hD ha.1, card_empty]
    exact Nat.zero_le _
  have hpl : (pubL es).length = 9 := (Node.pubCells_length (vkL es) (stL es 0) (stL es 1)).2
  set v := bTerms4 κ.isNode (vRSL4 κ es) (pubL es) (rsvL κ es)
  set t := bTerms4 κ.isNode (fipL4 R kf κ L es) ((cellsC cells κ).map (R.fz L es))
    ((cellsC rcells κ).map (R.fz L es))
  have hvt : v ≠ t := by
    intro hvt
    rcases hD with h | h | h
    · exact hf h
    · rw [hκ] at h
      exact h (by simpa [v, t, bTerms4] using congrFun hvt 0)
    · apply h
      have hall : ∀ ν, κ = .node ν → ∀ k < 69,
          (pubL es ++ rsvL κ es).getD k 0 = ((cells ν).map (R.fz L es) ++ (rcells ν).map (R.fz L es)).getD k 0 :=
        fun ν hν k hk => by
          have := congrFun hvt ⟨k + 2, by omega⟩
          subst hν
          simpa [v, t, bTerms4, CKind.isNode, cellsC] using this
      refine ⟨fun ν hν => ?_, fun ν hν => ?_⟩ <;> rw [hκ] at hν <;> have e := hall ν hν
      · refine list_eq_of_getD (by simp [(hcells ν).1, hpl]) fun k hk => ?_
        simp only [List.length_map, (hcells ν).1] at hk
        have := e k (by omega)
        rwa [List.getD_append _ _ _ _ (by rw [hpl]; exact hk),
          List.getD_append _ _ _ _ (by simp [(hcells ν).1, hk]), eq_comm] at this
      · subst hν
        refine list_eq_of_getD (by simp [(hrcells ν).1, rsvL_length]) fun k hk => ?_
        simp only [List.length_map, (hrcells ν).1] at hk
        have hk60 : k < 60 := by
          have : nRsv (.node ν) ≤ 60 := by cases ν <;> simp [nRsv, NodeKind.hasPrev]
          omega
        have := e (9 + k) (by omega)
        rwa [List.getD_append_right _ _ _ _ (by omega), hpl,
          List.getD_append_right _ _ _ _ (by simp [(hcells ν).1]), List.length_map, (hcells ν).1,
          show 9 + k - 9 = k by omega, eq_comm] at this
  refine batch_count (k := 70) _ v t hvt fun a ha => ?_
  have hnf' : ¬ F0 L (ext1 es a) := fun h => hf ((hfar a).mp h)
  have hc' : ∀ ν, ∀ c ∈ cells ν ++ rcells ν, c < 2 ^ ncR ν := fun ν c hc => by
    rcases List.mem_append.1 hc with h | h
    · exact (hcells ν).2 c h
    · exact (hrcells ν).2 c h
  have heq : vStarL4 κ (ext1 es a) = ipW (wrsL4 kf κ (ext1 es a)) (cellsC (fun ν => cells ν ++ rcells ν) κ)
      (kpL4 (ext1 es a)) (κ.m - 7) (R.fz L (ext1 es a)) := by
    by_contra hne; exact ha.2 (.inr ⟨hnf', by rw [hk]; exact hne⟩)
  rw [ipW_eq _ _ _ (cellsC_lt hc' κ)] at heq
  have hkp : kpL4 (ext1 es a) = chF a 0 := by
    simp [kpL4, fAt, ansAt, entAt, ext1, hl]
  have hz : R.fz L (ext1 es a) = R.fz L es := R.fz_same (hS a) (by norm_num)
  have hfip : ∑ y ∈ range (2 ^ (κ.m - 7)), wrsL4 kf κ (ext1 es a) y * R.fz L (ext1 es a) y =
      fipL4 R kf κ L es := by
    simp only [fipL4, wrsL4_congr kf (hag a), hz]
  have hv : vStarL4 κ (ext1 es a) = vRSL4 κ es +
      if κ.isNode then ∑ k ∈ range 69, chF a 0 ^ (k + 2) * (pubL es ++ rsvL κ es).getD k 0 else 0 := by
    simp only [vStarL4, vRSL4_congr (hag a), pubHL_congr ((hag a).mono (by norm_num)),
      rsvHL_congr (hag a) (by norm_num), hkp]
    rw [pubPart_eq]
  have hw : ∑ k ∈ range (cellsC (fun ν => cells ν ++ rcells ν) κ).length,
      kpL4 (ext1 es a) ^ (k + 2) * R.fz L (ext1 es a) ((cellsC (fun ν => cells ν ++ rcells ν) κ).getD k 0) =
      if κ.isNode then ∑ k ∈ range 69, chF a 0 ^ (k + 2) *
        ((cellsC cells κ).map (R.fz L es) ++ (cellsC rcells κ).map (R.fz L es)).getD k 0 else 0 := by
    rw [hkp, hz]
    cases κ with
    | seg σ => simp [cellsC, CKind.isNode]
    | node ν =>
      have hlen : (cells ν ++ rcells ν).length ≤ 69 := by
        have : nRsv (.node ν) ≤ 60 := by cases ν <;> simp [nRsv, NodeKind.hasPrev]
        simp only [List.length_append, (hcells ν).1, (hrcells ν).1]; omega
      simp only [cellsC, CKind.isNode, ite_true, ← List.map_append]
      exact sum_cells_pad _ _ (fun k => chF a 0 ^ (k + 2)) hlen
  simp only [v, t]
  rw [bTerms4_sum, bTerms4_sum, ← hv, ← hfip, ← hw]
  exact heq

/-! ## Controls -/

/-- (+) With all slices zero, `v_RS = 0` (`Φ_{r″}(0) = 0`). -/
theorem vRSL4_zero {es : Log} (κ : CKind) (h : ∀ j i, sliceL4 es j i = 0) : vRSL4 κ es = 0 := by
  have hT : ∀ j, rsTvL4 es j = 0 := fun j => by
    simp only [rsTvL4, h, Phi, frobMap_zero, mul_zero, sum_const_zero]
  simp [vRSL4, hT]

/-- (+) A segment's claim is `v_RS` alone, and its `W₀` the RS weight (no public cells). -/
theorem c₀L4_seg {kf : NodeKind → F → ℕ → F} {cells : NodeKind → List ℕ} {L es : Log} {σ : SegKind}
    (hk : kindOfC es = .seg σ) :
    c₀L4 L es = algebraMap F K (vRSL4 (.seg σ) es) ∧
      W₀L4 kf cells L es = fun y => algebraMap F K (wrsL4 kf (.seg σ) es y) := by
  refine ⟨by simp [c₀L4, vStarL4, hk, CKind.isNode], funext fun y => ?_⟩
  simp [W₀L4, hk, cellsC, w0F]

/-- (−) A node's claim adds `κ′²·pubH(κ′)` to `v_RS`: with `κ′ = 1`, zero digests and a zero
reserve claim the public part is `1`. -/
theorem vStarL4_node_ne {es : Log} (ν : NodeKind) (h1 : kpL4 es = 1)
    (hv : dLo (vkL es) = 0 ∧ dHi (vkL es) = 0 ∧ dLo (stL es 0) = 0 ∧ dHi (stL es 0) = 0 ∧
      dLo (stL es 1) = 0 ∧ dHi (stL es 1) = 0) (hr : ∀ i, rsvV es i = 0) :
    vStarL4 (.node ν) es = vRSL4 (.node ν) es + 1 := by
  obtain ⟨h₁, h₂, h₃, h₄, h₅, h₆⟩ := hv
  simp [vStarL4, pubHL, rsvHL, CKind.isNode, h1, h₁, h₂, h₃, h₄, h₅, h₆, hr]

/-- (−) **The reserve enters `v*`** (revision 4.4.2): on `N2` (a previous node) with `κ′ = 1`, zero
digests and the claim's first value `1` (the others `0`), `v*` is `v_RS + 2`. -/
theorem vStarL4_rsv_ne {es : Log} (h1 : kpL4 es = 1)
    (hv : dLo (vkL es) = 0 ∧ dHi (vkL es) = 0 ∧ dLo (stL es 0) = 0 ∧ dHi (stL es 0) = 0 ∧
      dLo (stL es 1) = 0 ∧ dHi (stL es 1) = 0) (hr : ∀ i, rsvV es i = if i = 0 then 1 else 0) :
    vStarL4 (.node .N2) es = vRSL4 (.node .N2) es + 2 := by
  obtain ⟨h₁, h₂, h₃, h₄, h₅, h₆⟩ := hv
  have e : rsvHL (.node .N2) es 1 = 1 := by
    simp only [rsvHL, nRsv, NodeKind.hasPrev, ite_true, one_pow, one_mul, hr]
    rw [Finset.sum_ite_eq' (range 60) 0 (fun _ => (1 : F)), ite_pos' (by simp)]
  simp only [vStarL4, CKind.isNode, ite_true, h1, e, pubHL, h₁, h₂, h₃, h₄, h₅, h₆]
  ring

/-- (+) A far word dooms B′; (−) on a close word with `v* = ⟨W₀, f⁽⁰⁾⟩`, B′ is not doomed. -/
theorem dB4_ctrl {R : FSrc} {kf : NodeKind → F → ℕ → F} {cells : NodeKind → List ℕ}
    {F0 : Log → Log → Prop} {L es : Log} :
    (F0 L es → DB4 R kf cells F0 L es) ∧
      (¬ F0 L es → vStarL4 (kindOfC es) es = ipW (wrsL4 kf (kindOfC es) es)
        (cellsC cells (kindOfC es)) (kpL4 es) ((kindOfC es).m - 7) (R.fz L es) →
        ¬ DB4 R kf cells F0 L es) :=
  ⟨.inl, fun hnf hc h => h.elim hnf fun h' => h'.2 hc⟩

/-- (+) A segment's public cells never doom; (−) a node with `f⁽⁰⁾` off `pubVals` at its cells
fails `PubOK4`. -/
theorem pubOK4_ctrl {R : FSrc} {cells : NodeKind → List ℕ} {L es : Log} :
    (∀ σ, kindOfC es = .seg σ → PubOK4 R cells L es) ∧
      (∀ ν, kindOfC es = .node ν → (cells ν).map (R.fz L es) ≠ pubL es → ¬ PubOK4 R cells L es) :=
  ⟨fun σ hσ ν hν => (by rw [hσ] at hν; cases hν), fun ν hν hne h => hne (h ν hν)⟩

end FR.Snd.P4b
