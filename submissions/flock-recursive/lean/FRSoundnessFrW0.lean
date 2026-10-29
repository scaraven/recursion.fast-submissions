-- New for `flock-recursive` (BLUEPRINT A.9 `finRS`/`finB′`/`finPf`, A.10 B′ → P1.0; stage S-G5).
-- RET-2: the declarations revision 4.1 reads moved to `FRSoundnessCoreRows`.
import FRSoundnessFront
import FRSoundnessWeights
import FRKindWeight
import FRSoundnessCoreRows

/-!
# The front's level-0 weight `W₀` and claim `c₀`, read off the chain

The front hands the tail (P1.0 on) a weight table `W₀` on level 0's cube and an initial claim `c₀`
(`FrontObl`'s `W₀`, `c₀`). Both are read off the chain's entries before P1.0 (position 318), with
the readers of `FRSoundnessStepA`, in the form of the verifier's registers:

* **the claim points** (`zSrc`, `lcSrc`, `shSrc`, `eSrc`, `rsPtIx`): `zPtL`, `lcPtL`, `shPtL`,
  `ePtL`, `rsPtsL` (Z, Lc, Sh at the kind's `m`, and E4's `r′` for a node);
* **RS1's coordinates** `r″` (`rsRL`) and `κ` (`rsKL`); **B′'s** `κ′` (`kpL`);
* **`wrsL`**: the RS weight table `y ↦ Σ_j κ^j Φ_{r″}(eq(p_j, y)·f_j(y))`, `f_1` the node's
  kind factor `kfT` (revision 3.16; `1` on a leaf), whose extension is `rsWeightS`
  (`weight_mle`, `rsWeight_kind_eq`);
* **`W₀L := ι ∘ w0F wrsL (cellsOf κ) κ′`** (`w0V`'s table: the RS weight and the public cells);
* **`c₀L := ι v*`** with `v* = v_RS + [node] κ′²·pubH(κ′)` (`relB`'s `vStar`): `v_RS` is `rsV`
  over RS0's slices (`sliceL`), `pubH` over the seed's `vk` and the statement's `c₁`, `c₂`
  (`pubHL`).

**`frontLocal_W0`**: `FrontLocal W₀L c₀L` (`FrontObl.loc`): every read is at a position below
`p1Start 0`.
-/

namespace FR.Snd
open RecursionFast Finset

/-! ## The readers' positions (controls against `fsStarts`) -/

/-- The positions the readers use are the phases' starts: Z1 (3), Z3 (15), L2 (69), S2 (114),
E4 (265), RS0 (312), RS1 (313), B′ (317), P1.0 (318). -/
theorem frW0_starts : phStart 3 = 3 ∧ phStart 5 = 15 ∧ phStart 8 = 69 ∧ phStart 12 = 114 ∧
    phStart 21 = 265 ∧ phStart 23 = 312 ∧ phStart 24 = 313 ∧ phStart 25 = 317 ∧
    p1Start 0 = 318 := by
  simp only [p1Start, phStart, fsStarts_eq]; decide

/-! ## The claim points -/

/-- The E4 claim's point (`eSrc`): E4's 23 challenges `r′`. -/
def ePtL (es : Log) : List F := (List.range 23).map (rch 265 es)

/-- **The claim points `rsWeight` takes** (`rsPtIx`): Z, Lc, Sh at the kind's `m`; E4's for a
node. -/
def rsPtsL (κ : Kind) (es : Log) : List (List F) :=
  [zPtL κ.m es, lcPtL κ.m es, shPtL κ.m es] ++ if κ.isNode then [ePtL es] else []

/-! ## RS1, B′, RS0's slices, the public values -/

/-- RS1's coordinate `p` (`p < 7`: `r″`; `p = 7`: `κ`). -/
def rsCoL (es : Log) (p : ℕ) : F := coordAt es 312 p

/-- `r″` (`rsFsRegs`). -/
def rsRL (es : Log) : List F := (List.range 7).map (rsCoL es)

/-- RS1's batching challenge `κ`. -/
def rsKL (es : Log) : F := rsCoL es 7

/-- B′'s challenge `κ′`. -/
def kpL (es : Log) : F := fAt es 317 0

/-! ## The node's kind factor (revision 3.16, R-V-M1) -/

/-- Node kind `i`'s indicator on block `t` (`finLc`'s `v_i` order `KW.nodeKinds`; the verifier's
intervals `KW.ivsQ 16`). -/
def indKW (i : Fin 8) (t : Fin (2 ^ 16)) : F := selOf (KW.ivsQ 16 (KW.nodeKinds.getD i .free)) t

/-- **The kind factor of block `t`**: a node's `B_β(t) = Σ_i β^i Ind_i(t)` with L3β's `β`
(position 98); a leaf's is `1` (`rsWeight` passes `β = 1` off a node). -/
noncomputable def kfT (κ : Kind) (es : Log) (t : ℕ) : F :=
  if κ.isNode then kindFac indKW (fAt es 98 0) ⟨t % 2 ^ 16, Nat.mod_lt _ (by positivity)⟩ else 1

/-- **The RS weight table** (`rsWeightS`'s table): `y ↦ Σ_j κ^j Φ_{r″}(eq(p_j, cube y)·f_j(y))`,
`f_1(y) = kfT κ es (y / 2^7)` (claim 2's kind factor on the block of `y`), `f_j = 1` otherwise. -/
noncomputable def wrsL (κ : Kind) (es : Log) (y : ℕ) : F :=
  ((rsPtsL κ es).zipIdx.map fun p =>
    rsKL es ^ p.2 * Phi (rsRL es) (eqPts p.1 (bitsL p.1.length y) *
      if p.2 = 1 then kfT κ es (y / 2 ^ 7) else 1)).sum

/-- Slice `i` of RS claim `j` (`sv`: RS0's message, claim-major, 16 bytes each). -/
def sliceL (es : Log) (j i : ℕ) : F := readF (msgAt es 312) (rsOff j i)

/-- Claim `j`'s switched claim `T_j = Σ_i bb_i Φ_{r″}(s_{j,i})` (`rsTv`). -/
noncomputable def rsTvL (es : Log) (j : ℕ) : F :=
  ∑ k ∈ range 128, bb k * Phi (rsRL es) (sliceL es j k)

/-- **`v_RS`** (`rsV`): `T₀ + κ(T₁ + κ(T₂ + κ·[node]T₃))`. -/
noncomputable def vRSL (κ : Kind) (es : Log) : F :=
  rsTvL es 0 + rsKL es * (rsTvL es 1 + rsKL es * (rsTvL es 2 +
    rsKL es * (if κ.isNode then rsTvL es 3 else 0)))

/-- **`v*`** (`vStar`): `v_RS + [node] κ′²·pubH(κ′)`. -/
noncomputable def vStarL (κ : Kind) (es : Log) : F :=
  vRSL κ es + if κ.isNode then kpL es * kpL es * pubHL es (kpL es) else 0

/-! ## `W₀`, `c₀` -/

/-- **The front's level-0 weight** (`w0V`'s table): the RS weight and, for a node, the public
cells weighted `κ′^(k+2)` (`w0F`), in K. -/
noncomputable def W₀L (_ : Log) (es : Log) (y : ℕ) : K :=
  algebraMap F K (w0F (wrsL (kindOf es) es) (cellsOf (kindOf es)) (kpL es) y)

/-- **The front's initial claim** (`relB`'s `v*`), in K. -/
noncomputable def c₀L (_ : Log) (es : Log) : K := algebraMap F K (vStarL (kindOf es) es)

/-! ## Locality -/

variable {es es' : Log} {n : ℕ}

theorem rsPtsL_congr (h : Agree es es' 311) (κ : Kind) : rsPtsL κ es = rsPtsL κ es' := by
  have hm := Kind.m_le κ
  have hz : zPtL κ.m es = zPtL κ.m es' := by
    unfold zPtL
    exact congrArg ((List.ofFn pinnedRho).drop 1 ++ ·) (List.map_congr_left fun j hj =>
      fAt_congr h (p := 2 + 1 + j / 2) (by simp only [List.mem_range] at hj; omega) (j % 2))
  have hl : lcPtL κ.m es = lcPtL κ.m es' := by
    unfold lcPtL
    rw [List.map_congr_left fun l hl => rch_congr h (b := 69) (l := 7 + l)
        (by simp only [List.mem_range] at hl; omega),
      List.map_congr_left fun l hl => rch_congr h (b := 15) (l := 8 + l)
        (by simp only [List.mem_range] at hl; omega)]
  have hs : shPtL κ.m es = shPtL κ.m es' := by
    unfold shPtL
    rw [List.map_congr_left fun l hl => rch_congr h (b := 114) (l := κ.m - 7 + l)
        (by simp only [List.mem_range] at hl; omega),
      List.map_congr_left fun l hl => rch_congr h (b := 114) (l := l)
        (by simp only [List.mem_range] at hl; omega)]
  have he : ePtL es = ePtL es' := by
    unfold ePtL
    rw [List.map_congr_left fun l hl => rch_congr h (b := 265) (l := l)
        (by simp only [List.mem_range] at hl; omega)]
  unfold rsPtsL
  rw [hz, hl, hs, he]

theorem rsCoL_congr (h : Agree es es' 317) {p : ℕ} (hp : p < 8) : rsCoL es p = rsCoL es' p :=
  fAt_congr h (by omega) _

theorem rsRL_congr (h : Agree es es' 317) : rsRL es = rsRL es' :=
  List.map_congr_left fun p hp => rsCoL_congr h (by simp at hp; omega)

theorem kfT_congr (h : Agree es es' 99) (κ : Kind) : kfT κ es = kfT κ es' := by
  funext t; simp only [kfT, fAt_congr h (show 98 < 99 by norm_num)]

theorem wrsL_congr (h : Agree es es' 317) (κ : Kind) : wrsL κ es = wrsL κ es' := by
  funext y
  simp only [wrsL, rsPtsL_congr (h.mono (by norm_num)) κ, rsRL_congr h, rsKL,
    rsCoL_congr h (show 7 < 8 by norm_num), kfT_congr (h.mono (by norm_num)) κ]

theorem vRSL_congr (h : Agree es es' 317) (κ : Kind) : vRSL κ es = vRSL κ es' := by
  have hs : ∀ j i, sliceL es j i = sliceL es' j i := fun j i => by
    simp only [sliceL, msgAt_congr h (show 312 < 317 by norm_num)]
  have hT : ∀ j, rsTvL es j = rsTvL es' j := fun j => by simp only [rsTvL, hs, rsRL_congr h]
  simp only [vRSL, hT, rsKL, rsCoL_congr h (show 7 < 8 by norm_num)]

theorem vStarL_congr (h : Agree es es' 318) (κ : Kind) : vStarL κ es = vStarL κ es' := by
  simp only [vStarL, vRSL_congr (h.mono (by norm_num)) κ, pubHL_congr (h.mono (by norm_num)), kpL,
    fAt_congr h (show 317 < 318 by norm_num)]

/-- **`FrontObl.loc`**: `W₀L` and `c₀L` read only entries before P1.0. -/
theorem frontLocal_W0 : FrontLocal W₀L c₀L := by
  refine frontLocal_of (fun L es L' es' hS => ?_) (fun L es L' es' hS => ?_)
  all_goals
    have h : Agree es es' 318 := frW0_starts.2.2.2.2.2.2.2.2 ▸ hS.1
    have hk : kindOf es = kindOf es' := kindOf_congr (h.mono (by norm_num))
  · funext y
    simp only [W₀L, hk, wrsL_congr (h.mono (by norm_num)), kpL,
      fAt_congr h (show 317 < 318 by norm_num)]
  · simp only [c₀L, hk, vStarL_congr h]

/-! ## Controls -/

/-- Control (positive): a node takes four claim points (Z, Lc, Sh, E4), each of 23 coordinates. -/
theorem rsPtsL_node (es : Log) :
    (rsPtsL .N30 es).length = 4 ∧ ∀ p ∈ rsPtsL .N30 es, p.length = 23 := by
  refine ⟨rfl, fun p hp => ?_⟩
  simp only [rsPtsL, Kind.isNode, ↓reduceIte, List.cons_append, List.nil_append, List.mem_cons,
    List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl | rfl | rfl <;> simp [zPtL, lcPtL, shPtL, ePtL, Kind.m]

/-- Control (negative): a leaf takes three claim points, of 25 coordinates at `m = 32` (not the
node's 23). -/
theorem rsPtsL_leaf (es : Log) :
    (rsPtsL .L32 es).length = 3 ∧ ∀ p ∈ rsPtsL .L32 es, p.length = 25 := by
  refine ⟨rfl, fun p hp => ?_⟩
  simp only [rsPtsL, Kind.isNode, Bool.false_eq_true, ↓reduceIte, List.append_nil, List.mem_cons,
    List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl | rfl <;> simp [zPtL, lcPtL, shPtL, Kind.m]

/-- Control (positive): with all slices zero, `v_RS = 0` (`Φ_{r″}(0) = 0`). -/
theorem vRSL_zero {es : Log} (κ : Kind) (h : ∀ j i, sliceL es j i = 0) : vRSL κ es = 0 := by
  have hT : ∀ j, rsTvL es j = 0 := fun j => by
    simp only [rsTvL, h, Phi, frobMap_zero, mul_zero, sum_const_zero]
  simp [vRSL, hT]

/-- Control (positive): a leaf's claim is `v_RS` alone (no public cells). -/
theorem c₀L_leaf {L es : Log} (hk : kindOf es = .P30) :
    c₀L L es = algebraMap F K (vRSL .P30 es) := by
  simp [c₀L, vStarL, hk, Kind.isNode]

/-- Control (negative): a node's claim adds `κ′²·pubH(κ′)` to `v_RS`: with `κ′ = 1` and zero
digests the public part is `1`, so `c₀` is not `v_RS`. -/
theorem vStarL_node_ne {es : Log} (h1 : kpL es = 1)
    (hv : dLo (vkL es) = 0 ∧ dHi (vkL es) = 0 ∧ dLo (stL es 0) = 0 ∧ dHi (stL es 0) = 0 ∧
      dLo (stL es 1) = 0 ∧ dHi (stL es 1) = 0) :
    vStarL .N30 es = vRSL .N30 es + 1 := by
  obtain ⟨h₁, h₂, h₃, h₄, h₅, h₆⟩ := hv
  simp [vStarL, pubHL, Kind.isNode, h1, h₁, h₂, h₃, h₄, h₅, h₆]

/-- Control (positive): off the cells, a node's `W₀` is the RS weight. -/
theorem W₀L_off {L es : Log} {y : ℕ} (hy : ∀ c ∈ cellsOf (kindOf es), y ≠ c) :
    W₀L L es y = algebraMap F K (wrsL (kindOf es) es y) := by
  simp only [W₀L, w0F]
  congr 1
  rw [add_eq_left]
  refine sum_eq_zero fun k hk => ?_
  rw [ite_neg' (hy _ (by
    rw [List.getD_eq_getElem _ _ (mem_range.mp hk)]; exact List.getElem_mem _)), mul_zero]

end FR.Snd
