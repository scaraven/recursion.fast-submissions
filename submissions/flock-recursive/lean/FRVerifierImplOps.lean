-- New for `flock-recursive` (BLUEPRINT §3, A.8, A.9; stage S-F2, track L-cert).
-- Split from `FRVerifierImpl` by S-E3 (mechanical: the op implementations, specifications and
-- `Meets` lemmas that do not depend on the node's M rows, so that `FRVIRTemplates` can use them).
import FRVIRFinalsSG
import FRVIREval
import FRRSEval
import FRVerifier
import FRBlockChain
import FRPubTarget

/-!
# The concrete op implementations (`implC`), their specification (`specC`) and `Meets`

BLUEPRINT §3 and A.8: `V` runs the IR with an `OpImpl`. This module gives, per op of `OpImpl`'s
`Array` signature,

* a **specification** `…S`: an adapter from the arrays to the owner's definition over `Fin n → R`
  (S-C: `FRSkip.lagrangeWeight`/`interpolateAt`/`z2Vals`, `FRSpartan.rowW`, `FRShift`'s
  `succT`/`shiftTarget`/the slot weight's extension, `FRRingSwitch.Phi`/`weightEval`; S-D:
  `FRRSEval.tensorTwin`; S-E2: `FRVIREval`'s `walkSpecA/B`, `kindIndSpec`, `evalRowsSpec`);
* a computable **implementation** `…I` on the fast fields `F`, `K`, with the constants an op needs
  (Lagrange denominators, Lagrange weights at fixed nodes, the novel-basis table) as closed
  definitions, computed once per process;
* the equality `…_meets` under the operand lengths `gen` produces (`OpImpl.Meets`' preconditions).

`specC`/`implC` assemble them and **`implC_meets : (implC …).Meets (specC …)`**.

**Interface gaps** (the RESULT's open questions; `FRVIR` is S-0's): `targetS`, `slotW` (slot map 1)
and `linkW` depend on the proof's kind, which `OpImpl`'s fields do not receive, and `shiftTarget`
needs `κ_s` (S1's coordinate 28), which its op does not pass. This module gives the kind-explicit
forms (`targetSLeaf`, `slotWI`, `shiftTargetI κs`) and fills the `OpImpl` fields at a fixed kind;
the fields become exact once `evalOp` passes `κ` (and `κ_s`).
-/

namespace FR
namespace Impl
open Finset RecursionFast RecursionFast.Blake2s

/-! ## Points and `eq` at an index -/

/-- An array read as a point with `n` coordinates (`0` past the end). -/
def ptA (n : ℕ) (r : Array F) : Fin n → F := fun l => r.getD l 0

/-- `eq(r, i)` at the Boolean point of the index `i` (bit `l` of `i` ↔ coordinate `l`). -/
def eqAtR {R : Type*} [CommRing R] {n : ℕ} (r : Fin n → R) (i : ℕ) : R :=
  ∏ l : Fin n, if i.testBit l then r l else 1 - r l

theorem eqTable_getD {R : Type*} [CommRing R] (r : List R) {i : ℕ} (hi : i < 2 ^ r.length) :
    (eqTable r).getD i 0 = eqAtR (ptOf r.length r) i := by
  have := congrFun (tbl_eqTable' r rfl) ⟨i, hi⟩
  simp only [tbl] at this
  rw [this, eq_cube]; rfl

/-! ## Lagrange weights at `ℕ`-indexed nodes -/

/-- The indices `0 … N−1` other than `i`. -/
def othersN (N i : ℕ) : List ℕ := (List.range N).filter (· ≠ i)

/-- `Π_{j < N, j ≠ i} (z − x_j)`. -/
def numL (x : ℕ → F) (N i : ℕ) (z : F) : F := (othersN N i).foldl (fun a j => a * (z - x j)) 1

/-- The inverted Lagrange denominators `(Π_{j ≠ i} (x_i − x_j))⁻¹`, `i < N`. -/
def lagTab (x : ℕ → F) (N : ℕ) : Array F := Array.ofFn (n := N) fun i => (numL x N i (x i))⁻¹

/-- The `N` Lagrange weights at `z`, from the inverted denominators `den`. -/
def lagW (x : ℕ → F) (N : ℕ) (den : Array F) (z : F) : Array F :=
  Array.ofFn (n := N) fun i => numL x N i z * den.getD i 0

/-- The 128 skip nodes `S ∪ Λ` as a table (computed once). -/
def skipTab : Array F := Array.ofFn (n := 128) skipNode

/-- Node `j mod 128` from the table (`xS`). -/
def xT (j : ℕ) : F := skipTab.getD (j % 128) 0

/-- The nodes of `Λ` (`Λ_k = skipNode (64 + k)`). -/
def lamX (k : ℕ) : F := xT (64 + k)

/-- Denominators of `S` (64 nodes), of `Λ` (64), and of `S ∪ Λ₀…₆₂` (127). -/
def denS : Array F := lagTab xT 64
def denL : Array F := lagTab lamX 64
def den127 : Array F := lagTab xT 127

/-- `P^z`'s Lagrange weights on `Λ` at each node of `S` (constants, `64 × 64`). -/
def lamAtS : Array (Array F) := Array.ofFn (n := 64) fun b => lagW lamX 64 denL (xT b)

/-! ## The implementations -/

/-- **`lagrangeS`** (A.8, revision 3.8): `(P^{ab}*(λ), P^z*(λ))`, `vals[0…63]` `P^z` on `Λ`,
`vals[64…126]` `P^{ab}` on `Λ₀…₆₂`, `pe` the 64 values of `P^e` on `S`. -/
def lagrangeSI (v : Array F) (l : F) (pe : Array F) : F × F :=
  let pz := Array.ofFn (n := 64) fun k => v.getD k 0
  let vals := Array.ofFn (n := 127) fun b =>
    if b.val < 64 then dot (lamAtS.getD b #[]) pz + pe.getD b 0 else v.getD b 0
  (dot (lagW xT 127 den127 l) vals, dot (lagW lamX 64 denL l) pz)

/-- **`eqZ`** (A.8, revision 3.9): `L_{i mod 64}(λ) · eq(ρ₁, bit 6 of i)`, `i < 128`. -/
def eqZI (l ρ : F) : Array F :=
  let L := lagW xT 64 denS l
  Array.ofFn (n := 128) fun i => L.getD (i % 64) 0 * if i.val.testBit 6 then ρ else 1 - ρ

/-- **`rowW`** (A.8): `L_{k mod 64}(λ) · eq(r′_hi, ⌊k/64⌋)`, `k < 2^14`. -/
def rowWI (l : F) (rhi : Array F) : Array F :=
  let L := lagW xT 64 denS l
  let E := eqTable (List.ofFn (ptA 8 rhi))
  Array.ofFn (n := 2 ^ (6 + 8)) fun k => L.getD (k % 64) 0 * E.getD (k / 64) 0

/-- **`phiRS`**: `Φ_{r″}(a)` by 127 squarings and the stage products (`FRRingSwitch.phiApply`). -/
def phiRSI (r : Array F) (a : F) : F := phiApply r.toList a

/-- **`shiftEq`**: `shift(τ, r)` in one pass (`FRShift.shiftPair`). -/
def shiftEqI (a b : Array F) : F := (shiftPair a.toList b.toList).2

/-- The novel-basis table `Ŵ_v(D[2^i])`, `v, i < 20` (S-D's `wRow`, computed once). -/
def wTab : Array (Array F) := Array.ofFn (n := logNMax) fun v => (wRow D logNMax v).toArray

/-- `Π_{i<n} f i` by a fold (the product twin of `FRMLE.sumTo`). -/
def prodTo {M : Type*} [CommMonoid M] (n : ℕ) (f : ℕ → M) : M :=
  Nat.fold n (fun i _ acc => acc * f i) 1

/-- `Ŵ_v(D[j])` from the table (`wAtD` past the table). -/
def wAtT (v j : ℕ) : F :=
  if v < logNMax then
    sumTo logNMax fun i => if j.testBit i then (wTab.getD v #[]).getD i 0 else 0
  else wAtD v j

/-- **`tensorW`** (A.8): `Π_{v < |r|} (1 − r_v + r_v Ŵ_v(D[j]))`. -/
def tensorWI (j : ℕ) (r : Array K) : K :=
  prodTo r.size fun v => 1 - r.getD v 0 + r.getD v 0 * algebraMap F K (wAtT v j)

/-- `eq(a, b) = Π (1 + a_v + b_v)` (characteristic two). -/
def eqPtsC (a b : List K) : K := (List.zipWith (fun x y => 1 + x + y) a b).prod

/-- `Σ_{k < |c|} c_k eq(r^{2^k}, ρ)`, the point squared once per `k` (`weightEval`'s fold). -/
def wEvalC (c : Array K) (r ρ : List K) : K :=
  (Nat.fold c.size (fun k _ (p : K × List K) =>
    (p.1 + c.getD k 0 * eqPtsC p.2 ρ, p.2.map fun a => a * a)) (0, r)).1

/-- **`rsWeight`** (A.8, revision 3.9): `Σ_j κ^j Σ_{k<128} c_k(r″) eq(r_j^{2^k}, ρ)`, the
coefficients `c_k(r″)` (`FRRingSwitch.phiTable`) computed once over F. -/
def rsWeightI (r : Array F) (ps : List (Array K)) (κ : F) (ρ : Array K) : K :=
  let c := (phiTable r.toList).map K.ofF
  ((ps.zipIdx).map fun p => K.ofF κ ^ p.2 * wEvalC c p.1.toList ρ.toList).sum

/-- The slot maps' bases (A.6, P2 §7.5 (4)): `0` the `h_out` slot `256 + σ`, `1` the chain
block's `d` slot `520 + σ` (a leaf's `In`), `2` the `h_in` slot `σ`. -/
def slotBase : ℕ → ℕ
  | 0 => 256 | 1 => 520 | _ => 0

/-- **`slotW`** (A.8, `slotW_mle`): `Σ_{σ<256} eq(θ, σ) eq(r, base + σ)` over 10 coordinates. -/
def slotWI (s : ℕ) (θ r : Array F) : F :=
  let Eθ := eqTable (List.ofFn (ptA 10 θ)); let Er := eqTable (List.ofFn (ptA 10 r))
  sumTo 256 fun σ => Eθ.getD σ 0 * Er.getD (slotBase s + σ) 0

/-- Bit `σ < 256` of a digest given as its two F halves (A.7's pack: bytes LE, bits LE). -/
def digBit (e₀ e₁ : F) (σ : ℕ) : Bool :=
  if h : σ < 128 then bitF e₀ ⟨σ, h⟩ else bitF e₁ ⟨(σ - 128) % 128, Nat.mod_lt _ (by decide)⟩

/-- `Σ_{σ<256} eq(θ, σ) · bit_σ(d)` from the table `Eθ = eq(θ, ·)`. -/
def digestMle (Eθ : Array F) (e₀ e₁ : F) : F :=
  sumTo 256 fun σ => if digBit e₀ e₁ σ then Eθ.getD σ 0 else 0

/-- **`shiftTarget`** with `κ_s` (A.9 `finSh` (i); the leaf's native reading, P2 §7.5 (4)):
`eq(τ, last) · h̃(θ) + κ_s · s̃(θ)`, `bnd = [s_lo, s_hi, h_lo, h_hi]`. -/
def shiftTargetI (κs : F) (τ θ bnd : Array F) : F :=
  let Eθ := eqTable (List.ofFn (ptA 10 θ))
  prodTo τ.size (fun l => τ.getD l 0) * digestMle Eθ (bnd.getD 2 0) (bnd.getD 3 0) +
    κs * digestMle Eθ (bnd.getD 0 0) (bnd.getD 1 0)

/-- The chain block's public target `E_chain` as 0/1 (A.6, `Chain.chainTarget`; `none` reads `0`). -/
def chainE (p : ℕ) : F := if Chain.chainTarget (ProductCircuit.pos p) = some true then 1 else 0

/-- `E_chain` on the `2^14` positions (computed once). -/
def chainTab : Array F := Array.ofFn (n := 2 ^ 14) fun p => chainE p

/-- The 8 position coordinates of the Z point (A.2): the pinned `ρ₁ … ρ₇`, then Z1's first. -/
def zLo (r : Array F) : Fin 8 → F := fun l => if h : l.val < 7 then pinnedRho ⟨l, h⟩ else r.getD 0 0

/-- **`targetS` of a leaf kind** (A.8; every block a `chain` block): `P^e(σ) = Σ_hi eq(r_lo, hi)
E_chain(σ + 64 hi)`, `r_lo = zLo r`. -/
def targetSLeafI (r : Array F) : Array F :=
  let H := eqTable (List.ofFn (zLo r))
  Array.ofFn (n := 64) fun σ => sumTo 256 fun hi => chainTab.getD (σ + 64 * hi) 0 * H.getD hi 0

/-! ## Specifications (adapters to the owners' definitions) -/

/-- **`lagrangeS`'s specification** (`FRSkip.z2Vals`, `interpolateAt`): `P^{ab}*(λ)` through
`S ∪ Λ₀…₆₂` from `z2Vals`, and `P^z*(λ)` through `Λ`. -/
def lagrangeSS (v : Array F) (l : F) (pe : Array F) : F × F :=
  (interpolateAt node127 (z2Vals (fun k => v.getD k 0) (fun k => v.getD (64 + k.val) 0)
    (fun σ => pe.getD σ 0)) l, interpolateAt lNode (fun k => v.getD k 0) l)

/-- **`eqZ`'s specification**: `lagrangeWeight` on `S` at `λ` for the low 6 bits, `eq(ρ₁, ·)` on
bit 6. -/
def eqZS (l ρ : F) : Array F :=
  Array.ofFn (n := 128) fun i => lagrangeWeight sNodeF l ⟨i.val % 64, Nat.mod_lt _ (by decide)⟩ *
    if i.val.testBit 6 then ρ else 1 - ρ

/-- **`rowW`'s specification** (`FRSpartan.rowW` with 8 high position bits). -/
def rowWS (l : F) (rhi : Array F) : Array F :=
  Array.ofFn (n := 2 ^ (6 + 8)) fun k => rowW l (ptA 8 rhi) k

/-- **`phiRS`'s specification** (`FRRingSwitch.Phi`). -/
def phiRSS (r : Array F) (a : F) : F := Phi r.toList a

/-- **`shiftEq`'s specification**: `Σ_{u,v} eq(τ, u) [v = u + 1] eq(v, r)` (`FRShift.succT`). -/
def shiftEqS (a b : Array F) : F :=
  ∑ u : Fin (2 ^ a.size), ∑ v : Fin (2 ^ a.size),
    eq (ptOf a.size a.toList) (cube u) * succT u v * eq (cube v) (ptOf a.size b.toList)

/-- **`tensorW`'s specification** (`FRRSEval.tensorTwin` on `D`, S-D's verifier tensor weight). -/
def tensorWS (j : ℕ) (r : Array K) : K := tensorTwin D logNMax r.size (fun v => r.getD v 0) j

/-- **`rsWeight`'s specification** (A.8, L-R4 `weight_mle`'s right side): `Σ_j κ^j Σ_{k<128}
c_k(r″) eq(r_j^{2^k}, ρ)`, `c_k(r″)` the coefficients of `Φ_{r″}` (`FRRingSwitch.phiTable`). -/
def rsWeightS (r : Array F) (ps : List (Array K)) (κ : F) (ρ : Array K) : K :=
  ((ps.zipIdx).map fun p => K.ofF κ ^ p.2 * ∑ k ∈ range 128,
    K.ofF ((phiTable r.toList).getD k 0) * eqPts (p.1.toList.map (sqIter k)) ρ.toList).sum

/-- A digest's bits as a table over the 10-bit slot index (`0` from `σ = 256` on). -/
def digTbl (e₀ e₁ : F) : Fin (2 ^ 10) → F := fun u => if u.val < 256 ∧ digBit e₀ e₁ u then 1 else 0

/-- **`shiftTarget`'s specification** with `κ_s` (`FRShift.shiftTarget`): `eq(τ, last) h̃V(θ) +
κ_s s̃V(θ)`, `sV`, `hV` the boundary digests `bnd[0,1]`, `bnd[2,3]` as bit tables. -/
def shiftTargetS (κs : F) (τ θ bnd : Array F) : F :=
  shiftTarget (ptA 10 θ) (ptA τ.size τ) κs (digTbl (bnd.getD 0 0) (bnd.getD 1 0))
    (digTbl (bnd.getD 2 0) (bnd.getD 3 0))

/-- **The leaf kinds' `targetS` specification** (`FRPubTarget.targetS` over the `8 + b` variables
of the quirky polynomial, `b = m − 14` block bits, with the leaf's `E(σ, (hi, t)) = E_chain(σ +
64 hi)` for every block `t`). -/
def targetSLeafS (b : ℕ) (r : Array F) : Array F :=
  Array.ofFn (n := 64) fun σ => FR.targetS (ℓ := 8 + b) (Fin.append (zLo r) fun l => r.getD (1 + l) 0)
    (fun σ u => chainE (σ + 64 * (u.val % 256))) σ

/-- **`slotW`'s specification** (`FRShift.slotW_mle`'s right side for the map `σ ↦ base + σ`,
`σ < 256`): `Σ_{σ<256} eq(θ, σ) eq(r, base + σ)`. -/
def slotWS (s : ℕ) (θ r : Array F) : F :=
  ∑ σ ∈ range 256, eqAtR (ptA 10 θ) σ * eqAtR (ptA 10 r) (slotBase s + σ)

/-! ## `Meets`, per op -/

section Lagrange

theorem prod_othersN (g : ℕ → F) {N i : ℕ} (hi : i < N) :
    ((othersN N i).map g).prod = ∏ j ∈ (univ : Finset (Fin N)).erase ⟨i, hi⟩, g j := by
  rw [othersN, ← List.prod_toFinset _ (List.nodup_range.filter _)]
  have : ((List.range N).filter (· ≠ i)).toFinset = ((univ : Finset (Fin N)).erase ⟨i, hi⟩).map Fin.valEmbedding := by
    ext j
    simp only [List.mem_toFinset, List.mem_filter, List.mem_range, ne_eq,
      decide_not, Bool.not_eq_eq_eq_not, Bool.not_true, decide_eq_false_iff_not, Finset.mem_map,
      Finset.mem_erase, Finset.mem_univ, and_true, Fin.valEmbedding_apply]
    constructor
    · rintro ⟨hj, hne⟩; exact ⟨⟨j, hj⟩, fun h => hne (congrArg Fin.val h), rfl⟩
    · rintro ⟨a, ha, rfl⟩; exact ⟨a.isLt, fun h => ha (Fin.ext h)⟩
  rw [this, Finset.prod_map]; rfl

theorem lagW_getD (x : ℕ → F) (N : ℕ) (den : Array F) (z : F) {i : ℕ} (hi : i < N) :
    (lagW x N den z).getD i 0 = numL x N i z * den.getD i 0 := by
  simp [lagW, Array.getD_eq_getD_getElem?, hi]

theorem lagTab_getD (x : ℕ → F) {N i : ℕ} (hi : i < N) :
    (lagTab x N).getD i 0 = (numL x N i (x i))⁻¹ := by
  simp [lagTab, Array.getD_eq_getD_getElem?, hi]

/-- The computed weight is `FRSkip.lagrangeWeight` at the nodes `x_0 … x_{N−1}`. -/
theorem lagW_eq (x : ℕ → F) (N : ℕ) (z : F) {i : ℕ} (hi : i < N) :
    (lagW x N (lagTab x N) z).getD i 0 = lagrangeWeight (fun b : Fin N => x b) z ⟨i, hi⟩ := by
  rw [lagW_getD _ _ _ _ hi, lagTab_getD _ hi, numL, numL, foldl_mul_eq, foldl_mul_eq, one_mul,
    one_mul, prod_othersN _ hi, prod_othersN _ hi, lagrangeWeight]

/-- A dot product with the weights is the interpolant's sum. -/
theorem dot_lagW (x : ℕ → F) (N : ℕ) (z : F) (w : Array F) :
    dot (lagW x N (lagTab x N) z) w =
      ∑ i : Fin N, lagrangeWeight (fun b : Fin N => x b) z i * w.getD i 0 := by
  rw [dot, sumTo_eq, show (lagW x N (lagTab x N) z).size = N from Array.size_ofFn,
    Finset.sum_range]
  exact Finset.sum_congr rfl fun i _ => by rw [lagW_eq _ _ _ i.isLt]

theorem xT_eq (j : ℕ) : xT j = xS j := by
  simp [xT, xS, skipTab, Array.getD_eq_getD_getElem?, Nat.mod_lt]

theorem xS_node127 : (fun b : Fin 127 => xT b) = node127 := by
  funext b; simp only [xT_eq, xS, node127]; congr 1; ext; simp; omega

theorem xS_sNode : (fun b : Fin 64 => xT b) = sNodeF := by
  funext b; rw [xT_eq]; exact xS_of_lt b.isLt

theorem lamX_lNode : (fun b : Fin 64 => lamX b) = lNode := by
  funext b; simp only [lamX, xT_eq, xS, lNode]; congr 1; ext; simp; omega

private theorem hzL (v : Array F) (z : F) : dot (lagW lamX 64 denL z) (Array.ofFn (n := 64) fun k => v.getD k 0) =
      interpolateAt lNode (fun k => v.getD k 0) z := by
  rewrite [denL, dot_lagW, lamX_lNode, interpolateAt]
  exact Finset.sum_congr rfl fun k _ => by simp [Array.getD_eq_getD_getElem?]

/-- **`lagrangeS` meets its specification.** -/
theorem lagrangeS_meets (v : Array F) (l : F) (pe : Array F) :
    lagrangeSI v l pe = lagrangeSS v l pe := by
  unfold lagrangeSI lagrangeSS
  dsimp only
  rewrite [den127, dot_lagW, xS_node127, hzL, interpolateAt]
  refine Prod.ext ?_ rfl
  dsimp only
  refine Finset.sum_congr rfl fun b _ => congrArg _ ?_
  rewrite [Array.getD_eq_getD_getElem?, Array.getElem?_ofFn]
  simp only [b.isLt, dite_true, Option.getD_some, z2Vals]
  split_ifs with h
  · have hl : lamAtS[b.val]? = some (lagW lamX 64 denL (xT b)) := by
      rewrite [lamAtS, Array.getElem?_ofFn]
      simp only [show b.val < 64 from h, dite_true]
    rewrite [Array.getD_eq_getD_getElem? (xs := lamAtS), hl, Option.getD_some, hzL]
    refine congrArg (· + _) (congrArg _ ?_)
    simp only [xT_eq, xS, Nat.mod_eq_of_lt (show b.val < 128 by omega)]
    rfl
  · show v.getD b 0 = v.getD (64 + (b.val - 64)) 0
    rewrite [Nat.add_sub_cancel' (by omega)]; rfl
end Lagrange

section Tables

theorem eqTable_ofFn_getD {R : Type*} [CommRing R] {n : ℕ} (f : Fin n → R) {i : ℕ}
    (hi : i < 2 ^ n) : (eqTable (List.ofFn f)).getD i 0 = eqAtR f i := by
  have h1 := congrFun (tbl_eqTable' (List.ofFn f) List.length_ofFn) ⟨i, hi⟩
  have h2 : ptOf n (List.ofFn f) = f := funext fun l => by
    simp [ptOf, List.getD_eq_getElem?_getD]
  simp only [tbl] at h1
  rw [h1, h2, eq_cube]; rfl

theorem prodTo_eq {M : Type*} [CommMonoid M] (n : ℕ) (f : ℕ → M) :
    prodTo n f = ∏ i ∈ range n, f i := by
  induction n with
  | zero => rfl
  | succ n ih => rw [prodTo, Nat.fold_succ, ← prodTo, ih, Finset.prod_range_succ]

/-- **`eqZ` meets its specification.** -/
theorem eqZ_meets (l ρ : F) : eqZI l ρ = eqZS l ρ := by
  unfold eqZI eqZS
  refine congrArg (Array.ofFn (n := 128)) (funext fun i => ?_)
  rewrite [denS, lagW_eq _ _ _ (Nat.mod_lt _ (by decide)), xS_sNode]
  rfl

/-- **`rowW` meets its specification.** -/
theorem rowW_meets (l : F) (rhi : Array F) : rowWI l rhi = rowWS l rhi := by
  unfold rowWI rowWS
  refine congrArg (Array.ofFn (n := 2 ^ (6 + 8))) (funext fun k => ?_)
  have hk : k.val / 64 < 2 ^ 8 := by have := k.isLt; omega
  rewrite [denS, lagW_eq _ _ _ (Nat.mod_lt _ (by decide)), xS_sNode, eqTable_ofFn_getD _ hk]
  simp only [rowW, joinEquiv, Equiv.coe_fn_symm_mk, eq_cube, eqAtR]
  rfl

/-- **`phiRS` meets its specification** (`FRRingSwitch.phiApply_eq`). -/
theorem phiRS_meets (r : Array F) (a : F) : phiRSI r a = phiRSS r a := phiApply_eq _ _

/-- **`shiftEq` meets its specification** on points of equal length (`FRShift.shiftEq_eq`). -/
theorem shiftEq_meets (a b : Array F) (h : a.size = b.size) : shiftEqI a b = shiftEqS a b :=
  shiftEq_eq a.size a.toList b.toList (by simp) (by simp [h])

/-- **`tensorW` meets its specification.** -/
theorem tensorW_meets (j : ℕ) (r : Array K) : tensorWI j r = tensorWS j r := by
  unfold tensorWI tensorWS tensorTwin
  rewrite [prodTo_eq]
  refine Finset.prod_congr rfl fun v _ => ?_
  congr 3
  unfold wAtT
  split_ifs with hv
  · rw [sumTo_eq, wAt]
    refine Finset.sum_congr rfl fun i _ => ?_
    simp [wTab, Array.getD_eq_getD_getElem?, hv, List.getD_eq_getElem?_getD]
  · rfl

/-- **`slotW` meets its specification.** -/
theorem slotW_meets (s : ℕ) (θ r : Array F) : slotWI s θ r = slotWS s θ r := by
  unfold slotWI slotWS
  rewrite [sumTo_eq]
  refine Finset.sum_congr rfl fun σ hσ => ?_
  have h1 : σ < 2 ^ 10 := by simp at hσ; omega
  have h2 : slotBase s + σ < 2 ^ 10 := by
    simp at hσ; unfold slotBase; split <;> omega
  rw [eqTable_ofFn_getD _ h1, eqTable_ofFn_getD _ h2]

theorem eqPtsC_eq : ∀ (a b : List K), eqPtsC a b = eqPts a b
  | [], _ => by simp [eqPtsC, eqPts]
  | _ :: _, [] => by simp [eqPtsC, eqPts]
  | x :: a, y :: b => by
    have h := eqPtsC_eq a b
    simp only [eqPtsC, eqPts, List.zipWith_cons_cons, List.prod_cons] at h ⊢
    rw [h]; congr 1
    linear_combination (x + y - x * y) * CharTwo.two_eq_zero (R := K)

theorem wEvalC_eq (c : Array K) (r ρ : List K) :
    wEvalC c r ρ = ∑ k ∈ range c.size, c.getD k 0 * eqPts (r.map (sqIter k)) ρ := by
  unfold wEvalC
  simp only [eqPtsC_eq]
  rw [weightEval_fold]

/-- **`rsWeight` meets its specification** (`r″` of 7 coordinates). -/
theorem rsWeight_meets (r : Array F) (ps : List (Array K)) (κ : F) (ρ : Array K) (hr : r.size = 7) :
    rsWeightI r ps κ ρ = rsWeightS r ps κ ρ := by
  unfold rsWeightI rsWeightS
  refine congrArg List.sum (List.map_congr_left fun p _ => congrArg _ ?_)
  rw [wEvalC_eq, Array.size_map, phiTable_size, Array.length_toList, hr]
  refine Finset.sum_congr rfl fun k _ => ?_
  congr 1
  simp only [Array.getD_eq_getD_getElem?, Array.getElem?_map]
  cases (phiTable r.toList)[k]? <;> rfl

theorem digestMle_eq (θ : Array F) (e₀ e₁ : F) :
    digestMle (eqTable (List.ofFn (ptA 10 θ))) e₀ e₁ = mle (digTbl e₀ e₁) (ptA 10 θ) := by
  set g : ℕ → F := fun σ => eqAtR (ptA 10 θ) σ * if σ < 256 ∧ digBit e₀ e₁ σ then 1 else 0
  have hR : mle (digTbl e₀ e₁) (ptA 10 θ) = ∑ σ ∈ range (2 ^ 10), g σ := by
    rw [mle, ← Fin.sum_univ_eq_sum_range]
    refine Finset.sum_congr rfl fun u _ => ?_
    rw [eq_cube]; rfl
  have hs : ∑ σ ∈ range 256, g σ = ∑ σ ∈ range (2 ^ 10), g σ :=
    Finset.sum_subset (Finset.range_subset_range.2 (by norm_num)) fun σ _ hσ => by
      have : ¬σ < 256 := fun h => hσ (Finset.mem_range.2 h)
      simp only [g, this, false_and, ite_false, mul_zero]
  rw [hR, ← hs, digestMle, sumTo_eq]
  refine Finset.sum_congr rfl fun σ hσ => ?_
  have hσ' : σ < 256 := Finset.mem_range.1 hσ
  rewrite [eqTable_ofFn_getD _ (show σ < 2 ^ 10 by omega)]
  simp only [g, hσ', true_and]
  split_ifs <;> simp

/-- **`shiftTarget` meets its specification** (at the same `κ_s`). -/
theorem shiftTarget_meets (κs : F) (τ θ bnd : Array F) :
    shiftTargetI κs τ θ bnd = shiftTargetS κs τ θ bnd := by
  unfold shiftTargetI shiftTargetS shiftTarget
  dsimp only
  rw [digestMle_eq, digestMle_eq, prodTo_eq, eq_cube, ← Fin.prod_univ_eq_prod_range]
  congr 2
  refine Finset.prod_congr rfl fun l _ => ?_
  simp [lastBlk, Nat.testBit_two_pow_sub_one, ptA]

/-- **`targetS` meets the leaf kinds' specification**, for every number `b` of block bits. -/
theorem targetSLeaf_meets (b : ℕ) (r : Array F) : targetSLeafI r = targetSLeafS b r := by
  unfold targetSLeafI targetSLeafS
  refine congrArg (Array.ofFn (n := 64)) (funext fun σ => ?_)
  rw [FR.targetS, ← (joinEquiv 8 b).sum_comp, Fintype.sum_prod_type, sumTo_eq,
    ← Fin.sum_univ_eq_sum_range]
  refine Finset.sum_congr rfl fun hi _ => ?_
  have hj : ∀ t : Fin (2 ^ b), (join hi t).val % 256 = hi.val := fun t => by
    show (2 ^ 8 * t.val + hi.val) % 256 = hi.val
    have := hi.isLt; omega
  have hc : chainTab.getD (σ.val + 64 * hi.val) 0 = chainE (σ.val + 64 * hi.val) := by
    have : σ.val + 64 * hi.val < 2 ^ 14 := by have := σ.isLt; have := hi.isLt; omega
    simp only [chainTab, Array.getD_eq_getD_getElem?, Array.getElem?_ofFn, this, dite_true,
      Option.getD_some]
  simp only [show ∀ t, (joinEquiv 8 b) (hi, t) = join hi t from fun _ => rfl, eq_append_join, hj]
  set e₁ := eq (zLo r) (cube hi)
  set C := chainE (σ.val + 64 * hi.val)
  rw [show ∑ x : Fin (2 ^ b), e₁ * eq (fun l : Fin b => r.getD (1 + l) 0) (cube x) * C =
      e₁ * C * ∑ x : Fin (2 ^ b), eq (fun l : Fin b => r.getD (1 + l) 0) (cube x) by
    rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun _ _ => by ring,
    eq_sum_one, mul_one, hc, eqTable_ofFn_getD _ hi.isLt, mul_comm]
  simp only [e₁, eq_cube, eqAtR]

end Tables

/-! ## Controls (§5.6) -/

theorem skipNode_injOn (N : ℕ) (hN : N ≤ 128) :
    Set.InjOn (fun b : Fin N => xT b) (Finset.univ : Finset (Fin N)) := fun a _ b _ h => by
  have ha := a.isLt; have hb := b.isLt
  dsimp only at h
  rw [xT_eq, xT_eq] at h
  unfold xS at h
  have := congrArg Fin.val (skipNode_injective h)
  simp only [Nat.mod_eq_of_lt (show a.val < 128 by omega),
    Nat.mod_eq_of_lt (show b.val < 128 by omega)] at this
  exact Fin.ext this

set_option maxRecDepth 4000 in
/-- (+) The computed Lagrange weights are the Lagrange basis: weight `i` at node `i` is `1`. -/
theorem ctrl_lag_self {i : ℕ} (hi : i < 64) : (lagW xT 64 denS (xT i)).getD i 0 = 1 := by
  rewrite [denS, lagW_eq _ _ _ hi, lagrangeWeight_eq]
  exact Lagrange.eval_basis_self (i := (⟨i, hi⟩ : Fin 64)) (skipNode_injOn 64 (by norm_num))
    (Finset.mem_univ _)

/-- (−) … and weight `i` at another node `j` is `0`. -/
theorem ctrl_lag_other {i j : ℕ} (hi : i < 64) (hj : j < 64) (hij : i ≠ j) :
    (lagW xT 64 denS (xT j)).getD i 0 = 0 := by
  rewrite [denS, lagW_eq _ _ _ hi, lagrangeWeight_eq]
  exact Lagrange.eval_basis_of_ne (s := Finset.univ) (v := fun b : Fin 64 => xT b)
    (i := ⟨i, hi⟩) (j := ⟨j, hj⟩) (fun h => hij (congrArg Fin.val h)) (Finset.mem_univ _)

/-- A Boolean point as an array (10 coordinates). -/
def cubeA (u : Fin (2 ^ 10)) : Array F := Array.ofFn (cube (R := F) u)

theorem eqAtR_cubeA (u : Fin (2 ^ 10)) {σ : ℕ} (hσ : σ < 2 ^ 10) :
    eqAtR (ptA 10 (cubeA u)) σ = if u.val = σ then 1 else 0 := by
  have : ptA 10 (cubeA u) = cube u := funext fun l => by
    simp [ptA, cubeA, Array.getD_eq_getD_getElem?]
  rw [this, show eqAtR (cube (R := F) u) σ = eq (cube u) (cube (⟨σ, hσ⟩ : Fin (2 ^ 10))) by
    rw [eq_cube]; rfl, eq_cube_cube]
  simp [Fin.ext_iff]

/-- (+) The slot weight at the Boolean points `θ = σ₀`, `r = base + σ₀` is `1`. -/
theorem ctrl_slotW_hit (s : ℕ) (σ₀ : Fin 256) :
    slotWI s (cubeA ⟨σ₀, by omega⟩) (cubeA ⟨slotBase s + σ₀, by unfold slotBase; split <;> omega⟩)
      = 1 := by
  rw [slotW_meets, slotWS, Finset.sum_eq_single σ₀.val]
  · rw [eqAtR_cubeA _ (by omega), eqAtR_cubeA _ (by unfold slotBase; split <;> omega)]; simp
  · intro σ hσ hne
    rw [eqAtR_cubeA _ (by simp at hσ; omega)]
    simp [Ne.symm hne]
  · simp

/-- (−) … and `0` when `r` is the position of another slot index. -/
theorem ctrl_slotW_miss (s : ℕ) (σ₀ σ₁ : Fin 256) (h : σ₀ ≠ σ₁) :
    slotWI s (cubeA ⟨σ₀, by omega⟩) (cubeA ⟨slotBase s + σ₁, by unfold slotBase; split <;> omega⟩)
      = 0 := by
  rw [slotW_meets, slotWS]
  refine Finset.sum_eq_zero fun σ hσ => ?_
  have hσ' : σ < 256 := Finset.mem_range.1 hσ
  rw [eqAtR_cubeA _ (by omega), eqAtR_cubeA _ (by unfold slotBase; split <;> omega)]
  by_cases h0 : σ₀.val = σ
  · have : ¬(σ₁.val = σ) := fun h' => h (Fin.ext (by omega))
    simp [h0, this]
  · simp [h0]

end Impl
end FR
