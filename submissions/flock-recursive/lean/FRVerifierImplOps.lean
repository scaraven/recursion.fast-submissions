-- New for `flock-recursive` (BLUEPRINT §3, A.8, A.9; stage S-F2, track L-cert).
-- Split from `FRVerifierImpl` by S-E3 (mechanical: the op implementations, specifications and
-- `Meets` lemmas that do not depend on the node's M rows, so that `FRVIRTemplates` can use them).
import FRVIRFinalsSG
import FRVIREval
import FRRSEval
import FRVerifier
import FRBlockChain
import FRPubTarget
import FRKindWeight

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

/-- **`wEvalC` at a point in `F`** (S-T1; `wEvalCF_eq`): the point squared in `F` per stage. -/
def wEvalCF (c : Array K) (r : Array F) (ρ : List K) : K :=
  (Nat.fold c.size (fun k _ (p : K × Array F) =>
    (p.1 + c.getD k 0 * eqPtsC (p.2.toList.map K.ofF) ρ, p.2.map F.sq)) (0, r)).1

/-- Claim 2's stage fold (revision 3.16): `Σ_{k<|c|} c_k eq(q_hi, ρ_hi)·kwI(β^(2^k), q_blk, ρ_blk)`,
`q = r^(2^k)` (hi: the first 7 coordinates; blk: the `|ρ| − 7` block coordinates). -/
def wEvalKC (c : Array K) (β : K) (r ρ : List K) : K :=
  let ρh := ρ.take 7
  let ρb := (ρ.drop 7).toArray
  (Nat.fold c.size (fun k _ (p : K × List K × K) =>
    (p.1 + c.getD k 0 * (eqPtsC (p.2.1.take 7) ρh *
        KW.kwI ρb.size p.2.2 (fun l => (p.2.1.drop 7).toArray.getD l 0) (fun l => ρb.getD l 0)),
     p.2.1.map fun a => a * a, p.2.2 * p.2.2)) (0, r, β)).1

/-- One stage of `wEvalKF`: add `c_k eq(q_hi, ρ_hi) T_k` (`T_k` the two Horner sums over the levels,
`s_l = 1 + q_l + ρ_l`), then square the point and the blocks' `F` factors. -/
def kfStep (c : Array K) (ρh : List K) (oρ : Array K) (k : ℕ)
    (st : K × Array F × List (List (F × K)) × List (List (F × K))) :
    K × Array F × List (List (F × K)) × List (List (F × K)) :=
  let q := st.2.1
  let s : ℕ → K := fun l => K.ofF (q.getD (7 + l) 0) + oρ.getD l 0
  (st.1 + c.getD k 0 * (eqPtsC ((q.toList.take 7).map K.ofF) ρh *
      (KW.hornerK s 0 (st.2.2.1.map KW.gsum) + KW.hornerK s 1 (st.2.2.2.map KW.gsum))),
    q.map F.sq, KW.sqG st.2.2.1, KW.sqG st.2.2.2)

/-- **Claim 2's stage fold, fast** (S-T1; `wEvalKF_eq`): the claim point `r` in `F` (23
coordinates), `ρ` of 23. The blocks' factors (`KW.mkEnt`: the point's side in `F`, `ρ`'s in `K`) are
made once; per stage the `F` factors are squared (`KW.sqG`), one `smulF` per block. -/
def wEvalKF (c : Array K) (β : F) (r : Array F) (ρ : List K) : K :=
  let ρb := (ρ.drop 7).toArray
  let gK : ℕ → Bool → K := fun l b => if b then ρb.getD l 0 else 1 - ρb.getD l 0
  let fF : ℕ → Bool → F := fun l b => if b then r.getD (7 + l) 0 else 1 - r.getD (7 + l) 0
  (Nat.fold c.size (fun k _ => kfStep c (ρ.take 7) (ρb.map (1 + ·)) k)
    (0, r, KW.skelM.map (KW.mkEnt (β ^ ·) fF gK), KW.skelP.map (KW.mkEnt (β ^ ·) fF gK))).1

/-- **`rsWeight`, fast** (S-T1; `rsWeightF_eq`): a claim point in `F` (every coordinate's `f₁` is
`0`) runs `wEvalKF` (claim 2, at 23 coordinates and `|ρ| = 23`) or `wEvalCF`; otherwise as
`rsWeightI`. -/
def rsWeightF (r : Array F) (ps : List (Array K)) (κ β : F) (ρ : Array K) : K :=
  let c := (phiTable r.toList).map K.ofF
  ((ps.zipIdx).map fun p => K.ofF κ ^ p.2 *
    (if p.1.all (·.f₁ == 0) then
      (if p.2 = 1 then
        (if p.1.size = 23 ∧ ρ.size = 23 then wEvalKF c β (p.1.map (·.f₀)) ρ.toList
         else wEvalKC c (K.ofF β) p.1.toList ρ.toList)
       else wEvalCF c (p.1.map (·.f₀)) ρ.toList)
     else
      (if p.2 = 1 then wEvalKC c (K.ofF β) p.1.toList ρ.toList else wEvalC c p.1.toList ρ.toList))).sum

/-- **`rsWeight`** (A.8, revisions 3.9, 3.16): `Σ_j κ^j Ŵ_j(ρ)`, `Ŵ_j = Σ_{k<128} c_k(r″)
eq(r_j^{2^k}, ρ)` except claim 2 (index 1), weighted by the kind factor (`wEvalKC`); the
coefficients `c_k(r″)` (`FRRingSwitch.phiTable`) computed once over F. -/
def rsWeightI (r : Array F) (ps : List (Array K)) (κ β : F) (ρ : Array K) : K :=
  let c := (phiTable r.toList).map K.ofF
  ((ps.zipIdx).map fun p => K.ofF κ ^ p.2 *
    (if p.2 = 1 then wEvalKC c (K.ofF β) p.1.toList ρ.toList
     else wEvalC c p.1.toList ρ.toList)).sum

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

/-- The last block of `shiftTarget`'s `bnd` as an 18-coordinate point (entries `4 … 21`; revision
3.15: `1^(m−14) ‖ 0^(32−m)`, `finSh`'s `bndOps`). -/
def lastOf (bnd : Array F) : Fin 18 → F := fun l => bnd.getD (4 + l.val) 0

/-- **`shiftTarget`** with `κ_s` (A.9 `finSh` (i); the leaf's native reading, P2 §7.5 (4);
revision 3.15: on 18 coordinates): `eq(τ, last) · h̃(θ) + κ_s · s̃(θ)`, `bnd = [s_lo, s_hi, h_lo,
h_hi] ‖ last`. -/
def shiftTargetI (κs : F) (τ θ bnd : Array F) : F :=
  let Eθ := eqTable (List.ofFn (ptA 10 θ))
  prodTo 18 (fun l => τ.getD l 0 * bnd.getD (4 + l) 0 + (1 - τ.getD l 0) * (1 - bnd.getD (4 + l) 0)) *
      digestMle Eθ (bnd.getD 2 0) (bnd.getD 3 0) +
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

/-- Claim 2's weight at one Frobenius stage (`KW.kwS`, revision 3.16): `eq(q_hi, ρ_hi)` on the 7 high
position coordinates times the kind-weighted block weight on the `|ρ| − 7` block coordinates. -/
def kwSL (β : K) (q ρ : List K) : K :=
  eqPts (q.take 7) (ρ.take 7) *
    KW.kwS (ρ.length - 7) β (ptOf (ρ.length - 7) (q.drop 7)) (ptOf (ρ.length - 7) (ρ.drop 7))

/-- **`rsWeight`'s specification** (A.8, L-R4 `weight_mle`'s right side; revision 3.16):
`Σ_j κ^j Σ_{k<128} c_k(r″) w_{j,k}` with `w_{j,k} = eq(r_j^{2^k}, ρ)`, except claim 2 (index 1):
`w_{1,k} = kwSL(β^(2^k), r_1^{2^k}, ρ)` (`FRRingSwitch.rsWeight_kind_eq` is its Φ form);
`c_k(r″)` the coefficients of `Φ_{r″}` (`FRRingSwitch.phiTable`). -/
def rsWeightS (r : Array F) (ps : List (Array K)) (κ β : F) (ρ : Array K) : K :=
  ((ps.zipIdx).map fun p => K.ofF κ ^ p.2 * ∑ k ∈ range 128,
    K.ofF ((phiTable r.toList).getD k 0) *
      (if p.2 = 1 then kwSL (sqIter k (K.ofF β)) (p.1.toList.map (sqIter k)) ρ.toList
       else eqPts (p.1.toList.map (sqIter k)) ρ.toList)).sum

/-- A digest's bits as a table over the 10-bit slot index (`0` from `σ = 256` on). -/
def digTbl (e₀ e₁ : F) : Fin (2 ^ 10) → F := fun u => if u.val < 256 ∧ digBit e₀ e₁ u then 1 else 0

/-- **`shiftTarget`'s specification** with `κ_s` (`FRShift.shiftTargetAt`, revision 3.15: on 18
coordinates): `eq(τ, last) h̃V(θ) + κ_s s̃V(θ)`, `sV`, `hV` the boundary digests `bnd[0,1]`,
`bnd[2,3]` as bit tables, `last = bnd[4 … 21]` (`shiftTargetS_pad`: at a zero-padded `τ` and the
kind's padded last block, `FRShift.shiftTarget` on `m − 14` coordinates). -/
def shiftTargetS (κs : F) (τ θ bnd : Array F) : F :=
  shiftTargetAt (ptA 10 θ) (ptA 18 τ) (lastOf bnd) κs (digTbl (bnd.getD 0 0) (bnd.getD 1 0))
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

/-- `n` squarings in `F` by `F.sq` (≈ 20 ns, against ≈ 100 ns for `a * a`). -/
def sqItF : ℕ → F → F
  | 0, a => a
  | n + 1, a => sqItF n (F.sq a)

theorem sqItF_eq : ∀ (n : ℕ) (a : F), sqItF n a = sqIter n a
  | 0, _ => rfl
  | n + 1, a => by rw [sqItF, sqItF_eq n, F.sq_eq_mul]; rfl

/-- `FRRingSwitch.frobMapC` with `F.sq`. -/
def frobMapF : List (ℕ × F) → F → F
  | [], a => a
  | (s, f) :: st, a => frobMapF st (a + f * sqItF s a)

theorem frobMapF_eq : ∀ (st : List (ℕ × F)) (a : F), frobMapF st a = frobMapC st a
  | [], _ => rfl
  | (s, f) :: st, a => by rw [frobMapF, frobMapC, sqItF_eq, frobMapF_eq st]

/-- **`phiRS`, fast** (S-T1; `phiRSF_eq`): `phiRSI` with its 127 squarings by `F.sq`. -/
def phiRSF (r : Array F) (a : F) : F := frobMapF (stages (r.toList.length - 1) r.toList) a

theorem phiRSF_eq (r : Array F) (a : F) : phiRSF r a = phiRSI r a := frobMapF_eq _ _

/-- (+) One squaring stage: `sqItF 1 a = a * a`. (−) `sqItF` is not the identity: `sqItF 1 u ≠ u`
for `F`'s `u = ⟨0, 1⟩` (`u^2 = u + β`). -/
theorem sqItF_ctrl : sqItF 1 (⟨0, 1⟩ : F) = ⟨0, 1⟩ * ⟨0, 1⟩ ∧ sqItF 1 (⟨0, 1⟩ : F) ≠ ⟨0, 1⟩ := by
  decide +kernel

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

/-! ### `tensorW`'s fast twin (S-E8) -/

/-- `Ŵ_v(D[x ⋅ 2^{8b}])` for a byte `x`, `v < 20`, `b < 3`: entry `x` of table `3v + b`. -/
def wByte : Array (Array F) := Array.ofFn (n := 3 * logNMax) fun vb =>
  Array.ofFn (n := 256) fun x => sumTo 8 fun i =>
    if x.val.testBit i && 8 * (vb.val % 3) + i < logNMax then
      (wTab.getD (vb.val / 3) #[]).getD (8 * (vb.val % 3) + i) 0 else 0

/-- Byte `b` of `j`'s contribution to `Ŵ_v(D[j])`, by table (`wAtF`'s terms, as the proof reads them). -/
def wB (v b j : ℕ) : F := (wByte.getD (3 * v + b) #[]).getD (j / 2 ^ (8 * b) % 2 ^ 8) 0

/-- **`wAtT` by three byte tables** (S-E8): three lookups instead of a 20-term sum (`wAtF_eq`); it is
`wB v 0 j + wB v 1 j + wB v 2 j` with the powers as literals (`2 ^ k` runs as a loop here). -/
def wAtF (v j : ℕ) : F :=
  if v < logNMax then
    (wByte.getD (3 * v) #[]).getD (j % 256) 0 + (wByte.getD (3 * v + 1) #[]).getD (j / 256 % 256) 0 +
      (wByte.getD (3 * v + 2) #[]).getD (j / 65536 % 256) 0
  else wAtD v j

theorem wB_eq (v b j : ℕ) (hv : v < logNMax) (hb : b < 3) :
    wB v b j =
      ∑ i ∈ range 8, if j.testBit (8 * b + i) && 8 * b + i < logNMax then
        (wTab.getD v #[]).getD (8 * b + i) 0 else 0 := by
  have h1 : 3 * v + b < 3 * logNMax := by omega
  have h2 : j / 2 ^ (8 * b) % 2 ^ 8 < 256 := Nat.mod_lt _ (by norm_num)
  have e1 : (3 * v + b) % 3 = b := by omega
  have e2 : (3 * v + b) / 3 = v := by omega
  simp only [wB, wByte, Array.getD_eq_getD_getElem?, Array.getElem?_ofFn, h1, h2, dite_true,
    Option.getD_some, e1, e2, sumTo_eq]
  refine sum_congr rfl fun i hi => ?_
  have hi8 : i < 8 := mem_range.1 hi
  have ht : (j / 2 ^ (8 * b) % 2 ^ 8).testBit i = j.testBit (8 * b + i) := by
    rw [Nat.testBit_mod_two_pow, Nat.testBit_div_two_pow]; simp [hi8, add_comm]
  rw [ht]

theorem wAtF_eq (v j : ℕ) : wAtF v j = wAtT v j := by
  unfold wAtF wAtT
  split_ifs with hv
  · rw [show j % 256 = j / 2 ^ (8 * 0) % 2 ^ 8 by norm_num, show j / 256 % 256 = j / 2 ^ (8 * 1) % 2 ^ 8 by
      norm_num, show j / 65536 % 256 = j / 2 ^ (8 * 2) % 2 ^ 8 by norm_num]
    change wB v 0 j + wB v 1 j + wB v 2 j = _
    rw [wB_eq v 0 j hv (by norm_num), wB_eq v 1 j hv (by norm_num), wB_eq v 2 j hv (by norm_num),
      sumTo_eq]
    set g : ℕ → F := fun i => if j.testBit i && i < logNMax then (wTab.getD v #[]).getD i 0 else 0
    have hz : ∑ x ∈ range 4, g (20 + x) = 0 := sum_eq_zero fun x _ => by simp [g, logNMax]
    have h20 : ∑ i ∈ range 20, g i = ∑ i ∈ range logNMax, if j.testBit i then (wTab.getD v #[]).getD i 0 else 0 :=
      sum_congr rfl fun i hi => by simp [g, mem_range.1 hi, logNMax]
    have hs : ∑ i ∈ range 20, g i = ∑ x ∈ range 8, g x + ∑ x ∈ range 8, g (8 + x) + ∑ x ∈ range 8, g (16 + x) := by
      rw [← add_zero (∑ i ∈ range 20, g i), ← hz, ← sum_range_add, show 20 + 4 = (8 + 8) + 8 from rfl,
        sum_range_add g (8 + 8) 8, sum_range_add g 8 8]
    rw [← h20, hs]
    rfl
  · rfl
/-- **`tensorW`'s fast twin** (S-E8): `wAtF`, and `r_v · Ŵ` as `smulF` (two `F` products instead
of a `K` product); `tensorWF_eq`. -/
def tensorWF (j : ℕ) (r : Array K) : K :=
  prodTo r.size fun v => 1 - r.getD v 0 + K.smulF (wAtF v j) (r.getD v 0)

theorem tensorWF_eq (j : ℕ) (r : Array K) : tensorWF j r = tensorWI j r :=
  congrArg (prodTo r.size) (funext fun v => by
    rw [wAtF_eq, K.smulF_eq_mul, ← K.algebraMap_eq_ofF, mul_comm])
/-- **`tensorW` at a point in `F`** (S-T1; `tensorWG_eq`): every factor in `F` (two F products
instead of a K product and a `smulF`); otherwise `tensorWF`. -/
def tensorWG (j : ℕ) (r : Array K) : K :=
  if r.all (·.f₁ == 0) then
    K.ofF (prodTo r.size fun v => 1 - (r.getD v 0).f₀ + wAtF v j * (r.getD v 0).f₀)
  else tensorWF j r

theorem prodTo_ofF (n : ℕ) (f : ℕ → F) : K.ofF (prodTo n f) = prodTo n fun v => K.ofF (f v) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    show K.ofF (prodTo n f * f n) = prodTo n (fun v => K.ofF (f v)) * K.ofF (f n)
    rw [← ih]; exact map_mul K.ofFRingHom _ _

theorem K_ofF_f0 : ∀ x : K, x.f₁ = 0 → x = K.ofF x.f₀
  | ⟨_, _⟩, h => by subst h; rfl

theorem getD_inF {r : Array K} (h : r.all (·.f₁ == 0) = true) (v : ℕ) :
    r.getD v 0 = K.ofF (r.getD v 0).f₀ := by
  rw [Array.all_eq_true] at h
  rw [Array.getD_eq_getD_getElem?]
  by_cases hv : v < r.size
  · rw [Array.getElem?_eq_getElem hv, Option.getD_some]
    have h1 : (r[v]).f₁ = 0 := by simpa using h v hv
    exact K_ofF_f0 _ h1
  · rw [Array.getElem?_eq_none (by omega)]; rfl

theorem tensorWG_eq (j : ℕ) (r : Array K) : tensorWG j r = tensorWF j r := by
  unfold tensorWG
  split_ifs with h
  · rw [prodTo_ofF, tensorWF]
    refine congrArg (prodTo r.size) (funext fun v => ?_)
    set x := (r.getD v 0).f₀
    rw [getD_inF h v, K.smulF_eq_mul]
    change K.ofFRingHom (1 - x + wAtF v j * x) = _
    simp only [map_add, map_sub, map_mul, map_one]
    rfl
  · rfl

/-- (+) The F path's reading of a point in `F` is exact (`K_ofF_f0`): `ofF 3` is `ofF 3`'s `f₀`. -/
theorem inF_pos : (#[K.ofF 3]).all (·.f₁ == 0) = true ∧ K.ofF 3 = K.ofF (K.ofF 3).f₀ := by
  decide +kernel

/-- (−) Outside `F` the projection to `f₀` loses `u`, so the guard of `tensorWG` and `rsWeightF` is
load-bearing: `u ≠ ofF u.f₀`, and the guard rejects it. -/
theorem inF_neg : K.u ≠ K.ofF K.u.f₀ ∧ (#[K.u]).all (·.f₁ == 0) = false := by decide +kernel

/-! #### Controls (S-E8) -/

/-- (+) `tensorW` at `j = 0`: `Π (1 + r_v)`; the twin agrees (`tensorWF_eq`). -/
theorem tensorW_pos : tensorWI 0 #[K.u] = 1 + K.u := by decide +kernel

theorem tensorWF_pos : tensorWF 0 #[K.u] = 1 + K.u := (tensorWF_eq 0 _).trans tensorW_pos

/-- (−) The third byte table is needed: its entry for `j = 2^16` is `Ŵ_0(D[2^16]) ≠ 0`, so a twin
reading only bits `0 … 15` is wrong at `j = 2^16`. -/
theorem wByte_neg : (wByte.getD 2 #[]).getD 1 0 ≠ 0 := by decide +kernel

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

theorem wEvalKC_fold (c : Array K) (β : K) (r ρ : List K) (n : ℕ) :
    Nat.fold n (fun k _ (p : K × List K × K) =>
      (p.1 + c.getD k 0 * (eqPtsC (p.2.1.take 7) (ρ.take 7) *
          KW.kwI (ρ.drop 7).toArray.size p.2.2 (fun l => (p.2.1.drop 7).toArray.getD l 0)
            (fun l => (ρ.drop 7).toArray.getD l 0)),
       p.2.1.map fun a => a * a, p.2.2 * p.2.2)) (0, r, β) =
    (∑ k ∈ range n, c.getD k 0 * (eqPtsC ((r.map (sqIter k)).take 7) (ρ.take 7) *
        KW.kwI (ρ.drop 7).toArray.size (sqIter k β)
          (fun l => ((r.map (sqIter k)).drop 7).toArray.getD l 0)
          (fun l => (ρ.drop 7).toArray.getD l 0)),
      r.map (sqIter n), sqIter n β) := by
  induction n with
  | zero => simp [sqIter]
  | succ n ih =>
    rw [Nat.fold_succ, ih, Finset.sum_range_succ, List.map_map]
    congr 2
    · exact List.map_congr_left fun a _ => by simp [sqIter_succ']
    · rw [sqIter_succ']

theorem toArray_getD_list (L : List K) (l : ℕ) : L.toArray.getD l 0 = L.getD l 0 := by
  simp [Array.getD_eq_getD_getElem?, List.getD_eq_getElem?_getD]

/-- **Claim 2's fold meets `kwSL`** (at least 16 block coordinates). -/
theorem wEvalKC_eq (c : Array K) (β : K) (r ρ : List K) (hρ : 23 ≤ ρ.length) :
    wEvalKC c β r ρ = ∑ k ∈ range c.size, c.getD k 0 * kwSL (sqIter k β) (r.map (sqIter k)) ρ := by
  dsimp only [wEvalKC]
  rw [wEvalKC_fold]
  dsimp only
  refine Finset.sum_congr rfl fun k _ => ?_
  have hn : (ρ.drop 7).toArray.size = ρ.length - 7 := by simp
  rw [kwSL, hn, KW.kwI_eq (by omega), eqPtsC_eq]
  congr 3 <;> funext l <;> simp only [ptOf, toArray_getD_list]

/-! ## S-T1: the fast folds meet the reference folds -/

/-- A fold that commutes with a map of states. -/
theorem fold_sim {σ τ : Type*} (g : σ → τ) (f1 : ℕ → σ → σ) (f2 : ℕ → τ → τ)
    (h : ∀ k s, f2 k (g s) = g (f1 k s)) (s : σ) :
    ∀ n, Nat.fold n (fun k _ => f2 k) (g s) = g (Nat.fold n (fun k _ => f1 k) s)
  | 0 => rfl
  | n + 1 => by rw [Nat.fold_succ, Nat.fold_succ, fold_sim g f1 f2 h s n, h]

theorem ofF_mul' (a b : F) : K.ofF (a * b) = K.ofF a * K.ofF b := map_mul K.ofFRingHom a b

theorem ofF_sq (a : F) : K.ofF (F.sq a) = K.ofF a * K.ofF a := by rw [F.sq_eq_mul, ofF_mul']

/-- **`wEvalCF` is `wEvalC` at the embedded point.** -/
theorem wEvalCF_eq (c : Array K) (r : Array F) (ρ : List K) :
    wEvalCF c r ρ = wEvalC c (r.toList.map K.ofF) ρ := by
  unfold wEvalCF wEvalC
  have := fold_sim (fun p : K × Array F => (p.1, p.2.toList.map K.ofF))
    (fun k (p : K × Array F) => (p.1 + c.getD k 0 * eqPtsC (p.2.toList.map K.ofF) ρ, p.2.map F.sq))
    (fun k (p : K × List K) => (p.1 + c.getD k 0 * eqPtsC p.2 ρ, p.2.map fun a => a * a))
    (fun k p => by simp [Array.toList_map, List.map_map, Function.comp_def, ofF_sq]) (0, r) c.size
  exact (congrArg Prod.fst this).symm

theorem sqIter_ofF (k : ℕ) (a : F) : sqIter k (K.ofF a) = K.ofF (sqIter k a) := by
  rw [sqIter_eq, sqIter_eq]; exact (map_pow K.ofFRingHom a _).symm

theorem sqIter_zeroF (k : ℕ) : sqIter k (0 : F) = 0 := by rw [sqIter_eq]; simp

theorem sq_ne_zero_iff (a : F) : (F.sq a != 0) = (a != 0) := by
  rw [F.sq_eq_mul, Bool.eq_iff_iff]
  simp only [bne_iff_ne, ne_eq, mul_self_eq_zero]

theorem filter_map_comm {α : Type*} (P : α → Bool) (f : α → α) (hP : ∀ x, P (f x) = P x) :
    ∀ L : List α, (L.filter P).map f = (L.map f).filter P
  | [] => rfl
  | x :: L => by
    simp only [List.filter_cons, List.map_cons, hP]
    split <;> simp [filter_map_comm P f hP L]

/-- **The next stage's blocks are the squares** (Frobenius on `F`). -/
theorem mkEnt_sq (β : F) (q : ℕ → F) (gK : ℕ → Bool → K) (g : List (List (ℕ × Bool) × List ℕ)) :
    (KW.mkEnt (β ^ ·) (fun l b => if b then q l else 1 - q l) gK g).map (fun p => (F.sq p.1, p.2)) =
      KW.mkEnt (F.sq β ^ ·) (fun l b => if b then F.sq (q l) else 1 - F.sq (q l)) gK g := by
  let φ : F →+* F := frobenius F 2
  have hφ : ∀ a : F, F.sq a = φ a := fun a => by rw [F.sq_eq_mul, frobenius_def, pow_two]
  unfold KW.mkEnt
  rw [filter_map_comm _ _ (fun x => sq_ne_zero_iff x.1), List.map_map]
  congr 1
  refine List.map_congr_left fun p _ => ?_
  simp only [Function.comp_apply, hφ, map_mul, map_list_sum, map_list_prod, List.map_map,
    Function.comp_def, map_pow]
  congr 3
  exact List.map_congr_left fun b _ => by split_ifs <;> simp [map_sub, map_one]

/-- Stage `k`'s blocks: the point's coordinates and `β` raised to `2^k`. -/
def gmK (sk : List (List (List (ℕ × Bool) × List ℕ))) (β : F) (r : Array F) (gK : ℕ → Bool → K)
    (k : ℕ) : List (List (F × K)) :=
  sk.map (KW.mkEnt (sqIter k β ^ ·)
    (fun l b => if b then sqIter k (r.getD (7 + l) 0) else 1 - sqIter k (r.getD (7 + l) 0)) gK)

theorem sqG_gmK (sk : List (List (List (ℕ × Bool) × List ℕ))) (β : F) (r : Array F)
    (gK : ℕ → Bool → K) (k : ℕ) : KW.sqG (gmK sk β r gK k) = gmK sk β r gK (k + 1) := by
  unfold KW.sqG gmK
  rw [List.map_map]
  refine List.map_congr_left fun g _ => ?_
  rw [Function.comp_apply, mkEnt_sq]
  simp only [F.sq_eq_mul, ← sqIter_succ']

/-- **The fast fold's invariant**: after `n` stages, the sum of the stage values, the point and
the blocks at `2^n`. -/
theorem kf_fold (c : Array K) (ρh : List K) (oρ : Array K) (β : F) (r : Array F)
    (gK : ℕ → Bool → K) : ∀ n,
    Nat.fold n (fun k _ => kfStep c ρh oρ k) (0, r, gmK KW.skelM β r gK 0, gmK KW.skelP β r gK 0) =
    (∑ k ∈ range n, c.getD k 0 * (eqPtsC (((r.map (sqIter k)).toList.take 7).map K.ofF) ρh *
        (KW.hornerK (fun l => K.ofF ((r.map (sqIter k)).getD (7 + l) 0) + oρ.getD l 0) 0
            ((gmK KW.skelM β r gK k).map KW.gsum) +
          KW.hornerK (fun l => K.ofF ((r.map (sqIter k)).getD (7 + l) 0) + oρ.getD l 0) 1
            ((gmK KW.skelP β r gK k).map KW.gsum))),
      r.map (sqIter n), gmK KW.skelM β r gK n, gmK KW.skelP β r gK n)
  | 0 => by simp [sqIter]
  | n + 1 => by
    rw [Nat.fold_succ, kf_fold c ρh oρ β r gK n, kfStep]
    simp only [sum_range_succ, sqG_gmK, Array.map_map, Function.comp_def, F.sq_eq_mul,
      ← sqIter_succ']

theorem getD_map_lt {α : Type*} (A : Array α) (f : α → α) (d : α) {i : ℕ} (hi : i < A.size) :
    (A.map f).getD i d = f (A.getD i d) := by
  simp [Array.getD_eq_getD_getElem?, hi]

/-- **`wEvalKF` meets claim 2's stage sum** (`wEvalKC_eq`'s right side) at a point in `F`. -/
theorem wEvalKF_eq (c : Array K) (β : F) (r : Array F) (ρ : List K) (hr : r.size = 23)
    (hρ : ρ.length = 23) : wEvalKF c β r ρ = ∑ k ∈ range c.size,
      c.getD k 0 * kwSL (sqIter k (K.ofF β)) ((r.toList.map K.ofF).map (sqIter k)) ρ := by
  unfold wEvalKF
  refine (congrArg Prod.fst (kf_fold c (ρ.take 7) ((ρ.drop 7).toArray.map (1 + ·)) β r
    (fun l b => if b then (ρ.drop 7).toArray.getD l 0 else 1 - (ρ.drop 7).toArray.getD l 0)
      c.size)).trans ?_
  dsimp only
  refine sum_congr rfl fun k _ => congrArg _ ?_
  have h16 : ρ.length - 7 = 16 := by omega
  rw [kwSL, h16, eqPtsC_eq]
  congr 1
  · simp [Array.toList_map, List.map_take, List.map_map, Function.comp_def, sqIter_ofF]
  · have hq : ptOf 16 (((r.toList.map K.ofF).map (sqIter k)).drop 7) =
        fun l : Fin 16 => K.ofF (sqIter k (r.getD (7 + l) 0)) := by
      funext l
      have := l.isLt
      simp [ptOf, List.getD_eq_getElem?_getD, Array.getD_eq_getD_getElem?, hr, sqIter_ofF,
        show 7 + l.val < 23 by omega]
    have hρ' : ptOf 16 (ρ.drop 7) = fun l : Fin 16 => (ρ.drop 7).toArray.getD l 0 := by
      funext l; simp only [ptOf, toArray_getD_list]
    rw [hq, hρ', sqIter_ofF]
    refine (KW.kwS_fast _ _ _ _ fun l hl => ?_).symm
    have hb : ((ρ.drop 7).toArray).size = 16 := by simp; omega
    rw [getD_map_lt _ _ _ (by rw [hr]; omega), getD_map_lt _ _ _ (by rw [hb]; exact hl)]

theorem ofF_f0 (a : Array K) (h : a.all (·.f₁ == 0) = true) :
    (a.map (·.f₀)).toList.map K.ofF = a.toList := by
  rw [Array.toList_map, List.map_map]
  conv_rhs => rw [← List.map_id a.toList]
  refine List.map_congr_left fun x hx => ?_
  rw [← Array.all_toList, List.all_eq_true] at h
  have h1 : x.f₁ = 0 := by simpa using h x hx
  obtain ⟨x0, x1⟩ := x
  simp only at h1
  subst h1
  rfl

/-- **`rsWeightF` is `rsWeightI`**, for every input. -/
theorem rsWeightF_eq (r : Array F) (ps : List (Array K)) (κ β : F) (ρ : Array K) :
    rsWeightF r ps κ β ρ = rsWeightI r ps κ β ρ := by
  unfold rsWeightF rsWeightI
  refine congrArg List.sum (List.map_congr_left fun p _ => congrArg _ ?_)
  split_ifs with hF h1 h23
  · rw [wEvalKF_eq _ _ _ _ (by simp [h23.1]) (by simp [h23.2]),
      wEvalKC_eq _ _ _ _ (by simp [h23.2]), ofF_f0 _ hF]
  · rfl
  · rw [wEvalCF_eq, ofF_f0 _ hF]
  · rfl
  · rfl

/-- (+) The guard takes the fast path at a point in `F`. -/
theorem rsF_guard_pos : (#[K.ofF 1, K.ofF 0]).all (·.f₁ == 0) = true := by decide +kernel

/-- (−) … and falls back at a point outside `F` (`u`). -/
theorem rsF_guard_neg : (#[K.ofF 1, K.u]).all (·.f₁ == 0) = false := by decide +kernel

/-- **`rsWeight` meets its specification** (`r″` of 7 coordinates, `ρ` of at least 23: the block
coordinates cover the node layout's `2^16` blocks). -/
theorem rsWeight_meets (r : Array F) (ps : List (Array K)) (κ β : F) (ρ : Array K) (hr : r.size = 7)
    (hρ : 23 ≤ ρ.size) : rsWeightI r ps κ β ρ = rsWeightS r ps κ β ρ := by
  unfold rsWeightI rsWeightS
  refine congrArg List.sum (List.map_congr_left fun p _ => congrArg _ ?_)
  have hc : ((phiTable r.toList).map K.ofF).size = 128 := by
    rw [Array.size_map, phiTable_size, Array.length_toList, hr]; norm_num
  have hg : ∀ k, ((phiTable r.toList).map K.ofF).getD k 0 = K.ofF ((phiTable r.toList).getD k 0) :=
    fun k => by
      simp only [Array.getD_eq_getD_getElem?, Array.getElem?_map]
      cases (phiTable r.toList)[k]? <;> rfl
  split_ifs
  · rw [wEvalKC_eq _ _ _ _ (by simpa using hρ), hc]
    exact Finset.sum_congr rfl fun k _ => by rw [hg]
  · rw [wEvalC_eq, hc]
    exact Finset.sum_congr rfl fun k _ => by rw [hg]

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
  unfold shiftTargetI shiftTargetS shiftTargetAt
  dsimp only
  rw [digestMle_eq, digestMle_eq, prodTo_eq, ← Fin.prod_univ_eq_prod_range]
  rfl

/-! ## Zero-padded `τ` (revision 3.15, ruling (c))

`finSh` gives `τ` and S2's block point `r_blk` 18 coordinates for every kind, P30's and N30's
padded with `0` in coordinates 16–17 (`FRVIRFinals.padB`). On such operands `eqPt`, `shiftEq` and
`shiftTarget` are their `m − 14`-coordinate forms (`eqPoint_pad`, `shiftEqS_pad`,
`shiftTargetS_pad`; `FRShift.eq_pad_zero`, `shiftPair_pad`, `shiftTarget_pad`). -/

theorem foldl_prod_range (g : ℕ → F) (n : ℕ) :
    (List.range n).foldl (fun acc v => acc * g v) 1 = ∏ v ∈ range n, g v := by
  induction n with
  | zero => rfl
  | succ n ih => rw [List.range_succ, List.foldl_append, ih, Finset.prod_range_succ]; rfl

/-- `eqPoint` is `eq` at the arrays' points (over `a`'s length). -/
theorem eqPoint_eq (a b : Array F) : eqPoint a b = eq (ptA a.size a) (ptA a.size b) := by
  simp only [eqPoint]
  rw [foldl_prod_range, eq, ← Fin.prod_univ_eq_prod_range (fun v => a.getD v 0 * b.getD v 0 +
    (1 - a.getD v 0) * (1 - b.getD v 0))]
  rfl

theorem ptA_toArray (n : ℕ) (xs : List F) : ptA n xs.toArray = ptOf n xs := by
  funext l; simp [ptA, ptOf, Array.getD_eq_getD_getElem?, List.getD_eq_getElem?_getD]

/-- `eqPoint` on points of one length is `shiftPair`'s first component. -/
theorem eqPoint_shiftPair (xs ys : List F) (h : xs.length = ys.length) :
    eqPoint xs.toArray ys.toArray = (shiftPair xs ys).1 := by
  rw [shiftPair_eq xs.length xs ys rfl h.symm, eqPoint_eq, List.size_toArray, ptA_toArray,
    ptA_toArray]

/-- **`eqPt` on zero-padded points** (`eq_pad_zero`). -/
theorem eqPoint_pad (k : ℕ) (xs ys : List F) (h : xs.length = ys.length) :
    eqPoint (xs ++ List.replicate k 0).toArray (ys ++ List.replicate k 0).toArray =
      eqPoint xs.toArray ys.toArray := by
  rw [eqPoint_shiftPair _ _ (by simp [h]), eqPoint_shiftPair _ _ h, shiftPair_pad k xs ys h]

/-- **`shiftEq`'s specification on zero-padded points** (`shiftPair_pad`). -/
theorem shiftEqS_pad (k : ℕ) (xs ys : List F) (h : xs.length = ys.length) :
    shiftEqS (xs ++ List.replicate k 0).toArray (ys ++ List.replicate k 0).toArray =
      shiftEqS xs.toArray ys.toArray := by
  rw [← shiftEq_meets _ _ (by simp [h]), ← shiftEq_meets _ _ (by simp [h]), shiftEqI, shiftEqI,
    List.toList_toArray, List.toList_toArray, shiftPair_pad k xs ys h]

/-- The last block's padded point: `1^n ‖ 0^k` (`finSh`'s `bnd[4 … 21]`). -/
def lastPad (n k : ℕ) : List F := List.replicate n 1 ++ List.replicate k 0

theorem getD_pad (xs : List F) (k i : ℕ) :
    (xs ++ List.replicate k 0).getD i 0 = xs.getD i 0 := by
  rcases lt_or_ge i xs.length with hi | hi
  · simp [List.getD_eq_getElem?_getD, List.getElem?_append_left hi]
  · simp only [List.getD_eq_getElem?_getD, List.getElem?_append_right hi, List.getElem?_replicate,
      List.getElem?_eq_none hi]
    split_ifs <;> rfl

/-- **`shiftTarget`'s specification at a zero-padded `τ`** and the kind's padded last block
`1^n ‖ 0^k` (`n + k = 18`): `FRShift.shiftTarget` on the `n` block coordinates. -/
theorem shiftTargetS_pad (κs : F) (θ : Array F) {n k : ℕ} (hnk : n + k = 18) (τ b4 : List F)
    (hτ : τ.length = n) (hb : b4.length = 4) :
    shiftTargetS κs (τ ++ List.replicate k 0).toArray θ (b4 ++ lastPad n k).toArray =
      shiftTarget (ptA 10 θ) (ptOf n τ) κs (digTbl (b4.getD 0 0) (b4.getD 1 0))
        (digTbl (b4.getD 2 0) (b4.getD 3 0)) := by
  have hb' : ∀ j, j < 4 → (b4 ++ lastPad n k).toArray.getD j 0 = b4.getD j 0 := fun j hj => by
    simp [Array.getD_eq_getD_getElem?, List.getD_eq_getElem?_getD,
      List.getElem?_append_left (show j < b4.length by omega)]
  have hl : ∀ l, (b4 ++ lastPad n k).toArray.getD (4 + l) 0 = if l < n then 1 else 0 := fun l => by
    simp only [Array.getD_eq_getD_getElem?, List.getElem?_toArray, lastPad,
      List.getElem?_append_right (show b4.length ≤ 4 + l by omega), hb, Nat.add_sub_cancel_left]
    rcases lt_or_ge l n with h | h
    · simp [List.getElem?_append_left (show l < (List.replicate n (1 : F)).length by simpa), h]
    · simp only [List.getElem?_append_right (show (List.replicate n (1 : F)).length ≤ l by simpa),
        List.getElem?_replicate, List.length_replicate, show ¬ l < n by omega, ite_false]
      split_ifs <;> rfl
  unfold shiftTargetS shiftTargetAt shiftTarget
  rw [hb' 0 (by omega), hb' 1 (by omega), hb' 2 (by omega), hb' 3 (by omega)]
  congr 2
  rw [eq_cube, eq]
  simp only [ptA, lastOf, ptOf]
  have e18 := Fin.prod_univ_eq_prod_range (fun l : ℕ => (τ ++ List.replicate k (0 : F)).toArray.getD l 0 *
      (b4 ++ lastPad n k).toArray.getD (4 + l) 0 + (1 - (τ ++ List.replicate k (0 : F)).toArray.getD l 0) *
      (1 - (b4 ++ lastPad n k).toArray.getD (4 + l) 0)) 18
  have en := Fin.prod_univ_eq_prod_range
    (fun l : ℕ => if (lastBlk n).val.testBit l then τ.getD l 0 else 1 - τ.getD l (0 : F)) n
  rw [e18, en]
  · rw [← hnk, Finset.prod_range_add]
    have h2 : ∀ x ∈ range k, (τ ++ List.replicate k 0).toArray.getD (n + x) 0 *
        (b4 ++ lastPad n k).toArray.getD (4 + (n + x)) 0 +
        (1 - (τ ++ List.replicate k 0).toArray.getD (n + x) 0) *
        (1 - (b4 ++ lastPad n k).toArray.getD (4 + (n + x)) 0) = 1 := fun x _ => by
      rw [hl, if_neg (by omega)]
      simp [Array.getD_eq_getD_getElem?, List.getElem?_append_right (show τ.length ≤ n + x by omega),
        hτ]
    rw [Finset.prod_eq_one h2, mul_one]
    refine Finset.prod_congr rfl fun l hl' => ?_
    have hln : l < n := Finset.mem_range.1 hl'
    rw [hl, if_pos hln, show (lastBlk n).val = 2 ^ n - 1 from rfl, Nat.testBit_two_pow_sub_one,
      decide_eq_true hln, if_pos rfl]
    simp [Array.getD_eq_getD_getElem?, List.getD_eq_getElem?_getD,
      List.getElem?_append_left (show l < τ.length by omega)]

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
