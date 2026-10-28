-- New for `flock-recursive` (BLUEPRINT §7, stage S-0; §3, B-2, B-7, Appendix A.8).
import FRFormat
import RecursionFast.Library.Fast

/-!
# The verifier IR: values, ops, `OpImpl`/`OpSpec`, `runIR`, `semIR`, `gen`

BLUEPRINT §3, B-2, B-7, A.8.

* **Registers** are SSA: every op appends its results (`Op.outs` values) to the register file;
  operands are absolute register numbers. A value is a `Val` (A.8's register kinds).
* **Ops** (A.8, plus the structural ops it leaves implicit: `input`, `const`, `packF`/`packK`,
  `getF`/`getK`, `piElemK`, `piDigestAt`, `eqTableK`, `dotKF`, `shrN`, `keep`, `kindSel`; see the
  stage RESULT). Kind-dependent data are tables `Kind → α` inside the op (**`KC`**): a kind's
  constants, the activity of an assertion or a dummy query. `gen` emits **one op list** for all
  kinds; a `VProg` pairs it with a **mode**: `fixed κ` (`gen κ`) or `mux` (`gen Mux`, the kind read
  from `hdr`'s kind byte, which the program asserts one-hot). So the three kinds and the mux share
  the op list literally, and `semIR (gen Mux) = semIR (gen κ)` on a proof of kind byte `κ`
  (`FRVIRSpec.semIR_mux`).
* Assertions do not stop the program: they clear the `ok` flag, so every run asks **every** ask op
  (the item sequence is a constant, §1.2). The result is the flag.
* `OpImpl` holds the op implementations other tracks supply (`lagrangeS`, `tensorW`, `rsWeight`,
  `phiRS`, `walkAB`, `kindInd`, `evalM`, `evalL`, `targetS`, `eqZ`, `shiftTarget`,
  `slotW`, `kindFoldWeight`, …; revision 3.9); `OpSpec` the same signatures as the
  mathematical reference; `OpImpl.Meets impl spec` is what `FRVIREval` proves.
* `runIR impl P inp : OProg Bool` (the verifier's program) and `semIR impl P inp tr : Option Bool`
  (the same ops against a trace, consumed in order: the semantics `FRVIRSpec` reasons about);
  `FRVIRSpec.runSeq_runIR : (runIR …).runSeq tr = semIR … tr`.
* **`gen`**: the phase table (`FRTranscriptDefs.phases`) drives one generator per `Shape`; the
  phase-final algebraic checks are a parameter `fin : Finals` (S-C / L-pcs / L-cert pin them; see
  the RESULT's open questions). Initial sumcheck claims: `initClaim`.
-/

namespace FR
open RecursionFast

/-! ## Values -/

/-- A register value (A.8's register kinds). -/
inductive Val where
  | f (x : F) | k (x : K) | d (x : Digest) | b (x : ByteArray) | n (x : ℕ) | bit (x : Bool)
  | af (x : Array F) | ak (x : Array K) | ad (x : Array Digest)

instance : Inhabited Val := ⟨.n 0⟩

/-- The zero digest. -/
def zeroD : Digest := Vector.replicate 32 0

namespace Val
def toF : Val → F | f x => x | _ => 0
def toK : Val → K | k x => x | _ => 0
def toD : Val → Digest | d x => x | _ => zeroD
def toB : Val → ByteArray | b x => x | _ => ByteArray.empty
def toN : Val → ℕ | n x => x | _ => 0
def toBit : Val → Bool | bit x => x | _ => false
def toAF : Val → Array F | af x => x | _ => #[]
def toAK : Val → Array K | ak x => x | _ => #[]

/-- The bytes of a value (`mkAbsorb`). -/
def bytes : Val → ByteArray
  | f x => bytesOf x.toBytes.toList
  | k x => bytesOf x.toBytes.toList
  | d x => bytesOf x.toList
  | b x => x
  | _ => ByteArray.empty

/-- Zero test (`assertZero`): every byte or element zero. -/
def isZero : Val → Bool
  | f x => decide (x = 0)
  | k x => decide (x = 0)
  | d x => decide (x = zeroD)
  | b x => x.data.all (· == 0)
  | n x => decide (x = 0)
  | bit x => !x
  | af x => x.all fun y => decide (y = 0)
  | ak x => x.all fun y => decide (y = 0)
  | ad x => x.all fun y => decide (y = zeroD)

/-- Bit test (`assertBit`, revision 3.16, R-V-m1): a `bit`, or the F value `0` or `1`. -/
def isBit : Val → Bool
  | bit _ => true
  | f x => decide (x = 0) || decide (x = 1)
  | _ => false

/-- Equality test (`assertEq`): same kind and equal. -/
def eqv : Val → Val → Bool
  | f x, f y => decide (x = y)
  | k x, k y => decide (x = y)
  | d x, d y => decide (x = y)
  | b x, b y => decide (x.data = y.data)
  | n x, n y => decide (x = y)
  | bit x, bit y => decide (x = y)
  | _, _ => false
end Val

/-- Read register `i` (the default value if absent). -/
def rd (regs : Array Val) (i : ℕ) : Val := regs[i]?.getD default

/-! ## Ops (A.8) -/

/-- Register numbers. -/
abbrev Reg := ℕ

/-- A kind-dependent datum. -/
abbrev KC (α : Type) := Kind → α

/-- Active for every kind. -/
def allK : KC Bool := fun _ => true

/-- The IR's ops (A.8 and the structural ops; `f` is an A.3 field, `o` a byte offset in it). -/
inductive Op where
  /-- D: the input `vk` (`w = 0`) or `c` (`w = 1`). -/
  | input (w : ℕ)
  /-- A kind-dependent constant. -/
  | const (c : KC Val)
  /-- B: bytes `[o, o + len)` of field `f`. -/
  | piField (f o len : ℕ)
  /-- F: the 16 bytes at `o` of field `f`. -/
  | piElem (f o : ℕ)
  /-- K: the 32 bytes at `o` of field `f`. -/
  | piElemK (f o : ℕ)
  /-- D: the 32 bytes at `o` of field `f`. -/
  | piDigest (f o : ℕ)
  /-- D: the 32 bytes at `o + 32 k` of field `f`, `k` a register. -/
  | piDigestAt (f o : ℕ) (k : Reg)
  /-- B: the concatenation of the values' bytes, zero-padded to a multiple of 16. -/
  | mkAbsorb (xs : List Reg)
  /-- The seed query `"FRSEED0" ‖ vk ‖ c ‖ hdr`; binds the answer. -/
  | askSeed (hdr : Reg)
  /-- The absorb query of a `len`-byte message. -/
  | askAbsorb (st msg : Reg) (len : ℕ)
  | askSqueeze (st : Reg)
  /-- The Merkle-node query of level `i`, depth `h`; `0^64` for the kinds where `act` fails. -/
  | askNode (i h : ℕ) (l r : Reg) (act : KC Bool)
  | askCol (i : ℕ) (col : Reg)
  /-- F: coordinate `c` of an answer. -/
  | chF (a : Reg) (c : ℕ)
  | chK (a : Reg)
  /-- N: index `i` of `b` bits of answer `a` (all three kind-dependent). -/
  | idx (a : KC Reg) (b i : KC ℕ)
  | bitOf (n : Reg) (h : ℕ)
  /-- N: `n >>> s`. -/
  | shrN (n : Reg) (s : KC ℕ)
  | mulF (a b : Reg) | addF (a b : Reg) | mulK (a b : Reg) | addK (a b : Reg)
  /-- K × F → K. -/
  | mulKF (a b : Reg)
  | invF (a : Reg)
  | packF (xs : List Reg) | packK (xs : List Reg)
  /-- AF: a kind-dependent list of F registers. -/
  | packFK (xs : KC (List Reg))
  | getF (a : Reg) (i : ℕ) | getK (a : Reg) (i : ℕ)
  /-- `eq(r, ·)` over F, `AF v → AF (2^v)`; `eqTableK` over K. -/
  | eqTable (r : Reg) | eqTableK (r : Reg)
  /-- K: `Σ_r w[r] · col_r` (a column's F elements folded by the K weights). -/
  | dotKF (w col : Reg)
  /-- `(P^{ab}*(λ), P^z*(λ))` from Z2's 127 values and `pe = targetS r` (two F registers; rev 3.8). -/
  | lagrangeS (vals lam pe : Reg)
  /-- AF 64: `P^e` on `S` at the zerocheck point (rev 3.8; S-C). -/
  | targetS (r : Reg)
  /-- AF 128: the Z claim's inner weight over an element's 128 bit positions,
  `L_{lo(i)}(λ) · eq(ρ₁, bit 6 of i)` (A.8, revision 3.9: bit 6's coordinate is `ρ₁`). -/
  | eqZ (lam rho1 : Reg)
  | tensorW (j r : Reg)
  /-- K: `Ŵ(ρ) = Σ_j κ^j Ŵ_j(ρ)` at the claims' outer points `pts` (AK registers; a leaf passes 3),
  `κ` (F), `β` (F; `1` where `act` fails) and the final point `ρ` (AK); `Ŵ_j(ρ) = Σ_{k<128}
  c_k(r″) eq(r_j^{2^k}, ρ)` (`weightEval`) except claim 2 (Lc, index 1), whose block factor is
  `B_β^(2^k)` over the node layout's kinds (revision 3.16, R-V-M1: `Σ_k c_k eq(p_hi^(2^k), ρ_hi)
  Σ_i β^(i 2^k) Σ_{t ∈ I_i} eq(p_blk^(2^k), t) eq(ρ_blk, t)`). `gen` gates `β` by `isNode`: a
  leaf's `β = 1` makes the factor `1` (`KW.kwS_one`). Revision 3.9, replaces `mbp`; revision 3.16
  adds `β`. -/
  | rsWeight (r : Reg) (pts : KC (List Reg)) (kappa beta : Reg) (act : KC Bool) (rho : Reg)
  /-- F: `Φ_{r″}(a)`, the staged Frobenius map (`FRRingSwitch.Phi`; revision 3.9). -/
  | phiRS (r a : Reg)
  /-- F × F: `(Â₀, B̂₀)` by one circuit walk at the (masked) row weights and the column weights
  (revision 3.12, the fused walk; S-E4). -/
  | walkAB (rowW colW : Reg)
  /-- AF: the indicator MLEs of the kinds at a point. -/
  | kindInd (r : Reg)
  /-- AF: `rowW′[k] = rowW[k] · Σ_{kind : k not pinned} v[kind]`, `v` the prover's per-kind
  claims (A.8, revision 3.4). -/
  | maskRows (kindW rowW : Reg)
  /-- Three F registers. -/
  | evalM (tau sigma : Reg) | evalL (tau sigma : Reg)
  /-- F: the shift sumcheck's boundary term with the boundary values `bnd` (AF 22: a leaf's `s`, `h`
  as two elements each, a node's zeros (revisions 3.9, 3.14); then the kind's last block
  `1^(m−14) ‖ 0^(32−m)`, revision 3.15). `tau` has 18 coordinates for every kind (P30/N30
  zero-padded, revision 3.15). -/
  | shiftTarget (tau theta bnd ks : Reg)
  /-- F: the slot weight of slot map `s` at `θ`, `r`. -/
  | slotW (s : ℕ) (theta r : Reg)
  /-- F: `Ŵ_β(ρ)`. **Withdrawn** (revision 3.16): the kind factor is `rsWeight`'s claim-2 weight;
  no `gen` emits this op, and `implC` gives `0`. -/
  | kindFoldWeight (r beta rho : Reg)
  /-- F: `eq(a, b) = Π_v (a_v b_v + (1 − a_v)(1 − b_v))` of two F points. In the circuit an
  import (revision 3.6: no rows; its value is a hypothesis discharged in `final`). -/
  | eqPt (a b : Reg)
  /-- AF: the lincheck's row weights (`OpImpl.rowW`; an import, revision 3.6). -/
  | rowW (lam rhi : Reg)
  /-- F: `shift(τ, r)` (`OpImpl.shiftEq`; an import, revision 3.6). -/
  | shiftEq (tau r : Reg)
  /-- AF 8: the 8 link families' weights at the Sh point (`OpImpl.linkWAll`, revision 3.14; replaces
  `linkW τ fam r_blk`): `tt = τ ‖ θ` (S1's 16 block, then 10 slot coordinates), `rr = r_blk ‖ r_pos`
  (S2's 16, then 10). A leaf's result is `0^8`. -/
  | linkWAll (tt rr : Reg)
  /-- F × F × F: the node's chain-masked shift weights (`OpImpl.shiftMask`, revision 3.14, the
  `WM` ruling): `Σ_{y ∈ Lk} eq(τ,y) eq(r,y)`, `Σ_{y ∈ Lk} eq(τ,y) eq(r,y+1)` and
  `eq(r,0) + eq(r,chainBase_2)`, `Lk` the blocks with an in-chain successor. -/
  | shiftMask (tau r : Reg)
  /-- Two F registers. -/
  | splitDigest (d : Reg)
  /-- D: `y` if the bit is set, else `x`. -/
  | selectHalf (b x y : Reg)
  /-- `new` for the kinds where `act` holds, else `old`. -/
  | keep (act : KC Bool) (new old : Reg)
  /-- D: the statement of `stmt` (`leafStmt h n` for the leaf kinds, `nodeStmt c₁ c₂`; in the
  circuit three blocks A, B1, B2 and `cᵢ = (s_L + s_P)·out_A + s_N·out_B2`, R4-M1). -/
  | hashStmt (stmt : Reg)
  /-- Three bits `(s_L, s_P, s_N)`: the kind byte of `hdr`. -/
  | kindSel
  | assertEq (a b : Reg) (act : KC Bool)
  | assertBit (a : Reg) (act : KC Bool)
  | assertZero (a : Reg) (act : KC Bool)
  | assertOneHot (s₁ s₂ s₃ : Reg)
  | accept

/-! ## Implementations supplied by other tracks -/

/-- The op implementations `FRVerifier` takes from `FRVIREval` (and the modules it uses). -/
structure OpImpl where
  /-- The degree-≤127 interpolant through `S ∪ Λ` at `λ` (FRSkip). -/
  lagrangeS : Array F → F → Array F → F × F
  /-- `P^e` on `S` (64 values) at the zerocheck point, for the proof's kind (FRPubTarget/S-C). -/
  targetS : Kind → Array F → Array F
  /-- The Z claim's inner weight `L_{lo(i)}(λ) · eq(ρ₁, bit 6 of i)`, 128 values (FRSkip). -/
  eqZ : F → F → Array F
  /-- `Π_v (1 − r_v + r_v Ŵ_v(D[j]))` (FRRS). -/
  tensorW : ℕ → Array K → K
  /-- `Ŵ(ρ) = Σ_j κ^j Ŵ_j(ρ)` (`r″`, the claims' outer points, `κ`, `β`, the final point;
  `weightEval`, L-R4; claim 2 with the kind factor `B_β`, revision 3.16; FRRingSwitch,
  FRKindWeight). -/
  rsWeight : Array F → List (Array K) → F → F → Array K → K
  /-- `Φ_{r″}(a)` (FRRingSwitch). -/
  phiRS : Array F → F → F
  /-- `Â₀`, `B̂₀` by the circuit walk at the (masked) row weights and the column weights
  (`walkE_eq_sum`; FRBlake2sWalk). -/
  walkAB : Array F → Array F → F × F
  /-- The indicator MLEs `Ĩnd_kind(r′)`, one per kind of `blockKinds` (FRNodeLayout). -/
  kindInd : Array F → Array F
  /-- The node's matrix MLEs (FRVIREval). -/
  evalM : Array F → Array F → F × F × F
  evalL : Array F → Array F → F × F × F
  /-- The shift sumcheck's boundary term: `κ_s`, `τ` (18 coordinates), `θ`, the boundary values
  and the kind's last block (P1-D5, A.9 `finSh` (i); FRShift; revision 3.15). -/
  shiftTarget : F → Array F → Array F → Array F → F
  /-- The collapse's slot weight of slot map `s` for the proof's kind, summed directly (S-C-m1;
  FRShift). -/
  slotW : Kind → ℕ → Array F → Array F → F
  /-- `Ŵ_β` at the ring-switching point (S-C-M1; FRRingSwitch). -/
  kindFoldWeight : Array F → F → Array K → F
  /-- The 8 link families' weights for the proof's kind at `τ ‖ θ`, `r_blk ‖ r_pos` (revision 3.14;
  FRNodeTarget's `linkWAllS`). -/
  linkWAll : Kind → Array F → Array F → Array F
  /-- The node's chain-masked shift weights at `τ`, `r_blk` (revision 3.14; FRNodeTarget's
  `shiftMaskS`). -/
  shiftMask : Array F → Array F → F × F × F
  /-- The lincheck's row weights `rowW` (`2^14`): Lagrange at `λ` on the skip coordinate ⊗
  `eq(r′_hi, ·)` on the 8 high position bits (A.9 `finLc`; FRSkip/FRSpartan). -/
  rowW : F → Array F → Array F
  /-- `shift(τ, r)`, the shift's MLE at two block points (FRShift). -/
  shiftEq : Array F → Array F → F

/-- **The specification record**: the same signatures, read as the mathematical definitions.
Owners of the concrete `OpSpec` and its lemmas (S-0-m2): S-C — `lagrangeS`, `tensorW`, `rsWeight`,
`phiRS`,
`shiftTarget`, `slotW`, `kindFoldWeight`, `linkWAll`, `shiftMask`, `rowW`, `shiftEq`; S-E1/S-E2 — `walkAB`,
`evalM/L`, `kindInd`; `FRPubTarget` — `targetS`; FRSkip — `eqZ`. -/
abbrev OpSpec := OpImpl

/-- **`impl ⊨ spec`, per op, on well-formed operands only** (S-0-m2): each implemented op equals its
specification where the verifier calls it (the operand lengths `gen` produces); malformed lengths
are unconstrained. `FRVIREval` proves it. -/
def OpImpl.Meets (impl : OpImpl) (spec : OpSpec) : Prop :=
  (∀ v l pe, v.size = 127 → impl.lagrangeS v l pe = spec.lagrangeS v l pe) ∧
  (∀ κ r, impl.targetS κ r = spec.targetS κ r) ∧ (∀ a b, impl.eqZ a b = spec.eqZ a b) ∧
  (∀ j r, impl.tensorW j r = spec.tensorW j r) ∧
  (∀ r ps k β p, r.size = 7 → 23 ≤ p.size →
    impl.rsWeight r ps k β p = spec.rsWeight r ps k β p) ∧
  (∀ r a, r.size = 7 → impl.phiRS r a = spec.phiRS r a) ∧
  (∀ rw cw, rw.size = 2 ^ 14 → cw.size = 2 ^ 14 → impl.walkAB rw cw = spec.walkAB rw cw) ∧
  (∀ a b, impl.evalM a b = spec.evalM a b) ∧ (∀ a b, impl.evalL a b = spec.evalL a b) ∧
  (∀ a, impl.kindInd a = spec.kindInd a) ∧
  (∀ k a b c, c.size = 22 → impl.shiftTarget k a b c = spec.shiftTarget k a b c) ∧
  (∀ κ s a b, impl.slotW κ s a b = spec.slotW κ s a b) ∧
  (∀ a b c, impl.kindFoldWeight a b c = spec.kindFoldWeight a b c) ∧
  (∀ κ a c, impl.linkWAll κ a c = spec.linkWAll κ a c) ∧
  (∀ a b, impl.shiftMask a b = spec.shiftMask a b) ∧ (∀ l a, impl.rowW l a = spec.rowW l a) ∧
  (∀ a b, a.size = b.size → impl.shiftEq a b = spec.shiftEq a b)

/-! ## One op -/

/-- The input of a run: the public key, the statement, the proof. -/
structure Input where
  vk : Digest
  c : Digest
  π : Proof

/-- Field offsets, computed once. -/
def fieldOffA : Array ℕ := ((List.range (nFields + 1)).map fieldOff).toArray

/-- The absolute offset of byte `o` of field `f`. -/
def absOff (f o : ℕ) : ℕ := fieldOffA.getD f 0 + o

/-- `eq(r, ·)`: bit `v` of the index is coordinate `v`. -/
def eqTab {R : Type} [Mul R] [Add R] [Sub R] [One R] (r : Array R) : Array R :=
  r.foldl (fun t x => t.map (· * (1 - x)) ++ t.map (· * x)) #[1]

/-- `eq(a, b)` of two F points (missing coordinates read as `0`). -/
def eqPoint (a b : Array F) : F :=
  (List.range a.size).foldl (fun acc v =>
    let x := a.getD v 0; let y := b.getD v 0
    acc * (x * y + (1 - x) * (1 - y))) 1

/-- The F elements of a byte string, 16 bytes each. -/
def felems (b : ByteArray) : Array F :=
  (Array.range (b.size / 16)).map fun r => F.ofBytes (bytesAt b (16 * r) 16)

/-- `Σ_r w[r] · col_r`. -/
def dotKF (w : Array K) (col : ByteArray) : K :=
  ((felems col).zipWith (fun c x => K.smulF c x) w).foldl (· + ·) 0

/-! ### Fast twins (S-E8): what `evalOp` runs, each equal to its reference -/

/-- The F element at byte `o` of `b` (zero past the end), read in place: `F.ofBytes (bytesAt b o 16)`
without its three intermediate vectors (`fAt_eq`). -/
def fAt (b : ByteArray) (o : ℕ) : F :=
  ⟨⟨(byteAt b (o + 0)).toUInt64 + ((byteAt b (o + 1)).toUInt64 <<< 8) +
      ((byteAt b (o + 2)).toUInt64 <<< 16) + ((byteAt b (o + 3)).toUInt64 <<< 24) +
      ((byteAt b (o + 4)).toUInt64 <<< 32) + ((byteAt b (o + 5)).toUInt64 <<< 40) +
      ((byteAt b (o + 6)).toUInt64 <<< 48) + ((byteAt b (o + 7)).toUInt64 <<< 56)⟩,
    ⟨(byteAt b (o + 8)).toUInt64 + ((byteAt b (o + 9)).toUInt64 <<< 8) +
      ((byteAt b (o + 10)).toUInt64 <<< 16) + ((byteAt b (o + 11)).toUInt64 <<< 24) +
      ((byteAt b (o + 12)).toUInt64 <<< 32) + ((byteAt b (o + 13)).toUInt64 <<< 40) +
      ((byteAt b (o + 14)).toUInt64 <<< 48) + ((byteAt b (o + 15)).toUInt64 <<< 56)⟩⟩

theorem fAt_eq (b : ByteArray) (o : ℕ) : fAt b o = F.ofBytes (bytesAt b o 16) := by
  simp only [fAt, F.ofBytes, B64.ofBytes, bytesAt, Vector.getElem_ofFn]

/-- `dotKFF`'s loop: `k` more terms from row `r`. -/
def dotKFGo (w : Array K) (col : ByteArray) : ℕ → ℕ → K → K
  | 0, _, acc => acc
  | k + 1, r, acc => dotKFGo w col k (r + 1) (acc + K.smulF (fAt col (16 * r)) w[r]!)

/-- **`dotKF` as one loop** (S-E8): no `felems` array, no zipped array (`dotKFF_eq`). -/
def dotKFF (w : Array K) (col : ByteArray) : K := dotKFGo w col (min (col.size / 16) w.size) 0 0

theorem dotKFGo_eq (w : Array K) (col : ByteArray) (k r : ℕ) (acc : K) :
    dotKFGo w col k r acc =
      ((List.range' r k).map fun i => K.smulF (fAt col (16 * i)) w[i]!).foldl (· + ·) acc := by
  induction k generalizing r acc with
  | zero => rfl
  | succ k ih => simp only [dotKFGo, ih, List.range'_succ, List.map_cons, List.foldl_cons]

theorem dotKFF_eq (w : Array K) (col : ByteArray) : dotKFF w col = dotKF w col := by
  rw [dotKFF, dotKFGo_eq, dotKF, ← Array.foldl_toList, ← List.range_eq_range']
  refine congrArg (List.foldl (· + ·) 0) (List.ext_getElem (by simp [felems]) fun i h₁ _ => ?_)
  simp only [List.length_map, List.length_range] at h₁
  simp only [List.getElem_map, List.getElem_range, List.getElem_zipWith, Array.toList_zipWith,
    Array.toList_map, Array.toList_range, Array.getElem_toList, felems]
  rw [fAt_eq, getElem!_pos w i (lt_min_iff.1 h₁).2]

/-- Zero-pad to a multiple of 16. -/
def pad16 (b : ByteArray) : ByteArray := b ++ ⟨Array.replicate ((16 - b.size % 16) % 16) 0⟩

/-- **`nodeQ`'s fast twin** (S-E8): the 72-byte query from arrays, not from three lists appended
(`nodeQF_eq`). -/
def nodeQF (i : ℕ) (l r : Digest) : ByteArray :=
  ⟨#[0x46, 0x52, 0x4D, 0x4E, 0x4F, 0x44, i.toUInt8, 0] ++ l.toArray ++ r.toArray⟩

theorem nodeQF_eq (i : ℕ) (l r : Digest) : nodeQF i l r = nodeQ i l r := by
  simp [nodeQF, nodeQ, bytesOf, tagNode]; rfl

/-- **A digest read from `q` at `o`** (S-E8): one 32-byte slice, not 32 bounds-checked reads into a
`Vector.ofFn` (`digestAt_eq`). -/
def digestAt (q : ByteArray) (o : ℕ) : Digest :=
  if h : o + 32 ≤ q.size then ⟨(q.extract o (o + 32)).data, by simp; omega⟩ else bytesAt q o 32

theorem digestAt_eq (q : ByteArray) (o : ℕ) : digestAt q o = bytesAt q o 32 := by
  unfold digestAt
  split_ifs with h
  · ext t ht
    simp only [Vector.getElem_mk, ByteArray.data_extract, Array.getElem_extract, bytesAt,
      Vector.getElem_ofFn, byteAt, show o + t < q.size by omega, dite_true]
    rfl
  · rfl

section IdxF
open Finset

/-- Byte `k` of a digest as a number, `0` past the end. -/
def dByte (a : Digest) (k : ℕ) : ℕ := if h : k < 32 then a[k].toNat else 0

/-- The four bytes from `k`, little-endian. -/
def dWin (a : Digest) (k : ℕ) : ℕ :=
  dByte a k + dByte a (k + 1) * 256 + dByte a (k + 2) * 65536 + dByte a (k + 3) * 16777216

/-- **`idxOf`'s fast twin** (S-E8): for `b ≤ 24`, bits `[i b, i b + b)` of `natLE a` lie in the four
bytes from `⌊i b / 8⌋`, so only those are read, with shifts in place of `2 ^ _` (which runs as a
loop in compiled code). Equal to `idxOf` for every `b`, `a`, `i` (`idxOfF_eq`). -/
def idxOfF (b : ℕ) (a : Digest) (i : ℕ) : ℕ :=
  if b ≤ 24 then dWin a (i * b / 8) >>> (i * b % 8) % (1 <<< b) else idxOf b a i

theorem dByte_lt (a : Digest) (k : ℕ) : dByte a k < 256 := by
  unfold dByte; split
  · exact UInt8.toNat_lt _
  · norm_num

theorem natLE_sum (a : Digest) (N : ℕ) (hN : 32 ≤ N) :
    natLE a = ∑ t ∈ range N, dByte a t * 256 ^ t := by
  obtain ⟨M, rfl⟩ := Nat.exists_eq_add_of_le hN
  rw [sum_range_add, show ∑ t ∈ range M, dByte a (32 + t) * 256 ^ (32 + t) = 0 from
    sum_eq_zero fun t _ => by simp [dByte], add_zero, natLE,
    ← Fin.sum_univ_eq_sum_range (fun t => dByte a t * 256 ^ t)]
  exact sum_congr rfl fun t _ => by simp [dByte, t.2]

theorem sum_lt_pow (a : Digest) (k : ℕ) : ∑ t ∈ range k, dByte a t * 256 ^ t < 256 ^ k := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [sum_range_succ, pow_succ]
    have := dByte_lt a k
    nlinarith [pow_pos (show (0:ℕ) < 256 by norm_num) k]

theorem natLE_split (a : Digest) (k : ℕ) :
    natLE a = ∑ t ∈ range k, dByte a t * 256 ^ t +
      256 ^ k * (dWin a k + 2 ^ 32 * ∑ t ∈ range 32, dByte a (k + (4 + t)) * 256 ^ t) := by
  rw [natLE_sum a (k + (4 + 32)) (by omega), sum_range_add, sum_range_add]
  have h4 : ∑ x ∈ range 4, dByte a (k + x) * 256 ^ (k + x) = 256 ^ k * dWin a k := by
    simp only [sum_range_succ, sum_range_zero, dWin, add_zero, pow_add]; ring_nf
  have h32 : ∑ x ∈ range 32, dByte a (k + (4 + x)) * 256 ^ (k + (4 + x)) =
      256 ^ k * (2 ^ 32 * ∑ t ∈ range 32, dByte a (k + (4 + t)) * 256 ^ t) := by
    rw [mul_sum, mul_sum]
    refine sum_congr rfl fun t _ => ?_
    rw [pow_add, pow_add, show (256 : ℕ) ^ 4 = 2 ^ 32 by norm_num]; ring
  rw [h4, h32, mul_add]

theorem idxOfF_eq (b : ℕ) (a : Digest) (i : ℕ) : idxOfF b a i = idxOf b a i := by
  unfold idxOfF
  split_ifs with hb
  swap; · rfl
  set s := i * b
  set k := s / 8
  set r := s % 8
  have hr : r < 8 := Nat.mod_lt _ (by norm_num)
  have hs : 2 ^ s = 256 ^ k * 2 ^ r := by
    rw [← Nat.div_add_mod s 8, pow_add, pow_mul]; norm_num; rfl
  set H := ∑ t ∈ range 32, dByte a (k + (4 + t)) * 256 ^ t
  have hY : 2 ^ 32 * H = 2 ^ r * (2 ^ b * (2 ^ (32 - r - b) * H)) := by
    rw [← mul_assoc, ← mul_assoc, ← pow_add, ← pow_add]; congr 2; omega
  rw [idxOf, natLE_split a k, hs, ← Nat.div_div_eq_div_mul, Nat.add_mul_div_left _ _ (by positivity),
    Nat.div_eq_of_lt (sum_lt_pow a k), zero_add, hY, Nat.add_mul_div_left _ _ (by positivity),
    Nat.add_mul_mod_self_left, Nat.shiftRight_eq_div_pow, Nat.one_shiftLeft]
end IdxF

/-- The sum of the indicator weights of the kinds (in `blockKinds` order) that do not pin row `k`. -/
def maskOf (kindW : Array F) (k : ℕ) : F :=
  ((blockKinds.zipIdx.filter fun p => !isZeroRow p.1 k).map fun p => kindW.getD p.2 0).sum

/-- The last row any kind pins (`zeroRows`' largest bound; `isZeroRow_of_gt`). -/
def pinEnd : ℕ := 1152

/-- **The masked row weights** (A.8 `maskRows`): row `k`'s weight times `maskOf kindW k`, the sum of
the indicator weights of the kinds that do not pin `k` (`maskRows_eq`). Past `pinEnd` no kind pins a
row, so that sum is computed once (S-E8). -/
def maskRows (kindW rowW : Array F) : Array F :=
  let all := maskOf kindW (pinEnd + 1)
  rowW.mapIdx fun k w => w * if k ≤ pinEnd then maskOf kindW k else all

theorem isZeroRow_of_gt (bk : BlockKind) {k : ℕ} (h : pinEnd < k) : isZeroRow bk k = false := by
  cases bk <;> simp only [isZeroRow, zeroRows, List.any_cons, List.any_nil, pinEnd] at h ⊢ <;>
    simp only [Bool.or_false, Bool.or_eq_false_iff, Bool.and_eq_false_iff, decide_eq_false_iff_not] <;>
    omega

theorem maskOf_of_gt (kindW : Array F) {k : ℕ} (h : pinEnd < k) :
    maskOf kindW k = maskOf kindW (pinEnd + 1) := by
  have e : ∀ x, pinEnd < x → (blockKinds.zipIdx.filter fun p => !isZeroRow p.1 x) = blockKinds.zipIdx :=
    fun x hx => List.filter_eq_self.2 fun p _ => by simp [isZeroRow_of_gt p.1 hx]
  simp only [maskOf, e k h, e (pinEnd + 1) (by omega)]

/-- **`maskRows` row by row** (its reading as A.8 states it): row `k`'s weight times `maskOf kindW k`. -/
theorem maskRows_eq (kindW rowW : Array F) :
    maskRows kindW rowW = rowW.mapIdx fun k w => w * maskOf kindW k :=
  congrArg rowW.mapIdx (funext fun k => funext fun w => by
    by_cases h : k ≤ pinEnd
    · simp only [h, if_true]
    · simp only [h, if_false, maskOf_of_gt kindW (Nat.lt_of_not_le h)])

/-- The statement of `stmt` for kind `κ` (§4.2, revision 3.3: `stmt` is the padded message blocks,
`tagLeaf ‖ h ‖ enc64 n ‖ 0^23 ‖ 0^64` or `tagNode ‖ c₁ ‖ c₂ ‖ 0^63`). -/
def stmtDigest (κ : Kind) (s : ByteArray) : Digest :=
  match κ with
  | .N30 => nodeStmtF (bytesAt s 1 32) (bytesAt s 33 32)
  | _ => leafStmtF (bytesAt s 1 32)
      (((List.range 8).map fun i => (s.data.getD (33 + i) 0).toNat * 256 ^ i).sum)

/-- What an op does: append values (and clear the flag on a failed assertion), or ask a query. -/
inductive Res where
  | vals (vs : List Val) (ok : Bool)
  | ask (q : ByteArray)

/-- **One op** under kind `κ`. -/
def evalOp (impl : OpImpl) (κ : Kind) (inp : Input) (regs : Array Val) : Op → Res
  | .input w => .vals [.d (if w = 0 then inp.vk else inp.c)] true
  | .const c => .vals [c κ] true
  | .piField f o len => .vals [.b (inp.π.extract (absOff f o) (absOff f o + len))] true
  | .piElem f o => .vals [.f (F.ofBytes (bytesAt inp.π (absOff f o) 16))] true
  | .piElemK f o => .vals [.k (K.ofBytes (bytesAt inp.π (absOff f o) 32))] true
  | .piDigest f o => .vals [.d (digestAt inp.π (absOff f o))] true
  | .piDigestAt f o k => .vals [.d (digestAt inp.π (absOff f o + 32 * (rd regs k).toN))] true
  | .mkAbsorb xs => .vals [.b (pad16 (xs.foldl (fun acc x => acc ++ (rd regs x).bytes) .empty))] true
  | .askSeed h => .ask (seedQ inp.vk inp.c (rd regs h).toB)
  | .askAbsorb st m _ => .ask (absorbQ (rd regs st).toD (rd regs m).toB)
  | .askSqueeze st => .ask (squeezeQ (rd regs st).toD)
  | .askNode i _ l r act =>
    .ask (if act κ then nodeQF i (rd regs l).toD (rd regs r).toD else nodeQF i zeroD zeroD)
  | .askCol i col => .ask (colQ i (rd regs col).toB)
  | .chF a c => .vals [.f (chF (rd regs a).toD c)] true
  | .chK a => .vals [.k (chK (rd regs a).toD)] true
  | .idx a b i => .vals [.n (idxOfF (b κ) (rd regs (a κ)).toD (i κ))] true
  | .bitOf n h => .vals [.bit ((rd regs n).toN.testBit h)] true
  | .shrN n s => .vals [.n ((rd regs n).toN >>> s κ)] true
  | .mulF a b => .vals [.f ((rd regs a).toF * (rd regs b).toF)] true
  | .addF a b => .vals [.f ((rd regs a).toF + (rd regs b).toF)] true
  | .mulK a b => .vals [.k ((rd regs a).toK * (rd regs b).toK)] true
  | .addK a b => .vals [.k ((rd regs a).toK + (rd regs b).toK)] true
  | .mulKF a b => .vals [.k (K.smulF (rd regs b).toF (rd regs a).toK)] true
  | .invF a => .vals [.f (rd regs a).toF⁻¹] true
  | .packF xs => .vals [.af (xs.map fun x => (rd regs x).toF).toArray] true
  | .packK xs => .vals [.ak (xs.map fun x => (rd regs x).toK).toArray] true
  | .packFK xs => .vals [.af ((xs κ).map fun x => (rd regs x).toF).toArray] true
  | .getF a i => .vals [.f ((rd regs a).toAF.getD i 0)] true
  | .getK a i => .vals [.k ((rd regs a).toAK.getD i 0)] true
  | .eqTable r => .vals [.af (eqTab (rd regs r).toAF)] true
  | .eqTableK r => .vals [.ak (eqTab (rd regs r).toAK)] true
  | .dotKF w col => .vals [.k (dotKFF (rd regs w).toAK (rd regs col).toB)] true
  | .lagrangeS v l pe =>
    let x := impl.lagrangeS (rd regs v).toAF (rd regs l).toF (rd regs pe).toAF
    .vals [.f x.1, .f x.2] true
  | .targetS r => .vals [.af (impl.targetS κ (rd regs r).toAF)] true
  | .eqZ l r₁ => .vals [.af (impl.eqZ (rd regs l).toF (rd regs r₁).toF)] true
  | .tensorW j r => .vals [.k (impl.tensorW (rd regs j).toN (rd regs r).toAK)] true
  | .rsWeight r ps κ' β act ρ =>
    .vals [.k (impl.rsWeight (rd regs r).toAF ((ps κ).map fun p => (rd regs p).toAK) (rd regs κ').toF
      (if act κ then (rd regs β).toF else 1) (rd regs ρ).toAK)] true
  | .phiRS r a => .vals [.f (impl.phiRS (rd regs r).toAF (rd regs a).toF)] true
  | .walkAB r c =>
    let x := impl.walkAB (rd regs r).toAF (rd regs c).toAF
    .vals [.f x.1, .f x.2] true
  | .kindInd r => .vals [.af (impl.kindInd (rd regs r).toAF)] true
  | .maskRows kw rw => .vals [.af (maskRows (rd regs kw).toAF (rd regs rw).toAF)] true
  | .evalM t s =>
    let x := impl.evalM (rd regs t).toAF (rd regs s).toAF
    .vals [.f x.1, .f x.2.1, .f x.2.2] true
  | .evalL t s =>
    let x := impl.evalL (rd regs t).toAF (rd regs s).toAF
    .vals [.f x.1, .f x.2.1, .f x.2.2] true
  | .shiftTarget t h bd ks =>
    .vals [.f (impl.shiftTarget (rd regs ks).toF (rd regs t).toAF (rd regs h).toAF (rd regs bd).toAF)]
      true
  | .slotW sm t r => .vals [.f (impl.slotW κ sm (rd regs t).toAF (rd regs r).toAF)] true
  | .eqPt a b => .vals [.f (eqPoint (rd regs a).toAF (rd regs b).toAF)] true
  | .rowW l h => .vals [.af (impl.rowW (rd regs l).toF (rd regs h).toAF)] true
  | .shiftEq t r => .vals [.f (impl.shiftEq (rd regs t).toAF (rd regs r).toAF)] true
  | .linkWAll t p => .vals [.af (impl.linkWAll κ (rd regs t).toAF (rd regs p).toAF)] true
  | .shiftMask t r =>
    let x := impl.shiftMask (rd regs t).toAF (rd regs r).toAF
    .vals [.f x.1, .f x.2.1, .f x.2.2] true
  | .kindFoldWeight r b ρ =>
    .vals [.f (impl.kindFoldWeight (rd regs r).toAF (rd regs b).toF (rd regs ρ).toAK)] true
  | .splitDigest d =>
    let x := (rd regs d).toD
    .vals [.f (F.ofBytes (Vector.ofFn fun i : Fin 16 => x[i.1])),
      .f (F.ofBytes (Vector.ofFn fun i : Fin 16 => x[16 + i.1]))] true
  | .selectHalf b x y => .vals [if (rd regs b).toBit then rd regs y else rd regs x] true
  | .keep act n o => .vals [if act κ then rd regs n else rd regs o] true
  | .hashStmt s => .vals [.d (stmtDigest κ (rd regs s).toB)] true
  | .kindSel =>
    let b := byteAt inp.π 0
    .vals [.bit (b == Kind.L32.byte), .bit (b == Kind.P30.byte), .bit (b == Kind.N30.byte)] true
  | .assertEq a b act => .vals [] (!act κ || (rd regs a).eqv (rd regs b))
  | .assertBit a act => .vals [] (!act κ || (rd regs a).isBit)
  | .assertZero a act => .vals [] (!act κ || (rd regs a).isZero)
  | .assertOneHot a b c =>
    .vals [] ([(rd regs a).toBit, (rd regs b).toBit, (rd regs c).toBit].count true == 1)
  | .accept => .vals [] true

/-! ## Programs, `runIR`, `semIR` -/

/-- How a program learns its kind: fixed (`gen κ`), or from `hdr`'s kind byte (`gen Mux`). -/
inductive Mode where
  | fixed (κ : Kind)
  | mux

/-- **A verifier program** (A.8): a mode and a straight-line op list. -/
structure VProg where
  mode : Mode
  ops : List Op

/-- The kind a program runs as on an input. -/
def VProg.kindOn (P : VProg) (inp : Input) : Kind :=
  match P.mode with
  | .fixed κ => κ
  | .mux => ((byteAt? inp.π 0).bind Kind.ofByte?).getD .L32

/-- The interpreter's state: the registers and the flag. -/
structure St where
  regs : Array Val
  ok : Bool

/-- The initial state. -/
def St.init : St := ⟨#[], true⟩

/-- Run ops against the oracle; return the flag. -/
def runOps (impl : OpImpl) (κ : Kind) (inp : Input) : List Op → St → OProg Bool
  | [], s => .ret s.ok
  | op :: ops, s =>
    match evalOp impl κ inp s.regs op with
    | .vals vs ok => runOps impl κ inp ops ⟨s.regs ++ vs.toArray, s.ok && ok⟩
    | .ask q => .query q fun a => runOps impl κ inp ops ⟨s.regs.push (.d a), s.ok⟩

/-- **`runIR impl P inp`**: the program as a query program (`V`'s SNARK branch). -/
def runIR (impl : OpImpl) (P : VProg) (inp : Input) : OProg Bool :=
  runOps impl (P.kindOn inp) inp P.ops St.init

/-- Run ops against a trace, consumed in order (each query must be the next entry's); the state
and the rest of the trace. -/
def exec (impl : OpImpl) (κ : Kind) (inp : Input) : List Op → St → Trace → Option (St × Trace)
  | [], s, tr => some (s, tr)
  | op :: ops, s, tr =>
    match evalOp impl κ inp s.regs op with
    | .vals vs ok => exec impl κ inp ops ⟨s.regs ++ vs.toArray, s.ok && ok⟩ tr
    | .ask q =>
      match tr with
      | [] => none
      | (q', a) :: tr' => if q' = q then exec impl κ inp ops ⟨s.regs.push (.d a), s.ok⟩ tr' else none

/-- **`semIR impl P inp tr`**: the program on the trace `tr`, used up exactly; the flag. -/
def semIR (impl : OpImpl) (P : VProg) (inp : Input) (tr : Trace) : Option Bool :=
  match exec impl (P.kindOn inp) inp P.ops St.init tr with
  | some (s, []) => some s.ok
  | _ => none

/-- The registers an op appends. -/
def Op.outs : Op → ℕ
  | .evalM .. | .evalL .. | .kindSel | .shiftMask .. => 3
  | .lagrangeS .. | .walkAB .. => 2
  | .splitDigest _ => 2
  | .assertEq .. | .assertBit .. | .assertZero .. | .assertOneHot .. | .accept => 0
  | _ => 1

/-- The registers an op list appends. -/
def opsOut (ops : List Op) : ℕ := (ops.map Op.outs).sum

/-- The item of an ask op (`none` for every other op). -/
def Op.item? : Op → Option Item
  | .askSeed _ => some .seed
  | .askAbsorb _ _ len => some (.absorb len)
  | .askSqueeze _ => some .squeeze
  | .askNode i h _ _ _ => some (.node i h)
  | .askCol i _ => some (.col i)
  | _ => none

/-! ## The generator -/

/-- How a sumcheck phase's first claim is obtained (provisional, S-C): from the last univariate
round's value (`Z3`), zero (the zerochecks `Lr2`, `E2`), or free (the first message's `c₁ + c₂`; the
claim is an output for the phase-final checks). -/
inductive Init where
  | uni | zero | free

/-- The initial claim per phase name (provisional, S-C). -/
def initClaim : String → Init
  | "Z3" => .uni
  | "Lr2" | "E2" => .zero
  | _ => .free

/-- The generator's context between phases. -/
structure GCtx where
  /-- The next free register. -/
  next : ℕ
  /-- The current Fiat–Shamir state. -/
  st : Reg
  /-- The last univariate round's value. -/
  uni : Reg
  /-- The last position answers and fold challenges. -/
  posAns : List Reg
  foldR : List Reg
  /-- The last coordinates array (a `.coords` phase's packed point; Z2's `targetS` reads Z1's). -/
  pt : Reg
  /-- Each phase's outputs, by phase number. -/
  outs : Array (List Reg)

/-- The phase-final checks as raw ops from the phases' outputs and the next free register (the typed
`Finals` of A.9 is `FRVIRFinals.Finals`, whose `ops` this is). They ask nothing
(`FRVIRSpec.items_gen` assumes it). -/
abbrev FinOps := Array (List Reg) → ℕ → List Op

/-- Seed: `hdr`, the seed query, the kind selector and the kind element (§4.3 (1)). -/
def seedOps (b : ℕ) : List Op :=
  [.piField fHdr 0 48, .askSeed b, .kindSel, .assertOneHot (b + 2) (b + 3) (b + 4),
   .piElem fHdr 0, .const (fun κ => .f (F.ofBytes (bytesAt (bytesOf (hdrBytes κ zeroD)) 0 16))),
   .assertEq (b + 5) (b + 6) allK]

/-- An absorb of `len` bytes at `o` of field `f`. -/
def absorbOps (f o len st b : ℕ) : List Op := [.piField f o len, .askAbsorb st b len]

/-- **`stmtOk`** after `stmt`'s absorb (§4.2, revision 3.3): the statement of `stmt` is `c`; the tag
byte is the kind's; a leaf kind's `n = 2^(m−14)` and zero bytes `41 … 127`; a node's zero bytes
`65 … 127`; a node's `hdr.pub` (bytes 16–47) is `vk` (stage-review changes 16: the extractor
rebuilds a node's FS seed from it). -/
def stmtOps (msg b : ℕ) : List Op :=
  [.hashStmt msg, .input 1, .assertEq b (b + 1) allK,
   .piField fStmt 0 1, .const (fun κ => .b (bytesOf [if κ.isNode then RecursionFast.tagNode else tagLeaf])),
   .assertEq (b + 2) (b + 3) allK,
   .piField fStmt 33 8, .const (fun κ => .b (bytesOf (enc64 (leafN κ)))),
   .assertEq (b + 4) (b + 5) (fun κ => !κ.isNode),
   .piField fStmt 41 87, .assertZero (b + 6) (fun κ => !κ.isNode),
   .piField fStmt 65 63, .assertZero (b + 7) Kind.isNode,
   .piDigest fHdr 16, .input 0, .assertEq (b + 8) (b + 9) Kind.isNode]

/-- The final message's padding is zero for the `m = 30` kinds. -/
def finalOps (b : ℕ) : List Op :=
  [.piField fFinal (2 ^ 5 * 32) ((finalElems - 2 ^ 5) * 32), .assertZero b (fun κ => decide (κ ≠ .L32))]

/-- `n` squeezes, each with its two F coordinates (width 3). -/
def sqzCoordOps : ℕ → Reg → ℕ → List Op
  | 0, _, _ => []
  | n + 1, st, b => [.askSqueeze st, .chF b 0, .chF b 1] ++ sqzCoordOps n b (b + 3)

/-- `n` squeezes (width 1). -/
def sqzOps : ℕ → Reg → ℕ → List Op
  | 0, _, _ => []
  | n + 1, st, b => .askSqueeze st :: sqzOps n b (b + 1)

/-- A univariate round's head: absorb, squeeze, `λ` (registers `b … b + 3`). -/
def uniHead (f o st b : ℕ) : List Op :=
  [.piField f o uniBytes, .askAbsorb st b uniBytes, .askSqueeze (b + 1), .chF (b + 2) 0]

/-- The 127 values of the message (registers `b + 4 … b + 130`). -/
def uniElems (f o : ℕ) : List Op := (List.range 127).map fun i => .piElem f (o + 16 * i)

/-- The interpolant at `λ` and the zero padding (registers `b + 131 … b + 133`). -/
def uniTail (f o pt b : ℕ) : List Op :=
  [.packF ((List.range 127).map (b + 4 + ·)), .targetS pt, .lagrangeS (b + 131) (b + 3) (b + 132),
   .piField f (o + 2032) 16, .assertZero (b + 135) allK]

/-- A univariate round from field `f` at `o` (width 134): `λ` at `b + 3`, the value at `b + 132`. -/
def uniOps (f o st pt b : ℕ) : List Op := uniHead f o st b ++ uniElems f o ++ uniTail f o pt b

/-- Width of one round. -/
def roundW (deg : ℕ) : ℕ := if deg = 3 then 16 else 13

/-- **One sumcheck round over F** (§2.3; A.2's message `c₀ ‖ c₁ ‖ c₂`): absorb, squeeze `r`; degree
3: `c₃ := claim + c₁ + c₂`; degree 2: check `c₁ + c₂ = claim`; the next claim `g(r)`; a dummy
round (`real` fails) has a zero message and keeps the claim. -/
def roundOpsF (f o deg : ℕ) (real : KC Bool) (st claim b : ℕ) : List Op :=
  [.piField f o 48, .askAbsorb st b 48, .askSqueeze (b + 1), .chF (b + 2) 0,
   .piElem f o, .piElem f (o + 16), .piElem f (o + 32), .addF (b + 5) (b + 6)] ++
  (if deg = 3 then
    [.addF claim (b + 7), .mulF (b + 3) (b + 8), .addF (b + 6) (b + 9), .mulF (b + 3) (b + 10),
     .addF (b + 5) (b + 11), .mulF (b + 3) (b + 12), .addF (b + 4) (b + 13),
     .assertZero b (fun κ => !real κ), .keep real (b + 14) claim]
   else
    [.assertEq (b + 7) claim real, .mulF (b + 3) (b + 6), .addF (b + 5) (b + 8),
     .mulF (b + 3) (b + 9), .addF (b + 4) (b + 10),
     .assertZero b (fun κ => !real κ), .keep real (b + 11) claim])

/-- One round over K (`P1`, degree 2; message `c₀ ‖ c₁ ‖ c₂` in K, 96 bytes). -/
def roundOpsK (f o : ℕ) (real : KC Bool) (st claim b : ℕ) : List Op :=
  [.piField f o 96, .askAbsorb st b 96, .askSqueeze (b + 1), .chK (b + 2),
   .piElemK f o, .piElemK f (o + 32), .piElemK f (o + 64), .addK (b + 5) (b + 6),
   .assertEq (b + 7) claim real, .mulK (b + 3) (b + 6), .addK (b + 5) (b + 8),
   .mulK (b + 3) (b + 9), .addK (b + 4) (b + 10),
   .assertZero b (fun κ => !real κ), .keep real (b + 11) claim]

/-- `n` rounds from round `j` (the next state is the squeeze answer `b + 2`, the next claim the
round's last register). -/
def roundsOps (f o deg : ℕ) (inK : Bool) (real : KC ℕ) : ℕ → ℕ → Reg → Reg → ℕ → List Op
  | 0, _, _, _, _ => []
  | n + 1, j, st, claim, b =>
    let w := if inK then 13 else roundW deg
    let o' := o + j * roundBytes inK
    (if inK then roundOpsK f o' (fun κ => decide (j < real κ)) st claim b
     else roundOpsF f o' deg (fun κ => decide (j < real κ)) st claim b) ++
    roundsOps f o deg inK real n (j + 1) (b + 2) (b + w - 1) (b + w)

/-- The first claim's ops (width 1 or 3) and its register. -/
def initOps (init : Init) (f o : ℕ) (inK : Bool) (uni b : ℕ) : List Op × Reg :=
  match init with
  | .uni => ([], uni)
  | .zero => ([.const fun _ => .f 0], b)
  | .free =>
    if inK then ([.piElemK f (o + 32), .piElemK f (o + 64), .addK b (b + 1)], b + 2)
    else ([.piElem f (o + 16), .piElem f (o + 32), .addF b (b + 1)], b + 2)

/-- The width of the first claim's ops. -/
def Init.width (init : Init) : ℕ := match init with | .uni => 0 | .zero => 1 | .free => 3

/-- The Merkle steps of one position (width 6 each): the sibling, the bit, the ordered halves,
the node query (`0^64` for the depths the kind lacks), the kept current digest; a dummy's sibling
slot is zero. -/
def merkleOps (i : ℕ) (j : Reg) : ℕ → ℕ → Reg → ℕ → ℕ → List Op
  | 0, _, _, _, _ => []
  | n + 1, h, cur, so, b =>
    let act : KC Bool := fun κ => decide (h < (lvl κ i).sib)
    [.piDigest fSibs so, .bitOf j h, .selectHalf (b + 1) cur b, .selectHalf (b + 1) b cur,
     .askNode i h (b + 2) (b + 3) act, .keep act (b + 4) cur,
     .assertZero b (fun κ => !act κ)] ++ merkleOps i j n (h + 1) (b + 5) (so + 32) (b + 6)

/-- The width of one position of level `i`. -/
def posW (i : ℕ) : ℕ := 4 + 6 * (lvlStar i).sib + 2

/-- The cap of level `i` starts at this offset of the caps field. -/
def capOff (i : ℕ) : ℕ := ((List.range i).map fun i' => 2 ^ (lvlStar i').cap * 32).sum

/-- One position `p` of level `i` (width `posW i`): the index, the column and its query, the fold
`y = Σ_r w[r] col_r`, the Merkle steps, the cap entry `j >>> sib` compared. -/
def posOps (i co so : ℕ) (ans : List Reg) (w : Reg) (p b : ℕ) : List Op :=
  let L := lvlStar i
  let cur := b + 4 + 6 * L.sib - 1
  [.idx (fun κ => ans.getD (p / (lvl κ i).per) 0) (fun κ => (lvl κ i).logN)
      (fun κ => p % (lvl κ i).per),
   .piField fCols (co + p * colBytes i) (colBytes i), .askCol i (b + 1), .dotKF w (b + 1)] ++
  merkleOps i b L.sib 0 (b + 2) (so + p * L.sib * 32) (b + 4) ++
  [.shrN b (fun κ => (lvl κ i).sib), .piDigestAt fCaps (capOff i) (b + 4 + 6 * L.sib),
   .assertEq (if L.sib = 0 then b + 2 else cur) (b + 4 + 6 * L.sib + 1) allK]

/-- **One phase** (number `n` of the table): its ops and the next context. -/
def genPhase (n : ℕ) (p : Phase) (c : GCtx) : List Op × GCtx :=
  let b := c.next
  let o := fun f => phaseOff n f
  let rec_ := fun (ops : List Op) (w : ℕ) (st : Reg) (out : List Reg) =>
    (ops, { c with next := b + w, st := st, outs := c.outs.push out })
  match p.shape with
  | .seed => rec_ (seedOps b) 7 (b + 1) [b + 1]
  | .absorb f len =>
    if f = fStmt then rec_ (absorbOps f (o f) len c.st b ++ stmtOps b (b + 2)) 12 (b + 1) [b]
    else if f = fFinal then rec_ (absorbOps f (o f) len c.st b ++ finalOps (b + 2)) 3 (b + 1) [b]
    else if f = fLrEnd ∨ f = fEEnd then
      rec_ (absorbOps f (o f) len c.st b ++ [.assertZero b (fun κ => !κ.isNode)]) 2 (b + 1) [b]
    else rec_ (absorbOps f (o f) len c.st b) 2 (b + 1) [b]
  | .squeezes k ch =>
    match ch with
    | .coords _ =>
      let rs := (List.range (2 * k)).map fun x => b + 3 * (x / 2) + 1 + x % 2
      let (ops, c') :=
        rec_ (sqzCoordOps k c.st b ++ [.packF rs]) (3 * k + 1) (b + 3 * k - 3) ((b + 3 * k) :: rs)
      (ops, { c' with pt := b + 3 * k })
    | .one _ => rec_ (sqzOps k c.st b ++ [.chF b 0]) (k + 1) (b + k - 1) [b + k]
    | .pos _ =>
      let ans := (List.range k).map (b + ·)
      let (ops, c') := rec_ (sqzOps k c.st b) k (b + k - 1) ans
      (ops, { c' with posAns := ans })
  | .uni f =>
    let (ops, c') := rec_ (uniOps f (o f) c.st c.pt b) 136 (b + 2) [b + 3, b + 133, b + 134]
    (ops, { c' with uni := b + 133 })
  | .rounds f k deg inK real =>
    let init := initClaim p.name
    let (iops, cl) := initOps init f (o f) inK c.uni b
    let b' := b + init.width
    let w := if inK then 13 else roundW deg
    let rs := (List.range k).map fun j => b' + w * j + 3
    let (ops, c') := rec_ (iops ++ roundsOps f (o f) deg inK real k 0 c.st cl b')
      (init.width + w * k) (if k = 0 then c.st else b' + w * k - w + 2)
      (cl :: rs ++ [if k = 0 then cl else b' + w * k - 1])
    (ops, if inK then { c' with foldR := rs } else c')
  | .queries i =>
    let L := lvlStar i
    let ops := [.packK c.foldR, .eqTableK b] ++ (List.range L.t).flatMap fun p =>
      posOps i (o fCols) (o fSibs) c.posAns (b + 1) p (b + 2 + posW i * p)
    rec_ ops (2 + posW i * L.t) c.st ((List.range L.t).map fun p => b + 2 + posW i * p + 3)

/-- The number of the phase called `name`. -/
def phaseIx (name : String) : ℕ := phases.findIdx (·.name = name)

/-- The phases from number `n`. -/
def genPhases : List Phase → ℕ → GCtx → List Op × GCtx
  | [], _, c => ([], c)
  | p :: ps, n, c =>
    let r₁ := genPhase n p c
    let r₂ := genPhases ps (n + 1) r₁.2
    (r₁.1 ++ r₂.1, r₂.2)

/-- The skeleton: every phase of the table, from register `0`. -/
def skeleton : List Op × GCtx := genPhases phases 0 ⟨0, 0, 0, [], [], 0, #[]⟩

/-- **`genWith fin mode`**: the verifier program of a kind (`.fixed κ`) or the mux (`.mux`): the
skeleton, the phase-final checks (all after the skeleton: they ask nothing, so their place does not
change the transcript), `accept`. `FRVIRFinals.gen` instantiates `fin` with the typed `Finals`. -/
def genWith (fin : FinOps) (mode : Mode) : VProg :=
  ⟨mode, skeleton.1 ++ fin skeleton.2.outs skeleton.2.next ++ [.accept]⟩

/-! ## Controls of the fast twins (S-E8) -/

/-- A 16-byte column: one row, the `F` element `1`. -/
def col1 : ByteArray := ⟨#[1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]⟩
/-- A 32-byte column: rows `1` and `x` (`c₀ = 2`). -/
def col2 : ByteArray := ⟨#[1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
  2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]⟩

/-- (+) `dotKF` on one row, through its twin. -/
theorem dotKF_pos : dotKF #[1] col1 = 1 := by rw [← dotKFF_eq]; decide +kernel

/-- (−) The loop one row short is not `dotKF` (the second row counts). -/
theorem dotKF_neg : dotKFGo #[1, 1] col2 1 0 0 ≠ dotKF #[1, 1] col2 := by
  rw [← dotKFF_eq]; decide +kernel

/-- The digest `0, 1, …, 31`. -/
def dCtl : Digest := Vector.ofFn fun i => i.val.toUInt8

/-- (+) `idxOf` through its twin: bits `[8, 12)`, `[12, 24)` and past the end. -/
theorem idxOf_pos : idxOf 4 dCtl 2 = 1 ∧ idxOf 12 dCtl 1 = 32 ∧ idxOf 20 dCtl 13 = 0 := by
  simp only [← idxOfF_eq]; decide +kernel

/-- (−) The window one byte late is not `idxOf`. -/
theorem idxOf_neg : dWin dCtl (12 / 8 + 1) >>> (12 % 8) % (1 <<< 12) ≠ idxOf 12 dCtl 1 := by
  rw [← idxOfF_eq]; decide +kernel

/-- (+) The node query's length and level byte. -/
theorem nodeQ_pos : (nodeQ 3 zeroD zeroD).size = 72 ∧ (nodeQ 3 zeroD zeroD).data[6]! = 3 := by
  rw [← nodeQF_eq]; decide +kernel

/-- (−) The children's order matters. -/
theorem nodeQ_neg : nodeQ 0 zeroD (Vector.replicate 32 1) ≠ nodeQ 0 (Vector.replicate 32 1) zeroD := by
  rw [← nodeQF_eq, ← nodeQF_eq]; decide +kernel

/-- Forty bytes `0, …, 39`. -/
def qCtl : ByteArray := ⟨Array.ofFn (n := 40) fun i => i.val.toUInt8⟩

/-- (+) A digest inside `q`, and one running past its end (zero-padded), through the twin. -/
theorem bytesAt_pos : bytesAt qCtl 8 32 = Vector.ofFn (fun i => (i.val + 8).toUInt8) ∧
    (bytesAt qCtl 20 32)[19] = 39 ∧ (bytesAt qCtl 20 32)[20] = 0 := by
  simp only [← digestAt_eq]; decide +kernel

/-- (−) The offset matters. -/
theorem bytesAt_neg : digestAt qCtl 8 ≠ bytesAt qCtl 9 32 := by rw [← digestAt_eq]; decide +kernel

/-- Kind weights with `c₀ = 2^i`: a sum of them names its set of kinds. -/
def kwCtl : Array F := Array.ofFn (n := 9) fun i => ⟨⟨(2 ^ i.val : ℕ).toUInt64⟩, ⟨0⟩⟩

/-- (−) **`free` in the walk** (the 3.15 node vector put `v_free` at index 8, R-V-M2): with weights
`2^i`, row 0 is pinned by `chain`, `streamStart`, `hashA`, `hashB1`, `w43`, so its mask is the other
four kinds' weights, `free`'s 256 included; past `pinEnd` it is all nine. -/
theorem maskOf_free_old : maskOf kwCtl 0 = ⟨⟨2 + 8 + 64 + 256⟩, ⟨0⟩⟩ ∧
    maskOf kwCtl (pinEnd + 1) = ⟨⟨511⟩, ⟨0⟩⟩ := by
  decide +kernel

/-- **The node's kind weights for the walk** (`finLc` (ii), revision 3.16, R-V-M2): `0` at `chain`,
`v_0 … v_6` at `stream … w43`, and `0` at `free` (`free`'s term is the closed form
`(1 + α)·v_free·⟨rowW, eq(r_k, ·)⟩`, not the walk: `A₀^free = I`). -/
def nodeKindW (v : List F) : List F := 0 :: (v.take 7 ++ [0])

/-- The control's claims `v_i = 2^(i+1)`. -/
def kwV : List F := List.ofFn (n := 8) fun i => ⟨⟨(2 ^ (i.val + 1) : ℕ).toUInt64⟩, ⟨0⟩⟩

/-- (+) **`free` has mask weight 0** (revision 3.16): with the node vector `nodeKindW`, row 0's mask
is `stream`, `streamEnd41`, `hashB2` only, and past `pinEnd` it is every kind but `free`. -/
theorem maskOf_pos : maskOf (nodeKindW kwV).toArray 0 = ⟨⟨2 + 8 + 64⟩, ⟨0⟩⟩ ∧
    maskOf (nodeKindW kwV).toArray (pinEnd + 1) = ⟨⟨254⟩, ⟨0⟩⟩ := by
  decide +kernel

/-- (+) **`assertBit`** (revision 3.16, R-V-m1): the F values `0`, `1` and bits pass. -/
theorem isBit_pos : Val.isBit (.f 0) = true ∧ Val.isBit (.f 1) = true ∧ Val.isBit (.bit false) = true :=
  by decide +kernel

/-- (−) … the F value `x` (`2`), a digest and a number do not. -/
theorem isBit_neg : Val.isBit (.f ⟨⟨2⟩, ⟨0⟩⟩) = false ∧ Val.isBit (.d zeroD) = false ∧
    Val.isBit (.n 1) = false := by decide +kernel

/-- (−) Row 1100 (in `[1024, 1152]`, pinned by every kind but `free`) does not take the shared value:
`pinEnd` cannot be lowered. -/
theorem maskOf_neg : maskOf kwCtl 1100 ≠ maskOf kwCtl (pinEnd + 1) := by decide +kernel

/-- (−) **`assertBit` rejects a non-bit** (revision 3.16, R-V-m1; before, it was a no-op): the
F value `2` clears `ok` where the op is active. -/
theorem assertBit_rejects (impl : OpImpl) (κ : Kind) (inp : Input) :
    evalOp impl κ inp #[.f ⟨⟨2⟩, ⟨0⟩⟩] (.assertBit 0 allK) = .vals [] false := rfl

/-- (+) … accepts a bit, and is inactive where `act` fails. -/
theorem assertBit_accepts (impl : OpImpl) (κ : Kind) (inp : Input) :
    evalOp impl κ inp #[.f 1] (.assertBit 0 allK) = .vals [] true ∧
      evalOp impl κ inp #[.f ⟨⟨2⟩, ⟨0⟩⟩] (.assertBit 0 fun _ => false) = .vals [] true :=
  ⟨rfl, rfl⟩

end FR
