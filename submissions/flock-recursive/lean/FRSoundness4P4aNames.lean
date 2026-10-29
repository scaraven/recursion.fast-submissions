-- New for `flock-recursive` (BLUEPRINT revision 4.1, A.10 rows Z1 … S2, B-12; stage P4a).
-- RET-2: import re-pointed at Core: `FRSoundnessFrZM` → `FRSoundnessCoreFront`.
import FRSoundnessCoreFront
import FRSoundness4Pos
import FRSegTarget4
import FRSoundness4TailStep

/-!
# The front's Z, L, S names at revision 4.1 (positions < 170): the asserted checks and the dooms

Revision 4.1's Z, L and S sit at 3.x's positions (S-G13 §0.1: identity below 170). What changes is
the **chain kind** (`CKind`, six kinds, read at byte 71 by `kindOfC`) and, for a **segment**, the
variable last block `L = n − 1` (B-12), which enters Z2's public target (the range factor) and S's
boundary (the shift's end at block `L`, the successor masked there).

* **The asserted checks** (`Rej*`, read on the log only, as the verifier computes them):
  **`RejZ`** (`relZ`'s first conjunct), 3.x's **`RejL2`** verbatim (kind-free: 14 rounds from 69),
  **`RejLc2`** (a segment's `finLc` (ii)), **`RejLcN`** (a node's), **`RejS2`** (S2's `nb + 10`
  round checks). R4 proves `¬ Rej*` on an accepted run of `gen4`.
* **The dooms** read the decoded witness through a parameter **`zw : Wit`** (`z = unpack f⁽⁰⁾` per
  kind; T4/X4 supply it) and the matrices through **`ZLM4`** (a kind's indicators; the target reads
  the log, so a segment's is the chain target on the blocks `t ≤ L` and `0` past, **`EtSeg`**).
* **The segment's last block** on the log: **`nStmt`** (`n mod 2^24` from `stmt` bytes 33–35, as
  `lastOps` reads it) and **`lastL`** (`(n − 1) mod 2^18`, `lastOps`' borrow chain).
* The rounds' dooms are T4's `T4.D3`/`T4.D2` (round count `nr (kindOfC es)`); the witness `zw` is
  T4's `T4.zW` at X4.
-/

namespace FR.Snd.P4a
open RecursionFast FR.Merkle Finset FR.Impl

set_option linter.constructorNameAsVariable false

noncomputable section

/-! ## Kinds and dimensions -/

/-- `κ.m − d` (3.x's `mm d`). -/
def mC (d : ℕ) (κ : CKind) : ℕ := κ.m - d

/-- The kind's block coordinates `nb = m − 14`. -/
def nbC (κ : CKind) : ℕ := κ.m - 14

/-- **The decoded witness's bits** per kind: `zw κ L es b` is bit `b` of `z = unpack f⁽⁰⁾` on the
log `L` and the chain `es` (T4's `zW` at `CKind`). -/
abbrev Wit : Type := CKind → Log → Log → ℕ → F

/-- **The kinds' block matrices** (revision 4.1): `Ak j`, `Bk j` over a block's `2^14` positions
(A.6's nine kinds), the indicators `Ind κ j t`, and the public target bits `Et κ es t p`, which
read the log (a segment's target depends on its last block `L`). -/
structure ZLM4 where
  Ak : Fin 9 → Fin (2 ^ 14) → Fin (2 ^ 14) → F
  Bk : Fin 9 → Fin (2 ^ 14) → Fin (2 ^ 14) → F
  Ind : CKind → Fin 9 → ℕ → F
  Et : CKind → Log → ℕ → Fin (2 ^ 14) → F

/-- The matrices, indicators and targets are bit-valued. -/
def ZLM4.Bits (M : ZLM4) : Prop :=
  (∀ j p k, IsBitF (M.Ak j p k)) ∧ (∀ j p k, IsBitF (M.Bk j p k)) ∧
    (∀ κ j t, IsBitF (M.Ind κ j t)) ∧ ∀ κ es t p, IsBitF (M.Et κ es t p)

/-- **The kinds' indicators match the L3 mask**: a node has no `chain` block, a segment only
`chain` blocks. -/
def ZLM4.IndKinds (M : ZLM4) : Prop :=
  ∀ κ t, (κ.isNode = true → M.Ind κ 0 t = 0) ∧
    (κ.isNode = false → ∀ j : Fin 9, j ≠ 0 → M.Ind κ j t = 0)

/-! ## A segment's last block on the log -/

/-- **`n mod 2^24`** as `lastOps` reads it: the 24-bit index 0 of the digest at `stmt` byte 33
(`stmt` bytes 33–35, little-endian). -/
def nStmt (es : Log) : ℕ := idxOfF 24 (digestAt (msgAt es 1) 33) 0

/-- **The last block** `L = (n − 1) mod 2^18` (`lastOps`' borrow chain over `n`'s 18 low bits). -/
def lastL (es : Log) : ℕ := (nStmt es + (2 ^ 18 - 1)) % 2 ^ 18

/-- The borrow into bit `k` of `N − 1` (`c_0 = 1`, `c_{k+1} = ¬N_k ∧ c_k`). -/
def borrow (N : ℕ) : ℕ → Bool
  | 0 => true
  | k + 1 => !N.testBit k && borrow N k

/-- Bit `k` of `N − 1`: `N_k ⊕ c_k`. -/
def lb (N k : ℕ) : Bool := N.testBit k ^^ borrow N k

/-- A Boolean in F. -/
def bF (x : Bool) : F := if x then 1 else 0

/-- `L`'s 18 bits in F, as `lastOps`' borrow chain computes them (`lastOuts`' registers;
`FRSoundness4P4aLast.lastSum`: they sum to `lastL`). -/
def lastBits (es : Log) : List F := (List.range 18).map fun k => bF (lb (nStmt es) k)

/-- **A segment's public target** (B-12, `targetSSegS` on the blocks): the chain block's target on
the blocks `t ≤ Lb`, `0` past. -/
def EtSeg (Lb t : ℕ) (p : Fin (2 ^ 14)) : F := if t ≤ Lb then chainE p.val else 0

/-- **The entry's matrices at revision 4.1**: 3.x's block matrices (`kMat`), a segment's indicator
(every block `chain`) and target (`EtSeg` at `lastL`); a node's indicators and targets are the
parameters `indN`, `etN` (S-E's node circuit maps, S-G13 F3). -/
def zlm4 (indN : Rev4.NodeKind → Fin 9 → ℕ → F) (etN : Rev4.NodeKind → ℕ → Fin (2 ^ 14) → F) : ZLM4 where
  Ak := kMat Block.circuitR1CS.A
  Bk := kMat Block.circuitR1CS.B
  Ind κ j t := match κ with
    | .seg _ => if j.val = 0 then 1 else 0
    | .node ν => indN ν j t
  Et κ es t p := match κ with
    | .seg _ => EtSeg (lastL es) t p
    | .node ν => etN ν t p

/-! ## Z (positions 2 … 67) -/

variable (M : ZLM4) (zw : Wit)

/-- Block `t`'s bit `k`. -/
def zBk (κ : CKind) (L es : Log) (t : ℕ) (k : Fin (2 ^ 14)) : F := zw κ L es (2 ^ 14 * t + k.val)

/-- `(A z)` at block `t`, position `p`. -/
def mvZ (A : Fin 9 → Fin (2 ^ 14) → Fin (2 ^ 14) → F) (κ : CKind) (L es : Log) (t : ℕ)
    (p : Fin (2 ^ 14)) : F :=
  ∑ j : Fin 9, M.Ind κ j t * ∑ k, A j p k * zBk zw κ L es t k

/-- The slice tables `a = A z`, `b = B z`, `z`, `E` (slice `σ`; `u`: 8 position bits, the block). -/
def aZ (ℓ : ℕ) (κ : CKind) (L es : Log) : Fin 64 → Fin (2 ^ ℓ) → F :=
  fun σ u => mvZ M zw M.Ak κ L es (u.val / 256) (pAt σ u.val)
def bZ (ℓ : ℕ) (κ : CKind) (L es : Log) : Fin 64 → Fin (2 ^ ℓ) → F :=
  fun σ u => mvZ M zw M.Bk κ L es (u.val / 256) (pAt σ u.val)
def zZ (ℓ : ℕ) (κ : CKind) (L es : Log) : Fin 64 → Fin (2 ^ ℓ) → F :=
  fun σ u => zBk zw κ L es (u.val / 256) (pAt σ u.val)
def eZ (ℓ : ℕ) (κ : CKind) (es : Log) : Fin 64 → Fin (2 ^ ℓ) → F :=
  fun σ u => M.Et κ es (u.val / 256) (pAt σ u.val)

/-- **Z's statement**: on the `2^(m−6)` slice points, `(A z)(B z) = z + E`. -/
def ZHolds (L es : Log) : Prop :=
  BHolds (ℓ := mC 6 (kindOfC es)) (aZ M zw _ (kindOfC es) L es) (bZ M zw _ (kindOfC es) L es)
    (zZ zw _ (kindOfC es) L es) (eZ M _ (kindOfC es) es)

/-- The residual slice `i`. -/
def zres (L es : Log) (i : Fin 64) : Fin (2 ^ mC 6 (kindOfC es)) → F :=
  bzRes (aZ M zw _ (kindOfC es) L es) (bZ M zw _ (kindOfC es) L es) (zZ zw _ (kindOfC es) L es)
    (eZ M _ (kindOfC es) es) i

/-- **Z1's point** `r = (ρ₁ … ρ₇, Z1's first m − 13 coordinates)`. -/
def zrL (es : Log) : List F :=
  List.ofFn pinnedRho ++ (List.range ((kindOfC es).m - 13)).map (coordAt es 2)

/-- **Z1's final doom**: some residual slice's extension at `r` is nonzero. -/
def ZEnd (L es : Log) : Prop :=
  ∃ i : Fin 64, mle (zres M zw L es i) (ptOf (mC 6 (kindOfC es)) (zrL es)) ≠ 0

/-- `P^e` on `S`: `Σ_u eq(r, u) E(σ, u)` (the verifier's `targetS r`). -/
def peL (es : Log) : Fin 64 → F := fun σ =>
  ∑ u, eq (ptOf (mC 6 (kindOfC es)) (zrL es)) (cube u) * eZ M _ (kindOfC es) es σ u

/-- **Z3's initial claim** `P^{ab}*(λ)`. -/
def c0Z (es : Log) : F := interpolateAt node127 (z2Vals (pzL es) (pabL es) (peL M es)) (lamL es)

/-- The true `P^{ab}`, `P^z` at Z1's point. -/
def pabT (L es : Log) : Polynomial F :=
  pabPoly (ptOf (mC 6 (kindOfC es)) (zrL es)) (aZ M zw _ (kindOfC es) L es)
    (bZ M zw _ (kindOfC es) L es)
def pzT (L es : Log) : Polynomial F :=
  pzPoly (ptOf (mC 6 (kindOfC es)) (zrL es)) (zZ zw _ (kindOfC es) L es)

/-- **The pending c-claim is false**: `P^z*(λ) ≠ ẑ(r, λ)` (3.x's `pzStar` is kind-free). -/
def PendZ (L es : Log) : Prop := 14 < es.length ∧ pzStar es ≠ (pzT zw L es).eval (lamL es)

/-- After `λ`: Z3's initial claim or the c-claim is false. -/
def Z2Bad (L es : Log) : Prop :=
  14 < es.length ∧ (c0Z M es ≠ (pabT M zw L es).eval (lamL es) ∨ PendZ zw L es)

/-- **Z2's doom** (positions 13, 14): `ZEnd` until `λ`, then `Z2Bad`. -/
def Z2D (L es : Log) : Prop := if es.length ≤ 14 then ZEnd M zw L es else Z2Bad M zw L es

/-- Z3's tables `eq(r, ·)`, `Â(λ, ·)`, `B̂(λ, ·)`. -/
def TZ (L es : Log) : Array (Array F) :=
  bzTables (ℓ := mC 6 (kindOfC es)) (zrL es) (lamL es) (aZ M zw _ (kindOfC es) L es)
    (bZ M zw _ (kindOfC es) L es)

/-- **Z3's rounds' doom** (`T4.D3` from 15, `m − 6` real rounds). -/
abbrev D3Z : Log → Log → Prop :=
  T4.D3 15 (fun _ es => c0Z M es) (mC 6) bzExpr (TZ M zw)

/-- Z3's challenges `r′`. -/
def rZ (es : Log) : List F := rchs 15 es (mC 6 (kindOfC es))

/-- The true pair at `(λ, r′)`. -/
def aStar (L es : Log) : F :=
  mle (fun u => (skipExt fun i => aZ M zw (mC 6 (kindOfC es)) (kindOfC es) L es i u).eval (lamL es))
    (ptOf (mC 6 (kindOfC es)) (rZ es))
def bStar (L es : Log) : F :=
  mle (fun u => (skipExt fun i => bZ M zw (mC 6 (kindOfC es)) (kindOfC es) L es i u).eval (lamL es))
    (ptOf (mC 6 (kindOfC es)) (rZ es))

/-- **`relZ`'s first conjunct fails on the log** (from 68): Z3's last claim is not
`eq(r, r′)·â·b̂`. -/
def RejZ (L es : Log) : Prop :=
  68 ≤ es.length ∧ clR 15 (fun _ es => c0Z M es) L es (mC 6 (kindOfC es)) ≠
    eq (ptOf (mC 6 (kindOfC es)) (zrL es)) (ptOf (mC 6 (kindOfC es)) (rZ es)) * (vZ es 0 * vZ es 1)

/-- **Zend's doom**: the absorbed pair is not the true one. -/
def ZendBad (L es : Log) : Prop :=
  68 ≤ es.length ∧ (vZ es 0, vZ es 1) ≠ (aStar M zw L es, bStar M zw L es)

/-- **The c-claim's binding** (`relZ`'s second conjunct): RS claim 1's value is `P^z*(λ)`. -/
def oZ (_κ : CKind) (es : Log) (v : F) : Prop := v = pzStar es

/-! ## L (positions 68 … 98) -/

/-- A kind's block bits `q = m − 14`. -/
def qL (κ : CKind) : ℕ := κ.m - 14

/-- The row point's 8 high bits and the block point (Z3's `r′`). -/
def rhiL (es : Log) : Fin 8 → F := ptOf 8 (rZ es)
def rbLc (es : Log) : Fin (qL (kindOfC es)) → F := ptOf _ ((rZ es).drop 8)

/-- The indicators as tables on the block cube. -/
def IndF (κ : CKind) (q : ℕ) : Fin 9 → Fin (2 ^ q) → F := fun j t => M.Ind κ j t.val

/-- The quirky row weights `rowW λ r′_hi`. -/
def rwL (es : Log) : Fin (2 ^ 14) → F := rowW (p := 8) (lamL es) (rhiL es)

/-- `z` over 14 position and `q` block bits. -/
def zN (κ : CKind) (L es : Log) (q : ℕ) : Fin (2 ^ (14 + q)) → F := fun y => zw κ L es y.val

/-- **The true `â`, `b̂`** in the lincheck's form (`linAK`). -/
def aLin (L es : Log) : F :=
  linAK M.Ak (IndF M (kindOfC es) _) (rwL es) (rbLc es) (zN zw (kindOfC es) L es (qL (kindOfC es)))
def bLin (L es : Log) : F :=
  linAK M.Bk (IndF M (kindOfC es) _) (rwL es) (rbLc es) (zN zw (kindOfC es) L es (qL (kindOfC es)))

/-- **L1's doom** (after `α`): the batched claim `â + α b̂` is false. -/
def L1Bad (L es : Log) : Prop :=
  69 ≤ es.length ∧ vZ es 0 + alL es * vZ es 1 ≠ aLin M zw L es + alL es * bLin M zw L es

/-- L2's tables: per kind `M_α` and the folded column `z̄_j`. -/
def TL (L es : Log) : Array (Array F) :=
  kindTables (K := 8) (fun j => linM (M.Ak j) (M.Bk j) (rwL es) (alL es))
    (zfoldK (IndF M (kindOfC es) _) (rbLc es) (zN zw (kindOfC es) L es (qL (kindOfC es))))

/-- **L2's rounds' doom** (from 69, 14 rounds, degree 2). -/
abbrev D2L : Log → Log → Prop :=
  T4.D2 69 16 readF (fun d => chF d 0) (fun _ es => c0L es) (fun _ => 14) (kindExpr 8) (TL M zw)

/-- **L2's round checks fail**: 3.x's `RejL2` (kind-free). -/
abbrev RejL2 : Log → Log → Prop := FR.Snd.RejL2

/-- **The kind-masked values** (`finLc`'s `packFK`): a node's `0 :: v`, a segment's `v₀ :: 0^8`. -/
def vM (κ : CKind) (es : Log) (j : Fin 9) : F :=
  if κ.isNode then (if j.val = 0 then 0 else vL es (j.val - 1)) else (if j.val = 0 then vL es 0 else 0)

/-- The per-kind true values `z̄̃_j(r_k)`. -/
def zfL (L es : Log) (j : Fin 9) : F :=
  mle (zfoldK (IndF M (kindOfC es) _) (rbLc es) (zN zw (kindOfC es) L es (qL (kindOfC es))) j)
    (ptOf 14 (rkL es))

/-- `finLc` (ii) fails on the log for the kind flag `b`: L2's last claim is not
`Σ_j v′_j M̃_j(r_k)`. -/
def PLc (b : Bool) (L es : Log) : Prop :=
  (kindOfC es).isNode = b ∧ clR2 69 16 readF (fun d => chF d 0) (fun _ es => c0L es) L es 14 ≠
    ∑ j, vM (kindOfC es) es j * mle (linM (M.Ak j) (M.Bk j) (rwL es) (alL es)) (ptOf 14 (rkL es))

/-- **A segment's `finLc` (ii) fails** (from 98). -/
def RejLc2 (L es : Log) : Prop := 98 ≤ es.length ∧ PLc M false L es

/-- **A node's `finLc` (ii) fails** (from 98). -/
def RejLcN (L es : Log) : Prop := 98 ≤ es.length ∧ PLc M true L es

/-- **L3's doom** (a segment): some masked value is not the kind's true value. -/
def L3Bad (L es : Log) : Prop :=
  98 ≤ es.length ∧ (kindOfC es).isNode = false ∧ ∃ j, vM (kindOfC es) es j ≠ zfL M zw L es j

/-- The batch's true values (a segment): kind `0`'s, then zeros. -/
def tL (L es : Log) (i : Fin 8) : F := if i.val = 0 then zfL M zw L es 0 else 0

/-- **The pending Lc claim is false** (a segment, after `β`). -/
def PendLc (L es : Log) : Prop :=
  99 ≤ es.length ∧ (kindOfC es).isNode = false ∧
    vBetaL es ≠ ∑ i : Fin 8, fAt es 98 0 ^ i.val * tL M zw L es i

/-! ## S (positions 98 … 169) -/

/-- S1's `τ` (the kind's `nb` read coordinates). -/
def tauL (κ : CKind) (es : Log) : List F := (List.range (nbC κ)).map (coS es)

/-- S2's challenges: the block part (`nb`), the position part (10). -/
def rbL (κ : CKind) (es : Log) : List F := (List.range (nbC κ)).map (rch 114 es)
def rpL (κ : CKind) (es : Log) : List F := (List.range 10).map fun l => rch 114 es (nbC κ + l)

/-- **The shift's boundary values**: a segment's `s` (`hdr` bytes 16–47) and `h` (`stmt` bytes
1–32); a node's are `0`. -/
def bndL (κ : CKind) (es : Log) : List F :=
  if κ.isNode then [0, 0, 0, 0] else
    [readF (entAt es 0).1 87, readF (entAt es 0).1 103, readF (msgAt es 1) 1, readF (msgAt es 1) 17]

/-- The start digest's bit `σ` and the end digest's. -/
def sbL (κ : CKind) (es : Log) (σ : ℕ) : F :=
  if digBit ((bndL κ es).getD 0 0) ((bndL κ es).getD 1 0) σ then 1 else 0
def hbL (κ : CKind) (es : Log) (σ : ℕ) : F :=
  if digBit ((bndL κ es).getD 2 0) ((bndL κ es).getD 3 0) σ then 1 else 0

/-- A list padded to 18 coordinates. -/
def pad18 (κ : CKind) (xs : List F) : Array F := (xs ++ List.replicate (18 - nbC κ) 0).toArray

/-- **The end block's bits** in `shiftTarget`'s operand: a segment's `L` (B-12, `lastRegs`), a
node's last block `2^nb − 1` (3.x's `lastPad`). -/
def endBits (κ : CKind) (es : Log) : List F :=
  if κ.isNode then lastPad (nbC κ) (18 - nbC κ) else lastBits es

/-- **S2's initial claim** (`finSh` (i) on `shiftTarget`'s specification). -/
def c0S (es : Log) : F :=
  shiftTargetS (ksL es) (pad18 (kindOfC es) (tauL (kindOfC es) es)) (thL es).toArray
    (bndL (kindOfC es) es ++ endBits (kindOfC es) es).toArray

/-- S2's round count `nb + 10`. -/
def nrS (κ : CKind) : ℕ := nbC κ + 10

/-- S2's initial claim as a `T4.D2` claim. -/
def c0SL (_L es : Log) : F := c0S es

/-- **S2's round checks fail** (the verifier's `c₁ + c₂ = claim` asserts). -/
def RejS2 (L es : Log) : Prop :=
  ∃ l < nrS (kindOfC es), 114 + 2 * l < es.length ∧
    ¬ Chk2 114 16 readF (fun d => chF d 0) c0SL L es l

end

end FR.Snd.P4a
