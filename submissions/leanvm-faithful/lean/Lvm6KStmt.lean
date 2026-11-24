-- New for lvm6 K1: the frozen statements of the tree batch and the sponge batch (BLUEPRINT §2.3 v3,
-- §5 T1/T2; `FORMAT6.md` §6.2, §6.3, §S). Frozen 2026-11-22 (`docs/lvm6/stages/K1-keccak.md`): a proof
-- never changes them.
import Lvm6KProg
import LvmE2VKec
import Lvm6StmtPhase

/-!
# The tree and sponge batches: relations, claims and frozen statements

Category A (specification of intent). The stack `q : ℕ → K` holds slot `o` of heap row `x` at
index `x + 2^κ·o` (`κ = logN + 1` row bits, slot high; BLUEPRINT §2.2).

* **`TreeOkG κ q h`** (BLUEPRINT §2.3, relation `TreeOk(q, h)` with the committed middle state): (W) parent row `k ≠ 0`'s slots
  `0 … 3` are the output lanes `0 … 3` of row `2k`, and every parent row's (row 0 included)
  slots `4 … 7` are those of row `2k + 1`; (R) row 0's slots `4 … 7` are the words of `h`; (G)
  every row's middle state (slots `8 … 32`) is 12 rounds of its input lanes `inTree`
  (`nodeLanes` of slots `0 … 7` on rows `< 2^(κ−1)`, `itemLanes` of slots `0 … 3` on the leaf
  rows), and its output is 12 more rounds (virtual, `outW`). Leaf rows' slots `4 … 7` and row 0's
  slots `0 … 3` are unconstrained.
* `TreeOkGStmt`: `TreeOkG (k+1) q h → TreeOkAt k q h` (WP S's relation, `Lvm6StmtTree`; S's
  `treeOk_sound` then gives `dataRoot (blocksOfAt k q) = h`). `Stack` is S's.
* `treeCols κ h out`: the 13 column claims the tree batch leaves on the stack (§6.2: 8 wiring
  claims at `(ρ, 0)`, 4 Boolean root claims at row 0, the middle-state claim `c_out`), and the 64
  slice claims (`SlicesTrue6`) at the input end's point.
* **`TreeSpecStmt κ`** (T2, `treeSpec`): the tree batch `treeProg κ` in the doom calculus, S1's
  `ksSpecE2` shape: from doom of `TreeOkG ∧ R` to doom of `TreeClaims ∧ R`, lead `0`, every group
  `≤ εS = 7·2^-131`, at one candidate.
* **`SpongeSpecStmt h nt`**: the sponge caller `spCaller6 h` (the v6 core inside season 1's
  caller): from doom of `RegionValid ∧ OutRel ∧ R` (season 1's sponge relation) to doom of the
  middle word claim, the 64 slice claims and the tied lanes' claims. The sponge link is season
  1's `ksLinkSpecE2`, unchanged (FORMAT6 §T: CB).
* **`TreeBridgeStmt`**: `TreeSpecStmt` at every `κ ≥ 5` gives WP S's `Stmt.treeSpec treeProgS`
  (`treeProgS` maps the output to S's `TreeOut`; it fails outside `M = logN + 7`, `logN ≥ 4`).
-/

set_option autoImplicit false

namespace Lvm6.K

open LeanVM.Parameters LeanVM.Semantics LeanVM.Protocol.Compile LeanVM.Protocol.Verifier
open LeanVM.Protocol.KeccakGkr (roundsFrom laneWord inState RegionValid)
open LeanVM.Protocol.EndToEnd.Front (Doomed Stable)
open Lvm.E2V
open Lvm.ASM (εS)
open RecursionFast
open Finset
open scoped ENNReal

/-! ## The stack and the tree relation -/

/-- The words of slots `base … base + 3` of row `x`, as lanes. -/
def wordsAt (κ : ℕ) (q : Stack) (x base : ℕ) : ℕ → UInt64 := fun j ↦ K.lane (q (x + 2 ^ κ * (base + j)))

/-- **Row `x`'s input lanes** (BLUEPRINT §2.3, the input map): `nodeLanes` of slots `0 … 7` on
the parent rows `x < 2^(κ−1)`, `itemLanes` of slots `0 … 3` on the leaf rows. -/
def inTree (κ : ℕ) (q : Stack) (x : ℕ) : KeccakState :=
  if x < 2 ^ (κ - 1) then nodeLanes (wordsAt κ q x 0) (wordsAt κ q x 4) else itemLanes (wordsAt κ q x 0)

/-- Row `x`'s committed middle state: slots `8 … 32`. -/
def midTree (κ : ℕ) (q : Stack) (x : ℕ) : KeccakState :=
  Vector.ofFn fun l : Fin 25 ↦ K.lane (q (x + 2 ^ κ * (8 + l)))

/-- Row `x`'s output lane `m` (virtual): 12 rounds of the middle state. -/
def outW (κ : ℕ) (q : Stack) (x m : ℕ) : K := laneWord (roundsFrom 12 12 (midTree κ q x)) m

/-- **The tree relation with the committed middle state** (BLUEPRINT §2.3 v3, `TreeOk(q, h)` with
(G) on slots `8 … 32`): what the tree batch's reduction proves. It implies WP S's `TreeOkAt`
(`Lvm6StmtTree`, whose outputs are `keccakF` of the input directly): `TreeOkGStmt`. -/
structure TreeOkG (κ : ℕ) (q : Stack) (h : Digest) : Prop where
  /-- (W) slots `0 … 3` of parent row `k ≠ 0` are row `2k`'s output lanes `0 … 3`. -/
  wl : ∀ k, 1 ≤ k → k < 2 ^ (κ - 1) → ∀ m < 4, q (k + 2 ^ κ * m) = outW κ q (2 * k) m
  /-- (W) slots `4 … 7` of every parent row (row 0 included) are row `2k + 1`'s. -/
  wr : ∀ k < 2 ^ (κ - 1), ∀ m < 4, q (k + 2 ^ κ * (4 + m)) = outW κ q (2 * k + 1) m
  /-- (R) row 0's slots `4 … 7` are the words of `h`. -/
  root : ∀ m < 4, q (2 ^ κ * (4 + m)) = K.ofLane (dLane h m)
  /-- (G) every row's middle state is 12 rounds of its input lanes. -/
  perm : ∀ x < 2 ^ κ, midTree κ q x = roundsFrom 0 12 (inTree κ q x)

/-- **`TreeOkG` implies WP S's `TreeOkAt`** (statement; `treeOkG_treeOkAt`): with `κ = k + 1`, the
middle state is mechanism, so S's `treeOk_sound` gives the data root. -/
def TreeOkGStmt : Prop :=
  ∀ (k : ℕ) (q : Stack) (h : Digest), TreeOkG (k + 1) q h → TreeOkAt k q h

/-- **Non-vacuity of `TreeOkG`** (statement): every `2^k` blocks have a stack with the honest
middle states satisfying `TreeOkG` for their root, whose blocks they are. -/
def TreeOkGHonestStmt : Prop :=
  ∀ (k : ℕ) (xs : List Digest), xs.length = 2 ^ k →
    ∃ q : Stack, TreeOkG (k + 1) q (dataRoot xs) ∧ blocksOfAt k q = xs

/-! ## The claims -/

/-- A column claim on a table of `2^n` words: the point and the value. -/
abbrev SClaim : Type := List E2 × E2

/-- A column claim holds on `q` (`n` variables): its point has `n` coordinates and `q̃` there is
the value. -/
def ColTrue (n : ℕ) (q : ℕ → K) (c : SClaim) : Prop := c.1.length = n ∧ stepMleK n c.1 q = c.2

/-- The 64 bit-slice claims hold on `q` (`n` variables) at `pt`. -/
def SlicesTrue6 (n : ℕ) (q : ℕ → K) (pt s : List E2) : Prop :=
  pt.length = n ∧ s.length = 64 ∧ ∀ i < 64,
    s.getD i 0 = ∑ x ∈ range (2 ^ n), eqAtF pt x * bitF ((q x).toBitVec.getLsbD i)

/-- **The tree batch's column claims** (§6.2, after rows 2–4 and row 9): wiring
`q̃((ρ, 0), slot m) = D⁰_m + eq(ρ, 0)·δ_m` and `q̃((ρ, 0), slot 4+m) = D¹_m`; root
`q(row 0, slot 4+m) = h_m`; middle `q̃((u, ρ), ϱm) = c_out`. -/
def treeCols (κ : ℕ) (h : Digest) (out : TreeOut) : List SClaim :=
  (List.range 4).map (fun m ↦ (out.ρ ++ [0] ++ bitsF m 6,
      out.dd.getD m 0 + eqAtF out.ρ 0 * kF (out.δ.getD m 0))) ++
    (List.range 4).map (fun m ↦ (out.ρ ++ [0] ++ bitsF (4 + m) 6, out.dd.getD (4 + m) 0)) ++
    (List.range 4).map (fun m ↦ (bitsF 0 κ ++ bitsF (4 + m) 6, kF (K.ofLane (dLane h m)))) ++
    [((out.u :: out.ρ) ++ out.hd.ϱm, out.hd.cout)]

/-- **The claims the tree batch leaves**: the 13 column claims and the 64 slice claims. -/
def TreeClaims (κ : ℕ) (q : Stack) (h : Digest) (out : TreeOut) : Prop :=
  (∀ c ∈ treeCols κ h out, ColTrue (κ + 6) q c) ∧ SlicesTrue6 (κ + 6) q out.en.pt out.en.s

/-- The lengths of the tree batch's output. -/
def TreeShape (κ : ℕ) (out : TreeOut) : Prop :=
  out.δ.length = 4 ∧ out.ρ.length = κ - 1 ∧ out.dd.length = 8 ∧ out.o.length = 25 ∧
    out.hd.sl.length = 6 ∧ ClaimShapeF (κ - 4) out.hd.claim ∧ out.hd.ϱm.length = 6 ∧
    out.en.ϱ.length = 11 ∧ out.en.pt.length = κ + 6 ∧ out.en.s.length = 64

/-- **The claims the sponge caller leaves** (`h` row bits, `nt` tied lanes): the middle word
claim `sp̃(r, ϱm) = c_out`, the 64 slice claims, the tied lanes' claims at `r`. -/
def SpongeClaims (h nt : ℕ) (sp : ℕ → K) (Y : ℕ → ℕ → K) (out : SpOut) : Prop :=
  ColTrue (h + 6) sp (out.1 ++ out.2.2.1.ϱm, out.2.2.1.cout) ∧
    SlicesTrue6 (h + 6) sp out.2.2.2.pt out.2.2.2.s ∧
    ∀ l < nt, stepMleK h out.1 (Y l) = out.2.1.getD l 0

/-- The lengths of the sponge caller's output. -/
def SpongeShape (h : ℕ) (out : SpOut) : Prop :=
  out.1.length = h ∧ out.2.1.length = 25 ∧ out.2.2.1.sl.length = 6 ∧
    ClaimShapeF (h - 4) out.2.2.1.claim ∧ out.2.2.1.ϱm.length = 6 ∧ out.2.2.2.ϱ.length = 10 ∧
    out.2.2.2.pt.length = h + 6 ∧ out.2.2.2.s.length = 64

/-! ## The frozen phase statements -/

/-- **T2, `treeSpec`** (statement): the tree batch of `2^κ` rows, from doom of `TreeOkG ∧ R` to
doom of the claims it leaves and `R`; lead `0`; every group `≤ εS` at one candidate; the
follower's lead `T` after the slices. -/
def TreeSpecStmt (κ : ℕ) : Prop :=
  ∀ {β : Type} [Finite β] (C : List Ev → Set β), Stable C → (∀ hh, (C hh).ncard ≤ 1) →
    ∀ (stk : β → Stack) (h : Digest) (R : β → Prop) (T : ℝ≥0∞), T ≤ εS →
      Nonempty (Spec (treeProg κ) (Doomed C (fun q ↦ TreeOkG κ (stk q) h ∧ R q))
        (fun out hist ↦ TreeShape κ out ∧
          Doomed C (fun q ↦ TreeClaims κ (stk q) h out ∧ R q) hist) εS 0 T)

/-- **The sponge caller** (statement): `spCaller6 h` with `nt ≤ 25` tied lanes, from doom of
season 1's sponge relation (`RegionValid`, `OutRel`) and `R` to doom of `SpongeClaims` and `R`;
lead `0`; every group `≤ εS`; the follower's lead `T` after the slices. -/
def SpongeSpecStmt (h nt : ℕ) : Prop :=
  ∀ {β : Type} [Finite β] (C : List Ev → Set β), Stable C → (∀ hh, (C hh).ncard ≤ 1) →
    ∀ (sp : β → ℕ → K) (Y : β → ℕ → ℕ → K) (R : β → Prop) (T : ℝ≥0∞), T ≤ εS →
      Nonempty (Spec (spCaller6 h)
        (Doomed C (fun q ↦ RegionValid h (sp q) ∧ Lvm.KG.OutRel h nt (sp q) (Y q) ∧ R q))
        (fun out hist ↦ SpongeShape h out ∧
          Doomed C (fun q ↦ SpongeClaims h nt (sp q) (Y q) out ∧ R q) hist) εS 0 T)

/-! ## The bridge to WP S's statement layer (`Lvm6StmtPhase`) -/

/-- **The 13 column claims in FORMAT6 §6.5's order** (WP ORD; claims 2–14 once claim 0 and the
ring claim 1 are placed): `c_out`, the eight wiring claims (slot `0 … 7`), the four root claims.
`treeCols` with its last claim (`c_out`) moved to the front (`treeColsS_perm`). -/
def treeColsS (κ : ℕ) (h : Digest) (out : TreeOut) : List SClaim :=
  ((out.u :: out.ρ) ++ out.hd.ϱm, out.hd.cout) ::
    ((List.range 4).map (fun m ↦ (out.ρ ++ [0] ++ bitsF m 6,
        out.dd.getD m 0 + eqAtF out.ρ 0 * kF (out.δ.getD m 0))) ++
      (List.range 4).map (fun m ↦ (out.ρ ++ [0] ++ bitsF (4 + m) 6, out.dd.getD (4 + m) 0)) ++
      (List.range 4).map (fun m ↦ (bitsF 0 κ ++ bitsF (4 + m) 6, kF (K.ofLane (dLane h m)))))

theorem treeColsS_perm (κ : ℕ) (h : Digest) (out : TreeOut) :
    (treeColsS κ h out).Perm (treeCols κ h out) :=
  (List.perm_append_singleton _ _).symm

/-- The tree batch's output as WP S's `TreeOut`: the 64 slices, and the 13 column claims with the
weights `eq(pt, ·)`, in FORMAT6 §6.5's order (`treeColsS`; WP ORD). -/
def toS (κ : ℕ) (h : Digest) (out : TreeOut) : Lvm6.TreeOut :=
  ⟨⟨out.en.pt, fun z ↦ out.en.s.getD z 0⟩, (treeColsS κ h out).map fun c ↦ (fun pt ↦ eqPt c.1 pt, c.2)⟩

/-- **The tree phase in WP S's form**: `treeProg (logN + 1)` with its output mapped by `toS`; it
fails outside the shapes it serves (`M = logN + 7`, `logN ≥ 4`; `P18` has `18`, `25`). -/
def treeProgS (sh : Lvm6.Shape) (x : Lvm6.Hdr) : VerifierProgram Lvm6.TreeOut :=
  if sh.M = sh.logN + 7 ∧ 4 ≤ sh.logN then
    treeProg (sh.logN + 1) >>= fun out ↦ pure (toS (sh.logN + 1) x.h out)
  else VerifierProgram.fail

/-- **The bridge** (statement): `treeSpec` at every `κ ≥ 5` gives S's `Stmt.treeSpec treeProgS`. -/
def TreeBridgeStmt : Prop := (∀ κ, 5 ≤ κ → TreeSpecStmt κ) → Stmt.treeSpec treeProgS

end Lvm6.K
