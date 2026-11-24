-- New for lvm6 (WP CC8). The frozen statements of the final WHIR level in the node circuit (CC-8):
-- the re-execution of W1's `finP` at `chalE2` with the deployed terminal check `chkE` (the tail
-- sumcheck), the weight at the final point as a cell (NODE §6a: `wFinG`), and the glue step that
-- builds that cell level by level (`docs/lvm6/stages/CC-circuit.md`, "CC8").
import Lvm6QCStmt
import Lvm6WhirWok

/-!
# CC-8's frozen statements

**Layout** (FORMAT6 v2.2.1 §6.6, `i = 4`, W1's `finP` order, CC's lane conventions): from lane `a`,
`ℓ` fold rounds (27 lanes each), the final polynomial's `nf` scalars `E(nf)`, the query group
`G(gq) D(kq)`, the `t` openings of `lev` at width `wdI` (cursor `finOpenAt`, first leaf word at
`cursor − 4`, as `layTail`), then the `κ` tail rounds `R(2, gT)` (14 lanes each) from
`cursor + t·openStride lev` (CC §2's lane after the openings).

**The gadgets the statement takes** (as CC-3 takes `posG`, `valsG`):
* `posG` meets `PosOK Fv.pos` (CC-3a's form);
* `fvG rc` meets `ValsAt` for the verifier's row fold `fv rs` (no high part: `hi` is ignored),
  whenever the cells `rc` represent the rounds `rs`;
* `fpG` meets `FpAt Fv`: the final polynomial `fpoly s` at the positions' domain points;
* `wG` meets `WAt Pre w` (**NODE §6a's `wC`**): on memories with `Pre`, from cells of the level's
  rounds and of the tail challenges `τ` (`w.1` of them), its output is the folded weight's table at `τ`, i.e.
  `chkE`'s `Φ(τ)`. `Pre` carries what the cell needs from the earlier levels (their cells represent
  their outputs), so the ghost weight `w` of `finP` is replaced by a cell.

**The statements**:
* `FinHarStmt Fv G` (**CC-8**): `G posG fvG fpG wG g gT κ ℓ lev wdI a σc gate` re-executes
  `finP WtE chalE2 Fv g gq i ℓ fv (chkE gT κ) w σ` on `layFin`, and on memories with `Pre` whose
  cell `σc` holds the claim `σ`, the program returns `true`.
* `WhAt κ whG`: a gadget giving `Ŵ_i(K(x))` for `i < κ` at a position cell `x` (CC-3b's table).
* `WGlueStmt G` (**CC-8g**, the glue step of `wFinG`): from a weight gadget `wGp` for an admitted
  weight `w` of a level (`wokE`), a `Ŵ` gadget and the cells of that level's rounds and interface,
  `G wGp whG rcP oc` is a weight gadget for the next level's weight `wGlueE … (wFolds ℓ rs w) o`.

Category A (CC8): `layFin`, `finOpenAt`, `FinOutC`, `FpAt`, `WAt`, `WhAt` and the statements;
`finP`, `chkE`, `fvE`, `WtE`, `wGlueE`, `wokE` are W1's.
-/

set_option autoImplicit false

namespace Lvm6.QC

open LeanVM.Parameters LeanVM.Protocol.Compile LeanVM.Protocol.Verifier LeanVM.Protocol.Whir
open Lvm Lvm.Loop Lvm.Loop.Build Lvm.Q2 Lvm.Har Lvm.E2V Lvm6.QK
open Lvm6 (Item Level rep rnd)

/-! ## Geometry -/

/-- The final level's openings' cursor: the lane after the query group. -/
def finOpenAt (nf kq ℓ a : ℕ) : ℕ := a + 27 * ℓ + 2 * nf + 10 + 9 * kq

/-- **The final level's slots** from lane `a`: `ℓ` fold rounds, `E(nf)`, `G(gq) D(kq)`, the `t`
openings, the `κ` tail rounds `R(2, gT)`. -/
def layFin (nf kq t κ : ℕ) (lev : Level) (wdI g gq gT ℓ a : ℕ) : List OEv :=
  layRounds g ℓ a ++ bl (layItems [.E nf, .G gq, .D kq] (a + 27 * ℓ)) ++
    [.o (openRows lev wdI (finOpenAt nf kq ℓ a - 4) t)] ++
    bl (layItems (rep κ (rnd 2 gT)) (finOpenAt nf kq ℓ a + t * openStride lev))

/-- The final level's cells: the rounds, the scalars, the positions, the tail challenges. -/
structure FinOutC where
  rc : List RndC
  s : List C2
  ps : List Cell
  tau : List C2

/-! ## The gadgets -/

/-- **A final-polynomial gadget**: from the scalars' cells and the position cells, the final
polynomial `fpoly s` at the positions' domain points. -/
def FpAt {n : ℕ} (Fv : Whir.FinIface E2 n) (G : List C2 → List Cell → Cell → BM (List C2)) :
    Prop :=
  ∀ (c : Ctx) (M : Mem) (sc : List C2) (ps : List Cell) (gate : Cell), gate.val M = 1 →
    HsA c M (G sc ps gate) fun fs ↦ ∀ p : Fin Fv.t → Fin n,
      posOf M ps = List.ofFn (fun k ↦ (p k : ℕ)) →
        fs.map (ev2 M) = List.ofFn fun k ↦ (Fv.fpoly (sc.map (ev2 M)) Whir.lane0).eval (Fv.dom (p k))

/-- **A weight gadget** for the weight `w` on `ℓ` rounds, on memories with `Pre`: from cells
representing the `ℓ` rounds `rs` and cells `τ` for the weight's `w.1` remaining variables, the folded
weight's table at `τ`. (INT3: `τ.length = w.1` added. Over every `τ`, W1's level-0 weight `w₀`, which
reads its point through `padD`, and the claim gadgets at `τ ++ α₀` disagree for `τ.length ≠ 18`;
every call site uses `τ` of that length: the tail challenges of `finP` (`w.1 = κ`, `FinHarStmt`), the
glue's `α' ++ τ` (`wokE`'s `w.1 = ko + 1 = ℓ' + κ'`).) -/
def WAt {ℓ : ℕ} (Pre : Mem → Prop) (w : Whir.WtE.Wt (0 + ℓ))
    (G : List RndC → List C2 → Cell → BM C2) : Prop :=
  ∀ (c : Ctx) (M : Mem), Pre M → ∀ (rc : List RndC) (rs : List (Whir.Rnd E2)), RndsRep M rc rs →
    rs.length = ℓ → ∀ (τ : List C2), τ.length = w.1 → ∀ (gate : Cell), gate.val M = 1 →
      HsA c M (G rc τ gate) fun o ↦ ev2 M o = (Whir.wFolds Whir.WtE ℓ rs w).2 (τ.map (ev2 M))

/-- **A `Ŵ` gadget**: at a `K` cell `x`, the values `Ŵ_i(K(x))` for `i < κ`. -/
def WhAt (κ : ℕ) (G : Cell → Cell → BM (List C2)) : Prop :=
  ∀ (c : Ctx) (M : Mem) (x gate : Cell), gate.val M = 1 →
    HsA c M (G x gate) fun ws ↦ ws.map (ev2 M) =
      (List.range κ).map fun i ↦ algebraMap K E2 (normVanishingAt i (K.ofBits (kToNat (kv M x))))

/-! ## The frozen statements -/

/-- **CC-8, the final level** (statement): for the code facts `Fv`, the verifier's row fold `fv`,
and gadgets meeting `PosOK`, `ValsAt` (for `fv rs` when the cells represent `rs`), `FpAt` and
`WAt Pre w`, and a weight on the `κ` tail variables (`w.1 = κ`, INT3: `WAt` is now asked only at
points of `w.1` variables, here the `κ` tail challenges), the generator re-executes
`finP WtE chalE2 Fv g gq i ℓ fv (chkE gT κ) w σ` on `layFin`; on memories with `Pre` where `σc` holds
`σ`, the program returns `true`. -/
def FinHarStmt {n : ℕ} (Fv : Whir.FinIface E2 n)
    (G : ((Fin (Fv.kq + 1) → C2) → Cell → BM (List Cell)) →
      (List RndC → List Cell → List (List (Option ℕ)) → Cell → BM (List C2)) →
      (List C2 → List Cell → Cell → BM (List C2)) → (List RndC → List C2 → Cell → BM C2) →
      ℕ → ℕ → ℕ → ℕ → Level → ℕ → ℕ → C2 → Cell → BM FinOutC) : Prop :=
  ∀ (fv : List (Whir.Rnd E2) → (Fin Fv.t → Fin n) → List (List K) → Fin Fv.t → E2) posG fvG fpG
    (ℓ : ℕ) (w : Whir.WtE.Wt (0 + ℓ)) (Pre : Mem → Prop) wG,
    PosOK Fv.pos posG →
    (∀ c M rc rs, RndsRep M rc rs → ValsAt c M (fun _ ↦ fv rs) (fun _ ↦ fvG rc)) →
    FpAt Fv fpG → WAt Pre w wG →
    ∀ (g gq gT i κ : ℕ), g ≤ 64 → gq ≤ 64 → gT ≤ 64 → w.1 = κ →
    ∀ (lev : Level) (wdI a : ℕ) (σ : E2) (σc : C2) (gate : Cell),
      HarO gate (G posG fvG fpG wG g gT κ ℓ lev wdI a σc gate)
        (Whir.finP Whir.WtE Whir.chalE2 Fv g gq i ℓ fv (Whir.chkE gT κ) w σ)
        (layFin Fv.nf Fv.kq Fv.t κ lev wdI g gq gT ℓ a)
        fun M _ out ↦ Pre M → ev2 M σc = σ → out = true

/-- **CC-8g, the glue step of `wFinG`** (statement): for an admitted weight `w` of a level
(`wokE (ko + 1) ℓ`) with a weight gadget `wGp` on `Pre`, a `Ŵ` gadget for `ko + 1` values, and
cells `rcP`, `oc` of that level's rounds and interface, `G wGp whG rcP oc` is a weight gadget for
the next level's weight `wGlueE κ' ℓ' ko t h (wFolds ℓ rs w) o`, on the memories with `Pre` where
`rcP`, `oc` represent the `ℓ` rounds `rs` and the interface's output `o`. -/
def WGlueStmt (G : (List RndC → List C2 → Cell → BM C2) → (Cell → Cell → BM (List C2)) →
    List RndC → TailOutC → List RndC → List C2 → Cell → BM C2) : Prop :=
  ∀ (κ' ℓ' ko t h ℓ : ℕ), 0 + ℓ' + κ' = ko + 1 → ∀ (w : Whir.WtE.Wt (0 + ℓ)) (Pre : Mem → Prop)
    wGp whG, Whir.wokE (ko + 1) ℓ w → WAt Pre w wGp → WhAt (ko + 1) whG →
    ∀ (rcP : List RndC) (rs : List (Whir.Rnd E2)) (oc : TailOutC) (o : Whir.TailOut E2 ko t (2 ^ h)),
      rs.length = ℓ →
      WAt (ℓ := ℓ') (fun M ↦ Pre M ∧ RndsRep M rcP rs ∧ TailRep M oc o)
        (Whir.wGlueE κ' ℓ' ko t h (Whir.wFolds Whir.WtE ℓ rs w) o) (G wGp whG rcP oc)

end Lvm6.QC
