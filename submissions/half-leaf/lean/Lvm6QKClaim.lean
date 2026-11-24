-- New for lvm6 (WP CB). The interface between CB's layer gadget and its neighbours: how the node
-- circuit carries a Keccak GKR claim (value, `μ`, point, and its 1600 weights kept structured), and
-- the frozen HAR statements of one layer and of the two input ends (`docs/lvm6/stages/CB-circuit.md`).
import Lvm6QKMid

/-!
# A Keccak claim in the circuit (CB, frozen interface)

The circuit never writes a claim's `1600` weights (season 1's WP-0: ≈ 9 k rows a layer). It keeps
what they are made of (`WRep`):

* `first rl`: leanVM's first claim, `firstWeightsF r_lane` (`weights_{64ℓ+z} = eq(r_lane, ℓ)·x^z`),
  carried by the cells of `r_lane` (the head's lane table is the gadget's business);
* `lt pos β`: the claim after a layer, `linearTransposeF (batchWF pos β)` (K0's `layerTailE2N`),
  carried by the cells of the 11 position challenges and `β`.

**`ClaimRep M o cl`**: the cells `o` represent the claim `cl` (value, `μ`, point, weights).

Frozen statements (generators as arguments, as `Lvm6QKStmt`):
* **`LayerHarStmt G`**: `G κ step q claim gate` re-executes K0's `layer6 κ step` (FORMAT6 §6.2 row 8,
  items `P18.layer κ`, lanes from `q`) on a represented claim and hands on a represented claim.
* **`TreeEndHarStmt G`**: `G κ q claim gate` re-executes `treeEnd6 (κ−4)` (row 10, `treeEndItems`) on
  a represented claim (`lt` weights, point of `κ − 3` coordinates) and hands on the end's cells.
* **`SpEndHarStmt G`**: the same for the sponge's `spongeEnd6 (h−4)` (§6.3).
-/

set_option autoImplicit false

namespace Lvm6.QK

open LeanVM.Parameters LeanVM.Protocol.Compile LeanVM.Protocol.Verifier
open LeanVM.Protocol.KeccakGkr (Shape)
open Lvm Lvm.Loop Lvm.Loop.Build Lvm.Q2 Lvm.Har Lvm.E2V Lvm6.K Lvm6.KPack
open Lvm6 (Item rep rnd)

/-- How a claim's weights are carried. -/
inductive WRep where
  /-- leanVM's first claim, from the lane point's cells. -/
  | first (rl : List C2)
  /-- After a layer: `linearTransposeF (batchWF pos β)`. -/
  | lt (pos : List C2) (β : C2)

/-- The weights the cells stand for. -/
def wOf (M : Mem) : WRep → List E2
  | .first rl => firstWeightsF (rl.map (ev2 M))
  | .lt pos β => linearTransposeF (batchWF (pos.map (ev2 M)) (ev2 M β))

/-- **A claim in the circuit.** -/
structure ClaimC where
  value : C2
  mu : List C2
  point : List C2
  w : WRep

/-- **The cells represent the claim.** -/
def ClaimRep (M : Mem) (o : ClaimC) (cl : KClaim E2) : Prop :=
  ev2 M o.value = cl.value ∧ o.mu.map (ev2 M) = cl.mu ∧ o.point.map (ev2 M) = cl.point ∧
    wOf M o.w = cl.weights

/-- The items of the tree's input end (§6.2 row 10). -/
def treeEndItems : List Item := rep 11 (rnd 2 2) ++ [.E 64]

/-- The items of the sponge's input end (§6.3). -/
def spEndItems : List Item := rep 10 (rnd 2 2) ++ [.E 64]

/-- **One layer** (statement): for `κ ≥ 5`, `step < 12`, with the gate on and the claim represented
(point of `κ − 3` coordinates), the gadget re-executes `layer6 κ step` and represents the next claim
(with `lt` weights). -/
def LayerHarStmt (G : ℕ → ℕ → ℕ → ClaimC → Cell → BM ClaimC) : Prop :=
  ∀ κ, 5 ≤ κ → ∀ step, step < 12 → ∀ (q : ℕ) (claim : ClaimC) (gate : Cell) (c : Ctx) (M : Mem),
    gate.val M = 1 → claim.point.length = κ - 3 → ∀ cl : KClaim E2, ClaimRep M claim cl →
      HsA c M (G κ step q claim gate) fun o ↦
        Runs M (layItems (P18.layer κ) q) (layer6 κ step cl)
          (fun cl' ↦ ClaimRep M o cl' ∧ o.point.length = κ - 3 ∧ ∃ pos β, o.w = .lt pos β)

/-- **The tree's input end** (statement). -/
def TreeEndHarStmt (G : ℕ → ℕ → ClaimC → Cell → BM (List C2 × List C2 × List C2)) : Prop :=
  ∀ κ, 5 ≤ κ → ∀ (q : ℕ) (claim : ClaimC) (gate : Cell) (c : Ctx) (M : Mem),
    gate.val M = 1 → claim.point.length = κ - 3 → (∃ pos β, claim.w = .lt pos β ∧ pos.length = 11) →
      ∀ cl : KClaim E2, ClaimRep M claim cl →
        HsA c M (G κ q claim gate) fun o ↦
          Runs M (layItems treeEndItems q) (treeEnd6 (κ - 4) cl)
            (fun en ↦ o.1.map (ev2 M) = en.ϱ ∧ o.2.1.map (ev2 M) = en.pt ∧ o.2.2.map (ev2 M) = en.s)

/-- **The sponge's input end** (statement). -/
def SpEndHarStmt (G : ℕ → ℕ → ClaimC → Cell → BM (List C2 × List C2 × List C2)) : Prop :=
  ∀ h, 5 ≤ h → ∀ (q : ℕ) (claim : ClaimC) (gate : Cell) (c : Ctx) (M : Mem),
    gate.val M = 1 → claim.point.length = h - 3 → (∃ pos β, claim.w = .lt pos β ∧ pos.length = 11) →
      ∀ cl : KClaim E2, ClaimRep M claim cl →
        HsA c M (G h q claim gate) fun o ↦
          Runs M (layItems spEndItems q) (spongeEnd6 (h - 4) cl)
            (fun en ↦ o.1.map (ev2 M) = en.ϱ ∧ o.2.1.map (ev2 M) = en.pt ∧ o.2.2.map (ev2 M) = en.s)

end Lvm6.QK
