-- New for lvm6 (WP NODE). The node circuit's generator in `prog6`'s order: the families that read only the
-- child's stream lanes and the node's `PUB` lanes (CB's tree, sponge caller and link, CD's typed phases),
-- placed at their stream lanes, and the composed HAR. CA's `Q_link`/`Q_sig`, the PoW rows and CC's opening
-- gadgets are marked slots (below).
import Lvm6QDCompose
import Lvm6QKTree
import Lvm6QKLink
import Lvm6QCWhir
import Lvm6NodeStmt

/-!
# The node circuit's generator (`node6E`) and its HAR (`node6E_har`)

**Lanes.** A part of `sched6 P17` that follows the items `pre` starts in the buffer of chain entry
`2 + queriesOf pre` (entries 0 and 1 are `q₀` and the seed), whose query starts at stream word
`eLane6 P6 i + 1`, its buffer at `eLane6 P6 i + 5` (length word and the previous answer), after the lanes
still pending from `pre` (`pendL`: `E k` 2k lanes, `K k` k lanes, a cap `4·2^lv` lanes; a draw flushes).
`partLane pre` is that lane. Within a part without caps or openings the items are contiguous (`layEnd`).

**Order** (`prog6`: commit, tree, sponge, typed, ring, opening):
1. commit (`CAP(0)`, `B`, `G D`, `E(1)`): lanes only, no rows.
2. tree `treeG6 18` at `aTree`; 3. sponge caller `spG6 13` at `aSp`, link `ksLinkG6 13 10 3816 7567 8032` at
   `aLink = layEnd (spItems 13) aSp`; 4. typed `ty6` at `aTy`.
5. ring (`ringGen`), opening rounds (`roundsGen`): CC's transcript gadgets place no rows.
- **SLOT `qlink6`/`qsig6`/`sigLeafCopy6`** (CA, CD): need the `K` input regions `QLT` (`CONST`), the `BITS`
  outputs (aux rows) and the `KS` aliases of the node's own sponge rows (`I.xs`, `I.ys`, `I.md`); not placed yet.
- **SLOT PoW rows** (`PowLay` of every family: one range check per ground draw, season 1's `powBlk`).
- **SLOT CC `posG`/`valsG`/final level/claim batch** (W1's deployed `TailIface`; CC-8).
The gate is the node flag `b` (`PUB` lane 1).
-/

set_option autoImplicit false

namespace Lvm6.Node

open Lvm Lvm.Loop Lvm.Loop.Build Lvm.Q2 Lvm.Har Lvm.E2V
open Lvm6.Q (eLane6)
open Lvm6.QK
open Lvm6.QD
open Lvm6.Ty (TInst6 typedProgE typedClaimsE phiVarsE PhiQE)
open Lvm6.Mb (mbClaimsG)
open Lvm6.K (treeProg spCaller6)

/-! ## Lanes -/

/-- The lanes still pending in the buffer after the items (`E k`: `2k`, `K k`: `k`, a cap: `4·2^lv`; any draw
flushes). -/
def pendL (L : List V.Lev) : List V.Item → ℕ → ℕ
  | [], n => n
  | .E k :: r, n => pendL L r (n + 2 * k)
  | .K k :: r, n => pendL L r (n + k)
  | .cap i :: r, n => pendL L r (n + 4 * 2 ^ (L.getD i default).lv)
  | _ :: r, _ => pendL L r 0

/-- **The stream lane of the first item of the part after `pre`** (in `sched6 P17`). -/
def partLane (pre : List V.Item) : ℕ :=
  eLane6 P6 (2 + V.queriesOf P17.levs pre) + 5 + pendL P17.levs pre 0

/-- The tree part's first lane. -/
def aTree : ℕ := partLane P17.commitPart

/-- The sponge caller's first lane. -/
def aSp : ℕ := partLane (P17.commitPart ++ P17.treePart)

/-- The sponge link's first lane (contiguous after the caller and the core). -/
def aLink : ℕ := layEnd (spItems 13) aSp

/-- The typed phases' first lane (CD's `aTy`). -/
def aTy : ℕ := partLane (P17.commitPart ++ P17.treePart ++ P17.spongePart)

/-! ## The generator -/

/-- What the composed families hand on. -/
structure NodeOutE where
  tree : TreeOutC
  sp : SpOutC
  link : LinkOutC
  ty : TyOutC

/-- **The node circuit's stream families** in `prog6`'s order (slots: module doc). -/
def node6E (Ti : TInst6) (pubC : ℕ → Cell) (ain : List C2) (yIn : C2) (own : List C2) (ownY : C2)
    (gate : Cell) : BM NodeOutE :=
  treeG6 18 aTree gate >>= fun t ↦ spG6 13 aSp gate >>= fun s ↦
    ksLinkG6 13 10 3816 7567 8032 aLink gate >>= fun l ↦
      ty6 Ti pubC ain yIn own ownY aTy gate >>= fun y ↦ pure ⟨t, s, l, y⟩

/-! ## The composed HAR -/

variable {c : Ctx} {M : Mem}

/-- **The families re-execute the child's phases** (CB-1, CB-2, CB-3, CD's `ty6_har`): with the gate on,
where the rows and gated assertions hold, the tree program, the sponge caller and the link return on every
matching event list with grinds passing (outputs = the gadgets' cells), and the typed conclusion of
`ty6_har` holds at `aTy`. -/
theorem node6E_har (Ti : TInst6) (hok : Ti.Ok) (hlay : TyLayOk Ti) (L : Lvm.M3.Lay) (pubC : ℕ → Cell)
    (ain : List C2) (yIn : C2) (own : List C2) (ownY : C2) (hain : ain.length = phiVarsE)
    (hown : own.length = phiVarsE) (gate : Cell) (hg : gate.val M = 1) :
    HsA c M (node6E Ti pubC ain yIn own ownY gate) fun o ↦
      Runs M (layItems (treeItems 18) aTree) (treeProg 18) (TreeRep M o.tree) ∧
      Runs M (layItems (spItems 13) aSp) (spCaller6 13) (SpRep M o.sp) ∧
      Runs M (layItems (linkItems 13) aLink) (ksLinkProgE2 13 10 (rowsBK2 3816 7567 8032)) (LinkRep M o.link) ∧
      (accOut6 (ain.map (ev2 M), ev2 M yIn) (gdraws M (aA aTy) 2) ((o.ty.zero.rx ++ o.ty.wire.ry).map (ev2 M))
          (scal M (aA aTy + 20) (phiVarsE + 1)) (ev2 M (ld2 (aA aTy + 20 + 2 * (phiVarsE + 1) + 1))) =
        (own.map (ev2 M), ev2 M ownY) ∧
      (PhiQE Ti.Q Ti.lay (own.map (ev2 M)) = ev2 M ownY →
        Runs M (layItems (tyItems ++ mbItems) aTy)
          (typedProgE Ti L (fun y ↦ ((pubC y).val M).c₀) (ain.map (ev2 M), ev2 M yIn))
          (fun out ↦ out = typedClaimsE Ti (o.ty.wire.ry.map (ev2 M)) (o.ty.wire.rv.map (ev2 M))
            (o.ty.relay.rr.map (ev2 M)) (ev2 M o.ty.relay.vR)
              ((mbClaimsG L.nuMain Ti.mbT (busOf M o.ty.mb)).map (·.onStack))))) := by
  unfold node6E
  refine hsA_bind (treeHar 18 (by norm_num) aTree gate c M hg) fun t ht ↦ ?_
  refine hsA_bind (spHar 13 (by norm_num) aSp gate c M hg) fun s hs ↦ ?_
  refine hsA_bind (linkHar 13 10 3816 7567 8032 (by norm_num) (by norm_num) (by norm_num) aLink gate c M hg)
    fun l hl ↦ ?_
  refine hsA_bind (ty6_har Ti hok hlay L pubC ain yIn own ownY hain hown aTy gate hg) fun y hy ↦ ?_
  exact hsA_pure ⟨ht, hs, hl, hy⟩

end Lvm6.Node
