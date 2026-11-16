-- New for lvm (WP-14a): the P20 commitment table of the compiled verifier and the relations between
-- V_S's claims (`FE`) and the verifier language's (`E`), shared by the per-phase refinements.
import LvmVEqPrim
import LvmVEqMid
import LvmVEqCore

-- ===== merged from `LvmVEqPhases` (GOLF module merge: `LvmVEqPhases.lean` is now a stub importing `LvmVEqRel`) =====
section
-- New for lvm (WP-14a): V_S's decision program (`LvmDecide.decideProg`) cut into its phases, each
-- a native step of its own, so that each phase's refinement is a lemma of its own.

/-!
# `decideProg` by phases

`decideProg p m vk c = decidePhases p m vk c` (`decideProg_eq`, by `rfl`): the header's public
values, the two caps skipped (`dCommit`), then

* `dBus p m pub` (phase 2): `α`, `β`, the grand-product GKR, `count ≠ 0`, the leaf-decomposition
  scalars, `busFinal`, `require bus.ok`; returns the GKR point and the bus result;
* `dTab p m pub point bus` (phase 3): `ξ`, the table sumcheck; the evaluations; then AC-V's
  `accFold` (phase 3b, A23): `PUB`'s check, `κ`, `h`, `t`, the zero scalar; the folded accumulator;
* `dKec h` (phases 4 and 6): the instance point, the 25 lanes, the Keccak GKR, the ring switch;
* `dTape`, `dWire` (lvm2 S2, phases 4–5, `LvmDecideTape`); `dChLink` (v1's phase 5) is kept but
  unused; `dKsLink p m rk pub` (phase 7): the `KS` link, `require ok`; its claims;
* `dOpen p claims` (phases 8–9): the two stacked openings of the claims, per commitment;
  `decidePhases` returns phase 3b's accumulator (A23).
-/

set_option autoImplicit false

namespace Lvm.VEq

open Lvm DM

/-- The two caps (phase 1). -/
def dCommit (p : Params) : DM Unit := do
  skip (nodeBytes * 2 ^ (p.level ⟨.main, 0⟩).cap)
  skip (nodeBytes * 2 ^ (p.level ⟨.crec, 0⟩).cap)

/-- The bus (phase 2): the GKR point and the bus result. -/
def dBus (p : Params) (m : M3) (pub : Pub) : DM (List FE × BusOut) := do
  let alphas ← samples busBits
  let beta ← sampleE
  let (countRoot, point, values) ← verifyGkrGrandProducts p.busDepth
  require (countRoot != 0)
  let leafdec ← readEs p.leafdecReads
  let bus := m.busFinal ⟨alphas, beta, countRoot, point, values, leafdec, pub⟩
  require bus.ok
  pure (point, bus)

/-- The tables (phase 3): the tables' points and evaluations (A23: no fixed-column check here;
phase 3b, `accFold`, folds them into the accumulator). -/
def dTab (p : Params) (m : M3) (pub : Pub) (point : List FE) (bus : BusOut) :
    DM (List (List FE × List FE)) := do
  let xi ← sampleE
  let tables := m.tables pub
  let nC := (tables.map (·.nConstraints)).sum
  let xiPowers := powers xi (nC + 3)
  let formPowers := xiPowers.drop nC
  tableSumcheck p.tableRounds tables bus.forms (xiPowers.take nC) formPowers
    point (dot formPowers bus.totals)

/-- A Keccak table with its caller's lanes (phases 4 and 6). -/
def dKec (h : Nat) : DM (List FE × List FE × KeccakOut × (FE × (List FE → FE))) := do
  let r ← samples h
  let v ← readEs lanes
  let ko ← verifyKeccak h r v
  let ring ← ringSwitch ko.slicePoint ko.slices
  pure (r, v, ko, ring)

/-- The `CH` link (phase 5): its claims. -/
def dChLink (p : Params) (m : M3) (r v : List FE) (pub : Pub) : DM (List (Com × BlockClaim)) := do
  let chal ← samples (p.logN + 3 + 6)
  let shift ← sumcheck (m.chShiftTarget chal) 3 (List.replicate p.logN none)
  let inS ← readEs kBits
  let ringIn ← ringRaw inS
  let sc2 ← sumcheck (m.chSc2Target chal shift inS) 3 [none, none]
  let yS ← readEs kBits
  let ringY ← ringRaw yS
  let constLanes ← samples laneBits
  let (okL, linkClaims) := m.chLink ⟨chal, shift, inS, ringIn, sc2, yS, ringY, constLanes, r, v, pub⟩
  require okL
  pure linkClaims

/-- The `KS` link (phase 7): its claims. -/
def dKsLink (p : Params) (m : M3) (rk : List FE) (pub : Pub) : DM (List (Com × BlockClaim)) := do
  let kchal ← samples (p.ksLog + laneBits)
  let kshift ← sumcheck (m.ksShiftTarget kchal) 3 (List.replicate p.ksLog none)
  let kvals ← readEs 4
  let (okK, kLinkClaims) := m.ksLink ⟨kchal, kshift, kvals, rk, pub⟩
  require okK
  pure kLinkClaims

/-- The openings (phases 8–9). -/
def dOpen (p : Params) (claims : List (Com × BlockClaim)) : DM Unit := do
  let on (com : Com) := (claims.filter (·.1 == com)).map (·.2.onStack)
  verifyStackedOpening p.recLevels p.nuRec (on .crec) false p.grind p.recOod
  verifyStackedOpening p.mainLevels p.nuMain (on .main) false p.grind p.mainOod

/-- The claims of phases 2–7 (`decideProg`'s list; lvm2 S2: the tape's claims in place of `CH`'s
and the `CH` link's). -/
def dClaims (m : M3) (p : Params) (pub : Pub) (bus : BusOut) (evals : List (List FE × List FE))
    (tp : TapeRes) (wo : WireOut)
    (ks : List FE × List FE × KeccakOut × (FE × (List FE → FE)))
    (kLinkClaims : List (Com × BlockClaim)) : List (Com × BlockClaim) :=
  bus.claims ++ m.tableClaims pub evals ++
    (tapeClaims p tp wo pub ++ keccakClaims m.ksBlock ks.2.2.1 ks.2.2.2).map (.main, ·) ++
    m.ksOutputClaims ks.1 ks.2.1 ++ kLinkClaims

/-- The claims of phases 2–7 with their tail values (roll 7, SH2-Z; `dClaimsZ`; `dClaimsT_fst`: without
the tails they are `dClaims`). -/
def dClaimsT (m : M3) (p : Params) (pub : Pub) (bus : BusOut) (evals : List (List FE × List FE))
    (tp : TapeRes) (wo : WireOut × List FE)
    (ks : List FE × List FE × KeccakOut × (FE × (List FE → FE)))
    (kLinkClaims : List (Com × BlockClaim)) : List (Com × BlockClaim × FE) :=
  Shape.dClaimsZ m p pub bus.claims evals tp wo.1 wo.2 ks.1 ks.2.1 (keccakClaims m.ksBlock ks.2.2.1 ks.2.2.2)
    kLinkClaims

/-- **`decideProg` by phases** (its value: phase 3b's folded accumulator). -/
def decidePhases (p : Params) (m : M3) (vk c : Vector UInt8 32) : DM Acc := do
  let sig ← read
  let pub := pubOf vk c sig
  dCommit p
  let pb ← dBus p m pub
  let evals ← dTab p m pub pb.1 pb.2
  let accOut ← accFold p m pub evals
  let tp ← dTape p.logN
  dRange p pub
  let wo ← Shape.dWireC p pub tp.claim
  let ks ← dKec p.ksLog
  let kLinkClaims ← dKsLink p m ks.1 pub
  Shape.dOpenZ p (Shape.smallP p pub) (dClaimsT m p pub pb.2 evals tp wo ks kLinkClaims)
  pure accOut

/-- `decideProg` is its phases. -/
theorem decideProg_eq (p : Params) (m : M3) (vk c : Vector UInt8 32) :
    decideProg p m vk c = decidePhases p m vk c := by
  simp only [decideProg, decidePhases, dCommit, dBus, dTab, dKec, dKsLink, dClaimsT,
    bind_assoc, pure_bind]

end Lvm.VEq
end
-- ===== end of `LvmVEqPhases` =====

/-!
# P20's commitments; native and language claims

* `capS` (= WP-14's `capOfS`: cap level 8 for `C_main`'s root of `2^19` leaves (lvm2 S2), 7 otherwise),
  `shpS` (M′: the three commitments in commit order, `C_main`'s root `(19, 64)` and its levels 1–2
  `(16, 48)`, `(13, 48)`), `idxS` (an oracle's commitment index);
* `BCRel c c'`: a native block claim and a language block claim (`LvmVEqMid.BClaim`) agree: same
  block, value and weight through `FE.toExt3` (the weight on every image point);
  `CRel` with the commitment; `SCRel` for stack claims.
-/

set_option autoImplicit false

namespace Lvm.VEq

open Lvm

/-- The cap level of a tree of `2^ht` leaves at P20 (WP-14's `capOfS`). -/
def capS (ht _w : ℕ) : ℕ := if ht = 19 then 8 else 7

/-- The occupied words of a commitment of `2^ht` rows of `w` words at P20 (`LvmCertS.occOfS`): `47`
for `C_main`'s root (both shapes; M′ `S2GM`, B1 had 46), `35` for `C_rec`'s (B1 only; unused at M′), the whole
row otherwise. -/
def occS (ht w : ℕ) : ℕ := if ht = 19 ∧ w = 64 then 47 else if ht = 15 ∧ w = 64 then 35 else w

/-- The three commitments' shapes `(height, width)` in commit order at P20 (lvm2 roll 11, M′ `S2GM`: one
commitment, `C_main`'s root and its WHIR levels 1–2; B1 had `C_rec`'s root and level 1 at 1, 2). -/
def shpS : ℕ → ℕ × ℕ
  | 0 => (19, 64)
  | 1 => (16, 48)
  | _ => (13, 48)

/-- An oracle's commitment index (M′: `C_main`'s level `j` at `j`, WHIR's `cidx` with `n₀ = 1`; `C_rec` has no
oracle at M′, its references are sent past the table). -/
def idxS : Ref → ℕ
  | ⟨.main, j⟩ => j
  | ⟨.crec, j⟩ => j + 100 -- unreachable at M′: no `C_rec` item is left in the schedule

/-- Refinement at P20's commitment table. -/
abbrev Ref20 {α β : Type} (sig : ByteArray) (d : DM β) (P : LeanVM.Protocol.Compile.VerifierProgram α)
    (R : β → α → Prop) : Prop := RefAt capS occS shpS sig d P R

/-- A native block claim and a language block claim agree. -/
def BCRel (c : Lvm.BlockClaim) (c' : BClaim) : Prop :=
  c'.block = ⟨c.block.variableCount, c.block.index⟩ ∧ c'.value = FE.toExt3 c.value ∧
    ∀ xs : List FE, c'.weight (xs.map FE.toExt3) = FE.toExt3 (c.weight xs)

/-- With the commitment. -/
def CRel (a : Com × Lvm.BlockClaim) (b : Com × BClaim) : Prop := a.1 = b.1 ∧ BCRel a.2 b.2

/-- A native stack claim and a language stack claim agree. -/
def SCRel (c : Lvm.StackClaim) (c' : VStackClaim) : Prop :=
  c'.2 = FE.toExt3 c.2 ∧ ∀ xs : List FE, c'.1 (xs.map FE.toExt3) = FE.toExt3 (c.1 xs)

end Lvm.VEq
