-- New for lvm2 (roll 8 = B1, L-H): roll 7's HAR helpers the typed HAR reuses (generic: they name no bus-program constant), split out of
-- `LvmQAsmHarMain` (unchanged text) so that the typed HAR (`LvmQTypedHar*`) reads them without the bus phases'
-- proofs: `PhaseAt` from `Replays`, the `E` constants, `M3.real` as `ofParts`, `n'`'s bits, the tape's claims and
-- their tails as cells, the claims with tails (`noDR`, `list_eq_of_proj`, `claimsT_proj`), the bus gadget's output
-- cells (`busV`, `busR_eq`, `busG_fst`, which the mini-bus reuses).
import LvmQAsmProg
import LvmQAsmHarBase
import RecursionFast.Library.Security
-- (GOLF2 import pruning: dropped LvmQAsmHarP47, LvmQShapeH: unused by this module.)

-- (GOLF2: 17 declarations that `certified` does not use moved verbatim to `LvmQTypedHarCOff`, outside its import closure.)

-- ===== merged from `LvmQAsmHarIn` (GOLF module merge: `LvmQAsmHarIn.lean` is now a stub importing `LvmQAsmHarTails`) =====
section
-- New for lvm (HAR): `harith`'s inputs: the node program's stream cells bind `Σ'` (the child's trace bytes),
-- the gate, and Q_arith's segments split into phases 4–7 and the rest.

set_option autoImplicit false

namespace Lvm.Har

open RecursionFast Lvm Lvm.Loop Lvm.Loop.Build Lvm.QLink Lvm.QAsm Lvm.Q1 Lvm.Replay

/-- **`Σ'` is the stream cells' bytes**: with Q_link's `LaneLink`, the child's trace bytes are `sigma`,
whose lanes the node program's stream cells hold (`InMapN.stream`). -/
theorem streamed_child (C : QCfg) {M : Mem} {ws : List Word} (hS : StreamOk C.p) (hL : LaneLink C.p ws)
    (hst : ∀ j < 2 ^ (lay C).m, M.k ((lay C).sb + j) = laneK ws j) {T : Nat} (hTm : T ≤ 2 ^ (lay C).m)
    (hT : 8 * T ≤ hashedLen C.p) (hl : T ≤ ws.length) :
    Streamed M (traceBytesB (decode C.p ws)) T := by
  rw [traceBytesB_decode hS hL]
  exact streamed_sigma C.p ws (N := 2 ^ (lay C).m) (fun j hj => by simpa [lay] using hst j hj) hTm hT hl

end Lvm.Har
end
-- ===== end of `LvmQAsmHarIn` =====

-- ===== merged from `LvmQAsmHarShape` (GOLF module merge: `LvmQAsmHarShape.lean` is now a stub importing `LvmQAsmHarTails`) =====
section
-- New for lvm (HAR): the shapes of the node program's tables do not depend on the closed forms of their
-- fixed columns (the cache `G`) nor on the public values (`PUB`'s contents): the circuit is built from
-- the shapes of one instance and `F` runs on another.

set_option autoImplicit false

namespace Lvm.Har

open Lvm Lvm.Loop Lvm.M3 Lvm.QAsm

/-- The sumcheck filter on shapes. -/
def TShape.sc (s : TShape) : Bool := !s.cons.isEmpty || !s.reads.isEmpty || !s.seeds.isEmpty

end Lvm.Har
end
-- ===== end of `LvmQAsmHarShape` =====

set_option autoImplicit false

namespace Lvm.Har

open Lvm Lvm.Loop Lvm.Loop.Build Lvm.Q1 Lvm.QAsm DM

/-- The `E` constant `k'` from any cell `x` (`x + 1·x + k'`). -/
theorem constE_val {c : Ctx} {M : Mem} {k' : FK} {x : Cell} {p : Ptr}
    (h : SegsHold c M p (const .E k' x p).2) : (const .E k' x p).1.val M = FE.ofK k' := by
  have e := lin_spec (c := c) (M := M) (p := p) (τ := .E) (k := 1) (k' := k') (a := x) (b := x) h
  show (lin .E 1 k' x x p).1.val M = _
  rw [e, ofK_one, one_mul, CharTwo.add_self_eq_zero, zero_add]

theorem bitE_out1 {v : Nat → FK} {w nb j : Nat} (hj : j < 64) (h : Lvm.QSig.Out1 v w (.bit j) (nb + j)) :
    FE.ofK (v (nb + j)) = bitE (v w).val.toNat j := by
  rw [h, Lvm.QSig.w64, bit_word _ hj, bitE]
  split_ifs <;> rfl

theorem ldEs_fst (st : Nat) : ∀ (n a : Nat) (p : Ptr),
    (Lvm.Har.ldEs a st n p).1 = (List.range n).map fun i => ec (p.e + i)
  | 0, _, _ => rfl
  | n + 1, a, p => by
    simp only [Lvm.Har.ldEs, bind_apply, pure_apply]
    rw [ldE_adv, ldEs_fst st n (a + st) ⟨p.k, p.e + 1⟩, ldE_apply, List.range_succ_eq_map]
    simp only [List.map_cons, List.map_map, Nat.add_zero]
    congr 1
    exact List.map_congr_left fun i _ => by simp only [Function.comp_apply]; congr 1; omega

/-- The bus phase's value: the output cells' values, one zero leaf-decomposition scalar. -/
def busV (M : Mem) (b : BusC) : List FE × FE × FE × List FE × List FE × List FE :=
  (vs M b.al, b.be.val M, b.cnt.val M, vs M b.pt, vs M b.vals, [0])

theorem busR_eq {M : Mem} {res : List FE × FE × FE × List FE × List FE × List FE} {b : BusC}
    (h : BusR M res b) : res = busV M b ∧ (vs M b.vals).length = 3 := by
  obtain ⟨a, b', c', d, e, f⟩ := res
  obtain ⟨h1, h2, h3, h4, h5, h6, h7⟩ := h
  simp only at h1 h2 h3 h4 h5 h6 h7
  subst h1 h2 h3 h4 h5 h6
  exact ⟨rfl, h7⟩

theorem busG_fst (p : Params) (z o g : Cell) (P : Nat) (ptr : Ptr) :
    (busG p z o g P ptr).1.al = (List.range busBits).map (fun i => ec (ptr.e + i)) ∧
      ∃ d : PD, (busG p z o g P ptr).1.pt = d.cells := by
  simp only [busG, bind_apply, pure_apply]
  exact ⟨ldEs_fst _ _ _ _, _, rfl⟩

end Lvm.Har
