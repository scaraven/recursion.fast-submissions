-- New for lvm2 (roll 8 = B1; statements by L-D, proofs owner L-H): the typed HAR, the circuit-soundness half of
-- `nodeT20`. Roll 7's `harith20` (`LvmFinHB`) / `harith_core` (`LvmQAsmHarMain`) for the B program: wherever the B
-- program's Q_arith (`qaB = phases47 >>= qarithB`) holds and asserts on a pair's memory, V_S's typed decision on the
-- child's stream accepts and folds to the statement's incoming accumulator. `harithT20`'s statement is L-D's (the form
-- `LvmNodeSoundT.nodeSoundT` consumes); L-H's proofs, with the parts in `LvmQTypedHar{T,G,C,Z,R,A,M}`.
import LvmNodeSoundT
import LvmQTypedHarC
import LvmQAsmArith2WhirP
import LvmAccNodePub
import LvmQLinkArithKS
import LvmQTypedHarB
import LvmQAsmHarTails
-- (GOLF2 import pruning: dropped LvmQAsmHarP47, LvmQTypedHarZ, LvmQTypedHarR: unused by this module.)

-- (GOLF2: 71 declarations that `certified` does not use moved verbatim to `LvmE2QNodeFOff`, outside its import closure.)

-- ===== merged from `LvmQLinkArithP8` (GOLF module merge: `LvmQLinkArithP8.lean` is now a stub importing `LvmQTypedHarS`) =====
section

/-!
# QA1 links: the `P8` instance (smoke check of `ksLink_sound`)

The `KS` link's template check (`SLok`) is discharged by evaluation at `P8`'s sizes (B1: `ksLog = 14`,
`recRowsLog = 14`, KS14's block E, `spongeBlocks P8` from `sizes_P8`). S2 has no `CH` link.
-/

set_option autoImplicit false

namespace Lvm.Q1

open Lvm Lvm.Loop Lvm.Loop.Build

/-! ## The template check does not read addresses -/

/-- An operand with its address forgotten. -/
def Src.shape : Src → Src
  | .ext _ => .ext default
  | s => s

/-- An instruction with its addresses forgotten. -/
def Ins.shape (i : Ins) : Ins := ⟨i.op, i.ty, i.args.map Src.shape⟩

/-! ## Combinators commute with forgetting addresses -/

-- (lvm2 GOLF: `okE_P8` and `ksLink_sound_P8` moved to `LvmQLinkArithP8S`, outside `Solution`'s import closure: only
-- `LvmFinDec` uses them, and `okE_P8`'s decision cost ≈ 14 s of the certificate's build.)

end Lvm.Q1
end
-- ===== end of `LvmQLinkArithP8` =====

-- ===== merged from `LvmQAsmHarLink20` (GOLF module merge: `LvmQAsmHarLink20.lean` is now a stub importing `LvmQTypedHarS`) =====
section
-- New for lvm (HAR; WP-16b: the checks through WP-16a2's one-pass `SLokF`, moved here from `LvmFinDec`):
-- QA1's link soundness at `P20` (`logN = 20`, `ksLog = 14`, `recRowsLog = 14`: KS14, lvm2 CR-K):
-- the template checks (`SLok`) decided as for `P8` (QA1's `LvmQLinkArithP8`), the KS template
-- (`okE`) after the re-freeze.

set_option autoImplicit false

namespace Lvm.Fin

open Lvm Lvm.Loop Lvm.Loop.Build Lvm.Q1

/-! ## `SLok` in one pass (WP-16a2, moved here from `LvmFinDec` for the `P20` glue checks)

`SLok` looks every operand's row up from the template's head (quadratic: 16 s of kernel at the
600-row block E); `SLokF` walks the template once and looks the assertions up in a short list. -/

end Lvm.Fin

end
-- ===== end of `LvmQAsmHarLink20` =====

-- ===== merged from `LvmQTypedHarA` (GOLF module merge: `LvmQTypedHarA.lean` is now a stub importing `LvmQTypedHarS`) =====
section
-- New for lvm2 (roll 8 = B1, L-H): the typed HAR's A23 phase at `Φ_Q`: `qaccT` replays V_S's `dAccT` (AC-Q's
-- `qacc_sound` with the typed instance: `dk = 2`, 43 variables, `b = κ ++ r_x ++ r_y`, no `PUB` table).

/-!
# A23 at `Φ_Q` in the circuit

**`qaccT_replays`**: wherever `qaccT (aP P / 8) pb r_x r_y v`'s rows hold and assert (gate on: `PUB` lane 0 is
`1`), `dAccT` on the child's `PUB` (`pubOf vk c_L Σ'`), the point `r_x ++ r_y` and the matrix values `v` from any
state at `aP P` with `ok` keeps `ok` (`h(0) = acc_in'.y`, `h(1) = Σ_o eq(κ, o)·v_o`, the zero scalar), ends at
`mbP P`, and folds to the current proof's `acc_in` (`accC M pb`, its `PUB` cells).

* **`qaccT_facts`** (AC-Q's `qacc_facts` for `qaccT`): from lane `L`, the gadget's rows and assertions give the
  five equations on the stream view `feAt Σ` (`h₀`, `Σh`, the line, `h(t)`, the zero scalar).
* **`dAccT_run`**: `dAccT` from any state at position `Q`, as a function of `Q` (`accFold_run`'s form).
-/

set_option autoImplicit false

namespace Lvm.Har

open Lvm Lvm.Loop Lvm.Loop.Build Lvm.QTyped Lvm.Q1 DM

section helpers
open Lvm.QAcc Lvm.QSig

end helpers

section
variable {c : Ctx} {M : Mem} {sig : ByteArray} {T : Nat}

end

end Lvm.Har
end
-- ===== end of `LvmQTypedHarA` =====

-- ===== merged from `LvmQTypedHarM` (GOLF module merge: `LvmQTypedHarM.lean` is now a stub importing `LvmQTypedHarS`) =====
section
-- New for lvm2 (roll 8 = B1, L-H): the typed HAR's mini-bus phase: `miniG` replays V_S's `dMiniT` (roll 7's
-- `busG_replays` at the mini-bus's depth, `tabG_replays` on its tables, and the fixed address columns checked in the
-- circuit by `powColG`, V_S's `tableCheckR`).

/-!
# The mini-bus in the circuit

* **`miniG_replays`**: on tables `tabs` that are all sumcheck tables, whose shapes, rounds and depth are the
  circuit's (`TData.mbS`, `mbR`, `mbD`), and whose every fixed column `x ↦ g^{b + s x}` is listed in `TData.mbFix`,
  `miniG` replays `dMiniT p (M3.real p fun _ ↦ tabs) tabs pub` from `P` to the table phase's end; the evaluations
  are its table cells' values.
* **`mbT_sumcheck`, `mbT_fix`**: B1-Q's mini-bus tables (`mbT`: the seed arrays, then the read tables) meet the
  first and the last condition at any placements (`mbFixOf`).
-/

set_option autoImplicit false

namespace Lvm.Har

open Lvm Lvm.Loop Lvm.Loop.Build Lvm.QTyped Lvm.QAsm Lvm.Q1 Lvm.M3 DM

/-- Every fixed column of `tabs` is listed in `fx` with its power closed form `g^b·powEval r (g^s)`. -/
def FixListed (tabs : List Tab) (fx : List (Nat × Nat × Nat × Nat)) : Prop :=
  ∀ k (t : Tab), tabs[k]? = some t → ∀ i (f : Nat → FK) (e : List FE → FE), t.cols[i]? = some (.fix f e) →
    ∃ b s, (k, i, b, s) ∈ fx ∧ ∀ r, e r = FE.ofK (FK.x ^ b) * powEval r (FK.x ^ s)

/-- **B1-Q's mini-bus tables are all sumcheck tables** (a seed array has a seed, a read table a read). -/
theorem mbT_sumcheck (C : QCfg) (wordK : Nat → Nat) (fin : Nat → Bool × Nat) (cnt : Nat → Nat) :
    sumcheckTabs (mbT C wordK fin cnt) = mbT C wordK fin cnt := by
  unfold sumcheckTabs
  rw [List.filter_eq_self]
  intro t ht
  rcases List.mem_append.mp ht with h | h
  · obtain ⟨a, -, rfl⟩ := List.mem_map.mp h
    simp [InArr.tab]
  · simp only [capReads, List.mem_map] at h
    obtain ⟨x, -, rfl⟩ := h
    simp [readTab]

/-- Seed array `k` of `mbArrs` (`fin` only changes its finalize column). -/
theorem mbArrs_get (C : QCfg) (fin : Nat → Bool × Nat) (k : Nat) :
    (mbArrs C fin)[k]? = ((mbBlocks C.p)[k]?).map fun q =>
      ⟨.K, mbBlk, (lay C).sb + 17 * q.2 + q.1, 17, [(false, Lvm.sCol C.p q.1 + q.2)], fin k, none⟩ := by
  rw [mbArrs, List.getElem?_map, List.getElem?_zipIdx, Option.map_map, Nat.zero_add]
  rfl

/-- **B1-Q's mini-bus tables' fixed columns are `mbFixOf`'s** (a seed array's address column; a read table has
none). -/
theorem mbT_fix (C : QCfg) (wordK : Nat → Nat) (fin : Nat → Bool × Nat) (cnt : Nat → Nat) :
    FixListed (mbT C wordK fin cnt) (mbFixOf C) := by
  intro k t hk i f e hc
  rw [mbT, List.getElem?_append] at hk
  split at hk
  · rw [List.getElem?_map, mbArrs_get] at hk
    cases hb : (mbBlocks C.p)[k]? with
    | none => simp [hb] at hk
    | some q =>
      simp only [hb, Option.map_some, Option.some.injEq] at hk
      subst hk
      simp only [InArr.tab, InArr.vcols, List.map_cons, List.map_nil, List.cons_append,
        List.nil_append] at hc
      match i, hc with
      | 2, hc =>
        simp only [List.getElem?_cons_succ, List.getElem?_cons_zero, Option.some.injEq,
          ColSrc.fix.injEq] at hc
        obtain ⟨-, rfl⟩ := hc
        refine ⟨(lay C).sb + 17 * q.2 + q.1, 17, ?_, fun r => rfl⟩
        rw [mbFixOf, List.mem_map]
        refine ⟨(⟨.K, mbBlk, (lay C).sb + 17 * q.2 + q.1, 17, [(false, Lvm.sCol C.p q.1 + q.2)], (false, 0),
          none⟩, k), ?_, rfl⟩
        rw [List.mem_zipIdx_iff_getElem?, mbArrs_get, hb]
        rfl
      | 0, hc => simp at hc
      | 1, hc => simp at hc
      | _ + 3, hc => simp at hc
  · simp only [capReads, List.getElem?_map, Option.map_eq_some_iff] at hk
    obtain ⟨x, -, rfl⟩ := hk
    simp only [readTab] at hc
    match i, hc with
    | 0, hc => simp at hc
    | 1, hc => simp at hc
    | 2, hc => simp at hc
    | _ + 3, hc => simp at hc

/-- The GKR layers end on a lane boundary (as in `busG_sound`). -/
theorem layersEnd_mod8 : ∀ (sts : List Nat) (n Q : Nat), Q % 8 = 0 → layersEnd sts n Q % 8 = 0
  | [], _, _, hQ => hQ
  | st :: sts, n, Q, hQ => layersEnd_mod8 sts _ _ (stepEnd_mod st n Q hQ)

/-- **The circuit's fixed-column checks give `tableCheckR`**: where `miniG`'s `powColG`/`assertEq` checks over `fx`
hold (gate on), every fixed column listed in `fx` evaluates at its table's point cells to its value cell. -/
theorem fixCheck_of {tabs : List Tab} {fx : List (Nat × Nat × Nat × Nat)} (hfix : FixListed tabs fx)
    {c : Ctx} {M : Mem} {z g : Cell} (hz : z.val M = 0) (hg : g.val M = 1)
    (tab : List (List Cell × List Cell)) {q : Ptr}
    (hok : Lvm.QSig.Ok c M (seqAll (fx.map fun f => do
      let e := tab.getD f.1 default
      let v ← powColG z f.2.2.1 f.2.2.2 e.1
      assertEq (e.2.getD f.2.1 z) v g)) q) :
    tableCheckR tabs (tab.map fun e => (vs M e.1, vs M e.2)) = true := by
  unfold tableCheckR
  rw [List.all_eq_true]
  rintro ⟨t, pt, ev⟩ hmem
  obtain ⟨k, hk⟩ := List.mem_iff_getElem?.mp hmem
  obtain ⟨hk1, hk2⟩ := List.getElem?_zip_eq_some.mp hk
  rw [List.getElem?_map, Option.map_eq_some_iff] at hk2
  obtain ⟨x, hx, hxe⟩ := hk2
  simp only [Prod.mk.injEq] at hxe
  obtain ⟨rfl, rfl⟩ := hxe
  rw [List.all_eq_true]
  rintro ⟨col, i⟩ hci
  rw [List.mem_zipIdx_iff_getElem?] at hci
  cases col with
  | com _ _ => rfl
  | fix f e =>
    obtain ⟨b, s, hmemfx, he⟩ := hfix k t hk1 i f e hci
    obtain ⟨q', hq'⟩ := Lvm.QSig.ok_seqAll _ q hok _ (List.mem_map_of_mem hmemfx)
    have htk : tab.getD k default = x := by rw [List.getD_eq_getElem?_getD, hx]; rfl
    obtain ⟨h1, h2, -⟩ := Lvm.QSig.ok_bind' hq'
    simp only [htk] at h1 h2
    have hv := powColG_spec hz b s x.1 q' h1.1
    have heq := Lvm.QAcc.assertEqE_spec h2 hg
    simp only [beq_iff_eq]
    rw [he]
    simp only [vs]
    rw [← hv, ← heq, List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, List.getElem?_map]
    cases x.2[i]? with
    | none => exact hz.symm
    | some y => rfl

section
variable {c : Ctx} {M : Mem} {sig : ByteArray} {T : Nat}

/-- **The mini-bus replayed** (soundness direction): wherever `miniG`'s rows hold and assert (gate on), `dMiniT` on
`tabs` from any state at `P` with `ok` keeps `ok`, ends at the table phase's end, and its evaluations are the table
cells' values. -/
theorem miniG_replays (hS : Streamed M sig T) {z o g : Cell} (hz : z.val M = 0) (ho : o.val M = 1)
    (hzE : z.ty = .E) (hoE : o.ty = .E) (hg : g.val M = 1) (hgK : g.ty = .K) (p : Params)
    (hl : p.leafdecReads = 1) (Td : TData) (tabs : List Tab) (hsc : sumcheckTabs tabs = tabs)
    (hS' : Td.mbS = tabs.map Tab.shape) (hR : Td.mbR = p.tableRounds) (hD : Td.mbD = p.busDepth)
    (hfix : FixListed tabs Td.mbFix) (pub : Pub) {P : Nat} (hP : P % 8 = 0)
    (hT : tabEnd Td.mbS Td.mbR (busEndD Td.mbD P) + 40 ≤ 8 * T) (ptr : Ptr) (hp : 1 ≤ ptr.e) :
    Replays c M sig (TypedV.dMiniT p (M3.real p fun _ => tabs) tabs pub) (miniG z o g Td P) ptr P
      (tabEnd Td.mbS Td.mbR (busEndD Td.mbD P)) fun v t => v = t.2.map fun e => (vs M e.1, vs M e.2) := by
  intro hok s hs hsok
  have hout : (miniG z o g Td P ptr).1 = ((busGD Td.mbD z o g P ptr).1,
      (tabG Td.mbS Td.mbR (busEndD Td.mbD P) z o g (busGD Td.mbD z o g P ptr).1
        (ptr.adv (busGD Td.mbD z o g P ptr).2)).1) := rfl
  obtain ⟨hB, hok1, -⟩ := Lvm.QSig.ok_bind' hok
  obtain ⟨hTb, hok2, -⟩ := Lvm.QSig.ok_bind' hok1
  obtain ⟨hFx, -⟩ := Lvm.QSig.ok_bind' hok2
  rw [hout]
  clear hout hok hok1 hok2
  have hS0 : Td.mbS = (sumcheckTabs tabs).map Tab.shape := by rw [hsc]; exact hS'
  rw [hS0, hR, hD] at hTb hFx hT ⊢
  rw [hD] at hB
  have e1 : busGD p.busDepth z o g P = busG p z o g P := rfl
  have e2 : busEndD p.busDepth P = busEnd p P := rfl
  rw [e1] at hB hTb hFx ⊢
  rw [e2] at hTb hFx hT ⊢
  have hT1 : busEnd p P + 40 ≤ 8 * T := by unfold tabEnd at hT; (clear * - hR hT e2; omega)
  have hP2 : busEnd p P % 8 = 0 := by
    have := layersEnd_mod8 (gkrSteps p.busDepth) 0 (busP1 P + 48) (by simp only [busP1, busBits]; (clear * - hP; omega))
    simp only [busEnd]; (clear * - this; omega)
  obtain ⟨b1, b2, b3⟩ := busG_replays (c := c) hS hz ho hg p hl hP hT1 ptr hB s hs hsok
  obtain ⟨hal, d, hpt⟩ := busG_fst p z o g P ptr
  generalize (busG p z o g P ptr).1 = bus at b3 hal hpt hTb hFx ⊢
  obtain ⟨hbv, h3⟩ := busR_eq b3
  rw [dMiniT_eq, bind_run']
  generalize busPh p sig s = BB at b1 b2 hbv ⊢
  obtain ⟨bv, s1⟩ := BB
  simp only at b1 b2 hbv
  subst hbv
  simp only [busV, bind_run', require_run']
  have hok2 : ((M3.real p fun _ => tabs).busFinal ⟨vs M bus.al, bus.be.val M, bus.cnt.val M, vs M bus.pt,
      vs M bus.vals, [0], pub⟩).ok = true := by
    show ((vs M bus.vals).length == 3 && [(0 : FE)] == [0]) = true
    rw [h3]; decide
  set bo := (M3.real p fun _ => tabs).busFinal ⟨vs M bus.al, bus.be.val M, bus.cnt.val M, vs M bus.pt,
      vs M bus.vals, [0], pub⟩
  have rt := tabG_replays (c := c) hS hz ho hg hzE hoE p (M3.real p fun _ => tabs) pub tabs rfl bus
    (countRoot := bus.cnt.val M) (leafdec := [0]) rfl rfl rfl rfl
    (by rw [hal]; simp [vs, busBits])
    (by rw [hal]; intro x hx; obtain ⟨i, -, rfl⟩ := List.mem_map.mp hx; rfl)
    (by rw [hpt]; intro x hx; obtain ⟨i, -, rfl⟩ := List.mem_map.mp hx; rfl)
    bo rfl hP2 hT (ptr.adv (busG p z o g P ptr).2)
  obtain ⟨t1, t2, t3⟩ := rt hTb ⟨s1.ent, s1.msg, bo.ok && s1.ok⟩ b2 (by rw [hok2, b1]; rfl)
  generalize tabPh p (M3.real p fun _ => tabs) pub bo (vs M bus.pt) sig ⟨s1.ent, s1.msg, bo.ok && s1.ok⟩ = TT
    at t1 t2 t3 ⊢
  obtain ⟨ev, s3⟩ := TT
  simp only [TabR] at t1 t2 t3
  subst t3
  generalize (tabG ((sumcheckTabs tabs).map Tab.shape) p.tableRounds (busEnd p P) z o g bus
    (ptr.adv (busG p z o g P ptr).2)).1 = tab at hFx ⊢
  rw [pure_run']
  refine ⟨?_, t2, rfl⟩
  rw [hsc, fixCheck_of hfix hz hg tab hFx, t1]
  rfl

end

end Lvm.Har
end
-- ===== end of `LvmQTypedHarM` =====

-- ===== merged from `LvmQTypedHarG` (GOLF module merge: `LvmQTypedHarG.lean` is now a stub importing `LvmQTypedHarS`) =====
section
-- New for lvm2 (roll 8 = B1, L-H): the typed core gadget `typedG` replays V_S's typed phases `dTypedT` (the
-- composition of the zerocheck's, the wiring's, the relayout's, A23's and the mini-bus's replays), generic in the
-- parameters, the static data and the instance.

/-!
# `typedG` replays `dTypedT`

**`typedG_replaysG`**: on regions that are V_S's (`TdOk`) and mini-bus tables whose shapes, rounds, depth and fixed
columns are the circuit's, wherever `typedG Td pb P z o`'s rows hold and assert (gate on), `dTypedT p N (N.m3 p)` on
the child's `PUB` from any state at `P` with `ok` keeps `ok`, ends at `typedEnd Td P`; its accumulator is the current
proof's `acc_in` (`accC M pb`), its claims are `typedClaimsN` of the output cells, its evaluations the table cells'.
-/

set_option autoImplicit false

namespace Lvm.Har

open Lvm Lvm.Loop Lvm.Loop.Build Lvm.QTyped Lvm.Q1 Lvm.M3 DM
open Lvm.TypedV (TNat)

/-! ## The positions -/

/-! ## The monad laws as propositional rewrites

`bind_run'`, `pure_run'` restated with a non-`rfl` proof, so that `simp` rewrites with
them by `Eq.mpr` steps instead of a definitional change: as `rfl` lemmas, the kernel re-checked the unfolded
`dTypedT` against the folded one through `DM`'s `bind` (≈ 9 s). -/

section
variable {c : Ctx} {M : Mem} {sig : ByteArray} {T : Nat}

end

end Lvm.Har
end
-- ===== end of `LvmQTypedHarG` =====

-- ===== merged from `LvmQTypedHarT` (GOLF module merge: `LvmQTypedHarT.lean` is now a stub importing `LvmQTypedHarS`) =====
section
-- New for lvm2 (roll 8 = B1, L-H): V_S's typed decision program cut into its phases (`decideProgT = decideProgTH`),
-- and the composition of the phase facts into `decideCoreT` and `accOutOfT` (roll 7's `core_of_phases` for
-- `decideProgT`: the typed phases replace phases 2, 3, 3b; phases 4–7 are unchanged; the openings are `dOpenT`).
-- lvm2 roll 11 (M′ `S2GM`, R11-N): one commitment, so one root skip (B1: `C_main`'s and `C_rec`'s).

/-!
# `decideProgT` by phases

| phase | program |
|---|---|
| typed (zerocheck, wiring, relayout, A23 at `Φ_Q`, mini-bus) | `dTypedT p N (N.m3 p) pub` |
| 4 tape, 5 wire, 6 `KS`, 7 `KS` link | `tapePh`, `wirePhC`, `ksPh`, `ksLinkPh` (roll 7's) |
| 8–9 openings | `dOpenT p (smallT p pub)` on the typed claims and `dClaimsZ`'s |

**`core_of_phasesT`**: if every phase, run from its start position with `ok`, keeps `ok`, reaches the next start and
yields fixed values, and the openings read `Σ` to its end, then `decideCoreT` accepts and `accOutOfT` is the typed
phases' accumulator.
-/

set_option autoImplicit false

namespace Lvm.Har

open Lvm DM

/-! The `DM` run lemmas restated with a non-`rfl` proof, so that `simp` rewrites with them by `Eq.mpr` steps: as
`rfl` lemmas, the kernel re-checked the rewritten run against the program through `DM`'s `bind`. -/

end Lvm.Har
end
-- ===== end of `LvmQTypedHarT` =====

/-!
# The typed HAR at `P20`

**Headline** (fixed; `nodeT20` consumes it with L-D's glue: `decideFT = decideCoreT ∧ Φ_Q(acc_out) = y`, the last
from `AccOkT` and `PhiQC_eq` through `S.cache`):

* **`harithT20 S H`**: on a node statement (`okS`, `b = 1`) and a good pair, with the input map on the pair's memory
  (`InMapM`), the child's stream a trace of the schedule (`LaneLink`, `LinkOk`), `qaB`'s segments holding and
  asserting at Q_arith's pointer, and the memory facts of the `BITS` rows (`BVT`, roll 7's `BVFacts` on `memT`;
  L-D proves them from the typed `BITS` rows): `decideCoreT P20 NT20 vk c_L Σ' = true` and
  `accOutOfT P20 NT20 vk c_L Σ' = acc_in`.

**Parts** (the static `Bool` check they need, `harChkB`, is L-W's guard field `S.har`, as roll 7's `S.hwr`, `S.hwm`,
`S.hwz`):

1. **`core_of_phasesT`** (`LvmQTypedHarT`; the composition, as `core_of_phases`): `decideCoreT ∧ accOutOfT = acc` from the typed phases'
   `PhaseAt` (`dTypedT`), phases 4–7 (`tapePh`, `wirePhC`, `ksPh`, `ksLinkPh`, unchanged) and the openings
   (`dOpenT` at `smallT`).
2. **`typedG_replays`** (the typed core gadget; restated with the guard `S` and the stream bounds): `typedG` replays `dTypedT` from `typedPos P20` to
   `typedEnd tdata20 (typedPos P20)`; its values are the cells' (the folded accumulator is `PUB`'s `acc_in`, the
   typed claims are `typedClaimsN` of the cells, the mini-bus's evaluations the table cells').
3. **Phases 4–7**: roll 7's `p47_at` (`LvmQAsmHarP47`), unchanged, at `P4 = typedEnd tdata20 (typedPos P20)`.
4. **`openT_at`** (the openings at ν = 23, both shapes): `openG`'s rows give `dOpenT P20 (smallT P20 pub)` on the
   cells' claims (`claimsT M cs`), as roll 7's `open_at` gives `openPhZ`.
-/

set_option autoImplicit false

namespace Lvm.Har

open RecursionFast Lvm Lvm.Loop Lvm.Loop.Build Lvm.Q1 Lvm.QAsm Lvm.QTyped Lvm.Typed Lvm.NS Lvm.T Lvm.ASM Lvm.QLink
  Lvm.Replay DM
open Lvm.M3 (lay26)
open Lvm.VEq (pubX)
open LeanVM.Protocol (Column)

/-! ## The static facts at `P20` (L-H) -/

-- (lvm2 E2F-G: `harNumT20`, `layOk_9T`, `okE_P20T`, `mini20`, `typedG_replays` and `harithT20`, roll 11's
-- decisions at `P20`, moved to `LvmQTypedHar20`, outside the S2GF certificate's import closure.)

/-! ## The guard check `harChkB` at `P20` -/

/-! ## Glue (`LvmFinHB`'s, which the typed closure does not import) -/

theorem sigma_sizeT {p : Params} {ws : List Word} (h : hashedLen p ≤ 8 * ws.length) :
    (sigma p ws).size = hashedLen p := by
  simp only [sigma, ByteArray.size, List.size_toArray, List.length_take, wordsBytes_length]
  omega

/-! ## The headline -/

/-! ## The parts -/

-- Part 1, the composition `core_of_phasesT`: proved in `LvmQTypedHarT` (L-D's statement, unchanged).

/-! ## The mini-bus's record at `P20` (from the guard's `fitsMiniB`) -/

theorem tdataOf_mb (C : QCfg) (F : TFrz) : (tdataOf C F).mbS = (mbTOf C F).map M3.Tab.shape ∧
    (tdataOf C F).mbR = ((mbTOf C F).map (·.τ)).foldl max 0 ∧
    (tdataOf C F).mbD = log2Ceil (M3.pushLeavesR (mbTOf C F)) ∧ (tdataOf C F).mbFix = mbFixOf C := by
  simp only [tdataOf, and_self]

end Lvm.Har
