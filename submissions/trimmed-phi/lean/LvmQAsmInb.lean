-- New for lvm (INB): `hinb` for the assembled node programs `QAsm.Q cfg20` and `QAsm.Q cfg8`
-- (WP-16a's `LvmQAsmProg`): WP-16a's position classes cover the cap bits (`capCov_pos`), Q_sig and
-- Q_arith have no `readd` (decided), and `LvmQAsmInbNode.hinb_node`/`inb_of_m3` do the rest.
import LvmQAsmProg
import LvmSigBits
import LvmNodeSoundCirc
import LvmNodeSoundGood
import LvmNodeSoundTr
import LvmNodeSoundKS
import LvmNodeSoundHdr
import LvmNodeSoundFields
import LvmQAsmInbCore
import LvmQLinkSound
import LvmBitsTab

-- (GOLF2: 64 declarations that `certified` does not use moved verbatim to `LvmQAsmInbOff`, outside its import closure.)

-- ===== merged from `LvmCertSNodeBits` (GOLF module merge: `LvmCertSNodeBits.lean` is now a stub importing `LvmQAsmInb`) =====
section
-- WP-14c (NodeSound, O10). New for lvm: the hypotheses `SigTabsIn` and `SigCellsLt` of WP-12b's
-- `sigBitsOk` (LvmSigBits): Q_sig's six BITS tables in the auxiliary tables, and every cell they
-- name inside the program. The part decomposition follows WP-12's `qsig_parts` (LvmQSigParts), with
-- QL's builder bookkeeping (`bind_apply`, `Ptr.adv_append`, `mkLoop_tw`; `loop_adv` as in QA2's
-- LvmQWhirBase).

/-!
# The BITS tables of `Q_sig` in the instance

* **`sigTabsIn_append`**: `SigTabsIn` holds for `aux = (sigSpecs I o bpl).map BSpec.tab ++ rest`
  (any other auxiliary tables after them, e.g. QL's position-field tables).
* **`sigCellsLt_of`**: `SigCellsLt Q I o bpl` from two layout facts: `SigRegLt C I` (the input
  regions of `I` the tables name, with their extents, below `C = Q.cells .K`) and `SigOutLt C o` (the
  chain and path cells of `Q_sig`'s output below `C`).
* **`sigOutLt_qsig`**: `SigOutLt C (qsig I p).1` whenever `Q_sig` placed at `p` ends at or below `C`
  (`(p.adv (qsig I p).2).k ≤ C`; true when `Q_sig`'s segments are a prefix of the program's at `p`):
  every cell a loop of `Q_sig` writes lies below the pointer after it.
-/

set_option autoImplicit false

namespace Lvm.NS

open Lvm Lvm.Loop Lvm.Loop.Build Lvm.QSig Lvm.SigBits Lvm.BitsTab Lvm.M3

/-! ## The tables in the auxiliary list -/

/-! ## The cells the tables name -/

/-! ## Q_sig's cells lie below the pointer after it -/

end Lvm.NS
end
-- ===== end of `LvmCertSNodeBits` =====

-- ===== merged from `LvmNodeSoundMain` (GOLF module merge: `LvmNodeSoundMain.lean` is now a stub importing `LvmQAsmInb`) =====
section
-- WP-14c (NodeSound, O10). New for lvm: `NodeSound` for `GoodN`, generic over the node program's
-- parts and its input map (BLUEPRINT §4.6, §7.1 row 4, A19); every remaining hypothesis is named
-- with its owner.

/-!
# `NodeSound` for the node program

**`nodeSound_main`**: `NodeSound (VS P20 m) vk Good childS` (any `Good` that implies `GoodN T hτ`;
A23's `GoodA`, `LvmAccNode`) for the node program
`Q = toProgram nK nE (qprog lay I qa)` (Q_link, Q_sig, Q_arith) on the tables
`lvmTabs Q pl groups (arrsX x) aux` (the input arrays depend on the statement through `PUB`), from:

| hypothesis | content | owner |
|---|---|---|
| `hT` | `T x` (O6's `sumcheckTabs (tabs (pubX x))`) is the node program's tables | final assembly (`lvmTabsC_eq`, filter = id) |
| `hst` | `AuxStatic`: `wf`, `GrpOk`, `InOk`, aux seed nothing, read columns inside widths, read count, `GInj` | final assembly (decided: `segsOk`, `grpOkCore`, `inOkB`, `tabsOkB`) |
| `hinb` | the interpreter's `inb` on the committed inputs (`b = 1`) | QL (position bits are bits + `QOk`'s bounds) |
| `hS`, `hQ`, `hws`, `hNs`, `hfg` | Q_link's static checks, its stream region inside the cells, one gate cell for Q_link and Q_sig | QL (decided per layout) |
| `hqlt` | Q_link's `QLT` cells hold the static table `qltData` | QL / INT-2 (a static input kind, QL's proposal) |
| `hpos` | Q_link's position-bit cells are the answers' bits (QIn.bits) | QL (its position `BITS` tables, as `sigBitsOk` for Q_sig) |
| `rest`, `haux`, `hR`, `hP` | `aux` starts with Q_sig's six `BITS` tables; their input regions (14 bounds) and Q_sig's segment lie below the cell count (then `SigTabsIn`, `SigCellsLt` by `LvmCertSNodeBits`) | final assembly (decided on the layout) |
| `hmap` | `InMapN`: the stream lanes, the flag, the `KS` `X`/`Y` cells (values of the committed pair; `SigKSin` and the trace digest then follow from `GoodK`, `LvmNodeSoundKS`), the `PUB` cells, `σ'`'s cells, the child header's cells | input map: `inKOf_pub`/`inKOf_com` on the concrete arrays |
| `harith` | Q_arith's segments on the committed memory, with the input map and Q_link's `LaneLink`/`LinkOk`, for a `Good` pair ⇒ `decideF … = true` (A23: from `decideCore` and `accOutOf = acc_in`, `LvmAccNode.nodeSound_acc`) | Q_arith (`Q_arith_eq`): HAR, AC-Q |
-/

set_option autoImplicit false

namespace Lvm.NS

open RecursionFast Lvm Lvm.T Lvm.ASM Lvm.Replay Lvm.Loop Lvm.Loop.Build Lvm.QLink Lvm.QSig Lvm.M3
open Lvm.SigBits LeanVM.Protocol

-- `okS` facts (`okS_vk`, `okS_sig`): `LvmNodeSoundFields`.

-- The header's lanes (the `PUB` values, `hdrBytesX`, `hdrLane`): `LvmNodeSoundFields`.

/-! ## The node program's hypotheses -/

section Main

variable {α : Type} (lay : Layout) (I : SigIn) (qa : BM α) (nK nE : ℕ)
  (pl : ℕ → Var → Bool × ℕ) (groups : List Grp) (arrsX : List UInt8 → List InArr) (aux : List Tab)
  (hτ' : ∀ x, ∀ t ∈ lvmTabs (Qn lay I qa nK nE) pl groups (arrsX x) aux, t.τ ≤ lay26.μ)

variable {lay I qa nK nE pl groups arrsX aux hτ'}

end Main

end Lvm.NS
end
-- ===== end of `LvmNodeSoundMain` =====

-- ===== merged from `LvmQAsmInbLink` (GOLF module merge: `LvmQAsmInbLink.lean` is now a stub importing `LvmQAsmInb`) =====
section
-- New for lvm (INB): Q_link's `readd`s are in region. The address computations are WP-11b-QL's
-- (`LvmQLinkGadgets.qltLoop_spec`, `capLoop_spec`: the parts that do not use the gate or the
-- assertions, adapted) and the opening walk is `LvmQLinkSound.open_facts`'s.

/-!
# Q_link's `readd` addresses

Q_link reads by address in two places, both into the stream region `[sb, sb + 2^m)`:

* the **QLT loop**: the table cells `g^e₁`, `g^e₂` and `g^l` times them (`qltLoop_in`);
* the **cap loops**: `g^(lo + 4·Σ_z β_z 2^z + i)`, `i < 4`, from the cap bits of each (padded)
  position (`capLoop_in`, `capAddr`). With every bit cell `0` or `1` the exponent is below
  `lo + 4·2^c` (`bitSum_lt`).

Neither uses the gate or any assertion: the address is a function of the rows alone.
**`qlink_in`**: with `QOk`, the QLT cells holding `qltData` and the cap bits of every position
`j < padT t` of every opening being bits, every `readd` of `qlink p lay` is in region (`InOk`).
-/

set_option autoImplicit false

namespace Lvm.Loop.Build

open Lvm.Loop

/-! ## The QLT loop -/

/-! ## The cap loops -/

end Lvm.Loop.Build

namespace Lvm.QLink

open RecursionFast Lvm Lvm.Replay Lvm.Loop Lvm.Loop.Build

/-! ## Q_link -/

theorem pchunks_end {t : Nat} : ∀ c ∈ pchunks t, c.1 + 2 ^ c.2 ≤ padT t := by
  intro c hc
  unfold padT
  by_cases h : t = 2 ^ t.log2
  · rw [pchunks, if_pos h] at hc ⊢
    rw [List.mem_singleton] at hc
    subst hc; simp
  · rw [pchunks, if_neg h] at hc ⊢
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl <;> simp

variable {p : Params} {lay : Layout} {c : Ctx} {M : Mem}

end Lvm.QLink
end
-- ===== end of `LvmQAsmInbLink` =====

-- ===== merged from `LvmQAsmInbSite` (GOLF module merge: `LvmQAsmInbSite.lean` is now a stub importing `LvmQAsmInb`) =====
section
-- New for lvm (INB): one lemma per kind of `readd` site, so a new site (Q_arith's remaining phases,
-- Q_acc, A23) costs one instance. Builds on WP-11b-QL's `gpowBits_spec` (`LvmQBuildLemmas`).

/-!
# `readd` sites: the generic lemmas

* `readd_in`: a straight-line `readd τ lo m α` is in region iff its address cell is `g^(lo + k)`,
  `k < 2^m`; `readd_in_gpow`: from `α = g^e`, `lo ≤ e < lo + 2^m`.
* **`gpowBits_in`**: an address from bit cells, `gpowBits lo s x bs` (WP-11b-QL), lies in
  `[lo, lo + s·(2^|bs| − 1)]` when the bits are bits (`bitsNat_lt`); `gpowBits_noReadd`: the
  address chain itself has no `readd`.
* **`readdBits` / `readdBits_in`**: the pattern "address from bits, then read" as one gadget, in
  region when `rlo ≤ lo` and `lo + s·(2^|bs| − 1) < rlo + 2^m`.
* Loop sites: `Build.loop_in` (`LvmQAsmInbCore`), instances `qltLoop_in`, `capLoop_in`
  (`LvmQAsmInbLink`).
-/

set_option autoImplicit false

namespace Lvm.Loop.Build

open Lvm.Loop

end Lvm.Loop.Build
end
-- ===== end of `LvmQAsmInbSite` =====

-- ===== merged from `LvmQAsmInbBits` (GOLF module merge: `LvmQAsmInbBits.lean` is now a stub importing `LvmQAsmInb`) =====
section
-- New for lvm (INB): the `BITS` outputs on the seed (committed) memory, without `inb`. Adapted from
-- WP-9b `LvmM3Aux.aux_read`/`aux_read_at` and WP-12b `LvmBitsTab.out_sound`: the same proofs with
-- their last step (`seedMem_eq_interp`, which needs `inb` through `interp_unique`) dropped, so the
-- conclusions are about `seedMem` (`Q.seedMem (witOf q) (inKOf q) (inEOf q)`) instead of `interpMem`.

/-!
# `BITS` outputs on the committed memory

`AuxH0` is WP-9b's `AuxHyps` without `wf`, `inj`'s use for the interpreter and `inb`. **`out_sound0`**:
at a real row of a `BITS` table in `aux`, the output cells of the seed memory hold the word functions
of the row's word. **`seedK_bit`**: a `bit z` output cell holds `0` or `1`.
-/

set_option autoImplicit false

namespace Lvm.Inb

open LeanVM.Parameters LeanVM.Protocol CompPoly Lvm Lvm.Bits Lvm.M3 Lvm.Loop Lvm.BitsTab

section Aux

variable (Q : Program) (pl : ℕ → Var → Bool × ℕ) (groups : List Grp) (arrs : List InArr)
  (aux : List Tab) (L : Lay) (hτ : ∀ t ∈ lvmTabs Q pl groups arrs aux, t.τ ≤ L.μ)

end Aux

end Lvm.Inb
end
-- ===== end of `LvmQAsmInbBits` =====

-- ===== merged from `LvmQAsmInbNode` (GOLF module merge: `LvmQAsmInbNode.lean` is now a stub importing `LvmQAsmInb`) =====
section
-- New for lvm (INB): WP-14c's `hinb` (`nodeSound_layout`) for the node program, generic over its
-- parts as `nodeSound_layout` is. The route: the seed (committed) memory satisfies every row
-- (WP-10 `holds_seedMem`, no `inb`), its `readd` addresses are in region (`qlink_in`; Q_sig and
-- Q_arith have no `readd`), so the interpreter finds every cell (`inb_of_mem`).

/-!
# `hinb` for the node program

**`hinb_node`**: for `Q = Qn lay I qa nK nE` on the tables `lvmTabs Q pl groups (arrsX x) aux`, for
every statement `x` with `b = 1` and every pair meeting `GoodN`, `(Q.interp inK inE).inb = true`
(`inK`, `inE` read off the pair's stack), in exactly `nodeSound_layout`'s form. Hypotheses, all
static except `hqlt` (`nodeSound_layout`'s own):

* `hT`, `hst` (`AuxStatic`), `hQ` (`QOk P20 lay`): `nodeSound_layout`'s;
* `hqlt`: `nodeSound_layout`'s (Q_link's `QLT` cells hold `qltData`), with `hqtK` (those cells are
  inputs);
* `hcov`: every cap bit cell of every padded position of every opening is a `bit` output of a real
  row of a `BITS` table in `aux` whose cells are inside `Q` (the position classes);
* `hsig`, `harr`: Q_sig's and Q_arith's segments have no `readd` (decided).

No `inb` is used: the proof runs on the seed memory (`holds_seedMem`), and the `BITS` outputs are
read there (`out_sound0`). The bits are needed for *every* padded position because the cap loops
run every iteration of a chunk (only their assertions are gated).
-/

set_option autoImplicit false

namespace Lvm.NS

open RecursionFast Lvm Lvm.T Lvm.ASM Lvm.Replay Lvm.Loop Lvm.Loop.Build Lvm.QLink Lvm.QSig Lvm.M3
open Lvm.SigBits Lvm.BitsTab Lvm.Inb LeanVM.Protocol

/-! ## Any parameter set -/

-- `qprogP` (the node program's shape for parameter set `p`) is `LvmNodeSoundCirc`'s.

/-! ## Any builder program: `inb` from the seed memory's `readd`s -/

section Seed

variable {α : Type} {m : BM α} {nK nE : ℕ}
  {pl : ℕ → Var → Bool × ℕ} {groups : List Grp} {arrs : List InArr} {aux : List Tab} {L : Lay}
  {hτ : ∀ t ∈ lvmTabs (toProgram nK nE m) pl groups arrs aux, t.τ ≤ L.μ}

end Seed

section Gen

variable {α : Type} {p : Params} {lay : Layout} {I : SigIn} {qa : BM α} {nK nE : ℕ}
  {pl : ℕ → Var → Bool × ℕ} {groups : List Grp} {arrs : List InArr} {aux : List Tab} {L : Lay}
  {hτ : ∀ t ∈ lvmTabs (toProgram nK nE (qprogP p lay I qa)) pl groups arrs aux, t.τ ≤ L.μ}

end Gen

/-! ## The node program (`nodeSound_layout`'s form) -/

section Inb

variable {α : Type} {lay : Layout} {I : SigIn} {qa : BM α} {nK nE : ℕ}
  {pl : ℕ → Var → Bool × ℕ} {groups : List Grp} {arrsX : List UInt8 → List InArr} {aux : List Tab}
  {hτ' : ∀ x, ∀ t ∈ lvmTabs (Qn lay I qa nK nE) pl groups (arrsX x) aux, t.τ ≤ lay26.μ}

end Inb

end Lvm.NS
end
-- ===== end of `LvmQAsmInbNode` =====

/-!
# `hinb` for `Q20` and `Q8`

* **`posSpecs_hit`**: every output of an opening's lane-`l` row (`laneOuts`) is an output of a row of
  lane class `l` (`posSpecs`, lvm2 EV-DIET B), at its `posCell`; **`posSpecs_bit`** for the bit cells.
* **`capCov_pos`**: the position classes `posSpecs C bpl` (one `BITS` row per 8 padded positions,
  `nRows`, per lane) put a `bit` output on every cap bit cell `bitBase k + H·j + z`, `j < padT t`, `z < H`,
  given that their cells lie inside `Q` (`PosCellsLt`, a static bound like Q_sig's `SigCellsLt`,
  independent of the placement).
* **`hinb20`**: `nodeSound_layout`'s `hinb` at WP-16a's `P20` node program (`lay cfg20`, `sigIn cfg20`,
  `qarith cfg20`, `nK cfg20`, `0`, `aux cfg20 D`), from `nodeSound_layout`'s `hT`, `hst`, `hQ`, `hqlt`
  and `PosCellsLt`. **`inb8`**: the same fact for `Q cfg8` on any stack with `M3Holds`.
-/

set_option autoImplicit false

namespace Lvm.QAsm

open RecursionFast Lvm Lvm.T Lvm.ASM Lvm.Replay Lvm.Loop Lvm.Loop.Build Lvm.QLink Lvm.QSig Lvm.M3
open Lvm.SigBits Lvm.Bits Lvm.BitsTab Lvm.Inb Lvm.NS LeanVM.Protocol

/-! ## The position classes cover the cap bits -/

theorem le_two_pow_clog2 (n : Nat) : n ≤ 2 ^ clog2 n := by
  unfold clog2
  split
  · simp; omega
  · have := @Nat.lt_log2_self (n - 1); rw [Nat.pow_succ] at this ⊢; omega

/-- The first outputs of lane `l`'s row are its bits. -/
theorem laneOuts_bit {H l z : Nat} (hz : z < 64) (h : 64 * l + z < 8 * H) :
    z < (laneOuts H l).length ∧ (laneOuts H l).getD z (.bit 0, 0, 0) = (.bit z, 0, 64 * l + z) := by
  unfold laneOuts
  rw [laneOuts_bits]
  have hl : z < ((List.range (laneBits H l)).map fun z => ((BOut.bit z, 0, 64 * l + z) : BOut × Nat × Nat)).length := by
    simp [laneBits]; omega
  refine ⟨by rw [List.length_append]; (clear * - hl; omega), ?_⟩
  rw [List.getD_append _ _ _ _ hl, List.getD_eq_getElem _ _ hl]
  simp

theorem mem_laneOuts_bit {H l z : Nat} (hz : z < 64) (h : 64 * l + z < 8 * H) :
    ((BOut.bit z, 0, 64 * l + z) : BOut × Nat × Nat) ∈ laneOuts H l := by
  obtain ⟨h1, h2⟩ := laneOuts_bit hz h
  rw [← h2, List.getD_eq_getElem _ _ h1]; exact List.getElem_mem h1

/-- An output of lane `l`'s row: a bit `z < laneBits` or a field `lo`/`hi` of a position `i < 8` in the
lane. -/
theorem mem_laneOuts {H l : Nat} {e : BOut × Nat × Nat} (h : e ∈ laneOuts H l) :
    (∃ z < laneBits H l, e = (.bit z, 0, 64 * l + z)) ∨
    ∃ i < 8, ((fields H i).1.1 = l ∧
        e = (.fld (fields H i).1.2.1 (fields H i).1.2.2.1 (fields H i).1.2.2.2, 1, i)) ∨
      ((fields H i).2.1 = l ∧
        e = (.fld (fields H i).2.2.1 (fields H i).2.2.2.1 (fields H i).2.2.2.2, 2, i)) := by
  unfold laneOuts at h
  rw [laneOuts_bits, List.mem_append] at h
  rcases h with h | h
  · obtain ⟨z, hz, rfl⟩ := List.mem_map.mp h
    exact Or.inl ⟨z, List.mem_range.mp hz, rfl⟩
  · right
    obtain ⟨i, hi, h⟩ := List.mem_flatMap.mp h
    refine ⟨i, List.mem_range.mp hi, ?_⟩
    rw [List.mem_append] at h
    rcases h with h | h <;> split at h <;> simp only [List.mem_singleton, List.not_mem_nil] at h
    · exact Or.inl ⟨‹_›, h⟩
    · exact Or.inr ⟨‹_›, h⟩

/-- **No two outputs of a lane's row have one word function** (`1 ≤ H`): bits by their index; a `lo`
field has `d = 0`, a `hi` field `d = m₁ ≥ 1` (or `m = H − m₁ = 1 ≠ m₁` when `H = 1`); two `lo`s (two `hi`s)
of the lane start at bit `64 l + z` (`64 l + z = s + m₁`), so their positions agree. -/
theorem laneOuts_inj {H l : Nat} (hH : 1 ≤ H) {e e' : BOut × Nat × Nat} (he : e ∈ laneOuts H l)
    (he' : e' ∈ laneOuts H l) (h : e.1 = e'.1) : e = e' := by
  have key : ∀ {i i' : Nat}, i * H = i' * H → i = i' := fun h => Nat.eq_of_mul_eq_mul_right hH h
  rcases mem_laneOuts he with ⟨z, -, rfl⟩ | ⟨i, -, ⟨hl, rfl⟩ | ⟨hl, rfl⟩⟩ <;>
  rcases mem_laneOuts he' with ⟨z', -, rfl⟩ | ⟨i', -, ⟨hl', rfl⟩ | ⟨hl', rfl⟩⟩ <;>
  simp only [BOut.bit.injEq, BOut.fld.injEq, reduceCtorEq] at h
  · rw [h]
  all_goals
    simp only [fields] at hl hl' h ⊢
    generalize hs : i * H = s at hl h ⊢
    generalize hs' : i' * H = s' at hl' h ⊢
  · obtain ⟨h1, -, -⟩ := h
    have : s = s' := by (clear * - hl hl' h1; omega)
    subst this; rw [key (hs.trans hs'.symm)]
  · obtain ⟨h1, h2, h3⟩ := h
    split_ifs at h1 h2 h3 hl hl' <;> (clear he he' hs' key; omega)
  · obtain ⟨h1, h2, h3⟩ := h
    split_ifs at h1 h2 h3 hl hl' <;> (clear he he' key; omega)
  · obtain ⟨h1, h2, h3⟩ := h
    have : s = s' := by split_ifs at h1 h2 h3 hl hl' <;> (clear * - hl h1 hl' h3; omega)
    subst this; rw [key (hs.trans hs'.symm)]

/-- `find?` by word function returns the output itself. -/
theorem find?_out {L : List (BOut × Nat × Nat)} {e : BOut × Nat × Nat} (he : e ∈ L)
    (hu : ∀ e' ∈ L, e'.1 = e.1 → e' = e) : L.find? (fun e' => e'.1 == e.1) = some e := by
  induction L with
  | nil => cases he
  | cons a L ih =>
    rw [List.find?_cons]
    by_cases ha : a.1 = e.1
    · rw [beq_iff_eq.mpr ha, hu a (List.mem_cons_self ..) ha]
    · rw [show (a.1 == e.1) = false from beq_eq_false_iff_ne.mpr ha]
      rcases List.mem_cons.mp he with rfl | he
      · exact absurd rfl ha
      · exact ih he fun e' h' => hu e' (List.mem_cons_of_mem _ h')

attribute [local irreducible] Lvm.schedule in
theorem mem_lnOps {p : Params} {l : Nat} {ko : Nat × OpenInfo} :
    ko ∈ lnOps p l ↔ ko.1 < (opens p).length ∧ ko.2 = (opens p).getD ko.1 default ∧ l < nLanes ko.2.L.height := by
  obtain ⟨k, o⟩ := ko
  simp only [lnOps, List.mem_filter, List.mem_map, List.mem_range, Prod.mk.injEq, decide_eq_true_eq]
  constructor
  · rintro ⟨⟨k', hk, rfl, rfl⟩, hl⟩; exact ⟨hk, rfl, hl⟩
  · rintro ⟨hk, rfl, hl⟩; exact ⟨⟨k, hk, rfl, rfl⟩, hl⟩

theorem le_foldl_max : ∀ (L : List Nat) (a : Nat), a ≤ L.foldl max a
  | [], _ => le_refl _
  | b :: L, a => le_trans (le_max_left a b) (le_foldl_max L (max a b))

theorem mem_le_foldl_max : ∀ {L : List Nat} {x : Nat} (a : Nat), x ∈ L → x ≤ L.foldl max a
  | b :: L, x, a, h => by
    rcases List.mem_cons.mp h with rfl | h
    · exact le_trans (le_max_right a x) (le_foldl_max L _)
    · exact mem_le_foldl_max (L := L) (max a b) h

theorem laneBits_le_lnBits {p : Params} {l : Nat} {ko : Nat × OpenInfo} (h : ko ∈ lnOps p l) :
    laneBits ko.2.L.height l ≤ lnBits p l :=
  mem_le_foldl_max 0 (List.mem_map.mpr ⟨ko, h, rfl⟩)

theorem lt_nPosCls {C : QCfg} {k l : Nat} (hk : k < (opens C.p).length)
    (hl : l < nLanes ((opens C.p).getD k default).L.height) : l < nPosCls C := by
  have hm : ((opens C.p).getD k default) ∈ opens C.p := by
    rw [List.getD_eq_getElem _ _ hk]; exact List.getElem_mem hk
  exact lt_of_lt_of_le hl (mem_le_foldl_max 0 (List.mem_map.mpr ⟨_, hm, rfl⟩))

theorem mem_foldl_addNew {α : Type} (f : α → BOut) :
    ∀ (L : List α) (a : List BOut) (u : BOut), u ∈ a → u ∈ L.foldl (fun a e => addNew a (f e)) a
  | [], _, _, h => h
  | e :: L, a, u, h => mem_foldl_addNew f L _ u (by show u ∈ addNew a (f e); unfold addNew; split <;> simp [h])

theorem mem_foldl_addNew' {α : Type} (f : α → BOut) :
    ∀ (L : List α) (a : List BOut) {e : α}, e ∈ L → f e ∈ L.foldl (fun a e => addNew a (f e)) a
  | e' :: L, a, e, h => by
    rcases List.mem_cons.mp h with rfl | h
    · exact mem_foldl_addNew f L _ _ (by show f e ∈ addNew a (f e); unfold addNew; split <;> simp_all)
    · exact mem_foldl_addNew' f L _ h

theorem mem_lnFlds_of (p : Params) (l : Nat) :
    ∀ (ops : List (Nat × OpenInfo)) (a : List BOut),
      (∀ u ∈ a, u ∈ ops.foldl (fun a ko => (laneFlds ko.2.L.height l).foldl (fun a e => addNew a e.1) a) a) ∧
      ∀ ko ∈ ops, ∀ e ∈ laneFlds ko.2.L.height l,
        e.1 ∈ ops.foldl (fun a ko => (laneFlds ko.2.L.height l).foldl (fun a e => addNew a e.1) a) a
  | [], _ => ⟨fun _ h => h, fun _ h => by cases h⟩
  | ko :: ops, a => by
    obtain ⟨h1, h2⟩ := mem_lnFlds_of p l ops ((laneFlds ko.2.L.height l).foldl (fun a e => addNew a e.1) a)
    refine ⟨fun u hu => h1 u (mem_foldl_addNew (fun e : BOut × Nat × Nat => e.1) _ _ u hu), fun ko' hko e he => ?_⟩
    rcases List.mem_cons.mp hko with rfl | hko
    · exact h1 _ (mem_foldl_addNew' (fun e : BOut × Nat × Nat => e.1) _ _ he)
    · exact h2 ko' hko e he

/-- **Every output of an opening's lane-`l` row is a class output.** -/
theorem mem_lnOuts {p : Params} {l : Nat} {ko : Nat × OpenInfo} (h : ko ∈ lnOps p l)
    {e : BOut × Nat × Nat} (he : e ∈ laneOuts ko.2.L.height l) : e.1 ∈ lnOuts p l := by
  unfold laneOuts at he
  rw [laneOuts_bits, List.mem_append] at he
  unfold lnOuts
  rcases he with he | he
  · obtain ⟨z, hz, rfl⟩ := List.mem_map.mp he
    refine List.mem_append_left _ (List.mem_map.mpr ⟨z, List.mem_range.mpr ?_, rfl⟩)
    exact lt_of_lt_of_le (List.mem_range.mp hz) (laneBits_le_lnBits h)
  · exact List.mem_append_right _ ((mem_lnFlds_of p l _ []).2 ko h e he)

theorem posRowsAux_hit (u l : Nat) :
    ∀ (b : Nat) (ops : List (Nat × OpenInfo)) {k : Nat} {o : OpenInfo} {x : Nat}, (k, o) ∈ ops → x < nRows o →
      ∃ sb, (k, o, x, sb) ∈ posRowsAux u l b ops
  | b, [], k, o, x, h, _ => by cases h
  | b, (k', o') :: ops, k, o, x, h, hx => by
    simp only [posRowsAux, List.mem_append, List.mem_map, List.mem_range]
    rcases List.mem_cons.mp h with h | h
    · obtain ⟨rfl, rfl⟩ := Prod.mk.inj h
      exact ⟨_, Or.inl ⟨x, hx, rfl⟩⟩
    · obtain ⟨sb, hs⟩ := posRowsAux_hit u l _ ops h hx
      exact ⟨sb, Or.inr hs⟩

attribute [local irreducible] Lvm.schedule in
/-- **The class row of an opening's output**: output `e` of lane `l` of answer `x` of opening `k` is
output `jo` (`lnOuts[jo] = e.1`) of a row `y` of lane class `l`, with the cell `posCell C k o x e`. -/
theorem posSpecs_hit (C : QCfg) (bpl : Nat → Nat → Bool × Nat) {k l x : Nat} (hk : k < (opens C.p).length)
    (hl : l < nLanes ((opens C.p).getD k default).L.height) (hx : x < nRows ((opens C.p).getD k default))
    {e : BOut × Nat × Nat} (he : e ∈ laneOuts ((opens C.p).getD k default).L.height l) :
    ∃ S ∈ posSpecs C bpl, S.n ≤ 2 ^ S.τ ∧ S.rd = true ∧ ∃ y < S.n,
      S.wc y = ansLane C.p (((opens C.p).getD k default).pe + x) + l ∧
      ∃ jo < S.outs.length, S.out jo = e.1 ∧ S.oc jo y = posCell C k ((opens C.p).getD k default) x e := by
  have hko : (k, (opens C.p).getD k default) ∈ lnOps C.p l := mem_lnOps.mpr ⟨hk, rfl, hl⟩
  obtain ⟨sb, hr⟩ := posRowsAux_hit (lnOuts C.p l).length l (spBase C l) (lnOps C.p l) hko hx
  have hr' : (k, (opens C.p).getD k default, x, sb) ∈ posRows C l := hr
  obtain ⟨y, hy, hry⟩ := List.mem_iff_getElem.mp hr'
  have hu := mem_lnOuts hko he
  have hjo := List.idxOf_lt_length_of_mem hu
  have hH : 1 ≤ ((opens C.p).getD k default).L.height := by unfold nLanes at hl; (clear * - hl; omega)
  have hg : (posRows C l).getD y default = (k, (opens C.p).getD k default, x, sb) := by
    rw [List.getD_eq_getElem _ _ hy, hry]
  have hn : (posSpec C bpl l).n ≤ 2 ^ (posSpec C bpl l).τ := by
    rw [posSpec_n, posSpec_τ]; exact le_two_pow_clog2 _
  have hy' : y < (posSpec C bpl l).n := by rw [posSpec_n]; exact hy
  have hjo' : (lnOuts C.p l).idxOf e.1 < (posSpec C bpl l).outs.length := by rw [posSpec_outs]; exact hjo
  refine ⟨posSpec C bpl l, List.mem_map_of_mem (List.mem_range.mpr (lt_nPosCls hk hl)), hn, posSpec_rd C bpl l,
    y, hy', ?_, (lnOuts C.p l).idxOf e.1, hjo', ?_, ?_⟩
  · rw [posSpec_wc, hg]
  · rw [BSpec.out, posSpec_outs, List.getD_eq_getElem _ _ hjo, List.getElem_idxOf hjo]
  · rw [posSpec_oc, hg]
    unfold posOc
    dsimp only
    rw [List.getD_eq_getElem _ _ hjo, List.getElem_idxOf hjo,
      find?_out he fun e' h' hq => laneOuts_inj hH h' he hq]

/-- **The bit cell of a position's bit** (`j < padT t`, `z < H`, `n = (j % 8)·H + z`): output `bit (n % 64)`
of lane `n / 64` at answer `j / 8`, at a row of lane class `n / 64`. -/
theorem posSpecs_bit (C : QCfg) (bpl : Nat → Nat → Bool × Nat) {k j z : Nat} (hk : k < (opens C.p).length)
    (hj : j < padT ((opens C.p).getD k default).L.t) (hz : z < ((opens C.p).getD k default).L.height) :
    ∃ S ∈ posSpecs C bpl, S.n ≤ 2 ^ S.τ ∧ S.rd = true ∧ ∃ y < S.n,
      S.wc y = ansLane C.p (((opens C.p).getD k default).pe + j / 8) +
        (j % 8 * ((opens C.p).getD k default).L.height + z) / 64 ∧
      ∃ jo < S.outs.length, S.out jo = .bit ((j % 8 * ((opens C.p).getD k default).L.height + z) % 64) ∧
        S.oc jo y = bitBase C.p (lay C) k + ((opens C.p).getD k default).L.height * j + z := by
  generalize hn : j % 8 * ((opens C.p).getD k default).L.height + z = n
  have h7 : j % 8 * ((opens C.p).getD k default).L.height ≤ 7 * ((opens C.p).getD k default).L.height :=
    Nat.mul_le_mul_right _ (by (clear * -; omega))
  have hl0 : n / 64 < nLanes ((opens C.p).getD k default).L.height := by unfold nLanes; (clear * - hz hn h7; omega)
  have hx : j / 8 < nRows ((opens C.p).getD k default) := by unfold nRows; (clear * - hj; omega)
  have hdm := Nat.div_add_mod n 64
  have hm := mem_laneOuts_bit (H := ((opens C.p).getD k default).L.height) (l := n / 64) (z := n % 64)
    (Nat.mod_lt _ (by norm_num)) (by (clear * - hz hn h7; omega))
  obtain ⟨S, hS, hτ, hrd, y, hy, hwc, jo, hjo, hout, hoc⟩ := posSpecs_hit C bpl hk hl0 hx hm
  refine ⟨S, hS, hτ, hrd, y, hy, hwc, jo, hjo, hout, ?_⟩
  rw [hoc]
  generalize (opens C.p).getD k default = o at hj hz hn h7 ⊢
  generalize hH : o.L.height = H at hz hn h7 ⊢
  have hnH : n / H = j % 8 := by
    rw [← hn, Nat.add_comm, Nat.add_mul_div_right _ _ (by (clear * - hH hz; omega)), Nat.div_eq_of_lt hz, Nat.zero_add]
  have hnm : n % H = z := by
    rw [← hn, Nat.add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hz]
  rw [show 64 * (n / 64) + n % 64 = n by omega]
  have hjj : 8 * (j / 8) + n / H = j := by rw [hnH]; (clear * -; omega)
  simp only [posCell, hH, hjj, if_pos hj, hnm]

/-! ## Decided: Q_sig reads no cell by address

Q_arith's fact `noReaddSegs (qarith C (p2C C)).2 = true` is a hypothesis (`hna`) of `hinb20`/`inb8`
(WP-16a2): with HAR's full Q_arith the kernel cannot evaluate it (`List.mergeSort` in the table phase
does not reduce; with a structural sort the table gadget alone exceeds 12 GB at `P8`). Natively it holds
(`P8`: 33,736 segments, no `readd`); a structural proof (no gadget of Q_arith emits a `readd`) is owed. -/

/-! ## `hinb` at `P20` (`nodeSound_layout`'s form) -/

section P20

variable {pl : ℕ → Var → Bool × ℕ} {groups : List Grp} {arrsX : List UInt8 → List InArr} {D : QData}
  {hτ' : ∀ x, ∀ t ∈ lvmTabs (Qn (lay cfg20) (sigIn cfg20) (qarith cfg20) (nK cfg20) 0) pl groups (arrsX x)
    (aux cfg20 D), t.τ ≤ lay26.μ}

end P20

/-! ## `inb` at `P8` (any stack with `M3Holds`) -/

section P8

variable {pl : ℕ → Var → Bool × ℕ} {groups : List Grp} {arrs : List InArr} {D : QData} {L : Lay}
  {hτ : ∀ t ∈ lvmTabs (Q cfg8) pl groups arrs (aux cfg8 D), t.τ ≤ L.μ}

end P8

end Lvm.QAsm
