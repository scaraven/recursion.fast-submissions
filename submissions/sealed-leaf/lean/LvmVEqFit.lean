-- New for lvm (WP-14a): the record's fit to the tables (`M3.fitsR`, INT-2) gives the facts the
-- phase specifications of WP-9/9b are stated with (the lvm instance `inst L T hτ` on
-- `L = ⟨nuMain, nuRec⟩`): the bus depth, the table rounds and evaluations, the heights, the
-- layout (`LayOk`), every constrained table reading or seeding.
import LvmVEqMid
import LvmM3Loop
import LvmM3Fid

-- (GOLF2: 33 declarations that `certified` does not use moved verbatim to `LvmMPCertOff`, outside its import closure.)

-- ===== merged from `LvmM3Check` (GOLF module merge: `LvmM3Check.lean` is now a stub importing `LvmVEqFit`) =====
section
-- new for lvm (WP-9b): kernel-cheap Boolean checks of the lvm instance's layout facts (`LayOk`,
-- `GrpOk`, `InOk`, the tables' shape) and their soundness: structured per table, group and array
-- (offsets laid end to end), never per pair of rows.

/-!
# Boolean layout checks

The layout facts of `LvmM3Inst`/`LvmM3Loop` quantify over rows (`GrpOk.disj`/`cover`, `InOk.inj`
over pairs of rows: about `2^36` pairs for P20's stream lanes). Each is implied by a check that
walks the structure once:

* **`tilesB`**: blocks lie end to end from a start to an end (each block starts where the previous
  one ends). It gives: every block inside `[c, N)` (`tiles_mem`), earlier blocks end before later
  ones start (`tiles_pairwise`), every point of `[c, N)` inside a block (`tiles_cover`).
* **`grpOkB`**: each group's members tile its rows `[0, 2^τ)` in list order, each member a piece of
  the group's shape at an offset its height divides, and the members' piece indices, sorted, are
  `0, …, (number of pieces) − 1` (every piece in exactly one place). `grpOk_of_B : grpOkB Q groups = true →
  GrpOk Q groups`.
* **`inOkB`** (`LvmM3CheckIn`): the input arrays tile the input cells.
* **`layOkB`**: every committed column is an aligned block inside its commitment (`LayOk`).
* **`tabsOkB`**: every table reads or seeds (`AllSc`), has a column, and its count columns are
  inside its width (`loop_bus`'s `hin`).

Cost: linear in the members, arrays, columns and reads, plus one sort of the piece indices.
-/

namespace Lvm.M3

open Lvm.Loop

/-! ## Blocks end to end -/

section Tiles

variable {α : Type} (b s : α → ℕ)

variable {b s}

end Tiles

/-! ## Kernel-cheap lookups and permutations -/

/-- A binary trie keyed by `ℕ` (Braun order: `0` the root, odd `n` in the left subtrie at `n / 2`,
even `n ≥ 2` in the right one at `n / 2 − 1`): `O(log n)` lookups the kernel reduces quickly. -/
inductive NTrie (α : Type) where
  | nil : NTrie α
  | node (v : Option α) (l r : NTrie α) : NTrie α

namespace NTrie

variable {α : Type}

/-- The root's entry and subtries. -/
def parts : NTrie α → Option α × NTrie α × NTrie α
  | .nil => (none, .nil, .nil)
  | .node v l r => (v, l, r)

/-- Set key `n` to `a` (`f` bounds the depth: keys `n + 1 < 2^f`). -/
def ins (a : α) : ℕ → NTrie α → ℕ → NTrie α
  | 0, t, _ => t
  | f + 1, t, n =>
    if n = 0 then .node (some a) t.parts.2.1 t.parts.2.2
    else if n % 2 = 1 then .node t.parts.1 (ins a f t.parts.2.1 (n / 2)) t.parts.2.2
    else .node t.parts.1 t.parts.2.1 (ins a f t.parts.2.2 (n / 2 - 1))

end NTrie

/-! ## Groups -/

/-! ## Committed columns aligned -/

/-- A column's alignment, as a Boolean. -/
def colOkB (L : Lay) (τ : ℕ) : ColSrc → Bool
  | .com rec off => off % 2 ^ τ == 0 && decide (off + 2 ^ τ ≤ 2 ^ (if rec then L.nuRec else L.nuMain)) &&
      decide (L.nuRec ≤ L.nuMain)
  | .fix _ _ => true

/-- **The layout's Boolean check**: every committed column is an aligned block inside its
commitment. -/
def layOkB (L : Lay) (tabs : List Tab) : Bool := tabs.all fun t ↦ t.cols.all (colOkB L t.τ)

/-- **The layout's check gives `LayOk`.** -/
theorem layOk_of_B {L : Lay} {tabs : List Tab} (h : layOkB L tabs = true) : LayOk L tabs := by
  intro t ht i hi
  simp only [layOkB, List.all_eq_true] at h
  have hc := h t ht _ (List.getElem_mem hi)
  unfold Aligned
  rw [List.getElem?_eq_getElem hi]
  revert hc
  cases t.cols[i] with
  | com rec off =>
    simp only [colOkB, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq]
    exact fun ⟨⟨h1, h2⟩, h3⟩ ↦ ⟨Nat.dvd_of_mod_eq_zero h1, h2, h3⟩
  | fix f ev => exact fun _ ↦ trivial

/-! ## The tables' shape -/

/-- **The tables' Boolean check**: every table reads or seeds, has a column, its read-count
columns are inside its width, and every key has at most 13 value limbs (the fingerprint's 16
coordinates: separator, address, count, values; `LvmM3FidBus.KeysOk`). -/
def tabsOkB (tabs : List Tab) : Bool :=
  tabs.all fun t ↦ (!t.reads.isEmpty || !t.seeds.isEmpty) && decide (0 < t.w) &&
    t.reads.all (fun r ↦ decide (r.2 < t.w)) &&
    t.reads.all (fun r ↦ decide (r.1.val.length ≤ 13)) && t.seeds.all fun s ↦ decide (s.1.val.length ≤ 13)

theorem allSc_of_B {tabs : List Tab} (h : tabsOkB tabs = true) : AllSc tabs := by
  intro t ht
  simp only [tabsOkB, List.all_eq_true, Bool.and_eq_true, Bool.or_eq_true, Bool.not_eq_true',
    List.isEmpty_eq_false_iff] at h
  exact (h t ht).1.1.1.1

theorem width_pos_of_B {tabs : List Tab} (h : tabsOkB tabs = true) : ∀ t ∈ tabs, 0 < t.w := by
  intro t ht
  simp only [tabsOkB, List.all_eq_true, Bool.and_eq_true, decide_eq_true_eq] at h
  exact (h t ht).1.1.1.2

/-- The keys' limb counts (`LvmM3FidBus.KeysOk`, unfolded). -/
theorem keys_of_B {tabs : List Tab} (h : tabsOkB tabs = true) :
    ∀ t ∈ tabs, (∀ r ∈ t.reads, r.1.val.length ≤ 13) ∧ ∀ s ∈ t.seeds, s.1.val.length ≤ 13 := by
  intro t ht
  simp only [tabsOkB, List.all_eq_true, Bool.and_eq_true, decide_eq_true_eq] at h
  exact ⟨(h t ht).1.2, (h t ht).2⟩

end Lvm.M3
end
-- ===== end of `LvmM3Check` =====

/-!
# `fitsR → inst` (INT-2's open item)

For `T = sumcheckTabs tabs` and `fitsR p tabs = true`:

* `μBus_eq`: `(inst L T hτ).μBus = p.busDepth` (leanVM's `μBus = ⌈log₂ pushLeaves⌉`, the record's
  `busDepth = log2Ceil (pushLeavesR tabs)`; `log2Ceil = Nat.clog 2`);
* `leafdecReads_eq`, `tableRounds_eq`, `tableEvals_eq`;
* `τ_le` (every height at most `L.μ = nuMain + 1`, `inst`'s `hτ`), `layOk_fit` (`colsFitB` gives
  WP-9b's `layOkB`, hence `LayOk`), `hcon_fit` (`inst_conditions`'s hypothesis).
-/

set_option autoImplicit false

namespace Lvm.VEq

open Lvm.M3 LeanVM.Protocol

/-- The layout of a parameter record: `C_main`, `C_rec`. -/
def layOf (p : Params) : Lay := ⟨p.nuMain, p.nuRec⟩

/-- `log2Ceil` is `Nat.clog 2`. -/
theorem log2Ceil_eq_clog (n : ℕ) : log2Ceil n = Nat.clog 2 n := by
  unfold log2Ceil bitLength
  rcases Nat.lt_or_ge n 2 with hn | hn
  · have h0 : n - 1 = 0 := by omega
    simp only [h0, ↓reduceIte]
    exact (Nat.clog_of_right_le_one (by (clear * - hn; omega)) _).symm
  · have h0 : n - 1 ≠ 0 := by omega
    simp only [h0, ↓reduceIte]
    apply le_antisymm
    · exact Nat.succ_le_of_lt ((Nat.lt_clog_iff_pow_lt (by norm_num)).mpr
        (lt_of_le_of_lt (Nat.log2_self_le h0) (by (clear * - hn; omega))))
    · exact (Nat.clog_le_iff_le_pow (by norm_num)).mpr (by have := Nat.lt_log2_self (n := n - 1); (clear * - hn this; omega))

section Fit

variable (p : Params) (tabs : List Tab)

/-- The push leaves of the lvm instance, table by table. -/
theorem pushLeaves_inst (L : Lay) (T : List Tab) (hτ : ∀ t ∈ T, t.τ ≤ L.μ) :
    (inst L T hτ).pushLeaves = (T.map fun t ↦ (t.reads.length + t.seeds.length) * 2 ^ t.τ).sum := by
  have e : ∀ j : Fin T.length, (((inst L T hτ).flushes j).filter fun f ↦ decide (f.1 = Side.push)).length *
      2 ^ (inst L T hτ).τ j = (fun t : Tab ↦ (t.reads.length + t.seeds.length) * 2 ^ t.τ) (T.get j) :=
    fun j ↦ congrArg (· * 2 ^ (T.get j).τ) (flushes_push_length (T.get j))
  simp only [M3Instance.pushLeaves, List.filter_nil, List.map_nil, List.sum_nil, zero_add]
  rw [List.map_congr_left fun j _ ↦ e j]
  exact congrArg List.sum ((List.map_map (g := fun t : Tab ↦ (t.reads.length + t.seeds.length) * 2 ^ t.τ)
    (f := T.get) (l := List.finRange T.length)).symm.trans (by rw [List.map_get_finRange]))

/-- **The facts `fitsR` decides.** -/
structure Fit : Prop where
  leafdec : p.leafdecReads = 1
  busDepth : p.busDepth = log2Ceil (pushLeavesR tabs)
  busPos : 1 ≤ p.busDepth
  busLe : p.busDepth ≤ 22
  rounds : p.tableRounds = ((sumcheckTabs tabs).map (·.τ)).foldl max 0
  evals : p.tableEvals = ((sumcheckTabs tabs).map (·.w)).sum
  τle : ∀ t ∈ tabs, t.τ ≤ p.nuMain + 1
  hcon : ∀ t ∈ tabs, t.cons = [] ∨ t.reads ≠ [] ∨ t.seeds ≠ []
  cols : colsFitB p tabs = true
  /-- A23: the table point fits in `Φ`'s variables. -/
  accRounds : p.tableRounds ≤ accVars
  /-- A23: `fixCols` has at most `2^accLog` columns. -/
  nFix : (fixColsR (sumcheckTabs tabs) p.pubTab).length ≤ 2 ^ p.accLog
  /-- A23: `PUB` is a sumcheck table. -/
  pubTab : p.pubTab < (sumcheckTabs tabs).length
  /-- A23: `PUB` holds the header's lanes. -/
  pubTau : pubLanes ≤ 2 ^ (((sumcheckTabs tabs).map (·.τ)).getD p.pubTab 0)
  /-- A23: `PUB`'s column 0 is fixed. -/
  pubFix : ((sumcheckTabs tabs).map col0Fix).getD p.pubTab false = true

theorem fit_of (h : fitsR p tabs = true) : Fit p tabs := by
  simp only [fitsR, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq, List.all_eq_true,
    Bool.or_eq_true, List.isEmpty_iff, Bool.not_eq_true', List.isEmpty_eq_false_iff] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩, h7⟩, h8⟩, h9⟩, h10⟩, h11⟩, h12⟩, h13⟩, h14⟩ := h
  exact ⟨h1, h2, h3, h4, h5, h6, h7, fun t ht ↦ by
    rcases h8 t ht with (h | h) | h
    · exact .inl h
    · exact .inr (.inl h)
    · exact .inr (.inr h), h9, h10, h11, h12, h13, h14⟩

variable {p tabs}

theorem mem_sumcheckTabs {t : Tab} (ht : t ∈ sumcheckTabs tabs) : t ∈ tabs :=
  (List.mem_filter.mp ht).1

/-- Every sumcheck table is at most `L.μ = nuMain + 1` high. -/
theorem Fit.hτ (F : Fit p tabs) : ∀ t ∈ sumcheckTabs tabs, t.τ ≤ (layOf p).μ :=
  fun t ht ↦ F.τle t (mem_sumcheckTabs ht)

/-- The layout facts (`LayOk`) of the sumcheck tables. -/
theorem Fit.layOk (F : Fit p tabs) : LayOk (layOf p) (sumcheckTabs tabs) := by
  apply layOk_of_B
  have h := F.cols
  simp only [colsFitB, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true] at h
  simp only [layOkB, List.all_eq_true]
  intro t ht c hc
  have := h.2 t (mem_sumcheckTabs ht) c hc
  cases c with
  | com rec off =>
    simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at this
    simp only [colOkB, layOf, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq]
    exact ⟨⟨this.1, decide_eq_true this.2⟩, decide_eq_true h.1⟩
  | fix f ev => rfl

end Fit

end Lvm.VEq
