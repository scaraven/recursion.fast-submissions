-- new for lvm (WP-12b): WP-12's `BITS` row (`LvmBits`) as an auxiliary table of WP-9's lvm M3
-- instance (`LvmM3Tab.Tab`), read through the bus (WP-9b `LvmM3Aux`: `aux_read_at`, `aux_cons`).
-- Searched for reuse: WP-9's `InArr.tab` (the fixed address-column pattern, followed here),
-- `LvmM3Loop.evalB_ofPoly2` (the `evalB` transport pattern); FR has no bus-read bit table.
import LvmBits
import LvmM3FidFixC
import LvmM3Loop

-- (GOLF2: 29 declarations that `certified` does not use moved verbatim to `LvmQAsmHar47Off`, outside its import closure.)

-- ===== merged from `LvmM3Aux` (GOLF module merge: `LvmM3Aux.lean` is now a stub importing `LvmBitsTab`) =====
section
-- new for lvm (WP-9b): the auxiliary tables' reads through the bus (the `BITS` bridge for WP-12),
-- from WP-9's `seed_key`/`mem_lookup` and WP-10's `seed_cases`/`holds_seedMem`/`interp_unique`
-- (the first lines of `loopir_sound`'s proof, `LvmLoopSound.lean:348`).

/-!
# Auxiliary tables read the interpreter's cells

**The `BITS` bridge (option "reads through the bus").** An auxiliary table (`aux`, WP-12's `BITS`)
seeds nothing; it *reads* cells of the LoopIR memories through the bus, like a LoopIR piece: the
word it decomposes and each of its outputs (`shl k`, `shr k`, `bit z`, a linear form of its bit
columns). The outputs are LoopIR *input* cells (seeded by an input array, any value the prover
chose); the table's reads pin them to the word's functions. `aux_read`: on the lvm instance with
`M3Holds`, each read of an auxiliary table at each row is, coordinate by coordinate, the key of a
cell of the interpreter's run on the inputs read off the stack (`interpMem (inKOf q) (inEOf q)`):
separator `sep τ`, address `g^e`, value limbs the cell's. `aux_read_at`: with the address known
(`g^a`, `a` below the cell count, a fixed column of the table), the value limbs are cell `a`'s.

WP-12 combines this with its row lemma (`LvmBits.row_sound`: the row's constraints make every
output the word function of the word) to get `SigBits` for `M = interpMem`.
-/

namespace Lvm.M3

open LeanVM.Parameters LeanVM.Protocol CompPoly
open Lvm.Loop

/-! ## The seed memory is the interpreter's -/

section Aux

variable (Q : Program) (pl : ℕ → Var → Bool × ℕ) (groups : List Grp) (arrs : List InArr)
  (aux : List Tab) (L : Lay) (hτ : ∀ t ∈ lvmTabs Q pl groups arrs aux, t.τ ≤ L.μ)

end Aux

end Lvm.M3
end
-- ===== end of `LvmM3Aux` =====

/-!
# The `BITS` table and its soundness through the bus

**The table** (`BSpec.tab`). A `BITS` class `S` (one output list for all rows) is a table of
height `2^τ`. Columns:
* `0`: the word `w`; `1 + z` (`z < 64`): the bit column `β_z` (committed);
* `65`: the count column of the word's read; `66`: its address `g^{wc x}` (fixed);
* `67 + j`: output `j`'s read count (committed);
* then the output addresses (fixed): with `sh > 0` (lvm2 EVD2), one **shared** column `g^{oc 0 x}`
  at `67 + |outs|` whose `g^j` multiple is output `j`'s address for `j < sh` (the class's cells
  satisfy `oc j x = oc 0 x + j` there, `hsh`); then one column `g^{oc j x}` per output `j ≥ sh`.

Constraints (degree 2, `CPoly`): `w + Σ_z x^z·β_z` and `β_z·β_z + β_z`. Reads of the `K` memory:
the word (value polynomial `w`; only when `rd`) and every output `j`, whose value polynomial is
the linear form `Σ_z coef_z·β_z` of `LvmBits` (`outPoly`). Rows `x < n` are the real ones; rows
`n ≤ x < 2^τ` repeat row `0`'s addresses (`BSpec.row`): `CountsNonzero` forbids count-`0` padding
(`rows = 2^τ`), so the honest prover fills them with further reads of row `0`'s cells, their counts
continuing those cells' `g`-power read sequences (finalize counts include them). With `rd = false`
columns `65`, `66` are don't-care (committed / fixed, never read).
A fixed column's closed form is its multilinear extension (`Loop.mle`, `O(2^τ)` for the executable
verifier), so `FixOk` holds by definition (`fixOk_tab`).

**Soundness** (`out_sound`): under WP-9b's `AuxHyps` (the hypotheses of `loopir_sound`), at a real
row `x` of a `BITS` table in `aux`, with the cells it names below `Q.cells .K`, there is a word
`w` (the row's) such that the read word cell holds `w` (when `rd`) and output cell `oc j x` holds
`⟨outs[j].word w.val⟩`, in the interpreter's memory: WP-12's `row_sound` transported through
`FK.toBF64` (WP-1's ring isomorphism `ringEquivBF64`).

**Completeness** (`honest_cons`, `honest_out`): the honest row of any word (its bits) makes every
constraint vanish and every output polynomial its word function.
-/

set_option autoImplicit false

namespace Lvm.BitsTab

open LeanVM.Parameters LeanVM.Protocol Lvm Lvm.Bits Lvm.M3 Lvm.Loop

/-! ## `CPoly`s over `FK` -/

theorem evalB_var (u : Nat → K) (i : Nat) : CPoly.evalB u (CPoly.var i) = u i := by
  simp [CPoly.evalB, CPoly.var]

/-! ## The table -/

/-- The word constraint `w + Σ_z x^z·β_z`. -/
def wcons : CPoly := (1, [0]) :: (List.range 64).map fun z => (wt z, [1 + z])

/-- The bit constraint `β_z·β_z + β_z`. -/
def bcons (z : Nat) : CPoly := [(1, [1 + z, 1 + z]), (1, [1 + z])]

/-- The constraints. -/
def cons : List CPoly := wcons :: (List.range 64).map bcons

/-- An output's value polynomial: `Σ_z coef_z·β_z`. -/
def outPoly (o : BOut) : CPoly := (List.range 64).map fun z => (o.coef z, [1 + z])

/-- **A `BITS` class**: `n` real rows of `2^τ`; row `x` reads the word of `K` cell `wc x` (when
`rd`) and writes output `outs[j]` to `K` cell `oc j x`; `pl c` places committed column `c`. -/
structure BSpec where
  /-- Log-height. -/
  τ : Nat
  /-- The real rows. -/
  n : Nat
  /-- The outputs of every row. -/
  outs : List BOut
  /-- Whether the word is read from a cell (else it is a free committed word). -/
  rd : Bool
  /-- The word's cell. -/
  wc : Nat → Nat
  /-- Output `j`'s cell at row `x`. -/
  oc : Nat → Nat → Nat
  /-- The committed columns' placements. -/
  pl : Nat → Bool × Nat
  /-- The first `sh` outputs share one address column (lvm2 EVD2; `0`: one column per output). -/
  sh : Nat
  /-- Their cells are consecutive at every real row. -/
  hsh : ∀ j < sh, ∀ x < n, oc j x = oc 0 x + j

namespace BSpec

variable (S : BSpec)

/-- Output `j`. -/
def out (j : Nat) : BOut := S.outs.getD j (.bit 0)

/-- The real row whose addresses row `x` uses (padding rows repeat row `0`). -/
def row (x : Nat) : Nat := if x < S.n then x else 0

/-- The number of shared address columns (`0` or `1`). -/
def nA : Nat := if S.sh = 0 then 0 else 1

/-- The first output-address column. -/
def ab : Nat := 67 + S.outs.length

/-- The width: `67`, the output counts, the shared address column, the other outputs' addresses. -/
def width : Nat := S.ab + S.nA + (S.outs.length - S.sh)

/-- The fixed address column `x ↦ g^{a (row x)}`, its closed form the extension. -/
def adrCol (a : Nat → Nat) : ColSrc :=
  .fix (fun x => FK.x ^ a (S.row x)) fun r => Loop.mle r fun x => FE.ofK (FK.x ^ a (S.row x))

/-- Column `c`. -/
def col (c : Nat) : ColSrc :=
  if c = 66 then S.adrCol S.wc
  else if c < S.ab then .com (S.pl c).1 (S.pl c).2
  else if S.sh ≠ 0 ∧ c = S.ab then S.adrCol (S.oc 0)
  else S.adrCol (S.oc (c - S.ab - S.nA + S.sh))

/-- Output `j`'s address: `g^j` times the shared column (`j < sh`), else its own column. -/
def oaddr (j : Nat) : CPoly :=
  if j < S.sh then [(FK.x ^ j, [S.ab])] else CPoly.var (S.ab + S.nA + (j - S.sh))

/-- The word's read. -/
def wread : Key × Nat := (⟨sep .K, CPoly.var 66, [CPoly.var 0]⟩, 65)

/-- Output `j`'s read. -/
def oread (j : Nat) : Key × Nat := (⟨sep .K, S.oaddr j, [outPoly (S.out j)]⟩, 67 + j)

/-- The reads. -/
def reads : List (Key × Nat) :=
  (if S.rd then [wread] else []) ++ (List.range S.outs.length).map S.oread

theorem deg_var (i : Nat) : CPoly.Deg2 (CPoly.var i) := fun m hm => by
  simp [CPoly.var] at hm; subst hm; simp

/-- **The `BITS` table.** -/
def tab : Tab where
  τ := S.τ
  cols := (List.range S.width).map S.col
  cons := cons
  reads := S.reads
  seeds := []
  deg := by
    refine ⟨fun C hC m hm => ?_, fun r hr => ?_, fun s hs => by simp at hs⟩
    · simp only [cons, List.mem_cons, List.mem_map, List.mem_range] at hC
      rcases hC with rfl | ⟨z, -, rfl⟩
      · simp only [wcons, List.mem_cons, List.mem_map, List.mem_range] at hm
        rcases hm with rfl | ⟨z, -, rfl⟩ <;> simp
      · simp only [bcons, List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at hm
        rcases hm with rfl | rfl <;> simp
    · simp only [reads, List.mem_append, List.mem_map, List.mem_range] at hr
      rcases hr with h | ⟨j, -, rfl⟩
      · split at h
        · simp only [List.mem_singleton] at h; subst h
          exact ⟨deg_var 66, fun P hP => by simp [wread] at hP; subst hP; exact deg_var 0⟩
        · simp at h
      · refine ⟨?_, fun P hP => ?_⟩
        · unfold oread oaddr; split
          · intro m hm; simp only [List.mem_singleton] at hm; subst hm; simp
          · exact deg_var _
        simp only [oread, List.mem_singleton] at hP; subst hP
        intro m hm
        simp only [outPoly, List.mem_map, List.mem_range] at hm
        obtain ⟨z, -, rfl⟩ := hm; simp

end BSpec

/-! ## The row lemma on `FK` rows -/

/-! ## Soundness through the bus -/

section Sound

variable (Q : Program) (pl : ℕ → Var → Bool × ℕ) (groups : List Grp) (arrs : List InArr)
  (aux : List Tab) (L : Lay) (hτ : ∀ t ∈ lvmTabs Q pl groups arrs aux, t.τ ≤ L.μ)

end Sound

/-! ## Completeness: the honest row -/

end Lvm.BitsTab
