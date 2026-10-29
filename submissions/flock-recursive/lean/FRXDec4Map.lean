-- New for `flock-recursive` (BLUEPRINT revision 4.2, §6.2 step 4; stage S-H4, pass 4, item 2).
import FRXDec4Msg
import FRXChain

/-!
# The node decoder's memory map at revision 4.1 (`Map4`)

The node decoder runs on `memX4 + mpw·t` words: the decoder's regions below `memX4 = 2^28`, the
log index from `memX4` on (Part 25 F2; the coordinator's Q2 ruling). `Map4` places every region:

| region | base (`map4`) | size at `m = 32` |
|---|---|---|
| registers | `0` | `256` |
| basis table (`wtabIR`) | `tb = 2^20` | `800` |
| the chain (`chainIR`: targets, `H`, answers) | `chB = 2^23` … `chEnd` | `6,144` |
| levels 1–4 (`lU`): flags, `J`, `P`, `Y`, rows, `eq`, `X`, `Y` | `2^24` … `2^24 + 2^23 + 2^20` | |
| level 0 (`l0`): flags, `J`, `P`, `Y`, rows, `eq`, `X`, `Y` | `2^24` … `2^25 + 2^22 + 256` | |
| levels 1–4's word | `lU.cb = 2^26` | `32 · 2^18` |
| level 0's word | `l0.cb = 2^27` | `128 · 2^20 = 2^27` |
| the log index | `ix = memX4 = 2^28` | `3t` |

Levels 1–4 run before level 0 and share one map (3.x's `obL`); level 0's regions overlap theirs
except level 1's decoded rows, which level 0's message step reads (`Map4.Ok`'s cross conditions).
The same literal serves `m = 31` (`N2`) and `m = 32` (`N4`, `N8`).

**`Map4.Ok M m`** is a conjunction of numeral inequalities (the sizes are `2^(m − 12 − 2i)`
positions, `2^(m − 13 − 3i)` targets): non-overlap of every region, `MsgOk4`'s `X`/`Y` regions, the
`2k` slack after each output (`ob + 2k(C + 1) ≤ eb`), and the fit under `2^28`. `map4_ok31`,
`map4_ok32` are `decide` on the literal record. `LvMap.back`/`LvMap.front` turn a level's `Ok` into
`BackLay4`/`FrontLay4` and `decLv4_sem`'s remaining layout hypotheses.
-/

namespace FR.X

open RecursionFast FR

-- The decoder's memory `memX4 = 2^28` is `FRXProg`'s (the program's memory, the index's base).

/-- **One level's regions**: flags `fb`, `J` at `jb`, the prefix table `pb`, `lagIR`'s `Y` at
`yl`, the decoded rows `ob`, the `eq` table `eb`, `X` at `xb`, `Y` at `yb`, the word's column store
at `cb` with `cs` words a position. -/
structure LvMap where
  fb : ℕ
  jb : ℕ
  pb : ℕ
  yl : ℕ
  ob : ℕ
  eb : ℕ
  xb : ℕ
  yb : ℕ
  cb : ℕ
  cs : ℕ
  deriving DecidableEq, Repr

/-- **A level's map fits** `n` positions, `k` targets, `C` decoded rows and `R` word rows, after
the basis table at `tb`: the regions in order, each output with `2k` words of slack. -/
def LvMap.Ok (M : LvMap) (tb n k C R : ℕ) : Prop :=
  tb + 800 ≤ M.fb ∧ M.fb + n ≤ M.jb ∧ M.jb + k ≤ M.pb ∧ M.pb + k ≤ M.yl ∧ M.yl + 2 * C * k ≤ M.ob ∧
    M.ob + 2 * k * (C + 1) ≤ M.eb ∧ M.eb + 256 ≤ M.xb ∧ M.xb + 2 * n ≤ M.yb ∧
    M.yb + 2 * n ≤ M.cb ∧ 2 * R ≤ M.cs ∧ M.cb + M.cs * n + 256 < 2 ^ 64

instance (M : LvMap) (tb n k C R : ℕ) : Decidable (M.Ok tb n k C R) := by
  unfold LvMap.Ok; infer_instance

/-- **The node decoder's map**: the basis table, level 0's and levels 1–4's regions, the index. -/
structure Map4 where
  tb : ℕ
  l0 : LvMap
  lU : LvMap
  ix : ℕ
  deriving DecidableEq, Repr

/-- **The map is sound at `m`** (numerals only): the chain's region `[chB, chEnd)` between the
basis table and both levels' regions; level 0 at `2^(m − 12)` positions, `2^(m − 13)` targets,
rows 4–7 decoded (`C = 4`) of 64; levels `i = 1 … 4` at `2^(m − 12 − 2i)` positions,
`2^(m − 13 − 3i)` targets, all 16 rows; levels 1–4 keep level 0's word; level 1's rows lie below
level 0's `eq` table; level 0's word ends at the index, at `2^28`. -/
def Map4.Ok (M : Map4) (m : ℕ) : Prop :=
  regs ≤ M.tb ∧ M.tb + 800 ≤ chB ∧ chEnd ≤ M.l0.fb ∧ chEnd ≤ M.lU.fb ∧
    M.l0.Ok M.tb (2 ^ (m - 12)) (2 ^ (m - 13)) 4 64 ∧
    M.lU.Ok M.tb (2 ^ (m - 12 - 2 * 1)) (2 ^ (m - 13 - 3 * 1)) 16 16 ∧
    M.lU.Ok M.tb (2 ^ (m - 12 - 2 * 2)) (2 ^ (m - 13 - 3 * 2)) 16 16 ∧
    M.lU.Ok M.tb (2 ^ (m - 12 - 2 * 3)) (2 ^ (m - 13 - 3 * 3)) 16 16 ∧
    M.lU.Ok M.tb (2 ^ (m - 12 - 2 * 4)) (2 ^ (m - 13 - 3 * 4)) 16 16 ∧
    M.lU.yb + 2 * 2 ^ (m - 12 - 2 * 1) ≤ M.l0.cb ∧
    M.lU.cb + M.lU.cs * 2 ^ (m - 12 - 2 * 1) ≤ M.l0.cb ∧
    M.lU.ob + 32 * 2 ^ (m - 13 - 3 * 1) ≤ M.l0.eb ∧
    M.l0.cb + M.l0.cs * 2 ^ (m - 12) ≤ M.ix ∧ M.ix = memX4

instance (M : Map4) (m : ℕ) : Decidable (M.Ok m) := by
  unfold Map4.Ok; infer_instance

/-- **The node decoder's map** (one literal for `m = 31` and `m = 32`). Reducible: a projection
`map4.tb + c` in an `omega` goal is then a literal sum, not a unary unfolding of `c`. -/
abbrev map4 : Map4 where
  tb := 1048576
  l0 := { fb := 16777216, jb := 17825792, pb := 18350080, yl := 18874368, ob := 23068672,
          eb := 33554432, xb := 33554688, yb := 35651840, cb := 134217728, cs := 128 }
  lU := { fb := 16777216, jb := 17039360, pb := 17104896, yl := 17170432, ob := 19267584,
          eb := 25165824, xb := 25166080, yb := 25690368, cb := 67108864, cs := 32 }
  ix := 268435456

/-- (+) **`map4` is sound at `m = 32`** (`N4`, `N8`). -/
theorem map4_ok32 : map4.Ok 32 := by decide

/-- (+) **`map4` is sound at `m = 31`** (`N2`). -/
theorem map4_ok31 : map4.Ok 31 := by decide

/-- (value) `map4`'s bases are the table's powers of two. -/
theorem map4_ctl : map4.tb = 2 ^ 20 ∧ map4.l0.fb = 2 ^ 24 ∧ map4.l0.eb = 2 ^ 25 ∧
    map4.l0.cb = 2 ^ 27 ∧ map4.lU.cb = 2 ^ 26 ∧ map4.lU.eb = 2 ^ 24 + 2 ^ 23 ∧ map4.ix = memX4 := by
  decide

/-- (−) **Overlap is rejected**: `X` of level 0 moved onto its `eq` table. -/
theorem not_map4_overlap : ¬ ({ map4 with l0 := { map4.l0 with xb := map4.l0.eb } } : Map4).Ok 32 := by
  decide

/-- (−) **The slack is required**: level 0's `eq` table moved to the end of its rows
(`ob + 2kC`, no `2k` slack). -/
theorem not_map4_slack :
    ¬ ({ map4 with l0 := { map4.l0 with eb := 23068672 + 2 * 2 ^ 19 * 4 } } : Map4).Ok 32 := by
  decide

/-- (−) **The fit is required**: level 0's word one position higher runs into the index. -/
theorem not_map4_fit :
    ¬ ({ map4 with l0 := { map4.l0 with cb := 134217728 + 128 } } : Map4).Ok 32 := by
  decide

/-- (−) **Level 1's rows must lie below level 0's `eq` table**: rows moved above it. -/
theorem not_map4_rows :
    ¬ ({ map4 with lU := { map4.lU with ob := 33554432 } } : Map4).Ok 32 := by
  decide

/-! ## From `Ok` to the level theorems' layouts -/

/-- A level's `Ok` gives the back half's map and `decLv4_sem`'s output slack. -/
theorem LvMap.back {M : LvMap} {tb n k C R : ℕ} (h : M.Ok tb n k C R) (htb : regs ≤ tb) :
    BackLay4 n k C tb M.fb M.jb M.pb M.yl M.ob ∧ M.ob + 2 * k * (C + 1) ≤ M.eb := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, -, h11⟩ := h
  exact ⟨⟨htb, h1, h2, h3, h4, h5, by omega⟩, h6⟩

/-- A level's `Ok` gives the front half's map, for challenges `cbS` in the chain's region below
the level's flags. -/
theorem LvMap.front {M : LvMap} {tb n k C R ℓ cbS : ℕ} (h : M.Ok tb n k C R) (htb : regs ≤ tb)
    (hS : regs ≤ cbS) (hS2 : cbS + 8 * ℓ + 4 ≤ M.fb) :
    FrontLay4 n ℓ tb M.fb M.eb M.xb M.yb cbS := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, -, h11⟩ := h
  exact ⟨htb, h1, by omega, h7, h8, by omega, hS, by omega, .inl hS2⟩

/-- A level's `Ok`: the store above `Y`, its column width, its end below `2^64`. -/
theorem LvMap.store {M : LvMap} {tb n k C R : ℕ} (h : M.Ok tb n k C R) :
    M.yb + 2 * n ≤ M.cb ∧ 2 * R ≤ M.cs ∧ M.cb + M.cs * n + 256 < 2 ^ 64 :=
  ⟨h.2.2.2.2.2.2.2.2.1, h.2.2.2.2.2.2.2.2.2.1, h.2.2.2.2.2.2.2.2.2.2⟩

/-! ## The ladder's sizes per kind -/

/-- Level 0's sizes at a node kind: `2^(m − 12)` positions, `2^(m − 13)` targets, 64 rows. -/
theorem lv0_sizes (κ : Rev4.NodeKind) :
    2 ^ (Snd.CKind.lv (.node κ) 0).logN = 2 ^ ((Snd.CKind.node κ).m - 12) ∧
      2 ^ Snd.T4.mLog (.node κ) 0 = 2 ^ ((Snd.CKind.node κ).m - 13) ∧
      (Snd.CKind.lv (.node κ) 0).rows = 64 ∧ (Snd.CKind.lv (.node κ) 0).ell = 6 := by
  cases κ <;> decide

/-- Level `i ∈ [1, 4]`'s sizes at a node kind: `2^(m − 12 − 2i)` positions, `2^(m − 13 − 3i)`
targets, 16 rows. -/
theorem lvU_sizes (κ : Rev4.NodeKind) {i : ℕ} (hi1 : 1 ≤ i) (hi : i ≤ 4) :
    2 ^ (Snd.CKind.lv (.node κ) i).logN = 2 ^ ((Snd.CKind.node κ).m - 12 - 2 * i) ∧
      2 ^ Snd.T4.mLog (.node κ) i = 2 ^ ((Snd.CKind.node κ).m - 13 - 3 * i) ∧
      (Snd.CKind.lv (.node κ) i).rows = 16 ∧ (Snd.CKind.lv (.node κ) i).ell = 4 := by
  cases κ <;> interval_cases i <;> decide

/-- The node kinds' sizes: `m = 31` (`N2`) or `32` (`N4`, `N8`). -/
theorem node_m (κ : Rev4.NodeKind) : (Snd.CKind.node κ).m = 31 ∨ (Snd.CKind.node κ).m = 32 := by
  cases κ <;> decide

/-- **`map4` is sound at every node kind's `m`.** -/
theorem map4_ok (κ : Rev4.NodeKind) : map4.Ok (Snd.CKind.node κ).m := by
  rcases node_m κ with h | h <;> rw [h]
  · exact map4_ok31
  · exact map4_ok32

/-- `map4`'s level-`i` regions are sound at a node kind's level `i` (`i ∈ [1, 4]`). -/
theorem map4_lvU (κ : Rev4.NodeKind) {i : ℕ} (hi1 : 1 ≤ i) (hi : i ≤ 4) :
    map4.lU.Ok map4.tb (2 ^ (Snd.CKind.lv (.node κ) i).logN) (2 ^ Snd.T4.mLog (.node κ) i) 16 16 := by
  obtain ⟨e1, e2, -, -⟩ := lvU_sizes κ hi1 hi
  rw [e1, e2]
  obtain ⟨-, -, -, -, -, o1, o2, o3, o4, -⟩ := map4_ok κ
  interval_cases i
  · exact o1
  · exact o2
  · exact o3
  · exact o4

/-- `map4`'s level-0 regions are sound at a node kind's level 0. -/
theorem map4_l0 (κ : Rev4.NodeKind) :
    map4.l0.Ok map4.tb (2 ^ (Snd.CKind.lv (.node κ) 0).logN) (2 ^ Snd.T4.mLog (.node κ) 0) 4 64 := by
  obtain ⟨e1, e2, -, -⟩ := lv0_sizes κ
  rw [e1, e2]
  exact (map4_ok κ).2.2.2.2.1

end FR.X
