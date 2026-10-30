-- New for `flock-recursive` (PACK-4.4.1 §5.2 as PK-M3 corrected, B2′'s option (a); stage B2″, track
-- L-circ).
import FRNodeRows4ArenaRows

/-!
# The arenas placed: arena₁, the binding's rows and the bits in each slot's own region

PK-M3: the arenas sit in the region of the slot whose prototype reads them, at the **same
M-relative addresses in both prototypes**. B2″'s cell packing (`FRVIRTplSet.fitCells`, `packOf`)
freed the cells between the skeleton (277,102 cells in both prototypes) and the lowest template
instance (414,016 / 441,152; `logs/B2pp/cellfit-3.log`); B2′'s option (a) drops arena₂'s own cells
(the binding's rows write the consumers' import cells, `FRNodeRows4ArenaRows.a2Rows`).

| | M-relative cells (region `σ`: `+ σ·2^20`) | rows (region `σ`: `+ σ·2^20`) |
|---|---|---|
| arena₁, `arN = 4·chainLenOf seq4` elements | `[arA1, arA1 + arN)` = `[290,816, 387,752)` | `[arR1, arR1 + arN)` = `[852,992, 949,928)` |
| the binding (import cells: B3/B4's) | — | `[arR2, arR2 + arR2N)` = `[720,896, 852,992)` |
| bits, `arNb` | `[arBt, arBt + arNb)` = `[389,120, 397,440)` | `[arRb, arRb + arNb)` = `[950,272, 958,592)` |

The rows lie above both prototypes' rows (700,160 / 686,080 in the region, `logs/B2pp/nodedump4-run.log`)
and below the link region (`arena_rows`); the cells between the skeleton's and the templates'
(`arena_cells`; the gap itself is the compile's, checked on the dump: `logs/B2pp/arenafit.log`). Rows
and cells as placed are what B4 folds into `nodeIRows4`; nothing here changes a statement of the
soundness chain.

**What the placed rows give** (B3/B4's interface: an ask's answer and operand cells are stream
elements): `a1_cells4`, `arena_elem4`, `bit_cells4`; **their values**: `a1V4_eq`, `a2V4_eq`,
`bitV4_eq` (the automaton runs at the placed addresses, absolute cells: `κ.oneCell + ·`).
-/

namespace FR
namespace Rev4
open RecursionFast Circ TEval

/-! ## The addresses (M-relative, in a slot's own region) -/

/-- Arena₁'s elements: the segment's H chain, four a block (`4·chainLenOf seq4`: 96,944 at RSV2's
`|π|`; taken from the format, so that a format change moves it without a proof change). -/
def arN : ℕ := 4 * chainLenOf seq4
/-- `arN` at today's format (one rewrite: a proof that compares `arN` inside arithmetic makes the kernel
evaluate `chainLenOf seq4`, ≈ 2.4 s each). -/
theorem arN_eq : arN = 96944 := by rw [arN, chainLenOf_seq4.1]

/-- Arena₁'s first cell: above the skeleton's 277,102 cells (both prototypes), with a margin of 13.7 k
cells below and 16.6 k above the bits (`logs/B2pp/arenafit.log`). -/
def arA1 : ℕ := 290816
/-- The bits' first cell, after arena₁. -/
def arBt : ℕ := 389120
/-- The bits (PACK-4.4.1 §5.2: the 62 answers' 256 bits tied to 8,320 M Boolean cells). -/
def arNb : ℕ := 16384
/-- The binding's first row: above both prototypes' rows (700,160 in the region; a margin of 20.7 k
rows). -/
def arR2 : ℕ := 720896
/-- The binding's rows (index space: the levels' positions at their `2^a` strides, PACK-4.4.1
§5.2's 132,096 allocated, 85,946 used; SEG-R2: cut to the template rows' used extent, 154,333 with SIB's
siblings at prototype 1, `2^8`-aligned, so that band B of the segment's replay rows starts at the bits'
end). -/
def arR2N : ℕ := 154368
/-- Arena₁'s first row, after the binding's. -/
def arR1 : ℕ := arR2 + arR2N
/-- The bits' first row, after arena₁'s (aligned to `2^8`). -/
def arRb : ℕ := 972288

/-- **The rows are ordered and below the link region**: the binding, arena₁, the bits, then
`linkN = 2^15` rows (`FRNodeRows4`). -/
theorem arena_rows : arR2 + arR2N = arR1 ∧ arR1 + arN ≤ arRb ∧ arRb + arNb + 2 ^ 15 ≤ slotM4 := by
  -- (`rw` keeps the statement's form: `simp` would make the kernel evaluate `arN`)
  refine ⟨rfl, by rw [arN_eq]; decide, by decide⟩

/-- **The cells are ordered and inside the region**: arena₁, then the bits; arena₁ fits the automaton's
17 bits. -/
theorem arena_cells : arA1 + arN ≤ arBt ∧ arBt + arNb ≤ slotM4 ∧ arN ≤ 2 ^ 17 ∧ arNb ≤ 2 ^ 14 := by
  refine ⟨by rw [arN_eq]; decide, by decide, by rw [arN_eq]; decide, by decide⟩

/-! ## The rows of slot `σ` (absolute cells, M's rows) -/

/-- **Arena₁'s rows of slot `σ`** (stream block `b0`: `packB κ σ`'s). -/
def a1Rows4 (κ : NodeKind) (σ b0 : ℕ) : List (ℕ × Row) :=
  a1Rows κ.oneCell (κ.oneCell + σ * slotM4 + arA1) (σ * slotM4 + arR1) b0 arN

/-- **The binding's rows of a level in slot `σ`** (the level's import cells and rows relative to the
region: `v.C`, `v.B`). -/
def a2Rows4 (κ : NodeKind) (σ : ℕ) (v : ALv) : List (ℕ × Row) :=
  a2Rows κ.oneCell (κ.oneCell + σ * slotM4 + arA1) (κ.oneCell + σ * slotM4) (σ * slotM4 + arR2) v

/-- **The bits' rows of slot `σ`.** -/
def bitRows4 (κ : NodeKind) (σ : ℕ) : List (ℕ × Row) :=
  bitRows (κ.oneCell + σ * slotM4 + arBt) (σ * slotM4 + arRb) arNb

/-- A level's rows lie in the binding's range (`B`, its positions at the `2^a` stride). -/
def LvIn (v : ALv) : Prop := v.S ≤ 2 ^ v.a ∧ v.B + v.t * 2 ^ v.a ≤ arR2N

/-! ## What they give -/

/-- **Arena₁'s cell `e` of slot `σ` is stream element `e`.** -/
theorem a1_cells4 {w : Asg} {κ : NodeKind} {σ b0 : ℕ} (hone : w κ.oneCell = 1)
    (h : ∀ p ∈ a1Rows4 κ σ b0, p.2.Holds w) {e : ℕ} (he : e < arN) :
    w (κ.oneCell + σ * slotM4 + arA1 + e) = w (sCell b0 e) :=
  a1_cells hone h he

/-- **An import cell of slot `σ` is its stream element**: position `p`, element `q` of a level `v`
is element `E + S·p + q` of the slot's stream (`sCell b0 ·`). -/
theorem arena_elem4 {w : Asg} {κ : NodeKind} {σ b0 : ℕ} {v : ALv} (hone : w κ.oneCell = 1)
    (h1 : ∀ p ∈ a1Rows4 κ σ b0, p.2.Holds w) (h2 : ∀ p ∈ a2Rows4 κ σ v, p.2.Holds w) {p q : ℕ}
    (hp : p < v.t) (hq : q < v.S) (hN : v.E + v.S * p + q < arN) :
    w (κ.oneCell + σ * slotM4 + v.C + p * 2 ^ v.c + v.off q) = w (sCell b0 (v.E + v.S * p + q)) :=
  arena_elem hone h1 h2 hp hq hN

/-- **The bits' cells of slot `σ` are bits.** -/
theorem bit_cells4 {w : Asg} {κ : NodeKind} {σ : ℕ} (h : ∀ p ∈ bitRows4 κ σ, p.2.Holds w) {j : ℕ}
    (hj : j < arNb) : w (κ.oneCell + σ * slotM4 + arBt + j) = 0 ∨ w (κ.oneCell + σ * slotM4 + arBt + j) = 1 :=
  bit_cells h hj

/-- (+) Element 5 of slot 1's arena₁ is the cell `oneCell + 2^20 + 290,821`, its row `2^20 + 875,269`;
(−) not slot 0's. -/
theorem a1Rows4_ctl (κ : NodeKind) :
    (a1Rows4 κ 1 0)[5]?.map (fun p => (p.1, p.2.b)) =
      some (2 ^ 20 + 875269, (Lin.cell (κ.oneCell + 2 ^ 20 + 290821)).sub (Lin.cell (sCell 0 5))) ∧
    (a1Rows4 κ 1 0)[5]?.map Prod.fst ≠ some 875269 := by
  have h : 5 < arN := by rw [arN_eq]; norm_num
  simp only [a1Rows4, a1Rows, List.getElem?_map, List.getElem?_range h, Option.map_some, cpRow, slotM4,
    arA1, arR1, arR2, arR2N]
  refine ⟨by norm_num [add_assoc], by norm_num⟩

/-! ## Their values at the placed addresses (absolute cells; `n`, `m` the matrix's row and cell
coordinates) -/

/-- Arena₁'s value of slot `σ`: three automaton runs over 17 bits (`a1V`). -/
def a1V4 (n m : ℕ) (t u : ℕ → F) (κ : NodeKind) (σ b0 : ℕ) : F3 :=
  a1V n m 17 t u κ.oneCell (κ.oneCell + σ * slotM4 + arA1) (σ * slotM4 + arR1) b0 arN

theorem a1V4_eq {n m : ℕ} (hn : 17 ≤ n) (hm : 22 ≤ m) (t u : ℕ → F) (κ : NodeKind) (σ b0 : ℕ) :
    a1V4 n m t u κ σ b0 = (rowsVal (RingHom.id F) .a n m t u (a1Rows4 κ σ b0),
      rowsVal (RingHom.id F) .b n m t u (a1Rows4 κ σ b0), rowsVal (RingHom.id F) .c n m t u (a1Rows4 κ σ b0)) :=
  a1V_eq hn (by omega) (by omega) t u _ _ _ _ _ arena_cells.2.2.1

/-- The binding's value of a level in slot `σ` (`a2V`: the import side once per level, one run per
position on arena₁'s side). -/
def a2V4 (n m k k' : ℕ) (t u : ℕ → F) (κ : NodeKind) (σ : ℕ) (v : ALv) : F :=
  a2V n m k k' t u (κ.oneCell + σ * slotM4 + arA1) (κ.oneCell + σ * slotM4) (σ * slotM4 + arR2) v

theorem a2V4_eq {n m k k' : ℕ} (hk : k ≤ n) (hm : k ≤ m) (t u : ℕ → F) (κ : NodeKind) (σ : ℕ) (v : ALv)
    (hS : v.S ≤ 2 ^ k) (ha : v.a ≤ n) (hc : v.c ≤ m) (hk1 : k' ≤ n - v.a) (hk2 : k' ≤ m - v.c)
    (ht : v.t ≤ 2 ^ k') (hR : 2 ^ v.a ∣ σ * slotM4 + arR2 + v.B) (hC : 2 ^ v.c ∣ κ.oneCell + σ * slotM4 + v.C)
    (hv : LvIn v) (hoff : ∀ q < v.S, v.off q < 2 ^ v.c) :
    a2V4 n m k k' t u κ σ v = rowsVal (RingHom.id F) .b n m t u (a2Rows4 κ σ v) :=
  a2V_eq hk hm t u κ.oneCell _ _ _ v hS ha hc hk1 hk2 ht hR hC hv.1 hoff

/-- The bits' value of slot `σ`: one automaton run over 14 bits. -/
def bitV4 (n m : ℕ) (t u : ℕ → F) (κ : NodeKind) (σ : ℕ) : F3 :=
  bitV n m 14 t u (κ.oneCell + σ * slotM4 + arBt) (σ * slotM4 + arRb) arNb

theorem bitV4_eq {n m : ℕ} (hn : 14 ≤ n) (hm : 14 ≤ m) (t u : ℕ → F) (κ : NodeKind) (σ : ℕ) :
    bitV4 n m t u κ σ = (rowsVal (RingHom.id F) .a n m t u (bitRows4 κ σ),
      rowsVal (RingHom.id F) .b n m t u (bitRows4 κ σ), rowsVal (RingHom.id F) .c n m t u (bitRows4 κ σ)) :=
  bitV_eq hn hm t u _ _ _ arena_cells.2.2.2

end Rev4
end FR
