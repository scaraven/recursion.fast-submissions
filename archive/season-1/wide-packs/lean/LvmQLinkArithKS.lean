import LvmQLinkArith
import LvmQLinkArithRead

-- (GOLF2: 82 declarations that `certified` does not use moved verbatim to `LvmQTypedHarZOff`, outside its import closure.)

-- ===== merged from `LvmQLinkArithRows` (GOLF module merge: `LvmQLinkArithRows.lean` is now a stub importing `LvmQLinkArithKS`) =====
section

/-!
# QA1 links: row combinators for the link circuits

Template combinators (`Ins` lists at an absolute position, QA1's `Fix` semantics, `LvmQSumcheckCore`) and
their values on any fixed point:

* `eqTabGo`: `eqKernel` itself, one level per coordinate (a `lin` for `1 + r`, then `2^k` rows
  `old·(1 + r)` and `2^k` rows `old·r`); **`eqTab_val`**: the last level's values are
  `rs.foldl eqStep olds` (so `eqKernel` of the point when `olds = [1]`);
* `mulChainIns` (`s·c₀·c₁…`), `dotIns` (`s + Σ aᵢbᵢ`), with `mulChain_val`, `dot_val`;
* `shiftRecIns`: `(eqEval, shiftEval)` from the last coordinate down (`shiftEval_cons`), 8 rows
  per coordinate; **`shiftRec_val`**;
* `preRecIns`: `preCF` for a static bound, 12 rows per coordinate; **`preRec_val`**.
-/

set_option autoImplicit false

namespace Lvm.Q1

open Lvm Lvm.Loop

/-! ## Generic helpers -/

@[simp] theorem val_loc (xv : Src → FE) (V : List FE) (k : Nat) : (Src.loc k).val xv V = V.getD k 0 := rfl

/-! ## `eqKernel` -/

/-! ## Chains -/

/-- `s·c₀·c₁·…`, one `muladd` per factor (`zero` the addend). -/
def mulChainIns (zero : Src) : Nat → Src → List Src → List Ins
  | _, _, [] => []
  | n, s, c :: cs => mulI s c zero :: mulChainIns zero (n + 1) (.loc n) cs

/-! ## The shift kernel, from the last coordinate down -/

/-- `eqEval`'s source after the coordinates `xs`, `ys` (`E0` before any). -/
def shiftRecE (n : Nat) : List Src → List Src → Src → Src
  | _ :: x, _ :: _, _ => .loc (n + 8 * x.length + 1)
  | _, _, E0 => E0

/-- `shiftEval`'s source. -/
def shiftRecS (n : Nat) : List Src → List Src → Src → Src
  | _ :: x, _ :: _, _ => .loc (n + 8 * x.length + 7)
  | _, _, S0 => S0

/-! ## The interval shift sum `pre(H)`, from the last coordinate down -/

/-- The 12 rows of one coordinate at `m` (bound bit `h`), from the tail's `P`, `E`, `Pt`. -/
def preLevel (zero : Src) (m : Nat) (h : Bool) (x0 y0 P E Pt : Src) : List Ins :=
  [linI 0 1 y0 y0, linI 0 1 x0 x0,
    mulI (.loc m) x0 zero, mulI y0 (.loc (m + 1)) zero, mulI (.loc m) (.loc (m + 1)) zero, mulI y0 x0 zero,
    addI E (if h then Pt else zero),
    mulI (.loc (m + 3)) P zero, mulI (.loc (m + 2)) (.loc (m + 6)) (.loc (m + 7)),
    mulI (.loc (m + 5)) E zero, mulI (.loc (m + 4)) (.loc (m + 6)) (.loc (m + 9)),
    mulI (if h then .loc (m + 5) else .loc (m + 4)) Pt zero]

/-- The sources of `(pre, E, Pt)` after the coordinates `xs`, `ys` (`base` before any). -/
def preRecOut (n : Nat) : List Src → List Src → Src × Src × Src → Src × Src × Src
  | _ :: x, _ :: _, _ => (.loc (n + 12 * x.length + 8), .loc (n + 12 * x.length + 10), .loc (n + 12 * x.length + 11))
  | _, _, base => base

/-- **`preCF xs ys H`**, the last coordinate first, 12 rows per coordinate. -/
def preRecIns (zero : Src) (n : Nat) : List Src → List Src → Nat → Src × Src × Src → List Ins
  | x0 :: x, y0 :: y, H, base => preRecIns zero n x y (H / 2) base ++
      preLevel zero (n + 12 * x.length) (H % 2 = 1) x0 y0 (preRecOut n x y base).1 (preRecOut n x y base).2.1
        (preRecOut n x y base).2.2
  | _, _, _, _ => []

end Lvm.Q1
end
-- ===== end of `LvmQLinkArithRows` =====

-- ===== merged from `LvmQLinkArithCH` (GOLF module merge: `LvmQLinkArithCH.lean` is now a stub importing `LvmQLinkArithKS`) =====
section

/-!
# QA1 links: the `CH` link circuit (phase 5)

Three straight-line blocks around two sumcheck gadgets (`scGadget`):

* **A** (`chGlueA`, `2n + 166` rows, `n = logN`): load the `n + 9` challenges `ρ, λ, ζ`; `eq(λ, ·)` (8) and
  `eq(ζ, ·)` (64) as `eqKernel`; `Pad43`'s constant bits; `Πρ`; the shift sumcheck's claim
  `C·(1 + Πρ)` (= `chShiftTarget0`, `chGlueA_target`).
* the shift sumcheck (`n` rounds, degree 2);
* **B** (`chGlueB`): the 64 `in` slices, `Σ_p eq(ζ,p)·inS_p`, `(eqEval, shiftEval)(ρ, ρ')`, the second
  sumcheck's claim (= `chSc2Target0`);
* the two-round sumcheck;
* **C** (`chGlueC`): the 64 `Y` slices, `eq(μ, ·)`, `α`, `β`, the two halves of `Σ_q W̃(μ,q)·yS_q`,
  `eqMasked`, and the gated assertion `gate·(f₂ − eqMasked·Σ) = 0` (`chLink0`'s check).
-/

set_option autoImplicit false

namespace Lvm.Q1

open Lvm Lvm.Loop Lvm.Loop.Build

/-! ## Helpers -/

/-- A cell as an operand of a template. -/
def cellSrc (c : Cell) : Src := .ext c.addr

/-- The loads of `N` scalars at lanes `q + s·i`. -/
def loadsAt (q s N : Nat) : List Ins := (List.range N).map fun i => loadI (q + s * i) []

/-! ## Block A: the shift sumcheck's claim -/

/-! ## Block B: the second sumcheck's claim -/

/-! ## Block C: the `CH` link's check -/

/-! ## Where the tables are -/

end Lvm.Q1
end
-- ===== end of `LvmQLinkArithCH` =====

-- ===== merged from `LvmQLinkArithCHSound` (GOLF module merge: `LvmQLinkArithCHSound.lean` is now a stub importing `LvmQLinkArithKS`) =====
section

/-!
# QA1 links: the `CH` link gadget and its soundness against `F`

`chLinkGadget n D Q gate`: block A, the shift sumcheck (`2^D ≥ n` iterations), block B, the two-round
sumcheck, block C. **`chLink_sound`**: in every memory where the gadget's rows hold, whose input lanes
are the stream's (`Streamed`), with the phase starting at position `P` (`P + 40 = 8Q`) and gate `1`:
if the gadget's assertion holds, then `chLink0`'s check on what `F` reads in phase 5
(`chLinkView`, `LvmQLinkArithRead`) is `true`.
-/

set_option autoImplicit false

namespace Lvm.Q1

open Lvm Lvm.Loop Lvm.Loop.Build

/-! ## Small facts -/

/-! ## The gadget -/

/-- `ρ'`'s cells (the shift sumcheck's challenges). -/
def rho'C (sh : LoopOut) (n : Nat) : List Cell := (List.range n).map fun i => sh.cell 2 i
/-! ## Soundness -/

end Lvm.Q1
end
-- ===== end of `LvmQLinkArithCHSound` =====

/-!
# QA1 links: the `KS` link circuit (phase 7) and its soundness against `F`

The shift sumcheck from a zero claim (`ksShiftTarget = 0` in `M3.ofParts` (ex `M3.v0`)), then block E (`ksBlockE`,
v1's `ksGlueE`, `39n + 15` rows, `n = ksLog`, or KS14's `ksGlueE14`, `39n + |sel| + 14` rows, lvm2 CR-K): the `n`
challenges `ρ`, the four scalars `Y_ω, in_ω, M_ω, X_ω`, `contShift` as `pre(B − 1) + pre(K + 31) + pre(K)` (three
`preRecIns`, `K = ksSplit p + 399`, `contShift_eq`), `eqEval(ρ, ρ')` (`n` `lin` + `n` products), and the gated
assertion `gate·(f − contShift·Y − eqEval·(in + (1 + x_r)M + x_r X)) = 0` (v1) or
`gate·(f − contShift·Y − eqEval·(in + M + sel·X)) = 0` (KS14, `sel = Π_{j ≥ ksXLog} ρ'_j`, a product chain over the
four cells) (`ksLink0`'s check). **`ksLink_sound`**: if the assertion holds (gate `1`), `ksLink0`'s check on what
`F` reads in phase 7 (`ksLinkView`) is `true`.
-/

set_option autoImplicit false

namespace Lvm.Q1

open Lvm Lvm.Loop Lvm.Loop.Build

/-- `pre(H)`'s source after a `preRecIns` at `a` over `n ≥ 1` coordinates. -/
def preP (a n : Nat) : Src := .loc (a + 12 * (n - 1) + 8)

/-- **Block E** (positions in the doc above). -/
def ksGlueE (n QR QV H1 H2 H3 : Nat) (rho' : List Cell) (xr f gate : Cell) : List Ins :=
  let z : Src := .loc (n + 4)
  let base : Src × Src × Src := (z, z, .loc (n + 5))
  let rS : List Src := (List.range n).map Src.loc
  let r'S : List Src := rho'.map cellSrc
  let g := 39 * n + 8
  loadsAt QR 9 n ++ (loadsAt QV 3 4 ++ ([linI 1 0 (.loc 0) (.loc 0), linI 1 1 (.loc 0) (.loc 0)] ++
    (preRecIns z (n + 6) rS r'S H1 base ++ (preRecIns z (13 * n + 6) rS r'S H2 base ++
    (preRecIns z (25 * n + 6) rS r'S H3 base ++
    ([addI (preP (n + 6) n) (preP (13 * n + 6) n), addI (.loc (37 * n + 6)) (preP (25 * n + 6) n)] ++
    (((List.range n).map fun i => linI 1 1 (.loc i) (r'S.getD i default)) ++
    (mulChainIns z (38 * n + 8) (.loc (n + 5)) ((List.range n).map fun i => .loc (37 * n + 8 + i)) ++
    [linI 0 1 (cellSrc xr) (cellSrc xr), mulI (.loc g) (.loc (n + 2)) (.loc (n + 1)),
      mulI (cellSrc xr) (.loc (n + 3)) (.loc (g + 1)), mulI (.loc (39 * n + 7)) (.loc (g + 2)) z,
      mulI (.loc (37 * n + 7)) (.loc n) (.loc (g + 3)), addI (cellSrc f) (.loc (g + 4)),
      ⟨.assert0, .K, [.loc (g + 5), cellSrc gate]⟩]))))))))

/-! ## Block E under KS14 (lvm2 CR-K)

`ksGlueE14`: block E with the check `f = (Σ pre)·Y + eqEval·(in + M + sel·X)`, `sel` the product of the cells
`sel` (the coordinates `xl … n − 1` of `ρ'`, a `mulChainIns` from `1`): `39n + |sel| + 14` rows. -/

/-- **Block E under KS14** (positions: block E's up to `39n + 7`, then the selector's product chain, then the
check). -/
def ksGlueE14 (n QR QV H1 H2 H3 : Nat) (rho' sel : List Cell) (f gate : Cell) : List Ins :=
  let z : Src := .loc (n + 4)
  let base : Src × Src × Src := (z, z, .loc (n + 5))
  let rS : List Src := (List.range n).map Src.loc
  let r'S : List Src := rho'.map cellSrc
  let sS : List Src := sel.map cellSrc
  let g := 39 * n + 8 + sel.length
  loadsAt QR 9 n ++ (loadsAt QV 3 4 ++ ([linI 1 0 (.loc 0) (.loc 0), linI 1 1 (.loc 0) (.loc 0)] ++
    (preRecIns z (n + 6) rS r'S H1 base ++ (preRecIns z (13 * n + 6) rS r'S H2 base ++
    (preRecIns z (25 * n + 6) rS r'S H3 base ++
    ([addI (preP (n + 6) n) (preP (13 * n + 6) n), addI (.loc (37 * n + 6)) (preP (25 * n + 6) n)] ++
    (((List.range n).map fun i => linI 1 1 (.loc i) (r'S.getD i default)) ++
    (mulChainIns z (38 * n + 8) (.loc (n + 5)) ((List.range n).map fun i => .loc (37 * n + 8 + i)) ++
    (mulChainIns z (39 * n + 8) (.loc (n + 5)) sS ++
    [addI (.loc (n + 1)) (.loc (n + 2)), mulI (sumSrc (39 * n + 8) (.loc (n + 5)) sS) (.loc (n + 3)) (.loc g),
      mulI (.loc (39 * n + 7)) (.loc (g + 1)) z, mulI (.loc (37 * n + 7)) (.loc n) (.loc (g + 2)),
      addI (cellSrc f) (.loc (g + 3)), ⟨.assert0, .K, [.loc (g + 4), cellSrc gate]⟩])))))))))

/-! ## The gadget and its soundness -/

/-- The `KS` shift sumcheck's first message lane (`n = ksLog`). -/
def ksQ1 (n Q : Nat) : Nat := Q + 9 * (n + laneBits)
/-- The four scalars' first lane. -/
def ksQV (n Q : Nat) : Nat := ksQ1 n Q + 15 * n

/-- The selector's cells: the shift sumcheck's challenges `xl … n − 1` (`xl = ksXLog p`, KS14). -/
def ksSelC (p : Params) (sh : LoopOut) : List Cell := (rho'C sh p.ksLog).drop (ksXLog p)

/-- **Block E of a parameter set** (lvm2 CR-K): KS14's (`ksLog ≤ recRowsLog`) or v1's; the WOTS leaf's
continuation rows from the split (`ksSplit p + 399`). -/
def ksBlockE (p : Params) (Q : Nat) (sh : LoopOut) (gate : Cell) : List Ins :=
  if p.ksLog ≤ p.recRowsLog then
    ksGlueE14 p.ksLog Q (ksQV p.ksLog Q) (spongeBlocks p - 1) (ksSplit p + 399 + 31) (ksSplit p + 399)
      (rho'C sh p.ksLog) (ksSelC p sh) (sh.cell 5 (p.ksLog - 1)) gate
  else
    ksGlueE p.ksLog Q (ksQV p.ksLog Q) (spongeBlocks p - 1) (ksSplit p + 399 + 31) (ksSplit p + 399)
      (rho'C sh p.ksLog) (sh.cell 2 p.recRowsLog) (sh.cell 5 (p.ksLog - 1)) gate

/-- **The `KS` link gadget** (phase 7's arithmetic): a zero claim, the shift sumcheck, block E. -/
def ksLinkGadget (p : Params) (D Q : Nat) (gate : Cell) : BM Unit := do
  let oD ← loop [] (tplOf [linI 1 0 (.ext ⟨.K, Q, []⟩) (.ext ⟨.K, Q, []⟩)])
  let sh ← scGadget D 2 (ksQ1 p.ksLog Q) .plain (oD.cell 0 0)
  let _ ← loop [] (tplOf (ksBlockE p Q sh gate))
  pure ()

end Lvm.Q1
