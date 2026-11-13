-- New for lvm2 (roll 8 = B1, B1-Q; B-DES §1.2, §1.4, §1.5): the in-circuit verifier of the typed backend's phases
-- (the child's zerocheck, wiring sumcheck, `S_flat` relayout, A23 at `Φ_Q`, the mini-bus) as one gadget `typedG`,
-- replacing Q_arith's bus, table, `qacc` and table-claim sections. Reuses QA2's round runners (`scRunQ3`,
-- `scRunP3`), HAR-BT's `busG`/`tabG` pattern, AC-Q's `qacc` pieces (`qyown`, `qpub`, `eqDot`, `linePts`).
import LvmQAsmArith2Tab
import LvmQAccParts
import LvmQAcc

/-!
# The typed backend's verifier in the circuit (`typedG`)

The child's `V_S` runs `typedProg` (`LvmTypedSpec`: `zeroProg`, `wireProg`, `relayProg`, `accProgQ`,
`miniBusProg`) right after the two cap skips, where the bus phase starts today (`typedPos = busPos`). The circuit
replays it on the child's stream, from position `P` (`pos = ent + msg`; a read takes 24 bytes and its value is at
byte `pos + 40`, a sample 72 bytes with its answer at `pos + 40`):

| phase | transcript | rows (P20) [e] |
|---|---|---|
| zerocheck | `τ` (20 samples); 20 equality-mode rounds of 2 scalars; `a*, b*, c*` | 20 loads + 1 + 7·20 + 2 |
| wiring | `γ`; 21 plain rounds of 2 scalars; `v_A, v_B, v_D, v_W`; the region values `v_C, v_S, v_σ, v_K` | 1 + 2 + 1 + 6·21 + 8 + ≈ 0.7 k (`PUB`, `1`) |
| relayout | 19 plain rounds; `v_R`; the stride-17 kernel (`relayKernG`, B-DES §1.4's carry automaton) | 1 + 6·19 + ≈ 0.8 k |
| A23 at `Φ_Q` | `κ` (2); `h` (44); `t`; the zero scalar | `qaccT`: ≈ 0.4 k |
| mini-bus | today's bus at depth 13 and the table phase on the mini-bus's shapes | `busGD`, `tabG` |

* **Checks** (gated by the node flag `g`): the zerocheck's final claim is `a*·b* + c*` (equality mode: no
  `eq(τ, r_x)` factor); the wiring's final claim is `(v_A + γ v_B + γ² (v_D + v_W))·(Σ rv + virt(r_y))`; the
  relayout's is `kern(r_y, r)·v_R`; A23's three equations (`qaccT`).
* **Not in the circuit**: `Φ_Q` (the accumulator carries it, as A23 carries the tables' fixed columns today).
* **Outputs** (`TypedC`): `r_x`, `r_y`, `abc`, `vs`, `rv`, the relayout point and value, the mini-bus's outputs; the
  claims (`typedClaimsC`): on `C_rec` the relayout's point claim, `σ′`'s region claim and the mini-bus's; on
  `C_main` the committed regions' claim, the `KS` aliases' and the mini-bus's.

**Static inputs** (`TData`, filled by the layout solver at the refreeze, as `QData` today): the word space's regions
(`TReg`: base, log, target word) per source, the `S_flat` and `PUB` bases, the word `1`, the mini-bus's shapes.

**Assumptions on the native side, to be matched by B1-V/B1-K/INT** (B1-Q's report):
1. the `S_flat` region is `2^19` words at a `2^19`-aligned base and `sflatW (b + p)` is
   `(p mod 17)·2^14 + p div 17` for `p < 17·2^14` and `p` above (a permutation of `C_rec`'s words);
2. a region of `com`, `ks`, `σ′` is aligned (`base` a multiple of `2^log`) and maps to `off + (y − base)`;
3. `PUB`'s region holds the child's header lanes in order (`qpub`'s `pubLane`), `2^10` words;
4. `QLT` is not a virtual region of `z̃` (B-DES §1.3: its cells are constants of `Φ_Q`). With `qltVirt` the circuit
   evaluates it (≈ 57 k `E` rows [e]); that is the fallback, not the plan.
5. `accVars = tVars = 43` (INT's refreeze): `qaccT` reads the child's `acc_in'` at `accLane` and `qpub` covers
   `pubLanes`, both keyed on `accVars`.
6. `TData` is the layout's: every region's `off` is a multiple of `2^log` (`Placement.eqAbove`); one `PUB` region
   (log 10, lanes past `pubLanes` zero), one `1` word, one `S_flat` region, `com`/`ks`/`sig` the layout's regions of
   those sources (disjoint); `mbFix` lists every fixed column of `mbT`.
7. The schedule (B1-V/INT): phases 4–7 (`phases47`, `arithPos`) start at `typedEnd (typedPos p)`; the `sflatW` tail
   above `17·2^14` is the identity, not `0`.
-/

set_option autoImplicit false

namespace Lvm.QTyped

open Lvm Lvm.Loop Lvm.Loop.Build Lvm.Har

/-! ## Sizes (B-DES §1.1; `LvmTypedLayout.xVars`, `yVars`, `LvmTypedSpec.relayRounds`, `LvmWiring.phiVars`) -/

/-- The constraint index's variables (`xVars`). -/
abbrev tX : Nat := 20
/-- The word index's variables (`yVars`). -/
abbrev tY : Nat := 21
/-- The relayout's rounds (`relayRounds`: `C_rec`'s variables). -/
abbrev tR : Nat := 19
/-- `Φ_Q`'s variables (`phiVars = 2 + 20 + 21`). -/
abbrev tVars : Nat := 2 + tX + tY
/-- The mini-bus's depth (`miniDepth`). -/
abbrev tMB : Nat := 13

/-! ## The transcript's positions (bytes, `pos = ent + msg`) from the typed phases' start `P` -/

/-- The zerocheck's rounds. -/
def zRP (P : Nat) : Nat := P + 72 * tX
/-- `a*, b*, c*` (pending). -/
def zAbcP (P : Nat) : Nat := zRP P + 120 * tX
/-- `γ`'s sample. -/
def wGP (P : Nat) : Nat := zAbcP P + 72
/-- The wiring's rounds. -/
def wRP (P : Nat) : Nat := wGP P + 72
/-- `v_o` (4), then the region values (4) (pending). -/
def wVP (P : Nat) : Nat := wRP P + 120 * tY
/-- The relayout's rounds (the 8 values are pending in its first round's entry). -/
def rRP (P : Nat) : Nat := wVP P + 192
/-- `v_R` (pending). -/
def rVP (P : Nat) : Nat := rRP P + 120 * tR
/-- A23's start (`κ`). -/
def aP (P : Nat) : Nat := rVP P + 24
/-- The mini-bus's start: after `κ` (2), `h` (`tVars + 1`), `t`, the zero scalar. -/
def mbP (P : Nat) : Nat := aP P + 144 + 24 * (tVars + 1) + 72 + 24

/-! ## Small gadgets -/

/-- The cell `x + 1` (`1 − x` in characteristic 2). -/
def neg1 (x : Cell) : BM Cell := addK x 1

/-- `eq(r, b) = Π_i (b_i ? r_i : 1 + r_i)` over the cells `r` (first on the lowest bit); `o` for no
coordinate. -/
def eqConstG (z o : Cell) : List Cell → Nat → BM Cell
  | [], _ => pure o
  | r :: rs, b => do
    let t ← eqConstG z o rs (b / 2)
    if b % 2 = 1 then mulAdd .E t r z else do
      let u ← neg1 r
      mulAdd .E t u z

/-- `Σ_k eq(r, k)·c_k` for constants `c_k` (`k < |cs|`, `r` the cells `al i`, `i < n`): an `eq` table (QAcc's
`eqTab`), then one `lin` per constant. -/
def dotConstG (al : Nat → Cell) (z o : Cell) (n : Nat) (cs : List FK) : BM Cell := do
  let eb ← Lvm.Loop.Build.eqTab al z o false n
  let rec go : List (Nat × FK) → Cell → BM Cell
    | [], acc => pure acc
    | (k, c) :: l, acc => do
      let acc' ← if c = 0 then pure acc else lin .E c 0 acc (ec (eb + k))
      go l acc'
  go (cs.zipIdx.map fun x => (x.2, x.1)) z

/-! ## Static inputs -/

/-- A region of the word space: `2^log` words from `base` (aligned), mapped to the commitment's words from `off`. -/
structure TReg where
  base : Nat
  log : Nat
  off : Nat
  deriving Repr, Inhabited, DecidableEq

/-- **The typed phases' static data** (the layout solver's, at the refreeze). -/
structure TData where
  /-- The committed regions (`C_main`). -/
  com : List TReg
  /-- The `KS` aliases (`C_main`'s `KS` block). -/
  ks : List TReg
  /-- `σ′`'s regions (`C_rec`'s column 17). -/
  sig : List TReg
  /-- `S_flat`'s base (`2^19` words, aligned). -/
  sflat : Nat
  /-- `PUB`'s base (`2^10` words, aligned). -/
  pub : Nat
  /-- The word `1`. -/
  one : Nat
  /-- `QLT`'s base, `log` and values, when it is a virtual region (`qltVirt`; the fallback). -/
  qlt : Option (Nat × Nat × List FK)
  /-- The mini-bus's table shapes. -/
  mbS : List TShape
  /-- The mini-bus's table rounds. -/
  mbR : Nat
  /-- The mini-bus's fixed columns with a power closed form: (table, column, `b`, `s`) for the column
  `x ↦ g^{b + s x}` (`InArr.tab`'s address column). -/
  mbFix : List (Nat × Nat × Nat × Nat)
  /-- The mini-bus's grand-product depth (B1-IX: the record's `busDepth`, `⌈log₂⌉` of the push leaves; `P20`'s 13
  is `tMB`). -/
  mbD : Nat := tMB

instance : Inhabited TData := ⟨⟨[], [], [], 0, 0, 0, none, [], 0, [], tMB⟩⟩

/-! ## The zerocheck -/

/-- **The zerocheck** from `P`: `τ`, 20 equality-mode rounds from `0`, `a*, b*, c*`, the check
`final = a*·b* + c*`. Returns `r_x` and `[a*, b*, c*]`. -/
def zeroG (z g : Cell) (P : Nat) : BM (List Cell × List Cell) := do
  let tb ← ldEsP ((P + 40) / 8) 9 tX
  let q ← getPtr
  let fin ← QB.scRunQ3 (binParts tX) (zRP P / 8) (fun i => tb.1 + i) (fun _ => 1) z
  let abc ← ldEs ((zAbcP P + 40) / 8) 3 3
  let t ← mulAdd .E (abc.getD 0 z) (abc.getD 1 z) (abc.getD 2 z)
  assertEq fin t g
  pure ((List.range tX).map fun i => ec (q.e + 3 + 7 * i), abc)

/-! ## The wiring sumcheck and the virtual regions -/

/-- `eq(r_y^{≥ l}, base >> l)`: a region's selector at `r_y` (its high coordinates). -/
def regSelG (z o : Cell) (ry : List Cell) (R : TReg) : BM Cell := eqConstG z o (ry.drop R.log) (R.base >>> R.log)

/-- **The natively computed part of `z̃(r_y)`** (`virtE`): `PUB` (the child's header lanes, `qpub`), the word `1`,
and with `qltVirt` the `QLT` region. -/
def virtG (z o : Cell) (T : TData) (pb : Nat) (ry : List Cell) : BM Cell := do
  let sP ← regSelG z o ry ⟨T.pub, 10, 0⟩
  let vP ← Lvm.QAcc.qpub (fun i => ry.getD i z) z o 10 11 (pb + 1) pubLanes
  let w ← mulAdd .E sP vP z
  let e1 ← eqConstG z o ry T.one
  let w ← add w e1
  match T.qlt with
  | none => pure w
  | some (b, l, cs) => do
    let sQ ← regSelG z o ry ⟨b, l, 0⟩
    let vQ ← dotConstG (fun i => ry.getD i z) z o l cs
    mulAdd .E sQ vQ w

/-- **The wiring sumcheck** after the zerocheck: `γ`, 21 plain rounds from `a* + γ b* + γ² c*`, `v_o` and the
region values, the check `final = (v_A + γ v_B + γ² (v_D + v_W))·(Σ rv + virt(r_y))`. Returns `r_y`, `v`, `rv`. -/
def wireG (z o g : Cell) (T : TData) (pb P : Nat) (abc : List Cell) :
    BM (List Cell × List Cell × List Cell) := do
  let γ ← Lvm.QAcc.ldE ((wGP P + 40) / 8)
  let u ← mulAdd .E γ (abc.getD 2 z) (abc.getD 1 z)
  let c0 ← mulAdd .E γ u (abc.getD 0 z)
  let q ← getPtr
  let fin ← QB.scRunP3 (binParts tY) (wRP P / 8) c0
  let ry := (List.range tY).map fun i => ec (q.e + 3 + 6 * i)
  let vs ← ldEs ((wVP P + 40) / 8) 3 4
  let rv ← ldEs ((wVP P + 40) / 8 + 12) 3 4
  let dw ← add (vs.getD 2 z) (vs.getD 3 z)
  let m1 ← mulAdd .E γ dw (vs.getD 1 z)
  let m2 ← mulAdd .E γ m1 (vs.getD 0 z)
  let ve ← virtG z o T pb ry
  let s ← sumG z (rv ++ [ve])
  let pr ← mulAdd .E m2 s z
  assertEq fin pr g
  pure (ry, vs, rv)

/-! ## The relayout and its kernel (B-DES §1.4: the stride-17 map as a carry automaton) -/

/-- One step of the division by 17 at `p`-bit `i` (most significant first): from the remainders' weights `W`
(`none`: statically zero), for each `(rem, b)` the quotient bit `qb = [2 rem + b ≥ 17]`, the new remainder
`2 rem + b − 17 qb`, weight `W[rem]·eq(ρ_i, b)·eq(r_i, qb)`; at `i ≥ 14` (no quotient coordinate) only `qb = 0`
(the indicator of `p < 17·2^14`). -/
def divStep (z : Cell) (ρi : Cell) (ri : Option Cell) (W : List (Option Cell)) : BM (List (Option Cell)) := do
  let nρ ← neg1 ρi
  let c ← match ri with
    | none => pure [(0, 0, nρ), (1, 0, ρi)]
    | some r => do
      let nr ← neg1 r
      let c00 ← mulAdd .E nρ nr z
      let c10 ← mulAdd .E ρi nr z
      let c01 ← mulAdd .E nρ r z
      let c11 ← mulAdd .E ρi r z
      pure [(0, 0, c00), (1, 0, c10), (0, 1, c01), (1, 1, c11)]
  -- the incoming transitions of each new remainder
  let ins (r' : Nat) : List (Cell × Cell) :=
    (List.range 17).flatMap fun rem => match W.getD rem none with
      | none => []
      | some w => c.filterMap fun x =>
        let v := 2 * rem + x.1
        let qb := if 17 ≤ v then 1 else 0
        if qb = x.2.1 ∧ v - 17 * qb = r' then some (w, x.2.2) else none
  seqAll ((List.range 17).map fun r' => match ins r' with
    | [] => pure none
    | l => do
      let s ← Lvm.QAcc.macChain l z
      pure (some s))

/-- The automaton's run over `p`-bits `18 … 0`, from `W[0] = 1`. -/
def divRun (z o : Cell) (ρ r : List Cell) : Nat → List (Option Cell) → BM (List (Option Cell))
  | 0, W => pure W
  | n + 1, W => do
    let W' ← divStep z (ρ.getD n z) (if n < 14 then some (r.getD n z) else none) W
    divRun z o ρ r n W'

/-- `Σ_{p ≥ 17·2^14} eq(ρ, p)·eq(r, p)` (the identity part of the map): `Π_{i<14} t_i · ρ₁₈ r₁₈ ·
(Π_{14≤i<18} t_i − Π_{14≤i<18} (1+ρ_i)(1+r_i))`, `t_i = ρ_i r_i + (1+ρ_i)(1+r_i)`. -/
def tailG (z o : Cell) (ρ r : List Cell) : BM Cell := do
  let ts ← forN 19 fun i => do
    let a := ρ.getD i z
    let b := r.getD i z
    let na ← neg1 a
    let nb ← neg1 b
    let d0 ← mulAdd .E na nb z
    let d1 ← mulAdd .E a b z
    let t ← add d0 d1
    pure (d0, d1, t)
  let lo ← Lvm.QAcc.macChain [] o
  let prodG (l : List Cell) : BM Cell := l.foldlM (fun acc x => mulAdd .E acc x z) lo
  let pT ← prodG ((ts.take 14).map (·.2.2))
  let pM ← prodG (((ts.drop 14).take 4).map (·.2.2))
  let pZ ← prodG (((ts.drop 14).take 4).map (·.1))
  let df ← add pM pZ
  let h ← mulAdd .E pT (ts.getD 18 (z, z, z)).2.1 z
  mulAdd .E h df z

/-- **The relayout's kernel** `Σ_{y ∈ S_flat} eq(r_y, y)·eq(r, sflatW y)`: the region's selector (`r_y`'s two high
coordinates), times the division automaton's sum over `p < 17·2^14` with the lane coordinates `r_{14..18}` against
the remainder, plus the identity part above. -/
def relayKernG (z o : Cell) (T : TData) (ry r : List Cell) : BM Cell := do
  let sel ← regSelG z o ry ⟨T.sflat, 19, 0⟩
  let ρ := ry.take 19
  let W ← divRun z o ρ r 19 ((List.range 17).map fun i => if i = 0 then some o else none)
  let a ← Lvm.QAcc.eqDot (fun i => r.getD (14 + i) z) 2 5 z o (W.map fun w => w.getD z)
  let b ← tailG z o ρ r
  let s ← add a b
  mulAdd .E sel s z

/-- **The relayout** after the wiring: 19 plain rounds from `v_S`, `v_R`, the check `final = kern(r_y, r)·v_R`.
Returns `r` and `v_R`. -/
def relayG (z o g : Cell) (T : TData) (P : Nat) (ry : List Cell) (vS : Cell) : BM (List Cell × Cell) := do
  let q ← getPtr
  let fin ← QB.scRunP3 (binParts tR) (rRP P / 8) vS
  let rr := (List.range tR).map fun i => ec (q.e + 3 + 6 * i)
  let vR ← Lvm.QAcc.ldE ((rVP P + 40) / 8)
  let k ← relayKernG z o T ry rr
  let pr ← mulAdd .E k vR z
  assertEq fin pr g
  pure (rr, vR)

/-! ## A23 at `Φ_Q` (AC-Q's `qacc` with the typed instance: `dk = 2`, `D = 43`, no `PUB` table) -/

/-- **Q_acc, typed** from lane `L` (`8 L = aP P`): `κ'` (2 samples), `h'` (`tVars + 1`), `t'`, the zero scalar;
`y' = Σ_{o<4} eq(κ', o)·v_o`; `h'₀ = acc_in'.y`, `Σ h' = y'`; the line from `acc_in'.pt` to
`b = κ' ++ r_x ++ r_y` at `t'` and `h'(t')` equal to the current proof's `acc_in` (`PUB` lanes `615 + 3j`). -/
def qaccT (L pb : Nat) (rx ry vs : List Cell) : BM Unit := do
  let g := kc pb
  let zo ← Lvm.QAcc.consts pb
  let kb ← Lvm.QAcc.ldEsB ((List.range 2).map fun i => L + 5 + 9 * i)
  let y ← Lvm.QAcc.qyown kb 1 2 zo.1 zo.2 vs
  let h0 := L + 18
  let hb ← Lvm.QAcc.ldEsB ((List.range (tVars + 1)).map fun j => h0 + 5 + 3 * j)
  let ab ← Lvm.QAcc.ldEsB ((List.range (tVars + 1)).map Lvm.QAcc.accLane)
  Lvm.QAcc.assertEqE (ec hb) (ec (ab + tVars)) g
  let sh ← Lvm.QAcc.macChain ((List.range (tVars + 1)).map fun j => (zo.2, ec (hb + j))) zo.1
  Lvm.QAcc.assertEqE sh y g
  let t ← Lvm.QAcc.ldE (h0 + 3 * (tVars + 1) + 5)
  let hv ← Lvm.QAcc.horner ((List.range (tVars + 1)).map fun j => ec (hb + j)) t zo.1
  let bc := (List.range 2).map (fun j => ec (kb + j)) ++ rx ++ ry
  let pts ← Lvm.QAcc.linePts ((List.range tVars).map fun i => (ec (ab + i), bc.getD i (ec 0))) t
  let pc ← Lvm.QAcc.ldEsB ((List.range (tVars + 1)).map fun j => pb + 615 + 3 * j)
  let _ ← Lvm.QAcc.assertEqs ((List.range tVars).map fun i => (pts.getD i default, ec (pc + i))) g
  Lvm.QAcc.assertEqE hv (ec (pc + tVars)) g
  let zz ← Lvm.QAcc.ldE (h0 + 3 * (tVars + 1) + 9 + 5)
  assert0 zz g

/-! ## The mini-bus (B-DES §1.5: today's bus with one table, `2^13` leaves) -/

/-- `g^b·Π_i (1 + r_i + r_i·g^{s·2^i})`: the extension of the column `x ↦ g^{b + s x}` at `r` (`InArr.tab`'s
closed form `g^b·powEval r (g^s)`). The mini-bus's fixed columns are checked in the circuit, as `V_S` checks them
natively (`lbusTableCheckProg`): they are not in `Φ_Q`. -/
def powColGo (z : Cell) : List Cell → FK → Cell → BM Cell
  | [], _, acc => pure acc
  | x :: xs, c, acc => do
    let u ← lin .E (c + 1) 1 z x
    let acc' ← mulAdd .E acc u z
    powColGo z xs (c * c) acc'

/-- `g^b·powEval r (g^s)` in the circuit. -/
def powColG (z : Cell) (b s : Nat) (r : List Cell) : BM Cell := do
  let c ← const .E (Lvm.Loop.Build.gpow b) z
  powColGo z r (Lvm.Loop.Build.gpow s) c

section
variable {c : Ctx} {M : Mem}

/-- **`powColGo`'s value**: `acc · powEval r c` (one factor `1 + r_i (c^{2^i} + 1) = 1 − r_i + r_i c^{2^i}` per
coordinate, characteristic 2). -/
theorem powColGo_spec {z : Cell} (hz : z.val M = 0) : ∀ (xs : List Cell) (k : FK) (acc : Cell) (p : Ptr),
    SegsHold c M p (powColGo z xs k acc p).2 →
      (powColGo z xs k acc p).1.val M = acc.val M * powEval (xs.map (Cell.val M)) k
  | [], _, _, _, _ => by simp [powColGo, pure, powEval]
  | x :: xs, k, acc, p, h => by
    simp only [powColGo, bind_apply] at h ⊢
    rw [segsHold_append, segsHold_append] at h
    rw [powColGo_spec hz xs _ _ _ h.2.2, mulAdd_spec h.2.1, lin_spec h.1, hz, List.map_cons, powEval,
      Lvm.Loop.Build.ofK_add, Lvm.Loop.Build.ofK_one]
    rw [CharTwo.sub_eq_add]
    ring

/-- **`powColG`'s value** is `InArr.tab`'s address column's closed form `g^b·powEval r (g^s)`. -/
theorem powColG_spec {z : Cell} (hz : z.val M = 0) (b s : Nat) (r : List Cell) (p : Ptr)
    (h : SegsHold c M p (powColG z b s r p).2) :
    (powColG z b s r p).1.val M = FE.ofK (FK.x ^ b) * powEval (r.map (Cell.val M)) (FK.x ^ s) := by
  simp only [powColG, bind_apply] at h ⊢
  rw [segsHold_append] at h
  rw [powColGo_spec hz _ _ _ _ h.2, const, lin_spec h.1, hz, ofK_one]
  simp [Lvm.Loop.Build.gpow]

end

/-- The position after a bus phase of depth `d` from `P` (`busEnd` at depth `d`). -/
def busEndD (d P : Nat) : Nat := layersEnd (gkrSteps d) 0 (busP1 P + 48) + 24

/-- **The bus phase at depth `d`** (`busG` with the depth a parameter). -/
def busGD (d : Nat) (z o g : Cell) (P : Nat) : BM BusC := do
  let al ← ldEs ((P + 40) / 8) 9 busBits
  let be ← Lvm.Har.ldE ((P + 40) / 8 + 9 * busBits)
  let sh ← Lvm.Har.ldE ((busP1 P + 40) / 8)
  let cnt ← Lvm.Har.ldE ((busP1 P + 40) / 8 + 3)
  QB.countNZ z o g cnt
  let r ← layersG z o g (gkrSteps d) (busP1 P + 48) [sh, sh, cnt] ⟨0, 0, 0, 0, 0⟩
  let ld ← Lvm.Har.ldE ((busEndD d P + 16) / 8)
  assert0 ld g
  pure ⟨al, be, cnt, r.2.cells, r.1⟩

/-- **The mini-bus**: the bus at depth `T.mbD` (`tMB` at `P20`) from `P`, then the table phase on the mini-bus's
shapes. -/
def miniG (z o g : Cell) (T : TData) (P : Nat) : BM (BusC × List (List Cell × List Cell)) := do
  let bus ← busGD T.mbD z o g P
  let tab ← tabG T.mbS T.mbR (busEndD T.mbD P) z o g bus
  let _ ← seqAll (T.mbFix.map fun f => do
    let e := tab.getD f.1 default
    let v ← powColG z f.2.2.1 f.2.2.2 e.1
    assertEq (e.2.getD f.2.1 z) v g)
  pure (bus, tab)

/-! ## The whole gadget and its claims -/

/-- What the typed phases hand on. -/
structure TypedC where
  rx : List Cell
  ry : List Cell
  abc : List Cell
  vs : List Cell
  rv : List Cell
  rr : List Cell
  vR : Cell
  bus : BusC
  tab : List (List Cell × List Cell)

/-- A region family's claim: `Σ_reg eq(r_y^{≥ log}, base >> log)·blk_reg~(r_y^{< log}) = v` (`sumClaim`). -/
def regClaimG (z o : Cell) (com : Com) (nu : Nat) (rs : List TReg) (ry : List Cell) (v : Cell) : BM CClaim := do
  let parts ← seqAll (rs.map fun R => do
    let s ← regSelG z o ry R
    pure (s, (⟨R.log, R.off⟩ : Placement), ry.take R.log))
  pure ⟨com, .sum nu parts, v⟩

/-- **The typed phases' claims** (`typedClaims`): `C_rec`'s (the relayout's point claim, `σ′`'s regions, the
mini-bus's), then `C_main`'s (the committed regions, the `KS` aliases, the mini-bus's). -/
def typedClaimsC (z o : Cell) (T : TData) (nuMain : Nat) (t : TypedC) : BM (List CClaim × List CClaim) := do
  let cS ← regClaimG z o .crec tR T.sig t.ry (t.rv.getD 2 z)
  let cC ← regClaimG z o .main nuMain T.com t.ry (t.rv.getD 0 z)
  let cK ← regClaimG z o .main nuMain T.ks t.ry (t.rv.getD 3 z)
  let mb := tabClaims T.mbS t.tab z
  pure (⟨.crec, .point ⟨tR, 0⟩ t.rr, t.vR⟩ :: cS :: mb.filter (·.com == .crec),
    cC :: cK :: mb.filter (·.com == .main))

/-- **The typed backend's verifier** from position `P` (`typedPos`), the current proof's `PUB` at cell `pb` (its
lane 0 the node flag `g`), `z`/`o` the `E` constants. -/
def typedG (T : TData) (pb P : Nat) (z o : Cell) : BM TypedC := do
  let g := kc pb
  let zr ← zeroG z g P
  let w ← wireG z o g T pb P zr.2
  let r ← relayG z o g T P w.1 (w.2.2.getD 1 z)
  qaccT (aP P / 8) pb zr.1 w.1 w.2.1
  let mb ← miniG z o g T (mbP P)
  pure ⟨zr.1, w.1, zr.2, w.2.1, w.2.2, r.1, r.2, mb.1, mb.2⟩

/-- **The typed phases' end**: after the mini-bus's table phase (`tabEnd`). The schedule's tape phase must start
here (assumption 7; INT checks `phaseByte p .tape = typedEnd (typedPos p) + …` by `decide` at the refreeze). -/
def typedEnd (T : TData) (P : Nat) : Nat := tabEnd T.mbS T.mbR (busEndD T.mbD (mbP P))

/-- The typed phases' start: where the bus phase starts today (after `q₀`, the seed and the two cap skips). -/
def typedPos (p : Params) : Nat := busPos p

end Lvm.QTyped
