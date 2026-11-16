-- New for lvm2 (roll 8 = B1, B1-K): the layout specification of the node program (`LSpec`): its input regions
-- (`LvmQAsmLay`), QLT's static `readd` targets (`qltPadded`, B1-P1P2 §1 "Row kinds"), the `BITS` tables
-- (`bspecs`); and the typed layouts `layQ C D`. Adapted from B1-W's `mkWorld` (its probe tool).
import LvmTypedLay
import LvmQAsmProg
import LvmQTypedBits
import LvmQAsmArith2Tab
import LvmQAccParts
import LvmQAcc
import LvmVFastQ

-- (GOLF2: 11 declarations that `certified` does not use moved verbatim to `LvmE2QNodeChkGOff`, outside its import closure.)

-- ===== merged from `LvmQTyped` (GOLF module merge: `LvmQTyped.lean` is now a stub importing `LvmTypedLayQ`) =====
section
-- New for lvm2 (roll 8 = B1, B1-Q; B-DES §1.2, §1.4, §1.5): the in-circuit verifier of the typed backend's phases
-- (the child's zerocheck, wiring sumcheck, `S_flat` relayout, A23 at `Φ_Q`, the mini-bus) as one gadget `typedG`,
-- replacing Q_arith's bus, table, `qacc` and table-claim sections. Reuses QA2's round runners (`scRunQ3`,
-- `scRunP3`), HAR-BT's `busG`/`tabG` pattern, AC-Q's `qacc` pieces (`qyown`, `qpub`, `eqDot`, `linePts`).

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
/-- The mini-bus's depth (`miniDepth`; M′ `S2GM`: 12, B1: 13). -/
abbrev tMB : Nat := 12

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
  /-- `σ′`'s regions (M′: the stream block's column 17, `C_main` words). -/
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

/-- **The typed phases' claims** (`typedClaims`; M′, lvm2 roll 11 `S2GM`: all on `C_main`, `TypedV.typedClaimsN`'s
order): the relayout's point claim on the stream block (`⟨19, sOff⟩`), `σ′`'s regions and the mini-bus's `C_rec`
claims (none: its seed columns are `C_main` words) first, then the committed regions, the `KS` aliases and the
mini-bus's `C_main` claims. -/
def typedClaimsC (z o : Cell) (T : TData) (nuMain sOff : Nat) (t : TypedC) : BM (List CClaim × List CClaim) := do
  let cS ← regClaimG z o .main nuMain T.sig t.ry (t.rv.getD 2 z)
  let cC ← regClaimG z o .main nuMain T.com t.ry (t.rv.getD 0 z)
  let cK ← regClaimG z o .main nuMain T.ks t.ry (t.rv.getD 3 z)
  let mb := tabClaims T.mbS t.tab z
  pure (⟨.main, .point ⟨tR, sOff⟩ t.rr, t.vR⟩ :: cS :: mb.filter (·.com == .crec),
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

/-- The typed phases' start: where the bus phase starts today (after `q₀`, the seed and the two cap skips). -/
def typedPos (p : Params) : Nat := busPos p

end Lvm.QTyped
end
-- ===== end of `LvmQTyped` =====

-- ===== merged from `LvmQTypedMB` (GOLF module merge: `LvmQTypedMB.lean` is now a stub importing `LvmTypedLayQ`) =====
section
-- New for lvm2 (roll 8 = B1, B1-Q; B-DES §1.5): the mini-bus `mbT`. `capTpl`'s `readd`s (the only reads left on a
-- bus) against seeds of the cap regions only, `2^13` leaves. Reuses `InArr.tab` (the seed side, `LvmM3LoopTab`),
-- the `Tab`/`Key` data of `LvmM3Tab`, `openLoops`' cap parameters (`LvmQLink`, untouched).

/-!
# The mini-bus's tables

Memory checking as WP-9's (`LvmM3Inst`): a read with count column `c` pulls `⟨k, c⟩` and pushes `⟨k, g·c⟩`; a seed
with finalize column `f` pushes `⟨k, 1⟩` and pulls `⟨k, f⟩`. Only `capTpl`'s reads are on this bus.

* **Seeds** (`mbArrs`): per lane class `l < 17` and aligned block of `2^4` rows meeting some cap region
  (`capRegions`: `capTpl`'s `[capL, capL + 4·2^c)`, `c = height − path`), once (`eraseDups`), an `InArr` over the
  stream cells `sb + 17 q + l` whose value column is the stream block's lane `l` there (M′: a `C_main` word,
  `sCol p l + q`; B1: `C_rec`'s; `S_flat`'s words, as today's lane arrays). Every cap cell is seeded (**`mbSeed_cover`**) and no cell twice (blocks are distinct and aligned).
* **Reads** (`capReads`): per loop block of the program with four `readd` rows (`capTpl`'s; QLT's loop has nine)
  and each of them, a table of `2^ℓ` rows: the address column (the words of the `readd`'s address cells), the value
  column (the words of its result cells), the read count; one read `⟨g^3, addr, [val]⟩`. Every iteration is a real
  read (the padded positions read cap cell `0`), so no padding row. The placements are the layout's (`wordK`, the
  word of a `K` cell; `MbFit`: the address and result cells of a block's row are consecutive words).
* **Targets**: a cap read's address is `g^{lo + 4·idx + r}` with `idx < 2^c`, `r < 4` (`capTpl`), inside the region
  (**`capTarget_mem`**), hence seeded (**`capRead_seeded`**). With honest counts (`g^0, g^1, …` per cell in read
  order, finalize `g^{reads}`) the bus balances.
-/

set_option autoImplicit false

namespace Lvm.QTyped

open Lvm Lvm.Loop Lvm.Loop.Build Lvm.QAsm Lvm.Har Lvm.M3 Lvm.QLink

/-! ## The seed side -/

/-- The cap regions `(first stream lane, cap bits)` of the openings (`openLoops`' `capL`, `height − path`). -/
def capRegions (p : Params) : List (Nat × Nat) :=
  ((opens p).map fun o => (eLane p o.ce + 1 + o.co / 8, o.L.height - o.L.path)).eraseDups

/-- The rows `[q0, q1)` of lane class `l < 17` whose lanes `17 q + l` lie in `[a, a + n)`. -/
def laneRows (a n l : Nat) : Nat × Nat := ((a + 16 - l) / 17, (a + n + 16 - l) / 17)

/-- The aligned blocks of `2^t` rows covering `[q0, q1)` (their first rows): from `q0`'s block, as many as cover
`⌈n/17⌉` rows at the worst alignment (B1-IX: a fixed count, so that the mini-bus's record does not depend on where
the caps fall in the stream, and the refreeze reaches a fixpoint). -/
def laneBlocks (a n l t : Nat) : List Nat :=
  let b0 := (laneRows a n l).1 / 2 ^ t
  (List.range (((n + 16) / 17 + 2 ^ t - 2) / 2 ^ t + 1)).map fun i => (b0 + i) * 2 ^ t

/-- The mini-bus's seed block: `2^4` rows. -/
abbrev mbBlk : Nat := 4

/-- The seeded `(lane class, first row)` blocks, each once. -/
def mbBlocks (p : Params) : List (Nat × Nat) :=
  ((capRegions p).flatMap fun c => (List.range 17).flatMap fun l =>
    (laneBlocks c.1 (4 * 2 ^ c.2) l mbBlk).map fun q => (l, q)).eraseDups

/-- **The mini-bus's seed arrays** (finalize count of array `k` at `fin k`; M′: value columns on `C_main`). -/
def mbArrs (C : QCfg) (fin : Nat → Bool × Nat) : List InArr :=
  (mbBlocks C.p).zipIdx.map fun x =>
    ⟨.K, mbBlk, (lay C).sb + 17 * x.1.2 + x.1.1, 17, [(false, Lvm.sCol C.p x.1.1 + x.1.2)], fin x.2, none⟩

/-- The seed arrays' fixed address columns, for the circuit's check (`TData.mbFix`): table `k`, column `2`. -/
def mbFixOf (C : QCfg) : List (Nat × Nat × Nat × Nat) :=
  (mbArrs C fun _ => (false, 0)).zipIdx.map fun a => (a.2, a.1.val.length + 1, a.1.base, a.1.stride)

/-! ## The read side -/

/-- Q_link alone (its cells are the B program's first cells: Q_link runs first). -/
def qlinkProg (C : QCfg) : Program := toProgram (nK C) 0 (qlink C.p (lay C))

/-- The `readd` rows of a block's template. -/
def readdRows (B : Block) : List Nat :=
  (List.range B.tpl.length).filter fun t => match (B.tpl.getD t default).op with
    | .readd _ _ => true
    | _ => false

/-- **`capTpl`'s reads**: `(block, template row)` of every `readd` row of a block with four (`capTpl`'s; QLT's
loop has nine). -/
def capReadRows (Q : Program) : List (Nat × Nat) :=
  (List.range Q.blocks.length).flatMap fun b =>
    if (readdRows (Q.blk b)).length = 4 then (readdRows (Q.blk b)).map (b, ·) else []

/-- Row `t`'s result cell at iteration `jf` (`K`). -/
def resCell (Q : Program) (b t jf : Nat) : Nat :=
  Q.start .K b + (Q.blk b).tw .K * jf + (Q.blk b).rank .K t

/-- The address cell of `readd` row `t` at iteration `jf`. -/
def adrCell (Q : Program) (b t jf : Nat) : Nat :=
  (((Q.blk b).tpl.getD t default).args.getD 0 default).at (unflat (Q.blk b).dims jf)

/-- The read key: `⟨g^3, column 0, [column 1]⟩`. -/
def readKey : Key := ⟨sep .K, CPoly.var 0, [CPoly.var 1]⟩

/-- **A read table**: `2^ℓ` reads of block `b`'s row `t`, address column at word `wa`, value column at `wv`, count
column at `wc` (all `C_main`). -/
def readTab (τ wa wv wc : Nat) : Tab where
  τ := τ
  cols := [.com false wa, .com false wv, .com false wc]
  cons := []
  reads := [(readKey, 2)]
  seeds := []
  deg := by
    refine ⟨fun C hC ↦ by simp at hC, fun r hr ↦ ?_, fun s hs ↦ by simp at hs⟩
    simp only [List.mem_singleton] at hr; subst hr
    have hv : ∀ i, CPoly.Deg2 (CPoly.var i) := fun i m hm ↦ by
      simp [CPoly.var] at hm; subst hm; simp
    exact ⟨hv _, fun P hP ↦ by simp [readKey] at hP; subst hP; exact hv _⟩

/-- **The read tables** of `capTpl`'s reads; `wordK` the layout's word of a `K` cell, `cnt k` table `k`'s count
column. -/
def capReads (C : QCfg) (wordK : Nat → Nat) (cnt : Nat → Nat) : List Tab :=
  let Q := qlinkProg C
  (capReadRows Q).zipIdx.map fun x =>
    readTab (Q.blk x.1.1).lsize (wordK (adrCell Q x.1.1 x.1.2 0)) (wordK (resCell Q x.1.1 x.1.2 0)) (cnt x.2)

/-- **The layout fits the read tables**: a read table's address and result cells are consecutive words. -/
def MbFit (C : QCfg) (wordK : Nat → Nat) : Prop :=
  ∀ x ∈ capReadRows (qlinkProg C), ∀ jf < 2 ^ ((qlinkProg C).blk x.1).lsize,
    wordK (adrCell (qlinkProg C) x.1 x.2 jf) = wordK (adrCell (qlinkProg C) x.1 x.2 0) + jf ∧
    wordK (resCell (qlinkProg C) x.1 x.2 jf) = wordK (resCell (qlinkProg C) x.1 x.2 0) + jf

/-- **The mini-bus's tables**: the seed arrays, then the read tables. -/
def mbT (C : QCfg) (wordK : Nat → Nat) (fin : Nat → Bool × Nat) (cnt : Nat → Nat) : List Tab :=
  (mbArrs C fin).map InArr.tab ++ capReads C wordK cnt

/-- **Each read block is a cap region's** (a native check, `true` at `P20` and `P8` [B1-Q]): a block with four
`readd` rows has `capTpl`'s length `2c + 16` and its address row's constant `g^{sb + a}` for a region `(a, c)` of
`capRegions`, and its reads search the stream. Then its targets are that region's (`capTpl`: `g^{lo + 4 idx + r}`,
`idx < 2^c`), so seeded (`capRead_seeded`), each once (`mbBlocks_disjoint`): with honest counts (`g^0 … g^{m−1}` on
a cell's `m` reads in order, finalize `g^m`) every cell's pushes `1, g, …, g^m` are its pulls, and the bus
balances. -/
def capBlocksOk (C : QCfg) : Bool :=
  let Q := qlinkProg C
  (capReadRows Q).all fun x =>
    let B := Q.blk x.1
    (capRegions C.p).any fun r =>
      B.tpl.length == 2 * r.2 + 16 &&
      (match (B.tpl.getD 2 default).op with
        | .lin _ k' => k' == Lvm.Loop.Build.gpow ((lay C).sb + r.1)
        | _ => false) &&
      (match (B.tpl.getD x.2 default).op with
        | .readd lo m => lo == (lay C).sb && m == (lay C).m
        | _ => false)

/-! ## Value lemmas -/

end Lvm.QTyped
end
-- ===== end of `LvmQTypedMB` =====

-- ===== merged from `LvmQTypedProg` (GOLF module merge: `LvmQTypedProg.lean` is now a stub importing `LvmTypedLayQ`) =====
section
-- New for lvm2 (roll 8 = B1, B1-Q): the B program. Q_arith without the bus, the table sumcheck, `qacc` and the
-- table claims (and without `withPad`: no record-dependent table groups remain), calling the typed verifier
-- `typedG`. The shipped bus program `QT` (`LvmQAsmProg`) is unchanged and stays the oracle until INT switches.

/-!
# The B program (`QB`)

* **`qarithB C T o`**: after phases 4–7 (`phases47`, unchanged), the typed phases' verifier (`typedG` at
  `typedPos`), the `KS` ring switch and link (unchanged), the claims in `assembleT₂`'s order (the typed phases'
  first, then the tape's, `KS`'s, `KS`'s outputs, the `KS` link's), the opening (`openG`: M′, `C_main`'s alone).
* **`QB C T = toProgram (nK C) 0 (qlink; qsig; phases47 >>= qarithB)`**: `Q_link`, `Q_sig` as today.
* **`tdataP C`**: a placeholder record of the typed phases' static data (the region list's shape the layout
  solver will fill: one committed region, one `KS` alias region, `σ′`, `S_flat`, `PUB`, the word `1`; the
  mini-bus's arrays `mbArrs`). INT's refreeze replaces it by the solver's record (the same fixed-point pattern as
  `QData`).
-/

set_option autoImplicit false

namespace Lvm.QTyped

open Lvm Lvm.Loop Lvm.Loop.Build Lvm.QAsm Lvm.Har Lvm.M3 Lvm.QLink Lvm.QSig

/-- **Q_arith of the B program** on the static data `T`. -/
def qarithB (C : QCfg) (T : TData) (o : P47Out) : BM Unit := do
  let g := kc (pbB C)
  let p := C.p
  let z ← const .E 0 (kc 0)
  let one ← const .E 1 (kc 0)
  let ksB : Placement := ⟨p.ksLog + slotLog, (layout0 p).ks⟩
  let t ← typedG T (pbB C) (typedPos p) z one
  let tc ← typedClaimsC z one T p.nuMain (layout0 p).s t
  let rgK ← ringGkr (p.ksLog - 4) (Lvm.Har.aLane p 6) z.n
  let clK ← ksLinkG p (Lvm.Har.aLane p 7) z.n one.n
  let cs := tc.1 ++ tc.2 ++ (tapeClaimsC p z.n one.n o ++ kClaimsC ksB o.kko rgK) ++
    ksOutC p o.rk o.vk z.n one.n ++ clK
  openG (cfgMain p (posBase C) (pwBase C))
    (p.logN == 20 && p.nuMain == CMain.nu20) cs o.mb z one g

/-- The B program's segments. -/
def qprogB (C : QCfg) (T : TData) : BM Unit := do
  qlink C.p (lay C)
  let _ ← qsig (sigIn C)
  phases47 C >>= qarithB C T

/-- **The B program** on the static data `T`. -/
def QB (C : QCfg) (T : TData) : Program := toProgram (nK C) 0 (qprogB C T)

/-- **A placeholder of the typed phases' static data** (shape only; INT's refreeze gives the solver's). -/
def tdataP (C : QCfg) : TData where
  com := [⟨0, 20, 0⟩]
  ks := [⟨3 * 2 ^ 19 + 2 ^ 14, 14, 0⟩]
  sig := [⟨3 * 2 ^ 19, 10, 17 * 2 ^ 14⟩]
  sflat := 2 ^ 20
  pub := 3 * 2 ^ 19 + 2 ^ 10
  one := 3 * 2 ^ 19 + 2 ^ 11
  qlt := none
  mbS := (mbT C (fun _ => 0) (fun _ => (false, 0)) (fun _ => 0)).map Tab.shape
  mbR := ((mbT C (fun _ => 0) (fun _ => (false, 0)) (fun _ => 0)).map (·.τ)).foldl max 0
  mbFix := mbFixOf C

end Lvm.QTyped
end
-- ===== end of `LvmQTypedProg` =====

-- ===== merged from `LvmQTypedSBits` (GOLF module merge: `LvmQTypedSBits.lean` is now a stub importing `LvmTypedLayQ`) =====
section
-- New for lvm2 (roll 8 = B1, B1-IX-S): the typed V_S's start-up. The `BITS` classes (`bspecs`) and QLT's data
-- with their parameters computed once: `bspecsF = bspecs`, `qltPaddedF = qltPadded`, `qltCstF = qltCst`.
-- Adapts V-PERF's `posCellF`/`posOcF` (`LvmVFast`, not imported: it imports a submission) and `qltEntriesF`.

/-!
# The `BITS` classes and QLT's data, fast

`opens p`, `plan p`, `spB C`, `bsB C`, `pwB C`, `ansLane p i`, `bitBase p lay k` each cost about a millisecond
[measured, P20], and the lane classes' cell functions (`posSpec`'s `wc`, `oc`), the `s'` class's and the PoW
class's call them at every row: B1-Q's chunking (`BSpec.ablks`) took 36–65 s at P20. Here the same classes with
those values computed once per class:

* **`bspecsF C D = bspecs C D`** (`bspecsF_eq`): `posSpecF` (lane classes; the openings' bases tabulated, the
  rows as an array with their `laneOuts`, `ansLaneF`), `sSpecF`, `powSpecF`;
* **`qltPaddedF = qltPadded`**, **`qltCstF = qltCst`** (V-PERF's `qltEntriesF`, `qltDataF`).
-/

set_option autoImplicit false

namespace Lvm.QTyped

open Lvm Lvm.Loop Lvm.QAsm Lvm.QLink Lvm.BitsTab Lvm.Bits Lvm.VF Lvm.Replay Lvm.SigBits

/-! ## `posCell`, `posOc` with their bases passed in (V-PERF's `posCellF`, `posOcF`) -/

/-- `posCell C k o x` with `bb = bitBase`, `sb = spB C + spBefore`, `fl = flB C`, `pa2 = 2^pa`,
`px = posIdx … k 0` (`H`, `t`, `pT`, `nR` the opening's height, `t`, `padT t`, `nRows`). -/
def posCellS (H t pT nR bb sb fl pa2 px x : Nat) : BOut × Nat × Nat → Nat
  | (_, 0, n) =>
    let j := 8 * x + n / H
    if j < pT then bb + H * j + n % H else sb + 2 * (8 * nR - t) + H * (j - pT) + n % H
  | (_, kind, i) =>
    let j := 8 * x + i
    if j < t then fl + (if kind = 1 then 0 else pa2) + (px + j) else sb + 2 * (j - t) + (kind - 1)

theorem posCellS_eq (C : QCfg) (k : Nat) (o : OpenInfo) (x : Nat) (u : BOut × Nat × Nat) :
    posCellS o.L.height o.L.t (padT o.L.t) (nRows o) (bitBase C.p (lay C) k)
      (spB C + spBefore C.p k) (flB C) (2 ^ C.pa) (posIdx C.p k 0) x u = posCell C k o x u := by
  obtain ⟨b, kind, n⟩ := u
  cases kind with
  | zero => rfl
  | succ kind =>
    have hp : posIdx C.p k (8 * x + n) = posIdx C.p k 0 + (8 * x + n) := by unfold posIdx; omega
    simp only [posCellS, posCell]
    rw [hp]

/-- `posOc C l U r j` with `u = U[j]`, the opening's bases `b`, the row's outputs `LO = laneOuts H l`, `fl`,
`pa2` passed in. -/
def posOcS (l : Nat) (u : BOut) (LO : List (BOut × Nat × Nat)) (fl pa2 : Nat) (b : Nat × Nat × Nat)
    (r : Nat × OpenInfo × Nat × Nat) (j : Nat) : Nat :=
  match LO.find? (fun e => e.1 == u) with
  | some e => posCellS r.2.1.L.height r.2.1.L.t (padT r.2.1.L.t) (nRows r.2.1) b.1 b.2.1 fl pa2 b.2.2 r.2.2.1 e
  | none => r.2.2.2 + (j - QAsm.laneBits r.2.1.L.height l)

theorem posOcS_eq (C : QCfg) (l : Nat) (U : List BOut) (r : Nat × OpenInfo × Nat × Nat) (j : Nat) :
    posOcS l (U.getD j (.bit 0)) (laneOuts r.2.1.L.height l) (flB C) (2 ^ C.pa)
      (bitBase C.p (lay C) r.1, spB C + spBefore C.p r.1, posIdx C.p r.1 0) r j = posOc C l U r j := by
  unfold posOcS posOc
  generalize (laneOuts r.2.1.L.height l).find? (fun e => e.1 == U.getD j (.bit 0)) = d
  cases d with
  | none => rfl
  | some e => exact posCellS_eq C r.1 r.2.1 r.2.2.1 e

/-! ## The openings' bases, once -/

/-- An opening's bases `(bitBase, spB + spBefore, posIdx … 0)`. -/
def opBase (C : QCfg) (k : Nat) : Nat × Nat × Nat := (bitBase C.p (lay C) k, spB C + spBefore C.p k, posIdx C.p k 0)

/-- **The openings' bases, tabulated** on the openings computed once (`opBaseT_eq`). -/
def opBaseT (C : QCfg) : Array (Nat × Nat × Nat) :=
  let OP := opens C.p
  let bb := (lay C).bb
  let sp := spB C
  (Array.range OP.length).map fun k =>
    (bb + ((OP.take k).map fun o => padT o.L.t * o.L.height).sum, sp + ((OP.take k).map spOf).sum,
      ((OP.take k).map fun o => o.L.t).sum + 0)

/-- A tabulated function with its fallback. -/
def tabOr {α : Type} (A : Array α) (f : Nat → α) (k : Nat) : α := if h : k < A.size then A[k] else f k

theorem tabOr_eq {α : Type} (n : Nat) (f : Nat → α) (A : Array α) (hA : A = (Array.range n).map f) :
    tabOr A f = f := by
  funext k
  unfold tabOr
  split
  · subst hA; simp
  · rfl

theorem opBaseT_eq (C : QCfg) : tabOr (opBaseT C) (opBase C) = opBase C :=
  tabOr_eq (opens C.p).length (opBase C) (opBaseT C) rfl

/-! ## The lane classes -/

/-- Row `y`'s data in lane class `l` (class rows `R`, bases `BT`): the class row, its `laneOuts`, its opening's
bases. -/
def rdOf (C : QCfg) (l : Nat) (R : List (Nat × OpenInfo × Nat × Nat)) (BT : Array (Nat × Nat × Nat)) (y : Nat) :
    (Nat × OpenInfo × Nat × Nat) × List (BOut × Nat × Nat) × (Nat × Nat × Nat) :=
  let r := R.getD y default
  (r, laneOuts r.2.1.L.height l, tabOr BT (opBase C) r.1)

/-- Lane class `l`'s output cell `j` at row `y`, from the row data (`RD`, `rd` its fallback). -/
def ocT (l fl pa2 : Nat) (UA : Array BOut)
    (RD : Array ((Nat × OpenInfo × Nat × Nat) × List (BOut × Nat × Nat) × (Nat × Nat × Nat)))
    (rd : Nat → (Nat × OpenInfo × Nat × Nat) × List (BOut × Nat × Nat) × (Nat × Nat × Nat)) (j y : Nat) : Nat :=
  let d := tabOr RD rd y
  posOcS l (UA.getD j (.bit 0)) d.2.1 fl pa2 d.2.2 d.1 j

theorem ocT_spec (C : QCfg) (l j y : Nat) :
    ocT l (flB C) (2 ^ C.pa) (lnOuts C.p l).toArray
      ((Array.range (posRows C l).length).map (rdOf C l (posRows C l) (opBaseT C)))
      (rdOf C l (posRows C l) (opBaseT C)) j y = posOc C l (lnOuts C.p l) ((posRows C l).getD y default) j := by
  unfold ocT
  rw [tabOr_eq _ _ _ rfl]
  simp only [rdOf, opBaseT_eq, opBase, toArray_getD]
  exact posOcS_eq C l _ _ j

/-- Lane class `l`'s word cell at row `y` (`RA` the class rows). -/
def wcT (C : QCfg) (l : Nat) (O0 : Array Nat) (PA : Array Replay.PE) (RA : Array (Nat × OpenInfo × Nat × Nat))
    (y : Nat) : Nat :=
  let r := RA.getD y default
  ansLaneF O0 PA C.p (r.2.1.pe + r.2.2.1) + l

theorem wcT_spec (C : QCfg) (l y : Nat) :
    wcT C l (offs C.p) (plan C.p).toArray (posRows C l).toArray y =
      ansLane C.p (((posRows C l).getD y default).2.1.pe + ((posRows C l).getD y default).2.2.1) + l := by
  simp only [wcT, toArray_getD, ansLaneF_eq']

/-- **Lane class `l`** (`posSpec`) with its row data tabulated (`posSpecF_eq`). -/
def posSpecF (C : QCfg) (bpl : Nat → Nat → Bool × Nat) (l : Nat) : BSpec :=
  let U := lnOuts C.p l
  let R := posRows C l
  let rd := rdOf C l R (opBaseT C)
  let RD := (Array.range R.length).map rd
  let fl := flB C
  let pa2 := 2 ^ C.pa
  let UA := U.toArray
  let O0 := offs C.p
  let PA := (plan C.p).toArray
  let RA := R.toArray
  { τ := clog2 R.length, n := R.length, outs := U, rd := true,
    wc := wcT C l O0 PA RA,
    oc := ocT l fl pa2 UA RD rd,
    pl := bpl l, sh := lnSh C.p l,
    hsh := fun j hj x hx => (ocT_spec C l j x).trans
      ((posOc_sh C l j hj x hx).trans (congrArg (· + j) (ocT_spec C l 0 x).symm)) }

theorem posSpecF_eq (C : QCfg) (bpl : Nat → Nat → Bool × Nat) (l : Nat) : posSpecF C bpl l = posSpec C bpl l := by
  unfold posSpecF posSpec
  simp only [BSpec.mk.injEq, true_and, and_true]
  exact ⟨funext fun y => wcT_spec C l y, funext fun j => funext fun y => ocT_spec C l j y⟩

/-- **The lane classes** (`posSpecs`). -/
def posSpecsF (C : QCfg) (bpl : Nat → Nat → Bool × Nat) : List BSpec := (List.range (nPosCls C)).map (posSpecF C bpl)

theorem posSpecsF_eq (C : QCfg) (bpl : Nat → Nat → Bool × Nat) : posSpecsF C bpl = posSpecs C bpl := by
  unfold posSpecsF posSpecs
  rw [show posSpecF C bpl = posSpec C bpl from funext (posSpecF_eq C bpl)]

/-! ## The `s'` and PoW classes -/

/-- **The `s'` bit class** (`sSpec`) with `sigIn`'s `hd` and `bsB` computed once. -/
def sSpecF (C : QCfg) (pl : Nat → Bool × Nat) : BSpec :=
  let hd := (sigIn C).hd
  let bs := bsB C
  ⟨2, 4, (List.range 64).map BOut.bit, true, fun x => hd + 9 + x, fun j x => bs + 64 * x + j, pl,
    64, by intros; omega⟩

theorem sSpecF_eq (C : QCfg) (pl : Nat → Bool × Nat) : sSpecF C pl = sSpec C pl := rfl

/-- **The PoW class** (`powSpec`) with the openings, `pwB` and the plan's offsets computed once. -/
def powSpecF (C : QCfg) (pl : Nat → Bool × Nat) : BSpec :=
  let OP := opens C.p
  let OA := OP.toArray
  let O0 := offs C.p
  let PA := (plan C.p).toArray
  let pw := pwB C
  ⟨clog2 OP.length, OP.length, [BOut.fld 0 (64 - C.p.grind) 0], true,
    fun x => ansLaneF O0 PA C.p ((OA.getD x default).pe - 1) + 2, fun _ x => pw + x, pl, 0,
    fun _ h => absurd h (Nat.not_lt_zero _)⟩

theorem powSpecF_eq (C : QCfg) (pl : Nat → Bool × Nat) : powSpecF C pl = powSpec C pl := by
  unfold powSpecF powSpec
  simp only [BSpec.mk.injEq, true_and, and_true]
  funext x
  rw [toArray_getD, ansLaneF_eq']

/-! ## The classes -/

/-- **The node program's `BITS` classes** (`bspecs`), fast. -/
def bspecsF (C : QCfg) (D : QData) : List BSpec :=
  sigSpecs (sigIn C) (sigOut C) (bplOf D) ++ posSpecsF C (fun c => bplOf D (6 + c)) ++
    ([sSpecF C (bplOf D (6 + nPosCls C)), powSpecF C (bplOf D (7 + nPosCls C))] ++
      (if C.p.leafOut then Lvm.QSig.sigSpecsC (sigInLC C) (sigInLC C).ys (sigOutSC C).2.pa
        (fun k => bplOf D (8 + nPosCls C + k)) else []))

theorem bspecsF_eq (C : QCfg) (D : QData) : bspecsF C D = bspecs C D := by
  unfold bspecsF bspecs
  rw [posSpecsF_eq, sSpecF_eq, powSpecF_eq]

/-! ## QLT's entries -/

/-- `qltPadded` on V-PERF's `qltEntriesF`. -/
def qltPaddedF (p : Params) (lay : Layout) : List (Nat × Nat × Nat) :=
  let E := qltEntriesF p lay
  E ++ List.replicate (2 ^ lay.aQ - E.length) (lay.sb, lay.sb + 1, lane0C)

theorem qltPaddedF_eq (p : Params) (lay : Layout) : qltPaddedF p lay = qltPadded p lay := by
  unfold qltPaddedF qltPadded
  rw [qltEntriesF_eq]

end Lvm.QTyped
end
-- ===== end of `LvmQTypedSBits` =====

/-!
# The node program's layout

* `inRegs C`: `S_flat` (`[0, 17·2^rl)`), `σ′`, the `KS` aliases (`xs`, `ys`, `md`), `PUB`, `QLT` (virtual) and the
  `BITS` outputs (committed, B1-P1P2 §5.3).
* `qltAlias C Q`: a `readd` whose address operand is QLT's `α` or `β` column, or a `lin (g^l + 1) 0` of one in the
  same block, reads stream cell `e₁ + l` (resp. `e₂ + l`) of the iteration's padded QLT entry: a static alias.
  Every other `readd` (`capTpl`'s) is committed (the mini-bus).
* `bitsOf C D`: the `BITS` tables of `bspecs` as `BitsSpec`.
* **`specQ C D`**, **`layQ C D`** (`mkLay` of `QT C D`).
-/

set_option autoImplicit false

namespace Lvm.Typed

open Lvm Lvm.Loop Lvm.Loop.Build Lvm.QAsm

/-- The input regions of the node program (QLT has none: its cells are constants of `Φ_Q`, `qltCst`). The `KS`
aliases (B1-IX): `xs` and `ys` are row-major (the program's arrays read lane `l`'s row `x` at `xsB + 17x + l`,
`ysB + 4x + l`), so they are lane-split (`inLanes`: 17 and 4 lanes of `2^9` rows, each lane its own word region,
mapped affinely onto its `C_main` run: `X_l` from row 0, `KS` lane `l` from the split); `md`'s 4 words (lane `l`'s
last trace row) one region each. -/
def inRegs (C : QCfg) : List (ℕ × ℕ × YSrc) :=
  [(0, nStream C, .sflat), (sgB C, sgB C + 2 ^ sgLog C, .sigma), (xsB C, ysB C, .ks), (ysB C, mdB C, .ks)] ++
    (List.range 4).map (fun l ↦ (mdB C + l, mdB C + l + 1, YSrc.ks)) ++
    [(pbB C, pbB C + 2 ^ 10, .pub), (obB C, nK C, .com)]

/-- The lanes of `inRegs`' regions: `xs` 17, `ys` 4, the others 1. -/
def inLanesQ : List ℕ := [1, 1, 17, 4, 1, 1, 1, 1, 1, 1]

/-- **QLT's cells as constants** (B1-Q's decision, B-DES §1.3): `qltData` (per padded entry `g^e₁, g^e₂, v`), zero
to the region's end. -/
def qltCst (C : QCfg) : List (ℕ × List FK) :=
  let vs := Lvm.QLink.qltData C.p (lay C)
  [(qtB C, vs ++ List.replicate (2 ^ C.aQT - vs.length) 0)]

/-- `qltCst` on V-PERF's `qltDataF` (B1-IX-S: `qltData` costs 3.6 s at P20, `qltDataF` 8 ms [measured]). -/
def qltCstF (C : QCfg) : List (ℕ × List FK) :=
  let vs := Lvm.VF.qltDataF C.p (lay C)
  [(qtB C, vs ++ List.replicate (2 ^ C.aQT - vs.length) 0)]

theorem qltCstF_eq (C : QCfg) : qltCstF C = qltCst C := by
  unfold qltCstF qltCst
  rw [Lvm.VF.qltDataF_eq]

/-- `l` with `g^l + 1 = k`, for `l ≤ 4`. -/
def gpowL (k : FK) : Option ℕ := [1, 2, 3, 4].find? fun l ↦ Build.gpow l + (1 : FK) == k

/-- QLT's static `readd` targets in `Q` from QLT's padded entries `pad` (`qltAlias`, `qltAliasF`). -/
def qltAliasE (C : QCfg) (Q : Program) (pad : List (ℕ × ℕ × ℕ)) : Array (Array (Option (List ℕ))) :=
  let qt := qtB C
  let ents := pad.toArray
  let qb := Q.blocks.toArray
  let stK := K.psumA (qb.map fun B ↦ B.tw .K * B.size) Q.nInK
  (Array.range qb.size).map fun b ↦
    let B := qb.getD b default
    let tp := B.tpl.toArray
    let rk := K.psumA (tp.map (Row.w .K)) 0
    tp.map fun r ↦
      match r.op with
      | .readd .. =>
        let a := r.args.getD 0 default
        let srcL : Option (ℕ × ℕ) :=
          if a.base == qt then some (0, 0) else if a.base == qt + 1 then some (1, 0) else
          -- a cell of this block's iteration: its writer
          let st := stK.getD b 0
          if a.base ≥ st && a.base < st + B.tw .K then
            match (List.range tp.size).find? fun t' ↦ rk.getD t' 0 == a.base - st && (tp.getD t' default).w .K == 1 with
            | some t' =>
              let r' := tp.getD t' default
              match r'.op with
              | .lin k _ =>
                let a' := r'.args.getD 0 default
                match gpowL k with
                | some l => if a'.base == qt then some (0, l) else if a'.base == qt + 1 then some (1, l) else none
                | none => none
              | _ => none
            | none => none
          else none
        srcL.map fun (src, l) ↦ (List.range B.size).map fun jf ↦
          let e := ents.getD jf (0, 0, 0)
          (if src == 0 then e.1 else e.2.1) + l
      | _ => none

/-- **QLT's static `readd` targets** in `Q` (blocks whose `readd` reads QLT's `α`/`β` columns), per block and
template row (a table: built once). -/
def qltAlias (C : QCfg) (Q : Program) : Array (Array (Option (List ℕ))) := qltAliasE C Q (Lvm.QLink.qltPadded C.p (lay C))

/-- `qltAlias` on `qltPaddedF` (B1-IX-S: `qltPadded` costs 3.4 s at P20 [measured]). -/
def qltAliasF (C : QCfg) (Q : Program) : Array (Array (Option (List ℕ))) :=
  qltAliasE C Q (QTyped.qltPaddedF C.p (lay C))

theorem qltAliasF_eq (C : QCfg) (Q : Program) : qltAliasF C Q = qltAlias C Q := by
  unfold qltAliasF qltAlias
  rw [QTyped.qltPaddedF_eq]

/-- An auxiliary block with its free words moved by `d`. -/
def moveAux (d : ℕ) (A : ABlk) : ABlk :=
  let mv : AOp → AOp := fun
    | .word b s => .word (b + d) s
    | a => a
  ⟨A.l, A.rows.map fun r ↦ ⟨r.ops.map fun e ↦ (e.1, mv e.2.1, e.2.2)⟩⟩

/-- **The layout specification of a node program `Q` of `C`**, reference form (the bus program `QT` or the B
program `QB`): the input regions, QLT's aliases, `BITS` as typed rows (B1-Q's `bitsAux`, 64 words per real row). -/
def specQRef (C : QCfg) (Q : Program) : LSpec :=
  let al := qltAlias C Q
  -- B1-Q's blocks per class at base `0`, built once, then moved to the solver's bases (`QTyped.bitsAux C bw`)
  let blks0 : Array (List ABlk) := ((bspecs C QTyped.noData).map fun S ↦ S.ablks 0).toArray
  ⟨inRegs C, fun b t ↦ (al.getD b #[]).getD t none, QTyped.bitsWords C,
    fun bw ↦ (List.range blks0.size).flatMap (fun k ↦ (blks0.getD k []).map (moveAux (bw k))), qltCst C,
    inLanesQ⟩

/-- **The layout specification of a node program `Q` of `C`**: `specQRef` (`specQ_eq`) with the `BITS` classes'
cell functions and QLT's entries computed on their parameters once (B1-IX-S: `bspecsF`, `qltAliasF`, `qltCstF`). -/
def specQ (C : QCfg) (Q : Program) : LSpec :=
  let al := qltAliasF C Q
  let bs := QTyped.bspecsF C QTyped.noData
  let blks0 : Array (List ABlk) := (bs.map fun S ↦ S.ablks 0).toArray
  ⟨inRegs C, fun b t ↦ (al.getD b #[]).getD t none, bs.map fun S ↦ 64 * S.n,
    fun bw ↦ (List.range blks0.size).flatMap (fun k ↦ (blks0.getD k []).map (moveAux (bw k))), qltCstF C,
    inLanesQ⟩

theorem specQ_eq (C : QCfg) (Q : Program) : specQ C Q = specQRef C Q := by
  unfold specQ specQRef
  rw [qltAliasF_eq, QTyped.bspecsF_eq, qltCstF_eq]
  rfl

end Lvm.Typed
