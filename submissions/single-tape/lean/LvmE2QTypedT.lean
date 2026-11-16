-- New for lvm2 S2GT (GT-C): the typed phases' verifier in the node program at stage S2GT (the typed backend at `E2`,
-- the frozen S2GT transcript with amendments 1–2), the circuit twin of `LvmE2TV.dTypedT` (V_S), read for read.
import LvmE2QTypedX
import LvmE2QWKit
import LvmE2QPlan
import LvmE2QPinOpen

/-!
# The typed phases at S2GT (`typedGT`)

Every `E2` value is a `C2` (two `K` cells, `LvmE2QGad`); an `E2` scalar of the transcript is `ld2` of its two lanes,
an `E2` challenge `ld2` of its answer's lanes 0–1 (its proof-of-work lane 2 is checked by the PoW rows, `typedPowT`).
Lanes come from the schedule (`L j`: the lane of item `j` of the phase `bus`), not from fixed strides.

* `zeroGT`: `τ` (20), `ω`, 20 equality-mode rounds (`roundPolyD 3 claim (some τ)`), the nine values, the check
  `final = Σ_k ω^k·(mulY3_k(A, B) + C_k)` (`zeroFinalD`);
* `wireGT`: `γ`, the nine values' Horner sum, 21 plain rounds, the twelve matrix values and four region values, the
  check `final = wGD(γ, vs)·(Σ rv + virt(r_y))` (`virtGT`: `PUB`'s lanes' extension and the word `1`, at `E2`);
* `relayGT`: 19 plain rounds from `rv₁`, `v_R`, the check `final = kern(r_y, r)·v_R` (`relayKernGT`, the division
  automaton at `E2`);
* `qaccGT`: A23 at `Φ_Q` in 45 variables (`κ` 4, `h` 46, `t`, the zero scalar); the folded accumulator on the current
  proof's `PUB` lanes `615 + 2j` (`E2`, two lanes a scalar);
* the mini-bus: roll 11's `miniG` (`E3`, S2GT amendment 1) from its first item;
* `typedClaimsGT`: the typed claims as the opening's `E2` halves (`typedClaimsND`'s order), the mini-bus's table
  claims as `E3` claims.
-/

set_option autoImplicit false

namespace Lvm.E2Q

open Lvm Lvm.Loop Lvm.Loop.Build Lvm.Har Lvm.QTyped Lvm.Q2

/-! ## Item indices of the phase `bus` at S2GT (`LvmE2TV.dTypedT`'s reads, `ref/s2gt.py`) -/

/-- `τ_i`'s answer item (after the separator; each `τ` its nonce first). -/
def iTau (i : Nat) : Nat := 2 + 2 * i
/-- `ω`'s answer item. -/
def iOm : Nat := iTau tX
/-- Zerocheck round `k`'s message, then its nonce, then its challenge. -/
def iZR (k : Nat) : Nat := iOm + 1 + 3 * k
/-- The nine values at `r_x`. -/
def iZV : Nat := iZR tX
/-- `γ`'s answer item. -/
def iGam : Nat := iZV + 2
/-- Wiring round `k`'s message. -/
def iWR (k : Nat) : Nat := iGam + 1 + 3 * k
/-- The twelve matrix values, then the four region values. -/
def iWV : Nat := iWR tY
/-- Relayout round `k`'s message. -/
def iRR (k : Nat) : Nat := iWV + 2 + 3 * k
/-- `v_R`. -/
def iRV : Nat := iRR tR
/-- `κ_j`'s answer item. -/
def iKap (j : Nat) : Nat := iRV + 2 + 2 * j
/-- `h` (46 scalars). -/
def iH : Nat := iKap 4 - 1
/-- `t`'s answer item. -/
def iT : Nat := iH + 2
/-- The zero scalar. -/
def iZ : Nat := iT + 1
/-- The mini-bus's first item. -/
def iMB : Nat := iZ + 1

/-! ## Small `E2` gadgets -/

/-- `acc + e·x` for an `E2` value `e` and a `K` cell `x` (two `K` rows). -/
def g2MacK (acc e : C2) (x : Cell) : BM C2 :=
  mulAdd .K e.re x acc.re >>= fun r => mulAdd .K e.im x acc.im >>= fun i => pure ⟨r, i⟩

/-- `acc + Σ e_i·x_i` (`E2` by `K`). -/
def g2DotK : C2 → List (C2 × Cell) → BM C2
  | acc, [] => pure acc
  | acc, (e, x) :: r => g2MacK acc e x >>= fun acc' => g2DotK acc' r

/-- `eq(r, b) = Π_i (b_i ? r_i : 1 + r_i)` at `E2` (first on the lowest bit; `o2` for no coordinate). -/
def eqConst2 (z2 o2 : C2) : List C2 → Nat → BM C2
  | [], _ => pure o2
  | r :: rs, b =>
    eqConst2 z2 o2 rs (b / 2) >>= fun t =>
    if b % 2 = 1 then g2Mul t r z2 else g2One r >>= fun u => g2Mul t u z2

/-- `Σ_k eq(r, k)·x_k` for `K` cells `x_k`, the point `r` split at `la` (`eqDot`'s blocks at `E2`). -/
def eqDot2K (z2 o2 : C2) (r : List C2) (la : Nat) (xs : List Cell) : BM C2 :=
  g2EqTab z2 [o2] (r.take la) >>= fun eL =>
  g2EqTab z2 [o2] (r.drop la) >>= fun eH =>
  let nb := (xs.length + 2 ^ la - 1) / 2 ^ la
  mapB (fun h => g2DotK z2 ((List.range (2 ^ la)).filterMap fun l =>
      (xs[h * 2 ^ la + l]?).map fun x => (eL.getD l default, x))) (List.range nb) >>= fun accs =>
  g2Dot z2 ((List.range nb).map fun h => (eH.getD h default, accs.getD h default))

/-- `Σ_k eq(r, k)·e_k` for `E2` values `e_k` (split at `la`). -/
def eqDot2 (z2 o2 : C2) (r : List C2) (la : Nat) (es : List C2) : BM C2 :=
  g2EqTab z2 [o2] (r.take la) >>= fun eL =>
  g2EqTab z2 [o2] (r.drop la) >>= fun eH =>
  let nb := (es.length + 2 ^ la - 1) / 2 ^ la
  mapB (fun h => g2Dot z2 ((List.range (2 ^ la)).filterMap fun l =>
      (es[h * 2 ^ la + l]?).map fun e => (eL.getD l default, e))) (List.range nb) >>= fun accs =>
  g2Dot z2 ((List.range nb).map fun h => (eH.getD h default, accs.getD h default))

/-- Horner's rule from `acc`: `acc ← γ·acc + x` for `x` in order. -/
def horner2 (γ : C2) : List C2 → C2 → BM C2
  | [], acc => pure acc
  | x :: xs, acc => g2Mul γ acc x >>= fun acc' => horner2 γ xs acc'

/-- `Σ_k γ^k·d_k` (Horner from the top). -/
def powSum2 (z2 γ : C2) (ds : List C2) : BM C2 := horner2 γ ds.reverse z2

/-- `a = b` on both coordinates (gated by `g`). -/
def assertEq2 (a b : C2) (g : Cell) : BM Unit := assertEq a.re b.re g >>= fun _ => assertEq a.im b.im g

/-! ## The zerocheck -/

/-- One equality-mode round (`roundPolyD 3 claim (some τ)`, then `sampleG`): the message's tail `c₁, c₂` at lanes
`qm, qm + 2`, the challenge `r` at the answer lane `qa`; the next claim `polyEvalF [claim + τ(c₁ + c₂), c₁, c₂] r`. -/
def eqRound2 (z2 τ : C2) (qm qa : Nat) (claim : C2) : BM (C2 × C2) :=
  let c1 := ld2 qm
  let c2 := ld2 (qm + 2)
  let r := ld2 qa
  g2Add c1 c2 >>= fun s => g2Mul τ s claim >>= fun c0 =>
  g2Mul c2 r c1 >>= fun t => g2Mul t r c0 >>= fun nc => pure (r, nc)

/-- One plain round (`roundPolyD 3 claim none`, then `sampleG`): `c₀, c₂` at lanes `qm, qm + 2`; the next claim
`polyEvalF [c₀, claim + c₂, c₂] r`. -/
def plainRound2 (qm qa : Nat) (claim : C2) : BM (C2 × C2) :=
  let c0 := ld2 qm
  let c2 := ld2 (qm + 2)
  let r := ld2 qa
  g2Add claim c2 >>= fun c1 => g2Mul c2 r c1 >>= fun t => g2Mul t r c0 >>= fun nc => pure (r, nc)

/-- `R` plain rounds, round `k`'s message at item `i0 + 3k` (its challenge at `i0 + 3k + 2`). -/
def plainRuns2 (L : Nat → Nat) : Nat → Nat → C2 → BM (List C2 × C2)
  | 0, _, claim => pure ([], claim)
  | R + 1, i0, claim => plainRound2 (L i0) (L (i0 + 2)) claim >>= fun rc =>
    plainRuns2 L R (i0 + 3) rc.2 >>= fun res => pure (rc.1 :: res.1, res.2)

/-- The equality-mode rounds `τ_k`, round `k`'s message at item `i0 + 3k`. -/
def eqRuns2 (z2 : C2) (L : Nat → Nat) : List C2 → Nat → C2 → BM (List C2 × C2)
  | [], _, claim => pure ([], claim)
  | τ :: τs, i0, claim => eqRound2 z2 τ (L i0) (L (i0 + 2)) claim >>= fun rc =>
    eqRuns2 z2 L τs (i0 + 3) rc.2 >>= fun res => pure (rc.1 :: res.1, res.2)

/-- `E2` scalars `j < n` of the read at lane `q` (16 B each). -/
def ld2s (q n : Nat) : List C2 := (List.range n).map fun j => ld2 (q + 2 * j)

/-- **The zerocheck at `E2`** (`dZeroT`) on the items `L` of the phase `bus`: `r_x` and the nine values. -/
def zeroGT (z2 : C2) (g : Cell) (L : Nat → Nat) : BM (List C2 × List C2) := do
  let tau := (List.range tX).map fun i => ld2 (L (iTau i))
  let om := ld2 (L iOm)
  let rf ← eqRuns2 z2 L tau (iZR 0) z2
  let v := ld2s (L iZV) 9
  let a (j : Nat) : C2 := v.getD j z2
  let b (j : Nat) : C2 := v.getD (3 + j) z2
  let c (j : Nat) : C2 := v.getD (6 + j) z2
  -- u = a₁b₂ + a₂b₁, w = a₂b₂
  let u0 ← g2Mul (a 2) (b 1) z2
  let u ← g2Mul (a 1) (b 2) u0
  let w ← g2Mul (a 2) (b 2) z2
  -- rel₀ = a₀b₀ + u + C₀
  let s0 ← g2Add u (c 0)
  let r0 ← g2Mul (a 0) (b 0) s0
  -- rel₁ = a₀b₁ + a₁b₀ + u + w + C₁
  let s1 ← g2Add u w
  let s1 ← g2Add s1 (c 1)
  let s1 ← g2Mul (a 1) (b 0) s1
  let r1 ← g2Mul (a 0) (b 1) s1
  -- rel₂ = a₀b₂ + a₁b₁ + a₂b₀ + w + C₂
  let s2 ← g2Add w (c 2)
  let s2 ← g2Mul (a 2) (b 0) s2
  let s2 ← g2Mul (a 1) (b 1) s2
  let r2 ← g2Mul (a 0) (b 2) s2
  -- rel₀ + ω(rel₁ + ω·rel₂)
  let t1 ← g2Mul om r2 r1
  let t ← g2Mul om t1 r0
  assertEq2 rf.2 t g
  pure (rf.1, v)

/-! ## The wiring and the virtual regions at `E2` -/

/-- A region's selector at `r_y` (its high coordinates), at `E2`. -/
def regSel2 (z2 o2 : C2) (ry : List C2) (R : TReg) : BM C2 := eqConst2 z2 o2 (ry.drop R.log) (R.base >>> R.log)

/-- `Σ_k eq(r, k)·c_k` for constants `c_k` at `E2` (`dotConstG`'s): an `eq` table, one product by a constant each. -/
def dotConst2 (z2 o2 : C2) (r : List C2) (cs : List FK) : BM C2 :=
  g2EqTab z2 [o2] r >>= fun eb =>
  (cs.zipIdx.filter fun x => x.1 ≠ 0).foldl (fun (m : BM C2) x => m >>= fun acc =>
    g2Lin x.1 0 acc (eb.getD x.2 default)) (pure z2)

/-- **The natively computed part of `z̃(r_y)` at `E2`** (`virtD`): `PUB` (the child's `n` header lanes from stream
lane `11`, the key from the cells `pb + 1 …`), the word `1`, and with `qltVirt` the `QLT` region. -/
def virtGT (z2 o2 : C2) (T : TData) (pb n : Nat) (ry : List C2) : BM C2 := do
  let sP ← regSel2 z2 o2 ry ⟨T.pub, 10, 0⟩
  let vP ← eqDot2K z2 o2 (ry.take 10) 5 ((List.range n).map (Lvm.QAcc.pubLaneC 11 (pb + 1)))
  let w ← g2Mul sP vP z2
  let e1 ← eqConst2 z2 o2 ry T.one
  let w ← g2Add w e1
  match T.qlt with
  | none => pure w
  | some (b, l, cs) => do
    let sQ ← regSel2 z2 o2 ry ⟨b, l, 0⟩
    let vQ ← dotConst2 z2 o2 (ry.take l) cs
    g2Mul sQ vQ w

/-- **The wiring at `E2`** (`dWiringT`) after the zerocheck: `r_y`, the twelve matrix values, the four region
values. -/
def wireGT (z2 o2 : C2) (g : Cell) (T : TData) (pb n : Nat) (L : Nat → Nat) (v : List C2) :
    BM (List C2 × List C2 × List C2) := do
  let γ := ld2 (L iGam)
  let c0 ← powSum2 z2 γ (v.take 9)
  let rf ← plainRuns2 L tY (iWR 0) c0
  let vs := ld2s (L iWV) 12
  let rv := ld2s (L (iWV + 1)) 4
  -- wGD: Σ_{j<3} γ^j vs₄ⱼ + γ^(3+j) vs₁₊₄ⱼ + γ^(6+j) (vs₂₊₄ⱼ + vs₃₊₄ⱼ)
  let d6 ← mapB (fun j => g2Add (vs.getD (2 + 4 * j) z2) (vs.getD (3 + 4 * j) z2)) (List.range 3)
  let ds := (List.range 3).map (fun j => vs.getD (4 * j) z2) ++ (List.range 3).map (fun j => vs.getD (1 + 4 * j) z2) ++ d6
  let m ← powSum2 z2 γ ds
  let ve ← virtGT z2 o2 T pb n rf.1
  let s ← g2Sum ve rv
  let pr ← g2Mul m s z2
  assertEq2 rf.2 pr g
  pure (rf.1, vs, rv)

/-! ## The relayout at `E2` (the division automaton, `relayKernG` at `E2`) -/

/-- One step of the division by 17 at `E2` (`divStep`'s). -/
def divStep2 (z2 : C2) (ρi : C2) (ri : Option C2) (W : List (Option C2)) : BM (List (Option C2)) := do
  let nρ ← g2One ρi
  let c ← match ri with
    | none => pure [(0, 0, nρ), (1, 0, ρi)]
    | some r => do
      let nr ← g2One r
      let c00 ← g2Mul nρ nr z2
      let c10 ← g2Mul ρi nr z2
      let c01 ← g2Mul nρ r z2
      let c11 ← g2Mul ρi r z2
      pure [(0, 0, c00), (1, 0, c10), (0, 1, c01), (1, 1, c11)]
  let ins (r' : Nat) : List (C2 × C2) :=
    (List.range 17).flatMap fun rem => match W.getD rem none with
      | none => []
      | some w => c.filterMap fun x =>
        let v := 2 * rem + x.1
        let qb := if 17 ≤ v then 1 else 0
        if qb = x.2.1 ∧ v - 17 * qb = r' then some (w, x.2.2) else none
  mapB (fun r' => match ins r' with
    | [] => pure none
    | l => g2Dot z2 l >>= fun s => pure (some s)) (List.range 17)

/-- The automaton's run over `p`-bits `n − 1 … 0`. -/
def divRun2 (z2 : C2) (ρ r : List C2) : Nat → List (Option C2) → BM (List (Option C2))
  | 0, W => pure W
  | n + 1, W => divStep2 z2 (ρ.getD n z2) (if n < 14 then some (r.getD n z2) else none) W >>= fun W' =>
    divRun2 z2 ρ r n W'

/-- The identity part at `E2` (`tailG`'s). -/
def tailG2 (z2 o2 : C2) (ρ r : List C2) : BM C2 := do
  let ts ← mapB (fun i => do
    let a := ρ.getD i z2
    let b := r.getD i z2
    let na ← g2One a
    let nb ← g2One b
    let d0 ← g2Mul na nb z2
    let d1 ← g2Mul a b z2
    let t ← g2Add d0 d1
    pure (d0, d1, t)) (List.range 19)
  let pT ← g2Prod z2 o2 ((ts.take 14).map (·.2.2))
  let pM ← g2Prod z2 o2 (((ts.drop 14).take 4).map (·.2.2))
  let pZ ← g2Prod z2 o2 (((ts.drop 14).take 4).map (·.1))
  let df ← g2Add pM pZ
  let h ← g2Mul pT (ts.getD 18 (z2, z2, z2)).2.1 z2
  g2Mul h df z2

/-- **The relayout's kernel at `E2`** (`relayKernG`'s). -/
def relayKernGT (z2 o2 : C2) (T : TData) (ry r : List C2) : BM C2 := do
  let sel ← regSel2 z2 o2 ry ⟨T.sflat, 19, 0⟩
  let ρ := ry.take 19
  let W ← divRun2 z2 ρ r 19 ((List.range 17).map fun i => if i = 0 then some o2 else none)
  let a ← eqDot2 z2 o2 ((List.range 5).map fun i => r.getD (14 + i) z2) 2 (W.map fun w => w.getD z2)
  let b ← tailG2 z2 o2 ρ r
  let s ← g2Add a b
  g2Mul sel s z2

/-- **The relayout at `E2`** (`dRelayT2`): 19 plain rounds from `v_S`, `v_R`, the check. -/
def relayGT (z2 o2 : C2) (g : Cell) (T : TData) (L : Nat → Nat) (ry : List C2) (vS : C2) : BM (List C2 × C2) := do
  let rf ← plainRuns2 L tR (iRR 0) vS
  let vR := ld2 (L iRV)
  let k ← relayKernGT z2 o2 T ry rf.1
  let pr ← g2Mul k vR z2
  assertEq2 rf.2 pr g
  pure (rf.1, vR)

/-! ## A23 at `E2` -/

/-- `Φ_Q`'s variables at S2GT (`4 + 20 + 21`). -/
abbrev tVarsT : Nat := 4 + tX + tY

/-- The child's `acc_in` scalar `j` at S2GT (stream lanes from `11 + 615`, two lanes a scalar). -/
def accLaneT (j : Nat) : Nat := 626 + 2 * j

/-- **A23 at `Φ_Q` in 45 variables at `E2`** (`dAccT`): `κ` (4), `h` (46), `t`, the zero scalar;
`h(0) = acc_in.y`, `h(1) = Σ_{o'} eq(κ, o')·vs_{o'}`, the zero scalar `0`; the folded accumulator (the line from
`acc_in.pt` to `κ ‖ r_x ‖ r_y` at `t`, and `h(t)`) equal to the current proof's `PUB` lanes `615 + 2j`. -/
def qaccGT (z2 o2 : C2) (pb : Nat) (L : Nat → Nat) (rx ry vs : List C2) : BM Unit := do
  let g := kc pb
  let kap := (List.range 4).map fun j => ld2 (L (iKap j))
  let h := ld2s (L iH) (tVarsT + 1)
  let t := ld2 (L iT)
  let zz := ld2 (L iZ)
  let ain := (List.range (tVarsT + 1)).map fun j => ld2 (accLaneT j)
  -- h(0) = h₀ = acc_in.y
  assertEq2 (h.getD 0 z2) (ain.getD tVarsT z2) g
  -- h(1) = Σ h_j = Σ eq(κ, o')·vs_{o'}
  let sh ← g2Sum z2 h
  let y ← eqDot2 z2 o2 kap 2 vs
  assertEq2 sh y g
  -- the zero scalar
  assertEq2 zz z2 g
  -- the line from acc_in.pt to κ ‖ r_x ‖ r_y at t, and h(t), on PUB lanes 615 + 2j
  let bc := kap ++ rx ++ ry
  let pts ← mapB (fun i => do
    let x := ain.getD i z2
    let d ← g2Add x (bc.getD i z2)
    g2Mul t d x) (List.range tVarsT)
  let hv ← horner2 t h.reverse z2
  let pc := (List.range (tVarsT + 1)).map fun j => ld2 (pb + 615 + 2 * j)
  let _ ← mapB (fun i => assertEq2 (pts.getD i z2) (pc.getD i z2) g) (List.range tVarsT)
  assertEq2 hv (pc.getD tVarsT z2) g

/-! ## The whole gadget and its claims -/

/-- What the typed phases hand on at S2GT. -/
structure TypedCT where
  rx : List C2
  ry : List C2
  abc : List C2
  vs : List C2
  rv : List C2
  rr : List C2
  vR : C2
  bus : BusC
  tab : List (List Cell × List Cell)

/-- The lane function of the phase `bus` at `p`. -/
def busL (p : Params) : Nat → Nat :=
  let A := (itemLanes p).toArray
  let i0 := phaseItem0 p .bus
  fun j => A.getD (i0 + j) 0

/-- The mini-bus's start position at `p` (its first item's value at `+ 40`). -/
def mbPT (p : Params) : Nat := 8 * busL p iMB - 40

/-- **The typed backend's verifier at S2GT** at `p` (lanes `busL p`), the current proof's `PUB` at cell `pb`,
`z`/`o` the `E` constants, `zk`/`ok` the `K` zero and one, `n` the child's `PUB` lanes. -/
def typedGT (T : TData) (p : Params) (pb n : Nat) (z o zk ok : Cell) : BM TypedCT := do
  let g := kc pb
  let L := busL p
  let z2 : C2 := ⟨zk, zk⟩
  let o2 : C2 := ⟨ok, zk⟩
  let zr ← zeroGT z2 g L
  let w ← wireGT z2 o2 g T pb n L zr.2
  let r ← relayGT z2 o2 g T L w.1 (w.2.2.getD 1 z2)
  qaccGT z2 o2 pb L zr.1 w.1 w.2.1
  let mb ← miniG z o g T (mbPT p)
  pure ⟨zr.1, w.1, zr.2, w.2.1, w.2.2, r.1, r.2, mb.1, mb.2⟩

/-- **The typed phases' end at S2GT** (after the mini-bus's table phase). -/
def typedEndT (T : TData) (p : Params) : Nat := tabEnd T.mbS T.mbR (busEndD T.mbD (mbPT p))

/-- A region family's claim at `E2` as the opening's parts: per region `(eq(r_y^{≥ log}, base >> log), ⟨log, off⟩,
r_y^{< log})`. -/
def regParts2 (z2 o2 : C2) (rs : List TReg) (ry : List C2) : BM (List (C2 × Placement × List C2)) :=
  mapB (fun R => regSel2 z2 o2 ry R >>= fun s => pure (s, (⟨R.log, R.off⟩ : Placement), ry.take R.log)) rs

/-- The two halves (re, then im) of an `E2` claim. -/
def halves2 (parts : List (C2 × Placement × List C2)) (v : C2) : List FClaim :=
  [.half false parts v.re, .half true parts v.im]

/-- **The typed phases' claims at S2GT** (`typedClaimsND`'s order: the relayout's point claim on the stream block,
`σ′`'s, the committed block's, the `KS` aliases', each split re then im), then the mini-bus's table claims (`E3`). -/
def typedClaimsGT (z : Cell) (z2 o2 : C2) (T : TData) (sOff : Nat) (t : TypedCT) : BM (List FClaim) := do
  let pS ← regParts2 z2 o2 T.sig t.ry
  let pC ← regParts2 z2 o2 T.com t.ry
  let pK ← regParts2 z2 o2 T.ks t.ry
  pure (halves2 [(o2, ⟨tR, sOff⟩, t.rr)] t.vR ++ halves2 pS (t.rv.getD 2 z2) ++ halves2 pC (t.rv.getD 0 z2) ++
    halves2 pK (t.rv.getD 3 z2) ++ (tabClaims T.mbS t.tab z).map .e3)

end Lvm.E2Q
