-- New for lvm2 E2F (slice S1, E2F-QH1): the tape GKR (phase CHtape) and the `KS` GKR (phase KS) verifier
-- gadgets at `E2` (twin rows), the `E2` counterparts of `tapeGadget`/`gkrGadget` (`LvmQKeccakGkr`) and of the
-- plain sumcheck gadget (`scGadget`, `LvmQSumcheck`).
import LvmE2QKLayer
import LvmVFastQ

/-!
# The Keccak GKR verifier gadgets at `E2`

* **`scGadget2 D d q claim`**: `2^D` iterations of a plain sumcheck round of `d + 1` coefficients at `E2` (`V`'s
  `sumcheckD`, mode `none`): `c₀` at lane `m`, `c₂ … c_d` at `m + 2, …`, the nonce at `m + 2d`, the challenge
  (answer lanes 0–1) at `m + 2d + 1`, `2d + 10` lanes a round (`roundLanes2`). No load rows: the challenge of
  round `i` is a pair of stream lanes (`scChal2`), the claim after round `i` the template's last twin pair
  (`scClaim2`).
* **`tapeGadgetE2 P qs inst out b`**: `V`'s `tapeGkrD (P + 5) inst out` (`LvmDecideE2`), `qs` the lane of the first
  lane challenge's answer (its nonce at `qs − 1`, lane `k` at `qs + 10k`); 24 layers from `tapeQ2 qs = qs + 49`;
  the result is the input claim's `E2` values (`TapeOutE2.cv j`, `j < 57 + P`, in `layerTB2`'s order).
* **`gkrGadgetE2 P qs inst out b`**: `V`'s `verifyKeccakD (P + 4) inst out`, `qs` the segment challenge's answer
  lane; lane `k` at `qs + 10(k + 1)`, `committed` at `qs + 59`; 12 layers (`loop [4]`, 4 dummies gated off) from
  `qs + 61`; the openings from `gkrQO2 = qs + 61 + 12·str2`: the committed open (6 rounds), the output word at
  `qO + 84`, the instance sumcheck (4 rounds) from `qO + 86`, the input open (6 rounds) from `qO + 142`, the 64
  slices at `qO + 226 + 2k`; `gkrEnd2 = qO + 354` (the row switch's samples follow).
* The callers' lanes (`callerOutLane2`, `callerQs2`) and the ground challenges' answer lanes with their grinding
  bits (`tapeChals2`, `gkrChals2`: `(lane, g)`; the PoW range rows read lane `+ 2`), for the assembly.

Every check is gated by the node flag `b`. The blocks are `VF.loopF` loops (`LvmVFastQ`: the template built in
linear time); proofs turn them into `loop` by one `rw [VF.loopF_eq]`. The algebra and the template structure are `E3`'s one for one
(`LvmQKeccakGkr`), with `E2` values (`LvmE2QKTB`, `LvmE2QKLayer`).
-/

set_option autoImplicit false

namespace Lvm.Q1

open Lvm Lvm.Loop Lvm.Loop.Build

/-! ## Operands across blocks -/

/-- A result pair of a straight block as an operand of a later block. -/
def S2.gkOut (o : LoopOut) (s : S2) : S2 := (Src.gkOut o s.1, Src.gkOut o s.2)

/-- A result pair of a straight block as cells. -/
def S2.gkCell (o : LoopOut) (s : S2) : C2 := ⟨s.1.gkCell o, s.2.gkCell o⟩

/-- Two stream lanes as an `E2` value. -/
def laneC2 (q : Nat) : C2 := ⟨kc q, kc (q + 1)⟩

/-- Template rows `t, t + 1` of a loop at iteration `jf` as an `E2` value. -/
def _root_.Lvm.Loop.Build.LoopOut.cell2 (o : LoopOut) (t jf : Nat) : C2 := ⟨o.cell t jf, o.cell (t + 1) jf⟩

/-! ## The plain sumcheck at `E2` -/

/-- Lanes per round of `d + 1` coefficients. -/
def roundLanes2 (d : Nat) : Nat := 2 * d + 10

/-- One plain round: `c₁ = claim + c₂ + … + c_d`, Horner at the challenge. -/
def scRound2 (d q : Nat) (str : List Nat) (claim : S2) : TB S2 :=
  q2Sum claim ((List.range (d - 1)).map fun k => lane2 (q + 2 * (k + 1)) str) >>= fun c1 =>
  q2Horner (lane2 (q + 2 * d + 1) str) (lane2 (q + 2 * (d - 1)) str)
    (((List.range (d - 2)).reverse.map fun k => lane2 (q + 2 * (k + 1)) str) ++ [c1, lane2 q str])

/-- The round template's length (`2(2d − 1)` rows). -/
def scLen2 (d : Nat) : Nat := 2 * (2 * d - 1)

/-- The round template, its message's first lane at `q`, the claim the previous iteration's last pair. -/
def scTpl2 (d q : Nat) : List Ins :=
  (scRound2 d q [roundLanes2 d] (.prev (scLen2 d - 2), .prev (scLen2 d - 1)) 0).2

/-- **The sumcheck gadget at `E2`**: the prologue holds the initial claim, then `2^D` rounds (those past the
sumcheck's compute values nobody reads). -/
def scGadget2 (D d q : Nat) (claim : C2) : BM LoopOut :=
  loopP [D] (tplOf (scTpl2 d q)) (fun t => if t = scLen2 d - 1 then claim.im else claim.re)

/-- Round `i`'s challenge. -/
def scChal2 (d q i : Nat) : C2 := laneC2 (q + roundLanes2 d * i + 2 * d + 1)

/-- The claim after round `i`. -/
def scClaim2 (o : LoopOut) (d i : Nat) : C2 := o.cell2 (scLen2 d - 2) i

/-! ## The first claims -/

/-- What a first-claim block exports at `E2`. -/
structure PreOut2 where
  /-- The committed scalar. -/
  com : S2
  /-- The segment challenge. -/
  seg : S2
  /-- The `eq` table of the lane challenges. -/
  lanes : List S2
  /-- The carried claim (`C` values). -/
  carried : List S2

/-- **`KS`'s first claim** at `E2` (`firstClaimSF Shape.v1`): segment at `qs`, lanes at `qs + 10(k + 1)`,
`committed` at `qs + 59`. -/
def preTB2 (P qs : Nat) (inst out : Nat → S2) (b : Src) : TB PreOut2 :=
  let seg := lane2 qs []
  let com := lane2 (qs + 59) []
  q2Base b >>= fun base =>
  let z := base.2.1
  let one := base.2.2
  q2EqTab z [one] ((List.range 5).map fun k => lane2 (qs + 10 * (k + 1)) []) >>= fun lanes =>
  q2Dot z ((List.range 25).map fun l => (lanes.getD l default, out l)) >>= fun dt =>
  q2Mul seg dt com >>= fun v0 =>
  q2EqTab z [one] ((List.range 4).map inst) >>= fun mu =>
  mapT2 (fun i => q2Scale (FK.x ^ iotaPos i) (lanes.getD 0 default)) (List.range 7) >>= fun fl =>
  pure ⟨com, seg, lanes, [v0] ++ mu ++ [one] ++ (List.range P).map (fun i => inst (4 + i)) ++ [seg] ++
    lanes.take 25 ++ List.replicate 6 z ++ fl⟩

/-- **The tape's first claim** at `E2` (`firstClaimSF Shape.tape`): lanes at `qs + 10k`. -/
def preTBT2 (P qs : Nat) (inst out : Nat → S2) (b : Src) : TB PreOut2 :=
  q2Base b >>= fun base =>
  let z := base.2.1
  let one := base.2.2
  q2EqTab z [one] ((List.range 5).map fun k => lane2 (qs + 10 * k) []) >>= fun lanes =>
  q2Dot z ((List.range 25).map fun l => (lanes.getD l default, out l)) >>= fun v0 =>
  q2EqTab z [one] ((List.range 4).map inst) >>= fun mu =>
  mapT2 (fun i => q2Scale (FK.x ^ iotaPos i) (lanes.getD 0 default)) (List.range 7) >>= fun fl =>
  pure ⟨z, z, lanes, [v0] ++ mu ++ [one] ++ (List.range (P + 1)).map (fun i => inst (4 + i)) ++
    lanes.take 25 ++ List.replicate 6 z ++ fl⟩

/-- Copy rows of carried `E2` values. -/
def cpIns2 (l : List S2) : List Ins := l.flatMap fun a => (q2Copy a 0).2

/-! ## The openings -/

/-- What the first opening block exports at `E2`. -/
structure Fin1Out2 where
  /-- The `E2` zero. -/
  z : S2
  /-- The committed word. -/
  word : S2
  /-- The `eq` table of the input open's slot point. -/
  e3 : List S2
  /-- The `eq` table of the last claim's slice challenges `a`. -/
  ea : List S2

/-- The slices' copies (128, twice the 64, `re` and `im` adjacent: the rotation loop's contiguous operand), the
`eq` tables, and the committed word's check `b·(Σ_l eq(slot, 25 + l)·(1 + seg)·lanes_l·word + value) = 0`. -/
def fin1TB2 (qO : Nat) (b : Src) (slot1 slot3 aF : List S2) (seg val1 : S2) (lanes : List S2) : TB Fin1Out2 :=
  mapT2 (fun t => kLin 0 0 (.ext ⟨.K, qO + 226 + 2 * (t / 2 % 64) + t % 2, []⟩)
    (.ext ⟨.K, qO + 226 + 2 * (t / 2 % 64) + t % 2, []⟩)) (List.range 256) >>= fun _ =>
  q2Base b >>= fun base =>
  let z := base.2.1
  let one := base.2.2
  let word := lane2 (qO + 84) []
  q2EqTab z [one] slot1 >>= fun e1 =>
  q2Dot z ((List.range 25).map fun l => (e1.getD (25 + l) default, lanes.getD l default)) >>= fun wc =>
  q2One seg >>= fun f =>
  q2Mul wc f z >>= fun w =>
  q2Mul w word val1 >>= fun t =>
  q2Assert t b >>= fun _ =>
  q2EqTab z [one] slot3 >>= fun e3 =>
  q2EqTab z [one] aF >>= fun ea =>
  pure ⟨z, word, e3, ea⟩

/-- The rotated sums at `E2`: iteration `i`, pair `w`: `Σ_{w' ≤ w} eq(a, w')·slice[w' + i]` (`sb` the first copy
cell, stride 2 per iteration). -/
def rotIns2 (ea : List S2) (sb : Nat) (z : S2) : List Ins :=
  (List.range 64).flatMap fun w =>
    mul2I (ea.getD w default) (.ext ⟨.K, sb + 2 * w, [2]⟩, .ext ⟨.K, sb + 2 * w + 1, [2]⟩)
      (if w = 0 then z else locS2 (2 * (w - 1)))

/-- `foldPairs` at `E2`, `r1 = 1 + r`. -/
def q2FoldPairs (z r1 r : S2) : List S2 → TB (List S2)
  | a :: b :: rest => q2Mul b r z >>= fun t => q2Mul a r1 t >>= fun x =>
      q2FoldPairs z r1 r rest >>= fun xs => pure (x :: xs)
  | _ => pure []

/-- `multilinearEval mle point` at `E2`. -/
def q2Mle (z : S2) : List S2 → List S2 → TB S2
  | cur, [] => pure (cur.headD z)
  | cur, r :: rs => q2One r >>= fun r1 => q2FoldPairs z r1 r cur >>= fun nxt => q2Mle z nxt rs

/-- The input check `b·(multilinearEval μ low · Σ_l W_l·laneForm B R l + value) = 0`. -/
def fin2TB2 (b : Src) (z : S2) (B : List S2) (R : Nat → S2) (e3 : List S2) (x : S2) (mu low : List S2)
    (val3 : S2) : TB Unit :=
  q2One x >>= fun x1 =>
  q2SumMap z 25 (fun l => q2LaneForm z B R l >>= fun lf => q2Mul (e3.getD l default) x1 z >>= fun u =>
    q2Mul (e3.getD (25 + l) default) x u >>= fun u' => q2Mul u' lf z) >>= fun tot =>
  q2Mle z mu low >>= fun mle =>
  q2Mul mle tot val3 >>= fun t => q2Assert t b

/-! ## The `KS` gadget -/

/-- The gadget's outputs (`V`'s `verifyKeccakD` result as cells). -/
structure GkrOutE2 where
  /-- The committed-output word claim's point. -/
  wordPoint : List C2
  /-- Its value. -/
  word : C2
  /-- The slice point. -/
  slicePoint : List C2
  /-- The slices (the stream lanes). -/
  slices : List C2

/-- The values of the outputs. -/
def GkrOutE2.vals (o : GkrOutE2) (M : Mem) : List FE2 × FE2 × List FE2 × List FE2 :=
  (o.wordPoint.map (C2.val M), o.word.val M, o.slicePoint.map (C2.val M), o.slices.map (C2.val M))

/-- The lane of the committed open's first message. -/
def gkrQO2 (P qs : Nat) : Nat := qs + 61 + 12 * (lay02 P).str2

/-- The lane after the `KS` GKR's slices. -/
def gkrEnd2 (P qs : Nat) : Nat := gkrQO2 P qs + 354

/-- The carried value `j` of the last real layer (iteration 11). -/
def lastC2 (P : Nat) (lay : LoopOut) (j : Nat) : C2 := lay.cell2 (cbOf2 P + 2 * j) 11

/-- **`V`'s `verifyKeccakD (P + 4) inst output` at `E2`**, its segment challenge's answer at lane `qs`, the
instance point and output scalars in `inst i` (`i < P + 4`), `out l` (`l < 25`), every check gated by `b`. -/
def gkrGadgetE2 (P qs : Nat) (inst out : Nat → C2) (b : Cell) : BM GkrOutE2 :=
  getPtr >>= fun p =>
  VF.loopF [] (tplOf (cstIns (gkS b))) >>= fun _ =>
  let F0 := preTB2 P qs (fun i => (inst i).s2) (fun l => (out l).s2) (gkS b) 0
  VF.loopF [] (tplOf F0.2) >>= fun pre =>
  VF.loopF [] (tplOf (cpIns2 (F0.1.carried.map (S2.gkOut pre)))) >>= fun _ =>
  VF.loopF [4] (layTpl2 P (qs + 61) p.k) >>= fun lay =>
  let qO := gkrQO2 P qs
  let lc := lastC2 P lay
  scGadget2 3 2 qO (F0.1.com.gkCell pre) >>= fun sc1 =>
  scGadget2 2 2 (qO + 86) (lc 0) >>= fun sc2 =>
  scGadget2 3 2 (qO + 142) (scClaim2 sc2 2 3) >>= fun sc3 =>
  let ch1 := (List.range 6).map fun i => scChal2 2 qO i
  let ch2 := (List.range 4).map fun i => scChal2 2 (qO + 86) i
  let ch3 := (List.range 6).map fun i => scChal2 2 (qO + 142) i
  let G := fin1TB2 qO (gkS b) (ch1.map C2.s2) (ch3.map C2.s2) ((List.range 6).map fun i => (lc (44 + P + i)).s2)
    (F0.1.seg.gkOut pre) (scClaim2 sc1 2 5).s2 (F0.1.lanes.map (S2.gkOut pre)) 0
  VF.loopF [] (tplOf G.2) >>= fun f1 =>
  VF.loopF [6] (tplOf (rotIns2 (G.1.ea.map (S2.gkOut f1)) f1.p.k (G.1.z.gkOut f1))) >>= fun rot =>
  VF.loopF [] (tplOf (fin2TB2 (gkS b) (G.1.z.gkOut f1)
    ((List.range 25).map fun l => (lc (19 + P + l)).s2)
    (fun s => (rot.cell2 126 ((64 - s) % 64)).s2) (G.1.e3.map (S2.gkOut f1))
    (lc (18 + P)).s2 ((List.range 16).map fun i => (lc (1 + i)).s2)
    (ch2.map C2.s2) (scClaim2 sc3 2 5).s2 0).2) >>= fun _ =>
  pure ⟨(List.range (P + 4)).map inst ++ ch1, laneC2 (qO + 84),
    ch2 ++ (List.range P).map (fun i => lc (18 + i)) ++ ch3,
    (List.range 64).map fun k => laneC2 (qO + 226 + 2 * k)⟩

/-! ## The tape gadget -/

/-- The lane of the tape's first layer's first product scalar. -/
def tapeQ2 (qs : Nat) : Nat := qs + 49

/-- The lane after the tape (the wiring phase's first message). -/
def tapeEnd2 (P qs : Nat) : Nat := tapeQ2 qs + tapeDepth * (lay02 P).str2

/-- The tape's result at `E2`: the input claim's carried values (`value, μ[16], κ, point[P+1], B[25], a[6],
flip[7]`), value `j` of the claim. -/
structure TapeOutE2 where
  /-- The carried values of the last layer. -/
  cv : Nat → C2

/-- **`V`'s `tapeGkrD (P + 5) inst output` at `E2`**, its first lane challenge's answer at lane `qs`, the instance
point in `inst i` (`i < P + 5`), the 25 output scalars in `out l`, every check gated by `b`. -/
def tapeGadgetE2 (P qs : Nat) (inst out : Nat → C2) (b : Cell) : BM TapeOutE2 :=
  getPtr >>= fun p =>
  VF.loopF [] (tplOf (cstInsT (gkS b))) >>= fun _ =>
  let F0 := preTBT2 P qs (fun i => (inst i).s2) (fun l => (out l).s2) (gkS b) 0
  VF.loopF [] (tplOf F0.2) >>= fun pre =>
  VF.loopF [] (tplOf (cpIns2 (F0.1.carried.map (S2.gkOut pre)))) >>= fun _ =>
  VF.loopF [4] (layTpl2 P (tapeQ2 qs) p.k) >>= fun _ =>
  VF.loopF [3] (layTpl2 P (tapeQ2 qs + 16 * (lay02 P).str2) (p.k + 16 * 16)) >>= fun lay =>
  pure ⟨fun j => lay.cell2 (cbOf2 P + 2 * j) 7⟩

/-! ## Lanes for the assembly -/

/-- A caller's output scalar `l` (after its last instance challenge's answer at lane `a`). -/
def callerOutLane2 (a l : Nat) : Nat := a + 9 + 2 * l

/-- The first challenge after a caller's 25 outputs (its last instance challenge's answer at lane `a`): the tape's
`qs`, `KS`'s `qs`. -/
def callerQs2 (a : Nat) : Nat := a + 60

/-- The ground challenges of one layer from `q` (answer lane, grinding bits): `s` (`c = 46`), the pack rounds and the
position rounds (`c = 3`), `β` (`c = 2`). -/
def layerChals2 (P q : Nat) : List (Nat × Nat) :=
  [(q + 104, 6)] ++ (List.range (P + 1)).map (fun i => (q + 113 + 14 * i + 5, 2)) ++
    (List.range 11).map (fun i => (q + 113 + 14 * (P + 1) + 16 * i + 7, 2)) ++ [(q + 289 + 14 * (P + 1) + 7, 2)]

/-- **The tape's ground challenges** (answer lane, `g`): the five lane coordinates (`c = 1`), the 24 layers. -/
def tapeChals2 (P qs : Nat) : List (Nat × Nat) :=
  (List.range 5).map (fun k => (qs + 10 * k, 1)) ++
    (List.range tapeDepth).flatMap fun L => layerChals2 P (tapeQ2 qs + L * (lay02 P).str2)

/-- **`KS`'s ground challenges** (answer lane, `g`): the segment and lane coordinates (`c = 1`), the 12 layers, the
three opening sumchecks (`c = 2`). -/
def gkrChals2 (P qs : Nat) : List (Nat × Nat) :=
  (List.range 6).map (fun k => (qs + 10 * k, 1)) ++
    (List.range 12).flatMap (fun L => layerChals2 P (qs + 61 + L * (lay02 P).str2)) ++
    (List.range 6).map (fun i => (gkrQO2 P qs + 14 * i + 5, 2)) ++
    (List.range 4).map (fun i => (gkrQO2 P qs + 86 + 14 * i + 5, 2)) ++
    (List.range 6).map (fun i => (gkrQO2 P qs + 142 + 14 * i + 5, 2))

end Lvm.Q1
