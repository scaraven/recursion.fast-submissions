-- New for `flock-recursive` (stage SEG-R2): prototype 1's replay templates, definitions only, below
-- `FRNodeRows4` (moved verbatim, names and namespaces kept, from `FRNodeRows4RepSegK`, `FRNodeRows4RepSeg`,
-- `FRNodeRows4RepSegT`), so that `repAllRows`, `askTG` and the plan name `rtC1d`.
import FRNodeRows4Defs
import FRVIRTplSegR
import FRVIRTplSegT

/-!
# The segment program's replay templates, definitions only

`nodeIRows4` (`FRNodeRows4`) folds the replay rows of `rtC1d` (prototype 0: `rtN0c`; prototype 1: `rtSeg1`),
and `askTG` fails at a replay op `rtC1d` does not cover (`TG.repF`). Their definitions lived in modules
above `FRNodeRows4` (SEG-R1, SEG-R1b); this module holds them, moved verbatim with their names and
namespaces, as `FRNodeRows4Defs` does for REPF's:

* from `FRNodeRows4RepSegK`: the wrapper (`KOpD`, `kdG`, `cstOf`, `kdMux`, `kdPos`, `kdAll`, `kdZero`, `kdIn`,
  `kdRows`, `rtKD`) and the dead ops' zero rows (`isEvML`, `zeroF3`, `rtEvZ`);
* from `FRNodeRows4RepSeg`: `rsWeight`'s `KOpD` (`isRSS`, `rssIn`, `rssM`, `rssLay`, `rssZf`, `kRSS`), the local
  blocks (`cbRSS`, `cbTSS`, `cbSTS`), `rtSeg1`, `rtC1d`;
* from `FRNodeRows4RepSegT`: `targetS`'s and `shiftTarget`'s (`tssIn`, `tssLay`, `kTSS`, `stArgs`, `stsIn`,
  `stsLay`, `kSTS`).

The theorems about them stay where they were.
-/

namespace FR
namespace N4s
open RecursionFast Rev4 Circ Tpl

-- from `FRNodeRows4RepSegK`

/-- **A kind-muxed op replay on canonical inputs** (one template for the three indices). -/
structure KOpD where
  cov : Op → Bool
  args : Op → Kind → List ℕ
  /-- The operand types the template serves (checked at every index). -/
  inOk : List Ty → Bool
  /-- The canonical inputs. -/
  W : ℕ
  /-- Canonical input `p`'s position in the operand encoding at types `ts` (`none`: `0`). -/
  lay : List Ty → ℕ → Option ℕ
  /-- The encoding positions forced to `0`. -/
  zf : List Ty → List ℕ
  /-- The template (inputs `I p`, `p < W`), given constants it may fold; its outputs and forcing rows. -/
  T : List (Option F) → GM (List LinT × List RowT)
  tys : List Ty

/-- Its blocks as `kBlocks` reads them. -/
def KOpD.toK (K : KOpD) : KOp := ⟨K.cov, K.args, K.inOk, fun _ _ _ => ⟨[], []⟩, K.tys⟩

/-- Canonical input `p`'s form in an operand block. -/
def kdG (K : KOpD) (b : List Ty × List Lin) (p : ℕ) : Lin :=
  match K.lay b.1 p with
  | some q => b.2.getD q []
  | none => []

/-- A form `c · Σ_κ sel_κ` (a kind-free constant, `Params.kc`): its `c`. -/
def cstOf (P : Params) (l : Lin) : Option F :=
  match l.head? with
  | some t => if l = P.kc (fun _ => t.2) then some t.2 else none
  | none => none

/-- **The mux** over the kinds `ks`, its locals from cell `c`: the sum of the locals, and the rows
`sel_ι · g_ι = m`. -/
def kdMux (P : Params) (g : Kind → Lin) : List Kind → ℕ → Lin × List Row
  | [], _ => ([], [])
  | ι :: ks, c => (((c, 1) :: (kdMux P g ks (c + 1)).1), ⟨P.sel ι, g ι, Lin.cell c⟩ :: (kdMux P g ks (c + 1)).2)

/-- **One canonical input** (the three kinds' forms `g`; mux locals from `c`): its form, its constant
hint, its rows, its mux locals. -/
def kdPos (P : Params) (g : Kind → Lin) (c : ℕ) : Lin × Option F × List Row × ℕ :=
  if g .L32 = g .P30 ∧ g .P30 = g .N30 then
    (g .L32, if zeroLin (g .L32) then some 0 else cstOf P (g .L32), [], 0)
  else ((kdMux P g kinds c).1, none, (kdMux P g kinds c).2, 3)

/-- **The canonical inputs** `p₀ … p₀ + n − 1`, mux locals from `c`: forms, hints, rows, the next
free local. -/
def kdAll (P : Params) (g : ℕ → Kind → Lin) : ℕ → ℕ → ℕ → List Lin × List (Option F) × List Row × ℕ
  | 0, _, c => ([], [], [], c)
  | n + 1, p, c =>
    ((kdPos P (g p) c).1 :: (kdAll P g n (p + 1) (c + (kdPos P (g p) c).2.2.2)).1,
     (kdPos P (g p) c).2.1 :: (kdAll P g n (p + 1) (c + (kdPos P (g p) c).2.2.2)).2.1,
     (kdPos P (g p) c).2.2.1 ++ (kdAll P g n (p + 1) (c + (kdPos P (g p) c).2.2.2)).2.2.1,
     (kdAll P g n (p + 1) (c + (kdPos P (g p) c).2.2.2)).2.2.2)

/-- The zero-forcing rows `one · f = 0` on every block's forced positions. -/
def kdZero (K : KOpD) (P : Params) (bs : List (List Ty × List Lin)) : List Row :=
  bs.flatMap fun b => (K.zf b.1).map fun q => ⟨P.one, b.2.getD q [], []⟩

/-- The canonical inputs of a block list (selector index `kIx ι` reads block `kIx ι`). -/
def kdIn (K : KOpD) (P : Params) (cb : ℕ) (bs : List (List Ty × List Lin)) :
    List Lin × List (Option F) × List Row × ℕ :=
  kdAll P (fun p ι => kdG K (bs.getD (kIx ι) ([], [])) p) K.W 0 cb

/-- **The replay rows of a `KOpD` op**: the mux's locals from `cb`, the template's after them. -/
def kdRows (K : KOpD) (B cb : ℕ) (P : Params) (cs : CS) (op : Op) (outs : List Slot) : List Row :=
  match kBlocks K.toK cs op with
  | some bs =>
    if outsOk K.tys outs && bs.all (fun b => K.inOk b.1) && ((bs.flatMap (·.2)) ++ outF outs).all (linLt B) &&
        (K.T (kdIn K P cb bs).2.1 0).2.1.length == (K.tys.map Ty.len).sum then
      (kdIn K P cb bs).2.2.1 ++ kdZero K P bs ++
        (rowsTR ⟨(K.T (kdIn K P cb bs).2.1 0).1, []⟩).map (instRow P.one (kdIn K P cb bs).1 (kdIn K P cb bs).2.2.2) ++
        (K.T (kdIn K P cb bs).2.1 0).2.2.map (instRow P.one (kdIn K P cb bs).1 (kdIn K P cb bs).2.2.2) ++
        copyRows P outs ((K.T (kdIn K P cb bs).2.1 0).2.1.map (instLin P.one (kdIn K P cb bs).1 (kdIn K P cb bs).2.2.2))
    else [rejRow P]
  | none => [rejRow P]

/-- **The replay template of a `KOpD` op.** -/
def rtKD (K : KOpD) (B cb : ℕ) : RT :=
  ⟨K.cov, fun P cs op outs => if K.cov op then kdRows K B cb P cs op outs else []⟩

/-- Whether an op is `evalM` or `evalL`. -/
def isEvML : Op → Bool
  | .evalM .. => true
  | .evalL .. => true
  | _ => false

/-- `one · out = 0` on three `F` output cells (checked below `B`); the rejecting row otherwise. -/
def zeroF3 (B : ℕ) (P : Params) (outs : List Slot) : List Row :=
  if outsOk [.f, .f, .f] outs && (outF outs).all (linLt B) then (outF outs).map fun l => ⟨P.one, l, []⟩
  else [rejRow P]

/-- **Prototype 1's `evalM`/`evalL` replay**: zero (`implSeg` pins them). -/
def rtEvZ (B : ℕ) : RT := ⟨isEvML, fun P _ op outs => if isEvML op then zeroF3 B P outs else []⟩

-- from `FRNodeRows4RepSegT`

/-- The operand types the template serves: one `AF 37`. -/
def tssIn : List Ty → Bool
  | [.af 37] => true
  | _ => false

/-- Canonical input `p < 37` is encoding entry `p`. -/
def tssLay (_ : List Ty) (p : ℕ) : Option ℕ := if p < 37 then some p else none

/-- **The segment's `targetS` replay.** -/
def kTSS : KOpD := ⟨isTS, tsArgs, tssIn, 37, tssLay, fun _ => [], tsSegT, [.af 64]⟩

/-- `shiftTarget`'s operands: `τ`, `θ`, `bnd`, `κs`. -/
def stArgs : Op → Kind → List ℕ
  | .shiftTarget t h bd ks, _ => [t, h, bd, ks]
  | _, _ => []

/-- The operand types the template serves: `[af 18, af 10, af 22, f]` (a segment's). -/
def stsIn : List Ty → Bool
  | [.af 18, .af 10, .af 22, .f] => true
  | _ => false

/-- Canonical input `p < 51` is encoding entry `p`. -/
def stsLay (_ : List Ty) (p : ℕ) : Option ℕ := if p < 51 then some p else none

/-- **The segment's `shiftTarget` replay.** -/
def kSTS : KOpD := ⟨isST, stArgs, stsIn, 51, stsLay, fun _ => [], stSegT, [.f]⟩

-- from `FRNodeRows4RepSeg`

/-- An `rsWeight` with `act` false and three claims at every index. -/
def isRSS : Op → Bool
  | .rsWeight _ ps _ _ act _ => kinds.all (fun ι => !act ι) && kinds.all fun ι => (ps ι).length == 3
  | _ => false

/-- The operand types the template serves: `[af 7, f, f, ak m ×4]`, `23 ≤ m ≤ 25`. -/
def rssIn : List Ty → Bool
  | [.af 7, .f, .f, .ak m, .ak m₁, .ak m₂, .ak m₃] =>
    decide (23 ≤ m) && decide (m ≤ 25) && m₁ == m && m₂ == m && m₃ == m
  | _ => false

/-- `ρ`'s width. -/
def rssM : List Ty → ℕ
  | _ :: _ :: _ :: .ak m :: _ => m
  | _ => 0

/-- Canonical input `p`'s encoding position (`r″`, `κ`; `ρ`; the claims' `f₀`). -/
def rssLay (ts : List Ty) (p : ℕ) : Option ℕ :=
  if p < 8 then some p
  else if p < 58 then (if (p - 8) / 2 < rssM ts then some (p + 1) else none)
  else if p < 133 then
    (if (p - 58) % 25 < rssM ts then
      some (9 + 2 * rssM ts + 2 * rssM ts * ((p - 58) / 25) + 2 * ((p - 58) % 25)) else none)
  else none

/-- The claims' `f₁` positions (forced to `0`: `F`-points). -/
def rssZf (ts : List Ty) : List ℕ :=
  (List.range 3).flatMap fun j => (List.range (rssM ts)).map fun l => 10 + 2 * rssM ts + 2 * rssM ts * j + 2 * l

/-- **The segment's `rsWeight` replay.** -/
def kRSS : KOpD := ⟨isRSS, rsArgs, rssIn, 133, rssLay, rssZf, rsSegT, [.k]⟩

/-- `rsWeight`'s locals (the mux's 207, then the template's 36,923; below `repB + 2^16`). -/
def cbRSS : ℕ := repB + 2 ^ 12

/-- `targetS`'s locals (mux, then `tsSegT`'s 55; < `2^9`) and `shiftTarget`'s (mux, then `stSegT`'s 1,301;
< `2^12 − 2^9`): both in `[repB, cbRSS)`, the block below `rsWeight`'s (R2: cell band 2). -/
def cbTSS : ℕ := repB
def cbSTS : ℕ := repB + 2 ^ 9

/-- **Prototype 1's replay templates** (SEG-R1, SEG-R1b): `linkWAll` (S-E14), `evalM`/`evalL` (zero),
`rsWeight`, `targetS`, `shiftTarget`. -/
def rtSeg1 : RT :=
  (rtLinkSegW repB).orElse ((rtEvZ repB).orElse ((rtKD kRSS repB cbRSS).orElse
    ((rtKD kTSS repB cbTSS).orElse (rtKD kSTS repB cbSTS))))

/-- **The replay templates per prototype** (`rtC1c` with prototype 1's `rtSeg1`). -/
def rtC1d (π : ℕ) : RT := if π = 0 then rtN0c else if π = 1 then rtSeg1 else RT.none

/-- Prototype 0's arm is REPF's (`rtC1c 0`), unchanged. -/
theorem rtC1d_zero : rtC1d 0 = rtC1c 0 := rfl

end N4s
end FR
