-- New for lvm6 (WP NODE3, item 7). The deployed node circuit's definition in Lean: the cell bases, `Q_link`'s
-- and `Q_sig`'s layouts, CC's generator at `P18` (`ccG18`, with LAY5's aligned position-bit blocks `bOf`) and the
-- five families in program order (`famQ6`). Until now these lived only in LAY's exporter (`exportN.tpl`).
import Lvm6NodeQ
import Lvm6QLinkP18
import Lvm6QDSig
import Lvm6QSig
import Lvm6QCFinM
import Lvm6KSParams
import Lvm6QCRing6
import Lvm6NodeLanes
import LvmVFastQ
import Lvm6NodeMbT
import Lvm6NodeMbC
import Lvm6QltF

/-!
# The deployed node circuit (`famQ6`, WP NODE3)

The text is the exporter's (`/home/devops/scratch-lvm6/LAY5/probe/exportN.tpl`, LAY5, the blob `q6-lay5.blob`),
with the tracing (`CT`, instance marks, classes) left out: the exporter should import this module instead of
carrying its own copy, so the program it exports is `toProgramF nK 0 (famQ6 lay)`.

* **`bOf B j = B + [0, 4096, 5120, 6144, 6656][j]`** (LAY5, W3 lever 1): level `j`'s position-bit block inside
  `ccbC`'s `2^13` cells. It was an exporter-side constant only; here it is the argument `posGen (bOf B j)` of the
  circuit's definition (`levCall`, `ccG18I`), so the circuit and the blob fix the same values. `bOf_blocks`: the
  five blocks (`128·(kq+1)` cells each) are disjoint and inside the region.
* **CC's inputs** (NODE3 phase 2): `famQ6` runs CC on `node6E`'s output cells (`ccG18o`, `inpReal`, `ccPre`;
  ORD's order); the stream lanes (`z₀`, `y₀`, ring and level lanes) are derived from `sched6 P18` (`lanes18`). The
  mini-bus claims' parts and values are `mbPre`'s cells on the deployed tables `mbTD lay` (MBT phase 2: `mbTL
  mbPar6` on `progR lay`, the families before CC, so the circuit does not read its own program). `ccG18` (LAY3's representative
  `mkInp`) is kept for comparison only.
-/

set_option autoImplicit false

namespace Lvm6.Node.Dep

section Consts

open Lvm.Typed

def sbC : ℕ := 0
def pbC : ℕ := 2 ^ 19
def sgC : ℕ := 2 ^ 19 + 2 ^ 11
def ksC : ℕ := 2 ^ 20
def xsC : ℕ := ksC
def ysC : ℕ := ksC + 2 ^ 15
def mdC : ℕ := ksC + 2 ^ 15 + 2 ^ 13
def zC : ℕ := 2 ^ 20 + 2 ^ 18
def X0 : ℕ := 2 ^ 20 + 2 ^ 18 + 2 ^ 16
def qtC : ℕ := X0
def bbC : ℕ := X0 + 2 ^ 13
def obC : ℕ := X0 + 2 * 2 ^ 13
def olC : ℕ := X0 + 3 * 2 ^ 13
def dstC : ℕ := X0 + 4 * 2 ^ 13
def hdC : ℕ := X0 + 4 * 2 ^ 13 + 2 ^ 11
/-- CC's `posGen` bit cells (`128` per draw, levels 0–4: `128·38` cells), its own committed region. -/
def ccbC : ℕ := X0 + 5 * 2 ^ 13
def nK : ℕ := X0 + 6 * 2 ^ 13

/-! ### The `KS` alias parameters (WP KSA, RV4 B2; `Lvm6KSParams`, guarded by `Lvm6NodeKS.ksAliasB`) -/

/-- **The deployed `C_main` targets** (PFW `KSTgt`): `Y` at slot 36 (`2^13` words a lane), `X` at slot 37 (`2^10`
a lane); `ys` from row 7168, `ysl` from row 7680, `md` at row 4001 (`B − 1`). -/
def ksT18 : Lvm6.KSP.KSTgt := ⟨36 * 2 ^ 19, 37 * 2 ^ 19, 2 ^ 13, 2 ^ 10, 7168, 7680, 4001⟩
/-- **The deployed alias cells**: `xs` 17 lanes × 912 rows (`2^10` a lane), `ys` 4 × 449 (`2^10`), `ysl` 4 × 400
(`2^9`, from `ysC + 4·2^10`), `md` 4 single words. -/
def ksC18 : Lvm6.KSP.KSCells := ⟨xsC, ysC, ysC + 4 * 2 ^ 10, mdC, 17, 912, 10, 4, 449, 10, 400, 9⟩
def ksXs : Lvm6.KSP.KSFam := ksT18.xFam ksC18
def ksYs : Lvm6.KSP.KSFam := ksT18.yFam ksC18
def ksYsl : Lvm6.KSP.KSFam := ksT18.ylFam ksC18
def ksMd : Lvm6.KSP.KSFam := ksT18.mdFam ksC18
/-- **The deployed `KS` alias parameters.** -/
def ksP18 : Lvm6.KSP.KSParams := ksT18.params ksC18

/-- **The instance meets the interface** (lanes, rows, aligned targets, disjoint windows). -/
theorem ksP18_ok : ksP18.Ok := by decide

/-- **The deployed `KS` word map.** -/
def ksWOf (lay : Lay) : ℕ → ℕ := Lvm6.KSP.ksWOf ksP18 lay

/-- **A `KS` region's target base** (claim 49's `regTgt`, the blob's `TYPED` offset). -/
def ksTgt (lay : Lay) (r : YReg) : ℕ := Lvm6.KSP.ksTgt ksP18 lay r

/-- **A region's `C_main`/`C_rec` target base** (the blob's `TYPED` offset; CC's claims 48, 49): `com` words at
`38·2^19 + y`, `σ′` at `2^18`, `KS` per KSA's `ksTgt` (one target base per lane region). -/
def regTgt (lay : Lay) (r : YReg) : ℕ :=
  match r.src with
  | .com => 38 * 2 ^ 19 + r.base
  | .sigma => 2 ^ 18
  | .ks => ksTgt lay r
  | _ => 0

end Consts

section CC

open LeanVM.Parameters LeanVM.Protocol.Compile LeanVM.Protocol.Verifier
open Lvm Lvm.Loop Lvm.Loop.Build Lvm.Q2 Lvm.Har Lvm.E2V Lvm6 Lvm6.QK Lvm6.QC

/-! ## Stream lanes of `sched6 P18` (NODE's `laneWalk`, recording the lane at every item) -/

/-- The lane `a` at every item (as `Lvm6.Node.laneWalk`: resynchronised after each opening). -/
def walkA (L : List V.Lev) : List V.Item → List ℕ → ℕ → ℕ → List ℕ
  | [], _, _, _ => []
  | it :: its, lens, a, off =>
    a :: (match it with
      | .E _ => walkA L its lens (layEnd [it] a) off
      | .K _ => walkA L its lens (layEnd [it] a) off
      | .cap _ => walkA L its lens (layEnd [it] a) off
      | .open i =>
        let n := V.queriesI L (.open i)
        let off' := off + Lvm.QLink.slenS (lens.take n)
        walkA L its (lens.drop n) (off' / 8 + 5) off'
      | _ =>
        let n := V.queriesI L it
        walkA L its (lens.drop n) (layEnd [it] a) (off + Lvm.QLink.slenS (lens.take n)))

def lanes18 : Array ℕ :=
  (walkA P18.levs (sched6 P18) Lvm6.Node.lens2 (Lvm6.Node.off2 / 8 + 5) Lvm6.Node.off2).toArray


/-- The schedule's items and their lanes, computed once and passed around. -/
structure Geo where
  ln : Array ℕ
  it : Array V.Item

def laneAt (G : Geo) (i : ℕ) : ℕ := G.ln.getD i 0
def itAt (G : Geo) (i : ℕ) : V.Item := G.it.getD i default

/-- The answer cells of the draws of item `i` (`layItems`' geometry). -/
def drawsAt (G : Geo) (i : ℕ) : List C2 :=
  let a := laneAt G i
  match itAt G i with
  | .G _ => [ld2 (a + 1)]
  | .D k => (List.range k).map fun j ↦ ld2 (a + 9 * j)
  | .B => [ld2 a]
  | .pos l _ => ld2 (a + 1) :: (List.range (posD l)).map fun j ↦ ld2 (a + 10 + 9 * j)
  | _ => []

/-- The scalar cells of item `i` (`E n`). -/
def scalarsAt (G : Geo) (i : ℕ) : List C2 :=
  match itAt G i with
  | .E n => (List.range n).map fun j ↦ ld2 (laneAt G i + 2 * j)
  | _ => []

def drawsIn (G : Geo) (lo hi : ℕ) : List C2 := (List.range (hi - lo)).flatMap fun d ↦ drawsAt G (lo + d)
def scalarsIn (G : Geo) (lo hi : ℕ) : List C2 :=
  (List.range (hi - lo)).flatMap fun d ↦ scalarsAt G (lo + d)

/-! ### Item indices of the parts of `sched6 P18` -/

def iT : ℕ := P18.commitPart.length
def iS : ℕ := iT + P18.treePart.length
def iSc : ℕ := iS + P18.subT.spCaller.length
def iSl : ℕ := iSc + (P18.keccakCore P18.κs false).length
def iTy : ℕ := iS + P18.spongePart.length
def iBus : ℕ := iTy + P18.subT.typed.length
def iR : ℕ := iBus + P18.subT.bus.length
def iO : ℕ := iR + P18.ringPart.length
def iLev (j : ℕ) : ℕ := iO + ((List.range j).map fun i ↦ (P18.levelPart i).length).sum

/-! ### The level parameters of `P18` (W1's `lad18`) -/

structure LP where
  ko : ℕ
  ℓ : ℕ
  h : ℕ
  kq : ℕ
  t : ℕ
  c : ℕ

/-- Levels 0–3 (`midE i ko ℓ h … kq t c`), level 4 = `fin18` (`κ ℓ h kq t c = 3 4 17 2 18 7`; `ko` unused). -/
def lp : ℕ → LP
  | 0 => ⟨18, 6, 21, 18, 110, 6⟩
  | 1 => ⟨14, 4, 20, 7, 45, 6⟩
  | 2 => ⟨10, 4, 19, 4, 28, 6⟩
  | 3 => ⟨6, 4, 18, 2, 21, 7⟩
  | _ => ⟨2, 4, 17, 2, 18, 7⟩

/-- Level `j`'s position-bit region: `128·draws` cells after the earlier levels'. -/
-- LAY5 (W3 lever 1): level `j`'s bit block at an aligned offset (`128·draws` cells: 2432, 1024, 640, 384, 384),
-- so the per-instance bit reads of `boolG`/`laneG` are aligned externals (`d = 3`).
def bOf (B j : ℕ) : ℕ := B + [0, 4096, 5120, 6144, 6656].getD j 0

/-! ### Inputs: derived stream lanes and representative ones (computed once, `Inp`) -/

def sigBg : ℕ := 2 ^ 19 + 2 ^ 11
/-- Mini-bus: `nParts` parts a claim, each `⟨10, k·2^10⟩` with 10 point cells. Representative. -/
def nParts : ℕ := 4

structure Inp where
  aRing : ℕ
  aLev : List ℕ
  z0 : List C2
  y0 : List C2
  svT : List C2
  svS : List C2
  treeX : List C2
  /-- Tree claim 2's point `(u, ρ, ϱm)`. -/
  tPt2 : List C2
  /-- The tree's `ρ` (claims 3–10's point `ρ ‖ 0 ‖ bits(m, 6)`). -/
  tRho : List C2
  spX : List C2
  rS : List C2
  rhoM : List C2
  rhoP : List C2
  lamL : List C2
  rY : List C2
  rrc : List C2
  busD : List C2
  busS : List C2
  vs : List C2
  /-- Claim 47's `σ` region base (B1: the layout's, `sigBgOf`). -/
  sigB : ℕ
  /-- Claims 48 and 49's regions `(log, base, target)` (B1: the layout's `com` and `ks` regions, `regsOf`). -/
  comQs : List (ℕ × ℕ × ℕ)
  ksQs : List (ℕ × ℕ × ℕ)
  /-- Claims 50–52's parts per side (MBT phase 2: `mbPreG`'s cells; `mkInp`: representative). -/
  mbP : List (List (C2 × LeanVM.Protocol.Verifier.Placement × List C2))

/-- * `z₀` (§6.1 `G 18, D 24`), `y₀` (`E 1`): derived. * slice values: the tree's and the sponge core's last
`E 64`. * points of 25 coordinates (tree claims 2–14 and the tree slice point; the sponge slice point): the last
25 draws of the tree part / the sponge core (representative). * `r` (13): the caller's draws; `ϱm` (6): the
core's `outR` round draws. * the link's 18 draws: `ρ'` first 13, `λ` next 5 (representative split). * typed:
`r_y` the 21 rounds after `rnd 3 2`, the relay's `r` 19 round draws (representative). * the 51 stack-claim
values: `y₀`; 13 of the tree's `E 21`; the caller's `E 25`, the link's `E 4`, the typed `E 4, E 4`
(representative except `y₀`). -/
def mkInp (G : Geo) : Inp :=
  let tyD := drawsIn G iTy iBus
  let spc := drawsIn G iSc iSl
  let lk := drawsIn G iSl iTy
  let y0 := scalarsAt G 4
  let busD := drawsIn G iBus iR
  let busS := scalarsIn G iBus iR
  { aRing := laneAt G iR
    aLev := (List.range 5).map fun j ↦ laneAt G (iLev j)
    z0 := drawsIn G 2 4
    y0 := y0
    svT := scalarsAt G (iS - 1)
    svS := scalarsAt G (iSl - 1)
    treeX := (drawsIn G iT iS).reverse.take 25 |>.reverse
    tPt2 := (drawsIn G iT iS).reverse.take 25 |>.reverse
    tRho := ((drawsIn G iT iS).reverse.take 25 |>.reverse).take 18
    spX := spc.reverse.take 25 |>.reverse
    rS := drawsIn G iS (iS + 13)
    rhoM := (spc.drop (spc.length - 16)).take 6
    rhoP := lk.take 13
    lamL := (lk.drop 13).take 5
    rY := (tyD.drop 41).take 21
    rrc := (tyD.drop 20).take 19
    busD := busD
    busS := busS
    mbP := (List.range 3).map fun s ↦ (List.range nParts).map fun k ↦
      (busS.getD (s * nParts + k) default, ⟨10, k * 2 ^ 10⟩, busD.take 10)
    sigB := sigBg
    comQs := [(19, 0, 38 * 2 ^ 19)]
    ksQs := [(18, 2 ^ 20, 36 * 2 ^ 19)]
    vs := y0 ++ (scalarsAt G (iT + 5)).take 13 ++ scalarsAt G (iS + 13) ++ scalarsAt G (iTy - 1) ++
      scalarsAt G (iTy + 104) ++ scalarsAt G (iTy + 105) }

def geo18 : Geo := ⟨lanes18, (sched6 P18).toArray⟩
def inp18 : Inp := mkInp geo18

def Inp.aL (I : Inp) (j : ℕ) : ℕ := I.aLev.getD j 0

/-- Claim `50 + s`'s parts (`Inp.mbP`; MBT phase 2: `mbPreG`'s, from the deployed tables). -/
def mbQs (I : Inp) (s : ℕ) : List (C2 × LeanVM.Protocol.Verifier.Placement × List C2) := I.mbP.getD s []

/-- `levelGenW` at level `j`, the generator. -/
def levCall (I : Inp) (B j : ℕ) (gate : Cell) : BM (List RndC × TailOutC × List (List C2)) :=
  let q := lp j
  levelGenW q.ℓ q.ko q.t (posGen (bOf B j) q.h q.c q.kq q.t) (valsGenW (j == 0) q.h q.ℓ (q.ko + 1)) 10 q.ℓ
    (P18.lvl j) (wdOf j) (P18.lvl (j + 1)).lv (I.aL j) gate

/-- **Tree claims 2–14** (`K.treeColsS`, WP ORD's order): `(u, ρ, ϱm)`; `ρ ‖ 0 ‖ bits(m, 6)` for `m < 8` (the
`0 ‖ bits(m, 6)` tail is `bits(2m, 7)`); `bits(0, 19) ‖ bits(4 + m, 6) = bits((4 + m)·2^19, 25)` for `m < 4`. -/
def treeClaimGs (I : Inp) : List (List C2 → Cell → BM C2) :=
  eqClaimG I.tPt2 :: ((List.range 8).map fun m ↦ eqBitsClaimG I.tRho (2 * m) 7) ++
    (List.range 4).map fun m ↦ eqBitsClaimG [] ((4 + m) * 2 ^ 19) 25

/-- **The level-0 claims' weight gadgets** in ORD's order (`placeRing`): 0, ring 1, 2–14, ring 15, 16–52 (53
gadgets; claim 44 is CLG's `cMG λ ρ'`; claims 50–52 are MBS's `mbClaimFG`, grouped by `τ`). The exporter's
`claimSpecs` with the generator halves only. -/
def claimGs (I : Inp) (rp : RingPhC) : List (List C2 → Cell → BM C2) :=
  [eqClaimG I.z0, ringClaimG 25 I.treeX rp.ft rp.gt] ++
  treeClaimGs I ++
  [ringClaimG 25 I.spX rp.fs rp.gs, eqBitsClaimG (I.rS ++ I.rhoM) 35 6] ++
  (List.range 25).map (fun l ↦ eqBitsClaimG I.rS (36 * 64 + l) 12) ++
  [laneSumG I.lamL I.rhoP 25 (36 * 64) 6 12,
   laneSumG I.lamL I.rhoP 25 (35 * 64) 6 12,
   cMG I.lamL I.rhoP,
   laneSumG I.lamL (I.rhoP.take 10) 17 (37 * 2 ^ 9) 9 15,
   relayClaimG I.rrc,
   sigClaimG I.rY I.sigB,
   regClaimG I.rY I.comQs,
   regClaimG I.rY I.ksQs] ++
  (List.range 3).map fun s ↦ Lvm6.Node.MbS.mbClaimFG 25 (mbQs I s)


/-- **The CC part of the node circuit at `P18`** (program order): the ring phase (CC-5′), the four mid levels
(`levelGenW` with `posGen`/`valsGenW`), the claim chain (`claimGlueG` ×4 from the ring phase's value cell),
then the final level `finGen` whose weight gadget is `glueGW` ×4 over `wBatchG` (so the level-0 weight cell
and the glue steps run inside `finGen`, at its `wG` call after `mleG`). -/
def ccG18I (I : Inp) (B : ℕ) (gate : Cell) : BM Unit :=
  ringPhaseGen 17 I.svT I.svS I.vs I.aRing gate >>= fun rp ↦
  levCall I B 0 gate >>= fun l0 ↦ levCall I B 1 gate >>= fun l1 ↦ levCall I B 2 gate >>= fun l2 ↦
  levCall I B 3 gate >>= fun l3 ↦
  claimGlueG rp.val l0.1 l0.2.1 >>= fun s1 ↦ claimGlueG s1 l1.1 l1.2.1 >>= fun s2 ↦
  claimGlueG s2 l2.1 l2.2.1 >>= fun s3 ↦ claimGlueG s3 l3.1 l3.2.1 >>= fun s4 ↦
  let w0 := wBatchG (claimGs I rp) rp.lam
  let w4 := glueGW (glueGW (glueGW (glueGW w0 l0.1 l0.2.1 l0.2.2) l1.1 l1.2.1 l1.2.2) l2.1 l2.2.1 l2.2.2)
    l3.1 l3.2.1 l3.2.2
  finGen 12 18 (posGen (bOf B 4) 17 7 2 18) (fun rc ↦ fvGen 17 4 3 rc) (fpGen 3 4) w4 10 2 3 4
    (P18.lvl 4) 32 (I.aL 4) s4 gate >>= fun _ ↦ pure ()

/-- **`ccG18`** at the stream lanes of `P18` (`inp18`: LAY3's representative claim data; superseded by
`ccG18o`). -/
def ccG18 (B : ℕ) (gate : Cell) : BM Unit := ccG18I inp18 B gate

/-- The child header's lane `l` in the stream (`HDR` from word `hdrW 0` of `S_flat`, at `sbC = 0`). -/
def hdrLaneC (l : ℕ) : Cell := kc (11 + l)

/-- **CC's computed inputs** from the node's outputs: a zero and a one, and tree claims 3–6's values
`D⁰_m + eq(ρ, 0)·δ_m` (`K.treeColsS`). -/
def ccPre (o : Lvm6.Node.NodeOutE) : BM (C2 × C2 × List C2) :=
  g2Zero o.tree.u >>= fun z ↦ g2Const 1 z >>= fun one ↦ eqAtG z one o.tree.ρ 0 >>= fun e ↦
    mapB (fun m ↦ g2Mul e ⟨o.tree.δ.getD m z.re, z.re⟩ (o.tree.dd.getD m z)) (List.range 4) >>= fun tv ↦
      pure (z, one, tv)

/-- **The layout's regions of a source** with their targets (CC's claims 48, 49: `RegAff`'s list). -/
def regsOf (lay : Lvm.Typed.Lay) (s : Lvm.Typed.YSrc) : List (Lvm.Typed.YReg × ℕ) :=
  (lay.yregs.filter fun r ↦ r.src == s).map fun r ↦ (r, regTgt lay r)

/-- **The layout's `σ′` region base** (CC's claim 47). -/
def sigBgOf (lay : Lvm.Typed.Lay) : ℕ := (((lay.yregs.filter fun r ↦ r.src == .sigma).head?).map (·.base)).getD 0

/-- **CC's real inputs** (NODE3 phase 2), in ORD's order, from the cells of `node6E`'s outputs:
* slices: the tree's `en` (`pt`, `s`), the sponge core's (`pt ‖ bits(35, 6)`, `s`) (`K.toS`, `SP.spS`);
* tree claims 2–14 (`treeClaimGs`) with values `c_out`, `D⁰_m + eq(ρ, 0)·δ_m` (`ccPre`), `D¹_m`, and the child
  header's root lanes `h_m` (`HDR` bytes 24–55, lanes 3–6) as `K` cells;
* sponge claims: `r`, `ϱm`, `v` (caller), `ρ'` = the link's `shift`, `λ` = `kchal` past 13, the link's values;
* typed: `r_y` (wiring), `r` and `v_R` (relayout), the region values `rv[2]` (σ), `rv[0]` (com), `rv[3]` (`KS`);
* the mini-bus claims (50–52) (MBT phase 2): parts and values are `mbPre`'s cells `mo` (`mbPartsG`, `mbValueG` of
  the deployed tables at the walk's outputs, `hs_mbPreG`).
`z₀`, `y₀`, the ring and level lanes are the stream's (`mkInp`, derived). -/
def inpReal (o : Lvm6.Node.NodeOutE) (lay : Lvm.Typed.Lay) (z one : C2) (tv : List C2)
    (mo : List (List (C2 × LeanVM.Protocol.Verifier.Placement × List C2)) × List C2) : Inp :=
  let kC : Cell → C2 := fun k ↦ ⟨k, z.re⟩
  { inp18 with
    sigB := sigBgOf lay
    comQs := regQs (regsOf lay .com)
    ksQs := regQs (regsOf lay .ks)
    svT := o.tree.s
    svS := o.sp.s
    treeX := o.tree.pt
    tPt2 := (o.tree.u :: o.tree.ρ) ++ o.tree.ϱm
    tRho := o.tree.ρ
    spX := o.sp.pt ++ bitC z one 35 6
    rS := o.sp.r
    rhoM := o.sp.ϱm
    rhoP := o.link.shift
    lamL := o.link.kchal.drop 13
    rY := o.ty.wire.ry
    rrc := o.ty.relay.rr
    mbP := mo.1
    vs := inp18.y0 ++ [o.tree.cout] ++ tv ++ ((List.range 4).map fun m ↦ o.tree.dd.getD (4 + m) z) ++
      ((List.range 4).map fun m ↦ kC (hdrLaneC (3 + m))) ++ [o.sp.cout] ++ o.sp.v ++ o.link.vals ++
      [o.ty.relay.vR, o.ty.wire.rv.getD 2 z, o.ty.wire.rv.getD 0 z, o.ty.wire.rv.getD 3 z] ++
      mo.2 }

/-- **MBT phase 2: claims 50–52's parts and values** (`mbPreG` on the mini-bus walk's output cells, the tables
`tabs`; `hs_mbPreG`: `mbPartsG`, `mbValueG`). -/
def mbPre (tabs : List Lvm.M3.Tab) (o : Lvm6.Node.NodeOutE) (gate : Cell) :
    BM (List (List (C2 × LeanVM.Protocol.Verifier.Placement × List C2)) × List C2) :=
  Lvm6.Node.MbC.mbPreG tabs o.ty.mb.alphas o.ty.mb.beta o.ty.mb.point o.ty.mb.values gate

/-- **The deployed CC part**: `ccPre`, the mini-bus claims' cells (`mbPre`, tables `tabs`), then `ccG18I` on the
real inputs. -/
def ccG18o (o : Lvm6.Node.NodeOutE) (lay : Lvm.Typed.Lay) (tabs : List Lvm.M3.Tab) (B : ℕ) (gate : Cell) :
    BM Unit :=
  ccPre o >>= fun pr ↦ mbPre tabs o gate >>= fun mo ↦ ccG18I (inpReal o lay pr.1 pr.2.1 pr.2.2 mo) B gate
end CC

section Cells

open Lvm Lvm.Loop Lvm.Loop.Build Lvm.Q2 Lvm.Typed Lvm6 Lvm6.QD Lvm6.Node Lvm6.QK Lvm.QSig
open Lvm6.Q (Layout6 qlink6 opensP18 qsig6)

/-- `Q_link`'s layout (CD's `m = 19`, `K = 6`, `aQ = 11`; `cp` = the child's statement cells, `Q_sig`'s `I.cL`).
NODE3 F1 (N4-cells): `cp = pbC + 7`, `c'`'s first `PUB` lane (FORMAT6 §2: `magic, b, n, h₀₋₃, c'₀₋₃, vk₀₋₃, …`). -/
def lay6 : Layout6 := ⟨sbC, pbC + 1, qtC, bbC, 19, 6, 11, pbC + 7⟩

/-- `Q_sig`'s walk over `σ'` (season 1's `sigIn` offsets; `KS` rows lane-split). NODE3 F1 (N4-cells): the key
`vk = pbC + 11` and `cL = pbC + 7` are FORMAT6 §2's `PUB` lanes (season 1's order put them at `+2`, `+6`). -/
def sigI : SigIn :=
  ⟨pbC + 1, pbC + 11, pbC + 7, pbC + 18, hdC, sgC, mdC, ysC, ysC + 4 * 430, ysC + 4 * 447, ysC + 4 * 448,
    obC, obC + 18, obC + 274, obC + 284, obC + 3476, obC + 4540, obC + 4820, obC + 4796, obC + 4804, obC + 4812,
    xsC, 18⟩

/-- The leaf walk over `σ_leaf` (variant C's offsets, `sigInLC`; its own `KS` rows and `BITS` region). -/
def sigIl : SigIn :=
  { sigI with
    sg := dstC
    ys := ysC + 4 * 2 ^ 10
    yc := ysC + 4 * 2 ^ 10 + 4 * (nStepRowsC + 31)
    yls := ysC + 4 * 2 ^ 10 + 4 * 447
    yns := ysC + 4 * 2 ^ 10 + 4 * 448
    bi := olC
    bd := olC + 18
    bc := olC + 274
    bx := olC + 18
    be := olC + 18 + gBxC 3
    bp := olC + 18 + gBxC 3 + 1064
    xs := xsC + 17 * 2 ^ 9 }

/-- The PoW answers of a plan, the lanes by lookups (SU2; `powAnsOf_eq`). -/
def powAnsOf (P : List Lvm6.Q.PE6) : List (ℕ × ℕ) :=
  let A := (Lvm6.Q.offsL P 1).toArray
  let PA := P.toArray
  (List.range P.length).filterMap fun i ↦ match (PA.getD i default).k with
    | .fs _ g => if 1 ≤ g then some (sbC + Lvm6.Q.ansLaneF A PA P.length i, g) else none
    | _ => none

theorem powAnsOf_eq (P : List Lvm6.Q.PE6) : powAnsOf P =
    (List.range P.length).filterMap fun i ↦ match (P.getD i default).k with
      | .fs _ g => if 1 ≤ g then some (sbC + Lvm6.Q.ansLane6 P i, g) else none
      | _ => none := by
  simp only [powAnsOf, Lvm6.Q.ansLaneF_eq, Array.getD_eq_getD_getElem?, List.getElem?_toArray,
    ← List.getD_eq_getElem?_getD]

/-- The PoW answers `(stream cell of the answer, g)`: every chain entry `fs st g` with `g ≥ 1` (`PowOK6`;
`powAns_eq`). -/
def powAns : List (ℕ × ℕ) := powAnsOf P6

theorem powAns_eq : powAns = (List.range P6.length).filterMap fun i ↦ match (P6.getD i default).k with
    | .fs _ g => if 1 ≤ g then some (sbC + Lvm6.Q.ansLane6 P6 i, g) else none
    | _ => none := powAnsOf_eq P6

def hdrW (k : ℕ) : ℕ := 11 + k

theorem hdrLaneC_eq (l : ℕ) : hdrLaneC l = kc (sbC + hdrW l) := by
  simp [hdrLaneC, sbC, hdrW]
def ainC : List C2 := (List.range 43).map fun i ↦ ld2 (sbC + hdrW (15 + 2 * i))
def yInC : C2 := ld2 (sbC + hdrW (15 + 86))
def ownC : List C2 := (List.range 43).map fun i ↦ ld2 (pbC + 15 + 2 * i)
def ownYC : C2 := ld2 (pbC + 15 + 86)
def gateC : Cell := kc (pbC + 1)

/-- The deployed typed instance (WP KSA: `ksW := ksWOf lay`, the `KS` aliases' targets). -/
def tiOf (lay : Lay) : Lvm6.Ty.TInst6 := ⟨toProgram 0 0 (pure ()), lay, [], id, ksWOf lay, id, id, fun _ ↦ 0⟩

def pubCOf (lay : Lay) (y : ℕ) : Cell :=
  let l := y - pubBase (tiOf lay)
  if l < 103 then kc (sbC + hdrW l) else kc zC
/-- **`Q_link`, `Q_sig` and the `σ_leaf` copy** (the exporter's `famM lay 3` after `node6E`). -/
def famR : BM Unit :=
  qlink6 P6 opensP18 lay6 >>= fun _ ↦ (qsig6 sigI sigIl sbC >>= fun _ ↦ pure ()) >>= fun _ ↦
    sigLeafCopy6 dstC (sgC + 597) (pbC + 1)

/-- **The mini-bus's placement parameters** (MBT): the stream at `sbC`, `C_main` of `2^25` words, the count words
in slot 36 from word `2^18` (CD §3), the region targets `regTgt`. -/
def mbPar6 (lay : Lay) : Lvm6.Node.Mb.MbPar := ⟨sbC, Ty.L6.nuMain, 36 * 2 ^ 19 + 2 ^ 18, regTgt lay⟩

theorem mbPar6_ok (lay : Lay) : (mbPar6 lay).Ok := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> dsimp only [mbPar6] <;> decide

/-- **The program before CC** (`node6E`, `famR`): the cap `readd` cells, whose words the mini-bus's read
tables take (MBT: CC's claims 50–52 read the tables, so the tables come from the families before CC). -/
def progR (lay : Lay) : Program :=
  Lvm.VF.toProgramF nK 0 (node6E (tiOf lay) (pubCOf lay) ainC yInC ownC ownYC gateC >>= fun _ ↦ famR)

/-- **The deployed mini-bus tables** on the layout `lay` (`mbTL` on `progR lay`). -/
def mbTD (lay : Lay) : List Lvm.M3.Tab := Lvm6.Node.Mb.mbTL (mbPar6 lay) (progR lay) lay

/-- **The deployed node circuit** (all five families): `node6E` (tree, sponge caller and link, typed), then
`famR`, then CC on `node6E`'s output cells (`ccG18o`). -/
def famQ6 (lay : Lay) : BM Unit :=
  node6E (tiOf lay) (pubCOf lay) ainC yInC ownC ownYC gateC >>= fun o ↦ famR >>= fun _ ↦
    ccG18o o lay (mbTD lay) ccbC gateC

/-- **The deployed program** on the layout `lay`. -/
def progQ6 (lay : Lay) : Program := Lvm.VF.toProgramF nK 0 (famQ6 lay)

end Cells

/-- **LAY5's position-bit blocks** lie in `ccbC`'s `2^13` cells, in order and disjoint: level `j`'s block has
`128·(kq_j + 1)` cells (`kq` = 18, 7, 4, 2, 2). -/
theorem bOf_blocks : ∀ j < 5, bOf 0 j + 128 * ((lp j).kq + 1) ≤ (if j + 1 < 5 then bOf 0 (j + 1) else 2 ^ 13) := by
  decide

theorem bOf_add (B j : ℕ) : bOf B j = B + bOf 0 j := by
  simp [bOf]

end Lvm6.Node.Dep
