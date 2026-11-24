-- New for lvm6 (PORT17 L1): the shape `P17` (`N★ = 2^17`, FORMAT6 v2.6, P17-freeze §1.1) beside `P18`, with the
-- kernel checks `Lvm6Format` has for `P18`, in the same form.
import Lvm6Format
import Lvm6Params17
import Lvm6VSched17

/-!
# The shape `P17` (FORMAT6 v2.6)

`P17` is the port's shape (P17-freeze §0, §1.1): `N★ = 2^17`, `κ = 18`, `κs = 13`, `M = 24`, 46 lanes,
`phiVars = 43`, the five WHIR levels `ht = 20, 19, 18, 17, 16` with `P18`'s caps, openings, folds and grinds
except level 4's query grind (18), the final polynomial of `2^2 + 4` scalars, two tail rounds; `qS = 4,106`,
`|π| = 230,424`. Its sub-schedules `subT17` are `subT18` with 18 relayout rounds (`C_rec = ⟨18, 33·2^18⟩`).
`P18` stays as it is until the port's rename (C1).

Every statement has the form of its `P18` counterpart in `Lvm6Format` (and `Lvm6FSCert` for the two ties to
`qS`/`qV`), with `P17`, `subT17`, `V.sched17`, `V.levs17` and PARAM's row at `M = 24` (`Lvm6.Params17`).
-/

set_option autoImplicit false

namespace Lvm6

open RecursionFast LeanVM.Parameters

/-- The sub-schedules of `P17` (P17-freeze §1.1): `subT18`'s, except the typed phases' relayout, 18 rounds
(`C_rec` is one slot of `2^18` words): 83 draws and 174 scalars (FORMAT6 v2.6 §6.4a). The sponge lists are
`subT18`'s by reference, so `Lvm6IntTies.subT18_sponge_eq` holds for them by `rfl`. -/
def subT17 : SubT where
  spCaller := subT18.spCaller
  spLink := subT18.spLink
  typed := rep 20 [.G 1] ++ rep 20 (rnd 2 2) ++ rnd 3 2 ++ rep 21 (rnd 2 2) ++ [.E 4, .E 4] ++
    rep 18 (rnd 2 2) ++ [.E 1] ++ rep 2 [.G 1] ++ rnd 44 6
  bus := subT18.bus

/-- **The port's shape** `P17` (FORMAT6 v2.6): `N★ = 2^17`, `κ = 18`, `κs = 13`, `M = 24`, 46 lanes, the five
WHIR levels of v2.6 §5, `phiVars = 43`, the sub-schedules `subT17`; `qS = 4,106`, `|π| = 230,424`. -/
def P17 : Shape where
  logN := 17
  κ := 18
  κs := 13
  M := 24
  lanes := 46
  phiVars := 43
  layers := 12
  prodLen := 47
  posRounds := 11
  levels := [⟨20, 7, 368, 110, 6, 10, 18, 19⟩, ⟨19, 6, 256, 45, 4, 10, 18, 17⟩,
    ⟨18, 5, 256, 28, 4, 10, 18, 18⟩, ⟨17, 5, 256, 21, 4, 10, 18, 17⟩,
    ⟨16, 5, 256, 18, 4, 10, 18, 18⟩]
  finalLen := 8
  tail := 2
  gRing := 17
  J₀ := 1024
  L₀ := 111
  gr := grinds18
  subT := subT17
  qS := 4106
  piLen := 230424

/-! ## The counts of `P17` (kernel-checked against FORMAT6 v2.6 §6–§7 and `Lvm6.Params17`) -/

/-- **`qS` is the schedule's query count** (FORMAT6 v2.6 §7: `3,926 + Q_sp + Q_ty + Q_mb`). -/
theorem qS_P17 : qSOf P17 = P17.qS := by decide +kernel

/-- **`|π|` is the header and the schedule's bytes.** -/
theorem piLen_P17 : piLenOf P17 = P17.piLen := by decide +kernel

/-- **The length rule holds** for `P17`'s schedule (and every query is within `2^20` bytes). -/
theorem fsLenOK_P17 : fsLenOK P17 = true := by decide +kernel

theorem shapeOK_P17 : shapeOK P17 = true := by decide +kernel

theorem stackOK_P17 : stackOK P17 = true := by decide +kernel

/-- The seed of `P17` is 856 bytes (`|HDR| = 824`). -/
theorem seedLen_P17 : seedLen P17 = 856 ∧ hdrLen P17 = 824 := by decide

/-- `qS ≤ qV = 16384` (PARAM at `M = 24`). -/
theorem qS_le_qV_P17 : P17.qS ≤ Params17.qV := by decide

/-- **One schedule**: `sched6 P17` is V1's `sched17` with `P17`'s sponge part and §T lists, and `P17`'s levels
are V1's `levs17`; FORMAT6 v2.6's §6 table is V1's `counts_*_17`. -/
theorem sched6_P17 :
    sched6 P17 = V.sched17 (P17.spongePart ++ subT17.typed ++ subT17.bus) ∧ P17.levs = V.levs17 := by
  decide +kernel

/-- `qS` is FORMAT6 v2.6 §7's `3,926 + Q_sp + Q_ty + Q_mb`, with the sponge core 298. -/
theorem qS_split_P17 :
    qSOf P17 = 3926 + V.queriesOf P17.levs (subT17.spCaller ++ subT17.spLink) +
      V.queriesOf P17.levs subT17.typed + V.queriesOf P17.levs subT17.bus := by
  decide +kernel

/-- **`P17` is PARAM's frozen row at `M = 24`** (`Lvm6.Params17`): stack, lanes, the levels' sizes, folds,
openings, caps and grinds, the batch grind, `J₀`, the level-0 list `L₀` (`listOf`), the residual, and the grinds
of the Keccak groups (tree rows 0–8, sponge rows 10–16, tail row 34 of `P.groups`). -/
theorem P17_params :
    P17.M = Params17.stackLog ∧ P17.lanes = Params17.leaf0Lanes ∧ P17.tail = Params17.residualLog ∧
    P17.gRing = Params17.batchGrind ∧ P17.J₀ = Params17.stackedClaims ∧
    P17.L₀ = Params17.listOf (Params17.levels.getD 0 (0, 0, 0, 0, [])) ∧
    P17.levels.map (fun l => (l.ht, l.fold)) =
      Params17.levels.map (fun l => (l.1 + l.2.1, l.2.2.1)) ∧
    P17.levels.map (·.nOpen) = Params17.queries ∧ P17.levels.map (·.lv) = Params17.logCaps ∧
    P17.levels.map (·.gFold) = Params17.foldGrind ∧ P17.levels.map (·.gOod) = Params17.oodGrind ∧
    P17.levels.map (·.gQuery) = Params17.queryGrind ∧
    [P17.gr.rho, P17.gr.u, P17.gr.seg, P17.gr.layer, P17.gr.eqR, P17.gr.posR, P17.gr.beta,
      P17.gr.outR, P17.gr.inR] = (Params17.groups.take 9).map (·.2) ∧
    [P17.gr.seg, P17.gr.layer, P17.gr.eqR, P17.gr.posR, P17.gr.beta, P17.gr.outR, P17.gr.inR] =
      ((Params17.groups.drop 10).take 7).map (·.2) ∧
    P17.gr.tail = (Params17.groups.getD 34 (0, 0)).2 := by
  decide +kernel

/-- **`Params17.qS` is the schedule's count** (FORMAT6 v2.6: 4,106; `Lvm6FSCert.qS_eq_params`'s form). -/
theorem qS_eq_params17 : qSOf P17 = Params17.qS := by decide +kernel

/-- `qV` is within `2^16` and covers `qS · 3/2` (`Lvm6FSCert.qV_ok_P18`'s form). -/
theorem qV_ok_P17 : Params17.qV ≤ 2 ^ 16 ∧ qSOf P17 * 3 / 2 ≤ Params17.qV := by decide +kernel

/-! ## The examples of FORMAT6 v2.6 §5 (non-vacuity of the codec at `P17`'s heights) -/

/-- §5: the positions of `00 01 … 1f` at level 0 (`ht = 20`). -/
theorem ans0_pos_P17 : posOf 20 ans0 = [131328, 16432, 460293, 36992, 789258, 57552] := by
  decide +kernel

/-- §5: the positions of `00 01 … 1f` at level 4 (`ht = 16`): eight a draw, all 128 bits of `N`. -/
theorem ans0_pos4_P17 : posOf 16 ans0 = [256, 770, 1284, 1798, 2312, 2826, 3340, 3854] := by
  decide +kernel

end Lvm6
