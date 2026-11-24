-- New for lvm6 (WP N4-split). NODE3 §2 items (3) and (2) at `P17`: V1's values `(accOf ….map NV.val).reverse`
-- split into the six phase segments, the tree, sponge and typed segments match the circuit's stream slots
-- (`EvMatch`, `NoRows`, `PowLay`), and the commitment phase returns on its segment (`hc`); `dec_of_split`.
import Lvm6NodeSplitSim

/-!
# The stream-lane split at `P17` (WP N4-split)

The driver's walk from `st0` (V1's `ns0`, entry 2) is cut at the parts of `sched6 P17`: `segAt ws pre part` are
the values `part` adds after the items `pre` (`Lvm6NodeSplitSim.segV`).

* **`split6`**: `(accOf P17 π tr).map (NV.val π)).reverse = vc ++ vt ++ vs ++ vy ++ vr ++ vo` (the six
  `segAt`), and for `vt`, `vs`, `vy` at the circuit's slots `layItems (treeItems 18) aTree`,
  `layItems (spItems 13 ++ linkItems 13) aSp`, `layItems (tyItems ++ mbItems) aTy`: `PowLay`, `NoRows`,
  `EvMatch`. Inputs: the stream words `ws` cover the plan (`hashedLen6 P6 ≤ 8|ws|`), the memory's `K` cells
  `0 … |ws|−1` are the stream (`QIn6.stream`, `sbC = 0`), and `PowLanes6 P6 ws`.
* **`hc6`** (item (2)): `afterV (commit6 P17) vc = some (.ret c0)` for some `c0`: the kinds of `vc` and the
  grind of its ground draw (`PowOK6` from `PowLanes6`, at the plan entry the simulation names).
* **`inv_ring`**: the simulation state at the ring part (lane `partLane` of the items before it), for CC.
* **`dec_of_split`**: `dec_of_runs` with `hsplit`, the slot facts and `hc` discharged.

The lane geometry is the simulation's (`laneW w = eLane6 P6 w.i + 5 + w.pend / 8`), which equals `partLane`
of the items before each part; no concrete schedule is evaluated except `plain17`/`tyItems_P17`
(`decide +kernel`, one table each).
-/

set_option autoImplicit false

namespace Lvm6.Node.Split

open RecursionFast Lvm Lvm.Replay Lvm6.Q Lvm6.QK Lvm6.Node
open Lvm.QLink (lw laneK slenS)
open LeanVM.Protocol.Compile hiding Proof Bytes Word
open Lvm.Loop Lvm.Loop.Build Lvm.Q2 Lvm.Har Lvm.E2V Lvm6.QK.W Lvm.QSig LeanVM.Parameters

set_option hygiene false in
local notation "τW" => decode6 P6 ws
set_option hygiene false in
local notation "πW" => reassemble6 P6 (decode6 P6 ws)

/-! ## The segments -/

/-- V1's driver state at the schedule's start (`accOf`). -/
def st0 (ws : List Word) : AS := (ns0 P17 (aOf (decode6 P6 ws) 1), 2)

/-- The state after the items `pre`. -/
def stAt (ws : List Word) (pre : List V.Item) : AS := nxt πW P17.levs τW pre (st0 ws)

/-- **The values the items `part` add after `pre`.** -/
def segAt (ws : List Word) (pre part : List V.Item) : List V.Val := segV πW P17.levs τW part (stAt ws pre)

/-- The items before the tree, sponge, typed, ring and opening parts. -/
def preT : List V.Item := P17.commitPart
def preS : List V.Item := preT ++ P17.treePart
def preY : List V.Item := preS ++ P17.spongePart
def preR : List V.Item := preY ++ (P17.subT.typed ++ P17.subT.bus)
def preO : List V.Item := preR ++ P17.ringPart

/-- The six segments. -/
def segC (ws : List Word) : List V.Val := segAt ws [] P17.commitPart
def segT (ws : List Word) : List V.Val := segAt ws preT P17.treePart
def segS (ws : List Word) : List V.Val := segAt ws preS P17.spongePart
def segY (ws : List Word) : List V.Val := segAt ws preY (P17.subT.typed ++ P17.subT.bus)
def segR (ws : List Word) : List V.Val := segAt ws preR P17.ringPart
def segO (ws : List Word) : List V.Val := segAt ws preO P17.openPart

/-- `accOf`'s values are the walk's from `ns0` (any shape). -/
theorem accOf_segV (sh : Shape) (π : ByteArray) (tr : Trace) :
    ((accOf sh π tr).map (V.NV.val π)).reverse = segV π sh.levs tr (sched6 sh) (ns0 sh (aOf tr 1), 2) := rfl

theorem stAt_append (ws : List Word) (pre part : List V.Item) :
    stAt ws (pre ++ part) = nxt πW P17.levs τW part (stAt ws pre) :=
  nxt_append _ _ _ pre part _

/-- **`hsplit`**: V1's values are the six segments. -/
theorem split_acc (ws : List Word) :
    ((accOf P17 πW τW).map (V.NV.val πW)).reverse =
      segC ws ++ (segT ws ++ (segS ws ++ (segY ws ++ (segR ws ++ segO ws)))) := by
  have e0 : ((accOf P17 πW τW).map (V.NV.val πW)).reverse = segV πW P17.levs τW (sched6 P17) (stAt ws []) :=
    accOf_segV P17 πW τW
  have hT : nxt πW P17.levs τW P17.commitPart (stAt ws []) = stAt ws preT := by rw [← stAt_append]; rfl
  have hS : nxt πW P17.levs τW P17.treePart (stAt ws preT) = stAt ws preS := (stAt_append ws preT _).symm
  have hY : nxt πW P17.levs τW P17.spongePart (stAt ws preS) = stAt ws preY := (stAt_append ws preS _).symm
  have hR : nxt πW P17.levs τW (P17.subT.typed ++ P17.subT.bus) (stAt ws preY) = stAt ws preR :=
    (stAt_append ws preY _).symm
  have hO : nxt πW P17.levs τW P17.ringPart (stAt ws preR) = stAt ws preO := (stAt_append ws preR _).symm
  have es : sched6 P17 = P17.commitPart ++ (P17.treePart ++ (P17.spongePart ++
      ((P17.subT.typed ++ P17.subT.bus) ++ (P17.ringPart ++ P17.openPart)))) := by
    simp only [sched6, List.append_assoc]
  rw [e0, es, segV_append πW P17.levs τW P17.commitPart, segV_append πW P17.levs τW P17.treePart,
    segV_append πW P17.levs τW P17.spongePart, segV_append πW P17.levs τW (P17.subT.typed ++ P17.subT.bus),
    segV_append πW P17.levs τW P17.ringPart, hT, hS, hY, hR, hO]
  rfl

/-! ## Static facts at `P17` -/

/-- Every item of the tree, sponge, typed and bus parts is plain (one table, by the kernel). -/
theorem plain17 : (P17.treePart ++ P17.spongePart ++ (P17.subT.typed ++ P17.subT.bus)).all plainB = true := by
  decide +kernel

/-- CD's typed items are `P17`'s (one table, by the kernel). -/
theorem tyItems_P17 : Lvm6.QD.tyItems ++ Lvm6.QD.mbItems = P17.subT.typed ++ P17.subT.bus := by
  decide +kernel

theorem spItems_P17 : spItems 13 ++ linkItems 13 = P17.spongePart := rfl

theorem plain_of {part : List V.Item} (h : ∀ it ∈ part, it ∈ P17.treePart ++ P17.spongePart ++
    (P17.subT.typed ++ P17.subT.bus)) : ∀ it ∈ part, plainB it = true :=
  fun it hit ↦ List.all_eq_true.mp plain17 it (h it hit)

theorem commitPart_eq : P17.commitPart = [.cap 0, .B, .G (P17.lvl 0).gOod, .D (P17.M - 1), .E 1] := rfl

theorem queriesOf_append (L : List V.Lev) (a b : List V.Item) :
    V.queriesOf L (a ++ b) = V.queriesOf L a + V.queriesOf L b := by
  simp [V.queriesOf]

theorem pendL_append (L : List V.Lev) : ∀ (a b : List V.Item) (n : ℕ),
    pendL L (a ++ b) n = pendL L b (pendL L a n)
  | [], _, _ => rfl
  | it :: a, b, n => by
    rw [List.cons_append, pendL_cons, pendL_append L a b, pendL_cons L it a]

/-! ## The simulation along `sched6 P17` -/

section P17

variable {ws : List Word} (hw : hashedLen6 P6 ≤ 8 * ws.length) {M : Lvm.Loop.Mem}
  (hM : ∀ j < ws.length, M.k j = laneK ws j) (hpow : PowLanes6 P6 ws)

/-- The CA items of a part. -/
abbrev its17 (part : List V.Item) : List It := part.flatMap (itOfs (lvOf P17))

/-- The CA state `w` sits after the items `pre`: lane `partLane pre`. -/
def AtPre (pre : List V.Item) (w : WS6) : Prop :=
  w.i = 2 + V.queriesOf P17.levs pre ∧ w.pend / 8 = pendL P17.levs pre 0

theorem laneW_of_at {pre : List V.Item} {w : WS6} (h : AtPre pre w) : laneW P6 w = partLane pre := by
  rw [laneW, partLane, h.1, h.2]

/-- `1 < n + 1 + 1` at a variable `n` (KDN: `omega` on the closed `(walk …).1.length` made the kernel run the walk). -/
theorem one_lt_add_one_add_one (n : ℕ) : 1 < n + 1 + 1 := by omega

/-- The walk's entry at a ground draw, at variables (KDN: `hc6` and `claim0At` rewrite with it; their former
`change` to `⟨.fs _ g, _⟩ :: _` was checked by the kernel by running the walk over the whole schedule). -/
theorem walk_G_append (lv : ℕ → Lv) (w : WS6) (g : ℕ) (R : List It) :
    (walk lv w (itOfs lv (.G g) ++ R)).1 = ⟨.fs w.st g, 40 + w.pend⟩ :: (walk lv (walkIt lv w (.G g)).2 R).1 :=
  rfl

include hw in
/-- The simulation at the start (entry 2, the cursor after `HDR`). -/
theorem inv0 : Inv P6 ws (lvOf P17) w06 (st0 ws) (its17 (sched6 P17)) := by
  have hP : 1 < P6.length := by
    show 1 < (planOf P17).length
    rw [planOf, List.length_cons, List.length_cons]
    exact one_lt_add_one_add_one _
  have hb := contrib_len (P := P6) (ws := ws) hw (n := 1) hP (st := 0) (g := 0) (len := Lvm6.seedLen P17) rfl
  have hb1 : (bodyTo τW P6 1).length = 0 := by
    rw [show (1 : ℕ) = 0 + 1 from rfl, bodyTo_succ]; rfl
  have hok := planOf_P17.1
  simp only [walkOK, Bool.and_eq_true, beq_iff_eq] at hok
  refine ⟨rfl, le_rfl, ?_, rfl, rfl, hok.1.1, hok.1.2⟩
  show Lvm6.hdrLen P17 = (bodyTo τW P6 (1 + 1)).length + 0
  rw [hb, hb1]
  simp only [Lvm6.seedLen]
  omega

/-- Level 0's cap: V1's cap size and CA's agree (`levOK`). -/
theorem cap0 : V.capOfL P17.levs (P17.levs.getD 0 default).ht (P17.levs.getD 0 default).wd = (lvOf P17 0).lv := by
  have h := simOK_P17
  simp only [simOK, Bool.and_eq_true] at h
  exact (levOK_get h.1.2 (i := 0) (by decide)).2.1

theorem lv0 : (lvOf P17 0).lv = (P17.levs.getD 0 default).lv := rfl

include hw hM hpow in
/-- **The commitment part**: the simulation after it, and its ground draw's plan entry. -/
theorem sim_commit {R : List It} (h : Inv P6 ws (lvOf P17) w06 (st0 ws) (its17 P17.commitPart ++ R)) :
    ∃ w, Inv P6 ws (lvOf P17) w (stAt ws P17.commitPart) R ∧ AtPre P17.commitPart w := by
  rw [commitPart_eq] at h ⊢
  simp only [its17, List.flatMap_cons, List.flatMap_nil, List.append_nil, List.append_assoc] at h
  obtain ⟨i1, -, hi1, hp1⟩ := sim_cap (lvOf P17) P17.levs 0 cap0 h
  rw [List.flatMap_singleton] at i1 hi1 hp1
  have h1 : Inv P6 ws (lvOf P17) (walk (lvOf P17) w06 (itOfs (lvOf P17) (.cap 0))).2
      (nxt πW P17.levs τW [.cap 0] (st0 ws))
      (its17 [.B, .G (P17.lvl 0).gOod, .D (P17.M - 1), .E 1] ++ R) := by
    simpa only [its17, List.flatMap_cons, List.flatMap_nil, List.append_nil, List.append_assoc] using i1
  obtain ⟨i2, -, -, -, -, q2, d2⟩ := simPart (lvOf P17) P17.levs streamOkP17 hw hM hpow _
    (by intro it hit; simp only [List.mem_cons, List.not_mem_nil, or_false] at hit
        rcases hit with rfl | rfl | rfl | rfl <;> rfl) h1
  refine ⟨(walk (lvOf P17) (walk (lvOf P17) w06 (itOfs (lvOf P17) (.cap 0))).2
    ([V.Item.B, .G (P17.lvl 0).gOod, .D (P17.M - 1), .E 1].flatMap (itOfs (lvOf P17)))).2, ?_, ?_, ?_⟩
  · rw [stAt, nxt_cons]; exact i2
  · rw [q2, hi1, queriesOf_cons P17.levs (.cap 0)]
    show 2 + _ = 2 + (0 + _); rw [Nat.zero_add]
  · rw [d2, hp1, pendL_cons P17.levs (.cap 0), lv0]
    congr 1

include hw hM hpow in
/-- **One plain part** after `pre`. -/
theorem sim_part {pre part : List V.Item} (hp : ∀ it ∈ part, plainB it = true) {w : WS6} {R : List It}
    (h : Inv P6 ws (lvOf P17) w (stAt ws pre) (its17 part ++ R)) (ha : AtPre pre w) :
    ∃ w', Inv P6 ws (lvOf P17) w' (stAt ws (pre ++ part)) R ∧ AtPre (pre ++ part) w' ∧
      EvMatch M (layItems part (partLane pre)) ((segAt ws pre part).map toEv) ∧ NoRows (segAt ws pre part) ∧
      PowLay M (layItems part (partLane pre)) := by
  obtain ⟨i1, e1, n1, p1, -, q1, d1⟩ := simPart (lvOf P17) P17.levs streamOkP17 hw hM hpow part hp h
  rw [laneW_of_at ha] at e1 p1
  refine ⟨(walk (lvOf P17) w (part.flatMap (itOfs (lvOf P17)))).2, by rw [stAt_append]; exact i1, ⟨?_, ?_⟩,
    e1, n1, p1⟩
  · rw [q1, ha.1, queriesOf_append]; omega
  · rw [d1, ha.2, pendL_append]

include hw hM hpow in
/-- **Items (3) at `P17`**: the tree, sponge and typed segments match the circuit's slots, and the simulation
reaches the ring part. -/
theorem split6 :
    (PowLay M (layItems (treeItems 18) aTree) ∧ NoRows (segT ws) ∧
      EvMatch M (layItems (treeItems 18) aTree) ((segT ws).map toEv)) ∧
    (PowLay M (layItems (spItems 13 ++ linkItems 13) aSp) ∧ NoRows (segS ws) ∧
      EvMatch M (layItems (spItems 13 ++ linkItems 13) aSp) ((segS ws).map toEv)) ∧
    (PowLay M (layItems (Lvm6.QD.tyItems ++ Lvm6.QD.mbItems) aTy) ∧ NoRows (segY ws) ∧
      EvMatch M (layItems (Lvm6.QD.tyItems ++ Lvm6.QD.mbItems) aTy) ((segY ws).map toEv)) ∧
    ∃ w, Inv P6 ws (lvOf P17) w (stAt ws preR) (its17 (P17.ringPart ++ P17.openPart)) ∧ laneW P6 w = partLane preR := by
  have h0 := inv0 hw
  have es : its17 (sched6 P17) = its17 P17.commitPart ++ (its17 P17.treePart ++ (its17 P17.spongePart ++
      (its17 (P17.subT.typed ++ P17.subT.bus) ++ its17 (P17.ringPart ++ P17.openPart)))) := by
    simp only [its17, sched6, List.flatMap_append, List.append_assoc]
  rw [es] at h0
  obtain ⟨w1, i1, a1⟩ := sim_commit hw hM hpow h0
  have pl : ∀ it ∈ P17.treePart ++ P17.spongePart ++ (P17.subT.typed ++ P17.subT.bus), plainB it = true :=
    plain_of fun _ h ↦ h
  obtain ⟨w2, i2, a2, eT, nT, pT⟩ := sim_part hw hM hpow (pre := preT)
    (fun it h ↦ pl it (by simp [h])) i1 a1
  obtain ⟨w3, i3, a3, eS, nS, pS⟩ := sim_part hw hM hpow (pre := preS)
    (fun it h ↦ pl it (by simp [h])) i2 a2
  obtain ⟨w4, i4, a4, eY, nY, pY⟩ := sim_part hw hM hpow (pre := preY)
    (fun it h ↦ pl it (by simp [h])) i3 a3
  refine ⟨⟨?_, nT, ?_⟩, ⟨?_, nS, ?_⟩, ⟨?_, nY, ?_⟩, w4, i4, laneW_of_at a4⟩
  · rw [treeItems_P17]; exact pT
  · rw [treeItems_P17]; exact eT
  · rw [spItems_P17]; exact pS
  · rw [spItems_P17]; exact eS
  · rw [tyItems_P17]; exact pY
  · rw [tyItems_P17]; exact eY

end P17

/-! ## Item (2): the commitment phase -/

theorem afterV_drawN {α : Type} : ∀ (cs : List E) (f : List E → VerifierProgram α),
    afterV (Lvm6.drawN cs.length f) (cs.map V.Val.c) = afterV (f cs) []
  | [], _ => rfl
  | c :: cs, f => afterV_drawN cs fun cs' ↦ f (c :: cs')

/-- **`commit6` returns** on values of its kinds (a cap of level 0's shape, the bind, the nonce, the ground
draw `x0`, `M − 1` draws, a scalar) when the ground draw passes its grind. -/
theorem commit_after (sh : Shape) {vc : List V.Val} (x0 : E)
    (hp : LeanVM.Protocol.Verifier.powOK (sh.lvl 0).gOod x0)
    (h : ∃ (xB n y : E) (f : ℕ → E), vc = [.cap (sh.levs.getD 0 default).ht (sh.levs.getD 0 default).wd] ++
      ([.c xB] ++ ([.e n, .c x0] ++ (((List.range (sh.M - 1)).map f).map V.Val.c ++ [.e y])))) :
    ∃ c0, afterV (commit6 sh) vc = some (.ret c0) := by
  obtain ⟨xB, n, y, f, rfl⟩ := h
  have hcap : afterV (VerifierProgram.readCommitment (sh.levs.getD 0 default).ht (sh.levs.getD 0 default).wd)
      [.cap (sh.levs.getD 0 default).ht (sh.levs.getD 0 default).wd] = some (.ret ()) := by
    simp [afterV, VerifierProgram.readCommitment]
  have hsep : afterV e2Sep [.c xB] = some (.ret ()) := rfl
  have hgrp : afterV (grp6 (sh.lvl 0).gOod (sh.M - 1)) ([.e n, .c x0] ++ ((List.range (sh.M - 1)).map f).map V.Val.c) =
      some (.ret (e2OfE x0 :: ((List.range (sh.M - 1)).map f).map e2OfE)) := by
    have e := afterV_drawN ((List.range (sh.M - 1)).map f)
      (fun cs ↦ (VerifierProgram.ret (e2OfE x0 :: cs.map e2OfE) : VerifierProgram (List E2)))
    rw [List.length_map, List.length_range] at e
    show afterV (if LeanVM.Protocol.Verifier.powOK (sh.lvl 0).gOod x0 then
      Lvm6.drawN (sh.M - 1) (fun cs ↦ VerifierProgram.ret (e2OfE x0 :: cs.map e2OfE)) else .fail)
        (((List.range (sh.M - 1)).map f).map V.Val.c) = _
    simp only [hp, ↓reduceIte]
    rw [e]
    rfl
  have hread : afterV e2Read [.e y] = some (.ret (e2OfE y)) := rfl
  rw [show [V.Val.e n, .c x0] ++ (((List.range (sh.M - 1)).map f).map V.Val.c ++ [.e y]) =
    ([.e n, .c x0] ++ ((List.range (sh.M - 1)).map f).map V.Val.c) ++ ([.e y] ++ []) by simp]
  rw [commit6, afterV_bind_append _ hcap, afterV_bind_append _ hsep, afterV_bind_append _ hgrp,
    afterV_bind_append _ hread]
  exact ⟨_, rfl⟩

section P17c

variable {ws : List Word} (hw : hashedLen6 P6 ≤ 8 * ws.length) {M : Lvm.Loop.Mem}
  (hM : ∀ j < ws.length, M.k j = laneK ws j) (hpow : PowLanes6 P6 ws)

include hw hM hpow in
/-- **Item (2), `hc`**: the commitment phase returns on its segment. -/
theorem hc6 : ∃ c0, afterV (commit6 P17) (segC ws) = some (.ret c0) := by
  have h0 := inv0 hw
  have es : sched6 P17 = P17.commitPart ++ (P17.treePart ++ (P17.spongePart ++
      ((P17.subT.typed ++ P17.subT.bus) ++ (P17.ringPart ++ P17.openPart)))) := by
    simp only [sched6, List.append_assoc]
  rw [es, its17, List.flatMap_append, commitPart_eq] at h0
  simp only [List.flatMap_cons, List.flatMap_nil, List.append_assoc, List.append_nil] at h0
  obtain ⟨i1, -, -, -⟩ := sim_cap (lvOf P17) P17.levs 0 cap0 h0
  obtain ⟨⟨h2, -, -, -, hdrop, -, -⟩, -⟩ := sim_B (lvOf P17) P17.levs streamOkP17 hw hM i1
  rw [walk_G_append] at hdrop
  change P6.drop _ = _ at hdrop
  obtain ⟨hn, hg⟩ := getD_of_drop hdrop
  have hpo := powOK6_of_lanes streamOkP17 hw hpow _ hn _ _ (by rw [hg])
  have hp : LeanVM.Protocol.Verifier.powOK (P17.lvl 0).gOod (Lvm.FS.chalOf (aOf τW
      (nxt πW P17.levs τW [.B] (nxt πW P17.levs τW [.cap 0] (st0 ws))).2)) := by
    rw [h2]
    have := pw_of_powOK (by decide) hpo
    simp only [V.pw, decide_eq_true_eq, Lvm.VEq.answerBits_eq] at this
    exact this
  have hD : ∀ (t : AS) (k : ℕ), (List.range k).map (fun j ↦ V.NV.val πW (.draw (aOf τW (t.2 + j)))) =
      ((List.range k).map fun j ↦ Lvm.FS.chalOf (aOf τW (t.2 + j))).map V.Val.c := fun t k ↦ by
    rw [List.map_map]; rfl
  refine commit_after P17 _ hp ?_
  rw [show segC ws = segV πW P17.levs τW P17.commitPart (st0 ws) from rfl, commitPart_eq,
    segV_cons πW P17.levs τW (.cap 0), segV_cons πW P17.levs τW .B,
    segV_cons πW P17.levs τW (.G _), segV_cons πW P17.levs τW (.D _), (item_cap πW P17.levs τW 0 _).1,
    (item_B πW P17.levs τW _).1, (item_G πW P17.levs τW _ _).1, (item_D πW P17.levs τW _ _).1,
    (item_E πW P17.levs τW _ _).1, hD]
  exact ⟨_, _, _, _, rfl⟩

include hw hM hpow in
/-- **`dec_of_runs` with items (3) and (2) discharged**: what is left is the phase runs (`node6E_har`) and
CC's tail (item (1)) on the ring and opening segments `segR`, `segO`. -/
theorem dec_of_split {tyOf : Hdr → Lvm6.Ty.TyInst6}
    {ring : Shape → List SliceClaim → List StackClaim6 → VerifierProgram StackClaim6}
    {whir : Shape → StackClaim6 → VerifierProgram Bool} {vk : Digest}
    {L : Lvm.M3.Lay} (hL : L = Lvm6.Ty.L6)
    {Pt : K.TreeOut → Prop} {Ps : K.SpOut → Prop} {Pl : SP.LinkOut → Prop} {Py : Lvm6.Ty.OpenClaimsE → Prop}
    (hT : Runs M (layItems (treeItems 18) aTree) (K.treeProg 18) Pt)
    (hS : Runs M (layItems (spItems 13) aSp) (K.spCaller6 13) Ps)
    (hK : Runs M (layItems (linkItems 13) aLink) (ksLinkProgE2 13 10 (rowsBK2 3816 7567 8032)) Pl)
    (hY : Runs M (layItems (Lvm6.QD.tyItems ++ Lvm6.QD.mbItems) aTy)
      (Lvm6.Ty.typedProgE (tyOf (hdrOf6 πW)).Ti L (tyOf (hdrOf6 πW)).pw (tyOf (hdrOf6 πW)).acc) Py)
    (htail : ∀ c0, afterV (commit6 P17) (segC ws) = some (.ret c0) →
      ∀ ot os lk oy, Pt ot → Ps os → Pl lk → Py oy →
      let t := K.toS 18 (hdrOf6 πW).h ot; let s := SP.spS os lk; let ty := Lvm6.Ty.claimsOnStack oy
      [t.slices, s.slices].length + (stackedOf c0 t s ty).length ≤ P17.J₀ ∧
      ∃ cl, afterV (ring P17 [t.slices, s.slices] (stackedOf c0 t s ty)) (segR ws) = some (.ret cl) ∧
        afterV (whir P17 cl) (segO ws) = some (.ret true)) :
    F6 (phases6 (fun sh x ↦ Lvm6.Ty.typedPhase6 sh (tyOf x)) ring whir) P17 vk πW (accOf P17 πW τW) = true := by
  obtain ⟨⟨pT, nT, eT⟩, ⟨pS, nS, eS⟩, ⟨pY, nY, eY⟩, -⟩ := split6 hw hM hpow
  obtain ⟨c0, hc⟩ := hc6 hw hM hpow
  exact dec_of_runs hL hT hS hK hY (split_acc ws) pT nT eT pS nS eS pY nY eY hc (htail c0 hc)

end P17c

end Lvm6.Node.Split
