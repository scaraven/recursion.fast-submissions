-- New for lvm6 (WP NODE5a). Claim 0 at the cells (`Claim0At`): the commitment's claim `q̃(z₀) = y₀` has the point of
-- `z₀`'s cells and the value of `y₀`'s cell, from N4-split's simulation of the commitment part.
import Lvm6NodeFinC

/-!
# Claim 0 at the cells (WP NODE5a)

* **`commit_ret`**: `commit_after` with the returned claim: `(eq(z₀, ·), y₀)` of the values' draws and scalar.
* **`claim0At`** (`hw hM hpow`): every claim `c0` the commitment returns on its segment is `Claim0At M c0`: the
  simulation (`inv0`, `sim_cap`, `sim_part` on `[B]`, `[G, D]`, `[E]`) matches the `G`/`D` draws and the `E`
  scalar with the stream cells at `partLane` (`EvMatch`), which are `inp18`'s `z₀`, `y₀` cells (`inp18_lanes`).
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

/-- **`commit6`'s claim** on values of its kinds: `(eq(z₀, ·), y₀)`, `z₀` the ground draw and the `M − 1` draws. -/
theorem commit_ret (sh : Shape) (xB n x0 y : E) (f : ℕ → E)
    (hp : LeanVM.Protocol.Verifier.powOK (sh.lvl 0).gOod x0) :
    afterV (commit6 sh) ([.cap (sh.levs.getD 0 default).ht (sh.levs.getD 0 default).wd] ++
      ([.c xB] ++ ([.e n, .c x0] ++ (((List.range (sh.M - 1)).map f).map V.Val.c ++ [.e y])))) =
      some (.ret ((fun pt ↦ eqPt (e2OfE x0 :: ((List.range (sh.M - 1)).map f).map e2OfE) pt), e2OfE y)) := by
  have hcap : afterV (VerifierProgram.readCommitment (sh.levs.getD 0 default).ht (sh.levs.getD 0 default).wd)
      [.cap (sh.levs.getD 0 default).ht (sh.levs.getD 0 default).wd] = some (.ret ()) := by
    simp [afterV, VerifierProgram.readCommitment]
  have hsep : afterV e2Sep [.c xB] = some (.ret ()) := rfl
  have hgrp : afterV (grp6 (sh.lvl 0).gOod (sh.M - 1))
      ([.e n, .c x0] ++ ((List.range (sh.M - 1)).map f).map V.Val.c) =
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
  rfl

theorem forall₂_map_map_of {α β γ : Type} {R : β → γ → Prop} {l : List α} {f : α → β} {g : α → γ}
    (h : List.Forall₂ R (l.map f) (l.map g)) : ∀ a ∈ l, R (f a) (g a) := by
  rw [List.forall₂_map_left_iff, List.forall₂_map_right_iff, List.forall₂_same] at h
  exact h

section Z

variable {ws : List Word} (hw : hashedLen6 P6 ≤ 8 * ws.length) {M : Lvm.Loop.Mem}
  (hM : ∀ j < ws.length, M.k j = laneK ws j) (hpow : PowLanes6 P6 ws)

include hw hM hpow in
/-- **Claim 0 is `z₀`'s and `y₀`'s cells.** -/
theorem claim0At : ∀ c0, afterV (commit6 P18) (segC ws) = some (.ret c0) → Fin.Claim0At M c0 := by
  intro c0 hc
  -- the commitment segment by parts
  have t1 : nxt πW P18.levs τW [.cap 0] (stAt ws []) = stAt ws [.cap 0] := (stAt_append ws [] [.cap 0]).symm
  have t2 : nxt πW P18.levs τW [.B] (stAt ws [.cap 0]) = stAt ws [.cap 0, .B] :=
    (stAt_append ws [.cap 0] [.B]).symm
  have t3 : nxt πW P18.levs τW [.G (P18.lvl 0).gOod, .D (P18.M - 1)] (stAt ws [.cap 0, .B]) =
      stAt ws [.cap 0, .B, .G (P18.lvl 0).gOod, .D (P18.M - 1)] :=
    (stAt_append ws [.cap 0, .B] [.G (P18.lvl 0).gOod, .D (P18.M - 1)]).symm
  have eS : segC ws = segV πW P18.levs τW [.cap 0] (stAt ws []) ++
      (segV πW P18.levs τW [.B] (stAt ws [.cap 0]) ++
        (segV πW P18.levs τW [.G (P18.lvl 0).gOod, .D (P18.M - 1)] (stAt ws [.cap 0, .B]) ++
          segV πW P18.levs τW [.E 1] (stAt ws [.cap 0, .B, .G (P18.lvl 0).gOod, .D (P18.M - 1)]))) := by
    rw [show segC ws = segV πW P18.levs τW ([.cap 0] ++ ([.B] ++ ([.G (P18.lvl 0).gOod, .D (P18.M - 1)] ++
      [.E 1]))) (stAt ws []) by rw [segC, segAt, commitPart_eq]; rfl]
    rw [segV_append, segV_append, segV_append, t1, t2, t3]
  have v3 : segV πW P18.levs τW [.G (P18.lvl 0).gOod, .D (P18.M - 1)] (stAt ws [.cap 0, .B]) =
      [V.NV.val πW (.rd (stAt ws [.cap 0, .B]).1.off 8), V.NV.val πW (.draw (aOf τW (stAt ws [.cap 0, .B]).2))] ++
        (List.range (P18.M - 1)).map (fun j ↦ V.NV.val πW (.draw (aOf τW ((stAt ws [.cap 0, .B]).2 + 1 + j)))) := by
    rw [segV_cons, (item_G πW P18.levs τW _ (stAt ws [.cap 0, .B])).1, (item_D πW P18.levs τW _ _).1, (item_G πW P18.levs τW _ (stAt ws [.cap 0, .B])).2.2]
  have v4 : segV πW P18.levs τW [.E 1] (stAt ws [.cap 0, .B, .G (P18.lvl 0).gOod, .D (P18.M - 1)]) = [V.NV.val πW (.rd (stAt ws [.cap 0, .B, .G (P18.lvl 0).gOod, .D (P18.M - 1)]).1.off 16)] := by
    rw [(item_E πW P18.levs τW 1 (stAt ws [.cap 0, .B, .G (P18.lvl 0).gOod, .D (P18.M - 1)])).1]
    rfl
  obtain ⟨n', hn'⟩ : ∃ e : E, V.NV.val πW (.rd (stAt ws [.cap 0, .B]).1.off 8) = .e e := ⟨_, rfl⟩
  obtain ⟨y', hy'⟩ : ∃ e : E, V.NV.val πW (.rd (stAt ws [.cap 0, .B, .G (P18.lvl 0).gOod, .D (P18.M - 1)]).1.off 16) = .e e := ⟨_, rfl⟩
  -- the ground draw's grind (as `hc6`)
  have hp : LeanVM.Protocol.Verifier.powOK (P18.lvl 0).gOod (Lvm.FS.chalOf (aOf τW (stAt ws [.cap 0, .B]).2)) := by
    have h0 := inv0 hw
    have es : sched6 P18 = P18.commitPart ++ (P18.treePart ++ (P18.spongePart ++
        ((P18.subT.typed ++ P18.subT.bus) ++ (P18.ringPart ++ P18.openPart)))) := by
      simp only [sched6, List.append_assoc]
    rw [es, its18, List.flatMap_append, commitPart_eq] at h0
    simp only [List.flatMap_cons, List.flatMap_nil, List.append_assoc, List.append_nil] at h0
    obtain ⟨i1, -, -, -⟩ := sim_cap (lvOf P18) P18.levs 0 cap0 h0
    obtain ⟨⟨h2, -, -, -, hdrop, -, -⟩, -⟩ := sim_B (lvOf P18) P18.levs streamOkP18 hw hM i1
    rw [walk_G_append] at hdrop
    change P6.drop _ = _ at hdrop
    obtain ⟨hn, hg⟩ := getD_of_drop hdrop
    have hpo := powOK6_of_lanes streamOkP18 hw hpow _ hn _ _ (by rw [hg])
    rw [show stAt ws [.cap 0, .B] = nxt πW P18.levs τW [.B] (nxt πW P18.levs τW [.cap 0] (st0 ws)) from
      nxt_cons πW P18.levs τW (.cap 0) [.B] (st0 ws), h2]
    have := pw_of_powOK (by decide) hpo
    simp only [V.pw, decide_eq_true_eq, Lvm.VEq.answerBits_eq] at this
    exact this
  -- the claim
  have hret := commit_ret P18 (Lvm.FS.chalOf (aOf τW (stAt ws [.cap 0]).2)) n' (Lvm.FS.chalOf (aOf τW (stAt ws [.cap 0, .B]).2)) y'
    (fun j ↦ Lvm.FS.chalOf (aOf τW ((stAt ws [.cap 0, .B]).2 + 1 + j))) hp
  have eL : segC ws = [.cap (P18.levs.getD 0 default).ht (P18.levs.getD 0 default).wd] ++
      ([.c (Lvm.FS.chalOf (aOf τW (stAt ws [.cap 0]).2))] ++ ([.e n', .c (Lvm.FS.chalOf (aOf τW (stAt ws [.cap 0, .B]).2))] ++
        (((List.range (P18.M - 1)).map fun j ↦ Lvm.FS.chalOf (aOf τW ((stAt ws [.cap 0, .B]).2 + 1 + j))).map V.Val.c ++ [.e y']))) := by
    rw [eS, (item_cap πW P18.levs τW 0 _).1, (item_B πW P18.levs τW _).1, v3, v4, hn', hy', List.map_map]
    simp only [List.cons_append, List.nil_append, List.append_assoc]
    rfl
  rw [eL, hret] at hc
  obtain rfl : _ = c0 := VerifierProgram.ret.inj (Option.some.inj hc)
  -- the simulation's events
  have h0' : Inv P6 ws (lvOf P18) w06 (st0 ws) (itOfs (lvOf P18) (.cap 0) ++ (its18 [.B] ++
      (its18 [.G (P18.lvl 0).gOod, .D (P18.M - 1)] ++ (its18 [.E 1] ++ its18 (P18.treePart ++ (P18.spongePart ++
        ((P18.subT.typed ++ P18.subT.bus) ++ (P18.ringPart ++ P18.openPart)))))))) := by
    have h0 := inv0 hw
    have es : sched6 P18 = [.cap 0] ++ ([.B] ++ ([.G (P18.lvl 0).gOod, .D (P18.M - 1)] ++ ([.E 1] ++
        (P18.treePart ++ (P18.spongePart ++ ((P18.subT.typed ++ P18.subT.bus) ++
          (P18.ringPart ++ P18.openPart))))))) := by
      rw [show sched6 P18 = P18.commitPart ++ (P18.treePart ++ (P18.spongePart ++
        ((P18.subT.typed ++ P18.subT.bus) ++ (P18.ringPart ++ P18.openPart)))) by
          simp only [sched6, List.append_assoc], commitPart_eq]
      rfl
    rw [es] at h0
    simpa only [its18, List.flatMap_append, List.flatMap_singleton] using h0
  obtain ⟨i1, -, hi1, hp1⟩ := sim_cap (lvOf P18) P18.levs 0 cap0 h0'
  have a1 : AtPre [.cap 0] (walk (lvOf P18) w06 ([V.Item.cap 0].flatMap (itOfs (lvOf P18)))).2 := by
    refine ⟨?_, ?_⟩
    · rw [hi1, queriesOf_cons P18.levs (.cap 0)]
      rfl
    · rw [hp1, lv0]
      show (0 + 32 * 2 ^ (P18.levs.getD 0 default).lv) / 8 = 0 + 4 * 2 ^ (P18.levs.getD 0 default).lv
      omega
  obtain ⟨w2, i2, a2, -, -, -⟩ := sim_part hw hM hpow (pre := [.cap 0]) (part := [.B])
    (by intro it h; simp only [List.mem_singleton] at h; subst h; rfl) i1 a1
  obtain ⟨w3, i3, a3, eGD, -, -⟩ := sim_part hw hM hpow (pre := [.cap 0] ++ [.B])
    (part := [.G (P18.lvl 0).gOod, .D (P18.M - 1)])
    (by intro it h; simp only [List.mem_cons, List.not_mem_nil, or_false] at h; rcases h with rfl | rfl <;> rfl) i2 a2
  clear i1 a1 i2 a2 h0' hi1 hp1
  have i3' : Inv P6 ws (lvOf P18) w3 (stAt ws [.cap 0, .B, .G (P18.lvl 0).gOod, .D (P18.M - 1)])
      (its18 [.E 1] ++ its18 (P18.treePart ++ (P18.spongePart ++
        ((P18.subT.typed ++ P18.subT.bus) ++ (P18.ringPart ++ P18.openPart))))) := i3
  have a3' : AtPre [.cap 0, .B, .G (P18.lvl 0).gOod, .D (P18.M - 1)] w3 := a3
  clear i3 a3
  have hE := sim_part hw hM hpow (part := [.E 1]) (fun it h ↦ by rw [List.mem_singleton.mp h]; rfl) i3' a3'
  obtain ⟨_, _, _, eE, _, _⟩ := hE
  have hl2 : P18.commitPart.take iOodG = [.cap 0, .B] := by rw [commitPart_eq]; rfl
  have hl4 : P18.commitPart.take iY0 = [.cap 0, .B, .G (P18.lvl 0).gOod, .D (P18.M - 1)] := by
    rw [commitPart_eq]; rfl
  have eGD' := eGD
  have eE' := eE
  simp only [segAt, List.singleton_append, List.cons_append, List.nil_append] at eGD' eE'
  rw [v3, hn'] at eGD'
  rw [v4, hy'] at eE'
  simp only [layItems, List.append_nil, List.map_append, List.map_cons, List.map_nil, List.map_map,
    List.cons_append, List.nil_append, List.forall₂_cons, EvMatch, List.range_one, Nat.mul_zero,
    Nat.add_zero] at eGD' eE'
  obtain ⟨-, hx0, hD⟩ := eGD'
  have hD' := forall₂_map_map_of hD
  obtain ⟨hy0, -⟩ := eE'
  refine ⟨fun X ↦ ?_, ?_⟩
  · show eqPt (Dep.inp18.z0.map (ev2 M)) X = eqPt _ X
    refine congrArg (fun z ↦ eqPt z X) ?_
    rw [inp18_lanes.z0, hl2, show List.range P18.M = List.range ((P18.M - 1) + 1) from rfl,
      List.range_succ_eq_map, List.map_cons,
      List.map_cons, List.map_map, List.map_map, List.map_map]
    refine congrArg₂ List.cons ?_ (List.map_congr_left fun j hj ↦ ?_)
    · obtain ⟨l0, l1, -⟩ := hx0
      show ev2 M (ld2 (partLane [.cap 0, .B] + 1)) = _
      rw [ev2_ld2, e2OfE, l0, l1]
    · obtain ⟨l0, l1, -⟩ := hD' j hj
      simp only [Function.comp_apply, QC.ansAt, Nat.succ_ne_zero, ↓reduceIte, Nat.add_sub_cancel]
      rw [ev2_ld2, e2OfE, l0, l1, Nat.succ_sub_one]
  · have hy0' : e2OfE y' = ev2 M (ld2 (partLane [.cap 0, .B, .G (P18.lvl 0).gOod, .D (P18.M - 1)])) := hy0
    show [e2OfE y'] = Dep.inp18.y0.map (ev2 M)
    rw [inp18_lanes.y0, hl4, List.map_cons, List.map_nil, hy0']

end Z

end Lvm6.Node.Split
