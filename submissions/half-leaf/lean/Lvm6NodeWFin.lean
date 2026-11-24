-- New for lvm6 (WP NODE3, item 1, last part). The weight cell of the final WHIR level composed (NODE §6a, CC8
-- second slice): `wBatchG` (level 0's batched stack claim), then `glueGW` for levels 0–3 at `P17`'s parameters,
-- then CC-8 at `finD` (`finHarE`) with that weight gadget.
import Lvm6QCFinB
import Lvm6QCFinE

/-!
# `wFinG` at `P17` (WP NODE3)

* **`wFinG_at`**: given one `ClaimAt Pre` gadget per stack claim, a cell holding `λ₀` and `MA 24` of the
  rotated batch (`wBatchHar`'s inputs), the four glue steps (`glueHarW`, levels `(ko, ℓ, t, h)` = `(17, 6, 110,
  20)`, `(13, 4, 45, 19)`, `(9, 4, 28, 18)`, `(5, 4, 21, 17)` of `ladD` at `P17`, `Ŵ` cells `ko + 2` per position
  from `valsGenW`) meet `WAt` of the glued weight on the memories where every level's rounds, interface and `Ŵ`
  cells are represented. The admissibility `wokE` of each level's weight is W1's `hglue_E`, from level 0's
  `⟨rfl, MA⟩`.
* **`finG_har`**: CC-8 at `finD` (`κ ℓ h kq t c = 2 4 16 2 18 8`) with that weight gadget: on those memories,
  where `σc` holds the claim, the final level returns `true`.

INT3 (padded `w₀`, `WAt` at `τ.length = w.1`): level 0's `wokE` is `MA_ofFn_getD` of `hma` (W1's `w₀` reads
`padD` of the point); `finHarE`'s `w.1 = κ` is `rfl` (the last glue's `κ' = 2`). Statements unchanged.
-/

set_option autoImplicit false

namespace Lvm6.QC

open LeanVM.Parameters LeanVM.Protocol.Compile LeanVM.Protocol.Verifier LeanVM.Protocol.Whir
open Lvm Lvm.Loop Lvm.Loop.Build Lvm.Q2 Lvm.Har Lvm.E2V Lvm6.QK
open Lvm6 (Item Level)

/-- The glued weight gadget of `P17` (levels 0–3 over `wBatchG`). -/
def wFinG (Gs : List (List C2 → Cell → BM C2)) (lc : C2) (rc0 rc1 rc2 rc3 : List RndC)
    (oc0 oc1 oc2 oc3 : TailOutC) (wss0 wss1 wss2 wss3 : List (List C2)) : List RndC → List C2 → Cell → BM C2 :=
  glueGW (glueGW (glueGW (glueGW (wBatchG Gs lc) rc0 oc0 wss0) rc1 oc1 wss1) rc2 oc2 wss2) rc3 oc3 wss3

/-- The glued weight of `P17` (W1's ladder: `wGlueE` per level over `w₀`). -/
noncomputable def wFin (lam : E2) (cs : List Ring.Claim) (rs0 rs1 rs2 rs3 : List (Whir.Rnd E2))
    (o0 : Whir.TailOut E2 17 110 (2 ^ 20)) (o1 : Whir.TailOut E2 13 45 (2 ^ 19))
    (o2 : Whir.TailOut E2 9 28 (2 ^ 18)) (o3 : Whir.TailOut E2 5 21 (2 ^ 17)) : Whir.WtE.Wt (0 + 4) :=
  Whir.wGlueE 2 4 5 21 17 (Whir.wFolds Whir.WtE 4 rs3
    (Whir.wGlueE 6 4 9 28 18 (Whir.wFolds Whir.WtE 4 rs2
      (Whir.wGlueE 10 4 13 45 19 (Whir.wFolds Whir.WtE 4 rs1
        (Whir.wGlueE 14 4 17 110 20 (Whir.wFolds Whir.WtE 6 rs0 (Whir.w₀ (Ring.batch lam cs))) o0)) o1)) o2)) o3

/-- What the four levels' cells represent. -/
def LevRep (M : Mem) (rc0 rc1 rc2 rc3 : List RndC) (rs0 rs1 rs2 rs3 : List (Whir.Rnd E2))
    (oc0 oc1 oc2 oc3 : TailOutC) (o0 : Whir.TailOut E2 17 110 (2 ^ 20)) (o1 : Whir.TailOut E2 13 45 (2 ^ 19))
    (o2 : Whir.TailOut E2 9 28 (2 ^ 18)) (o3 : Whir.TailOut E2 5 21 (2 ^ 17))
    (wss0 wss1 wss2 wss3 : List (List C2)) : Prop :=
  (RndsRep M rc0 rs0 ∧ TailRep M oc0 o0 ∧ WsRep M oc0.ps wss0 19) ∧
    (RndsRep M rc1 rs1 ∧ TailRep M oc1 o1 ∧ WsRep M oc1.ps wss1 15) ∧
    (RndsRep M rc2 rs2 ∧ TailRep M oc2 o2 ∧ WsRep M oc2.ps wss2 11) ∧
    (RndsRep M rc3 rs3 ∧ TailRep M oc3 o3 ∧ WsRep M oc3.ps wss3 7)

/-- **The final level's weight cell at `P17`**: `WAt` of the glued weight. -/
theorem wFinG_at (cs : List Ring.Claim) (Gs : List (List C2 → Cell → BM C2)) (lam : E2) (lc : C2)
    (Pre : Mem → Prop) (hGs : List.Forall₂ (fun G cl ↦ ClaimAt Pre cl G) Gs cs)
    (hlc : ∀ M, Pre M → ev2 M lc = lam)
    (hma : Whir.MA 24 (fun y ↦ (Ring.batch lam cs).1 (y.drop 6 ++ y.take 6)))
    (rc0 rc1 rc2 rc3 : List RndC) (rs0 rs1 rs2 rs3 : List (Whir.Rnd E2)) (oc0 oc1 oc2 oc3 : TailOutC)
    (o0 : Whir.TailOut E2 17 110 (2 ^ 20)) (o1 : Whir.TailOut E2 13 45 (2 ^ 19))
    (o2 : Whir.TailOut E2 9 28 (2 ^ 18)) (o3 : Whir.TailOut E2 5 21 (2 ^ 17))
    (wss0 wss1 wss2 wss3 : List (List C2))
    (hl0 : rs0.length = 6) (hl1 : rs1.length = 4) (hl2 : rs2.length = 4) (hl3 : rs3.length = 4) :
    WAt (fun M ↦ Pre M ∧ LevRep M rc0 rc1 rc2 rc3 rs0 rs1 rs2 rs3 oc0 oc1 oc2 oc3 o0 o1 o2 o3 wss0 wss1 wss2 wss3)
      (wFin lam cs rs0 rs1 rs2 rs3 o0 o1 o2 o3)
      (wFinG Gs lc rc0 rc1 rc2 rc3 oc0 oc1 oc2 oc3 wss0 wss1 wss2 wss3) := by
  have h0 := wBatchHar cs Gs lam lc Pre hGs hlc hma
  have hw0 : Whir.wokE 18 6 (Whir.w₀ (Ring.batch lam cs)) := ⟨rfl, MA_ofFn_getD 24 _ hma⟩
  have g0 := glueHarW 14 4 17 110 20 6 19 (by norm_num) (by norm_num) _ Pre _ hw0 h0 rc0 rs0 oc0 o0 wss0 hl0
  have hw1 := Whir.hglue_E (κ' := 14) (ℓ' := 4) (by norm_num) _ hw0 rs0 o0
  have g1 := glueHarW 10 4 13 45 19 4 15 (by norm_num) (by norm_num) _ _ _ hw1 g0 rc1 rs1 oc1 o1 wss1 hl1
  have hw2 := Whir.hglue_E (κ' := 10) (ℓ' := 4) (by norm_num) _ hw1 rs1 o1
  have g2 := glueHarW 6 4 9 28 18 4 11 (by norm_num) (by norm_num) _ _ _ hw2 g1 rc2 rs2 oc2 o2 wss2 hl2
  have hw3 := Whir.hglue_E (κ' := 6) (ℓ' := 4) (by norm_num) _ hw2 rs2 o2
  have g3 := glueHarW 2 4 5 21 17 4 7 (by norm_num) (by norm_num) _ _ _ hw3 g2 rc3 rs3 oc3 o3 wss3 hl3
  intro c M hP
  exact g3 c M ⟨⟨⟨⟨hP.1, hP.2.1⟩, hP.2.2.1⟩, hP.2.2.2.1⟩, hP.2.2.2.2⟩

/-- **CC-8 at `finD` with the glued weight cell**: the final level's generator re-executes `finP` at
`finE2 2 4 16 2 18 8`, and on memories with `Pre` and the levels' representations where `σc` holds `σ`, it
returns `true`. -/
theorem finG_har (B : ℕ) (cs : List Ring.Claim) (Gs : List (List C2 → Cell → BM C2)) (lam : E2) (lc : C2)
    (Pre : Mem → Prop) (hGs : List.Forall₂ (fun G cl ↦ ClaimAt Pre cl G) Gs cs)
    (hlc : ∀ M, Pre M → ev2 M lc = lam)
    (hma : Whir.MA 24 (fun y ↦ (Ring.batch lam cs).1 (y.drop 6 ++ y.take 6)))
    (rc0 rc1 rc2 rc3 : List RndC) (rs0 rs1 rs2 rs3 : List (Whir.Rnd E2)) (oc0 oc1 oc2 oc3 : TailOutC)
    (o0 : Whir.TailOut E2 17 110 (2 ^ 20)) (o1 : Whir.TailOut E2 13 45 (2 ^ 19))
    (o2 : Whir.TailOut E2 9 28 (2 ^ 18)) (o3 : Whir.TailOut E2 5 21 (2 ^ 17))
    (wss0 wss1 wss2 wss3 : List (List C2))
    (hl0 : rs0.length = 6) (hl1 : rs1.length = 4) (hl2 : rs2.length = 4) (hl3 : rs3.length = 4)
    (g gq gT i : ℕ) (hg : g ≤ 64) (hgq : gq ≤ 64) (hgT : gT ≤ 64) (lev : Level) (wdI a : ℕ) (σ : E2) (σc : C2)
    (gate : Cell) :
    HarO gate (finGen (2 ^ 2 + 4) 18 (posGen B 16 8 2 18) (fun rc ↦ fvGen 16 4 2 rc) (fpGen 2 4)
        (wFinG Gs lc rc0 rc1 rc2 rc3 oc0 oc1 oc2 oc3 wss0 wss1 wss2 wss3) g gT 2 4 lev wdI a σc gate)
      (Whir.finP Whir.WtE Whir.chalE2 (Whir.finE2 2 4 16 2 18 8 (by norm_num) (by norm_num) (by norm_num)
          (by norm_num) (by norm_num) (by norm_num) (by norm_num)) g gq i 4
        (Whir.fvE false 16 4 (by norm_num)) (Whir.chkE gT 2) (wFin lam cs rs0 rs1 rs2 rs3 o0 o1 o2 o3) σ)
      (layFin (2 ^ 2 + 4) 2 18 2 lev wdI g gq gT 4 a)
      fun M _ out ↦ (Pre M ∧ LevRep M rc0 rc1 rc2 rc3 rs0 rs1 rs2 rs3 oc0 oc1 oc2 oc3 o0 o1 o2 o3 wss0 wss1 wss2
        wss3) → ev2 M σc = σ → out = true :=
  finHarE B 2 4 16 2 18 8 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) _ _ _ (wFinG_at cs Gs lam lc Pre hGs hlc hma rc0 rc1 rc2 rc3 rs0 rs1 rs2 rs3 oc0 oc1 oc2 oc3
      o0 o1 o2 o3 wss0 wss1 wss2 wss3 hl0 hl1 hl2 hl3) rfl g gq gT i hg hgq hgT lev wdI a σ σc gate

end Lvm6.QC
