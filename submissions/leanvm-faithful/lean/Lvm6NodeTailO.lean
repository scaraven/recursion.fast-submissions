-- New for lvm6 (WP N4-tail). The opening of `dec_of_runs`'s `htail`: `whirP18` runs on the CC levels' slots
-- (CC-4 `levelHarW` per mid level, the claim chain `claimGlueHar`, NODE3's `finG18_har`), and returns `true`
-- on V1's values (`afterV`) when their openings carry `F18`; then `htail` itself.
import Lvm6NodeTail
import Lvm6NodeTailW
import Lvm6NodeWFin
import Lvm6NodeDeploy

/-!
# The opening and `htail` (WP N4-tail)

* `ladP_mid_eq`: a ladder level is `levelP` (CC-4's program) followed by the rest.
* **`fin_hsA`**: NODE3's `finG18_har` at a memory, for every round and interface output at once.
* **`whir_runsO`**: `whirP18 (batch λ cs)` runs on `lay₀ ++ … ++ lay₃ ++ layF` to `true`, from the four
  levels' runs (their `LevelRep`/`WsRep`), the claim chain's cells (`claimGlueHar`'s conclusion), the value
  cell of the ring phase holding the claim's value, and the final level's run.
* **`whir_afterV`**: on V1's values matching those slots, whose openings carry `F18` (`RowsF`), the opening
  returns `true` (`afterV_of_runsO_q`, `qAgree_whirP18`).
* **`htail_of_cc`**: `dec_of_runs`'s `htail` (`J₀`, ring, opening) at the represented outputs.
-/

set_option autoImplicit false

namespace Lvm6.Node

open RecursionFast Lvm6.Q Lvm.Replay
open LeanVM.Protocol.Compile hiding Proof Bytes Word
open Lvm Lvm.Loop Lvm.Loop.Build Lvm.Q2 Lvm.Har Lvm.E2V
open Lvm6.QK
open LeanVM.Parameters

/-! ## A level as `levelP` -/

theorem bind_pair {α β γ : Type} (p : VerifierProgram α) (q : α → VerifierProgram β)
    (k : α × β → VerifierProgram γ) :
    (p >>= fun a ↦ q a >>= fun b ↦ pure (a, b)) >>= k = p >>= fun a ↦ q a >>= fun b ↦ k (a, b) := by
  show (p.bind _).bind k = p.bind _
  rw [VerifierProgram.bind_assoc]
  congr 1
  funext a
  show ((q a).bind _).bind k = (q a).bind _
  rw [VerifierProgram.bind_assoc]
  rfl

theorem ladP_mid_eq {n ℓ n' ℓ' : ℕ} (M : Whir.MidLv E2 Whir.WtE n ℓ n' ℓ') (rest : Whir.Lad E2 Whir.WtE n' ℓ')
    (w : Whir.WtE.Wt (0 + ℓ)) (σ : E2) :
    Whir.ladP Whir.chalE2 (.mid M rest) w σ =
      Whir.levelP Whir.chalE2 M.L M.g M.gO M.gQ M.ht M.wd M.i ℓ M.vals >>= fun ro ↦
        Whir.ladP Whir.chalE2 rest (M.wGlue (Whir.wFolds Whir.WtE ℓ ro.1 w) ro.2)
          (Whir.gluedC (Whir.foldsC ℓ ro.1 σ) ro.2.y ro.2.lam ro.2.c) := by
  rw [Whir.ladP, Whir.levelP]
  exact (bind_pair (Whir.roundsP Whir.chalE2 M.g ℓ)
    (fun rs ↦ Whir.tailP M.L Whir.chalE2 M.ht M.wd M.i M.gO M.gQ (M.vals rs))
    (fun ro ↦ Whir.ladP Whir.chalE2 rest (M.wGlue (Whir.wFolds Whir.WtE ℓ ro.1 w) ro.2)
      (Whir.gluedC (Whir.foldsC ℓ ro.1 σ) ro.2.y ro.2.lam ro.2.c))).symm

/-- `fin18`'s step of the ladder is CC-8's program at `finE2 3 4 17 2 18 7`. -/
theorem ladP_fin18 (w : Whir.WtE.Wt (0 + 4)) (σ : E2) :
    Whir.ladP Whir.chalE2 (.fin Whir.fin18) w σ =
      Whir.finP Whir.WtE Whir.chalE2 (Whir.finE2 3 4 17 2 18 7 (by norm_num) (by norm_num) (by norm_num)
          (by norm_num) (by norm_num) (by norm_num) (by norm_num)) 10 13 4 4
        (Whir.fvE false 17 4 (by norm_num)) (Whir.chkE 2 3) w σ := rfl

/-! ## The final level at a memory -/

/-- **NODE3's `finG18_har` at a memory**: where the final level's rows and assertions hold, it re-executes
`fin18` (`ladP`'s last step) with the glued weight `wFin`, for every rounds and interface outputs. -/
theorem fin_hsA {c : Ctx} {M : Mem} (B : ℕ) (cs : List Ring.Claim) (Gs : List (List C2 → Cell → BM C2))
    (lam : E2) (lc : C2) (Pre : Mem → Prop) (hGs : List.Forall₂ (fun G cl ↦ QC.ClaimAt Pre cl G) Gs cs)
    (hlc : ∀ M, Pre M → ev2 M lc = lam)
    (hma : Whir.MA 25 (fun y ↦ (Ring.batch lam cs).1 (y.drop 6 ++ y.take 6)))
    (rc0 rc1 rc2 rc3 : List QC.RndC) (oc0 oc1 oc2 oc3 : QC.TailOutC) (wss0 wss1 wss2 wss3 : List (List C2))
    (lev : Level) (wdI a : ℕ) (σc : C2) (gate : Cell) (hg : gate.val M = 1) :
    HsA c M (QC.finGen (2 ^ 3 + 4) 18 (QC.posGen B 17 7 2 18) (fun rc ↦ QC.fvGen 17 4 3 rc) (QC.fpGen 3 4)
        (QC.wFinG Gs lc rc0 rc1 rc2 rc3 oc0 oc1 oc2 oc3 wss0 wss1 wss2 wss3) 10 2 3 4 lev wdI a σc gate)
      fun _ ↦ ∀ (rs0 rs1 rs2 rs3 : List (Whir.Rnd E2)) (o0 : Whir.TailOut E2 18 110 (2 ^ 21))
        (o1 : Whir.TailOut E2 14 45 (2 ^ 20)) (o2 : Whir.TailOut E2 10 28 (2 ^ 19))
        (o3 : Whir.TailOut E2 6 21 (2 ^ 18)), rs0.length = 6 → rs1.length = 4 → rs2.length = 4 →
        rs3.length = 4 → ∀ σ : E2,
        QC.RunsO M (QC.layFin (2 ^ 3 + 4) 2 18 3 lev wdI 10 13 2 4 a)
          (Whir.ladP Whir.chalE2 (.fin Whir.fin18) (QC.wFin lam cs rs0 rs1 rs2 rs3 o0 o1 o2 o3) σ)
          fun out ↦ (Pre M ∧ QC.LevRep M rc0 rc1 rc2 rc3 rs0 rs1 rs2 rs3 oc0 oc1 oc2 oc3 o0 o1 o2 o3 wss0 wss1
            wss2 wss3) → ev2 M σc = σ → out = true := by
  refine QC.hsA_pi fun rs0 ↦ QC.hsA_pi fun rs1 ↦ QC.hsA_pi fun rs2 ↦ QC.hsA_pi fun rs3 ↦ QC.hsA_pi fun o0 ↦
    QC.hsA_pi fun o1 ↦ QC.hsA_pi fun o2 ↦ QC.hsA_pi fun o3 ↦ QC.hsA_pi fun hl0 ↦ QC.hsA_pi fun hl1 ↦
    QC.hsA_pi fun hl2 ↦ QC.hsA_pi fun hl3 ↦ QC.hsA_pi fun σ ↦ ?_
  rw [ladP_fin18]
  exact QC.finG18_har B cs Gs lam lc Pre hGs hlc hma rc0 rc1 rc2 rc3 rs0 rs1 rs2 rs3 oc0 oc1 oc2 oc3 o0 o1 o2 o3
    wss0 wss1 wss2 wss3 hl0 hl1 hl2 hl3 10 13 2 4 (by norm_num) (by norm_num) (by norm_num) lev wdI a σ σc gate
    c M hg

/-! ## The opening runs -/

/-- The claim chain's step (`claimGlueHar`'s conclusion at the level's cells). -/
def GlueStep {ko t n : ℕ} (M : Mem) (s s' : C2) (rc : List QC.RndC) (oc : QC.TailOutC) : Prop :=
  ∀ (rs : List (Whir.Rnd E2)) (o : Whir.TailOut E2 ko t n), QC.RndsRep M rc rs → QC.TailRep M oc o →
    ev2 M s' = Whir.gluedC (Whir.foldsC rs.length rs (ev2 M s)) o.y o.lam o.c

/-- **The opening runs to `true`** on the levels' slots and the final level's, for the batch of `cs` at `λ`. -/
theorem whir_runsO {M : Mem} (lam : E2) (cs : List Ring.Claim) (Pre : Mem → Prop) (hPre : Pre M)
    (rc0 rc1 rc2 rc3 : List QC.RndC) (oc0 oc1 oc2 oc3 : QC.TailOutC) (wss0 wss1 wss2 wss3 : List (List C2))
    (hr0 : rc0.length = 6) (hr1 : rc1.length = 4) (hr2 : rc2.length = 4) (hr3 : rc3.length = 4)
    (lay0 lay1 lay2 lay3 layF : List QC.OEv)
    (h0 : QC.RunsO M lay0 (Whir.levelP Whir.chalE2 Whir.mid0.L Whir.mid0.g Whir.mid0.gO Whir.mid0.gQ Whir.mid0.ht
      Whir.mid0.wd Whir.mid0.i 6 Whir.mid0.vals) fun out ↦ QC.LevelRep M (rc0, oc0) out ∧ QC.WsRep M oc0.ps wss0 20)
    (h1 : QC.RunsO M lay1 (Whir.levelP Whir.chalE2 Whir.mid1.L Whir.mid1.g Whir.mid1.gO Whir.mid1.gQ Whir.mid1.ht
      Whir.mid1.wd Whir.mid1.i 4 Whir.mid1.vals) fun out ↦ QC.LevelRep M (rc1, oc1) out ∧ QC.WsRep M oc1.ps wss1 16)
    (h2 : QC.RunsO M lay2 (Whir.levelP Whir.chalE2 Whir.mid2.L Whir.mid2.g Whir.mid2.gO Whir.mid2.gQ Whir.mid2.ht
      Whir.mid2.wd Whir.mid2.i 4 Whir.mid2.vals) fun out ↦ QC.LevelRep M (rc2, oc2) out ∧ QC.WsRep M oc2.ps wss2 12)
    (h3 : QC.RunsO M lay3 (Whir.levelP Whir.chalE2 Whir.mid3.L Whir.mid3.g Whir.mid3.gO Whir.mid3.gQ Whir.mid3.ht
      Whir.mid3.wd Whir.mid3.i 4 Whir.mid3.vals) fun out ↦ QC.LevelRep M (rc3, oc3) out ∧ QC.WsRep M oc3.ps wss3 8)
    (s0 s1 s2 s3 s4 : C2) (hs0 : ev2 M s0 = (Ring.batch lam cs).2)
    (g0 : GlueStep (ko := 18) (t := 110) (n := 2 ^ 21) M s0 s1 rc0 oc0)
    (g1 : GlueStep (ko := 14) (t := 45) (n := 2 ^ 20) M s1 s2 rc1 oc1)
    (g2 : GlueStep (ko := 10) (t := 28) (n := 2 ^ 19) M s2 s3 rc2 oc2)
    (g3 : GlueStep (ko := 6) (t := 21) (n := 2 ^ 18) M s3 s4 rc3 oc3)
    (hF : ∀ (rs0 rs1 rs2 rs3 : List (Whir.Rnd E2)) (o0 : Whir.TailOut E2 18 110 (2 ^ 21))
        (o1 : Whir.TailOut E2 14 45 (2 ^ 20)) (o2 : Whir.TailOut E2 10 28 (2 ^ 19))
        (o3 : Whir.TailOut E2 6 21 (2 ^ 18)), rs0.length = 6 → rs1.length = 4 → rs2.length = 4 →
        rs3.length = 4 → ∀ σ : E2,
        QC.RunsO M layF
          (Whir.ladP Whir.chalE2 (.fin Whir.fin18) (QC.wFin lam cs rs0 rs1 rs2 rs3 o0 o1 o2 o3) σ)
          fun out ↦ (Pre M ∧ QC.LevRep M rc0 rc1 rc2 rc3 rs0 rs1 rs2 rs3 oc0 oc1 oc2 oc3 o0 o1 o2 o3 wss0 wss1
            wss2 wss3) → ev2 M s4 = σ → out = true) :
    QC.RunsO M (lay0 ++ (lay1 ++ (lay2 ++ (lay3 ++ layF)))) (Whir.whirP18 (Ring.batch lam cs))
      fun b ↦ b = true := by
  show QC.RunsO M _ (Whir.ladP Whir.chalE2 (.mid Whir.mid0 _) _ _) _
  rw [ladP_mid_eq]
  refine QC.runsO_bind h0 fun ro0 hro0 ↦ ?_
  rw [ladP_mid_eq]
  refine QC.runsO_bind h1 fun ro1 hro1 ↦ ?_
  rw [ladP_mid_eq]
  refine QC.runsO_bind h2 fun ro2 hro2 ↦ ?_
  rw [ladP_mid_eq]
  refine QC.runsO_bind h3 fun ro3 hro3 ↦ ?_
  obtain ⟨⟨r0, t0⟩, w0⟩ := hro0
  obtain ⟨⟨r1, t1⟩, w1⟩ := hro1
  obtain ⟨⟨r2, t2⟩, w2⟩ := hro2
  obtain ⟨⟨r3, t3⟩, w3⟩ := hro3
  have l0 : ro0.1.length = 6 := r0.length_eq.symm.trans hr0
  have l1 : ro1.1.length = 4 := r1.length_eq.symm.trans hr1
  have l2 : ro2.1.length = 4 := r2.length_eq.symm.trans hr2
  have l3 : ro3.1.length = 4 := r3.length_eq.symm.trans hr3
  refine QC.runsO_mono (hF ro0.1 ro1.1 ro2.1 ro3.1 ro0.2 ro1.2 ro2.2 ro3.2 l0 l1 l2 l3 _) fun b hb ↦
    hb ⟨hPre, ⟨r0, t0, w0⟩, ⟨r1, t1, w1⟩, ⟨r2, t2, w2⟩, ⟨r3, t3, w3⟩⟩ ?_
  rw [g3 _ _ r3 t3, g2 _ _ r2 t2, g1 _ _ r1 t1, g0 _ _ r0 t0, hs0, l0, l1, l2, l3]
  rfl

/-- **The opening returns `true` on V1's values** matching the slots, whose openings carry `F18`. -/
theorem whir_afterV {M : Mem} {lay : List QC.OEv} {cl : StackClaim6}
    (h : QC.RunsO M lay (Whir.whirP18 cl) fun b ↦ b = true) (hp : QC.PowLayO M lay) {vo : List V.Val}
    (he : QC.OEvMatch M lay (vo.map toEv)) (hq : RowsF F18 [] vo) :
    afterV (Whir.whirP18 cl) vo = some (.ret true) := by
  obtain ⟨out, h1, rfl⟩ := afterV_of_runsO_q h hp he (qAgree_whirP18 cl hq)
  exact h1

/-! ## `htail` -/

/-- **`dec_of_runs`'s `htail` from CC** (with V1c's phases: `ringPhase6`, `whirP18`), at the represented
outputs: the ring gadget's run (`ringPhase_runs`), the opening's run (`whir_runsO`) for the claim the ring
phase hands on, the slots' grinds and events, V1's openings carrying `F18`; per output tuple, the slice points'
lengths, at most 7 typed claims, and the cells holding the slice values and the stacked claims' values. -/
theorem htail_of_cc {M : Mem} {h : Digest} {c0 : StackClaim6} {Pt : K.TreeOut → Prop} {Ps : K.SpOut → Prop}
    {Pl : SP.LinkOut → Prop} {Py : Lvm6.Ty.OpenClaimsE → Prop} {o : QC.RingPhC} {svT svS vs : List C2} {aR : ℕ}
    (hR : ∀ (sl : List SliceClaim) (st : List StackClaim6), ringOK P18 sl → st.length + 2 ≤ P18.J₀ →
      QC.RunsO M (QC.layRing6 17 aR) (ringPhase6 P18 sl st) fun out ↦
        sl.map (fun c ↦ List.ofFn c.s) = [svT.map (ev2 M), svS.map (ev2 M)] →
          st.map (·.2) = vs.map (ev2 M) → QC.RingPhRep sl st M o out)
    (hpR : QC.PowLayO M (QC.layRing6 17 aR)) {vr : List V.Val} (hnR : NoRows vr)
    (heR : QC.OEvMatch M (QC.layRing6 17 aR) (vr.map toEv))
    {layW : List QC.OEv} (hpW : QC.PowLayO M layW) {vo : List V.Val} (heW : QC.OEvMatch M layW (vo.map toEv))
    (hqW : RowsF F18 [] vo)
    (hsh : ∀ ot os, Pt ot → Ps os → ot.en.pt.length = 19 + 6 ∧ os.2.2.2.pt.length = 13 + 6)
    (hty : ∀ oy, Py oy → (Lvm6.Ty.claimsOnStack oy).length ≤ 7)
    (hval : ∀ ot os lk oy, Pt ot → Ps os → Pl lk → Py oy →
      [List.ofFn (K.toS 19 h ot).slices.s, List.ofFn (SP.spS os lk).slices.s] =
          [svT.map (ev2 M), svS.map (ev2 M)] ∧
        (stackedOf c0 (K.toS 19 h ot) (SP.spS os lk) (Lvm6.Ty.claimsOnStack oy)).map (·.2) = vs.map (ev2 M))
    (hW : ∀ ot os lk oy, Pt ot → Ps os → Pl lk → Py oy → ∀ cl,
      QC.RingPhRep [(K.toS 19 h ot).slices, (SP.spS os lk).slices]
        (stackedOf c0 (K.toS 19 h ot) (SP.spS os lk) (Lvm6.Ty.claimsOnStack oy)) M o cl →
      QC.RunsO M layW (Whir.whirP18 cl) fun b ↦ b = true) :
    ∀ ot os lk oy, Pt ot → Ps os → Pl lk → Py oy →
      let t := K.toS 19 h ot; let s := SP.spS os lk; let ty := Lvm6.Ty.claimsOnStack oy
      [t.slices, s.slices].length + (stackedOf c0 t s ty).length ≤ P18.J₀ ∧
      ∃ cl, afterV (ringPhase6 P18 [t.slices, s.slices] (stackedOf c0 t s ty)) vr = some (.ret cl) ∧
        afterV (Whir.whirP18 cl) vo = some (.ret true) := by
  intro ot os lk oy hot hos hlk hoy
  obtain ⟨hpt, hps⟩ := hsh ot os hot hos
  obtain ⟨h1, h2⟩ := hval ot os lk oy hot hos hlk hoy
  obtain ⟨hJ, cl, hcl, hrep⟩ := tail_ring hR hpR hnR heR c0 h ot os lk _ (hty oy hoy) hpt hps h1 h2
  exact ⟨hJ, cl, hcl, whir_afterV (hW ot os lk oy hot hos hlk hoy cl hrep) hpW heW hqW⟩

/-! ## The mid levels at a memory (CC-4 with shared `Ŵ`, at `levCall`'s generator) -/

/-- **`levelHarW` at a memory** for a ladder level `Mv`. -/
theorem lev_hsA {c : Ctx} {M : Mem} {n ℓ n' ℓ' : ℕ} (Mv : Whir.MidLv E2 Whir.WtE n ℓ n' ℓ')
    (posG : (Fin (Mv.L.kq + 1) → C2) → Cell → BM (List Cell))
    (valsGW : List QC.RndC → List C2 → List Cell → List (List (Option ℕ)) → Cell → BM (List C2 × List (List C2)))
    (nw : ℕ) (hpos : QC.PosOK Mv.L.pos posG)
    (hvals : ∀ c M rc rs, QC.RndsRep M rc rs → QC.ValsWAt c M (Mv.vals rs) nw (valsGW rc))
    (hg10 : Mv.g ≤ 64) (hgO : Mv.gO ≤ 64) (hgQ : Mv.gQ ≤ 64) (lev : Level) (wdI lvN a : ℕ) (gate : Cell)
    (hg : gate.val M = 1) :
    HsA c M (QC.levelGenW Mv.L.nh Mv.L.ko Mv.L.t posG valsGW Mv.g ℓ lev wdI lvN a gate) fun o ↦
      QC.RunsO M (QC.layRounds Mv.g ℓ a ++ QC.layTail Mv.L.nh Mv.L.ko Mv.L.kq Mv.L.t lev wdI Mv.ht Mv.wd lvN
          Mv.gO Mv.gQ (a + 27 * ℓ))
        (Whir.levelP Whir.chalE2 Mv.L Mv.g Mv.gO Mv.gQ Mv.ht Mv.wd Mv.i ℓ Mv.vals)
        fun out ↦ QC.LevelRep M (o.1, o.2.1) out ∧ QC.WsRep M o.2.1.ps o.2.2 nw :=
  QC.levelHarW Mv.L nw Mv.vals posG valsGW hpos hvals Mv.g Mv.ht Mv.wd Mv.i Mv.gO Mv.gQ ℓ hg10 hgO hgQ lev wdI
    lvN a gate c M hg

/-- Level 0 of the deployed circuit (`levCall … 0`) runs `mid0`'s `levelP`. -/
theorem lev0_hsA {c : Ctx} {M : Mem} (I : Dep.Inp) (B : ℕ) (gate : Cell) (hg : gate.val M = 1) :
    HsA c M (Dep.levCall I B 0 gate) fun o ↦
      QC.RunsO M (QC.layRounds 10 6 (I.aL 0) ++ QC.layTail 6 18 18 110 (P18.lvl 0) (QC.wdOf 0) Whir.mid0.ht
          Whir.mid0.wd (P18.lvl 1).lv Whir.mid0.gO Whir.mid0.gQ (I.aL 0 + 27 * 6))
        (Whir.levelP Whir.chalE2 Whir.mid0.L Whir.mid0.g Whir.mid0.gO Whir.mid0.gQ Whir.mid0.ht Whir.mid0.wd
          Whir.mid0.i 6 Whir.mid0.vals)
        fun out ↦ QC.LevelRep M (o.1, o.2.1) out ∧ QC.WsRep M o.2.1.ps o.2.2 20 :=
  lev_hsA Whir.mid0 _ _ 20 (QC.posE2Har (Dep.bOf B 0) 21 6 18 110 (by norm_num) (by norm_num) (by norm_num)
      (by norm_num))
    (fun c M rc rs h ↦ QC.valsGenW_ok true 21 6 19 (by norm_num) 110 c M rc rs h)
    (show 10 ≤ 64 by norm_num) (show 18 ≤ 64 by norm_num) (show 19 ≤ 64 by norm_num) _ _ _ _ gate hg

/-- Level 1 of the deployed circuit (`levCall … 1`) runs `mid1`'s `levelP`. -/
theorem lev1_hsA {c : Ctx} {M : Mem} (I : Dep.Inp) (B : ℕ) (gate : Cell) (hg : gate.val M = 1) :
    HsA c M (Dep.levCall I B 1 gate) fun o ↦
      QC.RunsO M (QC.layRounds 10 4 (I.aL 1) ++ QC.layTail 4 14 7 45 (P18.lvl 1) (QC.wdOf 1) Whir.mid1.ht
          Whir.mid1.wd (P18.lvl 2).lv Whir.mid1.gO Whir.mid1.gQ (I.aL 1 + 27 * 4))
        (Whir.levelP Whir.chalE2 Whir.mid1.L Whir.mid1.g Whir.mid1.gO Whir.mid1.gQ Whir.mid1.ht Whir.mid1.wd
          Whir.mid1.i 4 Whir.mid1.vals)
        fun out ↦ QC.LevelRep M (o.1, o.2.1) out ∧ QC.WsRep M o.2.1.ps o.2.2 16 :=
  lev_hsA Whir.mid1 _ _ 16 (QC.posE2Har (Dep.bOf B 1) 20 6 7 45 (by norm_num) (by norm_num) (by norm_num)
      (by norm_num))
    (fun c M rc rs h ↦ QC.valsGenW_ok false 20 4 15 (by norm_num) 45 c M rc rs h)
    (show 10 ≤ 64 by norm_num) (show 18 ≤ 64 by norm_num) (show 17 ≤ 64 by norm_num) _ _ _ _ gate hg

/-- Level 2 of the deployed circuit (`levCall … 2`) runs `mid2`'s `levelP`. -/
theorem lev2_hsA {c : Ctx} {M : Mem} (I : Dep.Inp) (B : ℕ) (gate : Cell) (hg : gate.val M = 1) :
    HsA c M (Dep.levCall I B 2 gate) fun o ↦
      QC.RunsO M (QC.layRounds 10 4 (I.aL 2) ++ QC.layTail 4 10 4 28 (P18.lvl 2) (QC.wdOf 2) Whir.mid2.ht
          Whir.mid2.wd (P18.lvl 3).lv Whir.mid2.gO Whir.mid2.gQ (I.aL 2 + 27 * 4))
        (Whir.levelP Whir.chalE2 Whir.mid2.L Whir.mid2.g Whir.mid2.gO Whir.mid2.gQ Whir.mid2.ht Whir.mid2.wd
          Whir.mid2.i 4 Whir.mid2.vals)
        fun out ↦ QC.LevelRep M (o.1, o.2.1) out ∧ QC.WsRep M o.2.1.ps o.2.2 12 :=
  lev_hsA Whir.mid2 _ _ 12 (QC.posE2Har (Dep.bOf B 2) 19 6 4 28 (by norm_num) (by norm_num) (by norm_num)
      (by norm_num))
    (fun c M rc rs h ↦ QC.valsGenW_ok false 19 4 11 (by norm_num) 28 c M rc rs h)
    (show 10 ≤ 64 by norm_num) (show 18 ≤ 64 by norm_num) (show 18 ≤ 64 by norm_num) _ _ _ _ gate hg

/-- Level 3 of the deployed circuit (`levCall … 3`) runs `mid3`'s `levelP`. -/
theorem lev3_hsA {c : Ctx} {M : Mem} (I : Dep.Inp) (B : ℕ) (gate : Cell) (hg : gate.val M = 1) :
    HsA c M (Dep.levCall I B 3 gate) fun o ↦
      QC.RunsO M (QC.layRounds 10 4 (I.aL 3) ++ QC.layTail 4 6 2 21 (P18.lvl 3) (QC.wdOf 3) Whir.mid3.ht
          Whir.mid3.wd (P18.lvl 4).lv Whir.mid3.gO Whir.mid3.gQ (I.aL 3 + 27 * 4))
        (Whir.levelP Whir.chalE2 Whir.mid3.L Whir.mid3.g Whir.mid3.gO Whir.mid3.gQ Whir.mid3.ht Whir.mid3.wd
          Whir.mid3.i 4 Whir.mid3.vals)
        fun out ↦ QC.LevelRep M (o.1, o.2.1) out ∧ QC.WsRep M o.2.1.ps o.2.2 8 :=
  lev_hsA Whir.mid3 _ _ 8 (QC.posE2Har (Dep.bOf B 3) 18 7 2 21 (by norm_num) (by norm_num) (by norm_num)
      (by norm_num))
    (fun c M rc rs h ↦ QC.valsGenW_ok false 18 4 7 (by norm_num) 21 c M rc rs h)
    (show 10 ≤ 64 by norm_num) (show 18 ≤ 64 by norm_num) (show 17 ≤ 64 by norm_num) _ _ _ _ gate hg

/-! ## The deployed CC part at a memory -/

theorem hsA_and {c : Ctx} {M : Mem} {α : Type} {m : BM α} {P Q : α → Prop} (h1 : HsA c M m P)
    (h2 : HsA c M m Q) : HsA c M m fun o ↦ P o ∧ Q o :=
  fun p hh ha ↦ ⟨h1 p hh ha, h2 p hh ha⟩

/-- A level gadget hands out `ℓ` round cells. -/
theorem levelGenW_len {c : Ctx} {M : Mem} {kq : ℕ} (nh ko t : ℕ) (posG : (Fin (kq + 1) → C2) → Cell → BM (List Cell))
    (valsGW : List QC.RndC → List C2 → List Cell → List (List (Option ℕ)) → Cell → BM (List C2 × List (List C2)))
    (g ℓ : ℕ) (lev : Level) (wdI lvN a : ℕ) (gate : Cell) :
    HsA c M (QC.levelGenW nh ko t posG valsGW g ℓ lev wdI lvN a gate) fun o ↦ o.1.length = ℓ := by
  unfold QC.levelGenW
  rw [QC.roundsGen_eq]
  refine hsA_bind (hsA_pure (P := fun rc ↦ rc = QC.roundsCells ℓ a) rfl) fun rc hrc ↦
    hsA_bind (P := fun _ ↦ True) (fun _ _ _ ↦ trivial) fun _ _ ↦
      hsA_bind (P := fun _ ↦ True) (fun _ _ _ ↦ trivial) fun _ _ ↦ hsA_pure ?_
  rw [hrc]
  simp [QC.roundsCells]


/-- The claim chain's step at a memory (`claimGlueHar` for every rounds and interface). -/
theorem glue_hsA {c : Ctx} {M : Mem} {ko t n : ℕ} (σc : C2) (rc : List QC.RndC) (oc : QC.TailOutC) :
    HsA c M (QC.claimGlueG σc rc oc) fun s ↦ GlueStep (ko := ko) (t := t) (n := n) M σc s rc oc :=
  QC.hsA_pi fun rs ↦ QC.hsA_pi fun o ↦ QC.hsA_pi fun hr ↦ QC.hsA_pi fun ho ↦
    QC.claimGlueHar c M σc rc rs oc o hr ho

/-- **The CC part of the node circuit (`ccG18I I B`) at a memory**: where its rows and assertions hold, the ring
gadget runs `ringPhase6` (`ringPhase_runs`), the four levels run `mid_j`'s `levelP`, the claim chain glues, and
the final level runs `fin18` with the glued weight of the claim gadgets `claimGs I rp` (for any claims they
compute: `ClaimAt`, the `λ₀` cell, `MA 25`). These are `whir_runsO`'s hypotheses. -/
theorem ccG18_tail {c : Ctx} {M : Mem} (I : Dep.Inp) (B : ℕ) (gate : Cell) (hg : gate.val M = 1) :
    HsA c M (Dep.ccG18I I B gate) fun _ ↦ ∃ (rp : QC.RingPhC) (l0 l1 l2 l3 : List QC.RndC × QC.TailOutC ×
        List (List C2)) (s1 s2 s3 s4 : C2),
      (∀ (sl : List SliceClaim) (st : List StackClaim6), ringOK P18 sl → st.length + 2 ≤ P18.J₀ →
        QC.RunsO M (QC.layRing6 17 I.aRing) (ringPhase6 P18 sl st) fun out ↦
          sl.map (fun c ↦ List.ofFn c.s) = [I.svT.map (ev2 M), I.svS.map (ev2 M)] →
            st.map (·.2) = I.vs.map (ev2 M) → QC.RingPhRep sl st M rp out) ∧
      QC.RunsO M (QC.layRounds 10 6 (I.aL 0) ++ QC.layTail 6 18 18 110 (P18.lvl 0) (QC.wdOf 0) Whir.mid0.ht Whir.mid0.wd (P18.lvl 1).lv Whir.mid0.gO Whir.mid0.gQ (I.aL 0 + 27 * 6))
        (Whir.levelP Whir.chalE2 Whir.mid0.L Whir.mid0.g Whir.mid0.gO Whir.mid0.gQ Whir.mid0.ht Whir.mid0.wd Whir.mid0.i 6 Whir.mid0.vals)
        (fun out ↦ QC.LevelRep M (l0.1, l0.2.1) out ∧ QC.WsRep M l0.2.1.ps l0.2.2 20) ∧ l0.1.length = 6 ∧
      QC.RunsO M (QC.layRounds 10 4 (I.aL 1) ++ QC.layTail 4 14 7 45 (P18.lvl 1) (QC.wdOf 1) Whir.mid1.ht Whir.mid1.wd (P18.lvl 2).lv Whir.mid1.gO Whir.mid1.gQ (I.aL 1 + 27 * 4))
        (Whir.levelP Whir.chalE2 Whir.mid1.L Whir.mid1.g Whir.mid1.gO Whir.mid1.gQ Whir.mid1.ht Whir.mid1.wd Whir.mid1.i 4 Whir.mid1.vals)
        (fun out ↦ QC.LevelRep M (l1.1, l1.2.1) out ∧ QC.WsRep M l1.2.1.ps l1.2.2 16) ∧ l1.1.length = 4 ∧
      QC.RunsO M (QC.layRounds 10 4 (I.aL 2) ++ QC.layTail 4 10 4 28 (P18.lvl 2) (QC.wdOf 2) Whir.mid2.ht Whir.mid2.wd (P18.lvl 3).lv Whir.mid2.gO Whir.mid2.gQ (I.aL 2 + 27 * 4))
        (Whir.levelP Whir.chalE2 Whir.mid2.L Whir.mid2.g Whir.mid2.gO Whir.mid2.gQ Whir.mid2.ht Whir.mid2.wd Whir.mid2.i 4 Whir.mid2.vals)
        (fun out ↦ QC.LevelRep M (l2.1, l2.2.1) out ∧ QC.WsRep M l2.2.1.ps l2.2.2 12) ∧ l2.1.length = 4 ∧
      QC.RunsO M (QC.layRounds 10 4 (I.aL 3) ++ QC.layTail 4 6 2 21 (P18.lvl 3) (QC.wdOf 3) Whir.mid3.ht Whir.mid3.wd (P18.lvl 4).lv Whir.mid3.gO Whir.mid3.gQ (I.aL 3 + 27 * 4))
        (Whir.levelP Whir.chalE2 Whir.mid3.L Whir.mid3.g Whir.mid3.gO Whir.mid3.gQ Whir.mid3.ht Whir.mid3.wd Whir.mid3.i 4 Whir.mid3.vals)
        (fun out ↦ QC.LevelRep M (l3.1, l3.2.1) out ∧ QC.WsRep M l3.2.1.ps l3.2.2 8) ∧ l3.1.length = 4 ∧
      GlueStep (ko := 18) (t := 110) (n := 2 ^ 21) M rp.val s1 l0.1 l0.2.1 ∧
      GlueStep (ko := 14) (t := 45) (n := 2 ^ 20) M s1 s2 l1.1 l1.2.1 ∧
      GlueStep (ko := 10) (t := 28) (n := 2 ^ 19) M s2 s3 l2.1 l2.2.1 ∧
      GlueStep (ko := 6) (t := 21) (n := 2 ^ 18) M s3 s4 l3.1 l3.2.1 ∧
      ∀ (cs : List Ring.Claim) (Pre : Mem → Prop) (lam : E2),
        List.Forall₂ (fun G cl ↦ QC.ClaimAt Pre cl G) (Dep.claimGs I rp) cs → (∀ M, Pre M → ev2 M rp.lam = lam) →
        Whir.MA 25 (fun y ↦ (Ring.batch lam cs).1 (y.drop 6 ++ y.take 6)) →
        ∀ (rs0 rs1 rs2 rs3 : List (Whir.Rnd E2)) (o0 : Whir.TailOut E2 18 110 (2 ^ 21))
          (o1 : Whir.TailOut E2 14 45 (2 ^ 20)) (o2 : Whir.TailOut E2 10 28 (2 ^ 19))
          (o3 : Whir.TailOut E2 6 21 (2 ^ 18)), rs0.length = 6 → rs1.length = 4 → rs2.length = 4 →
          rs3.length = 4 → ∀ σ : E2,
          QC.RunsO M (QC.layFin (2 ^ 3 + 4) 2 18 3 (P18.lvl 4) 32 10 13 2 4 (I.aL 4))
            (Whir.ladP Whir.chalE2 (.fin Whir.fin18) (QC.wFin lam cs rs0 rs1 rs2 rs3 o0 o1 o2 o3) σ)
            fun out ↦ (Pre M ∧ QC.LevRep M l0.1 l1.1 l2.1 l3.1 rs0 rs1 rs2 rs3 l0.2.1 l1.2.1 l2.2.1 l3.2.1 o0 o1 o2
              o3 l0.2.2 l1.2.2 l2.2.2 l3.2.2) → ev2 M s4 = σ → out = true := by
  unfold Dep.ccG18I
  refine hsA_bind (ringPhase_runs I.svT I.svS I.vs I.aRing gate hg) fun rp hrp ↦ ?_
  refine hsA_bind (hsA_and (lev0_hsA I B gate hg) (levelGenW_len (c := c) _ _ _ _ _ _ _ _ _ _ _ gate)) fun l0 h0 ↦ ?_
  refine hsA_bind (hsA_and (lev1_hsA I B gate hg) (levelGenW_len (c := c) _ _ _ _ _ _ _ _ _ _ _ gate)) fun l1 h1 ↦ ?_
  refine hsA_bind (hsA_and (lev2_hsA I B gate hg) (levelGenW_len (c := c) _ _ _ _ _ _ _ _ _ _ _ gate)) fun l2 h2 ↦ ?_
  refine hsA_bind (hsA_and (lev3_hsA I B gate hg) (levelGenW_len (c := c) _ _ _ _ _ _ _ _ _ _ _ gate)) fun l3 h3 ↦ ?_
  refine hsA_bind (glue_hsA (ko := 18) (t := 110) (n := 2 ^ 21) rp.val l0.1 l0.2.1) fun s1 g1 ↦ ?_
  refine hsA_bind (glue_hsA (ko := 14) (t := 45) (n := 2 ^ 20) s1 l1.1 l1.2.1) fun s2 g2 ↦ ?_
  refine hsA_bind (glue_hsA (ko := 10) (t := 28) (n := 2 ^ 19) s2 l2.1 l2.2.1) fun s3 g3 ↦ ?_
  refine hsA_bind (glue_hsA (ko := 6) (t := 21) (n := 2 ^ 18) s3 l3.1 l3.2.1) fun s4 g4 ↦ ?_
  refine hsA_bind (QC.hsA_pi fun cs ↦ QC.hsA_pi fun Pre ↦ QC.hsA_pi fun lam ↦ QC.hsA_pi fun hGs ↦
    QC.hsA_pi fun hlc ↦ QC.hsA_pi fun hma ↦ fin_hsA (Dep.bOf B 4) cs (Dep.claimGs I rp) lam rp.lam Pre hGs hlc
      hma l0.1 l1.1 l2.1 l3.1 l0.2.1 l1.2.1 l2.2.1 l3.2.1 l0.2.2 l1.2.2 l2.2.2 l3.2.2 (P18.lvl 4) 32 (I.aL 4) s4
      gate hg) fun _ hf ↦ hsA_pure ⟨rp, l0, l1, l2, l3, s1, s2, s3, s4, hrp, h0.1, h0.2, h1.1, h1.2, h2.1, h2.2, h3.1, h3.2, g1, g2, g3, g4, hf⟩

/-- **The opening runs for the claim the ring phase hands on** (`RingPhRep`): `whir_runsO` at `λ₀` of the ring
cells and the placed claims, the claim chain starting at the ring phase's value cell. -/
theorem whir_of_ring {M : Mem} {sl : List SliceClaim} {st : List StackClaim6} {rp : QC.RingPhC} {cl : StackClaim6}
    (hrep : QC.RingPhRep sl st M rp cl) (Pre : Mem → Prop) (hPre : Pre M)
    (rc0 rc1 rc2 rc3 : List QC.RndC) (oc0 oc1 oc2 oc3 : QC.TailOutC) (wss0 wss1 wss2 wss3 : List (List C2))
    (hr0 : rc0.length = 6) (hr1 : rc1.length = 4) (hr2 : rc2.length = 4) (hr3 : rc3.length = 4)
    (lay0 lay1 lay2 lay3 layF : List QC.OEv)
    (h0 : QC.RunsO M lay0 (Whir.levelP Whir.chalE2 Whir.mid0.L Whir.mid0.g Whir.mid0.gO Whir.mid0.gQ Whir.mid0.ht
      Whir.mid0.wd Whir.mid0.i 6 Whir.mid0.vals) fun out ↦ QC.LevelRep M (rc0, oc0) out ∧ QC.WsRep M oc0.ps wss0 20)
    (h1 : QC.RunsO M lay1 (Whir.levelP Whir.chalE2 Whir.mid1.L Whir.mid1.g Whir.mid1.gO Whir.mid1.gQ Whir.mid1.ht
      Whir.mid1.wd Whir.mid1.i 4 Whir.mid1.vals) fun out ↦ QC.LevelRep M (rc1, oc1) out ∧ QC.WsRep M oc1.ps wss1 16)
    (h2 : QC.RunsO M lay2 (Whir.levelP Whir.chalE2 Whir.mid2.L Whir.mid2.g Whir.mid2.gO Whir.mid2.gQ Whir.mid2.ht
      Whir.mid2.wd Whir.mid2.i 4 Whir.mid2.vals) fun out ↦ QC.LevelRep M (rc2, oc2) out ∧ QC.WsRep M oc2.ps wss2 12)
    (h3 : QC.RunsO M lay3 (Whir.levelP Whir.chalE2 Whir.mid3.L Whir.mid3.g Whir.mid3.gO Whir.mid3.gQ Whir.mid3.ht
      Whir.mid3.wd Whir.mid3.i 4 Whir.mid3.vals) fun out ↦ QC.LevelRep M (rc3, oc3) out ∧ QC.WsRep M oc3.ps wss3 8)
    (s1 s2 s3 s4 : C2)
    (g0 : GlueStep (ko := 18) (t := 110) (n := 2 ^ 21) M rp.val s1 rc0 oc0)
    (g1 : GlueStep (ko := 14) (t := 45) (n := 2 ^ 20) M s1 s2 rc1 oc1)
    (g2 : GlueStep (ko := 10) (t := 28) (n := 2 ^ 19) M s2 s3 rc2 oc2)
    (g3 : GlueStep (ko := 6) (t := 21) (n := 2 ^ 18) M s3 s4 rc3 oc3)
    (hF : ∀ (rs0 rs1 rs2 rs3 : List (Whir.Rnd E2)) (o0 : Whir.TailOut E2 18 110 (2 ^ 21))
        (o1 : Whir.TailOut E2 14 45 (2 ^ 20)) (o2 : Whir.TailOut E2 10 28 (2 ^ 19))
        (o3 : Whir.TailOut E2 6 21 (2 ^ 18)), rs0.length = 6 → rs1.length = 4 → rs2.length = 4 →
        rs3.length = 4 → ∀ σ : E2,
        QC.RunsO M layF
          (Whir.ladP Whir.chalE2 (.fin Whir.fin18) (QC.wFin (ev2 M rp.lam)
            (placeRing (ringOf (sl.getD 0 ⟨[], 0⟩) (rp.ft.map (ev2 M)) (rp.gt.map (ev2 M)))
              (ringOf (sl.getD 1 ⟨[], 0⟩) (rp.fs.map (ev2 M)) (rp.gs.map (ev2 M))) st)
            rs0 rs1 rs2 rs3 o0 o1 o2 o3) σ)
          fun out ↦ (Pre M ∧ QC.LevRep M rc0 rc1 rc2 rc3 rs0 rs1 rs2 rs3 oc0 oc1 oc2 oc3 o0 o1 o2 o3 wss0 wss1
            wss2 wss3) → ev2 M s4 = σ → out = true) :
    QC.RunsO M (lay0 ++ (lay1 ++ (lay2 ++ (lay3 ++ layF)))) (Whir.whirP18 cl) fun b ↦ b = true := by
  obtain ⟨rfl, hv⟩ := hrep
  exact whir_runsO _ _ Pre hPre rc0 rc1 rc2 rc3 oc0 oc1 oc2 oc3 wss0 wss1 wss2 wss3 hr0 hr1 hr2 hr3
    lay0 lay1 lay2 lay3 layF h0 h1 h2 h3 rp.val s1 s2 s3 s4 hv g0 g1 g2 g3 hF

end Lvm6.Node
