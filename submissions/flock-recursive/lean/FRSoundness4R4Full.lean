-- New for `flock-recursive` (BLUEPRINT revision 4.1, A.9, A.10; track R4h): the assembly of
-- `FinRest4` and T4's `AcceptTail` from an accepted run, per kind.
import FRSoundness4R4PfFin

/-!
# `FinRest4` and `AcceptTail` from an accepted run, per kind

**`finRest4_full`**: on an accepted run's fields, `FinRest4` holds with `start`, `cols`, `link`
(R4g), `pf0`, `enc` (`FRSoundness4R4P4`, the zero tail from `finPf`'s tail flag) and `fin`
(`FRSoundness4R4PfFin`) proved; the hypotheses left are the op parameters (`phiRS`, `tensorW` at
their specs), the program's table facts (`FinTabs4`: discharged for every kind by `finTabs4_seg`,
`finTabs4_node`) and **`hW`**: `finPf`'s `Ŵ₄(P₄)` (`wV4`, its level steps from `Ŵ₀(P₀)`) is
`wHatL W₀ L es 4`.

**`acceptTail4_seg`**, **`acceptTail4_node`**: an accepted run of a kind's program gives
`T4.AcceptTail RejF W₀ c₀L4 L j`, given `¬ RejF` on accepted runs and `hW` on their fields.
-/

namespace FR.Snd.R4
open RecursionFast Rev4 Finset

/-- **The finals' table facts `finPf` needs** at `P` for the program kind `κ` whose chain has kind
`κc`. -/
structure FinTabs4 (P : FinP) (κ : Kind) (κc : CKind) : Prop where
  S : P.S = seq4
  ck : P.ck = true
  nc : 0 < P.nc
  nf : 0 < P.fams.length
  ix : ∀ j ∈ P.kv.ptIx κ, j < 8 + 8 * P.fams.length + P.e4s.length
  pad : (P.kv.selA κ = true ∧ κc.m = 32) ∨ (P.kv.selA κ = false ∧ P.fams.getD (famI P κ) 0 = κc.m)
  km : P.kv.m κ = κc.m
  tl : κc.m < 32 → κc.m ∈ P.tails
  node : P.kv.node κ = κc.isNode

theorem finTabs4_seg (σ : SegKind) (κ : Kind) : FinTabs4 (segFinP σ) κ (.seg σ) := by
  cases σ <;> refine ⟨rfl, rfl, ?_, ?_, ?_, ?_, rfl, ?_, rfl⟩ <;>
    simp (config := { decide := true }) [segFinP, kvOf, segFams, famI, selI, seq4_eq, SegKind.m, CKind.m]

theorem finTabs4_node (ν : NodeKind) (cells : List ℕ) (κ : Kind) : FinTabs4 (nodeFinP ν cells) κ (.node ν) := by
  cases ν <;> refine ⟨rfl, rfl, ?_, ?_, ?_, ?_, rfl, ?_, rfl⟩ <;>
    simp (config := { decide := true }) [nodeFinP, kvOf, nodeFams, nodeE4s, famI, selI, seq4_eq, NodeKind.m, CKind.m]

section Acc
variable {impl : OpImpl} {p : KindP} {inp : Input} {tr : Trace} {y : List Val × List Bool × Trace}
  {P : FinP} {zh : List Reg} {Rs : ℕ → Array Val} {Ex : ℕ → Array (List Reg)}

/-- **`FinRest4` on the fields** with every field proved; `hW` (`Ŵ₄(P₄)` at the spec) left. -/
theorem finRest4_full (hphi : ∀ r a, r.size = 7 → impl.phiRS r a = Impl.phiRSS r a)
    (ht : ∀ j r, impl.tensorW j r = Impl.tensorWS j r)
    (hF : Fields4 impl p inp tr P y zh Rs Ex) (hT : FinTabs4 P p.tix (kindOfC (fsOf tr (itemsOf seq4))))
    (hm : p.d.m = (kindOfC (fsOf tr (itemsOf seq4))).m) {L : Log} (hb : ¬ Bad L) (hin : ∀ e ∈ tr, e ∈ L)
    (hπ : inp.π.size = piSizeOf seq4) {W₀ : Log → Log → ℕ → K}
    (hW : wV4 impl p.tix ⟨(skeleton4 seq4 p).2.outs, zh, Ex 11⟩ (Rs 11) P =
      T4.wHatL W₀ L (fsOf tr (itemsOf seq4)) 4) :
    FinRest4 W₀ P4b.c₀L4 L (fsOf tr (itemsOf seq4)) (yv4 p (#[] ++ y.1.toArray)) := by
  have hix : ∀ j ∈ P.kv.ptIx p.tix, j < (gPfPts P ⟨(skeleton4 seq4 p).2.outs, zh, Ex 11⟩).length := by
    rw [gPfPts_length]; exact hT.ix
  exact finRest4_of_fields hphi hF hT.S hT.node hm hb hin hπ (pf04_of_fields hF _ L)
    (enc4_of_fields hF hT.S ht hb hin hm (hz_of_fields hF hT.S hT.ck hT.nc hT.nf hix hT.km hT.tl))
    (fin4_of_fields hF hT.S hT.ck hT.nc hT.nf hix hT.pad hW _)

end Acc

/-- **`AcceptTail` from an accepted segment run** (`acceptTail4_of_run` with `finRest4_full`). -/
theorem acceptTail4_seg {impl : OpImpl} {σ : SegKind} {inp : Input} {RejF : Log → Log → Prop}
    {W₀ : Log → Log → ℕ → K} {L : Log}
    (hphi : ∀ r a, r.size = 7 → impl.phiRS r a = Impl.phiRSS r a)
    (ht : ∀ j r, impl.tensorW j r = Impl.tensorWS j r)
    (hb : ¬ Bad L) (hπ : inp.π.size = piSizeOf seq4)
    (hrun : (runIR impl (gen4 seq4 (.ofSeg σ) (finOps4 (segFinP σ))) inp).runLog L = some true)
    (hR : ∀ tr, semIR impl (gen4 seq4 (.ofSeg σ) (finOps4 (segFinP σ))) inp tr = some true → (∀ e ∈ tr, e ∈ L) →
      ¬ RejF L (fsOf tr (itemsOf seq4)))
    (hW : ∀ tr y zh Rs Ex, semIR impl (gen4 seq4 (.ofSeg σ) (finOps4 (segFinP σ))) inp tr = some true →
      (∀ e ∈ tr, e ∈ L) → Fields4 impl (.ofSeg σ) inp tr (segFinP σ) y zh Rs Ex →
      wV4 impl (KindP.ofSeg σ).tix ⟨(skeleton4 seq4 (.ofSeg σ)).2.outs, zh, Ex 11⟩ (Rs 11) (segFinP σ) =
        T4.wHatL W₀ L (fsOf tr (itemsOf seq4)) 4) :
    ∃ j, T4.AcceptTail RejF W₀ P4b.c₀L4 L j := by
  refine acceptTail4_of_run _ hb hπ hrun fun tr hsem hin => ?_
  obtain ⟨y, zh, Rs, Ex, hF⟩ := fields4_of_accept (segFinP σ) hsem
  have hk := kindOfC_acc_seg hsem
  exact ⟨y, hF.sk, hR tr hsem hin, _, finRest4_full hphi ht hF (by rw [hk]; exact finTabs4_seg σ _)
    (dm_seg4 hF.sk) hb hin hπ (hW tr y zh Rs Ex hsem hin hF)⟩

/-- **`AcceptTail` from an accepted node run.** -/
theorem acceptTail4_node {impl : OpImpl} {ν : NodeKind} {cells : List ℕ} {inp : Input}
    {RejF : Log → Log → Prop} {W₀ : Log → Log → ℕ → K} {L : Log}
    (hphi : ∀ r a, r.size = 7 → impl.phiRS r a = Impl.phiRSS r a)
    (ht : ∀ j r, impl.tensorW j r = Impl.tensorWS j r)
    (hb : ¬ Bad L) (hπ : inp.π.size = piSizeOf seq4)
    (hrun : (runIR impl (gen4 seq4 (.ofNode ν) (finOps4 (nodeFinP ν cells))) inp).runLog L = some true)
    (hR : ∀ tr, semIR impl (gen4 seq4 (.ofNode ν) (finOps4 (nodeFinP ν cells))) inp tr = some true →
      (∀ e ∈ tr, e ∈ L) → ¬ RejF L (fsOf tr (itemsOf seq4)))
    (hW : ∀ tr y zh Rs Ex, semIR impl (gen4 seq4 (.ofNode ν) (finOps4 (nodeFinP ν cells))) inp tr = some true →
      (∀ e ∈ tr, e ∈ L) → Fields4 impl (.ofNode ν) inp tr (nodeFinP ν cells) y zh Rs Ex →
      wV4 impl (KindP.ofNode ν).tix ⟨(skeleton4 seq4 (.ofNode ν)).2.outs, zh, Ex 11⟩ (Rs 11) (nodeFinP ν cells) =
        T4.wHatL W₀ L (fsOf tr (itemsOf seq4)) 4) :
    ∃ j, T4.AcceptTail RejF W₀ P4b.c₀L4 L j := by
  refine acceptTail4_of_run _ hb hπ hrun fun tr hsem hin => ?_
  obtain ⟨y, zh, Rs, Ex, hF⟩ := fields4_of_accept (nodeFinP ν cells) hsem
  have hk := kindOfC_acc_node hsem
  exact ⟨y, hF.sk, hR tr hsem hin, _, finRest4_full hphi ht hF (by rw [hk]; exact finTabs4_node ν cells _)
    (dm_node4 hF.sk) hb hin hπ (hW tr y zh Rs Ex hsem hin hF)⟩

/-! ## Controls -/

/-- (−) **The tables are the kind's**: `L30`'s pad family is not `m*`'s, and `L32`'s chain is not
`L30`'s (`FinTabs4` fails at the wrong chain kind). -/
theorem finTabs4_ctl : (segFinP .L30).kv.selA .L32 = false ∧ ¬ FinTabs4 (segFinP .L30) .L32 (.seg .L32) :=
  ⟨rfl, fun h => by have := h.km; revert this; decide⟩

/-- (+/−) **`selI`**: the last selected index, `0` when none is. -/
theorem selI_ctl : selI (fun i => decide (i = 1)) 1 = 1 ∧ selI (fun _ => false) 3 = 0 := ⟨rfl, rfl⟩

/-- (+/−) **`padF4`**: `m*`'s family has the empty pad; `m = 30` has two factors. -/
theorem padF4_ctl (sfv : ℕ → K) : padF4 sfv 7 32 = 1 ∧ padF4 sfv 7 30 = (1 + sfv 5) * (1 + sfv 6) := by
  simp [padF4, List.range_succ]

/-- (+/−) **`tailOk4`**: with no tails it holds; it is the `and` of the tails' gated checks. -/
theorem tailOk4_ctl (P : FinP) (κ : Kind) (inp : Input) (hP : P.tails = []) : tailOk4 P κ inp = true := by
  simp [tailOk4, hP]

end FR.Snd.R4
