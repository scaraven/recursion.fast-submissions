-- New for lvm2 E2-FT (E2F-C2, from E2F-QH3's draft): the typed phases at S2GF in the circuit replay V_S's
-- (`typedGX` replays `LvmTypedVX.dTypedX`), the port of roll 11's `typedG_replays` (LvmQTypedHarZ/R/A/M/G) to
-- transcript amendment 1.
import LvmQTypedHarS
import LvmE2QTypedX
import LvmE2VPub
import LvmE2QHarFacts

/-!
# `typedGX` replays `dTypedX`

* **`zeroGX_replays`**: `zeroGX z g P` (gate on) replays `dZeroX` from `P` to `wGPX P`: `r_x` is the run's challenge
  cells, the six values its loaded cells.
* **`wireGX_replays`**: `wireGX` replays `dWiringX` from `wGPX P` to `rRPX P` (`virtGX`'s value is V_S's `virtEF`
  on the child's `PUB` at `acc_in` of `accV` coordinates, `virtGX_spec`).
* **`qaccTX_replays`**: `qaccTX` replays `dAccX` from `aPX P` to `mbPX P`, folding to the current proof's `acc_in`
  (`accCA accVF M pb`, its `PUB` cells).
* **`typedGX_replays`**, **`typed_phaseX`**: the composition (the relayout and the mini-bus are roll 11's
  `relayG_replays`, `miniG_replays`), as `Replays` and in the `PhaseAt` form `core_of_phasesF` takes.
-/

set_option autoImplicit false

namespace Lvm.E2Q

open Lvm Lvm.Loop Lvm.Loop.Build Lvm.QTyped Lvm.Q1 DM Lvm.Har
open Lvm.TypedV (TNat)


/-! ## The child's `PUB` lanes at `accV` variables (`pubOfA`, `pubLanesX`) -/

section Pub

open Lvm.QAcc

theorem range_splitA (F : Nat → FK) (accV : Nat) :
    (List.range (pubLanesX accV)).map F = [F 0] ++ ((List.range 4).map fun i => F (1 + i)) ++
      ((List.range 4).map fun i => F (5 + i)) ++ ((List.range 4).map fun i => F (9 + i)) ++ [F 13] ++
      ((List.range 4).map fun i => F (14 + i)) ++ ((List.range 597).map fun i => F (18 + i)) ++
      ((List.range (3 * (accV + 1))).map fun i => F (615 + i)) := by
  rw [show pubLanesX accV = 1 + 4 + 4 + 4 + 1 + 4 + 597 + 3 * (accV + 1) by unfold pubLanesX; omega]
  simp only [map_range_add, List.map_map, Function.comp_def, List.append_assoc]
  simp only [List.range_one, List.map_cons, List.map_nil, Nat.add_zero, Nat.zero_add, List.cons_append,
    List.nil_append, Nat.add_assoc, Nat.reduceAdd]

/-- **The child's `PUB` lanes at `accV` variables** are its stream's lanes from `11` (`pubOf_hdrLanes` with
`acc_in` of `accV + 1` scalars), except the key lanes `1 … 4`. -/
theorem pubOfA_hdrLanesS (accV : Nat) (vk c : Vector UInt8 32) (sig : ByteArray) :
    (Lvm.pubOfA accV vk c sig).hdrLanes = (List.range (pubLanesX accV)).map (hdrLaneS vk sig) := by
  have pos (i : Nat) (h : ¬ (1 ≤ i ∧ i < 5)) : hdrLaneS vk sig i = kAt sig (8 * (11 + i)) := by
    simp only [hdrLaneS, h, ite_false]
  have e0 : (⟨(Lvm.pubOfA accV vk c sig).b.toUInt64⟩ : FK) = hdrLaneS vk sig 0 := by
    rw [pos 0 (by omega)]
    simp only [Lvm.pubOfA, pubOf, kAt, Nat.toUInt64, UInt64.ofNat_toNat]; rfl
  have e1 : (Lvm.pubOfA accV vk c sig).vk = (List.range 4).map fun i => hdrLaneS vk sig (1 + i) := by
    show digestLanes vk = _
    conv_lhs => rw [list_eq_range_getD (digestLanes vk)]
    rw [show (digestLanes vk).length = 4 by simp [digestLanes]]
    apply List.map_congr_left; intro i hi
    simp only [List.mem_range] at hi
    simp [hdrLaneS, show 1 ≤ 1 + i ∧ 1 + i < 5 by omega]
  have seg (o k n : Nat) (ho : 5 ≤ k) (hk : headerAt o = 8 * (11 + k)) :
      ((List.range n).map fun i => kAt sig (headerAt o + 8 * i)) =
        (List.range n).map fun i => hdrLaneS vk sig (k + i) := by
    apply List.map_congr_left; intro i _
    rw [pos _ (by omega), hk, show 8 * (11 + k) + 8 * i = 8 * (11 + (k + i)) by ring]
  have e2 : (Lvm.pubOfA accV vk c sig).cL = (List.range 4).map fun i => hdrLaneS vk sig (5 + i) :=
    seg 48 5 4 (by omega) rfl
  have e3 : (Lvm.pubOfA accV vk c sig).s = (List.range 4).map fun i => hdrLaneS vk sig (9 + i) :=
    seg 80 9 4 (by omega) rfl
  have e4 : (⟨(Lvm.pubOfA accV vk c sig).n.toUInt64⟩ : FK) = hdrLaneS vk sig 13 := by
    rw [pos 13 (by omega)]
    simp only [Lvm.pubOfA, pubOf, kAt, Nat.toUInt64, UInt64.ofNat_toNat]; rfl
  have e5 : (Lvm.pubOfA accV vk c sig).h = (List.range 4).map fun i => hdrLaneS vk sig (14 + i) :=
    seg 120 14 4 (by omega) rfl
  have e6 : (Lvm.pubOfA accV vk c sig).sigLeaf = (List.range 597).map fun i => hdrLaneS vk sig (18 + i) := by
    simp only [Lvm.pubOfA, pubOf]
    rw [show sigBytes / 8 = 597 from rfl]
    exact seg 152 18 597 (by omega) rfl
  have hpos : ∀ i, headerAt (offAcc + eBytes * i) = 8 * (626 + 3 * i) := by
    intro i; simp only [headerAt, offAcc, eBytes, sigBytes]; omega
  have e7 : ((Lvm.pubOfA accV vk c sig).accIn.pt ++ [(Lvm.pubOfA accV vk c sig).accIn.y]).flatMap FE.lanes =
      (List.range (3 * (accV + 1))).map fun i => hdrLaneS vk sig (615 + i) := by
    have : (Lvm.pubOfA accV vk c sig).accIn.pt ++ [(Lvm.pubOfA accV vk c sig).accIn.y] =
        (List.range (accV + 1)).map fun j => feAt sig (8 * (626 + 3 * j)) := by
      simp only [Lvm.pubOfA, hpos]
      rw [List.range_succ, List.map_append, List.map_singleton]
    rw [this, flatMap_feAt sig 626 (accV + 1)]
    apply List.map_congr_left; intro i _
    rw [pos _ (by omega), show 11 + (615 + i) = 626 + i by omega]
  rw [range_splitA]
  simp only [Pub.hdrLanes, List.append_assoc]
  rw [e0, e1, e2, e3, e4, e5, e6, e7]

end Pub

section
variable {c : Ctx} {M : Mem} {sig : ByteArray} {T : Nat}

theorem wGPX_eq (P : Nat) : wGPX P = P + 4056 := by simp only [wGPX, zAbcPX, zRPX, tX]

/-- **The coordinate-split zerocheck replayed** (soundness direction): wherever `zeroGX`'s rows hold and assert
(gate on), `dZeroX` from any state at position `P` with `ok` keeps `ok`, ends at `wGPX P`; `r_x` is the output's
first list's values, the six values the second's. -/
theorem zeroGX_replays (hS : Streamed M sig T) {z g : Cell} (hz : z.val M = 0)
    (hg : g.val M = 1) {P : Nat} (hP : P % 8 = 0) (hT : wGPX P + 40 ≤ 8 * T) (ptr : Ptr) :
    Replays c M sig TypedV.dZeroX (zeroGX z g P) ptr P (wGPX P) fun v t =>
      v.1 = vs M t.1 ∧ v.2 = vs M t.2 ∧ t.1.length = 20 ∧ (∀ x ∈ t.1, x.ty = .E) ∧ t.2.length = 6 ∧
        (∀ x ∈ t.2, x.ty = .E) := by
  rw [wGPX_eq] at hT ⊢
  refine z_replays_of ?_
  unfold zeroGX
  refine z_soundAt_bind (z_soundAt_of (ldEsP_sound hS ((P + 40) / 8) 9 tX fun i hi => by simp only [tX] at hi; omega) _)
    fun tb htb => ?_
  refine z_soundAt_bind (z_ldE_at hS (a := (P + 72 * tX + 40) / 8) (by simp only [tX]; omega) _) fun om hom => ?_
  refine z_soundAt_getPtr ?_
  refine z_soundAt_bind (z_scQ3_at hS tX _ tb.1 z _ ((List.range tX).map fun i => feAt sig (P + 40 + 72 * i))
    (by simp) (fun i hi => by rw [htb.2 i hi, QB.getD_map_range _ _ hi]; congr 1; omega)
    (by simp only [zRPX, tX]; omega)) fun fin hfin => ?_
  refine z_soundAt_bind (z_soundAt_of (z_ldEs_soundE hS ((zAbcPX P + 40) / 8) 3 6 fun i hi => by
    simp only [zAbcPX, zRPX, tX]; omega) _) fun v hv => ?_
  refine z_soundAt_bind (z_soundAt_of (soundG_aspec (QB.aspec_mulAdd .E _ _ _)) _) fun t0 ht0 => ?_
  refine z_soundAt_bind (z_soundAt_of (soundG_aspec (QB.aspec_mulAdd .E _ _ _)) _) fun r0 hr0 => ?_
  refine z_soundAt_bind (z_soundAt_of (soundG_aspec (QB.aspec_mulAdd .E _ _ _)) _) fun p11 hp11 => ?_
  refine z_soundAt_bind (z_soundAt_of (soundG_aspec (QB.aspec_lin _ _ _ _ _)) _) fun t1 ht1 => ?_
  refine z_soundAt_bind (z_soundAt_of (soundG_aspec (QB.aspec_mulAdd .E _ _ _)) _) fun t2 ht2 => ?_
  refine z_soundAt_bind (z_soundAt_of (soundG_aspec (QB.aspec_mulAdd .E _ _ _)) _) fun r1 hr1 => ?_
  refine z_soundAt_bind (z_soundAt_of (soundG_aspec (QB.aspec_mulAdd .E _ _ _)) _) fun t ht => ?_
  refine z_soundAt_bind (z_soundAt_of (soundG_aspec (QB.aspec_assertEq _ _ _)) _) fun _ hA => ?_
  refine z_soundAt_pure ?_
  intro s hs hok
  simp only [pos] at hs
  simp only [TypedV.dZeroX, Q1.bind_run, Q1.samples_run sig _ s (by decide : 1 ≤ Lvm.Typed.xVars), Q1.sampleE_run,
    Q1.pure_run, Q1.readEs_run, Lvm.Har.require_run, hs, hok]
  have homv : om.val M = feAt sig (P + 72 * tX + 40) := by rw [hom]; congr 1; simp only [tX]; omega
  rw [hz] at hfin
  obtain ⟨h1, h2⟩ := hfin ⟨P + 72 * (tX + 1), 0, true⟩ rfl (by simp only [zRPX]; omega)
  have hst := congrArg Prod.snd (QB.sumcheck_run 3 (by decide) sig
    ((List.map (fun i => feAt sig (P + 40 + 72 * i)) (List.range tX)).map some) 0 ⟨P + 72 * (tX + 1), 0, true⟩ rfl)
  have hlen := sumcheck_len 0 3 (by decide)
    ((List.map (fun i => feAt sig (P + 40 + 72 * i)) (List.range tX)).map some) sig ⟨P + 72 * (tX + 1), 0, true⟩ rfl
  have hent : P + 72 * Lvm.Typed.xVars + 72 + 0 = P + 72 * (tX + 1) := by simp only [tX, Lvm.Typed.xVars]
  have hans : P + 72 * Lvm.Typed.xVars + 40 + 0 = P + 72 * tX + 40 := by simp only [tX, Lvm.Typed.xVars]
  simp only [hent, hans] at *
  generalize sumcheck 0 3 _ sig _ = R at h1 h2 hst hlen ⊢
  rw [hst]
  have hab : scalarsAt (feAt sig) (P + 72 * (tX + 1) + QB.entB (3 - 1) * tX + 0 + 40) 6 = vs M v := by
    rw [hv.1, scalarsAt]
    refine List.map_congr_left fun i _ => congrArg _ ?_
    simp only [zAbcPX, zRPX, tX, QB.entB]; omega
  simp only [List.length_map, List.length_range] at hst hlen ⊢
  rw [hab]
  simp only [z_getD_vs v z, hz] at ht0 hr0 hp11 ht1 ht2 hr1
  have hfa := (QB.gate_eq_iff hg _ _).mp hA.2
  refine ⟨?_, ?_, ?_, rfl, ?_, ?_, ?_, hv.2⟩
  · rw [Bool.and_true, QB.FE.beq_iff, ← h1, hfa, ht.1, hr1.1, ht2.1, ht1.1, hp11.1, hr0.1, ht0.1, homv, ofK_zero]
    ring
  · simp only [pos, QB.entB, tX]
  · apply List.ext_getElem (by simp [vs, hlen])
    intro i h1' h2'
    simp only [vs, List.map_map, List.getElem_map, List.getElem_range, Function.comp_apply, Cell.val_E]
    rw [h2 i (by simpa [hlen] using h1'), List.getD_eq_getElem _ _ h1']
  · simp
  · intro x hx
    simp only [List.mem_map, List.mem_range] at hx
    obtain ⟨i, _, rfl⟩ := hx
    rfl
  · simpa [vs] using congrArg List.length hv.1

end

/-! ## `PUB` and `acc_in` of the child at `acc_in` of `accV` coordinates -/

section PubEval

open Lvm.QAcc Lvm.QSig

/-- `pubEval` of the child's `PUB` lanes at `accV` (`pubEval_child` at `pubLanesX accV` lanes). -/
theorem pubEval_childA (accV : Nat) {M : Mem} {sig : ByteArray} {T : Nat} (hS : Streamed M sig T)
    (hT : 11 + pubLanesX accV ≤ T) {vk : Vector UInt8 32} (c : Vector UInt8 32) {vkc : Nat}
    (hvk : ∀ i < 4, M.k (vkc + i) = (digestLanes vk).getD i 0) (pt : List FE)
    (hn : pubLanesX accV ≤ 2 ^ pt.length) :
    M3.pubEval (Lvm.pubOfA accV vk c sig).hdrLanes pt =
      ∑ i ∈ Finset.range (pubLanesX accV), eqW pt i * FE.ofK (pubLane M 11 vkc i) := by
  rw [M3.pubEval_eq, mle_eq_sum, pubOfA_hdrLanesS]
  obtain ⟨m, hm⟩ : ∃ m, 2 ^ pt.length = pubLanesX accV + m := ⟨_, (Nat.add_sub_cancel' hn).symm⟩
  rw [hm, Finset.sum_range_add]
  have h0 : ∑ x ∈ Finset.range m, eqW pt (pubLanesX accV + x) *
      FE.ofK (M3.pubCell ((List.range (pubLanesX accV)).map (hdrLaneS vk sig)) (pubLanesX accV + x)) = 0 := by
    apply Finset.sum_eq_zero; intro x _
    simp [M3.pubCell, List.getD_eq_getElem?_getD, ofK_zero]
  rw [h0, add_zero]
  apply Finset.sum_congr rfl; intro i hi
  rw [Finset.mem_range] at hi
  refine congrArg (fun x => eqW pt i * FE.ofK x) ?_
  simp only [M3.pubCell, List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range hi,
    Option.map_some, Option.getD_some, hdrLaneS, pubLane]
  split_ifs with h
  · rw [hvk _ (by omega), List.getD_eq_getElem?_getD]
  · rw [hS _ (by omega)]

/-- The child's `acc_in` at `accV` coordinates at the stream lanes `accLane`. -/
theorem pubOfA_accIn (accV : Nat) (vk cL : Vector UInt8 32) (sig : ByteArray) :
    (Lvm.pubOfA accV vk cL sig).accIn.y = feAt sig (8 * accLane accV) ∧
      (Lvm.pubOfA accV vk cL sig).accIn.pt = (List.range accV).map fun i => feAt sig (8 * accLane i) := by
  have hacc : ∀ i, headerAt (offAcc + eBytes * i) = 8 * accLane i := by
    intro i; simp only [headerAt, offAcc, eBytes, sigBytes, accLane]; omega
  refine ⟨?_, ?_⟩
  · show feAt sig (headerAt (offAcc + eBytes * accV)) = _; rw [hacc]
  · show (List.range accV).map (fun i => feAt sig (headerAt (offAcc + eBytes * i))) = _
    simp only [hacc]

end PubEval

section
variable {c : Ctx} {M : Mem} {sig : ByteArray} {T : Nat}

/-! ## The wiring over the six values -/

/-- **`virtGX`'s value is V_S's `virtEF`** at `r_y` on the child's `PUB` at `acc_in` of `accV` coordinates
(`virtG_spec` at `pubLanesX accV` lanes). -/
theorem virtGX_spec (accV : Nat) (vk cL : Vector UInt8 32) (hS : Streamed M sig T)
    (hH : 11 + pubLanesX accV ≤ T) (hA : pubLanesX accV ≤ 2 ^ 10) {z o : Cell}
    (hz : z.val M = 0) (ho : o.val M = 1) (hzE : z.ty = .E) (hoE : o.ty = .E) {Td : TData} {N : TNat}
    (htd : TdOk Td N) {pb : Nat} (hvk : ∀ i < 4, M.k (pb + 1 + i) = (digestLanes vk).getD i 0) (ry : List Cell)
    (hry : ry.length = 21) (hryE : ∀ x ∈ ry, x.ty = .E) (q : Ptr)
    (h : SegsHold c M q (virtGX z o Td pb (pubLanesX accV) ry q).2) :
    (virtGX z o Td pb (pubLanesX accV) ry q).1.val M =
      TypedV.virtEF N (Lvm.pubOfA accV vk cL sig) (vs M ry) := by
  have hone : M.e o.n = 1 := by rw [← ho]; rcases o with ⟨τ, n⟩; simp only at hoE; subst hoE; rfl
  have hal : ∀ i, (ry.getD i z).ty = .E := fun i => by
    rw [List.getD_eq_getElem?_getD]
    cases h : ry[i]? with
    | none => exact hzE
    | some y => exact hryE y (List.mem_of_getElem? h)
  have hvl : (vs M ry).length = 21 := by simp [vs, hry]
  have hpt : (List.range 10).map (fun i => (ry.getD i z).val M) = (vs M ry).take 10 := by
    apply List.ext_getElem (by simp [hvl])
    intro i h1 h2
    simp only [List.length_map, List.length_range] at h1
    rw [List.getElem_map, List.getElem_range, List.getElem_take, z_getD_vs, List.getD_eq_getElem _ _ (by omega)]
  have hqp : ∀ p : Ptr, z_HoldAt c M (Lvm.QAcc.qpub (fun i => ry.getD i z) z o 10 11 (pb + 1) (pubLanesX accV)) p
      fun v => v.val M = M3.pubEval (Lvm.pubOfA accV vk cL sig).hdrLanes ((vs M ry).take 10) := fun p h => by
    refine (Lvm.QAcc.qpub_spec hz hal hone hA h).trans ?_
    rw [hpt, pubEval_childA accV hS hH cL hvk _ (by rw [List.length_take, hvl]; exact hA)]
  have key : z_HoldAt c M (virtGX z o Td pb (pubLanesX accV) ry) q fun w => w.val M =
      TypedV.hiW (vs M ry) 10 Td.pub * M3.pubEval (Lvm.pubOfA accV vk cL sig).hdrLanes ((vs M ry).take 10) +
        TypedV.hiW (vs M ry) 0 Td.one := by
    simp only [virtGX, regSelG, htd.qlt, Lvm.Loop.Build.add]
    refine z_holdAt_bind (z_eqConstG_hold hz ho _ _ _) fun sP hsP => ?_
    refine z_holdAt_bind (hqp _) fun vP hvP => ?_
    refine z_holdAt_bind (z_holdAt_mulAdd .E sP vP z _) fun w hw => ?_
    refine z_holdAt_bind (z_eqConstG_hold hz ho ry Td.one _) fun e1 he1 => ?_
    refine z_holdAt_bind (z_holdAt_lin _ 1 0 w e1 _) fun w' hw' => z_holdAt_pure ?_
    rw [hw', ofK_one, ofK_zero, one_mul, add_zero, hw, hz, add_zero, hsP, hvP, he1]
    simp only [TypedV.hiW, vs, List.map_drop, List.drop_zero, Nat.shiftRight_zero]
  rw [key h, z_virtEF_td htd, z_mleK_pub _ _ (by omega)]

theorem z_virtGX_at (accV : Nat) (vk cL : Vector UInt8 32) (hS : Streamed M sig T)
    (hH : 11 + pubLanesX accV ≤ T) (hA : pubLanesX accV ≤ 2 ^ 10) {z o : Cell}
    (hz : z.val M = 0) (ho : o.val M = 1) (hzE : z.ty = .E) (hoE : o.ty = .E) {Td : TData} {N : TNat}
    (htd : TdOk Td N) {pb : Nat} (hvk : ∀ i < 4, M.k (pb + 1 + i) = (digestLanes vk).getD i 0) (ry : List Cell)
    (hry : ry.length = 21) (hryE : ∀ x ∈ ry, x.ty = .E) (q : Ptr) :
    z_SoundAt c M (virtGX z o Td pb (pubLanesX accV) ry) q fun w =>
      w.val M = TypedV.virtEF N (Lvm.pubOfA accV vk cL sig) (vs M ry) :=
  fun h _ => virtGX_spec accV vk cL hS hH hA hz ho hzE hoE htd hvk ry hry hryE q h

/-- Horner's rule in the circuit (`hornerG`). -/
theorem hornerG_sound (γ : Cell) : ∀ (xs : List Cell) (acc : Cell),
    SoundG c M (hornerG γ xs acc) fun r => r.val M = xs.foldl (fun a x => γ.val M * a + x.val M) (acc.val M)
  | [], _ => soundG_pure rfl
  | x :: xs, acc => by
    rw [hornerG]
    exact soundG_bind (soundG_aspec (QB.aspec_mulAdd .E γ acc x)) fun a ha =>
      soundG_mono (hornerG_sound γ xs a) fun r hr => by rw [hr, ha.1]; rfl

/-- **`batch6G`'s value**: `Σ_{k<6} γ^k v_k` (V_S's initial claim of the wiring). -/
theorem batch6G_sound {z γ : Cell} {v : List Cell} (hv : v.length = 6) :
    SoundG c M (batch6G z γ v) fun c0 =>
      c0.val M = ((List.range 6).map fun k => γ.val M ^ k * (vs M v).getD k 0).sum := by
  match v, hv with
  | [a0, a1, a2, a3, a4, a5], _ =>
    rw [batch6G]
    simp only [List.take_succ_cons, List.take_zero, List.reverse_cons, List.reverse_nil, List.nil_append,
      List.cons_append, List.drop_succ_cons, List.drop_zero, List.getD_cons_succ, List.getD_cons_zero]
    refine soundG_mono (hornerG_sound γ [a4, a3, a2, a1, a0] a5) fun r hr => ?_
    rw [hr]
    simp [vs, List.range_succ]
    ring

/-- **The wiring over the six values replayed** (soundness direction): wherever `wireGX`'s rows hold and assert
(gate on), `dWiringX` on the zerocheck's six values from any state at `wGPX P` with `ok` keeps `ok`, ends at
`rRPX P`; `r_y`, the eight matrix values and the four region values are the output's cells' values. -/
theorem wireGX_replays (accV : Nat) (vk cL : Vector UInt8 32) (hS : Streamed M sig T)
    (hH : 11 + pubLanesX accV ≤ T) (hA : pubLanesX accV ≤ 2 ^ 10) {z o g : Cell}
    (hz : z.val M = 0) (ho : o.val M = 1) (hzE : z.ty = .E) (hoE : o.ty = .E) (hg : g.val M = 1)
    {Td : TData} {N : TNat} (htd : TdOk Td N) {pb : Nat}
    (hvk : ∀ i < 4, M.k (pb + 1 + i) = (digestLanes vk).getD i 0) {P : Nat} (hP : P % 8 = 0)
    (hT : rRPX P + 40 ≤ 8 * T) (v : List Cell) (hv : v.length = 6) (ptr : Ptr) :
    Replays c M sig (TypedV.dWiringX N (Lvm.pubOfA accV vk cL sig) (vs M v))
      (wireGX z o g Td pb P (pubLanesX accV) v) ptr (wGPX P) (rRPX P) fun r t =>
        r.1 = vs M t.1 ∧ r.2.1 = vs M t.2.1 ∧ r.2.2 = vs M t.2.2 ∧ t.1.length = 21 ∧ (∀ x ∈ t.1, x.ty = .E) ∧
          t.2.1.length = 8 ∧ (∀ x ∈ t.2.1, x.ty = .E) ∧ t.2.2.length = 4 ∧ (∀ x ∈ t.2.2, x.ty = .E) := by
  have hW : wGPX P = P + 4056 := wGPX_eq P
  have hR : rRPX P = P + 6936 := by simp only [rRPX, wVPX, wRPX, wGPX, zAbcPX, zRPX, tX, tY]
  have hV : wVPX P = P + 6648 := by simp only [wVPX, wRPX, wGPX, zAbcPX, zRPX, tX, tY]
  have hRP : wRPX P = P + 4128 := by simp only [wRPX, wGPX, zAbcPX, zRPX, tX]
  rw [hR] at hT
  rw [hW, hR]
  refine z_replays_of ?_
  unfold wireGX
  rw [hW, hV, hRP]
  refine z_soundAt_bind (z_ldE_at hS (a := (P + 4056 + 40) / 8) (by omega) _) fun γ hγ => ?_
  refine z_soundAt_bind (z_soundAt_of (batch6G_sound hv) _) fun c0 hc0 => ?_
  refine z_soundAt_getPtr ?_
  refine z_soundAt_bind (z_scP3_at hS tY ((P + 4128) / 8) c0 _ (by simp only [tY]; omega)) fun fin hfin => ?_
  refine z_soundAt_bind (z_soundAt_of (z_ldEs_soundE hS ((P + 6648 + 40) / 8) 3 8 fun i hi => by omega) _)
    fun vC hvC => ?_
  refine z_soundAt_bind (z_soundAt_of (z_ldEs_soundE hS ((P + 6648 + 40) / 8 + 24) 3 4 fun i hi => by omega) _)
    fun rC hrC => ?_
  refine z_soundAt_bind (z_soundAt_of (soundG_aspec (QB.aspec_lin _ 1 0 _ _)) _) fun d1 hd1 => ?_
  refine z_soundAt_bind (z_soundAt_of (soundG_aspec (QB.aspec_lin _ 1 0 _ _)) _) fun d0 hd0 => ?_
  refine z_soundAt_bind (z_soundAt_of (soundG_aspec (QB.aspec_mulAdd .E _ _ _)) _) fun m4 hm4 => ?_
  refine z_soundAt_bind (z_soundAt_of (soundG_aspec (QB.aspec_mulAdd .E _ _ _)) _) fun m3 hm3 => ?_
  refine z_soundAt_bind (z_soundAt_of (soundG_aspec (QB.aspec_mulAdd .E _ _ _)) _) fun m2 hm2 => ?_
  refine z_soundAt_bind (z_soundAt_of (soundG_aspec (QB.aspec_mulAdd .E _ _ _)) _) fun m1 hm1 => ?_
  refine z_soundAt_bind (z_soundAt_of (soundG_aspec (QB.aspec_mulAdd .E _ _ _)) _) fun m0 hm0 => ?_
  refine z_soundAt_bind (z_virtGX_at accV vk cL hS hH hA hz ho hzE hoE htd hvk _ (by simp) (by
    intro x hx
    simp only [List.mem_map, List.mem_range] at hx
    obtain ⟨i, _, rfl⟩ := hx
    rfl) _) fun ve hve => ?_
  refine z_soundAt_bind (z_soundAt_of (sumG_sound hz _) _) fun sC hsC => ?_
  refine z_soundAt_bind (z_soundAt_of (soundG_aspec (QB.aspec_mulAdd .E _ _ _)) _) fun pr hpr => ?_
  refine z_soundAt_bind (z_soundAt_of (soundG_aspec (QB.aspec_assertEq _ _ _)) _) fun _ hA' => ?_
  refine z_soundAt_pure ?_
  intro s hs hok
  simp only [pos] at hs
  simp only [TypedV.dWiringX, Q1.bind_run, Q1.sampleE_run, Q1.pure_run, Q1.readEs_run, Lvm.Har.require_run, hok]
  have e1 : s.ent + 40 + s.msg = P + 4056 + 40 := by omega
  have e2 : s.ent + 72 + s.msg = P + 4128 := by omega
  rw [e1, e2]
  have hγ' : γ.val M = feAt sig (P + 4056 + 40) := by rw [hγ]; congr 1; omega
  have hcl : c0.val M = ((List.range 6).map fun k => feAt sig (P + 4056 + 40) ^ k * (vs M v).getD k 0).sum := by
    rw [hc0, hγ']
  rw [hcl] at hfin
  obtain ⟨h1, h2⟩ := hfin ⟨P + 4128, 0, true⟩ rfl (by dsimp only; omega)
  have hst := congrArg Prod.snd (QB.sumcheck_run 3 (by decide) sig (List.replicate tY none) (c0.val M)
    ⟨P + 4128, 0, true⟩ rfl)
  have hlen := sumcheck_len (c0.val M) 3 (by decide) (List.replicate tY none) sig ⟨P + 4128, 0, true⟩ rfl
  rw [hcl] at hlen hst
  generalize sumcheck _ 3 _ sig _ = R at h1 h2 hst hlen ⊢
  simp only [List.length_replicate] at hst hlen
  rw [hst]
  rw [← h2] at hve
  have hv8 : ∀ s' : RS, s' = ⟨P + 4128 + QB.entB (3 - 1) * tY, 0, true⟩ →
      scalarsAt (feAt sig) (s'.ent + s'.msg + 40) 8 = vs M vC := by
    rintro s' rfl
    rw [hvC.1, scalarsAt]
    refine List.map_congr_left fun i _ => congrArg _ ?_
    simp only [QB.entB, tY]; omega
  have hr4 : ∀ s' : RS, s' = ⟨P + 4128 + QB.entB (3 - 1) * tY, 0, true⟩ →
      scalarsAt (feAt sig) (s'.ent + (s'.msg + 24 * 8) + 40) 4 = vs M rC := by
    rintro s' rfl
    rw [hrC.1, scalarsAt]
    refine List.map_congr_left fun i _ => congrArg _ ?_
    simp only [QB.entB, tY]; omega
  rw [hv8 _ rfl, hr4 _ rfl]
  dsimp only
  simp only [z_getD_vs vC z, hz] at hd1 hd0 hm4 hm3 hm2 hm1 hm0
  have hsC' : sC.val M = sumE (vs M rC) + ve.val M := by
    rw [hsC, show vs M (rC ++ [ve]) = vs M rC ++ [ve.val M] by simp [vs], sumE_append, sumE_cons, sumE_nil,
      add_zero]
  refine ⟨?_, ?_, h2, rfl, rfl, by simp, ?_, ?_, hvC.2, ?_, hrC.2⟩
  · rw [Bool.and_true, QB.FE.beq_iff, ← h1, (QB.gate_eq_iff hg _ _).mp hA'.2, hpr.1, hz, add_zero, hsC', hve,
      hm0.1, hm1.1, hm2.1, hm3.1, hm4.1, hd1.1, hd0.1, hγ', ofK_one, ofK_zero, one_mul, add_zero, add_zero,
      TypedV.wGXF]
    ring
  · simp only [pos, QB.entB, tY]
  · intro x hx
    simp only [List.mem_map, List.mem_range] at hx
    obtain ⟨i, _, rfl⟩ := hx
    rfl
  · simpa [vs] using congrArg List.length hvC.1
  · simpa [vs] using congrArg List.length hrC.1

/-! ## A23 at `Φ_Q` in 44 variables -/

section helpers
open Lvm.QAcc Lvm.QSig

attribute [local irreducible] Lvm.QAcc.horner Lvm.QAcc.macChain Lvm.QAcc.linePts in
set_option maxHeartbeats 1000000 in
/-- **`qaccTX`'s facts** (gate on, the child's stream bound): the five equations of A23 on `feAt Σ` (`qaccT_facts`
at `κ` of 3 samples, `h` of 45 scalars, the current `acc_in` at 44 coordinates). -/
theorem qaccTX_facts {L pb : Nat} {p : Ptr} (hS : Streamed M sig T) (hT : L + 178 < T)
    (hH : 11 + pubLanesX accVF ≤ T) (hg : M.k pb = 1)
    (rx ry v : List Cell) (hrx : rx.length = 20) (hry : ry.length = 21) (hv : v.length = 8)
    (h : Lvm.QSig.Ok c M (qaccTX L pb rx ry v) p) :
    let K := (List.range 3).map fun i => feAt sig (8 * (L + 5 + 9 * i))
    let H := (List.range 45).map fun j => feAt sig (8 * (L + 27 + 5 + 3 * j))
    let t := feAt sig (8 * (L + 27 + 3 * 45 + 5))
    H.headD 0 = feAt sig (8 * accLane 44) ∧ sumE H = Lvm.dot (eqKernel K) (vs M v) ∧
      accLine ((List.range 44).map fun i => feAt sig (8 * accLane i)) (K ++ vs M (rx ++ ry)) t =
        (accCA accVF M pb).pt ∧
      polyEval H t = (accCA accVF M pb).y ∧ feAt sig (8 * (L + 27 + 3 * 45 + 9 + 5)) = 0 := by
  have hD : tVarsX = 44 := rfl
  have hPL : pubLanesX accVF = 750 := rfl
  have hgv : (kc pb).val M = 1 := kc_val_one hg
  unfold qaccTX at h
  obtain ⟨zo, p1, evo1, epo1, o1, h⟩ := okBindE h
  obtain ⟨hz1, hz2, hz0, hone⟩ := consts_spec o1.1
  have hzv : (consts pb p).1.1.val M = 0 := by rw [hz1]; exact hz0
  have hov : M.e (consts pb p).1.2.n = 1 := by rw [hz2]; exact hone
  have hov' : (consts pb p).1.2.val M = 1 := by rw [hz2]; exact hone
  rw [evo1] at hzv hov hov'
  -- κ
  obtain ⟨kb, p2, evo2, epo2, o2, h⟩ := okBindE h
  have hk := ldEsB_spec hS (qs := (List.range 3).map fun i => L + 5 + 9 * i)
    (by intro q hq; simp only [List.mem_map, List.mem_range] at hq; obtain ⟨i, hi, rfl⟩ := hq; omega) o2.1
  rw [evo2] at hk
  -- y'
  obtain ⟨y, p5, evo5, epo5, o5, h⟩ := okBindE h
  have hy := qyown_spec (by omega : 1 ≤ 3) (by rw [hv]; decide) hzv hov o5.1
  rw [evo5] at hy
  -- h', acc_in'
  obtain ⟨hb, p6, evo6, epo6, o6, h⟩ := okBindE h
  have hh := ldEsB_spec hS (qs := (List.range (tVarsX + 1)).map fun j => L + 27 + 5 + 3 * j)
    (by intro q hq; simp only [List.mem_map, List.mem_range] at hq; obtain ⟨i, hi, rfl⟩ := hq; omega) o6.1
  rw [evo6] at hh
  obtain ⟨ab, p7, evo7, epo7, o7, h⟩ := okBindE h
  have ha := ldEsB_spec hS (qs := (List.range (tVarsX + 1)).map accLane)
    (by intro q hq; simp only [List.mem_map, List.mem_range] at hq; obtain ⟨i, hi, rfl⟩ := hq
        simp only [accLane]; omega) o7.1
  rw [evo7] at ha
  obtain ⟨_vo8, p8, evo8, epo8, o8, h⟩ := okBindE h
  have e8 := assertEqE_spec o8 hgv
  obtain ⟨sh, p9, evo9, epo9, o9, h⟩ := okBindE h
  have hsh := macChain_spec _ _ _ o9.1
  rw [evo9] at hsh
  obtain ⟨_vo10, p10, evo10, epo10, o10, h⟩ := okBindE h
  have e10 := assertEqE_spec o10 hgv
  -- t', h'(t'), the line
  obtain ⟨t, p11, evo11, epo11, o11, h⟩ := okBindE h
  have ht := ldE_feAt hS (q := L + 27 + 3 * (tVarsX + 1) + 5) (by omega) o11.1
  rw [evo11] at ht
  obtain ⟨hv', p12, evo12, epo12, o12, h⟩ := okBindE h
  have hhv := horner_spec (c := c) (M := M) t zo.1 hzv ((List.range (tVarsX + 1)).map fun j => ec (hb + j)) p11
    o12.1
  rw [evo12] at hhv
  obtain ⟨pts, p13, evo13, epo13, o13, h⟩ := okBindE h
  have hpt := linePts_spec (c := c) (M := M) t ((List.range tVarsX).map fun i =>
    (ec (ab + i), (((List.range 3).map (fun j => ec (kb + j)) ++ rx ++ ry).getD i (ec 0)))) p12 o13.1
  rw [evo13] at hpt
  -- the current acc_in
  obtain ⟨pc, p14, evo14, epo14, o14, h⟩ := okBindE h
  have hpc := ldEsB_val (c := c) (M := M) (qs := (List.range (tVarsX + 1)).map fun j => pb + 615 + 3 * j)
    (p := p13) o14.1
  rw [evo14] at hpc
  obtain ⟨_vo15, p15, evo15, epo15, o15, h⟩ := okBindE h
  have e15 := assertEqs_spec (c := c) (M := M) hgv
    ((List.range tVarsX).map fun i => (pts.getD i default, ec (pc + i))) p14 o15
  obtain ⟨_vo16, p16, evo16, epo16, o16, h⟩ := okBindE h
  have e16 := assertEqE_spec o16 hgv
  obtain ⟨zz, _qo17, evo17, epo17, o17, h⟩ := okBindE h
  have hz := ldE_feAt hS (q := L + 27 + 3 * (tVarsX + 1) + 9 + 5) (by omega) o17.1
  rw [evo17] at hz
  have e17 := assert0_spec h.2
  rw [hgv, one_mul] at e17
  have h45 : tVarsX + 1 = 45 := rfl
  rw [h45] at hh ha hpc ht hz hhv
  rw [hD] at e8 hpt e15 e16
  have hkv : ∀ i < 3, M.e (kb + i) = feAt sig (8 * (L + 5 + 9 * i)) := by
    intro i hi; rw [hk i (by simpa using hi)]; simp [List.getD_eq_getElem?_getD, List.getElem?_range hi]
  have hhv' : ∀ j < 45, M.e (hb + j) = feAt sig (8 * (L + 27 + 5 + 3 * j)) := by
    intro j hj; rw [hh j (by simpa using hj)]; simp [List.getD_eq_getElem?_getD, List.getElem?_range hj]
  have hav : ∀ j < 45, M.e (ab + j) = feAt sig (8 * accLane j) := by
    intro j hj; rw [ha j (by simpa using hj)]; simp [List.getD_eq_getElem?_getD, List.getElem?_range hj]
  have hHl : (List.range 45).map (fun j => feAt sig (8 * (L + 27 + 5 + 3 * j))) =
      ((List.range 45).map fun j => ec (hb + j)).map (Cell.val M) := by
    rw [List.map_map]; apply List.map_congr_left; intro j hj; rw [List.mem_range] at hj
    simp [hhv' j hj]
  have hKv : (List.range 3).map (fun i => M.e (kb + i)) =
      (List.range 3).map fun i => feAt sig (8 * (L + 5 + 9 * i)) := by
    apply List.map_congr_left; intro i hi; rw [List.mem_range] at hi; exact hkv i hi
  dsimp only
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · rw [List.range_succ_eq_map, List.map_cons, List.headD_cons]
    have := hhv' 0 (by omega)
    rw [Nat.add_zero] at this
    rw [← this, ← hav 44 (by omega)]; exact e8
  · have hsum : sh.val M = ((List.range 45).map fun j => feAt sig (8 * (L + 27 + 5 + 3 * j))).sum := by
      rw [hsh, hzv, zero_add, List.map_map, hHl, List.map_map]
      congr 1; apply List.map_congr_left; intro j _
      simp [hov']
    rw [Lvm.Har.sumE_eq, ← hsum, e10, hy, dot_eqKernel _ _ (by simp [vs, hv]), hKv]
    simp only [vs, List.length_map]
    refine Finset.sum_congr rfl fun k hk => ?_
    rw [Finset.mem_range] at hk
    rw [List.getD_eq_getElem _ _ hk, List.getD_eq_getElem _ _ (by simpa using hk), List.getElem_map]
  · have hbc : ((List.range 3).map (fun j => ec (kb + j)) ++ rx ++ ry).map (Cell.val M) =
        (List.range 3).map (fun i => feAt sig (8 * (L + 5 + 9 * i))) ++ vs M (rx ++ ry) := by
      rw [← hKv, List.append_assoc, List.map_append, List.map_map]; rfl
    have hbl : ((List.range 3).map (fun j => ec (kb + j)) ++ rx ++ ry).length = 44 := by
      simp [hrx, hry]
    rw [← hbc, ← ht]
    apply List.ext_getElem
    · simp [accLine, accCA, List.length_zipWith, hrx, hry, accVF]
    intro i h1 h2
    have hi : i < 44 := by simpa [accCA, accVF] using h2
    have hpi := hpt.2 i (by simpa using hi)
    rw [List.getD_eq_getElem ((List.range 44).map fun i =>
        (ec (ab + i), ((List.range 3).map (fun j => ec (kb + j)) ++ rx ++ ry).getD i (ec 0))) _ (by simpa using hi),
      List.getElem_map, List.getElem_range,
      List.getD_eq_getElem ((List.range 3).map (fun j => ec (kb + j)) ++ rx ++ ry) _ (by rw [hbl]; exact hi)] at hpi
    have hq := e15 ((pts.getD i default, ec (pc + i))) (List.mem_map.mpr ⟨i, List.mem_range.mpr hi, rfl⟩)
    have hpci : M.e (pc + i) = ⟨M.k (pb + 615 + 3 * i), M.k (pb + 615 + 3 * i + 1),
        M.k (pb + 615 + 3 * i + 2)⟩ := by
      rw [hpc i (by simp; omega)]
      simp [List.getD_eq_getElem?_getD, List.getElem?_range (by omega : i < 45)]
    simp only [Cell.val_E] at hq hpi
    rw [hq, hpci, hav i (by omega)] at hpi
    simp only [accLine, List.getElem_zipWith, List.getElem_map, List.getElem_range, accCA]
    exact hpi.symm
  · rw [hHl, ← ht, ← hhv, e16, Cell.val_E, hpc 44 (by simp)]
    simp [accCA, List.getD_eq_getElem?_getD, accVF]
  · exact hz.symm.trans e17

/-- **`dAccX` from position `Q = ent + msg`**: `κ` (3), `h` (45), `t`, the zero scalar at fixed offsets. -/
theorem dAccX_run (pub : Pub) (rxy w : List FE) (sig : ByteArray) (s : RS) :
    TypedV.dAccX pub rxy w sig s =
      let K := (List.range 3).map fun i => feAt sig (s.ent + s.msg + 40 + 72 * i)
      let H := (List.range 45).map fun j => feAt sig (s.ent + s.msg + 256 + 24 * j)
      let t := feAt sig (s.ent + s.msg + 1336)
      (⟨accLine pub.accIn.pt (K ++ rxy) t, polyEval H t⟩,
        ⟨s.ent + s.msg + 1368, 24, (feAt sig (s.ent + s.msg + 1408) == 0) &&
          ((sumE H == Lvm.dot (eqKernel K) w) && ((H.headD 0 == pub.accIn.y) && s.ok))⟩) := by
  unfold TypedV.dAccX
  rw [Lvm.Q1.bind_run, Lvm.Q1.samples_run sig 3 _ (by norm_num), Lvm.Q1.bind_run, Lvm.Q1.readEs_run,
    Lvm.Q1.bind_run, Lvm.Q1.sampleE_run, Lvm.Q1.bind_run, Lvm.Q1.readE_run, Lvm.Q1.bind_run, require_run_lk,
    Lvm.Q1.bind_run, require_run_lk, Lvm.Q1.bind_run, require_run_lk, Lvm.Q1.pure_run]
  dsimp only [scalarsAt]
  rfl

end helpers

/-- **A23 at `Φ_Q` in 44 variables replayed** (soundness direction): `dAccX` on the child's `PUB` at
`acc_in` of 44 coordinates folds to the current proof's `acc_in` (`accCA accVF M pb`). -/
theorem qaccTX_replays (vk cL : Vector UInt8 32) (hS : Streamed M sig T) (hH : 11 + pubLanesX accVF ≤ T)
    {pb : Nat} (hg : M.k pb = 1) {P : Nat} (hP : P % 8 = 0) (hT : mbPX P + 40 ≤ 8 * T) (rx ry v : List Cell)
    (hrx : rx.length = 20) (hry : ry.length = 21) (hv : v.length = 8) (ptr : Ptr) :
    Replays c M sig (TypedV.dAccX (Lvm.pubOfA accVF vk cL sig) (vs M (rx ++ ry)) (vs M v))
      (qaccTX (aPX P / 8) pb rx ry v) ptr (aPX P) (mbPX P) fun a _ => a = accCA accVF M pb := by
  intro h s hs hok
  have hD : tVarsX = 44 := rfl
  have h8 : 8 * (aPX P / 8) = aPX P := by
    have : aPX P % 8 = 0 := by simp only [aPX, rVPX, rRPX, wVPX, wRPX, wGPX, zAbcPX, zRPX, tX, tY, tR]; omega
    omega
  have hmb : mbPX P = aPX P + 1392 := by simp only [mbPX]; omega
  obtain ⟨F1, F2, F3, F4, F5⟩ := qaccTX_facts hS (by omega) hH hg rx ry v hrx hry hv h
  obtain ⟨hy, hpt⟩ := pubOfA_accIn accVF vk cL sig
  have hQ : s.ent + s.msg = 8 * (aPX P / 8) := by rw [h8]; exact hs
  rw [dAccX_run]
  dsimp only
  rw [hQ]
  have eK : (List.range 3).map (fun i => feAt sig (8 * (aPX P / 8) + 40 + 72 * i)) =
      (List.range 3).map fun i => feAt sig (8 * (aPX P / 8 + 5 + 9 * i)) :=
    List.map_congr_left fun i _ => congrArg _ (by omega)
  have eH : (List.range 45).map (fun j => feAt sig (8 * (aPX P / 8) + 256 + 24 * j)) =
      (List.range 45).map fun j => feAt sig (8 * (aPX P / 8 + 27 + 5 + 3 * j)) :=
    List.map_congr_left fun j _ => congrArg _ (by omega)
  have et : feAt sig (8 * (aPX P / 8) + 1336) = feAt sig (8 * (aPX P / 8 + 27 + 3 * 45 + 5)) :=
    congrArg _ (by omega)
  have ez : feAt sig (8 * (aPX P / 8) + 1408) = feAt sig (8 * (aPX P / 8 + 27 + 3 * 45 + 9 + 5)) :=
    congrArg _ (by omega)
  rw [eK, eH, et, ez]
  refine ⟨?_, ?_, ?_⟩
  · rw [F5, F1, hy, F2]
    simp [hok, accVF]
  · show 8 * (aPX P / 8) + 1368 + 24 = mbPX P
    omega
  · rw [hpt, show accVF = 44 from rfl, F3, F4]
    rfl

/-! ## The typed phases -/

theorem typedPosX_le (Td : TData) (P : Nat) :
    wGPX P ≤ rRPX P ∧ rRPX P ≤ aPX P ∧ aPX P ≤ mbPX P ∧ mbPX P ≤ typedEndX Td P := by
  have h1 : mbPX P ≤ busEndD Td.mbD (mbPX P) := by
    unfold busEndD
    have := le_layersEnd (gkrSteps Td.mbD) 0 (busP1 (mbPX P) + 48)
    simp only [busP1] at this ⊢
    omega
  have h2 : busEndD Td.mbD (mbPX P) ≤ typedEndX Td P := by
    unfold typedEndX tabEnd; omega
  refine ⟨?_, ?_, ?_, le_trans h1 h2⟩ <;> simp only [wGPX, rRPX, aPX, mbPX, wRPX, wVPX, rVPX] <;> omega

set_option maxHeartbeats 1000000 in
/-- **The typed core gadget at S2GF replays `dTypedX`** (soundness direction), on the child's `PUB` at
`acc_in` of 44 coordinates. -/
theorem typedGX_replays (vk cL : Vector UInt8 32) (hS : Streamed M sig T) (hH : 11 + pubLanesX accVF ≤ T)
    {pb : Nat} (hg : M.k pb = 1) (hvk : ∀ i < 4, M.k (pb + 1 + i) = (digestLanes vk).getD i 0) {z o : Cell}
    (hzE : z.ty = .E) (hoE : o.ty = .E) (hz : z.val M = 0) (ho : o.val M = 1) (p : Params)
    (hl : p.leafdecReads = 1) {Td : TData} {N : TNat} (htd : TdOk Td N) (hsc : Lvm.M3.sumcheckTabs N.mbT = N.mbT)
    (hS' : Td.mbS = N.mbT.map Lvm.M3.Tab.shape) (hR : Td.mbR = p.tableRounds) (hD : Td.mbD = p.busDepth)
    (hfix : FixListed N.mbT Td.mbFix) {P : Nat} (hP : P % 8 = 0) (hT : typedEndX Td P + 40 ≤ 8 * T) (q : Ptr)
    (hq : 1 ≤ q.e) :
    Replays c M sig (TypedV.dTypedX p N (N.m3 p) (Lvm.pubOfA accVF vk cL sig)) (typedGX Td pb P accVF z o) q P
      (typedEndX Td P) fun v t => v.1 = accCA accVF M pb ∧
        v.2.1 = TypedV.typedClaimsN N p (vs M t.ry) (vs M t.rv) (vs M t.rr) (t.vR.val M) ∧
        v.2.2 = t.tab.map fun e => (vs M e.1, vs M e.2) := by
  intro hok s hs hsok
  have hgv : (kc pb).val M = 1 := Lvm.QAcc.kc_val_one hg
  have hA : pubLanesX accVF ≤ 2 ^ 10 := by decide
  obtain ⟨l1, l2, l3, l4⟩ := typedPosX_le Td P
  have m1 : wGPX P % 8 = 0 := by simp only [wGPX, zAbcPX, zRPX, tX]; omega
  have m4 : mbPX P % 8 = 0 := by
    simp only [mbPX, aPX, rVPX, rRPX, wVPX, wRPX, wGPX, zAbcPX, zRPX, tVarsX, tX, tY, tR]; omega
  have eR : rRP (rRPX P - rRP 0) = rRPX P := by
    simp only [rRP, wVP, wRP, wGP, zAbcP, zRP, rRPX, wVPX, wRPX, wGPX, zAbcPX, zRPX, tX, tY]; omega
  have eA : aP (rRPX P - rRP 0) = aPX P := by
    simp only [aP, rVP, rRP, wVP, wRP, wGP, zAbcP, zRP, aPX, rVPX, rRPX, wVPX, wRPX, wGPX, zAbcPX, zRPX, tX, tY,
      tR]; omega
  have m2 : (rRPX P - rRP 0) % 8 = 0 := by
    simp only [rRP, wVP, wRP, wGP, zAbcP, zRP, rRPX, wVPX, wRPX, wGPX, zAbcPX, zRPX, tX, tY]; omega
  simp only [typedGX] at hok
  simp only [typedGX, bind_apply, pure_apply, TypedV.dTypedX, bind_run', pure_run']
  rw [show N.m3 p = M3.real p (fun _ => N.mbT) from rfl]
  -- the zerocheck
  obtain ⟨hZ, hok⟩ := okb hok
  generalize hzr : (zeroGX z (kc pb) P q).1 = zr at hok ⊢
  generalize hq1 : q.adv (zeroGX z (kc pb) P q).2 = q1 at hok ⊢
  have hq1e : 1 ≤ q1.e := le_trans hq (by rw [← hq1]; exact Lvm.QAcc.adv_e_le _ _)
  have RZ := zeroGX_replays (c := c) hS hz hgv hP (by omega) q hZ s hs hsok
  rw [hzr] at RZ
  generalize TypedV.dZeroX sig s = Zv at RZ ⊢
  obtain ⟨zv, s1⟩ := Zv
  obtain ⟨z1, z2, ⟨z3, z4, z5, z6, z7, z8⟩⟩ := RZ
  simp only at z1 z2 z3 z4 ⊢
  rw [z4]
  -- the wiring
  obtain ⟨hW, hok⟩ := okb hok
  generalize hw : (wireGX z o (kc pb) Td pb P (pubLanesX accVF) zr.2 q1).1 = w at hok ⊢
  generalize hq2 : q1.adv (wireGX z o (kc pb) Td pb P (pubLanesX accVF) zr.2 q1).2 = q2 at hok ⊢
  have hq2e : 1 ≤ q2.e := le_trans hq1e (by rw [← hq2]; exact Lvm.QAcc.adv_e_le _ _)
  have RW := wireGX_replays (c := c) accVF vk cL hS hH hA hz ho hzE hoE hgv htd hvk hP (by omega) zr.2 z7 q1 hW
    s1 z2 z1
  rw [hw] at RW
  generalize TypedV.dWiringX N (Lvm.pubOfA accVF vk cL sig) (vs M zr.2) sig s1 = Wv at RW ⊢
  obtain ⟨wv, s2⟩ := Wv
  obtain ⟨w1, w2, w3, w4, w5, w6, w7, w8, w9, w10, w11⟩ := RW
  simp only at w1 w2 w3 w4 w5 ⊢
  have evS : wv.2.2.getD 1 0 = (w.2.2.getD 1 z).val M := by
    rw [w5]; exact Lvm.QAcc.getD_vals _ _ hz 1
  rw [evS, w3]
  -- the relayout
  obtain ⟨hRl, hok⟩ := okb hok
  generalize hr : (relayG z o (kc pb) Td (rRPX P - rRP 0) w.1 (w.2.2.getD 1 z) q2).1 = r at hok ⊢
  generalize hq3 : q2.adv (relayG z o (kc pb) Td (rRPX P - rRP 0) w.1 (w.2.2.getD 1 z) q2).2 = q3 at hok ⊢
  have hq3e : 1 ≤ q3.e := le_trans hq2e (by rw [← hq3]; exact Lvm.QAcc.adv_e_le _ _)
  have RR := relayG_replays (c := c) hS hz ho hzE hoE hgv rfl htd m2 (by rw [eA]; omega) w.1 w6 w7
    (w.2.2.getD 1 z) q2 hq2e hRl s2 (by rw [eR]; exact w2) w1
  rw [hr, eA] at RR
  generalize TypedV.dRelayT N (vs M w.1) ((w.2.2.getD 1 z).val M) sig s2 = Rv at RR ⊢
  obtain ⟨rv, s3⟩ := Rv
  obtain ⟨r1, r2, r3, r4, r5, r6⟩ := RR
  simp only at r1 r2 r3 r4 ⊢
  have exy : zv.1 ++ vs M w.1 = vs M (zr.1 ++ w.1) := by rw [z3]; simp [vs]
  rw [exy, w4]
  -- A23 at `Φ_Q`
  obtain ⟨hA23, hok⟩ := okb hok
  generalize hq4 : q3.adv (qaccTX (aPX P / 8) pb zr.1 w.1 w.2.1 q3).2 = q4 at hok ⊢
  have hq4e : 1 ≤ q4.e := le_trans hq3e (by rw [← hq4]; exact Lvm.QAcc.adv_e_le _ _)
  have RA := qaccTX_replays (c := c) vk cL hS hH hg hP (by omega) zr.1 w.1 w.2.1 z5 w6 w8 q3 hA23 s3 r2 r1
  generalize TypedV.dAccX (Lvm.pubOfA accVF vk cL sig) (vs M (zr.1 ++ w.1)) (vs M w.2.1) sig s3 = Av at RA ⊢
  obtain ⟨av, s4⟩ := Av
  obtain ⟨a1, a2, a3⟩ := RA
  simp only at a1 a2 a3 ⊢
  -- the mini-bus
  obtain ⟨hM, -⟩ := okb hok
  have RM := miniG_replays (c := c) hS hz ho hzE hoE hgv rfl p hl Td N.mbT hsc hS' hR hD hfix
    (Lvm.pubOfA accVF vk cL sig) m4 (by unfold typedEndX at hT; omega) q4 hq4e hM s4 a2 a1
  generalize TypedV.dMiniT p (M3.real p fun _ => N.mbT) N.mbT (Lvm.pubOfA accVF vk cL sig) sig s4 = Mv at RM ⊢
  obtain ⟨mv, s5⟩ := Mv
  obtain ⟨b1, b2, b3⟩ := RM
  refine ⟨b1, b2, a3, ?_, b3⟩
  rw [w5, r3, r4]

/-- **The typed phases at S2GF in `PhaseAt` form** (`core_of_phasesF`'s `htyped`): from `P` to `typedEndX Td P`,
the accumulator the current proof's `acc_in` cells, the claims and evaluations the gadget's cells'. -/
theorem typed_phaseX (vk cL : Vector UInt8 32) (hS : Streamed M sig T) (hH : 11 + pubLanesX accVF ≤ T)
    {pb : Nat} (hg : M.k pb = 1) (hvk : ∀ i < 4, M.k (pb + 1 + i) = (digestLanes vk).getD i 0) {z o : Cell}
    (hzE : z.ty = .E) (hoE : o.ty = .E) (hz : z.val M = 0) (ho : o.val M = 1) (p : Params)
    (hl : p.leafdecReads = 1) {Td : TData} {N : TNat} (htd : TdOk Td N) (hsc : Lvm.M3.sumcheckTabs N.mbT = N.mbT)
    (hS' : Td.mbS = N.mbT.map Lvm.M3.Tab.shape) (hR : Td.mbR = p.tableRounds) (hD : Td.mbD = p.busDepth)
    (hfix : FixListed N.mbT Td.mbFix) {P : Nat} (hP : P % 8 = 0) (hT : typedEndX Td P + 40 ≤ 8 * T) (q : Ptr)
    (hq : 1 ≤ q.e) (hok : Lvm.QSig.Ok c M (typedGX Td pb P accVF z o) q) :
    PhaseAt (TypedV.dTypedX p N (N.m3 p) (Lvm.pubOfA accVF vk cL sig)) sig P (typedEndX Td P)
      (accCA accVF M pb, TypedV.typedClaimsN N p (vs M (typedGX Td pb P accVF z o q).1.ry)
        (vs M (typedGX Td pb P accVF z o q).1.rv) (vs M (typedGX Td pb P accVF z o q).1.rr)
        ((typedGX Td pb P accVF z o q).1.vR.val M),
        (typedGX Td pb P accVF z o q).1.tab.map fun e => (vs M e.1, vs M e.2)) :=
  phaseAt_of (typedGX_replays vk cL hS hH hg hvk hzE hoE hz ho p hl htd hsc hS' hR hD hfix hP hT q hq) hok
    fun a ⟨h1, h2, h3⟩ => Prod.ext h1 (Prod.ext h2 h3)

end

end Lvm.E2Q
