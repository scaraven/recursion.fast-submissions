-- New for lvm2 E2F (E2F-QH4): one Keccak GKR layer at `E2`: `V`'s `verifyKeccakLayerD` (`LvmDecideE2`) on a view of
-- the stream, and the `E2` layer template `layerTB2` replaying it (the `E2` counterpart of `LvmQEqKeccakRead`'s layer
-- part and `LvmQEqKeccakLayer`).
import LvmE2QKParts

/-!
# One Keccak GKR layer at `E2`

**`V` side.** `layerSpec2 v va io C p`: `V`'s layer from the position `p = ent + msg`, its reads on the `E2` view
`v` (`fe2At Σ`) and its ground answers on the `E` view `va` (`feAt Σ`): the next claim, the end position, the two
checks `ok1`, `ok2` and the proof-of-work flag `pw` (the answers of `s`, the pack rounds, the position rounds and
`β`). **`verifyKeccakLayerD_run`**: `verifyKeccakLayerD sh ls step C` is `layerSpec2 … (iotaSF sh ls step) C`; its
flag after is `ok1 ∧ ok2 ∧ pw ∧` the flag before.

**Circuit side.** `Rep2 P cv C first`: the carried `E2` values `cv` represent `V`'s claim `C` (the first claim's
weights `lanes ⊗ x^z` when `first`, else `Lᵀ(eq(a, ·) ⊗ B)`). **`layer2_core`**: one iteration of `layerTB2`
(`THold2`) whose carried values represent `C` and whose lanes are the stream computes `layerSpec2`'s claim in its
copy rows, moves the position by `8·str2`, and its two gated assertions hold iff `ok1` and `ok2` (gate `1`).
-/

set_option autoImplicit false

namespace Lvm.Q1

open Lvm Lvm.Loop Lvm.Loop.Build Lvm.E2V DM

/-! ## `V`'s layer on a view -/

theorem rdE_bind_run {α β : Type} (m : DM α) (f : α → DM β) (sig : ByteArray) (s : RS) :
    (m >>= f) sig s = f (m sig s).1 sig (m sig s).2 := (bind_run m f sig s).trans rfl
theorem rdE_pure_run {α : Type} (a : α) (sig : ByteArray) (s : RS) : (pure a : DM α) sig s = (a, s) :=
  (pure_run a sig s).trans rfl

theorem roundPolyD_some_run (sig : ByteArray) (count : Nat) (claim r : FE2) (s : RS) :
    roundPolyD count claim (some r) sig s =
      ((claim + r * sumF (scalars2 (fe2At sig) (s.ent + s.msg + 40) (count - 1))) ::
        scalars2 (fe2At sig) (s.ent + s.msg + 40) (count - 1), { s with msg := s.msg + 16 * (count - 1) }) := by
  rw [show roundPolyD count claim (some r) = (readE2s (count - 1) >>= fun tail =>
    pure ((claim + r * sumF tail) :: tail)) from rfl, rdE_bind_run, readE2s_run, rdE_pure_run]

theorem packRoundsD_cons (g : Nat) (r : FE2) (rs : List FE2) (value scale : FE2) :
    packRoundsD g (r :: rs) value scale = (roundPolyD 3 value (some r) >>= fun msg => sampleG g >>= fun c =>
      packRoundsD g rs ((1 + r + c) * polyEvalF msg c) (scale * (1 + r + c)) >>= fun res =>
        pure (res.1, res.2.1, c :: res.2.2)) := rfl

theorem packRoundsD_nil (g : Nat) (value scale : FE2) :
    packRoundsD g [] value scale = pure (value, scale, []) := rfl

theorem packRoundsD_run (sig : ByteArray) (g : Nat) : ∀ (pt : List FE2) (value scale : FE2) (s : RS) (p : Nat),
    pt ≠ [] → s.ent + s.msg = p →
    packRoundsD g pt value scale sig s =
      (((packSpec2 (fe2At sig) (feAt sig) g pt value scale p).1,
        (packSpec2 (fe2At sig) (feAt sig) g pt value scale p).2.1,
        (packSpec2 (fe2At sig) (feAt sig) g pt value scale p).2.2.1),
        ⟨(packSpec2 (fe2At sig) (feAt sig) g pt value scale p).2.2.2.1, 0,
          (packSpec2 (fe2At sig) (feAt sig) g pt value scale p).2.2.2.2 && s.ok⟩)
  | [], _, _, _, _, h, _ => absurd rfl h
  | r :: rs, value, scale, ⟨e, m, o⟩, p, _, hp => by
    simp only at hp
    subst hp
    rw [packRoundsD_cons]
    cases rs with
    | nil =>
      simp only [rdE_bind_run, roundPolyD_some_run, sampleG_run, packRoundsD_nil, rdE_pure_run, packSpec2,
        Nat.add_assoc, Bool.and_true]
    | cons r' rs' =>
      simp only [rdE_bind_run, roundPolyD_some_run, sampleG_run]
      rw [packRoundsD_run sig g (r' :: rs') _ _ _ (e + m + 112) (List.cons_ne_nil _ _) (by simp only []; omega)]
      simp only [rdE_pure_run, packSpec2, Nat.add_assoc]
      cases powOKR g (feAt sig (e + (m + 80))) <;> cases o <;> simp


theorem sumcheckD_nil' (g : Nat) (claim : FE2) (count : Nat) :
    sumcheckD g claim count [] = pure ([], claim) := rfl

/-- **`V`'s plain sumcheck, its state**: `R + 1` rounds from `p = ent + msg`. -/
theorem sumcheckD_runS (sig : ByteArray) (g count : Nat) (hc : 2 ≤ count) : ∀ (R : Nat) (claim : FE2) (s : RS) (p : Nat),
    s.ent + s.msg = p →
    sumcheckD g claim count (List.replicate (R + 1) none) sig s =
      (((scSpec2 (fe2At sig) (feAt sig) g count p claim (R + 1)).1,
        (scSpec2 (fe2At sig) (feAt sig) g count p claim (R + 1)).2.1),
        ⟨p + (R + 1) * roundLen2 count, 0, (scSpec2 (fe2At sig) (feAt sig) g count p claim (R + 1)).2.2 && s.ok⟩)
  | 0, claim, ⟨e, m, o⟩, p, hp => by
    simp only at hp
    subst hp
    simp only [List.replicate_succ, List.replicate_zero, sumcheckD_cons, rdE_bind_run, roundPolyD_run sig count hc,
      sampleG_run, sumcheckD_nil', rdE_pure_run, scSpec2, Bool.and_true, ansAt2, roundLen2]
    have h1 : e + (m + 16 * (count - 1)) + 48 = e + m + 48 + 16 * (count - 1) := by omega
    have h2 : e + (m + 16 * (count - 1)) + 80 = e + m + (0 + 1) * (80 + 16 * (count - 1)) := by omega
    rw [h1, h2]
  | R + 1, claim, ⟨e, m, o⟩, p, hp => by
    simp only at hp
    subst hp
    rw [List.replicate_succ, sumcheckD_cons]
    simp only [rdE_bind_run, roundPolyD_run sig count hc, sampleG_run]
    rw [sumcheckD_runS sig g count hc R _ ⟨e + (m + 16 * (count - 1)) + 80, 0,
      powOKR g (feAt sig (e + (m + 16 * (count - 1)) + 48)) && o⟩ (e + m + roundLen2 count)
      (by simp only [roundLen2]; omega)]
    have h1 : e + (m + 16 * (count - 1)) + 48 = e + m + 48 + 16 * (count - 1) := by omega
    simp only [rdE_pure_run, scSpec2, ansAt2, h1]
    rw [Prod.mk.injEq, RS.mk.injEq]
    exact ⟨rfl, by ring, rfl, by simp only [Bool.and_assoc, Bool.and_comm, Bool.and_left_comm]⟩


theorem rdE_require_run (c : Bool) (sig : ByteArray) (s : RS) :
    require c sig s = ((), { s with ok := c && s.ok }) := (require_run c sig s).trans rfl

theorem sepE2_run (sig : ByteArray) (s : RS) :
    sepE2 sig s = ((), ⟨s.ent + 72 + s.msg, 0, s.ok⟩) := rfl

theorem packRoundsD_run' (sig : ByteArray) (g : Nat) (pt : List FE2) (value scale : FE2) (s : RS) (hpt : pt ≠ []) :
    packRoundsD g pt value scale sig s =
      (((packSpec2 (fe2At sig) (feAt sig) g pt value scale (s.ent + s.msg)).1,
        (packSpec2 (fe2At sig) (feAt sig) g pt value scale (s.ent + s.msg)).2.1,
        (packSpec2 (fe2At sig) (feAt sig) g pt value scale (s.ent + s.msg)).2.2.1),
        ⟨(packSpec2 (fe2At sig) (feAt sig) g pt value scale (s.ent + s.msg)).2.2.2.1, 0,
          (packSpec2 (fe2At sig) (feAt sig) g pt value scale (s.ent + s.msg)).2.2.2.2 && s.ok⟩) :=
  packRoundsD_run sig g pt value scale s _ hpt rfl

theorem sumcheckD_runS' (sig : ByteArray) (g count : Nat) (hc : 2 ≤ count) (R : Nat) (claim : FE2) (s : RS) :
    sumcheckD g claim count (List.replicate (R + 1) none) sig s =
      (((scSpec2 (fe2At sig) (feAt sig) g count (s.ent + s.msg) claim (R + 1)).1,
        (scSpec2 (fe2At sig) (feAt sig) g count (s.ent + s.msg) claim (R + 1)).2.1),
        ⟨s.ent + s.msg + (R + 1) * roundLen2 count, 0,
          (scSpec2 (fe2At sig) (feAt sig) g count (s.ent + s.msg) claim (R + 1)).2.2 && s.ok⟩) :=
  sumcheckD_runS sig g count hc R claim s _ rfl

theorem bool_layer (a b c d e f o : Bool) :
    (f && (b && (c && (d && (e && (a && o)))))) = (((a && b) && (((e && d) && c) && f)) && o) := by
  cases a <;> cases b <;> cases c <;> cases d <;> cases e <;> cases f <;> cases o <;> rfl

/-- What `V`'s layer returns on a view. -/
structure LayerOut2 where
  claim : KClaim FE2
  pos : Nat
  ok1 : Bool
  ok2 : Bool
  pw : Bool

def layerSpec2 (v : Nat → FE2) (va : Nat → FE) (io : KClaim FE2 → FE2) (claim : KClaim FE2) (p : Nat) : LayerOut2 :=
  let product := scalars2 v (p + 40) productBits
  let s := e2OfFE (va (p + 872))
  let mu := instWeightsF s
  let kappa := sumF mu
  let pk := packSpec2 v va gC3 claim.point (polyEvalF product s) 1 (p + 904)
  let lv := scSpec2 v va gC3 4 pk.2.2.2.1 pk.1 LeanVM.Protocol.Verifier.keccakLocalBits
  let p3 := pk.2.2.2.1 + LeanVM.Protocol.Verifier.keccakLocalBits * roundLen2 4
  let t := scalars2 v (p3 + 40) 3
  let eq := eqKernelF lv.1
  let t0 := t.getD 0 0
  let t1 := t.getD 1 0
  let t2 := t.getD 2 0
  let beta := e2OfFE (va (p3 + 96))
  let weights := (List.range LeanVM.Protocol.Verifier.keccakBits).map fun j =>
    eq.getD j 0 + beta * (eq.getD (LeanVM.Protocol.Verifier.keccakAlong j 4) 0 +
      beta * eq.getD (LeanVM.Protocol.Verifier.keccakAlong j 3) 0)
  ⟨⟨t0 + beta * (t1 + beta * t2), mu, pk.2.2.1, linearTransposeF weights⟩, p3 + 128,
    projectedF claim product + io claim * sumF claim.mu == claim.value,
    pk.2.1 * dotF (eq.take LeanVM.Protocol.Verifier.keccakBits) claim.weights * (kappa * t0 + (kappa + t1) * t2) ==
      lv.2.1,
    powOKR gC46 (va (p + 872)) && pk.2.2.2.2 && lv.2.2 && powOKR gC2 (va (p3 + 96))⟩

theorem verifyKeccakLayerD_run (sig : ByteArray) (sh : LeanVM.Protocol.KeccakGkr.Shape) (ls step : Nat)
    (claim : KClaim FE2) (hpt : claim.point ≠ []) (s : RS) :
    verifyKeccakLayerD sh ls step claim sig s =
      ((layerSpec2 (fe2At sig) (feAt sig) (iotaSF sh ls step) claim (s.ent + s.msg)).claim,
        ⟨(layerSpec2 (fe2At sig) (feAt sig) (iotaSF sh ls step) claim (s.ent + s.msg)).pos, 0,
          ((layerSpec2 (fe2At sig) (feAt sig) (iotaSF sh ls step) claim (s.ent + s.msg)).ok1 &&
            (layerSpec2 (fe2At sig) (feAt sig) (iotaSF sh ls step) claim (s.ent + s.msg)).ok2 &&
            (layerSpec2 (fe2At sig) (feAt sig) (iotaSF sh ls step) claim (s.ent + s.msg)).pw) && s.ok⟩) := by
  obtain ⟨e, m, o⟩ := s
  simp only []
  unfold verifyKeccakLayerD
  rw [show LeanVM.Protocol.Verifier.keccakLocalBits = 10 + 1 from rfl]
  simp only [rdE_bind_run, readE2s_run, rdE_require_run, sepE2_run, sampleG_run, packRoundsD_run' sig gC3 _ _ _ _ hpt,
    sumcheckD_runS' sig gC3 4 (by omega), rdE_pure_run]
  simp only [layerSpec2, show LeanVM.Protocol.Verifier.keccakLocalBits = 10 + 1 from rfl]
  have q1 : e + 72 + (m + 16 * productBits) + 0 + 48 = e + m + 872 := by
    rw [show productBits = 47 from rfl]; omega
  have q2 : e + 72 + (m + 16 * productBits) + 0 + 80 + 0 = e + m + 904 := by
    rw [show productBits = 47 from rfl]; omega
  simp only [q1, q2]
  generalize packSpec2 (fe2At sig) (feAt sig) gC3 claim.point
    (polyEvalF (scalars2 (fe2At sig) (e + m + 40) productBits) (e2OfFE (feAt sig (e + m + 872)))) 1 (e + m + 904) = pk
  have q3 : pk.2.2.2.1 + 0 + (10 + 1) * roundLen2 4 + 0 + 40 = pk.2.2.2.1 + (10 + 1) * roundLen2 4 + 40 := by omega
  have q4 : pk.2.2.2.1 + 0 + (10 + 1) * roundLen2 4 + (0 + 16 * 3) + 48 =
      pk.2.2.2.1 + (10 + 1) * roundLen2 4 + 96 := by omega
  have q5 : pk.2.2.2.1 + 0 + (10 + 1) * roundLen2 4 + (0 + 16 * 3) + 80 =
      pk.2.2.2.1 + (10 + 1) * roundLen2 4 + 128 := by omega
  have q6 : pk.2.2.2.1 + 0 = pk.2.2.2.1 := rfl
  simp only [q3, q4, q5]
  simp only [q6]
  rw [Prod.mk.injEq, RS.mk.injEq]
  exact ⟨rfl, rfl, rfl, bool_layer _ _ _ _ _ _ _⟩


/-! ## Algebra at `FE2` for the layer -/

theorem fe2_beq_iff (x y : FE2) : (x == y) = true ↔ x = y := beq_iff_eq

theorem fe2_add_eq_zero (x y : FE2) : x + y = 0 ↔ x = y := by
  constructor
  · intro h
    calc x = x + (y + y) := by rw [fe2_add_self, add_zero]
      _ = (x + y) + y := by ring
      _ = y := by rw [h, zero_add]
  · intro h; rw [h, fe2_add_self]

/-- Horner from the top coefficient is `polyEvalF`. -/
theorem polyEvalF_horner2 (x h : FE2) (l : List FE2) : polyEvalF (l ++ [h]) x = hornerVal2 x h l.reverse := by
  unfold polyEvalF hornerVal2
  rw [List.foldr_append, List.foldl_reverse]
  simp only [List.foldr_cons, List.foldr_nil, zero_mul, zero_add]

/-- `eq` of an 11-point at `j < 2^11` splits into the low six and high five coordinates. -/
theorem eqKernelF_split11 {lp : List FE2} (hl : lp.length = 11) {j : Nat} (hj : j < 2048) :
    (eqKernelF lp).getD j 0 = eqAtG (lp.take 6) (j % 64) * (eqKernelF (lp.drop 6)).getD (j / 64) 0 := by
  have ht : (lp.take 6).length = 6 := by simp [hl]
  have hd : (lp.drop 6).length = 5 := by simp [hl]
  rw [eqKernelF_getD, ite_eq_left (by rw [hl]; exact hj), eqAtG, eqKernelF_getD, eqKernelF_getD,
    ite_eq_left (by rw [ht]; exact Nat.mod_lt _ (by omega)), ite_eq_left (by rw [hd]; omega),
    ← List.take_append_drop 6 lp, eqAtF_append, List.take_append_drop, ht, eqAtF_mod (lp.take 6) j, ht]
  rfl

/-- **`V`'s `dot(eq[:1600], W)`** on an 11-point is the lane-then-slice weighted sum. -/
theorem dot_take_weighted {lp W : List FE2} (hl : lp.length = 11) (hW : W.length = 1600) :
    dotF ((eqKernelF lp).take LeanVM.Protocol.Verifier.keccakBits) W =
      weightedFG (eqKernelF (lp.drop 6)) (eqKernelF (lp.take 6)) W := by
  rw [show LeanVM.Protocol.Verifier.keccakBits = W.length by rw [hW]; rfl,
    dotF_eq _ _ (by simp [eqKernelF_length, hl, hW]), List.length_take, eqKernelF_length, hl, hW]
  rw [show min 1600 (2 ^ 11) = 25 * 64 from rfl, sum_range_mulB, weightedFG, sumF_map_range]
  refine Finset.sum_congr rfl fun l hl' => ?_
  have hl25 := Finset.mem_range.mp hl'
  rw [sumF_map_range, Finset.mul_sum]
  refine Finset.sum_congr rfl fun z hz => ?_
  have hz64 := Finset.mem_range.mp hz
  rw [List.getD_eq_getElem?_getD, List.getElem?_take, ite_eq_left (by omega), ← List.getD_eq_getElem?_getD,
    eqKernelF_split11 hl (by omega), show (64 * l + z) % 64 = z by omega, show (64 * l + z) / 64 = l by omega]
  unfold eqAtG
  ring

theorem along_split (j k : Nat) :
    LeanVM.Protocol.Verifier.keccakAlong j k = 64 * (keccakAlong (64 * (j / 64)) k / 64) + j % 64 := by
  rw [← keccakAlong_eqV]
  unfold keccakAlong
  simp only []
  omega

/-- **The next claim's weights** are the product weights `eq(a', ·) ⊗ B'` (`a'` the low six position
challenges, `B'` the lane weights from the high five and `β`). -/
theorem next_weights {lp : List FE2} (hl : lp.length = 11) (beta : FE2) :
    (List.range LeanVM.Protocol.Verifier.keccakBits).map (fun j =>
      (eqKernelF lp).getD j 0 + beta * ((eqKernelF lp).getD (LeanVM.Protocol.Verifier.keccakAlong j 4) 0 +
        beta * (eqKernelF lp).getD (LeanVM.Protocol.Verifier.keccakAlong j 3) 0)) =
    prodWG (eqAtG (lp.take 6)) ((List.range 25).map fun l => (eqKernelF (lp.drop 6)).getD l 0 + beta *
      ((eqKernelF (lp.drop 6)).getD (keccakAlong (64 * l) 4 / 64) 0 + beta *
        (eqKernelF (lp.drop 6)).getD (keccakAlong (64 * l) 3 / 64) 0)) := by
  unfold prodWG
  rw [show LeanVM.Protocol.Verifier.keccakBits = keccakBits from rfl]
  refine List.map_congr_left fun j hj => ?_
  have hj' : j < 1600 := List.mem_range.mp hj
  have ha : ∀ k, k < 5 → keccakAlong (64 * (j / 64)) k / 64 < 25 := by
    intro k _; unfold keccakAlong; simp only []; omega
  rw [along_split j 4, along_split j 3, eqKernelF_split11 hl (by omega),
    eqKernelF_split11 hl (by have := ha 4 (by omega); omega), eqKernelF_split11 hl (by have := ha 3 (by omega); omega),
    show (64 * (keccakAlong (64 * (j / 64)) 4 / 64) + j % 64) % 64 = j % 64 by omega,
    show (64 * (keccakAlong (64 * (j / 64)) 3 / 64) + j % 64) % 64 = j % 64 by omega,
    show (64 * (keccakAlong (64 * (j / 64)) 4 / 64) + j % 64) / 64 = keccakAlong (64 * (j / 64)) 4 / 64 by omega,
    show (64 * (keccakAlong (64 * (j / 64)) 3 / 64) + j % 64) / 64 = keccakAlong (64 * (j / 64)) 3 / 64 by omega,
    List.getD_eq_getElem?_getD (l := List.map _ _), List.getElem?_map, List.getElem?_range (by omega)]
  simp only [Option.map_some, Option.getD_some]
  ring

/-- `V`'s projected value in the circuit's grouping. -/
theorem projectedF_eq2 (C : KClaim FE2) (product : List FE2) :
    projectedF C product = sumF ((List.range 47).map fun c =>
      sumF ((C.mu.zip Lvm.rmfeProject).filterMap fun p => if p.2.testBit c then some p.1 else none) *
        product.getD c 0) := by
  unfold projectedF
  rw [rmfeProject_eqV]
  rfl

/-- `V`'s instance weights in the circuit's form. -/
theorem instWeightsF_eq2 (s : FE2) :
    instWeightsF s = Lvm.rmfeEmbed.map (fun e => sumF ((List.range Lvm.embedBits).filterMap fun b =>
      if e.testBit b then some ((powersF s Lvm.embedBits).getD b 0) else none)) := by
  unfold instWeightsF
  rw [rmfeEmbed_eqV]

theorem laneFormF_congr (B : List FE2) {R R' : Nat → FE2} (hR : ∀ s < 64, R s = R' s) (l : Nat) :
    laneFormF B R l = laneFormF B R' l := by
  have h1 : ∀ i, R (rho i) = R' (rho i) := fun i => hR _ (rho_lt i)
  have h2 : ∀ i, R ((rho i + 1) % 64) = R' ((rho i + 1) % 64) := fun i => hR _ (Nat.mod_lt _ (by norm_num))
  simp only [laneFormF, h1, h2]

theorem rcBit_s2 (rc : UInt64) (i : Nat) : (⟨(rcBit rc i).c₀, 0⟩ : FE2) = rcBitG rc i := by
  unfold rcBit rcBitG; split <;> rfl

/-! ## The carried claim -/

/-- The carried lane weights `B`. -/
def repB2 (P : Nat) (cv : Nat → FE2) : List FE2 := (List.range 25).map fun l => cv (19 + P + l)

/-- The carried slice challenges `a`. -/
def repA2 (P : Nat) (cv : Nat → FE2) : List FE2 := (List.range 6).map fun i => cv (44 + P + i)

/-- **The carried `E2` values `cv` represent `V`'s claim `C`** (the first claim's weights when `first`). -/
structure Rep2 (P : Nat) (cv : Nat → FE2) (C : KClaim FE2) (first : Bool) : Prop where
  value : cv 0 = C.value
  mu : (List.range 16).map (fun i => cv (1 + i)) = C.mu
  kappa : cv 17 = sumF C.mu
  point : (List.range (P + 1)).map (fun i => cv (18 + i)) = C.point
  weights : C.weights = if first then firstWG gx (repB2 P cv)
    else linearTransposeF (prodWG (eqAtG (repA2 P cv)) (repB2 P cv))
  flips : ∀ i < 7, cv (50 + P + i) = if first then (repB2 P cv).getD 0 0 * gx ^ iotaPos i
    else flipFormG (repB2 P cv) (eqAtG (repA2 P cv)) i

/-- The iota sum on a represented claim's weights is the carried flips' (both kinds of claim). -/
theorem iota_rep2 {P : Nat} {cv : Nat → FE2} {C : KClaim FE2} {first : Bool} (hR : Rep2 P cv C first)
    {rc : UInt64} (hrc : rc ∈ keccakRC) :
    iotaFG rc C.weights = sumF ((List.range 7).map fun i => rcBitG rc i * cv (50 + P + i)) := by
  rw [hR.weights]
  cases first with
  | true =>
    simp only [ite_true]
    rw [iota_firstG gx hrc]
    refine congrArg sumF (List.map_congr_left fun i hi => ?_)
    rw [hR.flips i (List.mem_range.mp hi)]
    simp only [ite_true]
  | false =>
    simp only [Bool.false_eq_true, ite_false]
    rw [iota_flipsG hrc]
    refine congrArg sumF (List.map_congr_left fun i hi => ?_)
    rw [hR.flips i (List.mem_range.mp hi)]
    simp only [Bool.false_eq_true, ite_false]

theorem rep2_weights_length {P : Nat} {cv : Nat → FE2} {C : KClaim FE2} {first : Bool} (hR : Rep2 P cv C first) :
    C.weights.length = 1600 := by
  rw [hR.weights]; cases first
  · exact linearTransposeF_length _
  · exact firstWG_length _ _

/-- **A represented (non-first) claim's weight `j`** as a lane form (`lt_posF` on `Rep2`; the wiring's form). -/
theorem rep2_lt_posF {P : Nat} {cv : Nat → FE2} {C : KClaim FE2} (hR : Rep2 P cv C false) {j : Nat} (hj : j < 1600) :
    C.weights.getD j 0 = laneFormF (repB2 P cv)
      (fun s => (eqKernelF (repA2 P cv)).getD ((j % 64 + s) % 64) 0) (j / 64) := by
  rw [hR.weights]
  exact lt_posF _ _ hj

/-- `V`'s final-check weight on a represented claim: `(Σ eq_L·B)·indexProd` (first) or the lane forms. -/
theorem weighted_rep2 {P : Nat} {cv : Nat → FE2} {C : KClaim FE2} {first : Bool} (hR : Rep2 P cv C first)
    {lp : List FE2} (hlp : lp.length = 11) :
    dotF ((eqKernelF lp).take LeanVM.Protocol.Verifier.keccakBits) C.weights = if first then
        ((List.range 25).map fun l => (eqKernelF (lp.drop 6)).getD l 0 * (repB2 P cv).getD l 0).sum *
          indexProdG gx (lp.take 6)
      else ((List.range 25).map fun l => (eqKernelF (lp.drop 6)).getD l 0 *
        laneFormF (repB2 P cv) (rotSumG (eqAtG (lp.take 6)) (eqAtG (repA2 P cv))) l).sum := by
  rw [dot_take_weighted hlp (rep2_weights_length hR), hR.weights]
  cases first with
  | true =>
    simp only [ite_true]
    rw [weighted_firstG gx _ _ _ (by simp [hlp]), sumF_eq_sum]
  | false =>
    simp only [Bool.false_eq_true, ite_false]
    unfold weightedFG
    rw [sumF_eq_sum]
    refine congrArg List.sum (List.map_congr_left fun l hl => ?_)
    rw [lane_dotG (eqAtG (repA2 P cv)) (fun z => (eqKernelF (lp.take 6)).getD z 0) (repB2 P cv) (List.mem_range.mp hl)]
    rfl

/-! ## Twin cells and copies -/

/-- The twin cells of an `E2` gadget's result are `K` values. -/
theorem emit2_cells {xv : Src → FE} {V : Nat → FE} {n : Nat} {f : E2Fn} {xs : List S2}
    (h : THold2 xv V n (emit2 f xs n).2) : V n = FE.ofK (V n).c₀ ∧ V (n + 1) = FE.ofK (V (n + 1)).c₀ := by
  have h0 := h 0 (by simp [emit2, e2I]) (Or.inr ⟨f, false, by simp [emit2, e2I]⟩)
  have h1 := h 1 (by simp [emit2, e2I]) (Or.inr ⟨f, true, by simp [emit2, e2I]⟩)
  simp only [emit2, e2I, List.getD_cons_zero, List.getD_cons_succ, Ins.evalF2, Nat.add_zero] at h0 h1
  exact ⟨by rw [h0]; rfl, by rw [h1]; rfl⟩

/-- An `E2` gadget's result is `0` iff its two cells are. -/
theorem emit2_zero_iff {xv : Src → FE} {V : Nat → FE} {n : Nat} {f : E2Fn} {xs : List S2}
    (h : THold2 xv V n (emit2 f xs n).2) :
    (emit2 f xs n).1.valF xv V = 0 ↔ V n = 0 ∧ V (n + 1) = 0 := by
  obtain ⟨c0, c1⟩ := emit2_cells h
  show (⟨(V n).c₀, (V (n + 1)).c₀⟩ : FE2) = ⟨0, 0⟩ ↔ _
  constructor
  · intro e
    have e0 : (V n).c₀ = 0 := congrArg FE2.re e
    have e1 : (V (n + 1)).c₀ = 0 := congrArg FE2.im e
    exact ⟨by rw [c0, e0]; rfl, by rw [c1, e1]; rfl⟩
  · rintro ⟨e0, e1⟩
    rw [e0, e1]; rfl

/-- The copy rows of `l` placed at `n` hold. -/
def CopyHold2 (xv : Src → FE) (V : Nat → FE) (n : Nat) (l : List S2) : Prop := THold2 xv V n (cpIns2 l)

theorem mapT2_q2Copy_snd : ∀ (l : List S2) (n : Nat), (mapT2 q2Copy l n).2 = cpIns2 l
  | [], _ => rfl
  | a :: as, n => by
    simp only [mapT2, tb_bind, tb_pure, List.append_nil, cpIns2, List.flatMap_cons]
    rw [mapT2_q2Copy_snd as]
    rfl

theorem cpIns2_length (l : List S2) : (cpIns2 l).length = 2 * l.length := by
  induction l with
  | nil => rfl
  | cons a as ih =>
    simp only [cpIns2, List.flatMap_cons, List.length_append] at ih ⊢
    rw [ih]; simp [q2Copy, q2Lin, emit2, e2I]; omega

theorem cp2_append {xv : Src → FE} {V : Nat → FE} {n : Nat} {l₁ l₂ : List S2} (h : CopyHold2 xv V n (l₁ ++ l₂)) :
    CopyHold2 xv V n l₁ ∧ CopyHold2 xv V (n + 2 * l₁.length) l₂ := by
  unfold CopyHold2 at h ⊢
  rw [show cpIns2 (l₁ ++ l₂) = cpIns2 l₁ ++ cpIns2 l₂ from List.flatMap_append, thold2_append, cpIns2_length] at h
  exact h

theorem cp2_get' {xv : Src → FE} {V : Nat → FE} {n : Nat} {l : List S2} (h : CopyHold2 xv V n l) :
    ∀ j < l.length, (⟨(V (n + 2 * j)).c₀, (V (n + 2 * j + 1)).c₀⟩ : FE2) = (vals2 xv V l).getD j 0 := by
  have h' : THold2 xv V n (mapT2 q2Copy l n).2 := by rw [mapT2_q2Copy_snd]; exact h
  exact cp2_get h'

theorem cp2_range {xv : Src → FE} {V : Nat → FE} {n : Nat} {l : List S2} (h : CopyHold2 xv V n l) {k : Nat}
    (hk : l.length = k) :
    (List.range k).map (fun j => (⟨(V (n + 2 * j)).c₀, (V (n + 2 * j + 1)).c₀⟩ : FE2)) = vals2 xv V l := by
  subst hk
  rw [List.map_congr_left (fun j hj => cp2_get' h j (List.mem_range.mp hj))]
  apply List.ext_getElem (by simp)
  intro j h1 h2
  rw [List.getElem_map, List.getElem_range, List.getD_eq_getElem _ _ h2]

theorem eqTab_one2 {xv : Src → FE} {V : Nat → FE} {z one : S2} (hz : z.valF xv V = 0) (hone : one.valF xv V = 1)
    (pt : List S2) (n : Nat) (h : THold2 xv V n (q2EqTab z [one] pt n).2) :
    vals2 xv V (q2EqTab z [one] pt n).1 = eqKernelF (vals2 xv V pt) := by
  rw [q2EqTab_spec hz pt [one] n h, eqKernelF, vals2, List.map_singleton, hone]

instance charP_FE2 : CharP FE2 2 := charP_of_injective_algebraMap (algebraMap FK FE2).injective 2

/-- `layerSpec2`'s fields, its intermediate values named. -/
theorem layerSpec2_fields (v : Nat → FE2) (va : Nat → FE) (io : KClaim FE2 → FE2) (C : KClaim FE2) (p : Nat)
    {pk : FE2 × FE2 × List FE2 × Nat × Bool}
    (hpk : packSpec2 v va gC3 C.point (polyEvalF (scalars2 v (p + 40) productBits) (e2OfFE (va (p + 872)))) 1
      (p + 904) = pk)
    {sc : List FE2 × FE2 × Bool} (hsc : scSpec2 v va gC3 4 pk.2.2.2.1 pk.1 11 = sc)
    {p3 : Nat} (hp3 : pk.2.2.2.1 + 11 * roundLen2 4 = p3) :
    (layerSpec2 v va io C p).claim =
      ⟨(scalars2 v (p3 + 40) 3).getD 0 0 + e2OfFE (va (p3 + 96)) * ((scalars2 v (p3 + 40) 3).getD 1 0 +
        e2OfFE (va (p3 + 96)) * (scalars2 v (p3 + 40) 3).getD 2 0),
        instWeightsF (e2OfFE (va (p + 872))), pk.2.2.1,
        linearTransposeF ((List.range LeanVM.Protocol.Verifier.keccakBits).map fun j =>
          (eqKernelF sc.1).getD j 0 + e2OfFE (va (p3 + 96)) *
            ((eqKernelF sc.1).getD (LeanVM.Protocol.Verifier.keccakAlong j 4) 0 +
              e2OfFE (va (p3 + 96)) * (eqKernelF sc.1).getD (LeanVM.Protocol.Verifier.keccakAlong j 3) 0))⟩ ∧
    (layerSpec2 v va io C p).pos = p3 + 128 ∧
    (layerSpec2 v va io C p).ok1 =
      (projectedF C (scalars2 v (p + 40) productBits) + io C * sumF C.mu == C.value) ∧
    (layerSpec2 v va io C p).ok2 =
      (pk.2.1 * dotF ((eqKernelF sc.1).take LeanVM.Protocol.Verifier.keccakBits) C.weights *
        (sumF (instWeightsF (e2OfFE (va (p + 872)))) * (scalars2 v (p3 + 40) 3).getD 0 0 +
          (sumF (instWeightsF (e2OfFE (va (p + 872)))) + (scalars2 v (p3 + 40) 3).getD 1 0) *
            (scalars2 v (p3 + 40) 3).getD 2 0) == sc.2.1) := by
  subst hpk hsc hp3
  exact ⟨rfl, rfl, rfl, rfl⟩

theorem scSpec2_length (v : Nat → FE2) (va : Nat → FE) (g count : Nat) :
    ∀ (R p : Nat) (claim : FE2), (scSpec2 v va g count p claim R).1.length = R
  | 0, _, _ => rfl
  | R + 1, p, claim => by
    simp only [scSpec2, List.length_cons]
    rw [scSpec2_length v va g count R]

theorem scalars2_getD (v : Nat → FE2) (o : Nat) {n k : Nat} (hk : k < n) :
    (scalars2 v o n).getD k 0 = v (o + 16 * k) := by
  simp [scalars2, List.getD_eq_getElem?_getD, hk]

theorem scalars2_length (v : Nat → FE2) (o n : Nat) : (scalars2 v o n).length = n := by simp [scalars2]

/-- **One layer at `E2`**, read along `layerTB2`'s chain from the walking invariant `TInv2`. -/
theorem layer2_core {c : LCfg} {xv : Src → FE} {V : Nat → FE} {TA : Prop} {L : Nat}
    (h0 : TInv2 xv V TA L True (layerTB2 c) 0) (hcb : c.cb + 2 * (57 + c.P) = L)
    {C : KClaim FE2} {first : Bool} (hR : Rep2 c.P (fun j => (c.pv2 j).valF xv V) C first)
    {io : KClaim FE2 → FE2} {rc0 rc1 : UInt64} (RC1m : rc0 ∈ keccakRC) (RC2m : rc1 ∈ keccakRC)
    (hio : io C = (1 + C.point.getD c.P 0) * iotaFG rc0 C.weights + C.point.getD c.P 0 * iotaFG rc1 C.weights)
    (hrc : ∀ i < 7, xv (c.k i) = rcBit rc0 i ∧ xv (c.k (7 + i)) = rcBit rc1 i)
    (hfirst : xv (c.k 14) = if first then 1 else 0)
    {v : Nat → FE2} {va : Nat → FE} (hva : ∀ o, e2OfFE (va o) = v o)
    {off p : Nat} (hv : ∀ m < c.q + c.str2, lv2 xv [c.str2] m = v (8 * m + off))
    (hp : p + 40 = 8 * c.q + off) :
    Rep2 c.P (fun j => ⟨(V (c.cb + 2 * j)).c₀, (V (c.cb + 2 * j + 1)).c₀⟩) (layerSpec2 v va io C p).claim false ∧
    (layerSpec2 v va io C p).pos = p + 8 * c.str2 ∧
    (TA → xv (c.k 15) = 1 → (layerSpec2 v va io C p).ok1 = true ∧ (layerSpec2 v va io C p).ok2 = true) ∧
    ((layerSpec2 v va io C p).ok1 = true → (layerSpec2 v va io C p).ok2 = true → TA) := by
  have hstr : c.str2 = 305 + 14 * (c.P + 1) := rfl
  have hPB : productBits = 47 := rfl
  have hRmu : vals2 xv V ((List.range 16).map fun i => c.pv2 (1 + i)) = C.mu := by
    rw [vals2, List.map_map]; exact hR.mu
  have hRpt : vals2 xv V ((List.range (c.P + 1)).map fun i => c.pv2 (18 + i)) = C.point := by
    rw [vals2, List.map_map]; exact hR.point
  have hCptL : C.point.length = c.P + 1 := by rw [← hRpt, vals2, List.length_map, List.length_map, List.length_range]
  have hptP : ((List.range (c.P + 1)).map fun i => c.pv2 (18 + i)).getD c.P default = c.pv2 (18 + c.P) := by
    rw [List.getD_eq_getElem _ _ (by simp), List.getElem_map, List.getElem_range]
  have hσ : C.point.getD c.P 0 = (c.pv2 (18 + c.P)).valF xv V := by
    rw [← hRpt, ← hptP, getD_valF2 _ (by simp)]
  have hflS : ∀ i < 7, ((List.range 7).map fun i => c.pv2 (50 + c.P + i)).getD i default = c.pv2 (50 + c.P + i) := by
    intro i hi
    rw [List.getD_eq_getElem _ _ (by simpa using hi), List.getElem_map, List.getElem_range]
  have hlane : ∀ m, m < c.q + c.str2 → (lane2 m [c.str2]).valF xv V = v (8 * m + off) := fun m hm => by
    rw [lane2_valF, hv m hm]
  -- the named values of `V`'s layer
  obtain ⟨pkF, hpkF⟩ : ∃ x, packSpec2 v va gC3 C.point (polyEvalF (scalars2 v (p + 40) productBits)
    (e2OfFE (va (p + 872)))) 1 (p + 904) = x := ⟨_, rfl⟩
  obtain ⟨scF, hscF⟩ : ∃ x, scSpec2 v va gC3 4 pkF.2.2.2.1 pkF.1 11 = x := ⟨_, rfl⟩
  obtain ⟨p3, hp3⟩ : ∃ x, pkF.2.2.2.1 + 11 * roundLen2 4 = x := ⟨_, rfl⟩
  have hpkEnd : pkF.2.2.2.1 = p + 904 + 112 * (c.P + 1) := by rw [← hpkF, packSpec2_pos, hCptL]
  have hp3' : p3 = p + 2312 + 112 * (c.P + 1) := by rw [← hp3, hpkEnd]; simp only [roundLen2]; omega
  have hscL : scF.1.length = 11 := by
    rw [← hscF, scSpec2_length]
  obtain ⟨fC, fP, fO1, fO2⟩ := layerSpec2_fields v va io C p hpkF hscF hp3
  rw [fC, fP, fO1, fO2]
  dsimp only [layerTB2] at h0
  -- zero, one
  obtain ⟨base, n1, ebase, h1, h0⟩ := peelN2 h0 (noA_q2Base _)
  have hb := q2Base_spec h1
  rw [ebase] at hb
  obtain ⟨hzK, hz, hone⟩ := hb
  -- the projection
  obtain ⟨proj, n2, eproj, h2, h0⟩ := peelN2 h0 (noA_q2Proj _ _ _ _)
  have hprodv : ∀ k < 47,
      (((List.range productBits).map fun k => lane2 (c.q + 2 * k) [c.str2]).getD k default).valF xv V =
        (scalars2 v (p + 40) productBits).getD k 0 := by
    intro k hk
    rw [List.getD_eq_getElem _ _ (by simpa [hPB] using hk), List.getElem_map, List.getElem_range,
      hlane _ (by rw [hstr]; omega), scalars2_getD _ _ (by rw [hPB]; exact hk),
      show 8 * (c.q + 2 * k) + off = p + 40 + 16 * k by omega]
  have hproj : proj.valF xv V = projectedF C (scalars2 v (p + 40) productBits) := by
    rw [← eproj, q2Proj_spec hz _ _ _ _ h2, projectedF_eq2, hRmu, List.length_map, List.length_range,
      show (47 : Nat) = productBits from rfl]
    refine congrArg sumF (List.map_congr_left fun k hk => ?_)
    rw [hprodv k (List.mem_range.mp hk)]
  -- check 1: the projection and the iota term
  obtain ⟨seg0, n3, eseg0, h3, h0⟩ := peelN2 h0 (noA_q2One _)
  obtain ⟨in0, n4, ein0, h4, h0⟩ := peelN2 h0 (noA_q2Dot _ _)
  obtain ⟨in1, n5, ein1, h5, h0⟩ := peelN2 h0 (noA_q2Dot _ _)
  obtain ⟨iota, n6, eiota, h6, h0⟩ := peelN2 h0 (noA_q2Dot _ _)
  obtain ⟨e1, n7, ee1, h7, h0⟩ := peelN2 h0 (noA_q2Mul _ _ _)
  obtain ⟨e1', n8, ee1', h8, h0⟩ := peelN2 h0 (noA_q2Add _ _)
  obtain ⟨n9, h0⟩ := peelA2 h0
  have hk : ∀ i < 7, (kS2 (c.k i) base.1).valF xv V = rcBitG rc0 i ∧
      (kS2 (c.k (7 + i)) base.1).valF xv V = rcBitG rc1 i := by
    intro i hi
    refine ⟨?_, ?_⟩
    · show (⟨(xv (c.k i)).c₀, (base.1.valF xv V).c₀⟩ : FE2) = _
      rw [(hrc i hi).1, hzK, rcBit_s2]
    · show (⟨(xv (c.k (7 + i))).c₀, (base.1.valF xv V).c₀⟩ : FE2) = _
      rw [(hrc i hi).2, hzK, rcBit_s2]
  have hin0 : in0.valF xv V = iotaFG rc0 C.weights := by
    rw [iota_rep2 hR RC1m, ← ein0, q2Dot_spec _ _ _ h4, hz, zero_add, List.map_map, sumF_eq_sum]
    refine congrArg List.sum (List.map_congr_left fun i hi => ?_)
    have hi' := List.mem_range.mp hi
    show (kS2 (c.k i) base.1).valF xv V *
      (((List.range 7).map fun i => c.pv2 (50 + c.P + i)).getD i default).valF xv V = _
    rw [hflS i hi', (hk i hi').1]
  have hin1 : in1.valF xv V = iotaFG rc1 C.weights := by
    rw [iota_rep2 hR RC2m, ← ein1, q2Dot_spec _ _ _ h5, hz, zero_add, List.map_map, sumF_eq_sum]
    refine congrArg List.sum (List.map_congr_left fun i hi => ?_)
    have hi' := List.mem_range.mp hi
    show (kS2 (c.k (7 + i)) base.1).valF xv V *
      (((List.range 7).map fun i => c.pv2 (50 + c.P + i)).getD i default).valF xv V = _
    rw [hflS i hi', (hk i hi').2]
  have hseg0 : seg0.valF xv V = 1 + C.point.getD c.P 0 := by rw [← eseg0, q2One_spec h3, hptP, hσ]
  have hiota : iota.valF xv V = io C := by
    rw [hio, ← hin0, ← hin1, ← hseg0, ← eiota, q2Dot_spec _ _ _ h6, hz, hptP, hσ]
    simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, zero_add, add_zero]
  have he1' : e1'.valF xv V = (io C * sumF C.mu + projectedF C (scalars2 v (p + 40) productBits)) + C.value := by
    rw [← ee1', q2Add_spec h8, ← ee1, q2Mul_spec h7, hiota, hproj,
      show (c.pv2 17).valF xv V = sumF C.mu from hR.kappa, show (c.pv2 0).valF xv V = C.value from hR.value]
  have hK1 : e1'.valF xv V = 0 ↔
      (projectedF C (scalars2 v (p + 40) productBits) + io C * sumF C.mu == C.value) = true := by
    rw [he1', fe2_beq_iff, fe2_add_eq_zero, add_comm (io C * _)]
  have hK1c : e1'.valF xv V = 0 ↔ (e1'.1.valF xv V = 0 ∧ e1'.2.valF xv V = 0) := by
    rw [← ee1']; exact emit2_zero_iff h8
  -- instance weights, the pack value, the rounds
  obtain ⟨mk, n10, emk, h10, h0⟩ := peelN2 h0 (noA_q2Inst _ _ _ _)
  have hs : (lane2 (c.q + 104) [c.str2]).valF xv V = e2OfFE (va (p + 872)) := by
    rw [hlane _ (by rw [hstr]; omega), ← hva, show 8 * (c.q + 104) + off = p + 872 by omega]
  obtain ⟨hmk1, hmk2⟩ := q2Inst_spec hz hone rmfeEmbed _ h10
  rw [emk, hs] at hmk1
  rw [emk] at hmk2
  have hmu' : vals2 xv V mk.1 = instWeightsF (e2OfFE (va (p + 872))) := by rw [hmk1, instWeightsF_eq2]
  have hkap : mk.2.valF xv V = sumF (instWeightsF (e2OfFE (va (p + 872)))) := by rw [hmk2, hmu', sumF_eq_sum]
  have hmkL : mk.1.length = 16 := by
    have := congrArg List.length hmu'; rw [vals2, List.length_map, instWeightsF_length] at this; exact this
  obtain ⟨v0, n11, ev0, h11, h0⟩ := peelN2 h0 (noA_q2Horner _ _ _)
  have hv0 : v0.valF xv V = polyEvalF (scalars2 v (p + 40) productBits) (e2OfFE (va (p + 872))) := by
    have hsplit : scalars2 v (p + 40) productBits =
        (List.range 46).map (fun k => (scalars2 v (p + 40) productBits).getD k 0) ++
          [(scalars2 v (p + 40) productBits).getD 46 0] := by
      apply List.ext_getElem (by simp [scalars2, hPB])
      intro i h1 h2
      rw [List.getElem_append]
      simp only [List.length_map, List.length_range]
      split
      · rw [List.getElem_map, List.getElem_range, List.getD_eq_getElem _ _ h1]
      · have : i = 46 := by simp [scalars2, hPB] at h1; omega
        subst this
        rw [List.getD_eq_getElem _ _ h1]; simp
    rw [← ev0, q2Horner_spec _ _ _ _ h11, hs, hsplit, polyEvalF_horner2, hprodv 46 (by norm_num), vals2,
      List.map_map, List.map_reverse]
    refine congrArg (hornerVal2 _ _) (congrArg List.reverse (List.map_congr_left fun k hk => ?_))
    exact hprodv k (by have := List.mem_range.mp hk; omega)
  obtain ⟨pk, n12, epk, h12, h0⟩ := peelN2 h0 (noA_q2PackRounds _ _ _ _ _ _)
  have hpk := q2PackRounds_spec hz hva gC3 hv _ (c.q + 113) (p + 904)
    (by simp only [List.length_map, List.length_range]; rw [hstr]; omega) (by omega) _ _ _ h12
  rw [epk, hRpt, hv0, hone, hpkF] at hpk
  obtain ⟨hpk1, hpk2, hpk3⟩ := hpk
  have hpkL : pk.2.2.length = c.P + 1 := by
    have := congrArg List.length hpk3
    rw [vals2, List.length_map, ← hpkF, packSpec2_length, hCptL] at this
    exact this
  obtain ⟨lc, n13, elc, h13, h0⟩ := peelN2 h0 (noA_q2LocalRounds _ _ _ _)
  have hlc := q2LocalRounds_spec hva gC3 hv 11 (c.q + 113 + 14 * (c.P + 1)) pkF.2.2.2.1
    (by rw [hstr]; omega) (by rw [hpkEnd]; omega) pk.1 _ h13
  rw [elc, hpk1, hscF] at hlc
  obtain ⟨hlc1, hlc2⟩ := hlc
  have hlcL : lc.2.length = 11 := by
    have := congrArg List.length hlc2; rwa [vals2, List.length_map, hscL] at this
  -- `t`, `β`
  have htv : ∀ k < 3,
      (((List.range 3).map fun k => lane2 (c.q + 289 + 14 * (c.P + 1) + 2 * k) [c.str2]).getD k default).valF xv V =
        (scalars2 v (p3 + 40) 3).getD k 0 := by
    intro k hk
    rw [List.getD_eq_getElem _ _ (by simpa using hk), List.getElem_map, List.getElem_range,
      hlane _ (by rw [hstr]; omega), scalars2_getD _ _ hk,
      show 8 * (c.q + 289 + 14 * (c.P + 1) + 2 * k) + off = p3 + 40 + 16 * k by rw [hp3']; omega]
  have hbeta : (lane2 (c.q + 289 + 14 * (c.P + 1) + 7) [c.str2]).valF xv V = e2OfFE (va (p3 + 96)) := by
    rw [hlane _ (by rw [hstr]; omega), ← hva,
      show 8 * (c.q + 289 + 14 * (c.P + 1) + 7) + off = p3 + 96 by rw [hp3']; omega]
  -- the `eq` tables
  obtain ⟨tbLo, n14, etbLo, h14, h0⟩ := peelN2 h0 (noA_q2EqTab _ _ _)
  obtain ⟨tbHi, n15, etbHi, h15, h0⟩ := peelN2 h0 (noA_q2EqTab _ _ _)
  obtain ⟨taLo, n16, etaLo, h16, h0⟩ := peelN2 h0 (noA_q2EqTab _ _ _)
  obtain ⟨taHi, n17, etaHi, h17, h0⟩ := peelN2 h0 (noA_q2EqTab _ _ _)
  obtain ⟨eL, n18, eeL, h18, h0⟩ := peelN2 h0 (noA_q2EqTab _ _ _)
  have hA : vals2 xv V ((List.range 6).map fun i => c.pv2 (44 + c.P + i)) =
      repA2 c.P (fun j => (c.pv2 j).valF xv V) := by
    rw [vals2, List.map_map]; rfl
  have hAL : (repA2 c.P (fun j => (c.pv2 j).valF xv V)).length = 6 := by simp [repA2]
  have hbL : (scF.1.take 6).length = 6 := by simp [hscL]
  have hvb : vals2 xv V (lc.2.take 6) = scF.1.take 6 := by rw [vals2, List.map_take, ← vals2, hlc2]
  have htbLo : vals2 xv V tbLo = eqKernelF ((scF.1.take 6).take 3) := by
    rw [← etbLo, eqTab_one2 hz hone _ _ h14, vals2, List.map_take, ← vals2, hlc2, List.take_take]; rfl
  have htbHi : vals2 xv V tbHi = eqKernelF ((scF.1.take 6).drop 3) := by
    rw [← etbHi, eqTab_one2 hz hone _ _ h15, vals2, List.map_take, List.map_drop, ← vals2, hlc2, List.drop_take]
  have htaLo : vals2 xv V taLo = eqKernelF ((repA2 c.P (fun j => (c.pv2 j).valF xv V)).take 3) := by
    rw [← etaLo, eqTab_one2 hz hone _ _ h16, vals2, List.map_take, ← vals2, hA]
  have htaHi : vals2 xv V taHi = eqKernelF ((repA2 c.P (fun j => (c.pv2 j).valF xv V)).drop 3) := by
    rw [← etaHi, eqTab_one2 hz hone _ _ h17, vals2, List.map_drop, ← vals2, hA]
  have heL : vals2 xv V eL = eqKernelF (scF.1.drop 6) := by
    rw [← eeL, eqTab_one2 hz hone _ _ h18, vals2, List.map_drop, ← vals2, hlc2]
  have heLL : eL.length = 32 := by
    have := congrArg List.length heL
    rw [vals2, List.length_map, eqKernelF_length, List.length_drop, hscL] at this
    exact this
  -- the shift tables
  obtain ⟨L0, n19, eL0, h19, h0⟩ := peelN2 h0 (noA_mapT2 (fun _ => noA_q2LowTab _ _ _ _ _) _)
  have hL0 : vals2 xv V L0 = (List.range 8).map (lowTabG (repA2 c.P (fun j => (c.pv2 j).valF xv V)) (scF.1.take 6) 0) := by
    rw [← eL0]
    exact forall₂_map_eq2 (mapT2_spec (P := fun rl x => S2.valF xv V x = lowTabG _ _ 0 rl)
      (fun rl m hm => q2LowTab_spec hz htaLo htbLo (by rw [hAL]; norm_num) (by rw [hbL]; norm_num) 0 rl m hm) _ _ h19)
  obtain ⟨L1, n20, eL1, h20, h0⟩ := peelN2 h0 (noA_mapT2 (fun _ => noA_q2LowTab _ _ _ _ _) _)
  have hL1 : vals2 xv V L1 = (List.range 8).map (lowTabG (repA2 c.P (fun j => (c.pv2 j).valF xv V)) (scF.1.take 6) 1) := by
    rw [← eL1]
    exact forall₂_map_eq2 (mapT2_spec (P := fun rl x => S2.valF xv V x = lowTabG _ _ 1 rl)
      (fun rl m hm => q2LowTab_spec hz htaLo htbLo (by rw [hAL]; norm_num) (by rw [hbL]; norm_num) 1 rl m hm) _ _ h20)
  obtain ⟨H, n21, eH, h21, h0⟩ := peelN2 h0 (noA_mapT2 (fun _ => noA_q2HighTab _ _ _ _) _)
  have hH : vals2 xv V H = (List.range 8).map (highTabG (repA2 c.P (fun j => (c.pv2 j).valF xv V)) (scF.1.take 6)) := by
    rw [← eH]
    exact forall₂_map_eq2 (mapT2_spec (P := fun k x => S2.valF xv V x = highTabG _ _ k)
      (fun k m hm => q2HighTab_spec hz htaHi htbHi hAL hbL k m hm) _ _ h21)
  obtain ⟨sh, n22, esh, h22, h0⟩ := peelN2 h0 (noA_mapT2 (fun _ => noA_q2Shift _ _ _ _ _) _)
  have hsh0 : vals2 xv V sh =
      (List.range 64).map (shiftLHG (repA2 c.P (fun j => (c.pv2 j).valF xv V)) (scF.1.take 6)) := by
    rw [← esh]
    exact forall₂_map_eq2 (mapT2_spec_mem (P := fun r x => S2.valF xv V x = shiftLHG _ _ r) _
      (fun r hr m hm => q2Shift_spec hz hL0 hL1 hH (List.mem_range.mp hr) m hm) _ h22)
  have hshL : sh.length = 64 := by rw [← esh, mapT2_length, List.length_range]
  have hsh : ∀ r < 64, (sh.getD r default).valF xv V =
      rotSumG (eqAtG (scF.1.take 6)) (eqAtG (repA2 c.P (fun j => (c.pv2 j).valF xv V))) r := by
    intro r hr
    rw [getD_valF2 _ (by omega), hsh0, shift_LHG hAL hbL hr, List.getD_eq_getElem _ _ (by simpa using hr),
      List.getElem_map, List.getElem_range]
  -- the final check's weight
  have hBS : vals2 xv V ((List.range 25).map fun l => c.pv2 (19 + c.P + l)) =
      repB2 c.P (fun j => (c.pv2 j).valF xv V) := by
    rw [vals2, List.map_map]; rfl
  obtain ⟨Wk, n23, eWk, h23, h0⟩ :=
    peelN2 h0 (noA_q2SumMap _ _ fun _ => noA_bind (noA_q2LaneForm _ _ _ _) fun _ => noA_q2Mul _ _ _)
  have hWk : Wk.valF xv V = ((List.range 25).map fun l => (eqKernelF (scF.1.drop 6)).getD l 0 *
      laneFormF (repB2 c.P (fun j => (c.pv2 j).valF xv V))
        (rotSumG (eqAtG (scF.1.take 6)) (eqAtG (repA2 c.P (fun j => (c.pv2 j).valF xv V)))) l).sum := by
    rw [← eWk]
    refine q2SumMap_spec hz (fun l hl m hm => ?_) _ h23
    obtain ⟨g1, g2⟩ := (thold2_bind _ _).mp hm
    rw [tb_bind, q2Mul_spec g2, q2LaneForm_spec hz (by simp) _ hl _ g1, hz, add_zero, getD_valF2 _ (by omega), heL,
      hBS, laneFormF_congr _ hsh l]
  obtain ⟨dfB, n24, edfB, h24, h0⟩ := peelN2 h0 (noA_q2SumMap _ _ fun _ => noA_q2Mul _ _ _)
  have hdfB : dfB.valF xv V = ((List.range 25).map fun l =>
      (eqKernelF (scF.1.drop 6)).getD l 0 * (repB2 c.P (fun j => (c.pv2 j).valF xv V)).getD l 0).sum := by
    rw [← edfB]
    refine q2SumMap_spec hz (fun l hl m hm => ?_) _ h24
    rw [q2Mul_spec hm, hz, add_zero, getD_valF2 _ (by omega), heL, getD_valF2 _ (by simp; omega), hBS]
  obtain ⟨idx, n25, eidx, h25, h0⟩ := peelN2 h0 (noA_q2Index _ _ _ _)
  have hidx : idx.valF xv V = indexProdG gx (scF.1.take 6) := by
    have hlen : (lc.2.take 6).length = (scF.1.take 6).length := by rw [← hvb, vals2, List.length_map]
    rw [← eidx, q2Index_spec hz _ _ _ _ h25, hone, one_mul, indexProdG, hlen, hvb]
    simp only [Nat.zero_add]
  obtain ⟨Wf, n26, eWf, h26, h0⟩ := peelN2 h0 (noA_q2Mul _ _ _)
  obtain ⟨d, n27, ed, h27, h0⟩ := peelN2 h0 (noA_q2Add _ _)
  obtain ⟨W, n28, eW, h28, h0⟩ := peelN2 h0 (noA_q2Mul _ _ _)
  have hk14 : (kS2 (c.k 14) base.1).valF xv V = if first then 1 else 0 := by
    show (⟨(xv (c.k 14)).c₀, (base.1.valF xv V).c₀⟩ : FE2) = _
    rw [hfirst, hzK]; cases first <;> rfl
  have hW : W.valF xv V = dotF ((eqKernelF scF.1).take LeanVM.Protocol.Verifier.keccakBits) C.weights := by
    rw [weighted_rep2 hR hscL, ← eW, q2Mul_spec h28, ← ed, q2Add_spec h27, ← eWf, q2Mul_spec h26, hz, add_zero,
      hdfB, hidx, hWk, hk14]
    cases first
    · simp only [Bool.false_eq_true, ite_false, zero_mul, zero_add]
    · simp only [ite_true, one_mul, add_assoc, fe2_add_self, add_zero]
  -- check 2
  obtain ⟨kt0, n29, ekt0, h29, h0⟩ := peelN2 h0 (noA_q2Mul _ _ _)
  obtain ⟨k1, n30, ek1, h30, h0⟩ := peelN2 h0 (noA_q2Add _ _)
  obtain ⟨mm, n31, emm, h31, h0⟩ := peelN2 h0 (noA_q2Mul _ _ _)
  obtain ⟨sw, n32, esw, h32, h0⟩ := peelN2 h0 (noA_q2Mul _ _ _)
  obtain ⟨e2, n33, ee2, h33, h0⟩ := peelN2 h0 (noA_q2Mul _ _ _)
  obtain ⟨n34, h0⟩ := peelA2 h0
  have he2 : e2.valF xv V = pkF.2.1 * dotF ((eqKernelF scF.1).take LeanVM.Protocol.Verifier.keccakBits) C.weights *
      (sumF (instWeightsF (e2OfFE (va (p + 872)))) * (scalars2 v (p3 + 40) 3).getD 0 0 +
        (sumF (instWeightsF (e2OfFE (va (p + 872)))) + (scalars2 v (p3 + 40) 3).getD 1 0) *
          (scalars2 v (p3 + 40) 3).getD 2 0) + scF.2.1 := by
    rw [← ee2, q2Mul_spec h33, ← esw, q2Mul_spec h32, ← emm, q2Mul_spec h31, ← ek1, q2Add_spec h30, ← ekt0,
      q2Mul_spec h29, hz, hW, hkap, hpk2, hlc1, htv 0 (by norm_num), htv 1 (by norm_num), htv 2 (by norm_num)]
    ring
  have hK2 : e2.valF xv V = 0 ↔ (pkF.2.1 * dotF ((eqKernelF scF.1).take LeanVM.Protocol.Verifier.keccakBits) C.weights *
      (sumF (instWeightsF (e2OfFE (va (p + 872)))) * (scalars2 v (p3 + 40) 3).getD 0 0 +
        (sumF (instWeightsF (e2OfFE (va (p + 872)))) + (scalars2 v (p3 + 40) 3).getD 1 0) *
          (scalars2 v (p3 + 40) 3).getD 2 0) == scF.2.1) = true := by
    rw [he2, fe2_beq_iff, fe2_add_eq_zero]
  have hK2c : e2.valF xv V = 0 ↔ (e2.1.valF xv V = 0 ∧ e2.2.valF xv V = 0) := by
    rw [← ee2]; exact emit2_zero_iff h33
  -- the next claim
  obtain ⟨tt, n35, ett, h35, h0⟩ := peelN2 h0 (noA_q2Mul _ _ _)
  obtain ⟨v', n36, ev', h36, h0⟩ := peelN2 h0 (noA_q2Mul _ _ _)
  have hv' : v'.valF xv V = (scalars2 v (p3 + 40) 3).getD 0 0 + e2OfFE (va (p3 + 96)) *
      ((scalars2 v (p3 + 40) 3).getD 1 0 + e2OfFE (va (p3 + 96)) * (scalars2 v (p3 + 40) 3).getD 2 0) := by
    rw [← ev', q2Mul_spec h36, ← ett, q2Mul_spec h35, hbeta, htv 0 (by norm_num), htv 1 (by norm_num),
      htv 2 (by norm_num)]
    ring
  obtain ⟨B', n37, eB', h37, h0⟩ := peelN2 h0 (noA_q2LaneW _ _)
  have hB' : vals2 xv V B' = (List.range 25).map fun l => (eqKernelF (scF.1.drop 6)).getD l 0 + e2OfFE (va (p3 + 96)) *
      ((eqKernelF (scF.1.drop 6)).getD (keccakAlong (64 * l) 4 / 64) 0 + e2OfFE (va (p3 + 96)) *
        (eqKernelF (scF.1.drop 6)).getD (keccakAlong (64 * l) 3 / 64) 0) := by
    rw [← eB', q2LaneW_spec (by omega) _ _ h37, heL, hbeta]
  have hB'L : B'.length = 25 := by
    have := congrArg List.length hB'
    rwa [vals2, List.length_map, List.length_map, List.length_range] at this
  obtain ⟨A', n38, eA', h38, h0⟩ := peelN2 h0 (noA_q2EqTab _ _ _)
  have hA' : vals2 xv V A' = eqKernelF (scF.1.take 6) := by rw [← eA', eqTab_one2 hz hone _ _ h38, hvb]
  have hA'L : A'.length = 64 := by
    have := congrArg List.length hA'
    rw [vals2, List.length_map, eqKernelF_length, hbL] at this
    exact this
  obtain ⟨fl, n39, efl, h39, h0⟩ := peelN2 h0 (noA_mapT2 (fun _ => noA_q2Flip _ _ _ _) _)
  have hfl : vals2 xv V fl = (List.range 7).map (flipFormG (vals2 xv V B') (eqAtG (scF.1.take 6))) := by
    rw [← efl]
    refine forall₂_map_eq2 (mapT2_spec (P := fun i x => S2.valF xv V x = flipFormG (vals2 xv V B') (eqAtG (scF.1.take 6)) i)
      (fun i m hm => ?_) _ _ h39)
    rw [q2Flip_spec hz (by omega) hA'L i m hm, hA']
    rfl
  have hflL : fl.length = 7 := by rw [← efl, mapT2_length, List.length_range]
  -- the copy rows
  obtain ⟨hcp, h0⟩ := peelL2 h0 (noA_mapT2 (fun _ => noA_q2Copy _) _)
  obtain ⟨hLn, hTA⟩ := inv_end2 h0
  rw [mapT2_q2Copy_snd, cpIns2_length] at hLn
  simp only [List.length_append, List.length_singleton, hmkL, hpkL, hB'L, List.length_take, hlcL, hflL] at hLn
  have hcbN : n39 = c.cb := by omega
  rw [mapT2_q2Copy_snd, hcbN] at hcp
  obtain ⟨c6, cfl⟩ := cp2_append hcp
  obtain ⟨c5, cA⟩ := cp2_append c6
  obtain ⟨c4, cB⟩ := cp2_append c5
  obtain ⟨c3, cPt⟩ := cp2_append c4
  obtain ⟨c2, cK⟩ := cp2_append c3
  obtain ⟨cV, cM⟩ := cp2_append c2
  simp only [List.length_append, List.length_singleton, hmkL, hpkL, hB'L, List.length_take, hlcL] at cM cK cPt cB cA cfl
  have hrA : repA2 c.P (fun j => (⟨(V (c.cb + 2 * j)).c₀, (V (c.cb + 2 * j + 1)).c₀⟩ : FE2)) = scF.1.take 6 := by
    rw [← hvb, ← cp2_range cA (k := 6) (by simp [hlcL])]
    unfold repA2
    refine List.map_congr_left fun i _ => ?_
    dsimp only
    rw [show c.cb + 2 * (44 + c.P + i) = c.cb + 2 * (1 + 16 + 1 + (c.P + 1) + 25) + 2 * i by omega]
  have hrB : repB2 c.P (fun j => (⟨(V (c.cb + 2 * j)).c₀, (V (c.cb + 2 * j + 1)).c₀⟩ : FE2)) = vals2 xv V B' := by
    rw [← cp2_range cB hB'L]
    unfold repB2
    refine List.map_congr_left fun i _ => ?_
    dsimp only
    rw [show c.cb + 2 * (19 + c.P + i) = c.cb + 2 * (1 + 16 + 1 + (c.P + 1)) + 2 * i by omega]
  refine ⟨⟨?_, ?_, ?_, ?_, ?_, ?_⟩, ?_, ?_, ?_⟩
  · -- value
    have := cp2_get' cV 0 (by simp)
    rw [Nat.mul_zero, Nat.add_zero] at this
    show (⟨(V (c.cb + 2 * 0)).c₀, (V (c.cb + 2 * 0 + 1)).c₀⟩ : FE2) = _
    rw [Nat.mul_zero, Nat.add_zero, this]
    simp only [vals2, List.map_cons, List.map_nil, List.getD_cons_zero]
    exact hv'
  · -- μ
    show (List.range 16).map (fun i => (⟨(V (c.cb + 2 * (1 + i))).c₀, (V (c.cb + 2 * (1 + i) + 1)).c₀⟩ : FE2)) =
      instWeightsF (e2OfFE (va (p + 872)))
    rw [← hmu', ← cp2_range cM hmkL]
    refine List.map_congr_left fun i _ => ?_
    rw [show c.cb + 2 * (1 + i) = c.cb + 2 * 1 + 2 * i by omega]
  · -- κ
    have := cp2_get' cK 0 (by simp)
    show (⟨(V (c.cb + 2 * 17)).c₀, (V (c.cb + 2 * 17 + 1)).c₀⟩ : FE2) = _
    rw [show c.cb + 2 * 17 = c.cb + 2 * (1 + 16) + 2 * 0 by omega, this]
    simp only [vals2, List.map_cons, List.map_nil, List.getD_cons_zero]
    exact hkap
  · -- the point
    show (List.range (c.P + 1)).map (fun i => (⟨(V (c.cb + 2 * (18 + i))).c₀, (V (c.cb + 2 * (18 + i) + 1)).c₀⟩ : FE2)) =
      pkF.2.2.1
    rw [← hpk3, ← cp2_range cPt hpkL]
    refine List.map_congr_left fun i _ => ?_
    rw [show c.cb + 2 * (18 + i) = c.cb + 2 * (1 + 16 + 1) + 2 * i by omega]
  · -- the weights
    simp only [Bool.false_eq_true, ite_false]
    rw [hrA, hrB, hB', next_weights hscL]
  · -- the flips
    intro i hi
    simp only [Bool.false_eq_true, ite_false]
    rw [hrA, hrB]
    have := cp2_get' cfl i (by rw [hflL]; exact hi)
    rw [show min 6 11 = 6 from rfl] at this
    show (⟨(V (c.cb + 2 * (50 + c.P + i))).c₀, (V (c.cb + 2 * (50 + c.P + i) + 1)).c₀⟩ : FE2) = _
    rw [show c.cb + 2 * (50 + c.P + i) = c.cb + 2 * (1 + 16 + 1 + (c.P + 1) + 25 + 6) + 2 * i by omega, this, hfl,
      List.getD_eq_getElem _ _ (by simpa using hi), List.getElem_map, List.getElem_range]
  · -- the position
    rw [hp3', hstr]; omega
  · intro hta hg
    obtain ⟨⟨-, q1⟩, q2⟩ := hTA.mp hta
    have hg' : (c.k 15).valF xv V = 1 := hg
    rw [hg', one_mul, one_mul] at q1 q2
    exact ⟨hK1.mp (hK1c.mpr q1), hK2.mp (hK2c.mpr q2)⟩
  · intro o1 o2
    have a1 := hK1c.mp (hK1.mpr o1)
    have a2 := hK2c.mp (hK2.mpr o2)
    exact hTA.mpr ⟨⟨trivial, by rw [a1.1, mul_zero], by rw [a1.2, mul_zero]⟩, by rw [a2.1, mul_zero],
      by rw [a2.2, mul_zero]⟩

/-- **One layer at `E2`** (`layerTB2` replays `V`'s `verifyKeccakLayerD`): in any memory where the layer template's
rows hold (twin rows included) and its carried values represent `V`'s claim `C`, the copy rows represent the claim
`layerSpec2` returns, the position moves by `8·str2`, and with the gate `1` the assertions hold iff both checks do. -/
theorem layer2_spec {c : LCfg} {xv : Src → FE} {V : Nat → FE} (hH : THold2 xv V 0 (layerTB2 c 0).2)
    (hcb : c.cb + 2 * (57 + c.P) = (layerTB2 c 0).2.length)
    {C : KClaim FE2} {first : Bool} (hR : Rep2 c.P (fun j => (c.pv2 j).valF xv V) C first)
    {io : KClaim FE2 → FE2} {rc0 rc1 : UInt64} (RC1m : rc0 ∈ keccakRC) (RC2m : rc1 ∈ keccakRC)
    (hio : io C = (1 + C.point.getD c.P 0) * iotaFG rc0 C.weights + C.point.getD c.P 0 * iotaFG rc1 C.weights)
    (hrc : ∀ i < 7, xv (c.k i) = rcBit rc0 i ∧ xv (c.k (7 + i)) = rcBit rc1 i)
    (hfirst : xv (c.k 14) = if first then 1 else 0)
    {v : Nat → FE2} {va : Nat → FE} (hva : ∀ o, e2OfFE (va o) = v o)
    {off p : Nat} (hv : ∀ m < c.q + c.str2, lv2 xv [c.str2] m = v (8 * m + off))
    (hp : p + 40 = 8 * c.q + off) :
    Rep2 c.P (fun j => ⟨(V (c.cb + 2 * j)).c₀, (V (c.cb + 2 * j + 1)).c₀⟩) (layerSpec2 v va io C p).claim false ∧
    (layerSpec2 v va io C p).pos = p + 8 * c.str2 ∧
    (TAssert xv V (layerTB2 c 0).2 → xv (c.k 15) = 1 →
      (layerSpec2 v va io C p).ok1 = true ∧ (layerSpec2 v va io C p).ok2 = true) ∧
    ((layerSpec2 v va io C p).ok1 = true → (layerSpec2 v va io C p).ok2 = true → TAssert xv V (layerTB2 c 0).2) :=
  layer2_core (inv_start2 hH) hcb hR RC1m RC2m hio hrc hfirst hva hv hp

end Lvm.Q1
