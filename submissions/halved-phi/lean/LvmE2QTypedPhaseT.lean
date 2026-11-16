-- New for lvm2 S2GT (GT-C3): S2GT-STMT 10c, the typed phases at S2GT in the circuit replay V_S's (`typedGT` replays
-- `LvmE2TV.dTypedT`): the `E2` twins of `LvmE2QTypedPhase` (zerocheck, wiring, relayout, A23) on the schedule's lanes,
-- the `E3` mini-bus by roll 11's `miniG_replays`.
import LvmE2QTypedKitT
import LvmE2QLReplay
import LvmE2VDecG

/-!
# `typedGT` replays `dTypedT` (S2GT-STMT 10c)

* The rounds: `eqRuns2` (equality mode) and `plainRuns2` on lanes `L (i₀ + 3k) = q + 14k`, `L (i₀ + 3k + 2) = q + 14k + 5`
  are V's `sumcheckD` from the cursor at `8q − 40`: the challenges are the answers, the final claim `eqFold2` /
  `scFold2` of the stream's `E2` values.
* **`zeroGT_run`**, **`wireGT_run`**, **`relayGT_run`**, **`qaccGT_run`**: each gadget, where its rows hold and assert
  (gate on), replays its V phase from the cursor `P` (`ok` kept, the end position, the values the gadget's cells').
* **`typed_phaseT`**: the composition in the `PhaseAt` form `core_of_phasesG` takes.
-/

set_option autoImplicit false

namespace Lvm.E2Q

open Lvm Lvm.Loop Lvm.Loop.Build Lvm.Har Lvm.Q1 Lvm.Q2 DM Lvm.E2V Lvm.QTyped

/-! ## The rounds -/

/-- One equality-mode round's next claim: `polyEval [claim + τ(c₁ + c₂), c₁, c₂] r`. -/
def eqStepE (c1 c2 r τ claim : FE2) : FE2 := (c2 * r + c1) * r + (τ * (c1 + c2) + claim)

/-- Equality-mode rounds' final claim from lane `q` (round `k`'s message at `q + 14k`, its answer at `q + 14k + 5`). -/
def eqFold2 (v : Nat → FE2) : List FE2 → Nat → FE2 → FE2
  | [], _, claim => claim
  | τ :: τs, q, claim => eqFold2 v τs (q + 14) (eqStepE (v q) (v (q + 2)) (v (q + 5)) τ claim)

theorem roundPolyDE_run (claim τ : FE2) (sig : ByteArray) (s : RS) :
    roundPolyD 3 claim (some τ) sig s = ([claim + τ * sumF [fe2At sig (rpos s + 40), fe2At sig (rpos s + 56)],
      fe2At sig (rpos s + 40), fe2At sig (rpos s + 56)], { s with msg := s.msg + 16 * 2 }) := by
  show (readE2s 2 >>= fun tail => pure ((claim + τ * sumF tail) :: tail)) sig s = _
  rw [dbind_run, Lvm.Q2.readE2s_run, dpure_run]
  have e : (List.range 2).map (fun i => fe2At sig (rpos s + 40 + 16 * i)) =
      [fe2At sig (rpos s + 40), fe2At sig (rpos s + 56)] := by
    simp only [List.range_succ, List.range_zero, List.nil_append, List.map_cons, List.map_nil, List.cons_append]
  rw [e]

theorem polyEvalE (c1 c2 r τ claim : FE2) :
    polyEvalF [claim + τ * sumF [c1, c2], c1, c2] r = eqStepE c1 c2 r τ claim := by
  simp only [polyEvalF, sumF, eqStepE, List.foldr_cons, List.foldr_nil, List.foldl_cons, List.foldl_nil]
  ring

/-- **V's equality-mode `E2` sumcheck (count 3)** from a cursor whose first message is at lane `q`. -/
theorem sumcheckDE_run (g : Nat) (sig : ByteArray) : ∀ (τs : List FE2) (claim : FE2) (s : RS) (q : Nat),
    8 * q = rpos s + 40 →
    (sumcheckD g claim 3 (τs.map some) sig s).1 =
        ((List.range τs.length).map (fun k => fe2At sig (rpos s + 80 + 112 * k)),
          eqFold2 (fun k => fe2At sig (8 * k)) τs q claim) ∧
      rpos (sumcheckD g claim 3 (τs.map some) sig s).2 = rpos s + 112 * τs.length ∧
      (sumcheckD g claim 3 (τs.map some) sig s).2.ok = (okS g sig (rpos s) τs.length && s.ok)
  | [], claim, s, q, _ => ⟨rfl, rfl, by show s.ok = (true && s.ok); rw [Bool.true_and]⟩
  | τ :: τs, claim, s, q, hq => by
    have e : sumcheckD g claim 3 ((τ :: τs).map some) = (roundPolyD 3 claim (some τ) >>= fun msg =>
        sampleG g >>= fun c => sumcheckD g (polyEvalF msg c) 3 (τs.map some) >>= fun res =>
          pure (c :: res.1, res.2)) := rfl
    rw [e, dbind_run, roundPolyDE_run, dbind_run, Lvm.Q2.sampleG_run, dbind_run, dpure_run]
    dsimp only
    have hp1 : ∀ o : Bool, rpos (⟨s.ent + 72 + (s.msg + 16 * 2 + 8), 0, o⟩ : RS) = rpos s + 112 := by
      intro o; simp only [rpos]; omega
    have hb : s.ent + 40 + (s.msg + 16 * 2 + 8) = rpos s + 80 := by simp only [rpos]; omega
    rw [hb, Lvm.Q2.e2OfFE_feAt]
    obtain ⟨h1, h2, h3⟩ := sumcheckDE_run g sig τs
      (polyEvalF [claim + τ * sumF [fe2At sig (rpos s + 40), fe2At sig (rpos s + 56)], fe2At sig (rpos s + 40),
        fe2At sig (rpos s + 56)] (fe2At sig (rpos s + 80)))
      ⟨s.ent + 72 + (s.msg + 16 * 2 + 8), 0, powOKR g (feAt sig (rpos s + 80)) && s.ok⟩
      (q + 14) (by rw [hp1]; omega)
    have h40 : rpos s + 40 = 8 * q := by omega
    have h56 : rpos s + 56 = 8 * (q + 2) := by omega
    have h80 : rpos s + 80 = 8 * (q + 5) := by omega
    refine ⟨?_, ?_, ?_⟩
    · rw [h1, hp1]
      refine Prod.ext ?_ ?_
      · show fe2At sig (rpos s + 80) :: _ = _
        rw [List.length_cons, List.range_succ_eq_map, List.map_cons, List.map_map]
        refine congrArg₂ List.cons rfl (List.map_congr_left fun k _ => ?_)
        show fe2At sig (rpos s + 112 + 80 + 112 * k) = fe2At sig (rpos s + 80 + 112 * (k + 1))
        rw [show rpos s + 112 + 80 + 112 * k = rpos s + 80 + 112 * (k + 1) by ring]
      · show _ = eqFold2 _ τs (q + 14) _
        rw [polyEvalE, h40, h56, h80]
    · rw [h2, hp1, List.length_cons]; ring
    · rw [h3, hp1, List.length_cons]
      show (okS g sig _ τs.length && (powOKR g (feAt sig (rpos s + 80)) && s.ok)) = _
      rw [okS]
      generalize powOKR g (feAt sig (rpos s + 80)) = a
      generalize okS g sig (rpos s + 112) τs.length = b
      cases a <;> cases b <;> rfl

section
variable {c : Ctx} {M : Mem} {sig : ByteArray} {T : Nat}

theorem hs_eqRound2 (z2 τ : C2) (qm qa : Nat) (claim : C2) :
    Hs c M (eqRound2 z2 τ qm qa claim) (fun rc => rc.1 = ld2 qa ∧
      rc.2.val M = eqStepE ((ld2 qm).val M) ((ld2 (qm + 2)).val M) ((ld2 qa).val M) (τ.val M) (claim.val M)) :=
  hs_bind (hs_g2Add _ _) fun s hs => hs_bind (hs_g2Mul _ _ _) fun c0 hc0 => hs_bind (hs_g2Mul _ _ _) fun t ht =>
    hs_bind (hs_g2Mul _ _ _) fun nc hnc => hs_pure ⟨rfl, by rw [hnc, ht, hc0, hs, eqStepE]⟩

theorem hs_plainRound2 (qm qa : Nat) (claim : C2) :
    Hs c M (plainRound2 qm qa claim) (fun rc => rc.1 = ld2 qa ∧
      rc.2.val M = scStep2 ((ld2 qm).val M) ((ld2 (qm + 2)).val M) ((ld2 qa).val M) (claim.val M)) :=
  hs_bind (hs_g2Add _ _) fun c1 hc1 => hs_bind (hs_g2Mul _ _ _) fun t ht =>
    hs_bind (hs_g2Mul _ _ _) fun nc hnc => hs_pure ⟨rfl, by rw [hnc, ht, hc1, scStep2]; ring⟩

/-- **The circuit's equality-mode rounds** on lanes `q + 14k`, `q + 14k + 5`: the challenges and the final claim
`eqFold2` of the stream's values. -/
theorem hs_eqRuns2 (hS : Streamed M sig T) (z2 : C2) (L : Nat → Nat) : ∀ (τs : List C2) (i0 q : Nat) (claim : C2),
    (∀ k < τs.length, L (i0 + 3 * k) = q + 14 * k ∧ L (i0 + 3 * k + 2) = q + 14 * k + 5) →
    q + 14 * τs.length < T →
    Hs c M (eqRuns2 z2 L τs i0 claim) (fun res =>
      res.1.map (C2.val M) = (List.range τs.length).map (fun k => fe2At sig (8 * (q + 14 * k + 5))) ∧
      res.2.val M = eqFold2 (fun k => fe2At sig (8 * k)) (τs.map (C2.val M)) q (claim.val M))
  | [], _, _, claim, _, _ => hs_pure ⟨rfl, rfl⟩
  | τ :: τs, i0, q, claim, hL, hT => by
    obtain ⟨l0, l2⟩ := hL 0 (by simp)
    simp only [Nat.mul_zero, Nat.add_zero] at l0 l2
    rw [eqRuns2, l0, l2]
    refine hs_bind (hs_eqRound2 z2 τ q (q + 5) claim) fun rc ⟨r1, r2⟩ => ?_
    refine hs_bind (hs_eqRuns2 hS z2 L τs (i0 + 3) (q + 14) rc.2 (fun k hk => ?_) ?_) fun res ⟨e1, e2⟩ =>
      hs_pure ⟨?_, ?_⟩
    · obtain ⟨a, b⟩ := hL (k + 1) (by simp; omega)
      exact ⟨by rw [show i0 + 3 + 3 * k = i0 + 3 * (k + 1) by ring, a]; ring,
        by rw [show i0 + 3 + 3 * k + 2 = i0 + 3 * (k + 1) + 2 by ring, b]; ring⟩
    · simp only [List.length_cons] at hT ⊢; omega
    · simp only [List.length_cons] at hT
      rw [List.map_cons, e1, r1, ld2_val hS (q := q + 5) (by omega), List.length_cons, List.range_succ_eq_map,
        List.map_cons, List.map_map]
      exact congrArg₂ List.cons (congrArg (fe2At sig) (by ring))
        (List.map_congr_left fun k _ => congrArg (fe2At sig) (by simp only [Nat.succ_eq_add_one]; omega))
    · simp only [List.length_cons] at hT
      rw [e2, r2, ld2_val hS (q := q) (by omega), ld2_val hS (q := q + 2) (by omega),
        ld2_val hS (q := q + 5) (by omega), List.map_cons, eqFold2]

/-- **The circuit's plain rounds** on lanes `q + 14k`, `q + 14k + 5`: the challenges and `scFold2` of the stream's
values. -/
theorem hs_plainRuns2 (hS : Streamed M sig T) (L : Nat → Nat) : ∀ (R i0 q : Nat) (claim : C2),
    (∀ k < R, L (i0 + 3 * k) = q + 14 * k ∧ L (i0 + 3 * k + 2) = q + 14 * k + 5) → q + 14 * R < T →
    Hs c M (plainRuns2 L R i0 claim) (fun res =>
      res.1.map (C2.val M) = (List.range R).map (fun k => fe2At sig (8 * (q + 14 * k + 5))) ∧
      res.2.val M = scFold2 (fun k => fe2At sig (8 * k)) R q (claim.val M))
  | 0, _, _, claim, _, _ => hs_pure ⟨rfl, rfl⟩
  | R + 1, i0, q, claim, hL, hT => by
    obtain ⟨l0, l2⟩ := hL 0 (by omega)
    simp only [Nat.mul_zero, Nat.add_zero] at l0 l2
    rw [plainRuns2, l0, l2]
    refine hs_bind (hs_plainRound2 q (q + 5) claim) fun rc ⟨r1, r2⟩ => ?_
    refine hs_bind (hs_plainRuns2 hS L R (i0 + 3) (q + Q2.roundLanes2) rc.2 (fun k hk => ?_) ?_) fun res ⟨e1, e2⟩ =>
      hs_pure ⟨?_, ?_⟩
    · obtain ⟨a, b⟩ := hL (k + 1) (by omega)
      simp only [Q2.roundLanes2]
      exact ⟨by rw [show i0 + 3 + 3 * k = i0 + 3 * (k + 1) by ring, a]; ring,
        by rw [show i0 + 3 + 3 * k + 2 = i0 + 3 * (k + 1) + 2 by ring, b]; ring⟩
    · simp only [Q2.roundLanes2] at hT ⊢; omega
    · rw [List.map_cons, e1, r1, ld2_val hS (q := q + 5) (by omega), List.range_succ_eq_map, List.map_cons,
        List.map_map]
      exact congrArg₂ List.cons (congrArg (fe2At sig) (by ring))
        (List.map_congr_left fun k _ => congrArg (fe2At sig) (by simp only [Q2.roundLanes2, Nat.succ_eq_add_one]; omega))
    · rw [e2, r2, ld2_val hS (q := q) (by omega), ld2_val hS (q := q + 2) (by omega),
        ld2_val hS (q := q + 5) (by omega), scFold2]

/-- **An `E2` equality with gate `1`** (`assertEq2`). -/
theorem hsA_assertEq2 (a b : C2) {g : Cell} (hg : g.val M = 1) :
    HsA c M (assertEq2 a b g) (fun _ => a.val M = b.val M) := by
  intro p hh ha
  simp only [assertEq2] at hh ha
  rw [hold_bind] at hh
  rw [assert_bind] at ha
  have h1 := ((QB.aspec_assertEq (c := c) (M := M) a.re b.re g) p hh.1).2.mp ha.1
  have h2 := ((QB.aspec_assertEq (c := c) (M := M) a.im b.im g) _ hh.2).2.mp ha.2
  rw [(QB.gate_eq_iff hg _ _)] at h1 h2
  show (⟨(a.re.val M).c₀, (a.im.val M).c₀⟩ : FE2) = ⟨(b.re.val M).c₀, (b.im.val M).c₀⟩
  rw [h1, h2]

/-- `E2` scalars `j < n` from lane `q` are the stream's. -/
theorem ld2s_vals (hS : Streamed M sig T) {q n : Nat} (hq : q + 2 * n < T) :
    (ld2s q n).map (C2.val M) = (List.range n).map fun j => fe2At sig (8 * q + 16 * j) := by
  simp only [ld2s, List.map_map]
  refine List.map_congr_left fun j hj => ?_
  rw [List.mem_range] at hj
  simp only [Function.comp_apply]
  rw [ld2_val hS (by omega)]
  congr 1; ring

theorem ld2s_getD (q n : Nat) (z : C2) (j : Nat) (hj : j < n) : (ld2s q n).getD j z = ld2 (q + 2 * j) := by
  simp [ld2s, List.getD_eq_getElem?_getD, hj]

theorem kc2_ld2 (q : Nat) : KC2 (ld2 q) := ⟨rfl, rfl⟩

theorem hs_plainRuns2_fst (L : Nat → Nat) : ∀ (R i0 : Nat) (claim : C2),
    Hs c M (plainRuns2 L R i0 claim) (fun res => res.1 = (List.range R).map fun k => ld2 (L (i0 + 3 * k + 2)))
  | 0, _, _ => hs_pure rfl
  | R + 1, i0, claim => by
    rw [plainRuns2]
    refine hs_bind (hs_plainRound2 _ _ claim) fun rc ⟨r1, _⟩ =>
      hs_bind (hs_plainRuns2_fst L R (i0 + 3) rc.2) fun res e1 => hs_pure ?_
    rw [e1, r1, List.range_succ_eq_map, List.map_cons, List.map_map]
    exact congrArg₂ List.cons rfl (List.map_congr_left fun k _ => by
      simp only [Function.comp_apply, Nat.succ_eq_add_one]; congr 2; ring)

theorem kc2_range (L : Nat → Nat) (R i0 : Nat) : ∀ x ∈ (List.range R).map (fun k => ld2 (L (i0 + 3 * k + 2))), KC2 x := by
  intro x hx
  obtain ⟨k, -, rfl⟩ := List.mem_map.mp hx
  exact kc2_ld2 _


end

/-! ## V's runs -/

theorem requireT_run (b : Bool) (sig : ByteArray) (s : RS) : require b sig s = ((), { s with ok := b && s.ok }) := rfl

theorem sepE2_run (sig : ByteArray) (s : RS) : sepE2 sig s = ((), ⟨s.ent + 72 + s.msg, 0, s.ok⟩) := rfl

theorem zeroFinalD_eq (ω : FE2) (f : Nat → FE2) :
    Lvm.E2T.zeroFinalD ω ((List.range 9).map f) =
      (Lvm.Typed.mulY3 f (fun j => f (3 + j)) 0 + f 6) + ω * (Lvm.Typed.mulY3 f (fun j => f (3 + j)) 1 + f 7) +
        ω ^ 2 * (Lvm.Typed.mulY3 f (fun j => f (3 + j)) 2 + f 8) := by
  have hg : ∀ j < 9, ((List.range 9).map f).getD j 0 = f j := fun j hj => by
    simp [List.getD_eq_getElem?_getD, hj]
  simp only [Lvm.E2T.zeroFinalD, show List.range 3 = [0, 1, 2] from rfl, List.map_cons, List.map_nil,
    List.sum_cons, List.sum_nil, Lvm.Typed.mulY3, Nat.reduceAdd]
  rw [hg 0 (by omega), hg 1 (by omega), hg 2 (by omega), hg 3 (by omega), hg 4 (by omega), hg 5 (by omega),
    hg 6 (by omega), hg 7 (by omega), hg 8 (by omega)]
  ring

section
variable {c : Ctx} {M : Mem} {sig : ByteArray} {T : Nat}

/-! ## The zerocheck (`zeroGT` replays `dZeroT`) -/

set_option maxHeartbeats 800000 in
/-- **The zerocheck at `E2` replayed**: where `zeroGT`'s rows hold and assert (gate on), `dZeroT` from the cursor `P`
keeps `ok` and ends at `P + 4136`; `r_x` and the nine values are the gadget's cells' (the PoW checks of `τ`, `ω` and
the rounds given). -/
theorem zeroGT_run (hS : Streamed M sig T) {z2 : C2} (hz2 : z2.val M = 0) {g : Cell} (hg : g.val M = 1)
    {L : Nat → Nat} {P qz : Nat} (hτ : ∀ i < tX, 8 * L (iTau i) = P + 120 + 80 * i) (hω : 8 * L iOm = P + 1720)
    (hqz : 8 * qz = P + 1792)
    (hR : ∀ k < tX, L (iZR 0 + 3 * k) = qz + 14 * k ∧ L (iZR 0 + 3 * k + 2) = qz + 14 * k + 5)
    (hV : 8 * L iZV = P + 4032) (hT : P + 4200 ≤ 8 * T)
    (hpτ : okG Lvm.E2T.gTau sig (P + 72) tX = true) (hpω : powOKR Lvm.E2T.gOmega (feAt sig (P + 1720)) = true)
    (hpR : okS Lvm.E2T.gZero sig (P + 1752) tX = true) :
    HsA c M (zeroGT z2 g L) (fun out => ∀ s : RS, rpos s = P → s.ok = true →
      (Lvm.E2T.dZeroT sig s).1 = (out.1.map (C2.val M), out.2.map (C2.val M)) ∧
      (Lvm.E2T.dZeroT sig s).2.ok = true ∧ rpos (Lvm.E2T.dZeroT sig s).2 = P + 4136 ∧
      out.1.length = tX ∧ out.2 = ld2s (L iZV) 9) := by
  have hτv : ((List.range tX).map fun i => ld2 (L (iTau i))).map (C2.val M) =
      (List.range 20).map fun i => fe2At sig (P + 72 + 48 + 80 * i) := by
    rw [List.map_map]
    refine List.map_congr_left fun i hi => ?_
    have hi' : i < 20 := List.mem_range.mp hi
    have := hτ i hi'
    rw [Function.comp_apply, ld2_val hS (q := L (iTau i)) (by omega), this]
  have g9 : ∀ j < 9, (ld2s (L iZV) 9).getD j z2 = ld2 (L iZV + 2 * j) := fun j hj => ld2s_getD _ _ _ _ hj
  unfold zeroGT
  dsimp only
  refine hsA_bind (hsA_of_hs (hs_eqRuns2 hS z2 L _ (iZR 0) qz z2 (by simpa using hR)
    (by simp only [List.length_map, List.length_range, tX]; omega))) fun rf ⟨e1, e2⟩ => ?_
  refine hsA_bind (hsA_of_hs (hs_g2Mul _ _ _)) fun u0 hu0 => ?_
  refine hsA_bind (hsA_of_hs (hs_g2Mul _ _ _)) fun u hu => ?_
  refine hsA_bind (hsA_of_hs (hs_g2Mul _ _ _)) fun w hw => ?_
  refine hsA_bind (hsA_of_hs (hs_g2Add _ _)) fun s0 hs0 => ?_
  refine hsA_bind (hsA_of_hs (hs_g2Mul _ _ _)) fun r0 hr0 => ?_
  refine hsA_bind (hsA_of_hs (hs_g2Add _ _)) fun s1 hs1 => ?_
  refine hsA_bind (hsA_of_hs (hs_g2Add _ _)) fun s1' hs1' => ?_
  refine hsA_bind (hsA_of_hs (hs_g2Mul _ _ _)) fun s1'' hs1'' => ?_
  refine hsA_bind (hsA_of_hs (hs_g2Mul _ _ _)) fun r1 hr1 => ?_
  refine hsA_bind (hsA_of_hs (hs_g2Add _ _)) fun s2 hs2 => ?_
  refine hsA_bind (hsA_of_hs (hs_g2Mul _ _ _)) fun s2' hs2' => ?_
  refine hsA_bind (hsA_of_hs (hs_g2Mul _ _ _)) fun s2'' hs2'' => ?_
  refine hsA_bind (hsA_of_hs (hs_g2Mul _ _ _)) fun r2 hr2 => ?_
  refine hsA_bind (hsA_of_hs (hs_g2Mul _ _ _)) fun t1 ht1 => ?_
  refine hsA_bind (hsA_of_hs (hs_g2Mul _ _ _)) fun t ht => ?_
  refine hsA_bind (hsA_assertEq2 _ _ hg) fun _ hA => hsA_pure ?_
  intro s hs hok
  -- the circuit's check is `zeroFinalD`
  have hval : t.val M = Lvm.E2T.zeroFinalD ((ld2 (L iOm)).val M) ((ld2s (L iZV) 9).map (C2.val M)) := by
    have e : (ld2s (L iZV) 9).map (C2.val M) = (List.range 9).map fun j => (ld2 (L iZV + 2 * j)).val M := by
      simp only [ld2s, List.map_map, Function.comp_def]
    rw [e, zeroFinalD_eq, ht, ht1, hr2, hs2'', hs2', hs2, hr1, hs1'', hs1', hs1, hr0, hs0, hw, hu, hu0,
      g9 0 (by norm_num), g9 1 (by norm_num), g9 2 (by norm_num), g9 3 (by norm_num), g9 4 (by norm_num),
      g9 5 (by norm_num), g9 6 (by norm_num), g9 7 (by norm_num), g9 8 (by norm_num), hz2]
    simp only [Lvm.Typed.mulY3, Nat.reduceAdd, Nat.reduceMul]
    ring
  have hvl : (List.range 9).map (fun i => fe2At sig (P + 3992 + 40 + 16 * i)) =
      (ld2s (L iZV) 9).map (C2.val M) := by
    rw [ld2s_vals hS (by omega), hV]
  have hom : (ld2 (L iOm)).val M = fe2At sig (P + 1720) := by rw [ld2_val hS (q := L iOm) (by omega), hω]
  -- V's run
  unfold Lvm.E2T.dZeroT
  rw [dbind_run, sepE2_run, dbind_run]
  obtain ⟨X1, hX1⟩ : ∃ X, samplesG Lvm.E2T.gTau Lvm.Typed.xVars sig ⟨s.ent + 72 + s.msg, 0, s.ok⟩ = X := ⟨_, rfl⟩
  obtain ⟨a1, a2, a3⟩ := Lvm.Q2.samplesG_run Lvm.E2T.gTau sig Lvm.Typed.xVars ⟨s.ent + 72 + s.msg, 0, s.ok⟩
  rw [hX1] at a1 a2 a3
  rw [hX1, dbind_run, Lvm.Q2.sampleG_run, dbind_run]
  have hp1 : rpos (⟨s.ent + 72 + s.msg, 0, s.ok⟩ : RS) = P + 72 := by simp only [rpos] at hs ⊢; omega
  rw [hp1, show Lvm.Typed.xVars = 20 from rfl] at a1 a2 a3
  simp only [rpos] at a2
  have hom' : X1.2.ent + 40 + (X1.2.msg + 8) = P + 1720 := by omega
  rw [hom']
  obtain ⟨X2, hX2⟩ : ∃ X, sumcheckD Lvm.E2T.gZero 0 3 (X1.1.map some) sig
      ⟨X1.2.ent + 72 + (X1.2.msg + 8), 0, powOKR Lvm.E2T.gOmega (feAt sig (P + 1720)) && X1.2.ok⟩ = X := ⟨_, rfl⟩
  have hp3 : rpos (⟨X1.2.ent + 72 + (X1.2.msg + 8), 0,
      powOKR Lvm.E2T.gOmega (feAt sig (P + 1720)) && X1.2.ok⟩ : RS) = P + 1752 := by simp only [rpos]; omega
  obtain ⟨b1, b2, b3⟩ := sumcheckDE_run Lvm.E2T.gZero sig X1.1 0
    ⟨X1.2.ent + 72 + (X1.2.msg + 8), 0, powOKR Lvm.E2T.gOmega (feAt sig (P + 1720)) && X1.2.ok⟩ qz
    (by rw [hp3]; omega)
  rw [hX2, hp3] at b1 b2 b3
  have hl1 : X1.1.length = 20 := by rw [a1, List.length_map, List.length_range]
  rw [hl1] at b1 b2 b3
  rw [hX2, dbind_run, Lvm.Q2.readE2s_run, dbind_run, requireT_run, dpure_run]
  have hp2 : rpos X2.2 = P + 3992 := by rw [b2]
  rw [hp2, hvl]
  -- the challenges and the final claim
  have hx : X1.1 = ((List.range tX).map fun i => ld2 (L (iTau i))).map (C2.val M) := by rw [a1, hτv]
  have hrx : X2.1.1 = rf.1.map (C2.val M) := by
    rw [b1, e1]
    exact List.map_congr_left fun k _ => congrArg _ (by omega)
  have hfin : X2.1.2 = Lvm.E2T.zeroFinalD (fe2At sig (P + 1720)) ((ld2s (L iZV) 9).map (C2.val M)) := by
    rw [b1, ← hom, ← hval, ← hA, e2, hz2, hx]
  refine ⟨?_, ?_, ?_, by simpa using congrArg List.length e1, rfl⟩
  · rw [hrx]
  · show ((X2.1.2 == Lvm.E2T.zeroFinalD _ _) && X2.2.ok) = true
    dsimp only
    rw [b3, a3, hfin, Lvm.Q2.e2OfFE_feAt, beq_self_eq_true, hpR, hpω, hpτ, hok]
    rfl
  · simp only [rpos] at hp2 ⊢
    omega

end

/-! ## The wiring, the relayout, A23 (statements; GT-C3 10c WIP) -/

section
variable {c : Ctx} {M : Mem} {sig : ByteArray} {T : Nat}

/-- **The wiring at `E2` replayed** (from the cursor `P` after the zerocheck): `dWiringT` on the nine values keeps
`ok`, ends at `P + 2688`; `r_y`, the twelve and the four values are the gadget's cells' (`virtGT = virtD` on the
child's `PUB` at S2GT). -/
theorem wireGT_run (vk cL : Vector UInt8 32) (hS : Streamed M sig T) {z2 o2 : C2} (hz2 : z2.val M = 0)
    (ho2 : o2.val M = 1) (hz2K : KC2 z2) (ho2K : KC2 o2) {g : Cell} (hg : g.val M = 1) {Td : TData}
    {N : Lvm.E2T.TNatT} (htd : TdOk Td N.toN) {pb : Nat} (hvk : ∀ i < 4, M.k (pb + 1 + i) = (digestLanes vk).getD i 0)
    {L : Nat → Nat} {P qw : Nat} (hγ : 8 * L iGam = P + 48) (hqw : 8 * qw = P + 120)
    (hR : ∀ k < tY, L (iWR 0 + 3 * k) = qw + 14 * k ∧ L (iWR 0 + 3 * k + 2) = qw + 14 * k + 5)
    (hV : 8 * L iWV = P + 2472) (hV4 : 8 * L (iWV + 1) = P + 2664) (hT : P + 2736 ≤ 8 * T)
    (hH : 11 + pubLanesTC P20T ≤ T)
    (hpγ : powOKR Lvm.E2T.gGamma (feAt sig (P + 48)) = true) (hpR : okS Lvm.E2T.gWire sig (P + 80) tY = true)
    (v : List C2) (hv : v.length = 9) :
    HsA c M (wireGT z2 o2 g Td pb (pubLanesTC P20T) L v) (fun out => ∀ s : RS, rpos s = P → s.ok = true →
      (Lvm.E2T.dWiringT N (Lvm.E2T.pubG vk cL sig) (v.map (C2.val M)) sig s).1 =
          (out.1.map (C2.val M), out.2.1.map (C2.val M), out.2.2.map (C2.val M)) ∧
        (Lvm.E2T.dWiringT N (Lvm.E2T.pubG vk cL sig) (v.map (C2.val M)) sig s).2.ok = true ∧
        rpos (Lvm.E2T.dWiringT N (Lvm.E2T.pubG vk cL sig) (v.map (C2.val M)) sig s).2 = P + 2688 ∧
        out.1.length = tY ∧ (∀ x ∈ out.1, KC2 x) ∧ out.2.1 = ld2s (L iWV) 12 ∧ out.2.2 = ld2s (L (iWV + 1)) 4) := by
  have hv9 : v.take 9 = v := List.take_of_length_le (by omega)
  have hγv : (ld2 (L iGam)).val M = fe2At sig (P + 48) := by rw [ld2_val hS (q := L iGam) (by omega), hγ]
  unfold wireGT
  dsimp only
  rw [hv9]
  refine hsA_bind (hsA_of_hs (hs_powSum2 hz2 _ _)) fun c0 hc0 => ?_
  refine hsA_bind (hsA_of_hs (Lvm.QShape.hs_and (hs_plainRuns2 hS L tY (iWR 0) qw c0 hR (by show qw + 14 * 21 < T; omega))
    (hs_plainRuns2_fst L tY (iWR 0) c0))) fun rf ⟨⟨e1, e2⟩, e3⟩ => ?_
  refine hsA_bind (hsA_of_hs (hs_mapB _ (fun j => ((ld2s (L iWV) 12).getD (2 + 4 * j) z2).val M +
    ((ld2s (L iWV) 12).getD (3 + 4 * j) z2).val M) (fun j => hs_g2Add _ _) _)) fun d6 hd6 => ?_
  refine hsA_bind (hsA_of_hs (hs_powSum2 hz2 _ _)) fun m hm => ?_
  have hrl : rf.1.length = tY := by rw [e3]; simp
  refine hsA_bind (hsA_of_hs (hs_virtGT (c := c) vk cL hS hz2 ho2 hz2K ho2K htd (pb := pb) (n := pubLanesTC P20T)
    rfl hvk hH rf.1 (by rw [hrl]; decide))) fun ve hve => ?_
  refine hsA_bind (hsA_of_hs (hs_g2Sum ve _)) fun sm hsm => ?_
  refine hsA_bind (hsA_of_hs (hs_g2Mul m sm z2)) fun pr hpr => ?_
  refine hsA_bind (hsA_assertEq2 _ _ hg) fun _ hA => hsA_pure ?_
  intro s hs hok
  -- the stream's values
  have hvs : (ld2s (L iWV) 12).map (C2.val M) = (List.range 12).map fun i => fe2At sig (P + 2432 + 40 + 16 * i) := by
    rw [ld2s_vals hS (by omega), hV]
  have hrv : (ld2s (L (iWV + 1)) 4).map (C2.val M) = (List.range 4).map fun i => fe2At sig (P + 2624 + 40 + 16 * i) := by
    rw [ld2s_vals hS (by omega), hV4]
  have hgd : ∀ j < 12, ((ld2s (L iWV) 12).getD j z2).val M = fe2At sig (P + 2432 + 40 + 16 * j) := fun j hj => by
    rw [← getD_val2 hz2, hvs, List.getD_eq_getElem _ _ (by simpa using hj), List.getElem_map, List.getElem_range]
  -- the circuit's final claim
  have hm' : m.val M = Lvm.E2T.wGD (fe2At sig (P + 48)) ((List.range 12).map fun i => fe2At sig (P + 2432 + 40 + 16 * i)) := by
    have hds : (((List.range 3).map fun j => (ld2s (L iWV) 12).getD (4 * j) z2) ++
        (List.range 3).map (fun j => (ld2s (L iWV) 12).getD (1 + 4 * j) z2) ++ d6).map (C2.val M) =
        [fe2At sig (P + 2472), fe2At sig (P + 2536), fe2At sig (P + 2600), fe2At sig (P + 2488), fe2At sig (P + 2552),
          fe2At sig (P + 2616), fe2At sig (P + 2504) + fe2At sig (P + 2520),
          fe2At sig (P + 2568) + fe2At sig (P + 2584), fe2At sig (P + 2632) + fe2At sig (P + 2648)] := by
      rw [List.map_append, List.map_append, hd6]
      simp only [show List.range 3 = [0, 1, 2] from rfl, List.map_cons, List.map_nil, List.cons_append,
        List.nil_append]
      rw [hgd 0 (by omega), hgd 4 (by omega), hgd 8 (by omega), hgd 1 (by omega), hgd 5 (by omega),
        hgd 9 (by omega), hgd 2 (by omega), hgd 3 (by omega), hgd 6 (by omega), hgd 7 (by omega),
        hgd 10 (by omega), hgd 11 (by omega)]
    have hdl : (((List.range 3).map fun j => (ld2s (L iWV) 12).getD (4 * j) z2) ++
        (List.range 3).map (fun j => (ld2s (L iWV) 12).getD (1 + 4 * j) z2) ++ d6).length = 9 := by
      rw [← List.length_map (f := C2.val M), hds]; rfl
    rw [hm, hdl, hds, hγv]
    simp only [Nat.reduceMul, Nat.reduceAdd, Lvm.E2T.wGD, show List.range 3 = [0, 1, 2] from rfl, show List.range 9 = [0, 1, 2, 3, 4, 5, 6, 7, 8] from rfl,
      show List.range 12 = [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11] from rfl, List.map_cons, List.map_nil, List.sum_cons,
      List.sum_nil, List.getD_cons_succ, List.getD_cons_zero, List.length_cons, List.length_nil]
    ring
  -- V's run
  have hp1 : s.ent + 40 + (s.msg + 8) = P + 48 := by simp only [rpos] at hs; omega
  unfold Lvm.E2T.dWiringT
  rw [dbind_run, Lvm.Q2.sampleG_run, hp1, dbind_run, Lvm.Q2.e2OfFE_feAt]
  have hp2 : rpos (⟨s.ent + 72 + (s.msg + 8), 0, powOKR Lvm.E2T.gGamma (feAt sig (P + 48)) && s.ok⟩ : RS) = P + 80 := by
    simp only [rpos] at hs ⊢; omega
  obtain ⟨X, hX⟩ : ∃ X, sumcheckD Lvm.E2T.gWire (Lvm.E2T.wBatchD (fe2At sig (P + 48)) (v.map (C2.val M))) 3
      (List.replicate Lvm.Typed.yVars none) sig
      ⟨s.ent + 72 + (s.msg + 8), 0, powOKR Lvm.E2T.gGamma (feAt sig (P + 48)) && s.ok⟩ = X := ⟨_, rfl⟩
  obtain ⟨b1, b2, b3⟩ := Lvm.Q2.sumcheckD_run Lvm.E2T.gWire sig Lvm.Typed.yVars
    (Lvm.E2T.wBatchD (fe2At sig (P + 48)) (v.map (C2.val M)))
    ⟨s.ent + 72 + (s.msg + 8), 0, powOKR Lvm.E2T.gGamma (feAt sig (P + 48)) && s.ok⟩ qw (by rw [hp2]; omega)
  rw [hX, hp2] at b1 b2 b3
  rw [hX, dbind_run, Lvm.Q2.readE2s_run, dbind_run, Lvm.Q2.readE2s_run, dbind_run, requireT_run, dpure_run]
  have hpX : rpos X.2 = P + 2432 := by rw [b2]; show P + 80 + 112 * 21 = P + 2432; omega
  have hpX' : rpos { X.2 with msg := X.2.msg + 16 * 12 } = P + 2624 := by simp only [rpos] at hpX ⊢; omega
  rw [hpX, hpX']
  -- the challenges and the final claim
  have hry : X.1.1 = rf.1.map (C2.val M) := by
    rw [b1, e1]
    exact List.map_congr_left fun k _ => congrArg _ (by omega)
  have hc0' : c0.val M = Lvm.E2T.wBatchD (fe2At sig (P + 48)) (v.map (C2.val M)) := by
    rw [hc0, hγv, Lvm.E2T.wBatchD, hv]
  have hfin : X.1.2 = Lvm.E2T.wGD (fe2At sig (P + 48)) ((List.range 12).map fun i => fe2At sig (P + 2432 + 40 + 16 * i)) *
      (E2V.sumF ((List.range 4).map fun i => fe2At sig (P + 2624 + 40 + 16 * i)) +
        Lvm.E2T.virtD N (Lvm.E2T.pubG vk cL sig) (rf.1.map (C2.val M))) := by
    rw [b1]
    dsimp only
    rw [← hc0', ← e2, hA, hpr, hz2, add_zero, hsm, hve, hm', E2V.sumF_eq_sum, ← hrv]
    ring
  refine ⟨?_, ?_, ?_, hrl, by rw [e3]; exact kc2_range _ _ _, rfl, rfl⟩
  · rw [hry, hvs, hrv]
  · show ((X.1.2 == _) && _) = true
    rw [hry, hfin, beq_self_eq_true, Bool.true_and, b3, show Lvm.Typed.yVars = tY from rfl, hpR, hpγ, hok]; rfl
  · simp only [rpos] at hpX ⊢; omega

/-- **The relayout at `E2` replayed** (from the cursor `P` after the wiring): `dRelayT2` keeps `ok`, ends at
`P + 2144`; `r` and `v_R` are the gadget's cells' (`relayKernGT = relayKernD`). -/
theorem relayGT_run (hS : Streamed M sig T) {z2 o2 : C2} (hz2 : z2.val M = 0) (ho2 : o2.val M = 1)
    (hz2K : KC2 z2) (ho2K : KC2 o2) {g : Cell} (hg : g.val M = 1) {Td : TData} {N : Lvm.E2T.TNatT}
    (htd : TdOk Td N.toN) {L : Nat → Nat} {P qr : Nat} (hqr : 8 * qr = P + 40)
    (hR : ∀ k < tR, L (iRR 0 + 3 * k) = qr + 14 * k ∧ L (iRR 0 + 3 * k + 2) = qr + 14 * k + 5)
    (hV : 8 * L iRV = P + 2168) (hT : P + 2200 ≤ 8 * T) (hpR : okS Lvm.E2T.gWire sig P tR = true)
    (ry : List C2) (hry : ry.length = tY) (hryK : ∀ x ∈ ry, KC2 x) (vS : C2) :
    HsA c M (relayGT z2 o2 g Td L ry vS) (fun out => ∀ s : RS, rpos s = P → s.ok = true →
      (Lvm.E2T.dRelayT2 N (ry.map (C2.val M)) (vS.val M) sig s).1 = (out.1.map (C2.val M), out.2.val M) ∧
        (Lvm.E2T.dRelayT2 N (ry.map (C2.val M)) (vS.val M) sig s).2.ok = true ∧
        rpos (Lvm.E2T.dRelayT2 N (ry.map (C2.val M)) (vS.val M) sig s).2 = P + 2144 ∧
        out.1.length = tR ∧ (∀ x ∈ out.1, KC2 x) ∧ out.2 = ld2 (L iRV)) := by
  unfold relayGT
  dsimp only
  refine hsA_bind (hsA_of_hs (Lvm.QShape.hs_and (hs_plainRuns2 hS L tR (iRR 0) qr vS hR (by show qr + 14 * 19 < T; omega))
    (hs_plainRuns2_fst L tR (iRR 0) vS))) fun rf ⟨⟨e1, e2⟩, e3⟩ => ?_
  have hrl : rf.1.length = tR := by rw [e3]; simp
  refine hsA_bind (hsA_of_hs (hs_relayKernGT hz2 ho2 ho2K htd ry rf.1 hrl)) fun k hk => ?_
  refine hsA_bind (hsA_of_hs (hs_g2Mul k _ z2)) fun pr hpr => ?_
  refine hsA_bind (hsA_assertEq2 _ _ hg) fun _ hA => hsA_pure ?_
  intro s hs hok
  have hvR : (ld2 (L iRV)).val M = fe2At sig (P + 2128 + 40) := by rw [ld2_val hS (q := L iRV) (by omega), hV]
  unfold Lvm.E2T.dRelayT2
  obtain ⟨X, hX⟩ : ∃ X, sumcheckD Lvm.E2T.gWire (vS.val M) 3 (List.replicate Lvm.Typed.relayRounds none) sig s = X :=
    ⟨_, rfl⟩
  obtain ⟨b1, b2, b3⟩ := Lvm.Q2.sumcheckD_run Lvm.E2T.gWire sig Lvm.Typed.relayRounds (vS.val M) s qr (by rw [hs]; omega)
  rw [hX, hs] at b1 b2 b3
  rw [dbind_run, hX, dbind_run, Lvm.Q2.readE2_run, dbind_run, requireT_run, dpure_run]
  have hpX : X.2.ent + 40 + X.2.msg = P + 2128 + 40 := by
    rw [show Lvm.Typed.relayRounds = 19 from rfl] at b2; simp only [rpos] at b2; omega
  rw [hpX]
  have hrr : X.1.1 = rf.1.map (C2.val M) := by
    rw [b1, e1]
    exact List.map_congr_left fun k _ => congrArg _ (by omega)
  have hfin : X.1.2 = Lvm.E2T.relayKernD N (ry.map (C2.val M)) (rf.1.map (C2.val M)) * fe2At sig (P + 2128 + 40) := by
    rw [b1]
    dsimp only
    rw [← e2, hA, hpr, hz2, add_zero, hk, hvR]
  refine ⟨?_, ?_, ?_, hrl, by rw [e3]; exact kc2_range _ _ _, rfl⟩
  · rw [hrr, hvR]
  · show ((X.1.2 == _) && _) = true
    rw [hrr, hfin, beq_self_eq_true, Bool.true_and, b3, show Lvm.Typed.relayRounds = tR from rfl, hpR, hok]; rfl
  · simp only [rpos] at hpX ⊢; omega

/-! ### A23's helpers -/

theorem hsA_mapB_all {α β : Type} (f : α → BM β) (Q : α → Prop) (hf : ∀ a, HsA c M (f a) (fun _ => Q a)) :
    ∀ l : List α, HsA c M (mapB f l) (fun _ => ∀ a ∈ l, Q a)
  | [] => hsA_pure fun _ h => absurd h List.not_mem_nil
  | a :: l => hsA_bind (hf a) fun _ ha => hsA_bind (hsA_mapB_all f Q hf l) fun _ hl => hsA_pure fun x hx => by
    rcases List.mem_cons.mp hx with rfl | hx
    · exact ha
    · exact hl x hx

theorem hEvalD_eq (t : FE2) : ∀ hs : List FE2,
    Lvm.E2T.hEvalD hs t = ((List.range hs.length).map fun k => t ^ k * hs.getD k 0).sum
  | [] => rfl
  | c :: hs => by
    rw [show Lvm.E2T.hEvalD (c :: hs) t = c + t * Lvm.E2T.hEvalD hs t from rfl, hEvalD_eq t hs, List.length_cons,
      List.range_succ_eq_map, List.map_cons, List.sum_cons, List.map_map, ← List.sum_map_mul_left]
    simp only [Function.comp_def, List.getD_cons_succ, List.getD_cons_zero, pow_zero, one_mul, pow_succ]
    exact congrArg₂ _ rfl (congrArg List.sum (List.map_congr_left fun k _ => by ring))

theorem range_getD2 (L : List FE2) : (List.range L.length).map (fun k => L.getD k 0) = L := by
  apply List.ext_getElem (by simp)
  intro i h1 h2
  rw [List.getElem_map, List.getElem_range, List.getD_eq_getElem _ _ h2]

theorem zipWith_foldl_sum : ∀ (vs a : List FE2) (c : FE2), vs.length ≤ a.length →
    (List.zipWith (· * ·) a vs).foldl (· + ·) c = c + ∑ k ∈ Finset.range vs.length, a.getD k 0 * vs.getD k 0
  | [], a, c, _ => by simp
  | v :: vs, [], c, h => by simp at h
  | v :: vs, x :: a, c, h => by
    rw [List.zipWith_cons_cons, List.foldl_cons, zipWith_foldl_sum vs a _ (by simpa using h), List.length_cons,
      Finset.sum_range_succ']
    simp only [List.getD_cons_succ, List.getD_cons_zero]
    ring

/-- `yOwnD`'s dot product with the `eq` kernel as `eqDot2`'s sum. -/
theorem dotF_eqKernel (κ vs : List FE2) (h : vs.length ≤ 2 ^ κ.length) :
    E2V.dotF (E2V.eqKernelF κ) vs = ∑ k ∈ Finset.range vs.length, E2V.eqAtF κ k * vs.getD k 0 := by
  unfold E2V.dotF
  rw [zipWith_foldl_sum vs _ 0 (by rw [E2V.eqKernelF_length]; exact h), zero_add]
  refine Finset.sum_congr rfl fun k hk => ?_
  rw [E2V.eqKernelF_getD, if_pos (lt_of_lt_of_le (Finset.mem_range.mp hk) h)]

theorem lineD_range (n : Nat) (a b : Nat → FE2) (t : FE2) :
    Lvm.E2T.lineD ((List.range n).map a) ((List.range n).map b) t =
      (List.range n).map fun j => a j + t * (a j + b j) := by
  unfold Lvm.E2T.lineD
  rw [List.zipWith_map, List.zipWith_self]

theorem map_val_range2 {z2 : C2} (hz : z2.val M = 0) (l : List C2) :
    l.map (C2.val M) = (List.range l.length).map fun j => (l.getD j z2).val M := by
  apply List.ext_getElem (by simp)
  intro i h1 h2
  rw [List.getElem_map, List.getElem_map, List.getElem_range, List.getD_eq_getElem _ _ (by simpa using h1)]

/-- The current proof's accumulator at S2GT: `PUB` lanes `615 + 2j` (`E2`, two lanes a scalar) as `E3` scalars with
`c₂ = 0`. -/
def accCT (M : Mem) (pb : Nat) : Acc :=
  ⟨(List.range Lvm.VEq.accVT).map fun j => Lvm.E2T.fe2ToFE ((ld2 (pb + 615 + 2 * j)).val M),
    Lvm.E2T.fe2ToFE ((ld2 (pb + 615 + 2 * Lvm.VEq.accVT)).val M)⟩

/-- **A23 at `E2` replayed** (from the cursor `P` after the relayout): `dAccT` keeps `ok`, ends at `P + 1152`, and
folds to the current proof's `PUB` accumulator (`accCT`). -/
theorem qaccGT_run (vk cL : Vector UInt8 32) (hS : Streamed M sig T) {z2 o2 : C2} (hz2 : z2.val M = 0)
    (ho2 : o2.val M = 1) (hz2K : KC2 z2) (ho2K : KC2 o2) {pb : Nat} (hg : M.k pb = 1) {L : Nat → Nat} {P : Nat}
    (hκ : ∀ j < 4, 8 * L (iKap j) = P + 48 + 80 * j) (hh : 8 * L iH = P + 360) (ht : 8 * L iT = P + 1104)
    (hz : 8 * L iZ = P + 1176) (hT : P + 1192 ≤ 8 * T) (hH : 11 + pubLanesTC P20T ≤ T)
    (hpκ : okG Lvm.E2T.gKappa sig P 4 = true) (hpt : powOKR Lvm.E2T.gT (feAt sig (P + 1104)) = true)
    (rx ry vs : List C2) (hrx : rx.length = tX) (hry : ry.length = tY) (hvs : vs.length = 12) :
    HsA c M (qaccGT z2 o2 pb L rx ry vs) (fun _ => ∀ s : RS, rpos s = P → s.ok = true →
      (Lvm.E2T.dAccT (Lvm.E2T.pubG vk cL sig) ((rx ++ ry).map (C2.val M)) (vs.map (C2.val M)) sig s).1 =
          accCT M pb ∧
        (Lvm.E2T.dAccT (Lvm.E2T.pubG vk cL sig) ((rx ++ ry).map (C2.val M)) (vs.map (C2.val M)) sig s).2.ok = true ∧
        rpos (Lvm.E2T.dAccT (Lvm.E2T.pubG vk cL sig) ((rx ++ ry).map (C2.val M)) (vs.map (C2.val M)) sig s).2 =
          P + 1152) := by
  have hgv : (kc pb).val M = 1 := Lvm.QAcc.kc_val_one hg
  unfold qaccGT
  dsimp only
  refine hsA_bind (hsA_assertEq2 _ _ hgv) fun _ hA0 => ?_
  refine hsA_bind (hsA_of_hs (hs_g2Sum z2 _)) fun sh hsh => ?_
  refine hsA_bind (hsA_of_hs (hs_eqDot2 hz2 ho2 ((List.range 4).map fun j => ld2 (L (iKap j))) 2 (by simp) vs
    (by simp [hvs]))) fun y hy => ?_
  refine hsA_bind (hsA_assertEq2 _ _ hgv) fun _ hA1 => ?_
  refine hsA_bind (hsA_assertEq2 _ _ hgv) fun _ hAz => ?_
  refine hsA_bind (hsA_of_hs (hs_mapB _ (fun i => (ld2 (L iT)).val M *
      ((((List.range (tVarsT + 1)).map fun j => ld2 (accLaneT j)).getD i z2).val M +
        ((((List.range 4).map fun j => ld2 (L (iKap j))) ++ rx ++ ry).getD i z2).val M) +
      (((List.range (tVarsT + 1)).map fun j => ld2 (accLaneT j)).getD i z2).val M)
    (fun i => hs_bind (hs_g2Add _ _) fun d hd => hs_mono (hs_g2Mul _ _ _) fun r hr => by rw [hr, hd]) _))
    fun pts hpts => ?_
  refine hsA_bind (hsA_of_hs (hs_powSum2 hz2 (ld2 (L iT)) (ld2s (L iH) (tVarsT + 1)) :
    Hs c M (horner2 (ld2 (L iT)) (ld2s (L iH) (tVarsT + 1)).reverse z2) _)) fun hv hhvv => ?_
  refine hsA_bind (hsA_mapB_all _ (fun i => (pts.getD i z2).val M =
      (((List.range (tVarsT + 1)).map fun j => ld2 (pb + 615 + 2 * j)).getD i z2).val M)
    (fun i => hsA_assertEq2 _ _ hgv) _) fun _ hAp => ?_
  refine hsA_mono (hsA_assertEq2 _ _ hgv) fun _ hAh => ?_
  intro s hs hok
  -- the circuit's values
  have hκv : ∀ j < 4, (ld2 (L (iKap j))).val M = fe2At sig (P + 48 + 80 * j) := fun j hj => by
    rw [ld2_val hS (q := L (iKap j)) (by have := hκ j hj; omega), hκ j hj]
  have hkap : ((List.range 4).map fun j => ld2 (L (iKap j))).map (C2.val M) =
      (List.range 4).map fun j => fe2At sig (P + 48 + 80 * j) := by
    rw [List.map_map]; exact List.map_congr_left fun j hj => hκv j (List.mem_range.mp hj)
  have hhl : (ld2s (L iH) (tVarsT + 1)).map (C2.val M) = (List.range (tVarsT + 1)).map fun i => fe2At sig (P + 360 + 16 * i) := by
    rw [ld2s_vals hS (by show L iH + 2 * 46 < T; omega), hh]
  have htv : (ld2 (L iT)).val M = fe2At sig (P + 1104) := by rw [ld2_val hS (q := L iT) (by omega), ht]
  have hzv : fe2At sig (P + 1176) = 0 := by rw [← hz, ← ld2_val hS (q := L iZ) (by omega), hAz, hz2]
  have hain : ∀ j < 46, ((List.range (tVarsT + 1)).map fun j => ld2 (accLaneT j)).getD j z2 = ld2 (626 + 2 * j) :=
    fun j hj => by
      rw [List.getD_eq_getElem _ _ (by rw [List.length_map, List.length_range]; exact hj), List.getElem_map,
        List.getElem_range]; rfl
  have hainv : ∀ j < 46, (ld2 (626 + 2 * j)).val M = fe2At sig (8 * (626 + 2 * j)) := fun j hj =>
    ld2_val hS (by show 626 + 2 * j + 1 < T; have : 11 + 707 ≤ T := hH; omega)
  have hpc : ∀ j < 46, ((List.range (tVarsT + 1)).map fun j => ld2 (pb + 615 + 2 * j)).getD j z2 = ld2 (pb + 615 + 2 * j) :=
    fun j hj => by
      rw [List.getD_eq_getElem _ _ (by rw [List.length_map, List.length_range]; exact hj), List.getElem_map,
        List.getElem_range]
  -- the line and `h(t)`
  have hbc : (((List.range 4).map fun j => ld2 (L (iKap j))) ++ rx ++ ry).length = 45 := by
    simp only [List.length_append, List.length_map, List.length_range, hrx, hry]; rfl
  have hline : (Lvm.E2T.lineD ((Lvm.E2T.pubG vk cL sig).accIn.pt.map Lvm.e2OfFE)
      ((List.range 4).map (fun j => fe2At sig (P + 48 + 80 * j)) ++ (rx ++ ry).map (C2.val M)) (fe2At sig (P + 1104))) =
      (List.range 45).map fun j => (ld2 (pb + 615 + 2 * j)).val M := by
    have hA : (Lvm.E2T.pubG vk cL sig).accIn.pt.map Lvm.e2OfFE = (List.range 45).map fun j => fe2At sig (8 * (626 + 2 * j)) := by
      simp only [Lvm.E2T.pubG, pubOfW, List.map_map]
      exact List.map_congr_left fun j _ => congrArg (fe2At sig) (by simp only [headerAt, offAcc, sigBytes]; omega)
    have hB : (List.range 4).map (fun j => fe2At sig (P + 48 + 80 * j)) ++ (rx ++ ry).map (C2.val M) =
        (List.range 45).map fun j => ((((List.range 4).map fun j => ld2 (L (iKap j))) ++ rx ++ ry).getD j z2).val M := by
      rw [← hbc, ← map_val_range2 hz2]
      simp only [List.map_append, hkap, List.append_assoc]
    rw [hA, hB, lineD_range]
    refine List.map_congr_left fun j hj => ?_
    have hj' : j < 45 := List.mem_range.mp hj
    have e1 := hAp j (List.mem_range.mpr hj')
    rw [← getD_val2 hz2, hpts, List.getD_eq_getElem _ _ (by rw [List.length_map, List.length_range]; exact hj'),
      List.getElem_map, List.getElem_range,
      hain j (by omega), hainv j (by omega), htv, hpc j (by omega)] at e1
    rw [← e1]
    ring
  have hht : Lvm.E2T.hEvalD ((List.range (tVarsT + 1)).map fun i => fe2At sig (P + 360 + 16 * i)) (fe2At sig (P + 1104)) =
      (ld2 (pb + 615 + 2 * tVarsT)).val M := by
    rw [← hhl, hEvalD_eq, List.length_map, ← htv, ← hhvv, hAh, hpc tVarsT (by decide)]
  -- V's run
  unfold Lvm.E2T.dAccT
  obtain ⟨a1, a2, a3⟩ := Lvm.Q2.samplesG_run Lvm.E2T.gKappa sig Lvm.Typed.selBitsT s
  obtain ⟨K, hK⟩ : ∃ K, samplesG Lvm.E2T.gKappa Lvm.Typed.selBitsT sig s = K := ⟨_, rfl⟩
  rw [hK] at a1 a2 a3
  rw [dbind_run, hK, dbind_run, Lvm.Q2.readE2s_run, dbind_run, Lvm.Q2.sampleG_run, dbind_run, Lvm.Q2.readE2_run,
    dbind_run, requireT_run, dbind_run, requireT_run, dbind_run, requireT_run, dpure_run]
  have hK1 : K.1 = (List.range 4).map fun j => fe2At sig (P + 48 + 80 * j) := by rw [a1, hs]
  have hpK : rpos K.2 = P + 320 := by rw [a2, hs]; rfl
  dsimp only
  have hpK' : K.2.ent + K.2.msg = P + 320 := hpK
  have hφ : Lvm.Typed.phiVarsT = 45 := rfl
  have q1 : K.2.ent + 40 + (K.2.msg + 16 * (Lvm.Typed.phiVarsT + 1) + 8) = P + 1104 := by
    rw [hφ]; (clear * - hpK'; omega)
  have q2 : K.2.ent + 72 + (K.2.msg + 16 * (Lvm.Typed.phiVarsT + 1) + 8) + 40 + 0 = P + 1176 := by
    rw [Nat.add_zero, hφ]; (clear * - hpK'; omega)
  have hhV : (List.range (Lvm.Typed.phiVarsT + 1)).map (fun i => fe2At sig (rpos K.2 + 40 + 16 * i)) =
      (List.range (tVarsT + 1)).map fun i => fe2At sig (P + 360 + 16 * i) := by
    rw [hpK]
  -- `h(0) = acc_in.y`, `h(1) = Σ_{o'} eq(κ, o')·vs_{o'}`
  have hy0 : Lvm.E2T.hEvalD ((List.range (tVarsT + 1)).map fun i => fe2At sig (P + 360 + 16 * i)) 0 =
      Lvm.e2OfFE (Lvm.E2T.pubG vk cL sig).accIn.y := by
    have e0 : ((ld2s (L iH) (tVarsT + 1)).getD 0 z2).val M = fe2At sig (P + 360) := by
      rw [ld2s_getD _ _ _ _ (by decide), ld2_val hS (by omega)]
      exact congrArg (fe2At sig) (by omega)
    rw [e0, hain tVarsT (by decide), hainv tVarsT (by decide)] at hA0
    have hyv : Lvm.e2OfFE (Lvm.E2T.pubG vk cL sig).accIn.y = fe2At sig (headerAt (offAcc + 16 * Lvm.VEq.accVT)) := rfl
    simp only [Lvm.E2T.hEvalD, List.range_succ_eq_map, List.map_cons, List.foldr_cons, zero_mul, add_zero, Nat.mul_zero,
      Nat.add_zero]
    rw [hA0, hyv]
    exact congrArg (fe2At sig) (by
      rw [show tVarsT = 45 from rfl, show Lvm.VEq.accVT = 45 from rfl]; simp only [headerAt, offAcc, sigBytes])
  have hy1 : Lvm.E2T.hEvalD ((List.range (tVarsT + 1)).map fun i => fe2At sig (P + 360 + 16 * i)) 1 =
      Lvm.E2T.yOwnD (vs.map (C2.val M)) ((List.range 4).map fun j => fe2At sig (P + 48 + 80 * j)) := by
    rw [← hhl, hEvalD_eq]
    simp only [one_pow, one_mul]
    rw [range_getD2, show ((ld2s (L iH) (tVarsT + 1)).map (C2.val M)).sum = sh.val M by rw [hsh, hz2, zero_add], hA1, hy,
      Lvm.E2T.yOwnD, dotF_eqKernel _ _ (by simp [hvs]), List.length_map, hkap]
  rw [q1, q2, Lvm.Q2.e2OfFE_feAt, hhV, hK1]
  refine ⟨?_, ?_, ?_⟩
  · rw [hline, hht]
    unfold accCT
    rw [List.map_map]
    rfl
  · rw [hzv, hy0, hy1, beq_self_eq_true, beq_self_eq_true, beq_self_eq_true, hpt, a3, hs,
      show Lvm.Typed.selBitsT = 4 from rfl, hpκ, hok]
    rfl
  · show K.2.ent + 72 + (K.2.msg + 16 * (Lvm.Typed.phiVarsT + 1) + 8) + (0 + 16) = P + 1152
    rw [Nat.zero_add, hφ]; (clear * - hpK'; omega)

end

/-! ## The lanes of the phase `bus` at S2GT -/

/-- **The lanes of the phase `bus`** (`busT`'s reads) from its start `P`. -/
structure BusLanesT (L : Nat → Nat) (P : Nat) : Prop where
  tau : ∀ i < tX, 8 * L (iTau i) = P + 120 + 80 * i
  om : 8 * L iOm = P + 1720
  zr : ∀ k < tX, 8 * L (iZR 0 + 3 * k) = P + 1792 + 112 * k ∧ 8 * L (iZR 0 + 3 * k + 2) = P + 1832 + 112 * k
  zv : 8 * L iZV = P + 4032
  gam : 8 * L iGam = P + 4184
  wr : ∀ k < tY, 8 * L (iWR 0 + 3 * k) = P + 4256 + 112 * k ∧ 8 * L (iWR 0 + 3 * k + 2) = P + 4296 + 112 * k
  wv : 8 * L iWV = P + 6608
  wv4 : 8 * L (iWV + 1) = P + 6800
  rr : ∀ k < tR, 8 * L (iRR 0 + 3 * k) = P + 6864 + 112 * k ∧ 8 * L (iRR 0 + 3 * k + 2) = P + 6904 + 112 * k
  rv : 8 * L iRV = P + 8992
  kap : ∀ j < 4, 8 * L (iKap j) = P + 9016 + 80 * j
  h : 8 * L iH = P + 9328
  t : 8 * L iT = P + 10072
  z : 8 * L iZ = P + 10144
  mb : 8 * L iMB - 40 = P + 10120
  al : P % 8 = 0

/-- `BusLanesT`'s checker at `p` (from `typedPosF p`, the lane of the phase's first item). -/
def busLanesB (p : Params) : Bool :=
  let L := busL p
  let P := 8 * L 0 - 40
  (List.range tX).all (fun i => 8 * L (iTau i) == P + 120 + 80 * i) && (8 * L iOm == P + 1720) &&
  (List.range tX).all (fun k => 8 * L (iZR 0 + 3 * k) == P + 1792 + 112 * k &&
    8 * L (iZR 0 + 3 * k + 2) == P + 1832 + 112 * k) && (8 * L iZV == P + 4032) && (8 * L iGam == P + 4184) &&
  (List.range tY).all (fun k => 8 * L (iWR 0 + 3 * k) == P + 4256 + 112 * k &&
    8 * L (iWR 0 + 3 * k + 2) == P + 4296 + 112 * k) && (8 * L iWV == P + 6608) && (8 * L (iWV + 1) == P + 6800) &&
  (List.range tR).all (fun k => 8 * L (iRR 0 + 3 * k) == P + 6864 + 112 * k &&
    8 * L (iRR 0 + 3 * k + 2) == P + 6904 + 112 * k) && (8 * L iRV == P + 8992) &&
  (List.range 4).all (fun j => 8 * L (iKap j) == P + 9016 + 80 * j) && (8 * L iH == P + 9328) &&
  (8 * L iT == P + 10072) && (8 * L iZ == P + 10144) && (8 * L iMB - 40 == P + 10120) && (P % 8 == 0)

theorem busLanes_of {p : Params} (h : busLanesB p = true) : BusLanesT (busL p) (typedPosF p) := by
  have e : typedPosF p = 8 * busL p 0 - 40 := by
    show 8 * laneOf p (phaseItem0 p .bus + 0) - 40 = 8 * (itemLanes p).toArray.getD (phaseItem0 p .bus + 0) 0 - 40
    rw [getD_toArray]
  rw [e]
  simp only [busLanesB, Bool.and_eq_true, beq_iff_eq, List.all_eq_true, List.mem_range] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩, h7⟩, h8⟩, h9⟩, h10⟩, h11⟩, h12⟩, h13⟩, h14⟩, h15⟩, h16⟩ := h
  exact ⟨h1, h2, fun k hk => h3 k hk, h4, h5, fun k hk => h6 k hk, h7, h8, fun k hk => h9 k hk, h10, h11, h12, h13,
    h14, h15, h16⟩

/-! ## The typed phases' proof of work -/

theorem powT_facts {sig : ByteArray} {p : Params} {P : Nat} (hL : BusLanesT (busL p) P)
    (hpow : PowOkV (feAt sig) (typedChalsT p)) :
    okG Lvm.E2T.gTau sig (P + 72) tX = true ∧ powOKR Lvm.E2T.gOmega (feAt sig (P + 1720)) = true ∧
      okS Lvm.E2T.gZero sig (P + 1752) tX = true ∧ powOKR Lvm.E2T.gGamma (feAt sig (P + 4184)) = true ∧
      okS Lvm.E2T.gWire sig (P + 4216) tY = true ∧ okS Lvm.E2T.gWire sig (P + 6824) tR = true ∧
      okG Lvm.E2T.gKappa sig (P + 8968) 4 = true ∧ powOKR Lvm.E2T.gT (feAt sig (P + 10072)) = true := by
  have mem : ∀ a, a ∈ typedChalsT p → powOKR a.2 (feAt sig (8 * a.1)) = true := hpow
  simp only [typedChalsT, List.mem_append, List.mem_map, List.mem_range, List.mem_singleton] at mem
  refine ⟨okG_true _ _ fun i hi => ?_, ?_, okS_true _ _ fun k hk => ?_, ?_, okS_true _ _ fun k hk => ?_,
    okS_true _ _ fun k hk => ?_, okG_true _ _ fun j hj => ?_, ?_⟩
  · have := mem _ (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl ⟨i, hi, rfl⟩)))))))
    rwa [hL.tau i hi, show P + 120 + 80 * i = P + 72 + 48 + 80 * i by omega] at this
  · have := mem _ (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inr rfl)))))))
    rwa [hL.om] at this
  · have := mem _ (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inr ⟨k, hk, rfl⟩))))))
    rwa [show iZR k + 2 = iZR 0 + 3 * k + 2 by simp only [iZR], (hL.zr k hk).2,
      show P + 1832 + 112 * k = P + 1752 + 80 + 112 * k by omega] at this
  · have := mem _ (Or.inl (Or.inl (Or.inl (Or.inl (Or.inr rfl)))))
    rwa [hL.gam] at this
  · have := mem _ (Or.inl (Or.inl (Or.inl (Or.inr ⟨k, hk, rfl⟩))))
    rwa [show iWR k + 2 = iWR 0 + 3 * k + 2 by simp only [iWR], (hL.wr k hk).2,
      show P + 4296 + 112 * k = P + 4216 + 80 + 112 * k by omega] at this
  · have := mem _ (Or.inl (Or.inl (Or.inr ⟨k, hk, rfl⟩)))
    rwa [show iRR k + 2 = iRR 0 + 3 * k + 2 by simp only [iRR], (hL.rr k hk).2,
      show P + 6904 + 112 * k = P + 6824 + 80 + 112 * k by omega] at this
  · have := mem _ (Or.inl (Or.inr ⟨j, hj, rfl⟩))
    rwa [hL.kap j hj, show P + 9016 + 80 * j = P + 8968 + 48 + 80 * j by omega] at this
  · have := mem _ (Or.inr rfl)
    rwa [hL.t] at this

/-! ## The typed phases at S2GT (`typed_phaseT`) -/

theorem mbPT_le (Td : TData) (p : Params) : mbPT p ≤ typedEndT Td p := by
  have h1 : mbPT p ≤ busEndD Td.mbD (mbPT p) := by
    unfold busEndD
    have := le_layersEnd (gkrSteps Td.mbD) 0 (busP1 (mbPT p) + 48)
    simp only [busP1] at this ⊢
    omega
  have h2 : busEndD Td.mbD (mbPT p) ≤ typedEndT Td p := by
    unfold typedEndT tabEnd; omega
  omega

section
variable {c : Ctx} {M : Mem} {sig : ByteArray} {T : Nat}

set_option maxHeartbeats 1000000 in
/-- **S2GT-STMT 10c (`typed_phaseT`)**: the typed phases at S2GT in `PhaseAt` form (`core_of_phasesG`'s `htyped`):
where `typedGT`'s rows hold and assert (gate on) on the lanes of `P20T`'s phase `bus` (from `P`), V_S's `dTypedT`
runs from `P` to `typedEndT`, folds to the current proof's `PUB` accumulator, and its claims and evaluations are the
gadget's cells'. -/
theorem typed_phaseT (vk cL : Vector UInt8 32) (hS : Streamed M sig T) {pb : Nat} (hg : M.k pb = 1)
    (hvk : ∀ i < 4, M.k (pb + 1 + i) = (digestLanes vk).getD i 0) {z o zk ok : Cell} (hzE : z.ty = .E)
    (hoE : o.ty = .E) (hz : z.val M = 0) (ho : o.val M = 1) (hzK : zk.ty = .K) (hoK : ok.ty = .K)
    (hzk : zk.val M = 0) (hok1 : ok.val M = 1) {Td : TData} {N : Lvm.E2T.TNatT} (htd : TdOk Td N.toN)
    (p : Params) (hl : p.leafdecReads = 1) (hsc : Lvm.M3.sumcheckTabs N.mbT = N.mbT)
    (hS' : Td.mbS = N.mbT.map Lvm.M3.Tab.shape) (hR : Td.mbR = p.tableRounds) (hD : Td.mbD = p.busDepth)
    (hfix : FixListed N.mbT Td.mbFix) {P : Nat} (hL : BusLanesT (busL P20T) P)
    (hpow : PowOkV (feAt sig) (typedChalsT P20T)) (hT : typedEndT Td P20T + 40 ≤ 8 * T)
    (hH : 11 + pubLanesTC P20T ≤ T) (q : Ptr) (hq : 1 ≤ q.e)
    (hok : Lvm.QSig.Ok c M (typedGT Td P20T pb (pubLanesTC P20T) z o zk ok) q) :
    PhaseAt (Lvm.E2T.dTypedT p N (N.toN.m3 p) (Lvm.E2T.pubG vk cL sig)) sig P (typedEndT Td P20T)
      (accCT M pb, Lvm.E2T.typedClaimsND N p
        ((typedGT Td P20T pb (pubLanesTC P20T) z o zk ok q).1.ry.map (C2.val M))
        ((typedGT Td P20T pb (pubLanesTC P20T) z o zk ok q).1.rv.map (C2.val M))
        ((typedGT Td P20T pb (pubLanesTC P20T) z o zk ok q).1.rr.map (C2.val M))
        ((typedGT Td P20T pb (pubLanesTC P20T) z o zk ok q).1.vR.val M),
        (typedGT Td P20T pb (pubLanesTC P20T) z o zk ok q).1.tab.map fun e => (vs M e.1, vs M e.2)) := by
  intro s hs hsok
  have hgv : (kc pb).val M = 1 := Lvm.QAcc.kc_val_one hg
  have kz : ∀ x : Cell, x.ty = .K → x.val M = 0 → (x.val M).c₀ = 0 := fun x _ h => by rw [h]; rfl
  have hz2 : (⟨zk, zk⟩ : C2).val M = 0 := by
    show (⟨(zk.val M).c₀, (zk.val M).c₀⟩ : FE2) = 0; rw [hzk]; rfl
  have ho2 : (⟨ok, zk⟩ : C2).val M = 1 := by
    show (⟨(ok.val M).c₀, (zk.val M).c₀⟩ : FE2) = 1; rw [hok1, hzk]; rfl
  have hz2K : KC2 ⟨zk, zk⟩ := ⟨hzK, hzK⟩
  have ho2K : KC2 ⟨ok, zk⟩ := ⟨hoK, hzK⟩
  obtain ⟨pτ, pω, pZ, pγ, pW, pR, pκ, pt⟩ := powT_facts hL hpow
  have hP8 := hL.al
  have hmb : mbPT P20T = P + 10120 := hL.mb
  have hE := mbPT_le Td P20T
  -- the circuit's parts, at their pointers
  have hout : (typedGT Td P20T pb (pubLanesTC P20T) z o zk ok q) = (typedGT Td P20T pb (pubLanesTC P20T) z o zk ok q) :=
    rfl
  clear hout
  unfold typedGT at hok ⊢
  dsimp only at hok ⊢
  simp only [bind_apply, pure_apply] at ⊢
  obtain ⟨hZ, hok⟩ := okb hok
  obtain ⟨zr, hzr⟩ : ∃ x, (zeroGT ⟨zk, zk⟩ (kc pb) (busL P20T) q).1 = x := ⟨_, rfl⟩
  obtain ⟨q1, hq1⟩ : ∃ x, q.adv (zeroGT ⟨zk, zk⟩ (kc pb) (busL P20T) q).2 = x := ⟨_, rfl⟩
  have RZ := zeroGT_run (c := c) hS hz2 hgv (P := P) (qz := (P + 1792) / 8) hL.tau hL.om (by omega)
    (fun k hk => by have := hL.zr k hk; omega) hL.zv (by omega) pτ pω pZ q hZ.1 hZ.2
  rw [hzr] at RZ hok
  rw [hq1] at hok
  simp only [hzr, hq1]
  obtain ⟨hW, hok⟩ := okb hok
  obtain ⟨w, hw⟩ : ∃ x, (wireGT ⟨zk, zk⟩ ⟨ok, zk⟩ (kc pb) Td pb (pubLanesTC P20T) (busL P20T) zr.2 q1).1 = x :=
    ⟨_, rfl⟩
  obtain ⟨q2, hq2⟩ : ∃ x, q1.adv (wireGT ⟨zk, zk⟩ ⟨ok, zk⟩ (kc pb) Td pb (pubLanesTC P20T) (busL P20T) zr.2 q1).2 = x :=
    ⟨_, rfl⟩
  have hs1 : rpos s = P := hs
  obtain ⟨z1, z2', z3, z4, z5⟩ := RZ s hs1 hsok
  have RW := wireGT_run (c := c) vk cL hS hz2 ho2 hz2K ho2K hgv htd hvk (P := P + 4136) (qw := (P + 4256) / 8)
    (by rw [hL.gam]) (by omega) (fun k hk => by have := hL.wr k hk; omega) (by rw [hL.wv]) (by rw [hL.wv4])
    (by omega) hH (by rw [show P + 4136 + 48 = P + 4184 by omega]; exact pγ)
    (by rw [show P + 4136 + 80 = P + 4216 by omega]; exact pW) zr.2 (by rw [z5]; simp [ld2s]) q1 hW.1 hW.2
  rw [hw] at RW hok
  rw [hq2] at hok
  simp only [hw, hq2]
  obtain ⟨hRl, hok⟩ := okb hok
  obtain ⟨r, hr⟩ : ∃ x, (relayGT ⟨zk, zk⟩ ⟨ok, zk⟩ (kc pb) Td (busL P20T) w.1 (w.2.2.getD 1 ⟨zk, zk⟩) q2).1 = x :=
    ⟨_, rfl⟩
  obtain ⟨q3, hq3⟩ : ∃ x, q2.adv (relayGT ⟨zk, zk⟩ ⟨ok, zk⟩ (kc pb) Td (busL P20T) w.1
      (w.2.2.getD 1 ⟨zk, zk⟩) q2).2 = x := ⟨_, rfl⟩
  -- V's run
  unfold Lvm.E2T.dTypedT Lvm.E2T.dTypedTG
  rw [dbind_run]
  obtain ⟨Z, hZr⟩ : ∃ x, Lvm.E2T.dZeroT sig s = x := ⟨_, rfl⟩
  rw [hZr] at z1 z2' z3
  rw [hZr, dbind_run, Prod.fst, z1]
  obtain ⟨W1, W2, W3, W4, W5, W6, W7⟩ := RW Z.2 z3 z2'
  have RR := relayGT_run (c := c) hS hz2 ho2 hz2K ho2K hgv htd (N := N) (P := P + 6824) (qr := (P + 6864) / 8)
    (by omega) (fun k hk => by have := hL.rr k hk; omega) (by rw [hL.rv]) (by omega)
    (by rw [show P + 6824 = P + 6824 by rfl]; exact pR) w.1 W4 W5 (w.2.2.getD 1 ⟨zk, zk⟩) q2 hRl.1 hRl.2
  rw [hr] at RR hok
  rw [hq3] at hok
  simp only [hr, hq3]
  obtain ⟨hA, hok⟩ := okb hok
  obtain ⟨q4, hq4⟩ : ∃ x, q3.adv (qaccGT ⟨zk, zk⟩ ⟨ok, zk⟩ pb (busL P20T) zr.1 w.1 w.2.1 q3).2 = x := ⟨_, rfl⟩
  have RA := qaccGT_run (c := c) vk cL hS hz2 ho2 hz2K ho2K hg (P := P + 8968)
    (fun j hj => by rw [hL.kap j hj]) (by rw [hL.h]) (by rw [hL.t]) (by rw [hL.z]) (by omega) hH pκ
    (by rw [show P + 8968 + 1104 = P + 10072 by omega]; exact pt) zr.1 w.1 w.2.1 z4 W4
    (by rw [W6]; simp [ld2s]) q3 hA.1 hA.2
  rw [hq4] at hok
  simp only [hq4]
  have e1 : q.e ≤ q1.e := hq1 ▸ Lvm.Har.adv_e_le _ _
  have e2 : q1.e ≤ q2.e := hq2 ▸ Lvm.Har.adv_e_le _ _
  have e3 : q2.e ≤ q3.e := hq3 ▸ Lvm.Har.adv_e_le _ _
  have e4 : q3.e ≤ q4.e := hq4 ▸ Lvm.Har.adv_e_le _ _
  -- the wiring's run
  obtain ⟨Wr, hWr⟩ : ∃ x, Lvm.E2T.dWiringT N (Lvm.E2T.pubG vk cL sig) (zr.2.map (C2.val M)) sig Z.2 = x := ⟨_, rfl⟩
  rw [hWr] at W1 W2 W3
  rw [hWr, W1]
  dsimp only
  have egd : (w.2.2.map (C2.val M)).getD 1 0 = (w.2.2.getD 1 ⟨zk, zk⟩).val M := by rw [← hz2, List.getD_map]
  rw [egd, dbind_run]
  -- the relayout's run
  obtain ⟨Rr, hRr⟩ : ∃ x, Lvm.E2T.dRelayT2 N (w.1.map (C2.val M)) ((w.2.2.getD 1 ⟨zk, zk⟩).val M) sig Wr.2 = x :=
    ⟨_, rfl⟩
  obtain ⟨R1, R2, R3, R4, R5, R6⟩ := RR Wr.2 (by omega) W2
  rw [hRr] at R1 R2 R3
  rw [hRr, dbind_run, R1]
  dsimp only
  rw [← List.map_append]
  -- A23's run
  obtain ⟨Ar, hAr⟩ : ∃ x, Lvm.E2T.dAccT (Lvm.E2T.pubG vk cL sig) ((zr.1 ++ w.1).map (C2.val M))
      (w.2.1.map (C2.val M)) sig Rr.2 = x := ⟨_, rfl⟩
  obtain ⟨A1, A2, A3⟩ := RA Rr.2 (by omega) R2
  rw [hAr] at A1 A2 A3
  rw [hAr, dbind_run, A1]
  -- the mini-bus
  obtain ⟨hMi, -⟩ := okb hok
  have RM := miniG_replays (c := c) hS hz ho hzE hoE hgv rfl p hl Td N.mbT hsc hS' hR hD hfix
    (Lvm.E2T.pubG vk cL sig) (P := mbPT P20T) (by omega) (by unfold typedEndT at hT; omega) q4 (by omega) hMi Ar.2
    (by show Ar.2.ent + Ar.2.msg = _; simp only [rpos] at A3; omega) A2
  rw [show N.toN.m3 p = M3.real p (fun _ => N.mbT) from rfl]
  obtain ⟨Mv, hMv⟩ : ∃ x, TypedV.dMiniT p (M3.real p fun _ => N.mbT) N.mbT (Lvm.E2T.pubG vk cL sig) sig Ar.2 = x :=
    ⟨_, rfl⟩
  rw [hMv] at RM
  rw [hMv, dpure_run]
  obtain ⟨M1, M2, M3⟩ := RM
  exact ⟨by rw [M3], M1, M2⟩

end

/-! ## The typed gadget's shape (for the claims, 10d) -/

section
variable {c : Ctx} {M : Mem}

theorem hs_wireGT_fst (z2 o2 : C2) (g : Cell) (Td : TData) (pb n : Nat) (L : Nat → Nat) (v : List C2) :
    Hs c M (wireGT z2 o2 g Td pb n L v) (fun w =>
      w.1 = (List.range tY).map (fun k => ld2 (L (iWR 0 + 3 * k + 2))) ∧ w.2.2 = ld2s (L (iWV + 1)) 4) := by
  unfold wireGT
  dsimp only
  refine hs_bind (hs_true _) fun _ _ => hs_bind (hs_plainRuns2_fst _ _ _ _) fun rf hrf => ?_
  exact hs_bind (hs_true _) fun _ _ => hs_bind (hs_true _) fun _ _ => hs_bind (hs_true _) fun _ _ =>
    hs_bind (hs_true _) fun _ _ => hs_bind (hs_true _) fun _ _ => hs_bind (hs_true _) fun _ _ =>
    hs_pure ⟨hrf, rfl⟩

theorem hs_relayGT_fst (z2 o2 : C2) (g : Cell) (Td : TData) (L : Nat → Nat) (ry : List C2) (vS : C2) :
    Hs c M (relayGT z2 o2 g Td L ry vS) (fun r =>
      r.1 = (List.range tR).map (fun k => ld2 (L (iRR 0 + 3 * k + 2))) ∧ r.2 = ld2 (L iRV)) := by
  unfold relayGT
  dsimp only
  refine hs_bind (hs_plainRuns2_fst _ _ _ _) fun rf hrf => ?_
  exact hs_bind (hs_true _) fun _ _ => hs_bind (hs_true _) fun _ _ => hs_bind (hs_true _) fun _ _ =>
    hs_pure ⟨hrf, rfl⟩

/-- **The typed gadget's shape** (where its rows hold): `r_y` and `r_R` are `K`-celled lists of 21 and 19 answers,
`v_R` and the region values `K`-celled, the table columns of the mini-bus's lengths. -/
theorem typedGT_shape (Td : TData) (p : Params) (pb n : Nat) (z o zk ok : Cell) :
    Hs c M (typedGT Td p pb n z o zk ok) (fun t => (t.ry.length = tY ∧ ∀ x ∈ t.ry, KC2 x) ∧
      (t.rr.length = tR ∧ ∀ x ∈ t.rr, KC2 x) ∧ KC2 t.vR ∧ (∀ x ∈ t.rv, KC2 x) ∧
      ∀ x ∈ Td.mbS.zip t.tab, x.2.1.length = min Td.mbR x.1.τ) := by
  unfold typedGT
  dsimp only
  refine hs_bind_true fun zr => hs_bind (hs_wireGT_fst _ _ _ _ _ _ _ _) fun w ⟨hw1, hw2⟩ => ?_
  refine hs_bind (hs_relayGT_fst _ _ _ _ _ _ _) fun r ⟨hr1, hr2⟩ => hs_bind_true fun _ => ?_
  unfold miniG
  refine hs_bind (P := fun mb : BusC × List (List Cell × List Cell) =>
      ∀ x ∈ Td.mbS.zip mb.2, x.2.1.length = min Td.mbR x.1.τ)
    (hs_bind (hs_true _) fun bus _ => hs_bind (tabG_pts _ _ _ _ _ _ _)
      fun tab ht => hs_bind_true fun _ => hs_pure ht) fun mb hmb => ?_
  refine hs_pure ⟨⟨by rw [hw1]; simp, by rw [hw1]; exact kc2_range _ _ _⟩, ⟨by rw [hr1]; simp,
    by rw [hr1]; exact kc2_range _ _ _⟩, by rw [hr2]; exact kc2_ld2 _, ?_, hmb⟩
  rw [hw2]
  intro x hx
  obtain ⟨j, -, rfl⟩ := List.mem_map.mp hx
  exact kc2_ld2 _

end

set_option maxRecDepth 200000 in
/-- **The lanes of `P20T`'s phase `bus`** (one kernel evaluation of the schedule's lanes). -/
theorem busLanesB_P20T : busLanesB P20T = true := by
  unfold P20T; rw [Lvm.Replay.P20_eq]; decide +kernel

/-- S2GT's mini-bus instance's table claims are the record's (`m3G_tableClaims`). -/
theorem m3G_tableClaimsT (N : Lvm.E2T.TNatT) (p : Params) (pub : Pub) (evs : List (List FE × List FE)) :
    (Lvm.E2T.m3G N p).tableClaims pub evs = Lvm.M3.tableClaimsR (Lvm.M3.sumcheckTabs N.mbT) evs := rfl

end Lvm.E2Q
