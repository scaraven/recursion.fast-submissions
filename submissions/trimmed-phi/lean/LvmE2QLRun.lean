-- New for lvm2 E2F (slice S1, E2F-QH2): V's `E2` reader programs (`LvmDecideE2`) run on a cursor: where they read,
-- what `ok` becomes. The bridge from the gadgets' stream lanes to V's DM phases.
import LvmE2QWKitSem
import LvmDecideE2

/-!
# Running V's `E2` reader

At a cursor `s` (position `P = s.ent + s.msg`):

* `readE2_run`, `readE2s_run`: scalar `i` at byte `P + 40 + 16 i`;
* `sampleG_run`: the nonce at `P + 40`, the answer at `P + 48`; next `P' = P + 80`; `ok` gains `powOKR g`;
* `samplesG_run`: answer `i` at `P + 48 + 80 i`;
* `sumcheckD_run` (count 3, plain): round `k`'s message at `P + 40 + 112 k`, its answer at `P + 80 + 112 k`; the final
  claim is `scFold2` on the stream's `E2` values (`fe2At`).
-/

set_option autoImplicit false

namespace Lvm.Q2

open Lvm DM Lvm.E2V

theorem readE2_run (sig : ByteArray) (s : RS) :
    readE2 sig s = (fe2At sig (s.ent + 40 + s.msg), { s with msg := s.msg + 16 }) := rfl

theorem sampleG_run (g : Nat) (sig : ByteArray) (s : RS) :
    sampleG g sig s = (e2OfFE (feAt sig (s.ent + 40 + (s.msg + 8))),
      ⟨s.ent + 72 + (s.msg + 8), 0, powOKR g (feAt sig (s.ent + 40 + (s.msg + 8))) && s.ok⟩) := rfl

theorem e2OfFE_feAt (sig : ByteArray) (o : Nat) : e2OfFE (feAt sig o) = fe2At sig o := rfl

/-- The cursor's position. -/
def rpos (s : RS) : Nat := s.ent + s.msg

/-- The `powOK`s of `n` ground answers from position `P` (answers at `P + 48 + 80 i`). -/
def okG (g : Nat) (sig : ByteArray) : Nat → Nat → Bool
  | _, 0 => true
  | P, n + 1 => powOKR g (feAt sig (P + 48)) && okG g sig (P + 80) n

/-- `n` ground challenges from `P`: answers at `P + 48 + 80 i`, position `P + 80 n`, `ok` gains their `powOK`s. -/
theorem samplesG_run (g : Nat) (sig : ByteArray) : ∀ (n : Nat) (s : RS),
    (samplesG g n sig s).1 = (List.range n).map (fun i => fe2At sig (rpos s + 48 + 80 * i)) ∧
    rpos (samplesG g n sig s).2 = rpos s + 80 * n ∧
    (samplesG g n sig s).2.ok = (okG g sig (rpos s) n && s.ok)
  | 0, s => ⟨rfl, rfl, by show s.ok = (true && s.ok); rw [Bool.true_and]⟩
  | n + 1, s => by
    obtain ⟨h1, h2, h3⟩ := samplesG_run g sig n (sampleG g sig s).2
    have e : samplesG g (n + 1) sig s =
        ((sampleG g sig s).1 :: (samplesG g n sig (sampleG g sig s).2).1, (samplesG g n sig (sampleG g sig s).2).2) := rfl
    rw [e]
    have hp : rpos (sampleG g sig s).2 = rpos s + 80 := by simp only [sampleG_run, rpos]; (clear * - s g sig n; omega)
    refine ⟨?_, ?_, ?_⟩
    · rw [h1, hp, List.range_succ_eq_map, List.map_cons, List.map_map, sampleG_run, e2OfFE_feAt]
      simp only [rpos]
      refine List.cons_eq_cons.mpr ⟨by congr 1; (clear * - s g sig n; omega), List.map_congr_left fun i _ => ?_⟩
      simp only [Function.comp_apply]; congr 1; (clear * - s i g sig n; omega)
    · rw [h2, hp]; ring
    · rw [h3, hp]
      have hok : (sampleG g sig s).2.ok = (powOKR g (feAt sig (rpos s + 48)) && s.ok) := by
        rw [sampleG_run]; simp only [rpos]; rw [show s.ent + 40 + (s.msg + 8) = s.ent + s.msg + 48 by (clear * - s g sig n; omega)]
      rw [hok, okG]
      generalize powOKR g (feAt sig (rpos s + 48)) = a
      generalize okG g sig (rpos s + 80) n = b
      cases a <;> cases b <;> rfl

/-- The `powOK`s of `R` sumcheck rounds from position `P` (answers at `P + 80 + 112 k`). -/
def okS (g : Nat) (sig : ByteArray) : Nat → Nat → Bool
  | _, 0 => true
  | P, R + 1 => powOKR g (feAt sig (P + 80)) && okS g sig (P + 112) R

theorem dbind_run {α β : Type} (m : DM α) (f : α → DM β) (sig : ByteArray) (s : RS) :
    (m >>= f) sig s = f (m sig s).1 sig (m sig s).2 := rfl

theorem dpure_run {α : Type} (a : α) (sig : ByteArray) (s : RS) : (pure a : DM α) sig s = (a, s) := rfl

theorem roundPolyD3 (claim : FE2) : roundPolyD 3 claim none =
    (readE2 >>= fun c0 => readE2 >>= fun c2 => pure [c0, claim + (0 + c2), c2]) := by
  show (readE2 >>= fun c0 => (readE2 >>= fun x => (pure [] : DM (List FE2)) >>= fun xs => pure (x :: xs)) >>= fun tail =>
    pure (c0 :: (claim + sumF tail) :: tail)) = _
  simp only [bind_assoc, pure_bind, sumF, List.foldl_cons, List.foldl_nil]

theorem roundPolyD_run (claim : FE2) (sig : ByteArray) (s : RS) :
    roundPolyD 3 claim none sig s = ([fe2At sig (rpos s + 40), claim + (0 + fe2At sig (rpos s + 56)),
      fe2At sig (rpos s + 56)], { s with msg := s.msg + 16 + 16 }) := by
  rw [roundPolyD3, dbind_run, readE2_run, dbind_run, readE2_run, dpure_run]
  simp only [rpos]
  rw [show s.ent + 40 + s.msg = s.ent + s.msg + 40 by (clear * - s; omega), show s.ent + 40 + (s.msg + 16) = s.ent + s.msg + 56 by (clear * - s; omega)]

theorem polyEval3 (c0 c2 r claim : FE2) : polyEvalF [c0, claim + (0 + c2), c2] r = scStep2 c0 c2 r claim := by
  unfold polyEvalF scStep2
  simp only [List.foldr_cons, List.foldr_nil]
  ring

/-- **The `E2` sumcheck (count 3, plain) from a cursor** whose first message is at lane `q` (`8 q = P + 40`). -/
theorem sumcheckD_run (g : Nat) (sig : ByteArray) : ∀ (R : Nat) (claim : FE2) (s : RS) (q : Nat),
    8 * q = rpos s + 40 →
    (sumcheckD g claim 3 (List.replicate R none) sig s).1 =
        ((List.range R).map (fun k => fe2At sig (rpos s + 80 + 112 * k)),
          scFold2 (fun k => fe2At sig (8 * k)) R q claim) ∧
      rpos (sumcheckD g claim 3 (List.replicate R none) sig s).2 = rpos s + 112 * R ∧
      (sumcheckD g claim 3 (List.replicate R none) sig s).2.ok = (okS g sig (rpos s) R && s.ok)
  | 0, claim, s, q, _ => ⟨rfl, rfl, by show s.ok = (true && s.ok); rw [Bool.true_and]⟩
  | R + 1, claim, s, q, hq => by
    have e : sumcheckD g claim 3 (List.replicate (R + 1) none) = (roundPolyD 3 claim none >>= fun msg =>
        sampleG g >>= fun c => sumcheckD g (polyEvalF msg c) 3 (List.replicate R none) >>= fun res =>
          pure (c :: res.1, res.2)) := rfl
    rw [e, dbind_run, roundPolyD_run, dbind_run, sampleG_run, dbind_run, dpure_run]
    dsimp only
    have hp1 : ∀ o : Bool, rpos (⟨s.ent + 72 + (s.msg + 16 + 16 + 8), 0, o⟩ : RS) = rpos s + 112 := by
      intro o; simp only [rpos]; (clear * - s q; omega)
    obtain ⟨h1, h2, h3⟩ := sumcheckD_run g sig R
      (polyEvalF [fe2At sig (rpos s + 40), claim + (0 + fe2At sig (rpos s + 56)), fe2At sig (rpos s + 56)]
        (e2OfFE (feAt sig (s.ent + 40 + (s.msg + 16 + 16 + 8)))))
      ⟨s.ent + 72 + (s.msg + 16 + 16 + 8), 0, powOKR g (feAt sig (s.ent + 40 + (s.msg + 16 + 16 + 8))) && s.ok⟩
      (q + roundLanes2) (by rw [hp1]; simp only [roundLanes2]; (clear * - q s hq; omega))
    have hb : s.ent + 40 + (s.msg + 16 + 16 + 8) = rpos s + 80 := by simp only [rpos]; (clear * - s g sig R claim q; omega)
    rw [hb, e2OfFE_feAt] at h1 h2 h3 ⊢
    have h56 : rpos s + 56 = 8 * (q + 2) := by (clear * - s q g sig R claim hq; omega)
    have h80 : rpos s + 80 = 8 * (q + 5) := by (clear * - s q g sig R claim hq; omega)
    refine ⟨?_, ?_, ?_⟩
    · rw [h1, hp1]
      refine Prod.ext ?_ ?_
      · show fe2At sig (rpos s + 80) :: _ = _
        rw [List.range_succ_eq_map, List.map_cons, List.map_map]
        congr 1
        refine List.map_congr_left fun k _ => ?_
        show fe2At sig (rpos s + 112 + 80 + 112 * k) = fe2At sig (rpos s + 80 + 112 * (k + 1))
        rw [show rpos s + 112 + 80 + 112 * k = rpos s + 80 + 112 * (k + 1) by ring]
      · show scFold2 _ R (q + roundLanes2) _ = _
        rw [polyEval3, ← hq, h56, h80]
        rfl
    · rw [h2, hp1]; ring
    · rw [h3]
      show (okS g sig _ R && (powOKR g (feAt sig (rpos s + 80)) && s.ok)) = _
      rw [hp1, okS]
      generalize powOKR g (feAt sig (rpos s + 80)) = a
      generalize okS g sig (rpos s + 112) R = b
      cases a <;> cases b <;> rfl

/-- `n` `E2` scalars from a cursor: scalar `i` at `P + 40 + 16 i`. -/
theorem readE2s_run (sig : ByteArray) : ∀ (n : Nat) (s : RS),
    readE2s n sig s = ((List.range n).map (fun i => fe2At sig (rpos s + 40 + 16 * i)), { s with msg := s.msg + 16 * n })
  | 0, s => rfl
  | n + 1, s => by
    have e : readE2s (n + 1) = (readE2 >>= fun x => readE2s n >>= fun xs => pure (x :: xs)) := rfl
    rw [e, dbind_run, readE2_run, dbind_run, readE2s_run sig n, dpure_run]
    simp only [rpos]
    refine Prod.ext ?_ ?_
    · show fe2At sig _ :: _ = _
      rw [List.range_succ_eq_map, List.map_cons, List.map_map]
      congr 1
      · congr 1; (clear * - s; omega)
      · refine List.map_congr_left fun k _ => ?_
        show fe2At sig (s.ent + (s.msg + 16) + 40 + 16 * k) = fe2At sig (s.ent + s.msg + 40 + 16 * (k + 1))
        congr 1; ring
    · show RS.mk _ _ _ = RS.mk _ _ _
      congr 1; ring

/-- `scFold2` reads only the lanes `q + 14 j + {0, 2, 5}`, `j < R`. -/
theorem scFold2_congr (v w : Nat → FE2) : ∀ (R q : Nat) (claim : FE2),
    (∀ j < R, v (q + 14 * j) = w (q + 14 * j) ∧ v (q + 14 * j + 2) = w (q + 14 * j + 2) ∧
      v (q + 14 * j + 5) = w (q + 14 * j + 5)) → scFold2 v R q claim = scFold2 w R q claim
  | 0, _, _, _ => rfl
  | R + 1, q, claim, h => by
    obtain ⟨h0, h2, h5⟩ := h 0 (by (clear * - R; omega))
    simp only [Nat.mul_zero, Nat.add_zero] at h0 h2 h5
    show scFold2 v R (q + roundLanes2) _ = scFold2 w R (q + roundLanes2) _
    rw [h0, h2, h5]
    exact scFold2_congr v w R (q + roundLanes2) _ fun j hj => by
      obtain ⟨a, b, c⟩ := h (j + 1) (by (clear * - j R hj; omega))
      simp only [roundLanes2]
      refine ⟨?_, ?_, ?_⟩
      · rw [show q + 14 + 14 * j = q + 14 * (j + 1) by ring]; exact a
      · rw [show q + 14 + 14 * j + 2 = q + 14 * (j + 1) + 2 by ring]; exact b
      · rw [show q + 14 + 14 * j + 5 = q + 14 * (j + 1) + 5 by ring]; exact c

theorem okG_true {g : Nat} {sig : ByteArray} : ∀ (n P : Nat),
    (∀ i < n, powOKR g (feAt sig (P + 48 + 80 * i)) = true) → okG g sig P n = true
  | 0, _, _ => rfl
  | n + 1, P, h => by
    rw [okG, h 0 (by (clear * - n; omega)), Bool.true_and]
    exact okG_true n (P + 80) fun i hi => by
      have := h (i + 1) (by (clear * - i n hi; omega)); rwa [show P + 48 + 80 * (i + 1) = P + 80 + 48 + 80 * i by ring] at this

theorem okS_true {g : Nat} {sig : ByteArray} : ∀ (R P : Nat),
    (∀ k < R, powOKR g (feAt sig (P + 80 + 112 * k)) = true) → okS g sig P R = true
  | 0, _, _ => rfl
  | R + 1, P, h => by
    rw [okS, h 0 (by (clear * - R; omega)), Bool.true_and]
    exact okS_true R (P + 112) fun k hk => by
      have := h (k + 1) (by (clear * - k R hk; omega)); rwa [show P + 80 + 112 * (k + 1) = P + 112 + 80 + 112 * k by ring] at this

end Lvm.Q2
