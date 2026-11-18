-- New for lvm2 E2F (slice S1, E2F-QH1): `V`'s `E2` sumcheck (`sumcheckD`, LvmDecideE2) on a view of the stream, and
-- the `E2` sumcheck gadget (`scGadget2`, three coefficients) replaying it.
import LvmE2QKSem
import LvmE2QKGkr
import LvmDecideE2

/-!
# `V`'s `E2` sumcheck on the stream, and `scGadget2`

**`V` side.** From the reader's position `p = ent + msg`, a plain round of `count` coefficients reads `c₀` at byte
`p + 40`, `c₂ … c_{count−1}` at `p + 56 + 16k`, the nonce (8 B), and its ground challenge is lanes 0–1 of the answer at
`p + 48 + 16(count − 1)`; the next round starts at `p + 80 + 16(count − 1)` (`roundLen2`). **`sumcheckD_run`**:
`sumcheckD g claim count (none × R)` is `scSpec2` on `fe2At Σ`, `feAt Σ`; its flag is the flag before and every
challenge's `powOKR g` (`scPow2`).

**Circuit side.** **`sc2_spec`**: in a memory where `scGadget2 D 2 q claim` holds and the stream binds the lanes,
round `i`'s challenge cells (`scChal2`, stream lanes) are `V`'s challenge `i` and the claim cells after round `i`
(`scClaim2`) are `V`'s claim after `i + 1` rounds, from the position `8q − 40`.
-/

set_option autoImplicit false

namespace Lvm.Q1

open Lvm Lvm.Loop Lvm.Loop.Build DM Lvm.E2V

/-! ## `V` side -/

/-- `n` `E2` scalars at bytes `o, o + 16, …`. -/
def scalars2 (v : Nat → FE2) (o n : Nat) : List FE2 := (List.range n).map fun k => v (o + 16 * k)

/-- The bytes of one `E2` round's entry: length, state, `count − 1` scalars, the nonce, the answer. -/
def roundLen2 (count : Nat) : Nat := 80 + 16 * (count - 1)

/-- The round polynomial `V` forms in plain mode from the message at position `p`. -/
def roundPoly2 (v : Nat → FE2) (p count : Nat) (claim : FE2) : List FE2 :=
  v (p + 40) :: (claim + sumF (scalars2 v (p + 56) (count - 2))) :: scalars2 v (p + 56) (count - 2)

/-- The answer of the round at position `p`. -/
def ansAt2 (p count : Nat) : Nat := p + 48 + 16 * (count - 1)

/-- **`V`'s plain `E2` sumcheck from position `p`**: the challenges, the final claim, the proof-of-work checks. -/
def scSpec2 (v : Nat → FE2) (va : Nat → FE) (g count : Nat) : Nat → FE2 → Nat → List FE2 × FE2 × Bool
  | _, claim, 0 => ([], claim, true)
  | p, claim, R + 1 =>
    let ch := e2OfFE (va (ansAt2 p count))
    let r := scSpec2 v va g count (p + roundLen2 count) (polyEvalF (roundPoly2 v p count claim) ch) R
    (ch :: r.1, r.2.1, powOKR g (va (ansAt2 p count)) && r.2.2)

theorem readE2_run (sig : ByteArray) (s : RS) :
    readE2 sig s = (fe2At sig (s.ent + 40 + s.msg), { s with msg := s.msg + 16 }) := rfl

theorem readE2s_succ (n : Nat) :
    readE2s (n + 1) = (readE2 >>= fun x => readE2s n >>= fun xs => pure (x :: xs)) := rfl

theorem readE2s_run (sig : ByteArray) : ∀ (n : Nat) (s : RS),
    readE2s n sig s = (scalars2 (fe2At sig) (s.ent + s.msg + 40) n, { s with msg := s.msg + 16 * n })
  | 0, s => rfl
  | n + 1, s => by
    rw [readE2s_succ, bind_run, readE2_run, bind_run, readE2s_run sig n, pure_run]
    generalize fe2At sig = v
    simp only [scalars2, List.range_succ_eq_map, List.map_cons, List.map_map, Function.comp_def]
    have h1 : s.ent + 40 + s.msg = s.ent + s.msg + 40 + 16 * 0 := by (clear * - s; omega)
    have h2 : ∀ k, s.ent + (s.msg + 16) + 40 + 16 * k = s.ent + s.msg + 40 + 16 * (k + 1) := by
      intro k; (clear * - s k; omega)
    have h3 : s.msg + 16 + 16 * n = s.msg + 16 * (n + 1) := by (clear * - s n; omega)
    simp only [h1, h2, h3]

/-- **A ground challenge**: the nonce, the answer at `ent + msg + 48`, its `powOKR g`. -/
theorem sampleG_run (sig : ByteArray) (g : Nat) (s : RS) :
    sampleG g sig s = (e2OfFE (feAt sig (s.ent + s.msg + 48)),
      ⟨s.ent + s.msg + 80, 0, powOKR g (feAt sig (s.ent + s.msg + 48)) && s.ok⟩) := by
  have h1 : s.ent + 40 + (s.msg + 8) = s.ent + s.msg + 48 := by (clear * - s; omega)
  have h2 : s.ent + 72 + (s.msg + 8) = s.ent + s.msg + 80 := by (clear * - s; omega)
  show (e2OfFE (feAt sig (s.ent + 40 + (s.msg + 8))),
      (⟨s.ent + 72 + (s.msg + 8), 0, powOKR g (feAt sig (s.ent + 40 + (s.msg + 8))) && s.ok⟩ : RS)) = _
  rw [h1, h2]

theorem roundPolyD_run (sig : ByteArray) (count : Nat) (hc : 2 ≤ count) (claim : FE2) (s : RS) :
    roundPolyD count claim none sig s =
      (roundPoly2 (fe2At sig) (s.ent + s.msg) count claim, { s with msg := s.msg + 16 * (count - 1) }) := by
  rw [show roundPolyD count claim none = (readE2 >>= fun c0 => readE2s (count - 2) >>=
    fun tail => pure (c0 :: (claim + sumF tail) :: tail)) from rfl]
  rw [bind_run, readE2_run, bind_run, readE2s_run, pure_run]
  generalize fe2At sig = v
  have h1 : s.ent + (s.msg + 16) + 40 = s.ent + s.msg + 56 := by (clear * - s count; omega)
  have h2 : s.ent + 40 + s.msg = s.ent + s.msg + 40 := by (clear * - s count; omega)
  have h3 : s.msg + 16 + 16 * (count - 2) = s.msg + 16 * (count - 1) := by (clear * - s count hc; omega)
  simp only [roundPoly2, h1, h2, h3]

theorem sumcheckD_cons (g : Nat) (claim : FE2) (count : Nat) (e : Option FE2) (es : List (Option FE2)) :
    sumcheckD g claim count (e :: es) = (roundPolyD count claim e >>= fun msg =>
      sampleG g >>= fun c => sumcheckD g (polyEvalF msg c) count es >>= fun res =>
        pure (c :: res.1, res.2)) := rfl

/-- **`V`'s plain `E2` sumcheck is `scSpec2`** on the stream: its challenges and final claim, its position
moved by `R · roundLen2 count`, its flag the flag before and the challenges' proof-of-work checks. -/
theorem sumcheckD_run (sig : ByteArray) (g count : Nat) (hc : 2 ≤ count) :
    ∀ (R : Nat) (claim : FE2) (s : RS) (p : Nat), s.ent + s.msg = p →
      ((sumcheckD g claim count (List.replicate R none) sig s).1 =
          ((scSpec2 (fe2At sig) (feAt sig) g count p claim R).1,
            (scSpec2 (fe2At sig) (feAt sig) g count p claim R).2.1)) ∧
      (sumcheckD g claim count (List.replicate R none) sig s).2.ent +
          (sumcheckD g claim count (List.replicate R none) sig s).2.msg = p + R * roundLen2 count ∧
      (sumcheckD g claim count (List.replicate R none) sig s).2.ok =
          ((scSpec2 (fe2At sig) (feAt sig) g count p claim R).2.2 && s.ok)
  | 0, claim, s, p, hp =>
    ⟨rfl, by rw [← hp, Nat.zero_mul, Nat.add_zero]; rfl, by show s.ok = (true && s.ok); rw [Bool.true_and]⟩
  | R + 1, claim, s, p, hp => by
    rw [List.replicate_succ, sumcheckD_cons, bind_run, roundPolyD_run sig count hc, bind_run, sampleG_run,
      bind_run, pure_run]
    dsimp only
    have ha : s.ent + (s.msg + 16 * (count - 1)) + 48 = ansAt2 p count := by
      simp only [ansAt2]; (clear * - s count p hp; omega)
    rw [ha, hp]
    obtain ⟨i1, i2, i3⟩ := sumcheckD_run sig g count hc R
      (polyEvalF (roundPoly2 (fe2At sig) p count claim) (e2OfFE (feAt sig (ansAt2 p count))))
      ⟨s.ent + (s.msg + 16 * (count - 1)) + 80, 0, powOKR g (feAt sig (ansAt2 p count)) && s.ok⟩
      (p + roundLen2 count) (by show _ + 0 = _; simp only [roundLen2]; (clear * - s count p hp; omega))
    refine ⟨?_, ?_, ?_⟩
    · rw [i1]; rfl
    · rw [i2]; ring
    · rw [i3]
      show _ = ((powOKR g (feAt sig (ansAt2 p count)) && _) && s.ok)
      cases powOKR g (feAt sig (ansAt2 p count)) <;> cases s.ok <;> simp

theorem scSpec2_fst_getD (v : Nat → FE2) (va : Nat → FE) (g count : Nat) :
    ∀ (i R p : Nat) (claim : FE2), i < R →
      (scSpec2 v va g count p claim R).1.getD i 0 = e2OfFE (va (ansAt2 (p + i * roundLen2 count) count))
  | _, 0, _, _, h => absurd h (Nat.not_lt_zero _)
  | 0, R + 1, p, claim, _ => by simp [scSpec2]
  | i + 1, R + 1, p, claim, h => by
    simp only [scSpec2, List.getD_cons_succ]
    rw [scSpec2_fst_getD v va g count i R _ _ (by (clear * - i R h; omega))]
    congr 3; ring

theorem scSpec2_snd_succ (v : Nat → FE2) (va : Nat → FE) (g count : Nat) :
    ∀ (i p : Nat) (claim : FE2),
      (scSpec2 v va g count p claim (i + 1)).2.1 =
        polyEvalF (roundPoly2 v (p + i * roundLen2 count) count (scSpec2 v va g count p claim i).2.1)
          (e2OfFE (va (ansAt2 (p + i * roundLen2 count) count)))
  | 0, p, claim => by simp [scSpec2]
  | i + 1, p, claim => by
    have e1 : (scSpec2 v va g count p claim (i + 1 + 1)).2.1 = (scSpec2 v va g count (p + roundLen2 count)
        (polyEvalF (roundPoly2 v p count claim) (e2OfFE (va (ansAt2 p count)))) (i + 1)).2.1 := rfl
    have e2 : (scSpec2 v va g count p claim (i + 1)).2.1 = (scSpec2 v va g count (p + roundLen2 count)
        (polyEvalF (roundPoly2 v p count claim) (e2OfFE (va (ansAt2 p count)))) i).2.1 := rfl
    rw [e1, e2, scSpec2_snd_succ v va g count i,
      show p + roundLen2 count + i * roundLen2 count = p + (i + 1) * roundLen2 count by ring]

/-! ## Circuit side: `scGadget2` with three coefficients -/

/-- The stream's lanes are `K` cells: an `E2` pair of lanes is the `E2` scalar at its byte. -/
theorem laneC2_val {M : Mem} {sig : ByteArray} {T : Nat} (hS : Streamed M sig T) {a : Nat} (ha : a + 1 < T) :
    (laneC2 a).val M = fe2At sig (8 * a) := by
  show (⟨(FE.ofK (M.k a)).c₀, (FE.ofK (M.k (a + 1))).c₀⟩ : FE2) = _
  rw [hS a (by (clear * - a T ha; omega)), hS (a + 1) ha]
  show (⟨kAt sig (8 * a), kAt sig (8 * (a + 1))⟩ : FE2) = ⟨kAt sig (8 * a), kAt sig (8 * a + 8)⟩
  rw [show 8 * (a + 1) = 8 * a + 8 by ring]

theorem e2OfFE_feAt (sig : ByteArray) (o : Nat) : e2OfFE (feAt sig o) = fe2At sig o := rfl

theorem scLen2_two : scLen2 2 = 6 := rfl

theorem scTpl2_two (q : Nat) : scTpl2 2 q =
    lin2I 1 0 (.prev 4, .prev 5) (lane2 (q + 2) [14]) ++
      mul2I (lane2 (q + 2) [14]) (lane2 (q + 5) [14]) (.loc 0, .loc 1) ++
      mul2I (.loc 2, .loc 3) (lane2 (q + 5) [14]) (lane2 q [14]) := rfl

theorem thold2_of_loopP {c : Ctx} {M : Mem} {dims : List Nat} {ins : List Ins} {init : Nat → Cell} {p : Ptr}
    (h : SegsHold c M p (loopP dims (tplOf ins) init p).2) {jf : Nat} (hjf : jf < 2 ^ dims.sum) :
    THold2 (iterXv M (loopP dims (tplOf ins) init p).1 jf) (iterF M (loopP dims (tplOf ins) init p).1 jf) 0 ins := by
  rw [loopP_fst]
  exact thold2_of_loop (hold_loop_of_loopP h) hjf

/-- A pair of strided stream lanes in iteration `jf` of a one-dimensional loop. -/
theorem lane2_val {M : Mem} {sig : ByteArray} {T : Nat} (hS : Streamed M sig T) (o : LoopOut) {D : Nat}
    (ho : o.dims = [D]) {jf : Nat} (hjf : jf < 2 ^ D) (V : Nat → FE) {a s : Nat} (ha : a + s * jf + 1 < T) :
    (lane2 a [s]).valF (iterXv M o jf) V = fe2At sig (8 * (a + s * jf)) := by
  show (⟨(iterXv M o jf (.ext ⟨.K, a, [s]⟩)).c₀, (iterXv M o jf (.ext ⟨.K, a + 1, [s]⟩)).c₀⟩ : FE2) = _
  rw [iterXv_ext1 M o ho hjf, iterXv_ext1 M o ho hjf]
  show (⟨M.k (a + s * jf), M.k (a + 1 + s * jf)⟩ : FE2) = _
  rw [hS _ (by (clear * - a s jf T D ha; omega)), hS _ (by (clear * - a s jf T D ha; omega))]
  show (⟨kAt sig (8 * (a + s * jf)), kAt sig (8 * (a + 1 + s * jf))⟩ : FE2) =
    ⟨kAt sig (8 * (a + s * jf)), kAt sig (8 * (a + s * jf) + 8)⟩
  rw [show 8 * (a + 1 + s * jf) = 8 * (a + s * jf) + 8 by ring]

/-- The claim an iteration reads (the previous iteration's last pair, the prologue's at iteration `0`). -/
def scPrev2 (M : Mem) (o : LoopOut) (jf : Nat) : FE2 :=
  ⟨((Opd.prev 4).val M o jf).c₀, ((Opd.prev 5).val M o jf).c₀⟩

/-- A twin pair at position `n` of a template that holds. -/
theorem thold2_e2I {xv : Src → FE} {V : Nat → FE} {ins : List Ins} (hH : THold2 xv V 0 ins) {n : Nat} {f : E2Fn}
    {xs : List S2} (hseg : Seg ins n (e2I f xs)) (hlen : n + 2 ≤ ins.length) :
    (⟨(V n).c₀, (V (n + 1)).c₀⟩ : FE2) = f.val fun o => ((s2Args xs).getD o default |>.valF xv V).c₀ := by
  have g0 := hseg 0 (by simp [e2I])
  have g1 := hseg 1 (by simp [e2I])
  simp only [Nat.add_zero, e2I, List.getD_cons_zero, List.getD_cons_succ] at g0 g1
  have h0 := hH n (by (clear * - n ins hlen; omega)) (Or.inr ⟨f, false, by rw [g0]⟩)
  have h1 := hH (n + 1) (by (clear * - n ins hlen; omega)) (Or.inr ⟨f, true, by rw [g1]⟩)
  rw [Nat.zero_add, g0] at h0
  rw [Nat.zero_add, g1] at h1
  simp only [Ins.evalF2] at h0 h1
  apply FE2.ext_coord
  · show (V n).c₀ = _; rw [h0]; rfl
  · show (V (n + 1)).c₀ = _; rw [h1]; rfl

/-- **The round template's value**: `((c₂·ρ + (claim + c₂))·ρ + c₀)` on any values where it holds. -/
theorem sc2_round_val {xv : Src → FE} {V : Nat → FE} {q : Nat} (hH : THold2 xv V 0 (scTpl2 2 q)) :
    (⟨(V 4).c₀, (V 5).c₀⟩ : FE2) =
      ((lane2 (q + 2) [14]).valF xv V * (lane2 (q + 5) [14]).valF xv V +
          (S2.valF xv V (Src.prev 4, Src.prev 5) + (lane2 (q + 2) [14]).valF xv V)) *
        (lane2 (q + 5) [14]).valF xv V + (lane2 q [14]).valF xv V := by
  rw [scTpl2_two] at hH
  have hl : (lin2I 1 0 (.prev 4, .prev 5) (lane2 (q + 2) [14]) ++
      mul2I (lane2 (q + 2) [14]) (lane2 (q + 5) [14]) (.loc 0, .loc 1) ++
      mul2I (.loc 2, .loc 3) (lane2 (q + 5) [14]) (lane2 q [14])).length = 6 := rfl
  have e0 := thold2_e2I hH (n := 0) (f := .lin 1 (0 : FE2).re (0 : FE2).im)
    (xs := [(Src.prev 4, Src.prev 5), lane2 (q + 2) [14]])
    (by intro i hi; simp only [e2I, List.length_cons, List.length_nil] at hi; interval_cases i <;> try rfl)
    (by rw [hl]; all_goals (clear * - q; omega))
  have e1 := thold2_e2I hH (n := 2) (f := .mul) (xs := [lane2 (q + 2) [14], lane2 (q + 5) [14], (.loc 0, .loc 1)])
    (by intro i hi; simp only [e2I, List.length_cons, List.length_nil] at hi; interval_cases i <;> try rfl)
    (by rw [hl]; all_goals (clear * - q; omega))
  have e2 := thold2_e2I hH (n := 4) (f := .mul) (xs := [(.loc 2, .loc 3), lane2 (q + 5) [14], lane2 q [14]])
    (by intro i hi; simp only [e2I, List.length_cons, List.length_nil] at hi; interval_cases i <;> try rfl)
    (by rw [hl]; all_goals omega)
  have v0 : S2.valF xv V (Src.loc 0, Src.loc 1) =
      S2.valF xv V (Src.prev 4, Src.prev 5) + (lane2 (q + 2) [14]).valF xv V := by
    show (⟨(V 0).c₀, (V (0 + 1)).c₀⟩ : FE2) = _
    rw [e0]; show _ + FE2.ofK 1 * _ + ⟨(0 : FE2).re, (0 : FE2).im⟩ = _
    rw [fe2_ofK_one, one_mul, add_zero]
    rfl
  have v1 : S2.valF xv V (Src.loc 2, Src.loc 3) = (lane2 (q + 2) [14]).valF xv V * (lane2 (q + 5) [14]).valF xv V +
      S2.valF xv V (Src.loc 0, Src.loc 1) := by
    show (⟨(V 2).c₀, (V (2 + 1)).c₀⟩ : FE2) = _
    rw [e1]; rfl
  show (⟨(V 4).c₀, (V (4 + 1)).c₀⟩ : FE2) = _
  rw [e2]
  show S2.valF xv V (Src.loc 2, Src.loc 3) * _ + _ = _
  rw [v1, v0]
  rfl

/-- **One iteration of `scGadget2 D 2 q`** is one plain round of `V`'s `E2` sumcheck (three coefficients) at the
position `8q − 40 + jf · 112`, from the claim it reads. -/
theorem sc2_iter {c : Ctx} {M : Mem} {p : Ptr} {D q : Nat} {claim : C2} {sig : ByteArray} {T : Nat}
    (hq : 5 ≤ q) (hS : Streamed M sig T) (h : SegsHold c M p (scGadget2 D 2 q claim p).2) {jf : Nat}
    (hjf : jf < 2 ^ D) (hT : q + 14 * jf + 7 ≤ T) :
    ((scGadget2 D 2 q claim p).1.cell2 4 jf).val M =
      polyEvalF (roundPoly2 (fe2At sig) (8 * q - 40 + jf * roundLen2 3) 3 (scPrev2 M (scGadget2 D 2 q claim p).1 jf))
        (e2OfFE (feAt sig (ansAt2 (8 * q - 40 + jf * roundLen2 3) 3))) := by
  unfold scGadget2 at h ⊢
  have hH := thold2_of_loopP (dims := [D]) (ins := scTpl2 2 q) h (jf := jf) (by simpa using hjf)
  have hr := sc2_round_val hH
  generalize hodef : (loopP [D] (tplOf (scTpl2 2 q)) (fun t => if t = scLen2 2 - 1 then claim.im else claim.re)
    p).1 = o at hr ⊢
  have ho : o.dims = [D] := by rw [← hodef]; rfl
  have hl : ∀ a, a + 14 * jf + 1 < T → (lane2 a [14]).valF (iterXv M o jf) (iterF M o jf) =
      fe2At sig (8 * (a + 14 * jf)) := fun a ha => lane2_val hS o ho hjf _ ha
  have hcell : (o.cell2 4 jf).val M = (⟨(iterF M o jf 4).c₀, (iterF M o jf 5).c₀⟩ : FE2) := rfl
  have hprev : S2.valF (iterXv M o jf) (iterF M o jf) (Src.prev 4, Src.prev 5) = scPrev2 M o jf := rfl
  rw [hcell, hr, hprev, hl (q + 5) (by (clear * - q jf T D hT; omega)), hl (q + 2) (by (clear * - q jf T D hT; omega)), hl q (by (clear * - q jf T D hT; omega))]
  simp only [roundPoly2, scalars2, polyEvalF, ansAt2, roundLen2, sumF, List.range_one, List.map_cons, List.map_nil,
    List.foldl_cons, List.foldl_nil, List.foldr_cons, List.foldr_nil, show 3 - 2 = 1 from rfl,
    show 3 - 1 = 2 from rfl, e2OfFE_feAt, Nat.mul_zero, Nat.add_zero, zero_add, zero_mul]
  have p0 : 8 * (q + 14 * jf) = 8 * q - 40 + jf * (80 + 16 * 2) + 40 := by (clear * - q jf D T hq; omega)
  have p2 : 8 * (q + 2 + 14 * jf) = 8 * q - 40 + jf * (80 + 16 * 2) + 56 := by (clear * - q jf D T p0; omega)
  have p5 : 8 * (q + 5 + 14 * jf) = 8 * q - 40 + jf * (80 + 16 * 2) + 48 + 16 * 2 := by (clear * - q jf D T p0; omega)
  rw [p0, p2, p5]

/-- **`scGadget2 D 2 q claim` replays `V`'s plain `E2` sumcheck** (three coefficients, `R ≤ 2^D` rounds) from the
position `8q − 40`: round `i`'s challenge cells are `V`'s challenge `i` and the claim cells after round `i` are `V`'s
claim after `i + 1` rounds (for any grinding `g`: the proof-of-work checks are not the gadget's). -/
theorem sc2_spec {c : Ctx} {M : Mem} {p : Ptr} {D q R : Nat} {claim : C2} {sig : ByteArray} {T : Nat} (g : Nat)
    (hR : R ≤ 2 ^ D) (hq : 5 ≤ q) (hS : Streamed M sig T) (hT : q + 14 * R + 7 ≤ T)
    (h : SegsHold c M p (scGadget2 D 2 q claim p).2) :
    ∀ i < R,
      (scChal2 2 q i).val M = (scSpec2 (fe2At sig) (feAt sig) g 3 (8 * q - 40) (claim.val M) R).1.getD i 0 ∧
      (scClaim2 (scGadget2 D 2 q claim p).1 2 i).val M =
        (scSpec2 (fe2At sig) (feAt sig) g 3 (8 * q - 40) (claim.val M) (i + 1)).2.1 := by
  have hch : ∀ i < R, (scChal2 2 q i).val M =
      (scSpec2 (fe2At sig) (feAt sig) g 3 (8 * q - 40) (claim.val M) R).1.getD i 0 := by
    intro i hi
    rw [scSpec2_fst_getD _ _ _ _ i R _ _ hi, e2OfFE_feAt, show scChal2 2 q i = laneC2 (q + 14 * i + 5) from rfl,
      laneC2_val hS (by (clear * - q i T D R hT hi; omega))]
    congr 1
    simp only [ansAt2, roundLen2]
    (clear * - q i D R T hq; omega)
  have hlen : (tplOf (scTpl2 2 q)).length = 6 := rfl
  have hop : ((tplOf (scTpl2 2 q)).getD 4 default).op ≠ .assert0 := by
    rw [scTpl2_two]; simp [tplOf, mul2I, e2I, lin2I, Ins.toLRow]
  have hop5 : ((tplOf (scTpl2 2 q)).getD 5 default).op ≠ .assert0 := by
    rw [scTpl2_two]; simp [tplOf, mul2I, e2I, lin2I, Ins.toLRow]
  intro i
  induction i with
  | zero =>
    intro hi
    refine ⟨hch 0 hi, ?_⟩
    rw [scSpec2_snd_succ, show scClaim2 (scGadget2 D 2 q claim p).1 2 0 = (scGadget2 D 2 q claim p).1.cell2 4 0
      from rfl, sc2_iter hq hS h (by (clear * - D q R T hR hi; omega)) (by (clear * - q T D R hT hi; omega))]
    have hp : scPrev2 M (scGadget2 D 2 q claim p).1 0 = claim.val M := by
      show (⟨((Opd.prev 4).val M (loopP [D] (tplOf (scTpl2 2 q)) _ p).1 0).c₀,
        ((Opd.prev 5).val M (loopP [D] (tplOf (scTpl2 2 q)) _ p).1 0).c₀⟩ : FE2) = _
      rw [loopP_prev_zero h (by rw [hlen]; (clear * - D q R T; omega)) hop, loopP_prev_zero h (by rw [hlen]; (clear * - D q R T; omega)) hop5]
      rfl
    rw [hp]
    rfl
  | succ i ih =>
    intro hi
    refine ⟨hch (i + 1) hi, ?_⟩
    rw [scSpec2_snd_succ, show scClaim2 (scGadget2 D 2 q claim p).1 2 (i + 1) =
      (scGadget2 D 2 q claim p).1.cell2 4 (i + 1) from rfl, sc2_iter hq hS h (by (clear * - i D q R T hR hi; omega)) (by (clear * - q i T D R hT hi; omega))]
    have hp : scPrev2 M (scGadget2 D 2 q claim p).1 (i + 1) = (scClaim2 (scGadget2 D 2 q claim p).1 2 i).val M := by
      show (⟨((Opd.prev 4).val M (loopP [D] (tplOf (scTpl2 2 q)) _ p).1 (i + 1)).c₀,
        ((Opd.prev 5).val M (loopP [D] (tplOf (scTpl2 2 q)) _ p).1 (i + 1)).c₀⟩ : FE2) = _
      rw [loopP_prev_succ M [D] _ _ p (by simp; (clear * - i D q R T hR hi; omega)), loopP_prev_succ M [D] _ _ p (by simp; (clear * - i D q R T hR hi; omega))]
      rfl
    rw [hp, (ih (by (clear * - i R D q T hi; omega))).2]

end Lvm.Q1
