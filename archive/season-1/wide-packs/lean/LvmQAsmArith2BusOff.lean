/- `LvmQAsmArith2BusOff` (GOLF2 off-path move, group 35 of 48): declarations that the certificate `certified`
   does not use, moved here verbatim (same names, same namespaces and context) from LvmQBusGkr, LvmQAsmArith2Bus,
   so that `Solution`'s import closure need not elaborate them. Import this module where they are needed;
   the name -> module map is GOLF2's moved.tsv. -/
import LvmQBusGkr
import LvmQAsmArith2Bus

-- ===== from `LvmQBusGkr` =====

section
set_option autoImplicit false
namespace Lvm.Loop.Build.QB
open Lvm.Loop Lvm.QB
section
variable {c : Ctx} {M : Mem}

/-- **Q_arith_eq, the GKR step's check**: with the gate on, the gadget's assertion holds iff `F`'s
`require (claim == polyEval products combiner)` passes. -/
theorem gkrFinals_check {z o gate γ claim : Cell} (hz : z.val M = 0) (ho : o.val M = 1)
    (hg : gate.val M = 1) (c₀ c₁ c₂ y : List Cell) (p : Ptr)
    (h : SegsHold c M p (gkrFinals z o gate γ claim c₀ c₁ c₂ y p).2) :
    vals M (gkrFinals z o gate γ claim c₀ c₁ c₂ y p).1 = gkrValues M c₀ c₁ c₂ y ∧
      (SegsAssert M p (gkrFinals z o gate γ claim c₀ c₁ c₂ y p).2 ↔
        (claim.val M == polyEval (gkrProducts M c₀ c₁ c₂) (γ.val M)) = true) := by
  obtain ⟨h1, h2⟩ := gkrFinals_spec (c := c) hz ho c₀ c₁ c₂ y p h
  refine ⟨h1, ?_⟩
  rw [h2, gate_eq_iff hg, FE.beq_iff, eq_comm]

/-- The step's first claim, `polyEval values combiner` (`F`: `polyEval state.values combiner`). -/
theorem gkrClaim_spec {z γ : Cell} (hz : z.val M = 0) (vs : List Cell) :
    ASpec c M (hornerG z γ vs) (fun r => r.val M = polyEval (vals M vs) (γ.val M)) True :=
  hornerG_spec hz vs

end
end Lvm.Loop.Build.QB
end

section
set_option autoImplicit false
namespace Lvm.Loop.Build.QB
open Lvm.Loop Lvm.QB

/-- Non-vacuity: a one-level step's finals pass the program check. -/
theorem gkrFinals_segsOk :
    segsOk ⟨1, 20⟩ (gkrFinals (ec 0) (ec 1) (kc 0) (ec 2) (ec 3) [ec 4, ec 5] [ec 6, ec 7] [ec 8, ec 9]
      [ec 10] ⟨1, 20⟩).2 = true := by decide

end Lvm.Loop.Build.QB
end

-- ===== from `LvmQAsmArith2Bus` =====

section
section
set_option autoImplicit false
namespace Lvm.Loop.Build.QB
open Lvm.Loop Lvm.QB

theorem tplP3_allE (a S : Nat) : AllE (tplP3 a S) := by simp [AllE, tplP3, ldRow]

end Lvm.Loop.Build.QB
end
end

section
section
set_option autoImplicit false
namespace Lvm.Loop.Build.QB
open Lvm.Loop Lvm.QB
section
variable {c : Ctx} {M : Mem}

theorem lawP3 (a S : Nat) (p : Ptr) (i₀ d : Nat) (hp : 1 ≤ p.e)
    (h : SegsHold c M p (loop [d] (tplP3 (a + S * i₀) S) p).2) (jf : Nat) (hjf : jf < 2 ^ d) :
    LawR M a S 2 6 (fun _ => none) (p.e + 6 * jf) (i₀ + jf) := by
  have hA := tplP3_allE (a + S * i₀) S
  have hok : OpdsOk (tplP3 (a + S * i₀) S) := by simp [OpdsOk, tplP3, ldRow, kOp, opdOk]
  have E := fun t (ht : t < 6) => loop1_eqs h hA hok (L := 6) rfl hjf ht
  have l0 : M.e (p.e + 0 + 6 * jf) = kE M (a + S * i₀ + S * jf) := rowEq_ld (E 0 (by decide))
  have l1 : M.e (p.e + 1 + 6 * jf) = kE M (a + S * i₀ + 3 + S * jf) := rowEq_ld (E 1 (by decide))
  have l2 : M.e (p.e + 2 + 6 * jf) = kE M (a + S * i₀ + 6 + S * jf) := rowEq_ld (E 2 (by decide))
  have r3 := E 3 (by decide)
  have r4 := E 4 (by decide)
  have r5 := E 5 (by decide)
  simp only [tplP3, List.getD_cons_succ, List.getD_cons_zero, RowEq, ov, ofK_zero, ofK_one,
    one_mul, add_zero] at r3 r4 r5
  have hs : ∀ t, p.e + t + 6 * jf = p.e + 6 * jf + t := fun t => by (clear * -; omega)
  have hq : p.e + 5 - 6 + 6 * jf = p.e + 6 * jf - 1 := by (clear * - hp; omega)
  rw [hq] at r3
  simp only [hs] at l0 l1 l2 r3 r4 r5
  generalize p.e + 6 * jf = e at *
  rw [kE_idx M (show a + S * i₀ + S * jf = a + 3 * 0 + S * (i₀ + jf) by ring)] at l0
  rw [kE_idx M (show a + S * i₀ + 3 + S * jf = a + 3 * 1 + S * (i₀ + jf) by ring)] at l1
  rw [kE_idx M (show a + S * i₀ + 6 + S * jf = a + 3 * 2 + S * (i₀ + jf) by ring)] at l2
  refine ⟨fun k hk => ?_, ?_⟩
  · interval_cases k
    · exact l0
    · exact l1
    · exact l2
  · simp only [memRnd, rstep, roundPoly, polyEval, sumE, List.range_succ, List.range_zero,
      List.map_nil, List.map_cons, List.nil_append, List.cons_append, List.headD_cons, List.tail_cons,
      List.foldr_cons, List.foldr_nil, List.foldl_cons, List.foldl_nil, Nat.add_zero, Nat.mul_zero,
      show (6 : Nat) - 1 = 5 from rfl] at l0 l1 l2 ⊢
    rw [← l0, ← l1, ← l2, r5, r4, r3]
    ring

end
end Lvm.Loop.Build.QB
end
end

section
section
set_option autoImplicit false
namespace Lvm.Loop.Build.QB
open Lvm.Loop Lvm.QB
section
variable {c : Ctx} {M : Mem}

/-- **Q_arith_eq, plain rounds of count 3** (`F`'s `sumcheck claim 3 (replicate n none)`). -/
theorem scRunP3_eq (ds : List Nat) (L₀ : Nat) (claim : Cell) (p : Ptr)
    (h : SegsHold c M p (scRunP3 ds L₀ claim p).2) (sig : ByteArray) (s : RS) (hs : s.msg = 0)
    (hent : s.ent = 8 * L₀)
    (hlanes : ∀ j, L₀ ≤ j → j < L₀ + 15 * nRounds ds → M.k j = lane sig j) :
    (scRunP3 ds L₀ claim p).1.val M =
        (sumcheck (claim.val M) 3 (List.replicate (nRounds ds) none) sig s).1.2 ∧
      ∀ i < nRounds ds, M.e (p.e + 1 + 6 * i + 2) =
        (sumcheck (claim.val M) 3 (List.replicate (nRounds ds) none) sig s).1.1.getD i 0 :=
  scRunG_eq 3 (by decide) _ 6 L₀ (fun _ => none) (fun i => ⟨tplP3_allE _ _, rfl⟩) (by decide) ds
    (fun p i₀ d _ hp h jf hjf => lawP3 (L₀ + 5) 15 p i₀ d hp h jf hjf) claim p h sig s hs hent _
    (by simp) (fun i hi => by simp [List.getD_eq_getElem?_getD, hi]) hlanes

end
end Lvm.Loop.Build.QB
end
end

section
section
set_option autoImplicit false
namespace Lvm.Loop.Build.QB
open Lvm.Loop Lvm.QB

theorem scRun_segsOk :
    segsOk ⟨400, 20⟩ (scRunP3 [3] 0 (ec 0) ⟨400, 20⟩).2 = true ∧
      segsOk ⟨400, 20⟩ (scRunP4 [2, 0] 0 (ec 0) ⟨400, 20⟩).2 = true ∧
      segsOk ⟨400, 20⟩ (scRunQ3 [1, 0] 0 (fun _ => 3) (fun _ => 1) (ec 0) ⟨400, 20⟩).2 = true ∧
      segsOk ⟨400, 20⟩ (scRunQ5 [1] 0 (fun _ => 3) (fun _ => 1) (ec 0) ⟨400, 20⟩).2 = true := by
  decide

end Lvm.Loop.Build.QB
end
end

section
section
set_option autoImplicit false
namespace Lvm.Loop.Build.QB
open Lvm.Loop Lvm.QB

/-- Non-vacuity: the gadget passes the program check. -/
theorem countNZ_segsOk : segsOk ⟨1, 20⟩ (countNZ (ec 0) (ec 1) (kc 0) (ec 2) ⟨1, 20⟩).2 = true := by
  decide

end Lvm.Loop.Build.QB
end
end

section
set_option autoImplicit false
namespace Lvm.Har
open Lvm Lvm.Loop Lvm.Loop.Build DM
section
variable {c : Ctx} {M : Mem} {sig : ByteArray} {T : Nat}

theorem ldEs_noassert (st : Nat) : ∀ (n a : Nat) (p : Ptr), SegsAssert M p (ldEs a st n p).2
  | 0, _, _ => trivial
  | n + 1, a, p => by
    have happ : ldEs a st (n + 1) = (ldE a >>= fun x => ldEs (a + st) st n >>= fun xs => pure (x :: xs)) :=
      rfl
    rw [happ, assert_bind, assert_bind]
    refine ⟨?_, ldEs_noassert st n _ _, trivial⟩
    simp [ldE, loadE, rowRes, SegsAssert, Program.RowAssert, rowInst]

end
end Lvm.Har
end

section
set_option autoImplicit false
namespace Lvm.Har
open Lvm Lvm.Loop Lvm.Loop.Build DM

theorem busPos_mod_P20 : busPos P20 % 8 = 0 := by decide
theorem busPos_mod_P8 : busPos P8 % 8 = 0 := by decide

/-- **Phase 2 at `P20`.** -/
theorem busG_replays_P20 {c : Ctx} {M : Mem} {sig : ByteArray} {T : Nat} (hS : Q1.Streamed M sig T)
    {z o g : Cell} (hz : z.val M = 0) (ho : o.val M = 1) (hg : g.val M = 1)
    (hT : busEnd P20 (busPos P20) + 40 ≤ 8 * T) (ptr : Ptr) :
    Replays c M sig (busPh P20) (busG P20 z o g (busPos P20)) ptr (busPos P20) (busEnd P20 (busPos P20))
      (BusR M) :=
  busG_replays hS hz ho hg P20 rfl busPos_mod_P20 hT ptr

/-- **Phase 2 at `P8`.** -/
theorem busG_replays_P8 {c : Ctx} {M : Mem} {sig : ByteArray} {T : Nat} (hS : Q1.Streamed M sig T)
    {z o g : Cell} (hz : z.val M = 0) (ho : o.val M = 1) (hg : g.val M = 1)
    (hT : busEnd P8 (busPos P8) + 40 ≤ 8 * T) (ptr : Ptr) :
    Replays c M sig (busPh P8) (busG P8 z o g (busPos P8)) ptr (busPos P8) (busEnd P8 (busPos P8))
      (BusR M) :=
  busG_replays hS hz ho hg P8 rfl busPos_mod_P8 hT ptr

end Lvm.Har
end
