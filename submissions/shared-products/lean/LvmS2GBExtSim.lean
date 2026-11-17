-- New for lvm2 MP-B cap pruning (CAP-X, 2026-11-17): a program simulation on a fixed tape, for S2GB's extractor
-- whose log position depends on `|π|` (the S2GS reads take it as a constant).
import LvmXLookup

/-!
# Simulation of `XIR` programs on a tape

`Sim I P P'`: `P'` is `P` with some loop-free subprograms replaced by loop-free programs of the same semantics from every
state satisfying `Inv`, on the tape `I` (`Sim.leaf`). Then `P'` has `P`'s semantics (`Sim.sem`), is well formed
(`Sim.wf`), writes only what `P` writes (`Sim.writes`) and keeps `P`'s loop bounds (`Sim.safe`).

S2GB's extractor uses it with `P` the S2GS reads at the log position `pL` of the proof at hand and `P'` the reads that
compute `pL` from tape word 4 (`|π|`).
-/

set_option autoImplicit false

namespace Lvm.XB

open RecursionFast Lvm.X

/-- **`P'` simulates `P` on the tape `I`.** -/
inductive Sim (I : Array Word) : XIR → XIR → Prop
  | refl (P : XIR) : Sim I P P
  | leaf {P P' : XIR} (h : ∀ s : St, Lvm.X.Inv s.M → semXIR I P' s = semXIR I P s) (hw : WF P')
      (hwr : ∀ i, Writes P' i → Writes P i) (hn : NoLoopT P) (hn' : NoLoopT P') : Sim I P P'
  | seq {p q p' q' : XIR} : Sim I p p' → Sim I q q' → Sim I (.seq p q) (.seq p' q')
  | ite {c : ℕ} {p q p' q' : XIR} : Sim I p p' → Sim I q q' → Sim I (.ite c p q) (.ite c p' q')
  | loopK {c n : ℕ} {K : Word} {b b' : XIR} : Sim I b b' → Sim I (.loopK c n K b) (.loopK c n K b')
  | loopT {c n : ℕ} {cap : Aff} {b b' : XIR} : Sim I b b' → Sim I (.loopT c n cap b) (.loopT c n cap b')

variable {I : Array Word}

/-- `P'` writes only what `P` writes. -/
theorem Sim.writes {P P' : XIR} (h : Sim I P P') : ∀ i, Writes P' i → Writes P i := by
  induction h with
  | refl => exact fun _ h => h
  | leaf _ _ hwr => exact hwr
  | seq _ _ ihp ihq => exact fun i h => h.elim (fun h => .inl (ihp i h)) (fun h => .inr (ihq i h))
  | ite _ _ ihp ihq => exact fun i h => h.elim (fun h => .inl (ihp i h)) (fun h => .inr (ihq i h))
  | loopK _ ih => exact fun i h => h.elim .inl fun h => h.elim (fun h => .inr (.inl h)) fun h => .inr (.inr (ih i h))
  | loopT _ ih => exact fun i h => h.elim .inl fun h => .inr (ih i h)

/-- `P'` is well formed with `P`. -/
theorem Sim.wf {P P' : XIR} (h : Sim I P P') : WF P → WF P' := by
  induction h with
  | refl => exact id
  | leaf _ hw => exact fun _ => hw
  | seq _ _ ihp ihq => exact fun h => ⟨ihp h.1, ihq h.2⟩
  | ite _ _ ihp ihq => exact fun h => ⟨ihp h.1, ihq h.2⟩
  | loopK hb ih => exact fun h => ⟨h.1, h.2.1, fun hw => h.2.2.1 (hb.writes _ hw), ih h.2.2.2⟩
  | loopT hb ih => exact fun h => ⟨h.1, h.2.1, fun hw => h.2.2.1 (hb.writes _ hw), ih h.2.2.2⟩

/-- Loops of bodies with the same semantics from `Inv` states agree. -/
theorem iterL_congr {f f' : St → St} {c : ℕ} (hc : 4 ≤ c) (hf : ∀ s : St, Lvm.X.Inv s.M → Lvm.X.Inv (f s).M)
    (he : ∀ s : St, Lvm.X.Inv s.M → f' s = f s) : ∀ k s, Lvm.X.Inv s.M → iterL f' c k s = iterL f c k s
  | 0, _, _ => rfl
  | k + 1, s, h => by
    show iterL f' c k (decS c (f' s)) = iterL f c k (decS c (f s))
    rw [he s h]
    exact iterL_congr hc hf he k _ (inv_of_frame (hf s h) (size_decS ..)
      fun i hi => rd_decS (by (clear * - hc hi; omega)) _)

/-- **`P'` has `P`'s semantics** from every state satisfying `Inv`. -/
theorem Sim.sem {P P' : XIR} (h : Sim I P P') : WF P → ∀ s : St, Lvm.X.Inv s.M → semXIR I P' s = semXIR I P s := by
  induction h with
  | refl => exact fun _ _ _ => rfl
  | leaf he => exact fun _ => he
  | seq _ _ ihp ihq =>
    intro hw s hs
    show semXIR I _ (semXIR I _ s) = semXIR I _ (semXIR I _ s)
    rw [ihp hw.1 s hs, ihq hw.2 _ (inv_sem I hw.1 hs)]
  | ite _ _ ihp ihq =>
    intro hw s hs
    simp only [semXIR]
    split
    · exact ihq hw.2 s hs
    · exact ihp hw.1 s hs
  | @loopK c n K b b' _ ih =>
    intro hw s hs
    simp only [semXIR]
    have h0 : Lvm.X.Inv (entryK c n K s.M) := inv_of_frame hs (size_entryK ..)
      fun i hi => entryK_frame _ (by have := hw.1; (clear * - hi this; omega)) (by simp only [cTmp]; (clear * - hi; omega))
    exact iterL_congr (by have := hw.1; (clear * - this; omega)) (fun s' h' => inv_sem I hw.2.2.2 h')
      (ih hw.2.2.2) _ _ h0
  | @loopT c n cap b b' _ ih =>
    intro hw s hs
    simp only [semXIR]
    have h0 : Lvm.X.Inv (entryT c n s.M) := inv_of_frame hs (size_entryT ..)
      fun i hi => entryT_frame _ (by have := hw.1; (clear * - hi this; omega))
    exact iterL_congr (by have := hw.1; (clear * - this; omega)) (fun s' h' => inv_sem I hw.2.2.2 h')
      (ih hw.2.2.2) _ _ h0

/-- A loop-free program is safe. -/
theorem Sim.noLoopT {P P' : XIR} (h : Sim I P P') : NoLoopT P → NoLoopT P' := by
  induction h with
  | refl => exact id
  | leaf _ _ _ _ hn' => exact fun _ => hn'
  | seq _ _ ihp ihq => exact fun h => ⟨ihp h.1, ihq h.2⟩
  | ite _ _ ihp ihq => exact fun h => ⟨ihp h.1, ihq h.2⟩
  | loopK _ ih => exact fun h => ih h
  | loopT => exact fun h => h.elim

/-- Inversion at `seq`. -/
theorem Sim.inv_seq {p q P' : XIR} (h : Sim I (.seq p q) P') :
    (∃ p' q', P' = .seq p' q' ∧ Sim I p p' ∧ Sim I q q') ∨ (NoLoopT (.seq p q) ∧ NoLoopT P') := by
  cases h with
  | refl => exact .inl ⟨p, q, rfl, .refl _, .refl _⟩
  | leaf _ _ _ hn hn' => exact .inr ⟨hn, hn'⟩
  | seq hp hq => exact .inl ⟨_, _, rfl, hp, hq⟩

/-- Inversion at `loopT`. -/
theorem Sim.inv_loopT {c n : ℕ} {cap : Aff} {b P' : XIR} (h : Sim I (.loopT c n cap b) P') :
    ∃ b', P' = .loopT c n cap b' ∧ Sim I b b' := by
  cases h with
  | refl => exact ⟨b, rfl, .refl _⟩
  | leaf _ _ _ hn => exact hn.elim
  | loopT hb => exact ⟨_, rfl, hb⟩

/-- Inversion at `ite`. -/
theorem Sim.inv_ite {c : ℕ} {p q P' : XIR} (h : Sim I (.ite c p q) P') :
    (∃ p' q', P' = .ite c p' q' ∧ Sim I p p' ∧ Sim I q q') ∨ (NoLoopT (.ite c p q) ∧ NoLoopT P') := by
  cases h with
  | refl => exact .inl ⟨p, q, rfl, .refl _, .refl _⟩
  | leaf _ _ _ hn hn' => exact .inr ⟨hn, hn'⟩
  | ite hp hq => exact .inl ⟨_, _, rfl, hp, hq⟩

/-- Inversion at `loopK`. -/
theorem Sim.inv_loopK {c n : ℕ} {K : Word} {b P' : XIR} (h : Sim I (.loopK c n K b) P') :
    (∃ b', P' = .loopK c n K b' ∧ Sim I b b') ∨ (NoLoopT (.loopK c n K b) ∧ NoLoopT P') := by
  cases h with
  | refl => exact .inl ⟨b, rfl, .refl _⟩
  | leaf _ _ _ hn hn' => exact .inr ⟨hn, hn'⟩
  | loopK hb => exact .inl ⟨_, rfl, hb⟩

/-- **`P'` keeps `P`'s loop bounds.** -/
theorem Sim.safe {t : ℕ} {P : XIR} (hs : Safe I t P) : ∀ {P' : XIR}, Sim I P P' → WF P → Safe I t P' := by
  induction hs with
  | blk | load | store | input | out =>
    intro P' h _
    cases h with
    | refl => constructor
    | leaf _ _ _ _ hn' => exact safe_of_noLoopT hn'
  | seq _ _ ihp ihq =>
    intro P' h hw
    rcases h.inv_seq with ⟨p', q', rfl, hp, hq⟩ | ⟨-, hn'⟩
    · exact .seq (ihp hp hw.1) (ihq hq hw.2)
    · exact safe_of_noLoopT hn'
  | ite _ _ ihp ihq =>
    intro P' h hw
    rcases h.inv_ite with ⟨p', q', rfl, hp, hq⟩ | ⟨-, hn'⟩
    · exact .ite (ihp hp hw.1) (ihq hq hw.2)
    · exact safe_of_noLoopT hn'
  | loopK _ ih =>
    intro P' h hw
    rcases h.inv_loopK with ⟨b', rfl, hb⟩ | ⟨-, hn'⟩
    · exact .loopK (ih hb hw.2.2.2)
    · exact safe_of_noLoopT hn'
  | @loopT pre c n cap b _ hcnt _ ihpre ihb =>
    intro P' h hw
    rcases h.inv_seq with ⟨p', q', rfl, hp, hq⟩ | ⟨hn, -⟩
    · obtain ⟨b', rfl, hb⟩ := hq.inv_loopT
      refine .loopT (ihpre hp hw.1) (fun s hs => ?_) (ihb hb hw.2.2.2.2)
      rw [hp.sem hw.1 s hs]
      exact hcnt s hs
    · exact hn.2.elim

end Lvm.XB
