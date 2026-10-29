-- New for `flock-recursive` (BLUEPRINT §3, A.9; stage S-G3 pass 2, `hFin` step 1).
-- RET-2: the declarations revision 4.1 reads moved to `FRSoundnessCoreAcc`.
import FRSoundnessAccPos
import FRSoundnessCoreAcc

/-!
# `hFin`, step 1: an accepted run passes every phase and every final field

On a trace that `gen fin (.fixed κ)` consumes with verdict `true`:

* the skeleton is `refPhases` (`exec_skeleton`), every phase's flag holds, and the register file
  `R` it leaves has the size the finals start from (`genPhases_next`);
* every final field (`finRS`, then `Finals.rest` in order) runs, from a register file that
  extends `R`, to the flag `true` (**`accept_fields`**). The fields ask nothing (the `noAsk_*`
  lemmas), so each is a `pureRun` (`pureRun_noAsk`) and the run's flag is the conjunction
  (`exec_field`, `exec_ok_false`).

`runFields` is `Finals.ops`'s fold as a recursion (`foldl_step`).
-/

namespace FR.Snd
open RecursionFast

variable (impl : OpImpl) (κ : Kind) (inp : Input)

/-- The skeleton's next free register is the size of the register file it leaves. -/
theorem genPhases_next : ∀ (ps : List Phase) (n : ℕ) (c : GCtx) (r : Array Val) (tr : Trace)
    (y : List Val × List Bool × Trace), refPhases impl κ inp ps n c r tr = some y →
    c.next = r.size → StartOk ps c r → (genPhases ps n c).2.next = (r ++ y.1.toArray).size
  | [], _, c, r, tr, y, h, hb, _ => by
    simp only [refPhases, Option.some.injEq] at h; subst h; simp [genPhases, hb]
  | p :: ps, n, c, r, tr, y, h, hb, hs => by
    have hwf : (p.shape = .seed ∧ CtxOk c #[default]) ∨ CtxOk c r := by
      rcases hs with h | ⟨q, qs, he, hq, h0⟩
      · exact .inr h
      · cases he; exact .inl ⟨hq, h0⟩
    simp only [refPhases, Option.bind_eq_some_iff, Option.map_eq_some_iff] at h
    obtain ⟨x, hx, y', hy', rfl⟩ := h
    obtain ⟨h1, h2, -⟩ := genPhase_ctx impl κ inp n p c r tr x hb hwf hx
    have := genPhases_next ps (n + 1) _ _ _ y' hy' h1 (.inl h2)
    simp only [genPhases]
    rw [this]
    simp [Array.size_append]

/-- **An accepted run passes every phase and every final field**: the skeleton's registers `R`,
every phase flag `true`, and each field of `finRS :: Finals.rest` runs to `true` from registers
extending `R`, with the inputs the verifier gives it (R-V-m2): `finRS` with no `zhat` and no
exports; field `k` of the rest with `zhat` = `finRS`'s exports and `ex` = the exports of
`finRS` and the fields before it (`exAt`). -/
theorem accept_fields (fin : Finals) {tr : Trace}
    (hna : ∀ f ∈ fin.finRS :: fin.rest, ∀ fi b, (f fi b).1.filterMap Op.item? = [])
    (h : semIR impl (gen fin (.fixed κ)) inp tr = some true) :
    ∃ y, refPhases impl κ inp phases 0 ctx₀ #[] tr = some y ∧ (∀ b ∈ y.2.1, b = true) ∧
      (∃ Rk L, ExtA (#[] ++ y.1.toArray) Rk ∧ pureRun impl κ inp
        (fin.finRS ⟨skeleton.2.outs, [], #[]⟩ Rk.size).1 Rk [] = some (L, true)) ∧
      ∀ k (hk : k < fin.rest.length), ∃ Rk L, ExtA (#[] ++ y.1.toArray) Rk ∧
        pureRun impl κ inp ((fin.rest[k]'hk) ⟨skeleton.2.outs,
          (fin.finRS ⟨skeleton.2.outs, [], #[]⟩ skeleton.2.next).2,
          exAt skeleton.2.outs (fin.finRS ⟨skeleton.2.outs, [], #[]⟩ skeleton.2.next).2 fin.rest
            (skeleton.2.next + opsOut (fin.finRS ⟨skeleton.2.outs, [], #[]⟩ skeleton.2.next).1)
            #[(fin.finRS ⟨skeleton.2.outs, [], #[]⟩ skeleton.2.next).2] k⟩ Rk.size).1 Rk [] =
          some (L, true) := by
  unfold semIR at h
  split at h
  · next s hs =>
    simp only [Option.some.injEq] at h
    rw [show (gen fin (.fixed κ)).ops =
        skeleton.1 ++ (fin.ops skeleton.2.outs skeleton.2.next ++ [.accept]) by
      simp [gen, genWith], show (gen fin (.fixed κ)).kindOn inp = κ from rfl, St.init,
      exec_skeleton] at hs
    obtain ⟨y, hy, hs'⟩ := Option.bind_eq_some_iff.1 hs
    have hn := genPhases_next impl κ inp phases 0 ctx₀ #[] tr y hy rfl
      (.inr ⟨_, _, rfl, rfl, by simp [CtxOk, ctx₀]⟩)
    have hsk : genPhases phases 0 ctx₀ = skeleton := by rw [skeleton]; rfl
    rw [hsk] at hn
    rw [hn, finals_ops_eq] at hs'
    simp only [List.append_assoc] at hs'
    have hRS := fields_ok impl κ inp skeleton.2.outs [] [fin.finRS] _ #[] _ _ _ s []
      (fun f hf => hna f (by simp_all)) hs' h
    obtain ⟨hok, hRS⟩ := hRS
    refine ⟨y, hy, ?_, ?_, ?_⟩
    · simpa using hok
    · obtain ⟨Rk, L, hE, hp⟩ := hRS 0 (by simp)
      exact ⟨Rk, L, hE, hp⟩
    · -- the rest, after `finRS`
      obtain ⟨L, hL, -, h2⟩ := field_flag impl κ inp
        (hna _ (List.mem_cons_self ..) _ _) (by simpa only [runFields, List.append_nil] using hs') h
      have hsz : ((#[] ++ y.1.toArray) ++ L.toArray).size = (#[] ++ y.1.toArray).size +
          opsOut (fin.finRS ⟨skeleton.2.outs, [], #[]⟩ (#[] ++ y.1.toArray).size).1 := by
        have hl := pureRun_len impl κ inp _ _ [] L true hL
        simp [hl]
      rw [← hsz] at h2
      obtain ⟨-, hrest⟩ := fields_ok impl κ inp skeleton.2.outs _ fin.rest _ _ true _ _ s []
        (fun f hf => hna f (List.mem_cons_of_mem _ hf)) h2 h
      intro k hk
      obtain ⟨Rk, Lk, hE, hp⟩ := hrest k hk
      rw [hsz] at hp
      rw [hn]
      exact ⟨Rk, Lk, (ExtA.app _ L).trans hE, hp⟩
  · cases h

end FR.Snd
