-- Ported from leanVM `formal/lean_vm/LeanVM/Protocol/Compile/SpecRules/Cert.lean` (formal rev 40f877dc) as `LvmSpecRulesCert` for lvm (WP-2).
/-
  LeanVM.Protocol.Compile.SpecRules.Cert

  The doom certificate of a whole verifier program from a specification of it.
-/


import LvmSpecRulesBind

-- (GOLF2: 9 declarations that `certified` does not use moved verbatim to `LvmInvCertOff`, outside its import closure.)

/-!
# From a specification to a doom certificate

A specification `S : Spec P (fun _ ↦ False) (fun b _ ↦ b = false) εmax L 0` of a whole verifier
program `P : VerifierProgram Bool` (no follower; the postcondition is rejection; the precondition is
discharged at the start by hand) is a doom certificate `S.toCert` with doom `S.D []` and the
escape bound of the group at `h` the potential `S.V [] h` (where `h` is a reachable boundary in
doom, `0` elsewhere). The certificate's escape bounds, discounted by the proof of work before
each group, are at most `εmax` (`Spec.toCert_bound`), given the start group's bound.
`Spec.toCertOfLead` takes instead a specification from the empty history with lead at most
`εmax`.

The core is `Spec.esc_le`: from a reachable history, the probability that the group escapes doom
is at most the potential, because the potential is a supermartingale over the challenges, does
not grow at openings, and is `1` wherever the group ends outside doom (`moveEnd`, `retEnd`); a
rejection, a `false` verdict, and an opening of a missing commitment escape nothing.
-/

namespace LeanVM.Protocol.Compile

open LeanVM.Parameters VerifierProgram

section

namespace Spec

variable {P : VerifierProgram Bool} {εmax L : ENNReal}

/-- The escape probability of a group is at most the potential. -/
theorem esc_le (S : Spec P (fun _ ↦ False) (fun b _ ↦ b = false) εmax L 0) :
    ∀ (q : VerifierProgram Bool) {l : List Ev}, P.Reachable l → P.after l = some q →
      esc (S.D []) l q ≤ S.V [] l
  | .ret true, l, hl, ha => by
    simp only [esc]
    split_ifs with hD
    · exact zero_le
    · exact S.retEnd (reach_nil_iff.2 hl) ha hD
  | .ret false, l, _, _ => by simp [esc]
  | .fail, l, _, _ => by simp [esc]
  | .read k, l, hl, ha => by
    simp only [esc]
    split_ifs with hD
    · exact zero_le
    · exact S.moveEnd (reach_nil_iff.2 hl) ha trivial hD
  | .grind b k, l, hl, ha => by
    simp only [esc]
    split_ifs with hD
    · exact zero_le
    · exact S.moveEnd (reach_nil_iff.2 hl) ha trivial hD
  | .commit ht w k, l, hl, ha => by
    simp only [esc]
    split_ifs with hD
    · exact zero_le
    · exact S.moveEnd (reach_nil_iff.2 hl) ha trivial hD
  | .sample k, l, hl, ha => by
    simp only [esc]
    calc (Fintype.card E : ENNReal)⁻¹ * ∑ c : E, esc (S.D []) (l ++ [Ev.sample c]) (k c)
        ≤ (Fintype.card E : ENNReal)⁻¹ * ∑ c : E, S.V [] (l ++ [Ev.sample c]) := by
          gcongr with c
          exact esc_le S (k c) (.sample c hl ha) (by rw [after_snoc _ ha]; simp [after])
      _ ≤ S.V [] l := S.sample (reach_nil_iff.2 hl) ha
  | .query i ps k, l, hl, ha => by
    simp only [esc]
    split
    · rename_i rows hans
      exact (esc_le S (k rows) (.query hl ha hans) (by rw [after_snoc _ ha]; simp [after])).trans
        (S.query (reach_nil_iff.2 hl) ha (by simpa using hans))
    · exact zero_le

end Spec

end
end LeanVM.Protocol.Compile
