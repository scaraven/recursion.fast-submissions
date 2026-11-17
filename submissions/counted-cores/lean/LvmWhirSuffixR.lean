-- New for lvm2 (WP JB-L, J2): the opening after the residual, from the residual's doom: the second half of
-- `stackedPrefixSpecR` (LvmWhirSpecR), as `LvmCertSRes` uses `finQuerySpec` for unique decoding.
/-
  LeanVM.Protocol.Whir.Sound (lvm2: the relativised opening after the residual)
-/

import LvmWhirSpecR

-- (GOLF2: 4 declarations that `certified` does not use moved verbatim to `LvmWhirSuffixROff`, outside its import closure.)

/-!
# After the residual

`verifyStackedJ_eq_prefix` splits the opening at the final residual into `stackPrefixJ` and
`stackSuffixJ`. `stackedPrefixSpecR` ends in `PostR`: the residual is good (`GoodRes`: the extractor's
case) or the residual's doom `ResC` holds. This module closes the second case:

* `finInfo_index`, `finInfo_snd_fst`, `finInfo_snd_snd`: `finInfo`'s final index, fold count before
  it and fold count are the last level's (`levels.length − 1 + i`, `pre + Σ` of the others, its
  `fold`), the form `PostR`'s `ResC` and `finQuerySpec`'s `FinHyp` use;
* `finSuffixSpecR`: from `ResC` the suffix (`finSuffixJ`: proof of work, query group, glue, tail,
  terminal check) rejects but with probability `2^-g·eQueryFinal` at the query group and `eTail`
  per tail round (`grindPreInv`, then WP-7's `finQuerySpec`); post `False`;
* `finSuffixRec20JSpec`: at J2's `C_rec` (`cfgRec20J`, final level `(3, 3, 77)`, code `codeJ10R3`).

So an accepting run of J2's `C_rec` opening is, but for these escapes and `stackedPrefixSpecR`'s,
in `GoodRes` at the residual: it ends in a fold of a good candidate.
-/

namespace LeanVM.Protocol.Whir.Sound

open LeanVM.Parameters LeanVM.Protocol.Compile LeanVM.Protocol.Verifier
  LeanVM.Protocol.Whir LeanVM.Protocol.EndToEnd VerifierProgram Finset

section

variable {μ ℓ₀ per c₀ n₀ g : ℕ} {dir : Bool} {w : List E → E} {i : ℕ} {P : LevelCode}
  {level : Whir.Level} {pre : ℕ} {εmax : ENNReal}

/-- **The opening after the residual, from the residual's doom**: the proof of work, the query
group (escape `2^-g·eQueryFinal`), the glue, the tail (`eTail` per round) and the terminal check;
it never returns in doom. -/
noncomputable def finSuffixSpecR (H : FinHyp μ ℓ₀ per c₀ n₀ w P level pre) (hg : g ≤ 192)
    (hQlt : eQueryFinal P level.queries < 1)
    (hεQ : (2 : ENNReal)⁻¹ ^ g * eQueryFinal P level.queries ≤ εmax) (hεT : eTail ≤ εmax)
    (a : (WhirStateT × List E) × List E) :
    Spec (finSuffixJ μ ℓ₀ per c₀ n₀ g dir w i level a)
      (fun h ↦ ResC μ ℓ₀ w i P level.fold pre a.1 a.2 (viewC c₀ n₀ (commits h)))
      (fun _ _ ↦ False) εmax ((2 : ENNReal)⁻¹ ^ g * eQueryFinal P level.queries) 0 :=
  Spec.congr (p := (grindPre g).bind fun _ ↦
      (queryFragG g per (μ - a.1.1.folds.length + level.logInvRate) level.queries
        (cidx c₀ n₀ i)).bind fun gg ↦ finFinish μ ℓ₀ dir w i level a.1 a.2 gg.1 gg.2.1 gg.2.2)
    (by
      simp only [finSuffixJ]
      congr 1
      funext _
      exact (query_bindG' per g (cidx c₀ n₀ i) _ _ _).symm)
    ((grindPreInv (fun cs ↦ ResC μ ℓ₀ w i P level.fold pre a.1 a.2 (viewC c₀ n₀ cs)) g hεQ).bind
      fun _ ↦ finQuerySpec H hg hQlt hεT a.1 a.2)

end
end LeanVM.Protocol.Whir.Sound
