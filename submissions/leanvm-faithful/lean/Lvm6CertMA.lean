-- New for lvm6 (WP C1 of CERT): `MAOK` at every instance map, from MA's per-phase theorems and the ring phase's
-- multiaffinity (ported from ASM's WIP `ringPhase6_retMle`, `lvm6/ASM-ma` a34c9068); then `VSF6_eq` at `P18` with no
-- multiaffinity hypothesis.
import Lvm6VGuard
import Lvm6MultiaffPhases
import Lvm6MultiaffSponge

/-!
# The multiaffinity of the deployed phases (`MAOK`)

* **`ringPhase6_ma`**: every claim the ring phase returns is multiaffine on `sh.M` variables when the stacked claims are
  (`claimOf6_mle` under `ringOK`, `multiaffine_iff_mle`).
* **`maok`**: `MAOK inst` for every instance map (`commit6_ma`, `treeProgS6_ma`, `spongePhase6_ma`,
  `typedPhase6_ma_at`, `ringPhase6_ma`); **`maok6`**: at the guard's instance `inst6 B h`.
* **`VSF6_eqP18`**: `VSF6 B P18 = VSspec6 B P18` for every base `B` (`VSF6_eq` with `hM := rfl`, `hMA := maok6 B`).
-/

set_option autoImplicit false

namespace Lvm6

open LeanVM.Parameters LeanVM.Protocol LeanVM.Protocol.Compile LeanVM.Protocol.Verifier
open LeanVM.Protocol.EndToEnd.Front LeanVM.Protocol.Whir.Sound Lvm Lvm.E2V
open Lvm6.Ring

/-- The ring phase's body returns only `claimOf6 sl st (ringOut6 cs)` for some draws `cs`. -/
theorem ringBody_retAll {Q : StackClaim6 → Prop} (g : ℕ) (sl : List SliceClaim) (st : List StackClaim6)
    (h : ∀ cs, Q (claimOf6 sl st (ringOut6 cs))) : RetAll Q (ringBody g sl st) := by
  unfold ringBody
  refine RetAll.bind ?_
  refine RetAll.of_forall (fun cs => ?_) _
  refine RetAll.bind ?_
  unfold VerifierProgram.require
  split
  · exact h cs
  · trivial

/-- **Every batched claim the ring phase returns is multiaffine** on `sh.M` variables when the stacked claims are
(W1's F-3 for §6.5; `claimOf6_mle` under `ringOK`). -/
theorem ringPhase6_ma (sh : Shape) (sl : List SliceClaim) (st : List StackClaim6)
    (hst : ∀ c ∈ st, c.Multiaffine sh.M) :
    RetAll (fun c : StackClaim6 => c.Multiaffine sh.M) (ringPhase6 sh sl st) := by
  have hst' : ∀ c ∈ st, Claim.Mle sh.M c := fun c hc => (multiaffine_iff_mle sh.M c).mp (hst c hc)
  unfold ringPhase6
  refine RetAll.bind ?_
  unfold VerifierProgram.require
  split
  · rename_i hok
    refine RetAll.bind ?_
    refine RetAll.of_forall (fun _ => ?_) _
    refine RetAll.bind ?_
    refine RetAll.of_forall (fun _ => ?_) _
    exact @ringBody_retAll (fun c : StackClaim6 => c.Multiaffine sh.M) sh.gRing sl st fun cs =>
      (multiaffine_iff_mle sh.M (claimOf6 sl st (ringOut6 cs))).mpr
        (claimOf6_mle sh.M sl st (ringOut6 cs) hok.2.2.1 hok.2.2.2 hst')
  · trivial

end Lvm6

namespace Lvm6.V

/-- **The deployed phases are multiaffine** at every instance map (the restated `MAOK`, C1). -/
theorem maok (inst : Hdr → Ty.TyInst6) : MAOK inst where
  commit := commit6_ma
  tree := treeProgS6_ma
  sponge := spongePhase6_ma
  typed := typedPhase6_ma_at inst
  ring := ringPhase6_ma

/-- **`MAOK` at the guard's instance** (`VSF6_eq`'s `hMA`), for every base `B`. -/
theorem maok6 (B : TyBase6) (h : staticOk6 B = true) : MAOK (inst6 B h) :=
  maok (inst6 B h)

/-- **The guarded fast verifier is the specified one at `P18`**, with no multiaffinity hypothesis. -/
theorem VSF6_eqP18 (B : TyBase6) : VSF6 B P18 = VSspec6 B P18 :=
  VSF6_eq B P18 rfl (maok6 B)

end Lvm6.V
