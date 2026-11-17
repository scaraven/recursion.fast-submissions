-- New for lvm (WP-14a, H2): V_S's phases 4 and 6 (`dKec`: the caller's instance point and lanes, the
-- Keccak GKR, ring switching) refine WP-8's caller program (`Lvm.KG.callerProg`) on the stream.
import LvmVEqSum
import LvmVEqRel
import LvmQKeccakConst

-- (GOLF2: 63 declarations that `certified` does not use moved verbatim to `LvmVEqTapeOff`, outside its import closure.)

-- ===== merged from `LvmVEqKecAlg` (GOLF module merge: `LvmVEqKecAlg.lean` is now a stub importing `LvmVEqKec`) =====
section
-- New for lvm (WP-14a, H2): the native Keccak GKR and ring switching (LvmDecideKeccak, over `FE`)
-- compute the verifier language's values (LvmVCore, over `E`) through `FE.toExt3`: the pure parts.

/-!
# Keccak GKR and ring switching over `E`: the arithmetic

One transport lemma per pure piece of `LvmDecideKeccak` into its `LvmVCore` twin:

* the embedding's tables (`rmfeEmbed_eq`, `rmfeProject_eq`, from `Q1.rmfe_eq_V`) and the
  constants (`slotBits_eq`, `segmentBits_eq`);
* `map_keccakInstanceWeights`, `map_keccakLinearTranspose` (the arrays mapped entry by entry),
  `kcE_keccakFirstClaim` (a claim over `E`: `kcE`), `map_keccakSlotWeights`, `map_slotFold`
  (`keccakOpen`'s fold of the rows by the slot's challenges);
* a layer's checks: `toExt3_projected`, `toExt3_iota`, and the split kernel: V_S weighs bit
  `j = 64·lane + z` by `eq_z[z] · eq_lane[lane]` where the language weighs it by
  `eqKernel localPoint` (`toExt3_weighted`, `map_layerWeights`, for an `11`-coordinate point);
* ring switching: `toExt3_phiMap`, `map_ringCoefficients`, `toExt3_ringWeight` (V_S's `FE.frob k`
  and `FE.sq` are the language's `^ (2^k)` and `^ 2`).
-/

set_option autoImplicit false

namespace Lvm.VEq

open LeanVM.Parameters LeanVM.Protocol Finset
open Lvm.M3 (tE_add tE_mul tE_zero tE_one)
open LeanVM.Protocol.KeccakGkr (eqAt eqAt_append eqAt_mod eqKernel_getD eqKernel_length)

/-! ## Constants -/

/-! ## Lists and arrays -/

theorem getD_map_range {α : Type} (n i : ℕ) (f : ℕ → α) (d : α) (h : i < n) :
    ((List.range n).map f).getD i d = f i := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range h]
  rfl

/-! ## Claims over `E` -/

/-! ## The embedding's weights and the linear map -/

/-! ## The openings -/

/-! ## Ring switching -/

/-! ## A layer -/

end Lvm.VEq
end
-- ===== end of `LvmVEqKecAlg` =====

/-!
# The Keccak GKR and ring switching: V_S refines the verifier language

`Lvm.keccakPackRounds`, `verifyKeccakLayer`, `keccakLayers`, `keccakOpen`, `verifyKeccak`,
`ringSwitch` (over `FE`, on the reader `DM`) refine their `LvmVCore` twins (over `E`) wherever V_S's
checks hold (`RefAt`), generic in the commitment table `cap shp` and the stream `sig`; values are
related by `FE.toExt3` (a claim by `kcE`, `verifyKeccak`'s output by `koE`), the pure parts by
`LvmVEqKecAlg`. The language's `verifyKeccak` branches on `1 < keccakSegments`, which holds
(`keccakSegments = 2`); its committed-output block is reassociated (`bind_assoc`) to V_S's
straight line. Each native function never clears a failed check (`MonoD`).

Headline: **`ref_dKec h`**, V_S's `dKec h` refines `Lvm.KG.callerProg h` with `KecRel h`, and
**`keccakClaims_rel`**: related outputs give related block claims (`BCRel`).
-/

set_option autoImplicit false

namespace Lvm.VEq

open Lvm DM LeanVM.Parameters LeanVM.Protocol LeanVM.Protocol.Compile
open Lvm.M3 (tE_add tE_mul tE_zero tE_one FE_eq_of_beq)

/-! ## Returns of native steps -/

/-- Every value the native step returns satisfies `Q`. -/
def RetD {β : Type} (Q : β → Prop) (d : DM β) : Prop := ∀ sig s, Q (runD d sig s).1

theorem RetD.bind {β β' : Type} {Q' : β → Prop} {Q : β' → Prop} {d : DM β} {d' : β → DM β'}
    (h : RetD Q' d) (h' : ∀ b, Q' b → RetD Q (d' b)) : RetD Q (d >>= d') :=
  fun sig s ↦ h' _ (h sig s) sig _

theorem RetD.bind_true {β β' : Type} {Q : β' → Prop} {d : DM β} {d' : β → DM β'}
    (h' : ∀ b, RetD Q (d' b)) : RetD Q (d >>= d') :=
  fun sig _ ↦ h' _ sig _

theorem RetD.pure {β : Type} {Q : β → Prop} {b : β} (h : Q b) : RetD Q (Pure.pure b : DM β) :=
  fun _ _ ↦ h

theorem retD_samples : ∀ n, RetD (fun xs : List FE ↦ xs.length = n) (DM.samples n)
  | 0 => RetD.pure rfl
  | n + 1 => RetD.bind_true fun _ ↦ (retD_samples n).bind fun _ h ↦ RetD.pure (by simp [h])

theorem retD_sumcheck (count : ℕ) : ∀ (eqs : List (Option FE)) (claim : FE),
    RetD (fun r : List FE × FE ↦ r.1.length = eqs.length) (Lvm.sumcheck claim count eqs)
  | [], _ => RetD.pure rfl
  | _ :: eqs, _ => RetD.bind_true fun _ ↦ RetD.bind_true fun _ ↦
      (retD_sumcheck count eqs _).bind fun ⟨_, _⟩ h ↦ RetD.pure (by simp [h])

/-- A refinement with a fact on the native value. -/
theorem RefAt.retD {cap : ℕ → ℕ → ℕ} {occ : ℕ → ℕ → ℕ} {shp : ℕ → ℕ × ℕ} {sig : ByteArray} {α β : Type} {d : DM β}
    {P : VerifierProgram α} {R : β → α → Prop} {Q : β → Prop} (h : RefAt cap occ shp sig d P R)
    (hq : RetD Q d) : RefAt cap occ shp sig d P fun b a ↦ R b a ∧ Q b := fun s hok ↦ by
  obtain ⟨a, h1, h2, h3, h4⟩ := h s hok
  exact ⟨a, h1, h2, h3, h4, hq sig s⟩

/-! ## Checks over `E` -/

/-! ## `MonoD` -/

/-! ## Refinement -/

section Ref

variable {cap : ℕ → ℕ → ℕ} {occ : ℕ → ℕ → ℕ} {shp : ℕ → ℕ × ℕ} {sig : ByteArray}

end Ref

end Lvm.VEq
