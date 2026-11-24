-- New for lvm6 (WP-V1b): fast twin of the sponge caller (`spCaller6 h`: `h` ground coordinates, 25 scalars, the
-- sponge core = reduction head at slots `25m + ℓ` and the sponge's input end).
import Lvm6VTwH

/-!
# Fast twins: the sponge caller

* `fE2Samples`, `tw_e2Samples`; **`fSpongeCore6`**, **`tw_spongeCore6`**; **`fSpCaller6`**, **`tw_spCaller6`**.
-/

set_option autoImplicit false

namespace Lvm6.V

open RecursionFast LeanVM.Parameters Lvm.FS Lvm.Replay Lvm Lvm.E2V
open LeanVM.Protocol.Compile hiding Proof Bytes Word

/-- Fast `e2Samples g n`. -/
def fE2Samples (g : ℕ) : ℕ → VF (List FE2)
  | 0 => VF.pure []
  | n + 1 => VF.bind (fE2Sample g) fun x => VF.bind (fE2Samples g n) fun xs => VF.pure (x :: xs)

theorem tw_e2Samples (g : ℕ) : ∀ n, TwinF (List.map FE2.toE2) (e2Samples g n) (fE2Samples g n)
  | 0 => tw_pure rfl
  | n + 1 => tw_bind (f := fun x => e2Samples g n >>= fun xs => pure (x :: xs)) (tw_e2Sample g) fun x =>
      tw_bind (tw_e2Samples g n) fun xs => tw_pure rfl

/-- **Fast `spongeCore6 P inst output`.** -/
def fSpongeCore6 (P : ℕ) (inst output : List FE2) : VF (HeadOutF × EndOutF) :=
  VF.bind (fKHead6 P 25 inst output) fun hd =>
  VF.bind (fSpongeEnd6 P (toKF hd.claim)) fun en => VF.pure (hd, en)

/-- The decoding of the core's value. -/
def coreD (r : HeadOutF × EndOutF) : Lvm6.K.HeadOut × Lvm6.K.EndOut := (r.1.dec, r.2.dec)

theorem tw_spongeCore6 (P : ℕ) (inst output : List FE2) :
    TwinF coreD (Lvm6.K.spongeCore6 P (inst.map FE2.toE2) (output.map FE2.toE2)) (fSpongeCore6 P inst output) := by
  unfold Lvm6.K.spongeCore6
  refine tw_bind (tw_kHead6 _ _ _ _) fun hd => ?_
  rw [show (HeadOutF.dec hd).claim = (toKF hd.claim).dec from (toKF_dec _).symm]
  exact tw_bind (tw_spongeEnd6 _ _) fun en => tw_pure rfl

/-- **Fast `spCaller6 h`.** -/
def fSpCaller6 (h : ℕ) : VF (List FE2 × List FE2 × (HeadOutF × EndOutF)) :=
  VF.bind (fE2Samples gC1 h) fun r =>
  VF.bind (fE2Reads 25) fun v =>
  VF.bind (fSpongeCore6 (h - 4) r v) fun res => VF.pure (r, v, res)

/-- The decoding of the caller's value. -/
def spD (r : List FE2 × List FE2 × (HeadOutF × EndOutF)) : Lvm6.K.SpOut :=
  (r.1.map FE2.toE2, r.2.1.map FE2.toE2, coreD r.2.2)

theorem tw_spCaller6 (h : ℕ) : TwinF spD (Lvm6.K.spCaller6 h) (fSpCaller6 h) := by
  unfold Lvm6.K.spCaller6
  exact tw_bind (tw_e2Samples _ _) fun r => tw_bind (tw_e2Reads 25) fun v =>
    tw_bind (tw_spongeCore6 _ _ _) fun res => tw_pure rfl

end Lvm6.V
