-- New for lvm2 E2F (slice S1, E2F-QH2): the pin's claim cells are V's (`LvmDecideE2.pinD`): on a memory where the
-- stream cells are `Σ`'s lanes and `pinG`'s rows hold, its claim is the claim V reads.
import LvmE2QPin
import LvmQLinkArithRead
import LvmDecideE2

/-!
# The pin's semantics (`pin_replays`)

* `hs_loadLane`: a `loadE` of three stream lanes is `F`'s scalar there; `hs_mapBC`: `mapB` of cell gadgets;
* `pinD_run`: V's `pinD ν` from a cursor at position `P` reads the answers at `P + 40 + 72 k` and the value at
  `P + 72 ν + 40`;
* **`pin_replays`**: with `8 qz = P + 40` and `qa = qz + 9 ν`, `pinG ν qz qa`'s claim is `(.main, pinD's claim)`.
-/

set_option autoImplicit false

namespace Lvm.Q2

open Lvm Lvm.Loop Lvm.Loop.Build Lvm.Har Lvm.Q1 DM

variable {c : Ctx} {M : Mem}

theorem hs_loadLane {sig : ByteArray} {T : Nat} (hS : Streamed M sig T) {q : Nat} (hq : q + 2 < T) :
    Hs c M (loadE (kc q) (kc (q + 1)) (kc (q + 2))) (fun r => r.val M = feAt sig (8 * q)) := fun p h => by
  have e := Lvm.Loop.Build.loadE_spec h
  show Cell.val M _ = _
  rw [e, Cell.val_K, Cell.val_K, Cell.val_K]
  exact load_feAt hS hq

theorem hs_mapBC {α : Type} (f : α → BM Cell) (g : α → FE) :
    ∀ l : List α, (∀ a ∈ l, Hs c M (f a) (fun r => r.val M = g a)) →
      Hs c M (mapB f l) (fun rs => rs.map (Cell.val M) = l.map g)
  | [], _ => hs_pure rfl
  | a :: l, hf => hs_bind (hf a (List.mem_cons_self ..)) fun r hr =>
    hs_bind (hs_mapBC f g l fun b hb => hf b (List.mem_cons_of_mem _ hb)) fun rs hrs =>
    hs_pure (by rw [List.map_cons, List.map_cons, hr, hrs])

/-- **The pin's cells** hold the stream's scalars at the answer lanes `qz + 9 k` and the value lanes `qa`. -/
theorem pinG_spec {sig : ByteArray} {T : Nat} (hS : Streamed M sig T) {nu qz qa : Nat}
    (hz : qz + 9 * nu + 2 < T) (ha : qa + 2 < T) :
    Hs c M (pinG nu qz qa) (fun cc => cc.val M =
      (.main, BlockClaim.point ⟨nu, 0⟩ ((List.range nu).map fun k => feAt sig (8 * (qz + 9 * k)))
        (feAt sig (8 * qa)))) :=
  hs_bind (hs_mapBC _ (fun k => feAt sig (8 * (qz + 9 * k))) (List.range nu)
      fun k hk => hs_loadLane hS (by have := List.mem_range.mp hk; omega)) fun z hz' =>
    hs_bind (hs_loadLane hS ha) fun a ha' => hs_pure (by
      simp only [CClaim.val, vs, hz', ha'])

/-- **V's `pinD ν`** from a cursor `s`: the answers at `P + 40 + 72 k`, the value at `P + 72 ν + 40`
(`P = s.ent + s.msg`). -/
theorem pinD_run (sig : ByteArray) (s : RS) {nu : Nat} (hn : 1 ≤ nu) :
    (pinD nu sig s).1 = BlockClaim.point ⟨nu, 0⟩
      ((List.range nu).map fun i => feAt sig (s.ent + s.msg + 40 + 72 * i)) (feAt sig (s.ent + s.msg + 72 * nu + 40)) := by
  show (let r := samples nu sig s; let r2 := readE sig r.2; BlockClaim.point ⟨nu, 0⟩ r.1 r2.1) = _
  simp only [samples_run sig nu s hn, readE_run, Nat.add_zero]

/-- **The pin replays V's `pinD`**: with the first answer at lane `qz` (`8 qz = P + 40`) and the value at
`qa = qz + 9 ν`, the circuit's pin claim is V's. -/
theorem pin_replays {sig : ByteArray} {T : Nat} (hS : Streamed M sig T) (s : RS) {nu qz qa : Nat} (hn : 1 ≤ nu)
    (hP : 8 * qz = s.ent + s.msg + 40) (hqa : qa = qz + 9 * nu) (hz : qz + 9 * nu + 2 < T) (ha : qa + 2 < T) :
    Hs c M (pinG nu qz qa) (fun cc => cc.val M = (.main, (pinD nu sig s).1)) :=
  hs_mono (pinG_spec hS hz ha) fun cc h => by
    rw [h, pinD_run sig s hn]
    congr 3
    · funext k; congr 1; omega
    · congr 1; omega

end Lvm.Q2
