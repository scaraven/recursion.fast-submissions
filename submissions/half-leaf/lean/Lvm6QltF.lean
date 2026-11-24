-- New for lvm6 (SU2, start-up): `qltData6`'s fast twin. `qltEntries6` reads `eLane6 P i` (a prefix sum of the plan's
-- lengths) and `P.getD st` per entry, so it is quadratic in the plan (≈ 4,350 entries: ≈ 250 ms); the padding
-- recomputed `qltEntries6` for its length. Additive: no definition or statement changes.
import Lvm6QLink

/-!
# `qltData6F` (SU2)

* **`offsL P a`**: the entries' byte offsets from `a` (`a`, `a + 40 + len₀`, …), one pass; **`offsL_getD`**:
  entry `min i |P|` is `a + slenS ((lens6 P).take i)`, so `eLane6`/`ansLane6` are lookups (`eLaneF_eq`, `ansLaneF_eq`).
* **`qltEntries6F P lay`** (one prefix-sum array, the plan as an array, the hashed length once);
  **`qltEntries6F_eq`**: it is `qltEntries6 P lay`, for every plan and layout.
* **`qltData6F P lay`**; **`qltData6F_eq : qltData6F P lay = qltData6 P lay`**.
-/

set_option autoImplicit false

namespace Lvm6.Q

open RecursionFast Lvm Lvm.Replay Lvm.QLink Lvm.Loop Lvm.Loop.Build

/-- The byte offsets of the plan's entries from `a` (the last one past the plan). -/
def offsL : List PE6 → ℕ → List ℕ
  | [], a => [a]
  | e :: es, a => a :: offsL es (a + 40 + e.len)

theorem offsL_getD : ∀ (P : List PE6) (a i : ℕ),
    (offsL P a).getD (min i P.length) 0 = a + slenS ((lens6 P).take i)
  | [], a, i => by simp [offsL, lens6, slenS]
  | e :: es, a, 0 => by simp [offsL, slenS]
  | e :: es, a, i + 1 => by
    have h : min (i + 1) (e :: es).length = min i es.length + 1 := by simp [Nat.add_min_add_right]
    rw [h, offsL, List.getD_cons_succ, offsL_getD es]
    simp only [lens6, List.map_cons, List.take_succ_cons, slenS, List.sum_cons]
    omega

/-- `eLane6` off the offsets array `A` (`n` entries). -/
def eLaneF (A : Array ℕ) (n i : ℕ) : ℕ := A.getD (min i n) 0 / 8

/-- `ansLane6` off the offsets array and the plan as an array. -/
def ansLaneF (A : Array ℕ) (PA : Array PE6) (n i : ℕ) : ℕ :=
  if i = 0 then 2 else eLaneF A n i + 1 + (PA.getD i default).len / 8

theorem eLaneF_eq (P : List PE6) (i : ℕ) : eLaneF (offsL P 1).toArray P.length i = eLane6 P i := by
  rw [eLaneF, Array.getD_eq_getD_getElem?, List.getElem?_toArray, ← List.getD_eq_getElem?_getD, offsL_getD]
  rfl

theorem ansLaneF_eq (P : List PE6) (i : ℕ) : ansLaneF (offsL P 1).toArray P.toArray P.length i = ansLane6 P i := by
  rw [ansLaneF, eLaneF_eq, Array.getD_eq_getD_getElem?, List.getElem?_toArray, ← List.getD_eq_getElem?_getD]
  rfl

/-- **`qltEntries6`, fast**: the offsets once, the plan as an array, the hashed length once. -/
def qltEntries6F (P : List PE6) (lay : Layout6) : List (ℕ × ℕ × ℕ) :=
  let A := (offsL P 1).toArray
  let PA := P.toArray
  let n := P.length
  let H := hashedLen6 P
  [(lay.sb, lay.sb + 1, lane0C), (lay.sb + 1, lay.sb + 2, lane1C6)] ++
  (P.zipIdx.filterMap fun x => match x.1.k with
    | .fs st _ => some (lay.sb + eLaneF A n x.2, lay.sb + ansLaneF A PA n st, x.1.len)
    | .seed => some (lay.sb + eLaneF A n x.2, lay.sb + ansLaneF A PA n 0, x.1.len)
    | _ => none) ++
  ((List.range (17 * nBlk H - H / 8)).map fun k =>
    let q := H / 8 + k
    (lay.sb + q, lay.sb + q + 1, padLane H q))

theorem qltEntries6F_eq (P : List PE6) (lay : Layout6) : qltEntries6F P lay = qltEntries6 P lay := by
  simp only [qltEntries6F, qltEntries6, ansLaneF_eq, eLaneF_eq]
  rfl

/-- **`qltData6`, fast** (`qltEntries6F` once). -/
def qltData6F (P : List PE6) (lay : Layout6) : List FK :=
  let E := qltEntries6F P lay
  tblOf (E ++ List.replicate (2 ^ lay.aQ - E.length) (lay.sb, lay.sb + 1, lane0C))

theorem qltData6F_eq (P : List PE6) (lay : Layout6) : qltData6F P lay = qltData6 P lay := by
  simp only [qltData6F, qltData6, qltPadded6, qltEntries6F_eq]

end Lvm6.Q
