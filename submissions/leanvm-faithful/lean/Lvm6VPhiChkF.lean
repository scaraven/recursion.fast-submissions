-- New for lvm6 (ST-6, start-up speed): `phiChk`'s fast twin. `findK` builds the slot's candidate list per lookup
-- and `zpass` folds over `List.range`; here both are loops over the index arrays. With `rowsKF` (`Lvm6VPhiRowsF`),
-- `phiChkF` is `phiChk` (`phiChkF_eq`), so the guard calls `phiChkF` and its facts are `phiChk`'s.
import Lvm6VPhiRowsF

/-!
# `phiChk`, fast

* `findGo`, `findKA`: `findK` as a loop; **`findKA_eq`**.
* `foldRange`: `(List.range' i n).foldl` as a loop; **`foldRange_eq`**.
* `cancelStepF`, `zstepF`, `zpassF`, **`cancelChkF`**: `cancelChk`'s text on them; **`cancelChkF_eq`**.
* **`phiChkF Q lay P`**: `phiChk` on `rowsKF` and `cancelChkF`; **`phiChkF_eq : phiChkF Q lay P = phiChk Q lay P`**.
-/

set_option autoImplicit false

namespace Lvm6.V

open LeanVM.Parameters Lvm Lvm.E2V Lvm.Typed Lvm.Loop

/-- The candidates `pos[p], …, pos[p + n - 1]` scanned for key `k`. -/
def findGo (ka : Array (FE2 × ℕ)) (pos : Array ℕ) (k : ℕ) : ℕ → ℕ → Option ℕ
  | _, 0 => none
  | p, n + 1 =>
    let i := pos.getD p 0
    if decide (i < ka.size) && (ka.getD i (0, 0)).2 == k then some i else findGo ka pos k (p + 1) n

theorem findGo_eq (ka : Array (FE2 × ℕ)) (pos : Array ℕ) (k : ℕ) : ∀ p n,
    findGo ka pos k p n =
      ((List.range' p n).map fun q => pos.getD q 0).find? fun i => decide (i < ka.size) && (ka.getD i (0, 0)).2 == k
  | _, 0 => rfl
  | p, n + 1 => by
    rw [List.range'_succ, List.map_cons, List.find?_cons, findGo, findGo_eq ka pos k (p + 1) n]
    cases (decide (pos.getD p 0 < ka.size) && (ka.getD (pos.getD p 0) (0, 0)).2 == k) <;> rfl

/-- **`findK` as a loop.** -/
def findKA (ka : Array (FE2 × ℕ)) (ix : SlotIx) (k : ℕ) : Option ℕ :=
  let s := slotOf k
  findGo ka ix.pos k (ix.off.getD s 0) (ix.off.getD (s + 1) 0 - ix.off.getD s 0)

theorem findKA_eq (ka : Array (FE2 × ℕ)) (ix : SlotIx) (k : ℕ) : findKA ka ix k = findK ka ix k := by
  unfold findKA findK SlotIx.cands
  rw [findGo_eq]

/-- `(List.range' i n).foldl f b` as a loop. -/
def foldRange {β : Type} (f : β → ℕ → β) : ℕ → ℕ → β → β
  | _, 0, b => b
  | i, n + 1, b => foldRange f (i + 1) n (f b i)

theorem foldRange_eq {β : Type} (f : β → ℕ → β) : ∀ i n b, foldRange f i n b = (List.range' i n).foldl f b
  | _, 0, _ => rfl
  | i, n + 1, b => by rw [List.range'_succ, List.foldl_cons, foldRange, foldRange_eq f (i + 1) n]

/-- `cancelStep` on `findKA`. -/
def cancelStepF (ka : Array (FE2 × ℕ)) (ix : SlotIx) (st : Array FE2 × List (FE2 × ℕ)) (p : FE2 × ℕ) :
    Array FE2 × List (FE2 × ℕ) :=
  match findKA ka ix p.2 with
  | some i => (st.1.modify i (· - p.1), st.2)
  | none => (st.1, p :: st.2)

/-- `zstep` on `findKA`. -/
def zstepF (ka : Array (FE2 × ℕ)) (ix : SlotIx) (D : Array FE2) (i : ℕ) : Array FE2 :=
  let d := D.getD i 0
  if d == 0 then D else
    match findKA ka ix (ka.getD i (0, 0)).2 with
    | some j => if j == i then D else (D.modify j (· + d)).modify i (fun _ => 0)
    | none => D

/-- `zpass` as a loop on `zstepF`. -/
def zpassF (ka : Array (FE2 × ℕ)) (ix : SlotIx) (D : Array FE2) : Array FE2 :=
  foldRange (zstepF ka ix) 0 ka.size D

/-- **`cancelChk`, fast.** -/
def cancelChkF (ka : Array (FE2 × ℕ)) (ix : SlotIx) (pe : List (FE2 × ℕ)) : Bool :=
  let st := pe.foldl (cancelStepF ka ix) (ka.map (·.1), [])
  let sa := st.2.toArray
  (zpassF ka ix st.1).all (· == 0) && (zpassF sa (mkIx sa) (sa.map (·.1))).all (· == 0)

theorem cancelStepF_eq (ka : Array (FE2 × ℕ)) (ix : SlotIx) : cancelStepF ka ix = cancelStep ka ix := by
  funext st p
  unfold cancelStepF cancelStep
  rw [findKA_eq]
  rfl

theorem zpassF_eq (ka : Array (FE2 × ℕ)) (ix : SlotIx) (D : Array FE2) : zpassF ka ix D = zpass ka ix D := by
  have hz : zstepF ka ix = zstep ka ix := by
    funext D i
    unfold zstepF zstep
    rw [findKA_eq]
    rfl
  unfold zpassF zpass
  rw [foldRange_eq, hz, List.range_eq_range']

theorem cancelChkF_eq (ka : Array (FE2 × ℕ)) (ix : SlotIx) (pe : List (FE2 × ℕ)) :
    cancelChkF ka ix pe = cancelChk ka ix pe := by
  unfold cancelChkF cancelChk
  simp only [cancelStepF_eq, zpassF_eq]

/-- **`phiChk`, fast**: `rowsKF` and `cancelChkF`. -/
def phiChkF (Q : Program) (lay : Lay) (P : PT) : Bool :=
  let ka := rowsKF Q lay
  let pe := P.ents
  P.okB && pe.all (fun q => decide (q.2.1 < 4) && decide (q.2.2.1 < 2 ^ 20)) && cancelChkF ka (mkIx ka) (pe.map toIdx)

theorem phiChkF_eq (Q : Program) (lay : Lay) (P : PT) : phiChkF Q lay P = phiChk Q lay P := by
  unfold phiChkF phiChk
  simp only [rowsKF_eq, cancelChkF_eq]

end Lvm6.V
