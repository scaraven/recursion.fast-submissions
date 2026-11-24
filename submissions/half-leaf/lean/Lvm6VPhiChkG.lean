-- New for lvm6 (PHF, start-up speed): `phiChk` without the table's entry list. `phiChkF` builds `P.ents` (2.9 M
-- entries as list cells and tuples), maps it to keys and folds the cancellation over it; here the cancellation and
-- the entry bounds are folded straight over the table's kinds (`PT.foldG`), the keys of `rowsKG` read from an array
-- of keys alone.
import Lvm6VPhiRowsG

/-!
# `phiChk`, fused

* `CTpl.foldG`, `AK.foldG`, **`PT.foldG`**: `P.ents.foldl` without the list (**`PT.foldG_eq`**), the powers
  `2 ^ a`, `2 ^ bb` of a class computed once.
* `CTpl.okBG`, `PT.okBG`: `okB` with the powers computed once (`rfl`).
* `findKs`, `zpassK`: `findKA`, `zpassF` on the keys `ka.map (·.2)` (**`findKs_eq`**, **`zpassK_eq`**).
* `CS`, `stepK`: one entry's bound check and cancellation step (**`foldl_stepK`**: the bounds and `cancelChkF`'s fold).
* **`phiChkG Q lay P`**; **`phiChkG_eq : phiChkG Q lay P = phiChk Q lay P`** (no hypothesis).
-/

set_option autoImplicit false

namespace Lvm6.V

open LeanVM.Parameters Lvm Lvm.E2V Lvm.Typed Lvm.Loop

/-! ## The table's entries as a fold -/

/-- `k.ents.foldl g` without the list (the templates' entries built once). -/
@[specialize] def CTpl.foldG {σ : Type} (g : σ → Q4 → σ) (k : CTpl) (s : σ) : σ :=
  let e0 := k.t0.ents
  let e1 := k.t1.ents
  let e2 := k.t2.ents
  if 64 ≤ k.a ∨ 64 ≤ k.bb then k.ents.foldl g s else
  let pa := 2 ^ k.a
  let pb := 2 ^ k.bb
  let s := foldRange (fun s j =>
    let xj := k.xb + j * pa
    let yj := k.yb + j * pb
    e0.foldl (fun s e => g s (e.1, e.2.1, xj + e.2.2.1, yj + e.2.2.2)) s) 0 k.n s
  let s := foldRange (fun s j =>
    let xj := k.xb + j * pa
    let yj := k.yb + (j - 1) * pb
    e1.foldl (fun s e => g s (e.1, e.2.1, xj + e.2.2.1, yj + e.2.2.2)) s) 1 (k.n - 1) s
  foldRange (fun s j =>
    let xj := k.xb + j * pa
    e2.foldl (fun s e => g s (e.1, e.2.1, xj + e.2.2.1, e.2.2.2)) s) 0 k.n s

theorem CTpl.foldG_eq {σ : Type} (g : σ → Q4 → σ) (k : CTpl) (s : σ) : k.foldG g s = k.ents.foldl g s := by
  unfold CTpl.foldG
  split
  · rfl
  · unfold CTpl.ents
    simp only [List.foldl_append, List.foldl_flatMap, List.foldl_map, foldRange_eq, List.range_eq_range']

/-- `k.ents.foldl g` without the list. -/
@[specialize] def AK.foldG {σ : Type} (g : σ → Q4 → σ) (k : AK) (s : σ) : σ :=
  foldRange (fun s j => k.rows.foldl (fun s r => r.2.foldl (fun s t =>
    g s (t.c, t.o, r.1 + j * 2 ^ k.a, k.wd t j)) s) s) 0 k.n s

theorem AK.foldG_eq {σ : Type} (g : σ → Q4 → σ) (k : AK) (s : σ) : k.foldG g s = k.ents.foldl g s := by
  unfold AK.foldG AK.ents AK.rowEnts
  simp only [List.foldl_flatMap, List.foldl_map, foldRange_eq, List.range_eq_range', ← Array.foldl_toList]

/-- **`P.ents.foldl g` without the list.** -/
@[specialize] def PT.foldG {σ : Type} (g : σ → Q4 → σ) (P : PT) (s : σ) : σ :=
  let s := P.cls.foldl (fun s k => k.foldG g s) s
  let s := P.ak.foldl (fun s k => k.foldG g s) s
  let s := P.str.foldl (fun s k => k.ents.foldl g s) s
  let s := P.gk.foldl (fun s k => k.ents.foldl g s) s
  let s := P.bk.foldl (fun s k => k.toCTpl.foldG g s) s
  let s := P.rest.ents.foldl g s
  P.rk.ents.foldl g s

theorem PT.foldG_eq {σ : Type} (g : σ → Q4 → σ) (P : PT) (s : σ) : P.foldG g s = P.ents.foldl g s := by
  unfold PT.foldG PT.ents PT.kents
  simp only [CTpl.foldG_eq, AK.foldG_eq, List.foldl_append, List.foldl_flatMap, ← Array.foldl_toList, BKB.ents]

/-! ## The table check with the powers hoisted -/

/-- `CTpl.okB` with `2 ^ a`, `2 ^ bb` computed once (not per template entry). -/
def CTpl.okBG (k : CTpl) : Bool :=
  let pa := 2 ^ k.a
  let pb := 2 ^ k.bb
  decide (k.a + k.L ≤ 20) && decide (k.bb + k.L ≤ 21) && decide (k.n ≤ 2 ^ k.L) &&
    k.xb % 2 ^ (k.a + k.L) == 0 && k.yb % 2 ^ (k.bb + k.L) == 0 &&
    k.t0.ents.all (fun e => decide (e.2.2.1 < pa) && decide (e.2.2.2 < pb)) &&
    k.t1.ents.all (fun e => decide (e.2.2.1 < pa) && decide (e.2.2.2 < pb)) &&
    k.t2.ents.all (fun e => decide (e.2.2.1 < pa)) && decide (1 ≤ k.bb)

theorem CTpl.okBG_eq : CTpl.okBG = CTpl.okB := rfl

/-- `PT.okB` on `CTpl.okBG`. -/
def PT.okBG (P : PT) : Bool :=
  P.cls.toList.all CTpl.okBG && (P.ak.toList.all AK.okB && P.str.toList.all SRunF.okB &&
    P.gk.toList.all GK.okB && P.bk.toList.all fun k =>
      k.toCTpl.okBG && decide (k.β ≤ k.a) && decide (k.β ≤ k.bb) && decide (k.nb ≤ 2 ^ k.β))

theorem PT.okBG_eq (P : PT) : P.okBG = P.okB := rfl

/-! ## The cancellation on the keys -/

/-- `findGo` on the keys. -/
def findGoK (ks : Array ℕ) (pos : Array ℕ) (k : ℕ) : ℕ → ℕ → Option ℕ
  | _, 0 => none
  | p, n + 1 =>
    let i := pos.getD p 0
    if decide (i < ks.size) && ks.getD i 0 == k then some i else findGoK ks pos k (p + 1) n

theorem getD_map_snd (ka : Array (FE2 × ℕ)) (i : ℕ) : (ka.map (·.2)).getD i 0 = (ka.getD i (0, 0)).2 := by
  simp only [Array.getD_eq_getD_getElem?, Array.getElem?_map]
  cases ka[i]? <;> rfl

theorem findGoK_eq (ka : Array (FE2 × ℕ)) (pos : Array ℕ) (k : ℕ) : ∀ p n,
    findGoK (ka.map (·.2)) pos k p n = findGo ka pos k p n
  | _, 0 => rfl
  | p, n + 1 => by
    unfold findGoK findGo
    simp only [Array.size_map, getD_map_snd, findGoK_eq ka pos k (p + 1) n]

/-- `findKA` on the keys. -/
@[inline] def findKs (ks : Array ℕ) (ix : SlotIx) (k : ℕ) : Option ℕ :=
  let s := slotOf k
  findGoK ks ix.pos k (ix.off.getD s 0) (ix.off.getD (s + 1) 0 - ix.off.getD s 0)

theorem findKs_eq (ka : Array (FE2 × ℕ)) (ix : SlotIx) (k : ℕ) : findKs (ka.map (·.2)) ix k = findKA ka ix k := by
  unfold findKs findKA
  rw [findGoK_eq]

/-- The fold's state: the bounds so far, the coefficients, the side list. -/
structure CS where
  ok : Bool
  D : Array FE2
  side : List (FE2 × ℕ)

/-- `zstepF` on the keys alone. -/
def zstepK (ks : Array ℕ) (ix : SlotIx) (D : Array FE2) (i : ℕ) : Array FE2 :=
  let d := D.getD i 0
  if d == 0 then D else
    match findKs ks ix (ks.getD i 0) with
    | some j => if j == i then D else (D.modify j (· + d)).modify i (fun _ => 0)
    | none => D

/-- `zpassF` on the keys alone. -/
def zpassK (ks : Array ℕ) (ix : SlotIx) (D : Array FE2) : Array FE2 :=
  foldRange (zstepK ks ix) 0 ks.size D

theorem zpassK_eq (ka : Array (FE2 × ℕ)) (ix : SlotIx) (D : Array FE2) :
    zpassK (ka.map (·.2)) ix D = zpassF ka ix D := by
  have hz : zstepK (ka.map (·.2)) ix = zstepF ka ix := by
    funext D i
    unfold zstepK zstepF
    simp only [getD_map_snd, findKs_eq]
    rfl
  unfold zpassK zpassF
  rw [hz, Array.size_map]

/-- `stepG` on the keys alone. -/
@[inline] def stepK (ks : Array ℕ) (ix : SlotIx) (st : CS) (q : Q4) : CS :=
  let ok := st.ok && (decide (q.2.1 < 4) && decide (q.2.2.1 < 2 ^ 20))
  let k := idxOf q.2.1 q.2.2.1 q.2.2.2
  match findKs ks ix k with
  | some i => ⟨ok, st.D.modify i (· - q.1), st.side⟩
  | none => ⟨ok, st.D, (q.1, k) :: st.side⟩

theorem stepK_eq (ka : Array (FE2 × ℕ)) (ix : SlotIx) (b : Bool) (D : Array FE2) (L : List (FE2 × ℕ)) (q : Q4) :
    stepK (ka.map (·.2)) ix ⟨b, D, L⟩ q =
      ⟨b && (decide (q.2.1 < 4) && decide (q.2.2.1 < 2 ^ 20)), (cancelStepF ka ix (D, L) (toIdx q)).1,
        (cancelStepF ka ix (D, L) (toIdx q)).2⟩ := by
  unfold stepK cancelStepF toIdx
  dsimp only
  rw [findKs_eq]
  cases findKA ka ix (idxOf q.2.1 q.2.2.1 q.2.2.2) <;> rfl

/-- **The fused fold is the bounds check and `cancelChkF`'s fold.** -/
theorem foldl_stepK (ka : Array (FE2 × ℕ)) (ix : SlotIx) : ∀ (pe : List Q4) (b : Bool) (D : Array FE2)
    (L : List (FE2 × ℕ)),
    pe.foldl (stepK (ka.map (·.2)) ix) ⟨b, D, L⟩ =
      ⟨b && pe.all (fun q => decide (q.2.1 < 4) && decide (q.2.2.1 < 2 ^ 20)),
        ((pe.map toIdx).foldl (cancelStepF ka ix) (D, L)).1, ((pe.map toIdx).foldl (cancelStepF ka ix) (D, L)).2⟩
  | [], b, D, L => by simp
  | q :: pe, b, D, L => by
    rw [List.foldl_cons, List.map_cons, List.foldl_cons, List.all_cons, stepK_eq, foldl_stepK ka ix pe,
      Bool.and_assoc]

/-- **`phiChk`, fused.** -/
def phiChkG (Q : Program) (lay : Lay) (P : PT) : Bool :=
  let ka := rowsKG Q lay
  let ks := ka.map (·.2)
  let ix := mkIx ka
  let st := P.foldG (stepK ks ix) ⟨true, ka.map (·.1), []⟩
  let sa := st.side.toArray
  P.okBG && st.ok && (zpassK ks ix st.D).all (· == 0) && (zpassF sa (mkIx sa) (sa.map (·.1))).all (· == 0)

/-- **`phiChkG` is `phiChk`.** -/
theorem phiChkG_eq (Q : Program) (lay : Lay) (P : PT) : phiChkG Q lay P = phiChk Q lay P := by
  rw [← phiChkF_eq]
  unfold phiChkG phiChkF cancelChkF
  rw [rowsKG_eq, ← rowsKF_eq, PT.okBG_eq]
  dsimp only
  rw [PT.foldG_eq, foldl_stepK, zpassK_eq]
  simp only [Bool.true_and, Bool.and_assoc]

end Lvm6.V
