-- New for lvm6 (ST-6, start-up speed): array twins of LAY4's bisection entry functions (`Lvm6FLB`). `slotWordB`
-- reads a block's result chunks with `List.getD` and `auxEntsB` an auxiliary block's rows with `List.getD` on the
-- auxiliary-block list, once per cell or row instance (59% of `rowsK`'s pass in a stack sample); here both are
-- arrays built once (`AC.of`). The text is `Lvm6FLB`'s otherwise.
import Lvm6FLB

/-!
# The entry functions on arrays

* **`AC`**, `AC.of F`: the blocks' `K`/`E` result chunks and the auxiliary blocks' rows as arrays.
* `chainB`, `sortedL`, **`SC.okBL`**, **`SC.okBL_okB`**: `SC.okB` in one pass per table (adjacent pairs; the order is
  transitive on well-formed intervals).
* `slotRA` (**`slotRA_eq`**), `slotWordA`, `wordCA`, `wordKFA`, `wordE3A`, `cellEntsFA`, `rowEntsA`, **`rowEntsXA`**, **`auxEntsA`**: `Lvm6FLB`'s
  twins with those reads from `AC`; **`rowEntsXA_eq`**, **`auxEntsA_eq`**: equal to `rowEntsXB`, `auxEntsB` (no
  hypothesis).
-/

set_option autoImplicit false

namespace Lvm.Typed.K

open Lvm.Loop

/-- The array caches of the entry functions. -/
structure AC where
  /-- Per block, `BLay.chK` as an array. -/
  chK : Array (Array RChunk)
  /-- Per block, `BLay.chE` as an array. -/
  chE : Array (Array RChunk)
  /-- Per auxiliary block, its rows as an array. -/
  aux : Array (Array ARow)

/-- **The caches of `F`.** -/
def AC.of (F : FL) : AC :=
  ⟨F.bl.map fun B ↦ B.chK.toArray, F.bl.map fun B ↦ B.chE.toArray, F.lay.aux.toArray.map fun A ↦ A.rows.toArray⟩

theorem getD_toArray {α : Type} [Inhabited α] (l : List α) (i : ℕ) : l.toArray.getD i default = l.getD i default := by
  simp [Array.getD_eq_getD_getElem?, List.getD_eq_getElem?_getD]

theorem getD_map_toArray {β γ : Type} [Inhabited β] [Inhabited γ] (A : Array β) (g : β → List γ) (hg : g default = [])
    (b : ℕ) : (A.map fun x ↦ (g x).toArray).getD b #[] = (g (A.getD b default)).toArray := by
  simp only [Array.getD_eq_getD_getElem?, Array.getElem?_map]
  cases A[b]? <;> simp [hg]

theorem chA_getD (F : FL) (τ : Ty) (b i : ℕ) :
    ((match τ with | .K => (AC.of F).chK | .E => (AC.of F).chE).getD b #[]).getD i default =
      ((F.bl.getD b default).ch τ).getD i default := by
  cases τ
  · show ((F.bl.map fun B ↦ B.chK.toArray).getD b #[]).getD i default = _
    rw [getD_map_toArray F.bl BLay.chK rfl, getD_toArray]; rfl
  · show ((F.bl.map fun B ↦ B.chE.toArray).getD b #[]).getD i default = _
    rw [getD_map_toArray F.bl BLay.chE rfl, getD_toArray]; rfl

theorem auxA_getD (F : FL) (k r : ℕ) :
    ((AC.of F).aux.getD k #[]).getD r default = ((F.lay.aux.getD k default).rows.getD r default) := by
  show ((F.lay.aux.toArray.map fun A ↦ A.rows.toArray).getD k #[]).getD r default = _
  rw [getD_map_toArray F.lay.aux.toArray ABlk.rows rfl, getD_toArray, getD_toArray]

/-! ## The table check in one pass -/

/-- Adjacent intervals in order, each well formed (one pass; `sortedB` compares every pair). -/
def chainB : List (ℕ × ℕ × ℕ) → Bool
  | x :: y :: l => decide (x.1 ≤ x.2.1) && decide (x.2.1 ≤ y.1) && chainB (y :: l)
  | [x] => decide (x.1 ≤ x.2.1)
  | [] => true

theorem chainB_wf {x : ℕ × ℕ × ℕ} {l : List (ℕ × ℕ × ℕ)} (h : chainB (x :: l) = true) : x.1 ≤ x.2.1 := by
  cases l with
  | nil => simpa [chainB] using h
  | cons y l => simp only [chainB, Bool.and_eq_true, decide_eq_true_eq] at h; exact h.1.1

theorem chainB_tail {x : ℕ × ℕ × ℕ} {l : List (ℕ × ℕ × ℕ)} (h : chainB (x :: l) = true) : chainB l = true := by
  cases l with
  | nil => rfl
  | cons y l => simp only [chainB, Bool.and_eq_true] at h; exact h.2

theorem chainB_head : ∀ (x : ℕ × ℕ × ℕ) (l : List (ℕ × ℕ × ℕ)), chainB (x :: l) = true → ∀ z ∈ l, x.2.1 ≤ z.1
  | _, [], _, _, hz => by simp at hz
  | x, y :: l, h, z, hz => by
    have h' := h
    simp only [chainB, Bool.and_eq_true, decide_eq_true_eq] at h'
    rcases List.mem_cons.1 hz with rfl | hz
    · exact h'.1.2
    · exact h'.1.2.trans ((chainB_wf h'.2).trans (chainB_head y l h'.2 z hz))

theorem chainB_pairwise : ∀ l : List (ℕ × ℕ × ℕ), chainB l = true → l.Pairwise fun x y ↦ x.2.1 ≤ y.1
  | [], _ => List.Pairwise.nil
  | x :: l, h => List.Pairwise.cons (chainB_head x l h) (chainB_pairwise l (chainB_tail h))

/-- `sortedB` in one pass. -/
def sortedL (a : Array (ℕ × ℕ × ℕ)) : Bool := chainB a.toList

theorem sortedL_sortedB (a : Array (ℕ × ℕ × ℕ)) (h : sortedL a = true) : sortedB a = true := by
  unfold sortedB
  exact decide_eq_true (chainB_pairwise _ h)

/-- **`SC.okB` in one pass per table.** -/
def SC.okBL (C : SC) : Bool := C.xt.all sortedL && C.kt.all sortedL && C.et.all sortedL

theorem all_sortedL {A : Array (Array (ℕ × ℕ × ℕ))} (h : A.all sortedL = true) : A.all sortedB = true := by
  rw [Array.all_eq_true] at h ⊢
  exact fun i hi ↦ sortedL_sortedB _ (h i hi)

theorem SC.okBL_okB {C : SC} (h : C.okBL = true) : C.okB = true := by
  simp only [SC.okBL, SC.okB, Bool.and_eq_true] at h ⊢
  exact ⟨⟨all_sortedL h.1.1, all_sortedL h.1.2⟩, all_sortedL h.2⟩

/-! ## The searches and entries on arrays -/

/-- `slotRB` reading the chunk array directly (`slotRB` converts it to a list per call). -/
def slotRA (C : SC) (F : FL) (b r jf : ℕ) : ℕ :=
  match bsI (C.xt.getD b #[]) r with
  | some i =>
    let c := (F.xch.getD b #[]).getD i default
    c.base + (r - c.r0) * 2 ^ c.l + jf
  | none => 0

theorem slotRA_eq (C : SC) (F : FL) (b r jf : ℕ) : slotRA C F b r jf = slotRB C F b r jf := by
  unfold slotRA slotRB
  simp only [Array.getD_eq_getD_getElem?, List.getD_eq_getElem?_getD, Array.getElem?_toList]
  rfl

/-- `slotWordB` with the chunks from `AC`. -/
def slotWordA (A : AC) (C : SC) (F : FL) (b : ℕ) (τ : Ty) (s jf m : ℕ) : ℕ :=
  let B := F.bl.getD b default
  match bsI ((match τ with | .K => C.kt | .E => C.et).getD b #[]) s with
  | some i =>
    let c := ((match τ with | .K => A.chK | .E => A.chE).getD b #[]).getD i default
    c.bases.getD m 0 + (s - c.s0) * 2 ^ B.l + jf
  | none => 0

theorem slotWordA_eq (C : SC) (F : FL) (b : ℕ) (τ : Ty) (s jf m : ℕ) :
    slotWordA (AC.of F) C F b τ s jf m = slotWordB C F b τ s jf m := by
  unfold slotWordA slotWordB
  simp only [chA_getD]
  rfl

/-- `wordCB` on `slotWordA`. -/
def wordCA (A : AC) (C : SC) (F : FL) (b : ℕ) (τ : Ty) (n s jf m : ℕ) : ℕ :=
  match F.dreg τ n with
  | some d => d.word n m
  | none => slotWordA A C F b τ s jf m

theorem wordCA_eq (C : SC) (F : FL) (b : ℕ) (τ : Ty) (n s jf m : ℕ) :
    wordCA (AC.of F) C F b τ n s jf m = wordCB C F b τ n s jf m := by
  unfold wordCA wordCB
  simp only [slotWordA_eq]
  rfl

/-- `wordKFB` on `wordCA`. -/
def wordKFA (A : AC) (C : SC) (F : FL) (n : ℕ) : ℕ :=
  match F.ownerF .K n with
  | some b =>
    let B := F.bl.getD b default
    let off := n - B.stK
    match (F.srcKA.getD b #[]).getD (off % B.twK) default with
    | .slot s => wordCA A C F b .K n s (off / B.twK) 0
    | .alias tgt => F.wordD .K (tgt.getD (off / B.twK) 0) 0
    | .load _ => 0
  | none => F.wordD .K n 0

theorem wordKFA_eq (C : SC) (F : FL) (n : ℕ) : wordKFA (AC.of F) C F n = wordKFB C F n := by
  unfold wordKFA wordKFB
  simp only [wordCA_eq]
  rfl

/-- `wordE3B` on `wordCA`, `wordKFA`. -/
def wordE3A (A : AC) (C : SC) (F : FL) (n : ℕ) : ℕ × ℕ × ℕ :=
  match F.ownerF .E n with
  | some b =>
    let B := F.bl.getD b default
    let off := n - B.stE
    match (F.srcEA.getD b #[]).getD (off % B.twE) default with
    | .slot s => (wordCA A C F b .E n s (off / B.twE) 0, wordCA A C F b .E n s (off / B.twE) 1,
        wordCA A C F b .E n s (off / B.twE) 2)
    | .load args =>
      let j := unflat B.dims (off / B.twE)
      (wordKFA A C F ((args.getD 0 default).at j), wordKFA A C F ((args.getD 1 default).at j),
        wordKFA A C F ((args.getD 2 default).at j))
    | .alias _ => (0, 0, 0)
  | none => (F.wordD .E n 0, F.wordD .E n 1, F.wordD .E n 2)

theorem wordE3A_eq (C : SC) (F : FL) (n : ℕ) : wordE3A (AC.of F) C F n = wordE3B C F n := by
  unfold wordE3A wordE3B
  simp only [wordCA_eq, wordKFA_eq]
  rfl

/-- `cellEntsFB` on `wordKFA`, `wordE3A`. -/
def cellEntsFA (A : AC) (C : SC) (F : FL) (τ : Ty) (n : ℕ) (w : FE) : List (ℕ × FE) :=
  match τ with
  | .K => match F.cst n with
    | some v => [(F.lay.one, w * FE.ofK v)]
    | none => [(wordKFA A C F n, w)]
  | .E =>
    let ws := wordE3A A C F n
    let wy := w * FE.y
    [(ws.1, w), (ws.2.1, wy), (ws.2.2, wy * FE.y)]

theorem cellEntsFA_eq (C : SC) (F : FL) (τ : Ty) (n : ℕ) (w : FE) :
    cellEntsFA (AC.of F) C F τ n w = cellEntsFB C F τ n w := by
  unfold cellEntsFA cellEntsFB
  simp only [wordKFA_eq, wordE3A_eq]
  rfl

/-- `rowEntsB` on `cellEntsFA`. -/
def rowEntsA (A : AC) (C : SC) (G : FLF) (b t jf : ℕ) : List Ent :=
  let F := G.F
  let Bq := F.qb.getD b default
  let row := (F.tpls.getD b #[]).getD t default
  let j := unflat Bq.dims jf
  let x := match (F.crA.getD b #[]).getD t none with
    | some r => slotRA C F b r jf
    | none => 0
  let arg (k : ℕ) (w : FE) : List (ℕ × FE) :=
    let a := row.args.getD k default
    cellEntsFA A C F a.ty (a.at j) w
  let ck := F.stK.getD b 0 + G.twK.getD b 0 * jf + (F.rkK.getD b #[]).getD t 0
  let ce := F.stE.getD b 0 + G.twE.getD b 0 * jf + (F.rkE.getD b #[]).getD t 0
  let res : List (ℕ × FE) := cellEntsFA A C F row.ty (match row.ty with | .K => ck | .E => ce) 1
  match row.op with
  | .muladd => tagE 0 x (arg 0 1) ++ tagE 1 x (arg 1 1) ++ tagE 2 x (arg 2 1) ++ tagE 3 x res
  | .lin k k' => tagE 2 x (arg 0 1 ++ arg 1 (FE.ofK k) ++ [(F.lay.one, FE.ofK k')]) ++ tagE 3 x res
  | .assert0 => tagE 0 x (arg 1 1) ++ tagE 1 x (arg 0 1)
  | .fixmul => tagE 2 x (arg 0 (FE.ofK (F.Q.fixMat j)) ++ arg 1 1) ++ tagE 3 x res
  | _ => []

theorem rowEntsA_eq (C : SC) (G : FLF) (b t jf : ℕ) :
    rowEntsA (AC.of G.F) C G b t jf = rowEntsB C G b t jf := by
  unfold rowEntsA rowEntsB
  simp only [cellEntsFA_eq, slotRA_eq]
  rfl

/-- **`rowEntsXB` on `cellEntsFA`.** -/
def rowEntsXA (A : AC) (C : SC) (G : FLF) (b t jf : ℕ) : List Ent :=
  let F := G.F
  let Bq := F.qb.getD b default
  let row := (F.tpls.getD b #[]).getD t default
  let j := unflat Bq.dims jf
  let x := match (F.crA.getD b #[]).getD t none with
    | some r => slotRA C F b r jf
    | none => 0
  let arg (k : ℕ) (w : FE) : List (ℕ × FE) :=
    let a := row.args.getD k default
    cellEntsFA A C F a.ty (a.at j) w
  let ck := F.stK.getD b 0 + G.twK.getD b 0 * jf + (F.rkK.getD b #[]).getD t 0
  let ce := F.stE.getD b 0 + G.twE.getD b 0 * jf + (F.rkE.getD b #[]).getD t 0
  let res : List (ℕ × FE) := cellEntsFA A C F row.ty (match row.ty with | .K => ck | .E => ce) 1
  let res1 : List (ℕ × FE) := cellEntsFA A C F .K (ck + 1) 1
  match row.op with
  | .e2 .mul false =>
      tagE 0 x (arg 0 1) ++ tagE 4 x (arg 1 1) ++ tagE 1 x (arg 2 1) ++ tagE 5 x (arg 3 1) ++
      tagE 2 x (arg 4 1) ++ tagE 6 x (arg 5 1) ++ tagE 3 x res ++ tagE 7 x res1
  | .e2 (.lin k k₀ k₁) false =>
      tagE 2 x (arg 0 1 ++ arg 2 (FE.ofK k) ++ [(F.lay.one, FE.ofK k₀)]) ++
      tagE 6 x (arg 1 1 ++ arg 3 (FE.ofK k) ++ [(F.lay.one, FE.ofK k₁)]) ++
      tagE 3 x res ++ tagE 7 x res1
  | .e2 _ true => []
  | _ => rowEntsA A C G b t jf

theorem rowEntsXA_eq (C : SC) (G : FLF) (b t jf : ℕ) :
    rowEntsXA (AC.of G.F) C G b t jf = rowEntsXB C G b t jf := by
  unfold rowEntsXA rowEntsXB
  simp only [cellEntsFA_eq, rowEntsA_eq, slotRA_eq]
  rfl

/-- **`auxEntsB` with the rows from `AC`.** -/
def auxEntsA (A : AC) (C : SC) (G : FLF) (k r j : ℕ) : List Ent :=
  let F := G.F
  let x := slotRA C F (F.bl.size + k) r j
  ((A.aux.getD k #[]).getD r default).ops.flatMap fun e ↦
    tagE e.1 x (match e.2.1 with
      | .word base stride => [(base + stride * j, e.2.2)]
      | .cell a => cellEntsFA A C F a.ty (a.at [j]) e.2.2
      | .one => [(F.lay.one, e.2.2)])

theorem auxEntsA_eq (C : SC) (G : FLF) (k r j : ℕ) :
    auxEntsA (AC.of G.F) C G k r j = auxEntsB C G k r j := by
  unfold auxEntsA auxEntsB
  simp only [cellEntsFA_eq, auxA_getD, slotRA_eq]
  rfl

end Lvm.Typed.K
