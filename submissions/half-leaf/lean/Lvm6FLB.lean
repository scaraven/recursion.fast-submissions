-- New for lvm6 (WP LAY4): binary-search twins of the wiring cache's chunk searches (`FL.slotR`, `BLay.slotWord`)
-- and of the entry functions the blob exporter calls (`FLF.rowEntsX`, `FLF.auxEnts`), equal to them when the chunk
-- tables are sorted (`SC.okB`, checked once).
import LvmWiringXF
import LvmQTypedSWire

/-!
# Chunk searches by bisection

`FL.slotR b r jf` (the slot of constraint rank `r` of block `b`) and `BLay.slotWord τ s jf m` (the word of result
`s`) scan the block's chunk lists with `find?`, once per entry. LAY4's first-fit layout splits a glue block into
hundreds of chunks (CC's block 105: 413), so the exporter's entry pass grew from 136 s to more than 400 s.

* **`trs lo len L k`**: the intervals `[lo c, lo c + len c)` of a list, tagged with their positions from `k`;
  **`trs_find`**: a `find?` on them, mapped back through the position, is the list's own `find?`.
* **`SC`**, **`SC.of F`**: per block the interval tables of the constraint chunks and of the `K`/`E` word chunks;
  **`SC.okB`**: every table sorted and disjoint (`fl_bsLoop_spec`'s hypothesis), checked once.
* **`slotRB`**, **`slotWordB`**: the searches by `FL.bsRec` (the owner search); **`slotRB_eq`**,
  **`slotWordB_eq`**: equal to `FL.slotR`, `BLay.slotWord` under `SC.okB`.
* **`rowEntsXB`**, **`auxEntsB`**: `FLF.rowEntsX`, `FLF.auxEnts` with the bisections (the same text otherwise);
  **`rowEntsXB_eq`**, **`auxEntsB_eq`**: equal under `SC.okB`. Nothing here is a statement of the entry: the
  exporter uses them, the blob's entries are the same.
-/

set_option autoImplicit false

namespace Lvm.Typed.K

open Lvm.Loop

/-! ## Interval tables -/

/-- The intervals `[lo c, lo c + len c)` of `L`, tagged with their positions from `k`. -/
def trs {α : Type} (lo len : α → ℕ) : List α → ℕ → List (ℕ × ℕ × ℕ)
  | [], _ => []
  | c :: L, k => (lo c, lo c + len c, k) :: trs lo len L (k + 1)

theorem trs_ge {α : Type} (lo len : α → ℕ) : ∀ (L : List α) (k : ℕ), ∀ x ∈ trs lo len L k, k ≤ x.2.2
  | [], _, x, hx => by simp [trs] at hx
  | c :: L, k, x, hx => by
    simp only [trs, List.mem_cons] at hx
    rcases hx with hx | hx
    · rw [hx]
    · have := trs_ge lo len L (k + 1) x hx
      omega

theorem trs_wf {α : Type} (lo len : α → ℕ) : ∀ (L : List α) (k : ℕ), ∀ x ∈ trs lo len L k, x.1 ≤ x.2.1
  | [], _, x, hx => by simp [trs] at hx
  | c :: L, k, x, hx => by
    simp only [trs, List.mem_cons] at hx
    rcases hx with hx | hx
    · rw [hx]; exact Nat.le_add_right _ _
    · exact trs_wf lo len L (k + 1) x hx

/-- **A search on the tagged intervals is the list's search.** -/
theorem trs_find {α : Type} [Inhabited α] (lo len : α → ℕ) (r : ℕ) : ∀ (L : List α) (k : ℕ),
    ((trs lo len L k).find? fun x ↦ decide (x.1 ≤ r ∧ r < x.2.1)).map (fun x ↦ L.getD (x.2.2 - k) default) =
      L.find? fun c ↦ decide (lo c ≤ r ∧ r < lo c + len c)
  | [], _ => rfl
  | c :: L, k => by
    by_cases h : lo c ≤ r ∧ r < lo c + len c
    · rw [trs, List.find?_cons_of_pos (by simpa using h), List.find?_cons_of_pos (by simpa using h)]
      simp
    · rw [trs, List.find?_cons_of_neg (by simpa using h), List.find?_cons_of_neg (by simpa using h),
        ← trs_find lo len r L (k + 1)]
      cases hf : (trs lo len L (k + 1)).find? (fun x ↦ decide (x.1 ≤ r ∧ r < x.2.1)) with
      | none => rfl
      | some x =>
        have hx := trs_ge lo len L (k + 1) x (List.mem_of_find?_eq_some hf)
        obtain ⟨d, hd⟩ : ∃ d, x.2.2 = k + 1 + d := ⟨x.2.2 - (k + 1), by omega⟩
        simp only [Option.map_some, hd, show k + 1 + d - k = d + 1 by omega,
          show k + 1 + d - (k + 1) = d by omega, List.getD_cons_succ]

/-! ## The tables of a cache -/

/-- The interval table of a block's constraint chunks. -/
def tblX (a : Array XChunk) : Array (ℕ × ℕ × ℕ) := (trs XChunk.r0 XChunk.n a.toList 0).toArray

/-- The interval table of a block's word chunks. -/
def tblR (l : List RChunk) : Array (ℕ × ℕ × ℕ) := (trs RChunk.s0 RChunk.n l 0).toArray

/-- **The search tables**: per block (and auxiliary block) its constraint chunks, per block its `K` and `E`
word chunks. -/
structure SC where
  /-- Constraint chunks (`FL.xch`). -/
  xt : Array (Array (ℕ × ℕ × ℕ))
  /-- `K` word chunks (`BLay.chK`). -/
  kt : Array (Array (ℕ × ℕ × ℕ))
  /-- `E` word chunks (`BLay.chE`). -/
  et : Array (Array (ℕ × ℕ × ℕ))

/-- The tables of `F`. -/
def SC.of (F : FL) : SC :=
  ⟨F.xch.map tblX, F.bl.map fun B ↦ tblR B.chK, F.bl.map fun B ↦ tblR B.chE⟩

/-- A table is sorted and disjoint. -/
def sortedB (a : Array (ℕ × ℕ × ℕ)) : Bool := decide (a.toList.Pairwise fun x y ↦ x.2.1 ≤ y.1)

/-- **Every table sorted** (the bisection's hypothesis; checked once). -/
def SC.okB (C : SC) : Bool := C.xt.all sortedB && C.kt.all sortedB && C.et.all sortedB

theorem sortedB_getD (A : Array (Array (ℕ × ℕ × ℕ))) (h : A.all sortedB = true) (b : ℕ) :
    sortedB (A.getD b #[]) = true := by
  by_cases hb : b < A.size
  · rw [Array.all_eq_true] at h
    simpa [Array.getD, hb] using h b hb
  · simp [Array.getD, hb, sortedB]

theorem getD_map_tbl {β : Type} [Inhabited β] (A : Array β) (g : β → Array (ℕ × ℕ × ℕ)) (hg : g default = #[])
    (b : ℕ) : (A.map g).getD b #[] = g (A.getD b default) := by
  by_cases hb : b < A.size
  · simp [Array.getD, hb]
  · simp [Array.getD, hb, hg]

/-- The bisection of a table (`FL.bsRec`, the owner search). -/
def bsI (a : Array (ℕ × ℕ × ℕ)) (n : ℕ) : Option ℕ := FL.bsRec a n 0 a.size (a.size + 1)

/-- **`bsI` on a sorted table of a list is the list's search**, mapped back through the position. -/
theorem bsI_trs {α : Type} [Inhabited α] (lo len : α → ℕ) (L : List α) (r : ℕ)
    (hs : sortedB (trs lo len L 0).toArray = true) :
    (bsI (trs lo len L 0).toArray r).map (fun i ↦ L.getD i default) =
      L.find? fun c ↦ decide (lo c ≤ r ∧ r < lo c + len c) := by
  unfold bsI
  rw [bsRec_eq, fl_bsLoop_spec _ _ (by simpa [sortedB] using hs)
    (by simpa using trs_wf lo len L 0), ← trs_find lo len r L 0]
  simp only [Option.map_map]
  rfl

/-! ## The searches -/

/-- **`FL.slotR` by bisection.** -/
def slotRB (C : SC) (F : FL) (b r jf : ℕ) : ℕ :=
  match bsI (C.xt.getD b #[]) r with
  | some i =>
    let c := (F.xch.getD b #[]).toList.getD i default
    c.base + (r - c.r0) * 2 ^ c.l + jf
  | none => 0

theorem slotRB_eq (F : FL) (h : (SC.of F).okB = true) (b r jf : ℕ) :
    slotRB (SC.of F) F b r jf = F.slotR b r jf := by
  simp only [SC.okB, Bool.and_eq_true] at h
  have hs := sortedB_getD _ h.1.1 b
  have hx : (SC.of F).xt.getD b #[] = tblX (F.xch.getD b #[]) := getD_map_tbl _ _ rfl b
  rw [hx] at hs
  have key := bsI_trs XChunk.r0 XChunk.n (F.xch.getD b #[]).toList r hs
  unfold slotRB FL.slotR
  rw [hx, ← Array.find?_toList, ← key]
  unfold tblX
  cases bsI (trs XChunk.r0 XChunk.n (F.xch.getD b #[]).toList 0).toArray r <;> rfl

/-- **`BLay.slotWord` by bisection** (block `b`'s copy). -/
def slotWordB (C : SC) (F : FL) (b : ℕ) (τ : Ty) (s jf m : ℕ) : ℕ :=
  let B := F.bl.getD b default
  match bsI ((match τ with | .K => C.kt | .E => C.et).getD b #[]) s with
  | some i =>
    let c := (B.ch τ).getD i default
    c.bases.getD m 0 + (s - c.s0) * 2 ^ B.l + jf
  | none => 0

theorem slotWordB_eq (F : FL) (h : (SC.of F).okB = true) (b : ℕ) (τ : Ty) (s jf m : ℕ) :
    slotWordB (SC.of F) F b τ s jf m = (F.bl.getD b default).slotWord τ s jf m := by
  simp only [SC.okB, Bool.and_eq_true] at h
  have hT : ((match τ with | .K => (SC.of F).kt | .E => (SC.of F).et).getD b #[]) =
      tblR ((F.bl.getD b default).ch τ) := by
    cases τ
    · exact getD_map_tbl _ (fun B : BLay ↦ tblR B.chK) rfl b
    · exact getD_map_tbl _ (fun B : BLay ↦ tblR B.chE) rfl b
  have hs : sortedB (tblR ((F.bl.getD b default).ch τ)) = true := by
    rw [← hT]
    cases τ
    · exact sortedB_getD _ h.1.2 b
    · exact sortedB_getD _ h.2 b
  have key := bsI_trs RChunk.s0 RChunk.n ((F.bl.getD b default).ch τ) s hs
  unfold slotWordB BLay.slotWord
  rw [hT, ← key]
  unfold tblR
  cases bsI (trs RChunk.s0 RChunk.n ((F.bl.getD b default).ch τ) 0).toArray s <;> rfl

/-! ## The twins of the cell words and the entries -/

/-- `FL.wordC` on `slotWordB` (block `b`). -/
def wordCB (C : SC) (F : FL) (b : ℕ) (τ : Ty) (n s jf m : ℕ) : ℕ :=
  match F.dreg τ n with
  | some d => d.word n m
  | none => slotWordB C F b τ s jf m

theorem wordCB_eq (F : FL) (h : (SC.of F).okB = true) (b : ℕ) (τ : Ty) (n s jf m : ℕ) :
    wordCB (SC.of F) F b τ n s jf m = F.wordC (F.bl.getD b default) τ n s jf m := by
  unfold wordCB FL.wordC
  simp only [slotWordB_eq F h]
  rfl

/-- `FL.wordKF` on `wordCB`. -/
def wordKFB (C : SC) (F : FL) (n : ℕ) : ℕ :=
  match F.ownerF .K n with
  | some b =>
    let B := F.bl.getD b default
    let off := n - B.stK
    match (F.srcKA.getD b #[]).getD (off % B.twK) default with
    | .slot s => wordCB C F b .K n s (off / B.twK) 0
    | .alias tgt => F.wordD .K (tgt.getD (off / B.twK) 0) 0
    | .load _ => 0
  | none => F.wordD .K n 0

theorem wordKFB_eq (F : FL) (h : (SC.of F).okB = true) (n : ℕ) : wordKFB (SC.of F) F n = F.wordKF n := by
  unfold wordKFB FL.wordKF
  simp only [wordCB_eq F h]
  rfl

/-- `FL.wordE3` on `wordCB`, `wordKFB`. -/
def wordE3B (C : SC) (F : FL) (n : ℕ) : ℕ × ℕ × ℕ :=
  match F.ownerF .E n with
  | some b =>
    let B := F.bl.getD b default
    let off := n - B.stE
    match (F.srcEA.getD b #[]).getD (off % B.twE) default with
    | .slot s => (wordCB C F b .E n s (off / B.twE) 0, wordCB C F b .E n s (off / B.twE) 1,
        wordCB C F b .E n s (off / B.twE) 2)
    | .load args =>
      let j := unflat B.dims (off / B.twE)
      (wordKFB C F ((args.getD 0 default).at j), wordKFB C F ((args.getD 1 default).at j),
        wordKFB C F ((args.getD 2 default).at j))
    | .alias _ => (0, 0, 0)
  | none => (F.wordD .E n 0, F.wordD .E n 1, F.wordD .E n 2)

theorem wordE3B_eq (F : FL) (h : (SC.of F).okB = true) (n : ℕ) : wordE3B (SC.of F) F n = F.wordE3 n := by
  unfold wordE3B FL.wordE3
  simp only [wordCB_eq F h, wordKFB_eq F h]
  rfl

/-- `FL.cellEntsF` on `wordKFB`, `wordE3B`. -/
def cellEntsFB (C : SC) (F : FL) (τ : Ty) (n : ℕ) (w : FE) : List (ℕ × FE) :=
  match τ with
  | .K => match F.cst n with
    | some v => [(F.lay.one, w * FE.ofK v)]
    | none => [(wordKFB C F n, w)]
  | .E =>
    let ws := wordE3B C F n
    let wy := w * FE.y
    [(ws.1, w), (ws.2.1, wy), (ws.2.2, wy * FE.y)]

theorem cellEntsFB_eq (F : FL) (h : (SC.of F).okB = true) (τ : Ty) (n : ℕ) (w : FE) :
    cellEntsFB (SC.of F) F τ n w = F.cellEntsF τ n w := by
  unfold cellEntsFB FL.cellEntsF
  simp only [wordKFB_eq F h, wordE3B_eq F h]
  rfl

/-- `FLF.rowEnts` on the bisections. -/
def rowEntsB (C : SC) (G : FLF) (b t jf : ℕ) : List Ent :=
  let F := G.F
  let Bq := F.qb.getD b default
  let row := (F.tpls.getD b #[]).getD t default
  let j := unflat Bq.dims jf
  let x := match (F.crA.getD b #[]).getD t none with
    | some r => slotRB C F b r jf
    | none => 0
  let arg (k : ℕ) (w : FE) : List (ℕ × FE) :=
    let a := row.args.getD k default
    cellEntsFB C F a.ty (a.at j) w
  let ck := F.stK.getD b 0 + G.twK.getD b 0 * jf + (F.rkK.getD b #[]).getD t 0
  let ce := F.stE.getD b 0 + G.twE.getD b 0 * jf + (F.rkE.getD b #[]).getD t 0
  let res : List (ℕ × FE) := cellEntsFB C F row.ty (match row.ty with | .K => ck | .E => ce) 1
  match row.op with
  | .muladd => tagE 0 x (arg 0 1) ++ tagE 1 x (arg 1 1) ++ tagE 2 x (arg 2 1) ++ tagE 3 x res
  | .lin k k' => tagE 2 x (arg 0 1 ++ arg 1 (FE.ofK k) ++ [(F.lay.one, FE.ofK k')]) ++ tagE 3 x res
  | .assert0 => tagE 0 x (arg 1 1) ++ tagE 1 x (arg 0 1)
  | .fixmul => tagE 2 x (arg 0 (FE.ofK (F.Q.fixMat j)) ++ arg 1 1) ++ tagE 3 x res
  | _ => []

theorem rowEntsB_eq (G : FLF) (h : (SC.of G.F).okB = true) (b t jf : ℕ) :
    rowEntsB (SC.of G.F) G b t jf = G.rowEnts b t jf := by
  unfold rowEntsB FLF.rowEnts
  simp only [slotRB_eq G.F h, cellEntsFB_eq G.F h]
  rfl

/-- **`FLF.rowEntsX` on the bisections.** -/
def rowEntsXB (C : SC) (G : FLF) (b t jf : ℕ) : List Ent :=
  let F := G.F
  let Bq := F.qb.getD b default
  let row := (F.tpls.getD b #[]).getD t default
  let j := unflat Bq.dims jf
  let x := match (F.crA.getD b #[]).getD t none with
    | some r => slotRB C F b r jf
    | none => 0
  let arg (k : ℕ) (w : FE) : List (ℕ × FE) :=
    let a := row.args.getD k default
    cellEntsFB C F a.ty (a.at j) w
  let ck := F.stK.getD b 0 + G.twK.getD b 0 * jf + (F.rkK.getD b #[]).getD t 0
  let ce := F.stE.getD b 0 + G.twE.getD b 0 * jf + (F.rkE.getD b #[]).getD t 0
  let res : List (ℕ × FE) := cellEntsFB C F row.ty (match row.ty with | .K => ck | .E => ce) 1
  let res1 : List (ℕ × FE) := cellEntsFB C F .K (ck + 1) 1
  match row.op with
  | .e2 .mul false =>
      tagE 0 x (arg 0 1) ++ tagE 4 x (arg 1 1) ++ tagE 1 x (arg 2 1) ++ tagE 5 x (arg 3 1) ++
      tagE 2 x (arg 4 1) ++ tagE 6 x (arg 5 1) ++ tagE 3 x res ++ tagE 7 x res1
  | .e2 (.lin k k₀ k₁) false =>
      tagE 2 x (arg 0 1 ++ arg 2 (FE.ofK k) ++ [(F.lay.one, FE.ofK k₀)]) ++
      tagE 6 x (arg 1 1 ++ arg 3 (FE.ofK k) ++ [(F.lay.one, FE.ofK k₁)]) ++
      tagE 3 x res ++ tagE 7 x res1
  | .e2 _ true => []
  | _ => rowEntsB C G b t jf

theorem rowEntsXB_eq (G : FLF) (h : (SC.of G.F).okB = true) (b t jf : ℕ) :
    rowEntsXB (SC.of G.F) G b t jf = G.rowEntsX b t jf := by
  unfold rowEntsXB FLF.rowEntsX
  simp only [slotRB_eq G.F h, cellEntsFB_eq G.F h, rowEntsB_eq G h]
  rfl

/-- `FLF.auxEnts` on the bisections. -/
def auxEntsB (C : SC) (G : FLF) (k r j : ℕ) : List Ent :=
  let F := G.F
  let x := slotRB C F (F.bl.size + k) r j
  ((F.lay.aux.getD k default).rows.getD r default).ops.flatMap fun e ↦
    tagE e.1 x (match e.2.1 with
      | .word base stride => [(base + stride * j, e.2.2)]
      | .cell a => cellEntsFB C F a.ty (a.at [j]) e.2.2
      | .one => [(F.lay.one, e.2.2)])

theorem auxEntsB_eq (G : FLF) (h : (SC.of G.F).okB = true) (k r j : ℕ) :
    auxEntsB (SC.of G.F) G k r j = G.auxEnts k r j := by
  unfold auxEntsB FLF.auxEnts
  simp only [slotRB_eq G.F h, cellEntsFB_eq G.F h]
  rfl

end Lvm.Typed.K
