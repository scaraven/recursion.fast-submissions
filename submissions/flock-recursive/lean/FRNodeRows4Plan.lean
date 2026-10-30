-- New for `flock-recursive` (BLUEPRINT revision 4.1, B-16, §4.4; stage S-E12b, track L-circ).
import FRNodeRows4RepFD
import FRNodeRows4RepCFW
import FRInitFuse

/-!
# The 4.1 nodes' plan and `evalM`: one evaluation per prototype

**The plan** (`planOf4`, a closed constant built at process start, B-16) is the two prototypes'
proved pieces (S-E13's construction for one slot: `protoData`, `protoData_rows`), shared by `N2`,
`N4` and `N8`.

**`evalM`** (`evalMT4`). Every entry of slot `σ`'s rows has its row and its cell in region `σ`, so
for the prototype's rows moved to region `σ` and made absolute (`copy_val`):

  `MLE(slot σ)(τ, u) = eq(τ_[20,lm), σ) · eq(u_[20,lm), σ) · u_lm · u_lm+1 · MLE_lo(prototype)`

where `MLE_lo` is the prototype's value at the point restricted to region `π`'s low coordinates
(`starPt`): one evaluation per prototype, by the existing templated evaluator (21 row and 23 cell
coordinates), whatever the kind. The link region (S-E12c's ≤ 8 link rows, S-E13a's pack rows,
S-E13b's node rows, with H cells) is summed by split eq tables (`linkV4`) from data the plan prepares
once (B5): its rows grouped (`LkG`), the node rows coded against a cell dictionary (`crowsVal3`),
the pinned elements in runs and value classes whose inner sums the kinds share (`prIn`, `prVal`). The
region facts are checked once per process on the pieces (`pieceInB`, `pcIn_spec`), with the sparse
sum as the fallback. **`evalMT4_eq`**: `evalMT4` is the MLE of `nodeIRows4 κ`'s three matrices.

**The replay rows** (REPF, `FRNodeRows4.repAllRows`): the plan computes them in the template rows'
memoized pass (`arRepOf`, the fold lemma `arRepOf_eq`), checks their fit (`RepFit`, in `inR`) and keeps
slot 0's frame and local parts grouped in local coordinates (`rgF`, `rgL`); per call `rvOf` evaluates
them once (shared by `N2` and `N4`) and `repV4` scales them by the regions' high factors (`repV0_eq`);
a segment slot's 8 rows are summed sparsely (`repIRowsWP`).
-/

namespace FR
namespace Rev4
open RecursionFast Circ TEval Tpl

/-! ## The two prototypes' pieces (S-E13's `planData`, two programs) -/

/-- Prototype `π`'s `one` form. -/
abbrev oneP (π : ℕ) : Lin := Lin.cell (oneR π)

theorem infoOf_map (ks : List TKey) (k : TKey) :
    infoOf (ks.map mkKM) k = ((tRows k).length, cregion k, tNlocs k) := by
  rw [infoOf, kmOf_map, mkKM_info]

/-- **The plan's data**: both prototypes compiled once at their layouts (`protoLay`, constants)
with one template memo, their proto-pieces, **one grouping** (so that the keys, and their
preparation in `evalM`, are shared), each prototype's checked pieces. -/
noncomputable def planData4 : Array GK × Array (List Lin) × Array (List Lin) × List Piece × List Piece :=
  let ops0 := (protoProg 0).ops
  let ops1 := (protoProg 1).ops
  let l0 := protoLay 0
  let l1 := protoLay 1
  let ks0 := l0.map Prod.fst
  let kms := (ks0 ++ (l1.map Prod.fst).filter (fun k => !ks0.contains k)).map mkKM
  let r0 := compMSX (tplExt4 (protoF 0) (protoR 0)) l0 (protoP 0) [] (CS.init (baseR 0)) ops0 none []
  let r1 := compMSX (tplExt4 (protoF 1) (protoR 1)) l1 (protoP 1) r0.2.2 (CS.init (baseR 1)) ops1 none []
  let p0 := slotRP (oneP 0) kms l0 0 r0.1 r0.2.1.reverse []
  let rps1 := (slotRP (oneP 1) kms l1 (1 * slotM4) r1.1 r1.2.1.reverse p0.2).1
  let g := groupRP p0.1 rps1
  (g.1, g.2.1, g.2.2.1, piecesOf g.1 g.2.1 (oneP 0) p0.1 g.2.2.2.1, piecesOf g.1 g.2.2.1 (oneP 1) rps1 g.2.2.2.2)

/-- **The pieces are the prototypes' rows.** -/
theorem planData4_rows :
    planData4.2.2.2.1.flatMap (Piece.rows (planData4.1.map mkKey) planData4.2.1 (oneP 0)) = protoRows 0 ∧
      planData4.2.2.2.2.flatMap (Piece.rows (planData4.1.map mkKey) planData4.2.2.1 (oneP 1)) = protoRows 1 := by
  simp only [planData4, piecesOf_rows]
  obtain ⟨hr0, mr0⟩ := compMSX_T (tplExt4 (protoF 0) (protoR 0)) (protoLay 0) (protoP 0) (baseR 0)
    (protoProg 0).ops (M := []) (by simp [MOk])
  obtain ⟨hr1, -⟩ := compMSX_T (tplExt4 (protoF 1) (protoR 1)) (protoLay 1) (protoP 1) (baseR 1) (protoProg 1).ops mr0
  rw [slotRP_rows, slotRP_rows, hr0, hr1, protoRows, protoRows,
    protoCS, protoCS, compileTF4, compileTF4]
  exact ⟨rfl, by rw [one_mul]⟩

/-! ## The region check -/

/-- **A piece stays in region `π`** (its rows below the link region, its cells in the region);
`shOk k`: key `k`'s shared input forms are in the region (checked once per key). -/
def pieceInB (keys : Array Key) (shOk : Array Bool) (one : Lin) (π : ℕ) : Piece → Bool
  | .sp rs => rs.all fun p => idxInB π p.1 && linInB π p.2.a && linInB π p.2.b && linInB π p.2.c
  | .ins k xh ch own =>
    decide (π * slotM4 ≤ 2 ^ (keys.getD k dkey).A * xh) &&
    decide (2 ^ (keys.getD k dkey).A * xh + (keys.getD k dkey).rows.length + linkN ≤ π * slotM4 + slotM4) &&
    decide (π * slotM4 ≤ 2 ^ (keys.getD k dkey).B * ch) &&
    decide (2 ^ (keys.getD k dkey).B * ch + 2 ^ (keys.getD k dkey).B ≤ π * slotM4 + slotM4) &&
    linInB π one && shOk.getD k false && own.all (linInB π)

/-- The shared forms' check, once per key. -/
def shInB (sh : Array (List Lin)) (π : ℕ) : Array Bool := sh.map fun l => l.all (linInB π)

theorem shInB_get {sh : Array (List Lin)} {π k : ℕ} (h : (shInB sh π).getD k false = true) :
    (sh.getD k []).all (linInB π) = true := by
  simp only [shInB, Array.getD_eq_getD_getElem?, Array.getElem?_map] at h ⊢
  cases e : sh[k]? <;> simp_all

theorem linInB_spec {π : ℕ} {l : Lin} (h : linInB π l = true) {t : ℕ × F} (ht : t ∈ l) :
    π * slotM4 ≤ t.1 ∧ t.1 < π * slotM4 + slotM4 := by
  have := List.all_eq_true.1 h t ht
  simpa [inSB] using this

theorem mem_smul {c : F} {l : Lin} {t : ℕ × F} (h : t ∈ l.smul c) : ∃ t' ∈ l, t.1 = t'.1 := by
  simp only [Lin.smul, List.mem_map] at h
  obtain ⟨t', ht', rfl⟩ := h
  exact ⟨t', ht', rfl⟩

theorem pieceInB_spec {keys : Array Key} {sh : Array (List Lin)} {one : Lin} {π : ℕ}
    (hk : keys.all (Key.ok 21) = true) {pc : Piece} (h : pieceInB keys (shInB sh π) one π pc = true) :
    InSlot π (Piece.rows keys sh one pc) := by
  cases pc with
  | sp rs =>
    intro p hp
    have := List.all_eq_true.1 h p hp
    simp only [Bool.and_eq_true] at this
    obtain ⟨⟨⟨hi, ha⟩, hb⟩, hc⟩ := this
    refine ⟨by simpa [idxInB] using hi, fun s t ht => ?_⟩
    cases s
    · exact linInB_spec ha ht
    · exact linInB_spec hb ht
    · exact linInB_spec hc ht
  | ins k xh ch own =>
    simp only [pieceInB, Bool.and_eq_true, decide_eq_true_eq] at h
    obtain ⟨⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6s⟩, h6o⟩ := h
    have h6 : (sh.getD k [] ++ own).all (linInB π) = true := by
      rw [List.all_append, shInB_get h6s, h6o]; rfl
    obtain ⟨-, -, -, hloc⟩ := Key.ok_spec (key_ok hk k)
    intro p hp
    simp only [Piece.rows, instIR, List.mem_map] at hp
    obtain ⟨⟨r, i⟩, hri, rfl⟩ := hp
    have hri' := List.mk_mem_zipIdx_iff_getElem?.1 hri
    obtain ⟨hil, hr⟩ := List.getElem?_eq_some_iff.1 hri'
    have hrm : r ∈ (keys.getD k dkey).rows := hr ▸ List.getElem_mem hil
    refine ⟨⟨by omega, by omega⟩, fun s t ht => ?_⟩
    rw [Mat.r_inst] at ht
    simp only [instLin, List.mem_flatMap] at ht
    obtain ⟨⟨w, c⟩, hw, ht⟩ := ht
    cases w with
    | one =>
      obtain ⟨t', ht', he⟩ := mem_smul ht
      rw [he]; exact linInB_spec h5 ht'
    | inp j =>
      obtain ⟨t', ht', he⟩ := mem_smul ht
      rw [he]
      have hm : (sh.getD k [] ++ own).getD j [] ∈ (sh.getD k [] ++ own) ∨
          (sh.getD k [] ++ own).getD j [] = [] := by
        rw [List.getD_eq_getElem?_getD]
        rcases hj : (sh.getD k [] ++ own)[j]? with _ | l
        · exact Or.inr rfl
        · exact Or.inl (List.mem_of_getElem? hj)
      rcases hm with hm | hm
      · exact linInB_spec (List.all_eq_true.1 h6 _ hm) ht'
      · rw [hm] at ht'; simp at ht'
    | loc j =>
      simp only [List.mem_singleton] at ht
      subst ht
      have := hloc s r hrm j c hw
      dsimp only
      constructor <;> omega

theorem pcIn_spec {keys : Array Key} {sh : Array (List Lin)} {one : Lin} {π : ℕ}
    (hk : keys.all (Key.ok 21) = true) {pc : List Piece}
    (h : pc.all (pieceInB keys (shInB sh π) one π) = true) :
    InSlot π (pc.flatMap (Piece.rows keys sh one)) := by
  intro p hp
  obtain ⟨q, hq, hp⟩ := List.mem_flatMap.1 hp
  exact pieceInB_spec hk (List.all_eq_true.1 h q hq) p hp

/-! ## Distinct row indices -/

/-- The indices `[s, s + n)`. -/
def ivIdx (iv : ℕ × ℕ) : List ℕ := (List.range iv.2).map (iv.1 + ·)

/-- **A piece's row indices as intervals** `(start, length)`: an instance's rows, or each sparse
row. -/
def ivOf (keys : Array Key) : Piece → List (ℕ × ℕ)
  | .sp rs => rs.map fun p => (p.1, 1)
  | .ins k xh _ _ => [(2 ^ (keys.getD k dkey).A * xh, (keys.getD k dkey).rows.length)]

theorem ivOf_idx (keys : Array Key) (sh : Array (List Lin)) (one : Lin) (pc : Piece) :
    (Piece.rows keys sh one pc).map Prod.fst = (ivOf keys pc).flatMap ivIdx := by
  cases pc with
  | sp rs =>
    simp only [Piece.rows, ivOf]
    induction rs with
    | nil => rfl
    | cons p rs ih => simp [ivIdx, ih]
  | ins k xh ch own =>
    simp only [Piece.rows, instIR, ivOf, ivIdx, List.flatMap_singleton, List.map_map, Function.comp_def]
    apply List.ext_getElem <;> simp

/-- Sorted intervals, each ending before the next starts. -/
def ivsOkB : List (ℕ × ℕ) → Bool
  | a :: b :: l => decide (a.1 + a.2 ≤ b.1) && ivsOkB (b :: l)
  | _ => true

theorem ivsOkB_pairwise : ∀ l : List (ℕ × ℕ), ivsOkB l = true → l.Pairwise fun a b => a.1 + a.2 ≤ b.1
  | [], _ => .nil
  | [_], _ => List.pairwise_singleton _ _
  | a :: b :: l, h => by
    simp only [ivsOkB, Bool.and_eq_true, decide_eq_true_eq] at h
    have ih := ivsOkB_pairwise (b :: l) h.2
    refine List.Pairwise.cons (fun c hc => ?_) ih
    rcases List.mem_cons.1 hc with rfl | hc
    · exact h.1
    · have := List.rel_of_pairwise_cons ih hc; omega

/-- **Disjoint intervals give distinct indices** (checked after sorting by start). -/
theorem ivs_nodup (l : List (ℕ × ℕ)) (h : ivsOkB (l.mergeSort fun a b => decide (a.1 ≤ b.1)) = true) :
    (l.flatMap ivIdx).Nodup := by
  have hp := (List.mergeSort_perm l fun a b => decide (a.1 ≤ b.1)).flatMap_right ivIdx
  refine hp.nodup_iff.1 (List.nodup_flatMap.2 ⟨fun iv _ => ?_, ?_⟩)
  · exact (List.nodup_range).map fun a b h => by simpa using h
  · refine (ivsOkB_pairwise _ h).imp fun {a b} hab => ?_
    show List.Disjoint (ivIdx a) (ivIdx b)
    rw [List.disjoint_left]
    intro x hxa hxb
    simp only [ivIdx, List.mem_map, List.mem_range] at hxa hxb
    omega

/-- The pieces' index check. -/
def idsOkB (keys : Array Key) (pc : List Piece) : Bool :=
  ivsOkB ((pc.flatMap (ivOf keys)).mergeSort fun a b => decide (a.1 ≤ b.1))

theorem idsOkB_spec {keys : Array Key} {sh : Array (List Lin)} {one : Lin} {pc : List Piece}
    (h : idsOkB keys pc = true) : ((pc.flatMap (Piece.rows keys sh one)).map Prod.fst).Nodup := by
  have e : (pc.flatMap (Piece.rows keys sh one)).map Prod.fst = (pc.flatMap (ivOf keys)).flatMap ivIdx := by
    rw [List.map_flatMap, List.flatMap_assoc]
    exact congrArg pc.flatMap (funext fun q => ivOf_idx keys sh one q)
  rw [e]; exact ivs_nodup _ h

/-! ## The fit, checked on rows (the fallback's) -/

/-- Strictly increasing. -/
def strictB : List ℕ → Bool
  | a :: b :: l => decide (a < b) && strictB (b :: l)
  | _ => true

theorem strictB_iff : ∀ l : List ℕ, strictB l = true ↔ l.Pairwise (· < ·)
  | [] => by simp [strictB]
  | [_] => by simp [strictB]
  | a :: b :: l => by
    rw [strictB, Bool.and_eq_true, decide_eq_true_eq, strictB_iff (b :: l)]
    constructor
    · rintro ⟨hab, hl⟩
      refine List.Pairwise.cons (fun c hc => ?_) hl
      rcases List.mem_cons.1 hc with rfl | hc
      · exact hab
      · exact lt_trans hab (List.rel_of_pairwise_cons hl hc)
    · intro h; exact ⟨List.rel_of_pairwise_cons h (List.mem_cons_self ..), h.of_cons⟩

/-- **Distinct indices**, checked by sorting. -/
def idxNodupB (rows : List (ℕ × Row)) : Bool := strictB ((rows.map Prod.fst).mergeSort fun a b => decide (a ≤ b))

theorem idxNodupB_iff (rows : List (ℕ × Row)) : idxNodupB rows = true ↔ (rows.map Prod.fst).Nodup := by
  have hp := List.mergeSort_perm (rows.map Prod.fst) fun a b => decide (a ≤ b)
  rw [idxNodupB, strictB_iff, ← hp.nodup_iff]
  constructor
  · exact fun h => h.imp (ne_of_lt)
  · intro hn
    have hs := List.pairwise_mergeSort (le := fun a b : ℕ => decide (a ≤ b))
      (fun a b c hab hbc => by simp only [decide_eq_true_eq] at *; omega)
      (fun a b => by simp only [Bool.or_eq_true, decide_eq_true_eq]; omega) (rows.map Prod.fst)
    exact (hs.and hn).imp fun ⟨h1, h2⟩ => lt_of_le_of_ne (by simpa using h1) h2

/-- Rows of region `π` (Bool). -/
def inSlotB (π : ℕ) (rows : List (ℕ × Row)) : Bool :=
  rows.all fun p => idxInB π p.1 && linInB π p.2.a && linInB π p.2.b && linInB π p.2.c

theorem linInB_iff {π : ℕ} {l : Lin} : linInB π l = true ↔ ∀ t ∈ l, π * slotM4 ≤ t.1 ∧ t.1 < π * slotM4 + slotM4 := by
  simp [linInB, inSB]

theorem inSlotB_iff (π : ℕ) (rows : List (ℕ × Row)) : inSlotB π rows = true ↔ InSlot π rows := by
  simp only [inSlotB, InSlot, List.all_eq_true, Bool.and_eq_true, linInB_iff]
  refine forall_congr' fun p => imp_congr_right fun _ => ?_
  simp only [idxInB, Bool.and_eq_true, decide_eq_true_eq]
  constructor
  · rintro ⟨⟨⟨hi, ha⟩, hb⟩, hc⟩; exact ⟨hi, fun s => by cases s <;> assumption⟩
  · rintro ⟨hi, hs⟩; exact ⟨⟨⟨hi, hs .a⟩, hs .b⟩, hs .c⟩

/-- **A prototype's fit** (Bool, on its rows). -/
def fitB (π : ℕ) (rows : List (ℕ × Row)) : Bool := inSlotB π rows && idxNodupB rows

theorem fitB_iff (π : ℕ) (rows : List (ℕ × Row)) :
    fitB π rows = true ↔ InSlot π rows ∧ (rows.map Prod.fst).Nodup := by
  rw [fitB, Bool.and_eq_true, inSlotB_iff, idxNodupB_iff]

theorem protoFit_iff : ProtoFit ↔ (fitB 0 (protoRows 0) && fitB 1 (protoRows 1)) = true := by
  rw [Bool.and_eq_true, fitB_iff, fitB_iff]
  constructor
  · intro h; exact ⟨h 0 (by norm_num), h 1 le_rfl⟩
  · rintro ⟨h0, h1⟩ π hπ
    rcases Nat.le_one_iff_eq_zero_or_eq_one.1 hπ with rfl | rfl
    exacts [h0, h1]

/-! ## The arena rows' checks (ASK-P) -/

/-- Template rows indexed in the binding's range (`askPI`'s form, at any rows). -/
def idxAr (π : ℕ) (l : List Row) : List (ℕ × Row) := l.zipIdx.map fun p => (π * slotM4 + arR2 + p.2, p.1)

theorem askPI_eq (π : ℕ) : askPI π = idxAr π (askRowsT π) := rfl

/-- **The arenas' fit of prototype `π`** (Bool, on its rows): its rows below the binding's range, its
template rows at most `arR2N` and in the region (`ArFit`'s conjuncts). -/
def arFitB (π : ℕ) (rows : List (ℕ × Row)) (ar : List Row) : Bool :=
  rows.all (fun p => decide (p.1 < π * slotM4 + arR2)) && decide (ar.length ≤ arR2N) && inSlotB π (idxAr π ar)

theorem arFitB_iff (π : ℕ) (rows : List (ℕ × Row)) (ar : List Row) :
    arFitB π rows ar = true ↔
      (∀ p ∈ rows, p.1 < π * slotM4 + arR2) ∧ ar.length ≤ arR2N ∧ InSlot π (idxAr π ar) := by
  simp only [arFitB, Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq, inSlotB_iff, and_assoc]

theorem arFit_iff : ArFit ↔ (arFitB 0 (protoRows 0) (askRowsT 0) && arFitB 1 (protoRows 1) (askRowsT 1)) = true := by
  rw [Bool.and_eq_true, arFitB_iff, arFitB_iff]
  constructor
  · intro h; exact ⟨h 0 (by norm_num), h 1 le_rfl⟩
  · rintro ⟨h0, h1⟩ π hπ
    rcases Nat.le_one_iff_eq_zero_or_eq_one.1 hπ with rfl | rfl
    exacts [h0, h1]

/-- **The pieces' row indices lie below `b`** (Bool, on the pieces' intervals: the plan's check). -/
def ivBelow (keys : Array Key) (pc : List Piece) (b : ℕ) : Bool :=
  (pc.flatMap (ivOf keys)).all fun iv => decide (iv.1 + iv.2 ≤ b)

theorem ivBelow_spec {keys : Array Key} {sh : Array (List Lin)} {one : Lin} {pc : List Piece} {b : ℕ}
    (h : ivBelow keys pc b = true) : ∀ p ∈ pc.flatMap (Piece.rows keys sh one), p.1 < b := by
  intro p hp
  have e : (pc.flatMap (Piece.rows keys sh one)).map Prod.fst = (pc.flatMap (ivOf keys)).flatMap ivIdx := by
    rw [List.map_flatMap, List.flatMap_assoc]
    exact congrArg pc.flatMap (funext fun q => ivOf_idx keys sh one q)
  have hm : p.1 ∈ (pc.flatMap (ivOf keys)).flatMap ivIdx := e ▸ List.mem_map_of_mem hp
  obtain ⟨iv, hiv, hx⟩ := List.mem_flatMap.1 hm
  have hb := List.all_eq_true.1 h iv hiv
  simp only [decide_eq_true_eq] at hb
  simp only [ivIdx, List.mem_map, List.mem_range] at hx
  obtain ⟨j, hj, hj'⟩ := hx
  omega

/-- **`t` restricted to region `π`'s low coordinates**: `t` below 20, `π`'s bit at 20, `0` above
(so that `eq(starPt t π, π·2^20 + j) = eq(t_<20, j)`). -/
def starPt (t : ℕ → F) (π : ℕ) (l : ℕ) : F := if l < 20 then t l else if l = 20 then (if π = 1 then 1 else 0) else 0

/-! ## The link regions' data, prepared once (B5)

A slot's link region (S-E12c's link rows, S-E13a's kind tie and pinned elements, S-E13b's node rows)
does not depend on the evaluation point. The plan holds, per kind and slot, the head rows and the
node rows grouped by row block (`lkGOf`, lever (a)), and, per distinct `(first row, stream block)`,
the pinned elements in runs of one row block and one cell block (`runsOf`, lever (b)). A run's inner
sums read only the low tables, which every kind shares, so `evalMX4` computes them once per call. -/

/-- The rows before the pinned elements: S-E12c's link rows and the kind tie. -/
def linkHead4 (κ : NodeKind) (σ : ℕ) : List Row := linkRowsB4 κ σ ++ packHead4 κ σ

/-- The link region's first row. -/
def linkBase (σ : ℕ) : ℕ := σ * slotM4 + slotM4 - linkN

/-- The number of pinned elements at slot `σ` (`(packWf4 κ σ).length`, without building the rows). -/
def wfLen (κ : NodeKind) (σ : ℕ) : ℕ :=
  match packB κ σ with
  | some _ => wfSeg.length
  | none => 0

theorem wfLen_eq (κ : NodeKind) (σ : ℕ) : wfLen κ σ = (packWf4 κ σ).length := by
  unfold wfLen packWf4; rcases packB κ σ with _ | ⟨b0, G⟩ <;> simp [wfRows]

/-! ### S-E13b's node rows over a cell dictionary (B5)

The node rows (≈ 8k per kind) have ≈ 36k terms over ≈ 11k distinct cells. Their forms are coded
against a sorted cell dictionary, so that each distinct cell's `eq` value is one product per
evaluation and a term is a lookup. The coding is checked once, at plan init, by decoding (`cokB`). -/

/-- A form coded against a dictionary: `(cell index, coefficient)`. -/
abbrev CForm := List (ℕ × F)

/-- Coded rows by row block: `(row block, [(row low, a, b, c)])`. -/
abbrev CRows := List (ℕ × List (ℕ × CForm × CForm × CForm))

/-- Binary search in a sorted array: the last index whose entry is `≤ x` (fuel-bounded; the coding
is checked). -/
def bsGo (a : Array ℕ) (x : ℕ) (lo hi : ℕ) : ℕ → ℕ
  | 0 => lo
  | f + 1 => if lo + 1 ≥ hi then lo else
    let m := (lo + hi) / 2
    if a.getD m 0 ≤ x then bsGo a x m hi f else bsGo a x lo m f

/-- Adjacent duplicates dropped. -/
def dedupS : List ℕ → List ℕ
  | a :: b :: l => if a = b then dedupS (b :: l) else a :: dedupS (b :: l)
  | l => l

/-- The rows' cells, sorted and distinct. -/
def cellsOf (rows : List (ℕ × Row)) : Array ℕ :=
  (dedupS (((rows.flatMap fun p => p.2.a ++ p.2.b ++ p.2.c).map (·.1)).mergeSort
    fun a b => decide (a ≤ b))).toArray

/-- A form coded against `cs`. -/
def encF (cs : Array ℕ) (l : Lin) : CForm := l.map fun t => (bsGo cs t.1 0 cs.size 64, t.2)

/-- **The coded rows**, grouped by row block. -/
def crowsOf (cs : Array ℕ) (rows : List (ℕ × Row)) : CRows :=
  rows.foldr (fun p G => let r := (p.1 % 2 ^ 11, encF cs p.2.a, encF cs p.2.b, encF cs p.2.c)
    match G with
    | g :: gs => if g.1 = p.1 / 2 ^ 11 then (g.1, r :: g.2) :: gs else (p.1 / 2 ^ 11, [r]) :: G
    | [] => [(p.1 / 2 ^ 11, [r])]) []

/-- A coded form decoded. -/
def decF (cs : Array ℕ) (f : CForm) : Lin := f.map fun e => (cs.getD e.1 0, e.2)

/-- A coded row decoded. -/
def decR (cs : Array ℕ) (h : ℕ) (r : ℕ × CForm × CForm × CForm) : ℕ × Row :=
  (h * 2 ^ 11 + r.1, ⟨decF cs r.2.1, decF cs r.2.2.1, decF cs r.2.2.2⟩)

/-- The coded rows decoded. -/
def decRows (cs : Array ℕ) (G : CRows) : List (ℕ × Row) := G.flatMap fun g => g.2.map (decR cs g.1)

/-- Row lows below `2^11`, cell indices in the dictionary. -/
def cbnd (cs : Array ℕ) (G : CRows) : Bool :=
  G.all fun g => g.2.all fun r => decide (r.1 < 2 ^ 11) &&
    (r.2.1 ++ r.2.2.1 ++ r.2.2.2).all fun e => decide (e.1 < cs.size)

/-- **The coding check**: in bounds, and decoding gives back the rows. -/
def cokB (cs : Array ℕ) (G : CRows) (rows : List (ℕ × Row)) : Bool := cbnd cs G && decide (decRows cs G = rows)

/-- Slot `σ`'s node rows, indexed. -/
def extIRows (κ : NodeKind) (σ : ℕ) : List (ℕ × Row) :=
  ((extRowsC κ σ).zipIdx ((linkHead4 κ σ).length + wfLen κ σ)).map fun p => (linkBase σ + p.2, p.1)

/-- **A slot's link rows, prepared** (lever (a)): the head's length, the head rows and S-E13b's node
rows grouped by row block (`ex`, a thunk: grouped only if the coding check fails), and the node rows
coded against their cell dictionary (`ec`, `eg`; used if `eok`, the coding check). -/
structure LkG where
  nh : ℕ
  hd : GRows
  ex : Thunk GRows
  ec : Array ℕ
  eg : CRows
  eok : Bool

/-- Slot `σ`'s prepared link rows. -/
def lkGOf (κ : NodeKind) (σ : ℕ) : LkG :=
  let rows := extIRows κ σ
  let cs := cellsOf rows
  let G := crowsOf cs rows
  ⟨(linkHead4 κ σ).length, grows (2 ^ 11) (2 ^ 12) ((linkHead4 κ σ).zipIdx.map fun p => (linkBase σ + p.2, p.1)),
    Thunk.mk fun _ => grows (2 ^ 11) (2 ^ 12) rows, cs, G, cokB cs G rows⟩

/-- A kind's grouped link rows, slot by slot (a closed constant per kind). -/
def lkArr (κ : NodeKind) : Array LkG := (Array.range κ.vslots).map (lkGOf κ)

/-- **A run of pinned elements** (lever (b)): `(row block, cell block, [(row low, cell low)])`, the
rows split at `2^11` and the cells at `2^12`, as `ltbOf`'s tables. -/
abbrev PRun := ℕ × ℕ × List (ℕ × ℕ)

/-- **The pinned elements by value** (`wfSeg` has 24 distinct values): `(value, [(row block, [row
low])])`. -/
abbrev PCls := List (F × List (ℕ × List ℕ))

/-- Put the pinned element at row `x`, cell `c` in front of runs. -/
def prStep (x c : ℕ) : List PRun → List PRun
  | r :: rs => if r.1 = x / 2 ^ 11 ∧ r.2.1 = c / 2 ^ 12 then (r.1, r.2.1, (x % 2 ^ 11, c % 2 ^ 12) :: r.2.2) :: rs
    else (x / 2 ^ 11, c / 2 ^ 12, [(x % 2 ^ 11, c % 2 ^ 12)]) :: r :: rs
  | [] => [(x / 2 ^ 11, c / 2 ^ 12, [(x % 2 ^ 11, c % 2 ^ 12)])]

/-- Put row `x` in front of a value's row blocks. -/
def blkIns (x : ℕ) : List (ℕ × List ℕ) → List (ℕ × List ℕ)
  | g :: gs => if g.1 = x / 2 ^ 11 then (g.1, x % 2 ^ 11 :: g.2) :: gs else (x / 2 ^ 11, [x % 2 ^ 11]) :: g :: gs
  | [] => [(x / 2 ^ 11, [x % 2 ^ 11])]

/-- Put the pinned element at row `x` with value `k` in its value's class. -/
def clsIns (k : F) (x : ℕ) : PCls → PCls
  | c :: cs => if c.1 = k then (c.1, blkIns x c.2) :: cs else c :: clsIns k x cs
  | [] => [(k, blkIns x [])]

/-- **The pinned elements `ps`** of a stream at block `b0`, at rows `j, j + 1, …`: in runs (for the
cells) and by value (for the constants). -/
def runsOf (b0 : ℕ) : ℕ → List (ℕ × F) → List PRun × PCls
  | _, [] => ([], [])
  | j, p :: ps => let r := runsOf b0 (j + 1) ps; (prStep j (sCell b0 p.1) r.1, clsIns p.2 j r.2)

/-- The distinct `(first row, stream block)` of the slots with pinned elements, over the three kinds
(`(0, 0)`-blocks of `N2`/`N4`/`N8`'s slot 0 coincide, and so do `N2`/`N4`'s slot 1). -/
def pinKeys : List (ℕ × ℕ) :=
  (NodeKind.all.flatMap fun κ => (List.range κ.vslots).filterMap fun σ =>
    (packB κ σ).map fun b => (linkBase σ + (linkHead4 κ σ).length, b.1)).eraseDups

/-! ## The plan -/

/-- Every key's rows and locals fit 20 bits (so its preparation reads coordinates below 20 only,
which both prototypes' points share: `kprep_star`). -/
def lowKeys (keys : Array Key) : Bool := keys.all fun K => decide (K.A ≤ 20) && decide (K.B ≤ 20)

/-- **The 4.1 nodes' plan** (all of `N2`, `N4`, `N8`): the shared keys, each prototype's shared
forms and pieces (its rows, `ok`), the prepared forms, and the checks. -/
structure Plan4 where
  keys : Array Key
  sh0 : Array (List Lin)
  sh1 : Array (List Lin)
  pc0 : List Piece
  pc1 : List Piece
  ok : keys.all (Key.ok 21) = true ∧ pc0.flatMap (Piece.rows keys sh0 (oneP 0)) = protoRows 0 ∧
    pc1.flatMap (Piece.rows keys sh1 (oneP 1)) = protoRows 1
  g0 : Array (List GForm)
  g1 : Array (List GForm)
  p0 : List PPc
  p1 : List PPc
  pats : Array (Array Pat)
  pbs : List ℕ
  hg0 : g0 = sh0.map (·.map (grp 4096))
  hg1 : g1 = sh1.map (·.map (grp 4096))
  hp0 : p0 = pc0.map (prepPiece pats)
  hp1 : p1 = pc1.map (prepPiece pats)
  inR : Bool
  hR : inR = true → ProtoFit ∧ lowKeys keys = true ∧ ArFit ∧ RepFit
  /-- Each kind's grouped link rows (B5). -/
  lk2 : Array LkG
  lk4 : Array LkG
  lk8 : Array LkG
  hlk2 : lk2 = lkArr .N2
  hlk4 : lk4 = lkArr .N4
  hlk8 : lk8 = lkArr .N8
  /-- The pinned elements' runs, per `(first row, stream block)` (B5). -/
  pkr : List ((ℕ × ℕ) × (List PRun × PCls))
  hpkr : ∀ p ∈ pkr, p.2 = runsOf p.1.2 p.1.1 wfSeg
  /-- The prototypes' template rows (ASK-P; computed with the template memo, `arOf`). -/
  ar0 : List Row
  ar1 : List Row
  har : ar0 = askRowsT 0 ∧ ar1 = askRowsT 1
  /-- Their indexed rows, grouped (the prototype's split eq tables). -/
  ag0 : GRows
  ag1 : GRows
  hag : ag0 = grows (2 ^ 11) (2 ^ 12) (askPI 0) ∧ ag1 = grows (2 ^ 11) (2 ^ 12) (askPI 1)
  /-- The replay rows (REPF; the fallback's), recomputed on demand (`arRepOf`, the fold lemma
  `arRepOf_eq`): the plan is a persistent constant, and marking a 65,760-term form persistent
  overflowed the stack at process start. -/
  rp0 : Thunk (Array Row)
  rp1 : Thunk (Array Row)
  hrp : rp0.get.toList = N4s.repRowsP (N4s.rtC1c 0) 0 ∧ rp1.get.toList = N4s.repRowsP (N4s.rtC1c 1) 1
  /-- Prototype 0's replay rows (CF2): its row blocks' rows in local coordinates, grouped (frame part,
  local part), and its `rsWeight` ops prepared at their first rows (`kpOf`; their rows not built). -/
  rgF : GRows
  rgL : GRows
  kps : List (ℕ × KP)
  hrg : ∃ bs : List RBlk, bs.flatMap RBlk.rows = N4s.repRowsP (N4s.rtC1c 0) 0 ∧
    rgF = grows (2 ^ 11) (2 ^ 12) ((blkGo 0 bs [] []).1.map fun p => (p.2, rowFr p.1)) ∧
    rgL = grows (2 ^ 11) (2 ^ 12) ((blkGo 0 bs [] []).1.map fun p => (p.2, rowLoc p.1)) ∧
    kps = (blkGo 0 bs [] []).2

/-- A plan from its pieces (the region and key checks computed here, once). -/
def mkPlan4 (keys : Array Key) (sh0 sh1 : Array (List Lin)) (pc0 pc1 : List Piece)
    (pats : Array (Array Pat))
    (ok : keys.all (Key.ok 21) = true ∧ pc0.flatMap (Piece.rows keys sh0 (oneP 0)) = protoRows 0 ∧
      pc1.flatMap (Piece.rows keys sh1 (oneP 1)) = protoRows 1) (ar0 ar1 : List Row)
    (har : ar0 = askRowsT 0 ∧ ar1 = askRowsT 1) (rl1 : List Row)
    (hrl : rl1 = N4s.repRowsP (N4s.rtC1c 1) 1) (rp0 rp1 : Thunk (Array Row))
    (hrp : rp0.get.toList = N4s.repRowsP (N4s.rtC1c 0) 0 ∧ rp1.get.toList = N4s.repRowsP (N4s.rtC1c 1) 1)
    (q : List (Row × ℕ) × List (ℕ × KP))
    (hq : ∃ bs : List RBlk, bs.flatMap RBlk.rows = N4s.repRowsP (N4s.rtC1c 0) 0 ∧ q = blkGo 0 bs [] []) : Plan4 where
  keys := keys
  sh0 := sh0
  sh1 := sh1
  pc0 := pc0
  pc1 := pc1
  ok := ok
  g0 := sh0.map (·.map (grp 4096))
  g1 := sh1.map (·.map (grp 4096))
  p0 := pc0.map (prepPiece pats)
  p1 := pc1.map (prepPiece pats)
  pats := pats
  pbs := patBits pats
  hg0 := rfl
  hg1 := rfl
  hp0 := rfl
  hp1 := rfl
  inR := pc0.all (pieceInB keys (shInB sh0 0) (oneP 0) 0) && pc1.all (pieceInB keys (shInB sh1 1) (oneP 1) 1) &&
    idsOkB keys pc0 && idsOkB keys pc1 && lowKeys keys &&
    (ivBelow keys pc0 (0 * slotM4 + arR2) && ivBelow keys pc1 (1 * slotM4 + arR2) &&
      decide (ar0.length ≤ arR2N) && decide (ar1.length ≤ arR2N) && inSlotB 0 (idxAr 0 ar0) &&
      inSlotB 1 (idxAr 1 ar1)) && (repFitS q && repFitB 1 rl1)
  hR := fun h => by
    simp only [Bool.and_eq_true, decide_eq_true_eq] at h
    obtain ⟨⟨⟨⟨⟨⟨h0, h1⟩, i0⟩, i1⟩, hk⟩, ⟨⟨⟨⟨⟨b0, b1⟩, l0⟩, l1⟩, s0⟩, s1⟩⟩, r0, r1⟩ := h
    refine ⟨fun π hπ => ?_, hk, fun π hπ => ?_, fun π hπ => ?_⟩
    · rcases Nat.le_one_iff_eq_zero_or_eq_one.1 hπ with rfl | rfl
      · exact ⟨ok.2.1 ▸ pcIn_spec ok.1 h0, ok.2.1 ▸ idsOkB_spec i0⟩
      · exact ⟨ok.2.2 ▸ pcIn_spec ok.1 h1, ok.2.2 ▸ idsOkB_spec i1⟩
    · rcases Nat.le_one_iff_eq_zero_or_eq_one.1 hπ with rfl | rfl
      · rw [askPI_eq, ← har.1, ← ok.2.1, ← inSlotB_iff]
        exact ⟨ivBelow_spec b0, l0, s0⟩
      · rw [askPI_eq, ← har.2, ← ok.2.2, ← inSlotB_iff]
        exact ⟨ivBelow_spec b1, l1, s1⟩
    · rcases Nat.le_one_iff_eq_zero_or_eq_one.1 hπ with rfl | rfl
      · obtain ⟨bs, hb, rfl⟩ := hq; rw [← hb]; exact repFitS_spec bs r0
      · rw [← hrl]; exact r1
  lk2 := lkArr .N2
  lk4 := lkArr .N4
  lk8 := lkArr .N8
  hlk2 := rfl
  hlk4 := rfl
  hlk8 := rfl
  pkr := pinKeys.map fun k => (k, runsOf k.2 k.1 wfSeg)
  hpkr := fun p hp => by
    obtain ⟨k, -, rfl⟩ := List.mem_map.1 hp
    dsimp only
  ar0 := ar0
  ar1 := ar1
  har := har
  ag0 := grows (2 ^ 11) (2 ^ 12) (idxAr 0 ar0)
  ag1 := grows (2 ^ 11) (2 ^ 12) (idxAr 1 ar1)
  hag := by rw [har.1, har.2]; exact ⟨rfl, rfl⟩
  rp0 := rp0
  rp1 := rp1
  hrp := hrp
  rgF := grows (2 ^ 11) (2 ^ 12) (q.1.map fun p => (p.2, rowFr p.1))
  rgL := grows (2 ^ 11) (2 ^ 12) (q.1.map fun p => (p.2, rowLoc p.1))
  kps := q.2
  hrg := by obtain ⟨bs, hb, rfl⟩ := hq; exact ⟨bs, hb, rfl, rfl, rfl⟩

/-- **Prototype `π`'s template rows**, by the memoized trail (`trailMS`: each template built once). -/
def arOf (π : ℕ) : List Row :=
  (trailMS (tplExt4 (protoF π) (protoR π)) (protoLay π) (protoP π) (askTG π) [] (CS.init (baseR π)) none 0
    (protoProg π).ops []).reverse

theorem arOf_eq (π : ℕ) : arOf π = askRowsT π := trailMS_T _ _ _ _ _ _ (by simp [MOk])

theorem thunk_get' {α : Type} (f : Unit → α) : (Thunk.mk f).get = f () := rfl

/-- Prototype 1's replay rows as row blocks. -/
def spBlk (rt : RT) (P : Params) (c : CS) (op : Op) (o : List Slot) : RBlk := .sp (rt.rows P c op o)

/-- **The plan's data, the ask rows and the replay blocks, one walk per prototype** (CF2: INIT's
proposal 2 with the replay blocks, `compMSXB`; `planData4` is `noncomputable`, not built). -/
def planDataB : (Array GK × Array (List Lin) × Array (List Lin) × List Piece × List Piece) ×
    (List Row × List RBlk) × (List Row × List RBlk) :=
  let ops0 := (protoProg 0).ops
  let ops1 := (protoProg 1).ops
  let l0 := protoLay 0
  let l1 := protoLay 1
  let ks0 := l0.map Prod.fst
  let kms := (ks0 ++ (l1.map Prod.fst).filter (fun k => !ks0.contains k)).map mkKM
  let q0 := compMSXB (tplExt4 (protoF 0) (protoR 0)) l0 (protoP 0) (askTG 0) (N4s.rtC1c 0) blk0 []
    (CS.init (baseR 0)) ops0 none [] none 0 [] []
  let r0 := q0.1
  let q1 := compMSXB (tplExt4 (protoF 1) (protoR 1)) l1 (protoP 1) (askTG 1) (N4s.rtC1c 1) (spBlk (N4s.rtC1c 1))
    r0.2.2 (CS.init (baseR 1)) ops1 none [] none 0 [] []
  let r1 := q1.1
  let p0 := slotRP (oneP 0) kms l0 0 r0.1 r0.2.1.reverse []
  let rps1 := (slotRP (oneP 1) kms l1 (1 * slotM4) r1.1 r1.2.1.reverse p0.2).1
  let g := groupRP p0.1 rps1
  ((g.1, g.2.1, g.2.2.1, piecesOf g.1 g.2.1 (oneP 0) p0.1 g.2.2.2.1, piecesOf g.1 g.2.2.1 (oneP 1) rps1 g.2.2.2.2),
    (q0.2.1.reverse, q0.2.2.reverse), (q1.2.1.reverse, q1.2.2.reverse))

/-- The plan's facts about its data. -/
def DataOk (x : (Array GK × Array (List Lin) × Array (List Lin) × List Piece × List Piece) ×
    (List Row × List RBlk) × (List Row × List RBlk)) : Prop :=
  x.1 = planData4 ∧ x.2.1.1 = askRowsT 0 ∧ x.2.1.2.flatMap RBlk.rows = N4s.repRowsP (N4s.rtC1c 0) 0 ∧
    x.2.2.1 = askRowsT 1 ∧ x.2.2.2.flatMap RBlk.rows = N4s.repRowsP (N4s.rtC1c 1) 1

/-- **The one walk is the plan's data, the ask rows and the replay rows.** -/
theorem planDataB_eq : DataOk planDataB := by
  obtain ⟨-, mr0⟩ := compMSX_T (tplExt4 (protoF 0) (protoR 0)) (protoLay 0) (protoP 0) (baseR 0)
    (protoProg 0).ops (M := []) (by simp [MOk])
  unfold DataOk planDataB
  simp only [compMSXB_eq]
  rw [trailMB_eq _ _ _ _ _ _ _ _ _ _ _ _ _ (by simp [MOk]), trailMB_eq _ _ _ _ _ _ _ _ _ _ _ _ _ mr0]
  simp only [List.append_nil, List.reverse_reverse]
  refine ⟨rfl, rfl, repBlkX_rows _ _ _ _ blk0_rows _ _, rfl, repBlkX_rows _ _ _ _ (fun _ _ _ _ => rfl) _ _⟩

def planOf4D (x : (Array GK × Array (List Lin) × Array (List Lin) × List Piece × List Piece) ×
    (List Row × List RBlk) × (List Row × List RBlk)) (hx : DataOk x) : Plan4 :=
  -- REPF/CF2: each prototype's ask rows and replay blocks from the compile's walk (`planDataB`). The
  -- fallback's thunks recompute the rows from `d` (so that the compiler does not hoist them into a
  -- closed constant). Prototype 0's `rsWeight` ops are prepared (`blkGo`), not built.
  let d := x.1
  have hd : d = planData4 := hx.1
  let k0 := d.1.size - d.1.size
  let b0 := x.2.1
  let b1 := x.2.2
  have hk : k0 = 0 := Nat.sub_self _
  let q := blkGo 0 b0.2 [] []
  have hq : ∃ bs : List RBlk, bs.flatMap RBlk.rows = N4s.repRowsP (N4s.rtC1c 0) 0 ∧ q = blkGo 0 bs [] [] :=
    ⟨b0.2, hx.2.2.1, rfl⟩
  let t0 : Thunk (Array Row) := Thunk.mk fun _ => (arRepOf k0).2.toArray
  let t1 : Thunk (Array Row) := Thunk.mk fun _ => (arRepOf (k0 + 1)).2.toArray
  have h0 : t0.get.toList = N4s.repRowsP (N4s.rtC1c 0) 0 := by
    show (arRepOf k0).2.toArray.toList = _; rw [hk, arRepOf_eq 0, List.toList_toArray]
  have h1 : t1.get.toList = N4s.repRowsP (N4s.rtC1c 1) 1 := by
    show (arRepOf (k0 + 1)).2.toArray.toList = _; rw [hk, arRepOf_eq 1, List.toList_toArray]
  if h : (d.1.map mkKey).all (Key.ok 21) = true then
    mkPlan4 (d.1.map mkKey) d.2.1 d.2.2.1 d.2.2.2.1 d.2.2.2.2
      (mkPats (d.1.map mkKey).size d.2.2.2.1)
      ⟨h, by rw [hd]; exact planData4_rows.1, by rw [hd]; exact planData4_rows.2⟩ b0.1 b1.1
      ⟨hx.2.1, hx.2.2.2.1⟩ (b1.2.flatMap RBlk.rows) hx.2.2.2.2 t0 t1 ⟨h0, h1⟩ q hq
  else
    -- the fallback's rows depend on `d` (`protoRows (k − k)`), so that the compiler does not hoist
    -- `protoRows 0` into a closed constant built at every process start (S-E13's kernel and init traps)
    mkPlan4 #[] #[] #[] [.sp (protoRows (d.1.size - d.1.size))] [.sp (protoRows (d.1.size - d.1.size + 1))] #[]
      ⟨by simp, by rw [Nat.sub_self]; exact List.flatMap_singleton .., by rw [Nat.sub_self]; exact List.flatMap_singleton ..⟩
      b0.1 b1.1 ⟨hx.2.1, hx.2.2.2.1⟩ (b1.2.flatMap RBlk.rows) hx.2.2.2.2 t0 t1 ⟨h0, h1⟩ q hq

/-- **The 4.1 nodes' plan, built once per process** (B-16): from proved pieces, no run-time row
comparison. -/
def planOf4 : Plan4 := planOf4D planDataB planDataB_eq

/-! ## A prototype's value -/

/-- The evaluation tables of a prototype's point. -/
def tb4 (pl : Plan4) (π : ℕ) (t u : ℕ → F) : Tb :=
  tbOf 21 t u (oneP π) (needAll pl.keys (·.A) 12) (needAll pl.keys (·.B) 13 pl.pbs)
    (needAll pl.keys (·.A) 22) (needAll pl.keys (·.B) 24 pl.pbs)

theorem loTab_congr {A : ℕ} {t t' : ℕ → F} (h : ∀ l < A, t l = t' l) : loTab A t = loTab A t' := by
  unfold loTab; congr 1; exact List.map_congr_left fun l hl => h l (List.mem_range.1 hl)

/-- **A key's preparation reads coordinates below its bits only.** -/
theorem kprep_star (s : Mat) (t u : ℕ → F) (π π' : ℕ) {K : Key} (hA : K.A ≤ 20) (hB : K.B ≤ 20) :
    kprep s (starPt t π) (starPt u π) K = kprep s (starPt t π') (starPt u π') K := by
  unfold kprep
  rw [loTab_congr (t := starPt t π) (t' := starPt t π') (fun l hl => by simp [starPt, show l < 20 by omega]),
    loTab_congr (t := starPt u π) (t' := starPt u π') (fun l hl => by simp [starPt, show l < 20 by omega])]

theorem kp_shared (pl : Plan4) (hk : lowKeys pl.keys = true) (t u : ℕ → F) :
    pl.keys.map (kprep3 (tb4 pl 0 (starPt t 0) (starPt u 0)) (starPt t 0) (starPt u 0)) =
      pl.keys.map (kprep3 (tb4 pl 1 (starPt t 1) (starPt u 1)) (starPt t 1) (starPt u 1)) := by
  refine Array.map_congr_left fun K hK => ?_
  have h := Array.all_eq_true_iff_forall_mem.1 hk K hK
  simp only [Bool.and_eq_true, decide_eq_true_eq] at h
  simp only [tb4, kprep3_eq, kprep_star _ t u 0 1 h.1 h.2]

/-- The three matrices of rows, sparse. -/
def rows3 (n m : ℕ) (t u : ℕ → F) (rows : List (ℕ × Row)) : F3 :=
  (rowsVal (RingHom.id F) .a n m t u rows, rowsVal (RingHom.id F) .b n m t u rows,
    rowsVal (RingHom.id F) .c n m t u rows)

theorem rows3_append (n m : ℕ) (t u : ℕ → F) (a b : List (ℕ × Row)) :
    rows3 n m t u (a ++ b) = add3 (rows3 n m t u a) (rows3 n m t u b) := by
  simp [rows3, add3, rowsVal_append]

/-- **Grouped rows' value at a prototype's point** (ASK-P: the template rows, `askPI`), by its split eq
tables over 21 row and 23 cell coordinates (sparse; one product per entry). -/
def askV (G : GRows) (t u : ℕ → F) : F3 :=
  growsVal3 (loTab 11 t) (loTab 10 fun l => t (11 + l)) (loTab 12 u) (loTab 11 fun l => u (12 + l)) G

theorem askV_eq (t u : ℕ → F) (rows : List (ℕ × Row)) :
    askV (grows (2 ^ 11) (2 ^ 12) rows) t u = rows3 21 23 t u rows := by
  have ht : splitAt (loTab 11 t) (loTab 10 fun l => t (11 + l)) (2 ^ 11) = gN 21 t :=
    splitE_eq (m := 21) (s := 11) (by norm_num) t
  have hu : splitAt (loTab 12 u) (loTab 11 fun l => u (12 + l)) (2 ^ 12) = gN 23 u :=
    splitE_eq (m := 23) (s := 12) (by norm_num) u
  unfold askV
  rw [growsVal3_eq, growsVal_grows, growsVal_grows, growsVal_grows, ht, hu, rowsValI_eq, rowsValI_eq,
    rowsValI_eq]
  rfl

/-- **The two prototypes' values at `(t, u)`**: one key preparation, each prototype at its point, its
template rows added (ASK-P). -/
def protoV4 (pl : Plan4) (t u : ℕ → F) (node : Bool) : F3 × F3 :=
  let t0 := starPt t 0; let u0 := starPt u 0; let t1 := starPt t 1; let u1 := starPt u 1
  let tb0 := tb4 pl 0 t0 u0
  let kp := pl.keys.map (kprep3 tb0 t0 u0)
  (if node then add3 (slotV3 (ectx3 21 tb0 t0 u0 pl.keys kp pl.g0 pl.pats) pl.p0) (askV pl.ag0 t0 u0)
   else (0, 0, 0),
   add3 (slotV3 (ectx3 21 (tb4 pl 1 t1 u1) t1 u1 pl.keys kp pl.g1 pl.pats) pl.p1) (askV pl.ag1 t1 u1))

theorem protoV4_eq (pl : Plan4) (hk : lowKeys pl.keys = true) (t u : ℕ → F) (node : Bool) :
    (protoV4 pl t u node).1 =
        (if node then rows3 21 23 (starPt t 0) (starPt u 0) (protoRows 0 ++ askPI 0) else (0, 0, 0)) ∧
      (protoV4 pl t u node).2 = rows3 21 23 (starPt t 1) (starPt u 1) (protoRows 1 ++ askPI 1) := by
  simp only [protoV4]
  refine ⟨?_, ?_⟩
  · split_ifs
    · rw [rows3_append, pl.hag.1, askV_eq]
      refine congrArg (add3 · _) ?_
      simp only [tb4, slotV3_eq]
      rw [pl.hg0, pl.hp0]
      simp only [slotV_eq _ (by norm_num : 11 ≤ 21) _ _ _ _ _ _ _ _ _ _ pl.ok.1, pl.ok.2.1, rows3]
    · rfl
  · rw [kp_shared pl hk, rows3_append, pl.hag.2, askV_eq]
    refine congrArg (add3 · _) ?_
    simp only [tb4, slotV3_eq]
    rw [pl.hg1, pl.hp1]
    simp only [slotV_eq _ (by norm_num : 11 ≤ 21) _ _ _ _ _ _ _ _ _ _ pl.ok.1, pl.ok.2.2, rows3]

/-! ## The copy identity -/

theorem eqN_congr {n : ℕ} {t t' : ℕ → F} (h : ∀ l < n, t l = t' l) (x : ℕ) : eqN n t x = eqN n t' x :=
  Finset.prod_congr rfl fun l hl => by rw [h l (Finset.mem_range.1 hl)]

theorem gN_star {π n : ℕ} (hπ : π ≤ 1) (hn : 21 ≤ n) (t : ℕ → F) {j : ℕ} (hj : j < 2 ^ 20) :
    gN n (starPt t π) (π * slotM4 + j) = eqN 20 t j := by
  have e : π * slotM4 + j = 2 ^ 20 * π + j := by simp only [slotM4]; ring
  rw [e, gN_split (by omega) _ _ hj]
  have h1 : eqN 20 (starPt t π) j = eqN 20 t j := eqN_congr (fun l hl => by simp [starPt, hl]) j
  have h2 : gN (n - 20) (fun l => starPt t π (20 + l)) π = 1 := by
    have hp : π < 2 ^ (n - 20) := lt_of_le_of_lt hπ (Nat.one_lt_two_pow (by omega))
    rw [gN, if_pos hp]; unfold eqN
    refine Finset.prod_eq_one fun l _ => ?_
    rcases Nat.lt_or_ge l 1 with h0 | h0
    · obtain rfl : l = 0 := by omega
      interval_cases π <;> simp [starPt]
    · have hb : π.testBit l = false := Nat.testBit_lt_two_pow (lt_of_le_of_lt hπ
        (lt_of_lt_of_le (by norm_num : 1 < 2 ^ 1) (Nat.pow_le_pow_right (by norm_num) h0)))
      simp only [hb, Bool.false_eq_true, if_false, starPt, show ¬ 20 + l < 20 by omega,
        show 20 + l ≠ 20 by omega, sub_zero]
  rw [h1, h2, mul_one]

/-- The high factor of slot `σ`: `eq(t_[20,lm), σ)`. -/
def hiF (lm : ℕ) (t : ℕ → F) (σ : ℕ) : F := eqN (lm - 20) (fun l => t (20 + l)) σ

theorem gN_row {lm σ : ℕ} (hl : 20 ≤ lm) (hσ : σ < 2 ^ (lm - 20)) (t : ℕ → F) {j : ℕ} (hj : j < 2 ^ 20) :
    gN lm t (σ * slotM4 + j) = eqN 20 t j * hiF lm t σ := by
  have e : σ * slotM4 + j = 2 ^ 20 * σ + j := by simp only [slotM4]; ring
  rw [e, gN_split hl _ _ hj, gN, if_pos hσ, hiF]

theorem gN_two (v : ℕ → F) : gN 2 v 3 = v 0 * v 1 := by
  rw [gN, if_pos (by norm_num), eqN]
  simp only [Finset.prod_range_succ, Finset.prod_range_zero, one_mul]
  simp only [show (3 : ℕ).testBit 0 = true by decide, show (3 : ℕ).testBit 1 = true by decide, if_true]

theorem gN_cell {lm σ : ℕ} (hl : 20 ≤ lm) (hσ : σ < 2 ^ (lm - 20)) (u : ℕ → F) {x : ℕ} (hx : x < 2 ^ 20) :
    gN (lm + 2) u (σ * slotM4 + x + 3 * 2 ^ lm) = eqN 20 u x * (hiF lm u σ * (u lm * u (lm + 1))) := by
  have e : σ * slotM4 + x + 3 * 2 ^ lm = 2 ^ 20 * (2 ^ (lm - 20) * 3 + σ) + x := by
    rw [show 2 ^ lm = 2 ^ 20 * 2 ^ (lm - 20) by rw [← pow_add]; congr 1; omega]; simp only [slotM4]; ring
  rw [e, gN_split (by omega) _ _ hx, gN_split (by omega) _ _ hσ, hiF]
  have e2 : lm + 2 - 20 - (lm - 20) = 2 := by omega
  rw [e2, gN_two]
  have e3 : 20 + (lm - 20 + 0) = lm := by omega
  have e4 : 20 + (lm - 20 + 1) = lm + 1 := by omega
  simp only [e3, e4]

theorem r_rowMapC (s : Mat) (f : ℕ → ℕ) (r : Row) : s.r (rowMapC f r) = mapC f (s.r r) := by cases s <;> rfl

/-- One entry of a moved, absolute row against the prototype's. -/
theorem copy_term {π σ lm : ℕ} (hπ : π ≤ 1) (hl : 20 ≤ lm) (hσ : σ < 2 ^ (lm - 20)) (u : ℕ → F)
    {q : ℕ × F} (hq : π * slotM4 ≤ q.1 ∧ q.1 < π * slotM4 + slotM4) :
    q.2 * gN (lm + 2) u (mvC π σ q.1 + 3 * 2 ^ lm) =
      (hiF lm u σ * (u lm * u (lm + 1))) * (q.2 * gN 23 (starPt u π) q.1) := by
  obtain ⟨hq1, hq2⟩ := hq
  have hx : q.1 - π * slotM4 < 2 ^ 20 := by
    have : slotM4 = 2 ^ 20 := rfl
    omega
  have ec : mvC π σ q.1 + 3 * 2 ^ lm = σ * slotM4 + (q.1 - π * slotM4) + 3 * 2 ^ lm := by
    simp only [mvC]; omega
  have eq' : gN 23 (starPt u π) q.1 = gN 23 (starPt u π) (π * slotM4 + (q.1 - π * slotM4)) := by
    rw [Nat.add_sub_cancel' hq1]
  rw [ec, gN_cell hl hσ u hx, eq', gN_star hπ (by norm_num) u hx]
  ring

/-- **One moved, absolute row** against the prototype's. -/
theorem copy_row {π σ lm : ℕ} (hπ : π ≤ 1) (hl : 20 ≤ lm) (hσ : σ < 2 ^ (lm - 20)) (s : Mat) (t u : ℕ → F)
    {p : ℕ × Row} (hp : (π * slotM4 ≤ p.1 ∧ p.1 + linkN < π * slotM4 + slotM4) ∧
      ∀ s' : Mat, ∀ q ∈ s'.r p.2, π * slotM4 ≤ q.1 ∧ q.1 < π * slotM4 + slotM4) :
    gN lm t (mvC π σ p.1) * linE (RingHom.id F) (lm + 2) u
        (s.r (rowMapC (· + 3 * 2 ^ lm) (rowMapC (mvC π σ) p.2))) =
      (hiF lm t σ * (hiF lm u σ * (u lm * u (lm + 1)))) *
        (gN 21 (starPt t π) p.1 * linE (RingHom.id F) 23 (starPt u π) (s.r p.2)) := by
  obtain ⟨⟨h1, h2⟩, hc⟩ := hp
  have hj : p.1 - π * slotM4 < 2 ^ 20 := by
    have : slotM4 = 2 ^ 20 := rfl
    omega
  have er : mvC π σ p.1 = σ * slotM4 + (p.1 - π * slotM4) := by simp only [mvC]; omega
  have ep : gN 21 (starPt t π) p.1 = gN 21 (starPt t π) (π * slotM4 + (p.1 - π * slotM4)) := by
    rw [Nat.add_sub_cancel' h1]
  have hL : linE (RingHom.id F) (lm + 2) u (s.r (rowMapC (· + 3 * 2 ^ lm) (rowMapC (mvC π σ) p.2))) =
      (hiF lm u σ * (u lm * u (lm + 1))) * linE (RingHom.id F) 23 (starPt u π) (s.r p.2) := by
    rw [r_rowMapC, r_rowMapC]
    simp only [linE, mapC, List.map_map, Function.comp_def, RingHom.id_apply]
    rw [← List.sum_map_mul_left]
    refine congrArg List.sum (List.map_congr_left fun q hq => ?_)
    exact copy_term hπ hl hσ u (hc s q hq)
  rw [er, gN_row hl hσ t hj, hL, ep, gN_star hπ (le_refl _) t hj]
  ring

/-- **A slot's value is its prototype's, scaled** (the region facts given). -/
theorem copy_val {π σ lm : ℕ} (hπ : π ≤ 1) (hl : 20 ≤ lm) (hσ : σ < 2 ^ (lm - 20)) (s : Mat) (t u : ℕ → F)
    {rows : List (ℕ × Row)} (hR : InSlot π rows) :
    rowsVal (RingHom.id F) s lm (lm + 2) t u
        ((mvRows π σ rows).map fun p => (p.1, rowMapC (· + 3 * 2 ^ lm) p.2)) =
      (hiF lm t σ * (hiF lm u σ * (u lm * u (lm + 1)))) * rowsVal (RingHom.id F) s 21 23 (starPt t π) (starPt u π) rows := by
  simp only [rowsVal, mvRows, List.map_map, Function.comp_def]
  rw [← List.sum_map_mul_left]
  exact congrArg List.sum (List.map_congr_left fun p hp => copy_row hπ hl hσ s t u (hR p hp))

/-! ## The replay rows' value (REPF)

Slot 0's replay rows (`N2`, `N4`) sit at rows `κ.vslots·2^20 + k`; their frame cells at `oneCell + c`
(region 0), their locals at `oneCell + κ.vslots·2^20 + (c − repB)`. So their value is the local
coordinates' values of the frame part and the local part (`repLocF`, `repLocL`, kind-independent),
scaled by the regions' high factors (`repV0_eq`). -/

theorem gN_lo {x : ℕ} (hx : x < 2 ^ 20) (t : ℕ → F) : gN 20 t x = eqN 20 t x := by rw [gN, if_pos hx]

/-- The previous node's slot's spare region exists. -/
theorem vslots_lt {κ : NodeKind} (hp : κ.hasPrev = true) : κ.vslots < 2 ^ (κ.dims.logM - 20) := by
  cases κ <;> first | exact absurd hp (by decide) | decide

/-- One term of a replay form, moved by `repMapC κ 0`, against the local coordinates. -/
theorem repMapC_term {κ : NodeKind} (hp : κ.hasPrev = true) (u : ℕ → F) {q : ℕ × F}
    (hq : repCellOk 0 q.1 = true) :
    q.2 * gN (κ.dims.logM + 2) u (N4s.repMapC κ 0 q.1) =
      if q.1 < N4s.repB then (hiF κ.dims.logM u 0 * (u κ.dims.logM * u (κ.dims.logM + 1))) * (q.2 * gN 20 u q.1)
      else (hiF κ.dims.logM u κ.vslots * (u κ.dims.logM * u (κ.dims.logM + 1))) * (q.2 * gN 20 u (q.1 - N4s.repB)) := by
  have hl : 20 ≤ κ.dims.logM := by cases κ <;> decide
  have hv := vslots_lt hp
  have hM : slotM4 = 2 ^ 20 := rfl
  have hB : N4s.repB = 2 ^ 40 := rfl
  have h0 : (0 : ℕ) < 2 ^ (κ.dims.logM - 20) := Nat.two_pow_pos _
  simp only [repCellOk, if_true, Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq] at hq
  have hp0 : protoOf κ 0 = 0 := by simp [protoOf, isPrevSlot, hp]
  simp only [N4s.repMapC, hp0, mvC, oneCell_eq]
  split_ifs with h
  · have hx : q.1 < 2 ^ 20 := by rcases hq with hq | hq <;> omega
    have := gN_cell hl h0 u hx
    rw [show 0 * slotM4 + q.1 + 3 * 2 ^ κ.dims.logM = q.1 - 0 * slotM4 + 0 * slotM4 + 3 * 2 ^ κ.dims.logM by
      simp] at this
    rw [this, gN_lo hx]; ring
  · have hx : q.1 - N4s.repB < 2 ^ 20 := by rcases hq with hq | hq <;> omega
    rw [gN_cell hl hv u hx, gN_lo hx]; ring

/-- A replay form's value at the node, from its parts' local values. -/
theorem linE_rep {κ : NodeKind} (hp : κ.hasPrev = true) (u : ℕ → F) :
    ∀ (l : Lin), (∀ q ∈ l, repCellOk 0 q.1 = true) →
      linE (RingHom.id F) (κ.dims.logM + 2) u (mapC (N4s.repMapC κ 0) l) =
        (hiF κ.dims.logM u 0 * (u κ.dims.logM * u (κ.dims.logM + 1))) * linE (RingHom.id F) 20 u (linFr l) +
        (hiF κ.dims.logM u κ.vslots * (u κ.dims.logM * u (κ.dims.logM + 1))) *
          linE (RingHom.id F) 20 u (linLoc l)
  | [], _ => by simp [linE, mapC, linFr, linLoc]
  | q :: l, h => by
    have ih := linE_rep hp u l fun q' hq' => h q' (List.mem_cons_of_mem _ hq')
    have hq := repMapC_term hp u (h q (List.mem_cons_self ..))
    have ec : ∀ (m : ℕ) (v : ℕ → F) (x : ℕ × F) (l' : Lin),
        linE (RingHom.id F) m v (x :: l') = x.2 * gN m v x.1 + linE (RingHom.id F) m v l' := fun _ _ _ _ => by
      simp [linE]
    have em : mapC (N4s.repMapC κ 0) (q :: l) = (N4s.repMapC κ 0 q.1, q.2) :: mapC (N4s.repMapC κ 0) l := rfl
    by_cases h1 : q.1 < N4s.repB
    · rw [if_pos h1] at hq
      have e1 : linFr (q :: l) = q :: linFr l := List.filter_cons_of_pos (by simpa using h1)
      have e2 : linLoc (q :: l) = linLoc l := by
        simp only [linLoc]; rw [List.filter_cons_of_neg (by simpa using h1)]
      rw [em, e1, e2, ec, ec, ih]; dsimp only; rw [hq]; ring
    · rw [if_neg h1] at hq
      have e1 : linFr (q :: l) = linFr l := List.filter_cons_of_neg (by simpa using h1)
      have e2 : linLoc (q :: l) = (q.1 - N4s.repB, q.2) :: linLoc l := by
        simp only [linLoc]; rw [List.filter_cons_of_pos (by simpa using h1)]; rfl
      rw [em, e1, e2, ec, ec, ih]; dsimp only; rw [hq]; ring

/-- A replay row list's fit facts (`repFitB 0`). -/
theorem repFitB0_spec {rows : List Row} (h : repFitB 0 rows = true) :
    rows.length ≤ slotM4 ∧ ∀ r ∈ rows, ∀ t ∈ r.a ++ r.b ++ r.c, repCellOk 0 t.1 = true := by
  simp only [repFitB, if_true, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true] at h
  exact ⟨h.1, h.2⟩

/-- **Slot 0's replay rows' value, one matrix** (`N2`, `N4`): the frame and local parts' local values,
scaled by the regions' high factors. -/
theorem repV0_eq {κ : NodeKind} (hp : κ.hasPrev = true) (t u : ℕ → F) {rows : List Row}
    (hfit : repFitB 0 rows = true) (s : Mat) :
    rowsVal (RingHom.id F) s κ.dims.logM (κ.dims.logM + 2) t u
        (rows.zipIdx.map fun p => (κ.vslots * slotM4 + p.2, rowMapC (N4s.repMapC κ 0) p.1)) =
      (hiF κ.dims.logM t κ.vslots * (u κ.dims.logM * u (κ.dims.logM + 1))) *
        (hiF κ.dims.logM u 0 * rowsVal (RingHom.id F) s 20 20 t u (repLocF rows) +
          hiF κ.dims.logM u κ.vslots * rowsVal (RingHom.id F) s 20 20 t u (repLocL rows)) := by
  have hl : 20 ≤ κ.dims.logM := by cases κ <;> decide
  obtain ⟨hlen, hcell⟩ := repFitB0_spec hfit
  simp only [rowsVal, repLocF, repLocL, List.map_map, Function.comp_def]
  rw [← List.sum_map_mul_left, ← List.sum_map_mul_left, ← List.sum_map_add, ← List.sum_map_mul_left]
  refine congrArg List.sum (List.map_congr_left fun p hp' => ?_)
  obtain ⟨r, k⟩ := p
  obtain ⟨hkl, hr⟩ := List.getElem?_eq_some_iff.1 (List.mk_mem_zipIdx_iff_getElem?.1 hp')
  have hk : k < 2 ^ 20 := lt_of_lt_of_le hkl hlen
  have hrm : r ∈ rows := hr ▸ List.getElem_mem hkl
  have hc : ∀ q ∈ s.r r, repCellOk 0 q.1 = true := fun q hq =>
    hcell r hrm q (by cases s <;> simp only [Mat.r] at hq <;> simp [hq])
  dsimp only
  rw [r_rowMapC, linE_rep hp u _ hc, gN_row hl (vslots_lt hp) t hk, gN_lo hk, r_rowFr, r_rowLoc]
  ring

/-! ## `evalM` -/

/-- `c · x` over triples. -/
def smul3 (c : F) (x : F3) : F3 := (c * x.1, c * x.2.1, c * x.2.2)

/-- **The link regions' eq tables** (S-E13a; once per evaluation point): `eq(τ, ·)` over `lm` row
coordinates split at `2^11`, `eq(u, ·)` over `lm + 2` cell coordinates split at `2^12`. -/
structure LTb where
  tlo : Array F
  thi : Array F
  slo : Array F
  shi : Array F

/-- The tables at a point. -/
def ltbOf (lm : ℕ) (t u : ℕ → F) : LTb :=
  ⟨loTab 11 t, loTab (lm - 11) (fun l => t (11 + l)), loTab 12 u, loTab (lm + 2 - 12) (fun l => u (12 + l))⟩

/-- **The pinned elements' value** (S-E13a): the rows `pinRow one (sCell b0 e) c` of the list
`ps`, at indices `j, j + 1, …`: for each, the row factor `r = eq(τ, j)` times `E(one)` (matrix
`a`) and times `E(cell) − c·E(one)` (matrix `b`); one product per factor. -/
def wfSum (gt gs : ℕ → F) (e1 : F) (b0 : ℕ) : ℕ → List (ℕ × F) → F3
  | _, [] => (0, 0, 0)
  | j, p :: ps =>
    let r := gt j
    add3 (r * e1, r * (gs (sCell b0 p.1) - p.2 * e1), 0) (wfSum gt gs e1 b0 (j + 1) ps)

theorem rows3_nil (n m : ℕ) (t u : ℕ → F) : rows3 n m t u [] = (0, 0, 0) := by
  simp [rows3, rowsVal]

theorem rows3_cons (n m : ℕ) (t u : ℕ → F) (p : ℕ × Row) (l : List (ℕ × Row)) :
    rows3 n m t u (p :: l) = add3 (rows3 n m t u [p]) (rows3 n m t u l) := by
  rw [← rows3_append]; rfl

/-- **`wfSum` is the pin rows' sparse value.** -/
theorem wfSum_eq (n m : ℕ) (t u : ℕ → F) (one b0 base : ℕ) :
    ∀ (ps : List (ℕ × F)) (k : ℕ),
      rows3 n m t u (((ps.map fun p => pinRow one (sCell b0 p.1) p.2).zipIdx k).map
        fun q => (base + q.2, q.1)) = wfSum (gN n t) (gN m u) (gN m u one) b0 (base + k) ps
  | [], _ => by simp [wfSum, rows3_nil]
  | p :: ps, k => by
    rw [List.map_cons, List.zipIdx_cons, List.map_cons, rows3_cons, wfSum_eq n m t u one b0 base ps (k + 1),
      wfSum, show base + (k + 1) = base + k + 1 by omega]
    congr 1
    simp only [rows3, rowsVal, linE, pinRow, Mat.r, Lin.sub, Lin.cell, Lin.smul, List.map_cons,
      List.map_nil, List.sum_cons, List.sum_nil, List.cons_append, List.nil_append, RingHom.id_apply]
    refine Prod.ext ?_ (Prod.ext ?_ ?_) <;> simp only <;> ring

/-! ### The pinned elements by runs and by value (B5, lever (b)) -/

/-- The pinned elements' inner sums at the low tables: per run `Σ tlo[x]·slo[c]`, per value and row
block `Σ tlo[x]` (additions only). They read the low tables only, so the kinds share them. -/
abbrev PIn := List (ℕ × ℕ × F) × List (F × List (ℕ × F))

/-- The inner sums. -/
def prIn (tlo slo : Array F) (R : List PRun × PCls) : PIn :=
  (R.1.map fun r => (r.1, r.2.1, sumL (fun it => tlo.getD it.1 0 * slo.getD it.2 0) r.2.2),
   R.2.map fun c => (c.1, c.2.map fun g => (g.1, sumL (fun l => tlo.getD l 0) g.2)))

/-- **The pinned elements' value from the inner sums**: with `B = Σ_r thi[r]·shi[r]·ΣB`,
`A = Σ_{k, h} thi[h]·Σ_h` and `C = Σ_k k·Σ_h thi[h]·Σ_h`, the value `(e1·A, B − e1·C, 0)` (`wfSum`'s;
`prVal_runs`). Two products per run and one per value and row block, not five per element. -/
def prVal (thi shi : Array F) (e1 : F) (I : PIn) : F3 :=
  let b := sumL (fun r => thi.getD r.1 0 * shi.getD r.2.1 0 * r.2.2) I.1
  let ys := I.2.map fun c => (c.1, sumL (fun g => thi.getD g.1 0 * g.2) c.2)
  (e1 * sumL (fun y => y.2) ys, b - e1 * sumL (fun y => y.1 * y.2) ys, 0)

/-- The three sums, as plain sums (`prVal`'s specification). -/
def prA (tlo thi : Array F) (C : PCls) : F :=
  (C.map fun c => (c.2.map fun g => thi.getD g.1 0 * (g.2.map fun l => tlo.getD l 0).sum).sum).sum
def prB (tlo thi slo shi : Array F) (R : List PRun) : F :=
  (R.map fun r => thi.getD r.1 0 * shi.getD r.2.1 0 *
    (r.2.2.map fun it => tlo.getD it.1 0 * slo.getD it.2 0).sum).sum
def prC (tlo thi : Array F) (C : PCls) : F :=
  (C.map fun c => c.1 * (c.2.map fun g => thi.getD g.1 0 * (g.2.map fun l => tlo.getD l 0).sum).sum).sum

theorem prVal_eq (tlo thi slo shi : Array F) (e1 : F) (R : List PRun × PCls) :
    prVal thi shi e1 (prIn tlo slo R) =
      (e1 * prA tlo thi R.2, prB tlo thi slo shi R.1 - e1 * prC tlo thi R.2, 0) := by
  simp only [prVal, prIn, sumL_eq, List.map_map, Function.comp_def, prA, prB, prC]

theorem prStep_val (tlo thi slo shi : Array F) (x c : ℕ) (R : List PRun) :
    prB tlo thi slo shi (prStep x c R) =
      splitAt tlo thi (2 ^ 11) x * splitAt slo shi (2 ^ 12) c + prB tlo thi slo shi R := by
  cases R with
  | nil => simp only [prStep, prB, splitAt, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
      add_zero]; ring
  | cons r rs =>
    simp only [prStep]
    split_ifs with h
    · obtain ⟨h1, h2⟩ := h
      simp only [prB, splitAt, List.map_cons, List.sum_cons, h1, h2]
      ring
    · simp only [prB, splitAt, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero]
      ring

theorem blkIns_val (tlo thi : Array F) (x : ℕ) (G : List (ℕ × List ℕ)) :
    ((blkIns x G).map fun g => thi.getD g.1 0 * (g.2.map fun l => tlo.getD l 0).sum).sum =
      splitAt tlo thi (2 ^ 11) x + (G.map fun g => thi.getD g.1 0 * (g.2.map fun l => tlo.getD l 0).sum).sum := by
  cases G with
  | nil => simp only [blkIns, splitAt, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
      add_zero]; ring
  | cons g gs =>
    simp only [blkIns]
    split_ifs with h
    · simp only [splitAt, List.map_cons, List.sum_cons, h]; ring
    · simp only [splitAt, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero]; ring

theorem clsIns_val (tlo thi : Array F) (k : F) (x : ℕ) :
    ∀ C : PCls, prA tlo thi (clsIns k x C) = splitAt tlo thi (2 ^ 11) x + prA tlo thi C ∧
      prC tlo thi (clsIns k x C) = k * splitAt tlo thi (2 ^ 11) x + prC tlo thi C
  | [] => by
    simp only [clsIns, prA, prC, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero,
      blkIns_val]
    constructor <;> first | trivial | ring
  | c :: cs => by
    simp only [clsIns]
    split_ifs with h
    · simp only [prA, prC, List.map_cons, List.sum_cons, blkIns_val, h]
      constructor <;> ring
    · obtain ⟨hA, hC⟩ := clsIns_val tlo thi k x cs
      simp only [prA, prC, List.map_cons, List.sum_cons] at hA hC ⊢
      rw [hA, hC]; constructor <;> ring

/-- **The runs and classes give the pinned elements' value** (`wfSum`). -/
theorem prVal_runs (tlo thi slo shi : Array F) (e1 : F) (b0 : ℕ) :
    ∀ (j : ℕ) (ps : List (ℕ × F)), prVal thi shi e1 (prIn tlo slo (runsOf b0 j ps)) =
      wfSum (splitAt tlo thi (2 ^ 11)) (splitAt slo shi (2 ^ 12)) e1 b0 j ps
  | _, [] => by
    simp only [prVal_eq, runsOf, wfSum, prA, prB, prC, List.map_nil, List.sum_nil, mul_zero, sub_zero]
  | j, p :: ps => by
    have ih := prVal_runs tlo thi slo shi e1 b0 (j + 1) ps
    rw [prVal_eq] at ih ⊢
    obtain ⟨hA, hC⟩ := clsIns_val tlo thi p.2 j (runsOf b0 (j + 1) ps).2
    simp only [runsOf, prStep_val, hA, hC, wfSum, ← ih, add3]
    refine Prod.ext ?_ (Prod.ext ?_ ?_) <;> simp only <;> ring

/-! ### The node rows' value over the dictionary -/

/-- `w · Σ c·E[i]` of a coded form, no product for an empty form. -/
@[inline] def cfVal (E : Array F) (w : F) (f : CForm) : F :=
  match f with
  | [] => 0
  | _ => w * sumL (fun e => cmulF e.2 (E.getD e.1 0)) f

/-- **The coded rows' three values**, `E` the dictionary's cells' `eq` values. -/
def crowsVal3 (tlo thi E : Array F) (G : CRows) : F3 :=
  sum3 (fun h =>
    let x := sum3 (fun r => let w := tlo.getD r.1 0; (cfVal E w r.2.1, cfVal E w r.2.2.1, cfVal E w r.2.2.2)) h.2
    let y := thi.getD h.1 0
    (y * x.1, y * x.2.1, y * x.2.2)) G

theorem cfVal_eq (E : Array F) (w : F) (f : CForm) :
    cfVal E w f = w * (f.map fun e => e.2 * E.getD e.1 0).sum := by
  cases f with
  | nil => simp [cfVal]
  | cons _ _ => simp only [cfVal, sumL_eq, cmulF_eq]

theorem getD_map_lt (cs : Array ℕ) (g : ℕ → F) {i : ℕ} (h : i < cs.size) :
    (cs.map g).getD i 0 = g (cs.getD i 0) := by
  simp [Array.getD_eq_getD_getElem?, Array.getElem?_map, Array.getElem?_eq_getElem h]

theorem linEI_decF (cs : Array ℕ) (g : ℕ → F) (f : CForm) (hf : ∀ e ∈ f, e.1 < cs.size) :
    linEI (RingHom.id F) g (decF cs f) = (f.map fun e => e.2 * (cs.map g).getD e.1 0).sum := by
  simp only [linEI, decF, sumL_eq, List.map_map, Function.comp_def, cmul_eq, RingHom.id_apply]
  exact congrArg List.sum (List.map_congr_left fun e he => by rw [getD_map_lt cs g (hf e he)])

theorem sum_flatMap' {α : Type} (l : List α) (f : α → List F) :
    (l.flatMap f).sum = (l.map fun a => (f a).sum).sum := by
  induction l with
  | nil => simp
  | cons a l ih => simp [List.flatMap_cons, List.sum_append, ih]

/-- One matrix of the coded rows (`sel` its forms, `s` the decoded rows' matrix). -/
theorem crows_sel (tlo thi slo shi : Array F) (cs : Array ℕ) (G : CRows) (hb : cbnd cs G = true)
    (sel : ℕ × CForm × CForm × CForm → CForm) (s : Mat)
    (hs : ∀ h r, s.r (decR cs h r).2 = decF cs (sel r))
    (hsel : ∀ r, ∀ e ∈ sel r, e ∈ r.2.1 ++ r.2.2.1 ++ r.2.2.2) :
    (G.map fun g => thi.getD g.1 0 * (g.2.map fun r => cfVal (cs.map (splitAt slo shi (2 ^ 12)))
        (tlo.getD r.1 0) (sel r)).sum).sum =
      rowsValI (RingHom.id F) s (splitAt tlo thi (2 ^ 11)) (splitAt slo shi (2 ^ 12)) (decRows cs G) := by
  simp only [rowsValI, decRows, sumL_eq, List.map_flatMap, sum_flatMap', List.map_map,
    Function.comp_def]
  refine congrArg List.sum (List.map_congr_left fun g hg => ?_)
  rw [← List.sum_map_mul_left]
  refine congrArg List.sum (List.map_congr_left fun r hr => ?_)
  have hgb := List.all_eq_true.1 hb g hg
  have hrb := List.all_eq_true.1 hgb r hr
  simp only [Bool.and_eq_true, decide_eq_true_eq] at hrb
  obtain ⟨hlo, hix⟩ := hrb
  rw [hs, linEI_decF cs _ _ fun e he => by
    simpa using List.all_eq_true.1 hix e (hsel r e he), cfVal_eq]
  have e1 : (g.1 * 2 ^ 11 + r.1) % 2 ^ 11 = r.1 := by omega
  have e2 : (g.1 * 2 ^ 11 + r.1) / 2 ^ 11 = g.1 := by omega
  simp only [decR, splitAt, e1, e2]
  ring

/-- **The coded rows' value is the decoded rows'** (in bounds). -/
theorem crowsVal3_eq (tlo thi slo shi : Array F) (cs : Array ℕ) (G : CRows) (hb : cbnd cs G = true) :
    crowsVal3 tlo thi (cs.map (splitAt slo shi (2 ^ 12))) G =
      (rowsValI (RingHom.id F) .a (splitAt tlo thi (2 ^ 11)) (splitAt slo shi (2 ^ 12)) (decRows cs G),
       rowsValI (RingHom.id F) .b (splitAt tlo thi (2 ^ 11)) (splitAt slo shi (2 ^ 12)) (decRows cs G),
       rowsValI (RingHom.id F) .c (splitAt tlo thi (2 ^ 11)) (splitAt slo shi (2 ^ 12)) (decRows cs G)) := by
  rw [← crows_sel tlo thi slo shi cs G hb (·.2.1) .a (fun _ _ => rfl) (fun _ _ he => by simp [he]),
    ← crows_sel tlo thi slo shi cs G hb (·.2.2.1) .b (fun _ _ => rfl) (fun _ _ he => by simp [he]),
    ← crows_sel tlo thi slo shi cs G hb (·.2.2.2) .c (fun _ _ => rfl) (fun _ _ he => by simp [he])]
  simp only [crowsVal3, sum3_eq, sumL_eq]

/-! ### The link region's value -/

/-- **The link regions' per-call context**: the tables at the point, and the plan's pinned runs'
inner sums, each a thunk (computed by the first kind that reads it, shared with the others). -/
structure LCx where
  L : LTb
  ths : List ((ℕ × ℕ) × Thunk PIn)
  /-- The previous node's replay rows' frame and local values in local coordinates (REPF; once per
  call, shared by `N2` and `N4`). -/
  rv : Thunk (F3 × F3)

/-- The thunks of the plan's runs at the low tables. -/
def thsOf (pl : Plan4) (tlo slo : Array F) : List ((ℕ × ℕ) × Thunk PIn) :=
  pl.pkr.map fun p => (p.1, Thunk.mk fun _ => prIn tlo slo p.2)

/-- The inner sums of the runs at `(first row, stream block)` (regrouped if the plan lacks the key). -/
def innAt (cx : LCx) (k : ℕ × ℕ) : PIn :=
  match cx.ths.find? fun p => decide (p.1 = k) with
  | some p => p.2.get
  | none => prIn cx.L.tlo cx.L.slo (runsOf k.2 k.1 wfSeg)

theorem thunk_get {α : Type} (f : Unit → α) : (Thunk.mk f).get = f () := rfl

theorem innAt_thsOf (pl : Plan4) (L : LTb) (rv : Thunk (F3 × F3)) (k : ℕ × ℕ) :
    innAt ⟨L, thsOf pl L.tlo L.slo, rv⟩ k = prIn L.tlo L.slo (runsOf k.2 k.1 wfSeg) := by
  unfold innAt
  split
  · rename_i p hp
    have hk := List.find?_some hp
    simp only [decide_eq_true_eq] at hk
    obtain ⟨q, hq, rfl⟩ := List.mem_map.1 (List.mem_of_find?_eq_some hp)
    dsimp only at hk ⊢
    rw [thunk_get, pl.hpkr q hq, hk]
  · dsimp only

/-- **The replay rows' local values** (REPF): the frame and local parts of prototype 0's replay rows
at `(t, u)`'s low 20 coordinates (split tables `2^11 × 2^9`, `2^12 × 2^8`; the low halves shared).
CF2: the row blocks' grouped rows sparse, the `rsWeight` ops in closed form (`kopV`: frame part at
`wF`, locals `0`; local part at `wL`, locals `eq(u, 2^16 + ·)`). -/
def rvOf (pl : Plan4) (tlo slo : Array F) (t u : ℕ → F) : Thunk (F3 × F3) :=
  Thunk.mk fun _ =>
    let thi := loTab 9 fun l => t (11 + l)
    let shi := loTab 8 fun l => u (12 + l)
    let gt := splitAt tlo thi (2 ^ 11)
    let gu := splitAt slo shi (2 ^ 12)
    (add3 (growsVal3 tlo thi slo shi pl.rgF) (kpsV3F gt gu t u (wFA gu) 0 pl.kps),
      add3 (growsVal3 tlo thi slo shi pl.rgL) (kpsV3F gt gu t u (wLA gu) 1 pl.kps))

theorem repV_eq (t u : ℕ → F) (rows : List (ℕ × Row)) :
    growsVal3 (loTab 11 t) (loTab 9 fun l => t (11 + l)) (loTab 12 u) (loTab 8 fun l => u (12 + l))
      (grows (2 ^ 11) (2 ^ 12) rows) = rows3 20 20 t u rows := by
  have ht : splitAt (loTab 11 t) (loTab 9 fun l => t (11 + l)) (2 ^ 11) = gN 20 t :=
    splitE_eq (m := 20) (s := 11) (by norm_num) t
  have hu : splitAt (loTab 12 u) (loTab 8 fun l => u (12 + l)) (2 ^ 12) = gN 20 u :=
    splitE_eq (m := 20) (s := 12) (by norm_num) u
  rw [growsVal3_eq, growsVal_grows, growsVal_grows, growsVal_grows, ht, hu, rowsValI_eq, rowsValI_eq,
    rowsValI_eq]
  rfl

theorem rvOf_get (pl : Plan4) (t u : ℕ → F) : (rvOf pl (loTab 11 t) (loTab 12 u) t u).get =
    (rows3 20 20 t u (repLocF (N4s.repRowsP (N4s.rtC1c 0) 0)), rows3 20 20 t u (repLocL (N4s.repRowsP (N4s.rtC1c 0) 0))) := by
  obtain ⟨bs, hbs, hF, hL, hk⟩ := pl.hrg
  have ht : splitAt (loTab 11 t) (loTab 9 fun l => t (11 + l)) (2 ^ 11) = gN 20 t :=
    splitE_eq (m := 20) (s := 11) (by norm_num) t
  have hu : splitAt (loTab 12 u) (loTab 8 fun l => u (12 + l)) (2 ^ 12) = gN 20 u :=
    splitE_eq (m := 20) (s := 12) (by norm_num) u
  rw [rvOf, thunk_get]
  dsimp only
  rw [kpsV3F_eq _ _ _ _ _ _ _ (congrFun ht), kpsV3F_eq _ _ _ _ _ _ _ (congrFun ht), hF, hL, hk, repV_eq, repV_eq, ht, hu, wFA_eq _ u (fun _ => rfl), wLA_eq _ u (fun _ => rfl), ← hbs]
  simp only [rows3, add3, kpsV3, rowsVal_spF, rowsVal_spL, repLocF, repLocL, spV_zipIdx,
    blk_val _ t u _ _ (wF_cb u), blk_val _ t u _ _ (wL_cb u)]

/-- **`cx` is the context at `(t, u)`** over `lm` row coordinates. -/
def CxAt (cx : LCx) (lm : ℕ) (t u : ℕ → F) : Prop :=
  cx.L = ltbOf lm t u ∧ (∀ k, innAt cx k = prIn cx.L.tlo cx.L.slo (runsOf k.2 k.1 wfSeg)) ∧
    cx.rv.get = (rows3 20 20 t u (repLocF (N4s.repRowsP (N4s.rtC1c 0) 0)),
      rows3 20 20 t u (repLocL (N4s.repRowsP (N4s.rtC1c 0) 0)))

theorem ltbOf_lo (lm : ℕ) (t u : ℕ → F) : (ltbOf lm t u).tlo = loTab 11 t ∧ (ltbOf lm t u).slo = loTab 12 u := by
  simp only [ltbOf, and_self]

theorem cxAt_mk (pl : Plan4) (lm : ℕ) (t u : ℕ → F) (L : LTb) (hL : L = ltbOf lm t u) :
    CxAt ⟨L, thsOf pl L.tlo L.slo, rvOf pl L.tlo L.slo t u⟩ lm t u := by
  refine ⟨hL, innAt_thsOf pl L (rvOf pl L.tlo L.slo t u), ?_⟩
  rw [(congrArg LTb.tlo hL).trans (ltbOf_lo lm t u).1, (congrArg LTb.slo hL).trans (ltbOf_lo lm t u).2]
  exact rvOf_get pl t u

/-- `cxAt_mk` at a table literal (its low tables named, so that no `loTab` is unfolded). -/
theorem cxAt_lo (pl : Plan4) (lm : ℕ) (t u : ℕ → F) (lo so : Array F) (hi : Array F × Array F)
    (hL : (⟨lo, hi.1, so, hi.2⟩ : LTb) = ltbOf lm t u) :
    CxAt ⟨⟨lo, hi.1, so, hi.2⟩, thsOf pl lo so, rvOf pl lo so t u⟩ lm t u :=
  cxAt_mk pl lm t u _ hL

theorem cxAt_of (pl : Plan4) (lm : ℕ) (t u : ℕ → F) :
    CxAt ⟨ltbOf lm t u, thsOf pl (ltbOf lm t u).tlo (ltbOf lm t u).slo,
      rvOf pl (ltbOf lm t u).tlo (ltbOf lm t u).slo t u⟩ lm t u :=
  cxAt_mk pl lm t u _ rfl

/-- A kind's grouped link rows. -/
def lkK (pl : Plan4) : NodeKind → Array LkG
  | .N2 => pl.lk2
  | .N4 => pl.lk4
  | .N8 => pl.lk8

/-- **Slot `σ`'s grouped link rows**, from the plan (grouped here past the kind's slots). -/
def lkAt (pl : Plan4) (κ : NodeKind) (σ : ℕ) : LkG :=
  match (lkK pl κ)[σ]? with
  | some g => g
  | none => lkGOf κ σ

theorem lkAt_eq (pl : Plan4) (κ : NodeKind) (σ : ℕ) : lkAt pl κ σ = lkGOf κ σ := by
  have h : lkK pl κ = lkArr κ := by cases κ; exacts [pl.hlk2, pl.hlk4, pl.hlk8]
  unfold lkAt
  rw [h, lkArr, Array.getElem?_map, Array.getElem?_range]
  split_ifs <;> rfl

/-- **A link region's value** (S-E13a: up to `9 + 8,783 + 8,680` rows with H and L cells): the
head rows and S-E13b's node rows from the plan's grouping (`growsVal3`), the pinned elements from
their runs' inner sums (`prVal`); one product per entry or run, not `gN`'s `lm` products. -/
def linkV4 (pl : Plan4) (cx : LCx) (κ : NodeKind) (σ : ℕ) : F3 :=
  let L := cx.L
  let g := lkAt pl κ σ
  add3 (add3 (growsVal3 L.tlo L.thi L.slo L.shi g.hd)
    (match packB κ σ with
      | some (b0, _) =>
        prVal L.thi L.shi (splitAt L.slo L.shi (2 ^ 12) κ.oneCell) (innAt cx (linkBase σ + g.nh, b0))
      | none => (0, 0, 0)))
    (if g.eok then crowsVal3 L.tlo L.thi (g.ec.map (splitAt L.slo L.shi (2 ^ 12))) g.eg
      else growsVal3 L.tlo L.thi L.slo L.shi g.ex.get)

/-- **`linkV4` is the link rows' sparse value.** -/
theorem linkV4_eq {lm : ℕ} (hl : 11 ≤ lm) (t u : ℕ → F) (pl : Plan4) {cx : LCx} (hc : CxAt cx lm t u)
    (κ : NodeKind) (σ : ℕ) : linkV4 pl cx κ σ = rows3 lm (lm + 2) t u (linkIRows4 κ σ) := by
  obtain ⟨hL, hI, -⟩ := hc
  have ht : splitAt (loTab 11 t) (loTab (lm - 11) fun l => t (11 + l)) (2 ^ 11) = gN lm t :=
    splitE_eq hl t
  have hu : splitAt (loTab 12 u) (loTab (lm + 2 - 12) fun l => u (12 + l)) (2 ^ 12) = gN (lm + 2) u :=
    splitE_eq (by omega) u
  have hsplit : linkIRows4 κ σ = ((linkHead4 κ σ).zipIdx.map fun p => (linkBase σ + p.2, p.1)) ++
      (((packWf4 κ σ).zipIdx (linkHead4 κ σ).length).map fun p => (linkBase σ + p.2, p.1)) ++
      (((extRowsC κ σ).zipIdx ((linkHead4 κ σ).length + wfLen κ σ)).map fun p => (linkBase σ + p.2, p.1)) := by
    rw [linkIRows4, linkRows4, packRows4, wfLen_eq, ← List.append_assoc,
      List.zipIdx_append, List.zipIdx_append, List.map_append, List.map_append, Nat.zero_add,
      Nat.zero_add]
    rw [show (linkRowsB4 κ σ ++ packHead4 κ σ ++ packWf4 κ σ).length =
      (linkRowsB4 κ σ ++ packHead4 κ σ).length + (packWf4 κ σ).length from List.length_append ..]
    rfl
  have hg : ∀ rows : List (ℕ × Row), growsVal3 (ltbOf lm t u).tlo (ltbOf lm t u).thi (ltbOf lm t u).slo
      (ltbOf lm t u).shi (grows (2 ^ 11) (2 ^ 12) rows) = rows3 lm (lm + 2) t u rows := fun rows => by
    simp only [ltbOf, growsVal3_eq, growsVal_grows, rows3]
    rw [ht, hu, rowsValI_eq, rowsValI_eq, rowsValI_eq]
  rw [hsplit, rows3_append, rows3_append]
  have hx : (if (lkGOf κ σ).eok then crowsVal3 (ltbOf lm t u).tlo (ltbOf lm t u).thi
        ((lkGOf κ σ).ec.map (splitAt (ltbOf lm t u).slo (ltbOf lm t u).shi (2 ^ 12))) (lkGOf κ σ).eg
      else growsVal3 (ltbOf lm t u).tlo (ltbOf lm t u).thi (ltbOf lm t u).slo (ltbOf lm t u).shi
        (lkGOf κ σ).ex.get) = rows3 lm (lm + 2) t u (extIRows κ σ) := by
    split_ifs with h
    · simp only [lkGOf, cokB, Bool.and_eq_true, decide_eq_true_eq] at h ⊢
      rw [crowsVal3_eq _ _ _ _ _ _ h.1, h.2]
      simp only [ltbOf, rows3]
      rw [ht, hu, rowsValI_eq, rowsValI_eq, rowsValI_eq]
    · simp only [lkGOf, thunk_get]
      exact hg _
  simp only [linkV4, lkAt_eq, hL]
  rw [hx]
  simp only [lkGOf]
  rw [hg]
  congr 2
  unfold packWf4
  rcases packB κ σ with _ | ⟨b0, G⟩
  · simp [rows3_nil]
  · dsimp only
    rw [hI, hL, prVal_runs]
    simp only [ltbOf]
    rw [ht, hu, wfRows, wfSum_eq]

/-- **Slot `σ`'s arena₁ and bits** (ASK-P): their closed forms at the node's point (`a1V4`, `bitV4`:
a few automaton runs per slot). -/
def arV4 (κ : NodeKind) (t u : ℕ → F) (σ : ℕ) : F3 :=
  add3 (a1V4 κ.dims.logM (κ.dims.logM + 2) t u κ σ (slotB0 κ σ)) (bitV4 κ.dims.logM (κ.dims.logM + 2) t u κ σ)

theorem arV4_eq (κ : NodeKind) (t u : ℕ → F) (σ : ℕ) (hl : 20 ≤ κ.dims.logM) :
    arV4 κ t u σ = add3 (rows3 κ.dims.logM (κ.dims.logM + 2) t u (a1Rows4 κ σ (slotB0 κ σ)))
      (rows3 κ.dims.logM (κ.dims.logM + 2) t u (bitRows4 κ σ)) := by
  rw [arV4, a1V4_eq (n := κ.dims.logM) (m := κ.dims.logM + 2) (by omega) (by omega),
    bitV4_eq (n := κ.dims.logM) (m := κ.dims.logM + 2) (by omega) (by omega)]; rfl

/-- **Slot `σ`'s value** from its prototype's (`vN`, `vS`): the rest scaled, the link region by
`linkV4`. -/
def slotV4o (pl : Plan4) (κ : NodeKind) (t u : ℕ → F) (cx : LCx) (vN vS : F3) (σ : ℕ) : F3 :=
  let lm := κ.dims.logM
  add3 (add3 (smul3 (hiF lm t σ * (hiF lm u σ * (u lm * u (lm + 1)))) (if protoOf κ σ = 0 then vN else vS))
    (arV4 κ t u σ)) (linkV4 pl cx κ σ)

/-- Slot `v`'s replay rows from the plan's rows (`repIRowsW rtC1c`, `repIRowsWP_eq`). -/
def repIRowsWP (pl : Plan4) (κ : NodeKind) (v : ℕ) : List (ℕ × Row) :=
  (if protoOf κ v = 0 then pl.rp0 else pl.rp1).get.toList.zipIdx.map fun p =>
    (N4s.repRow0 κ v + p.2, rowMapC (N4s.repMapC κ v) p.1)

theorem repIRowsWP_eq (pl : Plan4) (κ : NodeKind) (v : ℕ) : repIRowsWP pl κ v = N4s.repIRowsW N4s.rtC1c κ v := by
  unfold repIRowsWP N4s.repIRowsW
  split_ifs with h
  · rw [h, pl.hrp.1]
  · have h1 : protoOf κ v = 1 := by
      have : protoOf κ v ≤ 1 := by unfold protoOf; split_ifs <;> omega
      omega
    rw [h1, pl.hrp.2]

/-- **Slot `σ`'s replay rows' value** (REPF): the previous node's slot from the context's shared local
values (`cx.rv`: frame and local parts, scaled by their regions' high factors), a segment slot's rows
(8, `rtLinkSegW`) sparse. -/
def repV4 (pl : Plan4) (κ : NodeKind) (t u : ℕ → F) (cx : LCx) (σ : ℕ) : F3 :=
  let lm := κ.dims.logM
  if protoOf κ σ = 0 then
    let r := cx.rv.get
    smul3 (hiF lm t κ.vslots * (u lm * u (lm + 1)))
      (add3 (smul3 (hiF lm u 0) r.1) (smul3 (hiF lm u κ.vslots) r.2))
  else rows3 lm (lm + 2) t u (repIRowsWP pl κ σ)

/-- **`repV4` is the slot's replay rows' sparse value** (the context at the point, the rows fit). -/
theorem repV4_eq (pl : Plan4) (κ : NodeKind) (t u : ℕ → F) {cx : LCx} (hc : CxAt cx κ.dims.logM t u)
    (hR : RepFit) (σ : ℕ) :
    repV4 pl κ t u cx σ = rows3 κ.dims.logM (κ.dims.logM + 2) t u (N4s.repIRowsW N4s.rtC1c κ σ) := by
  unfold repV4
  split_ifs with h0
  · have hp : κ.hasPrev = true ∧ σ = 0 := by
      unfold protoOf isPrevSlot at h0
      split_ifs at h0 with h'
      simpa using h'
    obtain ⟨hp, rfl⟩ := hp
    have hf := hR 0 (by norm_num)
    have e : N4s.repIRowsW N4s.rtC1c κ 0 = (N4s.repRowsP (N4s.rtC1c 0) 0).zipIdx.map fun p =>
        (κ.vslots * slotM4 + p.2, rowMapC (N4s.repMapC κ 0) p.1) := by
      simp only [N4s.repIRowsW, N4s.repRow0, h0, if_true]
    dsimp only
    rw [hc.2.2, e]
    simp only [rows3, smul3, add3, repV0_eq hp t u hf]
  · rw [repIRowsWP_eq]

theorem sum3_add {α : Type*} (f g : α → F3) (l : List α) :
    sum3 (fun x => add3 (f x) (g x)) l = add3 (sum3 f l) (sum3 g l) := by
  simp only [sum3_eq, add3, sumL_eq, List.sum_map_add]

/-- **Slot `σ`'s value** (with its replay rows, REPF). -/
def slotV4 (pl : Plan4) (κ : NodeKind) (t u : ℕ → F) (cx : LCx) (vN vS : F3) (σ : ℕ) : F3 :=
  add3 (slotV4o pl κ t u cx vN vS σ) (repV4 pl κ t u cx σ)

/-- A prototype's rows from the plan's pieces (the fallback's; no closed `protoRows` constant in
the compiled code). -/
def protoRowsP (pl : Plan4) (π : ℕ) : List (ℕ × Row) :=
  if π = 0 then pl.pc0.flatMap (Piece.rows pl.keys pl.sh0 (oneP 0))
  else pl.pc1.flatMap (Piece.rows pl.keys pl.sh1 (oneP 1))

theorem protoRowsP_eq (pl : Plan4) (π : ℕ) (hπ : π ≤ 1) : protoRowsP pl π = protoRows π := by
  unfold protoRowsP; split_ifs with h
  · subst h; exact pl.ok.2.1
  · obtain rfl : π = 1 := by omega
    exact pl.ok.2.2

theorem protoOf_le (κ : NodeKind) (σ : ℕ) : protoOf κ σ ≤ 1 := by unfold protoOf; split_ifs <;> omega

/-- The arenas' fit on the plan's rows (the fallback's; `arFit_iff`). -/
def arFitP (pl : Plan4) : Bool := arFitB 0 (protoRowsP pl 0) pl.ar0 && arFitB 1 (protoRowsP pl 1) pl.ar1

/-- Prototype `π`'s template rows from the plan. -/
def arP (pl : Plan4) (π : ℕ) : List Row := if π = 0 then pl.ar0 else pl.ar1

theorem arP_eq (pl : Plan4) (π : ℕ) (hπ : π ≤ 1) : arP pl π = askRowsT π := by
  unfold arP; split_ifs with h
  · subst h; exact pl.har.1
  · obtain rfl : π = 1 := by omega
    exact pl.har.2

/-- `arIRows4` from the plan's rows (the fallback's). -/
def arIRowsP (pl : Plan4) (κ : NodeKind) (σ : ℕ) : List (ℕ × Row) :=
  if arFitP pl = true then
    a1Rows4 κ σ (slotB0 κ σ) ++ absRows4 κ (mvRows (protoOf κ σ) σ (idxAr (protoOf κ σ) (arP pl (protoOf κ σ)))) ++
      bitRows4 κ σ
  else [(arRej σ, rejR κ)]

theorem arIRowsP_eq (pl : Plan4) (κ : NodeKind) (σ : ℕ) : arIRowsP pl κ σ = arIRows4 κ σ := by
  have hf : arFitP pl = true ↔ ArFit := by
    rw [arFit_iff, arFitP, protoRowsP_eq pl 0 (by norm_num), protoRowsP_eq pl 1 le_rfl, pl.har.1, pl.har.2]
  unfold arIRowsP arIRows4
  by_cases hA : ArFit
  · rw [if_pos (hf.2 hA), if_pos hA, arP_eq pl _ (protoOf_le κ σ), ← askPI_eq]
  · rw [if_neg (mt hf.1 hA), if_neg hA]

/-- `repAllRows` from the plan's rows (the fallback's). -/
def repAllRowsP (pl : Plan4) (κ : NodeKind) : List (ℕ × Row) :=
  if arFitP pl = true then
    (if (repFitB 0 pl.rp0.get.toList && repFitB 1 pl.rp1.get.toList) = true then (List.range κ.vslots).flatMap (repIRowsWP pl κ)
      else [(N4s.repSegB, rejR κ)])
  else []

theorem repFit_iff (pl : Plan4) : (repFitB 0 pl.rp0.get.toList && repFitB 1 pl.rp1.get.toList) = true ↔ RepFit := by
  rw [pl.hrp.1, pl.hrp.2, Bool.and_eq_true]
  constructor
  · rintro ⟨h0, h1⟩ π hπ
    rcases Nat.le_one_iff_eq_zero_or_eq_one.1 hπ with rfl | rfl
    exacts [h0, h1]
  · intro h; exact ⟨h 0 (by norm_num), h 1 le_rfl⟩

theorem repAllRowsP_eq (pl : Plan4) (κ : NodeKind) : repAllRowsP pl κ = repAllRows κ := by
  have hf : arFitP pl = true ↔ ArFit := by
    rw [arFit_iff, arFitP, protoRowsP_eq pl 0 (by norm_num), protoRowsP_eq pl 1 le_rfl, pl.har.1, pl.har.2]
  unfold repAllRowsP repAllRows
  by_cases hA : ArFit
  · rw [if_pos (hf.2 hA), if_pos hA]
    by_cases hR : RepFit
    · rw [if_pos ((repFit_iff pl).2 hR), if_pos hR]
      rw [show repIRowsWP pl κ = N4s.repIRowsW N4s.rtC1c κ from funext (repIRowsWP_eq pl κ)]
    · rw [if_neg (mt (repFit_iff pl).1 hR), if_neg hR]
  · rw [if_neg (mt hf.1 hA), if_neg hA]

/-- `nodeIRows4` from the plan's pieces, the fit checked on them (the fallback's). -/
def nodeIRowsP (pl : Plan4) (κ : NodeKind) : List (ℕ × Row) :=
  if (fitB 0 (protoRowsP pl 0) && fitB 1 (protoRowsP pl 1)) = true then
    ((List.range κ.vslots).flatMap fun σ =>
      absRows4 κ (mvRows (protoOf κ σ) σ (protoRowsP pl (protoOf κ σ))) ++ arIRowsP pl κ σ ++ linkIRows4 κ σ) ++
      repAllRowsP pl κ
  else rejectRows κ


theorem nodeIRowsP_eq (pl : Plan4) (κ : NodeKind) : nodeIRowsP pl κ = nodeIRows4 κ := by
  have h : ∀ σ, protoRowsP pl (protoOf κ σ) = protoRows (protoOf κ σ) := fun σ =>
    protoRowsP_eq pl _ (protoOf_le κ σ)
  unfold nodeIRowsP nodeIRows4
  rw [protoRowsP_eq pl 0 (by norm_num), protoRowsP_eq pl 1 le_rfl]
  by_cases hF : ProtoFit
  · rw [if_pos (protoFit_iff.1 hF), if_pos hF]
    simp only [slotRows4, h, arIRowsP_eq, repAllRowsP_eq]
  · rw [if_neg (mt protoFit_iff.2 hF), if_neg hF]

/-- **`evalM` of a 4.1 node** (S-E12b): the two prototypes' values once, every slot from them;
the sparse sum over `nodeIRows4 κ` if a check failed. -/
def evalMT4 (pl : Plan4) (κ : NodeKind) (τ σ : Array F) : F3 :=
  let t := fun l => τ.getD l 0; let u := fun l => σ.getD l 0
  if pl.inR then
    let v := protoV4 pl t u κ.hasPrev
    let L := ltbOf κ.dims.logM t u
    sum3 (slotV4 pl κ t u ⟨L, thsOf pl L.tlo L.slo, rvOf pl L.tlo L.slo t u⟩ v.1 v.2) (List.range κ.vslots)
  else rows3 κ.dims.logM (κ.dims.logM + 2) t u (nodeIRowsP pl κ)

/-- **`evalM`'s specification**: the MLEs of `nodeIRows4 κ`'s matrices (`τ`: `logM` coordinates,
`σ`: `m − 7 = logM + 2`). -/
noncomputable def evalMS4 (κ : NodeKind) (τ σ : Array F) : F3 :=
  (Eval.matMLE (entriesI .a (nodeIRows4 κ)) (Eval.ptOf κ.dims.logM τ) (Eval.ptOf (κ.dims.logM + 2) σ),
   Eval.matMLE (entriesI .b (nodeIRows4 κ)) (Eval.ptOf κ.dims.logM τ) (Eval.ptOf (κ.dims.logM + 2) σ),
   Eval.matMLE (entriesI .c (nodeIRows4 κ)) (Eval.ptOf κ.dims.logM τ) (Eval.ptOf (κ.dims.logM + 2) σ))

theorem logM_ge (κ : NodeKind) : 20 ≤ κ.dims.logM ∧ κ.vslots ≤ 2 ^ (κ.dims.logM - 20) := by
  cases κ <;> decide

theorem sum3_congr {f g : ℕ → F3} {l : List ℕ} (h : ∀ x ∈ l, f x = g x) : sum3 f l = sum3 g l := by
  simp only [sum3_eq, sumL_eq]
  rw [List.map_congr_left fun x hx => congrArg Prod.fst (h x hx),
    List.map_congr_left fun x hx => congrArg (fun y : F3 => y.2.1) (h x hx),
    List.map_congr_left fun x hx => congrArg (fun y : F3 => y.2.2) (h x hx)]

theorem rows3_flatMap (n m : ℕ) (t u : ℕ → F) (l : List ℕ) (f : ℕ → List (ℕ × Row)) :
    rows3 n m t u (l.flatMap f) = sum3 (fun σ => rows3 n m t u (f σ)) l := by
  simp only [rows3, sum3_eq, sumL_eq, rowsVal_flatMap]

theorem rows3_spec (κ : NodeKind) (τ σ : Array F) :
    rows3 κ.dims.logM (κ.dims.logM + 2) (fun l => τ.getD l 0) (fun l => σ.getD l 0) (nodeIRows4 κ) =
      evalMS4 κ τ σ := by
  simp only [rows3, evalMS4, rowsVal_F, Eval.sparse_eq]

/-- **A kind's slot sums are its `evalM`** (the plan's checks passed): at any context at the point,
with the prototypes' values at `node = b`, `b` set if the kind replays the previous node. -/
theorem slots_val (pl : Plan4) (hR : pl.inR = true) (κ : NodeKind) (τ σ : Array F) {cx : LCx}
    (hc : CxAt cx κ.dims.logM (fun l => τ.getD l 0) (fun l => σ.getD l 0)) (b : Bool)
    (hb : κ.hasPrev = true → b = true) :
    sum3 (slotV4 pl κ (fun l => τ.getD l 0) (fun l => σ.getD l 0) cx
        (protoV4 pl (fun l => τ.getD l 0) (fun l => σ.getD l 0) b).1
        (protoV4 pl (fun l => τ.getD l 0) (fun l => σ.getD l 0) b).2) (List.range κ.vslots) =
      evalMS4 κ τ σ := by
  obtain ⟨hF, hk, hA, hRF⟩ := pl.hR hR
  rw [← rows3_spec, nodeIRows4, if_pos hF, rows3_append, rows3_flatMap, repAllRows, if_pos hA, if_pos hRF,
    rows3_flatMap]
  unfold slotV4
  rw [sum3_add]
  refine congrArg₂ add3 ?_ (sum3_congr fun s _ => repV4_eq pl κ _ _ hc hRF s)
  obtain ⟨hR0, -⟩ := hF 0 (by norm_num)
  obtain ⟨hR1, -⟩ := hF 1 le_rfl
  obtain ⟨hl, hv⟩ := logM_ge κ
  obtain ⟨hv0, hv1⟩ := protoV4_eq pl hk (fun l => τ.getD l 0) (fun l => σ.getD l 0) b
  refine sum3_congr fun s hs => ?_
  have hs' : s < 2 ^ (κ.dims.logM - 20) := lt_of_lt_of_le (List.mem_range.1 hs) hv
  rw [rows3_append, rows3_append, slotV4o]
  rw [linkV4_eq (by omega) _ _ pl hc]
  refine congrArg (add3 · _) ?_
  have hcp : ∀ π : ℕ, π ≤ 1 → ∀ rows, InSlot π rows →
      smul3 (hiF κ.dims.logM (fun l => τ.getD l 0) s * (hiF κ.dims.logM (fun l => σ.getD l 0) s *
          (σ.getD κ.dims.logM 0 * σ.getD (κ.dims.logM + 1) 0)))
        (rows3 21 23 (starPt (fun l => τ.getD l 0) π) (starPt (fun l => σ.getD l 0) π) rows) =
      rows3 κ.dims.logM (κ.dims.logM + 2) (fun l => τ.getD l 0) (fun l => σ.getD l 0)
        (absRows4 κ (mvRows π s rows)) := by
    intro π hπ rows hr
    have hab : absRows4 κ (mvRows π s rows) =
        (mvRows π s rows).map fun p => (p.1, rowMapC (· + 3 * 2 ^ κ.dims.logM) p.2) := by
      simp only [absRows4, oneCell_eq]
    rw [hab]
    simp only [smul3, rows3, copy_val hπ hl hs' _ (fun l => τ.getD l 0) (fun l => σ.getD l 0) hr]
  have hin : ∀ π : ℕ, π ≤ 1 → InSlot π (protoRows π ++ askPI π) := fun π hπ p hp => by
    rcases List.mem_append.1 hp with hp | hp
    · exact (hF π hπ).1 p hp
    · exact (hA π hπ).2.2 p hp
  have hsm : ∀ (c : F) (x y : F3), smul3 c (add3 x y) = add3 (smul3 c x) (smul3 c y) := fun c x y => by
    simp only [smul3, add3, mul_add]
  have key : smul3 (hiF κ.dims.logM (fun l => τ.getD l 0) s * (hiF κ.dims.logM (fun l => σ.getD l 0) s *
          (σ.getD κ.dims.logM 0 * σ.getD (κ.dims.logM + 1) 0)))
        (rows3 21 23 (starPt (fun l => τ.getD l 0) (protoOf κ s)) (starPt (fun l => σ.getD l 0) (protoOf κ s))
          (protoRows (protoOf κ s) ++ askPI (protoOf κ s))) =
      add3 (rows3 κ.dims.logM (κ.dims.logM + 2) (fun l => τ.getD l 0) (fun l => σ.getD l 0) (slotRows4 κ s))
        (rows3 κ.dims.logM (κ.dims.logM + 2) (fun l => τ.getD l 0) (fun l => σ.getD l 0)
          (absRows4 κ (mvRows (protoOf κ s) s (askPI (protoOf κ s))))) := by
    rw [hcp _ (protoOf_le κ s) _ (hin _ (protoOf_le κ s)), ← rows3_append, slotRows4, absRows4, absRows4,
      absRows4, mvRows, mvRows, mvRows, List.map_append, List.map_append]
  have hvv : (if protoOf κ s = 0 then
        (protoV4 pl (fun l => τ.getD l 0) (fun l => σ.getD l 0) b).1
      else (protoV4 pl (fun l => τ.getD l 0) (fun l => σ.getD l 0) b).2) =
      rows3 21 23 (starPt (fun l => τ.getD l 0) (protoOf κ s)) (starPt (fun l => σ.getD l 0) (protoOf κ s))
        (protoRows (protoOf κ s) ++ askPI (protoOf κ s)) := by
    by_cases hp : protoOf κ s = 0
    · have hk' : κ.hasPrev = true := by
        by_contra hk'; simp [protoOf, isPrevSlot, hk'] at hp
      rw [if_pos hp, hv0, if_pos (hb hk'), hp]
    · have h1 : protoOf κ s = 1 := by
        simp only [protoOf] at hp ⊢; split_ifs at hp ⊢ <;> simp_all
      rw [if_neg hp, hv1, h1]
  rw [hvv, key, arV4_eq κ _ _ s hl, arIRows4, if_pos hA, rows3_append, rows3_append]
  simp only [add3]
  refine Prod.ext ?_ (Prod.ext ?_ ?_) <;> dsimp only <;> abel

/-- **`evalM_eq` for the 4.1 nodes.** -/
theorem evalMT4_eq (pl : Plan4) (κ : NodeKind) (τ σ : Array F) : evalMT4 pl κ τ σ = evalMS4 κ τ σ := by
  unfold evalMT4
  dsimp only
  by_cases hR : pl.inR = true
  · rw [if_pos hR]
    exact slots_val pl hR κ τ σ (cxAt_of pl _ _ _) κ.hasPrev id
  · rw [if_neg hR, nodeIRowsP_eq]; exact rows3_spec κ τ σ

/-! ## Controls -/

/-- (+) `starPt` keeps the low coordinates and sets coordinate 20 to the region's bit; (−) it drops
the coordinates above. -/
theorem star_ctl (t : ℕ → F) : starPt t 1 3 = t 3 ∧ starPt t 1 20 = 1 ∧ starPt t 0 20 = 0 ∧ starPt t 1 21 = 0 := by
  simp [starPt]

/-- (+) A piece inside region 1 passes the check; (−) one whose cell lies in region 0 fails. -/
theorem pieceInB_ctl :
    pieceInB #[] #[] [] 1 (.sp [(2 ^ 20, ⟨[(2 ^ 20 + 1, 1)], [], []⟩)]) = true ∧
      pieceInB #[] #[] [] 1 (.sp [(2 ^ 20, ⟨[(5, 1)], [], []⟩)]) = false := by
  constructor <;> decide

/-- (+) Sorted disjoint intervals pass the index check; (−) overlapping ones fail. -/
theorem ivsOkB_ctl : ivsOkB [(0, 5), (5, 3)] = true ∧ ivsOkB [(0, 5), (4, 1)] = false := by
  constructor <;> decide

/-- (+) Distinct indices pass `idxNodupB`, in any order; (−) a repeated index fails it. -/
theorem idxNodupB_ctl (r : Row) : idxNodupB [(3, r), (1, r)] = true ∧ idxNodupB [(1, r), (1, r)] ≠ true :=
  ⟨(idxNodupB_iff _).2 (by simp), fun h => by simpa using (idxNodupB_iff _).1 h⟩

/-- (+) Two pinned elements in one row block and one cell block share a run, and two with one value
share a class; (−) an element 200 stream elements on (cell block 1) starts a run, and one with
another value starts a class. -/
theorem runsOf_ctl :
    ((runsOf 0 0 [(0, 0), (1, 0)]).1.length, (runsOf 0 0 [(0, 0), (1, 0)]).2.length) = (1, 1) ∧
      ((runsOf 0 0 [(0, 0), (200, 1)]).1.length, (runsOf 0 0 [(0, 0), (200, 1)]).2.length) = (2, 2) := by
  decide

/-- (+) A coding that decodes to the rows passes `cokB`; (−) one whose index points at another cell,
or past the dictionary, fails it. -/
theorem cokB_ctl :
    cokB #[5, 9] [(0, [(1, [(0, 0)], [(1, 0)], [])])] [(1, ⟨[(5, 0)], [(9, 0)], []⟩)] = true ∧
      cokB #[5, 9] [(0, [(1, [(1, 0)], [(1, 0)], [])])] [(1, ⟨[(5, 0)], [(9, 0)], []⟩)] = false ∧
      cokB #[5, 9] [(0, [(1, [(2, 0)], [(1, 0)], [])])] [(1, ⟨[(0, 0)], [(9, 0)], []⟩)] = false := by
  decide

/-- (+) `crowsOf`'s coding against a sorted dictionary (`bsGo`) decodes to the rows (two rows, three
cells, one repeated); (−) against a dictionary missing a cell it does not. (`cellsOf` builds the
dictionary; it is not load-bearing: any dictionary is checked by `cokB`.) -/
theorem crowsOf_ctl :
    cokB #[2, 7, 9] (crowsOf #[2, 7, 9] [(3, ⟨[(7, 0)], [(2, 0)], []⟩), (4, ⟨[(2, 0)], [], [(9, 0)]⟩)])
      [(3, ⟨[(7, 0)], [(2, 0)], []⟩), (4, ⟨[(2, 0)], [], [(9, 0)]⟩)] = true ∧
    cokB #[2, 9] (crowsOf #[2, 9] [(3, ⟨[(7, 0)], [(2, 0)], []⟩), (4, ⟨[(2, 0)], [], [(9, 0)]⟩)])
      [(3, ⟨[(7, 0)], [(2, 0)], []⟩), (4, ⟨[(2, 0)], [], [(9, 0)]⟩)] = false := by
  decide

end Rev4
end FR
