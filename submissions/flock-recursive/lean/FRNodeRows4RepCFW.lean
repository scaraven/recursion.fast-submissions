-- New for `flock-recursive` (track CF2): prototype 0's replay blocks split for the plan.
import FRNodeRows4RepCFP
import FRVIRTplCFF

/-!
# Prototype 0's replay blocks, split for the plan

The plan keeps prototype 0's replay rows as **row blocks** (their rows at their indices, grouped
sparse) and **`rsWeight` ops prepared** (`kpOf`, at their first rows; their rows never built):
`blkGo` walks the blocks (`arBlk0`), the `rsWeight` op's row count from its preparation (`kpLen_eq`).
**`blkGo_val`**: the row blocks' value plus the ops' values is the rows' value (`rm`).
-/

namespace FR
namespace Rev4
open RecursionFast Circ TEval Tpl

/-- A prepared `rsWeight` op's row count. -/
def kpLen (kp : KP) : ℕ :=
  if kp.ok then (kp.subs.map fun p => p.2.2).sum + kp.mux.length + kp.copy.length else kp.alt.length

theorem copyRows_length (P : Params) (outs : List Slot) (o : List Lin) :
    (N4s.copyRows P outs o).length = (N4s.outF outs).length := by
  simp [N4s.copyRows]

/-- **The prepared op's row count is its rows'.** -/
theorem kpLen_eq (P : Params) (cs : CS) (op : Op) (outs : List Slot) :
    kpLen (kpOf P cs op outs) = (N4s.kRows N4s.kRS N4s.repB N4s.cbRS P cs op outs).length := by
  unfold kpOf N4s.kRows
  cases hbs : N4s.kBlocks N4s.kRS cs op with
  | none => simp [kpLen]
  | some bs =>
    simp only []
    by_cases hc : (N4s.outsOk N4s.kRS.tys outs && bs.all (fun b => N4s.kRS.inOk b.1) &&
        (N4s.kIns P bs ++ N4s.outF outs).all (linLt N4s.repB)) = true
    · rw [if_pos hc, if_pos hc]
      simp only [kpLen, ite_true, List.length_append, List.length_map, copyRows_length, N4s.rowsTR_eq]
      have hT : N4s.kTpl N4s.kRS op bs = kmuxT (N4s.kSig (bs.map fun b => b.2.length)) (bs.map fun b => b.2.length).sum 2
          ((rsTs bs).map fun T => (⟨sgGates T.1 0, T.2⟩ : Tpl)) := by
        simp only [N4s.kTpl, rsTs, List.map_cons, List.map_nil, ← rsT_segs]; rfl
      rw [hT]
      simp only [kmuxT, tpl_rows_eq, rowsAt_append, List.length_append, rowsAt_length, nrows_subsG,
        List.map_map, Function.comp_def, nrows_sgGates, subsG_two, nlocs_subsG, nlocs_sgGates]
      simp only [muxG, rsTs, List.length_cons, List.length_nil, List.map_cons, List.map_nil,
        show (0 + 1 + 1 + 1 : ℕ) = 3 from rfl]
    · rw [if_neg hc, if_neg hc]; simp [kpLen]

/-- **The blocks split**, from row `X` (accumulators reversed): the row blocks' rows at their
indices, the `rsWeight` ops prepared at their first rows. -/
def blkGo : ℕ → List RBlk → List (Row × ℕ) → List (ℕ × KP) → List (Row × ℕ) × List (ℕ × KP)
  | _, [], a, b => (a, b)
  | X, .sp l :: bs, a, b => blkGo (X + l.length) bs ((l.zipIdx X).reverseAux a) b
  | X, .rs P cs op outs :: bs, a, b =>
    let kp := kpOf P cs op outs
    blkGo (X + kpLen kp) bs a ((X, kp) :: b)

/-- Indexed rows' value (matrix `s`, row point `t`, cells at `w`). -/
def spV (s : Mat) (t : ℕ → F) (w : Asg) (l : List (Row × ℕ)) : F :=
  (l.map fun p => gN 20 t p.2 * (s.r p.1).ev w).sum

theorem spV_append (s : Mat) (t : ℕ → F) (w : Asg) (a b : List (Row × ℕ)) :
    spV s t w (a ++ b) = spV s t w a + spV s t w b := by simp [spV]

theorem spV_reverse (s : Mat) (t : ℕ → F) (w : Asg) (a : List (Row × ℕ)) :
    spV s t w a.reverse = spV s t w a := by simp [spV, List.sum_reverse]

theorem spV_zipIdx (s : Mat) (t : ℕ → F) (w : Asg) :
    ∀ (X : ℕ) (l : List Row), spV s t w (l.zipIdx X) = rm s t w X l
  | _, [] => rfl
  | X, r :: l => by
    rw [List.zipIdx_cons, rm, ← spV_zipIdx s t w (X + 1) l]
    simp [spV]

/-- **The split's value**: the row blocks' plus the prepared ops' (any `V` that is an op's rows' value
at its first row). -/
theorem blkGo_val (s : Mat) (t : ℕ → F) (w : Asg) (V : ℕ → KP → F)
    (hV : ∀ X P cs op outs, V X (kpOf P cs op outs) = rm s t w X (N4s.kRows N4s.kRS N4s.repB N4s.cbRS P cs op outs)) :
    ∀ (X : ℕ) (bs : List RBlk) (a : List (Row × ℕ)) (b : List (ℕ × KP)),
      spV s t w (blkGo X bs a b).1 + ((blkGo X bs a b).2.map fun q => V q.1 q.2).sum =
        spV s t w a + (b.map fun q => V q.1 q.2).sum + rm s t w X (bs.flatMap RBlk.rows)
  | _, [], a, b => by simp [blkGo, rm]
  | X, .sp l :: bs, a, b => by
    rw [blkGo, blkGo_val s t w V hV _ bs, List.flatMap_cons, rm_append, List.reverseAux_eq, spV_append,
      spV_reverse, spV_zipIdx]
    simp only [RBlk.rows]; ring
  | X, .rs P cs op outs :: bs, a, b => by
    rw [blkGo, blkGo_val s t w V hV _ bs, List.flatMap_cons, rm_append, List.map_cons, List.sum_cons, hV,
      kpLen_eq]
    simp only [RBlk.rows]; ring

/-- The split's row count. -/
theorem blkGo_len : ∀ (X : ℕ) (bs : List RBlk) (a : List (Row × ℕ)) (b : List (ℕ × KP)),
    (blkGo X bs a b).1.length + ((blkGo X bs a b).2.map fun q => kpLen q.2).sum =
      a.length + (b.map fun q => kpLen q.2).sum + (bs.flatMap RBlk.rows).length
  | _, [], a, b => by simp [blkGo]
  | X, .sp l :: bs, a, b => by
    rw [blkGo, blkGo_len _ bs, List.flatMap_cons, List.length_append, List.reverseAux_eq, List.length_append,
      List.length_reverse, List.length_zipIdx]
    simp only [RBlk.rows]; ring
  | X, .rs P cs op outs :: bs, a, b => by
    rw [blkGo, blkGo_len _ bs, List.flatMap_cons, List.length_append, List.map_cons, List.sum_cons, kpLen_eq]
    simp only [RBlk.rows]; ring

/-! ## The cell weights by split tables -/

/-- `wF` with an eq function. -/
def wFA (gu : ℕ → F) : Asg := fun c => if c < N4s.repB then gu c else 0

/-- `wL` with an eq function. -/
def wLA (gu : ℕ → F) : Asg := fun c => if c < N4s.repB then 0 else gu (c - N4s.repB)

theorem wFA_eq (gu u : ℕ → F) (h : ∀ x, gu x = gN 20 u x) : wFA gu = wF u := by
  funext c; simp only [wFA, wF, h]

theorem wLA_eq (gu u : ℕ → F) (h : ∀ x, gu x = gN 20 u x) : wLA gu = wL u := by
  funext c; simp only [wLA, wL, h]

theorem wF_cb (u : ℕ → F) (x : ℕ) : wF u (N4s.cbRS + x) = 0 * gN 20 u (2 ^ 16 + x) := by
  have h : ¬ N4s.cbRS + x < N4s.repB := by unfold N4s.cbRS; exact Nat.not_lt.2 (by omega)
  rw [wF, if_neg h, zero_mul]

theorem wL_cb (u : ℕ → F) (x : ℕ) : wL u (N4s.cbRS + x) = 1 * gN 20 u (2 ^ 16 + x) := by
  have h : ¬ N4s.cbRS + x < N4s.repB := by unfold N4s.cbRS; exact Nat.not_lt.2 (by omega)
  have e : N4s.cbRS + x - N4s.repB = 2 ^ 16 + x := by unfold N4s.cbRS; omega
  rw [wL, if_neg h, e, one_mul]

/-- The prepared ops' values, three matrices. -/
def kpsV3 (gt gu t u : ℕ → F) (w : Asg) (lam : F) (kps : List (ℕ × KP)) : F3 :=
  ((kps.map fun q => kopV .a gt gu t u w lam q.1 q.2).sum, (kps.map fun q => kopV .b gt gu t u w lam q.1 q.2).sum,
    (kps.map fun q => kopV .c gt gu t u w lam q.1 q.2).sum)

theorem rowsVal_spF (s : Mat) (t u : ℕ → F) (l : List (Row × ℕ)) :
    rowsVal (RingHom.id F) s 20 20 t u (l.map fun p => (p.2, rowFr p.1)) = spV s t (wF u) l := by
  simp only [rowsVal, spV, List.map_map, Function.comp_def, Mat.r_rowFr, linE_linFr]

theorem rowsVal_spL (s : Mat) (t u : ℕ → F) (l : List (Row × ℕ)) :
    rowsVal (RingHom.id F) s 20 20 t u (l.map fun p => (p.2, rowLoc p.1)) = spV s t (wL u) l := by
  simp only [rowsVal, spV, List.map_map, Function.comp_def, Mat.r_rowLoc, linE_linLoc]

/-- **The split's value at the plan's weights**: the row blocks' plus the ops' closed forms. -/
theorem blk_val (s : Mat) (t u : ℕ → F) (w : Asg) (lam : F) (hw : ∀ x, w (N4s.cbRS + x) = lam * gN 20 u (2 ^ 16 + x))
    (bs : List RBlk) :
    spV s t w (blkGo 0 bs [] []).1 + ((blkGo 0 bs [] []).2.map fun q => kopV s (gN 20 t) (gN 20 u) t u w lam q.1 q.2).sum =
      rm s t w 0 (bs.flatMap RBlk.rows) := by
  have h := blkGo_val s t w (fun X kp => kopV s (gN 20 t) (gN 20 u) t u w lam X kp)
    (fun X P cs op outs => kopV_eq s _ _ t u w lam (fun _ => rfl) (fun _ => rfl) hw P cs op outs X) 0 bs [] []
  simpa [spV] using h

/-! ## Prototype `π`'s ask rows and replay blocks (the plan's; `arBlk0` at `0`) -/

def arBlkN (π : ℕ) : List Row × List RBlk :=
  let r := trailMB (N4s.XofC π) (protoLay π) (protoP π) (askTG π) (N4s.rtC1c π) blk0 []
    (CS.init (baseR π)) none 0 (protoProg π).ops [] []
  (r.1.reverse, r.2.reverse)

theorem arBlkN_zero : arBlkN 0 = arBlk0 := rfl

/-! ## The structural fit (`RepFit` without the `rsWeight` rows)

A prepared op fits if its one and input forms' cells fit, its sub-templates' locals are below their
counts (`psLocOk`), the mux rows' locals and the sub-templates' total below `lRoom` (so the locals'
cells `cbRS + k` stay in `[repB, repB + 2^20)`), and its copy rows' cells fit. Sound, not complete:
the plan keeps the fallback. -/

/-- A form's cells fit prototype 0's replay. -/
def linCellOk (l : Lin) : Bool := l.all fun t => repCellOk 0 t.1

def rowCellOk (r : Row) : Bool := linCellOk r.a && linCellOk r.b && linCellOk r.c

theorem rowCellOk_iff (r : Row) : rowCellOk r = true ↔ ∀ t ∈ r.a ++ r.b ++ r.c, repCellOk 0 t.1 = true := by
  simp only [rowCellOk, linCellOk, Bool.and_eq_true, List.all_eq_true, List.mem_append]
  constructor
  · rintro ⟨⟨ha, hb⟩, hc⟩ t ((ht | ht) | ht)
    exacts [ha t ht, hb t ht, hc t ht]
  · intro h; exact ⟨⟨fun t ht => h t (Or.inl (Or.inl ht)), fun t ht => h t (Or.inl (Or.inr ht))⟩,
      fun t ht => h t (Or.inr ht)⟩

/-- The template locals' room above `cbRS`. -/
abbrev lRoom : ℕ := 2 ^ 20 - 2 ^ 16

theorem cb_cellOk {k : ℕ} (hk : k < lRoom) : repCellOk 0 (N4s.cbRS + k) = true := by
  have hM : slotM4 = 1048576 := rfl
  have hR : lRoom = 983040 := by norm_num [lRoom]
  have hk' : k < 983040 := hR ▸ hk
  have h1 : N4s.repB ≤ N4s.cbRS + k := by unfold N4s.cbRS; omega
  have h2 : N4s.cbRS + k < N4s.repB + slotM4 := by unfold N4s.cbRS; rw [hM]; omega
  unfold repCellOk
  rw [if_pos rfl, decide_eq_true h1, decide_eq_true h2, Bool.and_true, Bool.or_true]

theorem mem_smulC {c : F} {l : Lin} {t : ℕ × F} (h : t ∈ l.smul c) : ∃ t' ∈ l, t.1 = t'.1 := by
  simp only [Lin.smul, List.mem_map] at h
  obtain ⟨t', ht', rfl⟩ := h
  exact ⟨t', ht', rfl⟩

theorem instLin_cellOk {one : Lin} {ins : List Lin} (h1 : linCellOk one = true)
    (hi : ∀ x ∈ ins, linCellOk x = true) {l : LinT} (hl : locLt lRoom l = true) :
    linCellOk (instLin one ins N4s.cbRS l) = true := by
  have hl' := locLt_iff.1 hl
  unfold linCellOk at h1 ⊢
  rw [List.all_eq_true] at h1 ⊢
  intro t ht
  obtain ⟨⟨w, c⟩, hw, ht⟩ := List.mem_flatMap.1 ht
  cases w with
  | one =>
    obtain ⟨t', ht', he⟩ := mem_smulC ht
    rw [he]; exact h1 t' ht'
  | inp i =>
    obtain ⟨t', ht', he⟩ := mem_smulC ht
    rw [he]
    rw [List.getD_eq_getElem?_getD] at ht'
    cases hx : ins[i]? with
    | none => rw [hx] at ht'; simp at ht'
    | some x =>
      rw [hx] at ht'
      exact List.all_eq_true.1 (hi x (List.mem_of_getElem? hx)) t' ht'
  | loc k =>
    simp only [List.mem_singleton] at ht
    rw [ht]; exact cb_cellOk (hl' k c hw)

theorem instRow_cellOk {one : Lin} {ins : List Lin} (h1 : linCellOk one = true)
    (hi : ∀ x ∈ ins, linCellOk x = true) {r : RowT} (hr : rowLocLt lRoom r = true) :
    rowCellOk (instRow one ins N4s.cbRS r) = true := by
  simp only [rowLocLt, Bool.and_eq_true] at hr
  simp only [rowCellOk, instRow, Bool.and_eq_true]
  exact ⟨⟨instLin_cellOk h1 hi hr.1.1, instLin_cellOk h1 hi hr.1.2⟩, instLin_cellOk h1 hi hr.2⟩

theorem locLt_le {m M : ℕ} (h : m ≤ M) {l : LinT} (hl : locLt m l = true) : locLt M l = true :=
  locLt_iff.2 fun k c hk => lt_of_lt_of_le (locLt_iff.1 hl k c hk) h

/-- The sub-templates' rows (substituted, locals one after the other from `k`) read locals below
`k` plus their count. -/
theorem subsG_rows_loc (σ : ℕ → ℕ → LinT) (hσ : ∀ j i, locLt 0 (σ j i) = true) :
    ∀ (ts : List Tpl) (j k : ℕ), (∀ T ∈ ts, ∀ r ∈ rowsAt T.gates 0, rowLocLt (nlocs T.gates) r = true) →
      ∀ r ∈ rowsAt (subsG σ ts j k).1 k, rowLocLt (k + (ts.map fun T => nlocs T.gates).sum) r = true
  | [], _, _, _, r, hr => by simp [subsG] at hr
  | T :: ts, j, k, hT, r, hr => by
    simp only [subsG, rowsAt_append, List.mem_append, nlocs_subL] at hr
    rcases hr with hr | hr
    · have hs := rowsAt_sub (σ j) k T.gates 0
      rw [Nat.add_zero] at hs
      rw [hs] at hr
      obtain ⟨r0, hr0, rfl⟩ := List.mem_map.1 hr
      refine rowLocLt_mono ?_ (rowLocLt_sub (hT T List.mem_cons_self r0 hr0)
        (fun i => locLt_le (Nat.zero_le _) (hσ j i)) le_rfl)
      simp only [List.map_cons, List.sum_cons]; omega
    · have := subsG_rows_loc σ hσ ts (j + 1) (k + nlocs T.gates) (fun T' hT' => hT T' (List.mem_cons_of_mem _ hT')) r hr
      simpa [Nat.add_assoc] using this

theorem kSig_loc (ws : List ℕ) (j i : ℕ) : locLt 0 (N4s.kSig ws j i) = true := by
  unfold N4s.kSig; split_ifs <;> rfl

/-- **A prepared op's structural fit.** -/
def kpFit (kp : KP) : Bool :=
  if kp.ok then linCellOk kp.one && kp.ins.all linCellOk && kp.subs.all (fun x => psLocOk x.2.1 x.1) &&
    kp.mux.all (rowLocLt lRoom) && kp.copy.all rowCellOk && decide ((kp.subs.map fun x => x.2.1).sum ≤ lRoom)
  else kp.alt.all rowCellOk

/-- **A fitting prepared op's rows fit.** -/
theorem kpFit_rows (P : Params) (cs : CS) (op : Op) (outs : List Slot) (h : kpFit (kpOf P cs op outs) = true) :
    ∀ r ∈ N4s.kRows N4s.kRS N4s.repB N4s.cbRS P cs op outs, rowCellOk r = true := by
  unfold kpOf at h
  unfold N4s.kRows
  cases hbs : N4s.kBlocks N4s.kRS cs op with
  | none => simp only [hbs, kpFit] at h; simpa using h
  | some bs =>
    simp only [hbs] at h ⊢
    by_cases hc : (N4s.outsOk N4s.kRS.tys outs && bs.all (fun b => N4s.kRS.inOk b.1) &&
        (N4s.kIns P bs ++ N4s.outF outs).all (linLt N4s.repB)) = true
    · rw [if_pos hc] at h ⊢
      simp only [kpFit, ite_true, Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq] at h
      obtain ⟨⟨⟨⟨⟨h1, hins⟩, hsubs⟩, hmux⟩, hcopy⟩, hN⟩ := h
      have hT : N4s.kTpl N4s.kRS op bs = kmuxT (N4s.kSig (bs.map fun b => b.2.length)) (bs.map fun b => b.2.length).sum 2
          ((rsTs bs).map fun T => (⟨sgGates T.1 0, T.2⟩ : Tpl)) := by
        simp only [N4s.kTpl, rsTs, List.map_cons, List.map_nil, ← rsT_segs]; rfl
      rw [N4s.rowsTR_eq, hT]
      simp only [kmuxT, tpl_rows_eq, rowsAt_append, List.map_append, List.mem_append, List.mem_map]
      simp only [nlocs_subsG, subsG_two, List.map_map, Function.comp_def, nlocs_sgGates] at hmux hcopy hN ⊢
      have h3 : (List.map (fun T => ({ gates := sgGates T.1 0, outs := T.2 } : Tpl)) (rsTs bs)).length = 3 := by
        simp [rsTs]
      simp only [muxG] at hmux
      rw [h3, Nat.zero_add]
      rintro r ((⟨a, ha, rfl⟩ | ⟨a, ha, rfl⟩) | hr)
      · apply instRow_cellOk h1 hins
        have := subsG_rows_loc _ (kSig_loc _) _ 0 0 (fun T hT r hr => ?_) a ha
        · refine rowLocLt_mono ?_ this
          simpa [nlocs_sgGates, List.map_map, Function.comp_def] using hN
        · obtain ⟨T', hT', rfl⟩ := List.mem_map.1 hT
          rw [nlocs_sgGates]
          exact psLocOk_rows _ 0 0 T'.1 (hsubs _ (List.mem_map_of_mem hT')) r hr
      · exact instRow_cellOk h1 hins (hmux a ha)
      · exact hcopy r hr
    · rw [if_neg hc] at h ⊢
      simp only [kpFit] at h; simpa using h

theorem blkGo_sub : ∀ (X : ℕ) (bs : List RBlk) (a : List (Row × ℕ)) (b : List (ℕ × KP)),
    (∀ p ∈ a, p ∈ (blkGo X bs a b).1) ∧ ∀ x ∈ b, x ∈ (blkGo X bs a b).2
  | _, [], a, b => ⟨fun _ h => h, fun _ h => h⟩
  | X, .sp l :: bs, a, b => by
    obtain ⟨h1, h2⟩ := blkGo_sub (X + l.length) bs ((l.zipIdx X).reverseAux a) b
    refine ⟨fun p hp => h1 p ?_, h2⟩
    rw [List.reverseAux_eq]; exact List.mem_append_right _ hp
  | X, .rs P cs op outs :: bs, a, b => by
    obtain ⟨h1, h2⟩ := blkGo_sub (X + kpLen (kpOf P cs op outs)) bs a ((X, kpOf P cs op outs) :: b)
    exact ⟨h1, fun x hx => h2 x (List.mem_cons_of_mem _ hx)⟩

/-- Every replay row is a row block's (at some index) or a prepared op's. -/
theorem blkGo_mem : ∀ (X : ℕ) (bs : List RBlk) (a : List (Row × ℕ)) (b : List (ℕ × KP)),
    ∀ r ∈ bs.flatMap RBlk.rows, (∃ i, (r, i) ∈ (blkGo X bs a b).1) ∨
      ∃ Y P cs op outs, (Y, kpOf P cs op outs) ∈ (blkGo X bs a b).2 ∧
        r ∈ N4s.kRows N4s.kRS N4s.repB N4s.cbRS P cs op outs
  | _, [], _, _, r, hr => by simp only [List.flatMap_nil, List.not_mem_nil] at hr
  | X, .sp l :: bs, a, b, r, hr => by
    rw [List.flatMap_cons, List.mem_append] at hr
    rcases hr with hr | hr
    · left
      obtain ⟨i, hi⟩ : ∃ i, (r, i) ∈ l.zipIdx X := by
        obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem hr
        exact ⟨X + j, List.mk_mem_zipIdx_iff_le_and_getElem?_sub.2 ⟨by omega, by simp only [RBlk.rows] at hj ⊢; simp [hj]⟩⟩
      refine ⟨i, (blkGo_sub _ bs _ b).1 _ ?_⟩
      rw [List.reverseAux_eq]; exact List.mem_append_left _ (List.mem_reverse.2 hi)
    · exact blkGo_mem _ bs _ b r hr
  | X, .rs P cs op outs :: bs, a, b, r, hr => by
    rw [List.flatMap_cons, List.mem_append] at hr
    rcases hr with hr | hr
    · exact Or.inr ⟨X, P, cs, op, outs, (blkGo_sub _ bs a _).2 _ List.mem_cons_self, hr⟩
    · exact blkGo_mem _ bs _ _ r hr

/-- **The structural `RepFit` check** on the split (prototype 0). -/
def repFitS (q : List (Row × ℕ) × List (ℕ × KP)) : Bool :=
  decide (q.1.length + (q.2.map fun x => kpLen x.2).sum ≤ slotM4) && q.1.all (fun p => rowCellOk p.1) &&
    q.2.all fun x => kpFit x.2

theorem repFitS_spec (bs : List RBlk) (h : repFitS (blkGo 0 bs [] []) = true) :
    repFitB 0 (bs.flatMap RBlk.rows) = true := by
  simp only [repFitS, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true] at h
  obtain ⟨⟨hl, hsp⟩, hkp⟩ := h
  have hlen := blkGo_len 0 bs [] []
  simp only [List.length_nil, List.map_nil, List.sum_nil, Nat.zero_add] at hlen
  simp only [repFitB, ↓reduceIte, Bool.and_eq_true, decide_eq_true_eq]
  refine ⟨by omega, List.all_eq_true.2 fun r hr => List.all_eq_true.2 ((rowCellOk_iff r).1 ?_)⟩
  rcases blkGo_mem 0 bs [] [] r hr with ⟨i, hi⟩ | ⟨Y, P, cs, op, outs, hm, hr⟩
  · exact hsp _ hi
  · exact kpFit_rows P cs op outs (hkp _ hm) r hr

/-! ## The prepared op's value, three matrices in one pass (CF2 step 3)

The sub-templates' inputs from arrays (block `j`'s slice of the op's inputs: no `kSig`/`pullE` per
wire), `psVal3` (row weights and per-call sums once for the three matrices; vanishing placeholders
skipped: the frame part's locals are `0`, the local part's `one` and inputs are `0`). -/

/-- `rmG` of the three matrices in one pass. -/
def rmG3 (gt : ℕ → F) (w : Asg) (X : ℕ) (rows : List Row) : F3 :=
  (rmG .a gt w X rows, rmG .b gt w X rows, rmG .c gt w X rows)

/-- The sub-templates' value, three matrices; block `j`'s inputs `vin[off …]`. -/
def subsV3 (gt t u : ℕ → F) (one : F) (vin : Array F) (lam : F) (gu : ℕ → F) (zl zi : Bool) (ws : List ℕ) :
    List (List PS × ℕ × ℕ) → ℕ → ℕ → ℕ → ℕ → F3
  | [], _, _, _, _ => (0, 0, 0)
  | (ps, nl, nr) :: l, j, off, k, X =>
    let wj := ws.getD j 0
    let vj := (Array.range wj).map fun i => vin.getD (off + i) 0
    let e : Env := ⟨one, fun i => vj.getD i 0, fun x => if lam = 0 then 0 else mul1 lam (gu (2 ^ 16 + (k + x)))⟩
    add3 (psVal3 gt t u e lam (2 ^ 16 + k) X zl zi ps) (subsV3 gt t u one vin lam gu zl zi ws l (j + 1) (off + wj) (k + nl) (X + nr))

/-- **The prepared `rsWeight` op's value, three matrices.** -/
def kopV3 (gt gu t u : ℕ → F) (w : Asg) (lam : F) (X : ℕ) (kp : KP) : F3 :=
  if kp.ok then
    let vin := (kp.ins.map (Lin.ev w)).toArray
    let one := kp.one.ev w
    let zi := decide (one = 0) && vin.all fun v => decide (v = 0)
    let e : Env := ⟨one, fun i => vin.getD i 0, fun x => lam * gu (2 ^ 16 + x)⟩
    let R := (kp.subs.map fun p => p.2.2).sum
    add3 (add3 (subsV3 gt t u one vin lam gu (decide (lam = 0)) zi kp.ws kp.subs 0 0 0 X) (tmG3 gt e (X + R) kp.mux))
      (rmG3 gt w (X + R + kp.mux.length) kp.copy)
  else rmG3 gt w X kp.alt

theorem take_succ_sum (ws : List ℕ) (j : ℕ) : (ws.take (j + 1)).sum = (ws.take j).sum + ws.getD j 0 := by
  rw [List.take_succ, List.sum_append, List.getD_eq_getElem?_getD]
  cases ws[j]? <;> simp

theorem subsV3_eq (gt t u : ℕ → F) (one : F) (vin : Array F) (lam : F) (gu : ℕ → F) (zi : Bool) (ws : List ℕ)
    (hgt : ∀ x, gt x = gN 20 t x) (hzi : zi = true → one = 0 ∧ ∀ i, vin.getD i 0 = 0) :
    ∀ (l : List (List PS × ℕ × ℕ)) (j k X : ℕ),
      subsV3 gt t u one vin lam gu (decide (lam = 0)) zi ws l j (ws.take j).sum k X =
        (subsV .a gt t u ⟨one, fun i => vin.getD i 0, fun x => lam * gu (2 ^ 16 + x)⟩ lam (N4s.kSig ws) l j k X,
          subsV .b gt t u ⟨one, fun i => vin.getD i 0, fun x => lam * gu (2 ^ 16 + x)⟩ lam (N4s.kSig ws) l j k X,
          subsV .c gt t u ⟨one, fun i => vin.getD i 0, fun x => lam * gu (2 ^ 16 + x)⟩ lam (N4s.kSig ws) l j k X)
  | [], _, _, _ => rfl
  | (ps, nl, nr) :: l, j, k, X => by
    rw [subsV3, ← take_succ_sum, subsV3_eq gt t u one vin lam gu zi ws hgt hzi l (j + 1)]
    simp only [subsV, add3]
    have he : (⟨one, fun i => ((Array.range (ws.getD j 0)).map fun i => vin.getD ((ws.take j).sum + i) 0).getD i 0,
        fun x => if lam = 0 then 0 else mul1 lam (gu (2 ^ 16 + (k + x)))⟩ : Env) =
        pullE ⟨one, fun i => vin.getD i 0, fun x => lam * gu (2 ^ 16 + x)⟩ (N4s.kSig ws j) k := by
      simp only [pullE, Env.mk.injEq, true_and]
      refine ⟨?_, funext fun x => ?_⟩
      swap
      · rw [mul1_eq]; split_ifs with h0 <;> simp [h0]
      funext i
      rw [Array.getD_eq_getD_getElem?, Array.getElem?_map, Array.getElem?_range]
      unfold N4s.kSig
      split_ifs with h
      · simp [LinT.ev, I, Wire.ev]
      · simp [LinT.ev]
    have hl : decide (lam = 0) = true → ∀ x, (pullE ⟨one, fun i => vin.getD i 0, fun x => lam * gu (2 ^ 16 + x)⟩
        (N4s.kSig ws j) k).loc x = 0 := fun h x => by
      simp only [decide_eq_true_eq] at h; simp [pullE, h]
    have hi : zi = true → (pullE ⟨one, fun i => vin.getD i 0, fun x => lam * gu (2 ^ 16 + x)⟩
        (N4s.kSig ws j) k).one = 0 ∧ ∀ i, (pullE ⟨one, fun i => vin.getD i 0, fun x => lam * gu (2 ^ 16 + x)⟩
        (N4s.kSig ws j) k).inp i = 0 := fun h => by
      obtain ⟨h1, h2⟩ := hzi h
      refine ⟨h1, fun i => ?_⟩
      simp only [pullE]
      unfold N4s.kSig
      split_ifs <;> simp [LinT.ev, I, Wire.ev, h2]
    rw [he, psVal3_eq _ _ _ _ _ _ _ hgt hl hi]

theorem rmG3_eq (gt : ℕ → F) (w : Asg) (X : ℕ) (rows : List Row) :
    rmG3 gt w X rows = (rmG .a gt w X rows, rmG .b gt w X rows, rmG .c gt w X rows) := rfl

/-- **`kopV3` is `kopV`'s three values.** -/
theorem kopV3_eq (gt gu t u : ℕ → F) (w : Asg) (lam : F) (X : ℕ) (kp : KP) (hgt : ∀ x, gt x = gN 20 t x) :
    kopV3 gt gu t u w lam X kp = (kopV .a gt gu t u w lam X kp, kopV .b gt gu t u w lam X kp, kopV .c gt gu t u w lam X kp) := by
  unfold kopV3 kopV
  split_ifs with h
  · dsimp only
    have hzi : (decide (kp.one.ev w = 0) && (kp.ins.map (Lin.ev w)).toArray.all fun v => decide (v = 0)) = true →
        kp.one.ev w = 0 ∧ ∀ i, (kp.ins.map (Lin.ev w)).toArray.getD i 0 = 0 := fun hz => by
      simp only [Bool.and_eq_true, decide_eq_true_eq, Array.all_eq_true] at hz
      refine ⟨hz.1, fun i => ?_⟩
      rw [Array.getD_eq_getD_getElem?]
      by_cases hi : i < (kp.ins.map (Lin.ev w)).toArray.size
      · rw [Array.getElem?_eq_getElem hi]; simpa using hz.2 i hi
      · rw [Array.getElem?_eq_none (by omega)]; rfl
    have := subsV3_eq gt t u (kp.one.ev w) (kp.ins.map (Lin.ev w)).toArray lam gu _ kp.ws hgt hzi kp.subs 0 0 X
    simp only [List.take_zero, List.sum_nil] at this
    rw [this, tmG3_eq gt t _ hgt, rmG3_eq]
    simp only [add3]
  · rfl

/-- The prepared ops' values, one pass per op. -/
def kpsV3F (gt gu t u : ℕ → F) (w : Asg) (lam : F) (kps : List (ℕ × KP)) : F3 :=
  sum3 (fun q => kopV3 gt gu t u w lam q.1 q.2) kps

theorem kpsV3F_eq (gt gu t u : ℕ → F) (w : Asg) (lam : F) (kps : List (ℕ × KP)) (hgt : ∀ x, gt x = gN 20 t x) :
    kpsV3F gt gu t u w lam kps = kpsV3 gt gu t u w lam kps := by
  simp only [kpsV3F, kpsV3, sum3_eq, kopV3_eq _ _ _ _ _ _ _ _ hgt, sumL_eq]

end Rev4
end FR
