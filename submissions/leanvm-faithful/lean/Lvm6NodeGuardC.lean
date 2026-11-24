-- New for lvm6 (WP GRD, RV4 M1 and M3). Run-time Bools for the program facts the wiring bridge takes (`wf`,
-- `twinsOk`, `NoE3`) and for the stream and signature cells' words, each with its soundness lemma; and the `σ_leaf`
-- copy rows (`sigLeafCopy6_spec`) on the deployed circuit. For `staticOk6` (NODE3 phase 3 adds them).
import Lvm6NodeSlots
import LvmQBuildWf

/-!
# Program and cell facts as guard Bools (WP GRD)

Each Bool runs once per verifier process in one pass over the templates or cells (no instance or entry
enumeration); each comes as `xB` + `xB_sound` to a named Prop (PFW: `Chk.ofBool` at PF-0, a field at PF-1).
* **`wfB`** (`Q.wf = true`): `Program.wf` recomputes `Q.start`, `Block.rank` and `Block.tw` per row (quadratic in a
  glue block's template). `wfB` walks the blocks with the running pointer (season 1's `BlocksOk`,
  `wf_of_blocksOk`) and each template with the running rank; `tw` once per block.
* **`twinsOkB`** (`Q.twinsOk`, already one pass). **`noE3B`** (`NoE3 Q lay`): every cell an entry reads is a `K`
  cell, every auxiliary weight is in `K`.
* **`streamCellsB`**, **`sigCellsB`** (RV4 M3; premise `lay.okB Q`, the guard's first check) over the parameters
  `CellPar`: **`StreamCells`**, **`SigCells`** (`CellsAt`: no constant, word `base + j`; words through `FL`).
* **`GrdFacts Ti c`**: the five as named fields (`wf`, `twinsOk`, `noE3`, `streamCells`, `sigCells`);
  **`grdB`/`grdB_sound`** checks all five on one `FL`. `cellPar6`, `cells6`: the deployed instance.
  **`memTi_cell`**: such a cell's value is its word's.
* **`sigLeaf_of_tgoodE`**: `σ_leaf` as the leaf walk reads it (`sigIl.sg = dstC`) is `σ_leaf` as stored
  (`sgC + 597`), from `famQ6`'s copy rows (`sigLeafCopy6_spec`) and the flag.
-/

set_option autoImplicit false

namespace Lvm6.Node.Dep

open Lvm Lvm.Loop Lvm.Loop.Build Lvm.Typed Lvm.QSig Lvm.E2V LeanVM.Protocol
open Lvm6.Ty (TInst6 TGoodE NoE3)

/-! ## `wf` in one pass -/

/-- `Block.tw` from its two values. -/
def twOf (tK tE : ℕ) : Ty → ℕ
  | .K => tK
  | .E => tE

theorem twOf_tw (B : Block) : twOf (B.tw .K) (B.tw .E) = B.tw := by
  funext τ
  cases τ <;> rfl

/-- The template walk of a block at `p`: row `r` at the running rank `c`. -/
def tplOkL (p : Ptr) (dims : List ℕ) (tK tE : ℕ) : Ptr → List Row → Bool
  | _, [] => true
  | c, r :: rs => rowOkC (fun τ ↦ p.at τ + c.at τ) dims (twOf tK tE) r && tplOkL p dims tK tE (c.adv [.row r]) rs

/-- The block walk: every block at its pointer. -/
def blocksOkL : Ptr → List Block → Bool
  | _, [] => true
  | p, B :: bs => tplOkL p B.dims (B.tw .K) (B.tw .E) ⟨0, 0⟩ B.tpl && blocksOkL (p.advBs [B]) bs

/-- **`Program.wf` in one pass.** -/
def wfB (Q : Program) : Bool := blocksOkL ⟨Q.nInK, Q.nInE⟩ Q.blocks

theorem tplOkL_sound (p : Ptr) (dims : List ℕ) (tK tE : ℕ) : ∀ (c : Ptr) (rs : List Row),
    tplOkL p dims tK tE c rs = true → ∀ t < rs.length,
      rowOkC (fun τ ↦ p.at τ + (c.at τ + ((rs.take t).map (Row.w τ)).sum)) dims (twOf tK tE)
        (rs.getD t default) = true
  | _, [], _, t, ht => absurd ht (Nat.not_lt_zero t)
  | c, r :: rs, h, t, ht => by
    simp only [tplOkL, Bool.and_eq_true] at h
    cases t with
    | zero =>
      have e : (fun τ ↦ p.at τ + (c.at τ + (((r :: rs).take 0).map (Row.w τ)).sum)) = fun τ ↦ p.at τ + c.at τ := by
        funext τ
        simp
      rw [e]
      exact h.1
    | succ t =>
      have ih := tplOkL_sound p dims tK tE (c.adv [.row r]) rs h.2 t (by simpa using ht)
      have e : (fun τ ↦ p.at τ + (c.at τ + (((r :: rs).take (t + 1)).map (Row.w τ)).sum)) =
          fun τ ↦ p.at τ + ((c.adv [.row r]).at τ + ((rs.take t).map (Row.w τ)).sum) := by
        funext τ
        cases τ <;> simp [Ptr.at, Ptr.adv, segsW, Seg.w] <;> omega
      rw [e, List.getD_cons_succ]
      exact ih

theorem blockOkAt_of_tplOkL {p : Ptr} {B : Block} (h : tplOkL p B.dims (B.tw .K) (B.tw .E) ⟨0, 0⟩ B.tpl = true) :
    blockOkAt p B = true := by
  simp only [blockOkAt, List.all_eq_true, List.mem_range]
  intro t ht
  have := tplOkL_sound p B.dims _ _ _ _ h t ht
  rw [twOf_tw] at this
  have e : (fun τ ↦ p.at τ + B.rank τ t) =
      fun τ ↦ p.at τ + ((⟨0, 0⟩ : Ptr).at τ + ((B.tpl.take t).map (Row.w τ)).sum) := by
    funext τ
    cases τ <;> simp [Ptr.at, Block.rank]
  rw [e]
  exact this

theorem blocksOkL_sound : ∀ (p : Ptr) (bs : List Block), blocksOkL p bs = true → BlocksOk p bs
  | _, [], _ => trivial
  | p, B :: bs, h => by
    simp only [blocksOkL, Bool.and_eq_true] at h
    exact ⟨blockOkAt_of_tplOkL h.1, blocksOkL_sound _ bs h.2⟩

theorem wfB_sound {Q : Program} (h : wfB Q = true) : Q.wf = true :=
  wf_of_blocksOk Q (blocksOkL_sound _ _ h)

/-! ## `NoE3` from the templates and the auxiliary rows -/

/-- Operands `0 … n-1` of `r` are `K` cells. -/
def argsKB (r : Row) (n : ℕ) : Bool := (List.range n).all fun k ↦ (r.args.getD k default).ty == .K

/-- Every cell an entry of `r` reads (`instEntsX`) is a `K` cell. -/
def rowNoE3B (r : Row) : Bool :=
  match r.op with
  | .muladd => argsKB r 3 && r.ty == .K
  | .lin _ _ => argsKB r 2 && r.ty == .K
  | .assert0 => argsKB r 2
  | .fixmul => argsKB r 2 && r.ty == .K
  | .e2 .mul false => argsKB r 6 && r.ty == .K
  | .e2 (.lin _ _ _) false => argsKB r 4 && r.ty == .K
  | _ => true

/-- A coefficient in `K`. -/
def isKB (w : FE) : Bool := decide (w.c₁ = 0) && decide (w.c₂ = 0)

/-- An auxiliary operand reads no `E` cell. -/
def aopNoE3B : AOp → Bool
  | .cell a => a.ty == .K
  | _ => true

/-- **`NoE3` at run time**: the templates' rows, the auxiliary rows' weights and cells. -/
def noE3B (Q : Program) (lay : Lay) : Bool :=
  Q.blocks.all (fun B ↦ B.tpl.all rowNoE3B) &&
    lay.aux.all fun A ↦ A.rows.all fun r ↦ r.ops.all fun e ↦ isKB e.2.2 && aopNoE3B e.2.1

/-- Weighted words with coefficients in `K`. -/
def KL (l : List (ℕ × FE)) : Prop := ∀ q ∈ l, q.2.c₁ = 0 ∧ q.2.c₂ = 0

/-- Entries with coefficients in `K`. -/
def KE (l : List Ent) : Prop := ∀ e ∈ l, e.c.c₁ = 0 ∧ e.c.c₂ = 0

theorem kl_append {l l' : List (ℕ × FE)} (h : KL l) (h' : KL l') : KL (l ++ l') := fun q hq ↦
  (List.mem_append.mp hq).elim (h q) (h' q)

theorem kl_single (y : ℕ) (c : FK) : KL [(y, FE.ofK c)] := by
  intro q hq
  rw [List.mem_singleton.mp hq]
  exact ⟨rfl, rfl⟩

theorem ke_append {l l' : List Ent} (h : KE l) (h' : KE l') : KE (l ++ l') := fun e he ↦
  (List.mem_append.mp he).elim (h e) (h' e)

theorem ke_tagE {o x : ℕ} {l : List (ℕ × FE)} (h : KL l) : KE (tagE o x l) := by
  intro e he
  obtain ⟨q, hq, rfl⟩ := List.mem_map.mp he
  exact h q hq

theorem isK_ofK_c0 {w : FE} (hw : w.c₁ = 0 ∧ w.c₂ = 0) : w = FE.ofK w.c₀ := by
  obtain ⟨a, b, c⟩ := w
  simp only at hw
  rw [hw.1, hw.2]
  rfl

theorem kl_cellEnts_K (lay : Lay) (n : ℕ) {w : FE} (hw : w.c₁ = 0 ∧ w.c₂ = 0) : KL (lay.cellEnts .K n w) := by
  rcases hc : lay.cst? n with _ | v
  · simp only [Lay.cellEnts, hc]
    intro q hq
    rw [List.mem_singleton.mp hq]
    exact hw
  · simp only [Lay.cellEnts, hc]
    have e : w * FE.ofK v = FE.ofK (w.c₀ * v) := by
      have h1 : w * FE.ofK v = FE.ofK w.c₀ * FE.ofK v := congrArg (· * FE.ofK v) (isK_ofK_c0 hw)
      rw [h1]
      exact (map_mul FE.ofKRingHom w.c₀ v).symm
    rw [e]
    exact kl_single _ _

theorem argsKB_spec {r : Row} {n : ℕ} (h : argsKB r n = true) : ∀ k < n, (r.args.getD k default).ty = .K := by
  intro k hk
  have := List.all_eq_true.mp h k (List.mem_range.mpr hk)
  simpa using this

theorem kl_argEnts (lay : Lay) (i : Inst) {k : ℕ} (hk : (i.row.args.getD k default).ty = .K) {w : FE}
    (hw : w.c₁ = 0 ∧ w.c₂ = 0) : KL (lay.argEnts i k w) := by
  unfold Lay.argEnts
  rw [hk]
  exact kl_cellEnts_K lay _ hw

theorem kl_resEnts (lay : Lay) (i : Inst) (h : i.row.ty = .K) : KL (lay.resEnts i) := by
  unfold Lay.resEnts
  rw [h]
  exact kl_cellEnts_K lay _ ⟨rfl, rfl⟩

theorem one_isK : (1 : FE).c₁ = 0 ∧ (1 : FE).c₂ = 0 := ⟨rfl, rfl⟩

theorem ofK_isK (c : FK) : (FE.ofK c).c₁ = 0 ∧ (FE.ofK c).c₂ = 0 := ⟨rfl, rfl⟩

/-- **An instance of a checked row has entries in `K`.** -/
theorem ke_instEntsX (Q : Program) (lay : Lay) (i : Inst) (h : rowNoE3B i.row = true) : KE (instEntsX Q lay i) := by
  unfold rowNoE3B at h
  unfold instEntsX
  split
  · rename_i heq
    rw [heq] at h
    simp only [Bool.and_eq_true, beq_iff_eq] at h
    have a := argsKB_spec h.1
    refine ke_append (ke_append (ke_append (ke_append (ke_append (ke_append (ke_append ?_ ?_) ?_) ?_) ?_) ?_) ?_) ?_ <;>
      refine ke_tagE ?_
    all_goals first
      | exact kl_argEnts lay i (a _ (by norm_num)) one_isK
      | exact kl_resEnts lay i h.2
      | exact kl_cellEnts_K lay _ one_isK
  · rename_i k k₀ k₁ heq
    rw [heq] at h
    simp only [Bool.and_eq_true, beq_iff_eq] at h
    have a := argsKB_spec h.1
    refine ke_append (ke_append (ke_append (ke_tagE ?_) (ke_tagE ?_)) (ke_tagE ?_)) (ke_tagE ?_)
    · exact kl_append (kl_append (kl_argEnts lay i (a 0 (by norm_num)) one_isK)
        (kl_argEnts lay i (a 2 (by norm_num)) (ofK_isK k))) (kl_single _ _)
    · exact kl_append (kl_append (kl_argEnts lay i (a 1 (by norm_num)) one_isK)
        (kl_argEnts lay i (a 3 (by norm_num)) (ofK_isK k))) (kl_single _ _)
    · exact kl_resEnts lay i h.2
    · exact kl_cellEnts_K lay _ one_isK
  · intro e he
    simp at he
  · rename_i hn1 hn2 hn3
    unfold instEnts
    split
    · rename_i heq
      rw [heq] at h
      simp only [Bool.and_eq_true, beq_iff_eq] at h
      have a := argsKB_spec h.1
      exact ke_append (ke_append (ke_append (ke_tagE (kl_argEnts lay i (a 0 (by norm_num)) one_isK))
        (ke_tagE (kl_argEnts lay i (a 1 (by norm_num)) one_isK)))
        (ke_tagE (kl_argEnts lay i (a 2 (by norm_num)) one_isK))) (ke_tagE (kl_resEnts lay i h.2))
    · rename_i k k' heq
      rw [heq] at h
      simp only [Bool.and_eq_true, beq_iff_eq] at h
      have a := argsKB_spec h.1
      exact ke_append (ke_tagE (kl_append (kl_append (kl_argEnts lay i (a 0 (by norm_num)) one_isK)
        (kl_argEnts lay i (a 1 (by norm_num)) (ofK_isK k))) (kl_single _ _))) (ke_tagE (kl_resEnts lay i h.2))
    · rename_i heq
      rw [heq] at h
      have a := argsKB_spec h
      exact ke_append (ke_tagE (kl_argEnts lay i (a 1 (by norm_num)) one_isK))
        (ke_tagE (kl_argEnts lay i (a 0 (by norm_num)) one_isK))
    · rename_i heq
      rw [heq] at h
      simp only [Bool.and_eq_true, beq_iff_eq] at h
      have a := argsKB_spec h.1
      exact ke_append (ke_tagE (kl_append (kl_argEnts lay i (a 0 (by norm_num)) (ofK_isK _))
        (kl_argEnts lay i (a 1 (by norm_num)) one_isK))) (ke_tagE (kl_resEnts lay i h.2))
    · intro e he
      simp at he

theorem getD_mem_or {α : Type} (l : List α) (n : ℕ) (d : α) : l.getD n d ∈ l ∨ l.getD n d = d := by
  rw [List.getD_eq_getElem?_getD]
  cases hn : l[n]? with
  | none => exact Or.inr rfl
  | some x => exact Or.inl (List.mem_of_getElem? hn)

/-- **The auxiliary rows' entries are in `K`.** -/
theorem ke_auxEnts (lay : Lay)
    (h : (lay.aux.all fun A ↦ A.rows.all fun r ↦ r.ops.all fun e ↦ isKB e.2.2 && aopNoE3B e.2.1) = true) :
    KE (auxEnts lay) := by
  intro e he
  simp only [auxEnts, List.mem_flatMap, List.mem_range] at he
  obtain ⟨k, -, j, -, r, -, he⟩ := he
  unfold auxRowEnts at he
  obtain ⟨op, hop, he⟩ := List.mem_flatMap.mp he
  have hrow : ∀ A ∈ lay.aux, ∀ R ∈ A.rows, ∀ o ∈ R.ops, isKB o.2.2 = true ∧ aopNoE3B o.2.1 = true := by
    intro A hA R hR o ho
    have := List.all_eq_true.mp (List.all_eq_true.mp (List.all_eq_true.mp h A hA) R hR) o ho
    simpa only [Bool.and_eq_true] using this
  have hk : isKB op.2.2 = true ∧ aopNoE3B op.2.1 = true := by
    rcases getD_mem_or lay.aux k default with hA | hA
    · rcases getD_mem_or (lay.aux.getD k default).rows r default with hR | hR
      · exact hrow _ hA _ hR op hop
      · rw [hR] at hop
        exact absurd hop (List.not_mem_nil)
    · rw [hA] at hop
      exact absurd hop (List.not_mem_nil)
  have hw : op.2.2.c₁ = 0 ∧ op.2.2.c₂ = 0 := by
    simpa only [isKB, Bool.and_eq_true, decide_eq_true_eq] using hk.1
  refine ke_tagE ?_ e he
  unfold Lay.aopEnts
  split
  · intro q hq
    rw [List.mem_singleton.mp hq]
    exact hw
  · rename_i a heq
    have ha : a.ty = .K := by
      have := hk.2
      rw [heq] at this
      simpa [aopNoE3B] using this
    rw [ha]
    exact kl_cellEnts_K lay _ hw
  · intro q hq
    rw [List.mem_singleton.mp hq]
    exact hw

theorem noE3B_sound {Q : Program} {lay : Lay} (h : noE3B Q lay = true) : NoE3 Q lay := by
  simp only [noE3B, Bool.and_eq_true] at h
  intro e he
  rcases List.mem_append.mp he with he | he
  · obtain ⟨i, hi, he⟩ := List.mem_flatMap.mp he
    obtain ⟨b, hb, jf, -, t, ht, rfl⟩ := (Program.mem_insts Q i).mp hi
    have hB : Q.blk b ∈ Q.blocks := by
      rw [Program.blk_eq Q hb]
      exact List.getElem_mem hb
    have hR : (Q.blk b).tpl.getD t default ∈ (Q.blk b).tpl := by
      rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem ht, Option.getD_some]
      exact List.getElem_mem ht
    have hrow : rowNoE3B (Q.inst b jf t).row = true :=
      List.all_eq_true.mp (List.all_eq_true.mp h.1 _ hB) _ hR
    exact ke_instEntsX Q lay _ hrow e he
  · exact ke_auxEnts lay h.2 e he

/-! ## The program facts as fields (`xB` + `xB_sound`, for `Chk.ofBool` at PF-0) -/

/-- `twinsOk`'s Bool (`Program.twinsOk`, already one pass). -/
def twinsOkB (Q : Program) : Bool := Q.twinsOk

theorem twinsOkB_sound {Q : Program} (h : twinsOkB Q = true) : Q.twinsOk = true := h

/-! ## The stream and signature cells' words (RV4 M3) -/

open Lvm.Typed.K (FL)

/-- Cells `c + j` (`j < n`) are no constant and have the words `w + j` (through `FL`'s one owner search). -/
def cellsAtB (F : FL) (c w n : ℕ) : Bool :=
  (List.range n).all fun j ↦ (F.cst (c + j)).isNone && F.wordK (c + j) == w + j

/-- **Cells `c + j` (`j < n`) are no constant and have the words `w + j`.** -/
def CellsAt (lay : Lay) (c w n : ℕ) : Prop := ∀ j < n, lay.cst? (c + j) = none ∧ lay.wordK (c + j) = w + j

theorem cellsAtB_sound {Q : Program} {lay : Lay} (hlay : lay.okB Q = true) {c w n : ℕ}
    (h : cellsAtB (FL.ofLay Q lay) c w n = true) : CellsAt lay c w n := by
  intro j hj
  have := List.all_eq_true.mp h j (List.mem_range.mpr hj)
  simp only [Bool.and_eq_true, Option.isNone_iff_eq_none, beq_iff_eq] at this
  rw [K.fl_cst, K.fl_wordK Q lay hlay] at this
  exact this

/-! ### Per region (ST-2): linear in blocks + constants + regions, independent of `n` -/

/-- The first `K` input/dense region of `ds` covering `[c, c+n)`, provided no earlier `K` region meets it. -/
def firstCover (c n : ℕ) : List DReg → Option DReg
  | [] => none
  | d :: ds =>
    if (d.ty == .K && decide (d.lo ≤ c ∧ c + n ≤ d.lo + d.n)) = true then some d
    else if (d.ty == .K && decide (d.lo < c + n ∧ c < d.lo + d.n)) = true then none
    else firstCover c n ds

theorem firstCover_find (c n : ℕ) : ∀ (ds : List DReg) (d : DReg), firstCover c n ds = some d →
    ∀ j < n, ds.find? (fun d' ↦ d'.ty == .K && decide (d'.lo ≤ c + j ∧ c + j < d'.lo + d'.n)) = some d ∧
      d.lo ≤ c ∧ c + n ≤ d.lo + d.n
  | [], _, h, _, _ => by simp [firstCover] at h
  | d0 :: ds, d, h, j, hj => by
    unfold firstCover at h
    by_cases h1 : (d0.ty == .K && decide (d0.lo ≤ c ∧ c + n ≤ d0.lo + d0.n)) = true
    · rw [if_pos h1] at h
      cases h
      simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at h1
      refine ⟨?_, h1.2.1, h1.2.2⟩
      rw [List.find?_cons_of_pos]
      simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq]
      exact ⟨h1.1, by omega, by omega⟩
    · rw [if_neg h1] at h
      by_cases h2 : (d0.ty == .K && decide (d0.lo < c + n ∧ c < d0.lo + d0.n)) = true
      · rw [if_pos h2] at h
        cases h
      · rw [if_neg h2] at h
        obtain ⟨ih, hlo, hhi⟩ := firstCover_find c n ds d h j hj
        refine ⟨?_, hlo, hhi⟩
        rw [List.find?_cons_of_neg]
        · exact ih
        · simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq, not_and] at h2 ⊢
          intro hty hl
          have := h2 hty
          omega

/-- **Cells `c + j` (`j < n`) per region**: no block's `K` results and no constant region meet `[c, c+n)`; the first
`K` input/dense region meeting it covers it, has one lane, and maps `c` to `w`. -/
def cellsAtRB (lay : Lay) (c w n : ℕ) : Bool :=
  lay.blocks.all (fun B ↦ decide (B.stK + B.twK * 2 ^ B.l ≤ c ∨ c + n ≤ B.stK)) &&
    lay.cst.all (fun r ↦ decide (r.1 + r.2.length ≤ c ∨ c + n ≤ r.1)) &&
    match firstCover c n (lay.dense ++ lay.inp) with
    | some d => decide (d.lanes ≤ 1) && decide (d.bases.getD 0 0 + (c - d.lo) = w)
    | none => false

theorem cellsAtRB_sound {lay : Lay} {c w n : ℕ} (h : cellsAtRB lay c w n = true) : CellsAt lay c w n := by
  intro j hj
  simp only [cellsAtRB, Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨hB, hC⟩, hD⟩ := h
  have hcst : lay.cst? (c + j) = none := by
    simp only [Lay.cst?, Option.map_eq_none_iff, List.find?_eq_none, decide_eq_true_eq, not_and, not_lt]
    intro r hr h1
    have := hC r hr
    omega
  refine ⟨hcst, ?_⟩
  have hown : lay.owner? .K (c + j) = none := by
    simp only [Lay.owner?, List.find?_eq_none, List.mem_range, decide_eq_true_eq, not_and, not_lt]
    intro b hb h1
    have hm : lay.blocks.getD b default ∈ lay.blocks := by
      rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hb, Option.getD_some]
      exact List.getElem_mem hb
    have := hB _ hm
    simp only [BLay.st, BLay.tw] at h1 ⊢
    omega
  split at hD
  · rename_i d hd
    simp only [Bool.and_eq_true, decide_eq_true_eq] at hD
    obtain ⟨hf, hlo, -⟩ := firstCover_find c n _ d hd j hj
    have hdr : lay.dreg? .K (c + j) = some d := hf
    simp only [Lay.wordK, hown, Lay.wordD, hdr, DReg.word, if_pos hD.1]
    omega
  · exact absurd hD (by simp)

/-- **The cell parameters**: the stream cells `[sb, sb + nS)` on the words from `bs` (the `S_flat` region), the
signature cells `[sg, sg + nG)` on the words from `bg` (the `σ` region). At PF-1: `sb`, `sg` from `NodeLay`, `bs`,
`bg` from `TyBase6`. -/
structure CellPar where
  sb : ℕ
  nS : ℕ
  bs : ℕ
  sg : ℕ
  nG : ℕ
  bg : ℕ

/-- **The stream cells' words** (`hM`, the trace reader, `ExtEq6`). -/
def StreamCells (Ti : TInst6) (c : CellPar) : Prop := CellsAt Ti.lay c.sb c.bs c.nS

/-- **The signature cells' words** (`σ'`, `σ_leaf` as stored). -/
def SigCells (Ti : TInst6) (c : CellPar) : Prop := CellsAt Ti.lay c.sg c.bg c.nG

def streamCellsB (Ti : TInst6) (c : CellPar) : Bool := cellsAtRB Ti.lay c.sb c.bs c.nS

def sigCellsB (Ti : TInst6) (c : CellPar) : Bool := cellsAtRB Ti.lay c.sg c.bg c.nG

theorem streamCellsB_sound {Ti : TInst6} {c : CellPar} (hlay : Ti.lay.okB Ti.Q = true)
    (h : streamCellsB Ti c = true) : StreamCells Ti c := (fun _ ↦ cellsAtRB_sound h) hlay

theorem sigCellsB_sound {Ti : TInst6} {c : CellPar} (hlay : Ti.lay.okB Ti.Q = true)
    (h : sigCellsB Ti c = true) : SigCells Ti c := (fun _ ↦ cellsAtRB_sound h) hlay

/-! ## GRD's facts as one structure -/

/-- **GRD's run-time facts**, one named field each (the M1 and M3 fields of `NodeLay.Deployed` at PF-1). -/
structure GrdFacts (Ti : TInst6) (c : CellPar) : Prop where
  wf : Ti.Q.wf = true
  twinsOk : Ti.Q.twinsOk = true
  noE3 : NoE3 Ti.Q Ti.lay
  streamCells : StreamCells Ti c
  sigCells : SigCells Ti c

/-- **All five** (the cells per region, `cellsAtRB`). -/
def grdB (Ti : TInst6) (c : CellPar) : Bool :=
  wfB Ti.Q && twinsOkB Ti.Q && noE3B Ti.Q Ti.lay && streamCellsB Ti c && sigCellsB Ti c

theorem grdB_sound {Ti : TInst6} {c : CellPar} (hlay : Ti.lay.okB Ti.Q = true) (h : grdB Ti c = true) :
    GrdFacts Ti c := by
  simp only [grdB, Bool.and_eq_true] at h
  obtain ⟨⟨⟨⟨hw, ht⟩, hn⟩, hs⟩, hg⟩ := h
  exact ⟨wfB_sound hw, twinsOkB_sound ht, noE3B_sound hn, streamCellsB_sound hlay hs, sigCellsB_sound hlay hg⟩

/-- The deployed cells (`Lvm6NodeDeploy`): `2^19` stream cells from `sbC`; `σ'` then `σ_leaf` as stored (`597`
each) from `sgC`; `bs`, `bg` are `TyBase6`'s (`StreamRegs6`'s witnesses). -/
def cellPar6 (bs bg : ℕ) : CellPar := ⟨sbC, 2 ^ 19, bs, sgC, 2 * 597, bg⟩

/-- **The cells at the deployed parameters**, spelled out (the forms of `hM`, the readers and `ExtEq6`). -/
theorem cells6 {Ti : TInst6} {bs bg : ℕ} (h : GrdFacts Ti (cellPar6 bs bg)) :
    (∀ j < 2 ^ 19, Ti.lay.cst? (sbC + j) = none ∧ Ti.lay.wordK (sbC + j) = bs + j) ∧
      (∀ i < 2 * 597, Ti.lay.cst? (sgC + i) = none ∧ Ti.lay.wordK (sgC + i) = bg + i) :=
  ⟨fun j hj ↦ h.streamCells j hj, fun i hi ↦ h.sigCells i hi⟩

/-- **A cell with no constant and the word `w` has `z w`.** -/
theorem memTi_cell {Ti : TInst6} {L : Lvm.M3.Lay} {pw : ℕ → FK} {p : Column L.nuMain × Column L.nuRec}
    {n w : ℕ} (hc : Ti.lay.cst? n = none) (hw : Ti.lay.wordK n = w) :
    (memTi Ti L pw p).k n = Ti.zOf L pw p.1 p.2 w := by
  simp only [memTi, memOf, hc, hw, Option.getD_none]

/-! ## `σ_leaf`'s copy rows -/

/-- **`σ_leaf` as the leaf walk reads it is `σ_leaf` as stored**, on the deployed circuit with the flag on. -/
theorem sigLeaf_of_ok {c : Ctx} {M : Mem} {lay : Lay} {p : Ptr} (h : OkAt c M (famQ6 lay) p)
    (hg : M.k (pbC + 1) = 1) : sigAtP M.k sigIl.sg = sigAt' M.k (sgC + 597) :=
  Lvm6.QD.sigLeafCopy6_spec (famQ6_parts h).2.2.2.1 hg

/-- **The same from the typed relation** (the wiring bridge `segs_of_tgoodE` at the deployed program). -/
theorem sigLeaf_of_tgoodE (Ti : TInst6) (L : Lvm.M3.Lay) (hτ : ∀ t ∈ Ti.mbT, t.τ ≤ L.μ) (pw : ℕ → FK)
    (p : Column L.nuMain × Column L.nuRec) (hQ : Ti.Q = progQ6 Ti.lay) (hwf : Ti.Q.wf = true)
    (htw : Ti.Q.twinsOk = true) (hE3 : NoE3 Ti.Q Ti.lay) (hok : Ti.Ok) (hrd : ReaddOk Ti.Q (memTi Ti L pw p))
    (hg : TGoodE Ti L hτ pw p) (hfl : (memTi Ti L pw p).k (pbC + 1) = 1) :
    sigAtP (memTi Ti L pw p).k sigIl.sg = sigAt' (memTi Ti L pw p).k (sgC + 597) :=
  sigLeaf_of_ok (segs_of_tgoodE (famQ6 Ti.lay) nK 0 Ti L hτ pw p hQ hwf htw hE3 hok hrd hg) hfl

end Lvm6.Node.Dep
