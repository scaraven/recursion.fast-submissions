-- New for lvm2 (roll 8 = B1; statements by L-D, proofs owner L-H): the typed HAR, the circuit-soundness half of
-- `nodeT20`. Roll 7's `harith20` (`LvmFinHB`) / `harith_core` (`LvmQAsmHarMain`) for the B program: wherever the B
-- program's Q_arith (`qaB = phases47 >>= qarithB`) holds and asserts on a pair's memory, V_S's typed decision on the
-- child's stream accepts and folds to the statement's incoming accumulator. `harithT20`'s statement is L-D's (the form
-- `LvmNodeSoundT.nodeSoundT` consumes); L-H's proofs, with the parts in `LvmQTypedHar{T,G,C,Z,R,A,M}`.
import LvmNodeSoundT
import LvmQAsmHarP47
import LvmQTypedHarC
import LvmQAsmArith2WhirP
import LvmAccNodePub
import LvmQLinkArithKS
import LvmQTypedHarB
import LvmQAsmHarTails
import LvmQTypedHarZ
import LvmQTypedHarR

-- ===== merged from `LvmQLinkArithP8` (GOLF module merge: `LvmQLinkArithP8.lean` is now a stub importing `LvmQTypedHarS`) =====
section

/-!
# QA1 links: the `P8` instance (smoke check of `ksLink_sound`)

The `KS` link's template check (`SLok`) is discharged by evaluation at `P8`'s sizes (B1: `ksLog = 14`,
`recRowsLog = 14`, KS14's block E, `spongeBlocks P8` from `sizes_P8`). S2 has no `CH` link.
-/

set_option autoImplicit false

namespace Lvm.Q1

open Lvm Lvm.Loop Lvm.Loop.Build

theorem spongeBlocks_P8 : spongeBlocks P8 = 2262 := by
  rw [spongeBlocks, sizes_P8.2.2.2.2.2.2.2.1]

/-! ## The template check does not read addresses -/

/-- An operand with its address forgotten. -/
def Src.shape : Src → Src
  | .ext _ => .ext default
  | s => s

/-- An instruction with its addresses forgotten. -/
def Ins.shape (i : Ins) : Ins := ⟨i.op, i.ty, i.args.map Src.shape⟩

theorem getD_map_shape (ins : List Ins) (k : Nat) :
    (ins.map Ins.shape).getD k default = (ins.getD k default).shape := by
  simp only [List.getD_eq_getElem?_getD, List.getElem?_map]
  cases ins[k]? <;> rfl

theorem locOk_shape (ins : List Ins) (k : Nat) (i : Ins) :
    i.shape.locOk (ins.map Ins.shape) k = i.locOk ins k := by
  simp only [Ins.locOk, Ins.shape, List.all_map, getD_map_shape, List.length_map]
  congr 1
  congr 1
  funext s
  cases s <;> rfl

/-- **`SLok` of a template is that of its shape.** -/
theorem SLok_shape (ins : List Ins) : SLok (ins.map Ins.shape) = SLok ins := by
  simp only [SLok, List.length_map, getD_map_shape, locOk_shape]

/-! ## Combinators commute with forgetting addresses -/

/-- Two operand lists with the same shape. -/
def SameShape (xs ys : List Src) : Prop := xs.map Src.shape = ys.map Src.shape

theorem shape_loc (k : Nat) : (Src.loc k).shape = .loc k := rfl

theorem map_cellSrc_shape (l : List Cell) : (l.map cellSrc).map Src.shape = List.replicate l.length (.ext default) := by
  induction l with
  | nil => rfl
  | cons c l ih => simp only [List.map_cons, List.length_cons, List.replicate_succ, ih]; rfl

theorem shape_mulI (a b d : Src) : (mulI a b d).shape = mulI a.shape b.shape d.shape := rfl
theorem shape_linI (k k' : FK) (a b : Src) : (linI k k' a b).shape = linI k k' a.shape b.shape := rfl
theorem shape_addI (a b : Src) : (addI a b).shape = addI a.shape b.shape := rfl
theorem shape_shape (s : Src) : s.shape.shape = s.shape := by cases s <;> rfl

theorem dotIns_shape : ∀ (n : Nat) (s : Src) (ps : List (Src × Src)),
    (dotIns n s ps).map Ins.shape = (dotIns n s.shape (ps.map fun ab => (ab.1.shape, ab.2.shape))).map Ins.shape
  | _, _, [] => rfl
  | n, s, (a, b) :: ps => by
    simp only [dotIns, List.map_cons, shape_mulI, shape_shape, dotIns_shape (n + 1) (.loc n) ps]
    rfl

theorem mulChainIns_shape (z : Src) : ∀ (n : Nat) (s : Src) (cs : List Src),
    (mulChainIns z n s cs).map Ins.shape = (mulChainIns z n s.shape (cs.map Src.shape)).map Ins.shape
  | _, _, [] => rfl
  | n, s, c :: cs => by
    simp only [mulChainIns, List.map_cons, shape_mulI, shape_shape, mulChainIns_shape z (n + 1) (.loc n) cs]
    rfl

theorem shiftRecE_shape (n : Nat) : ∀ (xs ys : List Src) (E0 : Src),
    (shiftRecE n (xs.map Src.shape) (ys.map Src.shape) E0.shape).shape = (shiftRecE n xs ys E0).shape
  | _ :: _, _ :: _, _ => by simp [shiftRecE]
  | [], _, _ => by simp [shiftRecE, shape_shape]
  | _ :: _, [], _ => by simp [shiftRecE, shape_shape]

theorem shiftRecS_shape (n : Nat) : ∀ (xs ys : List Src) (S0 : Src),
    (shiftRecS n (xs.map Src.shape) (ys.map Src.shape) S0.shape).shape = (shiftRecS n xs ys S0).shape
  | _ :: _, _ :: _, _ => by simp [shiftRecS]
  | [], _, _ => by simp [shiftRecS, shape_shape]
  | _ :: _, [], _ => by simp [shiftRecS, shape_shape]

theorem shiftRecIns_shape (z : Src) (n : Nat) : ∀ (xs ys : List Src) (E0 S0 : Src),
    (shiftRecIns z n xs ys E0 S0).map Ins.shape =
      (shiftRecIns z.shape n (xs.map Src.shape) (ys.map Src.shape) E0.shape S0.shape).map Ins.shape
  | x0 :: x, y0 :: y, E0, S0 => by
    simp only [List.map_cons, shiftRecIns, List.map_append, shiftRecIns_shape z n x y E0 S0, List.length_map]
    congr 1
    simp only [shiftLevel, List.map_cons, List.map_nil, shape_mulI, shape_linI, shape_shape, shape_loc,
      shiftRecE_shape, shiftRecS_shape]
  | [], _, _, _ => rfl
  | _ :: _, [], _, _ => rfl

theorem preRecOut_shape (n : Nat) : ∀ (xs ys : List Src) (base : Src × Src × Src),
    preRecOut n (xs.map Src.shape) (ys.map Src.shape) (base.1.shape, base.2.1.shape, base.2.2.shape) =
      ((preRecOut n xs ys base).1.shape, (preRecOut n xs ys base).2.1.shape, (preRecOut n xs ys base).2.2.shape)
  | _ :: _, _ :: _, _ => by simp [preRecOut, shape_loc]
  | [], _, _ => rfl
  | _ :: _, [], _ => rfl

theorem preRecIns_shape (z : Src) (n : Nat) : ∀ (xs ys : List Src) (H : Nat) (base : Src × Src × Src),
    (preRecIns z n xs ys H base).map Ins.shape =
      (preRecIns z.shape n (xs.map Src.shape) (ys.map Src.shape) H
        (base.1.shape, base.2.1.shape, base.2.2.shape)).map Ins.shape
  | x0 :: x, y0 :: y, H, base => by
    simp only [List.map_cons, preRecIns, List.map_append, preRecIns_shape z n x y (H / 2) base, List.length_map,
      preRecOut_shape]
    congr 1
    simp only [preLevel, List.map_cons, List.map_nil, shape_mulI, shape_linI, shape_addI, shape_shape, shape_loc]
    split <;> simp [shape_mulI, shape_shape, shape_loc]
  | [], _, _, _ => rfl
  | _ :: _, [], _, _ => rfl

theorem eqLevelIns_shape (z : Src) (n : Nat) (olds : List Src) (r : Src) :
    (eqLevelIns z n olds r).map Ins.shape = (eqLevelIns z.shape n (olds.map Src.shape) r.shape).map Ins.shape := by
  simp only [eqLevelIns, List.map_cons, shape_linI, shape_shape, List.length_map, List.map_map]
  congr 1
  apply List.map_congr_left
  intro i hi
  have hi' := List.mem_range.mp hi
  simp only [Function.comp_def]
  split
  · rename_i h; simp only [shape_mulI, shape_shape, shape_loc]
    rw [List.getD_eq_getElem _ _ h, List.getD_eq_getElem _ _ (by simpa using h), List.getElem_map, shape_shape]
  · rename_i h; simp only [shape_mulI, shape_shape]
    rw [List.getD_eq_getElem _ _ (by omega), List.getD_eq_getElem _ _ (by simp; omega), List.getElem_map, shape_shape]

theorem eqLevelOut_shape (n m : Nat) : (eqLevelOut n m).map Src.shape = eqLevelOut n m := by
  unfold eqLevelOut; rw [List.map_map]; rfl

theorem eqTabGo_shape (z : Src) : ∀ (rs : List Src) (n : Nat) (olds : List Src),
    (eqTabGo z n olds rs).map Ins.shape = (eqTabGo z.shape n (olds.map Src.shape) (rs.map Src.shape)).map Ins.shape
  | [], _, _ => rfl
  | r :: rs, n, olds => by
    simp only [eqTabGo, List.map_cons, List.map_append, List.length_map]
    rw [eqLevelIns_shape, eqTabGo_shape z rs, eqLevelOut_shape]

theorem shape_cellSrc (c : Cell) : (cellSrc c).shape = .ext default := rfl

theorem shape_ins_mk (op : Op) (ty : Ty) (args : List Src) :
    (⟨op, ty, args⟩ : Ins).shape = ⟨op, ty, args.map Src.shape⟩ := rfl

theorem shape_getD_mapCellSrc {α : Type} (f : α → Cell) (l : List α) (i : Nat) :
    ((l.map fun x => cellSrc (f x)).getD i default).shape = .ext default := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_map]
  cases l[i]? <;> rfl

theorem eqTabOut_len : ∀ (n : Nat) (olds rs rs' : List Src), rs.length = rs'.length →
    eqTabOut n olds rs = eqTabOut n olds rs'
  | _, _, [], [], _ => rfl
  | n, olds, _ :: rs, _ :: rs', h => by
    simp only [eqTabOut]; exact eqTabOut_len _ _ rs rs' (by simpa using h)
  | _, _, [], _ :: _, h => by simp at h
  | _, _, _ :: _, [], h => by simp at h

theorem eMus_any (c₀ c₁ : Cell) : eMus [c₀, c₁] = eMus [default, default] := by
  funext m; unfold eMus
  rw [eqTabOut_len 66 [.loc 65] ([c₀, c₁].map cellSrc) ([default, default].map cellSrc) (by simp)]

theorem shape_getD_cellSrc (l : List Cell) (i : Nat) : ((l.map cellSrc).getD i default).shape = .ext default := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_map]
  cases l[i]? <;> rfl

theorem loadsAt_shape (q s N : Nat) : (loadsAt q s N).map Ins.shape = (loadsAt 0 0 N).map Ins.shape := by
  simp only [loadsAt, List.map_map]; rfl

/-- A placeholder loop output (only its shape matters to `SLok`). -/
def defOut : LoopOut := ⟨⟨0, 0⟩, [], []⟩

-- (lvm2 GOLF: `okE_P8` and `ksLink_sound_P8` moved to `LvmQLinkArithP8S`, outside `Solution`'s import closure: only
-- `LvmFinDec` uses them, and `okE_P8`'s decision cost ≈ 14 s of the certificate's build.)

end Lvm.Q1
end
-- ===== end of `LvmQLinkArithP8` =====

-- ===== merged from `LvmQAsmHarLink20` (GOLF module merge: `LvmQAsmHarLink20.lean` is now a stub importing `LvmQTypedHarS`) =====
section
-- New for lvm (HAR; WP-16b: the checks through WP-16a2's one-pass `SLokF`, moved here from `LvmFinDec`):
-- QA1's link soundness at `P20` (`logN = 20`, `ksLog = 14`, `recRowsLog = 14`: KS14, lvm2 CR-K):
-- the template checks (`SLok`) decided as for `P8` (QA1's `LvmQLinkArithP8`), the KS template
-- (`okE`) after the re-freeze.

set_option autoImplicit false

namespace Lvm.Fin

open Lvm Lvm.Loop Lvm.Loop.Build Lvm.Q1

/-! ## `SLok` in one pass (WP-16a2, moved here from `LvmFinDec` for the `P20` glue checks)

`SLok` looks every operand's row up from the template's head (quadratic: 16 s of kernel at the
600-row block E); `SLokF` walks the template once and looks the assertions up in a short list. -/

/-- The positions of a template's assertions. -/
def assertPos (ins : List Ins) : List ℕ :=
  (ins.zipIdx.filter fun x => !(x.1.op != .assert0)).map Prod.snd

/-- **`SLok` in one pass**: the reads of earlier results look the assertions up in `assertPos`. -/
def SLokF (ins : List Ins) : Bool :=
  ins.zipIdx.all fun x => (match x.1.op with
    | .muladd | .lin .. | .loadE | .assert0 | .e2 .. => true
    | _ => false) &&
    x.1.args.all fun s => match s with
      | .loc k' => decide (k' < x.2) && !((assertPos ins).contains k')
      | .prev k' => decide (k' < ins.length) && !((assertPos ins).contains k')
      | .ext _ => true

/-- A row is no assertion iff its position is not in `assertPos`. -/
theorem bne_assert {ins : List Ins} {k : ℕ} (hk : k < ins.length) :
    ((ins.getD k default).op != .assert0) = !((assertPos ins).contains k) := by
  rw [List.getD_eq_getElem _ _ hk]
  cases hc : (assertPos ins).contains k
  · have hn : ¬ k ∈ assertPos ins := by simpa using hc
    simp only [Bool.not_false]
    by_contra hb
    apply hn
    simp only [assertPos, List.mem_map, List.mem_filter]
    exact ⟨(ins[k], k), ⟨List.mem_zipIdx_iff_getElem?.mpr (by simp [hk]), by simpa using hb⟩, rfl⟩
  · have hm : k ∈ assertPos ins := by simpa using hc
    simp only [assertPos, List.mem_map, List.mem_filter] at hm
    obtain ⟨⟨i, k'⟩, ⟨hz, hb⟩, rfl⟩ := hm
    have := List.mem_zipIdx_iff_getElem?.mp hz
    simp only [List.getElem?_eq_getElem hk, Option.some.injEq] at this
    rw [← this] at hb
    simpa using hb

/-- **`SLokF` decides `SLok`** (one direction suffices). -/
theorem SLok_of_F {ins : List Ins} (h : SLokF ins = true) : SLok ins = true := by
  unfold SLok
  rw [List.all_eq_true]
  intro k hk
  rw [List.mem_range] at hk
  unfold SLokF at h
  rw [List.all_eq_true] at h
  have hx := h (ins[k], k) (List.mem_zipIdx_iff_getElem?.mpr (by simp [hk]))
  rw [List.getD_eq_getElem _ _ hk]
  unfold Ins.locOk
  simp only [Bool.and_eq_true, List.all_eq_true] at hx ⊢
  refine ⟨hx.1, fun s hs => ?_⟩
  have hs' := hx.2 s hs
  cases s with
  | loc k' =>
    simp only [Bool.and_eq_true, decide_eq_true_eq] at hs' ⊢
    refine ⟨hs'.1, ?_⟩
    rw [bne_assert (by omega)]
    exact hs'.2
  | prev k' =>
    simp only [Bool.and_eq_true, decide_eq_true_eq] at hs' ⊢
    refine ⟨hs'.1, ?_⟩
    rw [bne_assert hs'.1]
    exact hs'.2
  | ext a => rfl

end Lvm.Fin

end
-- ===== end of `LvmQAsmHarLink20` =====

-- ===== merged from `LvmQTypedHarA` (GOLF module merge: `LvmQTypedHarA.lean` is now a stub importing `LvmQTypedHarS`) =====
section
-- New for lvm2 (roll 8 = B1, L-H): the typed HAR's A23 phase at `Φ_Q`: `qaccT` replays V_S's `dAccT` (AC-Q's
-- `qacc_sound` with the typed instance: `dk = 2`, 43 variables, `b = κ ++ r_x ++ r_y`, no `PUB` table).

/-!
# A23 at `Φ_Q` in the circuit

**`qaccT_replays`**: wherever `qaccT (aP P / 8) pb r_x r_y v`'s rows hold and assert (gate on: `PUB` lane 0 is
`1`), `dAccT` on the child's `PUB` (`pubOf vk c_L Σ'`), the point `r_x ++ r_y` and the matrix values `v` from any
state at `aP P` with `ok` keeps `ok` (`h(0) = acc_in'.y`, `h(1) = Σ_o eq(κ, o)·v_o`, the zero scalar), ends at
`mbP P`, and folds to the current proof's `acc_in` (`accC M pb`, its `PUB` cells).

* **`qaccT_facts`** (AC-Q's `qacc_facts` for `qaccT`): from lane `L`, the gadget's rows and assertions give the
  five equations on the stream view `feAt Σ` (`h₀`, `Σh`, the line, `h(t)`, the zero scalar).
* **`dAccT_run`**: `dAccT` from any state at position `Q`, as a function of `Q` (`accFold_run`'s form).
-/

set_option autoImplicit false

namespace Lvm.Har

open Lvm Lvm.Loop Lvm.Loop.Build Lvm.QTyped Lvm.Q1 DM

section helpers
open Lvm.QAcc Lvm.QSig

attribute [local irreducible] Lvm.QAcc.horner Lvm.QAcc.macChain Lvm.QAcc.linePts in
set_option maxHeartbeats 1000000 in
/-- **`qaccT`'s facts** (gate on, the child's stream bound): the five equations of A23 on `feAt Σ`. -/
theorem qaccT_facts {c : Ctx} {M : Mem} {sig : ByteArray} {T : Nat} {L pb : Nat} {p : Ptr}
    (hS : Streamed M sig T) (hT : L + 166 < T) (hH : 11 + pubLanes ≤ T) (hg : M.k pb = 1)
    (rx ry v : List Cell) (hrx : rx.length = 20) (hry : ry.length = 21) (hv : v.length = 4)
    (h : Lvm.QSig.Ok c M (qaccT L pb rx ry v) p) :
    let K := (List.range 2).map fun i => feAt sig (8 * (L + 5 + 9 * i))
    let H := (List.range 44).map fun j => feAt sig (8 * (L + 18 + 5 + 3 * j))
    let t := feAt sig (8 * (L + 18 + 3 * 44 + 5))
    H.headD 0 = feAt sig (8 * accLane 43) ∧ sumE H = Lvm.dot (eqKernel K) (vs M v) ∧
      accLine ((List.range 43).map fun i => feAt sig (8 * accLane i)) (K ++ vs M (rx ++ ry)) t =
        (accC M pb).pt ∧
      polyEval H t = (accC M pb).y ∧ feAt sig (8 * (L + 18 + 3 * 44 + 9 + 5)) = 0 := by
  have hD : tVars = 43 := rfl
  have hA : accVars = 43 := rfl
  have hPL : pubLanes = 747 := rfl
  have hgv : (kc pb).val M = 1 := kc_val_one hg
  unfold qaccT at h
  obtain ⟨zo, p1, evo1, epo1, o1, h⟩ := okBindE h
  obtain ⟨hz1, hz2, hz0, hone⟩ := consts_spec o1.1
  have hzv : (consts pb p).1.1.val M = 0 := by rw [hz1]; exact hz0
  have hov : M.e (consts pb p).1.2.n = 1 := by rw [hz2]; exact hone
  have hov' : (consts pb p).1.2.val M = 1 := by rw [hz2]; exact hone
  rw [evo1] at hzv hov hov'
  -- κ
  obtain ⟨kb, p2, evo2, epo2, o2, h⟩ := okBindE h
  have hk := ldEsB_spec hS (qs := (List.range 2).map fun i => L + 5 + 9 * i)
    (by intro q hq; simp only [List.mem_map, List.mem_range] at hq; obtain ⟨i, hi, rfl⟩ := hq; (clear * - hT hi; omega)) o2.1
  rw [evo2] at hk
  -- y'
  obtain ⟨y, p5, evo5, epo5, o5, h⟩ := okBindE h
  have hy := qyown_spec (by (clear * -; omega) : 1 ≤ 2) (by rw [hv]; decide) hzv hov o5.1
  rw [evo5] at hy
  -- h', acc_in'
  obtain ⟨hb, p6, evo6, epo6, o6, h⟩ := okBindE h
  have hh := ldEsB_spec hS (qs := (List.range (tVars + 1)).map fun j => L + 18 + 5 + 3 * j)
    (by intro q hq; simp only [List.mem_map, List.mem_range] at hq; obtain ⟨i, hi, rfl⟩ := hq; (clear * - hT hD hi; omega)) o6.1
  rw [evo6] at hh
  obtain ⟨ab, p7, evo7, epo7, o7, h⟩ := okBindE h
  have ha := ldEsB_spec hS (qs := (List.range (tVars + 1)).map accLane)
    (by intro q hq; simp only [List.mem_map, List.mem_range] at hq; obtain ⟨i, hi, rfl⟩ := hq
        simp only [accLane]; (clear * - hH hD hPL hi; omega)) o7.1
  rw [evo7] at ha
  obtain ⟨_vo8, p8, evo8, epo8, o8, h⟩ := okBindE h
  have e8 := assertEqE_spec o8 hgv
  obtain ⟨sh, p9, evo9, epo9, o9, h⟩ := okBindE h
  have hsh := macChain_spec _ _ _ o9.1
  rw [evo9] at hsh
  obtain ⟨_vo10, p10, evo10, epo10, o10, h⟩ := okBindE h
  have e10 := assertEqE_spec o10 hgv
  -- t', h'(t'), the line
  obtain ⟨t, p11, evo11, epo11, o11, h⟩ := okBindE h
  have ht := ldE_feAt hS (q := L + 18 + 3 * (tVars + 1) + 5) (by (clear * - hT hD; omega)) o11.1
  rw [evo11] at ht
  obtain ⟨hv', p12, evo12, epo12, o12, h⟩ := okBindE h
  have hhv := horner_spec (c := c) (M := M) t zo.1 hzv ((List.range (tVars + 1)).map fun j => ec (hb + j)) p11 o12.1
  rw [evo12] at hhv
  obtain ⟨pts, p13, evo13, epo13, o13, h⟩ := okBindE h
  have hpt := linePts_spec (c := c) (M := M) t ((List.range tVars).map fun i =>
    (ec (ab + i), (((List.range 2).map (fun j => ec (kb + j)) ++ rx ++ ry).getD i (ec 0)))) p12 o13.1
  rw [evo13] at hpt
  -- the current acc_in
  obtain ⟨pc, p14, evo14, epo14, o14, h⟩ := okBindE h
  have hpc := ldEsB_val (c := c) (M := M) (qs := (List.range (tVars + 1)).map fun j => pb + 615 + 3 * j) (p := p13) o14.1
  rw [evo14] at hpc
  obtain ⟨_vo15, p15, evo15, epo15, o15, h⟩ := okBindE h
  have e15 := assertEqs_spec (c := c) (M := M) hgv ((List.range tVars).map fun i => (pts.getD i default, ec (pc + i))) p14 o15
  obtain ⟨_vo16, p16, evo16, epo16, o16, h⟩ := okBindE h
  have e16 := assertEqE_spec o16 hgv
  obtain ⟨zz, _qo17, evo17, epo17, o17, h⟩ := okBindE h
  have hz := ldE_feAt hS (q := L + 18 + 3 * (tVars + 1) + 9 + 5) (by omega) o17.1
  rw [evo17] at hz
  have e17 := assert0_spec h.2
  rw [hgv, one_mul] at e17
  have h44 : tVars + 1 = 44 := rfl
  rw [h44] at hh ha hpc ht hz hhv
  rw [hD] at e8 hpt e15 e16
  have hkv : ∀ i < 2, M.e (kb + i) = feAt sig (8 * (L + 5 + 9 * i)) := by
    intro i hi; rw [hk i (by simpa using hi)]; simp [List.getD_eq_getElem?_getD, List.getElem?_range hi]
  have hhv' : ∀ j < 44, M.e (hb + j) = feAt sig (8 * (L + 18 + 5 + 3 * j)) := by
    intro j hj; rw [hh j (by simpa using hj)]; simp [List.getD_eq_getElem?_getD, List.getElem?_range hj]
  have hav : ∀ j < 44, M.e (ab + j) = feAt sig (8 * accLane j) := by
    intro j hj; rw [ha j (by simpa using hj)]; simp [List.getD_eq_getElem?_getD, List.getElem?_range hj]
  have hHl : (List.range 44).map (fun j => feAt sig (8 * (L + 18 + 5 + 3 * j))) =
      ((List.range 44).map fun j => ec (hb + j)).map (Cell.val M) := by
    rw [List.map_map]; apply List.map_congr_left; intro j hj; rw [List.mem_range] at hj
    simp [hhv' j hj]
  have hKv : (List.range 2).map (fun i => M.e (kb + i)) = (List.range 2).map fun i => feAt sig (8 * (L + 5 + 9 * i)) := by
    apply List.map_congr_left; intro i hi; rw [List.mem_range] at hi; exact hkv i hi
  dsimp only
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · rw [List.range_succ_eq_map, List.map_cons, List.headD_cons]
    have := hhv' 0 (by (clear * -; omega))
    rw [Nat.add_zero] at this
    rw [← this, ← hav 43 (by (clear * -; omega))]; exact e8
  · have hsum : sh.val M = ((List.range 44).map fun j => feAt sig (8 * (L + 18 + 5 + 3 * j))).sum := by
      rw [hsh, hzv, zero_add, List.map_map, hHl, List.map_map]
      congr 1; apply List.map_congr_left; intro j _
      simp [hov']
    rw [sumE_eq, ← hsum, e10, hy, dot_eqKernel _ _ (by simp [vs, hv]), hKv]
    simp only [vs, List.length_map]
    refine Finset.sum_congr rfl fun k hk => ?_
    rw [Finset.mem_range] at hk
    rw [List.getD_eq_getElem _ _ hk, List.getD_eq_getElem _ _ (by simpa using hk), List.getElem_map]
  · have hbc : ((List.range 2).map (fun j => ec (kb + j)) ++ rx ++ ry).map (Cell.val M) =
        (List.range 2).map (fun i => feAt sig (8 * (L + 5 + 9 * i))) ++ vs M (rx ++ ry) := by
      rw [← hKv, List.append_assoc, List.map_append, List.map_map]; rfl
    have hbl : ((List.range 2).map (fun j => ec (kb + j)) ++ rx ++ ry).length = 43 := by
      simp [hrx, hry]
    rw [← hbc, ← ht]
    apply List.ext_getElem
    · simp [accLine, accC, List.length_zipWith, hrx, hry, hA]
    intro i h1 h2
    have hi : i < 43 := by simpa [accC, hA] using h2
    have hpi := hpt.2 i (by simpa using hi)
    rw [List.getD_eq_getElem ((List.range 43).map fun i =>
        (ec (ab + i), ((List.range 2).map (fun j => ec (kb + j)) ++ rx ++ ry).getD i (ec 0))) _ (by simpa using hi),
      List.getElem_map, List.getElem_range,
      List.getD_eq_getElem ((List.range 2).map (fun j => ec (kb + j)) ++ rx ++ ry) _ (by rw [hbl]; exact hi)] at hpi
    have hq := e15 ((pts.getD i default, ec (pc + i))) (List.mem_map.mpr ⟨i, List.mem_range.mpr hi, rfl⟩)
    have hpci : M.e (pc + i) = ⟨M.k (pb + 615 + 3 * i), M.k (pb + 615 + 3 * i + 1),
        M.k (pb + 615 + 3 * i + 2)⟩ := by
      rw [hpc i (by simp; (clear * - hi; omega))]
      simp [List.getD_eq_getElem?_getD, List.getElem?_range (by (clear * - hi; omega) : i < 44)]
    simp only [Cell.val_E] at hq hpi
    rw [hq, hpci, hav i (by (clear * - hi; omega))] at hpi
    simp only [accLine, List.getElem_zipWith, List.getElem_map, List.getElem_range, accC]
    exact hpi.symm
  · rw [hHl, ← ht, ← hhv, e16, Cell.val_E, hpc 43 (by simp)]
    simp [accC, List.getD_eq_getElem?_getD, hA]
  · exact hz.symm.trans e17

/-- **`dAccT` from position `Q = ent + msg`**: `κ`, `h`, `t`, the zero scalar at fixed offsets. -/
theorem dAccT_run (pub : Pub) (rxy w : List FE) (sig : ByteArray) (s : RS) :
    TypedV.dAccT pub rxy w sig s =
      let K := (List.range 2).map fun i => feAt sig (s.ent + s.msg + 40 + 72 * i)
      let H := (List.range 44).map fun j => feAt sig (s.ent + s.msg + 184 + 24 * j)
      let t := feAt sig (s.ent + s.msg + 1240)
      (⟨accLine pub.accIn.pt (K ++ rxy) t, polyEval H t⟩,
        ⟨s.ent + s.msg + 1272, 24, (feAt sig (s.ent + s.msg + 1312) == 0) &&
          ((sumE H == Lvm.dot (eqKernel K) w) && ((H.headD 0 == pub.accIn.y) && s.ok))⟩) := by
  unfold TypedV.dAccT
  rw [Lvm.Q1.bind_run, Lvm.Q1.samples_run sig 2 _ (by norm_num), Lvm.Q1.bind_run, Lvm.Q1.readEs_run,
    Lvm.Q1.bind_run, Lvm.Q1.sampleE_run, Lvm.Q1.bind_run, Lvm.Q1.readE_run, Lvm.Q1.bind_run, require_run_lk,
    Lvm.Q1.bind_run, require_run_lk, Lvm.Q1.bind_run, require_run_lk, Lvm.Q1.pure_run]
  dsimp only [scalarsAt]
  rfl

/-- The child's `acc_in` (`pubOf`'s header) at the stream lanes `accLane`. -/
theorem pubOf_accIn (vk cL : Vector UInt8 32) (sig : ByteArray) :
    (pubOf vk cL sig).accIn.y = feAt sig (8 * accLane 43) ∧
      (pubOf vk cL sig).accIn.pt = (List.range 43).map fun i => feAt sig (8 * accLane i) := by
  have hacc : ∀ i, headerAt (offAcc + eBytes * i) = 8 * accLane i := by
    intro i; simp only [headerAt, offAcc, eBytes, sigBytes, accLane]; omega
  refine ⟨?_, ?_⟩
  · show feAt sig (headerAt (offAcc + eBytes * 43)) = _; rw [hacc]
  · show (List.range 43).map (fun i => feAt sig (headerAt (offAcc + eBytes * i))) = _
    simp only [hacc]

end helpers

section
variable {c : Ctx} {M : Mem} {sig : ByteArray} {T : Nat}

/-- **A23 at `Φ_Q` replayed** (soundness direction). -/
theorem qaccT_replays (vk cL : Vector UInt8 32) (hS : Streamed M sig T) (hH : 11 + pubLanes ≤ T) {pb : Nat}
    (hg : M.k pb = 1) {P : Nat} (hP : P % 8 = 0) (hT : mbP P + 40 ≤ 8 * T) (rx ry v : List Cell)
    (hrx : rx.length = 20) (hry : ry.length = 21) (hv : v.length = 4) (hE : ∀ x ∈ rx ++ ry ++ v, x.ty = .E)
    (ptr : Ptr) :
    Replays c M sig (TypedV.dAccT (pubOf vk cL sig) (vs M (rx ++ ry)) (vs M v)) (qaccT (aP P / 8) pb rx ry v) ptr
      (aP P) (mbP P) fun a _ => a = Lvm.QAcc.accC M pb := by
  intro h s hs hok
  have hD : tVars = 43 := rfl
  have h8 : 8 * (aP P / 8) = aP P := by
    have : aP P % 8 = 0 := by simp only [aP, rVP, rRP, wVP, wRP, wGP, zAbcP, zRP]; (clear * - hP; omega)
    (clear * - this; omega)
  have hmb : mbP P = aP P + 1296 := by unfold mbP; rw [hD]
  obtain ⟨F1, F2, F3, F4, F5⟩ := qaccT_facts hS (by (clear * - hT h8 hmb; omega)) hH hg rx ry v hrx hry hv h
  obtain ⟨hy, hpt⟩ := pubOf_accIn vk cL sig
  have hQ : s.ent + s.msg = 8 * (aP P / 8) := by rw [h8]; exact hs
  rw [dAccT_run]
  dsimp only
  rw [hQ]
  -- the reader's positions as the gadget's lanes
  have eK : (List.range 2).map (fun i => feAt sig (8 * (aP P / 8) + 40 + 72 * i)) =
      (List.range 2).map fun i => feAt sig (8 * (aP P / 8 + 5 + 9 * i)) :=
    List.map_congr_left fun i _ => congrArg _ (by (clear * -; omega))
  have eH : (List.range 44).map (fun j => feAt sig (8 * (aP P / 8) + 184 + 24 * j)) =
      (List.range 44).map fun j => feAt sig (8 * (aP P / 8 + 18 + 5 + 3 * j)) :=
    List.map_congr_left fun j _ => congrArg _ (by (clear * -; omega))
  have et : feAt sig (8 * (aP P / 8) + 1240) = feAt sig (8 * (aP P / 8 + 18 + 3 * 44 + 5)) :=
    congrArg _ (by (clear * -; omega))
  have ez : feAt sig (8 * (aP P / 8) + 1312) = feAt sig (8 * (aP P / 8 + 18 + 3 * 44 + 9 + 5)) :=
    congrArg _ (by (clear * -; omega))
  rw [eK, eH, et, ez]
  refine ⟨?_, ?_, ?_⟩
  · rw [F5, F1, hy, F2]
    simp [hok]
  · show 8 * (aP P / 8) + 1272 + 24 = mbP P
    (clear * - h8 hmb; omega)
  · rw [hpt, F3, F4]

end

end Lvm.Har
end
-- ===== end of `LvmQTypedHarA` =====

-- ===== merged from `LvmQTypedHarM` (GOLF module merge: `LvmQTypedHarM.lean` is now a stub importing `LvmQTypedHarS`) =====
section
-- New for lvm2 (roll 8 = B1, L-H): the typed HAR's mini-bus phase: `miniG` replays V_S's `dMiniT` (roll 7's
-- `busG_replays` at the mini-bus's depth, `tabG_replays` on its tables, and the fixed address columns checked in the
-- circuit by `powColG`, V_S's `tableCheckR`).

/-!
# The mini-bus in the circuit

* **`miniG_replays`**: on tables `tabs` that are all sumcheck tables, whose shapes, rounds and depth are the
  circuit's (`TData.mbS`, `mbR`, `mbD`), and whose every fixed column `x ↦ g^{b + s x}` is listed in `TData.mbFix`,
  `miniG` replays `dMiniT p (M3.real p fun _ ↦ tabs) tabs pub` from `P` to the table phase's end; the evaluations
  are its table cells' values.
* **`mbT_sumcheck`, `mbT_fix`**: B1-Q's mini-bus tables (`mbT`: the seed arrays, then the read tables) meet the
  first and the last condition at any placements (`mbFixOf`).
-/

set_option autoImplicit false

namespace Lvm.Har

open Lvm Lvm.Loop Lvm.Loop.Build Lvm.QTyped Lvm.QAsm Lvm.Q1 Lvm.M3 DM

/-- Every fixed column of `tabs` is listed in `fx` with its power closed form `g^b·powEval r (g^s)`. -/
def FixListed (tabs : List Tab) (fx : List (Nat × Nat × Nat × Nat)) : Prop :=
  ∀ k (t : Tab), tabs[k]? = some t → ∀ i (f : Nat → FK) (e : List FE → FE), t.cols[i]? = some (.fix f e) →
    ∃ b s, (k, i, b, s) ∈ fx ∧ ∀ r, e r = FE.ofK (FK.x ^ b) * powEval r (FK.x ^ s)

/-- **B1-Q's mini-bus tables are all sumcheck tables** (a seed array has a seed, a read table a read). -/
theorem mbT_sumcheck (C : QCfg) (wordK : Nat → Nat) (fin : Nat → Bool × Nat) (cnt : Nat → Nat) :
    sumcheckTabs (mbT C wordK fin cnt) = mbT C wordK fin cnt := by
  unfold sumcheckTabs
  rw [List.filter_eq_self]
  intro t ht
  rcases List.mem_append.mp ht with h | h
  · obtain ⟨a, -, rfl⟩ := List.mem_map.mp h
    simp [InArr.tab]
  · simp only [capReads, List.mem_map] at h
    obtain ⟨x, -, rfl⟩ := h
    simp [readTab]

/-- Seed array `k` of `mbArrs` (`fin` only changes its finalize column). -/
theorem mbArrs_get (C : QCfg) (fin : Nat → Bool × Nat) (k : Nat) :
    (mbArrs C fin)[k]? = ((mbBlocks C.p)[k]?).map fun q =>
      ⟨.K, mbBlk, (lay C).sb + 17 * q.2 + q.1, 17, [(false, Lvm.sCol C.p q.1 + q.2)], fin k, none⟩ := by
  rw [mbArrs, List.getElem?_map, List.getElem?_zipIdx, Option.map_map, Nat.zero_add]
  rfl

/-- **B1-Q's mini-bus tables' fixed columns are `mbFixOf`'s** (a seed array's address column; a read table has
none). -/
theorem mbT_fix (C : QCfg) (wordK : Nat → Nat) (fin : Nat → Bool × Nat) (cnt : Nat → Nat) :
    FixListed (mbT C wordK fin cnt) (mbFixOf C) := by
  intro k t hk i f e hc
  rw [mbT, List.getElem?_append] at hk
  split at hk
  · rw [List.getElem?_map, mbArrs_get] at hk
    cases hb : (mbBlocks C.p)[k]? with
    | none => simp [hb] at hk
    | some q =>
      simp only [hb, Option.map_some, Option.some.injEq] at hk
      subst hk
      simp only [InArr.tab, InArr.vcols, List.map_cons, List.map_nil, List.cons_append,
        List.nil_append] at hc
      match i, hc with
      | 2, hc =>
        simp only [List.getElem?_cons_succ, List.getElem?_cons_zero, Option.some.injEq,
          ColSrc.fix.injEq] at hc
        obtain ⟨-, rfl⟩ := hc
        refine ⟨(lay C).sb + 17 * q.2 + q.1, 17, ?_, fun r => rfl⟩
        rw [mbFixOf, List.mem_map]
        refine ⟨(⟨.K, mbBlk, (lay C).sb + 17 * q.2 + q.1, 17, [(false, Lvm.sCol C.p q.1 + q.2)], (false, 0),
          none⟩, k), ?_, rfl⟩
        rw [List.mem_zipIdx_iff_getElem?, mbArrs_get, hb]
        rfl
      | 0, hc => simp at hc
      | 1, hc => simp at hc
      | _ + 3, hc => simp at hc
  · simp only [capReads, List.getElem?_map, Option.map_eq_some_iff] at hk
    obtain ⟨x, -, rfl⟩ := hk
    simp only [readTab] at hc
    match i, hc with
    | 0, hc => simp at hc
    | 1, hc => simp at hc
    | 2, hc => simp at hc
    | _ + 3, hc => simp at hc

/-- The GKR layers end on a lane boundary (as in `busG_sound`). -/
theorem layersEnd_mod8 : ∀ (sts : List Nat) (n Q : Nat), Q % 8 = 0 → layersEnd sts n Q % 8 = 0
  | [], _, _, hQ => hQ
  | st :: sts, n, Q, hQ => layersEnd_mod8 sts _ _ (stepEnd_mod st n Q hQ)

/-- **The circuit's fixed-column checks give `tableCheckR`**: where `miniG`'s `powColG`/`assertEq` checks over `fx`
hold (gate on), every fixed column listed in `fx` evaluates at its table's point cells to its value cell. -/
theorem fixCheck_of {tabs : List Tab} {fx : List (Nat × Nat × Nat × Nat)} (hfix : FixListed tabs fx)
    {c : Ctx} {M : Mem} {z g : Cell} (hz : z.val M = 0) (hg : g.val M = 1)
    (tab : List (List Cell × List Cell)) {q : Ptr}
    (hok : Lvm.QSig.Ok c M (seqAll (fx.map fun f => do
      let e := tab.getD f.1 default
      let v ← powColG z f.2.2.1 f.2.2.2 e.1
      assertEq (e.2.getD f.2.1 z) v g)) q) :
    tableCheckR tabs (tab.map fun e => (vs M e.1, vs M e.2)) = true := by
  unfold tableCheckR
  rw [List.all_eq_true]
  rintro ⟨t, pt, ev⟩ hmem
  obtain ⟨k, hk⟩ := List.mem_iff_getElem?.mp hmem
  obtain ⟨hk1, hk2⟩ := List.getElem?_zip_eq_some.mp hk
  rw [List.getElem?_map, Option.map_eq_some_iff] at hk2
  obtain ⟨x, hx, hxe⟩ := hk2
  simp only [Prod.mk.injEq] at hxe
  obtain ⟨rfl, rfl⟩ := hxe
  rw [List.all_eq_true]
  rintro ⟨col, i⟩ hci
  rw [List.mem_zipIdx_iff_getElem?] at hci
  cases col with
  | com _ _ => rfl
  | fix f e =>
    obtain ⟨b, s, hmemfx, he⟩ := hfix k t hk1 i f e hci
    obtain ⟨q', hq'⟩ := Lvm.QSig.ok_seqAll _ q hok _ (List.mem_map_of_mem hmemfx)
    have htk : tab.getD k default = x := by rw [List.getD_eq_getElem?_getD, hx]; rfl
    obtain ⟨h1, h2, -⟩ := Lvm.QSig.ok_bind' hq'
    simp only [htk] at h1 h2
    have hv := powColG_spec hz b s x.1 q' h1.1
    have heq := Lvm.QAcc.assertEqE_spec h2 hg
    simp only [beq_iff_eq]
    rw [he]
    simp only [vs]
    rw [← hv, ← heq, List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, List.getElem?_map]
    cases x.2[i]? with
    | none => exact hz.symm
    | some y => rfl

section
variable {c : Ctx} {M : Mem} {sig : ByteArray} {T : Nat}

/-- **The mini-bus replayed** (soundness direction): wherever `miniG`'s rows hold and assert (gate on), `dMiniT` on
`tabs` from any state at `P` with `ok` keeps `ok`, ends at the table phase's end, and its evaluations are the table
cells' values. -/
theorem miniG_replays (hS : Streamed M sig T) {z o g : Cell} (hz : z.val M = 0) (ho : o.val M = 1)
    (hzE : z.ty = .E) (hoE : o.ty = .E) (hg : g.val M = 1) (hgK : g.ty = .K) (p : Params)
    (hl : p.leafdecReads = 1) (Td : TData) (tabs : List Tab) (hsc : sumcheckTabs tabs = tabs)
    (hS' : Td.mbS = tabs.map Tab.shape) (hR : Td.mbR = p.tableRounds) (hD : Td.mbD = p.busDepth)
    (hfix : FixListed tabs Td.mbFix) (pub : Pub) {P : Nat} (hP : P % 8 = 0)
    (hT : tabEnd Td.mbS Td.mbR (busEndD Td.mbD P) + 40 ≤ 8 * T) (ptr : Ptr) (hp : 1 ≤ ptr.e) :
    Replays c M sig (TypedV.dMiniT p (M3.real p fun _ => tabs) tabs pub) (miniG z o g Td P) ptr P
      (tabEnd Td.mbS Td.mbR (busEndD Td.mbD P)) fun v t => v = t.2.map fun e => (vs M e.1, vs M e.2) := by
  intro hok s hs hsok
  have hout : (miniG z o g Td P ptr).1 = ((busGD Td.mbD z o g P ptr).1,
      (tabG Td.mbS Td.mbR (busEndD Td.mbD P) z o g (busGD Td.mbD z o g P ptr).1
        (ptr.adv (busGD Td.mbD z o g P ptr).2)).1) := rfl
  obtain ⟨hB, hok1, -⟩ := Lvm.QSig.ok_bind' hok
  obtain ⟨hTb, hok2, -⟩ := Lvm.QSig.ok_bind' hok1
  obtain ⟨hFx, -⟩ := Lvm.QSig.ok_bind' hok2
  rw [hout]
  clear hout hok hok1 hok2
  have hS0 : Td.mbS = (sumcheckTabs tabs).map Tab.shape := by rw [hsc]; exact hS'
  rw [hS0, hR, hD] at hTb hFx hT ⊢
  rw [hD] at hB
  have e1 : busGD p.busDepth z o g P = busG p z o g P := rfl
  have e2 : busEndD p.busDepth P = busEnd p P := rfl
  rw [e1] at hB hTb hFx ⊢
  rw [e2] at hTb hFx hT ⊢
  have hT1 : busEnd p P + 40 ≤ 8 * T := by unfold tabEnd at hT; (clear * - hR hT e2; omega)
  have hP2 : busEnd p P % 8 = 0 := by
    have := layersEnd_mod8 (gkrSteps p.busDepth) 0 (busP1 P + 48) (by simp only [busP1, busBits]; (clear * - hP; omega))
    simp only [busEnd]; (clear * - this; omega)
  obtain ⟨b1, b2, b3⟩ := busG_replays (c := c) hS hz ho hg p hl hP hT1 ptr hB s hs hsok
  obtain ⟨hal, d, hpt⟩ := busG_fst p z o g P ptr
  generalize (busG p z o g P ptr).1 = bus at b3 hal hpt hTb hFx ⊢
  obtain ⟨hbv, h3⟩ := busR_eq b3
  rw [dMiniT_eq, bind_run']
  generalize busPh p sig s = BB at b1 b2 hbv ⊢
  obtain ⟨bv, s1⟩ := BB
  simp only at b1 b2 hbv
  subst hbv
  simp only [busV, bind_run', require_run']
  have hok2 : ((M3.real p fun _ => tabs).busFinal ⟨vs M bus.al, bus.be.val M, bus.cnt.val M, vs M bus.pt,
      vs M bus.vals, [0], pub⟩).ok = true := by
    show ((vs M bus.vals).length == 3 && [(0 : FE)] == [0]) = true
    rw [h3]; decide
  set bo := (M3.real p fun _ => tabs).busFinal ⟨vs M bus.al, bus.be.val M, bus.cnt.val M, vs M bus.pt,
      vs M bus.vals, [0], pub⟩
  have rt := tabG_replays (c := c) hS hz ho hg hzE hoE p (M3.real p fun _ => tabs) pub tabs rfl bus
    (countRoot := bus.cnt.val M) (leafdec := [0]) rfl rfl rfl rfl
    (by rw [hal]; simp [vs, busBits])
    (by rw [hal]; intro x hx; obtain ⟨i, -, rfl⟩ := List.mem_map.mp hx; rfl)
    (by rw [hpt]; intro x hx; obtain ⟨i, -, rfl⟩ := List.mem_map.mp hx; rfl)
    bo rfl hP2 hT (ptr.adv (busG p z o g P ptr).2)
  obtain ⟨t1, t2, t3⟩ := rt hTb ⟨s1.ent, s1.msg, bo.ok && s1.ok⟩ b2 (by rw [hok2, b1]; rfl)
  generalize tabPh p (M3.real p fun _ => tabs) pub bo (vs M bus.pt) sig ⟨s1.ent, s1.msg, bo.ok && s1.ok⟩ = TT
    at t1 t2 t3 ⊢
  obtain ⟨ev, s3⟩ := TT
  simp only [TabR] at t1 t2 t3
  subst t3
  generalize (tabG ((sumcheckTabs tabs).map Tab.shape) p.tableRounds (busEnd p P) z o g bus
    (ptr.adv (busG p z o g P ptr).2)).1 = tab at hFx ⊢
  rw [pure_run']
  refine ⟨?_, t2, rfl⟩
  rw [hsc, fixCheck_of hfix hz hg tab hFx, t1]
  rfl

end

end Lvm.Har
end
-- ===== end of `LvmQTypedHarM` =====

-- ===== merged from `LvmQTypedHarG` (GOLF module merge: `LvmQTypedHarG.lean` is now a stub importing `LvmQTypedHarS`) =====
section
-- New for lvm2 (roll 8 = B1, L-H): the typed core gadget `typedG` replays V_S's typed phases `dTypedT` (the
-- composition of the zerocheck's, the wiring's, the relayout's, A23's and the mini-bus's replays), generic in the
-- parameters, the static data and the instance.

/-!
# `typedG` replays `dTypedT`

**`typedG_replaysG`**: on regions that are V_S's (`TdOk`) and mini-bus tables whose shapes, rounds, depth and fixed
columns are the circuit's, wherever `typedG Td pb P z o`'s rows hold and assert (gate on), `dTypedT p N (N.m3 p)` on
the child's `PUB` from any state at `P` with `ok` keeps `ok`, ends at `typedEnd Td P`; its accumulator is the current
proof's `acc_in` (`accC M pb`), its claims are `typedClaimsN` of the output cells, its evaluations the table cells'.
-/

set_option autoImplicit false

namespace Lvm.Har

open Lvm Lvm.Loop Lvm.Loop.Build Lvm.QTyped Lvm.Q1 Lvm.M3 DM
open Lvm.TypedV (TNat)

/-! ## The positions -/

theorem typedPos_le (Td : TData) (P : Nat) :
    wGP P ≤ rRP P ∧ rRP P ≤ aP P ∧ aP P ≤ mbP P ∧ mbP P ≤ typedEnd Td P := by
  have h1 : mbP P ≤ busEndD Td.mbD (mbP P) := by
    unfold busEndD
    have := le_layersEnd (gkrSteps Td.mbD) 0 (busP1 (mbP P) + 48)
    simp only [busP1] at this ⊢
    omega
  have h2 : busEndD Td.mbD (mbP P) ≤ typedEnd Td P := by
    unfold typedEnd tabEnd; (clear * -; omega)
  refine ⟨?_, ?_, ?_, le_trans h1 h2⟩ <;> simp only [wGP, rRP, aP, mbP, wRP, wVP, rVP] <;> (clear * -; omega)

theorem typedPos_mod {P : Nat} (hP : P % 8 = 0) :
    wGP P % 8 = 0 ∧ rRP P % 8 = 0 ∧ aP P % 8 = 0 ∧ mbP P % 8 = 0 := by
  simp only [wGP, rRP, aP, mbP, wRP, wVP, rVP, zAbcP, zRP, tX, tY, tR, tVars]
  omega

/-! ## The monad laws as propositional rewrites

`bind_run'`, `pure_run'` restated with a non-`rfl` proof, so that `simp` rewrites with
them by `Eq.mpr` steps instead of a definitional change: as `rfl` lemmas, the kernel re-checked the unfolded
`dTypedT` against the folded one through `DM`'s `bind` (≈ 9 s). -/

private theorem bind_runG {α β : Type} (m : DM α) (f : α → DM β) (sig : ByteArray) (s : RS) :
    (m >>= f) sig s = f (m sig s).1 sig (m sig s).2 := (bind_run' m f sig s).trans rfl
private theorem pure_runG {α : Type} (a : α) (sig : ByteArray) (s : RS) : (pure a : DM α) sig s = (a, s) :=
  (pure_run' a sig s).trans rfl

section
variable {c : Ctx} {M : Mem} {sig : ByteArray} {T : Nat}

set_option maxHeartbeats 1000000 in
/-- **The typed core gadget replays `dTypedT`** (soundness direction). -/
theorem typedG_replaysG (vk cL : Vector UInt8 32) (hS : Streamed M sig T) (hH : 11 + pubLanes ≤ T) {pb : Nat}
    (hg : M.k pb = 1) (hvk : ∀ i < 4, M.k (pb + 1 + i) = (digestLanes vk).getD i 0) {z o : Cell}
    (hzE : z.ty = .E) (hoE : o.ty = .E) (hz : z.val M = 0) (ho : o.val M = 1) (p : Params)
    (hl : p.leafdecReads = 1) {Td : TData} {N : TNat} (htd : TdOk Td N) (hsc : sumcheckTabs N.mbT = N.mbT)
    (hS' : Td.mbS = N.mbT.map Tab.shape) (hR : Td.mbR = p.tableRounds) (hD : Td.mbD = p.busDepth)
    (hfix : FixListed N.mbT Td.mbFix) {P : Nat} (hP : P % 8 = 0) (hT : typedEnd Td P + 40 ≤ 8 * T) (q : Ptr)
    (hq : 1 ≤ q.e) :
    Replays c M sig (TypedV.dTypedT p N (N.m3 p) (pubOf vk cL sig)) (typedG Td pb P z o) q P (typedEnd Td P)
      fun v t => v.1 = Lvm.QAcc.accC M pb ∧
        v.2.1 = TypedV.typedClaimsN N p (vs M t.ry) (vs M t.rv) (vs M t.rr) (t.vR.val M) ∧
        v.2.2 = t.tab.map fun e => (vs M e.1, vs M e.2) := by
  intro hok s hs hsok
  have hgv : (kc pb).val M = 1 := Lvm.QAcc.kc_val_one hg
  obtain ⟨l1, l2, l3, l4⟩ := typedPos_le Td P
  obtain ⟨m1, m2, m3, m4⟩ := typedPos_mod hP
  simp only [typedG] at hok
  simp only [typedG, bind_apply, pure_apply, TypedV.dTypedT, bind_runG, pure_runG]
  rw [show N.m3 p = M3.real p (fun _ => N.mbT) from rfl]
  -- the zerocheck
  obtain ⟨hZ, hok⟩ := okb hok
  generalize hzr : (zeroG z (kc pb) P q).1 = zr at hok ⊢
  generalize hq1 : q.adv (zeroG z (kc pb) P q).2 = q1 at hok ⊢
  have hq1e : 1 ≤ q1.e := le_trans hq (by rw [← hq1]; exact adv_e_le _ _)
  have RZ := zeroG_replays (c := c) hS hz hzE hgv rfl hP (by (clear * - hT l1 l2 l3 l4 m1 m2 m3 m4; omega)) q hq hZ s hs hsok
  rw [hzr] at RZ
  generalize TypedV.dZeroT sig s = Zv at RZ ⊢
  obtain ⟨zv, s1⟩ := Zv
  obtain ⟨z1, z2, z3, z4, z5, z6, z7, z8⟩ := RZ
  simp only at z1 z2 z3 z4 z5 z6 ⊢
  have ez : zv.2 = ((zr.2.getD 0 z).val M, (zr.2.getD 1 z).val M, (zr.2.getD 2 z).val M) := by
    rw [← z4, ← z5, ← z6]
  rw [ez]
  -- the wiring
  obtain ⟨hW, hok⟩ := okb hok
  generalize hw : (wireG z o (kc pb) Td pb P zr.2 q1).1 = w at hok ⊢
  generalize hq2 : q1.adv (wireG z o (kc pb) Td pb P zr.2 q1).2 = q2 at hok ⊢
  have hq2e : 1 ≤ q2.e := le_trans hq1e (by rw [← hq2]; exact adv_e_le _ _)
  have RW := wireG_replays (c := c) vk cL hS hH hz ho hzE hoE hgv rfl htd hvk hP (by (clear * - hT l2 l3 l4 m2 m3 m4; omega)) zr.2 q1 hq1e hW s1 z2 z1
  rw [hw] at RW
  generalize TypedV.dWiringT N (pubOf vk cL sig) ((zr.2.getD 0 z).val M, (zr.2.getD 1 z).val M,
    (zr.2.getD 2 z).val M) sig s1 = Wv at RW ⊢
  obtain ⟨wv, s2⟩ := Wv
  obtain ⟨w1, w2, w3, w4, w5, w6, w7, w8, w9, w10, w11⟩ := RW
  simp only at w1 w2 w3 w4 w5 ⊢
  have evS : wv.2.2.getD 1 0 = (w.2.2.getD 1 z).val M := by
    rw [w5]; exact Lvm.QAcc.getD_vals _ _ hz 1
  rw [evS, w3]
  -- the relayout
  obtain ⟨hRl, hok⟩ := okb hok
  generalize hr : (relayG z o (kc pb) Td P w.1 (w.2.2.getD 1 z) q2).1 = r at hok ⊢
  generalize hq3 : q2.adv (relayG z o (kc pb) Td P w.1 (w.2.2.getD 1 z) q2).2 = q3 at hok ⊢
  have hq3e : 1 ≤ q3.e := le_trans hq2e (by rw [← hq3]; exact adv_e_le _ _)
  have RR := relayG_replays (c := c) hS hz ho hzE hoE hgv rfl htd hP (by (clear * - hT l3 l4 m3 m4; omega)) w.1 w6 w7 (w.2.2.getD 1 z) q2
    hq2e hRl s2 w2 w1
  rw [hr] at RR
  generalize TypedV.dRelayT N (vs M w.1) ((w.2.2.getD 1 z).val M) sig s2 = Rv at RR ⊢
  obtain ⟨rv, s3⟩ := Rv
  obtain ⟨r1, r2, r3, r4, r5, r6⟩ := RR
  simp only at r1 r2 r3 r4 ⊢
  have exy : zv.1 ++ vs M w.1 = vs M (zr.1 ++ w.1) := by rw [z3]; simp [vs]
  rw [exy, w4]
  -- A23 at `Φ_Q`
  obtain ⟨hA, hok⟩ := okb hok
  generalize hq4 : q3.adv (qaccT (aP P / 8) pb zr.1 w.1 w.2.1 q3).2 = q4 at hok ⊢
  have hq4e : 1 ≤ q4.e := le_trans hq3e (by rw [← hq4]; exact adv_e_le _ _)
  have hE : ∀ x ∈ zr.1 ++ w.1 ++ w.2.1, x.ty = .E := by
    intro x hx
    simp only [List.mem_append] at hx
    rcases hx with (hx | hx) | hx
    · exact z8 x hx
    · exact w7 x hx
    · exact w9 x hx
  have RA := qaccT_replays (c := c) vk cL hS hH hg hP (by (clear * - hT l4 m4; omega)) zr.1 w.1 w.2.1 z7 w6 w8 hE q3 hA s3 r2 r1
  generalize TypedV.dAccT (pubOf vk cL sig) (vs M (zr.1 ++ w.1)) (vs M w.2.1) sig s3 = Av at RA ⊢
  obtain ⟨av, s4⟩ := Av
  obtain ⟨a1, a2, a3⟩ := RA
  simp only at a1 a2 a3 ⊢
  -- the mini-bus
  obtain ⟨hM, -⟩ := okb hok
  have RM := miniG_replays (c := c) hS hz ho hzE hoE hgv rfl p hl Td N.mbT hsc hS' hR hD hfix
    (pubOf vk cL sig) m4 (by unfold typedEnd at hT; omega) q4 hq4e hM s4 a2 a1
  generalize TypedV.dMiniT p (M3.real p fun _ => N.mbT) N.mbT (pubOf vk cL sig) sig s4 = Mv at RM ⊢
  obtain ⟨mv, s5⟩ := Mv
  obtain ⟨b1, b2, b3⟩ := RM
  refine ⟨b1, b2, a3, ?_, b3⟩
  rw [w5, r3, r4]

end

end Lvm.Har
end
-- ===== end of `LvmQTypedHarG` =====

-- ===== merged from `LvmQTypedHarT` (GOLF module merge: `LvmQTypedHarT.lean` is now a stub importing `LvmQTypedHarS`) =====
section
-- New for lvm2 (roll 8 = B1, L-H): V_S's typed decision program cut into its phases (`decideProgT = decideProgTH`),
-- and the composition of the phase facts into `decideCoreT` and `accOutOfT` (roll 7's `core_of_phases` for
-- `decideProgT`: the typed phases replace phases 2, 3, 3b; phases 4–7 are unchanged; the openings are `dOpenT`).
-- lvm2 roll 11 (M′ `S2GM`, R11-N): one commitment, so one root skip (B1: `C_main`'s and `C_rec`'s).

/-!
# `decideProgT` by phases

| phase | program |
|---|---|
| typed (zerocheck, wiring, relayout, A23 at `Φ_Q`, mini-bus) | `dTypedT p N (N.m3 p) pub` |
| 4 tape, 5 wire, 6 `KS`, 7 `KS` link | `tapePh`, `wirePhC`, `ksPh`, `ksLinkPh` (roll 7's) |
| 8–9 openings | `dOpenT p (smallT p pub)` on the typed claims and `dClaimsZ`'s |

**`core_of_phasesT`**: if every phase, run from its start position with `ok`, keeps `ok`, reaches the next start and
yields fixed values, and the openings read `Σ` to its end, then `decideCoreT` accepts and `accOutOfT` is the typed
phases' accumulator.
-/

set_option autoImplicit false

namespace Lvm.Har

open Lvm DM

/-- **`decideProgT` by phases.** -/
def decideProgTH (p : Params) (N : TypedV.TNat) (vk c : Vector UInt8 32) : DM Acc := do
  let sig ← read
  let pub := pubOf vk c sig
  skip (nodeBytes * 2 ^ (p.level ⟨.main, 0⟩).cap)
  let (acc, tcl, evals) ← TypedV.dTypedT p N (N.m3 p) pub
  let tp ← tapePh p
  let wo ← wirePhC p pub tp.claim
  let (rk, vks, kko, kring) ← ksPh p
  let (okK, kLinkClaims) ← ksLinkPh p (N.m3 p) rk pub
  require okK
  TypedV.dOpenT p (TypedV.smallT p pub) (tcl ++ Shape.dClaimsZ (N.m3 p) p pub [] evals tp wo.1 wo.2 rk vks
    (keccakClaims (N.m3 p).ksBlock kko kring) kLinkClaims)
  pure acc

set_option maxHeartbeats 4000000 in
theorem decideProgT_eq (p : Params) (N : TypedV.TNat) (vk c : Vector UInt8 32) :
    TypedV.decideProgT p N vk c = decideProgTH p N vk c := by
  funext sig s
  simp only [TypedV.decideProgT, decideProgTH, tapePh, wirePhC, ksPh, ksLinkPh, bind_assoc, pure_bind]

/-! The `DM` run lemmas restated with a non-`rfl` proof, so that `simp` rewrites with them by `Eq.mpr` steps: as
`rfl` lemmas, the kernel re-checked the rewritten run against the program through `DM`'s `bind`. -/

private theorem bind_runT {α β : Type} (m : DM α) (f : α → DM β) (sig : ByteArray) (s : RS) :
    (m >>= f) sig s = f (m sig s).1 sig (m sig s).2 := (bind_run' m f sig s).trans rfl
private theorem pure_runT {α : Type} (a : α) (sig : ByteArray) (s : RS) : (pure a : DM α) sig s = (a, s) :=
  (pure_run' a sig s).trans rfl
private theorem require_runT (c : Bool) (sig : ByteArray) (s : RS) :
    require c sig s = ((), { s with ok := c && s.ok }) := (require_run' c sig s).trans rfl
private theorem skip_runT (n : Nat) (sig : ByteArray) (s : RS) :
    skip n sig s = ((), { s with msg := s.msg + n }) := (skip_run' n sig s).trans rfl
private theorem read_runT (sig : ByteArray) (s : RS) : (read : DM ByteArray) sig s = (sig, s) :=
  (read_run' sig s).trans rfl

/-- **`decideCoreT` and `accOutOfT` from the phases** (generic in the parameters and the instance). -/
theorem core_of_phasesT (p : Params) (N : TypedV.TNat) (vk c : Vector UInt8 32) (sig : ByteArray)
    {Pb P4 P5 P6 P7 P8 : Nat} {acc : Acc} {tcl : List (Com × BlockClaim × FE)}
    {evals : List (List FE × List FE)} {tp : TapeRes} {wo : WireOut × List FE} {rk vks : List FE}
    {kko : KeccakOut} {kring : FE × (List FE → FE)} {okK : Bool} {kLinkClaims : List (Com × BlockClaim)}
    (h0 : RS.start.ent + nodeBytes * 2 ^ (p.level ⟨.main, 0⟩).cap = Pb)
    (htyped : PhaseAt (TypedV.dTypedT p N (N.m3 p) (pubOf vk c sig)) sig Pb P4 (acc, tcl, evals))
    (htape : PhaseAt (tapePh p) sig P4 P5 tp)
    (hwire : PhaseAt (wirePhC p (pubOf vk c sig) tp.claim) sig P5 P6 wo)
    (hks : PhaseAt (ksPh p) sig P6 P7 (rk, vks, kko, kring))
    (hksl : PhaseAt (ksLinkPh p (N.m3 p) rk (pubOf vk c sig)) sig P7 P8 (okK, kLinkClaims)) (hokK : okK = true)
    (hopen : ∀ s : RS, pos s = P8 → s.ok = true →
      let o := TypedV.dOpenT p (TypedV.smallT p (pubOf vk c sig))
        (tcl ++ Shape.dClaimsZ (N.m3 p) p (pubOf vk c sig) [] evals tp wo.1 wo.2 rk vks
          (keccakClaims (N.m3 p).ksBlock kko kring) kLinkClaims) sig s
      o.2.ok = true ∧ o.2.ent = sig.size ∧ o.2.msg = 0) :
    TypedV.decideCoreT p N vk c sig = true ∧ TypedV.accOutOfT p N vk c sig = acc := by
  obtain ⟨s1, hs1⟩ : ∃ s1 : RS, s1 = ⟨RS.start.ent, nodeBytes * 2 ^ (p.level ⟨.main, 0⟩).cap, true⟩ :=
    ⟨_, rfl⟩
  have e1 : pos s1 = Pb := by rw [← h0, hs1]; rfl
  obtain ⟨b1, b2, b3⟩ := htyped s1 e1 (by rw [hs1])
  generalize hB : TypedV.dTypedT p N (N.m3 p) (pubOf vk c sig) sig s1 = B at b1 b2 b3
  obtain ⟨bv, s2⟩ := B
  simp only at b1 b2 b3
  rw [b1] at hB
  obtain ⟨c1, c2, c3⟩ := htape s2 b3 b2
  generalize hC : tapePh p sig s2 = CC at c1 c2 c3
  obtain ⟨cv, s5⟩ := CC
  simp only at c1 c2 c3
  rw [c1] at hC
  obtain ⟨l1, l2, l3⟩ := hwire s5 c3 c2
  generalize hL : wirePhC p (pubOf vk c sig) tp.claim sig s5 = LL at l1 l2 l3
  obtain ⟨lv, s6⟩ := LL
  simp only at l1 l2 l3
  rw [l1] at hL
  obtain ⟨k1, k2, k3⟩ := hks s6 l3 l2
  generalize hK : ksPh p sig s6 = KK at k1 k2 k3
  obtain ⟨kv, s7⟩ := KK
  simp only at k1 k2 k3
  rw [k1] at hK
  obtain ⟨m1, m2, m3⟩ := hksl s7 k3 k2
  generalize hM : ksLinkPh p (N.m3 p) rk (pubOf vk c sig) sig s7 = MM at m1 m2 m3
  obtain ⟨mv, s8⟩ := MM
  simp only at m1 m2 m3
  rw [m1] at hM
  obtain ⟨s8', hs8'⟩ : ∃ s8' : RS, s8' = { s8 with ok := okK && s8.ok } := ⟨_, rfl⟩
  have e8 : pos s8' = P8 := by rw [hs8']; exact m3
  have o8 : s8'.ok = true := by rw [hs8']; simp [hokK, m2]
  obtain ⟨o1, o2', o3⟩ := hopen s8' e8 o8
  generalize hO : TypedV.dOpenT p (TypedV.smallT p (pubOf vk c sig))
    (tcl ++ Shape.dClaimsZ (N.m3 p) p (pubOf vk c sig) [] evals tp wo.1 wo.2 rk vks
      (keccakClaims (N.m3 p).ksBlock kko kring) kLinkClaims) sig s8' = OO at o1 o2' o3
  obtain ⟨ov, s9⟩ := OO
  simp only at o1 o2' o3
  have run : decideProgTH p N vk c sig RS.start = (acc, s9) := by
    unfold decideProgTH
    simp only [bind_runT, read_runT, skip_runT, pure_runT, require_runT]
    have hs1' : ({ RS.start with msg := RS.start.msg + nodeBytes * 2 ^ (p.level ⟨.main, 0⟩).cap } : RS) = s1 := by
      simp [hs1, RS.start]
    rw [hs1', hB]
    simp only
    rw [hC]
    simp only
    rw [hL]
    simp only
    rw [hK]
    simp only
    rw [hM]
    simp only
    rw [← hs8', hO]
  have hrun : (TypedV.decideProgT p N vk c).runOn sig = (acc, s9) := by
    rw [decideProgT_eq, DM.runOn, StateT.run]; exact run
  -- `decideCoreT`, `accOutOfT` by `delta` on the bare constants: unfolding them applied (`unfold`) left the kernel a
  -- check whose `match`/projection on the run it reduced by running `decideProgT` symbolically
  have eC : @TypedV.decideCoreT = @TypedV.decideCoreT := rfl
  conv at eC => rhs; delta TypedV.decideCoreT
  have eA : @TypedV.accOutOfT = @TypedV.accOutOfT := rfl
  conv at eA => rhs; delta TypedV.accOutOfT
  rw [eC, eA]
  beta_reduce
  rw [hrun]
  simp only [o1, o2', o3, Bool.true_and, beq_self_eq_true, and_self]

end Lvm.Har
end
-- ===== end of `LvmQTypedHarT` =====

/-!
# The typed HAR at `P20`

**Headline** (fixed; `nodeT20` consumes it with L-D's glue: `decideFT = decideCoreT ∧ Φ_Q(acc_out) = y`, the last
from `AccOkT` and `PhiQC_eq` through `S.cache`):

* **`harithT20 S H`**: on a node statement (`okS`, `b = 1`) and a good pair, with the input map on the pair's memory
  (`InMapM`), the child's stream a trace of the schedule (`LaneLink`, `LinkOk`), `qaB`'s segments holding and
  asserting at Q_arith's pointer, and the memory facts of the `BITS` rows (`BVT`, roll 7's `BVFacts` on `memT`;
  L-D proves them from the typed `BITS` rows): `decideCoreT P20 NT20 vk c_L Σ' = true` and
  `accOutOfT P20 NT20 vk c_L Σ' = acc_in`.

**Parts** (the static `Bool` check they need, `harChkB`, is L-W's guard field `S.har`, as roll 7's `S.hwr`, `S.hwm`,
`S.hwz`):

1. **`core_of_phasesT`** (`LvmQTypedHarT`; the composition, as `core_of_phases`): `decideCoreT ∧ accOutOfT = acc` from the typed phases'
   `PhaseAt` (`dTypedT`), phases 4–7 (`tapePh`, `wirePhC`, `ksPh`, `ksLinkPh`, unchanged) and the openings
   (`dOpenT` at `smallT`).
2. **`typedG_replays`** (the typed core gadget; restated with the guard `S` and the stream bounds): `typedG` replays `dTypedT` from `typedPos P20` to
   `typedEnd tdata20 (typedPos P20)`; its values are the cells' (the folded accumulator is `PUB`'s `acc_in`, the
   typed claims are `typedClaimsN` of the cells, the mini-bus's evaluations the table cells').
3. **Phases 4–7**: roll 7's `p47_at` (`LvmQAsmHarP47`), unchanged, at `P4 = typedEnd tdata20 (typedPos P20)`.
4. **`openT_at`** (the openings at ν = 23, both shapes): `openG`'s rows give `dOpenT P20 (smallT P20 pub)` on the
   cells' claims (`claimsT M cs`), as roll 7's `open_at` gives `openPhZ`.
-/

set_option autoImplicit false

namespace Lvm.Har

open RecursionFast Lvm Lvm.Loop Lvm.Loop.Build Lvm.Q1 Lvm.QAsm Lvm.QTyped Lvm.Typed Lvm.NS Lvm.T Lvm.ASM Lvm.QLink
  Lvm.Replay DM
open Lvm.M3 (lay26)
open Lvm.VEq (pubX)
open LeanVM.Protocol (Column)

/-! ## The static facts at `P20` (L-H) -/

/-- **The typed HAR's numbers at `P20`** (one kernel decision): phases 4–7's positions (roll 7's `P47Pos`), the
lane bounds, the sizes, the typed phases' and the openings' positions (`T` the stream's lanes). -/
def HarNumT (T P4 P5 P6 P7 P8 : Nat) : Prop :=
  (P4 + 40 = 8 * aLane P20 0 ∧ P4 + 72 * P20.logN + 40 = 8 * aLane P20 1 ∧
    8 * aLane P20 2 - 40 = P4 + 72 * P20.logN + 600 ∧
    Lvm.Q1.tapeEnd (P20.logN - 5) (aLane P20 2) = aLane P20 3 ∧ 8 * aLane P20 3 - 40 = P5 ∧
    8 * Lvm.Q1.wireEnd (P20.logN - 5) (aLane P20 3) - 40 = P6 ∧ P6 + 40 = 8 * aLane P20 4 ∧
    kV P20.ksLog P6 + 40 = 8 * aLane P20 5 ∧ kG P20.ksLog P6 = 8 * aLane P20 6 - 40 ∧
    8 * gkrEnd (P20.ksLog - 4) (aLane P20 6) - 40 + 72 * ringStages = P7 ∧ P7 + 40 = 8 * aLane P20 7 ∧
    ksP2 P20 P7 + 96 = P8) ∧
  5 ≤ P20.logN ∧ 4 ≤ P20.ksLog ∧ 5 ≤ aLane P20 2 ∧ 5 ≤ aLane P20 3 ∧ 5 ≤ aLane P20 6 ∧
  Lvm.Q1.wireEnd (P20.logN - 5) (aLane P20 3) + 2 ≤ T ∧ gkrEnd (P20.ksLog - 4) (aLane P20 6) + 48 ≤ T ∧
  aLane P20 0 + 9 * P20.logN + 2 < T ∧ aLane P20 1 + 3 * 25 + 2 < T ∧
  aLane P20 4 + 9 * P20.ksLog + 2 < T ∧ aLane P20 5 + 3 * 25 + 2 < T ∧
  P20.logN ≤ 2 ^ Lvm.QAsm.clog2 P20.logN ∧ P20.ksLog ≤ 2 ^ Lvm.QAsm.clog2 P20.ksLog ∧
  ksQV P20.ksLog (aLane P20 7) + 3 * 4 + 3 ≤ T ∧
  aLane P20 7 + 9 * (P20.ksLog + laneBits) + 15 * P20.ksLog + 12 ≤ T ∧
  1 ≤ spongeBlocks P20 ∧ spongeBlocks P20 ≤ 2 ^ P20.ksLog ∧ ksSplit P20 + 431 ≤ 2 ^ P20.ksLog ∧
  29 ≤ T ∧ P20.logN ≤ 64 ∧ 11 + pubLanes ≤ T ∧ P4 + 40 ≤ 8 * T ∧ P8 = 8 * openU P20 ∧
  P20.mainLevels.length ≤ (opens P20).length ∧
  P20.leafdecReads = 1 ∧ P20.nuRec = 19 ∧ P20.nuMain = 23 ∧ P20.logN = 20 ∧ typedPos P20 % 8 = 0 ∧
  busEndD P20.busDepth (mbP (typedPos P20)) + 72 + 144 * P20.tableRounds = phaseByte P20 .tape ∧
  RS.start.ent + nodeBytes * 2 ^ (P20.level ⟨.main, 0⟩).cap = typedPos P20

-- (lvm2 E2F-G: `harNumT20`, `layOk_9T`, `okE_P20T`, `mini20`, `typedG_replays` and `harithT20`, roll 11's
-- decisions at `P20`, moved to `LvmQTypedHar20`, outside the S2GF certificate's import closure.)

/-- `D`'s block and selector at `P20` (`tapeTails_eq`'s `hD`, `hds`). -/
theorem hDzT : Lvm.dBlock P20 = ⟨22, 0⟩ ∧ dSel P20 = 0 := ⟨by decide +kernel, by decide +kernel⟩

/-! ## The guard check `harChkB` at `P20` -/

theorem phases47S_eqT (C : QCfg) : phases47S C = phases47 C := by
  rw [phases47S_eq]; unfold VF.phases47F phases47; rw [VF.tapeGadgetF_eq, VF.gkrGadgetF_eq]

/-- **What `harChkB` gives** (L-W's guard field `SF20.har`): the regions, and the B program's claim parts at Q_arith's
pointer are well formed in both shapes. -/
theorem harChk_sound {C : QCfg} {T : TData} {N : TypedV.TNat} (h : harChkB C T N = true) :
    TdOk T N ∧ claimsOkB C (qarithBParts C T (phases47 C (p2C C)).1 ((p2C C).adv (phases47 C (p2C C)).2)).1 = true := by
  simp only [harChkB, phases47S_eqT, Bool.and_eq_true] at h
  exact ⟨tdOk_of h.2, h.1⟩

/-! ## Glue (`LvmFinHB`'s, which the typed closure does not import) -/

theorem vk_cellsT {M : Mem} {x : List UInt8} {pb : ℕ} {vk : RecursionFast.Digest}
    (hpub : ∀ j < pubLanes, M.k (pb + j) = Lvm.NS.hdrLane x j) (hvk : (hdrOf x).vk = vk) :
    ∀ i < 4, M.k (pb + 1 + i) = (digestLanes vk).getD i 0 := by
  intro i hi
  have hj : 1 + i < pubLanes := by rw [pubLanes_eq]; omega
  have e1 : M.k (pb + 1 + i) = (Lvm.NS.hdrLanes x).getD (1 + i) 0 := by
    rw [Nat.add_assoc, hpub _ hj, Lvm.NS.hdrLanes, List.getD_eq_getElem?_getD, List.getElem?_map,
      List.getElem?_range hj, Option.map_some, Option.getD_some]
  have hv : (pubX x).vk = digestLanes vk := by rw [← hvk]; rfl
  have hl : i < (digestLanes vk).length := by simp only [digestLanes, List.length_map, List.length_range]; omega
  rw [e1, Lvm.NS.hdrLanes_eq_pubX, Pub.hdrLanes, hv]
  simp only [List.append_assoc, List.singleton_append]
  rw [Nat.add_comm, List.getD_append _ _ _ _ (by rw [List.length_cons]; omega), List.getD_cons_succ]

/-- Accumulators equal coordinate-wise (`LvmAccNodeLen.acc_eq_of`'s text; that module imports the bus refinement). -/
theorem acc_eq_ofT {a b : Acc} (ha : a.pt.length = accVars) (hb : b.pt.length = accVars)
    (hpt : ∀ i < accVars, a.pt.getD i 0 = b.pt.getD i 0) (hy : a.y = b.y) : a = b := by
  obtain ⟨pa, ya⟩ := a
  obtain ⟨pb, yb⟩ := b
  simp only at ha hb hpt hy
  subst hy
  congr
  refine List.ext_getElem (by rw [ha, hb]) fun i h1 h2 ↦ ?_
  have := hpt i (by omega)
  rwa [List.getD_eq_getElem _ _ h1, List.getD_eq_getElem _ _ h2] at this

theorem accC_eqT {M : Mem} {x : List UInt8} {pb : ℕ}
    (hpub : ∀ j < pubLanes, M.k (pb + j) = Lvm.NS.hdrLane x j) : Lvm.QAcc.accC M pb = (pubX x).accIn := by
  have hP : ∀ j a, j < pubLanes → a = pb + j → M.k a = Lvm.NS.hdrLane x j := fun j a hj ha => ha ▸ hpub j hj
  have hL : pubLanes = 747 := pubLanes_eq
  have hA : accVars = 43 := rfl
  refine acc_eq_ofT (by simp only [Lvm.QAcc.accC, List.length_map, List.length_range])
    (by rw [pubX]; simp [pubOf]) (fun i hi => ?_) ?_
  · rw [accIn_pt_lanes x hi]
    simp only [Lvm.QAcc.accC, List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range hi,
      Option.map_some, Option.getD_some]
    rw [hP (615 + 3 * i) _ (by omega) (by omega), hP (616 + 3 * i) _ (by omega) (by omega),
      hP (617 + 3 * i) _ (by omega) (by omega)]
  · rw [accIn_y_lanes x]
    simp only [Lvm.QAcc.accC]
    rw [hP (615 + 3 * accVars) _ (by omega) (by omega), hP (616 + 3 * accVars) _ (by omega) (by omega),
      hP (617 + 3 * accVars) _ (by omega) (by omega)]

theorem sigma_sizeT {p : Params} {ws : List Word} (h : hashedLen p ≤ 8 * ws.length) :
    (sigma p ws).size = hashedLen p := by
  simp only [sigma, ByteArray.size, List.size_toArray, List.length_take, wordsBytes_length]
  omega

/-! ## The headline -/

/-- The child's trace bytes `Σ'` of a `C_rec` candidate. -/
abbrev sigC (qr : Column 19) : ByteArray := traceBytesB (decode P20 (wsC qr))

/-- **The memory facts of the `BITS` rows the HAR reads** (roll 7's `BVFacts` fields on the B program's memory
`memT`; L-D proves them from the typed `BITS` rows `bitsAux`): `s'`'s bits, `n'`'s bits and range, the positions of
both openings, the proof-of-work fields. -/
structure BVT (vk : RecursionFast.Digest) (x : List UInt8) (qm : Column CMain.nu20) (qr : Column 19) : Prop where
  sb : Lvm.Q1.SBitsS (memT x qm qr).k (sigIn cfg20).hd (bsB cfg20)
  nb : NBits (memT x qm qr).k ((sigIn cfg20).bn + 2) P20.logN
  n1 : 1 ≤ (pubOf vk (hdrOf x).cL (sigC qr)).n
  nN : (pubOf vk (hdrOf x).cL (sigC qr)).n ≤ 2 ^ P20.logN
  -- R11-E (M′, `S2GM`): the child has no `C_rec` opening, so B1's `posr` field (its positions) is gone and `posm`
  -- starts at `openU P20 + 15` (was `stackEndL … recLevels (openU P20 + 15) + 15`)
  posm : PosOk (cfgMain P20 (posBase cfg20) (pwBase cfg20)) (memT x qm qr) (sigC qr) 0 P20.mainLevels (openU P20 + 15)
  pw : ∀ k < (Lvm.QLink.opens P20).length, ((memT x qm qr).k (pwB cfg20 + k)).val.toNat < 2 ^ (64 - P20.grind)


/-! ## The parts -/

-- Part 1, the composition `core_of_phasesT`: proved in `LvmQTypedHarT` (L-D's statement, unchanged).

/-! ## The mini-bus's record at `P20` (from the guard's `fitsMiniB`) -/

theorem tdataOf_mb (C : QCfg) (F : TFrz) : (tdataOf C F).mbS = (mbTOf C F).map M3.Tab.shape ∧
    (tdataOf C F).mbR = ((mbTOf C F).map (·.τ)).foldl max 0 ∧
    (tdataOf C F).mbD = log2Ceil (M3.pushLeavesR (mbTOf C F)) ∧ (tdataOf C F).mbFix = mbFixOf C := by
  simp only [tdataOf, and_self]

theorem NT20_mbT : NT20.mbT = mbTOf cfg20 frz20 := by rw [NT20_eq]; simp only [tnatOf]
theorem tdata20_mbS : tdata20.mbS = (mbTOf cfg20 frz20).map M3.Tab.shape := by rw [tdata20_eq]; exact (tdataOf_mb _ _).1
theorem tdata20_mbR : tdata20.mbR = ((mbTOf cfg20 frz20).map (·.τ)).foldl max 0 := by
  rw [tdata20_eq]; exact (tdataOf_mb _ _).2.1
theorem tdata20_mbD : tdata20.mbD = log2Ceil (M3.pushLeavesR (mbTOf cfg20 frz20)) := by
  rw [tdata20_eq]; exact (tdataOf_mb _ _).2.2.1
theorem tdata20_mbFix : tdata20.mbFix = mbFixOf cfg20 := by rw [tdata20_eq]; exact (tdataOf_mb _ _).2.2.2


/-- **The opening at ν = 23, generic in the parameters** (the proof of part 4; M′ `S2GM`: `C_main`'s alone, roll 7's
`open_at` on `dOpenT`): from `openG`'s rows (gate on) on claims all on `C_main`, `dOpenT p (smallT p pub)` on the
cells' claims, from phase 8's start with `ok`, keeps `ok`, reads `Σ'` to its end and leaves no message pending. -/
theorem openT_atG (p : Params) (hnu : p.nuMain = 23) {c : Ctx} {M : Mem} {sig : ByteArray} {T : Nat}
    (hS : Streamed M sig T) (hg : M.k (pbB cfg20) = 1)
    (hlm : LayOk (cfgMain p (posBase cfg20) (pwBase cfg20)) T = true)
    (hop : p.mainLevels.length ≤ (Lvm.QLink.opens p).length)
    (hposm : PosOk (cfgMain p (posBase cfg20) (pwBase cfg20)) M sig 0 p.mainLevels (openU p + 15))
    (hend : 8 * stackEndL p.grind p.mainOod p.mainLevels (openU p + 15) = sig.size)
    (hpw : ∀ x < (Lvm.QLink.opens p).length, p.grind ≠ 0 → (M.k (pwB cfg20 + x)).val.toNat < 2 ^ (64 - p.grind))
    (cs : List CClaim) (hall : cs.all (·.com == .main) = true)
    (hwm : ClaimsWF p.nuMain (onCom cs .main) = true) {z one : Cell} (hzE : z.ty = .E) (hoE : one.ty = .E)
    (hz : z.val M = 0) (ho : one.val M = 1) {q : Ptr} (hq : 1 ≤ q.e) (pub : Pub) (mb : List Cell)
    (hσ : (1 + (mb.getD 18 default).val M) * (1 + (mb.getD 19 default).val M) =
      if decide (pub.n ≤ 2 ^ CMain.smallLogN20) then 1 else 0)
    (hzw : ∀ cc ∈ onCom cs .main, Lvm.QShape.ZWF z cc = true)
    (h : Lvm.QSig.Ok c M (openG (cfgMain p (posBase cfg20) (pwBase cfg20))
      (p.logN == 20 && p.nuMain == CMain.nu20) cs mb z one (kc (pbB cfg20))) q) :
    ∀ s : RS, pos s = 8 * openU p → s.ok = true →
      (TypedV.dOpenT p (TypedV.smallT p pub) (claimsT M cs) sig s).2.ok = true ∧
      (TypedV.dOpenT p (TypedV.smallT p pub) (claimsT M cs) sig s).2.ent = sig.size ∧
      (TypedV.dOpenT p (TypedV.smallT p pub) (claimsT M cs) sig s).2.msg = 0 := by
  intro s hs hok
  have hall' : (claimsT M cs).all (·.1 == .main) = true := by rw [claimsT, List.all_map]; exact hall
  have hrq : ({ s with ok := true && s.ok } : RS) = s := by cases s; rfl
  have e : TypedV.dOpenT p (TypedV.smallT p pub) (claimsT M cs) sig s =
      verifyStackedOpening p.mainLevels p.nuMain (Shape.onStackZsF (Shape.smallP p pub)
        ((onCom cs .main).map fun cc => ((cc.val M).2, Lvm.QShape.tailC M cc))) false p.grind p.mainOod sig s := by
    have h1 : TypedV.smallT p pub = Shape.smallP p pub := by simp only [TypedV.smallT, Shape.smallP, hnu]
    unfold TypedV.dOpenT Shape.onStackZsF
    rw [dm_bind, require_runW, hall', hrq, claimsT_main, h1, hnu, TypedV.onStackZBN_23]
  rw [e]
  simp only [openG] at h
  have hzp : (p.logN == 20 && p.nuMain == CMain.nu20) = true → p.logN = 20 ∧ p.nuMain = CMain.nu20 :=
    fun hz' => by simpa using hz'
  have hpwm : PwOk (cfgMain p (posBase cfg20) (pwBase cfg20)) M 0 (cfgMain p (posBase cfg20) (pwBase cfg20)).levels :=
    fun i hi hg0 => hpw (0 + i) (by simp only [cfgMain] at hi; omega) hg0
  have hs' : pos s = 8 * (cfgMain p (posBase cfg20) (pwBase cfg20)).U := hs
  have hend' : 8 * stackEndL (cfgMain p (posBase cfg20) (pwBase cfg20)).g (cfgMain p (posBase cfg20) (pwBase cfg20)).ood
      (cfgMain p (posBase cfg20) (pwBase cfg20)).levels ((cfgMain p (posBase cfg20) (pwBase cfg20)).U + 15) =
      sig.size := hend
  by_cases hz' : (p.logN == 20 && p.nuMain == CMain.nu20) = true
  · rw [if_pos hz'] at h
    have hsm : Shape.smallP p pub = decide (pub.n ≤ 2 ^ CMain.smallLogN20) := by
      obtain ⟨e1, e2⟩ := hzp hz'
      simp [Shape.smallP, e1, e2]
    rw [hsm]
    have hνZ : (cfgMain p (posBase cfg20) (pwBase cfg20)).nu = CMain.nu20 := (hzp hz').2
    have hwm' : ClaimsWF CMain.nu20 (onCom cs .main) = true := by rw [← (hzp hz').2]; exact hwm
    obtain ⟨o2, p2, m2⟩ := stackZ_run _ _ mb z one _ _ hσ hνZ hwm' hzw hS hlm hz ho hzE hoE (gate_val cfg20 hg) rfl
      hposm hpwm hq h s hs'
    simp only [cfgMain] at o2 p2 m2 hend'
    refine ⟨o2.trans hok, ?_, m2⟩
    simp only [pos] at p2
    omega
  · rw [if_neg hz'] at h
    have hsm : Shape.smallP p pub = false := by
      have : (p.logN == 20 && p.nuMain == CMain.nu20) = false := by simpa using hz'
      simp only [Shape.smallP]
      rw [this, Bool.false_and]
    rw [hsm]
    simp only [Shape.onStackZsF, Bool.false_eq_true, if_false, List.map_map]
    rw [show ((fun x : BlockClaim × FE => x.1.onStack) ∘
      fun cc : CClaim => ((CClaim.val M cc).2, Lvm.QShape.tailC M cc)) = fun cc => (cc.val M).2.onStack from rfl]
    obtain ⟨o2, p2, m2⟩ := stack_run _ _ z one _ hS (by simp only [StackOk, hlm, Bool.true_and]; exact hwm) hz ho
      hzE hoE (gate_val cfg20 hg) rfl
      hposm hpwm hq h s hs'
    simp only [cfgMain] at o2 p2 m2 hend'
    refine ⟨o2.trans hok, ?_, m2⟩
    simp only [pos] at p2
    omega

/-- **Part 4: the opening at ν = 23, both shapes** (R11-E, M′: restated on the one-commitment `openG`; B1's
`hlr`, `hposr`, `hwr` (`C_rec`'s layout, positions and claims) are gone, `C_main`'s opening starts at `openU P20`;
R11-N: `hall`, every claim on `C_main`, which `dOpenT` requires) (roll 7's `open_at` on `dOpenT`): from `openG`'s
rows (gate on), `dOpenT P20 (smallT P20 pub)` on the cells' claims, from phase 8's start with `ok`, keeps `ok`, reads
`Σ'` to its end and leaves no message pending. -/
theorem openT_at {c : Ctx} {M : Mem} {sig : ByteArray} {T : Nat} (hS : Streamed M sig T)
    (hg : M.k (pbB cfg20) = 1)
    (hlm : LayOk (cfgMain P20 (posBase cfg20) (pwBase cfg20)) T = true)
    (hop : P20.mainLevels.length ≤ (Lvm.QLink.opens P20).length)
    (hposm : PosOk (cfgMain P20 (posBase cfg20) (pwBase cfg20)) M sig 0 P20.mainLevels (openU P20 + 15))
    (hend : 8 * stackEndL P20.grind P20.mainOod P20.mainLevels (openU P20 + 15) = sig.size)
    (hpw : ∀ x < (Lvm.QLink.opens P20).length, P20.grind ≠ 0 → (M.k (pwB cfg20 + x)).val.toNat < 2 ^ (64 - P20.grind))
    (cs : List CClaim) (hall : cs.all (·.com == .main) = true)
    (hwm : ClaimsWF P20.nuMain (onCom cs .main) = true) {z one : Cell} (hzE : z.ty = .E) (hoE : one.ty = .E)
    (hz : z.val M = 0) (ho : one.val M = 1) {q : Ptr} (hq : 1 ≤ q.e) (pub : Pub) (mb : List Cell)
    (hσ : (1 + (mb.getD 18 default).val M) * (1 + (mb.getD 19 default).val M) =
      if decide (pub.n ≤ 2 ^ CMain.smallLogN20) then 1 else 0)
    (hzw : ∀ cc ∈ onCom cs .main, Lvm.QShape.ZWF z cc = true)
    (h : Lvm.QSig.Ok c M (openG (cfgMain P20 (posBase cfg20) (pwBase cfg20))
      (P20.logN == 20 && P20.nuMain == CMain.nu20) cs mb z one (kc (pbB cfg20))) q) :
    ∀ s : RS, pos s = 8 * openU P20 → s.ok = true →
      (TypedV.dOpenT P20 (TypedV.smallT P20 pub) (claimsT M cs) sig s).2.ok = true ∧
      (TypedV.dOpenT P20 (TypedV.smallT P20 pub) (claimsT M cs) sig s).2.ent = sig.size ∧
      (TypedV.dOpenT P20 (TypedV.smallT P20 pub) (claimsT M cs) sig s).2.msg = 0 :=
  openT_atG P20 rfl hS hg hlm hop hposm hend hpw cs hall hwm hzE hoE hz ho hq pub mb hσ hzw h

/-- **What phases 4–7's output cells are** (generic in the configuration and the pointer: roll 7's `claims_at`
steps; at the instance a `simp` on `phases47 cfg20 (p2C cfg20)` is slow): the tape's 25 values, `KS`'s 25 lanes,
`logN` point cells, and `KS`'s GKR slices are the stream's. -/
theorem p47_out_facts (C : QCfg) {c : Ctx} {M : Mem} {sig : ByteArray} {T : Nat} {p2 : Ptr} {o : P47Out}
    (h47 : Lvm.QSig.Ok c M (phases47 C) p2) (ho47 : (phases47 C p2).1 = o) (hS : Streamed M sig T)
    (hlayk : layOk (C.p.ksLog - 4) = true) (hqk : 5 ≤ aLane C.p 6) (hT : gkrEnd (C.p.ksLog - 4) (aLane C.p 6) ≤ T) :
    o.v.length = 25 ∧ o.vk.length = 25 ∧ o.r.length = C.p.logN ∧
      (o.kko.vals M).slices = slAt sig (gkrEnd (C.p.ksLog - 4) (aLane C.p 6) - 192) := by
  have hO : (phases47 C p2).1 = o := ho47
  simp only [phases47, bind_apply, pure_apply] at hO
  have ekko := congrArg P47Out.kko hO
  have ev : o.v.length = 25 := by rw [← hO]; simp only [List.length_map, List.length_range]
  have evk : o.vk.length = 25 := by rw [← hO]; simp only [List.length_map, List.length_range]
  have erl : o.r.length = C.p.logN := by rw [← hO]; simp only [List.length_map, List.length_range]
  dsimp only at ekko
  clear hO
  obtain ⟨hh, -⟩ := h47
  simp only [phases47] at hh
  rw [hold_bind] at hh; obtain ⟨-, hh⟩ := hh
  rw [hold_bind] at hh; obtain ⟨-, hh⟩ := hh
  rw [hold_bind] at hh; obtain ⟨-, hh⟩ := hh
  rw [hold_bind] at hh; obtain ⟨-, hh⟩ := hh
  rw [hold_bind] at hh; obtain ⟨-, hh⟩ := hh
  rw [hold_bind] at hh; obtain ⟨-, hh⟩ := hh
  rw [hold_bind] at hh; obtain ⟨-, hh⟩ := hh
  rw [hold_bind] at hh; obtain ⟨-, hh⟩ := hh
  rw [hold_bind] at hh; obtain ⟨-, hh⟩ := hh
  rw [hold_bind] at hh; obtain ⟨hhGk, -⟩ := hh
  have sK := gkrGadget_slices hlayk hqk hS hT hhGk
  rw [ekko] at sK
  exact ⟨ev, evk, erl, sK⟩

/-- **`claimsOkB`'s parts** (by rewriting a generic tuple: a `simp` on the instance's claim list is slow; M′: every
claim on `C_main`). -/
theorem claimsOkB_parts {C : QCfg} {z : Cell} {a b c d e f : List CClaim}
    (h : claimsOkB C (z, a, b, c, d, e, f) = true) :
    (a ++ b ++ (c ++ d) ++ e ++ f).all (·.com == .main) = true ∧
      ClaimsWF C.p.nuMain (onCom (a ++ b ++ (c ++ d) ++ e ++ f) .main) = true ∧
      (∀ cc ∈ onCom (a ++ b ++ (c ++ d) ++ e ++ f) .main, Lvm.QShape.ZWF z cc = true) ∧
      a.all noDRB = true ∧ b.all noDRB = true ∧ (d ++ e ++ f).all noDRB = true := by
  simp only [claimsOkB, csB, Bool.and_eq_true] at h
  obtain ⟨⟨⟨h1, h2⟩, h3⟩, h4⟩ := h
  simp only [List.all_append, Bool.and_eq_true] at h4
  obtain ⟨⟨⟨⟨h0, h5⟩, h6⟩, h7⟩, h8⟩ := h4
  exact ⟨h1, h2, List.all_eq_true.mp h3, h0, h5, by simp only [List.all_append, h6, h7, h8, Bool.and_self]⟩

/-- `M3.real`'s table claims on a native instance's tables. -/
theorem m3_tableClaimsT (N : TypedV.TNat) (p : Params) (pub : Pub) (ev : List (List FE × List FE)) :
    (N.m3 p).tableClaims pub ev = M3.tableClaimsR (M3.sumcheckTabs N.mbT) ev := rfl

/-- `M3.real`'s `KS` block on a native instance. -/
theorem m3_ksBlockT (N : TypedV.TNat) (p : Params) : (N.m3 p).ksBlock = ⟨p.ksLog + slotLog, (layout0 p).ks⟩ := rfl

/-- Q_arith's pointer (a rewrite: a definitional check would run Q_link's and Q_sig's builders). -/
theorem p2_eqT : p2 (lay cfg20) (sigIn cfg20) (nK cfg20) 0 = p2C cfg20 := by
  unfold p2 p2P p1P p0 p2C p1C
  rw [show cfg20.p = P20 from rfl]

end Lvm.Har
