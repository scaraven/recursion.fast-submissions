-- New for lvm (WP-16a-QFX); lvm2 roll 8 (B1, L-D): the static facts of `cfg20`'s node program that do not read
-- Q_arith or the bus record, split out of `LvmQAsmFacts` (unchanged) so that the typed backend's `NodeSound`
-- (`LvmNodeSoundT`, the B program `QB`) reads them without the bus path's modules.
import LvmNodeSoundCirc
import LvmQAsmLay
import LvmReplay

/-!
# The node program's static facts (any Q_arith)

For `lay := lay cfg20`, `I := sigIn cfg20`, `nK := nK cfg20`, `nE := 0` and any Q_arith `qa`:

* a gadget's program's cell counts from its segments (`cells_toProgram`: no `group` in the kernel), hence
  `nK ≤ cells .K` and Q_arith's pointer below it (`p2_le_cells`);
* the region facts `hfg20 … hslI20`, `hws20`, Q_link's `hQ20`, `hS20` (rfl or small `decide`s on `cfg20`'s numbers).
-/

set_option autoImplicit false

namespace Lvm.QAsm

open RecursionFast Lvm Lvm.Replay Lvm.Loop Lvm.Loop.Build Lvm.QLink Lvm.QSig Lvm.M3 Lvm.NS

/-! ## The cell counts of a gadget's program -/

theorem advBs_nil (p : Ptr) : p.advBs [] = p := by simp [Ptr.advBs]

theorem advBs_glueB (p : Ptr) (rs : List Row) (bs : List Block) :
    p.advBs (glueB rs bs) = (p.adv (rs.map .row)).advBs bs := by
  unfold glueB
  rcases rs with _ | ⟨r, rs⟩
  · simp
  · simp only [List.isEmpty_cons, Bool.false_eq_true, ite_false]
    rw [Ptr.advBs_cons, advBs_glue]

/-- Grouping keeps the pointer. -/
theorem groupAux_adv : ∀ (p : Ptr) (δ : List Seg),
    (p.adv ((groupAux δ).1.map .row)).advBs (groupAux δ).2 = p.adv δ
  | p, [] => by simp [groupAux, advBs_nil]
  | p, .row r :: δ => by
    rw [groupAux_row]
    split
    · simp only [List.map_cons, List.map_nil]
      rw [advBs_glueB, groupAux_adv _ δ, ← Ptr.adv_cons]
    · simp only [List.map_cons]
      rw [Ptr.adv_cons p (.row r) ((groupAux δ).1.map .row), groupAux_adv _ δ, ← Ptr.adv_cons]
  | p, .blk B :: δ => by
    rw [groupAux_blk]
    simp only [List.map_nil, Ptr.adv_nil]
    rw [Ptr.advBs_cons, advBs_blk, advBs_glueB, groupAux_adv _ δ, ← Ptr.adv_cons]

theorem advBs_group (p : Ptr) (δ : List Seg) : p.advBs (group δ) = p.adv δ := by
  rw [group_eq, advBs_glueB, groupAux_adv]

/-- **A gadget's program's cell counts** are its pointer after its segments. -/
theorem cells_toProgram {α : Type} (nK nE : ℕ) (m : BM α) :
    (toProgram nK nE m).cells .K = ((⟨nK, nE⟩ : Ptr).adv (m ⟨nK, nE⟩).2).k ∧
      (toProgram nK nE m).cells .E = ((⟨nK, nE⟩ : Ptr).adv (m ⟨nK, nE⟩).2).e := by
  have h := start_ptr (toProgram nK nE m) (toProgram nK nE m).blocks.length
  rw [List.take_length] at h
  have hb : (toProgram nK nE m).blocks = group (m ⟨nK, nE⟩).2 := rfl
  have hp : ((⟨(toProgram nK nE m).nInK, (toProgram nK nE m).nInE⟩ : Ptr)) = ⟨nK, nE⟩ := rfl
  rw [hb, hp, advBs_group] at h
  exact ⟨congrArg Ptr.k h, congrArg Ptr.e h⟩

theorem nK_le_cells {α : Type} (nK nE : ℕ) (m : BM α) : nK ≤ (toProgram nK nE m).cells .K := by
  rw [(cells_toProgram nK nE m).1]
  exact Nat.le_add_right _ _

/-- **Q_arith's pointer lies inside the program.** -/
theorem p2_le_cells {α : Type} (lay : Layout) (I : SigIn) (qa : BM α) (nK nE : ℕ) :
    (p2 lay I nK nE).k ≤ (Qn lay I qa nK nE).cells .K := by
  rw [(cells_toProgram nK nE _).1]
  have e : (qprog lay I qa ⟨nK, nE⟩).2 =
      (qlink P20 lay (p0 nK nE)).2 ++ ((qsig I (p1 lay nK nE)).2 ++ (qa (p2 lay I nK nE)).2) := rfl
  rw [e, Ptr.adv_append, Ptr.adv_append]
  exact Nat.le_add_right _ _

/-! ## The regions (`cfg20`) -/

theorem hfg20 : (lay cfg20).fg = (sigIn cfg20).flag := rfl
theorem hln20 : (sigIn cfg20).ln = 20 := rfl
theorem hhd20 : (sigIn cfg20).hd = (lay cfg20).sb + 11 := rfl
theorem hyc20 : (sigIn cfg20).yc = (sigIn cfg20).ys + 4 * 430 := rfl
theorem hyls20 : (sigIn cfg20).yls = (sigIn cfg20).ys + 4 * 447 := rfl
theorem hyns20 : (sigIn cfg20).yns = (sigIn cfg20).ys + 4 * 448 := rfl
theorem hfl20 : (sigIn cfg20).flag = pbB cfg20 := rfl
theorem hvkI20 : (sigIn cfg20).vk = pbB cfg20 + 1 := rfl
theorem hcLI20 : (sigIn cfg20).cL = pbB cfg20 + 5 := rfl
theorem hslI20 : (sigIn cfg20).sl = pbB cfg20 + 18 := rfl
theorem hws20 : 2 ^ (lay cfg20).m ≤ 17 * 2 ^ 14 := by decide

/-- Q_link's stream facts (QL's `streamOk_P20`). -/
theorem hS20 : StreamOk P20 := Lvm.QLink.streamOk_P20

/-- `a + slenS (ls.take i)` in one walk of `ls` (`eLane p i = offAt (lens p) 1 i / 8`). -/
def offAt : List ℕ → ℕ → ℕ → ℕ
  | _, a, 0 => a
  | [], a, _ + 1 => a
  | l :: ls, a, i + 1 => offAt ls (a + (40 + l)) i

theorem offAt_eq : ∀ (ls : List ℕ) (a i : ℕ), offAt ls a i = a + slenS (ls.take i)
  | _, a, 0 => by simp [offAt, slenS]
  | [], a, _ + 1 => by simp [offAt, slenS]
  | l :: ls, a, i + 1 => by
    rw [offAt, offAt_eq ls _ i]
    simp only [slenS, List.take_succ_cons, List.map_cons, List.sum_cons]
    omega

/-- `qOkB` with the caps' lanes through `offAt` (one walk of the plan's lengths per opening instead of
`take`, `map`, `sum`). -/
def qOkF (p : Params) (lay : Layout) : Bool :=
  decide ((qltEntries p lay).length ≤ 2 ^ lay.aQ) && decide (hashedLen p / 8 + 17 ≤ 2 ^ lay.m) &&
    decide (17 * nBlk (hashedLen p) + 4 ≤ 2 ^ lay.m) && decide (hashedLen p < 2 ^ 64) &&
    ((opens p).all fun o => decide (1 ≤ o.L.path) && decide (o.L.path < o.L.height) &&
      (pchunks o.L.t).all (fun c => decide (c.2 ≤ lay.K)) &&
      decide (offAt (lens p) 1 o.ce / 8 + 1 + o.co / 8 + 4 * 2 ^ (o.L.height - o.L.path) ≤ 2 ^ lay.m) &&
      decide (o.L.row < 2 ^ 64)) &&
    decide (((opens p).map fun o => o.L.t).sum ≤ 2 ^ lay.pa)

theorem qOkF_eq (p : Params) (lay : Layout) : qOkF p lay = qOkB p lay := by
  have h : ∀ i, offAt (lens p) 1 i / 8 = eLane p i := fun i => by rw [offAt_eq]; rfl
  simp only [qOkF, qOkB, h]

set_option maxRecDepth 200000 in
/-- **Q_link's static checks** on the node program's layout (`qOkB` reads `sb`, `m`, `K`, `aQ`, `pa`;
decided as `qOkF`). -/
theorem hQ20 : QOk P20 (lay cfg20) :=
  qOk_of Lvm.QLink.streamOk_P20 (by rw [← qOkF_eq, P20_eq]; decide +kernel)

end Lvm.QAsm
