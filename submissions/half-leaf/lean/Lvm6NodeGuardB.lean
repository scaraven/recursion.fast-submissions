-- New for lvm6 (WP NODE3, phase 2). The deployed layout's facts N4-cells needs, as run-time Bools for the static
-- guard (`staticOk6`) with soundness lemmas: the PoW blocks, the QLT constants, the `PUB` cells, and the stream and
-- signature cells carrying no public word.
import Lvm6NodeDeploy
import LvmE2QPow
import LvmWiring
import Lvm6NodeGuardC
import Lvm6NodeYRegs

/-!
# Layout facts as guard Bools (WP NODE3)

Each Bool is evaluated on the deployed layout once per process. Each soundness lemma states the fact in the form
N4-cells' `Lvm6NodeCells` takes, spelled out:
* **`powAuxInB`/`powAuxInB_sound`** (N4-cells' `PowAuxIn`): every PoW answer `(q, g)` of `powAns` has a block
  `powBlk g bw q` among the layout's auxiliary blocks. `bw` is read off the block (`blkBw`).
* **`qltCstB`/`qltCstB_sound`** (`QltCst`): the layout's constants are `[(zC, [0]), (qtC, qltData6 P6 lay6)]`.
* **`pubCellsB`/`pubCellsB_sound`** (`PubCells`): cell `pbC + l` (`l < 2^10`) is no constant, its word is
  `pubBase + l`, and that word is `PUB`.
* **`noPubB`/`noPubB_sound`** (the readers' condition, `memTi_pw`): the stream cells `sbC + j` (`j < 2^18`), the `σ'`
  cells `sgC + i` and the `σ_leaf` cells `dstC + i` (`i < 597`) have no `PUB` word.
-/

set_option autoImplicit false

namespace Lvm6.Node.Dep

open Lvm Lvm.Loop Lvm.Typed Lvm.Q2
open Lvm6.Ty (TInst6)

/-- Two auxiliary blocks with the same height and rows are equal. -/
theorem ablk_eq {b b' : ABlk} (hl : b.l = b'.l) (hr : b.rows.map ARow.ops = b'.rows.map ARow.ops) : b = b' := by
  obtain ⟨l, rs⟩ := b
  obtain ⟨l', rs'⟩ := b'
  have hinj : Function.Injective ARow.ops := fun a c h ↦ by
    cases a
    cases c
    simp only at h
    rw [h]
  have e : rs = rs' := List.map_injective_iff.mpr hinj hr
  simp only at hl
  rw [hl, e]

/-- The bit-word base of a PoW block (its first row's first operand). -/
def blkBw (b : ABlk) : ℕ :=
  match b.rows.head? with
  | some r => match r.ops.head? with
    | some (_, .word w _, _) => w
    | _ => 0
  | none => 0

/-- Block `b` is `powBlk g bw q` for its own `bw`. -/
def isPowBlkB (g q : ℕ) (b : ABlk) : Bool :=
  decide (b.l = (powBlk g (blkBw b) q).l) && decide (b.rows.map ARow.ops = (powBlk g (blkBw b) q).rows.map ARow.ops)

/-- **The PoW blocks are in the layout**, by position: aux block `k` is `powAns[k]`'s (G0: one comparison per
entry, not one per aux block). -/
def powAuxInB (lay : Lay) : Bool :=
  decide (powAns.length ≤ lay.aux.length) && (powAns.zip lay.aux).all fun p ↦ isPowBlkB p.1.2 p.1.1 p.2

/-- A positional check over `ps.zip l` gives, for each `a ∈ ps`, a matching element of `l`. -/
theorem zip_all_exists {α β : Type} {ps : List α} {l : List β} {f : α × β → Bool} (hl : ps.length ≤ l.length)
    (h : (ps.zip l).all f = true) : ∀ a ∈ ps, ∃ b ∈ l, f (a, b) = true := by
  intro a ha
  obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem ha
  have hz : (ps[i], l[i]'(by omega)) ∈ ps.zip l := by
    rw [List.mem_iff_getElem]
    exact ⟨i, by simp only [List.length_zip]; omega, by simp⟩
  exact ⟨_, List.getElem_mem _, List.all_eq_true.mp h _ hz⟩

theorem powAuxInB_sound {lay : Lay} (h : powAuxInB lay = true) :
    ∀ a ∈ powAns, ∃ bw, powBlk a.2 bw a.1 ∈ lay.aux := by
  intro a ha
  simp only [powAuxInB, Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨b, hb, hp⟩ := zip_all_exists h.1 h.2 a ha
  simp only [isPowBlkB, Bool.and_eq_true, decide_eq_true_eq] at hp
  exact ⟨blkBw b, ablk_eq hp.1 hp.2 ▸ hb⟩

/-- **The QLT constants.** -/
def qltCstB (lay : Lay) : Bool := decide (lay.cst = [(zC, [0]), (qtC, Lvm6.Q.qltData6 P6 lay6)])

theorem qltCstB_sound {lay : Lay} (h : qltCstB lay = true) :
    lay.cst = [(zC, [0]), (qtC, Lvm6.Q.qltData6 P6 lay6)] := of_decide_eq_true h

/-- A region of `Ti.lay.yregs` covers the words `[w, w + n)` with a source `P` accepts. -/
def coverB (Ti : TInst6) (w n : ℕ) (P : YSrc → Bool) : Bool :=
  Ti.lay.yregs.any fun r ↦ decide (r.base ≤ w ∧ w + n ≤ r.base + 2 ^ r.log) && P r.src

theorem src_of_coverB {Ti : TInst6} (hd : yDisjB Ti.lay.yregs = true) {w n : ℕ} {P : YSrc → Bool}
    (h : coverB Ti w n P = true) {j : ℕ} (hj : j < n) : ∃ s, Ti.src? (w + j) = some s ∧ P s = true := by
  obtain ⟨r, hr, hc⟩ := List.any_eq_true.mp h
  simp only [Bool.and_eq_true, decide_eq_true_eq] at hc
  exact ⟨r.src, src?_of_mem hd hr (by omega), hc.2⟩

/-- **The `PUB` cells** (STARTUP ST-2, per region: GRD's `cellsAtRB` for the cells and the words, the `PUB` region
covering the words on pairwise disjoint regions). -/
def pubCellsB (Ti : TInst6) : Bool :=
  yDisjB Ti.lay.yregs && cellsAtRB Ti.lay pbC (Lvm6.QD.pubBase Ti) (2 ^ 10) &&
    coverB Ti (Lvm6.QD.pubBase Ti) (2 ^ 10) (· == .pub)

theorem pubCellsB_sound {Ti : TInst6} (hlay : Ti.lay.okB Ti.Q = true) (h : pubCellsB Ti = true) :
    ∀ l < 2 ^ 10, Ti.lay.cst? (pbC + l) = none ∧ Ti.lay.wordK (pbC + l) = Lvm6.QD.pubBase Ti + l ∧
      Ti.src? (Lvm6.QD.pubBase Ti + l) = some .pub := by
  have _ := hlay
  intro l hl
  simp only [pubCellsB, Bool.and_eq_true] at h
  obtain ⟨⟨hd, hc⟩, hv⟩ := h
  obtain ⟨h1, h2⟩ := cellsAtRB_sound hc l hl
  obtain ⟨s, hs, hp⟩ := src_of_coverB hd hv hl
  simp only [beq_iff_eq] at hp
  exact ⟨h1, h2, hp ▸ hs⟩

/-- Cells `[c, c + n)` carry words outside `PUB` (per region: their words from `wordK c` on, covered by a non-`PUB`
region). -/
def notPubRB (Ti : TInst6) (c n : ℕ) : Bool :=
  cellsAtRB Ti.lay c (Ti.lay.wordK c) n && coverB Ti (Ti.lay.wordK c) n (· != .pub)

theorem notPubRB_sound {Ti : TInst6} (hd : yDisjB Ti.lay.yregs = true) {c n : ℕ} (h : notPubRB Ti c n = true) :
    ∀ j < n, Ti.src? (Ti.lay.wordK (c + j)) ≠ some .pub := by
  intro j hj
  simp only [notPubRB, Bool.and_eq_true] at h
  rw [(cellsAtRB_sound h.1 j hj).2]
  obtain ⟨s, hs, hp⟩ := src_of_coverB hd h.2 hj
  rw [hs]
  simp only [bne_iff_ne, ne_eq] at hp
  intro e
  exact hp (Option.some.inj e)

/-- **The stream, `σ'` and `σ_leaf` cells carry no public word** (STARTUP ST-2: per region, no word loop). -/
def noPubB (Ti : TInst6) : Bool :=
  yDisjB Ti.lay.yregs && notPubRB Ti sbC (2 ^ 18) && notPubRB Ti sgC 597 && notPubRB Ti dstC 597

theorem noPubB_sound {Ti : TInst6} (hlay : Ti.lay.okB Ti.Q = true) (h : noPubB Ti = true) :
    (∀ j < 2 ^ 18, Ti.src? (Ti.lay.wordK (sbC + j)) ≠ some .pub) ∧
      (∀ i < 597, Ti.src? (Ti.lay.wordK (sgC + i)) ≠ some .pub) ∧
      (∀ i < 597, Ti.src? (Ti.lay.wordK (dstC + i)) ≠ some .pub) := by
  have _ := hlay
  simp only [noPubB, Bool.and_eq_true] at h
  obtain ⟨⟨⟨hd, h1⟩, h2⟩, h3⟩ := h
  exact ⟨notPubRB_sound hd h1, notPubRB_sound hd h2, notPubRB_sound hd h3⟩

/-- **The node layout's facts** (the four above). -/
def nodeLayB (Ti : TInst6) : Bool := powAuxInB Ti.lay && qltCstB Ti.lay && pubCellsB Ti && noPubB Ti

end Lvm6.Node.Dep
