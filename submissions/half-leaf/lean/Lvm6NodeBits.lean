-- New for lvm6 (WP NODE3 phase 3, F2). The deployed circuit's `BITS` classes as typed auxiliary rows (season 1's
-- `BSpec.ablks`): `Q_sig`'s six walk classes and the specialised leaf walk's three, and a new class per
-- (opening, answer lane) for `Q_link`'s position bits (`posSpec6`); the guard's Bool that the layout holds them.
import Lvm6NodeGuardB
import Lvm6NodeSlots
import LvmQTypedBits
import Lvm6NodeBitsBlk
import LvmSigBits

/-!
# `BITS` classes of the deployed circuit (WP NODE3, F2)

Before F2 the `BITS` output cells (`Q_sig`'s `bi … bp`, `bn`, `bh`, `bcl`, `bls`, the leaf walk's, `Q_link`'s
position bits from `lay6.bb`) were free committed words: nothing constrained them. With F2 the exporter's layout
spec adds, per class `S`, the blocks `S.ablks bw` (booleanity of 64 bit words a row, the word read from `wc x`,
each output `oc j x` as the bits' combination; `LvmQTypedBits`), so `LvmBits.row_sound` gives the outputs.

* **`posSpec6 k l`**: opening `k` of `opensP17`, answer lane `l < 2`: one row per draw `q` of the opening's position
  group (entry `pd0 + q`), reading stream cell `sbC + ansLane6 P6 (pd0 + q) + l`. Output `z` is bit `z` of that
  lane (`BOut.bit z`). It goes to `Q_link`'s bit cell `bitBase6 opensP17 lay6 k + h·j + z'` for the position
  `j = q·per + n / h`, bit `z' = n % h` of answer bit `n = 64 l + z` (`QIn6.bits`), when `n < per·h`. The answer's
  unused bits go to a scratch region `lay6.bb + 5120 + 256 k` (unique cells, so no two bits share a cell:
  `Lvm6PlaceBits.posOut_nodup17`; at `P17` level 0 has `19·8 = 152 > 128` unused bits, so the stride is `256`).
* **`sigSpecs6 lay`**: season 1's `SigBits.sigSpecs sigI o` (six classes: the walk's `SigBits`) and
  `QSig.sigSpecsC sigIl sigIl.ys pa` (three: `SigBitsC`), at `qsig6`'s outputs at its pointer `pS lay ⟨nK, 0⟩`.
* **`boolBlk6 S w x`, `outBlk6 S w x`**: row `x` of class `S` (`rowRows6`, `S.chunkRows` at that row, bits from word
  `w`) as two one-iteration aux blocks: the 64 booleanity rows (exactly `2^6` slots), then the word and output rows.
  The exporter lays each as an instance of an aux class per `S` and kind (cost: the class templates plus the
  per-instance cells; one 67-row block padded to `2^7` overflowed the `2^20` slots, NODE3.md).
* **`bitsAuxInB lay`/`bitsAuxInB_sound`**: after the PoW blocks the layout's aux blocks are the rows `bitsRows6`, two
  a row, in order: `∀ S ∈ bitsSpecs6 lay, ∀ x < S.n, ∃ w, boolBlk6 S w x ∈ lay.aux ∧ outBlk6 S w x ∈ lay.aux`.
-/

set_option autoImplicit false

namespace Lvm6.Node.Dep

open Lvm Lvm.Loop Lvm.Typed Lvm.BitsTab Lvm.Bits Lvm.QSig
open Lvm6.Q (opensP17 bitBase6 ansLane6 qsig6)

/-- No bus placement (typed rows read none). -/
def noPl : ℕ → Bool × ℕ := fun _ ↦ (false, 0)

/-- The draws of opening `k`'s position group. -/
def nDraws (k : ℕ) : ℕ := ((opensP17.getD k default).t + (opensP17.getD k default).per - 1) /
  (opensP17.getD k default).per

/-- Answer bits opening `k`'s positions use per draw. -/
def usedBits (k : ℕ) : ℕ := (opensP17.getD k default).per * (opensP17.getD k default).h

/-- The output cell of answer bit `n` of draw `q` of opening `k`: `Q_link`'s position-bit cell, or scratch. -/
def posOut (k q n : ℕ) : ℕ :=
  let o := opensP17.getD k default
  if n < usedBits k then bitBase6 opensP17 lay6 k + o.h * (q * o.per + n / o.h) + n % o.h
  else lay6.bb + 5120 + 256 * k + q * (128 - usedBits k) + (n - usedBits k)

/-- **`Q_link`'s position bits, opening `k`, answer lane `l`**: one row per draw. -/
def posSpec6 (k l : ℕ) : BSpec :=
  ⟨Nat.log2 (nDraws k) + 1, nDraws k, (List.range 64).map BOut.bit, true,
    fun q ↦ sbC + ansLane6 P6 ((opensP17.getD k default).pd0 + q) + l,
    fun z q ↦ posOut k q (64 * l + z), noPl, 0, by intros; omega⟩

/-- The position classes: openings `0 … 4`, lanes `0, 1`. -/
def posSpecs6 : List BSpec := (List.range opensP17.length).flatMap fun k ↦ [posSpec6 k 0, posSpec6 k 1]

/-- **`Q_sig`'s classes** at its outputs (pointer `pS lay ⟨nK, 0⟩`). -/
def sigSpecs6 (lay : Lay) : List BSpec :=
  let q := qsig6 sigI sigIl sbC (pS lay ⟨nK, 0⟩)
  SigBits.sigSpecs sigI q.1.1 (fun _ ↦ noPl) ++ sigSpecsC sigIl sigIl.ys q.1.2.pa (fun _ ↦ noPl)

/-- **All `BITS` classes of the deployed circuit.** -/
def bitsSpecs6 (lay : Lay) : List BSpec := sigSpecs6 lay ++ posSpecs6

/-! ## The guard's Bool -/

/-- Two block lists are equal (heights and rows). -/
def ablksEqB : List ABlk → List ABlk → Bool
  | [], [] => true
  | a :: as, b :: bs => decide (a.l = b.l) && decide (a.rows.map ARow.ops = b.rows.map ARow.ops) && ablksEqB as bs
  | _, _ => false

theorem ablksEqB_sound : ∀ {as bs : List ABlk}, ablksEqB as bs = true → as = bs
  | [], [], _ => rfl
  | a :: as, b :: bs, h => by
    simp only [ablksEqB, Bool.and_eq_true, decide_eq_true_eq] at h
    rw [ablk_eq h.1.1 h.1.2, ablksEqB_sound h.2]
  | [], _ :: _, h => by simp [ablksEqB] at h
  | _ :: _, [], h => by simp [ablksEqB] at h

/-- The rows of every class, in order (`S`, `x`). -/
def bitsRows6 (lay : Lay) : List (BSpec × ℕ) := (bitsSpecs6 lay).flatMap fun S ↦ (List.range S.n).map fun x ↦ (S, x)

/-- The aux blocks `bs` start with the rows `rs`' two blocks each, in order (the bit base read off each booleanity
block). One walk over both lists. -/
def pairsB : List ABlk → List (BSpec × ℕ) → Bool
  | _, [] => true
  | b :: c :: bs, (S, x) :: rs =>
    ablksEqB [b, c] [boolBlk6 S (blkBw b) x, outBlk6 S (blkBw b) x] && pairsB bs rs
  | _, _ :: _ => false

theorem pairsB_sound : ∀ {bs : List ABlk} {rs : List (BSpec × ℕ)}, pairsB bs rs = true →
    ∀ S x, (S, x) ∈ rs → ∃ w, boolBlk6 S w x ∈ bs ∧ outBlk6 S w x ∈ bs
  | _, [], _, _, _, hm => absurd hm (List.not_mem_nil)
  | [], _ :: _, h, _, _, _ => by simp [pairsB] at h
  | [_], _ :: _, h, _, _, _ => by simp [pairsB] at h
  | b :: c :: bs, (S', x') :: rs, h, S, x, hm => by
    simp only [pairsB, Bool.and_eq_true] at h
    rcases List.mem_cons.mp hm with he | hm'
    · obtain ⟨rfl, rfl⟩ := Prod.mk.inj he
      have e := ablksEqB_sound h.1
      simp only [List.cons.injEq, and_true] at e
      exact ⟨blkBw b, e.1 ▸ List.mem_cons_self .., e.2 ▸ List.mem_cons_of_mem _ (List.mem_cons_self ..)⟩
    · obtain ⟨w, hb, ho⟩ := pairsB_sound h.2 S x hm'
      exact ⟨w, List.mem_cons_of_mem _ (List.mem_cons_of_mem _ hb), List.mem_cons_of_mem _ (List.mem_cons_of_mem _ ho)⟩

/-- **The `BITS` rows are in the layout**: after the PoW blocks, the aux blocks are the rows of `bitsRows6`, two a
row (booleanity, then word/output), in order (G0: the rows built once, one walk). -/
def bitsAuxInB (lay : Lay) : Bool := pairsB (lay.aux.drop powAns.length) (bitsRows6 lay)

theorem bitsAuxInB_sound {lay : Lay} (h : bitsAuxInB lay = true) :
    ∀ S ∈ bitsSpecs6 lay, ∀ x < S.n, ∃ w, boolBlk6 S w x ∈ lay.aux ∧ outBlk6 S w x ∈ lay.aux := by
  intro S hS x hx
  have hm : (S, x) ∈ bitsRows6 lay :=
    List.mem_flatMap.mpr ⟨S, hS, List.mem_map.mpr ⟨x, List.mem_range.mpr hx, rfl⟩⟩
  obtain ⟨w, hb, ho⟩ := pairsB_sound h S x hm
  exact ⟨w, List.mem_of_mem_drop hb, List.mem_of_mem_drop ho⟩

/-! ## CC's region claims (RV4 B1) -/

/-- **`RegAff` at run time** (CLG's `RegAff`: the source's regions are `regs`, aligned, `w` affine onto the targets). -/
def regAffB (Ti : Lvm6.Ty.TInst6) (s : YSrc) (w : ℕ → ℕ) (regs : List (YReg × ℕ)) : Bool :=
  decide ((Ti.lay.yregs.filter fun r ↦ r.src == s) = regs.map Prod.fst) &&
    regs.all fun p ↦ decide (p.1.base % 2 ^ p.1.log = 0) && decide (p.2 % 2 ^ p.1.log = 0) &&
      (List.range (2 ^ p.1.log)).all fun i ↦ decide (w (p.1.base + i) = p.2 + i)

theorem regAffB_sound {Ti : Lvm6.Ty.TInst6} {s : YSrc} {w : ℕ → ℕ} {regs : List (YReg × ℕ)}
    (h : regAffB Ti s w regs = true) : Lvm6.QC.RegAff Ti s w regs := by
  simp only [regAffB, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true, List.mem_range] at h
  exact ⟨h.1, fun p hp ↦ ⟨(h.2 p hp).1.1, (h.2 p hp).1.2, (h.2 p hp).2⟩⟩

/-- **CC's claims 48 and 49 read the deployed layout's regions**: `RegAff` for `com` and `KS` at `regsOf`. -/
def ccRegsB (Ti : Lvm6.Ty.TInst6) : Bool :=
  regAffB Ti .com Ti.comW (regsOf Ti.lay .com) && regAffB Ti .ks Ti.ksW (regsOf Ti.lay .ks)

/-- **Claim 47's base is the layout's `σ′` region** (with `tyLayOkB`'s form of the `σ′` region). -/
theorem sigBgOf_eq {lay : Lay} {bg l : ℕ} (h : (lay.yregs.filter fun r ↦ r.src == .sigma) = [⟨bg, l, .sigma⟩]) :
    sigBgOf lay = bg := by
  simp [sigBgOf, h]

/-- **The node layout's facts with F2 and B1** (`nodeLayB`, the `BITS` classes, CC's regions). -/
def nodeLayB2 (Ti : Lvm6.Ty.TInst6) : Bool := nodeLayB Ti && bitsAuxInB Ti.lay && ccRegsB Ti

end Lvm6.Node.Dep

namespace Lvm6.Node.Dep

/-- **`sigI.sl` is dead in v6**: `qsig6` is the header copy and `qsigSC` (`qsigNoSl`, no `σ_leaf'` loop `slTpl`), so
the program does not read the season-1 field `sl` (σ_leaf lives in `STREAM`/`σ`, FORMAT6 §2, §8). -/
theorem qsig6_sl (s : ℕ) : Lvm6.Q.qsig6 { sigI with sl := s } sigIl sbC = Lvm6.Q.qsig6 sigI sigIl sbC := rfl

end Lvm6.Node.Dep
