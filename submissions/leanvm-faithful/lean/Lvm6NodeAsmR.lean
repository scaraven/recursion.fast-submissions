-- New for lvm6 (WP NODE5b, RV4 M2). `ReaddOk` of the deployed instance: every `readd` instance of `Ti.Q` reads its
-- cell. A static (QLT) read by the layout's alias target (season 1's `readdOk_of_chkL`, static branch); a cap read by
-- the mini-bus (MBT's `mbRead_seeded6`, the bus half) and the stream cells (the seed half). The run-time part is one
-- pass over the program's template rows (`readdChk6B`), per `readd` row its iterations; no `Φ_Q` entry is expanded.
import Lvm6NodeMbR
import Lvm6NodeAsmChk
import Lvm6NodeTi
import LvmE2TWiring

/-!
# `ReaddOk` from the mini-bus and the alias targets (WP NODE5b, RV4 M2)

* **`readdChk6B Ti`** (run time): for every `readd` template row of `Ti.Q` (one pass over the blocks' templates), at
  every iteration `jf`:
  - the layout aliases the row (`CSrc.alias tgt`): target `e = tgt[jf]` an existing cell, `e` and the result cell
    no constant, the same word, the address cell the constant `g^e` or QLT's address row `g^l · g^(e−l)`
    (`aliasInstB`, season 1's `aliasOkB` on `lay.cst?`/`lay.wordK`);
  - otherwise a cap read: for some read table `k` of `Ti.mbT` (index: the number of seeds plus `k`), `jf < 2^τ_k`, the address and
    result cells are committed words mapped to its address and value columns plus `jf` (`capInstB`).
* **`readdOk_of_chk6`** (generic in the instance, the tables' words, the pair): the check, the bus fact (every cap
  read row reads a seed row: `mbRead_seeded6`'s conclusion), the seed fact (stream cell `sb + j` holds stack word
  `streamIdx j`) and the non-`readd` rows give `ReaddOk Ti.Q (memOf Ti.lay (Ti.zOf L pw qm qr))`.
* **`nonReadd_of_tgoodE`**: the non-`readd` rows hold on a good pair's memory without `ReaddOk`
  (`rowDef_of_wiringX`).
-/

set_option autoImplicit false

namespace Lvm6.Node.Asm

open Lvm Lvm.Loop Lvm.Loop.Build Lvm.Typed LeanVM.Protocol
open Lvm6.Ty (TInst6 TGoodE NoE3 wiringRelE_iff)
open Lvm6.Ty.TInst6 (comCell)
open Lvm6.Node.Mb

/-! ## Soundness -/

/-- **The non-`readd` rows hold** on a memory. -/
def NonReaddHolds (Q : Program) (M : Mem) : Prop :=
  ∀ i ∈ Q.insts, (∀ lo m, i.row.op ≠ .readd lo m) → Q.RowDef M i

/-- `zipIdx`'s `all` at an index. -/
theorem all_zipIdx6 {α : Type} {l : List α} {f : α × ℕ → Bool} (h : l.zipIdx.all f = true) {i : ℕ}
    (hi : i < l.length) : f (l[i], i) = true :=
  List.all_eq_true.mp h _ (List.mk_mem_zipIdx_iff_getElem?.mpr (List.getElem?_eq_getElem hi))

theorem memOf_k6 (lay : Lay) (z : ℕ → FK) (n : ℕ) : (memOf lay z).k n = (lay.cst? n).getD (z (lay.wordK n)) := rfl

theorem memOf_cst6 (lay : Lay) (z : ℕ → FK) {n : ℕ} {v : FK} (h : lay.cst? n = some v) : (memOf lay z).k n = v := by
  rw [memOf_k6, h, Option.getD_some]

theorem cells_ge_nInK6 (Q : Program) : Q.nInK ≤ Q.cells .K := by
  simp only [Program.cells, Program.start, Program.nIn]; omega

section
variable (Ti : TInst6) (L : Lvm.M3.Lay) (pw : ℕ → FK) (qm : Column L.nuMain) (qr : Column L.nuRec)

/-- A committed cell's value is its word's `C_main` cell. -/
theorem comVal {n : ℕ} (hc : Ti.lay.cst? n = none) (hs : Ti.src? (Ti.lay.wordK n) = some .com) :
    (memOf Ti.lay (Ti.zOf L pw qm qr)).k n = FK.ofBF64 (comCell L qm qr false (Ti.comW (Ti.lay.wordK n))) := by
  rw [memOf_k6, hc, Option.getD_none]
  unfold TInst6.zOf
  rw [hs]

/-- **`ReaddOk` from the check** (generic in the instance, the read tables' words and the pair): with the cap read
rows reading seeds (`hbus`, `mbRead_seeded6`'s conclusion), the seeds' cells holding their stack words (`hseed`) and
the non-`readd` rows (`hlin`), every `readd` instance has its `RowDef`. -/
theorem readdOk_of_chk6 (P : MbPar) (wa wv : ℕ → ℕ) (hT : Ti.mbT = mbTOf6 P wa wv) (hchk : readdChk6B Ti = true)
    (hbus : ∀ k (hk : k < capTaus6.length), ∀ x < 2 ^ capTaus6[k],
      ∃ i, ∃ hi : i < seedBlocks6.length, ∃ x' < 2 ^ mbBlk6,
        comCell L qm qr false (alignW P capTaus6[k] (wa k) + x) =
          FK.toBF64 (FK.x ^ (P.sb + 2 ^ mbBlk6 * seedBlocks6[i] + 1 * x')) ∧
        comCell L qm qr false (alignW P capTaus6[k] (wv k) + x) =
          comCell L qm qr false (Lvm6.QD.streamIdx (2 ^ mbBlk6 * seedBlocks6[i]) + x'))
    (hseed : ∀ i (hi : i < seedBlocks6.length), ∀ x' < 2 ^ mbBlk6,
      P.sb + 2 ^ mbBlk6 * seedBlocks6[i] + 1 * x' < Ti.Q.cells .K ∧
      (memOf Ti.lay (Ti.zOf L pw qm qr)).k (P.sb + 2 ^ mbBlk6 * seedBlocks6[i] + 1 * x') =
        FK.ofBF64 (comCell L qm qr false (Lvm6.QD.streamIdx (2 ^ mbBlk6 * seedBlocks6[i]) + x')))
    (hlin : NonReaddHolds Ti.Q (memOf Ti.lay (Ti.zOf L pw qm qr))) :
    ReaddOk Ti.Q (memOf Ti.lay (Ti.zOf L pw qm qr)) := by
  intro i hi lo m hop
  obtain ⟨b, hb, jf, hjf, t, ht, rfl⟩ := (Ti.Q.mem_insts i).mp hi
  set M := memOf Ti.lay (Ti.zOf L pw qm qr) with hMdef
  have hB : Ti.Q.blk b = Ti.Q.blocks[b] := by simp [Program.blk, List.getD_eq_getElem?_getD, hb]
  have hrow : (Ti.Q.blk b).tpl.getD t default = (Ti.Q.blk b).tpl[t] := by
    simp [List.getD_eq_getElem?_getD, ht]
  have h1 := all_zipIdx6 hchk hb
  rw [← hB] at h1
  have h2 := all_zipIdx6 h1 ht
  have hop' : ((Ti.Q.blk b).tpl[t]).op = .readd lo m := by rw [← hrow]; exact hop
  simp only [rdRowB, hop'] at h2
  simp only [Bool.and_eq_true, beq_iff_eq] at h2
  obtain ⟨⟨hty, haty⟩, hj⟩ := h2
  set A := ((Ti.Q.blk b).tpl[t]).args.getD 0 default with hA
  have harg : (M.arg (Ti.Q.inst b jf t) 0).c₀ = M.k (A.at (unflat (Ti.Q.blk b).dims jf)) := by
    simp only [Mem.arg, Inst.arg, Program.inst, hrow, ← hA, haty, Mem.rd]; rfl
  have hres : M.res (Ti.Q.inst b jf t) = FE.ofK (M.k (Ti.Q.start .K b + (Ti.Q.blk b).tw .K * jf + (Ti.Q.blk b).rank .K t)) := by
    simp only [Mem.res, Program.inst, hrow, hty, Inst.clock, Mem.rd]
  unfold Program.RowDef
  simp only [Program.inst, hrow, hop', hty]
  simp only [Program.inst, hrow] at harg hres
  revert hj
  split
  · -- a static read: the layout's alias target
    rename_i tgt _
    intro hj
    simp only [Bool.and_eq_true, decide_eq_true_eq] at hj
    obtain ⟨hlen, hall⟩ := hj
    have hjt : jf < tgt.length := by rw [hlen]; exact hjf
    have hx := all_zipIdx6 hall hjt
    simp only [aliasInstB, Bool.and_eq_true, Bool.or_eq_true, beq_iff_eq, decide_eq_true_eq,
      Option.isNone_iff_eq_none] at hx
    obtain ⟨⟨⟨⟨he, hce⟩, hcc⟩, hw⟩, hadr⟩ := hx
    refine ⟨tgt[jf], he, ?_, ?_⟩
    · rw [harg]
      rcases hadr with hc | hl
      · rw [memOf_cst6 _ _ hc]; rfl
      · -- QLT's address row: `a = g^l·α`, `α = g^(e − l)` a constant
        simp only [linOk6B, List.any_eq_true] at hl
        obtain ⟨⟨r', t'⟩, hmem, hx⟩ := hl
        have hr' := List.mk_mem_zipIdx_iff_getElem?.mp hmem
        have ht' : t' < (Ti.Q.blk b).tpl.length := (List.getElem?_eq_some_iff.mp hr').1
        have hrw : (Ti.Q.blk b).tpl.getD t' default = r' := by
          simp [List.getD_eq_getElem?_getD, hr']
        rcases hop1 : r'.op with _ | ⟨k, k'⟩ | _ | _ | _ | ⟨lo', m'⟩ <;>
          simp only [hop1, Bool.false_eq_true] at hx
        rcases hargs : r'.args with _ | ⟨α₀, _ | ⟨α₁, _ | ⟨_, _⟩⟩⟩ <;>
          simp only [hargs, Bool.false_eq_true] at hx
        simp only [Bool.and_eq_true, beq_iff_eq, List.any_eq_true, List.mem_cons, List.mem_nil_iff,
          or_false, decide_eq_true_eq] at hx
        obtain ⟨⟨⟨⟨⟨⟨hty', hk'⟩, h0⟩, h1⟩, hα⟩, hck⟩, l, -, ⟨hle, hkl⟩, hcα⟩ := hx
        have hi' : Ti.Q.inst b jf t' ∈ Ti.Q.insts := (Ti.Q.mem_insts _).mpr ⟨b, hb, jf, hjf, t', ht', rfl⟩
        have hop2 : ∀ lo m, (Ti.Q.inst b jf t').row.op ≠ .readd lo m := by
          intro lo m h; simp only [Program.inst, hrw, hop1] at h; cases h
        have hR := hlin _ hi' hop2
        unfold Program.RowDef at hR
        simp only [Program.inst, hrw, hop1, Mem.res, Mem.arg, Inst.arg, hargs, hty', Inst.clock, hck,
          List.getD_cons_zero, List.getD_cons_succ, h0, h1, Mem.rd, hα, hk'] at hR
        have hg : M.k (α₁.at (unflat (Ti.Q.blk b).dims jf)) = Build.gpow (tgt[jf] - l) := by
          rw [← hα]; exact memOf_cst6 _ _ hcα
        have hg0 : M.k (α₀.at (unflat (Ti.Q.blk b).dims jf)) = Build.gpow (tgt[jf] - l) := memOf_cst6 _ _ hcα
        rw [hg, hkl, ← Build.ofK_mul, ← Build.ofK_add, ← Build.ofK_add] at hR
        have hv := Build.ofK_inj hR
        try rw [hg0] at hv
        rw [gpow_scale l (tgt[jf] - l), Nat.sub_add_cancel hle] at hv
        exact hv.symm
    · rw [hres]
      show FE.ofK (M.k _) = FE.ofK (M.k _)
      rw [memOf_k6, memOf_k6, hcc, hce, hw]
  · -- a cap read: the mini-bus
    intro hj
    simp only [List.all_eq_true, List.mem_range] at hj
    have hc := hj jf hjf
    simp only [capInstB, Bool.and_eq_true, List.any_eq_true, List.mem_range, decide_eq_true_eq,
      Option.isNone_iff_eq_none] at hc
    obtain ⟨⟨⟨⟨hca, hcc⟩, hsa⟩, hsc⟩, k, hk, hk'⟩ := hc
    rw [hT, mbTOf6_get_read P wa wv hk] at hk'
    simp only [QTyped.readTab, Bool.and_eq_true, decide_eq_true_eq] at hk'
    obtain ⟨hjτ, ha, hcv⟩ := hk'
    have hjτ' : jf < 2 ^ capTaus6[k] := by first | exact of_decide_eq_true hjτ | simpa using hjτ
    have ha' : Ti.comW (Ti.lay.wordK (A.at (unflat (Ti.Q.blk b).dims jf))) = alignW P capTaus6[k] (wa k) + jf := by
      first | exact of_decide_eq_true ha | simpa using ha | exact ha
    have hcv' : Ti.comW (Ti.lay.wordK (Ti.Q.start .K b + (Ti.Q.blk b).tw .K * jf + (Ti.Q.blk b).rank .K t)) =
        alignW P capTaus6[k] (wv k) + jf := by
      first | exact of_decide_eq_true hcv | simpa using hcv | exact hcv
    obtain ⟨q, hq, x', hx', hAd, hV⟩ := hbus k hk jf hjτ'
    obtain ⟨hlt, hse⟩ := hseed q hq x' hx'
    refine ⟨_, hlt, ?_, ?_⟩
    · rw [harg, comVal Ti L pw qm qr hca hsa, ha', hAd]
      -- the round trip by its lemma (KDN: `rfl` made the kernel unfold `FK.x ^ (… seedBlocks6[q] …)`)
      exact (FK.ofBF64_toBF64 _).symm
    · rw [hres]
      show FE.ofK (M.k _) = FE.ofK (M.k _)
      rw [comVal Ti L pw qm qr hcc hsc, hcv', hV, hse]

end

/-- **The non-`readd` rows hold on a good pair's memory** (the wiring relation without `ReaddOk`). -/
theorem nonReadd_of_tgoodE (Ti : TInst6) (L : Lvm.M3.Lay) (hτ : ∀ t ∈ Ti.mbT, t.τ ≤ L.μ) (pw : ℕ → FK)
    (p : Column L.nuMain × Column L.nuRec) (hwf : Ti.Q.wf = true) (htw : Ti.Q.twinsOk = true)
    (hE3 : NoE3 Ti.Q Ti.lay) (hok : Ti.Ok) (hg : TGoodE Ti L hτ pw p) :
    NonReaddHolds Ti.Q (memOf Ti.lay (Ti.zOf L pw p.1 p.2)) := by
  have hone : Ti.zOf L pw p.1 p.2 Ti.lay.one = 1 := by
    unfold TInst6.zOf
    rw [hok.2]
  have hX := (wiringRelT_iff Ti.Q Ti.lay hok.1 _).mp ((wiringRelE_iff hok.1 hE3).mp hg.1)
  intro i hi hnr
  exact (rowDef_of_wiringX Ti.Q Ti.lay _ hwf htw hok.1 hone hX hi fun lo m h ↦ absurd h (hnr lo m)).1

end Lvm6.Node.Asm
