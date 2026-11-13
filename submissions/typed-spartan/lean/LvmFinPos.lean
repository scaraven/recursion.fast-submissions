-- New for lvm2 (roll 8 = B1, wave L; moved by L-D for the lead): FIN-BV's position facts that the typed certificate
-- reads, out of `LvmFinBVPos` and `LvmFinDec` (unchanged statements and proofs, a pure move), so that a typed module
-- imports them without the bus path: the fields of a position (`ubit_fld` … `hi_mem`), `PosLanes` and `posOk_of`
-- (`LvmFinBVPos`), and `PosLanes` at `P20` (`posLanes_of` … `posLanesB20`, `posLanesR20`, `posLanesM20`, `LvmFinDec`).
import LvmQAsmLay
import LvmQLinkBits
import LvmQAsmHarPos
import LvmXOutSeg
import LvmNodeSoundTr
import LvmQAsmFactsL
import LvmQAsmArith2

/-!
# FIN-BV's position facts

* From `LvmFinBVPos`: `ubit_fld`, `ubit_laneK`, `ubit_toUInt64`, `posL_testBit`, **`fields_posL`**, `lo_mem`,
  `hi_mem`; **`PosLanes`**, **`posOk_of`**.
* From `LvmFinDec`: `lens_run`, `ansLane_run`, `PosLanesR`, **`posLanes_of`**, the extractor-block decision
  (`PosLanesK`, `posLanesKB`, `posLanesK_of_B`), **`posLanesB20`** (`decide +kernel`, 6.5 s), **`posLanesR20`**,
  **`posLanesM20`**.
-/

set_option autoImplicit false

namespace Lvm.Fin

section BVPos

open RecursionFast Lvm Lvm.T Lvm.ASM Lvm.Replay Lvm.Loop Lvm.Loop.Build Lvm.QLink Lvm.QSig Lvm.M3
open Lvm.SigBits Lvm.BitsTab Lvm.Bits Lvm.NS Lvm.QAsm Lvm.Har LeanVM.Protocol

/-! ## Bits of a field and of a position -/

/-- Bit `i` of a `fld z₀ m d` output: bit `z₀ + (i − d)` of the word for `d ≤ i < d + m`. -/
theorem ubit_fld {z₀ m d : ℕ} (h : z₀ < 64 ∧ 1 ≤ m ∧ m + d ≤ 64) (w : UInt64) (i : ℕ) :
    ubit ((BOut.fld z₀ m d).word w) i =
      (decide (d ≤ i) && decide (i < d + m) && ubit w (z₀ + (i - d))) := by
  obtain ⟨h0, h1, h2⟩ := h
  by_cases hi : i < 64
  · simp only [BOut.word, ubit_shr _ (show 64 - m - d < 64 by omega), ubit_shl _ (show 64 - m < 64 by omega),
      ubit_shr _ h0]
    by_cases c1 : d ≤ i
    · by_cases c2 : i < d + m
      · rw [show z₀ + (64 - m - d + i - (64 - m)) = z₀ + (i - d) by omega]
        simp [c1, c2, show 64 - m - d + i < 64 by omega, show 64 - m ≤ 64 - m - d + i by omega]
      · simp [c2, show ¬ (64 - m - d + i < 64) by omega]
    · simp [c1, show ¬ (64 - m ≤ 64 - m - d + i) by omega]
  · rw [ubit_ge _ (by omega)]
    simp [show ¬ (i < d + m) by omega]

theorem ubit_laneK (ws : List Word) (j z : ℕ) : ubit (laneK ws j).val z = (lw ws j).testBit z := rfl

theorem ubit_toUInt64 (n : ℕ) {b : ℕ} (hb : b < 64) : ubit n.toUInt64 b = n.testBit b := by
  show (n.toUInt64).toNat.testBit b = _
  rw [Nat.toUInt64_eq, UInt64.toNat_ofNat', Nat.testBit_mod_two_pow]
  simp [hb]

/-- Bit `b` of a position: bit `s + b` of the answer's lanes, for `b < h`. -/
theorem posL_testBit (p : Params) (ws : List Word) (e s h : ℕ) (hs : s + h ≤ 192) (b : ℕ) :
    (posL p ws e s h).testBit b =
      (decide (b < h) && (lw ws (ansLane p e + (s + b) / 64)).testBit ((s + b) % 64)) := by
  rw [posL_eq p ws (lw ws (ansLane p e) + 2 ^ 64 * lw ws (ansLane p e + 1) + 2 ^ 128 * lw ws (ansLane p e + 2))
    e s h (fun n _ h2 => by rw [testBit_limbs (lw ws) (Har.lw_lt ws) _ n (by omega)]; rfl)]
  rw [Nat.testBit_mod_two_pow, Nat.testBit_shiftRight]
  by_cases hb : b < h
  · rw [testBit_limbs (lw ws) (Har.lw_lt ws) _ (s + b) (by omega)]
  · simp [hb]

/-- **A position's two fields add up to `posL`** (A20: `lo` holds bits `[0, m₁)`, `hi` bits `[m₁, H)`;
`K` addition is `xor` of disjoint bit ranges). -/
theorem fields_posL (p : Params) (ws : List Word) (e : ℕ) {H i : ℕ} (hH2 : 2 ≤ H) (hH : H ≤ 64)
    (h192 : i * H + H ≤ 192) :
    w64 ((BOut.fld (fields H i).1.2.1 (fields H i).1.2.2.1 (fields H i).1.2.2.2).word
        (laneK ws (ansLane p e + (fields H i).1.1)).val) +
      w64 ((BOut.fld (fields H i).2.2.1 (fields H i).2.2.2.1 (fields H i).2.2.2.2).word
        (laneK ws (ansLane p e + (fields H i).2.1)).val) =
      kOf (posL p ws e (i * H) H) := by
  simp only [fields]
  generalize hs : i * H = s at h192 ⊢
  generalize hm : (if s / 64 = (s + H - 1) / 64 then H - 1 else 64 - s % 64) = m₁
  have hm' : (s / 64 = (s + H - 1) / 64 ∧ m₁ = H - 1) ∨ (s / 64 ≠ (s + H - 1) / 64 ∧ m₁ = 64 - s % 64) := by
    by_cases hc : s / 64 = (s + H - 1) / 64
    · rw [if_pos hc] at hm; exact Or.inl ⟨hc, hm.symm⟩
    · rw [if_neg hc] at hm; exact Or.inr ⟨hc, hm.symm⟩
  have hv1 : s % 64 < 64 ∧ 1 ≤ m₁ ∧ m₁ + 0 ≤ 64 := by omega
  have hv2 : (s + m₁) % 64 < 64 ∧ 1 ≤ H - m₁ ∧ H - m₁ + m₁ ≤ 64 := by omega
  show (⟨_ ^^^ _⟩ : FK) = ⟨(posL p ws e s H).toUInt64⟩
  congr 1
  apply u64_ext
  intro b hb
  rw [ubit_xor, ubit_fld hv1, ubit_fld hv2, ubit_toUInt64 _ hb, posL_testBit p ws e s H h192, ubit_laneK,
    ubit_laneK]
  by_cases b1 : b < m₁
  · rw [show (s + b) / 64 = s / 64 by omega, show (s + b) % 64 = s % 64 + (b - 0) by omega]
    simp [b1, show ¬ m₁ ≤ b by omega, show b < H by omega]
  · by_cases b2 : b < H
    · rw [show (s + b) / 64 = (s + m₁) / 64 by omega, show (s + b) % 64 = (s + m₁) % 64 + (b - m₁) by omega]
      simp [b1, b2, show m₁ ≤ b by omega, show b < m₁ + (H - m₁) by omega]
    · simp [b1, b2, show ¬ b < m₁ + (H - m₁) by omega]

/-! ## The position classes' field outputs -/

theorem lo_mem (H : ℕ) {i : ℕ} (hi : i < 8) :
    ((BOut.fld (fields H i).1.2.1 (fields H i).1.2.2.1 (fields H i).1.2.2.2), 1, i) ∈
      laneOuts H (fields H i).1.1 := by
  unfold laneOuts
  refine List.mem_append_right _ (List.mem_flatMap.mpr ⟨i, List.mem_range.mpr hi, ?_⟩)
  simp

theorem hi_mem (H : ℕ) {i : ℕ} (hi : i < 8) :
    ((BOut.fld (fields H i).2.2.1 (fields H i).2.2.2.1 (fields H i).2.2.2.2), 2, i) ∈
      laneOuts H (fields H i).2.1 := by
  unfold laneOuts
  refine List.mem_append_right _ (List.mem_flatMap.mpr ⟨i, List.mem_range.mpr hi, ?_⟩)
  simp

/-! ## `PosOk` -/

/-- **`F`'s positions lanes and Q_link's openings** (a static fact of the schedule and `F`'s layout,
decidable on the frozen parameter set): level `i` of `Ls` (positions lanes from `V`) is opening `k0 + i`
of the plan, of height at most 64, and `F` reads that opening's positions answers (72 bytes each) at the
answers' lanes. -/
def PosLanes (p : Params) (g : ℕ) (ood : Bool) (Ls : List Level) (V k0 : ℕ) : Prop :=
  ∀ i < Ls.length, k0 + i < (opens p).length ∧ ((opens p).getD (k0 + i) default).L = Ls.getD i default ∧
    (Ls.getD i default).height ≤ 64 ∧
    ∀ x < nAns ((opens p).getD (k0 + i) default),
      8 * (posLanes g ood Ls V).getD i 0 + 72 * x + 40 = 8 * ansLane p (((opens p).getD (k0 + i) default).pe + x)

/-- **`PosOk` from the position cells' values** (`F`'s positions are `posL`, `qsAt_posL`). -/
theorem posOk_of (C : SCfg) (k0 : ℕ) (hpb : ∀ i, C.pb i = posBase cfg20 (k0 + i)) {Ls : List Level} {V : ℕ}
    (hPL : PosLanes P20 C.g C.ood Ls V k0) {M : Mem} {ws : List Word} (hS : StreamOk P20) (hL : LaneLink P20 ws)
    (hQ : QOk P20 (lay cfg20))
    (hcell : ∀ k < (opens P20).length, ((opens P20).getD k default).L.height ≤ 64 →
      ∀ j < ((opens P20).getD k default).L.t, M.k (nK cfg20 + posIdx P20 k j) =
        kOf (posL P20 ws (((opens P20).getD k default).pe + j / 8) (j % 8 * ((opens P20).getD k default).L.height)
          ((opens P20).getD k default).L.height)) :
    PosOk C M (traceBytesB (decode P20 ws)) 0 Ls V := by
  intro i hi j hj
  obtain ⟨hk, hLeq, hH, hP⟩ := hPL i hi
  rw [traceBytesB_decode hS hL, hpb, Nat.zero_add]
  have hjt : j < ((opens P20).getD (k0 + i) default).L.t := by rw [hLeq]; exact hj
  have ho : (opens P20).getD (k0 + i) default ∈ opens P20 := by
    -- `Option.getD_some` by `rw`: left to defeq, the kernel evaluates `opens P20` (1.5 s)
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hk, Option.getD_some]; exact List.getElem_mem hk
  obtain ⟨h192, h1, hlt⟩ := open_pos_facts hS hQ ho hjt
  have hin := lanes_in hS h1 hlt
  have hab := ansLane_bound hS hL.size hlt
  have e1 : posBase cfg20 (k0 + i) + j = nK cfg20 + posIdx P20 (k0 + i) j := by
    have hp : cfg20.p = P20 := rfl
    simp only [posBase, posIdx, hp]; omega
  rw [e1, hcell _ hk (by rw [hLeq]; exact hH) j hjt]
  have hx : j / 8 < nAns ((opens P20).getD (k0 + i) default) := by unfold nAns; omega
  have hb : j % 8 * (Ls.getD i default).height + (Ls.getD i default).height ≤ 192 := by rw [← hLeq]; exact h192
  have hlen : 8 * ansLane P20 (((opens P20).getD (k0 + i) default).pe + j / 8) + 24 ≤ hashedLen P20 := by
    simp only [ansLane, if_neg (show ((opens P20).getD (k0 + i) default).pe + j / 8 ≠ 0 by omega)]; omega
  rw [qsAt_posL P20 ws _ _ _ j hj (hP _ hx) hb hlen (by omega), hLeq]
  rfl

end BVPos

section Dec

open Lvm Lvm.Loop Lvm.Loop.Build Lvm.Q1 Lvm.Har Lvm.Replay Lvm.QLink
open Lvm.QAsm (QCfg cfg20 nK bsB pwB clog2 nAns pbB)
open Lvm.X (Blk blocks lensB lanesOf lanes_eq lensB_opn)

/-! ## FIN-BV's `PosLanes` -/

/-- A run of 32-byte queries in the plan (entries `e … e + n − 1`). -/
theorem lens_run {p : Params} {e n : ℕ} (hr : ((lens p).drop e).take n = List.replicate n 32) {y : ℕ}
    (hy : y < n) : e + y < (plan p).length ∧ ((plan p).getD (e + y) default).len = 32 := by
  have hl : (((lens p).drop e).take n).length = n := by rw [hr, List.length_replicate]
  simp only [List.length_take, List.length_drop, lens_length] at hl
  refine ⟨by omega, ?_⟩
  rw [← lens_getD]
  have h1 : (((lens p).drop e).take n).getD y 0 = 32 := by
    rw [hr, List.getD_eq_getElem _ _ (by simpa using hy), List.getElem_replicate]
  rw [List.getD_eq_getElem?_getD, List.getElem?_take_of_lt hy, List.getElem?_drop] at h1
  rw [List.getD_eq_getElem?_getD]
  exact h1

/-- **Consecutive positions answers lie 9 lanes apart** when the entries after the first carry 32-byte
queries (`ansLane (i + 1) = ansLane i + 5 + len (i + 1) / 8`, QL's `eLane_succ`). -/
theorem ansLane_run {p : Params} (hS : streamOkL (plan p) = true) {e n : ℕ} (he : 1 ≤ e)
    (hr : ((lens p).drop (e + 1)).take n = List.replicate n 32) :
    ∀ x ≤ n, ansLane p (e + x) = ansLane p e + 9 * x
  | 0, _ => rfl
  | x + 1, hx => by
    have ih := ansLane_run hS he hr x (by omega)
    obtain ⟨h0, l1⟩ := lens_run hr (y := x) (by omega)
    have hs := eLane_succ hS (i := e + x) (by omega) (by omega)
    have a0 : ansLane p (e + x) = eLane p (e + x) + 1 + ((plan p).getD (e + x) default).len / 8 := by
      simp only [ansLane, ite_eq_right (show e + x ≠ 0 by omega)]
    have a1 : ansLane p (e + (x + 1)) = eLane p (e + x + 1) + 1 + 32 / 8 := by
      rw [← Nat.add_assoc, ← l1, show e + 1 + x = e + x + 1 by omega]
      simp only [ansLane, ite_eq_right (show e + x + 1 ≠ 0 by omega)]
    omega

/-- **`PosLanes` with one answer per opening**: level `i` is opening `k0 + i` (height at most 64), the
opening's entries after its first positions entry carry 32-byte queries, and its first answer is at the
level's positions lane. -/
def PosLanesR (p : Params) (g : ℕ) (ood : Bool) (Ls : List Level) (V k0 : ℕ) : Prop :=
  ∀ i < Ls.length, k0 + i < (opens p).length ∧ ((opens p).getD (k0 + i) default).L = Ls.getD i default ∧
    (Ls.getD i default).height ≤ 64 ∧ 1 ≤ ((opens p).getD (k0 + i) default).pe ∧
    ((lens p).drop (((opens p).getD (k0 + i) default).pe + 1)).take
        (nAns ((opens p).getD (k0 + i) default) - 1) =
      List.replicate (nAns ((opens p).getD (k0 + i) default) - 1) 32 ∧
    8 * (posLanes g ood Ls V).getD i 0 + 40 = 8 * ansLane p ((opens p).getD (k0 + i) default).pe

theorem posLanes_of {p : Params} {g : ℕ} {ood : Bool} (hS : streamOkL (plan p) = true) {Ls : List Level} {V k0 : ℕ}
    (h : PosLanesR p g ood Ls V k0) : PosLanes p g ood Ls V k0 := by
  intro i hi
  obtain ⟨h1, h2, h3, h4, h5, h6⟩ := h i hi
  refine ⟨h1, h2, h3, fun x hx => ?_⟩
  rw [ansLane_run hS h4 h5 x (by omega)]
  omega

/-! ### The plan's lengths through the extractor's blocks

The plan's entries after `q₀` are the extractor's blocks' queries (`lens_P20`, `lensL`); a block's
entries and lanes are numbers of the block (`bCnt`, `Blk.lanes`), so an opening's first answer lane
is a sum over the blocks before it (`ansLane_blk`) and its run of 32-byte queries a run of blocks
(`lens_run_blk`): the decision walks 1,415 blocks instead of 5,464 plan entries. -/

/-- A block's entries. -/
def bCnt : Blk → ℕ
  | .one _ _ => 1
  | .opn t _ path => t * (path + 1)

theorem length_lensB (b : Blk) : (lensB b).length = bCnt b := by
  cases b with
  | one c len => rfl
  | opn t row path =>
    rw [lensB_opn]; simp [bCnt, List.length_flatten, List.map_replicate, List.sum_replicate]

theorem length_flatMap_lensB (bs : List Blk) : (bs.flatMap lensB).length = (bs.map bCnt).sum := by
  rw [List.length_flatMap]
  exact congrArg List.sum (List.map_congr_left fun b _ => length_lensB b)

theorem lanesOf_flatMap : ∀ bs : List Blk, lanesOf (bs.flatMap lensB) = (bs.map Blk.lanes).sum
  | [] => rfl
  | b :: bs => by
    rw [List.flatMap_cons, List.map_cons, List.sum_cons, ← lanesOf_flatMap bs, lanes_eq]
    simp only [lanesOf, List.map_append, List.sum_append]

theorem slenS_lanesOf : ∀ {l : List ℕ}, (∀ x ∈ l, x % 8 = 0) → slenS l = 8 * lanesOf l
  | [], _ => rfl
  | a :: l, h => by
    have ha := h a (List.mem_cons_self ..)
    have ih := slenS_lanesOf (l := l) fun x hx => h x (List.mem_cons_of_mem _ hx)
    simp only [slenS, lanesOf, List.map_cons, List.sum_cons] at ih ⊢
    omega

theorem lens_blocks : lens P20 = 7 :: (blocks P20).flatMap lensB := Lvm.NS.lens_P20

theorem mod8_blocks {x : ℕ} (hx : x ∈ (blocks P20).flatMap lensB) : x % 8 = 0 := by
  have h := List.all_eq_true.mp Lvm.X.lensL_facts.2 x hx
  simp only [Bool.and_eq_true, beq_iff_eq] at h
  exact h.1

/-- The answer lane of the entry that starts block `j` (a single query), from the blocks before it. -/
def blkAns (bs : List Blk) (j : ℕ) : Option ℕ :=
  match bs[j]? with
  | some (.one _ len) => some (6 + ((bs.take j).map Blk.lanes).sum + 1 + len / 8)
  | _ => none

theorem blkAns_some {bs : List Blk} {j A : ℕ} (h : blkAns bs j = some A) :
    ∃ c len, bs[j]? = some (.one c len) ∧ A = 6 + ((bs.take j).map Blk.lanes).sum + 1 + len / 8 := by
  unfold blkAns at h
  split at h
  · rename_i c len hj
    exact ⟨c, len, hj, (Option.some.inj h).symm⟩
  · cases h

/-- The plan's lengths around block `j` (a single query of `len` bytes). -/
theorem lens_split {j : ℕ} {c : QClass} {len : ℕ} (hj : (blocks P20)[j]? = some (.one c len)) :
    lens P20 =
      7 :: (((blocks P20).take j).flatMap lensB ++ len :: ((blocks P20).drop (j + 1)).flatMap lensB) := by
  have hl : j < (blocks P20).length := by
    by_contra h; rw [List.getElem?_eq_none (by omega)] at hj; cases hj
  have hd : (blocks P20).drop j = .one c len :: (blocks P20).drop (j + 1) := by
    rw [List.drop_eq_getElem_cons hl]
    rw [List.getElem?_eq_getElem hl, Option.some.injEq] at hj
    rw [hj]
  have e : (blocks P20).flatMap lensB =
      ((blocks P20).take j).flatMap lensB ++ ((blocks P20).drop j).flatMap lensB := by
    rw [← List.flatMap_append, List.take_append_drop]
  rw [lens_blocks, e, hd, List.flatMap_cons]
  rfl

theorem drop_mid {α : Type} (a : α) (pre : List α) (x : α) (R : List α) :
    (a :: (pre ++ x :: R)).drop (1 + pre.length + 1) = R := by
  have e : a :: (pre ++ x :: R) = (a :: pre ++ [x]) ++ R := by simp
  rw [e, show 1 + pre.length + 1 = (a :: pre ++ [x]).length by simp; omega, List.drop_left]

/-- **The answer lane of a block's first entry** from the blocks before it. -/
theorem ansLane_blk {j A : ℕ} (h : blkAns (blocks P20) j = some A) :
    ansLane P20 (1 + (((blocks P20).take j).map bCnt).sum) = A := by
  obtain ⟨c, len, hj, rfl⟩ := blkAns_some h
  have hs := lens_split hj
  set pre := ((blocks P20).take j).flatMap lensB with hpre
  have hpl : pre.length = (((blocks P20).take j).map bCnt).sum := length_flatMap_lensB _
  have h8 : ∀ x ∈ pre, x % 8 = 0 := fun x hx => mod8_blocks (by
    rw [hpre] at hx
    obtain ⟨b, hb, hx⟩ := List.mem_flatMap.mp hx
    exact List.mem_flatMap.mpr ⟨b, List.mem_of_mem_take hb, hx⟩)
  have hL : ((plan P20).getD (1 + pre.length) default).len = len := by
    rw [← lens_getD, hs, Nat.add_comm 1, List.getD_cons_succ, List.getD_append_right _ _ _ _ le_rfl,
      Nat.sub_self, List.getD_cons_zero]
  have hT : (lens P20).take (1 + pre.length) = 7 :: pre := by
    rw [hs, Nat.add_comm 1, List.take_succ_cons, List.take_left' rfl]
  rw [← hpl]
  simp only [ansLane, ite_eq_right (show 1 + pre.length ≠ 0 by omega), eLane, bOff, hT, hL]
  rw [show slenS (7 :: pre) = 47 + slenS pre from rfl, slenS_lanesOf h8, hpre, lanesOf_flatMap]
  omega

theorem flatMap_rep32 :
    ∀ n : ℕ, (List.replicate n (Blk.one .fs 32)).flatMap lensB = List.replicate n 32
  | 0 => rfl
  | n + 1 => by rw [List.replicate_succ, List.flatMap_cons, flatMap_rep32 n]; rfl

/-- **The run after a block's first entry**: `n` single 32-byte queries. -/
theorem lens_run_blk {j n : ℕ} {c : QClass} {len : ℕ} (hj : (blocks P20)[j]? = some (.one c len))
    (hr : ((blocks P20).drop (j + 1)).take n = List.replicate n (.one .fs 32)) :
    ((lens P20).drop (1 + (((blocks P20).take j).map bCnt).sum + 1)).take n = List.replicate n 32 := by
  rw [lens_split hj, ← length_flatMap_lensB, drop_mid, ← List.take_append_drop n ((blocks P20).drop (j + 1)),
    hr, List.flatMap_append, flatMap_rep32, List.take_left' (by simp)]

/-- **`PosLanesR` at `P20` through the extractor's blocks** (`js`: the block of each opening's first
positions entry). -/
def PosLanesK (g : ℕ) (ood : Bool) (Ls : List Level) (V k0 : ℕ) (js : List ℕ) : Prop :=
  ∀ i < Ls.length, k0 + i < (opens P20).length ∧ ((opens P20).getD (k0 + i) default).L = Ls.getD i default ∧
    (Ls.getD i default).height ≤ 64 ∧
    1 + (((blocks P20).take (js.getD i 0)).map bCnt).sum = ((opens P20).getD (k0 + i) default).pe ∧
    ((blocks P20).drop (js.getD i 0 + 1)).take (nAns ((opens P20).getD (k0 + i) default) - 1) =
      List.replicate (nAns ((opens P20).getD (k0 + i) default) - 1) (.one .fs 32) ∧
    blkAns (blocks P20) (js.getD i 0) = some ((posLanes g ood Ls V).getD i 0 + 5)

theorem posLanesR_of_K {g : ℕ} {ood : Bool} {Ls : List Level} {V k0 : ℕ} {js : List ℕ} (h : PosLanesK g ood Ls V k0 js) :
    PosLanesR P20 g ood Ls V k0 := by
  intro i hi
  obtain ⟨h1, h2, h3, h4, h5, h6⟩ := h i hi
  obtain ⟨c, len, hj, -⟩ := blkAns_some h6
  refine ⟨h1, h2, h3, by omega, ?_, ?_⟩
  · rw [← h4]; exact lens_run_blk hj h5
  · rw [← h4, ansLane_blk h6]; omega

/-- Walk `j` blocks: the entries and the lanes before block `j`, and the blocks from `j`. -/
def blkWalk : List Blk → ℕ → ℕ → ℕ → ℕ × ℕ × List Blk
  | bs, 0, c, l => (c, l, bs)
  | [], _ + 1, c, l => (c, l, [])
  | b :: bs, j + 1, c, l => blkWalk bs j (c + bCnt b) (l + b.lanes)

theorem blkWalk_eq : ∀ (bs : List Blk) (j c l : ℕ),
    blkWalk bs j c l = (c + ((bs.take j).map bCnt).sum, l + ((bs.take j).map Blk.lanes).sum, bs.drop j)
  | bs, 0, c, l => by simp [blkWalk]
  | [], _ + 1, c, l => by simp [blkWalk]
  | b :: bs, j + 1, c, l => by
    rw [blkWalk, blkWalk_eq bs j]
    simp only [List.take_succ_cons, List.map_cons, List.sum_cons, List.drop_succ_cons, Prod.mk.injEq,
      and_true]
    exact ⟨by omega, by omega⟩

/-- `blkAns` from the walk: the block at `j` is a single query, its answer lane is `A`. -/
def blkAnsW (pre : ℕ) (rest : List Blk) (A : ℕ) : Bool :=
  match rest with
  | .one _ len :: _ => 6 + pre + 1 + len / 8 == A
  | _ => false

theorem blkAns_of_W {bs : List Blk} {j A : ℕ}
    (h : blkAnsW ((bs.take j).map Blk.lanes).sum (bs.drop j) A = true) : blkAns bs j = some A := by
  unfold blkAns
  rw [← List.head?_drop]
  unfold blkAnsW at h
  split at h
  · rename_i c len r heq
    rw [heq]
    simp only [List.head?_cons, beq_iff_eq] at h ⊢
    rw [h]
  · cases h

/-- **`PosLanesK` as one Boolean**: each level's first positions block walked to once (`blkWalk`). -/
def posLanesKB (g : ℕ) (ood : Bool) (Ls : List Level) (V k0 : ℕ) (js : List ℕ) : Bool :=
  (List.range Ls.length).all fun i =>
    let o := (opens P20).getD (k0 + i) default
    let w := blkWalk (blocks P20) (js.getD i 0) 0 0
    decide (k0 + i < (opens P20).length) && decide (o.L = Ls.getD i default) &&
    decide ((Ls.getD i default).height ≤ 64) && decide (1 + w.1 = o.pe) &&
    decide ((w.2.2.drop 1).take (nAns o - 1) = List.replicate (nAns o - 1) (.one .fs 32)) &&
    blkAnsW w.2.1 w.2.2 ((posLanes g ood Ls V).getD i 0 + 5)

theorem posLanesK_of_B {g : ℕ} {ood : Bool} {Ls : List Level} {V k0 : ℕ} {js : List ℕ} (h : posLanesKB g ood Ls V k0 js = true) :
    PosLanesK g ood Ls V k0 js := by
  intro i hi
  unfold posLanesKB at h
  have hi' := List.all_eq_true.mp h i (List.mem_range.mpr hi)
  simp only [Bool.and_eq_true, decide_eq_true_eq, blkWalk_eq, Nat.zero_add, List.drop_drop] at hi'
  obtain ⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩ := hi'
  exact ⟨h1, h2, h3, h4, h5, blkAns_of_W h6⟩

set_option maxRecDepth 200000 in
/-- The positions lanes of both openings (the blocks of their first positions entries: 1272, 1295; 1342, 1378,
1396), and the `s'` bits' cells below `nK cfg20` (one decision, `posLanesKB`). -/
theorem posLanesB20 : PosLanesK P20.grind P20.recOod P20.recLevels (openU P20 + 15) 0 [1272, 1295] ∧
    PosLanesK P20.grind P20.mainOod P20.mainLevels (stackEndL P20.grind P20.recOod P20.recLevels (openU P20 + 15) + 15) 2
      [1342, 1378, 1396] ∧
    bsB cfg20 + 256 ≤ nK cfg20 := by
  have h : (posLanesKB P20.grind P20.recOod P20.recLevels (openU P20 + 15) 0 [1272, 1295] &&
      posLanesKB P20.grind P20.mainOod P20.mainLevels (stackEndL P20.grind P20.recOod P20.recLevels (openU P20 + 15) + 15) 2
        [1342, 1378, 1396] &&
      decide (bsB cfg20 + 256 ≤ nK cfg20)) = true := by decide +kernel
  simp only [Bool.and_eq_true, decide_eq_true_eq] at h
  exact ⟨posLanesK_of_B h.1.1, posLanesK_of_B h.1.2, h.2⟩

/-- **FIN-BV's `PosLanes` for `C_rec`** (`posOkR20`'s `hPL`). -/
theorem posLanesR20 : PosLanes P20 P20.grind P20.recOod P20.recLevels (openU P20 + 15) 0 :=
  posLanes_of Lvm.QAsm.hS20.1 (posLanesR_of_K posLanesB20.1)

/-- **FIN-BV's `PosLanes` for `C_main`** (`posOkM20`'s `hPL`). -/
theorem posLanesM20 : PosLanes P20 P20.grind P20.mainOod P20.mainLevels
    (stackEndL P20.grind P20.recOod P20.recLevels (openU P20 + 15) + 15) 2 :=
  posLanes_of Lvm.QAsm.hS20.1 (posLanesR_of_K posLanesB20.2.1)

end Dec

end Lvm.Fin
