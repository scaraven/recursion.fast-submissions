-- New for lvm2 U-TAPE (UT-L, 2026-11-16): DAY-0 STATEMENTS of S2GU's good pair and the K2-LS bridge (the tape's
-- sponge half is a sponge table: `traceDigest_of_KS`, `wots*_of_KS` apply on the `Y` block and the stream block).
-- Every `sorry` is a day-0 statement tagged `-- UTAPE-STMT <n>`.
import LvmS2GUFront
import LvmS2GUSched
import LvmNodeSoundKS
import LvmMPSig
import LvmS2GUPlan

/-!
# S2GU's good pair (day-0 statements)

* `spongeBlocksGU` (3,961, `ref/utape.py`), `contRowsU` (the trace rows `1 … B − 1`, the key leaf's rows
  `8,080 … 8,110`); **`spongeBlocksGU_eq`**, **`contU_iff`** (the wire's intervals are the rows).
* **`GkU`**: the Keccak half of a good pair at S2GU: the tape's relation on `C_main` (`TapeRelU`: chain half and the
  25 lanes of every sponge row) and the boundary claims are `GbTT`'s. No `KS` block: `Y` is the `Y` block, the messages
  the stream block `S`; the boundary claims stay `GbTT`'s.
* `SBlkU`: `qr` is `qm`'s stream block at S2GU (`sOffU20`).
* The bridge (owner L): **`spongeRel_of_GkU`** (K2-LS's `SpongeRel` on the virtual input column),
  **`traceDigest_of_GkU`** (row `B − 1` of the sponge half outputs the child's trace digest), **`sigKSin_of_GkU`**
  (Q_sig's `SigKSin` from the `X` rows of `S` and the `Y` block's digest cells).
-/

set_option autoImplicit false

namespace Lvm.E2U

open RecursionFast Lvm Lvm.KG Lvm.NS Lvm.QLink Lvm.QSig Lvm.Replay
open LeanVM.Parameters LeanVM.Protocol

/-- **The S2GU trace's sponge blocks** (`ref/utape.py --occ 46`: 3,961). -/
abbrev spongeBlocksGU : ℕ := 3961

/-- **The sponge rows that continue a sponge** at S2GU: the trace rows `1 … B − 1` and rows 1–31 of the WOTS key
leaf (`ks_split + 400 …`). -/
def contRowsU : List ℕ :=
  (List.range (spongeBlocksGU - 1)).map (· + 1) ++ (List.range 31).map (ksSplit P20 + 399 + 1 + ·)

/-- **UTAPE-STMT 10** (owner L): the literal is the S2GU trace's sponge-block count (decided). -/
theorem spongeBlocksGU_eq : spongeBlocks P20U = spongeBlocksGU := sizes_P20U.1.2.2.2.2.1

/-- **UTAPE-STMT 11** (owner L): the wire's `cont` intervals are the continuation rows. -/
theorem contU_iff (j : ℕ) : contU j = decide (j ∈ contRowsU) := by
  have hk : ksSplit P20 = 7680 := Lvm.ksSplit_P20
  have hm : j ∈ contRowsU ↔ (1 ≤ j ∧ j ≤ 3960) ∨ (8080 ≤ j ∧ j ≤ 8110) := by
    simp only [contRowsU, spongeBlocksGU, List.mem_append, List.mem_map, List.mem_range, hk]
    constructor
    · rintro (⟨a, ha, rfl⟩ | ⟨a, ha, rfl⟩) <;> (clear * - ha; omega)
    · rintro (h | h)
      · exact Or.inl ⟨j - 1, by (clear * - h; omega), by (clear * - h; omega)⟩
      · exact Or.inr ⟨j - 8080, by (clear * - h; omega), by (clear * - h; omega)⟩
  rw [Bool.eq_iff_iff, decide_eq_true_iff, hm]
  simp only [contU, contIvU, List.any_cons, List.any_nil, Bool.or_false, Bool.or_eq_true, decide_eq_true_eq]

/-- **`qr` is `qm`'s stream block at S2GU** (`2^19` words at `CMain.sOffU20`). -/
def SBlkU (qm : Column CMain.nu20) (qr : Column 19) : Prop :=
  ∀ w < 2 ^ 19, qr.values.getD w 0 = qm.values.getD (CMain.sOffU20 + w) 0

/-- **The Keccak half of a good pair at S2GU** (`GkFR`'s successor): the merged tape's relation on `C_main` (the
boundary claims are `GbTT`'s `BndS`, as at S2GT). -/
def GkU (x : List UInt8) (p : Column CMain.nu20 × Column 19) : Prop :=
  TapeRelU (Lvm.ASM.hdrOf x).s (Lvm.ASM.hdrOf x).n (colM p.1)

/-- `Y`'s lanes on a `C_main` candidate. -/
abbrev YqU (qm : Column CMain.nu20) : ℕ → ℕ → K := yU (colM qm)

/-- The message lanes on a `C_main` candidate (the stream block's columns). -/
abbrev MqU (qm : Column CMain.nu20) : ℕ → ℕ → K := msgU (colM qm)

/-- **UTAPE-STMT 12** (owner L): **the sponge half is a sponge table** (`spongeRel_of_tape`'s instance at `w = 20`,
`hs = 13`, `cont = contU`; whence K2-LS's `traceDigest_of_KS`, `row_perm`, `oneRow_perm`, `wots*_of_KS`). -/
theorem spongeRel_of_GkU {x : List UInt8} {p : Column CMain.nu20 × Column 19} (hG : GkU x p) :
    SpongeRel 13 (ksVirt 13 (YqU p.1) (MqU p.1) contU) (YqU p.1) (MqU p.1) contU where
  out i hi l hl := by
    rw [YqU, hG.2 i hi l hl, tapeInU, tapeIn, if_neg (by (clear * -; omega)), if_pos (by (clear * - hi; omega)),
      Nat.add_sub_cancel_left]
  link i hi l hl := by
    rw [ksVirt, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hi,
      Nat.add_mul_div_left _ _ (Nat.two_pow_pos 13), Nat.div_eq_of_lt hi, zero_add]
  cont0 := by decide

/-- The stream block's message lanes are `qr`'s (`qr` is `qm`'s stream block). -/
theorem MqU_eq {qm : Column CMain.nu20} {qr : Column 19} (hS : SBlkU qm qr) {j l : ℕ} (hj : j < 2 ^ 14)
    (hl : l < 17) : MqU qm j l = msgM qr j l := by
  simp only [MqU, msgU, colM, msgM, wd]
  rw [hS _ (by (clear * - hj hl; omega))]
  exact congrArg (fun k ↦ qm.values.getD k 0) (by simp only [CMain.sOffU20]; (clear * -; omega))

/-- **Byte `p` of the child's stream is byte `p mod 136` of sponge row `p / 136`** (`msgBytes_eq_stream` at S2GU: no
split, every row's messages are the stream block's). -/
theorem msgBytes_eq_streamU {qm : Column CMain.nu20} {qr : Column 19} (hS : SBlkU qm qr) {p : ℕ}
    (hp : p / 136 < 2 ^ 14) :
    Lvm.KG.msgBytes (MqU qm) (p / 136) (p % 136) = (wordsBytes (wsOf (Lvm.X.laneOf (wOfCol qr)))).getD p 0 := by
  have hq : p % 136 < 136 := Nat.mod_lt _ (by norm_num)
  have hl : p % 136 / 8 < 17 := by (clear * -; omega)
  have hb : p % 136 % 8 < 8 := Nat.mod_lt _ (by norm_num)
  have e1 : p = 8 * (17 * (p / 136) + p % 136 / 8) + p % 136 % 8 := by (clear * -; omega)
  have hu : 17 * (p / 136) + p % 136 / 8 < 17 * 2 ^ 14 := by (clear * - hp; omega)
  have hc : Lvm.X.crecIdx (17 * (p / 136) + p % 136 / 8) = p % 136 / 8 * 2 ^ 14 + p / 136 := by
    unfold Lvm.X.crecIdx; (clear * - hl; omega)
  have hm : Lvm.KG.msgBytes (MqU qm) (p / 136) (p % 136) = Lvm.KG.msgBytes (msgM qr) (p / 136) (p % 136) := by
    simp only [Lvm.KG.msgBytes]; rw [MqU_eq hS hp hl]
  conv_rhs => rw [e1]
  rw [hm, byte_of_lane _ _ _ hb, toUInt8_mod]
  simp only [Lvm.KG.msgBytes, msgM, wd, lw, wsOf]
  rw [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range hu, Option.map_some,
    Option.getD_some, Lvm.X.laneOf, hc, wOfCol]
  exact Lvm.Wots.byteW_toNat _ hb

/-- The trace rows continue a sponge. -/
theorem contU_of {i : ℕ} (h1 : 1 ≤ i) (h2 : i ≤ 3960) : contU i = true := by
  simp only [contU, contIvU, List.any_cons, List.any_nil, Bool.or_false, Bool.or_eq_true, decide_eq_true_eq]
  exact Or.inl ⟨h1, h2⟩

/-- **UTAPE-STMT 13** (owner L): **the sponge half outputs the child's trace digest** at row `B − 1`
(`traceDigest_of_goodKP`'s port: the stream's lane `17 i + l` is message lane `l` of row `i`, read from `qm`'s stream
block, which is `qr`). -/
theorem traceDigest_of_GkU {x : List UInt8} {qm : Column CMain.nu20} {qr : Column 19}
    (hG : GkU x (qm, qr)) (hS : SBlkU qm qr) (hL : LaneLink P20U (wsOf (Lvm.X.laneOf (wOfCol qr))))
    (hpad : PadOkB (wordsBytes (wsOf (Lvm.X.laneOf (wOfCol qr)))) (hashedLen P20U)) :
    Lvm.KSponge.stDigest (yState (YqU qm) (spongeBlocks P20U - 1)) =
      traceDigest (decode P20U (wsOf (Lvm.X.laneOf (wOfCol qr)))) := by
  have H := spongeRel_of_GkU hG
  have hS' := stream_of_laneLink Lvm.E2Q.streamOk_P20U hL
  have hsz : hashedLen P20U ≤ (wordsBytes (wsOf (Lvm.X.laneOf (wOfCol qr)))).length := by
    rw [wordsBytes_length]; exact hL.size
  have hsb : spongeBlocks P20U = Lvm.KSponge.nBlk (hashedLen P20U) := by
    rw [sizes_P20U.1.2.2.2.2.1, sizes_P20U.1.2.2.1]; rfl
  have hB : spongeBlocks P20U ≤ 7680 := by rw [sizes_P20U.1.2.2.2.2.1]; norm_num
  have hin : ∀ i, 0 < i → i < Lvm.KSponge.nBlk (hashedLen P20U) → contU i = true :=
    fun i h1 h2 => contU_of h1 (by rw [← hsb, sizes_P20U.1.2.2.2.2.1] at h2; omega)
  rw [hsb] at hB ⊢
  generalize hashedLen P20U = L at hS' hsz hpad hB hin
  have hnbL : Lvm.KSponge.nBlk L = L / 136 + 1 := rfl
  refine traceDigest_of_KS 13 _ (YqU qm) (MqU qm) _ H L (le_trans hB (by norm_num)) hin ?_ _ ?_
  · intro p h1 h2
    have h2' : p < 136 * Lvm.KSponge.nBlk L := h2
    have := msgBytes_eq_streamU hS (p := p) (by show p / 136 < 2 ^ 14; omega)
    rw [show p / RecursionFast.Keccak.rate = p / 136 from rfl,
      show p % RecursionFast.Keccak.rate = p % 136 from rfl, this, ← padAt_eq]
    exact hpad p h1 (by rw [nBlk_eq]; omega)
  · rw [← hS']
    refine List.ext_getElem (by rw [Lvm.KSponge.streamOf_length, List.length_take]; omega) fun p h1 h2 => ?_
    have hp : p < L := by rw [Lvm.KSponge.streamOf_length] at h1; exact h1
    simp only [Lvm.KSponge.streamOf, List.getElem_ofFn, List.getElem_take]
    rw [show p / RecursionFast.Keccak.rate = p / 136 from rfl,
      show p % RecursionFast.Keccak.rate = p % 136 from rfl,
      msgBytes_eq_streamU hS (by show p / 136 < 2 ^ 14; omega), List.getD_eq_getElem?_getD,
      List.getElem?_eq_getElem (by omega), Option.getD_some]

/-- A row from the split absorbs the `X` cells (`xorMsg_cells` at S2GU: the `X` rows are the stream block's). -/
theorem xorMsg_cellsU {qm : Column CMain.nu20} {v : ℕ → FK} {f : ℕ → ℕ} {r : ℕ}
    (h : ∀ l < 17, v (f l) = FK.ofBF64 (MqU qm (ksSplit P20 + r) l)) (a : RecursionFast.Keccak.State) :
    Lvm.KSponge.xorMsg a (Lvm.Wots.laneByte (lanesW v f)) =
      Lvm.KSponge.xorMsg a (Lvm.KG.msgBytes (MqU qm) (ksSplit P20 + r)) := by
  have e : Lvm.KSponge.rateArr (Lvm.Wots.laneByte (lanesW v f)) =
      Lvm.KSponge.rateArr (Lvm.KG.msgBytes (MqU qm) (ksSplit P20 + r)) := by
    unfold Lvm.KSponge.rateArr
    congr 1
    funext j
    have hj : j.val < 136 := j.2
    simp only [Lvm.Wots.laneByte, lanesW, Lvm.KG.msgBytes]
    rw [h _ (by (clear * - hj; omega))]
    rfl
  simp only [Lvm.KSponge.xorMsg, e]

/-- **UTAPE-STMT 14** (owner L): **Q_sig's `KS` hypothesis at S2GU** (`sigKSin_of_goodKP`'s port: the `X` rows are
the stream block's rows from `ks_split`, the digest cells the `Y` block's lanes 0–3). -/
theorem sigKSin_of_GkU {x : List UInt8} {qm : Column CMain.nu20} {qr : Column 19} {I : SigIn} {v : ℕ → FK}
    (hG : GkU x (qm, qr))
    (hx : ∀ r < 449, ∀ l < 17, v (I.xs + 17 * r + l) = FK.ofBF64 (MqU qm (ksSplit P20 + r) l))
    (hys : ∀ r < 399, ∀ l < 4, v (I.ys + 4 * r + l) = FK.ofBF64 (YqU qm (ksSplit P20 + r) l))
    (hyc : ∀ t ≤ 16, ∀ l < 4, v (I.yc + 4 * t + l) = FK.ofBF64 (YqU qm (ksSplit P20 + 430 + t) l))
    (hyls : ∀ l < 4, v (I.yls + l) = FK.ofBF64 (YqU qm (ksSplit P20 + 447) l))
    (hyns : ∀ l < 4, v (I.yns + l) = FK.ofBF64 (YqU qm (ksSplit P20 + 448) l)) :
    SigKSin I v := by
  have H := spongeRel_of_GkU hG
  have hrow : ∀ r < 449, ksSplit P20 + r < 2 ^ 13 := fun r hr => by rw [ksSplit_P20]; omega
  have hcF : ∀ r, r < 449 → ¬ (400 ≤ r ∧ r ≤ 430) →
      contU (ksSplit P20 + r) = false := fun r h1 h2 => by
    simp only [contU, contIvU, List.any_cons, List.any_nil, Bool.or_false, Bool.or_eq_false_iff, Bool.or_eq_true, decide_eq_false_iff_not, decide_eq_true_eq, ksSplit_P20]; omega
  have hcT : ∀ r, 400 ≤ r → r ≤ 430 → contU (ksSplit P20 + r) = true := fun r h1 h2 => by
    simp only [contU, contIvU, List.any_cons, List.any_nil, Bool.or_false, Bool.or_eq_true, decide_eq_true_eq, ksSplit_P20]; omega
  -- a one-block row
  have one : ∀ r < 449, ¬ (400 ≤ r ∧ r ≤ 430) → ∀ y, (∀ l < 4, v (y + l) = FK.ofBF64 (YqU qm (ksSplit P20 + r) l)) →
      OneHash v (fun l => I.xs + 17 * r + l) y := fun r hr hn y hy =>
    ⟨yState (YqU qm) (ksSplit P20 + r), by
      rw [xorMsg_cellsU (qm := qm) (r := r) (fun l hl => hx r hr l hl)]
      exact oneRow_perm 13 _ (YqU qm) (MqU qm) _ H (hrow r hr) (hcF r hr hn),
      digAt_of_cells hy⟩
  refine ⟨fun r hr => one r (by (clear * - hr; omega)) (by (clear * - hr; omega)) _ (hys r hr), ?_, fun t ht => ?_,
    one 447 (by (clear * -; omega)) (by (clear * -; omega)) _ hyls, one 448 (by (clear * -; omega)) (by (clear * -; omega)) _ hyns⟩
  · -- the key leaf: rows `S + 399 … S + 430`
    refine ⟨fun u => prevState (YqU qm) contU (ksSplit P20 + (399 + u)),
      fun u => yState (YqU qm) (ksSplit P20 + (399 + u)), ?_, fun u hu => ?_, fun u hu => ?_, ?_⟩
    · simp only [prevState, Nat.add_zero, hcF 399 (by (clear * -; omega)) (by (clear * -; omega))]; rfl
    · rw [xorMsg_cellsU (qm := qm) (r := 399 + u) (fun l hl => hx _ (by (clear * - hu; omega)) l hl)]
      exact row_perm 13 _ (YqU qm) (MqU qm) _ H (hrow _ (by (clear * - hu; omega)))
    · simp only [prevState, hcT (399 + (u + 1)) (by (clear * - hu; omega)) (by (clear * - hu; omega)), if_true]
      congr 1
    · refine digAt_of_cells fun l hl => ?_
      have := hyc 0 (by (clear * -; omega)) l hl
      simpa using this
  · -- path node `t`: row `S + 431 + t`
    refine one (431 + t) (by (clear * - ht; omega)) (by (clear * - ht; omega)) _ fun l hl => ?_
    have := hyc (t + 1) (by (clear * - ht; omega)) l hl
    rw [show ksSplit P20 + 430 + (t + 1) = ksSplit P20 + (431 + t) by (clear * -; omega)] at this
    exact this


end Lvm.E2U
