-- New for `flock-recursive` (BLUEPRINT §6.2 step 3, levels 1–4; stage S-H2, track L-ext).
import FRXRead
import FRXChainFlock

/-!
# The ladder read of levels 1–4

`readIR` is parametric in the level (`FRXReadDefs`): the level byte of the node and column tags,
the tape word of the cap's entry 0, the store's base and the words a column. This module fixes
Flock's `P30` instances of levels 1–4 (BLUEPRINT §2.2, revision 3.13):

| level | `log₂ n` | cap | `sib` | cap field offset (π) |
|---|---|---|---|---|
| 1 | 16 | `2^8` | 8 | 35,968 |
| 2 | 14 | `2^8` | 6 | 44,160 |
| 3 | 12 | `2^8` | 4 | 52,352 |
| 4 | 10 | `2^7` | 3 | 60,544 |

(Revision 3.13 offsets.) A column of levels 1–4 is 304 bytes: 16 `F` elements (256 bytes) and 48 zero bytes (3.12's
padding). The read copies the first 32 words, the 16 `F` elements, to `stB + 32 p` (`stB = 2^24`:
the level-0 output rows' region, free until level 0's interpolation). The offsets are those
of `FRXChainFlock.fsMsgs` at the C phases (`capOffL_ctl`).

**`readLv_spec`**: after `readLv i`, cell `stB + 32 q + w` holds word `w` of the column that
`colL (frEnc i)` reads under π's cap entry `q / 2^sib` of level `i`.
-/

namespace FR.X

open RecursionFast FR.Merkle

/-- The byte offset of level `i`'s cap in π (`i ≤ 4`; level 0 is `capOff`). -/
def capOffL : ℕ → ℕ
  | 0 => 19584
  | 1 => 35968
  | 2 => 44160
  | 3 => 52352
  | _ => 60544

/-- `log₂` of level `i`'s cap. -/
def capLogL (i : ℕ) : ℕ := if i = 0 then 9 else if i = 4 then 7 else 8

/-- `log₂ nᵢ` (`P30`). -/
def logNL (i : ℕ) : ℕ := 18 - 2 * i

/-- The Merkle height under a cap entry (`P30`): `9, 8, 6, 4, 3`. -/
def sibL (i : ℕ) : ℕ := logNL i - capLogL i

/-- **Cap entry `e` of level `i`**: the 32 bytes at `capOffL i + 32 e` of π. -/
def capPiL (i : ℕ) (π : Proof) (e : ℕ) : Digest := bytesAt π (capOffL i + 32 * e) 32

/-- The tape word of cap entry 0 of level `i`. -/
def capWL (i : ℕ) : ℕ := 5 + capOffL i / 8

/-- The store base of levels 1–4. -/
def stB : ℕ := 16777216

/-- **The read of level `i`** (`1 ≤ i ≤ 4`): `2^(logNL i)` positions, 32 words each at `stB`. -/
def readLv (i : ℕ) : XIR := readIR i (capWL i) stB 32 (sibL i) (2 ^ logNL i)

/-- The offsets are the C phases' messages (`fsMsgs`, positions `capPos 1 … 4`) and level 0's. -/
theorem capOffL_ctl : (List.range 5).map capOffL = [19584, 35968, 44160, 52352, 60544] ∧
    (List.range 5).map sibL = [9, 8, 6, 4, 3] ∧ capPiL 0 = capPi := by
  refine ⟨by decide, by decide, ?_⟩
  funext π e; simp only [capPiL, capPi, capOffL, capOff_eq]

theorem capPiL_zero (π : Proof) : capPiL 0 π = capPi π := by
  funext e; simp only [capPiL, capPi, capOffL, capOff_eq]

/-- **The tape at a cap entry** of any 8-aligned cap field inside π. -/
theorem tape_capL (c : Digest) (π : Proof) (L : Log) {off e m : ℕ} (h8 : off % 8 = 0)
    (he : off + 32 * e + 32 ≤ π.size) (hm : m < 4) :
    (extractorInput c π L).getD (5 + off / 8 + 4 * e + m) 0 =
      (packBytes (bytesAt π (off + 32 * e) 32).toList).getD m 0 := by
  rw [show off + 32 * e = 8 * (off / 8 + 4 * e) by omega, packBytes_bytesAt _ (by omega) hm,
    show 5 + off / 8 + 4 * e + m = 5 + (off / 8 + 4 * e + m) by omega,
    tape_getD_proof c π L (by omega), List.getD_eq_getElem _ _]

theorem capOffL_mod (i : ℕ) : capOffL i % 8 = 0 := by
  unfold capOffL; split <;> decide

theorem capOffL_le (i : ℕ) : capOffL i ≤ 60544 := by
  unfold capOffL; split <;> decide

theorem capLogL_le (i : ℕ) : capLogL i ≤ 9 := by
  unfold capLogL; split_ifs <;> decide

/-- The cap fields lie inside π: level `i`'s `2^(capLogL i)` entries end by byte 64,640. -/
theorem capOffL_fit {i : ℕ} (hi : i ≤ 4) :
    capOffL i + 32 * 2 ^ capLogL i ≤ 64640 := by
  interval_cases i <;> decide

variable {c : Digest} {π : Proof} {L : Log}

/-- **The read of level `i ∈ [1, 4]`** (any state with the sorted index at `memX`). -/
theorem readLv_spec (hD : Dom c π L) {Xi : ℕ → Word} (hX : Sorted (tp c π L) L Xi) (s : St)
    (hM : Inv s.M) (hXs : ∀ a < L.length, rd s.M (memX + a) = Xi a) (hsz : memX ≤ s.M.size)
    {i : ℕ} (hi1 : 1 ≤ i) (hi : i ≤ 4) :
    (∀ q < 2 ^ logNL i, ∀ w < 32, rd (semXIR (tp c π L) (readLv i) s).M (stB + 32 * q + w) =
      colWord (colL (frEnc i) L (capPiL i π (q / 2 ^ sibL i)) (sibL i) q) w) ∧
    (∀ a < L.length, rd (semXIR (tp c π L) (readLv i) s).M (memX + a) = Xi a) ∧
    Inv (semXIR (tp c π L) (readLv i) s).M := by
  have hps : π.size = 797904 := hD.hs.trans piSize_eq
  have hfit := capOffL_fit hi
  have hlog := capLogL_le i
  have hoff := capOffL_le i
  have hmod := capOffL_mod i
  have hcl : 2 ^ capLogL i ≤ 2 ^ 9 := Nat.pow_le_pow_right (by norm_num) hlog
  have hnp : 2 ^ logNL i ≤ 2 ^ 16 := Nat.pow_le_pow_right (by norm_num) (by unfold logNL; omega)
  have hcapn : 2 ^ logNL i ≤ 2 ^ capLogL i * 2 ^ sibL i := by
    rw [← Nat.pow_add]; refine Nat.pow_le_pow_right (by norm_num) ?_
    unfold sibL logNL capLogL; split_ifs <;> omega
  have hsib : sibL i < 64 := by unfold sibL logNL; omega
  exact readIR_sem hD hX s hM hXs (i := i) (cw := capWL i) (nw := 32) (ncap := 2 ^ capLogL i)
    (sb := stB) (cap := capPiL i π) (by unfold capWL; omega)
    (fun e he m hm => by
      simp only [tp, getD_toArray]
      exact tape_capL c π L hmod (by
        have : 32 * e + 32 ≤ 32 * 2 ^ capLogL i := by omega
        omega) hm)
    (by norm_num) hsib (by omega) (by simp only [stB, memX]; omega)
    (by simp only [regs, stB]; omega) hcapn hsz

/-- **The `F` reading of level `i ∈ [1, 4]`**: `rdF` at `stB + 32 q + 2 r` (`r < 16`) is the
column's `F` element `r` (`readF col (16 r)`), `0` where `colL` reads nothing: S-G's `wordOf`
with π's cap entries. -/
theorem readLv_spec_F (hD : Dom c π L) {Xi : ℕ → Word} (hX : Sorted (tp c π L) L Xi) (s : St)
    (hM : Inv s.M) (hXs : ∀ a < L.length, rd s.M (memX + a) = Xi a) (hsz : memX ≤ s.M.size)
    {i : ℕ} (hi1 : 1 ≤ i) (hi : i ≤ 4) {q r : ℕ} (hq : q < 2 ^ logNL i) (hr : r < 16) :
    rdF (semXIR (tp c π L) (readLv i) s).M (stB + 32 * q + 2 * r) =
      ((colL (frEnc i) L (capPiL i π (q / 2 ^ sibL i)) (sibL i) q).map
        fun col => F.ofBytes (bytesAt col (16 * r) 16)).getD 0 := by
  have h := (readLv_spec hD hX s hM hXs hsz hi1 hi).1 q hq
  rw [rdF, rdB, rdB, h (2 * r) (by omega),
    show stB + 32 * q + 2 * r + 1 = stB + 32 * q + (2 * r + 1) by omega, h (2 * r + 1) (by omega)]
  cases colL (frEnc i) L (capPiL i π (q / 2 ^ sibL i)) (sibL i) q with
  | none => rfl
  | some col => rw [Option.map_some, Option.getD_some, F_ofBytes_words]; rfl

/-- **The read's cost** for any level parameters. -/
theorem cost_readIR (i cw sb nw sib np t : ℕ) (h1 : sib < 2 ^ 64) (h2 : nw < 2 ^ 64)
    (h3 : np < 2 ^ 64) :
    cost (readIR i cw sb nw sib np) t = 14 + np * 6576 + np * sib * 6544 + np * nw * 25 :=
  cost_readIR4 memX posL i cw sb nw sib np t h3 h1 h2

/-- The four reads cost `3,914,334,222 + 764,149,774 + 137,429,006 + 27,656,206 ≈ 2^32.17`. -/
theorem cost_readLv (t : ℕ) :
    cost (readLv 1) t = 3914334222 ∧ cost (readLv 2) t = 764149774 ∧
    cost (readLv 3) t = 137429006 ∧ cost (readLv 4) t = 27656206 := by
  simp only [readLv]
  refine ⟨?_, ?_, ?_, ?_⟩ <;> rw [cost_readIR _ _ _ _ _ _ _ (by decide) (by norm_num) (by decide)] <;> decide

theorem wf_readLv (i : ℕ) : WF (readLv i) := wf_readIR ..
theorem noLoopT_readLv (i : ℕ) : NoLoopT (readLv i) := noLoopT_readIR ..
theorem outs_readLv (i t : ℕ) : outs (readLv i) t = 0 := outs_readIR ..

/-! ## Controls -/

open ReadControls in
/-- **The level byte is read** (positive and negative): a level-1 node query is a level-1 step,
and the level-0 query of `toyN` is none at level 1 (`nodeStepP_toy` is its level-0 twin). -/
theorem nodeStepP_lv1 : nodeStepP 1 [(nodeQ 1 (dg 1) (dg 2), dg 3)] 0 0 (dg 3) = some (dg 1) ∧
    nodeStepP 1 toyN 0 0 (dg 3) = none := by decide +kernel

/-- **The cap offsets are the C phases' messages**: `fsMsgs` at FS positions `330, 369, 396, 420`
(`capPos 1 … 4`, revision 3.13) absorbs π's bytes `capOffL i … + 32·2^(capLogL i)`. -/
theorem capOffL_fsMsgs :
    fsMsgs.getD 330 none = some (capOffL 1, 32 * 2 ^ capLogL 1) ∧
    fsMsgs.getD 369 none = some (capOffL 2, 32 * 2 ^ capLogL 2) ∧
    fsMsgs.getD 396 none = some (capOffL 3, 32 * 2 ^ capLogL 3) ∧
    fsMsgs.getD 420 none = some (capOffL 4, 32 * 2 ^ capLogL 4) := by decide +kernel

/-- The level tag words differ (`"FRMNOD" ‖ 1` against level 0's). -/
theorem tagNWl_one_ne : tagNWl 1 ≠ tagNW ∧ tagCWl 1 ≠ tagCW := by decide

end FR.X
