-- New for lvm2 roll 11 (M′, R11-LEAD freeze 2026-11-13): the advice decoders generic in the shape, and their
-- instances at `C_main`'s three levels (`cfgMain23Jq`). Definitions are final; the theorems are frozen
-- statements (owner: R11-X). A proof never changes its statement; a needed change is reported old → new.
import LvmXDec1Ud
import LvmXDecUd
import LvmWhirParamsJ23
import LvmLayout
import LvmMPDecG

/-!
# M′'s decoders (`C_rec` merged into `C_main`)

The extractor of M′ decodes `C_main` top-down from the residual, as J2′'s decodes `C_rec` (`decodeRec1` then
`decodeRec`): level 2 (`codeJ9R4`: `2^13` positions, 16 `E` rows of `2^9`), level 1 (`codeJ13R3`: `2^16`
positions, 16 `E` rows of `2^13`), level 0 (`codeJ17R2`: `2^19` positions, 64 `K` lanes of `2^17`). At level 0
only the **window** of lanes `[winLo, winLo + winC)` is interpolated: the lanes that hold the stream in every
shape (B1's strides 1–2, and 4 later). Fuel at `C = 8`: `2^44.52` [`R11` G0, the entry's `cost`].

* generic decoders: `encG`, `agreeG`/`decWordG`/`decodeG0` (level 0, `N` the NTT's domain bound, positions
  `2^nL`, lane size `2^kL`, window `lo`, `C`), `agree1G`/`coef1G`/`dec1G`/`decode1G` (levels ≥ 1, 16 `E` rows);
* the shipped decoders are instances (**`decodeRec_eq_G`**, **`decodeRec1_eq_G`**);
* M′'s instances `decodeMP2`, `decodeMP1`, `decodeMP0` and their correctness (**`decodeMP2_of_mem`**,
  **`decodeMP1_of_mem`**, **`decodeMP0_of_mem`**), in the form of `decodeRec1_of_ud` / `decodeRec_of_mem`.
-/

namespace Lvm.X

open Finset Lvm.Nb CompPoly.Extension BF64 LeanVM.Parameters LeanVM.Protocol LeanVM.Protocol.Compile
  LeanVM.Protocol.Whir LeanVM.Protocol.Whir.Ud LeanVM.Protocol.Whir.Sound LeanVM.Protocol.EndToEnd

/-! ## Generic decoders -/

/-- `Enc` of an `E` message of `2^kL` coefficients at position `q`. -/
noncomputable def encG (kL : ℕ) (f : ℕ → Ext3) (q : ℕ) : Ext3 :=
  ∑ v ∈ range (2 ^ kL), f v * ofK (nbAt v q)

/-- Level 0: the positions `q < 2^nL`, increasing, where the 64-lane fold agrees with `Enc(f)`. -/
noncomputable def agreeG (nL kL : ℕ) (wd : ℕ → ℕ → BF64) (α f : ℕ → Ext3) : List ℕ :=
  (List.range (2 ^ nL)).filter fun q => decide (foldAt α wd q = encG kL f q)

/-- Level 0: word `i` of the stack (lane `i / 2^kL`, coefficient `i % 2^kL`), the lane interpolated on the
first `2^kL` agreeing positions. -/
noncomputable def decWordG (N nL kL : ℕ) (wd : ℕ → ℕ → BF64) (α f : ℕ → Ext3) (i : ℕ) : BF64 :=
  coeffsAt ptK N kL 0 (interpF ptK ((agreeG nL kL wd α f).take (2 ^ kL)).toFinset (rowW wd (i / 2 ^ kL)))
    (i % 2 ^ kL)

/-- **The generic level-0 decoder**: `none` when fewer than `2^kL` positions agree, else the words of lanes
`lo … lo + C − 1` (`C · 2^kL` words, stack word `lo · 2^kL + i` at index `i`). -/
noncomputable def decodeG0 (N nL kL lo C : ℕ) (wd : ℕ → ℕ → BF64) (α f : ℕ → Ext3) : Option (List BF64) :=
  if 2 ^ kL ≤ (agreeG nL kL wd α f).length then
    some ((List.range (C * 2 ^ kL)).map fun i => decWordG N nL kL wd α f (lo * 2 ^ kL + i))
  else none

/-- Levels ≥ 1: the positions `q < 2^nL`, increasing, where the 16-row fold agrees with `Enc(f)`. -/
noncomputable def agree1G (nL kL : ℕ) (wd : ℕ → ℕ → BF64) (α f : ℕ → Ext3) : List ℕ :=
  (List.range (2 ^ nL)).filter fun q => decide (fold1At α wd q = encG kL f q)

/-- Levels ≥ 1: coefficient `v` of `K` lane `t`, interpolated on the first `2^kL` agreeing positions. -/
noncomputable def coef1G (N nL kL : ℕ) (wd : ℕ → ℕ → BF64) (α f : ℕ → Ext3) (t v : ℕ) : BF64 :=
  coeffsAt ptK N kL 0 (interpF ptK ((agree1G nL kL wd α f).take (2 ^ kL)).toFinset (lane1 wd t)) v

/-- Levels ≥ 1: entry `i = u + 16 v` of the level's message (row `u`, coefficient `v`). -/
noncomputable def dec1G (N nL kL : ℕ) (wd : ℕ → ℕ → BF64) (α f : ℕ → Ext3) (i : ℕ) : Ext3 :=
  mkE (coef1G N nL kL wd α f (3 * (i % 16)) (i / 16)) (coef1G N nL kL wd α f (3 * (i % 16) + 1) (i / 16))
    (coef1G N nL kL wd α f (3 * (i % 16) + 2) (i / 16))

/-- **The generic level-≥1 decoder**: `none` when fewer than `2^kL` positions agree, else the `2^(kL+4)`
entries of the level's message, `0` from there on. -/
noncomputable def decode1G (N nL kL : ℕ) (wd : ℕ → ℕ → BF64) (α f : ℕ → Ext3) : Option (ℕ → Ext3) :=
  if 2 ^ kL ≤ (agree1G nL kL wd α f).length then
    some fun i => if i < 2 ^ (kL + 4) then dec1G N nL kL wd α f i else 0
  else none

/-! ## The shipped decoders are instances (refactor; no behaviour change) -/

/-- `C_rec`'s level-0 decoder is `decodeG0 15 15 13 0 64`. -/
theorem decodeRec_eq_G : decodeRec = decodeG0 nLog 15 13 0 64 := by
  funext wd α f
  -- the two agreement lists differ only in the `DecidableEq K` instance (`BF64`'s and `K`'s)
  have hA : agreeL wd α f = agreeG 15 13 wd α f := by
    unfold agreeL agreeG
    exact congrArg (fun p => List.filter p (List.range (2 ^ 15)))
      (funext fun q => decide_eq_decide.mpr Iff.rfl)
  unfold decodeRec decodeG0
  rw [hA, show 64 * 2 ^ 13 = 2 ^ 19 by norm_num]
  refine congrArg (fun l => if 2 ^ 13 ≤ (agreeG 15 13 wd α f).length then some l else none)
    (List.map_congr_left fun i _ => ?_)
  rw [zero_mul, zero_add]
  unfold decWord decWordG selJ
  rw [hA]

/-- `C_rec`'s level-1 decoder is `decode1G 15 12 9`. -/
theorem decodeRec1_eq_G : decodeRec1 = decode1G nLog 12 9 := by
  funext wd α f
  rfl

/-! ## M′'s instances (`C_main` at `cfgMain23Jq`) -/

/-- The NTT's domain bound at M′ (`2^19` positions at level 0). -/
abbrev nLogMP : ℕ := 19

/-- **The stream window** of `C_main`'s level-0 lanes: lanes `40 … 47`. The layout must keep the stream's
physical words in these lanes in every shape (strides 1, 2, 4). -/
abbrev winLo : ℕ := 40
abbrev winC : ℕ := 8

/-- `E` coefficients of a message on `κ` bits, `ℕ`-indexed (`v ↦ f(bits v)`, `0` from `2^κ` on). -/
noncomputable def fNk (κ : ℕ) (f : (Fin κ → Bool) → E) (v : ℕ) : Ext3 :=
  if h : v < 2 ^ κ then f ((bitsEquiv κ).symm ⟨v, h⟩) else 0

/-- A `C_main` stack's words (`2^23`). -/
def msgOfN {μ : ℕ} (q : Column μ) (i : ℕ) : BF64 := q.values.getD i 0

/-- **The window of a `C_main` stack**: its words `winLo · 2^17 + i`, `i < winC · 2^17`. -/
def winOf (q : Column CMain.nu20) : List BF64 :=
  (List.range (winC * 2 ^ 17)).map fun i => msgOfN q (winLo * 2 ^ 17 + i)

/-- M′ level 2 (`codeJ9R4`). -/
noncomputable def decodeMP2 (wd : ℕ → ℕ → BF64) (α f : ℕ → Ext3) : Option (ℕ → Ext3) :=
  decode1G nLogMP 13 9 wd α f

/-- M′ level 1 (`codeJ13R3`). -/
noncomputable def decodeMP1 (wd : ℕ → ℕ → BF64) (α f : ℕ → Ext3) : Option (ℕ → Ext3) :=
  decode1G nLogMP 16 13 wd α f

/-- M′ level 0 (`codeJ17R2`), the window only. -/
noncomputable def decodeMP0 (wd : ℕ → ℕ → BF64) (α f : ℕ → Ext3) : Option (List BF64) :=
  decodeG0 nLogMP 19 17 winLo winC wd α f

/-- **Level 2 returns any member of its list** (as `decodeRec1_of_ud`): for `V` in level 2's list of the
level-2 word's rows (`IsInterleavedCodeword`, `IsClose` at `A ≥ 2^9`) whose fold by `α₂` is the residual, off
the luck event, the decoder returns `V`'s message. -/
theorem decodeMP2_of_mem (W : Compile.Word) (hW : ∀ v < 2 ^ 13, (W v).length = 48)
    (α : Fin 4 → E) (f : (Fin (codesMain23Jq 2).κ → Bool) → E)
    (V : (Fin 4 → Bool) → Fin (codesMain23Jq 2).n → E)
    (hcw : IsInterleavedCodeword (codesMain23Jq 2).code V) {A : ℕ} (hA : 2 ^ 9 ≤ A)
    (hcl : IsClose A (rows1 4 (codesMain23Jq 2).n W) V)
    (hf : f = ∑ u, eqW α u • decode (codesMain23Jq 2) V u)
    (hL : ¬ FoldAllLuck α (rows1 4 (codesMain23Jq 2).n W) V) :
    decodeMP2 (wdOf W) (alphaN1 α) (fNk 9 f) =
      some (fNk 13 (joinMsg (by rfl : 13 = 4 + (codesMain23Jq 2).κ) (decode (codesMain23Jq 2) V))) := by
  have hg : ∀ w : Fin (codesMain23Jq 2).κ → Bool, fNk 9 f (bitsToNat w) = f w := fun w => by
    have h : bitsToNat w < 2 ^ 9 := bitsToNat_lt w
    unfold fNk; rw [dif_pos h]
    exact congrArg f (bitsEquiv_symm_bitsToNat w)
  have hmsg : ∀ (u : Fin 4 → Bool) (w : Fin (codesMain23Jq 2).κ → Bool),
      fNk 13 (joinMsg (by rfl : 13 = 4 + (codesMain23Jq 2).κ) (decode (codesMain23Jq 2) V))
        (bitsToNat u + 16 * bitsToNat w) = decode (codesMain23Jq 2) V u w := fun u w => by
    have hu : bitsToNat u < 16 := bitsToNat_lt u
    have hw : bitsToNat w < 512 := bitsToNat_lt w
    have hv : bitsToNat u + 16 * bitsToNat w < 2 ^ 13 := by norm_num; omega
    unfold fNk; rw [dif_pos hv]
    exact joinMsg_natAt _ _ u w hv
  have hmsg0 : ∀ i, 2 ^ ((codesMain23Jq 2).κ + 4) ≤ i →
      fNk 13 (joinMsg (by rfl : 13 = 4 + (codesMain23Jq 2).κ) (decode (codesMain23Jq 2) V)) i = 0 :=
    fun i hi => by
      have hi' : 8192 ≤ i := hi
      unfold fNk; rw [dif_neg (by norm_num; omega)]
  unfold decodeMP2 decode1G
  exact dec1Body_of_mem (N := nLogMP) (codesMain23Jq 2) (by show 9 ≤ 19; norm_num) (by norm_num) W hW α f V
    hcw hA hcl hf hL _ hg _ hmsg hmsg0

/-- **Level 1 returns any member of its list**, the same at `codeJ13R3` (`A ≥ 2^13`). -/
theorem decodeMP1_of_mem (W : Compile.Word) (hW : ∀ v < 2 ^ 16, (W v).length = 48)
    (α : Fin 4 → E) (f : (Fin (codesMain23Jq 1).κ → Bool) → E)
    (V : (Fin 4 → Bool) → Fin (codesMain23Jq 1).n → E)
    (hcw : IsInterleavedCodeword (codesMain23Jq 1).code V) {A : ℕ} (hA : 2 ^ 13 ≤ A)
    (hcl : IsClose A (rows1 4 (codesMain23Jq 1).n W) V)
    (hf : f = ∑ u, eqW α u • decode (codesMain23Jq 1) V u)
    (hL : ¬ FoldAllLuck α (rows1 4 (codesMain23Jq 1).n W) V) :
    decodeMP1 (wdOf W) (alphaN1 α) (fNk 13 f) =
      some (fNk 17 (joinMsg (by rfl : 17 = 4 + (codesMain23Jq 1).κ) (decode (codesMain23Jq 1) V))) := by
  have hg : ∀ w : Fin (codesMain23Jq 1).κ → Bool, fNk 13 f (bitsToNat w) = f w := fun w => by
    have h : bitsToNat w < 2 ^ 13 := bitsToNat_lt w
    unfold fNk; rw [dif_pos h]
    exact congrArg f (bitsEquiv_symm_bitsToNat w)
  have hmsg : ∀ (u : Fin 4 → Bool) (w : Fin (codesMain23Jq 1).κ → Bool),
      fNk 17 (joinMsg (by rfl : 17 = 4 + (codesMain23Jq 1).κ) (decode (codesMain23Jq 1) V))
        (bitsToNat u + 16 * bitsToNat w) = decode (codesMain23Jq 1) V u w := fun u w => by
    have hu : bitsToNat u < 16 := bitsToNat_lt u
    have hw : bitsToNat w < 8192 := bitsToNat_lt w
    have hv : bitsToNat u + 16 * bitsToNat w < 2 ^ 17 := by norm_num; omega
    unfold fNk; rw [dif_pos hv]
    exact joinMsg_natAt _ _ u w hv
  have hmsg0 : ∀ i, 2 ^ ((codesMain23Jq 1).κ + 4) ≤ i →
      fNk 17 (joinMsg (by rfl : 17 = 4 + (codesMain23Jq 1).κ) (decode (codesMain23Jq 1) V)) i = 0 :=
    fun i hi => by
      have hi' : 131072 ≤ i := hi
      unfold fNk; rw [dif_neg (by norm_num; omega)]
  unfold decodeMP1 decode1G
  exact dec1Body_of_mem (N := nLogMP) (codesMain23Jq 1) (by show 13 ≤ 19; norm_num) (by norm_num) W hW α f V
    hcw hA hcl hf hL _ hg _ hmsg hmsg0

/-- **Level 0 returns a candidate's window** (as `decodeRec_of_mem`): for a candidate `q` of the root word at
`A ≥ 2^17`, off the luck event, the decoder on `q`'s fold returns `q`'s window. -/
theorem decodeMP0_of_mem (W : Compile.Word) (α : Fin LeanVM.Protocol.EndToEnd.laneBits → E) (q : Column CMain.nu20) {A : ℕ}
    (hW : ∀ v < 2 ^ 19, (W v).length = 64) (hq : q ∈ Candidates CMain.nu20 2 A W) (hA : 2 ^ 17 ≤ A)
    (hL : ¬ FoldAllLuck α (laneRows CMain.nu20 2 W) (encRows CMain.nu20 2 q)) :
    decodeMP0 (wdOf W) (alphaN α) (fNk 17 (foldMsg α q)) = some (winOf q) := by
  have hg : ∀ w : Fin 17 → Bool, fNk 17 (foldMsg α q) (bitsToNat w) = foldMsg α q w :=
    fun w => by
      have h : bitsToNat w < 2 ^ 17 := bitsToNat_lt w
      unfold fNk; rw [dif_pos h]
      exact congrArg (foldMsg α q) (bitsEquiv_symm_bitsToNat w)
  unfold decodeMP0 decodeG0 winOf
  exact dec0Body_of_mem (μ := CMain.nu20) (R := 2) (N := nLogMP) (lo := winLo) (C := winC) (by decide)
    (by decide) (by decide) (by decide) W α q hW hq hA hL _ hg

end Lvm.X
