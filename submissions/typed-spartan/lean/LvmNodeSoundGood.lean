-- WP-14c (NodeSound, O10). New for lvm: the good candidate pair `GoodN` (agreed with WP-14 for O6:
-- `Good := GoodN`) and its chain half (`chain_of_goodN`). lvm2 S2 (WP S2-CERT): the chain half is
-- the tape's (`TapeOut` on `D`, T-W's `chain_of_tape`), `C_main` is `2^23` words (lvm2 roll 8, B1; roll 7: `2^24`).
import LvmNodeSound
import LvmM3MidCert
import LvmKeccakCallerPhases
import LvmKeccakCallerTape

/-!
# The good candidate pair

**`GoodN T hτ x (qm, qr)`** = `Gb ∧ Gk` (the shape of WP-14's O6 glue `midSpecOf`):

* `Gb`: the M3 instance of the statement's tables `T x` holds on the stack of the pair
  (WP-9b `midBusTableSpecS`'s precondition: `M3Holds (inst lay26 (T x) _) () (stackOf lay26 qm qr)`;
  O6 takes `T x := sumcheckTabs (tabs (pubX x))`);
* `Gk` (lvm2 S2): the tape's chain part on `D` (`TapeOut 20 s n (dD qm)`: lanes 0–3 of every row
  are `Keccak-f` of the row's virtual input, T-W's `ChainTapeRel.out`), `KS`'s relation
  (`KSRel 13 9 y2 (contRows P20)`: KS13, messages from `X` from row 7,680, lvm2 CR-K, roll 8 B1; roll 7: KS14, 15,360), and the boundary claims `Bnd x qm` (T5: `D_{n−1} = h`, T-W's
  `ChainTapeRel.last`), `s, n, h` from the header, in `kgSpecS`'s argument order.

**The accessors** (V_S's P20 layout, `LvmLayout`'s `CMain`, KS13 (lvm2 CR-K, roll 8 B1): `D` at words
`x + 2^20·l` (slots 0–3, `dBlkE = ⟨22, 0⟩`), `ksBlk = ⟨19, ksOff20⟩`, `ksY2Off = ksY2Off20`, `X_l` at
`CMain.ksXW20 l 0 = xOff20 + l·2^9`; the stream columns `M_l` at `C_rec` words `l·2^14 + i`): `colM qm` (all
of `C_main`), `dD qm` (T-W's `dOf 20 0`), `ksCol qm`, `msgM qr i l`, `msgX qm i l`.

**`chain_of_goodN`**: a header that `okS` accepts and a good pair give `chainEnd s n = h`
(T-W's `chain_of_tape`).
-/

set_option autoImplicit false

namespace Lvm.NS

open RecursionFast Lvm Lvm.ASM Lvm.M3 Lvm.KG LeanVM.Parameters LeanVM.Protocol LeanVM.Protocol.KeccakGkr

/-! ## The accessors -/

/-- Word `i` of a committed column (`0` past it). -/
def wd {n : ℕ} (q : Column n) (i : ℕ) : K := q.values.getD i 0

/-- All of `C_main` (`2^23` words at roll 8, B1). -/
def colM (qm : Column CMain.nu20) : ℕ → K := wd qm

/-- The digest lanes `D_l[x]` (lvm2 S2: slots 0–3 of `C_main`, word `x + 2^20·l`; T-W's `dOf 20 0`). -/
def dD (qm : Column CMain.nu20) : ℕ → ℕ → K := Lvm.KG.dOf 20 0 (colM qm)

/-- `KS`'s block: `C_main` words from `ksOff20` (`2^19` words, KS13). -/
def ksCol (qm : Column CMain.nu20) (i : ℕ) : K := wd qm (CMain.ksOff20 + i)

/-- `KS`'s output lanes `14 … 24`: `C_main` from `ksY2Off20` (11 slots of `2^13`, KS13). -/
def ksY2 : ℕ := CMain.ksY2Off20

/-- The stream's message lanes (`KS` rows `< ksSplit P20 = 7,680`, KS13): `C_rec` column `l`, row `i`. -/
def msgM (qr : Column 19) (i l : ℕ) : K := wd qr (l * 2 ^ 14 + i)

/-- The `X` message lanes (`KS` rows `≥ ksSplit P20 = 7,680`, KS13): `C_main` from `xOff20`, column `l` of
`2^9` rows, row `i` (`CMain.ksXW20`). -/
def msgX (qm : Column CMain.nu20) (i l : ℕ) : K := wd qm (CMain.ksXW20 l i)

/-! ## The good pair -/

/-- **The chain's boundary claims** (T5, V_S's `tapeClaims` boundary part: `D̃_l(bits(n − 1)) = h_l`;
T-W's `ChainTapeRel.last`). -/
def Bnd (x : List UInt8) (qm : Column CMain.nu20) : Prop :=
  ∀ l < 4, dD qm ((hdrOf x).n - 1) l = K.ofLane (RecursionFast.Keccak.blockLane (hdrOf x).h.toArray l)

/-- **The tape's chain part** of a pair (T1–T4's relation, T-W's `ChainTapeRel.out` on `D`). -/
def TapeG (x : List UInt8) (qm : Column CMain.nu20) : Prop := TapeOut 20 (hdrOf x).s (hdrOf x).n (dD qm)

/-- **The Keccak half** of a good pair (`kgSpecS`'s relations, then the boundary claims). -/
def GoodK (x : List UInt8) (p : Column CMain.nu20 × Column 19) : Prop :=
  TapeG x p.1 ∧
  KSRel 13 9 ksY2 (contRows P20) (colM p.1) (ksCol p.1) (msgM p.2) (msgX p.1) ∧ Bnd x p.1

/-- **The bus/table half** of a good pair (WP-9b `midBusTableSpecS`'s precondition). -/
def GoodB (T : List UInt8 → List Tab) (hτ : ∀ x, ∀ t ∈ T x, t.τ ≤ lay26.μ) (x : List UInt8)
    (p : Column CMain.nu20 × Column 19) : Prop :=
  M3Holds (inst lay26 (T x) (hτ x)) () (stackOf lay26 p.1 p.2)

/-- **The good candidate pair** (O6's `Good`, O10's hypothesis). -/
def GoodN (T : List UInt8 → List Tab) (hτ : ∀ x, ∀ t ∈ T x, t.τ ≤ lay26.μ) : GoodRel :=
  fun x qm qr ↦ GoodB T hτ x (qm, qr) ∧ GoodK x (qm, qr)

/-! ## The chain -/

/-- `okS`'s length bounds. -/
theorem okS_n {vk c : RecursionFast.Digest} {x : List UInt8} (hok : okS vk c x = true) :
    1 ≤ (hdrOf x).n ∧ (hdrOf x).n ≤ 2 ^ 20 := by
  unfold okS at hok
  generalize hdrOf x = hd at hok ⊢
  simp only [Bool.and_eq_true, decide_eq_true_eq] at hok
  exact ⟨hok.1.1.2, hok.1.2⟩

/-- **The chain of a good pair** (T-W's `chain_of_tape`). -/
theorem chain_of_goodK {vk c : RecursionFast.Digest} {x : List UInt8} {p : Column CMain.nu20 × Column 19}
    (hok : okS vk c x = true) (hG : GoodK x p) :
    chainEnd (hdrOf x).s (hdrOf x).n = (hdrOf x).h :=
  chain_of_tape (okS_n hok).1 (okS_n hok).2 ⟨hG.1, hG.2.2⟩

/-- The chain half of `NodeSound` for `GoodN`. -/
theorem chain_of_goodN {T : List UInt8 → List Tab} {hτ : ∀ x, ∀ t ∈ T x, t.τ ≤ lay26.μ}
    {vk c : RecursionFast.Digest} {x : List UInt8} {qm : Column CMain.nu20} {qr : Column 19}
    (hok : okS vk c x = true) (hG : GoodN T hτ x qm qr) :
    chainEnd (hdrOf x).s (hdrOf x).n = (hdrOf x).h :=
  chain_of_goodK hok hG.2

end Lvm.NS
