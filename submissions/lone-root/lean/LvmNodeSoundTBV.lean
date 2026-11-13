-- New for lvm2 (roll 8 = B1, L-D): roll 7's FIN-BV memory facts (`LvmFinBV`: `posBits_of`, `hpos20`, `sBits20`,
-- `pw20`, `nBits20`, `n1_20`, `nN_20`) on any memory whose `K` cells carry the `BITS` classes' outputs (`OutsOn`, the
-- typed rows' `outT20`), their proofs copied with the bus's `out1_at` replaced by `out1_of`. Q_link's position bits are
-- nodeT20's `hpos`; the others are `BVT`'s fields (the typed HAR's hypothesis).
import LvmNodeSoundTBits
import LvmQAsmInb
import LvmQLinkBits
import LvmQAsmHarBase
import LvmQWireSound
import LvmFinPos

/-!
# The `BITS` facts that `NodeSound` and the HAR read, on the typed rows

* **`OutsOn v`**: every class of `bspecs cfg20 noData`, every real row, every valid output holds on `v`
  (`outT20` on `memT`); **`out1_of`**: then `Out1` for an output.
* **`posBits_on`** (`posBits_of`): Q_link's `PosBits`; **`hposT`**: nodeT20's `hpos` (`qin_bits`).
* **`sBits_on`** (`sBits20`), **`pw_on`** (`pw20`), **`nBits_on`** (`nBits20`), **`nRange_on`** (`n1_20`,
  `nN_20`, from Q_sig's `ChildOk`).
* **`out1_entryT`** (`out1_entry`), **`posVal_on`** (`posVal_of`): a position's two field cells add up to
  `kOf (posL …)` (Q_link's position cells then hold it on a good pair: `LvmNodeSoundT20B.posCellsT`).
-/

set_option autoImplicit false

namespace Lvm.NS

open RecursionFast Lvm Lvm.T Lvm.ASM Lvm.Replay Lvm.Loop Lvm.Loop.Build Lvm.QLink Lvm.QSig Lvm.M3
open Lvm.QAsm Lvm.QTyped Lvm.Typed Lvm.TypedV Lvm.BitsTab Lvm.Bits Lvm.SigBits Lvm.Har LeanVM.Protocol
open Lvm.VEq (pubX)

/-- **The `BITS` classes' outputs hold on `v`** (`outT20`'s form). -/
def OutsOn (v : ℕ → FK) : Prop :=
  ∀ B ∈ bspecs cfg20 noData, ∀ y < B.n, ∃ w : FK, (B.rd = true → v (B.wc y) = w) ∧
    ∀ j < B.outs.length, (B.out j).Valid → v (B.oc j y) = ⟨(B.out j).word w.val⟩

theorem outsOn_memT (S : Lvm.CT.SF20) (H : THyp TiB) {x : List UInt8} {qm : Column CMain.nu20} {qr : Column 19}
    (hG : GoodT TiB H x qm qr) : OutsOn (memT x qm qr).k :=
  fun _ hB _ hy ↦ outT20 S H hG hB hy

theorem lt_padT' {t j : ℕ} (hj : j < t) : j < padT t := by
  obtain ⟨c, hc, h1, h2, h3⟩ := pchunks_cover hj
  have := pchunks_end c hc
  omega

theorem posSpecs_mem {B : BSpec} (hB : B ∈ posSpecs cfg20 fun c ↦ bplOf noData (6 + c)) :
    B ∈ bspecs cfg20 noData :=
  List.mem_append_left _ (List.mem_append_right _ hB)

/-- The low `m` bits field of a word is below `2^m` (`LvmFinBV.fld_lt`). -/
theorem fld_lt' (w : UInt64) {m : Nat} (hm : 1 ≤ m) (hm' : m ≤ 64) :
    ((BOut.fld 0 m 0).word w).toNat < 2 ^ m := by
  simp only [BOut.word]
  rw [UInt64.toNat_shiftRight]
  have h1 : ((64 - m - 0 : Nat).toUInt64).toNat % 64 = 64 - m := by
    rw [Nat.toUInt64_eq, UInt64.toNat_ofNat']; omega
  rw [h1, Nat.shiftRight_eq_div_pow]
  have hlt := (((w >>> (0 : Nat).toUInt64) <<< (64 - m : Nat).toUInt64)).toNat_lt
  have e : 2 ^ 64 = 2 ^ (64 - m) * 2 ^ m := by rw [← pow_add]; congr 1; omega
  rw [e] at hlt
  exact Nat.div_lt_of_lt_mul hlt

/-- **A position's two field cells add up to `kOf (posL …)`** (`posVal_of`: the position classes' `fld`
outputs on the answer lanes, the stream cells `hs`). -/
theorem posVal_on {v : ℕ → FK} (C : QCfg)
    (hout : ∀ {k l x : ℕ} {o : OpenInfo}, k < (opens C.p).length → (opens C.p).getD k default = o →
      l < QAsm.nLanes o.L.height → x < nRows o → ∀ {e : BOut × ℕ × ℕ}, e ∈ laneOuts o.L.height l →
      e.1.Valid → Out1 v (ansLane C.p (o.pe + x) + l) e.1 (posCell C k o x e))
    (hS : StreamOk C.p) (hQ : QOk C.p (lay C)) {ws : List Word}
    (hs : ∀ l < 2 ^ (lay C).m, v ((lay C).sb + l) = laneK ws l)
    {k : ℕ} (hk : k < (opens C.p).length) (hH : ((opens C.p).getD k default).L.height ≤ 64)
    {j : ℕ} (hj : j < ((opens C.p).getD k default).L.t) :
    v ((lay C).fl + posIdx C.p k j) + v ((lay C).fl + 2 ^ (lay C).pa + posIdx C.p k j) =
      kOf (posL C.p ws (((opens C.p).getD k default).pe + j / 8)
        (j % 8 * ((opens C.p).getD k default).L.height) ((opens C.p).getD k default).L.height) := by
  generalize hoD : (opens C.p).getD k default = o at hH hj ⊢
  have ho : o ∈ opens C.p := by
    rw [← hoD, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hk]; exact List.getElem_mem hk
  obtain ⟨h192, h1, hlt⟩ := open_pos_facts hS hQ ho hj
  obtain ⟨hp1, hp2, -, -, -⟩ := hQ.opens _ ho
  have hin := lanes_in hS h1 hlt
  have hT := hQ.hT
  have hx : j / 8 < nRows o := by
    have := lt_padT' hj; unfold nRows; omega
  have hj8 : j % 8 < 8 := Nat.mod_lt _ (by norm_num)
  have hji : 8 * (j / 8) + j % 8 = j := by omega
  have hsH : j % 8 * o.L.height ≤ 7 * o.L.height := Nat.mul_le_mul_right _ (by omega)
  -- the two field entries, their lanes and validity
  have hl1 : (fields o.L.height (j % 8)).1.1 < QAsm.nLanes o.L.height := by
    simp only [fields, QAsm.nLanes]; omega
  have hl2 : (fields o.L.height (j % 8)).2.1 < QAsm.nLanes o.L.height := by
    simp only [fields, QAsm.nLanes]; split_ifs <;> omega
  have hv1 : (BOut.fld (fields o.L.height (j % 8)).1.2.1 (fields o.L.height (j % 8)).1.2.2.1
      (fields o.L.height (j % 8)).1.2.2.2).Valid := by
    show _ < 64 ∧ _ ∧ _
    simp only [fields]; split_ifs <;> omega
  have hv2 : (BOut.fld (fields o.L.height (j % 8)).2.2.1 (fields o.L.height (j % 8)).2.2.2.1
      (fields o.L.height (j % 8)).2.2.2.2).Valid := by
    show _ < 64 ∧ _ ∧ _
    simp only [fields]; split_ifs <;> omega
  have o1 := hout hk hoD hl1 hx (Lvm.Fin.lo_mem o.L.height hj8) hv1
  have o2 := hout hk hoD hl2 hx (Lvm.Fin.hi_mem o.L.height hj8) hv2
  have c1 : posCell C k o (j / 8) ((BOut.fld (fields o.L.height (j % 8)).1.2.1
      (fields o.L.height (j % 8)).1.2.2.1 (fields o.L.height (j % 8)).1.2.2.2), 1, j % 8) =
      (lay C).fl + posIdx C.p k j := by
    simp only [posCell, hji, if_pos hj, ↓reduceIte, Nat.add_zero]; rfl
  have c2 : posCell C k o (j / 8) ((BOut.fld (fields o.L.height (j % 8)).2.2.1
      (fields o.L.height (j % 8)).2.2.2.1 (fields o.L.height (j % 8)).2.2.2.2), 2, j % 8) =
      (lay C).fl + 2 ^ (lay C).pa + posIdx C.p k j := by
    simp only [posCell, hji, if_pos hj]; rfl
  have hlane : ∀ l ≤ 2, ansLane C.p (o.pe + j / 8) + l < 2 ^ (lay C).m := by
    intro l hl
    simp only [ansLane, if_neg (show o.pe + j / 8 ≠ 0 by omega)]; omega
  have hl1' : (fields o.L.height (j % 8)).1.1 ≤ 2 := by
    simp only [fields]; omega
  have hl2' : (fields o.L.height (j % 8)).2.1 ≤ 2 := by
    simp only [fields]; split_ifs <;> omega
  have hs' : ∀ l < 2 ^ (lay C).m, v l = laneK ws l := fun l hl => by
    have := hs l hl; rwa [show (lay C).sb = 0 from rfl, Nat.zero_add] at this
  unfold Out1 at o1 o2
  rw [← c1, ← c2, o1, o2, hs' _ (hlane _ hl1'), hs' _ (hlane _ hl2')]
  exact Lvm.Fin.fields_posL C.p ws (o.pe + j / 8) (by omega) hH h192

section On

variable {v : ℕ → FK} (hv : OutsOn v)
include hv

/-- One output, as `Out1` (the typed rows' `out1_at`). -/
theorem out1_of {B : BSpec} (hB : B ∈ bspecs cfg20 noData) (hrd : B.rd = true) {y j : ℕ} (hy : y < B.n)
    (hj : j < B.outs.length) {A Bc : ℕ} {b : BOut} (hA : B.wc y = A) (hBc : B.oc j y = Bc) (hb : B.out j = b)
    (hvb : b.Valid) : Out1 v A b Bc := by
  obtain ⟨w, h1, h2⟩ := hv B hB y hy
  have := h2 j hj (hb ▸ hvb)
  unfold Out1
  rw [← hA, ← hBc, this, h1 hrd, hb]

/-- **Q_link's position bits are the position classes' `bit` outputs** (`posBits_of`). -/
theorem posBits_on : PosBits cfg20.p (lay cfg20) v := by
  constructor
  intro k hk j hj z hz
  obtain ⟨S, hS, -, hrd, y, hy, hwc, jo, hjo, hout, hoc⟩ :=
    posSpecs_bit cfg20 (fun c ↦ bplOf noData (6 + c)) hk (lt_padT' hj) hz
  have hA : S.wc y = (lay cfg20).sb + ansLane cfg20.p (((opens cfg20.p).getD k default).pe + j / 8) +
      (j % 8 * ((opens cfg20.p).getD k default).L.height + z) / 64 := by
    rw [hwc]; show _ = 0 + _ + _; rw [Nat.zero_add]
  exact out1_of hv (posSpecs_mem hS) hrd hy hjo hA hoc hout (Nat.mod_lt _ (by norm_num))

/-- **The bits of `s'`** (`sBits20`): the class `sSpec`. -/
theorem sBits_on : Lvm.Q1.SBitsS v (sigIn cfg20).hd (bsB cfg20) := by
  intro l hl z hz
  have hS : sSpec cfg20 (bplOf noData (6 + nPosCls cfg20)) ∈ bspecs cfg20 noData :=
    List.mem_append_right _ (by simp)
  have hlen : (sSpec cfg20 (bplOf noData (6 + nPosCls cfg20))).outs.length = 64 := by
    show ((List.range 64).map BOut.bit).length = 64; simp
  have hout : (sSpec cfg20 (bplOf noData (6 + nPosCls cfg20))).out z = .bit z := by
    show ((List.range 64).map BOut.bit).getD z (.bit 0) = .bit z
    rw [List.getD_eq_getElem _ _ (by simpa using hz)]
    simp
  exact out1_of hv hS rfl (y := l) (j := z) hl (by rw [hlen]; exact hz) rfl rfl hout (show z < 64 from hz)

/-- **The PoW fields** (`pw20`): the class `powSpec` writes the low `64 − g` bits of each opening's PoW lane. -/
theorem pw_on (hg : 1 ≤ 64 - P20.grind) :
    ∀ k < (opens P20).length, (v (pwB cfg20 + k)).val.toNat < 2 ^ (64 - P20.grind) := by
  intro k hk
  have hS : powSpec cfg20 (bplOf noData (7 + nPosCls cfg20)) ∈ bspecs cfg20 noData :=
    List.mem_append_right _ (by simp)
  have hcp : cfg20.p = P20 := rfl
  have eout : (powSpec cfg20 (bplOf noData (7 + nPosCls cfg20))).out 0 = .fld 0 (64 - cfg20.p.grind) 0 := by
    simp only [powSpec, BitsTab.BSpec.out, List.getD_cons_zero]
  have hx : k < (powSpec cfg20 (bplOf noData (7 + nPosCls cfg20))).n := by
    simp only [powSpec]; rw [hcp]; exact hk
  have h1 := out1_of hv hS rfl hx (j := 0) (Bc := pwB cfg20 + k) (by simp [powSpec]) rfl rfl eout
    (by rw [hcp]; exact ⟨by decide, hg, by omega⟩)
  unfold Out1 at h1
  rw [h1]
  show ((BOut.fld 0 (64 - cfg20.p.grind) 0).word _).toNat < _
  rw [hcp]
  exact fld_lt' _ hg (by omega)

/-- An output of a position class's row, in `Out1` form (`out1_entry`). -/
theorem out1_entryT {k l x : ℕ} {o : OpenInfo} (hk : k < (opens cfg20.p).length)
    (ho : (opens cfg20.p).getD k default = o) (hl : l < QAsm.nLanes o.L.height) (hx : x < nRows o)
    {e : BOut × ℕ × ℕ} (he : e ∈ laneOuts o.L.height l) (hve : e.1.Valid) :
    Out1 v (ansLane cfg20.p (o.pe + x) + l) e.1 (posCell cfg20 k o x e) := by
  subst ho
  obtain ⟨S, hS, -, hrd, y, hy, hwc, jo, hjo, hout, hoc⟩ :=
    posSpecs_hit cfg20 (fun c ↦ bplOf noData (6 + c)) hk hl hx he
  exact out1_of hv (posSpecs_mem hS) hrd hy hjo hwc hoc hout hve

/-- `posVal_on` on `v` (the position classes' outputs: `out1_entryT`). -/
theorem posVal_onT (hS : StreamOk cfg20.p) (hQ : QOk cfg20.p (lay cfg20)) {ws : List Word}
    (hs : ∀ l < 2 ^ (lay cfg20).m, v ((lay cfg20).sb + l) = laneK ws l)
    {k : ℕ} (hk : k < (opens cfg20.p).length) (hH : ((opens cfg20.p).getD k default).L.height ≤ 64)
    {j : ℕ} (hj : j < ((opens cfg20.p).getD k default).L.t) :
    v ((lay cfg20).fl + posIdx cfg20.p k j) + v ((lay cfg20).fl + 2 ^ (lay cfg20).pa + posIdx cfg20.p k j) =
      kOf (posL cfg20.p ws (((opens cfg20.p).getD k default).pe + j / 8)
        (j % 8 * ((opens cfg20.p).getD k default).L.height) ((opens cfg20.p).getD k default).L.height) :=
  posVal_on cfg20 (out1_entryT hv) hS hQ hs hk hH hj

end On

/-- **Q_link's position bit cells are the answers' bits** (nodeT20's `hpos`; `qin_bits`). -/
theorem hposT {v : ℕ → FK} (hv : OutsOn v) {ws : List Word} (hs : ∀ L < 2 ^ (lay cfg20).m, v ((lay cfg20).sb + L) = laneK ws L) :
    ∀ k < (opens P20).length, ∀ j < ((opens P20).getD k default).L.t, ∀ z < ((opens P20).getD k default).L.height,
      v (bitBase P20 (lay cfg20) k + ((opens P20).getD k default).L.height * j + z) =
        if ansBit P20 ws (((opens P20).getD k default).pe + j / 8) (j % 8 * ((opens P20).getD k default).L.height + z)
        then 1 else 0 :=
  qin_bits hS20 hQ20 hs (posBits_on hv)

/-- The bits of the child's `n'` (`nBits20`): Q_sig's class `sN` (`SigBits.n_bit`). -/
theorem nBits_on {v : ℕ → FK} {o : SigOut} (hsb : SigBits (sigIn cfg20) o v) :
    NBits v ((sigIn cfg20).bn + 2) P20.logN := by
  intro j hj
  have hlog : P20.logN = 20 := rfl
  rw [hlog] at hj
  exact SigBits.n_bit hsb j (show j ≤ 20 by omega)

/-- `Σ` holds the seed query: `hashedLen ≥ 6,096` (`LvmFinBV.hashedLen_ge`). -/
theorem hashedLen_ge' {p : Params} (hS : StreamOk p) : 6096 ≤ hashedLen p := by
  have h := entry_end p (i := 1) (by have := plan_length_ge p; omega)
  have h1 : ((plan p).getD 1 default).len = 6008 := by rw [plan_one]; decide
  rw [bOff_one, h1, ← hS.2] at h
  omega

/-- **`1 ≤ n' ≤ 2^logN`** (`n1_20`, `nN_20`): Q_sig's `ChildOk` on the child's header lane `n'` (stream lane 24). -/
theorem nRange_on {v : ℕ → FK} (hch : ChildOk (sigIn cfg20) v) {qr : Column 19}
    (hhd : ∀ k < 615, v ((sigIn cfg20).hd + k) = laneK (wsC qr) (11 + k)) (hL : LaneLink P20 (wsC qr))
    (vk cL : RecursionFast.Digest) :
    1 ≤ (pubOf vk cL (traceBytesB (decode P20 (wsC qr)))).n ∧
      (pubOf vk cL (traceBytesB (decode P20 (wsC qr)))).n ≤ 2 ^ P20.logN := by
  have h1 : 1 ≤ (v ((sigIn cfg20).hd + 13)).val.toNat := hch.2.2.1
  have h2 : (v ((sigIn cfg20).hd + 13)).val.toNat ≤ 2 ^ P20.logN := hch.2.2.2.1
  rw [hhd 13 (by norm_num)] at h1 h2
  have hlen := hashedLen_ge' hS20
  have hws : (wsC qr).length = 17 * 2 ^ 14 := by simp [wsC, wsOf]
  have hk := kAt_sigma P20 (wsC qr) 24 (by omega) (by omega)
  rw [traceBytesB_decode hS20 hL]
  have e : (pubOf vk cL (sigma P20 (wsC qr))).n = (laneAt (sigma P20 (wsC qr)) (headerAt 112)).toNat := rfl
  rw [e, show headerAt 112 = 8 * 24 from rfl,
    show laneAt (sigma P20 (wsC qr)) (8 * 24) = (kAt (sigma P20 (wsC qr)) (8 * 24)).val from rfl, hk]
  exact ⟨h1, h2⟩

end Lvm.NS
