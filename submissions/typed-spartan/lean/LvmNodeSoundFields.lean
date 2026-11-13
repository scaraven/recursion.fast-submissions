-- WP-14c (NodeSound, O10); lvm2 roll 8 (B1, L-D): the input map's fields on any memory. Split out of
-- `LvmNodeSoundIn` (the lane/digest/signature conversions, unchanged) and `LvmNodeSoundMain` (`hdrBytesX`,
-- `hdrLane`), so that the typed backend's `NodeSound` (`LvmNodeSoundT`, the memory `memOf lay z`) reads them without
-- the bus path's interpreter memory `memN`.
import LvmNodeSoundKS
import LvmNodeSoundHdr

/-!
# The input map's fields on a memory

A memory's `K` cells `v` hold:

* **`CellsAt v L qm qr s τ base rec off`** (an `s`-bundle of a commitment's columns): cell `base + j` (`j < s·2^τ`)
  is word `off (j % s) + j / s` of commitment `rec` of the pair `(qm, qr)`;
* **`PubCells v x pb`**: cell `pb + j` (`j < pubLanes`) is the header's lane `j` (`hdrLane x j`).

From these, as `LvmNodeSoundIn`'s fields on the bus path's memory (which now read them): **`stream_v`** (a 17-bundle on
`C_rec`), **`hd_v`**, **`sg_v`** (`σ'`), **`xs_v`**, **`y_v`** (a `ys` word), **`ys_v`** (`ys`, `yc`, `yls`, `yns`),
**`md_v`**, **`flag_v`**, **`pub_digest_v`**, **`vk_v`**, **`cL_v`**, **`sl_v`**.
-/

set_option autoImplicit false

namespace Lvm.NS

open RecursionFast Lvm Lvm.T Lvm.ASM Lvm.Replay Lvm.Loop Lvm.Loop.Build Lvm.QLink Lvm.QSig Lvm.M3
open LeanVM.Parameters LeanVM.Protocol

/-! ## `okS` facts -/

theorem okS_vk {vk c : RecursionFast.Digest} {x : List UInt8} (hok : okS vk c x = true) :
    (hdrOf x).vk = vk := by
  unfold okS at hok
  generalize hdrOf x = hd at hok ⊢
  simp only [Bool.and_eq_true, beq_iff_eq] at hok
  exact hok.1.1.1.2

theorem okS_sig {vk c : RecursionFast.Digest} {x : List UInt8} (hok : okS vk c x = true)
    (hb : (hdrOf x).b = 1) : SigOk vk (traceDigest []) (hdrOf x).sig = true := by
  unfold okS at hok
  generalize hdrOf x = hd at hok hb ⊢
  simp only [Bool.and_eq_true, hb, one_ne_zero, if_false] at hok
  exact hok.2.2

/-! ## The header's lanes -/

/-- The statement's bytes where the header reader finds them (`hdrOf x = Header.ofProof (hdrBytesX x)`). -/
def hdrBytesX (x : List UInt8) : ByteArray := ⟨(List.replicate 8 0 ++ x).toArray⟩

/-- **Header lane `k`** of a statement: the little-endian word at byte `8 + 8k`. -/
def hdrLane (x : List UInt8) (k : ℕ) : FK := ⟨UInt64.ofNat (u64At (hdrBytesX x) (8 + 8 * k))⟩

/-- **The header's 702 lanes** (`b`, `vk`, `c_L`, `s`, `n`, `h`, `σ_leaf`: 615; A23: `acc_in`'s 29
scalars, 87): the `PUB` values (`pubLanes`; `= (pubX x).hdrLanes`, `LvmAccNodePub.hdrLanes_eq_pubX`). -/
def hdrLanes (x : List UInt8) : List FK := (List.range pubLanes).map (hdrLane x)

theorem lt_pubLanes {j : ℕ} (h : j < 615) : j < pubLanes := by rw [pubLanes_eq]; omega

theorem u64At_lt (b : ByteArray) (o : ℕ) : u64At b o < 2 ^ 64 := UInt64.toNat_lt _

theorem toNat_hdrLane (x : List UInt8) (k : ℕ) : (hdrLane x k).val.toNat = u64At (hdrBytesX x) (8 + 8 * k) :=
  UInt64.toNat_ofNat_of_lt' (u64At_lt _ _)

theorem byteW_hdrLane (x : List UInt8) (k : ℕ) {t : ℕ} (ht : t < 8) :
    (hdrBytesX x).get! (8 + 8 * k + t) = Lvm.Bits.byteW (hdrLane x k).val t := by
  rw [Lvm.Wots.byteW_toNat _ ht, toNat_hdrLane,
    ← RecursionFast.toUInt8_mod, u64At_eq, ofLE_div_mod]
  simp [List.getD_eq_getElem?_getD, ht]

theorem pub_bytes (x : List UInt8) :
    ∀ k < 615, ∀ t < 8, (hdrBytesX x).get! (8 + 8 * k + t) = Lvm.Bits.byteW (hdrLane x k).val t :=
  fun k _ t ht => byteW_hdrLane x k ht

theorem digOfW_congr {f g : ℕ → UInt64} (h : ∀ l < 4, f l = g l) : Lvm.Wots.digOfW f = Lvm.Wots.digOfW g := by
  refine Vector.ext fun i hi => ?_
  rw [Lvm.Wots.digOfW_get _ hi, Lvm.Wots.digOfW_get _ hi, h _ (by omega)]

/-! ## Lanes, digests and signatures -/

/-- The stream lanes of the child, as lanes. -/
theorem laneK_wsOf (qr : Column 19) {j : ℕ} (hj : j < 17 * 2 ^ 14) :
    laneK (wsOf (Lvm.X.laneOf (wOfCol qr))) j = FK.ofBF64 (wd qr (Lvm.X.crecIdx j)) := by
  simp only [laneK, wsOf, List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range hj,
    Option.map_some, Option.getD_some, Lvm.X.laneOf, wOfCol, FK.ofBF64, wd]

theorem byteW_toBitVec {u : UInt64} {w : Word} (h : u.toBitVec = w) {t : ℕ} (ht : t < 8) :
    Lvm.Bits.byteW u t = (wordsBytes [w]).getD t 0 := by
  have e := byte_of_lane [w] 0 t ht
  simp only [Nat.mul_zero, Nat.zero_add] at e
  rw [e, Lvm.Wots.byteW_toNat _ ht, ← RecursionFast.toUInt8_mod]
  simp [lw, ← h]

/-- **Four cells whose words are `f c … f (c+3)` hold the digest `digW (wsAt f c 4)`.** -/
theorem digAt_eq_digW {v : ℕ → FK} {a : ℕ} {f : ℕ → Word} {c : ℕ}
    (h : ∀ l < 4, (v (a + l)).val.toBitVec = f (c + l)) : digAt v a = Lvm.X.digW (Lvm.X.wsAt f c 4) := by
  refine Vector.ext fun i hi => ?_
  rw [digAt, Lvm.Wots.digOfW_get _ hi]
  simp only [Lvm.X.digW, Vector.getElem_ofFn]
  have hq : i / 8 < 4 := by omega
  have h8 : i % 8 < 8 := Nat.mod_lt _ (by omega)
  conv_rhs => rw [show i = 8 * (i / 8) + i % 8 by omega]
  rw [byte_of_lane _ _ _ h8, Lvm.Wots.byteW_toNat _ h8, ← RecursionFast.toUInt8_mod]
  have hw : (Lvm.X.wsAt f c 4).getD (i / 8) 0 = f (c + i / 8) := by
    simp [Lvm.X.wsAt, List.getD_eq_getElem?_getD, hq]
  have hv : (v (a + i / 8)).val.toNat = (f (c + i / 8)).toNat := by rw [← h _ hq]; rfl
  rw [hv, lw, hw]

/-- **Cells whose words are `f 0 … f 596` hold the signature `sigOfF f`.** -/
theorem sigAt'_eq_sigOfF {v : ℕ → FK} {a : ℕ} {f : ℕ → Word}
    (h : ∀ j < 597, (v (a + j)).val.toBitVec = f j) : sigAt' v a = Lvm.X.sigOfF f := by
  have h0 := h 0 (by omega)
  rw [Nat.add_zero] at h0
  have e1 : (v a).val.toNat = (f 0).toNat := by rw [← h0]; rfl
  have e2 : ((List.range wotsLen).map fun i => digAt v (a + 1 + 4 * i)) =
      (List.range wotsLen).map fun k => Lvm.X.digW (Lvm.X.wsAt f (1 + 4 * k) 4) := by
    refine List.map_congr_left fun i hi => ?_
    have hi' : i < 133 := by simpa [wotsLen] using List.mem_range.mp hi
    exact digAt_eq_digW fun l hl => by
      rw [show a + 1 + 4 * i + l = a + (1 + 4 * i + l) by omega]; exact h _ (by omega)
  have e3 : ((List.range sigHeight).map fun t => digAt v (a + 533 + 4 * t)) =
      (List.range sigHeight).map fun k => Lvm.X.digW (Lvm.X.wsAt f (1 + 4 * wotsLen + 4 * k) 4) := by
    refine List.map_congr_left fun t ht => ?_
    have ht' : t < 16 := by simpa [sigHeight] using List.mem_range.mp ht
    refine digAt_eq_digW fun l hl => ?_
    rw [show a + 533 + 4 * t + l = a + (533 + 4 * t + l) by omega, h _ (by omega)]
    congr 1
  unfold sigAt' Lvm.X.sigOfF
  rw [e1, e2, e3]

/-- `KS`'s output lane `l < 4` of row `i` is the `C_main` word `CMain.ksYW20 l i` (KS slot `50 + l`; KS13). -/
theorem Yq_eq (qm : Column CMain.nu20) (i : ℕ) {l : ℕ} (hl : l < 4) :
    Yq qm i l = wd qm (CMain.ksYW20 l i) := by
  simp only [Yq, Lvm.KG.ksYRow, Lvm.KG.ksY, if_pos (show l < 14 by omega), ksCol, CMain.ksYW20_eq]
  congr 1; simp only [CMain.ksOff20]; ring

/-! ## Words of the commitments -/

theorem wd_eq {n : ℕ} (q : Column n) {i : ℕ} (hi : i < 2 ^ n) : wd q i = q.values[i] := by
  rcases q with ⟨v⟩
  show Vector.getD v i 0 = v[i]
  unfold Vector.getD
  rw [Array.getD_eq_getD_getElem?]
  simp only [Vector.getElem?_toArray]
  rw [Vector.getElem?_eq_getElem hi]
  rfl

theorem comCell_rec {L : Lay} (qm : Column L.nuMain) (qr : Column L.nuRec) {n : ℕ} (hn : n < 2 ^ L.nuRec) :
    comCell L qm qr true n = wd qr n := by
  simp [comCell, hn, wd_eq qr hn]

theorem comCell_main {L : Lay} (qm : Column L.nuMain) (qr : Column L.nuRec) {n : ℕ}
    (hn : n < 2 ^ L.nuMain) : comCell L qm qr false n = wd qm n := by
  simp [comCell, hn, wd_eq qm hn]

/-! ## The fields on a memory's `K` cells -/

/-- **An `s`-bundle of a commitment's columns** in the cells `v`: cell `base + j` is word `off (j % s) + j / s` of
commitment `rec`. -/
def CellsAt (v : ℕ → FK) (L : Lay) (qm : Column L.nuMain) (qr : Column L.nuRec) (s τ base : ℕ) (rec : Bool)
    (off : ℕ → ℕ) : Prop :=
  ∀ j < s * 2 ^ τ, v (base + j) = FK.ofBF64 (comCell L qm qr rec (off (j % s) + j / s))

/-- **The header's lanes** in the cells `v` from `pb`. -/
def PubCells (v : ℕ → FK) (x : List UInt8) (pb : ℕ) : Prop := ∀ j < pubLanes, v (pb + j) = hdrLane x j

section Fields

variable {v : ℕ → FK} {qm : Column CMain.nu20} {qr : Column 19}

/-- **The stream** (a 17-bundle on `C_rec`, column `l` at word `l·2^14`): lane `j` of the child. -/
theorem stream_v {sb : ℕ} (hb : CellsAt v lay26 qm qr 17 14 sb true fun l => l * 2 ^ 14) {j : ℕ}
    (hj : j < 17 * 2 ^ 14) : v (sb + j) = laneK (wsOf (Lvm.X.laneOf (wOfCol qr))) j := by
  have h := hb j hj
  beta_reduce at h
  rw [h, laneK_wsOf qr hj, comCell_rec (L := lay26) qm qr (by show _ < 2 ^ 19; omega)]
  rfl

/-- **The child header's cells** are the stream's lanes `11 …`. -/
theorem hd_v {sb hd : ℕ} (hb : CellsAt v lay26 qm qr 17 14 sb true fun l => l * 2 ^ 14) (hhd : hd = sb + 11) :
    ∀ k < 615, v (hd + k) = laneK (wsOf (Lvm.X.laneOf (wOfCol qr))) (11 + k) := fun k hk => by
  rw [hhd, Nat.add_assoc]; exact stream_v hb (by omega)

/-- **`σ'`'s cells** (a 1-bundle at `C_rec` word `17·2^14`) hold `C_rec`'s column 17. -/
theorem sg_v {sg : ℕ} (hb : CellsAt v lay26 qm qr 1 10 sg true fun _ => 17 * 2 ^ 14) :
    sigAt' v sg = Lvm.X.sigOfF (Lvm.X.sigCol (wOfCol qr)) := by
  refine sigAt'_eq_sigOfF fun j hj => ?_
  rw [hb j (by omega)]
  simp only [Nat.div_one]
  rw [comCell_rec (L := lay26) qm qr (by show _ < 2 ^ 19; omega)]
  rfl

/-- **`KS`'s `X` message cells** (a 17-bundle on `C_main` at `CMain.ksXW20 l 0`, KS13). -/
theorem xs_v {xs : ℕ} (hb : CellsAt v lay26 qm qr 17 9 xs false fun l => CMain.ksXW20 l 0) :
    ∀ r < 449, ∀ l < 17, v (xs + 17 * r + l) = FK.ofBF64 (msgX qm r l) := fun r hr l hl => by
  have hm : (17 * r + l) % 17 = l := by omega
  have hd : (17 * r + l) / 17 = r := by omega
  have h := hb (17 * r + l) (by omega)
  beta_reduce at h
  rw [Nat.add_assoc, h, hm, hd,
    comCell_main (L := lay26) qm qr (by show _ < 2 ^ 23; rw [CMain.ksXW20_eq]; omega)]
  simp only [msgX, CMain.ksXW20_eq, Nat.add_zero]

/-- The `Y` bundle's cells: row `ksSplit P20 + r` (`r < 2^9`). -/
theorem y_v {yb : ℕ} (hb : CellsAt v lay26 qm qr 4 9 yb false fun l => CMain.ksYW20 l (ksSplit P20)) {r l : ℕ}
    (hr : r < 2 ^ 9) (hl : l < 4) : v (yb + 4 * r + l) = FK.ofBF64 (Yq qm (ksSplit P20 + r) l) := by
  have hm : (4 * r + l) % 4 = l := by omega
  have hd : (4 * r + l) / 4 = r := by omega
  have h := hb (4 * r + l) (by omega)
  beta_reduce at h
  rw [Nat.add_assoc, h, hm, hd,
    comCell_main (L := lay26) qm qr (by show _ < 2 ^ 23; rw [CMain.ksYW20_eq, ksSplit_P20]; omega), Yq_eq qm _ hl]
  congr 2; simp only [CMain.ksYW20_eq]; ring

/-- **`KS`'s digest cells** (`ys`, `yc`, `yls`, `yns` from one 4-bundle over rows `[S, S + 2^9)`, `S = ksSplit P20`). -/
theorem ys_v {ys yc yls yns : ℕ} (hb : CellsAt v lay26 qm qr 4 9 ys false fun l => CMain.ksYW20 l (ksSplit P20))
    (hyc : yc = ys + 4 * 430) (hyls : yls = ys + 4 * 447) (hyns : yns = ys + 4 * 448) :
    (∀ r < 399, ∀ l < 4, v (ys + 4 * r + l) = FK.ofBF64 (Yq qm (ksSplit P20 + r) l)) ∧
    (∀ t ≤ 16, ∀ l < 4, v (yc + 4 * t + l) = FK.ofBF64 (Yq qm (ksSplit P20 + 430 + t) l)) ∧
    (∀ l < 4, v (yls + l) = FK.ofBF64 (Yq qm (ksSplit P20 + 447) l)) ∧
    (∀ l < 4, v (yns + l) = FK.ofBF64 (Yq qm (ksSplit P20 + 448) l)) := by
  refine ⟨fun r hr l hl => y_v hb (by omega) hl, fun t ht l hl => ?_, fun l hl => ?_, fun l hl => ?_⟩
  · rw [hyc, show ys + 4 * 430 + 4 * t = ys + 4 * (430 + t) by ring,
      show ksSplit P20 + 430 + t = ksSplit P20 + (430 + t) by omega]
    exact y_v hb (by omega) hl
  · rw [hyls]; exact y_v hb (by omega) hl
  · rw [hyns]; exact y_v hb (by omega) hl

/-- **The trace-digest cells** (a 4-bundle of height 1 at `KS` row `B − 1`). -/
theorem md_v {md : ℕ} (hb : CellsAt v lay26 qm qr 4 0 md false fun l => CMain.ksYW20 l (spongeBlocks P20 - 1)) :
    ∀ l < 4, v (md + l) = FK.ofBF64 (Yq qm (spongeBlocks P20 - 1) l) := fun l hl => by
  have hB : spongeBlocks P20 = 6205 := sizes_P20.2.2.2.2.2.2.2.2
  have h := hb l (by omega)
  beta_reduce at h
  rw [h, Nat.mod_eq_of_lt hl, Nat.div_eq_of_lt hl, Nat.add_zero,
    comCell_main (L := lay26) qm qr (by show _ < 2 ^ 23; rw [CMain.ksYW20_eq, hB]; omega), Yq_eq qm _ hl]

/-- **The flag** (`PUB` lane 0): `1` for a node statement. -/
theorem flag_v {x : List UInt8} {pb : ℕ} (hp : PubCells v x pb) (hb1 : (hdrOf x).b = 1) : v pb = 1 := by
  have h0 := hp 0 (lt_pubLanes (by omega))
  rw [Nat.add_zero] at h0
  rw [h0]
  have e : u64At (hdrBytesX x) 8 = 1 := hb1
  simp only [hdrLane, Nat.mul_zero, Nat.add_zero, e]
  rfl

/-- Four `PUB` cells from lane `k` hold the header's digest at byte `8 + 8k`. -/
theorem pub_digest_v {x : List UInt8} {pb : ℕ} (hp : PubCells v x pb) {k o : ℕ} (hk : k + 4 ≤ 615)
    (ho : 8 + 8 * k = o) : digAt v (pb + k) = digestAt (hdrBytesX x) o := by
  rw [← ho, digestAt_of (pub_bytes x) hk]
  refine digOfW_congr fun l hl => ?_
  rw [Nat.add_assoc, hp _ (lt_pubLanes (by omega))]

/-- **The key's cells** (`PUB` lanes 1–4). -/
theorem vk_v {x : List UInt8} {pb : ℕ} (hp : PubCells v x pb) : digAt v (pb + 1) = (hdrOf x).vk :=
  pub_digest_v hp (by omega) rfl

/-- **The left statement's cells** (`PUB` lanes 5–8). -/
theorem cL_v {x : List UInt8} {pb : ℕ} (hp : PubCells v x pb) : digAt v (pb + 5) = (hdrOf x).cL :=
  pub_digest_v hp (by omega) rfl

/-- **The leaf signature's cells** (`PUB` lanes 18–614). -/
theorem sl_v {x : List UInt8} {pb : ℕ} (hp : PubCells v x pb) : sigAt' v (pb + 18) = (hdrOf x).sig := by
  have hv : ∀ j < 597, v (pb + 18 + j) = hdrLane x (18 + j) := fun j hj => by
    rw [Nat.add_assoc]; exact hp _ (lt_pubLanes (by omega))
  have e1 : (v (pb + 18)).val.toNat = u64At (hdrBytesX x) 152 := by
    have h0 := hv 0 (by omega); rw [Nat.add_zero] at h0; rw [h0, toNat_hdrLane]
  have e2 : ((List.range wotsLen).map fun i => digAt v (pb + 18 + 1 + 4 * i)) =
      (List.range wotsLen).map fun k => digestAt (hdrBytesX x) (152 + 8 + 32 * k) := by
    refine List.map_congr_left fun i hi => ?_
    have hi' : i < 133 := by simpa [wotsLen] using List.mem_range.mp hi
    rw [show pb + 18 + 1 + 4 * i = pb + (19 + 4 * i) by omega]
    exact pub_digest_v hp (by omega) (by omega)
  have e3 : ((List.range sigHeight).map fun t => digAt v (pb + 18 + 533 + 4 * t)) =
      (List.range sigHeight).map fun k => digestAt (hdrBytesX x) (152 + 8 + 32 * wotsLen + 32 * k) := by
    refine List.map_congr_left fun t ht => ?_
    have ht' : t < 16 := by simpa [sigHeight] using List.mem_range.mp ht
    rw [show pb + 18 + 533 + 4 * t = pb + (551 + 4 * t) by omega]
    exact pub_digest_v hp (by omega) (by simp only [wotsLen]; omega)
  have hs : (hdrOf x).sig = sigAt (hdrBytesX x) 152 := rfl
  rw [hs]
  unfold sigAt' sigAt
  rw [e1, e2, e3]

end Fields

end Lvm.NS
