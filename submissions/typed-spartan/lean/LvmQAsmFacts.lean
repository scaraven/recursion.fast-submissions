-- New for lvm (WP-16a-QFX): the static layout facts of the assembled `P20` node program
-- (`LvmQAsmProg.Q cfg20`) in the form WP-14c's `nodeSound_layout` (LvmNodeSoundLayout) asks.
import LvmQAsmV
import LvmNodeSoundLayout
import LvmVEqMid
import LvmQAsmFactsL

/-!
# The node program's layout facts

For `lay := lay cfg20`, `I := sigIn cfg20`, `qa := qarith cfg20`, `nK := nK cfg20`, `nE := 0`, the input
arrays `arrs cfg20 data20 (pubX x)` and `aux := aux cfg20 data20`:

* (the cell counts `cells_toProgram`, `nK_le_cells`, `p2_le_cells` and the region facts `hfg20 … hws20`, `hS20`,
  Q_link's `hQ20`: `LvmQAsmFactsL`, lvm2 roll 8, wave L);
* the region facts `hR20`, `hNs20`, `hP20`, `haux20`, `auxSeeds20` (rfl or small `decide`s on `cfg20`'s numbers);
* the placements of the input arrays (`hSt20 … hMd20`, A19) and the `PUB` array (`hPub20`): the
  header's lanes are the statement's public values (`hdrOfPub_pubX : hdrOfPub (pubX x) = hdrLanes x`).
-/

set_option autoImplicit false

namespace Lvm.QAsm

open RecursionFast Lvm Lvm.Replay Lvm.Loop Lvm.Loop.Build Lvm.QLink Lvm.QSig Lvm.M3 Lvm.SigBits Lvm.NS
open Lvm.VEq

/-- The node program (`nodeSound_layout`'s `Qn`). -/
abbrev Q20n : Program := Qn (lay cfg20) (sigIn cfg20) (qarith cfg20) (nK cfg20) 0

theorem Q20n_eq : Q20n = Q cfg20 := rfl

theorem sigRegLt_mono {C C' : ℕ} {I : SigIn} (h : SigRegLt C I) (hC : C ≤ C') : SigRegLt C' I :=
  ⟨by have := h.sg; omega, by have := h.bi; omega, by have := h.md; omega, by have := h.bd; omega,
    by have := h.bc; omega, by have := h.bx; omega, by have := h.be; omega, by have := h.bp; omega,
    by have := h.hd; omega, by have := h.bh; omega, by have := h.bcl; omega, by have := h.yls; omega,
    by have := h.bls; omega, by have := h.bn; omega⟩

/-- Q_sig's regions are input cells. -/
theorem sigRegLt_nK20 : SigRegLt (nK cfg20) (sigIn cfg20) :=
  ⟨by decide, by decide, by decide, by decide, by decide, by decide, by decide, by decide, by decide,
    by decide, by decide, by decide, by decide, by decide⟩

theorem hR20 : SigRegLt (Q20n.cells .K) (sigIn cfg20) := sigRegLt_mono sigRegLt_nK20 (nK_le_cells _ _ _)

theorem hNs20 : (lay cfg20).sb + 2 ^ (lay cfg20).m ≤ max (Q20n.cells .K) (Q20n.cells .E) :=
  le_trans (by decide : (lay cfg20).sb + 2 ^ (lay cfg20).m ≤ nK cfg20)
    (le_trans (nK_le_cells _ _ _) (le_max_left _ _))

theorem hP20 : (p2 (lay cfg20) (sigIn cfg20) (nK cfg20) 0).k ≤ Q20n.cells .K := p2_le_cells _ _ _ _ _

/-- **`aux` is Q_sig's six `BITS` tables, then the position classes, the `s'` bits and the PoW fields.** -/
theorem haux20 : aux cfg20 data20 =
    (sigSpecs (sigIn cfg20) (qsig (sigIn cfg20) (p1 (lay cfg20) (nK cfg20) 0)).1 (bplOf data20)).map
      BitsTab.BSpec.tab ++ ((posSpecs cfg20 fun c => bplOf data20 (6 + c)) ++
        [sSpec cfg20 (bplOf data20 (6 + nPosCls cfg20)), powSpec cfg20 (bplOf data20 (7 + nPosCls cfg20))]).map
          BitsTab.BSpec.tab := by
  unfold aux bspecs
  rw [List.append_assoc, List.map_append]
  rfl

theorem auxSeeds20 : ∀ t ∈ aux cfg20 data20, t.seeds = [] := fun t ht => by
  obtain ⟨S, -, rfl⟩ := List.mem_map.mp ht
  rfl

/-! ## The statement's header lanes -/

theorem getB_rep (n m : ℕ) (x : List UInt8) :
    (⟨(List.replicate n 0 ++ x).toArray⟩ : ByteArray).get! (n + m) = x.getD m 0 := by
  show (List.replicate n 0 ++ x).toArray[n + m]! = _
  simp [List.getElem?_append_right, List.getD_eq_getElem?_getD]
  rfl

theorem laneAt_congr {b b' : ByteArray} {o o' : ℕ} (h : ∀ i, b.get! (o + i) = b'.get! (o' + i)) :
    laneAt b o = laneAt b' o' := by
  simp only [laneAt, h]

theorem kAt_sig (x : List UInt8) (m : ℕ) : kAt (sigOfX x) (88 + m) = kAt (hdrBytesX x) (8 + m) := by
  unfold kAt
  congr 1
  refine laneAt_congr fun i => ?_
  rw [Nat.add_assoc, Nat.add_assoc]
  exact (getB_rep 88 (m + i) x).trans (getB_rep 8 (m + i) x).symm

theorem hdrLane_eq (x : List UInt8) (k : ℕ) : hdrLane x k = kAt (hdrBytesX x) (8 + 8 * k) := by
  simp only [hdrLane, kAt]
  congr 1
  exact UInt64.ofNat_toNat

theorem digestAt_getD (b : ByteArray) (o n : ℕ) (h : n < 32) :
    (digestAt b o).toArray.getD n 0 = b.get! (o + n) := by
  simp [digestAt, Array.getD, h]

theorem digestLanes_digestAt (b : ByteArray) (o : ℕ) :
    digestLanes (digestAt b o) = (List.range 4).map fun i => kAt b (o + 8 * i) := by
  unfold digestLanes
  refine List.map_congr_left fun i hi => ?_
  have hi : i < 4 := List.mem_range.mp hi
  simp only [kAt, laneAt]
  congr 1
  rw [show List.range 8 = [0, 1, 2, 3, 4, 5, 6, 7] from rfl]
  simp only [List.foldl_cons, List.foldl_nil]
  rw [digestAt_getD _ _ _ (by omega), digestAt_getD _ _ _ (by omega), digestAt_getD _ _ _ (by omega),
    digestAt_getD _ _ _ (by omega), digestAt_getD _ _ _ (by omega), digestAt_getD _ _ _ (by omega),
    digestAt_getD _ _ _ (by omega), digestAt_getD _ _ _ (by omega)]
  simp only [UInt64.zero_or, Nat.add_assoc]

/-- **The `PUB` values are the header's lanes**: V_S's public values of a statement (`pubX`,
WP-14a) in `hdrOfPub`'s order are WP-14c's `hdrLanes` (the little-endian words from byte 8). -/
theorem hdrOfPub_pubX (x : List UInt8) : hdrOfPub (pubX x) = hdrLanes x := by
  have hk : ∀ j m, headerAt j + m = 88 + (j - 8 + m) := fun j m => by simp only [headerAt]; omega
  have hL : ∀ (a n : ℕ), (List.range n).map (fun i => kAt (sigOfX x) (headerAt (8 + 8 * a) + 8 * i)) =
      (List.range n).map fun i => hdrLane x (a + i) := fun a n => List.map_congr_left fun i _ => by
    rw [hk, kAt_sig, hdrLane_eq]; congr 1; omega
  have hD : ∀ (a : ℕ), (List.range 4).map (fun i => kAt (hdrBytesX x) (8 + 8 * a + 8 * i)) =
      (List.range 4).map fun i => hdrLane x (a + i) := fun a => List.map_congr_left fun i _ => by
    rw [hdrLane_eq]; congr 1; omega
  have h0 : ∀ a, (⟨laneAt (sigOfX x) (headerAt (8 + 8 * a))⟩ : FK) = hdrLane x a := fun a => by
    have := kAt_sig x (8 * a); simp only [kAt] at this
    rw [show headerAt (8 + 8 * a) = 88 + 8 * a by simp only [headerAt]; omega, this, hdrLane_eq]; rfl
  -- A23: `acc_in`'s 29 scalars are header lanes `615 + 3i + t`
  have hE0 : ∀ i, kAt (sigOfX x) (headerAt (offAcc + eBytes * i)) = hdrLane x (615 + 3 * i) := fun i => by
    have h := hk (offAcc + eBytes * i) 0
    rw [Nat.add_zero] at h
    rw [h, kAt_sig, hdrLane_eq]; congr 1; simp only [offAcc, eBytes, sigBytes]; omega
  have hE1 : ∀ i, kAt (sigOfX x) (headerAt (offAcc + eBytes * i) + 8) = hdrLane x (615 + (3 * i + 1)) :=
    fun i => by rw [hk, kAt_sig, hdrLane_eq]; congr 1; simp only [offAcc, eBytes, sigBytes]; omega
  have hE2 : ∀ i, kAt (sigOfX x) (headerAt (offAcc + eBytes * i) + 16) = hdrLane x (615 + (3 * i + 2)) :=
    fun i => by rw [hk, kAt_sig, hdrLane_eq]; congr 1; simp only [offAcc, eBytes, sigBytes]; omega
  have hA : ∀ n, ((List.range n).map fun i => feAt (sigOfX x) (headerAt (offAcc + eBytes * i))).flatMap FE.lanes =
      (List.range (3 * n)).map fun i => hdrLane x (615 + i) := fun n => by
    induction n with
    | zero => rfl
    | succ n ih =>
      rw [List.range_succ, List.map_append, List.flatMap_append, ih,
        show 3 * (n + 1) = 3 * n + 3 by omega, List.range_add, List.map_append, List.map_map]
      congr 1
      simp only [List.map_cons, List.map_nil, List.flatMap_cons, List.flatMap_nil, List.append_nil, FE.lanes, feAt]
      rw [hE0, hE1, hE2]
      rfl
  unfold hdrLanes
  rw [show pubLanes = 1 + 4 + 4 + 4 + 1 + 4 + 597 + 3 * (accVars + 1) from rfl]
  simp only [List.range_add, List.map_append, List.map_map]
  unfold hdrOfPub pubX pubOf Pub.hdrLanes
  rw [show (List.range accVars).map (fun i => feAt (sigOfX x) (headerAt (offAcc + eBytes * i))) ++
      [feAt (sigOfX x) (headerAt (offAcc + eBytes * accVars))] =
      (List.range (accVars + 1)).map (fun i => feAt (sigOfX x) (headerAt (offAcc + eBytes * i))) from by
    rw [List.range_succ, List.map_append]; rfl, hA]
  simp only [Nat.toUInt64_eq, UInt64.ofNat_toNat]
  rw [show (hdX x).vk = digestAt (hdrBytesX x) (8 + 8 * 1) from rfl, digestLanes_digestAt, hD 1,
    show headerAt 48 = headerAt (8 + 8 * 5) from rfl, hL 5, show headerAt 80 = headerAt (8 + 8 * 9) from rfl,
    hL 9, show headerAt 120 = headerAt (8 + 8 * 14) from rfl, hL 14,
    show headerAt 152 = headerAt (8 + 8 * 18) from rfl, hL 18,
    show headerAt 8 = headerAt (8 + 8 * 0) from rfl, h0 0, show headerAt 112 = headerAt (8 + 8 * 13) from rfl,
    h0 13]
  rfl

/-! ## The input arrays' placement (A19) -/

theorem bundle_of_mem {arrs : List InArr} {s τ base : ℕ} {rec : Bool} {off : ℕ → ℕ}
    (h : ∀ l < s, ∃ a ∈ arrs, a.ty = .K ∧ a.pub = none ∧ a.τ = τ ∧ a.base = base + l ∧ a.stride = s ∧
      a.val = [(rec, off l)]) : Bundle arrs s τ base rec off := fun l hl => by
  obtain ⟨a, ha, hr⟩ := h l hl
  obtain ⟨k, hk, rfl⟩ := List.getElem_of_mem ha
  exact ⟨k, hk, hr⟩

section Arrs

variable (P : Pub)

theorem mem_arrs_st {l : ℕ} (hl : l < 17) :
    (⟨.K, cfg20.rl, l, 17, [(true, l * 2 ^ cfg20.rl)], fin data20 l, none⟩ : InArr) ∈ arrs cfg20 data20 P :=
  List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _
    (List.mem_append_left _ (List.mem_map.mpr ⟨l, List.mem_range.mpr hl, rfl⟩)))))

theorem mem_arrs_sg :
    (⟨.K, 10, sgB cfg20, 1, [(true, 17 * 2 ^ cfg20.rl)], fin data20 17, none⟩ : InArr) ∈
      arrs cfg20 data20 P :=
  List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _
    (List.mem_append_right _ (List.mem_singleton_self _)))))

theorem mem_arrs_xs {l : ℕ} (hl : l < 17) :
    (⟨.K, 9, xsB cfg20 + l, 17, [(false, xCol cfg20 l)], fin data20 (18 + l), none⟩ : InArr) ∈
      arrs cfg20 data20 P :=
  List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _
    (List.mem_append_right _ (List.mem_map.mpr ⟨l, List.mem_range.mpr hl, rfl⟩))))

theorem mem_arrs_ys {l : ℕ} (hl : l < 4) :
    (⟨.K, 9, ysB cfg20 + l, 4, [(false, ksY cfg20 l + ksSplit cfg20.p)], fin data20 (35 + l), none⟩ : InArr) ∈
      arrs cfg20 data20 P :=
  List.mem_append_left _ (List.mem_append_left _
    (List.mem_append_right _ (List.mem_map.mpr ⟨l, List.mem_range.mpr hl, rfl⟩)))

theorem mem_arrs_md {l : ℕ} (hl : l < 4) :
    (⟨.K, 0, mdB cfg20 + l, 4, [(false, ksY cfg20 l + (spongeBlocks cfg20.p - 1))], fin data20 (39 + l),
      none⟩ : InArr) ∈ arrs cfg20 data20 P :=
  List.mem_append_left _ (List.mem_append_right _ (List.mem_map.mpr ⟨l, List.mem_range.mpr hl, rfl⟩))

theorem mem_arrs_pub :
    pubArr 10 (pbB cfg20) 1 (false, 0) (fin data20 43) (hdrOfPub P) ∈ arrs cfg20 data20 P :=
  List.mem_append_right _ List.mem_cons_self

end Arrs

theorem ksY20 (l : ℕ) : ksY cfg20 l = CMain.ksYW20 l 0 := by
  simp only [ksY, cfg20, if_true]

/-- **The stream** (a 17-bundle on `C_rec`, column `l` at word `l·2^14`). -/
theorem hSt20 (x : List UInt8) :
    Bundle (arrs cfg20 data20 (pubX x)) 17 14 (lay cfg20).sb true fun l => l * 2 ^ 14 :=
  bundle_of_mem fun l hl => ⟨_, mem_arrs_st _ hl, rfl, rfl, rfl, (Nat.zero_add l).symm, rfl, rfl⟩

/-- **`σ'`** (`C_rec` word `17·2^14`). -/
theorem hSg20 (x : List UInt8) :
    Bundle (arrs cfg20 data20 (pubX x)) 1 10 (sigIn cfg20).sg true fun _ => 17 * 2 ^ 14 :=
  bundle_of_mem fun l hl => by
    obtain rfl : l = 0 := by omega
    exact ⟨_, mem_arrs_sg _, rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- **`KS`'s `X` message lanes** (a 17-bundle on `C_main`, `X_l` at `CMain.ksXW20 l 0`). -/
theorem hX20 (x : List UInt8) :
    Bundle (arrs cfg20 data20 (pubX x)) 17 9 (sigIn cfg20).xs false fun l => CMain.ksXW20 l 0 :=
  bundle_of_mem fun l hl => ⟨_, mem_arrs_xs _ hl, rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- **`KS`'s output lanes 0–3 of rows `[S, S + 2^9)`**, `S = ksSplit P20` (a 4-bundle). -/
theorem hY20 (x : List UInt8) :
    Bundle (arrs cfg20 data20 (pubX x)) 4 9 (sigIn cfg20).ys false
      fun l => CMain.ksYW20 l (ksSplit P20) :=
  bundle_of_mem fun l hl => ⟨_, mem_arrs_ys _ hl, rfl, rfl, rfl, rfl, rfl, by rw [ksY20]; rfl⟩

/-- **The trace digest** (`KS` row `B − 1`, a 4-bundle of height 1). -/
theorem hMd20 (x : List UInt8) :
    Bundle (arrs cfg20 data20 (pubX x)) 4 0 (sigIn cfg20).md false
      fun l => CMain.ksYW20 l (spongeBlocks P20 - 1) :=
  bundle_of_mem fun l hl => ⟨_, mem_arrs_md _ hl, rfl, rfl, rfl, rfl, rfl,
    by rw [ksY20, show cfg20.p = P20 from rfl]; simp only [CMain.ksYW20, Nat.add_zero]⟩

/-- **`PUB`**: the header's lanes at `pbB cfg20`. -/
theorem hPub20 (x : List UInt8) : PubAt (arrs cfg20 data20 (pubX x)) x (pbB cfg20) := by
  have h := mem_arrs_pub (pubX x)
  rw [hdrOfPub_pubX] at h
  obtain ⟨k, hk, he⟩ := List.getElem_of_mem h
  exact ⟨k, hk, _, _, he⟩

end Lvm.QAsm
