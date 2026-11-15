-- WP-14c (NodeSound, O10). New for lvm: the input map (A19) from input arrays. Committed bundles
-- of strided `K` arrays (H4's `inKOf_com`) and the header's public array (WP-9b's `inKOf_pub`, INT-2's
-- `pubArr`) give `InMapN`'s value fields on the interpreter's memory (WP-10/QL `toProgram_interp`'s
-- `Inputs`).
import LvmNodeSoundMain
import LvmCertSNodeIn

/-!
# The input map from the input arrays

* **`memN_inK`**: under `AuxHyps`, an input cell of the interpreter's memory is the input read off
  the stack (`inKOf`).
* **`Bundle arrs s τ base rec off`**: for every `l < s` a committed `K` array of height `2^τ`, first
  cell `base + l`, stride `s`, value column at word `off l` of commitment `rec`. **`bundle_cells`**:
  its cell `base + j` (`j < s·2^τ`) is word `off (j % s) + j / s` (from `inKOf_com`).
* The fields: **`stream_cells`** (a 17-bundle on `C_rec`, `off l = l·2^14`: the stream lanes `laneK`),
  **`hd_cells`**, **`sg_cells`** (`σ'`: a 1-bundle at `C_rec` word `17·2^14`), **`xs_cells`** (a 17-bundle
  on `C_main` at `CMain.ksXW20 l 0`: `msgX`), **`y_cells`** (`ys`/`yc`/`yls`/`yns`: a 4-bundle over
  `KS` rows `[S, S + 2^9)`, `S = ksSplit P20`, `off l = CMain.ksYW20 l S`), **`md_cells`** (a 4-bundle of
  height 1 at `KS` row `B − 1`).
* **`PUB`** (`hdrLanes x`: the header's 702 lanes from byte 8, V-computable from π): **`pub_cells`**,
  then **`flag_cell`**, **`vk_cells`**, **`cL_cells`**, **`sl_cells`** for `I.flag = pb`, `I.vk = pb + 1`,
  `I.cL = pb + 5`, `I.sl = pb + 18`.

All shapes above are aligned (`2^τ ∣ off`), as `LayOk` asks.
-/

set_option autoImplicit false

namespace Lvm.NS

open RecursionFast Lvm Lvm.T Lvm.ASM Lvm.Replay Lvm.Loop Lvm.Loop.Build Lvm.QLink Lvm.QSig Lvm.M3
open LeanVM.Parameters LeanVM.Protocol

/-! ## Bundles of committed arrays -/

/-- **An `s`-bundle of committed `K` input arrays**: for `l < s`, an array of height `2^τ`, first
cell `base + l`, stride `s`, value column at word `off l` of commitment `rec`. -/
def Bundle (arrs : List InArr) (s τ base : ℕ) (rec : Bool) (off : ℕ → ℕ) : Prop :=
  ∀ l < s, ∃ k, ∃ hk : k < arrs.length, arrs[k].ty = .K ∧ arrs[k].pub = none ∧ arrs[k].τ = τ ∧
    arrs[k].base = base + l ∧ arrs[k].stride = s ∧ arrs[k].val = [(rec, off l)]

section Gen

variable (Q : Program) (pl : ℕ → Var → Bool × ℕ) (groups : List Grp) (arrs : List InArr)
  (aux : List Tab) (L : Lay) (hτ : ∀ t ∈ lvmTabs Q pl groups arrs aux, t.τ ≤ L.μ)

/-- **A bundle's cells** are the commitment's words. -/
theorem bundle_cells (hok : InOk Q arrs) (hlay : LayOk L (lvmTabs Q pl groups arrs aux))
    (qm : Column L.nuMain) (qr : Column L.nuRec) {s τ base : ℕ} {rec : Bool} {off : ℕ → ℕ}
    (hb : Bundle arrs s τ base rec off) {j : ℕ} (hj : j < s * 2 ^ τ) :
    base + j < Q.nInK ∧ (inKOf Q pl groups arrs aux L hτ (stackOf L qm qr)).getD (base + j) 0 =
      FK.ofBF64 (comCell L qm qr rec (off (j % s) + j / s)) := by
  have hs : 0 < s := by
    rcases Nat.eq_zero_or_pos s with h | h
    · subst h; simp at hj
    · exact h
  obtain ⟨k, hk, hty, hpub, hτk, hbase, hstr, hval⟩ := hb (j % s) (Nat.mod_lt _ hs)
  have hx : j / s < 2 ^ arrs[k].τ := by rw [hτk]; exact Nat.div_lt_of_lt_mul hj
  have e : base + j = arrs[k].base + arrs[k].stride * (j / s) := by
    rw [hbase, hstr]; have := Nat.mod_add_div j s; omega
  refine ⟨?_, ?_⟩
  · have := hok.lt _ (List.getElem_mem hk) (j / s) hx
    rw [hty] at this; rw [e]; exact this
  · rw [e]; exact inKOf_com Q pl groups arrs aux L hτ hok hlay qm qr hk hty hpub hval hx

end Gen

/-! ## The interpreter's input cells -/

section Mem

variable {α : Type} {lay : Layout} {I : SigIn} {qa : BM α} {nK nE : ℕ}
  {pl : ℕ → Var → Bool × ℕ} {groups : List Grp} {arrs : List InArr} {aux : List Tab} {L : Lay}
  {hτ : ∀ t ∈ lvmTabs (Qn lay I qa nK nE) pl groups arrs aux, t.τ ≤ L.μ}

/-- **An input cell of the interpreter's memory is the input read off the stack.** -/
theorem memN_inK {q : Column L.μ} (H : AuxHyps (Qn lay I qa nK nE) pl groups arrs aux L hτ q)
    {n : ℕ} (hn : n < nK) :
    (memN lay I qa nK nE pl groups arrs aux L hτ q).k n =
      (inKOf (Qn lay I qa nK nE) pl groups arrs aux L hτ q).getD n 0 := by
  have hsz := And.intro (inKOf_size (Qn lay I qa nK nE) pl groups arrs aux L hτ q)
    (inEOf_size (Qn lay I qa nK nE) pl groups arrs aux L hτ q)
  obtain ⟨-, -, hin⟩ := toProgram_interp nK nE (qprog lay I qa) H.wf _ _ hsz H.inj H.inb
  exact hin.1 n hn

/-- A bundle's cells in the interpreter's memory. -/
theorem memN_bundle {qm : Column L.nuMain} {qr : Column L.nuRec}
    (H : AuxHyps (Qn lay I qa nK nE) pl groups arrs aux L hτ (stackOf L qm qr))
    (hlay : LayOk L (lvmTabs (Qn lay I qa nK nE) pl groups arrs aux)) {s τ base : ℕ} {rec : Bool}
    {off : ℕ → ℕ} (hb : Bundle arrs s τ base rec off) {j : ℕ} (hj : j < s * 2 ^ τ) :
    (memN lay I qa nK nE pl groups arrs aux L hτ (stackOf L qm qr)).k (base + j) =
      FK.ofBF64 (comCell L qm qr rec (off (j % s) + j / s)) := by
  obtain ⟨hlt, hv⟩ := bundle_cells _ pl groups arrs aux L hτ H.inOk hlay qm qr hb hj
  rw [memN_inK H hlt]; exact hv

end Mem

/-! ## The fields (on the pair's stack `stackOf lay26 qm qr`) -/

section Fields

variable {α : Type} {lay : Layout} {I : SigIn} {qa : BM α} {nK nE : ℕ}
  {pl : ℕ → Var → Bool × ℕ} {groups : List Grp} {arrs : List InArr} {aux : List Tab}
  {hτ : ∀ t ∈ lvmTabs (Qn lay I qa nK nE) pl groups arrs aux, t.τ ≤ lay26.μ}
  {qm : Column CMain.nu20} {qr : Column 19}

/-- **The stream** (a 17-bundle on `C_rec`, column `l` at word `l·2^14`): lane `j` of the child. -/
theorem stream_cells
    (H : AuxHyps (Qn lay I qa nK nE) pl groups arrs aux lay26 hτ (stackOf lay26 qm qr))
    (hlay : LayOk lay26 (lvmTabs (Qn lay I qa nK nE) pl groups arrs aux)) {sb : ℕ}
    (hb : Bundle arrs 17 14 sb true fun l => l * 2 ^ 14) {j : ℕ} (hj : j < 17 * 2 ^ 14) :
    (memN lay I qa nK nE pl groups arrs aux lay26 hτ (stackOf lay26 qm qr)).k (sb + j) =
      laneK (wsOf (Lvm.X.laneOf (wOfCol qr))) j :=
  stream_v (fun _ hj => memN_bundle H hlay hb hj) hj

/-- **The child header's cells** are the stream's lanes `11 …` (`I.hd = sb + 11`). -/
theorem hd_cells
    (H : AuxHyps (Qn lay I qa nK nE) pl groups arrs aux lay26 hτ (stackOf lay26 qm qr))
    (hlay : LayOk lay26 (lvmTabs (Qn lay I qa nK nE) pl groups arrs aux)) {sb : ℕ}
    (hb : Bundle arrs 17 14 sb true fun l => l * 2 ^ 14) (hhd : I.hd = sb + 11) :
    ∀ k < 615, (memN lay I qa nK nE pl groups arrs aux lay26 hτ (stackOf lay26 qm qr)).k (I.hd + k) =
      laneK (wsOf (Lvm.X.laneOf (wOfCol qr))) (11 + k) :=
  hd_v (fun _ hj => memN_bundle H hlay hb hj) hhd

/-- **`σ'`'s cells** (a 1-bundle at `C_rec` word `17·2^14`) hold `C_rec`'s column 17. -/
theorem sg_cells
    (H : AuxHyps (Qn lay I qa nK nE) pl groups arrs aux lay26 hτ (stackOf lay26 qm qr))
    (hlay : LayOk lay26 (lvmTabs (Qn lay I qa nK nE) pl groups arrs aux))
    (hb : Bundle arrs 1 10 I.sg true fun _ => 17 * 2 ^ 14) :
    sigAt' (memN lay I qa nK nE pl groups arrs aux lay26 hτ (stackOf lay26 qm qr)).k I.sg =
      Lvm.X.sigOfF (Lvm.X.sigCol (wOfCol qr)) :=
  sg_v (fun _ hj => memN_bundle H hlay hb hj)

/-- **`KS`'s `X` message cells** (a 17-bundle on `C_main` at `CMain.ksXW20 l 0`, KS13). -/
theorem xs_cells
    (H : AuxHyps (Qn lay I qa nK nE) pl groups arrs aux lay26 hτ (stackOf lay26 qm qr))
    (hlay : LayOk lay26 (lvmTabs (Qn lay I qa nK nE) pl groups arrs aux))
    (hb : Bundle arrs 17 9 I.xs false fun l => CMain.ksXW20 l 0) :
    ∀ r < 449, ∀ l < 17,
      (memN lay I qa nK nE pl groups arrs aux lay26 hτ (stackOf lay26 qm qr)).k (I.xs + 17 * r + l) =
        FK.ofBF64 (msgX qm r l) :=
  xs_v (fun _ hj => memN_bundle H hlay hb hj)

/-- The `Y` bundle's cells: row `ksSplit P20 + r` (`r < 2^9`). -/
theorem y_cell
    (H : AuxHyps (Qn lay I qa nK nE) pl groups arrs aux lay26 hτ (stackOf lay26 qm qr))
    (hlay : LayOk lay26 (lvmTabs (Qn lay I qa nK nE) pl groups arrs aux)) {yb : ℕ}
    (hb : Bundle arrs 4 9 yb false fun l => CMain.ksYW20 l (ksSplit P20)) {r l : ℕ}
    (hr : r < 2 ^ 9) (hl : l < 4) :
    (memN lay I qa nK nE pl groups arrs aux lay26 hτ (stackOf lay26 qm qr)).k (yb + 4 * r + l) =
      FK.ofBF64 (Yq qm (ksSplit P20 + r) l) :=
  y_v (fun _ hj => memN_bundle H hlay hb hj) hr hl

/-- **`KS`'s digest cells** (`ys`, `yc`, `yls`, `yns` from one 4-bundle over rows `[S, S + 2^9)`, `S = ksSplit P20`). -/
theorem y_cells
    (H : AuxHyps (Qn lay I qa nK nE) pl groups arrs aux lay26 hτ (stackOf lay26 qm qr))
    (hlay : LayOk lay26 (lvmTabs (Qn lay I qa nK nE) pl groups arrs aux))
    (hb : Bundle arrs 4 9 I.ys false fun l => CMain.ksYW20 l (ksSplit P20))
    (hyc : I.yc = I.ys + 4 * 430) (hyls : I.yls = I.ys + 4 * 447) (hyns : I.yns = I.ys + 4 * 448) :
    (∀ r < 399, ∀ l < 4, (memN lay I qa nK nE pl groups arrs aux lay26 hτ (stackOf lay26 qm qr)).k (I.ys + 4 * r + l) = FK.ofBF64 (Yq qm (ksSplit P20 + r) l)) ∧
    (∀ t ≤ 16, ∀ l < 4, (memN lay I qa nK nE pl groups arrs aux lay26 hτ (stackOf lay26 qm qr)).k (I.yc + 4 * t + l) = FK.ofBF64 (Yq qm (ksSplit P20 + 430 + t) l)) ∧
    (∀ l < 4, (memN lay I qa nK nE pl groups arrs aux lay26 hτ (stackOf lay26 qm qr)).k (I.yls + l) = FK.ofBF64 (Yq qm (ksSplit P20 + 447) l)) ∧
    (∀ l < 4, (memN lay I qa nK nE pl groups arrs aux lay26 hτ (stackOf lay26 qm qr)).k (I.yns + l) = FK.ofBF64 (Yq qm (ksSplit P20 + 448) l)) :=
  ys_v (fun _ hj => memN_bundle H hlay hb hj) hyc hyls hyns

/-- **The trace-digest cells** (a 4-bundle of height 1 at `KS` row `B − 1`). -/
theorem md_cells
    (H : AuxHyps (Qn lay I qa nK nE) pl groups arrs aux lay26 hτ (stackOf lay26 qm qr))
    (hlay : LayOk lay26 (lvmTabs (Qn lay I qa nK nE) pl groups arrs aux))
    (hb : Bundle arrs 4 0 I.md false fun l => CMain.ksYW20 l (spongeBlocks P20 - 1)) :
    ∀ l < 4, (memN lay I qa nK nE pl groups arrs aux lay26 hτ (stackOf lay26 qm qr)).k (I.md + l) =
      FK.ofBF64 (Yq qm (spongeBlocks P20 - 1) l) :=
  md_v (fun _ hj => memN_bundle H hlay hb hj)

/-! ### `PUB`: the header's lanes -/

/-- **A `PUB` array of the header's lanes** at `pb` (stride 1, height `2^10`). -/
def PubAt (arrs : List InArr) (x : List UInt8) (pb : ℕ) : Prop :=
  ∃ k, ∃ hk : k < arrs.length, ∃ val fin, arrs[k] = pubArr 10 pb 1 val fin (hdrLanes x)

theorem pub_cells
    (H : AuxHyps (Qn lay I qa nK nE) pl groups arrs aux lay26 hτ (stackOf lay26 qm qr))
    {x : List UInt8} {pb : ℕ} (hp : PubAt arrs x pb) {j : ℕ} (hj : j < pubLanes) :
    (memN lay I qa nK nE pl groups arrs aux lay26 hτ (stackOf lay26 qm qr)).k (pb + j) = hdrLane x j := by
  obtain ⟨k, hk, val, fin, he⟩ := hp
  have hx : j < 2 ^ arrs[k].τ := by rw [he]; show j < 2 ^ 10; rw [pubLanes_eq] at hj; omega
  have hlt := H.inOk.lt _ (List.getElem_mem hk) j hx
  rw [he] at hlt
  have hlt' : pb + j < (Qn lay I qa nK nE).nIn .K := by simpa [pubArr] using hlt
  rw [memN_inK H hlt']
  have hv := inKOf_pub _ pl groups arrs aux lay26 hτ H.inOk (stackOf lay26 qm qr) hk (by rw [he]; rfl)
    (by rw [he]; rfl) hx
  simp only [he, pubArr, Nat.one_mul] at hv
  rw [hv]
  simp [pubCell, hdrLanes, List.getD_eq_getElem?_getD, hj]

/-- **The flag** (`I.flag = pb`): `1` for a node statement. -/
theorem flag_cell
    (H : AuxHyps (Qn lay I qa nK nE) pl groups arrs aux lay26 hτ (stackOf lay26 qm qr))
    {x : List UInt8} {pb : ℕ} (hp : PubAt arrs x pb) (hfl : I.flag = pb) (hb1 : (hdrOf x).b = 1) :
    (memN lay I qa nK nE pl groups arrs aux lay26 hτ (stackOf lay26 qm qr)).k I.flag = 1 := by
  rw [hfl]; exact flag_v (fun _ hj => pub_cells H hp hj) hb1

/-- Four `PUB` cells from lane `k` hold the header's digest at byte `8 + 8k`. -/
theorem pub_digest
    (H : AuxHyps (Qn lay I qa nK nE) pl groups arrs aux lay26 hτ (stackOf lay26 qm qr))
    {x : List UInt8} {pb : ℕ} (hp : PubAt arrs x pb) {k o : ℕ} (hk : k + 4 ≤ 615) (ho : 8 + 8 * k = o) :
    digAt (memN lay I qa nK nE pl groups arrs aux lay26 hτ (stackOf lay26 qm qr)).k (pb + k) =
      digestAt (hdrBytesX x) o :=
  pub_digest_v (fun _ hj => pub_cells H hp hj) hk ho

/-- **The key's cells** (`I.vk = pb + 1`). -/
theorem vk_cells
    (H : AuxHyps (Qn lay I qa nK nE) pl groups arrs aux lay26 hτ (stackOf lay26 qm qr))
    {x : List UInt8} {pb : ℕ} (hp : PubAt arrs x pb) (hvk : I.vk = pb + 1) :
    digAt (memN lay I qa nK nE pl groups arrs aux lay26 hτ (stackOf lay26 qm qr)).k I.vk = (hdrOf x).vk := by
  rw [hvk]; exact vk_v (fun _ hj => pub_cells H hp hj)

/-- **The left statement's cells** (`I.cL = pb + 5`). -/
theorem cL_cells
    (H : AuxHyps (Qn lay I qa nK nE) pl groups arrs aux lay26 hτ (stackOf lay26 qm qr))
    {x : List UInt8} {pb : ℕ} (hp : PubAt arrs x pb) (hcL : I.cL = pb + 5) :
    digAt (memN lay I qa nK nE pl groups arrs aux lay26 hτ (stackOf lay26 qm qr)).k I.cL = (hdrOf x).cL := by
  rw [hcL]; exact cL_v (fun _ hj => pub_cells H hp hj)

/-- **The leaf signature's cells** (`I.sl = pb + 18`). -/
theorem sl_cells
    (H : AuxHyps (Qn lay I qa nK nE) pl groups arrs aux lay26 hτ (stackOf lay26 qm qr))
    {x : List UInt8} {pb : ℕ} (hp : PubAt arrs x pb) (hsl : I.sl = pb + 18) :
    sigAt' (memN lay I qa nK nE pl groups arrs aux lay26 hτ (stackOf lay26 qm qr)).k I.sl = (hdrOf x).sig := by
  rw [hsl]; exact sl_v (fun _ hj => pub_cells H hp hj)

end Fields

/-! ## `InMapN` from the arrays -/

section Assemble

variable {α : Type} {lay : Layout} {I : SigIn} {qa : BM α} {nK nE : ℕ}
  {pl : ℕ → Var → Bool × ℕ} {groups : List Grp} {arrsX : List UInt8 → List InArr} {aux : List Tab}
  {hτ' : ∀ x, ∀ t ∈ lvmTabs (Qn lay I qa nK nE) pl groups (arrsX x) aux, t.τ ≤ lay26.μ}

/-- **The input map from the input arrays**: the stream (17-bundle on `C_rec`, Q_sig's header at
lane 11), `σ'` (`C_rec` word `17·2^14`), `KS`'s `X` lanes (17-bundle) and output lanes (4-bundles on
`KS` rows `[S, S + 2^9)` (`S = ksSplit P20`) and row `B − 1`), and the header's public lanes at `pb` (flag, key,
left statement, leaf signature). -/
theorem inMapN_of {vk : RecursionFast.Digest} {x : List UInt8} {qm : Column CMain.nu20} {qr : Column 19}
    (H : AuxHyps (Qn lay I qa nK nE) pl groups (arrsX x) aux lay26 (hτ' x) (stackOf lay26 qm qr))
    (hlay : LayOk lay26 (lvmTabs (Qn lay I qa nK nE) pl groups (arrsX x) aux))
    (hws : 2 ^ lay.m ≤ 17 * 2 ^ 14)
    (hS : Bundle (arrsX x) 17 14 lay.sb true fun l => l * 2 ^ 14) (hhd : I.hd = lay.sb + 11)
    (hSg : Bundle (arrsX x) 1 10 I.sg true fun _ => 17 * 2 ^ 14)
    (hX : Bundle (arrsX x) 17 9 I.xs false fun l => CMain.ksXW20 l 0)
    (hY : Bundle (arrsX x) 4 9 I.ys false fun l => CMain.ksYW20 l (ksSplit P20))
    (hyc : I.yc = I.ys + 4 * 430) (hyls : I.yls = I.ys + 4 * 447) (hyns : I.yns = I.ys + 4 * 448)
    (hMd : Bundle (arrsX x) 4 0 I.md false
      fun l => CMain.ksYW20 l (spongeBlocks P20 - 1))
    {pb : ℕ} (hP : PubAt (arrsX x) x pb) (hfl : I.flag = pb) (hvkI : I.vk = pb + 1)
    (hcLI : I.cL = pb + 5) (hslI : I.sl = pb + 18)
    (hb1 : (hdrOf x).b = 1) (hvk : (hdrOf x).vk = vk) :
    InMapN lay I qa nK nE pl groups arrsX aux hτ' vk x qm qr := by
  have hy := y_cells H hlay hY hyc hyls hyns
  exact ⟨fun j hj => stream_cells H hlay hS (by omega), flag_cell H hP hfl hb1, xs_cells H hlay hX,
    hy.1, hy.2.1, hy.2.2.1, hy.2.2.2, (vk_cells H hP hvkI).trans hvk, cL_cells H hP hcLI,
    sl_cells H hP hslI, md_cells H hlay hMd, sg_cells H hlay hSg, hd_cells H hlay hS hhd,
    fun j hj => by rw [hfl]; exact pub_cells H hP hj⟩

end Assemble

end Lvm.NS
