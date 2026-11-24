-- New for lvm6 (WP MBT, phase 3). The mini-bus's reads read seeds (RV4 M2's bus half): on a stack where the
-- mini-bus relation holds (`M3Holds`), every row of every cap read table carries the address and value of a seed
-- row: the stream cell `sb + 16q + x'` and its stream word. Season 1's `mbRead_seeded` (`LvmNodeSoundTRd`) at
-- `mbTOf6 P wa wv`, for every `P` and words. And slot 36: the count words are disjoint from KSA's `Y` lanes.
import Lvm6NodeDeploy
import Lvm6Chk
import LvmM3Loop

/-!
# The mini-bus reads seeds (`mbRead_seeded6`, WP MBT phase 3)

* **`mbRead_seeded6`**: under `LayOk` and `M3Holds` of `inst L (mbTOf6 P wa wv)`, row `x` of read table `k` (address
  and value columns at `alignW P τ (wa k)`, `alignW P τ (wv k)`) equals some seed row `x'` of seed block `i`: the
  address is `g^(sb + 16·q_i + x')`, the value is the stream word `streamIdx (16·q_i) + x'` (WP-9's `mem_lookup`).
* **`mbCnt_ksY_disjoint`** (generic over `MbPar`, `KSTgt`, `KSCells`): if `chainB` orders `KS`'s `Y` lanes before the
  count words, no `Y` word is a finalize or count word; **`mbCnt_ksY6`** at the deployed parameters by `decide`.
-/

set_option autoImplicit false

namespace Lvm6.Node.Mb

open Lvm Lvm.M3 Lvm.Loop LeanVM.Protocol LeanVM.Parameters Lvm6.Mb

-- the plan's lists are data: never unfold them while elaborating (their facts are `mbStatic6`'s)
attribute [local irreducible] seedBlocks6 capTaus6 capRegs6

/-! ## Rows of the instance -/

section Rows

variable {L : Lay} {ts : List Tab} {hτ : ∀ t ∈ ts, t.τ ≤ L.μ}

theorem row_fixed6 (q : Column L.μ) (j : Fin ts.length) (x : Fin (2 ^ (ts.get j).τ)) (i : Fin (ts.get j).w)
    {f : ℕ → FK} (hf : (ts.get j).fixedOf i = some f) : (inst L ts hτ).row q j x i = FK.toBF64 (f x) := by
  simp only [M3Instance.row, M3Instance.column, inst, hf, Option.map_some, Option.elim_some, fixedColumn,
    Vector.get_ofFn]

theorem row_com6 (hlay : LayOk L ts) (qm : Column L.nuMain) (qr : Column L.nuRec) (j : Fin ts.length)
    (x : Fin (2 ^ (ts.get j).τ)) (i : Fin (ts.get j).w) {rec : Bool} {off : ℕ}
    (hcol : (ts.get j).cols[i.val]? = some (.com rec off)) :
    (inst L ts hτ).row (stackOf L qm qr) j x i = comCellG L qm qr rec (off + x.val) := by
  simp only [M3Instance.row]
  rw [column_stackOfG L ts hτ hlay qm qr j i hcol]
  simp [comBlockG, Vector.get]
  rfl

theorem evalV_vec_one {w : ℕ} (r : Fin w → K) (k : Key) (cnt : CPoly) :
    (evalV r (k.vec w cnt))[1] = CPoly.evalB (CPoly.ext r) k.addr := by
  simp [evalV, Key.vec, CPoly.eval_toMv]

theorem evalV_vec_three {w : ℕ} (r : Fin w → K) (k : Key) (cnt : CPoly) :
    (evalV r (k.vec w cnt))[3] = CPoly.evalB (CPoly.ext r) (k.val.getD 0 []) := by
  simp [evalV, Key.vec, CPoly.eval_toMv]

theorem evalB_var (v : ℕ → K) (i : ℕ) : CPoly.evalB v (CPoly.var i) = v i := by
  simp [CPoly.evalB, CPoly.var, FK.toBF64_one]

end Rows

/-! ## The tables' indices -/

section Idx

variable (P : MbPar) (wa wv : ℕ → ℕ)

theorem seedTabs6_length : (seedTabs6 P).length = seedBlocks6.length := by simp [seedTabs6]

theorem mbTOf6_get_seed {i : ℕ} (hi : i < seedBlocks6.length) :
    (mbTOf6 P wa wv)[i]? = some (seedArr6 P i seedBlocks6[i]).tab := by
  rw [mbTOf6, List.getElem?_append_left (by rw [seedTabs6_length]; exact hi)]
  simp [seedTabs6, List.getElem?_zipIdx, hi]

theorem mbTOf6_get_read {k : ℕ} (hk : k < capTaus6.length) :
    (mbTOf6 P wa wv)[seedBlocks6.length + k]? = some (QTyped.readTab capTaus6[k]
      (alignW P capTaus6[k] (wa k)) (alignW P capTaus6[k] (wv k)) (cnt6 P k)) := by
  rw [mbTOf6, List.getElem?_append_right (by rw [seedTabs6_length]; omega), seedTabs6_length,
    Nat.add_sub_cancel_left]
  simp [readTabs6, List.getElem?_zipIdx, hk]

/-- A table with a seed is a seed array. -/
theorem mbTOf6_seed_tab {j : ℕ} (hj : j < (mbTOf6 P wa wv).length) (hs : ((mbTOf6 P wa wv)[j]'hj).seeds ≠ []) :
    ∃ hi : j < seedBlocks6.length, (mbTOf6 P wa wv)[j]'hj = (seedArr6 P j (seedBlocks6[j]'hi)).tab := by
  rcases Nat.lt_or_ge j seedBlocks6.length with h | h
  · refine ⟨h, ?_⟩
    have e := mbTOf6_get_seed P wa wv h
    rw [List.getElem?_eq_getElem hj] at e
    exact Option.some.inj e
  · exfalso
    have hk : j - seedBlocks6.length < capTaus6.length := by
      have := hj; simp [mbTOf6, seedTabs6, readTabs6] at this; omega
    have e := mbTOf6_get_read P wa wv hk
    rw [Nat.add_sub_cancel' h, List.getElem?_eq_getElem hj] at e
    apply hs
    rw [Option.some.inj e]
    rfl

theorem mbTOf6_reads_in : ∀ t ∈ mbTOf6 P wa wv, ∀ r ∈ t.reads, r.2 < t.w := by
  intro t ht r hr
  rcases mem_mbTOf6 P wa wv ht with ⟨i, q, rfl, -, -⟩ | ⟨τ, k, rfl, -, -⟩
  · simp [InArr.tab] at hr
  · simp only [QTyped.readTab, List.mem_singleton] at hr
    subst hr
    simp only [Tab.w, QTyped.readTab, List.length_cons, List.length_nil]
    omega

/-- `(replicate n 0).sum = 0` at a variable `n` (KDN: no closed `seedBlocks6.length • 0` for the kernel to evaluate). -/
theorem sum_replicate_zero : ∀ n : ℕ, (List.replicate n 0).sum = 0
  | 0 => rfl
  | n + 1 => by rw [List.replicate_succ, List.sum_cons, sum_replicate_zero n]

theorem nReads_mbTOf6 : nReads (mbTOf6 P wa wv) = 1000 := by
  have hs : ((seedTabs6 P).map fun t ↦ t.reads.length * 2 ^ t.τ) = List.replicate seedBlocks6.length 0 := by
    simp only [seedTabs6, List.map_map]
    rw [List.eq_replicate_iff]
    refine ⟨by simp, fun n hn => ?_⟩
    obtain ⟨x, -, rfl⟩ := List.mem_map.mp hn
    simp [InArr.tab]
  have hr : ((readTabs6 P wa wv).map fun t ↦ t.reads.length * 2 ^ t.τ) = capTaus6.map (2 ^ ·) := by
    simp only [readTabs6, List.map_map]
    conv_rhs => rw [← List.zipIdx_map_fst 0 capTaus6]
    rw [List.map_map]
    exact List.map_congr_left fun x _ => by simp [QTyped.readTab]
  rw [nReads, mbTOf6, List.map_append, List.sum_append, hs, hr, mbStatic6.readLeaves, sum_replicate_zero,
    Nat.zero_add]

end Idx

/-! ## The bus half of `ReaddOk` -/

/-- A read row's tuple is a read tuple, at any tables `ts` (KDN: proved with `ts` a variable; inside
`mbRead_seeded6` the kernel checked it at `mbTOf6 P wa wv` and evaluated `seedBlocks6`). -/
theorem mem_readTuples_row (L : Lay) (ts : List Tab) (hτ : ∀ t ∈ ts, t.τ ≤ L.μ) (q : Column L.μ) {j : ℕ}
    (hj : j < ts.length) {x : ℕ} (hxj : x < 2 ^ (ts.get ⟨j, hj⟩).τ)
    (hrd : (QTyped.readKey, 2) ∈ (ts.get ⟨j, hj⟩).reads) :
    evalV ((inst L ts hτ).row q ⟨j, hj⟩ ⟨x, hxj⟩) ((ts.get ⟨j, hj⟩).readVec (QTyped.readKey, 2)) ∈
      readTuples L ts hτ q := by
  simp only [readTuples, partT, List.mem_flatMap, List.mem_map]
  refine ⟨⟨_, hj⟩, List.mem_finRange _, _, ⟨_, hrd, rfl⟩, ⟨x, hxj⟩, ?_, rfl⟩
  simp only [M3Instance.executed_eq, List.mem_map, List.mem_finRange, true_and]
  exact ⟨⟨x, by simpa [inst] using hxj⟩, rfl⟩

/-- `mbRead_seeded6` at any tables `ts` and table index `j` (KDN: checked with `ts`, `j` variables; at
`mbTOf6 P wa wv` and `seedBlocks6.length + k` the kernel evaluated `seedBlocks6`). -/
theorem mbRead_seeded6_aux (P : MbPar) (wa wv : ℕ → ℕ) (L : Lay) (ts : List Tab) (hτ : ∀ t ∈ ts, t.τ ≤ L.μ)
    (qm : Column L.nuMain) (qr : Column L.nuRec) (hlay : LayOk L ts)
    (hM : M3Holds (inst L ts hτ) () (stackOf L qm qr)) {k : ℕ} (hk : k < capTaus6.length)
    {x : ℕ} (hx : x < 2 ^ capTaus6[k]) {j : ℕ}
    (hg0 : ts[j]? = some (QTyped.readTab capTaus6[k] (alignW P capTaus6[k] (wa k)) (alignW P capTaus6[k] (wv k))
      (cnt6 P k)))
    (hin : ∀ t ∈ ts, ∀ r ∈ t.reads, r.2 < t.w) (hlen : nReads ts < 2 ^ 64 - 1)
    (hseedT : ∀ {j : ℕ} (hj : j < ts.length), (ts[j]'hj).seeds ≠ [] →
      ∃ hi : j < seedBlocks6.length, ts[j]'hj = (seedArr6 P j (seedBlocks6[j]'hi)).tab) :
    ∃ i, ∃ hi : i < seedBlocks6.length, ∃ x' < 2 ^ mbBlk6,
      comCellG L qm qr false (alignW P capTaus6[k] (wa k) + x) =
        FK.toBF64 (FK.x ^ (P.sb + 2 ^ mbBlk6 * seedBlocks6[i] + 1 * x')) ∧
      comCellG L qm qr false (alignW P capTaus6[k] (wv k) + x) =
        comCellG L qm qr false (QD.streamIdx (2 ^ mbBlk6 * seedBlocks6[i]) + x') := by
  obtain ⟨hj, hget0⟩ := List.getElem?_eq_some_iff.mp hg0
  have hget : ts.get ⟨_, hj⟩ = QTyped.readTab capTaus6[k] (alignW P capTaus6[k] (wa k))
      (alignW P capTaus6[k] (wv k)) (cnt6 P k) := by
    simp only [List.get_eq_getElem]; exact hget0
  have hτj : (ts.get ⟨_, hj⟩).τ = capTaus6[k] := by rw [hget]; rfl
  have hxj : x < 2 ^ (ts.get ⟨_, hj⟩).τ := lt_of_lt_of_eq hx (by rw [hτj])
  have hrd : (QTyped.readKey, 2) ∈ (ts.get ⟨_, hj⟩).reads := by rw [hget]; simp [QTyped.readTab]
  have hu := mem_readTuples_row L ts hτ (stackOf L qm qr) hj hxj hrd
  obtain ⟨s, hs, hks⟩ := List.mem_map.mp (mem_lookup L ts hτ (stackOf L qm qr) hM.2.1 hM.2.2.1 hin hlen _ hu)
  simp only [seedTuples, partT, List.mem_flatMap, List.mem_map] at hs
  obtain ⟨⟨jv, hjv⟩, -, v, ⟨sd, hsd, rfl⟩, x', -, rfl⟩ := hs
  have hsd0 : sd ∈ ts[jv].seeds := by simpa [List.get_eq_getElem] using hsd
  obtain ⟨hjb, hta⟩ := hseedT hjv (List.ne_nil_of_mem hsd0)
  have hgetS : ts.get ⟨jv, hjv⟩ = (seedArr6 P jv seedBlocks6[jv]).tab := by
    simp only [List.get_eq_getElem]; exact hta
  have hsd' : sd = (⟨Lvm.Loop.sep .K, CPoly.var 2, [CPoly.var 0]⟩, 1) := by
    rw [hta] at hsd0
    simpa [InArr.tab, seedArr6] using hsd0
  have hτs : (ts.get ⟨jv, hjv⟩).τ = mbBlk6 := by rw [hgetS]; rfl
  have hx'τ : x'.val < 2 ^ mbBlk6 := lt_of_lt_of_eq x'.isLt (by rw [hτs])
  refine ⟨jv, hjb, x'.val, hx'τ, ?_, ?_⟩
  · have h1 := keyT_coord hks 1 (by norm_num) (by norm_num)
    simp only [Tab.seedVec, Tab.readVec] at h1
    rw [evalV_vec_one, evalV_vec_one, hsd'] at h1
    simp only [QTyped.readKey, evalB_var, CPoly.ext] at h1
    have hw0 : 0 < (ts.get ⟨_, hj⟩).w := by rw [hget]; simp [QTyped.readTab, Tab.w]
    have hw2 : 2 < (ts.get ⟨jv, hjv⟩).w := by rw [hgetS]; simp [InArr.tab, Tab.w, InArr.vcols, seedArr6]
    rw [dif_pos hw2, dif_pos hw0] at h1
    have ec : (ts.get ⟨_, hj⟩).cols[0]? = some (.com false (alignW P capTaus6[k] (wa k))) := by
      rw [hget]; rfl
    have ef : (ts.get ⟨jv, hjv⟩).fixedOf 2 =
        some (fun y ↦ FK.x ^ (P.sb + 2 ^ mbBlk6 * seedBlocks6[jv] + 1 * y)) := by
      rw [hgetS]; rfl
    rw [row_fixed6 _ _ x' ⟨2, hw2⟩ ef, row_com6 hlay qm qr _ _ ⟨0, hw0⟩ ec] at h1
    exact h1.symm
  · have h3 := keyT_coord hks 3 (by norm_num) (by norm_num)
    simp only [Tab.seedVec, Tab.readVec] at h3
    rw [evalV_vec_three, evalV_vec_three, hsd'] at h3
    simp only [QTyped.readKey, List.getD_cons_zero, evalB_var, CPoly.ext] at h3
    have hw1 : 1 < (ts.get ⟨_, hj⟩).w := by rw [hget]; simp [QTyped.readTab, Tab.w]
    have hw0 : 0 < (ts.get ⟨jv, hjv⟩).w := by rw [hgetS]; simp [InArr.tab, Tab.w, InArr.vcols, seedArr6]
    rw [dif_pos hw0, dif_pos hw1] at h3
    have ec : (ts.get ⟨_, hj⟩).cols[1]? = some (.com false (alignW P capTaus6[k] (wv k))) := by
      rw [hget]; rfl
    have es : (ts.get ⟨jv, hjv⟩).cols[0]? =
        some (.com false (QD.streamIdx (2 ^ mbBlk6 * seedBlocks6[jv]))) := by
      rw [hgetS]; rfl
    rw [row_com6 hlay qm qr _ _ ⟨0, hw0⟩ es, row_com6 hlay qm qr _ _ ⟨1, hw1⟩ ec] at h3
    exact h3.symm

/-- **A mini-bus read row reads a seed**: on a stack where the mini-bus relation holds, row `x` of cap read table `k`
has the address `g^(sb + 16 q + x')` and the value of stream word `streamIdx (16 q) + x'`, for a seed block `q` and
`x' < 16` (season 1's `mbRead_seeded`, at stride 1). -/
theorem mbRead_seeded6 (P : MbPar) (wa wv : ℕ → ℕ) (L : Lay) (hτ : ∀ t ∈ mbTOf6 P wa wv, t.τ ≤ L.μ)
    (qm : Column L.nuMain) (qr : Column L.nuRec) (hlay : LayOk L (mbTOf6 P wa wv))
    (hM : M3Holds (inst L (mbTOf6 P wa wv) hτ) () (stackOf L qm qr)) {k : ℕ} (hk : k < capTaus6.length)
    {x : ℕ} (hx : x < 2 ^ capTaus6[k]) :
    ∃ i, ∃ hi : i < seedBlocks6.length, ∃ x' < 2 ^ mbBlk6,
      comCellG L qm qr false (alignW P capTaus6[k] (wa k) + x) =
        FK.toBF64 (FK.x ^ (P.sb + 2 ^ mbBlk6 * seedBlocks6[i] + 1 * x')) ∧
      comCellG L qm qr false (alignW P capTaus6[k] (wv k) + x) =
        comCellG L qm qr false (QD.streamIdx (2 ^ mbBlk6 * seedBlocks6[i]) + x') := by
  have hg0 := mbTOf6_get_read P wa wv hk
  have hin := mbTOf6_reads_in P wa wv
  have hlen : nReads (mbTOf6 P wa wv) < 2 ^ 64 - 1 := by rw [nReads_mbTOf6]; decide
  have hseedT : ∀ {j : ℕ} (hj : j < (mbTOf6 P wa wv).length), ((mbTOf6 P wa wv)[j]'hj).seeds ≠ [] →
      ∃ hi : j < seedBlocks6.length, (mbTOf6 P wa wv)[j]'hj = (seedArr6 P j (seedBlocks6[j]'hi)).tab :=
    fun hj hs ↦ mbTOf6_seed_tab P wa wv hj hs
  exact mbRead_seeded6_aux P wa wv L _ hτ qm qr hlay hM hk hx hg0 hin hlen hseedT

/-! ## Slot 36: the count words and `KS`'s `Y` lanes -/

/-- The finalize and count words as one region. -/
def mbCntReg (P : MbPar) : Lvm6.Node.Reg := ⟨P.cnt0, 2 ^ 12 + 2 ^ mbτMax * 40⟩

/-- `KS`'s `Y` lanes (`yLanes` lanes of `yLane` words from `yBase`). -/
def ksYReg (T : Lvm6.KSP.KSTgt) (C : Lvm6.KSP.KSCells) : Lvm6.Node.Reg := ⟨T.yBase, C.yLanes * T.yLane⟩

theorem fin6_has (P : MbPar) {i : ℕ} (hi : i < 76) {x : ℕ} (hx : x < 2 ^ mbBlk6) : (mbCntReg P).Has (fin6 P i + x) := by
  simp only [Lvm6.Node.Reg.Has, mbCntReg, fin6, mbBlk6, mbτMax] at *; omega

theorem cnt6_has (P : MbPar) {k : ℕ} (hk : k < 40) {x : ℕ} (hx : x < 2 ^ mbτMax) : (mbCntReg P).Has (cnt6 P k + x) := by
  simp only [Lvm6.Node.Reg.Has, mbCntReg, cnt6, mbτMax] at *
  have : 64 * k + 64 ≤ 64 * 40 := by omega
  omega

theorem ksY_has (T : Lvm6.KSP.KSTgt) (C : Lvm6.KSP.KSCells) {l r : ℕ} (hl : l < C.yLanes) (hr : r < T.yLane) :
    (ksYReg T C).Has (T.yBase + l * T.yLane + r) := by
  simp only [Lvm6.Node.Reg.Has, ksYReg]
  refine ⟨by omega, ?_⟩
  have : l * T.yLane + T.yLane ≤ C.yLanes * T.yLane := by
    have := Nat.mul_le_mul_right T.yLane (Nat.succ_le_of_lt hl); rw [Nat.succ_mul] at this; exact this
  omega

/-- **The count words are not `Y` words** (generic): if `chainB` orders the `Y` lanes before the count words, no
`Y` word (lane `l < yLanes`, row `r < yLane`) is a finalize or count word. -/
theorem mbCnt_ksY_disjoint (P : MbPar) (T : Lvm6.KSP.KSTgt) (C : Lvm6.KSP.KSCells) {N : ℕ}
    (h : Lvm6.Node.chainB 0 [ksYReg T C, mbCntReg P] N = true) {l r : ℕ} (hl : l < C.yLanes) (hr : r < T.yLane) :
    ¬ (mbCntReg P).Has (T.yBase + l * T.yLane + r) :=
  Lvm6.Node.Reg.disjoint (i := 0) (j := 1) h (by norm_num) (by simp) (ksY_has T C hl hr)

/-- **The deployed instance**: `KS`'s `Y` lanes (slot 36 below word `2^18`) end before the count words. -/
theorem mbCnt_ksY6 (lay : Lvm.Typed.Lay) :
    Lvm6.Node.chainB 0 [ksYReg Dep.ksT18 Dep.ksC18, mbCntReg (Dep.mbPar6 lay)] (2 ^ 25) = true := by
  dsimp only [Dep.mbPar6, mbCntReg]; decide

end Lvm6.Node.Mb
