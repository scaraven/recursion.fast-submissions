-- New for lvm2 E2-FT (E2F-QH6): the facts S2GF's typed HAR (`harithF20`, E2F-C) reads besides the gadgets' phase
-- lemmas: the child's stream on the node memory (`Streamed`), `Σ'`'s size, the incoming accumulator from `PUB` at
-- `acc_in` of 44 coordinates, and V's proof-of-work checks on the ground answers from the PoW blocks (`powBlk_ok`).
import LvmE2QNodeG
import LvmE2QWPhase
import LvmQAsmHarTails
import LvmQTypedHarS

/-!
# The HAR's facts at S2GF

* **`sigCF qr`**: the child's trace bytes `Σ'` at S2GF; **`sigCF_size`**: `|Σ'| = hashedLen P20F`.
* **`streamedF`**: the node memory's stream cells are `Σ'`'s lanes (`Streamed … (streamLanes P20F)`).
* **`accCA n M pb`**: `acc_in` read off its `PUB` cells at `n` coordinates (`accC` at `accVars`, `accCA_accVars`);
  **`accCA_pubXF`**: at `accVF = 44` it is the statement's `(pubXF x).accIn`.
* **`powOk_of_blks`**: on a layout built with `specQF … pw`, where the coordinate-split relation holds, every
  answer `(q, g)` of `pw` whose lanes are streamed has V's check `powOKR g (feAt Σ (8q))`; so `PowOkV (feAt Σ) L` for
  every challenge list `L ⊆ pw`.
-/

set_option autoImplicit false

namespace Lvm.E2Q

open RecursionFast Lvm Lvm.T Lvm.Loop Lvm.Loop.Build Lvm.QLink Lvm.QAsm Lvm.NS Lvm.Typed Lvm.QTyped
open Lvm.VEq (pubXF)
open LeanVM.Protocol (Column)

/-! ## `Σ'` and the stream -/

/-- **The child's trace bytes `Σ'`** of a `C_rec` candidate at S2GF. -/
abbrev sigCF (qr : Column 19) : ByteArray := traceBytesB (decode P20F (wsC qr))

/-- `|Σ'| = hashedLen P20F` on a linked stream. -/
theorem sigCF_size {qr : Column 19} (hL : LaneLink P20F (wsC qr)) : (sigCF qr).size = hashedLen P20F := by
  rw [sigCF, traceBytesB_decode streamOk_P20F hL, Lvm.Har.sigma_sizeT hL.size]

/-- **The node memory streams `Σ'`** (`streamed_child` at `cfgF20`, `T = streamLanes P20F = 73,001`). -/
theorem streamedF {M : Mem} {qr : Column 19}
    (hst : ∀ j < 2 ^ (lay cfgF20).m, M.k ((lay cfgF20).sb + j) = laneK (wsC qr) j) (hL : LaneLink P20F (wsC qr)) :
    Lvm.Q1.Streamed M (sigCF qr) (streamLanes P20F) := by
  have hh : hashedLen P20F = 584008 := spongeBlocks_P20F.2
  have hw : (wsC qr).length = 17 * 2 ^ 14 := by rw [wsC, wsOf, List.length_map, List.length_range]
  have h := Lvm.Har.streamed_child cfgF20 streamOk_P20F hL hst (T := streamLanes P20F)
    (by rw [streamLanes, hh]; decide) (by rw [show cfgF20.p = P20F from rfl, streamLanes]; omega)
    (by rw [streamLanes, hh, hw]; norm_num)
  rwa [show cfgF20.p = P20F from rfl] at h

/-! ## `acc_in` from `PUB` at 44 coordinates -/

/-- **`acc_in` read off its `PUB` cells** at `n` coordinates (three lanes per scalar from `pb + 615`). -/
def accCA (n : ℕ) (M : Mem) (pb : ℕ) : Acc :=
  ⟨(List.range n).map fun i => ⟨M.k (pb + 615 + 3 * i), M.k (pb + 615 + 3 * i + 1), M.k (pb + 615 + 3 * i + 2)⟩,
    ⟨M.k (pb + 615 + 3 * n), M.k (pb + 615 + 3 * n + 1), M.k (pb + 615 + 3 * n + 2)⟩⟩

theorem accCA_accVars (M : Mem) (pb : ℕ) : accCA accVars M pb = Lvm.QAcc.accC M pb := rfl

/-- `PUB` cell `pb + 615 + 3i + t` is the header's word at stream byte `headerAt (offAcc + 24 i) + 8 t`. -/
theorem pub_acc_lane {M : Mem} {x : List UInt8} {pb : ℕ}
    (hpub : ∀ j < pubLanesX accVF, M.k (pb + j) = hdrLane x j) {i t : ℕ} (hi : i ≤ accVF) (ht : t < 3) :
    M.k (pb + 615 + 3 * i + t) = kAt (Lvm.VEq.sigOfX x) (headerAt (offAcc + eBytes * i) + 8 * t) := by
  have hj : 615 + 3 * i + t < pubLanesX accVF := by
    unfold pubLanesX; rw [show accVF = 44 from rfl] at hi ⊢; omega
  rw [show pb + 615 + 3 * i + t = pb + (615 + 3 * i + t) by omega, hpub _ hj, hdrLane_eq_kAt]
  congr 1
  simp only [headerAt, offAcc, eBytes, sigBytes]
  omega

/-- **`acc_in` from `PUB` at S2GF** is the statement's (`accVF = 44` coordinates, `pubLanesX 44 = 750` lanes). -/
theorem accCA_pubXF {M : Mem} {x : List UInt8} {pb : ℕ}
    (hpub : ∀ j < pubLanesX accVF, M.k (pb + j) = hdrLane x j) : accCA accVF M pb = (pubXF x).accIn := by
  have e : (pubXF x).accIn = ⟨(List.range accVF).map fun i =>
      feAt (Lvm.VEq.sigOfX x) (headerAt (offAcc + eBytes * i)),
      feAt (Lvm.VEq.sigOfX x) (headerAt (offAcc + eBytes * accVF))⟩ := rfl
  rw [e]
  unfold accCA
  congr 1
  · refine List.map_congr_left fun i hi => ?_
    have hi' : i ≤ accVF := Nat.le_of_lt (List.mem_range.mp hi)
    have h0 := pub_acc_lane hpub hi' (t := 0) (by omega)
    have h1 := pub_acc_lane hpub hi' (t := 1) (by omega)
    have h2 := pub_acc_lane hpub hi' (t := 2) (by omega)
    rw [Nat.add_zero, Nat.mul_zero, Nat.add_zero] at h0
    rw [h0, h1, h2]
    rfl
  · have h0 := pub_acc_lane hpub (le_refl accVF) (t := 0) (by omega)
    have h1 := pub_acc_lane hpub (le_refl accVF) (t := 1) (by omega)
    have h2 := pub_acc_lane hpub (le_refl accVF) (t := 2) (by omega)
    rw [Nat.add_zero, Nat.mul_zero, Nat.add_zero] at h0
    rw [h0, h1, h2]
    rfl

/-! ## The ground answers' proof of work -/

/-- An answer of the list has its recomposition row among `powRecRows`, its bit words inside the region. -/
theorem powRecRows_mem : ∀ (bw : ℕ) (as : List (ℕ × ℕ)) {q g : ℕ}, (q, g) ∈ as →
    ∃ bw', bw ≤ bw' ∧ bw' + (64 - g) ≤ bw + Lvm.Q2.powWords as ∧ powRecRow g bw' q ∈ powRecRows bw as
  | _, [], _, _, h => absurd h List.not_mem_nil
  | bw, (q', g') :: as, q, g, h => by
    have hw : Lvm.Q2.powWords ((q', g') :: as) = (64 - g') + Lvm.Q2.powWords as := by
      simp only [Lvm.Q2.powWords, List.map_cons, List.sum_cons]
    rcases List.mem_cons.mp h with e | h
    · obtain ⟨rfl, rfl⟩ := Prod.mk.inj e
      exact ⟨bw, le_rfl, by rw [hw]; omega, List.mem_cons_self⟩
    · obtain ⟨b, h1, h2, hb⟩ := powRecRows_mem (bw + (64 - g')) as h
      exact ⟨b, by omega, by rw [hw]; omega, List.mem_cons_of_mem _ hb⟩

/-- `n mod 2^(k+1)` is `n mod 2^k` plus bit `k`'s weight. -/
theorem mod_two_pow_succ' (n k : ℕ) : n % 2 ^ (k + 1) = n % 2 ^ k + (if n.testBit k then 2 ^ k else 0) := by
  rw [Nat.mod_pow_succ, Nat.testBit_eq_decide_div_mod_eq]
  rcases Nat.mod_two_eq_zero_or_one (n / 2 ^ k) with h | h <;> simp [h]

/-- **The booleanity runs cover the region**: every offset `o` with `n − n mod 2^k ≤ o < n` lies in the run of one set
bit `a < k`. -/
theorem boolRuns_cover (bw n : ℕ) : ∀ (k o : ℕ), n - n % 2 ^ k ≤ o → o < n →
    ∃ a b, (⟨a, [Lvm.Q2.rowBoolL b]⟩ : ABlk) ∈ boolRuns bw n k ∧ b ≤ bw + o ∧ bw + o < b + 2 ^ a
  | 0, o, h1, h2 => by rw [pow_zero, Nat.mod_one, Nat.sub_zero] at h1; omega
  | k + 1, o, h1, h2 => by
    have hm := mod_two_pow_succ' n k
    have hle : n % 2 ^ k ≤ n := Nat.mod_le _ _
    have hle' : n % 2 ^ (k + 1) ≤ n := Nat.mod_le _ _
    by_cases ho : n - n % 2 ^ k ≤ o
    · obtain ⟨a, b, hb, h3, h4⟩ := boolRuns_cover bw n k o ho h2
      exact ⟨a, b, by rw [boolRuns]; exact List.mem_append_right _ hb, h3, h4⟩
    · have ht : n.testBit k = true := by
        by_contra hf
        rw [Bool.not_eq_true] at hf
        rw [hf, if_neg (by simp), Nat.add_zero] at hm
        omega
      rw [ht, if_pos rfl] at hm
      refine ⟨k, bw + (n - n % 2 ^ (k + 1)), ?_, by omega, by omega⟩
      rw [boolRuns, ht, if_pos rfl]
      exact List.mem_append_left _ List.mem_cons_self

/-- A row of the layout's auxiliary blocks holds at each of its block's iterations. -/
theorem auxRow_mem {Q : Program} {tl : Typed.Lay} {z : ℕ → FK} (hlay : tl.Ok Q) (hone : z tl.one = 1)
    (h : WiringRelX Q tl z) {B : ABlk} (hB : B ∈ tl.aux) {r : ARow} (hr : r ∈ B.rows) {j : ℕ} (hj : j < 2 ^ B.l) :
    ARowHolds tl z j r := by
  obtain ⟨k, hk, hkb⟩ := List.mem_iff_getElem.mp hB
  have hget : tl.aux.getD k default = B := by rw [List.getD_eq_getElem _ _ hk, hkb]
  obtain ⟨r', hr', hrr⟩ := List.mem_iff_getElem.mp hr
  have hj' : j < 2 ^ (tl.aux.getD k default).l := by rw [hget]; exact hj
  have hr'' : r' < (tl.aux.getD k default).rows.length := by rw [hget]; exact hr'
  have := auxRow_of_wiringX Q tl z hlay hone h hk hj' hr''
  rw [hget, List.getD_eq_getElem _ _ hr', hrr] at this
  exact this

/-- **V's proof-of-work checks from the PoW blocks** (`powBlk_ok`): on the layout built with `specQF C Q pw`, where
the coordinate-split relation holds and the word `1` holds `1`, every answer `(q, g)` of `pw` (with `g ≤ 64` and its
lane 2 streamed) passes `powOKR g` on `Σ`'s scalar at lane `q`; hence `PowOkV (feAt Σ) L` for every `L ⊆ pw`. -/
theorem powOk_of_blks (C : QCfg) {Q : Program} {tl : Typed.Lay} {z : ℕ → FK} {pw : List (ℕ × ℕ)}
    {d : Array (Ty × ℕ × ℕ)} (hl : tl = (mkLayD Q (Lvm.E2Q.specQF C Q pw) d).1) (hlay : tl.Ok Q)
    (hone : z tl.one = 1) (h : WiringRelX Q tl z) {sig : ByteArray} {T : ℕ}
    (hS : Lvm.Q1.Streamed (memOf tl z) sig T) {L : List (ℕ × ℕ)} (hL : ∀ a ∈ L, a ∈ pw)
    (hpw : ∀ a ∈ L, a.1 + 2 < T ∧ a.2 ≤ 64) : Lvm.Q1.PowOkV (feAt sig) L := by
  intro a ha
  obtain ⟨q, g⟩ := a
  have hapw := hL _ ha
  obtain ⟨hq, hg⟩ := hpw _ ha
  obtain ⟨f, hf⟩ := aux_mkLayD Q (specQF C Q pw) d
  have haux : tl.aux = (specQ C Q).auxOf f ++ (Lvm.Q2.rowAuxL (f (specQ C Q).auxWords.length) (tBw C) (wireSlices C.p) ++
      Lvm.Q2.rowAuxL (f ((specQ C Q).auxWords.length + 1)) (tBk C) (ksSlices C.p)) ++
      powBlksL (f ((specQ C Q).auxWords.length + 2)) pw := by rw [hl, hf]; rfl
  set bw := f ((specQ C Q).auxWords.length + 2) with hbw
  have hP : ∀ B ∈ powBlksL bw pw, B ∈ tl.aux := fun B hB => by rw [haux]; exact List.mem_append_right _ hB
  obtain ⟨bw', h1, h2, hb⟩ := powRecRows_mem bw pw hapw
  have hrows : ∀ r ∈ (Lvm.Q2.powBlk g bw' q).rows, ARowHolds tl z 0 r := by
    intro r hr
    rw [Lvm.Q2.powBlk, powRangeRows] at hr
    rcases List.mem_append.mp hr with hr | hr
    · obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hr
      rw [List.mem_range] at hi
      -- booleanity of the word `bw' + i`: its run in `boolRuns`
      obtain ⟨a, b, hB, hb1, hb2⟩ := boolRuns_cover bw (Lvm.Q2.powWords pw) ((Lvm.Q2.powWords pw).log2 + 1) (bw' + i - bw)
        (by rw [Nat.mod_eq_of_lt Nat.lt_log2_self]; omega) (by omega)
      have hBm : (⟨a, [Lvm.Q2.rowBoolL b]⟩ : ABlk) ∈ tl.aux := hP _ (List.mem_append_left _ hB)
      have hj : bw' + i - b < 2 ^ a := by omega
      refine (Lvm.Q2.aRowHolds_congr ?_).mpr (auxRow_mem hlay hone h hBm List.mem_cons_self hj)
      simp only [Lvm.Q2.aRowVals, Lvm.Q2.rowBoolL, List.map_cons, List.map_nil, aopVal, Nat.mul_zero, Nat.add_zero,
        Nat.one_mul, show b + (bw' + i - b) = bw' + i by omega]
    · rw [List.mem_singleton] at hr
      subst hr
      exact auxRow_mem hlay hone h (hP _ (List.mem_append_right _ List.mem_cons_self)) hb (by simp)
  have hc : (memOf tl z).k (q + 2) = (feAt sig (8 * q)).c₂ := by
    rw [hS _ hq]
    show kAt sig (8 * (q + 2)) = kAt sig (8 * q + 16)
    rw [show 8 * (q + 2) = 8 * q + 16 by ring]
  exact Lvm.Q2.powBlk_ok tl z hg hc hrows

/-- **V's proof-of-work checks at S2GF** on a good pair's memory (`powOk_of_blks` at `cfgF20`, the pair's words). -/
theorem powOkF {F : TFrz} {Q : Program} {tl : Typed.Lay} {N : TypedV.TNat} (S : NodeGF F Q tl N)
    (H : THypX (N.inst Q tl)) {x : List UInt8} {qm : Column CMain.nu20} {qr : Column 19}
    (hG : E2V.GoodTF (N.inst Q tl) H x qm qr) {pw : List (ℕ × ℕ)} {d : Array (Ty × ℕ × ℕ)}
    (hl : tl = (mkLayD Q (specQF cfgF20 Q pw) d).1) {sig : ByteArray} {T : ℕ}
    (hS : Lvm.Q1.Streamed (memF (N.inst Q tl) x qm qr) sig T) {L : List (ℕ × ℕ)} (hL : ∀ a ∈ L, a ∈ pw)
    (hpw : ∀ a ∈ L, a.1 + 2 < T ∧ a.2 ≤ 64) : Lvm.Q1.PowOkV (feAt sig) L :=
  powOk_of_blks cfgF20 hl S.st.hlay (one_zTX H pubXF) hG.1.1.1.1 hS hL hpw

/-- `PUB`'s first `pubLanes` cells from S2GF's input map (`pubLanesX 44 = 750 ≥ 747`; roll 11's `PUB` glue,
`Lvm.Har.vk_cellsT`, reads them). -/
theorem pub747F {M : Mem} {vk : RecursionFast.Digest} {x : List UInt8} {qm : Column CMain.nu20} {qr : Column 19}
    (hin : InMapMB (spongeBlocks P20F) (pubLanesX accVF) (lay cfgF20) (sigIn cfgF20) M vk x qm qr) :
    ∀ j < pubLanes, M.k ((sigIn cfgF20).flag + j) = hdrLane x j :=
  fun j hj ↦ hin.pub j (lt_of_lt_of_le hj (by decide))

end Lvm.E2Q
