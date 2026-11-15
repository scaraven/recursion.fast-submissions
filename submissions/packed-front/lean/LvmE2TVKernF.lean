-- New for lvm2 E2-FT (stage S2GT, E2F-T-H1): V_S's typed kernels at `E2` (`LvmE2TV`: `virtD`, `relayKernD`) are the
-- specification's region sums (`LvmE2TProg`: `virtT`, `relayKernT`) on `N.toN.inst Q lay`, through `FE2.toE2`
-- (roll 11's `LvmTypedVEqForms.virtEF_rel`, `relayKernF_rel` at S2GT).
import LvmE2TVKernP
import LvmE2TV
import LvmTypedVEqForms
import LvmE2VGkrBase
import LvmE2VWireAlg
import LvmE2VTwins

/-!
# The typed kernels' closed forms at `E2`

On a native instance whose shape check holds (`TNat.okB`) and whose regions are the layout's (`TNat.layOk`):

* over any field: `kf_eqAtF_split` (an aligned index splits), `kf_sflat` (a stream position's `C_rec` word),
  `kf_mleKG` (`mleKG` is its sum), `kf_virtG` (`virtG` is the sum of its regions' terms), `kf_regSumW`
  (`regSumW` on `N.inst` is a sum over the native regions);
* **`virtD_rel`**: `virtD` is `virtT`; **`relayKernD_rel`**: `relayKernD` is `relayKernT` (the automata,
  `LvmE2TVKernP`).
-/

set_option autoImplicit false

namespace Lvm.E2T

open Lvm Lvm.TypedV
open Lvm.Typed (YSrc xVars yVars relayRounds Lay)
open Finset (range)

section Gen

variable {F : Type} [Field F]

/-- A list sum over a range is the `Finset` sum. -/
theorem kf_list_sum_range {M : Type} [AddCommMonoid M] (f : ℕ → M) :
    ∀ n, ((List.range n).map f).sum = ∑ i ∈ range n, f i
  | 0 => by simp
  | n + 1 => by
    rw [List.range_succ, List.map_append, List.sum_append, kf_list_sum_range f n, Finset.sum_range_succ]
    simp

/-- A left fold adding terms is the sum. -/
theorem kf_foldl {α M : Type} [AddCommMonoid M] (L : List α) (G : M → α → M) (T : α → M)
    (h : ∀ acc g, G acc g = acc + T g) (a : M) : L.foldl G a = a + (L.map T).sum := by
  induction L generalizing a with
  | nil => simp
  | cons g L ih => rw [List.foldl_cons, ih, h, List.map_cons, List.sum_cons, add_assoc]

/-- **An aligned index splits**: the low `l` bits are `i`, the high ones `b >>> l` (any length of `X`). -/
theorem kf_eqAtF_split (X : List F) (b l i : ℕ) (hb : b % 2 ^ l = 0) (hi : i < 2 ^ l) :
    E2V.eqAtF X (b + i) = E2V.eqAtF (X.take l) i * E2V.eqAtF (X.drop l) (b >>> l) := by
  obtain ⟨q, rfl⟩ := Nat.dvd_of_mod_eq_zero hb
  conv_lhs => rw [← List.take_append_drop l X]
  rw [E2V.eqAtF_append]
  congr 1
  · rw [E2V.eqAtF_mod, E2V.eqAtF_mod _ i]
    have hd : 2 ^ (X.take l).length ∣ 2 ^ l := Nat.pow_dvd_pow 2 (by simp)
    rw [Nat.add_mod, Nat.mod_eq_zero_of_dvd (dvd_trans hd (dvd_mul_right _ _)), zero_add, Nat.mod_mod]
  · rcases le_or_gt l X.length with hl | hl
    · rw [List.length_take_of_le hl, Nat.shiftRight_eq_div_pow, Nat.mul_add_div (by positivity),
        Nat.div_eq_of_lt hi, add_zero, Nat.mul_div_cancel_left _ (by positivity)]
    · rw [List.drop_of_length_le hl.le, E2V.eqAtF_nil, E2V.eqAtF_nil]

/-- **A stream position's `C_rec` word** splits into its row (`i / 17`) and its lane (`i mod 17`). -/
theorem kf_sflat (R : List F) (i : ℕ) (hi : i < sPos) :
    E2V.eqAtF R (sflatWord i) =
      E2V.eqAtF (R.take recRowBits) (i / sLanes) * E2V.eqAtF (R.drop recRowBits) (i % sLanes) := by
  rw [sflatWord, ite_eq_left hi, kf_eqAtF_split R _ recRowBits _ (Nat.mul_mod_left _ _)]
  · rw [Nat.shiftRight_eq_div_pow, Nat.mul_div_cancel _ (by positivity)]
  · exact (Nat.div_lt_iff_lt_mul (by norm_num [sLanes, recStreamCols])).2 (by rw [mul_comm]; exact hi)

/-- **`mleKG` is its sum.** -/
theorem kf_mleKG [Algebra FK F] (log : ℕ) (v : ℕ → FK) (pt : List F) (hpt : log ≤ pt.length) :
    mleKG log v pt = ∑ i ∈ range (2 ^ log), algebraMap FK F (v i) * E2V.eqAtF (pt.take log) i := by
  unfold mleKG
  dsimp only
  rw [kg_foldl_range, zero_add]
  refine Finset.sum_congr rfl fun i hi ↦ ?_
  rw [kg_toArray_getD, E2V.eqKernelF_getD, List.length_take_of_le hpt, ite_eq_left (Finset.mem_range.1 hi)]

/-- **`virtG` is the sum of its regions' terms.** -/
theorem kf_virtG [Algebra FK F] (regs : List NReg) (hdr : Array FK) (ry : List F)
    (hl : ∀ g ∈ regs, g.src = .pub → g.log ≤ ry.length) :
    virtG regs hdr ry = (regs.map fun g ↦
      (if g.src = .pub then hiWG ry g.log g.base *
        ∑ i ∈ range (2 ^ g.log), algebraMap FK F (hdr.getD (g.dst + i) 0) * E2V.eqAtF (ry.take g.log) i
        else 0) + (if g.src = .one then hiWG ry g.log g.base else 0)).sum := by
  unfold virtG
  rw [kf_foldl _ _ (fun g ↦ (if g.src = .pub then hiWG ry g.log g.base *
      mleKG g.log (fun i ↦ hdr.getD (g.dst + i) 0) ry else 0) + (if g.src = .one then hiWG ry g.log g.base else 0))
    (fun acc g ↦ by rcases g with ⟨b, l, src, d⟩; cases src <;> simp), zero_add]
  refine congrArg List.sum (List.map_congr_left fun g hg ↦ ?_)
  by_cases hp : g.src = .pub
  · simp only [hp, ↓reduceIte]
    rw [kf_mleKG _ _ _ (hl g hg hp)]
  · simp only [hp, ↓reduceIte]

end Gen

/-- **`regSumW` on `N.inst`** is a sum over the native regions. -/
theorem kf_regSumW (N : TNat) (Q : Lvm.Loop.Program) (lay : Lay) (hlay : N.layOk lay = true) {M : Type}
    [AddCommMonoid M] (S : YSrc → Bool) (f : ℕ → M) :
    regSumW (N.inst Q lay) S f =
      (N.regs.map fun g ↦ if S g.src then ∑ i ∈ range (2 ^ g.log), f (g.base + i) else 0).sum := by
  have hy : lay.yregs = N.regs.map fun r ↦ (⟨r.base, r.log, r.src⟩ : Lvm.Typed.YReg) := by
    simpa [TNat.layOk] using hlay
  unfold regSumW
  simp only [TNat.inst, hy, List.map_map, Function.comp_def, kf_list_sum_range]

/-- `toE2` of a list sum. -/
theorem kf_toE2_sum {α : Type} (L : List α) (f : α → FE2) :
    FE2.toE2 (L.map f).sum = (L.map fun g ↦ FE2.toE2 (f g)).sum := by
  rw [← FE2.ringEquivE2_apply, map_list_sum, List.map_map]; rfl

/-- `toE2` of a `Finset` sum. -/
theorem kf_toE2_fsum {ι : Type} (s : Finset ι) (f : ι → FE2) :
    FE2.toE2 (∑ i ∈ s, f i) = ∑ i ∈ s, FE2.toE2 (f i) := by
  rw [← FE2.ringEquivE2_apply, map_sum]; rfl

theorem kf_toE2_mul (a b : FE2) : FE2.toE2 (a * b) = FE2.toE2 a * FE2.toE2 b := by
  rw [← FE2.ringEquivE2_apply, map_mul]; rfl

theorem kf_toE2_algebraMap (a : FK) : FE2.toE2 (algebraMap FK FE2 a) = kE2 a := rfl

variable (N : TNatT) (Q : Lvm.Loop.Program) (lay : Lay)

/-- **`virtD` is `virtT`** (the `PUB` region by its multilinear extension, the `1` region by its weight; the `QLT`
part is `0`: `TNat.inst`'s `qltV` is `0`). -/
theorem virtD_rel (nuMain nuRec : ℕ) (hok : N.toN.okB nuMain nuRec = true) (hlay : N.toN.layOk lay = true)
    (pub : Pub) (ry : List FE2) (hry : ry.length = yVars) :
    FE2.toE2 (virtD N pub ry) = virtT (N.toN.inst Q lay) pub (ry.map FE2.toE2) := by
  obtain ⟨hreg, -, hsort⟩ := fm_ok N.toN nuMain nuRec hok
  have hpw := fm_pairwise N.toN.regs hsort
  have hpub : ∀ g ∈ N.regs, g.src = .pub → g.log ≤ ry.length := fun g hg hs ↦ by
    rw [(hreg g hg).2.2.2.1 hs |>.1, hry]; norm_num
  unfold virtD
  rw [kf_virtG _ _ _ hpub, kf_toE2_sum]
  unfold virtT regSumT
  rw [kf_regSumW N.toN Q lay hlay, kf_regSumW N.toN Q lay hlay, kf_regSumW N.toN Q lay hlay,
    ← List.sum_map_add, ← List.sum_map_add]
  refine congrArg List.sum (List.map_congr_left fun g hg ↦ ?_)
  obtain ⟨hb1, -, -, hp, hone⟩ := hreg g hg
  have hoff := fm_off N.toN hpw g hg
  rcases g with ⟨b, l, src, d⟩
  cases src
  · simp
  · simp
  · obtain ⟨-, rfl⟩ := hp rfl
    simp only [ite_true, beq_iff_eq, reduceCtorEq, ite_false, add_zero, beq_self_eq_true, kf_toE2_mul, hiWG,
      E2V.toE2_eqAtF, kf_toE2_fsum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i hi ↦ ?_
    have hi' : i < 2 ^ l := Finset.mem_range.1 hi
    simp only at hb1 hoff
    rw [kf_toE2_algebraMap, kf_eqAtF_split _ b l i hb1 hi', List.map_take, List.map_drop, zero_add]
    simp only [TNat.inst]
    rw [hoff i hi', zero_add, Array.getD_eq_getD_getElem?, List.getElem?_toArray, List.getD_eq_getElem?_getD]
    ring
  · simp
  · simp
  · have hk0 : kE2 0 = 0 := by rw [kE2, show FE2.ofK 0 = 0 from rfl, FE2.toE2_zero]
    simp [TNat.inst, hk0]
  · obtain rfl := hone rfl
    simp [hiWG, E2V.toE2_eqAtF]

/-- **`relayKernD` is `relayKernT`** (the long-division automaton and the comparator, `LvmE2TVKernP`). -/
theorem relayKernD_rel (nuMain nuRec : ℕ) (hok : N.toN.okB nuMain nuRec = true) (hlay : N.toN.layOk lay = true)
    (ry r : List FE2) (hry : ry.length = yVars) (hr : r.length = relayRounds) :
    FE2.toE2 (relayKernD N ry r) = relayKernT (N.toN.inst Q lay) (ry.map FE2.toE2) (r.map FE2.toE2) := by
  obtain ⟨hreg, ⟨g, hg1, hlog, hdst⟩, hsort⟩ := fm_ok N.toN nuMain nuRec hok
  have hpw := fm_pairwise N.toN.regs hsort
  have hgm : g ∈ N.toN.regs :=
    (List.mem_filter.1 (hg1 ▸ List.mem_singleton_self g : g ∈ N.toN.regsOf .sflat)).1
  obtain ⟨hb1, -⟩ := hreg g hgm
  have hoff := fm_off N.toN hpw g hgm
  have hsingle : regSumW (N.toN.inst Q lay) (fun s ↦ s == .sflat)
      (fun y ↦ E2V.eqAtF (ry.map FE2.toE2) y *
        E2V.eqAtF (r.map FE2.toE2) ((N.toN.inst Q lay).sflatW y)) =
      ∑ i ∈ range (2 ^ g.log), E2V.eqAtF (ry.map FE2.toE2) (g.base + i) *
        E2V.eqAtF (r.map FE2.toE2) ((N.toN.inst Q lay).sflatW (g.base + i)) := by
    rw [kf_regSumW N.toN Q lay hlay]
    have := fm_sum_filter N.toN.regs (fun g ↦ g.src == .sflat)
      (fun g ↦ ∑ i ∈ range (2 ^ g.log), E2V.eqAtF (ry.map FE2.toE2) (g.base + i) *
        E2V.eqAtF (r.map FE2.toE2) ((N.toN.inst Q lay).sflatW (g.base + i)))
    rw [show N.toN.regs.filter (fun g ↦ g.src == .sflat) = [g] from hg1] at this
    simpa using this.symm
  unfold relayKernD relayKernT regSumT
  rw [hg1, hsingle]
  rcases g with ⟨b, l, src, d⟩
  simp only at hlog hdst hb1 hoff
  subst hlog hdst
  have hidp : ¬ (0 + 2 ^ posBits ≤ sPos) := by norm_num [sPos, sLanes, recStreamCols, recRowBits]
  have hρ : (ry.take posBits).length = posBits := List.length_take_of_le (by rw [hry]; norm_num)
  have hlo : (r.take recRowBits).length = recRowBits := List.length_take_of_le (by rw [hr]; norm_num)
  have hr' : r.length = posBits := hr
  have hc : sPos < 2 ^ posBits := by norm_num [sPos, sLanes, recStreamCols, recRowBits]
  simp only [relayKernG, List.foldl_cons, List.foldl_nil, zero_add, Nat.zero_shiftRight, Nat.min_zero,
    Nat.sub_zero, List.drop_of_length_le (le_of_eq hr'), List.take_of_length_le (le_of_eq hr')]
  rw [divKernG_eq _ _ _ hρ hlo, geKernG_eq _ _ _ _ hρ hr' hc, ite_eq_right (by simpa using hidp), E2V.eqAtF_nil,
    one_mul, kf_toE2_mul, FE2.toE2_add, hiWG, E2V.toE2_eqAtF, E2V.toE2_sumF, E2V.toE2_sumF, List.map_map,
    List.map_map, E2V.sumF_map_range, E2V.sumF_eq_sum, fm_sum_filter, kf_list_sum_range]
  simp only [TNat.inst]
  have e : ∀ i ∈ range (2 ^ posBits), E2V.eqAtF (ry.map FE2.toE2) (b + i) *
      E2V.eqAtF (r.map FE2.toE2) (sflatWord (N.toN.off (b + i))) =
        E2V.eqAtF ((ry.map FE2.toE2).drop posBits) (b >>> posBits) *
          (E2V.eqAtF ((ry.map FE2.toE2).take posBits) i * E2V.eqAtF (r.map FE2.toE2) (sflatWord i)) := by
    intro i hi
    rw [hoff i (Finset.mem_range.1 hi), zero_add, kf_eqAtF_split _ b posBits i hb1 (Finset.mem_range.1 hi)]
    ring
  rw [Finset.sum_congr rfl e, ← Finset.mul_sum, List.map_drop]
  conv_rhs => rw [← Finset.sum_range_add_sum_Ico _ hc.le]
  refine congrArg₂ (· * ·) rfl (congrArg₂ (· + ·) ?_ ?_)
  · refine Finset.sum_congr rfl fun i hi ↦ ?_
    simp only [Function.comp_apply]
    rw [kf_sflat _ i (Finset.mem_range.1 hi), kf_toE2_mul, kf_toE2_mul, E2V.toE2_eqAtF, E2V.toE2_eqAtF,
      E2V.toE2_eqAtF, List.map_take, List.map_drop, List.map_take]
    ring
  · rw [← Finset.sum_filter]
    have hset : (range (2 ^ posBits)).filter (fun k ↦ decide (sPos ≤ k) = true) = Finset.Ico sPos (2 ^ posBits) := by
      ext k
      simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_Ico, decide_eq_true_eq]
      omega
    rw [hset]
    refine Finset.sum_congr rfl fun i hi ↦ ?_
    have hi' : sPos ≤ i := (Finset.mem_Ico.1 hi).1
    simp only [Function.comp_apply]
    rw [sflatWord, ite_eq_right (by omega), kf_toE2_mul, E2V.toE2_eqAtF, E2V.toE2_eqAtF, List.map_take]

end Lvm.E2T
