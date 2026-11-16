-- New for lvm2 E2-FT (stage S2GT, E2F-T-H3): the region facts of the typed phases at `E2` (the twins of roll 11's
-- `LvmTypedSpec` "Facts": `mleZ_zOf`, `relay_true`, `holds_com`/`holds_ks`/`holds_sigma`, `holds_relayPoint`),
-- with the region-sum lemmas written once over any commutative monoid or semiring.
import LvmE2TProg
import LvmE2TSum

/-!
# The typed phases' region facts at `E2`

* **Region sums, generic** (`regSumW` over any `AddCommMonoid`): `sum_regionsW` (a cube sum of a function zero off
  the sorted regions is the regions' sums), `regSumW_sources` (the seven sources' sums add up to the regions'
  sums), `regSumW_congr`, `sum_regSumW` (a finite sum passes inside), `regSumW_mul`.
* **`zwT`** (a word in `E2`), **`mleYT`** (`z̃` at `E2` on the `2^21` words); **`mleZ_zOfT`**: `z̃(r_y)` of a
  candidate's words is the committed, `S_flat`, `σ′`, `KS` region sums and the native `virtT`.
* **The relayout's family at `E2`**: `recT` (`C_rec`'s words in `E2`), `relayGTT` (kernel times `C_rec`'s
  extension), `polyLEF_relayGTT` (degree 2 in each coordinate), **`relay_trueT`** (its cube sum is `S_flat`'s true
  region sum, the map inside `C_rec`).
* **The split claims mean the true values**: `holds_comT`, `holds_ksT`, `holds_sigmaT` (from
  `regClaimT_holds_iff`), **`holds_relayPointT`** (the relayout's split point claim holding gives `v_R = C̃_rec(r)`,
  from `splitE2_sound`).
-/

set_option autoImplicit false

namespace Lvm.E2T

open Lvm.Typed LeanVM.Parameters LeanVM.Protocol LeanVM.Protocol.Compile LeanVM.Protocol.EndToEnd Finset
open Lvm.E2V (splitE2 pointE2 SumE2 splitE2_sound)

/-! ## Region sums over any commutative monoid -/

section Gen

variable {M : Type} [AddCommMonoid M]

theorem listRange_sumW (n : ℕ) (f : ℕ → M) : ((List.range n).map f).sum = ∑ i ∈ range n, f i := by
  induction n with
  | zero => simp
  | succ n ih => rw [List.range_succ, List.map_append, List.sum_append, ih, Finset.sum_range_succ]; simp

/-- A finite sum of list sums is the list sum of the finite sums. -/
theorem sum_list_swapW {α ι : Type} (s : Finset ι) (l : List α) (F : α → ι → M) :
    ∑ u ∈ s, (l.map fun a ↦ F a u).sum = (l.map fun a ↦ ∑ u ∈ s, F a u).sum := by
  induction l with
  | nil => simp
  | cons a l ih => simp only [List.map_cons, List.sum_cons, Finset.sum_add_distrib, ih]

/-- **The cube sum splits into the regions' sums** (sorted regions inside `[0, N)`, `f` zero off them). -/
theorem sum_regionsW (N : ℕ) : ∀ (L : List YReg), L.Pairwise (fun r r' ↦ r.base + 2 ^ r.log ≤ r'.base) →
    (∀ r ∈ L, r.base + 2 ^ r.log ≤ N) → ∀ (f : ℕ → M), (∀ y, (∀ reg ∈ L, ¬ reg.Has y) → f y = 0) →
    ∑ y ∈ range N, f y = (L.map fun reg ↦ ∑ i ∈ range (2 ^ reg.log), f (reg.base + i)).sum
  | [], _, _, f, hf => by
    simp only [List.map_nil, List.sum_nil]
    exact Finset.sum_eq_zero fun y _ ↦ hf y (by simp)
  | r :: rs, hP, hN, f, hf => by
    have hrN := hN r (List.mem_cons_self ..)
    have hsplit : ∑ y ∈ range N, f y = ∑ y ∈ range N, (if r.Has y then f y else 0) +
        ∑ y ∈ range N, (if r.Has y then 0 else f y) := by
      rw [← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl fun y _ ↦ by split_ifs <;> simp
    have h1 : ∑ y ∈ range N, (if r.Has y then f y else 0) = ∑ i ∈ range (2 ^ r.log), f (r.base + i) := by
      rw [← Finset.sum_filter]
      have hset : (range N).filter (fun y ↦ r.Has y) = Finset.Ico r.base (r.base + 2 ^ r.log) := by
        ext y; simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_Ico, YReg.Has]; omega
      rw [hset, Finset.sum_Ico_eq_sum_range, Nat.add_sub_cancel_left]
    have h2 := sum_regionsW N rs (List.Pairwise.of_cons hP) (fun x hx ↦ hN x (List.mem_cons_of_mem _ hx))
      (fun y ↦ if r.Has y then 0 else f y) (fun y hy ↦ by
        split_ifs with hr
        · rfl
        · exact hf y fun reg hreg ↦ by
            rcases List.mem_cons.mp hreg with rfl | hreg
            · exact hr
            · exact hy reg hreg)
    rw [hsplit, h1, h2, List.map_cons, List.sum_cons]
    congr 1
    refine congrArg List.sum (List.map_congr_left fun reg hreg ↦ Finset.sum_congr rfl fun i _ ↦ ?_)
    have hle := List.rel_of_pairwise_cons hP hreg
    rw [ite_eq_right (by simp only [YReg.Has]; omega)]

variable (Ti : TInst)

/-- **The seven sources' region sums** add up to the regions' sums. -/
theorem regSumW_sources (f : ℕ → M) :
    regSumW Ti (· == .com) f + regSumW Ti (· == .sflat) f + regSumW Ti (· == .sigma) f +
        regSumW Ti (· == .ks) f + (regSumW Ti (· == .pub) f + regSumW Ti (· == .qlt) f +
          regSumW Ti (· == .one) f) =
      (Ti.lay.yregs.map fun reg ↦ ∑ i ∈ range (2 ^ reg.log), f (reg.base + i)).sum := by
  unfold regSumW
  generalize Ti.lay.yregs = L
  induction L with
  | nil => simp
  | cons reg L ih =>
    simp only [List.map_cons, List.sum_cons] at ih ⊢
    rw [← ih, listRange_sumW]
    cases reg.src <;> simp <;> abel

/-- Region sums agree when their functions agree on the regions' words. -/
theorem regSumW_congr (S : YSrc → Bool) {f g : ℕ → M}
    (h : ∀ reg ∈ Ti.lay.yregs, S reg.src = true → ∀ i < 2 ^ reg.log, f (reg.base + i) = g (reg.base + i)) :
    regSumW Ti S f = regSumW Ti S g := by
  unfold regSumW
  refine congrArg List.sum (List.map_congr_left fun reg hreg ↦ ?_)
  split_ifs with hS
  · refine congrArg List.sum (List.map_congr_left fun i hi ↦ ?_)
    rw [h reg hreg hS i (List.mem_range.mp hi)]
  · rfl

/-- A finite sum of region sums is the region sum of the finite sums. -/
theorem sum_regSumW {ι : Type} (S : YSrc → Bool) (s : Finset ι) (G : ι → ℕ → M) :
    ∑ u ∈ s, regSumW Ti S (G u) = regSumW Ti S fun y ↦ ∑ u ∈ s, G u y := by
  unfold regSumW
  rw [sum_list_swapW]
  refine congrArg List.sum (List.map_congr_left fun reg _ ↦ ?_)
  split_ifs
  · exact sum_list_swapW s _ _
  · exact Finset.sum_const_zero

end Gen

/-- A region sum times a constant. -/
theorem regSumW_mul {R : Type} [CommSemiring R] (Ti : TInst) (S : YSrc → Bool) (f : ℕ → R) (c : R) :
    regSumW Ti S f * c = regSumW Ti S fun y ↦ f y * c := by
  unfold regSumW
  rw [← List.sum_map_mul_right]
  refine congrArg List.sum (List.map_congr_left fun reg _ ↦ ?_)
  split_ifs
  · rw [← List.sum_map_mul_right]
  · exact zero_mul c

/-- A list sum of functions of degree `d` has degree `d`. -/
theorem polyLEF_listSum {F : Type} [Field F] {α : Type} (d : ℕ) (l : List α) (G : α → F → F)
    (h : ∀ a ∈ l, E2V.PolyLEF d (G a)) : E2V.PolyLEF d fun x ↦ (l.map fun a ↦ G a x).sum := by
  induction l with
  | nil => exact (E2V.PolyLEF.const d 0).congr fun _ ↦ rfl
  | cons a l ih =>
    exact (E2V.PolyLEF.add (h a (List.mem_cons_self ..))
      (ih fun b hb ↦ h b (List.mem_cons_of_mem _ hb))).congr fun _ ↦ rfl

/-! ## Words at `E2` -/

/-- A word at `E2`. -/
def zwT (z : ℕ → FK) (y : ℕ) : E2 := kE2 (z y)

/-- `z̃` at `E2` on the `2^|pt|` words (`r_y`: 21 coordinates). The range is never a literal: the kernel can then never
fall back to evaluating the `2^21`-element range in a defeq check. -/
def mleYT (pt : List E2) (f : ℕ → E2) : E2 := ∑ y ∈ range (2 ^ pt.length), E2V.eqAtF pt y * f y

theorem kE2_ofBF64 (b : K) : kE2 (FK.ofBF64 b) = algebraMap K E2 b := by
  rw [kE2, Lvm.FE2.toE2_ofK, FK.toBF64_ofBF64]; rfl

theorem kE2_zero : kE2 0 = 0 := by
  rw [kE2, Lvm.FE2.toE2_ofK, FK.toBF64_zero, Quad.C_eq_algebraMap, map_zero]

theorem kE2_one : kE2 1 = 1 := by
  rw [kE2, Lvm.FE2.toE2_ofK, FK.toBF64_one, Quad.C_eq_algebraMap, map_one]

section Facts

variable (Ti : TInst) (L : Lvm.M3.Lay) (pub : Lvm.Pub)

/-- **`z̃(r_y)` at `E2` is the regions' sums** (the committed, `S_flat`, `σ′`, `KS` parts and the native
`virtT`). -/
theorem mleZ_zOfT (hTi : Ti.Ok) (qm : Column L.nuMain) (qr : Column L.nuRec) {ry : List E2}
    (hry : ry.length = yVars) :
    mleYT ry (zwT (Ti.zOf L pub qm qr)) =
      regSumT Ti (· == .com) (zwT (Ti.zOf L pub qm qr)) ry + regSumT Ti (· == .sflat) (zwT (Ti.zOf L pub qm qr)) ry +
        regSumT Ti (· == .sigma) (zwT (Ti.zOf L pub qm qr)) ry + regSumT Ti (· == .ks) (zwT (Ti.zOf L pub qm qr)) ry +
          virtT Ti pub ry := by
  obtain ⟨hP, hfit⟩ := yregs_pairwise Ti hTi
  rw [mleYT, hry]
  rw [sum_regionsW (2 ^ yVars) _ hP hfit (fun y ↦ E2V.eqAtF ry y * zwT (Ti.zOf L pub qm qr) y) (fun y hy ↦ by
    simp only [zwT, TInst.zOf, src?_eq, ysrcL_none hy, kE2_zero, mul_zero])]
  rw [← regSumW_sources Ti fun y ↦ E2V.eqAtF ry y * zwT (Ti.zOf L pub qm qr) y]
  have hc : ∀ (s : YSrc) (f : ℕ → E2), (∀ y, Ti.src? y = some s → f y = zwT (Ti.zOf L pub qm qr) y) →
      regSumT Ti (· == s) f ry = regSumW Ti (· == s) (fun y ↦ E2V.eqAtF ry y * zwT (Ti.zOf L pub qm qr) y) :=
    fun s f hf ↦ regSumW_congr Ti (· == s) fun reg hreg hS i hi ↦ by
      rw [hf _ (by rw [src?_mem Ti hTi hreg hi]; simpa using hS)]
  have hv : virtT Ti pub ry =
      regSumW Ti (· == .pub) (fun y ↦ E2V.eqAtF ry y * zwT (Ti.zOf L pub qm qr) y) +
        regSumW Ti (· == .qlt) (fun y ↦ E2V.eqAtF ry y * zwT (Ti.zOf L pub qm qr) y) +
          regSumW Ti (· == .one) (fun y ↦ E2V.eqAtF ry y * zwT (Ti.zOf L pub qm qr) y) := by
    unfold virtT
    rw [hc .pub _ fun y hy ↦ by simp only [zwT, TInst.zOf, hy],
      hc .qlt _ fun y hy ↦ by simp only [zwT, TInst.zOf, hy],
      hc .one _ fun y hy ↦ by simp only [zwT, TInst.zOf, hy, kE2_one]]
  rw [hv]
  rfl

/-- **A split region claim holds iff the region's true value is its value**, when the candidate's words on the
source's regions are the commitment's words through the map, inside the commitment. -/
theorem holds_regTrueT (hTi : Ti.Ok) {μ : ℕ} (s : YSrc) (w : ℕ → ℕ) (q : Column μ) (z : ℕ → FK) (ry : List E2)
    (v : E2) (hz : ∀ y, Ti.src? y = some s → w y < 2 ^ μ ∧ zwT z y = algebraMap K E2 (q.values.getD (w y) 0)) :
    (∀ c ∈ regClaimT Ti s w ry v, StackClaim.Holds μ c q) ↔ regSumT Ti (· == s) (zwT z) ry = v := by
  have hm : ∀ reg ∈ Ti.lay.yregs, reg.src = s → ∀ i < 2 ^ reg.log, Ti.src? (reg.base + i) = some s :=
    fun reg hreg hS i hi ↦ by rw [src?_mem Ti hTi hreg hi, hS]
  rw [regClaimT_holds_iff Ti μ s w ry v q fun reg hreg hS i hi ↦ (hz _ (hm reg hreg hS i hi)).1]
  refine Eq.congr_left (regSumW_congr Ti _ fun reg hreg hS i hi ↦ ?_)
  rw [(hz _ (hm reg hreg (by simpa using hS) i hi)).2]

/-- The committed block's split claim. -/
theorem holds_comT (hTi : Ti.Ok) (hmaps : Ti.MapsFit L) (qm : Column L.nuMain) (qr : Column L.nuRec)
    (ry : List E2) (v : E2) :
    (∀ c ∈ regClaimT Ti .com Ti.comW ry v, StackClaim.Holds L.nuMain c qm) ↔
      regSumT Ti (· == .com) (zwT (Ti.zOf L pub qm qr)) ry = v :=
  holds_regTrueT Ti hTi .com Ti.comW qm _ ry v fun y hy ↦ by
    have hb : Ti.comW y < 2 ^ L.nuMain := by have := hmaps y; simp only [hy] at this; exact this
    refine ⟨hb, ?_⟩
    simp only [zwT, TInst.zOf, hy, comCell_of_lt L qm qr false (by simpa using hb)]
    exact kE2_ofBF64 _

/-- The `KS` aliases' split claim. -/
theorem holds_ksT (hTi : Ti.Ok) (hmaps : Ti.MapsFit L) (qm : Column L.nuMain) (qr : Column L.nuRec)
    (ry : List E2) (v : E2) :
    (∀ c ∈ regClaimT Ti .ks Ti.ksW ry v, StackClaim.Holds L.nuMain c qm) ↔
      regSumT Ti (· == .ks) (zwT (Ti.zOf L pub qm qr)) ry = v :=
  holds_regTrueT Ti hTi .ks Ti.ksW qm _ ry v fun y hy ↦ by
    have hb : Ti.ksW y < 2 ^ L.nuMain := by have := hmaps y; simp only [hy] at this; exact this
    refine ⟨hb, ?_⟩
    simp only [zwT, TInst.zOf, hy, comCell_of_lt L qm qr false (by simpa using hb)]
    exact kE2_ofBF64 _

/-- `σ′`'s split claim. -/
theorem holds_sigmaT (hTi : Ti.Ok) (hmaps : Ti.MapsFit L) (qm : Column L.nuMain) (qr : Column L.nuRec)
    (ry : List E2) (v : E2) :
    (∀ c ∈ regClaimT Ti .sigma Ti.sigmaW ry v, StackClaim.Holds L.nuRec c qr) ↔
      regSumT Ti (· == .sigma) (zwT (Ti.zOf L pub qm qr)) ry = v :=
  holds_regTrueT Ti hTi .sigma Ti.sigmaW qr _ ry v fun y hy ↦ by
    have hb : Ti.sigmaW y < 2 ^ L.nuRec := by have := hmaps y; simp only [hy] at this; exact this
    refine ⟨hb, ?_⟩
    simp only [zwT, TInst.zOf, hy, comCell_of_lt L qm qr true (by simpa using hb)]
    exact kE2_ofBF64 _

end Facts

/-! ## The relayout's family at `E2` -/

/-- A column's words at `E2`. -/
def recT {μ : ℕ} (q : Column μ) (w : ℕ) : E2 := algebraMap K E2 (q.values.getD w 0)

/-- **The relayout's summand at `E2`**: the kernel times the column's extension. -/
def relayGTT (Ti : TInst) (ry : List E2) (n : ℕ) (col : ℕ → E2) (pt : List E2) : E2 :=
  relayKernT Ti ry pt * ∑ w ∈ range (2 ^ n), E2V.eqAtF pt w * col w

/-- The relayout's summand has degree 2 in each coordinate. -/
theorem polyLEF_relayGTT (Ti : TInst) (ry : List E2) (n : ℕ) (col : ℕ → E2) (pre post : List E2) :
    E2V.PolyLEF 2 fun x ↦ relayGTT Ti ry n col (pre ++ x :: post) := by
  have hk : E2V.PolyLEF 1 fun x ↦ relayKernT Ti ry (pre ++ x :: post) := by
    unfold relayKernT regSumT regSumW
    refine polyLEF_listSum 1 _ _ fun reg _ ↦ ?_
    split_ifs
    · exact polyLEF_listSum 1 _ _ fun i _ ↦
        E2V.PolyLEF.const_mul (E2V.polyLEF_eqAtF pre post _) _
    · exact E2V.PolyLEF.const 1 0
  exact E2V.PolyLEF.mul hk (E2V.polyLEF_mle pre post (2 ^ n) col)

/-- **The relayout's claim is `S_flat`'s true region sum** (the map inside `C_rec`). -/
theorem relay_trueT (Ti : TInst) (L : Lvm.M3.Lay) (pub : Lvm.Pub) (hTi : Ti.Ok) (hmaps : Ti.MapsFit L)
    (qm : Column L.nuMain) (qr : Column L.nuRec) (ry : List E2) :
    tCubeSumF L.nuRec (relayGTT Ti ry L.nuRec (recT qr)) [] =
      regSumT Ti (· == .sflat) (zwT (Ti.zOf L pub qm qr)) ry := by
  have hb : ∀ y, Ti.src? y = some .sflat → Ti.sflatW y < 2 ^ L.nuRec := fun y hy ↦ by
    have := hmaps y; simp only [hy] at this; exact this
  rw [tCubeSumF_nil]
  unfold relayGTT
  rw [Finset.sum_congr rfl fun u hu ↦ by
    rw [E2V.sum_eqAtF_bitsF (Finset.mem_range.mp hu), relayKernT, regSumT, regSumW_mul]]
  rw [sum_regSumW]
  refine regSumW_congr Ti _ fun reg hreg hS i hi ↦ ?_
  have hy : Ti.src? (reg.base + i) = some .sflat := by rw [src?_mem Ti hTi hreg hi]; simpa using hS
  have hw := hb _ hy
  rw [Finset.sum_eq_single (Ti.sflatW (reg.base + i))]
  · rw [E2V.eqAtF_bitsF_lt hw hw, ite_eq_left rfl, mul_one]
    simp only [zwT, TInst.zOf, hy, comCell_of_lt L qm qr true (by simpa using hw), ite_true]
    rw [kE2_ofBF64]; rfl
  · intro u hu hne
    rw [E2V.eqAtF_bitsF_lt (Finset.mem_range.mp hu) hw, ite_eq_right (Ne.symm hne), mul_zero, zero_mul]
  · intro h; exact absurd (Finset.mem_range.mpr hw) h

/-- **The relayout's split point claim** (`C_rec`'s whole `⟨relayRounds, 0⟩`) holding on `C_rec` gives its value:
`C_rec`'s extension at the point. -/
theorem holds_relayPointT (L : Lvm.M3.Lay) (hrec : L.nuRec = relayRounds) (rr : List E2)
    (hrr : rr.length = relayRounds) (v : E2) (qr : Column L.nuRec) :
    (∀ c ∈ (splitE2 relayRounds (pointE2 ⟨relayRounds, 0⟩ rr v)).map (·.onStack), StackClaim.Holds L.nuRec c qr) →
      v = ∑ w ∈ range (2 ^ relayRounds), E2V.eqAtF rr w * recT qr w := by
  intro hall
  by_contra hne
  have hfit : (pointE2 ⟨relayRounds, 0⟩ rr v).Fits L.nuRec := by
    intro p hp
    simp only [pointE2, List.mem_singleton] at hp
    subst hp
    refine ⟨hrr, hrec.ge, dvd_zero _, ?_⟩
    rw [hrec, zero_add]
  have hfalse : ¬ (pointE2 ⟨relayRounds, 0⟩ rr v).Holds (fun i ↦ qr.values.getD i 0) := by
    intro h
    apply hne
    simp only [SumE2.Holds, pointE2, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero, one_mul,
      zero_add] at h
    rw [← h]
    rfl
  obtain ⟨b, hb, hnot⟩ := splitE2_sound L.nuRec _ hfit qr hfalse
  rw [hrec] at hb
  exact hnot (hall _ (List.mem_map.mpr ⟨b, hb, rfl⟩))

end Lvm.E2T
