-- New for lvm2 MB-LIN (MBL-L, 2026-11-16): the mini-bus's leaf linearity and its three final GKR claims as `K`-linear
-- claims on `C_main` (stage S2GL). DAY-0 STATEMENTS: every `sorry` is tagged `-- MBL-STMT <n>`. A proof never
-- changes its statement; a needed change goes to the lead old → new.
import LvmVEqMid
import LvmM3MidCert
import LvmDecideM3Real
import LvmCertSMid3Blk

/-!
# MB-LIN: the mini-bus's final claims are linear (day-0 statements)

The mini-bus's tables have no constraints and flush coordinates that are constants or single columns (`mbLinB`,
decided natively on blob L by the guard). Every leaf is then an affine function of one row, and a bus side's forms
(the `Seam.bus` relation) at the GKR's last point `ζ` are affine in the columns' extensions at `ζ.take τ`:

* **`mbLeafLin`** (MBL-STMT 1, generic over `M3Instance`): the extension of a row polynomial of total degree `≤ 1` is
  that polynomial at the columns' extensions; **`mbFormLin`**: so is a form of such polynomials.
* **The claims** (the lead's form, 2026-11-16): for each side `s` (push, pull, count) one `sumClaimE ν parts_s
  value_s` on `C_main`: `parts_s` in table order (seeds, then reads: `mbT`'s order) and column order, one part
  `(coef, ⟨τ_t, off_c⟩, ζ.take τ_t)` per committed column `c` the side's flushes of table `t` name (`sideColsL`);
  `coef` the column's coefficient in the side's form (`busResV`), `value_s = total_s + Σ_t const_{s,t}` (char 2:
  `total_s = v_s + 1 + Σ_b w_b`; `const` the form's constant terms and its fixed columns at their closed forms).
* **`mbClaimsL_iff`** (MBL-STMT 2): on the lvm instance of tables with `mbLinB`, the `Seam.bus` forms of the bus
  phase's output hold on `stackOf L qm qr` iff the three claims hold on `qm`.
-/

set_option autoImplicit false

namespace Lvm.M3

open LeanVM.Parameters LeanVM.Protocol LeanVM.Protocol.Verifier CompPoly CMlPolynomialEval
open Lvm.VEq (BClaim VPlacement sumClaimE)

/-! ## MBL-STMT 1: leaf linearity (generic) -/

/-- A polynomial of total degree `≤ 1` commutes with affine combinations (weights summing to one). -/
theorem eval₂_affineComb {σ ι R S : Type*} [CommSemiring R] [CommRing S] (f : R →+* S)
    (P : MvPolynomial σ R) (hP : P.totalDegree ≤ 1) (s : Finset ι) (w : ι → S)
    (hw : ∑ x ∈ s, w x = 1) (v : ι → σ → S) :
    P.eval₂ f (fun i ↦ ∑ x ∈ s, w x * v x i) = ∑ x ∈ s, w x * P.eval₂ f (v x) := by
  simp only [MvPolynomial.eval₂_eq, Finset.mul_sum]
  conv_rhs => rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun d hd ↦ ?_
  have hdeg : (d.sum fun _ e ↦ e) ≤ 1 := (MvPolynomial.le_totalDegree hd).trans hP
  rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hdeg with h0 | h1
  · obtain rfl : d = 0 := (Finsupp.degree_eq_zero_iff d).mp h0
    simp only [Finsupp.support_zero, Finset.prod_empty, mul_one]
    rw [← Finset.sum_mul, hw, one_mul]
  · obtain ⟨a, rfl⟩ := (Finsupp.sum_eq_one_iff d).mp h1
    simp only [Finsupp.support_single a one_ne_zero, Finset.prod_singleton,
      Finsupp.single_eq_same, pow_one, Finset.mul_sum]
    exact Finset.sum_congr rfl fun x _ ↦ by ring

/-- **MBL-STMT 1a** (owner L): **the extension of an affine row polynomial is affine in the columns' extensions**
(`Σ_x eq(z, x) = 1` for the constant term). -/
theorem mbLeafLin {I : M3Instance} (q : Column I.μ) (j : Fin I.ntab) (P : MvPolynomial (Fin (I.width j)) K)
    (hP : P.totalDegree ≤ 1) (z : Vector E (I.τ j)) :
    evalMle (I.virtualTable q j P) z =
      MvPolynomial.eval₂ (algebraMap K E) (fun i ↦ eval₂Mle (I.column q ⟨j, i⟩).values (algebraMap K E) z) P := by
  have hw : ∑ x : Fin (2 ^ I.τ j), (lagrangeBasis z)[x] = 1 := by
    simpa [sumCube] using sumCube_lagrangeBasis z
  have hcol : (fun i ↦ eval₂Mle (I.column q ⟨j, i⟩).values (algebraMap K E) z) =
      fun i ↦ ∑ x : Fin (2 ^ I.τ j), (lagrangeBasis z)[x] * algebraMap K E (I.row q j x i) := by
    funext i
    rw [eval₂Mle, evalMle_eq_sum]
    refine Finset.sum_congr rfl fun x _ ↦ ?_
    simp [CMlPolynomialEval.map, M3Instance.row, mul_comm, Vector.get_eq_getElem]
  rw [evalMle_eq_sum, hcol, eval₂_affineComb _ P hP _ _ hw]
  refine Finset.sum_congr rfl fun x _ ↦ ?_
  rw [mul_comm]
  congr 1
  simp only [M3Instance.virtualTable, Fin.getElem_fin, Vector.getElem_ofFn]
  exact (TableSumcheck.evalRow_ofK P (I.row q j x)).symm

/-- **MBL-STMT 1b** (owner L): **a form of affine row polynomials** is the same weighted sum of the polynomials at the
columns' extensions. -/
theorem mbFormLin {I : M3Instance} (q : Column I.μ) (j : Fin I.ntab) (f : I.Form j)
    (hf : ∀ t ∈ f, t.2.1.totalDegree ≤ 1) (z : Vector E (I.τ j)) :
    M3Instance.Form.eval I f q z = (f.map fun t ↦ t.1 * MvPolynomial.eval₂ (algebraMap K E)
      (fun i ↦ eval₂Mle (I.column q ⟨j, i⟩).values (algebraMap K E) z) t.2.1).sum := by
  unfold M3Instance.Form.eval
  exact congrArg List.sum (List.map_congr_left fun t ht ↦ by rw [mbLeafLin q j t.2.1 (hf t ht) z])

/-! ## The static condition -/

/-- A coordinate polynomial is a constant or one column with a coefficient (`Const`, `Col`, `GCol`). -/
def cpolyLinB (P : CPoly) : Bool := P.all fun m ↦ decide (m.2.length ≤ 1)

/-- **The mini-bus is MB-LIN** (a native check on the tables; G0-1): no constraints, every key coordinate and every
count column a constant or one column, every committed column on `C_main` (no `C_rec` flag). -/
def mbLinB (tabs : List Tab) : Bool :=
  tabs.all fun t ↦ t.cons.isEmpty &&
    (t.reads.map (·.1) ++ t.seeds.map (·.1)).all (fun k ↦ cpolyLinB k.addr && k.val.all cpolyLinB) &&
    t.cols.all fun c ↦ match c with
      | .com rec _ => !rec
      | .fix _ _ => true

/-! ## The three claims -/

/-- The columns side `s` (`0` push, `1` pull, `2` count) of table `t` names, in column order: push the keys' and the
reads' counts, pull the keys' and both count columns, count the read counts. -/
def sideColsL (t : Tab) (s : ℕ) : List ℕ :=
  let keyCols : List ℕ := (t.reads.map (·.1) ++ t.seeds.map (·.1)).flatMap fun k ↦
    (k.addr :: k.val).flatMap fun P ↦ P.flatMap (·.2)
  let named : List ℕ :=
    if s = 0 then keyCols ++ t.reads.map (·.2)
    else if s = 1 then keyCols ++ t.reads.map (·.2) ++ t.seeds.map (·.2)
    else t.counts.map (·.val)
  (List.range t.w).filter fun c ↦ named.contains c

/-- Column `c`'s coefficient in a form (`Σ` of its single-column terms). -/
def coefL (f : LeanVM.Protocol.Verifier.Form) (c : ℕ) : E :=
  LeanVM.Protocol.Verifier.sumE ((f.terms.filter fun m ↦ m.1 == [c]).map (·.2))

/-- A form's constant on table `t` at `pt`: its constant terms and its fixed columns at their closed forms (the
native evaluator through `FE.toExt3`, as `fixedEvalV`). -/
def constL (t : Tab) (f : LeanVM.Protocol.Verifier.Form) (pt : List E) : E :=
  LeanVM.Protocol.Verifier.sumE (f.terms.map fun m ↦ match m.1 with
    | [] => m.2
    | [c] => match t.cols[c]? with
      | some (ColSrc.fix _ ev) => m.2 * FE.toExt3 (ev (pt.map FE.ofExt3))
      | _ => 0
    | _ => 0)

/-- Table `j`'s form on side `s` in a bus result. -/
def formL (r : BusResult) (j s : ℕ) : LeanVM.Protocol.Verifier.Form := (r.forms.getD j []).getD s default

/-- **Side `s`'s parts**: table order, column order; one part per committed column the side names. -/
def mbPartsL (tabs : List Tab) (r : BusResult) (s : ℕ) : List (E × VPlacement × List E) :=
  tabs.zipIdx.flatMap fun (tj : Tab × ℕ) ↦ (sideColsL tj.1 s).filterMap fun c ↦ match tj.1.cols[c]? with
    | some (ColSrc.com _ off) => some (coefL (formL r tj.2 s) c, ⟨tj.1.τ, off⟩, r.point.take tj.1.τ)
    | _ => none

/-- **Side `s`'s value**: the side's total plus every table's constant (characteristic two). -/
def mbValueL (tabs : List Tab) (r : BusResult) (s : ℕ) : E :=
  r.totals.getD s 0 +
    LeanVM.Protocol.Verifier.sumE (tabs.zipIdx.map fun (t, j) ↦ constL t (formL r j s) (r.point.take t.τ))

/-- **Side `s`'s claim** on `C_main` (`ν` variables). -/
def mbClaimL (nu : ℕ) (tabs : List Tab) (r : BusResult) (s : ℕ) : BClaim :=
  sumClaimE nu (mbPartsL tabs r s) (mbValueL tabs r s)

/-- **The three claims** (push, pull, count) of what the bus phase read. -/
def mbClaimsL (nu : ℕ) (tabs : List Tab) (b : LBus) : List BClaim :=
  (List.range 3).map (mbClaimL nu tabs (busResV tabs b))

/-! ## The native twin (V_S's claims, `FE`) -/

/-- Column `c`'s coefficient in a native form. -/
def coefN (f : Lvm.Form) (c : ℕ) : FE := Lvm.sumE ((f.terms.filter fun m ↦ m.1 == [c]).map (·.2))

/-- A native form's constant on table `t` at `pt` (its fixed columns at their closed forms `ev`). -/
def constN (t : Tab) (f : Lvm.Form) (pt : List FE) : FE :=
  Lvm.sumE (f.terms.map fun m ↦ match m.1 with
    | [] => m.2
    | [c] => match t.cols[c]? with
      | some (ColSrc.fix _ ev) => m.2 * ev pt
      | _ => 0
    | _ => 0)

/-- Table `j`'s native form on side `s`. -/
def formN (o : Lvm.BusOut) (j s : ℕ) : Lvm.Form := (o.forms.getD j []).getD s default

/-- **Side `s`'s native parts** (`mbPartsL`'s twin on `busFinalR`'s output at the point `pt`). -/
def mbPartsN (tabs : List Tab) (o : Lvm.BusOut) (pt : List FE) (s : ℕ) : List (FE × Lvm.Placement × List FE) :=
  tabs.zipIdx.flatMap fun (tj : Tab × ℕ) ↦ (sideColsL tj.1 s).filterMap fun c ↦ match tj.1.cols[c]? with
    | some (ColSrc.com _ off) => some (coefN (formN o tj.2 s) c, ⟨tj.1.τ, off⟩, pt.take tj.1.τ)
    | _ => none

/-- **Side `s`'s native value.** -/
def mbValueN (tabs : List Tab) (o : Lvm.BusOut) (pt : List FE) (s : ℕ) : FE :=
  o.totals.getD s 0 + Lvm.sumE (tabs.zipIdx.map fun (t, j) ↦ constN t (formN o j s) (pt.take t.τ))

/-- **V_S's three claims** (`sumClaim 23`-shaped on `C_main`) from the native bus decomposition `busFinalR tabs i`. -/
def mbClaimsN (nu : ℕ) (tabs : List Tab) (i : Lvm.BusIn) : List Lvm.BlockClaim :=
  (List.range 3).map fun s ↦
    Lvm.sumClaim nu (mbPartsN tabs (busFinalR tabs i) i.point s) (mbValueN tabs (busFinalR tabs i) i.point s)

/-! ## MBL-STMT 2: the proof's steps

On MB-LIN tables every monomial of a side's form is a constant or one column the side names (`termIn_formL`); such a
form is affine in the column values (`evaluate_affine`), so its value at the stack is the form at the columns'
extensions, which splits into the constant and the committed columns' blocks of `C_main` (`evaluate_split`,
`formEval_lvm`); a `sumClaimE` claim holds iff its parts' blocks sum to its value (`holds_sumClaimE_iff`). -/

/-- The columns side `s` of table `t` names (`sideColsL`'s list before the range filter). -/
def keyColsL (t : Tab) : List ℕ :=
  (t.reads.map (·.1) ++ t.seeds.map (·.1)).flatMap fun k ↦ (k.addr :: k.val).flatMap fun P ↦ P.flatMap (·.2)

/-- The columns side `s` of table `t` names (`sideColsL`'s list before the range filter). -/
def namedL (t : Tab) (s : ℕ) : List ℕ :=
  if s = 0 then keyColsL t ++ t.reads.map (·.2)
  else if s = 1 then keyColsL t ++ t.reads.map (·.2) ++ t.seeds.map (·.2)
  else t.counts.map (·.val)

theorem sideColsL_eq (t : Tab) (s : ℕ) :
    sideColsL t s = (List.range t.w).filter fun c ↦ (namedL t s).contains c := rfl

/-- A monomial of at most one column, named in `N`. -/
def TermIn (N : List ℕ) (m : List ℕ) : Prop := m = [] ∨ ∃ c ∈ N, m = [c]

theorem termIn_cpoly {N : List ℕ} {P : CPoly} (hP : cpolyLinB P = true)
    (hN : ∀ m ∈ P, ∀ c ∈ m.2, c ∈ N) : ∀ m ∈ P, TermIn N m.2 := by
  intro m hm
  have h1 : m.2.length ≤ 1 := by simpa using List.all_eq_true.mp hP m hm
  rcases hc : m.2 with _ | ⟨c, _ | ⟨d, l⟩⟩
  · exact Or.inl rfl
  · exact Or.inr ⟨c, hN m hm c (by simp [hc]), rfl⟩
  · rw [hc] at h1; simp at h1

theorem termIn_cpolyForm {N : List ℕ} (w : E) (P : CPoly) (hP : ∀ m ∈ P, TermIn N m.2) :
    ∀ m ∈ (cpolyFormV w P).terms, TermIn N m.1 := by
  intro m hm
  obtain ⟨m', hm', rfl⟩ := List.mem_map.mp hm
  exact hP m' hm'

theorem termIn_leaf {N : List ℕ} (eqα : List E) (β : E) (k : Key) (cnt : CPoly)
    (hA : ∀ m ∈ k.addr, TermIn N m.2) (hC : ∀ m ∈ cnt, TermIn N m.2)
    (hV : ∀ P ∈ k.val, ∀ m ∈ P, TermIn N m.2) :
    ∀ m ∈ (leafFormV eqα β k cnt).terms, TermIn N m.1 := by
  intro m hm
  obtain ⟨f, hf, hmf⟩ := List.mem_flatMap.mp hm
  simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false, List.mem_map] at hf
  rcases hf with (rfl | rfl | rfl) | ⟨⟨P, l⟩, hPl, rfl⟩
  · obtain rfl := List.mem_singleton.mp hmf
    exact Or.inl rfl
  · exact termIn_cpolyForm _ _ hA m hmf
  · exact termIn_cpolyForm _ _ hC m hmf
  · exact termIn_cpolyForm _ _ (hV P (List.fst_mem_of_mem_zipIdx hPl)) m hmf

theorem mem_stackBlocksV {bs : List VBlock} {p : VBlock × ℕ} (h : p ∈ stackBlocksV bs) : p.1 ∈ bs := by
  have key : ∀ (l : List VBlock) (acc : List (VBlock × ℕ) × ℕ),
      p ∈ (l.foldl (fun (acc : List (VBlock × ℕ) × ℕ) b ↦ (acc.1 ++ [(b, acc.2)], acc.2 + 2 ^ b.κ)) acc).1 →
        p ∈ acc.1 ∨ p.1 ∈ l := by
    intro l
    induction l with
    | nil => exact fun _ h ↦ Or.inl h
    | cons b l ih =>
      intro acc h
      rcases ih _ h with h | h
      · rcases List.mem_append.mp h with h | h
        · exact Or.inl h
        · rw [List.mem_singleton.mp h]; exact Or.inr List.mem_cons_self
      · exact Or.inr (List.mem_cons_of_mem _ h)
  rcases key _ _ h with h | h
  · simp at h
  · exact List.mem_mergeSort.mp h

/-- The linear keys' leaves name their key's columns and their count's. -/
theorem termIn_keyLeaf {t : Tab} {N : List ℕ} (hN : ∀ c ∈ keyColsL t, c ∈ N)
    (hk : ∀ k ∈ t.reads.map (·.1) ++ t.seeds.map (·.1), cpolyLinB k.addr = true ∧ ∀ P ∈ k.val, cpolyLinB P = true)
    (eqα : List E) (β : E) {k : Key} (hkm : k ∈ t.reads.map (·.1) ++ t.seeds.map (·.1)) {cnt : CPoly}
    (hC : ∀ m ∈ cnt, TermIn N m.2) :
    ∀ m ∈ (leafFormV eqα β k cnt).terms, TermIn N m.1 := by
  have hl := hk k hkm
  refine termIn_leaf eqα β k cnt (termIn_cpoly hl.1 fun m hm c hc ↦ hN c ?_) hC
    fun P hP ↦ termIn_cpoly (hl.2 P hP) fun m hm c hc ↦ hN c ?_
  · exact List.mem_flatMap.mpr ⟨k, hkm, List.mem_flatMap.mpr ⟨_, List.mem_cons_self,
      List.mem_flatMap.mpr ⟨m, hm, hc⟩⟩⟩
  · exact List.mem_flatMap.mpr ⟨k, hkm, List.mem_flatMap.mpr ⟨P, List.mem_cons_of_mem _ hP,
      List.mem_flatMap.mpr ⟨m, hm, hc⟩⟩⟩

theorem termIn_one {N : List ℕ} (c : FK) (i : ℕ) (hi : i ∈ N) : ∀ m ∈ ([(c, [i])] : CPoly), TermIn N m.2 := by
  intro m hm
  obtain rfl := List.mem_singleton.mp hm
  exact Or.inr ⟨i, hi, rfl⟩

/-- Table `j`'s form on side `s`: a bucket of the side's blocks. -/
theorem formL_busResV (tabs : List Tab) (b : LBus) {j : ℕ} (hj : j < tabs.length) (s : ℕ) :
    formL (busResV tabs b) j s = ⟨bucketV ((sidesV tabs b.alphas b.beta b.point).getD s []) j⟩ := by
  have hr : (busResV tabs b).forms.getD j [] =
      (sidesV tabs b.alphas b.beta b.point).map fun sd ↦ (⟨bucketV sd j⟩ : LeanVM.Protocol.Verifier.Form) := by
    simp only [busResV, busFinalV]
    rw [List.getD_eq_getElem _ _ (by simpa using hj), List.getElem_map, List.getElem_range]
  rw [formL, hr, show (default : LeanVM.Protocol.Verifier.Form) = ⟨bucketV [] j⟩ from rfl, List.getD_map]

/-- **Every monomial of a side's form on an MB-LIN table** is a constant or one column the side names. -/
theorem termIn_formL {tabs : List Tab} (hlin : mbLinB tabs = true) (b : LBus) {j : ℕ} (hj : j < tabs.length)
    (s : ℕ) : ∀ m ∈ (formL (busResV tabs b) j s).terms, TermIn (namedL tabs[j] s) m.1 := by
  rw [formL_busResV tabs b hj]
  intro m hm
  simp only [bucketV, List.mem_flatMap, List.mem_reverse, List.mem_filter, List.mem_map] at hm
  obtain ⟨bw, ⟨hbw, htab⟩, t, ht, rfl⟩ := hm
  rw [sidesV, show ([] : List (VBlock × E)) = (stackBlocksV []).map
    (fun (bo : VBlock × ℕ) ↦ (bo.1, blockWeightV b.point bo.1.κ bo.2)) by simp [stackBlocksV],
    List.getD_map] at hbw
  obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hbw
  have hb := mem_stackBlocksV hp
  simp only [beq_iff_eq] at htab
  generalize p.1 = blk at hb htab ht
  have hlinj := List.all_eq_true.mp hlin tabs[j] (List.getElem_mem hj)
  simp only [Bool.and_eq_true, List.all_eq_true] at hlinj
  have hk := hlinj.1.2
  show TermIn _ t.1
  have hz : ∀ {tt : Tab} {j' : ℕ}, (tt, j') ∈ tabs.zipIdx → j' = j → tt = tabs[j] := by
    intro tt j' hz hj'
    subst hj'
    exact (List.mem_zipIdx' hz).2
  have h0 : ∀ c (_ : TermIn [] c), TermIn (namedL tabs[j] s) c := fun c hc ↦ by
    rcases hc with rfl | ⟨c, hc, -⟩
    · exact Or.inl rfl
    · simp at hc
  rcases s with _ | _ | _ | s
  · simp only [sideBlocksV, List.getD_cons_zero, List.mem_flatMap, List.mem_append, List.mem_map] at hb
    obtain ⟨⟨tt, j'⟩, hzm, (⟨r, hr, rfl⟩ | ⟨r, hr, rfl⟩)⟩ := hb <;> obtain rfl := hz hzm htab
    · refine termIn_keyLeaf (fun c hc ↦ ?_) hk _ _ (List.mem_append_left _ (List.mem_map_of_mem hr))
        (termIn_one _ _ ?_) t ht
      · simp [namedL, hc]
      · simp [namedL, List.mem_map_of_mem hr]
    · refine termIn_keyLeaf (fun c hc ↦ ?_) hk _ _ (List.mem_append_right _ (List.mem_map_of_mem hr))
        (fun m hm ↦ ?_) t ht
      · simp [namedL, hc]
      · obtain rfl := List.mem_singleton.mp hm; exact Or.inl rfl
  · simp only [sideBlocksV, List.getD_cons_succ, List.getD_cons_zero, List.mem_flatMap, List.mem_append,
      List.mem_map] at hb
    obtain ⟨⟨tt, j'⟩, hzm, (⟨r, hr, rfl⟩ | ⟨r, hr, rfl⟩)⟩ := hb <;> obtain rfl := hz hzm htab
    · refine termIn_keyLeaf (fun c hc ↦ ?_) hk _ _ (List.mem_append_left _ (List.mem_map_of_mem hr))
        (termIn_one _ _ ?_) t ht
      · simp [namedL, hc]
      · simp [namedL, List.mem_map_of_mem hr]
    · refine termIn_keyLeaf (fun c hc ↦ ?_) hk _ _ (List.mem_append_right _ (List.mem_map_of_mem hr))
        (termIn_one _ _ ?_) t ht
      · simp [namedL, hc]
      · simp [namedL, List.mem_map_of_mem hr]
  · simp only [sideBlocksV, List.getD_cons_succ, List.getD_cons_zero, List.mem_flatMap, List.mem_map] at hb
    obtain ⟨⟨tt, j'⟩, hzm, ⟨c, hc, rfl⟩⟩ := hb
    obtain rfl := hz hzm htab
    obtain rfl := List.mem_singleton.mp ht
    exact Or.inr ⟨c.val, by simp [namedL, List.mem_map_of_mem hc], rfl⟩
  · simp [sideBlocksV] at hb

/-! ## Affine forms -/

/-- A native form of monomials of at most one column is affine in the column values. -/
theorem evaluate_affine {ι : Type} (T : List (List ℕ × E)) (hT : ∀ m ∈ T, m.1.length ≤ 1)
    (s : Finset ι) (w : ι → E) (hw : ∑ x ∈ s, w x = 1) (col : ι → ℕ → E) :
    (⟨T⟩ : LeanVM.Protocol.Verifier.Form).evaluate (fun i ↦ ∑ x ∈ s, w x * col x i) =
      ∑ x ∈ s, w x * (⟨T⟩ : LeanVM.Protocol.Verifier.Form).evaluate (col x) := by
  simp only [evaluate_eq]
  induction T with
  | nil => simp
  | cons m T ih =>
    simp only [List.map_cons, List.sum_cons, mul_add, Finset.sum_add_distrib]
    rw [ih fun m' hm' ↦ hT m' (List.mem_cons_of_mem _ hm')]
    congr 1
    have h1 := hT m List.mem_cons_self
    rcases hc : m.1 with _ | ⟨i, _ | ⟨i', l⟩⟩
    · simp only [List.map_nil, List.prod_nil, mul_one]
      rw [← Finset.sum_mul, hw, one_mul]
    · simp only [List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one, Finset.mul_sum]
      exact Finset.sum_congr rfl fun x _ ↦ by ring
    · rw [hc] at h1; simp at h1

/-- Column `c`'s committed block value (`0` if `c` is not committed). -/
def comVal (t : Tab) (B : VPlacement → List E → E) (z : List E) (c : ℕ) : E :=
  match t.cols[c]? with
  | some (ColSrc.com _ off) => B ⟨t.τ, off⟩ z
  | _ => 0

theorem coefL_cons (m : List ℕ × E) (T : List (List ℕ × E)) (c : ℕ) :
    coefL ⟨m :: T⟩ c = (if m.1 = [c] then m.2 else 0) + coefL ⟨T⟩ c := by
  simp only [coefL, KeccakGkr.sumE_eq_sum, List.filter_cons, beq_iff_eq]
  split <;> simp

theorem constL_cons (t : Tab) (m : List ℕ × E) (T : List (List ℕ × E)) (pt : List E) :
    constL t ⟨m :: T⟩ pt = (match m.1 with
      | [] => m.2
      | [c] => match t.cols[c]? with
        | some (ColSrc.fix _ ev) => m.2 * FE.toExt3 (ev (pt.map FE.ofExt3))
        | _ => 0
      | _ => 0) + constL t ⟨T⟩ pt := by
  simp only [constL, KeccakGkr.sumE_eq_sum, List.map_cons, List.sum_cons]

theorem sum_parts_table (t : Tab) (T : List (List ℕ × E)) (SC : List ℕ) (B : VPlacement → List E → E)
    (z : List E) :
    ((SC.filterMap fun c ↦ match t.cols[c]? with
        | some (ColSrc.com _ off) => some (coefL ⟨T⟩ c, (⟨t.τ, off⟩ : VPlacement), z)
        | _ => none).map fun p ↦ p.1 * B p.2.1 p.2.2).sum =
      (SC.map fun c ↦ coefL ⟨T⟩ c * comVal t B z c).sum := by
  induction SC with
  | nil => simp
  | cons c SC ih =>
    rw [List.map_cons, List.sum_cons, ← ih]
    unfold comVal
    rcases hcol : t.cols[c]? with _ | (⟨rec, off⟩ | ⟨f, ev⟩) <;> simp [hcol]

/-- **A table's form on an MB-LIN side splits** into its constant (constant terms, fixed columns at their closed
forms) and its committed columns' blocks with their coefficients. -/
theorem evaluate_split (t : Tab) (T : List (List ℕ × E)) (N SC : List ℕ) (e : ℕ → E) (pt z : List E)
    (B : VPlacement → List E → E) (hT : ∀ m ∈ T, TermIn N m.1) (hN : ∀ c ∈ N, c < t.w → c ∈ SC)
    (hSC : SC.Nodup) (hnone : ∀ c, t.w ≤ c → e c = 0)
    (hfix : ∀ c f ev, t.cols[c]? = some (.fix f ev) → e c = FE.toExt3 (ev (pt.map FE.ofExt3)))
    (hcom : ∀ c rec off, t.cols[c]? = some (.com rec off) → e c = B ⟨t.τ, off⟩ z) :
    (⟨T⟩ : LeanVM.Protocol.Verifier.Form).evaluate e = constL t ⟨T⟩ pt +
      ((SC.filterMap fun c ↦ match t.cols[c]? with
        | some (ColSrc.com _ off) => some (coefL ⟨T⟩ c, (⟨t.τ, off⟩ : VPlacement), z)
        | _ => none).map fun p ↦ p.1 * B p.2.1 p.2.2).sum := by
  rw [sum_parts_table, ← List.sum_toFinset _ hSC]
  induction T with
  | nil => simp [evaluate_eq, constL, coefL, KeccakGkr.sumE_eq_sum]
  | cons m T ih =>
    have ih' := ih fun m' hm' ↦ hT m' (List.mem_cons_of_mem _ hm')
    rw [evaluate_eq] at ih' ⊢
    simp only [List.map_cons, List.sum_cons] at ih' ⊢
    rw [ih', constL_cons]
    simp only [coefL_cons, add_mul, Finset.sum_add_distrib]
    suffices h : m.2 * (m.1.map e).prod = (match m.1 with
        | [] => m.2
        | [c] => match t.cols[c]? with
          | some (ColSrc.fix _ ev) => m.2 * FE.toExt3 (ev (pt.map FE.ofExt3))
          | _ => 0
        | _ => 0) + ∑ c ∈ SC.toFinset, (if m.1 = [c] then m.2 else 0) * comVal t B z c by
      rw [h]; ring
    rcases hT m List.mem_cons_self with hm | ⟨c0, hc0, hm⟩
    · simp [hm]
    · rw [hm, Finset.sum_eq_single c0 (fun c _ hc ↦ by simp [Ne.symm hc]) (fun h ↦ ?_)]
      · simp only [List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one, ite_true]
        unfold comVal
        rcases hcol : t.cols[c0]? with _ | (⟨rec, off⟩ | ⟨f, ev⟩)
        · simp [hnone c0 (List.getElem?_eq_none_iff.mp hcol)]
        · simp [hcom c0 rec off hcol]
        · simp [hfix c0 f ev hcol]
      · rcases hcol : t.cols[c0]? with _ | (⟨rec, off⟩ | ⟨f, ev⟩)
        · simp [comVal, hcol]
        · exact absurd (List.mem_toFinset.mpr (hN c0 hc0 (by obtain ⟨h, -⟩ := List.getElem?_eq_some_iff.mp hcol; exact h))) h
        · simp [comVal, hcol]

/-! ## Claims on `C_main` -/

/-- A block's extension at `z` on commitment `q`: `Σ_n eq(z, n)·q[index + n]`. -/
def blkVal {μ : ℕ} (q : Column μ) (blk : VPlacement) (z : List E) : E :=
  ∑ n ∈ Finset.range (2 ^ blk.variableCount), KeccakGkr.eqAt z n * ofK (q.values.getD (blk.index + n) 0)

theorem sum_listSum {ι α : Type} (s : Finset ι) (l : List α) (f : ι → α → E) :
    ∑ x ∈ s, (l.map (f x)).sum = (l.map fun a ↦ ∑ x ∈ s, f x a).sum := by
  induction l with
  | nil => simp
  | cons a l ih => simp [Finset.sum_add_distrib, ih]

/-- **A `sumClaimE` claim on its commitment** is the combination of its parts' block extensions. -/
theorem holds_sumClaimE_iff {μ : ℕ} (parts : List (E × VPlacement × List E)) (val : E) (q : Column μ)
    (hP : ∀ p ∈ parts, p.2.2.length = p.2.1.variableCount ∧ 2 ^ p.2.1.variableCount ∣ p.2.1.index ∧
      p.2.1.index + 2 ^ p.2.1.variableCount ≤ 2 ^ μ) :
    EndToEnd.StackClaim.Holds μ (sumClaimE μ parts val).onStack q ↔
      (parts.map fun p ↦ p.1 * blkVal q p.2.1 p.2.2).sum = val := by
  unfold EndToEnd.StackClaim.Holds
  refine Eq.congr_left ?_
  have key : ∀ x : Fin (2 ^ μ),
      (sumClaimE μ parts val).onStack.1 (EndToEnd.boolPoint μ x) * ofK (q.values.getD x 0) =
        (parts.map fun p ↦ p.1 * (p.2.1.eqAbove (EndToEnd.boolPoint μ x) *
          LeanVM.Protocol.Verifier.eqEval p.2.2
            ((EndToEnd.boolPoint μ x).take p.2.1.variableCount) * ofK (q.values.getD x 0))).sum := by
    intro x
    have h1 : ({ variableCount := μ, index := 0 } : VPlacement).eqAbove (EndToEnd.boolPoint μ x) = 1 := by
      rw [Lvm.ASM.eqAbove_boolPoint (by simp) x.isLt, Nat.div_eq_of_lt x.isLt, Nat.zero_div, ite_eq_left rfl]
    have h2 : (EndToEnd.boolPoint μ x).take μ = EndToEnd.boolPoint μ x := List.take_of_length_le (by simp)
    show ({ variableCount := μ, index := 0 } : VPlacement).eqAbove (EndToEnd.boolPoint μ x) *
        LeanVM.Protocol.Verifier.sumE (parts.map fun (c, blk, z) =>
          c * blk.eqAbove ((EndToEnd.boolPoint μ x).take μ) *
            LeanVM.Protocol.Verifier.eqEval z
              (((EndToEnd.boolPoint μ x).take μ).take blk.variableCount)) *
        ofK (q.values.getD x 0) = _
    rw [h1, h2, one_mul, KeccakGkr.sumE_eq_sum, ← List.sum_map_mul_right]
    exact congrArg List.sum (List.map_congr_left fun p _ ↦ by
      obtain ⟨c, blk, z⟩ := p
      dsimp only
      ring)
  rw [Finset.sum_congr rfl fun x _ ↦ key x, sum_listSum]
  refine congrArg List.sum (List.map_congr_left fun p hp ↦ ?_)
  obtain ⟨hz, hal, hfit⟩ := hP p hp
  rw [← Finset.mul_sum]
  congr 1
  obtain ⟨c, ⟨v, off⟩, z⟩ := p
  simp only at hz hal hfit ⊢
  rw [Lvm.ASM.sum_block hal hfit]
  refine Finset.sum_congr rfl fun n _ ↦ ?_
  subst hz
  rw [EndToEnd.Front.eqEval_boolPoint_eqAt]

/-- A sum over `zipIdx` is a sum over the positions. -/
theorem sum_zipIdxFin {α : Type} (G : α × ℕ → E) : ∀ (l : List α) (k : ℕ),
    ((l.zipIdx k).map G).sum = ∑ j : Fin l.length, G (l[j], k + j)
  | [], _ => by simp
  | a :: l, k => by
    rw [List.zipIdx_cons, List.map_cons, List.sum_cons, sum_zipIdxFin G l (k + 1)]
    refine Eq.trans ?_ (Fin.sum_univ_succ (n := l.length) fun j ↦ G ((a :: l)[j], k + j)).symm
    simp only [Fin.getElem_fin, Fin.val_zero, List.getElem_cons_zero, add_zero, Fin.val_succ,
      List.getElem_cons_succ]
    congr 1
    exact Finset.sum_congr rfl fun j _ ↦ by rw [Nat.add_assoc, Nat.add_comm 1]

/-! ## The protocol's forms at the stack -/

/-- A column's extension is its rows against the Lagrange basis. -/
theorem colMle_eq {I : M3Instance} (q : Column I.μ) (j : Fin I.ntab) (z : Vector E (I.τ j)) (i : Fin (I.width j)) :
    eval₂Mle (I.column q ⟨j, i⟩).values (algebraMap K E) z =
      ∑ x : Fin (2 ^ I.τ j), (lagrangeBasis z)[x] * algebraMap K E (I.row q j x i) := by
  rw [eval₂Mle, evalMle_eq_sum]
  refine Finset.sum_congr rfl fun x _ ↦ ?_
  simp [CMlPolynomialEval.map, M3Instance.row, mul_comm, Vector.get_eq_getElem]

/-- A form's value is its rows' values against the Lagrange basis. -/
theorem formEval_eq_sum {I : M3Instance} (q : Column I.μ) (j : Fin I.ntab) (f : I.Form j) (z : Vector E (I.τ j)) :
    M3Instance.Form.eval I f q z =
      ∑ x : Fin (2 ^ I.τ j), (lagrangeBasis z)[x] * TableSumcheck.formAt f (fun i ↦ ofK (I.row q j x i)) := by
  induction f with
  | nil => simp [TableSumcheck.formAt, M3Instance.Form.eval]
  | cons p f ih =>
    simp only [TableSumcheck.formAt, M3Instance.Form.eval, List.map_cons, List.sum_cons] at ih ⊢
    rw [ih, evalMle_eq_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun x _ ↦ ?_
    rw [TableSumcheck.evalRow_ofK]
    simp only [M3Instance.virtualTable, Fin.getElem_fin, Vector.getElem_ofFn]
    ring

/-! ## MBL-STMT 2 at the lvm instance -/

theorem rec_false {tabs : List Tab} (hlin : mbLinB tabs = true) {t : Tab} (ht : t ∈ tabs) {c : ℕ} {rec : Bool}
    {off : ℕ} (hcol : t.cols[c]? = some (.com rec off)) : rec = false := by
  have h := List.all_eq_true.mp hlin t ht
  simp only [Bool.and_eq_true, List.all_eq_true] at h
  have := h.2 _ (List.mem_of_getElem? hcol)
  simpa using this

section Lvm

variable (L : Lay) (tabs : List Tab) (hτ : ∀ t ∈ tabs, t.τ ≤ L.μ) (hsc : AllSc tabs)

/-- The bus phase's point, at table `j`: the GKR point's first `τ_j` coordinates. -/
theorem lowPoint_lvm (b : LBus) (hp : b.point.length = (inst L tabs hτ).μBus) (j : Fin tabs.length) :
    ((inst L tabs hτ).lowPoint (lbusStmt (inst L tabs hτ) (condOf L tabs hτ hsc) () b (vals0 L tabs hτ)).2.point
      (stEq L tabs hτ hsc j)).toList = b.point.take tabs[j].τ := by
  have h1 := (inst L tabs hτ).τ_le_τmax (stEq L tabs hτ hsc j)
  have h2 := (condOf L tabs hτ hsc).τmax_le
  rw [toList_lowPoint]
  apply List.ext_getElem
  · simp only [List.length_take, Vector.length_toList, hp]
    show min (tabs.get j).τ _ = min (tabs.get j).τ _
    have : (tabs.get j).τ ≤ (inst L tabs hτ).τmax := h1
    omega
  · intro a ha1 ha2
    rw [List.getElem_take, List.getElem_take, Vector.getElem_toList]
    simp [lbusStmt, Bus.busOut, Bus.point, Gkr.lowPoint, EndToEnd.Front.layerStmtOf, EndToEnd.Front.vecOf,
      List.getElem?_eq_getElem (show a < b.point.length by simp at ha2; omega)]

/-- Table `j`'s parts on side `s` (`mbPartsL`'s block of table `j`). -/
def partsT (r : BusResult) (t : Tab) (j s : ℕ) : List (E × VPlacement × List E) :=
  (sideColsL t s).filterMap fun c ↦ match t.cols[c]? with
    | some (ColSrc.com _ off) => some (coefL (formL r j s) c, ⟨t.τ, off⟩, r.point.take t.τ)
    | _ => none

/-- **Table `j`'s form on side `s` at the stack** is its constant plus its committed columns' blocks of `C_main`. -/
theorem formEval_lvm (hlay : LayOk L tabs) (hfix : FixOk tabs) (hkey : KeysOk tabs) (hlin : mbLinB tabs = true)
    (b : LBus) (ha : b.alphas.length = 4) (hp : b.point.length = (inst L tabs hτ).μBus)
    (qm : Column L.nuMain) (qr : Column L.nuRec) (s : Fin 3) (j : Fin tabs.length) :
    M3Instance.Form.eval (inst L tabs hτ)
        ((lbusStmt (inst L tabs hτ) (condOf L tabs hτ hsc) () b (vals0 L tabs hτ)).2.forms s (stEq L tabs hτ hsc j))
        (stackOf L qm qr)
        ((inst L tabs hτ).lowPoint (lbusStmt (inst L tabs hτ) (condOf L tabs hτ hsc) () b (vals0 L tabs hτ)).2.point
          (stEq L tabs hτ hsc j)) =
      constL tabs[j] (formL (busResV tabs b) j s) (b.point.take tabs[j].τ) +
        ((partsT (busResV tabs b) tabs[j] j s).map fun p ↦ p.1 * blkVal qm p.2.1 p.2.2).sum := by
  have hzl := lowPoint_lvm L tabs hτ hsc b hp j
  set z := (inst L tabs hτ).lowPoint (lbusStmt (inst L tabs hτ) (condOf L tabs hτ hsc) () b (vals0 L tabs hτ)).2.point
    (stEq L tabs hτ hsc j) with hz
  set q := stackOf L qm qr
  have hT := termIn_formL hlin b j.isLt s.val
  rw [formEval_eq_sum]
  have hfa : ∀ x, TableSumcheck.formAt
      ((lbusStmt (inst L tabs hτ) (condOf L tabs hτ hsc) () b (vals0 L tabs hτ)).2.forms s (stEq L tabs hτ hsc j))
      (fun i ↦ ofK ((inst L tabs hτ).row q (stEq L tabs hτ hsc j).1 x i)) =
      (formL (busResV tabs b) j s).evaluate (rowE fun i ↦ ofK ((inst L tabs hτ).row q (stEq L tabs hτ hsc j).1 x i)) :=
    fun x ↦ formAt_busResV L tabs hτ hsc hkey b ha hp s (stEq L tabs hτ hsc j) _
  rw [Finset.sum_congr rfl fun x _ ↦ by rw [hfa x]]
  rw [partsT, show (busResV tabs b).point = b.point from rfl]
  generalize hF : formL (busResV tabs b) j s = F at hT ⊢
  obtain ⟨T⟩ := F
  have hw : ∑ x : Fin (2 ^ (inst L tabs hτ).τ (stEq L tabs hτ hsc j).1), (lagrangeBasis z)[x] = 1 := by
    simpa [sumCube] using sumCube_lagrangeBasis z
  rw [← evaluate_affine T (fun m hm ↦ by rcases hT m hm with h | ⟨c, -, h⟩ <;> simp [h]) _ _ hw]
  have hE : ∀ c (h : c < tabs[j].w), (∑ x : Fin (2 ^ (inst L tabs hτ).τ (stEq L tabs hτ hsc j).1),
      (lagrangeBasis z)[x] * rowE (fun i ↦ ofK ((inst L tabs hτ).row q (stEq L tabs hτ hsc j).1 x i)) c) =
      eval₂Mle ((inst L tabs hτ).column q ⟨(stEq L tabs hτ hsc j).1, ⟨c, h⟩⟩).values (algebraMap K E) z := by
    intro c h
    rw [colMle_eq]
    refine Finset.sum_congr rfl fun x _ ↦ ?_
    have h' : c < (tabs.get (stEq L tabs hτ hsc j).1).w := h
    simp only [rowE, h', dite_true]
    rfl
  refine evaluate_split tabs[j] T (namedL tabs[j] s) (sideColsL tabs[j] s) _ (b.point.take tabs[j].τ)
    (b.point.take tabs[j].τ) (blkVal qm) hT (fun c hc hcw ↦ ?_) ((List.nodup_range).filter _)
    (fun c hc ↦ ?_) (fun c f ev hcol ↦ ?_) (fun c rec off hcol ↦ ?_)
  · rw [sideColsL_eq, List.mem_filter, List.mem_range]
    exact ⟨hcw, List.elem_iff.mpr hc⟩
  · refine Finset.sum_eq_zero fun x _ ↦ ?_
    simp only [rowE]
    rw [dite_eq_right_of_eq_false (eq_false (show ¬ c < (tabs.get (stEq L tabs hτ hsc j).1).w from not_lt.mpr hc)),
      mul_zero]
  · have hcw : c < tabs[j].w := by obtain ⟨h, -⟩ := List.getElem?_eq_some_iff.mp hcol; exact h
    rw [hE c hcw]
    have hcolq : (inst L tabs hτ).column q ⟨(stEq L tabs hτ hsc j).1, ⟨c, hcw⟩⟩ = fixedColumn tabs[j].τ f := by
      have hfo : (tabs.get j).fixedOf c = some f := by
        show (match tabs[j].cols[c]? with | some (.fix f _) => some f | _ => none) = _
        rw [hcol]
      show (((tabs.get j).fixedOf c).map fun f _ ↦ fixedColumn (tabs.get j).τ f).elim
        ((layout L tabs hτ).read q ⟨j, ⟨c, hcw⟩⟩) (fun f ↦ f q) = _
      rw [hfo]
      rfl
    have hzl' : @Vector.toList E tabs[j].τ z = List.take tabs[j].τ b.point := hzl
    have hl : ((b.point.take tabs[j].τ).map FE.ofExt3).length = tabs[j].τ := by
      rw [List.length_map, ← hzl']; exact z.length_toList
    rw [hcolq]
    refine (toExt3_mle_fixed (τ := tabs[j].τ) f z).symm.trans ?_
    rw [hzl', ← hfix _ (List.getElem_mem j.isLt) f ev (List.mem_of_getElem? hcol) _ hl]
  · have hcw : c < tabs[j].w := by obtain ⟨h, -⟩ := List.getElem?_eq_some_iff.mp hcol; exact h
    rw [hE c hcw]
    obtain rfl := rec_false hlin (List.getElem_mem j.isLt) hcol
    rw [show (inst L tabs hτ).column q ⟨(stEq L tabs hτ hsc j).1, ⟨c, hcw⟩⟩ =
      comBlock L qm qr false tabs[j].τ off from column_stackOf L tabs hτ hlay qm qr j ⟨c, hcw⟩ hcol]
    refine (EndToEnd.Front.eval₂Mle_eq_sum_eqAt (n := tabs[j].τ) _ z).trans ?_
    have hzl' : @Vector.toList E tabs[j].τ z = List.take tabs[j].τ b.point := hzl
    rw [hzl']
    unfold blkVal
    refine Finset.sum_congr rfl fun n hn ↦ ?_
    have hn' : n < 2 ^ tabs[j].τ := Finset.mem_range.mp hn
    congr 2
    simp only [comBlock, comCell, Vector.getD, Bool.false_eq_true, ite_false]
    have hn2 : n < 2 ^ tabs[(j : ℕ)].τ := hn'
    by_cases h : off + n < 2 ^ L.nuMain <;> simp [hn2, h]

theorem sum_map_flatMap {α β : Type} (l : List α) (g : α → List β) (f : β → E) :
    ((l.flatMap g).map f).sum = (l.map fun a ↦ ((g a).map f).sum).sum := by
  induction l with
  | nil => simp
  | cons a l ih => simp [List.flatMap_cons, ih]

theorem add_eq_iff_char2 (a b c : E) : a + b = c ↔ b = c + a := by
  constructor
  · rintro rfl; rw [add_comm a b, add_assoc, CharTwo.add_self_eq_zero, add_zero]
  · rintro rfl; rw [add_comm c a, ← add_assoc, CharTwo.add_self_eq_zero, zero_add]

include hsc in
/-- The parts are aligned blocks of `C_main` at points of their height. -/
theorem parts_ok (hlay : LayOk L tabs) (hlin : mbLinB tabs = true) (b : LBus)
    (hp : b.point.length = (inst L tabs hτ).μBus) (s : ℕ) :
    ∀ p ∈ mbPartsL tabs (busResV tabs b) s, p.2.2.length = p.2.1.variableCount ∧
      2 ^ p.2.1.variableCount ∣ p.2.1.index ∧ p.2.1.index + 2 ^ p.2.1.variableCount ≤ 2 ^ L.nuMain := by
  intro p hpm
  obtain ⟨⟨t, j'⟩, hz, hpt⟩ := List.mem_flatMap.mp hpm
  obtain ⟨hj', ht⟩ := List.mem_zipIdx' hz
  have ht2 : t = tabs[j']'hj' := ht
  subst ht2
  obtain ⟨c, -, hsome⟩ := List.mem_filterMap.mp hpt
  rcases hcol : tabs[j'].cols[c]? with _ | (⟨rec, off⟩ | ⟨f, ev⟩) <;> simp only [hcol] at hsome
  · cases hsome
  · cases hsome
    obtain rfl := rec_false hlin (List.getElem_mem hj') hcol
    have hτj : tabs[j'].τ ≤ b.point.length := by
      have h1 := (inst L tabs hτ).τ_le_τmax (stEq L tabs hτ hsc ⟨j', hj'⟩)
      have h2 := (condOf L tabs hτ hsc).τmax_le
      have h3 : tabs[j'].τ ≤ (inst L tabs hτ).τmax := h1
      omega
    have hcw : c < tabs[j'].w := by obtain ⟨h, -⟩ := List.getElem?_eq_some_iff.mp hcol; exact h
    have hal := hlay _ (List.getElem_mem hj') c hcw
    unfold Aligned at hal
    rw [hcol] at hal
    obtain ⟨hd, hf, -⟩ := hal
    refine ⟨?_, hd, by simpa using hf⟩
    show (List.take tabs[j'].τ b.point).length = tabs[j'].τ
    simp [hτj]
  · cases hsome

end Lvm

/-! ## MBL-STMT 2: the bus seam's forms are the three claims -/

/-- **MBL-STMT 2** (owner L): **on MB-LIN tables, the bus phase's forms hold iff the three linear claims do**: at
the protocol's output on what the bus phase read (`lbusStmt`, no boundary value), every side's forms sum to the side's
total on the stack of the two commitments iff `mbClaimsL`'s three claims hold on `C_main`. -/
theorem mbClaimsL_iff (L : Lay) (tabs : List Tab) (hτ : ∀ t ∈ tabs, t.τ ≤ L.μ) (hsc : AllSc tabs)
    (hlay : LayOk L tabs) (hfix : FixOk tabs) (hkey : KeysOk tabs) (hlin : mbLinB tabs = true) (b : LBus)
    (hb : b.alphas.length = 4 ∧ b.point.length = (inst L tabs hτ).μBus ∧ b.values.length = 3)
    (qm : Column L.nuMain) (qr : Column L.nuRec) :
    (∀ side, ∑ j : (inst L tabs hτ).SumcheckTables,
        M3Instance.Form.eval (inst L tabs hτ)
          ((lbusStmt (inst L tabs hτ) (condOf L tabs hτ hsc) () b (vals0 L tabs hτ)).2.forms side j)
          (stackOf L qm qr)
          ((inst L tabs hτ).lowPoint
            (lbusStmt (inst L tabs hτ) (condOf L tabs hτ hsc) () b (vals0 L tabs hτ)).2.point j) =
        (lbusStmt (inst L tabs hτ) (condOf L tabs hτ hsc) () b (vals0 L tabs hτ)).2.totals side) ↔
      ∀ c ∈ mbClaimsL L.nuMain tabs b, LeanVM.Protocol.EndToEnd.StackClaim.Holds L.nuMain c.onStack qm := by
  obtain ⟨ha, hp, -⟩ := hb
  set r := busResV tabs b
  have hside : ∀ s : Fin 3, (∑ j : (inst L tabs hτ).SumcheckTables,
        M3Instance.Form.eval (inst L tabs hτ)
          ((lbusStmt (inst L tabs hτ) (condOf L tabs hτ hsc) () b (vals0 L tabs hτ)).2.forms s j)
          (stackOf L qm qr)
          ((inst L tabs hτ).lowPoint
            (lbusStmt (inst L tabs hτ) (condOf L tabs hτ hsc) () b (vals0 L tabs hτ)).2.point j)) =
      (∑ j : Fin tabs.length, constL tabs[j] (formL r j s) (b.point.take tabs[j].τ)) +
        ∑ j : Fin tabs.length, ((partsT r tabs[j] j s).map fun p ↦ p.1 * blkVal qm p.2.1 p.2.2).sum := by
    intro s
    rw [← Finset.sum_add_distrib]
    refine ((stEq L tabs hτ hsc).sum_comp _).symm.trans (Finset.sum_congr rfl fun j _ ↦ ?_)
    exact formEval_lvm L tabs hτ hsc hlay hfix hkey hlin b ha hp qm qr s j
  have hclaim : ∀ s : ℕ, (LeanVM.Protocol.EndToEnd.StackClaim.Holds L.nuMain
      (mbClaimL L.nuMain tabs r s).onStack qm ↔
      ∑ j : Fin tabs.length, ((partsT r tabs[j] j s).map fun p ↦ p.1 * blkVal qm p.2.1 p.2.2).sum =
        r.totals.getD s 0 + ∑ j : Fin tabs.length, constL tabs[j] (formL r j s) (b.point.take tabs[j].τ)) := by
    intro s
    rw [mbClaimL, holds_sumClaimE_iff _ _ _ (parts_ok L tabs hτ hsc hlay hlin b hp s)]
    have hP : mbPartsL tabs r s = tabs.zipIdx.flatMap fun tj ↦ partsT r tj.1 tj.2 s := rfl
    rw [hP, sum_map_flatMap, sum_zipIdxFin, mbValueL, KeccakGkr.sumE_eq_sum, sum_zipIdxFin]
    simp only [Nat.zero_add]
    rfl
  simp only [mbClaimsL, List.mem_map, List.mem_range, forall_exists_index, and_imp,
    forall_apply_eq_imp_iff₂]
  constructor
  · intro h s hs
    have := h ⟨s, hs⟩
    rw [hside, ← totals_busResV L tabs hτ hsc b hp] at this
    exact (hclaim s).mpr ((add_eq_iff_char2 _ _ _).mp this)
  · intro h side
    rw [hside, ← totals_busResV L tabs hτ hsc b hp]
    exact (add_eq_iff_char2 _ _ _).mpr ((hclaim side).mp (h side side.isLt))

/-- The three claims are three. -/
theorem length_mbClaimsL (nu : ℕ) (tabs : List Tab) (b : LBus) : (mbClaimsL nu tabs b).length = 3 := by
  simp [mbClaimsL]

end Lvm.M3
