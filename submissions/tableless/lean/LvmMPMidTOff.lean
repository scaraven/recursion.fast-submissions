/- `LvmMPMidTOff` (GOLF2 off-path move, group 4 of 48): declarations that the certificate `certified`
   does not use, moved here verbatim (same names, same namespaces and context) from LvmClaims, LvmLayoutStack, LvmRingFidelity, LvmTypedAcc, LvmTypedSpecP, LvmTypedSpec, LvmMPMidT,
   so that `Solution`'s import closure need not elaborate them. Import this module where they are needed;
   the name -> module map is GOLF2's moved.tsv. -/
import LvmClaims
import LvmLayoutStack
import LvmRingFidelity
import LvmTypedAcc
import LvmTypedSpecP
import LvmTypedSpec
import LvmMPMidT
import LvmE2QNodeChkGOff
import LvmM3MidCertOff
import LvmMPCertOff
import LvmChainTablePad
import LvmJBMutual
import LvmMlListLemmas
import LvmSpecRulesCert

-- ===== from `LvmClaims` =====

section
namespace LeanVM.Protocol.Verifier
open LeanVM.Parameters
open LeanVM.Semantics LeanVM.Protocol.Compile
section

/-- Step 7's ring-switching claim on the stack: supported on `q_keccak`'s region, its weight
carries the placement's selector (`lib.rs:305-311`). -/
def ringSwitchClaim (layout : Layout) (target : E) (weight : List E → E) : StackClaim :=
  let qkeccakPlacement := layout.placement qkeccak
  (fun x ↦ qkeccakPlacement.eqAbove x * weight (x.take qkeccakPlacement.variableCount), target)

end
end LeanVM.Protocol.Verifier
end

section
namespace LeanVM.Protocol.Verifier
open LeanVM.Parameters
open LeanVM.Semantics LeanVM.Protocol.Compile
section
namespace Claims

theorem allRet_of_forall {α : Type} {P : α → Prop} (h : ∀ a, P a) : ∀ p : VerifierProgram α,
    AllRet p P
  | .ret a => .ret (h a)
  | .fail => .fail
  | .read k => .read fun x ↦ allRet_of_forall h (k x)
  | .sample k => .sample fun c ↦ allRet_of_forall h (k c)
  | .grind _ k => .grind (allRet_of_forall h k)
  | .commit _ _ k => .commit (allRet_of_forall h k)
  | .query _ _ k => .query fun r ↦ allRet_of_forall h (k r)

theorem allRet_true {α : Type} (p : VerifierProgram α) : AllRet p fun _ ↦ True :=
  allRet_of_forall (fun _ ↦ trivial) p

end Claims
end
end LeanVM.Protocol.Verifier
end

section
namespace LeanVM.Protocol.Verifier
open LeanVM.Parameters
open LeanVM.Semantics LeanVM.Protocol.Compile
section
namespace Claims

/-- Two continuations that agree on every value a program returns make one program. -/
theorem bind_congr {α β : Type} {Q : α → Prop} {f g : α → VerifierProgram β} (h : ∀ a, Q a → f
    a = g a)
    (p : VerifierProgram α) (hp : AllRet p Q) : p.bind f = p.bind g := by
  induction hp with
  | ret hq => exact h _ hq
  | fail => rfl
  | read _ ih => exact congrArg VerifierProgram.read (funext ih)
  | sample _ ih => exact congrArg VerifierProgram.sample (funext ih)
  | grind _ ih => exact congrArg (VerifierProgram.grind _) ih
  | commit _ ih => exact congrArg (VerifierProgram.commit _ _) ih
  | query _ ih => exact congrArg (VerifierProgram.query _ _) (funext ih)

theorem allRet_readN : ∀ n : ℕ, AllRet (VerifierProgram.readScalars n) fun xs ↦ xs.length = n
  | 0 => .ret rfl
  | n + 1 => .read fun x ↦
    AllRet.bind (fun xs hxs ↦ .ret (by show (x :: xs).length = n + 1; simp [hxs])) _
      (allRet_readN n)

theorem allRet_liftOption {α : Type} (o : Option α) : AllRet (liftOption o) fun a ↦ o = some a := by
  cases o with
  | none => exact .fail
  | some a => exact .ret rfl

end Claims
end
end LeanVM.Protocol.Verifier
end

-- ===== from `LvmLayoutStack` =====

section
namespace LeanVM.Protocol.EndToEnd.Front
open LeanVM.Parameters LeanVM.Protocol.Verifier List
section

/-- Two indices that occur in both orders in a list without duplicates are equal. -/
theorem eq_of_pair_sublist {L : List ℕ} (hL : L.Nodup) {a b : ℕ} (h1 : [a, b] <+ L)
    (h2 : [b, a] <+ L) : a = b := by
  have key : ∀ {x y}, [x, y] <+ L → x ≠ y → L.idxOf x < L.idxOf y := by
    intro x y h hxy
    obtain ⟨r1, r2, rfl, hx, hy⟩ := List.cons_sublist_iff.mp h
    have hy' : y ∈ r2 := List.singleton_sublist.mp hy
    have hy1 : y ∉ r1 := fun hy1 ↦ List.disjoint_of_nodup_append hL hy1 hy'
    rw [List.idxOf_append_of_mem hx, List.idxOf_append_of_notMem hy1]
    have := List.idxOf_lt_length_of_mem hx
    omega
  by_contra hab
  have := key h1 hab
  have := key h2 (Ne.symm hab)
  omega

/-- Two increasing indices occur in that order in the range. -/
theorem pair_sublist_range {n a b : ℕ} (hab : a < b) (hb : b < n) : [a, b] <+ List.range n := by
  have : List.range n = List.range (a + 1) ++ (List.range (n - (a + 1))).map (a + 1 + ·) := by
    rw [← List.range_add]; congr 1; omega
  rw [this, show [a, b] = [a] ++ [b] from rfl]
  refine List.Sublist.append ?_ ?_
  · exact List.singleton_sublist.mpr (List.mem_range.mpr (by omega))
  · exact List.singleton_sublist.mpr
      (List.mem_map.mpr ⟨b - (a + 1), List.mem_range.mpr (by omega), by omega⟩)

/-- The comparator of `stack_offsets`. -/
def stackLe (size : ℕ → ℕ) (i j : ℕ) : Bool :=
  decide (size j < size i) || (decide (size i = size j) && decide (i ≤ j))

/-- `stack_offsets`' order is the stable sort by size, larger first: breaking ties by index is
what `mergeSort`'s stability does. -/
theorem mergeSort_range_stackLe (size : ℕ → ℕ) (n : ℕ) :
    (List.range n).mergeSort (stackLe size) =
      (List.range n).mergeSort fun i j ↦ decide (size j ≤ size i) := by
  have trans1 : ∀ a b c, stackLe size a b → stackLe size b c → stackLe size a c := by
    intro a b c; simp only [stackLe, Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq]; omega
  have total1 : ∀ a b, stackLe size a b || stackLe size b a := by
    intro a b; simp only [stackLe, Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq]; omega
  have trans2 : ∀ a b c : ℕ, decide (size b ≤ size a) → decide (size c ≤ size b) →
      decide (size c ≤ size a) := by
    intro a b c; simp only [decide_eq_true_eq]; omega
  have total2 : ∀ a b : ℕ, decide (size b ≤ size a) || decide (size a ≤ size b) := by
    intro a b; simp only [Bool.or_eq_true, decide_eq_true_eq]; omega
  apply List.Perm.eq_of_pairwise (le := fun a b ↦ stackLe size a b = true)
  · intro a b _ _ h1 h2
    simp only [stackLe, Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq] at h1 h2
    omega
  · exact List.pairwise_mergeSort trans1 total1 _
  · have hs := List.pairwise_mergeSort trans2 total2 (List.range n)
    have hnd : ((List.range n).mergeSort fun i j ↦ decide (size j ≤ size i)).Nodup :=
      (List.mergeSort_perm _ _).nodup_iff.mpr List.nodup_range
    rw [List.pairwise_iff_forall_sublist] at hs ⊢
    intro a b hab
    have hle := hs hab
    simp only [decide_eq_true_eq] at hle
    simp only [stackLe, Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq]
    by_cases hlt : size b < size a
    · exact Or.inl hlt
    · refine Or.inr ⟨by omega, ?_⟩
      by_contra hba
      have hmem := fun x (hx : x ∈ [a, b]) ↦
        (List.mergeSort_perm (List.range n) _).mem_iff.mp (hab.subset hx)
      have hb := List.mem_range.mp (hmem a (by simp))
      have h2 := List.pair_sublist_mergeSort trans2 total2 (by simp only [decide_eq_true_eq]; omega)
        (pair_sublist_range (n := n) (show b < a by omega) hb)
      have := eq_of_pair_sublist hnd hab h2
      omega
  · exact (List.mergeSort_perm _ _).trans (List.mergeSort_perm _ _).symm
/-- The step of `stack_offsets`' fold. -/
def placeStep (w : ℕ → ℕ) (acc : List ℕ × ℕ) (i : ℕ) : List ℕ × ℕ :=
  (acc.1.set i acc.2, acc.2 + w i)

/-- The running total of the fold: the sum of the heights. -/
theorem placeFold_snd (w : ℕ → ℕ) (l : List ℕ) (acc : List ℕ × ℕ) :
    (l.foldl (placeStep w) acc).2 = acc.2 + (l.map w).sum := by
  induction l generalizing acc with
  | nil => simp
  | cons a l ih => simp [ih, placeStep]; omega

/-- The fold keeps the length of the offset list. -/
theorem placeFold_length (w : ℕ → ℕ) (l : List ℕ) (acc : List ℕ × ℕ) :
    (l.foldl (placeStep w) acc).1.length = acc.1.length := by
  induction l generalizing acc with
  | nil => simp
  | cons a l ih => simp [ih, placeStep]

/-- An index the fold does not visit keeps its entry. -/
theorem placeFold_getElem?_of_not_mem (w : ℕ → ℕ) (l : List ℕ) (acc : List ℕ × ℕ) (i : ℕ)
    (hi : i ∉ l) : (l.foldl (placeStep w) acc).1[i]? = acc.1[i]? := by
  induction l generalizing acc with
  | nil => simp
  | cons a l ih =>
    simp only [List.mem_cons, not_or] at hi
    simp only [List.foldl_cons]
    rw [ih _ hi.2]
    simp [placeStep, Ne.symm hi.1]

/-- The offset of the `k`-th index of the order: the running total plus the heights before
it. -/
theorem placeFold_getElem? (w : ℕ → ℕ) (l : List ℕ) (hl : l.Nodup) (acc : List ℕ × ℕ)
    (hlt : ∀ i ∈ l, i < acc.1.length) (k : ℕ) (hk : k < l.length) :
    (l.foldl (placeStep w) acc).1[l[k]]? = some (acc.2 + ((l.take k).map w).sum) := by
  induction l generalizing acc k with
  | nil => simp at hk
  | cons a l ih =>
    simp only [List.foldl_cons]
    rcases k with _ | k
    · simp only [List.getElem_cons_zero, List.take_zero, List.map_nil, List.sum_nil, add_zero]
      rw [placeFold_getElem?_of_not_mem _ _ _ _ (List.nodup_cons.mp hl).1]
      simp [placeStep, hlt a (by simp)]
    · simp only [List.getElem_cons_succ, List.take_succ_cons, List.map_cons, List.sum_cons]
      rw [ih (List.nodup_cons.mp hl).2 _
        (fun i hi ↦ by simpa [placeStep] using hlt i (by simp [hi]))
        k (by simpa using hk)]
      simp [placeStep, add_assoc]

/-- `stack_offsets(sizes)`: the stable sort by size, and the fold of the heights along it. -/
theorem stackOffsets_eq (sizes : List ℕ) :
    stackOffsets sizes =
      let order := (List.range sizes.length).mergeSort
        fun i j ↦ decide (sizes.getD j 0 ≤ sizes.getD i 0)
      let placed := order.foldl (placeStep fun i ↦ 2 ^ sizes.getD i 0)
        (List.replicate sizes.length 0, 0)
      (placed.1, log2Ceil placed.2) := by
  show (_, _) = _
  simp only
  rw [← mergeSort_range_stackLe]
  rfl

end
end LeanVM.Protocol.EndToEnd.Front
end

section
namespace LeanVM.Protocol.EndToEnd.Front
open LeanVM.Parameters LeanVM.Protocol.Verifier List
section

/-- **A placed point**: the point, then the bits of the index above the window. -/
theorem stackPoint_aligned (v off μ : ℕ) (z : List E) :
    ({ variableCount := v, index := off } : Placement).stackPoint z μ =
      z ++ boolPoint (μ - v) (off / 2 ^ v) := by
  simp [Placement.stackPoint, selectorPoint_eq_boolPoint, Nat.shiftRight_eq_div_pow]

end
end LeanVM.Protocol.EndToEnd.Front
end

section
namespace LeanVM.Protocol.EndToEnd.Front
open LeanVM.Parameters LeanVM.Protocol.Verifier List
section

/-- **A slice placement** at slot `slot` of an aligned region of `2 ^ (v + k)` cells at `off`
(`index = off + slot · 2 ^ v`): the point, the slot's bits, then the region's bits
above it. -/
theorem stackPoint_slice (v k off slot μ : ℕ) (hk : v + k ≤ μ) (hoff : 2 ^ (v + k) ∣ off)
    (hslot : slot < 2 ^ k) (z : List E) :
    ({ variableCount := v, index := off + slot * 2 ^ v } : Placement).stackPoint z μ =
      z ++ boolPoint k slot ++ boolPoint (μ - (v + k)) (off / 2 ^ (v + k)) := by
  rw [stackPoint_aligned, List.append_assoc]
  congr 1
  obtain ⟨m, rfl⟩ := hoff
  have hdiv : (2 ^ (v + k) * m + slot * 2 ^ v) / 2 ^ v = slot + 2 ^ k * m := by
    rw [pow_add, show 2 ^ v * 2 ^ k * m + slot * 2 ^ v = 2 ^ v * (slot + 2 ^ k * m) by ring,
      Nat.mul_div_cancel_left _ (Nat.two_pow_pos _)]
  rw [hdiv, Nat.mul_div_cancel_left _ (Nat.two_pow_pos _),
    show μ - v = k + (μ - (v + k)) by omega, boolPoint_add_two_pow_mul _ _ _ _ hslot]

end
end LeanVM.Protocol.EndToEnd.Front
end

-- ===== from `LvmRingFidelity` =====

section
section
namespace LeanVM.Protocol.EndToEnd.Complete
open LeanVM.Prover (Script)
open LeanVM.Parameters LeanVM.Protocol.Compile LeanVM.Protocol.Verifier
open LeanVM.Protocol.Whir.Complete LeanVM.Protocol.EndToEnd Finset
section

/-- The extension of a table at a cube point is the table's entry. -/
theorem multilinearEval_boolPoint {m : ℕ} {t : List E} (ht : t.length = 2 ^ m) {l : ℕ}
    (hl : l < 2 ^ m) : multilinearEval t (boolPoint m l) = t.getD l 0 := by
  rw [multilinearEval_eq_sum m t _ ht (length_boolPoint m l)]
  rw [sum_congr rfl fun i hi ↦ by
    rw [eqEval_boolPoint_boolPoint m i l (mem_range.mp hi) hl]]
  simp [mem_range.mpr hl]

/-- **Partial evaluation by blocks.** Fixing the first `a` coordinates at `y`: the extension at
`y ++ x` is the extensions at the cube points `j ++ x`, weighted by `eq(j, y)`. -/
theorem multilinearEval_append {a d : ℕ} {t : List E} (ht : t.length = 2 ^ (a + d)) {y x : List E}
    (hy : y.length = a) (hx : x.length = d) :
    multilinearEval t (y ++ x) =
      ∑ j ∈ range (2 ^ a), multilinearEval t (boolPoint a j ++ x) * eqEval (boolPoint a j) y := by
  have hfold : ∀ r : List E, r.length = a →
      multilinearEval t (r ++ x) = multilinearEval (foldAll t r) x := fun r _ ↦ by
    rw [multilinearEval_eq_foldAll, multilinearEval_eq_foldAll, foldAll_append]
  have hlen : ∀ r : List E, r.length = a → (foldAll t r).length = 2 ^ d := fun r hr ↦
    length_foldAll r t d (by rw [hr, ht])
  have hentry : ∀ r : List E, r.length = a → ∀ i ∈ range (2 ^ d),
      (foldAll t r).getD i 0 =
        ∑ j ∈ range (2 ^ a), eqEval (boolPoint a j) r * t.getD (j + 2 ^ a * i) 0 :=
    fun r hr i hi ↦ by
      rw [getD_foldAll r t d i (by rw [hr, ht]) (mem_range.mp hi), hr]
  rw [hfold y hy, multilinearEval_eq_sum d _ x (hlen y hy) hx,
    sum_congr rfl fun i hi ↦ by rw [hentry y hy i hi]]
  simp_rw [sum_mul]
  rw [sum_comm]
  refine sum_congr rfl fun j hj ↦ ?_
  rw [hfold _ (length_boolPoint a j),
    multilinearEval_eq_sum d _ x (hlen _ (length_boolPoint a j)) hx, sum_mul]
  refine sum_congr rfl fun i hi ↦ ?_
  rw [hentry _ (length_boolPoint a j) i hi]
  rw [sum_congr rfl fun j' hj' ↦ by
    rw [eqEval_boolPoint_boolPoint a j' j (mem_range.mp hj') (mem_range.mp hj)]]
  simp only [ite_mul, one_mul, zero_mul, sum_ite_eq', hj, ↓reduceIte]
  rw [eqEval_comm]
  ring

/-- The equality weight is affine in any one coordinate of its second point. -/
theorem polyLE_eqEval : ∀ (u a v : List E), PolyLE 1 fun X ↦ eqEval a (u ++ X :: v)
  | [], [], v => (PolyLE.const 1 1).congr fun X ↦ by simp
  | [], a₀ :: a, v =>
    ((PolyLE.affine (1 + a₀) 1).mul (PolyLE.const 0 (eqEval a v))).congr fun X ↦ by
      rw [List.nil_append, eqEval_cons]; ring
  | _ :: _, [], v => (PolyLE.const 1 1).congr fun X ↦ by simp
  | u₀ :: u, a₀ :: a, v =>
    ((polyLE_eqEval u a v).const_mul (1 + a₀ + u₀)).congr fun X ↦ by
      rw [List.cons_append, eqEval_cons]

/-- A table's extension is affine in any one coordinate. -/
theorem polyLE_multilinearEval {t : List E} (u v : List E)
    (ht : t.length = 2 ^ (u.length + 1 + v.length)) :
    PolyLE 1 fun X ↦ multilinearEval t (u ++ X :: v) := by
  refine (PolyLE.sum (range (2 ^ (u.length + 1 + v.length))) fun i _ ↦
    (polyLE_eqEval u (boolPoint (u.length + 1 + v.length) i) v).const_mul
      (t.getD i 0)).congr fun X ↦ ?_
  rw [multilinearEval_eq_sum _ t _ ht (by simp; (clear * -; omega))]

/-- A product of polynomial functions, along a list. -/
theorem PolyLE.listProd {ι : Type} {d : ℕ} (F : ι → E → E) :
    ∀ l : List ι, (∀ i ∈ l, PolyLE d (F i)) → PolyLE (l.length * d) fun x ↦ (l.map (F · x)).prod
  | [], _ => (PolyLE.const _ 1).congr fun x ↦ by simp
  | i :: l, h =>
    ((PolyLE.mul (h i (by simp)) (PolyLE.listProd F l fun j hj ↦ h j (by simp [hj]))).mono
      (by rw [List.length_cons]; nlinarith)).congr fun x ↦ by simp

/-- Adjacent pairs multiplied: one level up a product tree. -/
def mulPairs : List E → List E
  | a :: b :: t => a * b :: mulPairs t
  | _ => []

/-- The layer `k` levels above the leaves `L`. -/
def up (k : ℕ) (L : List E) : List E := mulPairs^[k] L

theorem length_mulPairs : ∀ t : List E, (mulPairs t).length = t.length / 2
  | [] => rfl
  | [_] => by simp [mulPairs]
  | a :: b :: t => by
    simp only [mulPairs, List.length_cons, length_mulPairs t]
    omega

theorem getD_mulPairs : ∀ (t : List E) (j : ℕ), 2 * j + 1 < t.length →
    (mulPairs t).getD j 0 = t.getD (2 * j) 0 * t.getD (2 * j + 1) 0
  | [], _, h => by simp at h
  | [_], _, h => by simp at h
  | a :: b :: t, 0, _ => by simp [mulPairs]
  | a :: b :: t, j + 1, h => by
    simp only [mulPairs, List.getD_cons_succ, List.length_cons] at h ⊢
    rw [getD_mulPairs t j (by omega), show 2 * (j + 1) = 2 * j + 1 + 1 by ring]
    simp

/-- Multiplying adjacent pairs keeps the product of a list of even length. -/
theorem prod_mulPairs : ∀ t : List E, Even t.length → (mulPairs t).prod = t.prod
  | [], _ => rfl
  | [_], h => by simp at h
  | a :: b :: t, h => by
    have ht : Even t.length := by
      simpa [List.length_cons, Nat.even_add_one] using h
    simp only [mulPairs, List.prod_cons, prod_mulPairs t ht, mul_assoc]

theorem up_succ (k : ℕ) (L : List E) : up (k + 1) L = mulPairs (up k L) :=
  Function.iterate_succ_apply' _ _ _

theorem up_add (a b : ℕ) (L : List E) : up (a + b) L = up a (up b L) :=
  Function.iterate_add_apply _ _ _ _

theorem length_up : ∀ (k m : ℕ) (L : List E), L.length = 2 ^ (m + k) → (up k L).length = 2 ^ m
  | 0, m, L, h => by simpa [up] using h
  | k + 1, m, L, h => by
    rw [up_succ, length_mulPairs, length_up k (m + 1) L (by rw [h]; ring_nf), pow_succ,
      Nat.mul_div_cancel _ (by norm_num)]

/-- **A node of the tree** is the product of the leaves below it: entry `i` of the layer `k`
levels up is the product of the leaves `j + 2^k·i`. -/
theorem getD_up : ∀ (k m : ℕ) (L : List E), L.length = 2 ^ (m + k) → ∀ i, i < 2 ^ m →
    (up k L).getD i 0 = ((List.range (2 ^ k)).map fun j ↦ L.getD (j + 2 ^ k * i) 0).prod
  | 0, m, L, _, i, _ => by simp [up]
  | k + 1, m, L, h, i, hi => by
    have hl := length_up k (m + 1) L (by rw [h]; ring_nf)
    rw [up_succ, getD_mulPairs _ i (by rw [hl, pow_succ]; (clear * - hi; omega)),
      getD_up k (m + 1) L (by rw [h]; ring_nf) (2 * i) (by rw [pow_succ]; (clear * - hi; omega)),
      getD_up k (m + 1) L (by rw [h]; ring_nf) (2 * i + 1) (by rw [pow_succ]; (clear * - hi; omega)),
      pow_succ, mul_two, List.range_add, List.map_append, List.prod_append, List.map_map]
    congr 2
    · refine List.map_congr_left fun j _ ↦ ?_
      rw [show j + 2 ^ k * (2 * i) = j + (2 ^ k + 2 ^ k) * i by ring]
    · refine List.map_congr_left fun j _ ↦ ?_
      rw [Function.comp_apply, show j + 2 ^ k * (2 * i + 1) = 2 ^ k + j + (2 ^ k + 2 ^ k) * i by
        ring]

/-- The product of the layers is the product of the leaves. -/
theorem prod_up : ∀ (k m : ℕ) (L : List E), L.length = 2 ^ (m + k) → (up k L).prod = L.prod
  | 0, _, _, _ => rfl
  | k + 1, m, L, h => by
    have hl := length_up k (m + 1) L (by rw [h]; ring_nf)
    rw [up_succ, prod_mulPairs _ (by rw [hl, pow_succ]; exact ⟨2 ^ m, by ring⟩),
      prod_up k (m + 1) L (by rw [h]; ring_nf)]

/-- The root of a tree is the leaves' product. -/
theorem multilinearEval_up_root {D : ℕ} {L : List E} (h : L.length = 2 ^ D) :
    multilinearEval (up D L) [] = L.prod := by
  have hl := length_up D 0 L (by rw [h, zero_add])
  obtain ⟨a, ha⟩ : ∃ a, up D L = [a] := by
    match hu : up D L, hl with
    | [a], _ => exact ⟨a, rfl⟩
  rw [← prod_up D 0 L (by rw [h, zero_add]), ha]
  simp [multilinearEval]

end
end LeanVM.Protocol.EndToEnd.Complete
end
end

section
section
namespace LeanVM.Protocol.EndToEnd.Complete
open LeanVM.Prover (Script)
open LeanVM.Parameters LeanVM.Protocol.Compile LeanVM.Protocol.Verifier
open LeanVM.Protocol.Whir.Complete LeanVM.Protocol.EndToEnd Finset
section

/-- The children's products, batched in the Horner order of `polyEval`: the step's polynomial
`F(x)`. -/
def stepF (C₀ C₁ C₂ : List E) (step : ℕ) (c : E) (x : List E) : E :=
  polyEval [(child C₀ step x).prod, (child C₁ step x).prod, (child C₂ step x).prod] c

/-- The running claim of the step's sumcheck after the challenges `pre`:
`Σ_b eq(p_{≥|pre|}, b) · F(pre, b)`. -/
def stepClaim (C₀ C₁ C₂ : List E) (step : ℕ) (p : List E) (c : E) (pre : List E) : E :=
  ∑ b ∈ range (2 ^ (p.length - pre.length)),
    eqEval (p.drop pre.length) (boolPoint (p.length - pre.length) b) *
      stepF C₀ C₁ C₂ step c (pre ++ boolPoint (p.length - pre.length) b)

/-- The children's extension at `y` is the layer's extension at `y ++ x`. -/
theorem multilinearEval_child {C : List E} {step d : ℕ} (hC : C.length = 2 ^ (step + d))
    {x y : List E} (hx : x.length = d) (hy : y.length = step) :
    multilinearEval (child C step x) y = multilinearEval C (y ++ x) := by
  rw [multilinearEval_append hC hy hx, multilinearEval_eq_sum step _ y (by simp [child]) hy]
  refine sum_congr rfl fun j hj ↦ ?_
  simp [child, List.getD_eq_getElem?_getD, mem_range.mp hj]

/-- A child at a cube point is a node of the layer. -/
theorem child_boolPoint {C : List E} {step d : ℕ} (hC : C.length = 2 ^ (step + d)) {b : ℕ}
    (hb : b < 2 ^ d) :
    child C step (boolPoint d b) =
      (List.range (2 ^ step)).map fun j ↦ C.getD (j + 2 ^ step * b) 0 := by
  refine List.map_congr_left fun j hj ↦ ?_
  have hj' := List.mem_range.mp hj
  rw [← boolPoint_add step d j b hj', multilinearEval_boolPoint hC]
  rw [pow_add]
  exact add_mul_lt hj' hb

/-- **The start of the step.** The batched values of the layers at `p` are the sumcheck's
claim. -/
theorem stepClaim_nil {C₀ C₁ C₂ : List E} {step : ℕ} {p : List E}
    (h₀ : C₀.length = 2 ^ (step + p.length)) (h₁ : C₁.length = 2 ^ (step + p.length))
    (h₂ : C₂.length = 2 ^ (step + p.length)) (c : E) :
    polyEval [multilinearEval (up step C₀) p, multilinearEval (up step C₁) p,
      multilinearEval (up step C₂) p] c = stepClaim C₀ C₁ C₂ step p c [] := by
  have hT : ∀ C : List E, C.length = 2 ^ (step + p.length) →
      multilinearEval (up step C) p =
        ∑ b ∈ range (2 ^ p.length), (child C step (boolPoint p.length b)).prod *
          eqEval (boolPoint p.length b) p := fun C hC ↦ by
    have hl := length_up step p.length C (by rw [hC, add_comm])
    rw [multilinearEval_eq_sum p.length _ p hl rfl]
    refine sum_congr rfl fun b hb ↦ ?_
    rw [getD_up step p.length C (by rw [hC, add_comm]) b (mem_range.mp hb),
      child_boolPoint hC (mem_range.mp hb)]
  rw [hT C₀ h₀, hT C₁ h₁, hT C₂ h₂, polyEval_three, stepClaim]
  simp only [List.length_nil, Nat.sub_zero, List.drop_zero, List.nil_append, stepF,
    polyEval_three, sum_mul, ← sum_add_distrib]
  refine sum_congr rfl fun b _ ↦ ?_
  rw [eqEval_comm]
  ring

/-- **A round of the step.** The next claims at `0` and `1` split the claim as the equality-mode
round checks it, with the point's coordinate `p_k`. -/
theorem stepClaim_split (C₀ C₁ C₂ : List E) (step : ℕ) (p : List E) (c : E) (pre : List E)
    (hk : pre.length < p.length) :
    RoundSplit (some p[pre.length]) (stepClaim C₀ C₁ C₂ step p c pre)
      (stepClaim C₀ C₁ C₂ step p c (pre ++ [0])) (stepClaim C₀ C₁ C₂ step p c (pre ++ [1])) := by
  obtain ⟨m, hm⟩ : ∃ m, p.length - pre.length = m + 1 := ⟨p.length - pre.length - 1, by omega⟩
  have hm' : p.length - (pre.length + 1) = m := by omega
  simp only [RoundSplit, stepClaim, List.length_append, List.length_singleton, hm, hm']
  rw [pow_succ', sum_range_two_mul, List.drop_eq_getElem_cons hk, mul_sum, mul_sum,
    ← sum_add_distrib]
  refine sum_congr rfl fun j _ ↦ ?_
  rw [boolPoint_two_mul, boolPoint_two_mul_add_one, eqEval_cons, eqEval_cons,
    show pre ++ 0 :: boolPoint m j = pre ++ [0] ++ boolPoint m j by simp,
    show pre ++ 1 :: boolPoint m j = pre ++ [1] ++ boolPoint m j by simp]
  linear_combination (-(eqEval (p.drop (pre.length + 1)) (boolPoint m j) *
    stepF C₀ C₁ C₂ step c (pre ++ [1] ++ boolPoint m j))) * two_eq_zero_E

/-- **The degree of a round.** The next claim is a polynomial of degree `2^step` in the next
challenge. -/
theorem stepClaim_polyLE {C₀ C₁ C₂ : List E} {step : ℕ} {p : List E}
    (h₀ : C₀.length = 2 ^ (step + p.length)) (h₁ : C₁.length = 2 ^ (step + p.length))
    (h₂ : C₂.length = 2 ^ (step + p.length)) (c : E) (pre : List E)
    (hk : pre.length < p.length) :
    PolyLE (2 ^ step) fun X ↦ stepClaim C₀ C₁ C₂ step p c (pre ++ [X]) := by
  have hchild : ∀ C : List E, C.length = 2 ^ (step + p.length) → ∀ b : ℕ,
      PolyLE (2 ^ step) fun X ↦
        (child C step (pre ++ [X] ++ boolPoint (p.length - (pre.length + 1)) b)).prod := by
    intro C hC b
    have := PolyLE.listProd (d := 1) (fun j X ↦ multilinearEval C
      ((boolPoint step j ++ pre) ++ X :: boolPoint (p.length - (pre.length + 1)) b))
      (List.range (2 ^ step)) fun j _ ↦ polyLE_multilinearEval _ _ (by
        rw [hC]; simp only [List.length_append, length_boolPoint]; congr 1; (clear * - hk; omega))
    simp only [List.length_range, mul_one] at this
    refine this.congr fun X ↦ ?_
    simp [child]
  have hF : ∀ b, PolyLE (2 ^ step) fun X ↦
      stepF C₀ C₁ C₂ step c (pre ++ [X] ++ boolPoint (p.length - (pre.length + 1)) b) := by
    intro b
    refine (((hchild C₀ h₀ b).add ((hchild C₁ h₁ b).mul (PolyLE.const 0 c))).add
      ((hchild C₂ h₂ b).mul (PolyLE.const 0 (c ^ 2)))).congr fun X ↦ ?_
    simp only [stepF, polyEval_three]
  refine (PolyLE.sum (range (2 ^ (p.length - (pre.length + 1)))) fun b _ ↦
    (hF b).const_mul (eqEval (p.drop (pre.length + 1))
      (boolPoint (p.length - (pre.length + 1)) b))).congr fun X ↦ ?_
  simp only [stepClaim, List.length_append, List.length_singleton]

/-- **The end of the step.** With every coordinate bound, the claim is `F` at the challenges. -/
theorem stepClaim_self (C₀ C₁ C₂ : List E) (step : ℕ) (p : List E) (c : E) (x : List E)
    (hx : x.length = p.length) : stepClaim C₀ C₁ C₂ step p c x = stepF C₀ C₁ C₂ step c x := by
  simp [stepClaim, hx]


/-- `prodE` is the product. -/
theorem prodE_eq (l : List E) : prodE l = l.prod := by
  rw [prodE, foldl_mul_eq, one_mul]

end
end LeanVM.Protocol.EndToEnd.Complete
end
end

section
namespace LeanVM.Protocol.EndToEnd.Front
open LeanVM.Parameters LeanVM.Protocol.Verifier LeanVM.Protocol.Ring LeanVM.Protocol.KeccakGkr
open LeanVM.Semantics
section

/-- Word `n` of `q_keccak` on a stack of the layout: the stack's cell `n` past `QKECCAK`'s
offset (ported from leanVM `EndToEnd/Front/KeccakLayout.lean:31-32`). -/
def qkOf (layout : Verifier.Layout) (q : Column layout.stackLog) (n : ℕ) : K :=
  q.values.toArray.getD ((layout.placement qkeccak).index + n) 0

/-- Word `n` of the block of a stack at `off`. -/
def qkAt {μ : ℕ} (off : ℕ) (q : Column μ) (n : ℕ) : K := q.values.toArray.getD (off + n) 0

/-- `q_keccak`'s words on a stack of the layout are the block's at its placement. -/
theorem qkOf_eq_qkAt (layout : Verifier.Layout) (q : Column layout.stackLog) :
    qkOf layout q = qkAt (layout.placement qkeccak).index q := rfl

/-- **What ring switching needs of the layout**: `q_keccak` is placed on `h + 6` variables, at an
offset aligned to its size, inside the stack. -/
structure RingLayoutHyp (layout : Verifier.Layout) (h off : ℕ) : Prop where
  /-- `q_keccak`'s placement: `h + 6` variables at `off`. -/
  placement : layout.placement qkeccak = { variableCount := h + 6, index := off }
  /-- The offset is aligned to the block's size. -/
  aligned : 2 ^ (h + 6) ∣ off
  /-- The block lies inside the stack. -/
  fits : off + 2 ^ (h + 6) ≤ 2 ^ layout.stackLog

end
end LeanVM.Protocol.EndToEnd.Front
end

section
namespace LeanVM.Protocol.EndToEnd.Front
open LeanVM.Parameters LeanVM.Protocol.Verifier LeanVM.Protocol.Ring LeanVM.Protocol.KeccakGkr
open LeanVM.Semantics
section

/-- **An aligned placement's weight at a cube point**: the indicator of the block times the
equality weight of the offset inside it. -/
theorem eqAbove_mul_eqEval_boolPoint {v off μ x : ℕ} (hfit : off + 2 ^ v ≤ 2 ^ μ) (hx : x < 2 ^ μ)
    (p : List E) (hp : p.length = v) :
    ({ variableCount := v, index := off } : Placement).eqAbove (boolPoint μ x) *
        eqEval p ((boolPoint μ x).take v) =
      if x / 2 ^ v = off / 2 ^ v then eqAt p (x % 2 ^ v) else 0 := by
  have hv : v ≤ μ := by
    have : 2 ^ v ≤ 2 ^ μ := by omega
    exact (Nat.pow_le_pow_iff_right (by norm_num)).mp this
  have hpow : 2 ^ μ = 2 ^ v * 2 ^ (μ - v) := by rw [← pow_add, Nat.add_sub_cancel' hv]
  have hoff : off / 2 ^ v < 2 ^ (μ - v) :=
    Nat.div_lt_of_lt_mul (by rw [← hpow]; have := Nat.two_pow_pos v; omega)
  have hxv : x / 2 ^ v < 2 ^ (μ - v) := Nat.div_lt_of_lt_mul (by rw [← hpow]; exact hx)
  simp only [Placement.eqAbove, length_boolPoint, selectorPoint_eq_boolPoint,
    Nat.shiftRight_eq_div_pow, drop_boolPoint]
  rw [Complete.eqEval_boolPoint_boolPoint _ _ _ hoff hxv, take_boolPoint μ v x hv, ← hp,
    ← boolPoint_mod, eqEval_boolPoint_eqAt, hp]
  by_cases h : x / 2 ^ v = off / 2 ^ v
  · simp [h]
  · simp [h, Ne.symm h]

/-- **A sum over the stack weighted by an aligned placement** is the sum over the block. -/
theorem sum_placed {v off μ : ℕ} (hal : 2 ^ v ∣ off) (hfit : off + 2 ^ v ≤ 2 ^ μ) (p : List E)
    (hp : p.length = v) (q : Column μ) :
    ∑ x : Fin (2 ^ μ), ({ variableCount := v, index := off } : Placement).eqAbove (boolPoint μ x) *
        eqEval p ((boolPoint μ x).take v) * ofK (q.values.getD x 0) =
      ∑ n ∈ Finset.range (2 ^ v), eqAt p n * ofK (qkAt off q n) := by
  obtain ⟨t, rfl⟩ := hal
  have hpos := Nat.two_pow_pos v
  rw [Fin.sum_univ_eq_sum_range (fun x ↦ ({ variableCount := v, index := 2 ^ v * t } :
      Placement).eqAbove
    (boolPoint μ x) * eqEval p ((boolPoint μ x).take v) * ofK (q.values.getD x 0))]
  have hsub : Finset.Ico (2 ^ v * t) (2 ^ v * t + 2 ^ v) ⊆ Finset.range (2 ^ μ) := fun x hx ↦ by
    simp only [Finset.mem_Ico] at hx
    exact Finset.mem_range.mpr (by omega)
  rw [← Finset.sum_subset hsub fun x hx hn ↦ ?_, Finset.sum_Ico_eq_sum_range,
    Nat.add_sub_cancel_left]
  · refine Finset.sum_congr rfl fun n hn ↦ ?_
    have hn' := Finset.mem_range.mp hn
    rw [eqAbove_mul_eqEval_boolPoint hfit (by omega) p hp,
      Nat.mul_add_div hpos, Nat.div_eq_of_lt hn', add_zero, Nat.mul_div_cancel_left _ hpos]
    simp only [↓reduceIte]
    rw [Nat.mul_add_mod, Nat.mod_eq_of_lt hn', qkAt]
    rfl
  · have hx := Finset.mem_range.mp hx
    rw [eqAbove_mul_eqEval_boolPoint hfit hx p hp, Nat.mul_div_cancel_left _ hpos]
    suffices hne : x / 2 ^ v ≠ t by simp [hne]
    intro he
    refine hn (Finset.mem_Ico.mpr ⟨?_, ?_⟩)
    · rw [← he]; exact Nat.mul_div_le x _
    · have := Nat.lt_mul_div_succ x hpos
      rw [he, mul_add, mul_one] at this
      exact this

/-- **The ring claim paired with a stack** (any stack size `μ` the block fits in): with
`q_keccak` placed on `h + 6` variables at an aligned `off`, the pairing of the program's ring
claim is `Σ_i x^i Φ(ẑ_i(point))`. -/
theorem pair_ringClaim {layout : Verifier.Layout} {h off μ : ℕ}
    (hpl : layout.placement qkeccak = { variableCount := h + 6, index := off }) (hal : 2 ^ (h +
        6) ∣ off)
    (hfit : off + 2 ^ (h + 6) ≤ 2 ^ μ) (q : Column μ) {pt ch : List E}
    (hpt : pt.length = h + 6) (hch : ch.length = 6) (target : E) :
    ∑ x : Fin (2 ^ μ), (ringSwitchClaim layout target
        fun rPrime ↦ ringWeight pt rPrime (ringCoefficients ch)).1 (boolPoint μ x) *
          ofK (q.values.getD x 0) =
      ∑ i : Fin 64, ringW i * phiMap (sliceExt h (qkAt off q) pt i) ch := by
  simp only [ringSwitchClaim, hpl, ringWeight_eq_sum, length_ringCoefficients, Finset.mul_sum,
    Finset.sum_mul]
  rw [Finset.sum_comm]
  have e : ∀ k ∈ Finset.range 64,
      ∑ x : Fin (2 ^ μ), ({ variableCount := h + 6, index := off } : Placement).eqAbove
          (boolPoint μ x) *
          ((ringCoefficients ch).getD k 0 *
            eqEval (pt.map (· ^ 2 ^ k)) ((boolPoint μ x).take (h + 6))) *
          ofK (q.values.getD x 0) =
        (ringCoefficients ch).getD k 0 *
          ∑ i : Fin 64, ringW i * sliceExt h (qkAt off q) pt i ^ 2 ^ k := fun k _ ↦ by
    rw [← colExt_frob, colExt, ← sum_placed hal hfit _ (by rw [List.length_map, hpt]) q,
      Finset.mul_sum]
    exact Finset.sum_congr rfl fun x _ ↦ by ring
  rw [Finset.sum_congr rfl e]
  simp only [phiMap_eq_sum hch, Finset.mul_sum]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun i _ ↦ Finset.sum_congr rfl fun k _ ↦ by ring

end
end LeanVM.Protocol.EndToEnd.Front
end

section
namespace LeanVM.Protocol.EndToEnd.Front
open LeanVM.Parameters LeanVM.Protocol.Verifier LeanVM.Protocol.Ring LeanVM.Protocol.KeccakGkr
open LeanVM.Semantics
section

/-- **The ring claim holds exactly when the errors' twisted sum vanishes**: for the program's
target and weight, the claim on a stack holds iff `Σ_i x^i Φ(s_i - ẑ_i(point)) = 0`. -/
theorem ringClaim_holds_iff {layout : Verifier.Layout} {h off μ : ℕ}
    (hpl : layout.placement qkeccak = { variableCount := h + 6, index := off }) (hal : 2 ^ (h +
        6) ∣ off)
    (hfit : off + 2 ^ (h + 6) ≤ 2 ^ μ) (q : Column μ) {pt sv ch : List E}
    (hpt : pt.length = h + 6) (hsv : sv.length = 64) (hch : ch.length = 6) :
    StackClaim.Holds μ (ringSwitchClaim layout (polyEval (sv.map (phiMap · ch)) gen)
        fun rPrime ↦ ringWeight pt rPrime (ringCoefficients ch)) q ↔
      ∑ i : Fin 64, ringW i * phiMap (ringErr h (qkAt off q) pt sv i) ch = 0 := by
  unfold StackClaim.Holds
  rw [pair_ringClaim hpl hal hfit q hpt hch, ringTarget_eq_sum sv ch hsv]
  simp only [ringErr, phiMap_sub, mul_sub, Finset.sum_sub_distrib]
  rw [sub_eq_zero, eq_comm]
  exact Iff.rfl

end
end LeanVM.Protocol.EndToEnd.Front
end

-- ===== from `LvmTypedAcc` =====

section
set_option autoImplicit false
namespace Lvm.Typed
open Lvm.Loop LeanVM.Parameters LeanVM.Protocol LeanVM.Protocol.Compile LeanVM.Protocol.KeccakGkr
open Lvm.Acc Polynomial Finset
open scoped ENNReal

theorem toExt3_phiSum (es : List Ent) (pt : List E) :
    FE.toExt3 (phiSum es (pt.map FE.ofExt3)) = (es.map fun e ↦ FE.toExt3 e.c * eqAt pt e.idx).sum := by
  induction es with
  | nil => simp [phiSum]
  | cons e es ih =>
    simp only [phiSum, List.foldr_cons] at ih ⊢
    rw [FE.toExt3_add, FE.toExt3_mul, toExt3_eqW', ih, List.map_cons, List.sum_cons]

/-- **`Φ_Q` over `E` is the sparse multilinear sum** of the matrices' entries. -/
theorem phiQ_eq_sum (Q : Program) (lay : Lay) (pt : List E) :
    PhiQ Q lay pt = ((ents Q lay).map fun e ↦ FE.toExt3 e.c * eqAt pt e.idx).sum :=
  toExt3_phiSum _ _

end Lvm.Typed
end

section
set_option autoImplicit false
namespace Lvm.Typed
open Lvm.Loop LeanVM.Parameters LeanVM.Protocol LeanVM.Protocol.Compile LeanVM.Protocol.KeccakGkr
open Lvm.Acc Polynomial Finset
open scoped ENNReal

/-- The fixed claims' errors: `δ_o = v_o − M̃_o(r_x, r_y)` for `o < 4`. -/
def deltaQ (Q : Program) (lay : Lay) (vs rxy : List E) (o : ℕ) : E :=
  if o < 4 then vs.getD o 0 - matMle Q lay o rxy else 0

end Lvm.Typed
end

section
set_option autoImplicit false
namespace Lvm.Typed
open Lvm.Loop LeanVM.Parameters LeanVM.Protocol LeanVM.Protocol.Compile LeanVM.Protocol.KeccakGkr
open Lvm.Acc Polynomial Finset
open scoped ENNReal

/-- **Matrix `o`'s extension over `E`** is the sum over its entries (`rxy = r_x ++ r_y`). -/
theorem matMle_eq_sum (Q : Program) (lay : Lay) (o : ℕ) (rxy : List E) :
    matMle Q lay o rxy = (((ents Q lay).filter fun e ↦ e.o == o).map fun e ↦
      FE.toExt3 e.c * eqAt rxy (e.x + 2 ^ xVars * e.y)).sum := by
  unfold matMle matMleF
  rw [toExt3_foldr_ents]
  exact congrArg List.sum (List.map_congr_left fun e _ ↦ by rw [FE.toExt3_mul, toExt3_eqW'])

/-- A selector-weighted sum of the per-matrix sums is the weighted sum over all entries (every `o < 4`). -/
theorem sum_sel_filter (g : ℕ → E) (f : Ent → E) :
    ∀ l : List Ent, (∀ e ∈ l, e.o < 4) →
      ∑ w ∈ range (2 ^ 2), g w * ((l.filter fun e ↦ e.o == w).map f).sum = (l.map fun e ↦ g e.o * f e).sum
  | [], _ => by simp
  | e :: l, hl => by
    have ih := sum_sel_filter g f l fun e' he' ↦ hl e' (List.mem_cons_of_mem _ he')
    have he : e.o < 2 ^ 2 := hl e (List.mem_cons_self ..)
    rw [List.map_cons, List.sum_cons, ← ih]
    rw [Finset.sum_congr rfl fun w _ ↦ show g w * ((((e :: l).filter fun e ↦ e.o == w)).map f).sum =
        (if e.o = w then g e.o * f e else 0) + g w * ((l.filter fun e ↦ e.o == w).map f).sum by
      by_cases h : e.o = w
      · subst h; simp [mul_add]
      · simp [h]]
    rw [Finset.sum_add_distrib, Finset.sum_ite_eq, ite_eq_left (Finset.mem_range.mpr he)]

/-- **The selector split** (L-B): at `κ ++ r_x ++ r_y`, `y_own − Φ_Q` is the selector extension of the
matrices' errors. Needs every entry's `o < 4` (`okB`'s `auxOk`; `instEnts` by construction). -/
theorem phiQ_fold (Q : Program) (lay : Lay) (hlay : lay.Ok Q) (rxy vs : List E) (hr : rxy.length = xVars + yVars)
    (hvs : vs.length = 4) (κ : List E) (hκ : κ.length = 2) :
    yOwnQ vs κ - PhiQ Q lay (bOfQ rxy κ) = ∑ w ∈ range (2 ^ 2), eqAt κ w * deltaQ Q lay vs rxy w := by
  have hfit := ents_fit Q lay hlay
  have hk4 : (Verifier.eqKernel κ).length = 2 ^ 2 := by rw [eqKernel_length, hκ]
  have hown : yOwnQ vs κ = ∑ w ∈ range (2 ^ 2), eqAt κ w * vs.getD w 0 := by
    unfold yOwnQ
    rw [LeanVM.Protocol.KeccakGkr.dot_eq _ _ (by rw [hk4, hvs]; rfl), hk4]
    refine Finset.sum_congr rfl fun w hw ↦ ?_
    rw [eqKernel_getD, hκ, ite_eq_left (Finset.mem_range.mp hw)]
  have hphi : PhiQ Q lay (bOfQ rxy κ) = ∑ w ∈ range (2 ^ 2), eqAt κ w * matMle Q lay w rxy := by
    simp only [matMle_eq_sum]
    rw [sum_sel_filter (eqAt κ) _ _ fun e he ↦ (hfit e he).1, phiQ_eq_sum]
    refine congrArg List.sum (List.map_congr_left fun e he ↦ ?_)
    have ho := (hfit e he).1
    unfold bOfQ
    rw [eqAt_append, hκ, eqAt_mod κ, hκ, Ent.idx,
      show (e.o + 4 * (e.x + 2 ^ xVars * e.y)) % 2 ^ 2 = e.o by (clear * - ho; omega),
      show (e.o + 4 * (e.x + 2 ^ xVars * e.y)) / 2 ^ 2 = e.x + 2 ^ xVars * e.y by (clear * - ho; omega)]
    ring
  rw [hown, hphi, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun w hw ↦ ?_
  rw [deltaQ, ite_eq_left (by simpa using hw), mul_sub]

/-- **`AccHyp` at `Φ_Q`** (B-DES §1.2 step 3: `LvmAccSpec` unchanged): `dk = 2` (the selector), `D = 43`. -/
theorem accHypQ (Q : Program) (lay : Lay) (hlay : lay.Ok Q) (a rxy vs : List E) (ha : a.length = phiVars)
    (hr : rxy.length = xVars + yVars) (hvs : vs.length = 4) :
    AccHyp 2 phiVars a (yOwnQ vs) (bOfQ rxy) (PhiQ Q lay) (deltaQ Q lay vs rxy) where
  line_deg κ _ := by
    obtain ⟨g, hg, hgv⟩ := lineDeg_sparse ((ents Q lay).map fun e ↦ (e.idx, FE.toExt3 e.c)) a (bOfQ rxy κ)
    refine ⟨g, ha ▸ hg, fun t ↦ ?_⟩
    rw [hgv, phiQ_eq_sum, List.map_map]
    exact congrArg List.sum (List.map_congr_left fun e _ ↦ rfl)
  at0 κ hκ := line_zero _ _ (by simp [bOfQ, ha, hr, hκ, phiVars]; (clear * -; omega))
  at1 κ hκ := line_one _ _ (by simp [bOfQ, ha, hr, hκ, phiVars]; (clear * -; omega))
  fold κ hκ := phiQ_fold Q lay hlay rxy vs hr hvs κ hκ

/-- **`accSpecG` at `Φ_Q`**: A23's phase specification applies unchanged (escape `1/|E|` per `κ_j`, `43/|E|` at
`t`). -/
noncomputable def accSpecQ (Q : Program) (lay : Lay) (hlay : lay.Ok Q) {ok : Bool} {yIn : E}
    (a rxy vs : List E) (ha : a.length = phiVars) (hr : rxy.length = xVars + yVars) (hvs : vs.length = 4)
    (M : List Ev → Prop)
    (hM : ∀ h₀ l, (accProgQ Q lay ok yIn a rxy vs).Reach h₀ l → M h₀ → M (h₀ ++ l))
    {εmax T : ℝ≥0∞} (hD : errE phiVars ≤ εmax) (hT : T ≤ εmax) :
    Spec (accProgQ Q lay ok yIn a rxy vs)
      (fun h ↦ ¬ AccGood 2 ok yIn a (PhiQ Q lay) (deltaQ Q lay vs rxy) ∨ M h)
      (fun _ h ↦ M h) εmax (max (2 * errE 1) T) T :=
  accSpecG (accHypQ Q lay hlay a rxy vs ha hr hvs) M hM hD hT

end Lvm.Typed
end

-- ===== from `LvmTypedSpecP` =====

section
set_option autoImplicit false
namespace Lvm.Typed
open Lvm.Loop LeanVM.Parameters LeanVM.Protocol LeanVM.Protocol.Compile LeanVM.Protocol.Verifier
open LeanVM.Protocol.EndToEnd.Front LeanVM.Protocol.EndToEnd.Complete LeanVM.Protocol.KeccakGkr
open Polynomial Finset
open scoped ENNReal NNReal

/-- **`a + γb + γ²c` against a different triple agrees at `2/|E|` of the `γ`** (Schwartz–Zippel). -/
theorem quadT_escape {a b c a' b' c' : E} (hne : ¬ (a = a' ∧ b = b' ∧ c = c')) :
    avgE (fun g ↦ indE (a + g * b + g * g * c = a' + g * b' + g * g * c')) ≤ errE 2 := by
  have hp : ∀ (u v w : E), (C u + C v * X + C w * X ^ 2 : E[X]).natDegree ≤ 2 := fun u v w ↦ by
    refine (natDegree_add_le _ _).trans (max_le ((natDegree_add_le _ _).trans (max_le (by simp) ?_)) ?_)
    · exact (natDegree_C_mul_le _ _).trans (by simp)
    · exact (natDegree_C_mul_le _ _).trans (by simp)
  have hne' : (C a + C b * X + C c * X ^ 2 : E[X]) ≠ C a' + C b' * X + C c' * X ^ 2 := by
    intro h
    refine hne ⟨?_, ?_, ?_⟩
    · have := congrArg (fun p : E[X] ↦ p.coeff 0) h
      simpa using this
    · have := congrArg (fun p : E[X] ↦ p.coeff 1) h
      simpa [coeff_X, coeff_X_pow] using this
    · have := congrArg (fun p : E[X] ↦ p.coeff 2) h
      simpa [coeff_X, coeff_X_pow] using this
  refine (avgE_mono fun g ↦ indE_mono fun hg ↦ ?_).trans (sz_escape hne' (hp a b c) (hp a' b' c'))
  simp only [eval_add, eval_mul, eval_C, eval_X, eval_pow]
  linear_combination hg

end Lvm.Typed
end

section
set_option autoImplicit false
namespace Lvm.Typed
open Lvm.Loop LeanVM.Parameters LeanVM.Protocol LeanVM.Protocol.Compile LeanVM.Protocol.Verifier
open LeanVM.Protocol.EndToEnd.Front LeanVM.Protocol.EndToEnd.Complete LeanVM.Protocol.KeccakGkr
open Polynomial Finset
open scoped ENNReal NNReal

/-- `(M_o z)(x)` over `E` is its entries' sum. -/
theorem matE_eq (Q : Program) (lay : Lay) (z : ℕ → FK) (o x : ℕ) :
    matE Q lay z o x = (((ents Q lay).filter fun e ↦ e.o == o && e.x == x).map fun e ↦
      FE.toExt3 e.c * zwE z e.y).sum := by
  unfold matE matZ
  rw [toExt3_foldr_ents]
  exact congrArg List.sum (List.map_congr_left fun e _ ↦ by rw [FE.toExt3_mul]; rfl)

end Lvm.Typed
end

section
set_option autoImplicit false
namespace Lvm.Typed
open Lvm.Loop LeanVM.Parameters LeanVM.Protocol LeanVM.Protocol.Compile LeanVM.Protocol.Verifier
open LeanVM.Protocol.EndToEnd.Front LeanVM.Protocol.EndToEnd.Complete LeanVM.Protocol.KeccakGkr
open Polynomial Finset
open scoped ENNReal NNReal

/-- A matrix's slot extension at `r` is its entries' sum (a checked layout). -/
theorem mleZ_matE (Q : Program) (lay : Lay) (hlay : lay.Ok Q) (z : ℕ → FK) (o : ℕ) (r : List E) :
    mleZ xVars (matE Q lay z o) r = (((ents Q lay).filter fun e ↦ e.o == o).map fun e ↦
      eqAt r e.x * (FE.toExt3 e.c * zwE z e.y)).sum := by
  unfold mleZ
  simp only [matE_eq]
  exact mle_filter xVars o r _ _ fun e he ↦ (ents_fit Q lay hlay e he).2.1

end Lvm.Typed
end

section
set_option autoImplicit false
namespace Lvm.Typed
open Lvm.Loop LeanVM.Parameters LeanVM.Protocol LeanVM.Protocol.Compile LeanVM.Protocol.Verifier
open LeanVM.Protocol.EndToEnd.Front LeanVM.Protocol.EndToEnd.Complete LeanVM.Protocol.KeccakGkr
open Polynomial Finset
open scoped ENNReal NNReal

/-- The weights of the four matrices on `range 4`. -/
theorem sum_wG (γ : E) (S : ℕ → E) : ∑ w ∈ range (2 ^ 2), wG γ w * S w = S 0 + γ * S 1 + γ * γ * (S 2 + S 3) := by
  simp [Finset.sum_range_succ, wG]
  ring

/-- **The wiring sumcheck's claim**: before any challenge, the family is `a + γ b + γ² c` at the true slot
extensions (a checked layout: the entries' slots and words on the cube). -/
theorem wire_nil (Q : Program) (lay : Lay) (hlay : lay.Ok Q) (z : ℕ → FK) (γ : E) (rx : List E) :
    tCubeSum yVars (wireGT Q lay z γ rx) [] =
      mleZ xVars (matE Q lay z 0) rx + γ * mleZ xVars (matE Q lay z 1) rx +
        γ * γ * mleZ xVars (fun x ↦ matE Q lay z 2 x + matE Q lay z 3 x) rx := by
  have hfit := ents_fit Q lay hlay
  have hsplit : mleZ xVars (fun x ↦ matE Q lay z 2 x + matE Q lay z 3 x) rx =
      mleZ xVars (matE Q lay z 2) rx + mleZ xVars (matE Q lay z 3) rx := by
    simp only [mleZ, mul_add, Finset.sum_add_distrib]
  rw [hsplit]
  have key := sum_wG γ fun w ↦ mleZ xVars (matE Q lay z w) rx
  rw [← key]
  simp only [mleZ_matE Q lay hlay]
  rw [sum_sel_filter (wG γ) _ _ fun e he ↦ (hfit e he).1, tCubeSum_nil]
  unfold wireGT wireM
  have hz : ∀ u < 2 ^ yVars, mleZ yVars (zwE z) (bitsE u yVars) = zwE z u := fun u hu ↦ by
    unfold mleZ; exact sum_eqAt_bitsE hu _
  rw [Finset.sum_congr rfl fun u hu ↦ by rw [hz u (Finset.mem_range.mp hu), ← List.sum_map_mul_right],
    sum_list_swap]
  refine congrArg List.sum (List.map_congr_left fun e he ↦ ?_)
  have hy := (hfit e he).2.2
  rw [Finset.sum_congr rfl fun u hu ↦ by
    rw [eqAt_bitsE_lt (Finset.mem_range.mp hu) hy]]
  simp only [mul_ite, mul_one, mul_zero, ite_mul, zero_mul]
  rw [Finset.sum_ite_eq (range (2 ^ yVars)) e.y, ite_eq_left (Finset.mem_range.mpr hy)]
  ring

/-- **The wiring's final matrix weight** is the four matrices' values batched by `γ` (`|r_x| = 20`). -/
theorem wireM_full (Q : Program) (lay : Lay) (hlay : lay.Ok Q) (γ : E) (rx ry : List E)
    (hrx : rx.length = xVars) :
    wireM Q lay γ rx ry = matMle Q lay 0 (rx ++ ry) + γ * matMle Q lay 1 (rx ++ ry) +
      γ * γ * (matMle Q lay 2 (rx ++ ry) + matMle Q lay 3 (rx ++ ry)) := by
  have hfit := ents_fit Q lay hlay
  rw [← sum_wG γ fun w ↦ matMle Q lay w (rx ++ ry)]
  simp only [matMle_eq_sum]
  rw [sum_sel_filter (wG γ) _ _ fun e he ↦ (hfit e he).1]
  unfold wireM
  refine congrArg List.sum (List.map_congr_left fun e he ↦ ?_)
  have hx := (hfit e he).2.1
  rw [eqAt_append, hrx, eqAt_mod rx (e.x + 2 ^ xVars * e.y), hrx,
    show (e.x + 2 ^ xVars * e.y) % 2 ^ xVars = e.x by rw [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hx],
    show (e.x + 2 ^ xVars * e.y) / 2 ^ xVars = e.y by
      rw [Nat.add_mul_div_left _ _ (by positivity), Nat.div_eq_of_lt hx, zero_add]]
  ring

end Lvm.Typed
end

section
set_option autoImplicit false
namespace Lvm.Typed
open Lvm.Loop LeanVM.Parameters LeanVM.Protocol LeanVM.Protocol.Compile LeanVM.Protocol.Verifier
open LeanVM.Protocol.EndToEnd.Front LeanVM.Protocol.EndToEnd.Complete LeanVM.Protocol.KeccakGkr
open Polynomial Finset
open scoped ENNReal NNReal

/-- **The wiring relation is the slot relation on the cube** (a checked layout: no entry past `2^20`). -/
theorem wiringRel_iff (Q : Program) (lay : Lay) (hlay : lay.Ok Q) (z : ℕ → FK) :
    WiringRel Q lay z ↔ ∀ x < 2 ^ xVars, relE Q lay z x = 0 := by
  have hfit := ents_fit Q lay hlay
  have hrel : ∀ x, relE Q lay z x = FE.toExt3 (matA Q lay z x * matB Q lay z x + matD Q lay z x +
      matW Q lay z x) := fun x ↦ by
    simp only [relE, matE, FE.toExt3_add, FE.toExt3_mul]; ring
  constructor
  · intro h x _
    rw [hrel, h x, FE.toExt3_zero]
  · intro h x
    by_cases hx : x < 2 ^ xVars
    · have := h x hx
      rw [hrel, ← FE.toExt3_zero] at this
      exact FE.toExt3_injective this
    · have h0 : ∀ o, matZ Q lay o z x = 0 := fun o ↦ by
        unfold matZ
        rw [List.filter_eq_nil_iff.mpr fun e he ↦ by
          have := (hfit e he).2.1
          simp only [Bool.and_eq_true, beq_iff_eq, not_and]
          intro _ hex; (clear * - hx this hex; omega)]
        rfl
      simp only [matA, matB, matD, matW, h0, mul_zero, add_zero]

end Lvm.Typed
end

section
set_option autoImplicit false
namespace Lvm.Typed
open Lvm.Loop LeanVM.Parameters LeanVM.Protocol LeanVM.Protocol.Compile LeanVM.Protocol.Verifier
open LeanVM.Protocol.EndToEnd.Front LeanVM.Protocol.EndToEnd.Complete LeanVM.Protocol.KeccakGkr
open Polynomial Finset
open scoped ENNReal NNReal

theorem polyLE_wireM (Q : Program) (lay : Lay) (γ : E) (rx pre post : List E) :
    PolyLE 1 fun x ↦ wireM Q lay γ rx (pre ++ x :: post) :=
  polyLE_listSum 1 _ _ fun e _ ↦ PolyLE.const_mul (polyLE_eqAt pre post e.y) _

theorem polyLE_wireG (Q : Program) (lay : Lay) (z : ℕ → FK) (γ : E) (rx pre post : List E) :
    PolyLE 2 fun x ↦ wireGT Q lay z γ rx (pre ++ x :: post) :=
  PolyLE.mul (polyLE_wireM Q lay γ rx pre post) (polyLE_mleZ _ _ pre post)

end Lvm.Typed
end

-- ===== from `LvmTypedSpec` =====

section
set_option autoImplicit false
namespace Lvm.Typed
open Lvm.Loop LeanVM.Parameters LeanVM.Protocol LeanVM.Protocol.Compile LeanVM.Protocol.Verifier
open LeanVM.Protocol.Compile.VerifierProgram LeanVM.Protocol.EndToEnd LeanVM.Protocol.EndToEnd.Front
open LeanVM.Protocol.KeccakGkr LeanVM.Protocol.Whir.Sound
open LeanVM.Protocol.EndToEnd.Sound (RetOK)
open Lvm.M3 (Tab inst stackOf comCell vTables vLayout busResV lvmBusTableProg lbusTableCheckProg NoCG KeysOk AllSc
  LayOk FixOk lay26
  cg_ret cg_sample cg_readScalar cg_require cg_readScalars cg_sampleChallenges cg_sumcheck cg_lvmBusProg
  cg_tablePhaseClaims)
open Lvm.ASM (OpenClaims RootShape candPairs Pair GoodRel MidSpecR MidShape ExtJ kcertSJ GkS BndS KcS KgRet
  LkSJ εS midSpecOfRel retOK_kgProgS cg_kgProgS schemeS PSWith)
open Lvm.VEq (kgProgS hdX pubX assembleS KgOut tableClaimsE BClaim VStackClaim)
open Lvm.Shape (Good₂ view vp imgC imgC_append imgC_ncard_le doomed_imgC onStackZs specKgS₂ openPostR_congr)
open scoped ENNReal NNReal

/-- **The typed phases commit nothing and ask no proof of work.** -/
theorem cg_typedProg (Ti : TInst) (pub : Lvm.Pub) : NoCG (typedProg Ti pub) := by
  unfold typedProg zeroProg wireProg relayProg miniBusProg accProgQ lbusTableCheckProg
  refine Lvm.M3.NoCG.bind (Lvm.M3.NoCG.bind (cg_sampleChallenges _) fun _ ↦ Lvm.M3.NoCG.bind (cg_sumcheck _ _ _)
    fun _ ↦ Lvm.M3.NoCG.bind (cg_readScalars _) fun _ ↦ Lvm.M3.NoCG.bind (cg_require _) fun _ ↦ cg_ret _)
    fun _ ↦ ?_
  refine Lvm.M3.NoCG.bind (Lvm.M3.NoCG.bind cg_sample fun _ ↦ Lvm.M3.NoCG.bind (cg_sumcheck _ _ _) fun _ ↦
    Lvm.M3.NoCG.bind (cg_readScalars _) fun _ ↦ Lvm.M3.NoCG.bind (cg_readScalars _) fun _ ↦
      Lvm.M3.NoCG.bind (cg_require _) fun _ ↦ cg_ret _) fun _ ↦ ?_
  refine Lvm.M3.NoCG.bind (Lvm.M3.NoCG.bind (cg_sumcheck _ _ _) fun _ ↦ Lvm.M3.NoCG.bind cg_readScalar fun _ ↦
    Lvm.M3.NoCG.bind (cg_require _) fun _ ↦ cg_ret _) fun _ ↦ ?_
  exact Lvm.M3.NoCG.bind (Lvm.Acc.cg_accProg _ _ _ _ _ _ _ _) fun _ ↦
    Lvm.M3.NoCG.bind (Lvm.M3.NoCG.bind (Lvm.M3.NoCG.bind (cg_lvmBusProg _) fun _ ↦ cg_tablePhaseClaims _ _ _)
      fun _ ↦ Lvm.M3.NoCG.bind (cg_require _) fun _ ↦ cg_ret _) fun _ ↦ cg_ret _

end Lvm.Typed
end

section
set_option autoImplicit false
namespace Lvm.Typed
open Lvm.Loop LeanVM.Parameters LeanVM.Protocol LeanVM.Protocol.Compile LeanVM.Protocol.Verifier
open LeanVM.Protocol.Compile.VerifierProgram LeanVM.Protocol.EndToEnd LeanVM.Protocol.EndToEnd.Front
open LeanVM.Protocol.KeccakGkr LeanVM.Protocol.Whir.Sound
open LeanVM.Protocol.EndToEnd.Sound (RetOK)
open Lvm.M3 (Tab inst stackOf comCell vTables vLayout busResV lvmBusTableProg lbusTableCheckProg NoCG KeysOk AllSc
  LayOk FixOk lay26
  cg_ret cg_sample cg_readScalar cg_require cg_readScalars cg_sampleChallenges cg_sumcheck cg_lvmBusProg
  cg_tablePhaseClaims)
open Lvm.ASM (OpenClaims RootShape candPairs Pair GoodRel MidSpecR MidShape ExtJ kcertSJ GkS BndS KcS KgRet
  LkSJ εS midSpecOfRel retOK_kgProgS cg_kgProgS schemeS PSWith)
open Lvm.VEq (kgProgS hdX pubX assembleS KgOut tableClaimsE BClaim VStackClaim)
open Lvm.Shape (Good₂ view vp imgC imgC_append imgC_ncard_le doomed_imgC onStackZs specKgS₂ openPostR_congr)
open scoped ENNReal NNReal

/-- The typed phases' program, unfolded. -/
theorem typedProg_eq (Ti : TInst) (pub : Lvm.Pub) : typedProg Ti pub =
    zeroProg.bind fun z ↦ (wireProg Ti pub z.2).bind fun w ↦ (relayProg Ti w.1 (w.2.2.getD 1 0)).bind fun r ↦
      (accProgQ Ti.Q Ti.lay true (FE.toExt3 pub.accIn.y) (pub.accIn.pt.map FE.toExt3) (z.1 ++ w.1) w.2.1).bind
        fun _ ↦ (miniBusProg Ti).bind fun cl ↦ VerifierProgram.ret (typedClaims Ti w.1 w.2.2 r.1 r.2 cl) := by
  rw [typedProg]

end Lvm.Typed
end

section
set_option autoImplicit false
namespace Lvm.Typed
open Lvm.Loop LeanVM.Parameters LeanVM.Protocol LeanVM.Protocol.Compile LeanVM.Protocol.Verifier
open LeanVM.Protocol.Compile.VerifierProgram LeanVM.Protocol.EndToEnd LeanVM.Protocol.EndToEnd.Front
open LeanVM.Protocol.KeccakGkr LeanVM.Protocol.Whir.Sound
open LeanVM.Protocol.EndToEnd.Sound (RetOK)
open Lvm.M3 (Tab inst stackOf comCell vTables vLayout busResV lvmBusTableProg lbusTableCheckProg NoCG KeysOk AllSc
  LayOk FixOk lay26
  cg_ret cg_sample cg_readScalar cg_require cg_readScalars cg_sampleChallenges cg_sumcheck cg_lvmBusProg
  cg_tablePhaseClaims)
open Lvm.ASM (OpenClaims RootShape candPairs Pair GoodRel MidSpecR MidShape ExtJ kcertSJ GkS BndS KcS KgRet
  LkSJ εS midSpecOfRel retOK_kgProgS cg_kgProgS schemeS PSWith)
open Lvm.VEq (kgProgS hdX pubX assembleS KgOut tableClaimsE BClaim VStackClaim)
open Lvm.Shape (Good₂ view vp imgC imgC_append imgC_ncard_le doomed_imgC onStackZs specKgS₂ openPostR_congr)
open scoped ENNReal NNReal
section Phases
variable (Ti : TInst) (L : Lvm.M3.Lay) (pub : Lvm.Pub) (hτL : ∀ t ∈ Ti.mbT, t.τ ≤ L.μ)
  (R : Column L.nuMain × Column L.nuRec → Prop)

/-- The four matrix values are the matrices' extensions at `r_x ++ r_y`. -/
def VsTrue (rxy vs : List E) : Prop := ∀ o < 4, vs.getD o 0 = matMle Ti.Q Ti.lay o rxy

end Phases
end Lvm.Typed
end

section
set_option autoImplicit false
namespace Lvm.Typed
open Lvm.Loop LeanVM.Parameters LeanVM.Protocol LeanVM.Protocol.Compile LeanVM.Protocol.Verifier
open LeanVM.Protocol.Compile.VerifierProgram LeanVM.Protocol.EndToEnd LeanVM.Protocol.EndToEnd.Front
open LeanVM.Protocol.KeccakGkr LeanVM.Protocol.Whir.Sound
open LeanVM.Protocol.EndToEnd.Sound (RetOK)
open Lvm.M3 (Tab inst stackOf comCell vTables vLayout busResV lvmBusTableProg lbusTableCheckProg NoCG KeysOk AllSc
  LayOk FixOk lay26
  cg_ret cg_sample cg_readScalar cg_require cg_readScalars cg_sampleChallenges cg_sumcheck cg_lvmBusProg
  cg_tablePhaseClaims)
open Lvm.ASM (OpenClaims RootShape candPairs Pair GoodRel MidSpecR MidShape ExtJ kcertSJ GkS BndS KcS KgRet
  LkSJ εS midSpecOfRel retOK_kgProgS cg_kgProgS schemeS PSWith)
open Lvm.VEq (kgProgS hdX pubX assembleS KgOut tableClaimsE BClaim VStackClaim)
open Lvm.Shape (Good₂ view vp imgC imgC_append imgC_ncard_le doomed_imgC onStackZs specKgS₂ openPostR_congr)
open scoped ENNReal NNReal
section Phases
variable (Ti : TInst) (L : Lvm.M3.Lay) (pub : Lvm.Pub) (hτL : ∀ t ∈ Ti.mbT, t.τ ≤ L.μ)
  (R : Column L.nuMain × Column L.nuRec → Prop)

/-- Carried through the relayout. -/
def aR1 (z : List E × E × E × E) (w : List E × List E × List E) (q : Column L.nuMain × Column L.nuRec) : Prop :=
  VsTrue Ti (z.1 ++ w.1) w.2.1 ∧ aRegs Ti L pub w.1 w.2.2 q ∧ aR0 Ti L pub hτL R q

/-- **After the wiring**: `S_flat`'s value is true, with the rest. -/
def aW (z : List E × E × E × E) (w : List E × List E × List E) (q : Column L.nuMain × Column L.nuRec) : Prop :=
  w.2.2.getD 1 0 = regSum Ti (· == .sflat) (zwE (Ti.zOf L pub q.1 q.2)) w.1 ∧ aR1 Ti L pub hτL R z w q

end Phases
end Lvm.Typed
end

section
set_option autoImplicit false
namespace Lvm.Typed
open Lvm.Loop LeanVM.Parameters LeanVM.Protocol LeanVM.Protocol.Compile LeanVM.Protocol.Verifier
open LeanVM.Protocol.Compile.VerifierProgram LeanVM.Protocol.EndToEnd LeanVM.Protocol.EndToEnd.Front
open LeanVM.Protocol.KeccakGkr LeanVM.Protocol.Whir.Sound
open LeanVM.Protocol.EndToEnd.Sound (RetOK)
open Lvm.M3 (Tab inst stackOf comCell vTables vLayout busResV lvmBusTableProg lbusTableCheckProg NoCG KeysOk AllSc
  LayOk FixOk lay26
  cg_ret cg_sample cg_readScalar cg_require cg_readScalars cg_sampleChallenges cg_sumcheck cg_lvmBusProg
  cg_tablePhaseClaims)
open Lvm.ASM (OpenClaims RootShape candPairs Pair GoodRel MidSpecR MidShape ExtJ kcertSJ GkS BndS KcS KgRet
  LkSJ εS midSpecOfRel retOK_kgProgS cg_kgProgS schemeS PSWith)
open Lvm.VEq (kgProgS hdX pubX assembleS KgOut tableClaimsE BClaim VStackClaim)
open Lvm.Shape (Good₂ view vp imgC imgC_append imgC_ncard_le doomed_imgC onStackZs specKgS₂ openPostR_congr)
open scoped ENNReal NNReal
section Phases
variable (Ti : TInst) (L : Lvm.M3.Lay) (pub : Lvm.Pub) (hτL : ∀ t ∈ Ti.mbT, t.τ ≤ L.μ)
  (R : Column L.nuMain × Column L.nuRec → Prop)

/-- **After the relayout**: `C_rec`'s extension at the point, with the rest. -/
def aRl (z : List E × E × E × E) (w : List E × List E × List E) (r : List E × E)
    (q : Column L.nuMain × Column L.nuRec) : Prop :=
  r.2 = mleZ L.nuRec (recE L q) r.1 ∧ aR1 Ti L pub hτL R z w q

end Phases
end Lvm.Typed
end

section
set_option autoImplicit false
namespace Lvm.Typed
open Lvm.Loop LeanVM.Parameters LeanVM.Protocol LeanVM.Protocol.Compile LeanVM.Protocol.Verifier
open LeanVM.Protocol.Compile.VerifierProgram LeanVM.Protocol.EndToEnd LeanVM.Protocol.EndToEnd.Front
open LeanVM.Protocol.KeccakGkr LeanVM.Protocol.Whir.Sound
open LeanVM.Protocol.EndToEnd.Sound (RetOK)
open Lvm.M3 (Tab inst stackOf comCell vTables vLayout busResV lvmBusTableProg lbusTableCheckProg NoCG KeysOk AllSc
  LayOk FixOk lay26
  cg_ret cg_sample cg_readScalar cg_require cg_readScalars cg_sampleChallenges cg_sumcheck cg_lvmBusProg
  cg_tablePhaseClaims)
open Lvm.ASM (OpenClaims RootShape candPairs Pair GoodRel MidSpecR MidShape ExtJ kcertSJ GkS BndS KcS KgRet
  LkSJ εS midSpecOfRel retOK_kgProgS cg_kgProgS schemeS PSWith)
open Lvm.VEq (kgProgS hdX pubX assembleS KgOut tableClaimsE BClaim VStackClaim)
open Lvm.Shape (Good₂ view vp imgC imgC_append imgC_ncard_le doomed_imgC onStackZs specKgS₂ openPostR_congr)
open scoped ENNReal NNReal
section Phases
variable (Ti : TInst) (L : Lvm.M3.Lay) (pub : Lvm.Pub) (hτL : ∀ t ∈ Ti.mbT, t.τ ≤ L.μ)
  (R : Column L.nuMain × Column L.nuRec → Prop)
variable {L₀ : ℕ} {εmax : ℝ≥0∞} (S : Set (Column L.nuMain × Column L.nuRec)) (hS : S.ncard ≤ L₀)

/-- **`γ`'s escape**: a wrong triple batched by `γ` meets the true one at `2/|E|` of the `γ`. -/
theorem wire_escape (hTi : Ti.Ok) (z : List E × E × E × E) (q : Column L.nuMain × Column L.nuRec)
    (hq : ¬ aABC Ti L pub hτL R z q) :
    avgE (fun γ ↦ indE (z.2.1 + γ * z.2.2.1 + γ * γ * z.2.2.2 =
      tCubeSum yVars (wireGT Ti.Q Ti.lay (Ti.zOf L pub q.1 q.2) γ z.1) [] ∧ aR0 Ti L pub hτL R q)) ≤ errE 2 := by
  by_cases hR : aR0 Ti L pub hτL R q
  · have hne := fun h ↦ hq ⟨h, hR⟩
    refine (avgE_mono fun γ ↦ indE_mono fun hγ ↦ ?_).trans (quadT_escape hne)
    rw [wire_nil _ _ hTi.1] at hγ
    exact hγ.1
  · refine (avgE_mono fun γ ↦ indE_mono (q := False) fun h ↦ hR h.2).trans ?_
    exact (avgE_le_of_le fun c ↦ (indE_of_not not_false).le).trans zero_le

/-- **The wiring** (`γ`, 21 plain rounds, the matrix and region values, the final check): from doom of the three
values at `r_x` to doom of the region values at `r_y` and the matrix values; lead `L₀·2/|E|`. -/
noncomputable def wireSpecT (hTi : Ti.Ok) (he : (L₀ : ℝ≥0∞) * errE 2 + 0 ≤ εmax) (z : List E × E × E × E) :
    Spec (wireProg Ti pub z.2)
      (fun h ↦ z.1.length = xVars ∧ Doomed (fun _ ↦ S) (aABC Ti L pub hτL R z) h)
      (fun w h ↦ z.1.length = xVars ∧ w.1.length = yVars ∧ w.2.1.length = 4 ∧ w.2.2.length = 4 ∧
        Doomed (fun _ ↦ S) (aW Ti L pub hτL R z w) h) εmax ((L₀ : ℝ≥0∞) * errE 2 + 0) 0 := by
  exact if hz : z.1.length = xVars then by
    unfold wireProg
    refine ((doomSample (C := fun _ ↦ S) (fun _ _ _ ↦ rfl) (fun _ ↦ hS) (aABC Ti L pub hτL R z)
      (fun γ q ↦ z.2.1 + γ * z.2.2.1 + γ * γ * z.2.2.2 =
        tCubeSum yVars (wireGT Ti.Q Ti.lay (Ti.zOf L pub q.1 q.2) γ z.1) [] ∧ aR0 Ti L pub hτL R q)
      (errE 2) (fun q hq ↦ wire_escape Ti L pub hτL R hTi z q hq) (εmax := εmax) (T := 0)).mono
      (fun _ hp ↦ hp.2) (fun _ _ hp ↦ hp) le_rfl le_rfl le_rfl).bind fun γ ↦ ?_
    refine (LeanVM.Protocol.KeccakGkr.sumcheckSpec (C := fun _ ↦ S) (fun _ _ _ ↦ rfl) (fun _ ↦ hS)
      (aR0 Ti L pub hτL R) (F := fun q acc ↦ tCubeSum yVars (wireGT Ti.Q Ti.lay (Ti.zOf L pub q.1 q.2) γ z.1) acc)
      (tCubeSum_plainFamily yVars 2 _ fun q pre post ↦ polyLE_wireG _ _ _ _ _ pre post)
      (count := 3) (by norm_num) (by norm_num) zero_le he yVars [] _ (by simp)).bind fun rf ↦ ?_
    exact if hry : rf.1.length = yVars then
      ((doomReadN (C := fun _ ↦ S) (fun _ _ _ ↦ rfl)
          (fun q ↦ rf.2 = tCubeSum yVars (wireGT Ti.Q Ti.lay (Ti.zOf L pub q.1 q.2) γ z.1) ([] ++ rf.1) ∧
            aR0 Ti L pub hτL R q) (zero_le) 3).mono (fun _ hp ↦ hp.2) (fun _ _ hp ↦ hp) le_rfl le_rfl
          le_rfl).bind fun vs ↦
        if hvs : vs.length = 4 then
          ((doomReadN (C := fun _ ↦ S) (fun _ _ _ ↦ rfl)
              (fun q ↦ rf.2 = tCubeSum yVars (wireGT Ti.Q Ti.lay (Ti.zOf L pub q.1 q.2) γ z.1) ([] ++ rf.1) ∧
                aR0 Ti L pub hτL R q) (zero_le) 3).mono (fun _ hp ↦ hp.2) (fun _ _ hp ↦ hp) le_rfl le_rfl
              le_rfl).bind fun rv ↦
            if hrv : rv.length = 4 then
              (Spec.require (Pre := fun h ↦ rv.length = 3 + 1 ∧ Doomed (fun _ ↦ S) (fun q ↦ rf.2 =
                  tCubeSum yVars (wireGT Ti.Q Ti.lay (Ti.zOf L pub q.1 q.2) γ z.1) ([] ++ rf.1) ∧
                    aR0 Ti L pub hτL R q) h)
                (Post := fun _ h ↦ Doomed (fun _ ↦ S) (aW Ti L pub hτL R z (rf.1, vs, rv)) h)
                fun _ hp hc ↦ Doomed.mono hp.2 fun q ⟨hS1, hV, ⟨h0, h2, h3⟩, hR⟩ ↦ ⟨by
                  rw [List.nil_append, tCubeSum_full _ _ hry, wireGT, wireM_full _ _ hTi.1 _ _ _ hz,
                    mleZ_zOf Ti L pub hTi, hc, sum_four rv hrv]
                  simp only at hS1 h0 h2 h3
                  rw [← hV 0 (by norm_num), ← hV 1 (by norm_num), ← hV 2 (by norm_num), ← hV 3 (by norm_num),
                    h0, hS1, h2, h3], hR⟩).bind fun _ ↦
                (Spec.ret (Post := fun w h ↦ z.1.length = xVars ∧ w.1.length = yVars ∧ w.2.1.length = 4 ∧
                    w.2.2.length = 4 ∧ Doomed (fun _ ↦ S) (aW Ti L pub hτL R z w) h) (rf.1, vs, rv)).mono
                  (fun _ hp ↦ ⟨hz, hry, hvs, hrv, hp⟩) (fun _ _ hp ↦ hp) le_rfl le_rfl le_rfl
            else Spec.dead.mono (fun _ hp ↦ hrv hp.1) (fun _ _ hp ↦ hp) le_rfl zero_le le_rfl
        else Spec.dead.mono (fun _ hp ↦ hvs hp.1) (fun _ _ hp ↦ hp) le_rfl zero_le le_rfl
    else Spec.dead.mono (fun _ hp ↦ hry hp.1) (fun _ _ hp ↦ hp) le_rfl zero_le le_rfl
  else Spec.dead.mono (fun _ hp ↦ hz hp.1) (fun _ _ hp ↦ hp) le_rfl zero_le le_rfl

/-- **The `S_flat` relayout** (19 plain rounds, `v_R`, the final check): from doom of `S_flat`'s region value at
`r_y` to doom of `C_rec`'s extension at the point; lead `0`, follower `Tf`. -/
noncomputable def relaySpecT (hTi : Ti.Ok) (hmaps : Ti.MapsFit L) (hrec : L.nuRec = relayRounds)
    (he : (L₀ : ℝ≥0∞) * errE 2 + 0 ≤ εmax) {Tf : ℝ≥0∞} (hTf : Tf ≤ εmax) (z : List E × E × E × E)
    (w : List E × List E × List E) :
    Spec (relayProg Ti w.1 (w.2.2.getD 1 0))
      (fun h ↦ z.1.length = xVars ∧ w.1.length = yVars ∧ w.2.1.length = 4 ∧ w.2.2.length = 4 ∧
        Doomed (fun _ ↦ S) (aW Ti L pub hτL R z w) h)
      (fun r h ↦ z.1.length = xVars ∧ w.1.length = yVars ∧ w.2.1.length = 4 ∧ r.1.length = relayRounds ∧
        Doomed (fun _ ↦ S) (aRl Ti L pub hτL R z w r) h) εmax 0 Tf := by
  exact if hl : z.1.length = xVars ∧ w.1.length = yVars ∧ w.2.1.length = 4 then by
    unfold relayProg
    refine ((LeanVM.Protocol.KeccakGkr.sumcheckSpec (C := fun _ ↦ S) (fun _ _ _ ↦ rfl) (fun _ ↦ hS)
      (aR1 Ti L pub hτL R z w)
      (F := fun q acc ↦ tCubeSum L.nuRec (relayGT Ti.lay.yregs Ti.sflatW w.1 L.nuRec (recE L q)) acc)
      (tCubeSum_plainFamily L.nuRec 2 _ fun q pre post ↦ polyLE_relayG _ _ _ _ _ pre post)
      (count := 3) (by norm_num) (by norm_num) zero_le he relayRounds [] _ (by simp [hrec])).mono
      (fun _ hp ↦ Doomed.mono hp.2.2.2.2 fun q hq ↦ ⟨by
        rw [hq.1, relay_true Ti L pub hTi hmaps q.1 q.2 w.1], hq.2⟩)
      (fun _ _ hp ↦ hp) le_rfl le_rfl le_rfl).bind fun rf ↦ ?_
    exact if hrr : rf.1.length = relayRounds then
      ((doomRead (C := fun _ ↦ S) (fun _ _ _ ↦ rfl)
          (fun q ↦ rf.2 = tCubeSum L.nuRec (relayGT Ti.lay.yregs Ti.sflatW w.1 L.nuRec (recE L q)) ([] ++ rf.1) ∧
            aR1 Ti L pub hτL R z w q) hTf).mono (fun _ hp ↦ hp.2) (fun _ _ hp ↦ hp) le_rfl le_rfl le_rfl).bind
        fun vR ↦
        (Spec.require (Pre := Doomed (fun _ ↦ S) (fun q ↦
              rf.2 = tCubeSum L.nuRec (relayGT Ti.lay.yregs Ti.sflatW w.1 L.nuRec (recE L q)) ([] ++ rf.1) ∧
                aR1 Ti L pub hτL R z w q))
            (Post := fun _ h ↦ Doomed (fun _ ↦ S) (aRl Ti L pub hτL R z w (rf.1, vR)) h)
            fun _ hp hc ↦ Doomed.mono hp fun q hq ↦ ⟨by
              have h1 : vR = mleZ L.nuRec (recE L q) rf.1 := hq.1
              rw [List.nil_append, tCubeSum_full _ _ (hrr.trans hrec.symm), relayGT, hc, h1]
              rfl, hq.2⟩).bind fun _ ↦
          (Spec.ret (Post := fun r h ↦ z.1.length = xVars ∧ w.1.length = yVars ∧ w.2.1.length = 4 ∧
              r.1.length = relayRounds ∧ Doomed (fun _ ↦ S) (aRl Ti L pub hτL R z w r) h) (rf.1, vR)).mono
            (fun _ hp ↦ ⟨hl.1, hl.2.1, hl.2.2, hrr, hp⟩) (fun _ _ hp ↦ hp) le_rfl le_rfl le_rfl
    else Spec.dead.mono (fun _ hp ↦ hrr hp.1) (fun _ _ hp ↦ hp) le_rfl zero_le le_rfl
  else Spec.dead.mono (fun _ hp ↦ hl ⟨hp.1, hp.2.1, hp.2.2.1⟩) (fun _ _ hp ↦ hp) le_rfl zero_le le_rfl

/-- **A23 at `Φ_Q`** (`accSpecQ`): outside `AccGood` (a wrong matrix value or a wrong `acc_in`) the phase's own
escape bounds the run (`1/|E|` per `κ_j`, `43/|E|` at `t`); inside it, the matrix values and `AccOk acc_in` are true
and leave the carried predicate. -/
noncomputable def accSpecTy (hTi : Ti.Ok) (hacc : pub.accIn.pt.length = phiVars) {Tm : ℝ≥0∞}
    (hD : errE phiVars ≤ εmax) (hTm : Tm ≤ εmax) (z : List E × E × E × E) (w : List E × List E × List E)
    (r : List E × E) :
    Spec (accProgQ Ti.Q Ti.lay true (FE.toExt3 pub.accIn.y) (pub.accIn.pt.map FE.toExt3) (z.1 ++ w.1) w.2.1)
      (fun h ↦ z.1.length = xVars ∧ w.1.length = yVars ∧ w.2.1.length = 4 ∧ r.1.length = relayRounds ∧
        Doomed (fun _ ↦ S) (aRl Ti L pub hτL R z w r) h)
      (fun _ h ↦ Doomed (fun _ ↦ S) (fun q ↦ M3Holds (inst L Ti.mbT hτL) () (stackOf L q.1 q.2) ∧
        aRm Ti L pub R w r q) h) εmax (max (2 * errE 1) Tm) Tm :=
  if hl : z.1.length = xVars ∧ w.1.length = yVars ∧ w.2.1.length = 4 then
    (accSpecQ Ti.Q Ti.lay hTi.1 (ok := true) (yIn := FE.toExt3 pub.accIn.y) (pub.accIn.pt.map FE.toExt3)
        (z.1 ++ w.1) w.2.1 (by rw [List.length_map, hacc]) (by rw [List.length_append, hl.1, hl.2.1])
        hl.2.2 (Doomed (fun _ ↦ S) (fun q ↦ M3Holds (inst L Ti.mbT hτL) () (stackOf L q.1 q.2) ∧
          aRm Ti L pub R w r q)) (fun _ _ _ h ↦ h) hD hTm).mono
      (fun _ hp ↦ by
        by_cases hg : Lvm.Acc.AccGood 2 true (FE.toExt3 pub.accIn.y) (pub.accIn.pt.map FE.toExt3) (PhiQ Ti.Q Ti.lay)
            (deltaQ Ti.Q Ti.lay w.2.1 (z.1 ++ w.1))
        · refine .inr (Doomed.mono hp.2.2.2.2 fun q ⟨hm, ⟨hv, hrg⟩, hR⟩ ↦ ⟨hv, fun o ho ↦ ?_, hrg, hm, hR, hg.2.1⟩)
          have h0 := hg.2.2 o (by norm_num; omega)
          rw [deltaQ, ite_eq_left ho, sub_eq_zero] at h0
          exact h0
        · exact .inl hg)
      (fun _ _ hp ↦ hp) le_rfl le_rfl le_rfl
  else Spec.dead.mono (fun _ hp ↦ hl ⟨hp.1, hp.2.1, hp.2.2.1⟩) (fun _ _ hp ↦ hp) le_rfl zero_le le_rfl

end Phases
end Lvm.Typed
end

section
set_option autoImplicit false
namespace Lvm.Typed
open Lvm.Loop LeanVM.Parameters LeanVM.Protocol LeanVM.Protocol.Compile LeanVM.Protocol.Verifier
open LeanVM.Protocol.Compile.VerifierProgram LeanVM.Protocol.EndToEnd LeanVM.Protocol.EndToEnd.Front
open LeanVM.Protocol.KeccakGkr LeanVM.Protocol.Whir.Sound
open LeanVM.Protocol.EndToEnd.Sound (RetOK)
open Lvm.M3 (Tab inst stackOf comCell vTables vLayout busResV lvmBusTableProg lbusTableCheckProg NoCG KeysOk AllSc
  LayOk FixOk lay26
  cg_ret cg_sample cg_readScalar cg_require cg_readScalars cg_sampleChallenges cg_sumcheck cg_lvmBusProg
  cg_tablePhaseClaims)
open Lvm.ASM (OpenClaims RootShape candPairs Pair GoodRel MidSpecR MidShape ExtJ kcertSJ GkS BndS KcS KgRet
  LkSJ εS midSpecOfRel retOK_kgProgS cg_kgProgS schemeS PSWith)
open Lvm.VEq (kgProgS hdX pubX assembleS KgOut tableClaimsE BClaim VStackClaim)
open Lvm.Shape (Good₂ view vp imgC imgC_append imgC_ncard_le doomed_imgC onStackZs specKgS₂ openPostR_congr)
open scoped ENNReal NNReal
section Phases
variable (Ti : TInst) (L : Lvm.M3.Lay) (pub : Lvm.Pub) (hτL : ∀ t ∈ Ti.mbT, t.τ ≤ L.μ)
  (R : Column L.nuMain × Column L.nuRec → Prop)
variable {L₀ : ℕ} {εmax : ℝ≥0∞} (S : Set (Column L.nuMain × Column L.nuRec)) (hS : S.ncard ≤ L₀)

/-- **The typed phases on a fixed candidate set** (`typedSpecR` at `C h = S`): the zerocheck, the wiring, the
relayout, A23 and the mini-bus composed; the first commitment's word carried to the mini-bus. -/
noncomputable def typedSpecIn (hTi : Ti.Ok) (hmaps : Ti.MapsFit L) (hrec : L.nuRec = relayRounds)
    (hacc : pub.accIn.pt.length = phiVars) (hsc : AllSc Ti.mbT) (hlay : LayOk L Ti.mbT) (hkey : KeysOk Ti.mbT)
    (hw : ∀ t ∈ Ti.mbT, 0 < t.w) (hfix : FixOk Ti.mbT) (hμ : (inst L Ti.mbT hτL).μBus = miniDepth)
    (hfin : S.Finite) {T : ℝ≥0∞} (herr : TErrs L₀ (inst L Ti.mbT hτL) εmax T) :
    Spec (typedProg Ti pub)
      (fun h ↦ (∃ W, firstWord h = some W) ∧
        Doomed (fun _ ↦ S) (fun p ↦ TGood Ti L hτL pub p ∧ R p ∧ AccOkT Ti pub) h)
      (fun out h ↦ Doomed (fun _ ↦ S) (fun p ↦ TClaimsHold L out p ∧ R p) h) εmax (leadT L₀) T := by
  obtain ⟨he, hLacc, hD, hTm, hab, he4, hTl, hlam, he3, hTf, hxi⟩ := herr.facts
  have hJ : ∀ {α : Type} (p : VerifierProgram α) (h₀ l : List Ev), p.Reach h₀ l →
      (∃ W, firstWord h₀ = some W) → ∃ W, firstWord (h₀ ++ l) = some W :=
    fun _ _ l _ ⟨W, hW⟩ ↦ ⟨W, firstWord_append hW l⟩
  refine Spec.congr (typedProg_eq Ti pub).symm ?_
  refine (((zeroSpecT Ti L pub hτL R S hS he).frame _ (hJ _)).mono
    (fun _ hp ↦ ⟨Doomed.mono hp.2 fun q hq ↦ ⟨⟨(wiringRel_iff _ _ hTi.1 _).mpr ((zeroOn_nil _ _).mp hq.1),
      hq.2.1⟩, hq.2.2.1, hq.2.2.2⟩, hp.1⟩) (fun _ _ hp ↦ hp) le_rfl le_rfl le_rfl).bind fun z ↦ ?_
  refine ((wireSpecT Ti L pub hτL R S hS hTi he z).frame _ (hJ _)).bind fun w ↦ ?_
  -- the relayout's follower is A23, whose lead is `max (2/|E|) (abError + 0)` (`hLacc`)
  refine ((relaySpecT Ti L pub hτL R S hS hTi hmaps hrec he hLacc z w).frame _ (hJ _)).bind fun r ↦ ?_
  exact if hr1 : r.1.length = relayRounds then
    ((accSpecTy Ti L pub hτL R S hTi hacc hD hTm z w r).frame _ (hJ _)).bind fun _ ↦
      ((miniSpecTy Ti L pub hτL R S hS hfin hsc hlay hkey hw hfix hμ hab he4 hTl hlam he3 hTf (hxi _) w r).mono
        (fun _ hp ↦ ⟨hp.2, hp.1⟩) (fun _ _ hp ↦ hp) le_rfl le_rfl le_rfl).bind fun cl ↦
        (Spec.ret (Post := fun out h ↦ Doomed (fun _ ↦ S) (fun p ↦ TClaimsHold L out p ∧ R p) h)
          (typedClaims Ti w.1 w.2.2 r.1 r.2 cl)).mono
          (fun _ hp ↦ Doomed.mono hp.2 fun q hq ↦ by
            obtain ⟨⟨h1, h2⟩, hR⟩ := hq
            refine ⟨blockHolds_mini L hlay hp.1
                (fun c hc ↦ h1 c (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ hc)))
                (fun c hc ↦ h2 c (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ hc))), ⟨?_, ?_, ?_, ?_⟩, hR⟩
            · exact ((holds_relayPoint L hrec r.1 hr1 r.2 q.2).mp (h1 _ (List.mem_cons_self ..))).symm
            · exact ((holds_com Ti L pub hTi hmaps q.1 q.2 w.1 _).mp (h2 _ (List.mem_cons_self ..))).symm
            · exact ((holds_sigma Ti L pub hTi hmaps q.1 q.2 w.1 _).mp
                (h1 _ (List.mem_cons_of_mem _ (List.mem_cons_self ..)))).symm
            · exact ((holds_ks Ti L pub hTi hmaps q.1 q.2 w.1 _).mp
                (h2 _ (List.mem_cons_of_mem _ (List.mem_cons_self ..)))).symm)
          (fun _ _ hp ↦ hp) le_rfl le_rfl le_rfl
  else Spec.dead.mono (fun _ hp ↦ hr1 hp.1.2.2.2.1) (fun _ _ hp ↦ hp) le_rfl zero_le le_rfl

end Phases
end Lvm.Typed
end

section
set_option autoImplicit false
namespace Lvm.Typed
open Lvm.Loop LeanVM.Parameters LeanVM.Protocol LeanVM.Protocol.Compile LeanVM.Protocol.Verifier
open LeanVM.Protocol.Compile.VerifierProgram LeanVM.Protocol.EndToEnd LeanVM.Protocol.EndToEnd.Front
open LeanVM.Protocol.KeccakGkr LeanVM.Protocol.Whir.Sound
open LeanVM.Protocol.EndToEnd.Sound (RetOK)
open Lvm.M3 (Tab inst stackOf comCell vTables vLayout busResV lvmBusTableProg lbusTableCheckProg NoCG KeysOk AllSc
  LayOk FixOk lay26
  cg_ret cg_sample cg_readScalar cg_require cg_readScalars cg_sampleChallenges cg_sumcheck cg_lvmBusProg
  cg_tablePhaseClaims)
open Lvm.ASM (OpenClaims RootShape candPairs Pair GoodRel MidSpecR MidShape ExtJ kcertSJ GkS BndS KcS KgRet
  LkSJ εS midSpecOfRel retOK_kgProgS cg_kgProgS schemeS PSWith)
open Lvm.VEq (kgProgS hdX pubX assembleS KgOut tableClaimsE BClaim VStackClaim)
open Lvm.Shape (Good₂ view vp imgC imgC_append imgC_ncard_le doomed_imgC onStackZs specKgS₂ openPostR_congr)
open scoped ENNReal NNReal

/-- **The typed phases' specification** (B-DES §2's `typedSpecR`, in `midBusTableAccSpecB`'s shape, generic in
the candidate set `C` and the carried `R`): from `G ∧ firstWord ∧ Doomed C (TGood ∧ R ∧ AccOkT)` to the doom of the
returned claims with `R`. Owner **L-B** (B1-V: the programs' final form). -/
noncomputable def typedSpecR (Ti : TInst) (L : Lvm.M3.Lay) (pub : Lvm.Pub) (hτL : ∀ t ∈ Ti.mbT, t.τ ≤ L.μ)
    (hTi : Ti.Ok) (hmaps : Ti.MapsFit L) (hrec : L.nuRec = relayRounds)
    (hacc : pub.accIn.pt.length = phiVars) (hsc : AllSc Ti.mbT) (hlay : LayOk L Ti.mbT) (hkey : KeysOk Ti.mbT)
    (hw : ∀ t ∈ Ti.mbT, 0 < t.w) (hfix : FixOk Ti.mbT) (hμ : (inst L Ti.mbT hτL).μBus = miniDepth)
    (C : List Ev → Set (Column L.nuMain × Column L.nuRec)) (R : Column L.nuMain × Column L.nuRec → Prop)
    {L₀ : ℕ} {εmax T : ℝ≥0∞} (G : List Ev → Prop) (hCG : ∀ h₀ l, G h₀ → C (h₀ ++ l) = C h₀)
    (hf : ∀ h, (C h).Finite) (hc : ∀ h, (C h).ncard ≤ L₀)
    (herr : TErrs L₀ (inst L Ti.mbT hτL) εmax T) :
    Spec (typedProg Ti pub)
      (fun h ↦ G h ∧ (∃ W, firstWord h = some W) ∧
        Doomed C (fun p ↦ TGood Ti L hτL pub p ∧ R p ∧ AccOkT Ti pub) h)
      (fun out h ↦ Doomed C (fun p ↦ TClaimsHold L out p ∧ R p) h) εmax (leadT L₀) T :=
  (Lvm.M3.Spec.glue (ι := {S : Set (Column L.nuMain × Column L.nuRec) // S.Finite ∧ S.ncard ≤ L₀})
      (fun h ↦ ⟨C h, hf h, hc h⟩) G (fun h₀ l hG ↦ Subtype.ext (hCG h₀ l hG))
      fun S ↦ typedSpecIn Ti L pub hτL R S.1 S.2.2 hTi hmaps hrec hacc hsc hlay hkey hw hfix hμ S.2.1 herr).mono
    (fun _ hp ↦ ⟨hp.1, hp.2.1, hp.2.2⟩) (fun _ _ hp ↦ hp) le_rfl le_rfl le_rfl

end Lvm.Typed
end

section
set_option autoImplicit false
namespace Lvm.Typed
open Lvm.Loop LeanVM.Parameters LeanVM.Protocol LeanVM.Protocol.Compile LeanVM.Protocol.Verifier
open LeanVM.Protocol.Compile.VerifierProgram LeanVM.Protocol.EndToEnd LeanVM.Protocol.EndToEnd.Front
open LeanVM.Protocol.KeccakGkr LeanVM.Protocol.Whir.Sound
open LeanVM.Protocol.EndToEnd.Sound (RetOK)
open Lvm.M3 (Tab inst stackOf comCell vTables vLayout busResV lvmBusTableProg lbusTableCheckProg NoCG KeysOk AllSc
  LayOk FixOk lay26
  cg_ret cg_sample cg_readScalar cg_require cg_readScalars cg_sampleChallenges cg_sumcheck cg_lvmBusProg
  cg_tablePhaseClaims)
open Lvm.ASM (OpenClaims RootShape candPairs Pair GoodRel MidSpecR MidShape ExtJ kcertSJ GkS BndS KcS KgRet
  LkSJ εS midSpecOfRel retOK_kgProgS cg_kgProgS schemeS PSWith)
open Lvm.VEq (kgProgS hdX pubX assembleS KgOut tableClaimsE BClaim VStackClaim)
open Lvm.Shape (Good₂ view vp imgC imgC_append imgC_ncard_le doomed_imgC onStackZs specKgS₂ openPostR_congr)
open scoped ENNReal NNReal
variable {Ti : TInst}

/-- **`NodeSound` for `Good₂ (GoodT Ti H)`** from the big layout's (`LvmShape.nodeSound₂`, unchanged). -/
theorem nodeSoundT₂ (H : THyp Ti) {VS : Lvm.T.SProg} {vk : RecursionFast.Digest}
    {child : Column 19 → RecursionFast.Signed} (h : Lvm.ASM.NodeSound VS vk (GoodT Ti H) child) :
    Lvm.ASM.NodeSound VS vk (Good₂ (GoodT Ti H)) child :=
  Lvm.Shape.nodeSound₂ h

end Lvm.Typed
end

section
set_option autoImplicit false
namespace Lvm.Typed
open Lvm.Loop LeanVM.Parameters LeanVM.Protocol LeanVM.Protocol.Compile LeanVM.Protocol.Verifier
open LeanVM.Protocol.Compile.VerifierProgram LeanVM.Protocol.EndToEnd LeanVM.Protocol.EndToEnd.Front
open LeanVM.Protocol.KeccakGkr LeanVM.Protocol.Whir.Sound
open LeanVM.Protocol.EndToEnd.Sound (RetOK)
open Lvm.M3 (Tab inst stackOf comCell vTables vLayout busResV lvmBusTableProg lbusTableCheckProg NoCG KeysOk AllSc
  LayOk FixOk lay26
  cg_ret cg_sample cg_readScalar cg_require cg_readScalars cg_sampleChallenges cg_sumcheck cg_lvmBusProg
  cg_tablePhaseClaims)
open Lvm.ASM (OpenClaims RootShape candPairs Pair GoodRel MidSpecR MidShape ExtJ kcertSJ GkS BndS KcS KgRet
  LkSJ εS midSpecOfRel retOK_kgProgS cg_kgProgS schemeS PSWith)
open Lvm.VEq (kgProgS hdX pubX assembleS KgOut tableClaimsE BClaim VStackClaim)
open Lvm.Shape (Good₂ view vp imgC imgC_append imgC_ncard_le doomed_imgC onStackZs specKgS₂ openPostR_congr)
open scoped ENNReal NNReal
variable {Ti : TInst}

/-- **The typed claims and the Keccak phases' claims, in both shapes** (`assembleS₂`'s): `C_main`'s through
`onStackZ` when small. -/
def assembleT₂ (x : List UInt8) (a : OpenClaims) (kg : KgOut) : OpenClaims :=
  (a.1 ++ (assembleS [] (pubX x) [] kg).1, onStackZs x (a.2 ++ (assembleS [] (pubX x) [] kg).2))

/-- **The middle phases of the typed backend in both shapes**: the typed phases, V_S phases 4–7, the claims. -/
def midT₂ (Ti : TInst) (x : List UInt8) : VerifierProgram OpenClaims :=
  typedProg Ti (pubX x) >>= fun a ↦ kgProgS (hdX x).s (pubX x).n >>= fun k ↦
    VerifierProgram.ret (assembleT₂ x a k)

end Lvm.Typed
end

section
set_option autoImplicit false
namespace Lvm.Typed
open Lvm.Loop LeanVM.Parameters LeanVM.Protocol LeanVM.Protocol.Compile LeanVM.Protocol.Verifier
open LeanVM.Protocol.Compile.VerifierProgram LeanVM.Protocol.EndToEnd LeanVM.Protocol.EndToEnd.Front
open LeanVM.Protocol.KeccakGkr LeanVM.Protocol.Whir.Sound
open LeanVM.Protocol.EndToEnd.Sound (RetOK)
open Lvm.M3 (Tab inst stackOf comCell vTables vLayout busResV lvmBusTableProg lbusTableCheckProg NoCG KeysOk AllSc
  LayOk FixOk lay26
  cg_ret cg_sample cg_readScalar cg_require cg_readScalars cg_sampleChallenges cg_sumcheck cg_lvmBusProg
  cg_tablePhaseClaims)
open Lvm.ASM (OpenClaims RootShape candPairs Pair GoodRel MidSpecR MidShape ExtJ kcertSJ GkS BndS KcS KgRet
  LkSJ εS midSpecOfRel retOK_kgProgS cg_kgProgS schemeS PSWith)
open Lvm.VEq (kgProgS hdX pubX assembleS KgOut tableClaimsE BClaim VStackClaim)
open Lvm.Shape (Good₂ view vp imgC imgC_append imgC_ncard_le doomed_imgC onStackZs specKgS₂ openPostR_congr)
open scoped ENNReal NNReal
variable {Ti : TInst}

/-- **Every return of the typed phases meets `TRet`.** Owner **L-B**. -/
theorem retOK_typedProg (H : THyp Ti) (pub : Lvm.Pub) : RetOK TRet (typedProg Ti pub) := by
  rw [typedProg_eq]
  refine RetOK.bind_true fun z ↦ RetOK.bind_true fun w ↦ RetOK.bind_true fun r ↦ RetOK.bind_true fun _ ↦ ?_
  refine (Lvm.ASM.retOK_lbusTableCheckProg Ti.mbT miniDepth).bind fun cl hcl ↦ RetOK.ret ?_
  have hm1 := isMultiaffine_miniClaims Ti H.layOk .crec cl
  have hm2 := isMultiaffine_miniClaims Ti H.layOk .main cl
  have hl1 := length_miniClaims Ti .crec cl
  have hl2 := length_miniClaims Ti .main cl
  have hcl' : cl.length ≤ 2 ^ 38 := hcl.2.trans H.widths
  refine ⟨fun c hc ↦ ?_, fun c hc ↦ ?_, ?_, ?_⟩
  · rcases List.mem_cons.mp hc with rfl | hc
    · exact Lvm.ASM.isMultiaffine_onStack _ le_rfl (Lvm.ASM.isMultiaffine_eqEvalN _ _)
    rcases List.mem_cons.mp hc with rfl | hc
    · exact isMultiaffine_regClaim Ti 19 _ _ _ _
    · exact hm1 c hc
  · rcases List.mem_cons.mp hc with rfl | hc
    · exact isMultiaffine_regClaim Ti _ _ _ _ _
    rcases List.mem_cons.mp hc with rfl | hc
    · exact isMultiaffine_regClaim Ti _ _ _ _ _
    · exact hm2 c hc
  · simp only [typedClaims, List.length_cons]; (clear * - hl1 hcl'; omega)
  · simp only [typedClaims, List.length_cons]; (clear * - hl2 hcl'; omega)

/-- **The semantic link, typed** (`link_assembleS₂`'s): the assembled claims holding on a pair give the Keccak
phases' relation and the typed claims with the boundary claims on the view. Owner **L-B**. -/
theorem linkT₂ (x : List UInt8) (a : OpenClaims) (k : KgOut) (p : Pair) (ha : TRet a) (hk : KgRet k)
    (h1 : ∀ c ∈ (assembleT₂ x a k).1, LeanVM.Protocol.EndToEnd.StackClaim.Holds 19 c p.2)
    (h2 : ∀ c ∈ (assembleT₂ x a k).2, LeanVM.Protocol.EndToEnd.StackClaim.Holds CMain.nu20 c p.1) :
    KcS k (vp x p) ∧ BT x a (vp x p) := by
  have h2' : ∀ c ∈ a.2 ++ (assembleS [] (pubX x) [] k).2,
      LeanVM.Protocol.EndToEnd.StackClaim.Holds CMain.nu20 c (vp x p).1 := by
    intro c hc
    unfold assembleT₂ onStackZs at h2
    unfold vp view
    by_cases hs : Lvm.Shape.small x = true
    · simp only [hs, ite_true, List.mem_map] at h2 ⊢
      exact (Lvm.Shape.holds_onStackZ c p.1).mp (h2 _ ⟨c, hc, rfl⟩)
    · simp only [hs, ite_false, Bool.false_eq_true] at h2 ⊢
      exact h2 c hc
  have h1' : ∀ c ∈ a.1 ++ (assembleS [] (pubX x) [] k).1, LeanVM.Protocol.EndToEnd.StackClaim.Holds 19 c p.2 := h1
  have hc := Lvm.ASM.holdsC_of_assembleS (fun c hc ↦ h1' c (List.mem_append_right _ hc))
    (fun c hc ↦ h2' c (List.mem_append_right _ hc))
  obtain ⟨⟨hr, -, -⟩, ⟨hrk, -, hck, -, -, hkc, hks⟩⟩ := hk
  have hm : ∀ b, (Lvm.Com.main, b) ∈ Lvm.ASM.claimsS [] (pubX x) [] k →
      LeanVM.Protocol.EndToEnd.StackClaim.Holds CMain.nu20 b.onStack (vp x p).1 := fun b hb ↦ hc _ hb
  have hTP : ∀ b ∈ Lvm.VEq.tapeClaimsE k.1 (pubX x),
      LeanVM.Protocol.EndToEnd.StackClaim.Holds CMain.nu20 b.onStack (vp x p).1 :=
    fun b hb ↦ hm b (by simp [Lvm.ASM.claimsS, hb])
  have hKK : ∀ b ∈ Lvm.VEq.keccakClaimsE Lvm.VEq.ksBlk k.2.1,
      LeanVM.Protocol.EndToEnd.StackClaim.Holds CMain.nu20 b.onStack (vp x p).1 :=
    fun b hb ↦ hm b (by simp [Lvm.ASM.claimsS, hb])
  have hsub : ∀ l : List (Lvm.Com × BClaim), (∀ e ∈ l, e ∈ Lvm.ASM.claimsS [] (pubX x) [] k) →
      ∀ e ∈ l, Lvm.ASM.HoldsC (vp x p).1 (vp x p).2 e := fun l hl e he ↦ hc e (hl e he)
  refine ⟨⟨Lvm.ASM.tapeClaims_of k.1 hr (pubX x) hTP,
    ⟨Lvm.ASM.callerClaims_ks k.2.1 hrk hck hKK (hsub _ (fun e he ↦ by simp [Lvm.ASM.claimsS, he])),
      Lvm.ASM.ksLinkClaims_of k.2.2.1 k.2.2.2.1 k.2.2.2.2 hkc hks
        (hsub _ (fun e he ↦ by simp [Lvm.ASM.claimsS, he]))⟩⟩,
    ⟨fun c hc ↦ h1' c (List.mem_append_left _ hc), fun c hc ↦ h2' c (List.mem_append_left _ hc)⟩,
    Lvm.ASM.bndS_of_tape x _ hTP⟩

/-- **The side conditions, typed** (`side_midS₂`'s). Owner **L-B**. -/
theorem sideT₂ (x : List UInt8) (a : OpenClaims) (k : KgOut) (ha : TRet a) (hk : KgRet k) :
    (∀ c ∈ (assembleT₂ x a k).1, IsMultiaffine 19 c.1) ∧
    (∀ c ∈ (assembleT₂ x a k).2, IsMultiaffine CMain.nu20 c.1) ∧
    (assembleT₂ x a k).1.length ≤ 2 ^ 55 ∧ (assembleT₂ x a k).2.length ≤ 2 ^ 40 := by
  obtain ⟨s1, s2, s3, s4⟩ := Lvm.ASM.side_assembleS [] (pubX x) [] k (fun _ h ↦ by simp at h)
    ⟨fun _ h ↦ by simp at h, by simp⟩ (by simp) hk (by rw [Lvm.ASM.length_pubX_h]; norm_num)
  obtain ⟨a1, a2, a3, a4⟩ := ha
  have hk1 : (k.2.1.2.2.1.1).length ≤ 1 := hk.2.2.2.2.1
  have l1 : (assembleS [] (pubX x) [] k).1.length ≤ 1 := by
    rw [Lvm.ASM.assembleS_eq, List.length_map]
    simpa using Lvm.ASM.length_crec_le [] (pubX x) [] k
  have l2 : (assembleS [] (pubX x) [] k).2.length ≤ 40 := by
    rw [Lvm.ASM.assembleS_eq, List.length_map]
    have h := Lvm.ASM.length_claimsS [] (pubX x) [] k
    have h0 : (tableClaimsE [] []).length = 0 := rfl
    rw [Lvm.ASM.length_pubX_h, h0] at h
    exact (List.length_filter_le _ _).trans (by (clear * - hk1 h; omega))
  have hm : ∀ c ∈ a.2 ++ (assembleS [] (pubX x) [] k).2, IsMultiaffine CMain.nu20 c.1 := fun c hc ↦ by
    rcases List.mem_append.mp hc with hc | hc
    · exact a2 c hc
    · exact s2 c hc
  refine ⟨fun c hc ↦ ?_, fun c hc ↦ ?_, ?_, ?_⟩
  · rcases List.mem_append.mp hc with hc | hc
    · exact a1 c hc
    · exact s1 c hc
  · unfold assembleT₂ onStackZs at hc
    split_ifs at hc
    · obtain ⟨c', hc', rfl⟩ := List.mem_map.mp hc
      exact Lvm.Shape.isMultiaffine_onStackZ (hm c' hc')
    · exact hm c hc
  · simp only [assembleT₂, List.length_append]
    (clear * - s3 a3 l1; omega)
  · simp only [assembleT₂, onStackZs]
    split_ifs <;> simp only [List.length_map, List.length_append] <;> (clear * - s4 a4 l2; omega)

/-- **The typed phases on the viewed pairs** (`specBusA₂`'s: `typedSpecR` at `imgC x`, the doom pulled back to
`candPairs`). -/
noncomputable def specBusT₂ (H : THyp Ti) (x : List UInt8) (N : Pair → Prop) :
    Spec (typedProg Ti (pubX x))
      (fun h ↦ RootShape h ∧
        Doomed candPairs (fun p ↦ GbT Ti H x (vp x p) ∧ (GkS x (vp x p) ∧ N (vp x p))) h)
      (fun a h ↦ Doomed candPairs
        (fun p ↦ (BT x a (vp x p) ∧ N (vp x p)) ∧ (GkS x (vp x p) ∧ N (vp x p))) h ∧ RootShape h)
      εS εS LkSJ :=
  have S0 := typedSpecR Ti lay26 (pubX x) H.hτ H.ok H.maps rfl (H.acc x) H.sc H.layOk H.keys H.width H.fix
    (H.μBus H.hτ) (imgC x)
    (fun p ↦ BndS x p.1 ∧ GkS x p ∧ N p) (L₀ := 37696) (εmax := εS) (T := LkSJ)
    (fun h ↦ 2 ≤ (commits h).length) (imgC_append x) (fun _ ↦ Set.toFinite _) (imgC_ncard_le x) (H.errs H.hτ)
  (S0.frame RootShape (fun _ _ hl hr ↦ Lvm.M3.rootShape_append
      ((cg_typedProg Ti (pubX x)).1.reach_commits hl) hr)).mono
    (fun _ ⟨hr, hDm⟩ ↦ ⟨⟨Lvm.M3.rootShape_two hr, Lvm.M3.rootShape_firstWord hr, doomed_imgC.mpr
      (Doomed.mono hDm fun _ hq ↦ ⟨⟨⟨hq.1, hq.2.1.1⟩, hq.2.2⟩, hq.2.1.2⟩)⟩, hr⟩)
    (fun _ _ hp ↦ ⟨Doomed.mono (doomed_imgC.mp hp.1) fun _ hq ↦ ⟨hq.1.1.1, hq.1.1.2, hq.2.1, hq.1.2⟩, hp.2⟩)
    le_rfl (H.errs H.hτ).lead le_rfl

/-- **O6 for the typed backend in both shapes** (`midSpecR₂`'s proof): `MidSpecR (midT₂ Ti) (Good₂ (GoodT Ti H))
εS εS` by `midSpecOfRel`, with `LvmShape.specKgS₂` unchanged. -/
theorem midSpecR_T₂ (H : THyp Ti) : MidSpecR (midT₂ Ti) (Good₂ (GoodT Ti H)) εS εS := by
  intro x₀ T hT
  have M : MidSpecR (fun _ ↦ typedProg Ti (pubX x₀) >>= fun a ↦
        kgProgS (hdX x₀).s (pubX x₀).n >>= fun k ↦ VerifierProgram.ret (assembleT₂ x₀ a k))
      (fun _ qm qr ↦ GbT Ti H x₀ (vp x₀ (qm, qr)) ∧ GkS x₀ (vp x₀ (qm, qr))) εS εS :=
    midSpecOfRel
      (busP := fun _ ↦ typedProg Ti (pubX x₀))
      (kgP := fun _ ↦ kgProgS (hdX x₀).s (pubX x₀).n)
      (asm := fun _ a k ↦ assembleT₂ x₀ a k) (Lb := εS) (Lk := LkSJ)
      (Gb := fun _ p ↦ GbT Ti H x₀ (vp x₀ p)) (Gk := fun _ p ↦ GkS x₀ (vp x₀ p))
      (B := fun _ a p ↦ BT x₀ a (vp x₀ p)) (Kc := fun k p ↦ KcS k (vp x₀ p))
      (Qa := fun _ ↦ TRet) (Qk := KgRet)
      (fun _ ↦ specBusT₂ H x₀ fun p ↦ ¬ (GbT Ti H x₀ p ∧ GkS x₀ p))
      (fun _ ↦ retOK_typedProg H _)
      (fun _ a T hT ↦ (specKgS₂ x₀
          (fun p ↦ BT x₀ a (vp x₀ p) ∧ ¬ (GbT Ti H x₀ (vp x₀ p) ∧ GkS x₀ (vp x₀ p))) T hT).mono
        (fun _ hd ↦ Doomed.mono hd fun _ hq ↦ ⟨⟨hq.1, hq.2.2⟩, hq.2⟩) (fun _ _ h ↦ h) le_rfl le_rfl
        le_rfl)
      (fun _ ↦ retOK_kgProgS _ _) (fun _ ↦ cg_kgProgS _ _)
      (fun _ a k p ha hk h1 h2 ↦ linkT₂ x₀ a k p ha hk h1 h2)
      (fun _ a k ha hk ↦ sideT₂ x₀ a k ha hk)
  obtain ⟨S⟩ := M x₀ T hT
  have S' : Spec (midT₂ Ti x₀) RootShape (Lvm.ASM.OpenPostR
      (fun _ qm qr ↦ GbT Ti H x₀ (vp x₀ (qm, qr)) ∧ GkS x₀ (vp x₀ (qm, qr))) x₀) εS εS T := by
    unfold midT₂
    exact S
  refine ⟨S'.mono (fun _ h ↦ h) (fun cl h hp ↦ ?_) le_rfl le_rfl le_rfl⟩
  exact (openPostR_congr
    (G := fun _ qm qr ↦ GbT Ti H x₀ (vp x₀ (qm, qr)) ∧ GkS x₀ (vp x₀ (qm, qr)))
    (G' := Good₂ (GoodT Ti H)) fun _ _ ↦ Iff.rfl).mp hp

/-- **The middle phases' shape, typed** (`midShape_midS₂`'s). -/
theorem midShape_T₂ (H : THyp Ti) : MidShape (midT₂ Ti) where
  noCommit _ := (Lvm.M3.NoCG.bind (cg_typedProg _ _) fun _ ↦
    Lvm.M3.NoCG.bind (cg_kgProgS _ _) fun _ ↦ Lvm.M3.cg_ret _).1
  noGrind _ := (Lvm.M3.NoCG.bind (cg_typedProg _ _) fun _ ↦
    Lvm.M3.NoCG.bind (cg_kgProgS _ _) fun _ ↦ Lvm.M3.cg_ret _).2
  recAffine x l cl hl :=
    ((retOK_typedProg H _).bind fun a ha ↦ (retOK_kgProgS _ _).bind fun k hk ↦
      RetOK.ret (sideT₂ x a k ha hk).1 :
      RetOK (fun cl : OpenClaims ↦ ∀ c ∈ cl.1, IsMultiaffine 19 c.1) (midT₂ Ti x)) l cl hl

/-- **The knowledge certificate of the typed backend** (J2C-DES T9's `kcertSJ`, unchanged): from `midSpecR_T₂`,
`midShape_T₂` and an extraction for `Good₂ (GoodT Ti H)` (J2C-C's `extJ` at the typed `NodeSound`, L-D/INT). -/
noncomputable def kcertT (H : THyp Ti) {VS : Lvm.T.SProg} {vk : RecursionFast.Digest}
    (X : ExtJ (midT₂ Ti) (Good₂ (GoodT Ti H)) VS vk) :
    Lvm.FS.KCert (schemeS vk (PSWith (midT₂ Ti))) (RecursionFast.Rel (Lvm.T.accV VS vk)) :=
  kcertSJ (midSpecR_T₂ H) le_rfl (midShape_T₂ H) X

end Lvm.Typed
end

-- ===== from `LvmMPMidT` =====

section
set_option autoImplicit false
namespace Lvm.Typed
open LeanVM.Parameters LeanVM.Protocol LeanVM.Protocol.Compile LeanVM.Protocol.Verifier
open LeanVM.Protocol.Compile.VerifierProgram LeanVM.Protocol.EndToEnd LeanVM.Protocol.EndToEnd.Front
open LeanVM.Protocol.Whir.Sound
open LeanVM.Protocol.EndToEnd.Sound (RetOK)
open Lvm.M3 (lay26)
open Lvm.ASM (OpenClaims Pair GoodRel GoodRelM RootShapeM MidSpecM MidShapeM RelocLaw midM candM candRelM GoodOfM
  MidSpecP midSpecM_of midShapeM_of midSpecOfRelG GkS BndS KcS KgRet LkSJ εS retOK_kgProgS cg_kgProgS)
open Lvm.VEq (kgProgS hdX pubX assembleS KgOut)
open Lvm.NS (colM ksCol ksY2 msgM msgX)
open Lvm.Shape (Good₂ view vp)
open scoped ENNReal NNReal

theorem candRelM_stable (recOf : List UInt8 → Column CMain.nu20 → Column 19) (x : List UInt8) :
    Stable (candRelM recOf x) := fun h₀ l hl ↦ by
  rw [candRelM, candRelM, candM_stable h₀ l hl]

end Lvm.Typed
end

section
set_option autoImplicit false
namespace Lvm.Typed
open LeanVM.Parameters LeanVM.Protocol LeanVM.Protocol.Compile LeanVM.Protocol.Verifier
open LeanVM.Protocol.Compile.VerifierProgram LeanVM.Protocol.EndToEnd LeanVM.Protocol.EndToEnd.Front
open LeanVM.Protocol.Whir.Sound
open LeanVM.Protocol.EndToEnd.Sound (RetOK)
open Lvm.M3 (lay26)
open Lvm.ASM (OpenClaims Pair GoodRel GoodRelM RootShapeM MidSpecM MidShapeM RelocLaw midM candM candRelM GoodOfM
  MidSpecP midSpecM_of midShapeM_of midSpecOfRelG GkS BndS KcS KgRet LkSJ εS retOK_kgProgS cg_kgProgS)
open Lvm.VEq (kgProgS hdX pubX assembleS KgOut)
open Lvm.NS (colM ksCol ksY2 msgM msgX)
open Lvm.Shape (Good₂ view vp)
open scoped ENNReal NNReal

theorem candRelM_ncard_le (recOf : List UInt8 → Column CMain.nu20 → Column 19) (x : List UInt8) (h : List Ev) :
    (candRelM recOf x h).ncard ≤ 124 :=
  (Set.ncard_image_le (Set.toFinite _)).trans (candM_ncard_le h)

/-- The viewed one-root pairs. -/
def imgCM (recOf : List UInt8 → Column CMain.nu20 → Column 19) (x : List UInt8) (h : List Ev) : Set Pair :=
  vp x '' candRelM recOf x h

end Lvm.Typed
end

section
set_option autoImplicit false
namespace Lvm.Typed
open LeanVM.Parameters LeanVM.Protocol LeanVM.Protocol.Compile LeanVM.Protocol.Verifier
open LeanVM.Protocol.Compile.VerifierProgram LeanVM.Protocol.EndToEnd LeanVM.Protocol.EndToEnd.Front
open LeanVM.Protocol.Whir.Sound
open LeanVM.Protocol.EndToEnd.Sound (RetOK)
open Lvm.M3 (lay26)
open Lvm.ASM (OpenClaims Pair GoodRel GoodRelM RootShapeM MidSpecM MidShapeM RelocLaw midM candM candRelM GoodOfM
  MidSpecP midSpecM_of midShapeM_of midSpecOfRelG GkS BndS KcS KgRet LkSJ εS retOK_kgProgS cg_kgProgS)
open Lvm.VEq (kgProgS hdX pubX assembleS KgOut)
open Lvm.NS (colM ksCol ksY2 msgM msgX)
open Lvm.Shape (Good₂ view vp)
open scoped ENNReal NNReal
section Img
variable (recOf : List UInt8 → Column CMain.nu20 → Column 19) (x : List UInt8)

theorem imgCM_append (h₀ l : List Ev) (h1 : 1 ≤ (commits h₀).length) :
    imgCM recOf x (h₀ ++ l) = imgCM recOf x h₀ := by
  rw [imgCM, imgCM, candRelM, candRelM, candM_append h₀ l h1]

theorem imgCM_ncard_le (h : List Ev) : (imgCM recOf x h).ncard ≤ 37696 :=
  (Set.ncard_image_le (Set.toFinite _)).trans ((candRelM_ncard_le recOf x h).trans (by norm_num))

end Img
end Lvm.Typed
end

section
set_option autoImplicit false
namespace Lvm.Typed
open LeanVM.Parameters LeanVM.Protocol LeanVM.Protocol.Compile LeanVM.Protocol.Verifier
open LeanVM.Protocol.Compile.VerifierProgram LeanVM.Protocol.EndToEnd LeanVM.Protocol.EndToEnd.Front
open LeanVM.Protocol.Whir.Sound
open LeanVM.Protocol.EndToEnd.Sound (RetOK)
open Lvm.M3 (lay26)
open Lvm.ASM (OpenClaims Pair GoodRel GoodRelM RootShapeM MidSpecM MidShapeM RelocLaw midM candM candRelM GoodOfM
  MidSpecP midSpecM_of midShapeM_of midSpecOfRelG GkS BndS KcS KgRet LkSJ εS retOK_kgProgS cg_kgProgS)
open Lvm.VEq (kgProgS hdX pubX assembleS KgOut)
open Lvm.NS (colM ksCol ksY2 msgM msgX)
open Lvm.Shape (Good₂ view vp)
open scoped ENNReal NNReal
section Img
variable (recOf : List UInt8 → Column CMain.nu20 → Column 19) (x : List UInt8)
variable {recOf x}

theorem doomed_imgCM {A : Pair → Prop} {h : List Ev} :
    Doomed (imgCM recOf x) A h ↔ Doomed (candRelM recOf x) (fun p ↦ A (vp x p)) h :=
  ⟨fun hd p hp ↦ hd _ ⟨p, hp, rfl⟩, fun hd _ ⟨p, hp, e⟩ ↦ e ▸ hd p hp⟩

end Img
end Lvm.Typed
end

section
set_option autoImplicit false
namespace Lvm.Typed
open LeanVM.Parameters LeanVM.Protocol LeanVM.Protocol.Compile LeanVM.Protocol.Verifier
open LeanVM.Protocol.Compile.VerifierProgram LeanVM.Protocol.EndToEnd LeanVM.Protocol.EndToEnd.Front
open LeanVM.Protocol.Whir.Sound
open LeanVM.Protocol.EndToEnd.Sound (RetOK)
open Lvm.M3 (lay26)
open Lvm.ASM (OpenClaims Pair GoodRel GoodRelM RootShapeM MidSpecM MidShapeM RelocLaw midM candM candRelM GoodOfM
  MidSpecP midSpecM_of midShapeM_of midSpecOfRelG GkS BndS KcS KgRet LkSJ εS retOK_kgProgS cg_kgProgS)
open Lvm.VEq (kgProgS hdX pubX assembleS KgOut)
open Lvm.NS (colM ksCol ksY2 msgM msgX)
open Lvm.Shape (Good₂ view vp)
open scoped ENNReal NNReal
variable {Ti : TInst}

/-- **The typed phases on the viewed one-root pairs** (`specBusT₂` with `imgCM`, `RootShapeM`). -/
noncomputable def specBusTM (H : THyp Ti) (recOf : List UInt8 → Column CMain.nu20 → Column 19)
    (x : List UInt8) (N : Pair → Prop) :
    Spec (typedProg Ti (pubX x))
      (fun h ↦ RootShapeM h ∧
        Doomed (candRelM recOf x) (fun p ↦ GbT Ti H x (vp x p) ∧ (GkS x (vp x p) ∧ N (vp x p))) h)
      (fun a h ↦ Doomed (candRelM recOf x)
        (fun p ↦ (BT x a (vp x p) ∧ N (vp x p)) ∧ (GkS x (vp x p) ∧ N (vp x p))) h ∧ RootShapeM h)
      εS εS LkSJ :=
  have S0 := typedSpecR Ti lay26 (pubX x) H.hτ H.ok H.maps rfl (H.acc x) H.sc H.layOk H.keys H.width H.fix
    (H.μBus H.hτ) (imgCM recOf x)
    (fun p ↦ BndS x p.1 ∧ GkS x p ∧ N p) (L₀ := 37696) (εmax := εS) (T := LkSJ)
    (fun h ↦ 1 ≤ (commits h).length) (imgCM_append recOf x) (fun _ ↦ Set.toFinite _)
    (imgCM_ncard_le recOf x) (H.errs H.hτ)
  (S0.frame RootShapeM (fun _ _ hl hr ↦ rootShapeM_append
      ((cg_typedProg Ti (pubX x)).1.reach_commits hl) hr)).mono
    (fun _ ⟨hr, hDm⟩ ↦ ⟨⟨rootShapeM_one hr, rootShapeM_firstWord hr, doomed_imgCM.mpr
      (Doomed.mono hDm fun _ hq ↦ ⟨⟨⟨hq.1, hq.2.1.1⟩, hq.2.2⟩, hq.2.1.2⟩)⟩, hr⟩)
    (fun _ _ hp ↦ ⟨Doomed.mono (doomed_imgCM.mp hp.1) fun _ hq ↦ ⟨hq.1.1.1, hq.1.1.2, hq.2.1, hq.1.2⟩, hp.2⟩)
    le_rfl (H.errs H.hτ).lead le_rfl

/-- **Phases 4–7 on the viewed one-root pairs** (`LvmShape.specKgS₂` with `candRelM`). -/
noncomputable def specKgSM (recOf : List UInt8 → Column CMain.nu20 → Column 19) (x : List UInt8)
    (R : Pair → Prop) (T : ℝ≥0∞) (hT : T ≤ εS) :
    Spec (kgProgS (hdX x).s (pubX x).n) (Doomed (candRelM recOf x) (fun p ↦ GkS x (vp x p) ∧ R p))
      (fun k h ↦ Doomed (candRelM recOf x) (fun p ↦ KcS k (vp x p) ∧ R p) h) εS LkSJ T :=
  have e := Lvm.ASM.kg_errsJ2
  have s := Lvm.ASM.kg_struct
  (Lvm.ASM.kgSpecS (C := candRelM recOf x) (L₀ := 37696) (εmax := εS) (T := T) (candRelM_stable recOf x)
    (fun h ↦ (candRelM_ncard_le recOf x h).trans (by norm_num))
    (hdX x).s (pubX x).n 9 9 ksY2 (by norm_num) (Lvm.contRows Lvm.P20) s.2.2.1 s.2.2.2
    (fun q ↦ colM (vp x q).1) (fun q ↦ colM (vp x q).1) (fun q ↦ ksCol (vp x q).1) (fun q ↦ msgM q.2)
    (fun q ↦ msgX (vp x q).1) R e.1 e.2.1 e.2.2.1 e.2.2.2.1 hT).mono
    (fun _ hd ↦ Doomed.mono hd fun _ ⟨ht, hk, hb⟩ ↦
      ⟨⟨by rw [Lvm.ASM.pubX_n x] at ht; exact ht, hk⟩, hb⟩)
    (fun _ _ hp ↦ Doomed.mono hp.2 fun _ hq ↦ ⟨hq.1.1, hq.1.2, hq.2⟩) le_rfl le_rfl le_rfl

/-- **The pair form of the typed middle phases at the one-root pairs** (`midSpecR_T₂`'s proof through
`midSpecOfRelG`; `linkT₂`, `sideT₂`, `retOK_typedProg` unchanged). -/
theorem midSpecP_T₂ (H : THyp Ti) (recOf : List UInt8 → Column CMain.nu20 → Column 19) :
    MidSpecP (midT₂ Ti) (candRelM recOf) RootShapeM (Good₂ (GoodT Ti H)) εS εS :=
  midSpecOfRelG (busP := fun x ↦ typedProg Ti (pubX x)) (kgP := fun x ↦ kgProgS (hdX x).s (pubX x).n)
    (asm := fun x a k ↦ assembleT₂ x a k) (Lb := εS) (Lk := LkSJ)
    (Gb := fun x p ↦ GbT Ti H x (vp x p)) (Gk := fun x p ↦ GkS x (vp x p))
    (B := fun x a p ↦ BT x a (vp x p)) (Kc := fun x k p ↦ KcS k (vp x p))
    (Qa := fun _ ↦ TRet) (Qk := fun _ ↦ KgRet) (C := candRelM recOf) (Sh := RootShapeM)
    (fun _ _ hl hr ↦ rootShapeM_append hl hr)
    (fun x ↦ specBusTM H recOf x fun p ↦ ¬ (GbT Ti H x p ∧ GkS x p))
    (fun _ ↦ retOK_typedProg H _)
    (fun x a T hT ↦ (specKgSM recOf x
        (fun p ↦ BT x a (vp x p) ∧ ¬ (GbT Ti H x (vp x p) ∧ GkS x (vp x p))) T hT).mono
      (fun _ hd ↦ Doomed.mono hd fun _ hq ↦ ⟨⟨hq.1, hq.2.2⟩, hq.2⟩) (fun _ _ h ↦ h) le_rfl le_rfl le_rfl)
    (fun _ ↦ retOK_kgProgS _ _) (fun _ ↦ cg_kgProgS _ _)
    (fun x a k p ha hk h1 h2 ↦ linkT₂ x a k p ha hk h1 h2)
    (fun x a k ha hk ↦ sideT₂ x a k ha hk)

/-- The typed phases return at most `2^39 + 4` claims (each commitment: the mini-bus's `≤ 2^38` and two). -/
theorem retOK_typedProg_len (H : THyp Ti) (pub : Lvm.Pub) :
    RetOK (fun a : OpenClaims ↦ a.1.length + a.2.length ≤ 2 ^ 39 + 4) (typedProg Ti pub) := by
  rw [typedProg_eq]
  refine RetOK.bind_true fun z ↦ RetOK.bind_true fun w ↦ RetOK.bind_true fun r ↦ RetOK.bind_true fun _ ↦ ?_
  refine (Lvm.ASM.retOK_lbusTableCheckProg Ti.mbT miniDepth).bind fun cl hcl ↦ RetOK.ret ?_
  have hl1 := length_miniClaims Ti .crec cl
  have hl2 := length_miniClaims Ti .main cl
  have hcl' : cl.length ≤ 2 ^ 38 := hcl.2.trans H.widths
  simp only [typedClaims, List.length_cons]
  norm_num at hcl' ⊢
  (clear * - hl1 hl2 hcl'; omega)

/-- V_S phases 4–7 add at most `41` claims (`sideT₂`'s count). -/
theorem length_assembleT₂ (x : List UInt8) (a : OpenClaims) (k : KgOut) (hk : KgRet k) :
    (assembleT₂ x a k).2.length + (assembleT₂ x a k).1.length ≤ a.1.length + a.2.length + 41 := by
  have hk1 : (k.2.1.2.2.1.1).length ≤ 1 := hk.2.2.2.2.1
  have l1 : (assembleS [] (pubX x) [] k).1.length ≤ 1 := by
    rw [Lvm.ASM.assembleS_eq, List.length_map]
    simpa using Lvm.ASM.length_crec_le [] (pubX x) [] k
  have l2 : (assembleS [] (pubX x) [] k).2.length ≤ 40 := by
    rw [Lvm.ASM.assembleS_eq, List.length_map]
    have h := Lvm.ASM.length_claimsS [] (pubX x) [] k
    have h0 : (Lvm.VEq.tableClaimsE [] []).length = 0 := rfl
    rw [Lvm.ASM.length_pubX_h, h0] at h
    exact (List.length_filter_le _ _).trans (by (clear * - hk1 h; omega))
  have e2 : (assembleT₂ x a k).2.length = (a.2 ++ (assembleS [] (pubX x) [] k).2).length := by
    simp only [assembleT₂, Lvm.Shape.onStackZs]
    split_ifs <;> simp only [List.length_map]
  rw [e2]
  simp only [assembleT₂, List.length_append]
  (clear * - l1 l2; omega)

/-- **At most `2^40` claims in all** (`OpenPostM`'s bound after relocation). -/
theorem retOK_midT₂_len (H : THyp Ti) (x : List UInt8) :
    RetOK (fun cl : OpenClaims ↦ cl.2.length + cl.1.length ≤ 2 ^ 40) (midT₂ Ti x) :=
  ((retOK_typedProg_len H _).bind fun a ha ↦ (retOK_kgProgS _ _).bind fun k hk ↦
      RetOK.ret ((length_assembleT₂ x a k hk).trans (by norm_num at ha ⊢; (clear * - ha; omega))) :
    RetOK (fun cl : OpenClaims ↦ cl.2.length + cl.1.length ≤ 2 ^ 40) (midT₂ Ti x))

end Lvm.Typed
end

section
set_option autoImplicit false
namespace Lvm.Typed
open LeanVM.Parameters LeanVM.Protocol LeanVM.Protocol.Compile LeanVM.Protocol.Verifier
open LeanVM.Protocol.Compile.VerifierProgram LeanVM.Protocol.EndToEnd LeanVM.Protocol.EndToEnd.Front
open LeanVM.Protocol.Whir.Sound
open LeanVM.Protocol.EndToEnd.Sound (RetOK)
open Lvm.M3 (lay26)
open Lvm.ASM (OpenClaims Pair GoodRel GoodRelM RootShapeM MidSpecM MidShapeM RelocLaw midM candM candRelM GoodOfM
  MidSpecP midSpecM_of midShapeM_of midSpecOfRelG GkS BndS KcS KgRet LkSJ εS retOK_kgProgS cg_kgProgS)
open Lvm.VEq (kgProgS hdX pubX assembleS KgOut)
open Lvm.NS (colM ksCol ksY2 msgM msgX)
open Lvm.Shape (Good₂ view vp)
open scoped ENNReal NNReal
variable {Ti : TInst}

/-- **The good relation at M′**: the typed good pair (both shapes) at `(q, recOf x q)`. -/
def GoodTM (recOf : List UInt8 → Column CMain.nu20 → Column 19) (Ti : TInst) (H : THyp Ti) : GoodRelM :=
  GoodOfM recOf (Good₂ (GoodT Ti H))

/-- **O6 at M′ for the typed backend**: `MidSpecM (midM reloc (midT₂ Ti)) (GoodTM recOf Ti H) εS εS`, given the
relocation's laws. -/
theorem midSpecM_T₂ (H : THyp Ti) {recOf : List UInt8 → Column CMain.nu20 → Column 19}
    {reloc : List UInt8 → LeanVM.Protocol.Verifier.StackClaim → LeanVM.Protocol.Verifier.StackClaim}
    (hρ : RelocLaw recOf reloc) : MidSpecM (midM reloc (midT₂ Ti)) (GoodTM recOf Ti H) εS εS :=
  midSpecM_of hρ (midSpecP_T₂ H recOf) (retOK_midT₂_len H)

/-- **The middle phases' shape at M′** (no hypothesis on the relocation). -/
theorem midShapeM_T₂ (Ti : TInst)
    (reloc : List UInt8 → LeanVM.Protocol.Verifier.StackClaim → LeanVM.Protocol.Verifier.StackClaim) :
    MidShapeM (midM reloc (midT₂ Ti)) :=
  midShapeM_of fun _ ↦ Lvm.M3.NoCG.bind (cg_typedProg _ _) fun _ ↦
    Lvm.M3.NoCG.bind (cg_kgProgS _ _) fun _ ↦ Lvm.M3.cg_ret _

/-- **The knowledge certificate at M′ for the typed backend** (`kcertSM`): from the relocation's laws and an
extraction for `GoodTM recOf Ti H` (R11-C's `extJM` at the lead's `NodeSoundM`). -/
noncomputable def kcertTM (H : THyp Ti) {recOf : List UInt8 → Column CMain.nu20 → Column 19}
    {reloc : List UInt8 → LeanVM.Protocol.Verifier.StackClaim → LeanVM.Protocol.Verifier.StackClaim}
    (hρ : RelocLaw recOf reloc) {VS : Lvm.T.SProg} {vk : RecursionFast.Digest}
    (X : Lvm.ASM.ExtJM (midM reloc (midT₂ Ti)) (GoodTM recOf Ti H) VS vk) :
    Lvm.FS.KCert (Lvm.ASM.schemeS vk (Lvm.ASM.PSWithM (midM reloc (midT₂ Ti))))
      (RecursionFast.Rel (Lvm.T.accV VS vk)) :=
  Lvm.ASM.kcertSM (midSpecM_T₂ H hρ) le_rfl (midShapeM_T₂ Ti reloc) X

end Lvm.Typed
end
