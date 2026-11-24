-- New for lvm6 (WP TWO): the fast twin of W1's deployed opening `whirP`, part 1: the twins of the opening's
-- primitive steps at `E2` (the commitment, the openings, the groups `grp6`, the reads, the bind), the positions, and
-- the word-field forms of the `K` evaluations the opening makes (the subspace polynomials by their recurrence, the
-- novel basis, the high part, the final polynomial, the lanes of an opened row and their fold).
import Lvm6VTw
import Lvm6WhirProg

/-!
# The opening's steps and evaluations in the word field (TWO, part 1)

* `fSep`, `fGrp g k`, `tw_readF`, `tw_readFs`: the bind, a group (`grp6`: nonce, ground draw with its proof of
  work, `k` draws), the reads, at `chalE2`. `fCommit`, `tw_commit`; `RowsF` (the driver's opening record),
  `RowsF.dec`, `fQuery`, `twin_query`.
* `posNF`, `posListF`, `posE2_val`: the positions of a level from the group's values.
* `vanL` (the recurrence `W_{i+1} = W_i² + W_i(e_i)·W_i`), `rootsUpTo`, `nwF a = [Ŵ_0(a), …, Ŵ_19(a)]`
  (`nwF_spec`), `novN` (`novN_eq`: the novel basis), `highEvalF` (`highEval_eq`), `fpolyEvalF` (`fpolyEval_eq`).
* `leafWordF`, `rowWordF`, `laneF` (`laneVal_eq`), `foldRowF` (`foldRowE_eq`), `valAtF` (`valsE_eq`, `fvE_eq`).
-/

set_option autoImplicit false

namespace Lvm6.V

open RecursionFast LeanVM.Parameters Lvm.FS Lvm.Replay Lvm Lvm.E2V
open LeanVM.Protocol.Compile hiding Proof Bytes Word
open LeanVM.Protocol.Whir (vanishingAt normVanishingAt basisVec novelAt bitsToNat)

/-! ## The bind, groups, reads -/

/-- Fast `e2Sep`. -/
def fSep : VF Unit := VF.bind fSample fun _ => VF.pure ()

theorem tw_sep : TwinF id Whir.chalE2.sep fSep :=
  tw_sample (f := fun _ => pure ()) fun _ => tw_pure rfl

/-- One further draw (`D(1)`), lanes 0–1. -/
def fDraw1 : VF FE2 := VF.bind fSample fun a => VF.pure (fe2OfAns a)

theorem tw_draw1 :
    TwinF FE2.toE2 (VerifierProgram.sampleChallenge >>= fun c => pure (e2OfE c)) fDraw1 :=
  tw_sample fun a => tw_pure (e2OfE_chal a).symm

/-- Fast `drawsE2 n`. -/
def fDraws : ℕ → VF (List FE2)
  | 0 => VF.pure []
  | n + 1 => VF.bind fDraw1 fun x => VF.bind (fDraws n) fun xs => VF.pure (x :: xs)

theorem tw_draws : ∀ n, TwinF (List.map FE2.toE2) (drawsE2 n) (fDraws n)
  | 0 => tw_pure rfl
  | n + 1 => tw_bind (f := fun x => drawsE2 n >>= fun xs => pure (x :: xs)) tw_draw1 fun _ =>
      tw_bind (tw_draws n) fun _ => tw_pure rfl

/-- Fast `grp6 g k`: the nonce, the ground draw and its proof of work, `k` draws. -/
def fGrp (g k : ℕ) : VF (List FE2) :=
  VF.bind (fE2Sample g) fun c => VF.bind (fDraws k) fun cs => VF.pure (c :: cs)

theorem tw_grp (g k : ℕ) : TwinF (List.map FE2.toE2) (Whir.chalE2.grp g k) (fGrp g k) := by
  show TwinF _ (grp6 g k) _
  rw [grp6_eq]
  exact tw_bind (f := fun c => drawsE2 k >>= fun cs => pure (c :: cs)) (tw_e2Sample g) fun _ =>
    tw_bind (tw_draws k) fun _ => tw_pure rfl

theorem tw_readF : TwinF FE2.toE2 (Whir.readF Whir.chalE2) fReadF := tw_e2Read

theorem tw_readFs : ∀ n, TwinF (List.map FE2.toE2) (Whir.readFs Whir.chalE2 n) (fE2Reads n)
  | 0 => tw_pure rfl
  | n + 1 => tw_bind (f := fun x => Whir.readFs Whir.chalE2 n >>= fun xs => pure (x :: xs)) tw_readF
      fun _ => tw_bind (tw_readFs n) fun _ => tw_pure rfl

/-! ## The commitment and the openings -/

/-- Fast `readCommitment ht w`: the driver's cap of that shape. -/
def fCommit (ht w : ℕ) : VF Unit := fun _ tr =>
  match tr with
  | .cap ht' w' :: tr' => if ht = ht' ∧ w = w' then some ((), tr') else none
  | _ => none

theorem tw_commit (ht w : ℕ) : TwinF id (VerifierProgram.readCommitment ht w) (fCommit ht w) := by
  intro π tr
  rcases tr with _ | ⟨v, tr⟩
  · exact Option.Rel.none
  · cases v with
    | cap ht' w' =>
      show Option.Rel _ (if ht = ht' ∧ w = w' then some ((), tr) else none)
        (if ht = ht' ∧ w = w' then replayP (VerifierProgram.ret ()) (tr.map (NV.val π)) else none)
      by_cases hc : ht = ht' ∧ w = w'
      · rw [if_pos hc, if_pos hc]; exact Option.Rel.some ⟨rfl, rfl⟩
      · rw [if_neg hc, if_neg hc]; exact Option.Rel.none
    | rd _ _ => exact Option.Rel.none
    | draw _ => exact Option.Rel.none
    | rows _ _ _ _ _ _ => exact Option.Rel.none

/-- The driver's record of an opening: row width, occupied words, leaf bytes, leaf offsets. -/
structure RowsF where
  wd : ℕ
  oc : ℕ
  lb : ℕ
  os : List ℕ

/-- The opened rows the record stands for (`NV.val`). -/
def RowsF.dec (π : ByteArray) (r : RowsF) : List (List K) :=
  r.os.map fun o => padRowOf kOfBytes r.wd r.oc (((bl π).drop o).take r.lb)

/-- Fast `queryOpenings i ps`: the driver's record at these positions. -/
def fQuery (i : ℕ) (ps : List ℕ) : VF RowsF := fun _ tr =>
  match tr with
  | .rows i' ps' wd oc lb os :: tr' => if i = i' ∧ ps = ps' then some (⟨wd, oc, lb, os⟩, tr') else none
  | _ => none

theorem twin_query (i : ℕ) (ps : List ℕ) :
    Twin (fun π (b : RowsF) a => b.dec π = a) (VerifierProgram.queryOpenings i ps) (fQuery i ps) := by
  intro π tr
  rcases tr with _ | ⟨v, tr⟩
  · exact Option.Rel.none
  · cases v with
    | rows i' ps' wd oc lb os =>
      show Option.Rel _ (if i = i' ∧ ps = ps' then some ((⟨wd, oc, lb, os⟩ : RowsF), tr) else none)
        (if i = i' ∧ ps = ps' then replayP (VerifierProgram.ret
          (os.map fun o => padRowOf kOfBytes wd oc (((bl π).drop o).take lb))) (tr.map (NV.val π)) else none)
      by_cases hc : i = i' ∧ ps = ps'
      · rw [if_pos hc, if_pos hc]; exact Option.Rel.some ⟨rfl, rfl⟩
      · rw [if_neg hc, if_neg hc]; exact Option.Rel.none
    | rd _ _ => exact Option.Rel.none
    | draw _ => exact Option.Rel.none
    | cap _ _ => exact Option.Rel.none

/-! ## Positions -/

/-- A value's lanes 0–1 as a number. -/
@[inline] def e2NatF (a : FE2) : ℕ := a.re.val.toNat + 2 ^ 64 * a.im.val.toNat

theorem e2Nat_toE2 (a : FE2) : Whir.e2Nat (FE2.toE2 a) = e2NatF a := rfl

/-- Position `k` of a level: digit `k mod c` (base `2^h`) of the number of draw `k / c`. -/
@[inline] def posNF (h c : ℕ) (qv : List FE2) (k : ℕ) : ℕ :=
  e2NatF (qv.getD (k / c) 0) / (2 ^ h) ^ (k % c) % 2 ^ h

/-- The `t` positions of a level. -/
def posListF (h c t : ℕ) (qv : List FE2) : List ℕ := List.ofFn fun k : Fin t => posNF h c qv k

theorem posE2_val (h c d t : ℕ) (hc : 0 < c) (ht : t ≤ d * c) (qv : List FE2) (k : Fin t) :
    ((Whir.posE2 h c d t hc ht (fun i => (qv.map FE2.toE2).getD i 0) k : Fin (2 ^ h)) : ℕ) =
      posNF h c qv k := by
  show Whir.e2Nat ((qv.map FE2.toE2).getD ((k : ℕ) / c) 0) / (2 ^ h) ^ ((k : ℕ) % c) % 2 ^ h = _
  rw [← toE2_getD, e2Nat_toE2]
  rfl

/-! ## Subspace polynomials, the novel basis -/

/-- The `K` word of a number. -/
@[inline] def kOfNat (n : ℕ) : FK := ⟨n.toUInt64⟩

theorem toBF64_kOfNat (n : ℕ) : FK.toBF64 (kOfNat n) = K.ofBits n := rfl

/-- `W_{i+1}(a) = W_i(a)² + W_i(e_i)·W_i(a)`. -/
@[inline] def vStep (r w : FK) : FK := w * w + r * w

/-- `[W_i(a), …, W_{i+n}(a)]` from `W_i(a)` and the roots `W_{i+j}(e_{i+j})`, `j < n`. -/
def vanL : List FK → FK → List FK
  | [], w => [w]
  | r :: rs, w => w :: vanL rs (vStep r w)

theorem vanL_length : ∀ (rs : List FK) (w : FK), (vanL rs w).length = rs.length + 1
  | [], _ => rfl
  | _ :: rs, _ => by simp only [vanL, List.length_cons, vanL_length rs]

theorem vanishingAt_zero' (a : K) : vanishingAt 0 a = a := by simp [vanishingAt]

theorem vanL_spec (a : K) : ∀ (rs : List FK) (i : ℕ) (w : FK),
    (∀ j, j < rs.length → FK.toBF64 (rs.getD j 0) = vanishingAt (i + j) (basisVec (i + j))) →
    FK.toBF64 w = vanishingAt i a →
    ∀ j, j ≤ rs.length → FK.toBF64 ((vanL rs w).getD j 0) = vanishingAt (i + j) a
  | [], i, w, _, hw, j, hj => by
    obtain rfl : j = 0 := by simpa using hj
    exact hw
  | r :: rs, i, w, hr, hw, j, hj => by
    cases j with
    | zero => exact hw
    | succ j =>
      have h0 : FK.toBF64 r = vanishingAt i (basisVec i) := by
        simpa using hr 0 (by simp)
      have hstep : FK.toBF64 (vStep r w) = vanishingAt (i + 1) a := by
        rw [vStep, FK.toBF64_add, FK.toBF64_mul, FK.toBF64_mul, hw, h0, LeanVM.Protocol.Whir.vanishingAt_succ]
        ring
      have hr' : ∀ j', j' < rs.length →
          FK.toBF64 (rs.getD j' 0) = vanishingAt (i + 1 + j') (basisVec (i + 1 + j')) := by
        intro j' hj'
        have := hr (j' + 1) (by simp; omega)
        rw [List.getD_cons_succ, show i + (j' + 1) = i + 1 + j' by omega] at this
        exact this
      have := vanL_spec a rs (i + 1) (vStep r w) hr' hstep j (by simp at hj; omega)
      rw [show i + (j + 1) = i + 1 + j by omega]
      exact this

/-- `e_n = K(2^n)`. -/
@[inline] def eF (n : ℕ) : FK := kOfNat (2 ^ n)

/-- The roots `W_i(e_i)`, `i < n`. -/
def rootsUpTo : ℕ → List FK
  | 0 => []
  | n + 1 => rootsUpTo n ++ [(vanL (rootsUpTo n) (eF n)).getD n 0]

theorem rootsUpTo_spec : ∀ n, (rootsUpTo n).length = n ∧
    ∀ j, j < n → FK.toBF64 ((rootsUpTo n).getD j 0) = vanishingAt j (basisVec j)
  | 0 => ⟨rfl, fun _ hj => absurd hj (Nat.not_lt_zero _)⟩
  | n + 1 => by
    obtain ⟨hl, hr⟩ := rootsUpTo_spec n
    refine ⟨by simp [rootsUpTo, hl], fun j hj => ?_⟩
    simp only [rootsUpTo, List.getD_eq_getElem?_getD, List.getElem?_append, hl]
    by_cases hjn : j < n
    · rw [if_pos hjn]
      have := hr j hjn
      rwa [List.getD_eq_getElem?_getD] at this
    · have hj' : j = n := by omega
      subst hj'
      rw [if_neg (lt_irrefl j), Nat.sub_self]
      have := vanL_spec (basisVec j) (rootsUpTo j) 0 (eF j)
        (fun j' hj' => by rw [Nat.zero_add]; exact hr j' (by omega))
        (by rw [vanishingAt_zero']; rfl) j (by omega)
      rw [Nat.zero_add] at this
      simpa using this

/-- The roots `W_i(e_i)`, `i < 20`, and their inverses. -/
def rootsN : List FK := rootsUpTo 20

def invRootsN : List FK := rootsN.map (·⁻¹)

/-- `[Ŵ_0(a), …, Ŵ_19(a)]`, `Ŵ_i = W_i / W_i(e_i)`. -/
def nwF (a : FK) : List FK :=
  let v := vanL rootsN a
  List.ofFn fun i : Fin 20 => v.getD i 0 * invRootsN.getD i 0

theorem nwF_spec (a : FK) (i : ℕ) (hi : i < 20) :
    FK.toBF64 ((nwF a).getD i 0) = normVanishingAt i (FK.toBF64 a) := by
  obtain ⟨hl, hr⟩ := rootsUpTo_spec 20
  have hv := vanL_spec (FK.toBF64 a) rootsN 0 a (fun j hj => by
      rw [Nat.zero_add]; exact hr j (by rw [rootsN, hl] at hj; exact hj))
    (vanishingAt_zero' _).symm i (by rw [rootsN, hl]; omega)
  rw [Nat.zero_add] at hv
  have hinv : invRootsN.getD i 0 = (rootsN.getD i 0)⁻¹ := by
    have hi' : i < rootsN.length := by rw [rootsN, hl]; exact hi
    rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, invRootsN, List.getElem?_map,
      List.getElem?_eq_getElem hi']
    rfl
  have hn : (nwF a).getD i 0 = (vanL rootsN a).getD i 0 * invRootsN.getD i 0 := by
    show (List.ofFn fun i : Fin 20 => (vanL rootsN a).getD i 0 * invRootsN.getD i 0).getD i 0 = _
    rw [List.getD_eq_getElem?_getD, List.getElem?_ofFn, dif_pos hi]
    rfl
  have hr' : FK.toBF64 (rootsN.getD i 0) = vanishingAt i (basisVec i) := hr i hi
  rw [hn, hinv, FK.toBF64_mul, FK.toBF64_inv, hv, hr', normVanishingAt]

/-- `∏_{i<k, bit i of j} W_i` from the table `W`. -/
def novN (W : List FK) (j : ℕ) : ℕ → FK
  | 0 => 1
  | k + 1 => novN W j k * (if j.testBit k then W.getD k 0 else 1)

theorem novN_spec (a : FK) (j : ℕ) : ∀ k, k ≤ 20 →
    FK.toBF64 (novN (nwF a) j k) =
      ∏ i ∈ Finset.range k, (if j.testBit i then normVanishingAt i (FK.toBF64 a) else 1)
  | 0, _ => by simp [novN]
  | k + 1, hk => by
    rw [novN, FK.toBF64_mul, novN_spec a j k (by omega), Finset.prod_range_succ]
    congr 1
    by_cases hb : j.testBit k
    · rw [if_pos hb, if_pos hb]; exact nwF_spec a k (by omega)
    · rw [if_neg hb, if_neg hb, FK.toBF64_one]

/-- **The novel basis at `a`** from the table `nwF a`, for `j < 2^k`, `k ≤ 20`. -/
theorem novN_eq (a : FK) (j k : ℕ) (hk : k ≤ 20) (hj : j < 2 ^ k) :
    FK.toBF64 (novN (nwF a) j k) = novelAt j (FK.toBF64 a) := by
  rw [novN_spec a j k hk, novelAt]
  refine Finset.prod_subset (fun x hx => Finset.mem_range.mpr
    (lt_of_lt_of_le (Finset.mem_range.mp hx) (by omega))) fun i _ hni => ?_
  have hik : k ≤ i := by simpa using hni
  rw [Nat.testBit_lt_two_pow (lt_of_lt_of_le hj (Nat.pow_le_pow_right (by norm_num) hik))]
  rfl

/-! ## Evaluations at a position -/

theorem toE2_ofK' (k : FK) : FE2.toE2 (FE2.ofK k) = algebraMap K E2 (FK.toBF64 k) := by
  apply QuadraticAlgebra.ext <;> rfl

theorem toE2_sub' (a b : FE2) : FE2.toE2 (a - b) = FE2.toE2 a - FE2.toE2 b := map_sub tE a b

theorem toE2_headD' (l : List FE2) : FE2.toE2 (l.headD 0) = (l.map FE2.toE2).headD 0 := map_headD tE l

theorem eval_mapK (p : Polynomial K) (a : K) :
    (p.map (algebraMap K E2)).eval (algebraMap K E2 a) = algebraMap K E2 (p.eval a) := by
  rw [Polynomial.eval_map, Polynomial.eval₂_at_apply]

/-- `Σ_{s<n} f(s)`. -/
def sumR (f : ℕ → FE2) : ℕ → FE2
  | 0 => 0
  | n + 1 => sumR f n + f n

theorem toE2_sumR (f : ℕ → FE2) : ∀ n, FE2.toE2 (sumR f n) = ∑ s ∈ Finset.range n, FE2.toE2 (f s)
  | 0 => rfl
  | n + 1 => by rw [sumR, toE2_add', toE2_sumR f n, Finset.sum_range_succ]

/-- `(Ŵ_κ · Σ_{s<ℓ} hi_s X_s)(a)` from the table `W = nwF a`. -/
def highEvalF (κ ℓ : ℕ) (hi : List FE2) (W : List FK) : FE2 :=
  FE2.ofK (W.getD κ 0) * sumR (fun s => hi.getD s 0 * FE2.ofK (novN W s 3)) ℓ

theorem highEval_eq (κ ℓ : ℕ) (hκ : κ < 20) (hℓ : ℓ ≤ 8) (hi : List FE2) (a : FK) :
    (Whir.highF κ ℓ (hi.map FE2.toE2)).eval (FE2.toE2 (FE2.ofK a)) =
      FE2.toE2 (highEvalF κ ℓ hi (nwF a)) := by
  rw [toE2_ofK', Whir.highF, Polynomial.eval_mul, Polynomial.eval_finsetSum, highEvalF, toE2_mul',
    toE2_ofK', toE2_sumR, Whir.vanNF, eval_mapK, LeanVM.Protocol.Whir.eval_normVanishing, nwF_spec a κ hκ]
  congr 1
  refine Finset.sum_congr rfl fun s hs => ?_
  have hs8 : s < 2 ^ 3 := lt_of_lt_of_le (Finset.mem_range.mp hs) (le_trans hℓ (by norm_num))
  rw [Polynomial.eval_mul, Polynomial.eval_C, toE2_mul', toE2_ofK', ← toE2_getD, eval_mapK,
    LeanVM.Protocol.Whir.eval_novel, novN_eq a s 3 (by norm_num) hs8]

/-- The final polynomial `P_{s[0..2^κ)} + Ŵ_κ·Σ_{j<ℓ} s_{2^κ+j} X_j` at `a`, from the table `W = nwF a`. -/
def fpolyEvalF (κ ℓ : ℕ) (s : List FE2) (W : List FK) : FE2 :=
  sumR (fun j => s.getD j 0 * FE2.ofK (novN W j 3)) (2 ^ κ) + highEvalF κ ℓ (s.drop (2 ^ κ)) W

theorem fpolyEval_eq (κ ℓ : ℕ) (hκ : κ ≤ 3) (hℓ : ℓ ≤ 8) (s : List FE2) (a : FK) :
    (Whir.fpolyE κ ℓ (s.map FE2.toE2) Whir.lane0).eval (FE2.toE2 (FE2.ofK a)) =
      FE2.toE2 (fpolyEvalF κ ℓ s (nwF a)) := by
  show (Whir.msgPolyF κ (fun u => (s.map FE2.toE2).getD (bitsToNat u) 0) +
    Whir.highF κ ℓ ((s.map FE2.toE2).drop (2 ^ κ))).eval _ = _
  rw [Polynomial.eval_add, ← List.map_drop, highEval_eq κ ℓ (by omega) hℓ, fpolyEvalF, toE2_add',
    toE2_sumR]
  congr 1
  have hre : ∀ F : ℕ → E2, ∑ u : Fin κ → Bool, F (bitsToNat u) = ∑ j ∈ Finset.range (2 ^ κ), F j := by
    intro F
    calc ∑ u : Fin κ → Bool, F (bitsToNat u) = ∑ j : Fin (2 ^ κ), F j :=
          Fintype.sum_equiv (LeanVM.Protocol.Whir.bitsEquiv κ) _ _
            (fun u => by rw [LeanVM.Protocol.Whir.bitsEquiv_val])
      _ = _ := Fin.sum_univ_eq_sum_range F _
  show (∑ u : Fin κ → Bool, (s.map FE2.toE2).getD (bitsToNat u) 0 • Whir.novelF (F := E2) (bitsToNat u)).eval _ = _
  rw [Polynomial.eval_finsetSum]
  simp only [Polynomial.eval_smul, smul_eq_mul]
  rw [hre (fun j => (s.map FE2.toE2).getD j 0 * (Whir.novelF (F := E2) j).eval (FE2.toE2 (FE2.ofK a)))]
  refine Finset.sum_congr rfl fun j hj => ?_
  have hj8 : j < 2 ^ 3 :=
    lt_of_lt_of_le (Finset.mem_range.mp hj) (Nat.pow_le_pow_right (by norm_num) hκ)
  rw [toE2_mul', toE2_ofK', ← toE2_getD, toE2_ofK', eval_mapK, LeanVM.Protocol.Whir.eval_novel,
    novN_eq a j 3 (by norm_num) hj8]

/-! ## Lanes of an opened row -/

/-- Word `i` of a leaf of `lb` bytes at `o`. -/
@[inline] def leafWordF (π : ByteArray) (o lb i : ℕ) : FK :=
  if 8 * i + 8 ≤ lb then kAt π (o + 8 * i)
  else FK.ofBF64 (kOfBytes (((((bl π).drop o).take lb).drop (8 * i)).take 8))

theorem toBF64_leafWordF (π : ByteArray) (o lb i : ℕ) :
    FK.toBF64 (leafWordF π o lb i) = kOfBytes (((((bl π).drop o).take lb).drop (8 * i)).take 8) := by
  unfold leafWordF
  split
  · refine Lvm.VEq.toBF64_kAt_of π (o + 8 * i) _ fun j hj => ?_
    rw [get!_bl, List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, List.getElem?_take, if_pos hj,
      List.getElem?_drop, List.getElem?_take, if_pos (by omega), List.getElem?_drop, Nat.add_assoc]
  · rfl

/-- Word `j` of the padded row (`padRowOf`) of the leaf at `o`. -/
@[inline] def rowWordF (π : ByteArray) (r : RowsF) (o j : ℕ) : FK :=
  if j < r.wd - min r.oc r.wd then 0
  else if j - (r.wd - min r.oc r.wd) < min r.oc r.wd then leafWordF π o r.lb (j - (r.wd - min r.oc r.wd))
  else 0

theorem toBF64_rowWordF (π : ByteArray) (r : RowsF) (o j : ℕ) :
    FK.toBF64 (rowWordF π r o j) = (padRowOf kOfBytes r.wd r.oc (((bl π).drop o).take r.lb)).getD j 0 := by
  simp only [rowWordF, padRowOf, rowOf, List.getD_eq_getElem?_getD, List.getElem?_append,
    List.length_replicate, List.getElem?_replicate, List.getElem?_map]
  by_cases h1 : j < r.wd - min r.oc r.wd
  · simp [h1]
  · by_cases h2 : j - (r.wd - min r.oc r.wd) < min r.oc r.wd
    · simp [h1, h2, List.getElem?_range h2, toBF64_leafWordF]
    · have h3 : (List.range (min r.oc r.wd))[j - (r.wd - min r.oc r.wd)]? = none :=
        List.getElem?_eq_none (by simp; omega)
      simp [h1, h2, h3]

/-- Lane `s` of the opened row at `oo` (`none`: the empty row): level 0 reads word `63 − s`, later levels
the `E2` value of words `2s, 2s + 1`. -/
@[inline] def laneF (z : Bool) (π : ByteArray) (r : RowsF) (oo : Option ℕ) (s : ℕ) : FE2 :=
  match oo with
  | none => 0
  | some o => if z then FE2.ofK (rowWordF π r o (63 - s))
      else ⟨rowWordF π r o (2 * s), rowWordF π r o (2 * s + 1)⟩

theorem laneVal_eq (z : Bool) (π : ByteArray) (r : RowsF) (k s : ℕ) :
    Whir.laneVal z ((r.dec π).getD k []) s = FE2.toE2 (laneF z π r r.os[k]? s) := by
  rcases h : r.os[k]? with _ | o
  · have hrow : (r.dec π).getD k [] = [] := by
      simp [RowsF.dec, List.getD_eq_getElem?_getD, List.getElem?_map, h]
    rw [hrow]
    cases z
    · exact QuadraticAlgebra.ext rfl rfl
    · show algebraMap K E2 (([] : List K).getD (63 - s) 0) = FE2.toE2 0
      rw [List.getD_nil, map_zero]
      rfl
  · have hrow : (r.dec π).getD k [] = padRowOf kOfBytes r.wd r.oc (((bl π).drop o).take r.lb) := by
      simp [RowsF.dec, List.getD_eq_getElem?_getD, List.getElem?_map, h]
    rw [hrow]
    cases z
    · exact QuadraticAlgebra.ext (toBF64_rowWordF π r o (2 * s)).symm (toBF64_rowWordF π r o (2 * s + 1)).symm
    · show algebraMap K E2 _ = FE2.toE2 (FE2.ofK _)
      rw [toE2_ofK', toBF64_rowWordF]

/-! ## The fold of a row -/

/-- A fold round in the word field. -/
structure RndF where
  u₀ : FE2
  w : FE2
  c₀ : FE2
  c₁ : FE2
  α : FE2
  β : FE2

instance : Inhabited RndF := ⟨⟨0, 0, 0, 0, 0, 0⟩⟩

/-- Its value in `E2`. -/
def RndF.dec (r : RndF) : Whir.Rnd E2 :=
  ⟨FE2.toE2 r.u₀, FE2.toE2 r.w, FE2.toE2 r.c₀, FE2.toE2 r.c₁, FE2.toE2 r.α, FE2.toE2 r.β⟩

theorem bitsToNat_cons {n : ℕ} (b : Bool) (u : Fin n → Bool) :
    bitsToNat (Fin.cons b u : Fin (n + 1) → Bool) = b.toNat + 2 * bitsToNat u := by
  simp only [bitsToNat, Fin.sum_univ_succ, Fin.cons_zero, Fin.cons_succ, Fin.val_zero, pow_zero, mul_one,
    Fin.val_succ, Finset.mul_sum]
  congr 1
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [pow_succ]
  ring

theorem bitsToNat_zero (u : Fin 0 → Bool) : bitsToNat u = 0 := by simp [bitsToNat]

/-- The lanes `L` (by lane index) folded by `j` rounds at the point `x`. -/
def foldRowF (x : FE2) : ℕ → List RndF → (ℕ → FE2) → (ℕ → FE2)
  | 0, _, L => L
  | j + 1, rs, L =>
    let r := rs.headD default
    let c := r.α + r.β * x
    foldRowF x j rs.tail fun u => L (2 * u + 1) + c * L (2 * u)

theorem foldRowE_eq (x : FE2) : ∀ (j : ℕ) {m : ℕ} (rs : List RndF) (L : (Fin (m + j) → Bool) → E2)
    (L' : ℕ → FE2), (∀ v, L v = FE2.toE2 (L' (bitsToNat v))) → ∀ u,
      Whir.foldRowE (FE2.toE2 x) j (rs.map RndF.dec) L u = FE2.toE2 (foldRowF x j rs L' (bitsToNat u))
  | 0, _, _, _, _, h, u => h u
  | j + 1, m, rs, L, L', h, u => by
    have key : ∀ r : RndF, ∀ v : Fin (m + j) → Bool,
        L (Fin.cons true v) + ((RndF.dec r).α + (RndF.dec r).β * FE2.toE2 x) * L (Fin.cons false v) =
          FE2.toE2 (L' (2 * bitsToNat v + 1) + (r.α + r.β * x) * L' (2 * bitsToNat v)) := by
      intro r v
      rw [h, h, bitsToNat_cons, bitsToNat_cons, toE2_add', toE2_mul', toE2_add', toE2_mul']
      simp only [Bool.toNat_true, Bool.toNat_false, Nat.zero_add, Nat.add_comm 1]
      rfl
    cases rs with
    | nil =>
      exact foldRowE_eq x j []
        (fun v => L (Fin.cons true v) + ((RndF.dec default).α + (RndF.dec default).β * FE2.toE2 x) *
          L (Fin.cons false v))
        (fun n => L' (2 * n + 1) + ((default : RndF).α + (default : RndF).β * x) * L' (2 * n)) (key default) u
    | cons r rs =>
      exact foldRowE_eq x j rs
        (fun v => L (Fin.cons true v) + ((RndF.dec r).α + (RndF.dec r).β * FE2.toE2 x) * L (Fin.cons false v))
        (fun n => L' (2 * n + 1) + (r.α + r.β * x) * L' (2 * n)) (key r) u

/-- **A mid level's value at position `p`**: the row's lanes folded at `K(p)`, minus the high part there. -/
def valAtF (κ ℓ : ℕ) (rs : List RndF) (hi : List FE2) (p : ℕ) (lane : ℕ → FE2) : FE2 :=
  let a := kOfNat p
  foldRowF (FE2.ofK a) ℓ rs lane 0 - highEvalF κ ℓ hi (nwF a)

theorem domE_eq (h : ℕ) (hh : h ≤ 64) (x : Fin (2 ^ h)) (p : ℕ) (hp : (x : ℕ) = p) :
    Whir.domE h hh x = FE2.toE2 (FE2.ofK (kOfNat p)) := by
  rw [toE2_ofK', toBF64_kOfNat, ← hp]
  rfl

theorem valsE_eq (z : Bool) (h ℓ κ : ℕ) (hh : h ≤ 64) (hκ : κ < 20) (hℓ : ℓ ≤ 8) {t : ℕ}
    (rs : List RndF) (hi : List FE2) (ps : Fin t → Fin (2 ^ h)) (rows : List (List K)) (k : Fin t)
    (p : ℕ) (hp : (ps k : ℕ) = p) (lane : ℕ → FE2)
    (hl : ∀ s, Whir.laneVal z (Whir.rowAt rows k) s = FE2.toE2 (lane s)) :
    Whir.valsE z h ℓ κ hh (rs.map RndF.dec) (hi.map FE2.toE2) ps rows k =
      FE2.toE2 (valAtF κ ℓ rs hi p lane) := by
  unfold Whir.valsE
  simp only [valAtF]
  rw [domE_eq h hh (ps k) p hp, highEval_eq κ ℓ hκ hℓ, foldRowE_eq _ ℓ rs _ lane (fun v => hl _),
    bitsToNat_zero, toE2_sub']

theorem fvE_eq (z : Bool) (h ℓ : ℕ) (hh : h ≤ 64) {t : ℕ} (rs : List RndF) (ps : Fin t → Fin (2 ^ h))
    (rows : List (List K)) (k : Fin t) (p : ℕ) (hp : (ps k : ℕ) = p) (lane : ℕ → FE2)
    (hl : ∀ s, Whir.laneVal z (Whir.rowAt rows k) s = FE2.toE2 (lane s)) :
    Whir.fvE z h ℓ hh (rs.map RndF.dec) ps rows k =
      FE2.toE2 (foldRowF (FE2.ofK (kOfNat p)) ℓ rs lane 0) := by
  unfold Whir.fvE
  rw [domE_eq h hh (ps k) p hp, foldRowE_eq _ ℓ rs _ lane (fun v => hl _), bitsToNat_zero]

end Lvm6.V
