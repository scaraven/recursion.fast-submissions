-- New for `flock-recursive` (BLUEPRINT §7, A.9; stage S-G).
-- RET-3: the declarations revision 4 reads moved to `FRVIRFinalsCoreSG`.
import FRVIRFinalsSF
import FRNodeLayout
import FRVIRFinalsCoreSG

/-!
# S-G's side of the phase-final checks

* **`lagV_eq_lagrangeWeight`** (S-F RESULT, open 2): the skip Lagrange weight that `finRS`'s ops
  compute (`FRVIRFinalsSF.lagV`, a product with the barycentric constant `wInv`) is the weight
  `FRSkip.lagrangeWeight` at the 64 nodes of `S` that `FRSpartan.quirky_claim_split` uses. In
  characteristic 2, `λ − x_j = λ + x_j`.

* **`finP i`** (A.9, the native verifier `prover/ligerito.rs`): level `i`'s outputs are the phases
  `P1, C, P2, Q, P3` at `phaseIx "P1" + 5 i + 0 … 4`; `Q`'s outputs are the column folds
  `y_q = dotKF(column_q, eq(s_i, ·))` (the skeleton computes them), each three registers after its
  position `idx` (`FRVIR.posOps`).
  - `i < 4`: `claim0(P1.(i+1)) = claimN(P1.i) + Σ_q eq(κ_c, bits₉(q))·y_q` (`κ_c` the first 9
    coordinates of `P3.i`).
  - `i = 4`: `y_q = Enc₄(final)[p_q] = Σ_{c<2^7} final[c]·Π_v Ŵ_v(D[p_q])^{c_v}` for every `q`
    (`Ŵ_v(D[p]) = tensorW p e_v`, then Horner over the bits from the top), and Pf's initial claim is
    `claimN(P1.4)` (the native verifier adds nothing at the last level). The padding of an
    `m = 30` final message is zero (`FRVIR.finalOps`), so the sum over `2^7` is the sum over `2^5`.

* **`finPf`** (A.9, stage-review changes 11; the native `weight_eval`, `prover/ligerito.rs`): with
  `P₄ = s₄ ++ sf[..μ]` (`μ = m − 25`), `Pₖ = sₖ ++ Pₖ₊₁[1..]`, `û(β) = 1 + β(1 + u)` and
  `Ŵₖ(Pₖ) = û(Pₖ[0])·(Ŵₖ₋₁(Pₖ₋₁) + Σ_q eq(κ_c⁽ᵏ⁻¹⁾, bits₉(q))·tensorW(p_q⁽ᵏ⁻¹⁾, Pₖ[1..]))`,
  `Ŵ₀(ρ) = rsWeight(r″, pts, κ, ρ) + [node] Σ_k κ′^(k+2) eq(cell_k, ρ)` (revisions 3.12–3.13: no
  `evalMK` term; E4's claim is RS claim 4, whose outer point is E4's `r′`), the check is
  `claimN(Pf) = Ŵ₄(P₄) · Π_{x ∈ sf[μ..7)} (1 + x) · final̂(sf)`. The claim points `pts` are the
  native `claim_points` (`zSrc`, `lcSrc`, `shSrc`; the node's `eSrc`, E4's 23 challenges; revision
  3.13 withdrew Lr's own claim and its provisional point), the cells
  are `finB′`'s nine (`pfCells`). **`flag_finPf`**: its flag is `relPf` (`relPf_iff`), with
  `Ŵ₄` as `wV` (`lvsV` over `lvStepV`), `final̂` as `finHat` (`fhVal_eq`) and the cells' sum
  `cellsVal_eq`; **`noAsk_finPf`**: it asks nothing. The proof runs block by block on a growing
  register file (`pureRun_rebase`, `pr_seq`), with loop lemmas `run_ptsOps`, `run_prodKOps`,
  `run_cellsOps`, `run_lvOps`/`run_lvsOps`, `run_fhOps`.
-/

namespace FR

/-- The product over `others lo` is the product over the 63 nodes other than `lo`. -/
theorem prod_others (g : ℕ → F) {lo : ℕ} (hlo : lo < 64) :
    ((others lo).map g).prod = ∏ j ∈ (Finset.univ : Finset (Fin 64)).erase ⟨lo, hlo⟩, g j := by
  have hc : (Finset.univ : Finset (Fin 64)).erase ⟨lo, hlo⟩ =
      Finset.univ.map (Fin.succAboveEmb ⟨lo, hlo⟩) := by
    ext x
    simp only [Finset.mem_erase, Finset.mem_univ, and_true, Finset.mem_map, true_and,
      Fin.succAboveEmb_apply]
    exact ⟨fun h => Fin.exists_succAbove_eq h, fun ⟨y, hy⟩ => hy ▸ Fin.succAbove_ne _ _⟩
  have hl : ∀ h : ℕ → F, ((List.range 63).map h).prod = ∏ i ∈ Finset.range 63, h i := by
    intro h
    rw [Finset.prod_eq_multiset_prod, Finset.range_val, Multiset.range, Multiset.map_coe,
      Multiset.prod_coe]
  rw [hc, Finset.prod_map, others, List.map_map, hl, Finset.prod_range]
  refine Finset.prod_congr rfl fun i _ => ?_
  simp only [Function.comp_apply, Fin.succAboveEmb_apply]
  congr 1
  by_cases h : i.val < lo
  · simp only [h, ↓reduceIte]
    rw [Fin.succAbove_of_castSucc_lt _ _ (by simpa [Fin.lt_def] using h)]; rfl
  · simp only [h, ↓reduceIte]
    rw [Fin.succAbove_of_le_castSucc _ _ (by simp [Fin.le_def]; omega)]; rfl

/-- **`lagV_eq_lagrangeWeight`**: the weight `finRS`'s ops compute at `λ` is the Lagrange weight
of node `lo` of `S` at `λ`. -/
theorem lagV_eq_lagrangeWeight (l : F) {lo : ℕ} (hlo : lo < 64) :
    lagV l lo = lagrangeWeight sNodeF l ⟨lo, hlo⟩ := by
  have hx : ∀ j ∈ (Finset.univ : Finset (Fin 64)).erase ⟨lo, hlo⟩, xS j = sNodeF j :=
    fun j _ => xS_of_lt j.isLt
  rw [lagV, wInv, foldl_mul_eq, foldl_mul_eq, one_mul, prod_others _ hlo, prod_others _ hlo,
    lagrangeWeight, mul_comm, xS_of_lt hlo]
  have hp : ∀ c : F, ∏ j ∈ (Finset.univ : Finset (Fin 64)).erase ⟨lo, hlo⟩, (c + xS j) =
      ∏ j ∈ (Finset.univ : Finset (Fin 64)).erase ⟨lo, hlo⟩, (c - sNodeF j) := fun c =>
    Finset.prod_congr rfl fun j hj => by rw [hx j hj, sub_eq_add_neg, CharTwo.neg_eq]
  rw [hp, hp]

/-! ## `finP i` (A.9) -/

/-! ## `finP i < 4` runs to its relation -/

section RunP
variable (impl : OpImpl) (κ : Kind) (inp : Input) (r : Array Val)

variable (fi : FinIn)

/-! ### `finP 4` -/

/-- `Enc₄(final)[p]` as `encOps` computes it: Horner with `W_v = tensorW p e_v`. -/
def encVal (p : ℕ) : K := hornerVal (fun v => impl.tensorW p (unitK v)) 7 (finV inp)

/-- **One position at level 4**: `encW` registers; the flag is `y = Enc₄(final)[p]`. -/
theorem run_encOps (units fin : List Reg) (j y : Reg) (L : List Val) (hj : j < r.size)
    (hy : y < r.size)
    (hu : ∀ v < 7, units.getD v 0 < r.size + L.length ∧
      rd (r ++ L.toArray) (units.getD v 0) = .ak (unitK v))
    (hf : ∀ c < 2 ^ 7, fin.getD c 0 < r.size + L.length ∧
      rd (r ++ L.toArray) (fin.getD c 0) = .k (finV inp c)) :
    ∃ M, pureRun impl κ inp (encOps units fin j y (r.size + L.length)) r L =
      some (L ++ M, (Val.k (encVal impl inp (rd r j).toN)).eqv (rd r y)) ∧ M.length = encW := by
  set tws : List Op := (List.range 7).map fun v => .tensorW j (units.getD v 0)
  have h1 := run_frozen impl κ inp r L (twVal impl r L) tws [] (fun op hop Y => by
    obtain ⟨v, hv, rfl⟩ := List.mem_map.mp hop
    have hv' := (hu v (List.mem_range.mp hv)).1
    simp only [evalOp, twVal, rd_app_left _ _ hj, rd_pre r hv'])
  simp only [List.append_nil] at h1
  set M₁ := tws.map (twVal impl r L)
  have hl1 : M₁.length = 7 := by simp [M₁, tws]
  have hM₁ : ∀ v < 7, rd (r ++ (L ++ M₁).toArray) ((r.size + L.length) + v) =
      .k (impl.tensorW (rd r j).toN (unitK v)) := by
    intro v hv
    rw [show (r.size + L.length) + v = r.size + (L.length + v) by omega, rd_app,
      List.getD_append_right _ _ _ _ (by omega)]
    have hu2 := (hu v hv).2
    simp only [List.getD_eq_getElem?_getD] at hu2
    simp [M₁, tws, twVal, hv, hu2]; rfl
  obtain ⟨M₂, h2, hl2, hv2⟩ :=
    run_horner impl κ inp r ((List.range 7).map ((r.size + L.length) + ·))
    (fun v => impl.tensorW (rd r j).toN (unitK v)) 7 fin (finV inp) (L ++ M₁)
    (fun u hu' => by
      simp only [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range hu',
        Option.map_some, Option.getD_some, List.length_append, hl1]
      exact ⟨by rw [← Nat.add_assoc]; exact Nat.add_lt_add_left hu' _, hM₁ u hu'⟩)
    (fun c hc => by
      obtain ⟨a, a'⟩ := hf c hc
      exact ⟨Nat.lt_of_lt_of_le a (by simp only [List.length_append]; omega),
        by rw [rd_pre r a, a']⟩)
  have hb7 : r.size + (L ++ M₁).length = (r.size + L.length) + 7 := by
    rw [List.length_append, hl1]; omega
  rw [hb7] at h2 hv2
  refine ⟨M₁ ++ M₂, ?_, by simp [hl1, hl2, encW]⟩
  simp only [encOps]
  rw [List.append_assoc, pureRun_append, h1, Option.bind_some, pureRun_append, h2,
    Option.bind_some]
  simp only [pureRun, evalOp, allK, Bool.not_true, Bool.false_or, ← List.append_assoc]
  rw [hv2, rd_app_left _ _ hy]
  simp [encVal]

/-- The flag of position `q` at level 4: `y_q = Enc₄(final)[p_q]`. -/
def encFlag (ys : List Reg) (q : ℕ) : Bool :=
  (Val.k (encVal impl inp (rd r (ys.getD q 0 - 3)).toN)).eqv (rd r (ys.getD q 0))

/-- **The `T` first positions at level 4.** -/
theorem run_positions (units fin ys : List Reg) (L : List Val) (hys : ∀ y ∈ ys, y < r.size)
    (hu : ∀ v < 7, units.getD v 0 < r.size + L.length ∧
      rd (r ++ L.toArray) (units.getD v 0) = .ak (unitK v))
    (hf : ∀ c < 2 ^ 7, fin.getD c 0 < r.size + L.length ∧
      rd (r ++ L.toArray) (fin.getD c 0) = .k (finV inp c)) :
    ∀ T ≤ ys.length, ∃ M, pureRun impl κ inp ((List.range T).flatMap fun q =>
        encOps units fin (ys.getD q 0 - 3) (ys.getD q 0) (r.size + L.length + encW * q)) r L =
      some (L ++ M, (List.range T).all (encFlag impl inp r ys)) ∧ M.length = encW * T
  | 0, _ => ⟨[], by simp [pureRun], by simp⟩
  | T + 1, hT => by
    obtain ⟨M, hM, hl⟩ := run_positions units fin ys L hys hu hf T (by omega)
    have hyT : ys.getD T 0 < r.size := by
      have := hys _ (List.getElem_mem (show T < ys.length by omega))
      simpa [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (show T < ys.length by omega)]
    obtain ⟨M', hM', hl'⟩ := run_encOps impl κ inp r units fin (ys.getD T 0 - 3) (ys.getD T 0)
      (L ++ M) (Nat.lt_of_le_of_lt (Nat.sub_le _ _) hyT) hyT
      (fun v hv => by
        obtain ⟨a, a'⟩ := hu v hv
        exact ⟨Nat.lt_of_lt_of_le a (by simp), by rw [rd_pre r a, a']⟩)
      (fun c hc => by
        obtain ⟨a, a'⟩ := hf c hc
        exact ⟨Nat.lt_of_lt_of_le a (by simp), by rw [rd_pre r a, a']⟩)
    have hb : r.size + (L ++ M).length = r.size + L.length + encW * T := by
      rw [List.length_append, hl]; omega
    rw [hb] at hM'
    refine ⟨M ++ M', ?_, by simp [hl, hl']; ring⟩
    rw [List.range_succ, List.flatMap_append, pureRun_append, hM, Option.bind_some]
    simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil, hM', Option.map_some,
      List.all_append, List.all_cons, List.all_nil, Bool.and_true, List.append_assoc]
    rfl

/-- **A.9's `finP 4` relation**: every `y_q = Enc₄(final)[p_q]`, and Pf's initial claim is
`claimN(P1.4)`. -/
def relP4 : Bool :=
  (List.range (ysOf fi 4).length).all (encFlag impl inp r (ysOf fi 4)) &&
    (rd r (claim0 fi "Pf")).eqv (rd r (p1ClaimN fi 4))

/-- **`flag_finP4`**: `finP 4` asks nothing; its flag is `relP4`. -/
theorem flag_finP4 (hin : ∀ x ∈ ysOf fi 4 ++ [claim0 fi "Pf", p1ClaimN fi 4], x < r.size) :
    ∃ L, pureRun impl κ inp (finP4 fi r.size).1 r [] = some (L, relP4 impl inp r fi) := by
  simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hin
  have hys : ∀ y ∈ ysOf fi 4, y < r.size := fun y hy => hin y (.inl hy)
  have hP := hin _ (.inr (.inl rfl)); have hN := hin _ (.inr (.inr rfl))
  set A : List Op := (List.range 128).map fun c => .piElemK fFinal (32 * c)
  set B : List Op := (List.range 7).map fun v => .const fun _ => .ak (unitK v)
  have hAB := run_indep impl κ inp r (p4Val κ inp) (A ++ B) [] (fun op hop regs => by
    rcases List.mem_append.mp hop with h | h
    · obtain ⟨c, -, rfl⟩ := List.mem_map.mp h; rfl
    · obtain ⟨v, -, rfl⟩ := List.mem_map.mp h; rfl)
  simp only [List.nil_append] at hAB
  set L₀ := (A ++ B).map (p4Val κ inp)
  have hl0 : L₀.length = 135 := by simp [L₀, A, B]
  obtain ⟨M, hM, -⟩ := run_positions impl κ inp r ((List.range 7).map (r.size + 128 + ·))
    ((List.range 128).map (r.size + ·)) (ysOf fi 4) L₀ hys
    (fun v hv => by
      have hg : ((List.range 7).map (r.size + 128 + ·)).getD v 0 = r.size + 128 + v := by simp [hv]
      refine ⟨?_, ?_⟩
      · rw [hg]; simp only [L₀, A, B, List.length_map, List.length_append, List.length_range]
        rw [Nat.add_assoc]; exact Nat.add_lt_add_left (Nat.add_lt_add_left hv 128) _
      rw [hg, show r.size + 128 + v = r.size + (128 + v) by omega, rd_app]
      simp only [L₀, A, B, List.getD_eq_getElem?_getD, List.map_append, List.map_map]
      rw [List.getElem?_append_right (by simp)]
      simp [hv, p4Val])
    (fun c hc => by
      have hc' : c < 128 := by simpa using hc
      have hg : ((List.range 128).map (r.size + ·)).getD c 0 = r.size + c := by simp [hc']
      refine ⟨?_, ?_⟩
      · rw [hg]; simp only [L₀, A, B, List.length_map, List.length_append, List.length_range]
        exact Nat.add_lt_add_left (Nat.lt_of_lt_of_le hc' (by norm_num)) _
      rw [hg, rd_app]
      simp only [L₀, A, B, List.getD_eq_getElem?_getD, List.map_append, List.map_map]
      rw [List.getElem?_append_left (by simp; omega)]
      simp [hc', p4Val, finV])
    (ysOf fi 4).length le_rfl
  rw [hl0] at hM
  refine ⟨L₀ ++ M, ?_⟩
  simp only [finP4]
  rw [pureRun_append, pureRun_append, hAB, Option.bind_some, hM]
  simp only [Option.map_some, Option.bind_some, pureRun, evalOp, allK, Bool.not_true, Bool.false_or,
    rd_app_left _ _ hP, rd_app_left _ _ hN, Bool.true_and, Bool.and_true, relP4, List.append_nil]

end RunP

theorem noAsk_encOps (units fin : List Reg) (j y b : ℕ) :
    (encOps units fin j y b).filterMap Op.item? = [] := by
  simp [encOps, Op.item?, noAsk_hornerKOps, List.filterMap_eq_nil_iff]

/-- **S-G's `finP` asks nothing** (`items_gen`'s hypothesis, for these fields). -/
theorem noAsk_finP (i : ℕ) (fi : FinIn) (b : ℕ) : (finP i fi b).1.filterMap Op.item? = [] := by
  unfold finP
  split_ifs
  · simp only [finPLow, List.filterMap_append, List.filterMap_cons, Op.item?, noAsk_accOps]; rfl
  · simp [finP4, Op.item?, noAsk_encOps, List.filterMap_flatMap, List.filterMap_eq_nil_iff]

/-! ## `finPf` (A.9): Pf's final check, after the native `weight_eval` -/

/-! ### `finPf` asks nothing -/

theorem noAsk_cellsOps (one g h kp : Reg) :
    ∀ cs acc pw b, (cellsOps one g h kp cs acc pw b).filterMap Op.item? = []
  | [], _, _, _ => rfl
  | c :: cs, acc, pw, b => by
    rw [cellsOps, cellOps, List.filterMap_append, List.filterMap_append, noAsk_prodKOps,
      noAsk_cellsOps one g h kp cs]
    rfl

theorem noAsk_lvsOps (fi : FinIn) (one cu Ts : Reg) :
    ∀ ks W b, (lvsOps fi one cu Ts ks W b).filterMap Op.item? = []
  | [], _, _ => rfl
  | k :: ks, W, b => by
    have ht : ((List.range (ysOf fi (k - 1)).length).map fun q =>
        Op.tensorW ((ysOf fi (k - 1)).getD q 0 - 3) (Ts + (k - 1))).filterMap Op.item? = [] :=
      noAsk_map _ _ fun _ => rfl
    rw [lvsOps, lvOps, List.filterMap_append, noAsk_lvsOps fi one cu Ts ks]
    simp only [List.filterMap_append, noAsk_accOps, ht]
    rfl

/-- **`finPf` asks nothing** (`items_gen`'s hypothesis). -/
theorem noAsk_finPf (fi : FinIn) (b : ℕ) : (finPf fi b).1.filterMap Op.item? = [] := by
  have h1 : ∀ (a : Reg) (n : ℕ),
      ((List.range n).map fun v => Op.getK a v).filterMap Op.item? = [] :=
    fun _ _ => noAsk_map _ _ fun _ => rfl
  have h2 : ∀ (a c : Reg) (n : ℕ),
      ((List.range n).map fun v => Op.addK a (c + v)).filterMap Op.item? = [] :=
    fun _ _ _ => noAsk_map _ _ fun _ => rfl
  simp only [finPf, List.filterMap_append, noAsk_ptsOps, noAsk_cellsOps, noAsk_lvsOps,
    noAsk_fhOps, h1, h2]
  simp only [List.filterMap_cons, List.filterMap_nil, Op.item?, List.append_nil]

/-! ### `finPf` runs to its relation -/

section RunPf
variable (impl : OpImpl) (κ : Kind) (inp : Input)

/-! ### Points -/

variable (r : Array Val) (one z0 : ℕ) (h1 : one < r.size) (hv1 : rd r one = .k 1)
  (h0 : z0 < r.size) (hv0 : rd r z0 = .k 0)
include h1 hv1 h0 hv0

end RunPf

/-- `A + Σ_k pw·κ′^k·eq(cell_k, ρ)` (as `cellsOps` accumulates it). -/
def cellsVal (ρ : Array K) (kp : F) : List ℕ → F → K → K
  | [], _, A => A
  | c :: cs, pw, A => cellsVal ρ kp cs (pw * kp) (A + K.smulF pw (eqCellK ρ c))

section Loops
variable (impl : OpImpl) (κ : Kind) (inp : Input) (r : Array Val)

theorem foldl_sel (ρ : Array K) (g h c : ℕ)
    (hg : ∀ v < 23, (rd r (g + v)).toK = ρ.getD v 0)
    (hh : ∀ v < 23, (rd r (h + v)).toK = 1 + ρ.getD v 0) :
    ((List.range 23).map fun v => if c.testBit v then g + v else h + v).foldl
      (fun a x => a * (rd r x).toK) 1 = eqCellK ρ c := by
  rw [eqCellK, List.foldl_map, List.foldl_map]
  refine List.foldl_ext _ _ _ fun a v hv => ?_
  have hv' := List.mem_range.mp hv
  split <;> simp [hg v hv', hh v hv']

theorem run_cellsOps (one g h kp : ℕ) (ρ : Array K) (kpv : F)
    (h1 : one < r.size) (hv1 : rd r one = .k 1) (hk : kp < r.size) (hkv : (rd r kp).toF = kpv)
    (hg0 : ∀ v < 23, g + v < r.size ∧ (rd r (g + v)).toK = ρ.getD v 0)
    (hh0 : ∀ v < 23, h + v < r.size ∧ (rd r (h + v)).toK = 1 + ρ.getD v 0) :
    ∀ (cs : List ℕ) (acc pw : ℕ) (A : K) (Pw : F) (L : List Val),
    acc < r.size + L.length → rd (r ++ L.toArray) acc = .k A →
    pw < r.size + L.length → (rd (r ++ L.toArray) pw).toF = Pw →
    ∃ M, pureRun impl κ inp (cellsOps one g h kp cs acc pw (r.size + L.length)) r L =
        some (L ++ M, true) ∧ M.length = 26 * cs.length ∧
      rd (r ++ (L ++ M).toArray) (cellsAcc cs acc (r.size + L.length)) = .k (cellsVal ρ kpv cs Pw A)
  | [], acc, pw, A, Pw, L, _, hA, _, _ =>
    ⟨[], by simp [cellsOps, pureRun], rfl, by simpa [cellsAcc, cellsVal] using hA⟩
  | c :: cs, acc, pw, A, Pw, L, hacc, hA, hpw, hP => by
    set b := r.size + L.length with hb
    set xs := (List.range 23).map fun v => if c.testBit v then g + v else h + v
    have hxs : ∀ x ∈ xs, x < r.size := by
      intro x hx
      obtain ⟨v, hv, rfl⟩ := List.mem_map.mp hx
      have hv' := List.mem_range.mp hv
      split
      · exact (hg0 v hv').1
      · exact (hh0 v hv').1
    obtain ⟨M₁, h₁, hl₁, hv₁⟩ := run_prodKOps impl κ inp r xs one 1 L hxs
      (Nat.lt_of_lt_of_le h1 (by simp)) (by rw [rd_app_left _ _ h1, hv1])
    rw [prodKOut_eq xs one b (by simp [xs]), show xs.length = 23 by simp [xs],
      foldl_sel r ρ g h c (fun v hv => (hg0 v hv).2) (fun v hv => (hh0 v hv).2)] at hv₁
    have hl₁' : M₁.length = 23 := by rw [hl₁]; simp [xs]
    set e := eqCellK ρ c
    set u₁ : Val := .k (K.smulF Pw e)
    set u₂ : Val := .k (A + K.smulF Pw e)
    set u₃ : Val := .f (Pw * kpv)
    have e1 : evalOp impl κ inp (r ++ (L ++ M₁).toArray) (.mulKF (b + 22) pw) =
        .vals [u₁] true := by
      simp only [evalOp]; rw [show b + 23 - 1 = b + 22 by omega] at hv₁
      rw [hv₁, rd_pre r hpw, hP]; rfl
    have e2 : evalOp impl κ inp (r ++ (L ++ M₁ ++ [u₁]).toArray) (.addK acc (b + 23)) =
        .vals [u₂] true := by
      have : b + 23 = r.size + (L ++ M₁).length := by
        simp only [List.length_append, hl₁']; omega
      simp only [evalOp]; rw [this, rd_new1, List.append_assoc, rd_pre r hacc, hA]; rfl
    have e3 : evalOp impl κ inp (r ++ (L ++ M₁ ++ [u₁] ++ [u₂]).toArray) (.mulF pw kp) =
        .vals [u₃] true := by
      simp only [evalOp]
      rw [List.append_assoc, List.append_assoc, rd_pre r hpw, hP,
        rd_pre r (Nat.lt_of_lt_of_le hk (by simp)), rd_app_left _ _ hk, hkv]
    set L' := L ++ M₁ ++ [u₁] ++ [u₂] ++ [u₃]
    have hL' : r.size + L'.length = b + 26 := by
      simp only [L', List.length_append, List.length_singleton, hl₁']; omega
    obtain ⟨M, hM, hl, hv⟩ := run_cellsOps one g h kp ρ kpv h1 hv1 hk hkv hg0 hh0 cs (b + 24)
      (b + 25) (A + K.smulF Pw e) (Pw * kpv) L' (by rw [hL']; omega)
      (by
        have : b + 24 = r.size + (L ++ M₁ ++ [u₁]).length := by
          simp only [List.length_append, List.length_singleton, hl₁']; omega
        rw [this, show L' = L ++ M₁ ++ [u₁] ++ ([u₂] ++ [u₃]) by simp [L']]
        rw [show L ++ M₁ ++ [u₁] ++ ([u₂] ++ [u₃]) = L ++ M₁ ++ [u₁] ++ (u₂ :: [u₃]) by rfl,
          rd_new])
      (by rw [hL']; omega)
      (by
        have : b + 25 = r.size + (L ++ M₁ ++ [u₁] ++ [u₂]).length := by
          simp only [List.length_append, List.length_singleton, hl₁']; omega
        rw [this, rd_new1]; rfl)
    rw [hL'] at hM hv
    refine ⟨M₁ ++ [u₁, u₂, u₃] ++ M, ?_, by simp [hl, hl₁']; ring, ?_⟩
    · rw [cellsOps, cellOps, List.append_assoc, pr_app impl κ inp r h₁]
      simp only [List.cons_append, List.nil_append]
      rw [pr_op impl κ inp r e1, pr_op impl κ inp r e2, pr_op impl κ inp r e3,
        show L ++ M₁ ++ [u₁] ++ [u₂] ++ [u₃] = L' from rfl, hM]
      simp [L']
    · simp only [cellsAcc, cellsVal]
      rw [show L ++ (M₁ ++ [u₁, u₂, u₃] ++ M) = L' ++ M by simp [L']]
      exact hv

theorem run_fhOps (E : ℕ) (Ev : Array K) (hE : E < r.size) (hEv : (rd r E).toAK = Ev) :
    ∀ (cs : List ℕ) (acc : ℕ) (A : K) (L : List Val),
    acc < r.size + L.length → rd (r ++ L.toArray) acc = .k A →
    ∃ M, pureRun impl κ inp (fhOps E cs acc (r.size + L.length)) r L = some (L ++ M, true) ∧
      M.length = 4 * cs.length ∧
      rd (r ++ (L ++ M).toArray) (fhOut cs acc (r.size + L.length)) = .k (fhVal inp Ev cs A)
  | [], acc, A, L, _, hA => ⟨[], by simp [fhOps, pureRun], rfl, by simpa [fhOut, fhVal] using hA⟩
  | c :: cs, acc, A, L, hacc, hA => by
    set b := r.size + L.length with hb
    set u₁ : Val := .k (finV inp c)
    set u₂ : Val := .k (Ev.getD c 0)
    set u₃ : Val := .k (finV inp c * Ev.getD c 0)
    set u₄ : Val := .k (A + finV inp c * Ev.getD c 0)
    have e1 : evalOp impl κ inp (r ++ L.toArray) (.piElemK fFinal (32 * c)) = .vals [u₁] true := rfl
    have e2 : evalOp impl κ inp (r ++ (L ++ [u₁]).toArray) (.getK E c) = .vals [u₂] true := by
      simp only [evalOp, rd_app_left _ _ hE, hEv]; rfl
    have e3 : evalOp impl κ inp (r ++ (L ++ [u₁] ++ [u₂]).toArray) (.mulK b (b + 1)) =
        .vals [u₃] true := by
      have x2 : b + 1 = r.size + (L ++ [u₁]).length := by
        simp only [hb, List.length_append, List.length_singleton]; omega
      simp only [evalOp]
      rw [x2, rd_new1, List.append_assoc, List.singleton_append, rd_new]; rfl
    have e4 : evalOp impl κ inp (r ++ (L ++ [u₁] ++ [u₂] ++ [u₃]).toArray) (.addK acc (b + 2)) =
        .vals [u₄] true := by
      have x3 : b + 2 = r.size + (L ++ [u₁] ++ [u₂]).length := by
        simp only [hb, List.length_append, List.length_singleton]; omega
      simp only [evalOp]
      rw [x3, rd_new1, List.append_assoc, List.append_assoc, rd_pre r hacc, hA]; rfl
    set L' := L ++ [u₁] ++ [u₂] ++ [u₃] ++ [u₄]
    have hL' : r.size + L'.length = b + 4 := by
      simp only [L', hb, List.length_append, List.length_singleton]; omega
    obtain ⟨M, hM, hl, hv⟩ := run_fhOps E Ev hE hEv cs (b + 3) (A + finV inp c * Ev.getD c 0) L'
      (by rw [hL']; omega)
      (by
        have x4 : b + 3 = r.size + (L ++ [u₁] ++ [u₂] ++ [u₃]).length := by
          simp only [hb, List.length_append, List.length_singleton]; omega
        rw [x4, rd_new1])
    rw [hL'] at hM hv
    refine ⟨[u₁, u₂, u₃, u₄] ++ M, ?_, by simp [hl]; ring, ?_⟩
    · rw [fhOps]
      simp only [List.cons_append, List.nil_append]
      rw [pr_op impl κ inp r e1, pr_op impl κ inp r e2, pr_op impl κ inp r e3,
        pr_op impl κ inp r e4, show L ++ [u₁] ++ [u₂] ++ [u₃] ++ [u₄] = L' from rfl, hM]
      simp [L']
    · simp only [fhOut, fhVal]
      rw [show L ++ ([u₁, u₂, u₃, u₄] ++ M) = L' ++ M by simp [L']]
      exact hv

end Loops

/-! ### `finPf`'s relation -/

/-- The registers `finPf` reads (both `m`). -/
def pfRefs (fi : FinIn) : List ℕ :=
  (pfPts fi).flatMap (fun s => s.flatMap PtSrc.regs) ++
    (List.range 8).map (fun p => (coordsR fi "RS1").getD p 0) ++
    [(outsOf fi "B'").headD 0, claimN fi "Pf", (chals fi "Pf" 7).getD 5 0,
      (chals fi "Pf" 7).getD 6 0, (outsOf fi "L3β").headD 0] ++ chals fi "Pf" 7 ++
    [1, 2, 3, 4].flatMap (lvRefs fi)

section PfVal
variable (impl : OpImpl) (κ : Kind) (inp : Input) (fi : FinIn) (r : Array Val)

/-- `Pₖ[1..]` (`k = 1 … 4`) and `P₀` at the kind's `m`. -/
def tailV (k : ℕ) : Array K := ((tailRegs fi κ.m k).map fun x => (rd r x).toK).toArray
def p0V : Array K := ((p0Regs fi κ.m).map fun x => (rd r x).toK).toArray

/-- The claim points `rsWeight` gets. -/
def rsPtsV : List (Array K) := (rsPtIx κ).map fun j => ptV r ((pfPts fi).getD j [])

/-- **`Ŵ₀(P₀)`**: `rsWeight(r″, pts, κ, P₀)` (a node's four claims end with E4's, revision 3.13),
and for a node `Σ_k κ′^(k+2) eq(cell_k, P₀)`. -/
def w0V : K :=
  let kp := fv r ((outsOf fi "B'").headD 0)
  impl.rsWeight (ptF r ((List.range 7).map fun p => (coordsR fi "RS1").getD p 0))
      (rsPtsV κ fi r) (fv r ((coordsR fi "RS1").getD 7 0))
      (if κ.isNode then fv r ((outsOf fi "L3β").headD 0) else 1) (p0V κ fi r) +
    (if κ.isNode then cellsVal (p0V κ fi r) kp pfCells (kp * kp) 0 else 0)

/-- **`Ŵ₄(P₄)`**: the four level steps from `Ŵ₀(P₀)`. -/
def wV : K := lvsV impl fi (rd r) (tailV κ fi r) [1, 2, 3, 4] (w0V impl κ fi r)

/-- The padding factor `Π_{x ∈ sf[μ..7)} (1 + x)`. -/
def padV : K :=
  if κ = .L32 then 1
  else (1 + (rd r ((chals fi "Pf" 7).getD 5 0)).toK) * (1 + (rd r ((chals fi "Pf" 7).getD 6 0)).toK)

/-- `final̂(sf) = Σ_c final[c]·eq(sf, c)`. -/
def finHat : K :=
  fhVal inp (eqTab ((chals fi "Pf" 7).map fun x => (rd r x).toK).toArray) (List.range 128) 0

/-- **A.9's `finPf` relation**: `claimN(Pf) = Ŵ₄(P₄)·pad·final̂(sf)`. -/
def relPf : Bool :=
  (Val.k (wV impl κ fi r * padV κ fi r * finHat inp fi r)).eqv (rd r (claimN fi "Pf"))

end PfVal

theorem ptV_k (r : Array Val) (xs : List ℕ) :
    ptV r (xs.map .k) = (xs.map fun x => (rd r x).toK).toArray := by
  simp [ptV, srcVal, Function.comp_def]

theorem flag_finPf (impl : OpImpl) (κ : Kind) (inp : Input) (fi : FinIn) (r : Array Val)
    (hin : ∀ x ∈ pfRefs fi, x < r.size) :
    ∃ L, pureRun impl κ inp (finPf fi r.size).1 r [] = some (L, relPf impl κ inp fi r) := by
  have app0 : ∀ X : Array Val, X ++ ([] : List Val).toArray = X := fun X => by simp
  -- the registers read
  have mA : ∀ x ∈ (pfPts fi).flatMap (fun s => s.flatMap PtSrc.regs), x < r.size := fun x hx =>
    hin x (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _
      (List.mem_append_left _ hx))))
  have mB : ∀ p < 8, (coordsR fi "RS1").getD p 0 < r.size := fun p hp =>
    hin _ (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _
      (List.mem_append_right _ (List.mem_map.mpr ⟨p, List.mem_range.mpr hp, rfl⟩)))))
  have mC : ∀ x ∈ [(outsOf fi "B'").headD 0, claimN fi "Pf", (chals fi "Pf" 7).getD 5 0,
      (chals fi "Pf" 7).getD 6 0, (outsOf fi "L3β").headD 0], x < r.size :=
    fun x hx =>
    hin x (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_right _ hx)))
  have mD : ∀ x ∈ chals fi "Pf" 7, x < r.size := fun x hx =>
    hin x (List.mem_append_left _ (List.mem_append_right _ hx))
  have mE : ∀ k ∈ [1, 2, 3, 4], ∀ x ∈ lvRefs fi k, x < r.size := fun k hk x hx =>
    hin x (List.mem_append_right _ (List.mem_flatMap.mpr ⟨k, hk, hx⟩))
  have hOk : ∀ s ∈ pfPts fi, ∀ x ∈ s, x.Ok r.size := by
    intro s hs x hx
    cases x with
    | f y =>
      exact mA y (List.mem_flatMap.mpr ⟨s, hs, List.mem_flatMap.mpr ⟨_, hx, by simp [PtSrc.regs]⟩⟩)
    | k y =>
      exact mA y (List.mem_flatMap.mpr ⟨s, hs, List.mem_flatMap.mpr ⟨_, hx, by simp [PtSrc.regs]⟩⟩)
    | c v => trivial
  set kp := (outsOf fi "B'").headD 0 with hkp
  have hkpr : kp < r.size := mC _ (by simp [hkp])
  have hcNr : claimN fi "Pf" < r.size := mC _ (by simp)
  simp only [finPf, List.append_assoc]
  rw [show pfCells.length = 9 from rfl]
  generalize hpw : ptsW (pfPts fi) = pw
  generalize hlw : lvsW fi [1, 2, 3, 4] = lw
  set b := r.size with hb
  -- B1: the constants
  set V1 : List Val := [.k 1, .k (1 + K.u), .k 0]
  have hB1 : pureRun impl κ inp [Op.const fun _ => Val.k 1, Op.const fun _ => Val.k (1 + K.u),
      Op.const fun _ => Val.k 0] r [] = some (V1, true) := rfl
  set R1 := r ++ V1.toArray with hR1
  have sR1 : R1.size = b + 3 := by simp [R1, V1, hb]
  have r1one : rd R1 b = .k 1 := by rw [hR1, hb, rd_app0]; rfl
  have r1cu : rd R1 (b + 1) = .k (1 + K.u) := by rw [hR1, hb, rd_app]; rfl
  have r1z : rd R1 (b + 2) = .k 0 := by rw [hR1, hb, rd_app]; rfl
  have e01 : ExtA r R1 := ExtA.app r V1
  -- B2: the points
  obtain ⟨M2, hB2, hl2, hv2⟩ := run_ptsOps impl κ inp R1 b (b + 2) (by omega) r1one (by omega) r1z
    (pfPts fi) [] (fun s hs x hx => by
      have := hOk s hs x hx
      cases x with
      | f y => exact Nat.lt_of_lt_of_le this e01.1
      | k y => exact Nat.lt_of_lt_of_le this e01.1
      | c v => trivial)
  simp only [List.length_nil, Nat.add_zero, List.nil_append, sR1] at hB2 hv2
  set R2 := R1 ++ M2.toArray with hR2
  have sR2 : R2.size = b + 3 + pw := by simp [R2, sR1, hl2, hpw]
  have e12 : ExtA R1 R2 := ExtA.app R1 M2
  have hlen : (pfPts fi).length = 17 := by simp [pfPts]
  have hPv : ∀ j < 17, rd R2 (ptsOut (pfPts fi) (b + 3) j) = .ak (ptV r ((pfPts fi).getD j [])) ∧
      ptsOut (pfPts fi) (b + 3) j < R2.size := by
    intro j hj
    refine ⟨?_, ?_⟩
    · rw [hv2 j (by omega), hR1, ptV_app r V1 _ (hOk _ (by
        rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by omega)]
        exact List.getElem_mem _))]
    · rw [sR2, ← hpw]; exact ptsOut_lt _ _ _ (by omega)
  -- B3: the kind's tails and `P₀`
  have hkeep : ∀ j j', j < 17 → j' < 17 → ∀ L : List Val,
      evalOp impl κ inp (R2 ++ L.toArray) (.keep is32 (ptsOut (pfPts fi) (b + 3) j)
        (ptsOut (pfPts fi) (b + 3) j')) =
      .vals [if κ = .L32 then .ak (ptV r ((pfPts fi).getD j []))
        else .ak (ptV r ((pfPts fi).getD j' []))] true := by
    intro j j' hj hj' L
    simp only [evalOp, is32, rd_app_left _ _ (hPv j hj).2, rd_app_left _ _ (hPv j' hj').2,
      (hPv j hj).1, (hPv j' hj').1, decide_eq_true_eq]
  have hT : ∀ k < 4, (if κ = .L32 then Val.ak (ptV r ((pfPts fi).getD (7 + k) []))
      else .ak (ptV r ((pfPts fi).getD (11 + k) []))) = .ak (tailV κ fi r (k + 1)) := by
    intro k hk; interval_cases k <;> cases κ <;> simp [pfPts, ptV_k, tailV, Kind.m]
  have hT0 : (if κ = .L32 then Val.ak (ptV r ((pfPts fi).getD 15 []))
      else .ak (ptV r ((pfPts fi).getD 16 []))) = .ak (p0V κ fi r) := by
    cases κ <;> simp [pfPts, ptV_k, p0V, Kind.m]
  set V3 : List Val := [.ak (tailV κ fi r 1), .ak (tailV κ fi r 2), .ak (tailV κ fi r 3),
    .ak (tailV κ fi r 4), .ak (p0V κ fi r)]
  have hB3 : pureRun impl κ inp
      [.keep is32 (ptsOut (pfPts fi) (b + 3) 7) (ptsOut (pfPts fi) (b + 3) 11),
       .keep is32 (ptsOut (pfPts fi) (b + 3) 8) (ptsOut (pfPts fi) (b + 3) 12),
       .keep is32 (ptsOut (pfPts fi) (b + 3) 9) (ptsOut (pfPts fi) (b + 3) 13),
       .keep is32 (ptsOut (pfPts fi) (b + 3) 10) (ptsOut (pfPts fi) (b + 3) 14),
       .keep is32 (ptsOut (pfPts fi) (b + 3) 15) (ptsOut (pfPts fi) (b + 3) 16)] R2 [] =
      some (V3, true) := by
    rw [pr_op impl κ inp R2 ((hkeep 7 11 (by omega) (by omega) _).trans (by rw [hT 0 (by omega)])),
      pr_op impl κ inp R2 ((hkeep 8 12 (by omega) (by omega) _).trans (by rw [hT 1 (by omega)])),
      pr_op impl κ inp R2 ((hkeep 9 13 (by omega) (by omega) _).trans (by rw [hT 2 (by omega)])),
      pr_op impl κ inp R2 ((hkeep 10 14 (by omega) (by omega) _).trans (by rw [hT 3 (by omega)])),
      pr_op impl κ inp R2 ((hkeep 15 16 (by omega) (by omega) _).trans (by rw [hT0]))]
    rfl
  set R3 := R2 ++ V3.toArray with hR3
  have sR3 : R3.size = b + 3 + pw + 5 := by simp [R3, sR2, V3]
  have e23 : ExtA R2 R3 := ExtA.app R2 V3
  have r3T : ∀ k < 4, rd R3 (b + 3 + pw + k) = .ak (tailV κ fi r (k + 1)) := by
    intro k hk; rw [hR3, ← sR2, rd_app]; interval_cases k <;> rfl
  have r3P : rd R3 (b + 3 + pw + 4) = .ak (p0V κ fi r) := by rw [hR3, ← sR2, rd_app]; rfl
  -- B4: `rsWeight`
  have e03 : ExtA r R3 := e01.trans (e12.trans e23)
  have rr : ∀ x < r.size, ∀ L : List Val, rd (R3 ++ L.toArray) x = rd r x := fun x hx L => by
    rw [rd_app_left R3 L (Nat.lt_of_lt_of_le hx e03.1), e03.rd hx]
  have hix : ∀ j ∈ rsPtIx κ, j < 17 := by cases κ <;> decide
  have hpts : (rsPtIx κ).map (fun j => (rd R3 (ptsOut (pfPts fi) (b + 3) j)).toAK) =
      rsPtsV κ fi r := by
    simp only [rsPtsV]
    refine List.map_congr_left fun j hj => ?_
    rw [e23.rd (hPv j (hix j hj)).2, (hPv j (hix j hj)).1]; rfl
  set kpv := fv r kp
  set rsW := impl.rsWeight (ptF r ((List.range 7).map fun p => (coordsR fi "RS1").getD p 0))
      (rsPtsV κ fi r) (fv r ((coordsR fi "RS1").getD 7 0))
      (if κ.isNode then fv r ((outsOf fi "L3β").headD 0) else 1) (p0V κ fi r)
  set V4 : List Val := [.af (ptF r ((List.range 7).map fun p => (coordsR fi "RS1").getD p 0)),
    .k rsW]
  have hrpp : ∀ x ∈ (List.range 7).map (fun p => (coordsR fi "RS1").getD p 0), x < r.size := by
    intro x hx; obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hx; exact mB p (by simp at hp; omega)
  have hB4 : pureRun impl κ inp
      [.packF ((List.range 7).map fun p => (coordsR fi "RS1").getD p 0),
       .rsWeight (b + 3 + pw + 5) (fun κ => (rsPtIx κ).map (ptsOut (pfPts fi) (b + 3)))
         ((coordsR fi "RS1").getD 7 0) ((outsOf fi "L3β").headD 0) Kind.isNode
         (b + 3 + pw + 4)] R3 [] =
      some (V4, true) := by
    have hP4 : b + 3 + pw + 4 < R3.size := by rw [sR3]; omega
    have hPr : ∀ j ∈ rsPtIx κ, ptsOut (pfPts fi) (b + 3) j < R3.size := fun j hj =>
      Nat.lt_of_lt_of_le (hPv j (hix j hj)).2 e23.1
    have hptsL : ∀ L : List Val, (rsPtIx κ).map (fun x =>
        (rd (R3 ++ L.toArray) (ptsOut (pfPts fi) (b + 3) x)).toAK) = rsPtsV κ fi r := fun L => by
      rw [← hpts]; exact List.map_congr_left fun j hj => by rw [rd_app_left _ _ (hPr j hj)]
    have hrpp' : (List.range 7).map (fun x => (rd R3 ((coordsR fi "RS1").getD x 0)).toF) =
        (List.range 7).map (fun x => fv r ((coordsR fi "RS1").getD x 0)) :=
      List.map_congr_left fun p hp => by rw [e03.rd (mB p (by simp at hp; omega))]
    rw [← sR3]
    simp only [pureRun, evalOp, List.nil_append, List.cons_append, rd_app, rd_app0,
      rd_app_left _ _ hP4, r3P, List.map_map, Function.comp_def, hptsL,
      rr _ (mB 7 (by omega)), rr ((outsOf fi "L3β").headD 0) (mC _ (by simp)),
      List.getD_cons_succ, List.getD_cons_zero, Option.map_some, Bool.and_true,
      Array.append_empty, hrpp']
    rfl
  set R4 := R3 ++ V4.toArray with hR4
  have sR4 : R4.size = b + 3 + pw + 5 + 2 := by simp [R4, sR3, V4]
  have e34 : ExtA R3 R4 := ExtA.app R3 V4
  have r4 : ∀ j < 2, rd R4 (b + 3 + pw + 5 + j) = V4.getD j default := fun j _ => by
    rw [hR4, ← sR3, rd_app]
  -- B5, B6: `ρ_v` and `1 + ρ_v` of `P₀`'s 23 coordinates
  have hP4' : b + 3 + pw + 4 < R4.size := by rw [sR4]; omega
  have hB5 := run_base impl κ inp R4 ((List.range 23).map fun v => Op.getK (b + 3 + pw + 4) v) []
    (fun op hop Y => by
      obtain ⟨v, -, rfl⟩ := List.mem_map.mp hop
      simp only [evalOp, rd_app_left _ _ hP4'])
    (fun op hop => by obtain ⟨v, -, rfl⟩ := List.mem_map.mp hop; exact ⟨_, rfl⟩)
  set V5 : List Val := (List.range 23).map fun v => .k ((p0V κ fi r).getD v 0)
  have hV5 : ((List.range 23).map fun v => Op.getK (b + 3 + pw + 4) v).map
      (baseVal impl κ inp R4) = V5 := by
    simp only [List.map_map, V5]
    refine List.map_congr_left fun v _ => ?_
    simp only [Function.comp_apply, baseVal, evalOp, e34.rd (show b + 3 + pw + 4 < R3.size by
      rw [sR3]; omega), r3P, Val.toAK]
  rw [hV5, List.nil_append] at hB5
  set R5 := R4 ++ V5.toArray with hR5
  have sR5 : R5.size = b + 3 + pw + 5 + 25 := by simp [R5, sR4, V5]
  have e45 : ExtA R4 R5 := ExtA.app R4 V5
  have r5 : ∀ v < 23, rd R5 (b + 3 + pw + 5 + 2 + v) = .k ((p0V κ fi r).getD v 0) := fun v hv => by
    rw [hR5, ← sR4, rd_app]; simp [V5, hv]
  have e15 : ExtA R1 R5 := e12.trans (e23.trans (e34.trans e45))
  have r5one : rd R5 b = .k 1 := by rw [e15.rd (by omega), r1one]
  have hB6 := run_base impl κ inp R5
    ((List.range 23).map fun v => Op.addK b (b + 3 + pw + 5 + 2 + v)) []
    (fun op hop Y => by
      obtain ⟨v, hv, rfl⟩ := List.mem_map.mp hop
      have : b + 3 + pw + 5 + 2 + v < R5.size := by rw [sR5]; simp at hv; omega
      simp only [evalOp, rd_app_left _ _ this, rd_app_left _ _ (show b < R5.size by omega)])
    (fun op hop => by obtain ⟨v, -, rfl⟩ := List.mem_map.mp hop; exact ⟨_, rfl⟩)
  set V6 : List Val := (List.range 23).map fun v => .k (1 + (p0V κ fi r).getD v 0)
  have hV6 : ((List.range 23).map fun v => Op.addK b (b + 3 + pw + 5 + 2 + v)).map
      (baseVal impl κ inp R5) = V6 := by
    simp only [List.map_map, V6]
    refine List.map_congr_left fun v hv => ?_
    simp only [Function.comp_apply, baseVal, evalOp, r5one, r5 v (List.mem_range.mp hv), toK_k]
  rw [hV6, List.nil_append] at hB6
  set R6 := R5 ++ V6.toArray with hR6
  have sR6 : R6.size = b + 3 + pw + 5 + 48 := by simp [R6, sR5, V6]
  have e56 : ExtA R5 R6 := ExtA.app R5 V6
  -- B7: `κ′²`
  have e06 : ExtA r R6 := e03.trans (e34.trans (e45.trans e56))
  have hB7 : pureRun impl κ inp [.mulF kp kp] R6 [] = some ([.f (kpv * kpv)], true) := by
    simp only [pureRun, evalOp, List.nil_append, Array.append_empty, e06.rd hkpr]; rfl
  set R7 := R6 ++ [Val.f (kpv * kpv)].toArray with hR7
  have sR7 : R7.size = b + 3 + pw + 5 + 48 + 1 := by simp [R7, sR6]
  have e67 : ExtA R6 R7 := ExtA.app R6 _
  -- B8: the cells
  have e17 : ExtA R1 R7 := e15.trans (e56.trans e67)
  have e57 : ExtA R5 R7 := e56.trans e67
  obtain ⟨M8, hB8, hl8, hv8⟩ := run_cellsOps impl κ inp R7 b (b + 3 + pw + 5 + 2)
    (b + 3 + pw + 5 + 25) kp (p0V κ fi r) kpv (by rw [sR7]; omega)
    (by rw [e17.rd (by rw [sR1]; omega), r1one])
    (Nat.lt_of_lt_of_le hkpr (e06.trans e67).1) (by rw [e06.trans e67 |>.rd hkpr])
    (fun v hv => ⟨by rw [sR7]; omega, by
      rw [e57.rd (by rw [sR5]; omega), r5 v hv]; rfl⟩)
    (fun v hv => ⟨by rw [sR7]; omega, by
      rw [show b + 3 + pw + 5 + 25 + v = R5.size + v by rw [sR5],
        e67.rd (by rw [sR6]; omega), hR6, rd_app]; simp [V6, hv, toK_k]⟩)
    pfCells (b + 2) (b + 3 + pw + 5 + 48) 0 (kpv * kpv) []
    (by rw [List.length_nil, Nat.add_zero, sR7]; omega)
    (by rw [app0, e17.rd (by rw [sR1]; omega), r1z])
    (by rw [List.length_nil, Nat.add_zero, sR7]; omega)
    (by rw [app0, hR7, ← sR6, rd_app0]; rfl)
  simp only [List.length_nil, Nat.add_zero, List.nil_append, sR7] at hB8 hv8
  set R8 := R7 ++ M8.toArray with hR8
  have sR8 : R8.size = b + 3 + pw + 5 + 48 + 1 + 26 * 9 := by simp [R8, sR7, hl8, pfCells]
  have e78 : ExtA R7 R8 := ExtA.app R7 M8
  -- B9: `Ŵ₀(P₀)`
  have e48 : ExtA R4 R8 := e45.trans (e57.trans e78)
  have r8w : rd R8 (b + 3 + pw + 5 + 1) = .k rsW := by
    rw [e48.rd (by rw [sR4]; omega), r4 1 (by omega)]; rfl
  have r8z : rd R8 (b + 2) = .k 0 := by rw [(e17.trans e78).rd (by omega), r1z]
  set cv := cellsVal (p0V κ fi r) kpv pfCells (kpv * kpv) 0
  set V9 : List Val := [if κ.isNode then .k cv else .k 0, .k (w0V impl κ fi r)]
  have hB9 : pureRun impl κ inp
      [.keep Kind.isNode (cellsAcc pfCells (b + 2) (b + 3 + pw + 5 + 48 + 1)) (b + 2),
       .addK (b + 3 + pw + 5 + 1) (b + 3 + pw + 5 + 48 + 1 + 26 * 9)] R8 [] =
      some (V9, true) := by
    have hca : cellsAcc pfCells (b + 2) (b + 3 + pw + 5 + 48 + 1) < R8.size := by
      by_contra hc'
      have h0 := hv8; rw [rd, Array.getElem?_eq_none (by simpa using hc')] at h0; cases h0
    rw [← sR8]
    simp only [pureRun, evalOp, List.nil_append, List.cons_append, rd_app, rd_app0, app0,
      rd_app_left _ _ (show b + 3 + pw + 5 + 1 < R8.size by rw [sR8]; omega),
      rd_app_left _ _ (show b + 2 < R8.size by rw [sR8]; omega), rd_app_left _ _ hca, r8w, r8z, hv8,
      List.getD_cons_succ, List.getD_cons_zero, Option.map_some, Bool.and_true]
    simp only [V9, w0V, cv, toK_k, rsW]
    cases κ.isNode <;> rfl
  set R9 := R8 ++ V9.toArray with hR9
  have sR9 : R9.size = b + 3 + pw + 5 + 48 + 1 + 26 * 9 + 2 := by simp [R9, sR8, V9]
  have e89 : ExtA R8 R9 := ExtA.app R8 V9
  have r9w : rd R9 (b + 3 + pw + 5 + 48 + 1 + 26 * 9 + 1) = .k (w0V impl κ fi r) := by
    rw [hR9, ← sR8, rd_app]; rfl
  -- B10: the levels
  have e09 : ExtA r R9 := e06.trans (e67.trans (e78.trans e89))
  have e39 : ExtA R3 R9 := e34.trans (e48.trans e89)
  have e19 : ExtA R1 R9 := e17.trans (e78.trans e89)
  obtain ⟨M10, hB10, hl10, hv10⟩ := run_lvsOps impl κ inp fi b (b + 1) (b + 3 + pw)
    (tailV κ fi r) R9 (by rw [sR9]; omega) (by rw [e19.rd (by rw [sR1]; omega), r1one])
    (by rw [sR9]; omega) (by rw [e19.rd (by rw [sR1]; omega), r1cu]) [1, 2, 3, 4]
    (b + 3 + pw + 5 + 48 + 1 + 26 * 9 + 1)
    (w0V impl κ fi r) R9 le_rfl (fun _ _ => rfl)
    (fun k hk => by
      refine ⟨fun x hx => Nat.lt_of_lt_of_le (mE k hk x hx) e09.1, by
        rw [sR9]; simp at hk; rcases hk with rfl | rfl | rfl | rfl <;> omega, ?_⟩
      have hk' : k - 1 < 4 ∧ k - 1 + 1 = k := by simp at hk; omega
      rw [e39.rd (by rw [sR3]; omega), r3T (k - 1) hk'.1, hk'.2])
    (by rw [sR9]; omega) r9w
  rw [sR9] at hB10 hv10
  rw [lvsV_congr impl fi (tailV κ fi r) r.size (fun x hx => e09.rd hx) [1, 2, 3, 4] _ mE] at hv10
  set R10 := R9 ++ M10.toArray with hR10
  have sR10 : R10.size = b + 3 + pw + 5 + 48 + 1 + 26 * 9 + 2 + lw := by
    simp [R10, sR9, hl10, hlw]
  have e910 : ExtA R9 R10 := ExtA.app R9 M10
  -- B11: `sf` and `eq(sf, ·)`
  set fb := b + 3 + pw + 5 + 48 + 1 + 26 * 9 + 2 + lw with hfb
  have e010 : ExtA r R10 := e09.trans e910
  set sfV := ((chals fi "Pf" 7).map fun x => (rd r x).toK).toArray
  set V11 : List Val := [.ak sfV, .ak (eqTab sfV)]
  have hB11 : pureRun impl κ inp [.packK (chals fi "Pf" 7), .eqTableK fb] R10 [] =
      some (V11, true) := by
    have hm : (chals fi "Pf" 7).map (fun x => (rd R10 x).toK) =
        (chals fi "Pf" 7).map (fun x => (rd r x).toK) :=
      List.map_congr_left fun x hx => by rw [e010.rd (mD x hx)]
    rw [← sR10]
    simp only [pureRun, evalOp, List.nil_append, app0, rd_app0, hm, Option.map_some,
      Bool.and_true]
    rfl
  set R11 := R10 ++ V11.toArray with hR11
  have sR11 : R11.size = fb + 2 := by simp [R11, sR10, V11]
  have e1011 : ExtA R10 R11 := ExtA.app R10 V11
  -- B12: `final̂(sf)`
  obtain ⟨M12, hB12, hl12, hv12⟩ := run_fhOps impl κ inp R11 (fb + 1) (eqTab sfV)
    (by rw [sR11]; omega) (by rw [hR11, ← sR10, rd_app]; rfl) (List.range 128) (b + 2) 0 []
    (by rw [List.length_nil, Nat.add_zero, sR11, hfb]; omega)
    (by rw [app0, (e19.trans (e910.trans e1011)).rd (by omega), r1z])
  simp only [List.length_nil, Nat.add_zero, List.nil_append, sR11] at hB12 hv12
  set R12 := R11 ++ M12.toArray with hR12
  have sR12 : R12.size = fb + 2 + 4 * 128 := by simp [R12, sR11, hl12]
  have e1112 : ExtA R11 R12 := ExtA.app R11 M12
  -- B13: the padding and the check
  have e012 : ExtA r R12 := e010.trans (e1011.trans e1112)
  have e112 : ExtA R1 R12 := e19.trans (e910.trans (e1011.trans e1112))
  have hWo : lvsOut fi [1, 2, 3, 4] (b + 3 + pw + 5 + 48 + 1 + 26 * 9 + 1)
      (b + 3 + pw + 5 + 48 + 1 + 26 * 9 + 2) < R10.size := by
    by_contra hc'
    have h0 := hv10; rw [rd, Array.getElem?_eq_none (by simpa [R10] using hc')] at h0; cases h0
  have hFo : fhOut (List.range 128) (b + 2) (fb + 2) < R12.size := by
    by_contra hc'
    have h0 := hv12; rw [rd, Array.getElem?_eq_none (by simpa [R12] using hc')] at h0; cases h0
  have r12W : rd R12 (lvsOut fi [1, 2, 3, 4] (b + 3 + pw + 5 + 48 + 1 + 26 * 9 + 1)
      (b + 3 + pw + 5 + 48 + 1 + 26 * 9 + 2)) = .k (wV impl κ fi r) := by
    rw [(e1011.trans e1112).rd hWo, hv10]; rfl
  have h5 : (chals fi "Pf" 7).getD 5 0 < r.size := mC _ (by simp)
  have h6 : (chals fi "Pf" 7).getD 6 0 < r.size := mC _ (by simp)
  have r12one : rd R12 b = .k 1 := by rw [e112.rd (by rw [sR1]; omega), r1one]
  obtain ⟨V13, hB13⟩ : ∃ V13, pureRun impl κ inp
      [.addK b ((chals fi "Pf" 7).getD 5 0), .addK b ((chals fi "Pf" 7).getD 6 0),
       .mulK (fb + 2 + 4 * 128) (fb + 2 + 4 * 128 + 1), .keep is32 b (fb + 2 + 4 * 128 + 2),
       .mulK (lvsOut fi [1, 2, 3, 4] (b + 3 + pw + 5 + 48 + 1 + 26 * 9 + 1)
         (b + 3 + pw + 5 + 48 + 1 + 26 * 9 + 2)) (fb + 2 + 4 * 128 + 3),
       .mulK (fb + 2 + 4 * 128 + 4) (fhOut (List.range 128) (b + 2) (fb + 2)),
       .assertEq (fb + 2 + 4 * 128 + 5) (claimN fi "Pf") allK] R12 [] =
      some (V13, relPf impl κ inp fi r) := by
    rw [show fb + 2 + 4 * 128 = R12.size from sR12.symm]
    simp only [pureRun, evalOp, List.nil_append, List.cons_append, app0, rd_app, rd_app0,
      rd_app_left _ _ (show b < R12.size by rw [sR12]; omega), r12one,
      e012.rd h5,
      rd_app_left _ _ (Nat.lt_of_lt_of_le h6 e012.1), e012.rd h6,
      rd_app_left _ _ (Nat.lt_of_lt_of_le hcNr e012.1), e012.rd hcNr,
      rd_app_left _ _ (Nat.lt_of_lt_of_le hWo (e1011.trans e1112).1), rd_app_left _ _ hFo, r12W,
      hv12,
      List.getD_cons_succ, List.getD_cons_zero, Option.map_some, allK, Bool.not_true,
      Bool.false_or, Bool.true_and, Bool.and_true]
    refine ex_some ?_
    unfold relPf
    refine congrArg (fun z : K => (Val.k z).eqv (rd r (claimN fi "Pf"))) ?_
    simp only [toK_k, padV, finHat, is32, decide_eq_true_eq]
    by_cases hκ : κ = .L32
    · simp only [hκ, ↓reduceIte, toK_k]; rfl
    · simp only [hκ, ↓reduceIte, toK_k]; rfl
  exact ⟨_, pr_seq impl κ inp hB1 (pr_seq impl κ inp hB2 (pr_seq impl κ inp hB3
    (pr_seq impl κ inp hB4 (pr_seq impl κ inp hB5 (pr_seq impl κ inp hB6 (pr_seq impl κ inp hB7
    (pr_seq impl κ inp hB8 (pr_seq impl κ inp hB9 (pr_seq impl κ inp hB10
    (pr_seq impl κ inp hB11 (pr_seq impl κ inp hB12 hB13)))))))))))⟩

/-! ### Meaning lemmas and controls for `finPf` -/

/-- **`fhVal_eq`**: `final̂`'s accumulator is `A + Σ_c final[c]·E[c]`. -/
theorem fhVal_eq (inp : Input) (E : Array K) : ∀ (cs : List ℕ) (A : K),
    fhVal inp E cs A = A + (cs.map fun c => finV inp c * E.getD c 0).sum
  | [], A => by simp [fhVal]
  | c :: cs, A => by rw [fhVal, fhVal_eq inp E cs, List.map_cons, List.sum_cons, add_assoc]

/-- **`cellsVal_eq`**: the cells' accumulator is `A + Σ_k (pw·κ′^k)·eq(cell_k, ρ)`. -/
theorem cellsVal_eq (ρ : Array K) (kp : F) : ∀ (cs : List ℕ) (pw : F) (A : K),
    cellsVal ρ kp cs pw A =
      A + ((List.range cs.length).map fun k => K.smulF (pw * kp ^ k) (eqCellK ρ (cs.getD k 0))).sum
  | [], _, A => by simp [cellsVal]
  | c :: cs, pw, A => by
    have h2 : (List.range cs.length).map
          (fun k => K.smulF (pw * kp * kp ^ k) (eqCellK ρ (cs.getD k 0))) =
        (List.range cs.length).map ((fun k => K.smulF (pw * kp ^ k)
          (eqCellK ρ ((c :: cs).getD k 0))) ∘ Nat.succ) :=
      List.map_congr_left fun k _ => by
        simp only [Function.comp_apply, List.getD_cons_succ, mul_assoc, ← pow_succ']
    rw [cellsVal, cellsVal_eq ρ kp cs, List.length_cons, List.range_succ_eq_map, List.map_cons,
      List.sum_cons, List.map_map, h2, pow_zero, mul_one, List.getD_cons_zero, add_assoc]

/-- **`relPf_iff`**: `finPf`'s flag holds exactly when `claimN(Pf)` is the K value
`Ŵ₄(P₄)·pad·final̂(sf)`. -/
theorem relPf_iff (impl : OpImpl) (κ : Kind) (inp : Input) (fi : FinIn) (r : Array Val) :
    relPf impl κ inp fi r = true ↔
      rd r (claimN fi "Pf") = .k (wV impl κ fi r * padV κ fi r * finHat inp fi r) := by
  unfold relPf
  cases h : rd r (claimN fi "Pf") <;> simp [Val.eqv, eq_comm]

/-- Positive control: at `ρ = 0` the cell `0` has weight `1`. -/
theorem eqCellK_zero : eqCellK (Array.replicate 23 0) 0 = 1 := by
  simp [eqCellK, List.range_succ]

/-- Negative control: at `ρ = 0` the cell `1` has weight `0` (its bit 0 is set). -/
theorem eqCellK_one : eqCellK (Array.replicate 23 0) 1 = 0 := by
  simp [eqCellK, List.range_succ]

/-- The public cells: nine distinct addresses, the first M's `one` cell. -/
theorem pfCells_spec :
    pfCells.length = 9 ∧ pfCells.Nodup ∧ pfCells.head? = some Layout.oneCell := by
  refine ⟨rfl, ?_, rfl⟩
  simp only [pfCells, Layout.oneCell, Layout.mBase, Layout.chainN]
  decide

/-- `finPf` builds 17 points (`pfPts`'s index table; revision 3.13). -/
theorem pfPts_length (fi : FinIn) : (pfPts fi).length = 17 := by simp [pfPts]

end FR
