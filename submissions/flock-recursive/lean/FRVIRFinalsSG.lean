-- New for `flock-recursive` (BLUEPRINT §7, A.9; stage S-G).
import FRVIRFinalsSF
import FRNodeLayout

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

/-- The nodes of `S`, as `quirky_claim_split` indexes them. -/
def sNodeF (b : Fin 64) : F := skipNode (Fin.castLE (by norm_num) b)

theorem foldl_mul_eq {α : Type*} (g : α → F) :
    ∀ (xs : List α) (c : F), xs.foldl (fun a j => a * g j) c = c * (xs.map g).prod
  | [], c => by simp
  | x :: xs, c => by rw [List.foldl_cons, foldl_mul_eq g xs, List.map_cons, List.prod_cons]; ring

theorem xS_of_lt {j : ℕ} (hj : j < 64) : xS j = sNodeF ⟨j, hj⟩ := by
  simp only [xS, sNodeF, Nat.mod_eq_of_lt (show j < 128 by omega)]; rfl

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
  congr 1
  · refine Finset.prod_congr rfl fun j hj => ?_
    rw [hx j hj, sub_eq_add_neg, CharTwo.neg_eq]
  · congr 1
    refine Finset.prod_congr rfl fun j hj => ?_
    rw [hx j hj, sub_eq_add_neg, CharTwo.neg_eq]

/-! ## `finP i` (A.9) -/

/-- Level `i`'s phase `k` outputs (`k = 0 … 4`: `P1, C, P2, Q, P3`). -/
def lvOuts (fi : FinIn) (i k : ℕ) : List Reg := fi.outs.getD (phaseIx "P1" + 5 * i + k) []

/-- `P1.i`'s first and last claims. -/
def p1Claim0 (fi : FinIn) (i : ℕ) : Reg := (lvOuts fi i 0).headD 0
def p1ClaimN (fi : FinIn) (i : ℕ) : Reg := (lvOuts fi i 0).getLastD 0

/-- The column folds `y_q` of level `i`. -/
def ysOf (fi : FinIn) (i : ℕ) : List Reg := lvOuts fi i 3

/-- `κ_c`: the first 9 coordinates of `P3.i`. -/
def kcOf (fi : FinIn) (i : ℕ) : List Reg := ((lvOuts fi i 4).drop 1).take 9

/-- `acc + Σ_q e[q]·y_q`, three registers per `q` (`getF`, `mulKF`, `addK`). -/
def accOps (e : Reg) : List Reg → ℕ → Reg → ℕ → List Op
  | [], _, _, _ => []
  | y :: ys, q, acc, b =>
    [.getF e q, .mulKF y b, .addK acc (b + 1)] ++ accOps e ys (q + 1) (b + 2) (b + 3)

/-- The register `accOps` leaves its sum in. -/
def accOut : Reg → ℕ → List Reg → Reg
  | acc, _, [] => acc
  | _, b, _ :: ys => accOut (b + 2) (b + 3) ys

/-- **`finP i`, `i < 4`**: `claim0(P1.(i+1)) = claimN(P1.i) + Σ_q eq(κ_c, bits₉(q))·y_q`. Exports
the batched claim. -/
def finPLow (i : ℕ) : FinField := fun fi b =>
  let out := accOut (b + 3) (b + 4) (ysOf fi i)
  ([.packF (kcOf fi i), .eqTable b, .const (fun _ => .k 0), .addK (p1ClaimN fi i) (b + 2)] ++
    accOps (b + 1) (ysOf fi i) 0 (b + 3) (b + 4) ++
    [.assertEq out (p1Claim0 fi (i + 1)) allK], [out])

/-- One Horner layer: `x'[c] = x[c] + w·x[c + n]` for `c < n` (`xs` of length `2n`), two registers
per `c`. -/
def layerOps (w : Reg) (xs : List Reg) (n b : ℕ) : ℕ → List Op
  | 0 => []
  | k + 1 => layerOps w xs n b k ++ [.mulK w (xs.getD (k + n) 0), .addK (xs.getD k 0) (b + 2 * k)]

/-- The registers a layer leaves. -/
def layerOut (n b : ℕ) : List Reg := (List.range n).map fun c => b + 2 * c + 1

/-- Horner from bit `v - 1` down to bit `0` (`ws[v]` the weight of bit `v`), from `b`. -/
def hornerKOps (ws : List Reg) : ℕ → List Reg → ℕ → List Op
  | 0, _, _ => []
  | v + 1, xs, b => layerOps (ws.getD v 0) xs (2 ^ v) b (2 ^ v) ++
      hornerKOps ws v (layerOut (2 ^ v) b) (b + 2 * 2 ^ v)

/-- The register Horner leaves its value in. -/
def hornerKOut : ℕ → List Reg → ℕ → Reg
  | 0, xs, _ => xs.headD 0
  | v + 1, _, b => hornerKOut v (layerOut (2 ^ v) b) (b + 2 * 2 ^ v)

/-- Registers per position at level 4: 7 `tensorW`, then `2·(2^7 − 1)` Horner registers. -/
def encW : ℕ := 7 + 2 * (2 ^ 7 - 1)

/-- `Enc₄(final)[p] = y`: `Ŵ_v(D[p])` for `v < 7` (`units` the registers of `e_v`), Horner over
`fin` (the 128 final-message registers), the check. -/
def encOps (units fin : List Reg) (j y b : ℕ) : List Op :=
  (List.range 7).map (fun v => .tensorW j (units.getD v 0)) ++
    hornerKOps ((List.range 7).map (b + ·)) 7 fin (b + 7) ++
    [.assertEq (hornerKOut 7 fin (b + 7)) y allK]

/-- The unit vector `e_v` of `K^7`. -/
def unitK (v : ℕ) : Array K := ((List.range 7).map fun u => if u = v then (1 : K) else 0).toArray

/-- **`finP 4`**: `y_q = Enc₄(final)[p_q]` for every `q`, and Pf's initial claim is `claimN(P1.4)`.
Registers: the 128 final elements, the 7 unit vectors, then `encW` per position. -/
def finP4 : FinField := fun fi b =>
  let fin := (List.range 128).map (b + ·)
  let units := (List.range 7).map (b + 128 + ·)
  ((List.range 128).map (fun c => .piElemK fFinal (32 * c)) ++
    (List.range 7).map (fun v => .const fun _ => .ak (unitK v)) ++
    (List.range (ysOf fi 4).length).flatMap (fun q =>
      encOps units fin ((ysOf fi 4).getD q 0 - 3) ((ysOf fi 4).getD q 0) (b + 135 + encW * q)) ++
    [.assertEq (claim0 fi "Pf") (p1ClaimN fi 4) allK], [])

/-- **`finP i`** (A.9). -/
def finP (i : ℕ) : FinField := if i < 4 then finPLow i else finP4

/-! ## `finP i < 4` runs to its relation -/

/-- `A + Σ_k e[q + k]·Y_k`, as `accOps` accumulates it. -/
def accVal (E : Array F) : List K → ℕ → K → K
  | [], _, A => A
  | y :: ys, q, A => accVal E ys (q + 1) (A + K.smulF (E.getD q 0) y)

theorem accVal_eq (E : Array F) : ∀ (Ys : List K) (q : ℕ) (A : K),
    accVal E Ys q A =
      A + ((List.range Ys.length).map fun k => K.smulF (E.getD (q + k) 0) (Ys.getD k 0)).sum
  | [], _, A => by simp [accVal]
  | y :: ys, q, A => by
    rw [accVal, accVal_eq E ys (q + 1), List.length_cons, List.range_succ_eq_map, List.map_cons,
      List.sum_cons, List.map_map]
    simp only [Nat.add_zero, List.getD_cons_zero, Function.comp_def, List.getD_cons_succ,
      Nat.add_succ, Nat.succ_add]
    rw [add_assoc]

section RunP
variable (impl : OpImpl) (κ : Kind) (inp : Input) (r : Array Val)

theorem run_accOps (e : Reg) (E : Array F) : ∀ (ys : List Reg) (q acc : ℕ) (A : K) (L : List Val),
    (∀ y ∈ ys, y < r.size) → e < r.size + L.length → (rd (r ++ L.toArray) e).toAF = E →
    acc < r.size + L.length → rd (r ++ L.toArray) acc = .k A →
    ∃ M, pureRun impl κ inp (accOps e ys q acc (r.size + L.length)) r L = some (L ++ M, true) ∧
      rd (r ++ (L ++ M).toArray) (accOut acc (r.size + L.length) ys) =
        .k (accVal E (ys.map fun y => (rd r y).toK) q A)
  | [], q, acc, A, L, _, _, _, _, hA =>
    ⟨[], by simp [accOps, pureRun], by simpa [accOut, accVal] using hA⟩
  | y :: ys, q, acc, A, L, hy, he, hE, hacc, hA => by
    have hy0 : y < r.size := hy y (List.mem_cons_self ..)
    set b := r.size + L.length with hb
    set v₁ : Val := .f (E.getD q 0)
    set v₂ : Val := .k (K.smulF (E.getD q 0) (rd r y).toK)
    set v₃ : Val := .k (A + K.smulF (E.getD q 0) (rd r y).toK)
    have h1 : evalOp impl κ inp (r ++ L.toArray) (.getF e q) = .vals [v₁] true := by
      simp [evalOp, hE, v₁]
    have h2 : evalOp impl κ inp (r ++ (L ++ [v₁]).toArray) (.mulKF y b) = .vals [v₂] true := by
      simp only [evalOp, hb, rd_new1, rd_app_left _ _ hy0, v₂, v₁, Val.toF]
    have h3 : evalOp impl κ inp (r ++ (L ++ [v₁] ++ [v₂]).toArray) (.addK acc (b + 1)) =
        .vals [v₃] true := by
      have e1 : b + 1 = r.size + (L ++ [v₁]).length := by simp [hb]; omega
      have hacc' : acc < r.size + L.length := hacc
      simp only [evalOp]
      rw [e1, rd_new1, List.append_assoc, rd_pre r hacc', hA]; rfl
    obtain ⟨M, hM, hout⟩ := run_accOps e E ys (q + 1) (b + 2)
      (A + K.smulF (E.getD q 0) (rd r y).toK)
      (L ++ [v₁] ++ [v₂] ++ [v₃]) (fun x hx => hy x (List.mem_cons_of_mem _ hx))
      (Nat.lt_of_lt_of_le he (by simp [hb]))
      (by rw [List.append_assoc, List.append_assoc, rd_pre r he, hE])
      (by simp only [List.length_append, List.length_singleton]; omega) (by
        have e2 : b + 2 = r.size + (L ++ [v₁] ++ [v₂]).length := by simp [hb]; omega
        rw [e2, rd_new1])
    have e3 : r.size + (L ++ [v₁] ++ [v₂] ++ [v₃]).length = b + 3 := by simp [hb]; omega
    rw [e3] at hM hout
    refine ⟨[v₁, v₂, v₃] ++ M, ?_, ?_⟩
    · simp only [accOps, List.cons_append, List.nil_append]
      rw [pr_op impl κ inp r h1, pr_op impl κ inp r h2, pr_op impl κ inp r h3, hM]
      simp
    · simp only [accOut, List.map_cons, accVal]
      simpa using hout

variable (fi : FinIn)

/-- `eq(κ_c, ·)` on the 512 indices `bits₉(q)`. -/
def kcTab (i : ℕ) : Array F := eqTab ((kcOf fi i).map (fv r)).toArray

/-- The batched claim `claimN(P1.i) + Σ_q eq(κ_c, bits₉(q))·y_q`. -/
def vNext (i : ℕ) : K :=
  accVal (kcTab r fi i) ((ysOf fi i).map fun y => (rd r y).toK) 0 (rd r (p1ClaimN fi i)).toK

/-- **A.9's `finP i` relation, `i < 4`**: the batched claim is `P1.(i+1)`'s initial claim. -/
def relPLow (i : ℕ) : Bool := (Val.k (vNext r fi i)).eqv (rd r (p1Claim0 fi (i + 1)))

/-- **`flag_finPLow`**: `finP i` (`i < 4`) asks nothing; its flag is `relPLow`; its export is the
batched claim. -/
theorem flag_finPLow (i : ℕ)
    (hin : ∀ x ∈ kcOf fi i ++ ysOf fi i ++ [p1ClaimN fi i, p1Claim0 fi (i + 1)], x < r.size) :
    ∃ L, pureRun impl κ inp (finPLow i fi r.size).1 r [] = some (L, relPLow r fi i) ∧
      rd (r ++ L.toArray) ((finPLow i fi r.size).2.headD 0) = .k (vNext r fi i) := by
  simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hin
  have hk : ∀ x ∈ kcOf fi i, x < r.size := fun x hx => hin x (.inl (.inl hx))
  have hy : ∀ x ∈ ysOf fi i, x < r.size := fun x hx => hin x (.inl (.inr hx))
  have hN := hin _ (.inr (.inl rfl)); have h0 := hin _ (.inr (.inr rfl))
  set b := r.size
  set v₀ : Val := .af (((kcOf fi i).map (fv r)).toArray)
  set v₁ : Val := .af (kcTab r fi i)
  set v₂ : Val := .k 0
  set v₃ : Val := .k ((rd r (p1ClaimN fi i)).toK)
  have e0 : evalOp impl κ inp (r ++ ([] : List Val).toArray) (.packF (kcOf fi i)) =
      .vals [v₀] true := by
    simp only [evalOp, v₀]; rw [map_rd_app r [] _ hk]
  have e1 : evalOp impl κ inp (r ++ ([] ++ [v₀]).toArray) (.eqTable b) = .vals [v₁] true := by
    simp only [evalOp, v₁, kcTab]; rw [show b = r.size + 0 from rfl, rd_append_right]; rfl
  have e2 : evalOp impl κ inp (r ++ ([] ++ [v₀] ++ [v₁]).toArray) (.const fun _ => .k 0) =
      .vals [v₂] true := rfl
  have e3 : evalOp impl κ inp (r ++ ([] ++ [v₀] ++ [v₁] ++ [v₂]).toArray)
      (.addK (p1ClaimN fi i) (b + 2)) =
      .vals [v₃] true := by
    simp only [evalOp, v₃]
    rw [rd_app_left _ _ hN, show b + 2 = r.size + 2 from rfl, rd_app]
    simp [v₂]; rfl
  obtain ⟨M, hM, hout⟩ := run_accOps impl κ inp r (b + 1) (kcTab r fi i) (ysOf fi i) 0 (b + 3)
    (rd r (p1ClaimN fi i)).toK ([v₀] ++ [v₁] ++ [v₂] ++ [v₃]) hy (by simp [b]) (by
      rw [show b + 1 = r.size + 1 from rfl, rd_app]; rfl) (by simp [b]) (by
      rw [show b + 3 = r.size + 3 from rfl, rd_app]; rfl)
  have e4 : r.size + ([v₀] ++ [v₁] ++ [v₂] ++ [v₃]).length = b + 4 := by simp [b]
  rw [e4] at hM hout
  refine ⟨[v₀] ++ [v₁] ++ [v₂] ++ [v₃] ++ M, ?_, ?_⟩
  · simp only [finPLow, List.cons_append, List.nil_append]
    rw [pr_op impl κ inp r e0, pr_op impl κ inp r e1, pr_op impl κ inp r e2,
      pr_op impl κ inp r e3]
    rw [List.nil_append, pr_app impl κ inp r hM]
    simp only [pureRun, evalOp, allK, Bool.not_true, Bool.false_or]
    rw [hout, rd_app_left _ _ h0]
    simp [relPLow, vNext]
  · simp only [finPLow, List.headD_cons]
    exact hout

/-! ### `finP 4` -/

/-- Horner's value: bit `v - 1` first, `x'[c] = x[c] + W_{v-1}·x[c + 2^(v-1)]`. -/
def hornerVal (W : ℕ → K) : ℕ → (ℕ → K) → K
  | 0, X => X 0
  | v + 1, X => hornerVal W v fun c => X c + W v * X (c + 2 ^ v)

/-- Ops that append one value each, the same on every register file. -/
theorem run_indep (g : Op → Val) : ∀ (os : List Op) (L : List Val),
    (∀ op ∈ os, ∀ regs, evalOp impl κ inp regs op = .vals [g op] true) →
    pureRun impl κ inp os r L = some (L ++ os.map g, true)
  | [], L, _ => by simp [pureRun]
  | op :: os, L, h => by
    rw [pr_op impl κ inp r (h op (List.mem_cons_self ..) _),
      run_indep g os _ fun o ho => h o (List.mem_cons_of_mem _ ho)]
    simp

/-- Ops that append one value each, reading only registers below `r.size + L.length`. -/
theorem run_frozen (L : List Val) (g : Op → Val) : ∀ (os : List Op) (X : List Val),
    (∀ op ∈ os, ∀ Y, evalOp impl κ inp (r ++ (L ++ Y).toArray) op = .vals [g op] true) →
    pureRun impl κ inp os r (L ++ X) = some (L ++ X ++ os.map g, true)
  | [], X, _ => by simp [pureRun]
  | op :: os, X, h => by
    rw [pr_op impl κ inp r (h op (List.mem_cons_self ..) X), List.append_assoc,
      run_frozen L g os (X ++ [g op]) fun o ho => h o (List.mem_cons_of_mem _ ho)]
    simp

/-- **One Horner layer**: `k` pairs from `b = r.size + |L|`. -/
theorem run_layer (w : Reg) (W : K) (xs : List Reg) (X : ℕ → K) (n : ℕ) (L : List Val)
    (hw : w < r.size + L.length) (hW : rd (r ++ L.toArray) w = .k W)
    (hx : ∀ c < 2 * n, xs.getD c 0 < r.size + L.length ∧
      rd (r ++ L.toArray) (xs.getD c 0) = .k (X c)) :
    ∀ k ≤ n, ∃ M,
      pureRun impl κ inp (layerOps w xs n (r.size + L.length) k) r L = some (L ++ M, true) ∧
      M.length = 2 * k ∧ ∀ c < k,
        rd (r ++ (L ++ M).toArray) (r.size + L.length + 2 * c + 1) = .k (X c + W * X (c + n))
  | 0, _ => ⟨[], by simp [layerOps, pureRun], rfl, fun c hc => absurd hc (Nat.not_lt_zero _)⟩
  | k + 1, hk => by
    obtain ⟨M, hM, hlen, hval⟩ := run_layer w W xs X n L hw hW hx k (by omega)
    set b := r.size + L.length
    obtain ⟨h1, h1v⟩ := hx (k + n) (by omega)
    obtain ⟨h2, h2v⟩ := hx k (by omega)
    set u₁ : Val := .k (W * X (k + n))
    set u₂ : Val := .k (X k + W * X (k + n))
    have e1 : evalOp impl κ inp (r ++ (L ++ M).toArray) (.mulK w (xs.getD (k + n) 0)) =
        .vals [u₁] true := by
      simp only [evalOp, rd_pre r hw, rd_pre r h1, hW, h1v]; rfl
    have e2 : evalOp impl κ inp (r ++ (L ++ M ++ [u₁]).toArray) (.addK (xs.getD k 0) (b + 2 * k)) =
        .vals [u₂] true := by
      have eb : b + 2 * k = r.size + (L ++ M).length := by simp [b, hlen]; omega
      simp only [evalOp]
      rw [eb, rd_new1, List.append_assoc, rd_pre r h2, h2v]; rfl
    refine ⟨M ++ [u₁, u₂], ?_, by simp [hlen]; omega, fun c hc => ?_⟩
    · simp only [layerOps]
      rw [pr_app impl κ inp r hM, pr_op impl κ inp r e1, pr_op impl κ inp r e2]
      simp [pureRun]
    · by_cases hck : c < k
      · rw [show L ++ (M ++ [u₁, u₂]) = L ++ M ++ [u₁, u₂] by simp,
          rd_pre r (by simp [hlen]; omega), hval c hck]
      · have hc' : c = k := by omega
        subst hc'
        have : r.size + L.length + 2 * c + 1 = r.size + (L ++ M ++ [u₁]).length := by
          simp [hlen]; omega
        rw [this, show L ++ (M ++ [u₁, u₂]) = L ++ M ++ [u₁] ++ [u₂] by simp, rd_new1]

theorem layerOut_getD {n b c : ℕ} (hc : c < n) : (layerOut n b).getD c 0 = b + 2 * c + 1 := by
  simp [layerOut, hc]

/-- **Horner over `v` layers**. -/
theorem run_horner (ws : List Reg) (W : ℕ → K) :
    ∀ (v : ℕ) (xs : List Reg) (X : ℕ → K) (L : List Val),
    (∀ u < v, ws.getD u 0 < r.size + L.length ∧ rd (r ++ L.toArray) (ws.getD u 0) = .k (W u)) →
    (∀ c < 2 ^ v, xs.getD c 0 < r.size + L.length ∧ rd (r ++ L.toArray) (xs.getD c 0) = .k (X c)) →
    ∃ M, pureRun impl κ inp (hornerKOps ws v xs (r.size + L.length)) r L = some (L ++ M, true) ∧
      M.length = 2 * (2 ^ v - 1) ∧
      rd (r ++ (L ++ M).toArray) (hornerKOut v xs (r.size + L.length)) = .k (hornerVal W v X)
  | 0, xs, X, L, _, hx => by
    refine ⟨[], by simp [hornerKOps, pureRun], rfl, ?_⟩
    have := (hx 0 (by norm_num)).2
    cases xs with
    | nil => simpa [hornerKOut, hornerVal] using this
    | cons x _ => simpa [hornerKOut, hornerVal] using this
  | v + 1, xs, X, L, hw, hx => by
    obtain ⟨hw1, hW⟩ := hw v (by omega)
    obtain ⟨M₁, h1, hl1, hv1⟩ := run_layer impl κ inp r (ws.getD v 0) (W v) xs X (2 ^ v) L hw1 hW
      (fun c hc => hx c (by rw [pow_succ]; omega)) (2 ^ v) le_rfl
    have hb : r.size + (L ++ M₁).length = (r.size + L.length) + 2 * 2 ^ v := by simp [hl1]; omega
    obtain ⟨M₂, h2, hl2, hv2⟩ := run_horner ws W v (layerOut (2 ^ v) (r.size + L.length))
      (fun c => X c + W v * X (c + 2 ^ v)) (L ++ M₁)
      (fun u hu => by
        obtain ⟨a, a'⟩ := hw u (by omega)
        exact ⟨Nat.lt_of_lt_of_le a (by simp only [List.length_append]; omega),
          by rw [rd_pre r a, a']⟩)
      (fun c hc => by
        rw [layerOut_getD hc]
        refine ⟨?_, hv1 c hc⟩
        rw [hb, Nat.add_assoc]
        exact Nat.add_lt_add_left (show 2 * c + 1 < 2 * 2 ^ v by omega) _)
    rw [hb] at h2 hv2
    refine ⟨M₁ ++ M₂, ?_, ?_, ?_⟩
    · simp only [hornerKOps]
      rw [pr_app impl κ inp r h1, h2]; simp
    · simp [hl1, hl2, pow_succ]; have := Nat.one_le_two_pow (n := v); omega
    · simp only [hornerKOut, hornerVal]
      simpa using hv2

/-- The final message's element `c` (A.3's field `final`). -/
def finV (c : ℕ) : K := K.ofBytes (bytesAt inp.π (absOff fFinal (32 * c)) 32)

/-- `Enc₄(final)[p]` as `encOps` computes it: Horner with `W_v = tensorW p e_v`. -/
def encVal (p : ℕ) : K := hornerVal (fun v => impl.tensorW p (unitK v)) 7 (finV inp)

/-- The value `tensorW j u` the frozen `tensorW` ops append (`default` for other ops). -/
def twVal (L : List Val) : Op → Val
  | .tensorW j u => .k (impl.tensorW (rd r j).toN (rd (r ++ L.toArray) u).toAK)
  | _ => default

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

/-- `piElemK` and `const` values (the ops of `finP 4` that read no register). -/
def p4Val : Op → Val
  | .piElemK f o => .k (K.ofBytes (bytesAt inp.π (absOff f o) 32))
  | .const c => c κ
  | _ => default

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

/-- **`hornerVal_eq`**: Horner's value is `Σ_{c < 2^v} X c · Π_{u < v} W_u^{bit_u(c)}`; with
`W_u = Ŵ_u(D[p])` this is `Enc(final)[p]` in the novel basis (`FRRS.novelX`). -/
theorem hornerVal_eq (W : ℕ → K) : ∀ (v : ℕ) (X : ℕ → K), hornerVal W v X =
    ∑ c ∈ Finset.range (2 ^ v), X c * ∏ u ∈ Finset.range v, (if c.testBit u then W u else 1)
  | 0, X => by simp [hornerVal]
  | v + 1, X => by
    rw [hornerVal, hornerVal_eq W v, pow_succ, mul_two, Finset.sum_range_add,
      ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun c hc => ?_
    have hc' : c < 2 ^ v := Finset.mem_range.mp hc
    rw [Finset.prod_range_succ, Finset.prod_range_succ, Nat.testBit_lt_two_pow hc',
      add_comm (2 ^ v) c, ← Nat.add_comm, Nat.testBit_two_pow_add_eq, Nat.testBit_lt_two_pow hc']
    have hp : ∏ u ∈ Finset.range v, (if (2 ^ v + c).testBit u then W u else 1) =
        ∏ u ∈ Finset.range v, (if c.testBit u then W u else 1) :=
      Finset.prod_congr rfl fun u hu => by rw [Nat.testBit_two_pow_add_gt (Finset.mem_range.mp hu)]
    rw [hp]; simp only [Bool.false_eq_true, ↓reduceIte, Bool.not_false, mul_one]; ring

theorem noAsk_accOps (e : Reg) : ∀ ys q acc b, (accOps e ys q acc b).filterMap Op.item? = []
  | [], _, _, _ => rfl
  | _ :: ys, q, acc, b => by
    simp only [accOps, List.cons_append, List.nil_append, List.filterMap_cons, Op.item?,
      noAsk_accOps e ys]

theorem noAsk_layerOps (w : Reg) (xs : List Reg) (n b : ℕ) :
    ∀ k, (layerOps w xs n b k).filterMap Op.item? = []
  | 0 => rfl
  | k + 1 => by simp [layerOps, Op.item?, noAsk_layerOps w xs n b k]

theorem noAsk_hornerKOps (ws : List Reg) : ∀ v xs b, (hornerKOps ws v xs b).filterMap Op.item? = []
  | 0, _, _ => rfl
  | v + 1, xs, b => by simp [hornerKOps, noAsk_layerOps, noAsk_hornerKOps ws v]

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

/-- A coordinate of a K point: an F register (embedded in K), a K register, or a constant. -/
inductive PtSrc where
  | f (x : Reg)
  | k (x : Reg)
  | c (v : K)

/-- The op that puts a coordinate in a register (`one`, `z0`: registers holding `1`, `0` of K). -/
def srcOp (one z0 : Reg) : PtSrc → Op
  | .f x => .mulKF one x
  | .k x => .addK x z0
  | .c v => .const fun _ => .k v

/-- A K point from `b`: its coordinates, then `packK`; the point lands at `b + |src|`. -/
def ptOps (one z0 : Reg) (src : List PtSrc) (b : ℕ) : List Op :=
  src.map (srcOp one z0) ++ [.packK ((List.range src.length).map (b + ·))]

/-- Points, one after the other. -/
def ptsOps (one z0 : Reg) : List (List PtSrc) → ℕ → List Op
  | [], _ => []
  | s :: ss, b => ptOps one z0 s b ++ ptsOps one z0 ss (b + s.length + 1)

/-- The register of point `j`. -/
def ptsOut : List (List PtSrc) → ℕ → ℕ → ℕ
  | [], b, _ => b
  | s :: _, b, 0 => b + s.length
  | s :: ss, b, j + 1 => ptsOut ss (b + s.length + 1) j

/-- The registers `ptsOps` appends. -/
def ptsW (ss : List (List PtSrc)) : ℕ := (ss.map (·.length + 1)).sum

/-- `sᵢ`: P1.i's fold challenges (K). -/
def sRegs (fi : FinIn) (i : ℕ) : List Reg := ((lvOuts fi i 0).drop 1).take (lvlStar i).ell

/-- `Pₖ[1..]` (`k = 1 … 4`) at `m`: `sⱼ[1..]` for `j = k … 4`, then Pf's first `m − 25`
challenges. -/
def tailRegs (fi : FinIn) (m k : ℕ) : List Reg :=
  (List.range' k (5 - k)).flatMap (fun j => (sRegs fi j).drop 1) ++ (chals fi "Pf" 7).take (m - 25)

/-- `P₀ = s₀ ++ P₁[1..]`, the level-0 point (`m − 7` coordinates). -/
def p0Regs (fi : FinIn) (m : ℕ) : List Reg := sRegs fi 0 ++ tailRegs fi m 1

/-- The Z claim's outer point at `m` (native `r[1..]`): `ρ₂ … ρ₇`, then Z1's `m − 13` free
coordinates. -/
def zSrc (fi : FinIn) (m : ℕ) : List PtSrc :=
  ((List.ofFn pinnedRho).drop 1).map (fun x => .c (K.ofF x)) ++
    ((coordsR fi "Z1").take (m - 13)).map .f

/-- The Lc claim's outer point: L2's challenges `7 … 13`, then Z3's real challenges from `8`. -/
def lcSrc (fi : FinIn) (m : ℕ) : List PtSrc :=
  ((chals fi "L2" 14).drop 7).map .f ++ (((chals fi "Z3" 26).take (m - 6)).drop 8).map .f

/-- The Sh claim's outer point: S2's position challenges `7 … 9`, four zeros, S2's `m − 14` block
challenges. -/
def shSrc (fi : FinIn) (m : ℕ) : List PtSrc :=
  (((chals fi "S2" 28).drop (m - 7)).take 3).map .f ++ List.replicate 4 (.c 0) ++
    ((chals fi "S2" 28).take (m - 14)).map .f

/-- The E4 claim's outer point (`m = 30`, revisions 3.12–3.13): all of E4's 23 challenges `r′` (RS
claim 4, `f̂(r′)`, has the packing basis as its inner weights). -/
def eSrc (fi : FinIn) : List PtSrc := (chals fi "E4" 23).map .f

/-- The points `finPf` builds: the claim points `0 … 6` (Z, Lc, Sh at `m = 32, 30`; E4's `r′`), the
tails `P₁[1..] … P₄[1..]` at `m = 32` (`7 … 10`) and `m = 30` (`11 … 14`), `P₀` (`15`, `16`). -/
def pfPts (fi : FinIn) : List (List PtSrc) :=
  [zSrc fi 32, zSrc fi 30, lcSrc fi 32, lcSrc fi 30, shSrc fi 32, shSrc fi 30, eSrc fi] ++
    (List.range 4).map (fun k => (tailRegs fi 32 (k + 1)).map .k) ++
    (List.range 4).map (fun k => (tailRegs fi 30 (k + 1)).map .k) ++
    [(p0Regs fi 32).map .k, (p0Regs fi 30).map .k]

/-- The `m = 32` kind. -/
def is32 : KC Bool := fun κ => decide (κ = .L32)

/-- The claim points `rsWeight` takes (indices into `pfPts`): three for a leaf, four for a node
(Z, Lc, Sh, E4: `finRS`'s order, revision 3.13). -/
def rsPtIx : KC (List ℕ) := fun κ =>
  match κ with
  | .L32 => [0, 2, 4]
  | .P30 => [1, 3, 5]
  | .N30 => [1, 3, 5, 6]

/-- **The public cells** (A.7's order, the nine of `finB′`'s `pubH`): M's `one` cell, then slot
1's and slot 2's seed payload elements `0 … 3` (`vk`, `c` halves) as `Node.seedCell`. The six zero
padding cells are not claimed (`finB′` adds nothing for them). -/
def pfCells : List ℕ := Layout.oneCell :: (List.range 2).flatMap fun σ =>
  (List.range 4).map fun e => (σ * Layout.chainN + (1 + e) / 4) * 128 + 4 + (1 + e) % 4

/-- `acc · Π xs` (`mulK` from the left; the product lands at `b + |xs| − 1`). -/
def prodKOps : List Reg → Reg → ℕ → List Op
  | [], _, _ => []
  | x :: xs, acc, b => .mulK acc x :: prodKOps xs b (b + 1)

/-- One cell (width 26): `eq(cell, ρ)` from `one` over `ρ_v` (register `g + v`, bit `v` set) or
`1 + ρ_v` (`h + v`); then `acc + κ′^(k+2)·eq` (the power in `pw`), then the next power. -/
def cellOps (one g h kp : Reg) (cell acc pw b : ℕ) : List Op :=
  prodKOps ((List.range 23).map fun v => if cell.testBit v then g + v else h + v) one b ++
    [.mulKF (b + 22) pw, .addK acc (b + 23), .mulF pw kp]

/-- The cells, one after the other. -/
def cellsOps (one g h kp : Reg) : List ℕ → Reg → Reg → ℕ → List Op
  | [], _, _, _ => []
  | c :: cs, acc, pw, b =>
    cellOps one g h kp c acc pw b ++ cellsOps one g h kp cs (b + 24) (b + 25) (b + 26)

/-- The register `cellsOps` leaves its sum in. -/
def cellsAcc : List ℕ → ℕ → ℕ → ℕ
  | [], acc, _ => acc
  | _ :: cs, _, b => cellsAcc cs (b + 24) (b + 26)

/-- The column-fold registers of level `i`'s tensor weights, from `b`. -/
def tRegs (fi : FinIn) (i b : ℕ) : List Reg := (List.range (ysOf fi i).length).map (b + 2 + ·)

/-- **Level `k`'s step** (`k = 1 … 4`, width `4 t + 5`, `t` level `k − 1`'s queries): `eq(κ_c, ·)`,
`tensorW(p_q, Pₖ[1..])` (the tail in `T`), `W + Σ_q eq(κ_c, bits₉(q))·tensorW_q` (`accOps`), then
`û(sₖ[0])·(…)`. -/
def lvOps (fi : FinIn) (k : ℕ) (one cu T W b : Reg) : List Op :=
  let ys := ysOf fi (k - 1)
  let a := b + 2 + 4 * ys.length
  [.packF (kcOf fi (k - 1)), .eqTable b] ++
    (List.range ys.length).map (fun q => .tensorW (ys.getD q 0 - 3) T) ++
    accOps (b + 1) (tRegs fi (k - 1) b) 0 W (b + 2 + ys.length) ++
    [.mulK ((sRegs fi k).headD 0) cu, .addK one a,
     .mulK (a + 1) (accOut W (b + 2 + ys.length) (tRegs fi (k - 1) b))]

/-- Level `k`'s width. -/
def lvW (fi : FinIn) (k : ℕ) : ℕ := 4 * (ysOf fi (k - 1)).length + 5

/-- The levels `ks`, one after the other (the tail of level `k` in register `Ts + k − 1`). -/
def lvsOps (fi : FinIn) (one cu Ts : Reg) : List ℕ → Reg → ℕ → List Op
  | [], _, _ => []
  | k :: ks, W, b => lvOps fi k one cu (Ts + (k - 1)) W b ++
      lvsOps fi one cu Ts ks (b + lvW fi k - 1) (b + lvW fi k)

/-- The register the levels leave `Ŵ` in. -/
def lvsOut (fi : FinIn) : List ℕ → ℕ → ℕ → ℕ
  | [], W, _ => W
  | k :: ks, _, b => lvsOut fi ks (b + lvW fi k - 1) (b + lvW fi k)

/-- The levels' width. -/
def lvsW (fi : FinIn) (ks : List ℕ) : ℕ := (ks.map (lvW fi)).sum

/-- `acc + Σ_c final[c]·E[c]` (four registers per `c`). -/
def fhOps (E : Reg) : List ℕ → Reg → ℕ → List Op
  | [], _, _ => []
  | c :: cs, acc, b =>
    [.piElemK fFinal (32 * c), .getK E c, .mulK b (b + 1), .addK acc (b + 2)] ++
      fhOps E cs (b + 3) (b + 4)

/-- The register `fhOps` leaves its sum in. -/
def fhOut : List ℕ → ℕ → ℕ → ℕ
  | [], acc, _ => acc
  | _ :: cs, _, b => fhOut cs (b + 3) (b + 4)

/-- **`finPf`** (A.9). Registers from `b`: `1`, `1 + u`, `0` of K; the points (`pfPts`); the kind's
tails `P₁[1..] … P₄[1..]` and `P₀` (`keep`, at `sb … sb + 4`); `Ŵ₀(P₀)` (`rsWeight`, and for a node
the cells); the four level steps; `final̂(sf)`
(`eqTableK`); the padding factor `Π_{x ∈ sf[μ..7)} (1 + x)`; the check against `claimN(Pf)`. -/
def finPf : FinField := fun fi b =>
  let one := b
  let cu := b + 1
  let z0 := b + 2
  let pts := pfPts fi
  let P := ptsOut pts (b + 3)
  let sb := b + 3 + ptsW pts
  let wb := sb + 5
  let rs1 := coordsR fi "RS1"
  let kp := (outsOf fi "B'").headD 0
  let cb := wb + 48
  let ce := cb + 1 + 26 * pfCells.length
  let lb := ce + 2
  let fb := lb + lvsW fi [1, 2, 3, 4]
  let pd := fb + 2 + 4 * 128
  let sf := chals fi "Pf" 7
  ([.const (fun _ => .k 1), .const (fun _ => .k (1 + K.u)), .const (fun _ => .k 0)] ++
   ptsOps one z0 pts (b + 3) ++
   [.keep is32 (P 7) (P 11), .keep is32 (P 8) (P 12), .keep is32 (P 9) (P 13),
    .keep is32 (P 10) (P 14), .keep is32 (P 15) (P 16)] ++
   [.packF ((List.range 7).map fun p => rs1.getD p 0),
    .rsWeight wb (fun κ => (rsPtIx κ).map P) (rs1.getD 7 0) ((outsOf fi "L3β").headD 0)
      Kind.isNode (sb + 4)] ++
   (List.range 23).map (fun v => .getK (sb + 4) v) ++
   (List.range 23).map (fun v => .addK one (wb + 2 + v)) ++
   [.mulF kp kp] ++
   cellsOps one (wb + 2) (wb + 25) kp pfCells z0 cb (cb + 1) ++
   [.keep Kind.isNode (cellsAcc pfCells z0 (cb + 1)) z0, .addK (wb + 1) ce] ++
   lvsOps fi one cu sb [1, 2, 3, 4] (ce + 1) lb ++
   [.packK sf, .eqTableK fb] ++ fhOps (fb + 1) (List.range 128) z0 (fb + 2) ++
   [.addK one (sf.getD 5 0), .addK one (sf.getD 6 0), .mulK pd (pd + 1), .keep is32 one (pd + 2),
    .mulK (lvsOut fi [1, 2, 3, 4] (ce + 1) lb) (pd + 3),
    .mulK (pd + 4) (fhOut (List.range 128) z0 (fb + 2)),
    .assertEq (pd + 5) (claimN fi "Pf") allK], [])


/-! ### `finPf` asks nothing -/

theorem noAsk_map {α : Type} (l : List α) (f : α → Op) (h : ∀ a, (f a).item? = none) :
    (l.map f).filterMap Op.item? = [] := by
  rw [List.filterMap_eq_nil_iff]; simp only [List.mem_map]; rintro _ ⟨a, -, rfl⟩; exact h a

theorem noAsk_prodKOps : ∀ (xs : List Reg) (acc b : ℕ), (prodKOps xs acc b).filterMap Op.item? = []
  | [], _, _ => rfl
  | _ :: xs, _, b => by
    simp only [prodKOps, List.filterMap_cons, Op.item?]; exact noAsk_prodKOps xs b (b + 1)

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

theorem noAsk_fhOps (E : Reg) : ∀ cs acc b, (fhOps E cs acc b).filterMap Op.item? = []
  | [], _, _ => rfl
  | c :: cs, acc, b => by
    rw [fhOps, List.filterMap_append, noAsk_fhOps E cs]; rfl

theorem noAsk_ptsOps (one z0 : Reg) : ∀ ss b, (ptsOps one z0 ss b).filterMap Op.item? = []
  | [], _ => rfl
  | s :: ss, b => by
    rw [ptsOps, ptOps, List.filterMap_append, List.filterMap_append, noAsk_ptsOps one z0 ss,
      noAsk_map _ _ (fun x => by cases x <;> rfl)]
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
  rfl

/-! ### `finPf` runs to its relation -/

section RunPf
variable (impl : OpImpl) (κ : Kind) (inp : Input)

/-- Blocks in sequence: the second runs from the first's registers. -/
theorem pr_seq {A B : List Op} {R : Array Val} {M M' : List Val} {f : Bool}
    (hA : pureRun impl κ inp A R [] = some (M, true))
    (hB : pureRun impl κ inp B (R ++ M.toArray) [] = some (M', f)) :
    pureRun impl κ inp (A ++ B) R [] = some (M ++ M', f) := by
  rw [pr_app' impl κ inp R hA]
  have := pureRun_rebase impl κ inp B R M []
  simp only [List.append_nil] at this
  rw [this, hB]; rfl

/-- The one value an op appends from `R`'s registers. -/
def baseVal (R : Array Val) (op : Op) : Val :=
  match evalOp impl κ inp R op with
  | .vals [v] _ => v
  | _ => default

/-- Ops reading only `R`'s registers, each appending one value. -/
theorem run_base (R : Array Val) : ∀ (os : List Op) (L : List Val),
    (∀ op ∈ os, ∀ Y : List Val, evalOp impl κ inp (R ++ Y.toArray) op = evalOp impl κ inp R op) →
    (∀ op ∈ os, ∃ v, evalOp impl κ inp R op = .vals [v] true) →
    pureRun impl κ inp os R L = some (L ++ os.map (baseVal impl κ inp R), true)
  | [], L, _, _ => by simp [pureRun]
  | op :: os, L, h₁, h₂ => by
    obtain ⟨v, hv⟩ := h₂ op (List.mem_cons_self ..)
    have e : evalOp impl κ inp (R ++ L.toArray) op = .vals [v] true := by
      rw [h₁ op (List.mem_cons_self ..), hv]
    rw [pr_op impl κ inp R e,
      run_base R os (L ++ [v]) (fun o ho => h₁ o (List.mem_cons_of_mem _ ho))
      (fun o ho => h₂ o (List.mem_cons_of_mem _ ho))]
    simp [baseVal, hv]

/-! ### Points -/

/-- The value of a coordinate. -/
def srcVal (r : Array Val) : PtSrc → K
  | .f x => K.smulF (rd r x).toF 1
  | .k x => (rd r x).toK
  | .c v => v

/-- A coordinate reads a register below `n` (if any). -/
def PtSrc.Ok (n : ℕ) : PtSrc → Prop
  | .f x => x < n
  | .k x => x < n
  | .c _ => True

/-- A point's value. -/
def ptV (r : Array Val) (s : List PtSrc) : Array K := (s.map (srcVal r)).toArray

variable (r : Array Val) (one z0 : ℕ) (h1 : one < r.size) (hv1 : rd r one = .k 1)
  (h0 : z0 < r.size) (hv0 : rd r z0 = .k 0)
include h1 hv1 h0 hv0

theorem run_srcs : ∀ (src : List PtSrc) (L : List Val), (∀ s ∈ src, s.Ok r.size) →
    pureRun impl κ inp (src.map (srcOp one z0)) r L =
      some (L ++ src.map (fun s => .k (srcVal r s)), true)
  | [], L, _ => by simp [pureRun]
  | s :: src, L, hs => by
    have hs0 := hs s (List.mem_cons_self ..)
    have e : evalOp impl κ inp (r ++ L.toArray) (srcOp one z0 s) =
        .vals [.k (srcVal r s)] true := by
      cases s with
      | f x =>
        simp only [PtSrc.Ok] at hs0
        simp only [srcOp, evalOp, srcVal, rd_app_left _ _ h1, rd_app_left _ _ hs0, hv1]; rfl
      | k x =>
        simp only [PtSrc.Ok] at hs0
        simp only [srcOp, evalOp, srcVal, rd_app_left _ _ h0, rd_app_left _ _ hs0, hv0]
        simp [Val.toK]
      | c v => rfl
    rw [List.map_cons, pr_op impl κ inp r e, run_srcs src (L ++ _)
      (fun s hs' => hs s (List.mem_cons_of_mem _ hs'))]
    simp

theorem run_ptOps (src : List PtSrc) (L : List Val) (hs : ∀ s ∈ src, s.Ok r.size) :
    pureRun impl κ inp (ptOps one z0 src (r.size + L.length)) r L =
      some (L ++ (src.map (fun s => Val.k (srcVal r s)) ++ [.ak (ptV r src)]), true) := by
  rw [ptOps, pr_app impl κ inp r (run_srcs impl κ inp r one z0 h1 hv1 h0 hv0 src L hs)]
  simp only [pureRun, evalOp, Option.map_some, Bool.and_true]
  rw [List.append_assoc]
  congr 5
  simp only [ptV, List.map_map]
  congr 2
  apply List.ext_getElem (by simp)
  intro i hi _
  simp only [List.length_map, List.length_range] at hi
  simp only [List.getElem_map, List.getElem_range, Function.comp_apply, rdX]
  simp [List.getD_eq_getElem?_getD, hi, Val.toK]

theorem run_ptsOps : ∀ (ss : List (List PtSrc)) (L : List Val),
    (∀ s ∈ ss, ∀ x ∈ s, x.Ok r.size) →
    ∃ M, pureRun impl κ inp (ptsOps one z0 ss (r.size + L.length)) r L = some (L ++ M, true) ∧
      M.length = ptsW ss ∧ ∀ j < ss.length,
        rd (r ++ (L ++ M).toArray) (ptsOut ss (r.size + L.length) j) = .ak (ptV r (ss.getD j []))
  | [], L, _ => ⟨[], by simp [ptsOps, pureRun], rfl, fun j hj => absurd hj (by simp)⟩
  | s :: ss, L, hs => by
    set M₁ : List Val := s.map (fun s => Val.k (srcVal r s)) ++ [.ak (ptV r s)]
    have h₁ := run_ptOps impl κ inp r one z0 h1 hv1 h0 hv0 s L (hs s (List.mem_cons_self ..))
    have hl₁ : M₁.length = s.length + 1 := by simp [M₁]
    obtain ⟨M, hM, hl, hv⟩ := run_ptsOps ss (L ++ M₁) (fun t ht => hs t (List.mem_cons_of_mem _ ht))
    have hb : r.size + (L ++ M₁).length = r.size + L.length + s.length + 1 := by
      simp only [List.length_append, hl₁]; omega
    rw [hb] at hM hv
    refine ⟨M₁ ++ M, ?_, by simp [ptsW, hl₁, hl], ?_⟩
    · rw [ptsOps, pr_app impl κ inp r h₁, hM]; simp
    · intro j hj
      cases j with
      | zero =>
        simp only [ptsOut, List.getD_cons_zero]
        rw [← List.append_assoc, rd_pre r (by simp [hl₁]; omega), rdX]
        simp [M₁]
      | succ j =>
        simp only [ptsOut, List.getD_cons_succ]
        rw [← List.append_assoc]
        exact hv j (by simpa using hj)

end RunPf

theorem ptsOut_lt : ∀ (ss : List (List PtSrc)) (b j : ℕ), j < ss.length →
    ptsOut ss b j < b + ptsW ss
  | [], _, _, h => absurd h (by simp)
  | s :: ss, b, 0, _ => by
    simp only [ptsOut, ptsW, List.map_cons, List.sum_cons]
    generalize (List.map (fun x => x.length + 1) ss).sum = X; omega
  | s :: ss, b, j + 1, h => by
    have := ptsOut_lt ss (b + s.length + 1) j (by simpa using h)
    simp only [ptsOut, ptsW, List.map_cons, List.sum_cons] at this ⊢
    generalize (List.map (fun x => x.length + 1) ss).sum = X at this ⊢; omega


/-- The register `prodKOps` leaves its product in. -/
def prodKOut : List Reg → ℕ → ℕ → ℕ
  | [], acc, _ => acc
  | _ :: xs, _, b => prodKOut xs b (b + 1)

theorem prodKOut_eq : ∀ (xs : List Reg) (acc b : ℕ), xs ≠ [] → prodKOut xs acc b = b + xs.length - 1
  | [], _, _, h => absurd rfl h
  | [_], _, _, _ => by simp [prodKOut]
  | _ :: y :: xs, _, b, _ => by
    rw [prodKOut, prodKOut_eq (y :: xs) b (b + 1) (List.cons_ne_nil _ _)]
    simp only [List.length_cons]; omega

/-- `eq(cell, ρ)` over 23 coordinates, the product from the left (as `cellOps` computes it). -/
def eqCellK (ρ : Array K) (c : ℕ) : K :=
  ((List.range 23).map fun v => if c.testBit v then ρ.getD v 0 else 1 + ρ.getD v 0).foldl
    (· * ·) 1

/-- `A + Σ_k pw·κ′^k·eq(cell_k, ρ)` (as `cellsOps` accumulates it). -/
def cellsVal (ρ : Array K) (kp : F) : List ℕ → F → K → K
  | [], _, A => A
  | c :: cs, pw, A => cellsVal ρ kp cs (pw * kp) (A + K.smulF pw (eqCellK ρ c))

/-- `A + Σ_c final[c]·E[c]` (as `fhOps` accumulates it). -/
def fhVal (inp : Input) (E : Array K) : List ℕ → K → K
  | [], A => A
  | c :: cs, A => fhVal inp E cs (A + finV inp c * E.getD c 0)

section Loops
variable (impl : OpImpl) (κ : Kind) (inp : Input) (r : Array Val)

theorem run_prodKOps : ∀ (xs : List ℕ) (acc : ℕ) (A : K) (L : List Val),
    (∀ x ∈ xs, x < r.size) → acc < r.size + L.length → rd (r ++ L.toArray) acc = .k A →
    ∃ M, pureRun impl κ inp (prodKOps xs acc (r.size + L.length)) r L = some (L ++ M, true) ∧
      M.length = xs.length ∧ rd (r ++ (L ++ M).toArray) (prodKOut xs acc (r.size + L.length)) =
        .k (xs.foldl (fun a x => a * (rd r x).toK) A)
  | [], acc, A, L, _, _, hA => ⟨[], by simp [prodKOps, pureRun], rfl, by simpa [prodKOut] using hA⟩
  | x :: xs, acc, A, L, hx, hacc, hA => by
    have hx0 := hx x (List.mem_cons_self ..)
    set v : Val := .k (A * (rd r x).toK)
    have e : evalOp impl κ inp (r ++ L.toArray) (.mulK acc x) = .vals [v] true := by
      simp only [evalOp, hA, rd_app_left _ _ hx0]; rfl
    obtain ⟨M, hM, hl, hv⟩ := run_prodKOps xs (r.size + L.length) (A * (rd r x).toK) (L ++ [v])
      (fun y hy => hx y (List.mem_cons_of_mem _ hy)) (by simp) (rd_new1 r L v)
    have hb : r.size + (L ++ [v]).length = r.size + L.length + 1 := by simp; omega
    rw [hb] at hM hv
    refine ⟨v :: M, ?_, by simp [hl], ?_⟩
    · rw [prodKOps, pr_op impl κ inp r e, hM]; simp
    · rw [prodKOut, List.foldl_cons]; simpa using hv

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

theorem evalOp_outs_len (regs : Array Val) (op : Op) {vs : List Val} {ok : Bool}
    (h : evalOp impl κ inp regs op = .vals vs ok) : vs.length = op.outs := by
  cases op <;> simp only [evalOp, Res.vals.injEq, reduceCtorEq] at h <;> obtain ⟨rfl, -⟩ := h <;>
    rfl

theorem pureRun_len : ∀ (os : List Op) (L L' : List Val) (f : Bool),
    pureRun impl κ inp os r L = some (L', f) → L'.length = L.length + opsOut os
  | [], L, L', f, h => by simp [pureRun] at h; obtain ⟨rfl, -⟩ := h; simp [opsOut]
  | op :: os, L, L', f, h => by
    simp only [pureRun] at h
    split at h
    · next vs ok hv =>
      obtain ⟨⟨L₂, f₂⟩, h₂, he⟩ := Option.map_eq_some_iff.mp h
      simp only [Prod.mk.injEq] at he; obtain ⟨rfl, -⟩ := he
      rw [pureRun_len os _ _ _ h₂, List.length_append, evalOp_outs_len impl κ inp _ op hv]
      simp [opsOut]; omega
    · cases h

theorem opsOut_accOps (e : Reg) : ∀ ys q acc b, opsOut (accOps e ys q acc b) = 3 * ys.length
  | [], _, _, _ => rfl
  | _ :: ys, q, acc, b => by
    have := opsOut_accOps e ys (q + 1) (b + 2) (b + 3)
    simp only [opsOut, accOps, List.cons_append, List.nil_append, List.map_cons,
      List.sum_cons] at this ⊢
    rw [this]; simp [Op.outs]; ring

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

/-- `û(β) = 1 + β(1 + u)` (the fold factor of a later level's first challenge). -/
def uHat (β : K) : K := 1 + β * (1 + K.u)

theorem run_lvOps (fi : FinIn) (k one cu T W : ℕ) (Wv : K) (R : Array Val)
    (hys : ∀ y ∈ ysOf fi (k - 1), y < R.size)
    (hs : (sRegs fi k).headD 0 < R.size) (h1 : one < R.size) (hv1 : rd R one = .k 1)
    (hc : cu < R.size) (hcv : rd R cu = .k (1 + K.u)) (hT : T < R.size) (hW : W < R.size)
    (hWv : rd R W = .k Wv) :
    ∃ M, pureRun impl κ inp (lvOps fi k one cu T W R.size) R [] = some (M, true) ∧
      M.length = lvW fi k ∧
      rd (R ++ M.toArray) (R.size + lvW fi k - 1) =
        .k (uHat (rd R ((sRegs fi k).headD 0)).toK *
          accVal (eqTab (((kcOf fi (k - 1)).map fun x => (rd R x).toF).toArray))
            ((List.range (ysOf fi (k - 1)).length).map fun q =>
              impl.tensorW (rd R ((ysOf fi (k - 1)).getD q 0 - 3)).toN (rd R T).toAK) 0 Wv) := by
  have app0 : ∀ X : Array Val, X ++ ([] : List Val).toArray = X := fun X => by simp
  set ys := ysOf fi (k - 1) with hysd
  set t := ys.length with ht
  set b := R.size with hb
  set E := eqTab (((kcOf fi (k - 1)).map fun x => (rd R x).toF).toArray)
  set v₀ : Val := .af (((kcOf fi (k - 1)).map fun x => (rd R x).toF).toArray)
  set v₁ : Val := .af E
  set tens : List Op := (List.range t).map fun q => .tensorW (ys.getD q 0 - 3) T
  have hA : pureRun impl κ inp [.packF (kcOf fi (k - 1)), .eqTable b] R [] =
      some ([v₀, v₁], true) := by
    have e0 : evalOp impl κ inp (R ++ ([] : List Val).toArray) (.packF (kcOf fi (k - 1))) =
        .vals [v₀] true := by
      simp only [evalOp, v₀, app0]
    have e1 : evalOp impl κ inp (R ++ ([] ++ [v₀]).toArray) (.eqTable b) = .vals [v₁] true := by
      simp only [evalOp, hb, List.nil_append, rd_app0]; rfl
    rw [pr_op impl κ inp R e0, pr_op impl κ inp R e1]; rfl
  have hys0 : ∀ q < t, ys.getD q 0 - 3 < R.size := fun q hq => by
    have := hys _ (List.getElem_mem (show q < ys.length from hq))
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hq, Option.getD_some]
    exact Nat.lt_of_le_of_lt (Nat.sub_le _ _) this
  have hB := run_base impl κ inp R tens [v₀, v₁]
    (fun op hop Y => by
      obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hop
      simp only [evalOp, rd_app_left _ _ (hys0 q (List.mem_range.mp hq)), rd_app_left _ _ hT])
    (fun op hop => by obtain ⟨q, -, rfl⟩ := List.mem_map.mp hop; exact ⟨_, rfl⟩)
  set V := [v₀, v₁] ++ tens.map (baseVal impl κ inp R)
  have hV : V.length = 2 + t := by simp [V, tens]; omega
  have hAB : pureRun impl κ inp ([.packF (kcOf fi (k - 1)), .eqTable b] ++ tens) R [] =
      some (V, true) := by
    rw [pr_app' impl κ inp R hA, hB]
  set R' := R ++ V.toArray
  have hR' : R'.size = b + 2 + t := by simp [R', hV, hb]; omega
  have hR'0 : R'.size + ([] : List Val).length = b + 2 + t := by simp [hR']
  have rdV : ∀ x < b, rd R' x = rd R x := fun x hx => rd_app_left R V hx
  have hte : (tRegs fi (k - 1) b).map (fun y => (rd R' y).toK) =
      (List.range t).map fun q => impl.tensorW (rd R (ys.getD q 0 - 3)).toN (rd R T).toAK := by
    simp only [tRegs, List.map_map]
    refine List.map_congr_left fun q hq => ?_
    have hq' : q < t := List.mem_range.mp hq
    simp only [Function.comp_apply, R', show b + 2 + q = R.size + (2 + q) by omega, rd_app]
    simp only [V, List.getD_eq_getElem?_getD,
      List.getElem?_append_right (show [v₀, v₁].length ≤ 2 + q by simp)]
    simp [tens, hq', baseVal, evalOp, List.getD_eq_getElem?_getD, toK_k]
  obtain ⟨M₃, h₃, hv₃⟩ := run_accOps impl κ inp R' (b + 1) E (tRegs fi (k - 1) b) 0 W Wv []
    (fun y hy => by
      obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hy
      have := List.mem_range.mp hq; rw [hR']; exact Nat.add_lt_add_left this _)
    (by simp only [hR', List.length_nil, Nat.add_zero]; show b + 1 < b + 2 + t; omega)
    (by
      simp only [app0, R', show b + 1 = R.size + 1 by omega, rd_app]; rfl)
    (by simp only [hR', List.length_nil, Nat.add_zero]; exact Nat.lt_of_lt_of_le hW (by omega))
    (by simp only [app0]; rw [rdV W hW, hWv])
  simp only [List.length_nil, Nat.add_zero, List.nil_append] at h₃ hv₃
  rw [hR'] at h₃ hv₃
  rw [hte] at hv₃
  have hl₃ : M₃.length = 3 * t := by
    have := pureRun_len impl κ inp R' _ [] M₃ true h₃
    rw [opsOut_accOps] at this; simpa [tRegs, ← ht] using this
  set R'' := R' ++ M₃.toArray
  have hR'' : R''.size = b + 2 + 4 * t := by simp [R'', hR', hl₃]; omega
  have rdM : ∀ x < b, rd R'' x = rd R x := fun x hx => by
    rw [rd_app_left R' M₃ (by omega), rdV x hx]
  set s0 := (rd R ((sRegs fi k).headD 0)).toK
  set acc := accVal E ((List.range t).map fun q =>
    impl.tensorW (rd R (ys.getD q 0 - 3)).toN (rd R T).toAK) 0 Wv
  set w₁ : Val := .k (s0 * (1 + K.u))
  set w₂ : Val := .k (1 + s0 * (1 + K.u))
  set w₃ : Val := .k ((1 + s0 * (1 + K.u)) * acc)
  have hC : pureRun impl κ inp [.mulK ((sRegs fi k).headD 0) cu, .addK one (b + 2 + 4 * t),
      .mulK (b + 2 + 4 * t + 1) (accOut W (b + 2 + t) (tRegs fi (k - 1) b))] R'' [] =
      some ([w₁, w₂, w₃], true) := by
    have e1 : evalOp impl κ inp (R'' ++ ([] : List Val).toArray) (.mulK ((sRegs fi k).headD 0) cu) =
        .vals [w₁] true := by
      simp only [evalOp, app0, rdM _ hs, rdM _ hc, hcv]; rfl
    have e2 : evalOp impl κ inp (R'' ++ ([] ++ [w₁]).toArray) (.addK one (b + 2 + 4 * t)) =
        .vals [w₂] true := by
      simp only [evalOp, List.nil_append, rd_app_left _ _ (show one < R''.size by omega), rdM _ h1,
        hv1, ← hR'', rd_app0]; rfl
    have e3 : evalOp impl κ inp (R'' ++ ([] ++ [w₁] ++ [w₂]).toArray)
        (.mulK (b + 2 + 4 * t + 1) (accOut W (b + 2 + t) (tRegs fi (k - 1) b))) =
        .vals [w₃] true := by
      have hacc : accOut W (b + 2 + t) (tRegs fi (k - 1) b) < R''.size := by
        by_contra hc'
        have h0 := hv₃; rw [rd, Array.getElem?_eq_none (by simpa [R''] using hc')] at h0; cases h0
      simp only [evalOp, List.nil_append, rd_app_left _ _ hacc, R'', hv₃, ← hR'', rd_app]; rfl
    rw [pr_op impl κ inp R'' e1, pr_op impl κ inp R'' e2, pr_op impl κ inp R'' e3]; rfl
  refine ⟨V ++ M₃ ++ [w₁, w₂, w₃], ?_, ?_, ?_⟩
  · simp only [lvOps, ← hysd, ← ht]
    have e : R ++ (V ++ M₃).toArray = R'' := by simp [R'', R', Array.append_assoc]
    rw [← e] at hC
    exact pr_seq impl κ inp (pr_seq impl κ inp hAB h₃) hC
  · simp [lvW, hV, hl₃, ← hysd, ← ht]; omega
  · rw [show b + lvW fi k - 1 = R''.size + 2 by simp [lvW, hR'', ← hysd, ← ht]; omega,
      show R ++ (V ++ M₃ ++ [w₁, w₂, w₃]).toArray = R'' ++ [w₁, w₂, w₃].toArray by
        simp [R'', R', Array.append_assoc], rd_app]
    rfl

/-- **Level `k`'s step value** from register values `rv` and the tail points `tl`:
`û(sₖ[0])·(W + Σ_q eq(κ_c⁽ᵏ⁻¹⁾, bits₉(q))·tensorW(p_q⁽ᵏ⁻¹⁾, Pₖ[1..]))`. -/
def lvStepV (impl : OpImpl) (fi : FinIn) (rv : ℕ → Val) (tl : ℕ → Array K) (k : ℕ) (W : K) : K :=
  uHat (rv ((sRegs fi k).headD 0)).toK *
    accVal (eqTab (((kcOf fi (k - 1)).map fun x => (rv x).toF).toArray))
      ((List.range (ysOf fi (k - 1)).length).map fun q =>
        impl.tensorW (rv ((ysOf fi (k - 1)).getD q 0 - 3)).toN (tl k)) 0 W

/-- The levels `ks` in turn. -/
def lvsV (impl : OpImpl) (fi : FinIn) (rv : ℕ → Val) (tl : ℕ → Array K) : List ℕ → K → K
  | [], W => W
  | k :: ks, W => lvsV impl fi rv tl ks (lvStepV impl fi rv tl k W)

/-- The registers a level step reads. -/
def lvRefs (fi : FinIn) (k : ℕ) : List ℕ :=
  (sRegs fi k).headD 0 :: kcOf fi (k - 1) ++ ysOf fi (k - 1)

theorem lvStepV_congr (fi : FinIn) {rv rv' : ℕ → Val} (tl : ℕ → Array K) (k : ℕ) (W : K) (n : ℕ)
    (h : ∀ x < n, rv x = rv' x) (hr : ∀ x ∈ lvRefs fi k, x < n) :
    lvStepV impl fi rv tl k W = lvStepV impl fi rv' tl k W := by
  have h0 : (sRegs fi k).headD 0 < n := hr _ (by simp [lvRefs])
  have hk : ∀ x ∈ kcOf fi (k - 1), x < n := fun x hx => hr x (by simp [lvRefs, hx])
  have hys : ∀ x ∈ ysOf fi (k - 1), x < n := fun x hx => hr x (by simp [lvRefs, hx])
  have hy : ∀ q < (ysOf fi (k - 1)).length,
      rv ((ysOf fi (k - 1)).getD q 0 - 3) = rv' ((ysOf fi (k - 1)).getD q 0 - 3) := by
    intro q hq
    have := hys _ (List.getElem_mem hq)
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hq, Option.getD_some]
    exact h _ (Nat.lt_of_le_of_lt (Nat.sub_le _ _) this)
  unfold lvStepV
  rw [h _ h0, List.map_congr_left fun x hx => by rw [h x (hk x hx)]]
  congr 2
  exact List.map_congr_left fun q hq => by rw [hy q (List.mem_range.mp hq)]

theorem run_lvsOps (fi : FinIn) (one cu Ts : ℕ) (tl : ℕ → Array K) (R0 : Array Val)
    (h1 : one < R0.size) (hv1 : rd R0 one = .k 1) (hc : cu < R0.size)
    (hcv : rd R0 cu = .k (1 + K.u)) :
    ∀ (ks : List ℕ) (W : ℕ) (Wv : K) (R : Array Val), R0.size ≤ R.size →
    (∀ x < R0.size, rd R x = rd R0 x) →
    (∀ k ∈ ks, (∀ x ∈ lvRefs fi k, x < R0.size) ∧ Ts + (k - 1) < R0.size ∧
      rd R0 (Ts + (k - 1)) = .ak (tl k)) →
    W < R.size → rd R W = .k Wv →
    ∃ M, pureRun impl κ inp (lvsOps fi one cu Ts ks W R.size) R [] = some (M, true) ∧
      M.length = lvsW fi ks ∧
      rd (R ++ M.toArray) (lvsOut fi ks W R.size) = .k (lvsV impl fi (rd R0) tl ks Wv)
  | [], W, Wv, R, _, _, _, _, hWv =>
    ⟨[], by simp [lvsOps, pureRun], rfl, by simpa [lvsOut, lvsV] using hWv⟩
  | k :: ks, W, Wv, R, hle, hR, hk, hW, hWv => by
    obtain ⟨hr, hT, hTv⟩ := hk k (List.mem_cons_self ..)
    have hs : (sRegs fi k).headD 0 < R0.size := hr _ (by simp [lvRefs])
    have hys : ∀ y ∈ ysOf fi (k - 1), y < R.size := fun y hy =>
      Nat.lt_of_lt_of_le (hr y (by simp [lvRefs, hy])) hle
    obtain ⟨M₁, h₁, hl₁, hv₁⟩ := run_lvOps impl κ inp fi k one cu (Ts + (k - 1)) W Wv R hys
      (Nat.lt_of_lt_of_le hs hle) (Nat.lt_of_lt_of_le h1 hle) (by rw [hR _ h1, hv1])
      (Nat.lt_of_lt_of_le hc hle) (by rw [hR _ hc, hcv]) (Nat.lt_of_lt_of_le hT hle) hW hWv
    rw [hR _ hT, hTv] at hv₁
    have hstep : uHat (rd R ((sRegs fi k).headD 0)).toK *
        accVal (eqTab (((kcOf fi (k - 1)).map fun x => (rd R x).toF).toArray))
          ((List.range (ysOf fi (k - 1)).length).map fun q =>
            impl.tensorW (rd R ((ysOf fi (k - 1)).getD q 0 - 3)).toN (Val.ak (tl k)).toAK) 0 Wv =
        lvStepV impl fi (rd R0) tl k Wv :=
      lvStepV_congr impl fi tl k Wv R0.size hR hr
    rw [hstep] at hv₁
    set R' := R ++ M₁.toArray
    have hR' : R'.size = R.size + lvW fi k := by simp [R', hl₁]
    have hpos : 0 < lvW fi k := by simp [lvW]
    obtain ⟨M, hM, hl, hv⟩ := run_lvsOps fi one cu Ts tl R0 h1 hv1 hc hcv ks
      (R.size + lvW fi k - 1) (lvStepV impl fi (rd R0) tl k Wv)
      R' (by rw [hR']; omega) (fun x hx => by rw [rd_app_left R M₁ (by omega), hR x hx])
      (fun k' hk' => hk k' (List.mem_cons_of_mem _ hk')) (by rw [hR']; omega) hv₁
    rw [hR'] at hM hv
    refine ⟨M₁ ++ M, ?_, by simp [lvsW, hl₁, hl], ?_⟩
    · rw [lvsOps]
      exact pr_seq impl κ inp h₁ hM
    · simp only [lvsOut, lvsV]
      rw [show R ++ (M₁ ++ M).toArray = R' ++ M.toArray by simp [R', Array.append_assoc]]
      exact hv

end Loops

/-! ### `finPf`'s relation -/

/-- The registers of a coordinate. -/
def PtSrc.regs : PtSrc → List ℕ
  | .f x => [x]
  | .k x => [x]
  | .c _ => []

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

theorem ptV_app (r : Array Val) (L : List Val) (s : List PtSrc) (h : ∀ x ∈ s, x.Ok r.size) :
    ptV (r ++ L.toArray) s = ptV r s := by
  simp only [ptV]; congr 1
  refine List.map_congr_left fun x hx => ?_
  have := h x hx
  cases x with
  | f y => simp only [srcVal, rd_app_left _ _ (show y < r.size from this)]
  | k y => simp only [srcVal, rd_app_left _ _ (show y < r.size from this)]
  | c v => rfl

theorem ptV_k (r : Array Val) (xs : List ℕ) :
    ptV r (xs.map .k) = (xs.map fun x => (rd r x).toK).toArray := by
  simp [ptV, srcVal, Function.comp_def]

theorem lvsV_congr (impl : OpImpl) (fi : FinIn) {rv rv' : ℕ → Val} (tl : ℕ → Array K) (n : ℕ)
    (h : ∀ x < n, rv x = rv' x) :
    ∀ (ks : List ℕ) (W : K), (∀ k ∈ ks, ∀ x ∈ lvRefs fi k, x < n) →
      lvsV impl fi rv tl ks W = lvsV impl fi rv' tl ks W
  | [], _, _ => rfl
  | k :: ks, W, hk => by
    simp only [lvsV]
    rw [lvStepV_congr impl fi tl k W n h (hk k (List.mem_cons_self ..))]
    exact lvsV_congr impl fi tl n h ks _ fun k' hk' => hk k' (List.mem_cons_of_mem _ hk')

/-- `Ext R R'`: `R'` extends `R`. -/
def ExtA (R R' : Array Val) : Prop := R.size ≤ R'.size ∧ ∀ x < R.size, rd R' x = rd R x

theorem ExtA.app (R : Array Val) (M : List Val) : ExtA R (R ++ M.toArray) :=
  ⟨by simp, fun _ hx => rd_app_left R M hx⟩

theorem ExtA.trans {R R' R'' : Array Val} (h₁ : ExtA R R') (h₂ : ExtA R' R'') : ExtA R R'' :=
  ⟨le_trans h₁.1 h₂.1, fun x hx => by rw [h₂.2 x (Nat.lt_of_lt_of_le hx h₁.1), h₁.2 x hx]⟩

theorem ExtA.rd {R R' : Array Val} (h : ExtA R R') {x : ℕ} (hx : x < R.size) : rd R' x = rd R x :=
  h.2 x hx

theorem ex_some {A : List Val} {f g : Bool} (h : f = g) :
    ∃ V : List Val, some (A, f) = some (V, g) := ⟨A, by rw [h]⟩

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
    (b + 3 + pw + 5 + 25) kp (p0V κ fi r) kpv (by omega) (by rw [e17.rd (by omega), r1one])
    (Nat.lt_of_lt_of_le hkpr (e06.trans e67).1) (by rw [e06.trans e67 |>.rd hkpr])
    (fun v hv => ⟨by omega, by
      rw [e57.rd (by rw [sR5]; omega), r5 v hv]; rfl⟩)
    (fun v hv => ⟨by omega, by
      rw [show b + 3 + pw + 5 + 25 + v = R5.size + v by rw [sR5],
        e67.rd (by rw [sR6]; omega), hR6, rd_app]; simp [V6, hv, toK_k]⟩)
    pfCells (b + 2) (b + 3 + pw + 5 + 48) 0 (kpv * kpv) [] (by simp; omega)
    (by rw [app0, e17.rd (by omega), r1z])
    (by simp; omega)
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
      rd_app_left _ _ (show b + 3 + pw + 5 + 1 < R8.size by omega),
      rd_app_left _ _ (show b + 2 < R8.size by omega), rd_app_left _ _ hca, r8w, r8z, hv8,
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
    (tailV κ fi r) R9 (by omega) (by rw [e19.rd (by omega), r1one]) (by omega)
    (by rw [e19.rd (by omega), r1cu]) [1, 2, 3, 4] (b + 3 + pw + 5 + 48 + 1 + 26 * 9 + 1)
    (w0V impl κ fi r) R9 le_rfl (fun _ _ => rfl)
    (fun k hk => by
      refine ⟨fun x hx => Nat.lt_of_lt_of_le (mE k hk x hx) e09.1, by
        simp at hk; rcases hk with rfl | rfl | rfl | rfl <;> omega, ?_⟩
      have hk' : k - 1 < 4 ∧ k - 1 + 1 = k := by simp at hk; omega
      rw [e39.rd (by rw [sR3]; omega), r3T (k - 1) hk'.1, hk'.2])
    (by omega) r9w
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
  obtain ⟨M12, hB12, hl12, hv12⟩ := run_fhOps impl κ inp R11 (fb + 1) (eqTab sfV) (by omega)
    (by rw [hR11, ← sR10, rd_app]; rfl) (List.range 128) (b + 2) 0 []
    (by simp; omega) (by rw [app0, (e19.trans (e910.trans e1011)).rd (by omega), r1z])
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
