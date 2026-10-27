-- New for `flock-recursive` (BLUEPRINT §7, A.9; stage S-G).
import FRVIRFinalsSF

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

`finPf` is not in this module: it needs the `rsWeight` op (A.8, revision 3.9), which `FRVIR` does
not have yet, and `evalM` at a K point (S-G RESULT).
-/

namespace FR

/-- The nodes of `S`, as `quirky_claim_split` indexes them. -/
def sNode (b : Fin 64) : F := skipNode (Fin.castLE (by norm_num) b)

theorem foldl_mul_eq {α : Type*} (g : α → F) :
    ∀ (xs : List α) (c : F), xs.foldl (fun a j => a * g j) c = c * (xs.map g).prod
  | [], c => by simp
  | x :: xs, c => by rw [List.foldl_cons, foldl_mul_eq g xs, List.map_cons, List.prod_cons]; ring

theorem xS_of_lt {j : ℕ} (hj : j < 64) : xS j = sNode ⟨j, hj⟩ := by
  simp only [xS, sNode, Nat.mod_eq_of_lt (show j < 128 by omega)]; rfl

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
    lagV l lo = lagrangeWeight sNode l ⟨lo, hlo⟩ := by
  have hx : ∀ j ∈ (Finset.univ : Finset (Fin 64)).erase ⟨lo, hlo⟩, xS j = sNode j :=
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
def accV (E : Array F) : List K → ℕ → K → K
  | [], _, A => A
  | y :: ys, q, A => accV E ys (q + 1) (A + K.smulF (E.getD q 0) y)

theorem accV_eq (E : Array F) : ∀ (Ys : List K) (q : ℕ) (A : K),
    accV E Ys q A =
      A + ((List.range Ys.length).map fun k => K.smulF (E.getD (q + k) 0) (Ys.getD k 0)).sum
  | [], _, A => by simp [accV]
  | y :: ys, q, A => by
    rw [accV, accV_eq E ys (q + 1), List.length_cons, List.range_succ_eq_map, List.map_cons,
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
        .k (accV E (ys.map fun y => (rd r y).toK) q A)
  | [], q, acc, A, L, _, _, _, _, hA =>
    ⟨[], by simp [accOps, pureRun], by simpa [accOut, accV] using hA⟩
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
    · simp only [accOut, List.map_cons, accV]
      simpa using hout

variable (fi : FinIn)

/-- `eq(κ_c, ·)` on the 512 indices `bits₉(q)`. -/
def kcTab (i : ℕ) : Array F := eqTab ((kcOf fi i).map (fv r)).toArray

/-- The batched claim `claimN(P1.i) + Σ_q eq(κ_c, bits₉(q))·y_q`. -/
def vNext (i : ℕ) : K :=
  accV (kcTab r fi i) ((ysOf fi i).map fun y => (rd r y).toK) 0 (rd r (p1ClaimN fi i)).toK

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

end FR
