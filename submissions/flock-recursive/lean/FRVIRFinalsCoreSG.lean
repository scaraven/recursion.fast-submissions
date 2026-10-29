-- New for `flock-recursive` (BLUEPRINT §10 changes 27 (B) step 4; stage RET-3): the declarations of
-- the 3.x verifier-shape modules that the revision 4 certificate reads, moved here verbatim (same
-- names, statements and proofs) from `FRVIRMux` (5), `FRNodeLayout` (26), `FRVIRFinalsSG` (107),
-- `FRNodeCircuit` (6). Content: `FRVIRFinalsSG`'s `finP`, `finPf` and their run lemmas, the node
-- layout constants and `FRNodeCircuit`'s `PubCells` pieces that revision 4 reads. The 3.x modules
-- import this one.
import FRVIRCompile
import FRVIRFinalsCore

/-! ## From `FRVIRMux` (5 declarations) -/

section

namespace FR

namespace Circ

open RecursionFast

/-- The mux's selector forms: M's `one` cell and the three selector cells. -/
def muxP (one : ℕ) (cells : Kind → ℕ) : Params := ⟨Lin.cell one, fun κ => Lin.cell (cells κ)⟩

/-- **`compileMux`**: `compile` in gated mode. -/
def compileMux (one : ℕ) (cells : Kind → ℕ) (base : ℕ) (ops : List Op) : CS :=
  compile (muxP one cells) base ops

/-- The one-hot rows of the selector cells (A.8 `assertOneHot`: 3 products, 1 linear). -/
def OneHotRows (w : Asg) (one : ℕ) (cells : Kind → ℕ) : Prop :=
  w (cells .L32) * w (cells .P30) = 0 ∧ w (cells .L32) * w (cells .N30) = 0 ∧
  w (cells .P30) * w (cells .N30) = 0 ∧
  w one * (w (cells .L32) + w (cells .P30) + w (cells .N30)) = w one

/-- A cell is a bit (Lr's Booleanity). -/
def IsBitCell (w : Asg) (i : ℕ) : Prop := w i = 0 ∨ w i = 1

/-- **The one-hot rows fix the kind**: Boolean selector cells satisfying them are one-hot. -/
theorem oneHot_of_rows {w : Asg} {one : ℕ} {cells : Kind → ℕ} (hone : w one = 1)
    (hb : ∀ κ, IsBitCell w (cells κ)) (h : OneHotRows w one cells) :
    ∃ κ, SelOk w (muxP one cells) κ := by
  obtain ⟨h1, h2, h3, h4⟩ := h
  rw [hone, one_mul] at h4
  have bL := hb .L32; have bP := hb .P30; have bN := hb .N30
  simp only [muxP, SelOk, Lin.ev_cell, hone, true_and]
  rcases bL with eL | eL <;> rcases bP with eP | eP <;> rcases bN with eN | eN <;>
    simp only [eL, eP, eN, add_zero, zero_add, mul_one, one_mul, mul_zero, zero_mul] at h1 h2 h3 h4
  all_goals first
    | exact absurd h4 zero_ne_one
    | exact absurd h1 one_ne_zero | exact absurd h2 one_ne_zero | exact absurd h3 one_ne_zero
    | skip
  · exact ⟨.N30, fun κ => by cases κ <;> simp [eL, eP, eN]⟩
  · exact ⟨.P30, fun κ => by cases κ <;> simp [eL, eP, eN]⟩
  · exact ⟨.L32, fun κ => by cases κ <;> simp [eL, eP, eN]⟩

end Circ

end FR

end

/-! ## From `FRNodeLayout` (26 declarations) -/

section

namespace FR

namespace Layout

/-- Compressions of one digest chain (§4.2, revision 3.13: `chainLen_eq`; 23,225 under 3.12). -/
def chainN : ℕ := 23146

/-- `hashStmt`'s blocks: 3 per slot. -/
def stmtBase : ℕ := 2 * chainN

/-- WOTS: 133 chains × 3 steps, the key leaf's 67 blocks, the path's 16 × 2 per slot. -/
def wotsBase : ℕ := stmtBase + 6

def wotsSlot : ℕ := 133 * 3 + 67 + 2 * 16

/-- The mirror sub-region `WM` (revision 3.14, A.6: 146 blocks per slot, after both WOTS runs). -/
def wmBase : ℕ := wotsBase + 2 * wotsSlot

/-- Region L: base and used blocks (revision 3.12: moved from 46,336 past H's end, 47,480 then;
47,322 under revision 3.13, the base kept: stage-review changes 19). -/
def lBase : ℕ := 47616

/-- Region M: base, elements, blocks, per-slot elements. -/
def mBase : ℕ := 3 * 2 ^ 14

def slotM : ℕ := 2 ^ 20

/-- **M's `one` cell** (revision 3.6, S-E2 F-4): element `Mbase · 128` of `f`, pinned to `1` by a
point claim (`PubCells`); the compiler's `Params.one` is this cell. -/
def oneCell : ℕ := mBase * 128

/-- The node's blocks (`2^(30 − 14)`). -/
def nodeBlocks : ℕ := 2 ^ 16

/-- Blocks `[lo, hi)` of one kind. -/
structure Iv where
  kind : BlockKind
  lo : ℕ
  hi : ℕ

/-- Slot `σ`'s digest chain. -/
def chainIvs (σ : ℕ) : List Iv :=
  [⟨.streamStart, σ * chainN, σ * chainN + 1⟩, ⟨.stream, σ * chainN + 1, (σ + 1) * chainN⟩]

/-- `hashStmt`'s blocks A, B1, B2 of both slots. -/
def stmtIvs : List Iv :=
  (List.range 2).flatMap fun σ =>
    let b := stmtBase + 3 * σ
    [⟨.hashA, b, b + 1⟩, ⟨.hashB1, b + 1, b + 2⟩, ⟨.hashB2, b + 2, b + 3⟩]

/-- Slot `σ`'s WOTS blocks, consecutive (§4.2): chain steps, key leaf, path steps. -/
def wotsIvs (σ : ℕ) : List Iv :=
  let b := wotsBase + wotsSlot * σ
  [⟨.w43, b, b + 399⟩, ⟨.hashB1, b + 399, b + 400⟩, ⟨.stream, b + 400, b + 465⟩,
    ⟨.streamEnd41, b + 465, b + 466⟩] ++
  (List.range 16).flatMap fun t =>
    [⟨.hashB1, b + 466 + 2 * t, b + 467 + 2 * t⟩, ⟨.hashB2, b + 467 + 2 * t, b + 468 + 2 * t⟩]

/-- **`nodeLayout`**: the node's kind intervals in address order; `WM`, the spares, L and M have
the kind `free` (`A₀ = B₀ = I`, revision 3.8.1), so `Sel ≡ 1`. -/
def nodeLayout : List Iv :=
  chainIvs 0 ++ chainIvs 1 ++ stmtIvs ++ wotsIvs 0 ++ wotsIvs 1 ++ [⟨.free, wmBase, nodeBlocks⟩]

/-- The intervals of a kind (`kindInd`'s prefix sums run over them). -/
def kindIvs (κ : BlockKind) : List (ℕ × ℕ) :=
  (nodeLayout.filter fun iv => iv.kind == κ).map fun iv => (iv.lo, iv.hi)

/-- Nonempty and in increasing order, without overlap. -/
def chained : List Iv → Bool
  | a :: b :: t => decide (a.lo < a.hi) && decide (a.hi ≤ b.lo) && chained (b :: t)
  | [a] => decide (a.lo < a.hi)
  | [] => true

/-- **The kind of WOTS block `off` of a slot** (`off < wotsSlot = 498`), as `wotsIvs` lays them out:
chain `i`'s step `s` at `3 i + s` (`off < 399`, kind `w43`); the key leaf at `399 … 465`
(`hashB1` at 399, 65 `stream` blocks at 400–464, `streamEnd41` at 465); path step `t` at
`466 + 2 t` (`hashB1`) and `467 + 2 t` (`hashB2`). -/
def wotsKindAt (off : ℕ) : BlockKind :=
  if off < 399 then .w43
  else if off = 399 then .hashB1
  else if off < 465 then .stream
  else if off = 465 then .streamEnd41
  else if (off - 466) % 2 = 0 then .hashB1 else .hashB2

/-- Mirror sources per slot: `0 … 580` (581 of the 584 positions of 146 blocks). -/
def mirSources : ℕ := 581

/-- **The intervals are disjoint and in order** (so `Ind` partitions `Sel`). -/
theorem nodeLayout_chained : chained nodeLayout = true := by decide

/-- Slot `σ`'s selector cells in L (A.7, revision 3.11 F-5: after `sig` 299, the digits' 266
bit-elements, selectors 399, position bits 7,552). -/
def selCells (σ : ℕ) : FR.Kind → ℕ
  | .L32 => lBase * 128 + σ * 2 ^ 14 + 8516
  | .P30 => lBase * 128 + σ * 2 ^ 14 + 8517
  | .N30 => lBase * 128 + σ * 2 ^ 14 + 8518

/-- Slot `σ`'s first fresh M cell (after the `one` cell). -/
def slotBase (σ : ℕ) : ℕ := oneCell + 1 + σ * slotM

/-- Slot `σ`'s compiled program (`compileMux (gen fin .mux)`). -/
def slotCS (fin : Finals) (σ : ℕ) : Circ.CS :=
  Circ.compileMux oneCell (selCells σ) (slotBase σ) (gen fin .mux).ops

/-- **The node's M rows**: both slots'. -/
def nodeRows (fin : Finals) : List Circ.Row := (slotCS fin 0).rowList ++ (slotCS fin 1).rowList

/-- Slot `σ`'s declared bit cells in L (A.7, revision 3.11 F-5: after `sig`'s 299 elements, the
digits' 266 bit-elements (two per base-4 digit, the checksum's included), the step selectors 399,
the position bits 7,552 and the kind selector 3, each a bit-element). -/
def lBitCells (σ : ℕ) : List ℕ :=
  (List.range (266 + 399 + 7552 + 3)).map fun j => lBase * 128 + σ * 2 ^ 14 + 299 + j

/-- **L's rows** (`N_L = 2^15`): `b · (1 − b) = 0` for every declared bit of both slots, with M's
`one` cell. -/
def lRows : List Circ.Row :=
  ((List.range 2).flatMap lBitCells).map fun b =>
    ⟨Circ.Lin.cell b, (Circ.Lin.cell oneCell).sub (Circ.Lin.cell b), []⟩

end Layout

end FR

end

/-! ## From `FRVIRFinalsSG` (107 declarations) -/

section

namespace FR

/-- The nodes of `S`, as `quirky_claim_split` indexes them. -/
def sNodeF (b : Fin 64) : F := skipNode (Fin.castLE (by norm_num) b)

theorem foldl_mul_eq {α : Type*} (g : α → F) :
    ∀ (xs : List α) (c : F), xs.foldl (fun a j => a * g j) c = c * (xs.map g).prod
  | [], c => by simp
  | x :: xs, c => by rw [List.foldl_cons, foldl_mul_eq g xs, List.map_cons, List.prod_cons]; ring

theorem xS_of_lt {j : ℕ} (hj : j < 64) : xS j = sNodeF ⟨j, hj⟩ := by
  simp only [xS, sNodeF, Nat.mod_eq_of_lt (show j < 128 by omega)]; rfl

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
    ([.getF e q, .mulKF y b, .addK acc (b + 1)] : List Op) ++ accOps e ys (q + 1) (b + 2) (b + 3)

/-- The register `accOps` leaves its sum in. -/
def accOut : Reg → ℕ → List Reg → Reg
  | acc, _, [] => acc
  | _, b, _ :: ys => accOut (b + 2) (b + 3) ys

/-- **`finP i`, `i < 4`**: `claim0(P1.(i+1)) = claimN(P1.i) + Σ_q eq(κ_c, bits₉(q))·y_q`. Exports
the batched claim. -/
def finPLow (i : ℕ) : FinField := fun fi b =>
  let out := accOut (b + 3) (b + 4) (ysOf fi i)
  (([.packF (kcOf fi i), .eqTable b, .const (fun _ => .k 0),
      .addK (p1ClaimN fi i) (b + 2)] : List Op) ++
    accOps (b + 1) (ysOf fi i) 0 (b + 3) (b + 4) ++
    ([.assertEq out (p1Claim0 fi (i + 1)) allK] : List Op), [out])

/-- One Horner layer: `x'[c] = x[c] + w·x[c + n]` for `c < n` (`xs` of length `2n`), two registers
per `c`. -/
def layerOps (w : Reg) (xs : List Reg) (n b : ℕ) : ℕ → List Op
  | 0 => []
  | k + 1 => layerOps w xs n b k ++
      ([.mulK w (xs.getD (k + n) 0), .addK (xs.getD k 0) (b + 2 * k)] : List Op)

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
  ((List.range 7).map (fun v => .tensorW j (units.getD v 0)) : List Op) ++
    hornerKOps ((List.range 7).map (b + ·)) 7 fin (b + 7) ++
    ([.assertEq (hornerKOut 7 fin (b + 7)) y allK] : List Op)

/-- The unit vector `e_v` of `K^7`. -/
def unitK (v : ℕ) : Array K := ((List.range 7).map fun u => if u = v then (1 : K) else 0).toArray

/-- **`finP 4`**: `y_q = Enc₄(final)[p_q]` for every `q`, and Pf's initial claim is `claimN(P1.4)`.
Registers: the 128 final elements, the 7 unit vectors, then `encW` per position. -/
def finP4 : FinField := fun fi b =>
  let fin := (List.range 128).map (b + ·)
  let units := (List.range 7).map (b + 128 + ·)
  (((List.range 128).map (fun c => .piElemK fFinal (32 * c)) : List Op) ++
    ((List.range 7).map (fun v => .const fun _ => .ak (unitK v)) : List Op) ++
    (List.range (ysOf fi 4).length).flatMap (fun q =>
      encOps units fin ((ysOf fi 4).getD q 0 - 3) ((ysOf fi 4).getD q 0) (b + 135 + encW * q)) ++
    ([.assertEq (claim0 fi "Pf") (p1ClaimN fi 4) allK] : List Op), [])

/-- **`finP i`** (A.9). -/
def finP (i : ℕ) : FinField := if i < 4 then finPLow i else finP4

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

/-- The value `tensorW j u` the frozen `tensorW` ops append (`default` for other ops). -/
def twVal (L : List Val) : Op → Val
  | .tensorW j u => .k (impl.tensorW (rd r j).toN (rd (r ++ L.toArray) u).toAK)
  | _ => default

/-- `piElemK` and `const` values (the ops of `finP 4` that read no register). -/
def p4Val : Op → Val
  | .piElemK f o => .k (K.ofBytes (bytesAt inp.π (absOff f o) 32))
  | .const c => c κ
  | _ => default

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
  src.map (srcOp one z0) ++ ([.packK ((List.range src.length).map (b + ·))] : List Op)

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
  (((List.ofFn pinnedRho).drop 1).map (fun x => .c (K.ofF x)) : List PtSrc) ++
    (((coordsR fi "Z1").take (m - 13)).map .f : List PtSrc)

/-- The Lc claim's outer point: L2's challenges `7 … 13`, then Z3's real challenges from `8`. -/
def lcSrc (fi : FinIn) (m : ℕ) : List PtSrc :=
  (((chals fi "L2" 14).drop 7).map .f : List PtSrc) ++
    ((((chals fi "Z3" 26).take (m - 6)).drop 8).map .f : List PtSrc)

/-- The Sh claim's outer point: S2's position challenges `7 … 9`, four zeros, S2's `m − 14` block
challenges. -/
def shSrc (fi : FinIn) (m : ℕ) : List PtSrc :=
  ((((chals fi "S2" 28).drop (m - 7)).take 3).map .f : List PtSrc) ++
    (List.replicate 4 (.c 0) : List PtSrc) ++
    (((chals fi "S2" 28).take (m - 14)).map .f : List PtSrc)

/-- The E4 claim's outer point (`m = 30`, revisions 3.12–3.13): all of E4's 23 challenges `r′` (RS
claim 4, `f̂(r′)`, has the packing basis as its inner weights). -/
def eSrc (fi : FinIn) : List PtSrc := (chals fi "E4" 23).map .f

/-- The points `finPf` builds: the claim points `0 … 6` (Z, Lc, Sh at `m = 32, 30`; E4's `r′`), the
tails `P₁[1..] … P₄[1..]` at `m = 32` (`7 … 10`) and `m = 30` (`11 … 14`), `P₀` (`15`, `16`). -/
def pfPts (fi : FinIn) : List (List PtSrc) :=
  [zSrc fi 32, zSrc fi 30, lcSrc fi 32, lcSrc fi 30, shSrc fi 32, shSrc fi 30, eSrc fi] ++
    ((List.range 4).map (fun k => (tailRegs fi 32 (k + 1)).map .k) : List (List PtSrc)) ++
    ((List.range 4).map (fun k => (tailRegs fi 30 (k + 1)).map .k) : List (List PtSrc)) ++
    ([(p0Regs fi 32).map .k, (p0Regs fi 30).map .k] : List (List PtSrc))

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
    ([.mulKF (b + 22) pw, .addK acc (b + 23), .mulF pw kp] : List Op)

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
  ([.packF (kcOf fi (k - 1)), .eqTable b] : List Op) ++
    ((List.range ys.length).map (fun q => .tensorW (ys.getD q 0 - 3) T) : List Op) ++
    accOps (b + 1) (tRegs fi (k - 1) b) 0 W (b + 2 + ys.length) ++
    ([.mulK ((sRegs fi k).headD 0) cu, .addK one a,
     .mulK (a + 1) (accOut W (b + 2 + ys.length) (tRegs fi (k - 1) b))] : List Op)

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
    ([.piElemK fFinal (32 * c), .getK E c, .mulK b (b + 1), .addK acc (b + 2)] : List Op) ++
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
  (([.const (fun _ => .k 1), .const (fun _ => .k (1 + K.u)), .const (fun _ => .k 0)] : List Op) ++
   ptsOps one z0 pts (b + 3) ++
   ([.keep is32 (P 7) (P 11), .keep is32 (P 8) (P 12), .keep is32 (P 9) (P 13),
    .keep is32 (P 10) (P 14), .keep is32 (P 15) (P 16)] : List Op) ++
   ([.packF ((List.range 7).map fun p => rs1.getD p 0),
    .rsWeight wb (fun κ => (rsPtIx κ).map P) (rs1.getD 7 0) ((outsOf fi "L3β").headD 0)
      Kind.isNode (sb + 4)] : List Op) ++
   ((List.range 23).map (fun v => .getK (sb + 4) v) : List Op) ++
   ((List.range 23).map (fun v => .addK one (wb + 2 + v)) : List Op) ++
   ([.mulF kp kp] : List Op) ++
   cellsOps one (wb + 2) (wb + 25) kp pfCells z0 cb (cb + 1) ++
   ([.keep Kind.isNode (cellsAcc pfCells z0 (cb + 1)) z0, .addK (wb + 1) ce] : List Op) ++
   lvsOps fi one cu sb [1, 2, 3, 4] (ce + 1) lb ++
   ([.packK sf, .eqTableK fb] : List Op) ++ fhOps (fb + 1) (List.range 128) z0 (fb + 2) ++
   ([.addK one (sf.getD 5 0), .addK one (sf.getD 6 0), .mulK pd (pd + 1), .keep is32 one (pd + 2),
    .mulK (lvsOut fi [1, 2, 3, 4] (ce + 1) lb) (pd + 3),
    .mulK (pd + 4) (fhOut (List.range 128) z0 (fb + 2)),
    .assertEq (pd + 5) (claimN fi "Pf") allK] : List Op), [])

theorem noAsk_map {α : Type} (l : List α) (f : α → Op) (h : ∀ a, (f a).item? = none) :
    (l.map f).filterMap Op.item? = [] := by
  rw [List.filterMap_eq_nil_iff]; simp only [List.mem_map]; rintro _ ⟨a, -, rfl⟩; exact h a

theorem noAsk_prodKOps : ∀ (xs : List Reg) (acc b : ℕ), (prodKOps xs acc b).filterMap Op.item? = []
  | [], _, _ => rfl
  | _ :: xs, _, b => by
    simp only [prodKOps, List.filterMap_cons, Op.item?]; exact noAsk_prodKOps xs b (b + 1)

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

/-- The registers of a coordinate. -/
def PtSrc.regs : PtSrc → List ℕ
  | .f x => [x]
  | .k x => [x]
  | .c _ => []

theorem ptV_app (r : Array Val) (L : List Val) (s : List PtSrc) (h : ∀ x ∈ s, x.Ok r.size) :
    ptV (r ++ L.toArray) s = ptV r s := by
  simp only [ptV]; congr 1
  refine List.map_congr_left fun x hx => ?_
  have := h x hx
  cases x with
  | f y => simp only [srcVal, rd_app_left _ _ (show y < r.size from this)]
  | k y => simp only [srcVal, rd_app_left _ _ (show y < r.size from this)]
  | c v => rfl

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

end FR

end

/-! ## From `FRNodeCircuit` (6 declarations) -/

section

namespace FR

namespace Node

open RecursionFast Circ Layout

/-- H cell of slot `σ`'s seed payload element `e` (A.7: the payload starts at stream element 1;
stream element `e'` is slot `4 + e' mod 4` of block `chainBase_σ + ⌊e'/4⌋`). -/
def seedCell (σ e : ℕ) : ℕ := (σ * chainN + (1 + e) / 4) * 128 + 4 + (1 + e) % 4

/-- **The public cells in A.7's order** (stage-review changes 15): `pub_0 = f[Mbase]`; slot 1's
`vk` and `c₁` halves; slot 2's `vk` and `c₂` halves. There are no padding cells: the stream is
`64 · 22,465` bytes, so every last block is full. -/
def pubCells : List ℕ :=
  oneCell :: (List.range 2).flatMap (fun σ => (List.range 4).map (seedCell σ))

/-- A digest's two F halves. -/
def halves (d : Digest) : List F := [dlo d, dhi d]

/-- Their values: `1`, then the digests' halves. -/
def pubVals (vk c₁ c₂ : Digest) : List F :=
  1 :: (halves vk ++ halves c₁ ++ halves vk ++ halves c₂)

/-- **`PubCells`** (§4.3, A.7): the point claims on `f` hold. -/
def PubCells (w : Asg) (vk c₁ c₂ : Digest) : Prop :=
  pubCells.map w = pubVals vk c₁ c₂

/-- Nine public cells, as many as values. -/
theorem pubCells_length (vk c₁ c₂ : Digest) :
    pubCells.length = 9 ∧ (pubVals vk c₁ c₂).length = 9 := by
  simp [pubCells, pubVals, halves]

end Node

end FR

end
