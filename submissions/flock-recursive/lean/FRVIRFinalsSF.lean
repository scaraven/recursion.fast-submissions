-- New for `flock-recursive` (BLUEPRINT §7, A.9; stage S-F).
import FRVIRFinals
import FRSkip
import FRRingSwitch

/-!
# The phase-final checks owned by S-F: `finRS`, `finE`, `finB′` (A.9)

`FRVIRFinals` holds the typed `Finals`, S-0's four fields and `s0Finals`, which takes the other
owners' fields as arguments. This module gives S-F's three (a separate module so that S-G can work
on `FRVIRFinals` at the same time; RESULT deviation 1), each with its semantic lemma against A.9:

* **`finRS`** (ring switching, row RS1; `FRRingSwitch`; A.9 revisions 3.9, 3.12): from RS0's
  `J_z = 5 × 128` slice values `s_{j,i}` (claims Z, Lc, Sh, Lr, E) and RS1's `r″ = f₀ … f₆` and `κ`,
  the claim values `α_j = Σ_i c_{j,i} s_{j,i}` (the inner weights of `rs_column`: `eqZ λ ρ₁` for Z,
  `quirky_claim_split`; `eq` of the low 7 coordinates of the claim's point for Lc, Sh, Lr,
  `ml_claim_split`; the packing basis `bb i` for E's `f̂(r′) = Σ_i b_i s_{4,i}`, whose outer point
  is all of `r′`) and the batched switched claim `v_RS = Σ_j κ^j T_j`,
  `T_j = Σ_i bitBasis i · phiRS r″ s_{j,i}` (`rsT`; `phiRS` meets `Phi`). A leaf's fourth and fifth
  claims (Lr, E) are zero: their slice values are asserted zero and `T₃`, `T₄` are left out.
  **`exec_finRS`**.
* **`finE`** (node; revision 3.12, the shape of `finLr`): `c_{E2} = eq(r_E, r_{E2})·(â_M b̂_M + ĉ_M)`
  with `â_M ‖ b̂_M ‖ ĉ_M` the E-end absorb; `c₀^{E4} = â_M + κ_E b̂_M + κ_E² ĉ_M`;
  `c_{E4} = (Ã + κ_E B̃ + κ_E² C̃)(r_{E2}, r′)·f̂(r′)` (`evalM` at the F point `r′`, `f̂(r′)` RS
  claim 5). **`flag_finE`**.
* **`finB′`**: `v* = v_RS + Σ_k κ′^(k+2) pub_k` equals P1.0's initial claim (in `K`; no `v_E` term
  since revision 3.12). The public point claims of a node, in order `k`: M's `one` cell (`1`,
  revision 3.6), then slot 0's `vk` and `c₁` and slot 1's `vk` and `c₂`, each digest as its two F
  halves (`splitDigest`); the zero padding cells come after them and add nothing to `v*`.
  **`flag_finB'`**.

Proof kit: `pureRun_append`, `pr_op`, `pr_app'`, `rdX`, `rdL`; the blocks `elemsOps` (one claim's
slice values) and `claimOps`, run by induction on the generator, never on a concrete op list. The
computed skip Lagrange weight `lagV` (with `xS`, `others`, `wInv`) is kept: it is the concrete
`eqZ` (`FRVerifier.eqZImpl`) and S-G proves it equal to `lagrangeWeight`.
-/

namespace FR
open RecursionFast

/-! ## Kit -/

section Kit
variable (impl : OpImpl) (κ : Kind) (inp : Input) (r : Array Val)

theorem pureRun_append (o₁ o₂ : List Op) (L : List Val) :
    pureRun impl κ inp (o₁ ++ o₂) r L = (pureRun impl κ inp o₁ r L).bind fun p =>
      (pureRun impl κ inp o₂ r p.1).map fun q => (q.1, p.2 && q.2) := by
  induction o₁ generalizing L with
  | nil => simp only [List.nil_append, pureRun, Option.bind_some, Bool.true_and]; simp
  | cons op o ih =>
    simp only [List.cons_append, pureRun]
    split
    · rw [ih]
      cases pureRun impl κ inp o r _ with
      | none => rfl
      | some p => simp [Option.map_map, Function.comp_def, Bool.and_assoc]
    · rfl

/-- One op appending one value with no assertion. -/
theorem pr_op {op : Op} {ops : List Op} {L : List Val} {v : Val}
    (h : evalOp impl κ inp (r ++ L.toArray) op = .vals [v] true) :
    pureRun impl κ inp (op :: ops) r L = pureRun impl κ inp ops r (L ++ [v]) := by
  simp only [pureRun, h, Bool.true_and]; cases pureRun impl κ inp ops r (L ++ [v]) <;> rfl

theorem rd_pre {L M : List Val} {x : ℕ} (h : x < r.size + L.length) :
    rd (r ++ (L ++ M).toArray) x = rd (r ++ L.toArray) x := by
  rw [← app_app]; exact rd_append_left (by simpa using h)

theorem rd_new (L : List Val) (v : Val) (M : List Val) :
    rd (r ++ (L ++ v :: M).toArray) (r.size + L.length) = v := by
  rw [rd_app]; simp

theorem rd_new1 (L : List Val) (v : Val) : rd (r ++ (L ++ [v]).toArray) (r.size + L.length) = v :=
  rd_new r L v []

end Kit

/-! ## Blocks -/

/-- The packing basis element of index `i` (`bitBasis`, A.7). -/
def bb (i : ℕ) : F := bitBasis ⟨i % 128, Nat.mod_lt _ (by decide)⟩

/-- Slice value `i` of RS claim `j` (RS0's message: claim-major, 16 bytes each). -/
def rsOff (j i : ℕ) : ℕ := 16 * (128 * j + i)

/-- One slice value of claim `j` (8 registers): `s`, its inner weight `c` (`wop i`), `c·s` into the
claim value, `Φ_{r″}(s)` (`phiRS`, `r″` in register `R`), `bitBasis i · Φ(s)` into the switched
claim. -/
def elemOps (j i : ℕ) (wop : ℕ → Op) (R aA aT b : ℕ) : List Op :=
  [.piElem fRS0 (rsOff j i), wop i, .mulF (b + 1) b, .addF aA (b + 2), .phiRS R b,
   .const (fun _ => .f (bb i)), .mulF (b + 5) (b + 4), .addF aT (b + 6)]

/-- The width of `elemOps`. -/
def elemW : ℕ := 8

/-- Slice values `i … i + n − 1` of claim `j`. -/
def elemsOps (j : ℕ) (wop : ℕ → Op) (R : Reg) : ℕ → ℕ → Reg → Reg → ℕ → List Op
  | 0, _, _, _, _ => []
  | n + 1, i, aA, aT, b =>
    elemOps j i wop R aA aT b ++ elemsOps j wop R n (i + 1) (b + 3) (b + elemW - 1) (b + elemW)

/-- The skip node `x_j` (`S` is the first 64 nodes). -/
def xS (j : ℕ) : F := skipNode ⟨j % 128, Nat.mod_lt _ (by decide)⟩

/-- The nodes other than `lo` (63 of them, in order). -/
def others (lo : ℕ) : List ℕ := (List.range 63).map fun j => if j < lo then j else j + 1

/-- The barycentric constant `(Π_{j ≠ lo} (x_lo + x_j))⁻¹`. -/
def wInv (lo : ℕ) : F := ((others lo).foldl (fun a j => a * (xS lo + xS j)) 1)⁻¹

/-- The skip Lagrange weight `L_lo(λ)`, computed. -/
def lagV (l : F) (lo : ℕ) : F := (others lo).foldl (fun a j => a * (l + xS j)) (wInv lo)

theorem others_length (lo : ℕ) : (others lo).length = 63 := by simp [others]

/-! ## The blocks run -/

section Run
variable (impl : OpImpl) (κ : Kind) (inp : Input) (r : Array Val)

theorem pr_app {o₁ o₂ : List Op} {L M : List Val}
    (h : pureRun impl κ inp o₁ r L = some (L ++ M, true)) :
    pureRun impl κ inp (o₁ ++ o₂) r L = pureRun impl κ inp o₂ r (L ++ M) := by
  rw [pureRun_append, h, Option.bind_some]; cases pureRun impl κ inp o₂ r (L ++ M) <;> simp

theorem pr_app' {o₁ o₂ : List Op} {L L' : List Val}
    (h : pureRun impl κ inp o₁ r L = some (L', true)) :
    pureRun impl κ inp (o₁ ++ o₂) r L = pureRun impl κ inp o₂ r L' := by
  rw [pureRun_append, h, Option.bind_some]; cases pureRun impl κ inp o₂ r L' <;> simp

theorem rdX (L X : List Val) (t : ℕ) :
    rd (r ++ (L ++ X).toArray) (r.size + L.length + t) = X.getD t default := by
  rw [Nat.add_assoc, rd_app]; simp [List.getElem?_append_right]

theorem rdL {L X : List Val} {y : ℕ} (h : y < r.size + L.length) :
    rd (r ++ (L ++ X).toArray) y = rd (r ++ L.toArray) y := rd_pre r h

theorem rdX0 (L X : List Val) : rd (r ++ (L ++ X).toArray) (r.size + L.length) = X.getD 0 default := by
  simpa using rdX r L X 0

/-- Slice value `i` of claim `j`. -/
def sv (inp : Input) (j i : ℕ) : F := F.ofBytes (bytesAt inp.π (absOff fRS0 (rsOff j i)) 16)

/-- **One slice value**: the claim value gains `c · s`, the switched claim `bitBasis i · Φ(s)`. -/
theorem run_elemOps (j i aA aT R : ℕ) (wop : ℕ → Op) (c A T : F) (rpp : Array F) (L : List Val)
    (hR : R < r.size + L.length) (hRv : (rd (r ++ L.toArray) R).toAF = rpp)
    (hA : aA < r.size + L.length) (hT : aT < r.size + L.length)
    (hAv : (rd (r ++ L.toArray) aA).toF = A) (hTv : (rd (r ++ L.toArray) aT).toF = T)
    (hw : ∀ X : List Val, evalOp impl κ inp (r ++ (L ++ X).toArray) (wop i) = .vals [.f c] true) :
    ∃ M, pureRun impl κ inp (elemOps j i wop R aA aT (r.size + L.length)) r L = some (L ++ M, true) ∧
      M.length = elemW ∧
      (rd (r ++ (L ++ M).toArray) (r.size + L.length + 3)).toF = A + c * sv inp j i ∧
      (rd (r ++ (L ++ M).toArray) (r.size + L.length + elemW - 1)).toF =
        T + bb i * impl.phiRS rpp (sv inp j i) := by
  set s := sv inp j i
  have tf : ∀ x, (Val.f x).toF = x := fun _ => rfl
  have e0 : evalOp impl κ inp (r ++ L.toArray) (.piElem fRS0 (rsOff j i)) = .vals [.f s] true := rfl
  have e1 : evalOp impl κ inp (r ++ (L ++ [Val.f s]).toArray) (wop i) = .vals [.f c] true := hw _
  set φ := impl.phiRS rpp s
  refine ⟨[.f s, .f c, .f (c * s), .f (A + c * s), .f φ, .f (bb i), .f (bb i * φ),
    .f (T + bb i * φ)], ?_, rfl, ?_, ?_⟩
  · simp only [elemOps, List.cons_append, List.nil_append]
    rw [pr_op impl κ inp r e0, pr_op impl κ inp r e1]
    simp only [pureRun, evalOp, List.append_assoc, List.cons_append, List.nil_append, rdX, rdX0,
      List.getD_cons_succ, List.getD_cons_zero, tf, rdL r hA, rdL r hT, rdL r hR, hAv, hTv, hRv,
      Option.map_some, Bool.true_and, Bool.and_true]
    rfl
  · rw [rdX]; rfl
  · rw [show r.size + L.length + elemW - 1 = r.size + L.length + 7 from rfl, rdX]; rfl

/-- **A claim's slice values, `n` of them**: the claim value and the switched claim as sums. -/
theorem run_elemsOps (j : ℕ) (wop : ℕ → Op) (R : ℕ) (rpp : Array F) (c : ℕ → F) (L₀ : List Val)
    (hR : R < r.size + L₀.length) (hRv : (rd (r ++ L₀.toArray) R).toAF = rpp)
    (hw : ∀ i (X : List Val), evalOp impl κ inp (r ++ (L₀ ++ X).toArray) (wop i) = .vals [.f (c i)] true)
    (n : ℕ) : ∀ (i aA aT : ℕ) (A T : F) (X : List Val), aA < r.size + L₀.length + X.length →
    aT < r.size + L₀.length + X.length → (rd (r ++ (L₀ ++ X).toArray) aA).toF = A →
    (rd (r ++ (L₀ ++ X).toArray) aT).toF = T →
    ∃ M, pureRun impl κ inp (elemsOps j wop R n i aA aT (r.size + L₀.length + X.length)) r (L₀ ++ X) =
      some (L₀ ++ X ++ M, true) ∧ M.length = n * elemW ∧
      (0 < n → (rd (r ++ (L₀ ++ X ++ M).toArray) (r.size + L₀.length + X.length + (n - 1) * elemW + 3)).toF =
          A + ∑ k ∈ Finset.range n, c (i + k) * sv inp j (i + k) ∧
        (rd (r ++ (L₀ ++ X ++ M).toArray) (r.size + L₀.length + X.length + n * elemW - 1)).toF =
          T + ∑ k ∈ Finset.range n, bb (i + k) * impl.phiRS rpp (sv inp j (i + k))) := by
  induction n with
  | zero => intro i aA aT A T X _ _ _ _; exact ⟨[], by simp [elemsOps, pureRun], by simp, by simp⟩
  | succ n ih =>
    intro i aA aT A T X hA hT hAv hTv
    have hlen : r.size + (L₀ ++ X).length = r.size + L₀.length + X.length := by simp; omega
    obtain ⟨M₁, h₁, hl₁, hα, hτ⟩ := run_elemOps impl κ inp r j i aA aT R wop (c i) A T rpp (L₀ ++ X)
      (by rw [hlen]; omega) (by rw [rdL r hR, hRv]) (by rw [hlen]; exact hA) (by rw [hlen]; exact hT)
      hAv hTv (fun Y => by rw [List.append_assoc]; exact hw i _)
    rw [hlen] at h₁ hα hτ
    obtain ⟨M₂, h₂, hl₂, hv₂⟩ := ih (i + 1) (r.size + L₀.length + X.length + 3)
      (r.size + L₀.length + X.length + elemW - 1) (A + c i * sv inp j i)
      (T + bb i * impl.phiRS rpp (sv inp j i)) (X ++ M₁)
      (by simp only [List.length_append, hl₁, elemW]; omega)
      (by simp only [List.length_append, hl₁, elemW]; omega)
      (by simpa only [List.append_assoc] using hα) (by simpa only [List.append_assoc] using hτ)
    have hb : r.size + L₀.length + (X ++ M₁).length = r.size + L₀.length + X.length + elemW := by
      simp [hl₁]; omega
    rw [hb] at h₂ hv₂
    refine ⟨M₁ ++ M₂, ?_, by simp [hl₁, hl₂]; ring, fun _ => ?_⟩
    · simp only [elemsOps]
      rw [pr_app impl κ inp r h₁, List.append_assoc L₀ X M₁, h₂]; simp
    · rcases Nat.eq_zero_or_pos n with rfl | hn
      · rw [Nat.zero_mul, List.length_eq_zero_iff] at hl₂; subst hl₂
        simp only [List.append_nil, Nat.zero_add, Finset.sum_range_one, Nat.add_zero, Nat.sub_self,
          Nat.zero_mul, Nat.one_mul]
        exact ⟨hα, hτ⟩
      · obtain ⟨h3, h4⟩ := hv₂ hn
        have hk : ∀ k, i + 1 + k = i + (k + 1) := fun k => by omega
        simp only [List.append_assoc] at h3 h4 ⊢
        refine ⟨?_, ?_⟩
        · rw [show r.size + L₀.length + X.length + (n + 1 - 1) * elemW + 3 =
            r.size + L₀.length + X.length + elemW + (n - 1) * elemW + 3 by
              simp only [elemW]; omega, h3, Finset.sum_range_succ']
          simp only [hk, Nat.add_zero]; ring
        · rw [show r.size + L₀.length + X.length + (n + 1) * elemW - 1 =
            r.size + L₀.length + X.length + elemW + n * elemW - 1 by
              simp only [elemW]; omega, h4, Finset.sum_range_succ']
          simp only [hk, Nat.add_zero]; ring

/-- One claim: a zero, then its 128 slice values (width `1 + 128 · elemW`). -/
def claimOps (j : ℕ) (wop : ℕ → Op) (R : Reg) (b : ℕ) : List Op :=
  .const (fun _ => .f 0) :: elemsOps j wop R 128 0 b b (b + 1)

theorem run_claimOps (j : ℕ) (wop : ℕ → Op) (R : ℕ) (rpp : Array F) (c : ℕ → F) (L₀ X : List Val)
    (hR : R < r.size + L₀.length) (hRv : (rd (r ++ L₀.toArray) R).toAF = rpp)
    (hw : ∀ i (X : List Val), evalOp impl κ inp (r ++ (L₀ ++ X).toArray) (wop i) = .vals [.f (c i)] true) :
    ∃ M, pureRun impl κ inp (claimOps j wop R (r.size + L₀.length + X.length)) r (L₀ ++ X) =
      some (L₀ ++ X ++ M, true) ∧ M.length = 1 + 128 * elemW ∧
      (rd (r ++ (L₀ ++ X ++ M).toArray) (r.size + L₀.length + X.length + 127 * elemW + 4)).toF =
        ∑ k ∈ Finset.range 128, c k * sv inp j k ∧
      (rd (r ++ (L₀ ++ X ++ M).toArray) (r.size + L₀.length + X.length + 128 * elemW)).toF =
        ∑ k ∈ Finset.range 128, bb k * impl.phiRS rpp (sv inp j k) := by
  set B := r.size + L₀.length + X.length
  have e0 : evalOp impl κ inp (r ++ (L₀ ++ X).toArray) (.const (fun _ => .f 0)) = .vals [.f 0] true := rfl
  have hz : (rd (r ++ (L₀ ++ (X ++ [Val.f 0])).toArray) B).toF = 0 := by
    rw [← List.append_assoc, show B = r.size + (L₀ ++ X).length by simp [B]; omega, rd_new1]; rfl
  obtain ⟨M, hM, hl, hv⟩ := run_elemsOps impl κ inp r j wop R rpp c L₀ hR hRv hw 128 0 B B 0 0
    (X ++ [Val.f 0]) (by simp [B]) (by simp [B]) hz hz
  have hb : r.size + L₀.length + (X ++ [Val.f 0]).length = B + 1 := by simp [B]; omega
  rw [hb] at hM hv
  obtain ⟨h1, h2⟩ := hv (by decide)
  refine ⟨[Val.f 0] ++ M, ?_, by simp [hl]; omega, ?_, ?_⟩
  · simp only [claimOps]; rw [pr_op impl κ inp r e0]
    simp only [List.append_assoc] at hM ⊢; exact hM
  · simp only [List.append_assoc, zero_add] at h1 ⊢
    rw [show B + 127 * elemW + 4 = B + 1 + (128 - 1) * elemW + 3 from rfl, h1]
  · simp only [List.append_assoc, zero_add] at h2 ⊢
    rw [show B + 128 * elemW = B + 1 + 128 * elemW - 1 from rfl, h2]

end Run

/-! ## `finRS` (A.9, row RS1; revisions 3.9, 3.12) -/

/-- `v_RS` by Horner in `κ` from the switched claims `T₀ … T₄` (registers `t₀ … t₄`; a leaf's
`T₃ + κ T₄` replaced by `0`), from register `d`; then a leaf's zero check of claims 3 and 4's slice
values (revision 3.12: claim 4 is E's `f̂(r′)`, node only). -/
def rsTail (kap t₀ t₁ t₂ t₃ t₄ d : ℕ) : List Op :=
  [.const (fun _ => .f 0), .mulF kap t₄, .addF t₃ (d + 1), .keep Kind.isNode (d + 2) d,
   .mulF kap (d + 3), .addF t₂ (d + 4), .mulF kap (d + 5), .addF t₁ (d + 6), .mulF kap (d + 7),
   .addF t₀ (d + 8), .piField fRS0 (rsOff 3 0) 4096, .assertZero (d + 10) (fun κ => !κ.isNode)]

/-- RS1's `r″ = f₀ … f₆` (coordinates 0–6). -/
def rsFsRegs (fi : FinIn) : List Reg := (List.range 7).map fun p => (coordsR fi "RS1").getD p 0

/-- **`finRS`** (A.9 revisions 3.9, 3.12, `J_z = 5`): the claim values `α_Z, α_Lc, α_Sh, α_Lr, α_E`
and `v_RS` (exports, in this order). Registers from `b`: `ρ₁` (A.1's first pinned coordinate),
`eqZ λ ρ₁`, the three `eq` tables (Lc, Sh, Lr) after their points, `r″`; the claims from `b + 9`,
`1 + 128 · 8` each (claim 4, E's `f̂(r′)`, weighted by the packing basis `bb i`: `f̂(r′) =
Σ_i b_i s_{4,i}`); then `rsTail`. -/
def finRS : FinField := fun fi b =>
  let kap := (coordsR fi "RS1").getD 7 0
  let lam := (outsOf fi "Z2").headD 0
  let c₀ := b + 9
  let cw := 1 + 128 * elemW
  let d := c₀ + 5 * cw
  ([.const (fun _ => .f (pinnedRho 0)), .eqZ lam b,
    .packF ((chals fi "L2" 14).take 7), .eqTable (b + 2),
    .packFK (fun κ => ((chals fi "S2" 28).drop (κ.m - 14)).take 7), .eqTable (b + 4),
    .packF ((chals fi "Lr4" 15).take 7), .eqTable (b + 6), .packF (rsFsRegs fi)] ++
   claimOps 0 (fun i => .getF (b + 1) i) (b + 8) c₀ ++
   claimOps 1 (fun i => .getF (b + 3) i) (b + 8) (c₀ + cw) ++
   claimOps 2 (fun i => .getF (b + 5) i) (b + 8) (c₀ + 2 * cw) ++
   claimOps 3 (fun i => .getF (b + 7) i) (b + 8) (c₀ + 3 * cw) ++
   claimOps 4 (fun i => .const (fun _ => .f (bb i))) (b + 8) (c₀ + 4 * cw) ++
   rsTail kap (c₀ + cw - 1) (c₀ + 2 * cw - 1) (c₀ + 3 * cw - 1) (c₀ + 4 * cw - 1) (c₀ + 5 * cw - 1) d,
   (List.range 5).map (fun j => c₀ + j * cw + 127 * elemW + 4) ++ [d + 9])

/-- `finRS`'s export index of `v_RS` (after the `J_z = 5` claim values). -/
def nRS : ℕ := 5

/-- The bytes of claims 3 and 4's slice values (a leaf's are zero). -/
def rsLeafZero (inp : Input) : Bool :=
  (inp.π.extract (absOff fRS0 (rsOff 3 0)) (absOff fRS0 (rsOff 3 0) + 4096)).data.all (· == 0)

theorem run_rsTail (impl : OpImpl) (κ : Kind) (inp : Input) (r : Array Val) (kap t₀ t₁ t₂ t₃ t₄ : ℕ)
    (Lc : List Val) (T₀ T₁ T₂ T₃ T₄ kp : F) (hk : kap < r.size) (hkv : (rd r kap).toF = kp)
    (h₀ : t₀ < r.size + Lc.length) (h₁ : t₁ < r.size + Lc.length) (h₂ : t₂ < r.size + Lc.length)
    (h₃ : t₃ < r.size + Lc.length) (h₄ : t₄ < r.size + Lc.length)
    (v₀ : (rd (r ++ Lc.toArray) t₀).toF = T₀) (v₁ : (rd (r ++ Lc.toArray) t₁).toF = T₁)
    (v₂ : (rd (r ++ Lc.toArray) t₂).toF = T₂) (v₃ : (rd (r ++ Lc.toArray) t₃).toF = T₃)
    (v₄ : (rd (r ++ Lc.toArray) t₄).toF = T₄) :
    ∃ M, pureRun impl κ inp (rsTail kap t₀ t₁ t₂ t₃ t₄ (r.size + Lc.length)) r Lc =
        some (Lc ++ M, κ.isNode || rsLeafZero inp) ∧
      (rd (r ++ (Lc ++ M).toArray) (r.size + Lc.length + 9)).toF =
        T₀ + kp * (T₁ + kp * (T₂ + kp * (if κ.isNode then T₃ + kp * T₄ else 0))) := by
  have tf : ∀ x, (Val.f x).toF = x := fun _ => rfl
  have hkr : ∀ X : List Val, (rd (r ++ X.toArray) kap).toF = kp := fun X => by rw [rd_app_left r X hk, hkv]
  have rL : ∀ {t T} (X : List Val), t < r.size + Lc.length → (rd (r ++ Lc.toArray) t).toF = T →
      (rd (r ++ (Lc ++ X).toArray) t).toF = T := fun X h v => by rw [rdL r h, v]
  set y := (if κ.isNode then T₃ + kp * T₄ else 0)
  set v' : Val := if κ.isNode = true then Val.f (T₃ + kp * T₄) else Val.f 0
  have hv' : (if κ.isNode = true then Val.f (T₃ + kp * T₄) else Val.f 0).toF = y := by
    simp only [y]; split <;> rfl
  set by₁ := inp.π.extract (absOff fRS0 (rsOff 3 0)) (absOff fRS0 (rsOff 3 0) + 4096)
  refine ⟨[.f 0, .f (kp * T₄), .f (T₃ + kp * T₄), v', .f (kp * y), .f (T₂ + kp * y),
    .f (kp * (T₂ + kp * y)), .f (T₁ + kp * (T₂ + kp * y)), .f (kp * (T₁ + kp * (T₂ + kp * y))),
    .f (T₀ + kp * (T₁ + kp * (T₂ + kp * y))), .b by₁], ?_, ?_⟩
  · simp only [rsTail, pureRun, evalOp, List.append_assoc, List.cons_append, List.nil_append,
      rdX, rdX0, List.getD_cons_succ, List.getD_cons_zero, hkr, tf,
      rL _ h₀ v₀, rL _ h₁ v₁, rL _ h₂ v₂, rL _ h₃ v₃, rL _ h₄ v₄, hv', Bool.not_not, Val.isZero,
      Option.map_some, Bool.true_and, Bool.and_true, rsLeafZero]
    rfl
  · rw [rdX]; rfl

section RS
variable (impl : OpImpl) (κ : Kind) (inp : Input) (fi : FinIn) (r : Array Val)

/-- The F values of registers, as an array. -/
def ptF (xs : List Reg) : Array F := (xs.map (fv r)).toArray

/-- **The inner weights** `c_{j,i}` of the five claims (`rs_column`): `eqZ λ ρ₁` for Z; `eq` at the
low 7 coordinates of Lc's (L2), Sh's (S2's position part) and Lr's (Lr4) points; the packing basis
`bb i` for E's `f̂(r′)` (revision 3.12). -/
def rsW (j i : ℕ) : F :=
  match j with
  | 0 => (impl.eqZ (fv r ((outsOf fi "Z2").headD 0)) (pinnedRho 0)).getD i 0
  | 1 => (eqTab (ptF r ((chals fi "L2" 14).take 7))).getD i 0
  | 2 => (eqTab (ptF r (((chals fi "S2" 28).drop (κ.m - 14)).take 7))).getD i 0
  | 3 => (eqTab (ptF r ((chals fi "Lr4" 15).take 7))).getD i 0
  | _ => bb i

/-- **Claim `j`'s value** `α_j = Σ_i c_{j,i} s_{j,i}`. -/
def rsAlpha (j : ℕ) : F := ∑ k ∈ Finset.range 128, rsW impl κ fi r j k * sv inp j k

/-- **Claim `j`'s switched claim** `T_j = Σ_i bitBasis i · Φ_{r″}(s_{j,i})` (`rsT`). -/
def rsTv (j : ℕ) : F := ∑ k ∈ Finset.range 128, bb k * impl.phiRS (ptF r (rsFsRegs fi)) (sv inp j k)

/-- **`v_RS = Σ_j κ^j T_j`** (Horner; a leaf's `T₃`, `T₄` are `0`). -/
def rsV : F :=
  let kp := fv r ((coordsR fi "RS1").getD 7 0)
  rsTv impl inp fi r 0 + kp * (rsTv impl inp fi r 1 + kp * (rsTv impl inp fi r 2 +
    kp * (if κ.isNode then rsTv impl inp fi r 3 + kp * rsTv impl inp fi r 4 else 0)))

/-- `finRS`'s flag: a leaf's fourth and fifth claims have zero slice values. -/
def relRS : Bool := κ.isNode || rsLeafZero inp

/-- The registers `finRS` reads. -/
def rsRefs : List Reg :=
  (List.range 8).map (fun p => (coordsR fi "RS1").getD p 0) ++ [(outsOf fi "Z2").headD 0] ++
    (chals fi "L2" 14).take 7 ++ ((chals fi "S2" 28).drop (κ.m - 14)).take 7 ++ (chals fi "Lr4" 15).take 7

/-- **`exec_finRS`** (A.9, RS): `finRS` asks nothing; its flag is `relRS` (a leaf's fourth and fifth
claims are zero), its exports are the claim values `α_Z, α_Lc, α_Sh, α_Lr, α_E` (`rsAlpha`) and
`v_RS` (`rsV`). -/
theorem exec_finRS (hin : ∀ x ∈ rsRefs κ fi, x < r.size) :
    ∃ L, pureRun impl κ inp (finRS fi r.size).1 r [] = some (L, relRS κ inp) ∧
      (∀ j < 5, (rd (r ++ L.toArray) ((finRS fi r.size).2.getD j 0)).toF = rsAlpha impl κ inp fi r j) ∧
      (rd (r ++ L.toArray) ((finRS fi r.size).2.getD nRS 0)).toF = rsV impl κ inp fi r := by
  simp only [rsRefs, List.mem_append, List.mem_map, List.mem_range, List.mem_cons,
    List.not_mem_nil, or_false] at hin
  have tf : ∀ x, (Val.f x).toF = x := fun _ => rfl
  have hW : elemW = 8 := rfl
  set kap := (coordsR fi "RS1").getD 7 0 with hkapd
  set lam := (outsOf fi "Z2").headD 0 with hlamd
  have hkap : kap < r.size := hin _ (.inl (.inl (.inl (.inl ⟨7, by omega, rfl⟩))))
  have hlam : lam < r.size := hin _ (.inl (.inl (.inl (.inr rfl))))
  set x1 := (chals fi "L2" 14).take 7
  set x2 := ((chals fi "S2" 28).drop (κ.m - 14)).take 7
  set x3 := (chals fi "Lr4" 15).take 7
  set x4 := rsFsRegs fi
  have hx1 : ∀ x ∈ x1, x < r.size := fun x h => hin x (.inl (.inl (.inr h)))
  have hx2 : ∀ x ∈ x2, x < r.size := fun x h => hin x (.inl (.inr h))
  have hx3 : ∀ x ∈ x3, x < r.size := fun x h => hin x (.inr h)
  have hx4 : ∀ x ∈ x4, x < r.size := fun x h => by
    simp only [x4, rsFsRegs, List.mem_map, List.mem_range] at h
    obtain ⟨p, hp, rfl⟩ := h; exact hin _ (.inl (.inl (.inl (.inl ⟨p, by omega, rfl⟩))))
  set ρ := pinnedRho 0
  set p1 := ptF r x1; set p2 := ptF r x2; set p3 := ptF r x3; set p4 := ptF r x4
  set ez := impl.eqZ (fv r lam) ρ
  set L₀ : List Val := [.f ρ, .af ez, .af p1, .af (eqTab p1), .af p2, .af (eqTab p2),
    .af p3, .af (eqTab p3), .af p4] with hL₀
  have hpk : ∀ (xs : List Reg), (∀ x ∈ xs, x < r.size) → ∀ X : List Val,
      (xs.map fun x => (rd (r ++ X.toArray) x).toF).toArray = ptF r xs := fun xs h X => by
    rw [ptF, map_rd_app r X xs h]
  have es : ∀ ops, pureRun impl κ inp ([.const (fun _ => .f ρ), .eqZ lam r.size,
      .packF x1, .eqTable (r.size + 2),
      .packFK (fun κ => ((chals fi "S2" 28).drop (κ.m - 14)).take 7), .eqTable (r.size + 4),
      .packF x3, .eqTable (r.size + 6), .packF x4] ++ ops) r [] = pureRun impl κ inp ops r L₀ := by
    intro ops
    simp only [List.cons_append, List.nil_append]
    rw [pr_op impl κ inp r (v := .f ρ) rfl,
      pr_op impl κ inp r (v := .af ez) (by
        simp only [evalOp, rd_app0, rd_app_left r _ hlam, List.nil_append, List.getD_cons_zero]; rfl),
      pr_op impl κ inp r (v := .af p1) (by simp only [evalOp, hpk x1 hx1]; rfl),
      pr_op impl κ inp r (v := .af (eqTab p1)) (by
        simp only [evalOp, rd_app, List.nil_append, List.append_assoc, List.cons_append,
          List.getD_cons_succ, List.getD_cons_zero]; rfl),
      pr_op impl κ inp r (v := .af p2) (by
        simp only [evalOp]
        rw [show List.take 7 (List.drop (κ.m - 14) (chals fi "S2" 28)) = x2 from rfl, hpk x2 hx2]),
      pr_op impl κ inp r (v := .af (eqTab p2)) (by
        simp only [evalOp, rd_app, List.nil_append, List.append_assoc, List.cons_append,
          List.getD_cons_succ, List.getD_cons_zero]; rfl),
      pr_op impl κ inp r (v := .af p3) (by simp only [evalOp, hpk x3 hx3]; rfl),
      pr_op impl κ inp r (v := .af (eqTab p3)) (by
        simp only [evalOp, rd_app, List.nil_append, List.append_assoc, List.cons_append,
          List.getD_cons_succ, List.getD_cons_zero]; rfl),
      pr_op impl κ inp r (v := .af p4) (by simp only [evalOp, hpk x4 hx4]; rfl)]
    simp [hL₀]
  have hL0 : L₀.length = 9 := rfl
  have hrd : ∀ t < 9, ∀ X : List Val, rd (r ++ (L₀ ++ X).toArray) (r.size + t) = L₀.getD t default :=
    fun t ht X => by rw [rd_app, List.getD_append _ _ _ _ (by rw [hL0]; omega)]
  have hwE : ∀ t (ht : t < 9) (p : Array F), L₀.getD t default = .af p → ∀ i (X : List Val),
      evalOp impl κ inp (r ++ (L₀ ++ X).toArray) (.getF (r.size + t) i) =
        .vals [.f (p.getD i 0)] true := fun t ht p hp i X => by
    simp only [evalOp, hrd t ht X, hp]; rfl
  have hR : r.size + 8 < r.size + L₀.length := by rw [hL0]; omega
  have hRv : (rd (r ++ L₀.toArray) (r.size + 8)).toAF = p4 := by
    have h8 := hrd 8 (by decide) []; rw [List.append_nil] at h8; rw [h8]; rfl
  obtain ⟨N₀, c0h, c0l, c0a, c0t⟩ := run_claimOps impl κ inp r 0 _ (r.size + 8) p4 (rsW impl κ fi r 0)
    L₀ [] hR hRv (hwE 1 (by decide) ez rfl)
  obtain ⟨N₁, c1h, c1l, c1a, c1t⟩ := run_claimOps impl κ inp r 1 _ (r.size + 8) p4 (rsW impl κ fi r 1)
    L₀ N₀ hR hRv (hwE 3 (by decide) (eqTab p1) rfl)
  obtain ⟨N₂, c2h, c2l, c2a, c2t⟩ := run_claimOps impl κ inp r 2 _ (r.size + 8) p4 (rsW impl κ fi r 2)
    L₀ (N₀ ++ N₁) hR hRv (hwE 5 (by decide) (eqTab p2) rfl)
  obtain ⟨N₃, c3h, c3l, c3a, c3t⟩ := run_claimOps impl κ inp r 3 _ (r.size + 8) p4 (rsW impl κ fi r 3)
    L₀ (N₀ ++ N₁ ++ N₂) hR hRv (hwE 7 (by decide) (eqTab p3) rfl)
  obtain ⟨N₄, c4h, c4l, c4a, c4t⟩ := run_claimOps impl κ inp r 4 (fun i => .const (fun _ => .f (bb i)))
    (r.size + 8) p4 (rsW impl κ fi r 4) L₀ (N₀ ++ N₁ ++ N₂ ++ N₃) hR hRv (fun _ _ => rfl)
  simp only [List.length_append, List.length_nil, hL0, c0l, c1l, c2l, c3l, Nat.add_zero] at c0h c1h c2h c3h c4h c0a c1a c2a c3a c4a c0t c1t c2t c3t c4t
  simp only [List.append_nil, List.append_assoc] at c0h c1h c2h c3h c4h c0a c1a c2a c3a c4a c0t c1t c2t c3t c4t
  rw [show 1 + 128 * elemW + (1 + 128 * elemW) = 2 * (1 + 128 * elemW) by ring] at c2h
  rw [show 1 + 128 * elemW + (1 + 128 * elemW) + (1 + 128 * elemW) = 3 * (1 + 128 * elemW) by ring] at c3h
  rw [show 1 + 128 * elemW + (1 + 128 * elemW) + (1 + 128 * elemW) + (1 + 128 * elemW) =
    4 * (1 + 128 * elemW) by ring] at c4h
  simp only [finRS, List.append_assoc]
  rw [es, pr_app' impl κ inp r c0h, pr_app' impl κ inp r c1h, pr_app' impl κ inp r c2h,
    pr_app' impl κ inp r c3h, pr_app' impl κ inp r c4h]
  set A := 1 + 128 * elemW with hAd
  set Lc := L₀ ++ (N₀ ++ (N₁ ++ (N₂ ++ (N₃ ++ N₄))))
  have hLc : Lc.length = 9 + 5 * A := by
    simp only [Lc, List.length_append, hL0, c0l, c1l, c2l, c3l, c4l]; ring
  have pre : ∀ (P Q : List Val) (t : ℕ), t < r.size + P.length →
      rd (r ++ (P ++ Q).toArray) t = rd (r ++ P.toArray) t := fun P Q t h => rdL r h
  have rT : ∀ (P Q : List Val) (t t' : ℕ) (v : F), Lc = P ++ Q → t' < r.size + P.length → t = t' →
      (rd (r ++ P.toArray) t').toF = v → (rd (r ++ Lc.toArray) t).toF = v := by
    intro P Q t t' v hPQ ht he hv; rw [hPQ, he, pre P Q t' ht, hv]
  obtain ⟨Mt, ht, hvt⟩ := run_rsTail impl κ inp r kap (r.size + 9 + A - 1)
    (r.size + 9 + 2 * A - 1) (r.size + 9 + 3 * A - 1) (r.size + 9 + 4 * A - 1)
    (r.size + Lc.length - 1) Lc (rsTv impl inp fi r 0) (rsTv impl inp fi r 1) (rsTv impl inp fi r 2)
    (rsTv impl inp fi r 3) (rsTv impl inp fi r 4) (fv r kap) hkap rfl
    (by rw [hLc]; omega) (by rw [hLc]; omega) (by rw [hLc]; omega) (by rw [hLc]; omega)
    (by rw [hLc]; omega)
    (rT (L₀ ++ N₀) (N₁ ++ (N₂ ++ (N₃ ++ N₄))) _ _ _ (by simp [Lc]) (by simp [hL0, c0l]; omega)
      (by omega) c0t)
    (rT (L₀ ++ (N₀ ++ N₁)) (N₂ ++ (N₃ ++ N₄)) _ _ _ (by simp [Lc]) (by simp [hL0, c0l, c1l]; omega)
      (by omega) c1t)
    (rT (L₀ ++ (N₀ ++ (N₁ ++ N₂))) (N₃ ++ N₄) _ _ _ (by simp [Lc])
      (by simp [hL0, c0l, c1l, c2l]; omega) (by omega) c2t)
    (rT (L₀ ++ (N₀ ++ (N₁ ++ (N₂ ++ N₃)))) N₄ _ _ _ (by simp [Lc])
      (by simp [hL0, c0l, c1l, c2l, c3l]; omega) (by omega) c3t)
    (rT Lc [] _ _ _ (by simp) (by simp [Lc, hL0, c0l, c1l, c2l, c3l, c4l]; omega) (by omega) c4t)
  rw [← hkapd, show r.size + 9 + 5 * A = r.size + Lc.length by rw [hLc]; omega, ht]
  refine ⟨Lc ++ Mt, rfl, fun j hj => ?_, ?_⟩
  · have rA : ∀ (P Q : List Val) (t t' : ℕ) (v : F), Lc = P ++ Q → t' < r.size + P.length → t = t' →
        (rd (r ++ P.toArray) t').toF = v → (rd (r ++ (Lc ++ Mt).toArray) t).toF = v := by
      intro P Q t t' v hPQ ht' he hv
      have hlt : t < r.size + Lc.length := by rw [he, hPQ, List.length_append]; omega
      rw [pre Lc Mt t hlt]; exact rT P Q t t' v hPQ ht' he hv
    interval_cases j <;> simp only [List.range_succ, List.range_zero, List.map_append, List.map_cons,
      List.map_nil, List.nil_append, List.cons_append, List.getD_cons_zero, List.getD_cons_succ]
    · exact rA (L₀ ++ N₀) (N₁ ++ (N₂ ++ (N₃ ++ N₄))) _ _ _ (by simp [Lc]) (by simp [hL0, c0l]; omega)
        (by omega) c0a
    · exact rA (L₀ ++ (N₀ ++ N₁)) (N₂ ++ (N₃ ++ N₄)) _ _ _ (by simp [Lc])
        (by simp [hL0, c0l, c1l]; omega) (by omega) c1a
    · exact rA (L₀ ++ (N₀ ++ (N₁ ++ N₂))) (N₃ ++ N₄) _ _ _ (by simp [Lc])
        (by simp [hL0, c0l, c1l, c2l]; omega) (by omega) c2a
    · exact rA (L₀ ++ (N₀ ++ (N₁ ++ (N₂ ++ N₃)))) N₄ _ _ _ (by simp [Lc])
        (by simp [hL0, c0l, c1l, c2l, c3l]; omega) (by omega) c3a
    · exact rA Lc [] _ _ _ (by simp) (by simp [Lc, hL0, c0l, c1l, c2l, c3l, c4l]; omega) (by omega) c4a
  · simp only [nRS, List.range_succ, List.range_zero, List.map_append, List.map_cons, List.map_nil,
      List.nil_append, List.cons_append, List.getD_cons_zero, List.getD_cons_succ]
    rw [hvt]; rfl

end RS

/-! ## `finE` and `finB′` (A.9) -/

/-- **`finE`** (A.9 revision 3.12; node only; the shape of `finLr`): `â_M, b̂_M, ĉ_M` from the
E-end absorb (A.3 row 9′); (ii) `c_{E2} = eq(r_E, r_{E2})·(â_M b̂_M + ĉ_M)` (`r_E` E1's 21
coordinates, `r_{E2}` E2's challenges); (iii) `c₀^{E4} = â_M + κ_E b̂_M + κ_E² ĉ_M`, binding the E
lincheck's free initial claim; (iv) `c_{E4} = (Ã + κ_E B̃ + κ_E² C̃)(r_{E2}, r′)·f̂(r′)` with
`evalM` at the F point `r′` (E4's 23 challenges) and `f̂(r′)` RS claim 5 (`zhat` 4). `c₀^{E2} = 0`
holds by `initClaim`. Exports the point `r′`. -/
def finE : FinField := fun fi b =>
  let kE := (outsOf fi "E3").headD 0
  ([.piElem fEEnd 0, .piElem fEEnd 16, .piElem fEEnd 32,
    .packF ((coordsR fi "E1").take 21), .packF (chals fi "E2" 21), .eqPt (b + 3) (b + 4),
    .mulF b (b + 1), .addF (b + 6) (b + 2), .mulF (b + 5) (b + 7),
    .assertEq (b + 8) (claimN fi "E2") Kind.isNode,
    .mulF kE (b + 1), .mulF kE kE, .mulF (b + 10) (b + 2), .addF b (b + 9), .addF (b + 12) (b + 11),
    .assertEq (b + 13) (claim0 fi "E4") Kind.isNode,
    .packF (chals fi "E4" 23), .evalM (b + 4) (b + 14), .mulF kE (b + 16), .mulF (b + 10) (b + 17),
    .addF (b + 15) (b + 18), .addF (b + 20) (b + 19), .mulF (b + 21) (fi.zhat.getD 4 0),
    .assertEq (b + 22) (claimN fi "E4") Kind.isNode],
   [b + 14])

/-- The F halves of a digest (`splitDigest`). -/
def dLo (x : Digest) : F := F.ofBytes (Vector.ofFn fun i : Fin 16 => x[i.1])
def dHi (x : Digest) : F := F.ofBytes (Vector.ofFn fun i : Fin 16 => x[16 + i.1])

/-- **`finB′`** (A.9, revisions 3.6, 3.12): `v* = v_RS + Σ_k κ′^(k+2) pub_k` equals P1.0's initial
claim (in `K`); E is batched into `v_RS` as RS claim 5, so `v*` has no `v_E` term (stage-review
changes 18). A node's public point claims, in order: M's `one` cell `1`; slot 0's `vk`, `c₁`; slot
1's `vk`, `c₂` (each digest as its two halves); the zero padding cells after them add nothing. A
leaf kind has none (`keep`). `v_RS` is `finRS`'s export `nRS`. Exports `v*`. -/
def finB' : FinField := fun fi b =>
  let kp := (outsOf fi "B'").headD 0
  let vRS := fi.zhat.getD nRS 0
  ([.input 0, .splitDigest b, .piDigest fStmt 1, .splitDigest (b + 3), .piDigest fStmt 33,
    .splitDigest (b + 6), .const (fun _ => .f 1),
    .mulF kp (b + 8), .addF (b + 7) (b + 10), .mulF kp (b + 11), .addF (b + 2) (b + 12),
    .mulF kp (b + 13), .addF (b + 1) (b + 14), .mulF kp (b + 15), .addF (b + 5) (b + 16),
    .mulF kp (b + 17), .addF (b + 4) (b + 18), .mulF kp (b + 19), .addF (b + 2) (b + 20),
    .mulF kp (b + 21), .addF (b + 1) (b + 22), .mulF kp (b + 23), .addF (b + 9) (b + 24),
    .mulF kp kp, .mulF (b + 26) (b + 25), .const (fun _ => .f 0), .keep Kind.isNode (b + 27) (b + 28),
    .addF vRS (b + 29),
    .const (fun _ => .k 1), .mulKF (b + 31) (b + 30), .assertEq (b + 32) (claim0 fi "P1") allK],
   [b + 30])

section EB
variable (impl : OpImpl) (κ : Kind) (inp : Input) (fi : FinIn) (r : Array Val)

/-- **A.9's `finE` relation** (node only, revision 3.12) over the register values. -/
def relE : Bool :=
  let rE := (((coordsR fi "E1").take 21).map (fv r)).toArray
  let r2 := ((chals fi "E2" 21).map (fv r)).toArray
  let r4 := ((chals fi "E4" 23).map (fv r)).toArray
  let kE := fv r ((outsOf fi "E3").headD 0)
  let a := pe inp fEEnd 0; let bb := pe inp fEEnd 16; let c := pe inp fEEnd 32
  let m := impl.evalM r2 r4
  if κ.isNode then
    (Val.f (eqPoint rE r2 * (a * bb + c))).eqv (rd r (claimN fi "E2")) &&
    ((Val.f (a + kE * bb + kE * kE * c)).eqv (rd r (claim0 fi "E4")) &&
    (Val.f ((m.1 + kE * m.2.1 + kE * kE * m.2.2) * fv r (fi.zhat.getD 4 0))).eqv
      (rd r (claimN fi "E4")))
  else true

/-- **`flag_finE`**: `finE` asks nothing, its flag is `relE`, its export the point `r′`. -/
theorem flag_finE (hin : ∀ x ∈ (coordsR fi "E1").take 21 ++ chals fi "E2" 21 ++ chals fi "E4" 23 ++
      [(outsOf fi "E3").headD 0, claimN fi "E2", claim0 fi "E4", claimN fi "E4",
       fi.zhat.getD 4 0], x < r.size) :
    ∃ L, pureRun impl κ inp (finE fi r.size).1 r [] = some (L, relE impl κ inp fi r) ∧
      (rd (r ++ L.toArray) ((finE fi r.size).2.getD 0 0)).toAF =
        ((chals fi "E4" 23).map (fv r)).toArray := by
  simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hin
  have h1 := fun L => map_rd_app r L ((coordsR fi "E1").take 21) fun x hx => hin x (.inl (.inl (.inl hx)))
  have h2 := fun L => map_rd_app r L (chals fi "E2" 21) fun x hx => hin x (.inl (.inl (.inr hx)))
  have h3 := fun L => map_rd_app r L (chals fi "E4" 23) fun x hx => hin x (.inl (.inr hx))
  have tf : ∀ x, (Val.f x).toF = x := fun _ => rfl
  have taf : ∀ x, (Val.af x).toAF = x := fun _ => rfl
  simp only [finE, relE]
  generalize (outsOf fi "E3").headD 0 = ke at *
  generalize claimN fi "E2" = c2 at *
  generalize claim0 fi "E4" = c40 at *
  generalize claimN fi "E4" = c4 at *
  generalize fi.zhat.getD 4 0 = ze at *
  have hk := hin ke (.inr (.inl rfl)); have hc2 := hin c2 (.inr (.inr (.inl rfl)))
  have hc40 := hin c40 (.inr (.inr (.inr (.inl rfl))))
  have hc4 := hin c4 (.inr (.inr (.inr (.inr (.inl rfl)))))
  have hze := hin ze (.inr (.inr (.inr (.inr (.inr rfl)))))
  cases hn : κ.isNode <;>
  simp only [hn, pureRun, evalOp, tf, taf, List.nil_append, List.cons_append, h1, h2, h3,
    rd_app, rd_app0, rd_app_left _ _ hk, rd_app_left _ _ hc2, rd_app_left _ _ hc40,
    rd_app_left _ _ hc4, rd_app_left _ _ hze,
    List.getD_cons_succ, List.getD_cons_zero,
    Option.map_some, Bool.not_true, Bool.not_false, Bool.false_or, Bool.true_or, Bool.true_and,
    Bool.and_true, ↓reduceIte, Bool.false_eq_true] <;>
  exact ⟨_, rfl, rfl⟩

/-- The public point claims' Horner sum `Σ_k κ′^k pub_k` (A.9 `finB′`, the order of `finB'`). -/
def pubH (kp : F) : F :=
  let vl := dLo inp.vk; let vh := dHi inp.vk
  let c₁ := bytesAt inp.π (absOff fStmt 1) 32; let c₂ := bytesAt inp.π (absOff fStmt 33) 32
  1 + kp * (vl + kp * (vh + kp * (dLo c₁ + kp * (dHi c₁ + kp * (vl + kp * (vh + kp * (dLo c₂ +
    kp * dHi c₂)))))))

/-- **`v*`** (A.9 `finB′`) from the register values of `κ′` and `v_RS`. -/
def vStar : F :=
  let kp := fv r ((outsOf fi "B'").headD 0)
  fv r (fi.zhat.getD nRS 0) + (if κ.isNode then kp * kp * pubH inp kp else 0)

/-- **A.9's `finB′` relation**: `v*` (in `K`) is P1.0's initial claim. -/
def relB : Bool := (Val.k (K.smulF (vStar κ inp fi r) 1)).eqv (rd r (claim0 fi "P1"))

/-- **`flag_finB'`**: `finB'` asks nothing; its flag is `relB`; its export is `v*`. -/
theorem flag_finB' (hin : ∀ x ∈ [(outsOf fi "B'").headD 0, fi.zhat.getD nRS 0, claim0 fi "P1"],
      x < r.size) :
    ∃ L, pureRun impl κ inp (finB' fi r.size).1 r [] = some (L, relB κ inp fi r) ∧
      (rd (r ++ L.toArray) ((finB' fi r.size).2.getD 0 0)).toF = vStar κ inp fi r := by
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hin
  have tf : ∀ x, (Val.f x).toF = x := fun _ => rfl
  have td : ∀ x, (Val.d x).toD = x := fun _ => rfl
  have tk : ∀ x, (Val.k x).toK = x := fun _ => rfl
  simp only [finB', relB, vStar, pubH, dLo, dHi]
  generalize (outsOf fi "B'").headD 0 = kp at *
  generalize fi.zhat.getD nRS 0 = vR at *
  generalize claim0 fi "P1" = c0 at *
  have hk := hin kp (.inl rfl); have hR := hin vR (.inr (.inl rfl))
  have hc := hin c0 (.inr (.inr rfl))
  cases hn : κ.isNode <;>
  simp only [hn, pureRun, evalOp, tf, td, tk, List.nil_append, List.cons_append,
    rd_app, rd_app0, rd_app_left _ _ hk, rd_app_left _ _ hR, rd_app_left _ _ hc,
    List.getD_cons_succ, List.getD_cons_zero, Option.map_some, allK, Bool.not_true, Bool.false_or,
    Bool.true_and, Bool.and_true, ↓reduceIte, Bool.false_eq_true, ite_true, ite_false] <;>
  exact ⟨_, rfl, rfl⟩

end EB

/-! ## They ask nothing; the finals with S-F's fields -/

theorem noAsk_elemsOps (j : ℕ) (wop : ℕ → Op) (hw : ∀ i, (wop i).item? = none) (R : ℕ) :
    ∀ n i aA aT b, (elemsOps j wop R n i aA aT b).filterMap Op.item? = []
  | 0, _, _, _, _ => rfl
  | n + 1, i, aA, aT, b => by
    simp only [elemsOps, elemOps, List.filterMap_append, List.filterMap_cons, hw i,
      noAsk_elemsOps j wop hw R n, List.filterMap_nil, List.append_nil]
    rfl

theorem noAsk_claimOps (j : ℕ) (wop : ℕ → Op) (hw : ∀ i, (wop i).item? = none) (R b : ℕ) :
    (claimOps j wop R b).filterMap Op.item? = [] := by
  simp only [claimOps, List.filterMap_cons, noAsk_elemsOps j wop hw]; rfl

theorem noAsk_rsTail (kap t₀ t₁ t₂ t₃ t₄ d : ℕ) :
    (rsTail kap t₀ t₁ t₂ t₃ t₄ d).filterMap Op.item? = [] := rfl

/-- **S-F's fields ask nothing** (`items_gen`'s hypothesis, for these fields). -/
theorem noAsk_finRS (fi : FinIn) (b : ℕ) : (finRS fi b).1.filterMap Op.item? = [] := by
  simp only [finRS, List.filterMap_append, noAsk_rsTail,
    noAsk_claimOps _ (fun i => Op.getF _ i) (fun _ => rfl),
    noAsk_claimOps _ (fun i => Op.const (fun _ => .f (bb i))) (fun _ => rfl), List.append_nil,
    List.nil_append]
  rfl

theorem noAsk_finE (fi : FinIn) (b : ℕ) : (finE fi b).1.filterMap Op.item? = [] := by
  simp [finE, Op.item?]

theorem noAsk_finB' (fi : FinIn) (b : ℕ) : (finB' fi b).1.filterMap Op.item? = [] := by
  simp [finB', Op.item?]

/-- **The finals with S-0's and S-F's fields**; S-G's `finP`, `finPf` as arguments. -/
def sfFinals (p : ℕ → FinField) (pf : FinField) : Finals := s0Finals finRS finE finB' p pf

end FR

