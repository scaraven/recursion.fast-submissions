-- New for `flock-recursive` (BLUEPRINT §7, A.9; stage S-F).
import FRVIRFinals
import FRSkip
import FRRingSwitch

/-!
# The phase-final checks owned by S-F: `finRS`, `finE`, `finB′` (A.9)

`FRVIRFinals` holds the typed `Finals`, S-0's four fields and `s0Finals`, which takes the other
owners' fields as arguments. This module gives S-F's three (a separate module so that S-G can work
on `FRVIRFinals` at the same time; RESULT deviation 1), each with its semantic lemma against A.9:

* **`finRS`** (ring switching, row RS1; `FRRingSwitch`): from RS0's `J_z = 5 × 128` partials
  `s_{j,i}` and RS1's stage coefficients `f₀ … f₆` and `κ`, the claim values
  `α_j = Σ_i c_{j,i} s_{j,i}` (the low weights of `rs_column`: the skip Lagrange weights at `λ` times
  `eq(r′₀, ·)` for Z, `quirky_claim_split`; `eq(·)` of the low 7 coordinates of the claim's point for
  Lc, Sh (two claims) and Lr, `ml_claim_split`) and the batched switched claim
  `v_RS = Σ_j κ^j T_j`, `T_j = Σ_i bitBasis i · Φ(s_{j,i})` (`rsT`, `Φ` = `Phi`). A leaf's fifth
  claim (Lr) is zero: its partials are asserted zero and `T₃` is left out (revision 3.8: `J_z = 4`,
  Z's quirky point claim first, one Sh claim). **`exec_finRS`**.
* **`finE`** (node): `c_{E2} = eq(r_E, r)·(â_M b̂_M + ĉ_M)` with `â_M ‖ b̂_M ‖ ĉ_M` the E-end absorb
  (revision 3.7); exports `v_E = â_M + κ_E b̂_M + κ_E² ĉ_M` and the point `r`. **`flag_finE`**.
* **`finB′`**: `v* = v_RS + κ′ v_E + Σ_k κ′^(k+2) pub_k` equals P1.0's initial claim (in `K`). The
  public point claims of a node, in order `k`: M's `one` cell (`1`, revision 3.6), then slot 0's
  `vk` and `c₁` and slot 1's `vk` and `c₂`, each digest as its two F halves (`splitDigest`); the
  zero padding cells come after them and add nothing to `v*`. **`flag_finB'`**.

Proof kit: `pureRun_append`, `pr_op`, `rd_pre`, `rd_new`; the blocks `sqOps`, `phiOps` (the staged
map), `elemsOps` (one claim's partials), `prodOps` (a Lagrange weight), each run by induction on
the generator, never on a concrete op list.
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

/-- `n` squarings from register `x`: register `b + k` holds `x^(2^(k+1))`. -/
def sqOps : ℕ → Reg → ℕ → List Op
  | 0, _, _ => []
  | n + 1, x, b => .mulF x x :: sqOps n b (b + 1)

/-- **The staged map `Φ`** on register `x` (stage registers `fs`, first exponent `2^s`), from
register `b`: per stage `2^s` squarings, `f · x^(2^(2^s))`, `x + …` (width `phiW`). -/
def phiOps : List Reg → ℕ → Reg → ℕ → List Op
  | [], _, _, _ => []
  | f :: fs, s, x, b =>
    sqOps (2 ^ s) x b ++ [.mulF f (b + 2 ^ s - 1), .addF x (b + 2 ^ s)] ++
      phiOps fs (s - 1) (b + 2 ^ s + 1) (b + 2 ^ s + 2)

/-- The width of `phiOps`. -/
def phiW : List Reg → ℕ → ℕ
  | [], _ => 0
  | _ :: fs, s => 2 ^ s + 2 + phiW fs (s - 1)

/-- The packing basis element of index `i` (`bitBasis`, A.7). -/
def bb (i : ℕ) : F := bitBasis ⟨i % 128, Nat.mod_lt _ (by decide)⟩

/-- Partial `i` of RS claim `j` (RS0's message: claim-major, 16 bytes each). -/
def rsOff (j i : ℕ) : ℕ := 16 * (128 * j + i)

/-- One slice value of claim `j` (width `eW`): `s`, its low weight `c` (`wop i`), `c·s` into the claim
value, `Φ(s)`, `bitBasis i · Φ(s)` into the switched claim. -/
def elemOps (j i : ℕ) (wop : ℕ → Op) (fs : List Reg) (aA aT b : ℕ) : List Op :=
  [.piElem fRS0 (rsOff j i), wop i, .mulF (b + 1) b, .addF aA (b + 2)] ++ phiOps fs 6 b (b + 4) ++
  [.const (fun _ => .f (bb i)), .mulF (b + 4 + phiW fs 6) (b + 3 + phiW fs 6),
   .addF aT (b + 5 + phiW fs 6)]

/-- The width of `elemOps`. -/
def eW (fs : List Reg) : ℕ := 7 + phiW fs 6

/-- Partials `i … i + n − 1` of claim `j`. -/
def elemsOps (j : ℕ) (wop : ℕ → Op) (fs : List Reg) : ℕ → ℕ → Reg → Reg → ℕ → List Op
  | 0, _, _, _, _ => []
  | n + 1, i, aA, aT, b =>
    elemOps j i wop fs aA aT b ++ elemsOps j wop fs n (i + 1) (b + 3) (b + eW fs - 1) (b + eW fs)

/-- The skip node `x_j` (`S` is the first 64 nodes). -/
def xS (j : ℕ) : F := skipNode ⟨j % 128, Nat.mod_lt _ (by decide)⟩

/-- The nodes other than `lo` (63 of them, in order). -/
def others (lo : ℕ) : List ℕ := (List.range 63).map fun j => if j < lo then j else j + 1

/-- The barycentric constant `(Π_{j ≠ lo} (x_lo + x_j))⁻¹`. -/
def wInv (lo : ℕ) : F := ((others lo).foldl (fun a j => a * (xS lo + xS j)) 1)⁻¹

/-- `acc · Π_{j ∈ js} (λ + x_j)` (width 3 per factor). -/
def prodOps (lam : Reg) : List ℕ → Reg → ℕ → List Op
  | [], _, _ => []
  | j :: js, acc, b =>
    [.const (fun _ => .f (xS j)), .addF lam b, .mulF acc (b + 1)] ++ prodOps lam js (b + 2) (b + 3)

/-- The skip Lagrange weight `L_lo(λ)` (width 190: the constant, then 63 factors). -/
def lagOne (lam lo b : ℕ) : List Op := .const (fun _ => .f (wInv lo)) :: prodOps lam (others lo) b (b + 1)

/-- `L_lo(λ)` for `lo = i … i + n − 1`, register `b + 190 (lo − i) + 189`. -/
def lagAll (lam : Reg) : ℕ → ℕ → ℕ → List Op
  | 0, _, _ => []
  | n + 1, i, b => lagOne lam i b ++ lagAll lam n (i + 1) (b + 190)

/-- `L_lo(λ)` as the ops compute it. -/
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

theorem toF_f (x : F) : (Val.f x).toF = x := rfl

/-- `sqOps` squares `n` times. -/
theorem run_sqOps (n : ℕ) : ∀ (x : ℕ) (a : F) (L : List Val), x < r.size + L.length →
    (rd (r ++ L.toArray) x).toF = a →
    ∃ M, pureRun impl κ inp (sqOps n x (r.size + L.length)) r L = some (L ++ M, true) ∧
      M.length = n ∧ (0 < n → (rd (r ++ (L ++ M).toArray) (r.size + L.length + n - 1)).toF = a ^ 2 ^ n) := by
  induction n with
  | zero => intro x a L _ _; exact ⟨[], by simp [sqOps, pureRun], rfl, by simp⟩
  | succ n ih =>
    intro x a L hx ha
    obtain ⟨M, hM, hl, hv⟩ := ih (r.size + L.length) (a * a) (L ++ [.f (a * a)]) (by simp)
      (by rw [rd_new1]; rfl)
    refine ⟨.f (a * a) :: M, ?_, by simp [hl], fun _ => ?_⟩
    · simp only [sqOps]
      rw [pr_op impl κ inp r (v := .f (a * a)) (by simp [evalOp, ha])]
      simpa [Nat.add_assoc] using hM
    · rcases Nat.eq_zero_or_pos n with rfl | hn
      · rw [List.length_eq_zero_iff] at hl; subst hl
        simp only [Nat.add_sub_cancel, List.append_nil]; rw [rd_new1, toF_f]; ring
      · have := hv hn
        simp only [List.length_append, List.length_singleton, List.append_assoc,
          List.singleton_append] at this
        rw [show r.size + L.length + (n + 1) - 1 = r.size + (L.length + 1) + n - 1 by omega, this]
        rw [← sq, ← pow_mul, ← pow_succ']

/-- **`phiOps` computes the staged map** (`frobMap` of `stages s`, FRRingSwitch). -/
theorem run_phiOps (fs : List ℕ) : ∀ (s : ℕ) (x : ℕ) (a : F) (L : List Val),
    x < r.size + L.length → (∀ f ∈ fs, f < r.size + L.length) → (rd (r ++ L.toArray) x).toF = a →
    ∃ M, pureRun impl κ inp (phiOps fs s x (r.size + L.length)) r L = some (L ++ M, true) ∧
      M.length = phiW fs s ∧ (fs ≠ [] → (rd (r ++ (L ++ M).toArray)
        (r.size + L.length + phiW fs s - 1)).toF =
          frobMap (stages s (fs.map fun f => (rd (r ++ L.toArray) f).toF)) a) := by
  induction fs with
  | nil => intro s x a L _ _ _; exact ⟨[], by simp [phiOps, pureRun], rfl, by simp⟩
  | cons f fs ih =>
    intro s x a L hx hf ha
    have hf0 := hf f (by simp)
    have hfs : ∀ f' ∈ fs, f' < r.size + L.length := fun f' h => hf f' (by simp [h])
    obtain ⟨M₁, h₁, hl₁, hv₁⟩ := run_sqOps impl κ inp r (2 ^ s) x a L hx ha
    have hv₁' := hv₁ (Nat.two_pow_pos s)
    rw [List.map_cons, stages_cons, frobMap]
    simp only [phiOps, phiW]
    have hN := Nat.two_pow_pos s
    generalize 2 ^ s = N at *
    set φ := (rd (r ++ L.toArray) f).toF
    set y := a ^ 2 ^ N
    set a' := a + φ * y
    have e1 : evalOp impl κ inp (r ++ (L ++ M₁).toArray) (.mulF f (r.size + L.length + N - 1)) =
        .vals [.f (φ * y)] true := by
      simp only [evalOp]; rw [rdL r hf0, hv₁']
    have e2 : evalOp impl κ inp (r ++ (L ++ M₁ ++ [Val.f (φ * y)]).toArray)
        (.addF x (r.size + L.length + N)) = .vals [.f a'] true := by
      have h2 := rdX r L (M₁ ++ [Val.f (φ * y)]) N
      rw [List.getD_append_right _ _ _ _ (by omega), hl₁, Nat.sub_self] at h2
      simp only [evalOp, List.append_assoc]; rw [rdL r hx, ha, h2]; rfl
    obtain ⟨L₂, hL₂'⟩ : ∃ L₂, L ++ M₁ ++ [Val.f (φ * y)] ++ [Val.f a'] = L₂ := ⟨_, rfl⟩
    have hL₂ : L₂ = L ++ (M₁ ++ [Val.f (φ * y), Val.f a']) := by rw [← hL₂']; simp
    have hs₂ : r.size + L₂.length = r.size + L.length + N + 2 := by rw [hL₂]; simp [hl₁]; omega
    have hx₂ : (rd (r ++ L₂.toArray) (r.size + L.length + N + 1)).toF = a' := by
      have h3 := rdX r L (M₁ ++ [Val.f (φ * y), Val.f a']) (N + 1)
      rw [List.getD_append_right _ _ _ _ (by omega), hl₁,
        show N + 1 - N = 1 by omega, ← Nat.add_assoc] at h3
      rw [hL₂, h3]; rfl
    obtain ⟨M₃, h₃, hl₃, hv₃⟩ := ih (s - 1) (r.size + L.length + N + 1) a' L₂ (by rw [hs₂]; omega)
      (fun f' h => by have := hfs f' h; rw [hs₂]; omega) hx₂
    rw [hs₂] at h₃ hv₃
    have hmap : fs.map (fun f => (rd (r ++ L₂.toArray) f).toF) =
        fs.map fun f => (rd (r ++ L.toArray) f).toF :=
      List.map_congr_left fun f' hf' => by rw [hL₂, rdL r (hfs f' hf')]
    rw [hmap] at hv₃
    refine ⟨M₁ ++ [Val.f (φ * y), Val.f a'] ++ M₃, ?_, by simp [hl₁, hl₃]; omega, fun _ => ?_⟩
    · rw [List.append_assoc, pr_app impl κ inp r h₁, List.cons_append, pr_op impl κ inp r e1,
        List.cons_append, pr_op impl κ inp r e2, List.nil_append]
      rw [hL₂', h₃, hL₂]; simp
    · by_cases hne : fs = []
      · subst hne
        simp only [phiW, Nat.add_zero, List.map_nil, stages, List.mapIdx_nil, frobMap] at hl₃ ⊢
        rw [List.length_eq_zero_iff] at hl₃; subst hl₃
        rw [List.append_nil, show r.size + L.length + (N + 2) - 1 = r.size + L.length + N + 1 by omega]
        rw [← hL₂]; exact hx₂
      · rw [show r.size + L.length + (N + 2 + phiW fs (s - 1)) - 1 =
          r.size + L.length + N + 2 + phiW fs (s - 1) - 1 by omega, ← hv₃ hne, hL₂]
        simp

theorem rdX0 (L X : List Val) : rd (r ++ (L ++ X).toArray) (r.size + L.length) = X.getD 0 default := by
  simpa using rdX r L X 0

/-- Partial `i` of claim `j`. -/
def sv (inp : Input) (j i : ℕ) : F := F.ofBytes (bytesAt inp.π (absOff fRS0 (rsOff j i)) 16)

theorem phiW_pos {fs : List ℕ} (h : fs ≠ []) (s : ℕ) : 0 < phiW fs s := by
  cases fs with
  | nil => exact absurd rfl h
  | cons _ _ => simp only [phiW]; positivity

/-- **One slice value**: the claim value gains `c · s`, the switched claim `bitBasis i · Φ(s)`. -/
theorem run_elemOps (j i aA aT : ℕ) (wop : ℕ → Op) (fs : List ℕ) (c A T : F) (L : List Val)
    (hfs : fs ≠ []) (hf : ∀ f ∈ fs, f < r.size + L.length) (hA : aA < r.size + L.length)
    (hT : aT < r.size + L.length) (hAv : (rd (r ++ L.toArray) aA).toF = A)
    (hTv : (rd (r ++ L.toArray) aT).toF = T)
    (hw : ∀ X : List Val, evalOp impl κ inp (r ++ (L ++ X).toArray) (wop i) = .vals [.f c] true) :
    ∃ M, pureRun impl κ inp (elemOps j i wop fs aA aT (r.size + L.length)) r L = some (L ++ M, true) ∧
      M.length = eW fs ∧
      (rd (r ++ (L ++ M).toArray) (r.size + L.length + 3)).toF = A + c * sv inp j i ∧
      (rd (r ++ (L ++ M).toArray) (r.size + L.length + eW fs - 1)).toF =
        T + bb i * frobMap (stages 6 (fs.map fun f => (rd (r ++ L.toArray) f).toF)) (sv inp j i) := by
  set s := sv inp j i
  have hP := phiW_pos hfs 6
  set B := r.size + L.length with hB
  obtain ⟨L₁, hL₁⟩ : ∃ L₁, L₁ = L ++ [Val.f s, .f c, .f (c * s), .f (A + c * s)] := ⟨_, rfl⟩
  have e0 : evalOp impl κ inp (r ++ L.toArray) (.piElem fRS0 (rsOff j i)) = .vals [.f s] true := rfl
  have e1 : evalOp impl κ inp (r ++ (L ++ [Val.f s]).toArray) (wop i) = .vals [.f c] true := hw _
  have e2 : evalOp impl κ inp (r ++ (L ++ [Val.f s] ++ [Val.f c]).toArray)
      (.mulF (B + 1) B) = .vals [.f (c * s)] true := by
    simp only [evalOp, List.append_assoc, List.singleton_append, List.cons_append, List.nil_append,
      hB, rdX, rdX0, List.getD_cons_succ, List.getD_cons_zero, toF_f]
  have e3 : evalOp impl κ inp (r ++ (L ++ [Val.f s] ++ [Val.f c] ++ [Val.f (c * s)]).toArray)
      (.addF aA (B + 2)) = .vals [.f (A + c * s)] true := by
    simp only [evalOp, List.append_assoc, List.singleton_append, List.cons_append, List.nil_append,
      hB, rdX, List.getD_cons_succ, List.getD_cons_zero, toF_f, rdL r hA, hAv]
  have hs₁ : r.size + L₁.length = B + 4 := by
    simp only [hL₁, List.length_append, List.length_cons, List.length_nil, hB]; omega
  obtain ⟨M₂, h₂, hl₂, hv₂⟩ := run_phiOps impl κ inp r fs 6 B s L₁
    (by rw [hs₁]; omega) (fun f h => by have := hf f h; rw [hs₁]; omega)
    (by rw [hL₁, hB, rdX0]; rfl)
  rw [hs₁] at h₂ hv₂
  have hmap : fs.map (fun f => (rd (r ++ L₁.toArray) f).toF) = fs.map fun f => (rd (r ++ L.toArray) f).toF :=
    List.map_congr_left fun f hf' => by rw [hL₁, rdL r (hf f hf')]
  rw [hmap] at hv₂
  have hv₂' := hv₂ hfs
  set φ := frobMap (stages 6 (fs.map fun f => (rd (r ++ L.toArray) f).toF)) s
  obtain ⟨L₂, hL₂⟩ : ∃ L₂, L₂ = L₁ ++ M₂ := ⟨_, rfl⟩
  have hs₂ : r.size + L₂.length = B + 4 + phiW fs 6 := by
    rw [hL₂, List.length_append, hl₂, ← Nat.add_assoc, hs₁]
  have e4 : evalOp impl κ inp (r ++ L₂.toArray) (.const (fun _ => .f (bb i))) = .vals [.f (bb i)] true :=
    rfl
  have e5 : evalOp impl κ inp (r ++ (L₂ ++ [Val.f (bb i)]).toArray)
      (.mulF (B + 4 + phiW fs 6) (B + 3 + phiW fs 6)) = .vals [.f (bb i * φ)] true := by
    simp only [evalOp]
    rw [← hs₂, rdX0, rdL r (by rw [hs₂]; omega), show B + 3 + phiW fs 6 = B + 4 + phiW fs 6 - 1 by omega,
      hL₂, hv₂']; rfl
  have e6 : evalOp impl κ inp (r ++ (L₂ ++ [Val.f (bb i)] ++ [Val.f (bb i * φ)]).toArray)
      (.addF aT (B + 5 + phiW fs 6)) = .vals [.f (T + bb i * φ)] true := by
    simp only [evalOp, List.append_assoc, List.singleton_append]
    rw [show B + 5 + phiW fs 6 = r.size + L₂.length + 1 by omega, rdX,
      rdL r (by omega : aT < r.size + L₂.length), hL₂, hL₁, List.append_assoc, rdL r hT, hTv]; rfl
  have hlen₂ : ([Val.f s, .f c, .f (c * s), .f (A + c * s)] ++ M₂).length = 4 + phiW fs 6 := by
    simp [hl₂]; omega
  refine ⟨[Val.f s, .f c, .f (c * s), .f (A + c * s)] ++ M₂ ++ [.f (bb i), .f (bb i * φ),
    .f (T + bb i * φ)], ?_, by simp [eW, hl₂]; omega, ?_, ?_⟩
  · simp only [elemOps, List.cons_append, List.nil_append, List.append_assoc]
    rw [pr_op impl κ inp r e0, pr_op impl κ inp r e1, pr_op impl κ inp r e2, pr_op impl κ inp r e3]
    rw [show L ++ [Val.f s] ++ [Val.f c] ++ [Val.f (c * s)] ++ [Val.f (A + c * s)] = L₁ by simp [hL₁],
      pr_app impl κ inp r h₂, ← hL₂]
    rw [pr_op impl κ inp r e4, pr_op impl κ inp r e5, pr_op impl κ inp r e6]
    simp [pureRun, hL₂, hL₁]
  · rw [hB, rdX]; simp [toF_f]
  · rw [show B + eW fs - 1 = r.size + L.length + (4 + phiW fs 6 + 2) by simp only [eW]; omega, rdX,
      List.getD_append_right _ _ _ _ (by omega), hlen₂]
    simp [toF_f]

/-- **A claim's partials, `n` of them**: the claim value and the switched claim as sums. -/
theorem run_elemsOps (j : ℕ) (wop : ℕ → Op) (fs : List ℕ) (c : ℕ → F) (L₀ : List Val)
    (hfs : fs ≠ []) (hf : ∀ f ∈ fs, f < r.size + L₀.length)
    (hw : ∀ i (X : List Val), evalOp impl κ inp (r ++ (L₀ ++ X).toArray) (wop i) = .vals [.f (c i)] true)
    (n : ℕ) : ∀ (i aA aT : ℕ) (A T : F) (X : List Val), aA < r.size + L₀.length + X.length →
    aT < r.size + L₀.length + X.length → (rd (r ++ (L₀ ++ X).toArray) aA).toF = A →
    (rd (r ++ (L₀ ++ X).toArray) aT).toF = T →
    ∃ M, pureRun impl κ inp (elemsOps j wop fs n i aA aT (r.size + L₀.length + X.length)) r (L₀ ++ X) =
      some (L₀ ++ X ++ M, true) ∧ M.length = n * eW fs ∧
      (0 < n → (rd (r ++ (L₀ ++ X ++ M).toArray) (r.size + L₀.length + X.length + (n - 1) * eW fs + 3)).toF =
          A + ∑ k ∈ Finset.range n, c (i + k) * sv inp j (i + k) ∧
        (rd (r ++ (L₀ ++ X ++ M).toArray) (r.size + L₀.length + X.length + n * eW fs - 1)).toF =
          T + ∑ k ∈ Finset.range n, bb (i + k) *
            frobMap (stages 6 (fs.map fun f => (rd (r ++ L₀.toArray) f).toF)) (sv inp j (i + k))) := by
  induction n with
  | zero => intro i aA aT A T X _ _ _ _; exact ⟨[], by simp [elemsOps, pureRun], by simp, by simp⟩
  | succ n ih =>
    intro i aA aT A T X hA hT hAv hTv
    have hlen : r.size + (L₀ ++ X).length = r.size + L₀.length + X.length := by simp; omega
    obtain ⟨M₁, h₁, hl₁, hα, hτ⟩ := run_elemOps impl κ inp r j i aA aT wop fs (c i) A T (L₀ ++ X) hfs
      (fun f h => by have := hf f h; rw [hlen]; omega) (by rw [hlen]; exact hA) (by rw [hlen]; exact hT)
      hAv hTv (fun Y => by rw [List.append_assoc]; exact hw i _)
    rw [hlen] at h₁ hα hτ
    have hmap : fs.map (fun f => (rd (r ++ (L₀ ++ X).toArray) f).toF) =
        fs.map fun f => (rd (r ++ L₀.toArray) f).toF :=
      List.map_congr_left fun f hf' => rdL r (hf f hf') ▸ rfl
    rw [hmap] at hτ
    have hE : 7 ≤ eW fs := by simp [eW]
    obtain ⟨M₂, h₂, hl₂, hv₂⟩ := ih (i + 1) (r.size + L₀.length + X.length + 3)
      (r.size + L₀.length + X.length + eW fs - 1) (A + c i * sv inp j i)
      (T + bb i * frobMap (stages 6 (fs.map fun f => (rd (r ++ L₀.toArray) f).toF)) (sv inp j i)) (X ++ M₁)
      (by simp only [List.length_append, hl₁]; omega) (by simp only [List.length_append, hl₁]; omega)
      (by simpa only [List.append_assoc] using hα) (by simpa only [List.append_assoc] using hτ)
    have hb : r.size + L₀.length + (X ++ M₁).length = r.size + L₀.length + X.length + eW fs := by
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
        have hm : n * eW fs = eW fs + (n - 1) * eW fs := by
          obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
          simp only [Nat.add_sub_cancel, Nat.add_mul, Nat.one_mul]; ring
        have hk : ∀ k, i + 1 + k = i + (k + 1) := fun k => by omega
        simp only [List.append_assoc] at h3 h4 ⊢
        refine ⟨?_, ?_⟩
        · rw [show r.size + L₀.length + X.length + (n + 1 - 1) * eW fs + 3 =
            r.size + L₀.length + X.length + eW fs + (n - 1) * eW fs + 3 by
              rw [Nat.add_sub_cancel]; omega, h3, Finset.sum_range_succ']
          simp only [hk, Nat.add_zero]; ring
        · rw [show r.size + L₀.length + X.length + (n + 1) * eW fs - 1 =
            r.size + L₀.length + X.length + eW fs + n * eW fs - 1 by
              rw [Nat.add_mul, Nat.one_mul]; omega, h4, Finset.sum_range_succ']
          simp only [hk, Nat.add_zero]; ring

/-- `prodOps` multiplies by `λ + x_j` for each `j`. -/
theorem run_prodOps (lam : ℕ) (l : F) (js : List ℕ) : ∀ (acc : ℕ) (A : F) (L : List Val),
    lam < r.size + L.length → acc < r.size + L.length → (rd (r ++ L.toArray) lam).toF = l →
    (rd (r ++ L.toArray) acc).toF = A →
    ∃ M, pureRun impl κ inp (prodOps lam js acc (r.size + L.length)) r L = some (L ++ M, true) ∧
      M.length = 3 * js.length ∧ (js ≠ [] → (rd (r ++ (L ++ M).toArray)
        (r.size + L.length + 3 * js.length - 1)).toF = js.foldl (fun a j => a * (l + xS j)) A) := by
  induction js with
  | nil => intro acc A L _ _ _ _; exact ⟨[], by simp [prodOps, pureRun], by simp, by simp⟩
  | cons j js ih =>
    intro acc A L hl ha hlv hav
    set x := xS j
    have e0 : evalOp impl κ inp (r ++ L.toArray) (.const (fun _ => .f x)) = .vals [.f x] true := rfl
    have e1 : evalOp impl κ inp (r ++ (L ++ [Val.f x]).toArray) (.addF lam (r.size + L.length)) =
        .vals [.f (l + x)] true := by
      simp only [evalOp]; rw [rdL r hl, hlv, rd_new1]; rfl
    have e2 : evalOp impl κ inp (r ++ (L ++ [Val.f x] ++ [Val.f (l + x)]).toArray)
        (.mulF acc (r.size + L.length + 1)) = .vals [.f (A * (l + x))] true := by
      simp only [evalOp, List.append_assoc, List.singleton_append, List.cons_append, List.nil_append]
      rw [rdL r ha, hav, rdX]; rfl
    obtain ⟨M, hM, hlM, hvM⟩ := ih (r.size + L.length + 2) (A * (l + x))
      (L ++ [Val.f x, .f (l + x), .f (A * (l + x))])
      (by simp only [List.length_append, List.length_cons, List.length_nil]; omega)
      (by simp only [List.length_append, List.length_cons, List.length_nil]; omega)
      (by rw [rdL r hl]; exact hlv) (by rw [rdX]; rfl)
    have hb : r.size + (L ++ [Val.f x, .f (l + x), .f (A * (l + x))]).length = r.size + L.length + 3 := by
      simp; omega
    rw [hb] at hM hvM
    refine ⟨[Val.f x, .f (l + x), .f (A * (l + x))] ++ M, ?_, by simp [hlM]; ring, fun _ => ?_⟩
    · simp only [prodOps, List.cons_append, List.nil_append]
      rw [pr_op impl κ inp r e0, pr_op impl κ inp r e1, pr_op impl κ inp r e2]
      simp only [List.append_assoc, List.cons_append, List.nil_append] at hM ⊢; exact hM
    · by_cases hne : js = []
      · subst hne
        simp only [List.length_nil, Nat.mul_zero, List.length_eq_zero_iff] at hlM; subst hlM
        simp only [List.foldl_cons, List.foldl_nil, List.append_nil, List.length_singleton]
        rw [show r.size + L.length + 3 * 1 - 1 = r.size + L.length + 2 by omega, rdX]; rfl
      · rw [List.foldl_cons, ← hvM hne]; simp only [List.append_assoc, List.cons_append,
          List.nil_append, List.length_cons]
        congr 2; omega

/-- **The 64 skip Lagrange weights**: register `b + 190 k + 189` holds `L_{i+k}(λ)`. -/
theorem run_lagAll (lam : ℕ) (l : F) (n : ℕ) : ∀ (i : ℕ) (L : List Val), lam < r.size + L.length →
    (rd (r ++ L.toArray) lam).toF = l →
    ∃ M, pureRun impl κ inp (lagAll lam n i (r.size + L.length)) r L = some (L ++ M, true) ∧
      M.length = 190 * n ∧ ∀ k < n, (rd (r ++ (L ++ M).toArray)
        (r.size + L.length + 190 * k + 189)).toF = lagV l (i + k) := by
  induction n with
  | zero => intro i L _ _; exact ⟨[], by simp [lagAll, pureRun], by simp, by simp⟩
  | succ n ih =>
    intro i L hl hlv
    have e0 : evalOp impl κ inp (r ++ L.toArray) (.const (fun _ => .f (wInv i))) =
      .vals [.f (wInv i)] true := rfl
    obtain ⟨M₁, h₁, hl₁, hv₁⟩ := run_prodOps impl κ inp r lam l (others i) (r.size + L.length) (wInv i)
      (L ++ [Val.f (wInv i)]) (by simp; omega) (by simp) (by rw [rdL r hl]; exact hlv)
      (by rw [rd_new1]; rfl)
    rw [others_length] at hl₁ hv₁
    have hv₁' := hv₁ (by rw [← List.length_pos_iff, others_length]; omega)
    have hb : r.size + (L ++ [Val.f (wInv i)]).length = r.size + L.length + 1 := by simp; omega
    rw [hb] at h₁ hv₁'
    obtain ⟨M₂, h₂, hl₂, hv₂⟩ := ih (i + 1) (L ++ ([Val.f (wInv i)] ++ M₁)) (by simp; omega)
      (by rw [rdL r hl]; exact hlv)
    have hb₂ : r.size + (L ++ ([Val.f (wInv i)] ++ M₁)).length = r.size + L.length + 190 := by
      simp [hl₁]; omega
    rw [hb₂] at h₂ hv₂
    refine ⟨[Val.f (wInv i)] ++ M₁ ++ M₂, ?_, by simp [hl₁, hl₂]; ring, fun k hk => ?_⟩
    · simp only [lagAll, lagOne, List.cons_append]
      rw [pr_op impl κ inp r e0, pr_app impl κ inp r h₁]
      simp only [List.append_assoc] at h₂ ⊢; rw [h₂]; simp
    · rcases k with _ | k
      · simp only [Nat.mul_zero, Nat.add_zero]
        rw [show L ++ ([Val.f (wInv i)] ++ M₁ ++ M₂) = L ++ [Val.f (wInv i)] ++ M₁ ++ M₂ by simp,
          rdL r (by simp only [List.length_append, List.length_singleton, hl₁]; omega),
          show r.size + L.length + 189 = r.size + L.length + 1 + 3 * 63 - 1 by omega, hv₁']; rfl
      · have := hv₂ k (by omega)
        simp only [List.append_assoc] at this ⊢
        rw [show r.size + L.length + 190 * (k + 1) + 189 = r.size + L.length + 190 + 190 * k + 189 by ring,
          this, show i + 1 + k = i + (k + 1) by omega]

/-- One claim: a zero, then its 128 partials (width `1 + 128 · eW`). -/
def claimOps (j : ℕ) (wop : ℕ → Op) (fs : List Reg) (b : ℕ) : List Op :=
  .const (fun _ => .f 0) :: elemsOps j wop fs 128 0 b b (b + 1)

theorem run_claimOps (j : ℕ) (wop : ℕ → Op) (fs : List ℕ) (c : ℕ → F) (L₀ X : List Val)
    (hfs : fs ≠ []) (hf : ∀ f ∈ fs, f < r.size + L₀.length)
    (hw : ∀ i (X : List Val), evalOp impl κ inp (r ++ (L₀ ++ X).toArray) (wop i) = .vals [.f (c i)] true) :
    ∃ M, pureRun impl κ inp (claimOps j wop fs (r.size + L₀.length + X.length)) r (L₀ ++ X) =
      some (L₀ ++ X ++ M, true) ∧ M.length = 1 + 128 * eW fs ∧
      (rd (r ++ (L₀ ++ X ++ M).toArray) (r.size + L₀.length + X.length + 127 * eW fs + 4)).toF =
        ∑ k ∈ Finset.range 128, c k * sv inp j k ∧
      (rd (r ++ (L₀ ++ X ++ M).toArray) (r.size + L₀.length + X.length + 128 * eW fs)).toF =
        ∑ k ∈ Finset.range 128, bb k *
          frobMap (stages 6 (fs.map fun f => (rd (r ++ L₀.toArray) f).toF)) (sv inp j k) := by
  set B := r.size + L₀.length + X.length
  have e0 : evalOp impl κ inp (r ++ (L₀ ++ X).toArray) (.const (fun _ => .f 0)) = .vals [.f 0] true := rfl
  have hz : (rd (r ++ (L₀ ++ (X ++ [Val.f 0])).toArray) B).toF = 0 := by
    rw [← List.append_assoc, show B = r.size + (L₀ ++ X).length by simp [B]; omega, rd_new1]; rfl
  obtain ⟨M, hM, hl, hv⟩ := run_elemsOps impl κ inp r j wop fs c L₀ hfs hf hw 128 0 B B 0 0
    (X ++ [Val.f 0]) (by simp [B]) (by simp [B]) hz hz
  have hb : r.size + L₀.length + (X ++ [Val.f 0]).length = B + 1 := by simp [B]; omega
  rw [hb] at hM hv
  obtain ⟨h1, h2⟩ := hv (by decide)
  refine ⟨[Val.f 0] ++ M, ?_, by simp [hl]; omega, ?_, ?_⟩
  · simp only [claimOps]; rw [pr_op impl κ inp r e0]
    simp only [List.append_assoc] at hM ⊢; exact hM
  · simp only [List.append_assoc, zero_add] at h1 ⊢
    rw [show B + 127 * eW fs + 4 = B + 1 + (128 - 1) * eW fs + 3 by omega, h1]
  · simp only [List.append_assoc, zero_add] at h2 ⊢
    rw [show B + 128 * eW fs = B + 1 + 128 * eW fs - 1 by omega, h2]

end Run

/-! ## `finRS` (A.9, row RS1) -/

/-- `v_RS` by Horner in `κ` from the switched claims `T₀ … T₃` (registers `t₀ … t₃`; a leaf's
`T₃` replaced by `0`), from register `d`; then a leaf's zero check of claim 3's partials. -/
def rsTail (kap t₀ t₁ t₂ t₃ d : ℕ) : List Op :=
  [.const (fun _ => .f 0), .keep Kind.isNode t₃ d, .mulF kap (d + 1), .addF t₂ (d + 2),
   .mulF kap (d + 3), .addF t₁ (d + 4), .mulF kap (d + 5), .addF t₀ (d + 6),
   .piField fRS0 (rsOff 3 0) 2048, .assertZero (d + 8) (fun κ => !κ.isNode)]

/-- The register of the Z claim's coordinate that `eq(r₀, ·)` reads: bit 6 of the packed element
index (revision 3.8: the Z claim is at Z1's point `r` and `λ`; **open**: S-0 to confirm which
coordinate of `r` this is under A.1's pinned layout). -/
def zLow (fi : FinIn) : Reg := (coordsR fi "Z1").headD 0

/-- **`finRS`** (revision 3.8, `J_z = 4`): the claim values `α_Z, α_Lc, α_Sh, α_Lr` and `v_RS`
(exports, in this order). Registers: the 64 skip Lagrange weights from `b`; at
`b₁ = b + 12,160` the constant `1`, `1 + r₀`, and the three `eq` tables (Lc, Sh, Lr); the claims
from `b₁ + 8`, `1 + 128 · eW` each; then `rsTail`. -/
def finRS : FinField := fun fi b =>
  let fs := (List.range 7).map fun p => (coordsR fi "RS1").getD p 0
  let kap := (coordsR fi "RS1").getD 7 0
  let lam := (outsOf fi "Z2").headD 0
  let r0 := zLow fi
  let b₁ := b + 190 * 64
  let c₀ := b₁ + 8
  let cw := 1 + 128 * eW fs
  let d := c₀ + 4 * cw
  let zw : ℕ → Op := fun i => .mulF (b + 190 * (i % 64) + 189) (if i < 64 then b₁ + 1 else r0)
  (lagAll lam 64 0 b ++
   [.const (fun _ => .f 1), .addF b₁ r0,
    .packF ((chals fi "L2" 14).take 7), .eqTable (b₁ + 2),
    .packFK (fun κ => ((chals fi "S2" 28).drop (κ.m - 14)).take 7), .eqTable (b₁ + 4),
    .packF ((chals fi "Lr4" 15).take 7), .eqTable (b₁ + 6)] ++
   claimOps 0 zw fs c₀ ++ claimOps 1 (fun i => .getF (b₁ + 3) i) fs (c₀ + cw) ++
   claimOps 2 (fun i => .getF (b₁ + 5) i) fs (c₀ + 2 * cw) ++
   claimOps 3 (fun i => .getF (b₁ + 7) i) fs (c₀ + 3 * cw) ++
   rsTail kap (c₀ + cw - 1) (c₀ + 2 * cw - 1) (c₀ + 3 * cw - 1) (c₀ + 4 * cw - 1) d,
   (List.range 4).map (fun j => c₀ + j * cw + 127 * eW fs + 4) ++ [d + 7])

/-- `finRS`'s export index of `v_RS` (after the `J_z = 4` claim values). -/
def nRS : ℕ := 4

theorem run_rsTail (impl : OpImpl) (κ : Kind) (inp : Input) (r : Array Val) (kap t₀ t₁ t₂ t₃ : ℕ)
    (Lc : List Val) (T₀ T₁ T₂ T₃ kp : F) (hk : kap < r.size) (hkv : (rd r kap).toF = kp)
    (h₀ : t₀ < r.size + Lc.length) (h₁ : t₁ < r.size + Lc.length) (h₂ : t₂ < r.size + Lc.length)
    (h₃ : t₃ < r.size + Lc.length)
    (v₀ : (rd (r ++ Lc.toArray) t₀).toF = T₀) (v₁ : (rd (r ++ Lc.toArray) t₁).toF = T₁)
    (v₂ : (rd (r ++ Lc.toArray) t₂).toF = T₂) (v₃ : (rd (r ++ Lc.toArray) t₃).toF = T₃) :
    ∃ M, pureRun impl κ inp (rsTail kap t₀ t₁ t₂ t₃ (r.size + Lc.length)) r Lc =
        some (Lc ++ M, κ.isNode || (inp.π.extract (absOff fRS0 (rsOff 3 0))
          (absOff fRS0 (rsOff 3 0) + 2048)).data.all (· == 0)) ∧
      (rd (r ++ (Lc ++ M).toArray) (r.size + Lc.length + 7)).toF =
        T₀ + kp * (T₁ + kp * (T₂ + kp * (if κ.isNode then T₃ else 0))) := by
  have hkr : ∀ X : List Val, (rd (r ++ X.toArray) kap).toF = kp := fun X => by rw [rd_app_left r X hk, hkv]
  have rL : ∀ {t T} (X : List Val), t < r.size + Lc.length → (rd (r ++ Lc.toArray) t).toF = T →
      (rd (r ++ (Lc ++ X).toArray) t).toF = T := fun X h v => by rw [rdL r h, v]
  set v₃' := if κ.isNode = true then rd (r ++ (Lc ++ [Val.f 0]).toArray) t₃ else Val.f 0
  have hv₃' : v₃'.toF = if κ.isNode then T₃ else 0 := by
    simp only [v₃']; split <;> [exact rL _ h₃ v₃; rfl]
  set y := (if κ.isNode then T₃ else 0)
  have hv3e : (if κ.isNode = true then rd (r ++ (Lc ++ [Val.f 0]).toArray) t₃ else Val.f 0).toF = y :=
    hv₃'
  set by₁ := inp.π.extract (absOff fRS0 (rsOff 3 0)) (absOff fRS0 (rsOff 3 0) + 2048)
  refine ⟨[.f 0, v₃', .f (kp * y), .f (T₂ + kp * y), .f (kp * (T₂ + kp * y)),
    .f (T₁ + kp * (T₂ + kp * y)), .f (kp * (T₁ + kp * (T₂ + kp * y))),
    .f (T₀ + kp * (T₁ + kp * (T₂ + kp * y))), .b by₁], ?_, ?_⟩
  · simp only [rsTail, pureRun, evalOp, List.append_assoc, List.cons_append, List.nil_append,
      rdX, rdX0, List.getD_cons_succ, List.getD_cons_zero, hkr, toF_f,
      rL _ h₀ v₀, rL _ h₁ v₁, rL _ h₂ v₂, hv3e, Bool.not_not, Val.isZero,
      Option.map_some, Bool.true_and, Bool.and_true]
    rfl
  · rw [rdX]; rfl

section RS
variable (impl : OpImpl) (κ : Kind) (inp : Input) (fi : FinIn) (r : Array Val)

/-- The F values of registers, as an array. -/
def ptF (xs : List Reg) : Array F := (xs.map (fv r)).toArray

/-- RS1's stage coefficients `f₀ … f₆`. -/
def rsFs : List F := (List.range 7).map fun p => fv r ((coordsR fi "RS1").getD p 0)

/-- **The low weights** `c_{j,i}` of the five claims (`rs_column`): Z's skip Lagrange weight at `λ`
times `eq(r′₀, ·)`; `eq` at the low 7 coordinates of Lc's (L2), Sh's (S2's position part, twice)
and Lr's (Lr4) points. -/
def rsW (j i : ℕ) : F :=
  match j with
  | 0 => lagV (fv r ((outsOf fi "Z2").headD 0)) (i % 64) *
      (if i < 64 then 1 + fv r (zLow fi) else fv r (zLow fi))
  | 1 => (eqTab (ptF r ((chals fi "L2" 14).take 7))).getD i 0
  | 2 => (eqTab (ptF r (((chals fi "S2" 28).drop (κ.m - 14)).take 7))).getD i 0
  | _ => (eqTab (ptF r ((chals fi "Lr4" 15).take 7))).getD i 0

/-- **Claim `j`'s value** `α_j = Σ_i c_{j,i} s_{j,i}`. -/
def rsAlpha (j : ℕ) : F := ∑ k ∈ Finset.range 128, rsW κ fi r j k * sv inp j k

/-- **Claim `j`'s switched claim** `T_j = Σ_i bitBasis i · Φ(s_{j,i})` (`rsT`). -/
def rsTv (j : ℕ) : F := ∑ k ∈ Finset.range 128, bb k * frobMap (stages 6 (rsFs fi r)) (sv inp j k)

/-- **`v_RS = Σ_j κ^j T_j`** (Horner; a leaf's `T₃` is `0`). -/
def rsV : F :=
  let kp := fv r ((coordsR fi "RS1").getD 7 0)
  rsTv inp fi r 0 + kp * (rsTv inp fi r 1 + kp * (rsTv inp fi r 2 +
    kp * (if κ.isNode then rsTv inp fi r 3 else 0)))

/-- `finRS`'s flag: a leaf's fifth claim has zero partials. -/
def relRS : Bool :=
  κ.isNode || (inp.π.extract (absOff fRS0 (rsOff 3 0)) (absOff fRS0 (rsOff 3 0) + 2048)).data.all (· == 0)

/-- The registers `finRS` reads. -/
def rsRefs : List Reg :=
  (List.range 8).map (fun p => (coordsR fi "RS1").getD p 0) ++
    [(outsOf fi "Z2").headD 0, zLow fi] ++ (chals fi "L2" 14).take 7 ++
    ((chals fi "S2" 28).drop (κ.m - 14)).take 7 ++ (chals fi "Lr4" 15).take 7

theorem phiW_seven (fs : List ℕ) (h : fs.length = 7) : phiW fs 6 = 141 := by
  match fs, h with
  | [_, _, _, _, _, _, _], _ => rfl

/-- **`exec_finRS`** (A.9, RS): `finRS` asks nothing; its flag is `relRS` (a leaf's fifth claim is
zero), its exports are the claim values `α₀ … α₄` (`rsAlpha`) and `v_RS` (`rsV`). -/
theorem exec_finRS (hin : ∀ x ∈ rsRefs κ fi, x < r.size) :
    ∃ L, pureRun impl κ inp (finRS fi r.size).1 r [] = some (L, relRS κ inp) ∧
      (∀ j < 4, (rd (r ++ L.toArray) ((finRS fi r.size).2.getD j 0)).toF = rsAlpha κ inp fi r j) ∧
      (rd (r ++ L.toArray) ((finRS fi r.size).2.getD nRS 0)).toF = rsV κ inp fi r := by
  simp only [rsRefs, List.mem_append, List.mem_map, List.mem_range, List.mem_cons,
    List.not_mem_nil, or_false] at hin
  set fs := (List.range 7).map fun p => (coordsR fi "RS1").getD p 0 with hfsd
  have hfs : fs ≠ [] := by simp [fs]
  have hfin : ∀ f ∈ fs, f < r.size := fun f hf => by
    simp only [fs, List.mem_map, List.mem_range] at hf
    obtain ⟨p, hp, rfl⟩ := hf; exact hin _ (.inl (.inl (.inl (.inl ⟨p, by omega, rfl⟩))))
  have hE : eW fs = 148 := by simp only [eW, phiW_seven fs (by simp [fs])]
  set kap := (coordsR fi "RS1").getD 7 0 with hkapd
  set lam := (outsOf fi "Z2").headD 0 with hlamd
  set r0 := zLow fi with hr0d
  have hkap : kap < r.size := hin _ (.inl (.inl (.inl (.inl ⟨7, by omega, rfl⟩))))
  have hlam : lam < r.size := hin _ (.inl (.inl (.inl (.inr (.inl rfl)))))
  have hr0 : r0 < r.size := hin _ (.inl (.inl (.inl (.inr (.inr rfl)))))
  set x1 := (chals fi "L2" 14).take 7
  set x2 := ((chals fi "S2" 28).drop (κ.m - 14)).take 7
  set x3 := (chals fi "Lr4" 15).take 7
  have hx1 : ∀ x ∈ x1, x < r.size := fun x h => hin x (.inl (.inl (.inr h)))
  have hx2 : ∀ x ∈ x2, x < r.size := fun x h => hin x (.inl (.inr h))
  have hx3 : ∀ x ∈ x3, x < r.size := fun x h => hin x (.inr h)
  -- the Lagrange weights
  obtain ⟨M₁, h₁, hl₁, hv₁⟩ := run_lagAll impl κ inp r lam (fv r lam) 64 0 [] (by simpa using hlam)
    (by simp [fv])
  simp only [List.length_nil, Nat.add_zero, List.nil_append, Nat.zero_add] at h₁ hv₁
  -- the setup
  set p1 := ptF r x1; set p2 := ptF r x2; set p3 := ptF r x3
  set Ls : List Val := [.f 1, .f (1 + fv r r0), .af p1, .af (eqTab p1), .af p2, .af (eqTab p2),
    .af p3, .af (eqTab p3)] with hLs
  set L₀ := M₁ ++ Ls with hL₀
  have hrdL₀ : ∀ t < 8, ∀ X : List Val, rd (r ++ (L₀ ++ X).toArray) (r.size + 190 * 64 + t) = Ls.getD t default :=
    fun t ht X => by
      rw [hL₀, List.append_assoc, ← hl₁, rdX, List.getD_append _ _ _ _ (by simp [hLs]; omega)]
  have hrdr : ∀ x < r.size, ∀ X : List Val, rd (r ++ X.toArray) x = rd r x := fun x h X => rd_app_left r X h
  have hpk : ∀ (xs : List Reg), (∀ x ∈ xs, x < r.size) → ∀ X : List Val,
      (xs.map fun x => (rd (r ++ X.toArray) x).toF).toArray = ptF r xs := fun xs h X => by
    rw [ptF, map_rd_app r X xs h]
  have es : ∀ ops, pureRun impl κ inp ([.const (fun _ => .f 1), .addF (r.size + 190 * 64) r0,
      .packF x1, .eqTable (r.size + 190 * 64 + 2),
      .packFK (fun κ => ((chals fi "S2" 28).drop (κ.m - 14)).take 7), .eqTable (r.size + 190 * 64 + 4),
      .packF x3, .eqTable (r.size + 190 * 64 + 6)] ++ ops) r M₁ = pureRun impl κ inp ops r L₀ := by
    intro ops
    have hb : r.size + 190 * 64 = r.size + M₁.length := by rw [hl₁]
    simp only [List.cons_append, List.nil_append]
    rw [pr_op impl κ inp r (v := .f 1) rfl,
      pr_op impl κ inp r (v := .f (1 + fv r r0)) (by simp only [evalOp, hb, rd_new1, hrdr r0 hr0]; rfl),
      pr_op impl κ inp r (v := .af p1) (by simp only [evalOp, hpk x1 hx1]; rfl),
      pr_op impl κ inp r (v := .af (eqTab p1)) (by
        simp only [evalOp, hb, List.append_assoc, List.cons_append, List.nil_append, rdX]; rfl),
      pr_op impl κ inp r (v := .af p2) (by
        simp only [evalOp]
        rw [show List.take 7 (List.drop (κ.m - 14) (chals fi "S2" 28)) = x2 from rfl, hpk x2 hx2]),
      pr_op impl κ inp r (v := .af (eqTab p2)) (by
        simp only [evalOp, hb, List.append_assoc, List.cons_append, List.nil_append, rdX]; rfl),
      pr_op impl κ inp r (v := .af p3) (by simp only [evalOp, hpk x3 hx3]; rfl),
      pr_op impl κ inp r (v := .af (eqTab p3)) (by
        simp only [evalOp, hb, List.append_assoc, List.cons_append, List.nil_append, rdX]; rfl)]
    simp [hL₀, hLs]
  have hL0 : L₀.length = 12168 := by rw [hL₀, List.length_append, hl₁]; rfl
  have hfin' : ∀ f ∈ fs, f < r.size + L₀.length := fun f h => Nat.lt_of_lt_of_le (hfin f h) (Nat.le_add_right _ _)
  -- the low weights
  have hw0 : ∀ i (X : List Val), evalOp impl κ inp (r ++ (L₀ ++ X).toArray)
      (Op.mulF (r.size + 190 * (i % 64) + 189) (if i < 64 then r.size + 190 * 64 + 1 else r0)) =
        .vals [.f (rsW κ fi r 0 i)] true := fun i X => by
    have hi : i % 64 < 64 := Nat.mod_lt _ (by decide)
    have h1 : rd (r ++ (L₀ ++ X).toArray) (r.size + 190 * (i % 64) + 189) =
        rd (r ++ M₁.toArray) (r.size + 190 * (i % 64) + 189) := by
      rw [hL₀, List.append_assoc, rdL r (by rw [hl₁]; omega)]
    simp only [evalOp, h1, hv₁ _ hi, rsW]
    by_cases h : i < 64
    · simp only [h, if_true, hrdL₀ 1 (by decide)]; rfl
    · simp only [h, if_false, hrdr r0 hr0]; rfl
  have hwE : ∀ t (ht : t < 8) (p : Array F), Ls.getD t default = .af (eqTab p) → ∀ i (X : List Val),
      evalOp impl κ inp (r ++ (L₀ ++ X).toArray) (.getF (r.size + 190 * 64 + t) i) =
        .vals [.f ((eqTab p).getD i 0)] true := fun t ht p hp i X => by
    simp only [evalOp, hrdL₀ t ht X, hp]; rfl
  -- the claims
  obtain ⟨N₀, c0h, c0l, c0a, c0t⟩ := run_claimOps impl κ inp r 0 _ fs (rsW κ fi r 0) L₀ [] hfs hfin' hw0
  obtain ⟨N₁, c1h, c1l, c1a, c1t⟩ := run_claimOps impl κ inp r 1 _ fs (rsW κ fi r 1) L₀ N₀ hfs hfin'
    (hwE 3 (by decide) p1 rfl)
  obtain ⟨N₂, c2h, c2l, c2a, c2t⟩ := run_claimOps impl κ inp r 2 _ fs (rsW κ fi r 2) L₀ (N₀ ++ N₁) hfs
    hfin' (hwE 5 (by decide) p2 rfl)
  obtain ⟨N₃, c3h, c3l, c3a, c3t⟩ := run_claimOps impl κ inp r 3 _ fs (rsW κ fi r 3) L₀ (N₀ ++ N₁ ++ N₂)
    hfs hfin' (hwE 7 (by decide) p3 rfl)
  rw [hE] at c0l c1l c2l c3l c0a c1a c2a c3a c0t c1t c2t c3t
  simp only [List.length_append, List.length_nil, hL0, c0l, c1l, c2l, Nat.add_zero] at c0h c1h c2h c3h c0a c1a c2a c3a c0t c1t c2t c3t
  simp only [List.append_nil, List.append_assoc] at c0h c1h c2h c3h c0a c1a c2a c3a c0t c1t c2t c3t
  have hrs : fs.map (fun f => (rd (r ++ L₀.toArray) f).toF) = rsFs fi r := by
    rw [List.map_congr_left fun f hf => by rw [rd_app_left r L₀ (hfin f hf)]]
    simp only [fs, rsFs, List.map_map]; rfl
  rw [hrs] at c0t c1t c2t c3t
  rw [hr0d] at c0h
  rw [show r.size + 12168 = r.size + 190 * 64 + 8 by norm_num] at c0h c1h c2h c3h c0a c1a c2a c3a c0t c1t c2t c3t
  rw [show 1 + 128 * 148 + (1 + 128 * 148) = 2 * (1 + 128 * 148) by ring] at c2h
  rw [show 1 + 128 * 148 + (1 + 128 * 148) + (1 + 128 * 148) = 3 * (1 + 128 * 148) by ring] at c3h
  simp only [finRS, ← hfsd, hE, List.append_assoc]
  rw [pr_app' impl κ inp r h₁, es, pr_app' impl κ inp r c0h, pr_app' impl κ inp r c1h,
    pr_app' impl κ inp r c2h, pr_app' impl κ inp r c3h]
  set A := 1 + 128 * 148 with hAd
  set Lc := L₀ ++ (N₀ ++ (N₁ ++ (N₂ ++ N₃)))
  have hLc : Lc.length = 12168 + 4 * A := by
    simp only [Lc, List.length_append, hL0, c0l, c1l, c2l, c3l]; ring
  have pre : ∀ (P Q : List Val) (t : ℕ), t < r.size + P.length →
      rd (r ++ (P ++ Q).toArray) t = rd (r ++ P.toArray) t := fun P Q t h => rdL r h
  have rT : ∀ (P Q : List Val) (t t' : ℕ) (v : F), Lc = P ++ Q → t' < r.size + P.length → t = t' →
      (rd (r ++ P.toArray) t').toF = v → (rd (r ++ Lc.toArray) t).toF = v := by
    intro P Q t t' v hPQ ht he hv; rw [hPQ, he, pre P Q t' ht, hv]
  obtain ⟨Mt, ht, hvt⟩ := run_rsTail impl κ inp r kap (r.size + 190 * 64 + 8 + A - 1)
    (r.size + 190 * 64 + 8 + 2 * A - 1) (r.size + 190 * 64 + 8 + 3 * A - 1)
    (r.size + Lc.length - 1) Lc (rsTv inp fi r 0) (rsTv inp fi r 1) (rsTv inp fi r 2)
    (rsTv inp fi r 3) (fv r kap) hkap rfl
    (by rw [hLc]; omega) (by rw [hLc]; omega) (by rw [hLc]; omega) (by rw [hLc]; omega)
    (rT (L₀ ++ N₀) (N₁ ++ (N₂ ++ N₃)) _ _ _ (by simp [Lc]) (by simp [hL0, c0l]; omega) (by omega) c0t)
    (rT (L₀ ++ (N₀ ++ N₁)) (N₂ ++ N₃) _ _ _ (by simp [Lc]) (by simp [hL0, c0l, c1l]; omega) (by omega) c1t)
    (rT (L₀ ++ (N₀ ++ (N₁ ++ N₂))) N₃ _ _ _ (by simp [Lc]) (by simp [hL0, c0l, c1l, c2l]; omega)
      (by omega) c2t)
    (rT Lc [] _ _ _ (by simp) (by simp [Lc, hL0, c0l, c1l, c2l, c3l]; omega) (by omega) c3t)
  rw [← hkapd, show r.size + 190 * 64 + 8 + 4 * A = r.size + Lc.length by rw [hLc]; omega, ht]
  refine ⟨Lc ++ Mt, rfl, fun j hj => ?_, ?_⟩
  · have rA : ∀ (P Q : List Val) (t t' : ℕ) (v : F), Lc = P ++ Q → t' < r.size + P.length → t = t' →
        (rd (r ++ P.toArray) t').toF = v → (rd (r ++ (Lc ++ Mt).toArray) t).toF = v := by
      intro P Q t t' v hPQ ht' he hv
      have hlt : t < r.size + Lc.length := by rw [he, hPQ, List.length_append]; omega
      rw [pre Lc Mt t hlt]; exact rT P Q t t' v hPQ ht' he hv
    interval_cases j <;> simp only [List.range_succ, List.range_zero, List.map_append, List.map_cons,
      List.map_nil, List.nil_append, List.cons_append, List.getD_cons_zero, List.getD_cons_succ]
    · exact rA (L₀ ++ N₀) (N₁ ++ (N₂ ++ N₃)) _ _ _ (by simp [Lc]) (by simp [hL0, c0l]; omega) (by omega) c0a
    · exact rA (L₀ ++ (N₀ ++ N₁)) (N₂ ++ N₃) _ _ _ (by simp [Lc]) (by simp [hL0, c0l, c1l]; omega) (by omega) c1a
    · exact rA (L₀ ++ (N₀ ++ (N₁ ++ N₂))) N₃ _ _ _ (by simp [Lc]) (by simp [hL0, c0l, c1l, c2l]; omega)
        (by omega) c2a
    · exact rA Lc [] _ _ _ (by simp) (by simp [Lc, hL0, c0l, c1l, c2l, c3l]; omega) (by omega) c3a
  · simp only [nRS, List.range_succ, List.range_zero, List.map_append, List.map_cons, List.map_nil,
      List.nil_append, List.cons_append, List.getD_cons_zero, List.getD_cons_succ]
    rw [hvt]; rfl

end RS

/-! ## `finE` and `finB′` (A.9) -/

/-- **`finE`** (A.9; node only): `â_M, b̂_M, ĉ_M` from the E-end absorb (A.3 row 9′, revision 3.7);
`c_{E2} = eq(r_E, r)·(â_M b̂_M + ĉ_M)` (`r_E` E1's 21 coordinates, `r` E2's challenges);
`c₀^{E2} = 0` holds by `initClaim`. Exports `v_E = â_M + κ_E b̂_M + κ_E² ĉ_M` and the row point `r`
(for `evalM(r, ρ)` at `finPf`). -/
def finE : FinField := fun fi b =>
  let kE := (outsOf fi "E3").headD 0
  ([.piElem fEEnd 0, .piElem fEEnd 16, .piElem fEEnd 32,
    .packF ((coordsR fi "E1").take 21), .packF (chals fi "E2" 21), .eqPt (b + 3) (b + 4),
    .mulF b (b + 1), .addF (b + 6) (b + 2), .mulF (b + 5) (b + 7),
    .assertEq (b + 8) (claimN fi "E2") Kind.isNode,
    .mulF kE (b + 1), .mulF kE kE, .mulF (b + 10) (b + 2), .addF b (b + 9), .addF (b + 12) (b + 11)],
   [b + 13, b + 4])

/-- The F halves of a digest (`splitDigest`). -/
def dLo (x : Digest) : F := F.ofBytes (Vector.ofFn fun i : Fin 16 => x[i.1])
def dHi (x : Digest) : F := F.ofBytes (Vector.ofFn fun i : Fin 16 => x[16 + i.1])

/-- **`finB′`** (A.9, revision 3.6): `v* = v_RS + κ′ v_E + Σ_k κ′^(k+2) pub_k` equals P1.0's initial
claim (in `K`). A node's public point claims, in order: M's `one` cell `1`; slot 0's `vk`, `c₁`; slot
1's `vk`, `c₂` (each digest as its two halves); the zero padding cells after them add nothing. A
leaf kind has none (`keep`). `v_RS` is `finRS`'s export 5, `v_E` `finE`'s export 0. Exports `v*`. -/
def finB' : FinField := fun fi b =>
  let kp := (outsOf fi "B'").headD 0
  let vRS := fi.zhat.getD nRS 0
  let vE := (fi.ex.getD 5 []).headD 0
  ([.input 0, .splitDigest b, .piDigest fStmt 1, .splitDigest (b + 3), .piDigest fStmt 33,
    .splitDigest (b + 6), .const (fun _ => .f 1),
    .mulF kp (b + 8), .addF (b + 7) (b + 10), .mulF kp (b + 11), .addF (b + 2) (b + 12),
    .mulF kp (b + 13), .addF (b + 1) (b + 14), .mulF kp (b + 15), .addF (b + 5) (b + 16),
    .mulF kp (b + 17), .addF (b + 4) (b + 18), .mulF kp (b + 19), .addF (b + 2) (b + 20),
    .mulF kp (b + 21), .addF (b + 1) (b + 22), .mulF kp (b + 23), .addF (b + 9) (b + 24),
    .mulF kp kp, .mulF (b + 26) (b + 25), .const (fun _ => .f 0), .keep Kind.isNode (b + 27) (b + 28),
    .mulF kp vE, .addF vRS (b + 30), .addF (b + 31) (b + 29),
    .const (fun _ => .k 1), .mulKF (b + 33) (b + 32), .assertEq (b + 34) (claim0 fi "P1") allK],
   [b + 32])

section EB
variable (impl : OpImpl) (κ : Kind) (inp : Input) (fi : FinIn) (r : Array Val)

/-- **A.9's `finE` relation** (node only). -/
def relE : Bool :=
  let a := pe inp fEEnd 0; let bb := pe inp fEEnd 16; let c := pe inp fEEnd 32
  if κ.isNode then
    (Val.f (eqPoint (((coordsR fi "E1").take 21).map (fv r)).toArray ((chals fi "E2" 21).map (fv r)).toArray *
      (a * bb + c))).eqv (rd r (claimN fi "E2"))
  else true

/-- `v_E`. -/
def vE : F :=
  let kE := fv r ((outsOf fi "E3").headD 0)
  pe inp fEEnd 0 + kE * pe inp fEEnd 16 + kE * kE * pe inp fEEnd 32

/-- **`flag_finE`**: `finE` asks nothing, its flag is `relE`, its exports `v_E` and the point `r`. -/
theorem flag_finE (hin : ∀ x ∈ (coordsR fi "E1").take 21 ++ chals fi "E2" 21 ++
      [(outsOf fi "E3").headD 0, claimN fi "E2"], x < r.size) :
    ∃ L, pureRun impl κ inp (finE fi r.size).1 r [] = some (L, relE κ inp fi r) ∧
      (rd (r ++ L.toArray) ((finE fi r.size).2.getD 0 0)).toF = vE inp fi r ∧
      (rd (r ++ L.toArray) ((finE fi r.size).2.getD 1 0)).toAF = ((chals fi "E2" 21).map (fv r)).toArray := by
  simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hin
  have h1 := fun L => map_rd_app r L ((coordsR fi "E1").take 21) fun x hx => hin x (.inl (.inl hx))
  have h2 := fun L => map_rd_app r L (chals fi "E2" 21) fun x hx => hin x (.inl (.inr hx))
  have tf : ∀ x, (Val.f x).toF = x := fun _ => rfl
  have taf : ∀ x, (Val.af x).toAF = x := fun _ => rfl
  simp only [finE, relE, vE]
  generalize (outsOf fi "E3").headD 0 = kE at *
  generalize claimN fi "E2" = cE at *
  have hk := hin kE (.inr (.inl rfl)); have hc := hin cE (.inr (.inr rfl))
  cases hn : κ.isNode <;>
  simp only [hn, pureRun, evalOp, tf, taf, List.nil_append, List.cons_append, h1, h2,
    rd_app, rd_app0, rd_app_left _ _ hk, rd_app_left _ _ hc, List.getD_cons_succ, List.getD_cons_zero,
    Option.map_some, Bool.not_true, Bool.not_false, Bool.false_or, Bool.true_or, Bool.true_and,
    Bool.and_true, ↓reduceIte, Bool.false_eq_true] <;>
  exact ⟨_, rfl, rfl, rfl⟩

/-- The public point claims' Horner sum `Σ_k κ′^k pub_k` (A.9 `finB′`, the order of `finB'`). -/
def pubH (kp : F) : F :=
  let vl := dLo inp.vk; let vh := dHi inp.vk
  let c₁ := bytesAt inp.π (absOff fStmt 1) 32; let c₂ := bytesAt inp.π (absOff fStmt 33) 32
  1 + kp * (vl + kp * (vh + kp * (dLo c₁ + kp * (dHi c₁ + kp * (vl + kp * (vh + kp * (dLo c₂ +
    kp * dHi c₂)))))))

/-- **`v*`** (A.9 `finB′`) from the register values of `κ′`, `v_RS`, `v_E`. -/
def vStar : F :=
  let kp := fv r ((outsOf fi "B'").headD 0)
  fv r (fi.zhat.getD nRS 0) + kp * fv r ((fi.ex.getD 5 []).headD 0) +
    (if κ.isNode then kp * kp * pubH inp kp else 0)

/-- **A.9's `finB′` relation**: `v*` (in `K`) is P1.0's initial claim. -/
def relB : Bool := (Val.k (K.smulF (vStar κ inp fi r) 1)).eqv (rd r (claim0 fi "P1"))

/-- **`flag_finB'`**: `finB'` asks nothing; its flag is `relB`; its export is `v*`. -/
theorem flag_finB' (hin : ∀ x ∈ [(outsOf fi "B'").headD 0, fi.zhat.getD nRS 0, (fi.ex.getD 5 []).headD 0,
      claim0 fi "P1"], x < r.size) :
    ∃ L, pureRun impl κ inp (finB' fi r.size).1 r [] = some (L, relB κ inp fi r) ∧
      (rd (r ++ L.toArray) ((finB' fi r.size).2.getD 0 0)).toF = vStar κ inp fi r := by
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hin
  have tf : ∀ x, (Val.f x).toF = x := fun _ => rfl
  have td : ∀ x, (Val.d x).toD = x := fun _ => rfl
  have tk : ∀ x, (Val.k x).toK = x := fun _ => rfl
  simp only [finB', relB, vStar, pubH, dLo, dHi]
  generalize (outsOf fi "B'").headD 0 = kp at *
  generalize fi.zhat.getD nRS 0 = vR at *
  generalize (fi.ex.getD 5 []).headD 0 = vE at *
  generalize claim0 fi "P1" = c0 at *
  have hk := hin kp (.inl rfl); have hR := hin vR (.inr (.inl rfl))
  have hE := hin vE (.inr (.inr (.inl rfl))); have hc := hin c0 (.inr (.inr (.inr rfl)))
  cases hn : κ.isNode <;>
  simp only [hn, pureRun, evalOp, tf, td, tk, List.nil_append, List.cons_append,
    rd_app, rd_app0, rd_app_left _ _ hk, rd_app_left _ _ hR, rd_app_left _ _ hE, rd_app_left _ _ hc,
    List.getD_cons_succ, List.getD_cons_zero, Option.map_some, allK, Bool.not_true, Bool.false_or,
    Bool.true_and, Bool.and_true, ↓reduceIte, Bool.false_eq_true, ite_true, ite_false] <;>
  exact ⟨_, rfl, rfl⟩

end EB

/-! ## They ask nothing; the finals with S-F's fields -/

theorem noAsk_sqOps : ∀ n x b, (sqOps n x b).filterMap Op.item? = []
  | 0, _, _ => rfl
  | n + 1, x, b => by simp only [sqOps, List.filterMap_cons, Op.item?, noAsk_sqOps n b (b + 1)]

theorem noAsk_phiOps : ∀ (fs : List ℕ) (s x b : ℕ), (phiOps fs s x b).filterMap Op.item? = []
  | [], _, _, _ => rfl
  | f :: fs, s, x, b => by
    simp only [phiOps, List.filterMap_append, noAsk_sqOps, List.filterMap_cons, Op.item?,
      noAsk_phiOps fs, List.filterMap_nil, List.append_nil]

theorem noAsk_elemsOps (j : ℕ) (wop : ℕ → Op) (hw : ∀ i, (wop i).item? = none) (fs : List ℕ) :
    ∀ n i aA aT b, (elemsOps j wop fs n i aA aT b).filterMap Op.item? = []
  | 0, _, _, _, _ => rfl
  | n + 1, i, aA, aT, b => by
    simp only [elemsOps, elemOps, List.filterMap_append, List.filterMap_cons, hw i,
      noAsk_phiOps, noAsk_elemsOps j wop hw fs n, List.filterMap_nil, List.append_nil]
    rfl

theorem noAsk_prodOps (lam : ℕ) : ∀ (js : List ℕ) (acc b : ℕ), (prodOps lam js acc b).filterMap Op.item? = []
  | [], _, _ => rfl
  | j :: js, acc, b => by
    simp only [prodOps, List.filterMap_append, List.filterMap_cons, Op.item?, noAsk_prodOps lam js,
      List.filterMap_nil, List.append_nil]

theorem noAsk_lagAll (lam : ℕ) : ∀ n i b, (lagAll lam n i b).filterMap Op.item? = []
  | 0, _, _ => rfl
  | n + 1, i, b => by
    simp only [lagAll, lagOne, List.filterMap_append, List.filterMap_cons, Op.item?, noAsk_prodOps,
      noAsk_lagAll lam n, List.filterMap_nil, List.append_nil]

/-- **S-F's fields ask nothing** (`items_gen`'s hypothesis, for these fields). -/
theorem noAsk_claimOps (j : ℕ) (wop : ℕ → Op) (hw : ∀ i, (wop i).item? = none) (fs : List ℕ) (b : ℕ) :
    (claimOps j wop fs b).filterMap Op.item? = [] := by
  simp only [claimOps, List.filterMap_cons, noAsk_elemsOps j wop hw]; rfl

theorem noAsk_rsTail (kap t₀ t₁ t₂ t₃ d : ℕ) : (rsTail kap t₀ t₁ t₂ t₃ d).filterMap Op.item? = [] := rfl

theorem noAsk_finRS (fi : FinIn) (b : ℕ) : (finRS fi b).1.filterMap Op.item? = [] := by
  simp only [finRS, List.filterMap_append, noAsk_lagAll, noAsk_rsTail,
    noAsk_claimOps _ (fun i => Op.getF _ i) (fun _ => rfl),
    noAsk_claimOps _ (fun i => Op.mulF _ (if i < 64 then _ else _)) (fun _ => rfl),
    List.append_nil, List.nil_append]
  rfl

theorem noAsk_finE (fi : FinIn) (b : ℕ) : (finE fi b).1.filterMap Op.item? = [] := by
  simp [finE, Op.item?]

theorem noAsk_finB' (fi : FinIn) (b : ℕ) : (finB' fi b).1.filterMap Op.item? = [] := by
  simp [finB', Op.item?]

/-- **The finals with S-0's and S-F's fields**; S-G's `finP`, `finPf` as arguments. -/
def sfFinals (p : ℕ → FinField) (pf : FinField) : Finals := s0Finals finRS finE finB' p pf

end FR
