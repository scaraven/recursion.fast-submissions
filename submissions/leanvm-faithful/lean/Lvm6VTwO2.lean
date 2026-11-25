-- New for lvm6 (WP TWO): the fast twin of W1's deployed opening `whirP18`, part 2: the rounds, the weights (W1's
-- closures `WtE`, folded by substituting the challenge, valid for multiaffine weights: `wFolds_eq`), the glue, the
-- tail sumcheck, a level with a next one (`tw_mid`), the final level (`tw_fin`), and **`tw_whirP18`**.
import Lvm6VTwO

/-!
# The opening in the word field (TWO, part 2)

* `fRound`, `fRounds` (`tw_rounds`); `foldsCF` (`foldsC_eq`); `alphasF` (`alphasE_map`).
* **`wFolds_eq`**: a weight affine in its first `j` variables, folded by `j` rounds, is the weight at the rounds'
  challenges: `(wFolds j rs w).2 y = w.2 (α₁ … α_j ++ y)` (W1's `foldTab` doubles the evaluations; this does not).
  `WR κ m w φ`: `w` is admitted (`wokE`: affine in its `m + κ` variables) and `φ` is its fast form.
* `prodLF`, `eqLF`, `colLF`, `mleLF`, `psum`; `glueF` (`wGlueE_eq`), `gluedCF` (`gluedC_eq`).
* `fSumP` (`tw_sumP`), `fTail` (`tw_tail`), **`tw_mid`**, **`tw_fin`**, **`tw_whirP18`**.
-/

set_option autoImplicit false

namespace Lvm6.V

open RecursionFast LeanVM.Parameters Lvm.FS Lvm.Replay Lvm Lvm.E2V
open LeanVM.Protocol.Compile hiding Proof Bytes Word
open LeanVM.Protocol.Whir (bitsToNat)

/-! ## Rounds and claims -/

/-- Fast `roundP chalE2 g`. -/
def fRound (g : ℕ) : VF RndF :=
  VF.bind fReadF fun u₀ => VF.bind fReadF fun w => VF.bind fReadF fun c₀ => VF.bind fReadF fun c₁ =>
    VF.bind (fGrp g 1) fun v => VF.pure ⟨u₀, w, c₀, c₁, v.getD 0 0, v.getD 1 0⟩

theorem tw_round (g : ℕ) : TwinF RndF.dec (Whir.roundP Whir.chalE2 g) (fRound g) := by
  unfold Whir.roundP fRound
  exact tw_bind tw_readF fun _ => tw_bind tw_readF fun _ => tw_bind tw_readF fun _ =>
    tw_bind tw_readF fun _ => tw_bind (tw_grp g 1) fun _ => tw_pure (by simp only [RndF.dec, toE2_getD])

/-- Fast `roundsP chalE2 g n`. -/
def fRounds (g : ℕ) : ℕ → VF (List RndF)
  | 0 => VF.pure []
  | n + 1 => VF.bind (fRound g) fun r => VF.bind (fRounds g n) fun rs => VF.pure (r :: rs)

theorem tw_rounds (g : ℕ) : ∀ n, TwinF (List.map RndF.dec) (Whir.roundsP Whir.chalE2 g n) (fRounds g n)
  | 0 => tw_pure rfl
  | n + 1 => tw_bind (f := fun r => Whir.roundsP Whir.chalE2 g n >>= fun rs => pure (r :: rs)) (tw_round g)
      fun _ => tw_bind (tw_rounds g n) fun _ => tw_pure rfl

theorem headD_map_dec : ∀ rs : List RndF, (rs.map RndF.dec).headD default = RndF.dec (rs.headD default)
  | [] => rfl
  | _ :: _ => rfl

theorem tail_map_dec : ∀ rs : List RndF, (rs.map RndF.dec).tail = rs.tail.map RndF.dec
  | [] => rfl
  | _ :: _ => rfl

/-- The claim after a fold round. -/
def foldClaimF (σ α β u₀ w c₀ c₁ : FE2) : FE2 :=
  u₀ + α * (σ - u₀) + α ^ 2 * w + β * c₀ + α * β * (c₁ - c₀)

theorem toE2_foldClaimF (σ α β u₀ w c₀ c₁ : FE2) :
    FE2.toE2 (foldClaimF σ α β u₀ w c₀ c₁) = Whir.foldClaim (FE2.toE2 σ) (FE2.toE2 α) (FE2.toE2 β)
      (FE2.toE2 u₀) (FE2.toE2 w) (FE2.toE2 c₀) (FE2.toE2 c₁) := by
  simp only [foldClaimF, Whir.foldClaim, ← coe_tE, map_add, map_mul, map_sub, map_pow]

/-- The claim after `j` rounds. -/
def foldsCF : ℕ → List RndF → FE2 → FE2
  | 0, _, σ => σ
  | j + 1, rs, σ =>
    let r := rs.headD default
    foldsCF j rs.tail (foldClaimF σ r.α r.β r.u₀ r.w r.c₀ r.c₁)

theorem foldsC_eq : ∀ (j : ℕ) (rs : List RndF) (σ : FE2),
    Whir.foldsC j (rs.map RndF.dec) (FE2.toE2 σ) = FE2.toE2 (foldsCF j rs σ)
  | 0, _, _ => rfl
  | j + 1, rs, σ => by
    have h := foldsC_eq j rs.tail (foldClaimF σ (rs.headD default).α (rs.headD default).β
      (rs.headD default).u₀ (rs.headD default).w (rs.headD default).c₀ (rs.headD default).c₁)
    rw [toE2_foldClaimF, ← tail_map_dec] at h
    simp only [Whir.foldsC, foldsCF, headD_map_dec]
    exact h

/-- The fold challenges of `j` rounds, first round first. -/
def alphasE : ℕ → List (Whir.Rnd E2) → List E2
  | 0, _ => []
  | j + 1, rs => (rs.headD default).α :: alphasE j rs.tail

def alphasF : ℕ → List RndF → List FE2
  | 0, _ => []
  | j + 1, rs => (rs.headD default).α :: alphasF j rs.tail

theorem alphasE_map : ∀ (j : ℕ) (rs : List RndF), alphasE j (rs.map RndF.dec) = (alphasF j rs).map FE2.toE2
  | 0, _ => rfl
  | j + 1, rs => congrArg₂ List.cons (congrArg Whir.Rnd.α (headD_map_dec rs))
      ((congrArg (alphasE j) (tail_map_dec rs)).trans (alphasE_map j rs.tail))

/-! ## Folding a multiaffine weight -/

theorem MA_le : ∀ (n m : ℕ) (f : List E2 → E2), Whir.MA (n + m) f → Whir.MA n f
  | 0, _, _, _ => trivial
  | n + 1, m, f, h => by
    rw [show n + 1 + m = n + m + 1 by omega] at h
    exact ⟨h.1, fun X => MA_le n m _ (h.2 X)⟩

/-- **The fold of a weight affine in its first `j` variables is the substitution of the challenges.** -/
theorem wFolds_eq : ∀ (j : ℕ) {m : ℕ} (rs : List (Whir.Rnd E2)) (w : Whir.WtE.Wt (m + j)),
    Whir.MA j w.2 → (Whir.wFolds (m := m) Whir.WtE j rs w).2 = fun y => w.2 (alphasE j rs ++ y)
  | 0, _, _, _, _ => rfl
  | j + 1, m, rs, w, h =>
    (wFolds_eq j (m := m) rs.tail (Whir.WtE.wFold w (rs.headD default).α) (Whir.MA.fold h _)).trans
      (funext fun _ => (h.1 _ _).symm)

/-- **A fast weight**: `w` is admitted at `κ` message variables and `m` lanes, and `φ` computes it. -/
abbrev WR (κ m : ℕ) (w : Whir.WtE.Wt (0 + m)) (φ : List FE2 → FE2) : Prop :=
  Whir.wokE κ m w ∧ ∀ x : List FE2, w.2 (x.map FE2.toE2) = FE2.toE2 (φ x)

theorem wFolds_val (j : ℕ) {m : ℕ} (rs : List RndF) (w : Whir.WtE.Wt (m + j)) (φ : List FE2 → FE2)
    (hma : Whir.MA j w.2) (hφ : ∀ x : List FE2, w.2 (x.map FE2.toE2) = FE2.toE2 (φ x)) (x : List FE2) :
    (Whir.wFolds (m := m) Whir.WtE j (rs.map RndF.dec) w).2 (x.map FE2.toE2) =
      FE2.toE2 (φ (alphasF j rs ++ x)) := by
  rw [wFolds_eq j _ w hma]
  show w.2 (alphasE j (rs.map RndF.dec) ++ x.map FE2.toE2) = _
  rw [alphasE_map, ← List.map_append, hφ]

/-! ## The weights' factors -/

/-- `prodL` in the word field. -/
def prodLF (a : ℕ → FE2 → FE2) : ℕ → List FE2 → FE2
  | 0, _ => 1
  | n + 1, y => a 0 (y.headD 0) * prodLF (fun i => a (i + 1)) n y.tail

theorem toE2_prodLF : ∀ (n : ℕ) (a : ℕ → FE2 → FE2) (a' : ℕ → E2 → E2),
    (∀ i, i < n → ∀ X, FE2.toE2 (a i X) = a' i (FE2.toE2 X)) → ∀ y,
      FE2.toE2 (prodLF a n y) = Whir.prodL a' n (y.map FE2.toE2)
  | 0, _, _, _, _ => toE2_one'
  | n + 1, a, a', h, y => by
    have ih := toE2_prodLF n (fun i => a (i + 1)) (fun i => a' (i + 1))
      (fun i hi X => h (i + 1) (by omega) X)
    cases y with
    | nil =>
      show FE2.toE2 (a 0 0 * prodLF _ n []) = a' 0 0 * Whir.prodL _ n []
      rw [toE2_mul', h 0 (by omega), ih []]
      rfl
    | cons x y =>
      show FE2.toE2 (a 0 x * prodLF _ n y) = a' 0 (FE2.toE2 x) * Whir.prodL _ n (y.map FE2.toE2)
      rw [toE2_mul', h 0 (by omega), ih y]

theorem toE2_sum {ι : Type} (s : Finset ι) (f : ι → FE2) :
    FE2.toE2 (∑ i ∈ s, f i) = ∑ i ∈ s, FE2.toE2 (f i) := map_sum tE f s

/-- The OOD weight `eq(z, ·)` on `ν` variables. -/
def eqLF (ν : ℕ) (z y : List FE2) : FE2 :=
  prodLF (fun i X => z.getD i 0 * X + (1 - z.getD i 0) * (1 - X)) ν y

theorem toE2_eqLF (ν : ℕ) (z y : List FE2) :
    FE2.toE2 (eqLF ν z y) = Whir.eqL (ν := ν) (Whir.gv (z.map FE2.toE2)) (y.map FE2.toE2) :=
  toE2_prodLF ν _ _ (fun i hi X => by
    rw [dif_pos hi, toE2_add', toE2_mul', toE2_mul', toE2_sub', toE2_sub', toE2_one', toE2_getD]
    rfl) y

/-- The query weight at a position from its table `W = nwF (K(p))`. -/
def colLF (κ : ℕ) (W : List FK) (y : List FE2) : FE2 :=
  prodLF (fun i X => (1 - X) + FE2.mulK X (W.getD i 0)) κ y

theorem toE2_colLF (κ p : ℕ) (hκ : κ ≤ 20) (y : List FE2) :
    FE2.toE2 (colLF κ (nwF (kOfNat p)) y) = Whir.colL κ p (y.map FE2.toE2) :=
  toE2_prodLF κ _ _ (fun i hi X => by
    rw [toE2_add', toE2_sub', toE2_one', FE2.toE2_mulK, nwF_spec _ i (by omega), toBF64_kOfNat]
    rfl) y

/-- The final message's multilinear extension (`mleL (msgOf κ s)`). -/
def mleLF (κ : ℕ) (s y : List FE2) : FE2 :=
  ∑ c : Fin κ → Bool, s.getD (bitsToNat c) 0 *
    prodLF (fun i X => if h : i < κ then (if c ⟨i, h⟩ then X else 1 - X) else 1) κ y

theorem toE2_mleLF (κ : ℕ) (s y : List FE2) :
    FE2.toE2 (mleLF κ s y) = Whir.mleL (Whir.msgOf κ (s.map FE2.toE2)) (y.map FE2.toE2) := by
  simp only [mleLF, Whir.mleL, Whir.msgOf]
  rw [toE2_sum]
  refine Finset.sum_congr rfl fun c _ => ?_
  rw [toE2_mul', toE2_getD, toE2_prodLF κ _
    (fun i X => if h : i < κ then (if c ⟨i, h⟩ then X else 1 - X) else 1) (fun i hi X => ?_) y]
  rw [dif_pos hi, dif_pos hi]
  by_cases hc : c ⟨i, hi⟩ = true
  · rw [if_pos hc, if_pos hc]
  · rw [if_neg hc, if_neg hc, toE2_sub', toE2_one']

/-- `(Σ_{k<n} λ^(k+2) f(k), λ^(n+2))`, with a running power. -/
def psum (lam : FE2) (f : ℕ → FE2) : ℕ → FE2 × FE2
  | 0 => (0, lam * lam)
  | n + 1 => let r := psum lam f n; (r.1 + r.2 * f n, r.2 * lam)

theorem toE2_psum (lam : FE2) (f : ℕ → FE2) : ∀ n,
    FE2.toE2 (psum lam f n).1 = ∑ k ∈ Finset.range n, FE2.toE2 lam ^ (k + 2) * FE2.toE2 (f k) ∧
    FE2.toE2 (psum lam f n).2 = FE2.toE2 lam ^ (n + 2)
  | 0 => ⟨by simp [psum], by simp [psum, pow_two]⟩
  | n + 1 => by
    obtain ⟨h1, h2⟩ := toE2_psum lam f n
    refine ⟨?_, ?_⟩
    · show FE2.toE2 ((psum lam f n).1 + (psum lam f n).2 * f n) = _
      rw [toE2_add', toE2_mul', h1, h2, Finset.sum_range_succ]
    · show FE2.toE2 ((psum lam f n).2 * lam) = _
      rw [toE2_mul', h2]
      ring

/-- **The next level's weight** (`wGlueE` on the substituted weight `φ`): `φ + λ eq(z, ·) + Σ λ^(k+2) col_k`. -/
def glueF (ko t : ℕ) (φ : List FE2 → FE2) (zv : List FE2) (lam : FE2) (pk : ℕ → ℕ) (y : List FE2) : FE2 :=
  φ y + lam * eqLF (ko + 1) zv y + (psum lam (fun k => colLF (ko + 1) (nwF (kOfNat (pk k))) y) t).1

theorem wGlueE_eq (κ' ℓ' ko t h : ℕ) (hko : ko + 1 ≤ 20) (w : Whir.WtE.Wt 0) (φ : List FE2 → FE2)
    (hφ : ∀ x : List FE2, w.2 (x.map FE2.toE2) = FE2.toE2 (φ x)) (o : Whir.TailOut E2 ko t (2 ^ h))
    (zv : List FE2) (hz : o.z = Whir.gv (zv.map FE2.toE2)) (lam : FE2) (hlam : o.lam = FE2.toE2 lam)
    (pk : ℕ → ℕ) (hpk : ∀ k : Fin t, (o.ps k : ℕ) = pk k) (x : List FE2) :
    (Whir.wGlueE κ' ℓ' ko t h w o).2 (x.map FE2.toE2) = FE2.toE2 (glueF ko t φ zv lam pk x) := by
  show w.2 (x.map FE2.toE2) + o.lam * Whir.eqL o.z (x.map FE2.toE2) +
    ∑ k : Fin t, o.lam ^ ((k : ℕ) + 2) * Whir.colL (ko + 1) (o.ps k) (x.map FE2.toE2) = _
  have hcol : ∀ k : Fin t, Whir.colL (ko + 1) (o.ps k) (x.map FE2.toE2) =
      FE2.toE2 (colLF (ko + 1) (nwF (kOfNat (pk k))) x) := fun k => by
    rw [hpk k, toE2_colLF (ko + 1) (pk k) hko x]
  simp only [hcol]
  rw [hφ, hz, hlam, ← toE2_eqLF (ko + 1) zv x,
    Fin.sum_univ_eq_sum_range (fun k => FE2.toE2 lam ^ (k + 2) * FE2.toE2 (colLF (ko + 1) (nwF (kOfNat (pk k))) x)) t,
    ← (toE2_psum lam (fun k => colLF (ko + 1) (nwF (kOfNat (pk k))) x) t).1, glueF, toE2_add', toE2_add',
    toE2_mul']

/-- **The next level's claim** `σ + λ y + Σ_{k<t} λ^(k+2) c_k`. -/
def gluedCF (σ y lam : FE2) (t : ℕ) (cs : List FE2) : FE2 :=
  σ + lam * y + (psum lam (fun k => cs.getD k 0) t).1

theorem gluedC_eq (t : ℕ) (σ y lam : FE2) (cs : List FE2) :
    Whir.gluedC (FE2.toE2 σ) (FE2.toE2 y) (FE2.toE2 lam) (fun k : Fin t => FE2.toE2 (cs.getD k 0)) =
      FE2.toE2 (gluedCF σ y lam t cs) := by
  rw [Whir.gluedC, gluedCF, toE2_add', toE2_add', toE2_mul', (toE2_psum lam _ t).1,
    ← Fin.sum_univ_eq_sum_range (fun k => FE2.toE2 lam ^ (k + 2) * FE2.toE2 (cs.getD k 0)) t]

/-! ## The tail sumcheck -/

/-- The round polynomial `c₀ + (c − 2c₀ − c₂) r + c₂ r²`. -/
def roundPolyF (c c₀ c₂ r : FE2) : FE2 := c₀ + (c - 2 * c₀ - c₂) * r + c₂ * r ^ 2

theorem toE2_roundPolyF (c c₀ c₂ r : FE2) :
    FE2.toE2 (roundPolyF c c₀ c₂ r) =
      Whir.roundPoly (FE2.toE2 c) (FE2.toE2 c₀) (FE2.toE2 c₂) (FE2.toE2 r) := by
  simp only [roundPolyF, Whir.roundPoly, ← coe_tE, map_add, map_mul, map_sub, map_pow, map_ofNat]

/-- Fast `sumP chalE2 g Φ M n τ c`. -/
def fSumP (g : ℕ) (φ μ : List FE2 → FE2) : ℕ → List FE2 → FE2 → VF Bool
  | 0, τ, c => VF.pure (decide (φ τ * μ τ = c))
  | n + 1, τ, c => VF.bind fReadF fun c₀ => VF.bind fReadF fun c₂ => VF.bind (fGrp g 0) fun v =>
      fSumP g φ μ n (τ ++ [v.getD 0 0]) (roundPolyF c c₀ c₂ (v.getD 0 0))

theorem tw_sumP (g : ℕ) (Φ M : List E2 → E2) (φ μ : List FE2 → FE2)
    (hΦ : ∀ x : List FE2, Φ (x.map FE2.toE2) = FE2.toE2 (φ x))
    (hM : ∀ x : List FE2, M (x.map FE2.toE2) = FE2.toE2 (μ x)) :
    ∀ (n : ℕ) (τF : List FE2) (cF : FE2) (τ : List E2) (c : E2), τ = τF.map FE2.toE2 → c = FE2.toE2 cF →
      TwinF id (Whir.sumP Whir.chalE2 g Φ M n τ c) (fSumP g φ μ n τF cF)
  | 0, τF, cF, _, _, hτ, hc => by
    subst hτ hc
    refine tw_pure ?_
    show decide _ = decide _
    rw [hΦ, hM, ← toE2_mul']
    exact decide_eq_decide.mpr ⟨fun h => congrArg FE2.toE2 h, fun h => FE2.toE2_injective h⟩
  | n + 1, τF, cF, _, _, hτ, hc => by
    subst hτ hc
    show TwinF id (Whir.readF Whir.chalE2 >>= fun c₀ => Whir.readF Whir.chalE2 >>= fun c₂ =>
      Whir.chalE2.grp g 0 >>= fun v => Whir.sumP Whir.chalE2 g Φ M n (τF.map FE2.toE2 ++ [v.getD 0 0])
        (Whir.roundPoly (FE2.toE2 cF) c₀ c₂ (v.getD 0 0))) (fSumP g φ μ (n + 1) τF cF)
    exact tw_bind tw_readF fun c₀ => tw_bind tw_readF fun c₂ => tw_bind (tw_grp g 0) fun v =>
      tw_sumP g Φ M φ μ hΦ hM n _ _ _ _
        (by rw [List.map_append, List.map_cons, List.map_nil, toE2_getD])
        (by rw [toE2_roundPolyF, toE2_getD])

/-! ## A level's interface -/

/-- A level's interface output in the word field. -/
structure TailOutF where
  hi : List FE2
  zv : List FE2
  y : FE2
  qv : List FE2
  c : List FE2

/-- Its value. -/
noncomputable def TailOutF.dec {n n' m' : ℕ} (L : Whir.TailIface E2 n n' m') (o : TailOutF) :
    Whir.TailOut E2 L.ko L.t n :=
  ⟨o.hi.map FE2.toE2, Whir.gv (o.zv.map FE2.toE2), FE2.toE2 o.y, Whir.qPos L (o.qv.map FE2.toE2),
    Whir.qLam L (o.qv.map FE2.toE2), fun k => FE2.toE2 (o.c.getD k 0)⟩

/-- Fast `tailP`: the high part, the next commitment, the bind, the OOD group and value, the query group, the
openings, and the values `valsF` derives from the opened rows. -/
def fTail (nh ht wd i gO ko gQ kq : ℕ) (psF : List FE2 → List ℕ)
    (valsF : ByteArray → List FE2 → List FE2 → RowsF → List FE2) : VF TailOutF :=
  VF.bind (fE2Reads nh) fun hi => VF.bind (fCommit ht wd) fun _ => VF.bind fSep fun _ =>
  VF.bind (fGrp gO ko) fun zv => VF.bind fReadF fun y => VF.bind (fGrp gQ (kq + 1)) fun qv =>
  VF.bind (fQuery i (psF qv)) fun r => fun π tr => some (⟨hi, zv, y, qv, valsF π hi qv r⟩, tr)

theorem tw_tail {n n' m' : ℕ} (L : Whir.TailIface E2 n n' m') (ht wd i gO gQ : ℕ)
    (vals : List E2 → (Fin L.t → Fin n) → List (List K) → Fin L.t → E2) (psF : List FE2 → List ℕ)
    (hps : ∀ qv : List FE2, (List.ofFn fun k => (Whir.qPos L (qv.map FE2.toE2) k : ℕ)) = psF qv)
    (valsF : ByteArray → List FE2 → List FE2 → RowsF → List FE2)
    (hv : ∀ π hi qv (r : RowsF) (k : Fin L.t), vals (hi.map FE2.toE2) (Whir.qPos L (qv.map FE2.toE2)) (r.dec π) k =
      FE2.toE2 ((valsF π hi qv r).getD k 0)) :
    TwinF (TailOutF.dec L) (Whir.tailP L Whir.chalE2 ht wd i gO gQ vals)
      (fTail L.nh ht wd i gO L.ko gQ L.kq psF valsF) := by
  unfold Whir.tailP fTail
  refine tw_bind (tw_readFs L.nh) fun hi => tw_bind (tw_commit ht wd) fun _ => tw_bind tw_sep fun _ =>
    tw_bind (tw_grp gO L.ko) fun zv => tw_bind tw_readF fun y => tw_bind (tw_grp gQ (L.kq + 1)) fun qv => ?_
  rw [hps qv]
  refine tw_bindR (twin_query i (psF qv)) fun π r rows hr tr => ?_
  subst hr
  refine Option.Rel.some ⟨?_, rfl⟩
  show Whir.TailOut.mk _ _ _ _ _ (fun k => FE2.toE2 ((valsF π hi qv r).getD k 0)) =
    Whir.TailOut.mk _ _ _ _ _ (vals (hi.map FE2.toE2) (Whir.qPos L (qv.map FE2.toE2)) (r.dec π))
  congr 1
  funext k
  exact (hv π hi qv r k).symm

/-! ## A level with a next one -/

theorem getD_ofFn {t : ℕ} (f : Fin t → FE2) (k : ℕ) (hk : k < t) : (List.ofFn f).getD k 0 = f ⟨k, hk⟩ := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_ofFn, dif_pos hk]
  rfl

/-- A mid level's values at its `t` positions. -/
def valsMidF (z : Bool) (κ ℓ h c t : ℕ) (rs : List RndF) (π : ByteArray) (hi qv : List FE2) (r : RowsF) :
    List FE2 :=
  List.ofFn fun k : Fin t => valAtF κ ℓ rs hi (posNF h c qv k) (laneF z π r r.os[(k : ℕ)]?)

theorem ladP_claim {n ℓ : ℕ} {lad : Whir.Lad E2 Whir.WtE n ℓ} {w : Whir.WtE.Wt (0 + ℓ)} {s s' : E2}
    {fp : VF Bool} (h : s = s') (H : TwinF id (Whir.ladP Whir.chalE2 lad w s') fp) :
    TwinF id (Whir.ladP Whir.chalE2 lad w s) fp := h ▸ H

/-- **Fast level with a next one**: the rounds, the interface, then the next level on the glued weight and claim. -/
def fMid (i ko ℓ h h' kq t c gQ : ℕ) (z : Bool) (frest : (List FE2 → FE2) → FE2 → VF Bool)
    (φ : List FE2 → FE2) (σ : FE2) : VF Bool :=
  VF.bind (fRounds 10 ℓ) fun rs =>
  VF.bind (fTail ℓ h' 32 i 18 ko gQ kq (posListF h c t) (valsMidF z (ko + 1) ℓ h c t rs)) fun o =>
  frest (glueF ko t (fun y => φ (alphasF ℓ rs ++ y)) o.zv (o.qv.getD (kq + 1) 0) (posNF h c o.qv))
    (gluedCF (foldsCF ℓ rs σ) o.y (o.qv.getD (kq + 1) 0) t o.c)

/-- **A level with a next one**: from a fast form of an admitted weight, and the next level's twin. -/
theorem tw_mid (i ko ℓ h κ' ℓ' h' kq t c gQ A' : ℕ) (z : Bool) (hκ : 0 + ℓ' + κ' = ko + 1)
    (hko : ko + 1 < 64) (hℓ : 1 ≤ ℓ) (hℓ' : ℓ ≤ 64) (hh : h ≤ 64) (hh' : h' ≤ 64) (hc : 0 < c)
    (hch : c * h ≤ 128) (ht : t ≤ (kq + 1) * c) (hko20 : ko + 1 < 20) (hℓ8 : ℓ ≤ 8)
    (rest : Whir.Lad E2 Whir.WtE (2 ^ h') ℓ') (frest : (List FE2 → FE2) → FE2 → VF Bool)
    (hrest : ∀ w φ σ, WR κ' ℓ' w φ → TwinF id (Whir.ladP Whir.chalE2 rest w (FE2.toE2 σ)) (frest φ σ))
    (w : Whir.WtE.Wt (0 + ℓ)) (φ : List FE2 → FE2) (σ : FE2) (hw : WR (ko + 1) ℓ w φ) :
    TwinF id (Whir.ladP Whir.chalE2
      (.mid (Whir.midE i ko ℓ h κ' ℓ' h' kq t c gQ A' z hκ hko hℓ hℓ' hh hh' hc hch ht) rest) w (FE2.toE2 σ))
      (fMid i ko ℓ h h' kq t c gQ z frest φ σ) := by
  rw [Whir.ladP]
  unfold fMid
  have hps : ∀ qv : List FE2, (List.ofFn fun k => (Whir.qPos
      (Whir.midE i ko ℓ h κ' ℓ' h' kq t c gQ A' z hκ hko hℓ hℓ' hh hh' hc hch ht).L (qv.map FE2.toE2) k : ℕ)) =
      posListF h c t qv := fun qv => congrArg List.ofFn (funext fun k => posE2_val h c (kq + 1) t hc ht qv k)
  refine tw_bind (tw_rounds 10 ℓ) fun rs => tw_bind (tw_tail _ h' 32 i 18 gQ _ (posListF h c t) hps
    (valsMidF z (ko + 1) ℓ h c t rs) fun π hi qv r k => ?_) fun o => ?_
  · rw [valsMidF, getD_ofFn (t := t) _ k k.isLt]
    exact valsE_eq z h ℓ (ko + 1) hh hko20 hℓ8 rs hi _ (r.dec π) k (posNF h c qv k)
      (posE2_val h c (kq + 1) t hc ht qv k) _ (fun s => laneVal_eq z π r k s)
  · refine ladP_claim ?_ (hrest _ _ _ ⟨Whir.hglue_E hκ w hw.1 _ _, fun x => ?_⟩)
    · show Whir.gluedC (Whir.foldsC ℓ (rs.map RndF.dec) (FE2.toE2 σ)) (FE2.toE2 o.y)
        ((o.qv.map FE2.toE2).getD (kq + 1) 0) (fun k => FE2.toE2 (o.c.getD k 0)) = _
      rw [foldsC_eq, ← toE2_getD]
      exact gluedC_eq t _ _ _ o.c
    · exact wGlueE_eq κ' ℓ' ko t h hko20.le _ (fun y => φ (alphasF ℓ rs ++ y))
        (fun x => wFolds_val ℓ rs w φ (MA_le ℓ (ko + 1) w.2 hw.1.2) hw.2 x) _ o.zv rfl
        (o.qv.getD (kq + 1) 0) (toE2_getD _ _).symm (posNF h c o.qv)
        (fun k => posE2_val h c (kq + 1) t hc ht o.qv k) x

/-! ## The final level -/

/-- The final level's row check in the word field. -/
def finRowsOK (π : ByteArray) (rs : List RndF) (s qv : List FE2) (r : RowsF) : Bool :=
  decide (∀ k : Fin 18, foldRowF (FE2.ofK (kOfNat (posNF 17 7 qv k))) 4 rs (laneF false π r r.os[(k : ℕ)]?) 0 =
    fpolyEvalF 3 4 s (nwF (kOfNat (posNF 17 7 qv k))))

theorem finRowsOK_iff (π : ByteArray) (rs : List RndF) (s qv : List FE2) (r : RowsF) :
    finRowsOK π rs s qv r = true ↔ ∀ k : Fin Whir.fin18.Fv.t,
      Whir.fin18.fv (rs.map RndF.dec) (Whir.fPos Whir.fin18.Fv (qv.map FE2.toE2)) (r.dec π) k =
        (Whir.fin18.Fv.fpoly (s.map FE2.toE2) Whir.lane0).eval
          (Whir.fin18.Fv.dom (Whir.fPos Whir.fin18.Fv (qv.map FE2.toE2) k)) := by
  unfold finRowsOK
  rw [decide_eq_true_iff]
  refine forall_congr' fun k => ?_
  have hp := posE2_val 17 7 3 18 (by norm_num) (by norm_num) qv k
  show _ ↔ Whir.fvE false 17 4 (by norm_num) (rs.map RndF.dec)
      (Whir.posE2 17 7 3 18 (by norm_num) (by norm_num) (fun i => (qv.map FE2.toE2).getD i 0)) (r.dec π) k =
    (Whir.fpolyE 3 4 (s.map FE2.toE2) Whir.lane0).eval
      (Whir.domE 17 (by norm_num) (Whir.posE2 17 7 3 18 (by norm_num) (by norm_num)
        (fun i => (qv.map FE2.toE2).getD i 0) k))
  rw [fvE_eq false 17 4 (by norm_num) rs _ (r.dec π) k (posNF 17 7 qv k) hp _
    (fun s => laneVal_eq false π r k s), domE_eq 17 (by norm_num) _ _ hp,
    fpolyEval_eq 3 4 (by norm_num) (by norm_num) s]
  exact ⟨fun h => congrArg FE2.toE2 h, fun h => FE2.toE2_injective h⟩

/-- **The fast final level**: rounds, final polynomial, position group, openings, row check, tail sumcheck. -/
def fFin18 (φ : List FE2 → FE2) (σ : FE2) : VF Bool :=
  VF.bind (fRounds 10 4) fun rs => VF.bind (fE2Reads 12) fun s => VF.bind (fGrp 13 2) fun qv =>
  VF.bind (fQuery 4 (posListF 17 7 18 qv)) fun r => fun π tr =>
    if finRowsOK π rs s qv r then
      fSumP 2 (fun y => φ (alphasF 4 rs ++ y)) (mleLF 3 s) 3 [] (foldsCF 4 rs σ) π tr
    else none

theorem tw_fin (w : Whir.WtE.Wt (0 + 4)) (φ : List FE2 → FE2) (σ : FE2) (hw : WR 3 4 w φ) :
    TwinF id (Whir.ladP Whir.chalE2 (.fin Whir.fin18) w (FE2.toE2 σ)) (fFin18 φ σ) := by
  rw [Whir.ladP]
  unfold Whir.finP fFin18
  have hps : ∀ qv : List FE2, (List.ofFn fun k => (Whir.fPos Whir.fin18.Fv (qv.map FE2.toE2) k : ℕ)) =
      posListF 17 7 18 qv :=
    fun qv => congrArg List.ofFn (funext fun k => posE2_val 17 7 3 18 (by norm_num) (by norm_num) qv k)
  refine tw_bind (tw_rounds 10 4) fun rs => tw_bind (tw_readFs 12) fun s => tw_bind (tw_grp 13 2) fun qv => ?_
  rw [hps qv]
  refine tw_bindR (twin_query 4 (posListF 17 7 18 qv)) fun π r rows hr tr => ?_
  subst hr
  by_cases hok : finRowsOK π rs s qv r = true
  · rw [if_pos hok, if_pos ((finRowsOK_iff π rs s qv r).mp hok)]
    exact tw_sumP 2 (Whir.wFolds Whir.WtE 4 (rs.map RndF.dec) w).2 (Whir.mleL (Whir.msgOf 3 (s.map FE2.toE2)))
      (fun y => φ (alphasF 4 rs ++ y)) (mleLF 3 s) (wFolds_val 4 rs w φ (MA_le 4 3 w.2 hw.1.2) hw.2)
      (fun x => (toE2_mleLF 3 s x).symm) 3 [] (foldsCF 4 rs σ) [] _ rfl (foldsC_eq 4 rs σ) π tr
  · rw [if_neg hok, if_neg (fun h => hok ((finRowsOK_iff π rs s qv r).mpr h)), replayP_fail]
    exact Option.Rel.none

/-! ## The deployed opening -/

theorem tw_L3 (w : Whir.WtE.Wt (0 + 4)) (φ : List FE2 → FE2) (σ : FE2) (hw : WR 7 4 w φ) :
    TwinF id (Whir.ladP Whir.chalE2 (.mid Whir.mid3 (.fin Whir.fin18)) w (FE2.toE2 σ))
      (fMid 3 6 4 18 17 2 21 7 17 false fFin18 φ σ) :=
  tw_mid 3 6 4 18 3 4 17 2 21 7 17 (1548 - 4) false (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (.fin Whir.fin18) fFin18 tw_fin w φ σ hw

theorem tw_L2 (w : Whir.WtE.Wt (0 + 4)) (φ : List FE2 → FE2) (σ : FE2) (hw : WR 11 4 w φ) :
    TwinF id (Whir.ladP Whir.chalE2 (.mid Whir.mid2 (.mid Whir.mid3 (.fin Whir.fin18))) w (FE2.toE2 σ))
      (fMid 2 10 4 19 18 4 28 6 18 false (fMid 3 6 4 18 17 2 21 7 17 false fFin18) φ σ) :=
  tw_mid 2 10 4 19 7 4 18 4 28 6 18 (6525 - 4) false (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    _ _ tw_L3 w φ σ hw

theorem tw_L1 (w : Whir.WtE.Wt (0 + 4)) (φ : List FE2 → FE2) (σ : FE2) (hw : WR 15 4 w φ) :
    TwinF id (Whir.ladP Whir.chalE2 (.mid Whir.mid1 (.mid Whir.mid2 (.mid Whir.mid3 (.fin Whir.fin18)))) w
      (FE2.toE2 σ))
      (fMid 1 14 4 20 19 7 45 6 17 false
        (fMid 2 10 4 19 18 4 28 6 18 false (fMid 3 6 4 18 17 2 21 7 17 false fFin18)) φ σ) :=
  tw_mid 1 14 4 20 11 4 19 7 45 6 17 (34227 - 4) false (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    _ _ tw_L2 w φ σ hw

/-- A batched claim from a weight and a value in the word field (`FClaim.dec`'s form). -/
def clDec (f : List FE2 → FE2) (v : FE2) : (List E2 → E2) × E2 :=
  (fun x => FE2.toE2 (f (x.map FE2.ofE2)), FE2.toE2 v)

/-- The first 25 entries of a word-field list, zero-padded (W1's `pad25` in the word field). -/
def padF25 (y : List FE2) : List FE2 := List.ofFn fun i : Fin 25 => y.getD i 0

theorem pad25_map (x : List FE2) : Whir.pad25 (x.map FE2.toE2) = (padF25 x).map FE2.toE2 :=
  List.ext_getElem (by simp [Whir.pad25, padF25]) fun i _ _ => by
    simp only [Whir.pad25, padF25, List.getElem_ofFn, List.getElem_map, List.getD_eq_getElem?_getD,
      List.getElem?_map]
    cases x[i]? <;> simp [FE2.toE2_zero]

/-- A table affine in its first `n` variables stays so when read on the first `n` entries, zero-padded. -/
theorem MA_ofFn_getD' : ∀ (n : ℕ) (f : List E2 → E2), Whir.MA n f →
    Whir.MA n fun y => f (List.ofFn fun i : Fin n => y.getD i 0)
  | 0, _, _ => trivial
  | n + 1, f, h => by
    have hc : ∀ (X : E2) (x : List E2), (List.ofFn fun i : Fin (n + 1) => (X :: x).getD i 0) =
        X :: List.ofFn fun i : Fin n => x.getD i 0 := fun X x => by simp [List.ofFn_succ]
    refine ⟨fun X x => ?_, fun X => ?_⟩
    · simp only [hc]
      exact h.1 X _
    · simp only [hc]
      exact MA_ofFn_getD' n (fun y => f (X :: y)) (h.2 X)

/-- **The fast deployed opening** of a claim given in the word field (INT3: the claim is read on the first 25
entries, zero-padded, as W1's `w₀` reads it through `pad25`). -/
def fWhir18 (f : List FE2 → FE2) (v : FE2) : VF Bool :=
  fMid 0 18 6 21 20 18 110 6 19 true
    (fMid 1 14 4 20 19 7 45 6 17 false
      (fMid 2 10 4 19 18 4 28 6 18 false (fMid 3 6 4 18 17 2 21 7 17 false fFin18)))
    (fun y => f ((padF25 y).drop 6 ++ (padF25 y).take 6)) v

/-- **`fWhir18` is a fast twin of W1's deployed opening `whirP18`**, for a claim whose level-0 table `w₀` (the
weight read on the first 25 entries, zero-padded, rotated) is affine in each of its 25 variables (`wokE`'s `MA`;
`Whir.MA_w₀` gives it from S's `Multiaffine 25`). -/
theorem tw_whirP18w (f : List FE2 → FE2) (v : FE2) (hma : Whir.MA 25 (Whir.w₀ (clDec f v)).2) :
    TwinF id (Whir.whirP18 (clDec f v)) (fWhir18 f v) := by
  have hval : ∀ x : List FE2, (Whir.w₀ (clDec f v)).2 (x.map FE2.toE2) =
      FE2.toE2 ((fun y => f ((padF25 y).drop 6 ++ (padF25 y).take 6)) x) := fun x => by
    show FE2.toE2 (f (((Whir.pad25 (x.map FE2.toE2)).drop 6 ++
      (Whir.pad25 (x.map FE2.toE2)).take 6).map FE2.ofE2)) = _
    rw [pad25_map]
    simp only [← List.map_drop, ← List.map_take, ← List.map_append, List.map_map, Function.comp_def,
      FE2.ofE2_toE2, List.map_id']
  exact tw_mid 0 18 6 21 15 4 20 18 110 6 19 (188173 - 4) true (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) _ _ tw_L1 (Whir.w₀ (clDec f v)) _ v ⟨⟨rfl, hma⟩, hval⟩

/-- **`fWhir18` is a fast twin of W1's deployed opening `whirP18`**, for a claim whose weight is affine in each
of its 25 variables (in `w₀`'s rotated order; `whirSpec18`'s hypothesis). -/
theorem tw_whirP18 (f : List FE2 → FE2) (v : FE2)
    (hma : Whir.MA 25 fun y => (clDec f v).1 (y.drop 6 ++ y.take 6)) :
    TwinF id (Whir.whirP18 (clDec f v)) (fWhir18 f v) :=
  tw_whirP18w f v (MA_ofFn_getD' 25 _ hma)

end Lvm6.V
