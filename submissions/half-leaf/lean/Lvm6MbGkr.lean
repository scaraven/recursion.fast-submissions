-- New for lvm6 Y1 (2026-11-22): the GKR walk at `E2` with grinds (`gkrStepG`, `gkrLayersG`,
-- `verifyGkrGrandProductsG` of `Lvm6MbProg`) in the doom calculus: the twins of season 1's `stepSpec`,
-- `gkrLayersSpec` (`LvmFrontBusGkr`) and of the first part of `gkrSpec` (`LvmM3Fid`), every challenge ground.
import Lvm6MbSample

/-!
# The grand-product walk at `E2`

The walk's doom is stated on the grand product's relations (`Gkr.layerRel`, `Gkr.familyT`, `Gkr.childRelT`,
`Gkr.stepOutT`, `Gkr.relOut`, generic in the field), at `F = E2`, over oracles `∀ i, O i` of the first commitment
(`HDoom cands`), the leaves and riders parameters. Every group opens with a nonce, so every lead is `0` and every group
is bounded by its own escape plus the follower's lead:

* the combiner `λ` (`e2Sample gLam`): at most `2` bad values per oracle (`Gkr.card_lambda_le`): `L₀ · errG gLam 2`;
* each round (`sumcheckE2 gRd …` in equality mode, `wireSumcheckSpecG`): at most `2^ρ ≤ 4` bad values per oracle
  (`SumcheckRound.card_badChallenge_le`): `L₀ · errG gRd 4 ≤ L₀ · errG gRd 5`;
* the point `y` (`e2SampleN gy ρ`, one group, `Lvm6MbSample.e2SampleNSpecHCount`): the `ρ` combination challenges
  each restore `childRelT` at one value at most (`Gkr.card_interpNext_le`), so at most `ρ · |E2|^(ρ − 1)` bad tuples
  (`card_seq_le`): `L₀ · errG gy ρ`, `ρ ≤ 2` (priced `errG gY 2`, the last step `errG gYl 4`).

**Headline results** (consumed by the Bus agent):

* **`stepSpecG`**: one step, from `StepPreG` (doom on `layerRel m`) to `StepPostG` (doom on `stepOutT`);
* **`gkrLayersSpecG`**: the walk with `n` layers left at layer `m`, from `LayersPreG n m` to `LayersPreG 0 μ`
  (doom on `Gkr.relOut`), lead `walkLead n T`;
* **`gkrSpecG`**: `verifyGkrGrandProductsG μ`, from doom on any relation `R` at `x` that the roots reflect into
  (`hroots`: a nonzero count root in `Gkr.relIn` gives `R`; the Bus agent's `roots_reflect` twin) to `GkrPostG`
  (count root `0`, or doom on `Gkr.relOut` at the returned point and values), lead `0`, follower `T`.
-/

set_option autoImplicit false

namespace Lvm6.Mb

open LeanVM.Parameters LeanVM.Protocol LeanVM.Protocol.Compile LeanVM.Protocol.Verifier
open LeanVM.Protocol.EndToEnd.Front
open Lvm.E2V
open CompPoly CMlPolynomialEval
open scoped ENNReal

/-! ## The wire's arithmetic at `E2` is the protocol's -/

/-- The vector of `m` coordinates a list gives at `E2`, `0` past its end. -/
def vecOfG (m : ℕ) (l : List E2) : Vector E2 m := Vector.ofFn fun i ↦ l.getD i 0

theorem vecOfG_toList {m : ℕ} (v : Vector E2 m) : vecOfG m v.toList = v := by
  apply Vector.ext
  intro i hi
  simp [vecOfG]

theorem toList_vecOfG {n : ℕ} (l : List E2) (hlen : l.length = n) : (vecOfG n l).toList = l := by
  subst hlen
  apply List.ext_getElem (by simp)
  intro i h1 h2
  simp [vecOfG]

/-- Three values as the protocol's family of three. -/
def valuesFnG (vals : List E2) : Fin 3 → E2 := fun t ↦ vals.getD t 0

theorem polyEvalF_eq_powerBatch (vals : List E2) (hlen : vals.length = 3) (l : E2) :
    polyEvalF vals l = powerBatch (valuesFnG vals) l := by
  rw [polyEvalF_eq_sum, hlen, powerBatch, ← Fin.sum_univ_eq_sum_range]
  rfl

theorem prodF_eq_prod (l : List E2) : prodF l = l.prod := by
  unfold prodF
  rw [List.prod_eq_foldl]

theorem prod_eq_prod_vecOfG {n : ℕ} (l : List E2) (hlen : l.length = n) :
    l.prod = ∏ c : Fin n, (vecOfG n l)[c] := by
  subst hlen
  simp only [vecOfG, Fin.getElem_fin, Vector.getElem_ofFn]
  rw [← List.prod_ofFn]
  congr 1
  apply List.ext_getElem (by simp)
  intro i h1 h2
  simp

section State

variable {X : Type} (data : X)

/-- The protocol's layer statement of the wire's state at `E2`: the public data, the point, the three values. -/
def layerStmtOfG (m : ℕ) (s : GkrStateG) : Gkr.LayerStmt X E2 3 m :=
  (data, (vecOfG m s.point, valuesFnG s.values))

/-- The descendants' message of the wire's three lists. -/
def childrenOfG (ρ : ℕ) (children : List (List E2)) : Fin 3 → CMlPolynomialEval E2 ρ :=
  fun t ↦ vecOfG (2 ^ ρ) (children.getD t [])

theorem vecOfG_append {ρ m : ℕ} (y x : List E2) (hy : y.length = ρ) :
    vecOfG (m + ρ) (y ++ x) = Vector.cast (Nat.add_comm ρ m) (vecOfG ρ y ++ vecOfG m x) := by
  apply Vector.ext
  intro k hk
  simp only [vecOfG, Vector.getElem_ofFn, Vector.getElem_cast, Vector.getElem_append]
  split_ifs with h
  · simp [List.getD_eq_getElem?_getD, List.getElem?_append_left (show k < y.length by omega)]
  · simp [List.getD_eq_getElem?_getD, List.getElem?_append_right (show y.length ≤ k by omega), hy]

end State

/-! ## `multilinear_eval` at `E2` is the multilinear extension -/

theorem length_foldPairsF (r : E2) (l : List E2) : (foldPairsF r l).length = l.length / 2 := by
  induction l using foldPairsF.induct with
  | case1 a b rest ih => simp [foldPairsF, ih]; omega
  | case2 l h =>
    rcases l with _ | ⟨a, _ | ⟨b, rest⟩⟩
    · simp [foldPairsF]
    · simp [foldPairsF]
    · exact absurd rfl (h a b rest)

theorem getElem_foldPairsF (r : E2) (l : List E2) (i : ℕ) (hi : i < (foldPairsF r l).length) :
    (foldPairsF r l)[i] = l[2 * i]'(by rw [length_foldPairsF] at hi; omega) * (1 + r) +
      l[2 * i + 1]'(by rw [length_foldPairsF] at hi; omega) * r := by
  induction l using foldPairsF.induct generalizing i with
  | case1 a b rest ih =>
    rcases i with _ | i
    · simp [foldPairsF]
    · simp only [foldPairsF, List.getElem_cons_succ]
      rw [ih i (by simp [foldPairsF] at hi; omega)]
      simp only [show 2 * (i + 1) = 2 * i + 1 + 1 by omega, List.getElem_cons_succ]
  | case2 l h =>
    exfalso
    rcases l with _ | ⟨a, _ | ⟨b, rest⟩⟩
    · simp [foldPairsF] at hi
    · simp [foldPairsF] at hi
    · exact h a b rest rfl

theorem foldPairsF_toList {n : ℕ} (v : Vector E2 (2 ^ (n + 1))) (r : E2) :
    foldPairsF r v.toList = (evalMleLayer v r).toList := by
  apply List.ext_getElem
  · simp [length_foldPairsF, pow_succ]
  · intro i h1 h2
    rw [getElem_foldPairsF]
    simp only [Vector.getElem_toList]
    have hi : i < 2 ^ n := by simpa using h2
    have := evalMleLayer_get v r ⟨i, hi⟩
    simp only [Vector.get_eq_getElem] at this
    rw [this, CharTwo.sub_eq_add]
    ring

/-- **`multilinear_eval` at `E2` is the multilinear extension** (`multilinearEval_eq_evalMle`'s twin). -/
theorem multilinearEvalF_eq_evalMle {n : ℕ} (v : Vector E2 (2 ^ n)) (x : Vector E2 n) :
    multilinearEvalF v.toList x.toList = evalMle v x := by
  induction n with
  | zero =>
    rw [evalMle_zero]
    have hx : x.toList = [] := by simp
    rw [hx]
    have : v.toList = [v.get ⟨0, by norm_num⟩] := by
      apply List.ext_getElem (by simp)
      intro i h1 h2
      simp only [List.length_cons, List.length_nil] at h2
      obtain rfl : i = 0 := by omega
      simp [Vector.get_eq_getElem]
    rw [this]
    rfl
  | succ n ih =>
    rw [Vector.toList_eq_head_cons x, evalMle_succ, ← ih]
    show multilinearEvalF (foldPairsF x.head v.toList) x.tail.toList = _
    rw [foldPairsF_toList]

section State2

variable {X : Type} (data : X)

/-- **The wire's step output is the protocol's interpolated statement** at `E2`. -/
theorem interpDone_eqG {ρ m : ℕ} (x y : List E2) (children : List (List E2))
    (hy : y.length = ρ) (hc : children.length = 3) (hch : ∀ t ∈ children, t.length = 2 ^ ρ) :
    Gkr.interpDone 3 ρ m (((data, (vecOfG m x, childrenOfG ρ children)), vecOfG ρ y)) =
      layerStmtOfG data (m + ρ) ⟨children.map (multilinearEvalF · y), y ++ x⟩ := by
  refine Prod.ext rfl (Prod.ext (vecOfG_append y x hy).symm (funext fun t ↦ ?_))
  show evalMle (childrenOfG ρ children t) (vecOfG ρ y) = (children.map (multilinearEvalF · y)).getD t 0
  have ht : (t : ℕ) < children.length := by rw [hc]; exact t.isLt
  rw [List.getD_eq_getElem _ _ (by simpa using ht), List.getElem_map, childrenOfG,
    List.getD_eq_getElem _ _ ht, ← multilinearEvalF_eq_evalMle,
    toList_vecOfG _ (hch _ (List.getElem_mem ht)), toList_vecOfG _ hy]

/-- The wire's check of the descendants at `E2` is the protocol's. -/
theorem combineCheck_eqG {ρ m : ℕ} (st : SumcheckRound.Stmt (Gkr.LayerX X E2 3 m) E2 m)
    (children : List (List E2)) (hc : children.length = 3) (hch : ∀ t ∈ children, t.length = 2 ^ ρ)
    (heq : st.2.2 = polyEvalF (children.map prodF) st.1.2) :
    Gkr.combineCheck 3 ρ m st (childrenOfG ρ children) = true := by
  rw [Gkr.combineCheck, decide_eq_true_eq, heq, polyEvalF_eq_powerBatch _ (by simp [hc])]
  congr 1
  funext t
  have ht : (t : ℕ) < children.length := by rw [hc]; exact t.isLt
  show (children.map prodF).getD t 0 = ∏ c : Fin (2 ^ ρ), (vecOfG (2 ^ ρ) (children.getD t []))[c]
  rw [List.getD_eq_getElem _ _ (by simpa using ht), List.getElem_map, prodF_eq_prod,
    List.getD_eq_getElem _ _ ht, prod_eq_prod_vecOfG _ (hch _ (List.getElem_mem ht))]

end State2

/-! ## Wire messages at `E2` -/

/-- A wire round polynomial at `E2` read as the protocol's message: its first `d + 1` coefficients. -/
def toMessageG (d : ℕ) (msg : List E2) : SumcheckRound.Message E2 d := Vector.ofFn fun i ↦ msg.getD i 0

theorem evaluate_toMessageG {d : ℕ} (msg : List E2) (hlen : msg.length = d + 1) (x : E2) :
    SumcheckRound.evaluate d (toMessageG d msg) x = polyEvalF msg x := by
  rw [polyEvalF_eq_sum, hlen, SumcheckRound.evaluate, ← Fin.sum_univ_eq_sum_range]
  simp [toMessageG]

/-- The weighted domain of an equality-mode round against `r`: weights `1 − r, r` on `0, 1`. -/
def eqDomainG (r : E2) : SumcheckRound.WeightedDomain E2 := [(0, 1 - r), (1, r)]

/-- **The equality-mode wire round at `E2` passes the protocol's check**. -/
theorem weightedSum_eqG {d : ℕ} (claim r : E2) (tail : List E2) (hlen : tail.length + 1 = d + 1) :
    SumcheckRound.weightedSum d (eqDomainG r) (toMessageG d ((claim + r * sumF tail) :: tail)) = claim := by
  have hl : ((claim + r * sumF tail) :: tail).length = d + 1 := by simp; omega
  simp only [SumcheckRound.weightedSum, eqDomainG, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    add_zero]
  rw [evaluate_toMessageG _ hl, evaluate_toMessageG _ hl, polyEvalF_zero_cons, polyEvalF_one, sumF_eq_sum]
  simp only [List.sum_cons]
  linear_combination (r * tail.sum) * (CharTwo.two_eq_zero (R := E2))

/-! ## Reads at `E2` on any property reads keep -/

section Reads

variable {εmax T : ℝ≥0∞}

/-- An `E2` scalar, its value's postcondition from the read's. -/
noncomputable def e2ReadSpecQ {Pre : List Ev → Prop} (Q : E2 → List Ev → Prop)
    (hQ : ∀ h₀ x, Pre h₀ → Q (e2OfE x) (h₀ ++ [Ev.read x])) (hT : T ≤ εmax) :
    Spec e2Read Pre Q εmax 0 T :=
  (Spec.readE (Post := fun x h ↦ Q (e2OfE x) h) hQ hT).bind' fun x ↦ Spec.ret (Post := Q) (e2OfE x)

/-- `n + 1` `E2` scalars keep a property reads keep; lead `0`. -/
noncomputable def e2ReadsSpecP (P : List Ev → Prop) (hP : ∀ h x, P h → P (h ++ [Ev.read x]))
    (hT : T ≤ εmax) : (n : ℕ) → Spec (e2Reads (n + 1)) P (fun xs h ↦ xs.length = n + 1 ∧ P h) εmax 0 T
  | 0 => (e2ReadSpecQ (Pre := P) (fun _ h ↦ P h) (fun h x hp ↦ hP h x hp) hT).bind' fun x ↦
      (Spec.ret (Post := fun xs h ↦ xs = [] ∧ P h) []).mono
        (fun _ hd ↦ ⟨rfl, hd⟩) (fun _ _ h ↦ h) le_rfl le_rfl le_rfl |>.bind' fun xs ↦
          (Spec.ret (x :: xs)).mono (fun _ h ↦ ⟨by simp [h.1], h.2⟩) (fun _ _ h ↦ h) le_rfl le_rfl le_rfl
  | n + 1 => (e2ReadSpecQ (Pre := P) (T := 0) (fun _ h ↦ P h) (fun h x hp ↦ hP h x hp) zero_le).bind' fun x ↦
        (e2ReadsSpecP P hP hT n).bind' fun xs ↦
          (Spec.ret (x :: xs)).mono (fun _ h ↦ ⟨by simp [h.1], h.2⟩) (fun _ _ h ↦ h) le_rfl le_rfl le_rfl

end Reads

/-! ## The sumcheck at `E2` in equality mode, on doom -/

section Sumcheck

variable {ι : Type} {O : ι → Type} {X : Type} {d : ℕ} (Φ : SumcheckRound.Family E2 X O Unit d)
  (cands : Word → Set (∀ i, O i))

/-- What a round's wire polynomial gives at `E2`: `d + 1` coefficients that pass the check at the running claim,
and doom after the protocol's message. -/
def RoundPolyPostG (j : ℕ) (s : SumcheckRound.Stmt X E2 j) (r : E2) (msg : List E2) (h : List Ev) : Prop :=
  msg.length = d + 1 ∧ SumcheckRound.weightedSum d (eqDomainG r) (toMessageG d msg) = s.2.2 ∧
    HDoom cands (SumcheckRound.relMid Φ j) (s, toMessageG d msg) h

/-- The message's doom from the stage's. -/
theorem hdoom_relMidG {j : ℕ} {s : SumcheckRound.Stmt X E2 j} {h : List Ev}
    (hD : HDoom cands (SumcheckRound.rel Φ j) s h) (q : SumcheckRound.Message E2 d) :
    HDoom cands (SumcheckRound.relMid Φ j) (s, q) h := by
  obtain ⟨W, hW, hR⟩ := hD
  exact ⟨W, hW, say_keep (fun _ hout ↦ hout.1) hR⟩

variable {εmax T : ℝ≥0∞}

/-- **A round's wire polynomial at `E2`** (equality mode against `r`): reading it keeps doom, and it returns the
protocol's message, which passes the check and is doomed. Lead `0`. -/
noncomputable def roundSpecG (hd : 1 ≤ d) (j : ℕ) (s : SumcheckRound.Stmt X E2 j) (r : E2) (hT : T ≤ εmax) :
    Spec (roundPolyE2 (d + 1) s.2.2 (some r)) (HDoom cands (SumcheckRound.rel Φ j) s)
      (RoundPolyPostG Φ cands j s r) εmax 0 T :=
  Spec.congr (p := e2Reads (d - 1 + 1) >>= fun tail ↦ pure ((s.2.2 + r * sumF tail) :: tail)) (by
      rw [show d - 1 + 1 = d + 1 - 1 by omega]; rfl) <|
    (e2ReadsSpecP (HDoom cands (SumcheckRound.rel Φ j) s) (fun _ _ hp ↦ hp.append _) hT (d - 1)).bind' fun tail ↦
      (Spec.ret (Post := RoundPolyPostG Φ cands j s r) ((s.2.2 + r * sumF tail) :: tail)).mono
        (fun _ hp ↦ ⟨by simp [hp.1]; omega, weightedSum_eqG _ _ _ (by rw [hp.1]; omega),
          hdoom_relMidG Φ cands hp.2 _⟩) (fun _ _ h ↦ h) le_rfl le_rfl le_rfl

/-- A specification from a precondition that cannot hold. -/
noncomputable def specOfFalseG {α : Type} {p : VerifierProgram α} {Pre : List Ev → Prop}
    {Post : α → List Ev → Prop} {L T' : ℝ≥0∞} (h : ∀ h, Pre h → False) : Spec p Pre Post εmax L T' :=
  (Spec.dead (p := p) (Post := Post) (εmax := εmax) (L := L) (T := T')).mono (fun h' hp ↦ h h' hp)
    (fun _ _ h ↦ h) le_rfl le_rfl le_rfl

/-- **A round's ground challenge at `E2`**: from a doomed message that passes the check, doom on the next stage; at
most `d` bad values per oracle (`card_badChallenge_le`), the group `L₀ · errG g d + T ≤ εmax`. -/
noncomputable def roundChallengeSpecG {m : ℕ} (H : Φ.Consistent m) (S : Φ.Sound m) {L₀ : ℕ}
    (hfin : ∀ W, (cands W).Finite) (hcard : ∀ W, (cands W).ncard ≤ L₀) (j : ℕ) (hj : j < m)
    (s : SumcheckRound.Stmt X E2 j) (r : E2) (hw : Φ.weight s.1 j = eqDomainG r) (msg : List E2) {g : ℕ}
    (hg : g ≤ 64) (he : (L₀ : ℝ≥0∞) * errG g d + T ≤ εmax) :
    Spec (e2Sample g) (RoundPolyPostG Φ cands j s r msg)
      (fun c h ↦ HDoom cands (SumcheckRound.rel Φ (j + 1)) (s.1, (s.2.1.push c, polyEvalF msg c)) h) εmax 0 T :=
  if hm : msg.length = d + 1 ∧ SumcheckRound.weightedSum d (eqDomainG r) (toMessageG d msg) = s.2.2 then
    (e2SampleSpecH hfin hcard (SumcheckRound.relMid Φ j) (s, toMessageG d msg) (SumcheckRound.rel Φ (j + 1))
      (fun c ↦ (s.1, (s.2.1.push c, polyEvalF msg c))) hg (fun o ho ↦ by
        classical
        have hc : SumcheckRound.check j Φ.weight s (toMessageG d msg) = true := by
          rw [SumcheckRound.check, hw, hm.2]
          exact decide_eq_true rfl
        refine le_trans (Nat.card_mono (Set.toFinite _) fun y hy ↦ ?_)
          (SumcheckRound.card_badChallenge_le j Φ H S hj (s, toMessageG d msg) o hc)
        refine ⟨(), ho, ?_⟩
        simp only [SumcheckRound.next, evaluate_toMessageG msg hm.1]
        exact hy) he).mono (fun _ hp ↦ hp.2.2) (fun _ _ h ↦ h) le_rfl le_rfl le_rfl
  else specOfFalseG fun _ hp ↦ hm ⟨hp.1, hp.2.1⟩

/-- What the wire's sumcheck at `E2` gives from stage `j`: doom on its last stage `m`. -/
def SumcheckPostG (x : X) (m : ℕ) {j : ℕ} (cv : Vector E2 j) (r : List E2 × E2) (h : List Ev) : Prop :=
  j + r.1.length = m ∧ HDoom cands (SumcheckRound.rel Φ m) (x, (vecOfG m (cv.toList ++ r.1), r.2)) h

/-- **The wire's sumcheck at `E2` in equality mode** against `rs`, from stage `j`: from doom on stage `j` to doom on
the last stage `m`; each ground challenge at `L₀ · errG g d`, every group a nonce, so lead `T` (`0` with a round). -/
noncomputable def wireSumcheckSpecG {m : ℕ} (H : Φ.Consistent m) (S : Φ.Sound m) {L₀ : ℕ}
    (hfin : ∀ W, (cands W).Finite) (hcard : ∀ W, (cands W).ncard ≤ L₀) (hd : 1 ≤ d) {g : ℕ} (hg : g ≤ 64)
    (he : (L₀ : ℝ≥0∞) * errG g d + T ≤ εmax) (x : X) :
    (rs : List E2) → (j : ℕ) → (cv : Vector E2 j) → (claim : E2) → j + rs.length = m →
      (∀ k (hk : k < rs.length), Φ.weight x (j + k) = eqDomainG rs[k]) →
      Spec (sumcheckE2 g claim (d + 1) (rs.map some)) (HDoom cands (SumcheckRound.rel Φ j) (x, (cv, claim)))
        (SumcheckPostG Φ cands x m cv) εmax T T
  | [], j, cv, claim, hj, _ =>
    (Spec.ret (Post := SumcheckPostG Φ cands x m cv) ([], claim)).mono (fun h hp ↦ by
      obtain rfl : m = j := by simpa using hj.symm
      exact ⟨rfl, by simpa [vecOfG_toList] using hp⟩) (fun _ _ h ↦ h) le_rfl le_rfl le_rfl
  | r :: rs, j, cv, claim, hj, hw =>
    ((roundSpecG (T := 0) Φ cands hd j (x, (cv, claim)) r zero_le).bind' fun msg ↦
      (roundChallengeSpecG Φ cands H S hfin hcard j (by simp at hj; omega) (x, (cv, claim)) r
        (hw 0 (by simp)) msg hg he).bind' fun c ↦
        (wireSumcheckSpecG H S hfin hcard hd hg he x rs (j + 1) (cv.push c) (polyEvalF msg c)
          (by simp at hj; omega)
          (fun k hk ↦ by
            have h := hw (k + 1) (by simp; omega)
            rwa [show j + (k + 1) = j + 1 + k by omega] at h)).bind'
          fun ⟨pt, fin⟩ ↦ (Spec.ret (Post := SumcheckPostG Φ cands x m cv) (c :: pt, fin)).mono
            (fun h hp ↦ ⟨by have := hp.1; dsimp only at this ⊢; simp only [List.length_cons]; omega,
              by simpa [Vector.toList_push] using hp.2⟩)
            (fun _ _ h ↦ h) le_rfl le_rfl le_rfl).mono (fun _ h ↦ h) (fun _ _ h ↦ h) le_rfl zero_le le_rfl

end Sumcheck

/-! ## The point's group: a count -/

/-- A sum over `k + 1` coordinates is a sum over the first and the rest (in `ℕ`). -/
theorem sum_fin_succ_funG (k : ℕ) (f : (Fin (k + 1) → E2) → ℕ) :
    ∑ w, f w = ∑ c : E2, ∑ v : Fin k → E2, f (Fin.cons c v) := by
  rw [← (Fin.consEquiv fun _ ↦ E2).sum_comp, Fintype.sum_prod_type]
  rfl

/-- **The count of a sequence of restorations**: when a relation on the challenges so far, broken, is restored by
one more challenge at one value at most, a broken relation is restored by `k` more at `≤ k · |E2|^(k − 1)` tuples. -/
theorem card_seq_le (R : (i : ℕ) → Vector E2 i → Prop)
    (hR : ∀ i (v : Vector E2 i), ¬ R i v → Nat.card {c // R (i + 1) (v.push c)} ≤ 1) :
    ∀ (k i : ℕ) (v : Vector E2 i) (n : ℕ), n = i + k → ¬ R i v →
      Nat.card {w : Fin k → E2 // R n (vecOfG n (v.toList ++ List.ofFn w))} ≤ k * Fintype.card E2 ^ (k - 1)
  | 0, i, v, n, hn, hv => by
    have : IsEmpty {w : Fin 0 → E2 // R n (vecOfG n (v.toList ++ List.ofFn w))} :=
      ⟨fun w ↦ hv (by have h2 := w.2; subst hn; simpa [vecOfG_toList] using h2)⟩
    rw [Nat.card_of_isEmpty]
    exact Nat.zero_le _
  | k + 1, i, v, n, hn, hv => by
    classical
    have ih := fun c (hc : ¬ R (i + 1) (v.push c)) ↦
      card_seq_le R hR k (i + 1) (v.push c) n (by omega) hc
    rw [natCard_subtype_eq_card_filter, Finset.card_filter, sum_fin_succ_funG]
    have hrow : ∀ c : E2, ∑ w' : Fin k → E2,
        (if R n (vecOfG n (v.toList ++ List.ofFn (Fin.cons c w' : Fin (k + 1) → E2))) then 1 else 0) ≤
        if R (i + 1) (v.push c) then Fintype.card E2 ^ k else k * Fintype.card E2 ^ (k - 1) := by
      intro c
      have hl : ∀ w' : Fin k → E2, v.toList ++ List.ofFn (Fin.cons c w' : Fin (k + 1) → E2) =
          (v.push c).toList ++ List.ofFn w' := fun w' ↦ by simp [List.ofFn_succ, Vector.toList_push]
      simp_rw [hl]
      split_ifs with hc
      · calc ∑ w' : Fin k → E2, (if R n (vecOfG n ((v.push c).toList ++ List.ofFn w')) then 1 else 0)
            ≤ ∑ _w' : Fin k → E2, 1 := Finset.sum_le_sum fun _ _ ↦ by split_ifs <;> simp
          _ = Fintype.card E2 ^ k := by simp
      · have := ih c hc
        rw [natCard_subtype_eq_card_filter, Finset.card_filter] at this
        exact this
    have hB : (Finset.univ.filter fun c ↦ R (i + 1) (v.push c)).card ≤ 1 := by
      rw [← natCard_subtype_eq_card_filter]
      exact hR i v hv
    calc ∑ c : E2, ∑ w' : Fin k → E2,
          (if R n (vecOfG n (v.toList ++ List.ofFn (Fin.cons c w' : Fin (k + 1) → E2))) then 1 else 0)
        ≤ ∑ c : E2, (if R (i + 1) (v.push c) then Fintype.card E2 ^ k else k * Fintype.card E2 ^ (k - 1)) :=
          Finset.sum_le_sum fun c _ ↦ hrow c
      _ ≤ ∑ c : E2, ((if R (i + 1) (v.push c) then Fintype.card E2 ^ k else 0) +
            k * Fintype.card E2 ^ (k - 1)) :=
          Finset.sum_le_sum fun c _ ↦ by split_ifs <;> simp
      _ = (Finset.univ.filter fun c ↦ R (i + 1) (v.push c)).card * Fintype.card E2 ^ k +
            Fintype.card E2 * (k * Fintype.card E2 ^ (k - 1)) := by
          rw [Finset.sum_add_distrib, Finset.sum_ite, Finset.sum_const, Finset.sum_const_zero, add_zero,
            smul_eq_mul, Finset.sum_const, Finset.card_univ, smul_eq_mul]
      _ ≤ 1 * Fintype.card E2 ^ k + k * Fintype.card E2 ^ k := by
          refine Nat.add_le_add (Nat.mul_le_mul_right _ hB) ?_
          rcases k with _ | k
          · simp
          · rw [Nat.add_sub_cancel, pow_succ]
            exact le_of_eq (by ring)
      _ = (k + 1) * Fintype.card E2 ^ (k + 1 - 1) := by rw [Nat.add_sub_cancel]; ring

/-! ## A layer step -/

section Step

variable {ι : Type} {O : ι → Type} {X : Type} {μ : ℕ}
  (leaves : X → (∀ i, O i) → Fin 3 → CMlPolynomialEval E2 μ)
  (riders : X → (∀ i, O i) → List (Σ τ : Fin (μ + 1), CMlPolynomialEval E2 τ))
  (cands : Word → Set (∀ i, O i)) (data : X) {ρ m : ℕ}
  (T : Gkr.RiderTrack μ riders ρ m)

/-- The doom before a step at `E2`: doom on the layer relation at the wire's state. -/
def StepPreG (s : GkrStateG) (h : List Ev) : Prop :=
  s.point.length = m ∧ s.values.length = 3 ∧
    HDoom cands (Gkr.layerRel 3 μ leaves riders m) (layerStmtOfG data m s) h

/-- The doom after a step at `E2`: doom on the step's output relation at the wire's new state. -/
def StepPostG (s : GkrStateG) (h : List Ev) : Prop :=
  s.point.length = m + ρ ∧ s.values.length = 3 ∧
    HDoom cands (Gkr.stepOutT 3 μ leaves riders ρ m T) (layerStmtOfG data (m + ρ) s) h

/-- The layer's family has the wire's equality-mode domains. -/
theorem weights_eq_eqDomainG (s : GkrStateG) (hs : s.point.length = m) (l : E2) (k : ℕ)
    (hk : k < s.point.length) :
    Gkr.weights (F := E2) (X := X) 3 m (layerStmtOfG data m s, l) (0 + k) = eqDomainG s.point[k] := by
  have hk' : k < m := by omega
  simp only [Gkr.weights, SumcheckRound.normalizedWeights, zero_add, hk', ↓reduceDIte, eqDomainG, layerStmtOfG,
    vecOfG, Vector.getElem_ofFn]
  simp [List.getD_eq_getElem?_getD, hk]

/-- **The descendants keep doom**: values that pass the check carry doom on the sumcheck's last stage to doom on
`childRelT … 0`. -/
theorem children_keepG {C : Set (∀ i, O i)} {st : SumcheckRound.Stmt (Gkr.LayerX X E2 3 m) E2 m}
    (hpre : RelDoom C (SumcheckRound.rel (Gkr.familyT 3 μ leaves riders ρ m T) m) st)
    (ch : Fin 3 → CMlPolynomialEval E2 ρ) (hc : Gkr.combineCheck 3 ρ m st ch = true) :
    RelDoom C (Gkr.childRelT 3 μ leaves riders ρ m T 0) (Gkr.childNext 3 ρ m st ch) :=
  say_keep (fun o hout ↦ Gkr.combineCheck_sound 3 μ leaves riders ρ m T st o ch hc hout) hpre

variable {εmax T' : ℝ≥0∞}

open Classical in
/-- **A layer step at `E2`** at radix `2 ^ ρ` from layer `m`: from doom on the layer relation to doom on the step's
output relation. The combiner (`G(gLam)`) at `L₀ · errG gLam 2`, each round (`G(gRd)`) at `L₀ · errG gRd 2^ρ`, the
point `y` (`G(gy)`, one group of `ρ` draws) at `L₀ · errG gy ρ`; lead `0`, follower `T'`. -/
noncomputable def stepSpecG {L₀ : ℕ} (hfin : ∀ W, (cands W).Finite) (hcard : ∀ W, (cands W).ncard ≤ L₀)
    (hm : m + ρ ≤ μ) (hρ : 1 ≤ ρ) {gy : ℕ} (hgy : gy ≤ 64)
    (hlam : (L₀ : ℝ≥0∞) * errG gLam 2 + 0 ≤ εmax) (hrd : (L₀ : ℝ≥0∞) * errG gRd (2 ^ ρ) + 0 ≤ εmax)
    (hy : (L₀ : ℝ≥0∞) * errG gy ρ + T' ≤ εmax) (hε : εmax < 1) (s : GkrStateG) :
    Spec (gkrStepG gy ρ s) (StepPreG (m := m) leaves riders cands data s)
      (StepPostG leaves riders cands data T) εmax 0 T' :=
  if hs : s.point.length = m ∧ s.values.length = 3 then
    ((e2SampleSpecH (T := 0) hfin hcard (Gkr.layerRel 3 μ leaves riders m) (layerStmtOfG data m s)
      (SumcheckRound.rel (Gkr.familyT 3 μ leaves riders ρ m T) 0)
      (fun l ↦ Gkr.lambdaNext 3 m (layerStmtOfG data m s) l) (d := 2) (by norm_num) (fun o ho ↦ by
        refine le_trans (Nat.card_mono (Set.toFinite _) fun l hl ↦ ?_)
          (Gkr.card_lambda_le 3 μ leaves riders ρ m id T hm (relS := Gkr.layerRel 3 μ leaves riders m)
            (fun _ _ ↦ Iff.rfl) (layerStmtOfG data m s) o)
        exact ⟨(), ho, hl⟩) hlam).mono (fun _ hp ↦ hp.2.2) (fun _ _ h ↦ h) le_rfl le_rfl le_rfl).bind'
      fun lam ↦
    ((wireSumcheckSpecG (T := 0) (Gkr.familyT 3 μ leaves riders ρ m T) cands
      (Gkr.familyT_consistent' 3 μ leaves riders ρ m T) (Gkr.familyT_sound' 3 μ leaves riders ρ m T)
      hfin hcard Nat.one_le_two_pow (by norm_num) hrd (layerStmtOfG data m s, lam) s.point 0
      #v[] (polyEvalF s.values lam) (by simp [hs.1])
      (fun k hk ↦ weights_eq_eqDomainG data s hs.1 lam k hk)).mono
      (fun h hp ↦ by rw [polyEvalF_eq_powerBatch _ hs.2]; exact hp) (fun _ _ h ↦ h) le_rfl
      le_rfl le_rfl).bind' fun ⟨x, claim⟩ ↦
    let P0 := SumcheckPostG (Gkr.familyT 3 μ leaves riders ρ m T) cands
      (layerStmtOfG data m s, lam) m #v[] (x, claim)
    have hP0 : ∀ h z, P0 h → P0 (h ++ [Ev.read z]) := fun _ _ hp ↦ ⟨hp.1, hp.2.append _⟩
    have hread : e2Reads (2 ^ ρ - 1 + 1) = e2Reads (2 ^ ρ) := by
      rw [Nat.sub_add_cancel Nat.one_le_two_pow]
    (Spec.congr hread (e2ReadsSpecP P0 hP0 zero_le (2 ^ ρ - 1))).bind' fun child0 ↦
    let P1 := fun h ↦ child0.length = 2 ^ ρ - 1 + 1 ∧ P0 h
    (Spec.congr hread (e2ReadsSpecP P1 (fun _ _ hp ↦ ⟨hp.1, hP0 _ _ hp.2⟩) zero_le
      (2 ^ ρ - 1))).bind' fun child1 ↦
    let P2 := fun h ↦ child1.length = 2 ^ ρ - 1 + 1 ∧ P1 h
    (Spec.congr hread (e2ReadsSpecP P2 (fun _ _ hp ↦ ⟨hp.1, hp.2.1, hP0 _ _ hp.2.2⟩) zero_le
      (2 ^ ρ - 1))).bind' fun child2 ↦
    if hq : x.length = m ∧ child0.length = 2 ^ ρ ∧ child1.length = 2 ^ ρ ∧ child2.length = 2 ^ ρ then
      let base : X × (Vector E2 m × (Fin 3 → CMlPolynomialEval E2 ρ)) :=
        (data, (vecOfG m x, childrenOfG ρ [child0, child1, child2]))
      have hch : ∀ t ∈ [child0, child1, child2], t.length = 2 ^ ρ := by
        intro t ht
        simp only [List.mem_cons, List.not_mem_nil, or_false] at ht
        rcases ht with rfl | rfl | rfl
        exacts [hq.2.1, hq.2.2.1, hq.2.2.2]
      (Spec.require (Post := fun _ h ↦
          HDoom cands (Gkr.childRelT 3 μ leaves riders ρ m T 0) (base, #v[]) h)
        (fun _ hp hc ↦ by
          obtain ⟨-, -, -, -, W, hW, hR⟩ := hp
          exact ⟨W, hW, children_keepG leaves riders T hR _ (combineCheck_eqG _ _ rfl hch hc)⟩)).bind' fun _ ↦
      (Spec.congr (show e2SampleN gy (ρ - 1 + 1) = e2SampleN gy ρ by rw [Nat.sub_add_cancel hρ])
        (e2SampleNSpecHCount (T := T') hfin hcard (Gkr.childRelT 3 μ leaves riders ρ m T 0) (base, #v[])
          (Gkr.childRelT 3 μ leaves riders ρ m T ρ) (fun ys ↦ (base, vecOfG ρ ys)) (N := ρ) hgy
          (fun o ho ↦ by
            have := card_seq_le (fun i v ↦ (((base, v), o), ()) ∈ Gkr.childRelT 3 μ leaves riders ρ m T i)
              (fun i v hv ↦ Gkr.card_interpNext_le' 3 μ leaves riders ρ m T (base, v) o hv)
              (ρ - 1 + 1) 0 #v[] ρ (by omega) ho
            exact le_of_le_of_eq this (by rw [Nat.add_sub_cancel, Nat.sub_add_cancel hρ])) hy hε)).bind'
          fun y ↦
      (Spec.ret (Post := StepPostG leaves riders cands data T)
        ⟨[child0, child1, child2].map (multilinearEvalF · y), y ++ x⟩).mono
        (fun _ hp ↦ by
          obtain ⟨hyl, W, hW, hR⟩ := hp
          have hyl' : y.length = ρ := by omega
          have hR'' : RelDoom (cands W) (Gkr.stepOutT 3 μ leaves riders ρ m T)
              (Gkr.interpDone 3 ρ m (base, vecOfG ρ y)) := fun o ho hin ↦
            hR o ho ((Gkr.interpDone_mem_stepOutT_iff' 3 μ leaves riders ρ m T _ o).mp hin)
          rw [interpDone_eqG data x y [child0, child1, child2] hyl' rfl hch] at hR''
          exact ⟨by simp [hyl', hq.1]; omega, by simp, W, hW, hR''⟩)
        (fun _ _ h ↦ h) le_rfl le_rfl le_rfl
    else specOfFalseG fun _ hp ↦ hq ⟨by have := hp.2.2.2.1; simpa using this,
      by have := Nat.one_le_two_pow (n := ρ); have := hp.2.2.1; omega,
      by have := Nat.one_le_two_pow (n := ρ); have := hp.2.1; omega,
      by have := Nat.one_le_two_pow (n := ρ); have := hp.1; omega⟩
  else specOfFalseG fun _ hp ↦ hs ⟨hp.1, hp.2.1⟩

end Step

/-! ## The walk -/

section Walk

variable {ι : Type} {O : ι → Type} {X : Type} {μ : ℕ}
  (leaves : X → (∀ i, O i) → Fin 3 → CMlPolynomialEval E2 μ)
  (riders : X → (∀ i, O i) → List (Σ τ : Fin (μ + 1), CMlPolynomialEval E2 τ))
  (cands : Word → Set (∀ i, O i)) (data : X)

/-- The rider tracker of the next step at `E2`: progressive at the last step, constant before. -/
def trackOfG (n m : ℕ) (h : m + n = μ) : Gkr.RiderTrack μ riders (ρOf n) m :=
  if hl : n = ρOf n then Gkr.progTrack μ riders (ρOf n) m (by omega)
  else Gkr.constTrack μ riders (ρOf n) m

/-- **The walk's doom at `E2`** with `n` layers left at layer `m`: on the argument's output relation when none is
left; on the layer relation otherwise. -/
def LayersPreG (n m : ℕ) (_h : m + n = μ) (s : GkrStateG) (hist : List Ev) : Prop :=
  if n = 0 then
    s.point.length = μ ∧ s.values.length = 3 ∧
      HDoom cands (Gkr.relOut 3 μ leaves riders) (layerStmtOfG data μ s) hist
  else StepPreG (m := m) leaves riders cands data s hist

/-- The walk's lead with `n` layers left: the follower's when none is left, `0` otherwise (a nonce opens the
step). -/
noncomputable def walkLead (n : ℕ) (T : ℝ≥0∞) : ℝ≥0∞ := if n = 0 then T else 0

theorem walkLead_le (n : ℕ) (T : ℝ≥0∞) : walkLead n T ≤ T := by
  unfold walkLead; split_ifs <;> simp

/-- The doom after a step is the walk's doom with the layers it leaves. -/
theorem layersPre_of_stepPostG (n m : ℕ) (h : m + n = μ) (hn : n ≠ 0) (s : GkrStateG) (hist : List Ev)
    (hp : StepPostG leaves riders cands data (trackOfG riders n m h) s hist) :
    LayersPreG leaves riders cands data (n - ρOf n) (m + ρOf n) (by have := ρOf_le hn; omega) s hist := by
  obtain ⟨hl, hv, W, hW, hR⟩ := hp
  unfold LayersPreG
  split_ifs with h0
  · have hlast : n = ρOf n := by have := ρOf_le hn; omega
    have hm : m + ρOf n = μ := by omega
    unfold trackOfG at hR
    rw [dite_eq_left hlast] at hR
    refine ⟨by omega, hv, W, hW, fun o ho hin ↦ hR o ho ?_⟩
    have hvec : Vector.cast hm (vecOfG (m + ρOf n) s.point) = vecOfG μ s.point := by
      apply Vector.ext
      intro k hk
      simp [vecOfG]
    refine (Gkr.stepOutT_progTrack_iff 3 μ leaves riders (ρOf n) m hm _ o).mpr ?_
    simpa only [layerStmtOfG, hvec] using hin
  · have hlast : ¬ n = ρOf n := by omega
    unfold trackOfG at hR
    rw [dite_eq_right hlast] at hR
    exact ⟨hl, hv, W, hW, fun o ho hin ↦ hR o ho
      ((Gkr.stepOutT_constTrack_iff 3 μ leaves riders (ρOf n) m _ o).mpr hin)⟩

theorem layersPre_congrG {n n' m m' : ℕ} (hn : n = n') (hm : m = m') {h : m + n = μ} {h' : m' + n' = μ}
    {s : GkrStateG} {hist : List Ev} (hp : LayersPreG leaves riders cands data n m h s hist) :
    LayersPreG leaves riders cands data n' m' h' s hist := by
  subst hn hm
  exact hp

/-- `errG` grows with the numerator. -/
theorem errG_mono (g : ℕ) {a b : ℕ} (hab : a ≤ b) : errG g a ≤ errG g b := by
  unfold errG
  gcongr

variable {εmax T : ℝ≥0∞}

/-- **The walk's next step at `E2`** with `n ≠ 0` layers left, its point's grind `gy`: radix `2 ^ ρOf n`, from the
walk's doom to the walk's doom with `n − ρOf n` layers left. -/
noncomputable def walkStepSpecG {L₀ : ℕ} (hfin : ∀ W, (cands W).Finite) (hcard : ∀ W, (cands W).ncard ≤ L₀)
    (hlam : (L₀ : ℝ≥0∞) * errG gLam 2 + T ≤ εmax) (hrd : (L₀ : ℝ≥0∞) * errG gRd 5 + T ≤ εmax)
    (hε : εmax < 1) (n m : ℕ) (h : m + n = μ) (hn : n ≠ 0) {gy : ℕ} (hgy : gy ≤ 64)
    (hy : (L₀ : ℝ≥0∞) * errG gy (ρOf n) + walkLead (n - ρOf n) T ≤ εmax) (s : GkrStateG) :
    Spec (gkrStepG gy (ρOf n) s) (LayersPreG leaves riders cands data n m h s)
      (fun s' ↦ LayersPreG leaves riders cands data (n - ρOf n) (m + ρOf n) (by have := ρOf_le hn; omega) s')
      εmax 0 (walkLead (n - ρOf n) T) :=
  (stepSpecG leaves riders cands data (trackOfG riders n m h) (T' := walkLead (n - ρOf n) T) hfin hcard
    (by have := ρOf_le hn; omega) (by unfold ρOf; split_ifs <;> omega) hgy
    (le_trans (by rw [add_zero]; exact le_self_add) hlam)
    (le_trans (by
      gcongr
      · exact errG_mono _ (le_trans (Nat.pow_le_pow_right (by norm_num) (ρOf_le_two n)) (by norm_num))
      · exact zero_le) hrd)
    hy hε s).mono
    (fun hist hp ↦ by unfold LayersPreG at hp; simpa [hn] using hp)
    (fun s' hist hp ↦ layersPre_of_stepPostG leaves riders cands data n m h hn s' hist hp)
    le_rfl le_rfl le_rfl

/-- **The wire's GKR walk at `E2`** (`gkrLayersG`) with `n` layers left at layer `m`: from the walk's doom to doom on
the argument's output relation. Every group a nonce: lead `walkLead n T` (`0` with a step); the combiner at
`L₀ · errG gLam 2`, each round at `L₀ · errG gRd 5`, each point at `L₀ · errG gY 2` (the last at
`L₀ · errG gYl 4`), each plus the follower's `T`, within `εmax < 1`. -/
noncomputable def gkrLayersSpecG {L₀ : ℕ} (hfin : ∀ W, (cands W).Finite) (hcard : ∀ W, (cands W).ncard ≤ L₀)
    (hlam : (L₀ : ℝ≥0∞) * errG gLam 2 + T ≤ εmax) (hrd : (L₀ : ℝ≥0∞) * errG gRd 5 + T ≤ εmax)
    (hY : (L₀ : ℝ≥0∞) * errG gY 2 + T ≤ εmax) (hYl : (L₀ : ℝ≥0∞) * errG gYl 4 + T ≤ εmax) (hε : εmax < 1) :
    (n m : ℕ) → (h : m + n = μ) → (s : GkrStateG) →
      Spec (gkrLayersG n s) (LayersPreG leaves riders cands data n m h s)
        (fun s' ↦ LayersPreG leaves riders cands data 0 μ (by simp) s') εmax (walkLead n T) T
  | 0, m, h, s =>
    (Spec.ret (Post := fun s' ↦ LayersPreG leaves riders cands data 0 μ (by simp) s') s).mono
      (fun _ hp ↦ by unfold LayersPreG at hp ⊢; simpa using hp) (fun _ _ h ↦ h) le_rfl
      (by simp [walkLead]) le_rfl
  | 1, m, h, s =>
    (walkStepSpecG leaves riders cands data hfin hcard hlam hrd hε 1 m h one_ne_zero (gy := gYl) (by norm_num)
      (le_trans (by
        gcongr
        · exact errG_mono _ (by simp [ρOf])
        · simp [walkLead, ρOf]) hYl) s).mono
      (fun _ h ↦ h)
      (fun _ _ hp ↦ layersPre_congrG leaves riders cands data (by simp [ρOf]) (by simp [ρOf]; omega) hp)
      le_rfl (by simp [walkLead]) (by simp [walkLead, ρOf])
  | n + 2, m, h, s =>
    Spec.ite
      (fun hodd ↦
        have hρ : ρOf (n + 2) = 1 := by simp [ρOf, hodd]
        Spec.congr (by rw [hρ])
          (((walkStepSpecG leaves riders cands data hfin hcard hlam hrd hε (n + 2) m h (by omega) (gy := gY)
            (by norm_num) (le_trans (by
              gcongr
              · exact errG_mono _ (by rw [hρ]; norm_num)
              · rw [hρ]; simp [walkLead]) hY) s).bind' fun s' ↦
            (gkrLayersSpecG hfin hcard hlam hrd hY hYl hε (n + 1) (m + 1) (by omega) s').mono
              (fun _ hp ↦ layersPre_congrG leaves riders cands data (by rw [hρ]; omega) (by rw [hρ]) hp)
              (fun _ _ h ↦ h) le_rfl (le_of_eq (by rw [hρ]; rfl)) le_rfl).mono
            (fun _ h ↦ h) (fun _ _ h ↦ h) le_rfl (by simp [walkLead]) le_rfl))
      (fun heven ↦
        have hρ : ρOf (n + 2) = 2 := by
          have : n % 2 = 0 := by omega
          simp [ρOf, this]
        Spec.congr (by rw [hρ])
          (((walkStepSpecG leaves riders cands data hfin hcard hlam hrd hε (n + 2) m h (by omega)
            (gy := if n = 0 then gYl else gY) (by split_ifs <;> norm_num) (by
              rw [hρ, show n + 2 - 2 = n by omega]
              unfold walkLead
              split_ifs with h0
              · exact le_trans (by gcongr; exact errG_mono _ (by norm_num)) hYl
              · exact le_trans (by gcongr; exact zero_le) hY) s).bind' fun s' ↦
            (gkrLayersSpecG hfin hcard hlam hrd hY hYl hε n (m + 2) (by omega) s').mono
              (fun _ hp ↦ layersPre_congrG leaves riders cands data (by rw [hρ]; omega) (by rw [hρ]) hp)
              (fun _ _ h ↦ h) le_rfl (le_of_eq (by rw [hρ]; rfl)) le_rfl).mono
            (fun _ h ↦ h) (fun _ _ h ↦ h) le_rfl (by simp [walkLead]) le_rfl))

end Walk

/-! ## `verify_gkr_grand_products` at `E2` -/

section Gkr

variable {ι : Type} {O : ι → Type} {X : Type} {μ : ℕ}
  (leaves : X → (∀ i, O i) → Fin 3 → CMlPolynomialEval E2 μ)
  (riders : X → (∀ i, O i) → List (Σ τ : Fin (μ + 1), CMlPolynomialEval E2 τ))
  (cands : Word → Set (∀ i, O i)) (data : X)

/-- The protocol's roots statement is the wire's state at layer `0`. -/
theorem rootStmt_eqG (shared count : E2) :
    Gkr.rootStmt 3 (data, ![shared, shared, count]) = layerStmtOfG data 0 ⟨[shared, shared, count], []⟩ := by
  refine Prod.ext rfl (Prod.ext (Vector.ext fun i hi ↦ absurd hi (by omega)) ?_)
  funext t
  fin_cases t <;> rfl

/-- What the wire's GKR at `E2` gives: the count root `0`, which the bus phase rejects, or doom on the argument's
output relation at the point and values it returns. -/
def GkrPostG (r : E2 × List E2 × List E2) (h : List Ev) : Prop :=
  r.1 = 0 ∨ (r.2.1.length = μ ∧ r.2.2.length = 3 ∧
    HDoom cands (Gkr.relOut 3 μ leaves riders) (layerStmtOfG data μ ⟨r.2.2, r.2.1⟩) h)

variable {εmax T : ℝ≥0∞}

/-- **`verify_gkr_grand_products` at `E2`** (`gkrSpec`'s twin) at depth `μ ≠ 0`: from doom on a relation `R` at `x`
into which a nonzero count root in the grand product's input relation reflects (`hroots`), to `GkrPostG`. The two
root reads, then the walk; lead `0`, follower `T`; each group's error plus `T` within `εmax < 1`. -/
noncomputable def gkrSpecG {S : Type} (R : Set ((S × ∀ i, O i) × Unit)) (x : S)
    (hroots : ∀ o (shared count : E2), count ≠ 0 →
      ((((data, ![shared, shared, count]) : X × (Fin 3 → E2)), o), ()) ∈ Gkr.relIn 3 μ leaves riders →
        ((x, o), ()) ∈ R)
    {L₀ : ℕ} (hfin : ∀ W, (cands W).Finite) (hcard : ∀ W, (cands W).ncard ≤ L₀) (hμ : μ ≠ 0)
    (hlam : (L₀ : ℝ≥0∞) * errG gLam 2 + T ≤ εmax) (hrd : (L₀ : ℝ≥0∞) * errG gRd 5 + T ≤ εmax)
    (hY : (L₀ : ℝ≥0∞) * errG gY 2 + T ≤ εmax) (hYl : (L₀ : ℝ≥0∞) * errG gYl 4 + T ≤ εmax) (hε : εmax < 1) :
    Spec (verifyGkrGrandProductsG μ) (HDoom cands R x) (GkrPostG leaves riders cands data) εmax 0 T :=
  have hT : min 1 T ≤ εmax := le_trans (min_le_right _ _) (le_trans le_add_self hlam)
  (e2ReadSpecQ (Pre := HDoom cands R x) (fun _ h ↦ HDoom cands R x h) (fun _ _ hp ↦ hp.append _)
    zero_le).bind' fun shared ↦
  (e2ReadSpecQ (Pre := HDoom cands R x) (T := min 1 T) (fun count h ↦ count = 0 ∨ HDoom cands
      (Gkr.relIn 3 μ leaves riders) (data, ![shared, shared, count]) h)
    (fun _ c hp ↦ by
      by_cases hz : e2OfE c = 0
      · exact .inl hz
      · obtain ⟨W, hW, hR⟩ := hp
        exact .inr ⟨W, firstWord_append hW _, fun o ho hin ↦ hR o ho (hroots o shared _ hz hin)⟩)
    hT).bind' fun count ↦
  if hz : count = 0 then
    ((alwaysSpec (Post := fun _ _ ↦ True) (fun _ _ ↦ trivial) hT).bind' fun (s : GkrStateG) ↦
      (Spec.ret (Post := GkrPostG leaves riders cands data) (count, s.point, s.values)).mono
        (fun _ _ ↦ .inl hz) (fun _ _ h ↦ h) le_rfl le_rfl le_rfl).mono
      (fun _ _ ↦ trivial) (fun _ _ h ↦ h) le_rfl le_rfl le_rfl
  else
    ((gkrLayersSpecG leaves riders cands data hfin hcard hlam hrd hY hYl hε μ 0 (by simp)
      ⟨[shared, shared, count], []⟩).bind' fun s ↦
    (Spec.ret (Post := GkrPostG leaves riders cands data) (count, s.point, s.values)).mono
      (fun _ hp ↦ by
        unfold LayersPreG at hp
        simp only [↓reduceIte] at hp
        exact .inr hp) (fun _ _ h ↦ h) le_rfl le_rfl le_rfl).mono
      (fun h₀ hp ↦ by
        obtain ⟨W, hW, hR⟩ := hp.resolve_left hz
        unfold LayersPreG
        simp only [hμ, ↓reduceIte]
        refine ⟨rfl, rfl, W, hW, fun o ho hin ↦ hR o ho
          ((Gkr.relIn_iff_layerRel_zero 3 μ leaves riders _ o).mpr ?_)⟩
        rw [rootStmt_eqG data shared count]
        exact hin) (fun _ _ h ↦ h) le_rfl (by simp [walkLead, hμ]) le_rfl

end Gkr

end Lvm6.Mb
