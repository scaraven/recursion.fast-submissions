-- lvm6 F1: the v6 group rule (`FORMAT6.md` v2 §4; `MB-decision.md` §6 `e2SampleN`, written once):
-- one nonce, a ground draw with its proof of work, further draws; its doom rule and its escape.
import Lvm6Format
import LvmE2VSample
import LvmCertSFrame
import Mathlib.Algebra.MvPolynomial.SchwartzZippel

/-!
# Ground groups `G(g), D(k)`

In the verifier language (season 1's `VerifierProgram`, where a sample is a 24-byte challenge `c : E`
whose lanes 0–1 are the `E2` value and whose lane 2 is the proof-of-work lane):

* **`grp6 g k`**: the nonce (one read, absorbed last), the ground draw `c₀` with `require (powOK g c₀)`,
  then `k` further draws `c₁ … c_k` (empty buffer); it returns the `k + 1` values `e2OfE cᵢ`.
* **`grpEsc g k P`**: the joint probability, over the `k + 1` uniform draws, that the ground draw's
  proof of work passes and `P` holds of the values. Only the ground draw carries the work, so a group
  of `k + 1` draws costs one nonce and is priced once (`MB-decision.md` §7 risk 2).
* **`doomGrp6`**: the doom rule of a group, from `Doomed C A` to `Doomed C (A' ys)`: if every candidate
  not alive becomes alive with joint probability `≤ e`, the group's escape is `≤ L₀·e`; lead `0` (the
  nonce is a move), the boundary after the nonce at `L₀·e + T ≤ εmax`. It is `Spec.ofNoMove` on the
  draws (no prover move inside a group) after `doomRead`.
* **`grpEsc_sz`** (via `avgN_eq_sum`, `grpEsc_eq_card`, `card_grp_le`): Schwartz–Zippel with
  grinding: a nonzero polynomial in the `k + 1` values of total
  degree `≤ d` vanishes with joint probability `≤ errG g d = 2^-g · d / 2^128`.
* **`doomSep6`**: a bind draw `B` (v2.2) keeps doom at escape `0`.
* **`grp6_eq`**: `grp6 g k` is `e2Sample g` followed by `k` draws (WP K1's `gPoint` body).
* **`errG_le_εI`**: a group PARAM admits (`8c ≤ 7·2^g`) has `errG g c ≤ εI = 7·2^-131`.
-/

set_option autoImplicit false

namespace Lvm6

open LeanVM.Parameters LeanVM.Protocol.Compile LeanVM.Protocol.Verifier
open LeanVM.Protocol.EndToEnd.Front Lvm.E2V
open scoped ENNReal NNReal

/-! ## The programs -/

section Prog

variable {α : Type}

/-- `n` draws, passed to `f` in order. -/
def drawN : ℕ → (List E → VerifierProgram α) → VerifierProgram α
  | 0, f => f []
  | n + 1, f => .sample fun c ↦ drawN n fun cs ↦ f (c :: cs)

end Prog

/-- **The draws of a group**: the ground draw and its proof of work, then `k` further draws. -/
def draws6 (g k : ℕ) : VerifierProgram (List E2) :=
  .sample fun c ↦ if powOK g c then drawN k (fun cs ↦ .ret (e2OfE c :: cs.map e2OfE)) else .fail

/-- **A ground group** `G(g), D(k)`: the nonce, then the draws. -/
def grp6 (g k : ℕ) : VerifierProgram (List E2) := VerifierProgram.readScalar >>= fun _ ↦ draws6 g k

/-! ## The same group in `e2Sample` form (WP K1's `gPoint` shape) -/

/-- `n` further draws, one at a time (the shape of WP K1's `dDraws`). -/
def drawsE2 : ℕ → VerifierProgram (List E2)
  | 0 => pure []
  | n + 1 => (VerifierProgram.sampleChallenge >>= fun c ↦ pure (e2OfE c)) >>= fun x ↦
      drawsE2 n >>= fun xs ↦ pure (x :: xs)

theorem bind_assoc6 {α β γ : Type} (m : VerifierProgram α) (f : α → VerifierProgram β)
    (h : β → VerifierProgram γ) : (m.bind f).bind h = m.bind fun a ↦ (f a).bind h := by
  induction m with
  | ret a => rfl
  | fail => rfl
  | read k ih => exact congrArg VerifierProgram.read (funext ih)
  | sample k ih => exact congrArg VerifierProgram.sample (funext ih)
  | grind b k ih => exact congrArg (VerifierProgram.grind b) ih
  | commit ht w k ih => exact congrArg (VerifierProgram.commit ht w) ih
  | query i ps k ih => exact congrArg (VerifierProgram.query i ps) (funext ih)

theorem drawN_eq {β : Type} (f : List E2 → VerifierProgram β) :
    ∀ k, drawN k (fun cs ↦ f (cs.map e2OfE)) = (drawsE2 k).bind f
  | 0 => rfl
  | k + 1 => by
    show VerifierProgram.sample _ = VerifierProgram.sample _
    congr 1; funext c
    show drawN k (fun cs ↦ f ((c :: cs).map e2OfE)) =
      ((drawsE2 k).bind fun xs ↦ VerifierProgram.ret (e2OfE c :: xs)).bind f
    rw [bind_assoc6]
    exact drawN_eq (fun xs ↦ f (e2OfE c :: xs)) k

/-- **`grp6` is the group in `e2Sample` form**: the nonce, the ground draw with its proof of work
(`e2Sample g`), then `k` further draws. WP K1's `gPoint g k` has this body, so its specification is
`doomGrp6` through this equation. -/
theorem grp6_eq (g k : ℕ) :
    grp6 g k = e2Sample g >>= fun c ↦ drawsE2 k >>= fun cs ↦ pure (c :: cs) := by
  show VerifierProgram.read _ = VerifierProgram.read _
  congr 1; funext x
  show VerifierProgram.sample _ = VerifierProgram.sample _
  congr 1; funext c
  show _ = ((if powOK g c then VerifierProgram.ret () else VerifierProgram.fail).bind
      fun _ ↦ VerifierProgram.ret (e2OfE c)).bind fun c' ↦
        (drawsE2 k).bind fun cs ↦ VerifierProgram.ret (c' :: cs)
  by_cases hp : powOK g c
  · simp only [hp, ↓reduceIte]
    exact drawN_eq (fun cs ↦ VerifierProgram.ret (e2OfE c :: cs)) k
  · simp only [hp, ↓reduceIte]
    rfl

/-! ## No proof of work, no move inside a group -/

namespace VerifierProgram

variable {α : Type}

/-- A program of draws, rejections and returns only. -/
def NoMove : LeanVM.Protocol.Compile.VerifierProgram α → Prop
  | .ret _ => True
  | .fail => True
  | .sample k => ∀ c, NoMove (k c)
  | _ => False

theorem NoMove.after {p q : LeanVM.Protocol.Compile.VerifierProgram α} (hp : NoMove p) {l : List Ev}
    (h : p.after l = some q) : NoMove q := by
  induction l generalizing p with
  | nil => cases p <;> (cases h; exact hp)
  | cons e es ih =>
    cases p <;> cases e <;> simp only [LeanVM.Protocol.Compile.VerifierProgram.after,
      reduceCtorEq] at h
    all_goals first
      | exact ih (hp _) h
      | exact hp.elim

theorem NoMove.not_isMove {p : LeanVM.Protocol.Compile.VerifierProgram α} (hp : NoMove p) :
    ¬ p.IsMove := by
  cases p <;> simp_all [NoMove, LeanVM.Protocol.Compile.VerifierProgram.IsMove]

end VerifierProgram

open VerifierProgram in
theorem noMove_drawN {α : Type} {f : List E → LeanVM.Protocol.Compile.VerifierProgram α}
    (hf : ∀ cs, NoMove (f cs)) : ∀ n, NoMove (drawN n f)
  | 0 => hf []
  | n + 1 => fun c ↦ noMove_drawN (fun cs ↦ hf (c :: cs)) n

open VerifierProgram in
theorem noMove_draws6 (g k : ℕ) : NoMove (draws6 g k) := fun c ↦ by
  by_cases h : powOK g c
  · simp only [h, ite_true]; exact noMove_drawN (f := fun cs ↦ .ret (e2OfE c :: cs.map e2OfE))
      (fun _ ↦ trivial) k
  · simp only [h, ite_false]; trivial

theorem noGrind_drawN {α : Type} {f : List E → LeanVM.Protocol.Compile.VerifierProgram α}
    (hf : ∀ cs, (f cs).NoGrind) : ∀ n, (drawN n f).NoGrind
  | 0 => hf []
  | n + 1 => fun c ↦ noGrind_drawN (fun cs ↦ hf (c :: cs)) n

/-- **A group asks no proof of work** in the language's sense (`grind`): its work is the nonce and the
`require` on the ground draw, so the compiler's `grindBits` stay `0`. -/
theorem grp6_noGrind (g k : ℕ) : (grp6 g k).NoGrind :=
  LeanVM.Protocol.Compile.VerifierProgram.NoGrind.bind (fun _ ↦ trivial) fun _ c ↦ by
    by_cases h : powOK g c
    · simp only [h, ite_true]; exact noGrind_drawN (f := fun cs ↦ .ret (e2OfE c :: cs.map e2OfE))
        (fun _ ↦ trivial) k
    · simp only [h, ite_false]; trivial

/-! ## Averages over several draws -/

/-- The average over `n` uniform draws. -/
noncomputable def avgN : ℕ → (List E → ℝ≥0∞) → ℝ≥0∞
  | 0, f => f []
  | n + 1, f => avgE fun c ↦ avgN n fun cs ↦ f (c :: cs)

/-- **The escape of a group** for the event `P` on its values: the ground draw's proof of work passes
and `P` holds, jointly over the `k + 1` draws. -/
noncomputable def grpEsc (g k : ℕ) (P : List E2 → Prop) : ℝ≥0∞ :=
  avgE fun c ↦ if powOK g c then avgN k (fun cs ↦ indE (P (e2OfE c :: cs.map e2OfE))) else 0

theorem avgN_mono {n : ℕ} {f f' : List E → ℝ≥0∞} (h : ∀ cs, cs.length = n → f cs ≤ f' cs) :
    avgN n f ≤ avgN n f' := by
  induction n generalizing f f' with
  | zero => exact h [] rfl
  | succ n ih =>
    exact avgE_mono fun c ↦ ih fun cs hcs ↦ h (c :: cs) (by simp [hcs])

theorem avgE_finsetSum {ι : Type} (s : Finset ι) (f : ι → E → ℝ≥0∞) :
    avgE (fun c ↦ ∑ i ∈ s, f i c) = ∑ i ∈ s, avgE (f i) := by
  simp only [avgE]
  rw [Finset.sum_comm, Finset.mul_sum]

theorem avgN_finsetSum {ι : Type} (s : Finset ι) :
    ∀ (n : ℕ) (f : ι → List E → ℝ≥0∞), avgN n (fun cs ↦ ∑ i ∈ s, f i cs) = ∑ i ∈ s, avgN n (f i)
  | 0, _ => rfl
  | n + 1, f => by
    simp only [avgN]
    rw [← avgE_finsetSum]
    congr 1; funext c
    exact avgN_finsetSum s n (fun i cs ↦ f i (c :: cs))

/-! ## The escape of the draws -/

section Esc

variable {α : Type}

theorem retExp_drawN (G : α → List Ev → ℝ≥0∞) (h₀ : List Ev) :
    ∀ (n : ℕ) (f : List E → LeanVM.Protocol.Compile.VerifierProgram α) (l : List Ev),
      LeanVM.Protocol.Compile.VerifierProgram.retExp G h₀ l (drawN n f) =
        avgN n (fun cs ↦ LeanVM.Protocol.Compile.VerifierProgram.retExp G h₀
          (l ++ cs.map Ev.sample) (f cs))
  | 0, f, l => by simp [drawN, avgN]
  | n + 1, f, l => by
    simp only [drawN, avgN, LeanVM.Protocol.Compile.VerifierProgram.retExp, avgE]
    congr 1; refine Finset.sum_congr rfl fun c _ ↦ ?_
    rw [retExp_drawN G h₀ n]
    congr 1; funext cs
    simp [List.append_assoc]

theorem commits_map_sample (cs : List E) : commits (cs.map Ev.sample) = [] := by
  induction cs with
  | nil => rfl
  | cons c cs ih => simpa [commits] using ih

end Esc

section Doom

variable {β : Type} {C : List Ev → Set β} [Finite β] {L₀ : ℕ} {εmax T : ℝ≥0∞}

open Classical in
/-- The escape of the draws from `Doomed C A`: `L₀` times the per-candidate joint escape. -/
theorem escRet_draws6 (hst : Stable C) (hcard : ∀ h, (C h).ncard ≤ L₀) {g k : ℕ} (A : β → Prop)
    (A' : List E2 → β → Prop) (e : ℝ≥0∞) (hesc : ∀ q, ¬ A q → grpEsc g k (fun ys ↦ A' ys q) ≤ e)
    (h₀ : List Ev) (hd : Doomed C A h₀) :
    LeanVM.Protocol.Compile.VerifierProgram.escRet
      (fun ys h ↦ ys.length = k + 1 ∧ Doomed C (A' ys) h) h₀ [] (draws6 g k) ≤ L₀ * e := by
  have hfin : (C h₀).Finite := Set.toFinite _
  set S := hfin.toFinset
  have hS : (S.card : ℝ≥0∞) ≤ L₀ := by
    have := hcard h₀
    rw [Set.ncard_eq_toFinset_card _ hfin] at this
    exact_mod_cast this
  -- pointwise: a return outside the postcondition makes some candidate alive
  have hpt : ∀ (c : E) (cs : List E), cs.length = k →
      (if (e2OfE c :: cs.map e2OfE).length = k + 1 ∧
          Doomed C (A' (e2OfE c :: cs.map e2OfE)) (h₀ ++ ([] ++ [Ev.sample c] ++ cs.map Ev.sample))
        then (0 : ℝ≥0∞) else 1) ≤ ∑ q ∈ S, indE (A' (e2OfE c :: cs.map e2OfE) q) := by
    intro c cs hcs
    split_ifs with hp
    · exact zero_le
    · have hl : (e2OfE c :: cs.map e2OfE).length = k + 1 := by simp [hcs]
      have hcm : commits ([] ++ [Ev.sample c] ++ cs.map Ev.sample) = [] := by
        simpa [commits] using commits_map_sample cs
      rw [Doomed.append hst hcm] at hp
      have : ¬ Doomed C (A' (e2OfE c :: cs.map e2OfE)) h₀ := fun h ↦ hp ⟨hl, h⟩
      simp only [Doomed, not_forall, not_not] at this
      obtain ⟨q, hq, ha⟩ := this
      have hqS : q ∈ S := hfin.mem_toFinset.mpr hq
      calc (1 : ℝ≥0∞) = indE (A' (e2OfE c :: cs.map e2OfE) q) := by simp [indE, ha]
        _ ≤ _ := Finset.single_le_sum (f := fun q ↦ indE (A' (e2OfE c :: cs.map e2OfE) q))
            (fun _ _ ↦ zero_le) hqS
  -- the escape as an average over the draws
  have hstep : LeanVM.Protocol.Compile.VerifierProgram.escRet
      (fun ys h ↦ ys.length = k + 1 ∧ Doomed C (A' ys) h) h₀ [] (draws6 g k) ≤
      avgE fun c ↦ if powOK g c then
        avgN k (fun cs ↦ ∑ q ∈ S, indE (A' (e2OfE c :: cs.map e2OfE) q)) else 0 := by
    simp only [LeanVM.Protocol.Compile.VerifierProgram.escRet, draws6,
      LeanVM.Protocol.Compile.VerifierProgram.retExp, avgE]
    gcongr with c
    split_ifs with hw
    · rw [retExp_drawN]
      refine avgN_mono fun cs hcs ↦ ?_
      simp only [LeanVM.Protocol.Compile.VerifierProgram.retExp]
      convert hpt c cs hcs
    · simp [LeanVM.Protocol.Compile.VerifierProgram.retExp]
  refine hstep.trans ?_
  have hsum : (avgE fun c ↦ if powOK g c then
      avgN k (fun cs ↦ ∑ q ∈ S, indE (A' (e2OfE c :: cs.map e2OfE) q)) else 0) =
      ∑ q ∈ S, grpEsc g k (fun ys ↦ A' ys q) := by
    have hfun : (fun c ↦ if powOK g c then
        avgN k (fun cs ↦ ∑ q ∈ S, indE (A' (e2OfE c :: cs.map e2OfE) q)) else 0) =
        fun c ↦ ∑ q ∈ S, (if powOK g c then
          avgN k (fun cs ↦ indE (A' (e2OfE c :: cs.map e2OfE) q)) else 0) := by
      funext c; split_ifs <;> simp [avgN_finsetSum]
    rw [hfun, avgE_finsetSum]
    rfl
  rw [hsum]
  calc ∑ q ∈ S, grpEsc g k (fun ys ↦ A' ys q) ≤ ∑ _q ∈ S, e :=
        Finset.sum_le_sum fun q hq ↦ hesc q (hd q (hfin.mem_toFinset.mp hq))
    _ = S.card * e := by rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ L₀ * e := by gcongr

/-- The draws' specification (`Spec.ofNoMove`). -/
noncomputable def doomDraws6 (hst : Stable C) (hcard : ∀ h, (C h).ncard ≤ L₀) {g k : ℕ}
    (A : β → Prop) (A' : List E2 → β → Prop) (e : ℝ≥0∞)
    (hesc : ∀ q, ¬ A q → grpEsc g k (fun ys ↦ A' ys q) ≤ e) (hε : εmax < 1)
    (he : (L₀ : ℝ≥0∞) * e + T ≤ εmax) :
    Spec (draws6 g k) (Doomed C A) (fun ys h ↦ ys.length = k + 1 ∧ Doomed C (A' ys) h) εmax
      (L₀ * e + T) T :=
  Spec.ofNoMove (fun _ ha ↦ VerifierProgram.NoMove.not_isMove
      (VerifierProgram.NoMove.after (noMove_draws6 g k) ha))
    ((le_self_add.trans he).trans_lt hε)
    (fun h₀ hd ↦ escRet_draws6 hst hcard A A' e hesc h₀ hd)

/-- **The doom rule of a ground group** `G(g), D(k)`: from doom of `A` to doom of `A' ys` at the
group's values `ys`, when each candidate not alive becomes alive with joint probability `≤ e`
(`grpEsc`). Lead `0` (the nonce is a move); the group is `L₀ · e + T ≤ εmax`. -/
noncomputable def doomGrp6 (hst : Stable C) (hcard : ∀ h, (C h).ncard ≤ L₀) {g k : ℕ}
    (A : β → Prop) (A' : List E2 → β → Prop) (e : ℝ≥0∞)
    (hesc : ∀ q, ¬ A q → grpEsc g k (fun ys ↦ A' ys q) ≤ e) (hε : εmax < 1)
    (he : (L₀ : ℝ≥0∞) * e + T ≤ εmax) :
    Spec (grp6 g k) (Doomed C A) (fun ys h ↦ ys.length = k + 1 ∧ Doomed C (A' ys) h) εmax 0 T :=
  (doomRead hst A he).bind' fun _ ↦ doomDraws6 hst hcard A A' e hesc hε he

/-- **A bind draw** `B` (`FORMAT6.md` v2.2 §4: one draw, value and PoW lane discarded; season 1's
`e2Sep`) keeps doom with escape `0`: the lead is the follower's. -/
noncomputable def doomSep6 (hst : Stable C) (hcard : ∀ h, (C h).ncard ≤ L₀) (A : β → Prop) :
    Spec e2Sep (Doomed C A) (fun _ h ↦ Doomed C A h) εmax T T :=
  ((doomSample (εmax := εmax) (T := T) hst hcard A (fun _ ↦ A) 0
      (fun q hq ↦ by simp [indE, hq, avgE])).mono (fun _ h ↦ h) (fun _ _ h ↦ h) le_rfl
      (by simp) le_rfl).bind' fun _ ↦ Spec.ret (Post := fun _ h ↦ Doomed C A h) ()

end Doom

/-! ## Schwartz–Zippel with grinding -/

section SZ

open LeanVM.Protocol Finset

theorem card_K6 : Fintype.card K = 2 ^ 64 := by
  rw [Fintype.card_congr BF64.equivFin, Fintype.card_fin]

theorem avgN_eq_sum : ∀ (n : ℕ) (f : List E → ℝ≥0∞),
    avgN n f = (∑ v : Fin n → E, f (List.ofFn v)) * ((Fintype.card E : ℝ≥0∞) ^ n)⁻¹
  | 0, f => by simp [avgN]
  | n + 1, f => by
    have ih : ∀ c : E, avgN n (fun cs ↦ f (c :: cs)) =
        (∑ v : Fin n → E, f (c :: List.ofFn v)) * ((Fintype.card E : ℝ≥0∞) ^ n)⁻¹ :=
      fun c ↦ avgN_eq_sum n _
    simp only [avgN, avgE, ih]
    rw [← Finset.sum_mul, ← (Fin.consEquiv fun _ : Fin (n + 1) ↦ E).sum_comp,
      Fintype.sum_prod_type]
    simp only [Fin.consEquiv, Equiv.coe_fn_mk, List.ofFn_succ, Fin.cons_zero, Fin.cons_succ]
    rw [pow_succ', ENNReal.mul_inv (Or.inr (ENNReal.pow_ne_top (ENNReal.natCast_ne_top _)))
      (Or.inl (ENNReal.natCast_ne_top _))]
    ring

open Classical in
theorem grpEsc_eq_card (g k : ℕ) (P : List E2 → Prop) :
    grpEsc g k P = ((univ.filter fun w : Fin (k + 1) → E ↦
      powOK g (w 0) ∧ P (List.ofFn fun i ↦ e2OfE (w i))).card : ℝ≥0∞) *
      ((Fintype.card E : ℝ≥0∞) ^ (k + 1))⁻¹ := by
  rw [Finset.card_filter, Nat.cast_sum, ← (Fin.consEquiv fun _ : Fin (k + 1) ↦ E).sum_comp,
    Fintype.sum_prod_type, pow_succ', ENNReal.mul_inv
      (Or.inr (ENNReal.pow_ne_top (ENNReal.natCast_ne_top _))) (Or.inl (ENNReal.natCast_ne_top _)),
    grpEsc, avgE, Finset.mul_sum, Finset.sum_mul]
  refine Finset.sum_congr rfl fun c _ ↦ ?_
  simp only [avgN_eq_sum, Fin.consEquiv, Equiv.coe_fn_mk, Fin.cons_zero, List.ofFn_succ,
    Fin.cons_succ, List.map_ofFn, Function.comp_def]
  split_ifs with hw
  · simp only [hw, true_and, Finset.sum_mul, Finset.mul_sum]
    refine Finset.sum_congr rfl fun v _ ↦ ?_
    by_cases hP : P (e2OfE c :: List.ofFn fun i ↦ e2OfE (v i)) <;> simp [indE, hP]
  · simp [hw]

/-- The draws of a group as their `E2` values and their PoW lanes. -/
def splitEquiv (k : ℕ) : (Fin (k + 1) → E) ≃ (Fin (k + 1) → E2) × (Fin (k + 1) → K) :=
  (Equiv.arrowCongr (Equiv.refl _) eSplit).trans
    (Equiv.arrowProdEquivProdArrow _ (fun _ ↦ E2) (fun _ ↦ K))

theorem splitEquiv_symm_fst (k : ℕ) (y : Fin (k + 1) → E2) (z : Fin (k + 1) → K) (i : Fin (k + 1)) :
    e2OfE ((splitEquiv k).symm (y, z) i) = y i :=
  congrArg Prod.fst (eSplit.apply_symm_apply (y i, z i))

theorem splitEquiv_symm_snd (k : ℕ) (y : Fin (k + 1) → E2) (z : Fin (k + 1) → K) (i : Fin (k + 1)) :
    ((splitEquiv k).symm (y, z) i).limb 2 = z i :=
  congrArg Prod.snd (eSplit.apply_symm_apply (y i, z i))

open Classical in
theorem card_grp_le {g k d : ℕ} (hg : g ≤ 64) {p : MvPolynomial (Fin (k + 1)) E2} (hp : p ≠ 0)
    (hd : p.totalDegree ≤ d) :
    (univ.filter fun w : Fin (k + 1) → E ↦
      powOK g (w 0) ∧ MvPolynomial.eval (fun i ↦ e2OfE (w i)) p = 0).card ≤
      d * 2 ^ (64 - g + 192 * k) := by
  have hmap : (univ.filter fun w : Fin (k + 1) → E ↦
      powOK g (w 0) ∧ MvPolynomial.eval (fun i ↦ e2OfE (w i)) p = 0).map (splitEquiv k).toEmbedding =
      (univ.filter fun y : Fin (k + 1) → E2 ↦ MvPolynomial.eval y p = 0) ×ˢ
        (univ.filter fun z : Fin (k + 1) → K ↦ kToNat (z 0) < 2 ^ (64 - g)) := by
    ext ⟨y, z⟩
    simp only [Finset.mem_map_equiv, Finset.mem_filter, Finset.mem_univ, true_and,
      Finset.mem_product, powOK_iff_lane2 hg, splitEquiv_symm_fst, splitEquiv_symm_snd]
    tauto
  have hB : (univ.filter fun z : Fin (k + 1) → K ↦ kToNat (z 0) < 2 ^ (64 - g)).card =
      2 ^ (64 - g) * 2 ^ (64 * k) := by
    have hm : (univ.filter fun z : Fin (k + 1) → K ↦ kToNat (z 0) < 2 ^ (64 - g)).map
        (Fin.consEquiv fun _ ↦ K).symm.toEmbedding =
        (univ.filter fun a : K ↦ kToNat a < 2 ^ (64 - g)) ×ˢ (univ : Finset (Fin k → K)) := by
      ext ⟨a, t⟩
      simp [Finset.mem_map_equiv, Fin.consEquiv]
    rw [← Finset.card_map (Fin.consEquiv fun _ ↦ K).symm.toEmbedding, hm, Finset.card_product, card_kToNat_lt (by omega), Finset.card_univ,
      Fintype.card_fun, Fintype.card_fin, card_K6, ← pow_mul]
  have hA : ((univ.filter fun y : Fin (k + 1) → E2 ↦ MvPolynomial.eval y p = 0).card : ℚ≥0) ≤
      d * 2 ^ (128 * k) := by
    have h := MvPolynomial.schwartz_zippel_totalDegree hp (univ : Finset E2)
    rw [Fintype.piFinset_univ, card_univ, card_E2, Nat.cast_pow, Nat.cast_ofNat] at h
    rw [div_le_div_iff₀ (by positivity) (by positivity)] at h
    have hpos : (0 : ℚ≥0) < 2 ^ 128 := by positivity
    refine le_of_mul_le_mul_right ?_ hpos
    calc _ ≤ (p.totalDegree : ℚ≥0) * (2 ^ 128) ^ (k + 1) := h
      _ ≤ d * 2 ^ (128 * k) * 2 ^ 128 := by
        rw [pow_succ, pow_mul, ← mul_assoc]; gcongr
  have hA' : (univ.filter fun y : Fin (k + 1) → E2 ↦ MvPolynomial.eval y p = 0).card ≤
      d * 2 ^ (128 * k) := by exact_mod_cast hA
  rw [← Finset.card_map (splitEquiv k).toEmbedding, hmap, Finset.card_product, hB]
  calc _ ≤ d * 2 ^ (128 * k) * (2 ^ (64 - g) * 2 ^ (64 * k)) := Nat.mul_le_mul_right _ hA'
    _ = d * 2 ^ (64 - g + 192 * k) := by
      rw [mul_assoc, ← pow_add, ← pow_add]; congr 2; omega

/-- **Schwartz–Zippel with grinding over a group** (`MB-decision.md` §6 `szN_escape_grind`): a
nonzero polynomial in the group's `k + 1` values of total degree `≤ d` vanishes, with the ground
draw's proof of work passing, with joint probability `≤ errG g d = 2^-g · d / 2^128`. -/
theorem grpEsc_sz {g k d : ℕ} (hg : g ≤ 64) {p : MvPolynomial (Fin (k + 1)) E2} (hp : p ≠ 0)
    (hd : p.totalDegree ≤ d) :
    grpEsc g k (fun ys ↦ MvPolynomial.eval (fun i : Fin (k + 1) ↦ ys.getD i 0) p = 0) ≤ errG g d := by
  classical
  rw [grpEsc_eq_card]
  have hev : ∀ w : Fin (k + 1) → E,
      MvPolynomial.eval (fun i : Fin (k + 1) ↦ (List.ofFn fun j ↦ e2OfE (w j)).getD i 0) p =
        MvPolynomial.eval (fun i ↦ e2OfE (w i)) p := by
    intro w
    refine congrArg (fun f ↦ MvPolynomial.eval f p) (funext fun i ↦ ?_)
    rw [List.getD_eq_getElem _ _ (by rw [List.length_ofFn]; exact i.isLt), List.getElem_ofFn]
  simp only [hev]
  have hc := card_grp_le hg hp hd
  have hE : (Fintype.card E : ℝ≥0∞) ^ (k + 1) = 2 ^ g * 2 ^ 128 * 2 ^ (64 - g + 192 * k) := by
    rw [card_E, Nat.cast_pow, Nat.cast_ofNat, ← pow_mul, ← pow_add, ← pow_add]; congr 1; omega
  rw [hE, ENNReal.mul_inv (by simp) (by simp), ENNReal.mul_inv (by simp) (by simp)]
  have h2 : ((2 : ℝ≥0∞) ^ (64 - g + 192 * k)) * (2 ^ (64 - g + 192 * k))⁻¹ = 1 :=
    ENNReal.mul_inv_cancel (by simp) (by simp)
  calc _ ≤ ((d * 2 ^ (64 - g + 192 * k) : ℕ) : ℝ≥0∞) *
        ((2 ^ g)⁻¹ * (2 ^ 128)⁻¹ * (2 ^ (64 - g + 192 * k))⁻¹) := by gcongr
    _ = (2 : ℝ≥0∞)⁻¹ ^ g * (d * ((2 : ℝ≥0∞) ^ 128)⁻¹) *
        ((2 : ℝ≥0∞) ^ (64 - g + 192 * k) * (2 ^ (64 - g + 192 * k))⁻¹) := by
      push_cast; rw [ENNReal.inv_pow]; ring
    _ = errG g d := by rw [h2, mul_one, errG]

end SZ

/-! ## The ledger's unit -/

/-- **An admitted group is within `εI`**: `8c ≤ 7·2^g` gives `errG g c ≤ 7·2^-131`. -/
theorem errG_le_εI {c g : ℕ} (h : Params.admits c g = true) :
    errG g c ≤ ((7 * (2 : ℝ≥0)⁻¹ ^ 131 : ℝ≥0) : ℝ≥0∞) := by
  have h1 := Params.group_le_εI h
  have e : errG g c = (((c : ℝ≥0) * (2 : ℝ≥0)⁻¹ ^ (128 + g) : ℝ≥0) : ℝ≥0∞) := by
    rw [errG, ENNReal.inv_pow]
    push_cast
    rw [pow_add]
    ring
  rw [e]
  exact_mod_cast h1

end Lvm6
