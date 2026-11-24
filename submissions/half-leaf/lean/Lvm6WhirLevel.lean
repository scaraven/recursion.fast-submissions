-- New for lvm6 (WP W1, first slice). The interface of a WHIR level with a next one, after leanVM
-- `formal/lean_vm/LeanVM/Protocol/Whir/Sound/{LevelMid,Escape}.lean` @ fdb317982: the next
-- commitment, the folded lane's high part, the out-of-domain point (a ground group), its value, the
-- query message (positions and `λ`, one ground group), the openings, and the glued claim on the next
-- word. The code facts (domains, message map, OOD separation, positions) are the parameters
-- `TailIface` (the second half of `OpeningIface`); the doom is the descent invariant `TViol`.
import Lvm6WhirRound
import LvmWhirCounting

/-!
# A level's interface (W1)

`TailIface F n n' m'`: the current level's domain `dom` (`n` columns) and degree `d` (every round's),
the next level's domain `dom'`, degree `d'` and `m'` lanes; a next tuple's message `key U`; its
polynomial on the current level `φ U` (the message part, linear, a function of `key U`); the high
part's polynomial `hp hi`; the candidate `cand hi U = φ U + hp hi` of degree `≤ d`; the OOD point
(`ko + 1` challenges) and its functional `ood z`, a function of `key`, separating distinct messages
at all but `δ |F|^ko` points; the positions `pos v` (`t` of them) from `kq + 1` challenges, with
`card_pos`: they all fall in `S` with probability `≤ (|S|/n)^t`.

* `glued L W z λ ps`, `gluedC σ y λ c`: the next level's weight and claim, `λ⁰` for the running
  claim, `λ¹` for the OOD claim, `λ^(k+2)` for the `k`-th consistency claim (leanVM's `gluedW`,
  `gluedV`).
* `nextB L A f B hi`: the descent predicate handed to the next level: if the candidate agrees with
  the folded word `f` on `≥ A` columns, it satisfies `B`.
* `tailP`: the program. **`tailSpec`**: from `TViol` for the folded word at `(A, d)` (the end of the
  level's fold rounds) to `TViol` for the next word at `(A', d')` with the glued weight and claim
  and `nextB`; the OOD group escapes within `eOod = 2^-gO C(L', 2) δ / |F|`, the query message
  within `eQry = 2^-gQ ((t + 1) L' / |F| + ((A − 1)/n)^t)`, `L' = jl n' A' d'`. Lead `0`.
-/

namespace Lvm6.Whir

open LeanVM.Parameters LeanVM.Protocol.Compile LeanVM.Protocol.Whir.Sound VerifierProgram Finset
  LeanVM.Protocol.Whir.AffineCombiner
open scoped ENNReal

variable {F : Type} [Field F] [Fintype F] [DecidableEq F]

/-- The one lane of a single-lane word. -/
def lane0 : Fin 0 → Bool := fun i ↦ i.elim0

theorem lane0_eq (r : Fin 0 → Bool) : r = lane0 := funext fun i ↦ i.elim0

/-- Evaluation of a single-lane tuple at a column. -/
noncomputable def evx {n : ℕ} (dom : Fin n ↪ F) (x : Fin n) : Tup F 0 →ₗ[F] F where
  toFun U := (U lane0).eval (dom x)
  map_add' U V := by simp
  map_smul' c U := by simp

/-- **The code facts of a level's interface.** -/
structure TailIface (F : Type) [Field F] [Fintype F] [DecidableEq F] (n n' m' : ℕ) where
  dom : Fin n ↪ F
  dom' : Fin n' ↪ F
  /-- The degree of the level's rounds and of the next level's. -/
  d : ℕ
  d' : ℕ
  /-- The message of a next tuple (the low parts every claim weighs). -/
  Msg : Type
  msgDec : DecidableEq Msg
  key : Tup F m' → Msg
  /-- A next tuple's polynomial on the current level, message part. -/
  φ : Tup F m' →ₗ[F] Tup F 0
  φ_key : ∀ U V, key U = key V → φ U = φ V
  /-- The high part: `nh` scalars, polynomial `hp hi`. -/
  nh : ℕ
  hp : List F → Tup F 0
  cand_deg : ∀ U hi, DegLE d' U → DegLE d (φ U + hp hi)
  /-- The OOD point, `ko + 1` challenges, and its functional. -/
  ko : ℕ
  ood : (Fin (ko + 1) → F) → Tup F m' →ₗ[F] F
  ood_key : ∀ z U V, key U = key V → ood z U = ood z V
  δ : ℕ
  ood_sep : ∀ U V, DegLE d' U → DegLE d' V → key U ≠ key V →
    (univ.filter fun z ↦ ood z U = ood z V).card ≤ δ * Fintype.card F ^ ko
  /-- The positions: `t` columns from `kq + 1` challenges. -/
  kq : ℕ
  t : ℕ
  pos : (Fin (kq + 1) → F) → Fin t → Fin n
  card_pos : ∀ S : Finset (Fin n), ((univ.filter fun v ↦ ∀ k, pos v k ∈ S).card : ℝ≥0∞) ≤
    (Fintype.card F : ℝ≥0∞) ^ (kq + 1) * ((S.card : ℝ≥0∞) / n) ^ t

variable {n n' m' : ℕ} (L : TailIface F n n' m')

/-- The candidate on the current level of a next tuple. -/
noncomputable def TailIface.cand (hi : List F) (U : Tup F m') : Tup F 0 := L.φ U + L.hp hi

/-- **The next level's weight**: `W ∘ φ + λ ood_z + Σ_k λ^(k+2) ev_{x_k} ∘ φ`. -/
noncomputable def glued (W : Tup F 0 →ₗ[F] F) (z : Fin (L.ko + 1) → F) (lam : F)
    (ps : Fin L.t → Fin n) : Tup F m' →ₗ[F] F :=
  W ∘ₗ L.φ + lam • L.ood z + ∑ k : Fin L.t, lam ^ ((k : ℕ) + 2) • (evx L.dom (ps k) ∘ₗ L.φ)

/-- **The next level's claim**: `σ + λ y + Σ_k λ^(k+2) c_k`. -/
def gluedC {t : ℕ} (σ y lam : F) (c : Fin t → F) : F :=
  σ + lam * y + ∑ k : Fin t, lam ^ ((k : ℕ) + 2) * c k

/-- **The descent predicate handed to the next level.** -/
def nextB (A : ℕ) (f : Wd F n 0) (B : Tup F 0 → Prop) (hi : List F) : Tup F m' → Prop :=
  fun U ↦ A ≤ (agree L.dom (L.cand hi U) f).card → B (L.cand hi U)

/-- The interface's output. -/
structure TailOut (F : Type) (ko t n : ℕ) where
  hi : List F
  z : Fin (ko + 1) → F
  y : F
  ps : Fin t → Fin n
  lam : F
  c : Fin t → F

variable (I : ChalIface F)

/-- The query message's positions and `λ`. -/
def qPos (qv : List F) : Fin L.t → Fin n := L.pos fun k ↦ qv.getD k 0

def qLam (qv : List F) : F := qv.getD (L.kq + 1) 0

/-- **A level's interface** (FORMAT6 v2.2.1 §6.6 order): the high part, the next commitment
`(ht, wd)`, a bind, the OOD group (`gO` bits), its value, the query message (`gQ` bits: positions,
then `λ`), the openings of commitment `i`, and the values `vals` the verifier derives from the
opened rows. -/
def tailP (ht wd i gO gQ : ℕ)
    (vals : List F → (Fin L.t → Fin n) → List (List K) → Fin L.t → F) :
    VerifierProgram (TailOut F L.ko L.t n) :=
  readFs I L.nh >>= fun hi ↦ VerifierProgram.readCommitment ht wd >>= fun _ ↦ I.sep >>= fun _ ↦
  I.grp gO L.ko >>= fun zv ↦ readF I >>= fun y ↦
  I.grp gQ (L.kq + 1) >>= fun qv ↦
  queryOpenings i (List.ofFn fun k ↦ (qPos L qv k : ℕ)) >>= fun rows ↦
  pure ⟨hi, gv zv, y, qPos L qv, qLam L qv, vals hi (qPos L qv) rows⟩

/-- The OOD group's escape: `2^-gO · C(L', 2) δ / |F|`. -/
noncomputable def eOod (g Lst : ℕ) : ℝ≥0∞ :=
  (2 : ℝ≥0∞)⁻¹ ^ g * ((Lst.choose 2 * L.δ : ℕ) : ℝ≥0∞) / (Fintype.card F : ℝ≥0∞)

/-- The query message's escape: `2^-gQ ((t + 1) L' / |F| + ((A − 1)/n)^t)`. -/
noncomputable def eQry (g Lst A : ℕ) : ℝ≥0∞ :=
  (2 : ℝ≥0∞)⁻¹ ^ g * ((((L.t + 1) * Lst : ℕ) : ℝ≥0∞) / (Fintype.card F : ℝ≥0∞) +
    (((A - 1 : ℕ) : ℝ≥0∞) / n) ^ L.t)

/-- The doom at the start of the interface. -/
def tailPre (i : ℕ) (Rd : List (ℕ × ℕ × Word) → Prop) (cur : List (ℕ × ℕ × Word) → Wd F n 0)
    (W : Tup F 0 →ₗ[F] F) (σ : F) (A : ℕ) (B : List (ℕ × ℕ × Word) → Tup F 0 → Prop)
    (cs : List (ℕ × ℕ × Word)) : Prop :=
  cs.length = i + 1 ∧ Rd cs ∧ TViol L.dom (cur cs) W σ A L.d (B cs)

/-- The doom at the end of the interface: the next level's. -/
def tailPost (cur : List (ℕ × ℕ × Word) → Wd F n 0) (nxt : List (ℕ × ℕ × Word) → Wd F n' m')
    (W : Tup F 0 →ₗ[F] F) (σ : F) (A A' : ℕ) (B : List (ℕ × ℕ × Word) → Tup F 0 → Prop)
    (o : TailOut F L.ko L.t n) (cs : List (ℕ × ℕ × Word)) : Prop :=
  TViol L.dom' (nxt cs) (glued L W o.z o.lam o.ps) (gluedC σ o.y o.lam o.c) A' L.d'
    (nextB L A (cur cs) (B cs) o.hi)

/-! ## The two groups' counts -/

/-- **OOD separation**: members of the next list with distinct messages differ at `z`. -/
def OodOK (z : Fin (L.ko + 1) → F) (g : Wd F n' m') (A' : ℕ) : Prop :=
  ∀ U ∈ tupleList L.dom' g A' L.d', ∀ V ∈ tupleList L.dom' g A' L.d', L.key U ≠ L.key V →
    L.ood z U ≠ L.ood z V

open Classical in
/-- **The OOD group's bad points**: at most `C(L', 2) δ |F|^ko`. -/
theorem card_oodBad_le (g : Wd F n' m') (A' : ℕ) (hgap : n' * L.d' < A' * A') :
    (univ.filter fun z ↦ ¬ OodOK L z g A').card ≤
      (jl n' A' L.d').choose 2 * L.δ * Fintype.card F ^ L.ko := by
  set Ls := tupleList L.dom' g A' L.d'
  let bad : Finset (Tup F m') → Finset (Fin (L.ko + 1) → F) := fun s ↦
    univ.filter fun z ↦ ∃ U ∈ s, ∃ V ∈ s, L.key U ≠ L.key V ∧ L.ood z U = L.ood z V
  have hsub : (univ.filter fun z ↦ ¬ OodOK L z g A') ⊆ (Ls.powersetCard 2).biUnion bad := by
    intro z hz
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, OodOK, not_forall, not_not,
      exists_prop] at hz
    obtain ⟨U, hU, V, hV, hk, he⟩ := hz
    have hne : U ≠ V := fun h ↦ hk (h ▸ rfl)
    refine Finset.mem_biUnion.mpr ⟨{U, V}, Finset.mem_powersetCard.mpr ⟨?_, ?_⟩, ?_⟩
    · intro x hx
      rcases Finset.mem_insert.mp hx with rfl | hx
      · exact hU
      · rw [Finset.mem_singleton.mp hx]; exact hV
    · exact Finset.card_pair hne
    · simp only [bad, Finset.mem_filter, Finset.mem_univ, true_and]
      exact ⟨U, by simp, V, by simp, hk, he⟩
  have hbad : ∀ s ∈ Ls.powersetCard 2, (bad s).card ≤ L.δ * Fintype.card F ^ L.ko := by
    intro s hs
    obtain ⟨hsL, hs2⟩ := Finset.mem_powersetCard.mp hs
    obtain ⟨U, V, hne, rfl⟩ := Finset.card_eq_two.mp hs2
    have hU := (mem_tupleList _ _ _ _ U).mp (hsL (by simp))
    have hV := (mem_tupleList _ _ _ _ V).mp (hsL (by simp))
    by_cases hk : L.key U = L.key V
    · refine le_trans (le_of_eq (Finset.card_eq_zero.mpr ?_)) (Nat.zero_le _)
      refine Finset.filter_eq_empty_iff.mpr fun z _ ⟨a, ha, b, hb, hab, _⟩ ↦ hab ?_
      simp only [Finset.mem_insert, Finset.mem_singleton] at ha hb
      rcases ha with rfl | rfl <;> rcases hb with rfl | rfl <;> simp [hk]
    · refine le_trans (Finset.card_le_card fun z hz ↦ ?_) (L.ood_sep U V hU.1 hV.1 hk)
      simp only [bad, Finset.mem_filter, Finset.mem_univ, true_and] at hz ⊢
      obtain ⟨a, ha, b, hb, hab, he⟩ := hz
      simp only [Finset.mem_insert, Finset.mem_singleton] at ha hb
      rcases ha with rfl | rfl <;> rcases hb with rfl | rfl
      · exact absurd rfl hab
      · exact he
      · exact he.symm
      · exact absurd rfl hab
  calc (univ.filter fun z ↦ ¬ OodOK L z g A').card
      ≤ ((Ls.powersetCard 2).biUnion bad).card := Finset.card_le_card hsub
    _ ≤ ∑ s ∈ Ls.powersetCard 2, (bad s).card := Finset.card_biUnion_le
    _ ≤ ∑ _s ∈ Ls.powersetCard 2, L.δ * Fintype.card F ^ L.ko := Finset.sum_le_sum hbad
    _ = Ls.card.choose 2 * (L.δ * Fintype.card F ^ L.ko) := by
        rw [Finset.sum_const, Finset.card_powersetCard, smul_eq_mul]
    _ ≤ (jl n' A' L.d').choose 2 * (L.δ * Fintype.card F ^ L.ko) :=
        Nat.mul_le_mul_right _ (Nat.choose_le_choose 2 (card_tupleList_le_jl L.dom' g A' L.d' hgap))
    _ = _ := by ring

omit [Fintype F] [DecidableEq F] in
theorem mem_agree0 {dom : Fin n ↪ F} {P : Tup F 0} {f : Wd F n 0} {x : Fin n} :
    x ∈ agree dom P f ↔ (P lane0).eval (dom x) = f lane0 x := by
  rw [mem_agree]
  exact ⟨fun h ↦ h lane0, fun h r ↦ by rw [lane0_eq r]; exact h⟩

/-- The coefficients of the glued claim's discrepancy as a polynomial in `λ`. -/
noncomputable def coefQ (W : Tup F 0 →ₗ[F] F) (σ y : F) (z : Fin (L.ko + 1) → F) (ps : Fin L.t → Fin n)
    (c : Fin L.t → F) (U : Tup F m') : Fin (L.t + 2) → F :=
  Fin.cons (W (L.φ U) - σ) (Fin.cons (L.ood z U - y) fun k ↦ evx L.dom (ps k) (L.φ U) - c k)

/-- The glued claim's discrepancy is the polynomial `Σ_j coefQ_j λ^j`. -/
theorem glued_sub (W : Tup F 0 →ₗ[F] F) (σ y lam : F) (z : Fin (L.ko + 1) → F)
    (ps : Fin L.t → Fin n) (c : Fin L.t → F) (U : Tup F m') :
    glued L W z lam ps U - gluedC σ y lam c =
      ∑ j : Fin (L.t + 2), coefQ L W σ y z ps c U j * lam ^ (j : ℕ) := by
  rw [Fin.sum_univ_succ, Fin.sum_univ_succ]
  simp only [glued, gluedC, coefQ, LinearMap.add_apply, LinearMap.smul_apply, LinearMap.sum_apply,
    LinearMap.coe_comp, Function.comp_apply, smul_eq_mul, Fin.cons_zero,
    Fin.cons_succ, Fin.val_zero, Fin.val_succ, pow_zero, mul_one, zero_add, pow_one]
  have hs : ∑ x : Fin L.t, ((evx L.dom (ps x)) (L.φ U) - c x) * lam ^ ((x : ℕ) + 1 + 1) =
      ∑ k : Fin L.t, lam ^ ((k : ℕ) + 2) * evx L.dom (ps k) (L.φ U) -
        ∑ k : Fin L.t, lam ^ ((k : ℕ) + 2) * c k := by
    rw [← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun k _ ↦ by ring
  rw [hs]
  ring

/-- The query message's semantic claim values: the folded word minus the high part. -/
noncomputable def qVals (f : Wd F n 0) (hi : List F) (ps : Fin L.t → Fin n) : Fin L.t → F :=
  fun k ↦ f lane0 (ps k) - (L.hp hi lane0).eval (L.dom (ps k))

/-- The query message's bad values `(positions' challenges, λ)`. -/
def QBad (f : Wd F n 0) (g : Wd F n' m') (W : Tup F 0 →ₗ[F] F) (σ y : F) (A A' : ℕ)
    (B : Tup F 0 → Prop) (hi : List F) (z : Fin (L.ko + 1) → F) (v : Fin (L.kq + 1) → F)
    (lam : F) : Prop :=
  ¬ TViol L.dom' g (glued L W z lam (L.pos v)) (gluedC σ y lam (qVals L f hi (L.pos v))) A' L.d'
    (nextB L A f B hi)

open Classical in
/-- **The query message's bad values**: at most `|F|^(kq+1) (t + 1) L' + |F| |F|^(kq+1) ((A − 1)/n)^t`
pairs (positions' challenges, `λ`): a list member with a nonzero discrepancy polynomial has at most
`t + 1` roots `λ`; a member with zero discrepancy is the one message consistent with the OOD answer,
of agreement `< A` with the folded word, and all positions fall in its agreement set. -/
theorem card_qryBad_le (f : Wd F n 0) (g : Wd F n' m') (W : Tup F 0 →ₗ[F] F)
    (hWH : ∀ hi, W (L.hp hi) = 0) (σ y : F) (A A' : ℕ) (B : Tup F 0 → Prop) (hi : List F)
    (z : Fin (L.ko + 1) → F) (hv : TViol L.dom f W σ A L.d B) (hood : OodOK L z g A')
    (hgap : n' * L.d' < A' * A') :
    ((univ.filter fun u : Fin (L.kq + 2) → F ↦
        QBad L f g W σ y A A' B hi z (Fin.init u) (u (Fin.last _))).card : ℝ≥0∞) ≤
      (Fintype.card F : ℝ≥0∞) ^ (L.kq + 1) * (((L.t + 1) * jl n' A' L.d' : ℕ) : ℝ≥0∞) +
        Fintype.card F * ((Fintype.card F : ℝ≥0∞) ^ (L.kq + 1) *
          (((A - 1 : ℕ) : ℝ≥0∞) / n) ^ L.t) := by
  set Ls := tupleList L.dom' g A' L.d'
  set co := fun (v : Fin (L.kq + 1) → F) (U : Tup F m') ↦
    coefQ L W σ y z (L.pos v) (qVals L f hi (L.pos v)) U
  let PosBad : (Fin (L.kq + 1) → F) → Prop := fun v ↦
    ∃ U ∈ Ls, nextB L A f B hi U ∧ co v U = 0
  -- a witness of a bad pair
  have hwit : ∀ v lam, QBad L f g W σ y A A' B hi z v lam →
      ∃ U ∈ Ls, nextB L A f B hi U ∧ ∑ j : Fin (L.t + 2), co v U j * lam ^ (j : ℕ) = 0 := by
    intro v lam hb
    simp only [QBad, TViol, not_forall, not_not, exists_prop] at hb
    obtain ⟨U, hU, hag, hB, he⟩ := hb
    refine ⟨U, (mem_tupleList _ _ _ _ U).mpr ⟨hU, hag⟩, hB, ?_⟩
    rw [← glued_sub, he, sub_self]
  -- per positions: at most (t + 1) |Ls| + |F| [PosBad v] values λ
  have hlam : ∀ v, ((univ.filter fun lam ↦ QBad L f g W σ y A A' B hi z v lam).card : ℝ≥0∞) ≤
      (((L.t + 1) * jl n' A' L.d' : ℕ) : ℝ≥0∞) + (if PosBad v then (Fintype.card F : ℝ≥0∞) else 0) := by
    intro v
    let R : Tup F m' → Finset F := fun U ↦
      univ.filter fun lam ↦ ∑ j : Fin (L.t + 2), co v U j * lam ^ (j : ℕ) = 0
    have hsub : (univ.filter fun lam ↦ QBad L f g W σ y A A' B hi z v lam) ⊆
        ((Ls.filter fun U ↦ co v U ≠ 0).biUnion R) ∪ (if PosBad v then univ else ∅) := by
      intro lam hl
      obtain ⟨U, hU, hB, hz⟩ := hwit v lam (Finset.mem_filter.mp hl).2
      by_cases hc : co v U = 0
      · have hp : PosBad v := ⟨U, hU, hB, hc⟩
        simp [hp]
      · refine Finset.mem_union_left _ (Finset.mem_biUnion.mpr ⟨U, Finset.mem_filter.mpr ⟨hU, hc⟩, ?_⟩)
        simp only [R, Finset.mem_filter, Finset.mem_univ, true_and]
        exact hz
    have hR : ∀ U ∈ Ls.filter fun U ↦ co v U ≠ 0, (R U).card ≤ L.t + 1 := by
      intro U hU
      have hne : ∃ j, co v U j ≠ 0 := by
        by_contra hall
        simp only [not_exists, ne_eq, not_not] at hall
        exact (Finset.mem_filter.mp hU).2 (funext hall)
      exact LeanVM.Protocol.Whir.card_powerBatch_eq_zero_le (co v U) hne
    have h1 : ((Ls.filter fun U ↦ co v U ≠ 0).biUnion R).card ≤ (L.t + 1) * jl n' A' L.d' :=
      calc _ ≤ ∑ U ∈ Ls.filter fun U ↦ co v U ≠ 0, (R U).card := Finset.card_biUnion_le
        _ ≤ ∑ _U ∈ Ls.filter fun U ↦ co v U ≠ 0, (L.t + 1) := Finset.sum_le_sum hR
        _ = (Ls.filter fun U ↦ co v U ≠ 0).card * (L.t + 1) := by rw [Finset.sum_const, smul_eq_mul]
        _ ≤ jl n' A' L.d' * (L.t + 1) := Nat.mul_le_mul_right _
            ((Finset.card_filter_le _ _).trans (card_tupleList_le_jl L.dom' g A' L.d' hgap))
        _ = _ := by ring
    calc ((univ.filter fun lam ↦ QBad L f g W σ y A A' B hi z v lam).card : ℝ≥0∞)
        ≤ (((Ls.filter fun U ↦ co v U ≠ 0).biUnion R ∪ (if PosBad v then univ else ∅)).card : ℝ≥0∞) := by
          exact_mod_cast Finset.card_le_card hsub
      _ ≤ (((Ls.filter fun U ↦ co v U ≠ 0).biUnion R).card : ℝ≥0∞) +
            ((if PosBad v then univ else ∅ : Finset F).card : ℝ≥0∞) := by
          exact_mod_cast Finset.card_union_le _ _
      _ ≤ _ := add_le_add (by exact_mod_cast h1) (by split_ifs <;> simp)
  -- the positions with a zero-discrepancy member all fall in one agreement set of size < A
  have hpos : ((univ.filter PosBad).card : ℝ≥0∞) ≤
      (Fintype.card F : ℝ≥0∞) ^ (L.kq + 1) * (((A - 1 : ℕ) : ℝ≥0∞) / n) ^ L.t := by
    by_cases h0 : ∃ U₀ ∈ Ls, nextB L A f B hi U₀ ∧ W (L.φ U₀) = σ ∧ L.ood z U₀ = y
    · obtain ⟨U₀, hU₀, hB₀, hW₀, hy₀⟩ := h0
      set S := agree L.dom (L.cand hi U₀) f
      have hU₀' := (mem_tupleList _ _ _ _ U₀).mp hU₀
      have hS : S.card ≤ A - 1 := by
        by_contra hlt
        have hA : A ≤ S.card := by omega
        refine hv _ (L.cand_deg U₀ hi hU₀'.1) hA (hB₀ hA) ?_
        simp only [map_add, hWH, add_zero, hW₀]
      have hsub : univ.filter PosBad ⊆ univ.filter fun v ↦ ∀ k, L.pos v k ∈ S := by
        intro v hv'
        obtain ⟨U, hU, _, hc⟩ := (Finset.mem_filter.mp hv').2
        have hc0 := congrFun hc 0
        have hc1 := congrFun hc 1
        simp only [co, coefQ, Fin.cons_zero, Pi.zero_apply, sub_eq_zero] at hc0
        have hkey : L.key U = L.key U₀ := by
          by_contra hk
          have := congrFun hc (Fin.succ 0)
          simp only [co, coefQ, Fin.cons_succ, Fin.cons_zero, Pi.zero_apply, sub_eq_zero] at this
          exact hood U hU U₀ hU₀ hk (this.trans hy₀.symm)
        have hφ := L.φ_key U U₀ hkey
        simp only [Finset.mem_filter, Finset.mem_univ, true_and]
        intro k
        have := congrFun hc k.succ.succ
        simp only [co, coefQ, Fin.cons_succ, Pi.zero_apply, sub_eq_zero, qVals, evx,
          LinearMap.coe_mk, AddHom.coe_mk] at this
        rw [mem_agree0]
        simp only [TailIface.cand, Pi.add_apply, Polynomial.eval_add, ← hφ, this]
        ring
      calc ((univ.filter PosBad).card : ℝ≥0∞)
          ≤ ((univ.filter fun v ↦ ∀ k, L.pos v k ∈ S).card : ℝ≥0∞) := by
            exact_mod_cast Finset.card_le_card hsub
        _ ≤ (Fintype.card F : ℝ≥0∞) ^ (L.kq + 1) * ((S.card : ℝ≥0∞) / n) ^ L.t := L.card_pos S
        _ ≤ _ := by gcongr
    · have : univ.filter PosBad = ∅ := by
        refine Finset.filter_eq_empty_iff.mpr fun v _ ⟨U, hU, hB, hc⟩ ↦ h0 ⟨U, hU, hB, ?_, ?_⟩
        · have := congrFun hc 0
          simpa [co, coefQ, sub_eq_zero] using this
        · have := congrFun hc (Fin.succ 0)
          simpa [co, coefQ, sub_eq_zero] using this
      rw [this]
      simp
  -- sum over the positions' challenges
  have hsplit : (univ.filter fun u : Fin (L.kq + 2) → F ↦
        QBad L f g W σ y A A' B hi z (Fin.init u) (u (Fin.last _))).card =
      ∑ v : Fin (L.kq + 1) → F, (univ.filter fun lam ↦ QBad L f g W σ y A A' B hi z v lam).card := by
    rw [Finset.card_filter, ← (Fin.snocEquiv fun _ ↦ F).sum_comp, Fintype.sum_prod_type,
      Finset.sum_comm]
    refine Finset.sum_congr rfl fun v _ ↦ ?_
    rw [Finset.card_filter]
    refine Finset.sum_congr rfl fun lam _ ↦ ?_
    simp [Fin.snocEquiv, Fin.init_snoc, Fin.snoc_last]
  rw [hsplit, Nat.cast_sum]
  calc ∑ v : Fin (L.kq + 1) → F,
        ((univ.filter fun lam ↦ QBad L f g W σ y A A' B hi z v lam).card : ℝ≥0∞)
      ≤ ∑ v : Fin (L.kq + 1) → F, ((((L.t + 1) * jl n' A' L.d' : ℕ) : ℝ≥0∞) +
          (if PosBad v then (Fintype.card F : ℝ≥0∞) else 0)) := Finset.sum_le_sum fun v _ ↦ hlam v
    _ = (Fintype.card F : ℝ≥0∞) ^ (L.kq + 1) * (((L.t + 1) * jl n' A' L.d' : ℕ) : ℝ≥0∞) +
          Fintype.card F * ((univ.filter PosBad).card : ℝ≥0∞) := by
        rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fun,
          Fintype.card_fin, nsmul_eq_mul, Finset.sum_ite, Finset.sum_const_zero, add_zero,
          Finset.sum_const, nsmul_eq_mul, mul_comm (Fintype.card F : ℝ≥0∞)]
        push_cast
        ring
    _ ≤ _ := by gcongr

omit [Field F] [DecidableEq F] in
/-- A commitment appends its word. -/
theorem commits_append_commit (h : List Ev) (ht w : ℕ) (word : Word) :
    commits (h ++ [Ev.commit ht w word]) = commits h ++ [(ht, w, word)] := by
  induction h with
  | nil => rfl
  | cons e h ih => cases e <;> simp [commits, ih]

theorem ennr_div_pow (q : ℕ) (hq : q ≠ 0) (k : ℕ) (a : ℝ≥0∞) :
    a * (q : ℝ≥0∞) ^ k / (q : ℝ≥0∞) ^ (k + 1) = a / q := by
  rw [pow_succ, mul_comm ((q : ℝ≥0∞) ^ k) (q : ℝ≥0∞),
    ENNReal.mul_div_mul_right _ _ (by simp [hq]) (by simp)]

theorem ennr_div_pow' (q : ℕ) (hq : q ≠ 0) (k : ℕ) (a b : ℝ≥0∞) :
    ((q : ℝ≥0∞) ^ (k + 1) * a + q * ((q : ℝ≥0∞) ^ (k + 1) * b)) / (q : ℝ≥0∞) ^ (k + 2) =
      a / q + b := by
  have hq0 : (q : ℝ≥0∞) ≠ 0 := by simp [hq]
  have hqt : (q : ℝ≥0∞) ≠ ⊤ := by simp
  have hk0 : (q : ℝ≥0∞) ^ (k + 1) ≠ 0 := pow_ne_zero _ hq0
  have hkt : (q : ℝ≥0∞) ^ (k + 1) ≠ ⊤ := ENNReal.pow_ne_top hqt
  rw [ENNReal.add_div, show (q : ℝ≥0∞) ^ (k + 2) = (q : ℝ≥0∞) ^ (k + 1) * q from pow_succ _ _,
    ENNReal.mul_div_mul_left _ _ hk0 hkt, ← mul_assoc, mul_comm (q : ℝ≥0∞),
    mul_comm (_ * _) b, ENNReal.mul_div_cancel_right (mul_ne_zero hk0 hq0) (ENNReal.mul_ne_top hkt hqt)]

variable {εmax : ℝ≥0∞}

/-- **A WHIR level's interface, keeping its frame**: `tailSpec` with the commitments' length
`i + 2` and `Rd` also in the postcondition (as `roundSpecJ` keeps `J`), for the ladder. -/
noncomputable def tailSpecJ (ht wd i gO gQ : ℕ) (hgO : gO ≤ I.gmax) (hgQ : gQ ≤ I.gmax)
    (vals : List F → (Fin L.t → Fin n) → List (List K) → Fin L.t → F)
    (Rd : List (ℕ × ℕ × Word) → Prop) (cur : List (ℕ × ℕ × Word) → Wd F n 0)
    (nxt : List (ℕ × ℕ × Word) → Wd F n' m') (W : Tup F 0 →ₗ[F] F)
    (hWH : ∀ hi, W (L.hp hi) = 0) (σ : F) (A A' : ℕ)
    (B : List (ℕ × ℕ × Word) → Tup F 0 → Prop)
    (hstab : ∀ cs c, cs.length = i + 1 → Rd cs →
      cur (cs ++ [c]) = cur cs ∧ B (cs ++ [c]) = B cs ∧ Rd (cs ++ [c]))
    (hread : ∀ h, (commits h).length = i + 2 → Rd (commits h) → ∀ ps rows,
      answer h i (List.ofFn fun k ↦ (ps k : ℕ)) = some rows → ∀ hi,
        vals hi ps rows = fun k ↦ cur (commits h) lane0 (ps k) - (L.hp hi lane0).eval (L.dom (ps k)))
    (hgap : n' * L.d' < A' * A')
    (heO : eOod L gO (jl n' A' L.d') < 1) (heOT : eOod L gO (jl n' A' L.d') ≤ εmax)
    (heQ : eQry L gQ (jl n' A' L.d') A < 1) (heQT : eQry L gQ (jl n' A' L.d') A ≤ εmax) :
    Spec (tailP L I ht wd i gO gQ vals) (fun h ↦ tailPre L i Rd cur W σ A B (commits h))
      (fun o h ↦ ((commits h).length = i + 2 ∧ Rd (commits h)) ∧
        tailPost L cur nxt W σ A A' B o (commits h)) εmax 0 0 := by
  classical
  have h0 : (0 : ℝ≥0∞) ≤ εmax := by positivity
  have hq : Fintype.card F ≠ 0 := Fintype.card_ne_zero
  let D1 : List (ℕ × ℕ × Word) → Prop := fun cs ↦
    cs.length = i + 2 ∧ Rd cs ∧ TViol L.dom (cur cs) W σ A L.d (B cs)
  unfold tailP
  refine ((readFsSpec I (Inv := fun cs ↦ tailPre L i Rd cur W σ A B cs) (T := 0) h0 h0 L.nh).mono
    (fun _ h ↦ h) (fun _ _ h ↦ h) le_rfl (by split_ifs <;> simp) le_rfl).bind' fun hi ↦ ?_
  refine (Spec.commitP (Post := fun _ h ↦ D1 (commits h)) ht wd
    (fun h₀ word hP _ ↦ ?_) h0).bind' fun _ ↦ ?_
  · rw [commits_append_commit]
    obtain ⟨hl, hR, hT⟩ := hP
    obtain ⟨hc, hb, hr⟩ := hstab _ (ht, wd, word) hl hR
    exact ⟨by simp [hl], hr, by rw [hc, hb]; exact hT⟩
  refine (I.sepSpec D1 εmax 0).bind' fun _ ↦ ?_
  -- the OOD group
  refine ((I.grpSpec gO L.ko hgO D1 (fun u cs ↦ D1 cs ∧ OodOK L u (nxt cs) A')
    (eOod L gO (jl n' A' L.d')) heO fun cs hI ↦ ?_).mono (fun _ h ↦ h) (fun _ _ h ↦ h) heOT le_rfl
    le_rfl).bind' fun zv ↦ ?_
  · unfold grpE
    calc _ ≤ (2 : ℝ≥0∞)⁻¹ ^ gO * ((((jl n' A' L.d').choose 2 * L.δ : ℕ) : ℝ≥0∞) *
            (Fintype.card F : ℝ≥0∞) ^ L.ko) / (Fintype.card F : ℝ≥0∞) ^ (L.ko + 1) := by
          gcongr
          refine le_trans (Nat.cast_le.mpr (Finset.card_le_card
            (t := univ.filter fun z ↦ ¬ OodOK L z (nxt cs) A') fun u hu ↦ ?_)) ?_
          · simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hu ⊢
            exact fun h ↦ hu ⟨hI, h⟩
          · exact_mod_cast card_oodBad_le L (nxt cs) A' hgap
      _ = eOod L gO (jl n' A' L.d') := by rw [← mul_assoc, ennr_div_pow _ hq, eOod]
  -- its value
  refine ((readFSpec I (Inv := fun cs ↦ D1 cs ∧ OodOK L (gv zv) (nxt cs) A') h0).mono
    (fun _ h ↦ h) (fun _ _ h ↦ h) le_rfl le_rfl le_rfl).bind' fun y ↦ ?_
  -- the query message
  refine ((I.grpSpec gQ (L.kq + 1) hgQ (fun cs ↦ D1 cs ∧ OodOK L (gv zv) (nxt cs) A')
    (fun u cs ↦ D1 cs ∧ ¬ QBad L (cur cs) (nxt cs) W σ y A A' (B cs) hi (gv zv) (Fin.init u)
      (u (Fin.last (L.kq + 1)))) (eQry L gQ (jl n' A' L.d') A) heQ fun cs hI ↦ ?_).mono
    (fun _ h ↦ h) (fun _ _ h ↦ h) heQT le_rfl le_rfl).bind' fun qv ↦ ?_
  · unfold grpE
    calc _ ≤ (2 : ℝ≥0∞)⁻¹ ^ gQ * ((Fintype.card F : ℝ≥0∞) ^ (L.kq + 1) *
            (((L.t + 1) * jl n' A' L.d' : ℕ) : ℝ≥0∞) + Fintype.card F *
              ((Fintype.card F : ℝ≥0∞) ^ (L.kq + 1) * (((A - 1 : ℕ) : ℝ≥0∞) / n) ^ L.t)) /
            (Fintype.card F : ℝ≥0∞) ^ (L.kq + 1 + 1) := by
          gcongr
          refine le_trans (Nat.cast_le.mpr (Finset.card_le_card
            (t := univ.filter fun u : Fin (L.kq + 2) → F ↦ QBad L (cur cs) (nxt cs)
              W σ y A A' (B cs) hi (gv zv) (Fin.init u) (u (Fin.last (L.kq + 1))))
            fun u hu ↦ ?_)) ?_
          · simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hu ⊢
            by_contra hn
            exact hu ⟨hI.1, hn⟩
          · exact card_qryBad_le L (cur cs) (nxt cs) W hWH σ y A A' (B cs) hi (gv zv) hI.1.2.2
              hI.2 hgap
      _ = eQry L gQ (jl n' A' L.d') A := by
          rw [mul_div_assoc, ennr_div_pow' _ hq, eQry]
  -- the openings
  let o : List (List K) → TailOut F L.ko L.t n := fun rows ↦
    ⟨hi, gv zv, y, qPos L qv, qLam L qv, vals hi (qPos L qv) rows⟩
  refine ((Spec.ofNoMove (p := queryOpenings i (List.ofFn fun k ↦ (qPos L qv k : ℕ)))
    (Pre := fun h ↦ D1 (commits h) ∧ ¬ QBad L (cur (commits h)) (nxt (commits h)) W σ y A A'
      (B (commits h)) hi (gv zv) (Fin.init (gv (k := L.kq + 2) qv)) (gv (k := L.kq + 2) qv (Fin.last (L.kq + 1))))
    (Post := fun rows h ↦ ((commits h).length = i + 2 ∧ Rd (commits h)) ∧
      tailPost L cur nxt W σ A A' B (o rows) (commits h)) (T := 0)
    (noMv_queryP _ _).noMove (e := 0) (by norm_num) fun h₀ hP ↦ ?_).mono (fun _ h ↦ h)
    (fun _ _ h ↦ h) le_rfl (by simp) le_rfl).bind' fun rows ↦ ?_
  · unfold escRet
    rw [retExp_queryP]
    split
    · rename_i rows hans
      rw [List.append_nil] at hans
      have hv := hread h₀ hP.1.1 hP.1.2.1 (qPos L qv) rows hans hi
      have hpost : ((commits (h₀ ++ [] ++ [Ev.query rows])).length = i + 2 ∧
          Rd (commits (h₀ ++ [] ++ [Ev.query rows]))) ∧
          tailPost L cur nxt W σ A A' B (o rows) (commits (h₀ ++ [] ++ [Ev.query rows])) := by
        rw [List.append_nil, commits_append_query]
        refine ⟨⟨hP.1.1, hP.1.2.1⟩, ?_⟩
        have hq := hP.2
        simp only [QBad, not_not] at hq
        simp only [tailPost, o, hv]
        exact hq
      simp only [List.append_nil] at hpost
      simp [hpost]
    · exact le_rfl
  · exact Spec.ret (Post := fun o h ↦ ((commits h).length = i + 2 ∧ Rd (commits h)) ∧
      tailPost L cur nxt W σ A A' B o (commits h)) (o rows)

/-- **A WHIR level's interface** (Annex B `thm:rbr`, "The level interface", in the doom calculus):
from the descent invariant for the folded word `cur` at `(A, d)`, the program returns with the
descent invariant for the next word `nxt` at `(A', d')`, the glued weight and claim, and the
predicate `nextB`. Hypotheses: `Rd` and `cur`, `B` survive the next commitment; `vals` reads the
folded word minus the high part at the queried columns (`hread`); the weight ignores the high
part (`hWH`); the Johnson gap at the next level; the two groups' escapes below `1` and `εmax`. -/
noncomputable def tailSpec (ht wd i gO gQ : ℕ) (hgO : gO ≤ I.gmax) (hgQ : gQ ≤ I.gmax)
    (vals : List F → (Fin L.t → Fin n) → List (List K) → Fin L.t → F)
    (Rd : List (ℕ × ℕ × Word) → Prop) (cur : List (ℕ × ℕ × Word) → Wd F n 0)
    (nxt : List (ℕ × ℕ × Word) → Wd F n' m') (W : Tup F 0 →ₗ[F] F)
    (hWH : ∀ hi, W (L.hp hi) = 0) (σ : F) (A A' : ℕ)
    (B : List (ℕ × ℕ × Word) → Tup F 0 → Prop)
    (hstab : ∀ cs c, cs.length = i + 1 → Rd cs →
      cur (cs ++ [c]) = cur cs ∧ B (cs ++ [c]) = B cs ∧ Rd (cs ++ [c]))
    (hread : ∀ h, (commits h).length = i + 2 → Rd (commits h) → ∀ ps rows,
      answer h i (List.ofFn fun k ↦ (ps k : ℕ)) = some rows → ∀ hi,
        vals hi ps rows = fun k ↦ cur (commits h) lane0 (ps k) - (L.hp hi lane0).eval (L.dom (ps k)))
    (hgap : n' * L.d' < A' * A')
    (heO : eOod L gO (jl n' A' L.d') < 1) (heOT : eOod L gO (jl n' A' L.d') ≤ εmax)
    (heQ : eQry L gQ (jl n' A' L.d') A < 1) (heQT : eQry L gQ (jl n' A' L.d') A ≤ εmax) :
    Spec (tailP L I ht wd i gO gQ vals) (fun h ↦ tailPre L i Rd cur W σ A B (commits h))
      (fun o h ↦ tailPost L cur nxt W σ A A' B o (commits h)) εmax 0 0 :=
  (tailSpecJ L I ht wd i gO gQ hgO hgQ vals Rd cur nxt W hWH σ A A' B hstab hread hgap heO heOT
    heQ heQT).mono (fun _ h ↦ h) (fun _ _ h ↦ h.2) le_rfl le_rfl le_rfl

end Lvm6.Whir
