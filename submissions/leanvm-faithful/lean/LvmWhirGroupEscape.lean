-- Ported from leanVM `formal/lean_vm/LeanVM/Protocol/Whir/Sound/GroupEscape.lean` (formal rev 40f877dc) as
-- `LvmWhirGroupEscape` for lvm (WP-7). Changed for the unique-decoding regime: the out-of-domain group
-- (`escRet_sampleN_le`) is cut; `escRet_queryFrag_le` becomes `escRet_queryFrag_le_ud` (the one candidate from the
-- list bound, escape `eQueryUd`); the final level's group starts from the residual's doom `FinViol`
-- (`escRet_queryFrag_le_finViol`); the positions are `samplePositions per` of commitment index `c`.
/-
  LeanVM.Protocol.Whir.Sound.GroupEscape

  The escape expectations of a WHIR level's query group (positions, `λ`, openings), in the form
  `Spec.ofNoMove` consumes, on a level with a next commitment and on the final level.
-/
import LvmWhirProb
import LvmWhirProg
import LvmWhirCounting
import LvmWhirFolds

-- ===== merged from `LvmWhirQueries` (GOLF module merge: `LvmWhirQueries.lean` is now a stub importing `LvmWhirGroupEscape`) =====
section
-- Ported from leanVM `formal/lean_vm/LeanVM/Protocol/Whir/Sound/Queries.lean` (formal rev 40f877dc) as `LvmWhirQueries`
-- for lvm (WP-7). Changed: the positions are lvm's `samplePositions per depth` (`per` positions per challenge, leanVM
-- `192 / depth`); the hypotheses `1 ≤ depth ≤ 192` become `1 ≤ per`, `per · depth ≤ 192`.
/-
  LeanVM.Protocol.Whir.Sound.Queries

  The query positions of the deployed WHIR verifier are i.i.d. uniform: `sample_queries` cuts each
  uniform 192-bit sample into disjoint chunks of `depth` bits, so all `t` positions land in a set
  of `a` columns with probability at most `(a / 2^depth)^t`.
-/

/-!
# Uniformity of the query positions

lvm's positions (`LeanVM.Protocol.Verifier.samplePositions per depth t`, leanVM's
`sample_queries`, `crates/verifier/src/whir.rs:75-90` at `40f877dc`, with `per` in place of
`192/depth`; BLUEPRINT §2.2: 8 positions per answer) draw samples `c ∈ E` and read `int(c)`
(`eToNat`, the three limbs as one 192-bit integer); the chunks `(int(c) >> (k·depth)) mod 2^depth`,
`k < min(per, remaining)`, are the positions.

* `eNatEquiv`: `eToNat` is a bijection `E ≃ [0, 2^192)` (three independent 64-bit limbs).
* `card_chunks`: of the `2^192` samples, exactly `2^(192 − n·depth)·a^n` have their first `n`
  chunks in a set `S` with `a` elements in `[0, 2^depth)`, for `n·depth ≤ 192`.
* `retExp_samplePositions_le`: the probability that all `t` positions land in `S` is at most
  `(a / 2^depth)^t`, for `1 ≤ per` and `per · depth ≤ 192`.
-/

namespace LeanVM.Protocol.Whir.Sound

open LeanVM.Parameters LeanVM.Protocol.Compile LeanVM.Protocol.Verifier VerifierProgram Finset
  LeanVM.Protocol.Whir

section

/-! ## `int(e)` is uniform on `[0, 2^192)` -/

/-- The limbs of a word as `64`-bit digits. -/
def limbDigits (e : E) : Fin 3 → Fin (2 ^ 64) := fun i ↦ (e.limb i).toBitVec.toFin

theorem limbDigits_injective : Function.Injective limbDigits := by
  intro e e' h
  refine E.ext fun i ↦ ?_
  have := congrFun h i
  simp only [limbDigits] at this
  exact BF64.toBitVec_injective (BitVec.toFin_inj.mp this)

/-- `int(e)` as a digit expansion. -/
theorem eToNat_eq (e : E) : eToNat e = (finFunctionFinEquiv (limbDigits e) : ℕ) := by
  rw [finFunctionFinEquiv_apply, Fin.sum_univ_three]
  simp only [eToNat, kToNat, limbDigits, BitVec.val_toFin, Fin.val_zero, Fin.val_one, Fin.val_two]
  ring

/-- **`int` is a bijection `E ≃ [0, 2^192)`.** -/
noncomputable def eNatEquiv : E ≃ Fin ((2 ^ 64) ^ 3) :=
  Equiv.ofBijective (fun e ↦ finFunctionFinEquiv (limbDigits e))
    ((Fintype.bijective_iff_injective_and_card _).mpr
      ⟨finFunctionFinEquiv.injective.comp limbDigits_injective, by
        rw [card_E, Fintype.card_fin]; norm_num⟩)

theorem eNatEquiv_val (e : E) : (eNatEquiv e : ℕ) = eToNat e := by
  rw [eToNat_eq]; rfl

/-! ## Counting chunks -/

/-- Chunk `k` of `depth` bits of `x`. -/
def chunk (depth k x : ℕ) : ℕ := x / 2 ^ (k * depth) % 2 ^ depth

theorem chunk_eq_shiftRight (depth k x : ℕ) :
    (x >>> (k * depth)) % 2 ^ depth = chunk depth k x := by
  rw [Nat.shiftRight_eq_div_pow]; rfl

/-- The chunks of `x` below `n` digits are its base-`2^depth` digits. -/
theorem chunk_eq_digit (depth k x : ℕ) : chunk depth k x = x / (2 ^ depth) ^ k % 2 ^ depth := by
  rw [chunk, ← pow_mul, mul_comm]

/-- Adding a multiple of `(2^depth)^n` does not change the chunks below `n`. -/
theorem chunk_add_mul {depth n k : ℕ} (hk : k < n) (y u : ℕ) :
    chunk depth k (y + (2 ^ depth) ^ n * u) = chunk depth k y := by
  rw [chunk_eq_digit, chunk_eq_digit]
  obtain ⟨j, rfl⟩ := Nat.exists_eq_add_of_lt hk
  rw [show (2 ^ depth) ^ (k + j + 1) * u = (2 ^ depth) ^ k * ((2 ^ depth) ^ (j + 1) * u) by ring,
    Nat.add_mul_div_left _ _ (by positivity), pow_succ, show
      (2 ^ depth) ^ j * 2 ^ depth * u = 2 ^ depth * ((2 ^ depth) ^ j * u) by ring,
    Nat.add_mul_mod_self_left]

/-- **The chunk count**: exactly `2^(192 − n·depth)·a^n` samples have their first `n` chunks in
`S`, with `a` the number of elements of `S` below `2^depth`, for `n·depth ≤ 192`. -/
theorem card_chunks (depth n : ℕ) (hn : n * depth ≤ 192) (S : ℕ → Prop) [DecidablePred S] :
    (univ.filter fun e : E ↦ ∀ k < n, S (chunk depth k (eToNat e))).card =
      2 ^ (192 - n * depth) * (univ.filter fun j : Fin (2 ^ depth) ↦ S j).card ^ n := by
  set M := 2 ^ depth
  set U := 2 ^ (192 - n * depth)
  have hUL : (2 ^ 64) ^ 3 = U * M ^ n := by
    simp only [U, M, ← pow_mul, ← pow_add]
    rw [Nat.mul_comm depth n, Nat.sub_add_cancel hn]
  let P : ℕ → Prop := fun x ↦ ∀ k < n, S (chunk depth k x)
  -- Transport to `Fin (U * M^n)`.
  have h1 : (univ.filter fun e : E ↦ P (eToNat e)).card =
      (univ.filter fun x : Fin (U * M ^ n) ↦ P x).card := by
    let eqv : E ≃ Fin (U * M ^ n) := eNatEquiv.trans (finCongr hUL)
    have hv : ∀ e, (eqv e : ℕ) = eToNat e := fun e ↦ by
      rw [Equiv.trans_apply, finCongr_apply, Fin.val_cast, eNatEquiv_val]
    rw [← Finset.card_map eqv.toEmbedding]
    congr 1
    ext x
    simp only [Finset.mem_map_equiv, Finset.mem_filter, Finset.mem_univ, true_and]
    rw [← hv, Equiv.apply_symm_apply]
  -- Split into the high part and the `n` digits.
  have h2 : (univ.filter fun x : Fin (U * M ^ n) ↦ P x).card =
      U * (univ.filter fun y : Fin (M ^ n) ↦ P y).card := by
    have : (univ.filter fun x : Fin (U * M ^ n) ↦ P x) =
        (univ ×ˢ (univ.filter fun y : Fin (M ^ n) ↦ P y)).map finProdFinEquiv.toEmbedding := by
      ext x
      rw [Finset.mem_map_equiv, Finset.mem_product, Finset.mem_filter, Finset.mem_filter]
      simp only [Finset.mem_univ, true_and]
      conv_lhs => rw [← finProdFinEquiv.apply_symm_apply x, finProdFinEquiv_apply_val]
      exact forall₂_congr fun k hk ↦ by rw [chunk_add_mul hk]
    rw [this, Finset.card_map, Finset.card_product, Finset.card_univ, Fintype.card_fin]
  -- The digits are a function `Fin n → Fin M`.
  have h3 : (univ.filter fun y : Fin (M ^ n) ↦ P y).card =
      (univ.filter fun j : Fin M ↦ S j).card ^ n := by
    have : (univ.filter fun y : Fin (M ^ n) ↦ P y) =
        (univ.filter fun f : Fin n → Fin M ↦ ∀ k, f k ∈ univ.filter fun j : Fin M ↦ S j).map
          finFunctionFinEquiv.toEmbedding := by
      ext y
      rw [Finset.mem_map_equiv, Finset.mem_filter, Finset.mem_filter]
      simp only [Finset.mem_univ, true_and, Finset.mem_filter, finFunctionFinEquiv_symm_apply_val,
        P, chunk_eq_digit]
      exact ⟨fun h k ↦ h k k.isLt, fun h k hk ↦ h ⟨k, hk⟩⟩
    rw [this, Finset.card_map, card_forall_mem_fin]
  change (univ.filter fun e : E ↦ P (eToNat e)).card = _
  rw [h1, h2, h3]

/-! ## The positions -/

/-- The indicator that all positions land in `S`. -/
noncomputable def allIn (S : ℕ → Prop) [DecidablePred S] (qs : List ℕ) : ENNReal :=
  if ∀ q ∈ qs, S q then 1 else 0

theorem allIn_append (S : ℕ → Prop) [DecidablePred S] (a b : List ℕ) :
    allIn S (a ++ b) = allIn S a * allIn S b := by
  unfold allIn
  simp only [List.forall_mem_append]
  split_ifs <;> simp_all

/-- One sample: the probability that its `n` chunks land in `S`. -/
theorem avg_chunks (depth n : ℕ) (hn : n * depth ≤ 192) (S : ℕ → Prop) [DecidablePred S] :
    (Fintype.card E : ENNReal)⁻¹ * ∑ c : E,
        allIn S ((List.range n).map fun k ↦ (eToNat c >>> (k * depth)) % 2 ^ depth) =
      ((univ.filter fun j : Fin (2 ^ depth) ↦ S j).card / 2 ^ depth : ENNReal) ^ n := by
  have hall : ∀ c : E, allIn S ((List.range n).map fun k ↦ (eToNat c >>> (k * depth)) % 2 ^ depth)
      = if ∀ k < n, S (chunk depth k (eToNat c)) then 1 else 0 := by
    intro c
    simp only [allIn, List.mem_map, List.mem_range, forall_exists_index, and_imp,
      forall_apply_eq_imp_iff₂, chunk_eq_shiftRight]
  simp only [hall]
  rw [Finset.sum_boole, card_chunks depth n hn, card_E]
  set a := (univ.filter fun j : Fin (2 ^ depth) ↦ S j).card
  simp only [Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat]
  have h192 : (2 : ENNReal) ^ 192 = 2 ^ (192 - n * depth) * (2 ^ depth) ^ n := by
    rw [← pow_mul, ← pow_add, Nat.mul_comm depth n, Nat.sub_add_cancel hn]
  rw [h192, ENNReal.mul_inv (by simp) (by simp), ENNReal.div_eq_inv_mul, mul_pow]
  have hx : ((2 : ENNReal) ^ (192 - n * depth))⁻¹ * 2 ^ (192 - n * depth) = 1 :=
    ENNReal.inv_mul_cancel (by simp) (by simp)
  calc _ = (((2 : ENNReal) ^ (192 - n * depth))⁻¹ * 2 ^ (192 - n * depth)) *
        (((2 ^ depth) ^ n)⁻¹ * (a : ENNReal) ^ n) := by ring
    _ = _ := by rw [hx, one_mul, ENNReal.inv_pow]

/-- **The query positions are i.i.d. uniform.** With `1 ≤ per`, `per · depth ≤ 192` and
`rem ≤ fuel`, the probability that all positions of `samplePositionsAux per depth fuel rem` land
in `S` is at most `(a / 2^depth)^rem`. -/
theorem retExp_samplePositionsAux_le (per depth : ℕ) (hper : 1 ≤ per) (hpd : per * depth ≤ 192)
    (S : ℕ → Prop) [DecidablePred S] :
    ∀ (fuel rem : ℕ), rem ≤ fuel → ∀ h₀ l,
      retExp (fun qs _ ↦ allIn S qs) h₀ l (samplePositionsAux per depth fuel rem) ≤
        ((univ.filter fun j : Fin (2 ^ depth) ↦ S j).card / 2 ^ depth : ENNReal) ^ rem
  | 0, rem, hrem, h₀, l => by
    obtain rfl : rem = 0 := by (clear * - hrem; omega)
    simp [samplePositionsAux, retExp, allIn]
  | fuel + 1, rem, hrem, h₀, l => by
    set ρ := ((univ.filter fun j : Fin (2 ^ depth) ↦ S j).card / 2 ^ depth : ENNReal)
    by_cases h0 : rem = 0
    · subst h0
      simp [samplePositionsAux, retExp, allIn]
    set n := min per rem with hn
    have hn1 : 1 ≤ n := le_min hper (by (clear * - hper h0; omega))
    have hnd : n * depth ≤ 192 := (Nat.mul_le_mul_right _ (min_le_left _ _)).trans hpd
    have hnr : n ≤ rem := min_le_right _ _
    simp only [samplePositionsAux, h0, ite_false, bind_eq, pure_eq]
    rw [show sampleChallenge = (sample ret : VerifierProgram E) from rfl, VerifierProgram.bind]
    simp only [retExp, ret_bind]
    have hin : ∀ c : E,
        retExp (fun qs _ ↦ allIn S qs) h₀ (l ++ [Ev.sample c])
          ((samplePositionsAux per depth fuel (rem - n)).bind fun rest ↦
            ret ((List.range n).map (fun k ↦ (eToNat c >>> (k * depth)) % 2 ^ depth) ++ rest)) ≤
        allIn S ((List.range n).map fun k ↦ (eToNat c >>> (k * depth)) % 2 ^ depth) *
          ρ ^ (rem - n) := by
      intro c
      rw [retExp_bind]
      have : (fun a (h : List Ev) ↦ retExp (fun qs _ ↦ allIn S qs) h []
          (ret ((List.range n).map (fun k ↦ (eToNat c >>> (k * depth)) % 2 ^ depth) ++ a))) =
          fun a _ ↦ allIn S ((List.range n).map fun k ↦ (eToNat c >>> (k * depth)) % 2 ^ depth) *
            allIn S a := by
        funext a h; simp [retExp, allIn_append]
      rw [this, retExp_const_mul]
      gcongr
      exact retExp_samplePositionsAux_le per depth hper hpd S fuel (rem - n) (by (clear * - hrem hn1 hnr; omega)) _ _
    calc (Fintype.card E : ENNReal)⁻¹ * ∑ c : E, _
        ≤ (Fintype.card E : ENNReal)⁻¹ * ∑ c : E,
          allIn S ((List.range n).map fun k ↦ (eToNat c >>> (k * depth)) % 2 ^ depth) *
            ρ ^ (rem - n) := by gcongr with c; exact hin c
      _ = ρ ^ n * ρ ^ (rem - n) := by
        rw [← Finset.sum_mul, ← mul_assoc, avg_chunks depth n hnd S]
      _ = ρ ^ rem := by rw [← pow_add]; congr 1; (clear * - hnr; omega)

/-- **The positions are i.i.d. uniform**: all `t` positions land in `S` with probability at most
`(a / 2^depth)^t`. -/
theorem retExp_samplePositions_le (per depth t : ℕ) (hper : 1 ≤ per) (hpd : per * depth ≤ 192)
    (S : ℕ → Prop) [DecidablePred S] (h₀ l : List Ev) :
    retExp (fun qs _ ↦ allIn S qs) h₀ l (samplePositions per depth t) ≤
      ((univ.filter fun j : Fin (2 ^ depth) ↦ S j).card / 2 ^ depth : ENNReal) ^ t :=
  retExp_samplePositionsAux_le per depth hper hpd S t t le_rfl h₀ l

end
end LeanVM.Protocol.Whir.Sound
end
-- ===== end of `LvmWhirQueries` =====

-- ===== merged from `LvmWhirGroup` (GOLF module merge: `LvmWhirGroup.lean` is now a stub importing `LvmWhirGroupEscape`) =====
section
-- Ported from leanVM `formal/lean_vm/LeanVM/Protocol/Whir/Sound/Group.lean` (formal rev 40f877dc) as `LvmWhirGroup` for
-- lvm (WP-7). Changed: the query group draws lvm's `samplePositions per depth` (hypotheses `1 ≤ per`,
-- `per · depth ≤ 192` for leanVM's `1 ≤ depth ≤ 192`); its opening is of a commitment index `c` (the level's
-- `cidx`); the out-of-domain group is gone with the step.
/-
  LeanVM.Protocol.Whir.Sound.Group

  The move-free fragments of a WHIR level as joint groups of challenges: the query group (positions, `λ`, openings), with their escape expectations.
-/

/-!
# Groups of challenges

The calculus bounds a move-free fragment jointly (`Spec.ofNoMove`). This module provides:

* `NoMoves`: a program whose every node is a sample, an opening, a return or a rejection, closed
  under `bind`; `NoMoves.not_isMove` discharges the hypothesis of `Spec.ofNoMove`.
* `retExp_samplePositionsAux_restrict_len`: the positions `samplePositions` returns are below
  `2^depth` (chunks are reduced modulo `2^depth`), so an expectation over them only sees such
  position lists.
* `queryFrag per depth t i`: the query group `samplePositions`, `λ`, opening of commitment `i`, as
  one fragment returning `(positions, λ, rows)`; `retExp_queryFrag_le`: if, for every in-range
  position list, the average over `λ` of a function of the opened rows is at most
  `allIn S qs + ε`, the expectation over the group is at most `(|S| / 2^depth)^t + ε`.
-/

namespace LeanVM.Protocol.Whir.Sound

open LeanVM.Parameters LeanVM.Protocol.Compile LeanVM.Protocol.Verifier VerifierProgram Finset

section

variable {α β : Type}

/-! ## Move-free programs -/

/-- Every node of the program is a sample, an opening, a return or a rejection. -/
inductive NoMoves : VerifierProgram α → Prop where
  | ret (a : α) : NoMoves (VerifierProgram.ret a)
  | fail : NoMoves VerifierProgram.fail
  | sample {k : E → VerifierProgram α} : (∀ c, NoMoves (k c)) → NoMoves (VerifierProgram.sample k)
  | query {i : ℕ} {ps : List ℕ} {k : List (List K) → VerifierProgram α} :
      (∀ rows, NoMoves (k rows)) → NoMoves (VerifierProgram.query i ps k)

theorem NoMoves.after {p q : VerifierProgram α} (hp : NoMoves p) :
    ∀ {l : List Ev}, p.after l = some q → NoMoves q := by
  intro l
  induction l generalizing p with
  | nil => intro h; simp [VerifierProgram.after] at h; exact h ▸ hp
  | cons e l ih =>
    intro h
    cases hp with
    | ret a => cases e <;> simp [VerifierProgram.after] at h
    | fail => cases e <;> simp [VerifierProgram.after] at h
    | sample hk =>
      cases e <;> simp [VerifierProgram.after] at h
      exact ih (hk _) h
    | query hk =>
      cases e <;> simp [VerifierProgram.after] at h
      exact ih (hk _) h

theorem NoMoves.not_isMove {q : VerifierProgram α} (hq : NoMoves q) : ¬ q.IsMove := by
  cases hq <;> simp [VerifierProgram.IsMove]

/-- The hypothesis of `Spec.ofNoMove`. -/
theorem NoMoves.noMove {p : VerifierProgram α} (hp : NoMoves p) :
    ∀ {h₀ l : List Ev} {q : VerifierProgram α}, p.Reach h₀ l → p.after l = some q → ¬ q.IsMove :=
  fun _ ha ↦ (hp.after ha).not_isMove

theorem NoMoves.bind {p : VerifierProgram α} {f : α → VerifierProgram β} (hp : NoMoves p) (hf : ∀ a,
    NoMoves (f a)) :
    NoMoves (p.bind f) := by
  induction hp with
  | ret a => exact hf a
  | fail => exact NoMoves.fail
  | sample _ ih => exact NoMoves.sample ih
  | query _ ih => exact NoMoves.query ih

theorem noMoves_sampleE : NoMoves sampleChallenge := NoMoves.sample fun c ↦ NoMoves.ret c

theorem noMoves_queryP (i : ℕ) (ps : List ℕ) : NoMoves (queryOpenings i ps) :=
  NoMoves.query fun rows ↦ NoMoves.ret rows

theorem noMoves_sampleN : ∀ n, NoMoves (sampleChallenges n)
  | 0 => NoMoves.ret []
  | n + 1 => noMoves_sampleE.bind fun _ ↦ (noMoves_sampleN n).bind fun _ ↦ NoMoves.ret _

theorem noMoves_samplePositionsAux (per depth : ℕ) :
    ∀ fuel rem, NoMoves (samplePositionsAux per depth fuel rem)
  | 0, rem => NoMoves.ret []
  | fuel + 1, rem => by
    unfold samplePositionsAux
    split
    · exact NoMoves.ret []
    · exact noMoves_sampleE.bind fun _ ↦
        (noMoves_samplePositionsAux per depth fuel _).bind fun _ ↦ NoMoves.ret _

/-! ## The positions are in range -/

/-- An expectation over `samplePositions` only sees position lists of the requested length below
`2^depth`. -/
theorem retExp_samplePositionsAux_restrict_len (per depth : ℕ) (hper : 1 ≤ per)
    (g : List ℕ → List Ev → ENNReal) :
    ∀ fuel rem, rem ≤ fuel → ∀ h₀ l, retExp g h₀ l (samplePositionsAux per depth fuel rem) =
      retExp (fun qs h ↦ if (∀ q ∈ qs, q < 2 ^ depth) ∧ qs.length = rem then g qs h else 0) h₀ l
        (samplePositionsAux per depth fuel rem)
  | 0, rem, hrem, h₀, l => by
    obtain rfl : rem = 0 := by (clear * - hrem; omega)
    simp [samplePositionsAux, retExp]
  | fuel + 1, rem, hrem, h₀, l => by
    unfold samplePositionsAux
    split
    · rename_i h0
      subst h0
      simp [retExp]
    · rename_i h0
      have hn1 : 1 ≤ min per rem := le_min hper (by (clear * - h0; omega))
      have hnr : min per rem ≤ rem := min_le_right _ _
      simp only [bind_eq, pure_eq]
      rw [show sampleChallenge = (sample ret : VerifierProgram E) from rfl, VerifierProgram.bind]
      simp only [retExp, ret_bind]
      congr 1
      refine Finset.sum_congr rfl fun c _ ↦ ?_
      rw [retExp_bind, retExp_bind]
      rw [retExp_samplePositionsAux_restrict_len per depth hper _ fuel _ (by (clear * - hrem hn1 hnr; omega)) h₀ _]
      conv_rhs => rw [retExp_samplePositionsAux_restrict_len per depth hper _ fuel _ (by (clear * - hrem hn1 hnr; omega)) h₀ _]
      congr 1
      funext rest h
      simp only [retExp]
      by_cases hr : (∀ q ∈ rest, q < 2 ^ depth) ∧ rest.length = rem - min per rem
      · have hall : (∀ q ∈ (List.range (min per rem)).map
            (fun k ↦ (eToNat c >>> (k * depth)) % 2 ^ depth) ++ rest, q < 2 ^ depth) ∧
            ((List.range (min per rem)).map
            (fun k ↦ (eToNat c >>> (k * depth)) % 2 ^ depth) ++ rest).length = rem := by
          refine ⟨fun q hq ↦ ?_, by
            simp only [List.length_append, List.length_map, List.length_range, hr.2]; (clear * - hnr; omega)⟩
          rcases List.mem_append.mp hq with hq | hq
          · obtain ⟨a, -, rfl⟩ := List.mem_map.mp hq
            exact Nat.mod_lt _ (Nat.two_pow_pos _)
          · exact hr.1 q hq
        split_ifs
        simp_all
      · simp [hr]

/-! ## The query group -/

/-- The query group: positions, `λ`, the opening of commitment `i`. -/
def queryFrag (per depth t i : ℕ) : VerifierProgram (List ℕ × E × List (List K)) :=
  samplePositions per depth t >>= fun qs ↦ sampleChallenge >>= fun lam ↦ queryOpenings i qs >>= fun words ↦
    VerifierProgram.ret (qs, lam, words)

theorem noMoves_queryFrag (per depth t i : ℕ) : NoMoves (queryFrag per depth t i) :=
  (noMoves_samplePositionsAux per depth t t).bind fun _ ↦ noMoves_sampleE.bind fun _ ↦
    (noMoves_queryP i _).bind fun _ ↦ NoMoves.ret _

/-- **The query group's expectation.** For a function `F` of the group's values, if every
in-range position list has `avg_λ F(qs, λ, W(qs)) ≤ allIn S qs + ε` (the rows read from the
word `W` of commitment `i`), the expectation over the group is at most
`(|S ∩ [0, 2^depth)| / 2^depth)^t + ε`. -/
theorem retExp_queryFrag_le (per depth t i : ℕ) (hper : 1 ≤ per) (hpd : per * depth ≤ 192)
    (h₀ : List Ev) {wd : ℕ} {W : Word} (hc : (commits h₀)[i]? = some (depth, wd, W))
    (F : List ℕ × E × List (List K) → ENNReal) (S : ℕ → Prop) [DecidablePred S] (ε : ENNReal)
    (hF : ∀ qs : List ℕ, (∀ q ∈ qs, q < 2 ^ depth) → qs.length = t →
      (Fintype.card E : ENNReal)⁻¹ * ∑ lam : E, F (qs, lam, qs.map W) ≤ allIn S qs + ε) :
    retExp (fun a _ ↦ F a) h₀ [] (queryFrag per depth t i) ≤
      ((univ.filter fun j : Fin (2 ^ depth) ↦ S j).card / 2 ^ depth : ENNReal) ^ t + ε := by
  unfold queryFrag
  simp only [bind_eq]
  rw [retExp_bind]
  -- The inner expectation depends on the history only through its commitments.
  have hin : ∀ qs h, retExp (fun a _ ↦ F a) h []
      ((sampleChallenge.bind fun lam ↦ (queryOpenings i qs).bind fun words ↦ VerifierProgram.ret (qs, lam, words))) =
      (Fintype.card E : ENNReal)⁻¹ * ∑ lam : E,
        (match answer h i qs with
          | some rows => F (qs, lam, rows)
          | none => 0) := by
    intro qs h
    rw [retExp_bind, retExp_sampleE]
    congr 1
    refine Finset.sum_congr rfl fun lam _ ↦ ?_
    rw [retExp_bind, retExp_queryP, List.append_nil, List.append_nil, answer_append_sample]
    cases answer h i qs <;> simp [retExp]
  simp only [hin]
  -- Its value along the run is that at `h₀`.
  have hcom := retExp_commits (fun qs cs ↦ (Fintype.card E : ENNReal)⁻¹ * ∑ lam : E,
      (match (cs[i]?.map fun c ↦ qs.map fun p ↦ c.2.2 (p % 2 ^ c.1)) with
        | some rows => F (qs, lam, rows)
        | none => 0)) (samplePositions per depth t) h₀ []
  simp only [answer] at hcom ⊢
  rw [hcom, List.append_nil, samplePositions,
    retExp_samplePositionsAux_restrict_len per depth hper _ t t le_rfl]
  calc _ ≤ retExp (fun qs _ ↦ allIn S qs + ε) h₀ [] (samplePositionsAux per depth t t) := by
        refine retExp_mono (fun qs _ ↦ ?_) _ _ _
        split_ifs with hr
        · simp only [hc, Option.map_some]
          have hmap : (qs.map fun p ↦ W (p % 2 ^ depth)) = qs.map W :=
            List.map_congr_left fun q hq ↦ by rw [Nat.mod_eq_of_lt (hr.1 q hq)]
          rw [hmap]
          exact hF qs hr.1 hr.2
        · exact zero_le
    _ ≤ retExp (fun qs _ ↦ allIn S qs) h₀ [] (samplePositionsAux per depth t t) + ε :=
        retExp_le_add (fun _ _ ↦ le_rfl) _ _ _
    _ ≤ _ := by
        gcongr
        exact retExp_samplePositions_le per depth t hper hpd S h₀ []

end
end LeanVM.Protocol.Whir.Sound
end
-- ===== end of `LvmWhirGroup` =====

-- ===== merged from `LvmWhirInterface` (GOLF module merge: `LvmWhirInterface.lean` is now a stub importing `LvmWhirGroupEscape`) =====
section
-- Ported from leanVM `formal/lean_vm/LeanVM/Protocol/Whir/Sound/Interface.lean` (formal rev 40f877dc) as
-- `LvmWhirInterface` for lvm (WP-7). Changed for the unique-decoding regime: a level with a next commitment glues
-- one claim (no out-of-domain claim), so `claimSum_glue2`/`card_lambda_bad_le` become `claimSum_glue1`/
-- `card_lambda_bad_le_ud` (degree `t`, `t·L'` values). The final level's step is leanVM's.
/-
  LeanVM.Protocol.Whir.Sound.Interface

  The batching challenge `λ` of a WHIR level against the program's glued claim: after positions
  that catch every member of the next list, at most `t·L'` values of `λ` let a member satisfy the
  claim the verifier glues (`t` values on the final level, for the residual).
-/

/-!
# The glued claim of a level

The verifier glues a level's claims into the running sumcheck (`glueT`, lvm `whirLevelsUd`;
leanVM `crates/verifier/src/whir.rs:213-232` at `40f877dc` without the out-of-domain claim): the
running claim keeps `λ⁰` and the batch of consistency claims
`(induced_weight(κ, qs, powers(λ, t), ·), enforcedSum)` gets `λ`, on every level. With the inner
products of `LeanVM.Protocol.Whir.Sound.Weights` (`sum_inducedWeight_mul`: the batch weight pairs
with a message to `Σ_q λ^q Enc(G)[x_q]`) the glued claim of a member is a polynomial in `λ` of
degree `t` whose coefficients are the discrepancies of the separate claims.

* `card_lambda_bad_le_ud`: under `QueryGoodUd`, at most `t·listMax'` values of `λ` break `Viol`
  for the glued claim.
* `card_lambda_bad_le_final`: under `QueryGoodFinal`, at most `t` values of `λ` let the residual
  satisfy the glued claim.
-/

namespace LeanVM.Protocol.Whir.Sound

open LeanVM.Parameters LeanVM.Protocol.Compile LeanVM.Protocol.Verifier
  LeanVM.Protocol.Whir Finset

section

/-! ## Linearity and bookkeeping -/

theorem claimSum_glue1 {m κ : ℕ} (Φ Ψ : List E → E) (a : E)
    (g : (Fin m → Bool) → (Fin κ → Bool) → E) :
    claimSum (fun r ↦ Φ r + a * Ψ r) g = claimSum Φ g + a * claimSum Ψ g := by
  simp only [claimSum, Finset.mul_sum, ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun u _ ↦ Finset.sum_congr rfl fun x _ ↦ by ring

/-- The program's rows of an opening are the lanes of its leaves. -/
theorem rows_eq (i : ℕ) (words : List (List K)) :
    (if i = 0 then words.map (fun row ↦ row.reverse.map ofK) else words.map extRow) =
      words.map (lanesOf i) := by
  by_cases h : i = 0 <;> simp [lanesOf, h]

theorem wordOf_append (cs : List (ℕ × ℕ × Word)) (x : ℕ × ℕ × Word) {i : ℕ}
    (h : i < cs.length) : wordOf (cs ++ [x]) i = wordOf cs i := by
  simp [wordOf, List.getElem?_append_left h]

theorem laneO_append (cs : List (ℕ × ℕ × Word)) (x : ℕ × ℕ × Word) {i : ℕ} (h : i < cs.length)
    (n : ℕ) : laneO i (cs ++ [x]) n = laneO i cs n := by
  funext j v
  simp [laneO, wordOf_append cs x h]

theorem rowsOf_zero {ι : Type*} (O : ℕ → ι → E) : rowsOf 0 O = fun _ ↦ O 0 := by
  funext u
  simp [rowsOf, bitsToNat]

/-! ## The batching challenge -/

/-- The inner product of the batch weight with a member's message: `Σ_k λ^k Enc(G)[x_k]`. -/
theorem claimSum_inducedWeight (P : LevelCode) {ℓ' κ' : ℕ} (hκ : P.κ = ℓ' + κ')
    (qs : List ℕ) (hqs : ∀ q ∈ qs, q < P.n) (lam : E)
    (g : (Fin ℓ' → Bool) → (Fin κ' → Bool) → E) :
    claimSum (fun r ↦ Verifier.inducedWeight P.κ qs (powers lam qs.length) r) g =
      ∑ k : Fin qs.length, lam ^ (k : ℕ) * encAt P.κ P.R (joinMsg hκ g) qs[k] := by
  rw [← sum_joinMsg hκ, sum_inducedWeight_mul P.R (by have := P.h64; (clear * - P ℓ' κ' hκ this; omega)) qs _
    (length_powers lam qs.length) hqs, sum_zip_powers]

open Classical in
/-- **The batching step of a level with a next commitment** (unique decoding: one glued claim). -/
theorem card_lambda_bad_le_ud (P P' : LevelCode) {ℓ' : ℕ} (hκ : P.κ = ℓ' + P'.κ)
    (Q' : (Fin ℓ' → Bool) → Fin P'.n → E) (C : Fin P.n → E) (Φ : List E → E) (σ : E)
    (qs : List ℕ) (hqs : ∀ q ∈ qs, q < P.n)
    (hgood : QueryGoodUd P P' hκ Q' C Φ σ qs) :
    (univ.filter fun lam : E ↦ ¬ Viol P' Q'
        (fun r ↦ Φ r + 1 * lam * Verifier.inducedWeight P.κ qs (powers lam qs.length) r)
        (σ + 1 * lam * ∑ k : Fin qs.length, lam ^ (k : ℕ) * wordAt C qs[k])).card ≤
      qs.length * P'.listMax := by
  set L := iList P'.code P'.thr Q'
  refine (Finset.card_le_card fun lam hlam ↦ ?_).trans
    ((card_filter_exists_le L (fun V lam ↦
        claimSum Φ (decode P' V) + lam *
          ∑ k : Fin qs.length, lam ^ (k : ℕ) * encAt P.κ P.R (joinMsg hκ (decode P' V)) qs[k] =
        σ + lam * ∑ k : Fin qs.length, lam ^ (k : ℕ) * wordAt C qs[k])
      (N := qs.length) fun V hV ↦ ?_).trans ?_)
  · simp only [Finset.mem_filter, Finset.mem_univ, true_and, Viol, not_forall, not_not,
      exists_prop] at hlam ⊢
    obtain ⟨V, hV, heq⟩ := hlam
    refine ⟨V, hV, ?_⟩
    rw [claimSum_glue1, claimSum_inducedWeight P hκ qs hqs lam] at heq
    simpa only [one_mul] using heq
  · refine card_glue_bad_le_final _ σ _ _ ?_
    rcases hgood V hV with h | ⟨q, hq, hne⟩
    · exact Or.inl h
    · obtain ⟨k, hk, rfl⟩ := List.getElem_of_mem hq
      exact Or.inr ⟨⟨k, hk⟩, hne⟩
  · rw [mul_comm]
    exact Nat.mul_le_mul_left _ (P'.card_iList_le Q')

/-- The residual of the final level as a message (entry `⟨x⟩` of the table). -/
def resMsg {κ : ℕ} (res : List E) : (Fin κ → Bool) → E := fun x ↦ res.getD (bitsToNat x) 0

open Classical in
/-- **The batching step of the final level**: the residual alone, at most `t` values. -/
theorem card_lambda_bad_le_final (P : LevelCode) (C : Fin P.n → E) (Φ : List E → E) (σ : E)
    (G : (Fin P.κ → Bool) → E) (qs : List ℕ) (hqs : ∀ q ∈ qs, q < P.n)
    (hgood : QueryGoodFinal P C Φ σ G qs) :
    (univ.filter fun lam : E ↦
        ∑ x, (Φ (bitsL x) + 1 * lam * Verifier.inducedWeight P.κ qs (powers lam qs.length)
          (bitsL x)) * G x =
          σ + 1 * lam * ∑ k : Fin qs.length, lam ^ (k : ℕ) * wordAt C qs[k]).card ≤
      qs.length := by
  have hsum : ∀ lam, ∑ x, (Φ (bitsL x) + 1 * lam *
      Verifier.inducedWeight P.κ qs (powers lam qs.length)
      (bitsL x)) * G x = ∑ x, Φ (bitsL x) * G x +
        lam * ∑ k : Fin qs.length, lam ^ (k : ℕ) * encAt P.κ P.R G qs[k] := by
    intro lam
    rw [← sum_zip_powers, ← sum_inducedWeight_mul P.R (by have := P.h64; (clear * - P this; omega)) qs _
      (length_powers lam qs.length) hqs G, Finset.mul_sum, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun x _ ↦ by ring
  simp only [hsum]
  simp only [one_mul]
  refine card_glue_bad_le_final _ σ _ _ ?_
  rcases hgood with h | ⟨q, hq, hne⟩
  · exact Or.inl h
  · obtain ⟨k, hk, rfl⟩ := List.getElem_of_mem hq
    exact Or.inr ⟨⟨k, hk⟩, hne⟩

end
end LeanVM.Protocol.Whir.Sound
end
-- ===== end of `LvmWhirInterface` =====

-- ===== merged from `LvmWhirDefs` (GOLF module merge: `LvmWhirDefs.lean` is now a stub importing `LvmWhirGroupEscape`) =====
section
-- Ported from leanVM `formal/lean_vm/LeanVM/Protocol/Whir/Sound/Defs.lean` (formal rev 40f877dc) as `LvmWhirDefs` for
-- lvm (WP-7). Changed for the unique-decoding regime: `eOod` is cut and `eQuery` becomes `eQueryUd`
-- (`((A − 1)/n)^t + t·L'/|E|`: no out-of-domain claim in the glue); no proof-of-work discount.
/-
  LeanVM.Protocol.Whir.Sound.Defs

  The shapes of the WHIR commitments, the doom at the start of a level, and the escape bounds of
  each group of challenges of a level.
-/

/-!
# Level doom and escape bounds

A level `i` of the opening (`LeanVM.Protocol.Verifier.whirLevelsUd`) opens the `i`-th commitment
of the opening's view (`viewC`), a matrix of `2^(κ_i + R_i)` rows of `wdOf i ℓ_i` words: `2^ℓ₀`
`K`-words at level `0` (the stack's lanes), `3·2^ℓ_i` words (the lanes in `E`) deeper. `ShapeOK`
records that the view has exactly the commitments `0..i` and that the `i`-th has this shape;
`LevelPre` is the doom at the start of a level: `A(i, 0)` and `ShapeOK`.

The escape bounds of a level's groups, each a probability over the group's challenges:

* `eFold P ℓ` (`LeanVM.Protocol.Whir.Sound.Folds`): `(2·L + 2^(ℓ−1)·E_mca) / |E|` per fold;
* `eQueryUd P P' t`: `((A − 1)/n)^t + t·L' / |E|` for the query positions and `λ`, `A` the
  threshold `thr` and `n` the block length of the current level;
* `eQueryFinal P t`: `((A − 1)/n)^t + t / |E|` on the final level;
* `eTail`: `2 / |E|` per tail round.
-/

namespace LeanVM.Protocol.Whir.Sound

open LeanVM.Parameters LeanVM.Protocol.Compile LeanVM.Protocol.Verifier
  LeanVM.Protocol.Whir Finset

section

/-- The width of commitment `i`: `2^ℓ` words at level `0`, `3·2^ℓ` deeper. -/
def wdOf (i ℓ : ℕ) : ℕ := if i = 0 then 2 ^ ℓ else 3 * 2 ^ ℓ

/-- The history has the commitments `0..i`, the `i`-th of `2^(κ+R)` rows of `wdOf i ℓ` words. -/
def ShapeOK (i : ℕ) (P : LevelCode) (ℓ : ℕ) (cs : List (ℕ × ℕ × Word)) : Prop :=
  cs.length = i + 1 ∧ ∃ W, cs[i]? = some (P.κ + P.R, wdOf i ℓ, W) ∧ WellShaped (wdOf i ℓ) W

/-- **The doom at the start of level `i`**: `A(i, 0)` and the commitments' shape. -/
def LevelPre (μ ℓ₀ : ℕ) (w : List E → E) (i : ℕ) (P : LevelCode) (ℓ pre : ℕ) (s : WhirStateT)
    (cs : List (ℕ × ℕ × Word)) : Prop :=
  FoldInv μ ℓ₀ w i P ℓ pre s [] cs ∧ ShapeOK i P ℓ cs

/-- The query group's escape (unique decoding): `((A − 1)/n)^t + t·L' / |E|`. -/
noncomputable def eQueryUd (P P' : LevelCode) (t : ℕ) : ENNReal :=
  (((P.thr - 1 : ℕ) : ENNReal) / P.n) ^ t + ((t * P'.listMax : ℕ) : ENNReal) / Fintype.card E

/-- The final query group's escape: `((A − 1)/n)^t + t / |E|`. -/
noncomputable def eQueryFinal (P : LevelCode) (t : ℕ) : ENNReal :=
  (((P.thr - 1 : ℕ) : ENNReal) / P.n) ^ t + (t : ENNReal) / Fintype.card E

/-- A tail round's escape: `2 / |E|`. -/
noncomputable def eTail : ENNReal := (2 : ENNReal) / Fintype.card E

/-! ## Shape lemmas -/

theorem shapeOK_word {i : ℕ} {P : LevelCode} {ℓ : ℕ} {cs : List (ℕ × ℕ × Word)}
    (h : ShapeOK i P ℓ cs) : cs[i]? = some (P.κ + P.R, wdOf i ℓ, wordOf cs i) ∧
      WellShaped (wdOf i ℓ) (wordOf cs i) := by
  obtain ⟨-, W, hW, hws⟩ := h
  rw [wordOf_eq hW]
  exact ⟨hW, hws⟩

theorem shapeOK_append {i : ℕ} {P : LevelCode} {ℓ : ℕ} {cs : List (ℕ × ℕ × Word)}
    (h : ShapeOK i P ℓ cs) (x : ℕ × ℕ × Word) :
    (cs ++ [x])[i]? = some (P.κ + P.R, wdOf i ℓ, wordOf cs i) := by
  rw [List.getElem?_append_left (by rw [h.1]; (clear * - i; omega))]
  exact (shapeOK_word h).1

/-- The rows of a well-shaped leaf of commitment `i` give `2^ℓ` lanes. -/
theorem length_wordOf {i : ℕ} {P : LevelCode} {ℓ : ℕ} {cs : List (ℕ × ℕ × Word)}
    (h : ShapeOK i P ℓ cs) (q : ℕ) :
    (wordOf cs i q).length = if i = 0 then 2 ^ ℓ else 3 * 2 ^ ℓ :=
  (shapeOK_word h).2 q

end
end LeanVM.Protocol.Whir.Sound
end
-- ===== end of `LvmWhirDefs` =====

/-!
# Escapes of the query group

* `escRet_queryFrag_le_ud`: the query group escapes the glued claim's doom with probability at most
  `eQueryUd P P' t = ((A − 1)/n)^t + t·L'/|E|`: the positions avoid the agreement set of the one
  candidate except with probability `((A − 1)/n)^t` (`exists_agreeSet_ud`,
  `retExp_queryFrag_le`), and then `λ` escapes at at most `t·L'` values (`card_lambda_bad_le_ud`).
* `escRet_queryFrag_le_finViol`: the final level's `((A − 1)/n)^t + t/|E|`, from the residual's
  doom (`exists_agreeSet_finViol`).

The groups' posts are functions of the values and of the commitments, which a group does not
change (`retExp_commits`).
-/

namespace LeanVM.Protocol.Whir.Sound

open LeanVM.Parameters LeanVM.Protocol.Compile LeanVM.Protocol.Verifier
  LeanVM.Protocol.Whir VerifierProgram Finset

section

/-- The average of an indicator is the fraction of its support. -/
theorem avg_ite_le (p : E → Prop) [DecidablePred p] :
    (Fintype.card E : ENNReal)⁻¹ * ∑ c : E, (if p c then 0 else 1 : ENNReal) =
      (Fintype.card E : ENNReal)⁻¹ * ((univ.filter fun c ↦ ¬ p c).card : ENNReal) := by
  congr 1
  rw [Finset.card_filter, Nat.cast_sum]
  refine Finset.sum_congr rfl fun c _ ↦ ?_
  by_cases h : p c <;> simp [h]

/-- The count of the positions in the agreement set. -/
theorem card_filter_mem {n : ℕ} (A : Finset (Fin n)) :
    (univ.filter fun j : Fin n ↦ ∀ h : (j : ℕ) < n, (⟨j, h⟩ : Fin n) ∈ A).card = A.card := by
  congr 1
  ext j
  simp

/-- `((|A|)/n)^t ≤ ((thr − 1)/n)^t` for `|A| + 1 ≤ thr`. -/
theorem pow_frac_le (P : LevelCode) (A : Finset (Fin P.n)) (hA : A.card + 1 ≤ P.thr) (t : ℕ) :
    ((A.card : ENNReal) / 2 ^ (P.κ + P.R)) ^ t ≤ (((P.thr - 1 : ℕ) : ENNReal) / P.n) ^ t := by
  have hn : ((P.n : ℕ) : ENNReal) = 2 ^ (P.κ + P.R) := by simp [LevelCode.n]
  rw [hn]
  gcongr
  exact_mod_cast (show A.card ≤ P.thr - 1 by (clear * - P A hA; omega))

open Classical in
/-- **The query group of a level with a next commitment** (unique decoding). -/
theorem escRet_queryFrag_le_ud (P P' : LevelCode) {ℓ' : ℕ} (hκ : P.κ = ℓ' + P'.κ) (per t c : ℕ)
    (hper : 1 ≤ per) (hpd : per * (P.κ + P.R) ≤ 192)
    (h₀ : List Ev) {wd : ℕ} {W : Word} (hW : (commits h₀)[c]? = some (P.κ + P.R, wd, W))
    (Q' : (Fin ℓ' → Bool) → Fin P'.n → E) (C : Fin P.n → E) (Φ : List E → E) (σ : E)
    (hviol : Viol P (fun _ : Fin 0 → Bool ↦ C) Φ σ)
    (hone : (iList P'.code P'.thr Q').card ≤ 1)
    (J : List ℕ × E × List (List K) → List (ℕ × ℕ × Word) → Prop)
    (hJ : ∀ (qs : List ℕ) (lam : E), (∀ q ∈ qs, q < P.n) → qs.length = t →
      Viol P' Q' (fun r ↦ Φ r + 1 * lam * Verifier.inducedWeight P.κ qs (powers lam qs.length) r)
        (σ + 1 * lam * ∑ k : Fin qs.length, lam ^ (k : ℕ) * wordAt C qs[k]) →
      J (qs, lam, qs.map W) (commits h₀)) :
    escRet (fun g h ↦ J g (commits h)) h₀ [] (queryFrag per (P.κ + P.R) t c) ≤
      eQueryUd P P' t := by
  unfold escRet
  rw [retExp_commits (fun g cs ↦ if J g cs then 0 else 1), List.append_nil]
  obtain ⟨A, hA, hcatch⟩ := exists_agreeSet_ud P P' hκ Q' C Φ σ hviol hone
  refine (retExp_queryFrag_le per (P.κ + P.R) t c hper hpd h₀ hW _
    (fun q ↦ ∀ h : q < P.n, (⟨q, h⟩ : Fin P.n) ∈ A)
    (((t * P'.listMax : ℕ) : ENNReal) / Fintype.card E) ?_).trans ?_
  · intro qs hr hlen
    by_cases hall : ∀ q ∈ qs, ∀ h : q < P.n, (⟨q, h⟩ : Fin P.n) ∈ A
    · have : allIn (fun q ↦ ∀ h : q < P.n, (⟨q, h⟩ : Fin P.n) ∈ A) qs = 1 := by
        unfold allIn
        split_ifs with h
        · rfl
        · exact absurd hall h
      rw [this]
      exact (avg_le_one _ fun _ ↦ by split_ifs <;> simp).trans le_self_add
    · have hgood : QueryGoodUd P P' hκ Q' C Φ σ qs := by
        by_contra hng; exact hall (hcatch qs hng)
      have hcard := card_lambda_bad_le_ud P P' hκ Q' C Φ σ qs hr hgood
      refine le_trans ?_ le_add_self
      rw [avg_ite_le, ENNReal.div_eq_inv_mul]
      gcongr
      have hsub := Finset.card_le_card (s := univ.filter fun lam ↦ ¬ J (qs, lam, qs.map W)
          (commits h₀)) (t := univ.filter fun lam : E ↦ ¬ Viol P' Q'
          (fun r ↦ Φ r + 1 * lam * Verifier.inducedWeight P.κ qs (powers lam qs.length) r)
          (σ + 1 * lam * ∑ k : Fin qs.length, lam ^ (k : ℕ) * wordAt C qs[k])) fun lam hlam ↦ by
        simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hlam ⊢
        exact fun hv ↦ hlam (hJ qs lam hr hlen hv)
      rw [← hlen]
      exact_mod_cast hsub.trans hcard
  · rw [card_filter_mem, eQueryUd]
    exact add_le_add (pow_frac_le P A hA t) le_rfl

open Classical in
/-- **The query group of the final level**, from the residual's doom `FinViol`. -/
theorem escRet_queryFrag_le_finViol (P : LevelCode) (per t c : ℕ) (hper : 1 ≤ per)
    (hpd : per * (P.κ + P.R) ≤ 192)
    (h₀ : List Ev) {wd : ℕ} {W : Word} (hW : (commits h₀)[c]? = some (P.κ + P.R, wd, W))
    (C : Fin P.n → E) (Φ : List E → E) (σ : E)
    (G : (Fin P.κ → Bool) → E) (hD : FinViol P C Φ σ G)
    (J : List ℕ × E × List (List K) → List (ℕ × ℕ × Word) → Prop)
    (hJ : ∀ (qs : List ℕ) (lam : E), (∀ q ∈ qs, q < P.n) → qs.length = t →
      ∑ x, (Φ (bitsL x) + 1 * lam * Verifier.inducedWeight P.κ qs (powers lam qs.length)
          (bitsL x)) * G x ≠
        σ + 1 * lam * ∑ k : Fin qs.length, lam ^ (k : ℕ) * wordAt C qs[k] →
      J (qs, lam, qs.map W) (commits h₀)) :
    escRet (fun g h ↦ J g (commits h)) h₀ [] (queryFrag per (P.κ + P.R) t c) ≤
      eQueryFinal P t := by
  unfold escRet
  rw [retExp_commits (fun g cs ↦ if J g cs then 0 else 1), List.append_nil]
  obtain ⟨A, hA, hcatch⟩ := exists_agreeSet_finViol P C Φ σ G hD
  refine (retExp_queryFrag_le per (P.κ + P.R) t c hper hpd h₀ hW _
    (fun q ↦ ∀ h : q < P.n, (⟨q, h⟩ : Fin P.n) ∈ A) ((t : ENNReal) / Fintype.card E) ?_).trans ?_
  · intro qs hr hlen
    by_cases hall : ∀ q ∈ qs, ∀ h : q < P.n, (⟨q, h⟩ : Fin P.n) ∈ A
    · have : allIn (fun q ↦ ∀ h : q < P.n, (⟨q, h⟩ : Fin P.n) ∈ A) qs = 1 := by
        unfold allIn
        split_ifs with h
        · rfl
        · exact absurd hall h
      rw [this]
      exact (avg_le_one _ fun _ ↦ by split_ifs <;> simp).trans le_self_add
    · have hgood : QueryGoodFinal P C Φ σ G qs := by
        by_contra hng; exact hall (hcatch qs hng)
      have hcard := card_lambda_bad_le_final P C Φ σ G qs hr hgood
      refine le_trans ?_ le_add_self
      rw [avg_ite_le, ENNReal.div_eq_inv_mul]
      gcongr
      have hsub := Finset.card_le_card (s := univ.filter fun lam ↦ ¬ J (qs, lam, qs.map W)
          (commits h₀)) (t := univ.filter fun lam : E ↦
          ∑ x, (Φ (bitsL x) + 1 * lam * Verifier.inducedWeight P.κ qs (powers lam qs.length)
            (bitsL x)) * G x =
          σ + 1 * lam * ∑ k : Fin qs.length, lam ^ (k : ℕ) * wordAt C qs[k]) fun lam hlam ↦ by
        simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hlam ⊢
        by_contra hne
        exact hlam (hJ qs lam hr hlen hne)
      rw [← hlen]
      exact_mod_cast hsub.trans hcard
  · rw [card_filter_mem, eQueryFinal]
    exact add_le_add (pow_frac_le P A hA t) le_rfl

end
end LeanVM.Protocol.Whir.Sound
