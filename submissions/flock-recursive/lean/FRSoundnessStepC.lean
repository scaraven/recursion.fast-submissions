-- New for `flock-recursive` (BLUEPRINT §5.1–§5.2, A.10; stage S-G1c).
import FRSoundnessStepB

/-!
# The composed doom `Rej ∨ D_φ` and the generic rows (BLUEPRINT A.10, §5.2)

* **Part A: composition** (A.10, ratified). The entry's doom is `DC Rej Dp L es := Rej L es ∨
  Dp (|es| − 1) L es`: a failed asserted check (`Rej`), or the doom of the position's phase.
  `RejOK`: `Rej` is monotone, unchanged by appending at a squeeze position (every asserted check
  completes at an absorb), and stable under the charging log. **`stepObl_compose`** reduces the
  five obligations of `DC` to the same obligations for `DPos Dp` under `¬ Rej`: the rows never
  see `Rej` except as the assumption that the earlier checks passed.
* **Part B: the single-squeeze rows.** `single_F_le` / `single_K_le`: if every escaping answer has
  its first F coordinate (its K challenge) in a set of `s` bad challenges, at most `s·2^128`
  (`s`) answers escape (`card_chF_fiber`, `card_chK_fiber`).
* **Part C: the P2 row's arithmetic.** `p2_row_le`: at every level of both ladders,
  `(1 − eᵢ/nᵢ)^{tᵢ} ≤ 15/2^124 − 2·2^-142 − 2^-238 = deltaR` (kernel-checked rationals;
  `deltaR_coe`).
  `card_idx_in`: the answers whose first `c` indices of `b` bits lie in `S` number
  `|S|^c · 2^(256 − c b)` (`card_idx_fiber`, summed over `S^c`).
-/

namespace FR.Snd
open RecursionFast FR.Merkle Finset
open scoped NNReal

set_option linter.constructorNameAsVariable false

/-! ## Part A: the composed doom -/

/-- The doom of the position of a chain's last entry. -/
def DPos (Dp : ℕ → Log → Log → Prop) (L es : Log) : Prop := Dp (es.length - 1) L es

/-- **The composed doom** (A.10): a failed asserted check, or the current phase's doom. -/
def DC (Rej : Log → Log → Prop) (Dp : ℕ → Log → Log → Prop) (L es : Log) : Prop :=
  Rej L es ∨ DPos Dp L es

/-- What `Rej` must satisfy: monotone; unchanged by an entry at a squeeze position; stable under
the charging log. -/
structure RejOK (Rej : Log → Log → Prop) : Prop where
  mono : ∀ L es x, Rej L es → Rej L (es ++ [x])
  sq : ∀ L es x, fsItems[es.length]? = some .squeeze → (Rej L (es ++ [x]) ↔ Rej L es)
  stab : ∀ L i, ¬ Bad L → IsChain L i → ∀ k as,
    (Rej (L.take i) (ext ((entriesOf L (pathOf L i)).take k) as) ↔
      Rej L (ext ((entriesOf L (pathOf L i)).take k) as))

theorem length_ext1 (es : Log) (a : Digest) : (ext1 es a).length = es.length + 1 := by
  simp [ext1]

/-- Inside a multi-squeeze phase, `Rej` does not change along a formal extension. -/
theorem rej_ext {Rej : Log → Log → Prop} (hR : RejOK Rej) {L es₀ : Log} {s0 r : ℕ}
    (hl : es₀.length = s0 + 1) (hr : fsRnd (s0 + 1) = some (s0, r)) :
    ∀ as : List Digest, as.length ≤ r → (Rej L (ext es₀ as) ↔ Rej L es₀) := by
  obtain ⟨-, hpr, hspec⟩ := fsRnd_ok _ _ _ hr
  intro as
  induction as using List.reverseRecOn with
  | nil => intro _; rfl
  | append_singleton as a ih =>
    intro hlen
    simp only [List.length_append, List.length_singleton] at hlen
    rw [ext_append, ext1, hR.sq _ _ _ ?_, ih (by omega)]
    rw [length_ext as es₀, hl]
    exact (hspec _ (by omega) (by omega)).1

/-- `condCount` depends on the escape predicate only along the extensions of length `r`. -/
theorem condCount_congr {D D' : Log → Log → Prop} {L es₀ : Log} {r : ℕ}
    (h : ∀ as : List Digest, as.length = r → (EscAtG D L (ext es₀ as) ↔ EscAtG D' L (ext es₀ as))) :
    condCount D L es₀ r [] = condCount D' L es₀ r [] := by
  classical
  unfold condCount extCount
  congr 3
  exact Finset.filter_congr fun v _ => h _ (by simp)

/-- A position of a multi-squeeze phase is a squeeze. -/
theorem sq_of_fsRnd {p s0 r : ℕ} (h : fsRnd p = some (s0, r)) :
    fsItems[p]? = some .squeeze := by
  obtain ⟨h1, h2, hs⟩ := fsRnd_ok _ _ _ h
  exact (hs p h1 h2).1

open Classical in
/-- **`stepObl_compose`**: the obligations of the composed doom from those of the phases' doom
under `¬ Rej`. -/
theorem stepObl_compose {Rej : Log → Log → Prop} {Dp : ℕ → Log → Log → Prop} {δ : ℝ≥0} {N : ℕ}
    (hR : RejOK Rej)
    (habs : ∀ L es x len, Matches (es ++ [x]) → fsItems[es.length]? = some (.absorb len) →
      ¬ Rej L es → DPos Dp L es → Rej L (es ++ [x]) ∨ DPos Dp L (es ++ [x]))
    (hmid : ∀ L es x s0 r, Matches (es ++ [x]) → fsRnd es.length = some (s0, r) →
      es.length < s0 + r → ¬ Rej L es → (DPos Dp L (es ++ [x]) ↔ DPos Dp L es))
    (hsingle : ∀ L es, Matches es → fsItems[es.length]? = some .squeeze →
      fsRnd es.length = none → ¬ Rej L es →
      (Finset.univ.filter fun a => DPos Dp L es ∧ ¬ DPos Dp L (ext1 es a)).card ≤ N)
    (hround : ∀ L es₀ s0 r, Matches es₀ → es₀.length = s0 + 1 →
      fsRnd (s0 + 1) = some (s0, r) → ¬ Rej L es₀ → condCount (DPos Dp) L es₀ r [] ≤ δ)
    (hstab : ∀ L i, ¬ Bad L → IsChain L i → ∀ k as,
      (DPos Dp (L.take i) (ext ((entriesOf L (pathOf L i)).take k) as) ↔
        DPos Dp L (ext ((entriesOf L (pathOf L i)).take k) as))) :
    StepObl (DC Rej Dp) fsRnd δ N where
  habs L es x len hm hit hd := by
    by_cases hr : Rej L es
    · exact Or.inl (hR.mono _ _ _ hr)
    · exact habs L es x len hm hit hr (hd.resolve_left hr)
  hmid L es x s0 r hm hrnd hlt := by
    have hrej := hR.sq L es x (sq_of_fsRnd hrnd)
    by_cases hr : Rej L es
    · exact ⟨fun _ => Or.inl hr, fun _ => Or.inl (hrej.mpr hr)⟩
    · have := hmid L es x s0 r hm hrnd hlt hr
      simp only [DC, hrej, hr, false_or, this]
  hsingle L es hm hit hrnd := by
    by_cases hr : Rej L es
    · rw [Finset.filter_false_of_mem fun a _ h =>
        h.2 (Or.inl ((hR.sq L es _ hit).mpr hr))]
      simp
    · refine le_trans (Finset.card_le_card fun a ha => ?_) (hsingle L es hm hit hrnd hr)
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, DC, not_or] at ha ⊢
      exact ⟨ha.1.resolve_left hr, ha.2.2⟩
  hround L es₀ s0 r hm hl hrnd := by
    have hext := rej_ext hR (L := L) hl hrnd
    have hr1 : 1 ≤ r := by have := (fsRnd_ok _ _ _ hrnd).2.1; omega
    by_cases hr : Rej L es₀
    · rw [condCount_eq_zero]
      · exact zero_le
      intro as has ⟨_, _, hnd⟩
      exact hnd (Or.inl ((hext as has.le).mpr hr))
    · refine le_trans (le_of_eq (condCount_congr fun as has => ?_))
        (hround L es₀ s0 r hm hl hrnd hr)
      have hne : as ≠ [] := by rintro rfl; simp at has; omega
      have h1 : ¬ Rej L (ext es₀ as) := fun h => hr ((hext as has.le).mp h)
      have h2 : ¬ Rej L (ext es₀ as).dropLast := by
        rw [ext_dropLast _ hne]
        exact fun h => hr ((hext _ (by simp; omega)).mp h)
      simp only [EscAtG, DC, h1, h2, false_or]
  hstab L i hb hci k as := by
    simp only [DC, hR.stab L i hb hci k as, hstab L i hb hci k as]

/-! ## Part B: the single-squeeze rows -/

open Classical in
/-- **A single F squeeze**: escapes only at a bad first F coordinate, at most `s` of them. -/
theorem single_F_le (P : Digest → Prop) (S : Finset F) {s : ℕ} (hS : S.card ≤ s)
    (h : ∀ a, P a → chF a 0 ∈ S) : (Finset.univ.filter P).card ≤ s * 2 ^ 128 :=
  le_trans (Finset.card_le_card (t := Finset.univ.filter fun a : Digest => chF a 0 ∈ S)
      fun a ha => by
        simp only [Finset.mem_filter, Finset.mem_univ, true_and] at ha ⊢; exact h a ha)
    (by rw [card_chF_fiber]; exact Nat.mul_le_mul_right _ hS)

open Classical in
/-- **A single K squeeze**: escapes only at a bad K challenge, at most `s` of them. -/
theorem single_K_le (P : Digest → Prop) (S : Finset K) {s : ℕ} (hS : S.card ≤ s)
    (h : ∀ a, P a → chK a ∈ S) : (Finset.univ.filter P).card ≤ s :=
  le_trans (Finset.card_le_card (t := Finset.univ.filter fun a : Digest => chK a ∈ S)
      fun a ha => by
        simp only [Finset.mem_filter, Finset.mem_univ, true_and] at ha ⊢; exact h a ha)
    (by rw [card_chK_fiber]; exact hS)

open Classical in
/-- **A round row over F** (degree-2 and degree-3 rounds, §5.2): from a false claim, the answers
whose round passes its check and whose next claim is true number at most `deg e · 2^128`
(`round_escape_le`, `card_chF_fiber`). -/
theorem round_row_F (e : Expr) (ts : Array (Array F)) {m : ℕ}
    (hts : ∀ t ∈ ts, t.size = 2 ^ (m + 1)) {claim : F} (hw : claim ≠ trueSum e ts (m + 1))
    (g : Array F) (P : Digest → Prop)
    (hP : ∀ a, P a → (g.size = e.deg + 1 ∧ peval g 0 + peval g 1 = claim) ∧
      peval g (chF a 0) = trueSum e (ts.map (bind0 · (chF a 0))) m) :
    (Finset.univ.filter P).card ≤ e.deg * 2 ^ 128 :=
  single_F_le P _ (round_escape_le e ts hts hw g) fun a ha => by
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]; exact hP a ha

open Classical in
/-- **A round row over K** (P1, Pf): at most `deg e` answers (`card_chK_fiber`). -/
theorem round_row_K (e : Expr) (ts : Array (Array K)) {m : ℕ}
    (hts : ∀ t ∈ ts, t.size = 2 ^ (m + 1)) {claim : K} (hw : claim ≠ trueSum e ts (m + 1))
    (g : Array K) (P : Digest → Prop)
    (hP : ∀ a, P a → (g.size = e.deg + 1 ∧ peval g 0 + peval g 1 = claim) ∧
      peval g (chK a) = trueSum e (ts.map (bind0 · (chK a))) m) :
    (Finset.univ.filter P).card ≤ e.deg :=
  single_K_le P _ (round_escape_le e ts hts hw g) fun a ha => by
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]; exact hP a ha

/-! ## Part C: the P2 row -/

/-- The proximity parameters of level `i` of kind `κ`: `n = 2^log₂n`, `k = n/2^(i+1)`,
`e = ⌊(n − k)/2⌋` (§2.2). -/
def lvN (κ : Kind) (i : ℕ) : ℕ := 2 ^ (lvl κ i).logN
def lvK (κ : Kind) (i : ℕ) : ℕ := lvN κ i / 2 ^ (i + 1)
def lvE (κ : Kind) (i : ℕ) : ℕ := (lvN κ i - lvK κ i) / 2

/-- Control: the parameters are `pcsLevels`'s (the levels `mca_ud_line` is checked at). -/
theorem lv_eq_pcsLevels :
    ((List.range 5).map fun i => (lvN .P30 i, lvK .P30 i, lvE .P30 i)) ++
      ((List.range 5).map fun i => (lvN .L32 i, lvK .L32 i, lvE .L32 i)) = pcsLevels := by
  decide

/-- **The P2 row** (§5.2), in ℚ as `positions_bad_le` states it: at every level of every kind,
`(1 − eᵢ/nᵢ)^{tᵢ} ≤ 15/2^124 − 2·2^-142 − 2^-238` (kernel arithmetic: the exponents exceed
`norm_num`'s). -/
theorem p2_row_le_q (κ : Kind) (i : ℕ) (hi : i < 5) :
    (1 - (lvE κ i : ℚ) / lvN κ i) ^ (lvl κ i).t ≤ 15 / 2 ^ 124 - 2 / 2 ^ 142 - 1 / 2 ^ 238 := by
  interval_cases i <;> cases κ <;> decide +kernel

/-- **The P2 row against `deltaR`.** -/
theorem p2_row_le (κ : Kind) (i : ℕ) (hi : i < 5) :
    ((1 - (lvE κ i : ℚ) / lvN κ i) ^ (lvl κ i).t : ℝ) ≤ deltaR := by
  rw [deltaR_coe]
  have := p2_row_le_q κ i hi
  have h : ((15 / 2 ^ 124 - 2 / 2 ^ 142 - 1 / 2 ^ 238 : ℚ) : ℝ) =
      15 / 2 ^ 124 - 2 / 2 ^ 142 - 1 / 2 ^ 238 := by push_cast; ring
  rw [← h]
  exact_mod_cast this

theorem idx_lt (b : ℕ) (a : Digest) (i : ℕ) : idxOf b a i < 2 ^ b :=
  Nat.mod_lt _ (by positivity)

open Classical in
/-- **The answers whose first `c` indices of `b` bits lie in `S`** number `|S|^c · 2^(256 − cb)`. -/
theorem card_idx_in (b c : ℕ) (hcb : c * b ≤ 256) (S : Finset (Fin (2 ^ b))) :
    (Finset.univ.filter fun a : Digest =>
      ∀ j : Fin c, (⟨idxOf b a j, idx_lt b a j⟩ : Fin (2 ^ b)) ∈ S).card =
      S.card ^ c * 2 ^ (256 - c * b) := by
  have hU : (Finset.univ.filter fun a : Digest =>
      ∀ j : Fin c, (⟨idxOf b a j, idx_lt b a j⟩ : Fin (2 ^ b)) ∈ S) =
      (Fintype.piFinset fun _ : Fin c => S).biUnion fun f =>
        Finset.univ.filter fun a : Digest => ∀ j : Fin c, idxOf b a j = f j := by
    ext a
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_biUnion,
      Fintype.mem_piFinset]
    constructor
    · intro h
      exact ⟨fun j => ⟨idxOf b a j, idx_lt b a j⟩, h, fun j => rfl⟩
    · rintro ⟨f, hf, he⟩ j
      have : (⟨idxOf b a j, idx_lt b a j⟩ : Fin (2 ^ b)) = f j := Fin.ext (he j)
      rw [this]; exact hf j
  rw [hU, Finset.card_biUnion]
  · rw [Finset.sum_congr rfl fun f _ => card_idx_fiber b c hcb f, Finset.sum_const,
      Fintype.card_piFinset, smul_eq_mul]
    simp
  · intro f _ g _ hfg
    refine Finset.disjoint_left.mpr fun a ha hb => hfg ?_
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at ha hb
    funext j; exact Fin.ext ((ha j).symm.trans (hb j))

/-- The indices answer `s` contributes to the first `t` (`per` per answer). -/
def pc (per t s : ℕ) : ℕ := min per (t - s * per)

theorem sum_pc (per : ℕ) : ∀ r t : ℕ, t ≤ r * per → ∑ s ∈ range r, pc per t s = t
  | 0, t, h => by simp at h; simp [h]
  | r + 1, t, h => by
    have hs : ∀ s, pc per t (s + 1) = pc per (t - per) s := fun s => by
      unfold pc; rw [Nat.succ_mul]; congr 1; omega
    rw [Finset.sum_range_succ', Finset.sum_congr rfl fun s _ => hs s,
      sum_pc per r (t - per) (by rw [Nat.succ_mul] at h; omega)]
    unfold pc; omega

/-- The answer at Fiat–Shamir position `n + s` of a formal extension of a chain of length `n`. -/
theorem ansAt_ext {es₀ : Log} : ∀ (as : List Digest) {s : ℕ} (hs : s < as.length),
    ansAt (ext es₀ as) (es₀.length + s) = as[s] := by
  intro as
  induction as using List.reverseRecOn with
  | nil => intro s hs; simp at hs
  | append_singleton as a ih =>
    intro s hs
    simp only [List.length_append, List.length_singleton] at hs
    rw [ext_append, ext1]
    by_cases h : s < as.length
    · rw [ansAt, entAt_append _ _ (by rw [length_ext]; omega), ← ansAt, ih h,
        List.getElem_append_left h]
    · have hs' : s = as.length := by omega
      subst hs'
      simp [ansAt, entAt, length_ext]

/-- `S` as a set of naturals. -/
theorem mem_map_val {b : ℕ} (S : Finset (Fin (2 ^ b))) {x : ℕ} (hx : x < 2 ^ b) :
    x ∈ S.map Fin.valEmbedding ↔ (⟨x, hx⟩ : Fin (2 ^ b)) ∈ S := by
  simp only [Finset.mem_map, Fin.valEmbedding_apply]
  exact ⟨fun ⟨y, hy, he⟩ => by rwa [show (⟨x, hx⟩ : Fin (2 ^ b)) = y from Fin.ext he.symm],
    fun h => ⟨_, h, rfl⟩⟩

/-- An answer tuple read as one list of indices: answer `k / per`, index `k mod per`. -/
def vAt {r : ℕ} (v : Fin r → Digest) (s : ℕ) : Digest := if h : s < r then v ⟨s, h⟩ else 0

theorem vAt_of_lt {r : ℕ} (v : Fin r → Digest) {s : ℕ} (h : s < r) : vAt v s = v ⟨s, h⟩ := by
  simp [vAt, h]

open Classical in
/-- **The answer tuples whose first `t` indices lie in `S`** number
`Π_s |S|^{c_s}·2^(256 − c_s b)`. -/
theorem card_pos_in (b per r t : ℕ) (hper : 0 < per) (hpb : per * b ≤ 256) (ht : t ≤ r * per)
    (S : Finset (Fin (2 ^ b))) :
    (univ.filter fun v : Fin r → Digest => ∀ k < t,
      idxOf b (vAt v (k / per)) (k % per) ∈ S.map Fin.valEmbedding).card =
      ∏ s : Fin r, S.card ^ pc per t s * 2 ^ (256 - pc per t s * b) := by
  have hU : (univ.filter fun v : Fin r → Digest => ∀ k < t,
      idxOf b (vAt v (k / per)) (k % per) ∈ S.map Fin.valEmbedding) =
      Fintype.piFinset fun s : Fin r => univ.filter fun a : Digest =>
        ∀ j : Fin (pc per t s), (⟨idxOf b a j, idx_lt b a j⟩ : Fin (2 ^ b)) ∈ S := by
    ext v
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Fintype.mem_piFinset]
    constructor
    · intro h s j
      have hj := j.2
      simp only [pc, lt_min_iff] at hj
      have := h (per * s + j) (by rw [mul_comm]; omega)
      rwa [Nat.mul_add_div hper, Nat.div_eq_of_lt hj.1, add_zero, Nat.mul_add_mod,
        Nat.mod_eq_of_lt hj.1, vAt_of_lt v s.2, mem_map_val] at this
    · intro h k hk
      have hs : k / per < r := Nat.div_lt_of_lt_mul (by rw [mul_comm]; omega)
      have hj : k % per < pc per t (k / per) := by
        simp only [pc, lt_min_iff]
        refine ⟨Nat.mod_lt _ hper, ?_⟩
        have := Nat.div_add_mod k per
        rw [mul_comm] at this
        omega
      have := h ⟨k / per, hs⟩ ⟨k % per, hj⟩
      rw [vAt_of_lt v hs, mem_map_val]
      exact this
  rw [hU, Fintype.card_piFinset]
  refine Finset.prod_congr rfl fun s _ => card_idx_in b _ ?_ S
  exact le_trans (Nat.mul_le_mul_right _ (min_le_left _ _)) hpb

open Classical in
/-- **The P2 row's count** (`hround`): if the phase's escape puts each of its first `t` positions
(`posAt`, `per` per answer, `b` bits) in `S`, its conditional count from the entry is at most
`(|S|/2^b)^t`. -/
theorem p2_round_le {D : Log → Log → Prop} {L es₀ : Log} {s0 r b per t : ℕ}
    (hl : es₀.length = s0 + 1) (hper : 0 < per) (hpb : per * b ≤ 256) (ht : t ≤ r * per)
    (S : Finset (Fin (2 ^ b)))
    (hesc : ∀ as : List Digest, as.length = r → EscAtG D L (ext es₀ as) →
      ∀ k < t, posAt (ext es₀ as) s0 b per k ∈ S.map Fin.valEmbedding) :
    condCount D L es₀ r [] ≤ ((S.card : ℝ≥0) / 2 ^ b) ^ t := by
  unfold condCount extCount
  simp only [List.length_nil, Nat.sub_zero, List.nil_append]
  have hle := Finset.card_le_card (s := univ.filter fun v : Fin r → Digest =>
      EscAtG D L (ext es₀ (List.ofFn v)))
    (t := univ.filter fun v : Fin r → Digest => ∀ k < t,
      idxOf b (vAt v (k / per)) (k % per) ∈ S.map Fin.valEmbedding) fun v hv => by
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hv ⊢
    intro k hk
    have := hesc _ (by simp) hv k hk
    have hs : k / per < r := Nat.div_lt_of_lt_mul (by rw [mul_comm]; omega)
    rw [vAt_of_lt v hs]
    rwa [posAt, show s0 + 1 + k / per = es₀.length + k / per by omega,
      ansAt_ext _ (by simpa using hs), List.getElem_ofFn] at this
  rw [card_pos_in b per r t hper hpb ht S] at hle
  have hpow : ∀ s : Fin r, ((S.card ^ pc per t s * 2 ^ (256 - pc per t s * b) : ℕ) : ℝ≥0) /
      2 ^ 256 = ((S.card : ℝ≥0) / 2 ^ b) ^ pc per t s := fun s => by
    have hcb : pc per t s * b ≤ 256 := le_trans (Nat.mul_le_mul_right _ (min_le_left _ _)) hpb
    push_cast
    rw [div_pow, ← pow_mul, div_eq_div_iff (by positivity) (by positivity), mul_assoc, ← pow_add,
      show 256 - pc per t s * b + b * pc per t s = 256 by rw [mul_comm b]; omega]
  calc ((univ.filter fun v : Fin r → Digest => EscAtG D L (ext es₀ (List.ofFn v))).card : ℝ≥0) /
        2 ^ (256 * r)
      ≤ ((∏ s : Fin r, S.card ^ pc per t s * 2 ^ (256 - pc per t s * b) : ℕ) : ℝ≥0) /
          2 ^ (256 * r) := by gcongr
    _ = ∏ s : Fin r, ((S.card : ℝ≥0) / 2 ^ b) ^ pc per t s := by
        rw [show (2 : ℝ≥0) ^ (256 * r) = ∏ _s : Fin r, (2 : ℝ≥0) ^ 256 by
            rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin, ← pow_mul],
          Nat.cast_prod, ← Finset.prod_div_distrib]
        exact Finset.prod_congr rfl fun s _ => hpow s
    _ = ((S.card : ℝ≥0) / 2 ^ b) ^ t := by
        rw [Finset.prod_pow_eq_pow_sum, Fin.sum_univ_eq_sum_range (pc per t), sum_pc per r t ht]

/-- The P2 phase parameters (checked): `per ≥ 1` indices of `log₂ n` bits fit an answer, and the
phase's `sq` answers (sized for `m* = 32`) carry the `t` indices of every kind. -/
theorem p2_params (κ : Kind) (i : ℕ) (hi : i < 5) :
    0 < (lvl κ i).per ∧ (lvl κ i).per * (lvl κ i).logN ≤ 256 ∧
      (lvl κ i).t ≤ (lvlStar i).sq * (lvl κ i).per := by
  interval_cases i <;> cases κ <;> decide

/-- **The P2 row** (`hround`, §5.2): if level `i`'s escape puts all its `tᵢ` positions in a set
`S` with `|S| + eᵢ < nᵢ` (the consistency set of a far or wrong fold, A.10), the phase is charged
at most `deltaR` (`p2_round_le`, `p2_row_le`). -/
theorem p2_hround (κ : Kind) (i : ℕ) (hi : i < 5) {D : Log → Log → Prop} {L es₀ : Log} {s0 : ℕ}
    (hl : es₀.length = s0 + 1) (S : Finset (Fin (2 ^ (lvl κ i).logN)))
    (hS : S.card + lvE κ i < lvN κ i)
    (hesc : ∀ as : List Digest, as.length = (lvlStar i).sq → EscAtG D L (ext es₀ as) →
      ∀ k < (lvl κ i).t, posAt (ext es₀ as) s0 (lvl κ i).logN (lvl κ i).per k ∈
        S.map Fin.valEmbedding) :
    condCount D L es₀ (lvlStar i).sq [] ≤ deltaR := by
  obtain ⟨hper, hpb, ht⟩ := p2_params κ i hi
  have h1 := p2_round_le hl hper hpb ht S hesc
  have h2 := p2_row_le κ i hi
  rw [← NNReal.coe_le_coe] at h1 ⊢
  refine h1.trans (le_trans ?_ h2)
  push_cast
  have hn : (lvN κ i : ℝ) = 2 ^ (lvl κ i).logN := by simp [lvN]
  have hpos : (0 : ℝ) < 2 ^ (lvl κ i).logN := by positivity
  refine pow_le_pow_left₀ (by positivity) ?_ _
  rw [hn, div_le_iff₀ hpos, sub_mul, one_mul, div_mul_cancel₀ _ hpos.ne']
  have : (S.card : ℝ) + lvE κ i ≤ 2 ^ (lvl κ i).logN := by
    rw [← hn]; exact_mod_cast hS.le
  linarith

/-! ## Controls -/

/-- Control (positive): the empty `Rej` satisfies `RejOK`. -/
theorem rejOK_false : RejOK fun _ _ => False :=
  ⟨fun _ _ _ h => h, fun _ _ _ _ => Iff.rfl, fun _ _ _ _ _ _ => Iff.rfl⟩

/-- Control (negative): a `Rej` that changes at a squeeze position (here Z1's first, position 3)
is not `RejOK`. -/
theorem not_rejOK_len : ¬ RejOK fun _ es => 4 ≤ es.length := by
  intro h
  have h3 : fsItems[(List.replicate 3 (default : ByteArray × Digest)).length]? = some .squeeze := by
    simp only [List.length_replicate]; decide +kernel
  have := (h.sq [] _ default h3).mp (by simp)
  simp at this

/-- Control: level 0's last answer (`L32`: 12 indices per answer, 290 indices) carries 2. -/
theorem pc_last : pc 12 290 24 = 2 ∧ pc 12 290 23 = 12 := by decide

end FR.Snd
