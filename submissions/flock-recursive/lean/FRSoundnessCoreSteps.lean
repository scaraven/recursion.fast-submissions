-- New for `flock-recursive` (BLUEPRINT §10 changes 27 (B) step 3; stage RET-1): the position-free
-- declarations of the 3.x soundness modules that revision 4.1 reuses, moved here verbatim (same
-- names, statements and proofs) from `FRSoundnessStepA` (14), `FRSoundnessStepB` (30),
-- `FRSoundnessStepC` (19), `FRSoundnessTruths` (13), `FRSoundnessStepD` (6), `FRSoundnessStepE`
-- (30). Content: the log readers (`entAt`, `ansAt`, `msgAt`, `fAt`, `kAt`, `Agree`), the batched
-- and asserted rounds' claims (`clR`, `clR2`, `bindAll`, `bindL`, `Chk2`, `DC`), `mlDoom`/`msD`,
-- the ε arithmetic (`epsD`, `epsH`, `epsR`, `deltaR`) and the per-round counts (`round_row_*`,
-- `single_*_le`, `coords_round_le`, `seq_round_le`). The 3.x modules import this one.
import FRSoundnessCoreDefs
import FRSumcheck
import FRProximityFold
import FRRS

/-! ## From `FRSoundnessStepA` (14 declarations) -/

namespace FR.Snd

open RecursionFast FR.Merkle

/-- The entry at Fiat–Shamir position `p` (`default` past the end). -/
def entAt (es : Log) (p : ℕ) : ByteArray × Digest := es.getD p default

/-- The answer at position `p`. -/
def ansAt (es : Log) (p : ℕ) : Digest := (entAt es p).2

/-- The message of the absorb at position `p`: the query after its tag and state (40 bytes). -/
def msgAt (es : Log) (p : ℕ) : ByteArray := (entAt es p).1.extract 40 (entAt es p).1.size

/-- The F element at byte offset `o` of a message (16 bytes, A.2). -/
def readF (msg : ByteArray) (o : ℕ) : F := F.ofBytes (bytesAt msg o 16)

/-- The K element at byte offset `o` of a message (32 bytes). -/
def readK (msg : ByteArray) (o : ℕ) : K := K.ofBytes (bytesAt msg o 32)

/-- F coordinate `c` of the answer at position `p` (A.2: `c = 0` bytes `0…15`, `c = 1` `16…31`). -/
def fAt (es : Log) (p c : ℕ) : F := chF (ansAt es p) c

/-- The K challenge of the answer at position `p`. -/
def kAt (es : Log) (p : ℕ) : K := chK (ansAt es p)

/-- Coordinate `j` of the multi-squeeze phase entered at `s0` (A.2, S-0 deviation 7: coordinate
`2s + c` is F coordinate `c` of answer `s`). -/
def coordAt (es : Log) (s0 j : ℕ) : F := fAt es (s0 + 1 + j / 2) (j % 2)

/-- The `k`-th position of a P2 phase entered at `s0`, with `b` bits and `per` indices per answer
(A.2: index `k mod per` of answer `k / per`). -/
def posAt (es : Log) (s0 b per k : ℕ) : ℕ := idxOf b (ansAt es (s0 + 1 + k / per)) (k % per)

/-- Two logs agree on their first `n` positions. -/
def Agree (es es' : Log) (n : ℕ) : Prop := ∀ p < n, entAt es p = entAt es' p

theorem entAt_append (es xs : Log) {p : ℕ} (hp : p < es.length) :
    entAt (es ++ xs) p = entAt es p := by
  simp [entAt, List.getD_eq_getElem?_getD, List.getElem?_append_left hp]

theorem agree_append (es xs : Log) {n : ℕ} (hn : n ≤ es.length) : Agree (es ++ xs) es n :=
  fun p hp => entAt_append es xs (by omega)

theorem Agree.mono {es es' : Log} {n n' : ℕ} (h : Agree es es' n) (hn : n' ≤ n) :
    Agree es es' n' := fun p hp => h p (by omega)

theorem Agree.symm {es es' : Log} {n : ℕ} (h : Agree es es' n) : Agree es' es n :=
  fun p hp => (h p hp).symm

end FR.Snd

/-! ## From `FRSoundnessStepB` (30 declarations) -/

namespace FR.Snd

open RecursionFast FR.Merkle Finset

open scoped NNReal

/-- The entry's per-query knowledge error: `εR = 15/2^124 ≈ 2^-120.093`. -/
noncomputable def epsR : ℝ≥0 := 15 / 2 ^ 124

/-- **The Hide potential's per-query error** (§10 changes 15): its H row `2^-142` and its rounds'
`2^18/2^256 = 2^-238` (at most `eᵢ ≤ 2^18` hiding challenges per P1.i round). -/
noncomputable def epsH : ℝ≥0 := (2 : ℝ≥0)⁻¹ ^ 142 + (2 : ℝ≥0)⁻¹ ^ 238

/-- **The doom potential's per-query error**: `εD = εR − ε_H`, so that `εD + ε_H = εR`. -/
noncomputable def epsD : ℝ≥0 := epsR - epsH

/-- The rows' budget: `εD − 2^-142` (the H row takes `2^-142`, `badCount_frac_le`). -/
noncomputable def deltaR : ℝ≥0 := epsD - (2 : ℝ≥0)⁻¹ ^ 142

theorem h_le_epsR : (2 : ℝ≥0)⁻¹ ^ 142 ≤ epsR := by
  rw [epsR, inv_pow, ← one_div, div_le_div_iff₀ (by positivity) (by positivity)]
  norm_num

theorem epsH_le_epsR : epsH ≤ epsR := by
  rw [← NNReal.coe_le_coe, epsH, epsR]
  push_cast
  norm_num

theorem epsD_coe : (epsD : ℝ) = 15 / 2 ^ 124 - 1 / 2 ^ 142 - 1 / 2 ^ 238 := by
  rw [epsD, NNReal.coe_sub epsH_le_epsR, epsH, epsR]
  push_cast
  norm_num

theorem h_le_epsD : (2 : ℝ≥0)⁻¹ ^ 142 ≤ epsD := by
  rw [← NNReal.coe_le_coe, epsD_coe]
  push_cast
  norm_num

/-- **The two potentials' errors add up to `εR`** (kernel-checked: `ε_H ≤ εR`). -/
theorem epsD_add_epsH : epsD + epsH = epsR := tsub_add_cancel_of_le epsH_le_epsR

theorem deltaR_coe : (deltaR : ℝ) = 15 / 2 ^ 124 - 2 / 2 ^ 142 - 1 / 2 ^ 238 := by
  rw [deltaR, NNReal.coe_sub h_le_epsD, epsD_coe]
  push_cast
  ring

/-- **The doom potential's error**: the H row and the rows' budget fit `εD`. -/
theorem err_le_epsD : (badCount : ℝ≥0) / 2 ^ 256 + deltaR ≤ epsD :=
  calc (badCount : ℝ≥0) / 2 ^ 256 + deltaR ≤ (2 : ℝ≥0)⁻¹ ^ 142 + deltaR := by
        gcongr; exact badCount_frac_le
    _ = epsD := add_tsub_cancel_of_le h_le_epsD

/-- A single-squeeze row of `N` answers fits the budget when `N/2^256 ≤ deltaR` (in ℝ). -/
theorem N_le_deltaR {N : ℕ} (h : (N : ℝ) / 2 ^ 256 ≤ 15 / 2 ^ 124 - 2 / 2 ^ 142 - 1 / 2 ^ 238) :
    (N : ℝ≥0) ≤ 2 ^ 256 * deltaR := by
  rw [← NNReal.coe_le_coe, NNReal.coe_mul, deltaR_coe]
  push_cast
  rw [div_le_iff₀ (by positivity)] at h
  linarith

/-- A multi-squeeze phase on which `D` cannot escape is charged nothing. -/
theorem condCount_eq_zero {D : Log → Log → Prop} {L es₀ : Log} {r : ℕ}
    (h : ∀ as : List Digest, as.length = r → ¬ EscAtG D L (ext es₀ as)) :
    condCount D L es₀ r [] = 0 := by
  classical
  unfold condCount extCount
  rw [Finset.filter_false_of_mem fun v _ => h _ (by simp)]
  simp

/-- Binding one more challenge is mapping `bind0`. -/
theorem bindAll_append {R : Type*} [CommRing R] (ts : Array (Array R)) (rs : List R) (r : R) :
    bindAll ts (rs ++ [r]) = (bindAll ts rs).map (bind0 · r) := by
  induction rs generalizing ts with
  | nil => rfl
  | cons r' rs ih => exact ih _

theorem bindAll_size {R : Type*} [CommRing R] {m : ℕ} :
    ∀ (rs : List R) (ts : Array (Array R)), (∀ t ∈ ts, t.size = 2 ^ (rs.length + m)) →
      ∀ t ∈ bindAll ts rs, t.size = 2 ^ m
  | [], ts, h => fun t ht => by simpa using h t ht
  | r :: rs, ts, h => bindAll_size rs _ (map_bind0_size ts r fun t ht => by
      rw [h t ht]; congr 1; simp; omega)

section Rounds3

variable (b : ℕ)

/-- Round `l`'s coefficients from claim `c`: `c₀, c₁, c₂` from the message at `b + 2l`, and
`c₃ = c + (c₁ + c₂)` (`roundOpsF … 3`, `FRVIRSpec.g3`). -/
def g3At (es : Log) (l : ℕ) (c : F) : Array F :=
  #[readF (msgAt es (b + 2 * l)) 0, readF (msgAt es (b + 2 * l)) 16,
    readF (msgAt es (b + 2 * l)) 32,
    c + (readF (msgAt es (b + 2 * l)) 16 + readF (msgAt es (b + 2 * l)) 32)]

/-- Round `l`'s challenge: the first F coordinate of the answer at `b + 2l + 1`. -/
def rch (es : Log) (l : ℕ) : F := fAt es (b + 2 * l + 1) 0

/-- The first `l` challenges. -/
def rchs (es : Log) (l : ℕ) : List F := (List.range l).map (rch b es)

variable (c0 : Log → Log → F)

/-- The running claims: `c0`, then `g_l(r_l)`. -/
def clR (L es : Log) : ℕ → F
  | 0 => c0 L es
  | l + 1 => peval (g3At b es l (clR L es l)) (rch b es l)

variable (nr : Kind → ℕ)

variable (e : Expr) (T : Log → Log → Array (Array F))

variable {b c0 nr e T}

theorem peval_four (x0 x1 x2 x3 r : F) :
    peval #[x0, x1, x2, x3] r = x0 + r * (x1 + r * (x2 + r * x3)) := by
  simp [peval_eq_sum, Finset.sum_range_succ]
  ring

/-- The round's check always passes (`c₃` is set from the claim; characteristic two). -/
theorem g3_check (es : Log) (l : ℕ) (c : F) :
    peval (g3At b es l c) 0 + peval (g3At b es l c) 1 = c := by
  unfold g3At
  generalize readF (msgAt es (b + 2 * l)) 0 = x0
  generalize readF (msgAt es (b + 2 * l)) 16 = x1
  generalize readF (msgAt es (b + 2 * l)) 32 = x2
  rw [peval_four, peval_four]
  linear_combination (x0 + x1 + x2) * CharTwo.two_eq_zero (R := F)

theorem g3_size (es : Log) (l : ℕ) (c : F) : (g3At b es l c).size = 4 := rfl

theorem rchs_succ (es : Log) (l : ℕ) : rchs b es (l + 1) = rchs b es l ++ [rch b es l] := by
  simp [rchs, List.range_succ]

theorem rchs_congr {es es' : Log} {l : ℕ} (h : Agree es es' (b + 2 * l)) :
    rchs b es l = rchs b es' l := by
  unfold rchs rch fAt ansAt
  refine List.map_congr_left fun j hj => ?_
  rw [h _ (by simp at hj; omega)]

theorem clR_congr {L es es' : Log} (hc : c0 L es = c0 L es') :
    ∀ {l : ℕ}, Agree es es' (b + 2 * l) → clR b c0 L es l = clR b c0 L es' l
  | 0, _ => hc
  | l + 1, h => by
    simp only [clR]
    rw [clR_congr hc (h.mono (by omega))]
    simp only [g3At, rch, fAt, ansAt, msgAt, h (b + 2 * l) (by omega),
      h (b + 2 * l + 1) (by omega)]

theorem clR_log_congr {L L' es : Log} (hc : c0 L' es = c0 L es) :
    ∀ l, clR b c0 L' es l = clR b c0 L es l
  | 0 => hc
  | l + 1 => by simp only [clR, clR_log_congr hc l]

/-- What the truth must satisfy: it reads the entries before `b` only. -/
def TruthLocal (b : ℕ) (c0 : Log → Log → F) (T : Log → Log → Array (Array F)) : Prop :=
  ∀ L es es', Agree es es' b → T L es = T L es' ∧ c0 L es = c0 L es'

theorem entAt_ext1 (es : Log) (a : Digest) : (entAt (ext1 es a) es.length).2 = a := by
  simp [entAt, ext1]

theorem length_ext : ∀ (as : List Digest) (es : Log), (ext es as).length = es.length + as.length
  | [], _ => rfl
  | a :: as, es => by
    rw [show ext es (a :: as) = ext (ext1 es a) as from rfl, length_ext as]
    simp [ext1]; omega

theorem three_le_deltaR : ((3 * 2 ^ 128 : ℕ) : ℝ≥0) ≤ 2 ^ 256 * deltaR :=
  N_le_deltaR (by push_cast; norm_num)

end Rounds3

end FR.Snd

/-! ## From `FRSoundnessStepC` (19 declarations) -/

namespace FR.Snd

open RecursionFast FR.Merkle Finset

open scoped NNReal

set_option linter.constructorNameAsVariable false

/-- The doom of the position of a chain's last entry. -/
def DPos (Dp : ℕ → Log → Log → Prop) (L es : Log) : Prop := Dp (es.length - 1) L es

/-- **The composed doom** (A.10): a failed asserted check, or the current phase's doom. -/
def DC (Rej : Log → Log → Prop) (Dp : ℕ → Log → Log → Prop) (L es : Log) : Prop :=
  Rej L es ∨ DPos Dp L es

theorem length_ext1 (es : Log) (a : Digest) : (ext1 es a).length = es.length + 1 := by
  simp [ext1]

/-- `condCount` depends on the escape predicate only along the extensions of length `r`. -/
theorem condCount_congr {D D' : Log → Log → Prop} {L es₀ : Log} {r : ℕ}
    (h : ∀ as : List Digest, as.length = r → (EscAtG D L (ext es₀ as) ↔ EscAtG D' L (ext es₀ as))) :
    condCount D L es₀ r [] = condCount D' L es₀ r [] := by
  classical
  unfold condCount extCount
  congr 3
  exact Finset.filter_congr fun v _ => h _ (by simp)

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

/-- Control: level 0's last answer (`L32`: 12 indices per answer, 290 indices) carries 2. -/
theorem pc_last : pc 12 290 24 = 2 ∧ pc 12 290 23 = 12 := by decide

end FR.Snd

/-! ## From `FRSoundnessTruths` (13 declarations) -/

namespace FR.Snd

open RecursionFast FR.Merkle Finset

set_option linter.constructorNameAsVariable false

/-- Level `i`'s encoding with `carried` restricted to the query's windows. -/
def frEncW (i : ℕ) : MerkleEnc where
  nodeQ := nodeQ i
  colQ := colQ i
  parseNode := parseNode i
  parseCol := parseCol i
  carried q := (carried q).filter fun d => decide (d ∈ wins q)
  parseNode_nodeQ := parseNode_nodeQ i
  nodeQ_of_parseNode := nodeQ_of_parseNode i
  parseCol_colQ := parseCol_colQ i
  carried_nodeQ l r := by
    have hw : ∀ k, k < 4 → 8 + 16 * k + 32 ≤ 72 →
        bytesAt (nodeQ i l r) (8 + 16 * k) 32 ∈ wins (nodeQ i l r) := fun k hk h32 => by
      rw [wins, ite_eq_left (by rw [nodeQ_size]; unfold queryCap; norm_num)]
      refine List.mem_append_right _ (List.mem_filterMap.mpr ⟨k, ?_, ?_⟩)
      · rw [List.mem_range, nodeQ_size]; omega
      · rw [nodeQ_size, ite_eq_left h32]
    have hl := hw 0 (by norm_num) (by norm_num)
    have hr := hw 2 (by norm_num) (by norm_num)
    rw [show 8 + 16 * 0 = 8 by rfl, bytesAt_nodeQ_l] at hl
    rw [show 8 + 16 * 2 = 40 by rfl, bytesAt_nodeQ_r] at hr
    obtain ⟨cl, cr⟩ := carried_nodeQ i l r
    exact ⟨List.mem_filter.mpr ⟨cl, by simpa using hl⟩, List.mem_filter.mpr ⟨cr, by simpa using hr⟩⟩

/-- `colL` does not read `carried`. -/
theorem colL_frEncW (i : ℕ) (L : Log) : ∀ (h : ℕ) (d : Digest) (j : ℕ),
    colL (frEncW i) L d h j = colL (frEnc i) L d h j
  | 0, _, _ => rfl
  | h + 1, d, j => by
    simp only [colL]
    congr 1; funext e; congr 1; funext ab
    exact colL_frEncW i L h _ j

/-- **No bad event, no Merkle hit**: a hit under `frEncW` is a window hit. -/
theorem not_hit_of_not_bad {L : Log} (hb : ¬ Bad L) (i : ℕ) : ¬ Hit (frEncW i) L := by
  rintro ⟨a, b, hab, hbL, hm⟩
  have hm' := (List.mem_filter.mp hm).2
  simp only [decide_eq_true_eq] at hm'
  exact hb (Or.inr (Or.inl ⟨a, b, hab.le, hbL, hm'⟩))

/-- **`colL_take`**: on a non-bad log, the column read under a digest carried (within its
windows) by an entry of the prefix `L.take n` is the same on the prefix and on `L`. -/
theorem colL_take {L : Log} (hb : ¬ Bad L) (i n : ℕ) {d : Digest}
    (hd : ∃ e ∈ L.take n, d ∈ (frEncW i).carried e.1) (h j : ℕ) :
    colL (frEnc i) (L.take n) d h j = colL (frEnc i) L d h j := by
  have hnh : ¬ Hit (frEncW i) (L.take n ++ L.drop n) := by
    rw [List.take_append_drop]; exact not_hit_of_not_bad hb i
  rw [← colL_frEncW, ← colL_frEncW]
  cases hc : colL (frEncW i) (L.take n) d h j with
  | some col =>
    have := colL_append (E := frEncW i) (L.drop n) hc
    rw [List.take_append_drop] at this; exact this.symm
  | none =>
    cases hc' : colL (frEncW i) L d h j with
    | none => rfl
    | some col =>
      rw [← List.take_append_drop n L] at hc'
      rw [colL_prefix hnh hd hc'] at hc
      cases hc

/-- The bytes of a message read at `o` are the absorb query's bytes at `40 + o`. -/
theorem bytesAt_extract40 (q : ByteArray) (o : ℕ) (h : 40 + o + 32 ≤ q.size) :
    bytesAt (q.extract 40 q.size) o 32 = bytesAt q (40 + o) 32 := by
  ext k hk
  simp only [getElem_bytesAt _ _ _ _ hk, ByteArray.data_extract]
  rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, Array.getElem?_toList,
    Array.getElem?_toList, Array.getElem?_extract]
  simp only [ByteArray.size] at h
  rw [ite_eq_left (by have : q.size = q.data.size := rfl; omega)]
  congr 3
  omega

/-- **(a) A cap entry is carried (within its windows) by the cap's absorb query**: entry `c` of
an absorb of `len ≥ 32(c + 1)` bytes, at offset `40 + 32c = 8 + 16(2 + 2c)`. -/
theorem cap_carried {q : ByteArray} {len : ℕ} (hq : fsCheck (.absorb len) q = true)
    (hcap : q.size ≤ queryCap) {c : ℕ} (hc : 32 * (c + 1) ≤ len) (j : ℕ) :
    bytesAt (q.extract 40 q.size) (32 * c) 32 ∈ (frEncW j).carried q := by
  simp only [fsCheck, Bool.and_eq_true, beq_iff_eq] at hq
  obtain ⟨ht, hs⟩ := hq
  rw [bytesAt_extract40 q _ (by omega)]
  refine List.mem_filter.mpr ⟨?_, ?_⟩
  · simp only [carried, ht, ite_true]
    refine List.mem_cons_of_mem _ (List.mem_map.mpr ⟨c, ?_, rfl⟩)
    rw [List.mem_range, hs, Nat.lt_div_iff_mul_lt (by norm_num)]
    omega
  · rw [decide_eq_true_eq, wins, ite_eq_left hcap]
    refine List.mem_append_right _ (List.mem_filterMap.mpr ⟨2 + 2 * c, ?_, ?_⟩)
    · rw [List.mem_range]; omega
    · rw [ite_eq_left (by omega)]; congr 2; omega

/-- On a non-bad log, an entry answering a digest carried by entry `i` precedes `i`. -/
theorem ans_lt_of_carried {L : Log} (hb : ¬ Bad L) {i : ℕ} (hi : i < L.length) {j : ℕ}
    {d : Digest} (hd : d ∈ (frEncW j).carried (L[i]).1) {k : ℕ} (hk : k < L.length)
    (hkd : L[k].2 = d) : k < i := by
  by_contra hki
  rcases Nat.lt_or_eq_of_le (Nat.le_of_not_lt hki) with h | h
  · exact not_hit_of_not_bad hb j ⟨i, k, h, hk, hkd ▸ hd⟩
  · have hw := (List.mem_filter.mp hd).2
    simp only [decide_eq_true_eq] at hw
    exact hb (Or.inr (Or.inl ⟨i, k, h.le, hk, hkd ▸ hw⟩))

/-- Under the same hypotheses, the first preimage of `d` is read off `L.take i`. -/
theorem pre_take_own {L : Log} (hb : ¬ Bad L) {i : ℕ} (hi : i < L.length) {j : ℕ}
    {d : Digest} (hd : d ∈ (frEncW j).carried (L[i]).1) : pre (L.take i) d = pre L d := by
  have hnone : (L.drop i).find? (fun e => decide (e.2 = d)) = none := by
    rw [List.find?_eq_none]
    intro e he hed
    obtain ⟨m, hm, rfl⟩ := List.getElem_of_mem he
    rw [List.getElem_drop] at hed
    simp only [decide_eq_true_eq] at hed
    have := ans_lt_of_carried hb hi hd (by simp at hm; omega) hed
    omega
  conv_rhs => rw [← List.take_append_drop i L]
  simp only [pre, List.find?_append, hnone, Option.or_none]

/-- **(b) The cap's own absorb**: on a non-bad log, a column read under a digest carried by entry
`i` (e.g. the cap absorb as a chain's last entry) is the same on `L.take i` and on `L`. -/
theorem colL_take_own {L : Log} (hb : ¬ Bad L) {i : ℕ} (hi : i < L.length) {j : ℕ}
    {d : Digest} (hd : d ∈ (frEncW j).carried (L[i]).1) (h p : ℕ) :
    colL (frEnc j) (L.take i) d h p = colL (frEnc j) L d h p := by
  have hpre := pre_take_own hb hi hd
  cases h with
  | zero => simp only [colL, hpre]
  | succ h =>
    simp only [colL]
    rw [hpre]
    cases he : pre L d with
    | none => rfl
    | some e =>
      simp only [Option.bind_some]
      cases hn : (frEnc j).parseNode e.1 with
      | none => rfl
      | some ab =>
        simp only [Option.bind_some]
        have hmem : e ∈ L.take i := by
          rw [← hpre] at he; exact List.mem_of_find?_eq_some he
        have hc : ab.1 ∈ (frEncW j).carried e.1 ∧ ab.2 ∈ (frEncW j).carried e.1 := by
          rw [(frEncW j).nodeQ_of_parseNode e.1 ab.1 ab.2 hn]
          exact (frEncW j).carried_nodeQ _ _
        exact colL_take hb j i ⟨e, hmem, by split <;> simp [hc]⟩ h p

/-- Two sets of at least `n − e` positions meet in at least `n − 2e`. -/
theorem card_inter_ge {n e : ℕ} {A B : Finset (Fin n)} (hA : n - e ≤ A.card) (hB : n - e ≤ B.card) :
    n - 2 * e ≤ (A ∩ B).card := by
  have h1 := card_union_add_card_inter A B
  have h2 : (A ∪ B).card ≤ n := by simpa using card_le_univ (A ∪ B)
  omega

/-- **The coordinate split** (A.2, `ligerito.rs`): level `i + 1`'s weight table from a table over
level `i`'s folded message: variable 0 is the split bit (`1` for coordinate 0, `u` for
coordinate 1), the rest index the K element (`y = 2x + b`). Its MLE in the split bit at `β` is
`W(x)·û(β)`, `û(β) = 1 + β(1 + u)` (A.9's fold factor). -/
def wSplit (W : ℕ → K) (y : ℕ) : K := W (y / 2) * (if y % 2 = 0 then 1 else K.u)

theorem sum_range_two_mul {M : Type*} [AddCommMonoid M] (f : ℕ → M) :
    ∀ k, ∑ y ∈ range (2 * k), f y = ∑ x ∈ range k, (f (2 * x) + f (2 * x + 1))
  | 0 => by simp
  | k + 1 => by
    rw [show 2 * (k + 1) = 2 * k + 1 + 1 by ring, sum_range_succ, sum_range_succ,
      sum_range_two_mul f k, sum_range_succ, add_assoc]

open Classical in
/-- **The per-round hiding count** (Schwartz–Zippel, `zerocheck_bad_le` over K): for a family of
nonzero difference tables indexed by `P`, at most `|P|` values of a round's challenge make one of
them vanish when its first variable is bound. Over P1.i's `ℓᵢ` rounds with `|P| ≤ eᵢ`
(`card_not_jointAgree`) this is `eᵢ·ℓᵢ/|K|`, inside P1's cancellation charge. -/
theorem hide_round_le {ι : Type*} (P : Finset ι) {m : ℕ} (t : ι → Fin (2 ^ (m + 1)) → K)
    (ht : ∀ j ∈ P, t j ≠ 0) :
    (univ.filter fun c : K => ∃ j ∈ P, FR.fix0 (t j) c = 0).card ≤ P.card := by
  calc (univ.filter fun c : K => ∃ j ∈ P, FR.fix0 (t j) c = 0).card
      ≤ (P.biUnion fun j => univ.filter fun c => FR.fix0 (t j) c = 0).card :=
        card_le_card fun c hc => by
          simp only [mem_filter, mem_univ, true_and] at hc
          obtain ⟨j, hj, h⟩ := hc
          exact mem_biUnion.mpr ⟨j, hj, by simp [h]⟩
    _ ≤ ∑ j ∈ P, (univ.filter fun c => FR.fix0 (t j) c = 0).card := card_biUnion_le
    _ ≤ ∑ _j ∈ P, 1 := sum_le_sum fun j hj => zerocheck_bad_le _ (ht j hj)
    _ = P.card := by simp

end FR.Snd

/-! ## From `FRSoundnessStepD` (6 declarations) -/

namespace FR.Snd

open RecursionFast Finset

open scoped NNReal

set_option linter.constructorNameAsVariable false

/-- The coordinate tuple of `r` answers. -/
noncomputable def coordsOf {r : ℕ} (v : Fin r → Digest) : Fin r → F × F := fun s => chFEquiv (v s)

/-- **`card_coords_in`**: the answer tuples whose coordinates lie in `B` number exactly `|B|`. -/
theorem card_coords_in {r : ℕ} (B : Finset (Fin r → F × F)) :
    (univ.filter fun v : Fin r → Digest => coordsOf v ∈ B).card = B.card :=
  Finset.card_equiv (Equiv.piCongrRight fun _ => chFEquiv) fun v => by
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]; rfl

open Classical in
/-- **The coordinate row** (`hround`): if the escape puts the phase's coordinate tuple
(`fAt` at the `r` answers after the entry `s0`) in `B`, the phase's conditional count from its
entry is at most `|B| / 2^(256 r)`. -/
theorem coords_round_le {D : Log → Log → Prop} {L es₀ : Log} {s0 r : ℕ}
    (hl : es₀.length = s0 + 1) (B : Finset (Fin r → F × F))
    (hesc : ∀ as : List Digest, as.length = r → EscAtG D L (ext es₀ as) →
      (fun s : Fin r => (fAt (ext es₀ as) (s0 + 1 + s) 0, fAt (ext es₀ as) (s0 + 1 + s) 1)) ∈ B) :
    condCount D L es₀ r [] ≤ (B.card : ℝ≥0) / 2 ^ (256 * r) := by
  unfold condCount extCount
  simp only [List.length_nil, Nat.sub_zero, List.nil_append]
  have hle := Finset.card_le_card (s := univ.filter fun v : Fin r → Digest =>
      EscAtG D L (ext es₀ (List.ofFn v)))
    (t := univ.filter fun v : Fin r → Digest => coordsOf v ∈ B) fun v hv => by
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hv ⊢
    have := hesc _ (by simp) hv
    have hv' : ∀ s : Fin r, ∀ c, fAt (ext es₀ (List.ofFn v)) (s0 + 1 + s) c = chF (v s) c := by
      intro s c
      rw [fAt, show s0 + 1 + (s : ℕ) = es₀.length + s by omega,
        ansAt_ext _ (by simp), List.getElem_ofFn]
    simp only [hv'] at this
    exact this
  rw [card_coords_in B] at hle
  gcongr

/-- The count in probability form: `|B| / |F × F|^r`. -/
theorem coords_prob (r : ℕ) (B : Finset (Fin r → F × F)) :
    (B.card : ℝ≥0) / 2 ^ (256 * r) = (B.card : ℝ≥0) / (Fintype.card (F × F) : ℝ≥0) ^ r := by
  rw [Fintype.card_prod, F.card_F, pow_mul]; push_cast; ring_nf

/-- Control: the full set has count `1` (every tuple; `card_coords_in` is not an upper bound
only). -/
theorem card_coords_univ (r : ℕ) :
    (univ.filter fun v : Fin r → Digest => coordsOf v ∈ (univ : Finset (Fin r → F × F))).card =
      2 ^ (256 * r) := by
  rw [card_coords_in, Finset.card_univ, Fintype.card_fun, Fintype.card_prod, F.card_F,
    Fintype.card_fin, ← pow_add, ← pow_mul]

/-- Control: the empty set is never hit. -/
theorem card_coords_empty (r : ℕ) :
    (univ.filter fun v : Fin r → Digest => coordsOf v ∈ (∅ : Finset (Fin r → F × F))).card = 0 := by
  rw [card_coords_in, Finset.card_empty]

end FR.Snd

/-! ## From `FRSoundnessStepE` (30 declarations) -/

namespace FR.Snd

open RecursionFast FR.Merkle Finset

open scoped NNReal

set_option linter.constructorNameAsVariable false

/-- `r` coordinate pairs as `2r` coordinates, pair `s`'s coordinate `c` at `2s + c`. -/
def pairsEquiv (r : ℕ) : (Fin r → F × F) ≃ (Fin (r * 2) → F) :=
  (Equiv.arrowCongr (Equiv.refl _) (finTwoArrowEquiv F).symm).trans
    ((Equiv.curry _ _ _).symm.trans (Equiv.arrowCongr finProdFinEquiv (Equiv.refl F)))

theorem pairsEquiv_apply {r : ℕ} (u : Fin r → F × F) (j : Fin (r * 2)) :
    pairsEquiv r u j =
      if j.val % 2 = 0 then (u ⟨j / 2, by omega⟩).1 else (u ⟨j / 2, by omega⟩).2 := by
  simp only [pairsEquiv, Equiv.trans_apply, Equiv.arrowCongr_apply, Equiv.refl_symm,
    Equiv.coe_refl, Function.comp_apply, Equiv.curry_symm_apply, Function.uncurry_apply_pair,
    finTwoArrowEquiv_symm_apply, finProdFinEquiv_symm_apply, id]
  rcases Nat.mod_two_eq_zero_or_one j.val with h | h
  · have : Fin.modNat j = 0 := Fin.ext (by simp [Fin.modNat, h])
    simp [this, h, Fin.divNat]
  · have : Fin.modNat j = 1 := Fin.ext (by simp [Fin.modNat, h])
    simp [this, h, Fin.divNat]

open Classical in
/-- **The flattened coordinate row**: if a multi-squeeze phase's escape puts its `2r` coordinates
(`coordAt`) in a set `W`, its conditional count from the entry is at most `|W| / 2^(256 r)`. -/
theorem flat_round_le {D : Log → Log → Prop} {L es₀ : Log} {s0 r : ℕ}
    (hl : es₀.length = s0 + 1) (W : Finset (Fin (r * 2) → F))
    (hesc : ∀ as : List Digest, as.length = r → EscAtG D L (ext es₀ as) →
      (fun j : Fin (r * 2) => coordAt (ext es₀ as) s0 j) ∈ W) :
    condCount D L es₀ r [] ≤ (W.card : ℝ≥0) / 2 ^ (256 * r) := by
  have hB := coords_round_le (D := D) (L := L) hl (W.map (pairsEquiv r).symm.toEmbedding)
    fun as has hE => by
      rw [Finset.mem_map_equiv, Equiv.symm_symm]
      convert hesc as has hE using 1
      funext j
      rw [pairsEquiv_apply, coordAt]
      rcases Nat.mod_two_eq_zero_or_one j.val with h | h <;> simp [h]
  rwa [Finset.card_map] at hB

open Classical in
/-- **The Schwartz–Zippel row** (`seq_bad_le`): if a doom on the coordinate list holds at the
entry, loses at most `b i` values at coordinate `i`, and fails at every escape, the phase's charge
is at most `Σ_{i < 2r} b i / 2^128`. -/
theorem seq_round_le {D : Log → Log → Prop} {L es₀ : Log} {s0 r : ℕ}
    (hl : es₀.length = s0 + 1) (Doom : List F → Prop) (b : ℕ → ℕ)
    (hb : ∀ l, Doom l → (univ.filter fun c => ¬ Doom (l ++ [c])).card ≤ b l.length)
    (h0 : Doom [])
    (hesc : ∀ as : List Digest, as.length = r → EscAtG D L (ext es₀ as) →
      ¬ Doom (List.ofFn fun j : Fin (r * 2) => coordAt (ext es₀ as) s0 j)) :
    condCount D L es₀ r [] ≤ ((∑ i ∈ range (r * 2), b i : ℕ) : ℝ≥0) / 2 ^ 128 := by
  set W := univ.filter fun w : Fin (r * 2) → F => ¬ Doom (List.ofFn w)
  have h1 := flat_round_le (D := D) (L := L) hl W fun as has hE => by
    simp only [W, mem_filter, mem_univ, true_and]; exact hesc as has hE
  have h2 := seq_bad_le Doom b hb (r * 2) [] h0
  simp only [List.nil_append, List.length_nil, zero_add, F.card_F] at h2
  refine h1.trans ?_
  rw [div_le_div_iff₀ (by positivity) (by positivity)]
  have h3 : (W.card : ℝ≥0) * 2 ^ 128 ≤ (∑ i ∈ range (r * 2), b i : ℕ) * (2 ^ 128) ^ (r * 2) := by
    exact_mod_cast h2
  calc (W.card : ℝ≥0) * 2 ^ 128 ≤ _ := h3
    _ = _ := by rw [← pow_mul]; ring_nf

/-- A table with its first variables bound to `cs`, in order (`bind0` each). -/
def bindL {R : Type*} [CommRing R] (t : Array R) : List R → Array R
  | [] => t
  | c :: cs => bindL (bind0 t c) cs

theorem bindL_append {R : Type*} [CommRing R] (t : Array R) (cs : List R) (c : R) :
    bindL t (cs ++ [c]) = bind0 (bindL t cs) c := by
  induction cs generalizing t with
  | nil => rfl
  | cons c' cs ih => exact ih _

theorem bindL_size {R : Type*} [CommRing R] {n : ℕ} :
    ∀ (cs : List R) (t : Array R), t.size = 2 ^ (cs.length + n) → (bindL t cs).size = 2 ^ n
  | [], t, h => by rw [bindL]; simpa using h
  | c :: cs, t, h => bindL_size cs _ (by
      rw [bind0_size, h, List.length_cons, show cs.length + 1 + n = (cs.length + n) + 1 by omega,
        pow_succ, Nat.mul_div_cancel _ two_pos])

/-- **The multilinear zero test's doom** over a table of `n` variables: with the first coordinates
bound (at most `n`), the table is not zero. At `n` coordinates this is "the MLE of `t` at the
point is nonzero". -/
def mlDoom {R : Type*} [CommRing R] (n : ℕ) (t : Array R) (l : List R) : Prop :=
  tbl (n - (l.take n).length) (bindL t (l.take n)) ≠ 0

open Classical in
/-- Each coordinate loses at most one value (`zerocheck_bad_le`, `tbl_bind0`); past `n`, none. -/
theorem mlDoom_step {R : Type*} [Field R] [Fintype R] [DecidableEq R] {n : ℕ} {t : Array R}
    (ht : t.size = 2 ^ n) (l : List R) (hd : mlDoom n t l) :
    (univ.filter fun c => ¬ mlDoom n t (l ++ [c])).card ≤ if l.length < n then 1 else 0 := by
  by_cases hl : l.length < n
  · simp only [hl, ↓reduceIte]
    have hlk : l.take n = l := List.take_of_length_le (by omega)
    obtain ⟨m, hm⟩ : ∃ m, n - l.length = m + 1 := ⟨n - l.length - 1, by omega⟩
    have hsz : (bindL t l).size = 2 ^ (m + 1) := bindL_size l t (by rw [ht]; congr 1; omega)
    have hd' : tbl (m + 1) (bindL t l) ≠ 0 := by
      rw [mlDoom, hlk, hm] at hd; exact hd
    refine le_trans (card_le_card fun c hc => ?_) (zerocheck_bad_le _ hd')
    simp only [mem_filter, mem_univ, true_and, mlDoom, not_not] at hc ⊢
    rw [List.take_of_length_le (by simp; omega), bindL_append, List.length_append,
      List.length_singleton, show n - (l.length + 1) = m by omega, tbl_bind0 _ _ hsz] at hc
    exact hc
  · simp only [hl, ↓reduceIte, Nat.le_zero, Finset.card_eq_zero, filter_eq_empty_iff, mem_univ,
      true_implies, not_not]
    intro c
    rw [mlDoom, List.take_append_of_le_length (by omega)]
    exact hd

open Classical in
/-- **The multilinear row** (Z1, Lr1, E1, P3; A.10): if at the entry the table `t` of `n ≤ 2r`
variables is nonzero and every escape makes its MLE vanish at the phase's first `n`
coordinates, the phase's charge is at most `n / 2^128`. -/
theorem ml_round_le {D : Log → Log → Prop} {L es₀ : Log} {s0 r n : ℕ}
    (hl : es₀.length = s0 + 1) (hn : n ≤ r * 2) {t : Array F} (ht : t.size = 2 ^ n)
    (h0 : tbl n t ≠ 0)
    (hesc : ∀ as : List Digest, as.length = r → EscAtG D L (ext es₀ as) →
      ¬ mlDoom n t (List.ofFn fun j : Fin (r * 2) => coordAt (ext es₀ as) s0 j)) :
    condCount D L es₀ r [] ≤ (n : ℝ≥0) / 2 ^ 128 := by
  have h := seq_round_le hl (mlDoom n t) (fun i => if i < n then 1 else 0)
    (fun l hd => mlDoom_step ht l hd) (by cases n <;> exact h0) hesc
  refine h.trans (le_of_eq ?_)
  have : (∑ i ∈ range (r * 2), if i < n then 1 else 0) = n := by
    rw [Finset.sum_boole, show (range (r * 2)).filter (· < n) = range n by
      ext i; simp only [mem_filter, mem_range]; omega, card_range, Nat.cast_id]
  rw [this]

open Classical in
/-- **The ring-switching row** (RS1, 4 squeezes: `r″` = coordinates `0 … 6`, `κ` = coordinate
`7`): if the escape puts `(r″, κ)` in a set of at most `c·|F|^7` pairs (`rs1_joint`), the
phase's charge is at most `c / 2^128`. -/
theorem rs1_round_le {D : Log → Log → Prop} {L es₀ : Log} {s0 : ℕ} (hl : es₀.length = s0 + 1)
    (P : Finset ((Fin 7 → F) × F)) {c : ℕ} (hP : P.card ≤ c * Fintype.card F ^ 7)
    (hesc : ∀ as : List Digest, as.length = 4 → EscAtG D L (ext es₀ as) →
      ((fun i : Fin 7 => coordAt (ext es₀ as) s0 i), coordAt (ext es₀ as) s0 7) ∈ P) :
    condCount D L es₀ 4 [] ≤ (c : ℝ≥0) / 2 ^ 128 := by
  let pr : (Fin (4 * 2) → F) → (Fin 7 → F) × F := fun w => (Fin.init (n := 7) w, w (Fin.last 7))
  set W := univ.filter fun w : Fin (4 * 2) → F => pr w ∈ P
  have h1 := flat_round_le (D := D) (L := L) hl W fun as has hE => by
    simp only [W, mem_filter, mem_univ, true_and]; exact hesc as has hE
  have hinj : Set.InjOn pr W := fun w _ w' _ he => by
    have e1 := congrArg Prod.fst he; have e2 := congrArg Prod.snd he
    rw [← Fin.snoc_init_self (n := 7) w, ← Fin.snoc_init_self (n := 7) w']
    exact congrArg₂ (fun a b => Fin.snoc (α := fun _ => F) a b) e1 e2
  have h2 : W.card ≤ P.card := card_le_card_of_injOn pr (fun w hw => by
    simp only [W, coe_filter, mem_univ, true_and] at hw; exact hw) hinj
  rw [F.card_F] at hP
  refine h1.trans ?_
  rw [div_le_div_iff₀ (by positivity) (by positivity)]
  have h3 : (W.card : ℝ≥0) ≤ c * (2 ^ 128) ^ 7 := by exact_mod_cast h2.trans hP
  calc (W.card : ℝ≥0) * 2 ^ 128 ≤ c * (2 ^ 128) ^ 7 * 2 ^ 128 :=
        mul_le_mul_of_nonneg_right h3 (by positivity)
    _ = c * 2 ^ (256 * 4) := by
      rw [mul_assoc, ← pow_succ, ← pow_mul, show 128 * (7 + 1) = 256 * 4 by norm_num]

/-- A coordinate row of at most `239` bad values per `2^128` fits the rows' budget `deltaR`
(`εR − 2·2^-142 − 2^-238 ≈ 239.9998 / 2^128`). -/
theorem coord_le_deltaR {c : ℕ} (hc : c ≤ 239) : (c : ℝ≥0) / 2 ^ 128 ≤ deltaR := by
  rw [← NNReal.coe_le_coe, NNReal.coe_div, deltaR_coe]
  push_cast
  have : (c : ℝ) ≤ 239 := by exact_mod_cast hc
  rw [div_le_iff₀ (by positivity)]
  norm_num
  linarith

/-- **The Ligerito and PIOP coordinate rows fit `deltaR`** (A.10's counts: Z1 `≤ 20`, S1 `33`,
Lr1 `15`, RS1 `10`, E1 `21`, P3 `9`). -/
theorem coord_rows_le : ∀ c ∈ [20, 33, 15, 10, 21, 9], (c : ℝ≥0) / 2 ^ 128 ≤ deltaR :=
  fun c hc => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl | rfl | rfl | rfl | rfl <;> exact coord_le_deltaR (by norm_num)

/-- The phases with no Fiat–Shamir item (each level's `Q`). -/
def isQ (k : ℕ) : Bool := 29 ≤ k && k ≤ 49 && (k - 29) % 5 == 0

/-- **A multi-squeeze phase's doom** (A.10's `hround` rows): on a chain ending inside the phase
(before its last answer), the doom of the phase's entry `prev` there; at its last answer, `fin`. -/
def msD (prev fin : Log → Log → Prop) (s0 r : ℕ) (L es : Log) : Prop :=
  if es.length ≤ s0 + r then prev L (es.take (s0 + 1)) else fin L es

theorem ite_pos' {α : Sort*} {p : Prop} [Decidable p] (h : p) (a b : α) :
    (if p then a else b) = a := by simp [h]

theorem ite_neg' {α : Sort*} {p : Prop} [Decidable p] (h : ¬ p) (a b : α) :
    (if p then a else b) = b := by simp [h]

/-- A formal extension keeps its chain as a prefix. -/
theorem take_ext (es₀ : Log) : ∀ as : List Digest, (ext es₀ as).take es₀.length = es₀ := by
  intro as
  induction as using List.reverseRecOn with
  | nil => simp [ext_nil]
  | append_singleton as a ih =>
    rw [ext_append, ext1, List.take_append_of_le_length (by rw [length_ext]; omega), ih]

/-- **Two step laws add** (§10 changes 15: `μ = μ_doom + μ_Hide`): if `μ₁` and `μ₂` each satisfy
the contract's step law (with errors `ε₁`, `ε₂`) wherever they are below `1`, their sum satisfies
it with error `ε₁ + ε₂` wherever the sum is below `1`. -/
theorem step_add {μ₁ μ₂ : Log → ℝ≥0} {ε₁ ε₂ : ℝ≥0}
    (h₁ : ∀ L q, L.length < logCap → μ₁ L < 1 → q ∉ L.map Prod.fst →
      ∑ a : Digest, μ₁ (L ++ [(q, a)]) ≤ (μ₁ L + ε₁) * 2 ^ 256)
    (h₂ : ∀ L q, L.length < logCap → μ₂ L < 1 → q ∉ L.map Prod.fst →
      ∑ a : Digest, μ₂ (L ++ [(q, a)]) ≤ (μ₂ L + ε₂) * 2 ^ 256)
    (L : Log) (q : ByteArray) (hl : L.length < logCap) (hμ : μ₁ L + μ₂ L < 1)
    (hq : q ∉ L.map Prod.fst) :
    ∑ a : Digest, (μ₁ (L ++ [(q, a)]) + μ₂ (L ++ [(q, a)])) ≤
      (μ₁ L + μ₂ L + (ε₁ + ε₂)) * 2 ^ 256 := by
  rw [Finset.sum_add_distrib]
  have a₁ := h₁ L q hl (lt_of_le_of_lt le_self_add hμ) hq
  have a₂ := h₂ L q hl (lt_of_le_of_lt le_add_self hμ) hq
  calc _ ≤ (μ₁ L + ε₁) * 2 ^ 256 + (μ₂ L + ε₂) * 2 ^ 256 := add_le_add a₁ a₂
    _ = _ := by ring

section Rounds2

variable {R : Type*} [Field R]

variable (b wd : ℕ) (rd : ByteArray → ℕ → R) (ch : Digest → R)

/-- Round `l`'s coefficients `c₀, c₁, c₂`. -/
def g2At (es : Log) (l : ℕ) : Array R :=
  #[rd (msgAt es (b + 2 * l)) 0, rd (msgAt es (b + 2 * l)) wd, rd (msgAt es (b + 2 * l)) (2 * wd)]

/-- Round `l`'s challenge. -/
def rch2 (es : Log) (l : ℕ) : R := ch (ansAt es (b + 2 * l + 1))

/-- The first `l` challenges. -/
def rchs2 (es : Log) (l : ℕ) : List R := (List.range l).map (rch2 b ch es)

variable (c0 : Log → Log → R)

/-- The running claims: `c0`, then `g_l(r_l)`. -/
def clR2 (L es : Log) : ℕ → R
  | 0 => c0 L es
  | l + 1 => peval (g2At b wd rd es l) (rch2 b ch es l)

variable (nr : Kind → ℕ) (e : Expr) (T : Log → Log → Array (Array R))

/-- Round `l`'s asserted check, as `Rej` must guarantee it. -/
def Chk2 (L es : Log) (l : ℕ) : Prop :=
  peval (g2At b wd rd es l) 0 + peval (g2At b wd rd es l) 1 = clR2 b wd rd ch c0 L es l

variable {b wd rd ch c0 nr e T}

omit [Field R] in
theorem rchs2_congr {es es' : Log} {l : ℕ} (h : Agree es es' (b + 2 * l)) :
    rchs2 b ch es l = rchs2 b ch es' l := by
  unfold rchs2 rch2 ansAt
  refine List.map_congr_left fun j hj => ?_
  rw [h _ (by simp at hj; omega)]

theorem clR2_congr {L es es' : Log} (hc : c0 L es = c0 L es') :
    ∀ {l : ℕ}, Agree es es' (b + 2 * l) → clR2 b wd rd ch c0 L es l = clR2 b wd rd ch c0 L es' l
  | 0, _ => hc
  | l + 1, h => by
    simp only [clR2]
    simp only [g2At, rch2, ansAt, msgAt, h (b + 2 * l) (by omega), h (b + 2 * l + 1) (by omega)]

/-- The truth reads the entries before `b` only. -/
def TruthLocal2 (b : ℕ) (c0 : Log → Log → R) (T : Log → Log → Array (Array R)) : Prop :=
  ∀ L es es', Agree es es' b → T L es = T L es' ∧ c0 L es = c0 L es'

end Rounds2

/-- Control: inside the phase `msD` is the entry's doom, at the last answer `fin`. -/
theorem msD_inside_last (prev fin : Log → Log → Prop) (s0 r : ℕ) (L es : Log) :
    (es.length ≤ s0 + r → (msD prev fin s0 r L es ↔ prev L (es.take (s0 + 1)))) ∧
      (s0 + r < es.length → (msD prev fin s0 r L es ↔ fin L es)) :=
  ⟨fun h => by rw [msD, ite_pos' h], fun h => by rw [msD, ite_neg' (by omega)]⟩

/-- Control (positive): a nonzero table is doomed before any coordinate. -/
theorem mlDoom_nil {n : ℕ} {t : Array F} (h : tbl n t ≠ 0) : mlDoom n t [] := by
  cases n <;> exact h

/-- Control (negative): the zero table is never doomed. -/
theorem not_mlDoom_zero (n : ℕ) (l : List F) :
    ¬ mlDoom n (Array.replicate (2 ^ n) 0) l := by
  unfold mlDoom
  rw [not_not]
  funext u
  have hz : ∀ (cs : List F) (m : ℕ), cs.length ≤ m →
      bindL (Array.replicate (2 ^ m) (0 : F)) cs = Array.replicate (2 ^ (m - cs.length)) 0 := by
    intro cs
    induction cs with
    | nil => intro m _; simp [bindL]
    | cons c cs ih =>
      intro m hm
      obtain ⟨m', rfl⟩ : ∃ m', m = m' + 1 := ⟨m - 1, by simp at hm; omega⟩
      have : bind0 (Array.replicate (2 ^ (m' + 1)) (0 : F)) c = Array.replicate (2 ^ m') 0 := by
        apply Array.ext
        · simp [bind0_size, pow_succ]
        · intro j h1 h2; simp [bind0]
      rw [bindL, this, ih m' (by simp at hm; omega), List.length_cons,
        show m' + 1 - (cs.length + 1) = m' - cs.length by omega]
  rw [hz _ n (by simp)]
  simp only [tbl, Array.getD_eq_getD_getElem?, Array.getElem?_replicate, Pi.zero_apply]
  split <;> rfl

end FR.Snd
