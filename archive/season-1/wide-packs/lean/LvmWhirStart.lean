-- Ported from leanVM `formal/lean_vm/LeanVM/Protocol/Whir/Sound/Start.lean` (formal rev 40f877dc) as `LvmWhirStart` for
-- lvm (WP-7). leanVM's `WhirPre`/`levelPre_zero` are kept (on the opening's view of the commitments); new:
-- `WhirPreUd`, the starting relation on the history's commitments (root `c₀` of `n₀`), and `whirPre_of_ud`.
/-
  LeanVM.Protocol.Whir.Sound.Start

  WHIR's starting relation in terms of the commitment's candidates: if every candidate stack
  violates the opening's claim, every member of the level-0 Johnson list violates the running
  claim the verifier starts from, `A(0, 0)`.
-/
import LvmWhirLevelFinal
import LvmNovelBasis
import LvmDslProg
import LvmRS

-- ===== merged from `LvmWhirCandBase` (GOLF module merge: `LvmWhirCandBase.lean` is now a stub importing `LvmWhirStart`) =====
section
-- Ported from leanVM `formal/lean_vm/LeanVM/Protocol/EndToEnd/Candidates.lean` (formal rev 40f877dc) as
-- `LvmWhirCandBase` for lvm (WP-7), unchanged but for this header and the threshold's wording.
/-
  LeanVM.Protocol.EndToEnd.Candidates

  The stacks a level-0 commitment binds: those whose encoding agrees with the committed word on
  enough columns. The object the front phases' doom and WHIR's starting relation quantify over,
  and from which the knowledge extractor picks.
-/

/-!
# The candidates of a commitment

The deployed commitment (`verify_execution` step 2 and `verify_whir` level 0,
`crates/verifier/src/lib.rs:235-237` and `whir.rs:185-211` at leanVM `40f877dc`) is a Merkle
root of a word of `2^(μ − 6 + R)` columns, each a leaf of `64` words of `K`. The
leaf stores the lanes of its column in reverse order (`row.reverse`): lane `u` of column `v` is
word `63 − u` of leaf `v` (`laneOf`). Lane `u` of an honest word is the encoding (`enc`, the
novel-basis Reed-Solomon code) of the stack's block `u`: the `2^(μ−6)` consecutive cells at offset
`u · 2^(μ−6)`, so that the stack's coordinates are the message's `μ − 6` low bits and the lane's
six high bits (`blockOf`, Annex B "Optimizations", `f(u, x) = q(x, u)`).

`Agrees μ R W q S` says the encoding of the stack `q` agrees with the word `W` on every lane at
every column of `S`. `Candidates μ R A W` are the stacks whose encoding agrees with `W` on at
least `A` columns (lvm: `A = udThr`, the unique-decoding radius; leanVM: `A = ⌈(√ρ₋ + η)·n⌉`, the
stacks of the Johnson list at radius `1 − √ρ₋ − η`). The front phases' doom (no candidate is in their state function) and WHIR's
starting relation (every candidate violates a pooled claim) quantify over them; the knowledge
extractor returns the candidate satisfying the relation when there is one.

Candidates are `K`-valued stacks by type: a codeword of the `E`-code close to a `K`-valued word is
`K`-valued (WHIR's soundness proves the list members are the encodings of candidates).
-/

namespace LeanVM.Protocol.EndToEnd

open LeanVM.Parameters LeanVM.Protocol.Compile LeanVM.Protocol.Whir

section

/-- The number of lanes of the level-0 commitment: `2^6`. -/
abbrev laneBits : ℕ := 6

/-- Lane `u` of column `v` of a committed level-0 word, as an element of `E`: word `63 − u` of the
leaf (the leaf stores the lanes reversed; a missing word reads `0`). -/
def laneOf (W : Word) (u : Fin (2 ^ laneBits)) (v : ℕ) : E :=
  ofK ((W v).reverse.getD u 0)

/-- Block `u` of the stack: cell `x + 2^(μ−6)·u`, the message the lane `u` encodes, indexed by the
`μ − 6` low bits `x` (bit `0` first). -/
def blockOf {μ : ℕ} (q : Column μ) (u : Fin (2 ^ laneBits)) :
    (Fin (μ - laneBits) → Bool) → E :=
  fun x ↦ ofK (q.values.getD (bitsToNat x + 2 ^ (μ - laneBits) * u) 0)

/-- The encoding of the stack `q` agrees with the word `W` at every lane of every column of `S`. -/
def Agrees (μ R : ℕ) (W : Word) (q : Column μ) (S : Finset (Fin (2 ^ (μ - laneBits + R)))) :
    Prop :=
  ∀ v ∈ S, ∀ u, laneOf W u v = enc (μ - laneBits) R (blockOf q u) v

/-- The **candidates** of a committed word: the stacks whose encoding agrees with it on at least
`A` columns. -/
def Candidates (μ R A : ℕ) (W : Word) : Set (Column μ) :=
  {q | ∃ S, A ≤ S.card ∧ Agrees μ R W q S}

end
end LeanVM.Protocol.EndToEnd
end
-- ===== end of `LvmWhirCandBase` =====

-- ===== merged from `LvmWhirCandidates` (GOLF module merge: `LvmWhirCandidates.lean` is now a stub importing `LvmWhirStart`) =====
section
-- Ported from leanVM `formal/lean_vm/LeanVM/Protocol/Whir/Sound/Candidates.lean` (formal rev 40f877dc) as `LvmWhirCandidates` for lvm (WP-7).
/-
  LeanVM.Protocol.Whir.Sound.Candidates

  The level-0 list of a committed word and the candidates the commitment binds: every
  list member is the lane-wise encoding of a candidate stack, and every candidate's encoding is a
  list member.
-/

/-!
# The level-0 list and the candidates

The level-0 oracle of the deployed WHIR opening (`verify_whir` level `0`,
`crates/verifier/src/whir.rs:141-232` at leanVM `40f877dc`)
is the committed word read lane by lane: lane `u` of column `v` is `laneOf W u v`, word `63 − u`
of leaf `v` (the program's `row.reverse.map ofK`). Its code is the novel-basis Reed-Solomon code
`C₀ = RS[E, D_{μ−6,R}, 2^(μ−6)]` (`range_enc`), and its list at agreement threshold `A` is
`iList C₀ A (laneWord μ R W)`.

* `isInK_of_agree`: a codeword of the `E`-code whose entries lie in `K` on at least `2^κ`
  coordinates has a `K`-valued message. The message's limbs `1` and `2` encode `K`-codewords
  vanishing on those coordinates (Annex B's remark: "limbs 1, 2 are codewords agreeing with `0` on
  more than `2^κ − 1` points"), hence vanish.
* `exists_candidate_of_mem_iList`: **every list member is the encoding of a candidate**, for a
  threshold `A ≥ 2^(μ−6)` (every Johnson threshold is: `LevelCode.two_pow_le_thr`).
* `mem_iList_of_candidate`: conversely, the encoding of a candidate is a list member.
* `encStack_injective`: the encoding determines the stack, so list members and candidates are in
  bijection.

The candidates are `LeanVM.Protocol.EndToEnd.Candidates`: the stack's block `u` (cells
`x + 2^(μ−6)·u`) is the message of lane `u`, `f(u, x) = q(x, u)` of Annex B "Optimizations".
-/

namespace LeanVM.Protocol.Whir.Sound

open LeanVM.Parameters LeanVM.Protocol.Compile LeanVM.Protocol.Whir
  LeanVM.Protocol.EndToEnd

section

/-! ## The level-0 word and code -/

/-- The level-0 interleaved word of a committed word: lane `u` of column `v`. -/
def laneWord (μ R : ℕ) (W : Word) : Fin (2 ^ laneBits) → Fin (2 ^ (μ - laneBits + R)) → E :=
  fun u v ↦ laneOf W u v

/-- The lane-wise encoding of a stack: lane `u` encodes block `u`. -/
def encStack (μ R : ℕ) (q : Column μ) : Fin (2 ^ laneBits) → Fin (2 ^ (μ - laneBits + R)) → E :=
  fun u ↦ enc (μ - laneBits) R (blockOf q u)

/-- `Agrees` is agreement of the lane word with the stack's encoding. -/
theorem agrees_iff_agreeOn (μ R : ℕ) (W : Word) (q : Column μ)
    (S : Finset (Fin (2 ^ (μ - laneBits + R)))) :
    Agrees μ R W q S ↔ AgreeOn (laneWord μ R W) (encStack μ R q) S :=
  ⟨fun h u v hv ↦ h v hv u, fun h v hv u ↦ h u v hv⟩

/-! ## `K`-valuedness -/

section Limbs

variable {κ R : ℕ}

/-- The limb `i` of a message, as a `K`-valued message. -/
def msgLimb (g : (Fin κ → Bool) → E) (i : Fin 3) : (Fin κ → Bool) → K := fun u ↦ (g u).limb i

/-- A message is the sum of its limbs in the basis `1, y, y²`. -/
theorem msg_eq_limbs (g : (Fin κ → Bool) → E) :
    g = (fun u ↦ ofK (msgLimb g 0 u)) + y • (fun u ↦ ofK (msgLimb g 1 u)) +
      (y ^ 2) • (fun u ↦ ofK (msgLimb g 2 u)) := by
  funext u
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, msgLimb]
  conv_lhs => rw [E.eq_sum_limbs (g u)]
  ring

/-- The encoding of a message, limb by limb: limb `i` of a codeword entry is the `K`-encoding of
limb `i` of the message. -/
theorem enc_eq_ofLimbs (g : (Fin κ → Bool) → E) (v : Fin (2 ^ (κ + R))) :
    enc κ R g v = E.ofLimbs (encK κ R (msgLimb g 0) v) (encK κ R (msgLimb g 1) v)
      (encK κ R (msgLimb g 2) v) := by
  conv_lhs => rw [msg_eq_limbs g]
  rw [map_add, map_add, map_smul, map_smul, enc_ofK, enc_ofK, enc_ofK, ofLimbs_eq]
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  ring

/-- Limb `i` of a codeword entry is the `K`-encoding of limb `i` of the message. -/
theorem limb_enc (g : (Fin κ → Bool) → E) (v : Fin (2 ^ (κ + R))) (i : Fin 3) :
    (enc κ R g v).limb i = encK κ R (msgLimb g i) v := by
  rw [enc_eq_ofLimbs, limb_ofLimbs]
  fin_cases i <;> rfl

/-- A `K`-message whose encoding vanishes on `2^κ` coordinates is zero. -/
theorem eq_zero_of_encK_vanish (h : κ + R ≤ 64) (a : (Fin κ → Bool) → K)
    (S : Finset (Fin (2 ^ (κ + R)))) (hS : 2 ^ κ ≤ S.card) (hv : ∀ v ∈ S, encK κ R a v = 0) :
    a = 0 := by
  have hmem : enc κ R (fun u ↦ ofK (a u)) ∈ rsCode (domain κ R h) (2 ^ κ) := by
    rw [← range_enc h]; exact LinearMap.mem_range_self _ _
  have h0 : enc κ R (fun u ↦ ofK (a u)) = 0 :=
    eq_of_mem_code_of_agreeOn (domain κ R h) hmem (Submodule.zero_mem _) S hS fun v hvS ↦ by
      rw [enc_ofK]; simp [hv v hvS]
  have h1 : (fun u ↦ ofK (a u)) = 0 := enc_injective h (h0.trans (map_zero _).symm)
  funext u
  exact ofK_injective ((congrFun h1 u).trans (by simp))

/-- **`K`-valuedness.** If the encoding of a message lies in `K` on at least `2^κ` coordinates,
every entry of the message lies in `K`. -/
theorem isInK_of_agree (h : κ + R ≤ 64) (g : (Fin κ → Bool) → E)
    (S : Finset (Fin (2 ^ (κ + R)))) (hS : 2 ^ κ ≤ S.card) (hK : ∀ v ∈ S, IsInK (enc κ R g v)) :
    ∀ u, IsInK (g u) := by
  have h1 := eq_zero_of_encK_vanish h (msgLimb g 1) S hS fun v hv ↦ by
    rw [← limb_enc]; exact (hK v hv).1
  have h2 := eq_zero_of_encK_vanish h (msgLimb g 2) S hS fun v hv ↦ by
    rw [← limb_enc]; exact (hK v hv).2
  exact fun u ↦ ⟨congrFun h1 u, congrFun h2 u⟩

end Limbs

/-! ## Stacks from lane messages -/

section Stack

variable {μ : ℕ}

/-- The stack whose block `u` is the `K`-message `a u`: cell `i` is `a (i / 2^κ) (i % 2^κ)`. -/
def stackOf (hμ : laneBits ≤ μ) (a : Fin (2 ^ laneBits) → (Fin (μ - laneBits) → Bool) → K) :
    Column μ :=
  ⟨Vector.ofFn fun i : Fin (2 ^ μ) ↦
    a ⟨i / 2 ^ (μ - laneBits), by
      have hi := i.isLt
      rw [Nat.div_lt_iff_lt_mul (Nat.two_pow_pos _), ← pow_add]
      rwa [Nat.add_sub_cancel' hμ]⟩
      ((bitsEquiv (μ - laneBits)).symm ⟨i % 2 ^ (μ - laneBits), Nat.mod_lt _ (Nat.two_pow_pos _)⟩)⟩

/-- Block `u` of `stackOf a` is `a u`. -/
theorem blockOf_stackOf (hμ : laneBits ≤ μ)
    (a : Fin (2 ^ laneBits) → (Fin (μ - laneBits) → Bool) → K) (u : Fin (2 ^ laneBits)) :
    blockOf (stackOf hμ a) u = fun x ↦ ofK (a u x) := by
  funext x
  have hx := bitsToNat_lt x
  have hlt : bitsToNat x + 2 ^ (μ - laneBits) * u < 2 ^ μ := by
    have hu := u.isLt
    calc bitsToNat x + 2 ^ (μ - laneBits) * u < 2 ^ (μ - laneBits) * (u + 1) := by nlinarith
      _ ≤ 2 ^ (μ - laneBits) * 2 ^ laneBits := Nat.mul_le_mul_left _ hu
      _ = 2 ^ μ := by rw [← pow_add, Nat.sub_add_cancel hμ]
  simp only [EndToEnd.blockOf, stackOf, Vector.getD, Vector.toArray_ofFn, Array.getD_eq_getD_getElem?,
    Array.getElem?_ofFn, hlt, dite_true, Option.getD_some]
  congr 2
  · apply Fin.ext
    simp only
    rw [Nat.add_mul_div_left _ _ (Nat.two_pow_pos _), Nat.div_eq_of_lt hx, zero_add]
  · apply (bitsEquiv (μ - laneBits)).injective
    rw [Equiv.apply_symm_apply]
    apply Fin.ext
    simp only [bitsEquiv_val]
    rw [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hx]

/-- The blocks determine the stack. -/
theorem eq_of_blockOf_eq (hμ : laneBits ≤ μ) {q q' : Column μ}
    (h : ∀ u, blockOf q u = blockOf q' u) : q = q' := by
  obtain ⟨v⟩ := q
  obtain ⟨v'⟩ := q'
  congr 1
  apply Vector.ext
  intro i hi
  -- Cell `i` is cell `x + 2^κ u` of block `u = i / 2^κ`, `x = i % 2^κ`.
  have hu : i / 2 ^ (μ - laneBits) < 2 ^ laneBits := by
    rw [Nat.div_lt_iff_lt_mul (Nat.two_pow_pos _), ← pow_add, Nat.add_sub_cancel' hμ]
    exact hi
  have hx : bitsToNat ((bitsEquiv (μ - laneBits)).symm
      ⟨i % 2 ^ (μ - laneBits), Nat.mod_lt _ (Nat.two_pow_pos _)⟩) = i % 2 ^ (μ - laneBits) := by
    rw [← bitsEquiv_val, Equiv.apply_symm_apply]
  have := congrFun (h ⟨i / 2 ^ (μ - laneBits), hu⟩) ((bitsEquiv (μ - laneBits)).symm
      ⟨i % 2 ^ (μ - laneBits), Nat.mod_lt _ (Nat.two_pow_pos _)⟩)
  simp only [EndToEnd.blockOf, hx, Nat.mod_add_div] at this
  have := ofK_injective this
  simpa [Vector.getD, hi] using this

end Stack

/-! ## The bridge -/

variable {μ R A : ℕ}

/-- The encoding of a stack determines the stack. -/
theorem encStack_injective (hμ : laneBits ≤ μ) (h : μ - laneBits + R ≤ 64) :
    Function.Injective (encStack μ R) := fun _ _ hqq ↦
  eq_of_blockOf_eq hμ fun u ↦ enc_injective h (congrFun hqq u)

/-- The encoding of a stack is an interleaved codeword of the level-0 code. -/
theorem isInterleavedCodeword_encStack (h : μ - laneBits + R ≤ 64) (q : Column μ) :
    IsInterleavedCodeword (rsCode (domain (μ - laneBits) R h) (2 ^ (μ - laneBits)))
      (encStack μ R q) := fun u ↦ by
  rw [← range_enc h]; exact LinearMap.mem_range_self _ _

/-- **Every level-0 list member is the encoding of a candidate.** An interleaved codeword of the
level-0 code agreeing with the lane word of `W` on at least `A ≥ 2^(μ−6)` columns is
`encStack q` for a candidate `q` of `W`. -/
theorem exists_candidate_of_mem_iList (hμ : laneBits ≤ μ) (h : μ - laneBits + R ≤ 64)
    (hA : 2 ^ (μ - laneBits) ≤ A) {W : Word}
    {U : Fin (2 ^ laneBits) → Fin (2 ^ (μ - laneBits + R)) → E}
    (hU : U ∈ iList (rsCode (domain (μ - laneBits) R h) (2 ^ (μ - laneBits))) A
      (laneWord μ R W)) :
    ∃ q ∈ Candidates μ R A W, U = encStack μ R q := by
  rw [mem_iList] at hU
  obtain ⟨hcw, S, hS, hagree⟩ := hU
  -- Every row is the encoding of a message.
  have hmsg : ∀ u, ∃ g, enc (μ - laneBits) R g = U u := fun u ↦ by
    have := hcw u
    rw [← range_enc h] at this
    exact this
  choose g hg using hmsg
  -- The messages are `K`-valued.
  have hK : ∀ u x, IsInK (g u x) := fun u ↦
    isInK_of_agree h (g u) S (hA.trans hS) fun v hv ↦ by
      rw [hg u, ← hagree u v hv, isInK_iff]
      exact ⟨_, rfl⟩
  let a : Fin (2 ^ laneBits) → (Fin (μ - laneBits) → Bool) → K := fun u x ↦ (g u x).limb 0
  have hga : ∀ u, g u = fun x ↦ ofK (a u x) := fun u ↦ funext fun x ↦ by
    obtain ⟨c, hc⟩ := (isInK_iff _).mp (hK u x)
    simp [a, hc]
  refine ⟨stackOf hμ a, ⟨S, hS, (agrees_iff_agreeOn _ _ _ _ _).mpr ?_⟩, ?_⟩
  · intro u v hv
    rw [hagree u v hv, encStack, blockOf_stackOf, ← hga, hg]
  · funext u
    rw [encStack, blockOf_stackOf, ← hga, hg]

/-- **The encoding of a candidate is a level-0 list member.** -/
theorem mem_iList_of_candidate (h : μ - laneBits + R ≤ 64) {W : Word} {q : Column μ}
    (hq : q ∈ Candidates μ R A W) :
    encStack μ R q ∈ iList (rsCode (domain (μ - laneBits) R h) (2 ^ (μ - laneBits))) A
      (laneWord μ R W) := by
  obtain ⟨S, hS, hagree⟩ := hq
  rw [mem_iList]
  exact ⟨isInterleavedCodeword_encStack h q, S, hS, (agrees_iff_agreeOn _ _ _ _ _).mp hagree⟩

end
end LeanVM.Protocol.Whir.Sound
end
-- ===== end of `LvmWhirCandidates` =====

/-!
# The starting relation

The opening's input (`verify_whir(log_n, log_inv_rate, target, root, evaluate_basis)`,
`crates/verifier/src/whir.rs:141-149` at leanVM `40f877dc`) is the
level-0 commitment `W₀`, a weight function `w` (the batched `evaluate_basis`, a function of a point
of the stack's cube, bit `0` first) and a target `t`. Its relation, in the terms of
`LeanVM.Protocol.EndToEnd.Candidates`: **every candidate `q` of `W₀` at the Johnson threshold
violates the claim**, `¬ StackClaim.Holds μ (w, t) q`, i.e. `Σ_j w(j) q_j ≠ t`. lvm's openings
read the root `c₀` among the `n₀` commitments present at their start (`WhirPreUd`), which the
proofs see through the opening's view (`viewC`, `whirPre_of_ud`).

The verifier's sumcheck runs in the order (lanes, message bits): the first `ℓ₀ = 6` variables are
the lanes, which are the stack's six high bits, and its weight at a point `p` is
`w(p[6:] ++ p[:6])` (`runW` of the initial state, the terminal check's rotated point).

* `rowsOf_laneO_zero`: the level-0 lane oracle is the candidates' lane word (`laneWord`, leaf
  words reversed) with lanes indexed by their bits.
* `claimSum_encStack`: the running claim of the encoding of a stack `q` is `Σ_j w(j) q_j`: the
  rotation exactly undoes the stack/lane relayout `f(u, x) = q(x, u)`.
* `levelPre_zero`: **the starting doom** `LevelPre` of level `0` from the candidates' violation,
  through the bridge `exists_candidate_of_mem_iList` (a list member is the encoding of a
  candidate: `K`-valuedness and injectivity of the encoder).
-/

namespace LeanVM.Protocol.Whir.Sound

open LeanVM.Parameters LeanVM.Protocol.Compile LeanVM.Protocol.Verifier
  LeanVM.Protocol.Whir LeanVM.Protocol.EndToEnd Finset

section

/-! ## Reindexing -/

/-- Lists are invariant under reindexing the rows. -/
theorem mem_iList_comp {F ι ρ ρ' : Type*} [Field F] [Fintype F] [Fintype ι] [Fintype ρ]
    [Fintype ρ'] (C : Submodule F (ι → F)) (A : ℕ) (e : ρ' ≃ ρ) (O V : ρ' → ι → F) :
    V ∈ iList C A O ↔ (fun r ↦ V (e.symm r)) ∈ iList C A (fun r ↦ O (e.symm r)) := by
  simp only [mem_iList, IsInterleavedCodeword, IsClose, AgreeOn]
  constructor
  · rintro ⟨hc, S, hS, hag⟩
    exact ⟨fun r ↦ hc _, S, hS, fun r x hx ↦ hag _ x hx⟩
  · rintro ⟨hc, S, hS, hag⟩
    refine ⟨fun r ↦ by simpa using hc (e r), S, hS, fun r x hx ↦ by simpa using hag (e r) x hx⟩

theorem bitsToNat_append {m n : ℕ} (x : Fin m → Bool) (u : Fin n → Bool) :
    bitsToNat (Fin.append x u) = bitsToNat x + 2 ^ m * bitsToNat u := by
  simp only [bitsToNat, Fin.sum_univ_add, Fin.append_left, Fin.append_right, Fin.val_castAdd,
    Fin.val_natAdd, pow_add, Finset.mul_sum]
  congr 1
  exact Finset.sum_congr rfl fun i _ ↦ by ring

theorem boolPoint_bitsToNat {n : ℕ} (p : Fin n → Bool) : boolPoint n (bitsToNat p) = bitsL p := by
  refine List.ext_getElem (by simp [boolPoint]) fun i h₁ h₂ ↦ ?_
  simp only [boolPoint, List.getElem_map, List.getElem_range, bitsL, List.getElem_ofFn, bitE]
  have := testBit_bitsToNat p ⟨i, by simpa [boolPoint] using h₁⟩
  simp only at this
  rw [this]

/-- A sum over `2^(κ+m)` indices is a sum over the low `κ` and the high `m` bits. -/
theorem sum_split (κ m : ℕ) (f : ℕ → E) :
    ∑ j : Fin (2 ^ (κ + m)), f j =
      ∑ u : Fin m → Bool, ∑ x : Fin κ → Bool, f (bitsToNat x + 2 ^ κ * bitsToNat u) := by
  rw [← Equiv.sum_comp (bitsEquiv (κ + m)), ← (splitEquiv κ m).sum_comp, Fintype.sum_prod_type,
    Finset.sum_comm]
  refine Finset.sum_congr rfl fun u _ ↦ Finset.sum_congr rfl fun x _ ↦ ?_
  simp [bitsEquiv_val, splitEquiv, bitsToNat_append]

/-! ## The level-0 oracle -/

theorem getD_map_ofK (l : List K) (j : ℕ) : (l.map ofK).getD j 0 = ofK (l.getD j 0) := by
  simp only [List.getD_eq_getElem?_getD, List.getElem?_map]
  cases l[j]? <;> simp

/-- **The level-0 lane oracle** is the candidates' lane word. -/
theorem rowsOf_laneO_zero (μ R : ℕ) (cs : List (ℕ × ℕ × Word)) :
    rowsOf laneBits (laneO 0 cs (2 ^ (μ - laneBits + R))) =
      fun u ↦ laneWord μ R (wordOf cs 0) (bitsEquiv laneBits u) := by
  funext u v
  simp only [rowsOf, laneO, lanesOf, ↓reduceIte]
  rw [getD_map_ofK]
  simp [laneWord, laneOf, bitsEquiv_val]

/-- **The running claim of a stack's encoding** is the stack claim: the verifier's rotated
weight undoes the relayout `f(u, x) = q(x, u)`. -/
theorem claimSum_encStack {μ : ℕ} (hμ : laneBits ≤ μ) (w : List E → E) (q : Column μ) :
    claimSum (fun r ↦ w (rotL laneBits r)) (fun u ↦ blockOf q (bitsEquiv laneBits u)) =
      ∑ j : Fin (2 ^ μ), w (boolPoint μ j) * ofK (q.values.getD j 0) := by
  obtain ⟨κ, rfl⟩ : ∃ κ, μ = κ + laneBits := ⟨μ - laneBits, by omega⟩
  rw [sum_split κ laneBits (fun j ↦ w (boolPoint (κ + laneBits) j) * ofK (q.values.getD j 0)),
    claimSum]
  refine Finset.sum_congr rfl fun u _ ↦ Finset.sum_congr rfl fun x _ ↦ ?_
  have hrot : rotL laneBits (bitsL u ++ bitsL x) = bitsL x ++ bitsL u := by
    simp [rotL, List.drop_left' (length_bitsL u), List.take_left' (length_bitsL u)]
  rw [hrot, ← bitsL_append, ← boolPoint_bitsToNat, bitsToNat_append]
  simp [EndToEnd.blockOf, bitsEquiv_val]

/-! ## The starting doom -/

/-- WHIR's starting relation: the level-0 commitment has the right shape and every candidate of
its word violates the claim `(w, t)`. -/
def WhirPre (μ R : ℕ) (P₀ : LevelCode) (w : List E → E) (t : E) (cs : List (ℕ × ℕ × Word)) :
    Prop :=
  ShapeOK 0 P₀ laneBits cs ∧
    ∀ q ∈ Candidates μ R P₀.thr (wordOf cs 0), ¬ StackClaim.Holds μ (w, t) q

/-- **The starting doom**: from the candidates' violation and the first round polynomial,
`LevelPre` of level `0` for the initial state. -/
theorem levelPre_zero {μ R : ℕ} (P₀ : LevelCode) (hκ : P₀.κ = μ - laneBits) (hR : P₀.R = R)
    (hμ : laneBits ≤ μ) (w : List E → E) (t : E) (quad : List E) (cs : List (ℕ × ℕ × Word))
    (hpre : WhirPre μ R P₀ w t cs) (hq : QuadOK quad t) :
    LevelPre μ laneBits w 0 P₀ laneBits 0 ⟨t, quad, [], []⟩ cs := by
  refine ⟨⟨by simp, by simp, by omega, by simp [GluedOK], hq, ?_⟩, hpre.1⟩
  obtain ⟨-, hcand⟩ := hpre
  rcases P₀ with ⟨κ, R', h64, hκ1, hR1, thr, lM, mM, facts⟩
  simp only at hκ hR
  subst hκ hR
  intro V hV
  simp only [List.length_nil, Nat.sub_zero, foldsN, List.foldl_nil] at hV
  have hV' : V ∈ iList (rsCode (domain (μ - laneBits) R' h64) (2 ^ (μ - laneBits)))
      (LevelCode.thr ⟨μ - laneBits, R', h64, hκ1, hR1, thr, lM, mM, facts⟩)
      (rowsOf laneBits (laneO 0 cs (2 ^ (μ - laneBits + R')))) := hV
  rw [rowsOf_laneO_zero, mem_iList_comp _ _ (bitsEquiv laneBits)] at hV'
  clear hV
  have hV := hV'
  simp only [Equiv.apply_symm_apply] at hV
  obtain ⟨q, hqc, hVq⟩ := exists_candidate_of_mem_iList hμ h64
    (LevelCode.two_pow_le_thr ⟨μ - laneBits, R', h64, hκ1, hR1, thr, lM, mM, facts⟩) hV
  have hVe : V = fun u ↦ enc (μ - laneBits) R' (blockOf q (bitsEquiv laneBits u)) := by
    funext u
    have := congrFun hVq (bitsEquiv laneBits u)
    simpa [encStack] using this
  have hdec : decode ⟨μ - laneBits, R', h64, hκ1, hR1, thr, lM, mM, facts⟩ V =
      fun u ↦ blockOf q (bitsEquiv laneBits u) := by
    rw [hVe]
    exact decode_enc ⟨μ - laneBits, R', h64, hκ1, hR1, thr, lM, mM, facts⟩ _
  have hrun : runW w laneBits ⟨t, quad, [], []⟩ = fun r ↦ w (rotL laneBits r) := by
    funext r
    simp [runW]
  rw [hdec, hrun, claimSum_encStack hμ]
  exact hcand q hqc

/-! ## lvm's starting relation on the history -/

/-- The view at the start of an opening is its root alone. -/
theorem viewC_start {c₀ n₀ : ℕ} {cs : List (ℕ × ℕ × Word)} (hc : c₀ < n₀)
    (hlen : cs.length = n₀) : viewC c₀ n₀ cs = [cs[c₀]'(by omega)] := by
  have hle : n₀ ≤ cs.length := hlen.ge
  have hlt : c₀ < (cs.take n₀).length := by simp; omega
  simp only [viewC, hle, ↓reduceIte, List.drop_eq_nil_of_le hlen.le, List.getElem?_eq_getElem hlt,
    Option.getD_some, List.getElem_take]

/-- **lvm's starting relation of an opening**: the history has the `n₀` commitments the opening
starts with, its root `c₀` has the shape of the first level (`2^(κ₀+R₀)` leaves of `2^6` words of
`K`), and every candidate of the root's word violates the claim `(w, t)`. -/
def WhirPreUd (cfg : UdConfig) (P₀ : LevelCode) (w : List E → E) (t : E)
    (cs : List (ℕ × ℕ × Word)) : Prop :=
  cfg.c₀ < cfg.n₀ ∧ cs.length = cfg.n₀ ∧
    (∃ W, cs[cfg.c₀]? = some (P₀.κ + P₀.R, 2 ^ laneBits, W) ∧ WellShaped (2 ^ laneBits) W) ∧
    ∀ q ∈ Candidates cfg.μ P₀.R P₀.thr (wordOf cs cfg.c₀), ¬ StackClaim.Holds cfg.μ (w, t) q

/-- The root's shape at the start, through the view. -/
theorem shapeOK_viewC_start {cfg : UdConfig} {P₀ : LevelCode} {cs : List (ℕ × ℕ × Word)}
    (hc : cfg.c₀ < cfg.n₀) (hlen : cs.length = cfg.n₀)
    (hW : ∃ W, cs[cfg.c₀]? = some (P₀.κ + P₀.R, 2 ^ laneBits, W) ∧ WellShaped (2 ^ laneBits) W) :
    ShapeOK 0 P₀ laneBits (viewC cfg.c₀ cfg.n₀ cs) ∧
      wordOf (viewC cfg.c₀ cfg.n₀ cs) 0 = wordOf cs cfg.c₀ := by
  obtain ⟨W, hcW, hws⟩ := hW
  have hlt : cfg.c₀ < cs.length := by omega
  have he : cs[cfg.c₀] = (P₀.κ + P₀.R, 2 ^ laneBits, W) := by
    rw [List.getElem?_eq_getElem hlt] at hcW; exact Option.some.inj hcW
  rw [viewC_start hc hlen]
  refine ⟨⟨by simp, W, by simp [he, wdOf], by simpa [wdOf] using hws⟩, ?_⟩
  simp [wordOf, he, hcW]

/-- lvm's starting relation is leanVM's on the opening's view. -/
theorem whirPre_of_ud {cfg : UdConfig} {P₀ : LevelCode} {w : List E → E} {t : E}
    {cs : List (ℕ × ℕ × Word)} (h : WhirPreUd cfg P₀ w t cs) :
    WhirPre cfg.μ P₀.R P₀ w t (viewC cfg.c₀ cfg.n₀ cs) := by
  obtain ⟨hc, hlen, hW, hcand⟩ := h
  obtain ⟨hsh, hwo⟩ := shapeOK_viewC_start hc hlen hW
  exact ⟨hsh, by rw [hwo]; exact hcand⟩

end
end LeanVM.Protocol.Whir.Sound
