-- G6: this module also holds the former modules `FRXDecodeB`, `FRXBflyDefs` (one section each, in import order).
import FRSoundnessCoreTruths
import FRXRead

section G6_FRXDecodeB

-- New for `flock-recursive` (BLUEPRINT §6.2 step 4, §6.5 `coeffs_spec`; stage S-H2, track L-ext).

/-!
# The butterfly inverse NTT, iterative (phase 5, pure half)

S-D2's `coeffsAt` (`FRRSEval`) is the inverse additive NTT written top-down: the coefficients
on a coset of `2^(ℓ+1)` points are merged from those of its two halves. A machine runs it
bottom-up, in place: level `l = 0, 1, …` merges adjacent blocks of `2^l` into blocks of
`2^(l+1)`, `O(ℓ · 2^ℓ)` butterflies in all. This module defines that iteration on an array
(`bflyLevel`, `bflyRun`) and proves it equal to `coeffsAt` (`bflyRun_block`, `bflyRun_eq`), hence
to `coeffsOfValues` and, through `decode_row_D`, to the message of a codeword on `2^ℓ` agreeing
positions (`bfly_decode_D`). The machine program and its simulation are the next step.

The array is indexed from `0`; block `b` of level `l` covers `[b·2^l, (b+1)·2^l)` and holds the
coefficients on the coset at `s₀ + b·2^l` (`s₀` the array's domain offset).
-/

namespace FR.X

open FR Finset

section Bfly

variable {L : Type*} [Field L] {M : Type*} [Field M] [Algebra L M]

/-- **One butterfly level** `l`: in each block of `2^(l+1)` at `base`, the halves' coefficients
`u` (low) and `w` (high) merge into `u − α (w − u)` (low) and `w − u` (high), with
`α = Ŵ_l(pt (s₀ + base))` (`coeffsAt`'s step). -/
def bflyLevel (pt : ℕ → L) (N s0 l : ℕ) (A : ℕ → M) (i : ℕ) : M :=
  let base := i / 2 ^ (l + 1) * 2 ^ (l + 1)
  let x := i % 2 ^ (l + 1)
  let u := A (base + x % 2 ^ l)
  let w := A (base + 2 ^ l + x % 2 ^ l)
  let α := algebraMap L M (wAt pt N l (s0 + base))
  if x < 2 ^ l then u - α * (w - u) else w - u

/-- **The iteration**: levels `0, …, ℓ − 1`. -/
def bflyRun (pt : ℕ → L) (N s0 : ℕ) : ℕ → (ℕ → M) → ℕ → M
  | 0, A => A
  | l + 1, A => bflyLevel pt N s0 l (bflyRun pt N s0 l A)

/-- **The block invariant**: after `l` levels, block `b` holds `coeffsAt` of its coset. -/
theorem bflyRun_block (pt : ℕ → L) (N s0 : ℕ) (y : ℕ → M) :
    ∀ l b x, x < 2 ^ l → bflyRun pt N s0 l y (b * 2 ^ l + x) =
      coeffsAt pt N l (s0 + b * 2 ^ l) (fun j => y (b * 2 ^ l + j)) x := by
  intro l
  induction l with
  | zero =>
    intro b x hx
    obtain rfl : x = 0 := by simpa using hx
    simp [bflyRun, coeffsAt]
  | succ l ih =>
    intro b x hx
    have hp : 2 ^ (l + 1) = 2 * 2 ^ l := by rw [pow_succ]; ring
    have hpos : 0 < 2 ^ l := by positivity
    have hdiv : (b * 2 ^ (l + 1) + x) / 2 ^ (l + 1) = b := by
      rw [Nat.add_comm, Nat.add_mul_div_right _ _ (by positivity), Nat.div_eq_of_lt hx,
        Nat.zero_add]
    have hmod : (b * 2 ^ (l + 1) + x) % 2 ^ (l + 1) = x := by
      rw [Nat.add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hx]
    have hu := ih (2 * b) (x % 2 ^ l) (Nat.mod_lt _ hpos)
    have hw := ih (2 * b + 1) (x % 2 ^ l) (Nat.mod_lt _ hpos)
    have e1 : 2 * b * 2 ^ l = b * 2 ^ (l + 1) := by rw [hp]; ring
    have e2 : (2 * b + 1) * 2 ^ l = b * 2 ^ (l + 1) + 2 ^ l := by rw [hp]; ring
    rw [e1] at hu
    rw [e2] at hw
    simp only [bflyRun, bflyLevel, hdiv, hmod, coeffsAt]
    rw [hu, hw]
    have hY : (fun j => y (b * 2 ^ (l + 1) + 2 ^ l + j)) =
        fun j => (fun j => y (b * 2 ^ (l + 1) + j)) (2 ^ l + j) := by
      funext j; rw [Nat.add_assoc]
    rw [hY, ← Nat.add_assoc]
    by_cases hx' : x < 2 ^ l
    · rw [if_pos hx', if_pos hx', Nat.mod_eq_of_lt hx']
    · rw [if_neg hx', if_neg hx', show x % 2 ^ l = x - 2 ^ l by
        rw [Nat.mod_eq_sub_mod (by omega), Nat.mod_eq_of_lt (by omega)]]

/-- **The iteration is `coeffsAt`** on the array's first `2^ℓ` entries. -/
theorem bflyRun_eq (pt : ℕ → L) (N s0 ℓ : ℕ) (y : ℕ → M) {i : ℕ} (hi : i < 2 ^ ℓ) :
    bflyRun pt N s0 ℓ y i = coeffsAt pt N ℓ s0 y i := by
  simpa using bflyRun_block pt N s0 y ℓ 0 i hi

/-- From offset `0`, the iteration is `coeffsOfValues`. -/
theorem bflyRun_coeffs (pt : ℕ → L) (N ℓ : ℕ) (y : ℕ → M) (i : Fin (2 ^ ℓ)) :
    bflyRun pt N 0 ℓ y i = coeffsOfValues pt N ℓ y i :=
  bflyRun_eq pt N 0 ℓ y i.2

end Bfly

/-- **The extractor's row decoding, iterative** (`decode_row_D`): if the word `u` agrees with
`Enc(c)` on a set `J` of `2^ℓ` positions below `2^20`, the butterflies run on the values that
`interpF` gives at `D[0, 2^ℓ)` return the message `c`. -/
theorem bfly_decode_D {M : Type*} [Field M] [Algebra F M] {ℓ : ℕ} (hℓ : ℓ ≤ logNMax)
    {J : Finset ℕ} (hJN : ∀ i ∈ J, i < nMax) (hJc : J.card = 2 ^ ℓ) (c : Fin (2 ^ ℓ) → M)
    (u : ℕ → M) (hu : ∀ i ∈ J, u i = encN D c i) (i : Fin (2 ^ ℓ)) :
    bflyRun D logNMax 0 ℓ (interpF D J u) i = c i := by
  rw [bflyRun_coeffs, ← decode_row_D hℓ hJN hJc c u hu]
  rfl

/-! ## The agreement set's first `k` positions (§6.2 step 4: `P = A[0…k)`) -/

/-- **The first `k` positions of `A` below `n`**, in increasing order: the scan a machine makes
over the positions `0, …, n − 1`. -/
def firstK (n : ℕ) (A : Finset ℕ) (k : ℕ) : Finset ℕ :=
  (((List.range n).filter (· ∈ A)).take k).toFinset

theorem firstK_subset (n : ℕ) (A : Finset ℕ) (k : ℕ) : firstK n A k ⊆ A := fun i hi => by
  rw [firstK, List.mem_toFinset] at hi
  simpa using (List.mem_filter.1 (List.mem_of_mem_take hi)).2

theorem firstK_lt (n : ℕ) (A : Finset ℕ) (k : ℕ) : ∀ i ∈ firstK n A k, i < n := fun i hi => by
  rw [firstK, List.mem_toFinset] at hi
  exact List.mem_range.1 (List.mem_filter.1 (List.mem_of_mem_take hi)).1

theorem firstK_card {n : ℕ} {A : Finset ℕ} (hA : ∀ i ∈ A, i < n) {k : ℕ} (hk : k ≤ A.card) :
    (firstK n A k).card = k := by
  have hnd : ((List.range n).filter (· ∈ A)).Nodup := (List.nodup_range).filter _
  have hlen : ((List.range n).filter (· ∈ A)).length = A.card := by
    rw [← List.toFinset_card_of_nodup hnd]
    congr 1
    ext i
    simp only [List.mem_toFinset, List.mem_filter, List.mem_range, decide_eq_true_eq]
    exact ⟨fun h => h.2, fun h => ⟨hA i h, h⟩⟩
  rw [firstK, List.toFinset_card_of_nodup (hnd.sublist (List.take_sublist _ _)), List.length_take,
    hlen, Nat.min_eq_left hk]

/-- **Decoding on an agreement set** (phases 4–5, pure): if the word `u` agrees with `Enc(c)` on
a set `A` of at least `2^ℓ` positions below `n ≤ 2^20`, interpolating on its first `2^ℓ`
positions and running the butterflies returns `c`. -/
theorem decode_agree {M : Type*} [Field M] [Algebra F M] {ℓ : ℕ} (hℓ : ℓ ≤ logNMax)
    {n : ℕ} (hn : n ≤ nMax) {A : Finset ℕ} (hA : ∀ i ∈ A, i < n) (hcard : 2 ^ ℓ ≤ A.card)
    (c : Fin (2 ^ ℓ) → M) (u : ℕ → M) (hu : ∀ i ∈ A, u i = encN D c i) (i : Fin (2 ^ ℓ)) :
    bflyRun D logNMax 0 ℓ (interpF D (firstK n A (2 ^ ℓ)) u) i = c i :=
  bfly_decode_D hℓ (fun j hj => lt_of_lt_of_le (firstK_lt n A _ j hj) hn) (firstK_card hA hcard)
    c u (fun j hj => hu j (firstK_subset n A _ hj)) i

/-! ## Controls -/

section Controls

variable {L : Type*} [Field L] {M : Type*} [Field M] [Algebra L M]

/-- **Positive control**: one level on two points is the explicit merge
`(y₀ − α (y₁ − y₀), y₁ − y₀)`, `α = Ŵ₀(pt s₀)`. -/
theorem bflyRun_one (pt : ℕ → L) (N s0 : ℕ) (y : ℕ → M) :
    bflyRun pt N s0 1 y 0 = y 0 - algebraMap L M (wAt pt N 0 s0) * (y 1 - y 0) ∧
    bflyRun pt N s0 1 y 1 = y 1 - y 0 := by
  simp [bflyRun, bflyLevel]

/-- **Negative control**: zero levels change nothing, so the decoding needs all `ℓ` levels
(the first coefficient of a two-point row is not its first value unless `α (y₁ − y₀) = 0`). -/
theorem bflyRun_zero (pt : ℕ → L) (N s0 : ℕ) (y : ℕ → M) : bflyRun pt N s0 0 y = y := rfl

end Controls

/-- **Controls of `firstK`**: the first two of `{5, 1, 3}` are `{1, 3}`; asking for more than the
set holds gives the whole set (so `decode_agree` needs `2^ℓ ≤ |A|`). -/
theorem firstK_ctl : firstK 8 {5, 1, 3} 2 = {1, 3} ∧ firstK 8 {5, 1, 3} 7 = {1, 3, 5} := by
  decide

end FR.X

end G6_FRXDecodeB

section G6_FRXBflyDefs

-- New for `flock-recursive` (BLUEPRINT §6.2 step 4, §6.5 `coeffs_spec`; stage S-H2, track L-ext).

/-!
# The butterflies on the machine: the programs

BLUEPRINT §6.2 step 4 ("novel coefficients"), in the iterative form of `FRXDecodeB.bflyRun`.
An `F` element sits in two consecutive heap cells (`rdF`, `c₀` first); a row of `2^ℓ` elements
from cell `A` holds element `i` at `A + 2i`.

* **The basis table** (`wtabIR tb`): the rows `wRow D 20 v`, `v < 20`, at `tb + 40 v + 2 i`.
  Row `0` is `D(2^i)`, the words `(2^i, 0)`; row `v + 1` maps each entry `a` of row `v` to
  `a (a + 1) · (b (b + 1))⁻¹`, `b` entry `v + 1` of row `v` (LCH, `FRRSEval.wRow`): one `invF`
  per row.
* **`α`** (`alphaIR`): `wAt D 20 l base`, the sum over the set bits `i < 20` of `base` of the
  table entry `(l, i)`, branch-free (`mask = 0 − bit`).
* **One butterfly** (`pairBody`): pair `q < 2^(ℓ−1)` of level `l` (`P = 2^l`) has the positions
  `lo = ⌊q/P⌋·2P + q mod P` and `hi = lo + P`; with `u, w` their values,
  `lo := u + α (w + u)`, `hi := w + u` (characteristic 2: `bflyLevel`'s `u − α (w − u)`, `w − u`).
* **A level** (`levelIR ℓ`): the `2^(ℓ−1)` pairs; **the butterflies** (`bflyIR ℓ tb`): levels
  `0 … ℓ − 1` on the row at `rA0`.

Registers `140 … 177`.
-/

namespace FR.X

open RecursionFast

/-! ## Registers -/

/-- The pair index `q`. -/ def rQ : ℕ := 140
/-- The level `l`. -/ def rLv : ℕ := 141
/-- `2^l`. -/ def rP2 : ℕ := 142
/-- The block's base position. -/ def rBs : ℕ := 143
/-- `q mod 2^l`. -/ def uX : ℕ := 144
/-- Scratch. -/ def uT1 : ℕ := 145
/-- Scratch. -/ def uT2 : ℕ := 146
/-- The address of `lo`. -/ def rAL : ℕ := 147
/-- Its second word. -/ def rAL1 : ℕ := 148
/-- The address of `hi`. -/ def rAH : ℕ := 149
/-- Its second word. -/ def rAH1 : ℕ := 150
/-- A table address. -/ def rTa : ℕ := 151
/-- Its second word. -/ def rTa1 : ℕ := 152
/-- The bit mask. -/ def rBit : ℕ := 153
/-- The bit index. -/ def uI : ℕ := 154
/-- The row's first cell `A`. -/ def rA0 : ℕ := 155
/-- The table row's first cell. -/ def rTr : ℕ := 156
/-- Counter of the pair loop. -/ def rC1 : ℕ := 157
/-- Count of the pair loop. -/ def rN1 : ℕ := 158
/-- Counter of the bit loops. -/ def rC2 : ℕ := 159
/-- Count of the bit loops. -/ def rN2 : ℕ := 160
/-- Counter of the level loops. -/ def rC3 : ℕ := 161
/-- Count of the level loops. -/ def rN3 : ℕ := 162
/-- `α` (an `F` pair). -/ def fAl : ℕ := 164
/-- `u`. -/ def fU : ℕ := 166
/-- `w`. -/ def fW : ℕ := 168
/-- `w + u`. -/ def fH : ℕ := 170
/-- `α (w + u)`. -/ def fT : ℕ := 172
/-- The new `lo`. -/ def fN : ℕ := 174
/-- A table entry. -/ def fG : ℕ := 176

/-! ## Heap `F` elements -/

/-- `d, d + 1 :=` the heap element at `M[p]` (`p1 := p + 1`). -/
def ldF (d p p1 : ℕ) : XIR := .seq (.load d p) (.seq (.blk [.op .add p1 p cOne]) (.load (d + 1) p1))

/-- The heap element at `M[p]` `:=` registers `v, v + 1` (`p1 := p + 1`). -/
def stF (p p1 v : ℕ) : XIR := .seq (.blk [.op .add p1 p cOne]) (.seq (.store p v) (.store p1 (v + 1)))

/-! ## `α = wAt D 20 l base` -/

/-- One bit `i`: `α += [bit_i(base)] · T[l][i]`; `rTa += 2`, `i += 1`. -/
def alphaBody : XIR :=
  .seq (.blk [.op .shr rBit rBs uI, .op .and rBit rBit cOne, .const uT1 0, .op .sub rBit uT1 rBit])
    (.seq (ldF fG rTa rTa1)
      (.blk [.op .and fG fG rBit, .op .and (fG + 1) (fG + 1) rBit, .op .xor fAl fAl fG,
        .op .xor (fAl + 1) (fAl + 1) (fG + 1), .const uT1 2, .op .add rTa rTa uT1,
        .op .add uI uI cOne]))

/-- **`α`** for the block at `rBs`, from the table row at `rTr`. -/
def alphaIR : XIR :=
  .seq (.blk [.const fAl 0, .const (fAl + 1) 0, .const uI 0, .op .or rTa rTr rTr, .const rN2 20])
    (.loopK rC2 rN2 20 alphaBody)

/-! ## One butterfly, a level, the iteration -/

/-- The pair's addresses: `rBs := ⌊q/P⌋ · 2P`, `rAL := A + 2 lo`, `rAH := A + 2 hi`. -/
def pairPs : List Prim :=
  [.op .divu uT1 rQ rP2, .op .remu uX rQ rP2, .op .add uT2 rP2 rP2, .op .mul rBs uT1 uT2,
   .op .add uT1 rBs uX, .op .add uT1 uT1 uT1, .op .add rAL rA0 uT1, .op .add rAH rAL uT2]

/-- The butterfly's arithmetic: `u, w` from the heap, `fH := w + u`, `fN := u + α fH`. -/
def arithIR : XIR :=
  .seq (ldF fU rAL rAL1) (.seq (ldF fW rAH rAH1) (.seq (addF fH fW fU) (.seq (mulF fT fAl fH)
    (addF fN fU fT))))

/-- **One butterfly**: pair `q` of the level in `rLv`. -/
def pairBody : XIR :=
  .seq (.blk pairPs) (.seq alphaIR (.seq arithIR (.seq (stF rAL rAL1 fN)
    (.seq (stF rAH rAH1 fH) (.blk [.op .add rQ rQ cOne])))))

/-- **A level**: the `2^(ℓ−1)` pairs, `P = 2^l`. -/
def levelIR (ℓ : ℕ) : XIR :=
  .seq (.blk [.const rQ 0, .op .shl rP2 cOne rLv, .const rN1 (toWord (2 ^ (ℓ - 1)))])
    (.loopK rC1 rN1 (toWord (2 ^ (ℓ - 1))) pairBody)

/-- A level, then the next level and table row. -/
def lvlStep (ℓ : ℕ) : XIR :=
  .seq (levelIR ℓ) (.blk [.op .add rLv rLv cOne, .const uT1 40, .op .add rTr rTr uT1])

/-- **The butterflies**: levels `0 … ℓ − 1` on the row at `rA0`, the table at `tb`. -/
def bflyIR (ℓ tb : ℕ) : XIR :=
  .seq (.blk [.const rLv 0, .const rTr (toWord tb), .const rN3 (toWord ℓ)])
    (.loopK rC3 rN3 (toWord ℓ) (lvlStep ℓ))

/-! ## The basis table -/

/-- Row `0`, entry `i`: the words `(2^i, 0)` (`D(2^i)`). -/
def row0Body : XIR :=
  .seq (.blk [.op .shl fG cOne uI, .const (fG + 1) 0]) (.seq (stF rTa rTa1 fG)
    (.blk [.const uT1 2, .op .add rTa rTa uT1, .op .add uI uI cOne]))

/-- Row `0` at `rTr`. -/
def row0IR : XIR :=
  .seq (.blk [.const uI 0, .op .or rTa rTr rTr, .const rN2 20]) (.loopK rC2 rN2 20 row0Body)

/-- Row `v + 1`, entry at `rTa` (row `v`): `a (a + 1) · fAl`, stored 40 cells on. -/
def rowBody : XIR :=
  .seq (ldF fU rTa rTa1) (.seq (.blk [.op .xor fW fU cOne, .op .or (fW + 1) (fU + 1) (fU + 1)])
    (.seq (mulF fH fU fW) (.seq (mulF fN fH fAl) (.seq (.blk [.const uT1 40, .op .add rAH rTa uT1])
      (.seq (stF rAH rAH1 fN) (.blk [.const uT1 2, .op .add rTa rTa uT1]))))))

/-- Row `v + 1` from row `v` (at `rTr`, `v` in `rLv`): `fAl := (b (b + 1))⁻¹`, `b` entry `v + 1`;
then the 20 entries; `rLv += 1`, `rTr += 40`. -/
def rowIR : XIR :=
  .seq (.blk [.op .add uT1 rLv cOne, .op .add uT1 uT1 uT1, .op .add rTa rTr uT1])
    (.seq (ldF fU rTa rTa1) (.seq (.blk [.op .xor fW fU cOne, .op .or (fW + 1) (fU + 1) (fU + 1)])
      (.seq (mulF fH fU fW) (.seq (invF fAl fH) (.seq (.blk [.op .or rTa rTr rTr, .const rN2 20])
        (.seq (.loopK rC2 rN2 20 rowBody)
          (.blk [.op .add rLv rLv cOne, .const uT1 40, .op .add rTr rTr uT1])))))))

/-- **The basis table** at `tb`: row `0`, then rows `1 … 19`. -/
def wtabIR (tb : ℕ) : XIR :=
  .seq (.blk [.const rTr (toWord tb)]) (.seq row0IR (.seq (.blk [.const rLv 0, .const rN3 19])
    (.loopK rC3 rN3 19 rowIR)))

/-! ## Well formed, no tape loop, no output, cost -/

theorem wf_alphaIR : WF alphaIR := by
  simp +decide only [alphaIR, alphaBody, ldF, WF, Writes, Prim.dst, rBit, uT1, rTa, rTa1, fG, fAl,
    uI, rN2, rC2, cTmp, regs, or_false, and_true]

theorem nw_mulF {d a b c : ℕ} (hc : 15 ≤ c) (h0 : c ≠ d) (h1 : c ≠ d + 1) :
    ¬ Writes (mulF d a b) c := fun ⟨p, hp, he⟩ => by
  rcases mulFC_dst' d a b p hp with h | h | h <;> omega

theorem nw_invF {d a c : ℕ} (hc : 19 ≤ c) (h0 : c ≠ d) (h1 : c ≠ d + 1) :
    ¬ Writes (invF d a) c := fun ⟨p, hp, he⟩ => by
  rcases invFC_dst' d a p hp with h | h | h <;> omega

/-- `simp` forms of `wf_mulF` and `nw_mulF`: the `WF`/`Writes` side conditions never unfold
`mulF`'s primitives (G2: elaboration time). -/
theorem mulF_wf_iff {d a b : ℕ} (hd : 4 ≤ d) : WF (mulF d a b) ↔ True :=
  iff_true_intro (wf_mulF d a b hd)

theorem mulF_writes_iff {d a b c : ℕ} (hc : 15 ≤ c) (h0 : c ≠ d) (h1 : c ≠ d + 1) :
    Writes (mulF d a b) c ↔ False := ⟨nw_mulF hc h0 h1, False.elim⟩

theorem wf_bflyIR (ℓ tb : ℕ) : WF (bflyIR ℓ tb) := by
  simp +decide only [bflyIR, lvlStep, levelIR, pairBody, pairPs, arithIR, alphaIR, alphaBody, ldF,
    stF, addF, addFC, WF, Writes, Prim.dst, rQ, rLv, rP2, rBs, uX, uT1, uT2, rAL, rAL1, rAH, rAH1,
    rTa, rTa1, rBit, uI, rTr, rC1, rN1, rC2, rN2, rC3, rN3, fAl, fU, fW, fH, fT, fN, fG, cTmp, regs,
    mulF_wf_iff, mulF_writes_iff, List.mem_cons, List.mem_nil_iff, forall_eq_or_imp,
    exists_eq_or_imp, forall_eq, exists_eq_left, or_false, and_true]

theorem wf_wtabIR (tb : ℕ) : WF (wtabIR tb) := by
  have m1 := wf_mulF fH fU fW (by decide)
  have m2 := wf_mulF fN fH fAl (by decide)
  have m3 := wf_invF fAl fH (by decide)
  have n1 : ¬ Writes (mulF fH fU fW) rC2 := nw_mulF (by decide) (by decide) (by decide)
  have n2 : ¬ Writes (mulF fN fH fAl) rC2 := nw_mulF (by decide) (by decide) (by decide)
  have n3 : ¬ Writes (mulF fH fU fW) rC3 := nw_mulF (by decide) (by decide) (by decide)
  have n4 : ¬ Writes (invF fAl fH) rC3 := nw_invF (by decide) (by decide) (by decide)
  have n5 : ¬ Writes (mulF fN fH fAl) rC3 := nw_mulF (by decide) (by decide) (by decide)
  simp only [wtabIR, row0IR, row0Body, rowIR, rowBody, ldF, stF, WF, Writes, Prim.dst,
    List.mem_cons, List.mem_nil_iff, m1, m2, m3, n1, n2, n3, n4, n5]
  simp [rLv, uT1, rAH, rAH1, rTa, rTa1, uI, rTr, rC2, rN2, rC3, rN3, fU, fW, fG, cTmp,
    regs]

theorem noLoopT_bflyIR (ℓ tb : ℕ) : NoLoopT (bflyIR ℓ tb) := by
  simp [bflyIR, lvlStep, levelIR, pairBody, arithIR, alphaIR, alphaBody, ldF, stF, addF, mulF,
    NoLoopT]

theorem noLoopT_wtabIR (tb : ℕ) : NoLoopT (wtabIR tb) := by
  simp [wtabIR, row0IR, row0Body, rowIR, rowBody, ldF, stF, mulF, invF, NoLoopT]

theorem outs_bflyIR (ℓ tb t : ℕ) : outs (bflyIR ℓ tb) t = 0 := by
  simp [bflyIR, lvlStep, levelIR, pairBody, arithIR, alphaIR, alphaBody, ldF, stF, addF, mulF,
    outs]

theorem outs_wtabIR (tb t : ℕ) : outs (wtabIR tb) t = 0 := by
  simp [wtabIR, row0IR, row0Body, rowIR, rowBody, ldF, stF, mulF, invF, outs]

theorem cost_alphaIR (t : ℕ) : cost alphaIR t = 618 := by
  simp only [alphaIR, alphaBody, ldF, cost, blkSteps, List.length_cons, List.length_nil]
  norm_num

theorem cost_pairBody (t : ℕ) : cost pairBody t = 738 := by
  simp only [pairBody, pairPs, arithIR, ldF, stF, cost, cost_alphaIR, addF, mulF, blkSteps, len_addFC,
    len_mulFC, List.length_cons, List.length_nil]
  norm_num

/-- **The butterflies' cost**: `ℓ` levels of `2^(ℓ−1)` pairs. -/
theorem cost_bflyIR (ℓ tb t : ℕ) (hℓ : 2 ^ (ℓ - 1) < 2 ^ 64) (hℓ' : ℓ < 2 ^ 64) :
    cost (bflyIR ℓ tb) t = 14 + ℓ * (741 * 2 ^ (ℓ - 1) + 23) := by
  have a1 : (toWord (2 ^ (ℓ - 1))).toNat = 2 ^ (ℓ - 1) := toNat_toWord hℓ
  have a2 : (toWord ℓ).toNat = ℓ := toNat_toWord hℓ'
  simp only [bflyIR, lvlStep, levelIR, cost, cost_pairBody, blkSteps, List.length_cons,
    List.length_nil, a1, a2]
  norm_num
  ring

theorem cost_wtabIR (tb t : ℕ) : cost (wtabIR tb) t = 79606 := by
  have a : (19 : Word).toNat = 19 := rfl
  simp only [wtabIR, row0IR, row0Body, rowIR, rowBody, ldF, stF, mulF, invF, cost, blkSteps,
    len_mulFC, len_invFC, List.length_cons, List.length_nil, a]
  norm_num

end FR.X

end G6_FRXBflyDefs

section G6_FRXBaryDefs

-- New for `flock-recursive` (BLUEPRINT §6.2 step 4; S-H2 Part 11 §4 step 4; stage S-H2, track
-- L-ext).

/-!
# The barycentric interpolation: the pure form and the program

`interpF pt J y s` (`FRRSEval`) is the Lagrange interpolation of `y` on the points `pt J` at
`pt s`. The machine computes it in barycentric form (S-H2 Part 11 §4 step 4):

* off `J`: `interpF pt J y s = ℓ(s) · Σ_{i ∈ J} y i · w_i · (pt s − pt i)⁻¹`, with
  `ℓ(s) = Π_{m ∈ J} (pt s − pt m)` and `w_i = (Π_{m ∈ J∖i} (pt i − pt m))⁻¹` (`interpF_bary`);
* on `J`: `interpF pt J y s = y s` (`interpF_self`).

The machine tells the two apart by `ℓ(s) = 0` (`pt` injective). Over `F`, with `J` the list
`Jl = J₀ … J_{k−1}` (the agreement scan's), the machine's value is `baryVal` and
**`baryVal_eq`** proves it is `interpF D Jl.toFinset y s` for `s < 2^20`.

The program (`baryIR`) works coordinate-wise over `F`: a column holds `C` elements of `F` (level
0: 64; levels 1–4: the 16 `F`-coordinates of 8 `K` elements), element `c` of position `j` at
`cb + cs·j + 2c`. Its phases:

1. `djIR`: `DJ[t] := D(J_t)` (`alphaIR` on the basis table's row 0);
2. `wIR`: `W[t] := (Π_{m ≠ t} (DJ[t] + DJ[m]))⁻¹`;
3. per target `s < k` (`sBody`): `D(s)`; `E[t] := W[t] · (D(s) + DJ[t])⁻¹` and
   `ℓ := Π_t (D(s) + DJ[t])`; per coordinate `c`: `acc := Σ_t y_c(J_t) E[t]` (registers only),
   then `out[c][s] := (ℓ = 0 ? y_c(s) : ℓ · acc)` at `ob + 2(c·k + s)`.
-/

namespace FR.X

open RecursionFast FR Finset

/-! ## The pure form -/

section Pure

variable {L : Type*} [Field L] {M : Type*} [Field M] [Algebra L M]

/-- **On `J`, the interpolation returns the value.** -/
theorem interpF_self {pt : ℕ → L} {J : Finset ℕ} (hJ : Set.InjOn pt J) (y : ℕ → M) {s : ℕ}
    (hs : s ∈ J) : interpF pt J y s = y s := by
  unfold interpF
  rw [Finset.sum_eq_single s]
  · rw [Finset.prod_eq_one, mul_one]
    intro m hm
    obtain ⟨hne, hmJ⟩ := Finset.mem_erase.1 hm
    have : algebraMap L M (pt s) - algebraMap L M (pt m) ≠ 0 := by
      rw [sub_ne_zero]
      exact fun h => hne (hJ hmJ hs ((algebraMap L M).injective h).symm)
    exact div_self this
  · intro i hi hne
    rw [Finset.prod_eq_zero (i := s) (Finset.mem_erase.2 ⟨Ne.symm hne, hs⟩) (by simp), mul_zero]
  · intro h; exact absurd hs h

/-- **Off `J`, the interpolation is barycentric**: `ℓ(s) · Σ_i y i · w_i (pt s − pt i)⁻¹`. -/
theorem interpF_bary {pt : ℕ → L} {J : Finset ℕ} {s : ℕ} (hs : ∀ m ∈ J, pt s ≠ pt m)
    (y : ℕ → M) :
    interpF pt J y s = algebraMap L M (∏ m ∈ J, (pt s - pt m)) *
      ∑ i ∈ J, y i * algebraMap L M ((∏ m ∈ J.erase i, (pt i - pt m))⁻¹ * (pt s - pt i)⁻¹) := by
  unfold interpF
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun i hi => ?_
  have hsi : pt s - pt i ≠ 0 := sub_ne_zero.2 (hs i hi)
  have hl : ∏ m ∈ J, (pt s - pt m) = (pt s - pt i) * ∏ m ∈ J.erase i, (pt s - pt m) :=
    (Finset.mul_prod_erase J (fun m => pt s - pt m) hi).symm
  have e : ∏ m ∈ J.erase i, (algebraMap L M (pt s) - algebraMap L M (pt m)) /
      (algebraMap L M (pt i) - algebraMap L M (pt m)) =
      algebraMap L M (∏ m ∈ J.erase i, (pt s - pt m) / (pt i - pt m)) := by
    rw [map_prod]; simp [map_sub, map_div₀]
  rw [e, Finset.prod_div_distrib, hl]
  rw [mul_left_comm, ← map_mul]
  congr 2
  field_simp

end Pure

/-! ## The machine's value over `F`, against `interpF` -/

/-- `D(J_t)` for the list `Jl`. -/
def dj (Jl : List ℕ) (t : ℕ) : F := D (Jl.getD t 0)

/-- **The weight** `W[t] = (Π_{m < k, m ≠ t} (DJ[t] + DJ[m]))⁻¹`, as the machine's product
(`m = t` contributes `1`). -/
def wgt (Jl : List ℕ) (k t : ℕ) : F :=
  (∏ m ∈ range k, if m = t then 1 else dj Jl t + dj Jl m)⁻¹

/-- `ℓ(s) = Π_{t < k} (D s + DJ[t])`. -/
def ellS (Jl : List ℕ) (k s : ℕ) : F := ∏ t ∈ range k, (D s + dj Jl t)

/-- `E[t] = W[t] · (D s + DJ[t])⁻¹`. -/
def eAt (Jl : List ℕ) (k s t : ℕ) : F := wgt Jl k t * (D s + dj Jl t)⁻¹

/-- **The machine's value** at target `s` for the values `y`: `y s` when `ℓ(s) = 0`, else
`ℓ(s) · Σ_t y(J_t) E[t]`. -/
def baryVal (Jl : List ℕ) (k s : ℕ) (y : ℕ → F) : F :=
  if ellS Jl k s = 0 then y s else ellS Jl k s * ∑ t ∈ range k, y (Jl.getD t 0) * eAt Jl k s t

theorem sub_eq_add_F (a b : F) : a - b = a + b := rfl

theorem toFinset_eq_image (Jl : List ℕ) :
    Jl.toFinset = (range Jl.length).image (fun t => Jl.getD t 0) := by
  ext x
  simp only [List.mem_toFinset, Finset.mem_image, Finset.mem_range, List.mem_iff_getElem]
  constructor
  · rintro ⟨t, ht, rfl⟩; exact ⟨t, ht, by rw [List.getD_eq_getElem]⟩
  · rintro ⟨t, ht, rfl⟩; exact ⟨t, ht, by rw [List.getD_eq_getElem]⟩

theorem getD_injOn {Jl : List ℕ} (hnd : Jl.Nodup) :
    Set.InjOn (fun t => Jl.getD t 0) (range Jl.length : Set ℕ) := fun a ha b hb h => by
  simp only [coe_range, Set.mem_Iio] at ha hb
  simp only [List.getD_eq_getElem _ _ ha, List.getD_eq_getElem _ _ hb] at h
  exact (hnd.getElem_inj_iff).1 h

theorem prod_toFinset {Jl : List ℕ} (hnd : Jl.Nodup) (f : ℕ → F) :
    ∏ m ∈ Jl.toFinset, f m = ∏ t ∈ range Jl.length, f (Jl.getD t 0) := by
  rw [toFinset_eq_image, Finset.prod_image (getD_injOn hnd)]

theorem sum_toFinset {Jl : List ℕ} (hnd : Jl.Nodup) (f : ℕ → F) :
    ∑ m ∈ Jl.toFinset, f m = ∑ t ∈ range Jl.length, f (Jl.getD t 0) := by
  rw [toFinset_eq_image, Finset.sum_image (getD_injOn hnd)]

theorem prod_erase_ite {J : Finset ℕ} {i : ℕ} (hi : i ∈ J) (f : ℕ → F) :
    ∏ m ∈ J.erase i, f m = ∏ m ∈ J, if m = i then 1 else f m := by
  rw [← Finset.mul_prod_erase J _ hi, if_pos rfl, one_mul]
  exact Finset.prod_congr rfl fun m hm => by rw [if_neg (Finset.mem_erase.1 hm).1]

/-- **The machine's value is the interpolation** (`J ⊆ [0, 2^20)` listed without repeats,
`s < 2^20`). -/
theorem baryVal_eq {Jl : List ℕ} (hnd : Jl.Nodup) (hJ : ∀ j ∈ Jl, j < nMax) {s : ℕ}
    (hs : s < nMax) (y : ℕ → F) :
    baryVal Jl Jl.length s y = interpF D Jl.toFinset y s := by
  have hinj : Set.InjOn D (Jl.toFinset : Set ℕ) := fun a ha b hb h =>
    D_injOn_nMax (Set.mem_Iio.2 (hJ a (List.mem_toFinset.1 ha)))
      (Set.mem_Iio.2 (hJ b (List.mem_toFinset.1 hb))) h
  have hget : ∀ t < Jl.length, Jl.getD t 0 ∈ Jl := fun t ht => by
    rw [List.getD_eq_getElem _ _ ht]; exact List.getElem_mem ht
  by_cases hsJ : s ∈ Jl
  · obtain ⟨t, ht, hts⟩ := List.mem_iff_getElem.1 hsJ
    have h0 : ellS Jl Jl.length s = 0 := by
      refine Finset.prod_eq_zero (i := t) (Finset.mem_range.2 ht) ?_
      rw [dj, List.getD_eq_getElem _ _ ht, hts, ← sub_eq_add_F, sub_self]
    rw [baryVal, if_pos h0, interpF_self hinj y (List.mem_toFinset.2 hsJ)]
  · have hne : ∀ m ∈ Jl.toFinset, D s ≠ D m := fun m hm h => hsJ (by
      have := D_injOn_nMax (Set.mem_Iio.2 hs) (Set.mem_Iio.2 (hJ m (List.mem_toFinset.1 hm))) h
      rw [this]; exact List.mem_toFinset.1 hm)
    have h0 : ellS Jl Jl.length s ≠ 0 := by
      refine Finset.prod_ne_zero_iff.2 fun t ht => ?_
      rw [dj, ← sub_eq_add_F, sub_ne_zero]
      exact hne _ (List.mem_toFinset.2 (hget t (Finset.mem_range.1 ht)))
    rw [baryVal, if_neg h0, interpF_bary hne, Algebra.algebraMap_self]
    simp only [RingHom.id_apply]
    rw [prod_toFinset hnd, sum_toFinset hnd]
    refine congrArg₂ _ rfl (Finset.sum_congr rfl fun t ht => ?_)
    have ht' := Finset.mem_range.1 ht
    rw [eAt, wgt,
      prod_erase_ite (List.mem_toFinset.2 (hget t ht')), prod_toFinset hnd]
    congr 3
    refine Finset.prod_congr rfl fun m hm => ?_
    have hm' := Finset.mem_range.1 hm
    by_cases hmt : m = t
    · rw [if_pos hmt, if_pos (by rw [hmt])]
    · rw [if_neg hmt, if_neg (fun h => hmt ((hnd.getElem_inj_iff).1 (by
        rwa [List.getD_eq_getElem _ _ hm', List.getD_eq_getElem _ _ ht'] at h))), dj, dj]
      rfl

/-! ## Registers (`216 …`) -/

/-- `D(s)` or `DJ[t]`. -/ def fDs : ℕ := 216
/-- `ℓ`. -/ def fLp : ℕ := 218
/-- `D(s) + DJ[t]`. -/ def fDd : ℕ := 220
/-- Its inverse. -/ def fIv : ℕ := 222
/-- `E[t]`. -/ def fEt : ℕ := 224
/-- A product. -/ def fPr : ℕ := 226
/-- A column value. -/ def fY : ℕ := 228
/-- The accumulator. -/ def fAc : ℕ := 230
/-- A loaded element. -/ def fX : ℕ := 232
/-- `t` (or `m`'s partner). -/ def bT : ℕ := 236
/-- `m`. -/ def bM : ℕ := 237
/-- `s`. -/ def bS : ℕ := 238
/-- `c`. -/ def bCi : ℕ := 239
/-- An address. -/ def bA : ℕ := 240
/-- Its successor. -/ def bA1 : ℕ := 241
/-- A column address. -/ def bJ : ℕ := 242
/-- Constant scratch. -/ def bK : ℕ := 243
/-- A flag. -/ def bZ : ℕ := 244
/-- The outer loop's counter. -/ def bC1 : ℕ := 245
/-- Its count. -/ def bN1 : ℕ := 246
/-- The middle loop's counter. -/ def bC2 : ℕ := 247
/-- Its count. -/ def bN2 : ℕ := 248
/-- The inner loop's counter. -/ def bC3 : ℕ := 249
/-- Its count. -/ def bN3 : ℕ := 250
/-- `2c`. -/ def bCo : ℕ := 251

/-! ## The program -/

/-- `d := b + m · M[i]`. -/
def addrPs (d i b m : ℕ) : List Prim :=
  [.const bK (toWord m), .op .mul d i bK, .const bK (toWord b), .op .add d d bK]

/-- **`DJ[t] := D(J_t)`** for the current `t` (`J_t` at `jb + t`, `DJ[t]` at `djb + 2t`). -/
def djBody (jb djb tb : ℕ) : XIR :=
  .seq (.blk (addrPs bA bT jb 1)) (.seq (.load rBs bA) (.seq (.blk [.const rTr (toWord tb)])
    (.seq alphaIR (.seq (.blk (addrPs bA bT djb 2)) (.seq (stF bA bA1 fAl)
      (.blk [.op .add bT bT cOne]))))))

/-- The table `DJ`. -/
def djIR (k jb djb tb : ℕ) : XIR :=
  .seq (.blk [.const bT 0, .const bN1 (toWord k)]) (.loopK bC1 bN1 (toWord k) (djBody jb djb tb))

/-- One factor of `W[t]`'s product: `fPr *= DJ[t] + DJ[m]` unless `m = t`. -/
def wInner (djb : ℕ) : XIR :=
  .seq (.blk (addrPs bA bM djb 2)) (.seq (ldF fX bA bA1) (.seq (addF fDd fDs fX)
    (.seq (.blk [.op .eq bZ bM bT]) (.seq (.ite bZ (.blk []) (mulF fPr fPr fDd))
      (.blk [.op .add bM bM cOne])))))

/-- **`W[t] := (Π_{m ≠ t} (DJ[t] + DJ[m]))⁻¹`** at `wb + 2t`. -/
def wtBody (k djb wb : ℕ) : XIR :=
  .seq (.blk (addrPs bA bT djb 2)) (.seq (ldF fDs bA bA1)
    (.seq (.blk [.const fPr 1, .const (fPr + 1) 0, .const bM 0, .const bN2 (toWord k)])
      (.seq (.loopK bC2 bN2 (toWord k) (wInner djb)) (.seq (invF fIv fPr)
        (.seq (.blk (addrPs bA bT wb 2)) (.seq (stF bA bA1 fIv) (.blk [.op .add bT bT cOne])))))))

/-- The table `W`. -/
def wtIR (k djb wb : ℕ) : XIR :=
  .seq (.blk [.const bT 0, .const bN1 (toWord k)]) (.loopK bC1 bN1 (toWord k) (wtBody k djb wb))

/-- **`E[t] := W[t] · (D(s) + DJ[t])⁻¹`** at `eb + 2t`, and `ℓ *= D(s) + DJ[t]`. -/
def eBody (djb wb eb : ℕ) : XIR :=
  .seq (.blk (addrPs bA bT djb 2)) (.seq (ldF fX bA bA1) (.seq (addF fDd fDs fX)
    (.seq (mulF fLp fLp fDd) (.seq (invF fIv fDd) (.seq (.blk (addrPs bA bT wb 2))
      (.seq (ldF fX bA bA1) (.seq (mulF fEt fX fIv) (.seq (.blk (addrPs bA bT eb 2))
        (.seq (stF bA bA1 fEt) (.blk [.op .add bT bT cOne]))))))))))

/-- **`acc += y_c(J_t) · E[t]`** (`y_c(j)` at `cb + cs·j + 2c`, `2c` in `bCo`). -/
def aBody (jb eb cb cs : ℕ) : XIR :=
  .seq (.blk (addrPs bA bT jb 1)) (.seq (.load bJ bA)
    (.seq (.blk (addrPs bJ bJ cb cs ++ [.op .add bJ bJ bCo])) (.seq (ldF fY bJ bA1)
      (.seq (.blk (addrPs bA bT eb 2)) (.seq (ldF fX bA bA1) (.seq (mulF fPr fY fX)
        (.seq (addF fAc fAc fPr) (.blk [.op .add bT bT cOne]))))))))

/-- `fAc := y_c(s)`. -/
def yIR (cb cs : ℕ) : XIR :=
  .seq (.blk (addrPs bA bS cb cs ++ [.op .add bA bA bCo])) (ldF fAc bA bA1)

/-- **One coordinate `c`**: `acc := Σ_t y_c(J_t) E[t]`, then `out[c][s] := (ℓ = 0 ? y_c(s) :
ℓ · acc)` at `ob + 2k·c + 2s`. -/
def cBody (k jb eb cb cs ob : ℕ) : XIR :=
  .seq (.blk [.const fAc 0, .const (fAc + 1) 0, .const bT 0, .const bN3 (toWord k)])
    (.seq (.loopK bC3 bN3 (toWord k) (aBody jb eb cb cs))
      (.seq (.ite bZ (yIR cb cs) (mulF fAc fLp fAc))
        (.seq (.blk (addrPs bA bCi ob (2 * k) ++ [.op .add bA bA bS, .op .add bA bA bS]))
          (.seq (stF bA bA1 fAc) (.blk [.op .add bCi bCi cOne, .const bK 2,
            .op .add bCo bCo bK])))))

/-- **One target `s`**: `D(s)`, the `E` row and `ℓ`, the flag `[ℓ = 0]`, the `C` coordinates. -/
def sBody (k C jb djb wb eb cb cs ob tb : ℕ) : XIR :=
  .seq (.seq (.blk [.op .or rBs bS bS, .const rTr (toWord tb)]) alphaIR)
    (.seq (.blk [.op .or fDs fAl fAl, .op .or (fDs + 1) (fAl + 1) (fAl + 1), .const fLp 1,
        .const (fLp + 1) 0, .const bT 0, .const bN2 (toWord k)])
      (.seq (.loopK bC2 bN2 (toWord k) (eBody djb wb eb))
        (.seq (.blk [.op .or bZ fLp (fLp + 1), .const bK 0, .op .eq bZ bZ bK, .const bCi 0,
            .const bCo 0, .const bN2 (toWord C)])
          (.seq (.loopK bC2 bN2 (toWord C) (cBody k jb eb cb cs ob))
            (.blk [.op .add bS bS cOne])))))

/-- **The interpolation**: `out[c][s] = interpF D J y_c s` for `s < k`, `c < C`. -/
def baryIR (k C jb djb wb eb cb cs ob tb : ℕ) : XIR :=
  .seq (djIR k jb djb tb) (.seq (wtIR k djb wb)
    (.seq (.blk [.const bS 0, .const bN1 (toWord k)])
      (.loopK bC1 bN1 (toWord k) (sBody k C jb djb wb eb cb cs ob tb))))

/-! ## Well formed, cost, size -/

theorem bnw_mulF {d a b i : ℕ} (h1 : i ≠ d) (h2 : i ≠ d + 1) (h3 : 15 ≤ i) :
    Writes (mulF d a b) i ↔ False := ⟨nw_mulF h3 h1 h2, False.elim⟩

theorem bnw_addF {d a b i : ℕ} (h1 : i ≠ d) (h2 : i ≠ d + 1) : Writes (addF d a b) i ↔ False :=
  ⟨fun ⟨p, hp, he⟩ => by have := addFC_dst d a b p hp; omega, False.elim⟩

theorem bnw_invF {d a i : ℕ} (h1 : i ≠ d) (h2 : i ≠ d + 1) (h3 : 19 ≤ i) :
    Writes (invF d a) i ↔ False := ⟨nw_invF h3 h1 h2, False.elim⟩

theorem wfF_mul {d a b : ℕ} (h : 4 ≤ d) : WF (mulF d a b) ↔ True := iff_true_intro (wf_mulF d a b h)
theorem wfF_add {d a b : ℕ} (h : 4 ≤ d) : WF (addF d a b) ↔ True := iff_true_intro (wf_addF d a b h)
theorem wfF_inv {d a : ℕ} (h : 4 ≤ d) : WF (invF d a) ↔ True := iff_true_intro (wf_invF d a h)

theorem wf_baryIR (k C jb djb wb eb cb cs ob tb : ℕ) :
    WF (baryIR k C jb djb wb eb cb cs ob tb) := by
  simp [baryIR, djIR, djBody, wtIR, wtBody, wInner, sBody, eBody, cBody, aBody, yIR, addrPs,
    alphaIR, alphaBody, ldF, stF, WF, Writes, Prim.dst, bnw_mulF, bnw_addF, bnw_invF, wfF_mul, wfF_add, wfF_inv,
    fDs, fLp, fDd, fIv, fEt, fPr, fY, fAc, fX, bT, bM, bS, bCi, bA, bA1, bJ, bK, bZ, bC1, bN1, bC2,
    bN2, bC3, bN3, bCo, rBs, rTr, rTa, rTa1, rBit, uI, uT1, fG, fAl, rC2, rN2, cTmp, regs]

theorem noLoopT_baryIR (k C jb djb wb eb cb cs ob tb : ℕ) :
    NoLoopT (baryIR k C jb djb wb eb cb cs ob tb) := by
  simp [baryIR, djIR, djBody, wtIR, wtBody, wInner, sBody, eBody, cBody, aBody, yIR, alphaIR,
    alphaBody, ldF, stF, mulF, addF, invF, NoLoopT]

theorem outs_baryIR (k C jb djb wb eb cb cs ob tb t : ℕ) :
    outs (baryIR k C jb djb wb eb cb cs ob tb) t = 0 := by
  simp [baryIR, djIR, djBody, wtIR, wtBody, wInner, sBody, eBody, cBody, aBody, yIR, alphaIR,
    alphaBody, ldF, stF, mulF, addF, invF, outs]

/-- **The interpolation's cost** (`k, C < 2^64`). -/
theorem cost_baryIR (k C jb djb wb eb cb cs ob tb t : ℕ) (hk : k < 2 ^ 64) (hC : C < 2 ^ 64) :
    cost (baryIR k C jb djb wb eb cb cs ob tb) t =
      38 + k * 2487 + k * C * 108 + k ^ 2 * 1363 + k ^ 2 * C * 106 := by
  have e1 : (toWord k).toNat = k := toNat_toWord hk
  have e2 : (toWord C).toNat = C := toNat_toWord hC
  simp only [baryIR, djIR, djBody, wtIR, wtBody, wInner, sBody, eBody, cBody, aBody, yIR, addrPs,
    ldF, stF, cost, cost_mulF, cost_addF, cost_invF, cost_alphaIR, blkSteps, List.length_cons,
    List.length_nil, List.length_append, e1, e2]
  norm_num
  ring_nf

end FR.X

end G6_FRXBaryDefs
