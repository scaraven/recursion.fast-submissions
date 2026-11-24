-- lvm6 X6a: the pure fields of X5's `SFront6`, proved: `childFits6` (the left child of every stack fits the output
-- format) and `hdrTape6` (the replayed header's `b, n, h, c'` are tape words 6, 7, 8–11, 12–15). New.
import Lvm6XExt
import LvmVEqCodec

/-!
# The pure fields of `SFront6`

* **`childFits6`**: `(child6 q).Fits` for every stack `q`: the reassembled proof is `8 · 29,769` bytes (`pLen18`), the
  trace has `4,349` entries of fewer than `2^32` bytes, the signature's counts are fixed.
* **`hdrTape6`**: when the scheme's replay `Ex` returns the header bytes `x` (the first `hdrLen` bytes of `π`, V1's
  `hdr6`), the tape holds `hdrView P18 x`'s fields: `b` (offset 8) at word 6, `n` (16) at word 7, `h` (24) at words
  8–11, `c'` (56) at words 12–15 (the tape is `c`, `|π|`, then `π` packed from word 5).
* **`SFront6.ofOpen`**: `SFront6` from its three other fields (`len`, `goodL`, `descends`).
-/

set_option autoImplicit false

namespace Lvm6.X

open RecursionFast Lvm Lvm.X Lvm.FS

/-! ## `childFits6` -/

theorem length_lens18 : lens18.length = 4348 := by
  rw [lens18_blocks]; decide +kernel

theorem walk_snd_mem : ∀ (u : ℕ) (l : List ℕ), ∀ x ∈ walk u l, x.2 ∈ l
  | _, [], _, hx => by cases hx
  | u, len :: r, x, hx => by
    rcases List.mem_cons.mp hx with rfl | hx
    · exact List.mem_cons_self
    · exact List.mem_cons_of_mem _ (walk_snd_mem _ r x hx)

/-- **The left child of every stack fits the output format.** -/
theorem childFits6 (q : Stack) : (child6 q).Fits := by
  unfold child6 leftOf6 Signed.Fits
  refine ⟨?_, ?_, ?_, (stW q _).isLt, by simp [sigOf], by simp [sigOf]⟩
  · show (reassemble6 leafLs18 (readTrace6 lens18 fun u => stW q (33 * stride6 + u))).data.size < 2 ^ 64
    rw [← Array.length_toList, reassemble6_words _ leafLs18 lens18 (fun l h => (lensOK18 l h).1),
      wordsBytes_length, segOut_length, pLen18]
    norm_num
  · simp only [readTrace6, List.length_cons, List.length_map, length_walk, length_lens18]
    norm_num
  · intro e he
    simp only [readTrace6, List.mem_cons, List.mem_map] at he
    rcases he with rfl | ⟨x, hx, rfl⟩
    · simp only [q0Ent, bArr_size, List.length_drop, wordBytes, enc64_length]
      norm_num
    · have := (lensOK18 _ (walk_snd_mem _ _ x hx)).2
      simp only [entAt, bArr_size, wordsBytes_length, length_wsAt]
      omega

/-! ## `hdrTape6` -/

theorem ofLE_take (l : List UInt8) : ∀ n, ofLE (l.take n) = ∑ i ∈ Finset.range n, (l.getD i 0).toNat * 256 ^ i := by
  induction l with
  | nil => intro n; simp [ofLE]
  | cons a r ih =>
    intro n
    cases n with
    | zero => simp [ofLE]
    | succ n =>
      rw [List.take_succ_cons, Finset.sum_range_succ', ofLE, List.foldr_cons, ← ofLE, ih n, Finset.mul_sum]
      simp only [List.getD_cons_succ, List.getD_cons_zero, pow_zero, mul_one, pow_succ]
      rw [add_comm]
      congr 1
      exact Finset.sum_congr rfl fun i _ => by ring

theorem getD_drop' (l : List UInt8) (m k : ℕ) : (l.drop m).getD k 0 = l.getD (m + k) 0 := by
  simp only [List.getD_eq_getElem?_getD, List.getElem?_drop]

theorem getD_take' (l : List UInt8) {n k : ℕ} (h : k < n) : (l.take n).getD k 0 = l.getD k 0 := by
  simp only [List.getD_eq_getElem?_getD, List.getElem?_take, h, ite_true]

/-- Word `j` of packed bytes. -/
theorem packBytes_getElem (l : List UInt8) (j : ℕ) (hj : j < (packBytes l).length) :
    (packBytes l)[j] = toWord (∑ i ∈ Finset.range 8, (l.getD (8 * j + i) 0).toNat * 256 ^ i) := by
  simp only [packBytes, List.getElem_map, List.getElem_range, ofLE_take, getD_drop']

theorem toNat_rdU64' (x : List UInt8) (o : ℕ) :
    (rdU64 x o).toNat = ∑ i ∈ Finset.range 8, (x.getD (o + i) 0).toNat * 256 ^ i := by
  show (Lvm.FS.kOfBytes (x.drop o)).toBitVec.toNat = _
  rw [Lvm.VEq.toNat_kOfBytes, Fin.sum_univ_eq_sum_range (fun i => ((x.drop o).getD i 0).toNat * 256 ^ i)]
  exact Finset.sum_congr rfl fun i _ => by rw [getD_drop']

section Tape

variable {c : Digest} {π : Proof} {L : Log} {H j : ℕ}

/-- Tape word `5 + j` of a proof of at least `8 (j + 1)` bytes is its packed word `j`. -/
theorem tape_word (hH : 8 * (j + 1) ≤ π.size) :
    (extractorInput c π L).toArray.getD (5 + j) 0 =
      toWord (∑ i ∈ Finset.range 8, (π.data.toList.getD (8 * j + i) 0).toNat * 256 ^ i) := by
  have hj : j < (π.size + 7) / 8 := by omega
  rw [getD_toArray, tape_getD_proof c π L hj, packBytes_getElem]

/-- A `u64` header field at a word-aligned offset is its tape word. -/
theorem tape_u64 {o : ℕ} (ho : o % 8 = 0) (hoH : o + 8 ≤ H) (hH : H ≤ π.size) :
    (extractorInput c π L).toArray.getD (5 + o / 8) 0 = toWord (rdU64 (π.data.toList.take H) o).toNat := by
  rw [tape_word (by omega), toNat_rdU64']
  congr 1
  refine Finset.sum_congr rfl fun i hi => ?_
  rw [Finset.mem_range] at hi
  rw [getD_take' _ (by omega), show 8 * (o / 8) + i = o + i by omega]

/-- A digest's bytes. -/
theorem getD_rdD (x : List UInt8) (o : ℕ) {k : ℕ} (hk : k < 32) : (rdD x o).toList.getD k 0 = x.getD (o + k) 0 := by
  rw [rdD, Lvm.FS.dg, Vector.toList_ofFn, List.getD_eq_getElem?_getD, List.getElem?_ofFn]
  simp only [hk, dite_true, Option.getD_some]
  rw [getD_drop']

/-- A digest header field at a word-aligned offset is four tape words. -/
theorem tape_digest {o : ℕ} (ho : o % 8 = 0) (hoH : o + 32 ≤ H) (hH : H ≤ π.size) {i : ℕ} (hi : i < 4) :
    (extractorInput c π L).toArray.getD (5 + o / 8 + i) 0 =
      (packBytes (rdD (π.data.toList.take H) o).toList).getD i 0 := by
  have hl : (rdD (π.data.toList.take H) o).toList.length = 32 := by simp
  have hp : i < (packBytes (rdD (π.data.toList.take H) o).toList).length := by rw [packBytes_length, hl]; omega
  rw [List.getD_eq_getElem _ _ hp, packBytes_getElem, show 5 + o / 8 + i = 5 + (o / 8 + i) by omega,
    tape_word (by omega)]
  refine congrArg toWord (Finset.sum_congr rfl fun k hk => ?_)
  rw [Finset.mem_range] at hk
  rw [getD_rdD _ _ (by omega), getD_take' _ (by omega), show 8 * (o / 8 + i) + k = o + (8 * i + k) by omega]

end Tape

/-- The header bytes `Ex` replays are the first `hdrLen` bytes of the proof. -/
theorem Ex_hdr {prog : Shape → Digest → List UInt8 → LeanVM.Protocol.Compile.VerifierProgram Bool} {vk : Digest}
    {c : Digest} {π : Proof} {L : Log} {x : List UInt8} {h : List LeanVM.Protocol.Compile.Ev}
    (hE : (schemeOf prog P18 vk).Ex (fun _ x h => (x, h)) c π L = some (x, h)) :
    x = π.data.toList.take (V.hdrLen (toV P18)) ∧ V.hdrLen (toV P18) ≤ π.size := by
  unfold Scheme.Ex at hE
  have hh : (schemeOf prog P18 vk).hdr π = V.hdr6 (toV P18) π := rfl
  rw [hh] at hE
  by_cases hs : V.hdrLen (toV P18) ≤ π.size
  · rw [V.hdr6, if_pos hs] at hE
    refine ⟨?_, hs⟩
    try dsimp only at hE
    split_ifs at hE
    obtain ⟨e₀, -, hE⟩ := Option.bind_eq_some_iff.mp hE
    obtain ⟨e₁, -, hE⟩ := Option.bind_eq_some_iff.mp hE
    obtain ⟨r, -, hr⟩ := Option.bind_eq_some_iff.mp hE
    split_ifs at hr
    cases hr
    rfl
  · rw [V.hdr6, if_neg hs] at hE
    cases hE

/-- **`hdrTape6`**: the replayed header's fields are on the tape. -/
theorem hdrTape6 {prog : Shape → Digest → List UInt8 → LeanVM.Protocol.Compile.VerifierProgram Bool} {vk : Digest}
    (c : Digest) (π : Proof) (L : Log) (x : List UInt8) (h : List LeanVM.Protocol.Compile.Ev)
    (hE : (schemeOf prog P18 vk).Ex (fun _ x h => (x, h)) c π L = some (x, h)) :
    HdrTape (extractorInput c π L).toArray (hdrView P18 x) := by
  obtain ⟨rfl, hH⟩ := Ex_hdr hE
  have h136 : 136 ≤ V.hdrLen (toV P18) := by simp only [V.hdrLen]; omega
  refine ⟨?_, ?_, fun i hi => ?_, ?_⟩
  · exact tape_u64 (o := 8) (by norm_num) (by omega) hH
  · exact tape_u64 (o := 16) (by norm_num) (by omega) hH
  · exact tape_digest (o := 24) (by norm_num) (by omega) hH hi
  · have hl : (packBytes (hdrView P18 (π.data.toList.take (V.hdrLen (toV P18)))).c'.toList).length = 4 := by
      rw [packBytes_length, Vector.length_toList]
    refine List.ext_getElem (by rw [List.length_map, List.length_range, hl]) fun i h1 h2 => ?_
    rw [List.getElem_map, List.getElem_range, ← List.getD_eq_getElem _ 0 h2]
    exact tape_digest (o := 56) (by norm_num) (by omega) hH (by simpa using h1)

/-- **`SFront6` from its three non-pure fields**: `childFits6` and `hdrTape6` fill the pure ones. -/
theorem SFront6.ofOpen {prog : Shape → Digest → List UInt8 → LeanVM.Protocol.Compile.VerifierProgram Bool}
    {vk : Digest} {R : Digest → Wit → Prop} {K : KCert (schemeOf prog P18 vk) R} {I : OpeningIface} {descX : XIR}
    {G : List UInt8 → List LeanVM.Protocol.Compile.Ev → Prop}
    (len : ∀ c π L, Avail K c π L → π.size = pz6)
    (goodL : ∀ c π L, Avail K c π L → ∀ x h, (schemeOf prog P18 vk).Ex (fun _ x h => (x, h)) c π L = some (x, h) →
      G x h)
    (descends : ∀ c π L x h, (schemeOf prog P18 vk).Ex (fun _ x h => (x, h)) c π L = some (x, h) →
      π.size = pz6 → G x h → Inv (preOut6 descX (extractorInput c π L)).M ∧
        (preOut6 descX (extractorInput c π L)).o = #[] ∧
        HeapHolds (preOut6 descX (extractorInput c π L)).M (pick6 I h)) :
    SFront6 K I descX G :=
  ⟨len, fun c π L x h hE => hdrTape6 c π L x h hE, childFits6, goodL, descends⟩

end Lvm6.X
