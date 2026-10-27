-- New for `flock-recursive` (BLUEPRINT A.7, A.10; stage S-G1g).
import FRSoundnessHide
import FRLeafCircuit
import FRRingSwitch

/-!
# The PIOP truths over the decoded witness (A.10), part 1: `f⁽⁰⁾` in F, `z = unpack f⁽⁰⁾`

* **Part A: the level-0 message in F.** The committed word is F-valued, so each decoded row of a
  close word is `Enc_K` of an F-message (`interp_F_D` on the joint agreement set, which has
  `n₀ − e₀ ≥ k₀` positions). **`fF`** is A.10's `f⁽⁰⁾` in F (`f[e] = fTab … 0 e`, row bits first,
  A.7's element order); **`fTab_F`**: on a close level-0 word, `fTab … 0 = ι ∘ fF`.
* **Part B: the witness bits.** **`zW`**: `z = unpack f⁽⁰⁾` (A.7's pack map: bit `128e + k` of
  `z` is bit `k` of `f[e]`, `FRRingSwitch.unpack`); **`zBlk blk`** is block `blk`'s 2^14
  positions (element `k` of block `blk` is `f[blk·128 + k]`). **`zBlk_bool`**: the bits are
  Boolean by construction (`unpack_boolean`), which is `leaf_sound`'s `hbool`.
* **Part C: the Z truth and B′.** **`truthZ tgt nb`**: every used block satisfies its kind's block
  R1CS with its public target (`HoldsE`, A.10 Z1's identity `(A₀z)(B₀z) = z + E` per block).
  **`leaf_of_truthZ`**: with the chain links (S's truth), `leaf_sound` gives `chainEnd s n = h`.
  **`truthB'`** (A.10 B′, parametric in the cell list while S-E3 changes `pubVals`): `v*` is the
  batched true value with the cells' true values `f[cell_k]`.

The other PIOP truths (L, S, Lr, RS, E) and their handoffs are not built here (S-G1g RESULT).
-/

namespace FR.Snd
open RecursionFast FR.Merkle Finset

/-! ## Part A: the level-0 message in F -/

/-- **A.10's `f⁽⁰⁾` in F**: element `e` is the constant coefficient of the decoded level-0
message's element `e` (`fTab`, row bits first). -/
noncomputable def fF (κ : Kind) (L es : Log) (e : ℕ) : F := (fTab κ L es 0 e).f₀

theorem algebraMap_f₀ (c : F) : (algebraMap F K c).f₀ = c := rfl

/-- **A close level-0 word decodes to F-messages** (`interp_F_D`): every decoded row's message is
F-valued. -/
theorem msgOf_F {κ : Kind} {L es : Log} (hfar : ¬ farL κ L es 0) (r x : ℕ) :
    msgOf κ L es 0 r x = algebraMap F K (msgOf κ L es 0 r x).f₀ := by
  by_cases hr : r < (lvl κ 0).rows
  swap
  · simp only [msgOf, hr, dite_false]; rfl
  by_cases hx : x < 2 ^ mLog κ 0
  swap
  · simp only [msgOf, hr, hx, dite_true, dite_false]; rfl
  obtain ⟨hek, hN, -, hk, hn⟩ := lv_params κ (i := 0) (by norm_num)
  have hkN : 2 ^ mLog κ 0 ≤ nMax := by rw [← hk]; unfold lvK; exact (Nat.div_le_self _ _).trans hN
  have hnN : 2 ^ (lvl κ 0).logN ≤ nMax := hn ▸ hN
  obtain ⟨hV, hJ⟩ := decodeL_spec hfar
  set rr : Fin (lvl κ 0).rows := ⟨r, hr⟩
  have hv := hV rr
  rw [codeK, hk, ← encCode_D hkN] at hv
  have hA : 2 ^ mLog κ 0 ≤ (jointAgree (wordK κ L es 0) (decodeL κ L es 0)).card := by
    have : lvK κ 0 ≤ 2 ^ (lvl κ 0).logN - lvE κ 0 := by rw [← hn]; omega
    rw [← hk]; exact this.trans hJ
  obtain ⟨c, hc⟩ := interp_F_D hnN hkN hv (fun j => wordOf κ L es 0 rr j) _ hA fun j hj => by
    rw [mem_jointAgree] at hj; rw [← hj rr]; rfl
  have := msgOf_eq (i := 0) (by norm_num) (r := rr) hc.symm ⟨x, hx⟩
  rw [this, algebraMap_f₀]

/-- **`f⁽⁰⁾` is F-valued**: on a close level-0 word, `fTab … 0 = ι ∘ fF`. -/
theorem fTab_F {κ : Kind} {L es : Log} (hfar : ¬ farL κ L es 0) (e : ℕ) :
    fTab κ L es 0 e = algebraMap F K (fF κ L es e) := msgOf_F hfar _ _

/-! ## Part B: the witness bits `z = unpack f⁽⁰⁾` -/

/-- **A.10's `z := unpack f⁽⁰⁾`** (A.7's pack map): bit `b` of `z` is bit `b mod 128` of
`f[b / 128]`. -/
noncomputable def zW (κ : Kind) (L es : Log) (b : ℕ) : F :=
  unpack (fF κ L es (b / 128)) ⟨b % 128, Nat.mod_lt _ (by norm_num)⟩

/-- Block `blk`'s positions (A.7: block element `k` is `f[blk·128 + k]`, `2^14` bits). -/
noncomputable def zBlk (κ : Kind) (L es : Log) (blk : ℕ) : Block.Pos → F :=
  fun k => zW κ L es (blk * 2 ^ Blake2sCircuit.m + k.val)

/-- Block `blk`'s element `k` is `f[blk·128 + k]`: its bits are positions `128k … 128k + 127`. -/
theorem zBlk_elem (κ : Kind) (L es : Log) (blk : ℕ) (k : Block.Pos) :
    zBlk κ L es blk k = unpack (fF κ L es (blk * 128 + k.val / 128))
      ⟨k.val % 128, Nat.mod_lt _ (by norm_num)⟩ := by
  have hm : (2 : ℕ) ^ Blake2sCircuit.m = 128 * 128 := by decide
  have h1 : (blk * (128 * 128) + k.val) / 128 = blk * 128 + k.val / 128 := by omega
  have h2 : (blk * (128 * 128) + k.val) % 128 = k.val % 128 := by omega
  simp only [zBlk, zW, hm, h1, h2]

/-- **The unpacked witness is Boolean** (`leaf_sound`'s `hbool`). -/
theorem zBlk_bool (κ : Kind) (L es : Log) (blk : ℕ) (k : Block.Pos) :
    BlockR1CS.IsBool (zBlk κ L es blk k) :=
  unpack_boolean _ _

/-! ## Part C: the Z truth, the leaf, and B′ -/

/-- **The Z truth** (A.10 Z1, per block): each of the `nb` used blocks satisfies its kind's block
R1CS with its public target, `(A₀z)·(B₀z) = z + E` (`HoldsE`). -/
def truthZ (tgt : ℕ → Block.Target) (nb : ℕ) (κ : Kind) (L es : Log) : Prop :=
  ∀ blk < nb, Block.HoldsE (Block.blockR1CS (tgt blk)) (Block.targetVal F (tgt blk))
    (zBlk κ L es blk)

/-- **From the leaf's truths to the leaf's statement**: the Z truth with every block a chain block
and the chain links of the decoded witness give `chainEnd s n = h` (`leaf_sound` over F). -/
theorem leaf_of_truthZ {κ : Kind} {L es : Log} {n : ℕ} (hn : 1 ≤ n) {s h : Digest}
    (hZ : truthZ (fun _ => Chain.chainTarget) n κ L es)
    (hlinks : Leaf.ChainLinks n (zBlk κ L es) s h) : chainEnd s n = h :=
  Leaf.leaf_sound hn (zBlk κ L es) s h (fun i _ k => zBlk_bool κ L es i k) hZ hlinks

/-- **The B′ truth** (A.10 B′; `finB′`'s `v*`): the batched value is `v_RS + κ′·v_E +
Σ_k κ′^(k+2)·f[cell_k]` with the true values `vRS`, `vE` and the cells' true values. Parametric
in the cell list: A.7's nine cells are `Node.pubCells []` once S-E3 drops the padding cells. -/
def truthB' (κ : Kind) (L es : Log) (cells : List ℕ) (κ' vRS vE vStar : F) : Prop :=
  vStar = vRS + κ' * vE +
    ∑ k ∈ range cells.length, κ' ^ (k + 2) * fF κ L es (cells.getD k 0)

/-- Control (positive): the B′ truth holds at its own batched value. -/
theorem truthB'_self (κ : Kind) (L es : Log) (cells : List ℕ) (κ' vRS vE : F) :
    truthB' κ L es cells κ' vRS vE (vRS + κ' * vE +
      ∑ k ∈ range cells.length, κ' ^ (k + 2) * fF κ L es (cells.getD k 0)) := rfl

/-- Control (negative): with no cells, a wrong batched value fails the B′ truth. -/
theorem not_truthB'_of_ne (κ : Kind) (L es : Log) {κ' vRS vE v : F}
    (h : v ≠ vRS + κ' * vE) : ¬ truthB' κ L es [] κ' vRS vE v := by
  simpa [truthB'] using h

end FR.Snd
