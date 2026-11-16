-- New for lvm2 roll 11 (M′, R11-X): the shipped advice decoders' correctness (`LvmXDec.decodeRec_correct`,
-- `LvmXDecUd.decodeRec_of_mem`, `LvmXDec1.decodeRec1_correct`, `LvmXDec1Ud.decodeRec1_of_ud`) generalised from
-- their literals (`2^15`, `2^13`, `2^12`, `2^9`, `nLog = 15`) to any shape. Imported by `LvmMPDec`, which
-- instantiates it at `C_rec`'s and `C_main`'s shapes.
import LvmXDec1Ud
import LvmXDecUd

/-!
# The advice decoders' correctness, generic in the shape

The statements speak of the decoders' bodies, written with the shipped shape-free pieces (`foldAt`,
`fold1At`, `rowW`, `row1`, `lane1`, `nbAt`, `interpF`, `coeffsAt`): `LvmMPDec`'s generic decoders
(`decodeG0`, `decode1G`) unfold to them.

* `coeffs_interp_take`: interpolation on the first `2^kL` positions of a duplicate-free list on which a lane is
  a codeword of `2^kL` coefficients, then the inverse NTT (`coeffsAt ptK N kL 0`, `kL ≤ N ≤ 64`), returns the
  coefficients (`decode_row`).
* Level 0 (64 `K` lanes of `2^kL` words): **`dec0Body_of_mem`**, for a candidate `q` of the root word of a
  `μ`-variable stack at `R` (positions `2^(μ − 6 + R)`, lanes of `2^(μ − 6)`), any NTT bound `N`, any window
  `[lo, lo + C) ⊆ [0, 64)`.
* Levels ≥ 1 (16 `E` rows of a `LevelCode` `P`): **`dec1Body_of_mem`**, for a member `V` of `P`'s list.
-/

namespace Lvm.X

open Finset Lvm.Nb CompPoly.Extension BF64 LeanVM.Parameters LeanVM.Protocol LeanVM.Protocol.Compile
  LeanVM.Protocol.Whir LeanVM.Protocol.Whir.Ud LeanVM.Protocol.Whir.Sound LeanVM.Protocol.EndToEnd

/-! ## Interpolating one lane -/

/-- **One lane decodes**: on the first `2^kL` members of a duplicate-free list of positions below `2^64` where
`y` is `Enc` of the coefficients `c`, interpolation and the inverse NTT return `c`. -/
theorem coeffs_interp_take {N kL : ℕ} (hk : kL ≤ N) (hN : N ≤ 64) {L : List ℕ} (hnd : L.Nodup)
    (hlt : ∀ q ∈ L, q < 2 ^ 64) (hlen : 2 ^ kL ≤ L.length) (y c : ℕ → BF64)
    (hy : ∀ q ∈ L, y q = ∑ v ∈ range (2 ^ kL), c v * nbAt v q) {v : ℕ} (hv : v < 2 ^ kL) :
    coeffsAt ptK N kL 0 (interpF ptK (L.take (2 ^ kL)).toFinset y) v = c v := by
  set J := (L.take (2 ^ kL)).toFinset with hJ
  have hJsub : ∀ q ∈ J, q ∈ L := fun q hq => List.mem_of_mem_take (List.mem_toFinset.1 hq)
  have hJcard : J.card = 2 ^ kL := by
    rw [hJ, List.toFinset_card_of_nodup (hnd.sublist (List.take_sublist _ _)), List.length_take,
      Nat.min_eq_left hlen]
  have hrow : ∀ q ∈ J, y q = encN ptK (fun x : Fin (2 ^ kL) => c x) q := fun q hq => by
    rw [hy q (hJsub q hq), encN, ← Fin.sum_univ_eq_sum_range (fun v => c v * nbAt v q)]
    rfl
  have hdec := decode_row ptK_xor (ptK_injOn hN) hk
    (fun a ha b hb h => ptK_injOn64 (hlt a (hJsub a ha)) (hlt b (hJsub b hb)) h) hJcard _ y hrow
  have := congrFun hdec ⟨v, hv⟩
  simpa only [coeffsOfValues] using this

/-- A filtered `range (2^n)` is duplicate-free. -/
theorem nodup_filter_range (n : ℕ) (p : ℕ → Bool) : ((List.range (2 ^ n)).filter p).Nodup :=
  List.nodup_range.filter _

/-- A finite set of positions below `2^n` satisfying `p` is no larger than the filtered range. -/
theorem card_le_length_filter_range {n : ℕ} {p : ℕ → Bool} (S : Finset ℕ)
    (hS : ∀ q ∈ S, q < 2 ^ n ∧ p q = true) : S.card ≤ ((List.range (2 ^ n)).filter p).length := by
  have hsub : S ⊆ ((List.range (2 ^ n)).filter p).toFinset := fun q hq => by
    rw [List.mem_toFinset, List.mem_filter, List.mem_range]; exact hS q hq
  exact (card_le_card hsub).trans (List.toFinset_card_le _)

/-! ## Level 0: the pure decoder body -/

/-- **The level-0 decoder body** (64 `K` lanes of `2^kL` coefficients, window `[lo, lo + C)`): on a list of at
least `2^kL` duplicate-free positions below `2^64` where every lane is `Enc` of `msg`'s lane, the decoded words of
the window are `msg`'s. -/
theorem dec0Body_eq {N kL lo C : ℕ} (hk : kL ≤ N) (hN : N ≤ 64) (hC : lo + C ≤ 64)
    (wd : ℕ → ℕ → BF64) (msg : ℕ → BF64) {L : List ℕ} (hnd : L.Nodup) (hlt : ∀ q ∈ L, q < 2 ^ 64)
    (hlen : 2 ^ kL ≤ L.length)
    (hrow : ∀ q ∈ L, ∀ l < 64, rowW wd l q = ∑ v ∈ range (2 ^ kL), msg (l * 2 ^ kL + v) * nbAt v q) :
    ((List.range (C * 2 ^ kL)).map fun i =>
        coeffsAt ptK N kL 0 (interpF ptK (L.take (2 ^ kL)).toFinset (rowW wd ((lo * 2 ^ kL + i) / 2 ^ kL)))
          ((lo * 2 ^ kL + i) % 2 ^ kL)) =
      (List.range (C * 2 ^ kL)).map fun i => msg (lo * 2 ^ kL + i) := by
  refine List.map_congr_left fun i hi => ?_
  have hi' := List.mem_range.1 hi
  have hp : 0 < 2 ^ kL := by positivity
  set j := lo * 2 ^ kL + i with hj
  have hl : j / 2 ^ kL < 64 := by
    rw [Nat.div_lt_iff_lt_mul hp]
    calc j < lo * 2 ^ kL + C * 2 ^ kL := by omega
      _ = (lo + C) * 2 ^ kL := by ring
      _ ≤ 64 * 2 ^ kL := Nat.mul_le_mul_right _ hC
  rw [coeffs_interp_take hk hN hnd hlt hlen _ (fun v => msg (j / 2 ^ kL * 2 ^ kL + v))
    (fun q hq => hrow q hq _ hl) (Nat.mod_lt _ hp)]
  show msg (j / 2 ^ kL * 2 ^ kL + j % 2 ^ kL) = msg j
  rw [Nat.div_add_mod' j (2 ^ kL)]

/-! ## Level 0: the bridges, generic in `μ`, `R` -/

/-- **Lane `u` is leaf word `63 − ⟨u⟩`** (any shape). -/
theorem laneRows_eqG {μ R : ℕ} (W : Compile.Word) (hW : ∀ v < 2 ^ (μ - laneBits + R), (W v).length = 64)
    (u : Fin laneBits → Bool) (x : Fin (2 ^ (μ - laneBits + R))) :
    laneRows μ R W u x = ofK (rowW (wdOf W) (bitsToNat u) x) := by
  rw [laneRows, laneWord, laneOf, bitsEquiv_val, rowW, wdOf, ofK_eq,
    getD_reverse64 (hW x x.isLt) (bitsToNat_lt u)]

/-- **`q`'s lane encoding is `Enc` of its lane** (any shape). -/
theorem encRows_eqG {μ R : ℕ} (h64 : μ - laneBits + R ≤ 64) (q : Column μ) (u : Fin laneBits → Bool)
    (x : Fin (2 ^ (μ - laneBits + R))) :
    encRows μ R q u x = ofK (∑ v ∈ range (2 ^ (μ - laneBits)),
      q.values.getD (bitsToNat u * 2 ^ (μ - laneBits) + v) 0 * nbAt v x) := by
  rw [encRows, enc_apply, Lvm.X.ofK, map_sum,
    ← sum_cube (μ - laneBits) (fun v => algebraMap BF64 Ext3
      (q.values.getD (bitsToNat u * 2 ^ (μ - laneBits) + v) 0 * nbAt v x))]
  refine Finset.sum_congr rfl fun y _ => ?_
  have hy : bitsToNat y < 2 ^ 64 :=
    (bitsToNat_lt y).trans_le (Nat.pow_le_pow_right (by norm_num) (by omega))
  rw [blockOf, bitsEquiv_val, map_mul, nbAt_eq_novelAt hy, ← Lvm.X.ofK, ← Lvm.X.ofK, ofK_eq, ofK_eq]
  rw [show bitsToNat y + 2 ^ (μ - laneBits) * bitsToNat u = bitsToNat u * 2 ^ (μ - laneBits) + bitsToNat y
    by ring]

/-- **The fold of the lanes is `foldAt`** (any shape). -/
theorem foldAll_laneRows_eqG {μ R : ℕ} (W : Compile.Word)
    (hW : ∀ v < 2 ^ (μ - laneBits + R), (W v).length = 64) (α : Fin laneBits → E) (r : Fin 0 → Bool)
    (x : Fin (2 ^ (μ - laneBits + R))) :
    foldAll α (laneRows μ R W) r x = foldAt (alphaN α) (wdOf W) x := by
  rw [foldAll_eq_sum, foldAt, ← cube_sum64 (fun l => eqA (alphaN α) l * ofK (rowW (wdOf W) l x))]
  refine Finset.sum_congr rfl fun u _ => ?_
  rw [laneRows_eqG W hW, eqW_eq_eqA]

/-- **`Enc(f)` is the sum against the novel basis** of any `ℕ`-indexing `g` of `f`'s coefficients. -/
theorem enc_eq_sumG {κ R : ℕ} (h64 : κ + R ≤ 64) (f : (Fin κ → Bool) → E) (g : ℕ → Ext3)
    (hg : ∀ w, g (bitsToNat w) = f w) (x : Fin (2 ^ (κ + R))) :
    enc κ R f x = ∑ v ∈ range (2 ^ κ), g v * ofK (nbAt v x) := by
  rw [enc_apply, ← sum_cube κ (fun v => g v * ofK (nbAt v x))]
  refine Finset.sum_congr rfl fun u _ => ?_
  rw [nbAt_eq_novelAt ((bitsToNat_lt u).trans_le (Nat.pow_le_pow_right (by norm_num) (by omega))), ofK_eq,
    hg]

/-- The cube point of index `v < 2^κ` reads back `v`. -/
theorem bitsToNat_symm {κ v : ℕ} (hv : v < 2 ^ κ) : bitsToNat ((bitsEquiv κ).symm ⟨v, hv⟩) = v := by
  rw [← bitsEquiv_val, Equiv.apply_symm_apply]

/-- **The residual is the fold of `q`'s lanes** (any shape). -/
theorem foldMsg_eqG {μ : ℕ} (α : Fin laneBits → E) (q : Column μ) (g : ℕ → Ext3)
    (hg : ∀ w, g (bitsToNat w) = foldMsg α q w) {v : ℕ} (hv : v < 2 ^ (μ - laneBits)) :
    g v = ∑ l ∈ range 64, eqA (alphaN α) l * ofK (q.values.getD (l * 2 ^ (μ - laneBits) + v) 0) := by
  rw [← bitsToNat_symm hv, hg, foldMsg, Finset.sum_apply, bitsToNat_symm hv]
  rw [← cube_sum64 (fun l => eqA (alphaN α) l * ofK (q.values.getD (l * 2 ^ (μ - laneBits) + v) 0))]
  refine Finset.sum_congr rfl fun u _ => ?_
  rw [Pi.smul_apply, smul_eq_mul, eqW_eq_eqA, blockOf, bitsEquiv_val, ofK_eq, bitsToNat_symm hv]
  rw [show v + 2 ^ (μ - laneBits) * bitsToNat u = bitsToNat u * 2 ^ (μ - laneBits) + v by ring]

/-- **Level 0 for a candidate** (generic `decodeRec_of_mem`): for a candidate `q` of the root word at `A ≥
2^(μ − 6)`, off the luck event, the agreement list of the fold with `Enc` of `q`'s fold (`g` any `ℕ`-indexing of
`foldMsg α q`) has at least `2^(μ − 6)` positions, and on it every lane is `Enc` of `q`'s lane. -/
theorem agree0_of_mem {μ R : ℕ} (h64 : μ - laneBits + R ≤ 64) (W : Compile.Word) (α : Fin laneBits → E)
    (q : Column μ) {A : ℕ} (hW : ∀ v < 2 ^ (μ - laneBits + R), (W v).length = 64)
    (hq : q ∈ Candidates μ R A W) (hA : 2 ^ (μ - laneBits) ≤ A)
    (hL : ¬ FoldAllLuck α (laneRows μ R W) (encRows μ R q)) (g : ℕ → Ext3)
    (hg : ∀ w, g (bitsToNat w) = foldMsg α q w) :
    2 ^ (μ - laneBits) ≤ ((List.range (2 ^ (μ - laneBits + R))).filter fun x =>
        decide (foldAt (alphaN α) (wdOf W) x = ∑ v ∈ range (2 ^ (μ - laneBits)), g v * ofK (nbAt v x))).length ∧
      ∀ x ∈ (List.range (2 ^ (μ - laneBits + R))).filter (fun x =>
        decide (foldAt (alphaN α) (wdOf W) x = ∑ v ∈ range (2 ^ (μ - laneBits)), g v * ofK (nbAt v x))),
        ∀ l < 64, rowW (wdOf W) l x =
          ∑ v ∈ range (2 ^ (μ - laneBits)), q.values.getD (l * 2 ^ (μ - laneBits) + v) 0 * nbAt v x := by
  classical
  set κ := μ - laneBits with hκ
  have hcard := card_agreeSet_of_candidate h64 hq
  have hluck : agreeSet (foldAll α (laneRows μ R W)) (fun _ ↦ enc κ R (foldMsg α q)) =
      agreeSet (laneRows μ R W) (encRows μ R q) := by
    rw [← foldAll_encRows]; exact agreeSet_foldAll_eq (not_not.mp hL)
  -- the codeword's lanes
  have hfx : ∀ x : Fin (2 ^ (κ + R)),
      x ∈ agreeSet (laneRows μ R W) (encRows μ R q) ↔
        ∀ l < 64, rowW (wdOf W) l x =
          ∑ v ∈ range (2 ^ κ), q.values.getD (l * 2 ^ κ + v) 0 * nbAt v x := by
    intro x
    rw [mem_agreeSet]
    constructor
    · intro h l hl
      have := h ((bitsEquiv laneBits).symm ⟨l, hl⟩)
      rw [laneRows_eqG W hW, encRows_eqG h64, bitsToNat_symm hl] at this
      exact (algebraMap BF64 Ext3).injective this
    · intro h u
      rw [laneRows_eqG W hW, encRows_eqG h64, h _ (bitsToNat_lt u)]
  -- the fold's agreement with `Enc(g)` is the fold's agreement with `Enc(foldMsg α q)`
  have hfold : ∀ x : Fin (2 ^ (κ + R)),
      (foldAt (alphaN α) (wdOf W) x = ∑ v ∈ range (2 ^ κ), g v * ofK (nbAt v x)) ↔
        x ∈ agreeSet (foldAll α (laneRows μ R W)) (fun _ ↦ enc κ R (foldMsg α q)) := by
    intro x
    rw [mem_agreeSet, ← enc_eq_sumG h64 (foldMsg α q) g hg x]
    constructor
    · intro h r; rw [foldAll_laneRows_eqG W hW]; exact h
    · intro h; have := h (fun i => i.elim0); rwa [foldAll_laneRows_eqG W hW] at this
  have hlt : ∀ x, x < 2 ^ (κ + R) → x < 2 ^ 64 := fun x hx =>
    hx.trans_le (Nat.pow_le_pow_right (by norm_num) h64)
  refine ⟨?_, ?_⟩
  · refine hA.trans (hcard.trans ?_)
    refine le_trans ?_ (card_le_length_filter_range ((agreeSet (laneRows μ R W) (encRows μ R q)).map
      Fin.valEmbedding) ?_)
    · rw [card_map]
    · intro x hx
      obtain ⟨y, hy, rfl⟩ := Finset.mem_map.1 hx
      refine ⟨y.isLt, decide_eq_true ?_⟩
      rw [Fin.valEmbedding_apply, hfold, hluck]; exact hy
  · intro x hx
    rw [List.mem_filter, List.mem_range, decide_eq_true_iff] at hx
    have hmem := (hfold ⟨x, hx.1⟩).1 hx.2
    rw [hluck] at hmem
    exact (hfx ⟨x, hx.1⟩).1 hmem

/-- **The level-0 decoder body for a candidate** (generic in `μ`, `R`, the NTT bound `N`, the window): the
decoded words of lanes `[lo, lo + C)` are `q`'s. -/
theorem dec0Body_of_mem {μ R N lo C : ℕ} (h64 : μ - laneBits + R ≤ 64) (hk : μ - laneBits ≤ N) (hN : N ≤ 64)
    (hC : lo + C ≤ 64) (W : Compile.Word) (α : Fin laneBits → E) (q : Column μ) {A : ℕ}
    (hW : ∀ v < 2 ^ (μ - laneBits + R), (W v).length = 64) (hq : q ∈ Candidates μ R A W)
    (hA : 2 ^ (μ - laneBits) ≤ A) (hL : ¬ FoldAllLuck α (laneRows μ R W) (encRows μ R q)) (g : ℕ → Ext3)
    (hg : ∀ w, g (bitsToNat w) = foldMsg α q w) :
    (if 2 ^ (μ - laneBits) ≤ ((List.range (2 ^ (μ - laneBits + R))).filter fun x =>
        decide (foldAt (alphaN α) (wdOf W) x = ∑ v ∈ range (2 ^ (μ - laneBits)), g v * ofK (nbAt v x))).length
      then some ((List.range (C * 2 ^ (μ - laneBits))).map fun i =>
        coeffsAt ptK N (μ - laneBits) 0
          (interpF ptK (((List.range (2 ^ (μ - laneBits + R))).filter fun x =>
            decide (foldAt (alphaN α) (wdOf W) x =
              ∑ v ∈ range (2 ^ (μ - laneBits)), g v * ofK (nbAt v x))).take (2 ^ (μ - laneBits))).toFinset
            (rowW (wdOf W) ((lo * 2 ^ (μ - laneBits) + i) / 2 ^ (μ - laneBits))))
          ((lo * 2 ^ (μ - laneBits) + i) % 2 ^ (μ - laneBits)))
      else none) =
      some ((List.range (C * 2 ^ (μ - laneBits))).map fun i =>
        q.values.getD (lo * 2 ^ (μ - laneBits) + i) 0) := by
  obtain ⟨hlen, hrow⟩ := agree0_of_mem h64 W α q hW hq hA hL g hg
  rw [if_pos hlen]
  refine congrArg some (dec0Body_eq hk hN hC (wdOf W) (fun j => q.values.getD j 0)
    (nodup_filter_range _ _) ?_ hlen hrow)
  intro x hx
  rw [List.mem_filter, List.mem_range] at hx
  exact hx.1.trans_le (Nat.pow_le_pow_right (by norm_num) h64)

/-! ## Levels ≥ 1: the pure decoder body -/

/-- **The level-≥1 decoder body** (16 `E` rows of `2^kL` coefficients): on a list of at least `2^kL`
duplicate-free positions below `2^64` where every row is `Enc` of `msg`'s row, entry `i < 2^(kL+4)` of the
decoded message is `msg i`. -/
theorem dec1Body_eq {N kL : ℕ} (hk : kL ≤ N) (hN : N ≤ 64) (wd : ℕ → ℕ → BF64) (msg : ℕ → Ext3)
    {L : List ℕ} (hnd : L.Nodup) (hlt : ∀ q ∈ L, q < 2 ^ 64) (hlen : 2 ^ kL ≤ L.length)
    (hrow : ∀ q ∈ L, ∀ u < 16, row1 wd u q = ∑ v ∈ range (2 ^ kL), msg (u + 16 * v) * ofK (nbAt v q))
    {i : ℕ} (hi : i < 2 ^ (kL + 4)) :
    mkE (coeffsAt ptK N kL 0 (interpF ptK (L.take (2 ^ kL)).toFinset (lane1 wd (3 * (i % 16)))) (i / 16))
      (coeffsAt ptK N kL 0 (interpF ptK (L.take (2 ^ kL)).toFinset (lane1 wd (3 * (i % 16) + 1))) (i / 16))
      (coeffsAt ptK N kL 0 (interpF ptK (L.take (2 ^ kL)).toFinset (lane1 wd (3 * (i % 16) + 2))) (i / 16)) =
      msg i := by
  have hcoef : ∀ u < 16, ∀ c < 3, ∀ v < 2 ^ kL,
      coeffsAt ptK N kL 0 (interpF ptK (L.take (2 ^ kL)).toFinset (lane1 wd (3 * u + c))) v =
        limbN (msg (u + 16 * v)) c := by
    intro u hu c hc v hv
    refine coeffs_interp_take hk hN hnd hlt hlen _ (fun v => limbN (msg (u + 16 * v)) c) ?_ hv
    intro q hq
    have h := hrow q hq u hu
    have hcw : ∑ v ∈ range (2 ^ kL), msg (u + 16 * v) * ofK (nbAt v q) =
        mkE (∑ v ∈ range (2 ^ kL), limbN (msg (u + 16 * v)) 0 * nbAt v q)
          (∑ v ∈ range (2 ^ kL), limbN (msg (u + 16 * v)) 1 * nbAt v q)
          (∑ v ∈ range (2 ^ kL), limbN (msg (u + 16 * v)) 2 * nbAt v q) := by
      rw [← mkE_sum]
      refine sum_congr rfl fun v _ => ?_
      rw [← mkE_mul_ofK, mkE_limbN]
    rw [hcw, row1] at h
    obtain ⟨h0, h1, h2⟩ := mkE_inj h
    interval_cases c
    · exact h0
    · exact h1
    · exact h2
  have hu : i % 16 < 16 := Nat.mod_lt _ (by norm_num)
  have hv : i / 16 < 2 ^ kL := by
    rw [Nat.div_lt_iff_lt_mul (by norm_num)]; rw [pow_add] at hi; omega
  rw [show 3 * (i % 16) = 3 * (i % 16) + 0 from rfl, hcoef _ hu 0 (by norm_num) _ hv,
    hcoef _ hu 1 (by norm_num) _ hv, hcoef _ hu 2 (by norm_num) _ hv,
    show i % 16 + 16 * (i / 16) = i by omega, mkE_limbN]

/-! ## Levels ≥ 1: the bridges, generic in the code -/

/-- **The level rows are `row1` of the leaf words** (any code, leaves of 48 words). -/
theorem rows1_eqG (P : LevelCode) (W : Compile.Word) (hW : ∀ v < P.n, (W v).length = 48)
    (u : Fin 4 → Bool) (x : Fin P.n) :
    rows1 4 P.n W u x = row1 (wdOf W) (bitsToNat u) x := by
  rw [rows1, lanesOf, if_neg one_ne_zero, extRow_getD 16 (W x) (hW x x.isLt) _ (bitsToNat_lt u)]
  rfl

/-- **A codeword row is `Enc` of the message's row**, for any `msg` indexing `decode P V` as `⟨u⟩ + 16⟨w⟩`. -/
theorem enc_decode_sumG (P : LevelCode) (V : (Fin 4 → Bool) → Fin P.n → E)
    (hcw : IsInterleavedCodeword P.code V) (msg : ℕ → Ext3)
    (hmsg : ∀ u w, msg (bitsToNat u + 16 * bitsToNat w) = decode P V u w) (u : Fin 4 → Bool) (x : Fin P.n) :
    V u x = ∑ v ∈ range (2 ^ P.κ), msg (bitsToNat u + 16 * v) * ofK (nbAt v x) := by
  rw [← enc_decode P hcw u, enc_eq_sumG P.h64 _ (fun v => msg (bitsToNat u + 16 * v)) (fun w => hmsg u w)]

/-- **Levels ≥ 1 for a list member** (generic `decodeRec1_of_ud`): for `V` in `P`'s list of the word's rows at
`A ≥ 2^κ`, with `f` its fold by `α`, off the luck event, the agreement list of the fold with `Enc(f)` (`g` any
`ℕ`-indexing of `f`) has at least `2^κ` positions, and on it every row is `Enc` of the message's row (`msg` any
`ℕ`-indexing of `decode P V`, lane bits low). -/
theorem agree1_of_mem (P : LevelCode) (W : Compile.Word) (hW : ∀ v < P.n, (W v).length = 48)
    (α : Fin 4 → E) (f : (Fin P.κ → Bool) → E) (V : (Fin 4 → Bool) → Fin P.n → E)
    (hcw : IsInterleavedCodeword P.code V) {A : ℕ} (hA : 2 ^ P.κ ≤ A) (hcl : IsClose A (rows1 4 P.n W) V)
    (hf : f = ∑ u, eqW α u • decode P V u) (hL : ¬ FoldAllLuck α (rows1 4 P.n W) V) (g : ℕ → Ext3)
    (hg : ∀ w, g (bitsToNat w) = f w) (msg : ℕ → Ext3)
    (hmsg : ∀ u w, msg (bitsToNat u + 16 * bitsToNat w) = decode P V u w) :
    2 ^ P.κ ≤ ((List.range (2 ^ (P.κ + P.R))).filter fun x =>
        decide (fold1At (alphaN1 α) (wdOf W) x = ∑ v ∈ range (2 ^ P.κ), g v * ofK (nbAt v x))).length ∧
      ∀ x ∈ (List.range (2 ^ (P.κ + P.R))).filter (fun x =>
        decide (fold1At (alphaN1 α) (wdOf W) x = ∑ v ∈ range (2 ^ P.κ), g v * ofK (nbAt v x))),
        ∀ u < 16, row1 (wdOf W) u x = ∑ v ∈ range (2 ^ P.κ), msg (u + 16 * v) * ofK (nbAt v x) := by
  classical
  -- rows and codeword rows
  have hrow : ∀ x : Fin P.n, (∀ u, rows1 4 P.n W u x = V u x) →
      ∀ u' < 16, row1 (wdOf W) u' x = ∑ v ∈ range (2 ^ P.κ), msg (u' + 16 * v) * ofK (nbAt v x) := by
    intro x hx u' hu'
    have := hx ((bitsEquiv 4).symm ⟨u', hu'⟩)
    rw [rows1_eqG P W hW, enc_decode_sumG P V hcw msg hmsg, bitsToNat_symm hu'] at this
    exact this
  -- the fold of `V` is `Enc(f)`
  have hfoldV : ∀ x : Fin P.n, ∑ u, eqW α u * V u x = ∑ v ∈ range (2 ^ P.κ), g v * ofK (nbAt v x) := by
    intro x
    rw [← enc_eq_sumG P.h64 f g hg x, hf, enc_apply]
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Finset.sum_mul]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun u _ => ?_
    rw [← enc_decode P hcw u, enc_apply, Finset.mul_sum]
    exact Finset.sum_congr rfl fun w _ => by ring
  have hfold1 : ∀ x : Fin P.n, ∑ u, eqW α u * rows1 4 P.n W u x = fold1At (alphaN1 α) (wdOf W) x := by
    intro x
    rw [fold1At, ← cube_sum16 (fun l => eqA1 (alphaN1 α) l * row1 (wdOf W) l x)]
    refine Finset.sum_congr rfl fun u _ => ?_
    rw [rows1_eqG P W hW, eqW_eq_eqA1]
  refine ⟨?_, ?_⟩
  · have hthr := (isClose_iff_le_card_agreeSet _ _ _).mp hcl
    refine hA.trans (hthr.trans ?_)
    refine le_trans ?_ (card_le_length_filter_range ((agreeSet (rows1 4 P.n W) V).map
      Fin.valEmbedding) ?_)
    · rw [card_map]
    · intro x hx
      obtain ⟨y, hy, rfl⟩ := Finset.mem_map.1 hx
      refine ⟨y.isLt, decide_eq_true ?_⟩
      rw [mem_agreeSet] at hy
      rw [Fin.valEmbedding_apply, ← hfold1, ← hfoldV]
      exact Finset.sum_congr rfl fun u _ => by rw [hy u]
  · intro q hq u' hu'
    rw [List.mem_filter, List.mem_range, decide_eq_true_iff] at hq
    have hsub : agreeSet (foldAll α (rows1 4 P.n W)) (foldAll α V) ⊆ agreeSet (rows1 4 P.n W) V :=
      not_not.mp hL
    let x : Fin P.n := ⟨q, hq.1⟩
    have hx : x ∈ agreeSet (foldAll α (rows1 4 P.n W)) (foldAll α V) := by
      rw [mem_agreeSet]
      intro r
      rw [foldAll_eq_sum, foldAll_eq_sum, hfold1, hfoldV]
      exact hq.2
    have := hsub hx
    rw [mem_agreeSet] at this
    exact hrow x this u' hu'

/-- **The level-≥1 decoder body for a list member** (generic in the code `P` and the NTT bound `N`). -/
theorem dec1Body_of_mem {N : ℕ} (P : LevelCode) (hk : P.κ ≤ N) (hN : N ≤ 64) (W : Compile.Word)
    (hW : ∀ v < P.n, (W v).length = 48) (α : Fin 4 → E) (f : (Fin P.κ → Bool) → E)
    (V : (Fin 4 → Bool) → Fin P.n → E) (hcw : IsInterleavedCodeword P.code V) {A : ℕ} (hA : 2 ^ P.κ ≤ A)
    (hcl : IsClose A (rows1 4 P.n W) V) (hf : f = ∑ u, eqW α u • decode P V u)
    (hL : ¬ FoldAllLuck α (rows1 4 P.n W) V) (g : ℕ → Ext3) (hg : ∀ w, g (bitsToNat w) = f w)
    (msg : ℕ → Ext3) (hmsg : ∀ u w, msg (bitsToNat u + 16 * bitsToNat w) = decode P V u w)
    (hmsg0 : ∀ i, 2 ^ (P.κ + 4) ≤ i → msg i = 0) :
    (if 2 ^ P.κ ≤ ((List.range (2 ^ (P.κ + P.R))).filter fun x =>
        decide (fold1At (alphaN1 α) (wdOf W) x = ∑ v ∈ range (2 ^ P.κ), g v * ofK (nbAt v x))).length
      then some fun i => if i < 2 ^ (P.κ + 4) then
        mkE (coeffsAt ptK N P.κ 0 (interpF ptK (((List.range (2 ^ (P.κ + P.R))).filter fun x =>
            decide (fold1At (alphaN1 α) (wdOf W) x = ∑ v ∈ range (2 ^ P.κ), g v * ofK (nbAt v x))).take
              (2 ^ P.κ)).toFinset (lane1 (wdOf W) (3 * (i % 16)))) (i / 16))
          (coeffsAt ptK N P.κ 0 (interpF ptK (((List.range (2 ^ (P.κ + P.R))).filter fun x =>
            decide (fold1At (alphaN1 α) (wdOf W) x = ∑ v ∈ range (2 ^ P.κ), g v * ofK (nbAt v x))).take
              (2 ^ P.κ)).toFinset (lane1 (wdOf W) (3 * (i % 16) + 1))) (i / 16))
          (coeffsAt ptK N P.κ 0 (interpF ptK (((List.range (2 ^ (P.κ + P.R))).filter fun x =>
            decide (fold1At (alphaN1 α) (wdOf W) x = ∑ v ∈ range (2 ^ P.κ), g v * ofK (nbAt v x))).take
              (2 ^ P.κ)).toFinset (lane1 (wdOf W) (3 * (i % 16) + 2))) (i / 16))
        else 0
      else none) = some msg := by
  obtain ⟨hlen, hrow⟩ := agree1_of_mem P W hW α f V hcw hA hcl hf hL g hg msg hmsg
  rw [if_pos hlen]
  refine congrArg some (funext fun i => ?_)
  split_ifs with hi
  · refine dec1Body_eq hk hN (wdOf W) msg (nodup_filter_range _ _) ?_ hlen hrow hi
    intro x hx
    rw [List.mem_filter, List.mem_range] at hx
    exact hx.1.trans_le (Nat.pow_le_pow_right (by norm_num) P.h64)
  · exact (hmsg0 i (not_lt.1 hi)).symm

/-- **`joinMsg` read at `⟨u⟩ + 16⟨w⟩`** through `ℕ`-indexing (lane bits low). -/
theorem joinMsg_natAt {m κ : ℕ} (h : m = 4 + κ) (G : (Fin 4 → Bool) → (Fin κ → Bool) → E)
    (u : Fin 4 → Bool) (w : Fin κ → Bool) (hv : bitsToNat u + 16 * bitsToNat w < 2 ^ m) :
    joinMsg h G ((bitsEquiv m).symm ⟨bitsToNat u + 16 * bitsToNat w, hv⟩) = G u w := by
  subst h
  have happ : bitsToNat (Fin.append u w) = bitsToNat u + 16 * bitsToNat w := bitsToNat_append u w
  simp only [joinMsg]
  congr 1
  · funext i
    rw [bitsEquiv_symm_apply, Fin.val_cast, Fin.val_castAdd, Fin.val_mk, ← happ]
    have := testBit_bitsToNat (Fin.append u w) (Fin.castAdd _ i)
    rw [Fin.val_castAdd, Fin.append_left] at this
    exact this
  · funext i
    rw [bitsEquiv_symm_apply, Fin.val_cast, Fin.val_natAdd, Fin.val_mk, ← happ]
    have := testBit_bitsToNat (Fin.append u w) (Fin.natAdd 4 i)
    rw [Fin.val_natAdd, Fin.append_right] at this
    exact this

end Lvm.X
