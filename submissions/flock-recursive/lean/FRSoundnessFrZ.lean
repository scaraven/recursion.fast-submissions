-- New for `flock-recursive` (BLUEPRINT A.10 rows Z1–Zend, §5.2 rows Z1–Z3; stage S-G7).
-- RET-2: the declarations revision 4.1 reads moved to `FRSoundnessCoreRows`.
import FRSoundnessFrExt
import FRSoundnessFrPend
import FRSoundnessCoreRows

/-!
# Z: the block zerocheck with the univariate skip (positions 3 … 67)

Z proves that every block of `z = unpack f⁽⁰⁾` satisfies its kind's block R1CS with the public
target, `(A z)(B z) = z + E` (S-C's `BHolds`, `FRSpartan` part BZ). The witness is read as 64 skip
slices `σ` (the 6 low position bits) of tables over `ℓ = m − 6` variables `u`: `u mod 256` the 8
high position bits, `u / 256` the block. The kinds' matrices are a parameter **`ZLM`** (`Ak`, `Bk`
per block kind, the indicators `Ind`, the target bits `Et`); binding it to `truthZN`'s per-target
R1CS and to the verifier's `targetS`/`walkAB` specifications is a separate obligation (RESULT).

* **`ZHolds`** (the unit's statement), **`ZEnd`** (Z1's final doom: a residual slice's extension
  at Z1's point `r = (ρ₁ … ρ₇, Z1's m − 13 coordinates)` is nonzero), **`z1_hfin`** (`pinned_sound`
  for the 7 pinned coordinates, then one value per free coordinate: `≤ 19/2^128`).
* Z2 (absorb at 13, `λ` at 14): **`Z2D`** (`ZEnd` until `λ`, then **`Z2Bad`**: Z3's initial claim
  `P^{ab}*(λ)` or the c-claim `P^z*(λ)` is false), **`z2_habs`**, **`z2_single`**
  (`skip_pair_bad_le`: `126·2^128`).
* Z3 (rounds from 15): **`D3Z`** (`D3` over `bzTables`), **`z3_habs`** (into `D3Z`, or the pending
  c-claim **`PendZ`**), **`z3_single`** (`D3_single`: `3·2^128`).
* Zend (absorb at 67): **`RejZ`** (`relZ`'s first conjunct fails on the log), **`ZendBad`** (the
  pair `(â, b̂)` is not `(Â(λ, r′), B̂(λ, r′))`), **`zend_habs`**, **`rejZ_ok`**.
* The c-claim's binding **`oZ`** (`relZ`'s second conjunct: the RS claim-1 value is `P^z*(λ)`).
-/

namespace FR.Snd
open RecursionFast FR.Merkle Finset

set_option linter.constructorNameAsVariable false

noncomputable section

/-! ## The kinds' matrices (a parameter) -/

/-- The matrices, indicators and targets are bit-valued. -/
def ZLM.Bits (M : ZLM) : Prop :=
  (∀ j p k, IsBitF (M.Ak j p k)) ∧ (∀ j p k, IsBitF (M.Bk j p k)) ∧
    (∀ κ j t, IsBitF (M.Ind κ j t)) ∧ ∀ κ t p, IsBitF (M.Et κ t p)

/-! ## The slice tables -/

variable (M : ZLM)

/-- Block `t`'s bit `k`: `z[2^14·t + k]`. -/
def zBk (κ : Kind) (L es : Log) (t : ℕ) (k : Fin (2 ^ 14)) : F := zW κ L es (2 ^ 14 * t + k.val)

/-- `(A z)` at block `t`, position `p`: the block's kind's row. -/
def mvZ (A : Fin 9 → Fin (2 ^ 14) → Fin (2 ^ 14) → F) (κ : Kind) (L es : Log) (t : ℕ)
    (p : Fin (2 ^ 14)) : F :=
  ∑ j : Fin 9, M.Ind κ j t * ∑ k, A j p k * zBk κ L es t k

/-- The slice tables `a = A z`, `b = B z`, `z`, `E` (slice `σ`, `u`: position bits high, block). -/
def aZ (ℓ : ℕ) (κ : Kind) (L es : Log) : Fin 64 → Fin (2 ^ ℓ) → F :=
  fun σ u => mvZ M M.Ak κ L es (u.val / 256) (pAt σ u.val)
def bZ (ℓ : ℕ) (κ : Kind) (L es : Log) : Fin 64 → Fin (2 ^ ℓ) → F :=
  fun σ u => mvZ M M.Bk κ L es (u.val / 256) (pAt σ u.val)
def zZ (ℓ : ℕ) (κ : Kind) (L es : Log) : Fin 64 → Fin (2 ^ ℓ) → F :=
  fun σ u => zBk κ L es (u.val / 256) (pAt σ u.val)
def eZ (ℓ : ℕ) (κ : Kind) : Fin 64 → Fin (2 ^ ℓ) → F :=
  fun σ u => M.Et κ (u.val / 256) (pAt σ u.val)

/-- **Z's statement**: on the `2^(m−6)` slice points, `(A z)(B z) = z + E` (`BHolds`). -/
def ZHolds (L es : Log) : Prop :=
  BHolds (ℓ := mm 6 (kindOf es)) (aZ M _ (kindOf es) L es) (bZ M _ (kindOf es) L es)
    (zZ _ (kindOf es) L es) (eZ M _ (kindOf es))

/-- The residual slice `i` on the log. -/
def zres (L es : Log) (i : Fin 64) : Fin (2 ^ mm 6 (kindOf es)) → F :=
  bzRes (aZ M _ (kindOf es) L es) (bZ M _ (kindOf es) L es) (zZ _ (kindOf es) L es)
    (eZ M _ (kindOf es)) i

/-- **Z1's final doom**: some residual slice's extension at `r` is nonzero. -/
def ZEnd (L es : Log) : Prop :=
  ∃ i : Fin 64, mle (zres M L es i) (ptOf (mm 6 (kindOf es)) (zrL es)) ≠ 0

/-! ## Z2 on the log -/

/-- `P^e` on `S`: `Σ_u eq(r, u) E(σ, u)` (the verifier's `targetS r`). -/
def peL (es : Log) : Fin 64 → F := fun σ =>
  ∑ u, eq (ptOf (mm 6 (kindOf es)) (zrL es)) (cube u) * eZ M _ (kindOf es) σ u

/-- **Z3's initial claim** `P^{ab}*(λ)` (`lagrangeS`'s first value). -/
def c0Z (es : Log) : F := interpolateAt node127 (z2Vals (pzL es) (pabL es) (peL M es)) (lamL es)

/-- The true `P^{ab}`, `P^z` at Z1's point. -/
def pabT (L es : Log) : Polynomial F :=
  pabPoly (ptOf (mm 6 (kindOf es)) (zrL es)) (aZ M _ (kindOf es) L es) (bZ M _ (kindOf es) L es)
def pzT (L es : Log) : Polynomial F :=
  pzPoly (ptOf (mm 6 (kindOf es)) (zrL es)) (zZ _ (kindOf es) L es)

/-- **The pending c-claim is false**: `P^z*(λ) ≠ ẑ(r, λ)`. -/
def PendZ (L es : Log) : Prop := 14 < es.length ∧ pzStar es ≠ (pzT L es).eval (lamL es)

/-- After `λ`: Z3's initial claim or the c-claim is false. -/
def Z2Bad (L es : Log) : Prop :=
  14 < es.length ∧ (c0Z M es ≠ (pabT M L es).eval (lamL es) ∨ PendZ L es)

/-- **Z2's doom** (phase 4, positions 13 and 14): `ZEnd` until `λ` is drawn, then `Z2Bad`. -/
def Z2D (L es : Log) : Prop := if es.length ≤ 14 then ZEnd M L es else Z2Bad M L es

/-! ## Z3 and Zend on the log -/

/-- Z3's tables `eq(r, ·)`, `Â(λ, ·)`, `B̂(λ, ·)` (`bzTables`). -/
def TZ (L es : Log) : Array (Array F) :=
  bzTables (ℓ := mm 6 (kindOf es)) (zrL es) (lamL es) (aZ M _ (kindOf es) L es)
    (bZ M _ (kindOf es) L es)

/-- **Z3's rounds' doom** (`D3` from 15, `m − 6` real rounds, `w·a·b`). -/
abbrev D3Z : Log → Log → Prop := D3 15 (fun _ es => c0Z M es) (mm 6) bzExpr (TZ M)

/-- The true pair at `(λ, r′)`. -/
def aStar (L es : Log) : F :=
  mle (fun u => (skipExt fun i => aZ M (mm 6 (kindOf es)) (kindOf es) L es i u).eval (lamL es))
    (ptOf (mm 6 (kindOf es)) (rZ es))
def bStar (L es : Log) : F :=
  mle (fun u => (skipExt fun i => bZ M (mm 6 (kindOf es)) (kindOf es) L es i u).eval (lamL es))
    (ptOf (mm 6 (kindOf es)) (rZ es))

/-- **`relZ`'s first conjunct fails on the log** (from 68): Z3's last claim is not
`eq(r, r′)·â·b̂`. -/
def RejZ (L es : Log) : Prop :=
  68 ≤ es.length ∧ clR 15 (fun _ es => c0Z M es) L es (mm 6 (kindOf es)) ≠
    eq (ptOf (mm 6 (kindOf es)) (zrL es)) (ptOf (mm 6 (kindOf es)) (rZ es)) * (vZ es 0 * vZ es 1)

/-- **Zend's doom**: the absorbed pair is not the true one. -/
def ZendBad (L es : Log) : Prop :=
  68 ≤ es.length ∧ (vZ es 0, vZ es 1) ≠ (aStar M L es, bStar M L es)

/-- **The c-claim's binding** (`relZ`'s second conjunct, INT-4): RS claim 1's value is
`P^z*(λ)`. -/
def oZ (_κ : Kind) (es : Log) (v : F) : Prop := v = pzStar es

end

/-! ## Positions -/

/-- **Z's and L's positions** (A.4): Z1's ten squeezes after 2 (phase 3), Z2 at 13–14 (4), Z3 from
15 (5), Zend at 67 (6), L1 at 68 (7), L2 from 69 (8), L3 at 97 (9), L3β at 98 (10), S1 from 99. -/
theorem z_unit_pos :
    (2, 10) ∈ fsRanges ∧ phOf 2 = 2 ∧ phOf 3 = 3 ∧ phOf 12 = 3 ∧ phOf 13 = 4 ∧ phOf 14 = 4 ∧
    phOf 15 = 5 ∧ phOf 66 = 5 ∧ phOf 67 = 6 ∧ phOf 68 = 7 ∧ phOf 69 = 8 ∧ phOf 96 = 8 ∧
    phOf 97 = 9 ∧ phOf 98 = 10 ∧ phOf 99 = 11 := by
  refine ⟨by rw [fsRanges_eq]; simp, ?_⟩
  have hph : ∀ q, phOf q = (fsStarts.filter (· ≤ q)).length - 1 := fun _ => rfl
  simp only [hph, fsStarts_eq]
  exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

theorem mm6_eq (κ : Kind) : mm 6 κ = 7 + (κ.m - 13) := by cases κ <;> rfl

/-! ## Reads -/

section Reads
variable {M} {L es L' es' : Log} {p : ℕ}

theorem zBk_same (h : Same L es L' es' p) (hp : 3 ≤ p) (κ : Kind) :
    zBk κ L es = zBk κ L' es' := by
  funext t k; simp only [zBk, zW_same h hp κ]

theorem aZ_same (h : Same L es L' es' p) (hp : 3 ≤ p) (ℓ : ℕ) (κ : Kind) :
    aZ M ℓ κ L es = aZ M ℓ κ L' es' := by
  funext σ u; simp only [aZ, mvZ, zBk_same h hp κ]

theorem bZ_same (h : Same L es L' es' p) (hp : 3 ≤ p) (ℓ : ℕ) (κ : Kind) :
    bZ M ℓ κ L es = bZ M ℓ κ L' es' := by
  funext σ u; simp only [bZ, mvZ, zBk_same h hp κ]

theorem zZ_same (h : Same L es L' es' p) (hp : 3 ≤ p) (ℓ : ℕ) (κ : Kind) :
    zZ ℓ κ L es = zZ ℓ κ L' es' := by
  funext σ u; simp only [zZ, zBk_same h hp κ]

theorem zHolds_same (h : Same L es L' es' p) (hp : 3 ≤ p) : ZHolds M L es ↔ ZHolds M L' es' := by
  have hk := h.kind (by omega)
  unfold ZHolds
  rw [hk, aZ_same h hp, bZ_same h hp, zZ_same h hp]

theorem zHolds_reads : Reads 3 (ZHolds M) := fun _ _ _ _ _ _ h => zHolds_same h le_rfl

/-- `ZEnd` from a nonzero residual at Z1's point read off a longer chain. -/
theorem zEnd_of (h : Same L es L' es' 3) {i : Fin 64}
    (hne : mle (zres M L' es' i) (ptOf (mm 6 (kindOf es')) (List.ofFn pinnedRho ++
      (List.range ((kindOf es').m - 13)).map (coordAt es 2))) ≠ 0) : ZEnd M L es := by
  have hk := h.kind (by norm_num)
  refine ⟨i, ?_⟩
  unfold zres zrL
  rw [hk, aZ_same h le_rfl, bZ_same h le_rfl, zZ_same h le_rfl]
  exact hne

theorem zEnd_reads : Reads 13 (ZEnd M) := fun L es L' es' h1 h2 h => by
  have hk := h.kind (by norm_num)
  unfold ZEnd zres
  rw [hk, zrL_agree h.1, aZ_same h (by norm_num), bZ_same h (by norm_num),
    zZ_same h (by norm_num)]

end Reads

/-! ## Bits -/

theorem zBk_bit (κ : Kind) (L es : Log) (t : ℕ) (k : Fin (2 ^ 14)) : IsBitF (zBk κ L es t k) :=
  unpack_boolean _ _

variable {M}

theorem mvZ_bit (hM : M.Bits) {A : Fin 9 → Fin (2 ^ 14) → Fin (2 ^ 14) → F}
    (hA : ∀ j p k, IsBitF (A j p k)) (κ : Kind) (L es : Log) (t : ℕ) (p : Fin (2 ^ 14)) :
    IsBitF (mvZ M A κ L es t p) :=
  sum_bitF _ _ fun j _ => isBit_mul (hM.2.2.1 κ j t)
    (sum_bitF _ _ fun k _ => isBit_mul (hA j p k) (zBk_bit κ L es t k))

theorem zres_bit (hM : M.Bits) (L es : Log) (i : Fin 64) (u : Fin (2 ^ mm 6 (kindOf es))) :
    IsBitF (zres M L es i u) :=
  bzRes_bit (fun _ _ => mvZ_bit hM hM.1 _ L es _ _) (fun _ _ => mvZ_bit hM hM.2.1 _ L es _ _)
    (fun _ _ => zBk_bit _ L es _ _) (fun _ _ => hM.2.2.2 _ _ _) i u

/-! ## Z1 (`hfin`, positions 3 … 12) -/

/-- Z1's doom on the coordinate list: the background, or a pinned-fixed residual slice whose
extension is nonzero at the coordinates bound so far (`mlDoom`). -/
def Z1Doom (M : ZLM) (Bg : Log → Log → Prop) (L es₀ : Log) (l : List F) : Prop :=
  Bg L es₀ ∨ ∃ i : Fin 64, ∃ t : Array F,
    t.size = 2 ^ ((kindOf es₀).m - 13) ∧ mlDoom ((kindOf es₀).m - 13) t l ∧
    ∀ cs : List F, cs.length = (kindOf es₀).m - 13 →
      mle (tbl ((kindOf es₀).m - 13) t) (ptOf ((kindOf es₀).m - 13) cs) =
        mle (zres M L es₀ i) (ptOf (mm 6 (kindOf es₀)) (List.ofFn pinnedRho ++ cs))

open Classical in
/-- **Z1's charge** (§5.2 row Z1, `≤ 19/2^128 ≤ deltaR`): with the entry's doom `Bg ∨ ¬ ZHolds`
and a final doom containing `Bg ∨ ZEnd`, the ten squeezes escape with conditional probability at
most `deltaR`. The pinned coordinates cost nothing (`pinned_sound`), each free one at most one
value (`zerocheck_bad_le`). -/
theorem z1_hfin (hM : M.Bits) {Dk : ℕ → Log → Log → Prop} {Bg : Log → Log → Prop}
    (hBg : Reads 3 Bg) (hprev : ∀ L es, Dk (phOf 2) L es → Bg L es ∨ ¬ ZHolds M L es)
    {fin : Log → Log → Prop} (hfin : Dk (phOf 3) = msD (Dk (phOf 2)) fin 2 10)
    (hfinI : ∀ L es, Bg L es ∨ ZEnd M L es → fin L es)
    (L es₀ : Log) (hl : es₀.length = 3) : condCount (DPos (Dp Dk)) L es₀ 10 [] ≤ deltaR := by

  refine hfin_seq z_unit_pos.1 hfin (fun i => if i < 19 then 1 else 0) (by decide) (Z1Doom M Bg)
    (fun L es₀ l hd => ?_) (fun L es₀ hd => ?_) (fun L es₀ as hl' has hd hnf => ?_) L es₀ hl
  · rcases hd with hb | ⟨i, t, hts, hd, hcs⟩
    · exact (Finset.card_eq_zero.mpr (Finset.filter_eq_empty_iff.mpr fun c _ h => h (.inl hb))).trans_le
        (Nat.zero_le _)
    refine le_trans (card_le_card fun c hc => ?_) ((mlDoom_step hts l hd).trans ?_)
    · simp only [mem_filter, mem_univ, true_and] at hc ⊢
      exact fun h => hc (.inr ⟨i, t, hts, h, hcs⟩)
    · have := m13_le (kindOf es₀); split_ifs <;> omega
  · rcases hprev L es₀ hd with hb | hz
    · exact .inl hb
    obtain ⟨i, hi⟩ := bz_start hz
    obtain ⟨t, hts, ht0, hcs⟩ := pinned_table (mm6_eq (kindOf es₀)) (zres M L es₀ i)
      (zres_bit hM L es₀ i) hi
    exact .inr ⟨i, t, hts, mlDoom_nil ht0, hcs⟩
  · obtain ⟨ys, hy⟩ := ext_eq_append es₀ as
    have hS : Same L (ext es₀ as) L es₀ 3 := by
      rw [hy]; exact (same_append L es₀ ys).mono (by omega)
    rintro (hb | ⟨i, t, hts, hd, hcs⟩)
    · exact hnf (hfinI _ _ (.inl ((hBg.ext L es₀ as (by omega)).mpr hb)))
    have hk := m13_le (kindOf es₀)
    have hlen : (kindOf es₀).m - 13 ≤ (List.ofFn fun j : Fin (10 * 2) =>
        coordAt (ext es₀ as) 2 j).length := by simp; omega
    rw [mlDoom_full t hts _ hlen, hcs _ (by simp; omega),
      take_ofFn_coord (ext es₀ as) (by omega : (kindOf es₀).m - 13 ≤ 10 * 2)] at hd
    exact hnf (hfinI _ _ (.inr (zEnd_of hS hd)))

/-! ## Reads of Z2 … Zend -/

section Reads2
variable {L es L' es' X : Log} {p : ℕ}

theorem c0Z_agree (h : Agree es es' 15) : c0Z M es = c0Z M es' := by
  obtain ⟨hk, hz, hl, hp, hq⟩ := z2_agree h
  unfold c0Z peL; rw [hk, hz, hl, hp, hq]

theorem pzT_same (h : Same L es L' es' p) (hp : 13 ≤ p) : pzT L es = pzT L' es' := by
  have hk := h.kind (by omega)
  unfold pzT; rw [hk, zrL_agree (h.1.mono hp), zZ_same h (by omega)]

theorem pabT_same (h : Same L es L' es' p) (hp : 13 ≤ p) : pabT M L es = pabT M L' es' := by
  have hk := h.kind (by omega)
  unfold pabT; rw [hk, zrL_agree (h.1.mono hp), aZ_same h (by omega), bZ_same h (by omega)]

theorem pendZ_reads : Reads 15 PendZ := fun L es L' es' h1 h2 h => by
  have hl := (z2_agree h.1).2.2.1
  rw [PendZ, PendZ, pzStar_agree h.1, pzT_same h (by norm_num), hl]
  exact and_congr_left fun _ => ⟨fun _ => by omega, fun _ => by omega⟩

theorem z2Bad_reads : Reads 15 (Z2Bad M) := fun L es L' es' h1 h2 h => by
  have hl := (z2_agree h.1).2.2.1
  unfold Z2Bad
  rw [c0Z_agree h.1, pabT_same h (by norm_num), hl, pendZ_reads L es L' es' h1 h2 h]
  exact and_congr_left fun _ => ⟨fun _ => by omega, fun _ => by omega⟩

theorem TZ_same (h : Same L es L' es' p) (hp : 15 ≤ p) : TZ M L es = TZ M L' es' := by
  obtain ⟨hk, hz, hl, -, -⟩ := z2_agree (h.1.mono hp)
  unfold TZ; rw [hk, hz, hl, aZ_same h (by omega), bZ_same h (by omega)]

theorem TZ_local : TruthLocal 15 (fun _ es => c0Z M es) (TZ M) := fun L _ _ h =>
  ⟨TZ_same (same_of_agree L h) le_rfl, c0Z_agree h⟩

theorem TZ_size (L es : Log) : ∀ t ∈ TZ M L es, t.size = 2 ^ mm 6 (kindOf es) :=
  bz_sizes _ _ _ _

/-- Z's dooms read the log only through the level-0 word: on one chain, two logs whose words
agree give the same dooms (`hstab`, `FrontChainStab`). -/
theorem zDooms_log (h : Same L X L' X p) (hp : 3 ≤ p) :
    (ZEnd M L X ↔ ZEnd M L' X) ∧ (Z2D M L X ↔ Z2D M L' X) ∧ (D3Z M L X ↔ D3Z M L' X) ∧
      (ZendBad M L X ↔ ZendBad M L' X) ∧ (PendZ L X ↔ PendZ L' X) ∧ (ZHolds M L X ↔ ZHolds M L' X) := by
  have hz := zZ_same h hp; have ha := aZ_same (M := M) h hp; have hb := bZ_same (M := M) h hp
  have h1 : ZEnd M L X ↔ ZEnd M L' X := by unfold ZEnd zres; rw [ha, hb, hz]
  have h2 : PendZ L X ↔ PendZ L' X := by unfold PendZ pzT; rw [hz]
  have h3 : Z2Bad M L X ↔ Z2Bad M L' X := by unfold Z2Bad pabT; rw [ha, hb, h2]
  refine ⟨h1, ?_, ?_, ?_, h2, zHolds_same h hp⟩
  · unfold Z2D; split_ifs; exacts [h1, h3]
  · exact (D3_log_congr (b := 15) (c0 := fun _ es => c0Z M es) (nr := mm 6) (e := bzExpr)
      (T := TZ M) (by unfold TZ; rw [ha, hb]) rfl).symm
  · unfold ZendBad aStar bStar; rw [ha, hb]

theorem zendBad_reads : Reads 68 (ZendBad M) := fun L es L' es' h1 h2 h => by
  obtain ⟨hk, hz, hl, -, -⟩ := z2_agree (h.1.mono (by norm_num))
  have hr : rZ es = rZ es' := by
    unfold rZ rchs; rw [hk]
    refine List.map_congr_left fun j hj => ?_
    have := Kind.m_le (kindOf es'); simp only [List.mem_range, mm] at hj
    exact rch_congr h.1 (by omega)
  have hv : ∀ j, vZ es j = vZ es' j := fun j => by
    simp only [vZ, msgAt_congr h.1 (show 67 < 68 by norm_num)]
  unfold ZendBad aStar bStar
  rw [hk, hl, hr, hv, hv, aZ_same h (by norm_num), bZ_same h (by norm_num)]
  exact and_congr_left fun _ => ⟨fun _ => h2, fun _ => h1⟩

theorem rejZ_reads : Reads 68 fun L es => clR 15 (fun _ es => c0Z M es) L es (mm 6 (kindOf es)) ≠
    eq (ptOf (mm 6 (kindOf es)) (zrL es)) (ptOf (mm 6 (kindOf es)) (rZ es)) * (vZ es 0 * vZ es 1) :=
  fun L es L' es' h1 h2 h => by
  obtain ⟨hk, hz, -, -, -⟩ := z2_agree (h.1.mono (by norm_num))
  have hr : rZ es = rZ es' := by
    unfold rZ rchs; rw [hk]
    refine List.map_congr_left fun j hj => ?_
    have := Kind.m_le (kindOf es'); simp only [List.mem_range, mm] at hj
    exact rch_congr h.1 (by omega)
  have hv : ∀ j, vZ es j = vZ es' j := fun j => by
    simp only [vZ, msgAt_congr h.1 (show 67 < 68 by norm_num)]
  have hc : clR 15 (fun _ es => c0Z M es) L es (mm 6 (kindOf es)) =
      clR 15 (fun _ es => c0Z M es) L' es' (mm 6 (kindOf es)) := by
    rw [clR_log_congr (L := L) (L' := L') rfl]
    have := Kind.m_le (kindOf es)
    exact clR_congr (c0 := fun _ es => c0Z M es) (c0Z_agree (h.1.mono (by norm_num)))
      (h.1.mono (by simp only [mm]; omega))
  beta_reduce
  rw [hc, hk, hz, hr, hv, hv]

end Reads2

/-! ## Z2 (`habs` at 13, `hsingle` at 14) -/

/-- **Into Z2** (`habs` at 13): Z1's final doom carries over Z2's absorb. -/
theorem z2_habs {L es : Log} (x : ByteArray × Digest) (hl : es.length = 13) (hz : ZEnd M L es) :
    Z2D M L (es ++ [x]) := by
  have : (es ++ [x]).length ≤ 14 := by simp; omega
  rw [Z2D, if_pos this]; exact (zEnd_reads.append L es [x] (by omega)).mpr hz

theorem z2_ext1 (L es : Log) (a : Digest) (hl : es.length = 14) :
    c0Z M (ext1 es a) = interpolateAt node127 (z2Vals (pzL es) (pabL es) (peL M es)) (chF a 0) ∧
    pzStar (ext1 es a) = interpolateAt lNode (pzL es) (chF a 0) ∧
    pabT M L (ext1 es a) = pabT M L es ∧ pzT L (ext1 es a) = pzT L es ∧
    lamL (ext1 es a) = chF a 0 := by
  have hS := same_ext1 L es a
  rw [hl] at hS
  obtain ⟨hk, hz, hp, hq⟩ := z2_agree14 (hS.1 : Agree (ext1 es a) es 14)
  have hlam : lamL (ext1 es a) = chF a 0 := by
    have := entAt_ext1 es a; rw [hl] at this
    simp only [lamL, fAt, ansAt, this]
  refine ⟨?_, ?_, pabT_same hS (by norm_num), pzT_same hS (by norm_num), hlam⟩
  · unfold c0Z peL; rw [hk, hz, hp, hq, hlam]
  · unfold pzStar; rw [hp, hlam]

open Classical in
/-- **Z2's squeeze** (§5.2 row Z2, `126·2^128`; `skip_pair_bad_le`): from Z1's final doom, at most
126 values of `λ` make both reconstructed values agree with the truth. -/
theorem z2_single (L es : Log) (hl : es.length = 14) :
    (univ.filter fun a => Z2D M L es ∧ ¬ Z2D M L (ext1 es a)).card ≤ 126 * 2 ^ 128 := by
  have hle : es.length ≤ 14 := by omega
  have hgt : ∀ a, ¬ (ext1 es a).length ≤ 14 := fun a => by rw [length_ext1]; omega
  by_cases hz : ZEnd M L es
  swap
  · exact (Finset.card_eq_zero.mpr (Finset.filter_eq_empty_iff.mpr fun a _ h =>
      hz (by rw [Z2D, if_pos hle] at h; exact h.1))).trans_le (Nat.zero_le _)
  obtain ⟨i, hi⟩ := hz
  have hb : ∃ b : Fin 64, (pabT M L es).eval (skipNode (Fin.castLE (by norm_num) b)) ≠
      (pzT L es).eval (skipNode (Fin.castLE (by norm_num) b)) + peL M es b := ⟨i, bz_end hi⟩
  have hcnt := skip_pair_bad_le (pzL es) (pabL es) (peL M es) (pabT M L es) (pzT L es)
    (pabPoly_natDegree _ _ _) (pzPoly_natDegree _ _) (.inl hb)
  refine single_F_le' _ _ hcnt fun a ⟨_, hn⟩ => ?_
  simp only [Z2D, hgt a, if_false] at hn
  obtain ⟨h1, h2, h3, h4, h5⟩ := z2_ext1 (M := M) L es a hl
  refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩
  by_contra hc
  refine hn ⟨by rw [length_ext1]; omega, ?_⟩
  rw [h1, h3, h5, PendZ, h2, h4, h5]
  by_cases hab : interpolateAt node127 (z2Vals (pzL es) (pabL es) (peL M es)) (chF a 0) =
    (pabT M L es).eval (chF a 0)
  · exact .inr ⟨by rw [length_ext1]; omega, fun h => hc ⟨hab, h⟩⟩
  · exact .inl hab

/-! ## Z3 (`habs` at 15, `hsingle` per round) and Zend (`habs` at 67) -/

/-- **Into Z3** (`habs` at 15): a false initial claim `P^{ab}*(λ)` is Z3's round doom
(`bz_trueSum`); otherwise the c-claim is pending false. -/
theorem z3_habs {L es : Log} (x : ByteArray × Digest) (hl : es.length = 15) (hz : Z2Bad M L es) :
    D3Z M L (es ++ [x]) ∨ PendZ L (es ++ [x]) := by
  have hS := same_append L es [x]
  rw [hl] at hS
  rcases hz.2 with hc | hp
  · refine .inl ⟨by simp; omega, ?_⟩
    have ha0 : ans3 15 (mm 6) (es ++ [x]) = 0 := by
      simp only [ans3, List.length_append, List.length_singleton, hl]; simp
    rw [ha0]
    simp only [Wrong3, clR, rchs, List.range_zero, List.map_nil, bindAll, Nat.sub_zero]
    rw [TZ_same hS le_rfl, c0Z_agree (M := M) hS.1, hS.kind (by norm_num)]
    unfold TZ; rw [bz_trueSum]; exact hc
  · exact .inr ((pendZ_reads.append L es [x] (by omega)).mpr hp)

open Classical in
/-- **Z3's squeezes** (§5.2 row Z3, `3·2^128`, `D3_single`). -/
theorem z3_single (L es : Log) :
    (univ.filter fun a => D3Z M L es ∧ ¬ D3Z M L (ext1 es a)).card ≤ 3 * 2 ^ 128 :=
  D3_single (by norm_num) TZ_local bzExpr_deg (TZ_size (M := M)) L es

/-- **At Zend's absorb** (67): a false final Z3 claim gives `RejZ` (`relZ`'s first conjunct fails)
or a wrong pair `(â, b̂)` (`bz_final`, `bz_triple_wrong`). -/
theorem zend_habs {L es : Log} (x : ByteArray × Digest) (hl : es.length = 67)
    (hd : D3Z M L es) : RejZ M L (es ++ [x]) ∨ ZendBad M L (es ++ [x]) := by
  have hS := same_append L es [x]
  rw [hl] at hS
  have hk : kindOf (es ++ [x]) = kindOf es := hS.kind (by norm_num)
  have hm := Kind.m_le (kindOf es)
  obtain ⟨-, hw⟩ := hd
  have ha : ans3 15 (mm 6) es = mm 6 (kindOf es) := by
    simp only [ans3, hl, mm]; omega
  rw [ha] at hw
  unfold Wrong3 at hw
  rw [Nat.sub_self] at hw
  have hfin : trueSum bzExpr (bindAll (TZ M L es) (rchs 15 es (mm 6 (kindOf es)))) 0 =
      eq (ptOf (mm 6 (kindOf es)) (zrL es)) (ptOf (mm 6 (kindOf es)) (rZ es)) *
        (aStar M L es * bStar M L es) :=
    bz_final _ _ (by simp [rchs]) _ _ _
  rw [hfin] at hw
  have hag : Agree (es ++ [x]) es 67 := hS.1
  obtain ⟨-, hz, hlam, -, -⟩ := z2_agree (hag.mono (by norm_num))
  have hr : rZ (es ++ [x]) = rZ es := by
    unfold rZ rchs; rw [hk]
    refine List.map_congr_left fun j hj => ?_
    simp only [List.mem_range, mm] at hj
    exact rch_congr hag (by omega)
  have hc : clR 15 (fun _ es => c0Z M es) L (es ++ [x]) (mm 6 (kindOf es)) =
      clR 15 (fun _ es => c0Z M es) L es (mm 6 (kindOf es)) :=
    clR_congr (c0Z_agree (hag.mono (by norm_num))) (hag.mono (by simp only [mm]; omega))
  have haS : aStar M L (es ++ [x]) = aStar M L es ∧ bStar M L (es ++ [x]) = bStar M L es := by
    unfold aStar bStar; rw [hk, hlam, hr, aZ_same hS (by norm_num), bZ_same hS (by norm_num)]
    exact ⟨rfl, rfl⟩
  by_cases hrej : RejZ M L (es ++ [x])
  · exact .inl hrej
  refine .inr ⟨by simp; omega, ?_⟩
  have hchk : clR 15 (fun _ es => c0Z M es) L es (mm 6 (kindOf es)) =
      eq (ptOf (mm 6 (kindOf es)) (zrL es)) (ptOf (mm 6 (kindOf es)) (rZ es)) *
        (vZ (es ++ [x]) 0 * vZ (es ++ [x]) 1) := by
    by_contra hne
    exact hrej ⟨by simp; omega, by rw [hk, hz, hr, hc]; exact hne⟩
  rw [haS.1, haS.2]
  exact bz_triple_wrong hw hchk

theorem rejZ_ok (hp : fsItems[67]? ≠ some .squeeze) : RejOK (RejZ M) :=
  rejOK_at (p := 67) rejZ_reads hp

/-! ## The c-claim's binding -/

theorem oZ_reads (κ : Kind) (es es' : Log) (h : Agree es es' 312) : oZ κ es = oZ κ es' := by
  funext v; simp only [oZ, pzStar_agree (h.mono (by norm_num))]

/-! ## Controls -/

/-- The identity matrices on kind 0 with the target `e` (a control instance of `ZLM`). -/
def zlmId (e : F) : ZLM :=
  ⟨fun _ p k => if p = k then 1 else 0, fun _ p k => if p = k then 1 else 0,
    fun _ j _ => if j = 0 then 1 else 0, fun _ _ _ => e⟩

theorem mvZ_idA (e : F) (κ : Kind) (L es : Log) (t : ℕ) (p : Fin (2 ^ 14)) :
    mvZ (zlmId e) (zlmId e).Ak κ L es t p = zBk κ L es t p := by simp [mvZ, zlmId]

theorem mvZ_idB (e : F) (κ : Kind) (L es : Log) (t : ℕ) (p : Fin (2 ^ 14)) :
    mvZ (zlmId e) (zlmId e).Bk κ L es t p = zBk κ L es t p := by simp [mvZ, zlmId]

theorem zres_id (e : F) (L es : Log) (i : Fin 64) (u : Fin (2 ^ mm 6 (kindOf es))) :
    zres (zlmId e) L es i u = e := by
  simp only [zres, bzRes, aZ, bZ, zZ, eZ, mvZ_idA, mvZ_idB]
  rcases zBk_bit (kindOf es) L es (u.val / 256) (pAt i u.val) with h | h <;>
    simp [h, zlmId, CharTwo.add_self_eq_zero]

/-- Control (positive): with the identity matrices and the zero target, every log satisfies
Z's statement (`z·z = z` on bits). -/
theorem zHolds_id (L es : Log) : ZHolds (zlmId 0) L es := fun i u => by
  have := zres_id 0 L es i u
  simp only [zres, bzRes] at this
  rw [add_assoc] at this
  exact CharTwo.add_eq_zero.mp this

/-- Control (negative, non-vacuous): with the target `1` no log satisfies it, and Z1's final doom
holds at every point (the residual is the constant `1`). -/
theorem not_zHolds_one (L es : Log) : ¬ ZHolds (zlmId 1) L es := fun h => by
  have h0 := h 0 0
  have := zres_id 1 L es 0 0
  simp only [zres, bzRes] at this
  rw [h0, add_assoc, CharTwo.add_self_eq_zero] at this
  exact zero_ne_one this

theorem zEnd_one (L es : Log) : ZEnd (zlmId 1) L es := ⟨0, by
  have : zres (zlmId 1) L es 0 = fun _ => 1 := funext (zres_id 1 L es 0)
  rw [this]; simp [mle, eq_sum_one]⟩

theorem not_zEnd_id (L es : Log) : ¬ ZEnd (zlmId 0) L es := fun ⟨i, h⟩ => by
  have : zres (zlmId 0) L es i = fun _ => 0 := funext (zres_id 0 L es i)
  rw [this] at h; simp [mle] at h

/-- Controls of the binding `oZ` (`relZ`'s second conjunct): it accepts exactly `P^z*(λ)`. -/
theorem oZ_self (κ : Kind) (es : Log) : oZ κ es (pzStar es) := rfl

theorem not_oZ {κ : Kind} {es : Log} {v : F} (h : v ≠ pzStar es) : ¬ oZ κ es v := h

/-- Control: before `λ`, Z2's doom is Z1's; `RejZ` never holds before Zend's absorb. -/
theorem z2D_short {L es : Log} (h : es.length ≤ 14) : Z2D M L es ↔ ZEnd M L es := by
  rw [Z2D, if_pos h]

theorem not_rejZ_short {L es : Log} (h : es.length < 68) : ¬ RejZ M L es := fun hr => by
  have := hr.1; omega

theorem not_pendZ_of {L es : Log} (h : pzStar es = (pzT L es).eval (lamL es)) : ¬ PendZ L es :=
  fun hp => hp.2 h

end FR.Snd
