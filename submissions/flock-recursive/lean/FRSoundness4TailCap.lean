-- New for `flock-recursive` (PACK-4.4 §11.1, §11.5, `reviews/PACK-4.4-b2-review.md` PB-M1; track A3′
-- run 2): the batched cap check (β′) on the log.
import FRSoundness4Tail

/-!
# The batched cap check on the log (revision 4.4.1, (β′))

After `Pf` the chain absorbs `D` (phase 52, `CapD`), squeezes `ζ` (53, `CapZeta`), absorbs `A` (54,
`CapChk`) and squeezes `z` (55, `CapChkZ`). On the chain `es`:

* **the reads** `(i, q)`, `i < 5`, `q < tᵢ` (871 in all, ordinal `rdIx i q`): the committed path
  digest `dAt es i q` (`D_r`, from `CapD`'s message), the cap index `kCap es i q = qPos >>> sib`;
* **the batched caps** `capG es k`, `k < nE = 1,536` (level `lvOfE k`'s entry `k − cOff`), `A_k = aAt es k`;
* **`capChk4 es`**: what V's three `assertEq` say, (I) `Σ_r ζ^r·D_r = Σ_k A_k·cap[k]` per F half and
  (II) `Σ_k A_k·z^k = Σ_r ζ^r·z^{offᵢ + k_r}`;
* **`truthCap es`**: every committed digest is its cap entry (`D_r = cap_i[k_r]`);
* the two **escape sets** (PB-M1: not dooms): `DZeta` (a false `D` whose (I) vanishes at `ζ` with the
  honest `Â`) and `DZ` (a dishonest `A` whose (II) holds at `z`);
* **`cap_of_chk`**: `capChk4 → ¬DZeta → ¬DZ → truthCap`;
* **the counts**: `card_dZeta ≤ 870`, `card_dZ ≤ 1,535` answers (Schwartz–Zippel over `K`, `chK`
  a bijection), what `hsingle` charges at phases 53 and 55.

Every value but `ζ`, `A`, `z` is fixed by the entries before phase 53 (`dAt_append` …): `D`, the
caps and the `k_r` are in the chain before `ζ`, `A` before `z`.
-/

namespace FR.Snd.T4
open RecursionFast Finset Polynomial

set_option linter.constructorNameAsVariable false

/-! ## The values on the log -/

/-- Level `i`'s queries (`seq4`'s `tᵢ`; every kind's, `lvt_eq`). -/
abbrev tq (i : ℕ) : ℕ := (Rev4.seq4.lv i).t

/-- The ordinal of read `(i, q)` (item order: the levels below first). -/
def rdIx (i q : ℕ) : ℕ := Rev4.capReadsBelow Rev4.seq4 i + q

/-- Level `i`'s first batched cap entry (`0, 512, 768, 1024, 1280`). -/
def cOff (i : ℕ) : ℕ := Rev4.capEntriesBelow Rev4.seq4 i

/-- The batched cap entries (`1,536`). -/
def nE : ℕ := Rev4.capEntries Rev4.seq4

/-- **`D_r`**: read `(i, q)`'s committed path digest, 32 bytes of `CapD`'s message. -/
def dAt (es : Log) (i q : ℕ) : Digest := bytesAt (msgAt es (phStart4 52)) (32 * rdIx i q) 32

/-- **`ζ`**: `CapZeta`'s answer as a `K` element. -/
def zetaK (es : Log) : K := kAt es (phStart4 53)

/-- **`A_k`**: 32 bytes of `CapChk`'s message as a `K` element. -/
def aAt (es : Log) (k : ℕ) : K := K.ofBytes (bytesAt (msgAt es (phStart4 54)) (32 * k) 32)

/-- **`z`**: `CapChkZ`'s answer as a `K` element. -/
def zK (es : Log) : K := kAt es (phStart4 55)

/-- **`k_r`**: read `(i, q)`'s cap index `qPos >>> sib` (the chain's kind). -/
def kCap (es : Log) (i q : ℕ) : ℕ := qPos (kindOfC es) es i q / 2 ^ (CKind.lv (kindOfC es) i).sib

/-- The level of batched entry `k` (`cOff (lvOfE k) ≤ k < cOff (lvOfE k + 1)` below `nE`). -/
def lvOfE (k : ℕ) : ℕ :=
  if k < cOff 1 then 0 else if k < cOff 2 then 1 else if k < cOff 3 then 2 else if k < cOff 4 then 3 else 4

/-- **`cap[k]`**: batched entry `k` (level `lvOfE k`'s cap entry `k − cOff`). -/
def capG (es : Log) (k : ℕ) : Digest := capDig es (lvOfE k) (k - cOff (lvOfE k))

/-- A digest's first F half (V's `splitDigest`). -/
def loD (d : Digest) : F := F.ofBytes (Vector.ofFn fun i : Fin 16 => d[i.1])

/-- A digest's second F half. -/
def hiD (d : Digest) : F := F.ofBytes (Vector.ofFn fun i : Fin 16 => d[16 + i.1])

/-- The reads' sum `Σ_{i<5} Σ_{q<tᵢ} f i q`. -/
def sumR {M : Type*} [AddCommMonoid M] (f : ℕ → ℕ → M) : M :=
  ∑ i ∈ range 5, ∑ q ∈ range (tq i), f i q

/-- **(I)**'s left side in one F half `h`: `Σ_r ζ^r·h(D_r)`. -/
def capIL (h : Digest → F) (es : Log) : K :=
  sumR fun i q => K.smulF (h (dAt es i q)) (zetaK es ^ rdIx i q)

/-- **(I)**'s right side for weights `A`: `Σ_k A_k·h(cap[k])`. -/
def capIR (h : Digest → F) (es : Log) (A : ℕ → K) : K :=
  ∑ k ∈ range nE, K.smulF (h (capG es k)) (A k)

/-- **(II)**'s left side for weights `A`: `Σ_k A_k·z^k`. -/
def capIIL (es : Log) (A : ℕ → K) : K := ∑ k ∈ range nE, A k * zK es ^ k

/-- **(II)**'s right side: `Σ_r ζ^r·z^{offᵢ + k_r}`. -/
def capIIR (es : Log) : K := sumR fun i q => zetaK es ^ rdIx i q * zK es ^ (cOff i + kCap es i q)

/-- **The honest weights** `Â_k = Σ_{r : offᵢ + k_r = k} ζ^r`. -/
def aHat (es : Log) (k : ℕ) : K :=
  sumR fun i q => if cOff i + kCap es i q = k then zetaK es ^ rdIx i q else 0

/-- `A` is the honest one. -/
def aHon (es : Log) : Prop := ∀ k < nE, aAt es k = aHat es k

/-- **What the cap check asserts** (V's three `assertEq`, `capChkOps`): (I) in both halves, (II). -/
def capChk4 (es : Log) : Prop :=
  capIL loD es = capIR loD es (aAt es) ∧ capIL hiD es = capIR hiD es (aAt es) ∧
    capIIL es (aAt es) = capIIR es

/-- (I) at the honest weights, both halves (PB-M1's `Σ = 0`). -/
def capSig0 (es : Log) : Prop :=
  capIL loD es = capIR loD es (aHat es) ∧ capIL hiD es = capIR hiD es (aHat es)

/-- **`truthCap`**: every committed path digest is its cap entry. -/
def truthCap (es : Log) : Prop := ∀ i < 5, ∀ q < tq i, dAt es i q = capDig es i (kCap es i q)

/-- **The `ζ` escape set** (PB-M1, phase 53): a false `D` whose (I) vanishes at `ζ` and `Â`. -/
def DZeta (es : Log) : Prop := ¬ truthCap es ∧ capSig0 es

/-- **The `z` escape set** (phase 55): a dishonest `A` whose (II) holds at `z`. -/
def DZ (es : Log) : Prop := ¬ aHon es ∧ capIIL es (aAt es) = capIIR es

/-- **`cap_of_chk`** (PACK-4.4 §11.5): the cap check passes and neither escape happened, so `D` is
the caps' (`truthCap`). -/
theorem cap_of_chk {es : Log} (h : capChk4 es) (hζ : ¬ DZeta es) (hz : ¬ DZ es) : truthCap es := by
  by_contra ht
  by_cases ha : aHon es
  · have e : ∀ hf : Digest → F, capIR hf es (aAt es) = capIR hf es (aHat es) := fun hf =>
      sum_congr rfl fun k hk => by rw [ha k (mem_range.1 hk)]
    exact hζ ⟨ht, by rw [← e]; exact h.1, by rw [← e]; exact h.2.1⟩
  · exact hz ⟨ha, h.2.2⟩

/-! ## The ladder facts -/

theorem tq_eq : (List.range 5).map tq = [290, 178, 145, 132, 126] ∧
    (List.range 5).map (Rev4.capReadsBelow Rev4.seq4) = [0, 290, 468, 613, 745] ∧
    (List.range 6).map cOff = [0, 512, 768, 1024, 1280, 1536] ∧ nE = 1536 ∧
    (List.range 5).map (fun i => (Rev4.seq4.lv i).cap) = [9, 8, 8, 8, 8] := by
  unfold cOff nE; rw [Rev4.seq4_eq]; decide

theorem ladder_vals {i : ℕ} (hi : i < 5) :
    rdIx i 0 + tq i ≤ 871 ∧ (∀ i' < i, rdIx i' 0 + tq i' ≤ rdIx i 0) ∧
    cOff i + 2 ^ (Rev4.seq4.lv i).cap = cOff (i + 1) ∧ cOff (i + 1) ≤ nE ∧
      (Rev4.seq4.lv i).cap ≤ 9 := by
  unfold rdIx cOff nE tq; rw [Rev4.seq4_eq]; interval_cases i <;> decide


/-- The cap check's FS positions (`fsStarts4`): `482 … 485`. -/
theorem capPh_pos : phStart4 52 = 482 ∧ phStart4 53 = 483 ∧ phStart4 54 = 484 ∧ phStart4 55 = 485 := by
  unfold phStart4; rw [fsStarts4_eq]; exact ⟨rfl, rfl, rfl, rfl⟩

theorem cOff_vals : cOff 0 = 0 ∧ cOff 1 = 512 ∧ cOff 2 = 768 ∧ cOff 3 = 1024 ∧ cOff 4 = 1280 ∧
    cOff 5 = 1536 ∧ nE = 1536 := by
  unfold cOff nE; rw [Rev4.seq4_eq]; decide

theorem cap_vals : (Rev4.seq4.lv 0).cap = 9 ∧ (Rev4.seq4.lv 1).cap = 8 ∧ (Rev4.seq4.lv 2).cap = 8 ∧
    (Rev4.seq4.lv 3).cap = 8 ∧ (Rev4.seq4.lv 4).cap = 8 := by
  rw [Rev4.seq4_eq]; decide

theorem lvOfE_eq {i e : ℕ} (hi : i < 5) (he : e < 2 ^ (Rev4.seq4.lv i).cap) : lvOfE (cOff i + e) = i := by
  obtain ⟨c0, c1, c2, c3, c4, -⟩ := cOff_vals
  obtain ⟨d0, d1, d2, d3, d4⟩ := cap_vals
  unfold lvOfE
  interval_cases i <;> simp only [c0, c1, c2, c3, c4, d0, d1, d2, d3, d4] at he ⊢ <;>
    norm_num at he <;> split_ifs <;> omega

/-- A batched entry below `nE` lies in its level's block. -/
theorem lvOfE_spec {k : ℕ} (hk : k < nE) : lvOfE k < 5 ∧ cOff (lvOfE k) ≤ k ∧
    k - cOff (lvOfE k) < 2 ^ (Rev4.seq4.lv (lvOfE k)).cap := by
  obtain ⟨c0, c1, c2, c3, c4, -, c6⟩ := cOff_vals
  obtain ⟨d0, d1, d2, d3, d4⟩ := cap_vals
  rw [c6] at hk
  unfold lvOfE
  simp only [c1, c2, c3, c4]
  split_ifs <;> simp only [c0, c1, c2, c3, c4, d0, d1, d2, d3, d4] <;> norm_num <;> omega

theorem capG_eq (es : Log) {i e : ℕ} (hi : i < 5) (he : e < 2 ^ (Rev4.seq4.lv i).cap) :
    capG es (cOff i + e) = capDig es i e := by
  rw [capG, lvOfE_eq hi he, Nat.add_sub_cancel_left]

/-- Every kind's ladder against `seq4`'s: the same `t`, a cap at most `seq4`'s. -/
theorem lv_cap (κ : CKind) {i : ℕ} (hi : i < 5) : (CKind.lv κ i).t = tq i ∧
    (CKind.lv κ i).cap ≤ (Rev4.seq4.lv i).cap ∧ (CKind.lv κ i).cap ≤ (CKind.lv κ i).logN := by
  rcases κ with (_|_|_) | (_|_|_) <;> interval_cases i <;> decide

/-- **`k_r` lies in its level's cap** (`seq4`'s). -/
theorem kCap_lt (es : Log) {i : ℕ} (hi : i < 5) (q : ℕ) : kCap es i q < 2 ^ (Rev4.seq4.lv i).cap := by
  obtain ⟨-, hc, hl⟩ := lv_cap (kindOfC es) hi
  have hq : qPos (kindOfC es) es i q < 2 ^ (CKind.lv (kindOfC es) i).logN := idx_lt _ _ _
  unfold kCap
  rw [Nat.div_lt_iff_lt_mul (by positivity), ← pow_add]
  refine lt_of_lt_of_le hq (Nat.pow_le_pow_right (by norm_num) ?_)
  unfold Level.sib; omega

theorem cOff_kCap_lt (es : Log) {i : ℕ} (hi : i < 5) (q : ℕ) : cOff i + kCap es i q < nE := by
  obtain ⟨-, -, h3, h4, -⟩ := ladder_vals hi
  have := kCap_lt es hi q
  omega

/-- The reads' ordinals are distinct and below `871`. -/
theorem rdIx_inj {i q i' q' : ℕ} (hi : i < 5) (hq : q < tq i) (hi' : i' < 5) (hq' : q' < tq i')
    (h : rdIx i q = rdIx i' q') : i = i' ∧ q = q' := by
  have e : ∀ i q, rdIx i q = rdIx i 0 + q := fun _ _ => by simp [rdIx]
  rw [e i q, e i' q'] at h
  rcases lt_trichotomy i i' with hlt | rfl | hlt
  · have := (ladder_vals hi').2.1 i hlt; omega
  · exact ⟨rfl, by omega⟩
  · have := (ladder_vals hi).2.1 i' hlt; omega

theorem rdIx_le {i q : ℕ} (hi : i < 5) (hq : q < tq i) : rdIx i q ≤ 870 := by
  have e : rdIx i q = rdIx i 0 + q := by simp [rdIx]
  have := (ladder_vals hi).1; omega

/-! ## Reindexing the honest weights -/

theorem sumR_sigma {M : Type*} [AddCommMonoid M] (f : ℕ → ℕ → M) :
    sumR f = ∑ x ∈ (range 5).sigma (fun i => range (tq i)), f x.1 x.2 := by
  unfold sumR; rw [sum_sigma]

/-- **`Σ_k Â_k·f(k) = Σ_r ζ^r·f(offᵢ + k_r)`**. -/
theorem sum_aHat (es : Log) (f : ℕ → K) :
    ∑ k ∈ range nE, aHat es k * f k =
      sumR fun i q => zetaK es ^ rdIx i q * f (cOff i + kCap es i q) := by
  unfold aHat sumR
  simp_rw [sum_mul]
  rw [sum_comm]
  refine sum_congr rfl fun i hi => ?_
  rw [sum_comm]
  refine sum_congr rfl fun q _ => ?_
  simp_rw [ite_mul, zero_mul]
  rw [sum_ite_eq, if_pos (mem_range.2 (cOff_kCap_lt es (mem_range.1 hi) q))]

/-- (I) at the honest weights, as a polynomial in `ζ`: `Σ_r (h(D_r) − h(cap[k_r]))·ζ^r`. -/
def sigP (h : Digest → F) (es : Log) (x : K) : K :=
  sumR fun i q => algebraMap F K (h (dAt es i q) - h (capDig es i (kCap es i q))) * x ^ rdIx i q

theorem capIR_aHat (h : Digest → F) (es : Log) :
    capIR h es (aHat es) =
      sumR fun i q => K.smulF (h (capDig es i (kCap es i q))) (zetaK es ^ rdIx i q) := by
  unfold capIR
  simp_rw [K.smulF_eq_mul, mul_comm (K.ofF _)]
  rw [sum_aHat es fun k => K.ofF (h (capG es k))]
  unfold sumR
  refine sum_congr rfl fun i hi => sum_congr rfl fun q _ => ?_
  dsimp only
  rw [capG_eq es (mem_range.1 hi) (kCap_lt es (mem_range.1 hi) q), mul_comm]

theorem capI_sub (h : Digest → F) (es : Log) :
    capIL h es - capIR h es (aHat es) = sigP h es (zetaK es) := by
  rw [capIR_aHat, capIL, sumR, sumR, ← sum_sub_distrib, sigP, sumR]
  refine sum_congr rfl fun i _ => ?_
  rw [← sum_sub_distrib]
  refine sum_congr rfl fun q _ => ?_
  rw [K.smulF_eq_mul, K.smulF_eq_mul, ← sub_mul, map_sub, K.algebraMap_eq_ofF, K.algebraMap_eq_ofF]

theorem capII_sub (es : Log) :
    capIIL es (aAt es) - capIIR es = ∑ k ∈ range nE, (aAt es k - aHat es k) * zK es ^ k := by
  rw [capIIR, ← sum_aHat es fun k => zK es ^ k, capIIL, ← sum_sub_distrib]
  simp_rw [sub_mul]

/-! ## Schwartz–Zippel over `K` -/

open Classical in
/-- **At most `d` answers make a nonzero polynomial of degree `≤ d` vanish at their `K` challenge**
(distinct exponents `e`, one nonzero coefficient). -/
theorem card_poly_root {ι : Type*} (s : Finset ι) (e : ι → ℕ) (c : ι → K) {d : ℕ}
    (he : Set.InjOn e s) (hd : ∀ x ∈ s, e x ≤ d) {x₀ : ι} (hx₀ : x₀ ∈ s) (hc : c x₀ ≠ 0) :
    (univ.filter fun a : Digest => ∑ x ∈ s, c x * chK a ^ e x = 0).card ≤ d := by
  set P : K[X] := ∑ x ∈ s, C (c x) * X ^ e x with hPd
  have hP : ∀ y, P.eval y = ∑ x ∈ s, c x * y ^ e x := fun y => by simp [hPd, eval_finset_sum]
  have hcoef : P.coeff (e x₀) = c x₀ := by
    simp only [hPd, finset_sum_coeff, coeff_C_mul_X_pow]
    rw [sum_eq_single x₀ (fun x hx hne => if_neg fun h' => hne (he hx hx₀ h'.symm)) (fun h' => absurd hx₀ h'),
      if_pos rfl]
  have hP0 : P ≠ 0 := fun h' => hc (by rw [← hcoef, h', coeff_zero])
  have hdeg : P.natDegree ≤ d :=
    natDegree_sum_le_of_forall_le _ _ fun x hx => (natDegree_C_mul_X_pow_le _ _).trans (hd x hx)
  calc (univ.filter fun a : Digest => ∑ x ∈ s, c x * chK a ^ e x = 0).card
      ≤ (univ.filter fun a : Digest => chK a ∈ P.roots.toFinset).card := by
        refine card_le_card fun a ha => ?_
        simp only [mem_filter, mem_univ, true_and, Multiset.mem_toFinset, mem_roots hP0, IsRoot.def,
          hP] at ha ⊢
        exact ha
    _ = P.roots.toFinset.card := card_chK_fiber _
    _ ≤ P.roots.card := Multiset.toFinset_card_le _
    _ ≤ P.natDegree := card_roots' _
    _ ≤ d := hdeg

/-- A digest is its two F halves. -/
theorem digest_halves {d d' : Digest} (hl : loD d = loD d') (hh : hiD d = hiD d') : d = d' := by
  have e1 := congrArg F.toBytes hl
  have e2 := congrArg F.toBytes hh
  simp only [loD, hiD, F.toBytes_ofBytes] at e1 e2
  refine Vector.ext fun j hj => ?_
  by_cases hj16 : j < 16
  · have := congrArg (·[j]'hj16) e1; simpa using this
  · have := congrArg (·[j - 16]'(by omega)) e2
    simp only [Vector.getElem_ofFn] at this
    simpa [show 16 + (j - 16) = j by omega] using this

/-! ## The values along the chain -/

theorem entAt_last (es : Log) (x : ByteArray × Digest) : entAt (es ++ [x]) es.length = x := by
  simp [entAt]

theorem kAt_ext1 (es : Log) (a : Digest) : kAt (ext1 es a) es.length = chK a := by
  simp only [kAt, ansAt, ext1, entAt_last]

/-- Before `ζ`: `D`, the caps and the `k_r` read the entries before phase 53. -/
theorem capD_congr {es es' : Log} (h : Agree es es' (phStart4 53)) :
    (∀ i < 5, ∀ q < tq i, dAt es i q = dAt es' i q ∧ kCap es i q = kCap es' i q) ∧
      (∀ i < 5, ∀ e, capDig es i e = capDig es' i e) ∧ (truthCap es ↔ truthCap es') := by
  obtain ⟨p52, p53, -⟩ := capPh_pos
  have hk : kindOfC es = kindOfC es' := kindOfC_congr (h.mono (by omega))
  have hcp : ∀ i < 5, capPos i < phStart4 53 := fun i hi => by
    rw [p53]; unfold capPos phStart4; rw [fsStarts4_eq]; interval_cases i <;> decide
  have hD : ∀ i q, dAt es i q = dAt es' i q := fun i q => by
    simp only [dAt, msgAt, h (phStart4 52) (by omega)]
  have hK : ∀ i < 5, ∀ q < tq i, kCap es i q = kCap es' i q := fun i hi q hq => by
    have hS := same_of_agree [] h
    obtain ⟨ht, -⟩ := lv_cap (kindOfC es) hi
    have hp := (tail_pos hi).2.2.2.2
    have hnx : nxStart i ≤ phStart4 53 := by
      unfold nxStart p1Start pfStart; rw [p53]; unfold phStart4; rw [fsStarts4_eq]
      interval_cases i <;> decide
    simp only [kCap, hk, qPos_same hS hi (kindOfC es') (by omega) (by rw [← hk, ht]; exact hq)]
  have hC : ∀ i < 5, ∀ e, capDig es i e = capDig es' i e := fun i hi e => by
    simp only [capDig, msgAt, h (capPos i) (hcp i hi)]
  refine ⟨fun i hi q hq => ⟨hD i q, hK i hi q hq⟩, hC, ?_⟩
  unfold truthCap
  refine forall₂_congr fun i hi => forall₂_congr fun q hq => ?_
  rw [hD, hK i hi q hq, hC i hi]

/-- Before `A`: `ζ`, the honest weights and the (I) sums read the entries before phase 54. -/
theorem capZeta_congr {es es' : Log} (h : Agree es es' (phStart4 54)) :
    zetaK es = zetaK es' ∧ (∀ k, aHat es k = aHat es' k) ∧
      (∀ hf A, capIL hf es = capIL hf es' ∧ capIR hf es A = capIR hf es' A) ∧
      (capSig0 es ↔ capSig0 es') ∧ (∀ x, sigP loD es x = sigP loD es' x ∧ sigP hiD es x = sigP hiD es' x) := by
  obtain ⟨p52, p53, p54, p55⟩ := capPh_pos
  obtain ⟨hDK, hC, -⟩ := capD_congr (h.mono (by omega))
  have hz : zetaK es = zetaK es' := by simp only [zetaK, kAt, ansAt, h (phStart4 53) (by omega)]
  have hcg : ∀ k, capG es k = capG es' k := fun k => by
    unfold capG
    refine hC _ ?_ _
    unfold lvOfE; split_ifs <;> omega
  have hH : ∀ k, aHat es k = aHat es' k := fun k => by
    unfold aHat sumR
    refine sum_congr rfl fun i hi => sum_congr rfl fun q hq => ?_
    dsimp only
    rw [(hDK i (mem_range.1 hi) q (mem_range.1 hq)).2, hz]
  have hIL : ∀ hf, capIL hf es = capIL hf es' := fun hf => by
    unfold capIL sumR
    refine sum_congr rfl fun i hi => sum_congr rfl fun q hq => ?_
    dsimp only
    rw [(hDK i (mem_range.1 hi) q (mem_range.1 hq)).1, hz]
  have hIR : ∀ hf A, capIR hf es A = capIR hf es' A := fun hf A => by
    unfold capIR; simp only [hcg]
  refine ⟨hz, hH, fun hf A => ⟨hIL hf, hIR hf A⟩, ?_, fun x => ?_⟩
  · unfold capSig0
    have e : aHat es = aHat es' := funext hH
    rw [hIL, hIL, hIR, hIR, e]
  · unfold sigP sumR
    constructor <;> refine sum_congr rfl fun i hi => sum_congr rfl fun q hq => ?_ <;> dsimp only <;>
      rw [(hDK i (mem_range.1 hi) q (mem_range.1 hq)).1, (hDK i (mem_range.1 hi) q (mem_range.1 hq)).2,
        hC i (mem_range.1 hi)]

/-- Before `z`: `A` reads the entries before phase 55. -/
theorem capA_congr {es es' : Log} (h : Agree es es' (phStart4 55)) :
    (∀ k, aAt es k = aAt es' k) ∧ (aHon es ↔ aHon es') := by
  obtain ⟨p52, p53, p54, p55⟩ := capPh_pos
  obtain ⟨-, hH, -⟩ := capZeta_congr (h.mono (by omega))
  have hA : ∀ k, aAt es k = aAt es' k := fun k => by
    simp only [aAt, msgAt, h (phStart4 54) (by omega)]
  refine ⟨hA, ?_⟩
  unfold aHon; simp only [hA, hH]

/-- After `z`: the (II) sums and the whole check read the entries before phase 55 and `z`. -/
theorem capZ_congr {es es' : Log} (h : Agree es es' (phStart4 55 + 1)) :
    zK es = zK es' ∧ (capChk4 es ↔ capChk4 es') ∧ (DZ es ↔ DZ es') := by
  obtain ⟨p52, p53, p54, p55⟩ := capPh_pos
  obtain ⟨hDK, -, -⟩ := capD_congr (h.mono (by omega))
  obtain ⟨hz, -, hI, -, -⟩ := capZeta_congr (h.mono (by omega))
  obtain ⟨hA, hon⟩ := capA_congr (h.mono (by omega))
  have hzz : zK es = zK es' := by simp only [zK, kAt, ansAt, h (phStart4 55) (by omega)]
  have eA : aAt es = aAt es' := funext hA
  have hIIL : capIIL es (aAt es) = capIIL es' (aAt es') := by unfold capIIL; rw [eA, hzz]
  have hIIR : capIIR es = capIIR es' := by
    unfold capIIR sumR
    refine sum_congr rfl fun i hi => sum_congr rfl fun q hq => ?_
    dsimp only
    rw [(hDK i (mem_range.1 hi) q (mem_range.1 hq)).2, hz, hzz]
  refine ⟨hzz, ?_, ?_⟩
  · unfold capChk4
    rw [hIIL, hIIR, (hI loD 0).1, (hI hiD 0).1, (hI loD (aAt es)).2, (hI hiD (aAt es)).2, eA]
  · unfold DZ; rw [hon, hIIL, hIIR]

/-! ## The two counts (`hsingle` at phases 53 and 55) -/

open Classical in
/-- **The `ζ` row**: at `CapZeta`'s squeeze, with `D` false, at most `870` answers make (I) vanish
at the honest weights. -/
theorem card_dZeta {es : Log} (hl : es.length = phStart4 53) (ht : ¬ truthCap es) :
    (univ.filter fun a => capSig0 (ext1 es a)).card ≤ 870 := by
  obtain ⟨p52, p53, -⟩ := capPh_pos
  have hag : ∀ a, Agree (ext1 es a) es (phStart4 53) := fun a => by
    rw [ext1]; exact agree_append es _ hl.ge
  have hζ : ∀ a, zetaK (ext1 es a) = chK a := fun a => by rw [zetaK, ← hl, kAt_ext1]
  have hS : ∀ a hf, capIL hf (ext1 es a) - capIR hf (ext1 es a) (aHat (ext1 es a)) =
      sigP hf es (chK a) := fun a hf => by
    rw [capI_sub, hζ]
    unfold sigP sumR
    obtain ⟨hDK, hC, -⟩ := capD_congr (hag a)
    refine sum_congr rfl fun i hi => sum_congr rfl fun q hq => ?_
    dsimp only
    rw [(hDK i (mem_range.1 hi) q (mem_range.1 hq)).1, (hDK i (mem_range.1 hi) q (mem_range.1 hq)).2,
      hC i (mem_range.1 hi)]
  have hsig : ∀ a, capSig0 (ext1 es a) → sigP loD es (chK a) = 0 ∧ sigP hiD es (chK a) = 0 :=
    fun a h => ⟨by rw [← hS, h.1, sub_self], by rw [← hS, h.2, sub_self]⟩
  simp only [truthCap, not_forall] at ht
  obtain ⟨i, hi, q, hq, hne⟩ := ht
  have hmem : (⟨i, q⟩ : Σ _ : ℕ, ℕ) ∈ (range 5).sigma (fun i => range (tq i)) := by
    simp [hi, hq]
  have hinj : Set.InjOn (fun x : Σ _ : ℕ, ℕ => rdIx x.1 x.2) ((range 5).sigma fun i => range (tq i)) := by
    rintro ⟨i₁, q₁⟩ h₁ ⟨i₂, q₂⟩ h₂ he
    simp only [coe_sigma, Set.mem_sigma_iff, coe_range, Set.mem_Iio] at h₁ h₂
    obtain ⟨rfl, rfl⟩ := rdIx_inj h₁.1 h₁.2 h₂.1 h₂.2 he
    rfl
  have hle : ∀ x ∈ (range 5).sigma (fun i => range (tq i)), (fun x : Σ _ : ℕ, ℕ => rdIx x.1 x.2) x ≤ 870 := by
    rintro ⟨i₁, q₁⟩ h₁
    simp only [mem_sigma, mem_range] at h₁
    exact rdIx_le h₁.1 h₁.2
  by_cases hlo : loD (dAt es i q) = loD (capDig es i (kCap es i q))
  · have hhi : hiD (dAt es i q) ≠ hiD (capDig es i (kCap es i q)) := fun hh => hne (digest_halves hlo hh)
    refine le_trans (card_le_card fun a ha => ?_) (card_poly_root _ _
      (fun x : Σ _ : ℕ, ℕ => algebraMap F K (hiD (dAt es x.1 x.2) - hiD (capDig es x.1 (kCap es x.1 x.2))))
      hinj hle hmem ?_)
    · simp only [mem_filter, mem_univ, true_and] at ha ⊢
      have := (hsig a ha).2
      rwa [sigP, sumR_sigma] at this
    · simpa [sub_eq_zero] using hhi
  · refine le_trans (card_le_card fun a ha => ?_) (card_poly_root _ _
      (fun x : Σ _ : ℕ, ℕ => algebraMap F K (loD (dAt es x.1 x.2) - loD (capDig es x.1 (kCap es x.1 x.2))))
      hinj hle hmem ?_)
    · simp only [mem_filter, mem_univ, true_and] at ha ⊢
      have := (hsig a ha).1
      rwa [sigP, sumR_sigma] at this
    · simpa [sub_eq_zero] using hlo

open Classical in
/-- **The `z` row**: at `CapChkZ`'s squeeze, with `A` dishonest, at most `1,535` answers make (II)
hold. -/
theorem card_dZ {es : Log} (hl : es.length = phStart4 55) (ha : ¬ aHon es) :
    (univ.filter fun a => capIIL (ext1 es a) (aAt (ext1 es a)) = capIIR (ext1 es a)).card ≤ 1535 := by
  obtain ⟨p52, p53, p54, p55⟩ := capPh_pos
  have hag : ∀ a, Agree (ext1 es a) es (phStart4 55) := fun a => by
    rw [ext1]; exact agree_append es _ hl.ge
  have hzz : ∀ a, zK (ext1 es a) = chK a := fun a => by rw [zK, ← hl, kAt_ext1]
  simp only [aHon, not_forall] at ha
  obtain ⟨k, hk, hne⟩ := ha
  have hn : nE = 1536 := cOff_vals.2.2.2.2.2.2
  refine le_trans (card_le_card fun a hm => ?_) (card_poly_root (range nE) id
    (fun k => aAt es k - aHat es k) (fun _ _ _ _ h => h) (fun x hx => by
      simp only [mem_range] at hx; simp only [id]; omega) (mem_range.2 hk) (sub_ne_zero.2 hne))
  simp only [mem_filter, mem_univ, true_and] at hm ⊢
  obtain ⟨hA, -⟩ := capA_congr (hag a)
  obtain ⟨-, hH, -⟩ := capZeta_congr ((hag a).mono (by omega))
  have := capII_sub (ext1 es a)
  rw [hm, sub_self, hzz] at this
  simp only [hA, hH, id] at this
  exact this.symm

/-! ## Controls -/

/-- **`capChk_pos` (+)**: an honest prover passes the cap check: with `D` the caps' entries
(`truthCap`) and `A` the honest weights (`aHon`), V's three asserts hold (the check is complete). -/
theorem capChk_pos {es : Log} (ht : truthCap es) (ha : aHon es) : capChk4 es := by
  have hA : ∀ hf : Digest → F, capIR hf es (aAt es) = capIR hf es (aHat es) := fun hf =>
    sum_congr rfl fun k hk => by rw [ha k (mem_range.1 hk)]
  have h0 : ∀ hf : Digest → F, sigP hf es (zetaK es) = 0 := fun hf => by
    unfold sigP sumR
    refine sum_eq_zero fun i hi => sum_eq_zero fun q hq => ?_
    dsimp only
    rw [ht i (mem_range.1 hi) q (mem_range.1 hq), sub_self, map_zero, zero_mul]
  refine ⟨?_, ?_, ?_⟩
  · rw [hA, ← sub_eq_zero, capI_sub, h0]
  · rw [hA, ← sub_eq_zero, capI_sub, h0]
  · rw [← sub_eq_zero, capII_sub]
    exact sum_eq_zero fun k hk => by rw [ha k (mem_range.1 hk), sub_self, zero_mul]

open Classical in
/-- **`capChk_neg` (−)**: a wrong `A` fails (II) at some `z`: at `CapChkZ`'s squeeze, with `A` dishonest,
some answer makes (II) fail (at most `1,535` of the `2^256` make it hold, `card_dZ`). -/
theorem capChk_neg {es : Log} (hl : es.length = phStart4 55) (ha : ¬ aHon es) :
    ∃ a : Digest, ¬ capChk4 (ext1 es a) := by
  by_contra hall
  simp only [not_exists, not_not] at hall
  have hc := card_dZ hl ha
  rw [filter_true_of_mem fun a _ => (hall a).2.2, card_univ] at hc
  have : Fintype.card Digest = 2 ^ 256 := by
    rw [Fintype.card_congr chKEquiv]; exact (K.card_K)
  omega

open Classical in
/-- **`dZeta_neg` (−)**: a false `D` is not an escape at every `ζ`: some answer leaves (I) at the
honest weights nonzero (at most `870` roots, `card_dZeta`). -/
theorem dZeta_neg {es : Log} (hl : es.length = phStart4 53) (ht : ¬ truthCap es) :
    ∃ a : Digest, ¬ DZeta (ext1 es a) := by
  by_contra hall
  simp only [not_exists, not_not] at hall
  have hc := card_dZeta hl ht
  rw [filter_true_of_mem fun a _ => (hall a).2, card_univ] at hc
  have : Fintype.card Digest = 2 ^ 256 := by
    rw [Fintype.card_congr chKEquiv]; exact (K.card_K)
  omega

/-- **`dZeta_ctl` (+)**: the `ζ` escape set is exactly a root of (I)'s polynomial: on `CapZeta`'s
answer `a`, with `D` false, `DZeta` holds iff `chK a` is a common root of `sigP loD`, `sigP hiD`
(the polynomials of degree `≤ 870` the count bounds). -/
theorem dZeta_ctl {es : Log} (hl : es.length = phStart4 53) (a : Digest) :
    DZeta (ext1 es a) ↔ ¬ truthCap es ∧ sigP loD es (chK a) = 0 ∧ sigP hiD es (chK a) = 0 := by
  have hag : Agree (ext1 es a) es (phStart4 53) := by rw [ext1]; exact agree_append es _ hl.ge
  obtain ⟨hDK, hC, ht⟩ := capD_congr hag
  have hζ : zetaK (ext1 es a) = chK a := by rw [zetaK, ← hl, kAt_ext1]
  have hS : ∀ hf, capIL hf (ext1 es a) - capIR hf (ext1 es a) (aHat (ext1 es a)) = sigP hf es (chK a) :=
    fun hf => by
      rw [capI_sub, hζ]
      unfold sigP sumR
      refine sum_congr rfl fun i hi => sum_congr rfl fun q hq => ?_
      dsimp only
      rw [(hDK i (mem_range.1 hi) q (mem_range.1 hq)).1, (hDK i (mem_range.1 hi) q (mem_range.1 hq)).2,
        hC i (mem_range.1 hi)]
  unfold DZeta capSig0
  rw [ht, ← sub_eq_zero (a := capIL loD _), hS, ← sub_eq_zero (a := capIL hiD _), hS]

/-- **`dz_ctl` (+)**: the `z` escape set is exactly a root of (II)'s polynomial: on `CapChkZ`'s
answer, with `A` dishonest, `DZ` holds iff `chK a` is a root of `Σ_k (A_k − Â_k)·X^k`. -/
theorem dz_ctl {es : Log} (hl : es.length = phStart4 55) (a : Digest) :
    DZ (ext1 es a) ↔ ¬ aHon es ∧ ∑ k ∈ range nE, (aAt es k - aHat es k) * chK a ^ k = 0 := by
  have hag : Agree (ext1 es a) es (phStart4 55) := by rw [ext1]; exact agree_append es _ hl.ge
  obtain ⟨hA, hon⟩ := capA_congr hag
  obtain ⟨-, hH, -⟩ := capZeta_congr (hag.mono (by have := capPh_pos; omega))
  have hz : zK (ext1 es a) = chK a := by rw [zK, ← hl, kAt_ext1]
  unfold DZ
  rw [hon, ← sub_eq_zero, capII_sub, hz]
  simp only [hA, hH]

end FR.Snd.T4
