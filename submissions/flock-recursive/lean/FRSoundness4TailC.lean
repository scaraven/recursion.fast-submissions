-- G6: this module also holds the former modules `FRSoundness4Tail`, `FRSoundness4TailCap`, `FRSoundness4TailD`, `FRSoundness4TailO`, `FRSoundness4TailM` (one section each, in import order).
import FRSoundness4TailFold

section G6_FRSoundness4Tail

-- New for `flock-recursive` (BLUEPRINT §5.1, §5.4, A.10; stage T4, S-G13 route C): a copy-port of
-- `FRSoundnessTail` to revision 4.1's item sequence `seq4` (namespace `FR.Snd.T4`, see `FRSoundness4TailStep`):
-- the declarations that read positions, chains or the kind are copied, the rest is imported.

/-!
# The tail positions and `Same` at `seq4` (T4)

The 3.x declarations of `FRSoundnessTail` that read the positions, the chains or the kind, restated in
`FR.Snd.T4` over `fsItems4`/`phStart4`/`fsRnd4`, `G.Matches`/`G.IsChain` and `CKind`
(`kindOfC`, `CKind.lv`). Positions from P1.0 on are 3.x's plus 14 (`phStart4_shift`); the kind
enters through the ladder `lvOf κ.m` only. Changes beyond the renaming are marked `T4:`.
-/

/-! # Port of `FRSoundnessTail` (its module doc describes the 3.x original) -/

namespace FR.Snd.T4
open RecursionFast FR.Merkle Finset

set_option linter.constructorNameAsVariable false

/-! ## Part A: positions -/

/-- C.i's absorb (the next cap or the final message), P2.i's entry. -/
def cStart (i : ℕ) : ℕ := phStart4 (27 + 5 * i)

/-- P3.i's entry (P2.i's last answer). -/
def p3S0 (i : ℕ) : ℕ := phStart4 (30 + 5 * i) - 1

/-- Pf's first absorb. -/
def pfStart : ℕ := phStart4 51

/-- The first position after P3.i (P1.(i+1)'s first absorb, or Pf's). -/
def nxStart (i : ℕ) : ℕ := if i < 4 then p1Start (i + 1) else pfStart

theorem capPos_succ (i : ℕ) : capPos (i + 1) = cStart i := by
  simp only [capPos, cStart, Nat.add_one_ne_zero, ite_false]; congr 1; ring

theorem tail_pos_check : (List.range 5).all (fun i => decide (capPos i < p1Start i) &&
    decide (1 ≤ p1Start i) && decide (p1Start i + 2 * hEll i = cStart i) &&
    decide (cStart i + (lvlStar i).sq = p3S0 i) && decide (p3S0 i + 6 = nxStart i)) = true := by
  unfold nxStart p1Start pfStart cStart p3S0 capPos hEll phStart4; rw [fsStarts4_eq]; decide

theorem tail_pos {i : ℕ} (hi : i < 5) : capPos i < p1Start i ∧ 1 ≤ p1Start i ∧
    p1Start i + 2 * hEll i = cStart i ∧ cStart i + (lvlStar i).sq = p3S0 i ∧
      p3S0 i + 6 = nxStart i := by
  have h := tail_pos_check
  simp only [List.all_eq_true, List.mem_range, Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩ := h i hi
  exact ⟨h1, h2, h3, h4, h5⟩

theorem pfStart_eq : pfStart = 468 := by unfold pfStart phStart4; rw [fsStarts4_eq]; rfl

theorem p1Start_lt_nx {i : ℕ} (hi : i < 5) : p1Start i < nxStart i := by
  obtain ⟨-, -, h3, h4, h5⟩ := tail_pos hi; omega

theorem nxStart_le {i : ℕ} (hi : i + 1 < 5) : nxStart i = p1Start (i + 1) := by
  simp [nxStart, show i < 4 by omega]

/-! ## Part B: reads -/

/-- **The pairs `(L, es)` and `(L', es')` read the same before position `p`**: the chain entries,
and the level words whose caps lie before `p`. -/
def Same (L es L' es' : Log) (p : ℕ) : Prop :=
  Agree es es' p ∧ ∀ κ, ∀ i < 5, capPos i < p → wordK κ L es i = wordK κ L' es' i

variable {L es L' es' : Log} {p : ℕ}

theorem Same.mono (h : Same L es L' es' p) {q : ℕ} (hq : q ≤ p) : Same L es L' es' q :=
  ⟨h.1.mono hq, fun κ i hi hc => h.2 κ i hi (by omega)⟩

theorem same_of_agree (L : Log) (h : Agree es es' p) : Same L es L es' p :=
  ⟨h, fun κ i _ hc => by
    funext r j; simp only [wordK, wordOf, colOf_congr κ L i j (h.mono (by omega))]⟩

theorem same_append (L es : Log) (xs : Log) : Same L (es ++ xs) L es es.length :=
  same_of_agree L (agree_append es xs le_rfl)

theorem Same.kind (h : Same L es L' es' p) (hp : 1 ≤ p) : kindOfC es = kindOfC es' :=
  kindOfC_congr (h.1.mono hp)

/-- On a `StabExt` extension, the charging log and the whole log read the same. -/
theorem same_stabX (hb : ¬ Bad L) {n : ℕ} (hci : G.IsChain L n) {X : Log}
    (hX : StabExt fsRnd4 (entriesOf L (pathOf L n)) X) : Same (L.take n) X L X X.length :=
  ⟨fun _ _ => rfl, fun κ _ hi hc => wordK_stabX hb hci hX hi κ hc⟩

section Reads

variable (h : Same L es L' es' p) {i : ℕ} (hi : i < 5) (κ : CKind)
include h

theorem sAt_same {l : ℕ} (hp : p1Start i + 2 * l + 2 ≤ p) : sAt es i l = sAt es' i l :=
  sAt_congr (h.1.mono hp)

theorem sAt_same_lt (hp : cStart i ≤ p) (hi : i < 5) :
    ∀ v < hEll i, sAt es i v = sAt es' i v := fun v hv =>
  sAt_same h (by have := (tail_pos hi).2.2.1; omega)

include hi

theorem wordK_same (hp : capPos i < p) : wordK κ L es i = wordK κ L' es' i := h.2 κ i hi hp

theorem farL_same (hp : capPos i < p) : farL κ L es i ↔ farL κ L' es' i := by
  simp only [farL, wordK_same h hi κ hp]

theorem decodeL_same (hp : capPos i < p) : decodeL κ L es i = decodeL κ L' es' i :=
  decodeL_congr (wordK_same h hi κ hp)

theorem msgOf_same (hp : capPos i < p) : msgOf κ L es i = msgOf κ L' es' i := by
  funext r x; simp only [msgOf, decodeL_same h hi κ hp]

theorem fTab_same (hp : capPos i < p) : fTab κ L es i = fTab κ L' es' i := by
  funext y; simp only [fTab, msgOf_same h hi κ hp]

theorem foldAt_same (hp : cStart i ≤ p) : foldAt κ L es i = foldAt κ L' es' i := by
  have hc := (tail_pos hi).1
  have h3 := (tail_pos hi).2.2.1
  funext j
  simp only [foldAt, wordK_same h hi κ (by omega), lvl_ell κ hi,
    eqBits_congr (sAt_same_lt h hp hi)]

theorem foldMsg_same (hp : cStart i ≤ p) : foldMsg κ L es i = foldMsg κ L' es' i := by
  have hc := (tail_pos hi).1
  have h3 := (tail_pos hi).2.2.1
  funext x
  simp only [foldMsg, msgOf_same h hi κ (by omega), lvl_ell κ hi,
    eqBits_congr (sAt_same_lt h hp hi)]

theorem nextMsg_same (hp : cStart i + 1 ≤ p) : nextMsg κ L es i = nextMsg κ L' es' i := by
  funext x
  unfold nextMsg
  by_cases hn : i + 1 < nLevels
  · have := msgOf_same h hn κ (by rw [capPos_succ]; omega)
    simp only [hn, ite_true, this]
  · simp only [hn, ite_false, finalAt, msgAt, entAt]
    have h4 : i = 4 := by unfold nLevels at hn; omega
    subst h4
    have h46 : cStart 4 = phStart4 47 := rfl
    have := h.1 (phStart4 47) (by omega)
    simp only [entAt] at this
    rw [this]

theorem consSet_same (hp : cStart i + 1 ≤ p) : consSet κ L es i = consSet κ L' es' i := by
  simp only [consSet, foldAt_same h hi κ (by omega), nextMsg_same h hi κ hp]

theorem truthP2_same (hp : cStart i + 1 ≤ p) : truthP2 κ L es i ↔ truthP2 κ L' es' i := by
  simp only [truthP2, consSet_same h hi κ hp]

theorem truthC_same (hp : cStart i + 1 ≤ p) : truthC κ L es i ↔ truthC κ L' es' i := by
  simp only [truthC, foldMsg_same h hi κ (by omega), nextMsg_same h hi κ hp]

theorem qPos_same (hp : p3S0 i + 1 ≤ p) {q : ℕ} (hq : q < (CKind.lv κ i).t) :
    qPos κ es i q = qPos κ es' i q := by
  obtain ⟨hper, -, ht⟩ := p2_params κ i hi
  have h4 := (tail_pos hi).2.2.2.1
  have : q / (CKind.lv κ i).per < (lvlStar i).sq := (Nat.div_lt_iff_lt_mul hper).mpr (by omega)
  simp only [qPos, posAt, ansAt]
  rw [h.1 _ (by unfold cStart at h4; omega)]

theorem consErr_same (hp : p3S0 i + 1 ≤ p) {q : ℕ} (hq : q < (CKind.lv κ i).t) :
    consErr κ L es i q = consErr κ L' es' i q := by
  have h4 := (tail_pos hi).2.2.2.1
  simp only [consErr, foldAtN, qPos_same h hi κ hp hq, foldAt_same h hi κ (by omega),
    nextMsg_same h hi κ (by omega)]

theorem truthP3_same (hp : p3S0 i + 1 ≤ p) : truthP3 κ L es i ↔ truthP3 κ L' es' i :=
  forall₂_congr fun q hq => by rw [consErr_same h hi κ hp hq]

theorem kcAt_same (hp : nxStart i ≤ p) : ∀ v < 9, kcAt es i v = kcAt es' i v := by
  intro v hv
  have h5 := (tail_pos hi).2.2.2.2
  simp only [kcAt, coordAt, fAt, ansAt]
  rw [h.1 _ (by unfold p3S0 at h5; omega)]

theorem p3Batch_same (hp : nxStart i ≤ p) : p3Batch κ L es i = p3Batch κ L' es' i := by
  have h5 := (tail_pos hi).2.2.2.2
  refine sum_congr rfl fun q hq => ?_
  rw [eqBits_congr (kcAt_same h hi hp), consErr_same h hi κ (by omega) (mem_range.1 hq)]

theorem vNext_same (hp : nxStart i ≤ p) (c : K) : vNext κ L es i c = vNext κ L' es' i c := by
  have h5 := (tail_pos hi).2.2.2.2
  have h4 := (tail_pos hi).2.2.2.1
  unfold vNext
  exact congrArg (c + ·) (sum_congr rfl fun q hq => by
    rw [eqBits_congr (kcAt_same h hi hp), qPos_same h hi κ (by omega) (mem_range.1 hq),
      foldAtN, foldAtN, foldAt_same h hi κ (by omega)])

theorem wNext_same (hp : nxStart i ≤ p) (Wf : ℕ → K) : wNext κ es i Wf = wNext κ es' i Wf := by
  have h5 := (tail_pos hi).2.2.2.2
  funext x
  unfold wNext
  exact congrArg (Wf x + ·) (sum_congr rfl fun q hq => by
    rw [eqBits_congr (kcAt_same h hi hp), qPos_same h hi κ (by omega) (mem_range.1 hq)])

theorem foldW_same (hp : cStart i ≤ p) (W : ℕ → K) :
    foldW (CKind.lv κ i).ell (sAt es i) W = foldW (CKind.lv κ i).ell (sAt es' i) W := by
  funext x; simp only [foldW, lvl_ell κ hi, eqBits_congr (sAt_same_lt h hp hi)]

theorem nextW_same (hp : nxStart i ≤ p) (W : ℕ → K) : nextW κ es i W = nextW κ es' i W := by
  obtain ⟨-, -, -, h4, h5⟩ := tail_pos hi
  rw [nextW, nextW, foldW_same h hi κ (by omega), wNext_same h hi κ hp]

end Reads

/-! ## Part C: the level chain -/

/-- P1.i's variables: the `ℓᵢ` row bits (the rounds), then level `i`'s message bits. -/
def nrP (i : ℕ) (κ : CKind) : ℕ := (CKind.lv κ i).ell + mLog κ i

end FR.Snd.T4

end G6_FRSoundness4Tail

section G6_FRSoundness4TailCap

-- New for `flock-recursive` (PACK-4.4 §11.1, §11.5, `reviews/PACK-4.4-b2-review.md` PB-M1; track A3′
-- run 2): the batched cap check (β′) on the log.

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

end G6_FRSoundness4TailCap

section G6_FRSoundness4TailD

-- New for `flock-recursive` (BLUEPRINT §5.1, §5.4, A.10; stage T4, S-G13 route C): a copy-port of
-- `FRSoundnessTailD` to revision 4.1's item sequence `seq4` (namespace `FR.Snd.T4`, see `FRSoundness4TailStep`):
-- the declarations that read positions, chains or the kind are copied, the rest is imported.

/-!
# The tail dooms at `seq4` (T4)

The 3.x declarations of `FRSoundnessTailD` that read the positions, the chains or the kind, restated in
`FR.Snd.T4` over `fsItems4`/`phStart4`/`fsRnd4`, `G.Matches`/`G.IsChain` and `CKind`
(`kindOfC`, `CKind.lv`). Positions from P1.0 on are 3.x's plus 14 (`phStart4_shift`); the kind
enters through the ladder `lvOf κ.m` only. Changes beyond the renaming are marked `T4:`.
-/

/-! # Port of `FRSoundnessTailD` (its module doc describes the 3.x original) -/

namespace FR.Snd.T4
open RecursionFast FR.Merkle Finset

set_option linter.constructorNameAsVariable false

/-- **What the front hands the tail** reads only what lies before P1.0. -/
def FrontLocal (W₀ : Log → Log → ℕ → K) (c₀ : Log → Log → K) : Prop :=
  ∀ L es L' es' p, Same L es L' es' p → p1Start 0 ≤ p → W₀ L es = W₀ L' es' ∧ c₀ L es = c₀ L' es'

/-! ## Part A: the level chain -/

section Chain

variable (W₀ : Log → Log → ℕ → K) (c₀ : Log → Log → K)

/-- Level `i`'s weight table. -/
noncomputable def lvW : ℕ → Log → Log → ℕ → K
  | 0 => W₀
  | i + 1 => fun L es => nextW (kindOfC es) es i (lvW i L es)

/-- Level `i`'s initial claim (P1.i's; `lvC 5` is Pf's: P1.4's final claim, as `finP 4` asserts). -/
noncomputable def lvC : ℕ → Log → Log → K
  | 0 => c₀
  | i + 1 => fun L es =>
    if i < 4 then vNext (kindOfC es) L es i (clR2 (p1Start i) 32 readK chK (lvC i) L es (hEll i))
    else clR2 (p1Start i) 32 readK chK (lvC i) L es (hEll i)

/-- P1.i's final claim (after its `ℓᵢ` rounds). -/
noncomputable def c1 (i : ℕ) (L es : Log) : K :=
  clR2 (p1Start i) 32 readK chK (lvC c₀ i) L es (hEll i)

/-- P1.i's tables `[Wᵢ, f⁽ⁱ⁾]` over `ℓᵢ + mLog` variables. -/
noncomputable def lvT (i : ℕ) (L es : Log) : Array (Array K) :=
  tabs (lvW W₀ i L es) (fTab (kindOfC es) L es i) (nrP i (kindOfC es))

/-- Level `i`'s table bound at P1.i's challenges. -/
noncomputable def wFold (i : ℕ) (L es : Log) : ℕ → K :=
  foldW (CKind.lv (kindOfC es) i).ell (sAt es i) (lvW W₀ i L es)

/-- The folded claim's truth `⟨foldW Wᵢ, fold_z(f⁽ⁱ⁾)⟩`. -/
noncomputable def foldSum (i : ℕ) (L es : Log) : K :=
  ∑ x ∈ range (2 ^ mLog (kindOfC es) i), wFold W₀ i L es x * foldMsg (kindOfC es) L es i x

/-- Pf's weight: level 4's folded table, zero past its `2^mLog` message (`P30`/`N30`: `2^5`). -/
noncomputable def wPf (L es : Log) (x : ℕ) : K :=
  if x < 2 ^ mLog (kindOfC es) 4 then wFold W₀ 4 L es x else 0

/-- Pf's tables `[W_f, final]` over 7 variables. -/
noncomputable def tPf (L es : Log) : Array (Array K) := tabs (wPf W₀ L es) (finalAt es) 7

/-- Level `i`'s start (`pfStart` for `i = 5`). -/
def lvB (i : ℕ) : ℕ := if i < 5 then p1Start i else pfStart

theorem lvB_succ {i : ℕ} (hi : i < 5) : lvB (i + 1) = nxStart i := by
  unfold lvB nxStart; split_ifs <;> omega

theorem lvB_lt {i : ℕ} (hi : i < 5) : lvB i < lvB (i + 1) := by
  rw [lvB_succ hi]; simp only [lvB, hi, ite_true]; exact p1Start_lt_nx hi

variable {W₀ c₀}

/-- **The level chain reads only what lies before the level's start.** -/
theorem chain_same (hF : FrontLocal W₀ c₀) : ∀ i ≤ 5, ∀ {L es L' es' : Log} {p : ℕ},
    Same L es L' es' p → lvB i ≤ p →
      lvW W₀ i L es = lvW W₀ i L' es' ∧ lvC c₀ i L es = lvC c₀ i L' es'
  | 0, _, _, _, _, _, _, h, hp => hF _ _ _ _ _ h hp
  | i + 1, hi, L, es, L', es', p, h, hp => by
    have hi' : i < 5 := by omega
    have hlt := lvB_lt hi'
    obtain ⟨hW, hC⟩ := chain_same hF i (by omega) h (by omega)
    have hb : lvB i = p1Start i := by simp [lvB, hi']
    have h1 : 1 ≤ p := by have := (tail_pos hi').2.1; omega
    have hk := h.kind h1
    have hnx : nxStart i ≤ p := lvB_succ hi' ▸ hp
    obtain ⟨-, -, h3, h4, h5⟩ := tail_pos hi'
    refine ⟨?_, ?_⟩
    · show nextW (kindOfC es) es i (lvW W₀ i L es) = nextW (kindOfC es') es' i (lvW W₀ i L' es')
      rw [hW, hk, nextW_same h hi' _ hnx]
    · show (if i < 4 then vNext (kindOfC es) L es i
            (clR2 (p1Start i) 32 readK chK (lvC c₀ i) L es (hEll i))
          else clR2 (p1Start i) 32 readK chK (lvC c₀ i) L es (hEll i)) =
        (if i < 4 then vNext (kindOfC es') L' es' i
            (clR2 (p1Start i) 32 readK chK (lvC c₀ i) L' es' (hEll i))
          else clR2 (p1Start i) 32 readK chK (lvC c₀ i) L' es' (hEll i))
      rw [clR2_same hC (h.1.mono (by omega)), hk, vNext_same h hi' _ hnx]

variable (hF : FrontLocal W₀ c₀) {L es L' es' : Log} {p : ℕ} (h : Same L es L' es' p) {i : ℕ}
  (hi : i < 5)
include hF h hi

theorem lvW_same (hp : p1Start i ≤ p) : lvW W₀ i L es = lvW W₀ i L' es' :=
  (chain_same hF i (by omega) h (by simp [lvB, hi]; exact hp)).1

theorem lvC_same (hp : p1Start i ≤ p) : lvC c₀ i L es = lvC c₀ i L' es' :=
  (chain_same hF i (by omega) h (by simp [lvB, hi]; exact hp)).2

theorem c1_same (hp : cStart i ≤ p) : c1 c₀ i L es = c1 c₀ i L' es' := by
  obtain ⟨-, -, h3, -, -⟩ := tail_pos hi
  exact clR2_same (lvC_same hF h hi (by omega)) (h.1.mono (by omega))

theorem lvT_same (hp : p1Start i ≤ p) : lvT W₀ i L es = lvT W₀ i L' es' := by
  obtain ⟨hc, h1, -, -, -⟩ := tail_pos hi
  rw [lvT, lvT, lvW_same hF h hi hp, h.kind (by omega), fTab_same h hi _ (by omega)]

theorem wFold_same (hp : cStart i ≤ p) : wFold W₀ i L es = wFold W₀ i L' es' := by
  obtain ⟨-, h1, h3, -, -⟩ := tail_pos hi
  rw [wFold, wFold, lvW_same hF h hi (by omega), h.kind (by omega), foldW_same h hi _ hp]

theorem foldSum_same (hp : cStart i ≤ p) : foldSum W₀ i L es = foldSum W₀ i L' es' := by
  obtain ⟨-, h1, h3, -, -⟩ := tail_pos hi
  rw [foldSum, foldSum, wFold_same hF h hi hp, h.kind (by omega),
    foldMsg_same h hi _ hp]

end Chain

section ChainPf

variable {W₀ : Log → Log → ℕ → K} {c₀ : Log → Log → K} (hF : FrontLocal W₀ c₀)
  {L es L' es' : Log} {p : ℕ} (h : Same L es L' es' p)
include hF h

theorem tPf_same (hp : pfStart ≤ p) : tPf W₀ L es = tPf W₀ L' es' := by
  have h5 := (tail_pos (show 4 < 5 by norm_num)).2.2.2.2
  have h4 := (tail_pos (show 4 < 5 by norm_num)).2.2.2.1
  have hnx : nxStart 4 = pfStart := rfl
  have h1 : 1 ≤ p := by have := (tail_pos (show 4 < 5 by norm_num)).2.1; omega
  have hk := h.kind h1
  have hw : wPf W₀ L es = wPf W₀ L' es' := by
    funext x
    simp only [wPf, hk, wFold_same hF h (show 4 < 5 by norm_num) (by omega)]
  have hf : finalAt es = finalAt es' := by
    funext x
    have h46 : cStart 4 = phStart4 47 := rfl
    simp only [finalAt, msgAt, entAt]
    have := h.1 (phStart4 47) (by omega)
    simp only [entAt] at this
    rw [this]
  rw [tPf, tPf, hw, hf]

theorem lvC5_same (hp : pfStart ≤ p) : lvC c₀ 5 L es = lvC c₀ 5 L' es' :=
  (chain_same hF 5 le_rfl h (by simpa [lvB] using hp)).2

end ChainPf

/-- Below level 4, level `i + 1`'s initial claim is P3.i's batched claim. -/
theorem lvC_succ (c₀ : Log → Log → K) {i : ℕ} (hi : i < 4) (L es : Log) :
    lvC c₀ (i + 1) L es = vNext (kindOfC es) L es i (c1 c₀ i L es) := by
  show (if i < 4 then vNext (kindOfC es) L es i (c1 c₀ i L es) else c1 c₀ i L es) = _
  exact ite_pos' hi _ _

/-- **Pf's initial claim is P1.4's final claim** (`finP 4`: `claim0 Pf = claimN P1.4`). -/
theorem lvC_five (c₀ : Log → Log → K) (L es : Log) : lvC c₀ 5 L es = c1 c₀ 4 L es := by
  show (if 4 < 4 then vNext (kindOfC es) L es 4 (c1 c₀ 4 L es) else c1 c₀ 4 L es) = _
  exact ite_neg' (by norm_num) _ _

theorem mLog4_le (κ : CKind) : mLog κ 4 ≤ 7 := by rcases κ with (_|_|_) | (_|_|_) <;> decide

/-! ## Part B: the dooms -/

section Dooms

variable (W₀ : Log → Log → ℕ → K) (c₀ : Log → Log → K)

/-- **P1.i's doom** (A.10): the fold so far is far, or the word is close and the asserted rounds'
running claim is false (`D2` over K, the check in `RejT`). -/
def D1 (i : ℕ) (L es : Log) : Prop :=
  ¬ closeP (kindOfC es) L es i (hRnd es i) ∨
    (¬ farL (kindOfC es) L es i ∧
      D2 (p1Start i) 32 readK chK (lvC c₀ i) (nrP i) e2 (lvT W₀ i) L es)

/-- **C.i's doom**: the next codeword is not close to the fold (`¬ truthP2`), or the word is close
and the folded claim is false. -/
def DCi (i : ℕ) (L es : Log) : Prop :=
  ¬ truthP2 (kindOfC es) L es i ∨
    (¬ farL (kindOfC es) L es i ∧ c1 c₀ i L es ≠ foldSum W₀ i L es)

/-- P2.i's final doom: a queried fold is inconsistent, or the word is close, the next message is
the fold and the folded claim is false. -/
def finP2 (i : ℕ) (L es : Log) : Prop :=
  ¬ truthP3 (kindOfC es) L es i ∨
    (¬ farL (kindOfC es) L es i ∧ truthC (kindOfC es) L es i ∧ c1 c₀ i L es ≠ foldSum W₀ i L es)

/-- **P2.i's doom** (`msD` over C.i's). -/
def DP2 (i : ℕ) : Log → Log → Prop :=
  msD (DCi W₀ c₀ i) (finP2 W₀ c₀ i) (cStart i) (lvlStar i).sq

/-- The next level's true claim (`⟨W_{i+1}, f⁽ⁱ⁺¹⁾⟩`; Pf's `⟨W_f, final⟩` for `i = 4`). -/
noncomputable def nxSum (i : ℕ) (L es : Log) : K :=
  if i < 4 then
    ∑ y ∈ range (2 ^ nrP (i + 1) (kindOfC es)), lvW W₀ (i + 1) L es y * fTab (kindOfC es) L es (i + 1) y
  else ∑ x ∈ range (2 ^ 7), wPf W₀ L es x * finalAt es x

/-- P3.i's final doom: the next level is far, or its initial claim is false (`i < 4`); P2.4's
final doom (`i = 4`: `finP 4` does not batch, so `κ_c⁽⁴⁾` changes nothing). -/
def finP3 (i : ℕ) (L es : Log) : Prop :=
  if i < 4 then farL (kindOfC es) L es (i + 1) ∨ lvC c₀ (i + 1) L es ≠ nxSum W₀ i L es
  else finP2 W₀ c₀ i L es

/-- **P3.i's doom** (`msD` over P2.i's). -/
def DP3 (i : ℕ) : Log → Log → Prop := msD (DP2 W₀ c₀ i) (finP3 W₀ c₀ i) (p3S0 i) 5

/-- **Pf's doom**: a queried level-4 fold is not the final codeword's symbol (`finP 4`'s direct
check fails), or `D2` over K, 7 rounds, from P1.4's final claim. -/
def DPf (L es : Log) : Prop :=
  ¬ truthP3 (kindOfC es) L es 4 ∨
    D2 pfStart 32 readK chK (lvC c₀ 5) (fun _ => 7) e2 (tPf W₀) L es

/-! ### The cap check's dooms (revision 4.4.1, (β′); PB-M1's chain)

`D` is absorbed at phase 52, `ζ` squeezed at 53, `A` absorbed at 54, `z` squeezed at 55. The Pf doom is
carried while `D` is true (`truthCap`); a false `D` is a doom from phase 52 on, which `ζ` keeps only off
`DZeta` (charged `≤ 870` answers) and `z` keeps only off `DZ` (`≤ 1,535`). On an accepted chain (V's
three asserts, `capChk4`) none of the last phase's disjuncts holds (`not_DCapZ_of_chk`). -/

/-- **Phase 52 (`CapD`)**: Pf's doom, or a false `D`. -/
def DCapD (L es : Log) : Prop := DPf W₀ c₀ L es ∨ ¬ truthCap es

/-- **Phase 53 (`CapZeta`)**: Pf's doom on a true `D`, or a false `D` whose (I) at the honest weights
does not vanish at `ζ`. -/
def DCapZeta (L es : Log) : Prop :=
  (DPf W₀ c₀ L es ∧ truthCap es) ∨ (¬ truthCap es ∧ ¬ capSig0 es)

/-- **Phase 54 (`CapChk`)**: as 53 with `A` honest, or `A` dishonest. -/
def DCapA (L es : Log) : Prop :=
  (DPf W₀ c₀ L es ∧ truthCap es) ∨ (aHon es ∧ ¬ truthCap es ∧ ¬ capSig0 es) ∨ ¬ aHon es

/-- **Phase 55 (`CapChkZ`)**: as 54, a dishonest `A` doomed only if (II) fails at `z`. -/
def DCapZ (L es : Log) : Prop :=
  (DPf W₀ c₀ L es ∧ truthCap es) ∨ (aHon es ∧ ¬ truthCap es ∧ ¬ capSig0 es) ∨
    (¬ aHon es ∧ capIIL es (aAt es) ≠ capIIR es)

/-- The cap check's phase dooms (`k = 52 … 55`). -/
def DCap (k : ℕ) : Log → Log → Prop :=
  if k = 52 then DCapD W₀ c₀ else if k = 53 then DCapZeta W₀ c₀ else if k = 54 then DCapA W₀ c₀
  else DCapZ W₀ c₀

/-- The level phases' dooms (`k = 26 + 5i + t`: P1.i, C.i, P2.i, Q, P3.i). -/
def DTl (k : ℕ) : Log → Log → Prop :=
  if (k - 26) % 5 = 0 then D1 W₀ c₀ ((k - 26) / 5)
  else if (k - 26) % 5 = 1 then DCi W₀ c₀ ((k - 26) / 5)
  else if (k - 26) % 5 = 2 then DP2 W₀ c₀ ((k - 26) / 5)
  else if (k - 26) % 5 = 3 then fun _ _ => False
  else DP3 W₀ c₀ ((k - 26) / 5)

/-- **The tail's phase dooms**: the levels' (`26 … 50`), Pf's (`51`), the cap check's (`52 … 55`). -/
def DT (k : ℕ) : Log → Log → Prop :=
  if k = 51 then DPf W₀ c₀ else if 51 < k then DCap W₀ c₀ k else DTl W₀ c₀ k

theorem DT_lvl {k : ℕ} (hk : k < 51) : DT W₀ c₀ k = DTl W₀ c₀ k := by
  unfold DT; rw [ite_neg' (by omega), ite_neg' (by omega)]

theorem DT_cap : DT W₀ c₀ 52 = DCapD W₀ c₀ ∧ DT W₀ c₀ 53 = DCapZeta W₀ c₀ ∧
    DT W₀ c₀ 54 = DCapA W₀ c₀ ∧ DT W₀ c₀ 55 = DCapZ W₀ c₀ := by
  unfold DT DCap; simp

variable {i : ℕ} (hi : i < 5)
include hi

theorem DT_P1 : DT W₀ c₀ (26 + 5 * i) = D1 W₀ c₀ i := by
  rw [DT_lvl W₀ c₀ (by omega)]; unfold DTl
  rw [ite_pos' (by omega), show (26 + 5 * i - 26) / 5 = i by omega]

theorem DT_C : DT W₀ c₀ (27 + 5 * i) = DCi W₀ c₀ i := by
  rw [DT_lvl W₀ c₀ (by omega)]; unfold DTl
  rw [ite_neg' (by omega), ite_pos' (by omega),
    show (27 + 5 * i - 26) / 5 = i by omega]

theorem DT_P2 : DT W₀ c₀ (28 + 5 * i) = DP2 W₀ c₀ i := by
  rw [DT_lvl W₀ c₀ (by omega)]; unfold DTl
  rw [ite_neg' (by omega), ite_neg' (by omega), ite_pos' (by omega),
    show (28 + 5 * i - 26) / 5 = i by omega]

theorem DT_P3 : DT W₀ c₀ (30 + 5 * i) = DP3 W₀ c₀ i := by
  rw [DT_lvl W₀ c₀ (by omega)]; unfold DTl
  rw [ite_neg' (by omega), ite_neg' (by omega), ite_neg' (by omega),
    ite_neg' (by omega), show (30 + 5 * i - 26) / 5 = i by omega]

omit hi in
theorem DT_Pf : DT W₀ c₀ 51 = DPf W₀ c₀ := by unfold DT; rw [ite_pos' rfl]

end Dooms

/-! ## Part C: the asserted checks -/

/-- **The tail's asserted round checks**: some answered round of P1.i or Pf fails
`g(0) + g(1) = claim`. -/
def RejT (c₀ : Log → Log → K) (L es : Log) : Prop :=
  (∃ i < 5, ∃ j < hEll i, p1Start i + 2 * j < es.length ∧
    ¬ Chk2 (p1Start i) 32 readK chK (lvC c₀ i) L es j) ∨
  (∃ j < 7, pfStart + 2 * j < es.length ∧ ¬ Chk2 pfStart 32 readK chK (lvC c₀ 5) L es j)

theorem chk2_same {b : ℕ} {c0 : Log → Log → K} {L L' es es' : Log} {p : ℕ}
    (h : Same L es L' es' p) {j : ℕ} (hj : b + 2 * j < p) (hc : c0 L es = c0 L' es') :
    Chk2 b 32 readK chK c0 L es j ↔ Chk2 b 32 readK chK c0 L' es' j := by
  have hg : g2At b 32 readK es j = g2At b 32 readK es' j := by
    simp only [g2At, msgAt, h.1 (b + 2 * j) hj]
  simp only [Chk2, hg, clR2_same hc (h.1.mono (by omega) : Agree es es' (b + 2 * j))]

/-! ## Part D: the position facts -/

/-- Checked: phase `phOf4 p`'s first position is at most `p`, and `p` lies before the next phase's
(`p < 486`, the chain's length). -/
theorem phOf_check : (List.range 486).all (fun p => decide (phStart4 (phOf4 p) ≤ p) &&
    decide (phOf4 p ≤ 55) && (decide (phOf4 p = 55) || decide (p < phStart4 (phOf4 p + 1)))) = true := by
  unfold phOf4 phStart4; rw [fsStarts4_eq]; decide +kernel

/-- **The last phases' positions** (`fsStarts4`): Pf from `pfStart` (468) to the `CapD` absorb, then
one position per cap-check phase. -/
theorem phOf_ge {p : ℕ} (hp : pfStart ≤ p) :
    (p < phStart4 52 → phOf4 p = 51) ∧ (p = phStart4 52 → phOf4 p = 52) ∧
      (p = phStart4 53 → phOf4 p = 53) ∧ (p = phStart4 54 → phOf4 p = 54) ∧
      (phStart4 55 ≤ p → phOf4 p = 55) := by
  have hf : 485 ≤ p → (fsStarts4.filter (· ≤ p)).length = fsStarts4.length := fun h =>
    congrArg List.length (List.filter_eq_self.mpr fun x hx => by
      rw [fsStarts4_eq] at hx; simp only [decide_eq_true_eq]; fin_cases hx <;> omega)
  have e : pfStart = 468 := by unfold pfStart phStart4; rw [fsStarts4_eq]; rfl
  obtain ⟨p52, p53, p54, p55⟩ := capPh_pos
  rw [e] at hp
  rw [p52, p53, p54, p55]
  refine ⟨fun h => ?_, fun h => ?_, fun h => ?_, fun h => ?_, fun h => ?_⟩
  · unfold phOf4; interval_cases p <;> rw [fsStarts4_eq] <;> rfl
  all_goals first
    | (subst h; unfold phOf4; rw [fsStarts4_eq]; rfl)
    | (unfold phOf4; rw [hf (by omega), fsStarts4_eq]; rfl)

/-- **The phase bounds**: `phStart4 (phOf4 p) ≤ p`, and before the last phase `p` lies before the
next phase's start. -/
theorem phOf_bounds (p : ℕ) : phStart4 (phOf4 p) ≤ p ∧ phOf4 p ≤ 55 ∧
    (phOf4 p < 55 → p < phStart4 (phOf4 p + 1)) := by
  by_cases hp : p < 486
  · have h := phOf_check
    simp only [List.all_eq_true, List.mem_range, Bool.and_eq_true, Bool.or_eq_true,
      decide_eq_true_eq] at h
    obtain ⟨⟨h1, h2⟩, h3⟩ := h p hp
    exact ⟨h1, h2, fun hl => h3.resolve_left (by omega)⟩
  · have e : pfStart = 468 := by unfold pfStart phStart4; rw [fsStarts4_eq]; rfl
    rw [(phOf_ge (p := p) (by omega)).2.2.2.2 (by rw [capPh_pos.2.2.2]; omega)]
    refine ⟨?_, le_rfl, fun h => absurd h (lt_irrefl _)⟩
    unfold phStart4; rw [fsStarts4_eq]; simp; omega

/-- Checked: the rounds of P1.0 … P1.4 and Pf alternate a 96-byte absorb and a squeeze; there
are 486 Fiat–Shamir items (revision 4.4.1: the cap check's four after Pf's). -/
theorem rounds_check : ((List.range 5).all (fun i => (List.range (hEll i)).all fun l =>
      fsItems4[p1Start i + 2 * l]? == some (.absorb 96) &&
        fsItems4[p1Start i + 2 * l + 1]? == some .squeeze) &&
    (List.range 7).all (fun l => fsItems4[pfStart + 2 * l]? == some (.absorb 96) &&
        fsItems4[pfStart + 2 * l + 1]? == some .squeeze) && fsItems4.length == 486) = true := by
  unfold p1Start pfStart hEll phStart4; rw [fsStarts4_eq]; decide +kernel

end FR.Snd.T4

end G6_FRSoundness4TailD

section G6_FRSoundness4TailO

-- New for `flock-recursive` (BLUEPRINT §5.1, §5.4, A.10; stage T4, S-G13 route C): a copy-port of
-- `FRSoundnessTailO` to revision 4.1's item sequence `seq4` (namespace `FR.Snd.T4`, see `FRSoundness4TailStep`):
-- the declarations that read positions, chains or the kind are copied, the rest is imported.

/-!
# The tail obligations (absorbs, single squeezes) at `seq4` (T4)

The 3.x declarations of `FRSoundnessTailO` that read the positions, the chains or the kind, restated in
`FR.Snd.T4` over `fsItems4`/`phStart4`/`fsRnd4`, `G.Matches`/`G.IsChain` and `CKind`
(`kindOfC`, `CKind.lv`). Positions from P1.0 on are 3.x's plus 14 (`phStart4_shift`); the kind
enters through the ladder `lvOf κ.m` only. Changes beyond the renaming are marked `T4:`.
-/

/-! # Port of `FRSoundnessTailO` (its module doc describes the 3.x original) -/

namespace FR.Snd.T4
open RecursionFast FR.Merkle Finset

set_option linter.constructorNameAsVariable false

/-! ## Part A: reads -/

theorem pf_same {L es L' es' : Log} {p : ℕ} (h : Same L es L' es' p) {i : ℕ} (hi : i < 5)
    (κ : CKind) {l : ℕ} (hl : p1Start i + 2 * l ≤ p) : pf κ L es i l = pf κ L' es' i l := by
  have hc := (tail_pos hi).1
  have he : ∀ u, eqBits (sAt es i) l u = eqBits (sAt es' i) l u :=
    eqBits_congr fun v hv => sAt_same h (by omega)
  funext r j
  simp only [pf, wN, wordK_same h hi κ (by omega), he]

theorem closeP_same {L es L' es' : Log} {p : ℕ} (h : Same L es L' es' p) {i : ℕ} (hi : i < 5)
    (κ : CKind) {l : ℕ} (hl : p1Start i + 2 * l ≤ p) :
    closeP κ L es i l ↔ closeP κ L' es' i l := by
  simp only [closeP, pf_same h hi κ hl]

theorem Same.take {L es L' es' : Log} {p : ℕ} (h : Same L es L' es' p) {m : ℕ} (hm : m ≤ p) :
    Same L (es.take m) L' (es'.take m) m := by
  have hA : Agree (es.take m) es m := fun q hq => entAt_take hq
  have hA' : Agree (es'.take m) es' m := fun q hq => entAt_take hq
  refine ⟨fun q hq => by rw [hA q hq, hA' q hq, h.1 q (by omega)], fun κ i hi hc => ?_⟩
  rw [(same_of_agree L hA).2 κ i hi hc, h.2 κ i hi (by omega), (same_of_agree L' hA').2 κ i hi hc]

theorem kindOf_ext (es₀ : Log) (as : List Digest) (h : 0 < es₀.length) :
    kindOfC (ext es₀ as) = kindOfC es₀ := kindOfC_congr ((agree_ext es₀ as).mono h)

variable {W₀ : Log → Log → ℕ → K} {c₀ : Log → Log → K}

theorem p1_local (hF : FrontLocal W₀ c₀) {i : ℕ} (hi : i < 5) :
    TruthLocal2 (p1Start i) (lvC c₀ i) (lvT W₀ i) := fun L _ _ h =>
  ⟨lvT_same hF (same_of_agree L h) hi le_rfl, lvC_same hF (same_of_agree L h) hi le_rfl⟩

theorem pf_local (hF : FrontLocal W₀ c₀) : TruthLocal2 pfStart (lvC c₀ 5) (tPf W₀) :=
  fun L _ _ h => ⟨tPf_same hF (same_of_agree L h) le_rfl, lvC5_same hF (same_of_agree L h) le_rfl⟩

theorem lvT_size (i : ℕ) (L es : Log) : ∀ t ∈ lvT W₀ i L es, t.size = 2 ^ nrP i (kindOfC es) :=
  tabs_size _ _ _

theorem tPf_size (L es : Log) : ∀ t ∈ tPf W₀ L es, t.size = 2 ^ 7 := tabs_size _ _ _

theorem rchs2_sAt (es : Log) (i l : ℕ) :
    rchs2 (p1Start i) chK es l = (List.range l).map (sAt es i) := rfl

theorem fold_fTab (κ : CKind) (L es : Log) (i x : ℕ) :
    ∑ u ∈ range (2 ^ (CKind.lv κ i).ell), eqBits (sAt es i) (CKind.lv κ i).ell u *
      fTab κ L es i (u + 2 ^ (CKind.lv κ i).ell * x) = foldMsg κ L es i x := by
  rw [foldMsg, ← Fin.sum_univ_eq_sum_range (fun u => eqBits (sAt es i) (CKind.lv κ i).ell u *
    fTab κ L es i (u + 2 ^ (CKind.lv κ i).ell * x))]
  refine sum_congr rfl fun u _ => ?_
  have hu := u.2
  simp only [fTab, Level.rows, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hu,
    Nat.add_mul_div_left _ _ (Nat.two_pow_pos _), Nat.div_eq_of_lt hu, zero_add]

/-- **P1.i's true sum after its `ℓᵢ` rounds is the folded claim's truth.** -/
theorem trueSum_lvT_fold {i : ℕ} (hi : i < 5) (L es : Log) :
    trueSum e2 (bindAll (lvT W₀ i L es) (rchs2 (p1Start i) chK es (hEll i)))
      (nrP i (kindOfC es) - hEll i) = foldSum W₀ i L es := by
  rw [rchs2_sAt, lvT, nrP, ← lvl_ell (kindOfC es) hi, Nat.add_sub_cancel_left,
    trueSum_tabs_fold, foldSum]
  exact sum_congr rfl fun x _ => by rw [fold_fTab, wFold]

/-! ## Part B: the absorbs -/

section Absorbs

variable (hF : FrontLocal W₀ c₀) {L es : Log} (x : ByteArray × Digest)
include hF

/-- **Inside P1.i** an absorb keeps the doom (the round count and the fold do not move). -/
theorem habs_P1 {i l : ℕ} (hi : i < 5) (hl : 1 ≤ l) (hlen : es.length = p1Start i + 2 * l) :
    D1 W₀ c₀ i L es → D1 W₀ c₀ i L (es ++ [x]) := by
  have hc := (tail_pos hi).1
  have h1 := (tail_pos hi).2.1
  have hS := same_append L es [x]
  have hk : kindOfC (es ++ [x]) = kindOfC es := kindOf_append x (by omega)
  have hr : hRnd (es ++ [x]) i = hRnd es i := by
    simp only [hRnd, List.length_append, List.length_singleton]; congr 1; omega
  have hr2 : p1Start i + 2 * hRnd es i ≤ es.length := by unfold hRnd; omega
  unfold D1
  rw [hk, hr, closeP_same hS hi _ hr2, farL_same hS hi _ (by omega),
    D2_append_iff h1 (p1_local hF hi) x (by omega) (Or.inl (by omega))]
  exact id

/-- **Inside Pf** an absorb keeps the doom. -/
theorem habs_Pf {l : ℕ} (hl : 1 ≤ l) (hlen : es.length = pfStart + 2 * l) :
    DPf W₀ c₀ L es → DPf W₀ c₀ L (es ++ [x]) := by
  have hp := pfStart_eq
  have h4 := (tail_pos (show 4 < 5 by norm_num)).2.2.2.2
  have hnx : nxStart 4 = pfStart := rfl
  unfold DPf
  rw [kindOf_append x (by omega),
    truthP3_same (same_append L es [x]) (show 4 < 5 by norm_num) _ (by omega),
    D2_append_iff (by omega) (pf_local hF) x (by omega) (Or.inl (by omega))]
  exact id

/-- **P1.i → C.i** (A.10): a far fold refutes `truthP2` (`closeP_of_truthP2`); a close word with a
false final claim gives a false folded claim (`trueSum_lvT_fold`). -/
theorem habs_C {i : ℕ} (hi : i < 5) (hlen : es.length = cStart i) :
    D1 W₀ c₀ i L es → DCi W₀ c₀ i L (es ++ [x]) := by
  obtain ⟨hc, h1, h3, -, -⟩ := tail_pos hi
  have hS := same_append L es [x]
  have hk : kindOfC (es ++ [x]) = kindOfC es := kindOf_append x (by omega)
  have hell := lvl_ell (kindOfC es) hi
  have hr : hRnd es i = hEll i := by unfold hRnd; rw [min_eq_left]; omega
  unfold D1 DCi
  rw [hk]
  rintro (hf | ⟨hf, hd, hw⟩)
  · left
    intro h2
    refine hf ?_
    rw [hr, ← hell, ← closeP_same hS hi _ (by omega)]
    exact closeP_of_truthP2 hi h2
  · right
    rw [farL_same hS hi _ (by omega), c1_same hF hS hi (by omega),
      foldSum_same hF hS hi (by omega)]
    refine ⟨hf, ?_⟩
    have ha : ans3 (p1Start i) (nrP i) es = hEll i := by
      unfold ans3 nrP; rw [hlen, ← h3, Nat.add_sub_cancel_left, Nat.mul_div_cancel_left _ two_pos,
        ← hell, min_eq_right (by omega)]
    rw [ha, Wrong2, trueSum_lvT_fold hi] at hw
    exact hw

/-- **P3.i → P1.(i+1)** (A.10): a far next level is P1.(i+1)'s far fold at `l = 0`; a false next
claim is its asserted rounds' false initial claim. -/
theorem habs_P1_next {i : ℕ} (hi : i + 1 < 5) (hlen : es.length = p1Start (i + 1)) :
    finP3 W₀ c₀ i L es → D1 W₀ c₀ (i + 1) L (es ++ [x]) := by
  obtain ⟨hc, h1, -, -, -⟩ := tail_pos hi
  have hS := same_append L es [x]
  have hk : kindOfC (es ++ [x]) = kindOfC es := kindOf_append x (by omega)
  have hr : hRnd (es ++ [x]) (i + 1) = 0 := by
    simp only [hRnd, List.length_append, List.length_singleton, hlen]
    rw [show p1Start (i + 1) + 1 - p1Start (i + 1) = 1 by omega]; simp
  have hfar := farL_same hS hi (kindOfC es) (i := i + 1) (by omega)
  unfold finP3 D1
  rw [ite_pos' (show i < 4 by omega), hk, hr, closeP_zero, not_not, hfar]
  rintro (hf | hw)
  · exact Or.inl hf
  by_cases hf : farL (kindOfC es) L es (i + 1)
  · exact Or.inl hf
  refine Or.inr ⟨hf, by simp [hlen], ?_⟩
  have ha : ans3 (p1Start (i + 1)) (nrP (i + 1)) (es ++ [x]) = 0 := by
    simp [ans3, hlen]
  rw [ha, Wrong2]
  simp only [clR2, rchs2, List.range_zero, List.map_nil, bindAll, Nat.sub_zero, hk]
  rw [lvT, hk, trueSum_tabs, lvC_same hF hS hi (by omega), lvW_same hF hS hi (by omega),
    fTab_same hS hi _ (by omega)]
  unfold nxSum at hw
  rwa [ite_pos' (show i < 4 by omega)] at hw

omit hF in
/-- Pf's true sum is level 4's folded table against the final message (the padding is zero). -/
theorem sum_wPf (L es : Log) :
    ∑ x ∈ range (2 ^ 7), wPf W₀ L es x * finalAt es x =
      ∑ x ∈ range (2 ^ mLog (kindOfC es) 4), wFold W₀ 4 L es x * finalAt es x := by
  have hle : 2 ^ mLog (kindOfC es) 4 ≤ 2 ^ 7 := Nat.pow_le_pow_right two_pos (mLog4_le _)
  rw [← Finset.sum_range_add_sum_Ico _ hle, Finset.sum_eq_zero (s := Ico _ _) fun x hx => by
    simp only [mem_Ico] at hx; simp only [wPf, show ¬ x < 2 ^ mLog (kindOfC es) 4 by omega,
      ↓reduceIte, zero_mul], add_zero]
  exact sum_congr rfl fun x hx => by simp only [wPf, mem_range.1 hx, ↓reduceIte]

/-- **P3.4 → Pf**: an inconsistent level-4 query stays Pf's background; on a close word whose
final message is the fold, a false folded claim is Pf's false initial claim. -/
theorem habs_Pf_first (hlen : es.length = pfStart) :
    finP3 W₀ c₀ 4 L es → DPf W₀ c₀ L (es ++ [x]) := by
  have hS := same_append L es [x]
  have hp := pfStart_eq
  have h4 : (4 : ℕ) < 5 := by norm_num
  obtain ⟨-, -, -, h44, h45⟩ := tail_pos h4
  have hnx : nxStart 4 = pfStart := rfl
  have hk : kindOfC (es ++ [x]) = kindOfC es := kindOf_append x (by omega)
  unfold finP3 DPf
  rw [ite_neg' (by norm_num), hk, truthP3_same hS h4 _ (by omega)]
  unfold finP2
  rintro (h | ⟨-, hC, hw⟩)
  · exact Or.inl h
  refine Or.inr ⟨by simp [hlen], ?_⟩
  have ha : ans3 pfStart (fun _ => 7) (es ++ [x]) = 0 := by simp [ans3, hlen]
  rw [ha, Wrong2]
  simp only [clR2, rchs2, List.range_zero, List.map_nil, bindAll, Nat.sub_zero]
  rw [tPf, trueSum_tabs, lvC5_same hF hS (by omega)]
  have hw' : wPf W₀ L (es ++ [x]) = wPf W₀ L es := by
    funext y
    simp only [wPf, hk, wFold_same hF hS h4 (by omega)]
  have h46 : cStart 4 = phStart4 47 := rfl
  have hf' : finalAt (es ++ [x]) = finalAt es := funext fun y => by
    simp only [finalAt, msgAt, hS.1 (phStart4 47) (by omega)]
  rw [hw', hf', sum_wPf, lvC_five]
  convert hw using 1
  refine sum_congr rfl fun y hy => ?_
  rw [← hC y (mem_range.1 hy)]
  simp [nextMsg, nLevels]

end Absorbs

/-! ## Part C: the single squeezes -/

theorem rounds_P1 {i l : ℕ} (hi : i < 5) (hl : l < hEll i) :
    fsItems4[p1Start i + 2 * l]? = some (.absorb 96) ∧
      fsItems4[p1Start i + 2 * l + 1]? = some .squeeze := by
  have h := rounds_check
  simp only [Bool.and_eq_true, List.all_eq_true, List.mem_range, beq_iff_eq] at h
  exact h.1.1 i hi l hl

theorem rounds_Pf {l : ℕ} (hl : l < 7) :
    fsItems4[pfStart + 2 * l]? = some (.absorb 96) ∧ fsItems4[pfStart + 2 * l + 1]? = some .squeeze := by
  have h := rounds_check
  simp only [Bool.and_eq_true, List.all_eq_true, List.mem_range, beq_iff_eq] at h
  exact h.1.2 l hl

/-- P1's single-squeeze count fits `N = 239·2^128`. -/
theorem p1_N_le (κ : CKind) {i : ℕ} (hi : i < 5) :
    2 + 2 ^ 5 * cMca (lvN κ i) (lvK κ i) (lvE κ i) ≤ 239 * 2 ^ 128 := by
  rcases κ with (_|_|_) | (_|_|_) <;> interval_cases i <;> decide

theorem sAt_ext1 (es : Log) (a : Digest) {i l : ℕ} (h : es.length = p1Start i + 2 * l + 1) :
    sAt (ext1 es a) i l = chK a := by
  simp only [sAt, kAt, ansAt]
  rw [show phStart4 (26 + 5 * i) + 2 * l + 1 = es.length by unfold p1Start at h; omega,
    entAt_ext1]

open Classical in
/-- **P1.i's round squeeze** (A.10): an escape either makes the far fold close (its challenge in
the round's bad set, `closeP_cover`) or makes a false asserted claim true (`D2_single` over K,
`2` answers). -/
theorem single_P1 (hF : FrontLocal W₀ c₀) {i l : ℕ} (hi : i < 5) (hl : l < hEll i) {L es : Log}
    (hlen : es.length = p1Start i + 2 * l + 1) (hr : ¬ RejT c₀ L es) :
    (univ.filter fun a => D1 W₀ c₀ i L es ∧ ¬ D1 W₀ c₀ i L (ext1 es a)).card ≤
      2 + 2 ^ 5 * cMca (lvN (kindOfC es) i) (lvK (kindOfC es) i) (lvE (kindOfC es) i) := by
  obtain ⟨hc, h1, -, -, -⟩ := tail_pos hi
  set κ := kindOfC es with hκ
  have hell := lvl_ell κ hi
  obtain ⟨B, hB, hBz⟩ := closeP_cover (κ := κ) hi L es (l := l) (by omega)
  have hchk : ∀ j, es.length = p1Start i + 2 * j + 1 → j < nrP i (kindOfC es) →
      Chk2 (p1Start i) 32 readK chK (lvC c₀ i) L es j := by
    intro j hj _
    by_contra hcj
    exact hr (Or.inl ⟨i, hi, j, by omega, by omega, hcj⟩)
  have hD2 := D2_single (R := K) h1 (p1_local hF hi) e2_deg (M := 1)
    (fun S => by rw [card_chK_fiber, mul_one]) (lvT_size i) L es hchk
  refine (card_le_card (t := (univ.filter fun a => chK a ∈ B) ∪
    (univ.filter fun a => D2 (p1Start i) 32 readK chK (lvC c₀ i) (nrP i) e2 (lvT W₀ i) L es ∧
      ¬ D2 (p1Start i) 32 readK chK (lvC c₀ i) (nrP i) e2 (lvT W₀ i) L (ext1 es a))) ?_).trans ?_
  · intro a ha
    simp only [mem_filter, mem_univ, true_and, mem_union] at ha ⊢
    obtain ⟨hd, hnd⟩ := ha
    have hS : Same L (ext1 es a) L es es.length := same_append L es _
    have hk : kindOfC (ext1 es a) = κ := kindOf_ext1 es a (by omega)
    obtain ⟨hR1, hR2⟩ := hRnd_ext1 es a hl hlen
    unfold D1 at hd hnd
    rw [hk, hR2, farL_same hS hi _ (by omega), not_or, not_not] at hnd
    rw [hR1] at hd
    rcases hd with hf | ⟨hfar, hd2⟩
    · left
      by_contra hz
      rcases hBz (chK a) hz with hcl | hcl
      · exact hf hcl
      · apply hcl
        have := hnd.1
        unfold closeP at this
        rwa [pf_succ, sAt_ext1 es a hlen, pf_same hS hi κ (by omega)] at this
    · right
      exact ⟨hd2, fun h => hnd.2 ⟨hfar, h⟩⟩
  · refine (card_union_le _ _).trans ?_
    rw [card_chK_fiber]
    have h5 : 2 ^ ((CKind.lv κ i).ell - (l + 1)) ≤ 2 ^ 5 :=
      Nat.pow_le_pow_right two_pos (by have := hEll_le hi; omega)
    have := Nat.mul_le_mul_right (cMca (lvN κ i) (lvK κ i) (lvE κ i)) h5
    omega

open Classical in
/-- Pf's rounds' own count: `D2_single` over K, `2` answers. -/
theorem single_Pf_D2 (hF : FrontLocal W₀ c₀) {l : ℕ} {L es : Log}
    (hlen : es.length = pfStart + 2 * l + 1) (hr : ¬ RejT c₀ L es) :
    (univ.filter fun a => D2 pfStart 32 readK chK (lvC c₀ 5) (fun _ => 7) e2 (tPf W₀) L es ∧
      ¬ D2 pfStart 32 readK chK (lvC c₀ 5) (fun _ => 7) e2 (tPf W₀) L (ext1 es a)).card ≤ 2 := by
  have hp := pfStart_eq
  have := D2_single (R := K) (show 1 ≤ pfStart by omega) (pf_local hF) e2_deg (M := 1)
    (nr := fun _ => 7) (fun S => by rw [card_chK_fiber, mul_one]) (fun L es => tPf_size L es) L es
    (fun j hj _ => by
      by_contra hcj
      exact hr (Or.inr ⟨j, by omega, by omega, hcj⟩))
  refine le_trans (le_of_eq ?_) this
  congr 1

open Classical in
/-- **Pf's round squeeze**: at most `2` answers escape (the level-4 background never does). -/
theorem single_Pf (hF : FrontLocal W₀ c₀) {l : ℕ} {L es : Log}
    (hlen : es.length = pfStart + 2 * l + 1) (hr : ¬ RejT c₀ L es) :
    (univ.filter fun a => DPf W₀ c₀ L es ∧ ¬ DPf W₀ c₀ L (ext1 es a)).card ≤ 2 := by
  have hp := pfStart_eq
  have h4 := (tail_pos (show 4 < 5 by norm_num)).2.2.2.2
  have hnx : nxStart 4 = pfStart := rfl
  have hB : ∀ a, truthP3 (kindOfC (ext1 es a)) L (ext1 es a) 4 ↔ truthP3 (kindOfC es) L es 4 :=
    fun a => by
      rw [kindOf_ext1 es a (by omega)]
      exact truthP3_same (same_append L es _) (show 4 < 5 by norm_num) _ (by omega)
  refine le_trans (card_le_card fun a ha => ?_) (single_Pf_D2 hF hlen hr)
  simp only [mem_filter, mem_univ, true_and] at ha ⊢
  obtain ⟨h1, h2⟩ := ha
  unfold DPf at h1 h2
  rw [not_or, hB a, not_not] at h2
  exact ⟨h1.resolve_left (not_not.mpr h2.1), h2.2⟩

/-! ## Part D: the asserted checks -/

/-- **`RejT` is a valid rejection predicate** (monotone, unchanged at squeezes, stable). -/
theorem rejT_ok (hF : FrontLocal W₀ c₀) : RejOK (RejT c₀) where
  mono L es x h := by
    have hS := same_append L es [x]
    rcases h with ⟨i, hi, j, hj, hlt, hc⟩ | ⟨j, hj, hlt, hc⟩
    · refine Or.inl ⟨i, hi, j, hj, by simp; omega, fun h' => hc ?_⟩
      rwa [chk2_same hS hlt (lvC_same hF hS hi (by omega))] at h'
    · refine Or.inr ⟨j, hj, by simp; omega, fun h' => hc ?_⟩
      rwa [chk2_same hS hlt (lvC5_same hF hS (by omega))] at h'
  sq L es x hsq := by
    have hS := same_append L es [x]
    refine ⟨fun h => ?_, fun h => ?_⟩
    · rcases h with ⟨i, hi, j, hj, hlt, hc⟩ | ⟨j, hj, hlt, hc⟩
      · have hne : p1Start i + 2 * j ≠ es.length := fun he => by
          have := (rounds_P1 hi hj).1; rw [he, hsq] at this; simp at this
        simp only [List.length_append, List.length_singleton] at hlt
        refine Or.inl ⟨i, hi, j, hj, by omega, fun h' => hc ?_⟩
        rwa [chk2_same hS (by omega) (lvC_same hF hS hi (by omega))]
      · have hne : pfStart + 2 * j ≠ es.length := fun he => by
          have := (rounds_Pf hj).1; rw [he, hsq] at this; simp at this
        simp only [List.length_append, List.length_singleton] at hlt
        refine Or.inr ⟨j, hj, by omega, fun h' => hc ?_⟩
        rwa [chk2_same hS (by omega) (lvC5_same hF hS (by omega))]
    · rcases h with ⟨i, hi, j, hj, hlt, hc⟩ | ⟨j, hj, hlt, hc⟩
      · refine Or.inl ⟨i, hi, j, hj, by simp; omega, fun h' => hc ?_⟩
        rwa [chk2_same hS hlt (lvC_same hF hS hi (by omega))] at h'
      · refine Or.inr ⟨j, hj, by simp; omega, fun h' => hc ?_⟩
        rwa [chk2_same hS hlt (lvC5_same hF hS (by omega))] at h'
  stab L n hb hci X hX := by
    have hS := same_stabX hb hci hX
    refine or_congr ⟨fun ⟨i, hi, j, hj, hlt, hc⟩ => ⟨i, hi, j, hj, hlt, fun h' => hc ?_⟩,
      fun ⟨i, hi, j, hj, hlt, hc⟩ => ⟨i, hi, j, hj, hlt, fun h' => hc ?_⟩⟩
      ⟨fun ⟨j, hj, hlt, hc⟩ => ⟨j, hj, hlt, fun h' => hc ?_⟩,
      fun ⟨j, hj, hlt, hc⟩ => ⟨j, hj, hlt, fun h' => hc ?_⟩⟩
    · exact (chk2_same hS hlt (lvC_same hF hS hi (by omega))).mpr h'
    · exact (chk2_same hS hlt (lvC_same hF hS hi (by omega))).mp h'
    · exact (chk2_same hS hlt (lvC5_same hF hS (by omega))).mpr h'
    · exact (chk2_same hS hlt (lvC5_same hF hS (by omega))).mp h'

end FR.Snd.T4

end G6_FRSoundness4TailO

section G6_FRSoundness4TailM

-- New for `flock-recursive` (BLUEPRINT §5.1, §5.4, A.10; stage T4, S-G13 route C): a copy-port of
-- `FRSoundnessTailM` to revision 4.1's item sequence `seq4` (namespace `FR.Snd.T4`, see `FRSoundness4TailStep`):
-- the declarations that read positions, chains or the kind are copied, the rest is imported.

/-!
# The tail obligations (multi-squeeze phases, stability) at `seq4` (T4)

The 3.x declarations of `FRSoundnessTailM` that read the positions, the chains or the kind, restated in
`FR.Snd.T4` over `fsItems4`/`phStart4`/`fsRnd4`, `G.Matches`/`G.IsChain` and `CKind`
(`kindOfC`, `CKind.lv`). Positions from P1.0 on are 3.x's plus 14 (`phStart4_shift`); the kind
enters through the ladder `lvOf κ.m` only. Changes beyond the renaming are marked `T4:`.
-/

/-! # Port of `FRSoundnessTailM` (its module doc describes the 3.x original) -/

namespace FR.Snd.T4
open RecursionFast FR.Merkle Finset
open scoped NNReal

set_option linter.constructorNameAsVariable false

/-! ## Part A: the phase facts -/

theorem tail_ph_check : (List.range 5).all (fun i => phOf4 (p1Start i) == 26 + 5 * i &&
    phOf4 (cStart i) == 27 + 5 * i && phOf4 (cStart i + 1) == 28 + 5 * i &&
    phOf4 (p3S0 i) == 28 + 5 * i && phOf4 (p3S0 i + 1) == 30 + 5 * i &&
    phStart4 (28 + 5 * i) == cStart i + 1 && phStart4 (29 + 5 * i) == p3S0 i + 1 &&
    phStart4 (30 + 5 * i) == p3S0 i + 1 && phStart4 (31 + 5 * i) == nxStart i &&
    fsRanges4.contains (cStart i, (lvlStar i).sq) && fsRanges4.contains (p3S0 i, 5)) = true := by
  unfold nxStart p1Start pfStart cStart p3S0 phOf4 phStart4
  rw [fsStarts4_eq, fsRanges4_eq]; decide +kernel

theorem tail_ph {i : ℕ} (hi : i < 5) : phOf4 (p1Start i) = 26 + 5 * i ∧
    phOf4 (cStart i) = 27 + 5 * i ∧ phOf4 (cStart i + 1) = 28 + 5 * i ∧
    phOf4 (p3S0 i) = 28 + 5 * i ∧ phOf4 (p3S0 i + 1) = 30 + 5 * i ∧
    phStart4 (28 + 5 * i) = cStart i + 1 ∧ phStart4 (29 + 5 * i) = p3S0 i + 1 ∧
    phStart4 (30 + 5 * i) = p3S0 i + 1 ∧ phStart4 (31 + 5 * i) = nxStart i ∧
    (cStart i, (lvlStar i).sq) ∈ fsRanges4 ∧ (p3S0 i, 5) ∈ fsRanges4 := by
  have h := tail_ph_check
  simp only [List.all_eq_true, List.mem_range, Bool.and_eq_true, beq_iff_eq,
    List.contains_iff_mem] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩, h7⟩, h8⟩, h9⟩, h10⟩, h11⟩ := h i hi
  exact ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11⟩

variable {W₀ : Log → Log → ℕ → K} {c₀ : Log → Log → K}

theorem ms_P2 {Dk : ℕ → Log → Log → Prop} {i : ℕ} (hi : i < 5)
    (hC : Dk (27 + 5 * i) = DCi W₀ c₀ i) (hP : Dk (28 + 5 * i) = DP2 W₀ c₀ i) :
    Dk (phOf4 (cStart i + 1)) = msD (Dk (phOf4 (cStart i))) (finP2 W₀ c₀ i) (cStart i)
      (lvlStar i).sq := by
  obtain ⟨-, h2, h3, -⟩ := tail_ph hi
  rw [h2, h3, hC, hP, DP2]

theorem ms_P3 {Dk : ℕ → Log → Log → Prop} {i : ℕ} (hi : i < 5)
    (hP : Dk (28 + 5 * i) = DP2 W₀ c₀ i) (hQ : Dk (30 + 5 * i) = DP3 W₀ c₀ i) :
    Dk (phOf4 (p3S0 i + 1)) = msD (Dk (phOf4 (p3S0 i))) (finP3 W₀ c₀ i) (p3S0 i) 5 := by
  obtain ⟨-, -, -, h4, h5, -⟩ := tail_ph hi
  rw [h4, h5, hP, hQ, DP3]

/-! ## Part B: P2.i -/

theorem lvE_lt_lvN (κ : CKind) {i : ℕ} (hi : i < 5) : lvE κ i < lvN κ i := by
  rcases κ with (_|_|_) | (_|_|_) <;> interval_cases i <;> decide

open Classical in
/-- **P2.i's charge** (A.10, `p2_hround`): at most `deltaR`. -/
theorem hfin_P2 (hF : FrontLocal W₀ c₀) {Dk : ℕ → Log → Log → Prop} {i : ℕ} (hi : i < 5)
    (hC : Dk (27 + 5 * i) = DCi W₀ c₀ i) (hP : Dk (28 + 5 * i) = DP2 W₀ c₀ i)
    (L es₀ : Log) (hl : es₀.length = cStart i + 1) :
    condCount (DPos (Dp Dk)) L es₀ (lvlStar i).sq [] ≤ deltaR := by
  obtain ⟨-, h2, -, -, -, -, -, -, -, hmem, -⟩ := tail_ph hi
  have hms := ms_P2 hi hC hP
  set κ := kindOfC es₀
  let S : Finset (Fin (2 ^ (CKind.lv κ i).logN)) :=
    if truthP2 κ L es₀ i then ∅ else consSet κ L es₀ i
  refine p2_hround κ i hi hl S ?_ fun as has he => ?_
  · by_cases h : truthP2 κ L es₀ i
    · simp only [S, h, ite_true, card_empty, zero_add]; exact lvE_lt_lvN κ hi
    · simp only [S, h, ite_false]; exact consSet_card_of_not κ h
  obtain ⟨hd, hnf⟩ := esc_msD hmem hms hl as has he
  rw [h2, hC] at hd
  set X := ext es₀ as
  have hS : Same L X L es₀ (cStart i + 1) := hl ▸ same_of_agree L (agree_ext es₀ as)
  have hk : kindOfC X = κ := kindOf_ext es₀ as (by omega)
  unfold finP2 at hnf
  rw [hk, not_or, not_not] at hnf
  obtain ⟨h3, hn⟩ := hnf
  rw [farL_same hS hi _ (by have := (tail_pos hi).1; have := (tail_pos hi).2.2.1; omega),
    truthC_same hS hi _ le_rfl, c1_same hF hS hi (by omega),
    foldSum_same hF hS hi (by omega)] at hn
  have hP2 : ¬ truthP2 κ L es₀ i := by
    intro h2'
    rcases hd with hd | ⟨hf, hw⟩
    · exact hd h2'
    · exact hn ⟨hf, truthC_of hi hf h2', hw⟩
  intro k hk'
  have hq := h3 k hk'
  have hlt : qPos κ X i k < 2 ^ (CKind.lv κ i).logN := idx_lt _ _ _
  simp only [consErr, foldAtN, hlt, ↓reduceDIte, sub_eq_zero] at hq
  simp only [S, hP2, ite_false]
  refine mem_map.mpr ⟨⟨qPos κ X i k, hlt⟩, ?_, rfl⟩
  rw [← consSet_same hS hi κ le_rfl]
  simp only [consSet, mem_filter, mem_univ, true_and]
  exact hq

/-! ## Part C: P3.i -/

/-- P3.i's offset `d = c1 − ⟨Wf, f⁽ⁱ⁺¹⁾⟩`. -/
noncomputable def dP3 (W₀ : Log → Log → ℕ → K) (c₀ : Log → Log → K) (i : ℕ) (L es : Log) : K :=
  c1 c₀ i L es - ∑ x ∈ range (2 ^ mLog (kindOfC es) i),
    wFold W₀ i L es x * nextMsg (kindOfC es) L es i x

/-- `nxSum` as the next weight's inner product with level `i`'s folded message (`i < 4`). -/
theorem nxSum_eq (W₀ : Log → Log → ℕ → K) {i : ℕ} (hi : i < 4)
    (L es : Log) : nxSum W₀ i L es = ∑ x ∈ range (2 ^ mLog (kindOfC es) i),
      wNext (kindOfC es) es i (wFold W₀ i L es) x * nextMsg (kindOfC es) L es i x := by
  unfold nxSum
  rw [ite_pos' hi, nrP, ← wSplit_sum (show i + 1 < 5 by omega)]
  rfl

theorem dP3_same (hF : FrontLocal W₀ c₀) {L es L' es' : Log} {p : ℕ} (h : Same L es L' es' p)
    {i : ℕ} (hi : i < 5) (hp : cStart i + 1 ≤ p) : dP3 W₀ c₀ i L es = dP3 W₀ c₀ i L' es' := by
  have h1 := (tail_pos hi).2.1
  rw [dP3, dP3, c1_same hF h hi (by omega), wFold_same hF h hi (by omega), h.kind (by omega),
    nextMsg_same h hi _ hp]

theorem p3T_same {L es L' es' : Log} {p : ℕ} (h : Same L es L' es' p) {i : ℕ} (hi : i < 5)
    (κ : CKind) (hp : p3S0 i + 1 ≤ p) (d : K) : p3T κ L es i d = p3T κ L' es' i d := by
  have e : ∀ q : Fin (2 ^ 9), ((if (q : ℕ) < (CKind.lv κ i).t then consErr κ L es i q else 0) + d) =
      ((if (q : ℕ) < (CKind.lv κ i).t then consErr κ L' es' i q else 0) + d) := fun q => by
    by_cases hq : (q : ℕ) < (CKind.lv κ i).t
    · simp only [hq, ↓reduceIte, consErr_same h hi κ hp hq]
    · simp only [hq, ↓reduceIte]
  unfold p3T
  simp only [e]

theorem ofFn_coord_getD (X : Log) (i v : ℕ) (hv : v < 10) :
    ((List.ofFn fun j : Fin (5 * 2) => coordAt X (p3S0 i) j).map (algebraMap F K)).getD v 0 =
      algebraMap F K (kcAt X i v) := by
  simp [List.getD_eq_getElem?_getD, hv, kcAt, p3S0]
  interval_cases v <;> rfl

open Classical in
/-- **P3.i's charge** (A.10, `hfin_seq` over the 9 coordinates of `κ_c`): at most `9/2^128`. -/
theorem hfin_P3 (hF : FrontLocal W₀ c₀) {Dk : ℕ → Log → Log → Prop} {i : ℕ} (hi : i < 5)
    (hP : Dk (28 + 5 * i) = DP2 W₀ c₀ i) (hQ : Dk (30 + 5 * i) = DP3 W₀ c₀ i)
    (L es₀ : Log) (hl : es₀.length = p3S0 i + 1) :
    condCount (DPos (Dp Dk)) L es₀ 5 [] ≤ deltaR := by
  obtain ⟨-, -, -, h4, -, -, -, -, -, -, hmem⟩ := tail_ph hi
  obtain ⟨hc, h1, h3, hsq, h5⟩ := tail_pos hi
  have hms := ms_P3 hi hP hQ
  by_cases hi4 : i < 4
  swap
  · -- P3.4: `finP3 4` is P2.4's final doom, which reads no P3.4 answer: nothing escapes.
    obtain rfl : i = 4 := by omega
    refine (condCount_eq_zero fun as has he => ?_).trans_le zero_le
    obtain ⟨hd, hnf⟩ := esc_msD hmem hms hl as has he
    rw [h4, hP, DP2, msD, ite_neg' (by omega)] at hd
    unfold finP3 at hnf
    rw [ite_neg' (by norm_num)] at hnf
    have hS : Same L (ext es₀ as) L es₀ (p3S0 4 + 1) := hl ▸ same_of_agree L (agree_ext es₀ as)
    have hk : kindOfC (ext es₀ as) = kindOfC es₀ := kindOf_ext es₀ as (by omega)
    refine hnf ?_
    unfold finP2 at hd ⊢
    rw [hk, truthP3_same hS hi _ le_rfl, truthC_same hS hi _ (by omega),
      farL_same hS hi _ (by omega), c1_same hF hS hi (by omega), foldSum_same hF hS hi (by omega)]
    exact hd
  refine hfin_seq hmem hms (fun j => if j < 9 then 1 else 0) (by decide)
    (fun L es₀ l => es₀.length = p3S0 i + 1 →
      mlDoom 9 (p3T (kindOfC es₀) L es₀ i (dP3 W₀ c₀ i L es₀)) (l.map (algebraMap F K)))
    (fun L es₀ l hd => ?_) ?_ ?_ L es₀ hl
  · by_cases hlen : es₀.length = p3S0 i + 1
    · have := mlDoomF_step (p3T_size _ _ _ _ _) l (hd hlen)
      refine le_trans (card_le_card fun c hc => ?_) this
      simp only [mem_filter, mem_univ, true_and] at hc ⊢
      exact fun h => hc fun _ => h
    · refine le_trans (card_le_card (t := ∅) fun c hc => ?_) (by simp)
      simp only [mem_filter, mem_univ, true_and] at hc
      exact absurd (fun h' => absurd h' hlen) hc
  · intro L es₀ hd hlen
    rw [h4, hP, DP2, msD, ite_neg' (by omega)] at hd
    have hne : tbl 9 (p3T (kindOfC es₀) L es₀ i (dP3 W₀ c₀ i L es₀)) ≠ 0 := by
      refine p3T_ne_zero hi ?_
      rcases hd with hd | ⟨-, hC, hw⟩
      · exact Or.inl hd
      · right
        rw [dP3, sub_ne_zero]
        convert hw using 1
        refine sum_congr rfl fun x hx => ?_
        rw [hC x (mem_range.1 hx)]
    simp only [List.map_nil]
    exact hne
  · intro L es₀ as hl' has _ hnf hD
    have hm := hD hl'
    set X := ext es₀ as
    have hS : Same L X L es₀ (p3S0 i + 1) := hl' ▸ same_of_agree L (agree_ext es₀ as)
    have hk : kindOfC X = kindOfC es₀ := kindOf_ext es₀ as (by omega)
    unfold finP3 at hnf
    rw [ite_pos' hi4, not_or, not_not] at hnf
    have hv : vNext (kindOfC X) L X i (c1 c₀ i L X) = nxSum W₀ i L X := by
      rw [← lvC_succ c₀ hi4]; exact hnf.2
    have hsub := vNext_sub (kindOfC X) L X i (wFold W₀ i L X) (c1 c₀ i L X)
    rw [hv, nxSum_eq W₀ hi4, sub_self] at hsub
    have hmle := p3T_mle (kindOfC X) L X hi (dP3 W₀ c₀ i L X)
    rw [dP3, ← hsub] at hmle
    rw [← dP3, p3T_same hS hi _ le_rfl, dP3_same hF hS hi (by omega), hk] at hmle
    refine (not_mlDoom_nine (p3T_size _ _ _ _ _) _ (by simp)).mpr ?_ hm
    refine Eq.trans (sum_congr rfl fun q _ => ?_) hmle
    rw [eqBits_congr fun v hv => ofFn_coord_getD X i v (by omega)]

/-! ## Part D: stability -/

theorem D2_congrL {R : Type*} [Field R] {b wd : ℕ} {rd : ByteArray → ℕ → R} {ch : Digest → R}
    {c0 : Log → Log → R} {nr : CKind → ℕ} {e : Expr} {T : Log → Log → Array (Array R)}
    {L L' Y : Log} (hT : T L Y = T L' Y) (hc : c0 L Y = c0 L' Y) :
    D2 b wd rd ch c0 nr e T L Y ↔ D2 b wd rd ch c0 nr e T L' Y := by
  unfold D2 Wrong2
  rw [hT, clR2_same (L' := L') (es' := Y) hc (fun _ _ => rfl)]

theorem DT_Q (W₀ : Log → Log → ℕ → K) (c₀ : Log → Log → K) {i : ℕ} (hi : i < 5) :
    DT W₀ c₀ (29 + 5 * i) = fun _ _ => False := by
  rw [DT_lvl W₀ c₀ (by omega)]; unfold DTl
  rw [ite_neg' (by omega), ite_neg' (by omega), ite_neg' (by omega), ite_pos' (by omega)]

section Stab

variable (hF : FrontLocal W₀ c₀) {L L' Y : Log} {p : ℕ} (h : Same L Y L' Y p) {i : ℕ}
  (hi : i < 5)
include hF h hi

theorem D1_stab (hY : Y.length ≤ p) (hp : p1Start i + 1 ≤ p) :
    D1 W₀ c₀ i L Y ↔ D1 W₀ c₀ i L' Y := by
  have hc := (tail_pos hi).1
  have hr : p1Start i + 2 * hRnd Y i ≤ p := by unfold hRnd; omega
  unfold D1
  rw [closeP_same h hi _ hr, farL_same h hi _ (by omega),
    D2_congrL (lvT_same hF h hi (by omega)) (lvC_same hF h hi (by omega))]

theorem DCi_stab (hp : cStart i + 1 ≤ p) : DCi W₀ c₀ i L Y ↔ DCi W₀ c₀ i L' Y := by
  obtain ⟨hc, h1, h3, -, -⟩ := tail_pos hi
  unfold DCi
  rw [truthP2_same h hi _ hp, farL_same h hi _ (by omega), c1_same hF h hi (by omega),
    foldSum_same hF h hi (by omega)]

theorem finP2_stab (hp : p3S0 i + 1 ≤ p) : finP2 W₀ c₀ i L Y ↔ finP2 W₀ c₀ i L' Y := by
  obtain ⟨hc, h1, h3, h4, -⟩ := tail_pos hi
  unfold finP2
  rw [truthP3_same h hi _ hp, truthC_same h hi _ (by omega), farL_same h hi _ (by omega),
    c1_same hF h hi (by omega), foldSum_same hF h hi (by omega)]

omit h in
theorem DP2_stab (h : Same L Y L' Y p) (hY : Y.length ≤ p) (hp : cStart i + 1 ≤ p) :
    DP2 W₀ c₀ i L Y ↔ DP2 W₀ c₀ i L' Y := by
  have h4 := (tail_pos hi).2.2.2.1
  unfold DP2 msD
  split_ifs with hl
  · exact DCi_stab hF (h.take (m := cStart i + 1) hp) hi le_rfl
  · exact finP2_stab hF h hi (by omega)

theorem finP3_stab (hp : nxStart i ≤ p) : finP3 W₀ c₀ i L Y ↔ finP3 W₀ c₀ i L' Y := by
  obtain ⟨hc, h1, h3, h4, h5⟩ := tail_pos hi
  unfold finP3
  by_cases h4' : i < 4
  · have hC : lvC c₀ (i + 1) L Y = lvC c₀ (i + 1) L' Y :=
      (chain_same hF (i + 1) (by omega) h (by rw [lvB_succ hi]; exact hp)).2
    have hN : nxSum W₀ i L Y = nxSum W₀ i L' Y := by
      rw [nxSum_eq W₀ h4', nxSum_eq W₀ h4', wFold_same hF h hi (by omega),
        wNext_same h hi _ hp, nextMsg_same h hi _ (by omega)]
    rw [ite_pos' h4', ite_pos' h4', hC, hN,
      farL_same h (show i + 1 < 5 by omega) _ (by rw [capPos_succ]; omega)]
  · rw [ite_neg' h4', ite_neg' h4']
    exact finP2_stab hF h hi (by omega)

omit h in
theorem DP3_stab (h : Same L Y L' Y p) (hY : Y.length ≤ p) (hp : p3S0 i + 1 ≤ p) :
    DP3 W₀ c₀ i L Y ↔ DP3 W₀ c₀ i L' Y := by
  obtain ⟨-, -, -, h4, h5⟩ := tail_pos hi
  unfold DP3 msD
  split_ifs with hl
  · exact DP2_stab hF hi (h.take (m := p3S0 i + 1) hp) (by simp) (by omega)
  · exact finP3_stab hF h hi (by omega)

end Stab

theorem DPf_stab (hF : FrontLocal W₀ c₀) {L L' Y : Log} {p : ℕ} (h : Same L Y L' Y p)
    (hp : pfStart ≤ p) : DPf W₀ c₀ L Y ↔ DPf W₀ c₀ L' Y := by
  have h4 := (tail_pos (show 4 < 5 by norm_num)).2.2.2.2
  have hnx : nxStart 4 = pfStart := rfl
  unfold DPf
  rw [truthP3_same h (show 4 < 5 by norm_num) _ (by omega)]
  exact or_congr Iff.rfl (D2_congrL (tPf_same hF h hp) (lvC5_same hF h hp))

/-- **Pf's doom after Pf** reads nothing past Pf's last round (the cap check's phases keep it). -/
theorem DPf_append (hF : FrontLocal W₀ c₀) {L es : Log} (hl : pfStart + 14 ≤ es.length)
    (x : ByteArray × Digest) : DPf W₀ c₀ L (es ++ [x]) ↔ DPf W₀ c₀ L es := by
  have hS := same_append L es [x]
  have h4 := (tail_pos (show 4 < 5 by norm_num)).2.2.2.2
  have hnx : nxStart 4 = pfStart := rfl
  have hb1 : 1 ≤ pfStart := by rw [pfStart_eq]; norm_num
  unfold DPf
  rw [hS.kind (by omega), truthP3_same hS (show 4 < 5 by norm_num) _ (by omega),
    D2_append_iff hb1 (pf_local hF) x (by omega) (Or.inr (by show 7 ≤ _; omega))]

/-- The cap check's dooms read `L` only through Pf's. -/
theorem DCap_stab (hF : FrontLocal W₀ c₀) {k : ℕ} {L L' Y : Log} {p : ℕ} (h : Same L Y L' Y p)
    (hp : pfStart ≤ p) : DCap W₀ c₀ k L Y ↔ DCap W₀ c₀ k L' Y := by
  have e := DPf_stab hF h hp
  unfold DCap DCapD DCapZeta DCapA DCapZ
  split_ifs <;> simp only [e]

/-- **Every tail doom is stable** (`hstab`): on two logs whose words agree up to the chain's
length, once the chain has reached phase `k`. -/
theorem DT_stab (hF : FrontLocal W₀ c₀) {k : ℕ} (hk1 : 26 ≤ k) (hk2 : k ≤ 55) {L L' Y : Log}
    {p : ℕ} (h : Same L Y L' Y p) (hY : Y.length ≤ p) (hp : phStart4 k + 1 ≤ p) :
    DT W₀ c₀ k L Y ↔ DT W₀ c₀ k L' Y := by
  by_cases h50 : k = 51
  · subst h50; rw [DT_Pf]; exact DPf_stab hF h (by unfold pfStart; omega)
  by_cases h52 : 51 < k
  · have hk : phStart4 51 ≤ phStart4 k := by
      unfold phStart4; rw [fsStarts4_eq]; interval_cases k <;> decide
    unfold DT; rw [ite_neg' h50, ite_pos' h52]
    exact DCap_stab hF h (by unfold pfStart; omega)
  obtain ⟨i, t, ht, rfl⟩ : ∃ i t, t < 5 ∧ k = 26 + 5 * i + t :=
    ⟨(k - 26) / 5, (k - 26) % 5, Nat.mod_lt _ (by norm_num), by omega⟩
  have hi : i < 5 := by omega
  obtain ⟨-, -, -, -, -, h27, h28, h29, -⟩ := tail_ph hi
  interval_cases t
  · rw [add_zero, DT_P1 W₀ c₀ hi]; exact D1_stab hF h hi hY hp
  · rw [show 26 + 5 * i + 1 = 27 + 5 * i by ring, DT_C W₀ c₀ hi]
    exact DCi_stab hF h hi (by rw [show 26 + 5 * i + 1 = 27 + 5 * i by ring] at hp; exact hp)
  · rw [show 26 + 5 * i + 2 = 28 + 5 * i by ring, DT_P2 W₀ c₀ hi]
    rw [show 26 + 5 * i + 2 = 28 + 5 * i by ring, h27] at hp
    exact DP2_stab hF hi h hY (by omega)
  · rw [show 26 + 5 * i + 3 = 29 + 5 * i by ring, DT_Q W₀ c₀ hi]
  · rw [show 26 + 5 * i + 4 = 30 + 5 * i by ring, DT_P3 W₀ c₀ hi]
    rw [show 26 + 5 * i + 4 = 30 + 5 * i by ring, h29] at hp
    exact DP3_stab hF hi h hY (by omega)

end FR.Snd.T4

end G6_FRSoundness4TailM

section G6_FRSoundness4TailC

-- New for `flock-recursive` (BLUEPRINT §5.1, §5.4, A.10; stage T4, S-G13 route C): a copy-port of
-- `FRSoundnessCompose` to revision 4.1's item sequence `seq4` (namespace `FR.Snd.T4`, see `FRSoundness4TailStep`):
-- the declarations that read positions, chains or the kind are copied, the rest is imported.

/-!
# The composed doom and `PhaseObl` at `seq4` (T4)

The 3.x declarations of `FRSoundnessCompose` that read the positions, the chains or the kind, restated in
`FR.Snd.T4` over `fsItems4`/`phStart4`/`fsRnd4`, `G.Matches`/`G.IsChain` and `CKind`
(`kindOfC`, `CKind.lv`). Positions from P1.0 on are 3.x's plus 14 (`phStart4_shift`); the kind
enters through the ladder `lvOf κ.m` only. Changes beyond the renaming are marked `T4:`.
-/

/-! # Port of `FRSoundnessCompose` (its module doc describes the 3.x original) -/

namespace FR.Snd.T4
open RecursionFast FR.Merkle Finset
open scoped NNReal

set_option linter.constructorNameAsVariable false

/-! ## The combined doom -/

/-- The asserted checks: the front's or the tail's. -/
def RejC (RejF : Log → Log → Prop) (c₀ : Log → Log → K) (L es : Log) : Prop :=
  RejF L es ∨ RejT c₀ L es

/-- The phase dooms: the front's before P1.0, the tail's from P1.0 on. -/
def DkC (DF : ℕ → Log → Log → Prop) (W₀ : Log → Log → ℕ → K) (c₀ : Log → Log → K) (k : ℕ) :
    Log → Log → Prop :=
  if k < 26 then DF k else DT W₀ c₀ k

theorem rejOK_or {R₁ R₂ : Log → Log → Prop} (h₁ : RejOK R₁) (h₂ : RejOK R₂) :
    RejOK fun L es => R₁ L es ∨ R₂ L es where
  mono L es x h := h.imp (h₁.mono L es x) (h₂.mono L es x)
  sq L es x hs := or_congr (h₁.sq L es x hs) (h₂.sq L es x hs)
  stab L i hb hci X hX := or_congr (h₁.stab L i hb hci X hX) (h₂.stab L i hb hci X hX)

open Classical in
/-- **What the PIOP front still owes** (phases `0 … 25`, positions before P1.0). -/
structure FrontObl (RejF : Log → Log → Prop) (DF : ℕ → Log → Log → Prop)
    (W₀ : Log → Log → ℕ → K) (c₀ : Log → Log → K) : Prop where
  loc : FrontLocal W₀ c₀
  rej : RejOK RejF
  ms : ∀ s0 r, (s0, r) ∈ fsRanges4 → s0 + 1 < p1Start 0 →
    ∃ fin, DF (phOf4 (s0 + 1)) = msD (DF (phOf4 s0)) fin s0 r
  habs : ∀ L es x len, G.Matches (es ++ [x]) → fsItems4[es.length]? = some (.absorb len) →
    es.length < p1Start 0 → ¬ RejC RejF c₀ L es → DF (phOf4 (es.length - 1)) L es →
      RejC RejF c₀ L (es ++ [x]) ∨ DF (phOf4 es.length) L (es ++ [x])
  handoff : ∀ L es x len, G.Matches (es ++ [x]) → fsItems4[es.length]? = some (.absorb len) →
    es.length = p1Start 0 → ¬ RejC RejF c₀ L es → DF 25 L es →
      RejC RejF c₀ L (es ++ [x]) ∨ D1 W₀ c₀ 0 L (es ++ [x])
  hsingle : ∀ L es, G.Matches es → fsItems4[es.length]? = some .squeeze → fsRnd4 es.length = none →
    es.length < p1Start 0 → ¬ RejC RejF c₀ L es →
      (univ.filter fun a => DF (phOf4 (es.length - 1)) L es ∧
        ¬ DF (phOf4 es.length) L (ext1 es a)).card ≤ 239 * 2 ^ 128
  hfin : ∀ s0 r, (s0, r) ∈ fsRanges4 → s0 + 1 < p1Start 0 → ∀ L es₀, G.Matches es₀ →
    es₀.length = s0 + 1 → ¬ RejC RejF c₀ L es₀ → condCount (DPos (Dp DF)) L es₀ r [] ≤ deltaR
  hstab : ∀ k < 26, ∀ L i, ¬ Bad L → G.IsChain L i → ∀ X,
    StabExt fsRnd4 (entriesOf L (pathOf L i)) X → phOf4 (X.length - 1) = k →
      (DF k (L.take i) X ↔ DF k L X)

/-! ## Position facts -/

theorem front_check : ((List.range 30).all fun j => decide (p1Start 0 ≤ phStart4 (26 + j))) &&
    ((List.range 26).all fun k => decide (phStart4 (k + 1) ≤ p1Start 0)) &&
    phOf4 (p1Start 0 - 1) == 25 &&
    (List.range 5).all (fun i => fsItems4[cStart i]? != some .squeeze) &&
    fsRanges4.all (fun x => decide (x.1 + x.2 < p1Start 0) ||
      (List.range 5).any fun i => x == (cStart i, (lvlStar i).sq) || x == (p3S0 i, 5)) = true := by
  unfold p1Start cStart p3S0 phOf4 phStart4
  rw [fsStarts4_eq, fsRanges4_eq]; decide +kernel

theorem front_facts : (∀ j ≤ 29, p1Start 0 ≤ phStart4 (26 + j)) ∧
    (∀ k < 26, phStart4 (k + 1) ≤ p1Start 0) ∧ phOf4 (p1Start 0 - 1) = 25 ∧
    (∀ i < 5, fsItems4[cStart i]? ≠ some .squeeze) ∧
    ∀ x ∈ fsRanges4, x.1 + x.2 < p1Start 0 ∨
      ∃ i < 5, x = (cStart i, (lvlStar i).sq) ∨ x = (p3S0 i, 5) := by
  have h := front_check
  simp only [Bool.and_eq_true, List.all_eq_true, List.mem_range, decide_eq_true_eq, beq_iff_eq,
    bne_iff_ne, ne_eq, Bool.or_eq_true, List.any_eq_true] at h
  obtain ⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩ := h
  refine ⟨fun j hj => h1 j (by omega), h2, h3, h4, fun x hx => ?_⟩
  rcases h5 x hx with h | ⟨i, hi, h⟩
  · exact Or.inl h
  · exact Or.inr ⟨i, hi, h⟩

theorem phOf_lt_26 {p : ℕ} (hp : p < p1Start 0) : phOf4 p < 26 := by
  by_contra h
  obtain ⟨h1, h2, -⟩ := phOf_bounds p
  have := front_facts.1 (phOf4 p - 26) (by omega)
  rw [show 26 + (phOf4 p - 26) = phOf4 p by omega] at this
  omega

theorem phOf_ge_26 {p : ℕ} (hp : p1Start 0 ≤ p) : 26 ≤ phOf4 p := by
  by_contra h
  obtain ⟨-, -, h3⟩ := phOf_bounds p
  have := front_facts.2.1 (phOf4 p) (by omega)
  have := h3 (by omega)
  omega

theorem DkC_lt {DF : ℕ → Log → Log → Prop} {W₀ : Log → Log → ℕ → K} {c₀ : Log → Log → K}
    {k : ℕ} (h : k < 26) : DkC DF W₀ c₀ k = DF k := by rw [DkC, ite_pos' h]

theorem DkC_ge {DF : ℕ → Log → Log → Prop} {W₀ : Log → Log → ℕ → K} {c₀ : Log → Log → K}
    {k : ℕ} (h : 26 ≤ k) : DkC DF W₀ c₀ k = DT W₀ c₀ k := by rw [DkC, ite_neg' (by omega)]

/-- Checked: the class of every tail position (P1.i's absorb or squeeze, C.i, inside P2.i or
P3.i, Pf's absorb or squeeze), with the phases of it and of its predecessor. -/
def tailCls (p : ℕ) : Bool :=
  (List.range 5).any (fun i => (List.range (hEll i)).any fun l =>
      (p == p1Start i + 2 * l && phOf4 p == 26 + 5 * i &&
        ((l == 0 && phOf4 (p - 1) == 25 + 5 * i) || (l != 0 && phOf4 (p - 1) == 26 + 5 * i))) ||
      (p == p1Start i + 2 * l + 1 && phOf4 p == 26 + 5 * i && phOf4 (p - 1) == 26 + 5 * i)) ||
  (List.range 5).any (fun i => (p == cStart i && phOf4 p == 27 + 5 * i &&
      phOf4 (p - 1) == 26 + 5 * i) || (decide (cStart i < p) && decide (p ≤ p3S0 i + 5))) ||
  (List.range 7).any (fun l =>
      (p == pfStart + 2 * l && phOf4 p == 51 &&
        ((l == 0 && phOf4 (p - 1) == 50) || (l != 0 && phOf4 (p - 1) == 51))) ||
      (p == pfStart + 2 * l + 1 && phOf4 p == 51 && phOf4 (p - 1) == 51))

/-- Checked up to the cap check (`phStart4 52`, revision 4.4.1); its four positions are
`cap_items`'. -/
theorem tailCls_check : (List.range (phStart4 52 - p1Start 0)).all
    (fun j => tailCls (p1Start 0 + j)) = true := by
  unfold tailCls p1Start cStart p3S0 pfStart hEll phOf4 phStart4
  rw [fsStarts4_eq]; decide +kernel

theorem tail_cls {p : ℕ} (h1 : p1Start 0 ≤ p) (h2 : p < phStart4 52) :
    (∃ i < 5, ∃ l < hEll i, p = p1Start i + 2 * l ∧ phOf4 p = 26 + 5 * i ∧
      ((l = 0 ∧ phOf4 (p - 1) = 25 + 5 * i) ∨ (l ≠ 0 ∧ phOf4 (p - 1) = 26 + 5 * i))) ∨
    (∃ i < 5, ∃ l < hEll i, p = p1Start i + 2 * l + 1 ∧ phOf4 p = 26 + 5 * i ∧
      phOf4 (p - 1) = 26 + 5 * i) ∨
    (∃ i < 5, p = cStart i ∧ phOf4 p = 27 + 5 * i ∧ phOf4 (p - 1) = 26 + 5 * i) ∨
    (∃ i < 5, cStart i < p ∧ p ≤ p3S0 i + 5) ∨
    (∃ l < 7, p = pfStart + 2 * l ∧ phOf4 p = 51 ∧
      ((l = 0 ∧ phOf4 (p - 1) = 50) ∨ (l ≠ 0 ∧ phOf4 (p - 1) = 51))) ∨
    (∃ l < 7, p = pfStart + 2 * l + 1 ∧ phOf4 p = 51 ∧ phOf4 (p - 1) = 51) := by
  have h := tailCls_check
  simp only [List.all_eq_true, List.mem_range] at h
  have hc := h (p - p1Start 0) (by omega)
  rw [show p1Start 0 + (p - p1Start 0) = p by omega] at hc
  simp only [tailCls, Bool.or_eq_true, List.any_eq_true, List.mem_range, Bool.and_eq_true,
    beq_iff_eq, bne_iff_ne, ne_eq, decide_eq_true_eq] at hc
  rcases hc with (⟨i, hi, l, hl, h⟩ | ⟨i, hi, h⟩) | ⟨l, hl, h⟩
  · rcases h with ⟨⟨h1, h2⟩, h3⟩ | ⟨⟨h1, h2⟩, h3⟩
    · exact Or.inl ⟨i, hi, l, hl, h1, h2, h3⟩
    · exact Or.inr (Or.inl ⟨i, hi, l, hl, h1, h2, h3⟩)
  · rcases h with ⟨⟨h1, h2⟩, h3⟩ | ⟨h1, h2⟩
    · exact Or.inr (Or.inr (Or.inl ⟨i, hi, h1, h2, h3⟩))
    · exact Or.inr (Or.inr (Or.inr (Or.inl ⟨i, hi, h1, h2⟩)))
  · rcases h with ⟨⟨h1, h2⟩, h3⟩ | ⟨⟨h1, h2⟩, h3⟩
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨l, hl, h1, h2, h3⟩))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨l, hl, h1, h2, h3⟩))))

/-- A position inside a multi-squeeze phase is a squeeze of that phase. -/
theorem sq_of_mem {s0 r p : ℕ} (hx : (s0, r) ∈ fsRanges4) (h1 : s0 < p) (h2 : p ≤ s0 + r) :
    fsItems4[p]? = some .squeeze ∧ fsRnd4 p = some (s0, r) := by
  have h := rangesOK4_eq
  simp only [rangesOK4, List.all_eq_true, List.mem_range, Bool.and_eq_true, beq_iff_eq] at h
  have := h _ hx (p - (s0 + 1)) (by simp; omega)
  rwa [show s0 + 1 + (p - (s0 + 1)) = p by omega] at this

theorem sq_tail {i p : ℕ} (hi : i < 5) (h1 : cStart i < p) (h2 : p ≤ p3S0 i + 5) :
    fsItems4[p]? = some .squeeze ∧ fsRnd4 p ≠ none := by
  obtain ⟨-, -, -, -, -, -, -, -, -, hm2, hm3⟩ := tail_ph hi
  have hsq := (tail_pos hi).2.2.2.1
  by_cases h : p ≤ p3S0 i
  · obtain ⟨a, b⟩ := sq_of_mem hm2 h1 (by omega); exact ⟨a, by rw [b]; simp⟩
  · obtain ⟨a, b⟩ := sq_of_mem hm3 (by omega) h2; exact ⟨a, by rw [b]; simp⟩

theorem lt_length_of_get {p : ℕ} {it : Item} (h : fsItems4[p]? = some it) : p < fsItems4.length := by
  by_contra hc; rw [List.getElem?_eq_none (by omega)] at h; simp at h

/-! ## The cap check's positions and the guarded checks (revision 4.4.1, A3′ run 2) -/

/-- The cap check's items (`CapD` absorb, `CapZeta` squeeze, `CapChk` absorb, `CapChkZ` squeeze), single
squeezes, at the end of the chain. -/
theorem cap_items : fsItems4[phStart4 52]? = some (.absorb 27872) ∧ fsItems4[phStart4 53]? = some .squeeze ∧
    fsItems4[phStart4 54]? = some (.absorb 49152) ∧ fsItems4[phStart4 55]? = some .squeeze ∧
    fsRnd4 (phStart4 53) = none ∧ fsRnd4 (phStart4 55) = none ∧ fsItems4.length = phStart4 55 + 1 := by
  obtain ⟨p52, p53, p54, p55⟩ := capPh_pos
  rw [p52, p53, p54, p55, fsItems4_length]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, rfl⟩
  all_goals first
    | (rw [fsItems4, Rev4.seq4_eq]; decide +kernel)
    | (unfold fsRnd4; rw [fsRanges4_eq]; decide)

/-- **Before `D`, or `D` true**: the guard of the composed checks. -/
def cdOK (es : Log) : Prop := es.length ≤ phStart4 52 ∨ truthCap es

/-- **The composed checks, guarded by the cap truth** (A3′ run 2, journal R2.2): once `D` is in the
chain, a failed level check (`RejT`'s round 0 of P1.(i+1) reads the committed words) counts only if
`D` is true; a false `D` is a doom (`DCapD`). On an accepted chain `RejG` fails either way. -/
def RejG (RejF : Log → Log → Prop) (c₀ : Log → Log → K) (L es : Log) : Prop :=
  RejC RejF c₀ L es ∧ cdOK es

theorem cdOK_append {es : Log} (h : es.length ≠ phStart4 52) (x : ByteArray × Digest) :
    cdOK (es ++ [x]) ↔ cdOK es := by
  unfold cdOK
  rw [List.length_append, List.length_singleton]
  rcases Nat.lt_or_ge es.length (phStart4 52) with hl | hl
  · exact ⟨fun _ => Or.inl (by omega), fun _ => Or.inl (by omega)⟩
  · have hl' : phStart4 53 ≤ es.length := by have := capPh_pos; omega
    rw [(capD_congr (agree_append es [x] hl')).2.2]
    exact ⟨fun h' => h'.resolve_left (by omega) |> Or.inr, fun h' => h'.resolve_left (by omega) |> Or.inr⟩

theorem rejG_of {RejF : Log → Log → Prop} {c₀ : Log → Log → K} {L es : Log}
    (h : RejC RejF c₀ L es) (hl : es.length ≤ phStart4 52) : RejG RejF c₀ L es := ⟨h, Or.inl hl⟩

theorem not_rejC_of {RejF : Log → Log → Prop} {c₀ : Log → Log → K} {L es : Log}
    (h : ¬ RejG RejF c₀ L es) (hl : es.length ≤ phStart4 52) : ¬ RejC RejF c₀ L es := fun h' => h ⟨h', Or.inl hl⟩

theorem rejG_sq {RejF : Log → Log → Prop} {c₀ : Log → Log → K} (hR : RejOK (RejC RejF c₀)) :
    RejSq (RejG RejF c₀) where
  sq L es x hit := by
    have h52 : es.length ≠ phStart4 52 := fun h => by rw [h, cap_items.1] at hit; cases hit
    unfold RejG; rw [hR.sq L es x hit, cdOK_append h52]
  stab L i hb hci X hX := by unfold RejG; rw [hR.stab L i hb hci X hX]

theorem phOf_cap : phOf4 (phStart4 52 - 1) = 51 ∧ phOf4 (phStart4 52) = 52 ∧ phOf4 (phStart4 53) = 53 ∧
    phOf4 (phStart4 54) = 54 ∧ phOf4 (phStart4 55) = 55 := by
  have e : pfStart = 468 := by unfold pfStart phStart4; rw [fsStarts4_eq]; rfl
  obtain ⟨p52, p53, p54, p55⟩ := capPh_pos
  refine ⟨(phOf_ge (by omega)).1 (by omega), (phOf_ge (by omega)).2.1 rfl, (phOf_ge (by omega)).2.2.1 rfl,
    (phOf_ge (by omega)).2.2.2.1 rfl, (phOf_ge (by omega)).2.2.2.2 le_rfl⟩

variable {RejF : Log → Log → Prop} {DF : ℕ → Log → Log → Prop} {W₀ : Log → Log → ℕ → K}
  {c₀ : Log → Log → K}

/-- **`hrej`**: at an absorb a guarded check that held still holds, or (at `CapD`) `D` is false. -/
theorem hrej_G (hR : RejOK (RejC RejF c₀)) (L es : Log) (x : ByteArray × Digest)
    (h : RejG RejF c₀ L es) :
    RejG RejF c₀ L (es ++ [x]) ∨ DkC DF W₀ c₀ (phOf4 es.length) L (es ++ [x]) := by
  have hr := hR.mono L es x h.1
  by_cases h52 : es.length = phStart4 52
  · by_cases ht : truthCap (es ++ [x])
    · exact Or.inl ⟨hr, Or.inr ht⟩
    · right
      rw [h52, phOf_cap.2.1, DkC_ge (by norm_num), (DT_cap W₀ c₀).1]
      exact Or.inr ht
  · exact Or.inl ⟨hr, (cdOK_append h52 x).2 h.2⟩

/-- **The cap check's absorbs** (`CapD`, `CapChk`): an absorb never undooms. -/
theorem habs_cap (hF : FrontLocal W₀ c₀) {L es : Log} {x : ByteArray × Digest} {len : ℕ}
    (hit : fsItems4[es.length]? = some (.absorb len)) (h52 : phStart4 52 ≤ es.length)
    (hd : DT W₀ c₀ (phOf4 (es.length - 1)) L es) : DT W₀ c₀ (phOf4 es.length) L (es ++ [x]) := by
  obtain ⟨i52, i53, i54, i55, -, -, hlen⟩ := cap_items
  obtain ⟨p52, p53, p54, p55⟩ := capPh_pos
  obtain ⟨f51, f52, f53, f54, f55⟩ := phOf_cap
  obtain ⟨d52, d53, d54, d55⟩ := DT_cap W₀ c₀
  have hlt := lt_length_of_get hit
  have hpf : pfStart + 14 ≤ es.length := by rw [pfStart_eq]; omega
  have e : es.length = phStart4 52 ∨ es.length = phStart4 54 := by
    rcases (show es.length = 482 ∨ es.length = 483 ∨ es.length = 484 ∨ es.length = 485 by omega) with
      h | h | h | h
    · exact Or.inl (by omega)
    · rw [show es.length = phStart4 53 by omega, i53] at hit; cases hit
    · exact Or.inr (by omega)
    · rw [show es.length = phStart4 55 by omega, i55] at hit; cases hit
  rcases e with e | e
  · rw [e, f52, d52]
    rw [show es.length - 1 = phStart4 52 - 1 by omega, f51, DT_Pf] at hd
    exact Or.inl ((DPf_append hF hpf x).2 hd)
  · rw [e, f54, d54]
    rw [show es.length - 1 = phStart4 53 by omega, f53, d53] at hd
    have hag : Agree (es ++ [x]) es (phStart4 54) := agree_append es [x] (by omega)
    have ht := (capD_congr (hag.mono (by omega))).2.2
    have hs := (capZeta_congr hag).2.2.2.1
    rcases hd with ⟨hp, htc⟩ | ⟨htc, hsg⟩
    · exact Or.inl ⟨(DPf_append hF hpf x).2 hp, ht.2 htc⟩
    · by_cases ha : aHon (es ++ [x])
      · exact Or.inr (Or.inl ⟨ha, fun h => htc (ht.1 h), fun h => hsg (hs.1 h)⟩)
      · exact Or.inr (Or.inr ha)

open Classical in
/-- **The cap check's squeezes** (`CapZeta`, `CapChkZ`): the escapes are `DZeta` (`≤ 870`) and
`DZ` (`≤ 1,535`) answers. -/
theorem single_cap (hF : FrontLocal W₀ c₀) {L es : Log} (hit : fsItems4[es.length]? = some .squeeze)
    (h52 : phStart4 52 ≤ es.length) :
    (univ.filter fun a => DT W₀ c₀ (phOf4 (es.length - 1)) L es ∧
      ¬ DT W₀ c₀ (phOf4 es.length) L (ext1 es a)).card ≤ 239 * 2 ^ 128 := by
  obtain ⟨i52, i53, i54, i55, -, -, hlen⟩ := cap_items
  obtain ⟨p52, p53, p54, p55⟩ := capPh_pos
  obtain ⟨f51, f52, f53, f54, f55⟩ := phOf_cap
  obtain ⟨d52, d53, d54, d55⟩ := DT_cap W₀ c₀
  have hlt := lt_length_of_get hit
  have hpf : pfStart + 14 ≤ es.length := by rw [pfStart_eq]; omega
  have hP : ∀ a, DPf W₀ c₀ L (ext1 es a) ↔ DPf W₀ c₀ L es := fun a => DPf_append hF hpf _
  have e : es.length = phStart4 53 ∨ es.length = phStart4 55 := by
    rcases (show es.length = 482 ∨ es.length = 483 ∨ es.length = 484 ∨ es.length = 485 by omega) with
      h | h | h | h
    · rw [show es.length = phStart4 52 by omega, i52] at hit; cases hit
    · exact Or.inl (by omega)
    · rw [show es.length = phStart4 54 by omega, i54] at hit; cases hit
    · exact Or.inr (by omega)
  rcases e with e | e
  · rw [e, f53, d53, show phStart4 53 - 1 = phStart4 52 by omega, f52, d52]
    have hag : ∀ a, Agree (ext1 es a) es (phStart4 53) := fun a => by
      rw [ext1]; exact agree_append es _ (by omega)
    have ht : ∀ a, truthCap (ext1 es a) ↔ truthCap es := fun a => (capD_congr (hag a)).2.2
    by_cases htc : truthCap es
    · rw [filter_false_of_mem fun a _ h => h.2 (Or.inl ⟨(hP a).2 (h.1.resolve_right (not_not.2 htc)),
        (ht a).2 htc⟩)]
      simp
    · refine le_trans (card_le_card fun a ha => ?_) ((card_dZeta e htc).trans (by norm_num))
      simp only [mem_filter, mem_univ, true_and] at ha ⊢
      by_contra hs
      exact ha.2 (Or.inr ⟨fun h => htc ((ht a).1 h), hs⟩)
  · rw [e, f55, d55, show phStart4 55 - 1 = phStart4 54 by omega, f54, d54]
    have hag : ∀ a, Agree (ext1 es a) es (phStart4 55) := fun a => by
      rw [ext1]; exact agree_append es _ (by omega)
    have ht : ∀ a, truthCap (ext1 es a) ↔ truthCap es := fun a => (capD_congr ((hag a).mono (by omega))).2.2
    have hs : ∀ a, capSig0 (ext1 es a) ↔ capSig0 es := fun a => (capZeta_congr ((hag a).mono (by omega))).2.2.2.1
    have hon : ∀ a, aHon (ext1 es a) ↔ aHon es := fun a => (capA_congr (hag a)).2
    by_cases ha : aHon es
    · rw [filter_false_of_mem fun a _ h => ?_]
      · simp
      rcases h.1 with ⟨hp, htc⟩ | ⟨-, htc, hsg⟩ | hna
      · exact h.2 (Or.inl ⟨(hP a).2 hp, (ht a).2 htc⟩)
      · exact h.2 (Or.inr (Or.inl ⟨(hon a).2 ha, fun h' => htc ((ht a).1 h'), fun h' => hsg ((hs a).1 h')⟩))
      · exact hna ha
    · refine le_trans (card_le_card fun a hm => ?_) ((card_dZ e ha).trans (by norm_num))
      simp only [mem_filter, mem_univ, true_and] at hm ⊢
      by_contra hne
      exact hm.2 (Or.inr (Or.inr ⟨fun h' => ha ((hon a).1 h'), hne⟩))

/-! ## `PhaseObl` -/

/-- **The per-phase obligations of the whole transcript**, from the front's and the tail's. -/
theorem phaseObl_of (hFr : FrontObl RejF DF W₀ c₀) :
    PhaseObl (RejG RejF c₀) (DkC DF W₀ c₀) (239 * 2 ^ 128) where
  rej := rejG_sq (rejOK_or hFr.rej (rejT_ok hFr.loc))
  hrej L es x _ _ _ h := hrej_G (rejOK_or hFr.rej (rejT_ok hFr.loc)) L es x h
  ms s0 r hmem := by
    by_cases h : s0 + 1 < p1Start 0
    · obtain ⟨fin, hf⟩ := hFr.ms s0 r hmem h
      exact ⟨fin, by rw [DkC_lt (phOf_lt_26 h), DkC_lt (phOf_lt_26 (by omega)), hf]⟩
    rcases front_facts.2.2.2.2 _ hmem with hx | ⟨i, hi, hx | hx⟩
    · have := (ms_phOf hmem).1; simp at hx; omega
    · simp only [Prod.mk.injEq] at hx; obtain ⟨rfl, rfl⟩ := hx
      exact ⟨_, ms_P2 hi (by rw [DkC_ge (by omega), DT_C W₀ c₀ hi])
        (by rw [DkC_ge (by omega), DT_P2 W₀ c₀ hi])⟩
    · simp only [Prod.mk.injEq] at hx; obtain ⟨rfl, rfl⟩ := hx
      exact ⟨_, ms_P3 hi (by rw [DkC_ge (by omega), DT_P2 W₀ c₀ hi])
        (by rw [DkC_ge (by omega), DT_P3 W₀ c₀ hi])⟩
  habs L es x len hm hit hr hd := by
    have hlt := lt_length_of_get hit
    have h0 : p1Start 0 < phStart4 52 := by
      unfold p1Start phStart4; rw [fsStarts4_eq]; decide
    by_cases hcap : phStart4 52 ≤ es.length
    · right
      rw [DkC_ge (phOf_ge_26 (by omega))] at hd
      rw [DkC_ge (phOf_ge_26 (by omega))]
      exact habs_cap hFr.loc hit hcap hd
    have hr' := not_rejC_of hr (by omega)
    by_cases hp : es.length < p1Start 0
    · rw [DkC_lt (phOf_lt_26 (by omega))] at hd
      rw [DkC_lt (phOf_lt_26 hp)]
      exact (hFr.habs L es x len hm hit hp hr' hd).imp_left fun h => rejG_of h (by simp; omega)
    by_cases hp' : es.length = p1Start 0
    · rw [hp', front_facts.2.2.1, DkC_lt (by norm_num)] at hd
      have := (hFr.handoff L es x len hm hit hp' hr' hd).imp_left fun h => rejG_of h (by simp; omega)
      have hD : DT W₀ c₀ 26 = D1 W₀ c₀ 0 := DT_P1 W₀ c₀ (i := 0) (by norm_num)
      rwa [hp', (tail_ph (show 0 < 5 by norm_num)).1, DkC_ge le_rfl, hD]
    rcases tail_cls (by omega) (by omega : es.length < phStart4 52) with ⟨i, hi, l, hl, he, h1, h2⟩ | ⟨i, hi, l, hl, he, -, -⟩ |
      ⟨i, hi, he, h1, h2⟩ | ⟨i, hi, h1, h2⟩ | ⟨l, hl, he, h1, h2⟩ | ⟨l, hl, he, -, -⟩
    · right
      rw [h1, DkC_ge (by omega), DT_P1 W₀ c₀ hi]
      rcases h2 with ⟨rfl, h2⟩ | ⟨hl0, h2⟩
      · obtain ⟨j, rfl⟩ : ∃ j, i = j + 1 := ⟨i - 1, by
          rcases Nat.eq_zero_or_pos i with rfl | h
          · simp at he; omega
          · omega⟩
        rw [h2, show 25 + 5 * (j + 1) = 30 + 5 * j by ring, DkC_ge (by omega),
          DT_P3 W₀ c₀ (by omega), DP3, msD, ite_neg' (by
            have := (tail_pos (show j < 5 by omega)).2.2.2.2
            rw [nxStart_le hi] at this; omega)] at hd
        exact habs_P1_next hFr.loc x hi (by omega) hd
      · rw [h2, DkC_ge (by omega), DT_P1 W₀ c₀ hi] at hd
        exact habs_P1 hFr.loc x hi (by omega) he hd
    · have := (rounds_P1 hi hl).2; rw [← he, hit] at this; simp at this
    · right
      rw [h2, DkC_ge (by omega), DT_P1 W₀ c₀ hi] at hd
      rw [h1, DkC_ge (by omega), DT_C W₀ c₀ hi]
      exact habs_C hFr.loc x hi he hd
    · have := (sq_tail hi h1 h2).1; rw [hit] at this; simp at this
    · right
      rw [h1, DkC_ge (by omega), DT_Pf]
      rcases h2 with ⟨rfl, h2⟩ | ⟨hl0, h2⟩
      · rw [h2, show (50 : ℕ) = 30 + 5 * 4 by norm_num, DkC_ge (by omega),
          DT_P3 W₀ c₀ (by norm_num), DP3, msD, ite_neg' (by
            have := (tail_pos (show 4 < 5 by norm_num)).2.2.2.2
            have hnx : nxStart 4 = pfStart := rfl
            omega)] at hd
        exact habs_Pf_first hFr.loc x (by omega) hd
      · rw [h2, DkC_ge (by omega), DT_Pf] at hd
        exact habs_Pf hFr.loc x (by omega) he hd
    · have := (rounds_Pf hl).2; rw [← he, hit] at this; simp at this
  hsingle L es hm hit hrnd hr := by
    have hlt := lt_length_of_get hit
    have h0 : p1Start 0 < phStart4 52 := by
      unfold p1Start phStart4; rw [fsStarts4_eq]; decide
    by_cases hcap : phStart4 52 ≤ es.length
    · have e1 : 26 ≤ phOf4 (es.length - 1) := phOf_ge_26 (by omega)
      have e2 : 26 ≤ phOf4 es.length := phOf_ge_26 (by omega)
      have hc := single_cap hFr.loc hit hcap (L := L)
      refine le_trans (card_le_card ?_) hc
      intro a ha
      simp only [mem_filter, mem_univ, true_and] at ha ⊢
      rwa [DkC_ge e1, DkC_ge e2] at ha
    have hr' := not_rejC_of hr (by omega)
    by_cases hp : es.length < p1Start 0
    · rw [DkC_lt (phOf_lt_26 (by omega)), DkC_lt (phOf_lt_26 hp)]
      exact hFr.hsingle L es hm hit hrnd hp hr'
    have hrT : ¬ RejT c₀ L es := fun h => hr' (Or.inr h)
    rcases tail_cls (by omega) (by omega : es.length < phStart4 52) with ⟨i, hi, l, hl, he, -, -⟩ | ⟨i, hi, l, hl, he, h1, h2⟩ |
      ⟨i, hi, he, -, -⟩ | ⟨i, hi, h1, h2⟩ | ⟨l, hl, he, -, -⟩ | ⟨l, hl, he, h1, h2⟩
    · have := (rounds_P1 hi hl).1; rw [← he, hit] at this; simp at this
    · rw [h1, h2, DkC_ge (by omega), DT_P1 W₀ c₀ hi]
      exact (single_P1 hFr.loc hi hl he hrT).trans (p1_N_le _ hi)
    · exact absurd (he ▸ hit) (front_facts.2.2.2.1 i hi)
    · exact absurd hrnd (sq_tail hi h1 h2).2
    · have := (rounds_Pf hl).1; rw [← he, hit] at this; simp at this
    · rw [h1, h2, DkC_ge (by omega), DT_Pf]
      exact (single_Pf hFr.loc he hrT).trans (by norm_num)
  hfin s0 r hmem L es₀ hm hl hr := by
    by_cases h : s0 + 1 < p1Start 0
    · have hb : s0 + r < p1Start 0 := by
        rcases front_facts.2.2.2.2 _ hmem with hx | ⟨i, hi, hx | hx⟩
        · exact hx
        all_goals
          simp only [Prod.mk.injEq] at hx; obtain ⟨rfl, rfl⟩ := hx
          have h0 : p1Start 0 ≤ p1Start i := front_facts.1 (5 * i) (by omega)
          obtain ⟨-, -, h3, h4, -⟩ := tail_pos hi
          omega
      have h0 : p1Start 0 < phStart4 52 := by
        unfold p1Start phStart4; rw [fsStarts4_eq]; decide
      refine le_trans (le_of_eq (condCount_congr fun as has => ?_))
        (hFr.hfin s0 r hmem h L es₀ hm hl (not_rejC_of hr (by omega)))
      have hlx := length_ext as es₀
      have hd : (ext es₀ as).dropLast.length = s0 + r := by
        rw [List.length_dropLast]; omega
      simp only [EscAtG, DPos, Dp, hd, hlx, hl, has]
      rw [DkC_lt (phOf_lt_26 (by omega)), DkC_lt (phOf_lt_26 (by omega))]
    rcases front_facts.2.2.2.2 _ hmem with hx | ⟨i, hi, hx | hx⟩
    · have := (ms_phOf hmem).1; simp at hx; omega
    · simp only [Prod.mk.injEq] at hx; obtain ⟨rfl, rfl⟩ := hx
      exact hfin_P2 hFr.loc hi (by rw [DkC_ge (by omega), DT_C W₀ c₀ hi])
        (by rw [DkC_ge (by omega), DT_P2 W₀ c₀ hi]) L es₀ hl
    · simp only [Prod.mk.injEq] at hx; obtain ⟨rfl, rfl⟩ := hx
      exact hfin_P3 hFr.loc hi (by rw [DkC_ge (by omega), DT_P2 W₀ c₀ hi])
        (by rw [DkC_ge (by omega), DT_P3 W₀ c₀ hi]) L es₀ hl
  hstab k L i hb hci X hX hk := by
    by_cases h : k < 26
    · rw [DkC_lt h]; exact hFr.hstab k h L i hb hci X hX hk
    rw [DkC_ge (by omega)]
    have hX1 : 1 ≤ X.length := by
      obtain ⟨s0, r, as, -, hs, -, rfl⟩ := hX
      rw [length_ext, List.length_take]; omega
    obtain ⟨h1, h2, -⟩ := phOf_bounds (X.length - 1)
    rw [hk] at h1 h2
    exact DT_stab hFr.loc (by omega) h2 (same_stabX hb hci hX) le_rfl (by omega)

/-- T4: **the potential's laws at `εR` from the front's obligations** (3.x's `kstate_of_front`
without 3.x's `KState`/`FinalLaw`, whose verifier is 3.x's): `muT (RejG …) (DkC …)` starts at `0`
and meets the contract's `step` law at `εR = 15/2^124`. These are `ks4_of`'s `h0` and `hstep`
(`ks4_of_front`, `FRSoundness4TailLig`). -/
theorem muT_laws_of_front (hFr : FrontObl RejF DF W₀ c₀) :
    muT (RejG RejF c₀) (DkC DF W₀ c₀) [] = 0 ∧
    ∀ L q, L.length < logCap → muT (RejG RejF c₀) (DkC DF W₀ c₀) L < 1 → q ∉ L.map Prod.fst →
      ∑ a : Digest, muT (RejG RejF c₀) (DkC DF W₀ c₀) (L ++ [(q, a)]) ≤
        (muT (RejG RejF c₀) (DkC DF W₀ c₀) L + epsR) * 2 ^ 256 :=
  ⟨muT_empty _ _, fun L q hl hμ hq => muT_step N_le (phaseObl_of hFr) L q hl hμ hq⟩

/-! ## Stability on the chain itself (`ChainStab`, S-G1h deviation 1) -/

/-- On a non-bad log, a chain reads the same off the log before its last entry and off the log
(its caps are real entries, `capOK_of_matches`, `wordK_stab`). -/
theorem same_chain {L : Log} (hb : ¬ Bad L) {j : ℕ} (hci : G.IsChain L j) :
    Same (L.take j) (entriesOf L (pathOf L j)) L (entriesOf L (pathOf L j))
      (entriesOf L (pathOf L j)).length := by
  set es := entriesOf L (pathOf L j)
  have hes : ext (es.take es.length) [] = es := by rw [ext_nil, List.take_length]
  refine ⟨fun _ _ => rfl, fun κ i hi hc => ?_⟩
  have hw := wordK_stab hb hci es.length [] hi κ (by rw [hes]; exact capOK_of_matches hci.2 hi hc)
  rwa [hes] at hw

/-- The tail's asserted checks read the same off two logs whose words agree. -/
theorem rejT_same (hF : FrontLocal W₀ c₀) {L L' Y : Log} {p : ℕ} (hS : Same L Y L' Y p)
    (hY : Y.length ≤ p) : RejT c₀ L Y ↔ RejT c₀ L' Y := by
  refine or_congr ⟨fun ⟨i, hi, j, hj, hlt, hc⟩ => ⟨i, hi, j, hj, hlt, fun h' => hc ?_⟩,
    fun ⟨i, hi, j, hj, hlt, hc⟩ => ⟨i, hi, j, hj, hlt, fun h' => hc ?_⟩⟩
    ⟨fun ⟨j, hj, hlt, hc⟩ => ⟨j, hj, hlt, fun h' => hc ?_⟩,
    fun ⟨j, hj, hlt, hc⟩ => ⟨j, hj, hlt, fun h' => hc ?_⟩⟩
  · exact (chk2_same hS (by omega) (lvC_same hF hS hi (by omega))).mpr h'
  · exact (chk2_same hS (by omega) (lvC_same hF hS hi (by omega))).mp h'
  · exact (chk2_same hS (by omega) (lvC5_same hF hS (by omega))).mpr h'
  · exact (chk2_same hS (by omega) (lvC5_same hF hS (by omega))).mp h'

/-- What the front owes for `ChainStab`: its checks and dooms read the same on the chain itself. -/
def FrontChainStab (RejF : Log → Log → Prop) (DF : ℕ → Log → Log → Prop) : Prop :=
  ∀ L j, ¬ Bad L → G.IsChain L j →
    (RejF (L.take j) (entriesOf L (pathOf L j)) ↔ RejF L (entriesOf L (pathOf L j))) ∧
    ∀ k < 26, phOf4 ((entriesOf L (pathOf L j)).length - 1) = k →
      (DF k (L.take j) (entriesOf L (pathOf L j)) ↔ DF k L (entriesOf L (pathOf L j)))

/-- **`ChainStab` for the whole transcript's doom** (what `final`'s walk needs, S-G1h deviation 1;
revision 4.4.1: the checks guarded, `RejG`):
the tail's part is proved (`same_chain`, `DT_stab`, `rejT_same`); the front's is `FrontChainStab`. -/
theorem chainStab_of (hF : FrontLocal W₀ c₀) (hFS : FrontChainStab RejF DF) :
    ChainStab (DC (RejG RejF c₀) (Dp (DkC DF W₀ c₀))) := by
  intro L j hb hci
  set es := entriesOf L (pathOf L j)
  have hS := same_chain hb hci
  obtain ⟨hR, hD⟩ := hFS L j hb hci
  have h1 : 1 ≤ es.length := List.length_pos_iff.mpr (G.matches_ne_nil hci.2)
  unfold DC RejG RejC DPos Dp
  refine or_congr (and_congr (or_congr hR (rejT_same hF hS le_rfl)) Iff.rfl) ?_
  by_cases hk : phOf4 (es.length - 1) < 26
  · rw [DkC_lt hk]; exact hD _ hk rfl
  rw [DkC_ge (by omega)]
  obtain ⟨b1, b2, -⟩ := phOf_bounds (es.length - 1)
  have hl : (entriesOf L (pathOf L j)).length = es.length := rfl
  exact DT_stab hF (by omega) b2 hS le_rfl (by rw [hl]; omega)

/-! ## Controls -/

/-- Control (positive): on the empty log every intermediate fold is close (the word is `0`). -/
theorem closeP_nil (κ : CKind) (es : Log) {i l : ℕ} (hl : l ≤ (CKind.lv κ i).ell) :
    closeP κ [] es i l := closeP_of_not_far (not_farL_nil κ es i) l hl

/-- Control (positive): a far word before P1.i's first answer dooms P1.i (the far part is live). -/
theorem D1_of_far {i : ℕ} {L es : Log} (h0 : hRnd es i = 0) (hf : farL (kindOfC es) L es i) :
    D1 W₀ c₀ i L es := Or.inl (by rw [h0, closeP_zero, not_not]; exact hf)

/-- Control (negative): on the empty log, before P1.i's first absorb, P1.i is not doomed. -/
theorem not_D1_nil {i : ℕ} {es : Log} (hl : es.length ≤ p1Start i) : ¬ D1 W₀ c₀ i [] es := by
  rintro (h | ⟨-, hd⟩)
  · have h0 : hRnd es i = 0 := by unfold hRnd; omega
    rw [h0] at h; exact h (closeP_nil _ _ (Nat.zero_le _))
  · exact not_D2_short hl hd

/-- Control (negative): with every query consistent and no offset, P3.i's table is zero. -/
theorem p3T_zero {κ : CKind} {L es : Log} {i : ℕ} (h : truthP3 κ L es i) :
    tbl 9 (p3T κ L es i 0) = 0 := by
  funext q
  rw [tbl_p3T, add_zero]
  split_ifs with hq
  · exact h q hq
  · rfl

/-- Control (negative): no tail check fails before P1.0's first absorb. -/
theorem not_rejT_short {L es : Log} (hl : es.length ≤ p1Start 0) : ¬ RejT c₀ L es := by
  rintro (⟨i, hi, j, -, hlt, -⟩ | ⟨j, -, hlt, -⟩)
  · have : p1Start 0 ≤ p1Start i := front_facts.1 (5 * i) (by omega)
    omega
  · have : p1Start 0 ≤ pfStart := front_facts.1 25 (by norm_num)
    omega

open Classical in
/-- Control (positive, satisfiability): the empty front with constant `W₀`, `c₀` meets
`FrontObl` (the interface is not contradictory). -/
theorem frontObl_false :
    FrontObl (fun _ _ => False) (fun _ _ _ => False) (fun _ _ _ => 0) (fun _ _ => 0) where
  loc _ _ _ _ _ _ _ := ⟨rfl, rfl⟩
  rej := rejOK_false
  ms _ _ _ _ := ⟨fun _ _ => False, by funext L es; simp only [msD, eq_iff_iff]; split_ifs <;> rfl⟩
  habs _ _ _ _ _ _ _ _ h := h.elim
  handoff _ _ _ _ _ _ _ _ h := h.elim
  hsingle _ _ _ _ _ _ _ := by simp
  hfin _ _ _ _ L es₀ _ _ _ := by
    rw [condCount_eq_zero fun _ _ h => h.2.1]; exact zero_le
  hstab _ _ _ _ _ _ _ _ _ := Iff.rfl

end FR.Snd.T4

end G6_FRSoundness4TailC
