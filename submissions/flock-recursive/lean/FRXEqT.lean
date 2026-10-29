-- New for `flock-recursive` (BLUEPRINT §6.2 step 4, the K-folds; stage S-H2, track L-ext).
import FRXFwd
import FRXLevel
import FRXBary

/-!
# The `eq` table of P1.i's challenges on the machine

The column fold `foldAt` weighs row `r` by `eqBits s ℓ r`. Here `s_v` is P1.i's challenge `v`, the
K answer of FS position `phStart (26 + 5i) + 2v + 1`. The chain replay leaves that answer's four
words at `ansB + 4p` (`chain_dec`), so the challenges sit at `cb + 8v` (`kAt_words`).

`eqtIR ℓ cb eb` writes `E[x] = eqBits S ℓ x` at `eb + 4x` for `x < 2^ℓ` (K, `rdK`). Each entry
is computed directly by its definition `∏_{v<ℓ} (bit_v x ? s_v : 1 − s_v)`. That costs `ℓ` K
products per entry, `≤ 384` in all (`ℓ ≤ 6`).

* `eqBody_sem`: one factor;
* `eqEnt_sem`: one entry (the product over `v`, in `range` order);
* **`eqtIR_sem`**: the table, and the heap outside it kept.

Registers `190 … 212` (the chain's, free after the replay).
-/

namespace FR.X

open RecursionFast FR Finset

attribute [local irreducible] entryK storeM runPrims

/-! ## Registers and the program -/

/-- The accumulator (K). -/ def kA : ℕ := 190
/-- The challenge `s_v` (K). -/ def kS : ℕ := 194
/-- `1 − s_v` (K). -/ def kO : ℕ := 198
/-- The entry `x`. -/ def eX : ℕ := 202
/-- The factor `v`. -/ def eV : ℕ := 203
/-- An address. -/ def eAd : ℕ := 204
/-- Its successor. -/ def eA1 : ℕ := 205
/-- A second address. -/ def eA2 : ℕ := 206
/-- Bit `v` of `x`. -/ def eBit : ℕ := 207
/-- Constant scratch. -/ def eK : ℕ := 208
/-- Counter of the entry loop. -/ def eC1 : ℕ := 209
/-- Its count. -/ def eN1 : ℕ := 210
/-- Counter of the factor loop. -/ def eC2 : ℕ := 211
/-- Its count. -/ def eN2 : ℕ := 212

/-- `kO := 1 + kS` (`1 − s` in characteristic 2). -/
def omPs : List Prim :=
  [.op .xor kO kS cOne, .op .or (kO + 1) (kS + 1) (kS + 1), .op .or (kO + 2) (kS + 2) (kS + 2),
   .op .or (kO + 3) (kS + 3) (kS + 3)]

/-- `eBit := bit_v x`, `eAd += 8`, `v += 1`. -/
def bitPs : List Prim :=
  [.op .shr eBit eX eV, .op .and eBit eBit cOne, .const eK 8, .op .add eAd eAd eK,
   .op .add eV eV cOne]

/-- **One factor**: `acc *= (bit_v x ? s_v : 1 − s_v)`, `s_v` at `M[eAd]`. -/
def eqBody : XIR :=
  .seq (ldF kS eAd eA1) (.seq (.blk [.const eK 2, .op .add eA2 eAd eK]) (.seq (ldF (kS + 2) eA2 eA1)
    (.seq (.blk omPs) (.seq (.blk bitPs) (.ite eBit (mulK kA kA kS) (mulK kA kA kO))))))

/-- `acc := 1`, `v := 0`, `eAd := cb`. -/
def entPre (ℓ cb : ℕ) : List Prim :=
  [.const kA 1, .const (kA + 1) 0, .const (kA + 2) 0, .const (kA + 3) 0, .const eV 0,
   .const eAd (toWord cb), .const eN2 (toWord ℓ)]

/-- `eAd := eb + 4x`, `eA2 := eAd + 2`. -/
def entAd (eb : ℕ) : List Prim :=
  [.op .add eAd eX eX, .op .add eAd eAd eAd, .const eK (toWord eb), .op .add eAd eAd eK,
   .const eK 2, .op .add eA2 eAd eK]

/-- **One entry** `E[x] := ∏_{v<ℓ} …`, stored at `eb + 4x`; `x += 1`. -/
def eqEnt (ℓ cb eb : ℕ) : XIR :=
  .seq (.blk (entPre ℓ cb)) (.seq (.loopK eC2 eN2 (toWord ℓ) eqBody) (.seq (.blk (entAd eb))
    (.seq (stF eAd eA1 kA) (.seq (stF eA2 eA1 (kA + 2)) (.blk [.op .add eX eX cOne])))))

/-- **The table** `E[x] = eqBits S ℓ x` at `eb + 4x`, `x < 2^ℓ`. -/
def eqtIR (ℓ cb eb : ℕ) : XIR :=
  .seq (.blk [.const eX 0, .const eN1 (toWord (2 ^ ℓ))])
    (.loopK eC1 eN1 (toWord (2 ^ ℓ)) (eqEnt ℓ cb eb))

/-! ## Well formed, no tape loop, no output, cost -/

theorem nw_mulK {d a b c : ℕ} (hc : 31 ≤ c) (h0 : c ≠ d) (h1 : c ≠ d + 1) (h2 : c ≠ d + 2)
    (h3 : c ≠ d + 3) : ¬ Writes (mulK d a b) c := fun ⟨p, hp, he⟩ => by
  rcases mulKC_dst d a b p hp with h | h | h | h | h <;> omega

theorem lo_mulK {d a b : ℕ} (h : d + 3 < regs) : Lo (mulK d a b) := fun p hp => by
  rcases mulKC_dst d a b p hp with h' | h' | h' | h' | h' <;> simp only [regs] at * <;> omega

theorem wf_eqBody : WF eqBody := by
  have m1 := wf_mulK kA kA kS (by decide)
  have m2 := wf_mulK kA kA kO (by decide)
  simp only [eqBody, omPs, bitPs, ldF, WF, Prim.dst, List.mem_cons, List.mem_nil_iff, m1, m2]
  simp [kS, kO, eA1, eA2, eAd, eK, eBit, eV, regs]

theorem eqBody_nw {r : ℕ} (hr : r = eX ∨ r = eC1 ∨ r = eN1 ∨ r = eC2 ∨ r = eN2) :
    ¬ Writes eqBody r := by
  have hr' : 31 ≤ r ∧ r ≠ kA ∧ r ≠ kA + 1 ∧ r ≠ kA + 2 ∧ r ≠ kA + 3 := by
    rcases hr with rfl | rfl | rfl | rfl | rfl <;> decide
  have n1 := nw_mulK (a := kA) (b := kS) hr'.1 hr'.2.1 hr'.2.2.1 hr'.2.2.2.1 hr'.2.2.2.2
  have n2 := nw_mulK (a := kA) (b := kO) hr'.1 hr'.2.1 hr'.2.2.1 hr'.2.2.2.1 hr'.2.2.2.2
  simp only [eqBody, omPs, bitPs, ldF, Writes, Prim.dst, List.mem_cons, List.mem_nil_iff, n1, n2]
  rcases hr with rfl | rfl | rfl | rfl | rfl <;>
    simp [kS, kO, eA1, eA2, eAd, eK, eBit, eV, eX, eC1, eN1, eC2, eN2]

theorem wf_eqtIR (ℓ cb eb : ℕ) : WF (eqtIR ℓ cb eb) := by
  have n1 := eqBody_nw (r := eC2) (by simp)
  have n2 := eqBody_nw (r := eC1) (by simp)
  simp only [eqtIR, eqEnt, entPre, entAd, stF, WF, Writes, Prim.dst, List.mem_cons,
    List.mem_nil_iff, wf_eqBody, n1, n2]
  simp [kA, eX, eV, eAd, eA1, eA2, eK, eC1, eN1, eC2, eN2, cTmp, regs]

theorem noLoopT_eqtIR (ℓ cb eb : ℕ) : NoLoopT (eqtIR ℓ cb eb) := by
  simp [eqtIR, eqEnt, eqBody, ldF, stF, mulK, NoLoopT]

theorem outs_eqtIR (ℓ cb eb t : ℕ) : outs (eqtIR ℓ cb eb) t = 0 := by
  simp [eqtIR, eqEnt, eqBody, ldF, stF, mulK, outs]

/-- **The table's cost**: `2^ℓ` entries of `ℓ` factors. -/
theorem cost_eqtIR (ℓ cb eb t : ℕ) (hℓ : 2 ^ ℓ < 2 ^ 64) (hℓ' : ℓ < 2 ^ 64) :
    cost (eqtIR ℓ cb eb) t = 12 + 2 ^ ℓ * (63 + ℓ * 271) := by
  have a1 : (toWord (2 ^ ℓ)).toNat = 2 ^ ℓ := toNat_toWord hℓ
  have a2 : (toWord ℓ).toNat = ℓ := toNat_toWord hℓ'
  simp only [eqtIR, eqEnt, entPre, entAd, eqBody, omPs, bitPs, ldF, stF, mulK, cost, blkSteps,
    len_mulKC, List.length_cons, List.length_nil, a1, a2]
  norm_num
  ring

/-! ## One factor -/

/-- `1 − s` on the machine's words. -/
theorem rdK_one_sub (k0 k1 k2 k3 : Word) :
    (⟨⟨wB (k0 ^^^ 1), wB (k1 ||| k1)⟩, ⟨wB (k2 ||| k2), wB (k3 ||| k3)⟩⟩ : K) =
      1 - (⟨⟨wB k0, wB k1⟩, ⟨wB k2, wB k3⟩⟩ : K) := by
  rw [rdF_add_one, BitVec.or_self, BitVec.or_self]
  show (⟨⟨wB k0, wB k1⟩ + 1, ⟨wB k2, wB k3⟩⟩ : K) = ⟨1 + ⟨wB k0, wB k1⟩, 0 + ⟨wB k2, wB k3⟩⟩
  rw [add_comm, zero_add]

/-- The bit word: `(x >> v) & 1` is `1` or `0` with bit `v` of `x`. -/
theorem bit_word {x v : ℕ} (hx : x < 2 ^ 64) (hv : v < 64) :
    XOp.and.eval (XOp.shr.eval (toWord x) (toWord v)) 1 = toWord (if x.testBit v then 1 else 0) := by
  rw [shr_toWord hx hv, and_one_toWord (lt_of_le_of_lt (Nat.div_le_self _ _) hx), bit_eq]

/-- The bit block: `eBit := bit_v x`, `eAd += 8`, `v += 1`. -/
theorem bitPs_sem (I : Array Word) (s : St) (hM : Inv s.M) {x v a : ℕ} (hx : x < 2 ^ 64)
    (hv : v < 64) (hX : rd s.M eX = toWord x) (hV : rd s.M eV = toWord v)
    (hA : rd s.M eAd = toWord a) :
    rd (semXIR I (.blk bitPs) s).M eBit = toWord (if x.testBit v then 1 else 0) ∧
      rd (semXIR I (.blk bitPs) s).M eAd = toWord (a + 8) ∧
      rd (semXIR I (.blk bitPs) s).M eV = toWord (v + 1) := by
  have hs := hM.1
  simp only [regs] at hs
  have h1 : rd s.M cOne = 1 := hM.2 0 (by decide)
  simp only [semXIR, runPrims, bitPs, List.foldl, Prim.run]
  refine ⟨?_, ?_, ?_⟩ <;>
  simp (disch := first | decide | (simp only [size_set, eBit, eK, eAd, eV]; omega)) only
    [rd_set_self, rd_set_ne]
  · rw [hX, hV, h1, bit_word hx hv]
  · rw [hA, show (8 : Word) = toWord 8 from rfl, add_toWord]
  · rw [hV, h1, add_one_toWord]

theorem bitPs_frame (I : Array Word) (s : St) : ∀ i, i ≠ eBit → i ≠ eK → i ≠ eAd → i ≠ eV →
    rd (semXIR I (.blk bitPs) s).M i = rd s.M i := fun i h1 h2 h3 h4 => by
  have e : semXIR I (.blk bitPs) s = ⟨runPrims bitPs s.M, s.o⟩ := rfl
  simp only [e]
  exact rd_runPrims_of_not_writes (by
    intro p hp
    simp only [bitPs, List.mem_cons, List.mem_nil_iff, or_false] at hp
    rcases hp with rfl | rfl | rfl | rfl | rfl <;> simp only [Prim.dst] <;>
      first | exact Ne.symm h1 | exact Ne.symm h2 | exact Ne.symm h3 | exact Ne.symm h4) _

theorem omPs_frame (I : Array Word) (s : St) : ∀ i, i ≠ kO → i ≠ kO + 1 → i ≠ kO + 2 → i ≠ kO + 3 →
    rd (semXIR I (.blk omPs) s).M i = rd s.M i := fun i h1 h2 h3 h4 =>
  rd_runPrims_of_not_writes (by
    simp [omPs, Prim.dst]; exact ⟨Ne.symm h1, Ne.symm h2, Ne.symm h3, Ne.symm h4⟩) _

/-- **One factor**: with `x` in `eX`, `v` in `eV` and `s_v` at `a = M[eAd]`,
`acc *= (bit_v x ? s_v : 1 − s_v)`; `v += 1`, `eAd += 8`; the heap and the loop registers are
kept. -/
theorem eqBody_sem (I : Array Word) (s : St) (hM : Inv s.M) {x v a : ℕ} {S : K}
    (hx : x < 2 ^ 64) (hv : v < 64) (ha : regs ≤ a) (ha2 : a + 11 < 2 ^ 64)
    (hX : rd s.M eX = toWord x) (hV : rd s.M eV = toWord v) (hA : rd s.M eAd = toWord a)
    (hS : rdK s.M a = S) :
    rdK (semXIR I eqBody s).M kA = rdK s.M kA * (if x.testBit v then S else 1 - S) ∧
    rd (semXIR I eqBody s).M eV = toWord (v + 1) ∧
    rd (semXIR I eqBody s).M eAd = toWord (a + 8) ∧
    (∀ i, (regs ≤ i ∨ i = eX ∨ i = eC1 ∨ i = eN1 ∨ i = eC2 ∨ i = eN2) →
      rd (semXIR I eqBody s).M i = rd s.M i) ∧
    Inv (semXIR I eqBody s).M := by
  have hs := hM.1
  simp only [regs] at hs ha
  -- s_v's first coordinate
  rw [eqBody, semXIR_seq]
  obtain ⟨u1, -, u3⟩ := ldF_sem I s hM (d := kS) (p := eAd) (p1 := eA1) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) hA (by simp only [regs]; omega) (by omega)
  have hM1 := inv_sem I (P := ldF kS eAd eA1) (by simp +decide only [ldF, WF, Prim.dst, kS, eA1,
    and_true]) hM
  have hH1 := hframe I (ldF kS eAd eA1) s (by simp +decide only [ldF, Lo, Prim.dst, regs, kS, eA1,
    and_true])
  generalize semXIR I (ldF kS eAd eA1) s = s1 at u1 u3 hM1 hH1
  -- the second address
  rw [semXIR_seq]
  have hs1 := hM1.1
  simp only [regs] at hs1
  have q2 : rd (semXIR I (.blk [.const eK 2, .op .add eA2 eAd eK]) s1).M eA2 = toWord (a + 2) := by
    simp only [semXIR, runPrims, List.foldl, Prim.run]
    simp (disch := first | decide | (simp only [size_set, eK, eA2]; omega)) only
      [rd_set_self, rd_set_ne]
    rw [u3 _ (by decide) (by decide) (by decide), hA, show (2 : Word) = toWord 2 from rfl,
      add_toWord]
  have f2 : ∀ i, i ≠ eK → i ≠ eA2 →
      rd (semXIR I (.blk [.const eK 2, .op .add eA2 eAd eK]) s1).M i = rd s1.M i :=
    fun i h1 h2 => rd_runPrims_of_not_writes (by simp [Prim.dst]; exact ⟨Ne.symm h1, Ne.symm h2⟩) _
  have hM2 := inv_sem I (P := .blk [.const eK 2, .op .add eA2 eAd eK]) (by simp +decide only [WF,
    Prim.dst, eK, eA2]) hM1
  generalize semXIR I (.blk [.const eK 2, .op .add eA2 eAd eK]) s1 = s2 at q2 f2 hM2
  -- the second coordinate
  rw [semXIR_seq]
  obtain ⟨v1, -, v3⟩ := ldF_sem I s2 hM2 (d := kS + 2) (p := eA2) (p1 := eA1) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide) q2 (by simp only [regs]; omega)
    (by omega)
  have hM3 := inv_sem I (P := ldF (kS + 2) eA2 eA1) (by simp +decide only [ldF, WF, Prim.dst, kS,
    eA1, and_true]) hM2
  generalize semXIR I (ldF (kS + 2) eA2 eA1) s2 = s3 at v1 v3 hM3
  have hK3 : rdK s3.M kS = S := by
    have hf : rdF s3.M kS = rdF s.M a := by
      rw [rdF_eq (v3 _ (by decide) (by decide) (by decide)) (v3 _ (by decide) (by decide) (by decide)),
        rdF_eq (f2 _ (by decide) (by decide)) (f2 _ (by decide) (by decide)), u1]
    have hg : rdF s3.M (kS + 2) = rdF s.M (a + 2) := by
      rw [v1, rdF_eq (f2 (a + 2) (by simp only [eK]; omega) (by simp only [eA2]; omega))
        (f2 (a + 2 + 1) (by simp only [eK]; omega) (by simp only [eA2]; omega)),
        rdF_eq (hH1 (a + 2) (by simp only [regs]; omega)) (hH1 (a + 2 + 1) (by simp only [regs]; omega))]
    rw [← hS]
    show (⟨rdF s3.M kS, rdF s3.M (kS + 2)⟩ : K) = ⟨rdF s.M a, rdF s.M (a + 2)⟩
    rw [hf, hg]
  have e3 : ∀ i, i ≠ kS + 2 → i ≠ kS + 3 → i ≠ eA1 → i ≠ eK → i ≠ eA2 → i ≠ kS → i ≠ kS + 1 →
      rd s3.M i = rd s.M i := fun i h1 h2 h3 h4 h5 h6 h7 => by
    rw [v3 i h1 h2 h3, f2 i h4 h5, u3 i h6 h7 h3]
  -- `1 − s_v`
  rw [semXIR_seq]
  have hs3 := hM3.1
  simp only [regs] at hs3
  have o4 : rdK (semXIR I (.blk omPs) s3).M kO = 1 - S := by
    rw [← hK3]
    simp only [rdK, rdF, rdB, semXIR, runPrims, omPs, List.foldl, Prim.run]
    simp (disch := first | decide | (simp only [size_set, kO, kS]; omega)) only
      [rd_set_self, rd_set_ne]
    rw [show rd s3.M cOne = 1 from hM3.2 0 (by decide)]
    exact rdK_one_sub _ _ _ _
  have f4 := omPs_frame I s3
  have hM4 := inv_sem I (P := .blk omPs) (by simp +decide only [omPs, WF, Prim.dst, kO]) hM3
  generalize semXIR I (.blk omPs) s3 = s4 at o4 f4 hM4
  -- the bit, the address, `v`
  rw [semXIR_seq]
  have hs4 := hM4.1
  simp only [regs] at hs4
  have g5 := bitPs_sem (a := a) I s4 hM4 hx hv
    (by rw [f4 _ (by decide) (by decide) (by decide) (by decide),
      e3 _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), hX])
    (by rw [f4 _ (by decide) (by decide) (by decide) (by decide),
      e3 _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), hV])
    (by rw [f4 _ (by decide) (by decide) (by decide) (by decide),
      e3 _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), hA])
  have f5 := bitPs_frame I s4
  have hM5 := inv_sem I (P := .blk bitPs) (by simp +decide only [bitPs, WF, Prim.dst, eBit, eK, eAd,
    eV]) hM4
  generalize semXIR I (.blk bitPs) s4 = s5 at g5 f5 hM5
  obtain ⟨b5, a5, v5⟩ := g5
  -- the product
  have hk5 : rdK s5.M kS = S := by
    rw [← hK3]
    exact rdK_eq fun j hj => by
      rw [f5 _ (by simp only [kS, eBit]; omega) (by simp only [kS, eK]; omega)
        (by simp only [kS, eAd]; omega) (by simp only [kS, eV]; omega),
        f4 _ (by simp only [kS, kO]; omega) (by simp only [kS, kO]; omega)
        (by simp only [kS, kO]; omega) (by simp only [kS, kO]; omega)]
  have ho5 : rdK s5.M kO = 1 - S := by
    rw [← o4]
    exact rdK_eq fun j hj => f5 _ (by simp only [kO, eBit]; omega) (by simp only [kO, eK]; omega)
      (by simp only [kO, eAd]; omega) (by simp only [kO, eV]; omega)
  have ha5 : rdK s5.M kA = rdK s.M kA := rdK_eq fun j hj => by
    rw [f5 _ (by simp only [kA, eBit]; omega) (by simp only [kA, eK]; omega)
      (by simp only [kA, eAd]; omega) (by simp only [kA, eV]; omega),
      f4 _ (by simp only [kA, kO]; omega) (by simp only [kA, kO]; omega)
      (by simp only [kA, kO]; omega) (by simp only [kA, kO]; omega),
      e3 _ (by simp only [kA, kS]; omega) (by simp only [kA, kS]; omega) (by simp only [kA, eA1]; omega)
        (by simp only [kA, eK]; omega) (by simp only [kA, eA2]; omega) (by simp only [kA, kS]; omega)
        (by simp only [kA, kS]; omega)]
  have hP : ∀ i, (regs ≤ i ∨ i = eX ∨ i = eC1 ∨ i = eN1 ∨ i = eC2 ∨ i = eN2) →
      rd s5.M i = rd s.M i := by
    intro i hi
    rcases hi with hi | hi
    · rw [f5 _ (by simp only [eBit, regs] at *; omega) (by simp only [eK, regs] at *; omega)
        (by simp only [eAd, regs] at *; omega) (by simp only [eV, regs] at *; omega),
        f4 _ (by simp only [kO, regs] at *; omega) (by simp only [kO, regs] at *; omega)
        (by simp only [kO, regs] at *; omega) (by simp only [kO, regs] at *; omega),
        e3 _ (by simp only [kS, regs] at *; omega) (by simp only [kS, regs] at *; omega)
        (by simp only [eA1, regs] at *; omega) (by simp only [eK, regs] at *; omega)
        (by simp only [eA2, regs] at *; omega) (by simp only [kS, regs] at *; omega)
        (by simp only [kS, regs] at *; omega)]
    · have : i ≠ eBit ∧ i ≠ eK ∧ i ≠ eAd ∧ i ≠ eV ∧ i ≠ kO ∧ i ≠ kO + 1 ∧ i ≠ kO + 2 ∧
          i ≠ kO + 3 ∧ i ≠ kS + 2 ∧ i ≠ kS + 3 ∧ i ≠ eA1 ∧ i ≠ eA2 ∧ i ≠ kS ∧ i ≠ kS + 1 := by
        rcases hi with rfl | rfl | rfl | rfl | rfl <;> decide
      obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14⟩ := this
      rw [f5 _ h1 h2 h3 h4, f4 _ h5 h6 h7 h8, e3 _ h9 h10 h11 h2 h12 h13 h14]
  have wk1 := wf_mulK kA kA kS (by decide)
  have wk2 := wf_mulK kA kA kO (by decide)
  have nwk : ∀ i, (regs ≤ i ∨ i = eX ∨ i = eC1 ∨ i = eN1 ∨ i = eC2 ∨ i = eN2 ∨ i = eV ∨
      i = eAd) → ∀ b, (b = kS ∨ b = kO) → rd (semXIR I (mulK kA kA b) s5).M i = rd s5.M i := by
    intro i hi b hb
    rcases hi with hi | hi
    · exact hframe I (mulK kA kA b) s5 (lo_mulK (by decide)) i hi
    · have h31 : 31 ≤ i ∧ i ≠ kA ∧ i ≠ kA + 1 ∧ i ≠ kA + 2 ∧ i ≠ kA + 3 ∧ i < regs := by
        rcases hi with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
      exact frame I _ s5 (wf_mulK kA kA b (by decide)) hM5 i h31.2.2.2.2.2
        (nw_mulK h31.1 h31.2.1 h31.2.2.1 h31.2.2.2.1 h31.2.2.2.2.1)
  have hb0 : (toWord (if x.testBit v then 1 else 0) = 0) ↔ ¬ x.testBit v := by
    by_cases h : x.testBit v
    · rw [if_pos h]; exact ⟨fun e => absurd e (by decide), fun h' => absurd h h'⟩
    · rw [if_neg h]; exact ⟨fun _ => h, fun _ => rfl⟩
  simp only [semXIR]
  rw [b5]
  by_cases hbit : x.testBit v
  · rw [if_neg (by rw [hb0]; exact not_not_intro hbit), if_pos hbit]
    refine ⟨?_, (nwk _ (.inr (.inr (.inr (.inr (.inr (.inr (.inl rfl))))))) _ (.inl rfl)).trans v5,
      (nwk _ (.inr (.inr (.inr (.inr (.inr (.inr (.inr rfl))))))) _ (.inl rfl)).trans a5,
      fun i hi => (nwk i (hi.imp_right (Or.imp_right (Or.imp_right (Or.imp_right
        (Or.imp_right Or.inl))))) _ (.inl rfl)).trans (hP i hi), inv_sem I wk1 hM5⟩
    rw [mulK_sem hM5 (by decide) (by decide) (by decide) (by decide), ha5, hk5]
  · rw [if_pos (by rw [hb0]; exact hbit), if_neg hbit]
    refine ⟨?_, (nwk _ (.inr (.inr (.inr (.inr (.inr (.inr (.inl rfl))))))) _ (.inr rfl)).trans v5,
      (nwk _ (.inr (.inr (.inr (.inr (.inr (.inr (.inr rfl))))))) _ (.inr rfl)).trans a5,
      fun i hi => (nwk i (hi.imp_right (Or.imp_right (Or.imp_right (Or.imp_right
        (Or.imp_right Or.inl))))) _ (.inr rfl)).trans (hP i hi), inv_sem I wk2 hM5⟩
    rw [mulK_sem hM5 (by decide) (by decide) (by decide) (by decide), ha5, ho5]

/-! ## One entry, the table -/

theorem entPre_sem (I : Array Word) (s : St) (hM : Inv s.M) (ℓ cb : ℕ) :
    rdK (semXIR I (.blk (entPre ℓ cb)) s).M kA = 1 ∧
    rd (semXIR I (.blk (entPre ℓ cb)) s).M eV = toWord 0 ∧
    rd (semXIR I (.blk (entPre ℓ cb)) s).M eAd = toWord (cb + 8 * 0) ∧
    rd (semXIR I (.blk (entPre ℓ cb)) s).M eN2 = toWord ℓ ∧
    (∀ i, i ≠ kA → i ≠ kA + 1 → i ≠ kA + 2 → i ≠ kA + 3 → i ≠ eV → i ≠ eAd → i ≠ eN2 →
      rd (semXIR I (.blk (entPre ℓ cb)) s).M i = rd s.M i) ∧
    Inv (semXIR I (.blk (entPre ℓ cb)) s).M := by
  have hs := hM.1
  simp only [regs] at hs
  have e : semXIR I (.blk (entPre ℓ cb)) s = ⟨runPrims (entPre ℓ cb) s.M, s.o⟩ := rfl
  simp only [e]
  refine ⟨?_, ?_, ?_, ?_, fun i h1 h2 h3 h4 h5 h6 h7 => rd_runPrims_of_not_writes (by
    intro p hp
    simp only [entPre, List.mem_cons, List.mem_nil_iff, or_false] at hp
    rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp only [Prim.dst] <;>
      first | exact Ne.symm h1 | exact Ne.symm h2 | exact Ne.symm h3 | exact Ne.symm h4 |
        exact Ne.symm h5 | exact Ne.symm h6 | exact Ne.symm h7) _,
    inv_runPrims (by simp [entPre, Prim.dst, kA, eV, eAd, eN2]) hM⟩
  · simp only [rdK, rdF, rdB, entPre, runPrims, List.foldl, Prim.run]
    simp (disch := first | decide | (simp only [size_set, kA, eV, eAd, eN2]; omega)) only
      [rd_set_self, rd_set_ne]
    rfl
  all_goals simp only [entPre, runPrims, List.foldl, Prim.run]
  all_goals simp (disch := first | decide | (simp only [size_set, kA, eV, eAd, eN2]; omega)) only
      [rd_set_self, rd_set_ne]
  · rfl
  · rfl

theorem entAd_sem (I : Array Word) (s : St) (hM : Inv s.M) {x eb : ℕ}
    (hX : rd s.M eX = toWord x) :
    rd (semXIR I (.blk (entAd eb)) s).M eAd = toWord (eb + 4 * x) ∧
    rd (semXIR I (.blk (entAd eb)) s).M eA2 = toWord (eb + 4 * x + 2) ∧
    (∀ i, i ≠ eAd → i ≠ eK → i ≠ eA2 → rd (semXIR I (.blk (entAd eb)) s).M i = rd s.M i) ∧
    Inv (semXIR I (.blk (entAd eb)) s).M := by
  have hs := hM.1
  simp only [regs] at hs
  have e : semXIR I (.blk (entAd eb)) s = ⟨runPrims (entAd eb) s.M, s.o⟩ := rfl
  simp only [e]
  refine ⟨?_, ?_, fun i h1 h2 h3 => rd_runPrims_of_not_writes (by
    intro p hp
    simp only [entAd, List.mem_cons, List.mem_nil_iff, or_false] at hp
    rcases hp with rfl | rfl | rfl | rfl | rfl | rfl <;> simp only [Prim.dst] <;>
      first | exact Ne.symm h1 | exact Ne.symm h2 | exact Ne.symm h3) _,
    inv_runPrims (by simp [entAd, Prim.dst, eAd, eK, eA2]) hM⟩
  all_goals simp only [entAd, runPrims, List.foldl, Prim.run]
  all_goals simp (disch := first | decide | (simp only [size_set, eAd, eK, eA2]; omega)) only
      [rd_set_self, rd_set_ne]
  · rw [hX, add_toWord, add_toWord, add_toWord]; congr 1; ring
  · rw [hX, add_toWord, add_toWord, add_toWord, show (2 : Word) = toWord 2 from rfl, add_toWord]
    congr 1; ring

/-- **One entry**: with `x` in `eX` and the challenges `S v` at `cb + 8v`, `eqEnt` stores
`eqBits S ℓ x` at `eb + 4x`; `x += 1`; the heap outside the entry and the entry loop's
registers are kept. -/
theorem eqEnt_sem (I : Array Word) (s : St) (hM : Inv s.M) {ℓ cb eb x : ℕ} {S : ℕ → K}
    (hℓ : ℓ < 64) (hx : x < 2 ^ 64) (hcb : regs ≤ cb) (hcb2 : cb + 8 * ℓ + 11 < 2 ^ 64)
    (heb : regs ≤ eb) (heb2 : eb + 4 * x + 4 < 2 ^ 64) (hsz : eb + 4 * x + 4 ≤ s.M.size)
    (hX : rd s.M eX = toWord x) (hS : ∀ v < ℓ, rdK s.M (cb + 8 * v) = S v) :
    rdK (semXIR I (eqEnt ℓ cb eb) s).M (eb + 4 * x) = eqBits S ℓ x ∧
    rd (semXIR I (eqEnt ℓ cb eb) s).M eX = toWord (x + 1) ∧
    (∀ i, (regs ≤ i ∧ (i < eb + 4 * x ∨ eb + 4 * x + 4 ≤ i) ∨ i = eC1 ∨ i = eN1) →
      rd (semXIR I (eqEnt ℓ cb eb) s).M i = rd s.M i) ∧
    Inv (semXIR I (eqEnt ℓ cb eb) s).M := by
  have hs := hM.1
  simp only [regs] at hs hcb heb
  obtain ⟨p1, p2, p3, p4, p5, hM1⟩ := entPre_sem I s hM ℓ cb
  have z1 := size_sem I (.blk (entPre ℓ cb)) s
  rw [eqEnt, semXIR_seq]
  generalize semXIR I (.blk (entPre ℓ cb)) s = s1 at p1 p2 p3 p4 p5 hM1 z1
  have hR1 : ∀ i, (regs ≤ i ∨ i = eX ∨ i = eC1 ∨ i = eN1) → rd s1.M i = rd s.M i := by
    intro i hi
    have : i ≠ kA ∧ i ≠ kA + 1 ∧ i ≠ kA + 2 ∧ i ≠ kA + 3 ∧ i ≠ eV ∧ i ≠ eAd ∧ i ≠ eN2 := by
      rcases hi with hi | rfl | rfl | rfl
      · simp only [regs, kA, eV, eAd, eN2] at *; omega
      all_goals decide
    exact p5 i this.1 this.2.1 this.2.2.1 this.2.2.2.1 this.2.2.2.2.1 this.2.2.2.2.2.1
      this.2.2.2.2.2.2
  -- the factor loop
  rw [semXIR_seq]
  let Q : ℕ → St → Prop := fun j s' => Inv s'.M ∧ s'.M.size = s.M.size ∧
    rdK s'.M kA = ∏ v ∈ range j, (if x.testBit v then S v else 1 - S v) ∧
    rd s'.M eV = toWord j ∧ rd s'.M eAd = toWord (cb + 8 * j) ∧
    ∀ i, (regs ≤ i ∨ i = eX ∨ i = eC1 ∨ i = eN1) → rd s'.M i = rd s.M i
  have hE : ∀ i, i ≠ eC2 → i ≠ cTmp → rd (entryK eC2 eN2 (toWord ℓ) s1.M) i = rd s1.M i :=
    fun i h1 h2 => entryK_frame _ (Ne.symm h1) (Ne.symm h2)
  have q0 : Q 0 ⟨entryK eC2 eN2 (toWord ℓ) s1.M, s1.o⟩ := by
    refine ⟨inv_entryK hM1 (by decide), by simp only [size_entryK, z1], ?_, ?_, ?_,
      fun i hi => ?_⟩
    · dsimp only
      rw [prod_range_zero, ← p1]
      exact rdK_eq fun j hj => hE _ (by simp only [kA, eC2]; omega) (by simp only [kA, cTmp]; omega)
    · dsimp only; rw [hE _ (by decide) (by decide), p2]
    · dsimp only; rw [hE _ (by decide) (by decide), p3]
    · dsimp only
      have : i ≠ eC2 ∧ i ≠ cTmp := by
        rcases hi with hi | rfl | rfl | rfl
        · simp only [regs, eC2, cTmp] at *; omega
        all_goals decide
      rw [hE _ this.1 this.2, hR1 i hi]
  have qstep : ∀ j s', j < ℓ → Q j s' → Q (j + 1) (decS eC2 (semXIR I eqBody s')) := by
    rintro j s' hj ⟨i1, i2, i3, i4, i5, i6⟩
    have hS' : rdK s'.M (cb + 8 * j) = S j := by
      rw [← hS j hj]
      exact rdK_eq fun m hm => i6 _ (.inl (by simp only [regs]; omega))
    obtain ⟨e1, e2, e3, e4, e5⟩ := eqBody_sem I s' i1 (x := x) hx (by omega)
      (by simp only [regs]; omega) (by omega) ((i6 _ (.inr (.inl rfl))).trans hX) i4 i5 hS'
    have hd : ∀ i, i ≠ eC2 → rd (decS eC2 (semXIR I eqBody s')).M i =
        rd (semXIR I eqBody s').M i := fun i h => rd_decS (Ne.symm h) _
    refine ⟨inv_decS e5 (by decide), by rw [size_decS, size_sem, i2], ?_, ?_, ?_, fun i hi => ?_⟩
    · rw [rdK_eq (M' := (decS eC2 (semXIR I eqBody s')).M) (M := (semXIR I eqBody s').M)
        fun m hm => hd _ (by simp only [kA, eC2]; omega), e1, i3, prod_range_succ]
    · rw [hd _ (by decide), e2]
    · rw [hd _ (by decide), e3, Nat.mul_succ, Nat.add_assoc]
    · have : i ≠ eC2 := by
        rcases hi with hi | rfl | rfl | rfl
        · simp only [regs, eC2] at *; omega
        all_goals decide
      rw [hd _ this, e4 i (hi.imp_right fun h => h.imp_right fun h => h.imp_right Or.inl), i6 i hi]
  have hq := loopK_run I eqBody Q s1 hM1 (by decide) (by decide) (by decide) p4 (by omega) q0 qstep
  generalize semXIR I (.loopK eC2 eN2 (toWord ℓ) eqBody) s1 = s2 at hq
  obtain ⟨j1, j2, j3, -, -, j6⟩ := hq
  have hX2 : rd s2.M eX = toWord x := (j6 _ (.inr (.inl rfl))).trans hX
  -- the address, the stores
  rw [semXIR_seq]
  obtain ⟨a1, a2, a3, hM3⟩ := entAd_sem (eb := eb) I s2 j1 hX2
  have z3 := size_sem I (.blk (entAd eb)) s2
  generalize semXIR I (.blk (entAd eb)) s2 = s3 at a1 a2 a3 hM3 z3
  rw [j2] at z3
  have hk3 : rdK s3.M kA = eqBits S ℓ x := by
    rw [eqBits, bitSel, ← j3]
    exact rdK_eq fun m hm => a3 _ (by simp only [kA, eAd]; omega) (by simp only [kA, eK]; omega)
      (by simp only [kA, eA2]; omega)
  have hs3 := hM3.1
  simp only [regs] at hs3
  obtain ⟨c1, c2, hM4⟩ := stF_sem I s3 hM3 (p := eAd) (p1 := eA1) (v := kA) (x := eb + 4 * x)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) a1 (by simp only [regs]; omega) (by omega) (by omega)
  have z4 := size_sem I (stF eAd eA1 kA) s3
  rw [semXIR_seq]
  generalize semXIR I (stF eAd eA1 kA) s3 = s4 at c1 c2 hM4 z4
  have a24 : rd s4.M eA2 = toWord (eb + 4 * x + 2) :=
    (c2 _ (by simp only [eA2]; omega) (by simp only [eA2]; omega) (by decide) (by decide)).trans a2
  have k24 : rdF s4.M (kA + 2) = rdF s3.M (kA + 2) :=
    rdF_eq (c2 _ (by simp only [kA]; omega) (by simp only [kA]; omega) (by decide) (by decide))
      (c2 _ (by simp only [kA]; omega) (by simp only [kA]; omega) (by decide) (by decide))
  obtain ⟨d1, d2, hM5⟩ := stF_sem I s4 hM4 (p := eA2) (p1 := eA1) (v := kA + 2)
    (x := eb + 4 * x + 2) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) a24 (by simp only [regs]; omega) (by omega) (by omega)
  rw [semXIR_seq]
  generalize semXIR I (stF eA2 eA1 (kA + 2)) s4 = s5 at d1 d2 hM5
  have x5 : rd s5.M eX = toWord x := by
    rw [d2 _ (by simp only [eX]; omega) (by simp only [eX]; omega) (by decide) (by decide),
      c2 _ (by simp only [eX]; omega) (by simp only [eX]; omega) (by decide) (by decide),
      a3 _ (by decide) (by decide) (by decide), hX2]
  have e6 : semXIR I (.blk [.op .add eX eX cOne]) s5 =
      ⟨runPrims [.op .add eX eX cOne] s5.M, s5.o⟩ := rfl
  rw [e6]
  obtain ⟨g1, g2⟩ := incr_sem s5.M hM5 (r := eX) (by decide) (by decide) x5
  refine ⟨?_, g1, fun i hi => ?_, inv_runPrims (by simp [Prim.dst, eX]) hM5⟩
  · rw [← hk3]
    show (⟨rdF (runPrims _ s5.M) (eb + 4 * x), rdF (runPrims _ s5.M) (eb + 4 * x + 2)⟩ : K) =
      ⟨rdF s3.M kA, rdF s3.M (kA + 2)⟩
    rw [rdF_eq (g2 _ (by simp only [eX]; omega)) (g2 _ (by simp only [eX]; omega)),
      rdF_eq (g2 _ (by simp only [eX]; omega)) (g2 _ (by simp only [eX]; omega)), d1, k24,
      rdF_eq (d2 _ (by omega) (by omega) (by simp only [eA1]; omega) (by simp only [cTmp]; omega))
        (d2 _ (by omega) (by omega) (by simp only [eA1]; omega) (by simp only [cTmp]; omega)), c1]
  · have hne : i ≠ eX ∧ i ≠ eb + 4 * x + 2 ∧ i ≠ eb + 4 * x + 2 + 1 ∧ i ≠ eA1 ∧ i ≠ cTmp ∧
        i ≠ eb + 4 * x ∧ i ≠ eb + 4 * x + 1 ∧ i ≠ eAd ∧ i ≠ eK ∧ i ≠ eA2 := by
      rcases hi with ⟨h1, h2⟩ | rfl | rfl
      · simp only [regs, eX, eA1, cTmp, eAd, eK, eA2] at *; omega
      · simp only [eX, eA1, cTmp, eAd, eK, eA2, eC1]; omega
      · simp only [eX, eA1, cTmp, eAd, eK, eA2, eN1]; omega
    obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10⟩ := hne
    rw [g2 _ h1, d2 _ h2 h3 h4 h5, c2 _ h6 h7 h4 h5, a3 _ h8 h9 h10,
      j6 i (hi.imp (fun h => h.1) fun h => .inr h)]

/-- **The `eq` table** on the machine: from the challenges `S v` (K, `rdK`) at `cb + 8v`,
`v < ℓ`, `eqtIR ℓ cb eb` leaves `eqBits S ℓ x` at `eb + 4x` for every `x < 2^ℓ`, and keeps the
heap outside `[eb, eb + 4·2^ℓ)`. -/
theorem eqtIR_sem (I : Array Word) (s : St) (hM : Inv s.M) {ℓ cb eb : ℕ} {S : ℕ → K}
    (hℓ : ℓ < 64) (hcb : regs ≤ cb) (hcb2 : cb + 8 * ℓ + 11 < 2 ^ 64) (heb : regs ≤ eb)
    (heb2 : eb + 4 * 2 ^ ℓ < 2 ^ 64) (hsz : eb + 4 * 2 ^ ℓ ≤ s.M.size)
    (hdisj : cb + 8 * ℓ + 4 ≤ eb ∨ eb + 4 * 2 ^ ℓ ≤ cb)
    (hS : ∀ v < ℓ, rdK s.M (cb + 8 * v) = S v) :
    (∀ x < 2 ^ ℓ, rdK (semXIR I (eqtIR ℓ cb eb) s).M (eb + 4 * x) = eqBits S ℓ x) ∧
    (∀ i, regs ≤ i → (i < eb ∨ eb + 4 * 2 ^ ℓ ≤ i) → rd (semXIR I (eqtIR ℓ cb eb) s).M i = rd s.M i) ∧
    Inv (semXIR I (eqtIR ℓ cb eb) s).M := by
  have hs := hM.1
  simp only [regs] at hs hcb heb
  have hP : 2 ^ ℓ < 2 ^ 64 := Nat.pow_lt_pow_right (by norm_num) (by omega)
  have e0 : semXIR I (.blk [.const eX 0, .const eN1 (toWord (2 ^ ℓ))]) s =
      ⟨runPrims [.const eX 0, .const eN1 (toWord (2 ^ ℓ))] s.M, s.o⟩ := rfl
  obtain ⟨r1, r2, r3, hM0⟩ := pre2_sem s.M hM (r := eX) (n := eN1) 0 (toWord (2 ^ ℓ)) (by decide)
    (by decide) (by decide) (by decide) (by decide)
  rw [eqtIR, semXIR_seq, e0]
  generalize hM0e : runPrims [.const eX 0, .const eN1 (toWord (2 ^ ℓ))] s.M = M0 at r1 r2 r3 hM0
  have z0 : M0.size = s.M.size := by rw [← hM0e]; exact size_runPrims _ _
  let P : ℕ → St → Prop := fun j s' => Inv s'.M ∧ s'.M.size = s.M.size ∧ rd s'.M eX = toWord j ∧
    (∀ x < j, rdK s'.M (eb + 4 * x) = eqBits S ℓ x) ∧
    ∀ i, regs ≤ i → (i < eb ∨ eb + 4 * j ≤ i) → rd s'.M i = rd s.M i
  have hE : ∀ i, i ≠ eC1 → i ≠ cTmp → rd (entryK eC1 eN1 (toWord (2 ^ ℓ)) M0) i = rd M0 i :=
    fun i h1 h2 => entryK_frame _ (Ne.symm h1) (Ne.symm h2)
  have p0 : P 0 ⟨entryK eC1 eN1 (toWord (2 ^ ℓ)) M0, s.o⟩ := by
    refine ⟨inv_entryK hM0 (by decide), by simp only [size_entryK, z0], ?_,
      fun x hx => absurd hx (Nat.not_lt_zero _), fun i hi _ => ?_⟩
    · dsimp only; rw [hE _ (by decide) (by decide), r1, toWord_zero']
    · dsimp only
      rw [hE _ (by simp only [eC1, regs] at *; omega) (by simp only [cTmp, regs] at *; omega),
        r3 _ (by simp only [eX, regs] at *; omega) (by simp only [eN1, regs] at *; omega)]
  have step : ∀ j s', j < 2 ^ ℓ → P j s' → P (j + 1) (decS eC1 (semXIR I (eqEnt ℓ cb eb) s')) := by
    rintro j s' hj ⟨i1, i2, i3, i4, i5⟩
    have hS' : ∀ v < ℓ, rdK s'.M (cb + 8 * v) = S v := fun v hv => by
      rw [← hS v hv]
      exact rdK_eq fun m hm => i5 _ (by simp only [regs]; omega) (by omega)
    have hj4 : eb + 4 * j + 4 ≤ eb + 4 * 2 ^ ℓ := by omega
    obtain ⟨e1, e2, e3, e4⟩ := eqEnt_sem I s' i1 (ℓ := ℓ) (cb := cb) (eb := eb) (x := j) (S := S) hℓ
      (by omega) (by simp only [regs]; omega) hcb2 (by simp only [regs]; omega) (by omega)
      (by rw [i2]; omega) i3 hS'
    have hd : ∀ i, i ≠ eC1 → rd (decS eC1 (semXIR I (eqEnt ℓ cb eb) s')).M i =
        rd (semXIR I (eqEnt ℓ cb eb) s').M i := fun i h => rd_decS (Ne.symm h) _
    refine ⟨inv_decS e4 (by decide), by rw [size_decS, size_sem, i2], by rw [hd _ (by decide), e2],
      fun x hx => ?_, fun i hi hi2 => ?_⟩
    · rw [rdK_eq (M' := (decS eC1 (semXIR I (eqEnt ℓ cb eb) s')).M)
        (M := (semXIR I (eqEnt ℓ cb eb) s').M) fun m hm => hd _ (by simp only [eC1, regs] at *; omega)]
      rcases Nat.lt_succ_iff_lt_or_eq.mp hx with h | rfl
      · rw [← i4 x h]
        exact rdK_eq fun m hm => e3 _ (.inl ⟨by simp only [regs]; omega, by omega⟩)
      · exact e1
    · simp only [regs] at hi
      rw [hd _ (by simp only [eC1]; omega), e3 _ (.inl ⟨by simp only [regs]; omega, by omega⟩),
        i5 i (by simp only [regs]; omega) (by omega)]
  have := loopK_run I (eqEnt ℓ cb eb) P ⟨M0, s.o⟩ hM0 (by decide) (by decide) (by decide) r2 hP
    p0 step
  exact ⟨this.2.2.2.1, fun i hi hi2 => this.2.2.2.2 i hi hi2, this.1⟩


/-! ## The challenges from the chain's answers -/

/-- **P1.i's challenges on the machine**: if the chain replay left the answer of every FS position
`p = phStart (26 + 5i) + 2v + 1` (`v < ℓ`) at `ansB + 4p` (`chain_dec`, with `fmAns = ansAt`),
the K element at `ansB + 4·(phStart (26 + 5i) + 1) + 8v` is `sAt es i v`: the input layout of
`eqtIR`. The positions stay symbolic (`phStart`). -/
theorem sAt_words {M : Mem} {es : Log} {i ℓ : ℕ}
    (h : ∀ v < ℓ, ∀ m < 4, rd M (ansB + 4 * (FR.Snd.phStart (26 + 5 * i) + 2 * v + 1) + m) =
      (packBytes (FR.Snd.ansAt es (FR.Snd.phStart (26 + 5 * i) + 2 * v + 1)).toList).getD m 0) :
    ∀ v < ℓ, rdK M (ansB + 4 * (FR.Snd.phStart (26 + 5 * i) + 1) + 8 * v) = FR.Snd.sAt es i v := by
  intro v hv
  rw [FR.Snd.sAt, FR.Snd.kAt]
  refine rdK_of_words fun m hm => ?_
  rw [← h v hv m hm]
  congr 1
  ring

/-! ## Controls -/

/-- **Bit order control**: `eqBits` weighs bit `v` of the row by `s_v`, so row `1` of a
two-variable table is `s₀ (1 − s₁)` and row `2` is `(1 − s₀) s₁`; the table is not symmetric
in the challenges. -/
theorem eqBits_ctl (S : ℕ → K) :
    eqBits S 2 1 = S 0 * (1 - S 1) ∧ eqBits S 2 2 = (1 - S 0) * S 1 := by
  have b1 : Nat.testBit 1 0 = true := rfl
  have b2 : Nat.testBit 1 1 = false := rfl
  have b3 : Nat.testBit 2 0 = false := rfl
  have b4 : Nat.testBit 2 1 = true := rfl
  simp only [eqBits, bitSel, prod_range_succ, prod_range_zero, one_mul, b1, b2, b3, b4]
  exact ⟨rfl, rfl⟩

end FR.X
