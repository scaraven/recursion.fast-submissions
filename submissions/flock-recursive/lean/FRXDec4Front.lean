-- New for `flock-recursive` (BLUEPRINT revision 4.2, §6.2 step 4; stage S-H4, pass 2, item 2′).
import FRXDec4Level
import FRXDecLv

/-!
# The front half of one level's decode at revision 4.1's kinds, on a parametric memory map

`decFront4IR msg ℓ n R cs cb cbS tb fb eb xb yb` is 3.x's front half
(`eqtIR ; msg ; fwdIR ×2 ; flagIR`) with every base a parameter: the `eq` table of P1.i's `ℓ`
challenges (read at `cbS`) to `eb`, the next message's coordinate rows (`msg`) to `xb`, `yb`,
`Enc` of each, the agreement flags to `fb`.

**The memory map** (`FrontLay4`): the basis table at `tb` (800 words), the flags at `fb` (`n`), the
`eq` table at `eb` (256), `X` at `xb` (`2n`), `Y` at `yb` (`2n`), in this order; the word's column
store at `cb ≥ yb + 2n`; the challenges at `cbS` below `eb` (outside the flags).

**`decFront4_sem`** (3.x's `decFront_sem` over `CKind`): the flag at `fb + j` is nonzero iff
`j ∈ A_c` (`flagV_consSet4`). **`MsgOk4`** is 3.x's `MsgOk` at the map's `eb`, `xb`, `yb`.
-/

namespace FR.X

open RecursionFast FR Finset

-- G2: `entryK`/`storeM`/`runPrims` are never unfolded while unifying states (elaboration time).
attribute [local irreducible] entryK storeM runPrims

/-- **The agreement flag marks `A_c`** at a 4.1 kind (3.x's `flagV_consSet`). -/
theorem flagV_consSet4 {M : Mem} {κ : Snd.CKind} {L es : Log} {i cs cb eb xb yb : ℕ}
    (hW : ∀ j (hj : j < 2 ^ (Snd.CKind.lv κ i).logN) (r : Fin (Snd.CKind.lv κ i).rows),
      rdF M (cb + cs * j + 2 * r) = Snd.T4.wordOf κ L es i r ⟨j, hj⟩)
    (hE : ∀ r < (Snd.CKind.lv κ i).rows,
      rdK M (eb + 4 * r) = eqBits (Snd.T4.sAt es i) (Snd.CKind.lv κ i).ell r)
    (hX : ∀ j < 2 ^ (Snd.CKind.lv κ i).logN,
      rdF M (xb + 2 * j) = encF (Snd.T4.mLog κ i) (fun x => (Snd.T4.nextMsg κ L es i x).f₀) j)
    (hY : ∀ j < 2 ^ (Snd.CKind.lv κ i).logN,
      rdF M (yb + 2 * j) = encF (Snd.T4.mLog κ i) (fun x => (Snd.T4.nextMsg κ L es i x).f₁) j) :
    ∀ j < 2 ^ (Snd.CKind.lv κ i).logN,
      (j ∈ consN4 κ L es i ↔ flagV M (Snd.CKind.lv κ i).rows cs cb eb xb yb j ≠ 0) := by
  intro j hj
  rw [flagV, bW_dec_ne_zero, mem_consN4]
  have s0 : ∑ r ∈ range (Snd.CKind.lv κ i).rows, rdF M (cb + cs * j + 2 * r) * rdF M (eb + 4 * r) =
      ∑ r : Fin (Snd.CKind.lv κ i).rows,
        Snd.T4.wordOf κ L es i r ⟨j, hj⟩ * (eqBits (Snd.T4.sAt es i) (Snd.CKind.lv κ i).ell r).f₀ := by
    rw [← Fin.sum_univ_eq_sum_range]
    refine sum_congr rfl fun r _ => ?_
    rw [hW j hj r, ← hE r r.2]
    rfl
  have s1 : ∑ r ∈ range (Snd.CKind.lv κ i).rows, rdF M (cb + cs * j + 2 * r) * rdF M (eb + 4 * r + 2) =
      ∑ r : Fin (Snd.CKind.lv κ i).rows,
        Snd.T4.wordOf κ L es i r ⟨j, hj⟩ * (eqBits (Snd.T4.sAt es i) (Snd.CKind.lv κ i).ell r).f₁ := by
    rw [← Fin.sum_univ_eq_sum_range]
    refine sum_congr rfl fun r _ => ?_
    rw [hW j hj r, ← hE r r.2]
    rfl
  rw [s0, s1, hX j hj, hY j hj]
  constructor
  · rintro ⟨h, hm⟩; exact (mem_consSet4_iff κ L es i _).1 hm
  · intro h; exact ⟨hj, (mem_consSet4_iff κ L es i ⟨j, hj⟩).2 h⟩

/-- **The front half's memory map** (`n` positions, `ℓ` challenges at `cbS`). -/
def FrontLay4 (n ℓ tb fb eb xb yb cbS : ℕ) : Prop :=
  regs ≤ tb ∧ tb + 800 ≤ fb ∧ fb + n ≤ eb ∧ eb + 256 ≤ xb ∧ xb + 2 * n ≤ yb ∧
    yb + 2 * n + 2 < 2 ^ 64 ∧ regs ≤ cbS ∧ cbS + 8 * ℓ + 4 ≤ eb ∧ (cbS + 8 * ℓ + 4 ≤ fb ∨ fb + n ≤ cbS)

/-- **The front half** at a 4.1 level, on the map `tb fb eb xb yb`. -/
def decFront4IR (msg : XIR) (ℓ n R cs cb cbS tb fb eb xb yb : ℕ) : XIR :=
  .seq (eqtIR ℓ cbS eb) (.seq msg (.seq (setA xb) (.seq (fwdIR n tb) (.seq (setA yb)
    (.seq (fwdIR n tb) (flagIR (2 ^ n) R cs cb eb xb yb fb))))))

/-- What the message step owes (3.x's `MsgOk` at the map's `eb`, `xb`, `yb`, `X`/`Y` of `2^n`
entries). -/
def MsgOk4 (I : Array Word) (msg : XIR) (s : St) (eb xb yb n m : ℕ) (g : ℕ → K) : Prop :=
  ∀ s' : St, Inv s'.M → s'.M.size = s.M.size →
    (∀ y, regs ≤ y → (y < eb ∨ eb + 256 ≤ y) → rd s'.M y = rd s.M y) →
    (∀ j < 2 ^ n, rdF (semXIR I msg s').M (xb + 2 * j) = (if j < 2 ^ m then (g j).f₀ else 0) ∧
      rdF (semXIR I msg s').M (yb + 2 * j) = (if j < 2 ^ m then (g j).f₁ else 0)) ∧
    (∀ y, regs ≤ y → (y < xb ∨ yb + 2 * 2 ^ n ≤ y) → rd (semXIR I msg s').M y = rd s'.M y) ∧
    Inv (semXIR I msg s').M

/-- The level parameters the front half needs (every kind, every level). -/
theorem lv4_front (κ : Snd.CKind) {i : ℕ} (hi : i < 5) :
    (Snd.CKind.lv κ i).ell ≤ 6 ∧ 1 ≤ (Snd.CKind.lv κ i).logN ∧ (Snd.CKind.lv κ i).logN ≤ 20 ∧
      Snd.T4.mLog κ i ≤ (Snd.CKind.lv κ i).logN := by
  rcases κ with (_|_|_) | (_|_|_) <;> interval_cases i <;> decide

/-- **The front half marks `A_c`** at a 4.1 kind (3.x's `decFront_sem` on a parametric map). -/
theorem decFront4_sem (I : Array Word) (s : St) (hM : Inv s.M) {κ : Snd.CKind} {L es : Log}
    {i cs cb cbS tb fb eb xb yb : ℕ} {msg : XIR} (hi : i < 5)
    (hL : FrontLay4 (2 ^ (Snd.CKind.lv κ i).logN) (Snd.CKind.lv κ i).ell tb fb eb xb yb cbS)
    (hsz : yb + 2 * 2 ^ (Snd.CKind.lv κ i).logN ≤ s.M.size)
    (hcs : 2 * (Snd.CKind.lv κ i).rows ≤ cs) (hcb : yb + 2 * 2 ^ (Snd.CKind.lv κ i).logN ≤ cb)
    (hcb2 : cb + cs * 2 ^ (Snd.CKind.lv κ i).logN + 2 < 2 ^ 64)
    (hT : ∀ v < 20, ∀ i < 20, rdF s.M (tb + 40 * v + 2 * i) = (wRow D logNMax v).getD i 0)
    (hW : ∀ j (hj : j < 2 ^ (Snd.CKind.lv κ i).logN) (r : Fin (Snd.CKind.lv κ i).rows),
      rdF s.M (cb + cs * j + 2 * r) = Snd.T4.wordOf κ L es i r ⟨j, hj⟩)
    (hS : ∀ v < (Snd.CKind.lv κ i).ell, rdK s.M (cbS + 8 * v) = Snd.T4.sAt es i v)
    (hmsg : MsgOk4 I msg (semXIR I (eqtIR (Snd.CKind.lv κ i).ell cbS eb) s) eb xb yb
      (Snd.CKind.lv κ i).logN (Snd.T4.mLog κ i) (Snd.T4.nextMsg κ L es i)) :
    (∀ j < 2 ^ (Snd.CKind.lv κ i).logN, (j ∈ consN4 κ L es i ↔
      rd (semXIR I (decFront4IR msg (Snd.CKind.lv κ i).ell (Snd.CKind.lv κ i).logN
        (Snd.CKind.lv κ i).rows cs cb cbS tb fb eb xb yb) s).M (fb + j) ≠ 0)) ∧
    (∀ y, regs ≤ y → (y < fb ∨ (fb + 2 ^ (Snd.CKind.lv κ i).logN ≤ y ∧ y < eb) ∨
        yb + 2 * 2 ^ (Snd.CKind.lv κ i).logN ≤ y) →
      rd (semXIR I (decFront4IR msg (Snd.CKind.lv κ i).ell (Snd.CKind.lv κ i).logN
        (Snd.CKind.lv κ i).rows cs cb cbS tb fb eb xb yb) s).M y = rd s.M y) ∧
    Inv (semXIR I (decFront4IR msg (Snd.CKind.lv κ i).ell (Snd.CKind.lv κ i).logN
        (Snd.CKind.lv κ i).rows cs cb cbS tb fb eb xb yb) s).M := by
  obtain ⟨htb, htf, hfe, hex, hxy, hy2, hcS, hcS2, hcSf⟩ := hL
  obtain ⟨hl6, hn1, hn20, hmn⟩ := lv4_front κ hi
  have hs := hM.1
  simp only [regs] at hs hcS htb
  have hRe : (Snd.CKind.lv κ i).rows = 2 ^ (Snd.CKind.lv κ i).ell := rfl
  have hPl : 2 ^ (Snd.CKind.lv κ i).ell ≤ 2 ^ 6 := Nat.pow_le_pow_right (by norm_num) hl6
  have hP1 : 1 ≤ 2 ^ (Snd.CKind.lv κ i).logN := Nat.one_le_two_pow
  have dX : tb + 800 ≤ xb := by omega
  have dY : tb + 800 ≤ yb := by omega
  -- the `eq` table
  rw [decFront4IR, semXIR_seq]
  obtain ⟨e1, e2, hM1⟩ := eqtIR_sem I s hM (ℓ := (Snd.CKind.lv κ i).ell) (cb := cbS) (eb := eb)
    (S := Snd.T4.sAt es i) (by omega) (by simp only [regs]; omega) (by omega)
    (by simp only [regs]; omega) (by omega) (by omega) (.inl (by omega)) hS
  have z1 := size_sem I (eqtIR (Snd.CKind.lv κ i).ell cbS eb) s
  have h256 : 4 * 2 ^ (Snd.CKind.lv κ i).ell ≤ 256 := by
    have := Nat.mul_le_mul_left 4 hPl; simpa using this
  have e2' : ∀ y, regs ≤ y → (y < eb ∨ eb + 256 ≤ y) →
      rd (semXIR I (eqtIR (Snd.CKind.lv κ i).ell cbS eb) s).M y = rd s.M y := fun y hy h =>
    e2 y hy (h.imp_right fun h' => le_trans (Nat.add_le_add_left h256 _) h')
  have hmsg' := hmsg
  generalize semXIR I (eqtIR (Snd.CKind.lv κ i).ell cbS eb) s = s1 at e1 e2' hM1 z1 hmsg'
  clear e2
  -- the message
  rw [semXIR_seq]
  obtain ⟨m1, m2, hM2⟩ := hmsg' s1 hM1 rfl fun y _ _ => rfl
  have z2 := size_sem I msg s1
  generalize semXIR I msg s1 = s2 at m1 m2 hM2 z2
  -- `Enc` of `X`
  rw [semXIR_seq, semXIR_seq]
  obtain ⟨a1, a2, hM3⟩ := setA_sem I s2 hM2 xb
  have z3 := size_sem I (setA xb) s2
  generalize semXIR I (setA xb) s2 = s3 at a1 a2 hM3 z3
  have h31 : ∀ y, regs ≤ y → (y < xb ∨ yb + 2 * 2 ^ (Snd.CKind.lv κ i).logN ≤ y) →
      (y < eb ∨ eb + 256 ≤ y) → rd s3.M y = rd s.M y := fun y hy h1 h2 => by
    rw [a2 y hy, m2 y hy h1, e2' y hy h2]
  have hT3 : ∀ v < 20, ∀ i' < 20, rdF s3.M (tb + 40 * v + 2 * i') = (wRow D logNMax v).getD i' 0 :=
    fun v hv i' hi' => by
      rw [← hT v hv i' hi']
      exact rdF_eq (h31 _ (by simp only [regs]; omega) (.inl (by omega)) (.inl (by omega)))
        (h31 _ (by simp only [regs]; omega) (.inl (by omega)) (.inl (by omega)))
  have hX3 : ∀ j < 2 ^ (Snd.CKind.lv κ i).logN, rdF s3.M (xb + 2 * j) =
      if h : j < 2 ^ Snd.T4.mLog κ i then
        (fun x : Fin (2 ^ Snd.T4.mLog κ i) => (Snd.T4.nextMsg κ L es i x).f₀) ⟨j, h⟩
      else 0 := fun j hj => by
    rw [rdF_eq (a2 _ (by simp only [regs]; omega)) (a2 _ (by simp only [regs]; omega)), (m1 j hj).1]
    by_cases h : j < 2 ^ Snd.T4.mLog κ i
    · rw [if_pos h, dif_pos h]
    · rw [if_neg h, dif_neg h]
  have f1 := fwdIR_enc I s3 hM3 (A := xb) (tb := tb) hn1 hn20 hmn
    (by simp only [regs]; omega) (by omega) (by omega) (by simp only [regs]; omega)
    (by omega) (.inl dX) a1 hT3
    (fun x : Fin (2 ^ Snd.T4.mLog κ i) => (Snd.T4.nextMsg κ L es i x).f₀) hX3
  obtain ⟨-, f2, hM4⟩ := fwdIR_sem I s3 hM3 (A := xb) (tb := tb) hn1 hn20
    (by simp only [regs]; omega) (by omega) (by omega) (by simp only [regs]; omega)
    (by omega) (.inl dX) a1 hT3 (Y := fun j => if h : j < 2 ^ Snd.T4.mLog κ i then
      (fun x : Fin (2 ^ Snd.T4.mLog κ i) => (Snd.T4.nextMsg κ L es i x).f₀) ⟨j, h⟩ else 0) hX3
  have z4 := size_sem I (fwdIR (Snd.CKind.lv κ i).logN tb) s3
  generalize semXIR I (fwdIR (Snd.CKind.lv κ i).logN tb) s3 = s4 at f1 f2 hM4 z4
  -- `Enc` of `Y`
  rw [semXIR_seq, semXIR_seq]
  obtain ⟨b1, b2, hM5⟩ := setA_sem I s4 hM4 yb
  have z5 := size_sem I (setA yb) s4
  generalize semXIR I (setA yb) s4 = s5 at b1 b2 hM5 z5
  have hT5 : ∀ v < 20, ∀ i' < 20, rdF s5.M (tb + 40 * v + 2 * i') = (wRow D logNMax v).getD i' 0 :=
    fun v hv i' hi' => by
      rw [← hT3 v hv i' hi']
      exact rdF_eq ((b2 _ (by simp only [regs]; omega)).trans
          (f2 _ (by simp only [regs]; omega) (.inl (by omega))))
        ((b2 _ (by simp only [regs]; omega)).trans (f2 _ (by simp only [regs]; omega) (.inl (by omega))))
  have hY5 : ∀ j < 2 ^ (Snd.CKind.lv κ i).logN, rdF s5.M (yb + 2 * j) =
      if h : j < 2 ^ Snd.T4.mLog κ i then
        (fun x : Fin (2 ^ Snd.T4.mLog κ i) => (Snd.T4.nextMsg κ L es i x).f₁) ⟨j, h⟩
      else 0 := fun j hj => by
    rw [rdF_eq ((b2 _ (by simp only [regs]; omega)).trans
        (f2 _ (by simp only [regs]; omega) (.inr (by omega))))
      ((b2 _ (by simp only [regs]; omega)).trans (f2 _ (by simp only [regs]; omega) (.inr (by omega)))),
      rdF_eq (a2 _ (by simp only [regs]; omega)) (a2 _ (by simp only [regs]; omega)), (m1 j hj).2]
    by_cases h : j < 2 ^ Snd.T4.mLog κ i
    · rw [if_pos h, dif_pos h]
    · rw [if_neg h, dif_neg h]
  have g1 := fwdIR_enc I s5 hM5 (A := yb) (tb := tb) hn1 hn20 hmn
    (by simp only [regs]; omega) (by omega) (by omega) (by simp only [regs]; omega)
    (by omega) (.inl dY) b1 hT5
    (fun x : Fin (2 ^ Snd.T4.mLog κ i) => (Snd.T4.nextMsg κ L es i x).f₁) hY5
  obtain ⟨-, g2, hM6⟩ := fwdIR_sem I s5 hM5 (A := yb) (tb := tb) hn1 hn20
    (by simp only [regs]; omega) (by omega) (by omega) (by simp only [regs]; omega)
    (by omega) (.inl dY) b1 hT5 (Y := fun j => if h : j < 2 ^ Snd.T4.mLog κ i then
      (fun x : Fin (2 ^ Snd.T4.mLog κ i) => (Snd.T4.nextMsg κ L es i x).f₁) ⟨j, h⟩ else 0) hY5
  have z6 := size_sem I (fwdIR (Snd.CKind.lv κ i).logN tb) s5
  generalize semXIR I (fwdIR (Snd.CKind.lv κ i).logN tb) s5 = s6 at g1 g2 hM6 z6
  -- the heap of `s6`
  have h6 : ∀ y, regs ≤ y → (y < xb ∨ yb + 2 * 2 ^ (Snd.CKind.lv κ i).logN ≤ y) →
      (y < eb ∨ eb + 256 ≤ y) → rd s6.M y = rd s.M y := fun y hy h1 h2 => by
    rw [g2 y hy (by omega), b2 y hy, f2 y hy (by omega), h31 y hy h1 h2]
  have hb6 : ∀ y, cb ≤ y → rd s6.M y = rd s.M y := fun y hy =>
    h6 y (by simp only [regs]; omega) (.inr (by omega)) (.inr (by omega))
  have hW6 : ∀ j (hj : j < 2 ^ (Snd.CKind.lv κ i).logN) (r : Fin (Snd.CKind.lv κ i).rows),
      rdF s6.M (cb + cs * j + 2 * r) = Snd.T4.wordOf κ L es i r ⟨j, hj⟩ := fun j hj r => by
    rw [← hW j hj r]
    have l1 : cb ≤ cb + cs * j + 2 * r := (Nat.le_add_right cb _).trans (Nat.le_add_right _ _)
    exact rdF_eq (hb6 _ l1) (hb6 _ (l1.trans (Nat.le_add_right _ _)))
  have hE6 : ∀ r < (Snd.CKind.lv κ i).rows,
      rdK s6.M (eb + 4 * r) = eqBits (Snd.T4.sAt es i) (Snd.CKind.lv κ i).ell r :=
    fun r hr => by
      rw [← e1 r (by rw [← hRe]; exact hr)]
      refine rdK_eq fun t ht => ?_
      have hr64 : r < 64 := lt_of_lt_of_le hr (by rw [hRe]; simpa using hPl)
      rw [g2 _ (by simp only [regs]; omega) (by omega), b2 _ (by simp only [regs]; omega),
        f2 _ (by simp only [regs]; omega) (by omega), a2 _ (by simp only [regs]; omega),
        m2 _ (by simp only [regs]; omega) (.inl (by omega))]
  have hX6 : ∀ j < 2 ^ (Snd.CKind.lv κ i).logN,
      rdF s6.M (xb + 2 * j) = encF (Snd.T4.mLog κ i) (fun x => (Snd.T4.nextMsg κ L es i x).f₀) j :=
    fun j hj => by
      rw [← f1 j hj]
      exact rdF_eq ((g2 _ (by simp only [regs]; omega) (.inl (by omega))).trans
          (b2 _ (by simp only [regs]; omega)))
        ((g2 _ (by simp only [regs]; omega) (.inl (by omega))).trans (b2 _ (by simp only [regs]; omega)))
  -- the flags
  have hR64 : (Snd.CKind.lv κ i).rows ≤ 64 := by rw [hRe]; simpa using hPl
  obtain ⟨k1, k2, hM7⟩ := flagIR_sem I s6 hM6 (n := 2 ^ (Snd.CKind.lv κ i).logN)
    (R := (Snd.CKind.lv κ i).rows) (cs := cs) (cb := cb) (eb := eb) (xb := xb) (yb := yb) (fb := fb)
    (by omega) (by omega) hcs (by simp only [regs]; omega) hcb2 (by simp only [regs]; omega) (by omega)
    (by simp only [regs]; omega) (by omega) (by simp only [regs]; omega) (by omega)
    (by simp only [regs]; omega) (by omega) (by omega) (.inr (by omega)) (.inr (by omega))
    (.inr (by omega)) (.inr (by omega))
  have hc := flagV_consSet4 (M := s6.M) (cs := cs) (cb := cb) (eb := eb) (xb := xb) (yb := yb)
    hW6 hE6 hX6 g1
  refine ⟨fun j hj => by rw [k1 j hj]; exact hc j hj, fun y hy hy2 => ?_, hM7⟩
  rw [k2 y hy (by omega), h6 y hy (by omega) (by omega)]

end FR.X
