-- New for `flock-recursive` (BLUEPRINT revision 4.2, §6.2 step 4; stage S-H4, pass 2, item 2).
import FRXDec4Front
import FRXDec4Back

/-!
# One level's decode at revision 4.1's kinds (`decLv4_sem`)

`decLv4IR` is the front half (`eq` table, the next message by `msg`, `Enc`, the flags) followed by
the back half (scan, `lagIR` on rows `c₀ … c₀ + C − 1`, the butterflies). **The memory map is a
parameter**: `tb < fb < [jb, pb, yl, ob] < eb < xb < yb ≤ cb` (`BackLay4`, `FrontLay4`, and the back
half's regions ending below the `eq` table).

**`decLv4_sem`**: on a close word with `A_c = jointAgree`, row `c` at `ob + 2kc` holds the `F`
values of `T4.msgOf κ L es i (c₀ + c)`; the heap below `fb`, between the regions, and from
`yb + 2n` on is kept.
-/

namespace FR.X

open RecursionFast FR Finset

-- G2: `entryK`/`storeM`/`runPrims` are never unfolded while unifying states (elaboration time).
attribute [local irreducible] entryK storeM runPrims

/-- **One level's decode** at a 4.1 kind. -/
def decLv4IR (msg : XIR) (ℓ logN m R C c0 cs cb cbS tb fb jb pb yl ob eb xb yb : ℕ) : XIR :=
  .seq (decFront4IR msg ℓ logN R cs cb cbS tb fb eb xb yb)
    (decBack4IR (2 ^ logN) m C c0 cs cb tb fb jb pb yl ob)

/-- **One level decodes on the machine** at a 4.1 kind (`level_decode4`). -/
theorem decLv4_sem (I : Array Word) (s : St) (hM : Inv s.M) {κ : Snd.CKind} {L es : Log}
    {i C c0 cs cb cbS tb fb jb pb yl ob eb xb yb : ℕ} {msg : XIR} (hi : i < 5)
    (hfar : ¬ Snd.T4.farL κ L es i)
    (hA : Snd.T4.consSet κ L es i = jointAgree (Snd.T4.wordK κ L es i) (Snd.T4.decodeL κ L es i))
    (hC1 : 1 ≤ C) (hC : C ≤ 16) (hcr : c0 + C ≤ (Snd.CKind.lv κ i).rows)
    (hB : BackLay4 (2 ^ (Snd.CKind.lv κ i).logN) (2 ^ Snd.T4.mLog κ i) C tb fb jb pb yl ob)
    (hF : FrontLay4 (2 ^ (Snd.CKind.lv κ i).logN) (Snd.CKind.lv κ i).ell tb fb eb xb yb cbS)
    (hoe : ob + 2 * 2 ^ Snd.T4.mLog κ i * (C + 1) ≤ eb)
    (hsz : yb + 2 * 2 ^ (Snd.CKind.lv κ i).logN ≤ s.M.size)
    (hcs : 2 * (Snd.CKind.lv κ i).rows ≤ cs) (hcb : yb + 2 * 2 ^ (Snd.CKind.lv κ i).logN ≤ cb)
    (hcb2 : cb + cs * 2 ^ (Snd.CKind.lv κ i).logN + 2 * (c0 + C) + 2 < 2 ^ 64)
    (hT : ∀ v < 20, ∀ i < 20, rdF s.M (tb + 40 * v + 2 * i) = (wRow D logNMax v).getD i 0)
    (hW : ∀ j (hj : j < 2 ^ (Snd.CKind.lv κ i).logN) (r : Fin (Snd.CKind.lv κ i).rows),
      rdF s.M (cb + cs * j + 2 * r) = Snd.T4.wordOf κ L es i r ⟨j, hj⟩)
    (hS : ∀ v < (Snd.CKind.lv κ i).ell, rdK s.M (cbS + 8 * v) = Snd.T4.sAt es i v)
    (hmsg : MsgOk4 I msg (semXIR I (eqtIR (Snd.CKind.lv κ i).ell cbS eb) s) eb xb yb
      (Snd.CKind.lv κ i).logN (Snd.T4.mLog κ i) (Snd.T4.nextMsg κ L es i)) :
    (∀ c < C, ∀ x < 2 ^ Snd.T4.mLog κ i,
      algebraMap F K (rdF (semXIR I (decLv4IR msg (Snd.CKind.lv κ i).ell (Snd.CKind.lv κ i).logN
        (Snd.T4.mLog κ i) (Snd.CKind.lv κ i).rows C c0 cs cb cbS tb fb jb pb yl ob eb xb yb) s).M
        (ob + 2 * 2 ^ Snd.T4.mLog κ i * c + 2 * x)) = Snd.T4.msgOf κ L es i (c0 + c) x) ∧
    (∀ y, regs ≤ y → (y < fb ∨ (fb + 2 ^ (Snd.CKind.lv κ i).logN ≤ y ∧ y < jb) ∨
        (jb + 2 ^ Snd.T4.mLog κ i ≤ y ∧ y < pb) ∨ (ob + 2 * 2 ^ Snd.T4.mLog κ i * C ≤ y ∧ y < eb) ∨
        yb + 2 * 2 ^ (Snd.CKind.lv κ i).logN ≤ y) →
      rd (semXIR I (decLv4IR msg (Snd.CKind.lv κ i).ell (Snd.CKind.lv κ i).logN
        (Snd.T4.mLog κ i) (Snd.CKind.lv κ i).rows C c0 cs cb cbS tb fb jb pb yl ob eb xb yb) s).M y =
        rd s.M y) ∧
    Inv (semXIR I (decLv4IR msg (Snd.CKind.lv κ i).ell (Snd.CKind.lv κ i).logN
        (Snd.T4.mLog κ i) (Snd.CKind.lv κ i).rows C c0 cs cb cbS tb fb jb pb yl ob eb xb yb) s).M := by
  obtain ⟨htb, htf, hfj, hjp, hpy, hyo, ho2⟩ := hB
  have hF' := hF
  obtain ⟨-, -, hfe, hex, hxy, hy2, -, -, -⟩ := hF'
  have hkn : 2 ^ Snd.T4.mLog κ i ≤ 2 ^ (Snd.CKind.lv κ i).logN :=
    Nat.pow_le_pow_right (by norm_num) (lv4_front κ hi).2.2.2
  have hcs' : cs * 2 ^ (Snd.CKind.lv κ i).logN ≤ cs * 2 ^ (Snd.CKind.lv κ i).logN := le_rfl
  obtain ⟨a1, a2, hM1⟩ := decFront4_sem I s hM (msg := msg) hi hF hsz hcs hcb (by omega) hT hW hS hmsg
  rw [decLv4IR, semXIR_seq]
  have z1 := size_sem I (decFront4IR msg (Snd.CKind.lv κ i).ell (Snd.CKind.lv κ i).logN
    (Snd.CKind.lv κ i).rows cs cb cbS tb fb eb xb yb) s
  generalize semXIR I (decFront4IR msg (Snd.CKind.lv κ i).ell (Snd.CKind.lv κ i).logN
    (Snd.CKind.lv κ i).rows cs cb cbS tb fb eb xb yb) s = s1 at a1 a2 hM1 z1
  have hb1 : ∀ y, cb ≤ y → rd s1.M y = rd s.M y := fun y hy =>
    a2 y (by simp only [regs] at htb ⊢; omega) (.inr (.inr (by omega)))
  have hT1 : ∀ v < 20, ∀ i' < 20, rdF s1.M (tb + 40 * v + 2 * i') = (wRow D logNMax v).getD i' 0 :=
    fun v hv i' hi' => by
      rw [← hT v hv i' hi']
      exact rdF_eq (a2 _ (by simp only [regs] at htb ⊢; omega) (.inl (by omega)))
        (a2 _ (by simp only [regs] at htb ⊢; omega) (.inl (by omega)))
  have hW1 : ∀ j (hj : j < 2 ^ (Snd.CKind.lv κ i).logN) (r : Fin (Snd.CKind.lv κ i).rows),
      rdF s1.M (cb + cs * j + 2 * r) = Snd.T4.wordOf κ L es i r ⟨j, hj⟩ := fun j hj r => by
    rw [← hW j hj r]
    have l1 : cb ≤ cb + cs * j + 2 * r := (Nat.le_add_right cb _).trans (Nat.le_add_right _ _)
    exact rdF_eq (hb1 _ l1) (hb1 _ (l1.trans (Nat.le_add_right _ _)))
  obtain ⟨b1, b2, hM2⟩ := decBack4_sem I s1 hM1 (cs := cs) (cb := cb) hi hfar hA hC1 hC hcr
    ⟨htb, htf, hfj, hjp, hpy, hyo, ho2⟩ (by omega) hcb2 (by rw [z1]; omega) hT1 hW1 a1
  have hCk : 2 * 2 ^ Snd.T4.mLog κ i * (C + 1) = 2 * 2 ^ Snd.T4.mLog κ i * C + 2 * 2 ^ Snd.T4.mLog κ i :=
    Nat.mul_succ _ _
  refine ⟨b1, fun y hy hy2 => ?_, hM2⟩
  rw [b2 y hy (by omega), a2 y hy (by omega)]

/-! ## Controls: a level-0 map at `m = 32` -/

/-- (+) **The front half's map at `m = 32`, level 0**: flags `2^21`, the `eq` table `2^25`, `X`
`2^25 + 256`, `Y` `2^25 + 256 + 2^21`, the challenges at `2^24` (above the flags). With
`backLay4_m32` the back half's regions end at `2^23 + 2^22 + 5 · 2^20 ≤ 2^25`. -/
theorem frontLay4_m32 : FrontLay4 (2 ^ 20) 6 (2 ^ 20) (2 ^ 21) (2 ^ 25) (2 ^ 25 + 256)
    (2 ^ 25 + 256 + 2 ^ 21) (2 ^ 24) ∧ (2 ^ 23 + 2 ^ 22) + 2 * 2 ^ 19 * (4 + 1) ≤ 2 ^ 25 := by
  unfold FrontLay4; norm_num [regs]

/-- (−) **`FrontLay4` rejects `X` on top of the `eq` table.** -/
theorem not_frontLay4_overlap : ¬ FrontLay4 (2 ^ 20) 6 (2 ^ 20) (2 ^ 21) (2 ^ 25) (2 ^ 25)
    (2 ^ 25 + 256 + 2 ^ 21) (2 ^ 24) := by
  unfold FrontLay4; norm_num [regs]

end FR.X
