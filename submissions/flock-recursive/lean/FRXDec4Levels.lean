-- G6: this module also holds the former modules `FRXDec4Lv`, `FRXDec4Msg`, `FRXDec4Map` (one section each, in import order).
import FRXDec4Front
import FRXChainTop
import FRXRead

section G6_FRXDec4Lv

-- New for `flock-recursive` (BLUEPRINT revision 4.2, §6.2 step 4; stage S-H4, pass 2, item 2).

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

end G6_FRXDec4Lv

section G6_FRXDec4Msg

-- New for `flock-recursive` (BLUEPRINT revision 4.2, §6.2 step 4; stage S-H4, pass 4, item 1).

/-!
# The message steps at revision 4.1's kinds (`MsgOk4`)

Each level's front half runs a message step `msg` that lays out the next level's message as the
coordinate rows `X`, `Y` (`MsgOk4`). There are two (3.x's `msgOk_lower`/`msgOk_four` on a
parametric memory map, over T4's `CKind` truths):

* **`msgOk4_lower`** (levels 0–3): `msgHIR` gathers level `i + 1`'s decoded rows, all 16 of them,
  from `ob` (row `r` at `ob + 2kr`, `k = 2^mLog (i + 1)`; `decLv4_sem`'s output at `c₀ = 0`,
  `C = 16`);
* **`msgOk4_four`** (level 4): `msgTIR` copies the final message (`T4.finalAt`, the absorb at
  `phStart4 47`) from the tape at `tw`, given the tape link `hfin`. The link to π's final field at
  revision 4.1's offset is stated where the format is fixed (A2′), not here.

The constants per kind and level (`msg4_params`) are checked by `decide` on the ladder.
-/

namespace FR.X

open RecursionFast FR Finset

-- G2: `entryK`/`storeM`/`runPrims` are never unfolded while unifying states (elaboration time).
attribute [local irreducible] entryK storeM runPrims

/-- The ladder's message sizes (every 4.1 kind, levels 0–3): `kᵢ = 8 kᵢ₊₁`, `8 kᵢ₊₁ ≤ nᵢ`,
`log nᵢ ≤ 20`. -/
theorem msg4_params (κ : Snd.CKind) {i : ℕ} (hi : i < 4) :
    2 ^ Snd.T4.mLog κ i = 8 * 2 ^ Snd.T4.mLog κ (i + 1) ∧
      8 * 2 ^ Snd.T4.mLog κ (i + 1) ≤ 2 ^ (Snd.CKind.lv κ i).logN ∧ (Snd.CKind.lv κ i).logN ≤ 20 := by
  rcases κ with (_|_|_) | (_|_|_) <;> interval_cases i <;> decide

/-- Level 4's sizes (every 4.1 kind): `k₄ = 2^mLog 4 ≤ 2^logN`, `log n₄ ≤ 20`, `k₄ ≤ 2^7`. -/
theorem msg4_four_params (κ : Snd.CKind) :
    2 ^ Snd.T4.mLog κ 4 ≤ 2 ^ (Snd.CKind.lv κ 4).logN ∧ (Snd.CKind.lv κ 4).logN ≤ 20 ∧
      2 ^ Snd.T4.mLog κ 4 ≤ 2 ^ 7 := by
  rcases κ with (_|_|_) | (_|_|_) <;> decide

/-- **The rows of levels 0–3** at a 4.1 kind (3.x's `msgH_next`): if level `i + 1`'s decoded
row `r` sits at `ob + 2kr` as the `F` values of `msgOf (i + 1) r`, entry `j < 2^n` of `X` (`Y`)
is `(nextMsg i j).f₀` (`.f₁`) for `j < 2^mLog i`, and `0` above. -/
theorem msgH4_next {κ : Snd.CKind} {L es : Log} {i : ℕ} (hi : i < 4) (I : Array Word) (s : St)
    (hM : Inv s.M) {ob xb yb : ℕ}
    (hdec : ∀ r < 16, ∀ x < 2 ^ Snd.T4.mLog κ (i + 1),
      algebraMap F K (rdF s.M (ob + 2 * 2 ^ Snd.T4.mLog κ (i + 1) * r + 2 * x)) =
        Snd.T4.msgOf κ L es (i + 1) r x)
    (hF : ∀ r x, Snd.T4.msgOf κ L es (i + 1) r x =
      algebraMap F K (Snd.T4.msgOf κ L es (i + 1) r x).f₀)
    (hob : regs ≤ ob) (hob2 : ob + 32 * 2 ^ Snd.T4.mLog κ (i + 1) < 2 ^ 64)
    (hxb : regs ≤ xb) (hyb : regs ≤ yb)
    (hxb2 : xb + 2 * 2 ^ (Snd.CKind.lv κ i).logN < 2 ^ 64)
    (hyb2 : yb + 2 * 2 ^ (Snd.CKind.lv κ i).logN < 2 ^ 64)
    (hxs : xb + 2 * 2 ^ (Snd.CKind.lv κ i).logN ≤ s.M.size)
    (hys : yb + 2 * 2 ^ (Snd.CKind.lv κ i).logN ≤ s.M.size)
    (hd : xb + 2 * 2 ^ (Snd.CKind.lv κ i).logN ≤ yb ∨ yb + 2 * 2 ^ (Snd.CKind.lv κ i).logN ≤ xb)
    (hdx : ob + 32 * 2 ^ Snd.T4.mLog κ (i + 1) ≤ xb ∨ xb + 2 * 2 ^ (Snd.CKind.lv κ i).logN ≤ ob)
    (hdy : ob + 32 * 2 ^ Snd.T4.mLog κ (i + 1) ≤ yb ∨ yb + 2 * 2 ^ (Snd.CKind.lv κ i).logN ≤ ob) :
    ∀ j < 2 ^ (Snd.CKind.lv κ i).logN,
      rdF (semXIR I (msgHIR (Snd.CKind.lv κ i).logN (2 ^ Snd.T4.mLog κ (i + 1)) ob xb yb) s).M
          (xb + 2 * j) = (if j < 2 ^ Snd.T4.mLog κ i then (Snd.T4.nextMsg κ L es i j).f₀ else 0) ∧
      rdF (semXIR I (msgHIR (Snd.CKind.lv κ i).logN (2 ^ Snd.T4.mLog κ (i + 1)) ob xb yb) s).M
          (yb + 2 * j) = (if j < 2 ^ Snd.T4.mLog κ i then (Snd.T4.nextMsg κ L es i j).f₁ else 0) := by
  intro j hj
  obtain ⟨hm, hk, hn⟩ := msg4_params κ hi
  obtain ⟨h1, h2⟩ := (msgHIR_sem I s hM (k := 2 ^ Snd.T4.mLog κ (i + 1)) hn hk hob hob2 hxb hyb hxb2
    hyb2 hxs hys hd hdx hdy).1 j hj
  rw [h1, h2, hm]
  by_cases hjk : j < 8 * 2 ^ Snd.T4.mLog κ (i + 1)
  · rw [if_pos hjk, if_pos hjk, if_pos hjk, if_pos hjk,
      nextMsg4_coords (by simp only [nLevels]; omega) hF]
    have hd8 : j / 8 < 2 ^ Snd.T4.mLog κ (i + 1) := (Nat.div_lt_iff_lt_mul (by norm_num)).2 (by omega)
    have r0 := hdec (2 * (j % 8)) (by omega) (j / 8) hd8
    have r1 := hdec (2 * (j % 8) + 1) (by omega) (j / 8) hd8
    constructor
    · show _ = (Snd.T4.msgOf κ L es (i + 1) (2 * (j % 8)) (j / 8)).f₀
      rw [← r0]
      show _ = rdF s.M (ob + 2 * 2 ^ Snd.T4.mLog κ (i + 1) * (2 * (j % 8)) + 2 * (j / 8))
      congr 1; ring
    · show _ = (Snd.T4.msgOf κ L es (i + 1) (2 * (j % 8) + 1) (j / 8)).f₀
      rw [← r1]
      show _ = rdF s.M (ob + 2 * 2 ^ Snd.T4.mLog κ (i + 1) * (2 * (j % 8) + 1) + 2 * (j / 8))
      congr 1; ring
  · rw [if_neg hjk, if_neg hjk, if_neg hjk, if_neg hjk]
    exact ⟨rfl, rfl⟩

/-- **The message step of levels 0–3** at a 4.1 kind, on a parametric map (3.x's
`msgOk_lower`): level `i + 1`'s 16 decoded rows at `ob` (below the `eq` table at `eb`), `X` at
`xb ≥ eb + 256`, `Y` at `yb ≥ xb + 2n`. -/
theorem msgOk4_lower {κ : Snd.CKind} {L es : Log} {i : ℕ} (hi : i < 4) (I : Array Word) (s : St)
    {ob eb xb yb : ℕ}
    (hdec : ∀ r < 16, ∀ x < 2 ^ Snd.T4.mLog κ (i + 1),
      algebraMap F K (rdF s.M (ob + 2 * 2 ^ Snd.T4.mLog κ (i + 1) * r + 2 * x)) =
        Snd.T4.msgOf κ L es (i + 1) r x)
    (hF : ∀ r x, Snd.T4.msgOf κ L es (i + 1) r x =
      algebraMap F K (Snd.T4.msgOf κ L es (i + 1) r x).f₀)
    (hob : regs ≤ ob) (hoe : ob + 32 * 2 ^ Snd.T4.mLog κ (i + 1) ≤ eb) (hex : eb + 256 ≤ xb)
    (hxy : xb + 2 * 2 ^ (Snd.CKind.lv κ i).logN ≤ yb)
    (hy2 : yb + 2 * 2 ^ (Snd.CKind.lv κ i).logN < 2 ^ 64)
    (hsz : yb + 2 * 2 ^ (Snd.CKind.lv κ i).logN ≤ s.M.size) :
    MsgOk4 I (msgHIR (Snd.CKind.lv κ i).logN (2 ^ Snd.T4.mLog κ (i + 1)) ob xb yb) s eb xb yb
      (Snd.CKind.lv κ i).logN (Snd.T4.mLog κ i) (Snd.T4.nextMsg κ L es i) := by
  intro s' hM' hsz' hag
  simp only [regs] at hob
  have hdec' : ∀ r < 16, ∀ x < 2 ^ Snd.T4.mLog κ (i + 1),
      algebraMap F K (rdF s'.M (ob + 2 * 2 ^ Snd.T4.mLog κ (i + 1) * r + 2 * x)) =
        Snd.T4.msgOf κ L es (i + 1) r x := fun r hr x hx => by
    rw [← hdec r hr x hx]
    have : 2 * 2 ^ Snd.T4.mLog κ (i + 1) * r ≤ 2 * 2 ^ Snd.T4.mLog κ (i + 1) * 15 :=
      Nat.mul_le_mul_left _ (by omega)
    congr 1
    exact rdF_eq (hag _ (by simp only [regs]; omega) (.inl (by omega)))
      (hag _ (by simp only [regs]; omega) (.inl (by omega)))
  obtain ⟨-, h2, h3⟩ := msgHIR_sem I s' hM' (n := (Snd.CKind.lv κ i).logN)
    (k := 2 ^ Snd.T4.mLog κ (i + 1)) (ob := ob) (xb := xb) (yb := yb) (msg4_params κ hi).2.2
    (msg4_params κ hi).2.1 (by simp only [regs]; omega) (by omega) (by simp only [regs]; omega)
    (by simp only [regs]; omega) (by omega) hy2 (by omega) (by omega) (.inl hxy) (.inl (by omega))
    (.inl (by omega))
  refine ⟨fun j hj => ?_, fun y hy hy2 => ?_, h3⟩
  · have e := msgH4_next hi I s' hM' hdec' hF (by simp only [regs]; omega) (by omega)
      (by simp only [regs]; omega) (by simp only [regs]; omega) (by omega) hy2 (by omega) (by omega)
      (.inl hxy) (.inl (by omega)) (.inl (by omega)) j hj
    exact e
  · exact h2 y hy (by omega) (by omega)

/-- The final message (level 4's next message) is `T4.finalAt`. -/
theorem nextMsg4_four (κ : Snd.CKind) (L es : Log) (x : ℕ) :
    Snd.T4.nextMsg κ L es 4 x = Snd.T4.finalAt es x := by
  rw [Snd.T4.nextMsg, if_neg (by simp only [nLevels]; omega)]

/-- **Level 4's message step** at a 4.1 kind, on a parametric map (3.x's `msgOk_four`):
`msgTIR` copies `k₄ = 2^mLog 4` K elements from the tape at `tw`, given the link
`finalAt es x = (tapeF (tw + 4x), tapeF (tw + 4x + 2))`. -/
theorem msgOk4_four {κ : Snd.CKind} {L es : Log} (I : Array Word) (s : St) {tw eb xb yb : ℕ}
    (hfin : ∀ x < 2 ^ Snd.T4.mLog κ 4,
      Snd.T4.finalAt es x = ⟨tapeF I (tw + 4 * x), tapeF I (tw + 4 * x + 2)⟩)
    (htw : tw + 4 * 2 ^ 7 < 2 ^ 64) (hrx : regs ≤ eb) (hex : eb + 256 ≤ xb)
    (hxy : xb + 2 * 2 ^ (Snd.CKind.lv κ 4).logN ≤ yb)
    (hy2 : yb + 2 * 2 ^ (Snd.CKind.lv κ 4).logN < 2 ^ 64)
    (hsz : yb + 2 * 2 ^ (Snd.CKind.lv κ 4).logN ≤ s.M.size) :
    MsgOk4 I (msgTIR (Snd.CKind.lv κ 4).logN (2 ^ Snd.T4.mLog κ 4) tw xb yb) s eb xb yb
      (Snd.CKind.lv κ 4).logN (Snd.T4.mLog κ 4) (Snd.T4.nextMsg κ L es 4) := by
  intro s' hM' hsz' _
  obtain ⟨hk, hn, hk7⟩ := msg4_four_params κ
  simp only [regs] at hrx
  obtain ⟨h1, h2, h3⟩ := msgTIR_sem I s' hM' (n := (Snd.CKind.lv κ 4).logN)
    (k := 2 ^ Snd.T4.mLog κ 4) (tw := tw) (xb := xb) (yb := yb) hn hk (by omega)
    (by simp only [regs]; omega) (by simp only [regs]; omega) (by omega) hy2 (by omega) (by omega)
    (.inl hxy)
  refine ⟨fun j hj => ?_, fun y hy hy2 => h2 y hy (by omega) (by omega), h3⟩
  rw [(h1 j hj).1, (h1 j hj).2]
  by_cases h : j < 2 ^ Snd.T4.mLog κ 4
  · rw [if_pos h, if_pos h, if_pos h, if_pos h, nextMsg4_four, hfin j h]
    exact ⟨rfl, rfl⟩
  · rw [if_neg h, if_neg h, if_neg h, if_neg h]
    exact ⟨rfl, rfl⟩

/-! ## Controls -/

/-- (value) The ladder's final message sizes: `k₄ = 32, 64, 128` at `m = 30, 31, 32` (`L30`,
`N2`, `N4`). -/
theorem msg4_four_ctl : 2 ^ Snd.T4.mLog (.seg .L30) 4 = 32 ∧ 2 ^ Snd.T4.mLog (.node .N2) 4 = 64 ∧
    2 ^ Snd.T4.mLog (.node .N4) 4 = 128 := by decide

/-- (−) **`MsgOk4` is not trivial**: the empty step does not lay out a nonzero message over a
zero `X` row (3.x's `msgOk_empty_neg` on a parametric map). -/
theorem msgOk4_empty_neg (I : Array Word) (s : St) (hM : Inv s.M) {eb xb yb : ℕ}
    (h0 : rdF s.M xb = 0) : ¬ MsgOk4 I (.blk []) s eb xb yb 0 0 (fun _ => 1) := by
  intro h
  have := ((h s hM rfl fun _ _ _ => rfl).1 0 (by norm_num)).1
  rw [if_pos (by norm_num), Nat.mul_zero, Nat.add_zero] at this
  have e : semXIR I (.blk []) s = s := by rw [semB, runPrims_nil]
  rw [e, h0] at this
  exact absurd this (by decide)

end FR.X

end G6_FRXDec4Msg

section G6_FRXDec4Map

-- New for `flock-recursive` (BLUEPRINT revision 4.2, §6.2 step 4; stage S-H4, pass 4, item 2).

/-!
# The node decoder's memory map at revision 4.1 (`Map4`)

The node decoder runs on `memX4 + mpw·t` words: the decoder's regions below `memX4 = 2^28`, the
log index from `memX4` on (Part 25 F2; the coordinator's Q2 ruling). `Map4` places every region:

| region | base (`map4`) | size at `m = 32` |
|---|---|---|
| registers | `0` | `256` |
| basis table (`wtabIR`) | `tb = 2^20` | `800` |
| the chain (`chainIR`: targets, `H`, answers) | `chB = 2^23` … `chEnd` | `6,144` |
| levels 1–4 (`lU`): flags, `J`, `P`, `Y`, rows, `eq`, `X`, `Y` | `2^24` … `2^24 + 2^23 + 2^20` | |
| level 0 (`l0`): flags, `J`, `P`, `Y`, rows 1–7, `eq`, `X`, `Y` | `2^24` … `36,700,416 + 2^21` | |
| levels 1–4's word | `lU.cb = 2^26` | `32 · 2^18` |
| level 0's word | `l0.cb = 2^27` | `128 · 2^20 = 2^27` |
| the log index | `ix = memX4 = 2^28` | `3t` |

Levels 1–4 run before level 0 and share one map (3.x's `obL`); level 0's regions overlap theirs
except level 1's decoded rows, which level 0's message step reads (`Map4.Ok`'s cross conditions).
The same literal serves `m = 31` (`N2`) and `m = 32` (`N4`, `N8`).

**`Map4.Ok M m`** is a conjunction of numeral inequalities (the sizes are `2^(m − 12 − 2i)`
positions, `2^(m − 13 − 3i)` targets): non-overlap of every region, `MsgOk4`'s `X`/`Y` regions, the
`2k` slack after each output (`ob + 2k(C + 1) ≤ eb`), and the fit under `2^28`. `map4_ok31`,
`map4_ok32` are `decide` on the literal record. `LvMap.back`/`LvMap.front` turn a level's `Ok` into
`BackLay4`/`FrontLay4` and `decLv4_sem`'s remaining layout hypotheses.
-/

namespace FR.X

open RecursionFast FR

-- The decoder's memory `memX4 = 2^28` is `FRXProg`'s (the program's memory, the index's base).

/-- **One level's regions**: flags `fb`, `J` at `jb`, the prefix table `pb`, `lagIR`'s `Y` at
`yl`, the decoded rows `ob`, the `eq` table `eb`, `X` at `xb`, `Y` at `yb`, the word's column store
at `cb` with `cs` words a position. -/
structure LvMap where
  fb : ℕ
  jb : ℕ
  pb : ℕ
  yl : ℕ
  ob : ℕ
  eb : ℕ
  xb : ℕ
  yb : ℕ
  cb : ℕ
  cs : ℕ
  deriving DecidableEq, Repr

/-- **A level's map fits** `n` positions, `k` targets, `C` decoded rows and `R` word rows, after
the basis table at `tb`: the regions in order, each output with `2k` words of slack. -/
def LvMap.Ok (M : LvMap) (tb n k C R : ℕ) : Prop :=
  tb + 800 ≤ M.fb ∧ M.fb + n ≤ M.jb ∧ M.jb + k ≤ M.pb ∧ M.pb + k ≤ M.yl ∧ M.yl + 2 * C * k ≤ M.ob ∧
    M.ob + 2 * k * (C + 1) ≤ M.eb ∧ M.eb + 256 ≤ M.xb ∧ M.xb + 2 * n ≤ M.yb ∧
    M.yb + 2 * n ≤ M.cb ∧ 2 * R ≤ M.cs ∧ M.cb + M.cs * n + 256 < 2 ^ 64

instance (M : LvMap) (tb n k C R : ℕ) : Decidable (M.Ok tb n k C R) := by
  unfold LvMap.Ok; infer_instance

/-- **The node decoder's map**: the basis table, level 0's and levels 1–4's regions, the index. -/
structure Map4 where
  tb : ℕ
  l0 : LvMap
  lU : LvMap
  ix : ℕ
  deriving DecidableEq, Repr

/-- **The map is sound at `m`** (numerals only): the chain's region `[chB, chEnd)` between the
basis table and both levels' regions; level 0 at `2^(m − 12)` positions, `2^(m − 13)` targets,
rows 1–7 decoded (`C = 7`: the selector and `h_out` cells the output reads, S-H4 pass 7) of
64; levels `i = 1 … 4` at `2^(m − 12 − 2i)` positions, `2^(m − 13 − 3i)` targets, all 16 rows;
levels 1–4 keep level 0's word; level 1's rows lie below level 0's `eq` table; level 0's word
ends at the index, at `2^28`. -/
def Map4.Ok (M : Map4) (m : ℕ) : Prop :=
  regs ≤ M.tb ∧ M.tb + 800 ≤ chB ∧ chEnd ≤ M.l0.fb ∧ chEnd ≤ M.lU.fb ∧
    M.l0.Ok M.tb (2 ^ (m - 12)) (2 ^ (m - 13)) 7 64 ∧
    M.lU.Ok M.tb (2 ^ (m - 12 - 2 * 1)) (2 ^ (m - 13 - 3 * 1)) 16 16 ∧
    M.lU.Ok M.tb (2 ^ (m - 12 - 2 * 2)) (2 ^ (m - 13 - 3 * 2)) 16 16 ∧
    M.lU.Ok M.tb (2 ^ (m - 12 - 2 * 3)) (2 ^ (m - 13 - 3 * 3)) 16 16 ∧
    M.lU.Ok M.tb (2 ^ (m - 12 - 2 * 4)) (2 ^ (m - 13 - 3 * 4)) 16 16 ∧
    M.lU.yb + 2 * 2 ^ (m - 12 - 2 * 1) ≤ M.l0.cb ∧
    M.lU.cb + M.lU.cs * 2 ^ (m - 12 - 2 * 1) ≤ M.l0.cb ∧
    M.lU.ob + 32 * 2 ^ (m - 13 - 3 * 1) ≤ M.l0.eb ∧
    M.l0.cb + M.l0.cs * 2 ^ (m - 12) ≤ M.ix ∧ M.ix = memX4

instance (M : Map4) (m : ℕ) : Decidable (M.Ok m) := by
  unfold Map4.Ok; infer_instance

/-- **The node decoder's map** (one literal for `m = 31` and `m = 32`). Reducible: a projection
`map4.tb + c` in an `omega` goal is then a literal sum, not a unary unfolding of `c`. -/
abbrev map4 : Map4 where
  tb := 1048576
  l0 := { fb := 16777216, jb := 17825792, pb := 18350080, yl := 18874368, ob := 26214400,
          eb := 34603008, xb := 34603264, yb := 36700416, cb := 134217728, cs := 128 }
  lU := { fb := 16777216, jb := 17039360, pb := 17104896, yl := 17170432, ob := 19267584,
          eb := 25165824, xb := 25166080, yb := 25690368, cb := 67108864, cs := 32 }
  ix := 268435456

/-- (+) **`map4` is sound at `m = 32`** (`N4`, `N8`). -/
theorem map4_ok32 : map4.Ok 32 := by decide

/-- (+) **`map4` is sound at `m = 31`** (`N2`). -/
theorem map4_ok31 : map4.Ok 31 := by decide

/-- (value) `map4`'s bases are the table's powers of two. -/
theorem map4_ctl : map4.tb = 2 ^ 20 ∧ map4.l0.fb = 2 ^ 24 ∧ map4.l0.eb = 2 ^ 25 + 2 ^ 20 ∧
    map4.l0.cb = 2 ^ 27 ∧ map4.lU.cb = 2 ^ 26 ∧ map4.lU.eb = 2 ^ 24 + 2 ^ 23 ∧ map4.ix = memX4 := by
  decide

/-- (−) **Overlap is rejected**: `X` of level 0 moved onto its `eq` table. -/
theorem not_map4_overlap : ¬ ({ map4 with l0 := { map4.l0 with xb := map4.l0.eb } } : Map4).Ok 32 := by
  decide

/-- (−) **The slack is required**: level 0's `eq` table moved to the end of its rows
(`ob + 2kC`, no `2k` slack). -/
theorem not_map4_slack :
    ¬ ({ map4 with l0 := { map4.l0 with eb := 26214400 + 2 * 2 ^ 19 * 7 } } : Map4).Ok 32 := by
  decide

/-- (−) **The fit is required**: level 0's word one position higher runs into the index. -/
theorem not_map4_fit :
    ¬ ({ map4 with l0 := { map4.l0 with cb := 134217728 + 128 } } : Map4).Ok 32 := by
  decide

/-- (−) **Level 1's rows must lie below level 0's `eq` table**: rows moved above it. -/
theorem not_map4_rows :
    ¬ ({ map4 with lU := { map4.lU with ob := 33554432 } } : Map4).Ok 32 := by
  decide

/-! ## From `Ok` to the level theorems' layouts -/

/-- A level's `Ok` gives the back half's map and `decLv4_sem`'s output slack. -/
theorem LvMap.back {M : LvMap} {tb n k C R : ℕ} (h : M.Ok tb n k C R) (htb : regs ≤ tb) :
    BackLay4 n k C tb M.fb M.jb M.pb M.yl M.ob ∧ M.ob + 2 * k * (C + 1) ≤ M.eb := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, -, h11⟩ := h
  exact ⟨⟨htb, h1, h2, h3, h4, h5, by omega⟩, h6⟩

/-- A level's `Ok` gives the front half's map, for challenges `cbS` in the chain's region below
the level's flags. -/
theorem LvMap.front {M : LvMap} {tb n k C R ℓ cbS : ℕ} (h : M.Ok tb n k C R) (htb : regs ≤ tb)
    (hS : regs ≤ cbS) (hS2 : cbS + 8 * ℓ + 4 ≤ M.fb) :
    FrontLay4 n ℓ tb M.fb M.eb M.xb M.yb cbS := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, -, h11⟩ := h
  exact ⟨htb, h1, by omega, h7, h8, by omega, hS, by omega, .inl hS2⟩

/-- A level's `Ok`: the store above `Y`, its column width, its end below `2^64`. -/
theorem LvMap.store {M : LvMap} {tb n k C R : ℕ} (h : M.Ok tb n k C R) :
    M.yb + 2 * n ≤ M.cb ∧ 2 * R ≤ M.cs ∧ M.cb + M.cs * n + 256 < 2 ^ 64 :=
  ⟨h.2.2.2.2.2.2.2.2.1, h.2.2.2.2.2.2.2.2.2.1, h.2.2.2.2.2.2.2.2.2.2⟩

/-! ## The ladder's sizes per kind -/

/-- Level 0's sizes at a node kind: `2^(m − 12)` positions, `2^(m − 13)` targets, 64 rows. -/
theorem lv0_sizes (κ : Rev4.NodeKind) :
    2 ^ (Snd.CKind.lv (.node κ) 0).logN = 2 ^ ((Snd.CKind.node κ).m - 12) ∧
      2 ^ Snd.T4.mLog (.node κ) 0 = 2 ^ ((Snd.CKind.node κ).m - 13) ∧
      (Snd.CKind.lv (.node κ) 0).rows = 64 ∧ (Snd.CKind.lv (.node κ) 0).ell = 6 := by
  cases κ <;> decide

/-- Level `i ∈ [1, 4]`'s sizes at a node kind: `2^(m − 12 − 2i)` positions, `2^(m − 13 − 3i)`
targets, 16 rows. -/
theorem lvU_sizes (κ : Rev4.NodeKind) {i : ℕ} (hi1 : 1 ≤ i) (hi : i ≤ 4) :
    2 ^ (Snd.CKind.lv (.node κ) i).logN = 2 ^ ((Snd.CKind.node κ).m - 12 - 2 * i) ∧
      2 ^ Snd.T4.mLog (.node κ) i = 2 ^ ((Snd.CKind.node κ).m - 13 - 3 * i) ∧
      (Snd.CKind.lv (.node κ) i).rows = 16 ∧ (Snd.CKind.lv (.node κ) i).ell = 4 := by
  cases κ <;> interval_cases i <;> decide

/-- The node kinds' sizes: `m = 31` (`N2`) or `32` (`N4`, `N8`). -/
theorem node_m (κ : Rev4.NodeKind) : (Snd.CKind.node κ).m = 31 ∨ (Snd.CKind.node κ).m = 32 := by
  cases κ <;> decide

/-- **`map4` is sound at every node kind's `m`.** -/
theorem map4_ok (κ : Rev4.NodeKind) : map4.Ok (Snd.CKind.node κ).m := by
  rcases node_m κ with h | h <;> rw [h]
  · exact map4_ok31
  · exact map4_ok32

/-- `map4`'s level-`i` regions are sound at a node kind's level `i` (`i ∈ [1, 4]`). -/
theorem map4_lvU (κ : Rev4.NodeKind) {i : ℕ} (hi1 : 1 ≤ i) (hi : i ≤ 4) :
    map4.lU.Ok map4.tb (2 ^ (Snd.CKind.lv (.node κ) i).logN) (2 ^ Snd.T4.mLog (.node κ) i) 16 16 := by
  obtain ⟨e1, e2, -, -⟩ := lvU_sizes κ hi1 hi
  rw [e1, e2]
  obtain ⟨-, -, -, -, -, o1, o2, o3, o4, -⟩ := map4_ok κ
  interval_cases i
  · exact o1
  · exact o2
  · exact o3
  · exact o4

/-- `map4`'s level-0 regions are sound at a node kind's level 0. -/
theorem map4_l0 (κ : Rev4.NodeKind) :
    map4.l0.Ok map4.tb (2 ^ (Snd.CKind.lv (.node κ) 0).logN) (2 ^ Snd.T4.mLog (.node κ) 0) 7 64 := by
  obtain ⟨e1, e2, -, -⟩ := lv0_sizes κ
  rw [e1, e2]
  exact (map4_ok κ).2.2.2.2.1

end FR.X

end G6_FRXDec4Map

section G6_FRXDec4Levels

-- New for `flock-recursive` (BLUEPRINT revision 4.2, §6.2 steps 3–4; stage S-H4, pass 6, item 1).

/-!
# The five levels at a revision 4.1 node kind (`decLevels4`)

3.x's `FRXNode.decLevels` at a node kind `κ` (`m = 31` for `N2`, `32` for `N4`, `N8`), on the map
`map4` (`FRXDec4Map`), with the index at `memX4` and the log at tape word `pL`:

`wtabIR ; (readK4 4 ; decLv4IR msgT 4) ; (readK4 3 ; decLv4IR msgU 3) ; … ; decLv4IR msgU 0`.

Levels 4 … 1 decode all 16 rows into `map4.lU.ob` (level `i + 1`'s rows are level `i`'s message);
level 0 decodes rows `1 … 7` (`c₀ = 1`, `C = 7`) into `map4.l0.ob`, from its word at
`map4.l0.cb` (read before, `readK4 0`).

What the format fixes is a parameter: the cap fields' tape words `cw i` (with the tape link to
`capDig es i`), the P1 challenges' heap words `cbS i` (written by the chain, `sAt es i`), and the
final message's tape word `tw` (with the link to `finalAt es`). The ladder (`CKind.lv κ i`) fixes
the heights `sib` and the sizes.

* **`readK4_sem`**: the ladder read of level `i` stores the committed word `wordOf κ L es i`;
* **`lvStep4_sem`**, **`lv0Step4_sem`**: one level's read and decode, keeping `KeepR4`;
* **`decLevels4_sem`**: level 0's rows `1 … 7` at `map4.l0.ob` are `msgOf κ L es 0 (1 + c)`;
* **`cost_decLevels4`**: the exact cost at a kind.
-/

namespace FR.X

open RecursionFast FR FR.Merkle Finset

-- G2: `entryK`/`storeM`/`runPrims` are never unfolded while unifying states (elaboration time).
attribute [local irreducible] entryK storeM runPrims

/-! ## The ladder read at a 4.1 kind -/

/-- **Level `i`'s read at kind `κ`**: `2^logN` positions at height `sib` (the kind's ladder),
the cap entry 0 at tape word `cw`, `nw` words a position from `sb`; the index at `memX4`, the
log at tape word `pL`. -/
def readK4 (pL : ℕ) (κ : Snd.CKind) (i cw sb nw : ℕ) : XIR :=
  readIR4 memX4 pL i cw sb nw (Snd.CKind.lv κ i).sib (2 ^ (Snd.CKind.lv κ i).logN)

/-- The ladder's read parameters (every 4.1 kind, every level). -/
theorem lv4_read (κ : Snd.CKind) {i : ℕ} (hi : i < 5) :
    (Snd.CKind.lv κ i).sib < 64 ∧ (Snd.CKind.lv κ i).logN ≤ 20 ∧ (Snd.CKind.lv κ i).cap ≤ 9 ∧
      (Snd.CKind.lv κ i).logN = (Snd.CKind.lv κ i).cap + (Snd.CKind.lv κ i).sib ∧
      (Snd.CKind.lv κ i).rows ≤ 64 := by
  rcases κ with (_|_|_) | (_|_|_) <;> interval_cases i <;> decide

/-- Two words of a column reading are its `F` element. -/
theorem rdF_colWord {M : Mem} {a r : ℕ} {o : Option ByteArray} (h0 : rd M a = colWord o (2 * r))
    (h1 : rd M (a + 1) = colWord o (2 * r + 1)) :
    rdF M a = (o.map fun col => Snd.readF col (16 * r)).getD 0 := by
  rw [rdF, rdB, rdB, h0, h1]
  cases o with
  | none => rfl
  | some col => rw [Option.map_some, Option.getD_some, Snd.readF, F_ofBytes_words]; rfl

section Read

variable {c : Digest} {π : Proof} {L : Log} {pL : ℕ}

/-- **The read of level `i` at kind `κ` is the committed word** `wordOf κ L es i` when the tape
holds the cap `capDig es i` at `cw`; it keeps the index and the heap outside its store. -/
theorem readK4_sem (hpL : pL ≤ 2 ^ 60) (hD : Dom4 pL c π L) {Xi : ℕ → Word}
    (hX : Sorted4 pL (tp c π L) L Xi) (s : St) (hM : Inv s.M)
    (hXs : ∀ a < L.length, rd s.M (memX4 + a) = Xi a) (hsz : memX4 ≤ s.M.size)
    {κ : Snd.CKind} {es : Log} {i cw sb nw : ℕ} (hi : i < 5)
    (hcw : cw + 4 * 2 ^ (Snd.CKind.lv κ i).cap < 2 ^ 62)
    (hcap : ∀ e < 2 ^ (Snd.CKind.lv κ i).cap, ∀ m < 4,
      (tp c π L).getD (cw + 4 * e + m) 0 = (packBytes (Snd.T4.capDig es i e).toList).getD m 0)
    (hnw : 2 * (Snd.CKind.lv κ i).rows ≤ nw) (hnw2 : nw < 2 ^ 60)
    (hst : sb + nw * 2 ^ (Snd.CKind.lv κ i).logN ≤ memX4) (hsb : regs ≤ sb) :
    (∀ j (hj : j < 2 ^ (Snd.CKind.lv κ i).logN) (r : Fin (Snd.CKind.lv κ i).rows),
      rdF (semXIR (tp c π L) (readK4 pL κ i cw sb nw) s).M (sb + nw * j + 2 * r) =
        Snd.T4.wordOf κ L es i r ⟨j, hj⟩) ∧
    (∀ a < L.length, rd (semXIR (tp c π L) (readK4 pL κ i cw sb nw) s).M (memX4 + a) = Xi a) ∧
    (∀ y, regs ≤ y → (y < sb ∨ sb + nw * 2 ^ (Snd.CKind.lv κ i).logN ≤ y) →
      rd (semXIR (tp c π L) (readK4 pL κ i cw sb nw) s).M y = rd s.M y) ∧
    Inv (semXIR (tp c π L) (readK4 pL κ i cw sb nw) s).M := by
  obtain ⟨hsib, hn, -, hlc, hR⟩ := lv4_read κ hi
  have hb : regs ≤ memX4 := by simp only [regs, memX4]; norm_num
  have hb2 : memX4 ≤ 2 ^ 60 := by simp only [memX4]; norm_num
  have hnp : 2 ^ (Snd.CKind.lv κ i).logN ≤ 2 ^ 20 := Nat.pow_le_pow_right (by norm_num) hn
  have hcapn : 2 ^ (Snd.CKind.lv κ i).logN ≤ 2 ^ (Snd.CKind.lv κ i).cap * 2 ^ (Snd.CKind.lv κ i).sib := by
    rw [← Nat.pow_add, ← hlc]
  obtain ⟨d1, d2, d3⟩ := readIR4_sem hb hb2 hpL hD hX s hM hXs (i := i) (cw := cw) (nw := nw)
    (ncap := 2 ^ (Snd.CKind.lv κ i).cap) (sb := sb) (cap := Snd.T4.capDig es i) hcw hcap hnw2 hsib hnp
    hst hsb hcapn hsz
  have fr := readIR4_frame hb hb2 hpL hD hX s hM hXs (i := i) (cw := cw) (nw := nw)
    (ncap := 2 ^ (Snd.CKind.lv κ i).cap) (sb := sb) (cap := Snd.T4.capDig es i) hcw hcap hnw2 hsib hnp
    hst hsb hcapn hsz
  rw [readK4]
  refine ⟨fun j hj r => ?_, d2, fr, d3⟩
  have hr : 2 * (r : ℕ) + 1 < nw := by have := r.2; omega
  rw [rdF_colWord (d1 j hj (2 * r) (by omega)) (by rw [Nat.add_assoc]; exact d1 j hj (2 * r + 1) hr)]
  rfl

end Read

/-! ## The programs -/

section Prog

variable (κ : Snd.CKind)

/-- Level 4's message step: the final message from the tape at `tw`, into levels 1–4's `X`/`Y`. -/
def msgT4 (tw : ℕ) : XIR :=
  msgTIR (Snd.CKind.lv κ 4).logN (2 ^ Snd.T4.mLog κ 4) tw map4.lU.xb map4.lU.yb

/-- Level `i ∈ [1, 3]`'s message step: level `i + 1`'s 16 rows at `map4.lU.ob`. -/
def msgU4 (i : ℕ) : XIR :=
  msgHIR (Snd.CKind.lv κ i).logN (2 ^ Snd.T4.mLog κ (i + 1)) map4.lU.ob map4.lU.xb map4.lU.yb

/-- Level 0's message step: level 1's 16 rows at `map4.lU.ob`, into level 0's `X`/`Y`. -/
def msg04 : XIR :=
  msgHIR (Snd.CKind.lv κ 0).logN (2 ^ Snd.T4.mLog κ 1) map4.lU.ob map4.l0.xb map4.l0.yb

/-- **The decode of level `i ∈ [1, 4]`**: all 16 rows into `map4.lU.ob`, from the word at
`map4.lU.cb` (32 words a position). -/
def decU4 (cbS : ℕ) (msg : XIR) (i : ℕ) : XIR :=
  decLv4IR msg (Snd.CKind.lv κ i).ell (Snd.CKind.lv κ i).logN (Snd.T4.mLog κ i) (Snd.CKind.lv κ i).rows
    16 0 32 map4.lU.cb cbS map4.tb map4.lU.fb map4.lU.jb map4.lU.pb map4.lU.yl map4.lU.ob map4.lU.eb
    map4.lU.xb map4.lU.yb

/-- **The decode of level 0**: rows `1 … 7` into `map4.l0.ob`, from the word at `map4.l0.cb` (128
words a position). -/
def dec04 (cbS : ℕ) : XIR :=
  decLv4IR (msg04 κ) (Snd.CKind.lv κ 0).ell (Snd.CKind.lv κ 0).logN (Snd.T4.mLog κ 0)
    (Snd.CKind.lv κ 0).rows 7 1 128 map4.l0.cb cbS map4.tb map4.l0.fb map4.l0.jb map4.l0.pb map4.l0.yl
    map4.l0.ob map4.l0.eb map4.l0.xb map4.l0.yb

/-- **Read and decode level `i ∈ [1, 4]`.** -/
def stepU4 (pL cw cbS : ℕ) (msg : XIR) (i : ℕ) : XIR :=
  .seq (readK4 pL κ i cw map4.lU.cb 32) (decU4 κ cbS msg i)

/-- **The five levels at kind `κ`**: the basis table, levels 4, 3, 2, 1 (read and decode), level 0
(its word read before). `cw i`: level `i`'s cap at the tape; `cbS i`: its P1 challenges in the heap;
`tw`: the final message at the tape. -/
def decLevels4 (pL : ℕ) (cw cbS : ℕ → ℕ) (tw : ℕ) : XIR :=
  .seq (wtabIR map4.tb) (.seq (stepU4 κ pL (cw 4) (cbS 4) (msgT4 κ tw) 4)
    (.seq (stepU4 κ pL (cw 3) (cbS 3) (msgU4 κ 3) 3) (.seq (stepU4 κ pL (cw 2) (cbS 2) (msgU4 κ 2) 2)
      (.seq (stepU4 κ pL (cw 1) (cbS 1) (msgU4 κ 1) 1) (dec04 κ (cbS 0))))))

end Prog

/-- The programs read the kind only through its ladder (`m`): `N4` and `N8` share them. -/
theorem decLevels4_m {κ κ' : Snd.CKind} (h : κ.m = κ'.m) (pL : ℕ) (cw cbS : ℕ → ℕ) (tw : ℕ) :
    decLevels4 κ pL cw cbS tw = decLevels4 κ' pL cw cbS tw := by
  simp only [decLevels4, stepU4, readK4, decU4, dec04, msgT4, msgU4, msg04, Snd.T4.mLog, Snd.CKind.lv, h]

/-! ## The heap the chain keeps, the map's numbers -/

/-- The heap the chained decode keeps: below the levels' regions (the basis table, the chain's
answers), and from level 0's word on (the word, the index). -/
def KeepR4 (y : ℕ) : Prop := y < map4.lU.fb ∨ map4.l0.cb ≤ y

/-- Levels 1–4 at a node kind: at most `2^18` positions and `2^16` targets, 16 rows, `ℓ = 4`. -/
theorem lvU4_nums (κ : Rev4.NodeKind) {i : ℕ} (hi1 : 1 ≤ i) (hi : i ≤ 4) :
    2 ^ (Snd.CKind.lv (.node κ) i).logN ≤ 2 ^ 18 ∧ 2 ^ Snd.T4.mLog (.node κ) i ≤ 2 ^ 16 ∧
      (Snd.CKind.lv (.node κ) i).rows = 16 ∧ (Snd.CKind.lv (.node κ) i).ell = 4 := by
  cases κ <;> interval_cases i <;> decide

/-- Level 0 at a node kind: at most `2^20` positions and `2^19` targets, 64 rows, `ℓ = 6`. -/
theorem lv04_nums (κ : Rev4.NodeKind) :
    2 ^ (Snd.CKind.lv (.node κ) 0).logN ≤ 2 ^ 20 ∧ 2 ^ Snd.T4.mLog (.node κ) 0 ≤ 2 ^ 19 ∧
      (Snd.CKind.lv (.node κ) 0).rows = 64 ∧ (Snd.CKind.lv (.node κ) 0).ell = 6 ∧
      2 ^ Snd.T4.mLog (.node κ) 1 ≤ 2 ^ 16 := by
  cases κ <;> decide

/-- `map4`'s numbers (the literal). -/
theorem map4_nums : map4.tb = 1048576 ∧ map4.lU.fb = 16777216 ∧ map4.lU.ob = 19267584 ∧
    map4.lU.eb = 25165824 ∧ map4.lU.xb = 25166080 ∧ map4.lU.yb = 25690368 ∧
    map4.lU.cb = 67108864 ∧ map4.lU.cs = 32 ∧ map4.l0.fb = 16777216 ∧ map4.l0.ob = 26214400 ∧
    map4.l0.eb = 34603008 ∧ map4.l0.xb = 34603264 ∧ map4.l0.yb = 36700416 ∧
    map4.l0.cb = 134217728 ∧ map4.l0.cs = 128 ∧ memX4 = 268435456 := by
  decide

/-- The `eq` table keeps the heap outside `[eb, eb + 256)` (`ℓ ≤ 6`). -/
theorem eqt4_keep (I : Array Word) (s : St) (hM : Inv s.M) {ℓ cb eb : ℕ} (hℓ : ℓ ≤ 6)
    (hcb : regs ≤ cb) (hcb2 : cb + 8 * ℓ + 4 ≤ eb) (hsz : eb + 256 ≤ s.M.size) (heb : eb + 256 < 2 ^ 64) :
    Inv (semXIR I (eqtIR ℓ cb eb) s).M ∧
    ∀ y, regs ≤ y → (y < eb ∨ eb + 256 ≤ y) → rd (semXIR I (eqtIR ℓ cb eb) s).M y = rd s.M y := by
  have hp : 2 ^ ℓ ≤ 2 ^ 6 := Nat.pow_le_pow_right (by norm_num) hℓ
  simp only [regs] at hcb
  obtain ⟨-, h2, h3⟩ := eqtIR_sem I s hM (ℓ := ℓ) (cb := cb) (eb := eb)
    (S := fun v => rdK s.M (cb + 8 * v)) (by omega) (by simp only [regs]; omega) (by omega)
    (by simp only [regs]; omega) (by omega) (by omega) (.inl (by omega)) (fun _ _ => rfl)
  exact ⟨h3, fun y hy hy2 => h2 y hy (hy2.imp_right fun h => le_trans (by omega) h)⟩

/-! ## One step of levels 1–4 -/

section Steps

variable {c : Digest} {π : Proof} {L : Log} {pL : ℕ}

/-- **One step of levels 1–4** at a node kind: from a state `s` agreeing with `s₀` on `KeepR4`
(`s₀` holds the basis table, the challenges and the index), `stepU4` leaves level `i`'s 16 rows
`msgOf i` at `map4.lU.ob` and keeps `KeepR4`. -/
theorem lvStep4_sem (hpL : pL ≤ 2 ^ 60) (hD : Dom4 pL c π L) {Xi : ℕ → Word}
    (hX : Sorted4 pL (tp c π L) L Xi) (s₀ s : St) (hM : Inv s.M) (hsz : memX4 ≤ s.M.size)
    (hK : ∀ y, regs ≤ y → KeepR4 y → rd s.M y = rd s₀.M y)
    (hXs : ∀ a < L.length, rd s₀.M (memX4 + a) = Xi a)
    (hT : ∀ v < 20, ∀ i < 20, rdF s₀.M (map4.tb + 40 * v + 2 * i) = (wRow D logNMax v).getD i 0)
    {κ : Rev4.NodeKind} {es : Log} {i cw cbS : ℕ} {msg : XIR} (hi1 : 1 ≤ i) (hi : i ≤ 4)
    (hfar : ¬ Snd.T4.farL (.node κ) L es i)
    (hA : Snd.T4.consSet (.node κ) L es i =
      jointAgree (Snd.T4.wordK (.node κ) L es i) (Snd.T4.decodeL (.node κ) L es i))
    (hcw : cw + 4 * 2 ^ (Snd.CKind.lv (.node κ) i).cap < 2 ^ 62)
    (hcap : ∀ e < 2 ^ (Snd.CKind.lv (.node κ) i).cap, ∀ m < 4,
      (tp c π L).getD (cw + 4 * e + m) 0 = (packBytes (Snd.T4.capDig es i e).toList).getD m 0)
    (hcS : map4.tb + 800 ≤ cbS) (hcS2 : cbS + 8 * (Snd.CKind.lv (.node κ) i).ell + 4 ≤ map4.lU.fb)
    (hS : ∀ v < (Snd.CKind.lv (.node κ) i).ell, rdK s₀.M (cbS + 8 * v) = Snd.T4.sAt es i v)
    (hmsg : ∀ s' : St, Inv s'.M → s'.M.size = s.M.size →
      (∀ y, regs ≤ y → y < map4.lU.cb → (y < map4.lU.eb ∨ map4.lU.eb + 256 ≤ y) → rd s'.M y = rd s.M y) →
      MsgOk4 (tp c π L) msg s' map4.lU.eb map4.lU.xb map4.lU.yb (Snd.CKind.lv (.node κ) i).logN
        (Snd.T4.mLog (.node κ) i) (Snd.T4.nextMsg (.node κ) L es i)) :
    (∀ r < 16, ∀ x < 2 ^ Snd.T4.mLog (.node κ) i,
      algebraMap F K (rdF (semXIR (tp c π L) (stepU4 (.node κ) pL cw cbS msg i) s).M
        (map4.lU.ob + 2 * 2 ^ Snd.T4.mLog (.node κ) i * r + 2 * x)) = Snd.T4.msgOf (.node κ) L es i r x) ∧
    (∀ y, regs ≤ y → KeepR4 y → rd (semXIR (tp c π L) (stepU4 (.node κ) pL cw cbS msg i) s).M y = rd s.M y) ∧
    Inv (semXIR (tp c π L) (stepU4 (.node κ) pL cw cbS msg i) s).M := by
  set I := tp c π L
  obtain ⟨n1, n2, n3, n4⟩ := lvU4_nums κ hi1 hi
  obtain ⟨e1, e2, e3, e4, e5, e6, e7, e8, e9, e10, e11, e12, e13, e14, e15, e16⟩ := map4_nums
  have hXs' : ∀ a < L.length, rd s.M (memX4 + a) = Xi a := fun a ha =>
    (hK (memX4 + a) (by simp only [regs]; omega) (.inr (by omega))).trans (hXs a ha)
  obtain ⟨hW, -, fr, hM1⟩ := readK4_sem hpL hD hX s hM hXs' hsz (κ := .node κ) (es := es) (i := i)
    (cw := cw) (sb := map4.lU.cb) (nw := 32) (by omega) hcw hcap (by omega) (by norm_num)
    (by omega) (by simp only [regs]; omega)
  have z1 := size_sem I (readK4 pL (.node κ) i cw map4.lU.cb 32) s
  rw [stepU4, semXIR_seq]
  generalize semXIR I (readK4 pL (.node κ) i cw map4.lU.cb 32) s = s1 at hW fr hM1 z1
  have k1 : ∀ y, regs ≤ y → y < map4.lU.fb → rd s1.M y = rd s₀.M y := fun y hy h =>
    (fr y hy (.inl (by omega))).trans (hK y hy (.inl h))
  have hT1 : ∀ v < 20, ∀ i' < 20, rdF s1.M (map4.tb + 40 * v + 2 * i') = (wRow D logNMax v).getD i' 0 :=
    fun v hv i' hi' => by
      rw [← hT v hv i' hi']
      exact rdF_eq (k1 _ (by simp only [regs]; omega) (by omega)) (k1 _ (by simp only [regs]; omega) (by omega))
  have hS1 : ∀ v < (Snd.CKind.lv (.node κ) i).ell, rdK s1.M (cbS + 8 * v) = Snd.T4.sAt es i v :=
    fun v hv => by
      rw [← hS v hv]
      simp only [rdK]
      rw [rdF_eq (k1 _ (by simp only [regs]; omega) (by omega)) (k1 _ (by simp only [regs]; omega) (by omega)),
        rdF_eq (k1 _ (by simp only [regs]; omega) (by omega)) (k1 _ (by simp only [regs]; omega) (by omega))]
  obtain ⟨q1, q2⟩ := eqt4_keep I s1 hM1 (ℓ := (Snd.CKind.lv (.node κ) i).ell) (cb := cbS)
    (eb := map4.lU.eb) (by omega) (by simp only [regs]; omega) (by omega) (by omega) (by omega)
  have hmsg1 := hmsg _ q1 (by rw [size_sem, z1]) fun y hy hcb hq =>
    (q2 y hy hq).trans (fr y hy (.inl hcb))
  have hok := map4_lvU κ hi1 hi
  obtain ⟨hB, hoe⟩ := LvMap.back hok (by simp only [regs]; omega)
  have hF := LvMap.front hok (by simp only [regs]; omega) (by simp only [regs]; omega) hcS2
  obtain ⟨st1, -, st3⟩ := LvMap.store hok
  obtain ⟨b1, b2, b3⟩ := decLv4_sem I s1 hM1 (κ := .node κ) (L := L) (es := es) (i := i) (C := 16)
    (c0 := 0) (cs := 32) (msg := msg) (by omega) hfar hA (by norm_num) le_rfl (by omega) hB hF hoe
    (by omega) (by omega) st1 (by omega) hT1 hW hS1 hmsg1
  refine ⟨fun r hr x hx => ?_, fun y hy hy2 => ?_, b3⟩
  · have := b1 r hr x hx
    rwa [Nat.zero_add] at this
  · have hfr := b2 y hy (by rcases hy2 with h | h <;> [exact .inl (by omega); exact .inr (.inr (.inr (.inr (by omega))))])
    exact hfr.trans (fr y hy (by rcases hy2 with h | h <;> [exact .inl (by omega); exact .inr (by omega)]))

end Steps

/-! ## The message steps on `map4` -/

/-- Level 4's message step owes `MsgOk4` from every state of the size (`msgOk4_four`). -/
theorem msgT4_ok {κ : Rev4.NodeKind} {L es : Log} (I : Array Word) {tw : ℕ}
    (hfin : ∀ x < 2 ^ Snd.T4.mLog (.node κ) 4,
      Snd.T4.finalAt es x = ⟨tapeF I (tw + 4 * x), tapeF I (tw + 4 * x + 2)⟩)
    (htw : tw + 4 * 2 ^ 7 < 2 ^ 64) (s' : St) (hsz : memX4 ≤ s'.M.size) :
    MsgOk4 I (msgT4 (.node κ) tw) s' map4.lU.eb map4.lU.xb map4.lU.yb (Snd.CKind.lv (.node κ) 4).logN
      (Snd.T4.mLog (.node κ) 4) (Snd.T4.nextMsg (.node κ) L es 4) := by
  obtain ⟨n1, -, -, -⟩ := lvU4_nums κ (i := 4) (by norm_num) le_rfl
  obtain ⟨e1, e2, e3, e4, e5, e6, e7, e8, e9, e10, e11, e12, e13, e14, e15, e16⟩ := map4_nums
  exact msgOk4_four I s' hfin htw (by simp only [regs]; omega) (by omega) (by omega) (by omega)
    (by omega)

/-- Level `i ∈ [1, 3]`'s message step owes `MsgOk4` from every state agreeing with `s` below the
words (outside the `eq` table), given level `i + 1`'s rows at `map4.lU.ob` in `s`. -/
theorem msgU4_ok {κ : Rev4.NodeKind} {L es : Log} (I : Array Word) {i : ℕ} (hi1 : 1 ≤ i) (hi : i < 4)
    (s : St)
    (hdec : ∀ r < 16, ∀ x < 2 ^ Snd.T4.mLog (.node κ) (i + 1),
      algebraMap F K (rdF s.M (map4.lU.ob + 2 * 2 ^ Snd.T4.mLog (.node κ) (i + 1) * r + 2 * x)) =
        Snd.T4.msgOf (.node κ) L es (i + 1) r x)
    (hF : ∀ r x, Snd.T4.msgOf (.node κ) L es (i + 1) r x =
      algebraMap F K (Snd.T4.msgOf (.node κ) L es (i + 1) r x).f₀) (s' : St) (hsz : memX4 ≤ s'.M.size)
    (hag : ∀ y, regs ≤ y → y < map4.lU.cb → (y < map4.lU.eb ∨ map4.lU.eb + 256 ≤ y) →
      rd s'.M y = rd s.M y) :
    MsgOk4 I (msgU4 (.node κ) i) s' map4.lU.eb map4.lU.xb map4.lU.yb (Snd.CKind.lv (.node κ) i).logN
      (Snd.T4.mLog (.node κ) i) (Snd.T4.nextMsg (.node κ) L es i) := by
  obtain ⟨n1, -, -, -⟩ := lvU4_nums κ hi1 (by omega)
  obtain ⟨-, m2, -, -⟩ := lvU4_nums κ (i := i + 1) (by omega) (by omega)
  obtain ⟨e1, e2, e3, e4, e5, e6, e7, e8, e9, e10, e11, e12, e13, e14, e15, e16⟩ := map4_nums
  have hdec' : ∀ r < 16, ∀ x < 2 ^ Snd.T4.mLog (.node κ) (i + 1),
      algebraMap F K (rdF s'.M (map4.lU.ob + 2 * 2 ^ Snd.T4.mLog (.node κ) (i + 1) * r + 2 * x)) =
        Snd.T4.msgOf (.node κ) L es (i + 1) r x := fun r hr x hx => by
    rw [← hdec r hr x hx]
    have : 2 * 2 ^ Snd.T4.mLog (.node κ) (i + 1) * r ≤ 2 * 2 ^ 16 * 15 :=
      Nat.mul_le_mul (Nat.mul_le_mul_left 2 m2) (by omega)
    congr 1
    exact rdF_eq (hag _ (by simp only [regs]; omega) (by omega) (.inl (by omega)))
      (hag _ (by simp only [regs]; omega) (by omega) (.inl (by omega)))
  exact msgOk4_lower hi I s' hdec' hF (by simp only [regs]; omega) (by omega) (by omega) (by omega)
    (by omega) (by omega)

/-- Level 0's message step owes `MsgOk4` (on level 0's `X`/`Y`) from every state agreeing with `s`
below level 0's word (outside its `eq` table), given level 1's rows at `map4.lU.ob` in `s`. -/
theorem msg04_ok {κ : Rev4.NodeKind} {L es : Log} (I : Array Word) (s : St)
    (hdec : ∀ r < 16, ∀ x < 2 ^ Snd.T4.mLog (.node κ) 1,
      algebraMap F K (rdF s.M (map4.lU.ob + 2 * 2 ^ Snd.T4.mLog (.node κ) 1 * r + 2 * x)) =
        Snd.T4.msgOf (.node κ) L es 1 r x)
    (hF : ∀ r x, Snd.T4.msgOf (.node κ) L es 1 r x =
      algebraMap F K (Snd.T4.msgOf (.node κ) L es 1 r x).f₀) (s' : St) (hsz : memX4 ≤ s'.M.size)
    (hag : ∀ y, regs ≤ y → y < map4.l0.cb → (y < map4.l0.eb ∨ map4.l0.eb + 256 ≤ y) →
      rd s'.M y = rd s.M y) :
    MsgOk4 I (msg04 (.node κ)) s' map4.l0.eb map4.l0.xb map4.l0.yb (Snd.CKind.lv (.node κ) 0).logN
      (Snd.T4.mLog (.node κ) 0) (Snd.T4.nextMsg (.node κ) L es 0) := by
  obtain ⟨n1, -, -, -, m2⟩ := lv04_nums κ
  obtain ⟨e1, e2, e3, e4, e5, e6, e7, e8, e9, e10, e11, e12, e13, e14, e15, e16⟩ := map4_nums
  have hdec' : ∀ r < 16, ∀ x < 2 ^ Snd.T4.mLog (.node κ) 1,
      algebraMap F K (rdF s'.M (map4.lU.ob + 2 * 2 ^ Snd.T4.mLog (.node κ) 1 * r + 2 * x)) =
        Snd.T4.msgOf (.node κ) L es 1 r x := fun r hr x hx => by
    rw [← hdec r hr x hx]
    have : 2 * 2 ^ Snd.T4.mLog (.node κ) 1 * r ≤ 2 * 2 ^ 16 * 15 :=
      Nat.mul_le_mul (Nat.mul_le_mul_left 2 m2) (by omega)
    congr 1
    exact rdF_eq (hag _ (by simp only [regs]; omega) (by omega) (.inl (by omega)))
      (hag _ (by simp only [regs]; omega) (by omega) (.inl (by omega)))
  have m2' : 2 ^ Snd.T4.mLog (.node κ) (0 + 1) ≤ 2 ^ 16 := m2
  exact msgOk4_lower (by norm_num) I s' hdec' hF (by simp only [regs]; omega) (by omega) (by omega)
    (by omega) (by omega) (by omega)

/-! ## Level 0, and the five levels -/

/-- **Level 0's decode** at a node kind (`decLv4_sem` on `map4.l0`, rows `1 … 7`), from a state
agreeing with `s₀` on `KeepR4`. -/
theorem lv0Step4_sem (I : Array Word) (s₀ s : St) (hM : Inv s.M) (hsz : memX4 ≤ s.M.size)
    (hK : ∀ y, regs ≤ y → KeepR4 y → rd s.M y = rd s₀.M y)
    (hT : ∀ v < 20, ∀ i < 20, rdF s₀.M (map4.tb + 40 * v + 2 * i) = (wRow D logNMax v).getD i 0)
    {κ : Rev4.NodeKind} {L es : Log} {cbS : ℕ} (hfar : ¬ Snd.T4.farL (.node κ) L es 0)
    (hA : Snd.T4.consSet (.node κ) L es 0 =
      jointAgree (Snd.T4.wordK (.node κ) L es 0) (Snd.T4.decodeL (.node κ) L es 0))
    (hcS : map4.tb + 800 ≤ cbS) (hcS2 : cbS + 8 * (Snd.CKind.lv (.node κ) 0).ell + 4 ≤ map4.l0.fb)
    (hS : ∀ v < (Snd.CKind.lv (.node κ) 0).ell, rdK s₀.M (cbS + 8 * v) = Snd.T4.sAt es 0 v)
    (hW : ∀ j (hj : j < 2 ^ (Snd.CKind.lv (.node κ) 0).logN) (r : Fin (Snd.CKind.lv (.node κ) 0).rows),
      rdF s₀.M (map4.l0.cb + 128 * j + 2 * r) = Snd.T4.wordOf (.node κ) L es 0 r ⟨j, hj⟩)
    (hdec : ∀ r < 16, ∀ x < 2 ^ Snd.T4.mLog (.node κ) 1,
      algebraMap F K (rdF s.M (map4.lU.ob + 2 * 2 ^ Snd.T4.mLog (.node κ) 1 * r + 2 * x)) =
        Snd.T4.msgOf (.node κ) L es 1 r x)
    (hF : ∀ r x, Snd.T4.msgOf (.node κ) L es 1 r x =
      algebraMap F K (Snd.T4.msgOf (.node κ) L es 1 r x).f₀) :
    (∀ c < 7, ∀ x < 2 ^ Snd.T4.mLog (.node κ) 0,
      algebraMap F K (rdF (semXIR I (dec04 (.node κ) cbS) s).M
        (map4.l0.ob + 2 * 2 ^ Snd.T4.mLog (.node κ) 0 * c + 2 * x)) = Snd.T4.msgOf (.node κ) L es 0 (1 + c) x) ∧
    Inv (semXIR I (dec04 (.node κ) cbS) s).M := by
  obtain ⟨n1, n2, n3, n4, -⟩ := lv04_nums κ
  obtain ⟨e1, e2, e3, e4, e5, e6, e7, e8, e9, e10, e11, e12, e13, e14, e15, e16⟩ := map4_nums
  have k1 : ∀ y, regs ≤ y → y < map4.lU.fb → rd s.M y = rd s₀.M y := fun y hy h => hK y hy (.inl h)
  have hT1 : ∀ v < 20, ∀ i' < 20, rdF s.M (map4.tb + 40 * v + 2 * i') = (wRow D logNMax v).getD i' 0 :=
    fun v hv i' hi' => by
      rw [← hT v hv i' hi']
      exact rdF_eq (k1 _ (by simp only [regs]; omega) (by omega)) (k1 _ (by simp only [regs]; omega) (by omega))
  have hS1 : ∀ v < (Snd.CKind.lv (.node κ) 0).ell, rdK s.M (cbS + 8 * v) = Snd.T4.sAt es 0 v :=
    fun v hv => by
      rw [← hS v hv]
      simp only [rdK]
      rw [rdF_eq (k1 _ (by simp only [regs]; omega) (by omega)) (k1 _ (by simp only [regs]; omega) (by omega)),
        rdF_eq (k1 _ (by simp only [regs]; omega) (by omega)) (k1 _ (by simp only [regs]; omega) (by omega))]
  have hW1 : ∀ j (hj : j < 2 ^ (Snd.CKind.lv (.node κ) 0).logN) (r : Fin (Snd.CKind.lv (.node κ) 0).rows),
      rdF s.M (map4.l0.cb + 128 * j + 2 * r) = Snd.T4.wordOf (.node κ) L es 0 r ⟨j, hj⟩ := fun j hj r => by
    rw [← hW j hj r]
    exact rdF_eq (hK _ (by simp only [regs]; omega) (.inr (by omega)))
      (hK _ (by simp only [regs]; omega) (.inr (by omega)))
  obtain ⟨q1, q2⟩ := eqt4_keep I s hM (ℓ := (Snd.CKind.lv (.node κ) 0).ell) (cb := cbS)
    (eb := map4.l0.eb) (by omega) (by simp only [regs]; omega) (by omega) (by omega) (by omega)
  have hmsg1 := msg04_ok I s hdec hF _ (by rw [size_sem]; exact hsz) fun y hy _ hq => q2 y hy hq
  have hok := map4_l0 κ
  obtain ⟨hB, hoe⟩ := LvMap.back hok (by simp only [regs]; omega)
  have hF0 := LvMap.front hok (by simp only [regs]; omega) (by simp only [regs]; omega) hcS2
  obtain ⟨st1, -, st3⟩ := LvMap.store hok
  obtain ⟨b1, -, b3⟩ := decLv4_sem I s hM (κ := .node κ) (L := L) (es := es) (i := 0) (C := 7)
    (c0 := 1) (cs := 128) (msg := msg04 (.node κ)) (by omega) hfar hA (by norm_num) (by norm_num)
    (by omega) hB hF0 hoe (by omega) (by omega) st1 (by omega) hT1 hW1 hS1 hmsg1
  exact ⟨b1, b3⟩

section Five

variable {c : Digest} {π : Proof} {L : Log} {pL : ℕ}

/-- **The five levels decode at a node kind** (3.x's `decLevels_sem` on `map4`): on a domain tape
with the sorted index at `memX4`, level 0's word at `map4.l0.cb` (`readK4 0`), the P1 challenges
at `cbS i` (the chain's answers), and, as the log's transcript `es` provides them, the cap links
(tape words `cw i`), the final-message link (tape word `tw`), and at every level a close word with
`A_c = jointAgree`: level 0's rows `1 … 7` sit at `map4.l0.ob` as the `F` values of
`msgOf κ L es 0 (1 + c)` (row `c` at `map4.l0.ob + 2^(mLog 0 + 1) c`). -/
theorem decLevels4_sem (hpL : pL ≤ 2 ^ 60) (hD : Dom4 pL c π L) {Xi : ℕ → Word}
    (hX : Sorted4 pL (tp c π L) L Xi) (s : St) (hM : Inv s.M) (hsz : memX4 ≤ s.M.size)
    (hXs : ∀ a < L.length, rd s.M (memX4 + a) = Xi a)
    {κ : Rev4.NodeKind} {es : Log} {cw cbS : ℕ → ℕ} {tw : ℕ}
    (hW : ∀ j (hj : j < 2 ^ (Snd.CKind.lv (.node κ) 0).logN) (r : Fin (Snd.CKind.lv (.node κ) 0).rows),
      rdF s.M (map4.l0.cb + 128 * j + 2 * r) = Snd.T4.wordOf (.node κ) L es 0 r ⟨j, hj⟩)
    (hcw : ∀ i, 1 ≤ i → i ≤ 4 → cw i + 4 * 2 ^ (Snd.CKind.lv (.node κ) i).cap < 2 ^ 62)
    (hcap : ∀ i, 1 ≤ i → i ≤ 4 → ∀ e < 2 ^ (Snd.CKind.lv (.node κ) i).cap, ∀ m < 4,
      (tp c π L).getD (cw i + 4 * e + m) 0 = (packBytes (Snd.T4.capDig es i e).toList).getD m 0)
    (hcS : ∀ i < 5, map4.tb + 800 ≤ cbS i ∧ cbS i + 8 * (Snd.CKind.lv (.node κ) i).ell + 4 ≤ map4.lU.fb)
    (hS : ∀ i < 5, ∀ v < (Snd.CKind.lv (.node κ) i).ell, rdK s.M (cbS i + 8 * v) = Snd.T4.sAt es i v)
    (hfin : ∀ x < 2 ^ Snd.T4.mLog (.node κ) 4,
      Snd.T4.finalAt es x = ⟨tapeF (tp c π L) (tw + 4 * x), tapeF (tp c π L) (tw + 4 * x + 2)⟩)
    (htw : tw + 4 * 2 ^ 7 < 2 ^ 64)
    (hfar : ∀ i < 5, ¬ Snd.T4.farL (.node κ) L es i)
    (hA : ∀ i < 5, Snd.T4.consSet (.node κ) L es i =
      jointAgree (Snd.T4.wordK (.node κ) L es i) (Snd.T4.decodeL (.node κ) L es i)) :
    (∀ q < 7, ∀ x < 2 ^ Snd.T4.mLog (.node κ) 0,
      algebraMap F K (rdF (semXIR (tp c π L) (decLevels4 (.node κ) pL cw cbS tw) s).M
        (map4.l0.ob + 2 * 2 ^ Snd.T4.mLog (.node κ) 0 * q + 2 * x)) =
        Snd.T4.msgOf (.node κ) L es 0 (1 + q) x) ∧
    Inv (semXIR (tp c π L) (decLevels4 (.node κ) pL cw cbS tw) s).M := by
  set I := tp c π L
  obtain ⟨e1, e2, e3, e4, e5, e6, e7, e8, e9, e10, e11, e12, e13, e14, e15, e16⟩ := map4_nums
  -- the basis table
  obtain ⟨t1, t2, t3, t4⟩ := wtabIR_sem I s hM (tb := map4.tb) (by simp only [regs]; omega)
    (by omega) (by omega)
  rw [decLevels4, semXIR_seq]
  generalize semXIR I (wtabIR map4.tb) s = s₀ at t1 t2 t3 t4
  have hsz0 : memX4 ≤ s₀.M.size := t4 ▸ hsz
  have kt : ∀ y, regs ≤ y → map4.tb + 800 ≤ y → rd s₀.M y = rd s.M y := fun y hy h => t2 y hy (.inr h)
  have hXs0 : ∀ a < L.length, rd s₀.M (memX4 + a) = Xi a := fun a ha =>
    (kt _ (by simp only [regs]; omega) (by omega)).trans (hXs a ha)
  have hS0 : ∀ i < 5, ∀ v < (Snd.CKind.lv (.node κ) i).ell, rdK s₀.M (cbS i + 8 * v) = Snd.T4.sAt es i v :=
    fun i hi v hv => by
      rw [← hS i hi v hv]
      have := (hcS i hi).1
      simp only [rdK]
      rw [rdF_eq (kt _ (by simp only [regs]; omega) (by omega)) (kt _ (by simp only [regs]; omega) (by omega)),
        rdF_eq (kt _ (by simp only [regs]; omega) (by omega)) (kt _ (by simp only [regs]; omega) (by omega))]
  have hW0 : ∀ j (hj : j < 2 ^ (Snd.CKind.lv (.node κ) 0).logN) (r : Fin (Snd.CKind.lv (.node κ) 0).rows),
      rdF s₀.M (map4.l0.cb + 128 * j + 2 * r) = Snd.T4.wordOf (.node κ) L es 0 r ⟨j, hj⟩ := fun j hj r => by
    rw [← hW j hj r]
    exact rdF_eq (kt _ (by simp only [regs]; omega) (by omega)) (kt _ (by simp only [regs]; omega) (by omega))
  have hF : ∀ i < 5, ∀ r x, Snd.T4.msgOf (.node κ) L es i r x =
      algebraMap F K (Snd.T4.msgOf (.node κ) L es i r x).f₀ := fun i hi => msgOf4_embed hi (hfar i hi) (hA i hi)
  -- level 4
  obtain ⟨a1, a2, a3⟩ := lvStep4_sem hpL hD hX s₀ s₀ t3 hsz0 (fun _ _ _ => rfl) hXs0 t1 (i := 4)
    (cw := cw 4) (cbS := cbS 4) (msg := msgT4 (.node κ) tw) (by norm_num) le_rfl (hfar 4 (by norm_num))
    (hA 4 (by norm_num)) (hcw 4 (by norm_num) le_rfl) (hcap 4 (by norm_num) le_rfl)
    (hcS 4 (by norm_num)).1 (hcS 4 (by norm_num)).2 (hS0 4 (by norm_num))
    fun s' _ hz _ => msgT4_ok I hfin htw s' (hz ▸ hsz0)
  rw [semXIR_seq]
  have z4 := size_sem I (stepU4 (.node κ) pL (cw 4) (cbS 4) (msgT4 (.node κ) tw) 4) s₀
  generalize semXIR I (stepU4 (.node κ) pL (cw 4) (cbS 4) (msgT4 (.node κ) tw) 4) s₀ = s4 at a1 a2 a3 z4
  -- level 3
  obtain ⟨b1, b2, b3⟩ := lvStep4_sem hpL hD hX s₀ s4 a3 (z4 ▸ hsz0) a2 hXs0 t1 (i := 3)
    (cw := cw 3) (cbS := cbS 3) (msg := msgU4 (.node κ) 3) (by norm_num) (by norm_num)
    (hfar 3 (by norm_num)) (hA 3 (by norm_num)) (hcw 3 (by norm_num) (by norm_num))
    (hcap 3 (by norm_num) (by norm_num)) (hcS 3 (by norm_num)).1 (hcS 3 (by norm_num)).2
    (hS0 3 (by norm_num))
    fun s' _ hz hag => msgU4_ok I (i := 3) (by norm_num) (by norm_num) s4 a1 (hF 4 (by norm_num)) s'
      (hz ▸ z4 ▸ hsz0) hag
  rw [semXIR_seq]
  have z3 := size_sem I (stepU4 (.node κ) pL (cw 3) (cbS 3) (msgU4 (.node κ) 3) 3) s4
  generalize semXIR I (stepU4 (.node κ) pL (cw 3) (cbS 3) (msgU4 (.node κ) 3) 3) s4 = s3 at b1 b2 b3 z3
  have k3 : ∀ y, regs ≤ y → KeepR4 y → rd s3.M y = rd s₀.M y := fun y hy h =>
    (b2 y hy h).trans (a2 y hy h)
  -- level 2
  obtain ⟨c1, c2, c3⟩ := lvStep4_sem hpL hD hX s₀ s3 b3 (z3 ▸ z4 ▸ hsz0) k3 hXs0 t1 (i := 2)
    (cw := cw 2) (cbS := cbS 2) (msg := msgU4 (.node κ) 2) (by norm_num) (by norm_num)
    (hfar 2 (by norm_num)) (hA 2 (by norm_num)) (hcw 2 (by norm_num) (by norm_num))
    (hcap 2 (by norm_num) (by norm_num)) (hcS 2 (by norm_num)).1 (hcS 2 (by norm_num)).2
    (hS0 2 (by norm_num))
    fun s' _ hz hag => msgU4_ok I (i := 2) (by norm_num) (by norm_num) s3 b1 (hF 3 (by norm_num)) s'
      (hz ▸ z3 ▸ z4 ▸ hsz0) hag
  rw [semXIR_seq]
  have z2 := size_sem I (stepU4 (.node κ) pL (cw 2) (cbS 2) (msgU4 (.node κ) 2) 2) s3
  generalize semXIR I (stepU4 (.node κ) pL (cw 2) (cbS 2) (msgU4 (.node κ) 2) 2) s3 = s2 at c1 c2 c3 z2
  have k2 : ∀ y, regs ≤ y → KeepR4 y → rd s2.M y = rd s₀.M y := fun y hy h =>
    (c2 y hy h).trans (k3 y hy h)
  -- level 1
  obtain ⟨d1, d2, d3⟩ := lvStep4_sem hpL hD hX s₀ s2 c3 (z2 ▸ z3 ▸ z4 ▸ hsz0) k2 hXs0 t1 (i := 1)
    (cw := cw 1) (cbS := cbS 1) (msg := msgU4 (.node κ) 1) le_rfl (by norm_num)
    (hfar 1 (by norm_num)) (hA 1 (by norm_num)) (hcw 1 le_rfl (by norm_num))
    (hcap 1 le_rfl (by norm_num)) (hcS 1 (by norm_num)).1 (hcS 1 (by norm_num)).2
    (hS0 1 (by norm_num))
    fun s' _ hz hag => msgU4_ok I (i := 1) le_rfl (by norm_num) s2 c1 (hF 2 (by norm_num)) s'
      (hz ▸ z2 ▸ z3 ▸ z4 ▸ hsz0) hag
  rw [semXIR_seq]
  have z1 := size_sem I (stepU4 (.node κ) pL (cw 1) (cbS 1) (msgU4 (.node κ) 1) 1) s2
  generalize semXIR I (stepU4 (.node κ) pL (cw 1) (cbS 1) (msgU4 (.node κ) 1) 1) s2 = s1 at d1 d2 d3 z1
  have k1 : ∀ y, regs ≤ y → KeepR4 y → rd s1.M y = rd s₀.M y := fun y hy h =>
    (d2 y hy h).trans (k2 y hy h)
  -- level 0
  exact lv0Step4_sem I s₀ s1 d3 (z1 ▸ z2 ▸ z3 ▸ z4 ▸ hsz0) k1 t1 (hfar 0 (by norm_num))
    (hA 0 (by norm_num)) (hcS 0 (by norm_num)).1 (by have := (hcS 0 (by norm_num)).2; omega)
    (hS0 0 (by norm_num)) hW0 d1 (hF 1 (by norm_num))

end Five

/-! ## Well formed, no `loopT`, no output; the exact cost -/

theorem wf_setA4 (b : ℕ) : WF (setA b) := by
  simp +decide only [setA, WF, Prim.dst, rA0, List.mem_cons, List.mem_nil_iff, forall_eq, or_false]

theorem wf_decLv4IR {msg : XIR} (h : WF msg) (ℓ logN m R C c0 cs cb cbS tb fb jb pb yl ob eb xb yb : ℕ) :
    WF (decLv4IR msg ℓ logN m R C c0 cs cb cbS tb fb jb pb yl ob eb xb yb) :=
  ⟨⟨wf_eqtIR .., h, wf_setA4 _, wf_fwdIR .., wf_setA4 _, wf_fwdIR .., wf_flagIR ..⟩, wf_decBack4IR ..⟩

theorem noLoopT_decLv4IR {msg : XIR} (h : NoLoopT msg)
    (ℓ logN m R C c0 cs cb cbS tb fb jb pb yl ob eb xb yb : ℕ) :
    NoLoopT (decLv4IR msg ℓ logN m R C c0 cs cb cbS tb fb jb pb yl ob eb xb yb) :=
  ⟨⟨noLoopT_eqtIR .., h, trivial, noLoopT_fwdIR .., trivial, noLoopT_fwdIR .., noLoopT_flagIR ..⟩,
    noLoopT_decBack4IR ..⟩

theorem outs_decLv4IR {msg : XIR} {t : ℕ} (h : outs msg t = 0)
    (ℓ logN m R C c0 cs cb cbS tb fb jb pb yl ob eb xb yb : ℕ) :
    outs (decLv4IR msg ℓ logN m R C c0 cs cb cbS tb fb jb pb yl ob eb xb yb) t = 0 := by
  simp only [decLv4IR, decFront4IR, outs, h, outs_eqtIR, setA, outs_fwdIR, outs_flagIR,
    outs_decBack4IR]

/-- **One level's cost at a 4.1 kind** (exact): the message step's, the `eq` table, two forward
transforms, the flags, the back half (`cost_decBack4IR`), and 9 for the sequencing and the two
`setA`. -/
theorem cost_decLv4IR (msg : XIR) (ℓ logN m R C c0 cs cb cbS tb fb jb pb yl ob eb xb yb t : ℕ)
    (hℓ : ℓ ≤ 6) (hn : logN ≤ 20) (hm : m < 64) (hR : R ≤ 64) (hC : C ≤ 64) :
    cost (decLv4IR msg ℓ logN m R C c0 cs cb cbS tb fb jb pb yl ob eb xb yb) t = cost msg t +
      (12 + 2 ^ ℓ * (63 + ℓ * 271)) + 2 * (14 + logN * (741 * 2 ^ (logN - 1) + 27)) +
      (12 + 2 ^ logN * (92 + 156 * R)) +
      ((16 + 2 ^ logN * 32) + (27 + 2 ^ m * (1122 + 72 * C) + (2 ^ m) ^ 2 * (101 + 40 * C)) +
        (1 + C * (17 + m * (741 * 2 ^ (m - 1) + 23))) + 2) + 9 := by
  have p1 : 2 ^ ℓ < 2 ^ 64 := Nat.pow_lt_pow_right (by norm_num) (by omega)
  have p2 : 2 ^ (logN - 1) < 2 ^ 64 := Nat.pow_lt_pow_right (by norm_num) (by omega)
  have p3 : 2 ^ logN < 2 ^ 64 := Nat.pow_lt_pow_right (by norm_num) (by omega)
  rw [decLv4IR, decFront4IR, cost, cost, cost, cost, cost, cost, cost,
    cost_eqtIR _ _ _ _ p1 (by omega), cost_fwdIR _ _ _ p2 (by omega),
    cost_flagIR _ _ _ _ _ _ _ _ _ p3 (by omega), cost_decBack4IR _ _ _ _ _ _ _ _ _ _ _ _ t p3 hm (by omega)]
  simp only [setA, cost, blkSteps, List.length_cons, List.length_nil, ite_self]
  ring

theorem wf_readK4 (pL : ℕ) (κ : Snd.CKind) (i cw sb nw : ℕ) : WF (readK4 pL κ i cw sb nw) :=
  wf_readIR4 ..

theorem noLoopT_readK4 (pL : ℕ) (κ : Snd.CKind) (i cw sb nw : ℕ) : NoLoopT (readK4 pL κ i cw sb nw) :=
  noLoopT_readIR4 ..

theorem outs_readK4 (pL : ℕ) (κ : Snd.CKind) (i cw sb nw t : ℕ) : outs (readK4 pL κ i cw sb nw) t = 0 :=
  outs_readIR4 ..

/-- The read's cost at a 4.1 kind. -/
theorem cost_readK4 (pL : ℕ) (κ : Snd.CKind) {i : ℕ} (hi : i < 5) (cw sb nw t : ℕ) (hnw : nw < 2 ^ 64) :
    cost (readK4 pL κ i cw sb nw) t = 14 + 2 ^ (Snd.CKind.lv κ i).logN * 6576 +
      2 ^ (Snd.CKind.lv κ i).logN * (Snd.CKind.lv κ i).sib * 6544 + 2 ^ (Snd.CKind.lv κ i).logN * nw * 25 := by
  obtain ⟨hsib, hn, -⟩ := lv4_read κ hi
  have p3 : 2 ^ (Snd.CKind.lv κ i).logN < 2 ^ 64 := Nat.pow_lt_pow_right (by norm_num) (by omega)
  exact cost_readIR4 _ _ _ _ _ _ _ _ t p3 (by omega) hnw

section Struct

variable (κ : Snd.CKind) (pL : ℕ) (cw cbS : ℕ → ℕ) (tw : ℕ)

theorem wf_decLevels4 : WF (decLevels4 κ pL cw cbS tw) :=
  ⟨wf_wtabIR _, ⟨wf_readK4 .., wf_decLv4IR (wf_msgTIR ..) ..⟩, ⟨wf_readK4 .., wf_decLv4IR (wf_msgHIR ..) ..⟩,
    ⟨wf_readK4 .., wf_decLv4IR (wf_msgHIR ..) ..⟩, ⟨wf_readK4 .., wf_decLv4IR (wf_msgHIR ..) ..⟩,
    wf_decLv4IR (wf_msgHIR ..) ..⟩

theorem noLoopT_decLevels4 : NoLoopT (decLevels4 κ pL cw cbS tw) :=
  ⟨noLoopT_wtabIR _, ⟨noLoopT_readK4 .., noLoopT_decLv4IR (noLoopT_msgTIR ..) ..⟩,
    ⟨noLoopT_readK4 .., noLoopT_decLv4IR (noLoopT_msgHIR ..) ..⟩,
    ⟨noLoopT_readK4 .., noLoopT_decLv4IR (noLoopT_msgHIR ..) ..⟩,
    ⟨noLoopT_readK4 .., noLoopT_decLv4IR (noLoopT_msgHIR ..) ..⟩,
    noLoopT_decLv4IR (noLoopT_msgHIR ..) ..⟩

theorem outs_decLevels4 (t : ℕ) : outs (decLevels4 κ pL cw cbS tw) t = 0 := by
  simp only [decLevels4, stepU4, decU4, dec04, msgT4, msgU4, msg04, outs, outs_wtabIR, outs_readK4,
    outs_decLv4IR (outs_msgTIR _ _ _ _ _ t), outs_decLv4IR (outs_msgHIR _ _ _ _ _ t)]

end Struct

/-- One level of 1–4 at a node kind costs its read and its decode (exact, in the ladder's
numbers). -/
theorem cost_stepU4 (pL : ℕ) (κ : Rev4.NodeKind) {i : ℕ} (hi1 : 1 ≤ i) (hi : i ≤ 4) (cw cbS : ℕ)
    (msg : XIR) (t : ℕ) :
    cost (stepU4 (.node κ) pL cw cbS msg i) t = (14 + 2 ^ (Snd.CKind.lv (.node κ) i).logN * 6576 +
      2 ^ (Snd.CKind.lv (.node κ) i).logN * (Snd.CKind.lv (.node κ) i).sib * 6544 +
      2 ^ (Snd.CKind.lv (.node κ) i).logN * 32 * 25) +
      (cost msg t + (12 + 2 ^ 4 * (63 + 4 * 271)) +
        2 * (14 + (Snd.CKind.lv (.node κ) i).logN * (741 * 2 ^ ((Snd.CKind.lv (.node κ) i).logN - 1) + 27)) +
        (12 + 2 ^ (Snd.CKind.lv (.node κ) i).logN * (92 + 156 * 16)) +
        ((16 + 2 ^ (Snd.CKind.lv (.node κ) i).logN * 32) + (27 + 2 ^ Snd.T4.mLog (.node κ) i * (1122 + 72 * 16) +
          (2 ^ Snd.T4.mLog (.node κ) i) ^ 2 * (101 + 40 * 16)) +
          (1 + 16 * (17 + Snd.T4.mLog (.node κ) i * (741 * 2 ^ (Snd.T4.mLog (.node κ) i - 1) + 23))) + 2) + 9) + 1 := by
  obtain ⟨-, -, n3, n4⟩ := lvU4_nums κ hi1 hi
  obtain ⟨-, hn, -⟩ := lv4_read (.node κ) (i := i) (by omega)
  obtain ⟨-, hm, -⟩ := lv4_bounds (.node κ) (i := i) (by omega)
  rw [stepU4, cost, cost_readK4 _ _ (by omega) _ _ _ _ (by norm_num), decU4,
    cost_decLv4IR _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ t (by omega) hn (by omega) (by omega) (by norm_num),
    n3, n4]

/-- Level 0 at a node kind costs its message step and its decode (exact, in the ladder's numbers). -/
theorem cost_dec04 (κ : Rev4.NodeKind) (cbS t : ℕ) :
    cost (dec04 (.node κ) cbS) t = (46 + 36 * 2 ^ (Snd.CKind.lv (.node κ) 0).logN +
        560 * 2 ^ Snd.T4.mLog (.node κ) 1) + (12 + 2 ^ 6 * (63 + 6 * 271)) +
      2 * (14 + (Snd.CKind.lv (.node κ) 0).logN * (741 * 2 ^ ((Snd.CKind.lv (.node κ) 0).logN - 1) + 27)) +
      (12 + 2 ^ (Snd.CKind.lv (.node κ) 0).logN * (92 + 156 * 64)) +
      ((16 + 2 ^ (Snd.CKind.lv (.node κ) 0).logN * 32) + (27 + 2 ^ Snd.T4.mLog (.node κ) 0 * (1122 + 72 * 7) +
        (2 ^ Snd.T4.mLog (.node κ) 0) ^ 2 * (101 + 40 * 7)) +
        (1 + 7 * (17 + Snd.T4.mLog (.node κ) 0 * (741 * 2 ^ (Snd.T4.mLog (.node κ) 0 - 1) + 23))) + 2) + 9 := by
  obtain ⟨n1, -, n3, n4, -⟩ := lv04_nums κ
  obtain ⟨-, hn, -⟩ := lv4_read (.node κ) (i := 0) (by omega)
  obtain ⟨-, hm, -⟩ := lv4_bounds (.node κ) (i := 0) (by omega)
  have p1 : 2 * 2 ^ (Snd.CKind.lv (.node κ) 0).logN < 2 ^ 64 := by omega
  have p2 : 8 * 2 ^ Snd.T4.mLog (.node κ) 1 < 2 ^ 64 := by
    have := (lv04_nums κ).2.2.2.2; omega
  rw [dec04, cost_decLv4IR _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ t (by omega) hn (by omega) (by omega)
    (by norm_num), n3, n4, msg04, cost_msgHIR _ _ _ _ _ t p1 p2]

/-- The five levels' cost at a node kind: the basis table, four reads and decodes, level 0. -/
theorem cost_decLevels4_eq (κ : Rev4.NodeKind) (pL : ℕ) (cw cbS : ℕ → ℕ) (tw t : ℕ) :
    cost (decLevels4 (.node κ) pL cw cbS tw) t = 79606 +
      cost (stepU4 (.node κ) pL (cw 4) (cbS 4) (msgT4 (.node κ) tw) 4) t +
      cost (stepU4 (.node κ) pL (cw 3) (cbS 3) (msgU4 (.node κ) 3) 3) t +
      cost (stepU4 (.node κ) pL (cw 2) (cbS 2) (msgU4 (.node κ) 2) 2) t +
      cost (stepU4 (.node κ) pL (cw 1) (cbS 1) (msgU4 (.node κ) 1) 1) t +
      cost (dec04 (.node κ) (cbS 0)) t + 5 := by
  simp only [decLevels4, cost, cost_wtabIR]
  ring

/-- The message steps' costs at a node kind. -/
theorem cost_msgT4 (κ : Rev4.NodeKind) (tw t : ℕ) :
    cost (msgT4 (.node κ) tw) t = 46 + 36 * 2 ^ (Snd.CKind.lv (.node κ) 4).logN + 48 * 2 ^ Snd.T4.mLog (.node κ) 4 := by
  obtain ⟨n1, n2, -⟩ := lvU4_nums κ (i := 4) (by norm_num) le_rfl
  rw [msgT4, cost_msgTIR _ _ _ _ _ t (by omega) (by omega)]

theorem cost_msgU4 (κ : Rev4.NodeKind) {i : ℕ} (hi1 : 1 ≤ i) (hi : i < 4) (t : ℕ) :
    cost (msgU4 (.node κ) i) t = 46 + 36 * 2 ^ (Snd.CKind.lv (.node κ) i).logN +
      560 * 2 ^ Snd.T4.mLog (.node κ) (i + 1) := by
  obtain ⟨n1, -⟩ := lvU4_nums κ hi1 (by omega)
  obtain ⟨-, m2, -⟩ := lvU4_nums κ (i := i + 1) (by omega) (by omega)
  rw [msgU4, cost_msgHIR _ _ _ _ _ t (by omega) (by omega)]

/-- **The five levels' exact cost**: `27,032,483,570,671 ≈ 2^44.6` at `N2` (`m = 31`) and
`108,050,868,885,470 ≈ 2^46.6` at `N4`, `N8` (`m = 32`), of which level 0 (rows `1 … 7`) is
`2.62·10^13` and `1.05·10^14` (Part 25's model at `C = 7`). -/
theorem cost_decLevels4 (pL : ℕ) (cw cbS : ℕ → ℕ) (tw t : ℕ) :
    cost (decLevels4 (.node .N2) pL cw cbS tw) t = 27032483570671 ∧
    cost (decLevels4 (.node .N4) pL cw cbS tw) t = 108050868885470 ∧
    cost (decLevels4 (.node .N8) pL cw cbS tw) t = 108050868885470 := by
  refine ⟨?_, ?_, ?_⟩ <;>
  · rw [cost_decLevels4_eq, cost_stepU4 _ _ (by norm_num) le_rfl, cost_stepU4 _ _ (by norm_num) (by norm_num),
      cost_stepU4 _ _ (by norm_num) (by norm_num), cost_stepU4 _ _ le_rfl (by norm_num), cost_dec04,
      cost_msgT4, cost_msgU4 _ (by norm_num) (by norm_num), cost_msgU4 _ (by norm_num) (by norm_num),
      cost_msgU4 _ le_rfl (by norm_num)]
    rfl

/-! ## Controls -/

/-- (+/−) **`KeepR4`** holds on the basis table, the chain's answers, level 0's word and the index,
and not on the decoded rows of either map nor on levels 1–4's word (the decode and the reads write
them). -/
theorem keepR4_ctl : KeepR4 map4.tb ∧ KeepR4 ansB ∧ KeepR4 map4.l0.cb ∧ KeepR4 memX4 ∧
    ¬ KeepR4 map4.lU.ob ∧ ¬ KeepR4 map4.l0.ob ∧ ¬ KeepR4 map4.lU.cb := by
  simp only [KeepR4, ansB]; decide

/-- (value) **The read takes the kind's height**: level 0's `sib` is 10 at `N2` (`m = 31`) and 11
at `N4` (`m = 32`); the cap depths are the same. -/
theorem readK4_ctl : (Snd.CKind.lv (.node .N2) 0).sib = 10 ∧ (Snd.CKind.lv (.node .N4) 0).sib = 11 ∧
    (Snd.CKind.lv (.node .N2) 0).cap = (Snd.CKind.lv (.node .N4) 0).cap := by decide

/-- (−) **The five levels depend on the kind's ladder**: `N2`'s program is not `N4`'s (their costs
differ), while (+) `N8`'s is `N4`'s (`decLevels4_m`). -/
theorem decLevels4_ctl (pL : ℕ) (cw cbS : ℕ → ℕ) (tw : ℕ) :
    decLevels4 (.node .N2) pL cw cbS tw ≠ decLevels4 (.node .N4) pL cw cbS tw ∧
    decLevels4 (.node .N8) pL cw cbS tw = decLevels4 (.node .N4) pL cw cbS tw := by
  refine ⟨fun h => ?_, decLevels4_m rfl pL cw cbS tw⟩
  have := congrArg (cost · 0) h
  simp only [(cost_decLevels4 pL cw cbS tw 0).1, (cost_decLevels4 pL cw cbS tw 0).2.1] at this
  exact absurd this (by decide)

end FR.X

end G6_FRXDec4Levels
