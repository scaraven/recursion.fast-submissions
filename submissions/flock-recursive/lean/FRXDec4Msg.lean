-- New for `flock-recursive` (BLUEPRINT revision 4.2, §6.2 step 4; stage S-H4, pass 4, item 1).
import FRXDec4Lv

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
