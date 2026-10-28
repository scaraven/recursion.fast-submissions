-- New for `flock-recursive` (BLUEPRINT §6.2 step 4, one level's decode composed; stage S-H2,
-- track L-ext).
import FRXMsg
import FRXAgree

/-!
# One level's decode on the machine

The decode of level `i` (BLUEPRINT §6.2 step 4) is

`eqtIR ; msg ; fwdIR ×2 ; flagIR ; scanIR ; baryIR k R ; bflyIR ×R`

on a fixed memory map (words; `k = 2^mLog`, `n = 2^logN`, `R` rows):

| region | base | size |
|---|---|---|
| basis table (`wtabIR`) | `tb0 = 2^20` | 800 |
| `J` (the scan's list) | `jb0 = 2^21` | `k` |
| flags | `fbF = 2^21 + 2^18` | `n` |
| `DJ`, `W`, `E` | `djb0`, `wb0`, `eb0` | `2k` each |
| decoded rows, levels 1–4 | `obL = 2^22 + 2^21` | `2kR` |
| chain answers | `chB … chEnd` | (read) |
| `eq` table | `eqB = 2^23 + 2^15` | `4·2^ℓ` |
| `X`, `Y` (the next message, then `Enc`) | `xbM = 2^23 + 2^16`, `ybM = xbM + 2^19` | `2n` each |
| the word `W⁽ⁱ⁾` | `stB` (levels 1–4), `colBase` (level 0) | (read) |

* `bfRowsIR`: the butterflies on each of the `R` decoded rows (unrolled; `bfRows_sem`);
* `decFrontIR` (`eqtIR ; msg ; fwdIR ×2 ; flagIR`), `decFront_sem`: the flags mark `A_c`;
* `decBackIR` (`scanIR ; baryIR ; bfRowsIR`), `decBack_sem`: the rows are `msgOf` (`level_decode`);
* **`decLv_sem`**: one level, `decLvU_sem` (levels 1–4, the word at `stB`, the rows at `obL`) and
  `decLv0_sem` (level 0, the word at `colBase`, the rows at `ob0`);
* `MsgOk`: what the message step owes; `msgOk_four` (level 4, from π's tape and the chain link
  `finalAt = finPi`), `msgOk_lower` (levels 0–3, from the next level's decoded rows).
-/

namespace FR.X

open RecursionFast FR Finset

/-! ## The butterflies on the rows -/

/-- `rA0 := b`. -/
def setA (b : ℕ) : XIR := .blk [.const rA0 (toWord b)]

/-- **The butterflies on rows `0 … R − 1`** (row `c` of `2^m` entries at `ob + 2·2^m·c`). -/
def bfRowsIR (m ob tb : ℕ) : ℕ → XIR
  | 0 => .blk []
  | R + 1 => .seq (bfRowsIR m ob tb R) (.seq (setA (ob + 2 * 2 ^ m * R)) (bflyIR m tb))

theorem wf_bfRowsIR (m ob tb : ℕ) : ∀ R, WF (bfRowsIR m ob tb R)
  | 0 => by simp [bfRowsIR, WF]
  | R + 1 => ⟨wf_bfRowsIR m ob tb R, by simp [setA, WF, Prim.dst, rA0], wf_bflyIR m tb⟩

theorem noLoopT_bfRowsIR (m ob tb : ℕ) : ∀ R, NoLoopT (bfRowsIR m ob tb R)
  | 0 => by simp [bfRowsIR, NoLoopT]
  | R + 1 => ⟨noLoopT_bfRowsIR m ob tb R, by simp [setA, NoLoopT], noLoopT_bflyIR m tb⟩

theorem outs_bfRowsIR (m ob tb t : ℕ) : ∀ R, outs (bfRowsIR m ob tb R) t = 0
  | 0 => by simp [bfRowsIR, outs]
  | R + 1 => by simp [bfRowsIR, outs, outs_bfRowsIR m ob tb t R, setA, outs_bflyIR]

theorem cost_bfRowsIR (m ob tb t : ℕ) (hm : 2 ^ (m - 1) < 2 ^ 64) (hm' : m < 2 ^ 64) :
    ∀ R, cost (bfRowsIR m ob tb R) t = 1 + R * (17 + m * (741 * 2 ^ (m - 1) + 23))
  | 0 => by simp [bfRowsIR, cost, blkSteps]
  | R + 1 => by
    simp only [bfRowsIR, cost, cost_bfRowsIR m ob tb t hm hm' R, setA, blkSteps, List.length_cons,
      List.length_nil, cost_bflyIR m tb t hm hm']
    norm_num; ring

theorem setA_sem (I : Array Word) (s : St) (hM : Inv s.M) (b : ℕ) :
    rd (semXIR I (setA b) s).M rA0 = toWord b ∧
    (∀ x, regs ≤ x → rd (semXIR I (setA b) s).M x = rd s.M x) ∧ Inv (semXIR I (setA b) s).M := by
  have hs := hM.1
  simp only [regs] at hs
  refine ⟨?_, hframe I (setA b) s (by simp [setA, Lo, Prim.dst, rA0, regs]),
    inv_sem I (by simp [setA, WF, Prim.dst, rA0]) hM⟩
  simp only [setA, semXIR, runPrims, List.foldl, Prim.run]
  exact rd_set_self (by simp only [rA0]; omega)

/-- **The butterflies on the rows**: with row `c < R` holding `Y c` (`2^m` entries at
`ob + 2·2^m·c`) and the basis table at `tb`, `bfRowsIR m ob tb R` leaves `bflyRun … (Y c)` in
each row and keeps the heap outside `[ob, ob + 2·2^m·R)`. -/
theorem bfRows_sem (I : Array Word) {m ob tb : ℕ} (hm1 : 1 ≤ m) (hm : m ≤ 20) (hob : regs ≤ ob)
    (htb : regs ≤ tb) (htb2 : tb + 800 < 2 ^ 64) {Y : ℕ → ℕ → F} :
    ∀ R (s : St), Inv s.M → ob + 2 * 2 ^ m * R + 1 < 2 ^ 64 → ob + 2 * 2 ^ m * R ≤ s.M.size →
      (tb + 800 ≤ ob ∨ ob + 2 * 2 ^ m * R ≤ tb) →
      (∀ v < 20, ∀ i < 20, rdF s.M (tb + 40 * v + 2 * i) = (wRow D logNMax v).getD i 0) →
      (∀ c < R, ∀ x < 2 ^ m, rdF s.M (ob + 2 * 2 ^ m * c + 2 * x) = Y c x) →
      (∀ c < R, ∀ x < 2 ^ m, rdF (semXIR I (bfRowsIR m ob tb R) s).M (ob + 2 * 2 ^ m * c + 2 * x) =
        bflyRun (M := F) D logNMax 0 m (Y c) x) ∧
      (∀ y, regs ≤ y → (y < ob ∨ ob + 2 * 2 ^ m * R ≤ y) →
        rd (semXIR I (bfRowsIR m ob tb R) s).M y = rd s.M y) ∧
      Inv (semXIR I (bfRowsIR m ob tb R) s).M
  | 0, s, hM, _, _, _, _, _ => ⟨fun c hc => absurd hc (Nat.not_lt_zero _), fun _ _ _ => rfl, hM⟩
  | R + 1, s, hM, h2, hsz, hd, hW, hY => by
    have hs := hM.1
    simp only [regs] at hs hob htb
    have hR : 2 * 2 ^ m * R + 2 * 2 ^ m = 2 * 2 ^ m * (R + 1) := by ring
    obtain ⟨a1, a2, hM1⟩ := bfRows_sem I hm1 hm (by simp only [regs]; omega)
      (by simp only [regs]; omega) htb2 R s hM (by omega) (by omega) (by omega) hW
      (fun c hc x hx => hY c (by omega) x hx)
    rw [bfRowsIR, semXIR_seq, semXIR_seq]
    have z1 := size_sem I (bfRowsIR m ob tb R) s
    generalize semXIR I (bfRowsIR m ob tb R) s = s1 at a1 a2 hM1 z1
    obtain ⟨b1, b2, hM2⟩ := setA_sem I s1 hM1 (ob + 2 * 2 ^ m * R)
    have z2 := size_sem I (setA (ob + 2 * 2 ^ m * R)) s1
    generalize semXIR I (setA (ob + 2 * 2 ^ m * R)) s1 = s2 at b1 b2 hM2 z2
    have h2s : ∀ y, regs ≤ y → (y < ob + 2 * 2 ^ m * R ∨ ob + 2 * 2 ^ m * (R + 1) ≤ y) →
        rd s2.M y = rd s1.M y := fun y hy _ => b2 y hy
    have hW2 : ∀ v < 20, ∀ i < 20, rdF s2.M (tb + 40 * v + 2 * i) = (wRow D logNMax v).getD i 0 :=
      fun v hv i hi => by
        rw [← hW v hv i hi]
        exact rdF_eq ((b2 _ (by simp only [regs]; omega)).trans
            (a2 _ (by simp only [regs]; omega) (by omega)))
          ((b2 _ (by simp only [regs]; omega)).trans (a2 _ (by simp only [regs]; omega) (by omega)))
    have hY2 : ∀ x < 2 ^ m, rdF s2.M (ob + 2 * 2 ^ m * R + 2 * x) = Y R x := fun x hx => by
      rw [← hY R (by omega) x hx]
      exact rdF_eq ((b2 _ (by simp only [regs]; omega)).trans
          (a2 _ (by simp only [regs]; omega) (by omega)))
        ((b2 _ (by simp only [regs]; omega)).trans (a2 _ (by simp only [regs]; omega) (by omega)))
    obtain ⟨c1, c2, hM3⟩ := bflyIR_sem I s2 hM2 (A := ob + 2 * 2 ^ m * R) (tb := tb) (ℓ := m)
      (Y := Y R) hm1 hm (by simp only [regs]; omega) (by omega) (by omega)
      (by simp only [regs]; omega) htb2 (by omega) b1 hW2 hY2
    refine ⟨fun c hc x hx => ?_, fun y hy hy2 => ?_, hM3⟩
    · rcases Nat.lt_succ_iff_lt_or_eq.mp hc with h | rfl
      · rw [← a1 c h x hx]
        have hcx : 2 * 2 ^ m * c + 2 * 2 ^ m ≤ 2 * 2 ^ m * R := by
          rw [← Nat.mul_succ]; exact Nat.mul_le_mul_left _ h
        exact rdF_eq ((c2 _ (by simp only [regs]; omega) (by omega)).trans
            (b2 _ (by simp only [regs]; omega)))
          ((c2 _ (by simp only [regs]; omega) (by omega)).trans (b2 _ (by simp only [regs]; omega)))
      · exact c1 x hx
    · rw [c2 y hy (by omega), b2 y hy, a2 y hy (by omega)]

/-! ## The memory map -/

/-- The flags (`2^21 + 2^18`). -/ def fbF : ℕ := 2359296
/-- The decoded rows of levels 1–4 (`2^22 + 2^21`). -/ def obL : ℕ := 6291456
/-- The `eq` table (`2^23 + 2^15`). -/ def eqB : ℕ := 8421376
/-- `X` (`2^23 + 2^16`). -/ def xbM : ℕ := 8454144
/-- `Y` (`xbM + 2^19`). -/ def ybM : ℕ := 8978432

/-! ## The back half: the scan, the interpolation, the butterflies -/

/-- **The back half** of a level: the first `k` flagged positions to `J`, the interpolation of the
`R` rows of the word (at `cb + cs·j + 2r`) to `ob`, the butterflies on each row. -/
def decBackIR (n m R cs cb ob : ℕ) : XIR :=
  .seq (scanIR n (2 ^ m) fbF jb0)
    (.seq (baryIR (2 ^ m) R jb0 djb0 wb0 eb0 cb cs ob tb0) (bfRowsIR m ob tb0 R))

open FR.Snd in
/-- **The back half decodes** (`level_decode`): if the flags at `fbF` mark `A_c`, the word of
level `i` sits at `cb + cs·j + 2r`, the word is close and `A_c = jointAgree` (what `final` hands
over), then row `r` at `ob + 2kr` holds the `F` values of S-G's `msgOf (i) r`. -/
theorem decBack_sem (I : Array Word) (s : St) (hM : Inv s.M) {L es : Log} {i cs cb ob : ℕ}
    (hi : i < 5) (hfar : ¬ farL .N30 L es i)
    (hA : consSet .N30 L es i = jointAgree (wordK .N30 L es i) (decodeL .N30 L es i))
    (hsz : memX ≤ s.M.size)
    (hL : BaryLay (2 ^ mLog .N30 i) (lvl .N30 i).rows jb0 djb0 wb0 eb0 cb ob tb0)
    (hcb : cb + 128 * 2 ^ 20 + 256 < 2 ^ 64) (hcs : cs ≤ 128) (hob : ob + 2 * 2 ^ mLog .N30 i * (lvl .N30 i).rows ≤ memX)
    (hT : ∀ v < 20, ∀ i < 20, rdF s.M (tb0 + 40 * v + 2 * i) = (wRow D logNMax v).getD i 0)
    (hW : ∀ j (hj : j < 2 ^ (lvl .N30 i).logN) (r : Fin (lvl .N30 i).rows),
      rdF s.M (cb + cs * j + 2 * r) = wordOf .N30 L es i r ⟨j, hj⟩)
    (hF : ∀ j < 2 ^ (lvl .N30 i).logN, (j ∈ consN .N30 L es i ↔ rd s.M (fbF + j) ≠ 0)) :
    (∀ r < (lvl .N30 i).rows, ∀ x < 2 ^ mLog .N30 i,
      algebraMap F K (rdF (semXIR I (decBackIR (2 ^ (lvl .N30 i).logN) (mLog .N30 i)
        (lvl .N30 i).rows cs cb ob) s).M (ob + 2 * 2 ^ mLog .N30 i * r + 2 * x)) =
      msgOf .N30 L es i r x) ∧
    (∀ y, regs ≤ y → (y < jb0 ∨ (jb0 + 2 ^ mLog .N30 i ≤ y ∧ y < djb0) ∨
        (eb0 + 2 * 2 ^ mLog .N30 i ≤ y ∧ y < ob) ∨ ob + 2 * 2 ^ mLog .N30 i * (lvl .N30 i).rows ≤ y) →
      rd (semXIR I (decBackIR (2 ^ (lvl .N30 i).logN) (mLog .N30 i)
        (lvl .N30 i).rows cs cb ob) s).M y = rd s.M y) ∧
    Inv (semXIR I (decBackIR (2 ^ (lvl .N30 i).logN) (mLog .N30 i)
        (lvl .N30 i).rows cs cb ob) s).M := by
  classical
  obtain ⟨htb, htj, hjd, hdw, hwe, heo, hoc⟩ := hL
  have hs := hM.1
  simp only [regs] at hs htb
  have hm1 : 1 ≤ mLog .N30 i := by interval_cases i <;> decide
  have hm20 : mLog .N30 i ≤ 17 := by interval_cases i <;> decide
  have hn18 : (lvl .N30 i).logN ≤ 18 := by interval_cases i <;> decide
  have hmn : mLog .N30 i ≤ (lvl .N30 i).logN := by interval_cases i <;> decide
  have hR64 : (lvl .N30 i).rows ≤ 64 := by interval_cases i <;> decide
  have hP : 2 ^ (lvl .N30 i).logN ≤ 2 ^ 18 := Nat.pow_le_pow_right (by norm_num) hn18
  have hPm : 2 ^ mLog .N30 i ≤ 2 ^ (lvl .N30 i).logN := Nat.pow_le_pow_right (by norm_num) hmn
  have hmem : memX = 67108864 := rfl
  have etb : tb0 = 1048576 := rfl
  have ejb : jb0 = 2097152 := rfl
  have edj : djb0 = 4194304 := rfl
  have ewb : wb0 = 4718592 := rfl
  have eeb : eb0 = 5242880 := rfl
  have efb : fbF = 2359296 := rfl
  have enM : nMax = 1048576 := rfl
  -- the agreement set is large enough
  have hcard : (2 ^ mLog .N30 i) ≤ (consN .N30 L es i).card := by
    obtain ⟨-, -, -, hk', hn'⟩ := lv_params .N30 hi
    obtain ⟨-, hJ⟩ := decodeL_spec hfar
    rw [consN, card_map, hA]
    have : lvK .N30 i ≤ 2 ^ (lvl .N30 i).logN - lvE .N30 i := by
      rw [← hn']; obtain ⟨h1, -⟩ := lv_params .N30 hi; omega
    rw [← hk']; exact this.trans hJ
  -- the scan
  rw [decBackIR, semXIR_seq]
  obtain ⟨a1, a2, a3, hM1⟩ := scanIR_sem I s hM (n := 2 ^ (lvl .N30 i).logN) (k := 2 ^ mLog .N30 i) (fb := fbF) (lb := jb0)
    (f := fun j => rd s.M (fbF + j)) (by simp only [regs, jb0]; omega)
    (by simp only [jb0]; omega) (by simp only [jb0, memX] at *; omega)
    (by simp only [regs, fbF]; omega) (by simp only [fbF]; omega) (by omega)
    (.inr (by simp only [jb0, fbF]; omega)) (fun j _ => rfl)
  have z1 := size_sem I (scanIR (2 ^ (lvl .N30 i).logN) (2 ^ mLog .N30 i) fbF jb0) s
  generalize semXIR I (scanIR (2 ^ (lvl .N30 i).logN) (2 ^ mLog .N30 i) fbF jb0) s = s1 at a1 a2 a3 hM1 z1
  have hA' : ∀ j < (2 ^ (lvl .N30 i).logN), j ∈ consN .N30 L es i ↔ rd s.M (fbF + j) ≠ 0 := hF
  obtain ⟨SL, hSL⟩ : ∃ SL, SL = scanL (2 ^ (lvl .N30 i).logN) fun j => rd s.M (fbF + j) := ⟨_, rfl⟩
  rw [← hSL] at a1 a2
  obtain ⟨Jl, hJl⟩ : ∃ Jl, Jl = SL.take (2 ^ mLog .N30 i) := ⟨_, rfl⟩
  have hfk : firstK (2 ^ (lvl .N30 i).logN) (consN .N30 L es i) (2 ^ mLog .N30 i) = Jl.toFinset := by
    rw [hJl, hSL]; exact firstK_scan hA'
  have hlen : Jl.length = 2 ^ mLog .N30 i := by
    have h1 := firstK_card (n := 2 ^ (lvl .N30 i).logN) (A := consN .N30 L es i)
      (fun j hj => (mem_consN.1 hj).1) hcard
    rw [hfk] at h1
    have h2 := List.toFinset_card_le Jl
    have h3 : Jl.length ≤ 2 ^ mLog .N30 i := by rw [hJl]; exact List.length_take_le _ _
    omega
  have hlen0 : 2 ^ mLog .N30 i ≤ SL.length := by
    have := List.length_take_le' (2 ^ mLog .N30 i) SL
    rw [← hJl] at this; omega
  have hmin : min SL.length (2 ^ mLog .N30 i) = 2 ^ mLog .N30 i := by omega
  have hnd : Jl.Nodup := by
    rw [hJl, hSL]
    exact List.Nodup.sublist (List.take_sublist _ _) (List.Nodup.filter _ List.nodup_range)
  have hJmem : ∀ j ∈ Jl, j < 2 ^ (lvl .N30 i).logN := fun j hj => by
    rw [hJl, hSL] at hj
    have := List.mem_of_mem_take hj
    simp only [scanL, List.mem_filter, List.mem_range] at this
    exact this.1
  have hJ1 : ∀ t < Jl.length, rd s1.M (jb0 + t) = toWord (Jl.getD t 0) := fun t ht => by
    rw [a2 t (by omega), hJl, List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD,
      List.getElem?_take_of_lt (by omega)]
  have k1 : ∀ y, regs ≤ y → (y < jb0 ∨ jb0 + (2 ^ mLog .N30 i) ≤ y) → rd s1.M y = rd s.M y := a3
  -- the interpolation
  rw [semXIR_seq]
  have hL' : BaryLay Jl.length (lvl .N30 i).rows jb0 djb0 wb0 eb0 cb ob tb0 := by
    rw [hlen]; exact ⟨by simp only [regs]; omega, htj, hjd, hdw, hwe, heo, hoc⟩
  have hT1 : ∀ v < 20, ∀ i' < 20, rdF s1.M (tb0 + 40 * v + 2 * i') = (wRow D logNMax v).getD i' 0 :=
    fun v hv i' hi' => by
      rw [← hT v hv i' hi']
      exact rdF_eq (k1 _ (by simp only [regs]; omega) (.inl (by omega)))
        (k1 _ (by simp only [regs]; omega) (.inl (by omega)))
  have hb := baryIR_interp I s1 hM1 (C := (lvl .N30 i).rows) (cs := cs) hL' hnd
    (fun j hj => lt_of_lt_of_le (hJmem j hj) (by omega)) (by rw [hlen]; omega)
    (by omega) (by omega) (fun j hj c hc => by
      have : cs * j ≤ 128 * 2 ^ 20 := Nat.mul_le_mul hcs (by omega)
      omega)
    (by rw [hlen]; omega) (fun i' hi' => by simpa using hT1 0 (by norm_num) i' hi') hJ1
  rw [hlen] at hb
  obtain ⟨-, b2, hM2⟩ := baryIR_sem I s1 hM1 (Jl := Jl) (C := (lvl .N30 i).rows) (cs := cs) hL'
    (by rw [hlen]; omega) (by omega) (by omega) (fun j hj c hc => by
      have : cs * j ≤ 128 * 2 ^ 20 := Nat.mul_le_mul hcs (by omega)
      omega) (by rw [hlen]; omega)
    (fun t ht => lt_of_lt_of_le (hJmem _ (by rw [List.getD_eq_getElem _ _ ht]; exact List.getElem_mem ht))
      (by omega))
    (fun i' hi' => by simpa using hT1 0 (by norm_num) i' hi') hJ1
  rw [hlen] at b2 hM2
  have z2 := size_sem I (baryIR Jl.length (lvl .N30 i).rows jb0 djb0 wb0 eb0 cb cs ob tb0) s1
  rw [hlen] at z2
  generalize semXIR I (baryIR (2 ^ mLog .N30 i) (lvl .N30 i).rows jb0 djb0 wb0 eb0 cb cs ob tb0) s1 = s2 at hb b2 hM2 z2
  -- the butterflies
  have hT2 : ∀ v < 20, ∀ i' < 20, rdF s2.M (tb0 + 40 * v + 2 * i') = (wRow D logNMax v).getD i' 0 :=
    fun v hv i' hi' => by
      rw [← hT1 v hv i' hi']
      exact rdF_eq (b2 _ (by simp only [regs]; omega) (.inl (by omega)) (.inl (by omega)))
        (b2 _ (by simp only [regs]; omega) (.inl (by omega)) (.inl (by omega)))
  obtain ⟨c1, c2, hM3⟩ := bfRows_sem I (m := mLog .N30 i) (ob := ob) (tb := tb0)
    (Y := fun c => interpF D Jl.toFinset (fun j => rdF s1.M (cb + cs * j + 2 * c))) hm1
    (by omega) (by simp only [regs]; omega) (by simp only [regs]; omega) (by simp only [tb0]; omega)
    (lvl .N30 i).rows s2 hM2 (by rw [hmem] at hob; omega) (by rw [z2, z1]; exact hob.trans hsz)
    (.inl ((show tb0 + 800 ≤ eb0 by decide).trans ((Nat.le_add_right _ _).trans heo))) hT2
    (fun c hc x hx => hb x hx c hc)
  refine ⟨fun r hr x hx => ?_, fun y hy hy2 => ?_, hM3⟩
  · rw [c1 r hr x hx]
    have e : (fun j => rdF s1.M (cb + cs * j + 2 * r)) = fun j => rdF s1.M (cb + cs * j + 2 * r) := rfl
    have hY : interpF D Jl.toFinset (fun j => rdF s1.M (cb + cs * j + 2 * r)) =
        interpF D (firstK (2 ^ (lvl .N30 i).logN) (consN .N30 L es i) (2 ^ mLog .N30 i))
          (wordN .N30 L es i ⟨r, hr⟩) := by
      funext x'
      rw [hfk]
      refine interpF_congr D _ (fun j hj => ?_) x'
      have hjn := hJmem j (List.mem_toFinset.1 hj)
      have hc : cs * j ≤ cs * (2 ^ (lvl .N30 i).logN) := Nat.mul_le_mul_left _ hjn.le
      rw [rdF_eq (k1 _ (by simp only [regs]; omega) (.inr (by omega)))
        (k1 _ (by simp only [regs]; omega) (.inr (by omega))), hW j hjn ⟨r, hr⟩]
      simp only [wordN, hjn, dite_true]
    rw [hY]
    exact level_decode hi hfar hA ⟨r, hr⟩ ⟨x, hx⟩
  · rw [c2 y hy (by omega), b2 y hy (by omega) (by omega), k1 y hy (by omega)]

/-! ## The front half: the `eq` table, the next message, `Enc`, the flags -/

/-- **The front half** of a level: the `eq` table of the `ℓ` challenges at `cbS`, the next
message's rows (`msg`), `Enc` of each row (`n = log₂` of the positions), the flags. -/
def decFrontIR (msg : XIR) (ℓ n R cs cb cbS : ℕ) : XIR :=
  .seq (eqtIR ℓ cbS eqB) (.seq msg (.seq (setA xbM) (.seq (fwdIR n tb0) (.seq (setA ybM)
    (.seq (fwdIR n tb0) (flagIR (2 ^ n) R cs cb eqB xbM ybM fbF))))))

/-- What the message step of a level provides (`msgH_next`, `msg4_next`): from every state
that agrees with `s` on the heap outside the `eq` table, `msg` writes the next message's
coordinate rows at `xbM` and `ybM`, zero-padded, and keeps the heap outside `[xbM, ybM + 2^19)`. -/
def MsgOk (I : Array Word) (msg : XIR) (s : St) (n m : ℕ) (g : ℕ → K) : Prop :=
  ∀ s' : St, Inv s'.M → s'.M.size = s.M.size →
    (∀ y, regs ≤ y → (y < eqB ∨ eqB + 256 ≤ y) → rd s'.M y = rd s.M y) →
    (∀ j < 2 ^ n, rdF (semXIR I msg s').M (xbM + 2 * j) = (if j < 2 ^ m then (g j).f₀ else 0) ∧
      rdF (semXIR I msg s').M (ybM + 2 * j) = (if j < 2 ^ m then (g j).f₁ else 0)) ∧
    (∀ y, regs ≤ y → (y < xbM ∨ ybM + 2 ^ 19 ≤ y) → rd (semXIR I msg s').M y = rd s'.M y) ∧
    Inv (semXIR I msg s').M

open FR.Snd in
/-- **The front half marks `A_c`** (`flagV_consSet`): with the basis table at `tb0`, the word
of level `i` at `cb + cs·j + 2r` (above `2^24`), P1.i's challenges at `cbS`, and a message step
that lays out `nextMsg i`, the flag at `fbF + j` is nonzero iff `j ∈ A_c`. -/
theorem decFront_sem (I : Array Word) (s : St) (hM : Inv s.M) {L es : Log} {i cs cb cbS : ℕ}
    {msg : XIR} (hi : i < 5) (hsz : memX ≤ s.M.size) (hcs : 2 * (lvl .N30 i).rows ≤ cs)
    (hcb : 2 ^ 24 ≤ cb) (hcb2 : cb + cs * 2 ^ (lvl .N30 i).logN + 2 < 2 ^ 64)
    (hcS : regs ≤ cbS) (hcS2 : cbS + 8 * (lvl .N30 i).ell + 4 ≤ eqB)
    (hT : ∀ v < 20, ∀ i < 20, rdF s.M (tb0 + 40 * v + 2 * i) = (wRow D logNMax v).getD i 0)
    (hW : ∀ j (hj : j < 2 ^ (lvl .N30 i).logN) (r : Fin (lvl .N30 i).rows),
      rdF s.M (cb + cs * j + 2 * r) = wordOf .N30 L es i r ⟨j, hj⟩)
    (hS : ∀ v < (lvl .N30 i).ell, rdK s.M (cbS + 8 * v) = sAt es i v)
    (hmsg : MsgOk I msg (semXIR I (eqtIR (lvl .N30 i).ell cbS eqB) s) (lvl .N30 i).logN
      (mLog .N30 i) (nextMsg .N30 L es i)) :
    (∀ j < 2 ^ (lvl .N30 i).logN, (j ∈ consN .N30 L es i ↔
      rd (semXIR I (decFrontIR msg (lvl .N30 i).ell (lvl .N30 i).logN (lvl .N30 i).rows cs cb cbS)
        s).M (fbF + j) ≠ 0)) ∧
    (∀ y, regs ≤ y → (y < fbF ∨ (fbF + 2 ^ 18 ≤ y ∧ y < eqB) ∨ 2 ^ 24 ≤ y) →
      rd (semXIR I (decFrontIR msg (lvl .N30 i).ell (lvl .N30 i).logN (lvl .N30 i).rows cs cb cbS)
        s).M y = rd s.M y) ∧
    Inv (semXIR I (decFrontIR msg (lvl .N30 i).ell (lvl .N30 i).logN (lvl .N30 i).rows cs cb cbS)
        s).M := by
  have hs := hM.1
  simp only [regs] at hs hcS
  have hl6 : (lvl .N30 i).ell ≤ 6 := by interval_cases i <;> decide
  have hn1 : 1 ≤ (lvl .N30 i).logN := by interval_cases i <;> decide
  have hn18 : (lvl .N30 i).logN ≤ 18 := by interval_cases i <;> decide
  have hmn : mLog .N30 i ≤ (lvl .N30 i).logN := by interval_cases i <;> decide
  have hRe : (lvl .N30 i).rows = 2 ^ (lvl .N30 i).ell := rfl
  have hP : 2 ^ (lvl .N30 i).logN ≤ 2 ^ 18 := Nat.pow_le_pow_right (by norm_num) hn18
  have hPl : 2 ^ (lvl .N30 i).ell ≤ 2 ^ 6 := Nat.pow_le_pow_right (by norm_num) hl6
  have hmem : memX = 67108864 := rfl
  have etb : tb0 = 1048576 := rfl
  have efb : fbF = 2359296 := rfl
  have eqb : eqB = 8421376 := rfl
  have exb : xbM = 8454144 := rfl
  have eyb : ybM = 8978432 := rfl
  have dX : tb0 + 800 ≤ xbM := by decide
  have dY : tb0 + 800 ≤ ybM := by decide
  -- the `eq` table
  rw [decFrontIR, semXIR_seq]
  obtain ⟨e1, e2, hM1⟩ := eqtIR_sem I s hM (ℓ := (lvl .N30 i).ell) (cb := cbS) (eb := eqB)
    (S := sAt es i) (by omega) (by simp only [regs]; omega) (by omega) (by simp only [regs]; omega)
    (by omega) (by omega) (.inl (by omega)) hS
  have z1 := size_sem I (eqtIR (lvl .N30 i).ell cbS eqB) s
  have h256 : 4 * 2 ^ (lvl .N30 i).ell ≤ 256 := by
    have := Nat.mul_le_mul_left 4 hPl; simpa using this
  have e2' : ∀ y, regs ≤ y → (y < eqB ∨ eqB + 256 ≤ y) →
      rd (semXIR I (eqtIR (lvl .N30 i).ell cbS eqB) s).M y = rd s.M y := fun y hy h =>
    e2 y hy (h.imp_right fun h' => le_trans (Nat.add_le_add_left h256 _) h')
  have hmsg' := hmsg
  generalize semXIR I (eqtIR (lvl .N30 i).ell cbS eqB) s = s1 at e1 e2' hM1 z1 hmsg'
  clear e2
  -- the message
  rw [semXIR_seq]
  obtain ⟨m1, m2, hM2⟩ := hmsg' s1 hM1 rfl fun y _ _ => rfl
  have z2 := size_sem I msg s1
  generalize semXIR I msg s1 = s2 at m1 m2 hM2 z2
  -- `Enc` of `X`
  rw [semXIR_seq, semXIR_seq]
  obtain ⟨a1, a2, hM3⟩ := setA_sem I s2 hM2 xbM
  have z3 := size_sem I (setA xbM) s2
  generalize semXIR I (setA xbM) s2 = s3 at a1 a2 hM3 z3
  have h31 : ∀ y, regs ≤ y → (y < xbM ∨ ybM + 2 ^ 19 ≤ y) → (y < eqB ∨ eqB + 256 ≤ y) →
      rd s3.M y = rd s.M y := fun y hy h1 h2 => by rw [a2 y hy, m2 y hy h1, e2' y hy h2]
  have hT3 : ∀ v < 20, ∀ i' < 20, rdF s3.M (tb0 + 40 * v + 2 * i') = (wRow D logNMax v).getD i' 0 :=
    fun v hv i' hi' => by
      rw [← hT v hv i' hi']
      exact rdF_eq (h31 _ (by simp only [regs]; omega) (.inl (by omega)) (.inl (by omega)))
        (h31 _ (by simp only [regs]; omega) (.inl (by omega)) (.inl (by omega)))
  have hX3 : ∀ j < 2 ^ (lvl .N30 i).logN, rdF s3.M (xbM + 2 * j) =
      if h : j < 2 ^ mLog .N30 i then (fun x : Fin (2 ^ mLog .N30 i) => (nextMsg .N30 L es i x).f₀) ⟨j, h⟩
      else 0 := fun j hj => by
    rw [rdF_eq (a2 _ (by simp only [regs]; omega)) (a2 _ (by simp only [regs]; omega)), (m1 j hj).1]
    by_cases h : j < 2 ^ mLog .N30 i
    · rw [if_pos h, dif_pos h]
    · rw [if_neg h, dif_neg h]
  have f1 := fwdIR_enc I s3 hM3 (A := xbM) (tb := tb0) hn1 (by omega) hmn
    (by simp only [regs]; omega) (by omega) (by omega) (by simp only [regs]; omega)
    (by omega) (.inl dX) a1 hT3
    (fun x : Fin (2 ^ mLog .N30 i) => (nextMsg .N30 L es i x).f₀) hX3
  obtain ⟨-, f2, hM4⟩ := fwdIR_sem I s3 hM3 (A := xbM) (tb := tb0) hn1 (by omega)
    (by simp only [regs]; omega) (by omega) (by omega) (by simp only [regs]; omega)
    (by omega) (.inl dX) a1 hT3 (Y := fun j => if h : j < 2 ^ mLog .N30 i then
      (fun x : Fin (2 ^ mLog .N30 i) => (nextMsg .N30 L es i x).f₀) ⟨j, h⟩ else 0) hX3
  have z4 := size_sem I (fwdIR (lvl .N30 i).logN tb0) s3
  generalize semXIR I (fwdIR (lvl .N30 i).logN tb0) s3 = s4 at f1 f2 hM4 z4
  -- `Enc` of `Y`
  rw [semXIR_seq, semXIR_seq]
  obtain ⟨b1, b2, hM5⟩ := setA_sem I s4 hM4 ybM
  have z5 := size_sem I (setA ybM) s4
  generalize semXIR I (setA ybM) s4 = s5 at b1 b2 hM5 z5
  have hT5 : ∀ v < 20, ∀ i' < 20, rdF s5.M (tb0 + 40 * v + 2 * i') = (wRow D logNMax v).getD i' 0 :=
    fun v hv i' hi' => by
      rw [← hT3 v hv i' hi']
      exact rdF_eq ((b2 _ (by simp only [regs]; omega)).trans
          (f2 _ (by simp only [regs]; omega) (.inl (by omega))))
        ((b2 _ (by simp only [regs]; omega)).trans (f2 _ (by simp only [regs]; omega) (.inl (by omega))))
  have hY5 : ∀ j < 2 ^ (lvl .N30 i).logN, rdF s5.M (ybM + 2 * j) =
      if h : j < 2 ^ mLog .N30 i then (fun x : Fin (2 ^ mLog .N30 i) => (nextMsg .N30 L es i x).f₁) ⟨j, h⟩
      else 0 := fun j hj => by
    rw [rdF_eq ((b2 _ (by simp only [regs]; omega)).trans
        (f2 _ (by simp only [regs]; omega) (.inr (by omega))))
      ((b2 _ (by simp only [regs]; omega)).trans (f2 _ (by simp only [regs]; omega) (.inr (by omega)))),
      rdF_eq (a2 _ (by simp only [regs]; omega)) (a2 _ (by simp only [regs]; omega)), (m1 j hj).2]
    by_cases h : j < 2 ^ mLog .N30 i
    · rw [if_pos h, dif_pos h]
    · rw [if_neg h, dif_neg h]
  have g1 := fwdIR_enc I s5 hM5 (A := ybM) (tb := tb0) hn1 (by omega) hmn
    (by simp only [regs]; omega) (by omega) (by omega) (by simp only [regs]; omega)
    (by omega) (.inl dY) b1 hT5
    (fun x : Fin (2 ^ mLog .N30 i) => (nextMsg .N30 L es i x).f₁) hY5
  obtain ⟨-, g2, hM6⟩ := fwdIR_sem I s5 hM5 (A := ybM) (tb := tb0) hn1 (by omega)
    (by simp only [regs]; omega) (by omega) (by omega) (by simp only [regs]; omega)
    (by omega) (.inl dY) b1 hT5 (Y := fun j => if h : j < 2 ^ mLog .N30 i then
      (fun x : Fin (2 ^ mLog .N30 i) => (nextMsg .N30 L es i x).f₁) ⟨j, h⟩ else 0) hY5
  have z6 := size_sem I (fwdIR (lvl .N30 i).logN tb0) s5
  generalize semXIR I (fwdIR (lvl .N30 i).logN tb0) s5 = s6 at g1 g2 hM6 z6
  -- the heap of `s6`
  have h6 : ∀ y, regs ≤ y → (y < xbM ∨ ybM + 2 ^ 19 ≤ y) →
      (y < eqB ∨ eqB + 256 ≤ y) → rd s6.M y = rd s.M y := fun y hy h1 h2 => by
    rw [g2 y hy (by omega), b2 y hy, f2 y hy (by omega), h31 y hy h1 h2]
  have hb6 : ∀ y, cb ≤ y → rd s6.M y = rd s.M y := fun y hy =>
    h6 y ((show regs ≤ 2 ^ 24 by decide).trans (hcb.trans hy))
      (.inr ((show ybM + 2 ^ 19 ≤ 2 ^ 24 by decide).trans (hcb.trans hy)))
      (.inr ((show eqB + 256 ≤ 2 ^ 24 by decide).trans (hcb.trans hy)))
  have hW6 : ∀ j (hj : j < 2 ^ (lvl .N30 i).logN) (r : Fin (lvl .N30 i).rows),
      rdF s6.M (cb + cs * j + 2 * r) = wordOf .N30 L es i r ⟨j, hj⟩ := fun j hj r => by
    rw [← hW j hj r]
    have l1 : cb ≤ cb + cs * j + 2 * r := (Nat.le_add_right cb _).trans (Nat.le_add_right _ _)
    exact rdF_eq (hb6 _ l1) (hb6 _ (l1.trans (Nat.le_add_right _ _)))
  have hE6 : ∀ r < (lvl .N30 i).rows, rdK s6.M (eqB + 4 * r) = eqBits (sAt es i) (lvl .N30 i).ell r :=
    fun r hr => by
      rw [← e1 r (by rw [← hRe]; exact hr)]
      refine rdK_eq fun t ht => ?_
      have hr64 : r < 64 := lt_of_lt_of_le hr (by rw [hRe]; simpa using hPl)
      rw [g2 _ (by simp only [regs]; omega) (by omega), b2 _ (by simp only [regs]; omega),
        f2 _ (by simp only [regs]; omega) (by omega), a2 _ (by simp only [regs]; omega),
        m2 _ (by simp only [regs]; omega) (.inl (by omega))]
  have hX6 : ∀ j < 2 ^ (lvl .N30 i).logN,
      rdF s6.M (xbM + 2 * j) = encF (mLog .N30 i) (fun x => (nextMsg .N30 L es i x).f₀) j :=
    fun j hj => by
      rw [← f1 j hj]
      exact rdF_eq ((g2 _ (by simp only [regs]; omega) (.inl (by omega))).trans
          (b2 _ (by simp only [regs]; omega)))
        ((g2 _ (by simp only [regs]; omega) (.inl (by omega))).trans (b2 _ (by simp only [regs]; omega)))
  -- the flags
  obtain ⟨k1, k2, hM7⟩ := flagIR_sem I s6 hM6 (n := 2 ^ (lvl .N30 i).logN) (R := (lvl .N30 i).rows)
    (cs := cs) (cb := cb) (eb := eqB) (xb := xbM) (yb := ybM) (fb := fbF) (by omega) (by omega) hcs
    (by simp only [regs]; omega) hcb2 (by simp only [regs]; omega) (by omega)
    (by simp only [regs]; omega) (by omega) (by simp only [regs]; omega) (by omega)
    (by simp only [regs]; omega) (by omega) (by omega) (.inr (by omega)) (.inr (by omega))
    (.inr (by omega)) (.inr (by omega))
  have hc := flagV_consSet (M := s6.M) (cs := cs) (cb := cb) (eb := eqB) (xb := xbM) (yb := ybM)
    hW6 hE6 hX6 g1
  refine ⟨fun j hj => by rw [k1 j hj]; exact hc j hj, fun y hy hy2 => ?_, hM7⟩
  rw [k2 y hy (by omega), h6 y hy (by omega) (by omega)]

/-! ## One level -/

open FR.Snd in
/-- **The decode of level `i`** (`κ = N30`): the front half (`eq` table, the next message's rows
by `msg`, `Enc`, the flags), then the back half (scan, interpolation, butterflies) into `ob`. -/
def decLvIR (msg : XIR) (i cs cb cbS ob : ℕ) : XIR :=
  .seq (decFrontIR msg (lvl .N30 i).ell (lvl .N30 i).logN (lvl .N30 i).rows cs cb cbS)
    (decBackIR (2 ^ (lvl .N30 i).logN) (mLog .N30 i) (lvl .N30 i).rows cs cb ob)

open FR.Snd in
/-- **One level decodes on the machine** (BLUEPRINT §6.2 step 4, `level_decode`): with the basis
table at `tb0`, level `i`'s word at `cb + cs·j + 2r`, P1.i's challenges at `cbS`, a message step
that lays out `nextMsg i`, a close word and `A_c = jointAgree` (what `final` hands over), row `r`
of the decoded message sits at `ob + 2kr` as the `F` values of S-G's `msgOf i r`; the heap below
`jb0`, between `chB` and `eqB`, and from `2^24` on outside the rows, is kept. -/
theorem decLv_sem (I : Array Word) (s : St) (hM : Inv s.M) {L es : Log} {i cs cb cbS ob : ℕ}
    {msg : XIR} (hi : i < 5) (hfar : ¬ farL .N30 L es i)
    (hA : consSet .N30 L es i = jointAgree (wordK .N30 L es i) (decodeL .N30 L es i))
    (hsz : memX ≤ s.M.size) (hcs : 2 * (lvl .N30 i).rows ≤ cs) (hcs2 : cs ≤ 128)
    (hcb : 2 ^ 24 ≤ cb) (hcb2 : cb + 128 * 2 ^ 20 + 256 < 2 ^ 64)
    (hcS : regs ≤ cbS) (hcS2 : cbS + 8 * (lvl .N30 i).ell + 4 ≤ eqB)
    (hL : BaryLay (2 ^ mLog .N30 i) (lvl .N30 i).rows jb0 djb0 wb0 eb0 cb ob tb0)
    (hob : ob + 2 * 2 ^ mLog .N30 i * (lvl .N30 i).rows ≤ memX)
    (hobc : ob + 2 * 2 ^ mLog .N30 i * (lvl .N30 i).rows ≤ chB ∨ 2 ^ 24 ≤ ob)
    (hT : ∀ v < 20, ∀ i < 20, rdF s.M (tb0 + 40 * v + 2 * i) = (wRow D logNMax v).getD i 0)
    (hW : ∀ j (hj : j < 2 ^ (lvl .N30 i).logN) (r : Fin (lvl .N30 i).rows),
      rdF s.M (cb + cs * j + 2 * r) = wordOf .N30 L es i r ⟨j, hj⟩)
    (hS : ∀ v < (lvl .N30 i).ell, rdK s.M (cbS + 8 * v) = sAt es i v)
    (hmsg : MsgOk I msg (semXIR I (eqtIR (lvl .N30 i).ell cbS eqB) s) (lvl .N30 i).logN
      (mLog .N30 i) (nextMsg .N30 L es i)) :
    (∀ r < (lvl .N30 i).rows, ∀ x < 2 ^ mLog .N30 i,
      algebraMap F K (rdF (semXIR I (decLvIR msg i cs cb cbS ob) s).M
        (ob + 2 * 2 ^ mLog .N30 i * r + 2 * x)) = msgOf .N30 L es i r x) ∧
    (∀ y, regs ≤ y → (y < jb0 ∨ (chB ≤ y ∧ y < eqB) ∨
        (2 ^ 24 ≤ y ∧ (y < ob ∨ ob + 2 * 2 ^ mLog .N30 i * (lvl .N30 i).rows ≤ y))) →
      rd (semXIR I (decLvIR msg i cs cb cbS ob) s).M y = rd s.M y) ∧
    Inv (semXIR I (decLvIR msg i cs cb cbS ob) s).M := by
  have hn18 : (lvl .N30 i).logN ≤ 18 := by interval_cases i <;> decide
  have hP : 2 ^ (lvl .N30 i).logN ≤ 2 ^ 18 := Nat.pow_le_pow_right (by norm_num) hn18
  have hcbx : cb + cs * 2 ^ (lvl .N30 i).logN + 2 < 2 ^ 64 := by
    have : cs * 2 ^ (lvl .N30 i).logN ≤ 128 * 2 ^ 20 := Nat.mul_le_mul hcs2 (hP.trans (by norm_num))
    omega
  obtain ⟨a1, a2, hM1⟩ := decFront_sem I s hM (L := L) (es := es) (i := i) (cs := cs) (cb := cb)
    (cbS := cbS) (msg := msg) hi hsz hcs hcb hcbx hcS hcS2 hT hW hS hmsg
  rw [decLvIR, semXIR_seq]
  have z1 := size_sem I (decFrontIR msg (lvl .N30 i).ell (lvl .N30 i).logN (lvl .N30 i).rows cs cb
    cbS) s
  generalize semXIR I (decFrontIR msg (lvl .N30 i).ell (lvl .N30 i).logN (lvl .N30 i).rows cs cb
    cbS) s = s1 at a1 a2 hM1 z1
  have hb1 : ∀ y, cb ≤ y → rd s1.M y = rd s.M y := fun y hy =>
    a2 y ((show regs ≤ 2 ^ 24 by decide).trans (hcb.trans hy)) (.inr (.inr (hcb.trans hy)))
  have hT1 : ∀ v < 20, ∀ i' < 20, rdF s1.M (tb0 + 40 * v + 2 * i') = (wRow D logNMax v).getD i' 0 :=
    fun v hv i' hi' => by
      rw [← hT v hv i' hi']
      have l1 : tb0 + 40 * v + 2 * i' + 1 < fbF := by simp only [tb0, fbF]; omega
      exact rdF_eq (a2 _ (by simp only [regs, tb0]; omega) (.inl (by omega)))
        (a2 _ (by simp only [regs, tb0]; omega) (.inl l1))
  have hW1 : ∀ j (hj : j < 2 ^ (lvl .N30 i).logN) (r : Fin (lvl .N30 i).rows),
      rdF s1.M (cb + cs * j + 2 * r) = wordOf .N30 L es i r ⟨j, hj⟩ := fun j hj r => by
    rw [← hW j hj r]
    have l1 : cb ≤ cb + cs * j + 2 * r := (Nat.le_add_right cb _).trans (Nat.le_add_right _ _)
    exact rdF_eq (hb1 _ l1) (hb1 _ (l1.trans (Nat.le_add_right _ _)))
  obtain ⟨b1, b2, hM2⟩ := decBack_sem I s1 hM1 (L := L) (es := es) (i := i) (cs := cs) (cb := cb)
    (ob := ob) hi hfar hA (by rw [z1]; exact hsz) hL hcb2 hcs2 hob hT1 hW1 a1
  refine ⟨b1, fun y hy hy2 => ?_, hM2⟩
  obtain ⟨-, -, -, -, -, heo, -⟩ := hL
  have ejb : jb0 = 2097152 := rfl
  have edj : djb0 = 4194304 := rfl
  have eeb : eb0 = 5242880 := rfl
  have efb : fbF = 2359296 := rfl
  have ech : chB = 8388608 := rfl
  have eqb : eqB = 8421376 := rfl
  have hm17 : mLog .N30 i ≤ 17 := by interval_cases i <;> decide
  have hk : 2 ^ mLog .N30 i ≤ 2 ^ 17 := Nat.pow_le_pow_right (by norm_num) hm17
  rw [b2 y hy (by omega), a2 y hy (by omega)]

/-! ## The levels' layouts and message steps -/

open FR.Snd

/-- **The layout of levels 1–4**: the word at `stB`, the decoded rows at `obL`. -/
theorem layLv {i : ℕ} (hi1 : 1 ≤ i) (hi : i ≤ 4) :
    BaryLay (2 ^ mLog .N30 i) (lvl .N30 i).rows jb0 djb0 wb0 eb0 stB obL tb0 := by
  interval_cases i <;>
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> decide

/-- **The layout of level 0**: the word at `colBase`, the decoded rows at `ob0` (`lay0`). -/
theorem layLv0 : BaryLay (2 ^ mLog .N30 0) (lvl .N30 0).rows jb0 djb0 wb0 eb0 colBase ob0 tb0 :=
  lay0

/-- **Level 4's message step** (`msg4_next`): with the chain link `finalAt es x = finPi π x`. -/
theorem msgOk_four (c : Digest) (π : Proof) (L es : Log) (hs : π.size = piSize)
    (hfin : ∀ x < 32, finalAt es x = finPi π x) (s : St) (hsz : memX ≤ s.M.size) :
    MsgOk (tp c π L) (msgTIR 10 32 finW xbM ybM) s (lvl .N30 4).logN (mLog .N30 4)
      (nextMsg .N30 L es 4) := by
  intro s' hM' hsz' _
  have e : (lvl .N30 4).logN = 10 := rfl
  rw [e]
  have hX : xbM + 2 * 2 ^ 10 ≤ s'.M.size := by rw [hsz']; exact le_trans (by decide) hsz
  have hY : ybM + 2 * 2 ^ 10 ≤ s'.M.size := by rw [hsz']; exact le_trans (by decide) hsz
  have r1 : regs ≤ xbM := by decide
  have r2 : regs ≤ ybM := by decide
  have b1 : xbM + 2 * 2 ^ 10 < 2 ^ 64 := by decide
  have b2 : ybM + 2 * 2 ^ 10 < 2 ^ 64 := by decide
  have d : xbM + 2 * 2 ^ 10 ≤ ybM := by decide
  obtain ⟨-, h2, h3⟩ := msgTIR_sem (tp c π L) s' hM' (n := 10) (k := 32) (tw := finW) (xb := xbM)
    (yb := ybM) (by norm_num) (by norm_num) (by simp only [finW, finOff]; norm_num) r1 r2 b1 b2 hX hY
    (.inl d)
  refine ⟨msg4_next c π L es hs hfin s' hM' r1 r2 b1 b2 hX hY (.inl d), fun y hy hy2 => ?_, h3⟩
  exact h2 y hy (hy2.imp_right fun h => le_trans (by decide) h)
    (hy2.imp (fun h => lt_of_lt_of_le h (by decide)) fun h => le_trans (by decide) h)

/-- **The message step of levels 0–3** (`msgH_next`): if level `i + 1`'s decoded rows sit at
`obL` as the `F` values of `msgOf (i + 1)`, `msgHIR` lays out `nextMsg i`. -/
theorem msgOk_lower {L es : Log} {i : ℕ} (hi : i < 4) (I : Array Word) (s : St)
    (hsz : memX ≤ s.M.size)
    (hdec : ∀ r < 16, ∀ x < 2 ^ mLog .N30 (i + 1),
      algebraMap F K (rdF s.M (obL + 2 * 2 ^ mLog .N30 (i + 1) * r + 2 * x)) =
        msgOf .N30 L es (i + 1) r x)
    (hF : ∀ r x, msgOf .N30 L es (i + 1) r x = algebraMap F K (msgOf .N30 L es (i + 1) r x).f₀) :
    MsgOk I (msgHIR (lvl .N30 i).logN (2 ^ mLog .N30 (i + 1)) obL xbM ybM) s (lvl .N30 i).logN
      (mLog .N30 i) (nextMsg .N30 L es i) := by
  intro s' hM' hsz' hag
  have hn18 : (lvl .N30 i).logN ≤ 18 := by interval_cases i <;> decide
  have hP : 2 ^ (lvl .N30 i).logN ≤ 2 ^ 18 := Nat.pow_le_pow_right (by norm_num) hn18
  have hm : mLog .N30 (i + 1) ≤ 14 := by interval_cases i <;> decide
  have hk : 2 ^ mLog .N30 (i + 1) ≤ 2 ^ 14 := Nat.pow_le_pow_right (by norm_num) hm
  have hk8 : 8 * 2 ^ mLog .N30 (i + 1) ≤ 2 ^ (lvl .N30 i).logN := by interval_cases i <;> decide
  have hmem : memX = 67108864 := rfl
  have exb : xbM = 8454144 := rfl
  have eyb : ybM = 8978432 := rfl
  have eob : obL = 6291456 := rfl
  have eqb : eqB = 8421376 := rfl
  have hdec' : ∀ r < 16, ∀ x < 2 ^ mLog .N30 (i + 1),
      algebraMap F K (rdF s'.M (obL + 2 * 2 ^ mLog .N30 (i + 1) * r + 2 * x)) =
        msgOf .N30 L es (i + 1) r x := fun r hr x hx => by
    rw [← hdec r hr x hx]
    have : 2 * 2 ^ mLog .N30 (i + 1) * r ≤ 2 * 2 ^ 14 * 16 :=
      Nat.mul_le_mul (Nat.mul_le_mul_left 2 hk) hr.le
    congr 1
    exact rdF_eq (hag _ (by simp only [regs]; omega) (.inl (by omega)))
      (hag _ (by simp only [regs]; omega) (.inl (by omega)))
  obtain ⟨-, h2, h3⟩ := msgHIR_sem I s' hM' (n := (lvl .N30 i).logN) (k := 2 ^ mLog .N30 (i + 1))
    (ob := obL) (xb := xbM) (yb := ybM) (by omega) hk8 (by simp only [regs]; omega) (by omega)
    (by simp only [regs]; omega) (by simp only [regs]; omega) (by omega) (by omega) (by omega)
    (by omega) (.inl (by omega)) (.inl (by omega)) (.inl (by omega))
  refine ⟨msgH_next hi I s' hM' hdec' hF (by simp only [regs]; omega) (by omega)
    (by simp only [regs]; omega) (by simp only [regs]; omega) (by omega) (by omega) (by omega)
    (by omega) (.inl (by omega)) (.inl (by omega)) (.inl (by omega)), fun y hy hy2 => ?_, h3⟩
  exact h2 y hy (by omega) (by omega)

/-! ## The levels instantiated -/

/-- P1.i's challenges in the chain's answers: `s_v` at `cbS i + 8v` (`sAt_words`). -/
def cbS (i : ℕ) : ℕ := ansB + 4 * (phStart (26 + 5 * i) + 1)

theorem phStart_P1 {i : ℕ} (hi : i < 5) : phStart (26 + 5 * i) ≤ 434 := by
  unfold phStart; rw [fsStarts_eq]; interval_cases i <;> decide

theorem cbS_le {i : ℕ} (hi : i < 5) : regs ≤ cbS i ∧ cbS i + 8 * (lvl .N30 i).ell + 4 ≤ eqB := by
  have h := phStart_P1 hi
  have hl : (lvl .N30 i).ell ≤ 6 := by interval_cases i <;> decide
  have ea : ansB = 8392704 := rfl
  have eq : eqB = 8421376 := rfl
  simp only [cbS, regs]; omega

/-- **Levels 1–4 decode** (`decLv_sem` on the layout of `readLv`: the word at `stB`, 32 words a
position; the rows at `obL`). -/
theorem decLvU_sem (I : Array Word) (s : St) (hM : Inv s.M) {L es : Log} {i : ℕ} {msg : XIR}
    (hi1 : 1 ≤ i) (hi : i ≤ 4) (hfar : ¬ farL .N30 L es i)
    (hA : consSet .N30 L es i = jointAgree (wordK .N30 L es i) (decodeL .N30 L es i))
    (hsz : memX ≤ s.M.size)
    (hT : ∀ v < 20, ∀ i < 20, rdF s.M (tb0 + 40 * v + 2 * i) = (wRow D logNMax v).getD i 0)
    (hW : ∀ j (hj : j < 2 ^ (lvl .N30 i).logN) (r : Fin (lvl .N30 i).rows),
      rdF s.M (stB + 32 * j + 2 * r) = wordOf .N30 L es i r ⟨j, hj⟩)
    (hS : ∀ v < (lvl .N30 i).ell, rdK s.M (cbS i + 8 * v) = sAt es i v)
    (hmsg : MsgOk I msg (semXIR I (eqtIR (lvl .N30 i).ell (cbS i) eqB) s) (lvl .N30 i).logN
      (mLog .N30 i) (nextMsg .N30 L es i)) :
    (∀ r < (lvl .N30 i).rows, ∀ x < 2 ^ mLog .N30 i,
      algebraMap F K (rdF (semXIR I (decLvIR msg i 32 stB (cbS i) obL) s).M
        (obL + 2 * 2 ^ mLog .N30 i * r + 2 * x)) = msgOf .N30 L es i r x) ∧
    (∀ y, regs ≤ y → (y < jb0 ∨ (chB ≤ y ∧ y < eqB) ∨ 2 ^ 24 ≤ y) →
      rd (semXIR I (decLvIR msg i 32 stB (cbS i) obL) s).M y = rd s.M y) ∧
    Inv (semXIR I (decLvIR msg i 32 stB (cbS i) obL) s).M := by
  have hi5 : i < 5 := by omega
  have hR : (lvl .N30 i).rows = 16 := by interval_cases i <;> rfl
  have hm : 2 ^ mLog .N30 i ≤ 2 ^ 14 := by interval_cases i <;> decide
  have hob : obL + 2 * 2 ^ mLog .N30 i * (lvl .N30 i).rows ≤ chB := by
    rw [hR]; have : 2 * 2 ^ mLog .N30 i * 16 ≤ 2 * 2 ^ 14 * 16 :=
      Nat.mul_le_mul_right _ (Nat.mul_le_mul_left _ hm)
    exact le_trans (Nat.add_le_add_left this _) (by decide)
  obtain ⟨b1, b2, b3⟩ := decLv_sem I s hM (cs := 32) (cb := stB) (cbS := cbS i) (ob := obL)
    hi5 hfar hA hsz (by rw [hR]) (by norm_num) (by decide) (by decide) (cbS_le hi5).1
    (cbS_le hi5).2 (layLv hi1 hi) (hob.trans (by decide)) (.inl hob) hT hW hS hmsg
  refine ⟨b1, fun y hy hy2 => b2 y hy ?_, b3⟩
  rcases hy2 with h | h | h
  · exact .inl h
  · exact .inr (.inl h)
  · exact .inr (.inr ⟨h, .inr (le_trans (hob.trans (by decide)) h)⟩)

/-- **Level 0 decodes** (`decLv_sem` on the layout of `read0`: the word at `colBase`, 128 words
a position; the rows at `ob0`, row `c` at `ob0 + 2^18 c`). -/
theorem decLv0_sem (I : Array Word) (s : St) (hM : Inv s.M) {L es : Log} {msg : XIR}
    (hfar : ¬ farL .N30 L es 0)
    (hA : consSet .N30 L es 0 = jointAgree (wordK .N30 L es 0) (decodeL .N30 L es 0))
    (hsz : memX ≤ s.M.size)
    (hT : ∀ v < 20, ∀ i < 20, rdF s.M (tb0 + 40 * v + 2 * i) = (wRow D logNMax v).getD i 0)
    (hW : ∀ j (hj : j < 2 ^ (lvl .N30 0).logN) (r : Fin (lvl .N30 0).rows),
      rdF s.M (colBase + 128 * j + 2 * r) = wordOf .N30 L es 0 r ⟨j, hj⟩)
    (hS : ∀ v < (lvl .N30 0).ell, rdK s.M (cbS 0 + 8 * v) = sAt es 0 v)
    (hmsg : MsgOk I msg (semXIR I (eqtIR (lvl .N30 0).ell (cbS 0) eqB) s) (lvl .N30 0).logN
      (mLog .N30 0) (nextMsg .N30 L es 0)) :
    (∀ r < (lvl .N30 0).rows, ∀ x < 2 ^ mLog .N30 0,
      algebraMap F K (rdF (semXIR I (decLvIR msg 0 128 colBase (cbS 0) ob0) s).M
        (ob0 + 2 * 2 ^ mLog .N30 0 * r + 2 * x)) = msgOf .N30 L es 0 r x) ∧
    (∀ y, regs ≤ y → (y < jb0 ∨ (chB ≤ y ∧ y < eqB) ∨ 2 ^ 25 ≤ y) →
      rd (semXIR I (decLvIR msg 0 128 colBase (cbS 0) ob0) s).M y = rd s.M y) ∧
    Inv (semXIR I (decLvIR msg 0 128 colBase (cbS 0) ob0) s).M := by
  obtain ⟨b1, b2, b3⟩ := decLv_sem I s hM (cs := 128) (cb := colBase) (cbS := cbS 0) (ob := ob0)
    (by norm_num) hfar hA hsz (by decide) le_rfl (by decide) (by decide) (cbS_le (by norm_num)).1
    (cbS_le (by norm_num)).2 layLv0 (by decide) (.inr (by decide)) hT hW hS hmsg
  refine ⟨b1, fun y hy hy2 => b2 y hy ?_, b3⟩
  rcases hy2 with h | h | h
  · exact .inl h
  · exact .inr (.inl h)
  · exact .inr (.inr ⟨le_trans (by decide) h, .inr (le_trans (by decide) h)⟩)

end FR.X
