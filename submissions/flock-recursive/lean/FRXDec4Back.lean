-- New for `flock-recursive` (BLUEPRINT revision 4.2, §6.2 step 4; stage S-H4, pass 2, item 2).
import FRXDec4Level
import FRXLagT
import FRXDecLv

/-!
# The back half of one level's decode at revision 4.1's kinds: scan, `lagIR`, butterflies

`decBack4IR n m C c0 cs cb tb fb jb pb yb ob` is

`scanIR n 2^m fb jb ; lagIR 2^m C c0 jb pb yb ob cb cs ; bfRowsIR m ob tb C`:

the first `k = 2^m` flagged positions to `J`, the interpolation of the word's rows
`c₀ … c₀ + C − 1` (row `r` of position `j` at `cb + cs·j + 2r`) at the targets `0 … k − 1`, then
the butterflies on each of the `C` rows. Level 0 decodes rows 4–7 only (`c₀ = 4`, `C = 4`, the rows
the output reads); levels 1–4 decode all 16 rows (`c₀ = 0`, `C = 16`).

**The memory map is a parameter** (`BackLay4`): the basis table at `tb` (800 words), the flags at
`fb` (`n`), `J` at `jb` (`k`), the prefix table at `pb` (`k`), `Y` at `yb` (`2Ck`), the output at
`ob` (`2kC`, row `c` at `ob + 2kc`, plus `2k` words of slack), in this order; the word's column
store at `cb ≥ yb + 2Ck`.

**`decBack4_sem`**: if the flags mark `A_c` (`consN4`), the word is close and
`A_c = jointAgree`, then row `c` at `ob + 2kc` holds the `F` values of `T4.msgOf κ L es i (c₀ + c)`
(`level_decode4`). The heap outside `[jb, jb + k)` and `[pb, ob + 2kC)` is kept.
-/

namespace FR.X

open RecursionFast FR Finset FR.Snd.T4

-- G2: `entryK`/`storeM`/`runPrims` are never unfolded while unifying states (elaboration time).
attribute [local irreducible] entryK storeM runPrims

/-- **The back half's memory map** (`n` positions, `k` targets, `C` rows). -/
def BackLay4 (n k C tb fb jb pb yb ob : ℕ) : Prop :=
  regs ≤ tb ∧ tb + 800 ≤ fb ∧ fb + n ≤ jb ∧ jb + k ≤ pb ∧ pb + k ≤ yb ∧ yb + 2 * C * k ≤ ob ∧
    ob + 2 * k * (C + 1) + 2 < 2 ^ 64

/-- **The back half** at a 4.1 level: scan, interpolation of rows `c₀ … c₀ + C − 1`, butterflies. -/
def decBack4IR (n m C c0 cs cb tb fb jb pb yb ob : ℕ) : XIR :=
  .seq (scanIR n (2 ^ m) fb jb)
    (.seq (lagIR (2 ^ m) C c0 jb pb yb ob cb cs) (bfRowsIR m ob tb C))

theorem wf_decBack4IR (n m C c0 cs cb tb fb jb pb yb ob : ℕ) :
    WF (decBack4IR n m C c0 cs cb tb fb jb pb yb ob) :=
  ⟨wf_scanIR .., wf_lagIR .., wf_bfRowsIR ..⟩

theorem noLoopT_decBack4IR (n m C c0 cs cb tb fb jb pb yb ob : ℕ) :
    NoLoopT (decBack4IR n m C c0 cs cb tb fb jb pb yb ob) :=
  ⟨noLoopT_scanIR .., noLoopT_lagIR .., noLoopT_bfRowsIR ..⟩

theorem outs_decBack4IR (n m C c0 cs cb tb fb jb pb yb ob t : ℕ) :
    outs (decBack4IR n m C c0 cs cb tb fb jb pb yb ob) t = 0 := by
  simp only [decBack4IR, outs, outs_scanIR, outs_lagIR, outs_bfRowsIR]

/-- **The back half's cost** (exact): the scan `16 + 32n`, `lagIR` at `k = 2^m`, the butterflies. -/
theorem cost_decBack4IR (n m C c0 cs cb tb fb jb pb yb ob t : ℕ) (hn : n < 2 ^ 64) (hm : m < 64)
    (hC : C < 2 ^ 64) :
    cost (decBack4IR n m C c0 cs cb tb fb jb pb yb ob) t =
      (16 + n * 32) + (27 + 2 ^ m * (1122 + 72 * C) + (2 ^ m) ^ 2 * (101 + 40 * C)) +
        (1 + C * (17 + m * (741 * 2 ^ (m - 1) + 23))) + 2 := by
  have h1 : 2 ^ m < 2 ^ 64 := Nat.pow_lt_pow_right (by norm_num) hm
  have h2 : 2 ^ (m - 1) < 2 ^ 64 := Nat.pow_lt_pow_right (by norm_num) (by omega)
  simp only [decBack4IR, cost, cost_scanIR n _ fb jb t hn, cost_lagIR _ C c0 jb pb yb ob cb cs t h1 hC,
    cost_bfRowsIR m ob tb t h2 (by omega)]
  ring

/-- The level parameters the machine needs (every kind, every level). -/
theorem lv4_bounds (κ : Snd.CKind) {i : ℕ} (hi : i < 5) :
    1 ≤ Snd.T4.mLog κ i ∧ Snd.T4.mLog κ i ≤ 19 ∧ Snd.T4.mLog κ i ≤ (Snd.CKind.lv κ i).logN ∧
      (Snd.CKind.lv κ i).logN ≤ 20 := by
  rcases κ with (_|_|_) | (_|_|_) <;> interval_cases i <;> decide

/-- **The back half decodes** (`level_decode4`). -/
theorem decBack4_sem (I : Array Word) (s : St) (hM : Inv s.M) {κ : Snd.CKind} {L es : Log}
    {i C c0 cs cb tb fb jb pb yb ob : ℕ} (hi : i < 5) (hfar : ¬ Snd.T4.farL κ L es i)
    (hA : Snd.T4.consSet κ L es i = jointAgree (Snd.T4.wordK κ L es i) (Snd.T4.decodeL κ L es i))
    (hC1 : 1 ≤ C) (hC : C ≤ 16) (hcr : c0 + C ≤ (Snd.CKind.lv κ i).rows)
    (hL : BackLay4 (2 ^ (Snd.CKind.lv κ i).logN) (2 ^ Snd.T4.mLog κ i) C tb fb jb pb yb ob)
    (hcb : yb + 2 * C * 2 ^ Snd.T4.mLog κ i ≤ cb)
    (hcb2 : cb + cs * 2 ^ (Snd.CKind.lv κ i).logN + 2 * (c0 + C) + 2 < 2 ^ 64)
    (hsz : ob + 2 * 2 ^ Snd.T4.mLog κ i * (C + 1) ≤ s.M.size)
    (hT : ∀ v < 20, ∀ i < 20, rdF s.M (tb + 40 * v + 2 * i) = (wRow D logNMax v).getD i 0)
    (hW : ∀ j (hj : j < 2 ^ (Snd.CKind.lv κ i).logN) (r : Fin (Snd.CKind.lv κ i).rows),
      rdF s.M (cb + cs * j + 2 * r) = Snd.T4.wordOf κ L es i r ⟨j, hj⟩)
    (hF : ∀ j < 2 ^ (Snd.CKind.lv κ i).logN, (j ∈ consN4 κ L es i ↔ rd s.M (fb + j) ≠ 0)) :
    (∀ c < C, ∀ x < 2 ^ Snd.T4.mLog κ i,
      algebraMap F K (rdF (semXIR I (decBack4IR (2 ^ (Snd.CKind.lv κ i).logN) (Snd.T4.mLog κ i) C c0 cs cb
        tb fb jb pb yb ob) s).M (ob + 2 * 2 ^ Snd.T4.mLog κ i * c + 2 * x)) =
      Snd.T4.msgOf κ L es i (c0 + c) x) ∧
    (∀ y, regs ≤ y → (y < jb ∨ (jb + 2 ^ Snd.T4.mLog κ i ≤ y ∧ y < pb) ∨
        ob + 2 * 2 ^ Snd.T4.mLog κ i * C ≤ y) →
      rd (semXIR I (decBack4IR (2 ^ (Snd.CKind.lv κ i).logN) (Snd.T4.mLog κ i) C c0 cs cb
        tb fb jb pb yb ob) s).M y = rd s.M y) ∧
    Inv (semXIR I (decBack4IR (2 ^ (Snd.CKind.lv κ i).logN) (Snd.T4.mLog κ i) C c0 cs cb
        tb fb jb pb yb ob) s).M := by
  classical
  obtain ⟨htb, htf, hfj, hjp, hpy, hyo, ho2⟩ := hL
  obtain ⟨hm1, hm19, hmn, hn20⟩ := lv4_bounds κ hi
  have hs := hM.1
  simp only [regs] at hs htb
  have hP : 2 ^ (Snd.CKind.lv κ i).logN ≤ 2 ^ 20 := Nat.pow_le_pow_right (by norm_num) hn20
  have hPm : 2 ^ Snd.T4.mLog κ i ≤ 2 ^ (Snd.CKind.lv κ i).logN := Nat.pow_le_pow_right (by norm_num) hmn
  have hk1 : 1 ≤ 2 ^ Snd.T4.mLog κ i := Nat.one_le_two_pow
  have enM : nMax = 1048576 := rfl
  -- the agreement set is large enough
  have hcard : 2 ^ Snd.T4.mLog κ i ≤ (consN4 κ L es i).card := by
    obtain ⟨h1, -, -, hk', hn'⟩ := Snd.T4.lv_params κ hi
    obtain ⟨-, hJ⟩ := Snd.T4.decodeL_spec hfar
    rw [consN4, card_map, hA]
    have : Snd.T4.lvK κ i ≤ 2 ^ (Snd.CKind.lv κ i).logN - Snd.T4.lvE κ i := by rw [← hn']; omega
    rw [← hk']; exact this.trans hJ
  -- the scan
  rw [decBack4IR, semXIR_seq]
  obtain ⟨a1, a2, a3, hM1⟩ := scanIR_sem I s hM (n := 2 ^ (Snd.CKind.lv κ i).logN) (k := 2 ^ Snd.T4.mLog κ i)
    (fb := fb) (lb := jb) (f := fun j => rd s.M (fb + j)) (by simp only [regs]; omega)
    (by omega) (by omega) (by simp only [regs]; omega) (by omega) (by omega) (.inl hfj) (fun j _ => rfl)
  have z1 := size_sem I (scanIR (2 ^ (Snd.CKind.lv κ i).logN) (2 ^ Snd.T4.mLog κ i) fb jb) s
  generalize semXIR I (scanIR (2 ^ (Snd.CKind.lv κ i).logN) (2 ^ Snd.T4.mLog κ i) fb jb) s = s1 at a1 a2 a3 hM1 z1
  obtain ⟨SL, hSL⟩ : ∃ SL, SL = scanL (2 ^ (Snd.CKind.lv κ i).logN) fun j => rd s.M (fb + j) := ⟨_, rfl⟩
  rw [← hSL] at a1 a2
  obtain ⟨Jl, hJl⟩ : ∃ Jl, Jl = SL.take (2 ^ Snd.T4.mLog κ i) := ⟨_, rfl⟩
  have hfk : firstK (2 ^ (Snd.CKind.lv κ i).logN) (consN4 κ L es i) (2 ^ Snd.T4.mLog κ i) = Jl.toFinset := by
    rw [hJl, hSL]; exact firstK_scan hF
  have hlen : Jl.length = 2 ^ Snd.T4.mLog κ i := by
    have h1 := firstK_card (n := 2 ^ (Snd.CKind.lv κ i).logN) (A := consN4 κ L es i)
      (fun j hj => (mem_consN4.1 hj).1) hcard
    rw [hfk] at h1
    have h2 := List.toFinset_card_le Jl
    have h3 : Jl.length ≤ 2 ^ Snd.T4.mLog κ i := by rw [hJl]; exact List.length_take_le _ _
    omega
  have hlen0 : 2 ^ Snd.T4.mLog κ i ≤ SL.length := by
    have := List.length_take_le' (2 ^ Snd.T4.mLog κ i) SL
    rw [← hJl] at this; omega
  have hnd : Jl.Nodup := by
    rw [hJl, hSL]
    exact List.Nodup.sublist (List.take_sublist _ _) (List.Nodup.filter _ List.nodup_range)
  have hJmem : ∀ j ∈ Jl, j < 2 ^ (Snd.CKind.lv κ i).logN := fun j hj => by
    rw [hJl, hSL] at hj
    have := List.mem_of_mem_take hj
    simp only [scanL, List.mem_filter, List.mem_range] at this
    exact this.1
  have hJ1 : ∀ t < 2 ^ Snd.T4.mLog κ i, rd s1.M (jb + t) = jw Jl t := fun t ht => by
    rw [a2 t (by omega), jw, hJl, List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD,
      List.getElem?_take_of_lt (by omega)]
  have hget : ∀ t < 2 ^ Snd.T4.mLog κ i, Jl.getD t 0 < 2 ^ (Snd.CKind.lv κ i).logN := fun t ht =>
    hJmem _ (by rw [List.getD_eq_getElem _ _ (by omega)]; exact List.getElem_mem _)
  have k1 : ∀ y, regs ≤ y → (y < jb ∨ jb + 2 ^ Snd.T4.mLog κ i ≤ y) → rd s1.M y = rd s.M y := a3
  -- the interpolation
  rw [semXIR_seq]
  obtain ⟨b1, b2, hM2⟩ := lagIR_sem I s1 hM1 (k := 2 ^ Snd.T4.mLog κ i) (C := C) (c0 := c0) (cb := cb)
    (cs := cs) (Jl := Jl) hk1 (by omega) hC (by simp only [regs]; omega) hjp hpy hyo hcb
    (by rw [z1]; exact hsz) ho2 (fun t ht => by
      have : cs * Jl.getD t 0 ≤ cs * 2 ^ (Snd.CKind.lv κ i).logN := Nat.mul_le_mul_left _ (hget t ht).le
      omega) hJ1
  have z2 := size_sem I (lagIR (2 ^ Snd.T4.mLog κ i) C c0 jb pb yb ob cb cs) s1
  generalize semXIR I (lagIR (2 ^ Snd.T4.mLog κ i) C c0 jb pb yb ob cb cs) s1 = s2 at b1 b2 hM2 z2
  -- the butterflies
  have hT1 : ∀ v < 20, ∀ i' < 20, rdF s2.M (tb + 40 * v + 2 * i') = (wRow D logNMax v).getD i' 0 :=
    fun v hv i' hi' => by
      rw [← hT v hv i' hi']
      exact rdF_eq ((b2 _ (by simp only [regs]; omega) (.inl (by omega))).trans
          (k1 _ (by simp only [regs]; omega) (.inl (by omega))))
        ((b2 _ (by simp only [regs]; omega) (.inl (by omega))).trans
          (k1 _ (by simp only [regs]; omega) (.inl (by omega))))
  have hCk : 2 * 2 ^ Snd.T4.mLog κ i * (C + 1) = 2 * 2 ^ Snd.T4.mLog κ i * C + 2 * 2 ^ Snd.T4.mLog κ i :=
    Nat.mul_succ _ _
  obtain ⟨c1, c2, hM3⟩ := bfRows_sem I (m := Snd.T4.mLog κ i) (ob := ob) (tb := tb)
    (Y := fun c x => lagVal Jl (2 ^ Snd.T4.mLog κ i) x fun j => rdF s1.M (cb + cs * j + 2 * c0 + 2 * c))
    hm1 (by omega) (by simp only [regs]; omega) (by simp only [regs]; omega) (by omega) C s2 hM2
    (by omega) (by rw [z2, z1]; omega) (.inl (by omega)) hT1
    (fun c hc x hx => by rw [show ob + 2 * 2 ^ Snd.T4.mLog κ i * c + 2 * x =
      ob + 2 * x + 2 * 2 ^ Snd.T4.mLog κ i * c by ring]; exact b1 x hx c hc)
  refine ⟨fun c hc x hx => ?_, fun y hy hy2 => ?_, hM3⟩
  · rw [c1 c hc x hx]
    have hr : c0 + c < (Snd.CKind.lv κ i).rows := by omega
    have hY : (fun s' => lagVal Jl (2 ^ Snd.T4.mLog κ i) s' fun j => rdF s1.M (cb + cs * j + 2 * c0 + 2 * c)) =
        interpF D (firstK (2 ^ (Snd.CKind.lv κ i).logN) (consN4 κ L es i) (2 ^ Snd.T4.mLog κ i))
          (wordN4 κ L es i ⟨c0 + c, hr⟩) := by
      funext x'
      have hv := lagVal_eq hnd (fun j hj => lt_of_lt_of_le (hJmem j hj) (by omega)) (s := x')
        (fun j => rdF s1.M (cb + cs * j + 2 * c0 + 2 * c))
      rw [hlen] at hv
      rw [hv, hfk]
      refine interpF_congr D _ (fun j hj => ?_) x'
      have hjn := hJmem j (List.mem_toFinset.1 hj)
      have hc' : cs * j ≤ cs * (2 ^ (Snd.CKind.lv κ i).logN) := Nat.mul_le_mul_left _ hjn.le
      rw [show cb + cs * j + 2 * c0 + 2 * c = cb + cs * j + 2 * (c0 + c) by ring,
        rdF_eq (k1 _ (by simp only [regs]; omega) (.inr (by omega)))
        (k1 _ (by simp only [regs]; omega) (.inr (by omega)))]
      rw [show cb + cs * j + 2 * (c0 + c) = cb + cs * j + 2 * ((⟨c0 + c, hr⟩ : Fin _) : ℕ) from rfl,
        hW j hjn ⟨c0 + c, hr⟩]
      simp only [wordN4, hjn, dite_true]
    rw [hY]
    exact level_decode4 hi hfar hA ⟨c0 + c, hr⟩ ⟨x, hx⟩
  · rw [c2 y hy (by omega), b2 y hy (by omega), k1 y hy (by omega)]

/-! ## Controls and the level-0 cost at `m = 32` -/

/-- (+) **A level-0 memory map at `m = 32` fits** (`n = 2^20` positions, `k = 2^19`, rows 4–7):
basis table `2^20`, flags `2^21`, `J` `2^22`, `P` `2^22 + 2^19`, `Y` `2^23`, output `2^23 + 2^22`
(the word's columns may start at `2^23 + 2^22`). -/
theorem backLay4_m32 : BackLay4 (2 ^ 20) (2 ^ 19) 4 (2 ^ 20) (2 ^ 21) (2 ^ 22) (2 ^ 22 + 2 ^ 19) (2 ^ 23)
    (2 ^ 23 + 2 ^ 22) := by
  unfold BackLay4; norm_num [regs]

/-- (−) **`BackLay4` rejects overlapping regions**: the output on top of `Y` fails. -/
theorem not_backLay4_overlap : ¬ BackLay4 (2 ^ 20) (2 ^ 19) 4 (2 ^ 20) (2 ^ 21) (2 ^ 22)
    (2 ^ 22 + 2 ^ 19) (2 ^ 23) (2 ^ 23) := by
  unfold BackLay4; norm_num [regs]

/-- **Level 0's back half at `m = 32`** (rows 4–7): `7.18 · 10^13` steps, within 3.x's `decBudget`
(`2.11 · 10^14 + 8,176 t`) with room for the other levels (`logs/S-H4/fuel-check4.txt`). -/
theorem cost_back0_m32 (cs cb tb fb jb pb yb ob t : ℕ) :
    cost (decBack4IR (2 ^ 20) 19 4 4 cs cb tb fb jb pb yb ob) t = 71758669416262 := by
  rw [cost_decBack4IR _ _ _ _ _ _ _ _ _ _ _ _ _ (by norm_num) (by norm_num) (by norm_num)]
  norm_num

end FR.X
