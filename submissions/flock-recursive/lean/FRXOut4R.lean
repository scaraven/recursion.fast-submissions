-- New for `flock-recursive` (BLUEPRINT revision 4.1, §6.2 step 5; stage S-H4, pass 10, item 2: the
-- node output's machine pieces). 3.x analogue: `FRXOutRun` (one slot stream, no shift, no aggregate).
import FRXOut4C
import FRXOutRun

/-!
# The node output's machine pieces

After the decode, H's message words are heap words at `hAddr κ n` (`FRXSig4W`), the shape `apH κ`
over the base `hBase κ`. A signed child's chain words are H words of the blocks `blkOf` (the last one
redirected to `finBlk`), so

* **the chain loader** `ldC κ` reads chain word `n` at H word `n + cb + [⌊n/8⌋ = jL]·Δ` (registers
  `qCB`, `qJ`, `qDl`: the chain's base, its last block, the redirect);
* **the realign loop** `realign κ` writes segment `i`'s `segB/8` virtual words into the buffer at
  `bufB` (shape `apB`): word `u` is the shifted pair `(C(q+u) >>> 8s) + ((C(q+u+1) <<< 1) <<< (63 − 8s))`,
  `D = i·(segB − 1)`, `q = ⌊D/8⌋`, `s = D mod 8`, which is `shWd C s (q + u)` at every `s < 8`
  (**`realign_sem`**). The heap below `bufB` is kept, so the decode's cells stay readable.

The emitters over the buffer are 3.x's `segIR` unchanged (`FRXOut.segIR_sem`, linear in the
buffer's shape).
-/

namespace FR.X

open RecursionFast FR.Read FR.Rev4 FR.Snd

attribute [local irreducible] entryK storeM runPrims

/-! ## Registers (below `FRXOut`'s, which the segments write) -/

/-- The chain word index. -/ def qN : ℕ := 100
/-- The buffer index. -/ def qU : ℕ := 101
/-- `8s`. -/ def qA : ℕ := 102
/-- `63 − 8s`. -/ def qB : ℕ := 103
/-- The chain's last stream block. -/ def qJ : ℕ := 104
/-- The redirect `Δ`. -/ def qDl : ℕ := 105
/-- `8 ·` the chain's first block. -/ def qCB : ℕ := 106
/-- The segment count `k`. -/ def qK : ℕ := 107
/-- The segment index `i`. -/ def qI : ℕ := 108
/-- The realign loop's counter. -/ def qLc : ℕ := 109
/-- The realign loop's count. -/ def qLn : ℕ := 110
/-- The segment loop's counter. -/ def qSc : ℕ := 111
/-- Scratch. -/ def qT1 : ℕ := 112
/-- Scratch. -/ def qT2 : ℕ := 113
/-- The loader's index. -/ def qM : ℕ := 120

/-! ## Shapes, bases -/

/-- **H's shape** at node kind `κ`: 3.x's stream shape at level 0's row stride. -/
def apH (κ : NodeKind) : AP := ⟨3, 3, 2, T4.mLog (.node κ) 0 + 1⟩

/-- **H's base**: row 4 of level 0's decoded rows (`hAddr_eq`). -/
def hBase (κ : NodeKind) : ℕ := map4.l0.ob + 2 ^ (T4.mLog (.node κ) 0 + 1) * 3

/-- The buffer's shape. -/
def apB : AP := ⟨3, 3, 2, 20⟩

/-- **The buffer's base**: level 0's word region (free after the decode). -/
def bufB : ℕ := 134217728

/-- The buffer's words per segment. -/
def nW : ℕ := 185344

/-- Buffer word `u`'s address. -/
def bufA (u : ℕ) : ℕ := bufB + u / 2 % 4 * 2 ^ 20 + u / 8 * 4 + u % 2

/-! ## The chain loader and the realign loop -/

/-- **The chain loader**: `oX :=` H word `qM + qCB + [qM >>> 3 = qJ]·qDl`. -/
def ldC (κ : NodeKind) : XIR :=
  .seq (.blk [.const oK (toWord 3), .op .shr qT1 qM oK, .op .eq qT1 qT1 qJ, .op .mul qT1 qT1 qDl,
    .op .add oU qM qCB, .op .add oU oU qT1]) (ldw (apH κ))

/-- **One realigned word**: two chain words, shifted and added, stored at buffer word `qU`. -/
def rlBody (κ : NodeKind) : XIR :=
  .seq (.blk [.const oR (toWord (hBase κ)), .op .or qM qN qN]) (.seq (ldC κ)
  (.seq (.blk [.op .shr oY oX qA, .op .add qM qN cOne]) (.seq (ldC κ)
  (.seq (.blk [.op .shl oX oX cOne, .op .shl oX oX qB, .op .add oX oY oX, .const oR (toWord bufB),
      .op .or oU qU qU])
  (.seq (.blk (ldPs apB)) (.seq (.store oAd oX) (.blk [.op .add qN qN cOne, .op .add qU qU cOne])))))))

/-- **Segment `qI`'s realign**: `D := qI·(segB − 1)`, `q`, `8s`, `63 − 8s`, then `nW` words. -/
def realign (κ : NodeKind) : XIR :=
  .seq (.blk [.const qT1 (toWord (N4c.segB - 1)), .op .mul qT1 qI qT1, .const oK (toWord 3),
      .op .shr qN qT1 oK, .const oK (toWord 7), .op .and qA qT1 oK, .const oK (toWord 3),
      .op .shl qA qA oK, .op .sub qB c63 qA, .const qU 0, .const qLn (toWord nW)])
    (.loopK qLc qLn (toWord nW) (rlBody κ))

/-! ## Proof helpers: addresses -/

theorem addrH_toNat {st R u : ℕ} (hst : st ≤ 20) (hR : R < 2 ^ 62) (hu : u < 2 ^ 64) :
    (addrW ⟨3, 3, 2, st⟩ (toWord R) (toWord u)).toNat = R + u / 2 % 4 * 2 ^ st + u / 8 * 4 + u % 2 := by
  have h20 : 2 ^ st ≤ 2 ^ 20 := Nat.pow_le_pow_right (by norm_num) hst
  simp only [addrW]
  have h4 : u / 2 % 4 * 2 ^ st ≤ 3 * 2 ^ 20 := Nat.mul_le_mul (by omega) h20
  rw [shr_toWord hu (by norm_num), show (3 : ℕ) = 2 ^ 2 - 1 from rfl,
    and_mask_toWord (lt_of_le_of_lt (Nat.div_le_self _ _) hu) (by norm_num),
    shl_toWord (by omega) (by norm_num; omega), shr_toWord hu (by norm_num),
    shl_toWord (by norm_num) (by omega), and_one_toWord hu, add_toWord, add_toWord, add_toWord,
    toNat_toWord (by norm_num; omega)]
  norm_num

theorem mLog0_le (κ : NodeKind) : T4.mLog (.node κ) 0 + 1 ≤ 20 := by cases κ <;> decide

theorem hAddr_apH (κ : NodeKind) {n : ℕ} (hn : n < 2 ^ 64) :
    (addrW (apH κ) (toWord (hBase κ)) (toWord n)).toNat = hAddr κ n := by
  rw [apH, addrH_toNat (mLog0_le κ) (by cases κ <;> decide) hn, hAddr_eq, hBase]; ring

theorem bufA_apB {u : ℕ} (hu : u < 2 ^ 64) : (addrW apB (toWord bufB) (toWord u)).toNat = bufA u := by
  rw [apB, addrH_toNat le_rfl (by decide) hu, bufA]

theorem hAddr_lt (κ : NodeKind) {n : ℕ} (hn : n / 8 * 128 + 8 ≤ 2 ^ (κ.m - 7)) : hAddr κ n < bufB := by
  rw [hAddr_eq]
  have h4 : n / 2 % 4 < 4 := Nat.mod_lt _ (by norm_num)
  cases κ <;> simp only [NodeKind.m, bufB] at hn ⊢ <;>
    simp only [show T4.mLog (.node .N2) 0 = 18 from rfl, show T4.mLog (.node .N4) 0 = 19 from rfl,
      show T4.mLog (.node .N8) 0 = 19 from rfl] <;> omega

theorem regs_hAddr (κ : NodeKind) (n : ℕ) : regs ≤ hAddr κ n := by
  rw [hAddr_eq]; simp only [regs]; omega

theorem bufA_inj {u v : ℕ} (hu : u < nW) (hv : v < nW) (h : bufA u = bufA v) : u = v := by
  simp only [bufA, nW] at *
  have b1 : u / 8 * 4 + u % 2 < 2 ^ 20 := by omega
  have b2 : v / 8 * 4 + v % 2 < 2 ^ 20 := by omega
  have h1 : u / 2 % 4 = v / 2 % 4 := by omega
  have h2 : u / 8 = v / 8 := by omega
  omega

theorem bufA_ge (u : ℕ) : bufB ≤ bufA u := by simp only [bufA]; omega

theorem bufA_lt {u : ℕ} (hu : u < nW) : bufA u < bufB + 2 ^ 22 := by simp only [bufA, nW] at *; omega

/-! ## The output phase's frame -/

/-- **The output phase's frame**: the invariant, the size, and the heap below the buffer as
`M₀`'s (the decode's cells). -/
structure OF (M₀ : Mem) (s : St) : Prop where
  inv : Inv s.M
  size : s.M.size = M₀.size
  low : ∀ y, regs ≤ y → y < bufB → rd s.M y = rd M₀ y

theorem of_loK {M₀ : Mem} (I : Array Word) {P : XIR} (hL : LoK P) (hw : WF P) {s : St} (h : OF M₀ s) :
    OF M₀ (semXIR I P s) :=
  ⟨inv_sem I hw h.inv, (size_sem I P s).trans h.size, fun y h1 h2 => (hframeK I P s hL y h1).trans (h.low y h1 h2)⟩

theorem of_decS {M₀ : Mem} {c : ℕ} (hc4 : 4 ≤ c) (hc : c < regs) {s : St} (h : OF M₀ s) : OF M₀ (decS c s) :=
  ⟨inv_decS h.inv hc4, (size_decS c s).trans h.size, fun y h1 h2 => (rd_decS (by omega) s).trans (h.low y h1 h2)⟩

/-! ## The chain loader's semantics -/

/-- **The H word the loader reads** for chain word `n`: `n + cb`, plus `Δ` in block `jL`. -/
def ldIx (cb jL Δ n : ℕ) : ℕ := n + cb + if n / 8 = jL then Δ else 0

theorem eq_toWord {a b : ℕ} (ha : a < 2 ^ 64) (hb : b < 2 ^ 64) :
    XOp.eq.eval (toWord a) (toWord b) = if a = b then 1 else 0 := by
  simp only [XOp.eval, toWord_eq_iff ha hb]

theorem ite_mul_toWord (p : Prop) [Decidable p] (d : ℕ) :
    XOp.mul.eval (if p then 1 else 0) (toWord d) = toWord (if p then d else 0) := by
  split_ifs <;> simp [XOp.eval, toWord]

theorem ldC_sem (I : Array Word) (κ : NodeKind) (s : St) (hM : Inv s.M) {n cb jL Δ : ℕ}
    (hR : rd s.M oR = toWord (hBase κ)) (hn : rd s.M qM = toWord n) (hcb : rd s.M qCB = toWord cb)
    (hj : rd s.M qJ = toWord jL) (hd : rd s.M qDl = toWord Δ) (hb : n + cb + Δ < 2 ^ 64) (hjl : jL < 2 ^ 64) :
    rd (semXIR I (ldC κ) s).M oX = rd s.M (hAddr κ (ldIx cb jL Δ n)) ∧ (semXIR I (ldC κ) s).o = s.o := by
  have hs := hM.1
  simp only [regs] at hs
  rw [ldC, semXIR_seq, semXIR_blk]
  set ps : List Prim := [.const oK (toWord 3), .op .shr qT1 qM oK, .op .eq qT1 qT1 qJ, .op .mul qT1 qT1 qDl,
    .op .add oU qM qCB, .op .add oU oU qT1] with hps
  have hu : rd (runPrims ps s.M) oU = toWord (ldIx cb jL Δ n) := by
    simp only [hps, runPrims, List.foldl, Prim.run]
    simp (disch := (simp only [size_set, oK, oU, qT1, qM, qJ, qDl, qCB] at *; omega)) only [rd_set_self, rd_set_ne]
    rw [hn, hj, hd, hcb, shr_toWord (by omega) (by norm_num), eq_toWord (by omega) hjl, ite_mul_toWord,
      add_toWord, add_toWord, ldIx]
    norm_num
  have hr : rd (runPrims ps s.M) oR = toWord (hBase κ) := by
    simp only [hps, runPrims, List.foldl, Prim.run]
    simp (disch := (simp only [size_set, oK, oU, qT1, oR] at *; omega)) only [rd_set_ne]
    exact hR
  have hh : ∀ y, regs ≤ y → rd (runPrims ps s.M) y = rd s.M y := fun y hy =>
    rd_runPrims_of_not_writes (fun p hp he => by
      simp only [hps, List.mem_cons, List.mem_nil_iff, or_false] at hp
      simp only [regs] at hy
      rcases hp with rfl | rfl | rfl | rfl | rfl | rfl <;> simp only [Prim.dst, oK, oU, qT1] at he <;> omega) _
  have hI : ldIx cb jL Δ n < 2 ^ 64 := by unfold ldIx; split_ifs <;> omega
  have hA : (addrW (apH κ) (rd (runPrims ps s.M) oR) (rd (runPrims ps s.M) oU)).toNat = hAddr κ (ldIx cb jL Δ n) := by
    rw [hr, hu, hAddr_apH κ hI]
  have hM1 : Inv (runPrims ps s.M) := inv_sem I (P := .blk ps) (fun p hp => by
    simp only [hps, List.mem_cons, List.mem_nil_iff, or_false] at hp
    rcases hp with rfl | rfl | rfl | rfl | rfl | rfl <;> simp [Prim.dst, oK, oU, qT1]) hM
  obtain ⟨l1, l2⟩ := ldw_sem I (apH κ) ⟨runPrims ps s.M, s.o⟩ hM1 (by rw [hA]; exact regs_hAddr κ _)
  exact ⟨by rw [l1, hA, hh _ (regs_hAddr κ _)], l2⟩

theorem wf_ldC (κ : NodeKind) : WF (ldC κ) :=
  ⟨by simp +decide [WF], wf_ldw _⟩

theorem loK_ldC (κ : NodeKind) : LoK (ldC κ) :=
  ⟨by simp +decide [LoK, regs], loK_ldw _⟩

theorem keep_ldC (I : Array Word) (κ : NodeKind) {t : St} (hM : Inv t.M) {r : ℕ} (hr : r < regs)
    (h : r ∉ [oK, qT1, oU, oT1, oT2, oT3, oAd, oX]) : rd (semXIR I (ldC κ) t).M r = rd t.M r :=
  keep_of I (wf_ldC κ) hM hr (by
    simp only [List.mem_cons, List.mem_nil_iff, or_false, not_or] at h
    simp [wrL, ldC, ldw, ldPs, Prim.dst, h.1, h.2.1, h.2.2.1, h.2.2.2.1, h.2.2.2.2.1, h.2.2.2.2.2.1,
      h.2.2.2.2.2.2.1, h.2.2.2.2.2.2.2, eq_comm])

/-- The address block's value (`ldw_sem`'s first half). -/
theorem ldPs_oAd (ap : AP) (M : Mem) (hM : Inv M) :
    rd (runPrims (ldPs ap) M) oAd = addrW ap (rd M oR) (rd M oU) := by
  have hs := hM.1
  have h1 := one_cOne hM
  simp only [regs] at hs
  simp only [ldPs, runPrims, List.foldl, Prim.run]
  simp (disch := (simp only [size_set, oK, oT1, oT2, oT3, oAd, oX, oU, oR, cOne]; omega))
    only [rd_set_self, rd_set_ne, h1]
  simp only [addrW]

theorem ldPs_keep (ap : AP) (M : Mem) {r : ℕ} (h : r ∉ [oK, oT1, oT2, oT3, oAd]) :
    rd (runPrims (ldPs ap) M) r = rd M r :=
  rd_runPrims_of_not_writes (fun p hp he => by
    simp only [ldPs, List.mem_cons, List.mem_nil_iff, or_false] at hp
    simp only [List.mem_cons, List.mem_nil_iff, or_false, not_or] at h
    rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      simp only [Prim.dst] at he <;> subst he <;> simp_all) _

/-! ## The realign loop's semantics -/

/-- **The realign loop's invariant** after `j` words. -/
structure RlInv (κ : NodeKind) (M₀ : Mem) (o : Array Word) (cb jL Δ sh q j : ℕ) (t : St) : Prop where
  of : OF M₀ t
  o : t.o = o
  n : rd t.M qN = toWord (q + j)
  u : rd t.M qU = toWord j
  a : rd t.M qA = toWord (8 * sh)
  b : rd t.M qB = toWord (63 - 8 * sh)
  cbR : rd t.M qCB = toWord cb
  jlR : rd t.M qJ = toWord jL
  dR : rd t.M qDl = toWord Δ
  buf : ∀ u < j, rd t.M (bufA u) = shWd (fun n => rd M₀ (hAddr κ (ldIx cb jL Δ n))) sh (q + u)

theorem shl_shl_one (x : Word) {sh : ℕ} (hs : sh < 8) :
    XOp.shl.eval (XOp.shl.eval x 1) (toWord (63 - 8 * sh)) = x <<< (64 - 8 * sh) := by
  rw [shl_c _ _ (by omega)]
  simp only [XOp.eval]
  rw [show ((1 : Word).toNat % 64) = 1 from rfl, ← BitVec.shiftLeft_add]
  congr 1; omega

theorem shr_8s (x : Word) {sh : ℕ} (hs : sh < 8) : XOp.shr.eval x (toWord (8 * sh)) = x >>> (8 * sh) :=
  shr_c _ _ (by omega)

/-- **One realigned word.** -/
theorem rlBody_step (I : Array Word) (κ : NodeKind) {M₀ : Mem} {o : Array Word} {cb jL Δ sh q j : ℕ}
    (hs8 : sh < 8) (hb : q + nW + 1 + cb + Δ < 2 ^ 64) (hjl : jL < 2 ^ 64) (hj : j < nW)
    (hsz : bufB + 2 ^ 22 ≤ M₀.size)
    (hlow : ∀ n ≤ q + nW, hAddr κ (ldIx cb jL Δ n) < bufB)
    {t : St} (h : RlInv κ M₀ o cb jL Δ sh q j t) :
    RlInv κ M₀ o cb jL Δ sh q (j + 1) (decS qLc (semXIR I (rlBody κ) t)) := by
  obtain ⟨hO, ho, hn, hu, ha, hbb, hcb, hjj, hd, hbuf⟩ := h
  have hs := hO.inv.1
  simp only [regs] at hs
  set G : ℕ → Word := fun n => rd M₀ (hAddr κ (ldIx cb jL Δ n)) with hG
  -- block 1
  rw [rlBody, semXIR_seq, semXIR_blk]
  set M1 := runPrims [.const oR (toWord (hBase κ)), .op .or qM qN qN] t.M with hM1d
  have k1 : ∀ r, r ≠ oR → r ≠ qM → rd M1 r = rd t.M r := fun r h1 h2 => by
    simp only [hM1d, runPrims, List.foldl, Prim.run]; rw [rd_set_ne (Ne.symm h2), rd_set_ne (Ne.symm h1)]
  have r1 : rd M1 oR = toWord (hBase κ) := by
    simp only [hM1d, runPrims, List.foldl, Prim.run]
    simp (disch := (simp only [size_set, oR, qM] at *; omega)) only [rd_set_self, rd_set_ne]
  have m1 : rd M1 qM = toWord (q + j) := by
    simp only [hM1d, runPrims, List.foldl, Prim.run]
    simp (disch := (simp only [size_set, oR, qM, qN] at *; omega)) only [rd_set_self, rd_set_ne]
    rw [or_self_eval, hn]
  have i1 : Inv M1 := inv_sem I (P := .blk [.const oR (toWord (hBase κ)), .op .or qM qN qN])
    (by simp +decide [WF, Prim.dst, oR, qM]) hO.inv
  have hh1 : ∀ y, regs ≤ y → rd M1 y = rd t.M y := fun y hy => k1 y (by simp only [oR, regs] at *; omega)
    (by simp only [qM, regs] at *; omega)
  -- the first load
  obtain ⟨x1, o1⟩ := ldC_sem I κ ⟨M1, t.o⟩ i1 r1 m1 (by rw [k1 _ (by decide) (by decide)]; exact hcb)
    (by rw [k1 _ (by decide) (by decide)]; exact hjj) (by rw [k1 _ (by decide) (by decide)]; exact hd)
    (by omega) hjl
  rw [semXIR_seq]
  generalize hs2 : semXIR I (ldC κ) ⟨M1, t.o⟩ = s2 at x1 o1
  have i2 : Inv s2.M := hs2 ▸ inv_sem I (wf_ldC κ) i1
  have k2 : ∀ r < regs, r ∉ [oK, qT1, oU, oT1, oT2, oT3, oAd, oX] → rd s2.M r = rd M1 r := fun r hr hn =>
    hs2 ▸ keep_ldC I κ i1 hr hn
  have hh2 : ∀ y, regs ≤ y → rd s2.M y = rd M1 y := fun y hy => hs2 ▸ hframeK I _ _ (loK_ldC κ) y hy
  have sz2 : s2.M.size = t.M.size := by rw [← hs2, size_sem]; exact size_runPrims _ _
  have v1 : rd s2.M oX = G (q + j) := by
    rw [x1, hh1 _ (regs_hAddr κ _), hO.low _ (regs_hAddr κ _) (hlow _ (by omega))]
  -- block 2
  rw [semXIR_seq, semXIR_blk]
  have hs2' := i2.1
  simp only [regs] at hs2'
  set M3 := runPrims [.op .shr oY oX qA, .op .add qM qN cOne] s2.M with hM3d
  have k3 : ∀ r, r ≠ oY → r ≠ qM → rd M3 r = rd s2.M r := fun r h1 h2 => by
    simp only [hM3d, runPrims, List.foldl, Prim.run]; rw [rd_set_ne (Ne.symm h2), rd_set_ne (Ne.symm h1)]
  have y3 : rd M3 oY = G (q + j) >>> (8 * sh) := by
    simp only [hM3d, runPrims, List.foldl, Prim.run]
    simp (disch := (simp only [size_set, oY, qM, oX, qA] at *; omega)) only [rd_set_self, rd_set_ne]
    rw [v1, k2 _ (by decide) (by decide), k1 _ (by decide) (by decide), ha, shr_8s _ hs8]
  have m3 : rd M3 qM = toWord (q + j + 1) := by
    simp only [hM3d, runPrims, List.foldl, Prim.run]
    simp (disch := (simp only [size_set, oY, qM, qN, cOne] at *; omega)) only [rd_set_self, rd_set_ne]
    rw [k2 _ (by decide) (by decide), k1 _ (by decide) (by decide), hn, one_cOne i2, add_one_toWord]
  have i3 : Inv M3 := inv_sem I (P := .blk [.op .shr oY oX qA, .op .add qM qN cOne])
    (by simp +decide [WF, Prim.dst, oY, qM]) i2
  have k23 : ∀ r < regs, r ∉ [oK, qT1, oU, oT1, oT2, oT3, oAd, oX, oY, qM, oR] →
      rd M3 r = rd t.M r := fun r hr hn => by
    simp only [List.mem_cons, List.mem_nil_iff, or_false, not_or] at hn
    rw [k3 r hn.2.2.2.2.2.2.2.2.1 hn.2.2.2.2.2.2.2.2.2.1, k2 r hr (by simp [hn.1, hn.2.1, hn.2.2.1, hn.2.2.2.1,
      hn.2.2.2.2.1, hn.2.2.2.2.2.1, hn.2.2.2.2.2.2.1, hn.2.2.2.2.2.2.2.1]), k1 r hn.2.2.2.2.2.2.2.2.2.2 hn.2.2.2.2.2.2.2.2.2.1]
  -- the second load
  obtain ⟨x2, o2⟩ := ldC_sem I κ ⟨M3, s2.o⟩ i3
    (by rw [k3 _ (by decide) (by decide), k2 _ (by decide) (by decide)]; exact r1) m3
    (by rw [k23 _ (by decide) (by decide)]; exact hcb) (by rw [k23 _ (by decide) (by decide)]; exact hjj)
    (by rw [k23 _ (by decide) (by decide)]; exact hd) (by omega) hjl
  rw [semXIR_seq]
  generalize hs4 : semXIR I (ldC κ) ⟨M3, s2.o⟩ = s4 at x2 o2
  have i4 : Inv s4.M := hs4 ▸ inv_sem I (wf_ldC κ) i3
  have k4 : ∀ r < regs, r ∉ [oK, qT1, oU, oT1, oT2, oT3, oAd, oX] → rd s4.M r = rd M3 r := fun r hr hn =>
    hs4 ▸ keep_ldC I κ i3 hr hn
  have hh4 : ∀ y, regs ≤ y → rd s4.M y = rd t.M y := fun y hy => by
    rw [← hs4, hframeK I _ _ (loK_ldC κ) y hy]
    show rd M3 y = _
    rw [k3 _ (by simp only [oY, regs] at *; omega) (by simp only [qM, regs] at *; omega), hh2 y hy, hh1 y hy]
  have sz4 : s4.M.size = t.M.size := by rw [← hs4, size_sem]; show (runPrims _ _).size = _; rw [size_runPrims, sz2]
  have v2 : rd s4.M oX = G (q + j + 1) := by
    rw [x2, k3 _ (by have := regs_hAddr κ (ldIx cb jL Δ (q + j + 1)); simp only [oY, regs] at *; omega)
      (by have := regs_hAddr κ (ldIx cb jL Δ (q + j + 1)); simp only [qM, regs] at *; omega), hh2 _ (regs_hAddr κ _),
      hh1 _ (regs_hAddr κ _), hO.low _ (regs_hAddr κ _) (hlow _ (by omega))]
  -- block 3: the word, the buffer address's registers
  rw [semXIR_seq, semXIR_blk]
  have hs4' := i4.1
  simp only [regs] at hs4'
  set M5 := runPrims [.op .shl oX oX cOne, .op .shl oX oX qB, .op .add oX oY oX, .const oR (toWord bufB),
      .op .or oU qU qU] s4.M with hM5d
  have x5 : rd M5 oX = shWd G sh (q + j) := by
    simp only [hM5d, runPrims, List.foldl, Prim.run]
    simp (disch := (simp only [size_set, oX, oR, oU, qU, oY, qB, cOne] at *; omega)) only [rd_set_self, rd_set_ne]
    rw [v2, one_cOne i4, k4 qB (by decide) (by decide), k23 qB (by decide) (by decide), hbb, shl_shl_one _ hs8,
      k4 oY (by decide) (by decide), y3, shWd]
    rfl
  have r5 : rd M5 oR = toWord bufB := by
    simp only [hM5d, runPrims, List.foldl, Prim.run]
    simp (disch := (simp only [size_set, oX, oR, oU] at *; omega)) only [rd_set_self, rd_set_ne]
  have u5 : rd M5 oU = toWord j := by
    simp only [hM5d, runPrims, List.foldl, Prim.run]
    simp (disch := (simp only [size_set, oX, oR, oU, qU] at *; omega)) only [rd_set_self, rd_set_ne]
    rw [or_self_eval, k4 qU (by decide) (by decide), k23 qU (by decide) (by decide), hu]
  have i5 : Inv M5 := inv_sem I (P := .blk [.op .shl oX oX cOne, .op .shl oX oX qB, .op .add oX oY oX,
    .const oR (toWord bufB), .op .or oU qU qU]) (by simp +decide [WF, Prim.dst, oX, oR, oU]) i4
  have k5 : ∀ r, r ∉ [oX, oR, oU] → rd M5 r = rd s4.M r := fun r hr =>
    rd_runPrims_of_not_writes (fun p hp he => by
      simp only [List.mem_cons, List.mem_nil_iff, or_false] at hp
      simp only [List.mem_cons, List.mem_nil_iff, or_false, not_or] at hr
      rcases hp with rfl | rfl | rfl | rfl | rfl <;> simp only [Prim.dst] at he <;> subst he <;> simp_all) _
  -- the address block, the store
  rw [semXIR_seq, semXIR_blk, semXIR_seq]
  have i6 : Inv (runPrims (ldPs apB) M5) := inv_sem I (P := .blk (ldPs apB)) (s := ⟨M5, s4.o⟩) (by
    simp +decide only [ldPs, WF, Prim.dst, oK, oT1, oT2, oT3, oAd, List.mem_cons, List.mem_nil_iff,
      forall_eq_or_imp, forall_eq, or_false, and_true]) i5
  have ad6 : rd (runPrims (ldPs apB) M5) oAd = toWord (bufA j) := by
    rw [ldPs_oAd apB M5 i5, r5, u5]
    have := bufA_apB (u := j) (by simp only [nW] at hj; omega)
    rw [← this, toWord_toNat]
  have x6 : rd (runPrims (ldPs apB) M5) oX = shWd G sh (q + j) := by
    rw [ldPs_keep apB M5 (by decide), x5]
  have hBA := bufA_lt hj
  have hBA' := bufA_ge j
  simp only [semXIR]
  set M7 := storeM (runPrims (ldPs apB) M5) oAd oX with hM7d
  have st7 : ∀ i, i ≠ cTmp → rd M7 i = if i = bufA j then shWd G sh (q + j) else rd (runPrims (ldPs apB) M5) i :=
    fun i hi => by
      rw [hM7d, rd_storeM i6 ad6 (by simp only [regs, bufB] at *; omega) (by simp only [bufB] at *; omega)
        (by rw [size_runPrims, size_runPrims, sz4, hO.size]; omega) (by decide) (by decide) hi, x6]
  have i7 : Inv M7 := inv_sem I (P := .store oAd oX) (s := ⟨runPrims (ldPs apB) M5, s4.o⟩) (show oAd ≠ cTmp by decide) i6
  -- block 4 and the decrement
  refine ⟨⟨inv_decS (inv_sem I (P := .blk [.op .add qN qN cOne, .op .add qU qU cOne]) (s := ⟨M7, s4.o⟩)
      (by simp +decide [WF, Prim.dst, qN, qU]) i7) (by decide), ?_, ?_⟩, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp only [decS, size_set, size_runPrims, hM7d, hM5d, size_storeM, sz4, hO.size]
  · intro y hy1 hy2
    rw [rd_decS (by simp only [qLc, regs] at *; omega)]
    rw [rd_runPrims_of_not_writes (fun p hp he => by
      simp only [List.mem_cons, List.mem_nil_iff, or_false] at hp
      rcases hp with rfl | rfl <;> simp only [Prim.dst, qN, qU, regs] at he hy1 <;> omega)]
    rw [st7 y (by simp only [cTmp, regs] at *; omega), if_neg (by omega), ldPs_keep apB M5 (by
      simp only [List.mem_cons, List.mem_nil_iff, or_false, oK, oT1, oT2, oT3, oAd, regs] at *; omega),
      k5 y (by simp only [List.mem_cons, List.mem_nil_iff, or_false, oX, oR, oU, regs] at *; omega), hh4 y hy1,
      hO.low y hy1 hy2]
  · simp only [decS, ho, o2, o1]
  all_goals
    have kf : ∀ r, r < regs → r ∉ [oK, qT1, oU, oT1, oT2, oT3, oAd, oX, oY, qM, oR, cTmp] →
        rd M7 r = rd t.M r := fun r hr hn => by
      simp only [List.mem_cons, List.mem_nil_iff, or_false, not_or] at hn
      rw [st7 r hn.2.2.2.2.2.2.2.2.2.2.2, if_neg (by simp only [regs, bufB] at *; omega),
        ldPs_keep apB M5 (by simp [hn.1, hn.2.2.2.1, hn.2.2.2.2.1, hn.2.2.2.2.2.1, hn.2.2.2.2.2.2.1]),
        k5 r (by simp [hn.2.2.1, hn.2.2.2.2.2.2.2.1, hn.2.2.2.2.2.2.2.2.2.2.1]),
        k4 r hr (by simp [hn.1, hn.2.1, hn.2.2.1, hn.2.2.2.1, hn.2.2.2.2.1, hn.2.2.2.2.2.1, hn.2.2.2.2.2.2.1,
          hn.2.2.2.2.2.2.2.1]), k23 r hr (by simp [hn.1, hn.2.1, hn.2.2.1, hn.2.2.2.1, hn.2.2.2.2.1, hn.2.2.2.2.2.1,
          hn.2.2.2.2.2.2.1, hn.2.2.2.2.2.2.2.1, hn.2.2.2.2.2.2.2.2.1, hn.2.2.2.2.2.2.2.2.2.1,
          hn.2.2.2.2.2.2.2.2.2.2.1])]
    have hs7 : 256 ≤ M7.size := by
      simp only [hM7d, size_storeM, size_runPrims, hM5d, sz4]; omega
  · rw [rd_decS (by decide)]
    simp only [runPrims, List.foldl, Prim.run]
    simp (disch := (simp only [size_set, qN, qU, cOne] at *; omega)) only [rd_set_self, rd_set_ne]
    rw [kf qN (by decide) (by decide), hn, kf cOne (by decide) (by decide), one_cOne hO.inv, add_one_toWord]
    rfl
  · rw [rd_decS (by decide)]
    simp only [runPrims, List.foldl, Prim.run]
    simp (disch := (simp only [size_set, qN, qU, cOne] at *; omega)) only [rd_set_self, rd_set_ne]
    rw [kf qU (by decide) (by decide), hu, kf cOne (by decide) (by decide), one_cOne hO.inv, add_one_toWord]
  · rw [rd_decS (by decide)]
    simp only [runPrims, List.foldl, Prim.run]
    simp (disch := (simp only [size_set, qN, qU, qA] at *; omega)) only [rd_set_ne]
    rw [kf qA (by decide) (by decide), ha]
  · rw [rd_decS (by decide)]
    simp only [runPrims, List.foldl, Prim.run]
    simp (disch := (simp only [size_set, qN, qU, qB] at *; omega)) only [rd_set_ne]
    rw [kf qB (by decide) (by decide), hbb]
  · rw [rd_decS (by decide)]
    simp only [runPrims, List.foldl, Prim.run]
    simp (disch := (simp only [size_set, qN, qU, qCB] at *; omega)) only [rd_set_ne]
    rw [kf qCB (by decide) (by decide), hcb]
  · rw [rd_decS (by decide)]
    simp only [runPrims, List.foldl, Prim.run]
    simp (disch := (simp only [size_set, qN, qU, qJ] at *; omega)) only [rd_set_ne]
    rw [kf qJ (by decide) (by decide), hjj]
  · rw [rd_decS (by decide)]
    simp only [runPrims, List.foldl, Prim.run]
    simp (disch := (simp only [size_set, qN, qU, qDl] at *; omega)) only [rd_set_ne]
    rw [kf qDl (by decide) (by decide), hd]
  · intro u hu1
    have hbu := bufA_ge u
    rw [rd_decS (by simp only [qLc, bufB] at *; omega)]
    rw [rd_runPrims_of_not_writes (fun p hp he => by
      simp only [List.mem_cons, List.mem_nil_iff, or_false] at hp
      rcases hp with rfl | rfl <;> simp only [Prim.dst, qN, qU, bufB] at he hbu <;> omega)]
    rw [st7 _ (by simp only [cTmp, bufB] at *; omega)]
    by_cases huj : u = j
    · rw [if_pos (by rw [huj])]; rw [huj]
    · rw [if_neg (fun he => huj (bufA_inj (by omega) hj he)), ldPs_keep apB M5 (by
        simp only [List.mem_cons, List.mem_nil_iff, or_false, oK, oT1, oT2, oT3, oAd, bufB] at *; omega),
        k5 _ (by simp only [List.mem_cons, List.mem_nil_iff, or_false, oX, oR, oU, bufB] at *; omega),
        hh4 _ (by simp only [regs, bufB] at *; omega), hbuf u (by omega)]

theorem of_entryK {M₀ : Mem} {c n : ℕ} {K : Word} (hc : 4 < c) (hcr : c < regs) {s : St} (h : OF M₀ s) :
    OF M₀ ⟨entryK c n K s.M, s.o⟩ :=
  ⟨inv_entryK h.inv hc, (size_entryK ..).trans h.size, fun y h1 h2 =>
    (entryK_frame _ (by omega) (by simp only [cTmp, regs] at *; omega)).trans (h.low y h1 h2)⟩

theorem rlInv_entryK {κ : NodeKind} {M₀ : Mem} {o : Array Word} {cb jL Δ sh q : ℕ} {M : Mem} {K : Word}
    (h : RlInv κ M₀ o cb jL Δ sh q 0 ⟨M, o⟩) : RlInv κ M₀ o cb jL Δ sh q 0 ⟨entryK qLc qLn K M, o⟩ := by
  obtain ⟨hO, -, hn, hu, ha, hb, hc, hj, hd, -⟩ := h
  have e : ∀ r, r ≠ qLc → r ≠ cTmp → rd (entryK qLc qLn K M) r = rd M r := fun r h1 h2 =>
    entryK_frame _ (Ne.symm h1) (Ne.symm h2)
  exact ⟨of_entryK (by decide) (by decide) hO, rfl, by rw [e _ (by decide) (by decide)]; exact hn,
    by rw [e _ (by decide) (by decide)]; exact hu, by rw [e _ (by decide) (by decide)]; exact ha,
    by rw [e _ (by decide) (by decide)]; exact hb, by rw [e _ (by decide) (by decide)]; exact hc,
    by rw [e _ (by decide) (by decide)]; exact hj, by rw [e _ (by decide) (by decide)]; exact hd,
    fun u hu => absurd hu (Nat.not_lt_zero u)⟩

theorem wf_rlBody (κ : NodeKind) : WF (rlBody κ) := by
  refine ⟨by simp [WF, Prim.dst, oR, qM], wf_ldC κ, by simp [WF, Prim.dst, oY, qM], wf_ldC κ,
    by simp [WF, Prim.dst, oX, oR, oU], ?_, show oAd ≠ cTmp by decide, by simp [WF, Prim.dst, qN, qU]⟩
  simp +decide only [ldPs, WF, Prim.dst, oK, oT1, oT2, oT3, oAd, List.mem_cons, List.mem_nil_iff,
    forall_eq_or_imp, forall_eq, or_false, and_true]

theorem wf_realign (κ : NodeKind) : WF (realign κ) := by
  refine ⟨by simp +decide [WF], ⟨by decide, by decide, fun h => ?_, wf_rlBody κ⟩⟩
  have := writes_wrL _ _ h
  simp +decide [wrL, rlBody, ldC, ldw, ldPs, Prim.dst] at this

/-- **The realign loop** (`D = i·(segB − 1)`, `q = ⌊D/8⌋`, `s = D mod 8`): buffer word `u < nW` is the
shifted pair `shWd C s (q + u)` of the loader's words `C n` (H word `ldIx cb jL Δ n`); the heap below
the buffer and the output are kept. -/
theorem realign_sem (I : Array Word) (κ : NodeKind) {M₀ : Mem} {s : St} (hO : OF M₀ s)
    (hsz : bufB + 2 ^ 22 ≤ M₀.size) {i cb jL Δ : ℕ} (hi4 : i ≤ 4)
    (hi : rd s.M qI = toWord i) (hcb : rd s.M qCB = toWord cb) (hjr : rd s.M qJ = toWord jL)
    (hd : rd s.M qDl = toWord Δ) (hb : 2 ^ 23 + nW + 1 + cb + Δ < 2 ^ 64) (hjl : jL < 2 ^ 64)
    (hlow : ∀ n ≤ i * (N4c.segB - 1) / 8 + nW, hAddr κ (ldIx cb jL Δ n) < bufB) :
    OF M₀ (semXIR I (realign κ) s) ∧ (semXIR I (realign κ) s).o = s.o ∧
      ∀ u < nW, rd (semXIR I (realign κ) s).M (bufA u) =
        shWd (fun n => rd M₀ (hAddr κ (ldIx cb jL Δ n))) (i * (N4c.segB - 1) % 8) (i * (N4c.segB - 1) / 8 + u) := by
  have hs := hO.inv.1
  simp only [regs] at hs
  have hD : i * (N4c.segB - 1) < 2 ^ 23 := by simp only [N4c.segB]; omega
  set D := i * (N4c.segB - 1) with hDd
  rw [realign, semXIR_seq, semXIR_blk]
  set ps : List Prim := [.const qT1 (toWord (N4c.segB - 1)), .op .mul qT1 qI qT1, .const oK (toWord 3),
      .op .shr qN qT1 oK, .const oK (toWord 7), .op .and qA qT1 oK, .const oK (toWord 3),
      .op .shl qA qA oK, .op .sub qB c63 qA, .const qU 0, .const qLn (toWord nW)] with hps
  have c63v : rd s.M c63 = toWord 63 := hO.inv.2 3 (by decide)
  have kp : ∀ r, r ∉ [qT1, oK, qN, qA, qB, qU, qLn] → rd (runPrims ps s.M) r = rd s.M r := fun r hr =>
    rd_runPrims_of_not_writes (fun p hp he => by
      simp only [hps, List.mem_cons, List.mem_nil_iff, or_false] at hp
      simp only [List.mem_cons, List.mem_nil_iff, or_false, not_or] at hr
      rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
        simp only [Prim.dst] at he <;> subst he <;> simp_all) _
  have v : rd (runPrims ps s.M) qN = toWord (D / 8) ∧ rd (runPrims ps s.M) qA = toWord (8 * (D % 8)) ∧
      rd (runPrims ps s.M) qB = toWord (63 - 8 * (D % 8)) ∧ rd (runPrims ps s.M) qU = toWord 0 ∧
      rd (runPrims ps s.M) qLn = toWord nW := by
    simp only [hps, runPrims, List.foldl, Prim.run]
    simp (disch := (simp only [size_set, qT1, oK, qN, qA, qB, qU, qLn, qI, c63] at *; omega))
      only [rd_set_self, rd_set_ne]
    rw [hi, c63v, mul_toWord, ← hDd, shr_toWord (by omega) (by norm_num), show (7 : ℕ) = 2 ^ 3 - 1 from rfl,
      and_mask_toWord (by omega) (by norm_num), shl_toWord (by norm_num) (by omega),
      sub_toWord (by norm_num) (by omega)]
    refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> first | trivial | (congr 1; omega) | norm_num
  obtain ⟨vn, va, vb, vu, vl⟩ := v
  have i1 : Inv (runPrims ps s.M) := inv_sem I (P := .blk ps) (s := s) (by simp +decide [hps, WF]) hO.inv
  have O1 : OF M₀ ⟨runPrims ps s.M, s.o⟩ := of_loK I (P := .blk ps) (by simp +decide [hps, LoK, regs])
    (by simp +decide [hps, WF]) hO
  have h0 : RlInv κ M₀ s.o cb jL Δ (D % 8) (D / 8) 0 ⟨runPrims ps s.M, s.o⟩ :=
    ⟨O1, rfl, by rw [Nat.add_zero]; exact vn, vu, va, vb, by rw [kp _ (by decide)]; exact hcb,
      by rw [kp _ (by decide)]; exact hjr, by rw [kp _ (by decide)]; exact hd,
      fun u hu => absurd hu (Nat.not_lt_zero u)⟩
  have L := loopK_emit I (c := qLc) (n := qLn) (K := nW) (b := rlBody κ)
    (fun j t => RlInv κ M₀ s.o cb jL Δ (D % 8) (D / 8) j t) (fun _ => []) ⟨runPrims ps s.M, s.o⟩ i1
    (by decide) (by decide) (by decide) (by simp only [nW]; norm_num) vl (rlInv_entryK h0)
    (fun j t hj ht => ⟨by
        have e := (rlBody_step I κ (Nat.mod_lt _ (by norm_num)) (by omega) hjl hj hsz (fun n hn => hlow n hn) ht).o
        simp only [decS] at e; rw [e, ht.o]; simp, rlBody_step I κ (Nat.mod_lt _ (by norm_num)) (by omega) hjl hj hsz
        (fun n hn => hlow n hn) ht⟩)
  obtain ⟨-, Q⟩ := L
  exact ⟨Q.of, Q.o, fun u hu => Q.buf u hu⟩

end FR.X
