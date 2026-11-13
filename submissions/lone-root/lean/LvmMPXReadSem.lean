-- New for lvm2 roll 11 (M′, R11-X, `ext_eqM20` step (ii)): the semantics of the generic column reads `readGIR`.
-- Adapted from `LvmXRead.lean` (`cr_zero_sem`, `cr_copy_sem`) and `LvmXRead1.lean` (`cr1_capLd_sem`, `cr1_pos_sem`,
-- `cr1_posLoop`, `read1IR_sem4`, `read1IR_sem`) at a generic tree: `nPos` positions, `D` steps below the cap, rows of
-- `z` zero words and `occ` leaf words.
import LvmXRead1
import LvmMPXRead

/-!
# `readGIR_sem`: the generic column reads compute `readRowG`

After the index (`idxIR4`), `readGIR bX pL capW wB (2^ht) (ht − lv) z occ` stores `readRowG ht lv z occ L cap p` at
`wB + (z + occ) p + t` (`p < 2^ht`, `t < z + occ`); the index and the heap outside `[wB, wB + (z + occ) 2^ht)` are
kept. `readRowG` is the first-preimage reading of WP-5's `leafBytes` under `⟨ht, z + occ, lv, cap⟩`: `z` zero words,
then the leaf's first `occ` words.
-/

namespace Lvm.X

open RecursionFast

attribute [local irreducible] entryK storeM

/-! ## The pure reading -/

/-- The leaf bytes the log holds under the cap `cap` of a tree of height `ht` with a cap at level `lv`
(`none`: an erasure); WP-5's `leafBytes L ⟨ht, _, lv, cap⟩ p`. -/
def xLeafBytesG (ht lv : ℕ) (L : Log) (cap : List Digest) (p : ℕ) : Option (List UInt8) :=
  (cap[p % 2 ^ ht / 2 ^ (ht - lv)]?).bind fun v =>
    (xDescend L (ht - lv) v (p % 2 ^ ht)).bind fun d => (xFindA L d).map fun e => xQb e.1

/-- **The row the log holds** at position `p`: `z` zero words, then the leaf's first `occ` words; an erasure reads
as the row of the empty byte string. -/
def readRowG (ht lv z occ : ℕ) (L : Log) (cap : List Digest) (p : ℕ) : List BF64 :=
  List.replicate z 0 ++ xRowOf decLE occ ((xLeafBytesG ht lv L cap p).getD [])

@[simp] theorem readRowG_length (ht lv z occ : ℕ) (L : Log) (cap : List Digest) (p : ℕ) :
    (readRowG ht lv z occ L cap p).length = z + occ := by
  simp [readRowG, xRowOf]

theorem readRowG_getD (ht lv z occ : ℕ) (L : Log) (cap : List Digest) (p : ℕ) {t : ℕ} (ht' : t < z + occ) :
    (readRowG ht lv z occ L cap p).getD t 0 = if t < z then 0 else
      decLE ((((xLeafBytesG ht lv L cap p).getD []).drop (8 * (t - z))).take 8) := by
  rw [List.getD_eq_getElem _ _ (by rw [readRowG_length]; exact ht')]
  simp only [readRowG, xRowOf]
  rw [List.getElem_append]
  split_ifs with h1 h2 h2
  · simp
  · simp only [List.length_replicate] at h1; omega
  · simp only [List.length_replicate] at h1; omega
  · simp

/-- The reading at position `p` under the cap node `p / 2^D`, `D` steps down (`none` past the cap). -/
def crRdG (D : ℕ) (L : Log) (cap : List Digest) (p : ℕ) : Option (List UInt8) :=
  (cap[p / 2 ^ D]?).bind fun v => crRdN D L v p

theorem crRdG_eq {D : ℕ} {L : Log} {cap : List Digest} {p : ℕ} (hpc : p / 2 ^ D < cap.length) :
    crRdG D L cap p = crRdN D L (cap[p / 2 ^ D]'hpc) p := by
  unfold crRdG
  rw [List.getElem?_eq_getElem hpc]
  rfl

/-- On a position of the tree, the leaf bytes are the machine's reading. -/
theorem xLeafBytesG_eq {ht lv : ℕ} {L : Log} {cap : List Digest} {p : ℕ} (hp : p < 2 ^ ht) :
    xLeafBytesG ht lv L cap p = crRdG (ht - lv) L cap p := by
  unfold xLeafBytesG crRdG crRdN
  rw [Nat.mod_eq_of_lt hp]

/-- **Row word `t` of a reading** as the machine stores it: `z` zero words, then the leaf words. -/
def crGRowW (z : ℕ) (o : Option (List UInt8)) (t : ℕ) : Word :=
  if t < z then 0 else crLeafW o (t - z)

/-- **The stored word as a `K` element is the row's word.** -/
theorem crGRowW_readRowG {ht lv z occ : ℕ} (L : Log) (cap : List Digest) {p : ℕ} (hp : p < 2 ^ ht)
    {t : ℕ} (ht' : t < z + occ) :
    wK (crGRowW z (crRdG (ht - lv) L cap p) t) = (readRowG ht lv z occ L cap p).getD t 0 := by
  rw [readRowG_getD ht lv z occ L cap p ht', crGRowW, xLeafBytesG_eq hp]
  split_ifs
  · rfl
  · rw [wK_crLeafW]

/-! ## The cap node -/

/-- **The cap node's words**: after `crCapGPs capW D ; crLd4`, `rQ0 … rQ3` hold `cap[p / 2^D]`. -/
theorem crG_capLd_sem (I : Array Word) (s : St) (hM : Inv s.M) {capW D : ℕ} {cap : List Digest}
    (hD : D < 64) (hcw : capW + 4 * cap.length < 2 ^ 62)
    (hcap : ∀ e (he : e < cap.length), ∀ m < 4,
      I.getD (capW + 4 * e + m) 0 = (packBytes cap[e].toList).getD m 0)
    {p : ℕ} (hp : p < 2 ^ 62) (he : p / 2 ^ D < cap.length) (hP : rd s.M crP = toWord p) :
    [rd (semXIR I (.seq (.blk (crCapGPs capW D)) crLd4) s).M rQ0,
      rd (semXIR I (.seq (.blk (crCapGPs capW D)) crLd4) s).M rQ1,
      rd (semXIR I (.seq (.blk (crCapGPs capW D)) crLd4) s).M rQ2,
      rd (semXIR I (.seq (.blk (crCapGPs capW D)) crLd4) s).M rQ3] =
      packBytes (cap[p / 2 ^ D]'he).toList := by
  have hs := hM.1
  simp only [regs] at hs
  have hw : WF (.blk (crCapGPs capW D)) := by simp +decide only [crCapGPs, WF, Prim.dst, crK, crB,
    crTA, List.mem_cons, List.mem_nil_iff, forall_eq_or_imp, forall_eq, or_false, and_true]
  have hle : p / 2 ^ D ≤ p := Nat.div_le_self _ _
  have hA : rd (semXIR I (.blk (crCapGPs capW D)) s).M crTA = toWord (capW + 4 * (p / 2 ^ D)) := by
    simp only [crCapGPs, semXIR, runPrims, List.foldl, Prim.run]
    simp (disch := first | decide | (simp only [size_set, crK, crB, crTA]; omega)) only
      [rd_set_self, rd_set_ne]
    rw [hP, shr_toWord (by omega) hD, show (2 : Word) = toWord 2 from rfl]
    generalize p / 2 ^ D = e at hle ⊢
    rw [shl_toWord (by norm_num) (by omega), add_toWord]
    congr 1
    omega
  rw [semXIR_seq, cr_ld4_sem _ _ (inv_sem _ hw hM) (by omega) hA, cr_pk_digest_eq4,
    ← hcap _ he 0 (by decide), ← hcap _ he 1 (by decide), ← hcap _ he 2 (by decide),
    ← hcap _ he 3 (by decide)]
  simp only [Nat.add_zero]

/-! ## The row: zero prefix and copy -/

theorem crG_wf_zero (z : ℕ) : WF (crZeroG z) := by
  simp +decide only [crZeroG, crZeroBody, WF, Writes, Prim.dst, crV, crWA, crNw, crCw, cTmp, regs,
    List.mem_cons, List.mem_nil_iff, forall_eq_or_imp, forall_eq, or_false, and_true]

theorem crG_wf_copy (z occ : ℕ) : WF (crCopyG z occ) := by
  simp +decide only [crCopyG, crZeroG, crZeroBody, crCopyBody, WF, Writes, Prim.dst, crV, crMk, crK,
    crWA, crTA, cr8, crNw, crCw, crX, cTmp, regs, List.mem_cons, List.mem_nil_iff, forall_eq_or_imp,
    forall_eq, or_false, and_true]

/-- The registers the zero prefix keeps. -/
theorem crG_zero_nw (z : ℕ) {r : ℕ} (hr : r = crX ∨ r = crQe ∨ r = crP ∨ r = crTA ∨ r = cr8) :
    ¬ Writes (crZeroG z) r := by
  rcases hr with rfl | rfl | rfl | rfl | rfl <;>
  simp +decide only [crZeroG, crZeroBody, Writes, Prim.dst, crV, crWA, crNw, crCw, cTmp, crX, crQe,
    crP, crTA, cr8, List.mem_cons, List.mem_nil_iff, exists_eq_or_imp, exists_eq_left, or_false,
    not_or, exists_false, not_false_eq_true, and_self]

/-- **The row's zero prefix**: from `crWA = a`, cells `a … a + z − 1` get `0`; every other heap cell is kept;
`crWA` ends at `a + z`. -/
theorem crZeroG_sem (I : Array Word) (s : St) (hM : Inv s.M) {z a : ℕ} (ha : regs ≤ a)
    (ha2 : a + z < 2 ^ 64) (hsz : a + z ≤ s.M.size) (hA : rd s.M crWA = toWord a) :
    (∀ i < z, rd (semXIR I (crZeroG z) s).M (a + i) = 0) ∧
    (∀ y, regs ≤ y → (y < a ∨ a + (z) ≤ y) → rd (semXIR I (crZeroG z) s).M y = rd s.M y) ∧
    Inv (semXIR I (crZeroG z) s).M ∧ rd (semXIR I (crZeroG z) s).M crWA = toWord (a + (z)) := by
  have hs := hM.1
  simp only [regs] at hs ha
  rw [crZeroG, semXIR_seq]
  have w0 : WF (.blk [.const crV 0, .const crNw (toWord (z))]) := by
    simp +decide only [WF, Prim.dst, crV, crNw, List.mem_cons, List.mem_nil_iff, forall_eq_or_imp,
      forall_eq, or_false, and_true]
  have hM0 := inv_sem I w0 hM
  have z0 := size_sem I (.blk [.const crV 0, .const crNw (toWord (z))]) s
  have r0 : rd (semXIR I (.blk [.const crV 0, .const crNw (toWord (z))]) s).M crV = 0 ∧
      rd (semXIR I (.blk [.const crV 0, .const crNw (toWord (z))]) s).M crNw =
        toWord (z) ∧
      rd (semXIR I (.blk [.const crV 0, .const crNw (toWord (z))]) s).M crWA =
        toWord a := by
    simp only [semXIR, runPrims, List.foldl, Prim.run]
    refine ⟨?_, ?_, ?_⟩ <;>
    simp (disch := first | decide | (simp only [size_set, crV, crNw, crWA]; omega)) only
      [rd_set_self, rd_set_ne]
    all_goals first | rfl | exact hA
  have k0 : ∀ y, regs ≤ y →
      rd (semXIR I (.blk [.const crV 0, .const crNw (toWord (z))]) s).M y = rd s.M y :=
    hframe I _ s (by simp +decide only [Lo, Prim.dst, regs, crV, crNw, List.mem_cons,
      List.mem_nil_iff, forall_eq_or_imp, forall_eq, or_false, and_true])
  generalize semXIR I (.blk [.const crV 0, .const crNw (toWord (z))]) s = s0
    at hM0 z0 r0 k0
  obtain ⟨v0, n0, a0⟩ := r0
  let P : ℕ → St → Prop := fun j s' => Inv s'.M ∧ s'.M.size = s.M.size ∧
    rd s'.M crV = 0 ∧ rd s'.M crWA = toWord (a + j) ∧ (∀ i < j, rd s'.M (a + i) = 0) ∧
    (∀ y, regs ≤ y → (y < a ∨ a + j ≤ y) → rd s'.M y = rd s.M y)
  have hE : ∀ i, i ≠ crCw → i ≠ cTmp →
      rd (entryK crCw crNw (toWord (z)) s0.M) i = rd s0.M i :=
    fun i h1 h2 => entryK_frame _ (Ne.symm h1) (Ne.symm h2)
  have h0 : P 0 ⟨entryK crCw crNw (toWord (z)) s0.M, s0.o⟩ := by
    refine ⟨inv_entryK hM0 (by decide), by simp only [size_entryK, z0], ?_, ?_,
      fun i hi => absurd hi (by omega), fun y hy _ => ?_⟩ <;> dsimp only
    · rw [hE _ (by decide) (by decide), v0]
    · rw [hE _ (by decide) (by decide), a0, Nat.add_zero]
    · simp only [regs] at hy
      rw [hE _ (by simp only [crCw]; omega) (by simp only [cTmp]; omega),
        k0 y (by simp only [regs]; omega)]
  have hstep : ∀ j s', j < z → P j s' →
      P (j + 1) (decS crCw (semXIR I crZeroBody s')) := by
    rintro j s' hj ⟨i1, i2, i3, i4, i5, i6⟩
    rw [crZeroBody, semXIR_seq]
    obtain ⟨c1, c2, hM1⟩ := store_sem I s' i1 (p := crWA) (v := crV) (x := a + j) (by decide)
      (by decide) i4 (by simp only [regs]; omega) (by omega) (by omega)
    have z1 := size_sem I (.store crWA crV) s'
    generalize semXIR I (.store crWA crV) s' = s1 at c1 c2 hM1 z1
    have hs1 := hM1.1
    simp only [regs] at hs1
    have hdr : ∀ r, r < regs → r ≠ a + j := fun r hr => by simp only [regs] at hr; omega
    have b2 : ∀ r, r ≠ crWA → rd (semXIR I (.blk [.op .add crWA crWA cOne]) s1).M r = rd s1.M r :=
      fun r hr => by
        simp only [semXIR, runPrims, List.foldl, Prim.run]; exact rd_set_ne (Ne.symm hr)
    have hM2 := inv_sem I (P := .blk [.op .add crWA crWA cOne])
      (by simp +decide only [WF, Prim.dst, crWA, List.mem_cons, List.mem_nil_iff, forall_eq_or_imp,
        forall_eq, or_false, and_true]) hM1
    have hd : ∀ y, y ≠ crCw → rd (decS crCw (semXIR I (.blk [.op .add crWA crWA cOne]) s1)).M y =
        rd (semXIR I (.blk [.op .add crWA crWA cOne]) s1).M y := fun y hy => rd_decS (Ne.symm hy) _
    have hx : ∀ y, regs ≤ y → y ≠ crCw ∧ y ≠ crWA ∧ y ≠ cTmp := fun y hy => by
      simp only [regs, crCw, crWA, cTmp] at *; omega
    refine ⟨inv_decS hM2 (by decide), by rw [size_decS, size_sem, z1, i2], ?_, ?_,
      fun i hi => ?_, fun y hy hy2 => ?_⟩
    · rw [hd _ (by decide), b2 _ (by decide), c2 _ (hdr _ (by decide)) (by decide), i3]
    · rw [hd _ (by decide)]
      simp only [semXIR, runPrims, List.foldl, Prim.run]
      rw [rd_set_self (by simp only [crWA]; omega), c2 _ (hdr _ (by decide)) (by decide), i4,
        c2 _ (hdr _ (by decide)) (by decide), show rd s'.M cOne = 1 from i1.2 0 (by decide),
        add_one_toWord, Nat.add_assoc]
    · obtain ⟨x1, x2, x3⟩ := hx (a + i) (by simp only [regs]; omega)
      rw [hd _ x1, b2 _ x2]
      by_cases hij : i = j
      · subst hij; rw [c1, i3]
      · rw [c2 _ (by omega) x3, i5 i (by omega)]
    · obtain ⟨x1, x2, x3⟩ := hx y hy
      rw [hd _ x1, b2 _ x2, c2 _ (by omega) x3, i6 y hy (by omega)]
  have hfin := loopK_run I crZeroBody P s0 hM0 (c := crCw) (n := crNw) (K := z)
    (by decide) (by decide) (by decide) n0 (by omega) h0 hstep
  exact ⟨hfin.2.2.2.2.1, hfin.2.2.2.2.2, hfin.1, hfin.2.2.2.1⟩


/-- What the copy stores at row cell `i`: `0` in the first `z` cells, then copy word `i − z`. -/
def crCpRowG (I : Array Word) (x : Word) (ql z i : ℕ) : Word :=
  if i < z then 0 else crCpW I x ql (i - z)

/-- **The copy**: from `crX = x`, `crQe = ql`, `crWA = a`, cells `a … a + z + occ − 1` get `crCpRowG I x ql z ·`
(`z` zero words, then copy words `0 … occ − 1`); every other heap cell is kept; `crWA` ends at `a + z + occ`. -/
theorem crCopyG_sem (I : Array Word) (s : St) (hM : Inv s.M) {x : Word} {ql z occ a : ℕ}
    (hql : ql < 2 ^ 64) (ho : occ < 2 ^ 60) (ha : regs ≤ a) (ha2 : a + (z + occ) + 2 < 2 ^ 64)
    (hsz : a + (z + occ) ≤ s.M.size)
    (hX : rd s.M crX = x) (hQ : rd s.M crQe = toWord ql) (hA : rd s.M crWA = toWord a) :
    (∀ i < z + occ, rd (semXIR I (crCopyG z occ) s).M (a + i) = crCpRowG I x ql z i) ∧
    (∀ y, regs ≤ y → (y < a ∨ a + (z + occ) ≤ y) → rd (semXIR I (crCopyG z occ) s).M y = rd s.M y) ∧
    Inv (semXIR I (crCopyG z occ) s).M ∧ rd (semXIR I (crCopyG z occ) s).M crWA = toWord (a + (z + occ)) ∧
    rd (semXIR I (crCopyG z occ) s).M crP = rd s.M crP := by
  -- the zero prefix
  obtain ⟨z1, z2, hMz, az⟩ := crZeroG_sem I s hM (z := z) ha (by omega) (by omega) hA
  have fz : ∀ r, (r = crX ∨ r = crQe ∨ r = crP ∨ r = crTA ∨ r = cr8) →
      rd (semXIR I (crZeroG z) s).M r = rd s.M r := fun r hr =>
    frame I _ s (crG_wf_zero z) hM r (by rcases hr with rfl | rfl | rfl | rfl | rfl <;> decide)
      (crG_zero_nw z hr)
  have hszz := size_sem I (crZeroG z) s
  rw [crCopyG, semXIR_seq]
  generalize semXIR I (crZeroG z) s = s1 at z1 z2 hMz az fz hszz
  have hX1 : rd s1.M crX = x := (fz _ (.inl rfl)).trans hX
  have hQ1 : rd s1.M crQe = toWord ql := (fz _ (.inr (.inl rfl))).trans hQ
  have hP1 : rd s1.M crP = rd s.M crP := fz _ (.inr (.inr (.inl rfl)))
  -- the copy of `occ` words to `a + z`
  have hs := hMz.1
  have h1 : rd s1.M cOne = 1 := hMz.2 0 (by decide)
  simp only [regs] at hs
  have wf0 : WF (.blk [.op .add crTA crX cOne, .const cr8 0, .const crNw (toWord occ)]) := by
    simp +decide only [WF, Prim.dst, crTA, cr8, crNw, List.mem_cons, List.mem_nil_iff,
      forall_eq_or_imp, forall_eq, or_false, and_true]
  have hM0 := inv_sem I wf0 hMz
  have hH0 := hframe I (.blk [.op .add crTA crX cOne, .const cr8 0, .const crNw (toWord occ)]) s1
    (by simp +decide only [Lo, Prim.dst, regs, crTA, cr8, crNw, List.mem_cons, List.mem_nil_iff,
      forall_eq_or_imp, forall_eq, or_false, and_true])
  have hsz0 := size_sem I (.blk [.op .add crTA crX cOne, .const cr8 0, .const crNw (toWord occ)])
    s1
  have r0 : rd (semXIR I (.blk [.op .add crTA crX cOne, .const cr8 0, .const crNw (toWord occ)])
        s1).M crTA = x + toWord (1 + 0) ∧
      rd (semXIR I (.blk [.op .add crTA crX cOne, .const cr8 0, .const crNw (toWord occ)])
        s1).M cr8 = toWord (8 * 0) ∧
      rd (semXIR I (.blk [.op .add crTA crX cOne, .const cr8 0, .const crNw (toWord occ)])
        s1).M crNw = toWord occ ∧
      rd (semXIR I (.blk [.op .add crTA crX cOne, .const cr8 0, .const crNw (toWord occ)])
        s1).M crQe = toWord ql ∧
      rd (semXIR I (.blk [.op .add crTA crX cOne, .const cr8 0, .const crNw (toWord occ)])
        s1).M crWA = toWord (a + z + 0) ∧
      rd (semXIR I (.blk [.op .add crTA crX cOne, .const cr8 0, .const crNw (toWord occ)])
        s1).M crP = rd s1.M crP := by
    simp only [semXIR, runPrims, List.foldl, Prim.run]
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    simp (disch := first | decide | (simp only [size_set, crTA, cr8, crNw]; omega)) only
      [rd_set_self, rd_set_ne]
    all_goals first | rfl | exact hQ1 | exact az | (rw [hX1, h1]; all_goals rfl)
  rw [semXIR_seq]
  generalize semXIR I (.blk [.op .add crTA crX cOne, .const cr8 0, .const crNw (toWord occ)])
    s1 = s0 at hM0 hH0 hsz0 r0
  obtain ⟨t0, e0, n0, q0, a0, p0⟩ := r0
  have hE : ∀ i, i ≠ crCw → i ≠ cTmp → rd (entryK crCw crNw (toWord occ) s0.M) i = rd s0.M i :=
    fun i h1 h2 => entryK_frame _ (Ne.symm h1) (Ne.symm h2)
  have hcnt : rd (entryK crCw crNw (toWord occ) s0.M) crCw = toWord occ :=
    entryK_count hM0 (by decide) (by decide) (by decide) n0
  have hME := inv_entryK (c := crCw) (n := crNw) (K := toWord occ) hM0 (by decide)
  have e : semXIR I (.loopK crCw crNw (toWord occ) crCopyBody) s0 =
      iterL (semXIR I crCopyBody) crCw occ ⟨entryK crCw crNw (toWord occ) s0.M, s0.o⟩ := by
    simp only [semXIR, hcnt, toNat_toWord (show occ < 2 ^ 64 by omega)]
  rw [e]
  have hy : ∀ y, regs ≤ y → y ≠ crCw ∧ y ≠ cTmp := fun y hy => by
    simp only [crCw, cTmp, regs] at *; omega
  obtain ⟨d1, d2, d3, d4, d5⟩ := cr_copyLoop I (a := a + z) (nw := occ) hql
    (by simp only [regs] at ha ⊢; omega) (by omega) ho occ 0 ⟨entryK crCw crNw (toWord occ) s0.M, s0.o⟩
    (by omega) hME (by simp only [size_entryK]; omega) (by rw [hE _ (by decide) (by decide), a0])
    (by rw [hE _ (by decide) (by decide), t0]) (by rw [hE _ (by decide) (by decide), e0])
    (by rw [hE _ (by decide) (by decide), q0])
  have back : ∀ y, regs ≤ y → (y < a + z ∨ a + (z + occ) ≤ y) →
      rd (iterL (semXIR I crCopyBody) crCw occ ⟨entryK crCw crNw (toWord occ) s0.M, s0.o⟩).M y =
        rd s1.M y := fun y hy1 hy2 => by
    rw [d2 y hy1 (by omega)]
    show rd (entryK crCw crNw (toWord occ) s0.M) y = rd s1.M y
    rw [hE y (hy y hy1).1 (hy y hy1).2, hH0 y hy1]
  refine ⟨fun i hi => ?_, fun y hy1 hy2 => ?_, d3, ?_, ?_⟩
  · rw [crCpRowG]
    split_ifs with h
    · rw [back _ (by simp only [regs] at ha ⊢; omega) (.inl (by omega)), z1 i h]
    · rw [show a + i = a + z + (i - z) by omega]
      exact d1 _ (by omega) (by omega)
  · rw [back y hy1 (by omega), z2 y hy1 (by omega)]
  · rw [d4, show a + z + (0 + occ) = a + (z + occ) by omega]
  · rw [d5]
    show rd (entryK crCw crNw (toWord occ) s0.M) crP = rd s.M crP
    rw [hE _ (by decide) (by decide), p0, hP1]

section PosG

variable {nPos D z occ : ℕ}
variable {c : Digest} {π : Proof} {L : Log} {bX pL : ℕ}
variable (hbX : regs ≤ bX) (hbX2 : bX ≤ 2 ^ 60) (hpL : pL ≤ 2 ^ 60)
include hbX hbX2 hpL

/-- **One position**: the row of position `p` at `a … a + z + occ − 1`; `crP := p + 1`,
`crWA := a + (z + occ)`; every other heap cell kept. -/
theorem crPosG_sem (hD : RdDom pL c π L) {Xi : ℕ → Word} (hX : Sorted4 pL (crTape c π L) L Xi)
    (s : St) (hM : Inv s.M) (hXs : ∀ a < L.length, rd s.M (bX + a) = Xi a) {capW : ℕ}
    {cap : List Digest} (hcl : ∀ q < nPos, q / 2 ^ D < cap.length)
    (hcw : capW + 4 * cap.length < 2 ^ 62) (hn : nPos < 2 ^ 62) (hD64 : D < 64) (ho : occ < 2 ^ 60)
    (hcap : ∀ e (he : e < cap.length), ∀ m < 4,
      (crTape c π L).getD (capW + 4 * e + m) 0 = (packBytes cap[e].toList).getD m 0)
    {p a : ℕ} (hp : p < nPos) (hP : rd s.M crP = toWord p) (hA : rd s.M crWA = toWord a)
    (ha : regs ≤ a) (ha2 : a + (z + occ) + 2 < 2 ^ 64) (hsz : a + (z + occ) ≤ s.M.size) :
    (∀ t < (z + occ), rd (semXIR (crTape c π L) (crPosG bX pL capW D z occ) s).M (a + t) =
      crGRowW z (crRdG D L cap p) t) ∧
    (∀ y, regs ≤ y → (y < a ∨ a + (z + occ) ≤ y) →
      rd (semXIR (crTape c π L) (crPosG bX pL capW D z occ) s).M y = rd s.M y) ∧
    Inv (semXIR (crTape c π L) (crPosG bX pL capW D z occ) s).M ∧
    rd (semXIR (crTape c π L) (crPosG bX pL capW D z occ) s).M crWA = toWord (a + (z + occ)) ∧
    rd (semXIR (crTape c π L) (crPosG bX pL capW D z occ) s).M crP = toWord (p + 1) := by
  set I := crTape c π L with hI
  have hpc : p / 2 ^ D < cap.length := hcl p hp
  have hs := hM.1
  simp only [regs] at hs
  -- the cap node
  have wf1 : WF (.seq (.blk (crCapGPs capW D)) crLd4) := ⟨by simp +decide only [crCapGPs, WF,
    Prim.dst, crK, crB, crTA, List.mem_cons, List.mem_nil_iff, forall_eq_or_imp, forall_eq,
    or_false, and_true], cr_wf_ld4⟩
  have lo1 : Lo (.seq (.blk (crCapGPs capW D)) crLd4) := ⟨by simp +decide only [crCapGPs, Lo,
    Prim.dst, regs, crK, crB, crTA, List.mem_cons, List.mem_nil_iff, forall_eq_or_imp, forall_eq,
    or_false, and_true], cr_lo_ld4⟩
  have q1 := crG_capLd_sem I s hM hD64 hcw hcap (by omega) hpc hP
  have hH1 := hframe I _ s lo1
  have f1 : ∀ r, r = crP ∨ r = crWA → rd (semXIR I (.seq (.blk (crCapGPs capW D)) crLd4) s).M r =
      rd s.M r := fun r hr => frame I _ s wf1 hM r (by rcases hr with rfl | rfl <;> decide)
    (by rcases hr with rfl | rfl <;>
      simp +decide only [crCapGPs, crLd4, Writes, Prim.dst, crK, crB, crTA, rQ0, rQ1, rQ2, rQ3,
        crP, crWA, List.mem_cons, List.mem_nil_iff, exists_eq_or_imp, exists_eq_left, or_false])
  have hM1 := inv_sem I wf1 hM
  have hsz1 := size_sem I (.seq (.blk (crCapGPs capW D)) crLd4) s
  rw [crPosG, semXIR_seq]
  generalize semXIR I (.seq (.blk (crCapGPs capW D)) crLd4) s = s1 at q1 hH1 f1 hM1 hsz1
  -- `crOk := 1`, the height count
  have wf2 : WF (.blk [.const crOk 1, .const crNH (toWord D)]) := by simp +decide only [WF,
    Prim.dst, crOk, crNH, List.mem_cons, List.mem_nil_iff, forall_eq_or_imp, forall_eq, or_false,
    and_true]
  have hs1 := hM1.1
  simp only [regs] at hs1
  have r2 : ∀ r, r ≠ crOk → r ≠ crNH →
      rd (semXIR I (.blk [.const crOk 1, .const crNH (toWord D)]) s1).M r = rd s1.M r :=
    fun r h1 h2 => by
      simp only [semXIR, runPrims, List.foldl, Prim.run]
      rw [rd_set_ne (Ne.symm h2), rd_set_ne (Ne.symm h1)]
  have o2 : rd (semXIR I (.blk [.const crOk 1, .const crNH (toWord D)]) s1).M crOk = 1 ∧
      rd (semXIR I (.blk [.const crOk 1, .const crNH (toWord D)]) s1).M crNH = toWord D := by
    simp only [semXIR, runPrims, List.foldl, Prim.run]
    refine ⟨?_, ?_⟩ <;>
    simp (disch := first | decide | (simp only [size_set, crOk, crNH]; omega)) only
      [rd_set_self, rd_set_ne]
  have hM2 := inv_sem I wf2 hM1
  have hsz2 := size_sem I (.blk [.const crOk 1, .const crNH (toWord D)]) s1
  rw [semXIR_seq]
  generalize semXIR I (.blk [.const crOk 1, .const crNH (toWord D)]) s1 = s2 at r2 o2 hM2 hsz2
  have hW2 : crWalkN D L (cap[p / 2 ^ D]'hpc) p D s2.M := by
    refine .inl ⟨o2.1, cap[p / 2 ^ D]'hpc, ?_, rfl⟩
    rw [r2 rQ0 (by decide) (by decide), r2 rQ1 (by decide) (by decide),
      r2 rQ2 (by decide) (by decide), r2 rQ3 (by decide) (by decide)]
    exact q1
  have hH2 : ∀ y, regs ≤ y → rd s2.M y = rd s.M y := fun y hy => by
    rw [r2 y (by simp only [crOk, regs] at *; omega) (by simp only [crNH, regs] at *; omega),
      hH1 y hy]
  -- the height loop
  have hE : ∀ i, i ≠ crHc → i ≠ cTmp → rd (entryK crHc crNH (toWord D) s2.M) i = rd s2.M i :=
    fun i h1 h2 => entryK_frame _ (Ne.symm h1) (Ne.symm h2)
  have hcnt : rd (entryK crHc crNH (toWord D) s2.M) crHc = toWord D :=
    entryK_count hM2 (by decide) (by decide) (by decide) o2.2
  have hME := inv_entryK (c := crHc) (n := crNH) (K := toWord D) hM2 (by decide)
  have e : semXIR I (.loopK crHc crNH (toWord D) (crNode bX pL)) s2 =
      iterL (semXIR I (crNode bX pL)) crHc D ⟨entryK crHc crNH (toWord D) s2.M, s2.o⟩ := by
    simp only [semXIR, hcnt, toNat_toWord (show D < 2 ^ 64 by omega)]
  have hyE : ∀ y, regs ≤ y → y ≠ crHc ∧ y ≠ cTmp := fun y hy => by
    simp only [crHc, cTmp, regs] at *; omega
  have hWE : crWalkN D L (cap[p / 2 ^ D]'hpc) p D (entryK crHc crNH (toWord D) s2.M) := by
    unfold crWalkN at hW2 ⊢
    rw [hE crOk (by decide) (by decide), hE rQ0 (by decide) (by decide),
      hE rQ1 (by decide) (by decide), hE rQ2 (by decide) (by decide),
      hE rQ3 (by decide) (by decide)]
    exact hW2
  have hxr : ∀ a', regs ≤ bX + a' := fun a' => by simp only [regs] at hbX ⊢; omega
  have hXE : ∀ a' < L.length, rd (entryK crHc crNH (toWord D) s2.M) (bX + a') = Xi a' :=
    fun a' ha' => by
      rw [hE _ (hyE _ (hxr a')).1 (hyE _ (hxr a')).2, hH2 _ (hxr a'), hXs a' ha']
  have hPE : rd (entryK crHc crNH (toWord D) s2.M) crP = toWord p := by
    rw [hE _ (by decide) (by decide), r2 _ (by decide) (by decide), f1 _ (.inl rfl), hP]
  obtain ⟨n1, n2, n3, n4, n5⟩ := cr_nodeLoopN hbX hbX2 hpL hD hX (by omega) D
    ⟨entryK crHc crNH (toWord D) s2.M, s2.o⟩ hD64 hME hXE hPE hcnt hWE
  have hH3 : ∀ y, regs ≤ y →
      rd (iterL (semXIR I (crNode bX pL)) crHc D ⟨entryK crHc crNH (toWord D) s2.M, s2.o⟩).M y =
        rd s.M y := fun y hy => by
    rw [n3 y hy]
    show rd (entryK crHc crNH (toWord D) s2.M) y = _
    rw [hE y (hyE y hy).1 (hyE y hy).2, hH2 y hy]
  have hP3 : rd (iterL (semXIR I (crNode bX pL)) crHc D
      ⟨entryK crHc crNH (toWord D) s2.M, s2.o⟩).M crP = toWord p := by
    rw [n4]
    show rd (entryK crHc crNH (toWord D) s2.M) crP = _
    rw [hE _ (by decide) (by decide), r2 _ (by decide) (by decide), f1 _ (.inl rfl), hP]
  have hA3 : rd (iterL (semXIR I (crNode bX pL)) crHc D
      ⟨entryK crHc crNH (toWord D) s2.M, s2.o⟩).M crWA = toWord a := by
    rw [n5]
    show rd (entryK crHc crNH (toWord D) s2.M) crWA = _
    rw [hE _ (by decide) (by decide), r2 _ (by decide) (by decide), f1 _ (.inr rfl), hA]
  have hsz3 : (iterL (semXIR I (crNode bX pL)) crHc D
      ⟨entryK crHc crNH (toWord D) s2.M, s2.o⟩).M.size = s.M.size := by
    rw [size_iterL (fun s' => size_sem I (crNode bX pL) s')]
    show (entryK crHc crNH (toWord D) s2.M).size = _
    rw [size_entryK, hsz2, hsz1]
  rw [semXIR_seq, e]
  generalize iterL (semXIR I (crNode bX pL)) crHc D ⟨entryK crHc crNH (toWord D) s2.M, s2.o⟩ = s3
    at n1 n2 hH3 hP3 hA3 hsz3
  -- the leaf
  obtain ⟨ql, hql, c1, c2⟩ := cr_leaf_semN hbX hbX2 hpL hD hX s3 n2 (fun a' ha' => by
    rw [hH3 _ (by simp only [regs] at hbX ⊢; omega), hXs a' ha']) n1
  have hH4 := hframeK I (crLeaf bX pL) s3 cr_loK_leaf
  have hP4 : rd (semXIR I (crLeaf bX pL) s3).M crP = toWord p := by
    rw [frame I _ s3 (cr_wf_leaf (bX := bX) (pL := pL)) n2 crP (by decide)
      (cr_leaf_nw (.inl rfl)), hP3]
  have hA4 : rd (semXIR I (crLeaf bX pL) s3).M crWA = toWord a := by
    rw [frame I _ s3 (cr_wf_leaf (bX := bX) (pL := pL)) n2 crWA (by decide)
      (cr_leaf_nw (.inr rfl)), hA3]
  have hM4 := inv_sem I (cr_wf_leaf (bX := bX) (pL := pL)) n2
  have hsz4 := size_sem I (crLeaf bX pL) s3
  rw [semXIR_seq]
  generalize semXIR I (crLeaf bX pL) s3 = s4 at c1 c2 hH4 hP4 hA4 hM4 hsz4
  -- the copy
  obtain ⟨k1, k2, k3, k4, k5⟩ := crCopyG_sem I s4 hM4 hql ho ha ha2 (by omega) rfl c1 hA4
  rw [semXIR_seq]
  generalize semXIR I (crCopyG z occ) s4 = s5 at k1 k2 k3 k4 k5
  have hs5 := k3.1
  simp only [regs] at hs5
  have hc5 : rd s5.M cOne = 1 := k3.2 0 (by decide)
  have wf6 : WF (.blk [.op .add crP crP cOne]) := by simp +decide only [WF, Prim.dst, crP]
  have r6 : ∀ r, r ≠ crP → rd (semXIR I (.blk [.op .add crP crP cOne]) s5).M r = rd s5.M r :=
    fun r hr => by
      simp only [semXIR, runPrims, List.foldl, Prim.run]; exact rd_set_ne (Ne.symm hr)
  refine ⟨fun t ht => ?_, fun y hy1 hy2 => ?_, inv_sem I wf6 k3, ?_, ?_⟩
  · rw [r6 _ (by simp only [crP, regs] at *; omega), k1 t ht, crCpRowG, crGRowW]
    split_ifs
    · rfl
    · rw [c2, crRdG_eq hpc]
  · rw [r6 _ (by simp only [crP, regs] at *; omega), k2 y hy1 hy2, hH4 y hy1, hH3 y hy1]
  · rw [r6 _ (by decide), k4]
  · simp only [semXIR, runPrims, List.foldl, Prim.run]
    rw [rd_set_self (by simp only [crP]; omega), k5, hP4, hc5, add_one_toWord]

/-- **The position loop**: `m` positions from `j` fill their rows (`z` zero words, then the leaf words) at
`wB + (z + occ) q`. -/
theorem crPosG_loop (hD : RdDom pL c π L) {Xi : ℕ → Word} (hX : Sorted4 pL (crTape c π L) L Xi)
    {capW wB : ℕ} {cap : List Digest} (hcl : ∀ q < nPos, q / 2 ^ D < cap.length)
    (hcw : capW + 4 * cap.length < 2 ^ 62) (hn : nPos < 2 ^ 62) (hD64 : D < 64) (ho : occ < 2 ^ 60)
    (hcap : ∀ e (he : e < cap.length), ∀ m < 4,
      (crTape c π L).getD (capW + 4 * e + m) 0 = (packBytes cap[e].toList).getD m 0)
    (hwB : regs ≤ wB) (hwB2 : wB + (z + occ) * nPos ≤ bX) :
    ∀ (m j : ℕ) (s : St), j + m ≤ nPos → Inv s.M → bX ≤ s.M.size →
      (∀ a < L.length, rd s.M (bX + a) = Xi a) → rd s.M crP = toWord j →
      rd s.M crWA = toWord (wB + (z + occ) * j) →
      (∀ q, j ≤ q → q < j + m → ∀ t < (z + occ),
        rd (iterL (semXIR (crTape c π L) (crPosG bX pL capW D z occ)) crCp m s).M (wB + (z + occ) * q + t) =
          crGRowW z (crRdG D L cap q) t) ∧
      (∀ y, regs ≤ y → (y < wB + (z + occ) * j ∨ wB + (z + occ) * (j + m) ≤ y) →
        rd (iterL (semXIR (crTape c π L) (crPosG bX pL capW D z occ)) crCp m s).M y = rd s.M y) ∧
      Inv (iterL (semXIR (crTape c π L) (crPosG bX pL capW D z occ)) crCp m s).M
  | 0, j, s, _, hM, _, _, _, _ => ⟨fun q h1 h2 => by omega, fun _ _ _ => rfl, hM⟩
  | m + 1, j, s, hjm, hM, hsz, hXs, hP, hA => by
    set I := crTape c π L
    have e1 : (z + occ) * (j + 1) = (z + occ) * j + (z + occ) := Nat.mul_succ (z + occ) j
    have hmj : (z + occ) * (j + 1) ≤ (z + occ) * nPos := Nat.mul_le_mul_left _ (by omega)
    obtain ⟨b1, b2, b3, b4, b5⟩ := crPosG_sem (z := z) (occ := occ) hbX hbX2 hpL hD hX s hM hXs hcl hcw hn hD64 ho hcap (p := j)
      (a := wB + (z + occ) * j) (by omega) hP hA (by omega) (by omega) (by omega)
    have hM' : Inv (decS crCp (semXIR I (crPosG bX pL capW D z occ) s)).M := inv_decS b3 (by decide)
    have dk : ∀ r, r ≠ crCp → rd (decS crCp (semXIR I (crPosG bX pL capW D z occ) s)).M r =
        rd (semXIR I (crPosG bX pL capW D z occ) s).M r := fun r hr => rd_decS (Ne.symm hr) _
    have hy : ∀ y, regs ≤ y → y ≠ crCp := fun y hy => by simp only [crCp, regs] at *; omega
    have hsz' : bX ≤ (decS crCp (semXIR I (crPosG bX pL capW D z occ) s)).M.size := by
      rw [size_decS, size_sem]; exact hsz
    obtain ⟨d1, d2, d3⟩ := crPosG_loop hD hX hcl hcw hn hD64 ho hcap hwB hwB2 m (j + 1) _ (by omega) hM'
      hsz'
      (fun a ha => by
        rw [dk _ (hy _ (by simp only [regs] at hbX ⊢; omega)),
          b2 _ (by simp only [regs] at hbX ⊢; omega) (.inr (by omega)), hXs a ha])
      (by rw [dk _ (by decide), b5])
      (by rw [dk _ (by decide), b4, e1, Nat.add_assoc])
    have e3 : (z + occ) * (j + 1 + m) = (z + occ) * (j + (m + 1)) := by
      rw [show j + 1 + m = j + (m + 1) by omega]
    rw [e3] at d2
    simp only [iterL]
    refine ⟨fun q h1 h2 t ht => ?_, fun y hy1 hy2 => ?_, d3⟩
    · by_cases hq : q = j
      · subst hq
        rw [d2 _ (by simp only [regs] at hwB ⊢; omega) (.inl (by omega)), dk _ (hy _ (by simp only [regs] at hwB ⊢; omega)), b1 t ht]
      · exact d1 q (by omega) (by omega) t ht
    · have h2 : y < wB + (z + occ) * (j + 1) ∨ wB + (z + occ) * (j + (m + 1)) ≤ y := by
        rcases hy2 with h | h
        · exact .inl (by rw [e1]; omega)
        · exact .inr h
      have h3 : y < wB + (z + occ) * j ∨ wB + (z + occ) * j + (z + occ) ≤ y := by
        rcases hy2 with h | h
        · exact .inl h
        · refine .inr (le_trans ?_ h)
          rw [Nat.add_assoc, ← e1]
          exact Nat.add_le_add_left (Nat.mul_le_mul_left _ (by omega)) _
      rw [d2 _ hy1 h2, dk _ (hy _ hy1), b2 _ hy1 h3]

/-- **The column reads on a sorted index**: `readGIR bX pL capW wB nPos D z occ` stores at `wB + (z + occ) p + t`
row word `t` of the reading at position `p < nPos` and keeps every heap cell outside `[wB, wB + (z + occ) nPos)`. -/
theorem readGIR_sem4 (hD : RdDom pL c π L) {Xi : ℕ → Word} (hX : Sorted4 pL (crTape c π L) L Xi)
    (s : St) (hM : Inv s.M) (hXs : ∀ a < L.length, rd s.M (bX + a) = Xi a) {capW wB : ℕ}
    {cap : List Digest} (hcl : ∀ q < nPos, q / 2 ^ D < cap.length)
    (hcw : capW + 4 * cap.length < 2 ^ 62) (hn : nPos < 2 ^ 62) (hD64 : D < 64) (ho : occ < 2 ^ 60)
    (hcap : ∀ e (he : e < cap.length), ∀ m < 4,
      (crTape c π L).getD (capW + 4 * e + m) 0 = (packBytes cap[e].toList).getD m 0)
    (hwB : regs ≤ wB) (hwB2 : wB + (z + occ) * nPos ≤ bX) (hsz : bX ≤ s.M.size) :
    (∀ p < nPos, ∀ t < (z + occ),
      rd (semXIR (crTape c π L) (readGIR bX pL capW wB nPos D z occ) s).M (wB + (z + occ) * p + t) =
        crGRowW z (crRdG D L cap p) t) ∧
    (∀ y, regs ≤ y → (y < wB ∨ wB + (z + occ) * nPos ≤ y) →
      rd (semXIR (crTape c π L) (readGIR bX pL capW wB nPos D z occ) s).M y = rd s.M y) ∧
    Inv (semXIR (crTape c π L) (readGIR bX pL capW wB nPos D z occ) s).M := by
  set I := crTape c π L
  have hs := hM.1
  simp only [regs] at hs
  have wf0 : WF (.blk [.const crP 0, .const crWA (toWord wB), .const crNp (toWord (nPos))]) := by
    simp +decide only [WF, Prim.dst, crP, crWA, crNp, List.mem_cons, List.mem_nil_iff,
      forall_eq_or_imp, forall_eq, or_false, and_true]
  have r0 : rd (semXIR I (.blk [.const crP 0, .const crWA (toWord wB),
        .const crNp (toWord (nPos))]) s).M crP = toWord 0 ∧
      rd (semXIR I (.blk [.const crP 0, .const crWA (toWord wB),
        .const crNp (toWord (nPos))]) s).M crWA = toWord (wB + (z + occ) * 0) ∧
      rd (semXIR I (.blk [.const crP 0, .const crWA (toWord wB),
        .const crNp (toWord (nPos))]) s).M crNp = toWord (nPos) := by
    simp only [semXIR, runPrims, List.foldl, Prim.run]
    refine ⟨?_, ?_, ?_⟩ <;>
    simp (disch := first | decide | (simp only [size_set, crP, crWA, crNp]; omega)) only
      [rd_set_self, rd_set_ne]
    all_goals rfl
  have hH0 := hframe I (.blk [.const crP 0, .const crWA (toWord wB),
    .const crNp (toWord (nPos))]) s
    (by simp +decide only [Lo, Prim.dst, regs, crP, crWA, crNp, List.mem_cons, List.mem_nil_iff,
      forall_eq_or_imp, forall_eq, or_false, and_true])
  have hM0 := inv_sem I wf0 hM
  have hsz0 := size_sem I (.blk [.const crP 0, .const crWA (toWord wB),
    .const crNp (toWord (nPos))]) s
  rw [readGIR, semXIR_seq]
  generalize semXIR I (.blk [.const crP 0, .const crWA (toWord wB),
    .const crNp (toWord (nPos))]) s = s0 at r0 hH0 hM0 hsz0
  obtain ⟨p0, a0, n0⟩ := r0
  have hE : ∀ i, i ≠ crCp → i ≠ cTmp →
      rd (entryK crCp crNp (toWord (nPos)) s0.M) i = rd s0.M i :=
    fun i h1 h2 => entryK_frame _ (Ne.symm h1) (Ne.symm h2)
  have hcnt : rd (entryK crCp crNp (toWord (nPos)) s0.M) crCp = toWord (nPos) :=
    entryK_count hM0 (by decide) (by decide) (by decide) n0
  have hME := inv_entryK (c := crCp) (n := crNp) (K := toWord (nPos)) hM0 (by decide)
  have e : semXIR I (.loopK crCp crNp (toWord (nPos)) (crPosG bX pL capW D z occ)) s0 =
      iterL (semXIR I (crPosG bX pL capW D z occ)) crCp (nPos)
        ⟨entryK crCp crNp (toWord (nPos)) s0.M, s0.o⟩ := by
    simp only [semXIR, hcnt, toNat_toWord (show nPos < 2 ^ 64 by omega)]
  rw [e]
  have hy : ∀ y, regs ≤ y → y ≠ crCp ∧ y ≠ cTmp := fun y hy => by
    simp only [crCp, cTmp, regs] at *; omega
  have hHE : ∀ y, regs ≤ y → rd (entryK crCp crNp (toWord (nPos)) s0.M) y = rd s.M y :=
    fun y hy' => by rw [hE y (hy y hy').1 (hy y hy').2, hH0 y hy']
  have e0 : (z + occ) * (0 + nPos) = (z + occ) * nPos := by rw [Nat.zero_add]
  obtain ⟨d1, d2, d3⟩ := crPosG_loop hbX hbX2 hpL hD hX hcl hcw hn hD64 ho hcap hwB hwB2 (nPos) 0
    ⟨entryK crCp crNp (toWord (nPos)) s0.M, s0.o⟩
    (by omega) hME (by simp only [size_entryK]; omega)
    (fun a ha => by
      show rd (entryK crCp crNp (toWord (nPos)) s0.M) (bX + a) = _
      rw [hHE _ (by simp only [regs] at hbX ⊢; omega), hXs a ha])
    (by
      show rd (entryK crCp crNp (toWord (nPos)) s0.M) crP = _
      rw [hE _ (by decide) (by decide), p0])
    (by
      show rd (entryK crCp crNp (toWord (nPos)) s0.M) crWA = _
      rw [hE _ (by decide) (by decide), a0])
  rw [e0] at d2
  refine ⟨fun q hq t ht => d1 q (by omega) (by omega) t ht, fun y hy1 hy2 => ?_, d3⟩
  rw [d2 y hy1 (by omega)]
  show rd (entryK crCp crNp (toWord (nPos)) s0.M) y = _
  rw [hHE y hy1]

end PosG

/-- **The column reads** of a tree of height `ht` with its cap at level `lv` (`2^ht` positions, `ht − lv` steps):
row word `t` of position `p` is `readRowG ht lv z occ L cap p`'s word `t`; the index and the heap outside the rows
are kept. -/
theorem readGIR_sem {bX pL : ℕ} (hbX : regs ≤ bX) (hbX2 : bX ≤ 2 ^ 60) (hpL : pL ≤ 2 ^ 60)
    (c : Digest) (π : Proof) (L : Log) (hs : 5 + (π.size + 7) / 8 = pL)
    (hq : ∀ e ∈ L, e.1.size < 2 ^ 64) (ht : (extractorInput c π L).length ≤ 2 ^ 64)
    (s : St) (hM : Inv s.M) (hsz : bX + L.length + L.length ≤ s.M.size)
    (s₂ : St) (hM₂ : Inv s₂.M) (hsz₂ : bX ≤ s₂.M.size)
    (hX₂ : ∀ a < L.length, rd s₂.M (bX + a) =
      rd (semXIR (extractorInput c π L).toArray (idxIR4 bX pL) s).M (bX + a))
    {ht' lv z occ capW wB : ℕ} {cap : List Digest} (hcl : ∀ q < 2 ^ ht', q / 2 ^ (ht' - lv) < cap.length)
    (hcw : capW + 4 * cap.length < 2 ^ 62) (hn : 2 ^ ht' < 2 ^ 62) (hD64 : ht' - lv < 64)
    (ho : occ < 2 ^ 60)
    (hcap : ∀ e (he : e < cap.length), ∀ m < 4,
      (extractorInput c π L).toArray.getD (capW + 4 * e + m) 0 =
        (packBytes cap[e].toList).getD m 0)
    (hwB : regs ≤ wB) (hwB2 : wB + (z + occ) * 2 ^ ht' ≤ bX) :
    (∀ p < 2 ^ ht', ∀ t < z + occ,
      rdK (semXIR (extractorInput c π L).toArray (readGIR bX pL capW wB (2 ^ ht') (ht' - lv) z occ) s₂).M
        (wB + (z + occ) * p + t) = (readRowG ht' lv z occ L cap p).getD t 0) ∧
    (∀ y, regs ≤ y → (y < wB ∨ wB + (z + occ) * 2 ^ ht' ≤ y) →
      rd (semXIR (extractorInput c π L).toArray (readGIR bX pL capW wB (2 ^ ht') (ht' - lv) z occ) s₂).M y =
        rd s₂.M y) ∧
    (∀ a < L.length,
      rd (semXIR (extractorInput c π L).toArray (readGIR bX pL capW wB (2 ^ ht') (ht' - lv) z occ) s₂).M
        (bX + a) = rd s₂.M (bX + a)) ∧
    Inv (semXIR (extractorInput c π L).toArray (readGIR bX pL capW wB (2 ^ ht') (ht' - lv) z occ) s₂).M := by
  obtain ⟨r1, r2, r3⟩ := idxIR4_sorted hbX hbX2 hpL c π L hs hq ht s hM hsz
  have hSX : Sorted4 pL (crTape c π L) L
      (fun a => rd (semXIR (extractorInput c π L).toArray (idxIR4 bX pL) s).M (bX + a)) :=
    ⟨r1, r2, r3⟩
  obtain ⟨w1, w2, w3⟩ := readGIR_sem4 hbX hbX2 hpL ⟨hs, hq, ht⟩ hSX s₂ hM₂ hX₂ hcl hcw hn hD64 ho hcap hwB
    hwB2 hsz₂
  refine ⟨fun p hp t ht'' => ?_, w2, fun a _ => w2 _ (by simp only [regs] at hbX ⊢; omega)
    (.inr (by omega)), w3⟩
  rw [rdK, w1 p hp t ht'', crGRowW_readRowG L cap hp ht'']

end Lvm.X
