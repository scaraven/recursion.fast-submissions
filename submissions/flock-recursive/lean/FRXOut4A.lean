-- New for `flock-recursive` (BLUEPRINT revision 4.1, §6.2 step 5, A.5, A.7; stage S-H4, pass 11, item 3:
-- an aggregate's signed child on the machine). 3.x has no aggregate.
import FRXOut4P

/-!
# An aggregate's signed child (`aggIR4`)

Aggregate `a` (signed child `σ = aggChild κ a`, `k = kSel κ a w` segments) emits (`signedWords_agg`)
`|π_A| = 48 + k·piSize`, the header (`hdrWords`: `'A' ‖ k`, then `n` and `e` as shift-1 pairs of the
`c_A` block's message words), the `k` proofs, the count `k·|items| + (k − 1)`, the `k` traces' bodies
each after its spacer entry (`i ≥ 1`: the constant query words `spW`, then the answer as four shift-1
pairs of chain words, **`spPre`**), the signature. The two segment loops run `k ≤ maxK` times (the count
in `qK`, `loopK_emitR`); each iteration runs its prefix, copies segment `i` into the buffer (`cp_vS`) and
emits over it (**`segLoop_sem`**).

The chain loader's registers (**`aggRegs`**, `ChR` by **`chR_agg`**): base `8·chBase σ`, last block
`jL = k·sBlk − 3 = aggL k − 1` (revision 4.4.1), and the redirect
`Δ = [k < maxK]·8·(finB κ a − 1 − chBase σ + k − jL)`, so the stream's last block is read from the
candidate final block `finB κ a + k − 1`.
-/

namespace FR.X

open RecursionFast FR.Read FR.Rev4 FR.Snd

attribute [local irreducible] entryK storeM runPrims

/-! ## Specification -/

/-- `oX := c + qK·m`. -/
def lenW (c m : ℕ) : List Prim := [.const oK (toWord m), .op .mul oX qK oK, .const oK (toWord c), .op .add oX oX oK]

/-- **The length word and the header**: `48 + k·piSize`, `0x41 + 256k`, then `n` (shift 1 at word
`8·c_A + 4`) and `e` (four shift-1 pairs from word `8·c_A`). -/
def aggHd (κ : NodeKind) (a : ℕ) : XIR :=
  .seq (.blk (lenW 48 (piSizeOf seq4))) (.seq (.out oX)
  (.seq (.blk (lenW 0x41 256)) (.seq (.out oX)
  (.seq (.blk [.const qCB 0, .const qJ 0, .const qDl 0, .const qA (toWord 8), .const qB (toWord 55),
      .const qN (toWord (8 * N4c.cAB κ a + 4))])
  (.seq (shwO κ) (.seq (.blk [.const qN (toWord (8 * N4c.cAB κ a))]) (shw4 κ)))))))

/-- The redirect's constant `finB κ a − 1 − chBase σ`. -/
def dC (κ : NodeKind) (a : ℕ) : ℕ := N4c.finB κ a - 1 - N4c.chBase κ (N4c.aggChild κ a)

/-- **The chain loader's registers** for aggregate `a` with `k = qK` segments, and `qI := 0`:
`qJ := k·sBlk − 3·[0 < k]` (the stream's last block), the redirect `qDl`. -/
def aggRegs (κ : NodeKind) (a : ℕ) : XIR :=
  .seq (.blk [.const qCB (toWord (8 * N4c.chBase κ (N4c.aggChild κ a))), .const oK (toWord N4c.sBlk),
    .op .mul qJ qK oK, .const oK 0, .op .ltu qT1 oK qK, .const oK (toWord 3), .op .mul qT1 qT1 oK,
    .op .sub qJ qJ qT1, .const qI 0])
  (.blk [.const oK (toWord κ.maxK), .op .ltu qT1 qK oK, .const oK (toWord (dC κ a)), .op .add qDl qK oK,
    .op .sub qDl qDl qJ, .const oK (toWord 3), .op .shl qDl qDl oK, .op .mul qDl qT1 qDl])

/-- **A segment loop**: per segment `i < qK`, the prefix `P`, copy segment `i`, run `E` over the buffer,
`i += 1`. -/
def segLoop (κ : NodeKind) (P E : XIR) : XIR :=
  .loopK qSc qK (toWord κ.maxK) (.seq P (.seq (cpSeg κ) (.seq E (.blk [.op .add qI qI cOne]))))

/-- The spacer entry's query words as a segment of constants. -/
def spSeg : Seg := catL (spW.map .wd)

/-- **Spacer `qI`'s entry**: its query's words (constants), then its answer, four shift-1 pairs of chain
words from `qI·(strideB/8) − 4`. -/
def spIR (κ : NodeKind) : XIR :=
  .seq (bufSeg spSeg) (.seq (.blk [.const oK (toWord (N4c.strideB / 8)), .op .mul qN qI oK, .const oK (toWord 4),
    .op .sub qN qN oK, .const qA (toWord 8), .const qB (toWord 55)]) (shw4 κ))

/-- **The traces' prefix**: the spacer entry before segment `qI ≥ 1`. -/
def spPre (κ : NodeKind) : XIR := .ite qI (spIR κ) (.blk [])

/-- `oX := qK·(|items| + 1) − [0 < qK]`: the aggregate trace's length `k·|items| + (k − 1)`. -/
def cntW : List Prim :=
  lenW 0 ((itemsOf seq4).length + 1) ++ [.const oK 0, .op .ltu qT1 oK qK, .op .sub oX oX qT1]

/-- The traces: the count word, `qI := 0`, per segment its spacer entry (`i ≥ 1`) and its body. -/
def aggTr (κ : NodeKind) : XIR :=
  .seq (.blk cntW) (.seq (.out oX) (.seq (.blk [.const qI 0])
    (segLoop κ (spPre κ) (bufSeg (trBody4 seq4)))))

/-- **Aggregate `a`'s signed child.** -/
def aggIR4 (κ : NodeKind) (a : ℕ) : XIR :=
  .seq (kSelIR κ a κ.maxK) (.seq (aggHd κ a) (.seq (aggRegs κ a) (.seq (segLoop κ (.blk []) pfIR)
    (.seq (aggTr κ) (sigIR κ (N4c.aggChild κ a))))))

/-! ## Proof helpers: what the emitters write -/

theorem noW_lo (ap : AP) (sg : Seg) (d : ℕ) {r : ℕ} (hr : r < 200) (hc : r ≠ cTmp) : ¬ Writes (segIR ap d sg) r :=
  fun h => by
    rcases ow_segIR ap sg d r h with h1 | ⟨e, -, h2⟩
    · rcases h1 with h1 | h1
      · exact hc h1
      · omega
    · omega

theorem wf_setB : WF setB := by simp [setB, WF, Prim.dst, oR, oBd, oKF]

theorem wf_ladF : WF ladF :=
  ⟨by simp [WF, Prim.dst, oU], wf_ldw apB, by simp [WF, Prim.dst, oK, oX, qF0, qF1, qT1]⟩

theorem wf_pfS {m : ℕ} (hm : m ∈ [30, 31, 32]) : WF (pfS m) :=
  wf_segIR apB _ 0 (by have := (okSeg_pf m hm).2; omega)

theorem wf_pfIR : WF pfIR :=
  ⟨wf_setB, wf_ladF, wf_pfS (by simp), wf_pfS (by simp), wf_pfS (by simp)⟩

theorem wf_bufSeg {sg : Seg} (hd : depthSeg sg ≤ 9) : WF (bufSeg sg) := ⟨wf_setB, wf_segIR apB sg 0 (by omega)⟩

theorem noW_pfIR {r : ℕ} (hr : r < 200) (hc : r ≠ cTmp) (h : r ∉ [qF0, qF1, qT1, oU, oK, oX]) :
    ¬ Writes pfIR r := by
  simp only [List.mem_cons, List.mem_nil_iff, or_false, not_or] at h
  rintro (h1 | h1 | h1 | h1 | h1)
  · obtain ⟨p, hp, he⟩ := h1
    simp only [setB, List.mem_cons, List.mem_nil_iff, or_false] at hp
    rcases hp with rfl | rfl | rfl <;> simp only [Prim.dst, oR, oBd, oKF] at he <;> omega
  · rcases h1 with ⟨p, hp, he⟩ | h1 | ⟨p, hp, he⟩
    · simp only [List.mem_cons, List.mem_nil_iff, or_false] at hp; subst hp; exact h.2.2.2.1 he.symm
    · have := writes_wrL _ _ h1
      simp only [wrL, ldw, ldPs, List.map_cons, List.map_nil, Prim.dst, List.cons_append, List.nil_append,
        List.mem_cons, List.mem_nil_iff, or_false, List.append_nil] at this
      simp only [oK, oT1, oT2, oT3, oAd, oX] at this; omega
    · simp only [List.mem_cons, List.mem_nil_iff, or_false] at hp
      rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp only [Prim.dst] at he <;>
        subst he <;> simp_all [oK, oX, qF0, qF1, qT1]
  all_goals exact noW_lo apB _ 0 hr hc h1

theorem pfIR_keep (I : Array Word) {t : St} (hM : Inv t.M) {r : ℕ} (hr : r < 200) (hc : r ≠ cTmp)
    (h : r ∉ [qF0, qF1, qT1, oU, oK, oX]) : rd (semXIR I pfIR t).M r = rd t.M r :=
  frame I pfIR t wf_pfIR hM r (by simp only [regs]; omega) (noW_pfIR hr hc h)

theorem noW_bufSeg {sg : Seg} {r : ℕ} (hr : r < 200) (hc : r ≠ cTmp) : ¬ Writes (bufSeg sg) r := by
  rintro (⟨p, hp, he⟩ | h1)
  · simp only [setB, List.mem_cons, List.mem_nil_iff, or_false] at hp
    rcases hp with rfl | rfl | rfl <;> simp only [Prim.dst, oR, oBd, oKF] at he <;> omega
  · exact noW_lo apB _ 0 hr hc h1

theorem bufSeg_keep (I : Array Word) {sg : Seg} (hd : depthSeg sg ≤ 9) {t : St} (hM : Inv t.M) {r : ℕ}
    (hr : r < 200) (hc : r ≠ cTmp) : rd (semXIR I (bufSeg sg) t).M r = rd t.M r :=
  frame I (bufSeg sg) t (wf_bufSeg hd) hM r (by simp only [regs]; omega) (noW_bufSeg hr hc)

theorem cpSeg_keep (I : Array Word) (κ : NodeKind) {t : St} (hM : Inv t.M) {r : ℕ}
    (h : r ∈ [qI, qCB, qJ, qDl, qK, qSc]) : rd (semXIR I (cpSeg κ) t).M r = rd t.M r := by
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at h
  rcases h with rfl | rfl | rfl | rfl | rfl | rfl <;>
    exact keep_of I (wf_cpSeg κ) hM (by decide) (by cases κ <;> decide)

/-! ## The segment loops -/

/-- The segment loops' registers at segment `i`. -/
structure AgR (cb jL Δ k i : ℕ) (M : Mem) : Prop where
  i : rd M qI = toWord i
  cb : rd M qCB = toWord cb
  jl : rd M qJ = toWord jL
  dl : rd M qDl = toWord Δ
  k : rd M qK = toWord k

theorem agR_keep {cb jL Δ k i : ℕ} {M M' : Mem} (h : AgR cb jL Δ k i M)
    (hk : ∀ r ∈ [qI, qCB, qJ, qDl, qK], rd M' r = rd M r) : AgR cb jL Δ k i M' :=
  ⟨(hk _ (by simp)).trans h.i, (hk _ (by simp)).trans h.cb, (hk _ (by simp)).trans h.jl,
    (hk _ (by simp)).trans h.dl, (hk _ (by simp)).trans h.k⟩

/-- **A segment loop emits `pre i ++ out i` per segment `i < k`**, when the prefix `P` emits `pre i` at
segment `i`, `E` emits `F` of the buffer's words and `F` of segment `i`'s virtual words is `out i`. -/
theorem segLoop_sem (I : Array Word) (κ : NodeKind) {P E : XIR} {F : (ℕ → Word) → List Word}
    {pre out : ℕ → List Word} {M₀ : Mem} {σ k cb jL Δ nB : ℕ} {w : Circ.Asg}
    (hP : ∀ j < k, ∀ t, OF M₀ t → AgR cb jL Δ k j t.M → (semXIR I P t).o.toList = t.o.toList ++ pre j ∧
      OF M₀ (semXIR I P t) ∧ ∀ r ∈ [qI, qCB, qJ, qDl, qK, qSc], rd (semXIR I P t).M r = rd t.M r)
    (hE : ∀ t, OF M₀ t → (semXIR I E t).o.toList = t.o.toList ++ F (src t.M apB bufB) ∧ OF M₀ (semXIR I E t) ∧
      ∀ r ∈ [qI, qCB, qJ, qDl, qK, qSc], rd (semXIR I E t).M r = rd t.M r)
    (hF : ∀ i < k, ∀ V : ℕ → Word, (∀ u (hu : u < (vS κ σ k i w).length), (vS κ σ k i w)[u] = V u) → F V = out i)
    {t : St} (hO : OF M₀ t) (hsz : bufB + 2 ^ 22 ≤ M₀.size) (hH : HeapW κ M₀ w) (hC : 0 < k → ChR κ σ k cb jL Δ nB)
    (hk : k ≤ κ.maxK) (hk4 : κ.maxK ≤ 4) (hnB : ∀ i < k, i * (N4c.strideB / 8) + nW ≤ nB)
    (hD : ∀ i < k, i * N4c.strideB + N4c.segB ≤ N4c.streamB κ σ k) (hR : AgR cb jL Δ k 0 t.M) :
    (semXIR I (segLoop κ P E) t).o.toList = t.o.toList ++ (List.range k).flatMap (fun i => pre i ++ out i) ∧
      OF M₀ (semXIR I (segLoop κ P E) t) ∧ AgR cb jL Δ k k (semXIR I (segLoop κ P E) t).M := by
  have L := loopK_emitR I (c := qSc) (n := qK) (K := κ.maxK)
    (b := .seq P (.seq (cpSeg κ) (.seq E (.blk [.op .add qI qI cOne]))))
    (fun j st => OF M₀ st ∧ AgR cb jL Δ k j st.M) (fun i => pre i ++ out i) t hO.inv (by decide) (by decide)
    (by decide) (by decide) (by omega) hk hR.k
    ⟨of_entryK (by decide) (by decide) hO, agR_keep hR fun r hr => by
      simp only [List.mem_cons, List.mem_nil_iff, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl <;> exact entryK_frame _ (by decide) (by decide)⟩
    (fun j st hj ⟨hO', hR'⟩ => by
      obtain ⟨p0, P0, kP⟩ := hP j hj st hO' hR'
      rw [semXIR_seq]
      generalize semXIR I P st = s0 at p0 P0 kP
      have hR0 : AgR cb jL Δ k j s0.M := agR_keep hR' fun r hr => kP r (by
        simp only [List.mem_cons, List.mem_nil_iff, or_false] at hr ⊢; tauto)
      obtain ⟨O1, o1, hV⟩ := cp_vS I κ P0 hsz hH (hC (by omega)) (by omega) (hnB j hj) (hD j hj) hR0.i hR0.cb
        hR0.jl hR0.dl
      have k1 : ∀ r ∈ [qI, qCB, qJ, qDl, qK, qSc], rd (semXIR I (cpSeg κ) s0).M r = rd st.M r :=
        fun r hr => (cpSeg_keep I κ P0.inv hr).trans (kP r hr)
      rw [semXIR_seq]
      generalize semXIR I (cpSeg κ) s0 = s1 at O1 o1 hV k1
      obtain ⟨o2, O2, k2⟩ := hE s1 O1
      rw [semXIR_seq]
      generalize semXIR I E s1 = s2 at o2 O2 k2
      have hs2 := O2.inv.1
      simp only [regs] at hs2
      have e : ∀ r ∈ [qCB, qJ, qDl, qK],
          rd (decS qSc (semXIR I (.blk [.op .add qI qI cOne]) s2)).M r = rd st.M r := fun r hr => by
        simp only [List.mem_cons, List.mem_nil_iff, or_false] at hr
        rw [rd_decS (by rcases hr with rfl | rfl | rfl | rfl <;> decide), semXIR_blk,
          rd_runPrims_of_not_writes (by rcases hr with rfl | rfl | rfl | rfl <;> simp [Prim.dst, qI, qCB, qJ, qDl, qK]),
          k2 _ (by simp at hr ⊢; tauto), k1 _ (by simp at hr ⊢; tauto)]
      refine ⟨by rw [semXIR_blk]; simp only [o2, o1, p0, hF j hj _ hV, List.append_assoc],
        ⟨inv_decS (inv_runPrims (by simp [Prim.dst, qI])
        O2.inv) (by decide), by simp [semXIR_blk, O2.size], fun y h1 h2 => by
          rw [rd_decS (by simp only [qSc, regs] at *; omega), semXIR_blk,
            rd_runPrims_of_not_writes (by simp only [regs] at h1; simp [Prim.dst, qI]; omega), O2.low y h1 h2]⟩,
        ⟨?_, by rw [e _ (by simp)]; exact hR'.cb, by rw [e _ (by simp)]; exact hR'.jl, by rw [e _ (by simp)]; exact hR'.dl,
          by rw [e _ (by simp)]; exact hR'.k⟩⟩
      rw [rd_decS (by decide), semXIR_blk]
      simp only [runPrims, List.foldl, Prim.run]
      rw [rd_set_self (by simp only [qI]; omega), k2 _ (by simp), k1 _ (by simp), hR'.i, one_cOne O2.inv,
        add_one_toWord])
  exact ⟨L.1, L.2.1, L.2.2⟩

theorem rd_const_self {M : Mem} {d : ℕ} {v : Word} (h : d < M.size) : rd (runPrims [.const d v] M) d = v := by
  simp only [runPrims, List.foldl, Prim.run]; exact rd_set_self h

/-! ## An aggregate's numbers -/

/-- The stream's last block at `k` segments (`aggL k − 1 = k·sBlk − 3`, `k ≥ 1`). -/
def jLv (k : ℕ) : ℕ := k * N4c.sBlk - 3

theorem aggL_eq' {k : ℕ} (hk : 1 ≤ k) : N4c.aggL k = jLv k + 1 := by
  rw [(N4c.aggB_blocks hk).2.1, jLv, N4c.sBlk]; omega

/-- **The layout facts an aggregate's output uses** (decided per kind). -/
structure AggN (κ : NodeKind) (a : ℕ) : Prop where
  agg : N4c.isAgg κ (N4c.aggChild κ a) = true
  of : N4c.aggOf κ (N4c.aggChild κ a) = a
  len : N4c.chLen κ (N4c.aggChild κ a) = N4c.aggL κ.maxK
  fb : N4c.chBase κ (N4c.aggChild κ a) + N4c.aggL κ.maxK < N4c.finB κ a
  fe : N4c.finB κ a + κ.maxK ≤ N4c.hEnd κ
  nb : N4c.chBase κ (N4c.aggChild κ a) + ((κ.maxK - 1) * (N4c.strideB / 8) + nW) / 8 < N4c.hEnd κ
  mk1 : 1 ≤ κ.maxK
  mk4 : κ.maxK ≤ 4
  cab : N4c.cAB κ a < N4c.hEnd κ
  σ2 : N4c.aggChild κ a < 2
  he : N4c.hEnd κ < 2 ^ 20

theorem aggN (κ : NodeKind) {a : ℕ} (ha : a < N4c.nAgg κ) : AggN κ a := by
  have hn : N4c.nAgg κ ≤ 2 := by cases κ <;> decide
  have h : a = 0 ∨ a = 1 := by omega
  rcases h with rfl | rfl
  · cases κ <;> exact ⟨by decide, by decide, by decide, by decide, by decide, by decide, by decide, by decide,
      by decide, by decide, by decide⟩
  · cases κ
    · exact absurd ha (by decide)
    · exact absurd ha (by decide)
    · exact ⟨by decide, by decide, by decide, by decide, by decide, by decide, by decide, by decide,
        by decide, by decide, by decide⟩

/-- The redirect's value at `k` segments (`aggRegs`' `qDl`). -/
def dV (κ : NodeKind) (a k : ℕ) : ℕ := if k < κ.maxK then (k + dC κ a - jLv k) * 2 ^ 3 else 0

/-- **The aggregate's chain loader** (`k ≥ 1` segments): the loader's words are the chain words. -/
theorem chR_agg (κ : NodeKind) {a k : ℕ} (ha : a < N4c.nAgg κ) (hk1 : 0 < k) (hk : k ≤ κ.maxK) :
    ChR κ (N4c.aggChild κ a) k (8 * N4c.chBase κ (N4c.aggChild κ a)) (jLv k) (dV κ a k)
      ((κ.maxK - 1) * (N4c.strideB / 8) + nW) := by
  have N := aggN κ ha
  have hL : N4c.streamL κ (N4c.aggChild κ a) k = jLv k + 1 := by
    simp only [N4c.streamL, N.agg, if_true, aggL_eq' hk1]
  have hLm := aggL_eq' N.mk1
  have hF : N4c.finBlk κ (N4c.aggChild κ a) k = if k < κ.maxK then N4c.finB κ a + (k - 1) else
      N4c.chBase κ (N4c.aggChild κ a) + N4c.aggL κ.maxK - 1 := by
    simp only [N4c.finBlk, N.agg, true_and, N.of, N.len]
  have hb : ∀ i, N4c.blkOf κ (N4c.aggChild κ a) k i = if i = jLv k then
      N4c.finBlk κ (N4c.aggChild κ a) k else N4c.chBase κ (N4c.aggChild κ a) + i := by
    intro i; unfold N4c.blkOf; rw [hL]; split_ifs <;> omega
  have fb := N.fb; have fe := N.fe; have nb := N.nb; have he := N.he; have m4 := N.mk4
  have hc : N4c.chBase κ (N4c.aggChild κ a) < N4c.hEnd κ := by omega
  have hmono : jLv k ≤ jLv κ.maxK := by unfold jLv; have := Nat.mul_le_mul_right N4c.sBlk hk; omega
  have e3 : (2 : ℕ) ^ 3 = 8 := rfl
  have es : N4c.strideB / 8 = 193904 := rfl
  have hj : jLv k = k * 24238 - 3 := rfl
  have hjm : jLv κ.maxK = κ.maxK * 24238 - 3 := rfl
  rw [es] at nb ⊢
  refine ⟨fun n => ?_, fun n hn => ?_, ?_, ?_⟩
  · rw [hb, hF]; unfold ldIx dV dC; simp only [e3]
    by_cases h1 : n / 8 = jLv k <;> by_cases h2 : k < κ.maxK <;> simp only [h1, h2, ↓reduceIte] <;> omega
  · rw [hb, hF]
    by_cases h1 : n / 8 = jLv k <;> by_cases h2 : k < κ.maxK <;> simp only [h1, h2, ↓reduceIte] <;> omega
  · unfold dV dC; simp only [e3]; split_ifs <;> omega
  · unfold jLv; simp only [N4c.sBlk]; omega

/-! ## The header and the registers -/

theorem ltu_toWord {a b : ℕ} (ha : a < 2 ^ 64) (hb : b < 2 ^ 64) :
    XOp.ltu.eval (toWord a) (toWord b) = if a < b then 1 else 0 := by
  simp only [XOp.eval, BitVec.lt_def, toNat_toWord ha, toNat_toWord hb]

theorem lenW_val {M : Mem} (hM : Inv M) {k : ℕ} (hK : rd M qK = toWord k) (c m : ℕ) :
    rd (runPrims (lenW c m) M) oX = toWord (c + k * m) ∧ ∀ r, r ≠ oK → r ≠ oX → rd (runPrims (lenW c m) M) r = rd M r := by
  have hs := hM.1
  simp only [regs] at hs
  refine ⟨?_, fun r h1 h2 => rd_runPrims_of_not_writes (by simp [lenW, Prim.dst, Ne.symm h1, Ne.symm h2]) _⟩
  simp only [lenW, runPrims, List.foldl, Prim.run]
  simp (disch := (simp only [size_set, oK, oX, qK]; omega)) only [rd_set_self, rd_set_ne]
  rw [hK, mul_toWord, add_toWord, Nat.add_comm]

/-- **The length word and the header are emitted** (`hdrWords`), `qK` kept. -/
theorem aggHd_sem (I : Array Word) (κ : NodeKind) (a : ℕ) {M₀ : Mem} {w : Circ.Asg} (hH : HeapW κ M₀ w)
    (hc : N4c.cAB κ a < N4c.hEnd κ) (he : N4c.hEnd κ < 2 ^ 20) {k : ℕ} {t : St} (hO : OF M₀ t)
    (hK : rd t.M qK = toWord k) :
    (semXIR I (aggHd κ a) t).o.toList = t.o.toList ++
      (toWord (48 + k * piSizeOf seq4) :: hdrWords k (N4s.hAn κ a w) (N4s.hAe κ a w)) ∧
      OF M₀ (semXIR I (aggHd κ a) t) ∧ rd (semXIR I (aggHd κ a) t).M qK = toWord k := by
  have hs := hO.inv.1
  simp only [regs] at hs
  have hG : ∀ m ≤ 8 * N4c.cAB κ a + 7, ldG κ M₀ 0 0 0 m = hMW w m := fun m hm => by
    rw [ldG, ldIx_zero, hMW_heapW hH (by omega)]
  have hl : ∀ m ≤ 8 * N4c.cAB κ a + 7, hAddr κ (ldIx 0 0 0 m) < bufB := fun m hm => by
    rw [ldIx_zero]; exact hAddr_lt' (by omega)
  obtain ⟨x1, k1⟩ := lenW_val hO.inv hK 48 (piSizeOf seq4)
  rw [aggHd, semXIR_seq, semXIR_blk, semXIR_seq]
  rw [show semXIR I (.out oX) ⟨runPrims (lenW 48 (piSizeOf seq4)) t.M, t.o⟩ = ⟨runPrims (lenW 48 (piSizeOf seq4)) t.M,
    t.o.push (rd (runPrims (lenW 48 (piSizeOf seq4)) t.M) oX)⟩ from rfl, x1]
  have O1 : OF M₀ ⟨runPrims (lenW 48 (piSizeOf seq4)) t.M, t.o.push (toWord (48 + k * piSizeOf seq4))⟩ :=
    of_mk (of_loK I (P := .blk (lenW 48 (piSizeOf seq4))) (by simp [lenW, LoK, Prim.dst, oK, oX, regs])
      (by simp [lenW, WF, Prim.dst, oK, oX]) hO) _
  have K1 : rd (⟨runPrims (lenW 48 (piSizeOf seq4)) t.M, t.o.push (toWord (48 + k * piSizeOf seq4))⟩ : St).M qK =
      toWord k := by show rd (runPrims (lenW 48 (piSizeOf seq4)) t.M) qK = _; rw [k1 _ (by decide) (by decide)]; exact hK
  have o1 : (⟨runPrims (lenW 48 (piSizeOf seq4)) t.M, t.o.push (toWord (48 + k * piSizeOf seq4))⟩ : St).o =
    t.o.push (toWord (48 + k * piSizeOf seq4)) := rfl
  generalize (⟨runPrims (lenW 48 (piSizeOf seq4)) t.M, t.o.push (toWord (48 + k * piSizeOf seq4))⟩ : St) = t1 at O1 K1 o1
  have hs1 := O1.inv.1
  simp only [regs] at hs1
  rw [semXIR_seq, semXIR_blk, semXIR_seq]
  obtain ⟨x2, k2⟩ := lenW_val O1.inv K1 0x41 256
  rw [show semXIR I (.out oX) ⟨runPrims (lenW 0x41 256) t1.M, t1.o⟩ = ⟨runPrims (lenW 0x41 256) t1.M,
    t1.o.push (rd (runPrims (lenW 0x41 256) t1.M) oX)⟩ from rfl, x2]
  have O2 : OF M₀ ⟨runPrims (lenW 0x41 256) t1.M, t1.o.push (toWord (0x41 + k * 256))⟩ :=
    of_mk (of_loK I (P := .blk (lenW 0x41 256)) (by simp [lenW, LoK, Prim.dst, oK, oX, regs])
      (by simp [lenW, WF, Prim.dst, oK, oX]) O1) _
  have K2 : rd (⟨runPrims (lenW 0x41 256) t1.M, t1.o.push (toWord (0x41 + k * 256))⟩ : St).M qK = toWord k := by
    show rd (runPrims (lenW 0x41 256) t1.M) qK = _; rw [k2 _ (by decide) (by decide)]; exact K1
  have o2 : (⟨runPrims (lenW 0x41 256) t1.M, t1.o.push (toWord (0x41 + k * 256))⟩ : St).o =
    t1.o.push (toWord (0x41 + k * 256)) := rfl
  generalize (⟨runPrims (lenW 0x41 256) t1.M, t1.o.push (toWord (0x41 + k * 256))⟩ : St) = t2 at O2 K2 o2
  have hs2 := O2.inv.1
  simp only [regs] at hs2
  rw [semXIR_seq, semXIR_blk]
  set ps : List Prim := [.const qCB 0, .const qJ 0, .const qDl 0, .const qA (toWord 8), .const qB (toWord 55),
      .const qN (toWord (8 * N4c.cAB κ a + 4))] with hps
  have R3 : SwR 0 0 0 1 (8 * N4c.cAB κ a + 4) (runPrims ps t2.M) := by
    simp only [hps, runPrims, List.foldl, Prim.run]
    refine ⟨⟨?_, ?_, ?_⟩, ?_, ?_, ?_⟩ <;>
    simp (disch := (simp only [size_set, qCB, qJ, qDl, qA, qB, qN]; omega)) only [rd_set_self, rd_set_ne] <;>
    first | exact True.intro | rfl
  have K3 : rd (runPrims ps t2.M) qK = toWord k := by
    rw [rd_runPrims_of_not_writes (by simp [hps, Prim.dst, qCB, qJ, qDl, qA, qB, qN, qK])]; exact K2
  have O3 : OF M₀ ⟨runPrims ps t2.M, t2.o⟩ := of_loK I (P := .blk ps)
    (by simp [hps, LoK, Prim.dst, regs, qCB, qJ, qDl, qA, qB, qN]) (by simp [hps, WF, Prim.dst, qCB, qJ, qDl, qA, qB, qN]) O2
  rw [semXIR_seq]
  obtain ⟨a4, b4, c4, d4⟩ := shwO_sem I κ (sh := 1) (by norm_num) (by omega) (by norm_num) (hl _ (by omega))
    (hl _ (by omega)) O3 R3
  generalize semXIR I (shwO κ) ⟨runPrims ps t2.M, t2.o⟩ = t4 at a4 b4 c4 d4
  have K4 : rd t4.M qK = toWord k := by rw [d4 _ (by decide) (by decide)]; exact K3
  have hs4 := b4.inv.1
  simp only [regs] at hs4
  rw [semXIR_seq, semXIR_blk]
  have k5 : ∀ r, r ≠ qN → rd (runPrims [.const qN (toWord (8 * N4c.cAB κ a))] t4.M) r = rd t4.M r := fun r hr =>
    rd_runPrims_of_not_writes (by simp [Prim.dst, Ne.symm hr]) _
  have R5 : SwR 0 0 0 1 (8 * N4c.cAB κ a) (runPrims [.const qN (toWord (8 * N4c.cAB κ a))] t4.M) :=
    ⟨⟨by rw [k5 _ (by decide)]; exact c4.cb, by rw [k5 _ (by decide)]; exact c4.jl, by rw [k5 _ (by decide)]; exact c4.dl⟩,
      by simp only [runPrims, List.foldl, Prim.run]; rw [rd_set_self (by simp only [qN]; omega)],
      by rw [k5 _ (by decide)]; exact c4.a, by rw [k5 _ (by decide)]; exact c4.b⟩
  have O5 : OF M₀ ⟨runPrims [.const qN (toWord (8 * N4c.cAB κ a))] t4.M, t4.o⟩ :=
    of_loK I (P := .blk [.const qN (toWord (8 * N4c.cAB κ a))]) (by simp [LoK, Prim.dst, regs, qN])
      (by simp [WF, Prim.dst, qN]) b4
  obtain ⟨a6, b6, c6, d6⟩ := shw4_sem I κ (sh := 1) (by norm_num) (by omega) (by norm_num)
    (fun j hj => hl _ (by omega)) O5 R5
  refine ⟨?_, b6, by rw [d6 _ (by decide) (by decide), k5 _ (by decide)]; exact K4⟩
  rw [a6, a4, o2, o1]
  have sh : ∀ n ≤ 8 * N4c.cAB κ a + 6, shWd (ldG κ M₀ 0 0 0) 1 n = shWd (hMW w) 1 n := fun n hn => by
    simp only [shWd]; rw [hG n (by omega), hG (n + 1) (by omega)]
  rw [hdrWords, hAe_words, hAn_word, sh _ (by omega), List.map_congr_left fun j hj => sh _ (by
    have := List.mem_range.1 hj; omega), Nat.mul_comm k 256]
  simp only [Array.toList_push, List.append_assoc, List.cons_append, List.singleton_append, List.nil_append]


theorem aggRegs_sem (I : Array Word) (κ : NodeKind) {a : ℕ} (ha : a < N4c.nAgg κ) {M₀ : Mem} {t : St} (hO : OF M₀ t)
    {k : ℕ} (hk : k ≤ κ.maxK) (hK : rd t.M qK = toWord k) :
    (semXIR I (aggRegs κ a) t).o = t.o ∧ OF M₀ (semXIR I (aggRegs κ a) t) ∧
      AgR (8 * N4c.chBase κ (N4c.aggChild κ a)) (jLv k) (dV κ a k) k 0 (semXIR I (aggRegs κ a) t).M := by
  have N := aggN κ ha
  have hs := hO.inv.1
  simp only [regs] at hs
  have hLm := aggL_eq' N.mk1
  have fb := N.fb; have m4 := N.mk4; have he := N.he; have fe := N.fe
  have hmono : jLv k ≤ jLv κ.maxK := by unfold jLv; have := Nat.mul_le_mul_right N4c.sBlk hk; omega
  have hjd : jLv k ≤ k + dC κ a := by unfold dC; omega
  have hk4 : k ≤ 4 := le_trans hk m4
  rw [aggRegs, semXIR_seq, semXIR_blk]
  set ps : List Prim := [.const qCB (toWord (8 * N4c.chBase κ (N4c.aggChild κ a))), .const oK (toWord N4c.sBlk),
    .op .mul qJ qK oK, .const oK 0, .op .ltu qT1 oK qK, .const oK (toWord 3), .op .mul qT1 qT1 oK,
    .op .sub qJ qJ qT1, .const qI 0] with hps
  have O1 : OF M₀ ⟨runPrims ps t.M, t.o⟩ := of_loK I (P := .blk ps)
    (by simp [hps, LoK, Prim.dst, regs, qCB, oK, qJ, qT1, qI]) (by simp [hps, WF, Prim.dst, qCB, oK, qJ, qT1, qI]) hO
  have v1 : rd (runPrims ps t.M) qCB = toWord (8 * N4c.chBase κ (N4c.aggChild κ a)) ∧
      rd (runPrims ps t.M) qJ = toWord (jLv k) ∧ rd (runPrims ps t.M) qI = toWord 0 ∧
      rd (runPrims ps t.M) qK = toWord k := by
    simp only [hps, runPrims, List.foldl, Prim.run]
    simp (disch := (simp only [size_set, qCB, oK, qJ, qT1, qDl, qI, qK]; omega)) only [rd_set_self, rd_set_ne]
    refine ⟨by first | exact True.intro | rfl, ?_, by first | exact True.intro | rfl, by first | exact True.intro | exact hK⟩
    rw [hK, mul_toWord, show (0 : Word) = toWord 0 from rfl, ltu_toWord (by norm_num) (by omega), ite_mul_toWord,
      sub_toWord (by simp only [N4c.sBlk]; omega) (by split_ifs <;> simp only [N4c.sBlk] <;> omega)]
    congr 1; unfold jLv; simp only [N4c.sBlk]; split_ifs <;> omega
  obtain ⟨c1, j1, i1, k1⟩ := v1
  have hs1 := O1.inv.1
  simp only [regs] at hs1
  obtain ⟨M1, hM1⟩ : ∃ M1, runPrims ps t.M = M1 := ⟨_, rfl⟩
  rw [hM1] at O1 c1 j1 i1 k1 hs1
  rw [semXIR_blk, hM1]
  refine ⟨rfl, of_loK I (P := .blk _) (by simp [LoK, Prim.dst, regs, oK, qT1, qDl])
    (by simp [WF, Prim.dst, oK, qT1, qDl]) O1, ?_, ?_, ?_, ?_, ?_⟩
  all_goals simp only [runPrims, List.foldl, Prim.run]
  all_goals simp (disch := (simp only [size_set, qCB, oK, qJ, qT1, qDl, qI, qK] at *; omega)) only
    [rd_set_self, rd_set_ne]
  · exact i1
  · exact c1
  · exact j1
  · rw [k1, j1, add_toWord, sub_toWord (by unfold dC; omega) hjd,
      shl_toWord (by norm_num) (by unfold dC; omega), ltu_toWord (by omega) (by omega), ite_mul_toWord]; rfl
  · exact k1

theorem segOut_wds (W : ℕ → Word) (κ : Bool) (b : ℕ) : ∀ l : List Word, segOut W κ b (catL (l.map .wd)) = l
  | [] => rfl
  | x :: l => by simp only [List.map_cons, catL, segOut, segOut_wds W κ b l]; rfl

theorem okSeg_sp : okSeg spSeg = true ∧ depthSeg spSeg ≤ 9 := by decide

/-- **The traces' prefix at segment `j`**: nothing at `j = 0`; spacer `j`'s entry words (`spW` and its
answer) at `j ≥ 1`. -/
theorem spPre_sem (I : Array Word) (κ : NodeKind) {a k j : ℕ} (ha : a < N4c.nAgg κ) (hk : k ≤ κ.maxK) (hj : j < k)
    {M₀ : Mem} {w : Circ.Asg} (hH : HeapW κ M₀ w) {t : St} (hO : OF M₀ t)
    (hR : AgR (8 * N4c.chBase κ (N4c.aggChild κ a)) (jLv k) (dV κ a k) k j t.M) :
    (semXIR I (spPre κ) t).o.toList = t.o.toList ++
      (if j = 0 then [] else spW ++ packBytes (N4s.spAns κ (N4c.aggChild κ a) k w j).toList) ∧
      OF M₀ (semXIR I (spPre κ) t) ∧ ∀ r ∈ [qI, qCB, qJ, qDl, qK, qSc], rd (semXIR I (spPre κ) t).M r = rd t.M r := by
  have N := aggN κ ha
  have hk4 : k ≤ 4 := le_trans hk N.mk4
  have hC := chR_agg κ ha (by omega) hk
  rw [spPre, semXIR_ite, hR.i]
  by_cases hj0 : j = 0
  · subst hj0
    have e0 : (toWord 0 : Word) = 0 := rfl
    simp only [e0, if_true, semXIR_blk, List.append_nil]
    exact ⟨by first | exact True.intro | simp, by simpa [runPrims] using hO, fun _ _ => by simp only [runPrims, List.foldl]⟩
  rw [if_neg (show toWord j ≠ (0 : Word) from fun h =>
      hj0 ((toWord_eq_iff (a := j) (b := 0) (by omega) (by norm_num)).1 h)), if_neg hj0, spIR, semXIR_seq]
  -- the query's words
  obtain ⟨o1, O1, k1⟩ := bufSeg_sem I spSeg okSeg_sp.1 okSeg_sp.2 hO
  have kb : ∀ r < 200, r ≠ cTmp → rd (semXIR I (bufSeg spSeg) t).M r = rd t.M r := fun r hr hc =>
    bufSeg_keep I okSeg_sp.2 hO.inv hr hc
  rw [show segOut (src t.M apB bufB) false 0 spSeg = spW by rw [spSeg]; exact segOut_wds _ _ _ _] at o1
  generalize semXIR I (bufSeg spSeg) t = t1 at o1 O1 k1 kb
  have hs1 := O1.inv.1
  simp only [regs] at hs1
  -- the answer's registers
  have hQ : 4 ≤ j * (N4c.strideB / 8) := by
    have : N4c.strideB / 8 ≤ j * (N4c.strideB / 8) := Nat.le_mul_of_pos_left _ (by omega)
    have : 4 ≤ N4c.strideB / 8 := by decide
    omega
  have hQ' : j * (N4c.strideB / 8) < 2 ^ 23 := by
    have : j * (N4c.strideB / 8) ≤ 4 * (N4c.strideB / 8) := Nat.mul_le_mul_right _ (by omega)
    have : 4 * (N4c.strideB / 8) < 2 ^ 23 := by decide
    omega
  rw [semXIR_seq, semXIR_blk]
  set ps : List Prim := [.const oK (toWord (N4c.strideB / 8)), .op .mul qN qI oK, .const oK (toWord 4),
    .op .sub qN qN oK, .const qA (toWord 8), .const qB (toWord 55)] with hps
  have kp : ∀ r, r ∉ [oK, qN, qA, qB] → rd (runPrims ps t1.M) r = rd t1.M r := fun r hr =>
    rd_runPrims_of_not_writes (fun p hp he => by
      simp only [hps, List.mem_cons, List.mem_nil_iff, or_false] at hp
      simp only [List.mem_cons, List.mem_nil_iff, or_false, not_or] at hr
      rcases hp with rfl | rfl | rfl | rfl | rfl | rfl <;> simp only [Prim.dst] at he <;> subst he <;> simp_all) _
  have R2 : SwR (8 * N4c.chBase κ (N4c.aggChild κ a)) (jLv k) (dV κ a k) 1 (j * (N4c.strideB / 8) - 4)
      (runPrims ps t1.M) := by
    refine ⟨⟨?_, ?_, ?_⟩, ?_, ?_, ?_⟩
    · rw [kp _ (by decide), kb _ (by decide) (by decide)]; exact hR.cb
    · rw [kp _ (by decide), kb _ (by decide) (by decide)]; exact hR.jl
    · rw [kp _ (by decide), kb _ (by decide) (by decide)]; exact hR.dl
    all_goals simp only [hps, runPrims, List.foldl, Prim.run]
    all_goals simp (disch := (simp only [size_set, oK, qN, qA, qB, qI] at *; omega)) only [rd_set_self, rd_set_ne]
    all_goals first
      | (rw [kb _ (by decide) (by decide), hR.i, mul_toWord, sub_toWord (by omega) hQ]; done)
      | rfl
  have O2 : OF M₀ ⟨runPrims ps t1.M, t1.o⟩ := of_loK I (P := .blk ps)
    (by simp [hps, LoK, Prim.dst, regs, oK, qN, qA, qB]) (by simp [hps, WF, Prim.dst, oK, qN, qA, qB]) O1
  -- the answer's words
  have hG : ∀ n ≤ (κ.maxK - 1) * (N4c.strideB / 8) + nW,
      rd M₀ (hAddr κ (ldIx (8 * N4c.chBase κ (N4c.aggChild κ a)) (jLv k) (dV κ a k) n)) =
        chW κ (N4c.aggChild κ a) k w n ∧
      hAddr κ (ldIx (8 * N4c.chBase κ (N4c.aggChild κ a)) (jLv k) (dV κ a k) n) < bufB := fun n hn => by
    have hb := hC.blk n hn
    have e : ldIx (8 * N4c.chBase κ (N4c.aggChild κ a)) (jLv k) (dV κ a k) n / 8 =
        N4c.blkOf κ (N4c.aggChild κ a) k (n / 8) := by rw [hC.ld]; omega
    refine ⟨?_, hAddr_lt' (by rw [e]; exact hb)⟩
    rw [hMW_heapW hH (by rw [e]; exact hb), hC.ld, chW]
  have hnB : j * (N4c.strideB / 8) ≤ (κ.maxK - 1) * (N4c.strideB / 8) :=
    Nat.mul_le_mul_right _ (by omega)
  obtain ⟨a3, b3, -, d3⟩ := shw4_sem I κ (sh := 1) (by norm_num) (by have := hC.big; omega) hC.jl
    (fun i hi => (hG _ (by omega)).2) O2 R2
  refine ⟨?_, b3, fun r hr => ?_⟩
  · rw [a3, show ({ M := runPrims ps t1.M, o := t1.o } : St).o = t1.o from rfl, o1, List.append_assoc]
    have hD : j * N4c.strideB < N4c.streamB κ (N4c.aggChild κ a) k := by
      simp only [N4c.streamB, N.agg, if_true]
      have hb := (N4c.aggB_blocks (Nat.lt_of_le_of_lt (Nat.zero_le _) hj)).2.2
      have h1 : (j + 1) * N4c.strideB ≤ k * N4c.strideB := Nat.mul_le_mul_right _ (by omega)
      have h2 : 128 < N4c.strideB := by decide
      rw [Nat.add_one_mul] at h1; omega
    rw [spAns_words κ _ k w (by omega) hD]
    refine congrArg (fun l => t.o.toList ++ (spW ++ l)) (List.map_congr_left fun i hi => ?_)
    have hi4 := List.mem_range.1 hi
    simp only [ldG, shWd]
    rw [(hG _ (by omega)).1, (hG _ (by omega)).1]
  · simp only [List.mem_cons, List.mem_nil_iff, or_false] at hr
    rw [d3 r (by rcases hr with rfl | rfl | rfl | rfl | rfl | rfl <;> decide)
      (by rcases hr with rfl | rfl | rfl | rfl | rfl | rfl <;> decide), kp r (by
        rcases hr with rfl | rfl | rfl | rfl | rfl | rfl <;> decide),
      kb r (by rcases hr with rfl | rfl | rfl | rfl | rfl | rfl <;> decide)
      (by rcases hr with rfl | rfl | rfl | rfl | rfl | rfl <;> decide)]

/-- Every selector the count reads is a decoded cell inside `f`, on the heap below the buffer. -/
theorem sel_ok (κ : NodeKind) {a i : ℕ} (ha : a < N4c.nAgg κ) (hi : i < κ.maxK) (ι : Kind) :
    κ.oneCell + selR (N4c.sub κ a i) ι < 2 ^ (κ.m - 7) ∧ regs ≤ selA κ a i ι ∧ selA κ a i ι + 1 < bufB := by
  have hn : N4c.nAgg κ ≤ 2 := by cases κ <;> decide
  have hm : κ.maxK ≤ 4 := by cases κ <;> decide
  have h : a = 0 ∨ a = 1 := by omega
  have hi' : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 := by omega
  rcases h with rfl | rfl <;> rcases hi' with rfl | rfl | rfl | rfl <;> cases κ <;> cases ι <;>
    first | exact absurd hi (by decide) | exact absurd ha (by decide) | decide

theorem cntW_val {M : Mem} (hM : Inv M) {k : ℕ} (hk : k ≤ 4) (hK : rd M qK = toWord k) :
    rd (runPrims cntW M) oX = toWord (k * (itemsOf seq4).length + (k - 1)) ∧
      ∀ r, r ≠ oK → r ≠ oX → r ≠ qT1 → rd (runPrims cntW M) r = rd M r := by
  have hs := hM.1
  simp only [regs] at hs
  refine ⟨?_, fun r h1 h2 h3 => rd_runPrims_of_not_writes (by
    simp [cntW, lenW, Prim.dst, Ne.symm h1, Ne.symm h2, Ne.symm h3]) _⟩
  have hl : (itemsOf seq4).length = 8783 := itemsOf_seq4_len
  simp only [cntW, lenW, List.cons_append, List.nil_append, runPrims, List.foldl, Prim.run]
  simp (disch := (simp only [size_set, oK, oX, qK, qT1]; omega)) only [rd_set_self, rd_set_ne]
  rw [hK, mul_toWord, add_toWord, show (0 : Word) = toWord 0 from rfl, ltu_toWord (by norm_num) (by omega),
    hl]
  rcases Nat.eq_zero_or_pos k with rfl | hk0
  · rfl
  · rw [if_pos hk0, show (1 : Word) = toWord 1 from rfl, sub_toWord (by omega) (by omega)]
    congr 1; omega

/-- **Aggregate `a`'s signed child is emitted** (`signedWords_agg`). -/
theorem aggIR4_sem (I : Array Word) (κ : NodeKind) {a : ℕ} (ha : a < N4c.nAgg κ) {M₀ : Mem} {w : Circ.Asg}
    {s : St} (hO : OF M₀ s) (hsz : bufB + 2 ^ 22 ≤ M₀.size) (hH : HeapW κ M₀ w) :
    (semXIR I (aggIR4 κ a) s).o.toList = s.o.toList ++ signedWords (sgnX sigH κ (N4c.aggChild κ a) w) ∧
      OF M₀ (semXIR I (aggIR4 κ a) s) := by
  have N := aggN κ ha
  -- the count
  obtain ⟨o1, O1, K1⟩ := kSelIR_sem I κ a (w := w) (fun i hi ι => (sel_ok κ ha hi ι).2) (fun i hi ι =>
    hH _ ((out_cells_dec0 κ).1 _ ι) (sel_ok κ ha hi ι).1) hO
  rw [aggIR4, semXIR_seq]
  generalize semXIR I (kSelIR κ a κ.maxK) s = s1 at o1 O1 K1
  set k := kSel κ a w with hkd
  have hk : k ≤ κ.maxK := (kSel_ctl κ a w).2
  have hk4 : k ≤ 4 := le_trans hk N.mk4
  -- the header
  obtain ⟨o2, O2, K2⟩ := aggHd_sem I κ a hH N.cab N.he O1 K1
  rw [semXIR_seq]
  generalize semXIR I (aggHd κ a) s1 = s2 at o2 O2 K2
  -- the registers
  obtain ⟨o3, O3, R3⟩ := aggRegs_sem I κ ha O2 hk K2
  rw [semXIR_seq]
  generalize semXIR I (aggRegs κ a) s2 = s3 at o3 O3 R3
  have hD : ∀ i < k, i * N4c.strideB + N4c.segB ≤ N4c.streamB κ (N4c.aggChild κ a) k := fun i hi => by
    simp only [N4c.streamB, N.agg, if_true]
    have hb := (N4c.aggB_blocks (Nat.lt_of_le_of_lt (Nat.zero_le _) hi)).2.2
    have h1 : (i + 1) * N4c.strideB ≤ k * N4c.strideB := Nat.mul_le_mul_right _ (by omega)
    have h2 : N4c.strideB = N4c.segB + 128 := by decide
    rw [Nat.add_one_mul] at h1; omega
  have hnB : ∀ i < k, i * (N4c.strideB / 8) + nW ≤ (κ.maxK - 1) * (N4c.strideB / 8) + nW := fun i hi =>
    Nat.add_le_add_right (Nat.mul_le_mul_right _ (by omega)) _
  have hC : 0 < k → ChR κ (N4c.aggChild κ a) k (8 * N4c.chBase κ (N4c.aggChild κ a)) (jLv k) (dV κ a k)
      ((κ.maxK - 1) * (N4c.strideB / 8) + nW) := fun h => chR_agg κ ha h hk
  -- the proofs
  have L4 := segLoop_sem I κ (P := .blk []) (E := pfIR)
    (F := fun V => segOut V false 0 (pSeg4 seq4 (mOfB (V 10).toNat.toUInt8))) (pre := fun _ => [])
    (out := fun i => packBytes (bl (pf4 (N4s.segTr κ (N4c.aggChild κ a) k i w))))
    (fun j _ t ht _ => ⟨by simp [semXIR_blk, runPrims], by simpa [semXIR_blk, runPrims] using ht,
      fun r _ => by simp [semXIR_blk, runPrims]⟩)
    (fun t ht => by
      obtain ⟨g1, g2, -⟩ := pfIR_sem I ht
      exact ⟨g1, g2, fun r hr => by
        simp only [List.mem_cons, List.mem_nil_iff, or_false] at hr
        rcases hr with rfl | rfl | rfl | rfl | rfl | rfl <;> exact pfIR_keep I ht.inv (by decide) (by decide) (by decide)⟩)
    (fun i hi V hV => by rw [pf4_words κ (N4c.aggChild κ a) k i w (hD i hi) V hV false, packBytes_wordsBytes])
    O3 hsz hH hC hk N.mk4 hnB hD R3
  rw [semXIR_seq]
  generalize semXIR I (segLoop κ (.blk []) pfIR) s3 = s4 at L4
  obtain ⟨o4, O4, R4⟩ := L4
  -- (a `rw` with the theorem, not `simp`'s definitional `nil_append`: the kernel would otherwise unfold
  -- `packBytes` of a whole proof to see `[] ++ x ≡ x`)
  rw [List.flatMap_congr (l := List.range k) (fun i _ => List.nil_append
    (packBytes (bl (pf4 (N4s.segTr κ (N4c.aggChild κ a) k i w)))))] at o4
  -- the traces
  have hs4 := O4.inv.1
  simp only [regs] at hs4
  obtain ⟨x5, k5⟩ := cntW_val O4.inv hk4 R4.k
  rw [semXIR_seq, aggTr, semXIR_seq, semXIR_blk, semXIR_seq]
  rw [show semXIR I (.out oX) ⟨runPrims cntW s4.M, s4.o⟩ =
    ⟨runPrims cntW s4.M, s4.o.push (rd (runPrims cntW s4.M) oX)⟩ from rfl, x5]
  have O5 : OF M₀ ⟨runPrims cntW s4.M, s4.o.push (toWord (k * (itemsOf seq4).length + (k - 1)))⟩ :=
    of_mk (of_loK I (P := .blk cntW) (by simp [cntW, lenW, LoK, Prim.dst, oK, oX, qT1, regs])
      (by simp [cntW, lenW, WF, Prim.dst, oK, oX, qT1]) O4) _
  rw [semXIR_seq, semXIR_blk]
  have k6 : ∀ r, r ≠ qI → r ≠ oK → r ≠ oX → r ≠ qT1 → rd (runPrims [.const qI 0] (runPrims cntW s4.M)) r =
      rd s4.M r := fun r h1 h2 h3 h4 => by
    rw [rd_runPrims_of_not_writes (by simp [Prim.dst, Ne.symm h1]), k5 r h2 h3 h4]
  have R6 : AgR (8 * N4c.chBase κ (N4c.aggChild κ a)) (jLv k) (dV κ a k) k 0
      (runPrims [.const qI 0] (runPrims cntW s4.M)) :=
    ⟨by rw [rd_const_self (by rw [size_runPrims]; simp only [qI]; omega)]; rfl,
      by rw [k6 _ (by decide) (by decide) (by decide) (by decide)]; exact R4.cb,
      by rw [k6 _ (by decide) (by decide) (by decide) (by decide)]; exact R4.jl,
      by rw [k6 _ (by decide) (by decide) (by decide) (by decide)]; exact R4.dl,
      by rw [k6 _ (by decide) (by decide) (by decide) (by decide)]; exact R4.k⟩
  have O6 : OF M₀ ⟨runPrims [.const qI 0] (runPrims cntW s4.M),
      s4.o.push (toWord (k * (itemsOf seq4).length + (k - 1)))⟩ :=
    of_loK I (P := .blk [.const qI 0]) (by simp [LoK, Prim.dst, regs, qI]) (by simp [WF, Prim.dst, qI]) O5
  have hdT := okSeg_tr.2.2.2
  have L7 := segLoop_sem I κ (P := spPre κ) (E := bufSeg (trBody4 seq4)) (F := fun V => segOut V false 0 (trBody4 seq4))
    (pre := fun i => if i = 0 then [] else spW ++ packBytes (N4s.spAns κ (N4c.aggChild κ a) k w i).toList)
    (out := fun i => (N4s.segTr κ (N4c.aggChild κ a) k i w).flatMap entryW)
    (fun j hj t ht hR => spPre_sem I κ ha hk hj hH ht hR)
    (fun t ht => by
      obtain ⟨g1, g2, -⟩ := bufSeg_sem I (trBody4 seq4) okSeg_tr.2.2.1 (le_trans hdT (by norm_num)) ht
      exact ⟨g1, g2, fun r hr => by
        simp only [List.mem_cons, List.mem_nil_iff, or_false] at hr
        rcases hr with rfl | rfl | rfl | rfl | rfl | rfl <;>
          exact bufSeg_keep I (le_trans hdT (by norm_num)) ht.inv (by decide) (by decide)⟩)
    (fun i hi V hV => (entries_segTr κ (N4c.aggChild κ a) k i w (hD i hi) V hV false).symm)
    O6 hsz hH hC hk N.mk4 hnB hD R6
  dsimp only
  generalize semXIR I (segLoop κ (spPre κ) (bufSeg (trBody4 seq4))) ⟨runPrims [.const qI 0]
    (runPrims cntW s4.M), s4.o.push (toWord (k * (itemsOf seq4).length + (k - 1)))⟩ = s7 at L7
  obtain ⟨o7, O7, -⟩ := L7
  have hf := wb_fit κ N.σ2
  obtain ⟨o8, O8⟩ := sigIR_sem I κ (N4c.aggChild κ a) O7 hf.2 (fun m hm => hAddr_lt' (by omega))
  refine ⟨?_, O8⟩
  obtain ⟨V, hVd⟩ : ∃ V : ℕ → ℕ → Word, V = fun i u => (vS κ (N4c.aggChild κ a) k i w).getD u 0 := ⟨_, rfl⟩
  have hV : ∀ i < k, ∀ u (hu : u < (vS κ (N4c.aggChild κ a) k i w).length),
      (vS κ (N4c.aggChild κ a) k i w)[u] = V i u := fun i _ u hu => by
    rw [hVd]; exact (List.getD_eq_getElem _ _ hu).symm
  have hP : ((List.range k).flatMap fun i => segOut (V i) false 0 (pSeg4 seq4 (mOfB (V i 10).toNat.toUInt8))) =
      (List.range k).flatMap fun i => packBytes (bl (pf4 (N4s.segTr κ (N4c.aggChild κ a) k i w))) :=
    List.flatMap_congr fun i hi => by
      rw [pf4_words κ (N4c.aggChild κ a) k i w (hD i (List.mem_range.1 hi)) (V i) (hV i (List.mem_range.1 hi)) false,
        packBytes_wordsBytes]
  have hT : ((List.range k).flatMap fun i =>
        (if i = 0 then [] else spW ++ packBytes (N4s.spAns κ (N4c.aggChild κ a) k w i).toList) ++
          segOut (V i) false 0 (trBody4 seq4)) =
      (List.range k).flatMap fun i =>
        (if i = 0 then [] else spW ++ packBytes (N4s.spAns κ (N4c.aggChild κ a) k w i).toList) ++
          (N4s.segTr κ (N4c.aggChild κ a) k i w).flatMap entryW :=
    List.flatMap_congr fun i hi => by
      rw [entries_segTr κ (N4c.aggChild κ a) k i w (hD i (List.mem_range.1 hi)) (V i) (hV i (List.mem_range.1 hi)) false]
  rw [o8, o7, sigL_eq κ N.σ2 hH, signedWords_agg κ ha w V hV, ← hkd, hP, hT]
  dsimp only
  rw [Array.toList_push, o4, o3, o2, o1]
  simp only [Array.toList_push, List.append_assoc, List.cons_append, List.singleton_append, List.nil_append]

end FR.X
