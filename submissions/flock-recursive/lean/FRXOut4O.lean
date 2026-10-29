-- New for `flock-recursive` (BLUEPRINT revision 4.1, §6.2 step 5, A.7; stage S-H4, pass 11, items 3–4: the
-- node output program `outIR4`, its semantics, cost, output count and size). 3.x analogue: `FRXOutRun.outIR`.
import FRXOut4A

/-!
# The node output program `outIR4 κ`

`outIR4 κ` emits the tag `1`, the four statement cells' words (`stC κ σ h`, two words each), then
signed child `0` (a previous node for `N2`/`N4`, `prevIR`; aggregate `0` for `N8`) and signed child `1`
(the aggregate: aggregate `0` for `N2`/`N4`, `1` for `N8`).

* **`outIR4_sem`**: on a heap holding the decoded cells of `w = wF κ L es` (`HeapW`, from
  `decF04_wF`), `outIR4 κ` appends **`witWords (readW4 sigH κ L es)`** (`witWords_readW4`,
  `prevIR_sem`, `aggIR4_sem`);
* `wf_outIR4`, `noLoopT_outIR4`; the cost (an upper bound, `cost_outIR4`), the output count and the
  size are computed from their components (each segment's by `decide +kernel`).
-/

namespace FR.X

open RecursionFast FR.Read FR.Rev4 FR.Snd

attribute [local irreducible] entryK storeM runPrims

/-! ## Specification -/

/-- The statement cells' heap words: per signed child `σ < 2` and half `h < 2`, two words. -/
def stA (κ : NodeKind) : List ℕ :=
  (List.range 2).flatMap fun σ => (List.range 2).flatMap fun h => [wAddr κ (N4c.stC κ σ h), wAddr κ (N4c.stC κ σ h) + 1]

/-- **The node output program** at node kind `κ`. -/
def outIR4 (κ : NodeKind) : XIR :=
  .seq (.blk [.const oX 1]) (.seq (.out oX) (.seq (outAs (stA κ))
    (.seq (if κ.hasPrev then prevIR κ else aggIR4 κ 0) (aggIR4 κ (if κ.hasPrev then 0 else 1)))))

/-! ## The semantics -/

theorem stC_ok (κ : NodeKind) {σ h : ℕ} (hσ : σ < 2) (hh : h < 2) :
    N4c.stC κ σ h < 2 ^ (κ.m - 7) ∧ regs ≤ wAddr κ (N4c.stC κ σ h) ∧ wAddr κ (N4c.stC κ σ h) + 1 < bufB := by
  have e1 : σ = 0 ∨ σ = 1 := by omega
  have e2 : h = 0 ∨ h = 1 := by omega
  rcases e1 with rfl | rfl <;> rcases e2 with rfl | rfl <;> cases κ <;> decide

theorem stA_words (κ : NodeKind) {M₀ : Mem} {w : Circ.Asg} (hH : HeapW κ M₀ w) :
    (stA κ).map (rd M₀) = elemWords (w (N4c.stC κ 0 0)) ++ elemWords (w (N4c.stC κ 0 1)) ++
      (elemWords (w (N4c.stC κ 1 0)) ++ elemWords (w (N4c.stC κ 1 1))) := by
  have e : ∀ σ h, σ < 2 → h < 2 → elemWords (w (N4c.stC κ σ h)) =
      [rd M₀ (wAddr κ (N4c.stC κ σ h)), rd M₀ (wAddr κ (N4c.stC κ σ h) + 1)] := fun σ h hσ hh => by
    rw [← hH _ ((out_cells_dec0 κ).2 σ h hh) (stC_ok κ hσ hh).1, elemWords_rdF]
  rw [e 0 0 (by norm_num) (by norm_num), e 0 1 (by norm_num) (by norm_num), e 1 0 (by norm_num) (by norm_num),
    e 1 1 (by norm_num) (by norm_num)]
  rfl

/-- **The node output**: on a heap holding `wF κ L es`'s decoded cells, `outIR4 κ` appends the node
witness's words `witWords (readW4 sigH κ L es)`. -/
theorem outIR4_sem (I : Array Word) (κ : NodeKind) {L es : Log} {s : St} (hM : Inv s.M)
    (hsz : bufB + 2 ^ 22 ≤ s.M.size) (hH : HeapW κ s.M (wF κ L es)) :
    (semXIR I (outIR4 κ) s).o.toList = s.o.toList ++ witWords (readW4 sigH κ L es) := by
  have hO : OF s.M s := ⟨hM, rfl, fun _ _ _ => rfl⟩
  generalize s.M = M₀ at hO hsz hH
  have hs := hO.inv.1
  simp only [regs] at hs
  rw [witWords_readW4]
  unfold outIR4
  simp only [semXIR_seq, semXIR_blk]
  rw [show semXIR I (.out oX) ⟨runPrims [.const oX 1] s.M, s.o⟩ =
    ⟨runPrims [.const oX 1] s.M, s.o.push (rd (runPrims [.const oX 1] s.M) oX)⟩ from rfl]
  have x1 : rd (runPrims [.const oX 1] s.M) oX = toWord 1 := by
    simp only [runPrims, List.foldl, Prim.run]; rw [rd_set_self (by simp only [oX]; omega)]; rfl
  rw [x1]
  have O1 : OF M₀ ⟨runPrims [.const oX 1] s.M, s.o.push (toWord 1)⟩ :=
    of_mk (of_loK I (P := .blk [.const oX 1]) (by simp [LoK, Prim.dst, oX, regs]) (by simp [WF, Prim.dst, oX]) hO) _
  have o1 : (⟨runPrims [.const oX 1] s.M, s.o.push (toWord 1)⟩ : St).o = s.o.push (toWord 1) := rfl
  generalize (⟨runPrims [.const oX 1] s.M, s.o.push (toWord 1)⟩ : St) = s1 at O1 o1
  obtain ⟨o2, O2, -⟩ := outAs_sem I (stA κ) s1 (fun a ha => by
    simp only [stA, List.mem_flatMap, List.mem_range, List.mem_cons, List.mem_nil_iff, or_false] at ha
    obtain ⟨σ, hσ, h, hh, rfl | rfl⟩ := ha
    · exact ⟨(stC_ok κ hσ hh).2.1, Nat.lt_of_succ_lt (stC_ok κ hσ hh).2.2⟩
    · exact ⟨Nat.le_succ_of_le (stC_ok κ hσ hh).2.1, (stC_ok κ hσ hh).2.2⟩) O1
  generalize semXIR I (outAs (stA κ)) s1 = s2 at o2 O2
  rw [stA_words κ hH] at o2
  have hc : ∀ (P₀ P₁ : XIR) (σ₁ : ℕ), σ₁ = 1 →
      (∀ t, OF M₀ t → (semXIR I P₀ t).o.toList = t.o.toList ++ signedWords (sgnX sigH κ 0 (wF κ L es)) ∧
        OF M₀ (semXIR I P₀ t)) →
      (∀ t, OF M₀ t → (semXIR I P₁ t).o.toList = t.o.toList ++ signedWords (sgnX sigH κ σ₁ (wF κ L es)) ∧
        OF M₀ (semXIR I P₁ t)) →
      (semXIR I P₁ (semXIR I P₀ s2)).o.toList = s.o.toList ++ (toWord 1 ::
        (elemWords (wF κ L es (N4c.stC κ 0 0)) ++ elemWords (wF κ L es (N4c.stC κ 0 1)) ++
          (elemWords (wF κ L es (N4c.stC κ 1 0)) ++ elemWords (wF κ L es (N4c.stC κ 1 1))) ++
          signedWords (sgnX sigH κ 0 (wF κ L es)) ++ signedWords (sgnX sigH κ 1 (wF κ L es)))) := by
    intro P₀ P₁ σ₁ hσ h0 h1
    subst hσ
    obtain ⟨a3, b3⟩ := h0 s2 O2
    obtain ⟨a4, -⟩ := h1 _ b3
    rw [a4, a3, o2, o1]
    simp only [Array.toList_push, List.append_assoc, List.cons_append, List.singleton_append, List.nil_append]
  cases hp : κ.hasPrev
  · simp only [Bool.false_eq_true, if_false]
    have n8 : N4c.aggChild κ 0 = 0 ∧ N4c.aggChild κ 1 = 1 ∧ 1 < N4c.nAgg κ := by
      simp [N4c.aggChild, N4c.nAgg, hp]
    exact hc _ _ 1 rfl (fun t ht => by
        have := aggIR4_sem I κ (a := 0) (by omega) ht hsz hH; rwa [n8.1] at this)
      (fun t ht => by have := aggIR4_sem I κ (a := 1) n8.2.2 ht hsz hH; rwa [n8.2.1] at this)
  · simp only [if_true]
    have n2 : N4c.aggChild κ 0 = 1 ∧ 0 < N4c.nAgg κ := by simp [N4c.aggChild, N4c.nAgg, hp]
    exact hc _ _ 1 rfl (fun t ht => prevIR_sem I κ hp ht hsz hH)
      (fun t ht => by have := aggIR4_sem I κ (a := 0) n2.2 ht hsz hH; rwa [n2.1] at this)

/-! ## Well formed, no tape loop -/

theorem wf_ldA {d a : ℕ} (hd : 4 ≤ d) : WF (ldA d a) := ⟨by simp [WF, Prim.dst, oAd], hd⟩

theorem wf_outAs : ∀ l : List ℕ, WF (outAs l)
  | [] => by simp [outAs, WF]
  | _ :: l => ⟨wf_ldA (by decide), trivial, wf_outAs l⟩

theorem wf_kSelIR (κ : NodeKind) (a : ℕ) : ∀ n, WF (kSelIR κ a n)
  | 0 => by simp [kSelIR, WF, Prim.dst, qAl, qK]
  | n + 1 => ⟨wf_kSelIR κ a n, wf_ldA (by decide), wf_ldA (by decide), wf_ldA (by decide), wf_ldA (by decide),
      wf_ldA (by decide), wf_ldA (by decide), by simp [kPs, WF, Prim.dst, qS0, qS1, oK, qAl, qK]⟩

theorem wf_segLoop (κ : NodeKind) {E : XIR} (hE : WF E) (hn : ¬ Writes E qSc) : WF (segLoop κ E) := by
  refine ⟨⟨by decide, by decide, by decide⟩, by decide, ?_, wf_realign κ, hE, by simp [WF, Prim.dst, qI]⟩
  rintro (h | h | ⟨p, hp, he⟩)
  · exact absurd (writes_wrL _ _ h) (by cases κ <;> decide)
  · exact hn h
  · simp only [List.mem_cons, List.mem_nil_iff, or_false] at hp; subst hp; simp [Prim.dst, qI, qSc] at he

theorem wf_aggIR4 (κ : NodeKind) (a : ℕ) : WF (aggIR4 κ a) := by
  have hT := okSeg_tr.2.2.2
  refine ⟨wf_kSelIR κ a _, ⟨by simp [lenW, WF, Prim.dst, oK, oX], trivial, by simp [lenW, WF, Prim.dst, oK, oX],
    trivial, by simp [WF, Prim.dst, qCB, qJ, qDl, qA, qB, qN], wf_shwO κ, by simp [WF, Prim.dst, qN], wf_shw4 κ⟩,
    by simp [aggRegs, WF, Prim.dst, qCB, oK, qJ, qT1, qDl, qI], wf_segLoop κ wf_pfIR (noW_pfIR (by decide) (by decide)
      (by decide)), ⟨by simp [lenW, WF, Prim.dst, oK, oX], trivial, by simp [WF, Prim.dst, qI],
    wf_segLoop κ (wf_bufSeg (le_trans hT (by norm_num))) (noW_bufSeg (by decide) (by decide))⟩, wf_sigIR κ _⟩

theorem wf_prevIR (κ : NodeKind) : WF (prevIR κ) :=
  ⟨by simp [WF, Prim.dst, oX], trivial, by simp [prevRegs, WF, Prim.dst, qCB, qJ, qDl, qI], wf_realign κ, wf_pfIR,
    wf_bufSeg (le_trans okSeg_tr.2.1 (by norm_num)), wf_sigIR κ 0⟩

theorem wf_outIR4 (κ : NodeKind) : WF (outIR4 κ) := by
  refine ⟨by simp [WF, Prim.dst, oX], trivial, wf_outAs _, ?_, wf_aggIR4 κ _⟩
  cases κ.hasPrev
  · exact wf_aggIR4 κ 0
  · exact wf_prevIR κ

theorem noLoopT_segIR' (sg : Seg) : NoLoopT (segIR apB 0 sg) := noLoopT_segIR apB sg 0

theorem noLoopT_pfIR : NoLoopT pfIR :=
  ⟨trivial, ⟨trivial, by simp [NoLoopT, ldw], trivial⟩, noLoopT_segIR' _, noLoopT_segIR' _, noLoopT_segIR' _⟩

theorem noLoopT_shwC (κ : NodeKind) : NoLoopT (shwC κ) := by simp [NoLoopT, shwC, ldC, ldw]

theorem noLoopT_shw4 (κ : NodeKind) : NoLoopT (shw4 κ) := by simp [NoLoopT, shw4, shwO, shwC, ldC, ldw]

theorem noLoopT_realign (κ : NodeKind) : NoLoopT (realign κ) := by simp [NoLoopT, realign, rlBody, ldC, ldw]

theorem noLoopT_sigIR (κ : NodeKind) (σ : ℕ) : NoLoopT (sigIR κ σ) := by
  simp [NoLoopT, sigIR, sigHd, otsIR, pathIR, otsB, pathB, shw4, shwO, shwC, ldC, ldw]

theorem noLoopT_outAs : ∀ l : List ℕ, NoLoopT (outAs l)
  | [] => trivial
  | _ :: l => ⟨⟨trivial, trivial⟩, trivial, noLoopT_outAs l⟩

theorem noLoopT_kSelIR (κ : NodeKind) (a : ℕ) : ∀ n, NoLoopT (kSelIR κ a n)
  | 0 => trivial
  | n + 1 => ⟨noLoopT_kSelIR κ a n, by simp [NoLoopT, kStep, ldA]⟩

theorem noLoopT_aggIR4 (κ : NodeKind) (a : ℕ) : NoLoopT (aggIR4 κ a) :=
  ⟨noLoopT_kSelIR κ a _, ⟨trivial, trivial, trivial, trivial, trivial, by simp [NoLoopT, shwO, shwC, ldC, ldw], trivial,
    noLoopT_shw4 κ⟩, trivial, ⟨noLoopT_realign κ, noLoopT_pfIR, trivial⟩,
    ⟨trivial, trivial, trivial, noLoopT_realign κ, ⟨trivial, noLoopT_segIR' _⟩, trivial⟩, noLoopT_sigIR κ _⟩

theorem noLoopT_prevIR (κ : NodeKind) : NoLoopT (prevIR κ) :=
  ⟨trivial, trivial, trivial, noLoopT_realign κ, noLoopT_pfIR, ⟨trivial, noLoopT_segIR' _⟩, noLoopT_sigIR κ 0⟩

theorem noLoopT_outIR4 (κ : NodeKind) : NoLoopT (outIR4 κ) := by
  refine ⟨trivial, trivial, noLoopT_outAs _, ?_, noLoopT_aggIR4 κ _⟩
  cases κ.hasPrev
  · exact noLoopT_aggIR4 κ 0
  · exact noLoopT_prevIR κ

/-! ## Cost, output count, size (from the components') -/

theorem cso_pfIR : cost pfIR 0 = 4187043 ∧ outs pfIR 0 = 99774 ∧ sizeIR pfIR = 14878 := by decide +kernel

theorem cso_trS : cost (bufSeg (trSeg4 seq4)) 0 = 6603375 ∧ outs (bufSeg (trSeg4 seq4)) 0 = 185345 ∧
    sizeIR (bufSeg (trSeg4 seq4)) = 4910 := by decide +kernel

theorem cso_trB : cost (bufSeg (trBody4 seq4)) 0 = 6603371 ∧ outs (bufSeg (trBody4 seq4)) 0 = 185344 ∧
    sizeIR (bufSeg (trBody4 seq4)) = 4906 := by decide +kernel

theorem cso_realign (κ : NodeKind) : cost (realign κ) 0 = 26133534 ∧ outs (realign κ) 0 = 0 ∧
    sizeIR (realign κ) = 172 := by cases κ <;> exact ⟨rfl, rfl, rfl⟩

theorem cso_sigIR (κ : NodeKind) {σ : ℕ} (hσ : σ < 2) : cost (sigIR κ σ) 0 = 62091 ∧ outs (sigIR κ σ) 0 = 597 ∧
    sizeIR (sigIR κ σ) = 993 := by interval_cases σ <;> cases κ <;> decide +kernel

theorem cso_aggHd (κ : NodeKind) {a : ℕ} (ha : a < 2) : cost (aggHd κ a) 0 = 543 ∧ outs (aggHd κ a) 0 = 7 ∧
    sizeIR (aggHd κ a) = 543 := by interval_cases a <;> cases κ <;> decide +kernel

theorem cso_kSel (κ : NodeKind) {a : ℕ} (ha : a < 2) : cost (kSelIR κ a κ.maxK) 0 ≤ 179 ∧
    outs (kSelIR κ a κ.maxK) 0 = 0 ∧ sizeIR (kSelIR κ a κ.maxK) ≤ 179 := by
  interval_cases a <;> cases κ <;> decide +kernel

theorem cso_outAs (κ : NodeKind) : cost (outAs (stA κ)) 0 = 49 ∧ outs (outAs (stA κ)) 0 = 8 ∧
    sizeIR (outAs (stA κ)) = 49 := by cases κ <;> decide +kernel

/-- **The node output's cost, output count and size** (upper bounds; exact values: cost `163,163,886`,
`289,278,962`, `504,585,753`; outputs `856,567`, `1,426,803`, `2,282,163`; size `42,850`, `42,938`,
`43,885` at `N2`, `N4`, `N8`). -/
theorem cso_outIR4 (κ : NodeKind) : cost (outIR4 κ) 0 ≤ 600000000 ∧ outs (outIR4 κ) 0 ≤ 2300000 ∧
    sizeIR (outIR4 κ) ≤ 45000 := by
  -- κ stays a variable and the closed programs are opaque (`PF`, `PS`, `PB`): the kernel never
  -- evaluates a closed cost or size while checking the `simp` steps
  obtain ⟨r1, r2, r3⟩ := cso_realign κ
  obtain ⟨s1, s2, s3⟩ := cso_sigIR κ (σ := 0) (by norm_num)
  obtain ⟨u1, u2, u3⟩ := cso_sigIR κ (σ := N4c.aggChild κ 0) (by cases κ <;> decide)
  obtain ⟨v1, v2, v3⟩ := cso_sigIR κ (σ := N4c.aggChild κ 1) (by cases κ <;> decide)
  obtain ⟨h1, h2, h3⟩ := cso_aggHd κ (a := 0) (by norm_num)
  obtain ⟨g1, g2, g3⟩ := cso_aggHd κ (a := 1) (by norm_num)
  obtain ⟨k1, k2, k3⟩ := cso_kSel κ (a := 0) (by norm_num)
  obtain ⟨l1, l2, l3⟩ := cso_kSel κ (a := 1) (by norm_num)
  obtain ⟨o1, o2, o3⟩ := cso_outAs κ
  have hm : BitVec.toNat (toWord κ.maxK) ≤ 4 := by cases κ <;> decide
  obtain ⟨PF, hF⟩ : ∃ P, pfIR = P := ⟨_, rfl⟩
  obtain ⟨PS, hS⟩ : ∃ P, bufSeg (trSeg4 seq4) = P := ⟨_, rfl⟩
  obtain ⟨PB, hB⟩ : ∃ P, bufSeg (trBody4 seq4) = P := ⟨_, rfl⟩
  obtain ⟨p1, p2, p3⟩ := hF ▸ cso_pfIR
  obtain ⟨a1, a2, a3⟩ := hS ▸ cso_trS
  obtain ⟨b1, b2, b3⟩ := hB ▸ cso_trB
  simp only [outIR4, prevIR, aggIR4, aggTr, segLoop, prevRegs, aggRegs, hF, hS, hB]
  cases κ.hasPrev <;>
  simp [cost, outs, sizeIR, blkSteps, lenW, p1, p2, p3, r1, r2, r3, a1, a2, a3, b1, b2, b3, s1, s2, s3, u1, u2, u3,
    v1, v2, v3, h1, h2, h3, g1, g2, g3, k2, l2, o1, o2, o3] <;>
  omega

end FR.X
