-- lvm6 EXI phase 2: the extractor's `Open6` fields at `P17` with EXF's front (`frontIn`) and EXG's descent:
-- the extractor is `front6 ; fillIR ; descX6 (LvD FDep) finX`. The rows and cells EXF proves become the
-- descent's `FrontHeap` (`frontHeap`); `descendsD` runs the round induction (`chainD`) on every available log
-- (`¬ Bad L` from `μ < 1`, the tape sizes); `ext_eq6A` is X5's `ext_eq6` with the descent's fact on available logs;
-- `sizeIR_F` counts the fill. New.
import Lvm6XInd18
import Lvm6XFrontIn
import Lvm6Len

/-!
# The extractor at `P17`

* **`holdsW_rows`**, **`rows0_bridge`**, **`frontHeap`**: EXF's `RowsD`/`FrontSeg` give `FrontHeap FDep`.
* **`cellsOK`**: `FDep`'s cells lie in `[2^25, 2^26) ⊆ [regs, wB6 0)`.
* **`descendsD`**: on an available log (`¬ Bad L`, tape sizes), the state before the output holds the pinned stack.
* **`ext_eq6A`**, **`descOk6_seq`** (+ `budgetF`), **`sizeIR_F`**, **`open6XF`** (the target; `DescOk6` of
  `fillIR ; descX6 …` still a hypothesis: `descOk6_seq` with EXG's `descOk6` needs the descent's cost bound
  with the fill's slack, the numbers are `budgetF`).
-/

set_option autoImplicit false

namespace Lvm6.X

open RecursionFast Lvm.X Lvm.Nb Lvm6.FD Finset Lvm6.Whir LeanVM.Parameters LeanVM.Protocol.Whir
  LeanVM.Protocol.Whir.AffineCombiner
open LeanVM.Protocol.Compile (Ev)

/-! ## EXF's rows and cells as the descent reads them -/

/-- **A level-`i ≥ 1` word from its committed rows**: 32 words a position, lane `s` = words `2s, 2s + 1`. -/
theorem holdsW_rows {M : Mem} {cs : List (ℕ × ℕ × LeanVM.Protocol.Compile.Word)} {i h : ℕ}
    (hi : i < cs.length) (hc1 : (cs.getD i default).1 = h) (hz : zp6 i = 0) (ho : occ6 i = 32)
    (hrow : ∀ p < 2 ^ h, ∀ t < occ6 i, rdK M (wB6 i + occ6 i * p + t) =
      ((cs.getD i default).2.2 p).getD (zp6 i + t) 0) :
    HoldsW M (wB6 i) h (0 + 4) (wordE false i (0 + 4) h (cs.take (i + 1))) := by
  intro p u
  have hu : bitsToNat u < 16 := bitsToNat_lt u
  have e : (cs.take (i + 1))[i]? = some (cs.getD i default) := by
    rw [List.getElem?_take, if_pos (by omega), List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi]; rfl
  have hp := p.isLt
  have a0 := hrow p hp (2 * bitsToNat u) (by rw [ho]; omega)
  have a1 := hrow p hp (2 * bitsToNat u + 1) (by rw [ho]; omega)
  rw [ho, hz] at a0 a1
  rw [Nat.zero_add (2 * bitsToNat u)] at a0
  rw [Nat.zero_add (2 * bitsToNat u + 1)] at a1
  have e16 : (2 : ℕ) ^ (0 + 4) = 16 := by norm_num
  simp only [wordE, e, laneVal, Bool.false_eq_true, ↓reduceIte, hc1, Nat.mod_eq_of_lt hp]
  rw [show wB6 i + 2 * (↑p * 2 ^ (0 + 4) + bitsToNat u) = wB6 i + 32 * ↑p + 2 * bitsToNat u by rw [e16]; ring,
    ← a0, ← a1, show wB6 i + 32 * ↑p + (2 * bitsToNat u + 1) = wB6 i + 32 * ↑p + 2 * bitsToNat u + 1 by omega]
  rfl

/-- **Level 0's rows**: the committed row with its 18 zero words made explicit (`tr0IR_sem`'s form). -/
theorem rows0_bridge {M : Mem} {cs : List (ℕ × ℕ × LeanVM.Protocol.Compile.Word)} (h0 : 0 < cs.length)
    (hc1 : (cs.getD 0 default).1 = 20) (hz : ∀ p, ∀ t < 18, ((cs.getD 0 default).2.2 p).getD t 0 = 0)
    (hrow : ∀ p < 2 ^ 20, ∀ t < 46, rdK M (wB6 0 + 46 * p + t) = ((cs.getD 0 default).2.2 p).getD (18 + t) 0) :
    ∃ (row : ℕ → List BF64) (c : ℕ × ℕ × LeanVM.Protocol.Compile.Word), c.1 = 20 ∧
      (∀ p < 2 ^ 20, c.2.2 p = List.replicate 18 0 ++ row p) ∧
      wordE true 0 (0 + 6) 20 [c] = wordE true 0 (0 + 6) 20 cs ∧
      ∀ p < 2 ^ 20, ∀ t < 46, rdK M (wB6 0 + 46 * p + t) = (row p).getD t 0 := by
  let row : ℕ → List BF64 := fun p ↦ ((cs.getD 0 default).2.2 p).drop 18
  have hrow' : ∀ p, ∀ t < 46, (row p).getD t 0 = ((cs.getD 0 default).2.2 p).getD (18 + t) 0 := fun p t _ ↦ by
    simp only [row, List.getD_eq_getElem?_getD, List.getElem?_drop]
  have key : ∀ q, ∀ k < 64, (List.replicate 18 (0 : BF64) ++ row q).getD k 0 =
      ((cs.getD 0 default).2.2 q).getD k 0 := by
    intro q k hk
    by_cases h18 : k < 18
    · rw [hz q k h18, List.getD_append _ _ _ _ (by simp [h18]), List.getD_eq_getElem?_getD,
        List.getElem?_replicate, if_pos h18]
      rfl
    · rw [List.getD_append_right _ _ _ _ (by simp; omega), List.length_replicate, hrow' q _ (by omega),
        show 18 + (k - 18) = k by omega]
  refine ⟨row, (20, (cs.getD 0 default).2.1, fun p ↦ List.replicate 18 0 ++ row p), rfl, fun _ _ ↦ rfl, ?_,
    fun p hp t ht ↦ by rw [hrow p hp t ht, hrow' p t ht]⟩
  have e : cs[0]? = some (cs.getD 0 default) := by
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h0]; rfl
  funext u p
  have hs : bitsToNat u < 64 := bitsToNat_lt u
  simp only [wordE, List.getElem?_cons_zero, e, laneVal, ↓reduceIte, hc1]
  rw [key _ _ (by omega)]

/-- **EXF's rows and cells are the descent's `FrontHeap`** on every decomposition of the opening's log. -/
theorem frontHeap {M : Mem} {h : List Ev} (hR : RowsD M h) (hS : FrontSeg M h) :
    ∀ rs0 o0 l1 rs1 o1 l2 rs2 o2 l3 rs3 o3 l4 rs4 sc,
      RunMid mid0 (h.drop ND) rs0 o0 l1 → RunMid mid1 l1 rs1 o1 l2 → RunMid mid2 l2 rs2 o2 l3 →
      RunMid mid3 l3 rs3 o3 l4 → RunFin finD l4 rs4 sc →
      FrontHeap FDep M (LeanVM.Protocol.Compile.commits h) rs0 o0 rs1 o1 rs2 o2 rs3 o3 rs4 sc := by
  intro rs0 o0 l1 rs1 o1 l2 rs2 o2 l3 rs3 o3 l4 rs4 sc r0 r1 r2 r3 r4
  obtain ⟨c0, c1, c2, c3, c4, i0, i1, i2, i3, s0⟩ := hS rs0 o0 l1 rs1 o1 l2 rs2 o2 l3 rs3 o3 l4 rs4 sc r0 r1 r2 r3 r4
  obtain ⟨hlen, hrows⟩ := hR
  obtain ⟨a1, -, a3, a4⟩ := hrows 0 (by norm_num)
  obtain ⟨b1, -, -, b4⟩ := hrows 1 (by norm_num)
  obtain ⟨d1, -, -, d4⟩ := hrows 2 (by norm_num)
  obtain ⟨f1, -, -, f4⟩ := hrows 3 (by norm_num)
  obtain ⟨g1, -, -, g4⟩ := hrows 4 (by norm_num)
  exact ⟨rows0_bridge (by omega) a1 a3 a4,
    holdsW_rows (i := 1) (h := 19) (by omega) b1 rfl rfl b4,
    holdsW_rows (i := 2) (h := 18) (by omega) d1 rfl rfl d4,
    holdsW_rows (i := 3) (h := 17) (by omega) f1 rfl rfl f4,
    holdsW_rows (i := 4) (h := 16) (by omega) g1 rfl rfl g4,
    c0, c1, c2, c3, c4, i0, i1, i2, i3, s0⟩

/-- **`FDep`'s cells** lie in `[2^25, 2^26)`, below the rows of commitment 0. -/
theorem cellsOK : CellsOK FDep := by
  have hw0 : wB6 0 = 134217728 := rfl
  have hreg : regs = 256 := rfl
  have hr : ∀ i, rndD i ≤ 6 := fun i ↦ by unfold rndD; split <;> omega
  refine ⟨fun i hi k hk ↦ ?_, fun i hi ↦ ?_, ?_, ?_⟩
  · have := hr i; simp only [FDep, F17]; omega
  · have := hr i; simp only [FDep, F17]; omega
  · simp only [FDep, F17]; omega
  · simp only [FDep, F17, hw0]; norm_num

/-! ## The descent on an available log -/

section Assembly

open Lvm Lvm.T Lvm.FS
open scoped NNReal ENNReal

/-- **The descent at `P17` on a log with no `Bad` and the tape sizes**: the state before the output holds the
pinned stack (EXF's `frontIn`, the round induction `chainD`, EXG's `finX`). -/
theorem descendsD {Φ : Phases} (hPF : PhasesFollow Φ P17) (hw : Φ.whir = whirAt Whir.whirP)
    {SGood TGood : Hdr → Stack → Prop} {vk c : Digest} {π : Proof} {L : Log} {x : List UInt8} {h : List Ev}
    (hE : (schemeOf (prog6 Φ) P17 vk).Ex (fun _ x h => (x, h)) c π L = some (x, h)) (hl : π.size = pz6)
    (hq : ∀ e ∈ L, e.1.size < 2 ^ 64) (ht : (extractorInput c π L).length ≤ 2 ^ 64) (hB : ¬ Lvm.FS.Bad L)
    (hG : G6 SGood TGood x h) :
    Inv (preOut6 (.seq fillIR (descX6 (LvD FDep) finX)) (extractorInput c π L)).M ∧
      (preOut6 (.seq fillIR (descX6 (LvD FDep) finX)) (extractorInput c π L)).o = #[] ∧
      HeapHolds (preOut6 (.seq fillIR (descX6 (LvD FDep) finX)) (extractorInput c π L)).M
        (pick6 (Whir.I6 P17) h) := by
  obtain ⟨hX, hR⟩ := hG
  obtain ⟨cl, hma, hgw, htie⟩ := RG.mem_cands hR
  obtain ⟨N₀, -, h1, hs⟩ := hgw openKey_P17
  obtain ⟨fI, fO, -, fR, fS, fN⟩ := frontIn hPF hw hE hl hq ht hB
  have hN := fN cl N₀ true h1
  rw [hN] at hs
  have hsz : 2 ^ 30 ≤ (fillSt c π L).M.size := by
    simp only [fillSt, frontSt6, size_sem, initSt, size_runPrims, Array.size_replicate, mem6]
    omega
  have hM := mach_of (extractorInput c π L).toArray FDep cellsOK (fillSt c π L) fI hsz _ _ (frontHeap fR fS)
  obtain ⟨U, hU, hA, hW, hRep, hI', hO'⟩ := chainD _ (LvD FDep) 67 bDep _ cl hma _ _ hs hM
  obtain ⟨y1, y2, y3⟩ := finOut FDep (extractorInput c π L).toArray _ U hRep hI' (hO'.trans fO)
    (by rw [lvRun_size]; exact hsz)
  rw [pick6_eq_decD hX.1 htie ⟨hU, hA, hW⟩, preOut6_eqF, semXIR_seq, semXIR_descX6]
  exact ⟨y1, y2, y3⟩

/-- **`ext_eq6` with the descent's fact on available logs only** (X5's `ext_eq6`, whose `SFront6.descends` must
hold for every replay; here it may use `Avail`: the log's `¬ Bad` and the tape sizes). -/
theorem ext_eq6A {prog : Shape → Digest → List UInt8 → LeanVM.Protocol.Compile.VerifierProgram Bool} {vk : Digest}
    {R : Digest → Wit → Prop} (K : KCert (schemeOf prog P17 vk) R) (I : OpeningIface) {descX : XIR}
    {G : List UInt8 → List Ev → Prop} (hK : K.ext = ExtSpec6 I)
    (len : ∀ c π L, Avail K c π L → π.size = pz6)
    (goodL : ∀ c π L, Avail K c π L → ∀ x h, (schemeOf prog P17 vk).Ex (fun _ x h => (x, h)) c π L = some (x, h) →
      G x h)
    (descends : ∀ c π L x h, Avail K c π L → (schemeOf prog P17 vk).Ex (fun _ x h => (x, h)) c π L = some (x, h) →
      π.size = pz6 → G x h → Inv (preOut6 descX (extractorInput c π L)).M ∧
        (preOut6 descX (extractorInput c π L)).o = #[] ∧
        HeapHolds (preOut6 descX (extractorInput c π L)).M (pick6 I h)) :
    ExtEq6 (EX6 descX) K := by
  intro c π L hA
  have hA' := hA
  obtain ⟨hS, -, hμ, hacc⟩ := hA'
  obtain ⟨w, hw, -⟩ := Scheme.final_law K L c π hμ hacc
  rw [Eideal, hw]
  rw [Ex_map] at hw
  obtain ⟨⟨x, h⟩, hp, rfl⟩ := Option.map_eq_some_iff.mp hw
  have hlen := len c π L hA
  obtain ⟨hI, hO, hH⟩ := descends c π L x h hA hp hlen (goodL c π L hA x h hp)
  obtain ⟨t6, t7, t8, t12⟩ := hdrTape6 c π L x h hp
  rw [EX6, if_pos hS, Eden, den, extIR6, hK]
  set inp := extractorInput c π L
  -- the parse takes the `S` branch at `|π| = pz6`
  have hreg : regs ≤ mem6 := by simp only [regs, mem6]; norm_num
  have h0 : Inv (initSt (mem6 + mpwX * inp.length)).M := inv_initSt (Nat.le_add_right_of_le hreg)
  have hk5 := Lvm6.W.parse_isK pz6 inp.toArray _ h0
  have hz5 := parse_regs pz6 inp.toArray _ h0
  have hb0 : π.data[0]? = some sByte := by
    have hpos : 0 < π.data.size := by
      have : π.size = π.data.size := rfl
      rw [← this, hlen]; simp only [pz6]; norm_num
    have hg : π.data.getD 0 0 = sByte := by simpa [isS] using hS
    rw [Array.getElem?_eq_getElem hpos]
    rw [Array.getD_eq_getD_getElem?, Array.getElem?_eq_getElem hpos] at hg
    simpa using hg
  have hK5 : inp.toArray.getD 5 0 &&& 0xFF = kindS := by
    apply BitVec.eq_of_toNat_eq
    rw [Lvm6.W.lowByte, getD_toArray, Lvm6.W.tape_byte0 c π L hb0]
    rfl
  have hZ : inp.toArray.getD 4 0 = BitVec.ofNat 64 pz6 := by
    rw [getD_toArray, tape_getD4, hlen]; rfl
  rw [if_pos hK5] at hk5
  rw [if_pos hZ] at hz5
  rw [extIRWith, semXIR_seq, semXIR_ite, if_neg (by rw [hk5]; decide), semXIR_ite,
    if_neg (by rw [hz5]; decide), dec6, semXIR_seq, semXIR_seq]
  rw [show semXIR inp.toArray descX (semXIR inp.toArray frontIR6 (semXIR inp.toArray (parseIR pz6)
    (initSt (mem6 + mpwX * inp.length)))) = preOut6 descX inp from rfl]
  rw [outIR6_sem inp.toArray _ hI t6 (UInt64.toNat_lt _) (hdrView P17 x).c' (hdrView P17 x).h
    (hdrView P17 x).n.toNat t12 t8 t7 (UInt64.toNat_lt _), hO, Array.toList_empty, List.nil_append,
    out_witOf6 hH]
  exact decodeWit_witWords _ (fits_witOf6 childFits6 _ _)


/-! ## The fill inside the descent's budget -/

/-- **`DescOk6` of a part followed by a descent**, the part's steps inside the descent's slack. -/
theorem descOk6_seq {p q : XIR} {c : ℕ} (hp : PartOk p c) (hq : DescOk6 q)
    (hc : ∀ t, c + cost q t + 1 ≤ descCost6 + 2 ^ 43) : DescOk6 (.seq p q) :=
  ⟨⟨hp.wf, hq.wf⟩, ⟨hp.noLoopT, hq.noLoopT⟩,
    fun t ↦ by show outs p t + outs q t = 0; rw [hp.outs t, hq.outs t],
    fun t ↦ by show cost p t + cost q t + 1 ≤ _; have := hp.cost t; have := hc t; omega⟩

/-- The numbers of `budgetD` with the fill's `2944 + 1` steps. -/
theorem budgetF :
    lvB 0 6 191 6 + lvB 1 4 128 1 + lvB 2 4 128 1 + lvB 3 4 128 1 + lvB 4 4 128 1 + finCap + 5 + 2945 ≤
      descCost6 + 2 ^ 43 := by
  simp only [lvB, descCost6, descLvl, rds, lns, ht6, lamCost, laneCost, treeC, levelC, parentC, bflyC, fwdC, wtabC,
    trCap, ldCap, finCap]
  norm_num

/-- `sizeIR` of a part followed by the descent, level by level (generic: no part is evaluated). -/
theorem sizeIR_seq_descX6 (p : XIR) (L : ℕ → LevelX) (fin : XIR) :
    sizeIR (.seq p (descX6 L fin)) = sizeIR p + (sizeIR (levelX 4 (L 4)) + (sizeIR (levelX 3 (L 3)) +
      (sizeIR (levelX 2 (L 2)) + (sizeIR (levelX 1 (L 1)) + (sizeIR (levelX 0 (L 0)) + sizeIR fin + 1) + 1) + 1) +
        1) + 1) + 1 := by
  rw [descX6, sizeIR_seq, sizeIR_seq, sizeIR_seq, sizeIR_seq, sizeIR_seq, sizeIR_seq]

/-- **The size of `fillIR ; descX6 (LvD F) finX`** (`≤ 2944 + 472,477 + 1`). -/
theorem sizeIR_F (F : FrontA) : sizeIR (.seq fillIR (descX6 (LvD F) finX)) ≤ 2 ^ 19 := by
  -- `rw` with `sizeIR_seq_descX6` and every size generalized: a `simp only [descX6, sizeIR]` here made the kernel
  -- evaluate `sizeIR fillIR` (the whole fill table, about a minute of replay).
  have h4 : sizeIR (levelX 4 (LvD F 4)) ≤ 2 ^ 13 + 1 * 42330 + 4 := sizeIR_levelX_le (levelSz F (by norm_num))
  have h3 : sizeIR (levelX 3 (LvD F 3)) ≤ 2 ^ 13 + 1 * 42330 + 4 := sizeIR_levelX_le (levelSz F (by norm_num))
  have h2 : sizeIR (levelX 2 (LvD F 2)) ≤ 2 ^ 13 + 1 * 42330 + 4 := sizeIR_levelX_le (levelSz F (by norm_num))
  have h1 : sizeIR (levelX 1 (LvD F 1)) ≤ 2 ^ 13 + 1 * 42330 + 4 := sizeIR_levelX_le (levelSz F (by norm_num))
  have h0 : sizeIR (levelX 0 (LvD F 0)) ≤ 2 ^ 13 + 6 * 42330 + 4 := sizeIR_levelX_le (levelSz F (by norm_num))
  have hf : sizeIR finX ≤ 2 ^ 13 := by rw [finX, sizeIR_finIR]; norm_num
  have hF := sizeIR_fillIR
  rw [sizeIR_seq_descX6]
  generalize sizeIR fillIR = a at hF ⊢
  generalize sizeIR finX = b at hf ⊢
  generalize sizeIR (levelX 0 (LvD F 0)) = c0 at h0 ⊢
  generalize sizeIR (levelX 1 (LvD F 1)) = c1 at h1 ⊢
  generalize sizeIR (levelX 2 (LvD F 2)) = c2 at h2 ⊢
  generalize sizeIR (levelX 3 (LvD F 3)) = c3 at h3 ⊢
  generalize sizeIR (levelX 4 (LvD F 4)) = c4 at h4 ⊢
  omega

variable {Φ : Phases} {SGood TGood : Hdr → Stack → Prop} (H : PhaseSpecs Φ Whir.I6 SGood TGood)
  (HG : Stmt.openGoodC Whir.GWDc Φ.whir) (hPF : PhasesFollow Φ P17) {VS : Shape → SProg}
  (Xe : ∀ vk, Ext6 (schemeOf (prog6 Φ) P17 vk) (Rel (accV (VS P17) vk)) (G6 SGood TGood))

include H HG hPF in
/-- **The extractor's fields of `Open6` at `P17`** for the extractor `front6 ; fillIR ; descX6 (LvD FDep)
finX`: from `PhasesFollow`, the deployed opening, and the tape sizes of every available log. -/
theorem open6XF (hw : Φ.whir = whirAt Whir.whirP) (hX : ∀ vk, (Xe vk).ext = ExtSpec6 (Whir.I6 P17))
    (hlog : ∀ vk c π L, Avail (kcertAsmG H HG hPF vk (Xe vk)) c π L →
      (∀ e ∈ L, e.1.size < 2 ^ 64) ∧ (extractorInput c π L).length ≤ 2 ^ 64)
    (hok : DescOk6 (.seq fillIR (descX6 (LvD FDep) finX))) :
    (∀ vk, ∃ K : KCert (schemeOf (prog6 Φ) P17 vk) (Rel (accV (VS P17) vk)),
      Scheme.εFS K ≤ (2 : ℝ≥0)⁻¹ ^ 128 ∧ ExtEq6 (EX6 (.seq fillIR (descX6 (LvD FDep) finX))) K) ∧
    (∀ c π L, isS π = false → EX6 (.seq fillIR (descX6 (LvD FDep) finX)) c π L =
      RecursionFast.WitnessSending.decode π) ∧
    Computes (extX6 (.seq fillIR (descX6 (LvD FDep) finX))) (EX6 (.seq fillIR (descX6 (LvD FDep) finX)))
      fuel6 ∧
    (extX6 (.seq fillIR (descX6 (LvD FDep) finX))).body.size ≤ progCap :=
  ⟨sound_asmG H HG hPF Xe fun vk ↦ ext_eq6A (kcertAsmG H HG hPF vk (Xe vk)) (Whir.I6 P17) (hX vk)
      (fun c π L hA ↦ len6_whirAt hPF hw vk c π L hA.1 hA.2.2.2) (goodL6 H HG hPF vk (Xe vk))
      fun c π L x h hA hE hl hG ↦ descendsD hPF hw hE hl (hlog vk c π L hA).1 (hlog vk c π L hA).2
        (Scheme.mu_lt_one hA.2.2.1).1 hG,
    wBranch6 _, computes6 hok, size_extX6 (sizeIR_F FDep)⟩

end Assembly

end Lvm6.X
