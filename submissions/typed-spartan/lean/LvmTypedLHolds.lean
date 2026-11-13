-- New for lvm2 (roll 8 = B1, wave L, L-B): facts of a checked typed layout (`Lay.Ok`) that the typed
-- certificate reads: every matrix entry lies on `Φ_Q`'s cube (`ents_fit`; `phiQ_fold`, `typedSpecR`), and the
-- per-slot facts behind `LvmTyped.holds_of_wiring`.
import LvmWiring

/-!
# Facts of a checked typed layout

* **`ents_fit`**: on a checked layout every entry of the four matrices has `o < 4`, its slot below `2^20` and its
  word below `2^21`: the entries are indices of `Φ_Q`'s cube of `phiVars = 43` variables.
* **`lh_holds`** (`LvmTyped.holds_of_wiring`): constraint slots are injective (`lh_slot_inj`; auxiliary slots
  differ, `lh_aux_ne_slot`), so a constraint slot's matrices are its instance's entries (`lh_ents_at`), whose words
  are the memory read off `z` (`lh_cellSum`); a `loadE` result's words are its operands' (`lh_wordE_load`), which
  are no constant cells (`lh_loadE_cst`; `wf` gives the three operands).
-/

set_option autoImplicit false

namespace Lvm.Typed

open Lvm.Loop

/-! ## The check, unfolded (helpers `lh_`) -/

theorem lh_ok {Q : Program} {lay : Lay} (hlay : lay.Ok Q) :
    lay.nInK = Q.nInK ∧ lay.nInE = Q.nInE ∧ lay.blocks.length = Q.blocks.length ∧
      blocksOk lay.nInK lay.xs 0 Q.nInK Q.nInE lay.blocks Q.blocks = true ∧
      auxOk lay.xs lay.blocks.length lay.aux = true ∧ xsSorted lay.xs = true ∧
      lay.inp.all dregFits = true ∧ lay.dense.all dregFits = true ∧ lay.one < 2 ^ yVars ∧
      cstOk lay.cst lay.nInK lay.blocks Q.blocks = true := by
  have h : lay.okB Q = true := hlay
  unfold Lay.okB at h
  rw [Bool.and_eq_true, Bool.and_eq_true, Bool.and_eq_true, Bool.and_eq_true, Bool.and_eq_true, Bool.and_eq_true,
    Bool.and_eq_true, Bool.and_eq_true, Bool.and_eq_true, Bool.and_eq_true, beq_iff_eq, beq_iff_eq, beq_iff_eq,
    decide_eq_true_eq] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩, -⟩, h8⟩, h9⟩, h10⟩, h11⟩ := h
  exact ⟨h1, h2, h3, h4, h5, h6, h8, h9, h10, h11⟩

/-- What `blocksOk` checks of one block (block index `b`, first cells `sK`, `sE`). -/
def lh_BOk (nInK : ℕ) (xs : List XChunk) (b sK sE : ℕ) (B : BLay) (Bq : Block) : Prop :=
  B.dims = Bq.dims ∧ B.stK = sK ∧ B.stE = sE ∧ B.twK = Bq.tw .K ∧ B.twE = Bq.tw .E ∧
    tplOk Bq.size nInK Bq.tpl B.cr B.srcK B.srcE 0 = true ∧ B.chK.all (chFits B.l .K) = true ∧
    B.chE.all (chFits B.l .E) = true ∧ chunksCover B.l (xs.filter (·.blk == b)) 0 (nCon Bq) = true

theorem lh_blocksOk_at (nInK : ℕ) (xs : List XChunk) : ∀ (Bs : List BLay) (Bqs : List Block) (b0 sK sE : ℕ),
    blocksOk nInK xs b0 sK sE Bs Bqs = true → Bs.length = Bqs.length ∧ ∀ i < Bs.length,
      lh_BOk nInK xs (b0 + i) (sK + ((Bqs.take i).map fun B ↦ B.tw .K * B.size).sum)
        (sE + ((Bqs.take i).map fun B ↦ B.tw .E * B.size).sum) (Bs.getD i default) (Bqs.getD i default) := by
  intro Bs
  induction Bs with
  | nil =>
    intro Bqs b0 sK sE h
    cases Bqs with
    | nil => exact ⟨rfl, fun i hi ↦ absurd hi (Nat.not_lt_zero _)⟩
    | cons _ _ => simp [blocksOk] at h
  | cons B Bs ih =>
    intro Bqs b0 sK sE h
    cases Bqs with
    | nil => simp [blocksOk] at h
    | cons Bq Bqs =>
      unfold blocksOk at h
      simp only [Bool.and_eq_true, beq_iff_eq] at h
      obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨hd, hK⟩, hE⟩, htK⟩, htE⟩, htpl⟩, hcK⟩, hcE⟩, hcov⟩, hrest⟩ := h
      obtain ⟨ihl, ih2⟩ := ih Bqs _ _ _ hrest
      refine ⟨by simp [ihl], fun i hi ↦ ?_⟩
      cases i with
      | zero => exact ⟨hd, hK, hE, htK, htE, htpl, hcK, hcE, hcov⟩
      | succ i =>
        obtain ⟨a1, a2, a3, a4, a5, a6, a7, a8, a9⟩ := ih2 i (by simpa using hi)
        simp only [List.getD_cons_succ, List.take_succ_cons, List.map_cons, List.sum_cons]
        refine ⟨a1, ?_, ?_, a4, a5, a6, a7, a8, ?_⟩
        · rw [a2, htK, Nat.add_assoc]
        · rw [a3, htE, Nat.add_assoc]
        · rwa [show b0 + (i + 1) = b0 + 1 + i by omega]

/-- **Block `b` of a checked layout** is what `blocksOk` checks. -/
theorem lh_blk {Q : Program} {lay : Lay} (hlay : lay.Ok Q) {b : ℕ} (hb : b < lay.blocks.length) :
    lh_BOk lay.nInK lay.xs b (Q.start .K b) (Q.start .E b) (lay.blocks.getD b default) (Q.blk b) := by
  obtain ⟨-, -, -, h4, -⟩ := lh_ok hlay
  have := (lh_blocksOk_at _ _ _ _ _ _ _ h4).2 b hb
  rwa [Nat.zero_add] at this

theorem lh_auxOk_at (xs : List XChunk) : ∀ (As : List ABlk) (k0 : ℕ), auxOk xs k0 As = true → ∀ k < As.length,
    (∀ r ∈ (As.getD k default).rows, ∀ e ∈ r.ops, e.1 < 4 ∧ aopFits (As.getD k default).l e.2.1 = true) ∧
      chunksCover (As.getD k default).l (xs.filter (·.blk == k0 + k)) 0 (As.getD k default).rows.length = true := by
  intro As
  induction As with
  | nil => intro _ _ k hk; exact absurd hk (Nat.not_lt_zero _)
  | cons A As ih =>
    intro k0 h k hk
    unfold auxOk at h
    simp only [Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq] at h
    obtain ⟨⟨h1, h2⟩, h3⟩ := h
    cases k with
    | zero => exact ⟨h1, h2⟩
    | succ k =>
      obtain ⟨a1, a2⟩ := ih (k0 + 1) h3 k (by simpa using hk)
      refine ⟨a1, ?_⟩
      rw [List.getD_cons_succ, show k0 + (k + 1) = k0 + 1 + k by omega]
      exact a2

/-- **Auxiliary block `k` of a checked layout**. -/
theorem lh_aux {Q : Program} {lay : Lay} (hlay : lay.Ok Q) {k : ℕ} (hk : k < lay.aux.length) :
    (∀ r ∈ (lay.aux.getD k default).rows, ∀ e ∈ r.ops, e.1 < 4 ∧ aopFits (lay.aux.getD k default).l e.2.1 = true) ∧
      chunksCover (lay.aux.getD k default).l (lay.xs.filter (·.blk == lay.blocks.length + k)) 0
        (lay.aux.getD k default).rows.length = true :=
  lh_auxOk_at _ _ _ (lh_ok hlay).2.2.2.2.1 k hk

theorem lh_cover_l (l : ℕ) : ∀ (cs : List XChunk) (r n : ℕ), chunksCover l cs r n = true → ∀ c ∈ cs, c.l = l ∧ 0 < c.n
  | [], _, _, _, c, hc => absurd hc List.not_mem_nil
  | c :: cs, r, n, h, d, hd => by
    unfold chunksCover at h
    simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at h
    rcases List.mem_cons.mp hd with rfl | hd
    · exact ⟨h.1.1.1, h.1.2⟩
    · exact lh_cover_l l cs _ n h.2 d hd

theorem lh_xs_top : ∀ (xs : List XChunk), xsSorted xs = true → ∀ c ∈ xs, c.top ≤ 2 ^ xVars
  | [], _, c, hc => absurd hc List.not_mem_nil
  | [c], h, c', hc => by
    rw [List.mem_singleton] at hc; subst hc
    unfold xsSorted at h; exact of_decide_eq_true h
  | c :: c' :: cs, h, d, hd => by
    unfold xsSorted at h
    rw [Bool.and_eq_true, decide_eq_true_eq] at h
    have ih := lh_xs_top (c' :: cs) h.2
    rcases List.mem_cons.mp hd with rfl | hd
    · have h1 := ih c' List.mem_cons_self
      have h2 : c'.base ≤ c'.top := Nat.le_add_right _ _
      omega
    · exact ih d hd

/-- A chunked slot lies below its chunk's top, hence below `2^xVars`. -/
theorem lh_slotR_lt {Q : Program} {lay : Lay} (hlay : lay.Ok Q) (b r jf : ℕ)
    (hl : ∀ c ∈ lay.xs, c.blk = b → jf < 2 ^ c.l) : lay.slotR b r jf < 2 ^ xVars := by
  unfold Lay.slotR
  split
  · rename_i c hc
    have hm := List.mem_of_find?_eq_some hc
    have hp := List.find?_some hc
    simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at hp
    have htop := lh_xs_top _ (lh_ok hlay).2.2.2.2.2.1 c hm
    have hj := hl c hm hp.1
    unfold XChunk.top at htop
    have h1 : (r - c.r0) * 2 ^ c.l + jf < c.n * 2 ^ c.l := by
      have : r - c.r0 + 1 ≤ c.n := by omega
      calc (r - c.r0) * 2 ^ c.l + jf < (r - c.r0) * 2 ^ c.l + 2 ^ c.l := by omega
        _ = (r - c.r0 + 1) * 2 ^ c.l := by rw [Nat.add_mul, Nat.one_mul]
        _ ≤ c.n * 2 ^ c.l := Nat.mul_le_mul_right _ this
    omega
  · exact Nat.two_pow_pos _

/-! ## Words below `2^yVars` -/

theorem lh_getD_bound (L : List ℕ) (K N : ℕ) (hne : 0 < L.length) (h : ∀ b ∈ L, b + K ≤ N) (m : ℕ) :
    L.getD m 0 + K ≤ N := by
  rw [List.getD_eq_getElem?_getD]
  by_cases hm : m < L.length
  · rw [List.getElem?_eq_getElem hm, Option.getD_some]; exact h _ (List.getElem_mem hm)
  · rw [List.getElem?_eq_none (by omega), Option.getD_none, Nat.zero_add]
    have := h _ (List.getElem_mem hne); omega

theorem lh_limbs_pos (τ : Ty) : 0 < τ.limbs := by cases τ <;> decide

/-- A cell of a fitting region: its word is below `2^yVars`. -/
theorem lh_dword_lt (d : DReg) (hd : dregFits d = true) (n m : ℕ) (h1 : d.lo ≤ n) (h2 : n < d.lo + d.n) :
    d.word n m < 2 ^ yVars := by
  unfold dregFits at hd
  unfold DReg.word
  split
  · rename_i hl
    simp only [hl, ↓reduceIte, Bool.and_eq_true, beq_iff_eq, List.all_eq_true] at hd
    have := lh_getD_bound d.bases d.n (2 ^ yVars) (by rw [hd.1]; exact lh_limbs_pos _)
      (fun b hb ↦ of_decide_eq_true (hd.2 b hb)) m
    omega
  · rename_i hl
    simp only [hl, ↓reduceIte, Bool.and_eq_true, beq_iff_eq, List.all_eq_true, decide_eq_true_eq] at hd
    obtain ⟨⟨⟨-, hmod⟩, hlen⟩, hall⟩ := hd
    have hpos : 0 < d.lanes := by omega
    have hi : (n - d.lo) % d.lanes < d.laneBases.length := by rw [hlen]; exact Nat.mod_lt _ hpos
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi, Option.getD_some]
    have hb := hall _ (List.getElem_mem hi)
    have hq : (n - d.lo) / d.lanes < d.n / d.lanes := by
      obtain ⟨q, hq⟩ := Nat.dvd_of_mod_eq_zero hmod
      rw [hq, Nat.mul_div_cancel_left _ hpos, Nat.div_lt_iff_lt_mul hpos]
      rw [hq] at h2; rw [Nat.mul_comm]; omega
    omega

theorem lh_dreg?_some {lay : Lay} {τ : Ty} {n : ℕ} {d : DReg} (h : lay.dreg? τ n = some d) :
    d ∈ lay.dense ++ lay.inp ∧ d.ty = τ ∧ d.lo ≤ n ∧ n < d.lo + d.n := by
  have hm := List.mem_of_find?_eq_some h
  have hp := List.find?_some h
  simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at hp
  exact ⟨hm, hp.1, hp.2.1, hp.2.2⟩

theorem lh_dreg_word_lt {Q : Program} {lay : Lay} (hlay : lay.Ok Q) {τ : Ty} {n : ℕ} {d : DReg}
    (hd : lay.dreg? τ n = some d) (m : ℕ) : d.word n m < 2 ^ yVars := by
  obtain ⟨hm, -, h1, h2⟩ := lh_dreg?_some hd
  obtain ⟨-, -, -, -, -, -, hi, hde, -⟩ := lh_ok hlay
  rw [List.all_eq_true] at hi hde
  rcases List.mem_append.mp hm with hm | hm
  · exact lh_dword_lt d (hde d hm) n m h1 h2
  · exact lh_dword_lt d (hi d hm) n m h1 h2

theorem lh_wordD_lt {Q : Program} {lay : Lay} (hlay : lay.Ok Q) (τ : Ty) (n m : ℕ) : lay.wordD τ n m < 2 ^ yVars := by
  unfold Lay.wordD
  split
  · exact lh_dreg_word_lt hlay ‹_› m
  · exact Nat.two_pow_pos _

theorem lh_slotWord_lt (B : BLay) (τ : Ty) (hch : (B.ch τ).all (chFits B.l τ) = true) (s jf m : ℕ)
    (hjf : jf < 2 ^ B.l) : B.slotWord τ s jf m < 2 ^ yVars := by
  unfold BLay.slotWord
  split
  · rename_i c hc
    have hm := List.mem_of_find?_eq_some hc
    have hp := List.find?_some hc
    simp only [decide_eq_true_eq] at hp
    have hf := List.all_eq_true.mp hch c hm
    unfold chFits at hf
    rw [Bool.and_eq_true, beq_iff_eq, List.all_eq_true] at hf
    have := lh_getD_bound c.bases (c.n * 2 ^ B.l) (2 ^ yVars) (by rw [hf.1]; exact lh_limbs_pos _)
      (fun b hb ↦ of_decide_eq_true (hf.2 b hb)) m
    have h1 : (s - c.s0) * 2 ^ B.l + jf < c.n * 2 ^ B.l := by
      have : s - c.s0 + 1 ≤ c.n := by omega
      calc (s - c.s0) * 2 ^ B.l + jf < (s - c.s0) * 2 ^ B.l + 2 ^ B.l := by omega
        _ = (s - c.s0 + 1) * 2 ^ B.l := by rw [Nat.add_mul, Nat.one_mul]
        _ ≤ c.n * 2 ^ B.l := Nat.mul_le_mul_right _ this
    omega
  · exact Nat.two_pow_pos _

/-- The owner of a cell: a block whose range holds it. -/
theorem lh_owner?_some {lay : Lay} {τ : Ty} {n b : ℕ} (h : lay.owner? τ n = some b) :
    b < lay.blocks.length ∧ (lay.blocks.getD b default).st τ ≤ n ∧
      n < (lay.blocks.getD b default).st τ + (lay.blocks.getD b default).tw τ * 2 ^ (lay.blocks.getD b default).l := by
  have hm := List.mem_of_find?_eq_some h
  have hp := List.find?_some h
  simp only [decide_eq_true_eq] at hp
  exact ⟨List.mem_range.mp hm, hp⟩

/-- An owned cell's iteration `(n − st) / tw` is below `2^l`. -/
theorem lh_iter_lt {st tw l n : ℕ} (h1 : st ≤ n) (h2 : n < st + tw * 2 ^ l) : (n - st) / tw < 2 ^ l := by
  have hpos : 0 < tw := by
    rcases Nat.eq_zero_or_pos tw with h | h
    · rw [h, Nat.zero_mul] at h2; omega
    · exact h
  rw [Nat.div_lt_iff_lt_mul hpos, Nat.mul_comm]; omega

theorem lh_wordK_lt {Q : Program} {lay : Lay} (hlay : lay.Ok Q) (n : ℕ) : lay.wordK n < 2 ^ yVars := by
  unfold Lay.wordK
  split
  · rename_i b hb
    obtain ⟨hbl, h1, h2⟩ := lh_owner?_some hb
    obtain ⟨-, -, -, -, -, -, hcK, -, -⟩ := lh_blk hlay hbl
    dsimp only
    split
    · unfold Lay.wordC
      split
      · exact lh_dreg_word_lt hlay ‹_› 0
      · exact lh_slotWord_lt _ .K hcK _ _ _ (lh_iter_lt h1 h2)
    · exact lh_wordD_lt hlay _ _ _
    · exact Nat.two_pow_pos _
  · exact lh_wordD_lt hlay _ _ _

theorem lh_wordE_lt {Q : Program} {lay : Lay} (hlay : lay.Ok Q) (n m : ℕ) : lay.wordE n m < 2 ^ yVars := by
  unfold Lay.wordE
  split
  · rename_i b hb
    obtain ⟨hbl, h1, h2⟩ := lh_owner?_some hb
    obtain ⟨-, -, -, -, -, -, -, hcE, -⟩ := lh_blk hlay hbl
    dsimp only
    split
    · unfold Lay.wordC
      split
      · exact lh_dreg_word_lt hlay ‹_› m
      · exact lh_slotWord_lt _ .E hcE _ _ _ (lh_iter_lt h1 h2)
    · exact lh_wordK_lt hlay _
    · exact Nat.two_pow_pos _
  · exact lh_wordD_lt hlay _ _ _

/-- **A cell's words are below `2^yVars`.** -/
theorem lh_cellEnts_lt {Q : Program} {lay : Lay} (hlay : lay.Ok Q) (τ : Ty) (n : ℕ) (w : FE) :
    ∀ p ∈ lay.cellEnts τ n w, p.1 < 2 ^ yVars := by
  intro p hp
  cases τ with
  | K =>
    simp only [Lay.cellEnts] at hp
    cases hc : lay.cst? n with
    | some v =>
      simp only [hc, List.mem_singleton] at hp; subst hp; exact (lh_ok hlay).2.2.2.2.2.2.2.2.1
    | none => simp only [hc, List.mem_singleton] at hp; subst hp; exact lh_wordK_lt hlay n
  | E =>
    simp only [Lay.cellEnts, List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with rfl | rfl | rfl <;> exact lh_wordE_lt hlay _ _

/-! ## The entries -/

theorem lh_mem_tagE {o x : ℕ} {l : List (ℕ × FE)} {e : Ent} (h : e ∈ tagE o x l) : e.o = o ∧ e.x = x ∧ (e.y, e.c) ∈ l := by
  obtain ⟨p, hp, rfl⟩ := List.mem_map.mp h
  exact ⟨rfl, rfl, hp⟩

/-- An instance's entries: matrix `o < 4`, its slot, and a word of an operand, the result or the constant `1`. -/
theorem lh_instEnts_mem (Q : Program) (lay : Lay) (i : Inst) {e : Ent} (he : e ∈ instEnts Q lay i) :
    e.o < 4 ∧ e.x = lay.slot i.blk i.t i.jf ∧ (e.y = lay.one ∨ ∃ τ n w, (e.y, e.c) ∈ lay.cellEnts τ n w) := by
  unfold instEnts at he
  split at he
  · simp only [List.mem_append] at he
    rcases he with ((he | he) | he) | he <;> obtain ⟨h1, h2, h3⟩ := lh_mem_tagE he <;>
      exact ⟨by omega, h2, Or.inr ⟨_, _, _, h3⟩⟩
  · simp only [List.mem_append] at he
    rcases he with he | he <;> obtain ⟨h1, h2, h3⟩ := lh_mem_tagE he
    · refine ⟨by omega, h2, ?_⟩
      simp only [List.mem_append, List.mem_singleton] at h3
      rcases h3 with (h3 | h3) | h3
      · exact Or.inr ⟨_, _, _, h3⟩
      · exact Or.inr ⟨_, _, _, h3⟩
      · exact Or.inl (Prod.mk.inj h3).1
    · exact ⟨by omega, h2, Or.inr ⟨_, _, _, h3⟩⟩
  · simp only [List.mem_append] at he
    rcases he with he | he <;> obtain ⟨h1, h2, h3⟩ := lh_mem_tagE he <;>
      exact ⟨by omega, h2, Or.inr ⟨_, _, _, h3⟩⟩
  · simp only [List.mem_append] at he
    rcases he with he | he <;> obtain ⟨h1, h2, h3⟩ := lh_mem_tagE he
    · refine ⟨by omega, h2, ?_⟩
      simp only [List.mem_append] at h3
      rcases h3 with h3 | h3 <;> exact Or.inr ⟨_, _, _, h3⟩
    · exact ⟨by omega, h2, Or.inr ⟨_, _, _, h3⟩⟩
  · exact absurd he List.not_mem_nil

theorem lh_getD_mem {α : Type} [Inhabited α] (l : List α) {i : ℕ} (hi : i < l.length) : l.getD i default ∈ l := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi, Option.getD_some]; exact List.getElem_mem hi

/-- Only constraint rows have entries. -/
theorem lh_instEnts_con (Q : Program) (lay : Lay) (i : Inst) {e : Ent} (he : e ∈ instEnts Q lay i) :
    Row.isCon i.row = true := by
  unfold instEnts at he
  unfold Row.isCon
  split at he <;> (rename_i hop; first | rw [hop] | exact absurd he List.not_mem_nil)

/-- The instances of a program: block `b`, iteration `jf`, template row `t`, all in range. -/
theorem lh_mem_insts {Q : Program} {i : Inst} (hi : i ∈ Q.insts) :
    ∃ b < Q.blocks.length, ∃ jf < 2 ^ (Q.blk b).lsize, ∃ t < (Q.blk b).tpl.length, i = Q.inst b jf t := by
  rw [phi_insts] at hi
  simp only [List.mem_flatMap, List.mem_range, List.mem_map] at hi
  obtain ⟨b, hb, jf, hjf, t, ht, rfl⟩ := hi
  exact ⟨b, hb, jf, hjf, t, ht, rfl⟩

/-- The chunks of block `b < nB` have the block's iteration count. -/
theorem lh_blk_chunk_l {Q : Program} {lay : Lay} (hlay : lay.Ok Q) {b : ℕ} (hb : b < Q.blocks.length) :
    ∀ c ∈ lay.xs, c.blk = b → c.l = (Q.blk b).lsize ∧ 0 < c.n := by
  intro c hc hcb
  have hb' : b < lay.blocks.length := by rw [(lh_ok hlay).2.2.1]; exact hb
  obtain ⟨hd, -, -, -, -, -, -, -, hcov⟩ := lh_blk hlay hb'
  have := lh_cover_l _ _ _ _ hcov c (List.mem_filter.mpr ⟨hc, by simp [hcb]⟩)
  refine ⟨?_, this.2⟩
  rw [this.1, BLay.l, hd, Block.lsize]

/-- The chunks of auxiliary block `k` have its iteration count. -/
theorem lh_aux_chunk_l {Q : Program} {lay : Lay} (hlay : lay.Ok Q) {k : ℕ} (hk : k < lay.aux.length) :
    ∀ c ∈ lay.xs, c.blk = lay.blocks.length + k → c.l = (lay.aux.getD k default).l ∧ 0 < c.n := by
  intro c hc hcb
  exact lh_cover_l _ _ _ _ (lh_aux hlay hk).2 c (List.mem_filter.mpr ⟨hc, by simp [hcb]⟩)

theorem lh_slot_lt {Q : Program} {lay : Lay} (hlay : lay.Ok Q) {b jf : ℕ} (hb : b < Q.blocks.length)
    (hjf : jf < 2 ^ (Q.blk b).lsize) (t : ℕ) : lay.slot b t jf < 2 ^ xVars := by
  unfold Lay.slot
  split
  · exact lh_slotR_lt hlay _ _ _ fun c hc hcb ↦ by rw [(lh_blk_chunk_l hlay hb c hc hcb).1]; exact hjf
  · exact Nat.two_pow_pos _

/-- **Every entry lies on `Φ_Q`'s cube** (a checked layout): matrix `o < 4`, slot `x < 2^20`, word `y < 2^21`. -/
theorem ents_fit (Q : Program) (lay : Lay) (hlay : lay.Ok Q) :
    ∀ e ∈ ents Q lay, e.o < 4 ∧ e.x < 2 ^ xVars ∧ e.y < 2 ^ yVars := by
  have hone := (lh_ok hlay).2.2.2.2.2.2.2.2.1
  intro e he
  rcases List.mem_append.mp he with he | he
  · obtain ⟨i, hi, he⟩ := List.mem_flatMap.mp he
    obtain ⟨b, hb, jf, hjf, t, -, rfl⟩ := lh_mem_insts hi
    obtain ⟨h1, h2, h3⟩ := lh_instEnts_mem Q lay _ he
    refine ⟨h1, h2 ▸ lh_slot_lt hlay hb hjf t, ?_⟩
    rcases h3 with h3 | ⟨τ, n, w, h3⟩
    · rw [h3]; exact hone
    · exact lh_cellEnts_lt hlay τ n w _ h3
  · unfold auxEnts at he
    simp only [List.mem_flatMap, List.mem_range] at he
    obtain ⟨k, hk, j, hj, r, hr, he⟩ := he
    unfold auxRowEnts at he
    obtain ⟨op, hop, he⟩ := List.mem_flatMap.mp he
    obtain ⟨h1, h2, h3⟩ := lh_mem_tagE he
    obtain ⟨ho, hfit⟩ := (lh_aux hlay hk).1 _ (lh_getD_mem _ hr) op hop
    refine ⟨h1 ▸ ho, ?_, ?_⟩
    · rw [h2]
      exact lh_slotR_lt hlay _ _ _ fun c hc hcb ↦ by rw [(lh_aux_chunk_l hlay hk c hc hcb).1]; exact hj
    · obtain ⟨o, a, w⟩ := op
      cases a with
      | word base stride =>
        simp only [Lay.aopEnts, List.mem_singleton, Prod.mk.injEq] at h3
        rw [h3.1]
        unfold aopFits at hfit
        have hfit := of_decide_eq_true hfit
        have : stride * j ≤ stride * (2 ^ (lay.aux.getD k default).l - 1) := Nat.mul_le_mul_left _ (by omega)
        omega
      | cell a => exact lh_cellEnts_lt hlay _ _ _ _ h3
      | one =>
        simp only [Lay.aopEnts, List.mem_singleton, Prod.mk.injEq] at h3
        rw [h3.1]; exact hone

/-! ## The template walk -/

/-- The constraint rows before row `t`. -/
def lh_cnt (rows : List Row) (t : ℕ) : ℕ := ((rows.take t).filter Row.isCon).length

theorem lh_tplOk_step (size nInK : ℕ) (r : Row) (rs : List Row) (c : Option ℕ) (cr : List (Option ℕ))
    (sK sE : List CSrc) (rC : ℕ) (h : tplOk size nInK (r :: rs) (c :: cr) sK sE rC = true) :
    c = (if Row.isCon r then some rC else none) ∧
      (r.writes = some .K → srcOk r size nInK (sK.getD 0 default) = true) ∧
      (r.writes = some .E → srcOk r size nInK (sE.getD 0 default) = true) ∧
      tplOk size nInK rs cr (sK.drop (r.w .K)) (sE.drop (r.w .E)) (if Row.isCon r then rC + 1 else rC) = true := by
  have hwK : r.writes = some .K → r.w .K = 1 ∧ r.w .E = 0 := fun hw ↦ by simp [Row.w, hw]
  have hwE : r.writes = some .E → r.w .K = 0 ∧ r.w .E = 1 := fun hw ↦ by simp [Row.w, hw]
  have hwN : r.writes = none → r.w .K = 0 ∧ r.w .E = 0 := fun hw ↦ by simp [Row.w, hw]
  unfold tplOk at h
  rcases hw : r.writes with _ | τ
  · rw [hw] at h
    simp only [Bool.and_eq_true, beq_iff_eq] at h
    obtain ⟨h1, h2⟩ := hwN hw
    refine ⟨h.1, (fun h' ↦ by cases h'), (fun h' ↦ by cases h'), ?_⟩
    rw [h1, h2, List.drop_zero, List.drop_zero]; exact h.2
  · cases τ with
    | K =>
      rw [hw] at h
      obtain ⟨h1, h2⟩ := hwK hw
      cases sK with
      | nil => cases h
      | cons s sK' =>
        simp only [Bool.and_eq_true, beq_iff_eq] at h
        refine ⟨h.1.1, (fun _ ↦ h.1.2), (fun h' ↦ by cases h'), ?_⟩
        rw [h1, h2, List.drop_zero, List.drop_one, List.tail_cons]; exact h.2
    | E =>
      rw [hw] at h
      obtain ⟨h1, h2⟩ := hwE hw
      cases sE with
      | nil => cases h
      | cons s sE' =>
        simp only [Bool.and_eq_true, beq_iff_eq] at h
        refine ⟨h.1.1, (fun h' ↦ by cases h'), (fun _ ↦ h.1.2), ?_⟩
        rw [h1, h2, List.drop_zero, List.drop_one, List.tail_cons]; exact h.2

theorem lh_getD_drop {α : Type} (l : List α) (i j : ℕ) (d : α) : (l.drop i).getD j d = l.getD (i + j) d := by
  rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, List.getElem?_drop]

/-- **The template walk**: row `t`'s constraint rank is the count of constraint rows before it; its source is
the next one of its memory. -/
theorem lh_tplOk (size nInK : ℕ) : ∀ (rows : List Row) (cr : List (Option ℕ)) (sK sE : List CSrc) (rC : ℕ),
    tplOk size nInK rows cr sK sE rC = true → ∀ t < rows.length,
      cr.getD t none = (if Row.isCon (rows.getD t default) then some (rC + lh_cnt rows t) else none) ∧
      ((rows.getD t default).writes = some .K →
        srcOk (rows.getD t default) size nInK (sK.getD ((rows.take t).map (Row.w .K)).sum default) = true) ∧
      ((rows.getD t default).writes = some .E →
        srcOk (rows.getD t default) size nInK (sE.getD ((rows.take t).map (Row.w .E)).sum default) = true) := by
  intro rows
  induction rows with
  | nil => intro _ _ _ _ _ t ht; exact absurd ht (Nat.not_lt_zero _)
  | cons r rs ih =>
    intro cr sK sE rC h t ht
    cases cr with
    | nil => cases rs <;> simp [tplOk] at h
    | cons c cr =>
      obtain ⟨h1, h2, h3, h4⟩ := lh_tplOk_step size nInK r rs c cr sK sE rC h
      cases t with
      | zero =>
        simp only [List.getD_cons_zero, lh_cnt, List.take_zero, List.filter_nil, List.length_nil, Nat.add_zero,
          List.map_nil, List.sum_nil]
        exact ⟨h1, h2, h3⟩
      | succ t =>
        obtain ⟨a1, a2, a3⟩ := ih _ _ _ _ h4 t (by simpa using ht)
        simp only [List.getD_cons_succ, List.take_succ_cons, List.map_cons, List.sum_cons]
        refine ⟨?_, fun hw ↦ ?_, fun hw ↦ ?_⟩
        · rw [a1]
          unfold lh_cnt
          rw [List.take_succ_cons, List.filter_cons]
          by_cases hc : Row.isCon r = true
          · simp only [hc, ↓reduceIte, List.length_cons]; congr 2; omega
          · simp only [hc, ↓reduceIte, Bool.false_eq_true]
        · rw [← lh_getD_drop]; exact a2 hw
        · rw [← lh_getD_drop]; exact a3 hw

theorem lh_cnt_lt (rows : List Row) {t t' : ℕ} (ht : t < rows.length) (htt : t < t')
    (hc : Row.isCon (rows.getD t default) = true) : lh_cnt rows t < ((rows.take t').filter Row.isCon).length := by
  have h1 : ((rows.take (t + 1)).filter Row.isCon).length = lh_cnt rows t + 1 := by
    unfold lh_cnt
    rw [List.take_add_one, List.filter_append, List.length_append, List.getElem?_eq_getElem ht]
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem ht, Option.getD_some] at hc
    simp [hc]
  have h2 := ((List.take_sublist_take_left (l := rows) (show t + 1 ≤ t' by omega)).filter Row.isCon).length_le
  omega

/-- Distinct constraint rows have distinct ranks. -/
theorem lh_cnt_inj (rows : List Row) {t t' : ℕ} (ht : t < rows.length) (ht' : t' < rows.length)
    (hc : Row.isCon (rows.getD t default) = true) (hc' : Row.isCon (rows.getD t' default) = true)
    (h : lh_cnt rows t = lh_cnt rows t') : t = t' := by
  rcases Nat.lt_trichotomy t t' with h1 | h1 | h1
  · have := lh_cnt_lt rows ht h1 hc; unfold lh_cnt at this h; omega
  · exact h1
  · have := lh_cnt_lt rows ht' h1 hc'; unfold lh_cnt at this h; omega

theorem lh_rank_lt (B : Block) (τ : Ty) {t : ℕ} (ht : t < B.tpl.length) (hw : (B.tpl.getD t default).writes = some τ) :
    B.rank τ t < B.tw τ := by
  unfold Block.rank Block.tw
  conv => rhs; rw [← List.take_append_drop t B.tpl, List.drop_eq_getElem_cons ht]
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem ht, Option.getD_some] at hw
  simp only [List.map_append, List.map_cons, List.sum_append, List.sum_cons, Row.w, hw, ↓reduceIte]
  omega

/-! ## Chunks and slots -/

theorem lh_cover_mem (l : ℕ) : ∀ (cs : List XChunk) (r n : ℕ), chunksCover l cs r n = true → ∀ ρ, r ≤ ρ → ρ < n →
    ∃ c ∈ cs, c.r0 ≤ ρ ∧ ρ < c.r0 + c.n
  | [], r, n, h, ρ, h1, h2 => by unfold chunksCover at h; rw [beq_iff_eq] at h; omega
  | c :: cs, r, n, h, ρ, h1, h2 => by
    unfold chunksCover at h
    simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at h
    by_cases hρ : ρ < r + c.n
    · exact ⟨c, List.mem_cons_self, by omega, by omega⟩
    · obtain ⟨c', hc', h3⟩ := lh_cover_mem l cs _ n h.2 ρ (by omega) h2
      exact ⟨c', List.mem_cons_of_mem _ hc', h3⟩

/-- A chunk holding rank `ρ` of block `b` makes `xchunk?` find one. -/
theorem lh_xchunk?_some {lay : Lay} {b ρ : ℕ} (h : ∃ c ∈ lay.xs, c.blk = b ∧ c.r0 ≤ ρ ∧ ρ < c.r0 + c.n) :
    ∃ c, lay.xchunk? b ρ = some c := by
  obtain ⟨c, hc, h1, h2, h3⟩ := h
  have : (lay.xchunk? b ρ).isSome = true := by
    unfold Lay.xchunk?
    rw [List.find?_isSome]
    exact ⟨c, hc, by simp [h1, h2, h3]⟩
  exact Option.isSome_iff_exists.mp this

theorem lh_xchunk?_spec {lay : Lay} {b ρ : ℕ} {c : XChunk} (h : lay.xchunk? b ρ = some c) :
    c ∈ lay.xs ∧ c.blk = b ∧ c.r0 ≤ ρ ∧ ρ < c.r0 + c.n := by
  have hm := List.mem_of_find?_eq_some h
  have hp := List.find?_some h
  simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at hp
  exact ⟨hm, hp.1, hp.2.1, hp.2.2⟩

theorem lh_pairwise_cases {α : Type} {R : α → α → Prop} : ∀ {l : List α}, l.Pairwise R → ∀ {a b : α}, a ∈ l → b ∈ l →
    a = b ∨ R a b ∨ R b a
  | [], _, _, _, ha, _ => absurd ha List.not_mem_nil
  | x :: l, h, a, b, ha, hb => by
    rw [List.pairwise_cons] at h
    rcases List.mem_cons.mp ha with h1 | h1 <;> rcases List.mem_cons.mp hb with h2 | h2
    · exact Or.inl (h1.trans h2.symm)
    · subst h1; exact Or.inr (Or.inl (h.1 _ h2))
    · subst h2; exact Or.inr (Or.inr (h.1 _ h1))
    · exact lh_pairwise_cases h.2 h1 h2

theorem lh_xs_pairwise : ∀ (xs : List XChunk), xsSorted xs = true → xs.Pairwise fun c c' ↦ c.top ≤ c'.base
  | [], _ => List.Pairwise.nil
  | [_], _ => List.pairwise_singleton _ _
  | c :: c' :: cs, h => by
    unfold xsSorted at h
    rw [Bool.and_eq_true, decide_eq_true_eq] at h
    have ih := lh_xs_pairwise (c' :: cs) h.2
    refine List.Pairwise.cons (fun d hd ↦ ?_) ih
    rcases List.mem_cons.mp hd with rfl | hd
    · exact h.1
    · have := (List.pairwise_cons.mp ih).1 d hd
      have : c'.base ≤ c'.top := Nat.le_add_right _ _
      omega

theorem lh_mul_add_inj {a a' j j' L : ℕ} (hj : j < L) (hj' : j' < L) (h : a * L + j = a' * L + j') :
    a = a' ∧ j = j' := by
  have hL : 0 < L := by omega
  have h1 : ∀ a j, j < L → (a * L + j) / L = a ∧ (a * L + j) % L = j := fun a j hj ↦ by
    rw [Nat.mul_comm, Nat.mul_add_div hL, Nat.mul_add_mod, Nat.div_eq_of_lt hj, Nat.mod_eq_of_lt hj, Nat.add_zero]
    exact ⟨rfl, rfl⟩
  obtain ⟨h2, h3⟩ := h1 a j hj
  obtain ⟨h4, h5⟩ := h1 a' j' hj'
  rw [h] at h2 h3
  exact ⟨h2 ▸ h4, h3 ▸ h5⟩

/-- **Slots are injective**: two found chunks' slots agree only at the same block, rank and iteration. -/
theorem lh_slotR_inj {Q : Program} {lay : Lay} (hlay : lay.Ok Q) {b b' ρ ρ' jf jf' : ℕ} {c c' : XChunk}
    (hc : lay.xchunk? b ρ = some c) (hc' : lay.xchunk? b' ρ' = some c') (hj : jf < 2 ^ c.l) (hj' : jf' < 2 ^ c'.l)
    (h : lay.slotR b ρ jf = lay.slotR b' ρ' jf') : b = b' ∧ ρ = ρ' ∧ jf = jf' := by
  unfold Lay.slotR at h
  rw [hc, hc'] at h
  dsimp only at h
  obtain ⟨hm, hb, h1, h2⟩ := lh_xchunk?_spec hc
  obtain ⟨hm', hb', h1', h2'⟩ := lh_xchunk?_spec hc'
  have hlt : ∀ (d : XChunk) (r j : ℕ), d.r0 ≤ r → r < d.r0 + d.n → j < 2 ^ d.l →
      d.base + (r - d.r0) * 2 ^ d.l + j < d.top := by
    intro d r j h1 h2 hj
    unfold XChunk.top
    have : r - d.r0 + 1 ≤ d.n := by omega
    have : (r - d.r0 + 1) * 2 ^ d.l ≤ d.n * 2 ^ d.l := Nat.mul_le_mul_right _ this
    rw [Nat.add_mul, Nat.one_mul] at this
    omega
  have e1 := hlt c ρ jf h1 h2 hj
  have e2 := hlt c' ρ' jf' h1' h2' hj'
  rcases lh_pairwise_cases (lh_xs_pairwise _ (lh_ok hlay).2.2.2.2.2.1) hm hm' with rfl | hr | hr
  · obtain ⟨h3, h4⟩ := lh_mul_add_inj (a := ρ - c.r0) (a' := ρ' - c.r0) hj hj' (by omega)
    exact ⟨hb.symm.trans hb', by omega, h4⟩
  · omega
  · omega

/-- **A constraint row's chunk**: its rank is found, in a chunk of its block's iteration count. -/
theorem lh_con_chunk {Q : Program} {lay : Lay} (hlay : lay.Ok Q) {b t : ℕ} (hb : b < Q.blocks.length)
    (ht : t < (Q.blk b).tpl.length) (hc : Row.isCon ((Q.blk b).tpl.getD t default) = true) :
    ∃ c, (lay.blocks.getD b default).cr.getD t none = some (lh_cnt (Q.blk b).tpl t) ∧
      lay.xchunk? b (lh_cnt (Q.blk b).tpl t) = some c ∧ c.l = (Q.blk b).lsize := by
  have hb' : b < lay.blocks.length := by rw [(lh_ok hlay).2.2.1]; exact hb
  obtain ⟨-, -, -, -, -, htpl, -, -, hcov⟩ := lh_blk hlay hb'
  have hcr := (lh_tplOk _ _ _ _ _ _ _ htpl t ht).1
  simp only [hc, ↓reduceIte, Nat.zero_add] at hcr
  have hlt : lh_cnt (Q.blk b).tpl t < nCon (Q.blk b) := by
    have := lh_cnt_lt (Q.blk b).tpl ht (Nat.lt_succ_self t |>.trans_le (Nat.succ_le_of_lt ht)) hc
    rwa [List.take_length] at this
  obtain ⟨c, hcm, h1, h2⟩ := lh_cover_mem _ _ _ _ hcov _ (Nat.zero_le _) hlt
  have hcm' := List.mem_filter.mp hcm
  obtain ⟨c', hc'⟩ := lh_xchunk?_some (lay := lay) ⟨c, hcm'.1, by simpa using hcm'.2, h1, h2⟩
  obtain ⟨hm, hbk, -, -⟩ := lh_xchunk?_spec hc'
  exact ⟨c', hcr, hc', (lh_blk_chunk_l hlay hb c' hm hbk).1⟩

/-- **An auxiliary row's chunk.** -/
theorem lh_aux_chunk {Q : Program} {lay : Lay} (hlay : lay.Ok Q) {k r : ℕ} (hk : k < lay.aux.length)
    (hr : r < (lay.aux.getD k default).rows.length) :
    ∃ c, lay.xchunk? (lay.blocks.length + k) r = some c ∧ c.l = (lay.aux.getD k default).l := by
  obtain ⟨c, hcm, h1, h2⟩ := lh_cover_mem _ _ _ _ (lh_aux hlay hk).2 r (Nat.zero_le _) hr
  have hcm' := List.mem_filter.mp hcm
  obtain ⟨c', hc'⟩ := lh_xchunk?_some (lay := lay) ⟨c, hcm'.1, by simpa using hcm'.2, h1, h2⟩
  obtain ⟨hm, hbk, -, -⟩ := lh_xchunk?_spec hc'
  exact ⟨c', hc', (lh_aux_chunk_l hlay hk c' hm hbk).1⟩

/-- **Constraint slots are injective** over the instances. -/
theorem lh_slot_inj {Q : Program} {lay : Lay} (hlay : lay.Ok Q) {b b' t t' jf jf' : ℕ}
    (hb : b < Q.blocks.length) (ht : t < (Q.blk b).tpl.length) (hjf : jf < 2 ^ (Q.blk b).lsize)
    (hc : Row.isCon ((Q.blk b).tpl.getD t default) = true)
    (hb' : b' < Q.blocks.length) (ht' : t' < (Q.blk b').tpl.length) (hjf' : jf' < 2 ^ (Q.blk b').lsize)
    (hc' : Row.isCon ((Q.blk b').tpl.getD t' default) = true)
    (h : lay.slot b t jf = lay.slot b' t' jf') : b = b' ∧ t = t' ∧ jf = jf' := by
  obtain ⟨c, hcr, hx, hl⟩ := lh_con_chunk hlay hb ht hc
  obtain ⟨c', hcr', hx', hl'⟩ := lh_con_chunk hlay hb' ht' hc'
  unfold Lay.slot at h
  rw [hcr, hcr'] at h
  obtain ⟨rfl, h2, h3⟩ := lh_slotR_inj hlay hx hx' (hl ▸ hjf) (hl' ▸ hjf') h
  exact ⟨rfl, lh_cnt_inj _ ht ht' hc hc' h2, h3⟩

/-- **An auxiliary slot is no constraint slot.** -/
theorem lh_aux_ne_slot {Q : Program} {lay : Lay} (hlay : lay.Ok Q) {b t jf : ℕ}
    (hb : b < Q.blocks.length) (ht : t < (Q.blk b).tpl.length) (hjf : jf < 2 ^ (Q.blk b).lsize)
    (hc : Row.isCon ((Q.blk b).tpl.getD t default) = true) :
    ∀ e ∈ auxEnts lay, e.x ≠ lay.slot b t jf := by
  intro e he hx
  unfold auxEnts at he
  simp only [List.mem_flatMap, List.mem_range] at he
  obtain ⟨k, hk, j, hj, r, hr, he⟩ := he
  unfold auxRowEnts at he
  obtain ⟨op, -, he⟩ := List.mem_flatMap.mp he
  obtain ⟨-, h2, -⟩ := lh_mem_tagE he
  obtain ⟨c, hcr, hx1, hl⟩ := lh_con_chunk hlay hb ht hc
  obtain ⟨c', hx2, hl'⟩ := lh_aux_chunk hlay hk hr
  unfold Lay.slot at hx
  rw [h2, hcr, Lay.auxSlot] at hx
  have := (lh_slotR_inj hlay hx2 hx1 (hl' ▸ hj) (hl ▸ hjf) hx).1
  have : b < lay.blocks.length := by rw [(lh_ok hlay).2.2.1]; exact hb
  omega

/-! ## The matrices at a constraint slot -/

/-- An entry list's value against `z`. -/
def lh_val (z : ℕ → FK) (es : List Ent) : FE := (es.map fun e ↦ e.c * FE.ofK (z e.y)).sum

/-- A word list's value against `z`. -/
def lh_psum (z : ℕ → FK) (l : List (ℕ × FE)) : FE := (l.map fun p ↦ p.2 * FE.ofK (z p.1)).sum

theorem lh_matZ_eq (Q : Program) (lay : Lay) (o : ℕ) (z : ℕ → FK) (x : ℕ) :
    matZ Q lay o z x = lh_val z ((ents Q lay).filter fun e ↦ e.o == o && e.x == x) :=
  phi_foldr_eq_sum (fun e : Ent ↦ e.c * FE.ofK (z e.y)) _

theorem lh_flatMap_single {β : Type} (n a0 : ℕ) (f : ℕ → List β) (h0 : a0 < n) (h : ∀ a < n, a ≠ a0 → f a = []) :
    (List.range n).flatMap f = f a0 := by
  induction n with
  | zero => omega
  | succ n ih =>
    rw [List.range_succ, List.flatMap_append, List.flatMap_singleton]
    by_cases hn : a0 = n
    · subst hn
      rw [List.flatMap_eq_nil_iff.mpr fun a ha ↦ h a (by rw [List.mem_range] at ha; omega)
        (by rw [List.mem_range] at ha; omega), List.nil_append]
    · rw [ih (by omega) (fun a ha hne ↦ h a (by omega) hne), h n (by omega) (Ne.symm hn), List.append_nil]

/-- **At a constraint slot only its instance has entries.** -/
theorem lh_ents_at {Q : Program} {lay : Lay} (hlay : lay.Ok Q) {b t jf : ℕ}
    (hb : b < Q.blocks.length) (ht : t < (Q.blk b).tpl.length) (hjf : jf < 2 ^ (Q.blk b).lsize)
    (hc : Row.isCon ((Q.blk b).tpl.getD t default) = true) (o : ℕ) :
    (ents Q lay).filter (fun e ↦ e.o == o && e.x == lay.slot b t jf) =
      (instEnts Q lay (Q.inst b jf t)).filter (·.o == o) := by
  have hother : ∀ b' < Q.blocks.length, ∀ jf' < 2 ^ (Q.blk b').lsize, ∀ t' < (Q.blk b').tpl.length,
      ¬ (b' = b ∧ jf' = jf ∧ t' = t) →
        (instEnts Q lay (Q.inst b' jf' t')).filter (fun e ↦ e.o == o && e.x == lay.slot b t jf) = [] := by
    intro b' hb' jf' hjf' t' ht' hne
    rw [List.filter_eq_nil_iff]
    intro e he hp
    have h2 := (lh_instEnts_mem Q lay _ he).2.1
    have hcon := lh_instEnts_con Q lay _ he
    simp only [Bool.and_eq_true, beq_iff_eq] at hp
    have := lh_slot_inj hlay hb' ht' hjf' hcon hb ht hjf hc (h2.symm.trans hp.2)
    exact hne ⟨this.1, this.2.2, this.2.1⟩
  have haux : (auxEnts lay).filter (fun e ↦ e.o == o && e.x == lay.slot b t jf) = [] := by
    rw [List.filter_eq_nil_iff]
    intro e he hp
    simp only [Bool.and_eq_true, beq_iff_eq] at hp
    exact lh_aux_ne_slot hlay hb ht hjf hc e he hp.2
  rw [ents, List.filter_append, haux, List.append_nil, List.filter_flatMap, phi_insts, List.flatMap_assoc]
  rw [lh_flatMap_single _ b _ hb ?_]
  · rw [List.flatMap_assoc, lh_flatMap_single _ jf _ hjf ?_]
    · rw [List.flatMap_map, lh_flatMap_single _ t _ ht ?_]
      · refine List.filter_congr fun e he ↦ ?_
        have h2 : e.x = lay.slot b t jf := (lh_instEnts_mem Q lay _ he).2.1
        simp only [h2, beq_self_eq_true, Bool.and_true]
      · intro t' ht' hne; exact hother b hb jf hjf t' ht' fun h ↦ hne h.2.2
    · intro jf' hjf' hne
      rw [List.flatMap_map, List.flatMap_eq_nil_iff]
      intro t' ht'
      exact hother b hb jf' hjf' t' (List.mem_range.mp ht') fun h ↦ hne h.2.1
  · intro b' hb' hne
    rw [List.flatMap_assoc, List.flatMap_eq_nil_iff]
    intro jf' hjf'
    rw [List.flatMap_map, List.flatMap_eq_nil_iff]
    intro t' ht'
    exact hother b' hb' jf' (List.mem_range.mp hjf') t' (List.mem_range.mp ht') fun h ↦ hne h.1

theorem lh_val_tagE (z : ℕ → FK) (o x : ℕ) (l : List (ℕ × FE)) (o' : ℕ) :
    lh_val z ((tagE o x l).filter (·.o == o')) = if o = o' then lh_psum z l else 0 := by
  induction l with
  | nil => simp [tagE, lh_val, lh_psum]
  | cons p l ih =>
    by_cases h : o = o'
    · subst h
      simp only [tagE, lh_val, lh_psum, ↓reduceIte] at ih ⊢
      simp [ih]
    · simp only [tagE, lh_val, h, ↓reduceIte] at ih ⊢
      simp [h, ih]

theorem lh_val_append (z : ℕ → FK) (l1 l2 : List Ent) (p : Ent → Bool) :
    lh_val z ((l1 ++ l2).filter p) = lh_val z (l1.filter p) + lh_val z (l2.filter p) := by
  simp only [lh_val, List.filter_append, List.map_append, List.sum_append]

theorem lh_psum_append (z : ℕ → FK) (l1 l2 : List (ℕ × FE)) : lh_psum z (l1 ++ l2) = lh_psum z l1 + lh_psum z l2 := by
  simp only [lh_psum, List.map_append, List.sum_append]

theorem lh_ofK_one : FE.ofK 1 = 1 := FE.ofKRingHom.map_one

/-- **A cell's words against `z`** are its value in the memory read off `z`. -/
theorem lh_cellSum {lay : Lay} {z : ℕ → FK} (hone : z lay.one = 1) (τ : Ty) (n : ℕ) (w : FE) :
    lh_psum z (lay.cellEnts τ n w) = w * (memOf lay z).rd τ n := by
  cases τ with
  | K =>
    simp only [Lay.cellEnts, Mem.rd, memOf]
    cases hc : lay.cst? n with
    | some v => simp [lh_psum, hone, lh_ofK_one]
    | none => simp [lh_psum]
  | E =>
    simp only [Lay.cellEnts, lh_psum, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Mem.rd, memOf]
    ring

theorem lh_argSum {lay : Lay} {z : ℕ → FK} (hone : z lay.one = 1) (i : Inst) (k : ℕ) (w : FE) :
    lh_psum z (lay.argEnts i k w) = w * (memOf lay z).arg i k :=
  lh_cellSum hone _ _ _

theorem lh_resSum {lay : Lay} {z : ℕ → FK} (hone : z lay.one = 1) (i : Inst) :
    lh_psum z (lay.resEnts i) = (memOf lay z).res i := by
  rw [Lay.resEnts, lh_cellSum hone, one_mul]; rfl

theorem lh_c2 {a w : FE} (h : a + w = 0) : w = a := by
  rw [← neg_eq_of_add_eq_zero_right h, CharTwo.neg_eq]

theorem lh_psum_one {lay : Lay} {z : ℕ → FK} (hone : z lay.one = 1) (c : FE) : lh_psum z [(lay.one, c)] = c := by
  simp [lh_psum, hone, lh_ofK_one]

/-! ## `loadE` results -/

/-- **The owner of a cell in a block's range** is the block (the ranges are disjoint). -/
theorem lh_owner?_eq {Q : Program} {lay : Lay} (hlay : lay.Ok Q) (τ : Ty) {b n : ℕ} (hb : b < lay.blocks.length)
    (h1 : (lay.blocks.getD b default).st τ ≤ n)
    (h2 : n < (lay.blocks.getD b default).st τ + (lay.blocks.getD b default).tw τ * 2 ^ (lay.blocks.getD b default).l) :
    lay.owner? τ n = some b := by
  have hp := (K.fl_blocksOk_chain _ _ τ _ _ _ _ _ (lh_ok hlay).2.2.2.1).2
  rw [List.pairwise_iff_getElem] at hp
  have hg : ∀ i (hi : i < lay.blocks.length), lay.blocks.getD i default = lay.blocks[i] := fun i hi ↦ by
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi, Option.getD_some]
  cases hf : lay.owner? τ n with
  | none =>
    exfalso
    unfold Lay.owner? at hf
    rw [List.find?_eq_none] at hf
    exact hf b (List.mem_range.mpr hb) (by simp only [decide_eq_true_eq]; exact ⟨h1, h2⟩)
  | some b' =>
    obtain ⟨hb', h1', h2'⟩ := lh_owner?_some hf
    congr 1
    rw [hg b hb] at h1 h2
    rw [hg b' hb'] at h1' h2'
    rcases Nat.lt_trichotomy b' b with h | h | h
    · have := hp b' b hb' hb h; omega
    · exact h
    · have := hp b b' hb hb' h; omega

/-- **A `loadE` result's words** are its operands' words at the iteration. -/
theorem lh_wordE_load {Q : Program} {lay : Lay} (hlay : lay.Ok Q) {b jf t : ℕ} (hb : b < Q.blocks.length)
    (ht : t < (Q.blk b).tpl.length) (hjf : jf < 2 ^ (Q.blk b).lsize) (args : List Addr)
    (hw : ((Q.blk b).tpl.getD t default).writes = some .E)
    (hsrc : (lay.blocks.getD b default).srcE.getD ((Q.blk b).rank .E t) default = .load args) (m : ℕ) :
    lay.wordE (Q.start .E b + (Q.blk b).tw .E * jf + (Q.blk b).rank .E t) m =
      lay.wordK ((args.getD m default).at (unflat (Q.blk b).dims jf)) := by
  have hb' : b < lay.blocks.length := by rw [(lh_ok hlay).2.2.1]; exact hb
  obtain ⟨hd, -, hE, -, htE, -⟩ := lh_blk hlay hb'
  have hr := lh_rank_lt (Q.blk b) .E ht hw
  have hl : (lay.blocks.getD b default).l = (Q.blk b).lsize := by rw [BLay.l, hd, Block.lsize]
  have hown : lay.owner? .E (Q.start .E b + (Q.blk b).tw .E * jf + (Q.blk b).rank .E t) = some b := by
    refine lh_owner?_eq hlay .E hb' ?_ ?_
    · simp only [BLay.st, hE]; omega
    · simp only [BLay.st, BLay.tw, hE, htE, hl]
      have : (Q.blk b).tw .E * (jf + 1) ≤ (Q.blk b).tw .E * 2 ^ (Q.blk b).lsize := Nat.mul_le_mul_left _ hjf
      rw [Nat.mul_add, Nat.mul_one] at this
      omega
  have hoff : Q.start .E b + (Q.blk b).tw .E * jf + (Q.blk b).rank .E t - (lay.blocks.getD b default).stE =
      (Q.blk b).tw .E * jf + (Q.blk b).rank .E t := by rw [hE]; omega
  have htw : 0 < (Q.blk b).tw .E := by omega
  unfold Lay.wordE
  rw [hown]
  dsimp only
  rw [hoff, htE, Nat.mul_add_mod, Nat.mod_eq_of_lt hr, hsrc]
  dsimp only
  rw [Nat.mul_add_div htw, Nat.div_eq_of_lt hr, Nat.add_zero, hd]

theorem lh_cst?_none {lay : Lay} {lo hi n : ℕ} (h : cstMiss lay.cst lo hi = true) (h1 : lo ≤ n) (h2 : n ≤ hi) :
    lay.cst? n = none := by
  unfold Lay.cst?
  rw [Option.map_eq_none_iff, List.find?_eq_none]
  intro r hr hp
  have := List.all_eq_true.mp h r hr
  simp only [Bool.or_eq_true, decide_eq_true_eq] at this hp
  omega

theorem lh_dot_le : ∀ (s dims : List ℕ) (jf : ℕ), dot s (unflat dims jf) ≤ dot s (dims.map fun d ↦ 2 ^ d - 1)
  | [], _, _ => by simp [dot]
  | _ :: _, [], _ => by simp [dot, unflat]
  | s :: ss, d :: ds, jf => by
    simp only [unflat, List.map_cons, dot]
    have h1 : jf % 2 ^ d ≤ 2 ^ d - 1 := by have := Nat.mod_lt jf (Nat.two_pow_pos d); omega
    have := Nat.mul_le_mul_left s h1
    have := lh_dot_le ss ds (jf / 2 ^ d)
    omega

/-- **A `loadE` operand is never a constant cell** (`cstOk`). -/
theorem lh_loadE_cst {Q : Program} {lay : Lay} (hlay : lay.Ok Q) {b t : ℕ} (hb : b < Q.blocks.length)
    (ht : t < (Q.blk b).tpl.length) (hop : ((Q.blk b).tpl.getD t default).op = .loadE) {a : Addr}
    (ha : a ∈ ((Q.blk b).tpl.getD t default).args) (jf : ℕ) : lay.cst? (a.at (unflat (Q.blk b).dims jf)) = none := by
  have h := (lh_ok hlay).2.2.2.2.2.2.2.2.2
  unfold cstOk at h
  rw [Bool.and_eq_true, Bool.and_eq_true] at h
  have h1 := List.all_eq_true.mp (List.all_eq_true.mp h.1.2 _ (lh_getD_mem Q.blocks hb)) _ (lh_getD_mem _ ht)
  have hop2 : ((Q.blocks.getD b default).tpl.getD t default).op = .loadE := hop
  rw [hop2] at h1
  simp only [Op.kind, bne_self_eq_false, Bool.false_or, List.all_eq_true] at h1
  exact lh_cst?_none (h1 a ha) (Nat.le_add_right _ _) (Nat.add_le_add_left (lh_dot_le _ _ _) _)

theorem lh_wf_typeOk {Q : Program} (hwf : Q.wf = true) {b t : ℕ} (hb : b < Q.blocks.length)
    (ht : t < (Q.blk b).tpl.length) : ((Q.blk b).tpl.getD t default).typeOk = true := by
  unfold Program.wf at hwf
  have := List.all_eq_true.mp (List.all_eq_true.mp hwf b (List.mem_range.mpr hb)) t (List.mem_range.mpr ht)
  unfold Program.rowOk at this
  rw [Bool.and_eq_true, Bool.and_eq_true] at this
  exact this.1.1

/-- **`wf`'s operand count of `loadE`**: three `K` operands, an `E` result. -/
theorem lh_loadE_args {r : Row} (hop : r.op = .loadE) (h : r.typeOk = true) :
    r.ty = .E ∧ ∃ a0 a1 a2, r.args = [a0, a1, a2] ∧ a0.ty = .K ∧ a1.ty = .K ∧ a2.ty = .K := by
  simp only [Row.typeOk, hop, Bool.and_eq_true, beq_iff_eq] at h
  obtain ⟨h1, h2⟩ := h
  refine ⟨h2, ?_⟩
  obtain ⟨a0, l1, e1, t0, h1a⟩ := List.map_eq_cons_iff.mp h1
  obtain ⟨a1, l2, e2, t1, h1b⟩ := List.map_eq_cons_iff.mp h1a
  obtain ⟨a2, l3, e3, t2, h1c⟩ := List.map_eq_cons_iff.mp h1b
  rw [List.map_eq_nil_iff] at h1c
  rw [e1, e2, e3, h1c]
  exact ⟨a0, a1, a2, rfl, t0, t1, t2⟩

theorem lh_srcOk_load {r : Row} {size nInK : ℕ} {s : CSrc} (hop : r.op = .loadE) (h : srcOk r size nInK s = true) :
    s = .load r.args := by
  cases s
  · simp [srcOk, hop, Op.kind] at h
  · simp only [srcOk, Bool.and_eq_true, beq_iff_eq] at h
    rw [h.1.2]
  · simp [srcOk, hop, Op.kind] at h

/-! ## The relations -/

/-- **One instance's relation and assertion** (L-B, for `LvmTyped.rowDef_of_wiring`): with the program check,
on a checked layout, with `z(one) = 1` and the relation at every slot; a `readd` instance's relation is assumed
(the mini-bus's or the static one), no other instance needs it. -/
theorem lh_row (Q : Program) (lay : Lay) (z : ℕ → FK) (hwf : Q.wf = true) (hlay : lay.Ok Q)
    (hone : z lay.one = 1) (h : WiringRel Q lay z) {i : Inst} (hi : i ∈ Q.insts)
    (hrd : ∀ lo m, i.row.op = .readd lo m → Q.RowDef (memOf lay z) i) :
    Q.RowDef (memOf lay z) i ∧ Program.RowAssert (memOf lay z) i := by
  obtain ⟨b, hb, jf, hjf, t, ht, rfl⟩ := lh_mem_insts hi
  have hV : Row.isCon (Q.inst b jf t).row = true →
      lh_val z ((instEnts Q lay (Q.inst b jf t)).filter (·.o == 0)) *
          lh_val z ((instEnts Q lay (Q.inst b jf t)).filter (·.o == 1)) +
        lh_val z ((instEnts Q lay (Q.inst b jf t)).filter (·.o == 2)) +
        lh_val z ((instEnts Q lay (Q.inst b jf t)).filter (·.o == 3)) = 0 := by
    intro hc
    have := h (lay.slot b t jf)
    simp only [matA, matB, matD, matW, lh_matZ_eq, lh_ents_at hlay hb ht hjf hc] at this
    exact this
  rcases hop : (Q.inst b jf t).row.op with _ | ⟨k, k'⟩ | _ | _ | _ | ⟨lo, m⟩
  · -- muladd
    have := hV (by simp only [Row.isCon, hop])
    simp only [instEnts, hop, lh_val_append, lh_val_tagE, Nat.reduceEqDiff, ↓reduceIte, add_zero, zero_add,
      lh_argSum hone, lh_resSum hone, one_mul] at this
    simp only [Program.RowDef, Program.RowAssert, hop, and_true]
    exact lh_c2 this
  · -- lin
    have := hV (by simp only [Row.isCon, hop])
    simp only [instEnts, hop, lh_val_append, lh_val_tagE, Nat.reduceEqDiff, ↓reduceIte, add_zero, zero_add,
      mul_zero, lh_psum_append, lh_argSum hone, lh_resSum hone, lh_psum_one hone, one_mul] at this
    simp only [Program.RowDef, Program.RowAssert, hop, and_true]
    exact lh_c2 this
  · -- assert0
    have := hV (by simp only [Row.isCon, hop])
    simp only [instEnts, hop, lh_val_append, lh_val_tagE, Nat.reduceEqDiff, ↓reduceIte, add_zero, zero_add,
      lh_argSum hone, one_mul] at this
    simp only [Program.RowDef, Program.RowAssert, hop, true_and]
    simpa [lh_val] using this
  · -- loadE
    simp only [Program.RowDef, Program.RowAssert, hop, and_true]
    have hop' : ((Q.blk b).tpl.getD t default).op = .loadE := hop
    obtain ⟨hty, a0, a1, a2, hargs, t0, t1, t2⟩ := lh_loadE_args hop' (lh_wf_typeOk hwf hb ht)
    have hw : ((Q.blk b).tpl.getD t default).writes = some .E := by simp only [Row.writes, hop', hty]
    have hb' : b < lay.blocks.length := by rw [(lh_ok hlay).2.2.1]; exact hb
    obtain ⟨-, -, -, -, -, htpl, -⟩ := lh_blk hlay hb'
    have hsrc := lh_srcOk_load hop' ((lh_tplOk _ _ _ _ _ _ _ htpl t ht).2.2 hw)
    have hres : (memOf lay z).res (Q.inst b jf t) =
        (memOf lay z).e (Q.start .E b + (Q.blk b).tw .E * jf + (Q.blk b).rank .E t) := by
      unfold Mem.res
      rw [show (Q.inst b jf t).row.ty = .E from hty]
      rfl
    have harg : ∀ m < 3, (memOf lay z).arg (Q.inst b jf t) m =
        FE.ofK (z (lay.wordK ((((Q.blk b).tpl.getD t default).args.getD m default).at (unflat (Q.blk b).dims jf)))) := by
      intro m hm
      have hmem := lh_getD_mem ((Q.blk b).tpl.getD t default).args (i := m) (by rw [hargs]; simpa using hm)
      have hK : (((Q.blk b).tpl.getD t default).args.getD m default).ty = .K := by
        rw [hargs]; interval_cases m <;> simp [t0, t1, t2]
      have hcst := lh_loadE_cst hlay hb ht hop' hmem jf
      show (memOf lay z).rd (((Q.blk b).tpl.getD t default).args.getD m default).ty
        ((((Q.blk b).tpl.getD t default).args.getD m default).at (unflat (Q.blk b).dims jf)) = _
      rw [hK]
      simp only [Mem.rd, memOf, hcst, Option.getD_none]
    rw [hres, harg 0 (by omega), harg 1 (by omega), harg 2 (by omega)]
    simp only [memOf]
    rw [lh_wordE_load hlay hb ht hjf _ hw hsrc 0, lh_wordE_load hlay hb ht hjf _ hw hsrc 1,
      lh_wordE_load hlay hb ht hjf _ hw hsrc 2]
  · -- fixmul
    have := hV (by simp only [Row.isCon, hop])
    simp only [instEnts, hop, lh_val_append, lh_val_tagE, Nat.reduceEqDiff, ↓reduceIte, add_zero, zero_add,
      mul_zero, lh_psum_append, lh_argSum hone, lh_resSum hone, one_mul] at this
    simp only [Program.RowDef, Program.RowAssert, hop, and_true]
    exact lh_c2 this
  · -- readd
    refine ⟨hrd lo m hop, ?_⟩
    simp only [Program.RowAssert, hop]

/-- **The wiring relation is the program's relations** (`LvmTyped.holds_of_wiring`): with the program check (for
`loadE`'s operand count), on a checked layout, with `z(one) = 1`, the relation at every slot and every `readd`'s
relation. -/
theorem lh_holds (Q : Program) (lay : Lay) (z : ℕ → FK) (hwf : Q.wf = true) (hlay : lay.Ok Q)
    (hone : z lay.one = 1) (h : WiringRel Q lay z)
    (hrd : ∀ i ∈ Q.insts, ∀ lo m, i.row.op = .readd lo m → Q.RowDef (memOf lay z) i) :
    Q.Holds (memOf lay z) ∧ Q.Asserts (memOf lay z) :=
  ⟨fun i hi ↦ (lh_row Q lay z hwf hlay hone h hi (hrd i hi)).1,
    fun i hi ↦ (lh_row Q lay z hwf hlay hone h hi (hrd i hi)).2⟩

/-! ## The auxiliary rows (`BITS`) -/

/-- An auxiliary operand's value at iteration `j`: a free word, a cell of the memory read off `z`, the constant
`1`. -/
def aopVal (lay : Lay) (z : ℕ → FK) (j : ℕ) : AOp → FE
  | .word b s => FE.ofK (z (b + s * j))
  | .cell a => (memOf lay z).rd a.ty (a.at [j])
  | .one => 1

/-- Matrix `o`'s part of an auxiliary row at iteration `j`: `Σ_{(o', op, w) ∈ ops, o' = o} w · val(op)`. -/
def aRowMat (lay : Lay) (z : ℕ → FK) (j : ℕ) (row : ARow) (o : ℕ) : FE :=
  ((row.ops.filter fun e ↦ e.1 == o).map fun e ↦ e.2.2 * aopVal lay z j e.2.1).sum

/-- **An auxiliary row holds at an iteration**: `A·B + D + W = 0`. -/
def ARowHolds (lay : Lay) (z : ℕ → FK) (j : ℕ) (row : ARow) : Prop :=
  aRowMat lay z j row 0 * aRowMat lay z j row 1 + aRowMat lay z j row 2 + aRowMat lay z j row 3 = 0

/-- **At an auxiliary slot only its row has entries.** -/
theorem lh_ents_at_aux {Q : Program} {lay : Lay} (hlay : lay.Ok Q) {k r j : ℕ} (hk : k < lay.aux.length)
    (hr : r < (lay.aux.getD k default).rows.length) (hj : j < 2 ^ (lay.aux.getD k default).l) (o : ℕ) :
    (ents Q lay).filter (fun e ↦ e.o == o && e.x == lay.auxSlot k r j) =
      (auxRowEnts lay k r j).filter (·.o == o) := by
  obtain ⟨c, hc, hcl⟩ := lh_aux_chunk hlay hk hr
  have hinst : (Q.insts.flatMap (instEnts Q lay)).filter (fun e ↦ e.o == o && e.x == lay.auxSlot k r j) = [] := by
    rw [List.filter_eq_nil_iff]
    intro e he hp
    simp only [Bool.and_eq_true, beq_iff_eq] at hp
    obtain ⟨i, hi, he⟩ := List.mem_flatMap.mp he
    obtain ⟨b, hb, jf, hjf, t, ht, rfl⟩ := lh_mem_insts hi
    have hcon := lh_instEnts_con Q lay _ he
    have hx : e.x = lay.slot b t jf := (lh_instEnts_mem Q lay _ he).2.1
    obtain ⟨c', hcr, hx1, hl⟩ := lh_con_chunk hlay hb ht hcon
    unfold Lay.slot at hx
    rw [hcr] at hx
    have := (lh_slotR_inj hlay hx1 hc (hl ▸ hjf) (hcl ▸ hj) (hx.symm.trans hp.2)).1
    have : b < lay.blocks.length := by rw [(lh_ok hlay).2.2.1]; exact hb
    omega
  have haux : ∀ k' < lay.aux.length, ∀ j' < 2 ^ (lay.aux.getD k' default).l,
      ∀ r' < (lay.aux.getD k' default).rows.length, ¬ (k' = k ∧ j' = j ∧ r' = r) →
        (auxRowEnts lay k' r' j').filter (fun e ↦ e.o == o && e.x == lay.auxSlot k r j) = [] := by
    intro k' hk' j' hj' r' hr' hne
    rw [List.filter_eq_nil_iff]
    intro e he hp
    simp only [Bool.and_eq_true, beq_iff_eq] at hp
    unfold auxRowEnts at he
    obtain ⟨op, -, he⟩ := List.mem_flatMap.mp he
    obtain ⟨-, h2, -⟩ := lh_mem_tagE he
    obtain ⟨c', hc', hcl'⟩ := lh_aux_chunk hlay hk' hr'
    have := lh_slotR_inj hlay hc' hc (hcl' ▸ hj') (hcl ▸ hj) (h2.symm.trans hp.2)
    exact hne ⟨by omega, this.2.2, this.2.1⟩
  rw [ents, List.filter_append, hinst, List.nil_append, auxEnts]
  simp only [List.filter_flatMap]
  rw [lh_flatMap_single _ k _ hk fun k' hk' hne ↦ ?_]
  · rw [lh_flatMap_single _ j _ hj fun j' hj' hne ↦ ?_]
    · rw [lh_flatMap_single _ r _ hr fun r' hr' hne ↦ haux k hk j hj r' hr' fun h ↦ hne h.2.2]
      refine List.filter_congr fun e he ↦ ?_
      unfold auxRowEnts at he
      obtain ⟨op, -, he⟩ := List.mem_flatMap.mp he
      have h2 : e.x = lay.auxSlot k r j := (lh_mem_tagE he).2.1
      simp only [h2, beq_self_eq_true, Bool.and_true]
    · rw [List.flatMap_eq_nil_iff]
      intro r' hr'
      exact haux k hk j' hj' r' (List.mem_range.mp hr') fun h ↦ hne h.2.1
  · rw [List.flatMap_eq_nil_iff]
    intro j' hj'
    rw [List.flatMap_eq_nil_iff]
    intro r' hr'
    exact haux k' hk' j' (List.mem_range.mp hj') r' (List.mem_range.mp hr') fun h ↦ hne h.1

theorem lh_aopSum {lay : Lay} {z : ℕ → FK} (hone : z lay.one = 1) (j : ℕ) (w : FE) (op : AOp) :
    lh_psum z (lay.aopEnts j w op) = w * aopVal lay z j op := by
  cases op with
  | word b s => simp [Lay.aopEnts, lh_psum, aopVal]
  | cell a => exact lh_cellSum hone _ _ _
  | one => rw [Lay.aopEnts, lh_psum_one hone, aopVal, mul_one]

theorem lh_auxVal {lay : Lay} {z : ℕ → FK} (hone : z lay.one = 1) (k r j o : ℕ) :
    lh_val z ((auxRowEnts lay k r j).filter (·.o == o)) =
      aRowMat lay z j ((lay.aux.getD k default).rows.getD r default) o := by
  unfold auxRowEnts aRowMat
  induction ((lay.aux.getD k default).rows.getD r default).ops with
  | nil => simp [lh_val]
  | cons e es ih =>
    rw [List.flatMap_cons, lh_val_append, lh_val_tagE, ih, lh_aopSum hone]
    by_cases h : e.1 = o
    · simp [h]
    · simp [h]

/-- **An auxiliary row holds** at every iteration (a checked layout, `z(one) = 1`, the wiring relation). -/
theorem lh_auxRow (Q : Program) (lay : Lay) (z : ℕ → FK) (hlay : lay.Ok Q) (hone : z lay.one = 1)
    (h : WiringRel Q lay z) {k r j : ℕ} (hk : k < lay.aux.length) (hj : j < 2 ^ (lay.aux.getD k default).l)
    (hr : r < (lay.aux.getD k default).rows.length) :
    ARowHolds lay z j ((lay.aux.getD k default).rows.getD r default) := by
  have := h (lay.auxSlot k r j)
  simp only [matA, matB, matD, matW, lh_matZ_eq, lh_ents_at_aux hlay hk hr hj, lh_auxVal hone] at this
  exact this

end Lvm.Typed
