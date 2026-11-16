-- New for lvm2 E2F (slice S1, E2F-Q; E2AC-DES §6 statement 10, "`Ty.E2` in LoopIR", renamed "the `E2` rows in
-- LoopIR" with E2F-LEAD's approval of the twin-row design, 2026-11-13).
import LvmLoopInterp

/-!
# The `E2` rows of LoopIR

Statement 10 of E2AC-DES §6 asks for a 2-word cell type `Ty.E2` and `interp_unique` restated with it. lvm2 E2F
realises the 2-word cell without a third memory (`LvmLoopIR`, `Op.e2`): an `E2` value is the pair of `K` cells
`(c, c + 1)` written by a twin pair of adjacent template rows `e2 f false`, `e2 f true` with the same operands
(`Program.twinsOk`). So `Ty`, the memories, the clocks and the interpreter's state are roll 11's, and
**`Program.interp_unique` holds with `E2` rows under its unchanged statement** (`LvmLoopInterp`; its proof has the
`e2` case).

* **`e2Pair_of_holds`** (statement 10): on a memory where every row relation holds, the two cells of a twin pair
  are the `E2` value `f(a)` of its operands.
* `inst_mem_insts`: the closed-form instance of an in-range `(b, jf, t)` is an instance of the program.
-/

namespace Lvm.Loop

/-! ## The twin check -/

theorem twin?_some {o o' : Op} (h : o.twin? = some o') : ∃ f, o = .e2 f false ∧ o' = .e2 f true := by
  unfold Op.twin? at h
  split at h
  · exact ⟨_, rfl, (Option.some.inj h).symm⟩
  · exact absurd h (by simp)

theorem twin?_e2 (f : E2Fn) : (Op.e2 f false).twin? = some (.e2 f true) := rfl

theorem default_op : (default : Row).op = .assert0 := rfl

/-- **The twin check at a first row**: an `e2 f false` row is followed by `e2 f true` with its operands and
result memory. -/
theorem twinsTpl_lo : ∀ (l : List Row), twinsTpl l = true → ∀ (t : Nat) (f : E2Fn),
    (l.getD t default).op = .e2 f false →
    t + 1 < l.length ∧ (l.getD (t + 1) default).op = .e2 f true ∧
      (l.getD (t + 1) default).args = (l.getD t default).args ∧
      (l.getD (t + 1) default).ty = (l.getD t default).ty
  | [], _, t, f, hop => by simp [default_op] at hop
  | [r], h, t, f, hop => by
    rcases t with _ | t
    · simp only [List.getD_cons_zero] at hop
      simp [twinsTpl, hop, twin?_e2] at h
    · simp [default_op] at hop
  | r :: r' :: rs, h, t, f, hop => by
    unfold twinsTpl at h
    rcases hr : r.op.twin? with _ | o
    · rw [hr] at h
      simp only [Bool.and_eq_true, Bool.not_eq_true'] at h
      rcases t with _ | t
      · simp only [List.getD_cons_zero] at hop
        rw [hop, twin?_e2] at hr; exact absurd hr (by simp)
      · obtain ⟨h1, h2, h3, h4⟩ := twinsTpl_lo (r' :: rs) h.2 t f (by simpa using hop)
        exact ⟨by simpa using h1, by simpa using h2, by simpa using h3, by simpa using h4⟩
    · rw [hr] at h
      simp only [Bool.and_eq_true, beq_iff_eq] at h
      obtain ⟨⟨⟨ho, ha⟩, hty⟩, hrs⟩ := h
      obtain ⟨g, hg, rfl⟩ := twin?_some hr
      rcases t with _ | _ | t
      · simp only [List.getD_cons_zero] at hop
        rw [hg] at hop; injection hop with hf; subst hf
        exact ⟨by simp, by simpa using ho, by simpa using ha, by simpa using hty⟩
      · simp only [List.getD_cons_succ, List.getD_cons_zero] at hop
        rw [ho] at hop; simp at hop
      · obtain ⟨h1, h2, h3, h4⟩ := twinsTpl_lo rs hrs t f (by simpa using hop)
        exact ⟨by simpa using h1, by simpa using h2, by simpa using h3, by simpa using h4⟩

/-- **The twin check at a second row**: an `e2 f true` row follows an `e2 f false` row. -/
theorem twinsTpl_hi : ∀ (l : List Row), twinsTpl l = true → ∀ (t : Nat) (f : E2Fn),
    (l.getD t default).op = .e2 f true → 0 < t ∧ (l.getD (t - 1) default).op = .e2 f false
  | [], _, t, f, hop => by simp [default_op] at hop
  | [r], h, t, f, hop => by
    rcases t with _ | t
    · simp only [List.getD_cons_zero] at hop
      simp [twinsTpl, hop, Op.isHi, Op.twin?] at h
    · simp [default_op] at hop
  | r :: r' :: rs, h, t, f, hop => by
    unfold twinsTpl at h
    rcases hr : r.op.twin? with _ | o
    · rw [hr] at h
      simp only [Bool.and_eq_true, Bool.not_eq_true'] at h
      rcases t with _ | t
      · simp only [List.getD_cons_zero] at hop
        simp [hop, Op.isHi] at h
      · obtain ⟨h1, h2⟩ := twinsTpl_hi (r' :: rs) h.2 t f (by simpa using hop)
        refine ⟨by omega, ?_⟩
        obtain ⟨t', rfl⟩ : ∃ t', t = t' + 1 := ⟨t - 1, by omega⟩
        simpa using h2
    · rw [hr] at h
      simp only [Bool.and_eq_true, beq_iff_eq] at h
      obtain ⟨⟨⟨ho, -⟩, -⟩, hrs⟩ := h
      obtain ⟨g, hg, rfl⟩ := twin?_some hr
      rcases t with _ | _ | t
      · simp only [List.getD_cons_zero] at hop
        rw [hg] at hop; simp at hop
      · simp only [List.getD_cons_succ, List.getD_cons_zero] at hop
        rw [ho] at hop; injection hop with hf; subst hf
        exact ⟨by omega, by simpa using hg⟩
      · obtain ⟨h1, h2⟩ := twinsTpl_hi rs hrs t f (by simpa using hop)
        refine ⟨by omega, ?_⟩
        obtain ⟨t', rfl⟩ : ∃ t', t = t' + 1 := ⟨t - 1, by omega⟩
        simpa using h2

namespace Program

variable (Q : Program)

/-- The twin check of the program at a block. -/
theorem twinsTpl_blk (htw : Q.twinsOk = true) {b : Nat} (hb : b < Q.blocks.length) : twinsTpl (Q.blk b).tpl = true := by
  simp only [twinsOk, List.all_eq_true] at htw
  apply htw
  simp only [blk, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hb, Option.getD_some]
  exact List.getElem_mem hb

/-- The closed-form instance of a block, loop index and template row in range is an instance of the program. -/
theorem inst_mem_insts {b jf t : Nat} (hb : b < Q.blocks.length) (hjf : jf < (Q.blk b).size)
    (ht : t < (Q.blk b).tpl.length) : Q.inst b jf t ∈ Q.insts :=
  (Q.mem_insts _).2 ⟨b, hb, jf, hjf, t, ht, rfl⟩

/-- **Statement 10: an `E2` value is two `K` cells.** With the program check and the twin check, on a memory where
every row relation holds, the twin pair at `(b, jf, t)` (`t` the first row) writes the cells `c`, `c + 1`
(`c` its `K` clock) holding the `E2` value of `f` at its operands. Owner **E2F-Q**. -/
theorem e2Pair_of_holds (hwf : Q.wf = true) (htw : Q.twinsOk = true) (M : Mem) (hH : Q.Holds M)
    {b jf t : Nat} (hb : b < Q.blocks.length) (hjf : jf < (Q.blk b).size) (ht : t < (Q.blk b).tpl.length)
    {f : E2Fn} (hop : ((Q.blk b).tpl.getD t default).op = .e2 f false) :
    (⟨M.k (Q.inst b jf t).ck, M.k ((Q.inst b jf t).ck + 1)⟩ : FE2) =
      f.val fun o => (M.arg (Q.inst b jf t) o).c₀ := by
  obtain ⟨h1, h2, h3, h4⟩ := twinsTpl_lo _ (Q.twinsTpl_blk htw hb) t f hop
  have hok := Q.instOk_of_mem hwf (Q.inst_mem_insts hb hjf ht)
  have hty : ((Q.blk b).tpl.getD t default).ty = .K := by
    have h := hok.typeOk
    change ((Q.blk b).tpl.getD t default).typeOk = true at h
    simp only [Row.typeOk, hop, Bool.and_eq_true, beq_iff_eq] at h
    exact h.2
  -- the twin's clock is the next `K` cell
  have hck : (Q.inst b jf (t + 1)).ck = (Q.inst b jf t).ck + 1 := by
    have hw : ((Q.blk b).tpl.getD t default).w .K = 1 := by
      unfold Row.w Row.writes; rw [hop]; simp only [hty, if_true]
    have hr : (Q.blk b).rank .K (t + 1) = (Q.blk b).rank .K t + ((Q.blk b).tpl.getD t default).w .K := by
      simp only [Block.rank, List.take_add_one, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem ht,
        Option.getD_some, Option.toList_some, List.map_append, List.sum_append, List.map_cons, List.map_nil,
        List.sum_cons, List.sum_nil, Nat.add_zero]
    simp only [Program.inst]
    rw [hr, hw]; omega
  have hargs : ∀ o, M.arg (Q.inst b jf (t + 1)) o = M.arg (Q.inst b jf t) o := by
    intro o
    simp only [Mem.arg, Inst.arg, Program.inst]
    rw [h3]
  have hd0 := hH _ (Q.inst_mem_insts hb hjf ht)
  have hd1 := hH _ (Q.inst_mem_insts hb hjf h1)
  change (match ((Q.blk b).tpl.getD t default).op with
    | _ => _) at hd0
  simp only [RowDef, Program.inst, hop] at hd0
  simp only [RowDef, Program.inst, h2] at hd1
  simp only [Mem.res, hty, h4, Inst.clock, Mem.rd] at hd0 hd1
  have e0 : M.k (Q.inst b jf t).ck = (f.val fun o => (M.arg (Q.inst b jf t) o).c₀).coord false :=
    congrArg FE.c₀ hd0
  have e1 : M.k (Q.inst b jf (t + 1)).ck = (f.val fun o => (M.arg (Q.inst b jf (t + 1)) o).c₀).coord true :=
    congrArg FE.c₀ hd1
  simp only [hargs, hck] at e1
  exact FE2.ext_coord (by rw [← e0]; rfl) (by rw [← e1]; rfl)

end Program

end Lvm.Loop
