-- New for lvm2 E2F (slice S1, E2F-Q; E2AC-DES §1.2, §6 statement 11): the typed backend's circuit theorem with
-- `E2` twin rows. Frozen on day 0; proofs E2F-Q's.
import LvmWiringX
import LvmTyped
import LvmE2QFieldCorrect
import LvmLoopInterp

-- ===== merged from `LvmLoopE2` (VQ module merge: `LvmLoopE2.lean` removed) =====
section
-- New for lvm2 E2F (slice S1, E2F-Q; E2AC-DES §6 statement 10, "`Ty.E2` in LoopIR", renamed "the `E2` rows in
-- LoopIR" with E2F-LEAD's approval of the twin-row design, 2026-11-13).

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
end
-- ===== end of `LvmLoopE2` =====

/-!
# The circuit theorem with `E2` rows (`holds_of_wiringX`)

`LvmTyped.holds_of_wiring` (roll 8) reads one relation in `E` per slot; with `E2` twin rows (`LvmLoopIR`) a slot
of a twin's first row carries both coordinates of the `E2` relation (`LvmWiringX.WiringRelX`).

* **`twin_of_wiringX`**: from the one slot of a twin pair's first row, **both** rows' relations (the two
  coordinates of the `E2` value; E2F-LEAD's condition 2). The twin check `Program.twinsOk` (decided, static; the
  layout check makes the first row a constraint row and the second none, `Row.isCon`) is the only structural fact
  it consumes besides the program and layout checks.
* **`holds_of_wiringX`** (statement 11): the coordinate-split relation at every slot and the mini-bus obligation
  give every row relation and every gated assertion on the memory read off the words.
* **`typed_soundX`**: then `Program.interp_unique` (unchanged statement): the memory is the interpreter's.
-/

set_option autoImplicit false

namespace Lvm.Typed

open Lvm.Loop

/-! ## The entries at a slot -/

theorem lhx_ofK_add (a b : FK) : FE.ofK (a + b) = FE.ofK a + FE.ofK b := FE.ofKRingHom.map_add a b
theorem lhx_ofK_mul (a b : FK) : FE.ofK (a * b) = FE.ofK a * FE.ofK b := FE.ofKRingHom.map_mul a b

/-- An instance's coordinate-split entries lie at its slot, and it is a constraint row. -/
theorem lhx_instEntsX_slot (Q : Program) (lay : Lay) (i : Inst) {e : Ent} (he : e ∈ instEntsX Q lay i) :
    e.x = lay.slot i.blk i.t i.jf ∧ Row.isCon i.row = true := by
  simp only [instEntsX] at he
  split at he
  · rename_i hop
    refine ⟨?_, by simp only [Row.isCon, hop]⟩
    simp only [List.mem_append] at he
    rcases he with ((((((he | he) | he) | he) | he) | he) | he) | he <;> exact (lh_mem_tagE he).2.1
  · rename_i hop
    refine ⟨?_, by simp only [Row.isCon, hop]⟩
    simp only [List.mem_append] at he
    rcases he with ((he | he) | he) | he <;> exact (lh_mem_tagE he).2.1
  · exact absurd he List.not_mem_nil
  · exact ⟨(lh_instEnts_mem Q lay i he).2.1, lh_instEnts_con Q lay i he⟩

/-- **At a constraint slot only its instance has entries** (`lh_ents_at` for the eight matrices). -/
theorem lhx_ents_at {Q : Program} {lay : Lay} (hlay : lay.Ok Q) {b t jf : ℕ}
    (hb : b < Q.blocks.length) (ht : t < (Q.blk b).tpl.length) (hjf : jf < 2 ^ (Q.blk b).lsize)
    (hc : Row.isCon ((Q.blk b).tpl.getD t default) = true) (o : ℕ) :
    (entsX Q lay).filter (fun e ↦ e.o == o && e.x == lay.slot b t jf) =
      (instEntsX Q lay (Q.inst b jf t)).filter (·.o == o) := by
  have hother : ∀ b' < Q.blocks.length, ∀ jf' < 2 ^ (Q.blk b').lsize, ∀ t' < (Q.blk b').tpl.length,
      ¬ (b' = b ∧ jf' = jf ∧ t' = t) →
        (instEntsX Q lay (Q.inst b' jf' t')).filter (fun e ↦ e.o == o && e.x == lay.slot b t jf) = [] := by
    intro b' hb' jf' hjf' t' ht' hne
    rw [List.filter_eq_nil_iff]
    intro e he hp
    obtain ⟨h2, hcon⟩ := lhx_instEntsX_slot Q lay _ he
    simp only [Bool.and_eq_true, beq_iff_eq] at hp
    have := lh_slot_inj hlay hb' ht' hjf' hcon hb ht hjf hc (h2.symm.trans hp.2)
    exact hne ⟨this.1, this.2.2, this.2.1⟩
  have haux : (auxEnts lay).filter (fun e ↦ e.o == o && e.x == lay.slot b t jf) = [] := by
    rw [List.filter_eq_nil_iff]
    intro e he hp
    simp only [Bool.and_eq_true, beq_iff_eq] at hp
    exact lh_aux_ne_slot hlay hb ht hjf hc e he hp.2
  rw [entsX, List.filter_append, haux, List.append_nil, List.filter_flatMap, phi_insts, List.flatMap_assoc]
  rw [lh_flatMap_single _ b _ hb ?_]
  · rw [List.flatMap_assoc, lh_flatMap_single _ jf _ hjf ?_]
    · rw [List.flatMap_map, lh_flatMap_single _ t _ ht ?_]
      · refine List.filter_congr fun e he ↦ ?_
        have h2 : e.x = lay.slot b t jf := (lhx_instEntsX_slot Q lay _ he).1
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

theorem lhx_matZX_eq (Q : Program) (lay : Lay) (o : ℕ) (z : ℕ → FK) (x : ℕ) :
    matZX Q lay o z x = lh_val z ((entsX Q lay).filter fun e ↦ e.o == o && e.x == x) :=
  phi_foldr_eq_sum (fun e : Ent ↦ e.c * FE.ofK (z e.y)) _

/-- The value of matrix `o` of an instance's entries. -/
abbrev lvX (Q : Program) (lay : Lay) (z : ℕ → FK) (i : Inst) (o : ℕ) : FE :=
  lh_val z ((instEntsX Q lay i).filter (·.o == o))

/-- **The relation at a constraint row's slot**, on its own entries. -/
theorem lhx_slot (Q : Program) (lay : Lay) (z : ℕ → FK) (hlay : lay.Ok Q) (h : WiringRelX Q lay z) {b t jf : ℕ}
    (hb : b < Q.blocks.length) (ht : t < (Q.blk b).tpl.length) (hjf : jf < 2 ^ (Q.blk b).lsize)
    (hc : Row.isCon ((Q.blk b).tpl.getD t default) = true) :
    let i := Q.inst b jf t
    lvX Q lay z i 0 * lvX Q lay z i 1 + lvX Q lay z i 4 * lvX Q lay z i 5 + lvX Q lay z i 2 + lvX Q lay z i 3 = 0 ∧
      lvX Q lay z i 0 * lvX Q lay z i 5 + lvX Q lay z i 4 * lvX Q lay z i 1 +
        FE.ofK FK.x * (lvX Q lay z i 4 * lvX Q lay z i 5) + lvX Q lay z i 6 + lvX Q lay z i 7 = 0 := by
  have := h (lay.slot b t jf)
  simp only [relX0, relX1, lhx_matZX_eq, lhx_ents_at hlay hb ht hjf hc] at this
  exact this

/-- Roll 8's entries have matrices below `4`. -/
theorem lhx_val_hi (Q : Program) (lay : Lay) (z : ℕ → FK) (i : Inst) {o : ℕ} (ho : 4 ≤ o) :
    lh_val z ((instEnts Q lay i).filter (·.o == o)) = 0 := by
  rw [List.filter_eq_nil_iff.mpr fun e he hp ↦ by
    have := (lh_instEnts_mem Q lay i he).1
    simp only [beq_iff_eq] at hp; (clear * - o ho e this hp; omega)]
  rfl

/-- **Both rows of an `E2` twin pair hold from its one slot.** With the program and twin checks, on a checked
layout, with `z(one) = 1` and the coordinate-split relation, the first row `t` (`e2 f false`) and its twin `t + 1`
have their relations on the memory read off `z`. Owner **E2F-Q**. -/
theorem twin_of_wiringX (Q : Program) (lay : Lay) (z : ℕ → FK) (hwf : Q.wf = true) (htw : Q.twinsOk = true)
    (hlay : lay.Ok Q) (hone : z lay.one = 1) (h : WiringRelX Q lay z) {b jf t : ℕ} (hb : b < Q.blocks.length)
    (hjf : jf < (Q.blk b).size) (ht : t < (Q.blk b).tpl.length) {f : E2Fn}
    (hop : ((Q.blk b).tpl.getD t default).op = .e2 f false) :
    Q.RowDef (memOf lay z) (Q.inst b jf t) ∧ Q.RowDef (memOf lay z) (Q.inst b jf (t + 1)) := by
  obtain ⟨h1, h2, h3, h4⟩ := twinsTpl_lo _ (Q.twinsTpl_blk htw hb) t f hop
  have htyOk := lh_wf_typeOk hwf hb ht
  simp only [Row.typeOk, hop, Bool.and_eq_true, beq_iff_eq, List.length_map] at htyOk
  obtain ⟨⟨hlen, hallK⟩, hty⟩ := htyOk
  set M := memOf lay z with hM
  set i := Q.inst b jf t with hi
  have hopi : i.row.op = .e2 f false := hop
  -- the operands are `K` cells
  have hA : ∀ o < f.arity, FE.ofK (M.arg i o).c₀ = M.arg i o := by
    intro o ho
    have hmem : (i.row.args.getD o default) ∈ i.row.args := by
      simp only [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (show o < i.row.args.length by
        change o < ((Q.blk b).tpl.getD t default).args.length; (clear * - o Q b t jf f hlen ho; omega)), Option.getD_some]
      exact List.getElem_mem _
    have hK : (i.row.args.getD o default).ty = .K :=
      beq_iff_eq.mp (List.all_eq_true.mp hallK _ (List.mem_map_of_mem (f := fun a : Addr ↦ a.ty) hmem))
    simp only [Mem.arg, Inst.arg, hK]; rfl
  -- the twin reads the same operands and writes the next `K` cell
  have hargs : ∀ o, M.arg (Q.inst b jf (t + 1)) o = M.arg i o := by
    intro o; simp only [hi, Mem.arg, Inst.arg, Program.inst]; rw [h3]
  have hck : (Q.inst b jf (t + 1)).ck = i.ck + 1 := by
    have hw : ((Q.blk b).tpl.getD t default).w .K = 1 := by
      unfold Row.w Row.writes; rw [hop]; simp only [hty, if_true]
    have hr : (Q.blk b).rank .K (t + 1) = (Q.blk b).rank .K t + ((Q.blk b).tpl.getD t default).w .K := by
      simp only [Block.rank, List.take_add_one, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem ht,
        Option.getD_some, Option.toList_some, List.map_append, List.sum_append, List.map_cons, List.map_nil,
        List.sum_cons, List.sum_nil, Nat.add_zero]
    simp only [hi, Program.inst]
    rw [hr, hw]; (clear * - Q b jf t f; omega)
  have hres0 : M.res i = M.rd .K i.ck := by simp only [Mem.res]; rw [show i.row.ty = .K from hty]; rfl
  have hres1 : M.res (Q.inst b jf (t + 1)) = M.rd .K (i.ck + 1) := by
    simp only [Mem.res]; rw [show (Q.inst b jf (t + 1)).row.ty = .K from h4.trans hty, Inst.clock_K, hck]
  have hc : Row.isCon ((Q.blk b).tpl.getD t default) = true := by simp only [Row.isCon, hop]
  obtain ⟨R0, R1⟩ := lhx_slot Q lay z hlay h hb ht hjf hc
  simp only [lvX] at R0 R1
  rw [← hi] at R0 R1
  have hd0 : Q.RowDef M i ↔ M.res i = FE.ofK ((f.val fun o ↦ (M.arg i o).c₀).coord false) := by
    simp only [Program.RowDef, hopi]
  have hd1 : Q.RowDef M (Q.inst b jf (t + 1)) ↔
      M.res (Q.inst b jf (t + 1)) = FE.ofK ((f.val fun o ↦ (M.arg i o).c₀).coord true) := by
    have hop1 : (Q.inst b jf (t + 1)).row.op = .e2 f true := h2
    simp only [Program.RowDef, hop1, hargs]
  rw [hd0, hd1, hres1]
  cases f with
  | mul =>
    simp only [instEntsX, hopi, lh_val_append, lh_val_tagE, Nat.reduceEqDiff, ↓reduceIte, add_zero, zero_add,
      lh_argSum hone, lh_resSum hone, lh_cellSum hone, one_mul] at R0 R1
    simp only [E2Fn.arity] at hA
    simp only [E2Fn.val, E2Fn.opd, FE2.mul_def, FE2.add_def, FE2.coord_false, FE2.coord_true, Nat.mul_zero,
      Nat.zero_add, Nat.mul_one, Nat.reduceMul, Nat.reduceAdd, lhx_ofK_add, lhx_ofK_mul,
      hA 0 (by (clear * - Q b jf t; omega)), hA 1 (by (clear * - Q b jf t; omega)), hA 2 (by (clear * - Q b jf t; omega)), hA 3 (by (clear * - Q b jf t; omega)), hA 4 (by (clear * - Q b jf t; omega)), hA 5 (by (clear * - Q b jf t; omega))]
    exact ⟨lh_c2 R0, lh_c2 R1⟩
  | lin k k₀ k₁ =>
    simp only [instEntsX, hopi, lh_val_append, lh_val_tagE, Nat.reduceEqDiff, ↓reduceIte, add_zero, zero_add,
      lh_psum_append, lh_argSum hone, lh_resSum hone, lh_cellSum hone, lh_psum_one hone, one_mul, mul_zero,
      zero_mul] at R0 R1
    simp only [E2Fn.arity] at hA
    simp only [E2Fn.val, E2Fn.opd, FE2.mul_def, FE2.add_def, FE2.ofK, FE2.coord_false, FE2.coord_true,
      Nat.mul_zero, Nat.zero_add, Nat.mul_one, Nat.reduceMul, Nat.reduceAdd, zero_mul, mul_zero, add_zero,
      lhx_ofK_add, lhx_ofK_mul, hA 0 (by (clear * - Q b jf t k k₀ k₁; omega)), hA 1 (by (clear * - Q b jf t k k₀ k₁; omega)), hA 2 (by (clear * - Q b jf t k k₀ k₁; omega)), hA 3 (by (clear * - Q b jf t k k₀ k₁; omega))]
    exact ⟨lh_c2 R0, lh_c2 R1⟩

/-- **One instance's relation and gated assertion from the coordinate-split wiring relation** (its `readd` case from
`hrd`; `holds_of_wiringX`'s step, also giving the non-`readd` rows without `ReaddOk`). -/
theorem rowDef_of_wiringX (Q : Program) (lay : Lay) (z : ℕ → FK) (hwf : Q.wf = true) (htw : Q.twinsOk = true)
    (hlay : lay.Ok Q) (hone : z lay.one = 1) (h : WiringRelX Q lay z) {i : Inst} (hi : i ∈ Q.insts)
    (hrd : ∀ lo m, i.row.op = .readd lo m → Q.RowDef (memOf lay z) i) :
    Q.RowDef (memOf lay z) i ∧ Program.RowAssert (memOf lay z) i := by
  obtain ⟨b, hb, jf, hjf, t, ht, rfl⟩ := lh_mem_insts hi
  by_cases he : ∃ f hh, (Q.inst b jf t).row.op = .e2 f hh
  · obtain ⟨f, hh, hop⟩ := he
    refine ⟨?_, by simp only [Program.RowAssert, hop]⟩
    cases hh
    · exact (twin_of_wiringX Q lay z hwf htw hlay hone h hb hjf ht hop).1
    · obtain ⟨hpos, hprev⟩ := twinsTpl_hi _ (Q.twinsTpl_blk htw hb) t f hop
      have := (twin_of_wiringX Q lay z hwf htw hlay hone h hb hjf (t := t - 1) (by (clear * - t Q b jf ht hpos; omega)) hprev).2
      rwa [Nat.sub_add_cancel hpos] at this
  · have he2 : ∀ f hh, (Q.inst b jf t).row.op ≠ .e2 f hh := fun f hh h' ↦ he ⟨f, hh, h'⟩
    refine lh_row_at Q lay z hwf hlay hone hb hjf ht hi (fun hc ↦ ?_) (fun lo m hop ↦ hrd lo m hop) he2
    obtain ⟨R0, -⟩ := lhx_slot Q lay z hlay h hb ht hjf hc
    simp only [lvX, lhx_instEntsX_ne' Q lay _ he2, lhx_val_hi Q lay z _ (le_refl 4),
      lhx_val_hi Q lay z _ (show 4 ≤ 5 by (clear * - Q b jf t; omega)), mul_zero, add_zero] at R0
    exact R0

/-- **Statement 11: the coordinate-split wiring relation is the program's relations** (E2AC-DES §1.2, §6): with
the program and twin checks, on a checked layout, with `z(one) = 1`, the coordinate-split relation at every slot
and the mini-bus obligation, every row relation and every gated assertion holds on the memory read off `z`.
Owner **E2F-Q**. -/
theorem holds_of_wiringX (Q : Program) (lay : Lay) (z : ℕ → FK) (hwf : Q.wf = true) (htw : Q.twinsOk = true)
    (hlay : lay.Ok Q) (hone : z lay.one = 1) (h : WiringRelX Q lay z) (hrd : ReaddOk Q (memOf lay z)) :
    Q.Holds (memOf lay z) ∧ Q.Asserts (memOf lay z) :=
  ⟨fun i hi ↦ (rowDef_of_wiringX Q lay z hwf htw hlay hone h hi (hrd _ hi)).1,
    fun i hi ↦ (rowDef_of_wiringX Q lay z hwf htw hlay hone h hi (hrd _ hi)).2⟩

/-- **The typed backend's circuit theorem with `E2` rows**: `holds_of_wiringX`, then `Program.interp_unique`. -/
theorem typed_soundX (Q : Program) (lay : Lay) (z : ℕ → FK) (hwf : Q.wf = true) (htw : Q.twinsOk = true)
    (inK : Array FK) (inE : Array FE) (hsz : inK.size = Q.nInK ∧ inE.size = Q.nInE) (hlay : lay.Ok Q)
    (hone : z lay.one = 1) (h : WiringRelX Q lay z) (hrd : ReaddOk Q (memOf lay z))
    (hin : Q.Inputs (memOf lay z) inK inE) (hinj : GInj (max (Q.cells .K) (Q.cells .E)))
    (hinb : (Q.interp inK inE).inb = true) :
    (memOf lay z).Agrees (Q.interpMem inK inE) (Q.cells .K) (Q.cells .E) ∧
      (Q.interp inK inE).ok = true := by
  obtain ⟨hH, hA⟩ := holds_of_wiringX Q lay z hwf htw hlay hone h hrd
  obtain ⟨hag, hiff⟩ := Q.interp_unique hwf inK inE hsz _ hin hH hinj hinb
  exact ⟨hag, hiff.mpr hA⟩

end Lvm.Typed
