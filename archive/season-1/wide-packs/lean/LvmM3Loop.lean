-- new for lvm (WP-9): the LoopIR tables (WP-10, `LvmLoopTable`) as tables of the lvm M3 instance
-- (`LvmM3Inst`), and the bus hypotheses of WP-10's `loopir_sound` (`LvmLoopSound.lean:348`) from
-- `M3Holds` through `mem_lookup` (`LvmBusIMem`).
import LvmLoopSound
import LvmM3LoopTab
import LvmM3Inst

-- (GOLF2: 38 declarations that `certified` does not use moved verbatim to `LvmMPCertOff`, outside its import closure.)

-- ===== merged from `LvmBusIMem` (GOLF module merge: `LvmBusIMem.lean` is now a stub importing `LvmM3Loop`) =====
section
-- new for lvm (WP-9): leanerVM's `lookup_sound` (adapted in `LvmBusILookup`) applied to the
-- `M3Holds` clauses `Balanced` and `CountsNonzero` of the lvm instance (`LvmM3Inst`), the way
-- leanerVM `Arithmetization/Bus.lean`@25da57d32 applies it to leanISA's memory channel.

/-!
# The memory bus: a balanced bus with nonzero counts reads only seeded keys

On the lvm instance (`Lvm.M3.inst`) every flush is a memory message (`Tab.flushes`): a read's pull
`⟨k, c⟩` and push `⟨k, g·c⟩`, a seed's push `⟨k, 1⟩` and finalize `⟨k, f⟩`. **`mem_lookup`**: if
the bus is balanced (`M3Instance.Balanced`, a permutation counted in `ℕ`), every read count is
nonzero (`M3Instance.CountsNonzero`, the read-count columns being the instance's count columns),
the count columns are inside their tables and there are fewer than `2^64 - 1` reads, then the key
(every coordinate but the count, `keyT`) of every read tuple is the key of a seed tuple.

This is leanerVM's `lookup_sound` with the messages the evaluated sixteen-coordinate tuples, the
reads the read pulls, the seeds the seed pushes and the finalizes the finalize pulls (whose keys
are their seeds' at the same row). The `M3Holds` tuples are rearranged into that shape:
`flushTuples .push` is, table by table, the bumped reads then the seeds (`push_perm`), and
`flushTuples .pull` the reads then the finalizes (`pull_perm`).
-/

namespace Lvm.M3

open LeanVM.Parameters LeanVM.Protocol LeanVM.Arithmetization CompPoly CMlPolynomialEval

/-! ## Tuples -/

/-- The key of a tuple: every coordinate but the count (coordinate `2`). -/
def keyT (t : Vector K 16) : Vector K 16 := Vector.ofFn fun k ↦ if k.val = 2 then 0 else t[k]

/-- The push of a read: the count multiplied by `g`. -/
def bumpT (t : Vector K 16) : Vector K 16 := Vector.ofFn fun k ↦ if k.val = 2 then g * t[k] else t[k]

/-- The count of a tuple. -/
def cntT (t : Vector K 16) : K := t[2]

theorem keyT_bumpT (t : Vector K 16) : keyT (bumpT t) = keyT t := by
  apply Vector.ext; intro k hk; simp only [keyT, bumpT, Vector.getElem_ofFn]; split <;> simp_all

theorem cntT_bumpT (t : Vector K 16) : cntT (bumpT t) = g * cntT t := by
  simp [cntT, bumpT]

/-- A tuple of polynomials evaluated at a row. -/
noncomputable def evalV {w : ℕ} (r : Fin w → K) (v : Vector (MvPolynomial (Fin w) K) 16) :
    Vector K 16 :=
  v.map (MvPolynomial.eval r)

namespace Tab

variable (t : Tab)

theorem evalV_bumpVec (r : Fin t.w → K) (rd : Key × ℕ) :
    evalV r (t.bumpVec rd) = bumpT (evalV r (t.readVec rd)) := by
  apply Vector.ext; intro k hk
  simp only [evalV, bumpT, Vector.getElem_map, Vector.getElem_ofFn]
  by_cases h2 : k = 2
  · subst h2
    simp [bumpVec, readVec, Key.vec, CPoly.eval_toMv, CPoly.evalB, CPoly.var, FK.toBF64_x]
  · simp [h2, bumpVec, readVec, Key.vec]

theorem keyT_finVec (r : Fin t.w → K) (s : Key × ℕ) :
    keyT (evalV r (t.finVec s)) = keyT (evalV r (t.seedVec s)) := by
  apply Vector.ext; intro k hk
  simp only [keyT, evalV, finVec, seedVec, Key.vec, Vector.getElem_ofFn, Vector.getElem_map]
  split <;> simp_all

theorem cntT_readVec (r : Fin t.w → K) (rd : Key × ℕ) :
    cntT (evalV r (t.readVec rd)) = CPoly.ext r rd.2 := by
  simp [cntT, evalV, readVec, Key.vec, CPoly.eval_toMv, CPoly.evalB, CPoly.var]

end Tab

/-! ## The tuples of the instance, table by table -/

section Tuples

variable (L : Lay) (tabs : List Tab) (hτ : ∀ t ∈ tabs, t.τ ≤ L.μ) (q : Column L.μ)

/-- The tuples of a list of flush vectors of table `j`, on every row. -/
noncomputable def partT (j : Fin tabs.length)
    (vs : List (Vector (MvPolynomial (Fin (tabs.get j).w) K) 16)) : List (Vector K 16) :=
  vs.flatMap fun v ↦ ((inst L tabs hτ).executed j).map fun x ↦ evalV ((inst L tabs hτ).row q j x) v

/-- Every read tuple (the reads' pulls). -/
noncomputable def readTuples : List (Vector K 16) :=
  (List.finRange tabs.length).flatMap fun j ↦
    partT L tabs hτ q j ((tabs.get j).reads.map (tabs.get j).readVec)

/-- Every seed tuple (the seeds' pushes). -/
noncomputable def seedTuples : List (Vector K 16) :=
  (List.finRange tabs.length).flatMap fun j ↦
    partT L tabs hτ q j ((tabs.get j).seeds.map (tabs.get j).seedVec)

/-- Every finalize tuple. -/
noncomputable def finTuples : List (Vector K 16) :=
  (List.finRange tabs.length).flatMap fun j ↦
    partT L tabs hτ q j ((tabs.get j).seeds.map (tabs.get j).finVec)

/-- The number of reads: `Σ_t |reads t| · 2^τ`. -/
def nReads (tabs : List Tab) : ℕ := (tabs.map fun t ↦ t.reads.length * 2 ^ t.τ).sum

theorem flatMap_append_perm {α β : Type} (l : List α) (A B : α → List β) :
    (l.flatMap fun a ↦ A a ++ B a).Perm (l.flatMap A ++ l.flatMap B) := by
  induction l with
  | nil => simp
  | cons a l ih =>
    simp only [List.flatMap_cons, List.append_assoc]
    refine List.Perm.append_left _ ?_
    exact (List.Perm.append_left _ ih).trans (List.perm_append_comm_assoc _ _ _)

theorem flushTuples_push :
    (inst L tabs hτ).flushTuples q .push = (List.finRange tabs.length).flatMap fun j ↦
      partT L tabs hτ q j ((tabs.get j).reads.map (tabs.get j).bumpVec) ++
        partT L tabs hτ q j ((tabs.get j).seeds.map (tabs.get j).seedVec) := by
  unfold M3Instance.flushTuples
  refine List.flatMap_congr fun j _ ↦ ?_
  show List.flatMap _ (List.filter _ (tabs.get j).flushes) = _
  simp only [Tab.flushes, List.filter_append, List.filter_map, Function.comp_def,
    reduceCtorEq, decide_false, decide_true, List.filter_false, List.filter_true, List.map_nil,
    List.nil_append, List.append_nil, List.flatMap_map, List.flatMap_append]
  simp only [partT, List.flatMap_map, evalV]

theorem flushTuples_pull :
    (inst L tabs hτ).flushTuples q .pull = (List.finRange tabs.length).flatMap fun j ↦
      partT L tabs hτ q j ((tabs.get j).reads.map (tabs.get j).readVec) ++
        partT L tabs hτ q j ((tabs.get j).seeds.map (tabs.get j).finVec) := by
  unfold M3Instance.flushTuples
  refine List.flatMap_congr fun j _ ↦ ?_
  show List.flatMap _ (List.filter _ (tabs.get j).flushes) = _
  simp only [Tab.flushes, List.filter_append, List.filter_map, Function.comp_def,
    reduceCtorEq, decide_false, decide_true, List.filter_false, List.filter_true, List.map_nil,
    List.nil_append, List.append_nil, List.flatMap_map, List.flatMap_append]
  simp only [partT, List.flatMap_map, evalV]

theorem partT_bump (j : Fin tabs.length) :
    partT L tabs hτ q j ((tabs.get j).reads.map (tabs.get j).bumpVec) =
      (partT L tabs hτ q j ((tabs.get j).reads.map (tabs.get j).readVec)).map bumpT := by
  simp only [partT, List.flatMap_map, List.map_flatMap, List.map_map]
  refine List.flatMap_congr fun r _ ↦ List.map_congr_left fun x _ ↦ ?_
  exact (tabs.get j).evalV_bumpVec _ r

theorem length_readTuples : (readTuples L tabs hτ q).length = nReads tabs := by
  have hex : ∀ j : Fin tabs.length, ((inst L tabs hτ).executed j).length = 2 ^ (tabs.get j).τ := by
    intro j
    rw [M3Instance.executed_eq]
    simp [inst]
  have h1 : ∀ j : Fin tabs.length, (partT L tabs hτ q j
      ((tabs.get j).reads.map (tabs.get j).readVec)).length =
      (tabs.get j).reads.length * 2 ^ (tabs.get j).τ := by
    intro j
    simp only [partT, List.length_flatMap, List.length_map, hex, List.map_map,
      Function.comp_def, List.map_const', List.sum_replicate, smul_eq_mul]
  simp only [readTuples, List.length_flatMap, h1, nReads]
  rw [← List.ofFn_eq_map]
  conv_rhs => rw [← List.ofFn_get tabs]
  rw [List.map_ofFn]
  rfl

end Tuples

/-! ## The lookup -/

/-- **The memory bus reads only seeded keys.** On the lvm instance, a balanced bus with nonzero
read counts (the clauses `Balanced`, `CountsNonzero` of `M3Holds`), count columns inside their
tables and fewer than `2^64 - 1` reads: every read tuple's key is a seed tuple's key. -/
theorem mem_lookup (L : Lay) (tabs : List Tab) (hτ : ∀ t ∈ tabs, t.τ ≤ L.μ) (q : Column L.μ)
    (hbal : (inst L tabs hτ).Balanced q) (hcnt : (inst L tabs hτ).CountsNonzero q)
    (hin : ∀ t ∈ tabs, ∀ r ∈ t.reads, r.2 < t.w) (hlen : nReads tabs < 2 ^ 64 - 1) :
    ∀ u ∈ readTuples L tabs hτ q, keyT u ∈ (seedTuples L tabs hτ q).map keyT := by
  have hperm : ((readTuples L tabs hτ q).map bumpT ++ seedTuples L tabs hτ q).Perm
      (readTuples L tabs hτ q ++ finTuples L tabs hτ q) := by
    have h := hbal
    unfold M3Instance.Balanced M3Instance.tuples M3Instance.boundaryTuples at h
    simp only [inst, List.filter_nil, List.flatMap_nil, List.append_nil] at h
    rw [flushTuples_push L tabs hτ q, flushTuples_pull L tabs hτ q] at h
    simp only [partT_bump] at h
    have e : (readTuples L tabs hτ q).map bumpT = (List.finRange tabs.length).flatMap fun j ↦
        (partT L tabs hτ q j ((tabs.get j).reads.map (tabs.get j).readVec)).map bumpT := by
      rw [readTuples, List.map_flatMap]
    rw [e]
    exact ((flatMap_append_perm _ _ _).symm.trans h).trans (flatMap_append_perm _ _ _)
  refine lookup_sound (key := keyT) (count := cntT) (bump := bumpT) keyT_bumpT cntT_bumpT
    (Good := fun k ↦ k ∈ (seedTuples L tabs hτ q).map keyT) hperm
    (fun m hm ↦ List.mem_map_of_mem hm) ?_ ?_ ?_
  · intro m hm
    simp only [finTuples, partT, List.mem_flatMap, List.mem_map] at hm
    obtain ⟨j, -, v, ⟨s, hs, rfl⟩, x, hx, rfl⟩ := hm
    rw [Tab.keyT_finVec]
    refine List.mem_map_of_mem ?_
    simp only [seedTuples, partT, List.mem_flatMap, List.mem_map]
    exact ⟨j, List.mem_finRange _, _, ⟨s, hs, rfl⟩, x, hx, rfl⟩
  · intro m hm
    simp only [readTuples, partT, List.mem_flatMap, List.mem_map] at hm
    obtain ⟨j, -, v, ⟨r, hr, rfl⟩, x, hx, rfl⟩ := hm
    rw [Tab.cntT_readVec]
    have hrw := hin _ (List.get_mem _ _) r hr
    simp only [CPoly.ext, hrw, dif_pos]
    have hmem : (⟨r.2, hrw⟩ : Fin (tabs.get j).w) ∈ (inst L tabs hτ).counts j := by
      simp only [inst, Tab.counts, List.mem_filterMap]
      exact ⟨r, hr, by simp only [dif_pos hrw]⟩
    have hxr : x.val < (inst L tabs hτ).rows j := by simp [inst]
    exact hcnt j _ hmem x hxr
  · rw [length_readTuples]; exact hlen

end Lvm.M3
end
-- ===== end of `LvmBusIMem` =====

/-!
# The LoopIR tables in the M3 instance, and the bus bridge to `loopir_sound`

**Tables.** `lvmTabs Q pl groups arrs aux` lists the tables of the lvm instance: one per LoopIR piece
(`pieceTab`, piece `n` is table `n`), one per input array (`InArr.tab`), then auxiliary tables
(`BITS`; they read, they seed nothing). A piece's columns are its shape's committed columns,
placed by `pl n`, then its fixed columns (derived: `Q.fval`); its constraints, reads and seed are
WP-10's (`Shape.constraints`, `readFlushes`, `seedFlush`/`finFlush`) with variables renamed to
column indices. An input array of type `τ` seeds, at row `x`, the input cell `base + stride·x`
of memory `τ` with its value columns (one or three limbs); its address column is fixed.

**The witness on the stack** (`witOf`, `inKOf`, `inEOf`): piece `n`'s committed value of a
variable at row `x` is its column's cell; input cell `e` is the value of the input array row that
seeds it (`0` if none does).

**The bridge** (`loop_bus`): `M3Holds` of the instance (its `Balanced` and `CountsNonzero`
clauses), the input arrays' layout facts (`InOk`), count columns inside the widths and fewer than
`2^64 - 1` reads give WP-10's `hbus` verbatim; `loop_ginj` gives its `hinj` when the program has at
most `2^64 - 1` cells of each memory; `inKOf_size`/`inEOf_size` its `hsz`.
-/

namespace Lvm.M3

open LeanVM.Parameters LeanVM.Protocol CompPoly CMlPolynomialEval
open Lvm.Loop

/-! ## Facts the instance needs -/

section Bridge

variable (Q : Program) (pl : ℕ → Var → Bool × ℕ) (groups : List Grp) (arrs : List InArr) (aux : List Tab) (L : Lay)
  (hτ : ∀ t ∈ lvmTabs Q pl groups arrs aux, t.τ ≤ L.μ)

/-- **The lvm M3 instance.** -/
noncomputable abbrev lvmInst : M3Instance := inst L (lvmTabs Q pl groups arrs aux) hτ

/-- Where piece `n` sits: its group and row offset (the first member naming it). -/
def loc (groups : List Grp) (n : ℕ) : Option (ℕ × ℕ) :=
  (List.range groups.length).findSome? fun i ↦
    ((groups.getD i default).mem.find? fun m ↦ m.1 == n).map fun m ↦ (i, m.2)

/-- **The LoopIR witness on the stack**: piece `n`'s committed variable `u` at row `x` is its
column's cell in its group's table, at the piece's offset (`0` past the tables). -/
noncomputable def witOf (q : Column L.μ) : Witness := fun n x u ↦
  match loc groups n with
  | some (i, off) =>
    if h : i < (lvmTabs Q pl groups arrs aux).length then
      if hx : off + x < 2 ^ ((lvmTabs Q pl groups arrs aux).get ⟨i, h⟩).τ then
        if hi : vidx (Q.pieces.getD n default).shape u < ((lvmTabs Q pl groups arrs aux).get ⟨i, h⟩).w then
          FK.ofBF64 ((lvmInst Q pl groups arrs aux L hτ).row q ⟨i, h⟩ ⟨off + x, hx⟩ ⟨_, hi⟩)
        else 0
      else 0
    else 0
  | none => 0

end Bridge

/-! ## `g`-power injectivity -/

/-! ## Messages as tuples -/

theorem keyT_coord {t t' : Vector K 16} (h : keyT t = keyT t') (k : ℕ) (hk : k < 16) (hk2 : k ≠ 2) :
    t[k] = t'[k] := by
  have := congrArg (·[k]) h
  simpa [keyT, hk2] using this

/-! ## Fixed variables of the flushes are columns -/

/-- The fixed variables of a polynomial are among the shape's columns. -/
def FixIn (σ : Loop.Shape) (P : Poly2) : Prop :=
  ∀ m ∈ P, ∀ y ∈ m.vars, ∀ c, y = .fix c → y ∈ shapeVars σ

theorem fixIn_var_nonfix (σ : Loop.Shape) (u : Var) (hu : ∀ c, u ≠ .fix c) : FixIn σ (Poly2.var u) := by
  intro m hm y hy c hc
  simp [Poly2.var] at hm; subst hm; simp at hy; subst hy; exact absurd hc (hu c)

theorem fixIn_var_fix (σ : Loop.Shape) (c : FCol) (hc : c ∈ σ.fcols) : FixIn σ (Poly2.var (.fix c)) := by
  intro m hm y hy c' _
  simp [Poly2.var] at hm; subst hm; simp at hy; subst hy
  exact List.mem_append_right _ (List.mem_map_of_mem hc)

section Bridge2

variable (Q : Program) (pl : ℕ → Var → Bool × ℕ) (groups : List Grp) (arrs : List InArr) (aux : List Tab) (L : Lay)
  (hτ : ∀ t ∈ lvmTabs Q pl groups arrs aux, t.τ ≤ L.μ)

/-- The groups' facts: members are pieces of the group's shape inside its rows, members are
disjoint and cover the rows, every piece is in exactly one group, at one offset. -/
structure GrpOk (Q : Program) (groups : List Grp) : Prop where
  /-- A member is a piece of the group's shape, inside the group's rows. -/
  mem : ∀ g ∈ groups, ∀ m ∈ g.mem, ∃ p, Q.pieces[m.1]? = some p ∧ p.shape = g.σ ∧
    m.2 + 2 ^ Q.height p ≤ 2 ^ g.τ ∧ 2 ^ Q.height p ∣ m.2
  /-- One member holds a row. -/
  disj : ∀ g ∈ groups, ∀ m ∈ g.mem, ∀ m' ∈ g.mem, ∀ y, Grp.Holds Q m y = true →
    Grp.Holds Q m' y = true → m = m'
  /-- Every row of a group is a member's. -/
  cover : ∀ g ∈ groups, ∀ y < 2 ^ g.τ, ∃ m ∈ g.mem, Grp.Holds Q m y = true
  /-- Every piece is a member. -/
  all : ∀ n < Q.pieces.length, ∃ i, ∃ h : i < groups.length, ∃ off, (n, off) ∈ groups[i].mem
  /-- At one place. -/
  uniq : ∀ i i' (h : i < groups.length) (h' : i' < groups.length) n off off',
    (n, off) ∈ groups[i].mem → (n, off') ∈ groups[i'].mem → i = i' ∧ off = off'
  /-- No member is listed twice (a group's fixed columns sum over its members). -/
  nodup : ∀ g ∈ groups, g.mem.Nodup

theorem evalB_var (u : ℕ → K) (i : ℕ) : CPoly.evalB u (CPoly.var i) = u i := by
  simp [CPoly.evalB, CPoly.var]

/-! ## The constraints: `loopir_sound`'s `hcons` -/

theorem fixIn_append {σ : Loop.Shape} {P R : Poly2} (hP : FixIn σ P) (hR : FixIn σ R) :
    FixIn σ (P ++ R) := fun m hm ↦ by
  rcases List.mem_append.mp hm with h | h
  · exact hP m h
  · exact hR m h

theorem fixIn_nil (σ : Loop.Shape) : FixIn σ [] := fun m hm ↦ by simp at hm

theorem fixIn_prod (σ : Loop.Shape) (la lb l : ℕ) :
    FixIn σ (prodPoly (Var.arg 0) (Var.arg 1) la lb l) := by
  intro m hm y hy c hc
  simp only [prodPoly, List.mem_map] at hm
  obtain ⟨_, -, rfl⟩ := hm
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hy
  rcases hy with rfl | rfl <;> cases hc

theorem fixIn_limb (σ : Loop.Shape) (o n l : ℕ) : FixIn σ (limbPoly (Var.arg o) n l) := by
  unfold limbPoly; split
  · exact fixIn_var_nonfix σ _ (fun c h ↦ by cases h)
  · exact fixIn_nil σ

theorem fixIn_limbFix (σ : Loop.Shape) (c : FCol) (hc : c ∈ σ.fcols) (o n l : ℕ) :
    FixIn σ (limbFix c (Var.arg o) n l) := by
  unfold limbFix; split
  · intro m hm y hy c' hc'
    simp only [List.mem_singleton] at hm; subst hm
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hy
    rcases hy with rfl | rfl
    · exact List.mem_append_right _ (List.mem_map_of_mem hc)
    · cases hc'
  · exact fixIn_nil σ

/-- The fixed variables of WP-10's constraints are columns of the shape's table. -/
theorem constraints_fixIn (σ : Loop.Shape) : ∀ C ∈ σ.constraints, FixIn σ C := by
  intro C hC
  have nf : ∀ l, FixIn σ (Poly2.var (.res l)) := fun l ↦ fixIn_var_nonfix σ _ (fun c h ↦ by cases h)
  unfold Loop.Shape.constraints at hC
  split at hC <;> rename_i hk <;> simp only [List.mem_map, List.mem_range, List.mem_singleton] at hC <;>
    (try obtain ⟨l, -, rfl⟩ := hC) <;> (try subst hC)
  · exact fixIn_append (fixIn_append (nf l) (fixIn_prod _ _ _ _)) (fixIn_limb _ _ _ _)
  · have hk' : ∀ c ∈ [FCol.k, FCol.k'], c ∈ σ.fcols := fun c hc ↦ by
      simp only [Loop.Shape.fcols, hk, if_true, List.mem_append]
      exact Or.inl (Or.inr hc)
    refine fixIn_append (fixIn_append (fixIn_append (nf l) (fixIn_limb _ _ _ _))
      (fixIn_limbFix σ .k (hk' _ (by simp)) _ _ _)) ?_
    split
    · exact fixIn_var_fix σ .k' (hk' _ (by simp))
    · exact fixIn_nil σ
  · exact fixIn_prod _ _ _ _
  · exact fixIn_append (nf l) (fixIn_var_nonfix σ _ (fun c h ↦ by cases h))
  · have hF : FCol.F ∈ σ.fcols := by simp [Loop.Shape.fcols, hk]
    exact fixIn_append (fixIn_append (nf l) (fixIn_limbFix σ .F hF _ _ _)) (fixIn_limb _ _ _ _)
  -- the `E2` rows (lvm2 E2F): fixed variables `k`, `k'` of `e2lin` only
  all_goals simp [FixIn, Poly2.var, shapeVars, Loop.Shape.fcols, hk]

end Bridge2

/-! ## Non-vacuity -/

end Lvm.M3
