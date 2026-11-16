/- `LvmMPCertOff` (GOLF2 off-path move, group 6 of 48): declarations that the certificate `certified`
   does not use, moved here verbatim (same names, same namespaces and context) from LvmM3Loop, LvmVEqFit, LvmCertSMid3, LvmCertSJ, LvmCertSExtJSplit, LvmCertSExtJ, LvmMPCert,
   so that `Solution`'s import closure need not elaborate them. Import this module where they are needed;
   the name -> module map is GOLF2's moved.tsv. -/
import LvmM3Loop
import LvmVEqFit
import LvmCertSMid3
import LvmCertSJ
import LvmCertSExtJSplit
import LvmCertSExtJ
import LvmMPCert
import LvmE2QPinOpenFOff
import LvmM3MidCertOff
import LvmVEqWireOff
import LvmChainTablePad
import LvmJBMutual
import LvmMlListLemmas
import LvmSpecRulesCert

-- ===== from `LvmM3Loop` =====

section
section
namespace Lvm.M3
open LeanVM.Parameters LeanVM.Protocol LeanVM.Arithmetization CompPoly CMlPolynomialEval
section Tuples
variable (L : Lay) (tabs : List Tab) (hτ : ∀ t ∈ tabs, t.τ ≤ L.μ) (q : Column L.μ)

theorem partT_append (j : Fin tabs.length)
    (u v : List (Vector (MvPolynomial (Fin (tabs.get j).w) K) 16)) :
    partT L tabs hτ q j (u ++ v) = partT L tabs hτ q j u ++ partT L tabs hτ q j v := by
  unfold partT; exact List.flatMap_append

end Tuples
end Lvm.M3
end
end

section
namespace Lvm.M3
open LeanVM.Parameters LeanVM.Protocol CompPoly CMlPolynomialEval
open Lvm.Loop

theorem toBF64_prodK (l : List FK) : FK.toBF64 (prodK l) = (l.map FK.toBF64).prod := by
  induction l with
  | nil => simp [prodK]
  | cons a l ih => simp [prodK, ih]

/-- Evaluating the renamed polynomial at a row is evaluating the LoopIR polynomial at the
variables' values, when the row holds them. -/
theorem evalB_ofPoly2 (u : ℕ → K) (v : Var → FK) (idx : Var → ℕ) (P : Poly2)
    (h : ∀ m ∈ P, ∀ y ∈ m.vars, u (idx y) = FK.toBF64 (v y)) :
    CPoly.evalB u (ofPoly2 idx P) = FK.toBF64 (P.ev v) := by
  induction P with
  | nil => simp [ofPoly2, CPoly.evalB, Poly2.ev]
  | cons m P ih =>
    have ih' := ih fun m' hm' ↦ h m' (List.mem_cons_of_mem _ hm')
    simp only [ofPoly2, CPoly.evalB, List.map_cons, List.sum_cons] at ih' ⊢
    simp only [Poly2.ev, List.foldr_cons] at ih' ⊢
    rw [ih', FK.toBF64_add, FK.toBF64_mul, toBF64_prodK, List.map_map, List.map_map]
    congr 2
    exact congrArg List.prod (List.map_congr_left (f := u ∘ idx) (g := FK.toBF64 ∘ v)
      fun y hy ↦ h m (List.mem_cons_self ..) y hy)

/-- The input arrays' facts: limb counts, cells below the input counts, one seed per cell, every
input cell seeded. -/
structure InOk (Q : Program) (arrs : List InArr) : Prop where
  /-- One value column per limb. -/
  limbs : ∀ a ∈ arrs, a.val.length = a.ty.limbs
  /-- The seeded cells are input cells. -/
  lt : ∀ a ∈ arrs, ∀ x < 2 ^ a.τ, a.base + a.stride * x < Q.nIn a.ty
  /-- No cell is seeded twice. -/
  inj : ∀ (i i' : Fin arrs.length) (x x' : ℕ), x < 2 ^ (arrs.get i).τ → x' < 2 ^ (arrs.get i').τ →
    (arrs.get i).ty = (arrs.get i').ty →
    (arrs.get i).base + (arrs.get i).stride * x = (arrs.get i').base + (arrs.get i').stride * x' →
    i = i' ∧ x = x'
  /-- Every input cell is seeded (the inputs cover `[0, nIn τ)`; replay reads every input). -/
  cover : ∀ τ : Loop.Ty, ∀ e < Q.nIn τ, ∃ a ∈ arrs, a.ty = τ ∧ ∃ x < 2 ^ a.τ, a.base + a.stride * x = e

end Lvm.M3
end

section
namespace Lvm.M3
open LeanVM.Parameters LeanVM.Protocol CompPoly CMlPolynomialEval
open Lvm.Loop
section Bridge
variable (Q : Program) (pl : ℕ → Var → Bool × ℕ) (groups : List Grp) (arrs : List InArr) (aux : List Tab) (L : Lay)
  (hτ : ∀ t ∈ lvmTabs Q pl groups arrs aux, t.τ ≤ L.μ)

theorem lvmTabs_length :
    (lvmTabs Q pl groups arrs aux).length = groups.length + arrs.length + aux.length := by
  simp [lvmTabs]; omega

theorem get_grp {i : ℕ} (hi : i < groups.length) (h : i < (lvmTabs Q pl groups arrs aux).length) :
    (lvmTabs Q pl groups arrs aux).get ⟨i, h⟩ = grpTab Q (pl i) groups[i] := by
  simp only [List.get_eq_getElem, lvmTabs]
  rw [List.getElem_append_left (by simp; omega), List.getElem_append_left (by simp; omega)]
  simp [List.getElem?_eq_getElem hi]

theorem get_arr {k : ℕ} (hk : k < arrs.length) (h : groups.length + k < (lvmTabs Q pl groups arrs aux).length) :
    (lvmTabs Q pl groups arrs aux).get ⟨groups.length + k, h⟩ = arrs[k].tab := by
  simp only [List.get_eq_getElem, lvmTabs]
  rw [List.getElem_append_left (by simp; omega), List.getElem_append_right (by simp)]
  simp

theorem get_aux {k : ℕ} (hk : k < aux.length)
    (h : groups.length + arrs.length + k < (lvmTabs Q pl groups arrs aux).length) :
    (lvmTabs Q pl groups arrs aux).get ⟨groups.length + arrs.length + k, h⟩ = aux[k] := by
  simp only [List.get_eq_getElem, lvmTabs]
  rw [List.getElem_append_right (by simp)]
  simp

/-- The value of a fixed column at a row is its function's. -/
theorem row_fixed (q : Column L.μ) (j : Fin (lvmTabs Q pl groups arrs aux).length)
    (x : Fin (2 ^ ((lvmTabs Q pl groups arrs aux).get j).τ)) (i : Fin ((lvmTabs Q pl groups arrs aux).get j).w)
    {f : ℕ → FK} (hf : ((lvmTabs Q pl groups arrs aux).get j).fixedOf i = some f) :
    (lvmInst Q pl groups arrs aux L hτ).row q j x i = FK.toBF64 (f x) := by
  simp only [M3Instance.row, M3Instance.column, inst, hf, Option.map_some, Option.elim_some,
    fixedColumn, Vector.get_ofFn]

end Bridge
end Lvm.M3
end

section
namespace Lvm.M3
open LeanVM.Parameters LeanVM.Protocol CompPoly CMlPolynomialEval
open Lvm.Loop
section Bridge
variable (Q : Program) (pl : ℕ → Var → Bool × ℕ) (groups : List Grp) (arrs : List InArr) (aux : List Tab) (L : Lay)
  (hτ : ∀ t ∈ lvmTabs Q pl groups arrs aux, t.τ ≤ L.μ)

/-- The input array row seeding cell `e` of memory `τ`, if any: the first array that does. -/
def findIn (τ : Loop.Ty) (e : ℕ) : Option (ℕ × ℕ) :=
  (List.range arrs.length).findSome? fun k ↦
    ((List.range (2 ^ (arrs.getD k default).τ)).find? fun x ↦
      (arrs.getD k default).ty = τ ∧
        (arrs.getD k default).base + (arrs.getD k default).stride * x = e).map (k, ·)

/-- Limb `l` of the input array row `(k, x)` read off the stack (`0` outside). -/
noncomputable def inVal (q : Column L.μ) (k x l : ℕ) : FK :=
  if h : groups.length + k < (lvmTabs Q pl groups arrs aux).length then
    if hx : x < 2 ^ ((lvmTabs Q pl groups arrs aux).get ⟨_, h⟩).τ then
      if hl : l < ((lvmTabs Q pl groups arrs aux).get ⟨_, h⟩).w then
        FK.ofBF64 ((lvmInst Q pl groups arrs aux L hτ).row q ⟨_, h⟩ ⟨x, hx⟩ ⟨l, hl⟩)
      else 0
    else 0
  else 0

/-- **The `K` inputs on the stack.** -/
noncomputable def inKOf (q : Column L.μ) : Array FK :=
  Array.ofFn (n := Q.nInK) fun e ↦
    match findIn arrs .K e with
    | some (k, x) => inVal Q pl groups arrs aux L hτ q k x 0
    | none => 0

/-- **The `E` inputs on the stack.** -/
noncomputable def inEOf (q : Column L.μ) : Array FE :=
  Array.ofFn (n := Q.nInE) fun e ↦
    match findIn arrs .E e with
    | some (k, x) => ⟨inVal Q pl groups arrs aux L hτ q k x 0, inVal Q pl groups arrs aux L hτ q k x 1,
        inVal Q pl groups arrs aux L hτ q k x 2⟩
    | none => 0

theorem inKOf_size (q : Column L.μ) : (inKOf Q pl groups arrs aux L hτ q).size = Q.nInK := by
  simp [inKOf]

theorem inEOf_size (q : Column L.μ) : (inEOf Q pl groups arrs aux L hτ q).size = Q.nInE := by
  simp [inEOf]

end Bridge
end Lvm.M3
end

section
namespace Lvm.M3
open LeanVM.Parameters LeanVM.Protocol CompPoly CMlPolynomialEval
open Lvm.Loop

/-- **WP-10's `hinj`**: `g`-powers are injective below `N ≤ 2^64 - 1`. -/
theorem loop_ginj {N : ℕ} (hN : N ≤ 2 ^ 64 - 1) : GInj N :=
  fun _ _ ha hb h ↦ FK.FKx_pow_inj (by omega) (by omega) h

/-- A LoopIR message as sixteen coordinates: separator, address, count, value limbs, zeros. -/
def encT (m : Loop.Msg) : Vector K 16 := Vector.ofFn fun k ↦
  if k.val = 0 then FK.toBF64 m.sep else if k.val = 1 then FK.toBF64 m.addr
  else if k.val = 2 then FK.toBF64 m.cnt else FK.toBF64 (m.val.getD (k.val - 3) 0)

/-- A message of memory `τ`: its separator and its limb count. -/
def Shaped (m : Loop.Msg) : Prop := ∃ τ : Loop.Ty, m.sep = sep τ ∧ m.val.length = τ.limbs

theorem sep_ne : sep Loop.Ty.K ≠ sep Loop.Ty.E := by
  intro h
  have := FK.FKx_pow_inj (a := 3) (b := 4) (by norm_num) (by norm_num) h
  omega

theorem sep_inj' {τ τ' : Loop.Ty} (h : sep τ = sep τ') : τ = τ' := by
  cases τ <;> cases τ' <;> first | rfl | exact absurd h sep_ne | exact absurd h.symm sep_ne

end Lvm.M3
end

section
namespace Lvm.M3
open LeanVM.Parameters LeanVM.Protocol CompPoly CMlPolynomialEval
open Lvm.Loop

/-- **Equal tuple keys are equal message keys**, for shaped messages. -/
theorem key_of_keyT {m m' : Loop.Msg} (hm : Shaped m) (hm' : Shaped m')
    (h : keyT (encT m) = keyT (encT m')) : m.key = m'.key := by
  obtain ⟨τ, hs, hl⟩ := hm
  obtain ⟨τ', hs', hl'⟩ := hm'
  have h0 := keyT_coord h 0 (by norm_num) (by norm_num)
  have h1 := keyT_coord h 1 (by norm_num) (by norm_num)
  simp only [encT, Vector.getElem_ofFn] at h0 h1
  simp only [if_true, show ¬ (1 = 0) from by decide, if_false] at h0 h1
  have hsep : m.sep = m'.sep := FK.toBF64_injective h0
  have hτ : τ = τ' := sep_inj' (hs.symm.trans (hsep.trans hs'))
  subst hτ
  have hlen : m.val.length = m'.val.length := hl.trans hl'.symm
  have hlim : τ.limbs ≤ 3 := by cases τ <;> simp [Loop.Ty.limbs]
  have hval : m.val = m'.val := by
    apply List.ext_getElem hlen
    intro l hl1 hl2
    have hc := keyT_coord h (l + 3) (by omega) (by omega)
    simp only [encT, Vector.getElem_ofFn, show l + 3 ≠ 0 from by omega,
      show l + 3 ≠ 1 from by omega, show l + 3 ≠ 2 from by omega, if_false,
      Nat.add_sub_cancel] at hc
    have := FK.toBF64_injective hc
    rwa [List.getD_eq_getElem _ _ hl1, List.getD_eq_getElem _ _ hl2] at this
  simp only [Loop.Msg.key, hsep, FK.toBF64_injective h1, hval]

/-- The key of an evaluated table message is the key of a LoopIR message, when the separators,
addresses and value limbs agree. -/
theorem keyT_vec_eq {w : ℕ} (r : Fin w → K) (k : Key) (cnt : CPoly) (m : Loop.Msg)
    (hs : k.sep = m.sep) (ha : CPoly.evalB (CPoly.ext r) k.addr = FK.toBF64 m.addr)
    (hl : k.val.length = m.val.length)
    (hv : ∀ l (h1 : l < k.val.length) (h2 : l < m.val.length),
      CPoly.evalB (CPoly.ext r) k.val[l] = FK.toBF64 m.val[l]) :
    keyT (evalV r (k.vec w cnt)) = keyT (encT m) := by
  apply Vector.ext; intro i hi
  simp only [keyT, Vector.getElem_ofFn, Fin.getElem_fin, evalV, Vector.getElem_map, Key.vec, encT]
  by_cases h2 : i = 2
  · simp [h2]
  by_cases h0 : i = 0
  · subst h0; simp [hs]
  by_cases h1 : i = 1
  · subst h1; simp [CPoly.eval_toMv, ha]
  simp only [h0, h1, h2, if_false, CPoly.eval_toMv]
  rcases Nat.lt_or_ge (i - 3) k.val.length with h | h
  · rw [List.getD_eq_getElem _ _ h, List.getD_eq_getElem _ _ (hl ▸ h), hv _ h (hl ▸ h)]
  · rw [List.getD_eq_default _ _ h, List.getD_eq_default _ _ (hl ▸ h)]
    simp [CPoly.evalB]

end Lvm.M3
end

section
namespace Lvm.M3
open LeanVM.Parameters LeanVM.Protocol CompPoly CMlPolynomialEval
open Lvm.Loop

theorem read_fixIn (σ : Loop.Shape) (f : Flush) (hf : f ∈ σ.readFlushes) :
    FixIn σ f.addr ∧ ∀ P ∈ f.val, FixIn σ P := by
  simp only [Loop.Shape.readFlushes, List.mem_append, List.mem_map, List.mem_range] at hf
  rcases hf with ⟨o, ho, rfl⟩ | hf
  · refine ⟨fixIn_var_fix σ _ ?_, fun P hP ↦ ?_⟩
    · simp [Loop.Shape.fcols, ho]
    · simp only [Loop.Shape.argVals, List.mem_map] at hP
      obtain ⟨l, -, rfl⟩ := hP
      exact fixIn_var_nonfix σ _ (fun c h ↦ by cases h)
  · split at hf
    · simp only [List.mem_singleton] at hf; subst hf
      refine ⟨fixIn_var_nonfix σ _ (fun c h ↦ by cases h), fun P hP ↦ ?_⟩
      simp only [Loop.Shape.resVals, List.mem_map] at hP
      obtain ⟨l, -, rfl⟩ := hP
      exact fixIn_var_nonfix σ _ (fun c h ↦ by cases h)
    · simp at hf

theorem seed_fixIn (σ : Loop.Shape) (hw : σ.writes = true) :
    FixIn σ σ.seedFlush.addr ∧ ∀ P ∈ σ.seedFlush.val, FixIn σ P := by
  refine ⟨fixIn_var_fix σ _ (by simp [Loop.Shape.fcols, hw]), fun P hP ↦ ?_⟩
  simp only [Loop.Shape.seedFlush, Loop.Shape.resVals, List.mem_map] at hP
  obtain ⟨l, -, rfl⟩ := hP
  exact fixIn_var_nonfix σ _ (fun c h ↦ by cases h)

theorem read_shaped (σ : Loop.Shape) (f : Flush) (hf : f ∈ σ.readFlushes) (v : Var → FK) :
    Shaped (f.msg v) := by
  simp only [Loop.Shape.readFlushes, List.mem_append, List.mem_map, List.mem_range] at hf
  rcases hf with ⟨o, -, rfl⟩ | hf
  · exact ⟨σ.args.getD o .K, rfl, by simp [Flush.msg, Loop.Shape.argVals, Loop.Shape.argLimbs]⟩
  · split at hf
    · simp only [List.mem_singleton] at hf; subst hf
      exact ⟨σ.ty, rfl, by simp [Flush.msg, Loop.Shape.resVals]⟩
    · simp at hf

theorem seed_shaped (σ : Loop.Shape) (v : Var → FK) : Shaped (σ.seedFlush.msg v) :=
  ⟨σ.ty, rfl, by simp [Flush.msg, Loop.Shape.seedFlush, Loop.Shape.resVals]⟩

end Lvm.M3
end

section
namespace Lvm.M3
open LeanVM.Parameters LeanVM.Protocol CompPoly CMlPolynomialEval
open Lvm.Loop
section Bridge2
variable (Q : Program) (pl : ℕ → Var → Bool × ℕ) (groups : List Grp) (arrs : List InArr) (aux : List Tab) (L : Lay)
  (hτ : ∀ t ∈ lvmTabs Q pl groups arrs aux, t.τ ≤ L.μ)

theorem loc_eq (hg : GrpOk Q groups) {i n off : ℕ} (hi : i < groups.length)
    (hm : (n, off) ∈ groups[i].mem) : loc groups n = some (i, off) := by
  have hgd : ∀ i' (h : i' < groups.length), groups.getD i' default = groups[i'] := fun i' h ↦ by
    simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h]
  have hsome : (loc groups n).isSome := by
    unfold loc
    rw [List.findSome?_isSome_iff]
    refine ⟨i, List.mem_range.mpr hi, ?_⟩
    rw [Option.isSome_map, List.find?_isSome, hgd i hi]
    exact ⟨_, hm, by simp⟩
  obtain ⟨⟨i1, off1⟩, hres⟩ := Option.isSome_iff_exists.mp hsome
  rw [hres]
  unfold loc at hres
  obtain ⟨i1', hi1, hF⟩ := List.exists_of_findSome?_eq_some hres
  obtain ⟨m, hfind, heq⟩ := Option.map_eq_some_iff.mp hF
  simp only [Prod.mk.injEq] at heq
  obtain ⟨rfl, rfl⟩ := heq
  have hi1l : i1' < groups.length := List.mem_range.mp hi1
  have hpr := List.find?_some hfind
  have hmm := List.mem_of_find?_eq_some hfind
  rw [hgd i1' hi1l] at hmm
  simp only [beq_iff_eq] at hpr
  obtain ⟨m1, m2⟩ := m
  simp only at hpr; subst hpr
  obtain ⟨h1, h2⟩ := hg.uniq i1' i hi1l hi _ _ _ hmm hm
  rw [h1, h2]

theorem at_eq (hg : GrpOk Q groups) {g : Grp} (hgm : g ∈ groups) {n off y : ℕ}
    (hm : (n, off) ∈ g.mem) (hy : Grp.Holds Q (n, off) y = true) : g.at Q y = some (n, y - off) := by
  have hsome : (g.mem.find? fun m ↦ Grp.Holds Q m y).isSome := by
    rw [List.find?_isSome]; exact ⟨_, hm, hy⟩
  obtain ⟨m, hm'⟩ := Option.isSome_iff_exists.mp hsome
  have := hg.disj g hgm m (List.mem_of_find?_eq_some hm') _ hm y
    (List.find?_some (p := fun m ↦ Grp.Holds Q m y) hm') hy
  subst this
  simp [Grp.at, hm']

/-- **A group row on the stack holds the witness's values**: at row `off + x` of the table of the
group holding piece `n` at `off`, at the column of a variable, the row holds the variable's value
under `witOf` (fixed variables: when they are columns). -/
theorem ext_row_grp (hg : GrpOk Q groups) (q : Column L.μ) {i n off x : ℕ} {p : Piece}
    (hi : i < groups.length) (hm : (n, off) ∈ groups[i].mem) (hp : Q.pieces[n]? = some p)
    (hx : x < 2 ^ Q.height p) (h : i < (lvmTabs Q pl groups arrs aux).length)
    (hy : off + x < 2 ^ ((lvmTabs Q pl groups arrs aux).get ⟨i, h⟩).τ) (u : Var)
    (hu : ∀ c, u = .fix c → u ∈ shapeVars p.shape) :
    CPoly.ext ((lvmInst Q pl groups arrs aux L hτ).row q ⟨i, h⟩ ⟨off + x, hy⟩) (vidx p.shape u) =
      FK.toBF64 (Q.rowVal (witOf Q pl groups arrs aux L hτ q) n p x u) := by
  have hget := get_grp Q pl groups arrs aux hi h
  obtain ⟨p', hp', hσ, -, -⟩ := hg.mem _ (List.getElem_mem hi) _ hm
  simp only at hp'
  rw [hp] at hp'
  obtain rfl := Option.some.inj hp'
  have hw : ((lvmTabs Q pl groups arrs aux).get ⟨i, h⟩).w = (shapeVars p.shape).length := by
    rw [hget, hσ]; simp [grpTab, shapeTab, Tab.w]
  by_cases hfix : ∃ c, u = .fix c
  · obtain ⟨c, rfl⟩ := hfix
    have hmem := hu c rfl
    have hil : vidx p.shape (.fix c) < ((lvmTabs Q pl groups arrs aux).get ⟨i, h⟩).w := by
      rw [hw]; exact List.idxOf_lt_length_of_mem hmem
    have hfx : ((lvmTabs Q pl groups arrs aux).get ⟨i, h⟩).fixedOf (vidx p.shape (.fix c)) =
        some (grpFix Q groups[i] c) := by
      rw [hget]
      simp only [Tab.fixedOf, grpTab, shapeTab, List.getElem?_map, vidx, ← hσ]
      rw [List.getElem?_eq_getElem (List.idxOf_lt_length_of_mem hmem),
        List.getElem_idxOf (List.idxOf_lt_length_of_mem hmem)]
      rfl
    simp only [CPoly.ext, dif_pos hil]
    rw [row_fixed Q pl groups arrs aux L hτ q ⟨i, h⟩ ⟨off + x, hy⟩ ⟨_, hil⟩ hfx]
    have hpd : Q.pieces.getD n default = p := by simp [List.getD_eq_getElem?_getD, hp]
    have hholds : Grp.Holds Q (n, off) (off + x) = true := by
      simp [Grp.Holds, hp, hx]
    simp only [grpFix, at_eq Q groups hg (List.getElem_mem hi) hm hholds, hpd,
      Nat.add_sub_cancel_left]
    rfl
  · have hrv : Q.rowVal (witOf Q pl groups arrs aux L hτ q) n p x u =
        witOf Q pl groups arrs aux L hτ q n x u := by
      cases u <;> first | rfl | exact absurd ⟨_, rfl⟩ hfix
    rw [hrv]
    have hgd : Q.pieces.getD n default = p := by simp [List.getD_eq_getElem?_getD, hp]
    simp only [witOf, loc_eq Q groups hg hi hm, dif_pos h, dif_pos hy, CPoly.ext, hgd]
    split <;> simp

/-- Under `InOk`, the first array row seeding cell `base + stride·x` of array `k`'s memory is
`(k, x)`. -/
theorem findIn_eq (hok : InOk Q arrs) {k x : ℕ} (hk : k < arrs.length) (hx : x < 2 ^ arrs[k].τ) :
    findIn arrs arrs[k].ty (arrs[k].base + arrs[k].stride * x) = some (k, x) := by
  have hgd : ∀ k' (h : k' < arrs.length), arrs.getD k' default = arrs[k'] := fun k' h ↦ by
    simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h]
  have hsome : (findIn arrs arrs[k].ty (arrs[k].base + arrs[k].stride * x)).isSome := by
    unfold findIn
    rw [List.findSome?_isSome_iff]
    refine ⟨k, List.mem_range.mpr hk, ?_⟩
    rw [Option.isSome_map, List.find?_isSome]
    exact ⟨x, List.mem_range.mpr (by rw [hgd k hk]; exact hx),
      by simp [List.getElem?_eq_getElem hk]⟩
  obtain ⟨⟨k1, x1⟩, hres⟩ := Option.isSome_iff_exists.mp hsome
  rw [hres]
  unfold findIn at hres
  obtain ⟨k1', hk1, hF⟩ := List.exists_of_findSome?_eq_some hres
  obtain ⟨x1', hfind, heq⟩ := Option.map_eq_some_iff.mp hF
  simp only [Prod.mk.injEq] at heq
  obtain ⟨rfl, rfl⟩ := heq
  have hk1l : k1' < arrs.length := List.mem_range.mp hk1
  have hpr := List.find?_some hfind
  have hxm := List.mem_range.mp (List.mem_of_find?_eq_some hfind)
  simp only [hgd k1' hk1l, decide_eq_true_eq] at hpr hxm
  obtain ⟨h1, h2⟩ := (hok.inj ⟨k1', hk1l⟩ ⟨k, hk⟩ x1' x hxm hx hpr.1 hpr.2)
  simp only [Fin.mk.injEq] at h1
  rw [h1, h2]

/-- **A public array's value is its input cell** (BLUEPRINT A19's `PUB`): for every stack, the `K`
input cell `base + stride·x` of a public `K` array is the public value `f x`. -/
theorem inKOf_pub (hok : InOk Q arrs) (q : Column L.μ) {k : ℕ} (hk : k < arrs.length)
    (hty : arrs[k].ty = .K) {f : ℕ → FK} {e : List FE → FE} (hpub : arrs[k].pub = some (f, e))
    {x : ℕ} (hx : x < 2 ^ arrs[k].τ) :
    (inKOf Q pl groups arrs aux L hτ q).getD (arrs[k].base + arrs[k].stride * x) 0 = f x := by
  have hmem : arrs[k] ∈ arrs := List.getElem_mem hk
  have hlt : arrs[k].base + arrs[k].stride * x < Q.nInK := by
    have := hok.lt _ hmem x hx; rwa [hty] at this
  have hfind := findIn_eq Q arrs hok hk hx
  rw [hty] at hfind
  have hj : groups.length + k < (lvmTabs Q pl groups arrs aux).length := by
    rw [lvmTabs_length]; omega
  have hget := get_arr Q pl groups arrs aux hk hj
  have hlim : arrs[k].val.length = 1 := by have := hok.limbs _ hmem; rw [hty] at this; exact this
  have hτeq : ((lvmTabs Q pl groups arrs aux).get ⟨_, hj⟩).τ = arrs[k].τ := by rw [hget]; rfl
  have hxt : x < 2 ^ ((lvmTabs Q pl groups arrs aux).get ⟨_, hj⟩).τ := by rw [hτeq]; exact hx
  have hw : 0 < ((lvmTabs Q pl groups arrs aux).get ⟨_, hj⟩).w := by
    rw [hget]; simp [InArr.tab, Tab.w]
  have hfx : ((lvmTabs Q pl groups arrs aux).get ⟨_, hj⟩).fixedOf 0 = some f := by
    rw [hget]
    obtain ⟨v, hv⟩ : ∃ v, arrs[k].val = [v] := List.length_eq_one_iff.mp hlim
    simp [Tab.fixedOf, InArr.tab, InArr.vcols, hpub, hv]
  simp only [inKOf, Array.getD_eq_getD_getElem?, Array.getElem?_ofFn, dif_pos hlt, Option.getD_some,
    hfind, inVal, dif_pos hj, dif_pos hxt, dif_pos hw]
  rw [row_fixed Q pl groups arrs aux L hτ q ⟨_, hj⟩ ⟨x, hxt⟩ ⟨0, hw⟩ hfx, FK.ofBF64_toBF64]

end Bridge2
end Lvm.M3
end

section
namespace Lvm.M3
open LeanVM.Parameters LeanVM.Protocol CompPoly CMlPolynomialEval
open Lvm.Loop
section Bridge2
variable (Q : Program) (pl : ℕ → Var → Bool × ℕ) (groups : List Grp) (arrs : List InArr) (aux : List Tab) (L : Lay)
  (hτ : ∀ t ∈ lvmTabs Q pl groups arrs aux, t.τ ≤ L.μ)

/-- The seed of an input array row has the key of an input seed of the LoopIR program (the case of
`loop_bus` for the input arrays, in continuation form). -/
theorem inputKey (q : Column L.μ) (hok : InOk Q arrs) {k : ℕ} (hk : k < arrs.length)
    (hj : groups.length + k < (lvmTabs Q pl groups arrs aux).length)
    (x' : Fin (2 ^ ((lvmTabs Q pl groups arrs aux).get ⟨groups.length + k, hj⟩).τ)) (sd : Key × ℕ)
    (hsd : sd = (⟨sep arrs[k].ty, CPoly.var (arrs[k].val.length + 1),
      (List.range arrs[k].val.length).map CPoly.var⟩, arrs[k].val.length))
    (hget : (lvmTabs Q pl groups arrs aux).get ⟨groups.length + k, hj⟩ = arrs[k].tab) (goal : Prop)
    (hfin : ∀ m' : Loop.Msg, Shaped m' → m' ∈ Q.seedMsgs (witOf Q pl groups arrs aux L hτ q)
      (inKOf Q pl groups arrs aux L hτ q) (inEOf Q pl groups arrs aux L hτ q) →
      keyT (evalV ((lvmInst Q pl groups arrs aux L hτ).row q ⟨_, hj⟩ x')
        (((lvmTabs Q pl groups arrs aux).get ⟨_, hj⟩).seedVec sd)) = keyT (encT m') → goal) : goal := by
  subst hsd
  have hτeq : ((lvmTabs Q pl groups arrs aux).get ⟨_, hj⟩).τ = arrs[k].τ := by rw [hget]; rfl
  have hxa : x'.val < 2 ^ arrs[k].τ := lt_of_lt_of_eq x'.isLt (by rw [hτeq])
  have hw : ((lvmTabs Q pl groups arrs aux).get ⟨_, hj⟩).w = arrs[k].val.length + 2 := by
    rw [hget]; simp [InArr.tab, Tab.w]
  have hmem : arrs[k] ∈ arrs := List.getElem_mem hk
  have hlim := hok.limbs _ hmem
  have hlt := hok.lt _ hmem x'.val hxa
  have hfind := findIn_eq Q arrs hok hk hxa
  -- the address column
  have hcol : (arrs[k].tab.cols)[arrs[k].val.length + 1]? =
      some (.fix (fun x ↦ FK.x ^ (arrs[k].base + arrs[k].stride * x))
        (fun r ↦ FE.ofK (FK.x ^ arrs[k].base) * powEval r (FK.x ^ arrs[k].stride))) := by
    simp only [InArr.tab]
    rw [List.getElem?_append_right (by simp)]
    simp
  have haddr : CPoly.ext ((lvmInst Q pl groups arrs aux L hτ).row q ⟨_, hj⟩ x') (arrs[k].val.length + 1) =
      FK.toBF64 (FK.x ^ (arrs[k].base + arrs[k].stride * x'.val)) := by
    have hi : arrs[k].val.length + 1 < ((lvmTabs Q pl groups arrs aux).get ⟨_, hj⟩).w := by rw [hw]; omega
    have hfx : ((lvmTabs Q pl groups arrs aux).get ⟨_, hj⟩).fixedOf (arrs[k].val.length + 1) =
        some (fun x ↦ FK.x ^ (arrs[k].base + arrs[k].stride * x)) := by
      rw [hget]; simp only [Tab.fixedOf, hcol]
    simp only [CPoly.ext, dif_pos hi]
    exact row_fixed Q pl groups arrs aux L hτ q ⟨_, hj⟩ x' ⟨_, hi⟩ hfx
  -- the value columns
  have hval : ∀ l (hl : l < arrs[k].val.length),
      FK.toBF64 (inVal Q pl groups arrs aux L hτ q k x'.val l) =
        CPoly.ext ((lvmInst Q pl groups arrs aux L hτ).row q ⟨_, hj⟩ x') l := by
    intro l hl
    have hi : l < ((lvmTabs Q pl groups arrs aux).get ⟨_, hj⟩).w := by rw [hw]; omega
    simp only [inVal, dif_pos hj, dif_pos x'.isLt, dif_pos hi, CPoly.ext, FK.toBF64_ofBF64]
  -- the seed's key
  have hkey : ∀ m' : Loop.Msg, m'.sep = sep arrs[k].ty →
      m'.addr = FK.x ^ (arrs[k].base + arrs[k].stride * x'.val) →
      m'.val.length = arrs[k].val.length →
      (∀ l (hl : l < arrs[k].val.length) (h2 : l < m'.val.length),
        FK.toBF64 m'.val[l] = CPoly.ext ((lvmInst Q pl groups arrs aux L hτ).row q ⟨_, hj⟩ x') l) →
      keyT (evalV ((lvmInst Q pl groups arrs aux L hτ).row q ⟨_, hj⟩ x')
        (((lvmTabs Q pl groups arrs aux).get ⟨_, hj⟩).seedVec
          (⟨sep arrs[k].ty, CPoly.var (arrs[k].val.length + 1),
            (List.range arrs[k].val.length).map CPoly.var⟩, arrs[k].val.length))) =
        keyT (encT m') := by
    intro m' h1 h2 h3 h4
    refine keyT_vec_eq _ _ _ _ h1.symm ?_ (by simpa using h3.symm) ?_
    · rw [evalB_var, haddr, h2]
    · intro l h1' h2'
      simp only [List.getElem_map, List.getElem_range, evalB_var]
      have hl : l < arrs[k].val.length := by simpa using h1'
      exact (h4 l hl h2').symm
  cases hty : arrs[k].ty with
  | K =>
    rw [hty] at hfind hlt hlim
    refine hfin ⟨sep .K, FK.x ^ (arrs[k].base + arrs[k].stride * x'.val), 1,
      [(inKOf Q pl groups arrs aux L hτ q).getD (arrs[k].base + arrs[k].stride * x'.val) 0]⟩
      ⟨.K, rfl, rfl⟩ ?_ (hkey _ (by rw [hty]) rfl (by simp only [List.length_singleton]; exact hlim.symm) ?_)
    · simp only [Program.seedMsgs, Program.inputSeeds, List.mem_append, List.mem_map,
        List.mem_range]
      exact Or.inl (Or.inl ⟨_, hlt, rfl⟩)
    · intro l hl h2
      have hl0 : l = 0 := by simp at h2; omega
      subst hl0
      have hltK : arrs[k].base + arrs[k].stride * x'.val < Q.nInK := hlt
      simp only [List.getElem_cons_zero, inKOf, Array.getD_eq_getD_getElem?, Array.getElem?_ofFn,
        dif_pos hltK, Option.getD_some, hfind]
      exact hval 0 hl
  | E =>
    rw [hty] at hfind hlt hlim
    refine hfin ⟨sep .E, FK.x ^ (arrs[k].base + arrs[k].stride * x'.val), 1,
      limbsOf .E ((inEOf Q pl groups arrs aux L hτ q).getD (arrs[k].base + arrs[k].stride * x'.val) 0)⟩
      ⟨.E, rfl, rfl⟩ ?_ (hkey _ (by rw [hty]) rfl (by simp only [limbsOf]; exact hlim.symm) ?_)
    · simp only [Program.seedMsgs, Program.inputSeeds, List.mem_append, List.mem_map,
        List.mem_range]
      exact Or.inl (Or.inr ⟨_, hlt, rfl⟩)
    · intro l hl h2
      have hltE : arrs[k].base + arrs[k].stride * x'.val < Q.nInE := hlt
      simp only [inEOf, Array.getD_eq_getD_getElem?, Array.getElem?_ofFn, dif_pos hltE,
        Option.getD_some, hfind, limbsOf, List.getElem_cons_zero, List.getElem_cons_succ] at h2 ⊢
      have : l < 3 := by simpa using h2
      interval_cases l
      · exact hval 0 hl
      · exact hval 1 hl
      · exact hval 2 hl

/-- The key of an evaluated group flush is the LoopIR message's. -/
theorem grp_key (hg : GrpOk Q groups) (q : Column L.μ) {i n off x : ℕ} {p : Piece}
    (hi : i < groups.length) (hm : (n, off) ∈ groups[i].mem)
    (hp : Q.pieces[n]? = some p) (hx : x < 2 ^ Q.height p)
    (h : i < (lvmTabs Q pl groups arrs aux).length)
    (hy : off + x < 2 ^ ((lvmTabs Q pl groups arrs aux).get ⟨i, h⟩).τ)
    (f : Flush) (hfix : FixIn p.shape f.addr ∧ ∀ P ∈ f.val, FixIn p.shape P) (cnt : CPoly) :
    keyT (evalV ((lvmInst Q pl groups arrs aux L hτ).row q ⟨i, h⟩ ⟨off + x, hy⟩)
        ((keyOf p.shape f).vec ((lvmTabs Q pl groups arrs aux).get ⟨i, h⟩).w cnt)) =
      keyT (encT (f.msg (Q.rowVal (witOf Q pl groups arrs aux L hτ q) n p x))) := by
  have hrow := ext_row_grp Q pl groups arrs aux L hτ hg q hi hm hp hx h hy
  refine keyT_vec_eq _ _ _ _ rfl ?_ (by simp [keyOf, Flush.msg]) ?_
  · exact evalB_ofPoly2 _ _ _ _ fun m hm y hy ↦ hrow y fun c hc ↦ hfix.1 m hm y hy c hc
  · intro l h1 h2
    simp only [keyOf, Flush.msg, List.getElem_map]
    have hl : l < f.val.length := by simpa [keyOf] using h1
    exact evalB_ofPoly2 _ _ _ _ fun m hm y hy ↦ hrow y fun c hc ↦
      hfix.2 _ (List.getElem_mem hl) m hm y hy c hc

/-- **Every seed of the instance is a LoopIR seed**: a group's result seed, or an input array's
input seed (auxiliary tables seed nothing), with the witness and the inputs read off the stack. -/
theorem seed_key (hg : GrpOk Q groups) (hok : InOk Q arrs) (haux : ∀ t ∈ aux, t.seeds = [])
    (q : Column L.μ) {s : Vector K 16} (hs : s ∈ seedTuples L (lvmTabs Q pl groups arrs aux) hτ q) :
    ∃ m' : Loop.Msg, Shaped m' ∧ m' ∈ Q.seedMsgs (witOf Q pl groups arrs aux L hτ q)
      (inKOf Q pl groups arrs aux L hτ q) (inEOf Q pl groups arrs aux L hτ q) ∧
      keyT s = keyT (encT m') := by
  set W := witOf Q pl groups arrs aux L hτ q with hW
  simp only [seedTuples, partT, List.mem_flatMap, List.mem_map] at hs
  obtain ⟨⟨jv, hj⟩, -, v, ⟨sd, hsd, rfl⟩, x', -, rfl⟩ := hs
  have hfin : ∀ m' : Loop.Msg, Shaped m' → m' ∈ Q.seedMsgs W (inKOf Q pl groups arrs aux L hτ q)
      (inEOf Q pl groups arrs aux L hτ q) →
      keyT (evalV ((lvmInst Q pl groups arrs aux L hτ).row q ⟨jv, hj⟩ x')
        (((lvmTabs Q pl groups arrs aux).get ⟨jv, hj⟩).seedVec sd)) = keyT (encT m') →
      ∃ m' : Loop.Msg, Shaped m' ∧ m' ∈ Q.seedMsgs W (inKOf Q pl groups arrs aux L hτ q)
        (inEOf Q pl groups arrs aux L hτ q) ∧
        keyT (evalV ((lvmInst Q pl groups arrs aux L hτ).row q ⟨jv, hj⟩ x')
          (((lvmTabs Q pl groups arrs aux).get ⟨jv, hj⟩).seedVec sd)) = keyT (encT m') :=
    fun m' h1 h2 h3 ↦ ⟨m', h1, h2, h3⟩
  rcases (by omega : jv < groups.length ∨
      (groups.length ≤ jv ∧ jv < groups.length + arrs.length) ∨
      groups.length + arrs.length ≤ jv) with hjp | ⟨hj1, hj2⟩ | hj3
  · -- a group's result seed: the member holding the row
    have hget' := get_grp Q pl groups arrs aux hjp hj
    have hτj : ((lvmTabs Q pl groups arrs aux).get ⟨jv, hj⟩).τ = groups[jv].τ := by
      rw [hget']; rfl
    obtain ⟨⟨n', off'⟩, hm', hhold⟩ := hg.cover _ (List.getElem_mem hjp) x'.val
      (lt_of_lt_of_eq x'.isLt (by rw [hτj]))
    obtain ⟨p', hp', hσ', -, -⟩ := hg.mem _ (List.getElem_mem hjp) _ hm'
    simp only at hp'
    have hpd : Q.pieces.getD n' default = p' := by simp [List.getD_eq_getElem?_getD, hp']
    simp only [Grp.Holds, hpd, Bool.and_eq_true, decide_eq_true_eq] at hhold
    have hx' : x'.val - off' < 2 ^ Q.height p' := by omega
    rw [hget'] at hsd
    simp only [grpTab, shapeTab, ← hσ'] at hsd
    split at hsd
    · rename_i hwr
      simp only [List.mem_singleton] at hsd
      subst hsd
      refine hfin (p'.shape.seedFlush.msg (Q.rowVal W n' p' (x'.val - off')))
        (seed_shaped _ _) ?_ ?_
      · simp only [Program.seedMsgs, List.mem_append, List.mem_flatMap]
        refine Or.inr ⟨(n', p', x'.val - off'), (Q.mem_prows).mpr ⟨hp', hx'⟩, ?_⟩
        simp [hwr]
      · have hy' : off' + (x'.val - off') < 2 ^ ((lvmTabs Q pl groups arrs aux).get ⟨jv, hj⟩).τ := by
          have := x'.isLt; omega
        have hxe : (⟨off' + (x'.val - off'), hy'⟩ : Fin _) = x' := Fin.ext (by simp; omega)
        have := grp_key Q pl groups arrs aux L hτ hg q hjp hm' hp' hx' hj hy' _ (seed_fixIn _ hwr) (CPoly.const 1)
        rw [hxe] at this
        exact this
    · simp at hsd
  · -- an input array's seed
    obtain ⟨k, rfl⟩ : ∃ k, jv = groups.length + k := ⟨jv - groups.length, by omega⟩
    have hk : k < arrs.length := by omega
    have hget' := get_arr Q pl groups arrs aux hk hj
    have hsd' := hsd
    rw [hget'] at hsd'
    simp only [InArr.tab, List.mem_singleton] at hsd'
    exact inputKey Q pl groups arrs aux L hτ q hok hk hj x' sd hsd' hget' _ hfin
  · -- an auxiliary table seeds nothing
    obtain ⟨k, rfl⟩ : ∃ k, jv = groups.length + arrs.length + k :=
      ⟨jv - groups.length - arrs.length, by omega⟩
    have hk : k < aux.length := by rw [lvmTabs_length] at hj; omega
    rw [get_aux Q pl groups arrs aux hk hj, haux _ (List.getElem_mem hk)] at hsd
    simp at hsd

/-- **The bus hypothesis of `loopir_sound`, verbatim.** On the lvm instance, `M3Holds` (its
balance and nonzero-count clauses), the input arrays' facts, auxiliary tables that seed nothing,
count columns inside their tables and fewer than `2^64 - 1` reads: every read of the LoopIR
pieces, with the witness and the inputs read off the stack, has the key of a seed. -/
theorem loop_bus (hg : GrpOk Q groups) (hok : InOk Q arrs) (haux : ∀ t ∈ aux, t.seeds = [])
    (hin : ∀ t ∈ lvmTabs Q pl groups arrs aux, ∀ r ∈ t.reads, r.2 < t.w)
    (hlen : nReads (lvmTabs Q pl groups arrs aux) < 2 ^ 64 - 1) (q : Column L.μ)
    (hM : M3Holds (lvmInst Q pl groups arrs aux L hτ) () q) :
    ∀ m ∈ Q.readMsgs (witOf Q pl groups arrs aux L hτ q),
      m.key ∈ (Q.seedMsgs (witOf Q pl groups arrs aux L hτ q) (inKOf Q pl groups arrs aux L hτ q)
        (inEOf Q pl groups arrs aux L hτ q)).map Loop.Msg.key := by
  set W := witOf Q pl groups arrs aux L hτ q with hW
  intro m hm
  simp only [Program.readMsgs, List.mem_flatMap, List.mem_map] at hm
  obtain ⟨⟨n, p, x⟩, hpx, f, hf, rfl⟩ := hm
  obtain ⟨hp, hxh⟩ := (Q.mem_prows).mp hpx
  have hnp : n < Q.pieces.length := (List.getElem?_eq_some_iff.mp hp).1
  obtain ⟨i, hi, off, hmem⟩ := hg.all n hnp
  obtain ⟨p', hp', hσ, hfit, -⟩ := hg.mem _ (List.getElem_mem hi) _ hmem
  simp only at hp' hfit
  rw [hp] at hp'
  obtain rfl := Option.some.inj hp'
  have h : i < (lvmTabs Q pl groups arrs aux).length := by rw [lvmTabs_length]; omega
  have hget := get_grp Q pl groups arrs aux hi h
  have hτi : ((lvmTabs Q pl groups arrs aux).get ⟨i, h⟩).τ = groups[i].τ := by
    rw [hget]; rfl
  have hy : off + x < 2 ^ ((lvmTabs Q pl groups arrs aux).get ⟨i, h⟩).τ := by
    rw [hτi]; omega
  have hrd : (keyOf p.shape f, cntOf p.shape f) ∈ ((lvmTabs Q pl groups arrs aux).get ⟨i, h⟩).reads := by
    rw [hget]; simp only [grpTab, shapeTab, ← hσ]; exact List.mem_map_of_mem hf
  have hu : evalV ((lvmInst Q pl groups arrs aux L hτ).row q ⟨i, h⟩ ⟨off + x, hy⟩)
      (((lvmTabs Q pl groups arrs aux).get ⟨i, h⟩).readVec (keyOf p.shape f, cntOf p.shape f)) ∈
      readTuples L (lvmTabs Q pl groups arrs aux) hτ q := by
    simp only [readTuples, partT, List.mem_flatMap, List.mem_map]
    refine ⟨⟨i, h⟩, List.mem_finRange _, _, ⟨_, hrd, rfl⟩, ⟨off + x, hy⟩, ?_, rfl⟩
    simp [M3Instance.executed, inst]
  have hkey := grp_key Q pl groups arrs aux L hτ hg q hi hmem hp hxh h hy f (read_fixIn _ f hf) (CPoly.var (cntOf p.shape f))
  obtain ⟨s, hs, hks⟩ := List.mem_map.mp (mem_lookup L (lvmTabs Q pl groups arrs aux) hτ q hM.2.1
    hM.2.2.1 hin hlen _ hu)
  obtain ⟨m', hsh, hm', he⟩ := seed_key Q pl groups arrs aux L hτ hg hok haux q hs
  rw [key_of_keyT (read_shaped _ f hf (Q.rowVal W n p x)) hsh (hkey.symm.trans (hks.symm.trans he))]
  exact List.mem_map_of_mem hm'

end Bridge2
end Lvm.M3
end

section
namespace Lvm.M3
open LeanVM.Parameters LeanVM.Protocol CompPoly CMlPolynomialEval
open Lvm.Loop
section Bridge2
variable (Q : Program) (pl : ℕ → Var → Bool × ℕ) (groups : List Grp) (arrs : List InArr) (aux : List Tab) (L : Lay)
  (hτ : ∀ t ∈ lvmTabs Q pl groups arrs aux, t.τ ≤ L.μ)

/-- **The constraint hypothesis of `loopir_sound`, verbatim.** On the lvm instance, the clause
`ConstraintsVanish` of `M3Holds` gives every LoopIR constraint at every piece row, with the witness
read off the stack. -/
theorem loop_cons (hg : GrpOk Q groups) (q : Column L.μ)
    (hM : M3Holds (lvmInst Q pl groups arrs aux L hτ) () q) :
    Q.ConstraintsHold (witOf Q pl groups arrs aux L hτ q) := by
  intro ⟨n, p, x⟩ hpx C hC
  obtain ⟨hp, hxh⟩ := (Q.mem_prows).mp hpx
  simp only at hC ⊢
  have hnp : n < Q.pieces.length := (List.getElem?_eq_some_iff.mp hp).1
  obtain ⟨i, hi, off, hmem⟩ := hg.all n hnp
  obtain ⟨p', hp', hσ, hfit, -⟩ := hg.mem _ (List.getElem_mem hi) _ hmem
  simp only at hp' hfit
  rw [hp] at hp'
  obtain rfl := Option.some.inj hp'
  have h : i < (lvmTabs Q pl groups arrs aux).length := by rw [lvmTabs_length]; omega
  have hget := get_grp Q pl groups arrs aux hi h
  have hτi : ((lvmTabs Q pl groups arrs aux).get ⟨i, h⟩).τ = groups[i].τ := by rw [hget]; rfl
  have hy : off + x < 2 ^ ((lvmTabs Q pl groups arrs aux).get ⟨i, h⟩).τ := by rw [hτi]; omega
  have hcm : ofPoly2 (vidx p.shape) C ∈ ((lvmTabs Q pl groups arrs aux).get ⟨i, h⟩).cons := by
    rw [hget]; simp only [grpTab, shapeTab, ← hσ]; exact List.mem_map_of_mem hC
  have hz := hM.1 ⟨i, h⟩ _ (List.mem_map_of_mem hcm) ⟨off + x, hy⟩
  rw [CPoly.eval_toMv] at hz
  have hrow := ext_row_grp Q pl groups arrs aux L hτ hg q hi hmem hp hxh h hy
  rw [evalB_ofPoly2 _ _ _ _ fun m hm y hy' ↦ hrow y fun c hc ↦
    constraints_fixIn _ C hC m hm y hy' c hc] at hz
  exact FK.toBF64_injective (hz.trans FK.toBF64_zero.symm)

end Bridge2
end Lvm.M3
end

section
namespace Lvm.M3
open LeanVM.Parameters LeanVM.Protocol CompPoly CMlPolynomialEval
open Lvm.Loop

/-- The empty program's instance: no table. -/
def emptyProgram : Program := ⟨0, 0, [], []⟩

/-- **Non-vacuity of `loop_bus`'s hypotheses**: on the empty program's instance, `M3Holds`, `GrpOk`
and `InOk` hold of every stack. -/
theorem empty_hyps (L : Lay) (q : Column L.μ) :
    M3Holds (lvmInst emptyProgram (fun _ _ ↦ (false, 0)) [] [] [] L (by simp [lvmTabs])) () q ∧
      GrpOk emptyProgram [] ∧ InOk emptyProgram [] := by
  have hj : ∀ j : Fin (lvmTabs emptyProgram (fun _ _ ↦ (false, 0)) [] [] []).length, False := by
    intro j; have := j.isLt; simp [lvmTabs, emptyProgram, Program.pieces] at this
  refine ⟨⟨fun j ↦ (hj j).elim, ?_, fun j ↦ (hj j).elim, fun l hl ↦ by simp at hl,
    fun r hr ↦ by simp at hr⟩, ⟨by simp, by simp, by simp,
      fun n hn ↦ by simp [emptyProgram, Program.pieces] at hn, by simp, by simp⟩,
    ⟨by simp, by simp, fun i ↦ i.elim0, fun τ e he ↦ by cases τ <;> simp [emptyProgram, Program.nIn] at he⟩⟩
  have hnil : ∀ sd, (lvmInst emptyProgram (fun _ _ ↦ (false, 0)) [] [] [] L
      (by simp [lvmTabs])).flushTuples q sd = [] := by
    intro sd
    apply List.eq_nil_iff_forall_not_mem.mpr
    intro x hx
    simp only [M3Instance.flushTuples, List.mem_flatMap] at hx
    obtain ⟨j, -, -⟩ := hx
    have := j.isLt
    simp [lvmTabs, emptyProgram, Program.pieces] at this
  unfold M3Instance.Balanced M3Instance.tuples
  rw [hnil, hnil]
  simp [M3Instance.boundaryTuples]

end Lvm.M3
end

-- ===== from `LvmVEqFit` =====

section
section
namespace Lvm.M3
open Lvm.Loop
section Tiles
variable {α : Type} (b s : α → ℕ)

/-- **Blocks end to end**: block `a` spans `[b a, b a + s a)`; the blocks of `l` start at `c`, each
where the previous one ends, and the last ends at `N`. -/
def tilesB : List α → ℕ → ℕ → Bool
  | [], c, N => c == N
  | a :: l, c, N => b a == c && tilesB l (c + s a) N

end Tiles
end Lvm.M3
end
end

section
section
namespace Lvm.M3
open Lvm.Loop
section Tiles
variable {α : Type} (b s : α → ℕ)
variable {b s}

theorem tiles_cons {a : α} {l : List α} {c N : ℕ} (h : tilesB b s (a :: l) c N = true) :
    b a = c ∧ tilesB b s l (c + s a) N = true := by
  simp only [tilesB, Bool.and_eq_true, beq_iff_eq] at h; exact h

theorem tiles_le : ∀ {l : List α} {c N : ℕ}, tilesB b s l c N = true → c ≤ N
  | [], c, N, h => by simp only [tilesB, beq_iff_eq] at h; omega
  | a :: l, c, N, h => by
    have := tiles_le (tiles_cons h).2; omega

/-- Every block lies inside `[c, N)`. -/
theorem tiles_mem : ∀ {l : List α} {c N : ℕ}, tilesB b s l c N = true →
    ∀ a ∈ l, c ≤ b a ∧ b a + s a ≤ N
  | [], _, _, _, a, ha => by simp at ha
  | a' :: l, c, N, h, a, ha => by
    obtain ⟨h1, h2⟩ := tiles_cons h
    rcases List.mem_cons.mp ha with rfl | ha
    · exact ⟨h1.ge, by rw [h1]; exact tiles_le h2⟩
    · have := tiles_mem h2 a ha; omega

/-- Earlier blocks end before later ones start. -/
theorem tiles_pairwise : ∀ {l : List α} {c N : ℕ}, tilesB b s l c N = true →
    l.Pairwise fun a a' ↦ b a + s a ≤ b a'
  | [], _, _, _ => List.Pairwise.nil
  | a :: l, c, N, h => by
    obtain ⟨h1, h2⟩ := tiles_cons h
    refine List.Pairwise.cons (fun a' ha' ↦ ?_) (tiles_pairwise h2)
    have := (tiles_mem h2 a' ha').1; omega

/-- Every point of `[c, N)` lies in a block. -/
theorem tiles_cover : ∀ {l : List α} {c N : ℕ}, tilesB b s l c N = true →
    ∀ e, c ≤ e → e < N → ∃ a ∈ l, b a ≤ e ∧ e < b a + s a
  | [], c, N, h, e, h1, h2 => by simp only [tilesB, beq_iff_eq] at h; omega
  | a :: l, c, N, h, e, h1, h2 => by
    obtain ⟨ha, hl⟩ := tiles_cons h
    by_cases he : e < c + s a
    · exact ⟨a, List.mem_cons_self .., by omega, by omega⟩
    · obtain ⟨a', ha', h3⟩ := tiles_cover hl e (by omega) h2
      exact ⟨a', List.mem_cons_of_mem _ ha', h3⟩

/-- A tiling depends on the sizes of its blocks only. -/
theorem tilesB_congr {s' : α → ℕ} : ∀ {l : List α} {c N : ℕ}, (∀ a ∈ l, s a = s' a) →
    tilesB b s l c N = tilesB b s' l c N
  | [], _, _, _ => rfl
  | a :: l, c, N, h => by
    simp only [tilesB, h a List.mem_cons_self,
      tilesB_congr (l := l) fun a' ha' ↦ h a' (List.mem_cons_of_mem _ ha')]

/-- Two blocks of a tiling holding the same point are the same block. -/
theorem tiles_unique {l : List α} {c N : ℕ} (h : tilesB b s l c N = true) {a a' : α}
    (ha : a ∈ l) (ha' : a' ∈ l) {y : ℕ} (hy : b a ≤ y ∧ y < b a + s a)
    (hy' : b a' ≤ y ∧ y < b a' + s a') : a = a' := by
  have hp := List.pairwise_iff_getElem.mp (tiles_pairwise h)
  obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem ha
  obtain ⟨i', hi', rfl⟩ := List.getElem_of_mem ha'
  rcases Nat.lt_trichotomy i i' with hlt | rfl | hlt
  · have := hp i i' hi hi' hlt; omega
  · rfl
  · have := hp i' i hi' hi hlt; omega

end Tiles
end Lvm.M3
end
end

section
section
namespace Lvm.M3
open Lvm.Loop
namespace NTrie
variable {α : Type}

/-- The entry at key `n`. -/
def get? : NTrie α → ℕ → Option α
  | .nil, _ => none
  | .node v l r, n => if n = 0 then v else if n % 2 = 1 then l.get? (n / 2) else r.get? (n / 2 - 1)

end NTrie
end Lvm.M3
end
end

section
section
namespace Lvm.M3
open Lvm.Loop
namespace NTrie
variable {α : Type}

theorem get?_parts (t : NTrie α) (n : ℕ) :
    t.get? n = (NTrie.node t.parts.1 t.parts.2.1 t.parts.2.2).get? n := by
  cases t <;> simp [get?, parts]

theorem get?_ins (a : α) : ∀ (f : ℕ) (t : NTrie α) (n m : ℕ), n + 1 < 2 ^ f →
    (t.ins a f n).get? m = if m = n then some a else t.get? m
  | 0, _, n, _, h => by simp at h
  | f + 1, t, n, m, h => by
    rw [get?_parts t m]
    simp only [ins]
    by_cases hn : n = 0
    · subst hn; by_cases hm : m = 0 <;> simp [get?, hm]
    by_cases hp : n % 2 = 1
    · simp only [hn, hp, if_false, if_true, get?]
      have hf : n / 2 + 1 < 2 ^ f := by rw [pow_succ] at h; omega
      by_cases hm : m = 0
      · subst hm; simp only [get?, if_true]; rw [if_neg (fun h' : 0 = n ↦ hn h'.symm)]
      by_cases hq : m % 2 = 1
      · rw [get?_ins a f _ _ _ hf]; simp only [hm, hq, if_false, if_true]
        by_cases he : m / 2 = n / 2
        · have : m = n := by omega
          simp [he, this]
        · have : m ≠ n := fun h' ↦ he (by rw [h'])
          simp [he, this]
      · have : m ≠ n := by omega
        simp [hm, hq, this]
    · simp only [hn, hp, if_false, get?]
      have hf : n / 2 - 1 + 1 < 2 ^ f := by rw [pow_succ] at h; omega
      by_cases hm : m = 0
      · subst hm; simp only [get?, if_true]; rw [if_neg (fun h' : 0 = n ↦ hn h'.symm)]
      by_cases hq : m % 2 = 1
      · have : m ≠ n := by omega
        simp [hm, hq, this]
      · rw [get?_ins a f _ _ _ hf]; simp only [hm, hq, if_false]
        by_cases he : m / 2 - 1 = n / 2 - 1
        · have : m = n := by omega
          simp [he, this]
        · have : m ≠ n := fun h' ↦ he (by rw [h'])
          simp [he, this]

/-- The trie of a list from key `k` on. -/
def ofListFrom : List α → ℕ → NTrie α → NTrie α
  | [], _, t => t
  | a :: l, k, t => ofListFrom l (k + 1) (t.ins a 64 k)

/-- The trie of a list: entry `n` at key `n`. -/
def ofList (l : List α) : NTrie α := ofListFrom l 0 .nil

theorem get?_ofListFrom : ∀ (l : List α) (k : ℕ) (t : NTrie α), k + l.length < 2 ^ 64 →
    ∀ m, (ofListFrom l k t).get? m = if k ≤ m ∧ m < k + l.length then l[m - k]? else t.get? m
  | [], k, t, _, m => by simp [ofListFrom]
  | a :: l, k, t, h, m => by
    simp only [ofListFrom, List.length_cons] at h ⊢
    rw [get?_ofListFrom l (k + 1) _ (by omega), get?_ins a 64 t k m (by omega)]
    by_cases h1 : k + 1 ≤ m ∧ m < k + 1 + l.length
    · rw [if_pos h1, if_pos ⟨by omega, by omega⟩,
        show m - k = (m - (k + 1)) + 1 by omega, List.getElem?_cons_succ]
    · rw [if_neg h1]
      by_cases hm : m = k
      · subst hm; simp
      · rw [if_neg hm, if_neg (by omega)]

theorem get?_ofList (l : List α) (h : l.length < 2 ^ 64) (n : ℕ) : (ofList l).get? n = l[n]? := by
  rw [ofList, get?_ofListFrom l 0 .nil (by omega)]
  by_cases hn : n < l.length
  · simp [hn]
  · rw [if_neg (by omega), List.getElem?_eq_none (by omega)]; rfl

end NTrie
end Lvm.M3
end
end

section
section
namespace Lvm.M3
open Lvm.Loop

/-- Mark each index of `l` in the bitmask `m`: `none` if one is out of range or repeats. -/
def markAll (N : ℕ) : List ℕ → ℕ → Option ℕ
  | [], m => some m
  | n :: l, m => if n < N ∧ m.testBit n = false then markAll N l (m ||| 1 <<< n) else none

theorem testBit_one_shl (n i : ℕ) : (1 <<< n).testBit i = decide (i = n) := by
  simp only [Nat.one_shiftLeft, Nat.testBit_two_pow, decide_eq_decide]; exact eq_comm

/-- What `markAll` checks: the indices are in range, new, distinct, and the result marks them. -/
theorem markAll_spec (N : ℕ) : ∀ (l : List ℕ) (m m' : ℕ), markAll N l m = some m' →
    l.Nodup ∧ (∀ x ∈ l, m.testBit x = false) ∧ ∀ i, m'.testBit i = (m.testBit i || decide (i ∈ l))
  | [], m, m', h => by simp only [markAll, Option.some.injEq] at h; subst h; simp
  | n :: l, m, m', h => by
    simp only [markAll] at h
    split at h
    · rename_i hc
      obtain ⟨hnd, hnew, hbits⟩ := markAll_spec N l _ m' h
      have hn : n ∉ l := fun hn ↦ by
        have := hnew n hn; simp [Nat.testBit_or, testBit_one_shl] at this
      refine ⟨List.nodup_cons.mpr ⟨hn, hnd⟩, fun x hx ↦ ?_, fun i ↦ ?_⟩
      · rcases List.mem_cons.mp hx with rfl | hx
        · exact hc.2
        · have := hnew x hx; simp only [Nat.testBit_or, Bool.or_eq_false_iff] at this; exact this.1
      · rw [hbits i, Nat.testBit_or, testBit_one_shl]
        by_cases hi : i = n <;> simp [hi]
    · simp at h

/-- **A permutation of `0, …, N − 1`, by bitmask**: marking every index of `l` from `0` gives
`2^N − 1` exactly when `l` lists each index below `N` once. -/
theorem nodup_mem_of_markAll {N : ℕ} {l : List ℕ} (h : markAll N l 0 = some (2 ^ N - 1)) :
    l.Nodup ∧ ∀ n < N, n ∈ l := by
  obtain ⟨hnd, -, hbits⟩ := markAll_spec N l 0 _ h
  refine ⟨hnd, fun n hn ↦ ?_⟩
  have := hbits n
  rw [Nat.testBit_two_pow_sub_one, Nat.zero_testBit, Bool.false_or] at this
  simpa [hn] using this

/-- What the groups' check needs of a piece: its shape and log-height. -/
def pinfo (Q : Program) (p : Piece) : Loop.Shape × ℕ := (p.shape, Q.height p)

/-- **The groups' check on the pieces' shapes and log-heights** `info` (one entry per piece): each
group's members tile `[0, 2^τ)` in list order, each a piece of the group's shape at an offset its
height divides; the members' piece indices mark every piece once (`markAll`, a bitmask). Lookups
go through a trie (`NTrie`, `O(log n)`): list lookups and an insertion sort cost the kernel tens of
seconds at ~700 pieces. -/
def grpOkCore (info : List (Loop.Shape × ℕ)) (groups : List Grp) : Bool :=
  let tr := NTrie.ofList info
  groups.all (fun g ↦ tilesB (·.2) (fun m ↦ 2 ^ ((tr.get? m.1).getD default).2) g.mem 0 (2 ^ g.τ) &&
    g.mem.all fun m ↦ match tr.get? m.1 with
      | some sh => decide (sh.1 = g.σ) && m.2 % 2 ^ sh.2 == 0
      | none => false) &&
  decide (info.length < 2 ^ 64) &&
  markAll info.length (groups.flatMap fun g ↦ g.mem.map (·.1)) 0 == some (2 ^ info.length - 1)

/-- **The groups' Boolean check** of a program. For a large program, decide
`Q.pieces.map (pinfo Q) = info` once (the cost of `Q.pieces` in the kernel) and `grpOkCore info
groups` on literals (`grpOk_of_core`). -/
def grpOkB (Q : Program) (groups : List Grp) : Bool := grpOkCore (Q.pieces.map (pinfo Q)) groups

/-- The member `m`'s height. -/
def memSize (Q : Program) (m : ℕ × ℕ) : ℕ := 2 ^ Q.height (Q.pieces.getD m.1 default)

theorem holds_iff (Q : Program) (m : ℕ × ℕ) (y : ℕ) :
    Grp.Holds Q m y = true ↔ m.2 ≤ y ∧ y < m.2 + memSize Q m := by
  simp [Grp.Holds, memSize]

theorem memSize_eq (Q : Program) {m : ℕ × ℕ} (h : m.1 < Q.pieces.length) :
    2 ^ (((Q.pieces.map (pinfo Q))[m.1]?).getD default).2 = memSize Q m := by
  simp [memSize, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h, pinfo]

/-- **The groups' check gives `GrpOk`.** -/
theorem grpOk_of_B {Q : Program} {groups : List Grp} (h : grpOkB Q groups = true) :
    GrpOk Q groups := by
  simp only [grpOkB, grpOkCore, Bool.and_eq_true, List.all_eq_true, beq_iff_eq,
    decide_eq_true_eq, List.length_map] at h
  obtain ⟨⟨hg1, hlen⟩, hmark⟩ := h
  have hget : ∀ n, (NTrie.ofList (Q.pieces.map (pinfo Q))).get? n = (Q.pieces.map (pinfo Q))[n]? :=
    fun n ↦ NTrie.get?_ofList _ (by simpa using hlen) n
  simp only [hget] at hg1
  have hg0 := hg1
  have hg : ∀ g ∈ groups, tilesB (·.2) (memSize Q) g.mem 0 (2 ^ g.τ) = true ∧
      ∀ m ∈ g.mem, (match (Q.pieces.map (pinfo Q))[m.1]? with
        | some sh => decide (sh.1 = g.σ) && m.2 % 2 ^ sh.2 == 0
        | none => false) = true := by
    intro g hgm
    obtain ⟨ht, hall⟩ := hg0 g hgm
    refine ⟨?_, hall⟩
    rw [← ht]
    refine (tilesB_congr fun m hm ↦ (memSize_eq Q ?_).symm)
    have := hall m hm
    rcases Nat.lt_or_ge m.1 Q.pieces.length with h | h
    · exact h
    · rw [List.getElem?_eq_none (by simpa using h)] at this; simp at this
  obtain ⟨hnd, hall'⟩ := nodup_mem_of_markAll hmark
  refine ⟨fun g hgm m hm ↦ ?_, fun g hgm m hm m' hm' y h1 h2 ↦ ?_, fun g hgm y hy ↦ ?_,
    fun n hn ↦ ?_, fun i i' hi hi' n off off' h1 h2 ↦ ?_, fun g hgm ↦ ?_⟩
  · obtain ⟨ht, hall⟩ := hg g hgm
    have hmm := hall m hm
    rw [List.getElem?_map] at hmm
    cases hp : Q.pieces[m.1]? with
    | none => simp [hp] at hmm
    | some p =>
      simp only [hp, Option.map_some, pinfo, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at hmm
      have hpd : Q.pieces.getD m.1 default = p := by simp [List.getD_eq_getElem?_getD, hp]
      have hin := (tiles_mem ht m hm).2
      simp only [memSize, hpd] at hin
      exact ⟨p, rfl, hmm.1, hin, Nat.dvd_of_mod_eq_zero hmm.2⟩
  · obtain ⟨ht, -⟩ := hg g hgm
    exact tiles_unique ht hm hm' ((holds_iff Q m y).mp h1) ((holds_iff Q m' y).mp h2)
  · obtain ⟨ht, -⟩ := hg g hgm
    obtain ⟨m, hm, hy'⟩ := tiles_cover ht y (Nat.zero_le _) hy
    exact ⟨m, hm, (holds_iff Q m y).mpr hy'⟩
  · have hmem : n ∈ groups.flatMap fun g ↦ g.mem.map (·.1) := hall' n hn
    obtain ⟨g, hgm, hn'⟩ := List.mem_flatMap.mp hmem
    obtain ⟨m, hm, rfl⟩ := List.mem_map.mp hn'
    obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hgm
    exact ⟨i, hi, m.2, hm⟩
  · -- one place: the piece index appears once in the concatenation
    have hpw := (List.nodup_flatMap.mp hnd).2
    rcases Nat.lt_trichotomy i i' with hlt | rfl | hlt
    · have hd := List.pairwise_iff_getElem.mp hpw i i' hi hi' hlt
      exact absurd (List.mem_map_of_mem (f := (·.1)) h2) (hd (List.mem_map_of_mem (f := (·.1)) h1))
    · refine ⟨rfl, ?_⟩
      have hnd1 := (List.nodup_flatMap.mp hnd).1 _ (List.getElem_mem hi)
      obtain ⟨k, hk, hke⟩ := List.getElem_of_mem h1
      obtain ⟨k', hk', hke'⟩ := List.getElem_of_mem h2
      have hkk : k = k' := by
        have e1 : (groups[i].mem.map (·.1))[k]'(by simpa using hk) = n := by simp [hke]
        have e2 : (groups[i].mem.map (·.1))[k']'(by simpa using hk') = n := by simp [hke']
        exact (List.Nodup.getElem_inj_iff hnd1).mp (e1.trans e2.symm)
      subst hkk
      have := hke.symm.trans hke'
      simp only [Prod.mk.injEq] at this
      exact this.2
    · have hd := List.pairwise_iff_getElem.mp hpw i' i hi' hi hlt
      exact absurd (List.mem_map_of_mem (f := (·.1)) h1) (hd (List.mem_map_of_mem (f := (·.1)) h2))
  · -- members strictly increase in offset (each block has at least one row)
    obtain ⟨ht, -⟩ := hg g hgm
    exact (tiles_pairwise ht).imp fun {m m'} hle heq ↦ by
      subst heq; have : 0 < memSize Q m := Nat.two_pow_pos _; omega

/-- **The groups' check on literals**: the pieces' information, decided once, and the check on it. -/
theorem grpOk_of_core {Q : Program} {groups : List Grp} {info : List (Loop.Shape × ℕ)}
    (hinfo : Q.pieces.map (pinfo Q) = info) (h : grpOkCore info groups = true) : GrpOk Q groups :=
  grpOk_of_B (by rw [grpOkB, hinfo]; exact h)

end Lvm.M3
end
end

section
section
namespace Lvm.M3
open Lvm.Loop

theorem counts_of_B {tabs : List Tab} (h : tabsOkB tabs = true) : ∀ t ∈ tabs, ∀ r ∈ t.reads, r.2 < t.w := by
  intro t ht r hr
  simp only [tabsOkB, List.all_eq_true, Bool.and_eq_true, decide_eq_true_eq] at h
  exact (h t ht).1.1.2 r hr

end Lvm.M3
end
end

section
set_option autoImplicit false
namespace Lvm.VEq
open Lvm.M3 LeanVM.Protocol

theorem layOf_P20 : layOf P20 = ⟨23, 19⟩ := rfl

end Lvm.VEq
end

section
set_option autoImplicit false
namespace Lvm.VEq
open Lvm.M3 LeanVM.Protocol
section Fit
variable (p : Params) (tabs : List Tab)
variable {p tabs}

/-- Every sumcheck table reads or seeds (WP-9b's `AllSc`). -/
theorem Fit.allSc (F : Fit p tabs) : AllSc (sumcheckTabs tabs) := by
  intro t ht
  have hf := (List.mem_filter.mp ht).2
  rcases F.hcon t (mem_sumcheckTabs ht) with h | h
  · simp only [Bool.or_eq_true, Bool.not_eq_true', List.isEmpty_eq_false_iff, h] at hf
    simpa using hf
  · exact h

/-- `inst_conditions`'s hypothesis on the sumcheck tables. -/
theorem Fit.hcon' (F : Fit p tabs) :
    ∀ t ∈ sumcheckTabs tabs, t.cons ≠ [] → t.reads ≠ [] ∨ t.seeds ≠ [] :=
  fun t ht _ ↦ F.allSc t ht

/-- **The bus depth** of the lvm instance on the sumcheck tables is the record's. -/
theorem Fit.μBus_eq (F : Fit p tabs) (hτ : ∀ t ∈ sumcheckTabs tabs, t.τ ≤ (layOf p).μ) :
    (inst (layOf p) (sumcheckTabs tabs) hτ).μBus = p.busDepth := by
  rw [M3Instance.μBus, pushLeaves_inst, F.busDepth, log2Ceil_eq_clog]
  rfl

end Fit
end Lvm.VEq
end

section
set_option autoImplicit false
namespace Lvm.VEq
open Lvm.M3 LeanVM.Protocol
section Fit
variable (p : Params) (tabs : List Tab)
variable {p tabs}

/-- **`μBus` at `P20`** (WP-14's request): the bus depth of `midS`'s tables. -/
theorem μBus_P20 (h : fitsR P20 tabs = true) (hτ : ∀ t ∈ sumcheckTabs tabs, t.τ ≤ (⟨23, 19⟩ : Lay).μ) :
    (inst ⟨23, 19⟩ (sumcheckTabs tabs) hτ).μBus = P20.busDepth :=
  (fit_of P20 tabs h).μBus_eq hτ

end Fit
end Lvm.VEq
end

-- ===== from `LvmCertSMid3` =====

section
section
namespace Lvm.Acc
open LeanVM.Parameters LeanVM.Protocol LeanVM.Protocol.Compile LeanVM.Protocol.EndToEnd.Front
open LeanVM.Protocol.KeccakGkr CompPoly CMlPolynomialEval
open Lvm.M3 (Tab sumcheckTabs vTables vLayout busResV Lay inst colOfL TablePostC lvmBusTableProg
  NoCG cg_ret cg_sample cg_readScalar cg_require cg_readScalars cg_sampleChallenges cg_lvmBusProg
  cg_tablePhaseClaims MidTablePost CandIdx candIdx candSet oraOf publicLines_lvm auxAt_lvm
  CommittedHolds BlockHolds stackOf lay26 holds_of_committed committedHolds_iff_block)
open scoped ENNReal

/-- **V_S phases 2–3b commit nothing and ask no proof of work.** -/
theorem noCG_lbusTableAccProg (P : Params) (tabs : Pub → List Tab) (pub : Pub) (μ : ℕ) :
    NoCG (lbusTableAccProg P tabs pub μ) :=
  Lvm.M3.NoCG.bind (Lvm.M3.NoCG.bind (cg_lvmBusProg μ) fun _ ↦ cg_tablePhaseClaims _ _ _) fun _ ↦
    Lvm.M3.NoCG.bind (cg_accProg _ _ _ _ _ _ _ _) fun _ ↦ cg_ret _

end Lvm.Acc
end
end

section
section
namespace Lvm.Acc
open LeanVM.Parameters LeanVM.Protocol LeanVM.Protocol.Compile LeanVM.Protocol.EndToEnd.Front
open LeanVM.Protocol.KeccakGkr CompPoly CMlPolynomialEval
open Lvm.M3 (Tab sumcheckTabs vTables vLayout busResV Lay inst colOfL TablePostC lvmBusTableProg
  NoCG cg_ret cg_sample cg_readScalar cg_require cg_readScalars cg_sampleChallenges cg_lvmBusProg
  cg_tablePhaseClaims MidTablePost CandIdx candIdx candSet oraOf publicLines_lvm auxAt_lvm
  CommittedHolds BlockHolds stackOf lay26 holds_of_committed committedHolds_iff_block)
open scoped ENNReal
section Mid
variable (L : Lay) (P : Params) (tabs : Pub → List Tab) (pub : Pub)
  (hτL : ∀ t ∈ sumcheckTabs (tabs pub), t.τ ≤ L.μ) (hsc : Lvm.M3.AllSc (sumcheckTabs (tabs pub)))
  {β : Type} (C : List Ev → Set β) (stk : β → Column L.μ) (R : β → Prop) {L₀ : ℕ} {εmax : ℝ≥0∞}

/-- **Phases 2–3b with a post on the claims alone** (WP-9b's `midBusTableSpec'`). -/
noncomputable def midBusTableAccSpec' (H : AccInst P (sumcheckTabs (tabs pub)) pub)
    (hkey : Lvm.M3.KeysOk (sumcheckTabs (tabs pub))) (hw : ∀ t ∈ sumcheckTabs (tabs pub), 0 < t.w)
    (G : List Ev → Prop) (hCG : ∀ h₀ l, G h₀ → C (h₀ ++ l) = C h₀)
    (hf : ∀ h, (C h).Finite) (hc : ∀ h, (C h).ncard ≤ L₀)
    (hμ : (inst L (sumcheckTabs (tabs pub)) hτL).μBus ≠ 0)
    (hab : abError (inst L (sumcheckTabs (tabs pub)) hτL) L₀ < 1)
    (he4 : roundError L₀ 4 ≤ εmax) (hT : interpLead L₀ 2 (lambdaError L₀) ≤ εmax)
    (hlam : lambdaError L₀ + 0 ≤ εmax) {T : ℝ≥0∞}
    (he3 : roundError L₀ 3 + max (P.accLog * errE 1) T ≤ εmax)
    (hTa : max (P.accLog * errE 1) T ≤ εmax)
    (hxi : xiError (inst L (sumcheckTabs (tabs pub)) hτL) L₀ +
      sumcheckLead (List.replicate ((vLayout (sumcheckTabs (tabs pub))).tableLogHeights.foldl max 0) none)
        (max (P.accLog * errE 1) T) ≤ εmax)
    (hD : errE accVars ≤ εmax) (hTf : T ≤ εmax) :
    Spec (lbusTableAccProg P tabs pub (inst L (sumcheckTabs (tabs pub)) hτL).μBus)
      (fun h ↦ G h ∧ (∃ W, firstWord h = some W) ∧
        Doomed C (fun p ↦ M3Holds (inst L (sumcheckTabs (tabs pub)) hτL) () (stk p) ∧ R p ∧
          AccOkE P tabs pub) h)
      (fun cl h ↦ Doomed C (fun p ↦ (∀ c ∈ cl, CommittedHolds L (sumcheckTabs (tabs pub)) hτL (stk p) c) ∧
        R p) h) εmax (abError (inst L (sumcheckTabs (tabs pub)) hτL) L₀ + 0) T :=
  (midBusTableAccSpec L P tabs pub hτL hsc C stk R H hkey hw G hCG hf hc hμ hab he4 hT hlam he3 hTa
    hxi hD hTf).mono (fun _ h ↦ h)
    (fun cl h ⟨tout, hDm, hmem, _⟩ p hp ⟨hall, hR⟩ ↦
      hDm p hp ⟨holds_of_committed L _ hτL hmem hall, hR⟩) le_rfl le_rfl le_rfl

end Mid
end Lvm.Acc
end
end

section
section
namespace Lvm.Acc
open LeanVM.Parameters LeanVM.Protocol LeanVM.Protocol.Compile LeanVM.Protocol.EndToEnd.Front
open LeanVM.Protocol.KeccakGkr CompPoly CMlPolynomialEval
open Lvm.M3 (Tab sumcheckTabs vTables vLayout busResV Lay inst colOfL TablePostC lvmBusTableProg
  NoCG cg_ret cg_sample cg_readScalar cg_require cg_readScalars cg_sampleChallenges cg_lvmBusProg
  cg_tablePhaseClaims MidTablePost CandIdx candIdx candSet oraOf publicLines_lvm auxAt_lvm
  CommittedHolds BlockHolds stackOf lay26 holds_of_committed committedHolds_iff_block)
open scoped ENNReal
section Blocks
variable (L : Lay) (P : Params) (tabs : Pub → List Tab) (pub : Pub)
  (hτL : ∀ t ∈ sumcheckTabs (tabs pub), t.τ ≤ L.μ) (hsc : Lvm.M3.AllSc (sumcheckTabs (tabs pub)))
  {L₀ : ℕ} {εmax : ℝ≥0∞}

/-- **Phases 2–3b on the commitments' blocks** (WP-9b's `midBusTableSpecB`). -/
noncomputable def midBusTableAccSpecB (C : List Ev → Set (Column L.nuMain × Column L.nuRec))
    (R : Column L.nuMain × Column L.nuRec → Prop) (hlay : Lvm.M3.LayOk L (sumcheckTabs (tabs pub)))
    (H : AccInst P (sumcheckTabs (tabs pub)) pub)
    (hkey : Lvm.M3.KeysOk (sumcheckTabs (tabs pub))) (hw : ∀ t ∈ sumcheckTabs (tabs pub), 0 < t.w)
    (G : List Ev → Prop) (hCG : ∀ h₀ l, G h₀ → C (h₀ ++ l) = C h₀)
    (hf : ∀ h, (C h).Finite) (hc : ∀ h, (C h).ncard ≤ L₀)
    (hμ : (inst L (sumcheckTabs (tabs pub)) hτL).μBus ≠ 0)
    (hab : abError (inst L (sumcheckTabs (tabs pub)) hτL) L₀ < 1)
    (he4 : roundError L₀ 4 ≤ εmax) (hT : interpLead L₀ 2 (lambdaError L₀) ≤ εmax)
    (hlam : lambdaError L₀ + 0 ≤ εmax) {T : ℝ≥0∞}
    (he3 : roundError L₀ 3 + max (P.accLog * errE 1) T ≤ εmax)
    (hTa : max (P.accLog * errE 1) T ≤ εmax)
    (hxi : xiError (inst L (sumcheckTabs (tabs pub)) hτL) L₀ +
      sumcheckLead (List.replicate ((vLayout (sumcheckTabs (tabs pub))).tableLogHeights.foldl max 0) none)
        (max (P.accLog * errE 1) T) ≤ εmax)
    (hD : errE accVars ≤ εmax) (hTf : T ≤ εmax) :
    Spec (lbusTableAccProg P tabs pub (inst L (sumcheckTabs (tabs pub)) hτL).μBus)
      (fun h ↦ G h ∧ (∃ W, firstWord h = some W) ∧
        Doomed C (fun p ↦ M3Holds (inst L (sumcheckTabs (tabs pub)) hτL) () (stackOf L p.1 p.2) ∧ R p ∧
          AccOkE P tabs pub) h)
      (fun cl h ↦ Doomed C (fun p ↦ (∀ c ∈ cl, BlockHolds L (sumcheckTabs (tabs pub)) p.1 p.2 c) ∧ R p) h)
      εmax (abError (inst L (sumcheckTabs (tabs pub)) hτL) L₀ + 0) T :=
  (midBusTableAccSpec' L P tabs pub hτL hsc C (fun p ↦ stackOf L p.1 p.2) R H hkey hw G hCG hf hc hμ
    hab he4 hT hlam he3 hTa hxi hD hTf).mono (fun _ h ↦ h)
    (fun cl h hDm p hp ⟨hall, hR⟩ ↦ hDm p hp ⟨fun c hc ↦
      (committedHolds_iff_block L _ hτL hlay p.1 p.2 c).mpr (hall c hc), hR⟩) le_rfl le_rfl le_rfl

end Blocks
end Lvm.Acc
end
end

section
section
namespace Lvm.Acc
open LeanVM.Parameters LeanVM.Protocol LeanVM.Protocol.Compile LeanVM.Protocol.EndToEnd.Front
open LeanVM.Protocol.KeccakGkr CompPoly CMlPolynomialEval
open Lvm.M3 (Tab sumcheckTabs vTables vLayout busResV Lay inst colOfL TablePostC lvmBusTableProg
  NoCG cg_ret cg_sample cg_readScalar cg_require cg_readScalars cg_sampleChallenges cg_lvmBusProg
  cg_tablePhaseClaims MidTablePost CandIdx candIdx candSet oraOf publicLines_lvm auxAt_lvm
  CommittedHolds BlockHolds stackOf lay26 holds_of_committed committedHolds_iff_block)
open scoped ENNReal
section Pairs
variable (P : Params) (tabs : Pub → List Tab) (pub : Pub)
  (hτL : ∀ t ∈ sumcheckTabs (tabs pub), t.τ ≤ lay26.μ) {L₀ : ℕ} {εmax : ℝ≥0∞}

/-- **V_S phases 2–3b on WP-14's candidate pairs** (WP-9b's `midBusTableSpecS` with phase 3b in place
of the fixed-column check, BLUEPRINT §12.6): from `RootShape` and the root doom of
`M3Holds ∘ stackOf ∧ R ∧ AccOk acc_in` to the doom of the returned claims on the pairs' blocks, with
`R`, and `RootShape`. `AccOk acc_in` is discharged: it is not in the post. -/
noncomputable def midBusTableAccSpecS (R : Column CMain.nu20 × Column 19 → Prop)
    (hlay : Lvm.M3.LayOk lay26 (sumcheckTabs (tabs pub))) (hsc : Lvm.M3.AllSc (sumcheckTabs (tabs pub)))
    (H : AccInst P (sumcheckTabs (tabs pub)) pub)
    (hkey : Lvm.M3.KeysOk (sumcheckTabs (tabs pub))) (hw : ∀ t ∈ sumcheckTabs (tabs pub), 0 < t.w)
    (hc : ∀ h, (Lvm.ASM.candPairs h).ncard ≤ L₀)
    (hμ : (inst lay26 (sumcheckTabs (tabs pub)) hτL).μBus ≠ 0)
    (hab : abError (inst lay26 (sumcheckTabs (tabs pub)) hτL) L₀ < 1)
    (he4 : roundError L₀ 4 ≤ εmax) (hT : interpLead L₀ 2 (lambdaError L₀) ≤ εmax)
    (hlam : lambdaError L₀ + 0 ≤ εmax) {T : ℝ≥0∞}
    (he3 : roundError L₀ 3 + max (P.accLog * errE 1) T ≤ εmax)
    (hTa : max (P.accLog * errE 1) T ≤ εmax)
    (hxi : xiError (inst lay26 (sumcheckTabs (tabs pub)) hτL) L₀ +
      sumcheckLead (List.replicate ((vLayout (sumcheckTabs (tabs pub))).tableLogHeights.foldl max 0) none)
        (max (P.accLog * errE 1) T) ≤ εmax)
    (hD : errE accVars ≤ εmax) (hTf : T ≤ εmax) :
    Spec (lbusTableAccProg P tabs pub (inst lay26 (sumcheckTabs (tabs pub)) hτL).μBus)
      (fun h ↦ Lvm.ASM.RootShape h ∧ Doomed Lvm.ASM.candPairs
        (fun p ↦ M3Holds (inst lay26 (sumcheckTabs (tabs pub)) hτL) () (stackOf lay26 p.1 p.2) ∧ R p ∧
          AccOkE P tabs pub) h)
      (fun cl h ↦ Doomed Lvm.ASM.candPairs
        (fun p ↦ (∀ c ∈ cl, BlockHolds lay26 (sumcheckTabs (tabs pub)) p.1 p.2 c) ∧ R p) h ∧
          Lvm.ASM.RootShape h)
      εmax (abError (inst lay26 (sumcheckTabs (tabs pub)) hτL) L₀ + 0) T :=
  ((midBusTableAccSpecB lay26 P tabs pub hτL hsc Lvm.ASM.candPairs R hlay H hkey hw
      (fun h ↦ 2 ≤ (commits h).length) (fun h₀ l h2 ↦ Lvm.M3.candPairs_append h₀ l h2)
      (fun _ ↦ Set.toFinite _) hc hμ hab he4 hT hlam he3 hTa hxi hD hTf).frame Lvm.ASM.RootShape
    (fun _ _ hl hr ↦ Lvm.M3.rootShape_append
      ((noCG_lbusTableAccProg P tabs pub _).1.reach_commits hl) hr)).mono
    (fun h ⟨hr, hDm⟩ ↦ ⟨⟨Lvm.M3.rootShape_two hr, Lvm.M3.rootShape_firstWord hr, hDm⟩, hr⟩)
    (fun _ _ h ↦ h) le_rfl le_rfl le_rfl

end Pairs
end Lvm.Acc
end
end

section
section
set_option autoImplicit false
namespace Lvm.ASM
open LeanVM.Parameters LeanVM.Protocol LeanVM.Protocol.Compile LeanVM.Protocol.Verifier
open LeanVM.Protocol.Compile.VerifierProgram LeanVM.Protocol.Whir.Sound LeanVM.Protocol.EndToEnd
open LeanVM.Protocol.EndToEnd.Front (Doomed)
open scoped ENNReal
section Glue
variable {α κ : Type} {busP : List UInt8 → VerifierProgram α} {kgP : VerifierProgram κ}
  {asm : List UInt8 → α → κ → OpenClaims}
  {Gb : List UInt8 → Pair → Prop} {Gk : Pair → Prop} {B : List UInt8 → α → Pair → Prop}
  {Kc : κ → Pair → Prop} {Lb Lk : ℝ≥0∞}

/-- The assembled claims' doom: a pair failing `Kc ∧ B` fails one of the assembled claims. -/
theorem openPost_of {x : List UInt8} {a : α} {k : κ} {h : List Ev}
    (hasm : ∀ p : Pair, (∀ c ∈ (asm x a k).1, StackClaim.Holds 19 c p.2) →
      (∀ c ∈ (asm x a k).2, StackClaim.Holds CMain.nu20 c p.1) → Kc k p ∧ B x a p)
    (hside : (∀ c ∈ (asm x a k).1, IsMultiaffine 19 c.1) ∧ (∀ c ∈ (asm x a k).2, IsMultiaffine CMain.nu20 c.1) ∧
      (asm x a k).1.length ≤ 2 ^ 63 ∧ (asm x a k).2.length ≤ 2 ^ 40)
    (hD : Doomed candPairs (fun p ↦ Kc k p ∧ B x a p) h) (hR : RootShape h) :
    OpenPost (asm x a k) h := by
  refine ⟨fun p hp ↦ ?_, hR, hside⟩
  by_contra hno
  push Not at hno
  exact hD p hp (hasm p hno.1 hno.2)

/-- **`MidSpec` from the phases** (see the module docstring). -/
noncomputable def midSpecOf
    (SB : ∀ x (T : ℝ≥0∞), T ≤ εS → Spec (busP x)
      (fun h ↦ RootShape h ∧ Doomed candPairs (fun p ↦ Gb x p ∧ Gk p) h)
      (fun a h ↦ Doomed candPairs (fun p ↦ B x a p ∧ Gk p) h ∧ RootShape h) εS Lb T)
    (SK : ∀ x a (T : ℝ≥0∞), T ≤ εS → Spec kgP (Doomed candPairs (fun p ↦ Gk p ∧ B x a p))
      (fun k h ↦ Doomed candPairs (fun p ↦ Kc k p ∧ B x a p) h) εS Lk T)
    (hkc : kgP.NoCommit) (hLk : Lk ≤ εS)
    (hasm : ∀ x a k (p : Pair), (∀ c ∈ (asm x a k).1, StackClaim.Holds 19 c p.2) →
      (∀ c ∈ (asm x a k).2, StackClaim.Holds CMain.nu20 c p.1) → Kc k p ∧ B x a p)
    (hside : ∀ x a k, (∀ c ∈ (asm x a k).1, IsMultiaffine 19 c.1) ∧
      (∀ c ∈ (asm x a k).2, IsMultiaffine CMain.nu20 c.1) ∧ (asm x a k).1.length ≤ 2 ^ 63 ∧
      (asm x a k).2.length ≤ 2 ^ 40) :
    MidSpec (fun x ↦ busP x >>= fun a ↦ kgP >>= fun k ↦ VerifierProgram.ret (asm x a k))
      (fun x qm qr ↦ Gb x (qm, qr) ∧ Gk (qm, qr)) εS Lb := fun x T hT ↦
  ⟨((SB x Lk hLk).bind' fun a ↦
      (((SK x a T hT).frame RootShape fun _ _ hl hr ↦
          rootShape_append' (hkc.reach_commits hl) hr).mono
        (fun h hp ↦ ⟨Doomed.mono hp.1 fun p hq ↦ ⟨hq.2, hq.1⟩, hp.2⟩) (fun _ _ h ↦ h) le_rfl
        le_rfl le_rfl).bind' fun k ↦
      (Spec.ret (Post := OpenPost) (εmax := εS) (T := T) (asm x a k)).mono
        (fun h hp ↦ openPost_of (hasm x a k) (hside x a k) hp.1 hp.2) (fun _ _ h ↦ h) le_rfl
        le_rfl le_rfl).mono
    (fun h hp ↦ ⟨hp.2, hp.1⟩) (fun _ _ h ↦ h) le_rfl le_rfl le_rfl⟩

/-- **`MidShape` of the composed phases.** -/
theorem midShapeOf (hbc : ∀ x, (busP x).NoCommit) (hbg : ∀ x, (busP x).NoGrind)
    (hkc : kgP.NoCommit) (hkg : kgP.NoGrind)
    (hret : ∀ x l cl, (busP x >>= fun a ↦ kgP >>= fun k ↦ VerifierProgram.ret (asm x a k)).after l =
      some (.ret cl) → ∀ c ∈ cl.1, IsMultiaffine 19 c.1) :
    MidShape (fun x ↦ busP x >>= fun a ↦ kgP >>= fun k ↦ VerifierProgram.ret (asm x a k)) where
  noCommit x := NoCommit.bind (hbc x) fun _ ↦ NoCommit.bind hkc fun _ ↦ trivial
  noGrind x := NoGrind.bind (hbg x) fun _ ↦ NoGrind.bind hkg fun _ ↦ trivial
  recAffine := hret

/-- The returned claims of the composed phases are the assembled ones. -/
theorem ret_assembled {x : List UInt8} {l : List Ev} {cl : OpenClaims}
    (h : (busP x >>= fun a ↦ kgP >>= fun k ↦ VerifierProgram.ret (asm x a k)).after l =
      some (.ret cl)) : ∃ a k, cl = asm x a k := by
  obtain ⟨a, -, l₂, -, -, h2⟩ := after_bind_ret (p := busP x) h
  obtain ⟨k, -, l₃, -, -, h3⟩ := after_bind_ret (p := kgP) h2
  cases l₃ with
  | nil => simp [VerifierProgram.after] at h3; exact ⟨a, k, h3.symm⟩
  | cons e es => cases e <;> simp [VerifierProgram.after] at h3

end Glue
end Lvm.ASM
end
end

section
section
set_option autoImplicit false
namespace Lvm.ASM
open LeanVM.Parameters LeanVM.Protocol LeanVM.Protocol.Compile LeanVM.Protocol.Verifier
open LeanVM.Protocol.Compile.VerifierProgram LeanVM.Protocol.KeccakGkr
open LeanVM.Protocol.Whir.Sound LeanVM.Protocol.EndToEnd
open Lvm.M3 (NoCG cg_ret cg_sample cg_readScalar cg_require cg_readScalars cg_sampleChallenges
  cg_roundPoly cg_sumcheck noCG_lbusTableCheckProg)
open scoped ENNReal

theorem cg_ite {α : Type} {c : Prop} [Decidable c] {p q : VerifierProgram α} (hp : NoCG p)
    (hq : NoCG q) : NoCG (if c then p else q) := by
  split <;> assumption

end Lvm.ASM
end
end

section
section
set_option autoImplicit false
namespace Lvm.ASM
open LeanVM.Parameters LeanVM.Protocol LeanVM.Protocol.Compile LeanVM.Protocol.Verifier
open LeanVM.Protocol.Compile.VerifierProgram LeanVM.Protocol.KeccakGkr
open LeanVM.Protocol.Whir.Sound LeanVM.Protocol.EndToEnd
open Lvm.M3 (NoCG cg_ret cg_sample cg_readScalar cg_require cg_readScalars cg_sampleChallenges
  cg_roundPoly cg_sumcheck noCG_lbusTableCheckProg)
open scoped ENNReal

theorem sum6 : (∑ _i ∈ Finset.range 6, ((1 : ℕ) : ℝ≥0∞) * errE 1) = errE 6 := by
  rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul, Nat.cast_one, one_mul,
    show ((6 : ℕ) : ℝ≥0∞) = (6 : ℝ≥0∞) from rfl, ← Nat.cast_ofNat, errE_smul]

end Lvm.ASM
end
end

section
section
set_option autoImplicit false
namespace Lvm.ASM
open LeanVM.Parameters LeanVM.Protocol LeanVM.Protocol.Compile LeanVM.Protocol.Verifier
open LeanVM.Protocol.Compile.VerifierProgram LeanVM.Protocol.KeccakGkr
open LeanVM.Protocol.Whir.Sound LeanVM.Protocol.EndToEnd
open Lvm.M3 (NoCG cg_ret cg_sample cg_readScalar cg_require cg_readScalars cg_sampleChallenges
  cg_roundPoly cg_sumcheck noCG_lbusTableCheckProg)
open scoped ENNReal

theorem midSpec_congr {mid : List UInt8 → VerifierProgram OpenClaims} {G G' : GoodRel}
    (hG : ∀ x qm qr, G x qm qr ↔ G' x qm qr) {εm Lm : ℝ≥0∞} (h : MidSpec mid G εm Lm) :
    MidSpec mid G' εm Lm := by
  have e : G = G' := funext fun x ↦ funext fun qm ↦ funext fun qr ↦ propext (hG x qm qr)
  exact e ▸ h

end Lvm.ASM
end
end

section
section
set_option autoImplicit false
namespace Lvm.ASM
open LeanVM.Parameters LeanVM.Protocol LeanVM.Protocol.Verifier LeanVM.Protocol.EndToEnd
open LeanVM.Protocol.EndToEnd.Front LeanVM.Protocol.KeccakGkr LeanVM.Protocol.Whir.Sound
open LeanVM.Protocol.EndToEnd.Sound (RetOK)
open Lvm.VEq Finset
open Lvm.NS (colM ksCol ksY2 msgM msgX)

/-- A commitment's cell is its word's entry, `0` past it. -/
theorem comCell_lay26 (qm : Column CMain.nu20) (qr : Column 19) (rec : Bool) (n : ℕ) :
    Lvm.M3.comCell Lvm.M3.lay26 qm qr rec n =
      if rec then qr.values.getD n 0 else qm.values.getD n 0 := by
  cases rec <;> simp only [Lvm.M3.comCell, Vector.getD, Array.getD, Vector.size_toArray,
    Bool.false_eq_true, ↓reduceIte] <;> rfl

open CompPoly CMlPolynomialEval in
/-- A block's extension at a point of its height is the `eqAt`-weighted sum of its cells. -/
theorem eval_comBlock_sum (qm : Column CMain.nu20) (qr : Column 19) (rec : Bool) (τ off : ℕ) (z : List E)
    (hz : z.length = τ) :
    eval₂Mle (Lvm.M3.comBlock Lvm.M3.lay26 qm qr rec τ off).values (algebraMap K E) (vecOf τ z) =
      ∑ n ∈ range (2 ^ τ), eqAt z n * ofK (Lvm.M3.comCell Lvm.M3.lay26 qm qr rec (off + n)) := by
  subst hz
  rw [← sum_eqEval_mul, toList_vecOf z rfl]
  rw [Fin.sum_univ_eq_sum_range (fun x => LeanVM.Protocol.Verifier.eqEval z (boolPoint z.length x) *
    ofK ((Lvm.M3.comBlock Lvm.M3.lay26 qm qr rec z.length off).values.getD x 0))]
  refine sum_congr rfl fun n hn => ?_
  rw [eqEval_boolPoint_eqAt]
  have hn' := mem_range.mp hn
  simp [Lvm.M3.comBlock, Vector.getD, hn']

/-- **The table claims' link**: `tableClaimsE` holding on the commitments gives `BlockHolds`. -/
theorem blockHolds_of_tableClaims {T : List Lvm.M3.Tab} (hlay : Lvm.M3.LayOk Lvm.M3.lay26 T)
    {cl : List ColumnClaim} (hret : TabRet T cl) {qm : Column CMain.nu20} {qr : Column 19}
    (h : ∀ e ∈ tableClaimsE T cl, HoldsC qm qr e) :
    ∀ c ∈ cl, Lvm.M3.BlockHolds Lvm.M3.lay26 T qm qr c := by
  intro c hc j i hj rec off hloc hcol
  have hi : i < (T.get ⟨j, hj⟩).w := (List.getElem?_eq_some_iff.mp hcol).1
  have hal := hlay (T.get ⟨j, hj⟩) (List.get_mem _ _) i hi
  unfold Lvm.M3.Aligned at hal
  rw [hcol] at hal
  obtain ⟨hdvd, hfit, -⟩ := hal
  have hτ : (T[j]?.map (·.τ)).getD 0 = (T.get ⟨j, hj⟩).τ := by simp [List.getElem?_eq_getElem hj]
  have hz : c.point.length = (T.get ⟨j, hj⟩).τ := (hret.1 c hc j i hloc).trans hτ
  have hmem : (if rec then Com.crec else Com.main,
      BClaim.point ⟨(T.get ⟨j, hj⟩).τ, off⟩ c.point c.value) ∈ tableClaimsE T cl := by
    unfold tableClaimsE
    refine List.mem_filterMap.mpr ⟨c, hc, ?_⟩
    rw [hloc]
    have hcol' : T[j].cols[i]? = some (.com rec off) := hcol
    simp only [Option.bind_some, List.getElem?_eq_getElem hj, hcol']
    rfl
  have hh := h _ hmem
  rw [eval_comBlock_sum qm qr rec _ off c.point hz]
  simp only [comCell_lay26]
  cases rec
  · exact (holds_point hdvd hfit c.point hz c.value qm).mp hh
  · exact (holds_point hdvd hfit c.point hz c.value qr).mp hh

end Lvm.ASM
end
end

section
section
set_option autoImplicit false
namespace Lvm.ASM
open LeanVM.Parameters LeanVM.Protocol LeanVM.Protocol.Verifier LeanVM.Protocol.EndToEnd
open LeanVM.Protocol.EndToEnd.Front LeanVM.Protocol.KeccakGkr LeanVM.Protocol.Whir.Sound
open LeanVM.Protocol.EndToEnd.Sound (RetOK)
open Lvm.VEq Finset
open Lvm.NS (colM dD ksCol ksY2 msgM msgX)
namespace Kec

/-- A column claim on a block. -/
theorem colTrue_of_holds {μ h off : ℕ} (hal : 2 ^ (h + 6) ∣ off)
    (hfit : off + 2 ^ (h + 6) ≤ 2 ^ μ) {q : Column μ} {c : ColumnClaim}
    (hc : c.column = qkeccak ∧ c.point.length = h + 6)
    (H : StackClaim.Holds μ (BClaim.point ⟨h + 6, off⟩ c.point c.value).onStack q) :
    colTrue h (fun n ↦ q.values.getD (off + n) 0) c :=
  ⟨hc.1, hc.2, ((holds_point hal hfit _ hc.2 _ q).1 H).symm⟩

end Kec
end Lvm.ASM
end
end

section
section
set_option autoImplicit false
namespace Lvm.ASM
open LeanVM.Parameters LeanVM.Protocol LeanVM.Protocol.Verifier LeanVM.Protocol.EndToEnd
open LeanVM.Protocol.EndToEnd.Front LeanVM.Protocol.KeccakGkr LeanVM.Protocol.Whir.Sound
open LeanVM.Protocol.EndToEnd.Sound (RetOK)
open Lvm.VEq Finset
open Lvm.NS (colM dD ksCol ksY2 msgM msgX)
namespace Kec

/-- `pad43`'s lanes are `pad43Lane`'s. -/
theorem pad43_getD (d : List FK) {l : ℕ} (hl : l < 25) :
    ((pad43 d).getD l 0).val = Lvm.KG.pad43Lane (fun m ↦ (d.getD m 0).val) l := by
  interval_cases l <;> rfl

/-- `pad43Lane` reads only lanes `0 … 3`. -/
theorem pad43Lane_congr {w w' : ℕ → UInt64} (h : ∀ m < 4, w m = w' m) (l : ℕ) :
    Lvm.KG.pad43Lane w l = Lvm.KG.pad43Lane w' l := by
  by_cases h0 : l = 0
  · simp only [Lvm.KG.pad43Lane, h0, ite_true, h 0 (by norm_num)]
  by_cases h4 : l < 4
  · simp only [Lvm.KG.pad43Lane, h0, h4, ite_true, ite_false, h l h4, h (l - 1) (by (clear * - h4; omega))]
  · simp only [Lvm.KG.pad43Lane, h0, h4, ite_false, h 3 (by norm_num)]

end Kec
end Lvm.ASM
end
end

section
section
set_option autoImplicit false
namespace Lvm.ASM
open LeanVM.Parameters LeanVM.Protocol LeanVM.Protocol.Verifier LeanVM.Protocol.EndToEnd
open LeanVM.Protocol.EndToEnd.Front LeanVM.Protocol.KeccakGkr LeanVM.Protocol.Whir.Sound
open LeanVM.Protocol.EndToEnd.Sound (RetOK)
open Lvm.VEq Finset
open Lvm.NS (colM dD ksCol ksY2 msgM msgX)
open Kec

/-- **The tape's claims** (lvm2 S2, T1 and T4): the ring claim on the whole `C_main` (`h = 17`: lvm2 roll 8, B1,
ν = 23; roll 7: `h = 18`) and the tied digest lanes `D̃_l(r) = a_l` on `D`'s slots 0–3. -/
theorem tapeClaims_of (tp : Lvm.KG.TapeOutE) (hr : tp.1.length = 20) (pub : Lvm.Pub) {qm : Column CMain.nu20}
    (h : ∀ b ∈ tapeClaimsE tp pub, StackClaim.Holds CMain.nu20 b.onStack qm) :
    Lvm.KG.RingColTrue 17 (colM qm) tp.2.2.2.d.ring ∧ Lvm.KG.TiedD 20 (dD qm) tp.1 tp.2.1 := by
  have hal : 2 ^ (17 + 6) ∣ 0 := dvd_zero _
  have hfit : 0 + 2 ^ (17 + 6) ≤ 2 ^ 23 := le_of_eq (by norm_num)
  have hal2 : 2 ^ (20 + 2) ∣ 0 := dvd_zero _
  have hfit2 : 0 + 2 ^ (20 + 2) ≤ 2 ^ 23 := by norm_num
  refine ⟨?_, fun l hl ↦ ?_⟩
  · have H := ringCol_of_holds (ring := tp.2.2.2.d.ring) hal hfit
      (h _ (List.mem_append_left _ (List.mem_append_right _ (List.mem_singleton_self _))))
    simp only [zero_add] at H
    exact H
  · have H := holds_split (h := 20) (k := 2) hal2 hfit2 hr (b := l) (by omega)
      (h _ (List.mem_append_left _ (List.mem_append_left _
        (List.mem_map.2 ⟨l, List.mem_range.2 hl, rfl⟩))))
    simp only [zero_add] at H
    simp only [stepMle, dD, Lvm.KG.dOf, colM, Lvm.NS.wd, Nat.mul_zero, Nat.add_zero]
    exact H

/-- **T5's boundary claims** give `BndS` (`D̃_l(bits(n − 1)) = h_l`, the header's `n`, `h`). -/
theorem bndS_of_tape (x : List UInt8) (tp : Lvm.KG.TapeOutE) {qm : Column CMain.nu20}
    (h : ∀ b ∈ tapeClaimsE tp (pubX x), StackClaim.Holds CMain.nu20 b.onStack qm) : BndS x qm := by
  intro hn m hm
  have hal2 : 2 ^ (20 + 2) ∣ 0 := dvd_zero _
  have hfit2 : 0 + 2 ^ (20 + 2) ≤ 2 ^ 23 := by norm_num
  have hN : (pubX x).n = (hdrOf x).n := pubX_n x
  have hH : ∀ m < 4, ((pubX x).h.getD m 0).val =
      RecursionFast.Keccak.blockLane (hdrOf x).h.toArray m := by
    intro m hm
    show (((List.range 4).map fun i ↦ kAt (sigOfX x) (headerAt 120 + 8 * i)).getD m 0).val = _
    rw [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range hm]
    exact lane_hdr x (by norm_num) hm
  have hlenH : (pubX x).h.length = 4 := by simp [pubX, pubOf]
  have hmem : BClaim.point dBlkE (selE ((pubX x).n - 1) 20 ++ selE m 2)
      (M3.kE ((pubX x).h.getD m 0)) ∈ tapeClaimsE tp (pubX x) :=
    List.mem_append_right _ (List.mem_map.2 ⟨_, getD_mem_zipIdx _ (by (clear * - hm hlenH; omega)), rfl⟩)
  have hlt : (pubX x).n - 1 < 2 ^ 20 := by rw [hN]; (clear * - hn hN; omega)
  have H := holds_split (h := 20) (k := 2) hal2 hfit2 (by simp [selE_eq_bitsE]) (b := m)
    (by omega) (h _ hmem)
  rw [selE_eq_bitsE, sum_eqAt_bitsE hlt, zero_add] at H
  have H' := Lvm.KG.ofK_injective H
  rw [hN] at H'
  simp only [dD, Lvm.KG.dOf, colM, Lvm.NS.wd, Nat.mul_zero, Nat.add_zero]
  rw [H', ← hH m hm]
  rfl

/-- **`KS`'s caller claims** (ring, column claims, all 25 output lanes tied; lvm2 roll 8, B1: KS13, `ρ` of
`P20.ksLog = 13` coordinates, the block `2^(13 + 6)` words at `ksOff20`, `KSY2`'s lanes `2^13` words). -/
theorem callerClaims_ks (co : CallerOut) (hr : co.1.length = 13)
    (hcol : ∀ c ∈ co.2.2.1.1, c.column = qkeccak ∧ c.point.length = 19) {qm : Column CMain.nu20}
    {qr : Column 19} (hk : ∀ b ∈ keccakClaimsE ksBlk co, StackClaim.Holds CMain.nu20 b.onStack qm)
    (ho : ∀ e ∈ ksOutputClaimsE co.1 co.2.1, HoldsC qm qr e) :
    Lvm.KG.CallerClaims 13 25 (ksCol qm) (Lvm.KG.ksY 13 ksY2 (colM qm) (ksCol qm)) co := by
  have hal : 2 ^ (13 + 6) ∣ CMain.ksOff20 := ⟨10, by decide⟩
  have hfit : CMain.ksOff20 + 2 ^ (13 + 6) ≤ 2 ^ 23 := by decide
  refine ⟨ringCol_of_holds (ring := co.2.2.2) hal hfit
      (hk _ (List.mem_append_right _ (List.mem_singleton_self _))),
    fun c hc ↦ colTrue_of_holds hal hfit (hcol c hc)
      (hk _ (List.mem_append_left _ (List.mem_map_of_mem hc))), fun l hl ↦ ?_⟩
  have H : StackClaim.Holds CMain.nu20
      (BClaim.point (ksYPartE l co.1).1 (ksYPartE l co.1).2 (co.2.1.getD l 0)).onStack qm :=
    ho _ (List.mem_map.2 ⟨l, List.mem_range.2 hl, rfl⟩)
  unfold stepMle Lvm.KG.ksY
  by_cases h14 : l < 14
  · simp only [ite_eq_left h14]
    have e : ksYPartE l co.1 = (⟨13 + slotLog, CMain.ksOff20⟩, co.1 ++ selE (50 + l) slotLog) :=
      ite_eq_left h14
    rw [e] at H
    exact holds_split (h := 13) (k := 6) hal hfit hr (by (clear * - hl h14; omega)) H
  · simp only [ite_eq_right h14]
    have e : ksYPartE l co.1 = (⟨13, ksY2Off + (l - 14) * 2 ^ 13⟩, co.1) := ite_eq_right h14
    rw [e] at H
    have hal' : 2 ^ 13 ∣ ksY2Off + (l - 14) * 2 ^ 13 :=
      Nat.dvd_add ⟨739, by norm_num [ksY2Off]⟩ (Nat.dvd_mul_left _ _)
    have hfit' : ksY2Off + (l - 14) * 2 ^ 13 + 2 ^ 13 ≤ 2 ^ 23 := by
      simp only [ksY2Off]; norm_num; (clear * - hl h14; omega)
    exact (holds_point hal' hfit' _ hr _ qm).1 H

end Lvm.ASM
end
end

section
section
set_option autoImplicit false
namespace Lvm.ASM
open LeanVM.Parameters LeanVM.Protocol LeanVM.Protocol.Verifier LeanVM.Protocol.EndToEnd
open LeanVM.Protocol.EndToEnd.Front LeanVM.Protocol.KeccakGkr LeanVM.Protocol.Whir.Sound
open LeanVM.Protocol.EndToEnd.Sound (RetOK)
open Lvm.VEq Finset
open Lvm.NS (colM ksCol ksY2 msgM msgX)

/-- Equality weights at a cube point: the indicator of the index. -/
theorem lk_eqAt_boolPoint {m z w : ℕ} (hz : z < 2 ^ m) (hw : w < 2 ^ m) :
    eqAt (boolPoint m z) w = if w = z then 1 else 0 := by
  have e := eqEval_boolPoint_eqAt (boolPoint m z) w
  rw [length_boolPoint] at e
  rw [← e, Complete.eqEval_boolPoint_boolPoint m z w hz hw]
  by_cases hwz : w = z
  · simp [hwz]
  · simp [hwz, Ne.symm hwz]

/-- A sum weighted by `eq(a ‖ sel(t), ·)` over `h + 6` coordinates is slot `t`'s. -/
theorem lk_sum_sel {h t : ℕ} {a : List E} (ha : a.length = h) (ht : t < 2 ^ 6) (F : ℕ → E) :
    ∑ n ∈ range (2 ^ (h + 6)), eqAt (a ++ selE t 6) n * F n =
      ∑ x ∈ range (2 ^ h), eqAt a x * F (x + 2 ^ h * t) := by
  have hs : (selE t 6).length = 6 := by simp [selE, selectorPoint_eq_boolPoint]
  have e := col_split (s := selE t 6) ha F
  rw [hs] at e
  rw [e, Finset.sum_eq_single t]
  · simp only [selE, selectorPoint_eq_boolPoint]
    rw [lk_eqAt_boolPoint ht ht, ite_eq_left rfl, one_mul]
  · intro o ho hne
    simp only [selE, selectorPoint_eq_boolPoint]
    rw [lk_eqAt_boolPoint ht (Finset.mem_range.1 ho), ite_eq_right hne, zero_mul]
  · intro hn
    exact absurd (Finset.mem_range.2 ht) hn

/-- A list sum over `range k` is the `Finset` sum. -/
theorem lk_sum_map_range (g : ℕ → E) :
    ∀ k, ((List.range k).map g).sum = ∑ l ∈ range k, g l
  | 0 => by simp
  | k + 1 => by
    rw [List.range_succ, List.map_append, List.sum_append, lk_sum_map_range g k,
      Finset.sum_range_succ]
    simp

/-- A placed point weight paired with the stack is the block's extension at the point. -/
theorem lk_sum_placed {μ : ℕ} (blk : VPlacement) (z : List E) (hz : z.length = blk.variableCount)
    (hal : 2 ^ blk.variableCount ∣ blk.index) (hfit : blk.index + 2 ^ blk.variableCount ≤ 2 ^ μ)
    (q : Column μ) :
    ∑ x : Fin (2 ^ μ), blk.eqAbove (boolPoint μ x) *
        LeanVM.Protocol.Verifier.eqEval z ((boolPoint μ x).take blk.variableCount) *
        ofK (q.values.getD x 0) =
      ∑ n ∈ range (2 ^ blk.variableCount), eqAt z n * ofK (q.values.getD (blk.index + n) 0) := by
  obtain ⟨v, off⟩ := blk
  simp only at hz hal hfit ⊢
  rw [sum_block hal hfit]
  refine Finset.sum_congr rfl fun n _ ↦ ?_
  subst hz
  rw [eqEval_boolPoint_eqAt]

/-- **A `sumClaimE` claim on its commitment** is the combination of its parts' block extensions. -/
theorem lk_holds_sumClaim {μ k : ℕ} (F : ℕ → E × VPlacement × List E) (val : E) (q : Column μ)
    (hF : ∀ l < k, (F l).2.2.length = (F l).2.1.variableCount ∧
      2 ^ (F l).2.1.variableCount ∣ (F l).2.1.index ∧
      (F l).2.1.index + 2 ^ (F l).2.1.variableCount ≤ 2 ^ μ)
    (h : StackClaim.Holds μ (sumClaimE μ ((List.range k).map F) val).onStack q) :
    ∑ l ∈ range k, (F l).1 * ∑ n ∈ range (2 ^ (F l).2.1.variableCount),
      eqAt (F l).2.2 n * ofK (q.values.getD ((F l).2.1.index + n) 0) = val := by
  have h' : ∑ x : Fin (2 ^ μ), (sumClaimE μ ((List.range k).map F) val).onStack.1 (boolPoint μ x) *
      ofK (q.values.getD x 0) = val := h
  have key : ∀ x : Fin (2 ^ μ),
      (sumClaimE μ ((List.range k).map F) val).onStack.1 (boolPoint μ x) * ofK (q.values.getD x 0) =
        ∑ l ∈ range k, (F l).1 * ((F l).2.1.eqAbove (boolPoint μ x) *
          LeanVM.Protocol.Verifier.eqEval (F l).2.2
            ((boolPoint μ x).take (F l).2.1.variableCount) * ofK (q.values.getD x 0)) := by
    intro x
    have h1 : ({ variableCount := μ, index := 0 } : VPlacement).eqAbove (boolPoint μ x) = 1 := by
      rw [eqAbove_boolPoint (by simp) x.isLt, Nat.div_eq_of_lt x.isLt, Nat.zero_div, ite_eq_left rfl]
    have h2 : (boolPoint μ x).take μ = boolPoint μ x := List.take_of_length_le (by simp)
    show ({ variableCount := μ, index := 0 } : VPlacement).eqAbove (boolPoint μ x) *
        LeanVM.Protocol.Verifier.sumE (((List.range k).map F).map fun (c, blk, z) =>
          c * blk.eqAbove ((boolPoint μ x).take μ) *
            LeanVM.Protocol.Verifier.eqEval z (((boolPoint μ x).take μ).take blk.variableCount)) *
        ofK (q.values.getD x 0) = _
    rw [h1, h2, one_mul, LeanVM.Protocol.Verifier.sumE, foldl_add_eq, zero_add, List.map_map,
      lk_sum_map_range, Finset.sum_mul]
    refine Finset.sum_congr rfl fun l _ ↦ ?_
    rw [Function.comp_apply]
    generalize F l = p
    obtain ⟨c, blk, z⟩ := p
    dsimp only
    ring
  rw [← h', Finset.sum_congr rfl fun x _ ↦ key x, Finset.sum_comm]
  refine Finset.sum_congr rfl fun l hl ↦ ?_
  obtain ⟨hz, hal, hfit⟩ := hF l (Finset.mem_range.1 hl)
  rw [← Finset.mul_sum, lk_sum_placed _ _ hz hal hfit]


/-- A two-block list of parts is one `range` map. -/
theorem lk_range_append {α : Type} (k : ℕ) (F G : ℕ → α) :
    (List.range k).map F ++ (List.range k).map G =
      (List.range (k + k)).map fun j ↦ if j < k then F j else G (j - k) := by
  rw [List.range_add, List.map_append, List.map_map]
  congr 1
  · exact List.map_congr_left fun j hj ↦ by rw [if_pos (List.mem_range.1 hj)]
  · exact List.map_congr_left fun j _ ↦ by
      simp only [Function.comp_apply, if_neg (show ¬ k + j < k by omega), Nat.add_sub_cancel_left]

/-- **The `KS` link's claims** (KS13, lvm2 roll 8, B1: `ρ'` has 13 coordinates, `λ` 5; `M` cut at 7,680, `X` on
`2^9` rows; roll 7: KS14, 14, 15,360, `2^10`; lvm2 roll 11, M′ `S2GM`: `X_l` is the stream block's column `l` from
the split, stride `2^14`). -/
theorem ksLinkClaims_of (kchal : List E) (kshift : List E × E) (vals : List E)
    (h1 : kchal.length = 18) (h2 : kshift.1.length = 13) {qm : Column CMain.nu20} {qr : Column 19}
    (h : ∀ e ∈ ksLinkClaimsE kchal kshift vals, HoldsC qm qr e) :
    Lvm.KG.KsLinkClaims 13 9 (ksCol qm) (Lvm.KG.ksYRow 13 ksY2 (colM qm) (ksCol qm)) (msgM qr)
      (msgX qm) (kchal, kshift, vals) := by
  have hlam : (kchal.drop 13).length = 5 := by simp [h1]
  have hom : ∀ l < 25, (LeanVM.Protocol.Verifier.eqKernel (kchal.drop 13)).getD l 0 =
      eqAt (kchal.drop 13) l := fun l hl ↦ by
    rw [eqKernel_getD, hlam, ite_eq_left (by (clear * - hl; omega))]
  have hlo9 : (kshift.1.take 9).length = 9 := by simp [h2]
  have hy := h _ (List.mem_cons_self ..)
  have hi := h _ (List.mem_cons_of_mem _ (List.mem_cons_self ..))
  have hm := h _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self ..)))
  have hx := h _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _
    (List.mem_cons_self ..))))
  refine ⟨?_, ?_, ?_, ?_⟩
  · have e := lk_holds_sumClaim (μ := CMain.nu20) (k := 25) (fun l ↦
      ((LeanVM.Protocol.Verifier.eqKernel (kchal.drop 13)).getD l 0, (ksYPartE l kshift.1).1,
        (ksYPartE l kshift.1).2)) (vals.getD 0 0) qm ?_ hy
    · dsimp only at e ⊢
      rw [← e]
      refine Finset.sum_congr rfl fun l hl ↦ ?_
      have hl' := Finset.mem_range.1 hl
      rw [hom l hl']
      refine congrArg (eqAt (kchal.drop 13) l * ·) ?_
      unfold LeanVM.Protocol.KeccakGkr.stepMle
      by_cases hl14 : l < 14
      · simp only [ksYPartE, hl14, ↓reduceIte, ksBlk]
        rw [show slotLog = 6 from rfl, lk_sum_sel h2 (by (clear * - hl' hl14; omega))]
        refine Finset.sum_congr rfl fun x _ ↦ ?_
        simp only [Lvm.KG.ksYRow, Lvm.KG.ksY, hl14, ↓reduceIte, ksCol, Lvm.NS.wd]
      · simp only [ksYPartE, hl14, ↓reduceIte]
        refine Finset.sum_congr rfl fun x _ ↦ ?_
        simp only [Lvm.KG.ksYRow, Lvm.KG.ksY, hl14, ↓reduceIte, colM, Lvm.NS.wd, ksY2Off, ksY2]
    · intro l hl
      dsimp only
      by_cases hl14 : l < 14
      · simp only [ksYPartE, hl14, ↓reduceIte, ksBlk]
        exact ⟨by simp [h2, selE, selectorPoint_eq_boolPoint, slotLog], ⟨10, by norm_num [slotLog]⟩,
          by norm_num [slotLog]⟩
      · simp only [ksYPartE, hl14, ↓reduceIte]
        exact ⟨h2, ⟨739 + (l - 14), by rw [ksY2Off]; ring⟩, by rw [ksY2Off]; norm_num; (clear * - hl hl14; omega)⟩
  · have e := lk_holds_sumClaim (μ := CMain.nu20) (k := 25) (fun l ↦
      ((LeanVM.Protocol.Verifier.eqKernel (kchal.drop 13)).getD l 0,
        ({ variableCount := 13 + slotLog, index := CMain.ksOff20 } : VPlacement),
        kshift.1 ++ selE l slotLog)) (vals.getD 1 0) qm
      (fun l hl ↦ by
        dsimp only
        exact ⟨by simp [h2, selE, selectorPoint_eq_boolPoint, slotLog], ⟨10, by norm_num [slotLog]⟩,
          by norm_num [slotLog]⟩) hi
    dsimp only at e ⊢
    rw [← e]
    refine Finset.sum_congr rfl fun l hl ↦ ?_
    have hl' := Finset.mem_range.1 hl
    rw [hom l hl']
    refine congrArg (eqAt (kchal.drop 13) l * ·) ?_
    unfold LeanVM.Protocol.KeccakGkr.stepMle
    rw [show slotLog = 6 from rfl, lk_sum_sel h2 (by (clear * - hl'; omega))]
    refine Finset.sum_congr rfl fun x _ ↦ ?_
    simp only [ksCol, Lvm.NS.wd]
  · have hm' : HoldsC qm qr (.crec, sumClaimE 19 ((List.range (17 + 17)).map fun j ↦ if j < 17 then
        ((LeanVM.Protocol.Verifier.eqKernel (kchal.drop 13)).getD j 0,
          ({ variableCount := 13, index := j * 2 ^ 14 } : VPlacement), kshift.1) else
        ((LeanVM.Protocol.Verifier.eqKernel (kchal.drop 13)).getD (j - 17) 0 * Lvm.KG.selX 9 kshift.1,
          ({ variableCount := 9, index := (j - 17) * 2 ^ 14 + ksSplit P20 } : VPlacement),
          kshift.1.take 9)) (vals.getD 2 0)) := by
      simpa only [lk_range_append] using hm
    have hsp : ksSplit P20 = 7680 := ksSplit_P20
    have e := lk_holds_sumClaim (μ := 19) (k := 17 + 17) _ (vals.getD 2 0) qr (fun j hj ↦ by
        by_cases hj17 : j < 17
        · rw [if_pos hj17]
          exact ⟨h2, ⟨2 * j, by ring⟩, by dsimp only; (clear * - hj hj17; omega)⟩
        · rw [if_neg hj17]
          exact ⟨hlo9, ⟨(j - 17) * 32 + 15, by dsimp only; rw [hsp]; (clear * -; omega)⟩, by dsimp only; rw [hsp]; (clear * - hj hj17; omega)⟩) hm'
    rw [← e, Finset.sum_range_add, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun l hl ↦ ?_
    have hl' := Finset.mem_range.1 hl
    rw [if_pos hl', if_neg (show ¬ 17 + l < 17 by (clear * - hl'; omega)), Nat.add_sub_cancel_left]
    dsimp only
    rw [hom l (by (clear * - hl'; omega)), mul_assoc, ← mul_add]
    refine congrArg (eqAt (kchal.drop 13) l * ·) ?_
    rw [← Lvm.KG.cut_split (hk := 13) (xl := 9) (by norm_num) h2 (fun n ↦ ofK (msgM qr n l))]
    have hsN : Lvm.KG.ksSplitN 13 9 = 7680 := by decide
    simp only [msgM, Lvm.NS.wd, hsp, hsN, Nat.add_assoc]
  · have e := lk_holds_sumClaim (μ := CMain.nu20) (k := 17) (fun l ↦
      ((LeanVM.Protocol.Verifier.eqKernel (kchal.drop 13)).getD l 0,
        ({ variableCount := 9, index := xOff + l * 2 ^ 14 } : VPlacement), kshift.1.take 9))
      (vals.getD 3 0) qm
      (fun l hl ↦ ⟨hlo9, ⟨11279 + 32 * l, by rw [xOff]; ring⟩, by
        have hl' := Finset.mem_range.1 (Finset.mem_range.2 hl)
        show xOff + l * 2 ^ 14 + 2 ^ 9 ≤ 2 ^ 23
        simp only [xOff, CMain.xOff20]; (clear * - hl; omega)⟩) hx
    dsimp only at e ⊢
    rw [← e]
    refine Finset.sum_congr rfl fun l hl ↦ ?_
    have hl' := Finset.mem_range.1 hl
    rw [hom l (by (clear * - hl'; omega))]
    unfold LeanVM.Protocol.KeccakGkr.stepMle
    refine congrArg (eqAt (kchal.drop 13) l * ·) (Finset.sum_congr rfl fun x _ ↦ ?_)
    simp only [msgX, Lvm.NS.wd, CMain.ksXW20_eq, xOff]
    rfl

end Lvm.ASM
end
end

section
section
set_option autoImplicit false
namespace Lvm.ASM
open LeanVM.Parameters LeanVM.Protocol LeanVM.Protocol.Verifier LeanVM.Protocol.EndToEnd
open LeanVM.Protocol.EndToEnd.Front LeanVM.Protocol.KeccakGkr LeanVM.Protocol.Whir.Sound
open LeanVM.Protocol.EndToEnd.Sound (RetOK)
open Lvm.VEq Finset
open Lvm.NS (colM ksCol ksY2 msgM msgX)

/-- `sumE` of multiaffine weights is multiaffine. -/
theorem isMultiaffine_sumE {n : ℕ} {γ : Type} (xs : List γ) (F : γ → List E → E)
    (hF : ∀ a ∈ xs, IsMultiaffine n (F a)) :
    IsMultiaffine n fun l ↦ LeanVM.Protocol.Verifier.sumE (xs.map fun a ↦ F a l) := by
  simp only [LeanVM.Protocol.Verifier.sumE, foldl_add_eq, zero_add]
  induction xs with
  | nil => simpa using (IsMultiaffine.zero (n := n))
  | cons a xs ih =>
    simp only [List.map_cons, List.sum_cons]
    exact (hF a (List.mem_cons_self ..)).add (ih fun b hb ↦ hF b (List.mem_cons_of_mem _ hb))

/-- **A sum claim's weight is multiaffine** when its parts' blocks fit. -/
theorem isMultiaffine_sumClaimE (nu : ℕ) (parts : List (E × VPlacement × List E)) (value : E)
    (hp : ∀ p ∈ parts, p.2.1.variableCount ≤ nu) :
    IsMultiaffine nu (sumClaimE nu parts value).weight := by
  unfold sumClaimE
  refine isMultiaffine_sumE parts _ fun p hpm ↦ ?_
  obtain ⟨c, blk, z⟩ := p
  have h := (isMultiaffine_onStack (n := nu) ⟨blk, LeanVM.Protocol.Verifier.eqEval z, 0⟩
    (hp _ hpm) (isMultiaffine_eqEvalN z _)).const_mul c
  have e : (fun x ↦ c * blk.eqAbove x *
      LeanVM.Protocol.Verifier.eqEval z (x.take blk.variableCount)) =
      fun r ↦ c * (BClaim.onStack ⟨blk, LeanVM.Protocol.Verifier.eqEval z, 0⟩).1 r :=
    funext fun x ↦ mul_assoc _ _ _
  show IsMultiaffine nu fun x ↦
    c * blk.eqAbove x * LeanVM.Protocol.Verifier.eqEval z (x.take blk.variableCount)
  rw [e]
  exact h

/-- A Keccak table's claims on `C_main`. -/
theorem okC_keccakClaimsE (blk : VPlacement) (co : CallerOut) (hv : blk.variableCount ≤ 23)
    (hr : ∀ n, IsMultiaffine n co.2.2.2.2) : ∀ b ∈ keccakClaimsE blk co, OkC (.main, b) := by
  intro b hb
  simp only [keccakClaimsE, List.mem_append, List.mem_map, List.mem_singleton] at hb
  rcases hb with ⟨c, -, rfl⟩ | rfl
  · exact okC_point _ _ _ _ hv
  · exact ⟨hv, hr _⟩

/-- The tape's claims on `C_main` (lvm2 S2): point claims on `D`'s block, the ring claim on all of
`C_main`. -/
theorem okC_tapeClaimsE (tp : Lvm.KG.TapeOutE) (pub : Lvm.Pub)
    (hr : ∀ n, IsMultiaffine n tp.2.2.2.d.ring.2) : ∀ b ∈ tapeClaimsE tp pub, OkC (.main, b) := by
  intro b hb
  simp only [tapeClaimsE, List.mem_append, List.mem_map, List.mem_singleton] at hb
  rcases hb with (⟨l, -, rfl⟩ | rfl) | ⟨⟨w, l⟩, -, rfl⟩
  · exact okC_point _ _ _ _ (by simp [dBlkE, nuOf])
  · exact ⟨by simp [nuMainE, nuOf], hr _⟩
  · exact okC_point _ _ _ _ (by simp [dBlkE, nuOf])

/-- `KS`'s `Y` lane blocks fit `C_main`. -/
theorem ksYPartE_le (l : ℕ) (pt : List E) : (ksYPartE l pt).1.variableCount ≤ 23 := by
  unfold ksYPartE
  split <;> simp [slotLog, ksBlk]

/-- **Every assembled claim** fits its commitment with a multiaffine weight. -/
theorem okC_claimsS (T : List Lvm.M3.Tab) (pub : Lvm.Pub) (cl : List ColumnClaim) (kg : KgOut)
    (hlay : Lvm.M3.LayOk Lvm.M3.lay26 T) (hk : KgRet kg) : ∀ e ∈ claimsS T pub cl kg, OkC e := by
  obtain ⟨⟨-, -, hr1⟩, ⟨-, -, -, -, hr2, -, -⟩⟩ := hk
  intro e he
  simp only [claimsS, List.mem_append] at he
  rcases he with ((htab | hm) | hko) | hkl
  · exact okC_tableClaimsE T cl hlay e htab
  · simp only [List.mem_map, List.mem_append] at hm
    obtain ⟨b, hb | hb, rfl⟩ := hm
    · exact okC_tapeClaimsE _ _ hr1 b hb
    · exact okC_keccakClaimsE _ _ (by simp [ksBlk, slotLog]) hr2 b hb
  · simp only [ksOutputClaimsE, List.mem_map] at hko
    obtain ⟨l, -, rfl⟩ := hko
    exact okC_point _ _ _ _ (ksYPartE_le l _)
  · simp only [ksLinkClaimsE, List.mem_cons, List.mem_nil_iff, or_false] at hkl
    rcases hkl with rfl | rfl | rfl | rfl
    · refine ⟨le_rfl, isMultiaffine_sumClaimE _ _ _ fun p hp ↦ ?_⟩
      simp only [List.mem_map] at hp
      obtain ⟨l, -, rfl⟩ := hp
      exact ksYPartE_le l _
    · refine ⟨le_rfl, isMultiaffine_sumClaimE _ _ _ fun p hp ↦ ?_⟩
      simp only [List.mem_map] at hp
      obtain ⟨l, -, rfl⟩ := hp
      simp [sumClaimE, slotLog, ksBlk, nuMainE, CMain.nu20]
    · refine ⟨le_rfl, isMultiaffine_sumClaimE _ _ _ fun p hp ↦ ?_⟩
      simp only [List.mem_append, List.mem_map] at hp
      rcases hp with ⟨l, -, rfl⟩ | ⟨l, -, rfl⟩ <;> simp [sumClaimE, nuMainE, CMain.nu20]
    · refine ⟨le_rfl, isMultiaffine_sumClaimE _ _ _ fun p hp ↦ ?_⟩
      simp only [List.mem_map] at hp
      obtain ⟨l, -, rfl⟩ := hp
      simp [sumClaimE, nuMainE, CMain.nu20]

/-- `C_rec`'s claims: the tables' on it and `mC`. -/
theorem length_crec_le (T : List Lvm.M3.Tab) (pub : Lvm.Pub) (cl : List ColumnClaim)
    (kg : KgOut) : ((claimsS T pub cl kg).filter (·.1 == .crec)).length ≤ cl.length + 1 := by
  have hmc : (Com.main == Com.crec) = false := rfl
  simp [hmc, claimsS, ksOutputClaimsE, ksLinkClaimsE, List.filter_append,
    List.filter_map, Function.comp_def]
  exact (List.length_filter_le _ _).trans (List.length_filterMap_le _ _)

/-- The number of assembled claims. -/
theorem length_claimsS (T : List Lvm.M3.Tab) (pub : Lvm.Pub) (cl : List ColumnClaim)
    (kg : KgOut) : (claimsS T pub cl kg).length = (tableClaimsE T cl).length +
      kg.2.1.2.2.1.1.length + pub.h.length + 35 := by
  simp [claimsS, ksOutputClaimsE, ksLinkClaimsE, keccakClaimsE, tapeClaimsE]
  omega

/-- `C_main` holds one claim per lane of `pub.h` (`tapeClaimsE`'s boundary claims), and more. -/
theorem length_h_lt_main (T : List Lvm.M3.Tab) (pub : Lvm.Pub) (cl : List ColumnClaim)
    (kg : KgOut) : pub.h.length < (assembleS T pub cl kg).2.length := by
  rw [assembleS_eq]
  simp [claimsS, ksOutputClaimsE, ksLinkClaimsE, keccakClaimsE, tapeClaimsE,
    List.filter_append, List.filter_map, Function.comp_def]
  omega

/-- **`assembleS`'s side conditions**, when `pub.h` has at most `2^38` lanes (lvm2 J2′: at most `2^55` claims on
`C_rec`, its batching at the Johnson list bound). -/
theorem side_assembleS (T : List Lvm.M3.Tab) (pub : Lvm.Pub) (cl : List ColumnClaim)
    (kg : KgOut) (hlay : Lvm.M3.LayOk Lvm.M3.lay26 T) (hret : TabRet T cl)
    (hn : (T.map (·.w)).sum ≤ 2 ^ 38) (hk : KgRet kg) (hh : pub.h.length ≤ 2 ^ 38) :
    (∀ c ∈ (assembleS T pub cl kg).1, IsMultiaffine 19 c.1) ∧
    (∀ c ∈ (assembleS T pub cl kg).2, IsMultiaffine CMain.nu20 c.1) ∧
    (assembleS T pub cl kg).1.length ≤ 2 ^ 55 ∧ (assembleS T pub cl kg).2.length ≤ 2 ^ 40 := by
  have hok := okC_claimsS T pub cl kg hlay hk
  have hcl := hret.2
  have hk2 := hk.2.2.2.2.1
  rw [assembleS_eq]
  refine ⟨fun c hc ↦ ?_, fun c hc ↦ ?_, ?_, ?_⟩
  · obtain ⟨e, he, rfl⟩ := List.mem_map.mp hc
    obtain ⟨he, hcom⟩ := List.mem_filter.mp he
    obtain ⟨hv, hw⟩ := hok e he
    obtain ⟨com, b⟩ := e
    cases com
    · cases hcom
    · exact isMultiaffine_onStack b hv hw
  · obtain ⟨e, he, rfl⟩ := List.mem_map.mp hc
    obtain ⟨he, hcom⟩ := List.mem_filter.mp he
    obtain ⟨hv, hw⟩ := hok e he
    obtain ⟨com, b⟩ := e
    cases com
    · exact isMultiaffine_onStack b hv hw
    · cases hcom
  · rw [List.length_map]
    have := length_crec_le T pub cl kg
    (clear * - hn hcl this; omega)
  · rw [List.length_map]
    have h1 := List.length_filter_le (·.1 == Com.main) (claimsS T pub cl kg)
    have h2 := length_claimsS T pub cl kg
    have h4 : (tableClaimsE T cl).length ≤ cl.length := List.length_filterMap_le _ _
    (clear * - hn hh hcl hk2 h1 h2 h4; omega)

end Lvm.ASM
end
end

section
set_option autoImplicit false
namespace Lvm.ASM
open LeanVM.Parameters LeanVM.Protocol LeanVM.Protocol.Compile LeanVM.Protocol.Verifier
open LeanVM.Protocol.Compile.VerifierProgram LeanVM.Protocol.Whir.Sound LeanVM.Protocol.EndToEnd
open LeanVM.Protocol.EndToEnd.Front LeanVM.Protocol.KeccakGkr
open LeanVM.Protocol.EndToEnd.Sound (RetOK)
open Lvm.VEq Lvm.KG Lvm.M3
open Lvm.NS (colM ksCol ksY2 msgM msgX Bnd GoodB GoodN)
open scoped ENNReal NNReal
section Glue
variable {α κ : Type} {busP : List UInt8 → VerifierProgram α} {kgP : List UInt8 → VerifierProgram κ}
  {asm : List UInt8 → α → κ → OpenClaims}
  {Gb Gk : List UInt8 → Pair → Prop} {B : List UInt8 → α → Pair → Prop}
  {Kc : κ → Pair → Prop} {Qa : List UInt8 → α → Prop} {Qk : κ → Prop} {Lb Lk : ℝ≥0∞}

open Classical in
/-- **`MidSpec` from the phases, with return facts** (`midSpecOf` with `Qa`, `Qk`; lvm2 S2: the Keccak
phases read the statement, `kgP x`). -/
theorem midSpecOfR
    (SB : ∀ x, Spec (busP x)
      (fun h ↦ RootShape h ∧ Doomed candPairs (fun p ↦ Gb x p ∧ Gk x p) h)
      (fun a h ↦ Doomed candPairs (fun p ↦ B x a p ∧ Gk x p) h ∧ RootShape h) εS Lb Lk)
    (hQa : ∀ x, RetOK (Qa x) (busP x))
    (SK : ∀ x a (T : ℝ≥0∞), T ≤ εS → Spec (kgP x) (Doomed candPairs (fun p ↦ Gk x p ∧ B x a p))
      (fun k h ↦ Doomed candPairs (fun p ↦ Kc k p ∧ B x a p) h) εS Lk T)
    (hQk : ∀ x, RetOK Qk (kgP x)) (hkc : ∀ x, NoCG (kgP x))
    (hasm : ∀ x a k (p : Pair), Qa x a → Qk k →
      (∀ c ∈ (asm x a k).1, StackClaim.Holds 19 c p.2) →
      (∀ c ∈ (asm x a k).2, StackClaim.Holds CMain.nu20 c p.1) → Kc k p ∧ B x a p)
    (hside : ∀ x a k, Qa x a → Qk k → (∀ c ∈ (asm x a k).1, IsMultiaffine 19 c.1) ∧
      (∀ c ∈ (asm x a k).2, IsMultiaffine CMain.nu20 c.1) ∧ (asm x a k).1.length ≤ 2 ^ 63 ∧
      (asm x a k).2.length ≤ 2 ^ 40) :
    MidSpec (fun x ↦ busP x >>= fun a ↦ kgP x >>= fun k ↦ VerifierProgram.ret (asm x a k))
      (fun x qm qr ↦ Gb x (qm, qr) ∧ Gk x (qm, qr)) εS Lb := fun x T hT ↦
  ⟨((Lvm.KG.specWithRet (SB x) (hQa x)).bind' fun a ↦
      if ha : Qa x a then
        ((Lvm.KG.specWithRet ((SK x a T hT).frame RootShape fun _ _ hl hr ↦
            rootShape_append' ((hkc x).1.reach_commits hl) hr) (hQk x)).mono
          (fun h hp ↦ ⟨Doomed.mono hp.2.1 fun p hq ↦ ⟨hq.2, hq.1⟩, hp.2.2⟩) (fun _ _ h ↦ h) le_rfl
          le_rfl le_rfl).bind' fun k ↦
        if hk : Qk k then
          (Spec.ret (Post := OpenPost) (εmax := εS) (T := T) (asm x a k)).mono
            (fun h hp ↦ openPost_of (hasm x a k · ha hk) (hside x a k ha hk) hp.2.1 hp.2.2)
            (fun _ _ h ↦ h) le_rfl le_rfl le_rfl
        else Spec.dead.mono (fun _ hd ↦ hk hd.1) (fun _ _ h ↦ h) le_rfl le_rfl le_rfl
      else Spec.dead.mono (fun _ hd ↦ ha hd.1) (fun _ _ h ↦ h) le_rfl le_rfl le_rfl).mono
    (fun h hp ↦ ⟨hp.2, hp.1⟩) (fun _ _ h ↦ h) le_rfl le_rfl le_rfl⟩

end Glue
end Lvm.ASM
end

section
set_option autoImplicit false
namespace Lvm.ASM
open LeanVM.Parameters LeanVM.Protocol LeanVM.Protocol.Compile LeanVM.Protocol.Verifier
open LeanVM.Protocol.Compile.VerifierProgram LeanVM.Protocol.Whir.Sound LeanVM.Protocol.EndToEnd
open LeanVM.Protocol.EndToEnd.Front LeanVM.Protocol.KeccakGkr
open LeanVM.Protocol.EndToEnd.Sound (RetOK)
open Lvm.VEq Lvm.KG Lvm.M3
open Lvm.NS (colM ksCol ksY2 msgM msgX Bnd GoodB GoodN)
open scoped ENNReal NNReal

/-- **The good pair of O6**: WP-14c's `GoodN` with the boundary claims when the chain fits `D`. -/
def GoodS (T : List UInt8 → List Tab) (hτ : ∀ x, ∀ t ∈ T x, t.τ ≤ lay26.μ) : GoodRel :=
  fun x qm qr ↦ (GoodB T hτ x (qm, qr) ∧ BndS x qm) ∧ GkS x (qm, qr)

/-- **`NodeSound` for `GoodS`** from `NodeSound` for WP-14c's `GoodN`: `okS` bounds `n` by `2^20`. -/
theorem nodeSound_goodS {VS : Lvm.T.SProg} {vk : RecursionFast.Digest} {T : List UInt8 → List Tab}
    {hτ : ∀ x, ∀ t ∈ T x, t.τ ≤ lay26.μ} {child : Column 19 → RecursionFast.Signed}
    (h : NodeSound VS vk (GoodN T hτ) child) : NodeSound VS vk (GoodS T hτ) child :=
  fun c x qm qr hok hG ↦ h c x qm qr hok
    ⟨hG.1.1, hG.2.1, hG.2.2, hG.1.2 (Lvm.NS.okS_n hok).2⟩

end Lvm.ASM
end

section
set_option autoImplicit false
namespace Lvm.ASM
open LeanVM.Parameters LeanVM.Protocol LeanVM.Protocol.Compile LeanVM.Protocol.Verifier
open LeanVM.Protocol.Compile.VerifierProgram LeanVM.Protocol.Whir.Sound LeanVM.Protocol.EndToEnd
open LeanVM.Protocol.EndToEnd.Front LeanVM.Protocol.KeccakGkr
open LeanVM.Protocol.EndToEnd.Sound (RetOK)
open Lvm.VEq Lvm.KG Lvm.M3
open Lvm.NS (colM ksCol ksY2 msgM msgX Bnd GoodB GoodN)
open scoped ENNReal NNReal

theorem LkSJ_eq : LkSJ = errE ((15 + 5) * (37696 * 1)) := by
  simp only [LkSJ, add_zero, errE_smul]

/-- **`midBusTableSpecS`'s error side conditions at `εS` with `37,696` candidate pairs** (lvm2 J2′), follower
`LkSJ`; the batching bound `I.B ≤ 2^48` (not `2^56`): `37,696·(I.B + 2) + 20·37,696 ≤ 7·2^61` (`εS` exactly,
`errE_le_εS7`; `2^63.20` against `2^63.81`). -/
theorem bus_errsJ2 (I : LeanVM.Protocol.M3Instance) (hμ : I.μBus ≤ 22) (hB : I.B ≤ 2 ^ 48) (m : ℕ) :
    abError I 37696 < 1 ∧ abError I 37696 + 0 ≤ εS ∧ roundError 37696 4 ≤ εS ∧
    interpLead 37696 2 (lambdaError 37696) ≤ εS ∧ lambdaError 37696 + 0 ≤ εS ∧
    roundError 37696 3 + LkSJ ≤ εS ∧ LkSJ ≤ εS ∧
    xiError I 37696 + sumcheckLead (List.replicate m none) LkSJ ≤ εS := by
  have hab : abError I 37696 = errE (37696 * (4 * 2 ^ I.μBus)) := by
    rw [abError, coe_overE, errE_smul]
  have hab' : abError I 37696 ≤ εS := by
    rw [hab]
    refine errE_le_εS (le_trans (Nat.mul_le_mul_left 37696 (Nat.mul_le_mul_left 4
      (Nat.pow_le_pow_right (by norm_num) hμ))) (by norm_num))
  have hr : ∀ d, roundError 37696 d = errE (37696 * d) := fun d ↦ by
    rw [roundError, coe_div_card, errE_smul]
  have hl : lambdaError 37696 = errE (37696 * 2) := by
    rw [lambdaError, coe_div_card, errE_smul]
  have hu : unitError 37696 = errE (37696 * 1) := by
    rw [← errE_smul]; simp [unitError, errE]
  have hx : xiError I 37696 = errE (37696 * (I.B + 3 - 1)) := by
    rw [xiError, coe_div_card, errE_smul]
  refine ⟨lt_of_le_of_lt hab' εS_lt_one, by rw [add_zero]; exact hab', ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hr]; exact errE_le_εS (by norm_num)
  · rw [interpLead_eq, hu, hl, errE_smul, errE_add]
    exact errE_le_εS (by norm_num)
  · rw [hl, add_zero]; exact errE_le_εS (by norm_num)
  · rw [hr, LkSJ_eq, errE_add]; exact errE_le_εS (by norm_num)
  · rw [LkSJ_eq]; exact errE_le_εS (by norm_num)
  · -- `37,696·(I.B + 2) + 20·37,696 ≤ 7·2^61` (`εS = 7·2^-131` exactly, `2^63.81`): `I.B ≤ 2^48` suffices
    -- (`2^63.20`); the `2^63` of `errE_le_εS` would need `I.B ≤ 2^47.8`.
    refine (add_le_add le_rfl (sumcheckLead_le _ _)).trans ?_
    rw [hx, LkSJ_eq, errE_add]
    have hB' : I.B ≤ 281474976710656 := by simpa using hB
    exact errE_le_εS7 (by norm_num; omega)

end Lvm.ASM
end

section
set_option autoImplicit false
namespace Lvm.ASM
open LeanVM.Parameters LeanVM.Protocol LeanVM.Protocol.Compile LeanVM.Protocol.Verifier
open LeanVM.Protocol.Compile.VerifierProgram LeanVM.Protocol.Whir.Sound LeanVM.Protocol.EndToEnd
open LeanVM.Protocol.EndToEnd.Front LeanVM.Protocol.KeccakGkr
open LeanVM.Protocol.EndToEnd.Sound (RetOK)
open Lvm.VEq Lvm.KG Lvm.M3
open Lvm.NS (colM ksCol ksY2 msgM msgX Bnd GoodB GoodN)
open scoped ENNReal NNReal

/-- The record's table evaluations are few (`≤ 2^38`: `C_main`'s claims stay under `2^40`, the
Johnson batching's `(J − 1)·98/|E|`). -/
theorem tableEvals_P20_le : Lvm.P20.tableEvals ≤ 2 ^ 38 := by decide

end Lvm.ASM
end

section
set_option autoImplicit false
namespace Lvm.ASM
open LeanVM.Parameters LeanVM.Protocol LeanVM.Protocol.Compile LeanVM.Protocol.Verifier
open LeanVM.Protocol.Compile.VerifierProgram LeanVM.Protocol.Whir.Sound LeanVM.Protocol.EndToEnd
open LeanVM.Protocol.EndToEnd.Front LeanVM.Protocol.KeccakGkr
open LeanVM.Protocol.EndToEnd.Sound (RetOK)
open Lvm.VEq Lvm.KG Lvm.M3
open Lvm.NS (colM ksCol ksY2 msgM msgX Bnd GoodB GoodN)
open scoped ENNReal NNReal
variable {tabs : Lvm.Pub → List Tab}

/-- The bus/table phase's claims on a pair (`midBusTableSpecS`'s post) and the boundary claims,
carried through V_S phases 4–7. -/
def BS (tabs : Lvm.Pub → List Tab) (x : List UInt8) (a : List ColumnClaim) (p : Pair) : Prop :=
  (∀ c ∈ a, BlockHolds lay26 (TS tabs x) p.1 p.2 c) ∧ BndS x p.1

/-- V_S phases 4–7 at P20, in `midSpecOfR`'s form (lvm2 S2: `kgSpecS`, the tape then `KS`), carrying `R`
(J2′: `BS ∧ ¬ Good`) at `L₀ = 37,696`; `KS` at `Pk = xl = 9` (KS13, lvm2 roll 8, B1; roll 7: `10 10`). -/
noncomputable def specKgS (x : List UInt8) (R : Pair → Prop) (T : ℝ≥0∞) (hT : T ≤ εS) :
    Spec (kgProgS (hdX x).s (pubX x).n) (Doomed candPairs (fun p ↦ GkS x p ∧ R p))
      (fun k h ↦ Doomed candPairs (fun p ↦ KcS k p ∧ R p) h) εS LkSJ T :=
  have e := kg_errsJ2
  have s := kg_struct
  (kgSpecS (C := candPairs) (L₀ := 37696) (εmax := εS) (T := T) candPairs_stable candPairs_ncard_le
    (hdX x).s (pubX x).n 9 9 ksY2 (by norm_num) (Lvm.contRows Lvm.P20) s.2.2.1 s.2.2.2
    (fun q ↦ colM q.1) (fun q ↦ colM q.1) (fun q ↦ ksCol q.1) (fun q ↦ msgM q.2)
    (fun q ↦ msgX q.1) R e.1 e.2.1 e.2.2.1 e.2.2.2.1 hT).mono
    (fun _ hd ↦ Doomed.mono hd fun q ⟨ht, hk, hb⟩ ↦
      ⟨⟨by rw [pubX_n x] at ht; exact ht, hk⟩, hb⟩)
    (fun _ _ hp ↦ Doomed.mono hp.2 fun _ hq ↦ ⟨hq.1.1, hq.1.2, hq.2⟩) le_rfl le_rfl le_rfl

/-- **The semantic link**: the assembled claims holding on a pair give `KcS ∧ BS` (lvm2 S2: the
tape's ring claim, tied lanes and boundary claims). -/
theorem link_assembleS (H : MidHyp tabs) (x : List UInt8) (a : List ColumnClaim) (k : KgOut)
    (p : Pair) (ha : TabRet (TS tabs x) a) (hk : KgRet k)
    (h1 : ∀ c ∈ (assembleS (TS tabs x) (pubX x) a k).1, StackClaim.Holds 19 c p.2)
    (h2 : ∀ c ∈ (assembleS (TS tabs x) (pubX x) a k).2, StackClaim.Holds CMain.nu20 c p.1) :
    KcS k p ∧ BS tabs x a p := by
  have hc := holdsC_of_assembleS h1 h2
  obtain ⟨⟨hr, -, -⟩, ⟨hrk, -, hck, -, -, hkc, hks⟩⟩ := hk
  have hm : ∀ b, (Com.main, b) ∈ claimsS (TS tabs x) (pubX x) a k →
      StackClaim.Holds CMain.nu20 b.onStack p.1 := fun b hb ↦ hc _ hb
  have hTP : ∀ b ∈ tapeClaimsE k.1 (pubX x), StackClaim.Holds CMain.nu20 b.onStack p.1 :=
    fun b hb ↦ hm b (by simp [claimsS, hb])
  have hKK : ∀ b ∈ keccakClaimsE ksBlk k.2.1, StackClaim.Holds CMain.nu20 b.onStack p.1 :=
    fun b hb ↦ hm b (by simp [claimsS, hb])
  have hsub : ∀ l : List (Com × BClaim), (∀ e ∈ l, e ∈ claimsS (TS tabs x) (pubX x) a k) →
      ∀ e ∈ l, HoldsC p.1 p.2 e := fun l hl e he ↦ hc e (hl e he)
  refine ⟨⟨tapeClaims_of k.1 hr (pubX x) hTP,
    ⟨callerClaims_ks k.2.1 hrk hck hKK (hsub _ (fun e he ↦ by simp [claimsS, he])),
      ksLinkClaims_of k.2.2.1 k.2.2.2.1 k.2.2.2.2 hkc hks
        (hsub _ (fun e he ↦ by simp [claimsS, he]))⟩⟩,
    blockHolds_of_tableClaims (T := TS tabs x) (fit_of Lvm.P20 _ (H.fit (pubX x))).layOk ha
      (hsub _ (fun e he ↦ by simp [claimsS, he])), bndS_of_tape x _ hTP⟩

theorem side_midS (H : MidHyp tabs) (x : List UInt8) (a : List ColumnClaim) (k : KgOut)
    (ha : TabRet (TS tabs x) a) (hk : KgRet k) :
    (∀ c ∈ (assembleS (TS tabs x) (pubX x) a k).1, IsMultiaffine 19 c.1) ∧
    (∀ c ∈ (assembleS (TS tabs x) (pubX x) a k).2, IsMultiaffine CMain.nu20 c.1) ∧
    (assembleS (TS tabs x) (pubX x) a k).1.length ≤ 2 ^ 55 ∧
    (assembleS (TS tabs x) (pubX x) a k).2.length ≤ 2 ^ 40 :=
  have F := fit_of Lvm.P20 _ (H.fit (pubX x))
  side_assembleS _ _ a k F.layOk ha (F.evals ▸ tableEvals_P20_le) hk (by rw [length_pubX_h]; norm_num)

end Lvm.ASM
end

-- ===== from `LvmCertSJ` =====

section
set_option autoImplicit false
namespace Lvm.ASM
open LeanVM.Parameters LeanVM.Protocol LeanVM.Protocol.Compile LeanVM.Protocol.Verifier
open LeanVM.Protocol.Compile.VerifierProgram LeanVM.Protocol.Whir.Sound LeanVM.Protocol.EndToEnd
open LeanVM.Protocol.EndToEnd.Front LeanVM.Protocol.KeccakGkr
open Lvm.VEq Lvm.KG Lvm.M3
open scoped ENNReal NNReal

/-- `124·304`: J2′'s candidate pairs (`candPairsJ_ncard_le`; the front end's `kg_errsJ2`, `LkSJ`, `bus_errsJ2`
are in `LvmCertSMid2`/`LvmCertSMid3`, where `specKgS` and `specBusA` use them). -/
theorem l0J2_eq : (37696 : ℕ) = 124 * 304 := rfl

end Lvm.ASM
end

-- ===== from `LvmCertSExtJSplit` =====

section
section
set_option autoImplicit false
namespace Lvm.ASM
open LeanVM.Parameters LeanVM.Protocol LeanVM.Protocol.Compile LeanVM.Protocol.Verifier
open LeanVM.Protocol.Compile.VerifierProgram LeanVM.Protocol.Whir.Sound LeanVM.Protocol.EndToEnd
open LeanVM.Protocol.Whir LeanVM.Protocol.Whir.Ud
open scoped ENNReal

/-- **`C_rec`'s level-1 cap at J2′** (the UD reader: the first commitment after the middle phases, and the
events after it). -/
abbrev rec1OfJ (mid : List UInt8 → VerifierProgram OpenClaims) (x : List UInt8) (h : List Ev) :
    Option (Word × List Ev) :=
  rec1Of mid x h

end Lvm.ASM
end
end

section
set_option autoImplicit false
namespace Lvm.ASM
open RecursionFast Lvm.FS Lvm.T
open LeanVM.Parameters LeanVM.Protocol LeanVM.Protocol.Compile LeanVM.Protocol.Verifier
open LeanVM.Protocol.Compile.VerifierProgram LeanVM.Protocol.Whir.Sound LeanVM.Protocol.EndToEnd
open LeanVM.Protocol.Whir
open scoped NNReal ENNReal

theorem levels_rec20Jp_ne : cfgRec20Jp.levels ≠ [] := List.cons_ne_nil _ _

/-- **`P_S` at J2′ is the run up to `C_rec`'s residual, then `C_rec`'s suffix, `C_main`'s opening and
`true`.** -/
theorem PSWith_eq_prefixJ (mid : List UInt8 → VerifierProgram OpenClaims) (x : List UInt8) :
    PSWith mid x = (recPrefixProg mid x).bind fun ca ↦
      (stackSuffixJ cfgRec20Jp ca.1.1 levels_rec20Jp_ne ca.2).bind fun _ ↦
        (verifyStackedJ (cfgMain23Jq 3) ca.1.2).bind fun _ ↦ .ret true := by
  unfold PSWith recPrefixProg
  simp only [verifyStackedJ_eq_prefix cfgRec20Jp rfl levels_rec20Jp_ne, bind_eq,
    VerifierProgram.bind_assoc, VerifierProgram.ret_bind]
  rfl

end Lvm.ASM
end

section
set_option autoImplicit false
namespace Lvm.ASM
open RecursionFast Lvm.FS Lvm.T
open LeanVM.Parameters LeanVM.Protocol LeanVM.Protocol.Compile LeanVM.Protocol.Verifier
open LeanVM.Protocol.Compile.VerifierProgram LeanVM.Protocol.Whir.Sound LeanVM.Protocol.EndToEnd
open LeanVM.Protocol.Whir
open scoped NNReal ENNReal
section Split
variable {mid : List UInt8 → VerifierProgram OpenClaims} {x : List UInt8}

/-- **An accepted history of `P_S` at J2′** is a completed run of `recPrefixProg` (`recPrefix_split`
splits it), then a run of `C_rec`'s suffix, `C_main`'s opening and `true`. -/
theorem accept_splitJ {h : List Ev} (hacc : (PSWith mid x).after h = some (.ret true)) :
    ∃ (h₁ rest : List Ev) (cl : OpenClaims) (a : E × ((WhirStateT × List E) × List E)),
      h = h₁ ++ rest ∧ (recPrefixProg mid x).after h₁ = some (.ret (cl, a)) ∧
      ((stackSuffixJ cfgRec20Jp cl.1 levels_rec20Jp_ne a).bind fun _ ↦
        (verifyStackedJ (cfgMain23Jq 3) cl.2).bind fun _ ↦ .ret true).after rest = some (.ret true) := by
  rw [PSWith_eq_prefixJ] at hacc
  obtain ⟨⟨cl, a⟩, h₁, rest, rfl, h1, h2⟩ := after_bind_ret hacc
  exact ⟨h₁, rest, cl, a, rfl, h1, h2⟩

end Split
end Lvm.ASM
end

-- ===== from `LvmCertSExtJ` =====

section
section
namespace LeanVM.Protocol.Whir.Sound
open LeanVM.Parameters LeanVM.Protocol.Compile LeanVM.Protocol.Verifier
  LeanVM.Protocol.Whir LeanVM.Protocol.EndToEnd Finset
section

/-- `PostR`'s final level at J2′ is level `1`, after `6` fold challenges, with `4` folds. -/
theorem finInfo_rec20Jp : finInfo 0 0 cfgRec20Jp.levels = (1, 6, 4) := rfl

end
end LeanVM.Protocol.Whir.Sound
end
end

section
section
namespace LeanVM.Protocol.Whir.Sound
open LeanVM.Parameters LeanVM.Protocol.Compile LeanVM.Protocol.Verifier
  LeanVM.Protocol.Whir LeanVM.Protocol.EndToEnd Finset
section

/-- **The Johnson and the UD level-1 codes decode alike** (same `κ`, `R`, code; only the threshold
differs): X-REC2's `decodeRec1_of_ud` (stated on `decode (codesRec20 1)`, `codesRec20 1 = ud 9 3`) reads
the same message from a Johnson list member. -/
theorem decode_codeJ9R3_eq_ud {ρ : Type*} (V : ρ → Fin codeJ9R3.n → E) :
    decode codeJ9R3 V = decode (LevelCode.ud 9 3 (by norm_num) (by norm_num) (by norm_num)) V := rfl

/-- The two level-1 codes are the same submodule. -/
theorem code_codeJ9R3_eq_ud :
    codeJ9R3.code = (LevelCode.ud 9 3 (by norm_num) (by norm_num) (by norm_num)).code := rfl

end
end LeanVM.Protocol.Whir.Sound
end
end

section
set_option autoImplicit false
namespace Lvm.ASM
open RecursionFast Lvm.FS Lvm.T
open LeanVM.Parameters LeanVM.Protocol LeanVM.Protocol.Compile LeanVM.Protocol.Verifier
open LeanVM.Protocol.Compile.VerifierProgram LeanVM.Protocol.Whir.Sound LeanVM.Protocol.EndToEnd
open LeanVM.Protocol.Whir LeanVM.Protocol.Whir.Ud
open scoped NNReal ENNReal

/-- **`C_rec`'s UD level-1 code is J2′'s** (`κ = 9`, `R = 3`; only the threshold differs). -/
theorem codesRec20_one_code : (codesRec20 1).code = codeJ9R3.code := rfl

end Lvm.ASM
end

section
set_option autoImplicit false
namespace Lvm.ASM
open RecursionFast Lvm.FS Lvm.T
open LeanVM.Parameters LeanVM.Protocol LeanVM.Protocol.Compile LeanVM.Protocol.Verifier
open LeanVM.Protocol.Compile.VerifierProgram LeanVM.Protocol.Whir.Sound LeanVM.Protocol.EndToEnd
open LeanVM.Protocol.Whir LeanVM.Protocol.Whir.Ud
open scoped NNReal ENNReal
variable {mid : List UInt8 → VerifierProgram OpenClaims} {Good : GoodRel}

/-- **`extJ`'s map is the decoder chain** `recData2J` → `decodeRec1` → `decodeRec` (no choice). -/
theorem extJ_ext (hsh : MidShape mid) {VS : SProg} {vk : RecursionFast.Digest}
    {child : LeanVM.Protocol.Column 19 → Signed} (hnode : NodeSound VS vk Good child) :
    (extJ hsh hnode).ext = extSJ mid child := rfl

end Lvm.ASM
end

-- ===== from `LvmMPCert` =====

section
set_option autoImplicit false
namespace Lvm.ASM
open RecursionFast Lvm.FS Lvm.T
open LeanVM.Parameters
open LeanVM.Protocol.Compile hiding Proof Bytes
open LeanVM.Protocol.Verifier LeanVM.Protocol.Whir.Sound LeanVM.Protocol.EndToEnd
open LeanVM.Protocol.Whir (iList)
open scoped NNReal ENNReal
section Frozen
variable {mid : List UInt8 → VerifierProgram (List LeanVM.Protocol.Verifier.StackClaim)} {Good : GoodRelM} {Lm : ℝ≥0∞}

end Frozen
end Lvm.ASM
end

section
set_option autoImplicit false
namespace Lvm.ASM
open RecursionFast Lvm.FS Lvm.T
open LeanVM.Parameters
open LeanVM.Protocol.Compile hiding Proof Bytes
open LeanVM.Protocol.Verifier LeanVM.Protocol.Whir.Sound LeanVM.Protocol.EndToEnd
open LeanVM.Protocol.Whir (iList)
open scoped NNReal ENNReal
section Frozen
variable {mid : List UInt8 → VerifierProgram (List LeanVM.Protocol.Verifier.StackClaim)} {Good : GoodRelM} {Lm : ℝ≥0∞}

end Frozen
end Lvm.ASM
end

section
set_option autoImplicit false
namespace Lvm.ASM
open RecursionFast Lvm.FS Lvm.T
open LeanVM.Parameters
open LeanVM.Protocol.Compile hiding Proof Bytes
open LeanVM.Protocol.Verifier LeanVM.Protocol.Whir.Sound LeanVM.Protocol.EndToEnd
open LeanVM.Protocol.Whir (iList)
open scoped NNReal ENNReal
variable {mid : List UInt8 → VerifierProgram (List LeanVM.Protocol.Verifier.StackClaim)} {Good : GoodRelM} {Lm : ℝ≥0∞}
  {VS : SProg} {vk : RecursionFast.Digest}

/-- **Its error**: `εFS ≤ 2^-128`. -/
theorem εFS_kcertSM (hmid : MidSpecM mid Good εS Lm) (hLm : Lm ≤ εS) (hsh : MidShapeM mid)
    (X : ExtJM mid Good VS vk) : Scheme.εFS (kcertSM hmid hLm hsh X) ≤ (2 : ℝ≥0)⁻¹ ^ 128 :=
  Scheme.εFS_le_of _ (by
    show (0 : ℝ≥0) + (7 * (2 : ℝ≥0)⁻¹ ^ 131 + (2 : ℝ≥0)⁻¹ ^ 132) + (2 : ℝ≥0)⁻¹ ^ 139 ≤ (2 : ℝ≥0)⁻¹ ^ 128
    rw [← NNReal.coe_le_coe]; push_cast; norm_num)

/-- **M′'s open obligations** (as `OpenS`): the middle phases on `C_main` only, `NodeSoundM`, the refinement of
`V_S` to `PSWithM`, the executable extractor on good logs. -/
structure OpenSM (VS : SProg) (E : Digest → Proof → Log → Option Wit) : Type where
  mid : List UInt8 → VerifierProgram (List LeanVM.Protocol.Verifier.StackClaim)
  Good : GoodRelM
  Lm : ℝ≥0∞
  hmid : MidSpecM mid Good εS Lm
  hLm : Lm ≤ εS
  hsh : MidShapeM mid
  child : List UInt8 → List BF64 → Signed
  hnode : ∀ vk, NodeSoundM VS vk Good child
  refines : ∀ vk L c π, isS π = true → (VS vk c π).runLog L = some true →
    ((schemeS vk (PSWithM mid)).V c π).runLog L = some true
  ext_eq : ∀ vk L c π, isS π = true → L.length ≤ logCap →
    Lvm.FS.Scheme.μ (kcertSM hmid hLm hsh (extJM hsh (hnode vk))) L < 1 →
    ((schemeS vk (PSWithM mid)).V c π).runLog L = some true →
    (∃ w, E c π L = some w ∧ Rel (accV VS vk) c w) ∨
      E c π L = (schemeS vk (PSWithM mid)).Ex (kcertSM hmid hLm hsh (extJM hsh (hnode vk))).ext c π L

/-- **`SSound` from M′'s open obligations.** -/
theorem sSound_of_openSM {E : Digest → Proof → Log → Option Wit} (o : OpenSM VS E) (vk : Digest) :
    SSound VS E vk :=
  sSound_of VS E vk (PSWithM o.mid) (kcertSM o.hmid o.hLm o.hsh (extJM o.hsh (o.hnode vk)))
    (εFS_kcertSM o.hmid o.hLm o.hsh (extJM o.hsh (o.hnode vk))) (o.refines vk)
    fun L c π hS hl hμ hv ↦ o.ext_eq vk L c π hS hl hμ hv

end Lvm.ASM
end

section
set_option autoImplicit false
namespace Lvm.ASM
open RecursionFast Lvm.FS Lvm.T
open LeanVM.Parameters
open LeanVM.Protocol.Compile hiding Proof Bytes
open LeanVM.Protocol.Verifier LeanVM.Protocol.Whir.Sound LeanVM.Protocol.EndToEnd
open LeanVM.Protocol.Whir (iList)
open scoped NNReal ENNReal
variable {mid : List UInt8 → VerifierProgram (List LeanVM.Protocol.Verifier.StackClaim)} {Good : GoodRelM} {Lm : ℝ≥0∞}
  {VS : SProg} {vk : RecursionFast.Digest}

/-- **M′'s format** (S2GM): 24 bytes per read, `|π| = piSz`, `headerBytes` of header, `occOfS`. -/
def fmtM : SFmt := ⟨fun _ ↦ 24, fun _ ↦ by decide, piSz, Lvm.headerBytes, occOfS⟩

/-- **`schemeS` is the scheme at M′'s format.** -/
theorem schemeSW_fmtM (vk : RecursionFast.Digest) (P : List UInt8 → VerifierProgram Bool) :
    schemeSW fmtM vk P = schemeS vk P := rfl

end Lvm.ASM
end
