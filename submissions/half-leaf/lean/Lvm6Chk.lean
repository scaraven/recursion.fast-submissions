-- lvm6 (WP PF-0, docs/lvm6/design/PFW-framework.md §2.2–2.3): the `Chk` type for guard Bools and the region
-- table `Reg`/`chainB`. A leaf module (Lean core only), lifted from the PFW proof of concept §1 and §3.
--
-- Usage: a guard Bool and its statement are one term `c : Chk P`; the guard evaluates `c.b`, a theorem reads
-- `c.sound h : P`. Build it with `Chk.dec` (decidable fact), `Chk.ofBool b b_sound` (an existing Bool and its
-- lemma), `Chk.and`, `Chk.map` (rename into a named-field structure), `Chk.all` (a list), `Chk.below` (`i < n`).

set_option autoImplicit false

namespace Lvm6.Node

/-! ## `Chk`: a run-time Bool together with the fact it gives -/

/-- A run-time check of `P`: the Bool the guard evaluates (`b`) and its soundness. The statement is the type. -/
structure Chk (P : Prop) where
  /-- The Bool the guard evaluates. -/
  b : Bool
  /-- If the Bool holds, so does the statement. -/
  sound : b = true → P

namespace Chk

variable {P Q : Prop}

/-- A decidable fact, checked by `decide`. -/
def dec (P : Prop) [Decidable P] : Chk P := ⟨decide P, of_decide_eq_true⟩

/-- An existing Bool with its soundness lemma (for a Bool that needs a real proof). -/
def ofBool (b : Bool) (h : b = true → P) : Chk P := ⟨b, h⟩

/-- Both checks; the Bool is `a.b && c.b`. -/
def and (a : Chk P) (c : Chk Q) : Chk (P ∧ Q) :=
  ⟨a.b && c.b, fun h ↦ ⟨a.sound (Bool.and_eq_true_iff.mp h).1, c.sound (Bool.and_eq_true_iff.mp h).2⟩⟩

/-- Weaken or rename the statement (e.g. a nested `∧` into a named-field structure); the Bool is unchanged. -/
def map (f : P → Q) (a : Chk P) : Chk Q := ⟨a.b, fun h ↦ f (a.sound h)⟩

/-- A check for every element of a list. -/
def all {α : Type} {p : α → Prop} (l : List α) (f : ∀ a, Chk (p a)) : Chk (∀ a ∈ l, p a) :=
  ⟨l.all fun a ↦ (f a).b, fun h a ha ↦ (f a).sound (List.all_eq_true.mp h a ha)⟩

/-- A check for every index below `n`. -/
def below {p : Nat → Prop} (n : Nat) (f : ∀ i, Chk (p i)) : Chk (∀ i < n, p i) :=
  (all (List.range n) f).map fun h i hi ↦ h i (List.mem_range.mpr hi)

@[simp] theorem dec_b (P : Prop) [Decidable P] : (dec P).b = decide P := rfl

@[simp] theorem ofBool_b (b : Bool) (h : b = true → P) : (ofBool b h).b = b := rfl

@[simp] theorem and_b (a : Chk P) (c : Chk Q) : (a.and c).b = (a.b && c.b) := rfl

@[simp] theorem map_b (f : P → Q) (a : Chk P) : (a.map f).b = a.b := rfl

@[simp] theorem all_b {α : Type} {p : α → Prop} (l : List α) (f : ∀ a, Chk (p a)) :
    (all l f).b = l.all fun a ↦ (f a).b := rfl

@[simp] theorem below_b {p : Nat → Prop} (n : Nat) (f : ∀ i, Chk (p i)) :
    (below n f).b = (List.range n).all fun i ↦ (f i).b := rfl

end Chk

/-! ## Region tables: the instance by `decide`, the consequences once for every table -/

/-- A cell region `[base, base + size)`. -/
structure Reg where
  /-- First cell. -/
  base : Nat
  /-- Number of cells. -/
  size : Nat
  deriving DecidableEq, Repr

/-- Cell `n` lies in the region. -/
def Reg.Has (r : Reg) (n : Nat) : Prop := r.base ≤ n ∧ n < r.base + r.size

instance (r : Reg) (n : Nat) : Decidable (r.Has n) := inferInstanceAs (Decidable (_ ∧ _))

theorem Reg.has_iff {r : Reg} {n : Nat} : r.Has n ↔ r.base ≤ n ∧ n < r.base + r.size := Iff.rfl

/-- The regions follow each other in order from `lo` (gaps allowed) and the last one ends by `N`. -/
def chainB : Nat → List Reg → Nat → Bool
  | lo, [], N => decide (lo ≤ N)
  | lo, r :: rs, N => decide (lo ≤ r.base) && chainB (r.base + r.size) rs N

@[simp] theorem chainB_nil (lo N : Nat) : chainB lo [] N = decide (lo ≤ N) := rfl

@[simp] theorem chainB_cons (lo N : Nat) (r : Reg) (rs : List Reg) :
    chainB lo (r :: rs) N = (decide (lo ≤ r.base) && chainB (r.base + r.size) rs N) := rfl

/-- A checked table starts no later than it ends. -/
theorem chainB_le : ∀ {lo : Nat} {rs : List Reg} {N : Nat}, chainB lo rs N = true → lo ≤ N
  | _, [], _, h => of_decide_eq_true h
  | _, r :: rs, _, h => by
    simp only [chainB, Bool.and_eq_true, decide_eq_true_eq] at h
    have := chainB_le h.2
    omega

/-- In a checked table every region lies inside `[lo, N)`. -/
theorem chainB_mem : ∀ {lo : Nat} {rs : List Reg} {N : Nat}, chainB lo rs N = true →
    ∀ r ∈ rs, lo ≤ r.base ∧ r.base + r.size ≤ N
  | _, [], _, _, r, hr => by cases hr
  | lo, r' :: rs, N, h, r, hr => by
    simp only [chainB, Bool.and_eq_true, decide_eq_true_eq] at h
    rcases List.mem_cons.mp hr with rfl | hr
    · exact ⟨h.1, chainB_le h.2⟩
    · have := chainB_mem h.2 r hr
      omega

/-- **Generic**: in a checked table each region ends before every later one starts. -/
theorem chainB_pairwise : ∀ {lo : Nat} {rs : List Reg} {N : Nat}, chainB lo rs N = true →
    rs.Pairwise fun r s ↦ r.base + r.size ≤ s.base
  | _, [], _, _ => List.Pairwise.nil
  | _, r :: rs, _, h => by
    simp only [chainB, Bool.and_eq_true, decide_eq_true_eq] at h
    exact List.Pairwise.cons (fun s hs ↦ (chainB_mem h.2 s hs).1) (chainB_pairwise h.2)

/-- **Generic**: in a checked table, regions at different positions `i < j` share no cell. -/
theorem Reg.disjoint {lo N : Nat} {rs : List Reg} (h : chainB lo rs N = true) {i j : Nat} (hij : i < j)
    (hj : j < rs.length) {n : Nat} (hi : (rs[i]'(Nat.lt_trans hij hj)).Has n) : ¬ (rs[j]).Has n := by
  have := (List.pairwise_iff_getElem.mp (chainB_pairwise h)) i j (Nat.lt_trans hij hj) hj hij
  intro hn
  simp only [Reg.Has] at hi hn
  omega

/-! ## Examples -/

section Examples

/-- An existing guard Bool with its own soundness lemma. -/
private def evenB (n : Nat) : Bool := n % 2 == 0

private theorem evenB_sound {n : Nat} (h : evenB n = true) : n % 2 = 0 := by
  simpa [evenB] using h

/-- Wrap the Bool with `ofBool`, join a decidable fact with `and`; the guard runs `.b`, the proof uses `.sound`. -/
example : 4 % 2 = 0 ∧ 3 < 5 :=
  let c : Chk (4 % 2 = 0 ∧ 3 < 5) := (Chk.ofBool (evenB 4) evenB_sound).and (Chk.dec _)
  c.sound (by decide)

/-- `all` over a list and `below` over indices; the Bool is the obvious one (`simp` lemmas). -/
example : (Chk.all [2, 4, 6] fun a ↦ Chk.ofBool (evenB a) evenB_sound).b = true ∧
    (Chk.below (p := fun i ↦ i * 0 = 0) 3 fun _ ↦ Chk.dec _).b = true := by
  decide

/-- A region table checked once by `decide`; disjointness of any two rows then needs no arithmetic. -/
example {n : Nat} (h : (⟨0, 4⟩ : Reg).Has n) : ¬ (⟨6, 2⟩ : Reg).Has n :=
  Reg.disjoint (lo := 0) (N := 8) (rs := [⟨0, 4⟩, ⟨4, 2⟩, ⟨6, 2⟩]) (i := 0) (j := 2) (by decide) (by decide)
    (by decide) h

end Examples

end Lvm6.Node
