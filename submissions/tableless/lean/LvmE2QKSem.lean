-- New for lvm2 E2F (slice S1, E2F-QH1): the program logic of `E2` templates (twin rows) and the specs of the `E2`
-- template gadgets (`LvmE2QKTB`'s primitives and list combinators), the `E2` counterpart of `LvmQKeccakTB`'s
-- `THold` logic and specs.
import LvmE2QKTB

/-!
# `E2` templates: program logic and gadget specs

`THold2 xv V n δ`: the instructions `δ` placed at `n` hold in `V`, the `E2` twin rows included (`Ins.evalF2`: row
`e2 f h` holds coordinate `h` of `f`'s `E2` value at its `K` operands, as `LRel` states it). **`thold2_of_loop`**:
a loop of a template holds it at each iteration; `thold2_bind` splits it along `>>=`.

An `E2` operand's value is `S2.valF` (the two `K` coordinates). Each gadget's spec is stated as
`THold2 xv V n (g n).2 → value = …` in `FE2`'s field: `q2Mul_spec` (`a·b + d`), `q2Lin_spec`, `q2Add_spec`,
`q2One_spec`, `q2Scale_spec`, `q2Copy_spec`, `q2Base_spec` (zero and one), and the list combinators
`q2Sum_spec`, `q2Dot_spec`, `q2Horner_spec`, `q2EqTab_spec`, `mapT2_spec`, `q2SumMap_spec`; `q2Assert_spec`
for the coordinatewise assertion.
-/

set_option autoImplicit false

namespace Lvm.Q1

open Lvm Lvm.Loop Lvm.Loop.Build

/-! ## Program logic -/

/-- An instruction's value on `V`, `E2` twin rows included. -/
def Ins.evalF2 (xv : Src → FE) (V : Nat → FE) (i : Ins) : FE :=
  match i.op with
  | .e2 f h => FE.ofK ((f.val fun o => (Src.valF xv V (i.args.getD o default)).c₀).coord h)
  | _ => i.evalF xv V

/-- The ops whose relation `evalF2` states. -/
def Ins.arith2 (i : Ins) : Prop := i.arith ∨ ∃ f h, i.op = .e2 f h

/-- **The instructions `δ` placed at `n` hold in `V`** (twin rows included). -/
def THold2 (xv : Src → FE) (V : Nat → FE) (n : Nat) (δ : List Ins) : Prop :=
  ∀ k < δ.length, (δ.getD k default).arith2 → V (n + k) = (δ.getD k default).evalF2 xv V

theorem evalF2_of_arith {xv : Src → FE} {V : Nat → FE} {i : Ins} (h : i.arith) : i.evalF2 xv V = i.evalF xv V := by
  unfold Ins.evalF2
  rcases h with h1 | ⟨a, b, h1⟩ | h1 <;> simp only [h1]

/-- **A loop of a template holds the template** at each iteration, twin rows included. -/
theorem thold2_of_loop {c : Ctx} {M : Mem} {dims : List Nat} {ins : List Ins} {p : Ptr}
    (h : SegsHold c M p (loop dims (tplOf ins) p).2) {jf : Nat} (hjf : jf < 2 ^ dims.sum) :
    THold2 (iterXv M (loop dims (tplOf ins) p).1 jf) (iterF M (loop dims (tplOf ins) p).1 jf) 0 ins := by
  intro t ht hw
  rcases hw with hw | ⟨f, hh, he⟩
  · rw [evalF2_of_arith hw]
    exact thold_of_loop h hjf t ht hw
  · rw [Nat.zero_add]
    have hrel := loop_rel h hjf (t := t) (by simpa [tplOf] using ht)
    have harg : ∀ k, LoopOut.arg M (loop dims (tplOf ins) p).1 jf t k =
        ((ins.getD t default).args.getD k default).valF (iterXv M (loop dims (tplOf ins) p).1 jf)
          (iterF M (loop dims (tplOf ins) p).1 jf) := by
      intro k
      simp only [LoopOut.arg]
      show (((tplOf ins).getD t default).args.getD k default).val M _ jf = _
      rw [tplOf_getD ins ht, Ins.toLRow, getD_map_default Src.toOpd rfl]
      cases ((ins.getD t default).args.getD k default) with
      | loc k' => rw [Src.toOpd, Opd.val_cur M _ hjf]; rfl
      | prev k' => rfl
      | ext a => rfl
    unfold LRel at hrel
    simp only [harg] at hrel
    have hop : ((loop dims (tplOf ins) p).1.tpl.getD t default).op = (ins.getD t default).op := by
      show ((tplOf ins).getD t default).op = _
      rw [tplOf_getD ins ht]; rfl
    rw [hop, he] at hrel
    unfold Ins.evalF2
    rw [he]
    exact hrel

theorem thold2_append {xv : Src → FE} {V : Nat → FE} {n : Nat} {δ₁ δ₂ : List Ins} :
    THold2 xv V n (δ₁ ++ δ₂) ↔ THold2 xv V n δ₁ ∧ THold2 xv V (n + δ₁.length) δ₂ := by
  constructor
  · intro h
    refine ⟨fun k hk hw => ?_, fun k hk hw => ?_⟩
    · have e : (δ₁ ++ δ₂).getD k default = δ₁.getD k default := by
        simp [List.getD_eq_getElem?_getD, List.getElem?_append_left hk]
      rw [← e] at hw ⊢
      exact h k (by simp; omega) hw
    · have e : (δ₁ ++ δ₂).getD (δ₁.length + k) default = δ₂.getD k default := by
        simp [List.getD_eq_getElem?_getD, List.getElem?_append_right]
      rw [← e] at hw ⊢
      rw [Nat.add_assoc]
      exact h _ (by simp; omega) hw
  · rintro ⟨h₁, h₂⟩ k hk hw
    by_cases hk1 : k < δ₁.length
    · have e : (δ₁ ++ δ₂).getD k default = δ₁.getD k default := by
        simp [List.getD_eq_getElem?_getD, List.getElem?_append_left hk1]
      rw [e] at hw ⊢
      exact h₁ k hk1 hw
    · obtain ⟨k', rfl⟩ : ∃ k', k = δ₁.length + k' := ⟨k - δ₁.length, by omega⟩
      have e : (δ₁ ++ δ₂).getD (δ₁.length + k') default = δ₂.getD k' default := by
        simp [List.getD_eq_getElem?_getD, List.getElem?_append_right]
      rw [e] at hw ⊢
      rw [← Nat.add_assoc]
      exact h₂ k' (by simp at hk; omega) hw

/-- **Composition**: a bind holds iff both parts hold at their positions. -/
theorem thold2_bind {α β : Type} {xv : Src → FE} {V : Nat → FE} {n : Nat} (m : TB α) (f : α → TB β) :
    THold2 xv V n ((m >>= f) n).2 ↔
      THold2 xv V n (m n).2 ∧ THold2 xv V (n + (m n).2.length) (f (m n).1 (n + (m n).2.length)).2 := by
  rw [tb_bind]; exact thold2_append

/-! ## Values -/

/-- The value of an `E2` operand. -/
def S2.valF (xv : Src → FE) (V : Nat → FE) (s : S2) : FE2 := ⟨(s.1.valF xv V).c₀, (s.2.valF xv V).c₀⟩

/-- The values of a list of `E2` operands. -/
abbrev vals2 (xv : Src → FE) (V : Nat → FE) (l : List S2) : List FE2 := l.map (S2.valF xv V)

theorem fe_ofK_c0 (k : FK) : (FE.ofK k).c₀ = k := rfl

/-- **A twin pair's value** is `f`'s at its operands. -/
theorem emit2_spec {xv : Src → FE} {V : Nat → FE} {n : Nat} {f : E2Fn} {xs : List S2}
    (h : THold2 xv V n (emit2 f xs n).2) :
    (emit2 f xs n).1.valF xv V = f.val fun o => ((s2Args xs).getD o default |>.valF xv V).c₀ := by
  have h0 := h 0 (by simp [emit2, e2I]) (Or.inr ⟨f, false, by simp [emit2, e2I]⟩)
  have h1 := h 1 (by simp [emit2, e2I]) (Or.inr ⟨f, true, by simp [emit2, e2I]⟩)
  simp only [emit2, e2I, List.getD_cons_zero, List.getD_cons_succ, Ins.evalF2, Nat.add_zero] at h0 h1
  apply FE2.ext_coord
  · show (V n).c₀ = _; rw [h0]; rfl
  · show (V (n + 1)).c₀ = _; rw [h1]; rfl

theorem q2Mul_spec {xv : Src → FE} {V : Nat → FE} {n : Nat} {a b d : S2} (h : THold2 xv V n (q2Mul a b d n).2) :
    (q2Mul a b d n).1.valF xv V = a.valF xv V * b.valF xv V + d.valF xv V := by
  rw [q2Mul, emit2_spec h]; rfl

theorem q2Lin_spec {xv : Src → FE} {V : Nat → FE} {n : Nat} {k : FK} {k' : FE2} {a b : S2}
    (h : THold2 xv V n (q2Lin k k' a b n).2) :
    (q2Lin k k' a b n).1.valF xv V = a.valF xv V + FE2.ofK k * b.valF xv V + k' := by
  rw [q2Lin, emit2_spec h]; rfl

theorem fe2_add_self (x : FE2) : x + x = 0 := by
  apply FE2.ext_coord <;> simp only [FE2.add_def, FE2.coord_false, FE2.coord_true] <;> exact fk_add_self _

theorem fe2_ofK_one : FE2.ofK 1 = 1 := rfl
theorem fe2_ofK_zero : FE2.ofK 0 = 0 := rfl

theorem fe2_ofK_add (a b : FK) : FE2.ofK (a + b) = FE2.ofK a + FE2.ofK b := map_add FE2.ofKRingHom a b

theorem q2Add_spec {xv : Src → FE} {V : Nat → FE} {n : Nat} {a b : S2} (h : THold2 xv V n (q2Add a b n).2) :
    (q2Add a b n).1.valF xv V = a.valF xv V + b.valF xv V := by
  rw [q2Add, q2Lin_spec h, fe2_ofK_one, one_mul, add_zero]

theorem q2One_spec {xv : Src → FE} {V : Nat → FE} {n : Nat} {a : S2} (h : THold2 xv V n (q2One a n).2) :
    (q2One a n).1.valF xv V = 1 + a.valF xv V := by
  rw [q2One, q2Lin_spec h, fe2_ofK_zero, zero_mul, add_zero, add_comm]

theorem q2Scale_spec {xv : Src → FE} {V : Nat → FE} {n : Nat} {k : FK} {a : S2}
    (h : THold2 xv V n (q2Scale k a n).2) : (q2Scale k a n).1.valF xv V = FE2.ofK k * a.valF xv V := by
  rw [q2Scale, q2Lin_spec h, add_zero, fe2_ofK_add, fe2_ofK_one]
  have := fe2_add_self (a.valF xv V)
  calc a.valF xv V + (FE2.ofK k + 1) * a.valF xv V = FE2.ofK k * a.valF xv V + (a.valF xv V + a.valF xv V) := by
        ring
    _ = _ := by rw [this, add_zero]

theorem q2Copy_spec {xv : Src → FE} {V : Nat → FE} {n : Nat} {a : S2} (h : THold2 xv V n (q2Copy a n).2) :
    (q2Copy a n).1.valF xv V = a.valF xv V := by
  rw [q2Copy, q2Lin_spec h, fe2_ofK_zero, zero_mul, add_zero, add_zero]

/-- A `K` row's value. -/
theorem kLin_spec {xv : Src → FE} {V : Nat → FE} {n : Nat} {k k' : FK} {a b : Src}
    (h : THold2 xv V n (kLin k k' a b n).2) :
    (kLin k k' a b n).1.valF xv V = a.valF xv V + FE.ofK k * b.valF xv V + FE.ofK k' := by
  have := h 0 (by simp [kLin, emit]) (Or.inl (Or.inr (Or.inl ⟨k, k', rfl⟩)))
  simpa [kLin, emit, Src.valF, Ins.evalF2, Ins.evalF] using this

theorem fe_c0_add (a b : FE) : (a + b).c₀ = a.c₀ + b.c₀ := rfl

/-- **The zeros**: `zK` is `0`, the `E2` zero is `0`, the `E2` one is `1`. -/
theorem q2Base_spec {xv : Src → FE} {V : Nat → FE} {n : Nat} {b : Src} (h : THold2 xv V n (q2Base b n).2) :
    ((q2Base b n).1.1.valF xv V).c₀ = 0 ∧ (q2Base b n).1.2.1.valF xv V = 0 ∧ (q2Base b n).1.2.2.valF xv V = 1 := by
  have e : q2Base b n = ((.loc n, (.loc n, .loc n), (.loc (n + 1), .loc n)),
      [⟨.lin 1 0, .K, [b, b]⟩, ⟨.lin 0 1, .K, [.loc n, .loc n]⟩]) := rfl
  rw [e] at h ⊢
  have hA := h 0 (by simp) (Or.inl (Or.inr (Or.inl ⟨1, 0, rfl⟩)))
  have hB := h 1 (by simp) (Or.inl (Or.inr (Or.inl ⟨0, 1, rfl⟩)))
  simp only [List.getD_cons_zero, List.getD_cons_succ, Ins.evalF2, Ins.evalF, Nat.add_zero, List.getD_cons_zero,
    Src.valF] at hA hB
  have z : V n = 0 := by
    rw [hA, show FE.ofK 1 = 1 from rfl, show FE.ofK 0 = 0 from rfl, one_mul, add_zero, FE_add_self]
  have o : V (n + 1) = 1 := by
    rw [hB, z, show FE.ofK 1 = 1 from rfl, show FE.ofK 0 = 0 from rfl, zero_mul, zero_add, zero_add]
  refine ⟨?_, ?_, ?_⟩
  · show (V n).c₀ = 0; rw [z]; rfl
  · show (⟨(V n).c₀, (V n).c₀⟩ : FE2) = 0; rw [z]; rfl
  · show (⟨(V (n + 1)).c₀, (V n).c₀⟩ : FE2) = 1; rw [z, o]; rfl

/-! ## Assertions -/

theorem q2Assert_spec {xv : Src → FE} {V : Nat → FE} {n : Nat} {a : S2} {gate : Src}
    (h : TAssert xv V (q2Assert a gate n).2) :
    gate.valF xv V * a.1.valF xv V = 0 ∧ gate.valF xv V * a.2.valF xv V = 0 := by
  obtain ⟨h1, h2⟩ := (tassert_bind _ _).mp h
  exact ⟨gAssert_spec h1, gAssert_spec h2⟩

/-! ## Lists -/

theorem mapT2_spec {α β : Type} {xv : Src → FE} {V : Nat → FE} {f : α → TB β} {P : α → β → Prop}
    (hf : ∀ a n, THold2 xv V n (f a n).2 → P a (f a n).1) :
    ∀ (as : List α) (n : Nat), THold2 xv V n (mapT2 f as n).2 → List.Forall₂ P as (mapT2 f as n).1
  | [], _, _ => List.Forall₂.nil
  | a :: as, n, h => by
    simp only [mapT2, tb_bind, tb_pure, List.append_nil] at h ⊢
    rw [thold2_append] at h
    exact List.Forall₂.cons (hf a n h.1) (mapT2_spec hf as _ h.2)

theorem mapT2_length {α β : Type} (f : α → TB β) : ∀ (as : List α) (n : Nat), (mapT2 f as n).1.length = as.length
  | [], _ => rfl
  | a :: as, n => by
    simp only [mapT2, tb_bind, tb_pure, List.length_cons]
    rw [mapT2_length f as]

theorem forall₂_map_eq2 {α : Type} {g : α → FE2} {h : S2 → FE2} :
    ∀ {as : List α} {bs : List S2}, List.Forall₂ (fun a s => h s = g a) as bs → bs.map h = as.map g
  | [], [], _ => rfl
  | _ :: _, _ :: _, List.Forall₂.cons h1 h2 => by simp [h1, forall₂_map_eq2 h2]

theorem q2Sum_spec {xv : Src → FE} {V : Nat → FE} : ∀ (s : S2) (cs : List S2) (n : Nat),
    THold2 xv V n (q2Sum s cs n).2 → (q2Sum s cs n).1.valF xv V = s.valF xv V + (vals2 xv V cs).sum
  | s, [], n, _ => by simp [q2Sum, tb_pure]
  | s, c :: cs, n, h => by
    simp only [q2Sum] at h ⊢
    rw [thold2_bind] at h
    rw [tb_bind, q2Sum_spec _ cs _ h.2, q2Add_spec h.1]
    simp [add_assoc]

theorem q2Dot_spec {xv : Src → FE} {V : Nat → FE} : ∀ (acc : S2) (cds : List (S2 × S2)) (n : Nat),
    THold2 xv V n (q2Dot acc cds n).2 →
      (q2Dot acc cds n).1.valF xv V = acc.valF xv V + (cds.map fun cd => cd.1.valF xv V * cd.2.valF xv V).sum
  | acc, [], n, _ => by simp [q2Dot, tb_pure]
  | acc, cd :: rest, n, h => by
    simp only [q2Dot] at h ⊢
    rw [thold2_bind] at h
    rw [tb_bind, q2Dot_spec _ rest _ h.2, q2Mul_spec h.1]
    simp only [List.map_cons, List.sum_cons]
    ring

/-- Horner's value at `E2`. -/
def hornerVal2 (x h : FE2) (cs : List FE2) : FE2 := cs.foldl (fun acc c => acc * x + c) h

theorem q2Horner_spec {xv : Src → FE} {V : Nat → FE} (x : S2) : ∀ (h : S2) (cs : List S2) (n : Nat),
    THold2 xv V n (q2Horner x h cs n).2 →
      (q2Horner x h cs n).1.valF xv V = hornerVal2 (x.valF xv V) (h.valF xv V) (vals2 xv V cs)
  | h, [], n, _ => by simp [q2Horner, tb_pure, hornerVal2]
  | h, c :: cs, n, hh => by
    simp only [q2Horner] at hh ⊢
    rw [thold2_bind] at hh
    rw [tb_bind, q2Horner_spec x _ cs _ hh.2, q2Mul_spec hh.1]
    rfl

theorem q2One_fst (r : S2) (n : Nat) : (q2One r n).1 = (.loc n, .loc (n + 1)) := rfl

theorem q2EqStep_spec {xv : Src → FE} {V : Nat → FE} {z : S2} (hz : z.valF xv V = 0) (tab : List S2) (r : S2)
    (n : Nat) (h : THold2 xv V n (q2EqStep z tab r n).2) :
    vals2 xv V (q2EqStep z tab r n).1 =
      (vals2 xv V tab).map (· * (1 + r.valF xv V)) ++ (vals2 xv V tab).map (· * r.valF xv V) := by
  obtain ⟨h1, h'⟩ := (thold2_bind _ _).mp h
  obtain ⟨h2, h''⟩ := (thold2_bind _ _).mp h'
  obtain ⟨h3, -⟩ := (thold2_bind _ _).mp h''
  have e1 : (q2One r n).1.valF xv V = 1 + r.valF xv V := q2One_spec h1
  have k2 := mapT2_spec (P := fun e s => S2.valF xv V s = e.valF xv V * (1 + r.valF xv V))
    (fun a m hm => by rw [q2Mul_spec hm, e1, hz, add_zero]) tab _ h2
  have k3 := mapT2_spec (P := fun e s => S2.valF xv V s = e.valF xv V * r.valF xv V)
    (fun a m hm => by rw [q2Mul_spec hm, hz, add_zero]) tab _ h3
  simp only [q2EqStep, tb_bind, tb_pure, vals2] at k2 k3 ⊢
  rw [List.map_append, forall₂_map_eq2 k2, forall₂_map_eq2 k3, List.map_map, List.map_map]
  rfl

theorem q2EqTab_spec {xv : Src → FE} {V : Nat → FE} {z : S2} (hz : z.valF xv V = 0) :
    ∀ (pt tab : List S2) (n : Nat), THold2 xv V n (q2EqTab z tab pt n).2 →
      vals2 xv V (q2EqTab z tab pt n).1 =
        (vals2 xv V pt).foldl (fun out r => out.map (· * (1 + r)) ++ out.map (· * r)) (vals2 xv V tab)
  | [], tab, n, _ => by simp [q2EqTab, tb_pure]
  | r :: rs, tab, n, h => by
    simp only [q2EqTab] at h ⊢
    rw [thold2_bind] at h
    rw [tb_bind, q2EqTab_spec hz rs _ _ h.2, q2EqStep_spec hz tab r n h.1]
    rfl

theorem q2SumMap_spec {xv : Src → FE} {V : Nat → FE} {z : S2} (hz : z.valF xv V = 0) {k : Nat}
    {f : Nat → TB S2} {F : Nat → FE2} (hf : ∀ c < k, ∀ n, THold2 xv V n (f c n).2 → (f c n).1.valF xv V = F c)
    (n : Nat) (h : THold2 xv V n (q2SumMap z k f n).2) :
    (q2SumMap z k f n).1.valF xv V = ((List.range k).map F).sum := by
  obtain ⟨h1, h2⟩ := (thold2_bind _ _).mp h
  have k1 : ∀ (cs : List Nat), (∀ c ∈ cs, c < k) → ∀ m, THold2 xv V m (mapT2 f cs m).2 →
      List.Forall₂ (fun c s => S2.valF xv V s = F c) cs (mapT2 f cs m).1 := by
    intro cs
    induction cs with
    | nil => intro _ _ _; exact List.Forall₂.nil
    | cons c cs ih =>
      intro hc m hm
      simp only [mapT2, tb_bind, tb_pure, List.append_nil] at hm ⊢
      rw [thold2_append] at hm
      exact List.Forall₂.cons (hf c (hc c (by simp)) m hm.1)
        (ih (fun d hd => hc d (by simp [hd])) _ hm.2)
  have k2 := k1 (List.range k) (fun c hc => List.mem_range.mp hc) n h1
  rw [q2SumMap, tb_bind, q2Sum_spec _ _ _ h2, hz, zero_add]
  exact congrArg List.sum (forall₂_map_eq2 k2)

end Lvm.Q1
