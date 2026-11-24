import LvmQKeccakConst
import LvmQEqKeccakAlg3
import LvmQSumcheck
import LvmQEqKeccakRead

-- ===== merged from `LvmQKeccakTB` (GOLF module merge: `LvmQKeccakTB.lean` is now a stub importing `LvmQKeccakLayer`) =====
section

/-!
# QA1: a builder for loop templates (`TB`) and its program logic (`THold`)

Large loop templates (the Keccak layer) are written as programs `TB α = Nat → α × List Ins`: given
the position of the next instruction, they return their result (operands `Src`) and the
instructions they emit; `emit i` returns `loc n`. The program logic mirrors QL's `SegsHold`: on a
fixed point `V` of the whole template (`Fix`, what `fix_of_loop` gives for a loop's iteration),
`THold xv V n δ` says the instructions `δ` placed at `n` hold. **`thold_of_fix`** gives it for the
whole template; `thold_bind` splits it along `>>=`; each gadget's spec is stated as
`THold xv V n (g n).2 → P (g n).1`.
-/

set_option autoImplicit false

namespace Lvm.Q1

open Lvm Lvm.Loop Lvm.Loop.Build

/-- A template program: from the next position, its result and its instructions. -/
def TB (α : Type) : Type := Nat → α × List Ins

instance : Monad TB where
  pure a := fun _ => (a, [])
  bind m f := fun n =>
    let r := m n
    let r' := f r.1 (n + r.2.length)
    (r'.1, r.2 ++ r'.2)

/-- Emit one instruction; its result is `loc n`. -/
def emit (i : Ins) : TB Src := fun n => (.loc n, [i])

/-- Emit an assertion (no result). -/
def emitA (i : Ins) : TB Unit := fun _ => ((), [i])

theorem tb_bind {α β : Type} (m : TB α) (f : α → TB β) (n : Nat) :
    (m >>= f) n = ((f (m n).1 (n + (m n).2.length)).1, (m n).2 ++ (f (m n).1 (n + (m n).2.length)).2) := rfl

theorem tb_pure {α : Type} (a : α) (n : Nat) : (pure a : TB α) n = (a, []) := rfl

/-- An operand's value: `V k` for `loc k`, `xv` for the others (values as a function). -/
def Src.valF (xv : Src → FE) (V : Nat → FE) : Src → FE
  | .loc k => V k
  | s => xv s

/-- An instruction's value on `V`. -/
def Ins.evalF (xv : Src → FE) (V : Nat → FE) (i : Ins) : FE :=
  let a (o : Nat) : FE := Src.valF xv V (i.args.getD o default)
  match i.op with
  | .muladd => a 0 * a 1 + a 2
  | .lin k k' => a 0 + FE.ofK k * a 1 + FE.ofK k'
  | .loadE => a 0 + FE.y * a 1 + FE.y * FE.y * a 2
  | _ => 0

/-- The ops whose relation `evalF` states. -/
def Ins.arith (i : Ins) : Prop := i.op = .muladd ∨ (∃ k k', i.op = .lin k k') ∨ i.op = .loadE

/-- **The instructions `δ` placed at `n` hold in `V`**: every arithmetic one's value is its
evaluation. -/
def THold (xv : Src → FE) (V : Nat → FE) (n : Nat) (δ : List Ins) : Prop :=
  ∀ k < δ.length, (δ.getD k default).arith → V (n + k) = (δ.getD k default).evalF xv V

/-- Iteration `jf`'s cells as a function. -/
def iterF (M : Mem) (o : LoopOut) (jf : Nat) (t : Nat) : FE := (o.cell t jf).val M

/-- **A loop of a template holds the template** at each iteration (no well-formedness needed:
`cur k` reads row `k`'s cell whatever `k`). -/
theorem thold_of_loop {c : Ctx} {M : Mem} {dims : List Nat} {ins : List Ins} {p : Ptr}
    (h : SegsHold c M p (loop dims (tplOf ins) p).2) {jf : Nat} (hjf : jf < 2 ^ dims.sum) :
    THold (iterXv M (loop dims (tplOf ins) p).1 jf) (iterF M (loop dims (tplOf ins) p).1 jf) 0 ins := by
  intro t ht hw
  rw [Nat.zero_add]
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
  rw [hop] at hrel
  unfold Ins.evalF
  rcases hw with h1 | ⟨a, b, h1⟩ | h1 <;> simp only [h1] at hrel ⊢ <;> exact hrel

theorem thold_of_loopP {c : Ctx} {M : Mem} {dims : List Nat} {ins : List Ins} {init : Nat → Cell} {p : Ptr}
    (h : SegsHold c M p (loopP dims (tplOf ins) init p).2) {jf : Nat} (hjf : jf < 2 ^ dims.sum) :
    THold (iterXv M (loopP dims (tplOf ins) init p).1 jf) (iterF M (loopP dims (tplOf ins) init p).1 jf) 0 ins := by
  rw [loopP_fst]
  exact thold_of_loop (hold_loop_of_loopP h) hjf

theorem thold_append {xv : Src → FE} {V : Nat → FE} {n : Nat} {δ₁ δ₂ : List Ins} :
    THold xv V n (δ₁ ++ δ₂) ↔ THold xv V n δ₁ ∧ THold xv V (n + δ₁.length) δ₂ := by
  constructor
  · intro h
    refine ⟨fun k hk hw => ?_, fun k hk hw => ?_⟩
    · have e : (δ₁ ++ δ₂).getD k default = δ₁.getD k default := by
        exact List.getD_append _ _ _ _ hk
      rw [← e] at hw ⊢
      exact h k (by simp; (clear * - hk; omega)) hw
    · have e : (δ₁ ++ δ₂).getD (δ₁.length + k) default = δ₂.getD k default := by
        rw [List.getD_append_right _ _ _ _ (Nat.le_add_right _ _), Nat.add_sub_cancel_left]
      rw [← e] at hw ⊢
      rw [Nat.add_assoc]
      exact h _ (by simp; omega) hw
  · rintro ⟨h₁, h₂⟩ k hk hw
    by_cases hk1 : k < δ₁.length
    · have e : (δ₁ ++ δ₂).getD k default = δ₁.getD k default := by
        exact List.getD_append _ _ _ _ hk1
      rw [e] at hw ⊢
      exact h₁ k hk1 hw
    · obtain ⟨k', rfl⟩ : ∃ k', k = δ₁.length + k' := ⟨k - δ₁.length, by (clear * - hk1; omega)⟩
      have e : (δ₁ ++ δ₂).getD (δ₁.length + k') default = δ₂.getD k' default := by
        rw [List.getD_append_right _ _ _ _ (Nat.le_add_right _ _), Nat.add_sub_cancel_left]
      rw [e] at hw ⊢
      rw [← Nat.add_assoc]
      exact h₂ k' (by simp at hk; omega) hw

/-- **Composition**: a bind holds iff both parts hold at their positions. -/
theorem thold_bind {α β : Type} {xv : Src → FE} {V : Nat → FE} {n : Nat} (m : TB α) (f : α → TB β) :
    THold xv V n ((m >>= f) n).2 ↔
      THold xv V n (m n).2 ∧ THold xv V (n + (m n).2.length) (f (m n).1 (n + (m n).2.length)).2 := by
  rw [tb_bind]; exact thold_append

/-- **One instruction**: its result's value is its evaluation. -/
theorem emit_spec {xv : Src → FE} {V : Nat → FE} {n : Nat} {i : Ins} (hw : i.arith)
    (h : THold xv V n (emit i n).2) : (emit i n).1.valF xv V = i.evalF xv V := by
  have := h 0 (by simp [emit]) (by simpa [emit] using hw)
  simpa [emit, Src.valF] using this

/-! ## Primitive gadgets (all results in `E`) -/

/-- `a·b + d`. -/
def gMul (a b d : Src) : TB Src := emit (mulI a b d)
/-- `a + b`. -/
def gAdd (a b : Src) : TB Src := emit (addI a b)
/-- `a + k·b + k'`. -/
def gLin (k k' : FK) (a b : Src) : TB Src := emit (linI k k' a b)
/-- `1 + a`. -/
def gOne (a : Src) : TB Src := gLin 0 1 a a
/-- `0` (`a + a`). -/
def gZero (a : Src) : TB Src := gLin 1 0 a a
/-- `k·a` for a constant `k ∈ K` (`a + (k + 1)·a`). -/
def gScale (k : FK) (a : Src) : TB Src := gLin (k + 1) 0 a a
/-- A stream scalar: `loadE` of lanes `q, q+1, q+2`, moving by `str` per loop step. -/
def gLoad (q : Nat) (str : List Nat) : TB Src := emit (loadI q str)

theorem gMul_spec {xv : Src → FE} {V : Nat → FE} {n : Nat} {a b d : Src} (h : THold xv V n (gMul a b d n).2) :
    (gMul a b d n).1.valF xv V = a.valF xv V * b.valF xv V + d.valF xv V := by
  rw [gMul, emit_spec (Or.inl rfl) h]; rfl

theorem gAdd_spec {xv : Src → FE} {V : Nat → FE} {n : Nat} {a b : Src} (h : THold xv V n (gAdd a b n).2) :
    (gAdd a b n).1.valF xv V = a.valF xv V + b.valF xv V := by
  rw [gAdd, emit_spec (Or.inr (Or.inl ⟨1, 0, rfl⟩)) h]
  show _ + FE.ofK 1 * _ + FE.ofK 0 = _
  rw [show FE.ofK 1 = 1 from rfl, show FE.ofK 0 = 0 from rfl, one_mul, add_zero]; rfl

theorem gLin_spec {xv : Src → FE} {V : Nat → FE} {n : Nat} {k k' : FK} {a b : Src}
    (h : THold xv V n (gLin k k' a b n).2) :
    (gLin k k' a b n).1.valF xv V = a.valF xv V + FE.ofK k * b.valF xv V + FE.ofK k' := by
  rw [gLin, emit_spec (Or.inr (Or.inl ⟨k, k', rfl⟩)) h]; rfl

theorem FE_add_self (x : FE) : x + x = 0 := CharTwo.add_self_eq_zero x

theorem gOne_spec {xv : Src → FE} {V : Nat → FE} {n : Nat} {a : Src} (h : THold xv V n (gOne a n).2) :
    (gOne a n).1.valF xv V = 1 + a.valF xv V := by
  rw [gOne, gLin_spec h, show FE.ofK 0 = 0 from rfl, show FE.ofK 1 = 1 from rfl]; ring

theorem gZero_spec {xv : Src → FE} {V : Nat → FE} {n : Nat} {a : Src} (h : THold xv V n (gZero a n).2) :
    (gZero a n).1.valF xv V = 0 := by
  rw [gZero, gLin_spec h, show FE.ofK 0 = 0 from rfl, show FE.ofK 1 = 1 from rfl, one_mul, add_zero,
    FE_add_self]

theorem gScale_spec {xv : Src → FE} {V : Nat → FE} {n : Nat} {k : FK} {a : Src}
    (h : THold xv V n (gScale k a n).2) : (gScale k a n).1.valF xv V = FE.ofK k * a.valF xv V := by
  rw [gScale, gLin_spec h, show FE.ofK 0 = 0 from rfl, add_zero,
    show FE.ofK (k + 1) = FE.ofK k + 1 from map_add FE.ofKRingHom k 1]
  have := FE_add_self (a.valF xv V)
  calc a.valF xv V + (FE.ofK k + 1) * a.valF xv V = FE.ofK k * a.valF xv V + (a.valF xv V + a.valF xv V) := by ring
    _ = _ := by rw [this, add_zero]

theorem gLoad_spec {xv : Src → FE} {V : Nat → FE} {n q : Nat} {str : List Nat} (h : THold xv V n (gLoad q str n).2) :
    (gLoad q str n).1.valF xv V = xv (.ext ⟨.K, q, str⟩) + FE.y * xv (.ext ⟨.K, q + 1, str⟩) +
      FE.y * FE.y * xv (.ext ⟨.K, q + 2, str⟩) := by
  rw [gLoad, emit_spec (Or.inr (Or.inr rfl)) h]; rfl

/-! ## Lists -/

/-- Run a gadget per element. -/
def mapTB {α : Type} (f : α → TB Src) : List α → TB (List Src)
  | [] => pure []
  | a :: as => f a >>= fun x => mapTB f as >>= fun xs => pure (x :: xs)

theorem mapTB_length {α : Type} (f : α → TB Src) : ∀ (as : List α) (n : Nat), (mapTB f as n).1.length = as.length
  | [], _ => rfl
  | a :: as, n => by
    simp only [mapTB, tb_bind, tb_pure, List.length_cons]
    rw [mapTB_length f as]

/-- **Per-element specs** of `mapTB`. -/
theorem mapTB_spec {α : Type} {xv : Src → FE} {V : Nat → FE} {f : α → TB Src} {P : α → FE → Prop}
    (hf : ∀ a n, THold xv V n (f a n).2 → P a ((f a n).1.valF xv V)) :
    ∀ (as : List α) (n : Nat), THold xv V n (mapTB f as n).2 →
      List.Forall₂ (fun a s => P a (s.valF xv V)) as (mapTB f as n).1
  | [], _, _ => List.Forall₂.nil
  | a :: as, n, h => by
    simp only [mapTB, tb_bind, tb_pure, List.append_nil] at h ⊢
    rw [thold_append] at h
    exact List.Forall₂.cons (hf a n h.1) (mapTB_spec hf as _ h.2)

theorem forall₂_map_eq {α : Type} {g : α → FE} {h : Src → FE} :
    ∀ {as : List α} {bs : List Src}, List.Forall₂ (fun a s => h s = g a) as bs → bs.map h = as.map g
  | [], [], _ => rfl
  | _ :: _, _ :: _, List.Forall₂.cons h1 h2 => by simp [h1, forall₂_map_eq h2]

/-! ## Sums, dot products, Horner, `eq` tables -/

/-- `s + c₀ + c₁ + …`. -/
def gSum : Src → List Src → TB Src
  | s, [] => pure s
  | s, c :: cs => gAdd s c >>= fun s' => gSum s' cs

theorem gSum_spec {xv : Src → FE} {V : Nat → FE} : ∀ (s : Src) (cs : List Src) (n : Nat),
    THold xv V n (gSum s cs n).2 → (gSum s cs n).1.valF xv V = s.valF xv V + (cs.map (Src.valF xv V)).sum
  | s, [], n, _ => by simp [gSum, tb_pure]
  | s, c :: cs, n, h => by
    simp only [gSum] at h ⊢
    rw [thold_bind] at h
    rw [tb_bind, gSum_spec _ cs _ h.2, gAdd_spec h.1]
    simp [add_assoc]

/-- `acc + Σ cᵢ·dᵢ`. -/
def gDot : Src → List (Src × Src) → TB Src
  | acc, [] => pure acc
  | acc, cd :: rest => gMul cd.1 cd.2 acc >>= fun a => gDot a rest

theorem gDot_spec {xv : Src → FE} {V : Nat → FE} : ∀ (acc : Src) (cds : List (Src × Src)) (n : Nat),
    THold xv V n (gDot acc cds n).2 →
      (gDot acc cds n).1.valF xv V = acc.valF xv V + (cds.map fun cd => cd.1.valF xv V * cd.2.valF xv V).sum
  | acc, [], n, _ => by simp [gDot, tb_pure]
  | acc, cd :: rest, n, h => by
    simp only [gDot] at h ⊢
    rw [thold_bind] at h
    rw [tb_bind, gDot_spec _ rest _ h.2, gMul_spec h.1]
    simp only [List.map_cons, List.sum_cons]
    ring

/-- Horner from the top coefficient `h`, then `cs` downwards. -/
def gHorner (x : Src) : Src → List Src → TB Src
  | h, [] => pure h
  | h, c :: cs => gMul h x c >>= fun h' => gHorner x h' cs

theorem gHorner_spec {xv : Src → FE} {V : Nat → FE} (x : Src) : ∀ (h : Src) (cs : List Src) (n : Nat),
    THold xv V n (gHorner x h cs n).2 →
      (gHorner x h cs n).1.valF xv V = hornerVal (x.valF xv V) (h.valF xv V) (cs.map (Src.valF xv V))
  | h, [], n, _ => by simp [gHorner, tb_pure, hornerVal]
  | h, c :: cs, n, hh => by
    simp only [gHorner] at hh ⊢
    rw [thold_bind] at hh
    rw [tb_bind, gHorner_spec x _ cs _ hh.2, gMul_spec hh.1]
    rfl

/-- One level of an `eq` table (`eqKernel`'s step): `e·(1 + r)` for every `e`, then `e·r`. -/
def gEqStep (z : Src) (tab : List Src) (r : Src) : TB (List Src) :=
  gOne r >>= fun r1 => mapTB (fun e => gMul e r1 z) tab >>= fun lo =>
    mapTB (fun e => gMul e r z) tab >>= fun hi => pure (lo ++ hi)

/-- The `eq` table of a point from `tab` (`z` a zero cell). -/
def gEqTab (z : Src) : List Src → List Src → TB (List Src)
  | tab, [] => pure tab
  | tab, r :: rs => gEqStep z tab r >>= fun t => gEqTab z t rs

theorem gOne_fst (r : Src) (n : Nat) : (gOne r n).1 = .loc n := rfl

theorem gEqStep_spec {xv : Src → FE} {V : Nat → FE} {z : Src} (hz : z.valF xv V = 0) (tab : List Src) (r : Src)
    (n : Nat) (h : THold xv V n (gEqStep z tab r n).2) :
    (gEqStep z tab r n).1.map (Src.valF xv V) =
      (tab.map (Src.valF xv V)).map (· * (1 + r.valF xv V)) ++ (tab.map (Src.valF xv V)).map (· * r.valF xv V) := by
  obtain ⟨h1, h'⟩ := (thold_bind _ _).mp h
  obtain ⟨h2, h''⟩ := (thold_bind _ _).mp h'
  obtain ⟨h3, -⟩ := (thold_bind _ _).mp h''
  have e1 : V n = 1 + r.valF xv V := gOne_spec h1
  rw [gOne_fst] at h2 h3
  have k2 := mapTB_spec (P := fun e v => v = e.valF xv V * (1 + r.valF xv V))
    (fun a m hm => by rw [gMul_spec hm, show (Src.loc n).valF xv V = V n from rfl, e1, hz, add_zero]) tab _ h2
  have k3 := mapTB_spec (P := fun e v => v = e.valF xv V * r.valF xv V)
    (fun a m hm => by rw [gMul_spec hm, hz, add_zero]) tab _ h3
  simp only [gEqStep, tb_bind, tb_pure, gOne_fst] at k2 k3 ⊢
  rw [List.map_append, forall₂_map_eq k2, forall₂_map_eq k3, List.map_map, List.map_map]
  rfl

theorem gEqTab_spec {xv : Src → FE} {V : Nat → FE} {z : Src} (hz : z.valF xv V = 0) :
    ∀ (pt tab : List Src) (n : Nat), THold xv V n (gEqTab z tab pt n).2 →
      (gEqTab z tab pt n).1.map (Src.valF xv V) =
        (pt.map (Src.valF xv V)).foldl (fun out r => out.map (· * (1 + r)) ++ out.map (· * r)) (tab.map (Src.valF xv V))
  | [], tab, n, _ => by simp [gEqTab, tb_pure]
  | r :: rs, tab, n, h => by
    simp only [gEqTab] at h ⊢
    rw [thold_bind] at h
    rw [tb_bind, gEqTab_spec hz rs _ _ h.2, gEqStep_spec hz tab r n h.1]
    rfl

/-! ## Assertions -/

/-- The assertions of `δ` placed at `n` hold: `gate · a = 0`. -/
def TAssert (xv : Src → FE) (V : Nat → FE) (δ : List Ins) : Prop :=
  ∀ k < δ.length, (δ.getD k default).op = .assert0 →
    ((δ.getD k default).args.getD 1 default).valF xv V * ((δ.getD k default).args.getD 0 default).valF xv V = 0

theorem tassert_append {xv : Src → FE} {V : Nat → FE} {δ₁ δ₂ : List Ins} :
    TAssert xv V (δ₁ ++ δ₂) ↔ TAssert xv V δ₁ ∧ TAssert xv V δ₂ := by
  constructor
  · intro h
    refine ⟨fun k hk ha => ?_, fun k hk ha => ?_⟩
    · have e : (δ₁ ++ δ₂).getD k default = δ₁.getD k default := by
        exact List.getD_append _ _ _ _ hk
      rw [← e] at ha ⊢; exact h k (by simp; (clear * - hk; omega)) ha
    · have e : (δ₁ ++ δ₂).getD (δ₁.length + k) default = δ₂.getD k default := by
        rw [List.getD_append_right _ _ _ _ (Nat.le_add_right _ _), Nat.add_sub_cancel_left]
      rw [← e] at ha ⊢; exact h _ (by simp; omega) ha
  · rintro ⟨h₁, h₂⟩ k hk ha
    by_cases hk1 : k < δ₁.length
    · have e : (δ₁ ++ δ₂).getD k default = δ₁.getD k default := by
        exact List.getD_append _ _ _ _ hk1
      rw [e] at ha ⊢; exact h₁ k hk1 ha
    · obtain ⟨k', rfl⟩ : ∃ k', k = δ₁.length + k' := ⟨k - δ₁.length, by (clear * - hk1; omega)⟩
      have e : (δ₁ ++ δ₂).getD (δ₁.length + k') default = δ₂.getD k' default := by
        rw [List.getD_append_right _ _ _ _ (Nat.le_add_right _ _), Nat.add_sub_cancel_left]
      rw [e] at ha ⊢; exact h₂ k' (by simp at hk; omega) ha

theorem tassert_bind {α β : Type} {xv : Src → FE} {V : Nat → FE} {n : Nat} (m : TB α) (f : α → TB β) :
    TAssert xv V ((m >>= f) n).2 ↔
      TAssert xv V (m n).2 ∧ TAssert xv V (f (m n).1 (n + (m n).2.length)).2 := by
  rw [tb_bind]; exact tassert_append

theorem tassert_of_loop {M : Mem} {dims : List Nat} {ins : List Ins} {p : Ptr}
    (h : SegsAssert M p (loop dims (tplOf ins) p).2) {jf : Nat} (hjf : jf < 2 ^ dims.sum) :
    TAssert (iterXv M (loop dims (tplOf ins) p).1 jf) (iterF M (loop dims (tplOf ins) p).1 jf) ins := by
  intro t ht ha
  have hA := loop_assert h hjf (t := t) (by simpa [tplOf] using ht)
  unfold LAssert at hA
  have hop : ((loop dims (tplOf ins) p).1.tpl.getD t default).op = .assert0 := by
    show ((tplOf ins).getD t default).op = _
    rw [tplOf_getD ins ht]; exact ha
  rw [hop] at hA
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
  simp only [harg] at hA
  exact hA

/-- A gated assertion `gate · a = 0`. -/
def gAssert (a gate : Src) : TB Unit := emitA ⟨.assert0, .K, [a, gate]⟩

theorem gAssert_spec {xv : Src → FE} {V : Nat → FE} {n : Nat} {a gate : Src}
    (h : TAssert xv V (gAssert a gate n).2) : gate.valF xv V * a.valF xv V = 0 :=
  h 0 (by simp [gAssert, emitA]) rfl

end Lvm.Q1
end
-- ===== end of `LvmQKeccakTB` =====

-- ===== merged from `LvmQKeccakRounds` (GOLF module merge: `LvmQKeccakRounds.lean` is now a stub importing `LvmQKeccakLayer`) =====
section

/-!
# QA1: the Keccak layer's rounds as template gadgets (pack rounds, position rounds)

Unrolled inside the layer template (the layer is the loop). Stream scalars are loads of lanes;
`lv xv str q` is the value of the load at lane `q` (`gLoad_spec`), and a view `v` of `F`'s scalars
matches it at an offset: `lv q = v (8q + off)`. With that, **`gPackRounds_spec`** is `F`'s
`packSpec` (equality-mode rounds with the scale, `keccakPackRounds`) and **`gLocalRounds_spec`** is
`F`'s `scSpec` with four coefficients (the eleven position rounds).

Rows: a pack round 3 loads + 7 rows (`c₀ = r(c₁+c₂) + v`, Horner 2, `1 + r + ρ`, two products);
a position round 4 loads + 5 rows (`c₁ = v + c₂ + c₃`, Horner 3).
-/

set_option autoImplicit false

namespace Lvm.Q1

open Lvm Lvm.Loop

/-- The load at lane `q` (a loop's iteration fixed by `xv`). -/
def lv (xv : Src → FE) (str : List Nat) (q : Nat) : FE :=
  xv (.ext ⟨.K, q, str⟩) + FE.y * xv (.ext ⟨.K, q + 1, str⟩) + FE.y * FE.y * xv (.ext ⟨.K, q + 2, str⟩)

theorem gLoad_lv {xv : Src → FE} {V : Nat → FE} {n q : Nat} {str : List Nat} (h : THold xv V n (gLoad q str n).2) :
    (gLoad q str n).1.valF xv V = lv xv str q := gLoad_spec h

/-! ## Pack rounds -/

/-- One pack round: message `c₁, c₂` at lanes `q, q+3`, challenge at `q+6`. Returns the new value,
the new scale and the challenge. -/
def gPackRound (z : Src) (q : Nat) (str : List Nat) (r value scale : Src) : TB (Src × Src × Src) :=
  gLoad q str >>= fun c1 => gLoad (q + 3) str >>= fun c2 => gLoad (q + 6) str >>= fun ch =>
  gAdd c1 c2 >>= fun s => gMul r s value >>= fun c0 => gMul c2 ch c1 >>= fun h =>
  gMul h ch c0 >>= fun pe => gLin 1 1 r ch >>= fun g => gMul g pe z >>= fun v' =>
  gMul scale g z >>= fun s' => pure (v', s', ch)

/-- The pack rounds from lane `q` (15 lanes a round). -/
def gPackRounds (z : Src) (str : List Nat) : Nat → List Src → Src → Src → TB (Src × Src × List Src)
  | _, [], value, scale => pure (value, scale, [])
  | q, r :: rs, value, scale =>
    gPackRound z q str r value scale >>= fun a =>
      gPackRounds z str (q + 15) rs a.1 a.2.1 >>= fun b => pure (b.1, b.2.1, a.2.2 :: b.2.2)

theorem one_add_one_mul (x : FE) : FE.ofK 1 * x = x := by rw [show FE.ofK 1 = 1 from rfl, one_mul]

theorem gPackRound_spec {xv : Src → FE} {V : Nat → FE} {z : Src} (hz : z.valF xv V = 0) {v : Nat → FE}
    {off q N : Nat} {str : List Nat} (hv : ∀ m < N, lv xv str m = v (8 * m + off)) (hN : q + 6 < N) {p : Nat}
    (hp : p + 40 = 8 * q + off)
    (r value scale : Src) (n : Nat) (h : THold xv V n (gPackRound z q str r value scale n).2) :
    (gPackRound z q str r value scale n).1.1.valF xv V =
        (1 + r.valF xv V + v (p + 88)) *
          polyEval (roundPoly v p 3 (value.valF xv V) (some (r.valF xv V))) (v (p + 88)) ∧
    (gPackRound z q str r value scale n).1.2.1.valF xv V = scale.valF xv V * (1 + r.valF xv V + v (p + 88)) ∧
    (gPackRound z q str r value scale n).1.2.2.valF xv V = v (p + 88) := by
  unfold gPackRound at h ⊢
  obtain ⟨h1, h⟩ := (thold_bind _ _).mp h
  obtain ⟨h2, h⟩ := (thold_bind _ _).mp h
  obtain ⟨h3, h⟩ := (thold_bind _ _).mp h
  obtain ⟨h4, h⟩ := (thold_bind _ _).mp h
  obtain ⟨h5, h⟩ := (thold_bind _ _).mp h
  obtain ⟨h6, h⟩ := (thold_bind _ _).mp h
  obtain ⟨h7, h⟩ := (thold_bind _ _).mp h
  obtain ⟨h8, h⟩ := (thold_bind _ _).mp h
  obtain ⟨h9, h⟩ := (thold_bind _ _).mp h
  obtain ⟨h10, -⟩ := (thold_bind _ _).mp h
  have e1 := gLoad_lv h1
  have e2 := gLoad_lv h2
  have e3 := gLoad_lv h3
  have e4 := gAdd_spec h4
  have e5 := gMul_spec h5
  have e6 := gMul_spec h6
  have e7 := gMul_spec h7
  have e8 := gLin_spec h8
  have e9 := gMul_spec h9
  have e10 := gMul_spec h10
  simp only [tb_bind, tb_pure]
  rw [hv _ (by (clear * - hN; omega))] at e1; rw [hv _ (by (clear * - hN; omega))] at e2; rw [hv _ (by omega)] at e3
  have q1 : 8 * q + off = p + 40 := by (clear * - hp; omega)
  have q2 : 8 * (q + 3) + off = p + 64 := by (clear * - hp; omega)
  have q3 : 8 * (q + 6) + off = p + 88 := by (clear * - hp; omega)
  rw [q1] at e1; rw [q2] at e2; rw [q3] at e3
  simp only [roundPoly, scalarsAt, show (3 - 1 : Nat) = 2 from rfl, List.range_succ, List.range_zero,
    List.map_append, List.map_nil, List.nil_append, List.map_cons, sumE, polyEval, List.cons_append,
    List.singleton_append, List.foldl_cons, List.foldl_nil, List.foldr_cons, List.foldr_nil]
  refine ⟨?_, ?_, ?_⟩
  · rw [e9, e8, e7, e6, e5, e4, e1, e2, e3, hz, one_add_one_mul]
    simp only [show (FE.ofK 1) = 1 from rfl, Nat.mul_zero, Nat.add_zero, Nat.mul_one]
    ring
  · rw [e10, e8, e3, hz, one_add_one_mul]
    simp only [show (FE.ofK 1) = 1 from rfl]
    ring
  · exact e3

/-- **The pack rounds are `F`'s `packSpec`.** -/
theorem gPackRounds_spec {xv : Src → FE} {V : Nat → FE} {z : Src} (hz : z.valF xv V = 0) {v : Nat → FE}
    {off N : Nat} {str : List Nat} (hv : ∀ m < N, lv xv str m = v (8 * m + off)) :
    ∀ (rs : List Src) (q p : Nat), q + 15 * rs.length ≤ N → p + 40 = 8 * q + off → ∀ (value scale : Src) (n : Nat),
      THold xv V n (gPackRounds z str q rs value scale n).2 →
      (gPackRounds z str q rs value scale n).1.1.valF xv V =
          (packSpec v (rs.map (Src.valF xv V)) (value.valF xv V) (scale.valF xv V) p).1 ∧
      (gPackRounds z str q rs value scale n).1.2.1.valF xv V =
          (packSpec v (rs.map (Src.valF xv V)) (value.valF xv V) (scale.valF xv V) p).2.1 ∧
      (gPackRounds z str q rs value scale n).1.2.2.map (Src.valF xv V) =
          (packSpec v (rs.map (Src.valF xv V)) (value.valF xv V) (scale.valF xv V) p).2.2.1
  | [], q, p, _, _, value, scale, n, _ => by simp [gPackRounds, tb_pure, packSpec]
  | r :: rs, q, p, hN, hp, value, scale, n, h => by
    simp only [gPackRounds] at h ⊢
    obtain ⟨h1, h⟩ := (thold_bind _ _).mp h
    obtain ⟨h2, -⟩ := (thold_bind _ _).mp h
    obtain ⟨e1, e2, e3⟩ := gPackRound_spec hz hv (by simp at hN; (clear * - hN; omega)) hp r value scale n h1
    have ih := gPackRounds_spec hz hv rs (q + 15) (p + 120) (by simp at hN; (clear * - hN; omega)) (by (clear * - hp; omega)) _ _ _ h2
    simp only [tb_bind, tb_pure, List.map_cons, packSpec]
    rw [e1, e2] at ih
    exact ⟨ih.1, ih.2.1, congrArg₂ List.cons e3 ih.2.2⟩

/-! ## Position rounds (plain, four coefficients) -/

/-- One position round: `c₀, c₂, c₃` at lanes `q, q+3, q+6`, challenge at `q+9`. Returns the new
claim and the challenge. -/
def gLocalRound (q : Nat) (str : List Nat) (value : Src) : TB (Src × Src) :=
  gLoad q str >>= fun c0 => gLoad (q + 3) str >>= fun c2 => gLoad (q + 6) str >>= fun c3 =>
  gLoad (q + 9) str >>= fun ch => gAdd value c2 >>= fun s => gAdd s c3 >>= fun c1 =>
  gMul c3 ch c2 >>= fun h1 => gMul h1 ch c1 >>= fun h2 => gMul h2 ch c0 >>= fun h3 => pure (h3, ch)

/-- The position rounds from lane `q` (18 lanes a round). -/
def gLocalRounds (str : List Nat) : Nat → Nat → Src → TB (Src × List Src)
  | 0, _, value => pure (value, [])
  | k + 1, q, value =>
    gLocalRound q str value >>= fun a => gLocalRounds str k (q + 18) a.1 >>= fun b => pure (b.1, a.2 :: b.2)

theorem gLocalRound_spec {xv : Src → FE} {V : Nat → FE} {v : Nat → FE}
    {off q N : Nat} {str : List Nat} (hv : ∀ m < N, lv xv str m = v (8 * m + off)) (hN : q + 9 < N) {p : Nat}
    (hp : p + 40 = 8 * q + off)
    (value : Src) (n : Nat) (h : THold xv V n (gLocalRound q str value n).2) :
    (gLocalRound q str value n).1.1.valF xv V =
        polyEval (roundPoly v p 4 (value.valF xv V) none) (v (p + 40 + 24 * (4 - 1))) ∧
    (gLocalRound q str value n).1.2.valF xv V = v (p + 40 + 24 * (4 - 1)) := by
  unfold gLocalRound at h ⊢
  obtain ⟨h1, h⟩ := (thold_bind _ _).mp h
  obtain ⟨h2, h⟩ := (thold_bind _ _).mp h
  obtain ⟨h3, h⟩ := (thold_bind _ _).mp h
  obtain ⟨h4, h⟩ := (thold_bind _ _).mp h
  obtain ⟨h5, h⟩ := (thold_bind _ _).mp h
  obtain ⟨h6, h⟩ := (thold_bind _ _).mp h
  obtain ⟨h7, h⟩ := (thold_bind _ _).mp h
  obtain ⟨h8, h⟩ := (thold_bind _ _).mp h
  obtain ⟨h9, -⟩ := (thold_bind _ _).mp h
  have e1 := gLoad_lv h1
  have e2 := gLoad_lv h2
  have e3 := gLoad_lv h3
  have e4 := gLoad_lv h4
  have e5 := gAdd_spec h5
  have e6 := gAdd_spec h6
  have e7 := gMul_spec h7
  have e8 := gMul_spec h8
  have e9 := gMul_spec h9
  simp only [tb_bind, tb_pure]
  rw [hv _ (by (clear * - hN; omega))] at e1; rw [hv _ (by (clear * - hN; omega))] at e2; rw [hv _ (by (clear * - hN; omega))] at e3
  rw [hv _ (by omega)] at e4
  rw [show 8 * q + off = p + 40 by (clear * - hp; omega)] at e1
  rw [show 8 * (q + 3) + off = p + 64 by (clear * - hp; omega)] at e2
  rw [show 8 * (q + 6) + off = p + 88 by (clear * - hp; omega)] at e3
  rw [show 8 * (q + 9) + off = p + 40 + 24 * (4 - 1) by (clear * - hp; omega)] at e4
  refine ⟨?_, e4⟩
  simp only [roundPoly, scalarsAt, show (4 - 2 : Nat) = 2 from rfl, List.range_succ, List.range_zero,
    List.map_append, List.map_nil, List.nil_append, List.map_cons, sumE, polyEval, List.cons_append,
    List.singleton_append, List.foldl_cons, List.foldl_nil, List.foldr_cons, List.foldr_nil]
  rw [e9, e8, e7, e6, e5, e1, e2, e3, e4]
  simp only [Nat.mul_zero, Nat.add_zero, Nat.mul_one, show p + 64 + 24 = p + 88 by (clear * -; first | decide | (simp only [Nat.add_comm, Nat.add_left_comm, Nat.add_assoc]; done) | ring1 | omega)]
  ring

/-- **The position rounds are `F`'s `scSpec` with four coefficients.** -/
theorem gLocalRounds_spec {xv : Src → FE} {V : Nat → FE} {v : Nat → FE}
    {off N : Nat} {str : List Nat} (hv : ∀ m < N, lv xv str m = v (8 * m + off)) :
    ∀ (k q p : Nat), q + 18 * k ≤ N → p + 40 = 8 * q + off → ∀ (value : Src) (n : Nat),
      THold xv V n (gLocalRounds str k q value n).2 →
      (gLocalRounds str k q value n).1.1.valF xv V = (scSpec v 4 p (value.valF xv V) (List.replicate k none)).2 ∧
      (gLocalRounds str k q value n).1.2.map (Src.valF xv V) = (scSpec v 4 p (value.valF xv V) (List.replicate k none)).1
  | 0, q, p, _, _, value, n, _ => by simp [gLocalRounds, tb_pure, scSpec]
  | k + 1, q, p, hN, hp, value, n, h => by
    simp only [gLocalRounds] at h ⊢
    obtain ⟨h1, h⟩ := (thold_bind _ _).mp h
    obtain ⟨h2, -⟩ := (thold_bind _ _).mp h
    obtain ⟨e1, e2⟩ := gLocalRound_spec hv (by (clear * - hN; omega)) hp value n h1
    have ih := gLocalRounds_spec hv k (q + 18) (p + roundLen 4) (by (clear * - hN; omega)) (by simp [roundLen]; (clear * - hp; omega)) _ _ h2
    simp only [tb_bind, tb_pure, List.map_cons, List.replicate_succ, scSpec]
    rw [e1] at ih
    exact ⟨ih.1, congrArg₂ List.cons e2 ih.2⟩

end Lvm.Q1
end
-- ===== end of `LvmQKeccakRounds` =====

-- ===== merged from `LvmQKeccakParts` (GOLF module merge: `LvmQKeccakParts.lean` is now a stub importing `LvmQKeccakLayer`) =====
section

/-!
# QA1: the Keccak layer's arithmetic as template gadgets

Each gadget computes one piece of `F`'s `verifyKeccakLayer` (or of the structured forms of
`LvmQKeccakSpec`), and its spec states the value in `F`'s own form:

* `gProj`: the RMFE projection `Σ_c (Σ_{i: mask_i ∋ c} μ_i)·product_c` (masks a parameter; `F` uses
  `rmfeProject`);
* `gPowers`, `gInst`: `powers s 24` and the instance weights `Σ_{b ∈ e} s^b` per embedding `e`
  (`keccakInstanceWeights` with `rmfeEmbed`);
* `gSumMap`: `Σ_{c<k} f(c)` for per-index gadgets (the pattern of every sum below).
-/

set_option autoImplicit false

namespace Lvm.Q1

open Lvm Lvm.Loop

/-- `Σ_{c<k}` of per-index gadgets. -/
def gSumMap (z : Src) (k : Nat) (f : Nat → TB Src) : TB Src :=
  mapTB f (List.range k) >>= fun ts => gSum z ts

theorem gSumMap_spec {xv : Src → FE} {V : Nat → FE} {z : Src} (hz : z.valF xv V = 0) {k : Nat}
    {f : Nat → TB Src} {F : Nat → FE} (hf : ∀ c n, THold xv V n (f c n).2 → (f c n).1.valF xv V = F c)
    (n : Nat) (h : THold xv V n (gSumMap z k f n).2) :
    (gSumMap z k f n).1.valF xv V = ((List.range k).map F).sum := by
  obtain ⟨h1, h2⟩ := (thold_bind _ _).mp h
  have k1 := mapTB_spec (P := fun c v => v = F c) (fun c m hm => hf c m hm) _ _ h1
  rw [gSumMap, tb_bind, gSum_spec _ _ _ h2, hz, zero_add, forall₂_map_eq k1]

/-- `mapTB_spec` with the elements' membership. -/
theorem mapTB_spec_mem {α : Type} {xv : Src → FE} {V : Nat → FE} {f : α → TB Src} {P : α → FE → Prop} :
    ∀ (as : List α), (∀ a ∈ as, ∀ n, THold xv V n (f a n).2 → P a ((f a n).1.valF xv V)) →
      ∀ (n : Nat), THold xv V n (mapTB f as n).2 → List.Forall₂ (fun a s => P a (s.valF xv V)) as (mapTB f as n).1
  | [], _, _, _ => List.Forall₂.nil
  | a :: as, hf, n, h => by
    simp only [mapTB, tb_bind, tb_pure, List.append_nil] at h ⊢
    rw [thold_append] at h
    exact List.Forall₂.cons (hf a (by simp) n h.1)
      (mapTB_spec_mem as (fun b hb => hf b (by simp [hb])) _ h.2)

theorem gSumMap_spec' {xv : Src → FE} {V : Nat → FE} {z : Src} (hz : z.valF xv V = 0) {k : Nat}
    {f : Nat → TB Src} {F : Nat → FE} (hf : ∀ c < k, ∀ n, THold xv V n (f c n).2 → (f c n).1.valF xv V = F c)
    (n : Nat) (h : THold xv V n (gSumMap z k f n).2) :
    (gSumMap z k f n).1.valF xv V = ((List.range k).map F).sum := by
  obtain ⟨h1, h2⟩ := (thold_bind _ _).mp h
  have k1 := mapTB_spec_mem (P := fun c v => v = F c) _ (fun c hc m hm => hf c (List.mem_range.mp hc) m hm) _ h1
  rw [gSumMap, tb_bind, gSum_spec _ _ _ h2, hz, zero_add, forall₂_map_eq k1]

theorem getD_valF {xv : Src → FE} {V : Nat → FE} (l : List Src) {i : Nat} (hi : i < l.length) :
    (l.getD i default).valF xv V = (l.map (Src.valF xv V)).getD i 0 := by
  simp [List.getD_eq_getElem _ _ hi, hi]

/-! ## The RMFE projection -/

/-- The weights summed for product coefficient `c`: `μ_i` with bit `c` of mask `i`. -/
def projSrcs (masks : List Nat) (mu : List Src) (c : Nat) : List Src :=
  (mu.zip masks).filterMap fun p => if p.2.testBit c then some p.1 else none

theorem projSrcs_map {xv : Src → FE} {V : Nat → FE} (masks : List Nat) (c : Nat) (mu : List Src) :
    (projSrcs masks mu c).map (Src.valF xv V) =
      ((mu.map (Src.valF xv V)).zip masks).filterMap fun p => if p.2.testBit c then some p.1 else none := by
  rw [projSrcs, List.map_filterMap, List.zip_map_left, List.filterMap_map]
  apply List.filterMap_congr
  intro p _
  simp only [Function.comp_def, Prod.map_fst, Prod.map_snd, id_eq]
  split <;> rfl

/-- **The projection**: `Σ_{c<k} (Σ projSrcs c)·product_c`. -/
def gProj (z : Src) (masks : List Nat) (mu prod : List Src) : TB Src :=
  gSumMap z prod.length fun c => gSum z (projSrcs masks mu c) >>= fun P => gMul P (prod.getD c default) z

theorem gProj_spec {xv : Src → FE} {V : Nat → FE} {z : Src} (hz : z.valF xv V = 0) (masks : List Nat)
    (mu prod : List Src) (n : Nat) (h : THold xv V n (gProj z masks mu prod n).2) :
    (gProj z masks mu prod n).1.valF xv V = sumE ((List.range prod.length).map fun c =>
      sumE (((mu.map (Src.valF xv V)).zip masks).filterMap fun p => if p.2.testBit c then some p.1 else none) *
        (prod.getD c default).valF xv V) := by
  rw [sumE_eq_sum]
  refine gSumMap_spec hz (fun c m hm => ?_) n h
  obtain ⟨h1, h2⟩ := (thold_bind _ _).mp hm
  rw [tb_bind, gMul_spec h2, gSum_spec _ _ _ h1, hz, zero_add, add_zero, projSrcs_map, sumE_eq_sum]

/-! ## Instance weights -/

/-- `acc, acc·s, acc·s², …` (`k` terms; `powersFrom`). -/
def gPowers (z s : Src) : Src → Nat → TB (List Src)
  | _, 0 => pure []
  | acc, k + 1 => gMul acc s z >>= fun nx => gPowers z s nx k >>= fun rest => pure (acc :: rest)

theorem gPowers_spec {xv : Src → FE} {V : Nat → FE} {z s : Src} (hz : z.valF xv V = 0) :
    ∀ (k : Nat) (acc : Src) (n : Nat), THold xv V n (gPowers z s acc k n).2 →
      (gPowers z s acc k n).1.map (Src.valF xv V) = powersFrom (acc.valF xv V) (s.valF xv V) k
  | 0, _, _, _ => rfl
  | k + 1, acc, n, h => by
    simp only [gPowers] at h ⊢
    obtain ⟨h1, h⟩ := (thold_bind _ _).mp h
    obtain ⟨h2, -⟩ := (thold_bind _ _).mp h
    simp only [tb_bind, tb_pure, List.map_cons, powersFrom]
    rw [gPowers_spec hz k _ _ h2, gMul_spec h1, hz, add_zero]

theorem powersFrom_length (acc base : FE) : ∀ k : Nat, (powersFrom acc base k).length = k
  | 0 => rfl
  | k + 1 => by simp [powersFrom, powersFrom_length _ _ k]

theorem gPowers_length (z s : Src) : ∀ (k : Nat) (acc : Src) (n : Nat), (gPowers z s acc k n).1.length = k
  | 0, _, _ => rfl
  | k + 1, acc, n => by simp [gPowers, tb_bind, tb_pure, gPowers_length z s k]

/-- The powers an embedding `e` sums. -/
def embSrcs (pw : List Src) (e : Nat) : List Src :=
  (List.range embedBits).filterMap fun b => if e.testBit b then some (pw.getD b default) else none

/-- **The instance weights** `μ_e = Σ_{b ∈ e} s^b` and their sum `κ` (`one` a cell holding `1`). -/
def gInst (z one s : Src) (embs : List Nat) : TB (List Src × Src) :=
  gPowers z s one embedBits >>= fun pw => mapTB (fun e => gSum z (embSrcs pw e)) embs >>= fun mu =>
    gSum z mu >>= fun kappa => pure (mu, kappa)

theorem gInst_spec {xv : Src → FE} {V : Nat → FE} {z one s : Src} (hz : z.valF xv V = 0)
    (hone : one.valF xv V = 1) (embs : List Nat) (n : Nat) (h : THold xv V n (gInst z one s embs n).2) :
    (gInst z one s embs n).1.1.map (Src.valF xv V) =
        embs.map (fun e => sumE ((List.range embedBits).filterMap fun b =>
          if e.testBit b then some ((powers (s.valF xv V) embedBits).getD b 0) else none)) ∧
    (gInst z one s embs n).1.2.valF xv V = ((gInst z one s embs n).1.1.map (Src.valF xv V)).sum := by
  obtain ⟨h1, h⟩ := (thold_bind _ _).mp h
  obtain ⟨h2, h⟩ := (thold_bind _ _).mp h
  obtain ⟨h3, -⟩ := (thold_bind _ _).mp h
  have epw := gPowers_spec hz embedBits one n h1
  rw [hone] at epw
  have hlen := gPowers_length z s embedBits one n
  have k2 := mapTB_spec (P := fun e v => v = sumE ((List.range embedBits).filterMap fun b =>
      if e.testBit b then some ((powers (s.valF xv V) embedBits).getD b 0) else none))
    (fun e m hm => by
      rw [gSum_spec _ _ _ hm, hz, zero_add, sumE_eq_sum]
      congr 1
      simp only [embSrcs, List.map_filterMap]
      apply List.filterMap_congr
      intro b hb
      split
      · simp only [Option.map_some, Option.some.injEq]
        rw [getD_valF _ (by rw [hlen]; simpa using hb), epw]; rfl
      · rfl) embs _ h2
  refine ⟨?_, ?_⟩
  · simp only [gInst, tb_bind, tb_pure]
    exact forall₂_map_eq k2
  · simp only [gInst, tb_bind, tb_pure]
    rw [gSum_spec _ _ _ h3, hz, zero_add]

end Lvm.Q1
end
-- ===== end of `LvmQKeccakParts` =====

-- ===== merged from `LvmQKeccakParts2` (GOLF module merge: `LvmQKeccakParts2.lean` is now a stub importing `LvmQKeccakLayer`) =====
section

/-!
# QA1: the Keccak layer's weight gadgets (structured forms of `LvmQKeccakSpec`)

* `gLowTab`, `gHighTab`, `gShift`: `lowTab`, `highTab`, `shiftLH` from `eq` tables of the two
  six-coordinate points (split three and three);
* `gLaneForm`, `gFlip`: `laneForm` and `flipForm`;
* `gKForm`: `kForm` (the final check's weight, the guest's `keccak_form`);
* `gLaneW`: `F`'s next lane weights `eq_L(ℓ) + β(eq_L(x+4) + β eq_L(x+3))` (`laneWF`);
* `gIndex`: `indexMle` (`Π (1 + r_t (1 + g^{2^t}))`, constants in `K`).
-/

set_option autoImplicit false

namespace Lvm.Q1

open Lvm Lvm.Loop

/-- A list of sources as values. -/
abbrev vals (xv : Src → FE) (V : Nat → FE) (l : List Src) : List FE := l.map (Src.valF xv V)

theorem getD_vals {xv : Src → FE} {V : Nat → FE} (l : List Src) {i : Nat} (hi : i < l.length) :
    (l.getD i default).valF xv V = (vals xv V l).getD i 0 := getD_valF l hi

/-! ## The shift tables -/

/-- `L_c(r_l)` from the `eq` tables `ta` (of `a_lo`) and `tb` (of `b_lo`). -/
def gLowTab (z : Src) (ta tb : List Src) (c rl : Nat) : TB Src :=
  gSumMap z 8 fun zz => if (zz + rl) / 8 = c then gMul (tb.getD zz default) (ta.getD ((zz + rl) % 8) default) z
    else pure z

/-- `H(k)` from the `eq` tables of `a_hi`, `b_hi`. -/
def gHighTab (z : Src) (ta tb : List Src) (k : Nat) : TB Src :=
  gSumMap z 8 fun zz => gMul (tb.getD zz default) (ta.getD ((zz + k) % 8) default) z

theorem eqKernel_len (pt : List FE) : (eqKernel pt).length = 2 ^ pt.length := by
  unfold eqKernel
  suffices h : ∀ (l : List FE) (acc : List FE), (l.foldl (fun out r => out.map (· * (1 + r)) ++ out.map (· * r)) acc).length =
      acc.length * 2 ^ l.length by simpa using h pt [1]
  intro l
  induction l with
  | nil => simp
  | cons r rs ih => intro acc; rw [List.foldl_cons, ih]; simp [pow_succ]; ring

theorem gLowTab_spec {xv : Src → FE} {V : Nat → FE} {z : Src} (hz : z.valF xv V = 0) {ta tb : List Src}
    {a b : List FE} (hta : vals xv V ta = eqKernel (a.take 3)) (htb : vals xv V tb = eqKernel (b.take 3))
    (ha : 3 ≤ a.length) (hb : 3 ≤ b.length) (c rl : Nat) (n : Nat) (h : THold xv V n (gLowTab z ta tb c rl n).2) :
    (gLowTab z ta tb c rl n).1.valF xv V = lowTab a b c rl := by
  have la : ta.length = 8 := by
    have := congrArg List.length hta; rw [List.length_map, eqKernel_len] at this; simp [this, ha]
  have lb : tb.length = 8 := by
    have := congrArg List.length htb; rw [List.length_map, eqKernel_len] at this; simp [this, hb]
  rw [lowTab, sumE_eq_sum]
  refine gSumMap_spec' hz (fun zz hzz m hm => ?_) n h
  by_cases hc : (zz + rl) / 8 = c
  · simp only [hc, if_true] at hm ⊢
    rw [gMul_spec hm, hz, add_zero, getD_vals _ (by (clear * - lb hzz; omega)), getD_vals _ (by rw [la]; exact Nat.mod_lt _ (by (clear * -; first | decide | (simp only [Nat.add_comm, Nat.add_left_comm, Nat.add_assoc]; done) | ring1 | omega))),
      hta, htb]
    rfl
  · simp only [hc, if_false] at hm ⊢
    exact hz

theorem gHighTab_spec {xv : Src → FE} {V : Nat → FE} {z : Src} (hz : z.valF xv V = 0) {ta tb : List Src}
    {a b : List FE} (hta : vals xv V ta = eqKernel (a.drop 3)) (htb : vals xv V tb = eqKernel (b.drop 3))
    (ha : a.length = 6) (hb : b.length = 6) (k : Nat) (n : Nat) (h : THold xv V n (gHighTab z ta tb k n).2) :
    (gHighTab z ta tb k n).1.valF xv V = highTab a b k := by
  have la : ta.length = 8 := by
    have := congrArg List.length hta; rw [List.length_map, eqKernel_len] at this; simp [this, ha]
  have lb : tb.length = 8 := by
    have := congrArg List.length htb; rw [List.length_map, eqKernel_len] at this; simp [this, hb]
  rw [highTab, sumE_eq_sum]
  refine gSumMap_spec' hz (fun zz hzz m hm => ?_) n h
  rw [gMul_spec hm, hz, add_zero, getD_vals _ (by (clear * - lb hzz; omega)), getD_vals _ (by rw [la]; exact Nat.mod_lt _ (by (clear * -; first | decide | (simp only [Nat.add_comm, Nat.add_left_comm, Nat.add_assoc]; done) | ring1 | omega))),
    hta, htb]
  rfl

/-- `shift(r) = L₀·H + L₁·H'` from the three tables. -/
def gShift (z : Src) (L0 L1 H : List Src) (r : Nat) : TB Src :=
  gMul (L1.getD (r % 8) default) (H.getD ((r / 8 + 1) % 8) default) z >>= fun t =>
    gMul (L0.getD (r % 8) default) (H.getD (r / 8) default) t

theorem gShift_spec {xv : Src → FE} {V : Nat → FE} {z : Src} (hz : z.valF xv V = 0) {L0 L1 H : List Src}
    {a b : List FE} (h0 : vals xv V L0 = (List.range 8).map (lowTab a b 0))
    (h1 : vals xv V L1 = (List.range 8).map (lowTab a b 1)) (hH : vals xv V H = (List.range 8).map (highTab a b))
    {r : Nat} (hr : r < 64) (n : Nat) (h : THold xv V n (gShift z L0 L1 H r n).2) :
    (gShift z L0 L1 H r n).1.valF xv V = shiftLH a b r := by
  have l0 : L0.length = 8 := by simpa using congrArg List.length h0
  have l1 : L1.length = 8 := by simpa using congrArg List.length h1
  have lH : H.length = 8 := by simpa using congrArg List.length hH
  obtain ⟨g1, g2⟩ := (thold_bind _ _).mp h
  rw [gShift, tb_bind, gMul_spec g2, gMul_spec g1, hz, add_zero,
    getD_vals _ (by rw [l0]; exact Nat.mod_lt _ (by (clear * -; first | decide | (simp only [Nat.add_comm, Nat.add_left_comm, Nat.add_assoc]; done) | ring1 | omega))), getD_vals _ (by rw [lH]; (clear * - hr; omega)),
    getD_vals _ (by rw [l1]; exact Nat.mod_lt _ (by (clear * -; first | decide | (simp only [Nat.add_comm, Nat.add_left_comm, Nat.add_assoc]; done) | ring1 | omega))), getD_vals _ (by rw [lH]; exact Nat.mod_lt _ (by (clear * -; first | decide | (simp only [Nat.add_comm, Nat.add_left_comm, Nat.add_assoc]; done) | ring1 | omega))),
    h0, h1, hH]
  simp [List.getD_eq_getElem?_getD, Nat.mod_lt _ (show 0 < 8 by (clear * -; first | decide | (simp only [Nat.add_comm, Nat.add_left_comm, Nat.add_assoc]; done) | ring1 | omega)), show r / 8 < 8 by (clear * - hr; omega),
    Nat.mod_lt _ (show 0 < 8 by (clear * -; first | decide | (simp only [Nat.add_comm, Nat.add_left_comm, Nat.add_assoc]; done) | ring1 | omega)), shiftLH]

theorem kPi_lt : ∀ l < 25, keccakPi l < 25 := by decide

/-- `laneForm B R ℓ`: the lane, then the two columns. -/
def gLaneForm (z : Src) (B : List Src) (R : Nat → Src) (l : Nat) : TB Src :=
  gMul (B.getD (keccakPi l) default) (R (rho l)) z >>= fun t1 =>
  gDot t1 ((List.range 5).map fun y =>
    (B.getD (keccakPi ((l % 5 + 1) % 5 + 5 * y)) default, R (rho ((l % 5 + 1) % 5 + 5 * y)))) >>= fun t2 =>
  gDot t2 ((List.range 5).map fun y =>
    (B.getD (keccakPi ((l % 5 + 4) % 5 + 5 * y)) default, R ((rho ((l % 5 + 4) % 5 + 5 * y) + 1) % 64)))

theorem gLaneForm_spec {xv : Src → FE} {V : Nat → FE} {z : Src} (hz : z.valF xv V = 0) {B : List Src}
    (hB : 25 ≤ B.length) (R : Nat → Src) {l : Nat} (hl : l < 25) (n : Nat)
    (h : THold xv V n (gLaneForm z B R l n).2) :
    (gLaneForm z B R l n).1.valF xv V = laneForm (vals xv V B) (fun s => (R s).valF xv V) l := by
  obtain ⟨g1, h'⟩ := (thold_bind _ _).mp h
  obtain ⟨g2, g3⟩ := (thold_bind _ _).mp h'
  have hp : ∀ x y, x < 5 → y < 5 → keccakPi (x + 5 * y) < B.length := fun x y hx hy =>
    lt_of_lt_of_le (kPi_lt _ (by (clear * - hx hy; omega))) hB
  rw [gLaneForm, tb_bind, tb_bind, gDot_spec _ _ _ g3, gDot_spec _ _ _ g2, gMul_spec g1, hz, add_zero,
    laneForm, sumE_eq_sum, sumE_eq_sum, getD_vals _ (lt_of_lt_of_le (kPi_lt _ hl) hB)]
  simp only [List.map_map, Function.comp_def]
  congr 2
  · congr 1
    apply List.map_congr_left
    intro y hy
    rw [getD_vals _ (hp _ _ (Nat.mod_lt _ (by (clear * -; first | decide | (simp only [Nat.add_comm, Nat.add_left_comm, Nat.add_assoc]; done) | ring1 | omega))) (List.mem_range.mp hy))]
  · apply List.map_congr_left
    intro y hy
    rw [getD_vals _ (hp _ _ (Nat.mod_lt _ (by (clear * -; first | decide | (simp only [Nat.add_comm, Nat.add_left_comm, Nat.add_assoc]; done) | ring1 | omega))) (List.mem_range.mp hy))]

/-- `flip_i = flipForm B A i`, `A` given as an `eq` table of 64 sources. -/
def gFlip (z : Src) (B A : List Src) (i : Nat) : TB Src :=
  gLaneForm z B (fun s => A.getD ((iotaPos i + s) % 64) default) 0

theorem gFlip_spec {xv : Src → FE} {V : Nat → FE} {z : Src} (hz : z.valF xv V = 0) {B A : List Src}
    (hB : 25 ≤ B.length) (hA : A.length = 64) (i n : Nat) (h : THold xv V n (gFlip z B A i n).2) :
    (gFlip z B A i n).1.valF xv V = flipForm (vals xv V B) (fun s => (vals xv V A).getD s 0) i := by
  rw [gFlip, gLaneForm_spec hz hB _ (by (clear * -; first | decide | (simp only [Nat.add_comm, Nat.add_left_comm, Nat.add_assoc]; done) | ring1 | omega)) n h, flipForm]
  congr 1
  funext s
  rw [getD_vals _ (by rw [hA]; exact Nat.mod_lt _ (by (clear * -; first | decide | (simp only [Nat.add_comm, Nat.add_left_comm, Nat.add_assoc]; done) | ring1 | omega)))]

/-- `F`'s next lane weights from the `eq` table `eL` of the lane challenges. -/
def gLaneW (eL : List Src) (beta : Src) : TB (List Src) :=
  mapTB (fun l => gMul beta (eL.getD (keccakAlong (64 * l) 3 / 64) default)
    (eL.getD (keccakAlong (64 * l) 4 / 64) default) >>= fun u => gMul beta u (eL.getD l default)) (List.range 25)

theorem along_lt : ∀ l < 25, keccakAlong (64 * l) 3 / 64 < 25 ∧ keccakAlong (64 * l) 4 / 64 < 25 := by decide

theorem gLaneW_spec {xv : Src → FE} {V : Nat → FE} {eL : List Src} (hL : 25 ≤ eL.length) (beta : Src) (n : Nat)
    (h : THold xv V n (gLaneW eL beta n).2) :
    vals xv V (gLaneW eL beta n).1 = (List.range 25).map fun l => (vals xv V eL).getD l 0 + beta.valF xv V *
      ((vals xv V eL).getD (keccakAlong (64 * l) 4 / 64) 0 + beta.valF xv V *
        (vals xv V eL).getD (keccakAlong (64 * l) 3 / 64) 0) := by
  refine forall₂_map_eq (mapTB_spec_mem (P := fun l v => v = _) _ (fun l hl m hm => ?_) n h)
  have hl' := List.mem_range.mp hl
  obtain ⟨g1, g2⟩ := (thold_bind _ _).mp hm
  rw [tb_bind, gMul_spec g2, gMul_spec g1, getD_vals (i := l) eL (by (clear * - hL hl'; omega)),
    getD_vals (i := keccakAlong (64 * l) 3 / 64) eL (lt_of_lt_of_le (along_lt l hl').1 hL),
    getD_vals (i := keccakAlong (64 * l) 4 / 64) eL (lt_of_lt_of_le (along_lt l hl').2 hL)]
  ring

/-- One coordinate of `indexMle`: `acc·(1 + r·(1 + g^{2^k}))`, the constant in `K`. -/
def gIndexStep (z : Src) (k : Nat) (acc r : Src) : TB Src :=
  gScale (1 + FK.x ^ (2 ^ k)) r >>= fun u => gOne u >>= fun w => gMul acc w z

theorem gIndexStep_spec {xv : Src → FE} {V : Nat → FE} {z : Src} (hz : z.valF xv V = 0) (k : Nat) (acc r : Src)
    (n : Nat) (h : THold xv V n (gIndexStep z k acc r n).2) :
    (gIndexStep z k acc r n).1.valF xv V = acc.valF xv V * (1 + r.valF xv V * (1 + gen ^ (2 ^ k))) := by
  obtain ⟨g1, h⟩ := (thold_bind _ _).mp h
  obtain ⟨g2, g3⟩ := (thold_bind _ _).mp h
  rw [gIndexStep, tb_bind, tb_bind, gMul_spec g3, gOne_spec g2, gScale_spec g1, hz, add_zero,
    show FE.ofK (1 + FK.x ^ 2 ^ k) = 1 + gen ^ 2 ^ k by
      show FE.ofKRingHom (1 + FK.x ^ 2 ^ k) = _
      rw [map_add, map_pow, map_one]; rfl]
  ring

/-- `indexMleFrom (g^{2^k})` over the coordinates `rs`. -/
def gIndex (z : Src) : Nat → Src → List Src → TB Src
  | _, acc, [] => pure acc
  | k, acc, r :: rs => gIndexStep z k acc r >>= fun acc' => gIndex z (k + 1) acc' rs

theorem gIndex_spec {xv : Src → FE} {V : Nat → FE} {z : Src} (hz : z.valF xv V = 0) :
    ∀ (rs : List Src) (k : Nat) (acc : Src) (n : Nat), THold xv V n (gIndex z k acc rs n).2 →
      (gIndex z k acc rs n).1.valF xv V = indexMleFrom (gen ^ (2 ^ k)) (vals xv V rs) (acc.valF xv V)
  | [], k, acc, n, _ => rfl
  | r :: rs, k, acc, n, h => by
    obtain ⟨g1, g2⟩ := (thold_bind _ _).mp h
    have e1 := gIndexStep_spec hz k acc r n g1
    have e2 := gIndex_spec hz rs (k + 1) _ _ g2
    rw [e1] at e2
    have hp : (gen ^ (2 ^ k)) ^ 2 = gen ^ (2 ^ (k + 1)) := by rw [← pow_mul, pow_succ]
    show (gIndex z (k + 1) (gIndexStep z k acc r n).1 rs (n + (gIndexStep z k acc r n).2.length)).1.valF xv V = _
    rw [e2]
    simp only [vals, List.map_cons, indexMleFrom, hp]

end Lvm.Q1
end
-- ===== end of `LvmQKeccakParts2` =====

/-!
# QA1: one Keccak GKR layer as a loop template (`layerTB`)

The template of one layer of `F`'s `verifyKeccakLayer` on a table of `2^(P+4)` instances (`CH`:
`P = 16`, `KS`: `P = 11`). The claim is carried from the previous iteration through `C = 57 + P`
copy rows at the template's end (`cb` is the first): `value, μ[16], κ, point[P+1], B[25], a[6],
flip[7]`; the weights are `Lᵀ(eq(a) ⊗ B)` (or the first claim's `lanes ⊗ x^z` when the layer's
`first` constant is `1`). Per-layer constants (`K` cells, 16 per layer from `cst`): the RC bits at
`2^i − 1` of both segments (`14`), `first`, the gate. Stream: the layer's first product scalar is
lane `q`; a layer is `366 + 15(P+1)` lanes.
-/

set_option autoImplicit false

namespace Lvm.Q1

open Lvm Lvm.Loop

/-- The layer's configuration. -/
structure LCfg where
  /-- Pack rounds minus one (`logSteps − 4`). -/
  P : Nat
  /-- The lane of the first product scalar at layer `0`. -/
  q : Nat
  /-- The first constant cell. -/
  cst : Nat
  /-- The first carried copy row. -/
  cb : Nat

/-- Lanes per layer. -/
def LCfg.str (c : LCfg) : Nat := 366 + 15 * (c.P + 1)

/-- Carried rows. -/
def LCfg.C (c : LCfg) : Nat := 57 + c.P

/-- A carried input (the previous iteration's copy `j`). -/
def LCfg.pv (c : LCfg) (j : Nat) : Src := .prev (c.cb + j)

/-- A constant `K` cell of the layer. -/
def LCfg.k (c : LCfg) (j : Nat) : Src := .ext ⟨.K, c.cst + j, [16]⟩

/-- A copy row. -/
def gCopy (a : Src) : TB Src := gLin 0 0 a a

/-- **The layer.** -/
def layerTB (c : LCfg) : TB Unit :=
  let str := [c.str]
  let value := c.pv 0
  let mu := (List.range 16).map fun i => c.pv (1 + i)
  let kappa := c.pv 17
  let point := (List.range (c.P + 1)).map fun i => c.pv (18 + i)
  let B := (List.range 25).map fun l => c.pv (19 + c.P + l)
  let a := (List.range 6).map fun i => c.pv (44 + c.P + i)
  let flips := (List.range 7).map fun i => c.pv (50 + c.P + i)
  let q := c.q
  gZero (.ext ⟨.K, q, str⟩) >>= fun z => gOne z >>= fun one =>
  mapTB (fun k => gLoad (q + 3 * k) str) (List.range productBits) >>= fun prod =>
  gLoad (q + 141) str >>= fun s =>
  gProj z rmfeProject mu prod >>= fun proj =>
  gOne (point.getD c.P default) >>= fun seg0 =>
  gDot z ((List.range 7).map fun i => (c.k i, flips.getD i default)) >>= fun in0 =>
  gDot z ((List.range 7).map fun i => (c.k (7 + i), flips.getD i default)) >>= fun in1 =>
  gDot z [(seg0, in0), (point.getD c.P default, in1)] >>= fun iota =>
  gMul iota kappa proj >>= fun e1 => gAdd e1 value >>= fun e1' => gAssert e1' (c.k 15) >>= fun _ =>
  gInst z one s rmfeEmbed >>= fun mk =>
  gHorner s (prod.getD 46 default) ((List.range 46).reverse.map fun k => prod.getD k default) >>= fun v0 =>
  gPackRounds z str (q + 150) point v0 one >>= fun pk =>
  gLocalRounds str 11 (q + 150 + 15 * (c.P + 1)) pk.1 >>= fun lc =>
  let q3 := q + 348 + 15 * (c.P + 1)
  mapTB (fun k => gLoad (q3 + 3 * k) str) (List.range 3) >>= fun t =>
  gLoad (q3 + 9) str >>= fun beta =>
  gEqTab z [one] (lc.2.take 3) >>= fun tbLo => gEqTab z [one] ((lc.2.drop 3).take 3) >>= fun tbHi =>
  gEqTab z [one] (a.take 3) >>= fun taLo => gEqTab z [one] (a.drop 3) >>= fun taHi =>
  gEqTab z [one] (lc.2.drop 6) >>= fun eL =>
  mapTB (gLowTab z taLo tbLo 0) (List.range 8) >>= fun L0 =>
  mapTB (gLowTab z taLo tbLo 1) (List.range 8) >>= fun L1 =>
  mapTB (gHighTab z taHi tbHi) (List.range 8) >>= fun H =>
  mapTB (gShift z L0 L1 H) (List.range 64) >>= fun sh =>
  gSumMap z 25 (fun l => gLaneForm z B (fun r => sh.getD r default) l >>= fun lf =>
    gMul (eL.getD l default) lf z) >>= fun Wk =>
  gSumMap z 25 (fun l => gMul (eL.getD l default) (B.getD l default) z) >>= fun dfB =>
  gIndex z 0 one (lc.2.take 6) >>= fun idx => gMul dfB idx z >>= fun Wf =>
  gAdd Wf Wk >>= fun d => gMul (c.k 14) d Wk >>= fun W =>
  gMul mk.2 (t.getD 0 default) z >>= fun kt0 => gAdd mk.2 (t.getD 1 default) >>= fun k1 =>
  gMul k1 (t.getD 2 default) kt0 >>= fun m => gMul pk.2.1 W z >>= fun sw => gMul sw m lc.1 >>= fun e2 =>
  gAssert e2 (c.k 15) >>= fun _ =>
  gMul beta (t.getD 2 default) (t.getD 1 default) >>= fun tt => gMul beta tt (t.getD 0 default) >>= fun v' =>
  gLaneW eL beta >>= fun B' =>
  gEqTab z [one] (lc.2.take 6) >>= fun A' =>
  mapTB (gFlip z B' A') (List.range 7) >>= fun fl =>
  mapTB gCopy ([v'] ++ mk.1 ++ [mk.2] ++ pk.2.2 ++ B' ++ lc.2.take 6 ++ fl) >>= fun _ => pure ()

end Lvm.Q1
