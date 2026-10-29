-- New for `flock-recursive` (R-OPS §5.2, stage R3: the chain template library).
import FRVIRTplLag

/-!
# Chain templates: a gadget builder with value lemmas

Replay templates (`Tpl`) are gate lists with locals numbered in gate order. Writing one by hand means
tracking every stage's first local (`FRVIRTplRepLW`'s `lwK8 … lwK13`). This module gives a builder
that tracks the locals itself, and Hoare-style value lemmas that compose without offset arithmetic.

* **`GM α`**: from a first local `k`, a gate list and a result (forms over the template's wires).
  `ret`, `bind` (the second part's locals follow the first's), `gate`.
* **`GM.Ok e g P`**: wherever the gate equations of `g` hold at `e` (from any first local), its
  result satisfies `P`. `ok_ret`, `ok_bind`, `ok_mono`; `ok_mapL`, `ok_foldL`, `ok_iterL` for the
  list combinators `mapL` (independent instances), `foldL` (a chain through a list), `iterL` (a
  chain of `n` steps returning every value).
* **Gadgets on `F`** (one gate each): `mulF`; on **`K`** as a pair of `F` forms (`KF`, value `evK`):
  `mulK` (Karatsuba, `mulKG`), `sqK` (two gates), `smulK` (an `F` form times a `K` pair, two
  gates), and the linear ones `oneK`, `zeroK`, `addK`, `sumK`, `ofFK`, `oneSubK` (no gates).
* **The chains** (R-OPS §5.2's shapes): `sqChainF`/`sqChainK` (`x^(2^i)`, `i ≤ n`; `sqIter`),
  `powF` (`x^i`, `i ≤ n`), `prodK` (a product chain), `hornerKG` (`KW.hornerK`), `phiG`
  (`phiTable`'s tree).

Every lemma is generic in the template's wires: the gadgets are reusable by any replay template.
-/

namespace FR
namespace Tpl
open Circ

/-- **A gadget builder**: from its first local, its gates and its result. -/
abbrev GM (α : Type) := ℕ → List Gate × α

namespace GM

variable {α β γ : Type} {e : Env}

/-- No gates. -/
def ret (a : α) : GM α := fun _ => ([], a)

/-- `g`, then `f` of its result, whose locals follow `g`'s. -/
def bind (g : GM α) (f : α → GM β) : GM β := fun k =>
  ((g k).1 ++ (f (g k).2 (k + nlocs (g k).1)).1, (f (g k).2 (k + nlocs (g k).1)).2)

/-- `g`, its result mapped (no gates; no copy of `g`'s gates). -/
def map (g : GM α) (h : α → β) : GM β := fun k => ((g k).1, h (g k).2)

/-- One gate, its result read from its first local. -/
def gate (g : Gate) (out : ℕ → α) : GM α := fun k => ([g], out k)

/-- **`g` computes `P`**: wherever its gate equations hold at `e`, its result satisfies `P`. -/
def Ok (e : Env) (g : GM α) (P : α → Prop) : Prop := ∀ k, Eqns e (g k).1 k → P (g k).2

theorem ok_ret {P : α → Prop} {a : α} (h : P a) : Ok e (ret a) P := fun _ _ => h

theorem ok_bind {g : GM α} {f : α → GM β} {P : α → Prop} {Q : β → Prop} (hg : Ok e g P)
    (hf : ∀ a, P a → Ok e (f a) Q) : Ok e (g.bind f) Q := fun k h => by
  have h' := Eqns.append.1 h
  exact hf _ (hg k h'.1) _ h'.2

theorem ok_map {g : GM α} {h : α → β} {P : α → Prop} {Q : β → Prop} (hg : Ok e g P)
    (hh : ∀ a, P a → Q (h a)) : Ok e (g.map h) Q := fun k hk => hh _ (hg k hk)

theorem ok_mono {g : GM α} {P Q : α → Prop} (hg : Ok e g P) (h : ∀ a, P a → Q a) : Ok e g Q :=
  fun k hk => h _ (hg k hk)

/-! ## List combinators -/

/-- Independent instances, one per element. -/
def mapL (f : α → GM β) : List α → GM (List β)
  | [] => ret []
  | a :: as => (f a).bind fun b => (mapL f as).map fun bs => b :: bs

theorem ok_mapL {f : α → GM β} {E : β → γ} {v : α → γ} :
    ∀ l : List α, (∀ a ∈ l, Ok e (f a) fun b => E b = v a) → Ok e (mapL f l) fun bs => bs.map E = l.map v
  | [], _ => ok_ret rfl
  | a :: as, h =>
    ok_bind (h a (List.mem_cons_self ..)) fun b hb =>
      ok_map (ok_mapL as fun x hx => h x (List.mem_cons_of_mem _ hx)) fun bs hbs => by
        simp [hb, hbs]

/-- **A chain through a list**: `b ↦ f b a` for each element in turn. -/
def foldL (f : β → α → GM β) : β → List α → GM β
  | b, [] => ret b
  | b, a :: as => (f b a).bind fun b' => foldL f b' as

theorem ok_foldL {f : β → α → GM β} {E : β → γ} {g : γ → α → γ} :
    ∀ (l : List α) (b : β), (∀ b a, a ∈ l → Ok e (f b a) fun b' => E b' = g (E b) a) →
      Ok e (foldL f b l) fun b' => E b' = l.foldl g (E b)
  | [], _, _ => ok_ret rfl
  | a :: as, b, h =>
    ok_bind (h b a (List.mem_cons_self ..)) fun b' hb' =>
      ok_mono (ok_foldL as b' fun c x hx => h c x (List.mem_cons_of_mem _ hx)) fun r hr => by
        rw [hr, hb', List.foldl_cons]

/-- **A chain of `n` steps**, every value: `[b, f b, f (f b), …]` (`n + 1` entries). -/
def iterL (f : β → GM β) : ℕ → β → GM (List β)
  | 0, b => ret [b]
  | n + 1, b => (f b).bind fun b' => (iterL f n b').map fun bs => b :: bs

theorem ok_iterL {f : β → GM β} {E : β → γ} {g : γ → γ} (hf : ∀ b, Ok e (f b) fun b' => E b' = g (E b)) :
    ∀ (n : ℕ) (b : β), Ok e (iterL f n b) fun bs => bs.map E = (List.range (n + 1)).map fun i => g^[i] (E b)
  | 0, _ => ok_ret rfl
  | n + 1, b =>
    ok_bind (hf b) fun b' hb' => ok_map (ok_iterL hf n b') fun bs hbs => (by
      rw [List.map_cons, hbs, List.range_succ_eq_map (n := n + 1), List.map_cons, List.map_map]
      simp only [Function.comp_def, Function.iterate_succ_apply, hb', Function.iterate_zero_apply])

theorem iterL_length {f : β → GM β} : ∀ (n : ℕ) (b : β) (k : ℕ), ((iterL f n b) k).2.length = n + 1
  | 0, _, _ => rfl
  | n + 1, b, k => by
    simp only [iterL, bind, map, List.length_cons, iterL_length n]

end GM

open GM

variable {e : Env}

/-! ## Gadgets -/

/-- A `K` value as its two `F` forms. -/
abbrev KF := LinT × LinT

/-- An `F` product (one gate). -/
def mulF (a b : LinT) : GM LinT := gate (.mul a b) L

theorem ok_mulF (a b : LinT) : Ok e (mulF a b) fun o => o.ev e = a.ev e * b.ev e := fun k h => by
  have := (Eqns.cons.1 h).1
  simpa [mulF, gate, Gate.Eqn] using this

/-- A `K` product (Karatsuba, three gates: `mulKG`). -/
def mulK (a b : KF) : GM KF := mulKG a b

theorem ok_mulK (a b : KF) : Ok e (mulK a b) fun o => evK e o = evK e a * evK e b :=
  fun k h => mulKG_ev a b k h

/-- **A `K` square** (two gates): `(a₀² + α a₁², a₁²)`. -/
def sqK (a : KF) : GM KF := fun k =>
  ([.mul a.1 a.1, .mul a.2 a.2], (L k ++ sc F.alpha (L (k + 1)), L (k + 1)))

theorem ok_sqK (a : KF) : Ok e (sqK a) fun o => evK e o = evK e a * evK e a := fun k h => by
  simp only [sqK, Eqns.cons, Gate.Eqn, Gate.nloc, Eqns.nil, and_true] at h
  obtain ⟨h0, h1⟩ := h
  apply K_ext'
  · rw [K_mul_f₀]; simp only [evK, sqK, ev_append, ev_sc, ev_L, h0, h1]
  · rw [K_mul_f₁]; simp only [evK, sqK, ev_L, h1]
    linear_combination (-(a.1.ev e * a.1.ev e) - a.1.ev e * a.2.ev e) * CharTwo.two_eq_zero (R := F)

/-- **An `F` form times a `K` pair** (two gates). -/
def smulK (c : LinT) (a : KF) : GM KF := fun k => ([.mul c a.1, .mul c a.2], (L k, L (k + 1)))

theorem ok_smulK (c : LinT) (a : KF) : Ok e (smulK c a) fun o => evK e o = K.ofF (c.ev e) * evK e a :=
  fun k h => by
    simp only [smulK, Eqns.cons, Gate.Eqn, Gate.nloc, Eqns.nil, and_true] at h
    obtain ⟨h0, h1⟩ := h
    rw [← K.smulF_eq_mul]
    exact K_ext' (by simp only [evK, smulK, ev_L, h0]; rfl) (by simp only [evK, smulK, ev_L, h1]; rfl)

/-- `1`, `0`, `a + b`, a sum, an `F` form in `K`, `1 − a` (linear: no gates). -/
def oneK : KF := (C 1, [])
def zeroK : KF := ([], [])
def addK (a b : KF) : KF := (a.1 ++ b.1, a.2 ++ b.2)
def sumK (l : List KF) : KF := (l.flatMap (·.1), l.flatMap (·.2))
def ofFK (c : LinT) : KF := (c, [])
def oneSubK (a : KF) : KF := (C 1 ++ a.1, a.2)

theorem evK_oneK (h1 : e.one = 1) : evK e oneK = 1 := by
  apply K_ext' <;> simp [evK, oneK, h1] <;> rfl
theorem evK_zeroK : evK e zeroK = 0 := rfl
theorem evK_addK (a b : KF) : evK e (addK a b) = evK e a + evK e b :=
  K_ext' (by simp only [evK, addK, ev_append, K_add_f₀]) (by simp only [evK, addK, ev_append, K_add_f₁])
theorem evK_sumK : ∀ l : List KF, evK e (sumK l) = (l.map (evK e)).sum
  | [] => rfl
  | a :: l => by
    have ih := evK_sumK l
    simp only [sumK, List.flatMap_cons, List.map_cons, List.sum_cons] at ih ⊢
    rw [← ih]
    exact K_ext' (by simp only [evK, ev_append, K_add_f₀]) (by simp only [evK, ev_append, K_add_f₁])
theorem evK_ofFK (c : LinT) : evK e (ofFK c) = K.ofF (c.ev e) := rfl
theorem evK_oneSubK (h1 : e.one = 1) (a : KF) : evK e (oneSubK a) = 1 - evK e a :=
  K_ext' (by simp only [evK, oneSubK, ev_append, ev_C, h1, mul_one, K_one_sub_f₀])
    (by simp only [evK, oneSubK, K_one_sub_f₁, zero_add])

/-! ## Chains -/

theorem iterate_sq {R : Type*} [CommRing R] : ∀ (i : ℕ) (x : R), (fun y => y * y)^[i] x = sqIter i x
  | 0, _ => rfl
  | i + 1, x => by rw [Function.iterate_succ_apply, iterate_sq i, sqIter]

/-- **The squaring chain in `F`**: `x^(2^i)` for `i ≤ n`. -/
def sqChainF (n : ℕ) (x : LinT) : GM (List LinT) := iterL (fun y => mulF y y) n x

theorem ok_sqChainF (n : ℕ) (x : LinT) :
    Ok e (sqChainF n x) fun ys => ys.map (LinT.ev e) = (List.range (n + 1)).map fun i => sqIter i (x.ev e) :=
  ok_mono (ok_iterL (g := fun y => y * y) (fun y => ok_mulF y y) n x) fun ys h => by
    rw [h]; exact List.map_congr_left fun i _ => iterate_sq i _

/-- **The squaring chain in `K`**: `x^(2^i)` for `i ≤ n` (two gates per step). -/
def sqChainK (n : ℕ) (x : KF) : GM (List KF) := iterL sqK n x

theorem ok_sqChainK (n : ℕ) (x : KF) :
    Ok e (sqChainK n x) fun ys => ys.map (evK e) = (List.range (n + 1)).map fun i => sqIter i (evK e x) :=
  ok_mono (ok_iterL (g := fun y => y * y) ok_sqK n x) fun ys h => by
    rw [h]; exact List.map_congr_left fun i _ => iterate_sq i _

theorem iterate_mul {R : Type*} [CommMonoid R] (i : ℕ) (x : R) : (fun y => y * x)^[i] 1 = x ^ i := by
  induction i with
  | zero => simp
  | succ i ih => rw [Function.iterate_succ_apply', ih, pow_succ]

/-- **The powers** `x^i`, `i ≤ n` (one gate per step). -/
def powF (n : ℕ) (x : LinT) : GM (List LinT) := iterL (fun y => mulF y x) n (C 1)

theorem ok_powF (h1 : e.one = 1) (n : ℕ) (x : LinT) :
    Ok e (powF n x) fun ys => ys.map (LinT.ev e) = (List.range (n + 1)).map fun i => x.ev e ^ i :=
  ok_mono (ok_iterL (g := fun y => y * x.ev e) (fun y => ok_mulF y x) n (C 1)) fun ys h => by
    rw [h]
    refine List.map_congr_left fun i _ => ?_
    rw [ev_C, h1, mul_one]
    exact iterate_mul i _

theorem foldl_mul_map {R : Type*} [CommMonoid R] {α : Type*} (g : α → R) :
    ∀ (l : List α) (c : R), l.foldl (fun y x => y * g x) c = c * (l.map g).prod
  | [], c => by simp
  | x :: l, c => by rw [List.foldl_cons, foldl_mul_map g l, List.map_cons, List.prod_cons, mul_assoc]

/-- **A product chain in `K`**: `Π l` (`|l| − 1` products; `1` for the empty list). -/
def prodK : List KF → GM KF
  | [] => ret oneK
  | a :: as => foldL mulK a as

theorem ok_prodK (h1 : e.one = 1) : ∀ l : List KF, Ok e (prodK l) fun o => evK e o = (l.map (evK e)).prod
  | [] => ok_ret (evK_oneK h1)
  | a :: as => ok_mono (ok_foldL (g := fun y x => y * evK e x) as a fun b x _ => ok_mulK b x) fun o h => by
      rw [h, List.map_cons, List.prod_cons, foldl_mul_map]

/-- **Horner in `K`**: `Σ_j (Π_{l<j} s (o + l)) y_j` (`KW.hornerK`), one product per entry. -/
def hornerKG (s : ℕ → KF) : ℕ → List KF → GM KF
  | _, [] => ret zeroK
  | o, y :: ys => (hornerKG s (o + 1) ys).bind fun h => (mulK (s o) h).map (addK y)

theorem ok_hornerKG (s : ℕ → KF) : ∀ (o : ℕ) (ys : List KF),
    Ok e (hornerKG s o ys) fun h => evK e h = KW.hornerK (fun l => evK e (s l)) o (ys.map (evK e))
  | _, [] => ok_ret rfl
  | o, y :: ys =>
    ok_bind (ok_hornerKG s (o + 1) ys) fun h hh => ok_map (ok_mulK (s o) h) fun m hm => by
      rw [evK_addK, hm, hh, List.map_cons, KW.hornerK]

/-- **`phiTable`'s tree** over `F` forms: the later stages' table `t`, then `t_e · f^(2^e)`. -/
def phiG : List LinT → GM (List LinT)
  | [] => ret [C 1]
  | f :: fs => (phiG fs).bind fun t => (sqChainF (t.length - 1) f).bind fun pw =>
      (mapL (fun p : LinT × LinT => mulF p.1 p.2) (t.zip pw)).map fun m => t ++ m

theorem phiTable_cons_toList {R : Type*} [CommRing R] (f : R) (fs : List R) :
    (phiTable (f :: fs)).toList = (phiTable fs).toList ++
      ((List.range (phiTable fs).size).map fun i => (phiTable fs).toList.getD i 0 * sqIter i f) := by
  rw [phiTable, Array.toList_append, Array.toList_ofFn]
  congr 1
  refine List.ext_getElem (by simp) fun i h1 h2 => ?_
  simp only [List.getElem_ofFn, List.getElem_map, List.getElem_range]
  rw [List.getD_eq_getElem _ _ (by simpa using h1)]
  simp

/-- **`phiG` computes `phiTable`.** -/
theorem ok_phiG (h1 : e.one = 1) : ∀ fs : List LinT,
    Ok e (phiG fs) fun t => t.map (LinT.ev e) = (phiTable (fs.map (LinT.ev e))).toList
  | [] => ok_ret (by simp [phiTable, ev_C, h1])
  | f :: fs => ok_bind (ok_phiG h1 fs) fun t ht => ok_bind (ok_sqChainF _ f) fun pw hpw =>
      ok_map (ok_mapL (E := LinT.ev e) (v := fun p : LinT × LinT => p.1.ev e * p.2.ev e) _
        fun p _ => ok_mulF p.1 p.2) fun m hm => (by
      have hl : t.length = (phiTable (fs.map (LinT.ev e))).size := by
        simpa using congrArg List.length ht
      have hpos : 0 < t.length := by rw [hl, phiTable_size]; exact Nat.two_pow_pos _
      rw [List.map_append, hm, ht, List.map_cons, phiTable_cons_toList, ← hl]
      congr 1
      have hpl : pw.length = t.length := by
        have := congrArg List.length hpw; simp at this; omega
      refine List.ext_getElem (by simp [hpl]) fun i h1' h2' => ?_
      simp only [List.length_map, List.length_zip, hpl, min_self] at h1'
      have hpi : (pw.map (LinT.ev e))[i]'(by simp [hpl, h1']) = sqIter i (f.ev e) := by
        rw [List.getElem_of_eq hpw]; simp
      simp only [List.getElem_map, List.getElem_zip, List.getElem_range]
      rw [← ht, List.getD_eq_getElem _ _ (by simpa using h1'), List.getElem_map]
      simp only [List.getElem_map] at hpi
      rw [hpi])

end Tpl
end FR
