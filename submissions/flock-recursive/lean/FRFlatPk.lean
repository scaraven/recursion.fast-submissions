-- New for `flock-recursive` (stage V4 of `flock-x2`; IV §5e, V0 §5): the flat evaluator, proved.
import FRVIRTplRun

/-!
# The flat evaluator of indexed rows

Indexed rows (`List (ℕ × Row)`) are evaluated by their sparse value `rowsVal` at split eq tables. For
a large irregular family that is one product per row and per term. Here the rows are **packed** once
(at process start, from the plan's own row lists) and the packed form is evaluated with one product
per *segment*:

* **terms** (`termsOf`): every `(matrix, coefficient, row, cell)`; a row `i` is split at `2^11`
  (`ih`, `il`) and a cell `j` at `2^12` (`jh`, `jl`), as the split tables are;
* **blocks** `(matrix, coefficient, ih, jh)`, each a **token stream**: a key token `2k + 1` starts a
  segment (row low `il = k`, or in a *transposed* block cell low `jl = k`), an element token `2e`
  adds the other low index `e` to it;
* **value** (`evalPk`): `Σ_blk c · thi[ih] · shi[jh] · Σ_seg A[key] · Σ_e B[e]`, the inner sums
  `Σ_e B[e]` by word `xor` (`+` on `F` is `xor`, `tokGo`): no product, no allocation per term.

**Correctness** has three generic parts and no data-specific proof:

* `evalPk_dec`: the evaluator is the sum over its decoding `dec`, for every packed value;
* `pack_perm`: the decoding of `pack rows` is a permutation of the rows' terms. `pack` puts the
  terms in buckets (`bktA`, one counting-sort pass; `bktA_perm`); a bucket whose terms share their
  block becomes one block (checked, `sameB`; else one block per term), its tokens by `encA`
  (`decT_encA`: the tokens decode to the entries). The bucket of a term (`blkIds`, a hash map of the
  blocks) and which blocks are transposed (`flagsA`) are heuristics: no proof depends on them;
* `evalPk_rows`: at the split eq tables of `(t, u)`, `evalPk (tabsOf n m t u) (pack rows)` is the
  rows' three sparse values `rowsVal`.
-/

namespace FR
namespace Flat
open Circ TEval

/-! ## Terms -/

/-- A term of indexed rows: matrix `s` (`0, 1, 2` for `a, b, c`), coefficient, row, cell. -/
structure Tm where
  s : ℕ
  c : F
  i : ℕ
  j : ℕ

/-- A form's terms at matrix `s`, row `i`, in front of `acc`. -/
def tl (s i : ℕ) : Lin → List Tm → List Tm
  | [], acc => acc
  | e :: l, acc => ⟨s, e.2, i, e.1⟩ :: tl s i l acc

/-- **The rows' terms**, row by row, matrices `a`, `b`, `c`. -/
def termsOf (rows : List (ℕ × Row)) : List Tm :=
  rows.foldr (fun p acc => tl 0 p.1 p.2.a (tl 1 p.1 p.2.b (tl 2 p.1 p.2.c acc))) []

/-- A value placed at matrix `s`. -/
def place (s : ℕ) (v : F) : F3 := if s = 0 then (v, 0, 0) else if s = 1 then (0, v, 0) else (0, 0, v)

theorem place_add (s : ℕ) (a b : F) : place s (a + b) = place s a + place s b := by
  unfold place; split_ifs <;> simp

theorem place_zero (s : ℕ) : place s 0 = 0 := by unfold place; split_ifs <;> rfl

theorem sum_place {α : Type} (s : ℕ) (f : α → F) (l : List α) :
    (l.map fun x => place s (f x)).sum = place s ((l.map f).sum) := by
  induction l with
  | nil => simp [place_zero]
  | cons x l ih => simp only [List.map_cons, List.sum_cons, ih, place_add]

/-- A term's value at the row and cell weights `gt`, `gs`. -/
def tval (gt gs : ℕ → F) (x : Tm) : F3 := place x.s (x.c * (gt x.i * gs x.j))

theorem sum_tl (gt gs : ℕ → F) (s i : ℕ) : ∀ (l : Lin) (acc : List Tm),
    ((tl s i l acc).map (tval gt gs)).sum =
      place s (gt i * (l.map fun e => e.2 * gs e.1).sum) + (acc.map (tval gt gs)).sum
  | [], acc => by simp [tl, place_zero]
  | e :: l, acc => by
    rw [tl, List.map_cons, List.sum_cons, sum_tl gt gs s i l acc, List.map_cons, List.sum_cons, mul_add,
      place_add, add_assoc]
    have h : tval gt gs ⟨s, e.2, i, e.1⟩ = place s (gt i * (e.2 * gs e.1)) := by
      simp only [tval]; exact congrArg (place s) (by ring)
    rw [h]

/-- **The terms' value is the rows' three sparse values** (with eq functions). -/
theorem sum_termsOf (gt gs : ℕ → F) (rows : List (ℕ × Row)) :
    ((termsOf rows).map (tval gt gs)).sum =
      (rowsValI (RingHom.id F) .a gt gs rows, rowsValI (RingHom.id F) .b gt gs rows,
        rowsValI (RingHom.id F) .c gt gs rows) := by
  simp only [rowsValI, linEI, cmul_eq, sumL_eq, RingHom.id_apply]
  induction rows with
  | nil => rfl
  | cons p rows ih =>
    simp only [termsOf, List.foldr_cons] at ih ⊢
    rw [sum_tl, sum_tl, sum_tl, ih]
    simp only [List.map_cons, List.sum_cons, Mat.r, place]
    refine Prod.ext ?_ (Prod.ext ?_ ?_) <;> simp

/-! ## The packed form and its evaluation -/

/-- A block: matrix, coefficient, row high `ih`, cell high `jh`, transposed or not, its tokens. -/
structure Blk where
  s : ℕ
  c : F
  ih : ℕ
  jh : ℕ
  tr : Bool
  tk : Array ℕ

/-- **A packed family.** -/
abbrev Pk := List Blk

/-- Split tables: rows at `2^11`, cells at `2^12`. -/
structure Tabs where
  tlo : Array F
  thi : Array F
  slo : Array F
  shi : Array F

/-- **The split eq tables of `(t, u)`** over `n` row and `m` cell coordinates. -/
def tabsOf (n m : ℕ) (t u : ℕ → F) : Tabs :=
  ⟨loTab 11 t, loTab (n - 11) (fun l => t (11 + l)), loTab 12 u, loTab (m - 12) (fun l => u (12 + l))⟩

/-- **A token stream's value** from token `k` on: the open segment's key `cur` and its `xor` sum in
the words `(x0, x1)`, the closed segments' sum `tot`. A key token closes the open segment (one
product) and opens its own; an element token is one table read and two word `xor`s. -/
def tokGo (A B : Array F) (tk : Array ℕ) (k cur : ℕ) (x0 x1 : UInt64) (tot : F) : F :=
  if h : k < tk.size then
    if tk[k] % 2 = 1 then tokGo A B tk (k + 1) (tk[k] / 2) 0 0 (tot + A.getD cur 0 * ⟨⟨x0⟩, ⟨x1⟩⟩)
    else
      let x := B.getD (tk[k] / 2) 0
      tokGo A B tk (k + 1) cur (x0 ^^^ x.c₀.val) (x1 ^^^ x.c₁.val) tot
  else tot + A.getD cur 0 * ⟨⟨x0⟩, ⟨x1⟩⟩
termination_by tk.size - k

/-- The tokens' entries `(key, element)`, from the key `cur` on. -/
def decT : ℕ → List ℕ → List (ℕ × ℕ)
  | _, [] => []
  | cur, t :: ts => if t % 2 = 1 then decT (t / 2) ts else (cur, t / 2) :: decT cur ts

theorem mk_xor (a0 a1 : UInt64) (x : F) :
    (⟨⟨a0 ^^^ x.c₀.val⟩, ⟨a1 ^^^ x.c₁.val⟩⟩ : F) = ⟨⟨a0⟩, ⟨a1⟩⟩ + x := rfl

theorem mk_zero : (⟨⟨0⟩, ⟨0⟩⟩ : F) = 0 := rfl

theorem tokGo_eq (A B : Array F) (tk : Array ℕ) (k cur : ℕ) (x0 x1 : UInt64) (tot : F) :
    tokGo A B tk k cur x0 x1 tot = tot + A.getD cur 0 * ⟨⟨x0⟩, ⟨x1⟩⟩ +
      ((decT cur (tk.toList.drop k)).map fun p => A.getD p.1 0 * B.getD p.2 0).sum := by
  fun_induction tokGo A B tk k cur x0 x1 tot with
  | case1 k cur x0 x1 tot h ht ih =>
    rw [ih, List.drop_eq_getElem_cons (i := k) (by simp only [Array.length_toList]; omega),
      Array.getElem_toList, decT, mk_zero, mul_zero, add_zero]
    simp only [ht, ↓reduceIte]
  | case2 k cur x0 x1 tot h ht x ih =>
    rw [ih, List.drop_eq_getElem_cons (i := k) (by simp only [Array.length_toList]; omega),
      Array.getElem_toList, decT, mk_xor, mul_add]
    simp only [ht, ↓reduceIte, List.map_cons, List.sum_cons, x]; abel
  | case3 k cur x0 x1 tot h =>
    rw [List.drop_eq_nil_of_le (by simp only [Array.length_toList]; omega)]
    simp [decT]

/-- **`F.mul` on words** (V5): the product's body on the operands' four words, so that the token
loop below keeps its sums in words and allocates nothing per segment (`mulW_eq`: it is `F.mul`). -/
@[inline] def mulW (a0 a1 b0 b1 : UInt64) : UInt64 × UInt64 :=
  let p0 := B64.clmul64 a0 b0
  let p1 := B64.clmul64 a1 b1
  let pm := B64.clmul64 (a0 ^^^ a1) (b0 ^^^ b1)
  let r1 := B64.reduce p1.lo p1.hi
  (B64.reduce (p0.lo ^^^ (r1 <<< 63)) (p0.hi ^^^ (r1 >>> 1)), B64.reduce (pm.lo ^^^ p0.lo) (pm.hi ^^^ p0.hi))

theorem mulW_eq (a : F) (x0 x1 s0 s1 : UInt64) :
    (⟨⟨s0 ^^^ (mulW a.c₀.val a.c₁.val x0 x1).1⟩, ⟨s1 ^^^ (mulW a.c₀.val a.c₁.val x0 x1).2⟩⟩ : F) =
      ⟨⟨s0⟩, ⟨s1⟩⟩ + a * ⟨⟨x0⟩, ⟨x1⟩⟩ := rfl

/-- **`tokGo` on words** (V5): the closed segments' sum `(s0, s1)` in words, each segment's product
by `mulW` (`tokW_eq`). -/
def tokW (A B : Array F) (tk : Array ℕ) (k cur : ℕ) (x0 x1 s0 s1 : UInt64) : UInt64 × UInt64 :=
  if h : k < tk.size then
    if tk[k] % 2 = 1 then
      let a := A.getD cur 0
      let p := mulW a.c₀.val a.c₁.val x0 x1
      tokW A B tk (k + 1) (tk[k] / 2) 0 0 (s0 ^^^ p.1) (s1 ^^^ p.2)
    else
      let x := B.getD (tk[k] / 2) 0
      tokW A B tk (k + 1) cur (x0 ^^^ x.c₀.val) (x1 ^^^ x.c₁.val) s0 s1
  else
    let a := A.getD cur 0
    let p := mulW a.c₀.val a.c₁.val x0 x1
    (s0 ^^^ p.1, s1 ^^^ p.2)
termination_by tk.size - k

/-- `tokW`'s words are `tokGo`'s value. -/
theorem tokW_eq (A B : Array F) (tk : Array ℕ) (k cur : ℕ) (x0 x1 s0 s1 : UInt64) :
    (⟨⟨(tokW A B tk k cur x0 x1 s0 s1).1⟩, ⟨(tokW A B tk k cur x0 x1 s0 s1).2⟩⟩ : F) =
      tokGo A B tk k cur x0 x1 ⟨⟨s0⟩, ⟨s1⟩⟩ := by
  fun_induction tokW A B tk k cur x0 x1 s0 s1 with
  | case1 k cur x0 x1 s0 s1 h ht a p ih =>
    rw [ih]; conv_rhs => rw [tokGo, dif_pos h, if_pos ht]
    rfl
  | case2 k cur x0 x1 s0 s1 h ht x ih =>
    rw [ih]; conv_rhs => rw [tokGo, dif_pos h, if_neg ht]
  | case3 k cur x0 x1 s0 s1 h a p =>
    conv_rhs => rw [tokGo, dif_neg h]
    rfl

/-- A block's value: its tokens at the low tables (`tokW`, V5), the high factors, the coefficient (no
product for `1`). -/
def blkV (T : Tabs) (b : Blk) : F :=
  let p := if b.tr then tokW T.slo T.tlo b.tk 0 0 0 0 0 0 else tokW T.tlo T.slo b.tk 0 0 0 0 0 0
  let v : F := ⟨⟨p.1⟩, ⟨p.2⟩⟩
  let w := T.thi.getD b.ih 0 * (T.shi.getD b.jh 0 * v)
  if b.c == 1 then w else b.c * w

/-- `acc + Σ_blk` its value, placed at its matrix. -/
def evalGo (T : Tabs) : Pk → F3 → F3
  | [], acc => acc
  | b :: P, acc => evalGo T P (add3 acc (place b.s (blkV T b)))

/-- **The flat evaluator.** -/
def evalPk (T : Tabs) (P : Pk) : F3 := evalGo T P (0, 0, 0)

/-! ## Decoding -/

/-- A split term: matrix, coefficient, `ih`, `il`, `jh`, `jl`. -/
structure T6 where
  s : ℕ
  c : F
  ih : ℕ
  il : ℕ
  jh : ℕ
  jl : ℕ

/-- A term split at `2^11` (row) and `2^12` (cell). -/
def split6 (x : Tm) : T6 := ⟨x.s, x.c, x.i / 2 ^ 11, x.i % 2 ^ 11, x.j / 2 ^ 12, x.j % 2 ^ 12⟩

/-- A block's split terms. -/
def decBlk (b : Blk) : List T6 :=
  (decT 0 b.tk.toList).map fun p => if b.tr then ⟨b.s, b.c, b.ih, p.2, b.jh, p.1⟩ else ⟨b.s, b.c, b.ih, p.1, b.jh, p.2⟩

/-- **The decoding**: the packed value's split terms. -/
def dec (P : Pk) : List T6 := P.flatMap decBlk

/-- A split term's value at the tables. -/
def qv (T : Tabs) (x : T6) : F3 :=
  place x.s (x.c * ((T.tlo.getD x.il 0 * T.thi.getD x.ih 0) * (T.slo.getD x.jl 0 * T.shi.getD x.jh 0)))

theorem sum_map_flatMap {α β γ : Type} [AddCommMonoid γ] (l : List α) (f : α → List β) (g : β → γ) :
    ((l.flatMap f).map g).sum = (l.map fun a => ((f a).map g).sum).sum := by
  induction l with
  | nil => simp
  | cons a l ih => simp only [List.flatMap_cons, List.map_append, List.sum_append, ih, List.map_cons, List.sum_cons]

theorem tokV_eq (A B : Array F) (tk : Array ℕ) :
    tokGo A B tk 0 0 0 0 0 = ((decT 0 tk.toList).map fun p => A.getD p.1 0 * B.getD p.2 0).sum := by
  rw [tokGo_eq, mk_zero, mul_zero, add_zero, zero_add, List.drop_zero]

/-- `tokV_eq` for `tokW` (V5). -/
theorem tokWV_eq (A B : Array F) (tk : Array ℕ) :
    (⟨⟨(tokW A B tk 0 0 0 0 0 0).1⟩, ⟨(tokW A B tk 0 0 0 0 0 0).2⟩⟩ : F) =
      ((decT 0 tk.toList).map fun p => A.getD p.1 0 * B.getD p.2 0).sum := by
  rw [tokW_eq, show (⟨⟨0⟩, ⟨0⟩⟩ : F) = 0 from rfl, tokV_eq]

theorem blkV_eq (T : Tabs) (b : Blk) : place b.s (blkV T b) = ((decBlk b).map (qv T)).sum := by
  unfold blkV decBlk
  have hc : ∀ w : F, (if (b.c == 1) = true then w else b.c * w) = b.c * w := fun w => by
    split_ifs with h
    · rw [beq_iff_eq.1 h, one_mul]
    · rfl
  simp only [hc, List.map_map]
  cases hb : b.tr
  · simp only [Bool.false_eq_true, ↓reduceIte, tokWV_eq]
    have hq : (qv T ∘ fun p : ℕ × ℕ => (⟨b.s, b.c, b.ih, p.1, b.jh, p.2⟩ : T6)) = fun p : ℕ × ℕ =>
        place b.s (b.c * (T.thi.getD b.ih 0 * (T.shi.getD b.jh 0 * (T.tlo.getD p.1 0 * T.slo.getD p.2 0)))) := by
      funext p; simp only [Function.comp_def, qv]; exact congrArg (place b.s) (by ring)
    rw [hq, sum_place, List.sum_map_mul_left, List.sum_map_mul_left, List.sum_map_mul_left]
  · simp only [↓reduceIte, tokWV_eq]
    have hq : (qv T ∘ fun p : ℕ × ℕ => (⟨b.s, b.c, b.ih, p.2, b.jh, p.1⟩ : T6)) = fun p : ℕ × ℕ =>
        place b.s (b.c * (T.thi.getD b.ih 0 * (T.shi.getD b.jh 0 * (T.slo.getD p.1 0 * T.tlo.getD p.2 0)))) := by
      funext p; simp only [Function.comp_def, qv]; exact congrArg (place b.s) (by ring)
    rw [hq, sum_place, List.sum_map_mul_left, List.sum_map_mul_left, List.sum_map_mul_left]

theorem evalGo_eq (T : Tabs) : ∀ (P : Pk) (acc : F3),
    evalGo T P acc = acc + (P.map fun b => place b.s (blkV T b)).sum
  | [], acc => by simp [evalGo]
  | b :: P, acc => by rw [evalGo, evalGo_eq T P, List.map_cons, List.sum_cons, ← add_assoc]; rfl

/-- **The evaluator is the sum over its decoding** (every packed value). -/
theorem evalPk_dec (T : Tabs) (P : Pk) : evalPk T P = ((dec P).map (qv T)).sum := by
  rw [evalPk, evalGo_eq, show ((0, 0, 0) : F3) = 0 from rfl, zero_add, dec, sum_map_flatMap]
  exact congrArg List.sum (List.map_congr_left fun b _ => blkV_eq T b)

/-! ## A counting-sort pass -/

/-- **Buckets** `0 … K`, digit `d x mod (K + 1)` (each bucket in reverse order). -/
def bktA {α : Type} (K : ℕ) (d : α → ℕ) (l : List α) : Array (List α) :=
  l.foldl (fun A x => A.modify (d x % (K + 1)) (x :: ·)) (Array.replicate (K + 1) [])

theorem flatten_modify {α : Type} (x : α) : ∀ (L : List (List α)) (k : ℕ), k < L.length →
    (L.modify k (x :: ·)).flatten.Perm (x :: L.flatten)
  | [], _, h => absurd h (Nat.not_lt_zero _)
  | b :: L, 0, _ => by simp
  | b :: L, k + 1, h => by
    simp only [List.modify_succ_cons, List.flatten_cons]
    exact ((flatten_modify x L k (by simpa using h)).append_left b).trans List.perm_middle

theorem bktA_fold {α : Type} (K : ℕ) (d : α → ℕ) : ∀ (l : List α) (A : Array (List α)), A.size = K + 1 →
    (l.foldl (fun A x => A.modify (d x % (K + 1)) (x :: ·)) A).toList.flatten.Perm (l ++ A.toList.flatten)
  | [], A, _ => by simp
  | x :: l, A, h => by
    rw [List.foldl_cons]
    refine (bktA_fold K d l _ (by rw [Array.size_modify, h])).trans ?_
    rw [Array.toList_modify]
    refine ((flatten_modify x _ _ (by rw [Array.length_toList, h]; exact Nat.mod_lt _ (Nat.succ_pos K))).append_left
      l).trans ?_
    simp only [List.cons_append]
    exact List.perm_middle

/-- **The buckets hold the list.** -/
theorem bktA_perm {α : Type} (K : ℕ) (d : α → ℕ) (l : List α) : (bktA K d l).toList.flatten.Perm l := by
  have h := bktA_fold K d l (Array.replicate (K + 1) []) (Array.size_replicate ..)
  simpa [bktA] using h

/-! ## Token streams -/

/-- **The tokens of entries**, left to right: a key token `2k + 1` where the key changes (and first),
then the element token `2e`. -/
def encL {α : Type} (kf ef : α → ℕ) : Option ℕ → List α → List ℕ
  | _, [] => []
  | p, y :: l => (if p = some (kf y) then [] else [2 * kf y + 1]) ++ 2 * ef y :: encL kf ef (some (kf y)) l

/-- `encL` into an array (the plan's). -/
def encA {α : Type} (kf ef : α → ℕ) : List α → Option ℕ → Array ℕ → Array ℕ
  | [], _, acc => acc
  | y :: l, p, acc =>
    encA kf ef l (some (kf y)) ((if p = some (kf y) then acc else acc.push (2 * kf y + 1)).push (2 * ef y))

theorem encA_toList {α : Type} (kf ef : α → ℕ) : ∀ (l : List α) (p : Option ℕ) (acc : Array ℕ),
    (encA kf ef l p acc).toList = acc.toList ++ encL kf ef p l
  | [], _, _ => by simp [encA, encL]
  | y :: l, p, acc => by
    rw [encA, encA_toList kf ef l, encL]
    split_ifs <;> simp

theorem decT_odd (cur k : ℕ) (s : List ℕ) : decT cur ((2 * k + 1) :: s) = decT k s := by
  rw [decT, show (2 * k + 1) % 2 = 1 by omega, show (2 * k + 1) / 2 = k by omega]; rfl

theorem decT_even (cur e : ℕ) (s : List ℕ) : decT cur (2 * e :: s) = (cur, e) :: decT cur s := by
  rw [decT, show 2 * e % 2 = 0 by omega, show 2 * e / 2 = e by omega]; rfl

/-- **The tokens decode to the entries** (from the key `cur`, the encoder's last key `cur` or none). -/
theorem decT_encL {α : Type} (kf ef : α → ℕ) : ∀ (l : List α) (cur : ℕ) (p : Option ℕ), (p = none ∨ p = some cur) →
    decT cur (encL kf ef p l) = l.map fun y => (kf y, ef y)
  | [], _, _, _ => rfl
  | y :: l, cur, p, hp => by
    rw [encL]
    by_cases h : p = some (kf y)
    · have hc : kf y = cur := by
        rcases hp with hp | hp
        · rw [hp] at h; cases h
        · rw [hp] at h; exact (Option.some.inj h).symm
      rw [if_pos h, List.nil_append, decT_even, hc, decT_encL kf ef l cur _ (Or.inr rfl), List.map_cons, hc]
    · rw [if_neg h, List.singleton_append, decT_odd, decT_even, decT_encL kf ef l _ _ (Or.inr rfl), List.map_cons]

theorem decT_encA {α : Type} (kf ef : α → ℕ) (l : List α) :
    decT 0 (encA kf ef l none #[]).toList = l.map fun y => (kf y, ef y) := by
  rw [encA_toList]; exact decT_encL kf ef l 0 none (Or.inl rfl)

/-! ## Packing -/

/-- A term's block, as a hash key (a heuristic: it only chooses the bucket). -/
def bkey (x : Tm) : F × ℕ := (x.c, (x.s * 2 ^ 24 + x.i / 2 ^ 11) * 2 ^ 24 + x.j / 2 ^ 12)

/-- The blocks' bucket numbers, in order of first appearance (a heuristic). -/
def blkIds (ts : List Tm) : Std.HashMap (F × ℕ) ℕ :=
  ts.foldl (fun m x => let k := bkey x; if m.contains k then m else m.insert k m.size) {}

/-- Which buckets to transpose (a heuristic): those with fewer distinct `jl` than distinct `il`. -/
def flagsA (B : Array (List Tm)) : Array Bool := Id.run do
  let mut sI : Array ℕ := Array.replicate (2 ^ 11) 0
  let mut sJ : Array ℕ := Array.replicate (2 ^ 12) 0
  let mut out : Array Bool := Array.mkEmpty B.size
  let mut st := 1
  for b in B do
    let mut nI := 0
    let mut nJ := 0
    for y in b do
      let il := y.i % 2 ^ 11
      let jl := y.j % 2 ^ 12
      if sI.getD il 0 != st then
        nI := nI + 1
        sI := sI.set! il st
      if sJ.getD jl 0 != st then
        nJ := nJ + 1
        sJ := sJ.set! jl st
    out := out.push (decide (nJ < nI))
    st := st + 1
  return out

/-- `y` is in `x`'s block. -/
def sameB (x y : Tm) : Bool :=
  y.s == x.s && y.c == x.c && y.i / 2 ^ 11 == x.i / 2 ^ 11 && y.j / 2 ^ 12 == x.j / 2 ^ 12

theorem sameB_refl (x : Tm) : sameB x x = true := by simp [sameB]

/-- A block's terms by `jl`: a merge sort for a small block, else a bucket pass. -/
def sortJ (l : List Tm) : List Tm :=
  if l.length ≤ 2 ^ 9 then l.mergeSort fun a b => decide (a.j % 2 ^ 12 ≤ b.j % 2 ^ 12)
  else (bktA (2 ^ 12) (fun y => y.j % 2 ^ 12) l).toList.flatten

theorem sortJ_perm (l : List Tm) : (sortJ l).Perm l := by
  unfold sortJ; split_ifs
  · exact List.mergeSort_perm _ _
  · exact bktA_perm _ _ _

/-- **A block** of `x`'s terms `l`: segments by `il`, or (transposed) by `jl` after sorting by `jl`. -/
def mkBlk (f : Bool) (x : Tm) (l : List Tm) : Blk :=
  if f then
    ⟨x.s, x.c, x.i / 2 ^ 11, x.j / 2 ^ 12, true,
      encA (fun y => y.j % 2 ^ 12) (fun y => y.i % 2 ^ 11) (sortJ l) none #[]⟩
  else ⟨x.s, x.c, x.i / 2 ^ 11, x.j / 2 ^ 12, false, encA (fun y => y.i % 2 ^ 11) (fun y => y.j % 2 ^ 12) l none #[]⟩

/-- A bucket's blocks: one if its terms share their block, else one per term. -/
def blksOf (f : Bool) : List Tm → List Blk
  | [] => []
  | x :: l => if (x :: l).all (sameB x) then [mkBlk f x (x :: l)] else (x :: l).map fun y => mkBlk false y [y]

/-- **The packed rows.** -/
def pack (rows : List (ℕ × Row)) : Pk :=
  let ts := termsOf rows
  let ids := blkIds ts
  let B := bktA ids.size (fun x => ids.getD (bkey x) 0) ts
  let fl := flagsA B
  B.toList.zipIdx.flatMap fun p => blksOf (fl.getD p.2 false) p.1

/-! ## The packing permutes the terms -/

theorem perm_flatMap_congr {α β : Type} {l : List α} {f g : α → List β} (h : ∀ a ∈ l, (f a).Perm (g a)) :
    (l.flatMap f).Perm (l.flatMap g) := by
  induction l with
  | nil => exact List.Perm.refl _
  | cons a l ih =>
    simp only [List.flatMap_cons]
    exact (h a (List.mem_cons_self ..)).append (ih fun b hb => h b (List.mem_cons_of_mem _ hb))

theorem split6_same {x y : Tm} (h : sameB x y = true) :
    split6 y = ⟨x.s, x.c, x.i / 2 ^ 11, y.i % 2 ^ 11, x.j / 2 ^ 12, y.j % 2 ^ 12⟩ := by
  simp only [sameB, Bool.and_eq_true, beq_iff_eq] at h
  obtain ⟨⟨⟨h1, h2⟩, h3⟩, h4⟩ := h
  simp only [split6, h1, h2, h3, h4]

theorem mkBlk_dec (f : Bool) (x : Tm) (l : List Tm) (h : l.all (sameB x) = true) :
    (decBlk (mkBlk f x l)).Perm (l.map split6) := by
  rw [List.all_eq_true] at h
  unfold mkBlk decBlk
  cases f
  · simp only [Bool.false_eq_true, ↓reduceIte, decT_encA, List.map_map]
    rw [List.map_congr_left fun y hy => by simp only [Function.comp_def]; exact (split6_same (h y hy)).symm]
  · simp only [↓reduceIte, decT_encA, List.map_map]
    have hp := sortJ_perm l
    rw [List.map_congr_left fun y hy => by
      simp only [Function.comp_def]; exact (split6_same (h y (hp.subset hy))).symm]
    exact hp.map _

theorem blksOf_perm (f : Bool) : ∀ l : List Tm, ((blksOf f l).flatMap decBlk).Perm (l.map split6)
  | [] => List.Perm.refl _
  | x :: l => by
    simp only [blksOf]
    split_ifs with h
    · rw [List.flatMap_singleton]; exact mkBlk_dec f x _ h
    · rw [List.flatMap_map, List.map_eq_flatMap]
      exact perm_flatMap_congr fun y _ => by
        have := mkBlk_dec false y [y] (by simp [sameB_refl])
        simpa using this

/-- **The decoding of `pack rows` is a permutation of the rows' split terms.** -/
theorem pack_perm (rows : List (ℕ × Row)) : (dec (pack rows)).Perm ((termsOf rows).map split6) := by
  unfold dec pack
  dsimp only
  generalize hB : bktA _ _ (termsOf rows) = B
  rw [List.flatMap_assoc]
  refine (perm_flatMap_congr fun p _ => blksOf_perm _ p.1).trans ?_
  have hz : ∀ L : List (List Tm), (L.zipIdx.flatMap fun p => p.1.map split6) = L.flatten.map split6 := by
    intro L
    rw [show (L.zipIdx.flatMap fun p => p.1.map split6) = (L.zipIdx.map Prod.fst).flatMap (fun b => b.map split6)
      by rw [List.flatMap_map], List.zipIdx_map_fst]
    induction L with
    | nil => rfl
    | cons b L ih => simp [ih]
  rw [hz, ← hB]
  exact (bktA_perm _ _ _).map _

/-! ## The value -/

/-- **The packed rows' value** at any tables: the terms' value at the split functions. -/
theorem evalPk_pack (T : Tabs) (rows : List (ℕ × Row)) :
    evalPk T (pack rows) =
      ((termsOf rows).map (tval (splitAt T.tlo T.thi (2 ^ 11)) (splitAt T.slo T.shi (2 ^ 12)))).sum := by
  rw [evalPk_dec, ((pack_perm rows).map (qv T)).sum_eq, List.map_map]
  rfl

/-- **At the split eq tables of `(t, u)`, the packed rows' value is the rows' sparse value.** -/
theorem evalPk_rows {n m : ℕ} (hn : 11 ≤ n) (hm : 12 ≤ m) (t u : ℕ → F) (rows : List (ℕ × Row)) :
    evalPk (tabsOf n m t u) (pack rows) =
      (rowsVal (RingHom.id F) .a n m t u rows, rowsVal (RingHom.id F) .b n m t u rows,
        rowsVal (RingHom.id F) .c n m t u rows) := by
  have ht : splitAt (loTab 11 t) (loTab (n - 11) fun l => t (11 + l)) (2 ^ 11) = gN n t := splitE_eq hn t
  have hu : splitAt (loTab 12 u) (loTab (m - 12) fun l => u (12 + l)) (2 ^ 12) = gN m u := splitE_eq hm u
  rw [evalPk_pack, sum_termsOf]
  simp only [tabsOf, ht, hu, rowsValI_eq]

/-! ## Controls -/

/-- (+) Tokens decode to their entries, a key token re-opening a segment; (−) an element before any key token
reads the key `cur`. -/
theorem decT_ctl : decT 0 [3, 4, 6, 5, 2] = [(1, 2), (1, 3), (2, 1)] ∧ decT 7 [4, 3, 2] = [(7, 2), (1, 1)] := by
  decide

/-- (+) Entries encode with one key token per run; (−) a key that returns opens a new segment. -/
theorem encL_ctl : encL Prod.fst Prod.snd none [(1, 2), (1, 3), (2, 1)] = [3, 4, 6, 5, 2] ∧
    encL Prod.fst Prod.snd none [(1, 2), (2, 1), (1, 3)] = [3, 4, 5, 2, 3, 6] := by
  decide

/-- (+) Two terms in one block; (−) the same row and cell lows with another cell high. -/
theorem sameB_ctl : sameB ⟨0, ⟨⟨1⟩, ⟨0⟩⟩, 5, 7⟩ ⟨0, ⟨⟨1⟩, ⟨0⟩⟩, 6, 8⟩ = true ∧
    sameB ⟨0, ⟨⟨1⟩, ⟨0⟩⟩, 5, 7⟩ ⟨0, ⟨⟨1⟩, ⟨0⟩⟩, 6, 4100⟩ = false := by
  decide

/-- (+) A bucket of one block gives one block; (−) a mixed bucket gives one block per term. -/
theorem blksOf_ctl : (blksOf false [⟨0, ⟨⟨1⟩, ⟨0⟩⟩, 5, 7⟩, ⟨0, ⟨⟨1⟩, ⟨0⟩⟩, 6, 8⟩]).length = 1 ∧
    (blksOf false [⟨0, ⟨⟨1⟩, ⟨0⟩⟩, 5, 7⟩, ⟨0, ⟨⟨1⟩, ⟨0⟩⟩, 6, 4100⟩]).length = 2 := by
  decide

/-- (+) A token stream's value in words is its segments' products: key `1` over elements `0, 2`, key `0` over
element `1`, `5 · (2 + 6) + 3 · 7 = 29` in `GF(2^128)`; (−) with two elements' places swapped it is not
(V5, review V24 m-1: `tokW`, so `tokGo`). -/
theorem tokW_ctl :
    (tokW #[⟨⟨3⟩, ⟨0⟩⟩, ⟨⟨5⟩, ⟨0⟩⟩] #[⟨⟨2⟩, ⟨0⟩⟩, ⟨⟨7⟩, ⟨0⟩⟩, ⟨⟨6⟩, ⟨0⟩⟩] #[3, 0, 4, 1, 2] 0 0 0 0 0 0) = (29, 0) ∧
    (tokW #[⟨⟨3⟩, ⟨0⟩⟩, ⟨⟨5⟩, ⟨0⟩⟩] #[⟨⟨2⟩, ⟨0⟩⟩, ⟨⟨6⟩, ⟨0⟩⟩, ⟨⟨7⟩, ⟨0⟩⟩] #[3, 0, 4, 1, 2] 0 0 0 0 0 0) ≠ (29, 0) := by
  decide +kernel

/-- (+) The counting-sort pass puts each element in its digit's bucket (each bucket last first); (−) another
digit puts them elsewhere (V5, review V24 m-1). -/
theorem bktA_ctl : bktA 2 (· % 3) [0, 1, 2, 3, 4] = #[[3, 0], [4, 1], [2]] ∧
    bktA 2 (· % 3) [0, 1, 2, 3, 4] ≠ bktA 2 (fun x => (x + 1) % 3) [0, 1, 2, 3, 4] := by
  decide

/-- (+) Two rows packed and evaluated at small tables are their direct sum (`a`: rows 5 and 2 at cell 7,
`(6·9 + 3·9)·(17·18) = 10794`; `b`: row 5 at cell `4100 = 2^12 + 4`, coefficient 3, `3·(6·9·(14·19)) = 13780`;
products in `GF(2^128)`); (−) with row 2's cell moved to 6 the value differs (V5, review V24 m-1:
`evalPk ∘ pack`; `pack`'s bucket map is a hash map, so the controls go through `evalPk_pack`, then the kernel
evaluates the terms). -/
theorem evalPk_pack_ctl :
    evalPk ⟨#[⟨⟨1⟩, ⟨0⟩⟩, ⟨⟨2⟩, ⟨0⟩⟩, ⟨⟨3⟩, ⟨0⟩⟩, ⟨⟨4⟩, ⟨0⟩⟩, ⟨⟨5⟩, ⟨0⟩⟩, ⟨⟨6⟩, ⟨0⟩⟩, ⟨⟨7⟩, ⟨0⟩⟩, ⟨⟨8⟩, ⟨0⟩⟩],
        #[⟨⟨9⟩, ⟨0⟩⟩], #[⟨⟨10⟩, ⟨0⟩⟩, ⟨⟨11⟩, ⟨0⟩⟩, ⟨⟨12⟩, ⟨0⟩⟩, ⟨⟨13⟩, ⟨0⟩⟩, ⟨⟨14⟩, ⟨0⟩⟩, ⟨⟨15⟩, ⟨0⟩⟩,
          ⟨⟨16⟩, ⟨0⟩⟩, ⟨⟨17⟩, ⟨0⟩⟩], #[⟨⟨18⟩, ⟨0⟩⟩, ⟨⟨19⟩, ⟨0⟩⟩]⟩
        (pack [(5, ⟨[(7, 1)], [(4100, ⟨⟨3⟩, ⟨0⟩⟩)], []⟩), (2, ⟨[(7, 1)], [], []⟩)]) =
      (⟨⟨10794⟩, ⟨0⟩⟩, ⟨⟨13780⟩, ⟨0⟩⟩, 0) ∧
    evalPk ⟨#[⟨⟨1⟩, ⟨0⟩⟩, ⟨⟨2⟩, ⟨0⟩⟩, ⟨⟨3⟩, ⟨0⟩⟩, ⟨⟨4⟩, ⟨0⟩⟩, ⟨⟨5⟩, ⟨0⟩⟩, ⟨⟨6⟩, ⟨0⟩⟩, ⟨⟨7⟩, ⟨0⟩⟩, ⟨⟨8⟩, ⟨0⟩⟩],
        #[⟨⟨9⟩, ⟨0⟩⟩], #[⟨⟨10⟩, ⟨0⟩⟩, ⟨⟨11⟩, ⟨0⟩⟩, ⟨⟨12⟩, ⟨0⟩⟩, ⟨⟨13⟩, ⟨0⟩⟩, ⟨⟨14⟩, ⟨0⟩⟩, ⟨⟨15⟩, ⟨0⟩⟩,
          ⟨⟨16⟩, ⟨0⟩⟩, ⟨⟨17⟩, ⟨0⟩⟩], #[⟨⟨18⟩, ⟨0⟩⟩, ⟨⟨19⟩, ⟨0⟩⟩]⟩
        (pack [(5, ⟨[(7, 1)], [(4100, ⟨⟨3⟩, ⟨0⟩⟩)], []⟩), (2, ⟨[(6, 1)], [], []⟩)]) ≠
      (⟨⟨10794⟩, ⟨0⟩⟩, ⟨⟨13780⟩, ⟨0⟩⟩, 0) := by
  rw [evalPk_pack, evalPk_pack]
  simp only [termsOf, tl, List.foldr_cons, List.foldr_nil, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    add_zero]
  decide +kernel

end Flat
end FR
