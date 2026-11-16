-- New for lvm2 E2F (slice S1, E2F-Q; E2AC-DES §1.2, the coordinate-split zerocheck): the wiring of a program with
-- `E2` twin rows. Statement 13 (`PhiQCX_eq`) frozen on day 0; its proof is E2F-Q's.
import LvmWiring
import LvmTypedLHolds

/-!
# The wiring with `E2` rows: two coordinates per slot, read in `E2 ⊗_K E3`

E2AC-DES §1.2 names the mechanism "`Ty.E2`"; lvm2 E2F realises it without a third memory (E2F-LEAD, 2026-11-13):
an `E2` value is two `K` cells written by a twin pair of rows `e2 f false`, `e2 f true` (`LvmLoopIR`). The
first row's slot carries both coordinates.

* **Entries** (`instEntsX`): every entry has a matrix `o ∈ [0, 8)`, `o = m + 4s`: `m` the matrix (`A, B, D, W`),
  `s` the coordinate (`E2 = K ⊕ K·X`). Rows other than `e2` keep `instEnts`'s entries (`s = 0`). The first row of
  an `e2 mul` twin pair `[a₀, a₁, b₀, b₁, d₀, d₁]` at slot `x`: `A_s = a_s`, `B_s = b_s`, `D_s = d_s`, `W_0` its
  result cell, `W_1` the next `K` cell (the twin's result); `e2 (lin k k₀ k₁)`: `D_s = a_s + k·b_s + k_s·1`. The
  second row has no slot and no entries.
* **The relation** (`WiringRelX`): at every slot, with `M_o = (M_o z)(x)` and `A = A_0 + A_1 X` etc., the
  value `A·B + D + W` of `E2 ⊗_K E3` is zero, coordinate by coordinate (`X² = 1 + xX`):
  `relX0 = A₀B₀ + A₁B₁ + D₀ + W₀`, `relX1 = A₀B₁ + A₁B₀ + x·A₁B₁ + D₁ + W₁`. On slots without `s = 1` entries
  `relX1` is `0` and `relX0` is roll 8's relation.
* **`Φ_Q`** (`PhiQFX`, `PhiQX`): the sparse multilinear extension of the eight matrices in
  `phiVarsX = 3 + 20 + 21 = 44` variables, the selector `o` lowest (bits `m` then `s`), then `x`, then `y`.
* **The fast evaluator** (`PhiQCX`): roll 8's evaluator `PhiQC` on each coordinate's terms, combined by the
  selector bit `s` (`pt[2]`): `(1 + p₂)·Φ₀ + p₂·Φ₁`. The cache (`cacheWX`) and its check (`PhiCacheX.okB`) are
  `K.deriveTermsG`/`K.checkTermsG` on the coordinate's entries (`srcEntsX`). **`PhiQCX_eq`** (statement 13).
-/

set_option autoImplicit false

namespace Lvm.Typed

open Lvm.Loop LeanVM.Parameters

/-! ## Entries -/

/-- **The entries of one instance, coordinate-split**: an `e2` twin's first row at its slot (both coordinates;
the second row's result is the next `K` cell), every other row as `instEnts`. -/
def instEntsX (Q : Program) (lay : Lay) (i : Inst) : List Ent :=
  let x := lay.slot i.blk i.t i.jf
  let res1 : List (ℕ × FE) := lay.cellEnts .K (i.ck + 1) 1
  match i.row.op with
  | .e2 .mul false =>
      tagE 0 x (lay.argEnts i 0 1) ++ tagE 4 x (lay.argEnts i 1 1) ++
      tagE 1 x (lay.argEnts i 2 1) ++ tagE 5 x (lay.argEnts i 3 1) ++
      tagE 2 x (lay.argEnts i 4 1) ++ tagE 6 x (lay.argEnts i 5 1) ++
      tagE 3 x (lay.resEnts i) ++ tagE 7 x res1
  | .e2 (.lin k k₀ k₁) false =>
      tagE 2 x (lay.argEnts i 0 1 ++ lay.argEnts i 2 (FE.ofK k) ++ [(lay.one, FE.ofK k₀)]) ++
      tagE 6 x (lay.argEnts i 1 1 ++ lay.argEnts i 3 (FE.ofK k) ++ [(lay.one, FE.ofK k₁)]) ++
      tagE 3 x (lay.resEnts i) ++ tagE 7 x res1
  | .e2 _ true => []
  | _ => instEnts Q lay i

/-- **The eight matrices' entries** of `(Q, lay)`: every instance's, then the auxiliary rows' (`s = 0`). -/
def entsX (Q : Program) (lay : Lay) : List Ent := Q.insts.flatMap (instEntsX Q lay) ++ auxEnts lay

/-! ## The relation -/

/-- **`(M_o z)(x)`** for `o < 8` (`o = m + 4s`). -/
def matZX (Q : Program) (lay : Lay) (o : ℕ) (z : ℕ → FK) (x : ℕ) : FE :=
  ((entsX Q lay).filter fun e ↦ e.o == o && e.x == x).foldr (fun e acc ↦ e.c * FE.ofK (z e.y) + acc) 0

/-- Coordinate `1` of `A·B + D + W` at slot `x`: `A₀B₀ + A₁B₁ + D₀ + W₀` (`X² = 1 + xX`). -/
def relX0 (Q : Program) (lay : Lay) (z : ℕ → FK) (x : ℕ) : FE :=
  matZX Q lay 0 z x * matZX Q lay 1 z x + matZX Q lay 4 z x * matZX Q lay 5 z x + matZX Q lay 2 z x +
    matZX Q lay 3 z x

/-- Coordinate `X` of `A·B + D + W` at slot `x`: `A₀B₁ + A₁B₀ + x·A₁B₁ + D₁ + W₁`. -/
def relX1 (Q : Program) (lay : Lay) (z : ℕ → FK) (x : ℕ) : FE :=
  matZX Q lay 0 z x * matZX Q lay 5 z x + matZX Q lay 4 z x * matZX Q lay 1 z x +
    FE.ofK FK.x * (matZX Q lay 4 z x * matZX Q lay 5 z x) + matZX Q lay 6 z x + matZX Q lay 7 z x

/-- **The coordinate-split wiring relation**: `A z·B z + D z + W z = 0` in `E2 ⊗_K E3` at every slot, both
coordinates. -/
def WiringRelX (Q : Program) (lay : Lay) (z : ℕ → FK) : Prop :=
  ∀ x, relX0 Q lay z x = 0 ∧ relX1 Q lay z x = 0

/-! ## `Φ_Q` in 44 variables -/

/-- `Φ_Q`'s variables with the coordinate bit: the selector `o` (3: `m`, then `s`), `x` (20), `y` (21). -/
abbrev phiVarsX : ℕ := 3 + xVars + yVars

/-- An entry's index on the 44-variable cube: `o` the low 3 bits, then `x`, then `y`. -/
def Ent.idxX (e : Ent) : ℕ := e.o + 8 * (e.x + 2 ^ xVars * e.y)

/-- **`Φ_Q` natively, coordinate-split**: at a point of `phiVarsX` coordinates (`o ++ x ++ y`). -/
def PhiQFX (Q : Program) (lay : Lay) (pt : List FE) : FE :=
  (entsX Q lay).foldr (fun e acc ↦ e.c * eqW pt e.idxX + acc) 0

/-- **`Φ_Q` over `E`, coordinate-split** (the accumulator's `Φ`, 44 variables). -/
def PhiQX (Q : Program) (lay : Lay) (pt : List E) : E := FE.toExt3 (PhiQFX Q lay (pt.map FE.ofExt3))

/-- **Matrix `o`'s extension at `(r_x, r_y)`** (`o < 8`; natively; `rxy = r_x ++ r_y`). -/
def matMleFX (Q : Program) (lay : Lay) (o : ℕ) (rxy : List FE) : FE :=
  ((entsX Q lay).filter fun e ↦ e.o == o).foldr (fun e acc ↦ e.c * eqW rxy (e.x + 2 ^ xVars * e.y) + acc) 0

/-- Matrix `o`'s extension over `E`. -/
def matMleX (Q : Program) (lay : Lay) (o : ℕ) (rxy : List E) : E :=
  FE.toExt3 (matMleFX Q lay o (rxy.map FE.ofExt3))

/-! ## The fast evaluator -/

/-- Coordinate `s`'s entries of a row at an iteration (matrix `o mod 4`; the auxiliary rows are coordinate `0`). -/
def srcEntsX (Q : Program) (lay : Lay) (s : Bool) : TSrc → ℕ → List Ent
  | .row b t, jf => ((instEntsX Q lay (Q.inst b jf t)).filter fun e ↦ (e.o / 4 == 1) == s).map
      fun e ↦ { e with o := e.o % 4 }
  | .aux k r, j => if s then [] else auxRowEnts lay k r j

/-- The canonical term keys of coordinate `s`: every row's entry positions (a row's entry count does not depend
on the iteration). -/
def termKeysX (Q : Program) (lay : Lay) (s : Bool) : List (TSrc × ℕ) :=
  (rowsOf Q lay).flatMap fun src ↦ (List.range (srcEntsX Q lay s src 0).length).map (src, ·)

/-- The terms of coordinate `s`, in the canonical order (rows, then entry positions; `K.rowTermsG` per row). -/
def deriveTermsX (Q : Program) (lay : Lay) (s : Bool) : Array CTerm :=
  let ents : TSrc → ℕ → Array Ent := fun src jf ↦ (srcEntsX Q lay s src jf).toArray
  ((rowsOf Q lay).map fun src ↦ K.rowTermsG ents src (srcL Q lay src) (srcEntsX Q lay s src 0).length
    (match src with
      | .row b _ => K.fields (Q.blk b).dims
      | .aux k _ => [(0, (lay.aux.getD k default).l)])).foldl (· ++ ·) #[]

/-- **The coordinate-split cache**: one `PhiCache` per coordinate. -/
structure PhiCacheX where
  /-- Coordinate `1`'s terms and evaluator. -/
  c0 : PhiCache
  /-- Coordinate `X`'s terms and evaluator. -/
  c1 : PhiCache
  deriving Inhabited

/-- The cache of `(Q, lay)`: each coordinate's terms, compiled (`K.compileT`). -/
def cacheWX (Q : Program) (lay : Lay) : PhiCacheX :=
  let t0 := deriveTermsX Q lay false
  let t1 := deriveTermsX Q lay true
  ⟨⟨t0.toList, K.compileT t0⟩, ⟨t1.toList, K.compileT t1⟩⟩

/-- **The class check of one coordinate** (as `PhiCache.okB`, on `srcEntsX`): the terms are the canonical keys in
order, have their row's iteration count and are well formed, and are their row's entries at every iteration. -/
def PhiCache.okBX (Q : Program) (lay : Lay) (s : Bool) (c : PhiCache) : Bool :=
  c.terms.map (fun t ↦ (t.src, t.idx)) == termKeysX Q lay s &&
    c.terms.all (fun t ↦ t.l == srcL Q lay t.src && K.termWFB t) &&
    K.checkTermsG (srcEntsX Q lay s) c.terms.toArray

/-- **The class check of the coordinate-split cache.** -/
def PhiCacheX.okB (Q : Program) (lay : Lay) (c : PhiCacheX) : Bool :=
  c.c0.okBX Q lay false && c.c1.okBX Q lay true

/-- **The fast evaluator, coordinate-split**: `(1 + p₂)·Φ₀(p') + p₂·Φ₁(p')`, `p₂ = pt[2]` the coordinate bit and
`p'` the point without it (characteristic 2: `1 − p₂ = 1 + p₂`). -/
def PhiQCX (c : PhiCacheX) (pt : List FE) : FE :=
  let p := pt.getD 2 0
  let pt' := pt.take 2 ++ pt.drop 3
  (1 + p) * PhiQC c.c0 pt' + p * PhiQC c.c1 pt'

/-! ## Statement 13's proof -/

/-- `phi_checkTerms` on any entry function (the same loop). -/
theorem phi_checkTermsG (ents : TSrc → ℕ → List Ent) (ts : Array CTerm)
    (hl : ∀ k k', k < ts.size → k' < ts.size → (ts.getD k default).src = (ts.getD k' default).src →
      (ts.getD k default).l = (ts.getD k' default).l)
    (h : K.checkTermsG ents ts = true) :
    ∀ k < ts.size, ∀ jf < 2 ^ (ts.getD k default).l,
      (ents (ts.getD k default).src jf).toArray.getD (ts.getD k default).idx default =
        (ts.getD k default).at jf := by
  unfold K.checkTermsG at h
  dsimp only [Id.run] at h
  generalize hR : (forIn (m := Id) Lean.Loop.mk ((none : Option Bool), (0 : ℕ)) _) = R at h
  have hpost : (R.1 = none → ∀ k < ts.size, ∀ jf < 2 ^ (ts.getD k default).l,
      (ents (ts.getD k default).src jf).toArray.getD (ts.getD k default).idx default =
        (ts.getD k default).at jf) ∧ R.1 ≠ some true := by
    rw [← hR]
    refine phi_loop_inv _ (fun s : Option Bool × ℕ => s.1 = none ∧ s.2 ≤ ts.size ∧ ∀ k < s.2, ∀ jf < 2 ^ (ts.getD k default).l,
      (ents (ts.getD k default).src jf).toArray.getD (ts.getD k default).idx default =
        (ts.getD k default).at jf)
      (fun s : Option Bool × ℕ => (s.1 = none → ∀ k < ts.size, ∀ jf < 2 ^ (ts.getD k default).l,
      (ents (ts.getD k default).src jf).toArray.getD (ts.getD k default).idx default =
        (ts.getD k default).at jf) ∧ s.1 ≠ some true) (fun s : Option Bool × ℕ => ts.size - s.2) ?_ _ ⟨rfl, Nat.zero_le _, by simp⟩
    rintro ⟨o, i⟩ ⟨ho, hi, hgood⟩
    dsimp only at ho hi hgood ⊢
    subst ho
    by_cases hlt : i < ts.size
    · rw [ite_eq_left hlt]
      simp only [phi_id_bind]
      generalize hJd : (forIn (m := Id) Lean.Loop.mk i _) = J
      obtain ⟨J, rfl⟩ : ∃ J' : ℕ, J' = J := ⟨J, rfl⟩
      have hJ : i < J ∧ J ≤ ts.size ∧
          ∀ k, i ≤ k → k < J → (ts.getD k default).src = (ts.getD i default).src := by
        rw [← hJd]
        refine phi_loop_inv _ (fun j : ℕ => i ≤ j ∧ j ≤ ts.size ∧
            ∀ k, i ≤ k → k < j → (ts.getD k default).src = (ts.getD i default).src)
          (fun j : ℕ => i < j ∧ j ≤ ts.size ∧
            ∀ k, i ≤ k → k < j → (ts.getD k default).src = (ts.getD i default).src)
          (fun j => ts.size - j) ?_ i ⟨le_rfl, hi, fun k h1 h2 => absurd h2 (by omega)⟩
        rintro j ⟨h1, h2, h3⟩
        by_cases hc : (decide (j < ts.size) && (ts.getD j default).src == (ts.getD i default).src) = true
        · rw [ite_eq_left hc]
          simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at hc
          refine ⟨fun v hv => (by cases hv), fun v hv => ?_⟩
          cases hv
          refine ⟨⟨by omega, by omega, fun k hk1 hk2 => ?_⟩, by omega⟩
          rcases Nat.lt_succ_iff_lt_or_eq.1 hk2 with hk | rfl
          · exact h3 k hk1 hk
          · exact hc.2
        · rw [ite_eq_right hc]
          refine ⟨fun v hv => ?_, fun v hv => by cases hv⟩
          cases hv
          refine ⟨?_, h2, h3⟩
          rcases Nat.lt_or_eq_of_le h1 with h | rfl
          · exact h
          · exact absurd (by simp [hlt]) hc
      generalize hSd : (forIn (m := Id) [:2 ^ (ts.getD i default).l] ((none : Option Bool), ()) _) = S
      obtain ⟨S, rfl⟩ : ∃ S' : Option Bool × Unit, S' = S := ⟨S, rfl⟩
      have hS : (S.1 = none → ∀ jf < 2 ^ (ts.getD i default).l, ∀ k, i ≤ k → k < J →
          (ents (ts.getD i default).src jf).toArray.getD (ts.getD k default).idx default =
            (ts.getD k default).at jf) ∧ S.1 ≠ some true := by
        rw [← hSd, Std.Legacy.Range.forIn_eq_forIn_range']
        refine phi_forIn_early' _ _ (fun jf => ∀ k, i ≤ k → k < J →
          (ents (ts.getD i default).src jf).toArray.getD (ts.getD k default).idx default =
            (ts.getD k default).at jf) _ (fun H jf hjf => H jf (List.mem_range'_1.2 ⟨Nat.zero_le _, by simp only [Std.Legacy.Range.size]; omega⟩)) ?_
        intro jf _
        generalize hKd : (forIn (m := Id) [i:J] ((none : Option Bool), ()) _) = KR
        obtain ⟨KR, rfl⟩ : ∃ K' : Option Bool × Unit, K' = KR := ⟨KR, rfl⟩
        have hK : (KR.1 = none → ∀ k, i ≤ k → k < J →
            (ents (ts.getD i default).src jf).toArray.getD (ts.getD k default).idx default =
              (ts.getD k default).at jf) ∧ KR.1 ≠ some true := by
          rw [← hKd, Std.Legacy.Range.forIn_eq_forIn_range']
          refine phi_forIn_early' _ _ (fun k =>
            (ents (ts.getD i default).src jf).toArray.getD (ts.getD k default).idx default =
              (ts.getD k default).at jf) _
            (fun H k hk1 hk2 => H k (List.mem_range'_1.2 ⟨hk1, by simp only [Std.Legacy.Range.size]; omega⟩)) ?_
          intro k _
          by_cases hc : (!(ents (ts.getD i default).src jf).toArray.getD
              (ts.getD k default).idx default == (ts.getD k default).at jf) = true
          · rw [ite_eq_left hc]; right; rfl
          · rw [ite_eq_right hc]
            left
            exact ⟨rfl, by simpa using hc⟩
        obtain ⟨o', u⟩ := KR
        cases o' with
        | none => exact Or.inl ⟨rfl, hK.1 rfl⟩
        | some r =>
          cases r
          · exact Or.inr rfl
          · exact absurd rfl hK.2
      obtain ⟨o'', u⟩ := S
      cases o'' with
      | none =>
        refine ⟨fun v hv => (by cases hv), fun v hv => ?_⟩
        cases hv
        refine ⟨⟨rfl, hJ.2.1, fun k hk jf hjf => ?_⟩, by dsimp only; omega⟩
        by_cases hki : k < i
        · exact hgood k hki jf hjf
        · have hsrc := hJ.2.2 k (by omega) hk
          have hlk := hl k i (by omega) hlt hsrc
          rw [hsrc]
          exact hS.1 rfl jf (hlk ▸ hjf) k (by omega) hk
      | some r =>
        refine ⟨fun v hv => ?_, fun v hv => by cases hv⟩
        cases hv
        exact ⟨fun hn => (by cases hn), hS.2⟩
    · rw [ite_eq_right hlt]
      refine ⟨fun v hv => ?_, fun v hv => ?_⟩
      · cases hv
        exact ⟨fun _ k hk => hgood k (by omega), by simp⟩
      · cases hv
  obtain ⟨o, n⟩ := R
  cases o with
  | none => exact hpost.1 rfl
  | some r =>
    cases r
    · change false = true at h
      cases h
    · exact absurd rfl hpost.2

/-- `eqW` at a coordinate-split index: the coordinate bit splits off. -/
theorem eqW_idxX (a b c : FE) (rest : List FE) (o R : ℕ) (ho : o < 8) :
    eqW (a :: b :: c :: rest) (o + 8 * R) =
      (if o / 4 = 1 then c else 1 - c) * eqW (a :: b :: rest) (o % 4 + 4 * R) := by
  simp only [eqW]
  have e1 : (o + 8 * R) % 2 = o % 2 := by omega
  have e2 : (o + 8 * R) / 2 % 2 = o / 2 % 2 := by omega
  have e3 : (o + 8 * R) / 2 / 2 % 2 = o / 4 := by omega
  have e4 : (o + 8 * R) / 2 / 2 / 2 = R := by omega
  have f1 : (o % 4 + 4 * R) % 2 = o % 2 := by omega
  have f2 : (o % 4 + 4 * R) / 2 % 2 = o / 2 % 2 := by omega
  have f3 : (o % 4 + 4 * R) / 2 / 2 = R := by omega
  rw [e1, e2, e3, e4, f1, f2, f3]
  ring

/-- The selector split of one entry list (entries with matrices below `8`). -/
theorem phiX_split (L : List Ent) (hL : ∀ e ∈ L, e.o < 8) (a b c : FE) (rest : List FE) :
    (L.map fun e ↦ e.c * eqW (a :: b :: c :: rest) e.idxX).sum =
      (1 + c) * (((L.filter fun e ↦ (e.o / 4 == 1) == false).map fun e ↦ { e with o := e.o % 4 }).map
          fun e ↦ e.c * eqW (a :: b :: rest) e.idx).sum +
        c * (((L.filter fun e ↦ (e.o / 4 == 1) == true).map fun e ↦ { e with o := e.o % 4 }).map
          fun e ↦ e.c * eqW (a :: b :: rest) e.idx).sum := by
  induction L with
  | nil => simp
  | cons e L ih =>
    have he := hL e (List.mem_cons_self ..)
    have ih' := ih fun e' he' ↦ hL e' (List.mem_cons_of_mem _ he')
    have hx : e.c * eqW (a :: b :: c :: rest) e.idxX =
        (if e.o / 4 = 1 then c else 1 + c) * (e.c * eqW (a :: b :: rest) ({ e with o := e.o % 4 } : Ent).idx) := by
      show e.c * eqW _ (e.o + 8 * (e.x + 2 ^ xVars * e.y)) = _ * (e.c * eqW _ (e.o % 4 + 4 * (e.x + 2 ^ xVars * e.y)))
      rw [eqW_idxX a b c rest e.o _ he, show (1 : FE) - c = 1 + c from rfl]
      split <;> ring
    rw [List.map_cons, List.sum_cons, ih', hx]
    by_cases h4 : e.o / 4 = 1
    · have h4' : (e.o / 4 == 1) = true := by simpa using h4
      rw [List.filter_cons_of_neg (by simp [h4']), List.filter_cons_of_pos (by simp [h4'])]
      simp only [List.map_cons, List.sum_cons, if_pos h4]
      ring
    · have h4' : (e.o / 4 == 1) = false := by simpa using h4
      rw [List.filter_cons_of_pos (by simp [h4']), List.filter_cons_of_neg (by simp [h4'])]
      simp only [List.map_cons, List.sum_cons, if_neg h4]
      ring

theorem phiX_sum_add {α : Type} (l : List α) (f g : α → FE) :
    (l.map fun x ↦ f x + g x).sum = (l.map f).sum + (l.map g).sum := by
  induction l with
  | nil => simp
  | cons x l ih => simp only [List.map_cons, List.sum_cons, ih]; ring

theorem phiX_sum_mul {α : Type} (l : List α) (c : FE) (f : α → FE) :
    c * (l.map f).sum = (l.map fun x ↦ c * f x).sum := by
  induction l with
  | nil => simp
  | cons x l ih => simp only [List.map_cons, List.sum_cons, ← ih]; ring


/-- The raw entries of a row at an iteration (the eight matrices). -/
def rawX (Q : Program) (lay : Lay) : TSrc → ℕ → List Ent
  | .row b t, jf => instEntsX Q lay (Q.inst b jf t)
  | .aux k r, j => auxRowEnts lay k r j

theorem phiX_rows (Q : Program) (lay : Lay) (pt : List FE) :
    PhiQFX Q lay pt = ((rowsOf Q lay).map fun s => ((List.range (2 ^ srcL Q lay s)).map fun jf =>
      ((rawX Q lay s jf).map fun e => e.c * eqW pt e.idxX).sum).sum).sum := by
  unfold PhiQFX entsX rowsOf auxEnts
  rw [phi_foldr_eq_sum (fun e : Ent => e.c * eqW pt e.idxX)]
  simp only [List.map_append, List.sum_append, phi_sum_flatMap, phi_insts, List.map_map,
    Function.comp_def, srcL, rawX]
  congr 1
  · apply congrArg
    apply List.map_congr_left
    intro b _
    exact phi_sum_comm _ _ _
  · apply congrArg
    apply List.map_congr_left
    intro k _
    exact phi_sum_comm _ _ _

/-- The coordinate-split entries have matrices below `8`. -/
theorem instEntsX_o (Q : Program) (lay : Lay) (i : Inst) : ∀ e ∈ instEntsX Q lay i, e.o < 8 := by
  intro e he
  simp only [instEntsX] at he
  split at he
  · simp only [List.mem_append] at he
    rcases he with ((((((he | he) | he) | he) | he) | he) | he) | he <;> (have := (lh_mem_tagE he).1; omega)
  · simp only [List.mem_append] at he
    rcases he with ((he | he) | he) | he <;> (have := (lh_mem_tagE he).1; omega)
  · exact absurd he List.not_mem_nil
  · have := (lh_instEnts_mem Q lay i he).1; omega


theorem auxRowEnts_o' {Q : Program} {lay : Lay} (hlay : lay.Ok Q) (k r j : ℕ) :
    ∀ e ∈ auxRowEnts lay k r j, e.o < 4 := by
  intro e he
  unfold auxRowEnts at he
  simp only [List.mem_flatMap] at he
  obtain ⟨op, hop, he⟩ := he
  rw [(lh_mem_tagE he).1]
  by_cases hk : k < lay.aux.length
  · by_cases hr : r < (lay.aux.getD k default).rows.length
    · exact ((lh_aux hlay hk).1 _ (lh_getD_mem _ hr) op hop).1
    · rw [K.fl_getD_ge _ _ _ (by omega)] at hop; exact absurd hop List.not_mem_nil
  · rw [K.fl_getD_ge lay.aux _ _ (by omega)] at hop; exact absurd hop List.not_mem_nil

theorem phiX_split_rows (Q : Program) (lay : Lay) (hlay : lay.Ok Q) (a b c : FE) (rest : List FE) (src : TSrc)
    (jf : ℕ) :
    ((rawX Q lay src jf).map fun e ↦ e.c * eqW (a :: b :: c :: rest) e.idxX).sum =
      (1 + c) * ((srcEntsX Q lay false src jf).map fun e ↦ e.c * eqW (a :: b :: rest) e.idx).sum +
        c * ((srcEntsX Q lay true src jf).map fun e ↦ e.c * eqW (a :: b :: rest) e.idx).sum := by
  cases src with
  | row b' t => exact phiX_split _ (instEntsX_o Q lay _) a b c rest
  | aux k r =>
    have ho := auxRowEnts_o' hlay k r jf
    rw [show rawX Q lay (.aux k r) jf = auxRowEnts lay k r jf from rfl,
      phiX_split _ (fun e he ↦ by have := ho e he; omega) a b c rest]
    have h0 : ((auxRowEnts lay k r jf).filter fun e ↦ (e.o / 4 == 1) == false).map
        (fun e ↦ { e with o := e.o % 4 }) = auxRowEnts lay k r jf := by
      rw [List.filter_eq_self.mpr fun e he ↦ by
        have := ho e he; simp [show e.o / 4 = 0 by omega]]
      conv_rhs => rw [← List.map_id (auxRowEnts lay k r jf)]
      exact List.map_congr_left fun e he ↦ by
        have := ho e he; rw [Nat.mod_eq_of_lt this]; rfl
    have h1 : (auxRowEnts lay k r jf).filter (fun e ↦ (e.o / 4 == 1) == true) = [] :=
      List.filter_eq_nil_iff.mpr fun e he ↦ by have := ho e he; simp [show e.o / 4 = 0 by omega]
    simp only [srcEntsX, h0, h1, if_true, if_false, Bool.false_eq_true, List.map_nil]

theorem phiX_termSum_eq (Q : Program) (lay : Lay) (s : Bool) (t : CTerm) (pt : List FE)
    (hl : t.l = srcL Q lay t.src)
    (hg : ∀ jf < 2 ^ t.l, (srcEntsX Q lay s t.src jf).toArray.getD t.idx default = t.at jf) :
    K.termSum t pt = ((List.range (2 ^ srcL Q lay t.src)).map fun jf =>
      ((srcEntsX Q lay s t.src jf).getD t.idx default).c *
        eqW pt ((srcEntsX Q lay s t.src jf).getD t.idx default).idx).sum := by
  rw [phi_termSum, ← hl]
  congr 1
  apply List.map_congr_left
  intro jf hjf
  have hw : t.wAt jf = (t.at jf).c := rfl
  rw [K.termAt, hw, ← hg jf (List.mem_range.1 hjf), Array.getD_eq_getD_getElem?, List.getElem?_toArray,
    List.getD_eq_getElem?_getD]

theorem phiX_sum_keys (Q : Program) (lay : Lay) (s : Bool) (ts : List CTerm) (F : TSrc → ℕ → FE)
    (hkeys : ts.map (fun t => (t.src, t.idx)) = termKeysX Q lay s) :
    (ts.map fun t => F t.src t.idx).sum =
      ((rowsOf Q lay).map fun src => ((List.range (srcEntsX Q lay s src 0).length).map (F src)).sum).sum := by
  have : (ts.map fun t => F t.src t.idx) = (ts.map fun t => (t.src, t.idx)).map fun p => F p.1 p.2 := by
    rw [List.map_map]; rfl
  rw [this, hkeys, termKeysX, phi_sum_flatMap]
  simp only [List.map_map, Function.comp_def]

/-- A filtered tagged list's length. -/
theorem lhx_len_tag (s : Bool) (o x : ℕ) (l : List (ℕ × FE)) :
    ((tagE o x l).filter fun e ↦ (e.o / 4 == 1) == s).length = if (o / 4 == 1) == s then l.length else 0 := by
  induction l with
  | nil => simp [tagE]
  | cons p l ih =>
    simp only [tagE, List.map_cons, List.filter_cons] at ih ⊢
    by_cases h : ((o / 4 == 1) == s) = true <;> simp [h, ih]

theorem lhx_instEntsX_ne' (Q : Program) (lay : Lay) (i : Inst) (he2 : ∀ f h, i.row.op ≠ .e2 f h) :
    instEntsX Q lay i = instEnts Q lay i := by
  simp only [instEntsX]
  split
  · rename_i hop; exact absurd hop (he2 _ _)
  · rename_i hop; exact absurd hop (he2 _ _)
  · rename_i hop; exact absurd hop (he2 _ _)
  · rfl

/-- **A row's coordinate entry count does not depend on the iteration.** -/
theorem lhx_len (Q : Program) (lay : Lay) (s : Bool) (src : TSrc) (jf : ℕ) :
    (srcEntsX Q lay s src jf).length = (srcEntsX Q lay s src 0).length := by
  cases src with
  | aux k r =>
    cases s
    · simp only [srcEntsX, Bool.false_eq_true, if_false]
      exact (entCount_eq Q lay (.aux k r) jf).trans (entCount_eq Q lay (.aux k r) 0).symm
    · simp [srcEntsX]
  | row b t =>
    simp only [srcEntsX, List.length_map]
    have hrow : ∀ j, (Q.inst b j t).row = (Q.blk b).tpl.getD t default := fun _ ↦ rfl
    by_cases he : ∃ f hh, ((Q.blk b).tpl.getD t default).op = .e2 f hh
    · obtain ⟨f, hh, hop⟩ := he
      have hop' : ∀ j, (Q.inst b j t).row.op = .e2 f hh := fun j ↦ hop
      cases hh <;> cases f <;>
        simp only [instEntsX, hop', hrow, hop, List.filter_append, List.length_append, lhx_len_tag, Lay.argEnts,
          Lay.resEnts, fl_cellEnts_length, List.filter_nil, List.length_nil, hrow]
    · have he2 : ∀ j, ∀ f hh, (Q.inst b j t).row.op ≠ .e2 f hh := fun j f hh h' ↦ he ⟨f, hh, h'⟩
      have hlo : ∀ j, ∀ e ∈ instEnts Q lay (Q.inst b j t), e.o < 4 := fun j e he ↦ (lh_instEnts_mem Q lay _ he).1
      rw [lhx_instEntsX_ne' Q lay _ (he2 jf), lhx_instEntsX_ne' Q lay _ (he2 0)]
      cases s
      · rw [List.filter_eq_self.mpr fun e he ↦ by have := hlo jf e he; simp [show e.o / 4 = 0 by omega],
          List.filter_eq_self.mpr fun e he ↦ by have := hlo 0 e he; simp [show e.o / 4 = 0 by omega]]
        exact (entCount_eq Q lay (.row b t) jf).trans (entCount_eq Q lay (.row b t) 0).symm
      · rw [List.filter_eq_nil_iff.mpr fun e he ↦ by have := hlo jf e he; simp [show e.o / 4 = 0 by omega],
          List.filter_eq_nil_iff.mpr fun e he ↦ by have := hlo 0 e he; simp [show e.o / 4 = 0 by omega]]

theorem phiX_row_swap (Q : Program) (lay : Lay) (s : Bool) (pt : List FE) (src : TSrc) :
    ((List.range (srcEntsX Q lay s src 0).length).map fun i => ((List.range (2 ^ srcL Q lay src)).map fun jf =>
      ((srcEntsX Q lay s src jf).getD i default).c * eqW pt ((srcEntsX Q lay s src jf).getD i default).idx).sum).sum =
    ((List.range (2 ^ srcL Q lay src)).map fun jf =>
      ((srcEntsX Q lay s src jf).map fun e => e.c * eqW pt e.idx).sum).sum := by
  rw [phi_sum_comm (srcEntsX Q lay s src 0).length (2 ^ srcL Q lay src) fun i jf =>
      ((srcEntsX Q lay s src jf).getD i default).c * eqW pt ((srcEntsX Q lay s src jf).getD i default).idx]
  apply congrArg
  apply List.map_congr_left
  intro jf _
  rw [← lhx_len Q lay s src jf]
  exact phi_sum_getD (srcEntsX Q lay s src jf) fun e => e.c * eqW pt e.idx

/-- **One coordinate's fast evaluator** is its entries' sparse sum. -/
theorem phiX_coord (Q : Program) (lay : Lay) (s : Bool)
    (hc : PhiCache.okBX Q lay s ⟨(deriveTermsX Q lay s).toList, K.compileT (deriveTermsX Q lay s)⟩ = true)
    (pt : List FE) (hpt : pt.length = phiVars) :
    PhiQC ⟨(deriveTermsX Q lay s).toList, K.compileT (deriveTermsX Q lay s)⟩ pt =
      ((rowsOf Q lay).map fun src => ((List.range (2 ^ srcL Q lay src)).map fun jf =>
        ((srcEntsX Q lay s src jf).map fun e => e.c * eqW pt e.idx).sum).sum).sum := by
  set ts := deriveTermsX Q lay s
  unfold PhiCache.okBX at hc
  simp only [Bool.and_eq_true, beq_iff_eq, List.all_eq_true, Array.toArray_toList] at hc
  obtain ⟨⟨hkeys, hall⟩, hchk⟩ := hc
  have hl : ∀ t ∈ ts.toList, t.l = srcL Q lay t.src := fun t ht ↦ (hall t ht).1
  have hwf : ∀ t ∈ ts, K.TermWF t := fun t ht ↦ phi_termWF t (hall t (Array.mem_toList_iff.2 ht)).2
  have hg := phi_checkTermsG (srcEntsX Q lay s) ts
    (fun k k' hk hk' hs ↦ by rw [hl _ (phi_getD_mem _ k hk), hl _ (phi_getD_mem _ k' hk'), hs]) hchk
  show K.evalC (K.compileT ts) pt = _
  rw [K.compileT_eq ts hwf pt hpt]
  rw [List.map_congr_left fun t ht ↦ phiX_termSum_eq Q lay s t pt (hl t ht) (by
    obtain ⟨k, hk, rfl⟩ := phi_mem_getD _ t ht
    exact hg k hk)]
  rw [phiX_sum_keys Q lay s _ (fun src i ↦ ((List.range (2 ^ srcL Q lay src)).map fun jf ↦
      ((srcEntsX Q lay s src jf).getD i default).c * eqW pt ((srcEntsX Q lay s src jf).getD i default).idx).sum)
    hkeys]
  simp only [phiX_row_swap]


/-- **Statement 13: the fast evaluator is `Φ_Q` with the third selector bit** (E2AC-DES §6): on a checked layout
and a checked cache, at every point of `phiVarsX` coordinates. Owner **E2F-Q**. -/
theorem PhiQCX_eq (Q : Program) (lay : Lay) (hlay : lay.Ok Q) (hc : (cacheWX Q lay).okB Q lay = true)
    (pt : List FE) (hpt : pt.length = phiVarsX) :
    PhiQCX (cacheWX Q lay) pt = PhiQFX Q lay pt := by
  obtain ⟨a, b, c, rest, rfl⟩ : ∃ a b c rest, pt = a :: b :: c :: rest := by
    match pt, hpt with
    | a :: b :: c :: rest, _ => exact ⟨a, b, c, rest, rfl⟩
  have hrest : (a :: b :: rest).length = phiVars := by
    simp only [List.length_cons, phiVarsX, phiVars] at hpt ⊢; omega
  have hc0 := (Bool.and_eq_true _ _).mp hc
  unfold PhiQCX
  simp only [List.getD_cons_succ, List.getD_cons_zero, List.take_succ_cons, List.take_zero, List.drop_succ_cons,
    List.drop_zero, List.cons_append, List.nil_append]
  rw [show (cacheWX Q lay).c0 = ⟨(deriveTermsX Q lay false).toList, K.compileT (deriveTermsX Q lay false)⟩ from rfl,
    show (cacheWX Q lay).c1 = ⟨(deriveTermsX Q lay true).toList, K.compileT (deriveTermsX Q lay true)⟩ from rfl,
    phiX_coord Q lay false hc0.1 _ hrest, phiX_coord Q lay true hc0.2 _ hrest, phiX_rows]
  simp only [phiX_split_rows Q lay hlay a b c rest, phiX_sum_add, ← phiX_sum_mul]

end Lvm.Typed
