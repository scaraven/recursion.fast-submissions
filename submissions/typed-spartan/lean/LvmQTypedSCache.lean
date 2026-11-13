-- New for lvm2 (roll 8 = B1, B1-IX-S): the typed V_S's start-up. `Φ_Q`'s entries tabulated once (`EntTab`), read
-- by the class derivation and by the class check: one enumeration instead of two.
import LvmQTypedSWire

/-!
# One table of the entries

`EntTab.of G`: every row's entries at every iteration (`FLF`'s), as arrays: `rows[b][t][jf]`, `aux[k][r][j]`.
`EntTab.get`: a lookup, else the entries (`EntTab.get_of`: it *is* the entry function, at every row and
iteration). The derivation (`deriveTermsG`) and the check (`checkTermsGA`) both read it.
-/

set_option autoImplicit false

namespace Lvm.Typed.K

open Lvm.Loop

/-- A function of three indices tabulated on `i < n`, `j < m i`, `l < k i j`. -/
def tab3 {α : Type} (n : ℕ) (m : ℕ → ℕ) (k : ℕ → ℕ → ℕ) (f : ℕ → ℕ → ℕ → α) : Array (Array (Array α)) :=
  (Array.range n).map fun i ↦ (Array.range (m i)).map fun j ↦ (Array.range (k i j)).map fun l ↦ f i j l

/-- A lookup in a three-index table, else `d ()`. -/
def look3 {α : Type} (A : Array (Array (Array α))) (i j l : ℕ) (d : Unit → α) : α :=
  match (A[i]?.bind (·[j]?)).bind (·[l]?) with
  | some x => x
  | none => d ()

theorem look3_tab3 {α : Type} (n : ℕ) (m : ℕ → ℕ) (k : ℕ → ℕ → ℕ) (f : ℕ → ℕ → ℕ → α) (i j l : ℕ) :
    look3 (tab3 n m k f) i j l (fun _ ↦ f i j l) = f i j l := by
  unfold look3 tab3
  by_cases hi : i < n
  · by_cases hj : j < m i
    · by_cases hl : l < k i j
      · simp [hi, hj, hl]
      · simp [hi, hj, hl]
    · simp [hi, hj]
  · simp [hi]

/-- **Every row's entries at every iteration**, as arrays. -/
structure EntTab where
  /-- `rows[b][t][jf]`: template row `t` of block `b`. -/
  rows : Array (Array (Array (Array Ent)))
  /-- `aux[k][r][j]`: row `r` of auxiliary block `k`. -/
  aux : Array (Array (Array (Array Ent)))

/-- **The table of `FLF`'s entries.** -/
def EntTab.of (G : FLF) : EntTab :=
  ⟨tab3 G.F.qb.size (fun b ↦ (G.F.tpls.getD b #[]).size) (fun b t ↦ 2 ^ G.F.srcL (.row b t))
      (fun b t jf ↦ (G.srcEnts (.row b t) jf).toArray),
    tab3 G.F.lay.aux.length (fun k ↦ (G.F.lay.aux.getD k default).rows.length) (fun k r ↦ 2 ^ G.F.srcL (.aux k r))
      (fun k r j ↦ (G.srcEnts (.aux k r) j).toArray)⟩

/-- A row's entries at an iteration, from the table (else computed). -/
def EntTab.get (E : EntTab) (G : FLF) : TSrc → ℕ → Array Ent
  | .row b t, jf => look3 E.rows b t jf fun _ ↦ (G.srcEnts (.row b t) jf).toArray
  | .aux k r, j => look3 E.aux k r j fun _ ↦ (G.srcEnts (.aux k r) j).toArray

/-- **The table's lookup is the entry function.** -/
theorem EntTab.get_of (G : FLF) : (EntTab.of G).get G = fun s jf ↦ (G.srcEnts s jf).toArray := by
  funext s jf
  cases s with
  | row b t => exact look3_tab3 _ _ _ (fun b t jf ↦ (G.srcEnts (.row b t) jf).toArray) b t jf
  | aux k r => exact look3_tab3 _ _ _ (fun k r j ↦ (G.srcEnts (.aux k r) j).toArray) k r jf

/-- **The terms and their check on one table** (`G = FLF.ofLay Q lay`): `(terms, check)`. -/
def termsChecked (G : FLF) : Array CTerm × Bool :=
  let ea := (EntTab.of G).get G
  let ts := deriveTermsG ea G.F
  (ts, checkTermsGA ea CTerm.atF ts)

theorem termsChecked_fst (Q : Program) (lay : Lay) : (termsChecked (FLF.ofLay Q lay)).1 = deriveTerms Q lay := by
  show deriveTermsG ((EntTab.of (FLF.ofLay Q lay)).get (FLF.ofLay Q lay)) (FLF.ofLay Q lay).F = _
  rw [EntTab.get_of]
  rfl

/-- The check on the table is `checkTerms`. -/
theorem checkTab_eq (Q : Program) (lay : Lay) (ts : Array CTerm) :
    checkTermsGA ((EntTab.of (FLF.ofLay Q lay)).get (FLF.ofLay Q lay)) CTerm.atF ts = checkTerms Q lay ts := by
  rw [EntTab.get_of, cterm_atF, flf_srcEnts, checkTerms_eqG, checkTermsG_eqA]

theorem termsChecked_snd (Q : Program) (lay : Lay) :
    (termsChecked (FLF.ofLay Q lay)).2 = checkTerms Q lay (termsChecked (FLF.ofLay Q lay)).1 :=
  checkTab_eq Q lay _

end Lvm.Typed.K
