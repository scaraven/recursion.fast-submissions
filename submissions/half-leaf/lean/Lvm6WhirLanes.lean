-- New for lvm6 (WP W1). The deployed reading of a level's commitment (FORMAT6 v2.2.1 §5 "Lanes",
-- "Level-0 leaf", "Level i ≥ 1 leaf"): the word of commitment `i` as lanes (level 0: the `K` word
-- `63 − s` of the verifier's 64-word row for slot `s`; levels `≥ 1`: lane `u` is the `E2` value of
-- words `2u, 2u+1`), the fold of an opened row by the rounds (`foldRowE`, the pointwise
-- `foldsQ`), and the verifier's values `valsE`/`fvE` with the read facts the ladder asks for
-- (`MidOK.hread`, `MidOK.hstab`, `FinOK.hread`). After leanVM `Whir/Sound/State.lean`
-- (`lanesOf`, `laneO`, `foldRow_eq`) @ fdb317982.
import Lvm6WhirCode

/-!
# Lanes of a commitment (W1)

* `laneVal z row s`: lane `s` of an opened row (`z = true` at level 0).
* `wordE z i cs`: **the word of commitment `i`** of the commitments `cs`, on `m` lane variables
  (lane index `bitsToNat u`, low bit first), position `p` read at `p mod 2^ht`.
* `foldRowE x j rs L`: the lanes `L` folded by `j` rounds at the point `x`; `foldsQ_eq_foldRowE`.
* `valsE`, `fvE`: the folded row at each queried position (minus the high part at a mid level);
  `hread_valsE`, `hread_fvE`, `wordE_append`.
-/

namespace Lvm6.Whir

open LeanVM.Parameters LeanVM.Protocol.Compile LeanVM.Protocol.Whir.Sound
  LeanVM.Protocol.Whir Finset

/-- **Lane `s` of an opened row**: level 0 reads `K` word `63 − s`, later levels the `E2` value of
words `2s, 2s + 1` (low limb first). -/
noncomputable def laneVal (z : Bool) (row : List K) (s : ℕ) : E2 :=
  if z then algebraMap K E2 (row.getD (63 - s) 0) else ⟨row.getD (2 * s) 0, row.getD (2 * s + 1) 0⟩

/-- **The word of commitment `i`**, on `m` lane variables, `2^h` positions. -/
noncomputable def wordE (z : Bool) (i m h : ℕ) (cs : List (ℕ × ℕ × Word)) : Wd E2 (2 ^ h) m :=
  fun u p ↦ match cs[i]? with
    | some c => laneVal z (c.2.2 ((p : ℕ) % 2 ^ c.1)) (bitsToNat u)
    | none => 0

theorem wordE_append (z : Bool) (i m h : ℕ) (cs : List (ℕ × ℕ × Word)) (c : ℕ × ℕ × Word)
    (hl : cs.length = i + 1) : wordE z i m h (cs ++ [c]) = wordE z i m h cs := by
  funext u p
  simp only [wordE, List.getElem?_append_left (by omega : i < cs.length)]

/-- **The lanes folded by `j` rounds** at the point `x`. -/
def foldRowE {m : ℕ} (x : E2) : (j : ℕ) → List (Rnd E2) → ((Fin (m + j) → Bool) → E2) →
    ((Fin m → Bool) → E2)
  | 0, _, L => L
  | j + 1, rs, L => foldRowE x j rs.tail fun u ↦
      L (Fin.cons true u) + ((rs.headD default).α + (rs.headD default).β * x) * L (Fin.cons false u)

theorem foldsQ_eq_foldRowE {n m : ℕ} (dom : Fin n ↪ E2) :
    ∀ (j : ℕ) (rs : List (Rnd E2)) (Q : Wd E2 n (m + j)) (u : Fin m → Bool) (x : Fin n),
      foldsQ dom j rs Q u x = foldRowE (dom x) j rs (fun v ↦ Q v x) u
  | 0, _, _, _, _ => rfl
  | j + 1, rs, Q, u, x => foldsQ_eq_foldRowE dom j rs.tail _ u x

/-- The row of position `k` among the opened rows. -/
def rowAt {t : ℕ} (rows : List (List K)) (k : Fin t) : List K := rows.getD k []

/-- **The verifier's values at a mid level**: each opened row folded by the rounds, minus the high
part at its point. -/
noncomputable def valsE (z : Bool) (h ℓ κ : ℕ) (hh : h ≤ 64) {t : ℕ} (rs : List (Rnd E2))
    (hi : List E2) (ps : Fin t → Fin (2 ^ h)) (rows : List (List K)) (k : Fin t) : E2 :=
  foldRowE (domE h hh (ps k)) ℓ rs (fun v : Fin (0 + ℓ) → Bool ↦
      laneVal z (rowAt rows k) (bitsToNat v)) lane0 - (highF κ ℓ hi).eval (domE h hh (ps k))

/-- **The verifier's values at the final level**: each opened row folded by the rounds. -/
noncomputable def fvE (z : Bool) (h ℓ : ℕ) (hh : h ≤ 64) {t : ℕ} (rs : List (Rnd E2))
    (ps : Fin t → Fin (2 ^ h)) (rows : List (List K)) (k : Fin t) : E2 :=
  foldRowE (domE h hh (ps k)) ℓ rs (fun v : Fin (0 + ℓ) → Bool ↦
      laneVal z (rowAt rows k) (bitsToNat v)) lane0

/-- The opened rows are the committed rows at the positions. -/
theorem rowAt_of_answer {h₀ : List Ev} {i h t : ℕ} {ps : Fin t → Fin (2 ^ h)}
    {rows : List (List K)} (hans : answer h₀ i (List.ofFn fun k ↦ (ps k : ℕ)) = some rows)
    (k : Fin t) : ∃ c, (commits h₀)[i]? = some c ∧ rowAt rows k = c.2.2 ((ps k : ℕ) % 2 ^ c.1) := by
  unfold answer at hans
  cases hc : (commits h₀)[i]? with
  | none => rw [hc] at hans; exact absurd hans (by simp)
  | some c =>
    rw [hc] at hans
    simp only [Option.map_some, Option.some.injEq] at hans
    refine ⟨c, rfl, ?_⟩
    rw [rowAt, ← hans]
    simp

/-- **`MidOK.hread`** for the deployed values. -/
theorem hread_valsE (z : Bool) (i h ℓ κ : ℕ) (hh : h ≤ 64) {t : ℕ} (rs : List (Rnd E2))
    (h₀ : List Ev) (ps : Fin t → Fin (2 ^ h)) (rows : List (List K))
    (hans : answer h₀ i (List.ofFn fun k ↦ (ps k : ℕ)) = some rows) (hi : List E2) :
    valsE z h ℓ κ hh rs hi ps rows = fun k ↦
      foldsQ (domE h hh) ℓ rs (wordE z i (0 + ℓ) h (commits h₀)) lane0 (ps k) -
        (highF κ ℓ hi).eval (domE h hh (ps k)) := by
  funext k
  obtain ⟨c, hc, hrow⟩ := rowAt_of_answer hans k
  rw [valsE, foldsQ_eq_foldRowE, hrow]
  congr 2
  funext v
  simp only [wordE, hc]

/-- **`FinOK.hread`** for the deployed values. -/
theorem hread_fvE (z : Bool) (i h ℓ : ℕ) (hh : h ≤ 64) {t : ℕ} (rs : List (Rnd E2))
    (h₀ : List Ev) (ps : Fin t → Fin (2 ^ h)) (rows : List (List K))
    (hans : answer h₀ i (List.ofFn fun k ↦ (ps k : ℕ)) = some rows) :
    fvE z h ℓ hh rs ps rows = fun k ↦
      foldsQ (domE h hh) ℓ rs (wordE z i (0 + ℓ) h (commits h₀)) lane0 (ps k) := by
  funext k
  obtain ⟨c, hc, hrow⟩ := rowAt_of_answer hans k
  rw [fvE, foldsQ_eq_foldRowE, hrow]
  congr 1
  funext v
  simp only [wordE, hc]

end Lvm6.Whir
