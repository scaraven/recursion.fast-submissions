-- New for lvm6 (WP MBS). Small mini-bus gadgets: a top-down trie of `eq` weights of aligned blocks (`eqHiG`), a
-- sparse `eq` sum (`sparseG`), and claims 50–52's gadget `mbClaimFG` (one `eq` product per log-height `τ`, one
-- sparse sum over the parts' blocks per `τ`) with its `ClaimAt` (`mbClaimF_ok`, the claim of `mbClaim_ok`).
import Lvm6QCFinM

/-!
# Small mini-bus gadgets (WP MBS)

* **`eqHiG z one ys os Q`**: for each `(κ, q)` of `Q`, the cell `eq(ys_{≥κ}, q)` (`hs_eqHiG`). The trie of `Q`
  from the top coordinate down: a node `(m, p)` holds `eq(ys_{≥m}, p)`, a child one product
  (`(1 + y_m)·acc` or `y_m·acc`); only the nodes on a path to a request are built (`hiNodes`).
* **`sparseG z ys os m R`**: `Σ_{(a, w) ∈ R} a·eq(ys_{<m}, w)` (`hs_sparseG`), top coordinate first, on the split
  `eq(ys_{<m+1}, w) = eq(ys_{<m}, w)·(bit_m w ? y_m : 1 + y_m)`: two children `S₀ + y·(S₀ + S₁)` (two rows), one
  child one product.
* **`mbClaimFG ν qs`** (claims 50–52): the parts grouped by `τ` (`groupsG`), per group
  `eq(z_τ, x_{<τ})·Σ_p c_p·eq(x_{≥τ}, off_p/2^τ)`. **`mbClaimF_ok`**: `ClaimAt Pre ((sumClaimG ν parts v).onStack)`
  when the parts' points depend only on `τ` (`p.2.2 = ζ.take τ`, which `mbPartsG` satisfies: `mbPartsG_pt`).

`os` are the cells `1 + y` (`OnesOk`, `onesG`). Everything is generic over the requests and the parts.
-/

set_option autoImplicit false

namespace Lvm6.Node.MbS

open LeanVM.Parameters LeanVM.Protocol.Compile LeanVM.Protocol.Verifier
open Lvm Lvm.Loop Lvm.Loop.Build Lvm.Q2 Lvm.Har Lvm.E2V Lvm6.QK Lvm6.QC

variable {c : Ctx} {M : Mem}

/-- A block of the stack (`Placement`). -/
abbrev Pl : Type := LeanVM.Protocol.Verifier.Placement

/-! ## The cells `1 + y` -/

/-- `1 + y` per coordinate. -/
def onesG (ys : List C2) : BM (List C2) := mapB g2One ys

/-- The cells `os` are `1 + y` of `ys` (`z` the `getD` default). -/
def OnesOk (M : Mem) (z : C2) (ys os : List C2) : Prop :=
  ∀ i < ys.length, ev2 M (os.getD i z) = 1 + ev2 M (ys.getD i z)

theorem ev2_getD {l : List C2} {i : ℕ} (h : i < l.length) (z : C2) :
    ev2 M (l.getD i z) = (l.map (ev2 M))[i]'(by simpa using h) := by
  rw [List.getD_eq_getElem _ _ h, List.getElem_map]

theorem hs_onesG (ys : List C2) (z : C2) : Hs c M (onesG ys) fun os ↦ OnesOk M z ys os := by
  refine hs_mono (hs_mapB2 g2One (fun y ↦ 1 + ev2 M y) (ev2 M) (fun y ↦ hs_mono (hs_g2One y) fun r hr ↦ by
    simp [ev2, hr]) ys) fun os hos i hi ↦ ?_
  have hl : os.length = ys.length := by simpa using congrArg List.length hos
  rw [ev2_getD (hl ▸ hi), ev2_getD hi, List.getElem_of_eq hos]
  simp

theorem OnesOk.take {z : C2} {ys os : List C2} (h : OnesOk M z ys os) (n : ℕ) :
    OnesOk M z (ys.take n) (os.take n) := fun i hi ↦ by
  have hi' : i < n ∧ i < ys.length := by simpa using hi
  have := h i hi'.2
  simpa [List.getD_eq_getElem?_getD, List.getElem?_take, hi'.1] using this

theorem OnesOk.drop {z : C2} {ys os : List C2} (h : OnesOk M z ys os) (n : ℕ) :
    OnesOk M z (ys.drop n) (os.drop n) := fun i hi ↦ by
  have := h (n + i) (by simp at hi; omega)
  simpa [List.getD_eq_getElem?_getD, List.getElem?_drop] using this

/-! ## Sums of lists split by a predicate -/

theorem sum_filter_split {α : Type} (p : α → Bool) (f : α → E2) : ∀ R : List α,
    (R.map f).sum = ((R.filter p).map f).sum + ((R.filter fun a ↦ !p a).map f).sum
  | [] => by simp
  | a :: R => by
    rw [List.map_cons, List.sum_cons, sum_filter_split p f R]
    cases h : p a <;> simp [List.filter_cons, h] <;> ring

theorem sum_map_eq_mul {α : Type} (f g : α → E2) (k : E2) :
    ∀ L : List α, (∀ a ∈ L, f a = k * g a) → (L.map f).sum = k * (L.map g).sum
  | [], _ => by simp
  | a :: L, h => by
    rw [List.map_cons, List.sum_cons, h a List.mem_cons_self,
      sum_map_eq_mul f g k L fun b hb ↦ h b (List.mem_cons_of_mem _ hb), List.map_cons, List.sum_cons]
    ring

/-! ## The sparse `eq` sum -/

/-- Bit `m` of `w`. -/
def bitB (m w : ℕ) : Bool := (w / 2 ^ m) % 2 == 1

/-- The top coordinate of `ys_{<m+1}` split off. -/
theorem eqAtF_take_succ (Y : List E2) {m : ℕ} (hm : m < Y.length) (w : ℕ) :
    eqAtF (Y.take (m + 1)) w = eqAtF (Y.take m) w * (if bitB m w then Y[m] else 1 + Y[m]) := by
  rw [List.take_succ, List.getElem?_eq_getElem hm, Option.toList_some, eqAtF_append,
    List.length_take, min_eq_left hm.le]
  simp only [eqAtF_succ, eqAtF_nil, mul_one, bitB, beq_iff_eq]

/-- `acc + Σ l`. -/
def addAll : C2 → List C2 → BM C2
  | acc, [] => pure acc
  | acc, x :: xs => g2Add acc x >>= fun a ↦ addAll a xs

theorem hs_addAll : ∀ (l : List C2) (acc : C2),
    Hs c M (addAll acc l) fun r ↦ ev2 M r = ev2 M acc + (l.map (ev2 M)).sum
  | [], acc => hs_pure (by simp)
  | x :: xs, acc => hs_bind (hs_g2Add acc x) fun a ha ↦ hs_mono (hs_addAll xs a) fun r hr ↦ by
      rw [hr, ev2_add ha, List.map_cons, List.sum_cons, add_assoc]

/-- **A sparse `eq` sum** `Σ_{(a, w) ∈ R} a·eq(ys_{<m}, w)`, top coordinate first (`os` the cells `1 + y`). -/
def sparseG (z : C2) (ys os : List C2) : ℕ → List (C2 × ℕ) → BM C2
  | 0, [] => pure z
  | 0, r :: R => addAll r.1 (R.map (·.1))
  | m + 1, R =>
    let R1 := R.filter fun r ↦ bitB m r.2
    let R0 := R.filter fun r ↦ !bitB m r.2
    if R.isEmpty then pure z
    else if R1.isEmpty then sparseG z ys os m R0 >>= fun s ↦ g2Mul (os.getD m z) s z
    else if R0.isEmpty then sparseG z ys os m R1 >>= fun s ↦ g2Mul (ys.getD m z) s z
    else sparseG z ys os m R0 >>= fun s0 ↦ sparseG z ys os m R1 >>= fun s1 ↦
      g2Add s0 s1 >>= fun t ↦ g2Mul (ys.getD m z) t s0

/-- The value of a request list at `ys_{<m}`. -/
def sparseV (M : Mem) (Y : List E2) (m : ℕ) (R : List (C2 × ℕ)) : E2 :=
  (R.map fun r ↦ ev2 M r.1 * eqAtF (Y.take m) r.2).sum

theorem sparseV_succ (Y : List E2) {m : ℕ} (hm : m < Y.length) (R : List (C2 × ℕ)) :
    sparseV M Y (m + 1) R = (1 + Y[m]) * sparseV M Y m (R.filter fun r ↦ !bitB m r.2) +
      Y[m] * sparseV M Y m (R.filter fun r ↦ bitB m r.2) := by
  unfold sparseV
  rw [sum_filter_split (fun r : C2 × ℕ ↦ !bitB m r.2)]
  simp only [Bool.not_not]
  congr 1
  · refine sum_map_eq_mul _ _ (1 + Y[m]) _ fun r hr ↦ ?_
    have hb : bitB m r.2 = false := by simpa using (List.mem_filter.mp hr).2
    rw [eqAtF_take_succ Y hm, hb]
    simp only [Bool.false_eq_true, if_false]
    ring
  · refine sum_map_eq_mul _ _ Y[m] _ fun r hr ↦ ?_
    rw [eqAtF_take_succ Y hm, (List.mem_filter.mp hr).2]
    simp only [if_true]
    ring

theorem sparseV_nil (Y : List E2) (m : ℕ) : sparseV M Y m [] = 0 := by simp [sparseV]

theorem hs_sparseG {z : C2} (hz : z.val M = 0) {ys os : List C2} (hos : OnesOk M z ys os) :
    ∀ m, m ≤ ys.length → ∀ R : List (C2 × ℕ),
      Hs c M (sparseG z ys os m R) fun s ↦ ev2 M s = sparseV M (ys.map (ev2 M)) m R
  | 0, _, [] => hs_pure (by rw [ev2_of_zero hz, sparseV_nil])
  | 0, _, r :: R => hs_mono (hs_addAll _ _) fun s hs ↦ by
      rw [hs]
      simp [sparseV, Function.comp_def]
  | m + 1, hm, R => by
    have hm' : m < (ys.map (ev2 M)).length := by simp; omega
    have hy : ev2 M (ys.getD m z) = (ys.map (ev2 M))[m] := ev2_getD (by omega) z
    have ho : ev2 M (os.getD m z) = 1 + (ys.map (ev2 M))[m] := by rw [hos m (by omega), hy]
    have IH := hs_sparseG hz hos m (by omega)
    simp only [sparseG]
    split_ifs with h0 h1 h2
    · rw [List.isEmpty_iff.mp h0]
      exact hs_pure (by rw [ev2_of_zero hz, sparseV_nil])
    · refine hs_bind (IH _) fun s hs ↦ hs_mono (hs_g2Mul _ s z) fun r hr ↦ ?_
      rw [ev2_mul hr, ev2_of_zero hz, ho, hs, sparseV_succ _ hm', List.isEmpty_iff.mp h1, sparseV_nil]
      ring
    · refine hs_bind (IH _) fun s hs ↦ hs_mono (hs_g2Mul _ s z) fun r hr ↦ ?_
      rw [ev2_mul hr, ev2_of_zero hz, hy, hs, sparseV_succ _ hm', List.isEmpty_iff.mp h2, sparseV_nil]
      ring
    · refine hs_bind (IH _) fun s0 hs0 ↦ hs_bind (IH _) fun s1 hs1 ↦ hs_bind (hs_g2Add s0 s1) fun t ht ↦
        hs_mono (hs_g2Mul _ t s0) fun r hr ↦ ?_
      rw [ev2_mul hr, ev2_add ht, hy, hs0, hs1, sparseV_succ _ hm']
      ring

/-! ## The trie of block weights -/

/-- **The trie of the requests `Q`** (`(κ, q)`: `eq(ys_{≥κ}, q)`) below node `(m, p)`, `acc` its cell
(`eq(ys_{≥m}, p)`): the node, then the children on a path to a request, one product each. -/
def hiNodes (z : C2) (ys os : List C2) : ℕ → ℕ → C2 → List (ℕ × ℕ) → BM (List ((ℕ × ℕ) × C2))
  | 0, p, acc, _ => pure [((0, p), acc)]
  | m + 1, p, acc, Q =>
    let Q' := Q.filter fun q ↦ decide (q.1 ≤ m)
    let Q0 := Q'.filter fun q ↦ q.2 / 2 ^ (m - q.1) == 2 * p
    let Q1 := Q'.filter fun q ↦ q.2 / 2 ^ (m - q.1) == 2 * p + 1
    (if Q0.isEmpty then pure [] else
      g2Mul (os.getD m z) acc z >>= fun a ↦ hiNodes z ys os m (2 * p) a Q0) >>= fun L0 ↦
    (if Q1.isEmpty then pure [] else
      g2Mul (ys.getD m z) acc z >>= fun a ↦ hiNodes z ys os m (2 * p + 1) a Q1) >>= fun L1 ↦
    pure (((m + 1, p), acc) :: (L0 ++ L1))

/-- A trie entry holds its node's weight. -/
def NodeOk (M : Mem) (Y : List E2) (e : (ℕ × ℕ) × C2) : Prop := ev2 M e.2 = eqAtF (Y.drop e.1.1) e.1.2

theorem hs_hiNodes {z : C2} (hz : z.val M = 0) {ys os : List C2} (hos : OnesOk M z ys os) :
    ∀ m p (acc : C2) (Q : List (ℕ × ℕ)), m ≤ ys.length → ev2 M acc = eqAtF ((ys.map (ev2 M)).drop m) p →
      Hs c M (hiNodes z ys os m p acc Q) fun N ↦ ∀ e ∈ N, NodeOk M (ys.map (ev2 M)) e
  | 0, p, acc, Q, _, hacc => hs_pure fun e he ↦ by
      rw [List.mem_singleton] at he
      subst he
      exact hacc
  | m + 1, p, acc, Q, hm, hacc => by
    have hm' : m < (ys.map (ev2 M)).length := by simp; omega
    have hy : ev2 M (ys.getD m z) = (ys.map (ev2 M))[m] := ev2_getD (by omega) z
    have ho : ev2 M (os.getD m z) = 1 + (ys.map (ev2 M))[m] := by rw [hos m (by omega), hy]
    have hd := List.drop_eq_getElem_cons hm'
    have c0 : ∀ Q' : List (ℕ × ℕ), Hs c M (if Q'.isEmpty then pure [] else g2Mul (os.getD m z) acc z >>= fun a ↦
        hiNodes z ys os m (2 * p) a Q') fun L ↦ ∀ e ∈ L, NodeOk M (ys.map (ev2 M)) e := fun Q' ↦ by
      split_ifs
      · exact hs_pure fun e he ↦ absurd he List.not_mem_nil
      · refine hs_bind (hs_g2Mul _ acc z) fun a ha ↦ hs_hiNodes hz hos m _ a Q' (by omega) ?_
        rw [ev2_mul ha, ev2_of_zero hz, add_zero, ho, hacc, hd, eqAtF_even]
    have c1 : ∀ Q' : List (ℕ × ℕ), Hs c M (if Q'.isEmpty then pure [] else g2Mul (ys.getD m z) acc z >>= fun a ↦
        hiNodes z ys os m (2 * p + 1) a Q') fun L ↦ ∀ e ∈ L, NodeOk M (ys.map (ev2 M)) e := fun Q' ↦ by
      split_ifs
      · exact hs_pure fun e he ↦ absurd he List.not_mem_nil
      · refine hs_bind (hs_g2Mul _ acc z) fun a ha ↦ hs_hiNodes hz hos m _ a Q' (by omega) ?_
        rw [ev2_mul ha, ev2_of_zero hz, add_zero, hy, hacc, hd, eqAtF_odd]
    simp only [hiNodes]
    refine hs_bind (c0 _) fun L0 h0 ↦ hs_bind (c1 _) fun L1 h1 ↦ hs_pure ?_
    intro e he
    rcases List.mem_cons.mp he with rfl | he
    · exact hacc
    · rcases List.mem_append.mp he with he | he
      · exact h0 e he
      · exact h1 e he

/-- A request's cell: the trie's, or `eqAtG` when the trie lacks it. -/
def hiAt (z one : C2) (ys : List C2) (N : List ((ℕ × ℕ) × C2)) (q : ℕ × ℕ) : BM C2 :=
  match N.find? (fun e ↦ e.1 == q) with
  | some e => pure e.2
  | none => eqAtG z one (ys.drop q.1) q.2

/-- **`eq(ys_{≥κ}, q)` for each request `(κ, q)` of `Q`**, from the trie of `Q`. -/
def eqHiG (z one : C2) (ys os : List C2) (Q : List (ℕ × ℕ)) : BM (List C2) :=
  hiNodes z ys os ys.length 0 one Q >>= fun N ↦ mapB (hiAt z one ys N) Q

theorem hs_eqHiG {z one : C2} (hz : z.val M = 0) (hone : ev2 M one = 1) {ys os : List C2}
    (hos : OnesOk M z ys os) (Q : List (ℕ × ℕ)) :
    Hs c M (eqHiG z one ys os Q) fun W ↦ W.map (ev2 M) = Q.map fun q ↦ eqAtF ((ys.map (ev2 M)).drop q.1) q.2 := by
  refine hs_bind (hs_hiNodes hz hos _ 0 one Q le_rfl (by rw [hone, List.drop_eq_nil_of_le (by simp)]; rfl))
    fun N hN ↦ hs_mapB2 _ _ (ev2 M) (fun q ↦ ?_) Q
  unfold hiAt
  split
  · rename_i e he
    refine hs_pure ?_
    have hk : e.1 = q := by simpa using List.find?_some he
    have := hN e (List.mem_of_find?_eq_some he)
    rw [this.trans (by rw [hk])]
  · exact hs_mono (hs_eqAtG hz hone _ _) fun r hr ↦ by rw [hr, List.map_drop]

/-- The full `eq` table of `ys` (`eqKernelF`'s order), by the trie. -/
def eqTabG (z one : C2) (ys os : List C2) : BM (List C2) :=
  eqHiG z one ys os ((List.range (2 ^ ys.length)).map fun i ↦ (0, i))

theorem hs_eqTabG {z one : C2} (hz : z.val M = 0) (hone : ev2 M one = 1) {ys os : List C2}
    (hos : OnesOk M z ys os) :
    Hs c M (eqTabG z one ys os) fun T ↦ T.map (ev2 M) = (List.range (2 ^ ys.length)).map (eqAtF (ys.map (ev2 M))) :=
  hs_mono (hs_eqHiG hz hone hos _) fun T hT ↦ by simp [hT, Function.comp_def]

/-! ## Claims 50–52 -/

/-- A part's request: its coefficient cell and its block's index above the window. -/
def reqOf (q : C2 × Pl × List C2) : C2 × ℕ := (q.1, q.2.1.index / 2 ^ q.2.1.variableCount)

/-- The parts grouped by `τ` (the first part's `τ`, then the rest): per group `eq(z_τ, x_{<τ})·Σ_p c_p·eq(x_{≥τ},
off_p/2^τ)` with the first part's point `z_τ`, added to `acc`. -/
def groupsG (z one : C2) (x os : List C2) : ℕ → C2 → List (C2 × Pl × List C2) → BM C2
  | 0, acc, _ => pure acc
  | _ + 1, acc, [] => pure acc
  | n + 1, acc, q :: qs =>
    let τ := q.2.1.variableCount
    eqPtG z one q.2.2 (x.take τ) >>= fun e ↦
    sparseG z (x.drop τ) (os.drop τ) (x.length - τ)
      (((q :: qs).filter fun p ↦ p.2.1.variableCount == τ).map reqOf) >>= fun s ↦
    g2Mul e s acc >>= fun a ↦ groupsG z one x os n a ((q :: qs).filter fun p ↦ !(p.2.1.variableCount == τ))

/-- A part's term at the point `X`. -/
def termV (M : Mem) (X : List E2) (q : C2 × Pl × List C2) : E2 :=
  ev2 M q.1 * eqAtF (X.drop q.2.1.variableCount) (q.2.1.index / 2 ^ q.2.1.variableCount) *
    eqPt (q.2.2.map (ev2 M)) (X.take q.2.1.variableCount)

/-- The parts' points depend only on `τ`. -/
def PtsOk (M : Mem) (qs : List (C2 × Pl × List C2)) : Prop :=
  ∀ p ∈ qs, ∀ p' ∈ qs, p.2.1.variableCount = p'.2.1.variableCount → p.2.2.map (ev2 M) = p'.2.2.map (ev2 M)

theorem hs_groupsG {z one : C2} (hz : z.val M = 0) (hone : ev2 M one = 1) {x os : List C2}
    (hos : OnesOk M z x os) : ∀ n (acc : C2) (qs : List (C2 × Pl × List C2)), qs.length ≤ n → PtsOk M qs →
      Hs c M (groupsG z one x os n acc qs) fun r ↦ ev2 M r = ev2 M acc + (qs.map (termV M (x.map (ev2 M)))).sum
  | 0, acc, qs, hn, _ => hs_pure (by rw [List.eq_nil_of_length_eq_zero (Nat.le_zero.mp hn)]; simp)
  | _ + 1, acc, [], _, _ => hs_pure (by simp)
  | n + 1, acc, q :: qs, hn, hpt => by
    have hRs : ((q :: qs).filter fun p ↦ !(p.2.1.variableCount == q.2.1.variableCount)).length ≤ n := by
      rw [List.filter_cons_of_neg (by simp)]
      exact (List.length_filter_le _ _).trans (by simpa using hn)
    have hptR : PtsOk M ((q :: qs).filter fun p ↦ !(p.2.1.variableCount == q.2.1.variableCount)) :=
      fun p hp p' hp' ↦ hpt p (List.mem_of_mem_filter hp) p' (List.mem_of_mem_filter hp')
    have hS := hs_sparseG (c := c) hz (hos.drop q.2.1.variableCount) (x.length - q.2.1.variableCount) (by simp)
      (((q :: qs).filter fun p ↦ p.2.1.variableCount == q.2.1.variableCount).map reqOf)
    have htk : ((x.drop q.2.1.variableCount).map (ev2 M)).take (x.length - q.2.1.variableCount) =
        (x.map (ev2 M)).drop q.2.1.variableCount := by
      rw [List.take_of_length_le (by simp), List.map_drop]
    have key : (((q :: qs).filter fun p ↦ p.2.1.variableCount == q.2.1.variableCount).map
        (termV M (x.map (ev2 M)))).sum = eqPt (q.2.2.map (ev2 M)) ((x.take q.2.1.variableCount).map (ev2 M)) *
          sparseV M ((x.drop q.2.1.variableCount).map (ev2 M)) (x.length - q.2.1.variableCount)
            (((q :: qs).filter fun p ↦ p.2.1.variableCount == q.2.1.variableCount).map reqOf) := by
      rw [sparseV, htk, List.map_map]
      refine sum_map_eq_mul _ _ _ _ fun p hp ↦ ?_
      have hpτ : p.2.1.variableCount = q.2.1.variableCount := beq_iff_eq.mp (List.mem_filter.mp hp).2
      have hpp : p.2.2.map (ev2 M) = q.2.2.map (ev2 M) :=
        hpt p (List.mem_of_mem_filter hp) q List.mem_cons_self hpτ
      simp only [termV, Function.comp_def, reqOf, hpτ, hpp, List.map_take]
      ring
    refine hs_bind (hs_eqPtG hz hone _ _) fun e he ↦ hs_bind hS fun s hs ↦ hs_bind (hs_g2Mul e s acc)
      fun a ha ↦ hs_mono (hs_groupsG hz hone hos n a _ hRs hptR) fun r hr ↦ ?_
    rw [hr, ev2_mul ha, hs, he,
      sum_filter_split (fun p ↦ p.2.1.variableCount == q.2.1.variableCount) _ (q :: qs), key]
    ring

/-- The inner sum of claims 50–52 on the window's coordinates `x`. -/
def mbSumG (qs : List (C2 × Pl × List C2)) (x : List C2) (gate : Cell) : BM C2 :=
  g2Zero ⟨gate, gate⟩ >>= fun z ↦ g2Const 1 z >>= fun one ↦ onesG x >>= fun os ↦
    groupsG z one x os qs.length z qs

/-- **Claims 50–52's gadget** (`sumClaimG ν parts` on `C_main`'s window `⟨ν, 0⟩`), grouped by `τ`. -/
def mbClaimFG (nu : ℕ) (qs : List (C2 × Pl × List C2)) : List C2 → Cell → BM C2 :=
  aboveG ⟨nu, 0⟩ (mbSumG qs)

/-- **Claims 50–52** (`mbClaim_ok`'s claim): the parts' coefficients and points as cells, the points `ζ.take τ`. -/
theorem mbClaimF_ok (Pre : Mem → Prop) (nu : ℕ) (qs : List (C2 × Pl × List C2))
    (parts : List (E2 × Pl × List E2)) (v : E2) (ζ : List E2)
    (h : ∀ M, Pre M → partsV M qs = parts) (hpt : ∀ p ∈ parts, p.2.2 = ζ.take p.2.1.variableCount) :
    ClaimAt Pre ((Mb.sumClaimG nu parts v).onStack) (mbClaimFG nu qs) := by
  refine claimAt_above (v := v) _ fun c M hP x gate _ ↦ ?_
  refine hsA_of_hs ?_
  have hq : ∀ q ∈ qs, q.2.2.map (ev2 M) = ζ.take q.2.1.variableCount := fun q hq ↦
    hpt _ (by rw [← h M hP, partsV]; exact List.mem_map_of_mem hq)
  refine hs_bind (hs_g2Zero _) fun z hz ↦ hs_bind (hs_g2Const 1 z) fun one hone ↦
    hs_bind (hs_onesG _ z) fun os hos ↦ hs_mono (hs_groupsG hz (ev2_one' hone) hos _ z qs le_rfl
      fun p hp p' hp' he ↦ by rw [hq p hp, hq p' hp', he]) fun r hr ↦ ?_
  rw [hr, ev2_of_zero hz, zero_add, ← h M hP]
  show _ = E2V.sumF _
  rw [E2V.sumF_eq_sum, partsV, List.map_map]
  refine congrArg List.sum (List.map_congr_left fun q _ ↦ ?_)
  obtain ⟨cq, ⟨vc, idx⟩, pq⟩ := q
  simp only [termV, Function.comp_def, Mb.eqAboveG_eq, eqEvalF_eq_eqPt]

/-- **`mbPartsG`'s points are `ζ.take τ`** (`mbClaimF_ok`'s `hpt`). -/
theorem mbPartsG_pt (tabs : List Lvm.M3.Tab) (r : Mb.BusResG) (s : ℕ) :
    ∀ p ∈ Mb.mbPartsG tabs r s, p.2.2 = r.point.take p.2.1.variableCount := by
  intro p hp
  simp only [Mb.mbPartsG, List.mem_flatMap, List.mem_filterMap] at hp
  obtain ⟨tj, -, cc, -, hc⟩ := hp
  split at hc
  · cases hc
    rfl
  · cases hc

end Lvm6.Node.MbS
