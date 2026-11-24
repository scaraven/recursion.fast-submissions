-- lvm6 DP6 (X9 §3 item 2): a level's invariant `QL` and the `GroupSem`/`GroupsSem` instances from X9's parts (the
-- builder `sbIR`, the loader `ldF`): the level's columns follow the recursion `colsL` (round `r + 1`'s columns are
-- FD1 on round `r`'s list `sbList` and the loader's lanes `ysF`); `levelX_cols` runs a whole level. New.
import Lvm6XDescTr0
import Lvm6XDescSbW

/-!
# A level's rounds on the machine, by X9's parts

* **`sbList M₀ N ℓ d tS r C`**: the builder's list for columns `C` (first `d + 3` positions where every column's
  encoding equals round `r`'s folded word, table `tS` of `M₀`); **`sbSpec_eq_sbList`**: `sbSpec` of any heap that
  holds the columns `C` and agrees with `M₀` on the table and the word.
* **`colsL`**: the columns round by round (`colsL 0 = C₀`, `colsL (r+1) q = fd1 N ℓ (sbList … (colsL r)) (ysF … r q)`).
* **`QL`**: round `r`'s invariant: the heap holds `colsL r` (`nc r` columns of `d + 1` coefficients) and agrees with
  `M₀` below `B`.
* **`groupSem_L`** / **`groupsSem_L`**: X8a's `GroupSem` / `GroupsSem` for groups with `sb = sbIR …`, `ld = ldF …`,
  `m = d + 3`, from the layout facts of each round (`GrpOK`; the only non-layout fact is that round `r`'s list has
  `d + 3` positions: the agreement fact the opening backwards supplies).
* **`levelX_cols`**: a level run from any transition: the columns at the end are `colsL (Σ nr)` from the columns
  after the transition.
-/

set_option autoImplicit false

namespace Lvm6.X

open RecursionFast Lvm.X Lvm.Nb Lvm6.FD Finset

open Classical in
/-- **The builder's list for columns `C`**: the first `d + 3` positions where every column's encoding is round
`r`'s folded word (table `tS` of `M₀`). -/
noncomputable def sbList (M₀ : Mem) (N ℓ d tS r : ℕ) (C : ℕ → ℕ → BF64) : List ℕ :=
  ((List.range (2 ^ ℓ)).filter fun j ↦ decide (∀ q < tbOcc M₀ tS r,
    fwdRun ptK N ℓ (fun x ↦ if x < d + 1 then C q x else 0) j =
      rdK M₀ (tbBase M₀ tS r + q + tbOcc M₀ tS r * j))).take (d + 3)

/-- **The level's columns** round by round. -/
noncomputable def colsL (M₀ : Mem) (N ℓ d tb tS : ℕ) (C₀ : ℕ → ℕ → BF64) : ℕ → ℕ → ℕ → BF64
  | 0 => C₀
  | r + 1 => fun q x ↦ fd1 N ℓ (sbList M₀ N ℓ d tS r (colsL M₀ N ℓ d tb tS C₀ r)) (ysF M₀ tb r q) x

/-- The heap holds `nc` columns of `d + 1` coefficients. -/
def ColsAt (M : Mem) (colB str d nc : ℕ) (C : ℕ → ℕ → BF64) : Prop :=
  ∀ q < nc, ∀ x < d + 1, rdK M (colB + str * q + x) = C q x

/-- **Round `r`'s invariant**: the columns `colsL r`, the heap below `B` is `M₀`'s. -/
def QL (M₀ : Mem) (N ℓ B colB str d tb tS : ℕ) (C₀ : ℕ → ℕ → BF64) (nc : ℕ → ℕ) (r : ℕ) (s : St) : Prop :=
  ColsAt s.M colB str d (nc r) (colsL M₀ N ℓ d tb tS C₀ r) ∧ ∀ x, regs ≤ x → x < B → rd s.M x = rd M₀ x

theorem heapPred_QL (M₀ : Mem) {N ℓ B colB str d tb tS : ℕ} (C₀ : ℕ → ℕ → BF64) (nc : ℕ → ℕ)
    (hc : regs ≤ colB) (r : ℕ) : HeapPred (QL M₀ N ℓ B colB str d tb tS C₀ nc r) := by
  intro s s' _ _ he ⟨h1, h2⟩
  refine ⟨fun q hq x hx ↦ ?_, fun x hx hxB ↦ (he x hx).trans (h2 x hx hxB)⟩
  rw [← h1 q hq x hx]
  simp only [rdK]
  rw [he _ (le_trans hc (by omega))]

/-- **`sbSpec` is `sbList`** on a heap holding the columns, agreeing with `M₀` on the table entry and the word. -/
theorem sbSpec_eq_sbList {M M₀ : Mem} {N ℓ colB str d tS r : ℕ} {C : ℕ → ℕ → BF64}
    (hb : tbBase M tS r = tbBase M₀ tS r) (ho : tbOcc M tS r = tbOcc M₀ tS r)
    (hw : ∀ q < tbOcc M₀ tS r, ∀ j < 2 ^ ℓ, rdK M (tbBase M₀ tS r + q + tbOcc M₀ tS r * j) =
      rdK M₀ (tbBase M₀ tS r + q + tbOcc M₀ tS r * j))
    (hc : ColsAt M colB str d (tbOcc M₀ tS r) C) :
    sbSpec M N ℓ colB str d tS r = sbList M₀ N ℓ d tS r C := by
  rw [sbSpec_eq, sbList]
  refine congrArg (List.take (d + 3)) (List.filter_congr fun j hj ↦ decide_eq_decide.2 ?_)
  have hj' : j < 2 ^ ℓ := List.mem_range.1 hj
  simp only [GoodB, encRow, hb, ho]
  refine forall₂_congr fun q hq ↦ ?_
  rw [hw q hq j hj']
  have e : (fun x ↦ if x < d + 1 then rdK M (colB + str * q + x) else 0) =
      (fun x ↦ if x < d + 1 then C q x else 0) := by
    funext x
    split_ifs with h
    · exact hc q hq x h
    · rfl
  rw [e]

/-- **A group's layout facts** at its first level round `r` (`sb = sbIR … K`, `ld = ldF`, `m = d + 3`); the last
conjunct (round `r + j`'s list has `d + 3` positions) is the agreement fact. -/
def GrpOK (M₀ : Mem) (N ℓ B colB str d tb tS : ℕ) (C₀ : ℕ → ℕ → BF64) (nc : ℕ → ℕ) (sz : ℕ) (g : GroupX)
    (r : ℕ) : Prop :=
  ∃ K, g.sb = sbIR N ℓ B colB str d tS K ∧ g.ld = ldF tb B ℓ ∧ g.m = d + 3 ∧ K < 2 ^ 64 ∧
    colB + str * g.n < 2 ^ 64 ∧ colB + str * g.n ≤ sz ∧ r + g.nr < 2 ^ 64 ∧
    ∀ j < g.nr, tS + 2 * (r + j) + 1 < B ∧ tb + 2 * (r + j) + 2 ≤ B ∧ tbOcc M₀ tS (r + j) ≤ K ∧
      tbOcc M₀ tS (r + j) ≤ nc (r + j) ∧ nc (r + j) ≤ g.n ∧ nc (r + (j + 1)) ≤ g.n ∧
      tbOcc M₀ tb (r + j) ≤ 4096 ∧
      (∀ q < tbOcc M₀ tS (r + j), ∀ p < 2 ^ ℓ, regs ≤ tbBase M₀ tS (r + j) + q + tbOcc M₀ tS (r + j) * p ∧
        tbBase M₀ tS (r + j) + q + tbOcc M₀ tS (r + j) * p < B) ∧
      (∀ q < g.n, regs ≤ tbBase M₀ tb (r + j) + q ∧
        ∀ p < 2 ^ ℓ, tbBase M₀ tb (r + j) + q + tbOcc M₀ tb (r + j) * p < B) ∧
      (sbList M₀ N ℓ d tS (r + j) (colsL M₀ N ℓ d tb tS C₀ (r + j))).length = d + 3

/-- **X8a's `GroupSem` from X9's parts.** -/
theorem groupSem_L (I : Array Word) {N ℓ B colB str d tb tS : ℕ} (M₀ : Mem) (C₀ : ℕ → ℕ → BF64) (nc : ℕ → ℕ)
    {sz : ℕ} (g : GroupX) (r : ℕ) (hN : N ≤ 64) (hN1 : 1 ≤ N) (hℓN : ℓ ≤ N) (hB : regs ≤ B)
    (hE : fdEnd B ℓ < 2 ^ 64) (hNN : N * N ≤ 8 * 2 ^ ℓ) (hd : d + 3 ≤ 2 ^ ℓ) (hcol : fdEnd B ℓ ≤ colB)
    (hstr : 2 ^ ℓ ≤ str) (htb : regs ≤ tb) (htS : regs ≤ tS)
    (hg : GrpOK M₀ N ℓ B colB str d tb tS C₀ nc sz g r) :
    GroupSem I N ℓ B colB str M₀ (fun r ↦ sbList M₀ N ℓ d tS r (colsL M₀ N ℓ d tb tS C₀ r))
      (fun r ↦ ysF M₀ tb r) (QL M₀ N ℓ B colB str d tb tS C₀ nc) sz g r := by
  obtain ⟨K, hsb, hld, hgm, hK, h64, hsz, hr64, hR⟩ := hg
  have eE : fdEnd B ℓ = B + 4096 + 11 * 2 ^ ℓ := rfl
  have eS : sA B = B + 4096 := rfl
  refine ⟨h64, hsz, hr64, fun j hj ↦ by rw [hgm]; exact (hR j hj).2.2.2.2.2.2.2.2.2, by omega,
    fun j _ x hx ↦ List.mem_range.1 (List.mem_filter.1 (List.mem_of_mem_take hx)).1,
    by rw [hsb]; exact wf_sbIR .., by rw [hsb]; exact allBelow_sbIR .., by rw [hld]; exact wf_ldF ..,
    by rw [hld]; exact allBelow_ldF .., ?_, ?_, ?_⟩
  · -- the builder
    rintro j hj s ⟨⟨hC, h0⟩, hRd⟩ hM hsz'
    obtain ⟨t1, -, hK', hnc, hncn, -, -, hWd, -, -⟩ := hR j hj
    rw [hsb]
    have hb : tbBase s.M tS (r + j) = tbBase M₀ tS (r + j) := by
      simp only [tbBase]; rw [h0 _ (le_trans htS (by omega)) (by omega)]
    have ho : tbOcc s.M tS (r + j) = tbOcc M₀ tS (r + j) := by
      simp only [tbOcc]; rw [h0 _ (le_trans htS (by omega)) (by omega)]
    have hok := sbIR_okW I (N := N) (ℓ := ℓ) (B := B) (colB := colB) (str := str) (d := d) (tS := tS) (K := K)
      (r := r + j) s.M hN hN1 hℓN hB hE hNN hd hK (by rw [ho]; exact hK')
      ⟨le_trans htS (by omega), Or.inl (by omega)⟩ ⟨le_trans htS (by omega), Or.inl (by omega)⟩ (by omega)
      (fun q hq p hp ↦ by
        rw [ho] at hq
        rw [hb, ho]
        obtain ⟨a1, a2⟩ := hWd q hq p hp
        exact ⟨⟨a1, Or.inl (by omega)⟩, by omega⟩)
      (fun q hq ↦ by
        rw [ho] at hq
        have hm : str * (q + 1) ≤ str * g.n := Nat.mul_le_mul_left _ (by omega)
        rw [Nat.mul_succ] at hm
        exact ⟨fun x hx ↦ ⟨le_trans hB (by omega), Or.inr (by omega)⟩, by omega⟩)
    have e := sbSpec_eq_sbList (N := N) (colB := colB) (str := str) (d := d)
      (C := colsL M₀ N ℓ d tb tS C₀ (r + j)) hb ho
      (fun q hq p hp ↦ by
        obtain ⟨a1, a2⟩ := hWd q hq p hp
        simp only [rdK]; rw [h0 _ a1 a2])
      (fun q hq x hx ↦ hC q (by omega) x hx)
    rw [e] at hok
    exact hok s ⟨hRd, fun _ _ _ ↦ rfl⟩ hM hsz'
  · -- the loader
    intro j hj q hq
    obtain ⟨-, t2, -, -, -, -, hocc, -, hL, -⟩ := hR j hj
    obtain ⟨a1, a2⟩ := hL q hq
    rw [hld]
    exact ldF_ok I M₀ htb t2 hocc a1 a2 hE
  · -- the round step
    rintro j hj s s' ⟨_, h0⟩ ⟨-, -, -, hcols, hfr⟩
    obtain ⟨-, -, -, -, -, hn1, -⟩ := hR j hj
    refine ⟨fun q hq x hx ↦ ?_, fun x hx hxB ↦ (hfr x hx (Or.inl hxB)).trans (h0 x hx hxB)⟩
    rw [hcols q (by omega) x (by omega)]
    rfl

/-- **Every group's layout facts**, group `k` from the rounds of the groups before it. -/
def GrpsOK (M₀ : Mem) (N ℓ B colB str d tb tS : ℕ) (C₀ : ℕ → ℕ → BF64) (nc : ℕ → ℕ) (sz : ℕ) :
    List GroupX → ℕ → Prop
  | [], _ => True
  | g :: gs, r => GrpOK M₀ N ℓ B colB str d tb tS C₀ nc sz g r ∧ GrpsOK M₀ N ℓ B colB str d tb tS C₀ nc sz gs (r + g.nr)

/-- **X8a's `GroupsSem` from X9's parts.** -/
theorem groupsSem_L (I : Array Word) {N ℓ B colB str d tb tS : ℕ} (M₀ : Mem) (C₀ : ℕ → ℕ → BF64) (nc : ℕ → ℕ)
    {sz : ℕ} (hN : N ≤ 64) (hN1 : 1 ≤ N) (hℓN : ℓ ≤ N) (hB : regs ≤ B)
    (hE : fdEnd B ℓ < 2 ^ 64) (hNN : N * N ≤ 8 * 2 ^ ℓ) (hd : d + 3 ≤ 2 ^ ℓ) (hcol : fdEnd B ℓ ≤ colB)
    (hstr : 2 ^ ℓ ≤ str) (htb : regs ≤ tb) (htS : regs ≤ tS) :
    ∀ (gs : List GroupX) (r : ℕ), GrpsOK M₀ N ℓ B colB str d tb tS C₀ nc sz gs r →
      GroupsSem I N ℓ B colB str M₀ (fun r ↦ sbList M₀ N ℓ d tS r (colsL M₀ N ℓ d tb tS C₀ r))
        (fun r ↦ ysF M₀ tb r) (QL M₀ N ℓ B colB str d tb tS C₀ nc) sz gs r
  | [], _, _ => trivial
  | g :: gs, r, ⟨h1, h2⟩ =>
    ⟨groupSem_L I M₀ C₀ nc g r hN hN1 hℓN hB hE hNN hd hcol hstr htb htS h1,
      groupsSem_L I M₀ C₀ nc hN hN1 hℓN hB hE hNN hd hcol hstr htb htS gs (r + g.nr) h2⟩

/-- **A level on the machine, by X9's parts**: from any transition (`M₀` the heap after it), the level ends with
the columns `colsL (Σ nr)` from the columns after the transition, `Inv`, the transition's output, and the heap
below `B` of `M₀`. -/
theorem levelX_cols (I : Array Word) (i : ℕ) (L : LevelX) (s : St) {d tb tS : ℕ} (nc : ℕ → ℕ)
    (hN64 : ht6 i + 1 ≤ 64) (hB : regs ≤ L.B) (hE : fdEnd L.B (ht6 i) < 2 ^ 64)
    (hNN : (ht6 i + 1) * (ht6 i + 1) ≤ 8 * 2 ^ ht6 i) (hd : d + 3 ≤ 2 ^ ht6 i) (hcol : fdEnd L.B (ht6 i) ≤ L.colB)
    (hstr : 2 ^ ht6 i ≤ L.str) (htb : regs ≤ tb) (htS : regs ≤ tS)
    (htr : Inv (semXIR I L.tr s).M)
    (hgs : GrpsOK (semXIR I L.tr s).M (ht6 i + 1) (ht6 i) L.B L.colB L.str d tb tS
      (fun q x ↦ rdK (semXIR I L.tr s).M (L.colB + L.str * q + x)) nc (semXIR I L.tr s).M.size L.gs 0) :
    let M₀ := (semXIR I L.tr s).M
    QL M₀ (ht6 i + 1) (ht6 i) L.B L.colB L.str d tb tS (fun q x ↦ rdK M₀ (L.colB + L.str * q + x)) nc
        (L.gs.map GroupX.nr).sum (semXIR I (levelX i L) s) ∧ Inv (semXIR I (levelX i L) s).M ∧
      (semXIR I (levelX i L) s).o = (semXIR I L.tr s).o ∧
      ∀ x, regs ≤ x → x < L.B → rd (semXIR I (levelX i L) s).M x = rd M₀ x := by
  intro M₀
  have hc : regs ≤ L.colB := le_trans hB (le_trans (by simp only [fdEnd]; omega) hcol)
  exact levelX_sem I i L M₀ _ _ (QL M₀ (ht6 i + 1) (ht6 i) L.B L.colB L.str d tb tS
      (fun q x ↦ rdK M₀ (L.colB + L.str * q + x)) nc) hN64 hB hcol hstr
    (fun j ↦ heapPred_QL M₀ _ nc hc j) s
    ⟨htr, ⟨fun _ _ _ _ ↦ rfl, fun _ _ _ ↦ rfl⟩, fun _ _ _ ↦ rfl⟩
    (groupsSem_L I M₀ _ nc (by omega) (by omega) (by omega) hB hE hNN hd hcol hstr htb htS L.gs 0 hgs)

/-! ## A machine round is the backward chain's round -/

open Polynomial Lvm6.Whir LeanVM.Parameters LeanVM.Protocol.Whir.AffineCombiner in
/-- **FD1 on a loader's lane is the near tuple's coefficient** (the bridge from `colsL` to W1's backward chain):
if `S` lists `d + 3` positions of a set `A` on which `T` is a near tuple of the unfolded word `Q` (`NearT`, as W1's
`ClaimBack` gives on the agreement set of the decoded folded tuple), and the lane `y` reads component `i` of lane
`v` of `Q` (`ysF_coord`), then FD1 returns component `i` of `T v`'s coefficients. -/
theorem fd1_near {N ℓ d m : ℕ} (hN : ℓ + 1 ≤ N) (hN64 : N ≤ 64) {dom : Fin (2 ^ ℓ) ↪ E2}
    (hdom : ∀ j, dom j = algebraMap BF64 E2 (ptK j)) {Q : Wd E2 (2 ^ ℓ) (m + 1)} {A : Finset (Fin (2 ^ ℓ))}
    {S : List ℕ} (hnd : S.Nodup) (hlen : S.length = d + 3)
    (hS : ∀ j ∈ S, ∃ h : j < 2 ^ ℓ, (⟨j, h⟩ : Fin (2 ^ ℓ)) ∈ A)
    {T : Tup E2 (m + 1)} (hT : NearT dom Q d A T) (v : Fin (m + 1) → Bool) {c : Fin (d + 1) → E2}
    (hc : T v = ∑ x : Fin (d + 1), C (c x) * novM ptK x) (i : Fin 2) {y : ℕ → BF64}
    (hy : ∀ j (h : j < 2 ^ ℓ), y j = basisE2.coord i (Q v ⟨j, h⟩)) :
    ∀ x < 2 ^ ℓ, fd1 N ℓ S y x = if hx : x < d + 1 then basisE2.coord i (c ⟨x, hx⟩) else 0 := by
  classical
  have he : ∃ e, ∀ j ∈ S, j ≠ e → wAtN (Q v) j = encN ptK c j := by
    obtain ⟨-, hl⟩ := hT
    have tail : ∀ j (h : j < 2 ^ ℓ), (∀ v', (T v').eval (dom ⟨j, h⟩) = Q v' ⟨j, h⟩) →
        wAtN (Q v) j = encN ptK c j := by
      intro j h hv
      rw [wAtN, dif_pos h, ← hv v, hc, eval_dom hdom]
    by_cases hne : ∃ x0 ∈ A, ∃ v', (T v').eval (dom x0) ≠ Q v' x0
    · obtain ⟨x0, hx0A, v0, hv0⟩ := hne
      refine ⟨x0.val, fun j hj hje ↦ ?_⟩
      obtain ⟨h, hA⟩ := hS j hj
      refine tail j h fun v' ↦ ?_
      by_contra hne'
      exact hje (congrArg Fin.val (Finset.card_le_one.1 hl ⟨j, h⟩
        (by simp only [Finset.mem_filter]; exact ⟨hA, v', hne'⟩) x0
        (by simp only [Finset.mem_filter]; exact ⟨hx0A, v0, hv0⟩)))
    · refine ⟨0, fun j hj _ ↦ ?_⟩
      obtain ⟨h, hA⟩ := hS j hj
      exact tail j h fun v' ↦ by
        by_contra hne'
        exact hne ⟨_, hA, v', hne'⟩
  obtain ⟨a1, a2, a3, e, a5⟩ := oneErr_coord basisE2 i hnd (show S.length = (d + 1) + 2 by omega)
    (fun j hj ↦ (hS j hj).1) he
  refine fd1_correct (y := y) (c := fun x ↦ basisE2.coord i (c x)) hN hN64 ⟨a1, a2, a3, e, fun j hj hje ↦ ?_⟩
  obtain ⟨h, -⟩ := hS j hj
  rw [hy j h]
  have := a5 j hj hje
  simp only [wAtN, h, ↓reduceDIte] at this
  exact this

end Lvm6.X
