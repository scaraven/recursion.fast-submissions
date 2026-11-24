-- lvm6 EXI (DP6 §2 item 4): the round induction of a level. The machine's columns are, exactly, the `K`-coordinates
-- of the descent's decoded tuples (`colsL_descD`: FD1 reads only the listed positions, the builder's list is the
-- extractor's `S`); the backward chain (`roundsBackD`) gives every round's list its `d + 3` positions
-- (`lens_back`); hence a level run on the machine ends with columns representing the backward chain's tuple
-- (`levelX_back`). New.
import Lvm6XDescLv
import Lvm6XDescBack
import Lvm6XDescGood

/-!
# A level's rounds, by induction

* **`fd1_congr`**: FD1 reads its lane only on `S`. **`coord_fd1F`**: a `K`-coordinate of `fd1F` is FD1 on that
  coordinate of the lane.
* **`ColsRep d C Tc`**: column `2⟨u⟩ + i` of `C` holds coordinate `i` of `Tc u` (first `d + 1` coefficients).
* **`sbList_eq_agreeS`**: the builder's list on columns representing `Tc` is `agreeS (goodAt Tc W)` for the round's
  folded word `W` (held position-major at the `tS` entry).
* **`TblOK`**: the round tables of a level of `j` rounds (round `j − 1` the least folded), top-down like `descD`;
  **`tblOK_of_chain`**: from the transition's `ChainW` and table entries (`TabW.entries`).
* **`colsL_descD`**: `colsL j` represents `descD j ch Q Tc` when `C₀` represents `Tc` (no agreement needed).
* **`lens_back`**: from W1's per-round facts (`GoodRs`) and a start tuple with its start facts, every round's
  list has `d + 3` positions.
* **`GrpLay`/`GrpsLay`**: X9's group layout facts without the agreement conjunct; `grpsOK_of_lay`.
* **`levelX_back`** (the level theorem): a level run from a transition whose tables are `TblOK` for the rounds `rs`
  and whose columns represent a start tuple `P` with W1's start facts ends with columns representing a tuple `T` of
  degree `≤ d` agreeing with the level's word on `a` columns and satisfying the level's claim (`roundsBackD`).
-/

set_option autoImplicit false

namespace Lvm6.X

open RecursionFast Lvm.X Lvm.Nb Lvm6.FD Finset Lvm6.Whir LeanVM.Parameters LeanVM.Protocol.Whir
  LeanVM.Protocol.Whir.AffineCombiner

/-! ## FD1 on the listed positions -/

/-- **FD1 reads its lane only on `S`.** -/
theorem fd1_congr {N ℓ : ℕ} {S : List ℕ} {y y' : ℕ → BF64} (h : ∀ j ∈ S, y j = y' j) (x : ℕ) :
    fd1 N ℓ S y x = fd1 N ℓ S y' x := by
  have h0 : syn0 N ℓ S y = syn0 N ℓ S y' := by
    unfold syn0; exact congrArg List.sum (List.map_congr_left fun j hj ↦ by rw [h j hj])
  have h1 : syn1 N ℓ S y = syn1 N ℓ S y' := by
    unfold syn1; exact congrArg List.sum (List.map_congr_left fun j hj ↦ by rw [h j hj])
  have hc : ∀ j, corrAt N ℓ S y j ↔ corrAt N ℓ S y' j := fun j ↦ by
    simp only [corrAt, errIdx, h0, h1]
  have hg : gIn N ℓ S y = gIn N ℓ S y' := by
    funext j
    have e1 : (if j ∈ S then y j * lam N S ℓ j else 0) = (if j ∈ S then y' j * lam N S ℓ j else 0) := by
      by_cases hj : j ∈ S
      · rw [if_pos hj, if_pos hj, h j hj]
      · rw [if_neg hj, if_neg hj]
    have e2 : (if corrAt N ℓ S y j then syn0 N ℓ S y else 0) =
        (if corrAt N ℓ S y' j then syn0 N ℓ S y' else 0) := by
      by_cases hk : corrAt N ℓ S y j
      · rw [if_pos hk, if_pos ((hc j).1 hk), h0]
      · rw [if_neg hk, if_neg (mt (hc j).2 hk)]
    unfold gIn
    rw [e1, e2]
  unfold fd1 fCos gEval
  rw [hg]

/-- **A `K`-coordinate of `fd1F`** is FD1 on that coordinate of the lane. -/
theorem coord_fd1F {N ℓ : ℕ} (S : List ℕ) (v : ℕ → E2) (x : ℕ) (i : Fin 2) :
    basisE2.coord i (fd1F basisE2 N ℓ S v x) = fd1 N ℓ S (fun j ↦ basisE2.coord i (v j)) x := by
  rw [fd1F, Module.Basis.coord_apply]
  exact congrFun (basisE2.repr_sum_self _) i

/-! ## Columns representing coefficient tuples -/

/-- **`C` represents `Tc`**: column `2⟨u⟩ + i` holds coordinate `i` of `Tc u` (first `d + 1` coefficients). -/
def ColsRep {m : ℕ} (d : ℕ) (C : ℕ → ℕ → BF64) (Tc : CT E2 m) : Prop :=
  ∀ (u : Fin m → Bool) (i : Fin 2), ∀ x < d + 1, C (2 * bitsToNat u + i) x = basisE2.coord i (Tc u x)

/-- **The first `n` columns of `C` represent `Tc`** (a level may decode only some lanes in its last round). -/
def ColsRepN {m : ℕ} (d n : ℕ) (C : ℕ → ℕ → BF64) (Tc : CT E2 m) : Prop :=
  ∀ (u : Fin m → Bool) (i : Fin 2), 2 * bitsToNat u + i < n → ∀ x < d + 1,
    C (2 * bitsToNat u + i) x = basisE2.coord i (Tc u x)

theorem ColsRepN.mono {m d n n' : ℕ} {C : ℕ → ℕ → BF64} {Tc : CT E2 m} (hn : n ≤ n')
    (h : ColsRepN d n' C Tc) : ColsRepN d n C Tc := fun u i hq ↦ h u i (by omega)

theorem ColsRepN.full {m d n : ℕ} {C : ℕ → ℕ → BF64} {Tc : CT E2 m} (hn : 2 * 2 ^ m ≤ n)
    (h : ColsRepN d n C Tc) : ColsRep d C Tc := fun u i ↦
  h u i (by have := bitsToNat_lt u; have := i.2; omega)

/-- The zero-padded forward NTT of a column is `encN` of its first `d + 1` entries. -/
theorem fwdRun_cols {N ℓ d : ℕ} (hN : ℓ ≤ N) (hN64 : N ≤ 64) (hd : d + 1 ≤ 2 ^ ℓ) (f : ℕ → BF64) {j : ℕ}
    (hj : j < 2 ^ ℓ) :
    fwdRun ptK N ℓ (fun x ↦ if x < d + 1 then f x else 0) j = encN ptK (fun x : Fin (d + 1) ↦ f x) j := by
  let g : ℕ → BF64 := fun x ↦ if x < d + 1 then f x else 0
  have e1 : fwdRun ptK N ℓ g j = encN ptK (fun x : Fin (2 ^ ℓ) ↦ g x) j := by
    refine fwdRun_enc ptK_xor (ptK_injOn hN64) le_rfl hN (fun x : Fin (2 ^ ℓ) ↦ g x) g (fun x ↦ ?_) hj
    by_cases h : x < 2 ^ ℓ
    · rw [dif_pos h]
    · rw [dif_neg h]; exact if_neg (by omega)
  show fwdRun ptK N ℓ g j = _
  rw [e1, encN_pad g hd (fun x hx ↦ if_neg (by omega))]
  exact congrArg (fun c : Fin (d + 1) → BF64 ↦ encN ptK c j) (funext fun x ↦ if_pos x.2)

open Classical in
/-- **The builder's list is the extractor's `S`** on columns representing `Tc`, for the round's folded word `W`
held position-major at the `tS` entry. -/
theorem sbList_eq_agreeS {M₀ : Mem} {N ℓ d tS r m buf : ℕ} {W : Wd E2 (2 ^ ℓ) m} {Tc : CT E2 m}
    {C : ℕ → ℕ → BF64} (hN : ℓ ≤ N) (hN64 : N ≤ 64) (hd : d + 1 ≤ 2 ^ ℓ)
    (hW : HoldsW M₀ buf ℓ m W) (hb : tbBase M₀ tS r = buf) (ho : tbOcc M₀ tS r = 2 * 2 ^ m)
    (hC : ColsRep d C Tc) :
    sbList M₀ N ℓ d tS r C = agreeS ℓ (d + 1) (goodAt d Tc W) := by
  rw [sbList, agreeS]
  refine congrArg (List.take (d + 3)) (List.filter_congr fun j hj ↦ decide_eq_decide.2 ?_)
  have hj : j < 2 ^ ℓ := List.mem_range.1 hj
  have hE : ∀ (u : Fin m → Bool) (i : Fin 2),
      fwdRun ptK N ℓ (fun x ↦ if x < d + 1 then C (2 * bitsToNat u + i) x else 0) j =
        basisE2.coord i (encN ptK (fun x : Fin (d + 1) ↦ Tc u x) j) := fun u i ↦ by
    rw [fwdRun_cols hN hN64 hd _ hj, encN_coord basisE2]
    exact congrArg (fun c : Fin (d + 1) → BF64 ↦ encN ptK c j) (funext fun x ↦ hC u i x x.2)
  have hV : ∀ (u : Fin m → Bool) (i : Fin 2),
      rdK M₀ (tbBase M₀ tS r + (2 * bitsToNat u + i) + tbOcc M₀ tS r * j) = basisE2.coord i (wAtN (W u) j) :=
    fun u i ↦ by
      have h2 := ysF_coord hW hb ho u ⟨j, hj⟩
      rw [show wAtN (W u) j = W u ⟨j, hj⟩ from dif_pos hj]
      fin_cases i
      · show rdK M₀ (tbBase M₀ tS r + (2 * bitsToNat u + 0) + tbOcc M₀ tS r * j) = basisE2.coord 0 _
        rw [Nat.add_zero]; exact h2.1
      · show rdK M₀ (tbBase M₀ tS r + (2 * bitsToNat u + 1) + tbOcc M₀ tS r * j) = basisE2.coord 1 _
        exact h2.2
  constructor
  · intro hg u
    refine coord_ext fun i ↦ ?_
    have hq : 2 * bitsToNat u + (i : ℕ) < tbOcc M₀ tS r := by
      have := bitsToNat_lt u; have := i.2; rw [ho]; omega
    rw [← hE, ← hV]
    exact hg _ hq
  · intro hg q hq
    rw [ho] at hq
    have hq2 : q / 2 < 2 ^ m := by omega
    let u : Fin m → Bool := fun i ↦ (q / 2).testBit i
    have hu : bitsToNat u = q / 2 := bitsToNat_testBit hq2
    have eq : q = 2 * bitsToNat u + ((⟨q % 2, Nat.mod_lt _ (by norm_num)⟩ : Fin 2) : ℕ) := by
      simp only [hu]; omega
    rw [eq, hE, hV, hg u]

/-! ## The round tables of a level -/

/-- **The round tables of a level of `j` rounds** (top-down, like `descD`): round `j − 1` reads the unfolded word
`Q` at the `tb` entry (`2·2^(m+j)` words a row) and its fold by the first pair of `ch` at the `tS` entry. -/
def TblOK (M₀ : Mem) (ℓ tb tS : ℕ) (dom : Fin (2 ^ ℓ) ↪ E2) (m : ℕ) :
    (j : ℕ) → List (E2 × E2) → Wd E2 (2 ^ ℓ) (m + j) → Prop
  | 0, _, _ => True
  | j + 1, ch, Q => (HoldsW M₀ (tbBase M₀ tb j) ℓ (m + j + 1) Q ∧ tbOcc M₀ tb j = 2 * 2 ^ (m + j + 1) ∧
      HoldsW M₀ (tbBase M₀ tS j) ℓ (m + j) (foldQ dom (ch.headD (0, 0)).1 (ch.headD (0, 0)).2 Q) ∧
      tbOcc M₀ tS j = 2 * 2 ^ (m + j)) ∧
    TblOK M₀ ℓ tb tS dom m j ch.tail (foldQ dom (ch.headD (0, 0)).1 (ch.headD (0, 0)).2 Q)

theorem chainW_head {M : Mem} {h : ℕ} {hh : h ≤ 64} {m : ℕ} :
    ∀ {j : ℕ} {bf : ℕ → ℕ} {l : List (E2 × E2)} {W : Wd E2 (2 ^ h) (m + j)},
      ChainW M h hh m j bf l W → HoldsW M (bf 0) h (m + j) W
  | 0, _, _, _, hc => hc
  | _ + 1, _, _, _, hc => hc.1

/-- **The tables from the transition**: the fold chain's buffers and the table entries (`TabW.entries`). -/
theorem tblOK_of_chain {M : Mem} {ℓ : ℕ} (hh : ℓ ≤ 64) {tb tS m : ℕ} :
    ∀ (j : ℕ) (bf : ℕ → ℕ) (l : List (E2 × E2)) (W : Wd E2 (2 ^ ℓ) (m + j)), ChainW M ℓ hh m j bf l W →
      (∀ r < j, tbBase M tb r = bf (j - 1 - r) ∧ tbOcc M tb r = 2 * 2 ^ (m + 1 + r) ∧
        tbBase M tS r = bf (j - r) ∧ tbOcc M tS r = 2 * 2 ^ (m + r)) →
      TblOK M ℓ tb tS (domE ℓ hh) m j l W
  | 0, _, _, _, _, _ => trivial
  | j + 1, bf, l, W, hc, ht => by
    obtain ⟨h0, hc'⟩ := hc
    obtain ⟨e1, e2, e3, e4⟩ := ht j (by omega)
    refine ⟨⟨?_, ?_, ?_, e4⟩, tblOK_of_chain hh j (fun k ↦ bf (k + 1)) l.tail _ hc' fun r hr ↦ ?_⟩
    · rw [e1, show j + 1 - 1 - j = 0 by omega]; exact h0
    · rw [e2, show m + 1 + j = m + j + 1 by omega]
    · rw [e3, show j + 1 - j = 0 + 1 by omega]; exact chainW_head hc'
    · obtain ⟨f1, f2, f3, f4⟩ := ht r (by omega)
      refine ⟨?_, f2, ?_, f4⟩
      · rw [f1, show j + 1 - 1 - r = (j - 1 - r) + 1 by omega]
      · rw [f3, show j + 1 - r = (j - r) + 1 by omega]

theorem tblOK_succ_map {M₀ : Mem} {ℓ tb tS : ℕ} {dom : Fin (2 ^ ℓ) ↪ E2} {m j : ℕ} {rs : List (Rnd E2)}
    {Q : Wd E2 (2 ^ ℓ) (m + (j + 1))} (h : TblOK M₀ ℓ tb tS dom m (j + 1) (rs.map fun r ↦ (r.α, r.β)) Q) :
    (HoldsW M₀ (tbBase M₀ tb j) ℓ (m + j + 1) Q ∧ tbOcc M₀ tb j = 2 * 2 ^ (m + j + 1) ∧
      HoldsW M₀ (tbBase M₀ tS j) ℓ (m + j) (foldQ dom (rs.headD default).α (rs.headD default).β Q) ∧
      tbOcc M₀ tS j = 2 * 2 ^ (m + j)) ∧
    TblOK M₀ ℓ tb tS dom m j (rs.tail.map fun r ↦ (r.α, r.β))
      (foldQ dom (rs.headD default).α (rs.headD default).β Q) := by
  cases rs <;> exact h

/-! ## The machine's columns are the descent's coefficients -/

/-- **`colsL j` represents the descent's output**: with the round tables `TblOK` and start columns representing
`Tc`, the machine's columns after `j` rounds represent `descD j ch Q Tc` (exactly: FD1 reads the unfolded word only
on the builder's list, which is the extractor's `S`). -/
theorem colsL_descD {M₀ : Mem} {N ℓ d tb tS : ℕ} {dom : Fin (2 ^ ℓ) ↪ E2} (hN : ℓ ≤ N) (hN64 : N ≤ 64)
    (hd : d + 1 ≤ 2 ^ ℓ) (C₀ : ℕ → ℕ → BF64) {m : ℕ} :
    ∀ (j : ℕ) (ch : List (E2 × E2)) (Q : Wd E2 (2 ^ ℓ) (m + j)) (Tc : CT E2 m),
      TblOK M₀ ℓ tb tS dom m j ch Q → ColsRep d C₀ Tc →
      ColsRep d (colsL M₀ N ℓ d tb tS C₀ j) (descD basisE2 N d dom j ch Q Tc)
  | 0, _, _, _, _, hC => hC
  | j + 1, ch, Q, Tc, hT, hC => by
    obtain ⟨⟨hWu, hou, hWf, hof⟩, hT'⟩ := hT
    have ih := colsL_descD hN hN64 hd C₀ j ch.tail _ Tc hT' hC
    have hS := sbList_eq_agreeS hN hN64 hd hWf rfl hof ih
    intro v i x _
    simp only [colsL, descD, stepD]
    rw [hS, coord_fd1F]
    refine fd1_congr (fun p hp ↦ ?_) x
    have hp' : p < 2 ^ ℓ := List.mem_range.1 (List.mem_filter.1 (List.mem_of_mem_take hp)).1
    rw [show wAtN (Q v) p = Q v ⟨p, hp'⟩ from dif_pos hp']
    have h2 := ysF_coord hWu rfl hou v ⟨p, hp'⟩
    fin_cases i
    · show ysF M₀ tb j (2 * bitsToNat v + 0) p = basisE2.coord 0 (Q v ⟨p, hp'⟩)
      rw [Nat.add_zero]; exact h2.1
    · show ysF M₀ tb j (2 * bitsToNat v + 1) p = basisE2.coord 1 (Q v ⟨p, hp'⟩)
      exact h2.2

/-! ## Every round's list has `d + 3` positions -/

/-- **The lists' lengths from the backward chain**: under W1's per-round facts and a start tuple with its start
facts (`roundsBackD`'s hypotheses), the builder's list of every round has `d + 3` positions. -/
theorem lens_back {M₀ : Mem} {N ℓ d tb tS : ℕ} {dom : Fin (2 ^ ℓ) ↪ E2} (hN : ℓ + 1 ≤ N) (hN64 : N ≤ 64)
    (hd : d + 1 ≤ 2 ^ ℓ) (hdom : ∀ j, dom j = algebraMap BF64 E2 (ptK j)) (C₀ : ℕ → ℕ → BF64)
    {Ar : ℕ → ℕ} {m : ℕ} :
    ∀ (j t : ℕ) (rs : List (Rnd E2)) (Q : Wd E2 (2 ^ ℓ) (m + j)) (W : Tup E2 (m + j) →ₗ[E2] E2) (σ : E2)
      (a : ℕ), GoodRs dom Ar d j t rs Q W σ →
      (∀ s, t ≤ s → s + 1 < t + j → Ar s ≤ Ar (s + 1) - 1) →
      (0 < j → a ≤ Ar t - 1) →
      (∀ s, t ≤ s → s < t + j → d + 3 ≤ Ar s) →
      ∀ (Tc : CT E2 m) (P : Tup E2 m), RepT d Tc P → DegLE d P →
        aOut Ar a t j ≤ (agree dom P (foldsQ dom j rs Q)).card →
        foldsW j rs W P = foldsC j rs σ →
        TblOK M₀ ℓ tb tS dom m j (rs.map fun r ↦ (r.α, r.β)) Q → ColsRep d C₀ Tc →
        ∀ r < j, (sbList M₀ N ℓ d tS r (colsL M₀ N ℓ d tb tS C₀ r)).length = d + 3
  | 0, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, r, hr => absurd hr (Nat.not_lt_zero _)
  | j + 1, t, rs, Q, W, σ, a, hG, hch, ha, h3, Tc, P, hR, hP, hA, hW, hT, hC, r, hr => by
    obtain ⟨-, hG'⟩ := hG
    obtain ⟨⟨-, -, hWf, hof⟩, hT'⟩ := tblOK_succ_map hT
    rcases Nat.lt_succ_iff_lt_or_eq.1 hr with hr | hr
    · exact lens_back hN hN64 hd hdom C₀ j (t + 1) rs.tail _ _ _ (Ar t) hG'
        (fun s h1 h2 ↦ hch s (by omega) (by omega)) (fun _ ↦ hch t le_rfl (by omega))
        (fun s h1 h2 ↦ h3 s (by omega) (by omega)) Tc P hR hP hA hW hT' hC r hr
    · rw [hr]
      obtain ⟨T₁, hR₁, -, hA₁, -⟩ := roundsBackD basisE2 hN hN64 hd hdom j (t + 1) rs.tail _ _ _ (Ar t) hG'
        (fun s h1 h2 ↦ hch s (by omega) (by omega)) (fun _ ↦ hch t le_rfl (by omega))
        (fun s h1 h2 ↦ h3 s (by omega) (by omega)) Tc P hR hP hA hW
      have hcols := colsL_descD (N := N) (by omega) hN64 hd C₀ j _ _ Tc hT' hC
      rw [sbList_eq_agreeS (by omega) hN64 hd hWf rfl hof hcols]
      have h3t := h3 t le_rfl (by omega)
      exact (agreeS_spec (k := d + 1) (dom := dom) (T := T₁)
        (w := foldQ dom (rs.headD default).α (rs.headD default).β Q) (fun i h ↦ by
        have hR' : ∀ u, T₁ u = _ := hR₁
        simp only [goodAt, mem_agree, hR', eval_dom hdom, wAtN, h, ↓reduceDIte]) (by omega)).2.1

/-! ## The level theorem -/

/-- **A group's layout facts** (X9's `GrpOK` without the agreement conjunct). -/
def GrpLay (M₀ : Mem) (N ℓ B colB str d tb tS : ℕ) (nc : ℕ → ℕ) (sz : ℕ) (g : GroupX) (r : ℕ) : Prop :=
  ∃ K, g.sb = sbIR N ℓ B colB str d tS K ∧ g.ld = ldF tb B ℓ ∧ g.m = d + 3 ∧ K < 2 ^ 64 ∧
    colB + str * g.n < 2 ^ 64 ∧ colB + str * g.n ≤ sz ∧ r + g.nr < 2 ^ 64 ∧
    ∀ j < g.nr, tS + 2 * (r + j) + 1 < B ∧ tb + 2 * (r + j) + 2 ≤ B ∧ tbOcc M₀ tS (r + j) ≤ K ∧
      tbOcc M₀ tS (r + j) ≤ nc (r + j) ∧ nc (r + j) ≤ g.n ∧ nc (r + (j + 1)) ≤ g.n ∧
      tbOcc M₀ tb (r + j) ≤ 4096 ∧
      (∀ q < tbOcc M₀ tS (r + j), ∀ p < 2 ^ ℓ, regs ≤ tbBase M₀ tS (r + j) + q + tbOcc M₀ tS (r + j) * p ∧
        tbBase M₀ tS (r + j) + q + tbOcc M₀ tS (r + j) * p < B) ∧
      (∀ q < g.n, regs ≤ tbBase M₀ tb (r + j) + q ∧
        ∀ p < 2 ^ ℓ, tbBase M₀ tb (r + j) + q + tbOcc M₀ tb (r + j) * p < B)

/-- **Every group's layout facts.** -/
def GrpsLay (M₀ : Mem) (N ℓ B colB str d tb tS : ℕ) (nc : ℕ → ℕ) (sz : ℕ) : List GroupX → ℕ → Prop
  | [], _ => True
  | g :: gs, r => GrpLay M₀ N ℓ B colB str d tb tS nc sz g r ∧ GrpsLay M₀ N ℓ B colB str d tb tS nc sz gs (r + g.nr)

theorem grpOK_of_lay {M₀ : Mem} {N ℓ B colB str d tb tS : ℕ} {nc : ℕ → ℕ} {sz : ℕ} {g : GroupX} {r : ℕ}
    (C₀ : ℕ → ℕ → BF64) (h : GrpLay M₀ N ℓ B colB str d tb tS nc sz g r)
    (hl : ∀ j < g.nr, (sbList M₀ N ℓ d tS (r + j) (colsL M₀ N ℓ d tb tS C₀ (r + j))).length = d + 3) :
    GrpOK M₀ N ℓ B colB str d tb tS C₀ nc sz g r := by
  obtain ⟨K, a1, a2, a3, a4, a5, a6, a7, hR⟩ := h
  refine ⟨K, a1, a2, a3, a4, a5, a6, a7, fun j hj ↦ ?_⟩
  obtain ⟨b1, b2, b3, b4, b5, b6, b7, b8, b9⟩ := hR j hj
  exact ⟨b1, b2, b3, b4, b5, b6, b7, b8, b9, hl j hj⟩

theorem grpsOK_of_lay {M₀ : Mem} {N ℓ B colB str d tb tS : ℕ} {nc : ℕ → ℕ} {sz : ℕ} (C₀ : ℕ → ℕ → BF64) :
    ∀ (gs : List GroupX) (r : ℕ), GrpsLay M₀ N ℓ B colB str d tb tS nc sz gs r →
      (∀ k, r ≤ k → k < r + (gs.map GroupX.nr).sum →
        (sbList M₀ N ℓ d tS k (colsL M₀ N ℓ d tb tS C₀ k)).length = d + 3) →
      GrpsOK M₀ N ℓ B colB str d tb tS C₀ nc sz gs r
  | [], _, _, _ => trivial
  | g :: gs, r, ⟨h1, h2⟩, hl => by
    have e : ((g :: gs).map GroupX.nr).sum = g.nr + (gs.map GroupX.nr).sum := by
      simp only [List.map_cons, List.sum_cons]
    rw [e] at hl
    exact ⟨grpOK_of_lay C₀ h1 fun j hj ↦ hl (r + j) (by omega) (by omega),
      grpsOK_of_lay C₀ gs (r + g.nr) h2 fun k hk1 hk2 ↦ hl k (by omega) (by omega)⟩

/-- **The level theorem**: a level run from a transition whose round tables are `TblOK` for the rounds `rs` of the
level's word `Q`, whose layout gives `GrpsOK` once every round's list has `d + 3` positions (`GrpsLay` with `grpsOK_of_lay`, or
EXG's `grpsOK18`), and whose columns represent the coefficients `Tc` of a start tuple `P`
with W1's start facts (`GoodRs` a round, `P`'s degree, agreement with the folded word and claim) ends with its first `nc J`
columns representing the coefficients of a tuple `T` of degree `≤ d` agreeing with `Q` on `a` columns and with `W T = σ`
(the backward chain's tuple), `Inv`, the transition's output and the heap below `B` of the transition. -/
theorem levelX_back (I : Array Word) (i : ℕ) (L : LevelX) (s : St) {h d tb tS m J : ℕ} (nc : ℕ → ℕ)
    (hh : ht6 i = h) {dom : Fin (2 ^ h) ↪ E2} (hdom : ∀ j, dom j = algebraMap BF64 E2 (ptK j))
    (hN64 : ht6 i + 1 ≤ 64) (hB : regs ≤ L.B) (hE : fdEnd L.B (ht6 i) < 2 ^ 64)
    (hNN : (ht6 i + 1) * (ht6 i + 1) ≤ 8 * 2 ^ ht6 i) (hd : d + 3 ≤ 2 ^ ht6 i) (hcol : fdEnd L.B (ht6 i) ≤ L.colB)
    (hstr : 2 ^ ht6 i ≤ L.str) (htb : regs ≤ tb) (htS : regs ≤ tS)
    (htr : Inv (semXIR I L.tr s).M)
    (hlay : (∀ r < J, (sbList (semXIR I L.tr s).M (ht6 i + 1) (ht6 i) d tS r (colsL (semXIR I L.tr s).M (ht6 i + 1)
      (ht6 i) d tb tS (fun q x ↦ rdK (semXIR I L.tr s).M (L.colB + L.str * q + x)) r)).length = d + 3) →
      GrpsOK (semXIR I L.tr s).M (ht6 i + 1) (ht6 i) L.B L.colB L.str d tb tS
        (fun q x ↦ rdK (semXIR I L.tr s).M (L.colB + L.str * q + x)) nc (semXIR I L.tr s).M.size L.gs 0)
    (hJ : (L.gs.map GroupX.nr).sum = J)
    (rs : List (Rnd E2)) (Q : Wd E2 (2 ^ h) (m + J))
    (hT : TblOK (semXIR I L.tr s).M h tb tS dom m J (rs.map fun r ↦ (r.α, r.β)) Q)
    {Ar : ℕ → ℕ} {t : ℕ} {W : Tup E2 (m + J) →ₗ[E2] E2} {σ : E2} {a : ℕ}
    (hG : GoodRs dom Ar d J t rs Q W σ) (hch : ∀ s, t ≤ s → s + 1 < t + J → Ar s ≤ Ar (s + 1) - 1)
    (ha : 0 < J → a ≤ Ar t - 1) (h3 : ∀ s, t ≤ s → s < t + J → d + 3 ≤ Ar s)
    {Tc : CT E2 m} {P : Tup E2 m}
    (hC : ColsRep d (fun q x ↦ rdK (semXIR I L.tr s).M (L.colB + L.str * q + x)) Tc)
    (hR : RepT d Tc P) (hP : DegLE d P) (hA : aOut Ar a t J ≤ (agree dom P (foldsQ dom J rs Q)).card)
    (hW : foldsW J rs W P = foldsC J rs σ) :
    ∃ (T : Tup E2 (m + J)) (Tc' : CT E2 (m + J)), RepT d Tc' T ∧ DegLE d T ∧ a ≤ (agree dom T Q).card ∧
      W T = σ ∧ ColsRepN d (nc J) (fun q x ↦ rdK (semXIR I (levelX i L) s).M (L.colB + L.str * q + x)) Tc' ∧
      Inv (semXIR I (levelX i L) s).M ∧ (semXIR I (levelX i L) s).o = (semXIR I L.tr s).o ∧
      ∀ x, regs ≤ x → x < L.B → rd (semXIR I (levelX i L) s).M x = rd (semXIR I L.tr s).M x := by
  subst hh
  have hd1 : d + 1 ≤ 2 ^ ht6 i := by omega
  have hlens := lens_back (M₀ := (semXIR I L.tr s).M) (N := ht6 i + 1) (tb := tb) (tS := tS) le_rfl hN64 hd1 hdom
    (fun q x ↦ rdK (semXIR I L.tr s).M (L.colB + L.str * q + x)) J t rs Q W σ a hG hch ha h3 Tc P hR hP hA hW
    hT hC
  have hgs := hlay hlens
  obtain ⟨hQL, hI, hO, hF⟩ := levelX_cols I i L s nc hN64 hB hE hNN hd hcol hstr htb htS htr hgs
  obtain ⟨T, hRT, hTd, hTa, hTW⟩ := roundsBackD basisE2 (N := ht6 i + 1) le_rfl hN64 hd1 hdom J t rs Q W σ a
    hG hch ha h3 Tc P hR hP hA hW
  have hcols := colsL_descD (M₀ := (semXIR I L.tr s).M) (N := ht6 i + 1) (by omega) hN64 hd1
    (fun q x ↦ rdK (semXIR I L.tr s).M (L.colB + L.str * q + x)) J _ Q Tc hT hC
  refine ⟨T, _, hRT, hTd, hTa, hTW, fun u k hq x hx ↦ ?_, hI, hO, hF⟩
  rw [← hcols u k x hx]
  rw [hJ] at hQL
  exact hQL.1 _ hq x hx

end Lvm6.X
