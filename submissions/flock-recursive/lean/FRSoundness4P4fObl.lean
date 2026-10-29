-- New for `flock-recursive` (BLUEPRINT revision 4.1, A.10 rows Lr1 … B′ → P1.0, §5.1–§5.2; stage
-- P4f): X4's residual 1, `FrontHi DFhi`, from P4b's phase lemmas and T4's frames. 3.x's
-- `FRSoundnessFrObl` is the template, P4a's `FRSoundness4P4aDF` the form (one `seq4` certificate).
import FRSoundness4P4fDF
import FRSoundness4XFinal

/-!
# `FrontHi DFhi`: the front's obligations at positions 170 … 331

* **`frontClsHi_check`**: one checked classification of the `seq4` positions `170 … 331` (by
  item): every absorb is a boundary of `absPtsHi` or a round absorb of `rndPhHi`, every single
  squeeze one of `sqPtsHi` or a round squeeze; the phases at the boundary points (`ph_checkHi`), the
  rounds phases by `phOf4_eq` from their starts.
* The fields: **`ms_hi`** (Lr1, E1, RS1 are `msD`), **`habs_hi`**, **`handoff_hi`** (B′'s `DB4` is
  T4's `D1 W0X c0X 0` after P1.0's first absorb, with `ipW_eq` and `fTab_F`), **`hsingle_hi`**,
  **`hfin_hi`** (Lr1's and E1's zerocheck charges `lr4_zc_count`/`e4_zc_count`, RS1's
  `rs1_hfin4`, framed by `hfin_frame`), **`hstab_hi`**, **`chain_hi`** (`dfhi_ss`).
* **`frontHi_X : X4.FrontHi DFhi`**; **`frontObl_P4f`**, **`frontChainStab_P4f`** and
  **`ks_rev4F`** (X4's `ks_rev4` without `hHi`).
-/

namespace FR.Snd.P4f
open RecursionFast FR.Merkle FR.Rev4 Finset FR.Impl
open scoped NNReal

set_option linter.constructorNameAsVariable false

/-! ## The classification of positions 170 … 331 -/

/-- The boundary absorbs `(p, phOf4 (p − 1), phOf4 p)` from 170 on. -/
def absPtsHi : List (ℕ × ℕ × ℕ) :=
  [(179, 13, 14), (213, 14, 15), (227, 17, 18), (273, 18, 19), (275, 20, 21), (325, 21, 22),
    (326, 22, 23)]

/-- The single squeezes outside a rounds phase from 170 on. -/
def sqPtsHi : List (ℕ × ℕ × ℕ) := [(214, 15, 16), (274, 19, 20), (331, 24, 25)]

/-- The rounds phases `(b, end, k)` from 170 on: phase `k` runs from `b` to `end`. -/
def rndPhHi : List (ℕ × ℕ × ℕ) := [(179, 213, 14), (227, 273, 18), (275, 325, 21)]

def rndClsHi (par p : ℕ) : Bool :=
  rndPhHi.any fun x => decide (x.1 < p) && decide (p < x.2.1) && (p - x.1) % 2 == par

/-- **A position's class** by its item. -/
def frontClsHi (p : ℕ) : Item → Bool
  | .squeeze => fsRnd4 p != none || sqPtsHi.any (fun x => p == x.1) || rndClsHi 1 p
  | .absorb _ => absPtsHi.any (fun x => p == x.1) || rndClsHi 0 p
  | _ => true

/-- **Checked: every `seq4` position from 170 to 331 has its class.** -/
theorem frontClsHi_check :
    ((fsItems4.take 332).zipIdx).all (fun x => decide (x.2 < 170) || frontClsHi x.2 x.1) = true := by
  unfold frontClsHi rndClsHi absPtsHi sqPtsHi rndPhHi fsRnd4
  rw [fsRanges4_eq, fsItems4, Rev4.seq4_eq]; decide +kernel

/-- **Checked: the phases at the boundary points**, and the rounds phases' starts and ends. -/
theorem ph_checkHi : ((absPtsHi ++ sqPtsHi).all fun x =>
      phOf4 (x.1 - 1) == x.2.1 && phOf4 x.1 == x.2.2) = true ∧
    (rndPhHi.all fun x => phStart4 x.2.2 == x.1 && phStart4 (x.2.2 + 1) == x.2.1) = true := by
  unfold absPtsHi sqPtsHi rndPhHi phOf4 phStart4; rw [fsStarts4_eq]; decide +kernel

theorem frontClsHi_of {p : ℕ} {it : Item} (h1 : 170 ≤ p) (hp : p < 332) (h : fsItems4[p]? = some it) :
    frontClsHi p it = true := by
  have hc := frontClsHi_check
  rw [List.all_eq_true] at hc
  have := hc (it, p) (List.mem_zipIdx_iff_getElem?.mpr (by simp [hp, h]))
  simpa [show ¬ p < 170 by omega] using this

theorem pt_phHi {x : ℕ × ℕ × ℕ} (hx : x ∈ absPtsHi ++ sqPtsHi) :
    phOf4 (x.1 - 1) = x.2.1 ∧ phOf4 x.1 = x.2.2 := by
  have := List.all_eq_true.mp ph_checkHi.1 x hx
  simpa only [Bool.and_eq_true, beq_iff_eq] using this

theorem rnd_phHi {x : ℕ × ℕ × ℕ} (hx : x ∈ rndPhHi) {p : ℕ} (h1 : x.1 < p) (h2 : p < x.2.1) :
    phOf4 (p - 1) = x.2.2 ∧ phOf4 p = x.2.2 := by
  have hs := List.all_eq_true.mp ph_checkHi.2 x hx
  simp only [Bool.and_eq_true, beq_iff_eq] at hs
  have hk : x.2.2 < 51 := by
    simp only [rndPhHi, List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl | rfl <;> norm_num
  exact ⟨P4a.phOf4_eq hk (by omega) (by omega), P4a.phOf4_eq hk (by omega) (by omega)⟩

theorem abs_clsHi {p len : ℕ} (h1 : 170 ≤ p) (hp : p < 332) (h : fsItems4[p]? = some (.absorb len)) :
    (∃ x ∈ absPtsHi, p = x.1 ∧ phOf4 (p - 1) = x.2.1 ∧ phOf4 p = x.2.2) ∨
    ∃ x ∈ rndPhHi, x.1 < p ∧ p < x.2.1 ∧ (p - x.1) % 2 = 0 ∧ phOf4 (p - 1) = x.2.2 ∧
      phOf4 p = x.2.2 := by
  have hc := frontClsHi_of h1 hp h
  simp only [frontClsHi, rndClsHi, Bool.or_eq_true, List.any_eq_true, Bool.and_eq_true,
    beq_iff_eq, decide_eq_true_eq] at hc
  rcases hc with ⟨x, hx, h1⟩ | ⟨x, hx, ⟨h1, h2⟩, h3⟩
  · have := pt_phHi (List.mem_append_left _ hx); subst h1
    exact Or.inl ⟨x, hx, rfl, this⟩
  · exact Or.inr ⟨x, hx, h1, h2, h3, rnd_phHi hx h1 h2⟩

theorem sq_clsHi {p : ℕ} (h1 : 170 ≤ p) (hp : p < 332) (h : fsItems4[p]? = some .squeeze)
    (hr : fsRnd4 p = none) :
    (∃ x ∈ sqPtsHi, p = x.1 ∧ phOf4 (p - 1) = x.2.1 ∧ phOf4 p = x.2.2) ∨
    ∃ x ∈ rndPhHi, x.1 < p ∧ p < x.2.1 ∧ (p - x.1) % 2 = 1 ∧ phOf4 (p - 1) = x.2.2 ∧
      phOf4 p = x.2.2 := by
  have hc := frontClsHi_of h1 hp h
  simp only [frontClsHi, rndClsHi, hr, Bool.or_eq_true, List.any_eq_true, Bool.and_eq_true,
    beq_iff_eq, decide_eq_true_eq, bne_self_eq_false, Bool.false_eq_true, false_or] at hc
  rcases hc with ⟨x, hx, h1⟩ | ⟨x, hx, ⟨h1, h2⟩, h3⟩
  · have := pt_phHi (List.mem_append_right _ hx); subst h1
    exact Or.inl ⟨x, hx, rfl, this⟩
  · exact Or.inr ⟨x, hx, h1, h2, h3, rnd_phHi hx h1 h2⟩

/-- The multi-squeeze phases entered between 170 and 331: Lr1, E1, RS1. -/
theorem fsRanges_hi {s0 r : ℕ} (hmem : (s0, r) ∈ fsRanges4) (h1 : 170 ≤ s0 + 1)
    (h2 : s0 + 1 < 332) : (s0 = 169 ∧ r = 9) ∨ (s0 = 214 ∧ r = 12) ∨ (s0 = 326 ∧ r = 4) := by
  rw [fsRanges4_eq] at hmem
  simp only [List.mem_cons, Prod.mk.injEq, List.not_mem_nil, or_false] at hmem
  rcases hmem with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ |
    ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ |
    ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> simp_all

/-- `phOf4_eq` at known starts. -/
theorem phOf4_at {k p a b : ℕ} (hk : k < 51) (ha : phStart4 k = a) (hb : phStart4 (k + 1) = b)
    (h1 : a ≤ p) (h2 : p < b) : phOf4 p = k :=
  P4a.phOf4_eq hk (by omega) (by omega)

/-- The phases around the multi-squeeze entries (`phOf4_eq` at the starts). -/
theorem ph_msHi : phOf4 169 = 12 ∧ phOf4 170 = 13 ∧ phOf4 214 = 16 ∧ phOf4 215 = 17 ∧
    phOf4 326 = 23 ∧ phOf4 327 = 24 := by
  obtain ⟨h12, h13, h14, -, h16, h17, h18, -, -, -, -, h23, h24, h25, -⟩ := phStart_hi
  exact ⟨phOf4_at (by norm_num) h12 h13 (by norm_num) (by norm_num),
    phOf4_at (by norm_num) h13 h14 (by norm_num) (by norm_num),
    phOf4_at (by norm_num) h16 h17 (by norm_num) (by norm_num),
    phOf4_at (by norm_num) h17 h18 (by norm_num) (by norm_num),
    phOf4_at (by norm_num) h23 h24 (by norm_num) (by norm_num),
    phOf4_at (by norm_num) h24 h25 (by norm_num) (by norm_num)⟩

/-! ## `ms` -/

theorem ms_hi : ∀ s0 r, (s0, r) ∈ fsRanges4 → 170 ≤ s0 + 1 → s0 + 1 < T4.p1Start 0 →
    ∃ fin, X4.DFX DFhi (phOf4 (s0 + 1)) = msD (X4.DFX DFhi (phOf4 s0)) fin s0 r := by
  intro s0 r hmem h1 h2
  rw [X4.p1Start_zero4] at h2
  obtain ⟨p169, p170, p214, p215, p326, p327⟩ := ph_msHi
  rcases fsRanges_hi hmem h1 h2 with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · rw [p170, p169, X4.DFX_hi (by norm_num), X4.DFX_lo (by norm_num)]; exact ⟨_, rfl⟩
  · rw [p215, p214, X4.DFX_hi (by norm_num), X4.DFX_hi (by norm_num)]; exact ⟨_, rfl⟩
  · rw [p327, p326, X4.DFX_hi (by norm_num), X4.DFX_hi (by norm_num)]; exact ⟨_, rfl⟩

/-! ## `habs` -/

/-- **`FrontHi.habs`**: at every absorb from 170 to 331, the doom of the previous position gives a
failed check (`RejF4b`'s end checks, `finE` (iv), RS0's slices) or the next position's doom. -/
theorem habs_hi : ∀ L es x len, G.Matches (es ++ [x]) → fsItems4[es.length]? = some (.absorb len) →
    170 ≤ es.length → es.length < T4.p1Start 0 → ¬ T4.RejC X4.RejFX X4.c0X L es →
      X4.DFX DFhi (phOf4 (es.length - 1)) L es →
        T4.RejC X4.RejFX X4.c0X L (es ++ [x]) ∨ X4.DFX DFhi (phOf4 es.length) L (es ++ [x]) := by
  intro L es x len _ hit h1 hp _ hd
  rw [X4.p1Start_zero4] at hp
  have ap := fun {Q : Log → Log → Prop} {q : ℕ} (h : T4.Reads q Q) (hq : q ≤ es.length) =>
    h.append L es [x] hq
  rcases abs_clsHi h1 hp hit with ⟨⟨q, a, b⟩, hy, he, ha, hb⟩ |
    ⟨⟨q, e, k⟩, hy, hq, he, hpar, ha, hb⟩
  · simp only [absPtsHi, List.mem_cons, Prod.mk.injEq, List.not_mem_nil, or_false] at hy
    dsimp only at he ha hb
    rw [ha] at hd; rw [hb]
    rcases hy with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ |
      ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ <;>
      rw [X4.DFX_hi (by norm_num)] at hd ⊢
    · -- 179: Lr1's end into Lr2
      simp only [DFhi, msD, if_neg (show ¬ es.length ≤ 169 + 9 by omega)] at hd
      right; simp only [DFhi]
      rcases hd with h | h
      · exact .inl ((ap rd_bg12X (by omega)).mpr h)
      · exact .inr (P4b.lr4_habs_outer X4.src4 NI4F.srcL4 x he h)
    · -- 213: Lr end (`finLr` (ii))
      simp only [DFhi] at hd
      rcases hd with h | h
      · right; simp only [DFhi]; exact .inl ((ap rd_bg12X (by omega)).mpr h)
      · rcases P4b.lr4_habs_end X4.src4 NI4F.srcL4 x he h with h' | h'
        · exact .inl (.inl (.inr (.inl h')))
        · right; simp only [DFhi]; exact .inr h'
    · -- 227: E1's end into E2
      simp only [DFhi, msD, if_neg (show ¬ es.length ≤ 214 + 12 by omega)] at hd
      right; simp only [DFhi]
      rcases hd with h | h
      · exact .inl ((ap rd_bg16X (by omega)).mpr h)
      · exact .inr (P4b.e4_habs_outer X4.src4 NI4F.srcE4 x he h)
    · -- 273: E end (`finE` (ii))
      simp only [DFhi] at hd
      rcases hd with h | h
      · right; simp only [DFhi]; exact .inl ((ap rd_bg16X (by omega)).mpr h)
      · rcases P4b.e4_habs_end X4.src4 NI4F.srcE4 x he h with h' | h'
        · exact .inl (.inl (.inr (.inr (.inl h'))))
        · right; simp only [DFhi]; exact .inr h'
    · -- 275: E3 into E4
      simp only [DFhi] at hd
      right; simp only [DFhi]
      rcases hd with h | h
      · exact .inl ((ap rd_bg20X (by omega)).mpr h)
      · exact .inr (P4b.e4_habs_innerE X4.src4 NI4F.srcE4 NI4F.srcL4 x he h)
    · -- 325: E4 end (`finE` (iv)–(v))
      simp only [DFhi] at hd
      rcases hd with h | h
      · right; simp only [DFhi]; exact .inl ((ap rd_bg20X (by omega)).mpr h)
      · rcases P4b.e4_habs_end4 X4.src4 NI4F.srcE4 NI4F.srcL4 x he h with h' | h'
        · exact .inl (.inl (.inr (.inr (.inr (.inr (.inl h'))))))
        · right; simp only [DFhi]; exact .inr h'
    · -- 326: RS0 (the pending claims against the slices)
      rcases P4b.habs_RS0_4 (R := X4.src4) X4.okReads_X rd_far0X rd_PubX x he
        (dPend_X (by omega) hd) with h' | h'
      · exact .inl (.inl (.inr (.inr (.inr (.inr (.inr h'))))))
      · right; simp only [DFhi]; exact h'
  · simp only [rndPhHi, List.mem_cons, Prod.mk.injEq, List.not_mem_nil, or_false] at hy
    dsimp only at hq he hpar ha hb
    rw [ha] at hd; rw [hb]; right
    rcases hy with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ <;>
      rw [X4.DFX_hi (by norm_num)] at hd ⊢ <;> simp only [DFhi] at hd ⊢
    · exact hd.imp (ap rd_bg12X (by omega)).mpr
        (P4b.lr4_outer_append X4.src4 NI4F.srcL4 x (by omega) (Or.inl hpar)).mpr
    · exact hd.imp (ap rd_bg16X (by omega)).mpr
        (P4b.e4_outer_append X4.src4 NI4F.srcE4 x (by omega) (Or.inl hpar)).mpr
    · exact hd.imp (ap rd_bg20X (by omega)).mpr
        (P4b.e4_inner_appendE X4.src4 NI4F.srcE4 NI4F.srcL4 x (by omega) (Or.inl hpar)).mpr

/-! ## `hsingle` -/

open Classical in
/-- **`FrontHi.hsingle`**: at every single squeeze from 170 to 331 at most `239·2^128` answers
escape (Lr3 `2`, E3 `3`, B′ `10`, a round `2` or `3`). -/
theorem hsingle_hi : ∀ L es, G.Matches es → fsItems4[es.length]? = some .squeeze →
    fsRnd4 es.length = none → 170 ≤ es.length → es.length < T4.p1Start 0 →
      ¬ T4.RejC X4.RejFX X4.c0X L es →
        (univ.filter fun a => X4.DFX DFhi (phOf4 (es.length - 1)) L es ∧
          ¬ X4.DFX DFhi (phOf4 es.length) L (ext1 es a)).card ≤ 239 * 2 ^ 128 := by
  intro L es _ hit hrnd h1 hp hr
  rw [X4.p1Start_zero4] at hp
  rcases sq_clsHi h1 hp hit hrnd with ⟨⟨q, a, b⟩, hy, he, ha, hb⟩ |
    ⟨⟨q, e, k⟩, hy, hq, he, hpar, ha, hb⟩
  · simp only [sqPtsHi, List.mem_cons, Prod.mk.injEq, List.not_mem_nil, or_false] at hy
    dsimp only at he ha hb
    rw [ha, hb]
    rcases hy with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ <;>
      rw [X4.DFX_hi (by norm_num), X4.DFX_hi (by norm_num)]
    · -- 214: Lr3's `κ_L`
      refine le_trans (P4a.card_frame2_4 (U := P4b.EndBadLr4 X4.src4 NI4F.srcL4)
        (U' := P4b.BatBadLr4 X4.src4 NI4F.srcL4) rd_bg12X (by omega) (fun h => h) ?_)
        ((P4b.lr4_single_batch X4.src4 NI4F.srcL4 L es he).trans (by norm_num))
      intro a h
      simp only [DFhi, D16X, bg16X, bg12X] at h ⊢
      rcases h with (h | h) | h
      · exact .inl (.inl h)
      · exact .inr (.inl h)
      · exact .inl (.inr h)
    · -- 274: E3's `κ_E`
      have hc := (P4b.e4_single_batchE X4.src4 NI4F.srcE4 NI4F.srcL4 L es he).trans
        (show 4 * 2 ^ 128 ≤ 239 * 2 ^ 128 by norm_num)
      refine le_trans (P4a.card_frame2_4 (Bg := bg20X)
        (U := fun L es => P4b.EndBadE4 X4.src4 NI4F.srcE4 L es ∨ P4b.BatBadLr4 X4.src4 NI4F.srcL4 L es)
        (U' := P4b.BatBadE4 X4.src4 NI4F.srcE4 NI4F.srcL4) rd_bg20X (by omega) ?_ (fun _ h => h))
        (by convert hc using 3)
      intro h
      simp only [DFhi, bg16X] at h
      rcases h with (h | h) | h
      · exact .inl h
      · exact .inr (.inr h)
      · exact .inr (.inl h)
    · -- 331: B′'s `κ′`
      refine le_trans (P4a.card_frame2_4 (U := DRS1X) (U' := DBX) (T4.reads_false 0) (Nat.zero_le _)
        ?_ ?_) ((P4b.single_B4 (R := X4.src4) rd_far0X N4c.hcells4P4b L es he).trans (by norm_num))
      · intro h
        simp only [DFhi, msD, if_neg (show ¬ es.length ≤ 326 + 4 by omega)] at h
        exact .inr h
      · intro a h
        simp only [DFhi]
        exact h.elim False.elim id
  · simp only [rndPhHi, List.mem_cons, Prod.mk.injEq, List.not_mem_nil, or_false] at hy
    dsimp only at hq he hpar ha hb
    rw [ha, hb]
    rcases hy with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ <;>
      rw [X4.DFX_hi (by norm_num)]
    · exact le_trans (P4a.card_frame2_4 (U := P4b.D3Lr4 X4.src4 NI4F.srcL4)
        (U' := P4b.D3Lr4 X4.src4 NI4F.srcL4) rd_bg12X (by omega) (fun h => h) (fun _ h => h))
        ((P4b.lr4_single_outer X4.src4 NI4F.srcL4 L es).trans (by norm_num))
    · exact le_trans (P4a.card_frame2_4 (U := P4b.D3E4 X4.src4 NI4F.srcE4)
        (U' := P4b.D3E4 X4.src4 NI4F.srcE4) rd_bg16X (by omega) (fun h => h)
        (fun _ h => h)) ((P4b.e4_single_outer X4.src4 NI4F.srcE4 L es).trans (by norm_num))
    · exact le_trans (P4a.card_frame2_4 (U := P4b.D4E4 X4.src4 NI4F.srcE4 NI4F.srcL4)
        (U' := P4b.D4E4 X4.src4 NI4F.srcE4 NI4F.srcL4) rd_bg20X (by omega) (fun h => h)
        (fun _ h => h)) ((P4b.e4_single_innerE X4.src4 NI4F.srcE4 NI4F.srcL4 L es fun h =>
          hr (.inl (.inr (.inr (.inr (.inl h)))))).trans (by norm_num))

/-! ## `hfin` -/

open Classical in
/-- **A multi-squeeze phase's charge through its frame**: if the entry's doom is a background `Bg`
(read before the phase) or the unit's statement `U`, and the phase's final doom contains `Bg` and
the unit's final `U'`, the charge is the unit's count from `U` against escapes that clear `U'`. -/
theorem hfin_frame {Dk : ℕ → Log → Log → Prop} {s0 r : ℕ} (hmem : (s0, r) ∈ fsRanges4)
    {fin : Log → Log → Prop} (hfin : Dk (phOf4 (s0 + 1)) = msD (Dk (phOf4 s0)) fin s0 r)
    {Bg U U' : Log → Log → Prop} (hBg : T4.Reads (s0 + 1) Bg)
    (hprev : ∀ L es, Dk (phOf4 s0) L es → Bg L es ∨ U L es)
    (hfinI : ∀ L es, Bg L es ∨ U' L es → fin L es) {L es₀ : Log} (hl : es₀.length = s0 + 1)
    (hcnt : U L es₀ → (∀ as : List Digest, as.length = r → EscAtG (DPos (T4.Dp Dk)) L (ext es₀ as) →
      ¬ U' L (ext es₀ as)) → condCount (DPos (T4.Dp Dk)) L es₀ r [] ≤ deltaR) :
    condCount (DPos (T4.Dp Dk)) L es₀ r [] ≤ deltaR := by
  have esc : ∀ as : List Digest, as.length = r → EscAtG (DPos (T4.Dp Dk)) L (ext es₀ as) →
      U L es₀ ∧ ¬ U' L (ext es₀ as) := fun as has he => by
    obtain ⟨hd, hnf⟩ := T4.esc_msD hmem hfin hl as has he
    have hb : ¬ Bg L es₀ := fun hb => hnf (hfinI _ _ (.inl ((hBg.ext L es₀ as (by omega)).mpr hb)))
    exact ⟨(hprev _ _ hd).resolve_left hb, fun hu => hnf (hfinI _ _ (.inr hu))⟩
  by_cases hU : U L es₀
  · exact hcnt hU fun as has he => (esc as has he).2
  · rw [condCount_eq_zero fun as has he => hU (esc as has he).1]; exact zero_le

/-- Phase 12's doom is `bg12X` or Lr's statement (X4's `BgA4` split). -/
theorem df12_split {L es : Log} (h : P4a.DF4a X4.P4X 12 L es) :
    bg12X L es ∨ P4b.RowsBadLr4 X4.src4 NI4F.srcL4 L es := by
  simp only [P4a.DF4a, P4a.bg10_4] at h
  rcases h with ((h | h | h | h) | h | h | h) | h
  · exact .inl (.inl (.inl h))
  · exact .inl (.inl (.inr (.inl h)))
  · exact .inr h
  · exact .inl (.inr h)
  · exact .inl (.inl (.inr (.inr (.inl h))))
  · exact .inl (.inl (.inr (.inr (.inr (.inl h)))))
  · exact .inl (.inl (.inr (.inr (.inr (.inr (.inl h))))))
  · exact .inl (.inl (.inr (.inr (.inr (.inr (.inr h))))))

/-- **`FrontHi.hfin`**: Lr1's charge (`lr4_zc_count`, `≤ lrR κ/2^128`), E1's (`e4_zc_count`,
`≤ 24/2^128`: the M rows or the child claim, RSV2 §2.6), RS1's (`rs1_hfin4`, `≤ 10/2^128`). -/
theorem hfin_hi : ∀ s0 r, (s0, r) ∈ fsRanges4 → 170 ≤ s0 + 1 → s0 + 1 < T4.p1Start 0 → ∀ L es₀,
    G.Matches es₀ → es₀.length = s0 + 1 → ¬ T4.RejC X4.RejFX X4.c0X L es₀ →
      condCount (DPos (T4.Dp (X4.DFX DFhi))) L es₀ r [] ≤ deltaR := by
  intro s0 r hmem h1 h2 L es₀ _ hl _
  rw [X4.p1Start_zero4] at h2
  obtain ⟨p169, p170, p214, p215, p326, p327⟩ := ph_msHi
  rcases fsRanges_hi hmem h1 h2 with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · have hfin : X4.DFX DFhi (phOf4 (169 + 1)) = msD (X4.DFX DFhi (phOf4 169))
        (fun L es => bg12X L es ∨ P4b.ZCwLr4 X4.src4 NI4F.srcL4 L es) 169 9 := by
      rw [p170, p169, X4.DFX_hi (by norm_num), X4.DFX_lo (by norm_num)]; rfl
    refine hfin_frame (U := P4b.RowsBadLr4 X4.src4 NI4F.srcL4) hmem hfin rd_bg12X (fun L es h => ?_) (fun L es h => h) hl
      fun hU hesc => ?_
    · rw [p169, X4.DFX_lo (by norm_num)] at h; exact df12_split h
    · obtain ⟨κ, hk, -⟩ := id hU
      exact (P4b.lr4_zc_count X4.src4 NI4F.srcL4 hk hl hU hesc).trans
        (coord_le_deltaR (by have := (P4b.dims_le' κ).1; omega))
  · have hfin : X4.DFX DFhi (phOf4 (214 + 1)) = msD (X4.DFX DFhi (phOf4 214))
        (fun L es => bg16X L es ∨ P4b.ZCwE4 X4.src4 NI4F.srcE4 L es) 214 12 := by
      rw [p215, p214, X4.DFX_hi (by norm_num), X4.DFX_hi (by norm_num)]; rfl
    refine hfin_frame (U := fun L es => P4b.nE4 X4.src4 NI4F.srcE4 L es ∨ P4b.ChildBad4 NI4F.srcE4 L es)
      hmem hfin rd_bg16X (fun L es h => ?_) (fun L es h => h) hl fun hU hesc => ?_
    · rw [p214, X4.DFX_hi (by norm_num)] at h; exact h
    · obtain ⟨κ, hk, -⟩ : ∃ κ, kindOfC es₀ = .node κ ∧ True := by
        rcases hU with ⟨κ, hk, -⟩ | ⟨κ, hk, -⟩ <;> exact ⟨κ, hk, trivial⟩
      exact (P4b.e4_zc_count X4.src4 NI4F.srcE4 hk hl hU hesc).trans (coord_le_deltaR (by norm_num))
  · have hfin : X4.DFX DFhi (phOf4 (326 + 1)) = msD (X4.DFX DFhi (phOf4 326)) DRS1X 326 4 := by
      rw [p327, p326, X4.DFX_hi (by norm_num), X4.DFX_hi (by norm_num)]; rfl
    refine hfin_frame (Bg := fun _ _ => False) (U := DRS0X) hmem hfin (T4.reads_false _) (fun L es h => ?_)
      (fun L es h => h.elim False.elim id) hl fun hU hesc => ?_
    · rw [p326, X4.DFX_hi (by norm_num)] at h; exact .inr h
    · exact (P4b.rs1_hfin4 (R := X4.src4) rd_far0X rd_PubX hl hU hesc).trans
        (coord_le_deltaR (by norm_num))

/-! ## The handoff: B′ → P1.0 -/

theorem nrP0 (κ : CKind) : T4.nrP 0 κ = κ.m - 7 := by
  rcases κ with σ | ν <;> [cases σ; cases ν] <;> decide

/-- `W0X`, `c0X` read only the entries before P1.0 (`frontLocal4`). -/
theorem locX : T4.FrontLocal X4.W0X X4.c0X := fun L es L' es' _ hS hp =>
  P4b.frontLocal4 N4c.kf4 N4c.cells4 L L' (hS.1.mono (by rw [← X4.p1Start_zero4]; exact hp))

/-- **`⟨W₀, f⁽⁰⁾⟩` in P1.0's form** on a close level-0 word (3.x's `ip_W0`): T4's `trueSum` of
`lvT W0X 0` is `ι` of B′'s `ipW` (`fTab_F`, `trueSum_tabs`). -/
theorem ip_W0X {L es : Log} (hnf : ¬ T4.farL (kindOfC es) L es 0) :
    trueSum e2 (T4.lvT X4.W0X 0 L es) (T4.nrP 0 (kindOfC es)) =
      algebraMap F K (P4b.ipW (P4b.wrsL4 N4c.kf4 (kindOfC es) es)
        (P4b.cellsC N4c.cells4 (kindOfC es)) (P4b.kpL4 es) ((kindOfC es).m - 7) (X4.src4.fz L es)) := by
  rw [T4.lvT, trueSum_tabs, nrP0]
  simp only [T4.lvW, X4.W0X, P4b.W₀L4, T4.fTab_F hnf, ← map_mul, ← map_sum, P4b.ipW]
  rfl

/-- **`FrontHi.handoff`**: B′'s doom (`DB4`) is P1.0's doom `D1 0` after P1.0's first absorb
(3.x's `handoff_B`). -/
theorem handoff_hi : ∀ L es x len, G.Matches (es ++ [x]) → fsItems4[es.length]? = some (.absorb len) →
    es.length = T4.p1Start 0 → ¬ T4.RejC X4.RejFX X4.c0X L es → X4.DFX DFhi 25 L es →
      T4.RejC X4.RejFX X4.c0X L (es ++ [x]) ∨ T4.D1 X4.W0X X4.c0X 0 L (es ++ [x]) := by
  intro L es x len _ _ hl _ hd
  right
  rw [X4.DFX_hi (by norm_num)] at hd
  have hp := X4.p1Start_zero4
  have hS : T4.Same L (es ++ [x]) L es (T4.p1Start 0) := hl ▸ T4.same_append L es [x]
  have hk : kindOfC (es ++ [x]) = kindOfC es := hS.kind (by rw [hp]; norm_num)
  have hfar : T4.farL (kindOfC es) L (es ++ [x]) 0 ↔ T4.farL (kindOfC es) L es 0 :=
    T4.farL_same hS (i := 0) (by norm_num) _ (by rw [P4a.capPos_zero4, hp]; norm_num)
  have h0 : T4.hRnd (es ++ [x]) 0 = 0 := by simp [T4.hRnd, hl]
  unfold T4.D1
  rw [h0, T4.closeP_zero, not_not, hk, hfar]
  rcases hd with hd | ⟨hnf, hd⟩
  · exact .inl hd
  refine .inr ⟨hnf, by simp [hl], ?_⟩
  have ha : T4.ans3 (T4.p1Start 0) (T4.nrP 0) (es ++ [x]) = 0 := by simp [T4.ans3, hl]
  rw [ha]
  simp only [T4.Wrong2, clR2, T4.lvC, rchs2, List.range_zero, List.map_nil, bindAll, Nat.sub_zero, hk]
  rw [(locX L (es ++ [x]) L es _ hS le_rfl).2, T4.lvT_same locX hS (show 0 < 5 by norm_num) le_rfl,
    ip_W0X hnf]
  intro heq
  exact hd ((algebraMap F K).injective heq)

/-! ## `hstab` and `chain` -/

theorem len_stabExt {L : Log} {i : ℕ} {X : Log} (hX : StabExt fsRnd4 (entriesOf L (pathOf L i)) X) :
    1 ≤ X.length := by
  obtain ⟨s0, r, as, -, hs, -, rfl⟩ := hX
  rw [length_ext, List.length_take]; omega

/-- **`FrontHi.hstab`** (`dfhi_ss` on T4's `same_stabX`). -/
theorem hstab_hi : ∀ k, 12 < k → k < 26 → ∀ L i, ¬ Bad L → G.IsChain L i → ∀ X,
    StabExt fsRnd4 (entriesOf L (pathOf L i)) X → phOf4 (X.length - 1) = k →
      (DFhi k (L.take i) X ↔ DFhi k L X) := by
  intro k hk1 hk2 L i hb hci X hX hph
  have hX1 := len_stabExt hX
  obtain ⟨b1, -, -⟩ := T4.phOf_bounds (X.length - 1)
  rw [hph] at b1
  exact dfhi_ss k hk1 (by omega) _ _ X (by omega) (T4.same_stabX hb hci hX)

/-- **`FrontHi.chain`** (`dfhi_ss` on T4's `same_chain`). -/
theorem chain_hi : ∀ L j, ¬ Bad L → G.IsChain L j → ∀ k, 12 < k → k < 26 →
    phOf4 ((entriesOf L (pathOf L j)).length - 1) = k →
      (DFhi k (L.take j) (entriesOf L (pathOf L j)) ↔ DFhi k L (entriesOf L (pathOf L j))) := by
  intro L j hb hci k hk1 hk2 hph
  have h1 : 1 ≤ (entriesOf L (pathOf L j)).length :=
    List.length_pos_iff.mpr (G.matches_ne_nil hci.2)
  obtain ⟨b1, -, -⟩ := T4.phOf_bounds ((entriesOf L (pathOf L j)).length - 1)
  rw [hph] at b1
  exact dfhi_ss k hk1 (by omega) _ _ _ (by omega) (T4.same_chain hb hci)

/-! ## `FrontHi DFhi` -/

/-- **X4's residual 1**: the front's obligations at positions 170 … 331 for the concrete dooms. -/
theorem frontHi_X : X4.FrontHi DFhi where
  ms := ms_hi
  habs := habs_hi
  handoff := handoff_hi
  hsingle := hsingle_hi
  hfin := hfin_hi
  hstab := hstab_hi
  chain := chain_hi

/-- **T4's `FrontObl` at revision 4.1**, unconditionally (X4's `frontObl_X` at `frontHi_X`). -/
theorem frontObl_P4f : T4.FrontObl X4.RejFX (X4.DFX DFhi) X4.W0X X4.c0X := X4.frontObl_X frontHi_X

theorem frontChainStab_P4f : T4.FrontChainStab X4.RejFX (X4.DFX DFhi) :=
  X4.frontChainStab_X frontHi_X

/-! ## `ks_rev4` and `certificate_rev4` without residual 1 -/

section KS
open FR.X.X4

/-- **X4's `ks_rev4` with residual 1 discharged** (`frontHi_X`): `KS` for revision 4.1's verifier at
`E4X nd S.acc` and `εR`. Every hypothesis after `hε` is one of X4's residuals 2 … 6. -/
theorem ks_rev4F (impl₀ : OpImpl) (base : NodeKind → OpImpl) (S : Submission) (vk : Digest)
    (hV : S.V = VC4 impl₀ (NI4F.implN4F base) N4c.cells4) (hq : S.qV = qV4)
    {nd : X.XIR} (hE : S.E = E4X nd S.acc) (hε : S.ε = epsR)
    (hRun : X4.RunFacts4 (VsegC impl₀) (VnodeC (NI4F.implN4F base) N4c.cells4) vk)
    (I : N4c.SlotIface4 (VsegC impl₀) (VnodeC (NI4F.implN4F base) N4c.cells4)) (rd : N4c.Read4)
    (hI : I.lrows = lRows4 ∧ I.irows = nodeIRows4)
    (hRes : ∀ κ w c₁ c₂, N4c.StmtN4 κ (lRows4 κ) (nodeIRows4 κ) vk c₁ c₂ w →
      N4c.NodeResid4 I rd κ vk c₁ c₂ w)
    (D : NodeDec4 nd)
    (hL : ∀ κ L c π, X4.GoodX DFhi L → kindOf4 π = .node κ → X.InDomE c π L →
      (VnodeC (NI4F.implN4F base) N4c.cells4 κ vk c π).runLog L = some true →
      ∃ es, D.Links κ L es π c ∧ Rel (S.acc vk) c (D.readW κ L es)) :
    KS (Rel (S.acc vk)) (S.V vk) S.E S.ε S.qV :=
  X4.ks_rev4 impl₀ base S vk hV hq hE hε frontHi_X hRun I rd hI hRes D hL

/-- **X4's `certificate_rev4` with residual 1 discharged.** -/
theorem certificate_rev4F (impl₀ : OpImpl) (base : NodeKind → OpImpl) (S : Submission) {nd : X.XIR}
    (hV : S.V = VC4 impl₀ (NI4F.implN4F base) N4c.cells4) (hq : S.qV = qV4)
    (hE : S.E = E4X nd S.acc) (hε : S.ε = epsR) (hext : S.ext = ext4With nd) (hfuel : S.fuel = X.fuel)
    (hnd : DecOk4 nd) (D : NodeDec4 nd) (hR : ∀ vk, X4.Resid4 impl₀ base S nd D DFhi vk)
    (hC : ∀ vk, CompleteWithError (Rel (S.acc vk)) (S.P vk) (S.V vk) S.δ)
    (hδ : S.δ ≤ completenessCap) : Certificate S :=
  X4.certificate_rev4 impl₀ base S hV hq hE hε hext hfuel hnd D frontHi_X hR hC hδ

end KS

end FR.Snd.P4f
