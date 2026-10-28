-- New for `flock-recursive` (BLUEPRINT revision 4.1, A.10, §5.1–§5.2; stage P4a pass 4 (P4d)):
-- 3.x's `FRSoundnessFrDF`/`FrStab`/`FrObl` restricted to the phases 0 … 12 (positions < 170), at
-- `seq4` and `CKind`.
import FRSoundness4P4aL

/-!
# The front's phases 0 … 12 at revision 4.1: the dooms `DF4a`, the checks `RejF4a`, the obligations

P4a's half of T4's `FrontObl` (phases 0 … 12 are Z, L and S, positions `< 170`; P4b owns 13 … 25).

* **`Front4a`**: the parameters (the matrices `M`, the witness `zw`, a node's S2 weight `wN` and S
  truth `truthSN`, and the background `BgA`: the statement parts that phases 13 … 25 reduce, far,
  the public cells, Lr's and E's rows). **`Front4a.OK`**: their hypotheses (bit-valued, the
  indicators' kinds, the targets' and witness's locality, `BgA` reads before 3).
* **`DF4a`**: the phase dooms `Bg_k ∨ U_k` (3.x's `DF 0 … 12` with `BgA` for 3.x's
  `far0 ∨ nPub ∨ nLr ∨ nE`, `PendLcN` for its `PendN`, `L3BadN` for `L3N`). Phase 2's doom is the
  split statement `bgZ4 ∨ ¬ ZHolds` (3.x's `stmt_split` is the composer's).
* **`RejF4a`**: Z's, L2's, `finLc` (ii)'s (both kinds) and S2's checks; **`rejF4a_ok`**.
* The obligations of `FrontObl` restricted to positions `< 170`: **`ms4a`**, **`habs4a`**,
  **`hsingle4a`**, **`hfin4a`**, **`hstab4a`**, from one `seq4` classification certificate
  (`frontCls4a_check`).
-/

namespace FR.Snd.P4a
open RecursionFast FR.Merkle Finset FR.Impl

set_option linter.constructorNameAsVariable false

/-! ## The parameters -/

/-- **The front's parameters for phases 0 … 12.** -/
structure Front4a where
  M : ZLM4
  zw : Wit
  wN : CKind → Log → ℕ → ℕ → F
  truthSN : CKind → Log → Log → Prop
  BgA : Log → Log → Prop

/-- **Their hypotheses.** -/
structure Front4a.OK (P : Front4a) : Prop where
  bits : P.M.Bits
  ind : P.M.IndKinds
  et : P.M.EtLocal
  wbits : WitBits P.zw
  same : ZwSame P.zw
  wloc : WNLocal P.wN
  bgA : T4.Reads 3 P.BgA

/-! ## The dooms and the checks -/

section Doom
variable (P : Front4a)

/-- Z's background: `BgA` and S's truth. -/
def bgZ4 (L es : Log) : Prop := P.BgA L es ∨ ¬ truthS P.truthSN P.zw L es
/-- From Z3 on: and the pending c-claim. -/
def bg5_4 (L es : Log) : Prop := bgZ4 P L es ∨ PendZ P.zw L es
/-- From L3β on: S's truth leaves the background (S1 reduces it); the pending Lc claims join. -/
def bg10_4 (L es : Log) : Prop :=
  P.BgA L es ∨ PendZ P.zw L es ∨ PendLc P.M P.zw L es ∨ PendLcN P.M P.zw L es

/-- Phase 2's doom (`cap₀`): the statement split into its parts. -/
def D2F4 (L es : Log) : Prop := bgZ4 P L es ∨ ¬ ZHolds P.M P.zw L es
/-- L3β's doom (S1's entry). -/
def D10F4 (L es : Log) : Prop := bg10_4 P L es ∨ ¬ truthS P.truthSN P.zw L es

/-- **The front's phase dooms 0 … 12** (3.x's `DF`). -/
def DF4a : ℕ → Log → Log → Prop
  | 2 => D2F4 P
  | 3 => msD (D2F4 P) (fun L es => bgZ4 P L es ∨ ZEnd P.M P.zw L es) 2 10
  | 4 => fun L es => bgZ4 P L es ∨ Z2D P.M P.zw L es
  | 5 => fun L es => bg5_4 P L es ∨ D3Z P.M P.zw L es
  | 6 => fun L es => bg5_4 P L es ∨ ZendBad P.M P.zw L es
  | 7 => fun L es => bg5_4 P L es ∨ L1Bad P.M P.zw L es
  | 8 => fun L es => bg5_4 P L es ∨ D2L P.M P.zw L es
  | 9 => fun L es => bg5_4 P L es ∨ (L3Bad P.M P.zw L es ∨ L3BadN P.M P.zw L es)
  | 10 => D10F4 P
  | 11 => msD (D10F4 P) (fun L es => bg10_4 P L es ∨ S2Bad P.wN P.zw L es) 98 15
  | 12 => fun L es => bg10_4 P L es ∨ D2S P.wN P.zw L es
  | _ => fun _ _ => False

end Doom

/-- **The checks of phases 0 … 12**: `relZ`'s first conjunct, L2's rounds, `finLc` (ii) on a
segment and on a node, S2's rounds. -/
def RejF4a (M : ZLM4) (L es : Log) : Prop :=
  RejZ M L es ∨ RejL2 L es ∨ RejLc2 M L es ∨ RejLcN M L es ∨ RejS2 L es

theorem rejF4a_ok {M : ZLM4} (hE : M.EtLocal) : T4.RejOK (RejF4a M) :=
  T4.rejOK_or (rejZ_ok4 hE) (T4.rejOK_or rejL2_ok4 (T4.rejOK_or rejLc2_ok4
    (T4.rejOK_or rejLcN_ok4 rejS2_ok4)))

/-! ## Positions (`seq4` certificates) -/

/-- The boundary absorbs `(p, phOf4 (p − 1), phOf4 p)` below 170. -/
def absPts4a : List (ℕ × ℕ × ℕ) :=
  [(1, 0, 1), (2, 1, 2), (13, 3, 4), (15, 4, 5), (67, 5, 6), (69, 7, 8), (97, 8, 9), (114, 11, 12)]

/-- The single squeezes outside a rounds phase below 170. -/
def sqPts4a : List (ℕ × ℕ × ℕ) := [(14, 4, 4), (68, 6, 7), (98, 9, 10)]

/-- The rounds phases `(b, end, k)` below 170: phase `k` runs from `b` to `end`. -/
def rndPh4a : List (ℕ × ℕ × ℕ) := [(15, 67, 5), (69, 97, 8), (114, 170, 12)]

def rndCls4a (par p : ℕ) : Bool :=
  rndPh4a.any fun x => decide (x.1 < p) && decide (p < x.2.1) && (p - x.1) % 2 == par

/-- **A position's class** by its item (the phases are checked separately). -/
def frontCls4a (p : ℕ) : Item → Bool
  | .squeeze => fsRnd4 p != none || sqPts4a.any (fun x => p == x.1) || rndCls4a 1 p
  | .absorb _ => absPts4a.any (fun x => p == x.1) || rndCls4a 0 p
  | _ => true

/-- **Checked: every `seq4` position before 170 has its class**; the multi-squeeze phases
starting before 169 are Z1's and S1's. -/
theorem frontCls4a_check : ((fsItems4.take 170).zipIdx).all (fun x => frontCls4a x.2 x.1) = true ∧
    fsRanges4.all (fun x => decide (169 ≤ x.1) || x == (2, 10) || x == (98, 15)) = true := by
  unfold frontCls4a rndCls4a absPts4a sqPts4a rndPh4a fsRnd4
  rw [fsRanges4_eq, fsItems4, Rev4.seq4_eq]; decide +kernel

/-- **Checked: the phases at the boundary points**, and the rounds phases' starts and ends. -/
theorem ph_check4a : ((absPts4a ++ sqPts4a).all fun x =>
      phOf4 (x.1 - 1) == x.2.1 && phOf4 x.1 == x.2.2) = true ∧
    (rndPh4a.all fun x => phStart4 x.2.2 == x.1 && phStart4 (x.2.2 + 1) == x.2.1) = true ∧
    ((List.range 51).all fun a => decide (phStart4 a ≤ phStart4 (a + 1))) = true := by
  unfold absPts4a sqPts4a rndPh4a phOf4 phStart4; rw [fsStarts4_eq]; decide +kernel

theorem phStart4_mono {a b : ℕ} (hab : a ≤ b) (hb : b ≤ 51) : phStart4 a ≤ phStart4 b := by
  induction b with
  | zero => rw [Nat.le_zero.mp hab]
  | succ b ih =>
    rcases Nat.lt_or_ge a (b + 1) with h | h
    · have h1 := ih (by omega) (by omega)
      have h2 := List.all_eq_true.mp ph_check4a.2.2 b (List.mem_range.mpr (by omega))
      simp only [decide_eq_true_eq] at h2
      omega
    · rw [show a = b + 1 by omega]

/-- **A position between phase `k`'s start and the next is in phase `k`.** -/
theorem phOf4_eq {k p : ℕ} (hk : k < 51) (h1 : phStart4 k ≤ p) (h2 : p < phStart4 (k + 1)) :
    phOf4 p = k := by
  obtain ⟨b1, b2, b3⟩ := T4.phOf_bounds p
  by_contra hne
  rcases Nat.lt_or_gt_of_ne hne with h | h
  · have := b3 (by omega)
    have := phStart4_mono (show phOf4 p + 1 ≤ k by omega) (by omega)
    omega
  · have := phStart4_mono (show k + 1 ≤ phOf4 p by omega) b2
    omega

theorem frontCls4a_of {p : ℕ} {it : Item} (hp : p < 170) (h : fsItems4[p]? = some it) :
    frontCls4a p it = true := by
  have hc := frontCls4a_check.1
  rw [List.all_eq_true] at hc
  exact hc (it, p) (List.mem_zipIdx_iff_getElem?.mpr (by simp [hp, h]))

theorem pt_ph4a {x : ℕ × ℕ × ℕ} (hx : x ∈ absPts4a ++ sqPts4a) :
    phOf4 (x.1 - 1) = x.2.1 ∧ phOf4 x.1 = x.2.2 := by
  have := List.all_eq_true.mp ph_check4a.1 x hx
  simpa only [Bool.and_eq_true, beq_iff_eq] using this

theorem rnd_ph4a {x : ℕ × ℕ × ℕ} (hx : x ∈ rndPh4a) {p : ℕ} (h1 : x.1 < p) (h2 : p < x.2.1) :
    phOf4 (p - 1) = x.2.2 ∧ phOf4 p = x.2.2 := by
  have hs := List.all_eq_true.mp ph_check4a.2.1 x hx
  simp only [Bool.and_eq_true, beq_iff_eq] at hs
  have hk : x.2.2 < 51 := by
    simp only [rndPh4a, List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl | rfl <;> norm_num
  exact ⟨phOf4_eq hk (by omega) (by omega), phOf4_eq hk (by omega) (by omega)⟩

theorem abs_cls4a {p len : ℕ} (hp : p < 170) (h : fsItems4[p]? = some (.absorb len)) :
    (∃ x ∈ absPts4a, p = x.1 ∧ phOf4 (p - 1) = x.2.1 ∧ phOf4 p = x.2.2) ∨
    ∃ x ∈ rndPh4a, x.1 < p ∧ p < x.2.1 ∧ (p - x.1) % 2 = 0 ∧ phOf4 (p - 1) = x.2.2 ∧
      phOf4 p = x.2.2 := by
  have hc := frontCls4a_of hp h
  simp only [frontCls4a, rndCls4a, Bool.or_eq_true, List.any_eq_true, Bool.and_eq_true,
    beq_iff_eq, decide_eq_true_eq] at hc
  rcases hc with ⟨x, hx, h1⟩ | ⟨x, hx, ⟨h1, h2⟩, h3⟩
  · have := pt_ph4a (List.mem_append_left _ hx); subst h1
    exact Or.inl ⟨x, hx, rfl, this⟩
  · exact Or.inr ⟨x, hx, h1, h2, h3, rnd_ph4a hx h1 h2⟩

theorem sq_cls4a {p : ℕ} (hp : p < 170) (h : fsItems4[p]? = some .squeeze) (hr : fsRnd4 p = none) :
    (∃ x ∈ sqPts4a, p = x.1 ∧ phOf4 (p - 1) = x.2.1 ∧ phOf4 p = x.2.2) ∨
    ∃ x ∈ rndPh4a, x.1 < p ∧ p < x.2.1 ∧ (p - x.1) % 2 = 1 ∧ phOf4 (p - 1) = x.2.2 ∧
      phOf4 p = x.2.2 := by
  have hc := frontCls4a_of hp h
  simp only [frontCls4a, rndCls4a, hr, Bool.or_eq_true, List.any_eq_true, Bool.and_eq_true,
    beq_iff_eq, decide_eq_true_eq, bne_self_eq_false, Bool.false_eq_true, false_or] at hc
  rcases hc with ⟨x, hx, h1⟩ | ⟨x, hx, ⟨h1, h2⟩, h3⟩
  · have := pt_ph4a (List.mem_append_right _ hx); subst h1
    exact Or.inl ⟨x, hx, rfl, this⟩
  · exact Or.inr ⟨x, hx, h1, h2, h3, rnd_ph4a hx h1 h2⟩

theorem fsRanges4_front {s0 r : ℕ} (hmem : (s0, r) ∈ fsRanges4) (hs : s0 + 1 < 170) :
    (s0 = 2 ∧ r = 10) ∨ (s0 = 98 ∧ r = 15) := by
  have hc := frontCls4a_check.2
  rw [List.all_eq_true] at hc
  have := hc _ hmem
  simp only [Bool.or_eq_true, decide_eq_true_eq, beq_iff_eq, Prod.mk.injEq] at this
  omega

/-! ## Reads of the backgrounds -/

section Reads
variable {P : Front4a} (hP : P.OK) (hN : SNode P.wN P.truthSN P.zw)
include hP hN

theorem rd_bgZ4 : T4.Reads 3 (bgZ4 P) :=
  hP.bgA.or (T4.reads_of_same fun _ _ _ _ h => (truthS_same4 hN.truth_same hP.same h le_rfl).not)

theorem rd_bg5_4 : T4.Reads 15 (bg5_4 P) :=
  ((rd_bgZ4 hP hN).mono (by norm_num)).or (pendZ_reads4 hP.same)

omit hN in
theorem rd_bg10_4 : T4.Reads 99 (bg10_4 P) :=
  (hP.bgA.mono (by norm_num)).or (((pendZ_reads4 hP.same).mono (by norm_num)).or
    ((pendLc_reads4 hP.same).or (pendLcN_reads4 hP.same)))

end Reads

open Classical in
/-- **The frame at a single squeeze** (3.x's `card_frame2` over T4's `Reads`). -/
theorem card_frame2_4 {D D' Bg U U' : Log → Log → Prop} {p : ℕ} (hBg : T4.Reads p Bg) {L es : Log}
    (hp : p ≤ es.length) (h1 : D L es → Bg L es ∨ U L es)
    (h2 : ∀ a, Bg L (ext1 es a) ∨ U' L (ext1 es a) → D' L (ext1 es a)) :
    (univ.filter fun a => D L es ∧ ¬ D' L (ext1 es a)).card ≤
      (univ.filter fun a => U L es ∧ ¬ U' L (ext1 es a)).card := by
  refine card_le_card fun a ha => ?_
  simp only [mem_filter, mem_univ, true_and] at ha ⊢
  refine ⟨(h1 ha.1).resolve_left fun hb => ha.2 (h2 a (Or.inl ((hBg.ext1 L es a hp).mpr hb))),
    fun hu => ha.2 (h2 a (Or.inr hu))⟩

open Classical in
theorem card_or_le4 {A B C D : Digest → Prop} :
    (univ.filter fun a => (A a ∨ B a) ∧ ¬ (C a ∨ D a)).card ≤
      (univ.filter fun a => A a ∧ ¬ C a).card + (univ.filter fun a => B a ∧ ¬ D a).card := by
  refine (card_le_card fun a ha => ?_).trans (card_union_le _ _)
  simp only [mem_filter, mem_univ, true_and, mem_union, not_or] at ha ⊢
  rcases ha.1 with h | h
  · exact Or.inl ⟨h, ha.2.1⟩
  · exact Or.inr ⟨h, ha.2.2⟩

theorem ph_vals4a : phOf4 2 = 2 ∧ phOf4 3 = 3 ∧ phOf4 98 = 10 ∧ phOf4 99 = 11 := by
  obtain ⟨-, p2, p3, -, -, -, -, -, -, -, -, -, -, p98, p99⟩ := z_unit_pos4
  exact ⟨p2, p3, p98, p99⟩

/-! ## `ms` -/

/-- **`FrontObl.ms` below 170**: Z1's and S1's dooms are `msD` over their entries'. -/
theorem ms4a (P : Front4a) : ∀ s0 r, (s0, r) ∈ fsRanges4 → s0 + 1 < 170 →
    ∃ D, DF4a P (phOf4 (s0 + 1)) = msD (DF4a P (phOf4 s0)) D s0 r := by
  intro s0 r hmem hs
  obtain ⟨p2, p3, p98, p99⟩ := ph_vals4a
  rcases fsRanges4_front hmem hs with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · rw [p3, p2]; exact ⟨_, rfl⟩
  · rw [p99, p98]; exact ⟨_, rfl⟩

/-! ## `habs` -/

section Obl
variable {P : Front4a} (hP : P.OK) (hN : SNode P.wN P.truthSN P.zw)
include hP hN

/-- **`FrontObl.habs` below 170**: at every absorb, the doom of the previous position gives a
failed check or the next position's doom. -/
theorem habs4a (L es : Log) (x : ByteArray × Digest) (len : ℕ)
    (hit : fsItems4[es.length]? = some (.absorb len)) (hp : es.length < 170)
    (hd : DF4a P (phOf4 (es.length - 1)) L es) :
    RejF4a P.M L (es ++ [x]) ∨ DF4a P (phOf4 es.length) L (es ++ [x]) := by
  have hz := hP.same
  have ap := fun {Q : Log → Log → Prop} {q : ℕ} (h : T4.Reads q Q) (hq : q ≤ es.length) =>
    h.append L es [x] hq
  rcases abs_cls4a hp hit with ⟨⟨q, a, b⟩, hy, he, h1, h2⟩ |
    ⟨⟨q, e, k⟩, hy, hb, he, hpar, h1, h2⟩
  · simp only [absPts4a, List.mem_cons, Prod.mk.injEq, List.not_mem_nil, or_false] at hy
    dsimp only at he h1 h2
    rw [h1] at hd; rw [h2]
    rcases hy with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ |
      ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩
    · simp [DF4a] at hd
    · simp [DF4a] at hd
    · -- 13: Z1's end into Z2
      simp only [DF4a, msD, if_neg (show ¬ es.length ≤ 2 + 10 by omega)] at hd
      right; simp only [DF4a]
      rcases hd with h | h
      · exact Or.inl ((ap (rd_bgZ4 hP hN) (by omega)).mpr h)
      · exact Or.inr (z2_habs4 hz hP.et x he h)
    · -- 15: Z2 into Z3
      simp only [DF4a, Z2D, if_neg (show ¬ es.length ≤ 14 by omega)] at hd
      right; simp only [DF4a, bg5_4]
      rcases hd with h | h
      · exact Or.inl (Or.inl ((ap (rd_bgZ4 hP hN) (by omega)).mpr h))
      · rcases z3_habs4 hz hP.et x he h with h' | h'
        · exact Or.inr h'
        · exact Or.inl (Or.inr h')
    · -- 67: Zend
      simp only [DF4a] at hd
      rcases hd with h | h
      · right; simp only [DF4a]; exact Or.inl ((ap (rd_bg5_4 hP hN) (by omega)).mpr h)
      · rcases zend_habs4 hz hP.et x he h with h' | h'
        · exact Or.inl (Or.inl h')
        · right; simp only [DF4a]; exact Or.inr h'
    · -- 69: L1 into L2
      simp only [DF4a] at hd
      right; simp only [DF4a]
      rcases hd with h | h
      · exact Or.inl ((ap (rd_bg5_4 hP hN) (by omega)).mpr h)
      · exact Or.inr (l2_habs4 hz x he h)
    · -- 97: L3
      simp only [DF4a] at hd
      rcases hd with h | h
      · right; simp only [DF4a]; exact Or.inl ((ap (rd_bg5_4 hP hN) (by omega)).mpr h)
      · cases hn : (kindOfC es).isNode
        · rcases l3_habs4 hz x he hn h with h' | h'
          · exact Or.inl (Or.inr (Or.inr (Or.inl h')))
          · right; simp only [DF4a]; exact Or.inr (Or.inl h')
        · rcases l3N_habs4 hz x he hn h with h' | h'
          · exact Or.inl (Or.inr (Or.inr (Or.inr (Or.inl h'))))
          · right; simp only [DF4a]; exact Or.inr (Or.inr h')
    · -- 114: S1's end into S2
      simp only [DF4a, msD, if_neg (show ¬ es.length ≤ 98 + 15 by omega)] at hd
      right; simp only [DF4a]
      rcases hd with h | h
      · exact Or.inl ((ap (rd_bg10_4 hP) (by omega)).mpr h)
      · exact Or.inr (habs_S2_4 hP.wloc hz x he h)
  · simp only [rndPh4a, List.mem_cons, Prod.mk.injEq, List.not_mem_nil, or_false] at hy
    dsimp only at hb he hpar h1 h2
    rw [h1] at hd; rw [h2]; right
    rcases hy with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩
    · simp only [DF4a] at hd ⊢
      exact hd.imp (ap (rd_bg5_4 hP hN) (by omega)).mpr
        (T4.D3_append_iff (by norm_num) (TZ_local4 hz hP.et) x (by omega) (Or.inl hpar)).mpr
    · simp only [DF4a] at hd ⊢
      exact hd.imp (ap (rd_bg5_4 hP hN) (by omega)).mpr
        (append_L2_4 hz x (by omega) (Or.inl hpar)).mpr
    · simp only [DF4a] at hd ⊢
      exact hd.imp (ap (rd_bg10_4 hP) (by omega)).mpr
        (append_S2_4 hP.wloc hz x (by omega) (Or.inl hpar)).mpr

/-! ## `hsingle` -/

open Classical in
/-- **`FrontObl.hsingle` below 170**: at every single squeeze at most `239·2^128` answers escape
(the largest is Z2's `126`). -/
theorem hsingle4a (L es : Log) (hit : fsItems4[es.length]? = some .squeeze)
    (hrnd : fsRnd4 es.length = none) (hp : es.length < 170) (hr : ¬ RejF4a P.M L es) :
    (univ.filter fun a => DF4a P (phOf4 (es.length - 1)) L es ∧
      ¬ DF4a P (phOf4 es.length) L (ext1 es a)).card ≤ 239 * 2 ^ 128 := by
  have hz := hP.same
  rcases sq_cls4a hp hit hrnd with ⟨⟨q, a, b⟩, hy, he, h1, h2⟩ |
    ⟨⟨q, e, k⟩, hy, hb, he, hpar, h1, h2⟩
  · simp only [sqPts4a, List.mem_cons, Prod.mk.injEq, List.not_mem_nil, or_false] at hy
    dsimp only at he h1 h2
    rw [h1, h2]
    rcases hy with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩
    · -- 14: Z2's `λ`
      exact le_trans (card_frame2_4 (U := Z2D P.M P.zw) (U' := Z2D P.M P.zw) (rd_bgZ4 hP hN)
        (by omega) (fun h => h) (fun _ h => h)) ((z2_single4 hz hP.et L es he).trans (by norm_num))
    · -- 68: L1's `α`
      exact le_trans (card_frame2_4 (U := ZendBad P.M P.zw) (U' := L1Bad P.M P.zw)
        (rd_bg5_4 hP hN) (by omega) (fun h => h) (fun _ h => h))
        ((l1_single4 hz L es he).trans (by norm_num))
    · -- 98: L3β's `β`
      have hc : (univ.filter fun a => (L3Bad P.M P.zw L es ∨ L3BadN P.M P.zw L es) ∧
          ¬ (PendLc P.M P.zw L (ext1 es a) ∨ PendLcN P.M P.zw L (ext1 es a))).card ≤
            239 * 2 ^ 128 := by
        have h7 := l3b_single4 hz hP.ind L es he
        have h8 := l3bN_single4 hz hP.ind L es he
        have hu := card_or_le4 (A := fun _ => L3Bad P.M P.zw L es)
          (B := fun _ => L3BadN P.M P.zw L es) (C := fun a => PendLc P.M P.zw L (ext1 es a))
          (D := fun a => PendLcN P.M P.zw L (ext1 es a))
        omega
      refine le_trans (card_frame2_4 (U := fun L es => L3Bad P.M P.zw L es ∨ L3BadN P.M P.zw L es)
        (U' := fun L es => PendLc P.M P.zw L es ∨ PendLcN P.M P.zw L es) (rd_bg5_4 hP hN)
        (by omega) (fun h => h) ?_) (by convert hc using 3)
      intro a h
      simp only [DF4a, D10F4, bg10_4, bg5_4, bgZ4] at h ⊢
      rcases h with ((h | h) | h) | h | h
      · exact Or.inl (Or.inl h)
      · exact Or.inr h
      · exact Or.inl (Or.inr (Or.inl h))
      · exact Or.inl (Or.inr (Or.inr (Or.inl h)))
      · exact Or.inl (Or.inr (Or.inr (Or.inr h)))
  · simp only [rndPh4a, List.mem_cons, Prod.mk.injEq, List.not_mem_nil, or_false] at hy
    dsimp only at hb he hpar h1 h2
    rw [h1, h2]
    rcases hy with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩
    · exact le_trans (card_frame2_4 (U := D3Z P.M P.zw) (U' := D3Z P.M P.zw) (rd_bg5_4 hP hN)
        (by omega) (fun h => h) (fun _ h => h)) ((z3_single4 hz hP.et L es).trans (by norm_num))
    · exact le_trans (card_frame2_4 (U := D2L P.M P.zw) (U' := D2L P.M P.zw) (rd_bg5_4 hP hN)
        (by omega) (fun h => h) (fun _ h => h)) ((l2_single4 hz L es fun j hj hjn =>
          chk_of_not_rejL2 (fun h => hr (Or.inr (Or.inl h))) j hj hjn).trans (by norm_num))
    · exact le_trans (card_frame2_4 (U := D2S P.wN P.zw) (U' := D2S P.wN P.zw) (rd_bg10_4 hP)
        (by omega) (fun h => h) (fun _ h => h)) ((single_S2_4 hP.wloc hz L es fun j hj hjn =>
          chk_of_not_rejS2_4 (fun h => hr (Or.inr (Or.inr (Or.inr (Or.inr h))))) j hj
            hjn).trans (by norm_num))

/-! ## `hfin` -/

/-- **`FrontObl.hfin` below 170**: Z1's charge (`z1_hfin4`) and S1's (`s1_hfin4`). -/
theorem hfin4a : ∀ s0 r, (s0, r) ∈ fsRanges4 → s0 + 1 < 170 → ∀ L es₀, es₀.length = s0 + 1 →
    condCount (DPos (T4.Dp (DF4a P))) L es₀ r [] ≤ deltaR := by
  intro s0 r hmem hs L es₀ hl
  obtain ⟨p2, p3, p98, p99⟩ := ph_vals4a
  rcases fsRanges4_front hmem hs with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · exact z1_hfin4 hP.bits hP.wbits hP.same hP.et (Bg := bgZ4 P) (rd_bgZ4 hP hN)
      (fun L es h => by rw [p2] at h; exact h) (by rw [p3, p2]; rfl) (fun _ _ h => h) L es₀ hl
  · exact s1_hfin4 hN hP.same (Bg := bg10_4 P) (rd_bg10_4 hP) (by rw [p98]; rfl)
      (by rw [p99, p98]; rfl) L es₀ hl

end Obl

/-! ## `hstab`: the dooms read `L` only through the witness -/

/-- **`P` reads the same off two logs whose words agree on `X`** (3.x's `SameStab` over T4's
`Same`). -/
def SameStab4 (q : ℕ) (P : Log → Log → Prop) : Prop :=
  ∀ L L' X, q ≤ X.length → T4.Same L X L' X X.length → (P L X ↔ P L' X)

section SS
variable {q : ℕ} {Q R : Log → Log → Prop}

theorem SameStab4.up (h : SameStab4 q Q) (q' : ℕ) (hq : q ≤ q' := by norm_num) : SameStab4 q' Q :=
  fun L L' X hx hS => h L L' X (by omega) hS

theorem SameStab4.or (hQ : SameStab4 q Q) (hR : SameStab4 q R) :
    SameStab4 q fun L es => Q L es ∨ R L es :=
  fun L L' X hx hS => or_congr (hQ L L' X hx hS) (hR L L' X hx hS)

theorem SameStab4.not (hQ : SameStab4 q Q) : SameStab4 q fun L es => ¬ Q L es :=
  fun L L' X hx hS => not_congr (hQ L L' X hx hS)

theorem ss_reads4 {p : ℕ} (h : T4.Reads p Q) : SameStab4 p Q :=
  fun L L' X hx hS => h L X L' X hx hx (hS.mono hx)

theorem ss_log4 (h : ∀ L L' X p, T4.Same L X L' X p → 3 ≤ p → (Q L X ↔ Q L' X)) : SameStab4 3 Q :=
  fun L L' X hx hS => h L L' X _ hS hx

theorem ss_msD4 {prev fin : Log → Log → Prop} {s0 r : ℕ} (hp : SameStab4 (s0 + 1) prev)
    (hf : SameStab4 q fin) (hq : q ≤ s0 + r + 1) : SameStab4 (s0 + 1) (msD prev fin s0 r) := by
  intro L L' X hx hS
  unfold msD
  split_ifs with h
  · have hl : (X.take (s0 + 1)).length = s0 + 1 := by simp; omega
    exact hp L L' _ hl.ge (by rw [hl]; exact hS.take hx)
  · exact hf L L' X (by omega) hS

theorem ss_false4 (q : ℕ) : SameStab4 q fun _ _ => False := fun _ _ _ _ _ => Iff.rfl

end SS

theorem phStart_vals4a : phStart4 2 = 2 ∧ phStart4 3 = 3 ∧ phStart4 4 = 13 ∧ phStart4 5 = 15 ∧
    phStart4 6 = 67 ∧ phStart4 7 = 68 ∧ phStart4 8 = 69 ∧ phStart4 9 = 97 ∧ phStart4 10 = 98 ∧
    phStart4 11 = 99 ∧ phStart4 12 = 114 := by
  simp only [phStart4, fsStarts4_eq]; exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

section Stab
variable {P : Front4a} (hP : P.OK) (hN : SNode P.wN P.truthSN P.zw)
include hP hN

theorem ss_nS4 : SameStab4 3 fun L es => ¬ truthS P.truthSN P.zw L es :=
  ss_log4 fun _ _ _ _ h hp => (truthS_same4 hN.truth_same hP.same h hp).not

theorem ss_bgZ4 : SameStab4 3 (bgZ4 P) := (ss_reads4 hP.bgA).or (ss_nS4 hP hN)

omit hN in
theorem ss_bg10_4 : SameStab4 3 (bg10_4 P) :=
  (ss_reads4 hP.bgA).or ((ss_log4 fun _ _ _ _ h hp => (zDooms_log4 (M := P.M) hP.same h hp).2.2.2.2.1).or
    ((ss_log4 fun _ _ _ _ h hp => (lDooms_log4 (M := P.M) hP.same h hp).2.2.2.1).or
      (ss_log4 fun _ _ _ _ h hp => (lDooms_log4 (M := P.M) hP.same h hp).2.2.2.2.2)))

theorem ss_bg5_4 : SameStab4 3 (bg5_4 P) :=
  (ss_bgZ4 hP hN).or (ss_log4 fun _ _ _ _ h hp => (zDooms_log4 (M := P.M) hP.same h hp).2.2.2.2.1)

theorem ss_D2F4 : SameStab4 3 (D2F4 P) :=
  (ss_bgZ4 hP hN).or (ss_log4 fun _ _ _ _ h hp => (zDooms_log4 (M := P.M) hP.same h hp).2.2.2.2.2).not

theorem ss_D10F4 : SameStab4 3 (D10F4 P) := (ss_bg10_4 hP).or (ss_nS4 hP hN)

/-- **Phase `k`'s doom reads the same off two logs whose words agree**, on `X` of at least
`phStart4 k + 1` entries (`k ≤ 12`). -/
theorem df_ss4a : ∀ k ≤ 12, SameStab4 (phStart4 k + 1) (DF4a P k) := by
  obtain ⟨h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12⟩ := phStart_vals4a
  have hz := hP.same
  have z := fun {Q : Log → Log → Prop} (hq : ∀ L L' X p, T4.Same L X L' X p → 3 ≤ p →
    (Q L X ↔ Q L' X)) => ss_log4 hq
  have hS2 : SameStab4 114 (S2Bad P.wN P.zw) := fun L L' X hx hS => by
    simp only [S2Bad, TS_same4 hP.wloc hz hS hx]
  have hD2S : SameStab4 114 (D2S P.wN P.zw) := fun L L' X hx hS =>
    T4.D2_congrL (TS_same4 hP.wloc hz hS hx) rfl
  intro k hk
  interval_cases k
  · exact ss_false4 _
  · exact ss_false4 _
  · rw [h2]; exact ss_D2F4 hP hN
  · rw [h3]; exact (ss_msD4 (ss_D2F4 hP hN) ((ss_bgZ4 hP hN).or
      (z fun _ _ _ _ h hp => (zDooms_log4 (M := P.M) hz h hp).1)) (by norm_num)).up _
  · rw [h4]; exact ((ss_bgZ4 hP hN).or (z fun _ _ _ _ h hp => (zDooms_log4 (M := P.M) hz h hp).2.1)).up _
  · rw [h5]; exact ((ss_bg5_4 hP hN).or (z fun _ _ _ _ h hp => (zDooms_log4 (M := P.M) hz h hp).2.2.1)).up _
  · rw [h6]; exact ((ss_bg5_4 hP hN).or
      (z fun _ _ _ _ h hp => (zDooms_log4 (M := P.M) hz h hp).2.2.2.1)).up _
  · rw [h7]; exact ((ss_bg5_4 hP hN).or (z fun _ _ _ _ h hp => (lDooms_log4 (M := P.M) hz h hp).1)).up _
  · rw [h8]; exact ((ss_bg5_4 hP hN).or (z fun _ _ _ _ h hp => (lDooms_log4 (M := P.M) hz h hp).2.1)).up _
  · rw [h9]; exact ((ss_bg5_4 hP hN).or ((z fun _ _ _ _ h hp => (lDooms_log4 (M := P.M) hz h hp).2.2.1).or
      (z fun _ _ _ _ h hp => (lDooms_log4 (M := P.M) hz h hp).2.2.2.2.1))).up _
  · rw [h10]; exact (ss_D10F4 hP hN).up _
  · rw [h11]; exact (ss_msD4 ((ss_D10F4 hP hN).up 99) (((ss_bg10_4 hP).up 114).or hS2)
      (by norm_num)).up _
  · rw [h12]; exact ((ss_bg10_4 hP).up 114).or hD2S |>.up _

/-- **`FrontObl.hstab` for phases 0 … 12** (`same_stabX`). -/
theorem hstab4a : ∀ k ≤ 12, ∀ L i, ¬ Bad L → G.IsChain L i → ∀ X,
    StabExt fsRnd4 (entriesOf L (pathOf L i)) X → phOf4 (X.length - 1) = k →
      (DF4a P k (L.take i) X ↔ DF4a P k L X) := by
  intro k hk L i hb hci X hX hph
  have hX1 : 1 ≤ X.length := by
    obtain ⟨s0, r, as, -, hs, -, rfl⟩ := hX
    rw [length_ext, List.length_take]; omega
  obtain ⟨b1, -, -⟩ := T4.phOf_bounds (X.length - 1)
  rw [hph] at b1
  exact df_ss4a hP hN k hk _ _ X (by omega) (T4.same_stabX hb hci hX)

end Stab

end FR.Snd.P4a
