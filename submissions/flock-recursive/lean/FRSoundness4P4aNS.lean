-- G6: this module also holds the former modules `FRSoundness4P4aDF`, `FRSoundness4P4bRS`, `FRSoundness4P4aT`, `FRSoundness4P4aRS`, `FRSoundness4P4aNZ` (one section each, in import order).
import FRSoundness4P4aL
import FRSoundness4P4bE
import FRNodeCircuit4

section G6_FRSoundness4P4aDF

-- New for `flock-recursive` (BLUEPRINT revision 4.1, A.10, §5.1–§5.2; stage P4a pass 4 (P4d)):
-- 3.x's `FRSoundnessFrDF`/`FrStab`/`FrObl` restricted to the phases 0 … 12 (positions < 170), at
-- `seq4` and `CKind`.

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
    ((List.range 55).all fun a => decide (phStart4 a ≤ phStart4 (a + 1))) = true := by
  unfold absPts4a sqPts4a rndPh4a phOf4 phStart4; rw [fsStarts4_eq]; decide +kernel

theorem phStart4_mono {a b : ℕ} (hab : a ≤ b) (hb : b ≤ 55) : phStart4 a ≤ phStart4 b := by
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

end G6_FRSoundness4P4aDF

section G6_FRSoundness4P4bRS

-- New for `flock-recursive` (BLUEPRINT revision 4.1, A.10 rows E4 end and RS0, §5.2; stage P4b):
-- RS0's column checks at `seq4` (326), E4 end's claim as RS claim 4, the pending claims' doom.
-- The 3.x templates are `FRSoundnessFrRS0`, `FRSoundnessFrRS` (`gL`, `sL`, `DRS0`) and
-- `FRSoundnessFrPend`.

/-!
# RS0 at revision 4.1 (P4b)

RS0 absorbs at 326 the 128 slices of each claim (`sliceL4`); `finRS` computes `α_j` from them
(`alphaL4`) and the finals bind each `α_j` where it is used (`okRS4`). Here, at the chain's kind
`κ : CKind` (`kindOfC`):

* **`gL4 kf κ es j`**: claim `j`'s weight on level 0's `2^(m − 7)` cells, `eq(p_j, ·)`, times the
  node's **kind factor** for claim 2 (revision 3.16). The kind factor `kf ν β t` (block `t`'s
  `B_β(t) = Σ_i β^i Ind_i(t)`, `β` L3β's challenge at 98) is a parameter: its indicators are the
  revision 4.1 node's block kinds, S-E's (S-G13 F3). A segment's is `1`.
* **`trueL4`** (the same inner weights on the true slices of `f⁽⁰⁾`'s bit planes `rsQ4`),
  **`PendBad4 ok`** (a claim's binding fails at its true value), **`DPend4`** (E4 end's doom: far,
  a false public cell, or `PendBad4`), **`DRS0_4`** (RS0's: far, a false public cell, a false
  slice). Far and the public cells are parameters (`F0`, `Pub`, read before 3): the level-0 word's
  distance is T4's, the node's public cells are S-E's.
* **`habs_RS0_4`**: `DPend4` before RS0's absorb gives `RejRS4` or `DRS0_4` after it
  (`rs_column`); **`rejRS4_log`**; the reads.
* **`trueL4_three`**/**`pendE4_pendBad4`**: on a node, RS claim 4's true value is `ẑ(r′)` at E4's
  `ncR κ` challenges, so E's pending doom (`PendE4`) is `PendBad4` at claim 4.
-/

namespace FR.Snd.P4b
open RecursionFast FR.Merkle FR.Rev4 Finset

set_option linter.constructorNameAsVariable false

theorem CKind.m_le (κ : CKind) : κ.m ≤ 32 := by rcases κ.m_mem with h | h | h <;> omega

theorem CKind.m_ge (κ : CKind) : 30 ≤ κ.m := by rcases κ.m_mem with h | h | h <;> omega

theorem ncR_eq (κ : NodeKind) : ncR κ = (CKind.node κ).m - 7 := rfl

/-! ## Reads of the claim points, weights and slices -/

section Congr
variable {es es' : Log}

theorem rsPtsL4_congr (h : Agree es es' 325) (κ : CKind) : rsPtsL4 κ es = rsPtsL4 κ es' := by
  have hm := CKind.m_le κ
  have hz : zPtL κ.m es = zPtL κ.m es' := by
    unfold zPtL
    exact congrArg ((List.ofFn pinnedRho).drop 1 ++ ·) (List.map_congr_left fun j hj =>
      fAt_congr h (p := 2 + 1 + j / 2) (by simp only [List.mem_range] at hj; omega) (j % 2))
  have hl : lcPtL κ.m es = lcPtL κ.m es' := by
    unfold lcPtL
    rw [List.map_congr_left fun l hl => rch_congr h (b := 69) (l := 7 + l)
        (by simp only [List.mem_range] at hl; omega),
      List.map_congr_left fun l hl => rch_congr h (b := 15) (l := 8 + l)
        (by simp only [List.mem_range] at hl; omega)]
  have hs : shPtL κ.m es = shPtL κ.m es' := by
    unfold shPtL
    rw [List.map_congr_left fun l hl => rch_congr h (b := 114) (l := κ.m - 7 + l)
        (by simp only [List.mem_range] at hl; omega),
      List.map_congr_left fun l hl => rch_congr h (b := 114) (l := l)
        (by simp only [List.mem_range] at hl; omega)]
  have he : ∀ ν : NodeKind, ePtL4 (ncR ν) es = ePtL4 (ncR ν) es' := fun ν => by
    have := (dims_le' ν).2.2.1
    unfold ePtL4
    rw [List.map_congr_left fun l hl => rch_congr h (b := 275) (l := l)
        (by simp only [List.mem_range] at hl; omega)]
  cases κ with
  | seg σ => simp only [rsPtsL4, hz, hl, hs]
  | node ν => simp only [rsPtsL4, hz, hl, hs, he ν]

theorem cwL4_congr (h : Agree es es' 326) (κ : CKind) : cwL4 κ es = cwL4 κ es' := by
  have hm := CKind.m_le κ
  have h1 : xLL es = xLL es' :=
    List.map_congr_left fun l hl => rch_congr h (by simp at hl; omega)
  have h2 : xSL4 κ es = xSL4 κ es' :=
    List.map_congr_left fun l hl => rch_congr h (by simp at hl; omega)
  have h0 : fAt es 14 0 = fAt es' 14 0 := fAt_congr h (by norm_num) 0
  unfold cwL4; rw [h0, h1, h2]

theorem sL4_congr (h : Agree es es' 327) (κ : CKind) : sL4 κ es = sL4 κ es' := by
  funext j i
  rw [sL4, sL4, rsPtsL4_congr (h.mono (by norm_num)) κ, sliceL4, sliceL4,
    msgAt_congr h (show 326 < 327 by norm_num)]

theorem alphaL4_congr (h : Agree es es' 327) (κ : CKind) : alphaL4 κ es = alphaL4 κ es' := by
  funext j; simp only [alphaL4, cwL4_congr (h.mono (by norm_num)) κ, sL4_congr h κ]

end Congr

/-! ## The claims' weights and true values -/

/-- **The kind factor at the chain's kind**: a node's `kf ν β t` with L3β's `β` (98); `1` on a
segment. -/
def kfT4 (kf : NodeKind → F → ℕ → F) (κ : CKind) (es : Log) (t : ℕ) : F :=
  match κ with
  | .node ν => kf ν (fAt es 98 0) t
  | .seg _ => 1

/-- Claim `j`'s weight on level 0's cube: `eq(p_j, cube u)`, times the kind factor for claim 2;
`0` for a segment's fourth claim. -/
noncomputable def gL4 (kf : NodeKind → F → ℕ → F) (κ : CKind) (es : Log) (j : Fin 4)
    (u : Fin (2 ^ (κ.m - 7))) : F :=
  if j.val < (rsPtsL4 κ es).length then
    eqPts ((rsPtsL4 κ es).getD j []) (bitsL ((rsPtsL4 κ es).getD j []).length u) *
      (if j.val = 1 then kfT4 kf κ es (u.val / 2 ^ 7) else 1) else 0

/-- **The bit planes of `f⁽⁰⁾`** (`Q_i(u)` is bit `i` of `f[u]`). -/
noncomputable def rsQ4 (R : FSrc) (L es : Log) (ℓ : ℕ) : Fin 128 → Fin (2 ^ ℓ) → F :=
  fun i u => unpack (R.fz L es u) i

/-- **Claim `j`'s true value**: the inner weights on the true slices `Σ_u g_j(u) Q_i(u)`. -/
noncomputable def trueL4 (R : FSrc) (kf : NodeKind → F → ℕ → F) (κ : CKind) (L es : Log)
    (j : Fin 4) : F :=
  ∑ i : Fin 128, cwL4 κ es j i *
    ∑ u, gL4 kf κ es j u * algebraMap F F (rsQ4 R L es (κ.m - 7) i u)

/-- **The RS0 truth** (A.10 RS0): every claim's partials are the true bit-plane claims. -/
def truthRS0_4 (R : FSrc) {J ℓ : ℕ} (L es : Log) (g : Fin J → Fin (2 ^ ℓ) → F)
    (s : Fin J → Fin 128 → F) : Prop :=
  ∀ j i, s j i = ∑ u, g j u * algebraMap F F (rsQ4 R L es ℓ i u)

theorem gL4_congr (kf : NodeKind → F → ℕ → F) {es es' : Log} (h : Agree es es' 325) (κ : CKind) :
    gL4 kf κ es = gL4 kf κ es' := by
  have hk : kfT4 kf κ es = kfT4 kf κ es' := by
    funext t
    cases κ with
    | seg σ => rfl
    | node ν =>
      show kf ν (fAt es 98 0) t = kf ν (fAt es' 98 0) t
      rw [fAt_congr h (show 98 < 325 by norm_num)]
  funext j u; simp only [gL4, rsPtsL4_congr h κ, hk]

theorem rsQ4_same (R : FSrc) {L es L' es' : Log} {p : ℕ} (h : R.Sm L es L' es' p) (hp : 3 ≤ p)
    (ℓ : ℕ) : rsQ4 R L es ℓ = rsQ4 R L' es' ℓ := by
  funext i u; simp only [rsQ4, R.fz_same h hp]

theorem trueL4_same (R : FSrc) (kf : NodeKind → F → ℕ → F) {L es L' es' : Log} {p : ℕ}
    (h : R.Sm L es L' es' p) (hp : 326 ≤ p) (κ : CKind) :
    trueL4 R kf κ L es = trueL4 R kf κ L' es' := by
  funext j
  simp only [trueL4, cwL4_congr ((R.agree h).mono hp) κ,
    gL4_congr kf ((R.agree h).mono (by omega)) κ, rsQ4_same R h (by omega)]

/-! ## The pending claims and RS0's doom -/

section Bind
variable (R : FSrc) (kf : NodeKind → F → ℕ → F) (ok : CKind → Log → ℕ → F → Prop)
  (F0 Pub : Log → Log → Prop)

/-- The bindings read the log before RS0's absorb. -/
def OkReads4 : Prop := ∀ κ es es', Agree es es' 326 → ok κ es = ok κ es'

/-- **A pending claim is false**: some claim's binding fails at its true value. -/
def PendBad4 (L es : Log) : Prop :=
  ∃ j : Fin 4, j.val < (rsPtsL4 (kindOfC es) es).length ∧
    ¬ ok (kindOfC es) es j (trueL4 R kf (kindOfC es) L es j)

/-- **The doom before RS0** (E4 end's): far, a public cell false, or a pending claim false. -/
def DPend4 (L es : Log) : Prop := F0 L es ∨ ¬ Pub L es ∨ PendBad4 R kf ok L es

/-- **RS0's doom** at its absorb: far, a public cell false, or a slice false. -/
def DRS0_4 (L es : Log) : Prop :=
  F0 L es ∨ ¬ Pub L es ∨
    ¬ truthRS0_4 R L es (gL4 kf (kindOfC es) es) (sL4 (kindOfC es) es)

end Bind

section BindLemmas
variable {R : FSrc} {kf : NodeKind → F → ℕ → F} {ok : CKind → Log → ℕ → F → Prop}
  {F0 Pub : Log → Log → Prop}

theorem pendBad4_reads (hok : OkReads4 ok) : ReadsS R 326 (PendBad4 R kf ok) :=
  fun L es L' es' h1 h2 h => by
    have hk := kindOfC_congr ((R.agree h).mono (by norm_num))
    simp only [PendBad4, hk, rsPtsL4_congr ((R.agree h).mono (by norm_num)),
      hok _ es es' (R.agree h), trueL4_same R kf h le_rfl]

theorem dPend4_reads (hok : OkReads4 ok) (hF : ReadsS R 3 F0) (hP : ReadsS R 3 Pub) :
    ReadsS R 326 (DPend4 R kf ok F0 Pub) :=
  (hF.mono (by norm_num)).or ((hP.mono (by norm_num)).not.or (pendBad4_reads hok))

theorem rejRS4_log (hok : OkReads4 ok) : RejLog4 (RejRS4 ok) := by
  refine rejLog4_of (q := 327) (by norm_num) (fun _ _ h => h.1) (fun L es L' es' h1 h2 h => ?_)
    (by simpa using (p4b_abs).2.2.2.1)
  have hk := kindOfC_congr (h.mono (by norm_num))
  simp only [RejRS4, hk, rsPtsL4_congr (h.mono (by norm_num)), hok _ es es' (h.mono (by norm_num)),
    alphaL4_congr h]
  exact and_congr_left fun _ => ⟨fun _ => h2, fun _ => h1⟩

/-- **`habs` at RS0's absorb** (A.10 RS0, `rs_column`): if a pending claim is false before the
absorb, then after it a binding fails at the slices' value (`RejRS4`) or a slice is false
(`DRS0_4`). Far words and false public cells carry over. -/
theorem habs_RS0_4 (hok : OkReads4 ok) (hF : ReadsS R 3 F0) (hP : ReadsS R 3 Pub) {L es : Log}
    (x : ByteArray × Digest) (hl : es.length = 326) (hd : DPend4 R kf ok F0 Pub L es) :
    RejRS4 ok L (es ++ [x]) ∨ DRS0_4 R kf F0 Pub L (es ++ [x]) := by
  have hag : Agree (es ++ [x]) es 326 := hl ▸ agree_append es [x] le_rfl
  have hS : R.Sm L (es ++ [x]) L es 326 := R.ofAgree L hag
  have hk : kindOfC (es ++ [x]) = kindOfC es := kindOfC_congr (hag.mono (by norm_num))
  rcases hd with h | h | ⟨j, hj, hn⟩
  · exact .inr (.inl ((hF.append L es [x] (by omega)).mpr h))
  · exact .inr (.inr (.inl fun h' => h ((hP.append L es [x] (by omega)).mp h')))
  by_cases hr : RejRS4 ok L (es ++ [x])
  · exact .inl hr
  refine .inr (.inr (.inr ?_))
  have hok' : ok (kindOfC es) (es ++ [x]) = ok (kindOfC es) es := hok _ _ _ hag
  have hpts := rsPtsL4_congr (hag.mono (by norm_num)) (kindOfC es)
  have hα : ok (kindOfC es) es j (alphaL4 (kindOfC es) (es ++ [x]) j) := by
    by_contra hc
    exact hr ⟨by simp; omega, j, by rw [hk, hpts]; exact hj, by rw [hk, hok']; exact hc⟩
  have hne : alphaL4 (kindOfC es) (es ++ [x]) j ≠ trueL4 R kf (kindOfC es) L (es ++ [x]) j := by
    rw [trueL4_same R kf hS le_rfl]; intro he; exact hn (he ▸ hα)
  have hcol := rs_column (c := fun i => cwL4 (kindOfC es) (es ++ [x]) j i)
    (s := fun i => sL4 (kindOfC es) (es ++ [x]) j i)
    (t := fun i => ∑ u, gL4 kf (kindOfC es) (es ++ [x]) j u *
      algebraMap F F (rsQ4 R L (es ++ [x]) ((kindOfC es).m - 7) i u)) rfl
    (fun he => hne (by unfold alphaL4 trueL4; exact he.symm))
  rw [hk]
  intro ht
  exact hcol (funext fun i => sub_eq_zero.mpr (ht j i))

end BindLemmas

/-! ## E4 end's claim is RS claim 4 -/

theorem ePtL4_eq (κ : NodeKind) (es : Log) : ePtL4 (ncR κ) es = rPt4 κ es := by
  unfold ePtL4 rPt4 rchs2; exact List.map_congr_left fun _ _ => rfl

/-- **RS claim 4's true value is `ẑ(r′)`** on a node (`pack_unpack`, `eqPts_eq`). -/
theorem trueL4_three (R : FSrc) (kf : NodeKind → F → ℕ → F) (κ : NodeKind) (L es : Log) :
    trueL4 R kf (.node κ) L es 3 = mle (zCG R (ncR κ) L es) (ptOf (ncR κ) (rPt4 κ es)) := by
  have hlen : (rsPtsL4 (.node κ) es).length = 4 := rsPtsL4_length _ _
  have hlr : (rPt4 κ es).length = ncR κ := rPt4_length κ es
  have h3 : ((3 : Fin 4) : ℕ) = 3 := rfl
  have hg : ∀ u : Fin (2 ^ ((CKind.node κ).m - 7)),
      gL4 kf (.node κ) es 3 u = eqPts (rPt4 κ es) (bitsL (ncR κ) u) := by
    intro u
    rw [gL4, h3, ite_pos' (by rw [hlen]; norm_num), ite_neg' (show (3 : ℕ) ≠ 1 by norm_num),
      mul_one]
    simp only [rsPtsL4, List.getD_eq_getElem?_getD]
    rw [show ([zPtL (CKind.node κ).m es, lcPtL (CKind.node κ).m es, shPtL (CKind.node κ).m es] ++
      [ePtL4 (ncR κ) es])[3]? = some (ePtL4 (ncR κ) es) from rfl, Option.getD_some, ePtL4_eq, hlr]
  have hb : ∀ i : Fin 128, bb i = bitBasis i := fun i => by
    simp only [bb, Nat.mod_eq_of_lt i.isLt]
  have hl : trueL4 R kf (.node κ) L es 3 =
      ∑ u ∈ range (2 ^ ncR κ), eqPts (rPt4 κ es) (bitsL (ncR κ) u) * R.fz L es u := by
    unfold trueL4
    rw [← Fin.sum_univ_eq_sum_range (fun u => eqPts (rPt4 κ es) (bitsL (ncR κ) u) * R.fz L es u)]
    simp only [hg, h3, cwL4, cwF, hb, Algebra.algebraMap_self, RingHom.id_apply, mul_sum]
    rw [sum_comm]
    refine sum_congr rfl fun u _ => ?_
    rw [← pack_unpack (R.fz L es u), mul_sum]
    refine sum_congr rfl fun i _ => ?_
    simp only [rsQ4]; ring
  have hr : mle (zCG R (ncR κ) L es) (ptOf (ncR κ) (rPt4 κ es)) =
      ∑ u ∈ range (2 ^ ncR κ), eqPts (rPt4 κ es) (bitsL (ncR κ) u) * R.fz L es u := by
    rw [mle, ← Fin.sum_univ_eq_sum_range (fun u => eqPts (rPt4 κ es) (bitsL (ncR κ) u) * R.fz L es u)]
    refine sum_congr rfl fun u _ => ?_
    rw [eqPts_eq _ _ hlr (by simp [bitsL]), ptOf_bitsL u.val (ncR κ) u.isLt]
    rfl
  rw [hl, hr]

/-- **E's pending doom is RS0's `PendBad4` at claim 4** (with RS0's bindings `okRS4`). -/
theorem pendE4_pendBad4 {R : FSrc} {kf : NodeKind → F → ℕ → F} {oZ oLc oSh : CKind → Log → F → Prop}
    {L es : Log} (h : PendE4 R L es) : PendBad4 R kf (okRS4 oZ oLc oSh) L es := by
  obtain ⟨κ, hk, -, hne⟩ := h
  refine ⟨3, by rw [hk, rsPtsL4_length]; simp [CKind.isNode], ?_⟩
  rw [hk]
  show ¬ okE4 es (trueL4 R kf (.node κ) L es 3)
  rw [trueL4_three]; exact hne

/-- RS0's bindings read before 326 when Z's, Lc's and Sh's do. -/
theorem okRS4_reads {oZ oLc oSh : CKind → Log → F → Prop}
    (hZ : ∀ κ es es', Agree es es' 326 → oZ κ es = oZ κ es')
    (hL : ∀ κ es es', Agree es es' 326 → oLc κ es = oLc κ es')
    (hSh : ∀ κ es es', Agree es es' 326 → oSh κ es = oSh κ es') : OkReads4 (okRS4 oZ oLc oSh) := by
  intro κ es es' h
  have he : okE4 es = okE4 es' := by
    funext v; simp only [okE4, msgAt_congr h (show 325 < 326 by norm_num)]
  funext j v
  rcases j with _ | _ | _ | j
  · simp only [okRS4, hZ κ es es' h]
  · simp only [okRS4, hL κ es es' h]
  · simp only [okRS4, hSh κ es es' h]
  · simp only [okRS4, he]

/-! ## RS1's count (the core of `hfin` at RS1, 327 … 330) -/

open Classical in
/-- **RS1's count from a false RS0 truth** (A.10 RS1, `rs1_joint`): if some slice claim is wrong,
at most `(7 + J′)·|F|^7` of the draws `(r″, κ)` make the batched switched claim equal its true
value. The frame at `fsRanges4`'s `(326, 4)` is the composition's (T4's `hfin_rs1`). -/
theorem rs1_count4 {J' ℓ : ℕ} {R : FSrc} {L es : Log} {g : Fin (J' + 1) → Fin (2 ^ ℓ) → F}
    {s : Fin (J' + 1) → Fin 128 → F} (h : ¬ truthRS0_4 R L es g s) :
    (univ.filter fun p : (Fin 7 → F) × F =>
      ∑ j, p.2 ^ j.val * rsT s p.1 j = ∑ j, p.2 ^ j.val * rsTruth (rsQ4 R L es ℓ) g p.1 j).card ≤
      (7 + J') * Fintype.card F ^ 7 := by
  refine rs1_joint _ (fun i u => unpack_boolean _ _) g s ?_
  unfold truthRS0_4 at h
  push Not at h
  obtain ⟨j, i, hji⟩ := h
  exact ⟨j, fun hz => hji (sub_eq_zero.mp (congrFun hz i))⟩

/-! ## Controls -/

/-- (+) With the bindings at the true values, no pending claim is false. -/
theorem not_pendBad4_true (R : FSrc) (kf : NodeKind → F → ℕ → F) (L es : Log) :
    ¬ PendBad4 R kf (fun κ _ j v => ∀ hj : j < 4, v = trueL4 R kf κ L es ⟨j, hj⟩) L es := by
  rintro ⟨j, -, hn⟩; exact hn fun _ => rfl

/-- (−) A binding that refuses every value is pending-false, and rejected after RS0. -/
theorem pendBad4_false (R : FSrc) (kf : NodeKind → F → ℕ → F) (L es : Log) :
    PendBad4 R kf (fun _ _ _ _ => False) L es :=
  ⟨0, by rw [rsPtsL4_length]; split_ifs <;> norm_num, not_false⟩

theorem rejRS4_false (L es : Log) (hl : 327 ≤ es.length) : RejRS4 (fun _ _ _ _ => False) L es :=
  ⟨hl, 0, by rw [rsPtsL4_length]; split_ifs <;> norm_num, not_false⟩

/-- (+) With RS0's truth, a claim's slice value is its true value. -/
theorem alphaL4_true {R : FSrc} {kf : NodeKind → F → ℕ → F} {L es : Log} {κ : CKind}
    (h : truthRS0_4 R L es (gL4 kf κ es) (sL4 κ es)) (j : Fin 4) :
    alphaL4 κ es j = trueL4 R kf κ L es j := by
  unfold alphaL4 trueL4; exact sum_congr rfl fun i _ => by rw [h j i]

/-- (−) Zero slices give every claim the value `0`. -/
theorem alphaL4_zero {κ : CKind} {es : Log} (h : ∀ j i, sliceL4 es j i = 0) (j : Fin 4) :
    alphaL4 κ es j = 0 := by
  unfold alphaL4 sL4; exact sum_eq_zero fun i _ => by split_ifs <;> simp [h]

/-- (+) A segment's kind factor is `1` (it has no node kinds). -/
theorem kfT4_seg (kf : NodeKind → F → ℕ → F) (σ : SegKind) (es : Log) (t : ℕ) :
    kfT4 kf (.seg σ) es t = 1 := rfl

end FR.Snd.P4b

end G6_FRSoundness4P4bRS

section G6_FRSoundness4P4aT

-- New for `flock-recursive` (BLUEPRINT revision 4.1, A.10 S2 → RS0; stage P4a pass 4 (P4d)):
-- 3.x's `trueL_two` (`FRSoundnessFrS`) at P4b's `trueL4`.

/-!
# S's claim into RS0 at revision 4.1

* **`trueL4_two`**: P4b's `trueL4` at RS claim 3 (index 2, the Sh claim at `shPtL`) is `zS2`, `ẑ`
  at S2's point `(r_blk, r_pos)`, when the witness `zw` is the unpacked `f⁽⁰⁾` of P4b's source
  (`WitOf`: at X4, `zw := T4.zW` and `R.fz := fF (kindOfC es)`, so it holds by `rfl`).
* **`pendS4_pendBad4`**: S2's doom at its end is RS0's `PendBad4` at claim 3 (3.x's
  `okF_pendS`), through `endS4`.
-/

namespace FR.Snd.P4a
open RecursionFast FR.Merkle Finset FR.Impl

set_option linter.constructorNameAsVariable false

/-- **The witness is the unpacked `f⁽⁰⁾` of P4b's source** at the log's kind. -/
def WitOf (R : P4b.FSrc) (zw : Wit) : Prop :=
  ∀ L es b, zw (kindOfC es) L es b = unpack (R.fz L es (b / 128)) ⟨b % 128, Nat.mod_lt _ (by norm_num)⟩

theorem rpL_length4 (κ : CKind) (es : Log) : (rpL κ es).length = 10 := by simp [rpL]

/-- **RS claim 3's true value is `ẑ` at S2's point** (3.x's `trueL_two`). -/
theorem trueL4_two (R : P4b.FSrc) (kf : Rev4.NodeKind → F → ℕ → F) {zw : Wit} (hzw : WitOf R zw)
    (L es : Log) : P4b.trueL4 R kf (kindOfC es) L es 2 = zS2 zw L es := by
  unfold zS2
  have hzw' := fun b => hzw L es b
  revert hzw'
  generalize kindOfC es = κ
  intro hzw'
  have hm : κ.m = nbC κ + 14 := by unfold nbC; rcases κ.m_mem with h | h | h <;> omega
  have hP0 : κ.m - 7 = nbC κ + 7 := by omega
  set xS := P4b.xSL4 κ es
  set sP := shPtL κ.m es
  have hxS : xS.length = 7 := by simp [xS, P4b.xSL4]
  have hsP : sP.length = nbC κ + 7 := by simp [sP, shPtL]; omega
  have hcw : ∀ i : Fin 128, P4b.cwL4 κ es ((2 : Fin 4) : ℕ) i = eqAtR (ptOf 7 xS) i := by
    intro i
    rw [P4b.cwL4, show ((2 : Fin 4) : ℕ) = 2 from rfl, cwF]
    change (eqTab xS.toArray).getD i 0 = _
    rw [eqTab_getD _ (by simp [hxS]), List.size_toArray, hxS, eqBits, bitSel,
      eqAtR, ← Fin.prod_univ_eq_prod_range]
    refine prod_congr rfl fun l _ => ?_
    simp [ptOf, Array.getD_eq_getD_getElem?, List.getD_eq_getElem?_getD]
  have hg : ∀ u : Fin (2 ^ (κ.m - 7)), P4b.gL4 kf κ es 2 u = eqAtR (ptOf (κ.m - 7) sP) u := by
    intro u
    have hl : (P4b.rsPtsL4 κ es).getD 2 [] = sP := by cases κ <;> rfl
    have h2 : (2 : ℕ) < (P4b.rsPtsL4 κ es).length := by
      rw [P4b.rsPtsL4_length]; split_ifs <;> norm_num
    have h2' : ((2 : Fin 4) : ℕ) = 2 := rfl
    rw [P4b.gL4, h2', if_pos h2, if_neg (show (2 : ℕ) ≠ 1 by norm_num), mul_one, hl,
      eqPts_eq _ _ (hsP.trans hP0.symm) (by simp [bitsL, hsP, hP0]), hsP, ← hP0,
      ptOf_bitsL u.val _ u.isLt, eq_cube_eqAtR]
  have hq : ∀ (i : Fin 128) (u : Fin (2 ^ (κ.m - 7))),
      algebraMap F F (P4b.rsQ4 R L es (κ.m - 7) i u) = zw κ L es (i.val + 2 ^ 7 * u.val) := by
    intro i u
    have h1 : (i.val + 2 ^ 7 * u.val) / 128 = u.val := by have := i.isLt; omega
    have h2 : (i.val + 2 ^ 7 * u.val) % 128 = i.val := by have := i.isLt; omega
    simp only [P4b.rsQ4, hzw', Algebra.algebraMap_self, RingHom.id_apply, h1]
    congr 2; exact Fin.ext h2.symm
  have step1 : P4b.trueL4 R kf κ L es 2 = ∑ u ∈ range (2 ^ (nbC κ + 7)), ∑ i ∈ range (2 ^ 7),
      eqAtR (ptOf 7 xS) i * eqAtR (ptOf (nbC κ + 7) sP) u * zw κ L es (i + 2 ^ 7 * u) := by
    unfold P4b.trueL4
    simp only [hcw, hg, hq, mul_sum]
    rw [sum_comm, hP0]
    rw [Fin.sum_univ_eq_sum_range (fun y => ∑ x : Fin 128, eqAtR (ptOf 7 xS) x *
      (eqAtR (ptOf (nbC κ + 7) sP) y * zw κ L es (x + 2 ^ 7 * y)))]
    refine sum_congr rfl fun y _ => ?_
    rw [Fin.sum_univ_eq_sum_range (fun x => eqAtR (ptOf 7 xS) x *
      (eqAtR (ptOf (nbC κ + 7) sP) y * zw κ L es (x + 2 ^ 7 * y)))]
    exact sum_congr rfl fun x _ => by ring
  have hP7 : ptOf 7 (xS ++ sP) = ptOf 7 xS := by
    funext l; simp only [ptOf, List.getD_eq_getElem?_getD,
      List.getElem?_append_left (show l.val < xS.length by rw [hxS]; exact l.isLt)]
  have hPd : (xS ++ sP).drop 7 = sP := by rw [List.drop_left' hxS]
  have step2 : P4b.trueL4 R kf κ L es 2 = ∑ b ∈ range (2 ^ (14 + nbC κ)),
      eqAtR (ptOf (14 + nbC κ) (xS ++ sP)) b * zw κ L es b := by
    rw [step1, show 14 + nbC κ = 7 + (nbC κ + 7) by omega, sum_eqAtR_split, hP7, hPd]
  rw [step2, sum_eqAtR_split]
  have hD : (xS ++ sP).drop 14 = rbL κ es := by
    rw [show (14 : ℕ) = 7 + 7 from rfl, ← List.drop_drop, hPd]
    simp only [sP, shPtL]
    rw [List.drop_left' (by simp)]; rfl
  have hpre : xS ++ (List.range 3).map (fun l => rch 114 es (κ.m - 7 + l)) = rpL κ es := by
    rw [rpL, show (10 : ℕ) = 7 + 3 from rfl, List.range_add, List.map_append, List.map_map]
    refine congrArg₂ _ rfl (List.map_congr_left fun l _ => ?_)
    simp only [Function.comp_apply]; congr 1; omega
  have h14 : ptOf 14 (xS ++ sP) = ptOf 14 (rpL κ es ++ [0, 0, 0, 0]) := by
    have he : xS ++ sP = (rpL κ es ++ [0, 0, 0, 0]) ++ (List.range (κ.m - 14)).map (rch 114 es) := by
      rw [← hpre]; simp only [sP, shPtL, List.append_assoc]; rfl
    rw [he]; funext l
    simp only [ptOf, List.getD_eq_getElem?_getD, List.getElem?_append_left
      (show l.val < (rpL κ es ++ [0, 0, 0, 0]).length by simp [rpL_length4])]
  have hQ10 : ptOf 10 (rpL κ es ++ [0, 0, 0, 0]) = ptOf 10 (rpL κ es) := by
    funext l; simp only [ptOf, List.getD_eq_getElem?_getD,
      List.getElem?_append_left (show l.val < (rpL κ es).length by
        rw [rpL_length4]; exact l.isLt)]
  have hQd : (rpL κ es ++ [0, 0, 0, 0]).drop 10 = [0, 0, 0, 0] :=
    List.drop_left' (rpL_length4 κ es)
  rw [hD, h14]
  have inner : ∀ y ∈ range (2 ^ nbC κ), ∑ x ∈ range (2 ^ 14),
      eqAtR (ptOf 14 (rpL κ es ++ [0, 0, 0, 0])) x * eqAtR (ptOf (nbC κ) (rbL κ es)) y *
        zw κ L es (x + 2 ^ 14 * y) = ∑ q ∈ range (2 ^ 10),
      eqAtR (ptOf (nbC κ) (rbL κ es)) y * eqAtR (ptOf 10 (rpL κ es)) q * zNodeC zw κ L es y q := by
    intro y _
    simp only [mul_assoc]
    rw [show (14 : ℕ) = 10 + 4 from rfl, sum_eqAtR_split, hQ10, hQd]
    rw [sum_eq_single 0]
    · simp only [eqAtR_zeros4 (show 0 < 16 by norm_num), if_true, mul_one, mul_zero, add_zero]
      refine sum_congr rfl fun q _ => ?_
      simp only [zNodeC, show y * 2 ^ 14 + q = q + 2 ^ (10 + 4) * y by ring]
      ring
    · intro h hh h0
      rw [eqAtR_zeros4 (mem_range.1 hh), if_neg h0]
      simp
    · intro h; exact absurd (mem_range.2 (by norm_num)) h
  rw [sum_congr rfl inner, sum_comm]

/-- **At S2's end its doom is RS0's `PendBad4` at claim 3** (3.x's `okF_pendS`): the Sh binding
`oSh4` fails at claim 3's true value. -/
theorem pendS4_pendBad4 (R : P4b.FSrc) (kf : Rev4.NodeKind → F → ℕ → F)
    {oZ oLc : CKind → Log → F → Prop} {wN : CKind → Log → ℕ → ℕ → F} {zw : Wit}
    {wNS : CKind → Log → F} (hzw : WitOf R zw) {L es : Log}
    (hNS : (kindOfC es).isNode = true → wNS (kindOfC es) es =
      ∑ q ∈ range (2 ^ 10), ∑ y ∈ range (2 ^ nbC (kindOfC es)),
        eqAtR (ptOf (nbC (kindOfC es)) (rbL (kindOfC es) es)) y *
          eqAtR (ptOf 10 (rpL (kindOfC es) es)) q * wN (kindOfC es) es y q)
    (hL : (kindOfC es).isNode = false → lastL es < 2 ^ nbC (kindOfC es))
    (h : D2S wN zw L es) (hl : 170 ≤ es.length) :
    P4b.PendBad4 R kf (P4b.okRS4 oZ oLc (oSh4 wNS)) L es := by
  refine ⟨2, by rw [P4b.rsPtsL4_length]; split_ifs <;> norm_num, fun ho => endS4 hNS hL h hl ?_⟩
  have ho' : oSh4 wNS (kindOfC es) es (P4b.trueL4 R kf (kindOfC es) L es 2) := ho
  rwa [trueL4_two R kf hzw] at ho'

end FR.Snd.P4a

end G6_FRSoundness4P4aT

section G6_FRSoundness4P4aRS

-- New for `flock-recursive` (BLUEPRINT revision 4.1, A.10 Z3 → RS0, L3β → RS0, E4 end; stage P4a
-- pass 5 (P4e)): 3.x's `trueL_zero`/`pendZ_pendBad` (`FRSoundnessFrBind`), `trueL_one`/`zfL_leaf`/
-- `pendLc_pendBad` (`FRSoundnessFrZM`) and `trueL_node` (`FRSoundnessFrLN`) at P4b's `trueL4`.

/-!
# The pending Z and Lc claims into RS0 at revision 4.1

With the witness the unpacked `f⁽⁰⁾` of P4b's source (`WitOf`):

* **`trueL4_zero`**: RS claim 1's true value is `P^z(λ)` at Z1's point (the c-claim's true value),
  so **`pendZ4_pendBad4`**: Z's pending doom `PendZ` is RS0's `PendBad4` at claim 1 (binding `oZ`).
* **`trueL4_one`**: RS claim 2's true value is the kind-weighted `ẑ(r_k, r_blk)` (P4b's kind factor
  `kfT4`); **`zfL_eq4`**: a kind's true value `z̄̃_k(r_k)` on the cube.
* **`oLc4`**: claim 2's binding `v = v_β` (`finLc` (iii), every kind; 3.x's `oLcV`).
* A segment (`SegInd`: its indicator is `chain` everywhere): **`pendLc4_pendBad4`**.
* A node (**`KfInd`**: the kind factor is `Σ_i β^i Ind_{i+1}`, `finLc`'s `v_i` order): **`trueL4_node`**
  (claim 2's true value is the true batch), **`pendLcN4_pendBad4`**.
* **`pendF4a_pendBad4`**: phase 12's pending dooms (Z, Lc on both kinds, S2) are `PendBad4` from
  170 on; **`dF4a12_pendBad4`**: phase 12's doom is `BgA` or `PendBad4` (E4 end's `DPend4`, with
  P4b's `pendE4_pendBad4`).
-/

namespace FR.Snd.P4a
open RecursionFast FR.Merkle Finset FR.Impl

set_option linter.constructorNameAsVariable false

/-! ## RS claim 1 -/

theorem zZ_eq4 (zw : Wit) (ℓ : ℕ) (κ : CKind) (L es : Log) (σ : Fin 64) (u : Fin (2 ^ ℓ)) :
    zZ zw ℓ κ L es σ u = zw κ L es (σ.val + 64 * u.val) := by
  simp only [zZ, zBk, pAt]
  congr 1
  have := Nat.div_add_mod u.val 256
  norm_num
  omega

/-- (`rw`, not `rfl`: the kernel's `rfl` unfolds `eqZS` first, 1.1 s.) -/
theorem cwF_zero (lam : F) (xL xS : List F) (i : ℕ) :
    cwF lam xL xS 0 i = (eqZS lam (pinnedRho 0)).getD i 0 := by
  rw [cwF]

theorem cwF_one (lam : F) (xL xS : List F) (i : ℕ) :
    cwF lam xL xS 1 i = (eqTab xL.toArray).getD i 0 := by
  rw [cwF]

/-- RS claim 1's inner weight: the Lagrange weight of the low 6 bits times `eq(ρ₁, ·)` at bit 6. -/
theorem cwL4_zero (κ : CKind) (es : Log) {σ y : ℕ} (hσ : σ < 64) (hy : y < 2) :
    P4b.cwL4 κ es 0 (σ + 64 * y) = lagrangeWeight sNodeF (lamL es) ⟨σ, hσ⟩ *
      eqAtR (ptOf 1 [pinnedRho 0]) y := by
  rw [P4b.cwL4, cwF_zero, ← cwF_zero (fAt es 14 0) (xLL es) (xSL .N30 es)]
  exact cwL_zero .N30 es hσ hy

theorem zPtL_length4 (κ : CKind) (es : Log) : (zPtL κ.m es).length = κ.m - 7 := by
  have := κ.m_mem; simp only [zPtL, List.length_append, List.length_drop, List.length_ofFn,
    List.length_map, List.length_range]; omega

theorem zrL_drop4 (es : Log) : (zrL es).drop 1 = zPtL (kindOfC es).m es := by
  simp only [zrL, zPtL]
  rw [List.drop_append_of_le_length (by simp)]

/-- **RS claim 1's true value is `P^z(λ)` at Z1's point** (3.x's `trueL_zero`). -/
theorem trueL4_zero (R : P4b.FSrc) (kf : Rev4.NodeKind → F → ℕ → F) {zw : Wit} (hzw : WitOf R zw)
    (L es : Log) : P4b.trueL4 R kf (kindOfC es) L es 0 = (pzT zw L es).eval (lamL es) := by
  have hzd := zrL_drop4 es
  have hzw' := fun b => hzw L es b
  simp only [pzT, pzPoly, Polynomial.eval_finset_sum, Polynomial.eval_mul, Polynomial.eval_C,
    skipExt_eval]
  revert hzw'
  generalize kindOfC es = κ at hzd ⊢
  intro hzw'
  have hm := κ.m_mem
  have hℓ : mC 6 κ = 1 + (κ.m - 7) := by unfold mC; omega
  set zr := zrL es
  set zP := zPtL κ.m es
  have hzP : zP.length = κ.m - 7 := zPtL_length4 κ es
  have hg : ∀ u : Fin (2 ^ (κ.m - 7)), P4b.gL4 kf κ es 0 u = eqAtR (ptOf (κ.m - 7) zP) u := by
    intro u
    have hl : (P4b.rsPtsL4 κ es).getD 0 [] = zP := by cases κ <;> rfl
    have h0 : (0 : ℕ) < (P4b.rsPtsL4 κ es).length := by
      rw [P4b.rsPtsL4_length]; split_ifs <;> norm_num
    rw [P4b.gL4, Fin.val_zero, if_pos h0, if_neg (show (0 : ℕ) ≠ 1 by norm_num), mul_one, hl,
      eqPts_eq _ _ hzP (by simp [bitsL, hzP]), hzP, ptOf_bitsL u.val _ u.isLt, eq_cube_eqAtR]
  have hq : ∀ (i : Fin 128) (u : Fin (2 ^ (κ.m - 7))),
      algebraMap F F (P4b.rsQ4 R L es (κ.m - 7) i u) = zw κ L es (i.val + 2 ^ 7 * u.val) := by
    intro i u
    have h1 : (i.val + 2 ^ 7 * u.val) / 128 = u.val := by have := i.isLt; omega
    have h2 : (i.val + 2 ^ 7 * u.val) % 128 = i.val := by have := i.isLt; omega
    simp only [P4b.rsQ4, hzw', Algebra.algebraMap_self, RingHom.id_apply, h1]
    congr 2; exact Fin.ext h2.symm
  set lw : ℕ → F := fun σ => lagrangeWeight sNodeF (lamL es) ⟨σ % 64, Nat.mod_lt _ (by norm_num)⟩
  have hL : P4b.trueL4 R kf κ L es 0 = ∑ q ∈ range (2 ^ (κ.m - 7)), ∑ y ∈ range 2, ∑ σ ∈ range 64,
      lw σ * eqAtR (ptOf 1 [pinnedRho 0]) y * eqAtR (ptOf (κ.m - 7) zP) q *
        zw κ L es (σ + 64 * y + 2 ^ 7 * q) := by
    unfold P4b.trueL4
    simp only [hg, hq, mul_sum, Fin.val_zero]
    rw [sum_comm]
    rw [Fin.sum_univ_eq_sum_range (fun q => ∑ i : Fin 128, P4b.cwL4 κ es 0 i *
      (eqAtR (ptOf (κ.m - 7) zP) q * zw κ L es (i + 2 ^ 7 * q)))]
    refine sum_congr rfl fun q _ => ?_
    rw [Fin.sum_univ_eq_sum_range (fun i => P4b.cwL4 κ es 0 i *
      (eqAtR (ptOf (κ.m - 7) zP) q * zw κ L es (i + 2 ^ 7 * q))), show (128 : ℕ) = 64 * 2 from rfl,
      sum_range_mul_split]
    refine sum_congr rfl fun y hy => sum_congr rfl fun σ hσ => ?_
    rw [mem_range] at hy hσ
    rw [cwL4_zero κ es hσ hy]
    simp only [lw, Nat.mod_eq_of_lt hσ]
    ring
  have hR : ∑ u : Fin (2 ^ mC 6 κ), eq (ptOf (mC 6 κ) zr) (cube u) *
      ∑ σ : Fin 64, lagrangeWeight (fun b : Fin 64 => skipNode (Fin.castLE (by norm_num) b))
        (lamL es) σ * zZ zw (mC 6 κ) κ L es σ u =
      ∑ u ∈ range (2 ^ (1 + (κ.m - 7))), eqAtR (ptOf (1 + (κ.m - 7)) zr) u *
        ∑ σ ∈ range 64, lw σ * zw κ L es (σ + 64 * u) := by
    rw [← hℓ, ← Fin.sum_univ_eq_sum_range (fun u => eqAtR (ptOf (mC 6 κ) zr) u *
      ∑ σ ∈ range 64, lw σ * zw κ L es (σ + 64 * u))]
    refine sum_congr rfl fun u _ => ?_
    rw [eq_cube_eqAtR, ← Fin.sum_univ_eq_sum_range (fun σ => lw σ * zw κ L es (σ + 64 * u))]
    refine congrArg _ (sum_congr rfl fun σ _ => ?_)
    rw [zZ_eq4]
    simp only [lw, Nat.mod_eq_of_lt σ.isLt]
    rfl
  rw [hR, sum_eqAtR_split, hL, hzd]
  refine sum_congr rfl fun q _ => ?_
  rw [pow_one]
  refine sum_congr rfl fun y _ => ?_
  have h1 : ptOf 1 zr = ptOf 1 [pinnedRho 0] := by
    funext l; fin_cases l; simp [ptOf, zr, zrL, List.getD_eq_getElem?_getD]
  rw [h1, mul_sum]
  refine sum_congr rfl fun σ _ => ?_
  rw [show σ + 64 * y + 2 ^ 7 * q = σ + 64 * (y + 2 ^ 1 * q) by ring]
  ring_nf

/-- **Z's pending doom is RS0's `PendBad4` at claim 1** (binding `oZ`: the value is `P^z*(λ)`). -/
theorem pendZ4_pendBad4 (R : P4b.FSrc) (kf : Rev4.NodeKind → F → ℕ → F)
    {oLc oSh : CKind → Log → F → Prop} {zw : Wit} (hzw : WitOf R zw) {L es : Log}
    (h : PendZ zw L es) : P4b.PendBad4 R kf (P4b.okRS4 oZ oLc oSh) L es :=
  ⟨0, by rw [P4b.rsPtsL4_length]; split_ifs <;> norm_num, fun ho => h.2 (by
    have ho' : P4b.trueL4 R kf (kindOfC es) L es 0 = pzStar es := ho
    rw [← trueL4_zero R kf hzw, ho'])⟩

/-! ## RS claim 2 -/

theorem ptOf_rkL4 (es : Log) :
    ptOf 14 (xLL es ++ lcPtL (kindOfC es).m es) = ptOf 14 (rkL es) := by
  funext l
  fin_cases l <;> simp [ptOf, xLL, lcPtL, rkL, rchs, List.getD_eq_getElem?_getD,
    List.getElem?_append_left, List.getElem?_append_right]

theorem ptOf_rbLc4 (es : Log) :
    ptOf (qL (kindOfC es)) ((xLL es ++ lcPtL (kindOfC es).m es).drop 14) = rbLc es := by
  have hm := (kindOfC es).m_mem
  have hd : (xLL es ++ lcPtL (kindOfC es).m es).drop 14 =
      (List.range ((kindOfC es).m - 14)).map (fun l => rch 15 es (8 + l)) := by
    rw [lcPtL, ← List.append_assoc, List.drop_left' (by simp [xLL])]
  funext l
  have hl := l.isLt
  rw [hd]
  simp only [rbLc, ptOf, rZ, rchs, List.getD_eq_getElem?_getD, List.getElem?_drop,
    List.getElem?_map, List.getElem?_range (show l.val < (kindOfC es).m - 14 by unfold qL at hl; omega),
    List.getElem?_range (show 8 + l.val < mC 6 (kindOfC es) by unfold mC qL at *; omega),
    Option.map_some, Option.getD_some]

/-- **RS claim 2's true value is the kind-weighted `ẑ(r_k, r_blk)`** (3.x's `trueL_one`; the weight
`kfT4` is a node's kind factor `kf ν β t`, a segment's `1`). -/
theorem trueL4_one (R : P4b.FSrc) (kf : Rev4.NodeKind → F → ℕ → F) {zw : Wit} (hzw : WitOf R zw)
    (L es : Log) : P4b.trueL4 R kf (kindOfC es) L es 1 =
    ∑ t ∈ range (2 ^ qL (kindOfC es)), ∑ j ∈ range (2 ^ 14),
      eqAtR (ptOf 14 (rkL es)) j * eqAtR (rbLc es) t * P4b.kfT4 kf (kindOfC es) es t *
        zw (kindOfC es) L es (j + 2 ^ 14 * t) := by
  rw [← ptOf_rkL4, ← ptOf_rbLc4]
  have hzw' := fun b => hzw L es b
  revert hzw'
  generalize kindOfC es = κ
  intro hzw'
  have hm := κ.m_mem
  have hP0 : κ.m - 7 = qL κ + 7 := by unfold qL; omega
  set xL := xLL es
  set lP := lcPtL κ.m es
  have hxL : xL.length = 7 := by simp [xL, xLL]
  have hlP : lP.length = qL κ + 7 := by simp [lP, lcPtL, qL]; omega
  have hcw : ∀ i : Fin 128, P4b.cwL4 κ es ((1 : Fin 4) : ℕ) i = eqAtR (ptOf 7 xL) i := by
    intro i
    rw [P4b.cwL4, show ((1 : Fin 4) : ℕ) = 1 from rfl, cwF_one, show xLL es = xL from rfl]
    rw [eqTab_getD _ (by simp [hxL]), List.size_toArray, hxL, eqBits, bitSel,
      eqAtR, ← Fin.prod_univ_eq_prod_range]
    refine prod_congr rfl fun l _ => ?_
    simp [ptOf, Array.getD_eq_getD_getElem?, List.getD_eq_getElem?_getD]
  have hg : ∀ u : Fin (2 ^ (κ.m - 7)), P4b.gL4 kf κ es 1 u =
      eqAtR (ptOf (κ.m - 7) lP) u * P4b.kfT4 kf κ es (u.val / 2 ^ 7) := by
    intro u
    have hl : (P4b.rsPtsL4 κ es).getD 1 [] = lP := by cases κ <;> rfl
    have h1 : (1 : ℕ) < (P4b.rsPtsL4 κ es).length := by
      rw [P4b.rsPtsL4_length]; split_ifs <;> norm_num
    have h1' : ((1 : Fin 4) : ℕ) = 1 := rfl
    rw [P4b.gL4, h1', if_pos h1, if_pos rfl, hl,
      eqPts_eq _ _ (hlP.trans hP0.symm) (by simp [bitsL, hlP, hP0]),
      hlP, ← hP0, ptOf_bitsL u.val _ u.isLt, eq_cube_eqAtR]
  have hq : ∀ (i : Fin 128) (u : Fin (2 ^ (κ.m - 7))),
      algebraMap F F (P4b.rsQ4 R L es (κ.m - 7) i u) = zw κ L es (i.val + 2 ^ 7 * u.val) := by
    intro i u
    have h1 : (i.val + 2 ^ 7 * u.val) / 128 = u.val := by have := i.isLt; omega
    have h2 : (i.val + 2 ^ 7 * u.val) % 128 = i.val := by have := i.isLt; omega
    simp only [P4b.rsQ4, hzw', Algebra.algebraMap_self, RingHom.id_apply, h1]
    congr 2; exact Fin.ext h2.symm
  set g : ℕ → F := fun b => P4b.kfT4 kf κ es (b / 2 ^ 14) * zw κ L es b with hgdef
  have step1 : P4b.trueL4 R kf κ L es 1 = ∑ u ∈ range (2 ^ (qL κ + 7)), ∑ i ∈ range (2 ^ 7),
      eqAtR (ptOf 7 xL) i * eqAtR (ptOf (qL κ + 7) lP) u * g (i + 2 ^ 7 * u) := by
    unfold P4b.trueL4
    simp only [hcw, hg, hq, mul_sum]
    rw [sum_comm, hP0, Finset.sum_range]
    refine sum_congr rfl fun y _ => ?_
    rw [Finset.sum_range]
    refine sum_congr rfl fun x _ => ?_
    have hx := x.isLt
    simp only [hgdef]
    rw [show (x.val + 2 ^ 7 * y.val) / 2 ^ 14 = y.val / 2 ^ 7 by omega]
    ring
  have hP7 : ptOf 7 (xL ++ lP) = ptOf 7 xL := by
    funext l; simp only [ptOf, List.getD_eq_getElem?_getD,
      List.getElem?_append_left (show l.val < xL.length by rw [hxL]; exact l.isLt)]
  have hPd : (xL ++ lP).drop 7 = lP := by rw [List.drop_left' hxL]
  have hR : ∀ P : List F, (∑ t ∈ range (2 ^ qL κ), ∑ j ∈ range (2 ^ 14),
      eqAtR (ptOf 14 P) j * eqAtR (ptOf (qL κ) (P.drop 14)) t * P4b.kfT4 kf κ es t *
        zw κ L es (j + 2 ^ 14 * t)) = ∑ t ∈ range (2 ^ qL κ), ∑ j ∈ range (2 ^ 14),
      eqAtR (ptOf 14 P) j * eqAtR (ptOf (qL κ) (P.drop 14)) t * g (j + 2 ^ 14 * t) := fun P =>
    sum_congr rfl fun t _ => sum_congr rfl fun j hj => by
      rw [mem_range] at hj
      simp only [hgdef]
      rw [show (j + 2 ^ 14 * t) / 2 ^ 14 = t by omega]
      ring
  rw [step1, hR, ← sum_eqAtR_split 14 (qL κ) g, show 14 + qL κ = 7 + (qL κ + 7) by omega,
    sum_eqAtR_split, hP7, hPd]

/-- Kind `k`'s true value `z̄̃_k(r_k)` as a sum on the cube (3.x's `zfL_eq`). -/
theorem zfL_eq4 (M : ZLM4) (zw : Wit) (L es : Log) (k : Fin 9) : zfL M zw L es k =
    ∑ t ∈ range (2 ^ qL (kindOfC es)), ∑ j ∈ range (2 ^ 14),
      eqAtR (ptOf 14 (rkL es)) j * eqAtR (rbLc es) t * M.Ind (kindOfC es) k t *
        zw (kindOfC es) L es (j + 2 ^ 14 * t) := by
  unfold zfL zfoldK mle IndF
  simp only [eq_cube_eqAtR, zN, join, mul_sum]
  rw [← Fin.sum_univ_eq_sum_range (fun t => ∑ j ∈ range (2 ^ 14), eqAtR (ptOf 14 (rkL es)) j *
      eqAtR (rbLc es) t * M.Ind (kindOfC es) k t * zw (kindOfC es) L es (j + 2 ^ 14 * t)),
    sum_comm]
  refine sum_congr rfl fun t _ => ?_
  rw [← Fin.sum_univ_eq_sum_range (fun j => eqAtR (ptOf 14 (rkL es)) j *
      eqAtR (rbLc es) t.val * M.Ind (kindOfC es) k t.val *
        zw (kindOfC es) L es (j + 2 ^ 14 * t.val))]
  exact sum_congr rfl fun j _ => by rw [add_comm (2 ^ 14 * t.val)]; ring

/-- **Claim 2's binding** (every kind; 3.x's `oLcV`, `finLc` (iii)): `v = v_β`. -/
def oLc4 (_κ : CKind) (es : Log) (v : F) : Prop := v = vBetaL es

/-- **A segment's indicators are `chain` everywhere** (`zlm4`'s, `segInd_zlm4`). -/
def SegInd (M : ZLM4) : Prop := ∀ σ t, M.Ind (.seg σ) 0 t = 1

/-- **The kind factor is the node's indicators batched by `β`** (`finLc`'s `v_i` order: kind
`i + 1`). -/
def KfInd (M : ZLM4) (kf : Rev4.NodeKind → F → ℕ → F) : Prop :=
  ∀ ν β t, kf ν β t = ∑ i : Fin 8, β ^ i.val * M.Ind (.node ν) i.succ t

theorem segInd_zlm4 (indN : Rev4.NodeKind → Fin 9 → ℕ → F)
    (etN : Rev4.NodeKind → ℕ → Fin (2 ^ 14) → F) : SegInd (zlm4 indN etN) := fun _ _ => rfl

/-- On a segment, `z̄̃_chain(r_k)` is RS claim 2's true value. -/
theorem zfL_seg4 (R : P4b.FSrc) (kf : Rev4.NodeKind → F → ℕ → F) {M : ZLM4} (hS : SegInd M)
    {zw : Wit} (hzw : WitOf R zw) {L es : Log} (hn : (kindOfC es).isNode = false) :
    zfL M zw L es 0 = P4b.trueL4 R kf (kindOfC es) L es 1 := by
  rw [trueL4_one R kf hzw, zfL_eq4]
  obtain ⟨σ, hσ⟩ : ∃ σ, kindOfC es = .seg σ := by
    cases h : kindOfC es with
    | seg σ => exact ⟨σ, rfl⟩
    | node ν => rw [h] at hn; cases hn
  simp only [hσ, hS σ, P4b.kfT4]

/-- **A segment's pending Lc claim is RS0's `PendBad4` at claim 2** (`v_β`; 3.x's
`pendLc_pendBad`). -/
theorem pendLc4_pendBad4 (R : P4b.FSrc) (kf : Rev4.NodeKind → F → ℕ → F)
    {oZ' oSh : CKind → Log → F → Prop} {M : ZLM4} (hS : SegInd M) {zw : Wit} (hzw : WitOf R zw)
    {L es : Log} (h : PendLc M zw L es) : P4b.PendBad4 R kf (P4b.okRS4 oZ' oLc4 oSh) L es := by
  obtain ⟨-, hn, hne⟩ := h
  refine ⟨1, by rw [P4b.rsPtsL4_length]; split_ifs <;> norm_num, fun ho => hne ?_⟩
  have ho' : P4b.trueL4 R kf (kindOfC es) L es 1 = vBetaL es := ho
  have ht : ∑ i : Fin 8, fAt es 98 0 ^ i.val * tL M zw L es i = zfL M zw L es 0 := by
    rw [Fin.sum_univ_succ]; simp [tL]
  rw [ht, zfL_seg4 R kf hS hzw hn, ho']

/-- **RS claim 2's true value on a node is the true batch** `Σ_i β^i z̄̃_{i+1}(r_k)` (3.x's
`trueL_node`). -/
theorem trueL4_node (R : P4b.FSrc) {kf : Rev4.NodeKind → F → ℕ → F} {M : ZLM4} (hkf : KfInd M kf)
    {zw : Wit} (hzw : WitOf R zw) {L es : Log} (hn : (kindOfC es).isNode = true) :
    P4b.trueL4 R kf (kindOfC es) L es 1 = ∑ i : Fin 8, fAt es 98 0 ^ i.val * tNL M zw L es i := by
  obtain ⟨ν, hν⟩ : ∃ ν, kindOfC es = .node ν := by
    cases h : kindOfC es with
    | seg σ => rw [h] at hn; cases hn
    | node ν => exact ⟨ν, rfl⟩
  rw [trueL4_one R kf hzw]
  simp only [tNL, zfL_eq4, mul_sum]
  symm
  rw [sum_comm]
  refine sum_congr rfl fun t _ => ?_
  rw [sum_comm]
  refine sum_congr rfl fun j _ => ?_
  have hk : P4b.kfT4 kf (kindOfC es) es t =
      ∑ i : Fin 8, fAt es 98 0 ^ i.val * M.Ind (kindOfC es) i.succ t := by
    rw [hν]; exact hkf ν _ t
  rw [hk, mul_sum, sum_mul]
  exact sum_congr rfl fun i _ => by ring

/-- **A node's pending Lc claim is RS0's `PendBad4` at claim 2** (through the kind factor). -/
theorem pendLcN4_pendBad4 (R : P4b.FSrc) {kf : Rev4.NodeKind → F → ℕ → F}
    {oZ' oSh : CKind → Log → F → Prop} {M : ZLM4} (hkf : KfInd M kf) {zw : Wit}
    (hzw : WitOf R zw) {L es : Log} (h : PendLcN M zw L es) :
    P4b.PendBad4 R kf (P4b.okRS4 oZ' oLc4 oSh) L es := by
  obtain ⟨-, hn, hne⟩ := h
  refine ⟨1, by rw [P4b.rsPtsL4_length]; split_ifs <;> norm_num, fun ho => hne ?_⟩
  have ho' : P4b.trueL4 R kf (kindOfC es) L es 1 = vBetaL es := ho
  rw [← ho', trueL4_node R hkf hzw hn]

/-! ## Phase 12's pending dooms are RS0's `PendBad4` -/

section Pend
variable (R : P4b.FSrc) {kf : Rev4.NodeKind → F → ℕ → F} {P : Front4a} {wNS : CKind → Log → F}

/-- **Phase 12's pending claims are false at RS0** (from 170): Z's, a segment's or a node's Lc,
S2's (3.x's four `okF_pend*` bridges without E's). -/
theorem pendF4a_pendBad4 (hS : SegInd P.M) (hkf : KfInd P.M kf) (hzw : WitOf R P.zw) {L es : Log}
    (hNS : (kindOfC es).isNode = true → wNS (kindOfC es) es =
      ∑ q ∈ range (2 ^ 10), ∑ y ∈ range (2 ^ nbC (kindOfC es)),
        eqAtR (ptOf (nbC (kindOfC es)) (rbL (kindOfC es) es)) y *
          eqAtR (ptOf 10 (rpL (kindOfC es) es)) q * P.wN (kindOfC es) es y q)
    (hL : (kindOfC es).isNode = false → lastL es < 2 ^ nbC (kindOfC es)) (hl : 170 ≤ es.length)
    (h : PendZ P.zw L es ∨ PendLc P.M P.zw L es ∨ PendLcN P.M P.zw L es ∨ D2S P.wN P.zw L es) :
    P4b.PendBad4 R kf (P4b.okRS4 oZ oLc4 (oSh4 wNS)) L es := by
  rcases h with h | h | h | h
  · exact pendZ4_pendBad4 R kf hzw h
  · exact pendLc4_pendBad4 R kf hS hzw h
  · exact pendLcN4_pendBad4 R hkf hzw h
  · exact pendS4_pendBad4 R kf hzw hNS hL h hl

/-- **Phase 12's doom at E4 end** is the background or a false pending claim (E4 end's `DPend4`
with P4b's `pendE4_pendBad4` and the background's far and public parts). -/
theorem dF4a12_pendBad4 (hS : SegInd P.M) (hkf : KfInd P.M kf) (hzw : WitOf R P.zw) {L es : Log}
    (hNS : (kindOfC es).isNode = true → wNS (kindOfC es) es =
      ∑ q ∈ range (2 ^ 10), ∑ y ∈ range (2 ^ nbC (kindOfC es)),
        eqAtR (ptOf (nbC (kindOfC es)) (rbL (kindOfC es) es)) y *
          eqAtR (ptOf 10 (rpL (kindOfC es) es)) q * P.wN (kindOfC es) es y q)
    (hL : (kindOfC es).isNode = false → lastL es < 2 ^ nbC (kindOfC es)) (hl : 170 ≤ es.length)
    (h : DF4a P 12 L es) : P.BgA L es ∨ P4b.PendBad4 R kf (P4b.okRS4 oZ oLc4 (oSh4 wNS)) L es := by
  rcases h with (h | h | h | h) | h
  · exact .inl h
  all_goals refine .inr (pendF4a_pendBad4 R hS hkf hzw hNS hL hl ?_)
  · exact .inl h
  · exact .inr (.inl h)
  · exact .inr (.inr (.inl h))
  · exact .inr (.inr (.inr h))

end Pend

end FR.Snd.P4a

end G6_FRSoundness4P4aRS

section G6_FRSoundness4P4aNZ

-- New for `flock-recursive` (BLUEPRINT revision 4.1, A.6/A.7 per node kind, A.10 Z1/L3β; stage P4a
-- pass 5 (P4e)): the node half's Z and kind factor at S-E12a's maps (`FRNodeKinds4`,
-- `FRNodeCircuit4`). 3.x templates: `FRSoundnessFrZM` (`zlmFR_bits`, `zHolds_iff_truthZN`),
-- `FRSoundnessFrLN` (`kfT_node`).

/-!
# The node's matrices at revision 4.1: bits, the kind factor, Z's statement

`M := zlm4 indN4 etN4` (S-E12a's indicators `indN4` and targets `etN4`, from `nodeLayout4`):

* **`zlm4_bits4`** (`ZLM4.Bits`), with S-E12a's `zlm4_indKinds` (`IndKinds`) and P4d's
  `zlm4_etLocal` (`EtLocal`): `Front4a.OK`'s matrix fields.
* **`kfInd4`**: S-E12a's kind factor `kf4` is the node's indicators batched by `β` (`KfInd`), so
  `PendLcN` is RS claim 2's doom (`pendLcN4_pendBad4`).
* **`zHolds_iff_truthZ4`**: on a node, `ZHolds` is S-E12a's `truthZ4` on `f⁽⁰⁾` (every non-free
  block meets its kind's R1CS with its target; the free blocks' rows `z² = z` hold on bits).
-/

namespace FR.Snd.P4a
open RecursionFast FR.Merkle Finset FR.Impl

set_option linter.constructorNameAsVariable false

/-! ## Bits and the kind factor -/

/-- **`zlm4`'s matrices, indicators and targets are bits** when the node maps are. -/
theorem zlm4_bits {indN : Rev4.NodeKind → Fin 9 → ℕ → F} {etN : Rev4.NodeKind → ℕ → Fin (2 ^ 14) → F}
    (hI : ∀ ν j t, IsBitF (indN ν j t)) (hE : ∀ ν t p, IsBitF (etN ν t p)) :
    (zlm4 indN etN).Bits := by
  refine ⟨kMat_bit _, kMat_bit _, fun κ j t => ?_, fun κ es t p => ?_⟩
  · cases κ with
    | seg σ => simp only [zlm4]; split_ifs <;> simp [IsBitF]
    | node ν => exact hI ν j t
  · cases κ with
    | seg σ =>
      simp only [zlm4, EtSeg, chainE]
      split_ifs <;> simp [IsBitF]
    | node ν => exact hE ν t p

/-- **S-E12a's maps give bits.** -/
theorem zlm4_bits4 : (zlm4 N4c.indN4 N4c.etN4).Bits :=
  zlm4_bits (fun ν j t => (N4c.indN4_etN4_bits ν j t 0).1) (fun ν t p => (N4c.indN4_etN4_bits ν 0 t p).2)

/-- **S-E12a's kind factor is the batched indicators** (`kf4` sums over `blockKinds.tail`, the
indicators of kinds `1 … 8`). -/
theorem kfInd4 : KfInd (zlm4 N4c.indN4 N4c.etN4) N4c.kf4 := fun ν β t => by
  rw [N4c.kf4, Finset.sum_range (fun i => β ^ i * _)]
  refine sum_congr rfl fun i _ => ?_
  congr 1

/-! ## Z's statement on a node -/

theorem bkIdx4_eq (b : BlockKind) : N4c.bkIdx4 b = bkIdx b := by cases b <;> rfl

/-- **A target of a kind's form pins exactly the kind's rows** (3.x's `pins_*`). -/
theorem kindTgt_pins {b : BlockKind} {t : Block.Target} (h : N4c.KindTgt b t) (p : Block.Pos) :
    (t p).isNone = !isZeroRow b p.val := by
  match b, h with
  | .stream, ⟨L, i, h⟩ => rw [h]; exact pins_stream L i p
  | .streamStart, h => rw [h]; exact pins_streamStart p
  | .streamEnd41, h => rw [h]; exact pins_streamEnd41 p
  | .hashA, h => rw [h]; exact pins_hashA p
  | .hashB1, ⟨tag, h⟩ => rw [h]; exact pins_hashB1 tag p
  | .hashB2, h => rw [h]; exact pins_hashB2 p
  | .w43, ⟨i, s, h⟩ => rw [h]; exact pins_w43 i s p

/-- **`ZHolds` from the blocks' rows** (the converse of `zHolds_blocks`). -/
theorem zHolds_of_blocks4 {M : ZLM4} {zw : Wit} {L es : Log}
    (h : ∀ t < 2 ^ qL (kindOfC es), ∀ p : Fin (2 ^ 14),
      mvZ M zw M.Ak (kindOfC es) L es t p * mvZ M zw M.Bk (kindOfC es) L es t p =
        zBk zw (kindOfC es) L es t p + M.Et (kindOfC es) es t p) : ZHolds M zw L es := by
  intro σ u
  have h8 : 2 ^ mC 6 (kindOfC es) = 256 * 2 ^ qL (kindOfC es) := by
    rw [mC6_q, pow_add]; norm_num
  have hu : u.val / 256 < 2 ^ qL (kindOfC es) := by
    have := lt_of_lt_of_eq u.isLt h8; omega
  exact h _ hu (pAt σ u.val)

/-- A node's block rows read the block's kind only (`indN4_eq`). -/
theorem mvZ_node4 (ν : Rev4.NodeKind) (zw : Wit) (C : Block.Pos → Block.Pos → Bool) (L es : Log)
    (t : ℕ) (p : Fin (2 ^ 14)) :
    mvZ (zlm4 N4c.indN4 N4c.etN4) zw (kMat C) (.node ν) L es t p =
      ∑ k, kMat C (bkIdx (N4c.nodeBK4 ν t)) p k * zBk zw (.node ν) L es t k := by
  unfold mvZ
  rw [sum_eq_single (bkIdx (N4c.nodeBK4 ν t)) (fun j _ hj => by
      rw [show (zlm4 N4c.indN4 N4c.etN4).Ind (.node ν) j t = N4c.indN4 ν j t from rfl,
        N4c.indN4_eq, bkIdx4_eq, if_neg hj, zero_mul])
    (fun h => absurd (mem_univ _) h)]
  rw [show (zlm4 N4c.indN4 N4c.etN4).Ind (.node ν) _ t = N4c.indN4 ν _ t from rfl,
    N4c.indN4_eq, bkIdx4_eq, if_pos rfl, one_mul]

/-- The node's witness blocks are `f⁽⁰⁾`'s (`WitOf`). -/
theorem zBk_zB4 {R : P4b.FSrc} {zw : Wit} (hzw : WitOf R zw) {ν : Rev4.NodeKind} {L es : Log}
    (hν : kindOfC es = .node ν) (t : ℕ) (k : Fin (2 ^ 14)) :
    zBk zw (.node ν) L es t k = N4c.zB4 (R.fz L es) t k := by
  have := hzw L es (t * 2 ^ 14 + k.val)
  rw [hν] at this
  simp only [zBk, N4c.zB4, N4c.zW4]
  rw [mul_comm, this]

/-- **On a node, Z's statement is S-E12a's `truthZ4`** on `f⁽⁰⁾` (3.x's `zHolds_iff_truthZN`). -/
theorem zHolds_iff_truthZ4 {R : P4b.FSrc} {zw : Wit} (hzw : WitOf R zw) (hb : WitBits zw)
    {ν : Rev4.NodeKind} {L es : Log} (hν : kindOfC es = .node ν) :
    ZHolds (zlm4 N4c.indN4 N4c.etN4) zw L es ↔ N4c.truthZ4 ν (R.fz L es) := by
  have hq : 2 ^ qL (kindOfC es) = ν.blocks := by rw [hν]; rfl
  have hA : (zlm4 N4c.indN4 N4c.etN4).Ak = kMat Block.circuitR1CS.A := rfl
  have hB : (zlm4 N4c.indN4 N4c.etN4).Bk = kMat Block.circuitR1CS.B := rfl
  have hE : ∀ t p, (zlm4 N4c.indN4 N4c.etN4).Et (.node ν) es t p = N4c.etN4 ν t p := fun _ _ => rfl
  have hz : ∀ t, zBk zw (.node ν) L es t = N4c.zB4 (R.fz L es) t := fun t =>
    funext (zBk_zB4 hzw hν t)
  constructor
  · intro h blk hblk tgt ht k
    have hbf : N4c.nodeBK4 ν blk ≠ .free := fun e => by
      rw [← N4c.nodeKind4_none_iff ν hblk, ht] at e; cases e
    have e := zHolds_blocks h blk (by rw [hq]; exact hblk) k
    rw [hν, hA, hB, mvZ_node4, mvZ_node4, hE,
      kMat_mulVec _ hbf (kindTgt_pins (N4c.nodeKind4_kind ht)),
      kMat_mulVec _ hbf (kindTgt_pins (N4c.nodeKind4_kind ht))] at e
    simp only [N4c.etN4, ht, tgtE_eq, hz] at e
    exact e
  · intro h
    refine zHolds_of_blocks4 fun t ht p => ?_
    rw [hq] at ht
    rw [hν, hA, hB, mvZ_node4, mvZ_node4, hE]
    rcases hk : N4c.nodeKind4 ν t with _ | tgt
    · have hbf : N4c.nodeBK4 ν t = .free := (N4c.nodeKind4_none_iff ν ht).mp hk
      rw [hbf, kMat_free, kMat_free, N4c.etN4, hk]
      exact bit_sq (hb _ _ _ _)
    · have hbf : N4c.nodeBK4 ν t ≠ .free := fun e => by
        rw [← N4c.nodeKind4_none_iff ν ht, hk] at e; cases e
      rw [kMat_mulVec _ hbf (kindTgt_pins (N4c.nodeKind4_kind hk)),
        kMat_mulVec _ hbf (kindTgt_pins (N4c.nodeKind4_kind hk))]
      simp only [N4c.etN4, hk, tgtE_eq, hz]
      exact h t ht tgt hk p

end FR.Snd.P4a

end G6_FRSoundness4P4aNZ

section G6_FRSoundness4P4aNS

-- New for `flock-recursive` (BLUEPRINT revision 4.1, A.8/A.9 `finSh` on a node, A.10 S1/S2; stage P4a
-- pass 5 (P4e)): the node's S2 law at S-E12a's layout (`chainLk4`, `srcB4`/`mirB4`). 3.x templates:
-- `FRSoundnessFrSh` (`wNode`, `resNode`, `sh_sum_node`, `res_ne_node`).

/-!
# The node's S2 law at revision 4.1: `SNode` for `truthS4`

A node's S truth (S-E12a's `truthS4` on `f⁽⁰⁾`, **`truthS4_iff`**) is **`ShHoldsN4`**: block `y`'s
`h_out` is block `y + 1`'s `h_in` on the chain mask `chainLk4` (both signed children's main
chains), and each WOTS link family's field equals its mirror (`srcB4`/`mirB4`, 3.x's families
rebased).

* **`wNode4`**: S2's weight on a node (A.9 `finSh` (ii), 3.x's `wNode` at the 4.1 layout and
  `nb = m − 14` block coordinates): `Out` at `[lk y] eq(τ, y)`, `In` at the shifted mask plus the
  start term `κ_s ([y = 0] + [y = chLen₀])`, the eight families batched by `κ_s^(f+2)`.
* **`resNode4`** (`J = 10`), **`sh_sum_node4`**: the true sum is the batched residual (the target is
  `0`: `c0S_node4`). **`res_ne_node4`**: a failed `ShHoldsN4` leaves a nonzero residual.
* **`sNode4`**: P4c's `SNode wN4 (truthSN4 zw) zw`; **`wNLocal4`**; **`wNS4`**, `hNS4` (the
  weight's extension at S2's point, `pendS4_pendBad4`'s `hNS`).

What the node verifier computes in `finSh` (ii) is `implN κ`'s (`VnodeC`; parametric): that it is
`wNS4` is the node ops' specification, not proved here.
-/

namespace FR.Snd.P4a
open RecursionFast FR.Merkle Finset FR.Impl

set_option linter.constructorNameAsVariable false

/-! ## The layout's bounds -/

section Bounds
variable {ν : Rev4.NodeKind}

theorem nodeBK4_lt {blk : ℕ} (h : N4c.nodeBK4 ν blk ≠ .free) : blk < 2 ^ nbC (.node ν) := by
  unfold N4c.nodeBK4 at h
  rcases e : N4c.ivAt (N4c.nodeLayout4 ν) blk with _ | iv
  · rw [e] at h; exact absurd rfl h
  · have hm := List.mem_of_find?_eq_some e
    have hk : iv.mem blk = true := by simpa using List.find?_some e
    have := N4c.layout_bounds ν hm
    simp only [N4c.TIv.mem, Bool.and_eq_true, decide_eq_true_eq] at hk
    show blk < ν.blocks
    omega

theorem chainLk4_lt {y : ℕ} (h : N4c.chainLk4 ν y = true) : y + 1 < 2 ^ nbC (.node ν) :=
  nodeBK4_lt (by rw [N4c.chainLk4_stream h]; exact fun e => by cases e)

theorem chLen0_lt (ν : Rev4.NodeKind) : N4c.chLen ν 0 < 2 ^ nbC (.node ν) := by
  refine nodeBK4_lt (ν := ν) ?_
  rw [N4c.bk_of_mem (iv := ⟨.streamStart, N4c.chBase ν 1, N4c.chBase ν 1 + 1,
      fun _ => some Kinds.streamStart.target⟩)
    (N4c.chainIvs_mem ν (σ := 1) (by norm_num) _ (by simp [N4c.chainIvs]))
    (by simp [N4c.TIv.mem, N4c.chBase])]
  exact fun e => by cases e

theorem hUsedN_lt (ν : Rev4.NodeKind) : N4c.hUsedN ν < 2 ^ nbC (.node ν) := by
  obtain ⟨h1, h2⟩ := N4c.hEnd_le ν
  obtain ⟨-, h3, h4, -⟩ := Rev4.regions_fit ν
  have h5 : 1 ≤ N4c.nAgg ν * ν.maxK := by cases ν <;> decide
  show _ < ν.blocks
  omega

theorem fam_mir_lt {f t : ℕ} (ht : t < (NodeT.fam f).n) : (NodeT.fam f).mir t < Layout.mirSources := by
  have hm : Layout.mirSources = 581 := rfl
  rw [hm]
  rcases f with _ | _ | _ | _ | _ | _ | _ | _ | f <;> simp only [NodeT.fam, id] at ht ⊢ <;> omega

theorem srcB4_lt {σ f t : ℕ} (hσ : σ < 2) (ht : t < (NodeT.fam f).n) :
    N4c.srcB4 ν σ f t < 2 ^ nbC (.node ν) := by
  have hs : (NodeT.fam f).src t < Rev4.wotsSlot4 := fam_src_lt ht
  refine nodeBK4_lt ?_
  rw [N4c.srcB4, N4c.nodeBK4_wots ν hσ hs]
  exact N4c.wotsKindAt_ne_free _

theorem mirB4_lt {σ f t : ℕ} (hσ : σ < 2) (ht : t < (NodeT.fam f).n) :
    N4c.mirB4 ν σ f t < 2 ^ nbC (.node ν) :=
  lt_trans (N4c.mir4_fits ν hσ (fam_mir_lt ht)).2.1 (hUsedN_lt ν)

/-- Distinct sources of a family lie in distinct blocks (3.x's `srcB_inj`). -/
theorem srcB4_inj {f σ σ' t t' : ℕ} (hσ : σ < 2) (hσ' : σ' < 2) (ht : t < (NodeT.fam f).n)
    (ht' : t' < (NodeT.fam f).n) (h : N4c.srcB4 ν σ' f t' = N4c.srcB4 ν σ f t) : σ' = σ ∧ t' = t := by
  have h1 := fam_src_lt ht
  have h2 := fam_src_lt ht'
  have hw : Layout.wotsSlot = 498 := rfl
  have hw4 : Rev4.wotsSlot4 = 498 := rfl
  unfold N4c.srcB4 N4c.wotsB at h
  rw [hw4] at h
  rw [hw] at h1 h2
  have hs : σ' = σ := by
    rcases (by omega : σ = 0 ∨ σ = 1) with rfl | rfl <;>
      rcases (by omega : σ' = 0 ∨ σ' = 1) with rfl | rfl <;> omega
  subst hs
  exact ⟨rfl, fam_src_inj (f := f) (by omega)⟩

end Bounds

/-! ## The truth -/

/-- **A node's S truth** on the witness's blocks (S-E12a's `truthS4`). -/
def ShHoldsN4 (ν : Rev4.NodeKind) (z : ℕ → ℕ → F) : Prop :=
  (∀ y, N4c.chainLk4 ν y = true → ∀ j < 256, z (y + 1) j = z y (256 + j)) ∧
    ∀ f < nLinkFam, ∀ σ < 2, ∀ t < (NodeT.fam f).n, ∀ s < NodeT.fbits f,
      z (N4c.srcB4 ν σ f t) (NodeT.fpos f s) = z (N4c.mirB4 ν σ f t) (NodeT.mpos f t s)

/-- **The node's S truth by kind** (`Front4a.truthSN`; a segment's is `truthS`'s own branch). -/
def truthSN4 (zw : Wit) : CKind → Log → Log → Prop
  | .node ν, L, es => ShHoldsN4 ν (zNodeC zw (.node ν) L es)
  | .seg _, _, _ => True

theorem zNodeC_zN4 {R : P4b.FSrc} {zw : Wit} (hzw : WitOf R zw) {ν : Rev4.NodeKind} {L es : Log}
    (hν : kindOfC es = .node ν) : zNodeC zw (.node ν) L es = N4c.zN4 (R.fz L es) := by
  funext blk p
  have := hzw L es (blk * 2 ^ 14 + p)
  rw [hν] at this
  simp only [zNodeC, N4c.zN4, N4c.zW4, this]

/-- **`truthSN4` is S-E12a's `truthS4`** on `f⁽⁰⁾`. -/
theorem truthS4_iff {R : P4b.FSrc} {zw : Wit} (hzw : WitOf R zw) {ν : Rev4.NodeKind} {L es : Log}
    (hν : kindOfC es = .node ν) : N4c.truthS4 ν (R.fz L es) ↔ truthSN4 zw (kindOfC es) L es := by
  rw [hν]
  simp only [truthSN4, zNodeC_zN4 hzw hν]
  rfl

/-! ## The weight and the residual -/

section Weight
variable (ν : Rev4.NodeKind)

/-- The `Out` weight `[lk y] eq(τ, y)`. -/
def lkW4 {n : ℕ} (τ : Fin n → F) (y : ℕ) : F := if N4c.chainLk4 ν y then eqAtR τ y else 0

/-- The `In` weight: `[lk (y−1)] eq(τ, y − 1) + κ_s ([y = 0] + [y = chLen₀])`. -/
def shN4 {n : ℕ} (τ : Fin n → F) (κ : F) (y : ℕ) : F :=
  (if 1 ≤ y ∧ N4c.chainLk4 ν (y - 1) then eqAtR τ (y - 1) else 0) +
    κ * ((if y = 0 then 1 else 0) + if y = N4c.chLen ν 0 then 1 else 0)

/-- Family `f`'s weight at cell `(y, q)`: `Σ_σ Σ_t Σ_s eq(τ, src) eq(θ, s)` times the
source-minus-mirror indicator (3.x's `famW` through `linkInd_sum`). -/
def famW4 (f : ℕ) {n : ℕ} (τ : Fin n → F) (θ : Fin 10 → F) (y q : ℕ) : F :=
  ∑ σ ∈ range 2, ∑ t ∈ range (NodeT.fam f).n, ∑ s ∈ range (NodeT.fbits f),
    eqAtR τ (N4c.srcB4 ν σ f t) * eqAtR θ s *
      ((if y = N4c.srcB4 ν σ f t ∧ q = NodeT.fpos f s then 1 else 0) -
        (if y = N4c.mirB4 ν σ f t ∧ q = NodeT.mpos f t s then 1 else 0))

/-- **A node's S2 weight** (A.9 `finSh` (ii)). -/
def wNode4 {n : ℕ} (τ : Fin n → F) (θ : Fin 10 → F) (κ : F) (y q : ℕ) : F :=
  lkW4 ν τ y * slotT θ 256 q + shN4 ν τ κ y * slotT θ 0 q +
    ∑ f ∈ range nLinkFam, κ ^ (f + 2) * famW4 ν f τ θ y q

/-- **A node's residuals** (`J = 10`): the masked links, the starts, the families' differences
(table `f + 2` at a source block and a field bit). -/
def resNode4 (z : ℕ → ℕ → F) (j u q : ℕ) : F :=
  if j = 0 then (if q < 256 ∧ N4c.chainLk4 ν u then z u (256 + q) + z (u + 1) q else 0)
  else if j = 1 then (if q < 256 then z 0 q + z (N4c.chLen ν 0) q else 0)
  else ∑ σ ∈ range 2, ∑ t ∈ range (NodeT.fam (j - 2)).n,
    if u = N4c.srcB4 ν σ (j - 2) t ∧ q < NodeT.fbits (j - 2) then
      z u (NodeT.fpos (j - 2) q) - z (N4c.mirB4 ν σ (j - 2) t) (NodeT.mpos (j - 2) t q) else 0

end Weight

section Sum
variable {ν : Rev4.NodeKind}

/-- Two outer and two inner sums swap. -/
theorem sum_swap22 (A B C D : Finset ℕ) (g : ℕ → ℕ → ℕ → ℕ → F) :
    ∑ a ∈ A, ∑ b ∈ B, ∑ c ∈ C, ∑ d ∈ D, g a b c d =
      ∑ c ∈ C, ∑ d ∈ D, ∑ a ∈ A, ∑ b ∈ B, g a b c d :=
  calc _ = ∑ a ∈ A, ∑ c ∈ C, ∑ b ∈ B, ∑ d ∈ D, g a b c d := sum_congr rfl fun _ _ => sum_comm
    _ = ∑ a ∈ A, ∑ c ∈ C, ∑ d ∈ D, ∑ b ∈ B, g a b c d :=
        sum_congr rfl fun _ _ => sum_congr rfl fun _ _ => sum_comm
    _ = ∑ c ∈ C, ∑ a ∈ A, ∑ d ∈ D, ∑ b ∈ B, g a b c d := sum_comm
    _ = _ := sum_congr rfl fun _ _ => sum_comm

theorem sum_delta2 {A B a b : ℕ} (ha : a < A) (hb : b < B) (z : ℕ → ℕ → F) :
    ∑ q ∈ range B, ∑ y ∈ range A, (if y = a ∧ q = b then (1 : F) else 0) * z y q = z a b := by
  rw [sum_eq_single b, sum_eq_single a]
  · simp
  · intro y _ hy; simp [hy]
  · intro h; exact absurd (mem_range.2 ha) h
  · intro q _ hq
    exact sum_eq_zero fun y _ => by simp [hq]
  · intro h; exact absurd (mem_range.2 hb) h

/-- Family `f`'s part of the true sum: the weighted source-minus-mirror differences. -/
theorem sum_famW4 {f : ℕ} (τ : Fin (nbC (.node ν)) → F) (θ : Fin 10 → F) (z : ℕ → ℕ → F) :
    ∑ q ∈ range (2 ^ 10), ∑ y ∈ range (2 ^ nbC (.node ν)), famW4 ν f τ θ y q * z y q =
      ∑ σ ∈ range 2, ∑ t ∈ range (NodeT.fam f).n, ∑ s ∈ range (NodeT.fbits f),
        eqAtR τ (N4c.srcB4 ν σ f t) * eqAtR θ s *
          (z (N4c.srcB4 ν σ f t) (NodeT.fpos f s) -
            z (N4c.mirB4 ν σ f t) (NodeT.mpos f t s)) := by
  simp only [famW4, sum_mul]
  rw [sum_comm (s := range (2 ^ 10))]
  simp only [sum_comm (s := range (2 ^ 10)) (t := range 2), sum_comm (s := range (2 ^ 10))
    (t := range (NodeT.fam f).n), sum_comm (s := range (2 ^ 10)) (t := range (NodeT.fbits f))]
  rw [sum_comm (s := range (2 ^ nbC (.node ν))) (t := range 2)]
  refine sum_congr rfl fun σ hσ => ?_
  rw [sum_comm (s := range (2 ^ nbC (.node ν))) (t := range (NodeT.fam f).n)]
  refine sum_congr rfl fun t ht => ?_
  rw [sum_comm (s := range (2 ^ nbC (.node ν))) (t := range (NodeT.fbits f))]
  refine sum_congr rfl fun s hs => ?_
  have hσ' := mem_range.1 hσ
  have ht' := mem_range.1 ht
  have hb := (NodeT.fam_bounds (s := s) hσ' ht').2.2 (mem_range.1 hs)
  rw [sum_comm]
  simp only [mul_assoc, ← mul_sum, sub_mul, sum_sub_distrib]
  rw [sum_delta2 (srcB4_lt hσ' ht') hb.1, sum_delta2 (mirB4_lt hσ' ht') hb.2]

/-- Family `f`'s residual table, batched at `(τ, θ)`. -/
theorem sum_resF4 {f : ℕ} (τ : Fin (nbC (.node ν)) → F) (θ : Fin 10 → F) (z : ℕ → ℕ → F) :
    ∑ q ∈ range (2 ^ 10), ∑ u ∈ range (2 ^ nbC (.node ν)), eqAtR τ u * eqAtR θ q *
      resNode4 ν z (f + 2) u q =
      ∑ σ ∈ range 2, ∑ t ∈ range (NodeT.fam f).n, ∑ s ∈ range (NodeT.fbits f),
        eqAtR τ (N4c.srcB4 ν σ f t) * eqAtR θ s *
          (z (N4c.srcB4 ν σ f t) (NodeT.fpos f s) -
            z (N4c.mirB4 ν σ f t) (NodeT.mpos f t s)) := by
  simp only [resNode4, show f + 2 ≠ 0 by omega, show f + 2 ≠ 1 by omega, if_false,
    Nat.add_sub_cancel, mul_sum]
  rw [sum_swap22]
  refine sum_congr rfl fun σ hσ => sum_congr rfl fun t ht => ?_
  have hσ' := mem_range.1 hσ
  have ht' := mem_range.1 ht
  rw [sum_comm, sum_eq_single (N4c.srcB4 ν σ f t)]
  · simp only [true_and, mul_ite, mul_zero]
    rw [sum_range_ite_lt (NodeT.fbits_le f)]
  · intro u _ hu; exact sum_eq_zero fun q _ => by simp [hu]
  · intro h; exact absurd (mem_range.2 (srcB4_lt hσ' ht')) h

theorem chainLk4_top (ν : Rev4.NodeKind) : N4c.chainLk4 ν (2 ^ nbC (.node ν) - 1) = false := by
  by_contra h
  have := chainLk4_lt (Bool.not_eq_false _ ▸ h)
  have := Nat.two_pow_pos (nbC (.node ν))
  omega

/-- **The node's true S2 sum is its residual** (3.x's `sh_sum_node`; the target is `0`). -/
theorem sh_sum_node4 (τ : Fin (nbC (.node ν)) → F) (θ : Fin 10 → F) (κ : F) (z : ℕ → ℕ → F) :
    ∑ q ∈ range (2 ^ 10), ∑ y ∈ range (2 ^ nbC (.node ν)), wNode4 ν τ θ κ y q * z y q =
      resSum (nbC (.node ν)) 10 (resNode4 ν z) τ θ κ := by
  set O : ℕ → F := fun y => thS θ fun σ => z y (256 + σ)
  set I : ℕ → F := fun y => thS θ fun σ => z y σ
  set G : ℕ → F := fun f => ∑ q ∈ range (2 ^ 10), ∑ y ∈ range (2 ^ nbC (.node ν)), famW4 ν f τ θ y q * z y q
  have hL : ∑ q ∈ range (2 ^ 10), ∑ y ∈ range (2 ^ nbC (.node ν)), wNode4 ν τ θ κ y q * z y q =
      ∑ y ∈ range (2 ^ nbC (.node ν)), (lkW4 ν τ y * O y + shN4 ν τ κ y * I y) +
        ∑ f ∈ range nLinkFam, κ ^ (f + 2) * G f := by
    have e1 : ∑ q ∈ range (2 ^ 10), ∑ y ∈ range (2 ^ nbC (.node ν)),
        (lkW4 ν τ y * slotT θ 256 q + shN4 ν τ κ y * slotT θ 0 q) * z y q =
        ∑ y ∈ range (2 ^ nbC (.node ν)), (lkW4 ν τ y * O y + shN4 ν τ κ y * I y) := by
      rw [sum_comm]
      refine sum_congr rfl fun y _ => ?_
      simp only [add_mul, sum_add_distrib, mul_assoc]
      rw [← mul_sum, ← mul_sum, sum_slotT θ (by norm_num), sum_slotT θ (by norm_num)]
      simp only [O, I, thS, zero_add]
    have e2 : ∑ q ∈ range (2 ^ 10), ∑ y ∈ range (2 ^ nbC (.node ν)),
        (∑ f ∈ range nLinkFam, κ ^ (f + 2) * famW4 ν f τ θ y q) * z y q =
        ∑ f ∈ range nLinkFam, κ ^ (f + 2) * G f := by
      simp only [G, sum_mul, mul_sum, mul_assoc]
      rw [sum_congr rfl fun q _ => sum_comm, sum_comm]
    simp only [wNode4, add_mul (lkW4 ν τ _ * _ + _), sum_add_distrib]
    rw [e1, e2, sum_add_distrib]
  have hN : N4c.chLen ν 0 < 2 ^ nbC (.node ν) := chLen0_lt ν
  obtain ⟨M, hM⟩ : ∃ M, 2 ^ nbC (.node ν) = M + 1 := ⟨2 ^ nbC (.node ν) - 1, by have := Nat.two_pow_pos (nbC (.node ν)); omega⟩
  have hS : ∑ y ∈ range (2 ^ nbC (.node ν)), shN4 ν τ κ y * I y =
      ∑ u ∈ range (2 ^ nbC (.node ν)), lkW4 ν τ u * I (u + 1) + κ * (I 0 + I (N4c.chLen ν 0)) := by
    have e1 : ∑ y ∈ range (2 ^ nbC (.node ν)), shN4 ν τ κ y * I y =
        ∑ y ∈ range (2 ^ nbC (.node ν)), (if 1 ≤ y ∧ N4c.chainLk4 ν (y - 1) then eqAtR τ (y - 1) * I y else 0) +
          κ * (I 0 + I (N4c.chLen ν 0)) := by
      simp only [shN4, add_mul, sum_add_distrib, ite_mul, zero_mul, mul_ite, mul_one, mul_zero,
        one_mul, mul_assoc, ← mul_sum, sum_ite_eq', mem_range, hN, Nat.two_pow_pos, if_true]
    have hl : N4c.chainLk4 ν M = false := by
      have := chainLk4_top ν; rw [hM, Nat.add_sub_cancel] at this; exact this
    rw [e1, hM, sum_range_succ', sum_range_succ]
    simp only [show ¬ (1 ≤ 0 ∧ N4c.chainLk4 ν (0 - 1) = true) from fun h => absurd h.1 (by omega),
      if_false, add_zero, Nat.add_sub_cancel, show ∀ u, 1 ≤ u + 1 from fun u => by omega, true_and]
    simp only [lkW4, hl, Bool.false_eq_true, if_false, zero_mul, add_zero, ite_mul, zero_mul]
  have hR0 : ∀ u, ∑ q ∈ range (2 ^ 10), eqAtR θ q * resNode4 ν z 0 u q =
      if N4c.chainLk4 ν u then O u + I (u + 1) else 0 := by
    intro u
    simp only [resNode4, if_true, ite_and, mul_ite, mul_zero]
    rw [sum_range_ite_lt (by norm_num)]
    by_cases h : N4c.chainLk4 ν u <;> simp only [h, if_true, if_false, sum_const_zero, O, I, thS,
      mul_add, sum_add_distrib, Bool.false_eq_true]
  have hR1 : ∀ u, ∑ q ∈ range (2 ^ 10), eqAtR θ q * resNode4 ν z 1 u q =
      I 0 + I (N4c.chLen ν 0) := by
    intro u
    simp only [resNode4, one_ne_zero, if_false, if_true, mul_ite, mul_zero]
    rw [sum_range_ite_lt (by norm_num)]
    simp only [I, thS, mul_add, sum_add_distrib]
  have hRf : ∀ f, ∑ q ∈ range (2 ^ 10), ∑ u ∈ range (2 ^ nbC (.node ν)), eqAtR τ u * eqAtR θ q *
      resNode4 ν z (f + 2) u q = G f := fun f => by
    simp only [G]; rw [sum_resF4, sum_famW4]
  have hres : resSum (nbC (.node ν)) 10 (resNode4 ν z) τ θ κ =
      ∑ u ∈ range (2 ^ nbC (.node ν)), lkW4 ν τ u * (O u + I (u + 1)) + κ * (I 0 + I (N4c.chLen ν 0)) +
        ∑ f ∈ range nLinkFam, κ ^ (f + 2) * G f := by
    unfold resSum
    rw [show range 10 = range (nLinkFam + 1 + 1) from rfl, sum_range_succ', sum_range_succ']
    simp only [hRf, pow_zero, one_mul, zero_add, pow_one]
    rw [sum_comm (s := range (2 ^ 10)), sum_comm (s := range (2 ^ 10))]
    simp only [mul_assoc, ← mul_sum, hR0, hR1, ← sum_mul, sum_eqAtR_one, one_mul]
    simp only [lkW4, mul_ite, mul_zero, ite_mul, zero_mul]
    ring
  rw [hL, hres, sum_add_distrib, hS]
  simp only [lkW4, mul_add, sum_add_distrib, ite_mul, zero_mul]
  ring

/-! ## A failed truth leaves a nonzero residual -/

/-- **A family residual at a source's field bit** is the source-minus-mirror difference. -/
theorem resNode4_src (z : ℕ → ℕ → F) {f σ t s : ℕ} (hσ : σ < 2) (ht : t < (NodeT.fam f).n)
    (hs : s < NodeT.fbits f) :
    resNode4 ν z (f + 2) (N4c.srcB4 ν σ f t) s =
      z (N4c.srcB4 ν σ f t) (NodeT.fpos f s) - z (N4c.mirB4 ν σ f t) (NodeT.mpos f t s) := by
  simp only [resNode4, show f + 2 ≠ 0 by omega, show f + 2 ≠ 1 by omega, if_false,
    Nat.add_sub_cancel]
  rw [sum_eq_single σ, sum_eq_single t]
  · simp only [hs, and_true, if_true]
  · intro t' ht' hne
    rw [if_neg fun he => hne (srcB4_inj hσ hσ ht (mem_range.1 ht') he.1.symm).2]
  · intro h; exact absurd (mem_range.2 ht) h
  · intro σ' hσ' hne
    refine sum_eq_zero fun t' ht' => ?_
    rw [if_neg fun he => hne (srcB4_inj hσ (mem_range.1 hσ') ht (mem_range.1 ht') he.1.symm).1]
  · intro h; exact absurd (mem_range.2 hσ) h

theorem shHoldsN4_of_res {z : ℕ → ℕ → F}
    (h : ∀ j < 10, ∀ u < 2 ^ nbC (.node ν), ∀ q < 2 ^ 10, resNode4 ν z j u q = 0) :
    ShHoldsN4 ν z := by
  refine ⟨fun y hy j hj => ?_, fun f hf σ hσ t ht s hs => ?_⟩
  · have e := h 0 (by norm_num) y (by have := chainLk4_lt hy; omega) j (by omega)
    simp only [resNode4, if_true, hj, hy, and_self] at e
    exact (CharTwo.add_eq_zero.mp e).symm
  · have hb := (NodeT.fam_bounds (s := s) hσ ht).2.2 hs
    have e := h (f + 2) (by unfold nLinkFam at hf; omega) _ (srcB4_lt hσ ht) s
      (lt_of_lt_of_le hs (NodeT.fbits_le f))
    rw [resNode4_src z hσ ht hs] at e
    exact sub_eq_zero.mp e

/-- **Some node residual table is nonzero** when the node's S truth fails. -/
theorem res_ne_node4 {z : ℕ → ℕ → F} (h : ¬ ShHoldsN4 ν z) :
    ∃ j < 10, ∃ u < 2 ^ nbC (.node ν), ∃ q < 2 ^ 10, resNode4 ν z j u q ≠ 0 := by
  by_contra hc
  push Not at hc
  exact h (shHoldsN4_of_res hc)

end Sum

/-! ## `SNode` at revision 4.1 -/

/-- **A node's S2 weight on the log** (S1's `τ`, `θ`, `κ_s`); `0` on a segment (`wS` reads the
segment's own). -/
def wN4 : CKind → Log → ℕ → ℕ → F
  | .node ν, es => wNode4 ν (ptOf (nbC (.node ν)) (tauL (.node ν) es)) (ptOf 10 (thL es)) (ksL es)
  | .seg _, _ => fun _ _ => 0

/-- The residual tables by kind. -/
def resN4 (zw : Wit) : CKind → Log → Log → ℕ → ℕ → ℕ → F
  | .node ν, L, es => resNode4 ν (zNodeC zw (.node ν) L es)
  | .seg _, _, _ => fun _ _ _ => 0

/-- **The weight's extension at S2's point** (`hNS` of `pendS4_pendBad4`, by definition). -/
def wNS4 (κ : CKind) (es : Log) : F :=
  ∑ q ∈ range (2 ^ 10), ∑ y ∈ range (2 ^ nbC κ),
    eqAtR (ptOf (nbC κ) (rbL κ es)) y * eqAtR (ptOf 10 (rpL κ es)) q * wN4 κ es y q

theorem hNS4 {es : Log} : (kindOfC es).isNode = true → wNS4 (kindOfC es) es =
    ∑ q ∈ range (2 ^ 10), ∑ y ∈ range (2 ^ nbC (kindOfC es)),
      eqAtR (ptOf (nbC (kindOfC es)) (rbL (kindOfC es) es)) y *
        eqAtR (ptOf 10 (rpL (kindOfC es) es)) q * wN4 (kindOfC es) es y q := fun _ => rfl

/-- **A node's S2 weight reads S1's challenges only** (before 114). -/
theorem wNLocal4 : WNLocal wN4 := fun κ es es' h => by
  obtain ⟨h1, h2, h3⟩ := s1_congr4 h le_rfl κ
  cases κ with
  | node ν => simp only [wN4, h1, h2, h3]
  | seg σ => rfl

/-- **A node's S2 initial claim is `0`** (the boundary values are zeros). -/
theorem c0S_node4 {es : Log} (hn : (kindOfC es).isNode = true) : c0S es = 0 := by
  rw [c0S, pad18, shiftTargetS, shiftTargetAt, ptA_toArray, ptA_toArray, mle_digTbl, mle_digTbl]
  generalize kindOfC es = κ at hn ⊢
  have hb : (bndL κ es).length = 4 := by unfold bndL; split_ifs <;> rfl
  have hg : ∀ j < 4, (bndL κ es ++ endBits κ es).toArray.getD j 0 = (bndL κ es).getD j 0 :=
    fun j hj => by
      simp [Array.getD_eq_getD_getElem?, List.getD_eq_getElem?_getD,
        List.getElem?_append_left (show j < (bndL κ es).length by omega)]
  rw [hg 0 (by norm_num), hg 1 (by norm_num), hg 2 (by norm_num), hg 3 (by norm_num)]
  simp only [bndL, hn, if_true, List.getD_cons_zero, List.getD_cons_succ, digBit_zero,
    Bool.false_eq_true, if_false, thS, mul_zero, sum_const_zero, add_zero]

section Inst
variable {zw : Wit} (hz : ZwSame zw)

theorem sum_wS_node {L es : Log} {ν : Rev4.NodeKind} (hν : kindOfC es = .node ν) :
    trueSum innerExpr (TS wN4 zw L es) (nrS (kindOfC es)) =
      ∑ q ∈ range (2 ^ 10), ∑ y ∈ range (2 ^ nbC (kindOfC es)),
        wN4 (kindOfC es) es y q * zNodeC zw (kindOfC es) L es y q := by
  rw [sum_TS]
  refine sum_congr rfl fun q _ => sum_congr rfl fun y _ => ?_
  simp only [wS, hν, CKind.isNode, if_true]

include hz in
/-- **The node's S2 law** (P4c's `SNode`) at S-E12a's layout. -/
def sNode4 : SNode wN4 (truthSN4 zw) zw where
  nJ _ := 10
  res := resN4 zw
  nJ_pos _ := by norm_num
  nJ_le κ := by have := nbC_le κ; omega
  sum L es hn := by
    obtain ⟨ν, hν⟩ : ∃ ν, kindOfC es = .node ν := by
      cases h : kindOfC es with
      | seg σ => rw [h] at hn; cases hn
      | node ν => exact ⟨ν, rfl⟩
    rw [sum_wS_node hν, c0S_node4 hn, zero_add]
    have e := sh_sum_node4 (ν := ν) (ptOf (nbC (.node ν)) (tauL (.node ν) es)) (ptOf 10 (thL es))
      (ksL es) (zNodeC zw (.node ν) L es)
    rw [hν]
    exact e
  ne κ L es hn hS := by
    cases κ with
    | seg σ => cases hn
    | node ν => exact res_ne_node4 hS
  same κ L es L' es' p h hp := by
    cases κ with
    | seg σ => rfl
    | node ν => simp only [resN4, zNodeC_same hz h (by omega)]
  truth_same κ L es L' es' p h hp := by
    cases κ with
    | seg σ => exact Iff.rfl
    | node ν => simp only [truthSN4, zNodeC_same hz h hp]

end Inst

end FR.Snd.P4a

end G6_FRSoundness4P4aNS
