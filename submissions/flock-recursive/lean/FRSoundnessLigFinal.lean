-- New for `flock-recursive` (BLUEPRINT §5.4 step 2, A.10 "What `final` then gets"; stage S-G2).
import FRSoundnessCompose

/-!
# `ligerito_final`: unique decoding of the five Ligerito levels (BLUEPRINT §5.4 (2))

The tail's dooms (`FRSoundnessTailD`: `D1`, `DCi`, `DP2`, `DP3`, `DPf`, composed as `DT`) are what
an accepted, non-escaping chain avoids. This module reads them off, level by level, and states
what they give `final`.

* **`LigeritoOut W₀ c₀ L es`** (Part B): on the chain `es` of the log `L`, for every level `i < 5`:
  - `close`: the word read under its cap is `eᵢ`-close (`¬ farL`);
  - `claim`: P1.i's initial claim is `⟨Wᵢ, f⁽ⁱ⁾⟩` over level `i`'s variables (`lvC`, `lvW`,
    `fTab`); at level 0 this is `c₀ = ⟨W₀, f⁽⁰⁾⟩`, the claim RS/B′ hand off;
  - `folded`: P1.i's claim after its `ℓᵢ` fold rounds is `⟨foldW Wᵢ, fold_z(f⁽ⁱ⁾)⟩`;
  - `near`, `fold`: the next codeword is close to the column fold (`truthP2`), and the next message
    is the fold of the decoded messages (`truthC`; level 4: the final message);
  - `cons`: every queried fold is the next codeword's symbol (`truthP3`);
  - `agree`: the consistency set is the joint agreement set (`consSet = jointAgree`, what the
    extractor's flags compute, S-H2 `level_decode`).
* **`ligerito_final`** (Part B): if no tail doom holds on any prefix of `es` from P1.0 to P2.4's
  last answer, and the Hide doom `DH` holds on `es`, then `LigeritoOut`. The dooms read are
  `D1 i` at P1.i's first absorb, `DCi i` at C.i, `DP2 i` at P2.i's last answer; P3.4 and Pf are
  not read (Part F).
* **`ligerito_final_of_walk`** (Part C): the same from what `final` has: a non-bad log, no escape
  of the composed doom or of `DH`, `ChainStab` of the composed doom (`chainStab_of`), and the
  composed doom false at the chain's end.
* **Level 0** (Part B): `f⁽⁰⁾` is F-valued and fixed once `cap₀` is absorbed
  (`level0_committed`): every prefix past `cap₀` reads the same close word and message.
* **Part D, Pf's end**: `DPf` at the chain's end is the final check `c_{Pf} = Ŵ(ρ)·final̂(ρ)` in
  the tables' extensions (`mleN`) at Pf's challenges (`not_DPf_end_iff`).
* **Part E, Merkle binding**: a path that evaluates on the log to the cap entry fixes the column
  `colOf` reads (`colOf_of_path`, from `cap_binding`), so the verifier's fold of an opened column
  is `foldAt` (`foldAt_of_cols`).
* **Part F, level 4** (finding): the tail batches level 4's queries into Pf's claim
  (`lvC_five_eq`), while `finP 4` checks them directly and asserts Pf's initial claim is P1.4's
  final claim (A.9). See the RESULT.
* **Part G**: controls.
-/

namespace FR.Snd
open RecursionFast FR.Merkle Finset

set_option linter.constructorNameAsVariable false

/-! ## Part A: positions and prefix reads -/

theorem lig_pos_check : (List.range 5).all (fun i => decide (p1Start 0 ≤ p1Start i) &&
    decide (p3S0 i ≤ p3S0 4)) = true := by
  unfold p1Start p3S0 phStart; rw [fsStarts_eq]; decide

theorem lig_pos {i : ℕ} (hi : i < 5) : p1Start 0 ≤ p1Start i ∧ p3S0 i ≤ p3S0 4 := by
  have h := lig_pos_check
  simp only [List.all_eq_true, List.mem_range, Bool.and_eq_true, decide_eq_true_eq] at h
  exact h i hi

/-- A prefix reads what the chain reads before its length. -/
theorem same_take (L es : Log) (n : ℕ) : Same L (es.take n) L es n :=
  same_of_agree L fun _ hq => entAt_take hq

theorem length_take_succ {es : Log} {p : ℕ} (hp : p < es.length) :
    (es.take (p + 1)).length = p + 1 := by
  rw [List.length_take]; omega

variable {W₀ : Log → Log → ℕ → K} {c₀ : Log → Log → K}

section Reads

variable (hF : FrontLocal W₀ c₀) {L es : Log} {i : ℕ} (hi : i < 5)
include hF hi

/-- **P1.i's first absorb**: off `D1 i`, level `i` is close and P1.i's initial claim is
`⟨Wᵢ, f⁽ⁱ⁾⟩`. -/
theorem p1_of_not_D1 (hl : p1Start i < es.length)
    (hD : ¬ D1 W₀ c₀ i L (es.take (p1Start i + 1))) :
    ¬ farL (kindOf es) L es i ∧ lvC c₀ i L es =
      ∑ y ∈ range (2 ^ nrP i (kindOf es)), lvW W₀ i L es y * fTab (kindOf es) L es i y := by
  set X := es.take (p1Start i + 1)
  have hS : Same L X L es (p1Start i + 1) := same_take L es (p1Start i + 1)
  have hX : X.length = p1Start i + 1 := length_take_succ hl
  have hc := capPos_lt hi
  have hk : kindOf X = kindOf es := hS.kind (by omega)
  have hr : hRnd X i = 0 := by unfold hRnd; rw [hX]; simp
  unfold D1 at hD
  rw [hk, hr, closeP_zero, not_not] at hD
  have hfX : ¬ farL (kindOf es) L X i := fun h => hD (Or.inl h)
  have hf : ¬ farL (kindOf es) L es i := (farL_same hS hi _ (by omega)).not.mp hfX
  refine ⟨hf, ?_⟩
  by_contra hne
  refine hD (Or.inr ⟨hfX, by rw [hX]; omega, ?_⟩)
  have ha : ans3 (p1Start i) (nrP i) X = 0 := by simp [ans3, hX]
  rw [ha, Wrong2]
  simp only [clR2, rchs2, List.range_zero, List.map_nil, bindAll, Nat.sub_zero]
  rw [lvT, hk, trueSum_tabs, lvC_same hF hS hi (by omega), lvW_same hF hS hi (by omega),
    fTab_same hS hi _ (by omega)]
  exact hne

/-- **C.i's absorb**: off `DCi i`, the next codeword is close to the column fold, and on a close
word P1.i's final claim is the folded claim's truth. -/
theorem c_of_not_DCi (hD : ¬ DCi W₀ c₀ i L (es.take (cStart i + 1))) :
    truthP2 (kindOf es) L es i ∧
      (¬ farL (kindOf es) L es i → c1 c₀ i L es = foldSum W₀ i L es) := by
  obtain ⟨hc, h1, h3, -, -⟩ := tail_pos hi
  have hS := same_take L es (cStart i + 1)
  have hk : kindOf (es.take (cStart i + 1)) = kindOf es := hS.kind (by omega)
  unfold DCi at hD
  rw [hk, truthP2_same hS hi _ le_rfl, farL_same hS hi _ (by omega),
    c1_same hF hS hi (by omega), foldSum_same hF hS hi (by omega)] at hD
  exact ⟨Classical.byContradiction fun h => hD (Or.inl h),
    fun hf => Classical.byContradiction fun h => hD (Or.inr ⟨hf, h⟩)⟩

omit hF in
/-- **P2.i's last answer**: off `DP2 i`, every queried fold is the next codeword's symbol. -/
theorem p2_of_not_DP2 (hl : p3S0 i < es.length)
    (hD : ¬ DP2 W₀ c₀ i L (es.take (p3S0 i + 1))) : truthP3 (kindOf es) L es i := by
  obtain ⟨-, -, -, h4, -⟩ := tail_pos hi
  have hS := same_take L es (p3S0 i + 1)
  have hX := length_take_succ hl
  have hk : kindOf (es.take (p3S0 i + 1)) = kindOf es := hS.kind (by omega)
  unfold DP2 msD at hD
  rw [ite_neg' (by rw [hX]; omega)] at hD
  unfold finP2 at hD
  rw [hk, truthP3_same hS hi _ le_rfl] at hD
  exact Classical.byContradiction fun h => hD (Or.inl h)

end Reads

/-! ## Part B: `LigeritoOut` and `ligerito_final` -/

/-- **What the Ligerito tail hands `final`** (BLUEPRINT §5.4 (2), A.10), on the chain `es` of the
log `L`, for the level-0 table `W₀` and initial claim `c₀` the front hands P1.0. -/
structure LigeritoOut (W₀ : Log → Log → ℕ → K) (c₀ : Log → Log → K) (L es : Log) : Prop where
  /-- Every level's word is `eᵢ`-close (`¬ far_i`). -/
  close : ∀ i < 5, ¬ farL (kindOf es) L es i
  /-- P1.i's initial claim is `⟨Wᵢ, f⁽ⁱ⁾⟩` (level 0: `c₀ = ⟨W₀, f⁽⁰⁾⟩`). -/
  claim : ∀ i < 5, lvC c₀ i L es =
    ∑ y ∈ range (2 ^ nrP i (kindOf es)), lvW W₀ i L es y * fTab (kindOf es) L es i y
  /-- P1.i's final claim is `⟨foldW Wᵢ, fold_z(f⁽ⁱ⁾)⟩`. -/
  folded : ∀ i < 5, c1 c₀ i L es = foldSum W₀ i L es
  /-- The next codeword agrees with the column fold on at least `nᵢ − eᵢ` positions. -/
  near : ∀ i < 5, truthP2 (kindOf es) L es i
  /-- The next message is the fold of level `i`'s decoded messages (level 4: the final one). -/
  fold : ∀ i < 5, truthC (kindOf es) L es i
  /-- Every queried fold is the next codeword's symbol. -/
  cons : ∀ i < 5, truthP3 (kindOf es) L es i
  /-- The consistency set is the joint agreement set. -/
  agree : ∀ i < 5, consSet (kindOf es) L es i =
    jointAgree (wordK (kindOf es) L es i) (decodeL (kindOf es) L es i)

/-- **`ligerito_final`** (BLUEPRINT §5.4 (2)): off the tail's dooms on every prefix of the chain
from P1.0 to P2.4's last answer, and with the Hide doom on the chain, the five levels decode
uniquely and consistently, and the claim RS/B′ hand P1.0 is `⟨W₀, f⁽⁰⁾⟩`. -/
theorem ligerito_final (hF : FrontLocal W₀ c₀) {L es : Log} (hlen : p3S0 4 < es.length)
    (hD : ∀ p, p1Start 0 ≤ p → p < es.length → ¬ DT W₀ c₀ (phOf p) L (es.take (p + 1)))
    (hH : DH L es) : LigeritoOut W₀ c₀ L es := by
  have hlv : ∀ i < 5, ¬ farL (kindOf es) L es i ∧ (lvC c₀ i L es =
      ∑ y ∈ range (2 ^ nrP i (kindOf es)), lvW W₀ i L es y * fTab (kindOf es) L es i y) ∧
      truthP2 (kindOf es) L es i ∧ c1 c₀ i L es = foldSum W₀ i L es ∧
      truthP3 (kindOf es) L es i := by
    intro i hi
    obtain ⟨hp0, hp4⟩ := lig_pos hi
    obtain ⟨-, -, h3, h4, -⟩ := tail_pos hi
    obtain ⟨g1, g2, -, g4, -⟩ := tail_ph hi
    have hP := hD (p1Start i) hp0 (by omega)
    rw [g1, DT_P1 W₀ c₀ hi] at hP
    have hC := hD (cStart i) (by omega) (by omega)
    rw [g2, DT_C W₀ c₀ hi] at hC
    have h2 := hD (p3S0 i) (by omega) (by omega)
    rw [g4, DT_P2 W₀ c₀ hi] at h2
    obtain ⟨hf, hcl⟩ := p1_of_not_D1 hF hi (by omega) hP
    obtain ⟨hn, hfo⟩ := c_of_not_DCi hF hi hC
    exact ⟨hf, hcl, hn, hfo hf, p2_of_not_DP2 hi (by omega) h2⟩
  have hfold : ∀ i < 5, truthC (kindOf es) L es i := fun i hi =>
    truthC_of hi (hlv i hi).1 (hlv i hi).2.2.1
  refine ⟨fun i hi => (hlv i hi).1, fun i hi => (hlv i hi).2.1, fun i hi => (hlv i hi).2.2.2.1,
    fun i hi => (hlv i hi).2.2.1, hfold, fun i hi => (hlv i hi).2.2.2.2, fun i hi => ?_⟩
  obtain ⟨hp0, hp4⟩ := lig_pos hi
  obtain ⟨-, -, h3, h4, -⟩ := tail_pos hi
  exact consSet_eq_of_DH hi (by omega) hH (hlv i hi).1 (hfold i hi)

/-- **Level 0's claim** (what RS/B′ hand off): `c₀ = ⟨W₀, ι ∘ fF⟩` over level 0's variables. -/
theorem LigeritoOut.claim0 {L es : Log} (h : LigeritoOut W₀ c₀ L es) :
    c₀ L es = ∑ y ∈ range (2 ^ nrP 0 (kindOf es)),
      W₀ L es y * algebraMap F K (fF (kindOf es) L es y) := by
  rw [show c₀ L es = lvC c₀ 0 L es from rfl, h.claim 0 (by norm_num)]
  exact sum_congr rfl fun y _ => by rw [fTab_F (h.close 0 (by norm_num))]; rfl

/-- **`f⁽⁰⁾` is the committed polynomial**: every prefix of the chain past `cap₀`'s absorb reads
the same close level-0 word, the same decoded messages and the same F-valued `f⁽⁰⁾`. -/
theorem LigeritoOut.level0_committed {L es : Log} (h : LigeritoOut W₀ c₀ L es) {p : ℕ}
    (hp : capPos 0 < p) :
    ¬ farL (kindOf es) L (es.take p) 0 ∧ msgOf (kindOf es) L (es.take p) 0 = msgOf (kindOf es) L es 0 ∧
      fF (kindOf es) L (es.take p) = fF (kindOf es) L es := by
  have hS := same_take L es p
  refine ⟨(farL_same hS (by norm_num) _ hp).not.mpr (h.close 0 (by norm_num)),
    msgOf_same hS (by norm_num) _ hp, ?_⟩
  funext e; simp only [fF, fTab_same hS (by norm_num) _ hp]

/-! ## Part C: from the walk -/

/-- A prefix of the chain from P1.0 on is doomed by the tail only if the composed doom holds. -/
theorem not_DT_of_not_DC {RejF : Log → Log → Prop} {DF : ℕ → Log → Log → Prop} {L X : Log}
    (hp : p1Start 0 ≤ X.length - 1) (h : ¬ DC (RejC RejF c₀) (Dp (DkC DF W₀ c₀)) L X) :
    ¬ DT W₀ c₀ (phOf (X.length - 1)) L X := by
  intro hT
  refine h (Or.inr ?_)
  unfold DPos Dp
  rwa [DkC_ge (phOf_ge_26 hp)]

/-- **Off a doom on every prefix**: with no escape, `ChainStab`, and `¬ D` at the chain's end, `D`
fails on every prefix of the chain, on the log itself. -/
theorem not_D_prefix {D : Log → Log → Prop} (hS : ChainStab D) {L : Log} (hb : ¬ Bad L)
    (hE : ¬ EscG D L) {j : ℕ} (hci : IsChain L j)
    (hend : ¬ D L (entriesOf L (pathOf L j))) {p : ℕ}
    (hp : p < (entriesOf L (pathOf L j)).length) :
    ¬ D L ((entriesOf L (pathOf L j)).take (p + 1)) := by
  have hm : p < (pathOf L j).length := by rwa [length_entriesOf] at hp
  have hw := walk_back hS hb hE hci ((hS L j hb hci).not.mpr hend) hm
  have hc := isChain_prefix hci hm
  rw [← entriesOf_prefix L j hm] at hw ⊢
  exact (hS L _ hb hc).not.mp hw

/-- **`ligerito_final` from what `final` has** (A.10): a non-bad log, no escape of the composed
doom or of the Hide doom, the composed doom's `ChainStab`, and the composed doom false at the end
of a chain that has passed P2.4. -/
theorem ligerito_final_of_walk {RejF : Log → Log → Prop} {DF : ℕ → Log → Log → Prop}
    (hF : FrontLocal W₀ c₀) (hS : ChainStab (DC (RejC RejF c₀) (Dp (DkC DF W₀ c₀))))
    {L : Log} (hb : ¬ Bad L) (hE : ¬ EscG (DC (RejC RejF c₀) (Dp (DkC DF W₀ c₀))) L)
    (hEH : ¬ EscG DH L) {j : ℕ} (hci : IsChain L j)
    (hlen : p3S0 4 < (entriesOf L (pathOf L j)).length)
    (hend : ¬ DC (RejC RejF c₀) (Dp (DkC DF W₀ c₀)) L (entriesOf L (pathOf L j))) :
    LigeritoOut W₀ c₀ L (entriesOf L (pathOf L j)) := by
  refine ligerito_final hF hlen (fun p hp hpl => ?_) (DH_of_noEsc hb hEH hci)
  have h := not_D_prefix hS hb hE hci hend hpl
  have hX := length_take_succ hpl
  have := not_DT_of_not_DC (W₀ := W₀) (c₀ := c₀) (by rw [hX]; omega) h
  rwa [hX, Nat.add_sub_cancel] at this

/-! ## Part D: Pf's end (the fold rounds' binding) -/

/-- Binding every variable of a table of `2^n` entries at a list of `n` challenges evaluates its
extension there. -/
theorem bindL_ofFn_mle {n : ℕ} (g : ℕ → K) (cs : List K) (hl : cs.length = n) :
    tbl 0 (bindL (Array.ofFn (n := 2 ^ n) fun y => g y) cs) 0 = mleN n g (ptOf n cs) := by
  subst hl
  rw [bindL_mle _ _ (Array.size_ofFn ..), mleN, pt_eq_ptOf]
  congr 1
  funext u; exact ofFn_getD g u.2

/-- Pf's seven challenges, as a point. -/
def pfPt (es : Log) : Fin 7 → K := ptOf 7 (rchs2 pfStart chK es 7)

/-- **Pf's tables bound at all seven challenges**: the summand at the tables' extensions,
`W̃_f(ρ)·final̂(ρ)`. -/
theorem trueSum_tPf_end (L es : Log) :
    trueSum e2 (bindAll (tPf W₀ L es) (rchs2 pfStart chK es 7)) 0 =
      mleN 7 (wPf W₀ L es) (pfPt es) * mleN 7 (finalAt es) (pfPt es) := by
  have hl : (rchs2 pfStart chK es 7).length = 7 := by simp [rchs2]
  rw [trueSum_e2, pow_zero, sum_range_one, getD_bindAll, getD_bindAll, tPf, tabs_getD0,
    tabs_getD1, pfPt, ← bindL_ofFn_mle _ _ hl, ← bindL_ofFn_mle _ _ hl]
  rfl

/-- **Pf's doom at the chain's end** is the failure of the final check in the tables' extensions:
the claim after Pf's seven rounds is not `W̃_f(ρ)·final̂(ρ)`. -/
theorem DPf_end_iff {L es : Log} (hl : pfStart + 14 ≤ es.length) :
    DPf W₀ c₀ L es ↔ clR2 pfStart 32 readK chK (lvC c₀ 5) L es 7 ≠
      mleN 7 (wPf W₀ L es) (pfPt es) * mleN 7 (finalAt es) (pfPt es) := by
  have ha : ans3 pfStart (fun _ => 7) es = 7 := by
    unfold ans3; show min 7 ((es.length - pfStart) / 2) = 7; omega
  unfold DPf D2 Wrong2
  beta_reduce
  rw [ha, Nat.sub_self, trueSum_tPf_end]
  exact ⟨fun h => h.2, fun h => ⟨by omega, h⟩⟩

/-! ### The level tables' extensions at ℕ-indexed points (`finPf`'s level steps) -/

/-- The extension of `W`'s first `2^n` entries at the ℕ-indexed point `ρ`. -/
noncomputable def mleP (n : ℕ) (W ρ : ℕ → K) : K := mleN n W (fun v => ρ v)

theorem fin_append_nat {a b : ℕ} (s ρ : ℕ → K) (v : Fin (a + b)) :
    Fin.append (fun u : Fin a => s u) (fun u : Fin b => ρ u) v =
      if (v : ℕ) < a then s v else ρ (v - a) := by
  refine Fin.addCases (fun u => ?_) (fun u => ?_) v
  · simp [Fin.append_left, u.2]
  · simp [Fin.append_right]

theorem mleP_zero (W ρ : ℕ → K) : mleP 0 W ρ = W 0 := by
  rw [mleP, mleN, mle_zero]; rfl

/-- **One level step** (A.9 `finPf`'s `lvStepV`, at the spec): level `i + 1`'s table at `P` is
`û(P₀)·(Wᵢ(sᵢ, P[1..]) + Σ_q eq(κ_c, bits₉(q))·tensorW(p_q, P[1..]))`. -/
theorem mleP_lvW_succ {i : ℕ} (hi : i + 1 < 5) (L es : Log) (P : ℕ → K) :
    mleP (nrP (i + 1) (kindOf es)) (lvW W₀ (i + 1) L es) P = uHat (P 0) *
      (mleP (nrP i (kindOf es)) (lvW W₀ i L es)
          (fun v => if v < (lvl (kindOf es) i).ell then sAt es i v
            else P (v - (lvl (kindOf es) i).ell + 1)) +
        ∑ q ∈ range (lvl (kindOf es) i).t, algebraMap F K (eqBits (kcAt es i) 9 q) *
          tensorTwin D logNMax (mLog (kindOf es) i)
            (fun v => if v < mLog (kindOf es) i then P (v + 1) else 0)
            (qPos (kindOf es) es i q)) := by
  obtain ⟨-, he, hm⟩ := lv_next (kindOf es) hi
  have hn : nrP (i + 1) (kindOf es) = mLog (kindOf es) i + 1 := by unfold nrP; omega
  rw [hn]
  unfold mleP
  show mleN _ (nextW (kindOf es) es i (lvW W₀ i L es)) _ = _
  rw [mleN_nextW]
  have hpt : Fin.append (fun v : Fin (lvl (kindOf es) i).ell => sAt es i v)
      (Fin.tail fun v : Fin (mLog (kindOf es) i + 1) => P v) =
      fun v : Fin ((lvl (kindOf es) i).ell + mLog (kindOf es) i) =>
        (fun v => if v < (lvl (kindOf es) i).ell then sAt es i v
          else P (v - (lvl (kindOf es) i).ell + 1)) v := by
    funext v; exact fin_append_nat (sAt es i) (fun w => P (w + 1)) v
  have htl : (fun v => if h : v < mLog (kindOf es) i then
      Fin.tail (fun v : Fin (mLog (kindOf es) i + 1) => P v) ⟨v, h⟩ else 0) =
      fun v => if v < mLog (kindOf es) i then P (v + 1) else 0 := by
    funext v; split_ifs <;> rfl
  rw [hpt, htl]
  rfl

/-- The point of a table indexed by `ℕ` (`Fin.append` of a prefix and the rest, as in
`mle_split`). -/
theorem mleP_pt_split (m k : ℕ) (W ρ : ℕ → K) :
    mleP (m + k) W ρ = mle (fun u : Fin (2 ^ (m + k)) => W u)
      (Fin.append (fun v : Fin m => ρ v) (fun v : Fin k => ρ (m + v))) := by
  unfold mleP mleN
  congr 1
  funext v
  rw [fin_append_nat ρ (fun u => ρ (m + u))]
  split_ifs with h
  · rfl
  · congr 1; omega

/-- **Zero padding** (A.9 `finPf`'s `P30` factor): a table zero from `2^m` on has, over `n ≥ m`
variables, the extension over `m` times `Π_{m ≤ v < n} (1 − ρ_v)`. -/
theorem mleP_pad {m n : ℕ} (hmn : m ≤ n) {W : ℕ → K} (hW : ∀ x, 2 ^ m ≤ x → W x = 0)
    (ρ : ℕ → K) : mleP n W ρ = mleP m W ρ * ∏ v ∈ Ico m n, (1 - ρ v) := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hmn
  rw [mleP_pt_split, mle_split]
  have hin : ∀ u₁ : Fin (2 ^ m), mle (fun u₂ : Fin (2 ^ k) =>
      (fun u : Fin (2 ^ (m + k)) => W u) (join u₁ u₂)) (fun v : Fin k => ρ (m + v)) =
      (∏ v ∈ Ico m (m + k), (1 - ρ v)) * W u₁ := fun u₁ => by
    have hf : (fun u₂ : Fin (2 ^ k) => (fun u : Fin (2 ^ (m + k)) => W u) (join u₁ u₂)) =
        fun u₂ => if u₂ = 0 then W u₁ else 0 := by
      funext u₂
      simp only [join]
      split_ifs with h
      · subst h; simp
      · refine hW _ ?_
        have : 1 ≤ u₂.val := Nat.one_le_iff_ne_zero.mpr fun h' => h (Fin.ext h')
        nlinarith [u₁.2, Nat.one_le_two_pow (n := m)]
    rw [hf, mle]
    simp only [mul_ite, mul_zero, sum_ite_eq', mem_univ, ite_true, eq_cube]
    congr 1
    rw [prod_Ico_eq_prod_range, Nat.add_sub_cancel_left, ← Fin.prod_univ_eq_prod_range]
    exact prod_congr rfl fun v _ => by simp
  refine (sum_congr rfl fun u₁ _ => congrArg _ (hin u₁)).trans ?_
  unfold mleP mleN mle
  rw [sum_mul]
  exact sum_congr rfl fun u _ => by ring

/-! ## Part E: Merkle binding (`cap_binding`) -/

/-- **An opened column is the committed one**: on a log without collisions, if the path of position
`p` from `col` evaluates to its cap entry, then `colOf` reads `col` there. -/
theorem colOf_of_path {κ : Kind} {L es : Log} (hc : ¬ Collision L) {i p : ℕ} {col : ByteArray}
    {ss : List Digest} (hss : ss.length = (lvl κ i).sib)
    (h : (openPath (frEnc i) col p ss).runLog L = some (capDig es i (p / 2 ^ (lvl κ i).sib))) :
    colOf κ L es i p = some col := by
  have h' := cap_binding hc h
  rw [hss] at h'
  exact h'

/-- **The verifier's fold of an opened column is `foldAt`**: `Σ_r eq(sᵢ, r)·col_r`, the column's F
elements read as the word's rows. -/
theorem foldAt_of_cols {κ : Kind} {L es : Log} (hc : ¬ Collision L) {i : ℕ}
    {j : Fin (2 ^ (lvl κ i).logN)} {col : ByteArray} {ss : List Digest}
    (hss : ss.length = (lvl κ i).sib)
    (h : (openPath (frEnc i) col j ss).runLog L = some (capDig es i (j / 2 ^ (lvl κ i).sib))) :
    foldAt κ L es i j =
      ∑ r : Fin (lvl κ i).rows, eqBits (sAt es i) (lvl κ i).ell r *
        algebraMap F K (readF col (16 * r)) := by
  have hcol := colOf_of_path hc hss h
  refine sum_congr rfl fun r _ => ?_
  simp only [wordK, wordOf, hcol, Option.map_some, Option.getD_some]

/-! ## Part F: level 4 (finding: the tail batches level 4, the verifier does not) -/

/-- **The tail's Pf claim batches level 4's queries** (`vNext 4`), unlike `finP 4`, which asserts
Pf's initial claim is P1.4's final claim `c1 4` (A.9, `FRVIRFinalsSG.finP4`). -/
theorem lvC_five_eq (L es : Log) :
    lvC c₀ 5 L es = c1 c₀ 4 L es + ∑ q ∈ range (lvl (kindOf es) 4).t,
      K.smulF (eqBits (kcAt es 4) 9 q) (foldAtN (kindOf es) L es 4 (qPos (kindOf es) es 4 q)) :=
  rfl

/-- **The conflict**: the tail's check of Pf's first round (`RejT`) and the verifier's
(`g(0) + g(1) = c1 4`, `finP 4` with `initClaim "Pf" = free`) hold together only if level 4's
batched folds vanish at P3.4's `κ_c`. -/
theorem pf_round0_conflict {L es : Log} (hR : ¬ RejT c₀ L es) (hl : pfStart < es.length)
    (hV : peval (g2At pfStart 32 readK es 0) 0 + peval (g2At pfStart 32 readK es 0) 1 =
      c1 c₀ 4 L es) :
    ∑ q ∈ range (lvl (kindOf es) 4).t,
      K.smulF (eqBits (kcAt es 4) 9 q) (foldAtN (kindOf es) L es 4 (qPos (kindOf es) es 4 q)) =
      0 := by
  have hc : Chk2 pfStart 32 readK chK (lvC c₀ 5) L es 0 :=
    Classical.byContradiction fun h => hR (Or.inr ⟨0, by norm_num, by omega, h⟩)
  unfold Chk2 at hc
  rw [hV, clR2, lvC_five_eq] at hc
  exact (add_eq_left.mp hc.symm)

/-! ## Part G: controls -/

theorem bytesAt_empty (o n : ℕ) : bytesAt ByteArray.empty o n = Vector.replicate n 0 := by
  ext k hk; simp [bytesAt, byteAt, Vector.getElem_ofFn]

theorem msgAt_nil (p : ℕ) : msgAt [] p = ByteArray.empty := by
  simp [msgAt, entAt]; decide

theorem K_ofBytes_zero : K.ofBytes (Vector.replicate 32 0) = 0 := by decide

theorem readK_nil (p o : ℕ) : readK (msgAt [] p) o = 0 := by
  rw [readK, msgAt_nil, bytesAt_empty, K_ofBytes_zero]

/-- On the empty log the decoded rows are `0` (the zero word decodes to the zero codeword). -/
theorem decodeL_nil (κ : Kind) (es : Log) {i : ℕ} (hi : i < 5) : decodeL κ [] es i = 0 := by
  obtain ⟨hV, hJ⟩ := decodeL_spec (not_farL_nil κ es i)
  obtain ⟨hek, hN, -, -, hn⟩ := lv_params κ hi
  have hw : wordK κ [] es i = 0 := by funext r p; simp [wordK, wordOf_nil]
  funext r
  refine rs_eq_of_agree (Dpts_injective (hn ▸ hN)) (hV r) (Submodule.zero_mem _) _
    (le_trans (by rw [← hn]; omega) hJ) fun j hj => ?_
  rw [mem_jointAgree, hw] at hj
  exact (hj r).symm

theorem msgOf_nil (κ : Kind) (es : Log) {i : ℕ} (hi : i < 5) : msgOf κ [] es i = 0 := by
  funext r x
  by_cases hr : r < (lvl κ i).rows
  · by_cases hx : x < 2 ^ mLog κ i
    · have hc : enc D (2 ^ (lvl κ i).logN) _ (0 : Fin (2 ^ mLog κ i) → K) =
          decodeL κ [] es i ⟨r, hr⟩ := by
        rw [decodeL_nil κ es hi]
        exact (encL (M := K) D (2 ^ (lvl κ i).logN) (2 ^ mLog κ i)).map_zero
      exact msgOf_eq hi hc ⟨x, hx⟩
    · simp [msgOf, hr, hx]
  · simp [msgOf, hr]

theorem nextMsg_nil (κ : Kind) (i : ℕ) : nextMsg κ [] [] i = 0 := by
  funext x
  unfold nextMsg
  split_ifs with h
  · rw [msgOf_nil κ [] h]; simp
  · simp [finalAt, readK_nil]

theorem c1_nil (c₀ : Log → Log → K) {i : ℕ} (hi : i < 5) : c1 c₀ i [] [] = 0 := by
  have h1 : 0 < hEll i := by interval_cases i <;> decide
  obtain ⟨l, hl⟩ : ∃ l, hEll i = l + 1 := ⟨hEll i - 1, by omega⟩
  rw [c1, hl, clR2]
  simp [g2At, readK_nil, peval]

/-- On the empty chain of the empty log with `c₀ = 0`, every level's claim is `0`. -/
theorem lvC_nil : ∀ i ≤ 5, lvC (fun _ _ => (0 : K)) i [] [] = 0
  | 0, _ => rfl
  | i + 1, hi => by
    show vNext _ [] [] i (c1 _ i [] []) = 0
    rw [c1_nil _ (by omega), vNext]
    simp [foldAtN, foldAt_nil, K.smulF_eq_mul]

/-- **Control (positive)**: `LigeritoOut` holds on the empty chain of the empty log with `W₀ = 0`
and `c₀ = 0` (every word, message and claim is `0`). -/
theorem ligeritoOut_nil :
    LigeritoOut (fun _ _ _ => (0 : K)) (fun _ _ => (0 : K)) [] [] := by
  have hcons : ∀ i < 5, consSet (kindOf []) [] [] i = univ := fun i hi => by
    ext j
    simp [consSet, foldAt_nil, nextMsg_nil _ i, encAt_eq_sum]
  refine ⟨fun i _ => not_farL_nil _ _ i, fun i hi => ?_, fun i hi => ?_, fun i hi => ?_,
    fun i hi x _ => ?_, fun i hi q _ => ?_, fun i hi => ?_⟩
  · rw [lvC_nil i (by omega)]; simp [fTab, msgOf_nil _ _ hi]
  · rw [c1_nil _ hi, foldSum]; simp [foldMsg, msgOf_nil _ _ hi]
  · rw [truthP2, hcons i hi, card_univ, Fintype.card_fin, lvN]; exact Nat.sub_le _ _
  · rw [nextMsg_nil _ i]; simp [foldMsg, msgOf_nil _ _ hi]
  · simp [consErr, foldAtN, foldAt_nil, nextMsg_nil _ i, encAt_eq_sum]
  · rw [hcons i hi, decodeL_nil _ _ hi]
    have hw : wordK (kindOf []) [] [] i = 0 := by funext r p; simp [wordK, wordOf_nil]
    rw [hw]; ext j; simp

/-- **Control (negative)**: with `c₀ = 1` the same empty chain fails `LigeritoOut` (level 0's
claim `1 ≠ ⟨0, f⁽⁰⁾⟩ = 0`): the claim field is not vacuous. -/
theorem not_ligeritoOut_one :
    ¬ LigeritoOut (fun _ _ _ => (0 : K)) (fun _ _ => (1 : K)) [] [] := fun h => by
  have := h.claim 0 (by norm_num)
  simp only [lvC, lvW, zero_mul, sum_const_zero] at this
  exact one_ne_zero this

end FR.Snd
