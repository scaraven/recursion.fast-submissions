-- New for `flock-recursive` (BLUEPRINT §5.4 step 2, A.10 "What `final` then gets"; stage S-G2).
-- RET-1: position-free declarations moved to `FRSoundnessCoreTail`.
import FRSoundnessCompose
import FRSoundnessCoreTail

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
* **Part D, Pf's end**: `DPf` at the chain's end is `¬ truthP3 4` or the failure of the final
  check `c_{Pf} = Ŵ(ρ)·final̂(ρ)` in the tables' extensions at Pf's challenges (`DPf_end_iff`);
  the level step at the spec (`mleP_lvW_succ`) and the zero padding (`mleP_pad`).
* **Part E, Merkle binding**: a path that evaluates on the log to the cap entry fixes the column
  `colOf` reads (`colOf_of_path`, from `cap_binding`), so the verifier's fold of an opened column
  is `foldAt` (`foldAt_of_cols`).
* **Part F, level 4 and Pf against `finP 4`/`finPf`** (pass 2, after the tail fix): `RejT`'s Pf
  round 0 is the verifier's (`pf_round0_agree`); `finP 4`'s direct checks give `truthP3 4`
  (`truthP3_four_of_cols`); `DPf` at the end is `relPf`'s failure in `Ŵ₄(P₄)·pad·final̂`
  (`wHatL`, `mleN_wPf`, `DPf_end_chain`).
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
    ¬ farL (kindOf es) L (es.take p) 0 ∧
      msgOf (kindOf es) L (es.take p) 0 = msgOf (kindOf es) L es 0 ∧
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

/-- **Pf's doom at the chain's end** is the failure of `finP 4`'s direct checks or of the final
check in the tables' extensions: the claim after Pf's seven rounds is not `W̃_f(ρ)·final̂(ρ)`. -/
theorem DPf_end_iff {L es : Log} (hl : pfStart + 14 ≤ es.length) :
    DPf W₀ c₀ L es ↔ ¬ truthP3 (kindOf es) L es 4 ∨ clR2 pfStart 32 readK chK (lvC c₀ 5) L es 7 ≠
      mleN 7 (wPf W₀ L es) (pfPt es) * mleN 7 (finalAt es) (pfPt es) := by
  have ha : ans3 pfStart (fun _ => 7) es = 7 := by
    unfold ans3; show min 7 ((es.length - pfStart) / 2) = 7; omega
  unfold DPf D2 Wrong2
  beta_reduce
  rw [ha, Nat.sub_self, trueSum_tPf_end]
  exact or_congr Iff.rfl ⟨fun h => h.2, fun h => ⟨by omega, h⟩⟩

/-! ### The level tables' extensions at ℕ-indexed points (`finPf`'s level steps) -/

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

/-! ## Part F: level 4 and Pf's end, against `finP 4` and `finPf` (pass 2)

The tail now matches the verifier (S-G2 pass 2): Pf starts from P1.4's final claim
(`lvC_five`), `wPf` is the zero-padded `wFold 4`, and level 4's queries are a background of Pf's
doom (`¬ truthP3 4`), refuted by `finP 4`'s direct checks (`truthP3_four_of_cols`). -/

/-- **Control (pass 2)**: `RejT`'s check of Pf's first round is the verifier's
(`g(0) + g(1) = claim0 Pf = claimN P1.4`, `finP 4` with `initClaim "Pf" = free`). -/
theorem pf_round0_agree (L es : Log) :
    Chk2 pfStart 32 readK chK (lvC c₀ 5) L es 0 ↔
      peval (g2At pfStart 32 readK es 0) 0 + peval (g2At pfStart 32 readK es 0) 1 =
        c1 c₀ 4 L es := by
  rw [Chk2, clR2, lvC_five]

/-- **`finP 4`'s direct checks give `truthP3 4`**: every queried position's opened column has a
path to its cap entry and its fold is `Enc₄(final)` there. -/
theorem truthP3_four_of_cols {L es : Log} (hc : ¬ Collision L)
    (hq : ∀ q < (lvl (kindOf es) 4).t, ∃ col : ByteArray, ∃ ss : List Digest,
      ss.length = (lvl (kindOf es) 4).sib ∧
      (openPath (frEnc 4) col (qPos (kindOf es) es 4 q) ss).runLog L =
        some (capDig es 4 (qPos (kindOf es) es 4 q / 2 ^ (lvl (kindOf es) 4).sib)) ∧
      ∑ r : Fin (lvl (kindOf es) 4).rows, eqBits (sAt es 4) (lvl (kindOf es) 4).ell r *
          algebraMap F K (readF col (16 * r)) =
        encAt (kindOf es) 4 (finalAt es) (qPos (kindOf es) es 4 q)) :
    truthP3 (kindOf es) L es 4 := by
  intro q hq'
  obtain ⟨col, ss, hss, hpath, hfold⟩ := hq q hq'
  have hlt : qPos (kindOf es) es 4 q < 2 ^ (lvl (kindOf es) 4).logN := idx_lt _ _ _
  have hn : nextMsg (kindOf es) L es 4 = finalAt es := by
    funext x; simp [nextMsg, nLevels]
  rw [consErr, foldAtN, dite_eq_left_of_eq_true (eq_true hlt),
    foldAt_of_cols (j := ⟨_, hlt⟩) hc hss hpath, hfold, hn, sub_self]

/-- Pf's challenges as an ℕ-indexed point. -/
def pfP (es : Log) (v : ℕ) : K := (rchs2 pfStart chK es 7).getD v 0

/-- Level `k`'s point at the chain's end, from level 4 down (`d = 4 − k` steps). -/
def ptD (es : Log) : ℕ → ℕ → ℕ → K
  | 0, k, v => if v < hEll k then sAt es k v else pfP es (v - hEll k)
  | d + 1, k, v => if v < hEll k then sAt es k v else ptD es d (k + 1) (v - hEll k + 1)

/-- **Level `k`'s point** (A.9 `finPf`'s `Pₖ`, `tailRegs`): `sₖ`, then level `k + 1`'s point from
its coordinate 1; level 4: `s₄`, then Pf's challenges. -/
def ptL (es : Log) (k : ℕ) : ℕ → K := ptD es (4 - k) k

theorem ptL_lt {k : ℕ} (hk : k < 4) (es : Log) :
    ptL es k = fun v => if v < hEll k then sAt es k v else ptL es (k + 1) (v - hEll k + 1) := by
  unfold ptL; rw [show 4 - k = (4 - (k + 1)) + 1 by omega]; rfl

/-- **`Ŵₖ(Pₖ)`** (A.9 `finPf`'s `wV`, at the spec): `W̃₀(P₀)`, then the level steps `lvStepV`. -/
noncomputable def wHatL (W₀ : Log → Log → ℕ → K) (L es : Log) : ℕ → K
  | 0 => mleP (nrP 0 (kindOf es)) (W₀ L es) (ptL es 0)
  | k + 1 => uHat (ptL es (k + 1) 0) * (wHatL W₀ L es k +
      ∑ q ∈ range (lvl (kindOf es) k).t, algebraMap F K (eqBits (kcAt es k) 9 q) *
        tensorTwin D logNMax (mLog (kindOf es) k)
          (fun v => if v < mLog (kindOf es) k then ptL es (k + 1) (v + 1) else 0)
          (qPos (kindOf es) es k q))

/-- **The level tables at their points are `wHatL`** (levels `0 … 4`). -/
theorem mleP_lvW_chain (L es : Log) : ∀ k ≤ 4,
    mleP (nrP k (kindOf es)) (lvW W₀ k L es) (ptL es k) = wHatL W₀ L es k
  | 0, _ => rfl
  | k + 1, hk => by
    rw [mleP_lvW_succ (by omega), wHatL, ← mleP_lvW_chain L es k (by omega), ptL_lt (k := k)
      (by omega), lvl_ell (kindOf es) (show k < 5 by omega)]

/-- **Pf's weight at Pf's challenges** is `Ŵ₄(P₄)` times the padding `Π_{μ ≤ v < 7} (1 − ρ_v)`
(A.9 `finPf`: `wV · padV`). -/
theorem mleN_wPf (L es : Log) :
    mleN 7 (wPf W₀ L es) (pfPt es) =
      wHatL W₀ L es 4 * ∏ v ∈ Ico (mLog (kindOf es) 4) 7, (1 - pfP es v) := by
  have h1 : mleN 7 (wPf W₀ L es) (pfPt es) = mleP 7 (wPf W₀ L es) (pfP es) := rfl
  have h2 : mleP (mLog (kindOf es) 4) (wPf W₀ L es) (pfP es) =
      mleP (mLog (kindOf es) 4) (wFold W₀ 4 L es) (pfP es) := by
    unfold mleP mleN; congr 1; funext u; simp [wPf, u.2]
  have h3 : mleP (mLog (kindOf es) 4) (wFold W₀ 4 L es) (pfP es) =
      mleP (nrP 4 (kindOf es)) (lvW W₀ 4 L es) (ptL es 4) := by
    unfold mleP wFold
    rw [mleN_foldW]
    unfold nrP mleN
    congr 1
    funext v
    have he := lvl_ell (kindOf es) (show 4 < 5 by norm_num)
    rw [fin_append_nat (sAt es 4) (pfP es)]
    simp only [he]
    rfl
  rw [h1, mleP_pad (mLog4_le (kindOf es)) (W := wPf W₀ L es)
    (fun x hx => by simp only [wPf]; rw [ite_neg' (by omega)]) (pfP es),
    h2, h3, mleP_lvW_chain L es 4 le_rfl]

/-- **Pf's doom at the chain's end, in `finPf`'s terms** (A.9 `relPf`:
`claimN(Pf) = Ŵ₄(P₄)·pad·final̂(sf)`; and `finP 4`'s direct checks). -/
theorem DPf_end_chain {L es : Log} (hl : pfStart + 14 ≤ es.length) :
    DPf W₀ c₀ L es ↔ ¬ truthP3 (kindOf es) L es 4 ∨
      clR2 pfStart 32 readK chK (lvC c₀ 5) L es 7 ≠ wHatL W₀ L es 4 *
        (∏ v ∈ Ico (mLog (kindOf es) 4) 7, (1 - pfP es v)) * mleN 7 (finalAt es) (pfPt es) := by
  rw [DPf_end_iff hl, mleN_wPf]

/-! ## Part H: `FinalLaw` from the tail's end, the front and the extractor (pass 2) -/

/-- **What an accepted SNARK run gives on the log for the tail** (`runLog_chain` and the finals'
semantics: P1.i's and Pf's round checks, `finP 4`'s direct checks, `finPf`'s `relPf`), on the
chain of entry `j`, with the front's asserts passed. -/
structure AcceptTail (RejF : Log → Log → Prop) (W₀ : Log → Log → ℕ → K) (c₀ : Log → Log → K)
    (L : Log) (j : ℕ) : Prop where
  /-- The accepted run's Fiat–Shamir entries are a chain of the log. -/
  chain : IsChain L j
  /-- The chain has passed Pf's last round. -/
  len : pfStart + 14 ≤ (entriesOf L (pathOf L j)).length
  /-- The front's asserted checks pass. -/
  rejF : ¬ RejF L (entriesOf L (pathOf L j))
  /-- Every P1.i round check holds against the tail's claims. -/
  p1 : ∀ i < 5, ∀ l < hEll i,
    Chk2 (p1Start i) 32 readK chK (lvC c₀ i) L (entriesOf L (pathOf L j)) l
  /-- Every Pf round check holds (round 0 from `c1 4`, `pf_round0_agree`). -/
  pf : ∀ l < 7, Chk2 pfStart 32 readK chK (lvC c₀ 5) L (entriesOf L (pathOf L j)) l
  /-- `finP 4`'s direct checks (`truthP3_four_of_cols`). -/
  lvl4 : truthP3 (kindOf (entriesOf L (pathOf L j))) L (entriesOf L (pathOf L j)) 4
  /-- `finPf`'s `relPf` at the spec (`DPf_end_chain`). -/
  fin : clR2 pfStart 32 readK chK (lvC c₀ 5) L (entriesOf L (pathOf L j)) 7 =
    wHatL W₀ L (entriesOf L (pathOf L j)) 4 *
      (∏ v ∈ Ico (mLog (kindOf (entriesOf L (pathOf L j))) 4) 7,
        (1 - pfP (entriesOf L (pathOf L j)) v)) *
      mleN 7 (finalAt (entriesOf L (pathOf L j))) (pfPt (entriesOf L (pathOf L j)))

/-- **`hend`**: on an accepted chain the composed doom is false at its end (phase 51, Pf). -/
theorem not_DC_end {RejF : Log → Log → Prop} {DF : ℕ → Log → Log → Prop} {L : Log} {j : ℕ}
    (h : AcceptTail RejF W₀ c₀ L j) :
    ¬ DC (RejC RejF c₀) (Dp (DkC DF W₀ c₀)) L (entriesOf L (pathOf L j)) := by
  have hp := pfStart_eq
  have hlen := h.len
  rintro ((hR | ⟨i, hi, l, hl, -, hc⟩ | ⟨l, hl, -, hc⟩) | hD)
  · exact h.rejF hR
  · exact hc (h.p1 i hi l hl)
  · exact hc (h.pf l hl)
  · unfold DPos Dp at hD
    rw [phOf_ge (by omega), DkC_ge (by norm_num), DT_Pf, DPf_end_chain (by omega)] at hD
    exact hD.elim (fun h4 => h4 h.lvl4) fun hf => hf h.fin

/-- **`FinalLaw` from the tail's end, the front and the extractor.** The tail (P1.0 … Pf, the
walk, unique decoding, Hide) is discharged; what is left is named: `hAcc` (an accepted run is a
`W` proof with its witness, or gives `AcceptTail`: `runLog_chain` and the finals' semantics) and
`hExt` (the front's truths on `f⁽⁰⁾` and the extractor: from no doom on any prefix and
`LigeritoOut`, the extractor's output is a witness). -/
theorem finalLaw_of (S : Submission) (vk : Digest) {RejF : Log → Log → Prop}
    {DF : ℕ → Log → Log → Prop} (hF : FrontLocal W₀ c₀) (hFS : FrontChainStab RejF DF)
    (hAcc : ∀ L c π, L.length ≤ logCap → ¬ Bad L → (S.V vk c π).runLog L = some true →
      (∃ w, S.E c π L = some w ∧ Rel (S.acc vk) c w) ∨ ∃ j, AcceptTail RejF W₀ c₀ L j)
    (hExt : ∀ L c π j, L.length ≤ logCap → ¬ Bad L → (S.V vk c π).runLog L = some true →
      AcceptTail RejF W₀ c₀ L j →
      (∀ p < (entriesOf L (pathOf L j)).length,
        ¬ DC (RejC RejF c₀) (Dp (DkC DF W₀ c₀)) L ((entriesOf L (pathOf L j)).take (p + 1))) →
      LigeritoOut W₀ c₀ L (entriesOf L (pathOf L j)) →
      ∃ w, S.E c π L = some w ∧ Rel (S.acc vk) c w) :
    FinalLaw S vk (RejC RejF c₀) (DkC DF W₀ c₀) := by
  intro L c π hl hμ hrun
  obtain ⟨hb, hE, hEH⟩ := muT_lt_one hμ
  rcases hAcc L c π hl hb hrun with hw | ⟨j, hT⟩
  · exact hw
  have hS := chainStab_of hF hFS
  have hend := not_DC_end (DF := DF) hT
  have hp := pfStart_eq
  have hlen := hT.len
  have h4 := (tail_pos (show 4 < 5 by norm_num)).2.2.2.2
  have hnx : nxStart 4 = pfStart := rfl
  exact hExt L c π j hl hb hrun hT (fun p hp' => not_D_prefix hS hb hE hT.chain hend hp')
    (ligerito_final_of_walk hF hS hb hE hEH hT.chain (by omega) hend)

/-! ## Part G: controls -/

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
    by_cases h4 : i < 4
    · rw [lvC_succ _ h4, c1_nil _ (by omega), vNext]
      simp [foldAtN, foldAt_nil, K.smulF_eq_mul]
    · rw [show i = 4 by omega, lvC_five, c1_nil _ (by norm_num)]

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

/-- Control (value): `pfP` reads Pf's challenges (`kAt` at Pf's squeeze positions). -/
theorem pfP_eq (es : Log) {v : ℕ} (hv : v < 7) : pfP es v = kAt es (pfStart + 2 * v + 1) := by
  simp [pfP, rchs2, rch2, kAt, List.getD_eq_getElem?_getD, hv]

/-- Control (value): level 4's point starts with P1.4's fold challenges. -/
theorem ptL_four_lt (es : Log) {v : ℕ} (hv : v < hEll 4) : ptL es 4 v = sAt es 4 v := by
  simp [ptL, ptD, hv]

/-- Control (negative): an inconsistent level-4 query refutes `AcceptTail` (its `lvl4` field is not
vacuous). -/
theorem not_acceptTail_of_cons {RejF : Log → Log → Prop} {L : Log} {j : ℕ}
    (h : consErr (kindOf (entriesOf L (pathOf L j))) L (entriesOf L (pathOf L j)) 4 0 ≠ 0) :
    ¬ AcceptTail RejF W₀ c₀ L j := fun hT =>
  not_truthP3_of _ (lvl_t_pos _ (by norm_num)) h hT.lvl4

/-- **Control (negative)**: with `c₀ = 1` the same empty chain fails `LigeritoOut` (level 0's
claim `1 ≠ ⟨0, f⁽⁰⁾⟩ = 0`): the claim field is not vacuous. -/
theorem not_ligeritoOut_one :
    ¬ LigeritoOut (fun _ _ _ => (0 : K)) (fun _ _ => (1 : K)) [] [] := fun h => by
  have := h.claim 0 (by norm_num)
  simp only [lvC, lvW, zero_mul, sum_const_zero] at this
  exact one_ne_zero this

end FR.Snd
