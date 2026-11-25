-- New for lvm6 (WP W1). The candidate seam of WP S (`OpeningIface`, CAND decision) at `P18`: the
-- level-0 ball `ball18` (W1's decoded Johnson list), the OOD pair `(z₀, y₀)` read from the history
-- after its first commitment (§6.1: `CAP(0)`, `B`, the nonce, 25 draws, `E(1)`), the candidates
-- (ball members satisfying claim 0 `q̃(z₀) = y₀`), the pin (the OOD answer present and at most one
-- candidate), and `L₀ = 111` (PARAM's level-0 list).
import Lvm6WhirOpen

/-!
# `OpeningIface` at `P18` (W1)

* `firstCommit h`, `oodZ h`, `oodY h`, `claim0 h = (eqPt z₀, y₀)`: the OOD pair of a history.
* `cands18`, `pinned18`; `ball18_append`, `ball18_card` (`≤ jl = 111`), `cands18_append`.
* **`I18 : OpeningIface`**; `I6 sh` (`I18` where `openKey sh`, empty elsewhere).
* `MA_w₀`: S's `Multiaffine 25` gives the level-0 table `wokE` asks.
* **`openSpec6_W1 : Stmt.openSpec6 I6 (whirAt whirP18)`**.
-/

namespace Lvm6.Whir

open LeanVM.Parameters LeanVM.Protocol.Compile LeanVM.Protocol.Whir.Sound LeanVM.Protocol.Whir
  LeanVM.Protocol.Whir.AffineCombiner LeanVM.Protocol.EndToEnd.Front Finset

/-! ## The OOD pair of a history -/

/-- The value of an event (draws and reads; lanes 0–1). -/
def evVal : Ev → E2
  | .sample c => e2OfE c
  | .read x => e2OfE x
  | _ => 0

/-- The position of the first commitment (the length if there is none). -/
def firstCommit : List Ev → ℕ
  | [] => 0
  | Ev.commit _ _ _ :: _ => 0
  | _ :: es => firstCommit es + 1

theorem firstCommit_lt : ∀ {h : List Ev}, commits h ≠ [] → firstCommit h < h.length
  | [], hc => absurd rfl hc
  | Ev.commit _ _ _ :: _, _ => by simp [firstCommit]
  | Ev.read _ :: es, hc => by simp only [firstCommit, List.length_cons]; have := firstCommit_lt (h := es) (by simpa [commits] using hc); omega
  | Ev.sample _ :: es, hc => by simp only [firstCommit, List.length_cons]; have := firstCommit_lt (h := es) (by simpa [commits] using hc); omega
  | Ev.grind _ :: es, hc => by simp only [firstCommit, List.length_cons]; have := firstCommit_lt (h := es) (by simpa [commits] using hc); omega
  | Ev.query _ :: es, hc => by simp only [firstCommit, List.length_cons]; have := firstCommit_lt (h := es) (by simpa [commits] using hc); omega

theorem firstCommit_append : ∀ {h : List Ev} (l : List Ev), commits h ≠ [] →
    firstCommit (h ++ l) = firstCommit h
  | [], _, hc => absurd rfl hc
  | Ev.commit _ _ _ :: _, _, _ => rfl
  | Ev.read _ :: es, l, hc => by simp only [List.cons_append, firstCommit]; rw [firstCommit_append l (by simpa [commits] using hc)]
  | Ev.sample _ :: es, l, hc => by simp only [List.cons_append, firstCommit]; rw [firstCommit_append l (by simpa [commits] using hc)]
  | Ev.grind _ :: es, l, hc => by simp only [List.cons_append, firstCommit]; rw [firstCommit_append l (by simpa [commits] using hc)]
  | Ev.query _ :: es, l, hc => by simp only [List.cons_append, firstCommit]; rw [firstCommit_append l (by simpa [commits] using hc)]

/-- The OOD point: the 25 draws after the commitment, its bind and the nonce. -/
def oodZ (h : List Ev) : List E2 := ((h.drop (firstCommit h + 3)).take 25).map evVal

/-- The OOD value: the read after the point. -/
def oodY (h : List Ev) : E2 := (h[firstCommit h + 28]?.map evVal).getD 0

/-- **Claim 0 of a history**: `q̃(z₀) = y₀`. -/
def claim0 (h : List Ev) : StackClaim6 := (fun pt ↦ eqPt (oodZ h) pt, oodY h)

/-- The history holds its OOD answer. -/
def HasOod (h : List Ev) : Prop := commits h ≠ [] ∧ firstCommit h + 29 ≤ h.length

theorem HasOod.append {h : List Ev} (hp : HasOod h) (l : List Ev) : HasOod (h ++ l) :=
  ⟨by rw [commits_app]; exact fun he ↦ hp.1 (List.append_eq_nil_iff.mp he).1, by
    rw [firstCommit_append l hp.1, List.length_append]; have := hp.2; omega⟩

theorem claim0_append {h : List Ev} (hp : HasOod h) (l : List Ev) : claim0 (h ++ l) = claim0 h := by
  have hf := firstCommit_append l hp.1
  have hl := hp.2
  unfold claim0 oodZ oodY
  rw [hf, List.getElem?_append_left (by omega), List.drop_append_of_le_length (by omega),
    List.take_append_of_le_length (by simp; omega)]

/-! ## The ball, the candidates, the pin -/

theorem ball18_append {h : List Ev} (hc : commits h ≠ []) (l : List Ev) :
    ball18 (h ++ l) = ball18 h := by
  have hw : wordE true 0 (0 + 6) 21 (commits (h ++ l)) = wordE true 0 (0 + 6) 21 (commits h) := by
    funext u p
    rw [commits_app]
    simp only [wordE]
    rw [List.getElem?_append_left (List.length_pos_of_ne_nil hc)]
  show ball lad18 dec18 _ (h ++ l) = ball lad18 dec18 _ h
  unfold ball
  simp only [Lad.word, Lad.d, Lad.dom, lad18, mid0, midE, hw]

/-- **The candidates**: ball members satisfying claim 0 of the history. -/
def cands18 (h : List Ev) : Set Stack := {q | q ∈ ball18 h ∧ (claim0 h).Holds 25 q}

/-- **The pin**: the OOD answer is in the history and at most one candidate. -/
def pinned18 (h : List Ev) : Prop := HasOod h ∧ (cands18 h).Subsingleton

theorem cands18_append {h : List Ev} (hp : HasOod h) (l : List Ev) : cands18 (h ++ l) = cands18 h := by
  unfold cands18
  rw [ball18_append hp.1, claim0_append hp]

theorem ball18_eq (h : List Ev) : ball18 h = dec18 '' ↑(tupleList (domE 21 (by norm_num))
    (wordE true 0 (0 + 6) 21 (commits h)) (1053300 - 6) (2 ^ 19 - 1 + 6)) := by
  show ball lad18 dec18 _ h = _
  unfold ball
  congr 1
  ext U
  simp only [Set.mem_setOf_eq, Finset.mem_coe, mem_tupleList]
  rfl

/-- **The list bound** `L₀ = 111`. -/
theorem ball18_card (h : List Ev) : (ball18 h).Finite ∧ (ball18 h).ncard ≤ 111 := by
  rw [ball18_eq]
  refine ⟨Set.Finite.image _ (Finset.finite_toSet _), (Set.ncard_image_le (Finset.finite_toSet _)).trans ?_⟩
  rw [Set.ncard_coe_finset]
  refine (card_tupleList_le_jl _ _ _ _ (by norm_num)).trans ?_
  decide +kernel

/-- **The candidate seam at `P18`.** -/
noncomputable def I18 : OpeningIface where
  cands := cands18
  pinned := pinned18
  pinned_append h l hp := ⟨hp.1.append l, by rw [cands18_append hp.1]; exact hp.2⟩
  pinned_sub _ hp := hp.2
  ball := ball18
  L₀ := 111
  ball_card h _ := ball18_card h
  ball_append h l hp := ball18_append hp.1.1 l
  cands_append h l hp := cands18_append hp.1 l
  cands_sub _ _ hq := hq.1

/-- The seam elsewhere: nothing (only `P18` is deployed). -/
def Itriv : OpeningIface where
  cands _ := ∅
  pinned _ := True
  pinned_append _ _ _ := trivial
  pinned_sub _ _ := Set.subsingleton_empty
  ball _ := ∅
  L₀ := 0
  ball_card _ _ := ⟨Set.finite_empty, by simp⟩
  ball_append _ _ _ := rfl
  cands_append _ _ _ := rfl
  cands_sub _ := le_rfl

/-! ## Multiaffine claims -/

/-- The first `n` entries of a list, padded with zeros. -/
def padN (n : ℕ) (y : List E2) : List E2 := List.ofFn fun i : Fin n ↦ y.getD i 0

theorem padN_cons (n : ℕ) (X : E2) (x : List E2) : padN (n + 1) (X :: x) = X :: padN n x := by
  simp [padN, List.ofFn_succ]

theorem eqPt_cons (a₀ X : E2) (a x : List E2) :
    eqPt (a₀ :: a) (X :: x) = (a₀ * X + (1 + a₀) * (1 + X)) * eqPt a x := by
  simp [eqPt]

/-- `eq(a, ·)` on the first `|a|` entries is affine in each of them. -/
theorem MA_eqPt_padN : ∀ (a : List E2), MA a.length fun y ↦ eqPt a (padN a.length y)
  | [] => trivial
  | a₀ :: a => by
    refine ⟨fun X x ↦ ?_, fun X ↦ ?_⟩
    · simp only [List.length_cons, padN_cons, eqPt_cons]
      ring
    · simp only [List.length_cons, padN_cons, eqPt_cons]
      exact MA_mul_const _ (MA_eqPt_padN a)

theorem eqPt_rot (b p : List E2) (hb : b.length = 25) (hp : p.length = 25) :
    eqPt b (p.drop 6 ++ p.take 6) = eqPt (b.drop 19 ++ b.take 19) p := by
  unfold eqPt
  conv_lhs => rw [← List.take_append_drop 19 b]
  conv_rhs => rw [← List.take_append_drop 6 p]
  rw [List.zipWith_append (by simp [hb, hp]), List.zipWith_append (by simp [hb, hp]),
    List.prod_append, List.prod_append, mul_comm]

theorem pad25_eq_padN (y : List E2) : pad25 y = padN 25 y := rfl

/-- **A multiaffine claim (S's `Multiaffine`) gives a multiaffine level-0 table** (`wokE`'s `MA`). -/
theorem MA_w₀ (cl : StackClaim6) (hcl : cl.Multiaffine 25) : MA 25 (w₀ cl).2 := by
  have hfun : (w₀ cl).2 = fun y ↦ ∑ x : Fin (2 ^ 25), cl.1 (boolPt 25 x) *
      eqPt ((boolPt 25 x).drop 19 ++ (boolPt 25 x).take 19) (padN 25 y) := by
    funext y
    show cl.1 ((pad25 y).drop 6 ++ (pad25 y).take 6) = _
    have hl : ((pad25 y).drop 6 ++ (pad25 y).take 6).length = 25 := by simp [pad25]
    rw [hcl _ hl]
    refine Finset.sum_congr rfl fun x _ ↦ ?_
    rw [eqPt_rot _ _ (by simp [boolPt]) (by simp [pad25]), pad25_eq_padN]
  rw [hfun]
  refine MA_sum _ _ fun x _ ↦ MA_mul_const _ ?_
  have hlen : ((boolPt 25 x).drop 19 ++ (boolPt 25 x).take 19).length = 25 := by simp [boolPt]
  have := MA_eqPt_padN ((boolPt 25 x).drop 19 ++ (boolPt 25 x).take 19)
  rwa [hlen] at this

/-! ## S's `openSpec6` -/

/-- **The seam per shape**: `I18` on shapes with `P18`'s opening constants, empty elsewhere. -/
noncomputable def I6 (sh : Shape) : OpeningIface := if openKey sh = true then I18 else Itriv

theorem openKey_M {sh : Shape} (hk : openKey sh = true) : sh.M = 25 := by
  simp only [openKey, Bool.and_eq_true, decide_eq_true_eq] at hk
  rw [hk.1.1.1.1.1.1]
  rfl

/-- **T3 `openSpec6`** (W1): the deployed opening `whirP18` (on shapes with `P18`'s opening
constants, `whirAt`) meets `stackedSpec` with W1's candidate seam `I6`. -/
theorem openSpec6_W1 : Stmt.openSpec6 I6 (whirAt whirP18) :=
  Stmt.openSpec6_whirAt fun sh hk ↦ by
    have hI : I6 sh = I18 := if_pos hk
    rw [hI, openKey_M hk]
    intro cl hcl
    exact openSpec18 cl (MA_w₀ cl hcl)

end Lvm6.Whir
