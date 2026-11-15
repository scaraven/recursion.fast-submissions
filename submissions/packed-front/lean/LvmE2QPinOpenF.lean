-- New for lvm2 E2-FT (E2F-QH5): `C_main`'s opening at S2GF (`LvmE2QPinOpen.openGF`) replays V's opening
-- (`LvmDecideE2.dOpenF`), big shape: what each circuit claim stands for (`FRel`), the batched basis with the `E2`
-- claim forms (`basisGF_spec`: word halves by `w6Leaf_spec`, row claims by `rowLeaf_weightN`, `E3` claims by
-- `oneClaim_spec`), and the stacked opening's run (`openGF_big_run`, by the generic `stackG_run`).
import LvmE2QPinOpenSem
import LvmQRingCrtSem
import LvmQAsmArith2Whir

/-!
# The opening at S2GF, big shape

* **`FRel M ν fc bc`**: the circuit claim `fc` (`FClaim`) stands for V's block claim `bc` on the stack of `ν`
  variables: an `E3` claim its `CClaim.val`; a half `h` of an `E2` sum claim `halfB ν h parts v` (`splitD`'s,
  `splitD_halfB`); a `D` half the half of the one-part sum on `⟨22, 0⟩`; a row claim the block claim with V's row
  weight `rowW eqR z` (`rowValD_weight`), its `ν` cells standing for `eqR` (`RowNuOk`).
* **`pfTermsB_spec`**, **`basisGF_spec`**: the terms of the big-shape preparations sum to `sc·onStack(x)`; the
  basis is `Σ_i s^i·onStack_i(x)`.
* **`openGF_big_run`**: on the claim list `(pinW, pin.value) :: bcs.map onStack` (the pin first, `pinW` its
  weight on the stack), V's `verifyStackedOpening` keeps `ok`, ends where the circuit's opening does, and leaves no
  message pending.
-/

set_option autoImplicit false

namespace Lvm.Q2

open Lvm Lvm.Loop Lvm.Loop.Build Lvm.Har Lvm.QShape Finset

variable {c : Ctx} {M : Mem}

/-! ## V's claims of the circuit's forms -/

/-- Coordinate `h` of a `Quad Ext3` value. -/
def c6 (h : Bool) (a : FE6) : FE := if h then a.im else a.re

/-- An `E2` sum claim's parts as values. -/
def partsV (M : Mem) (parts : List (C2 × Placement × List C2)) : List (FE2 × Placement × List FE2) :=
  parts.map fun e => (e.1.val M, e.2.1, e.2.2.map (C2.val M))

/-- **Half `h` of an `E2` sum claim** on the stack of `ν` variables (`splitD`'s claims). -/
def halfB (ν : ℕ) (h : Bool) (parts : List (FE2 × Placement × List FE2)) (v : FE) : BlockClaim :=
  ⟨⟨ν, 0⟩, fun x => c6 h (sumW6D parts x), v⟩

theorem splitD_halfB (ν : ℕ) (parts : List (FE2 × Placement × List FE2)) (v : FE2) :
    splitD ν parts v = [halfB ν false parts (FE.ofK v.re), halfB ν true parts (FE.ofK v.im)] := rfl

/-- Both cells of an `E2` value are `K` cells. -/
def KC2 (x : C2) : Prop := x.re.ty = .K ∧ x.im.ty = .K

/-- **What a circuit claim stands for** (big shape) on the stack of `ν` variables. -/
def FRel (M : Mem) (ν : ℕ) : FClaim → BlockClaim → Prop
  | .e3 cc, bc => WF1 ν cc = true ∧ bc = (cc.val M).2
  | .half h parts v, bc => (∀ e ∈ parts, KC2 e.1 ∧ (∀ x ∈ e.2.2, KC2 x) ∧ e.2.2.length = e.2.1.variableCount ∧
      e.2.1.variableCount ≤ ν) ∧ bc = halfB ν h (partsV M parts) (v.val M)
  | .dhalf h z v, bc => (∀ x ∈ z, KC2 x) ∧ z.length = 22 ∧ 22 ≤ ν ∧
      bc = halfB ν h [(1, ⟨22, 0⟩, z.map (C2.val M))] (v.val M)
  | .row blk z nu v, bc => ∃ eqR, RowNuOk M nu eqR ∧ z ≠ [] ∧ (∀ x ∈ z, KC2 x) ∧
      z.length = blk.variableCount ∧ blk.variableCount ≤ ν ∧ bc = ⟨blk, rowW eqR (z.map (C2.val M)), v.val M⟩
  | .drow z nu v, bc => ∃ eqR, RowNuOk M nu eqR ∧ z ≠ [] ∧ (∀ x ∈ z, KC2 x) ∧
      z.length = CMain.nu20 ∧ CMain.nu20 ≤ ν ∧ bc = ⟨⟨CMain.nu20, 0⟩, rowW eqR (z.map (C2.val M)), v.val M⟩

/-- The opening's shared cells hold their constants. -/
structure FCtxOk (M : Mem) (F : FCtx) : Prop where
  z : F.z.val M = 0
  o : F.o.val M = 1
  zk : F.zk.val M = 0
  zE : F.z.ty = .E
  oE : F.o.ty = .E
  o2 : F.o2.val M = 1
  o2K : KC2 F.o2
  z2 : F.z2.val M = 0

/-! ## Algebra of the word halves -/

theorem c6_mk (h : Bool) (a b : FE) : c6 h ⟨a, b⟩ = if h then b else a := rfl

/-- A coordinate of `sumW6D` is the sum of the parts' coordinates. -/
theorem c6_sumW6D (h : Bool) (parts : List (FE2 × Placement × List FE2)) (x : List FE) :
    c6 h (sumW6D parts x) = (parts.map fun e => c6 h (FE6.mul (FE6.mul (FE6.ofE2 e.1) (FE6.ofE (e.2.1.eqAbove x)))
      (wordWD e.2.2 (x.take e.2.1.variableCount)))).sum := by
  have hgen : ∀ (ps : List (FE2 × Placement × List FE2)) (acc : FE6),
      c6 h (ps.foldl (fun acc (e : FE2 × Placement × List FE2) =>
        let w := FE6.mul (FE6.mul (FE6.ofE2 e.1) (FE6.ofE (e.2.1.eqAbove x))) (wordWD e.2.2 (x.take e.2.1.variableCount))
        (⟨acc.re + w.re, acc.im + w.im⟩ : FE6)) acc) =
      c6 h acc + (ps.map fun e => c6 h (FE6.mul (FE6.mul (FE6.ofE2 e.1) (FE6.ofE (e.2.1.eqAbove x)))
        (wordWD e.2.2 (x.take e.2.1.variableCount)))).sum := by
    intro ps
    induction ps with
    | nil => intro acc; simp
    | cons e ps ih =>
      intro acc
      rw [List.foldl_cons, ih, List.map_cons, List.sum_cons]
      cases h <;> simp only [c6, Bool.false_eq_true, if_false, if_true] <;> ring
  rw [sumW6D, hgen]
  cases h <;> simp [c6]

/-- A part's coordinate: the selector times the coordinate of `wordW·c`. -/
theorem c6_part (h : Bool) (cv : FE2) (e : FE) (W : FE6) :
    c6 h (FE6.mul (FE6.mul (FE6.ofE2 cv) (FE6.ofE e)) W) = e * c6 h (FE6.mul W (FE6.ofE2 cv)) := by
  simp only [fe6_mul, FE6.ofE2, FE6.ofE, c6]
  cases h <;> simp only [Bool.false_eq_true, if_false, if_true] <;> ring

theorem eqAbove_top (ν : ℕ) (y : List FE) (hy : y.length = ν) : (⟨ν, 0⟩ : Placement).eqAbove y = 1 := by
  simp [Placement.eqAbove, hy, selectorPoint, eqEval]

theorem xs_take (ν xb k : ℕ) (hk : k ≤ ν) : (xsOf M ν xb).take k = (List.range k).map fun i => M.e (xb + i) := by
  rw [xsOf, ← List.map_take, List.take_range, min_eq_left hk]

/-! ## The big-shape terms -/

theorem kcell_C2 {x : C2} (hx : KC2 x) : FE6.ofE2 (x.val M) = ⟨x.re.val M, x.im.val M⟩ := by
  simp only [FE6.ofE2, C2.val]
  rw [kcell_val hx.1, kcell_val hx.2]

/-- **The big-shape terms of a half's parts**: no pairs; they sum to `sc · Σ_parts eqAbove·coord(wordW·c)`. -/
theorem halfTermsB_spec {F : FCtx} (hF : FCtxOk M F) {ν xb : ℕ} (sc : Cell) (h : Bool) :
    ∀ (parts : List (C2 × Placement × List C2)) (m6 : Memo6),
      (∀ e ∈ parts, KC2 e.1 ∧ (∀ x ∈ e.2.2, KC2 x) ∧ e.2.2.length = e.2.1.variableCount ∧
        e.2.1.variableCount ≤ ν) → Memo6Ok M xb m6 →
      Hs c M (halfTerms F ν xb sc h false parts m6) (fun r => Memo6Ok M xb r.1 ∧ r.2.1 = [] ∧
        (r.2.2.map (tval M (fun i => M.e (xb + i)) ν)).sum =
          sc.val M * (partsV M parts |>.map fun e => c6 h (FE6.mul (FE6.mul (FE6.ofE2 e.1)
            (FE6.ofE (e.2.1.eqAbove (xsOf M ν xb)))) (wordWD e.2.2 ((xsOf M ν xb).take e.2.1.variableCount)))).sum)
  | [], m6, _, hm => hs_pure ⟨hm, rfl, by simp [partsV]⟩
  | (cv, blk, zl) :: ps, m6, hp, hm => by
    obtain ⟨hcK, hzK, hzl, hvc⟩ := hp _ (List.mem_cons_self ..)
    unfold halfTerms
    refine hs_bind (w6Leaf_spec hF.z hF.o xb cv zl hcK hzK m6 hm) fun r ⟨hm', hr⟩ => ?_
    refine hs_bind (halfTermsB_spec hF sc h ps r.1 (fun e he => hp e (List.mem_cons_of_mem _ he)) hm')
      fun rs ⟨hm'', hn, hs⟩ => ?_
    simp only [Bool.false_eq_true, if_false]
    refine hs_pure ⟨hm'', hn, ?_⟩
    rw [List.map_cons, List.sum_cons, hs]
    simp only [partsV, List.map_cons, List.sum_cons]
    have hlf : (if h then r.2.2 else r.2.1).val M =
        c6 h (FE6.mul (wordF (fun i => M.e (xb + i)) 0 ⟨1, 0⟩ (zl.map (C2.val M))) (FE6.ofE2 (cv.val M))) := by
      rw [← hr]; cases h <;> rfl
    have hW : wordF (fun i => M.e (xb + i)) 0 ⟨1, 0⟩ (zl.map (C2.val M)) =
        wordWD (zl.map (C2.val M)) ((xsOf M ν xb).take blk.variableCount) := by
      rw [wordF_eq_wordWD, xs_take ν xb _ hvc, List.length_map, hzl]
    have hE : kprod (fun i => M.e (xb + i)) ν (keyOf (selbit blk) ν blk.variableCount) = blk.eqAbove (xsOf M ν xb) := by
      rw [kprod_keyOf, eqAbove_prod blk _ (fun i => M.e (xb + i)) (by rw [xs_length]; exact hvc)
        (fun i hi => xs_getD (by rwa [xs_length] at hi)), xs_length]
    simp only [tval]
    rw [hE, hlf, hW, c6_part]
    ring

/-- **The big-shape terms of one prepared claim**: no pairs; they sum to `sc · bc.onStack(x)`. -/
theorem pfTermsB_spec {F : FCtx} (hF : FCtxOk M F) {ν xb : ℕ} (sc : Cell) {fc : FClaim} {bc : BlockClaim}
    (hr : FRel M ν fc bc) (memo : Memo) (m6 : Memo6) (hm : MemoOk M (fun i => M.e (xb + i)) memo)
    (hm6 : Memo6Ok M xb m6) :
    Hs c M (pfTerms F ν xb sc (prepB F fc).1 memo m6) (fun r => MemoOk M (fun i => M.e (xb + i)) r.1 ∧
      Memo6Ok M xb r.2.1 ∧ r.2.2.1 = [] ∧
      (r.2.2.2.map (tval M (fun i => M.e (xb + i)) ν)).sum = sc.val M * bc.onStack.1 (xsOf M ν xb)) := by
  have hX : (xsOf M ν xb).length = ν := xs_length ν xb
  cases fc with
  | e3 cc =>
    obtain ⟨hwf, rfl⟩ := hr
    show Hs c M (oneClaim ν xb F.z F.o sc cc memo >>= fun r => pure (r.1, m6, [], r.2)) _
    exact hs_bind (oneClaim_spec hF.z hF.o hF.zE hwf hm) fun r ⟨hm', hv⟩ => hs_pure ⟨hm', hm6, rfl, hv⟩
  | half h parts v =>
    obtain ⟨hp, rfl⟩ := hr
    show Hs c M (halfTerms F ν xb sc h false parts m6 >>= fun r => pure (memo, r.1, r.2.1, r.2.2)) _
    refine hs_bind (halfTermsB_spec hF sc h parts m6 hp hm6) fun r ⟨hm', hn, hs⟩ => hs_pure ⟨hm, hm', hn, ?_⟩
    rw [hs, BlockClaim.onStack]
    simp only [halfB]
    rw [eqAbove_top ν _ hX, one_mul, List.take_of_length_le (by rw [hX]), c6_sumW6D]
  | dhalf h z v =>
    obtain ⟨hzK, hzl, h22, rfl⟩ := hr
    show Hs c M (halfTerms F ν xb sc h false [(F.o2, ⟨22, 0⟩, z)] m6 >>= fun r => pure (memo, r.1, r.2.1, r.2.2)) _
    refine hs_bind (halfTermsB_spec hF sc h [(F.o2, ⟨22, 0⟩, z)] m6 (fun e he => by
      simp only [List.mem_singleton] at he; subst he; exact ⟨hF.o2K, hzK, hzl, h22⟩) hm6)
      fun r ⟨hm', hn, hs⟩ => hs_pure ⟨hm, hm', hn, ?_⟩
    rw [hs, BlockClaim.onStack]
    simp only [halfB]
    rw [eqAbove_top ν _ hX, one_mul, List.take_of_length_le (i := ν) (l := xsOf M ν xb) (by rw [hX]),
      c6_sumW6D]
    simp only [partsV, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, hF.o2]
  | row blk z nu v =>
    obtain ⟨eqR, hnu, hne, hzK, hzl, hvc, rfl⟩ := hr
    simp only [prepB, pfTerms, Bool.false_eq_true, ↓reduceIte]
    refine hs_bind (rowLeaf_weightN nu eqR hnu z hne hzK xb ((xsOf M ν xb).take blk.variableCount)
      (by rw [List.length_take, hX, hzl]; omega)
      (fun l hl => by rw [getD_take' _ _ (by omega), xs_getD (by omega)]) hF.z hF.zk) fun lf hlf =>
      hs_pure ⟨hm, hm6, rfl, ?_⟩
    have hE := eqAbove_prod blk (xsOf M ν xb) (fun i => M.e (xb + i)) (by rw [hX]; exact hvc)
      (fun i hi => xs_getD (by rwa [hX] at hi))
    rw [hX] at hE
    rw [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero, tval, kprod_keyOf, hlf, ← hE,
      BlockClaim.onStack]
    ring
  | drow z nu v =>
    obtain ⟨eqR, hnu, hne, hzK, hzl, hvc, rfl⟩ := hr
    simp only [prepB, pfTerms, Bool.false_eq_true, ↓reduceIte]
    refine hs_bind (rowLeaf_weightN nu eqR hnu z hne hzK xb ((xsOf M ν xb).take CMain.nu20)
      (by rw [List.length_take, hX, hzl]; omega)
      (fun l hl => by rw [getD_take' _ _ (by omega), xs_getD (by omega)]) hF.z hF.zk) fun lf hlf =>
      hs_pure ⟨hm, hm6, rfl, ?_⟩
    have hE := eqAbove_prod (⟨CMain.nu20, 0⟩ : Placement) (xsOf M ν xb) (fun i => M.e (xb + i)) (by rw [hX]; exact hvc)
      (fun i hi => xs_getD (by rwa [hX] at hi))
    rw [hX] at hE
    rw [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero, tval, kprod_keyOf, hlf, ← hE,
      BlockClaim.onStack]
    ring

/-- **The big-shape terms of the prepared claims** from index `i` (scale cells `sp + i`). -/
theorem pfTermsAllB_spec {F : FCtx} (hF : FCtxOk M F) {ν xb sp N : ℕ} {s : FE}
    (hs : ∀ j < N, M.e (sp + j) = s ^ j) :
    ∀ (fcs : List FClaim) (bcs : List BlockClaim), List.Forall₂ (FRel M ν) fcs bcs →
      ∀ (i : ℕ) (memo : Memo) (m6 : Memo6), MemoOk M (fun i => M.e (xb + i)) memo → Memo6Ok M xb m6 →
      i + fcs.length ≤ N →
      Hs c M (pfTermsAll F ν xb sp i (fcs.map fun fc => (prepB F fc).1) memo m6) (fun r => r.1 = [] ∧
        (r.2.map (tval M (fun i => M.e (xb + i)) ν)).sum = bsum s i (bcs.map fun bc => bc.onStack.1 (xsOf M ν xb)))
  | [], [], _, _, _, _, _, _, _ => hs_pure ⟨rfl, by simp [bsum]⟩
  | fc :: fcs, bc :: bcs, .cons hr hrs, i, memo, m6, hm, hm6, hN => by
    simp only [List.length_cons] at hN
    simp only [List.map_cons]
    show Hs c M (pfTerms F ν xb (ec (sp + i)) (prepB F fc).1 memo m6 >>= fun r =>
      pfTermsAll F ν xb sp (i + 1) (fcs.map fun fc => (prepB F fc).1) r.1 r.2.1 >>= fun rs =>
        pure (r.2.2.1 ++ rs.1, r.2.2.2 ++ rs.2)) _
    refine hs_bind (pfTermsB_spec hF (ec (sp + i)) hr memo m6 hm hm6) fun r ⟨hm', hm6', hn, hv⟩ =>
      hs_bind (pfTermsAllB_spec hF hs fcs bcs hrs (i + 1) r.1 r.2.1 hm' hm6' (by omega)) fun rs ⟨hn', hv'⟩ =>
        hs_pure ⟨by rw [hn, hn', List.nil_append], ?_⟩
    rw [List.map_append, List.sum_append, hv, hv', bsum, Cell.val_E, hs i (by omega)]

/-- **The batched basis, big shape**: `Σ_i s^i·onStack_i(x)` over V's claims. -/
theorem basisGF_spec {F : FCtx} (hF : FCtxOk M F) {ν sp xb : ℕ} {s : FE} {fcs : List FClaim}
    {bcs : List BlockClaim} (hrel : List.Forall₂ (FRel M ν) fcs bcs) (hs : ∀ j < fcs.length, M.e (sp + j) = s ^ j) :
    Hs c M (basisGF F ν (fcs.map fun fc => (prepB F fc).1) sp xb) (fun r =>
      r.val M = Lvm.dot (powers s bcs.length) (bcs.map fun bc => bc.onStack.1 (xsOf M ν xb))) := by
  unfold basisGF
  refine hs_bind (pfTermsAllB_spec hF hs fcs bcs hrel 0 [] [] (fun _ he => by simp at he)
    (fun _ he => by simp at he) (by omega)) fun r ⟨_, hv⟩ => hs_mono (trieG_spec hF.z ν r.2) fun w hw => ?_
  rw [hw, hv]
  have hl : bcs.length = (bcs.map fun bc => bc.onStack.1 (xsOf M ν xb)).length := by simp
  rw [hl, dot_powers_bsum]

/-! ## The opening, big shape -/

theorem prepB_value {F : FCtx} {ν : ℕ} {fc : FClaim} {bc : BlockClaim} (hr : FRel M ν fc bc) :
    (prepB F fc).2.val M = bc.value := by
  cases fc with
  | e3 cc => obtain ⟨-, rfl⟩ := hr; exact (cval_value cc).symm
  | half h parts v => obtain ⟨-, rfl⟩ := hr; rfl
  | dhalf h z v => obtain ⟨-, -, -, rfl⟩ := hr; rfl
  | row blk z nu v => obtain ⟨eqR, -, -, -, -, -, rfl⟩ := hr; rfl
  | drow z nu v => obtain ⟨eqR, -, -, -, -, -, rfl⟩ := hr; rfl

theorem vals_eq {F : FCtx} {ν : ℕ} : ∀ {fcs : List FClaim} {bcs : List BlockClaim},
    List.Forall₂ (FRel M ν) fcs bcs → fcs.map (fun fc => (prepB F fc).2.val M) = bcs.map (·.value)
  | [], [], _ => rfl
  | _ :: _, _ :: _, .cons hr hrs => by rw [List.map_cons, List.map_cons, prepB_value hr, vals_eq hrs]

set_option maxHeartbeats 1000000 in
/-- **`C_main`'s opening at S2GF, big shape, replays V's**: on the claim list `(pinW, pin.value) :: bcs.map onStack`
(`pinW` the pin's weight on the stack, `bcs` what the circuit's claims stand for), `verifyStackedOpening` keeps
`ok`, ends at the opening's end and leaves no message pending. -/
theorem openGF_big_run (Cm : SCfg) {F : FCtx} (hF : FCtxOk M F) (pin : CClaim) (pinB : BlockClaim)
    (hpin : FRel M Cm.nu (.e3 pin) pinB) (pinW : List FE → FE)
    (hpinW : ∀ x : List FE, x.length = Cm.nu → pinW x = pinB.onStack.1 x) (cs : List FClaim)
    (bcs : List BlockClaim) (hrel : List.Forall₂ (FRel M Cm.nu) cs bcs) (mb : List Cell) (sK g : Cell)
    {sig : ByteArray} {T : Nat} (hS : Lvm.Q1.Streamed M sig T) (hok : LayOk Cm T = true) (hg : g.val M = 1)
    (hgK : g.ty = .K) (hpos : PosOk Cm M sig 0 Cm.levels (Cm.U + 15)) (hpw : PwOk Cm M 0 Cm.levels) {p : Ptr}
    (hp : 1 ≤ p.e) (h : Lvm.QSig.Ok c M (openGF Cm false F pin cs mb sK g) p) (s : RS) (hs : pos s = 8 * Cm.U) :
    let scs := (pinW, pinB.value) :: bcs.map (·.onStack)
    (verifyStackedOpening Cm.levels Cm.nu scs false Cm.g Cm.ood sig s).2.ok = s.ok ∧
    pos (verifyStackedOpening Cm.levels Cm.nu scs false Cm.g Cm.ood sig s).2 =
      8 * stackEndL Cm.g Cm.ood Cm.levels (Cm.U + 15) ∧
    (verifyStackedOpening Cm.levels Cm.nu scs false Cm.g Cm.ood sig s).2.msg = 0 := by
  intro scs
  simp only [openGF, Bool.false_eq_true, if_false] at h
  have hrel' : List.Forall₂ (FRel M Cm.nu) (.e3 pin :: cs) (pinB :: bcs) := .cons hpin hrel
  have hlen : scs.length = cs.length + 1 := by simp [scs, hrel.length_eq]
  have hw : (PF.e3 pin false, pin.value) :: cs.map (prepB F) = (FClaim.e3 pin :: cs).map (prepB F) := rfl
  refine stackG_run Cm (cs.length + 1) _ _ _ (fun w => w = (FClaim.e3 pin :: cs).map (prepB F)) scs hlen
    (hs_pure hw) ?_ ?_ F.z F.o g hS hok hF.z hF.o hF.zE hF.oE hg hgK hpos hpw hp h s hs
  · intro w hw' sp σ hsp p' h'
    subst hw'
    have hl : (((FClaim.e3 pin :: cs).map (prepB F)).map fun e =>
        (⟨.main, .point ⟨0, 0⟩ [], e.2⟩ : CClaim)).length = cs.length + 1 := by simp
    rw [targetG_spec h' hF.z σ (fun i hi => hsp i (by rw [← hl]; exact hi)), hl]
    have hv : ((((FClaim.e3 pin :: cs).map (prepB F)).map fun e => (⟨.main, .point ⟨0, 0⟩ [], e.2⟩ : CClaim)).map
        fun cc => (cc.val M).2.value) = scs.map (·.2) := by
      rw [List.map_map, List.map_map,
        show scs.map (·.2) = (pinB :: bcs).map (·.value) by simp only [scs, List.map_cons, List.map_map]; rfl]
      exact vals_eq hrel'
    rw [hv]
  · intro w hw' sp xb σ hsp
    subst hw'
    have e : ((FClaim.e3 pin :: cs).map (prepB F)).map (·.1) = (FClaim.e3 pin :: cs).map fun fc => (prepB F fc).1 := by
      rw [List.map_map]; rfl
    rw [e]
    refine hs_mono (basisGF_spec hF hrel' fun j hj => hsp j (by simpa using hj)) fun r hr => ?_
    rw [hr]
    have hl : (pinB :: bcs).length = cs.length + 1 := by simp [hrel.length_eq]
    rw [hl]
    congr 1
    simp only [scs, List.map_cons, List.map_map]
    have hX : ((List.range Cm.nu).map fun i => M.e (xb + i)).length = Cm.nu := by simp
    refine congrArg₂ List.cons (hpinW _ hX).symm ?_
    rfl

/-! ## V's `dOpenF`, big shape -/

/-- **What a circuit claim stands for in V's list** (`dOpenF`'s `(com, claim, tail)`): on `C_main`, `FRel`. -/
def FRelT (M : Mem) (ν : ℕ) (fc : FClaim) (cl : Com × BlockClaim × FE) : Prop := cl.1 = .main ∧ FRel M ν fc cl.2.1

theorem point_onStack (ν : ℕ) (z : List FE) (a : FE) (x : List FE) (hx : x.length = ν) :
    (BlockClaim.point ⟨ν, 0⟩ z a).weight x = (BlockClaim.point ⟨ν, 0⟩ z a).onStack.1 x := by
  simp only [BlockClaim.point, BlockClaim.onStack]
  rw [eqAbove_top ν x hx, one_mul, List.take_of_length_le (by omega)]

theorem relT_main {ν : ℕ} : ∀ {cs : List FClaim} {cls : List (Com × BlockClaim × FE)},
    List.Forall₂ (FRelT M ν) cs cls → cls.all (·.1 == .main) = true ∧
      List.Forall₂ (FRel M ν) cs ((cls.filter (·.1 == .main)).map (·.2.1))
  | [], [], _ => ⟨rfl, .nil⟩
  | _ :: _, cl :: _, .cons ⟨hm, hr⟩ hrs => by
    obtain ⟨h1, h2⟩ := relT_main hrs
    refine ⟨by simp only [List.all_cons, hm, h1]; rfl, ?_⟩
    rw [List.filter_cons_of_pos (by simp [hm]), List.map_cons]
    exact .cons hr h2

set_option maxHeartbeats 1000000 in
/-- **`C_main`'s opening at S2GF, big shape, is V's `dOpenF p false`** (`hopen` of `core_of_phasesF` for a big
child): from the opening's start with `ok`, V keeps `ok`, reads `Σ` to the opening's end and leaves no message
pending; `pinB` is V's pin claim (`pinD`'s point claim), `cls` V's other claims, each standing for the circuit's. -/
theorem openF_big_at (p : Params) (Cm : SCfg) (hlv : Cm.levels = p.mainLevels) (hnu : Cm.nu = p.nuMain)
    (hgr : Cm.g = p.grind) (hood : Cm.ood = p.mainOod) {F : FCtx} (hF : FCtxOk M F) (pin : CClaim)
    (z : List FE) (a : FE) (hpin : FRel M Cm.nu (.e3 pin) (BlockClaim.point ⟨Cm.nu, 0⟩ z a)) (cs : List FClaim)
    (cls : List (Com × BlockClaim × FE)) (hrel : List.Forall₂ (FRelT M Cm.nu) cs cls) (mb : List Cell)
    (sK g : Cell) {sig : ByteArray} {T : Nat} (hS : Lvm.Q1.Streamed M sig T) (hok : LayOk Cm T = true)
    (hg : g.val M = 1) (hgK : g.ty = .K) (hpos : PosOk Cm M sig 0 Cm.levels (Cm.U + 15)) (hpw : PwOk Cm M 0 Cm.levels)
    (hend : 8 * stackEndL Cm.g Cm.ood Cm.levels (Cm.U + 15) = sig.size) {q : Ptr} (hq : 1 ≤ q.e)
    (h : Lvm.QSig.Ok c M (openGF Cm false F pin cs mb sK g) q) :
    ∀ s : RS, pos s = 8 * Cm.U → s.ok = true →
      (dOpenF p false (BlockClaim.point ⟨Cm.nu, 0⟩ z a) cls sig s).2.ok = true ∧
      (dOpenF p false (BlockClaim.point ⟨Cm.nu, 0⟩ z a) cls sig s).2.ent = sig.size ∧
      (dOpenF p false (BlockClaim.point ⟨Cm.nu, 0⟩ z a) cls sig s).2.msg = 0 := by
  intro s hs hsok
  obtain ⟨hall, hrel'⟩ := relT_main hrel
  have hrq : ({ s with ok := true && s.ok } : RS) = s := by cases s; rfl
  have e : dOpenF p false (BlockClaim.point ⟨Cm.nu, 0⟩ z a) cls sig s =
      verifyStackedOpening Cm.levels Cm.nu (((BlockClaim.point ⟨Cm.nu, 0⟩ z a).weight, a) ::
        ((cls.filter (·.1 == .main)).map (·.2.1)).map (·.onStack)) false Cm.g Cm.ood sig s := by
    unfold dOpenF
    rw [dm_bind, require_runW, hall, hrq, hlv, hnu, hgr, hood]
    simp only [Bool.false_eq_true, if_false, List.map_map]
    rfl
  rw [e]
  obtain ⟨o1, o2, o3⟩ := openGF_big_run Cm hF pin _ hpin _ (fun x hx => point_onStack Cm.nu z a x hx) cs _ hrel' mb
    sK g hS hok hg hgK hpos hpw hq h s hs
  refine ⟨o1.trans hsok, ?_, o3⟩
  simp only [pos] at o2
  rw [show (BlockClaim.point ⟨Cm.nu, 0⟩ z a).value = a from rfl] at o2 o3
  omega

end Lvm.Q2
