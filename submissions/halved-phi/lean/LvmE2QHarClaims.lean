-- New for lvm2 E2-FT (E2F-C7): the front's claims stand for V's (`FRelZ`), generic in the cells' values: the `D` word
-- halves of the tape, the `E2` halves of `KS` and the link (for `front_phasesF`).
import LvmE2QOpenPhase
import LvmE2QAsmFront

/-!
# The front's claims and V's

* **`forall₂_flatMap`**: `Forall₂` of two `flatMap`s over one list, element by element.
* **`selC2_vals`**, **`selC2_K`**: the selector cells hold `selPtF`, on `K` cells.
* **`dhalf_rel`**, **`dhalves_rel`**: the tape's `D` word halves (`FClaim.dhalf`) stand for V's split claims with the
  tails `tailDE2`.
* **`half_rel`**, **`halves_rel`**: an `E2` sum claim's halves stand for V's split claim (regular blocks, tail `0`).
* **`bound_rel`**: a boundary claim `D̃_l(bits(n − 1) ‖ l) = h_l` (tail `0`: `tailD_small` for `n ≤ 2^18`).
* **`frontCsF`**, **`front_claimsG`**: `frontF`'s claim list over its gadgets' outputs as variables, and the whole
  list stands for `frontClaimsD p` at a `p` with `P20`'s front facts (`RegsP`, `DselP`) (tape, `KS`, its outputs, the link), so that `front_phasesF` meets no builder
  run in the claims.
-/

set_option autoImplicit false

namespace Lvm.E2Q

open Lvm Lvm.Loop Lvm.Loop.Build Lvm.Har Lvm.Q2 Lvm.QShape

variable {M : Mem}

theorem forall₂_flatMap {α β γ : Type} {R : β → γ → Prop} {f : α → List β} {g : α → List γ} :
    ∀ (L : List α), (∀ a ∈ L, List.Forall₂ R (f a) (g a)) → List.Forall₂ R (L.flatMap f) (L.flatMap g)
  | [], _ => .nil
  | a :: L, h => by
    rw [List.flatMap_cons, List.flatMap_cons]
    exact List.rel_append (h a (List.mem_cons_self ..)) (forall₂_flatMap L fun b hb => h b (List.mem_cons_of_mem _ hb))

/-- The selector cells hold `selPtF`. -/
theorem selC2_vals {F : FCtx} (hz2 : F.z2.val M = 0) (ho2 : F.o2.val M = 1) (sel len : ℕ) :
    (selC2 F sel len).map (C2.val M) = E2V.selPtF sel len := by
  simp only [selC2, E2V.selPtF, List.map_map]
  refine List.map_congr_left fun i _ => ?_
  by_cases h : (sel >>> i) % 2 = 1 <;> simp [h, ho2, hz2]

theorem selC2_K {F : FCtx} (hz2 : KC2 F.z2) (ho2 : KC2 F.o2) (sel len : ℕ) : ∀ x ∈ selC2 F sel len, KC2 x := by
  intro x hx
  obtain ⟨i, -, rfl⟩ := List.mem_map.mp hx
  split
  · exact ho2
  · exact hz2

theorem selC2_length (F : FCtx) (sel len : ℕ) : (selC2 F sel len).length = len := by simp [selC2]

/-- A `K` cell pair's halves are its value's coordinates. -/
theorem kre_val {x : C2} (hx : KC2 x) : x.re.val M = FE.ofK (x.val M).re := (kcell_val hx.1).symm
theorem kim_val {x : C2} (hx : KC2 x) : x.im.val M = FE.ofK (x.val M).im := (kcell_val hx.2).symm

/-- **One `D` word claim's halves** (lane `l`, value cells `w`) stand for V's split claims with tails `tailDE2`. -/
theorem dhalf_rel {zc : Cell} {b : Bool} {F : FCtx} (hz2 : F.z2.val M = 0) (ho2 : F.o2.val M = 1) (hz2K : KC2 F.z2)
    (ho2K : KC2 F.o2) {r : List C2} (hr : ∀ x ∈ r, KC2 x) (hrl : r.length = 20) {l : ℕ} (hl : l < 4) {w : C2}
    (hw : KC2 w) :
    List.Forall₂ (FRelZ M zc b) [.dhalf false (r ++ selC2 F l 2) w.re, .dhalf true (r ++ selC2 F l 2) w.im]
      (((splitD 23 [(1, ⟨22, 0⟩, r.map (C2.val M) ++ E2V.selPtF l 2)] (w.val M)).zip
        (tailDE2 (r.map (C2.val M)) l)).map fun e => (Com.main, e.1, e.2)) := by
  have hz : (r ++ selC2 F l 2).map (C2.val M) = r.map (C2.val M) ++ E2V.selPtF l 2 := by
    rw [List.map_append, selC2_vals hz2 ho2]
  have hK : ∀ x ∈ r ++ selC2 F l 2, KC2 x := by
    intro x hx
    rcases List.mem_append.mp hx with h | h
    · exact hr x h
    · exact selC2_K hz2K ho2K l 2 x h
  have hlen : (r ++ selC2 F l 2).length = 22 := by rw [List.length_append, hrl, selC2_length]
  have hrl' : (r.map (C2.val M)).length = 20 := by rw [List.length_map, hrl]
  rw [splitD_halfB]
  refine .cons ⟨⟨rfl, hK, hlen, by decide, ?_⟩, r.map (C2.val M), l, hl, hrl', hz, rfl⟩
    (.cons ⟨⟨rfl, hK, hlen, by decide, ?_⟩, r.map (C2.val M), l, hl, hrl', hz, rfl⟩ .nil)
  · show halfB 23 false _ _ = halfB 23 false _ _
    rw [hz, kre_val hw]
  · show halfB 23 true _ _ = halfB 23 true _ _
    rw [hz, kim_val hw]

/-- **The tape's `D` word claims** (four lanes; the point cells `r`, the value cells `v`) stand for V's. -/
theorem dhalves_rel {zc : Cell} {b : Bool} {F : FCtx} (hz2 : F.z2.val M = 0) (ho2 : F.o2.val M = 1)
    (hz2K : KC2 F.z2) (ho2K : KC2 F.o2) {r : List C2} (hr : ∀ x ∈ r, KC2 x) (hrl : r.length = 20) {v : List C2}
    (hv : ∀ l < 4, KC2 (v.getD l default)) {rv : List FE2} (hrv : rv = r.map (C2.val M)) {vv : List FE2}
    (hvv : ∀ l < 4, vv.getD l 0 = (v.getD l default).val M) :
    List.Forall₂ (FRelZ M zc b)
      ((List.range 4).flatMap fun l => [.dhalf false (r ++ selC2 F l 2) (v.getD l default).re,
        .dhalf true (r ++ selC2 F l 2) (v.getD l default).im])
      ((List.range 4).flatMap fun l => ((splitD 23 [(1, ⟨22, 0⟩, rv ++ E2V.selPtF l 2)] (vv.getD l 0)).zip
        (tailDE2 rv l)).map fun e => (Com.main, e.1, e.2)) := by
  refine forall₂_flatMap _ fun l hl => ?_
  have hl' := List.mem_range.mp hl
  rw [hrv, hvv l hl']
  exact dhalf_rel hz2 ho2 hz2K ho2K hr hrl hl' (hv l hl')


/-! ## Generic list facts -/

theorem forall₂_map_of {α β γ : Type} {R : β → γ → Prop} {f : α → β} {g : α → γ} :
    ∀ (L : List α), (∀ a ∈ L, R (f a) (g a)) → List.Forall₂ R (L.map f) (L.map g)
  | [], _ => .nil
  | a :: L, h => .cons (h a (List.mem_cons_self ..)) (forall₂_map_of L fun b hb => h b (List.mem_cons_of_mem _ hb))

theorem zipIdx_map_range {α : Type} (f : ℕ → α) (n : ℕ) :
    ((List.range n).map f).zipIdx = (List.range n).map fun i => (f i, i) := by
  apply List.ext_getElem (by simp)
  intro i h1 h2
  simp

theorem mem_map_range {α : Type} {P : α → Prop} {f : ℕ → α} {n : ℕ} (h : ∀ l < n, P (f l)) :
    ∀ e ∈ (List.range n).map f, P e := by
  intro e he
  obtain ⟨l, hl, rfl⟩ := List.mem_map.mp he
  exact h l (List.mem_range.mp hl)

theorem getD_mapV {l : List C2} {i : ℕ} (hi : i < l.length) :
    (l.map (C2.val M)).getD i 0 = (l.getD i default).val M := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi]

theorem ld2_K (L : List ℕ) : ∀ x ∈ L.map Lvm.Q2.ld2, KC2 x := by
  intro x hx
  obtain ⟨q, -, rfl⟩ := List.mem_map.mp hx
  exact ⟨rfl, rfl⟩

/-! ## One claim -/

/-- A part of an `E2` sum claim on `K` cells, its point as long as its (regular) block's variables. -/
abbrev PartOk (e : C2 × Placement × List C2) : Prop :=
  KC2 e.1 ∧ (∀ x ∈ e.2.2, KC2 x) ∧ e.2.2.length = e.2.1.variableCount ∧ e.2.1.variableCount ≤ CMain.nu20 ∧ RegP e.2.1

/-- **Half `h` of an `E2` sum claim** stands for V's half (regular blocks, zero tail). -/
theorem half_rel {zc : Cell} {b : Bool} (h : Bool) {parts : List (C2 × Placement × List C2)}
    {pv : List (FE2 × Placement × List FE2)} {w : Cell} {wv : FE}
    (hp : ∀ e ∈ parts, PartOk e) (hpv : partsV M parts = pv) (hw : w.val M = wv) :
    FRelZ M zc b (.half h parts w) (.main, halfB CMain.nu20 h pv wv, 0) :=
  ⟨⟨rfl, fun e he => ⟨(hp e he).1, (hp e he).2.1, (hp e he).2.2.1, (hp e he).2.2.2.1⟩, by rw [hpv, hw]⟩,
    fun e he => (hp e he).2.2.2.2, rfl⟩

theorem splitZ_eq (ν : ℕ) (pv : List (FE2 × Placement × List FE2)) (v : FE2) :
    splitZ ν pv v = [(.main, halfB ν false pv (FE.ofK v.re), 0), (.main, halfB ν true pv (FE.ofK v.im), 0)] := rfl

/-- **An `E2` sum claim's halves** stand for V's split claim. -/
theorem halves_rel {zc : Cell} {b : Bool} {parts : List (C2 × Placement × List C2)}
    {pv : List (FE2 × Placement × List FE2)} {v : C2} {vv : FE2}
    (hp : ∀ e ∈ parts, PartOk e) (hpv : partsV M parts = pv) (hv : KC2 v) (hvv : v.val M = vv) :
    List.Forall₂ (FRelZ M zc b) (halves parts v) (splitZ CMain.nu20 pv vv) := by
  rw [splitZ_eq]
  exact .cons (half_rel false hp hpv (by rw [kre_val hv, hvv])) (.cons (half_rel true hp hpv (by rw [kim_val hv, hvv]))
    .nil)

/-! ## `KS`'s `Y` parts -/

theorem ksYPart2_fst (p : Params) (F : FCtx) (l : ℕ) (pt : List C2) :
    (ksYPart2 p F l pt).1 = (ksYPartD p (layout0 p) l []).1 := by
  unfold ksYPart2 ksYPartD; by_cases hl : l < 14 <;> simp [hl]

theorem ksYPartD_fst (p : Params) (l : ℕ) (pt : List FE2) :
    (ksYPartD p (layout0 p) l pt).1 = (ksYPartD p (layout0 p) l []).1 := by
  unfold ksYPartD; by_cases hl : l < 14 <;> simp [hl]

theorem ksYPart2_snd {F : FCtx} (hz2 : F.z2.val M = 0) (ho2 : F.o2.val M = 1) (p : Params) (l : ℕ) (pt : List C2) :
    (ksYPart2 p F l pt).2.map (C2.val M) = (ksYPartD p (layout0 p) l (pt.map (C2.val M))).2 := by
  unfold ksYPart2 ksYPartD; by_cases hl : l < 14 <;> simp [hl, selC2_vals hz2 ho2]

theorem ksYPart2_K {F : FCtx} (hz2 : KC2 F.z2) (ho2 : KC2 F.o2) (p : Params) (l : ℕ) {pt : List C2}
    (hpt : ∀ x ∈ pt, KC2 x) : ∀ x ∈ (ksYPart2 p F l pt).2, KC2 x := by
  unfold ksYPart2; by_cases hl : l < 14
  · simp only [hl, ite_true]
    intro x hx
    rcases List.mem_append.mp hx with h | h
    · exact hpt x h
    · exact selC2_K hz2 ho2 _ _ x h
  · simp only [hl, ite_false]; exact hpt

theorem ksYPart2_len (p : Params) (F : FCtx) (l : ℕ) (pt : List C2) (hpt : pt.length = p.ksLog) :
    (ksYPart2 p F l pt).2.length = (ksYPart2 p F l pt).1.variableCount := by
  unfold ksYPart2; by_cases hl : l < 14 <;> simp [hl, hpt, selC2_length]

/-! ## The static blocks at `P20F` -/

/-- The front's `E2` claims' blocks at `p` are regular (`KS`, its `Y` lanes, the stream block's columns). -/
def RegsP (p : Params) : Prop := RegP ⟨p.ksLog + slotLog, (layout0 p).ks⟩ ∧
    (∀ l < 25, RegP (ksYPartD p (layout0 p) l []).1 ∧
      (ksYPartD p (layout0 p) l []).1.variableCount ≤ CMain.nu20) ∧
    (∀ l < 17, RegP ⟨p.ksLog, (layout0 p).s + l * 2 ^ p.recRowsLog⟩ ∧
      RegP ⟨ksXLog p, (layout0 p).s + l * 2 ^ p.recRowsLog + ksSplit p⟩ ∧
      RegP ⟨ksXLog p, (layout0 p).x + l * 2 ^ p.recRowsLog⟩)

/-- The front's selector and sizes at `p` (`P20`'s). -/
def DselP (p : Params) : Prop := dSel p = 0 ∧ dSelBits p = 1 ∧ dBlock p = ⟨22, 0⟩ ∧ p.nuMain = CMain.nu20 ∧
    p.ksLog = 13 ∧ ksXLog p = 9 ∧ p.logN = 20 ∧ dLanes = 4

theorem regs_P20F : RegsP P20F := by
  unfold RegsP
  rw [show layout0 P20F = layout0 P20 from rfl, layout0_P20]
  decide +kernel

theorem dsel_P20F : DselP P20F := ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

/-! ## The boundary claims -/

theorem tailD_small {m : ℕ} (hm : m < 2 ^ 18) (z : List FE) : tailD (selectorPoint m 20 ++ z) = 0 := by
  have h18 : (selectorPoint m 20 ++ z).getD 18 0 = 0 := by
    rw [List.getD_append _ _ _ _ (by simp [selectorPoint_length'])]
    simp only [selectorPoint, List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range (by norm_num : 18 < 20),
      Option.map_some, Option.getD_some, Nat.shiftRight_eq_div_pow, Nat.div_eq_of_lt hm, Nat.zero_mod]
    rfl
  have h19 : (selectorPoint m 20 ++ z).getD 19 0 = 0 := by
    rw [List.getD_append _ _ _ _ (by simp [selectorPoint_length'])]
    simp only [selectorPoint, List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range (by norm_num : 19 < 20),
      Option.map_some, Option.getD_some, Nat.shiftRight_eq_div_pow,
      Nat.div_eq_of_lt (lt_trans hm (by norm_num) : m < 2 ^ 19), Nat.zero_mod]
    rfl
  rw [tailD, kappaD, h18, h19, add_zero, one_mul, CharTwo.add_self_eq_zero, zero_mul]

/-- **A boundary claim** `D̃_l(bits(n − 1) ‖ l) = h_l` stands for V's (tail `0`; small children: `n ≤ 2^18`). -/
theorem bound_rel {zc : Cell} {b : Bool} {mbE : List Cell} {N : ℕ} (hmb : vs M mbE = selectorPoint (N - 1) 20)
    (hsm : b = true → N ≤ 2 ^ 18) (hN : 1 ≤ N) {zE oE : ℕ} (hz : M.e zE = 0) (ho : M.e oE = 1) {l : ℕ} (w : ℕ) :
    FRelZ M zc b (.e3 ⟨.main, .point ⟨22, 0⟩ (mbE ++ Lvm.Har.selC zE oE l 2), kc w⟩)
      (.main, BlockClaim.point ⟨22, 0⟩ (selectorPoint (N - 1) 20 ++ selectorPoint l 2) (FE.ofK (M.k w)), 0) := by
  have hml : mbE.length = 20 := by
    have := congrArg List.length hmb; simpa [vs, selectorPoint_length'] using this
  have hlen : (mbE ++ Lvm.Har.selC zE oE l 2).length = 22 := by simp [hml, Lvm.Har.selC]
  have hv : vs M (mbE ++ Lvm.Har.selC zE oE l 2) = selectorPoint (N - 1) 20 ++ selectorPoint l 2 := by
    rw [vs, List.map_append, ← vs, ← vs, hmb, Lvm.Har.selC_vs hz ho]
  refine ⟨⟨rfl, ?_, ?_⟩, ?_, fun hb => ?_⟩
  · show (decide (22 ≤ CMain.nu20) && decide ((mbE ++ Lvm.Har.selC zE oE l 2).length = 22)) = true
    rw [hlen]; rfl
  · show _ = BlockClaim.point ⟨22, 0⟩ (vs M (mbE ++ Lvm.Har.selC zE oE l 2)) ((kc w).val M)
    rw [hv, Cell.val_K]
  · show (if (⟨22, 0⟩ : Placement) = ⟨22, 0⟩ then decide ((mbE ++ Lvm.Har.selC zE oE l 2).length = 22)
      else decide (RegP (⟨22, 0⟩ : Placement))) = true
    simp [hlen]
  · show 0 = if (⟨22, 0⟩ : Placement) = ⟨22, 0⟩ then tailD (vs M (mbE ++ Lvm.Har.selC zE oE l 2)) else 0
    simp only [↓reduceIte, hv]
    rw [tailD_small (by have := hsm hb; omega)]

/-! ## The front's claims -/

/-- **`frontF`'s claims** from its gadgets' outputs (`frontF`'s list with the outputs as variables). -/
def frontCsF (p : Params) (F : FCtx) (r v ki kv : List C2) (wo : WireOut2) (rw : RowOut) (nuW : RowNu)
    (ko : Lvm.Q1.GkrOutE2) (rk : RowOut) (nuK : RowNu) (kl : KsLinkOut2) (mbE : List Cell) (omS : List C2) :
    List FClaim :=
  let L := layout0 p
  let blkD := dBlock p
  let ksBlk : Placement := ⟨p.ksLog + slotLog, L.ks⟩
  let xl := ksXLog p
  let R := 2 ^ p.recRowsLog
  let rho' := kl.shift
  let xlo := rho'.take xl
  let om := kl.om
  let tape : List FClaim :=
    ((List.range dLanes).flatMap fun l =>
      let zl := r ++ selC2 F l 2
      let vl := v.getD l default
      [.dhalf false zl vl.re, .dhalf true zl vl.im]) ++
    [.drow (wo.sigma ++ wo.tau ++ selC2 F (dSel p) (dSelBits p)) nuW rw.target] ++
    (List.range 4).map fun l => .e3 ⟨.main, .point blkD (mbE ++ Lvm.Har.selC F.z.n F.o.n l 2), kc (hLane l)⟩
  let ks : List FClaim :=
    halves [(F.o2, ksBlk, ko.wordPoint)] ko.word ++ [.row ksBlk ko.slicePoint nuK rk.target]
  let ksOut : List FClaim := (List.range 25).flatMap fun l =>
    let bz := ksYPart2 p F l ki
    halves [(F.o2, bz.1, bz.2)] (kv.getD l default)
  let yParts := (List.range 25).map fun l => let bz := ksYPart2 p F l rho'; (om.getD l default, bz.1, bz.2)
  let inParts := (List.range 25).map fun l => (om.getD l default, ksBlk, rho' ++ selC2 F l slotLog)
  let mParts := (List.range 17).map (fun l => (om.getD l default, (⟨p.ksLog, L.s + l * R⟩ : Placement), rho')) ++
    (List.range 17).map (fun l => (omS.getD l default, (⟨xl, L.s + l * R + ksSplit p⟩ : Placement), xlo))
  let xParts := (List.range 17).map fun l => (om.getD l default, (⟨xl, L.x + l * R⟩ : Placement), xlo)
  let vY := kl.vals.getD 0 default
  let vIn := kl.vals.getD 1 default
  let vM := kl.vals.getD 2 default
  let vX := kl.vals.getD 3 default
  let link : List FClaim :=
    halves yParts vY ++ halves inParts vIn ++ [.half false xParts vX.re] ++ halves mParts vM ++
      [.half true xParts vX.im]
  tape ++ ks ++ ksOut ++ link


theorem rowValD_snd (z sv : List FE2) (e : List FE) : (rowValD z sv e).2 = e := rfl

theorem getD_K {l : List C2} (h : ∀ x ∈ l, KC2 x) {i : ℕ} (hi : i < l.length) : KC2 (l.getD i default) := by
  rw [List.getD_eq_getElem _ _ hi]; exact h _ (List.getElem_mem hi)

theorem partsV_range {n : ℕ} {f : ℕ → C2 × Placement × List C2} {g : ℕ → FE2 × Placement × List FE2}
    (h : ∀ l < n, (f l).1.val M = (g l).1 ∧ (f l).2.1 = (g l).2.1 ∧ (f l).2.2.map (C2.val M) = (g l).2.2) :
    partsV M ((List.range n).map f) = (List.range n).map g := by
  simp only [partsV, List.map_map]
  refine List.map_congr_left fun l hl => ?_
  obtain ⟨e1, e2, e3⟩ := h l (List.mem_range.mp hl)
  simp only [Function.comp_apply, e1, e2, e3]

theorem partsV_append (a b : List (C2 × Placement × List C2)) : partsV M (a ++ b) = partsV M a ++ partsV M b :=
  List.map_append ..

set_option maxHeartbeats 1000000 in
/-- **The front's claims stand for V's** (`frontClaimsD p` at the phases' values; `p` with `P20`'s front facts: S2GF, S2GT), from the front gadgets'
outputs as variables: the tape's `D` word halves, row claim and boundary claims, `KS`'s word halves and row claim, its
25 output lanes, the link's `Y`, `in`, `X`, `M` halves. -/
theorem front_claimsG {p : Params} (hR : RegsP p) (hD : DselP p) {zc : Cell} {b : Bool} {pub : Pub} {F : FCtx} {r v ki kv : List C2} {wo : WireOut2}
    {rw : RowOut} {nuW : RowNu} {ko : Lvm.Q1.GkrOutE2} {rk : RowOut} {nuK : RowNu} {kl : KsLinkOut2}
    {mbE : List Cell} {omS : List C2} {tr tv tgl tsv cr cv csl : List FE2} {tk : E2V.KClaim FE2}
    {tfin tfo lfin : FE2} {eqW eqK : List FE}
    (hz2 : F.z2.val M = 0) (ho2 : F.o2.val M = 1) (hz2K : KC2 F.z2) (ho2K : KC2 F.o2) (hzE : M.e F.z.n = 0)
    (hoE : M.e F.o.n = 1)
    (hr : ∀ x ∈ r, KC2 x) (hrl : r.length = 20) (hv : ∀ l < 4, KC2 (v.getD l default))
    (htr : tr = r.map (C2.val M)) (htv : ∀ l < 4, tv.getD l 0 = (v.getD l default).val M)
    (hsgK : ∀ x ∈ wo.sigma, KC2 x) (hsgl : wo.sigma.length = 20) (htaK : ∀ x ∈ wo.tau, KC2 x)
    (htal : wo.tau.length = 2)
    (htr1 : (rowValD (wo.sigma.map (C2.val M) ++ wo.tau.map (C2.val M) ++ E2V.selPtF (dSel p) (dSelBits p))
      tsv eqW).1.1 = rw.target.val M)
    (hnuW : RowNuOk M nuW eqW)
    (hmbE : vs M mbE = selectorPoint (pub.n - 1) 20) (hh : pub.h = (List.range 4).map fun l => M.k (hLane l))
    (hsm : b = true → pub.n ≤ 2 ^ 18) (hn : 1 ≤ pub.n)
    (hwpK : ∀ x ∈ ko.wordPoint, KC2 x) (hwpl : ko.wordPoint.length = 19) (hwK : KC2 ko.word)
    (hspK : ∀ x ∈ ko.slicePoint, KC2 x) (hspl : ko.slicePoint.length = 19)
    (hcr1 : (rowValD (ko.slicePoint.map (C2.val M)) csl eqK).1.1 = rk.target.val M) (hnuK : RowNuOk M nuK eqK)
    (hkiK : ∀ x ∈ ki, KC2 x) (hkil : ki.length = 13) (hcr : cr = ki.map (C2.val M))
    (hkvK : ∀ l < 25, KC2 (kv.getD l default)) (hcv : ∀ l < 25, cv.getD l 0 = (kv.getD l default).val M)
    (hshK : ∀ x ∈ kl.shift, KC2 x) (hshl : kl.shift.length = 13) (hkcl : kl.kchal.length = 18)
    (homK : ∀ x ∈ kl.om, KC2 x)
    (hom : kl.om.map (C2.val M) = E2V.eqKernelF ((kl.kchal.drop p.ksLog).map (C2.val M)))
    (hsel : kl.sel.val M = E2V.selXF (ksXLog p) (kl.shift.map (C2.val M)))
    (homS : ∀ l < 17, KC2 (omS.getD l default) ∧
      (omS.getD l default).val M = (kl.om.getD l default).val M * kl.sel.val M)
    (hvl : kl.vals.length = 4) (hvK : ∀ x ∈ kl.vals, KC2 x) :
    List.Forall₂ (FRelZ M zc b) (frontCsF p F r v ki kv wo rw nuW ko rk nuK kl mbE omS)
      (frontClaimsD p pub
        (tr, tv, tk, ((wo.sigma.map (C2.val M), tfin), tgl, ((wo.tau.map (C2.val M), tfo), tsv,
          rowValD (wo.sigma.map (C2.val M) ++ wo.tau.map (C2.val M) ++ E2V.selPtF (dSel p) (dSelBits p))
            tsv eqW)))
        (cr, cv, ([(ko.wordPoint.map (C2.val M), ko.word.val M)], ko.slicePoint.map (C2.val M), csl),
          rowValD (ko.slicePoint.map (C2.val M)) csl eqK)
        (kl.kchal.map (C2.val M), (kl.shift.map (C2.val M), lfin), kl.vals.map (C2.val M))) := by
  obtain ⟨hdS, hdB, hdBl, hnu, hksL, hxl, hlogN, hdL⟩ := hD
  obtain ⟨rK, rY, rS⟩ := hR
  have h19 : (19 : ℕ) = p.ksLog + slotLog := by rw [hksL]; rfl
  have homl : kl.om.length = 32 := by
    have := congrArg List.length hom
    rw [List.length_map, E2V.eqKernelF_length] at this
    rw [this]; simp [hkcl, hksL]
  have homg : ∀ l < 32, (kl.om.getD l default).val M =
      (E2V.eqKernelF ((kl.kchal.map (C2.val M)).drop p.ksLog)).getD l 0 := fun l hl => by
    rw [← getD_mapV (by omega), hom, List.map_drop]
  have hvv : ∀ k < 4, (kl.vals.getD k default).val M = (kl.vals.map (C2.val M)).getD k 0 := fun k hk =>
    (getD_mapV (by omega)).symm
  have hvK' : ∀ k < 4, KC2 (kl.vals.getD k default) := fun k hk => getD_K hvK (by omega)
  have homK' : ∀ l < 25, KC2 (kl.om.getD l default) := fun l hl => getD_K homK (by omega)
  have hselC : ∀ l, ∀ x ∈ kl.shift ++ selC2 F l slotLog, KC2 x := fun l x hx => by
    rcases List.mem_append.mp hx with h | h
    · exact hshK x h
    · exact selC2_K hz2K ho2K _ _ x h
  have htakeK : ∀ x ∈ kl.shift.take (ksXLog p), KC2 x := fun x hx => hshK x (List.mem_of_mem_take hx)
  have htakel : (kl.shift.take (ksXLog p)).length = ksXLog p := by simp [hshl, hxl]
  simp only [frontCsF, frontClaimsD]
  rw [hnu]
  refine List.rel_append (List.rel_append (List.rel_append ?_ ?_) ?_) ?_
  · -- the tape
    refine List.rel_append (List.rel_append ?_ ?_) ?_
    · rw [hdBl, hdL]
      exact dhalves_rel hz2 ho2 hz2K ho2K hr hrl hv htr htv
    · have hzz : (wo.sigma ++ wo.tau ++ selC2 F (dSel p) (dSelBits p)).map (C2.val M) =
          wo.sigma.map (C2.val M) ++ wo.tau.map (C2.val M) ++ E2V.selPtF (dSel p) (dSelBits p) := by
        simp only [List.map_append, selC2_vals hz2 ho2]
      have hzl : (wo.sigma ++ wo.tau ++ selC2 F (dSel p) (dSelBits p)).length = CMain.nu20 := by
        simp only [List.length_append, hsgl, htal, selC2_length, hdB]
      have hzK : ∀ x ∈ wo.sigma ++ wo.tau ++ selC2 F (dSel p) (dSelBits p), KC2 x := fun x hx => by
        rcases List.mem_append.mp hx with h | h
        · rcases List.mem_append.mp h with h | h
          · exact hsgK x h
          · exact htaK x h
        · exact selC2_K hz2K ho2K _ _ x h
      refine .cons ⟨⟨rfl, eqW, hnuW, ?_, hzK, hzl, le_refl _, ?_⟩, ?_, eqW, hnuW, by rw [hzz, rowValD_snd]⟩ .nil
      · intro e; rw [e] at hzl; simp at hzl
      · show (⟨⟨CMain.nu20, 0⟩, (rowValD _ _ eqW).1.2, (rowValD _ _ eqW).1.1⟩ : BlockClaim) = _
        rw [htr1, rowValD_weight, hzz]
      · rw [hzz, List.getD_append_right _ _ _ _ (by simp [hsgl, htal]), hdS, hdB]
        simp [hsgl, htal, E2V.selPtF]
    · rw [hh, zipIdx_map_range, List.map_map, hdBl, hlogN]
      exact forall₂_map_of _ fun l _ => bound_rel hmbE hsm hn hzE hoE (hLane l)
  · -- `KS`: the word halves, the row claim
    refine List.rel_append ?_ (.cons ⟨⟨rfl, eqK, hnuK, ?_, hspK, hspl.trans h19,
      by show p.ksLog + slotLog ≤ CMain.nu20; rw [hksL]; decide, ?_⟩, rK, rfl⟩ .nil)
    · rw [List.flatMap_cons, List.flatMap_nil, List.append_nil]
      refine halves_rel ?_ (by simp only [partsV, List.map_cons, List.map_nil, ho2]) hwK rfl
      simp only [List.mem_singleton, forall_eq]
      exact ⟨ho2K, hwpK, hwpl.trans h19, by show p.ksLog + slotLog ≤ CMain.nu20; rw [hksL]; decide, rK⟩
    · intro e; rw [e] at hspl; simp at hspl
    · show (⟨_, (rowValD _ _ eqK).1.2, (rowValD _ _ eqK).1.1⟩ : BlockClaim) = _
      rw [hcr1, rowValD_weight]
  · -- `KS`'s 25 output lanes
    refine forall₂_flatMap _ fun l hl => ?_
    have hl' := List.mem_range.mp hl
    refine halves_rel ?_ ?_ (hkvK l hl') (hcv l hl').symm
    · simp only [List.mem_singleton, forall_eq]
      refine ⟨ho2K, ksYPart2_K hz2K ho2K _ _ hkiK, ksYPart2_len _ _ _ _ (hkil.trans hksL.symm), ?_, ?_⟩ <;>
        rw [ksYPart2_fst]
      · exact (rY l hl').2
      · exact (rY l hl').1
    · simp only [partsV, List.map_cons, List.map_nil, ho2, ksYPart2_snd hz2 ho2, hcr, ksYPart2_fst, ksYPartD_fst]
  · -- the link
    have hY : ∀ l < 25, KC2 (kl.om.getD l default) ∧ (∀ x ∈ (ksYPart2 p F l kl.shift).2, KC2 x) ∧
        (ksYPart2 p F l kl.shift).2.length = (ksYPart2 p F l kl.shift).1.variableCount ∧
        (ksYPart2 p F l kl.shift).1.variableCount ≤ CMain.nu20 ∧ RegP (ksYPart2 p F l kl.shift).1 :=
      fun l hl => ⟨homK' l hl, ksYPart2_K hz2K ho2K _ _ hshK, ksYPart2_len _ _ _ _ (hshl.trans hksL.symm),
        by rw [ksYPart2_fst]; exact (rY l hl).2, by rw [ksYPart2_fst]; exact (rY l hl).1⟩
    have hxv : ∀ l < 17, (kl.om.getD l default).val M =
        (E2V.eqKernelF ((kl.kchal.map (C2.val M)).drop p.ksLog)).getD l 0 := fun l hl => homg l (by omega)
    have hX : partsV M ((List.range 17).map fun l => (kl.om.getD l default,
          (⟨ksXLog p, (layout0 p).x + l * 2 ^ p.recRowsLog⟩ : Placement), kl.shift.take (ksXLog p))) =
        (List.range 17).map fun l => ((E2V.eqKernelF ((kl.kchal.map (C2.val M)).drop p.ksLog)).getD l 0,
          (⟨ksXLog p, (layout0 p).x + l * 2 ^ p.recRowsLog⟩ : Placement),
          (kl.shift.map (C2.val M)).take (ksXLog p)) :=
      partsV_range fun l hl => ⟨hxv l hl, rfl, List.map_take ..⟩
    have hXp : ∀ e ∈ (List.range 17).map (fun l => (kl.om.getD l default,
          (⟨ksXLog p, (layout0 p).x + l * 2 ^ p.recRowsLog⟩ : Placement), kl.shift.take (ksXLog p))),
        KC2 e.1 ∧ (∀ x ∈ e.2.2, KC2 x) ∧ e.2.2.length = e.2.1.variableCount ∧ e.2.1.variableCount ≤ CMain.nu20 ∧
          RegP e.2.1 :=
      mem_map_range fun l hl => ⟨homK' l (by omega), htakeK, htakel, by show ksXLog p ≤ CMain.nu20; rw [hxl]; decide,
        (rS l hl).2.2⟩
    refine List.rel_append (List.rel_append (List.rel_append (List.rel_append ?_ ?_) ?_) ?_) ?_
    · refine halves_rel (mem_map_range hY) (partsV_range fun l hl => ⟨homg l (by omega), ?_, ?_⟩)
        (hvK' 0 (by omega)) (hvv 0 (by omega))
      · simp only [ksYPart2_fst, ksYPartD_fst]
      · simp only [ksYPart2_snd hz2 ho2]
    · refine halves_rel (mem_map_range fun l hl => ⟨homK' l hl, hselC l, ?_,
        by show p.ksLog + slotLog ≤ CMain.nu20; rw [hksL]; decide, rK⟩)
        (partsV_range fun l hl => ⟨homg l (by omega), rfl, ?_⟩) (hvK' 1 (by omega)) (hvv 1 (by omega))
      · simp [hshl, selC2_length, hksL]
      · rw [List.map_append, selC2_vals hz2 ho2]
    · rw [splitZ_eq, List.take_succ_cons, List.take_zero]
      exact .cons (half_rel false hXp hX (by rw [kre_val (hvK' 3 (by omega)), hvv 3 (by omega)])) .nil
    · refine halves_rel ?_ ?_ (hvK' 2 (by omega)) (hvv 2 (by omega))
      · intro e he
        rcases List.mem_append.mp he with h | h
        · refine mem_map_range (P := PartOk) ?_ e h
          intro l hl
          exact ⟨homK' l (by omega), hshK, by rw [hshl, hksL],
            by show p.ksLog ≤ CMain.nu20; rw [hksL]; decide,
            (rS l hl).1⟩
        · refine mem_map_range (P := PartOk) ?_ e h
          intro l hl
          exact ⟨(homS l hl).1, htakeK, htakel, by show ksXLog p ≤ CMain.nu20; rw [hxl]; decide, (rS l hl).2.1⟩
      · rw [partsV_append]
        congr 1
        · exact partsV_range fun l hl => ⟨homg l (by omega), rfl, rfl⟩
        · exact partsV_range fun l hl => ⟨by rw [(homS l hl).2, homg l (by omega), hsel], rfl, List.map_take ..⟩
    · rw [splitZ_eq, List.drop_succ_cons, List.drop_zero]
      exact .cons (half_rel true hXp hX (by rw [kim_val (hvK' 3 (by omega)), hvv 3 (by omega)])) .nil

end Lvm.E2Q
