-- New for lvm2 E2-FT (E2F-QH5): `C_main`'s opening at S2GF (`LvmE2QPinOpen.openGF`) replays V's opening
-- (`LvmDecideE2.dOpenF`), big shape: what each circuit claim stands for (`FRel`), the batched basis with the `E2`
-- claim forms (`basisGF_spec`: word halves by `w6Leaf_spec`, row claims by `rowLeafGL_weightN`, `E3` claims by
-- `oneClaim_spec`), and the stacked opening's run (`openGF_big_run`, by the generic `stackG_run`).
import LvmE2QPinOpenSem
import LvmQRingCrtSem
import LvmQRingCrtLSem
import LvmQAsmArith2Whir

-- (GOLF2: 10 declarations that `certified` does not use moved verbatim to `LvmE2QPinOpenFOff`, outside its import closure.)

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

/-! ## The opening, big shape -/

/-! ## V's `dOpenF`, big shape -/

/-- **What a circuit claim stands for in V's list** (`dOpenF`'s `(com, claim, tail)`): on `C_main`, `FRel`. -/
def FRelT (M : Mem) (ν : ℕ) (fc : FClaim) (cl : Com × BlockClaim × FE) : Prop := cl.1 = .main ∧ FRel M ν fc cl.2.1

theorem relT_main {ν : ℕ} : ∀ {cs : List FClaim} {cls : List (Com × BlockClaim × FE)},
    List.Forall₂ (FRelT M ν) cs cls → cls.all (·.1 == .main) = true ∧
      List.Forall₂ (FRel M ν) cs ((cls.filter (·.1 == .main)).map (·.2.1))
  | [], [], _ => ⟨rfl, .nil⟩
  | _ :: _, cl :: _, .cons ⟨hm, hr⟩ hrs => by
    obtain ⟨h1, h2⟩ := relT_main hrs
    refine ⟨by simp only [List.all_cons, hm, h1]; rfl, ?_⟩
    rw [List.filter_cons_of_pos (by simp [hm]), List.map_cons]
    exact .cons hr h2

end Lvm.Q2
